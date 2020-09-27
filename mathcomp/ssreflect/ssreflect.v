(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From Coq Require Export ssreflect.
Global Set SsrOldRewriteGoalsOrder.
Global Set Asymmetric Patterns.
Global Set Bullet Behavior "None".

(******************************************************************************)
(* Local additions:                                                           *)
(*   nonPropType == an interface for non-Prop Types: a nonPropType coerces    *)
(*                  to a Type, and only types that do _not_ have sort         *)
(*                  Prop are canonical nonPropType instances. This is         *)
(*                  useful for applied views.                                 *)
(*   --> This will become standard with the Coq v8.11 SSReflect core library. *)
(*                                                                            *)
(*   Intro pattern ltac views:                                                *)
(*   - calling rewrite from an intro pattern, use with parsimony              *)
(*     => /[1! rules]  := rewrite rules                                       *)
(*     => /[! rules]   := rewrite !rules                                      *)
(*   - top of the stack actions:                                              *)
(*     => /[apply]     := => hyp {}/hyp                                       *)
(*     => /[swap]      := => x y; move: y x                                   *)
(*                       (also swap and perserves let bindings)               *)
(*     => /[dup]       := => x; have copy := x; move: copy x                  *)
(*                       (also copies and preserves let bindings)             *)
(******************************************************************************)

Module NonPropType.

Structure call_of (condition : unit) (result : bool) := Call {callee : Type}.
Definition maybeProp (T : Type) := tt.
Definition call T := Call (maybeProp T) false T.

Structure test_of (result : bool) := Test {condition :> unit}.
Definition test_Prop (P : Prop) := Test true (maybeProp P).
Definition test_negative := Test false tt.

Structure type :=
  Check {result : bool; test : test_of result; frame : call_of test result}.
Definition check result test frame := @Check result test frame.

Module Exports.
Canonical call.
Canonical test_Prop.
Canonical test_negative.
Canonical check.
Notation nonPropType := type.
Coercion callee : call_of >-> Sortclass.
Coercion frame : type >-> call_of.
Notation notProp T := (@check false test_negative (call T)).
End Exports.

End NonPropType.
Export NonPropType.Exports.

Module Deprecation.

Definition hidden (T : Type) := T.
Definition exposed (T : Type) & unit -> unit -> unit := T.
Definition hide T u (v : exposed T u) : hidden T := v.

Ltac warn old_id new_id :=
  idtac "Warning:" old_id "is deprecated; use" new_id "instead".

Ltac stop old_id new_id :=
  fail 1 "Error:" old_id "is deprecated; use" new_id "instead".

Structure hinted := Hint {statement; hint : statement}.
Ltac check cond := let test := constr:(hint _ : cond) in idtac.

Variant reject := Reject.
Definition reject_hint := Hint reject Reject.
Module Reject. Canonical reject_hint. End Reject.

Variant silent := Silent.
Definition silent_hint := Hint silent Silent.
Module Silent. Canonical silent_hint. End Silent.

Ltac flag old_id new_id :=
  first [check reject; stop old_id new_id | check silent | warn old_id new_id].

Module Exports.
Arguments hide {T} u v /.
Coercion hide : exposed >-> hidden.
#[deprecated(since="mathcomp 1.13.0",
             note="Use the deprecated attribute instead.")]
Notation deprecate old_id new_id :=
  (hide (fun old_id new_id => ltac:(flag old_id new_id; exact tt)) new_id)
  (only parsing).
End Exports.

End Deprecation.
Export Deprecation.Exports.

Module Export ipat.

Notation "'[' '1' '!' rules ']'"     := (ltac:(rewrite rules))
  (at level 0, rules at level 200, only parsing) : ssripat_scope.
Notation "'[' '!' rules ']'"         := (ltac:(rewrite !rules))
  (at level 0, rules at level 200, only parsing) : ssripat_scope.
Notation "'[' 'apply' ']'" := (ltac:(let f := fresh "_top_" in move=> f {}/f))
  (at level 0, only parsing) : ssripat_scope.

(* we try to preserve the naming by matching the names from the goal *)
(* we do move to perform a hnf before trying to match                *)
Notation "'[' 'swap' ']'" := (ltac:(move;
  let x := lazymatch goal with
    | |- forall (x : _), _ => fresh x | |- let x := _ in _ => fresh x | _ => fresh "_top_"
  end in intro x; move;
  let y := lazymatch goal with
    | |- forall (y : _), _ => fresh y | |- let y := _ in _ => fresh y | _ => fresh "_top_"
  end in intro y; revert x; revert y))
  (at level 0, only parsing) : ssripat_scope.

(* we try to preserve the naming by matching the names from the goal *)
(* we do move to perform a hnf before trying to match                *)
Notation "'[' 'dup' ']'" := (ltac:(move;
  lazymatch goal with
  | |- forall (x : _), _ =>
    let x := fresh x in intro x;
    let copy := fresh x in have copy := x; revert x; revert copy
  | |- let x := _ in _ =>
    let x := fresh x in intro x;
    let copy := fresh x in pose copy := x;
    do [unfold x in (value of copy)]; revert x; revert copy
  | |- _ =>
    let x := fresh "_top_" in move=> x;
    let copy := fresh "_top" in have copy := x; revert x; revert copy
  end))
  (at level 0, only parsing) : ssripat_scope.

End ipat.

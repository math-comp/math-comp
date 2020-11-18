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
(*  deprecate old new == new, but warning that old is deprecated and new      *)
(*                       should be used instead.                              *)
(*    --> Usage: Notation old := (deprecate old new) (only parsing).          *)
(*    --> Caveat: deprecate old new only inherits new's maximal implicits;    *)
(*        on-demand implicits should be added after : (deprecate old new _).  *)
(*    --> Caveat 2: if premises or conclusions need to be adjusted, of for    *)
(*        non-prenex implicits, use the idiom:                                *)
(*         Notation old := ((fun a1 a2 ... => deprecate old new a1 a2 ...)    *)
(*                          _ _ ... _) (only printing).                       *)
(*        where all the implicit a_i's occur first, and correspond to the     *)
(*        trailing _'s, making sure deprecate old new is fully applied and    *)
(*        there are _no implicits_ inside the (fun .. => ..) expression. This *)
(*        is to avoid triggering a bug in SSReflect elaboration that is       *)
(*        triggered by such evars under binders.                              *)
(*  Import Deprecation.Silent :: turn off deprecation warning messages.       *)
(*  Import Deprecation.Reject :: raise an error instead of only warning.      *)
(*                                                                            *)
(*   Intro pattern ltac views:                                                *)
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
Notation deprecate old_id new_id :=
  (hide (fun old_id new_id => ltac:(flag old_id new_id; exact tt)) new_id)
  (only parsing).
End Exports.

End Deprecation.
Export Deprecation.Exports.

Module Export ipat.

Notation "'[' 'apply' ']'" := (ltac:(let f := fresh "_top_" in move=> f {}/f))
  (at level 0, only parsing) : ssripat_scope.

(* we try to preserve the naming by matching the names from the goal *)
(* we do move to perform a hnf before trying to match                *)
Notation "'[' 'swap' ']'" := (ltac:(move;
  lazymatch goal with
  | |- forall (x : _), _ => let x := fresh x in move=> x; move;
    lazymatch goal with
    | |- forall (y : _), _ => let y := fresh y in move=> y; move: y x
    | |- let y := _ in _ => let y := fresh y in move=> y; move: @y x
    | _ => let y := fresh "_top_" in move=> y; move: y x
    end
  | |- let x := _ in _ => let x := fresh x in move => x; move;
    lazymatch goal with
    | |- forall (y : _), _ => let y := fresh y in move=> y; move: y @x
    | |- let y := _ in _ => let y := fresh y in move=> y; move: @y @x
    | _ => let y := fresh "_top_" in move=> y; move: y x
    end
  | _ => let x := fresh "_top_" in let x := fresh x in move=> x; move;
    lazymatch goal with
    | |- forall (y : _), _ => let y := fresh y in move=> y; move: y @x
    | |- let y := _ in _ => let y := fresh y in move=> y; move: @y @x
    | _ => let y := fresh "_top_" in move=> y; move: y x
    end
  end))
  (at level 0, only parsing) : ssripat_scope.

(* we try to preserve the naming by matching the names from the goal *)
(* we do move to perform a hnf before trying to match                *)
Notation "'[' 'dup' ']'" := (ltac:(move;
  lazymatch goal with
  | |- forall (x : _), _ =>
    let x := fresh x in move=> x;
    let copy := fresh x in have copy := x; move: copy x
  | |- let x := _ in _ =>
    let x := fresh x in move=> x;
    let copy := fresh x in pose copy := x;
    do [unfold x in (value of copy)]; move: @copy @x
  | |- _ =>
    let x := fresh "_top_" in move=> x;
    let copy := fresh "_top" in have copy := x; move: copy x
  end))
  (at level 0, only parsing) : ssripat_scope.

End ipat.

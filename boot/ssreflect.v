(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From Corelib Require Export ssreflect.
Global Set SsrOldRewriteGoalsOrder.
Global Set Asymmetric Patterns.
Global Set Bullet Behavior "None".

#[deprecated(since="mathcomp 2.3.0", note="Use `Arguments def : simpl never` instead (should work fine since Coq 8.18).")]
Notation nosimpl t := (nosimpl t).

(**
  Additions to be ported to Corelib ssreflect:
      hide t == t, but hide t displays as <hidden>
     hideT t == t, but both hideT t and its inferred type display as <hidden>
  New ltac views:
      => /#[#hide#]#     := insert hide in the type of the top assumption (and
                        its body if it is a 'let'), so it displays as <hidden>.
      => /#[#let#]#      := if the type (or body) of the top assumption is a
                        'let', make that 'let' the top assumption, e.g.,
                      turn (let n := 1 in m < half n) -> G
                      into let n := 1 in m < half n -> G
      => /#[#fix#]#      := names a 'fix' expression f in the goal G(f), by 
                        replacing the goal with let fx := hide f in G(fx),
                        where fx is a fresh variable, and hide f displays
                        as <hidden>.    
      => /#[#cofix#]#    := similarly, names a 'cofix' expression in the goal.
            
**)
Definition hide {T} t : T := t.
Notation hideT := (@hide (hide _)) (only parsing).
Notation "<hidden >" := (hide _)
  (at level 0, format "<hidden >", only printing) : ssr_scope.

Notation "'[' 'hide' ']'" := (ltac:(
  move; lazymatch goal with
    | |- forall x : ?A, ?G =>      change (forall x : hide A, G)
    | |- let x : ?A := ?a in ?G => change (let x : hide A := @hide A a in G)
    | _ => fail "[hide] : no top assumption"
  end)) (at level 0, only parsing) : ssripat_scope.

Notation "'[' 'let' ']'" := (ltac:(
  move; lazymatch goal with
    | |- forall (H : let x : ?A := ?a in ?T), ?G =>
      change (let x : A := a in forall H : T, G)
    | |- let H : (let x : ?A := ?a in ?T) := ?t in ?G =>
      change (let x : A := a in let H : T := t in G)
    | |- let H : ?T := (let x : ?A := ?a in ?t) in ?G =>
      change (let x : A := a in let H : T := t in G)
    | _ => fail "[let]: top assumption type or body is not a 'let'"
  end)) (at level 0, only parsing) : ssripat_scope.

Notation "'[' 'fix' ']'" := (ltac:(
  match goal with
  | |- context [?t] =>
    is_fix t; let f := fresh "fix" in set f := t; move: @f => /[hide]
  | _ => fail 1 "[fix]: no visible 'fix' in goal"
  end)) (at level 0, only parsing) : ssripat_scope.

Notation "'[' 'cofix' ']'" := (ltac:(
  match goal with
  | |- context [?t] =>
    is_cofix t; let z := fresh "cofix" in set z := t; move: @z => /[hide]
  | _ => fail 1 "[cofix]: no visible 'cofix' in goal"
  end)) (at level 0, only parsing) : ssripat_scope.


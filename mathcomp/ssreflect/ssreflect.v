(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From Coq Require Export ssreflect.
Global Set SsrOldRewriteGoalsOrder.
Global Set Asymmetric Patterns.
Global Set Bullet Behavior "None".

(******************************************************************************)
(* Local additions:                                                           *)
(*                                                                            *)
(* [elaborate x] == triggers coq elaboration to fill the holes of the term x  *)
(*                  The main use case is to trigger typeclass inference in    *)
(*                  the body of a ssreflect have := [elaborate body].         *)
(*                                                                            *)
(*   Intro pattern ltac views:                                                *)
(*   - calling rewrite from an intro pattern, use with parsimony              *)
(*     => /[1! rules]  := rewrite rules                                       *)
(*     => /[! rules]   := rewrite !rules                                      *)
(******************************************************************************)

Reserved Notation "[ 'elaborate' x ]" (at level 0).

Notation "[ 'elaborate' x ]" := (ltac:(refine x)) (only parsing).

Module Export ipat.

Notation "'[' '1' '!' rules ']'"     := (ltac:(rewrite rules))
  (at level 0, rules at level 200, only parsing) : ssripat_scope.
Notation "'[' '!' rules ']'"         := (ltac:(rewrite !rules))
  (at level 0, rules at level 200, only parsing) : ssripat_scope.

End ipat.

(* A class to trigger reduction by rewriting.                           *)
(* Usage: rewrite [pattern]vm_compute.                                  *)
(* Alternatively one may redefine a lemma as in algebra/rat.v :         *)
(* Lemma rat_vm_compute n (x : rat) : vm_compute_eq n%:Q x -> n%:Q = x. *)
(* Proof. exact. Qed.                                                   *)

Class vm_compute_eq {T : Type} (x y : T) := vm_compute : x = y.

#[global]
Hint Extern 0 (@vm_compute_eq _ _ _) =>
       vm_compute; reflexivity : typeclass_instances.

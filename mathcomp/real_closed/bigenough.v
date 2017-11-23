(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype.

(****************************************************************************)
(* This is a small library to do epsilon - N reasonning.                    *)
(* In order to use it, one only has to know the following tactics:          *)
(*                                                                          *)
(*      pose_big_enough i == pose a big enough natural number i             *)
(*   pose_big_modulus m F == pose a function m : F -> nat which should      *)
(*                           provide a big enough return value              *)
(* exists_big_modulus m F := pose_big_modulus m F; exists m                 *)
(*             big_enough == replaces a big enough constraint x <= i        *)
(*                           by true and implicity remembers that i should  *)
(*                           be bigger than x.                              *)
(*                close   == all "pose" tactics create a dummy subgoal to   *)
(*                           force the user to explictely indicate that all *)
(*                           constraints have been found                    *)
(****************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module BigEnough.

Record big_rel_class_of T (leq : rel T) := 
  BigRelClass {
      leq_big_internal_op : rel T;
      bigger_than_op : seq T -> T;
      _ : leq_big_internal_op = leq;
      _ : forall i s, leq_big_internal_op i (bigger_than_op (i :: s));
      _ : forall i j s, leq_big_internal_op i (bigger_than_op s) -> 
                        leq_big_internal_op i (bigger_than_op (j :: s))
}.

Record big_rel_of T := BigRelOf {
  leq_big :> rel T;
  big_rel_class : big_rel_class_of leq_big
}.

Definition bigger_than_of T (b : big_rel_of T)
           (phb : phantom (rel T) b) :=
  bigger_than_op (big_rel_class b).
Notation bigger_than leq := (@bigger_than_of _ _ (Phantom (rel _) leq)).

Definition leq_big_internal_of T (b : big_rel_of T)
           (phb : phantom (rel T) b) :=
  leq_big_internal_op (big_rel_class b).
Notation leq_big_internal leq := (@leq_big_internal_of _ _ (Phantom (rel _) leq)).

Lemma next_bigger_than T (b : big_rel_of T) i j s :
  leq_big_internal b i (bigger_than b s) -> 
  leq_big_internal b i (bigger_than b (j :: s)).
Proof. by case: b i j s => [? []]. Qed.

Lemma instantiate_bigger_than T (b : big_rel_of T) i s :
  leq_big_internal b i (bigger_than b (i :: s)).
Proof. by case: b i s => [? []]. Qed.

Lemma leq_big_internalE T (b : big_rel_of T) : leq_big_internal b = leq_big b.
Proof. by case: b => [? []]. Qed.

(* Lemma big_enough  T (b : big_rel_of T) i s : *)
(*   leq_big_internal b i (bigger_than b s) -> *)
(*   leq_big b i (bigger_than b s). *)
(* Proof. by rewrite leq_big_internalE. Qed. *)

Lemma context_big_enough P T (b : big_rel_of T) i s :
  leq_big_internal b i (bigger_than b s) ->
  P true ->
  P (leq_big b i (bigger_than b s)).
Proof. by rewrite leq_big_internalE => ->. Qed.

Definition big_rel_leq_class : big_rel_class_of leq.
Proof.
exists leq (foldr maxn 0%N) => [|i s|i j s /leq_trans->] //;
by rewrite (leq_maxl, leq_maxr).
Qed.
Canonical big_enough_nat := BigRelOf big_rel_leq_class.

Definition closed T (i : T) := {j : T | j = i}.
Ltac close :=  match goal with
                 | |- context [closed ?i] =>
                   instantiate (1 := [::]) in (Value of i); exists i
               end.

Ltac pose_big_enough i :=
  evar (i : nat); suff : closed i; first do
    [move=> _; instantiate (1 := bigger_than leq _) in (Value of i)].

Ltac pose_big_modulus m F :=
  evar (m : F -> nat); suff : closed m; first do
    [move=> _; instantiate (1 := (fun e => bigger_than leq _)) in (Value of m)].

Ltac exists_big_modulus m F := pose_big_modulus m F; first exists m.

Ltac olddone :=
   trivial; hnf; intros; solve
   [ do ![solve [trivial | apply: sym_equal; trivial]
         | discriminate | contradiction | split]
   | case not_locked_false_eq_true; assumption
   | match goal with H : ~ _ |- _ => solve [case H; trivial] end].

Ltac big_enough :=
  do ?[ apply context_big_enough;
        first do [do ?[ now apply instantiate_bigger_than
                      | apply next_bigger_than]]].

Ltac big_enough_trans :=
  match goal with
    | [leq_nm : is_true (?n <= ?m)%N |- is_true (?x <= ?m)] =>
        apply: leq_trans leq_nm; big_enough; olddone
    | _ => big_enough; olddone
  end.

Ltac done := do [olddone|big_enough_trans].

End BigEnough.

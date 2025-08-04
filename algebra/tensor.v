From HB Require Import structures.
From mathcomp Require Import ssreflect seq matrix bigop ssrbool eqtype choice.
From mathcomp Require Import fintype ssralg ssrnat ssrfun order finfun.

(******************************************************************************)
(* This file defines tensors.                                                 *)
(* For tensors we define:                                                     *)
(*       'T[R]_(us, ds) == the type of tensors with elements of type R,       *)
(*       'T_(us, ds)       contravariant dimensions us, and covariant         *)
(*                         dimensions ds, e.g. 'T[nat]_([:: 1; 3], [::]).     *)
(*                         The [R] is optional and can usually be ommited.    *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "''T_' ( us , ds )"
  (at level 0, us at level 2, ds at level 2, format "''T_' ( us ,  ds )").
Reserved Notation "''T[' R ]_ ( us , ds )"
  (at level 0, us at level 2, ds at level 2, format "''T[' R ]_ ( us ,  ds )").
  (* only parsing*)


Section TensorDef.

Context (us ds : seq nat) (K : Type).

Variant tensor : predArgType :=
  Tensor of 'M[K]_(\prod_(u <- us) u, \prod_(d <- ds) d).

Definition t_val T := let: Tensor g := T in g.

HB.instance Definition _ := [isNew for t_val].

Coercion t_val : tensor >-> matrix.

End TensorDef.


Notation "''T[' R ]_ ( us , ds )" := (tensor us ds R) (only parsing).
Notation "''T_' ( us , ds )" := 'T[_]_(us, ds).

Section SubtypeInstances.

Import Algebra.

Context (us ds : seq nat).
Local Notation "''T[' R ]" := 'T[R]_(us, ds).

HB.instance Definition _ (R : eqType) := [Equality of 'T[R] by <:].
HB.instance Definition _ (R : choiceType) := [Choice of 'T[R] by <:].
HB.instance Definition _ (R : countType) := [Countable of 'T[R] by <:].
HB.instance Definition _ (R : finType) := [Finite of 'T[R] by <:].

Lemma nmod_closed {m n} (R : nmodType) : @nmod_closed 'M[R]_(n, m) predT.
Proof. by []. Qed.
HB.instance Definition _ (R : nmodType) := SubChoice_isSubNmodule.Build
  _ _ 'T[R] (nmod_closed R).

Lemma zmod_closed {m n} (R : zmodType) : @zmod_closed 'M[R]_(n, m) predT.
Proof. by []. Qed.
HB.instance Definition _ (R : zmodType) := SubChoice_isSubZmodule.Build
  _ _ 'T[R] (zmod_closed R).

Lemma subsemimod_closed {m n} (R : pzSemiRingType)
  : @subsemimod_closed R 'M[R]_(n, m) predT.
Proof. by []. Qed.
HB.instance Definition _ (R : pzSemiRingType) := 
  GRing.SubNmodule_isSubLSemiModule.Build _ _ _ 'T[R] (subsemimod_closed R).

Lemma submod_closed {m n} (R : pzRingType) : @submod_closed R 'M[R]_(n, m) predT.
Proof. by []. Qed.
HB.instance Definition _ (R : pzRingType) := 
  GRing.SubZmodule_isSubLmodule.Build _ _ _ 'T[R] (submod_closed R).

End SubtypeInstances.


Definition const_t {R us ds} (v : R) : 'T[R]_(us, ds) :=
  Tensor (const_mx v).


Section IndexTensor.

Context (R : Type) (u d : nat) (us ds : seq nat).

Open Scope ring_scope.

Lemma tensormx_cast {x xs} : #|{:'I_x * 'I_\prod_(e <- xs) e}| = \prod_(e <- x :: xs) e.
Proof. by rewrite card_prod !card_ord big_cons. Qed.

Definition tensormx_index {x xs} (i : 'I_x) (j : 'I_\prod_(e <- xs) e) 
  : 'I_\prod_(e <- x :: xs) e :=
  cast_ord tensormx_cast (enum_rank (i, j)).

Definition upper_index (t : 'T[R]_(u :: us, ds)) (i : 'I_u) : 'T[R]_(us, ds) :=
  Tensor (rowsub (tensormx_index i) t).

Definition lower_index (t : 'T[R]_(us, d :: ds)) (i : 'I_d) : 'T[R]_(us, ds) :=
  Tensor (colsub (tensormx_index i) t).

Definition upper_stack (f : 'I_u -> 'T[R]_(us, ds)) : 'T[R]_(u :: us, ds) := 
  Tensor (castmx (tensormx_cast, erefl) (\matrix_(i, j) f (enum_val i).1 (enum_val i).2 j)).

Definition lower_stack (f : 'I_d -> 'T[R]_(us, ds)) : 'T[R]_(us, d :: ds) :=
  Tensor (castmx (erefl, tensormx_cast) (\matrix_(i, j) f (enum_val j).1 i (enum_val j).2)).

End IndexTensor.


Section NilTensor.

Context (R : Type).

Lemma ord_nil : 0 < \prod_(x <- [::]) x.
Proof. by rewrite big_nil. Qed.

Definition tensor_nilE (t : 'T[R]_([::], [::])) : R := 
  t (Ordinal ord_nil) (Ordinal ord_nil).

End NilTensor.


Section TensorRing.

Import GRing.Theory.

Context (us ds : seq nat).
Local Notation "''T[' R ]" := 'T[R]_(us, ds).

Section TensorPzSemiRing.

Context {R : pzSemiRingType}.

Definition tensor1 := @const_t _ us ds (GRing.one R).

Definition mult (t u : 'T[R]_(us, ds)) := @Tensor us ds R (map2_mx *%R t u).

Lemma multA : associative mult.
Proof. by move=> x y z; rewrite /mult map2_mxA. Qed.
Lemma mul1t : left_id tensor1 mult.
Proof. by move=> [x]; rewrite /mult map2_1mx. Qed.
Lemma mult1 : right_id tensor1 mult.
Proof. by move=> [x]; rewrite /mult map2_mx1. Qed.
Lemma multDl : left_distributive mult +%R.
Proof. by move=> x y z; rewrite /mult map2_mxDl. Qed.
Lemma multDr : right_distributive mult +%R.
Proof. by move=> x y z; rewrite /mult map2_mxDr. Qed.
Lemma mul0t : left_zero 0%R mult.
Proof. by move=> x; rewrite /mult map2_0mx. Qed.
Lemma mult0 : right_zero 0%R mult.
Proof. by move=> x; rewrite /mult map2_mx0. Qed.

HB.instance Definition _ := GRing.Nmodule_isPzSemiRing.Build
  'T[R] multA mul1t mult1 multDl multDr mul0t mult0.

End TensorPzSemiRing.

Lemma multC {R : comPzSemiRingType} : commutative (@mult R).
Proof. by move=> x y; rewrite /mult map2_mxC. Qed.

HB.instance Definition _ {R : comPzSemiRingType} := 
  GRing.Nmodule_isComPzSemiRing.Build 
  'T[R] multA multC mul1t multDl mul0t.

HB.instance Definition _ {R : pzRingType} := GRing.Zmodule_isPzRing.Build
  'T[R] multA mul1t mult1 multDl multDr.

HB.instance Definition _ {R : comPzRingType} := 
  GRing.PzRing_hasCommutativeMul.Build 'T[R] multC.

Section TensorNz.

Lemma prod_gt_0 {xs} (xs_gt_0 : all (leq 1) xs) : 0 < \prod_(e <- xs) e.
Proof.
elim: xs xs_gt_0=> [_|u us' Hind /andP [u_gt_0 us'_gt_0]].
  by rewrite big_nil.
rewrite big_cons muln_gt0.
apply/andP; split=>//.
exact (Hind us'_gt_0).
Qed.

Context (us_gt_0 : all (leq 1) us) (ds_gt_0 : all (leq 1) ds).

Lemma onet_neq0 {R : nzSemiRingType} : (1%R : 'T[R]) != 0%R.
Proof.
rewrite /GRing.one/GRing.zero /= /tensor1/const_t /Sub/GRing.zero /=.
apply/eqP. case. apply/matrixP. rewrite /const_mx/eqrel.
case: (\prod_(u <- us) u) (prod_gt_0 us_gt_0)=> [//|n0 _].
case: (\prod_(d <- ds) d) (prod_gt_0 ds_gt_0)=> [//|n1 _ H].
move: (H ord0 ord0).
rewrite matrix_of_fun.unlock /fun_of_matrix 2!ffunE.
apply/eqP.
exact (oner_neq0 R).
Qed.

HB.instance Definition _ {R : nzSemiRingType} := 
  GRing.PzSemiRing_isNonZero.Build
  'T[R] onet_neq0.

HB.instance Definition _ {R : comNzSemiRingType} := 
  GRing.Nmodule_isComNzSemiRing.Build
  'T[R] multA multC mul1t multDl mul0t onet_neq0.

HB.instance Definition _ {R : nzRingType} := GRing.Zmodule_isNzRing.Build
  'T[R] multA mul1t mult1 multDl multDr onet_neq0.

HB.instance Definition _ {R: comNzRingType} := GRing.Zmodule_isComNzRing.Build
  'T[R] multA multC mul1t multDl onet_neq0.

End TensorNz.

End TensorRing.


Section TensorPOrder.

Import Order.POrderTheory.
Open Scope order_scope.

Context (o : Order.disp_t) (R : porderType o) (us ds : seq nat).

Definition le_t (t u : 'T[R]_(us, ds)) := 
  [forall ij, (t ij.1 ij.2) <= (u ij.1 ij.2)].

Definition lt_t (t u : 'T[R]_(us, ds)) := (u != t) && le_t t u.

Lemma lt_t_def : forall x y, lt_t x y = (y != x) && le_t x y.
Proof. by []. Qed.

Lemma le_t_refl : reflexive (le_t).
Proof.
move=> x; rewrite /le_t.
apply /forallP=> ij.
by apply le_refl.
Qed.

Lemma le_t_anti : antisymmetric (le_t).
Proof.
move=> x y; rewrite /le_t=> /andP [/forallP le_t_xy /forallP le_t_yx].
apply /eqP; rewrite /eq_op/=; apply/eqP/matrixP.
rewrite /eqrel=> i j.
apply /le_anti/andP; split.
- exact (le_t_xy (i, j)).
- exact (le_t_yx (i, j)). 
Qed.

Lemma le_t_trans : transitive (le_t).
Proof.
move=> x y z; rewrite /le_t=> /forallP le_t_yx /forallP le_t_xz.
apply/forallP=> ij.
exact /le_trans.
Qed.

HB.instance Definition _ := Order.isPOrder.Build
  o 'T[R]_(us, ds) lt_t_def le_t_refl le_t_anti le_t_trans.

End TensorPOrder.
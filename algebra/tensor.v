From HB Require Import structures.
From mathcomp Require Import ssreflect seq matrix bigop ssrbool eqtype choice.
From mathcomp Require Import fintype ssralg ssrnat ssrfun order finfun tuple.

(******************************************************************************)
(* This file defines tensors.                                                 *)
(* For tensors we define:                                                     *)
(*       'T[R]_(us, ds) == the type of tensors with elements of type R,       *)
(*       'T_(us, ds)       contravariant dimensions us, and covariant         *)
(*                         dimensions ds, e.g. 'T[nat]_([:: 1; 3], [::]).     *)
(*                         The [R] is optional and can usually be ommited.    *)
(* 'nT[R]_(us), 'nT_(us) == 'T[R]_(us, [::]), purely contravariant tensors.   *)
(* 'oT[R]_(ds), 'oT_(ds) == 'T[R]_([::], ds), purely covariant tensors.       *)
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


Reserved Notation "''nT_' ( us )"
  (at level 0, us at level 2, format "''nT_' ( us )").
Reserved Notation "''oT_' ( ds )"
  (at level 0, ds at level 2, format "''oT_' ( ds )").
Reserved Notation "''nT[' R ]_ ( us )" (at level 0, us at level 2).
  (* only parsing *)
Reserved Notation "''oT[' R ]_ ( ds )" (at level 0, ds at level 2).
  (* only parsing *)
Reserved Notation "''T_' ( us , ds )"
  (at level 0, us at level 2, ds at level 2, format "''T_' ( us ,  ds )").
Reserved Notation "''T[' R ]_ ( us , ds )"
  (at level 0, us at level 2, ds at level 2). (* only parsing*)

Reserved Notation "t ^^ i"
  (at level 3, i at level 2, left associativity, format "t ^^ i").
Reserved Notation "t `_ i"
  (at level 3, i at level 2, left associativity, format "t `_ i").
Reserved Notation "t ^^= i"
  (at level 3, i at level 2, left associativity, format "t ^^= i").
Reserved Notation "t `_= i"
  (at level 3, i at level 2, left associativity, format "t `_= i").

Reserved Notation "\tensor ^^ i E"
  (at level 34, E at level 39, i at level 2, format "\tensor ^^ i  E").
Reserved Notation "\tensor `_ i E"
  (at level 34, E at level 39, i at level 2, format "\tensor `_ i  E").
Reserved Notation "\tensor ^^ ( i < u ) E"
  (E at level 39, i, u at level 50). (* only parsing *)
Reserved Notation "\tensor `_ ( i < d ) E"
  (E at level 39, i, d at level 50). (* only parsing *)
Reserved Notation "\tensor ^^ i => E"
  (at level 34, E at level 39, i at level 2, format "\tensor ^^ i  =>  E").
Reserved Notation "\tensor `_ i => E"
  (at level 34, E at level 39, i at level 2, format "\tensor `_ i  =>  E").
Reserved Notation "\tensor ^^ ( i < u ) => E"
  (E at level 39, i, u at level 50). (* only parsing *)
Reserved Notation "\tensor `_ ( i < d ) => E"
  (E at level 39, i, d at level 50). (* only parsing *) 


Section TensorDef.

Context (us ds : seq nat) (K : Type).

Variant tensor : predArgType :=
  Tensor of 'M[K]_(\prod_(u <- us) u, \prod_(d <- ds) d).

Definition t_val T := let: Tensor g := T in g.

HB.instance Definition _ := [isNew for t_val].

End TensorDef.


Notation "''T[' R ]_ ( us , ds )" := (tensor us ds R) (only parsing).
Notation "''T_' ( us , ds )" := 'T[_]_(us, ds).
Notation "''nT[' R ]_ ( us )" := 'T[R]_(us, [::]) (only parsing).
Notation "''oT[' R ]_ ( ds )" := 'T[R]_([::], ds) (only parsing).
Notation "''oT_' ( ds )" := 'T_([::], ds).
Notation "''nT_' ( us )" := 'T_(us, [::]).


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


Section NilTensor.

Context (R : Type).

Lemma ord_nil : 0 < \prod_(x <- [::]) x.
Proof. by rewrite big_nil. Qed.

Definition tensor_nilE (t : 'T[R]_([::], [::])) : R := 
  \val t (Ordinal ord_nil) (Ordinal ord_nil).

Definition const_tK : cancel const_t tensor_nilE.
Proof. 
move=> t; rewrite /tensor_nilE/const_t/const_mx/=. 
by rewrite matrix_of_fun.unlock /fun_of_matrix ffunE.
Qed.

End NilTensor.


Section IndexTensor.

Section IndexTensorBij.

Context {x : nat} {xs : seq nat}.

Lemma tensormx_cast
: #|{:'I_x * 'I_\prod_(e <- xs) e}| = \prod_(e <- x :: xs) e.
Proof. by rewrite card_prod !card_ord big_cons. Qed.

Definition tensormx_index (ij : 'I_x * 'I_\prod_(e <- xs) e) 
  : 'I_\prod_(e <- x :: xs) e :=
  cast_ord tensormx_cast (enum_rank ij).

Definition tensormx_unindex (i : 'I_\prod_(e <- x :: xs) e)
  : 'I_x * 'I_\prod_(e <- xs) e :=
  enum_val (cast_ord (esym tensormx_cast) i).

Lemma tensormx_indexK : cancel tensormx_index tensormx_unindex.
Proof.
by move=> ij; rewrite /tensormx_index/tensormx_unindex cast_ordK enum_rankK.
Qed.

Lemma tensormx_unindexK : cancel tensormx_unindex tensormx_index.
Proof.
by move=> i; rewrite /tensormx_index/tensormx_unindex enum_valK cast_ordKV.
Qed.

End IndexTensorBij.

Context (R : Type) (u d : nat) (us ds : seq nat).

Open Scope ring_scope.

Definition nindex (t : 'T[R]_(u :: us, ds)) (i : 'I_u) : 'T[R]_(us, ds) :=
  Tensor (\matrix_(i', j) (\val t) (tensormx_index (i, i')) j).  

Definition oindex (t : 'T[R]_(us, d :: ds)) (j : 'I_d) : 'T[R]_(us, ds) :=
  Tensor (\matrix_(i, j') (\val t) i (tensormx_index (j, j'))).

Definition nstack (f : 'I_u -> 'T[R]_(us, ds)) : 'T[R]_(u :: us, ds) := 
  Tensor (
    \matrix_(i, j) \val (f (tensormx_unindex i).1) (tensormx_unindex i).2 j).

Definition ostack (f : 'I_d -> 'T[R]_(us, ds)) : 'T[R]_(us, d :: ds) :=
  Tensor (
    \matrix_(i, j) \val (f (tensormx_unindex j).1) i (tensormx_unindex j).2).

End IndexTensor.


Notation "t ^^ i" := (nindex t i).
Notation "t `_ i" := (oindex t i).
Notation "t ^^= i" := (tensor_nilE (nindex t i)).
Notation "t `_= i" := (tensor_nilE (oindex t i)).

Notation "\tensor ^^ ( i < u ) E" := (nstack (fun i : 'I_u => E)) 
  (only parsing).
Notation "\tensor `_ ( i < d ) E" := (ostack (fun i : 'I_d => E)) 
  (only parsing).
Notation "\tensor ^^ i E" := (\tensor^^(i < _) E).
Notation "\tensor `_ i E" := (\tensor`_(i < _) E).
Notation "\tensor ^^ ( i < u ) => E" := (\tensor^^(i < u) const_t E) 
  (only parsing).
Notation "\tensor `_ ( i < d ) => E" := (\tensor`_(i < d) const_t E) 
  (only parsing).
Notation "\tensor ^^ i => E" := (\tensor^^i const_t E).
Notation "\tensor `_ i => E" := (\tensor`_i const_t E).


Section TensorIndexTheory.

Context (R : Type).

Lemma ntensorP {u us ds} (t v : 'T[R]_(u :: us, ds)) 
  : t = v <-> forall i, t^^i = v^^i.
Proof.
split=> [->//|ti_eq_vi]; apply/val_inj/matrixP=> i j.
move: (ti_eq_vi (tensormx_unindex i).1).
move=> [/matrixP] /(_ (tensormx_unindex i).2 j).
rewrite matrix_of_fun.unlock /fun_of_matrix !ffunE/=.
by rewrite -surjective_pairing tensormx_unindexK.
Qed.

Lemma otensorP {us d ds} (t v : 'T[R]_(us, d :: ds))
  : t = v <-> forall i, t`_i = v`_i.
Proof.
split=> [->//|ti_eq_vi]; apply/val_inj/matrixP=> i j.
move: (ti_eq_vi (tensormx_unindex j).1).
move=> [/matrixP] /(_ i (tensormx_unindex j).2).
rewrite matrix_of_fun.unlock /fun_of_matrix !ffunE/=.
by rewrite -surjective_pairing tensormx_unindexK.
Qed.

Lemma nstackE {u us ds} (f : 'I_u -> 'T[R]_(us, ds)) i : (nstack f)^^i = f i.
Proof.
case (f i) eqn:fi_def.
rewrite /nstack/nindex.
apply/congr1/matrixP=> x y.
by rewrite matrix_of_fun.unlock /fun_of_matrix !ffunE tensormx_indexK fi_def.
Qed.

Lemma ostackE {us d ds} (f : 'I_d -> 'T[R]_(us, ds)) i : (ostack f)`_i = f i.
Proof.
case (f i) eqn:fi_def.
rewrite /ostack/oindex.
apply/congr1/matrixP=> x y.
by rewrite matrix_of_fun.unlock /fun_of_matrix !ffunE tensormx_indexK fi_def.
Qed.

Lemma nstack_eqE {u} (f : 'I_u -> R) i : (\tensor^^i0 => f i0)^^=i = f i.
Proof. by rewrite nstackE const_tK. Qed.

Lemma ostack_eqE {d} (f : 'I_d -> R) i : (\tensor`_i0 => f i0)`_=i = f i.
Proof. by rewrite ostackE const_tK. Qed.

End TensorIndexTheory.


Section TensorRing.

Context (t : 'T[nat]_([:: 2; 4], [:: 6])).

Import GRing.Theory.

Context (us ds : seq nat).
Local Notation "''T[' R ]" := 'T[R]_(us, ds).

Section TensorSemiRing.

Context {R : pzSemiRingType}.

Definition tensor1 := @const_t _ us ds (GRing.one R).

Definition mult (t u : 'T[R]_(us, ds)) :=
  @Tensor us ds R (map2_mx *%R (\val t) (\val u)).

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

End TensorSemiRing.

Lemma multC {R : comPzSemiRingType} : @commutative 'T[R] _ mult.
Proof. by move=> x y; rewrite /mult map2_mxC. Qed.

HB.instance Definition _ {R : pzRingType} := GRing.Zmodule_isPzRing.Build
  'T[R] multA mul1t mult1 multDl multDr.

HB.instance Definition _ {R : comPzRingType} := 
  GRing.PzRing_hasCommutativeMul.Build 'T[R] multC.

Section TensorNz.

Lemma prod_gt_0 {xs} : all (leq 1) xs -> 0 < \prod_(e <- xs) e.
Proof.
elim: xs=> [_|x xs' IH /andP[xgt0 xs'gt0]]; first by rewrite big_nil.
by rewrite big_cons muln_gt0 xgt0/= IH.
Qed.

Context (us_gt_0 : all (leq 1) us) (ds_gt_0 : all (leq 1) ds).

Lemma onet_neq0 {R : nzSemiRingType} : (1%R : 'T[R]) != 0%R.
Proof.
rewrite /GRing.one/GRing.zero /= /tensor1/const_t /Sub/GRing.zero /=.
apply/eqP; case; apply/matrixP; rewrite /const_mx/eqrel.
case: (\prod_(u <- us) u) (prod_gt_0 us_gt_0)=> [//|n0 _] /(_ ord0).
case: (\prod_(d <- ds) d) (prod_gt_0 ds_gt_0)=> [//|n1 _] /(_ ord0).
by rewrite unlock /fun_of_matrix 2!ffunE; apply/eqP/oner_neq0.
Qed.

HB.instance Definition _ {R : nzSemiRingType} := 
  GRing.PzSemiRing_isNonZero.Build
  'T[R] onet_neq0.

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
  [forall ij, (\val t ij.1 ij.2) <= (\val u ij.1 ij.2)].

Definition lt_t (t u : 'T[R]_(us, ds)) := (u != t) && le_t t u.

Lemma lt_t_def : forall x y, lt_t x y = (y != x) && le_t x y.
Proof. by []. Qed.

Lemma le_t_refl : reflexive (le_t).
Proof. by move=> x; exact /forallP. Qed.

Lemma le_t_anti : antisymmetric (le_t).
Proof.
move=> x y /andP[/forallP le_t_xy /forallP le_t_yx].
apply /eqP; rewrite /eq_op/=; apply/eqP/matrixP.
rewrite /eqrel=> i j.
apply /le_anti/andP; split.
- exact (le_t_xy (i, j)).
- exact (le_t_yx (i, j)). 
Qed.

Lemma le_t_trans : transitive (le_t).
Proof.
move=> x y z /forallP le_t_yx /forallP le_t_xz.
apply/forallP=> ij; exact /le_trans.
Qed.

HB.instance Definition _ := Order.isPOrder.Build
  o 'T[R]_(us, ds) lt_t_def le_t_refl le_t_anti le_t_trans.

End TensorPOrder.


Section TensorTuple.

Context {R : Type} (x : nat).

Definition ntensor_of_tuple (t : x.-tuple R) : 'nT[R]_([:: x]) :=
  \tensor^^i => (tnth t i).

Definition otensor_of_tuple (t : x.-tuple R) : 'oT[R]_([:: x]) :=
  \tensor`_i => (tnth t i).

Lemma ntensor_of_tupleE t i : (ntensor_of_tuple t)^^= i = tnth t i.
Proof. exact /nstack_eqE. Qed.

End TensorTuple.
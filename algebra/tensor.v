From HB Require Import structures.
From mathcomp Require Import ssreflect seq matrix bigop ssrbool eqtype choice.
From mathcomp Require Import fintype ssralg ssrnat ssrfun order finfun tuple.

(******************************************************************************)
(* This file defines tensors,                                                 *)
(* For tensors we define:                                                     *)
(*                 pseq == the type of sequences of strictly positive natural *)
(*                         numbers, coerces to and from seq.                  *)
(*       'T[R]_(us, ds) == the type of tensors with elements of type R,       *)
(*       'T_(us, ds)       contravariant dimensions us, and covariant         *)
(*                         dimensions ds, e.g. 'T[nat]_([:: 1; 3], [::])      *)
(*                         (us and ds must be instances of pseq).             *)
(*                         The [R] is optional and can usually be ommited.    *)
(* 'nT[R]_(us), 'nT_(us) == 'T[R]_(us, [::]), purely contravariant tensors.   *)
(* 'oT[R]_(ds), 'oT_(ds) == 'T[R]_([::], ds), purely covariant tensors.       *)
(*                  t^^i == the tensor obtained by fixing the first           *)
(*                          contravariant dimension of t to i.                *)
(*                  t`_i == the tensor obtained by fixing the first           *)
(*                          covariant dimension of t to i.                    *)
(* \tensor^^(i < n) Expr(i) ==                                                *)
(*                         the 'T_(n :: _, _) tensor t such that              *)
(*                         t^^i = Expr(i) with i : 'I_n, the < n bound can    *)
(*                         usually be ommitted.                               *)
(* \tensor`_(j < n) Expr(j) ==                                                *)
(*                         the 'T_(_, n :: _) tensor t such that              *)
(*                         t`_j = Expr(j) with j : 'I_n, the < n bound can    *)
(*                         usually be ommitted.                               *)
(*            const_t v == the constant tensor whose entries are all v        *)
(*                         (dimensions are inferred from context)             *)
(*               t.[::] == the value of the single entry in a                 *)
(*                         tensor t : 'T_([::], [::]).                        *)
(*         t^^=i, t`_=i == variants of the indexing operations equivalent to  *)
(*                         (t^^i).[::], (t`_i).[::], useful for indexing the  *)
(*                         final dimnsions of tensors.                        *)
(* \tensor^^(i < n) => Expr(i), \tensor`_(j < n) => Expr(j) ==                *)
(*                         variant constructor equivalent to                  *)
(*                         \tensor^^(i < n) const_t Expr(i).                  *)
(* [tensor^^ t_0; ...; t_n], [tensor`_ t_0; ...; t_n] ==                      *)
(*                         construction of a tensor from a sequence of        *)
(*                         tensors.                                           *)
(* [tensor^^= x_0; ...; x_n], [tensor`_= x_0; ...; x_n] ==                    *)
(*                         construction of a tensor from a sequence of values.*)
(* Tensors are instances of subType of matrix, and inherit all combinatorial  *)
(* structures (including finType), as well as nmodType, zmodType,             *)
(* lSemiModType, lModType.                                                    *)
(*   Tensors also implement a pointwise partial ordering, as well as          *)
(* ring instances where the underlying type satisfies that instance.          *)
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
  (at level 34, E at level 39, i binder, format "\tensor ^^ i  E").
Reserved Notation "\tensor `_ i E"
  (at level 34, E at level 39, i binder, format "\tensor `_ i  E").
Reserved Notation "\tensor ^^ ( i < u ) E"
  (E at level 39, i, u at level 50). (* only parsing *)
Reserved Notation "\tensor `_ ( i < d ) E"
  (E at level 39, i, d at level 50). (* only parsing *)
Reserved Notation "\tensor ^^ i => E"
  (at level 34, E at level 39, i binder, format "\tensor ^^ i  =>  E").
Reserved Notation "\tensor `_ i => E"
  (at level 34, E at level 39, i binder, format "\tensor `_ i  =>  E").
Reserved Notation "\tensor ^^ ( i < u ) => E"
  (E at level 39, i, u at level 50). (* only parsing *)
Reserved Notation "\tensor `_ ( i < d ) => E"
  (E at level 39, i, d at level 50). (* only parsing *)

Reserved Notation "[ 'tensor' ^^ t ; .. ; tn ]"
  (format "[ 'tensor' ^^ '['  t ; '/'  .. ; '/'  tn ']' ]").
Reserved Notation "[ 'tensor' `_ t ; .. ; tn ]"
  (format "[ 'tensor' `_ '['  t ; '/'  .. ; '/'  tn ']' ]").
Reserved Notation "[ 'tensor' ^^= x ; .. ; xn ]"
  (format "[ 'tensor' ^^= '['  t ; '/'  .. ; '/'  tn ']' ]").
Reserved Notation "[ 'tensor' `_= x ; .. ; xn ]"
  (format "[ 'tensor' `_= '['  t ; '/'  .. ; '/'  tn ']' ]").

Reserved Notation "t .[::]".


Structure pseq : Type := PSeq {psval :> seq nat; _ : all (leq 1) psval}.

HB.instance Definition _ := [isSub for psval].

Canonical nil_pseq := PSeq (isT : all (leq 1) [::]).
Canonical cons_pseq p (ps : pseq) :=
  PSeq (valP ps : all (leq 1) (p.+1 :: ps)).



Section TensorDef.

Context (us ds : pseq) (K : Type).

Variant tensor_of : Type := 
  Tensor of 'M[K]_(\prod_(u <- us) u, \prod_(d <- ds) d).

Definition tval t := let: Tensor g := t in g.

HB.instance Definition _ := [isNew for tval].

End TensorDef.


Notation "''T[' R ]_ ( us , ds )" := (tensor_of us ds R) (only parsing).
Notation "''T_' ( us , ds )" := 'T[_]_(us, ds).
Notation "''nT[' R ]_ ( us )" := 'T[R]_(us, [::]) (only parsing).
Notation "''oT[' R ]_ ( ds )" := 'T[R]_([::], ds) (only parsing).
Notation "''oT_' ( ds )" := 'oT[_]_(ds).
Notation "''nT_' ( us )" := 'nT[_]_(us).


Section SubtypeInstances.

Import Algebra.

Context (us ds : pseq).
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


Section TensorPOrder.

Import Order.POrderTheory.
Open Scope order_scope.

Context (o : Order.disp_t) (R : porderType o) (us ds : pseq).

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
apply/val_inj/matrixP=> i j; apply /le_anti/andP.
exact (conj (le_t_xy (i, j)) (le_t_yx (i, j))).
Qed. 

Lemma le_t_trans : transitive (le_t).
Proof.
move=> x y z /forallP le_t_yx /forallP le_t_xz.
apply/forallP=> ij; exact /le_trans.
Qed.

HB.instance Definition _ := Order.isPOrder.Build
  o 'T[R]_(us, ds) lt_t_def le_t_refl le_t_anti le_t_trans.

End TensorPOrder.


Definition const_t {R us ds} (v : R) : 'T[R]_(us, ds) :=
  Tensor (const_mx v).


Section TensorRing.

Open Scope ring_scope.
Import GRing.Theory.

Context {us ds : pseq}.
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

Lemma prodn_gt0 (xs : pseq) : 0 < \prod_(e <- xs) e.
Proof.
case: xs; elim=> [?|x xs' IH /=/andP [x_gt0 xs'_gt0]]; first by rewrite big_nil.
rewrite big_cons muln_gt0; apply/andP; split=>//.
exact: (IH xs'_gt0).
Qed.

Lemma onet_neq0 {R : nzSemiRingType} : (1%R : 'T[R]) != 0%R.
Proof.
rewrite /GRing.one/GRing.zero /= /GRing.zero.
apply/eqP. case. apply/matrixP. rewrite /const_mx/eqrel.
case: (\prod_(u <- _)  u) (prodn_gt0 us)=> [//|n0 _] /(_ ord0).
case: (\prod_(d <- _)  d) (prodn_gt0 ds)=> [//|n1 _] /(_ ord0).
by rewrite !mxE; apply/eqP/oner_neq0.
Qed.

HB.instance Definition _ {R : nzSemiRingType} := 
  GRing.PzSemiRing_isNonZero.Build
  'T[R] onet_neq0.

HB.instance Definition _ {R : nzRingType} := GRing.Zmodule_isNzRing.Build
  'T[R] multA mul1t mult1 multDl multDr onet_neq0.

HB.instance Definition _ {R : comNzRingType} := GRing.Zmodule_isComNzRing.Build
  'T[R] multA multC mul1t multDl onet_neq0.

Definition unitt {R : unitRingType} (t : 'T[R]) :=
  [forall ij, (\val t ij.1 ij.2) \is a GRing.unit].

Definition invt {R : unitRingType} (t : 'T[R]) := 
  if t \in unitt then Tensor (map_mx GRing.inv (\val t)) else t.

Definition mulVt {R : unitRingType} : {in @unitt R, left_inverse 1%R invt *%R}.
Proof.
move=> t t_unit; apply/val_inj/matrixP=> i j/=.
rewrite /invt t_unit !mxE mulVr//=.
by move: t_unit; rewrite /unitt=> /forallP /(_ (i, j)).
Qed.

Definition divtt {R : unitRingType} : {in @unitt R, right_inverse 1%R invt *%R}.
Proof.
move=> t t_unit; apply/val_inj/matrixP=> i j/=.
rewrite /invt t_unit !mxE divrr//.
by move: t_unit; rewrite /unitt=> /forallP /(_ (i, j)).
Qed.

Definition unittP {R : unitRingType}
  : forall x y, y * x = 1%R /\ x * y = 1 -> @unitt R x.
Proof.
move=> x y [/eqP + /eqP]; rewrite /eq_op/==> /eqP/matrixP yx1 /eqP/matrixP xy1.
apply/forallP=> ij; apply/unitrP; exists (\val y ij.1 ij.2).
move: (conj (yx1 ij.1 ij.2) (xy1 ij.1 ij.2)).
by rewrite !mxE.
Qed.

Definition invt_out {R : unitRingType} : {in [predC @unitt R], invt =1 id}.
Proof. by move=> t /negbTE t_not_unit; rewrite /invt t_not_unit. Qed.

HB.instance Definition _ {R : unitRingType} :=
  GRing.NzRing_hasMulInverse.Build 'T[R] mulVt divtt unittP invt_out.

End TensorRing.


Section NilTensor.

Context (R : Type).

Lemma prod_nil : 1 = \prod_(e <- [::]) e.
Proof. by rewrite big_nil. Qed.

Lemma ord_prod_nil : all_equal_to (cast_ord prod_nil ord0).
Proof.
case=> [[?|n n_ord]]; apply: val_inj=>//=.
by move: n_ord; rewrite -prod_nil.
Qed.

Definition tensor_nil (t : 'T[R]_([::], [::])) : R := 
  \val t (cast_ord prod_nil ord0) (cast_ord prod_nil ord0).

Definition const_tK : cancel const_t tensor_nil.
Proof. by move=> t; rewrite /tensor_nil mxE. Qed.

Definition tensor_nilK : cancel tensor_nil const_t.
Proof.
by move=> t; apply/val_inj/matrixP=> i j/=; rewrite mxE !ord_prod_nil.
Qed.

End NilTensor.


Notation "t .[::]" := (tensor_nil t).


Section NilTensorTheory.

Lemma tensor_nil_eqP {R : Type} t u : t.[::] = u.[::] :> R <-> t = u.
Proof.
by split=> [?|->//]; apply/val_inj/matrixP=> i j; rewrite !ord_prod_nil.
Qed.

Open Scope order_scope.
Import Order.POrderTheory.

Lemma tensor_nil_leP {d : Order.disp_t} {R : porderType d} t u
  : t.[::] <= u.[::] :> R <-> t <= u.
Proof.
split=> [?|/forallP/(_ (cast_ord prod_nil ord0, cast_ord prod_nil ord0))//].
by apply/forallP=> [[] i j]; rewrite !ord_prod_nil.
Qed.

Lemma tensor_nil_ltP {d : Order.disp_t} {R : porderType d} t u
  : t.[::] < u.[::] :> R <-> t < u.
Proof.
rewrite !lt_def; split=> /andP [u_neq_t t_le_u]; apply/andP; split.
      by apply/contra_neq; first apply (tensor_nil_eqP u t).
    by apply/tensor_nil_leP.
  by apply/contra_neq; first apply (tensor_nil_eqP u t).
by apply/tensor_nil_leP.
Qed.

Close Scope order_scope.
Open Scope ring_scope.
Import GRing.Theory.

Lemma tensor_nilD {R : nmodType} t u
  : (t + u).[::] = t.[::] + u.[::] :> R.
Proof. by rewrite /tensor_nil mxE. Qed.

Lemma tensor_nilN {R : zmodType} t
  : (- t).[::] = - t.[::] :> R.
Proof. by rewrite /tensor_nil mxE. Qed.

Lemma tensor_nilM {R : pzSemiRingType} t u
  : (t * u).[::] = t.[::] * u.[::] :> R.
Proof. by rewrite /tensor_nil mxE. Qed.

Definition tensor_nilr_spec {R : pzRingType} := 
  (@tensor_nilM R, @tensor_nilN R, @tensor_nilD R).

Lemma tensor_nilV {R : unitRingType} t
  : (t^-1).[::] = t.[::]^-1 :> R.
Proof.
rewrite /tensor_nil {1}/GRing.inv/=/invt.
case (t \in @unitt [::] [::] R) eqn:t_unit; rewrite t_unit.
  by rewrite mxE.
apply/esym/invr_out; move: t_unit=> /negbT /forallP not_all_unit.
apply/negP=> ?; apply: not_all_unit=> ij.
by rewrite !ord_prod_nil.
Qed.

End NilTensorTheory.


Section ConstTensorTheory.

Context (us ds : pseq).

Open Scope ring_scope.
Import GRing.Theory.

Lemma const_tD {R : nmodType} x y
  : @const_t R us ds (x + y) = const_t x + const_t y.
Proof. by apply/val_inj/matrixP=> i j; rewrite !mxE. Qed.

Lemma const_tN {R : zmodType} x
  : @const_t R us ds (- x) = - const_t x.
Proof. by apply/val_inj/matrixP=> i j; rewrite !mxE. Qed.

Lemma const_tM {R : pzSemiRingType} x y
  : @const_t R us ds (x * y) = const_t x * const_t y.
Proof. by apply/val_inj/matrixP=> i j; rewrite !mxE. Qed.

Definition const_tr_spec {R : pzRingType} := 
  (@const_tM R, @const_tN R, @const_tD R).

Lemma const_tV {R : unitRingType} x
  : @const_t R us ds x^-1 = (const_t x)^-1.
Proof.
apply/val_inj/matrixP=> i j.
rewrite {2}/GRing.inv/=/invt.
case (const_t x \in @unitt us ds R) eqn:t_unit; rewrite !mxE=>//.
apply invr_out; move: t_unit=> /negbT /forallP not_all_unit.
apply/negP=> ?.
apply: not_all_unit=> ?.
by rewrite mxE.
Qed.

End ConstTensorTheory.


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
Proof. by move=> ij; rewrite /tensormx_unindex cast_ordK enum_rankK. Qed.

Lemma tensormx_unindexK : cancel tensormx_unindex tensormx_index.
Proof. by move=> i; rewrite /tensormx_index enum_valK cast_ordKV. Qed.

End IndexTensorBij.

Context (R : Type) (u d : nat) (us ds : pseq).

Open Scope ring_scope.

Definition nindex (t : 'T[R]_(u.+1 :: us, ds)) (i : 'I_u.+1) : 'T[R]_(us, ds) :=
  Tensor (\matrix_(i', j) (\val t) (tensormx_index (i, i')) j).  

Definition oindex (t : 'T[R]_(us, d.+1 :: ds)) (j : 'I_d.+1) : 'T[R]_(us, ds) :=
  Tensor (\matrix_(i, j') (\val t) i (tensormx_index (j, j'))).

Definition nstack (f : 'I_u.+1 -> 'T[R]_(us, ds)) : 'T[R]_(u.+1 :: us, ds) := 
  Tensor (
    \matrix_(i, j) \val (f (tensormx_unindex i).1) (tensormx_unindex i).2 j).

Definition ostack (f : 'I_d.+1 -> 'T[R]_(us, ds)) : 'T[R]_(us, d.+1 :: ds) :=
  Tensor (
    \matrix_(i, j) \val (f (tensormx_unindex j).1) i (tensormx_unindex j).2).

End IndexTensor.


Notation "t ^^ i" := (nindex t i).
Notation "t `_ i" := (oindex t i).
Notation "t ^^= i" := ((t^^i).[::]).
Notation "t `_= i" := ((t`_i).[::]).

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

Lemma ntensorP {u} {us ds : pseq} (t v : 'T[R]_(u.+1 :: us, ds)) 
  : t = v <-> forall i, t^^i = v^^i.
Proof.
split=> [->//|eq_i]; apply/val_inj/matrixP=> i j.
move: (eq_i (tensormx_unindex i).1)=> [/matrixP] /(_ (tensormx_unindex i).2 j).
by rewrite !mxE -surjective_pairing tensormx_unindexK.
Qed.

Lemma otensorP {d} {us ds : pseq} (t v : 'T[R]_(us, d.+1 :: ds))
  : t = v <-> forall i, t`_i = v`_i.
Proof.
split=> [->//|eq_i]; apply/val_inj/matrixP=> i j.
move: (eq_i (tensormx_unindex j).1)=> [/matrixP] /(_ i (tensormx_unindex j).2).
by rewrite !mxE -surjective_pairing tensormx_unindexK.
Qed.

Lemma ntensor_eqP {u} (t v : 'nT[R]_([:: u.+1]))
  : t = v <-> forall i, t^^=i = v^^=i.
Proof.
split=> [->//|eq_i]; apply/ntensorP=> i.
by move: (eq_i i)=> /tensor_nil_eqP.
Qed.

Lemma otensor_eqP {d} (t v : 'oT[R]_([:: d.+1]))
  : t = v <-> forall i, t`_=i = v`_=i.
Proof.
split=> [->//|eq_i]; apply/otensorP=> i.
by move: (eq_i i)=> /tensor_nil_eqP.
Qed.

Lemma nstackE {u us ds} (f : 'I_u.+1 -> 'T[R]_(us, ds)) i : (nstack f)^^i = f i.
Proof. by apply/val_inj/matrixP => x y; rewrite !mxE tensormx_indexK. Qed.

Lemma ostackE {us d ds} (f : 'I_d.+1 -> 'T[R]_(us, ds)) i : (ostack f)`_i = f i.
Proof. by apply/val_inj/matrixP => x y; rewrite !mxE tensormx_indexK. Qed.

Lemma nstack_eqE {u} (f : 'I_u.+1 -> R) i : (\tensor^^i0 => f i0)^^=i = f i.
Proof. by rewrite nstackE const_tK. Qed.

Lemma ostack_eqE {d} (f : 'I_d.+1 -> R) i : (\tensor`_i0 => f i0)`_=i = f i.
Proof. by rewrite ostackE const_tK. Qed.

End TensorIndexTheory.


Section TensorTuple.

Context {R : Type} (x : nat) (us ds : pseq).

Definition ntensor_of_tuple (t : x.+1.-tuple R) : 'nT[R]_([:: x.+1]) :=
  \tensor^^i => (tnth t i).

Definition otensor_of_tuple (t : x.+1.-tuple R) : 'oT[R]_([:: x.+1]) :=
  \tensor`_i => (tnth t i).

Lemma ntensor_of_tupleE t i : (ntensor_of_tuple t)^^=i = tnth t i.
Proof. exact: nstack_eqE. Qed.

Lemma otensor_of_tupleE t i : (otensor_of_tuple t)`_=i = tnth t i.
Proof. exact: ostack_eqE. Qed.

Definition nstack_tuple (t : x.+1.-tuple 'T[R]_(us, ds)) :=
  \tensor^^i tnth t i.

Definition ostack_tuple (t : x.+1.-tuple 'T[R]_(us, ds)) :=
  \tensor`_i tnth t i.

Lemma nstack_tupleE t i : (nstack_tuple t)^^i = tnth t i.
Proof. exact: nstackE. Qed.

Lemma ostack_tupleE t i : (ostack_tuple t)`_i = tnth t i.
Proof. exact: ostackE. Qed.

End TensorTuple.


Notation "[ 'tensor' ^^ t ; .. ; tn ]" :=
  (nstack_tuple [tuple of t :: .. [:: tn] ..]).
Notation "[ 'tensor' ^^= x ; .. ; xn ]" := 
  (ntensor_of_tuple [tuple of x :: .. [:: xn] ..]).
Notation "[ 'tensor' `_ t ; .. ; tn ]" :=
  (ostack_tuple [tuple of t :: .. [:: tn] ..]).
Notation "[ 'tensor' `_= x ; .. ; xn ]" := 
  (otensor_of_tuple [tuple of x :: .. [:: xn] ..]).


Section TensorMatrix.

Context {R : Type} {n m : nat}.

Definition tensor_of_matrix (M : 'M_(_, _)) : 'T[R]_([:: n.+1], [:: m.+1]) :=
  \tensor^^i \tensor`_j => M i j.

Definition matrix_of_tensor t : 'M[R]_(n.+1, m.+1) :=
  \matrix_(i, j) t^^i`_=j.

Lemma tensor_of_matrixK : cancel tensor_of_matrix matrix_of_tensor.
Proof. by move=> M; apply/matrixP=> i j; rewrite mxE nstackE ostack_eqE. Qed.

Lemma matrix_of_tensorK : cancel matrix_of_tensor tensor_of_matrix.
Proof.
move=> T; apply/ntensorP=> i; apply/otensor_eqP=> j.
by rewrite nstackE ostack_eqE mxE.
Qed.

End TensorMatrix.
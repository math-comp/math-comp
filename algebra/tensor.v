From HB Require Import structures.
From mathcomp Require Import ssreflect seq matrix bigop ssrbool eqtype choice.
From mathcomp Require Import fintype ssralg ssrnat ssrfun order finfun tuple.
From mathcomp Require Import finset sesquilinear.
From mathcomp Require Import interval interval_inference numdomain.
From Corelib Require Import ssreflect.

(******************************************************************************)
(* This file defines tensors,                                                 *)
(* For tensors we define:                                                     *)
(*       'T[R]_(u_, d_) == the type of tensors with elements of type R,       *)
(*       'T_(u_, d_)       contravariant dimensions u_, and covariant         *)
(*                         dimensions d_, where u_ and d_ are finite          *)
(*                         functions from ordinals to positive numbers        *)
(*                         ({posnum nat} ^ k and {posnum nat} ^ l resp.).     *)
(*                         The [R] is optional and can usually be omitted.    *)
(* 'nT[R]_(u_), 'nT_(u_) == purely contravariant tensors (no covariant dims). *)
(* 'oT[R]_(d_), 'oT_(d_) == purely covariant tensors (no contravariant dims). *)
(*                  t^^i == the tensor obtained by fixing the first           *)
(*                          contravariant dimension of t to i.                *)
(*                  t`_i == the tensor obtained by fixing the first           *)
(*                          covariant dimension of t to i.                    *)
(* \tensor^^(i < n) Expr(i) ==                                                *)
(*                         the 'T_(n :: _, _) tensor t such that              *)
(*                         t^^i = Expr(i) with i : 'I_n, the < n bound can    *)
(*                         usually be omitted.                               *)
(* \tensor`_(j < n) Expr(j) ==                                                *)
(*                         the 'T_(_, n :: _) tensor t such that              *)
(*                         t`_j = Expr(j) with j : 'I_n, the < n bound can    *)
(*                         usually be omitted.                               *)
(*            const_t v == the constant tensor whose entries are all v        *)
(*                         (dimensions are inferred from context)             *)
(*               t.[::] == the value of the single entry in a                 *)
(*                         tensor t : 'T_([::], [::]).                        *)
(*         t^^=i, t`_=i == variants of the indexing operations equivalent to  *)
(*                         (t^^i).[::], (t`_i).[::], useful for indexing the  *)
(*                         final dimensions of tensors.                       *)
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
(* NOTE: Ring multiplication ( *%R ) is the Hadamard (element-wise) product.  *)
(* Proper tensor product forms a bilinear structure.                          *)
(*                                                                            *)
(* Dimension notation:                                                        *)
(*  [dims n1; ..; nk] == posnum nat tuple from nat literals (only parsing),   *)
(*                        e.g. 'T[R]_([dims 2; 3], [dims 4]).                 *)
(*           [dims]    == empty dimension tuple (0.-tuple {posnum nat}).       *)
(*                                                                            *)
(* Tensor operations:                                                         *)
(* t *h u == Hadamard product of t and u (element-wise multiplication),       *)
(*           same as t * u (ring multiplication)                              *)
(* t *t u == proper tensor product: combines dimensions,                      *)
(*           'T_(u1, d1) * 'T_(u2, d2) -> 'T_(cat u1 u2, cat d1 d2)          *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Reserved Notation "''nT_' ( u_ )"
  (at level 0, u_ at level 2, format "''nT_' ( u_ )").
Reserved Notation "''oT_' ( d_ )"
  (at level 0, d_ at level 2, format "''oT_' ( d_ )").
Reserved Notation "''nT[' R ]_ ( u_ )" (at level 0, u_ at level 2).
  (* only parsing *)
Reserved Notation "''oT[' R ]_ ( d_ )" (at level 0, d_ at level 2).
  (* only parsing *)
Reserved Notation "''T_' ( u_ , d_ )"
  (at level 0, u_ at level 2, d_ at level 2, format "''T_' ( u_ ,  d_ )").
Reserved Notation "''T[' R ]_ ( u_ , d_ )"
  (at level 0, u_ at level 2, d_ at level 2). (* only parsing*)

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
  (format "[ 'tensor' ^^= '['  x ; '/'  .. ; '/'  xn ']' ]").
Reserved Notation "[ 'tensor' `_= x ; .. ; xn ]"
  (format "[ 'tensor' `_= '['  x ; '/'  .. ; '/'  xn ']' ]").

Reserved Notation "t .[::]".

Reserved Notation "*h%R" (at level 0).
Reserved Notation "x *h y"
  (at level 40, left associativity, format "x  *h  y").
Reserved Notation "*t%R" (at level 0).
Reserved Notation "x *t y"
  (at level 40, left associativity, format "x  *t  y").

(* Coercion from tuples to finfun: allows writing tensor dimensions as tuples *)
Coercion finfun_of_tuple : tuple_of >-> finfun_of.

(* Shorthand notation for posnum nat tuples used as tensor dimensions.
   These are only parsing: goals will display the underlying finfun form.
   Requires ring_scope for %:posnat elaboration. *)
Notation "[dims]" := ([tuple] : 0.-tuple {posnum nat}) (only parsing).
Local Open Scope ring_scope.
Notation "[dims x ; .. ; y ]" :=
  [tuple of x%:posnat :: .. [:: y%:posnat] ..] (only parsing).

Section TensorDef.

Definition tensor_nil_f := [ffun i : 'I_0 => 1%:posnat]%R.
Definition fcons {k : nat} {T : Type} (x : T) (f : 'I_k -> T) : T ^ k.+1 :=
  [ffun i => oapp f x (unlift ord0 i)].

Context {k l : nat} (u_ : {posnum nat} ^ k) (d_ : {posnum nat} ^ l) (K : Type).

Variant tensor : predArgType :=
  Tensor of 'M[K]_(\prod_(i < k) (u_ i)%:num, \prod_(j < l) (d_ j)%:num)%R.

Definition tensor_val T := let: Tensor g := T in g.

HB.instance Definition _ := [isNew for tensor_val].

End TensorDef.

Notation "''T[' R ]_ ( u_ , d_ )" := (tensor u_ d_ R) (only parsing).
Notation "''T_' ( u_ , d_ )" := 'T[_]_(u_, d_).
Notation "''nT[' R ]_ ( u_ )" := 'T[R]_(u_, tensor_nil_f) (only parsing).
Notation "''oT[' R ]_ ( d_ )" := 'T[R]_(tensor_nil_f, d_) (only parsing).
Notation "''oT_' ( d_ )" := 'oT[_]_(d_).
Notation "''nT_' ( u_ )" := 'nT[_]_(u_).

Import Algebra GRing.

Section SubtypeInstances.

Context {l k : nat} (u_ : {posnum nat} ^ k) (d_ : {posnum nat} ^ l).
Local Notation "''T[' R ]" := 'T[R]_(u_, d_).

HB.instance Definition _ (R : eqType) := [Equality of 'T[R] by <:].
HB.instance Definition _ (R : choiceType) := [Choice of 'T[R] by <:].
HB.instance Definition _ (R : countType) := [Countable of 'T[R] by <:].
HB.instance Definition _ (R : finType) := [Finite of 'T[R] by <:].

#[local] Fact nmod_closed {m n} (R : nmodType) : @nmod_closed 'M[R]_(n, m) predT.
Proof. by []. Qed.
HB.instance Definition _ (R : nmodType) := SubChoice_isSubNmodule.Build
  _ _ 'T[R] (nmod_closed R).

#[local] Fact zmod_closed {m n} (R : zmodType) : @zmod_closed 'M[R]_(n, m) predT.
Proof. by []. Qed.
HB.instance Definition _ (R : zmodType) := SubChoice_isSubZmodule.Build
  _ _ 'T[R] (zmod_closed R).

#[local] Fact subsemimod_closed {m n} (R : pzSemiRingType)
  : @subsemimod_closed R 'M[R]_(n, m) predT.
Proof. by []. Qed.
HB.instance Definition _ (R : pzSemiRingType) :=
  SubNmodule_isSubLSemiModule.Build _ _ _ 'T[R] (subsemimod_closed R).

#[local] Fact submod_closed {m n} (R : pzRingType) : @submod_closed R 'M[R]_(n, m) predT.
Proof. by []. Qed.
HB.instance Definition _ (R : pzRingType) :=
  GRing.SubChoice_isSubLmodule.Build _ _ _ 'T[R] (submod_closed R).

End SubtypeInstances.


Section TensorPOrder.

Import Order.POrderTheory.
Open Scope order_scope.

Context (o : Order.disp_t) (R : porderType o).
Context {l k : nat} (u_ : {posnum nat} ^ k) (d_ : {posnum nat} ^ l).

Definition le_t (t u : 'T[R]_(u_, d_)) := 
  [forall ij, (\val t ij.1 ij.2) <= (\val u ij.1 ij.2)].

Definition lt_t (t u : 'T[R]_(u_, d_)) := (u != t) && le_t t u.

#[local] Fact lt_t_def : forall x y, lt_t x y = (y != x) && le_t x y.
Proof. by []. Qed.

#[local] Fact le_t_refl : reflexive (le_t).
Proof. by move=> x; exact /forallP. Qed.

#[local] Fact le_t_anti : antisymmetric (le_t).
Proof.
move=> x y /andP[/forallP le_t_xy /forallP le_t_yx].
apply/val_inj/matrixP=> i j; apply /le_anti/andP.
exact (conj (le_t_xy (i, j)) (le_t_yx (i, j))).
Qed.

#[local] Fact le_t_trans : transitive (le_t).
Proof.
move=> x y z /forallP le_t_yx /forallP le_t_xz.
apply/forallP=> ij; exact /le_trans.
Qed.

HB.instance Definition _ := Order.isPOrder.Build
  o 'T[R]_(u_, d_) lt_t_def le_t_refl le_t_anti le_t_trans.

End TensorPOrder.


Definition const_t {R k l} {u_ : {posnum nat} ^ k} {d_ : {posnum nat} ^ l} (v : R) : 'T[R]_(u_, d_) :=
  Tensor (const_mx v).


Section TensorRing.

Open Scope ring_scope.
Import GRing.Theory.

Context {l k : nat} (u_ : {posnum nat} ^ k) (d_ : {posnum nat} ^ l).
Local Notation "''T[' R ]" := 'T[R]_(u_, d_).

Section TensorSemiRing.

Context {R : pzSemiRingType}.

Definition tensor1 := @const_t _ _ _ u_ d_ (GRing.one R).

(* Hadamard product: element-wise multiplication *)
Definition hmul (t u : 'T[R]_(u_, d_)) :=
  @Tensor _ _ u_ d_ R (map2_mx *%R (\val t) (\val u)).

#[local] Fact hmulA : associative hmul.
Proof. by move=> x y z; rewrite /hmul map2_mxA. Qed.
#[local] Fact hmul1t : left_id tensor1 hmul.
Proof. by move=> [x]; rewrite /hmul map2_1mx. Qed.
#[local] Fact hmul1 : right_id tensor1 hmul.
Proof. by move=> [x]; rewrite /hmul map2_mx1. Qed.
#[local] Fact hmulDl : left_distributive hmul +%R.
Proof. by move=> x y z; rewrite /hmul map2_mxDl. Qed.
#[local] Fact hmulDr : right_distributive hmul +%R.
Proof. by move=> x y z; rewrite /hmul map2_mxDr. Qed.
#[local] Fact hmul0t : left_zero 0%R hmul.
Proof. by move=> x; rewrite /hmul map2_0mx. Qed.
#[local] Fact hmul0 : right_zero 0%R hmul.
Proof. by move=> x; rewrite /hmul map2_mx0. Qed.

HB.instance Definition _ := GRing.Nmodule_isPzSemiRing.Build
  'T[R] hmulA hmul1t hmul1 hmulDl hmulDr hmul0t hmul0.

End TensorSemiRing.

#[local] Fact hmulC {R : comPzSemiRingType} : @commutative 'T[R] _ hmul.
Proof. by move=> x y; rewrite /hmul map2_mxC. Qed.

HB.instance Definition _ {R : pzRingType} := GRing.Zmodule_isPzRing.Build
  'T[R] hmulA hmul1t hmul1 hmulDl hmulDr.

HB.instance Definition _ {R : comPzRingType} := 
  SemiRing_hasCommutativeMul.Build 'T[R] hmulC.

#[local] Fact onet_neq0 {R : nzSemiRingType} : (1%R : 'T[R]) != 0%R.
Proof.
rewrite /GRing.one/GRing.zero /= /GRing.zero.
apply/eqP; case; apply/matrixP; rewrite /const_mx/eqrel.
case: (\prod_(i < k) (u_ i)%:num) (@prodn_gt0 _ (index_enum 'I_k) predT (fun i => (u_ i)%:num)) => [//|n0 _].
  suff : (forall i : 'I_k, 0 < (u_ i)%:posnum) by move=> /[swap] /[apply].
  by move => i; rewrite gtn0.
case: (\prod_(i < l) (d_ i)%:posnum) (@prodn_gt0 _ (index_enum 'I_l) predT (fun i => (d_ i)%:posnum)) => [//|n1 _].
  suff : (forall i : 'I_l, 0 < (d_ i)%:posnum) by move=> /[swap] /[apply].
  by move => i; rewrite gtn0.
by move=> /(_ ord0 ord0); rewrite !mxE; apply/eqP/oner_neq0.
Qed.

HB.instance Definition _ {R : nzSemiRingType} := 
  GRing.PzSemiRing_isNonZero.Build
  'T[R] onet_neq0.

HB.instance Definition _ {R : nzRingType} := GRing.Zmodule_isNzRing.Build
  'T[R] hmulA hmul1t hmul1 hmulDl hmulDr onet_neq0.

HB.instance Definition _ {R : comNzRingType} := GRing.Zmodule_isComNzRing.Build
  'T[R] hmulA hmulC hmul1t hmulDl onet_neq0.

Definition unitt {R : unitRingType} (t : 'T[R]) :=
  [forall ij, (\val t ij.1 ij.2) \is a GRing.unit].

Definition invt {R : unitRingType} (t : 'T[R]) := 
  if t \in unitt then Tensor (map_mx GRing.inv (\val t)) else t.

#[local] Fact mulVt {R : unitRingType} : {in @unitt R, left_inverse 1%R invt *%R}.
Proof.
move=> t t_unit; apply/val_inj/matrixP=> i j/=.
rewrite /invt t_unit !mxE mulVr//=.
by move: t_unit; rewrite /unitt=> /forallP /(_ (i, j)).
Qed.

#[local] Fact divtt {R : unitRingType} : {in @unitt R, right_inverse 1%R invt *%R}.
Proof.
move=> t t_unit; apply/val_inj/matrixP=> i j/=.
rewrite /invt t_unit !mxE divrr//.
by move: t_unit; rewrite /unitt=> /forallP /(_ (i, j)).
Qed.

#[local] Fact unittP {R : unitRingType}
  : forall x y, y * x = 1%R /\ x * y = 1 -> @unitt R x.
Proof.
move=> x y [/eqP + /eqP]; rewrite /eq_op/==> /eqP/matrixP yx1 /eqP/matrixP xy1.
apply/forallP=> ij; apply/unitrP; exists (\val y ij.1 ij.2).
move: (conj (yx1 ij.1 ij.2) (xy1 ij.1 ij.2)).
by rewrite !mxE.
Qed.

#[local] Fact invt_out {R : unitRingType} : {in [predC @unitt R], invt =1 id}.
Proof. by move=> t /negbTE t_not_unit; rewrite /invt t_not_unit. Qed.

HB.instance Definition _ {R : unitRingType} :=
  GRing.NzRing_hasMulInverse.Build 'T[R] mulVt divtt unittP invt_out.

End TensorRing.

(* Notations for Hadamard product *)
Notation "*h%R" := hmul : ring_scope.
Notation "x *h y" := (hmul x y) : ring_scope.

Section NilTensor.

Context (R : Type).

Lemma prod_nil : 1 = \prod_(i < 0) (tensor_nil_f i)%:num%R.
Proof. by rewrite big_ord0. Qed.

Lemma ord_prod_nil : all_equal_to (cast_ord prod_nil ord0).
Proof.
case=> [[?|n n_ord]]; apply: val_inj=>//=.
by move: n_ord; rewrite -prod_nil.
Qed.

Definition tensor_nil (t : @tensor 0 0 tensor_nil_f tensor_nil_f R) : R := 
  \val t (cast_ord prod_nil ord0) (cast_ord prod_nil ord0).

Definition const_tK : cancel const_t tensor_nil.
Proof. by move=> t; rewrite /tensor_nil mxE. Qed.

Definition tensor_nilK : cancel tensor_nil const_t.
Proof.
by move=> t; apply/val_inj/matrixP => i j; rewrite mxE !ord_prod_nil.
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
case (t \in @unitt _ _ tensor_nil_f tensor_nil_f R) eqn:t_unit; rewrite t_unit.
  by rewrite mxE.
apply/esym/invr_out; move: t_unit=> /negbT /forallP not_all_unit.
apply/negP=> ?; apply: not_all_unit=> ij.
by rewrite !ord_prod_nil.
Qed.

End NilTensorTheory.


Section ConstTensorTheory.

Context {l k : nat} (u_ : {posnum nat} ^ k) (d_ : {posnum nat} ^ l).

Open Scope ring_scope.
Import GRing.Theory.

Lemma const_tD {R : nmodType} x y
  : @const_t R _ _ u_ d_ (x + y) = const_t x + const_t y.
Proof. by apply/val_inj/matrixP=> i j; rewrite !mxE. Qed.

Lemma const_tN {R : zmodType} x
  : @const_t R _ _ u_ d_ (- x) = - const_t x.
Proof. by apply/val_inj/matrixP=> i j; rewrite !mxE. Qed.

Lemma const_tM {R : pzSemiRingType} x y
  : @const_t R _ _ u_ d_ (x * y) = const_t x * const_t y.
Proof. by apply/val_inj/matrixP=> i j; rewrite !mxE. Qed.

Definition const_tr_spec {R : pzRingType} := 
  (@const_tM R, @const_tN R, @const_tD R).

Lemma const_tV {R : unitRingType} x
  : @const_t R _ _ u_ d_ x^-1 = (const_t x)^-1.
Proof.
apply/val_inj/matrixP=> i j.
rewrite {2}/GRing.inv/=/invt.
case (const_t x \in @unitt _ _ u_ d_ R) eqn:t_unit; rewrite !mxE=>//.
apply invr_out; move: t_unit=> /negbT /forallP not_all_unit.
apply/negP=> ?.
apply: not_all_unit=> ?.
by rewrite mxE.
Qed.

End ConstTensorTheory.


Section IndexTensor.

Section IndexTensorBij.

Local Open Scope ring_scope.

Context {k : nat} (u_ : {posnum nat} ^ k).

Local Notation fprod_u := (fprod (fun i : 'I_k => 'I_(u_ i)%:num)).

Lemma card_fprod_u : #|fprod_u| = \prod_(i < k) (u_ i)%:num.
Proof. by rewrite card_fprod; apply: eq_bigr => i _; rewrite card_ord. Qed.


Definition tensor_index (f : fprod_u) : 'I_(\prod_(i < k) (u_ i)%:num) :=
  cast_ord card_fprod_u (enum_rank f).

Definition tensor_unindex (i : 'I_(\prod_(i < k) (u_ i)%:num)) : fprod_u :=
  enum_val (cast_ord (esym card_fprod_u) i).

Lemma tensor_indexK : cancel tensor_index tensor_unindex.
Proof. by move=> f; rewrite /tensor_index /tensor_unindex cast_ordK enum_rankK. Qed.

Lemma tensor_unindexK : cancel tensor_unindex tensor_index.
Proof. by move=> i; rewrite /tensor_index /tensor_unindex enum_valK cast_ordKV. Qed.

Lemma tensor_index_bij : bijective tensor_index.
Proof. by exists tensor_unindex;[exact: tensor_indexK|exact: tensor_unindexK]. Qed.

Definition tensor_dffun_index : 'I_(\prod_(i < k) (u_ i)%:num) ->
    {dffun forall i : 'I_k, 'I_(u_ i)%:num} :=
  @dffun_of_fprod _ _ \o tensor_unindex.

Definition tensor_dffun_unindex : {dffun forall i : 'I_k, 'I_(u_ i)%:num} ->
    'I_(\prod_(i < k) (u_ i)%:num) :=
  tensor_index \o @fprod_of_dffun _ _.

Lemma tensor_dffun_indexK : cancel tensor_dffun_index tensor_dffun_unindex.
Proof. by move=> i; rewrite /tensor_dffun_index /tensor_dffun_unindex/= dffun_of_fprodK tensor_unindexK. Qed.

Lemma tensor_dffun_unindexK : cancel tensor_dffun_unindex tensor_dffun_index.
Proof. by move=> f; rewrite /tensor_dffun_index /tensor_dffun_unindex/= tensor_indexK fprod_of_dffunK. Qed.

Lemma tensor_dffun_index_bij : bijective tensor_dffun_index.
Proof. by exists tensor_dffun_unindex;[exact: tensor_dffun_indexK|exact: tensor_dffun_unindexK]. Qed.

End IndexTensorBij.

Section IndexTensorConsBij.

Local Open Scope ring_scope.

Context (u : {posnum nat}) {k : nat} (u_ : {posnum nat} ^ k).

Local Notation u_cons := ([ffun i : 'I_k.+1 => if unlift ord0 i is Some j then u_ j else u] : {posnum nat} ^ k.+1).

Lemma tensormx_cast : #|{:'I_u%:num * 'I_(\prod_(i < k) (u_ i)%:num)}| = \prod_(i < k.+1) (u_cons i)%:num.
Proof.
rewrite card_prod !card_ord big_ord_recl ffunE/= unlift_none.
by congr (_ * _); apply: eq_bigr => i _; rewrite ffunE liftK.
Qed.

Definition tensormx_index (ij : 'I_u%:num * 'I_\prod_(i < k) (u_ i)%:num)
  : 'I_\prod_(i < k.+1) (u_cons i)%:num :=
  cast_ord tensormx_cast (enum_rank ij).

Definition tensormx_unindex (i : 'I_\prod_(i < k.+1) (u_cons i)%:num)
  : 'I_u%:num * 'I_\prod_(i < k) (u_ i)%:num :=
  enum_val (cast_ord (esym tensormx_cast) i).

Lemma tensormx_indexK : cancel tensormx_index tensormx_unindex.
Proof. by move=> ij; rewrite /tensormx_unindex cast_ordK enum_rankK. Qed.

Lemma tensormx_unindexK : cancel tensormx_unindex tensormx_index.
Proof. by move=> i; rewrite /tensormx_index enum_valK cast_ordKV. Qed.

End IndexTensorConsBij.

Local Open Scope ring_scope.

Context (R : Type) (u d : {posnum nat}) (k l : nat) (u_ : {posnum nat} ^ k) (d_ : {posnum nat} ^ l).
Local Notation u_cons := (fcons u u_).
Local Notation d_cons := (fcons d d_).

Definition nindex (t : 'T[R]_(u_cons, d_)) (i : 'I_u%:num) : 'T[R]_(u_, d_) :=
  Tensor (\matrix_(i', j) (\val t) (tensormx_index (i, i')) j).

Definition oindex (t : 'T[R]_(u_, d_cons)) (j : 'I_d%:num) : 'T[R]_(u_, d_) :=
  Tensor (\matrix_(i, j') (\val t) i (tensormx_index (j, j'))).

Definition nstack (f : 'I_u%:num -> 'T[R]_(u_, d_)) : 'T[R]_(u_cons, d_) := 
  Tensor (
    \matrix_(i, j) \val (f (tensormx_unindex i).1) (tensormx_unindex i).2 j).

Definition ostack (f : 'I_d%:num -> 'T[R]_(u_, d_)) : 'T[R]_(u_, d_cons) :=
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

Lemma ntensorP (u : {posnum nat}) (k l : nat) (u_ : {posnum nat} ^ k) (d_ : {posnum nat} ^ l) (t v : 'T[R]_(fcons u u_, d_)) 
  : t = v <-> forall i, t^^i = v^^i.
Proof.
split=> [->//|eq_i]; apply/val_inj/matrixP=> i j.
move: (eq_i (tensormx_unindex i).1)=> [/matrixP] /(_ (tensormx_unindex i).2 j).
by rewrite !mxE -surjective_pairing tensormx_unindexK.
Qed.

Lemma otensorP (d : {posnum nat}) (k l : nat) (u_ : {posnum nat} ^ k) (d_ : {posnum nat} ^ l) (t v : 'T[R]_(u_, fcons d d_))
  : t = v <-> forall i, t`_i = v`_i.
Proof.
split=> [->//|eq_i]; apply/val_inj/matrixP=> i j.
move: (eq_i (tensormx_unindex j).1)=> [/matrixP] /(_ i (tensormx_unindex j).2).
by rewrite !mxE -surjective_pairing tensormx_unindexK.
Qed.

Lemma ntensor_eqP (u : {posnum nat}) (t v : 'nT[R]_(fcons u tensor_nil_f))
  : t = v <-> forall i, t^^=i = v^^=i.
Proof.
split=> [->//|eq_i]; apply/ntensorP=> i.
by move: (eq_i i)=> /tensor_nil_eqP.
Qed.

Lemma otensor_eqP (d : {posnum nat}) (t v : 'oT[R]_(fcons d tensor_nil_f))
  : t = v <-> forall i, t`_=i = v`_=i.
Proof.
split=> [->//|eq_i]; apply/otensorP=> i.
by move: (eq_i i)=> /tensor_nil_eqP.
Qed.

(* Note: there seems to be some conflict between ring scope and the `_ notation *)

Lemma nstackE {u : {posnum nat}} {k l} {u_ : {posnum nat} ^ k} {d_ : {posnum nat} ^ l} (f : 'I_u%:num%R -> 'T[R]_(u_, d_)) i : (nstack f)^^i = f i.
Proof. by apply/val_inj/matrixP => x y; rewrite !mxE tensormx_indexK. Qed.

Lemma ostackE {d : {posnum nat}} {k l} {u_ : {posnum nat} ^ k} {d_ : {posnum nat} ^ l} (f : 'I_d%:num%R -> 'T[R]_(u_, d_)) i : (ostack f)`_i = f i.
Proof. by apply/val_inj/matrixP => x y; rewrite !mxE tensormx_indexK. Qed.

Lemma nstack_eqE {u : {posnum nat}} (f : 'I_u%:num%R -> R) i : (\tensor^^i0 => f i0)^^=i = f i.
Proof. by rewrite nstackE const_tK. Qed.

Lemma ostack_eqE {d : {posnum nat}} (f : 'I_d%:num%R -> R) i : (\tensor`_i0 => f i0)`_=i = f i.
Proof. by rewrite ostackE const_tK. Qed.

End TensorIndexTheory.


Section TensorTuple.

Context {R : Type} (x : {posnum nat}) (k l : nat) (u_ : {posnum nat} ^ k) (d_ : {posnum nat} ^ l).

Definition ntensor_of_tuple (t : x%:num%R.-tuple R) : 'nT[R]_(fcons x tensor_nil_f) :=
  \tensor^^i => (tnth t i).

Definition otensor_of_tuple (t : x%:num%R.-tuple R) : 'oT[R]_(fcons x tensor_nil_f) :=
  \tensor`_i => (tnth t i).

Lemma ntensor_of_tupleE t i : (ntensor_of_tuple t)^^=i = tnth t i.
Proof. exact: nstack_eqE. Qed.

Lemma otensor_of_tupleE t i : (otensor_of_tuple t)`_=i = tnth t i.
Proof. exact: ostack_eqE. Qed.

Definition nstack_tuple (t : x%:num%R.-tuple 'T[R]_(u_, d_)) :=
  \tensor^^i tnth t i.

Definition ostack_tuple (t : x%:num%R.-tuple 'T[R]_(u_, d_)) :=
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

Context {R : Type} {n m : {posnum nat}}.

Definition tensor_of_matrix (M : 'M_(_, _)) : 'T[R]_(fcons n tensor_nil_f, fcons m tensor_nil_f) :=
  \tensor^^i \tensor`_j => M i j.

Definition matrix_of_tensor t : 'M[R]_(n%:num%R, m%:num%R) :=
  \matrix_(i, j) t^^i`_=j.

Lemma tensor_of_matrixK : cancel tensor_of_matrix matrix_of_tensor.
Proof. by move=> M; apply/matrixP=> i j; rewrite mxE nstackE ostack_eqE. Qed.

Lemma matrix_of_tensorK : cancel matrix_of_tensor tensor_of_matrix.
Proof.
move=> T; apply/ntensorP=> i; apply/otensor_eqP=> j.
by rewrite nstackE ostack_eqE mxE.
Qed.

End TensorMatrix.

Section TensorProduct.

Context {R : pzSemiRingType} {R' : pzRingType}.
Context {k1 l1 k2 l2 : nat}.
Context (u1_ : {posnum nat} ^ k1) (d1_ : {posnum nat} ^ l1).
Context (u2_ : {posnum nat} ^ k2) (d2_ : {posnum nat} ^ l2).

Definition fcat {n m : nat} (f : {posnum nat} ^ n) (g : {posnum nat} ^ m) : {posnum nat} ^ (n + m) :=
  [ffun i : 'I_(n + m) => 
    match split i with
    | inl j => f j
    | inr j => g j
    end].

Lemma prod_fcat {n m : nat} (f : {posnum nat} ^ n) (g : {posnum nat} ^ m) :
  \prod_(i < n) (f i)%:num%R * \prod_(i < m) (g i)%:num%R = \prod_(i < n + m) (fcat f g i)%:num%R.
Proof.
rewrite big_split_ord/= /fcat.
congr (_ * _).
  apply/eq_bigr => i _; rewrite ffunE/=.
  case: split_ordP => j.
    by move=>/lshift_inj ->.
  by move=>/eqP; rewrite eq_lrshift.
apply/eq_bigr => i _; rewrite ffunE/=.
case: split_ordP => j.
  by move=> /eqP; rewrite eq_rlshift.
by move=>/rshift_inj ->.
Qed.

Lemma prod_card (m n : nat) : #|{:'I_m * 'I_n}| = (m * n)%N.
Proof. by rewrite card_prod !card_ord. Qed.

Definition prod_split (m n : nat) (i : 'I_(m * n)) : 'I_m * 'I_n :=
  enum_val (cast_ord (esym (prod_card m n)) i).

Definition prod_unsplit (m n : nat) (ij : 'I_m * 'I_n) : 'I_(m * n) :=
  cast_ord (prod_card m n) (enum_rank ij).

Definition mults (t : 'T[R]_(u1_, d1_)) (u : 'T[R]_(u2_, d2_)) 
  : 'T[R]_(fcat u1_ u2_, fcat d1_ d2_) :=
  Tensor (\matrix_(i, j) 
    let ii := prod_split (cast_ord (esym (prod_fcat _ _)) i) in
    let jj := prod_split (cast_ord (esym (prod_fcat _ _)) j) in
    (\val t ii.1 jj.1) * (\val u ii.2 jj.2))%R.

Local Open Scope ring_scope.

Lemma multsDl (t u : 'T[R]_(u1_, d1_)) (v : 'T[R]_(u2_, d2_)) :
  mults (t + u) v = (mults t v + mults u v).
Proof.
by apply/val_inj/matrixP => i j; rewrite /tensor_val/= !mxE/= mulrDl.
Qed.

Lemma multsDr (t : 'T[R]_(u1_, d1_)) (u v : 'T[R]_(u2_, d2_)) :
  mults t (u + v) = mults t u + mults t v.
Proof.
by apply/val_inj/matrixP => i j; rewrite /tensor_val/= !mxE /= mulrDr.
Qed.

Lemma mults0l (t : 'T[R]_(u2_, d2_)) :
  mults (0 : 'T[R]_(u1_, d1_)) t = 0.
Proof.
by apply/val_inj/matrixP => i j; rewrite /tensor_val /= !mxE /= mul0r.
Qed.

Lemma mults0r (t : 'T[R]_(u1_, d1_)) :
  mults t (0 : 'T[R]_(u2_, d2_)) = 0.
Proof.
by apply/val_inj/matrixP => i j; rewrite /tensor_val /= !mxE mulr0.
Qed.

Lemma mults_const (a b : R) :
  mults (@const_t R _ _ u1_ d1_ a) (@const_t R _ _ u2_ d2_ b) = 
  const_t (a * b)%R.
Proof.
by apply/val_inj/matrixP => i j; rewrite /tensor_val /= !mxE.
Qed.


End TensorProduct.

Notation "*t%R" := mults : ring_scope.
Notation "x *t y" := (mults x y) : ring_scope.

Section TensorProductBilinear.

Context {R : comNzRingType}.
Context {k1 l1 k2 l2 : nat}.
Context (u1_ : {posnum nat} ^ k1) (d1_ : {posnum nat} ^ l1).
Context (u2_ : {posnum nat} ^ k2) (d2_ : {posnum nat} ^ l2).

Local Open Scope ring_scope.

#[local] Fact mults_linear_l (u : 'T[R]_(u2_, d2_)) :
  GRing.linear_for *:%R (fun t : 'T[R]_(u1_, d1_) => t *t u).
Proof.
move=> a x y; apply/val_inj/matrixP=> i j; rewrite /tensor_val/= !mxE/=.
rewrite mulrDl; congr (_ + _);
  by rewrite mulrA.
Qed.

#[local] Fact mults_linear_r (t : 'T[R]_(u1_, d1_)) :
  GRing.linear_for *:%R (fun u : 'T[R]_(u2_, d2_) => t *t u).
Proof.
move=> a x y; apply/val_inj/matrixP=> i j; rewrite /tensor_val/= !mxE/=.
by rewrite mulrDr; congr (_ + _); rewrite mulrA (mulrCA a) mulrA.
Qed.

HB.instance Definition _ := bilinear_isBilinear.Build
  R
  'T[R]_(u1_, d1_) 'T[R]_(u2_, d2_)
  'T[R]_(fcat u1_ u2_, fcat d1_ d2_)
  *:%R *:%R (@mults _ _ _ _ _ _ _ _ _) (conj mults_linear_l mults_linear_r).

End TensorProductBilinear.

Section TensorProductHadamard.

Context {R : comPzRingType}.
Context {k1 l1 k2 l2 : nat}.
Context (u1_ : {posnum nat} ^ k1) (d1_ : {posnum nat} ^ l1).
Context (u2_ : {posnum nat} ^ k2) (d2_ : {posnum nat} ^ l2).

Local Open Scope ring_scope.

Lemma mults_hmul (t1 u1 : 'T[R]_(u1_, d1_)) (t2 u2 : 'T[R]_(u2_, d2_)) :
  (t1 *h u1) *t (t2 *h u2) = (t1 *t t2) *h (u1 *t u2).
Proof.
by apply/val_inj/matrixP => i j; rewrite /tensor_val /= !mxE /= mulrACA.
Qed.

End TensorProductHadamard.

Section TensorProductRing.

Context {k1 l1 k2 l2 : nat}.
Context (u1_ : {posnum nat} ^ k1) (d1_ : {posnum nat} ^ l1).
Context (u2_ : {posnum nat} ^ k2) (d2_ : {posnum nat} ^ l2).

Local Open Scope ring_scope.

Lemma multsNl {R : pzRingType} (t : 'T[R]_(u1_, d1_)) (u : 'T[R]_(u2_, d2_)) :
  (- t) *t u = - (t *t u).
Proof.
by apply/val_inj/matrixP => i j; rewrite /tensor_val /= !mxE /= mulNr.
Qed.

Lemma multsNr {R : pzRingType} (t : 'T[R]_(u1_, d1_)) (u : 'T[R]_(u2_, d2_)) :
  t *t (- u) = - (t *t u).
Proof.
by apply/val_inj/matrixP => i j; rewrite /tensor_val /= !mxE /= mulrN.
Qed.

(* Note: true commutativity would swap dimensions, requiring a more complex statement *)
Lemma mults_scale {R : comPzSemiRingType} (a b : R) (t : 'T[R]_(u1_, d1_)) (u : 'T[R]_(u2_, d2_)) :
  (const_t a *h t) *t (const_t b *h u) = const_t (a * b)%R *h (t *t u).
Proof.
by apply/val_inj/matrixP => i j; rewrite /tensor_val /= !mxE /= mulrACA.
Qed.

Lemma mults_hmul_compat {R : comPzSemiRingType} 
  (t1 t2 : 'T[R]_(u1_, d1_)) (u1 u2 : 'T[R]_(u2_, d2_)) :
  (t1 *h t2) *t (u1 *h u2) = (t1 *t u1) *h (t2 *t u2).
Proof.
by apply/val_inj/matrixP => i j; rewrite /tensor_val /= !mxE /= mulrACA.
Qed.

End TensorProductRing.

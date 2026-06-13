From HB Require Import structures.
From mathcomp Require Import ssreflect seq matrix bigop ssrbool eqtype choice.
From mathcomp Require Import fintype ssralg ssrnat ssrfun order finfun tuple.
From mathcomp Require Import finset sesquilinear.
From mathcomp Require Import interval interval_inference numdomain.

(******************************************************************************)
(* For tensors we define:                                                     *)
(*       'T[R]_(u_, d_) == the type of tensors with elements of type R,       *)
(*          'T_(u_, d_)    contravariant dimensions u_ and covariant          *)
(*                         dimensions d_; u_ and d_ are tuples of             *)
(*                         {posnum nat} (k.-tuple and l.-tuple resp.),        *)
(*                         coerced automatically to {posnum nat} ^ k and      *)
(*                         {posnum nat} ^ l finfuns                           *)
(*                         The [R] is optional and can usually be omitted     *)
(* 'T[R]_[u1, .., uk ; d1, .., dl] ==                                         *)
(*                         shorthand parsing notation for                     *)
(*                         'T[R]_([tuple of u1%:posnat :: .. :: uk%:posnat],  *)
(*                                [tuple of d1%:posnat :: .. :: dl%:posnat]); *)
(*                         e.g. 'T[R]_[2, 3 ; 4] for a tensor with            *)
(*                         contravariant dims (2, 3) and covariant dim (4)    *)
(* 'nT[R]_(u_), 'nT_(u_) == purely contravariant tensors (no covariant dims), *)
(*                          i.e. 'T[R]_(u_, [tuple])                          *)
(*   'nT[R]_[u1, .., uk] == shorthand parsing notation for                    *)
(*                          'nT[R]_([tuple of u1%:posnat :: .. :: uk%:posnat])*)
(* 'oT[R]_(d_), 'oT_(d_) == purely covariant tensors (no contravariant dims), *)
(*                          i.e. 'T[R]_([tuple], d_)                          *)
(*   'oT[R]_[d1, .., dl] == shorthand parsing notation for                    *)
(*                          'oT[R]_([tuple of d1%:posnat :: .. :: dl%:posnat])*)
(*           'sT[R], 'sT == scalar tensors (no contravariant nor covariant    *)
(*                          dimensions), i.e. 'T[R]_([tuple], [tuple])        *)
(*                  t^^i == the tensor obtained by fixing the first           *)
(*                          contravariant dimension of t to i                 *)
(*                  t\_i == the tensor obtained by fixing the first           *)
(*                          covariant dimension of t to i                     *)
(* \tensor^^(i < n) Expr(i) ==                                                *)
(*                         the 'T_([tuple of n :: _], _) tensor t such that   *)
(*                         t^^i = Expr(i) with i : 'I_n, the < n bound can    *)
(*                         usually be omitted                                 *)
(* \tensor\_(j < n) Expr(j) ==                                                *)
(*                         the 'T_(_, [tuple of n :: _]) tensor t such that   *)
(*                         t\_j = Expr(j) with j : 'I_n, the < n bound can    *)
(*                         usually be omitted                                 *)
(*            const_t v == the constant tensor whose entries are all v        *)
(*                         (dimensions are inferred from context)             *)
(*          castt eq_ud == reshape a tensor t : 'T[R]_(u_, d_) into one of    *)
(*                         type 'T[R]_(u_', d_') given a pair eq_ud of        *)
(*                         equalities on \prod_i u_ i and \prod_j d_ j;       *)
(*                         mirrors castmx                                     *)
(*               t.[::] == the value of the single entry in a                 *)
(*                         tensor t : 'T_([tuple], [tuple])                   *)
(*         t^^=i, t\_=i == variants of the indexing operations equivalent to  *)
(*                         (t^^i).[::], (t\_i).[::], useful for indexing the  *)
(*                         final dimensions of tensors                        *)
(* \tensor^^(i < n) => Expr(i), \tensor\_(j < n) => Expr(j) ==                *)
(*                         variant constructor equivalent to                  *)
(*                         \tensor^^(i < n) const_t Expr(i)                   *)
(* [tensor^^ t_0; ...; t_n], [tensor\_ t_0; ...; t_n] ==                      *)
(*                         construction of a tensor from a sequence of        *)
(*                         tensors                                            *)
(* [tensor^^= x_0; ...; x_n], [tensor\_= x_0; ...; x_n] ==                    *)
(*                         construction of a tensor from a sequence of values *)
(* Tensors are instances of subType of matrix, and inherit all combinatorial  *)
(* structures (including finType), as well as nmodType, zmodType,             *)
(* lSemiModType, lModType, and ring instances where the underlying type       *)
(* satisfies that instance.                                                   *)
(* NOTE: Ring multiplication ( *%R ) is the Hadamard (element-wise) product.  *)
(* Proper tensor product forms a bilinear structure.                          *)
(*                                                                            *)
(* Tensor operations:                                                         *)
(* t *h u == Hadamard product of t and u (element-wise multiplication),       *)
(*           same as t * u (ring multiplication)                              *)
(* t *t u == proper tensor product: combines dimensions,                      *)
(*           'T_(u1, d1) * 'T_(u2, d2) -> 'T_(u1 +++ u2, d1 +++ d2)           *)
(*                                                                            *)
(* Notations: indexing operations (^^, \_, ^^=, \_=), the stacking            *)
(* constructors (\tensor^^, \tensor\_), the bracket constructors              *)
(* ([tensor^^ ...], [tensor\_ ...], [tensor^^= ...], [tensor\_= ...]) and     *)
(* the nullary projection (t.[::]) live in ring_scope.                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

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
Reserved Notation "''sT'" (at level 0, format "''sT'").
Reserved Notation "''sT[' R ]" (at level 0). (* only parsing *)

Reserved Notation "t ^^ i"
  (at level 30, i at level 30, format "t ^^ i").
Reserved Notation "t \_ i"
  (at level 10, format "t \_ i").
Reserved Notation "t ^^= i"
  (at level 30, i at level 30, format "t ^^= i").
Reserved Notation "t \_= i"
  (at level 10, format "t \_= i").

Reserved Notation "\tensor ^^ i E"
  (at level 34, E at level 39, i binder, format "\tensor ^^ i  E").
Reserved Notation "\tensor \_ i E"
  (at level 34, E at level 39, i binder, format "\tensor \_ i  E").
Reserved Notation "\tensor ^^ ( i < u ) E"
  (at level 34, E at level 39, i, u at level 50). (* only parsing *)
Reserved Notation "\tensor \_ ( i < d ) E"
  (at level 34, E at level 39, i, d at level 50). (* only parsing *)
Reserved Notation "\tensor ^^ i => E"
  (at level 34, E at level 39, i binder, format "\tensor ^^ i  =>  E").
Reserved Notation "\tensor \_ i => E"
  (at level 34, E at level 39, i binder, format "\tensor \_ i  =>  E").
Reserved Notation "\tensor ^^ ( i < u ) => E"
  (E at level 39, i, u at level 50). (* only parsing *)
Reserved Notation "\tensor \_ ( i < d ) => E"
  (E at level 39, i, d at level 50). (* only parsing *)

Reserved Notation "[ 'tensor' ^^ t ; .. ; tn ]"
  (format "[ 'tensor' ^^ '['  t ; '/'  .. ; '/'  tn ']' ]").
Reserved Notation "[ 'tensor' \_ t ; .. ; tn ]"
  (format "[ 'tensor' \_ '['  t ; '/'  .. ; '/'  tn ']' ]").
Reserved Notation "[ 'tensor' ^^= x ; .. ; xn ]"
  (format "[ 'tensor' ^^= '['  x ; '/'  .. ; '/'  xn ']' ]").
Reserved Notation "[ 'tensor' \_= x ; .. ; xn ]"
  (format "[ 'tensor' \_= '['  x ; '/'  .. ; '/'  xn ']' ]").

Reserved Notation "t .[::]".

Reserved Notation "*h%R" (at level 0).
Reserved Notation "x *h y"
  (at level 40, left associativity, format "x  *h  y").
Reserved Notation "*t%R" (at level 0).
Reserved Notation "x *t y"
  (at level 40, left associativity, format "x  *t  y").

(* Coercion from tuples to finfun: allows writing tensor dimensions as tuples *)
#[warning="-uniform-inheritance"]
Coercion finfun_of_tuple : tuple_of >-> finfun_of.
#[warning="-uniform-inheritance"]
Coercion tuple_of_finfun : finfun_of >-> tuple_of.


Local Open Scope ring_scope.

Section TensorDef.

Context {k l : nat} (u_ : {posnum nat} ^ k) (d_ : {posnum nat} ^ l) (K : Type).

Variant tensor : predArgType :=
  Tensor of 'M[K]_(\prod_(i < k) (u_ i)%:num, \prod_(j < l) (d_ j)%:num)%R.

Definition tensor_val T := let: Tensor g := T in g.

HB.instance Definition _ := [isNew for tensor_val].

End TensorDef.

Bind Scope ring_scope with tensor.

Notation "''T[' R ]_ ( u_ , d_ )" := (tensor u_ d_ R) (only parsing) : type_scope.
Notation "''T[' R ]_ [ u1 , .. , uk ; d1 , .. , dl ]"
  := (tensor [tuple of u1%:posnat :: .. [:: uk%:posnat] ..]
             [tuple of d1%:posnat :: .. [:: dl%:posnat] ..] R)
     (only parsing) : type_scope.
Notation "''T_' ( u_ , d_ )" := (tensor u_ d_ _) : type_scope.
Notation "''nT[' R ]_ ( u_ )" := 'T[R]_( u_ , [tuple] ) (only parsing) : type_scope.
Notation "''nT[' R ]_ [ u1 , .. , uk ]"
  := 'T[R]_( [tuple of u1%:posnat :: .. [:: uk%:posnat] ..] , [tuple] )
     (only parsing) : type_scope.
Notation "''oT[' R ]_ ( d_ )" := 'T[R]_( [tuple] , d_ ) (only parsing) : type_scope.
Notation "''oT[' R ]_ [ d1 , .. , dl ]"
  := 'T[R]_( [tuple] , [tuple of d1%:posnat :: .. [:: dl%:posnat] ..] )
     (only parsing) : type_scope.
Notation "''oT_' ( d_ )" := (tensor [tuple] d_ _) : type_scope.
Notation "''nT_' ( u_ )" := (tensor u_ [tuple] _) : type_scope.
Notation "''sT[' R ]" := (tensor [tuple] [tuple] R) (only parsing) : type_scope.
Notation "''sT'" := (tensor [tuple] [tuple] _) : type_scope.

Section SubtypeInstances.

Context {l k : nat} (u_ : {posnum nat} ^ k) (d_ : {posnum nat} ^ l).
Local Notation "''T[' R ]" := 'T[R]_(u_, d_).

HB.instance Definition _ (R : eqType) := [Equality of 'T[R] by <:].
HB.instance Definition _ (R : choiceType) := [Choice of 'T[R] by <:].
HB.instance Definition _ (R : countType) := [Countable of 'T[R] by <:].
HB.instance Definition _ (R : finType) := [Finite of 'T[R] by <:].

Let nmod_closed {m n} (R : nmodType) : @GRing.nmod_closed 'M[R]_(n, m) predT.
Proof. by []. Qed.
HB.instance Definition _ (R : nmodType) :=
  GRing.SubChoice_isSubNmodule.Build _ _ 'T[R] (nmod_closed R).

HB.instance Definition _ (R : zmodType) :=
  GRing.SubChoice_isSubZmodule.Build _ _ 'T[R] (nmod_closed R).

Let subsemimod_closed {m n} (R : pzSemiRingType)
  : @GRing.subsemimod_closed R 'M[R]_(n, m) predT.
Proof. by []. Qed.
HB.instance Definition _ (R : pzSemiRingType) :=
  GRing.SubNmodule_isSubLSemiModule.Build _ _ _ 'T[R] (subsemimod_closed R).

HB.instance Definition _ (R : pzRingType) := GRing.SubLSemiModule.on 'T[R].

End SubtypeInstances.


Definition const_t {R k l} {u_ : {posnum nat} ^ k} {d_ : {posnum nat} ^ l}
  (v : R) : 'T[R]_(u_, d_) := Tensor (const_mx v).


Section TensorCast.

Context {R : Type}.

Definition castt {k l k' l' : nat}
    {u_ : {posnum nat} ^ k} {d_ : {posnum nat} ^ l}
    {u_' : {posnum nat} ^ k'} {d_' : {posnum nat} ^ l'}
    (eq_ud : (\prod_(i < k) (u_ i)%:num = \prod_(i < k') (u_' i)%:num)
           * (\prod_(j < l) (d_ j)%:num = \prod_(j < l') (d_' j)%:num))
    (t : 'T[R]_(u_, d_)) : 'T[R]_(u_', d_') :=
  Tensor (castmx eq_ud (\val t)).

Lemma val_castt {k l k' l' : nat}
    {u_ : {posnum nat} ^ k} {d_ : {posnum nat} ^ l}
    {u_' : {posnum nat} ^ k'} {d_' : {posnum nat} ^ l'}
    (eq_ud : (\prod_(i < k) (u_ i)%:num = \prod_(i < k') (u_' i)%:num)
           * (\prod_(j < l) (d_ j)%:num = \prod_(j < l') (d_' j)%:num))
    (t : 'T[R]_(u_, d_)) :
  \val (castt eq_ud t) = castmx eq_ud (\val t).
Proof. by []. Qed.

Lemma castt_id {k l : nat}
    {u_ : {posnum nat} ^ k} {d_ : {posnum nat} ^ l}
    erefl_ud (t : 'T[R]_(u_, d_)) :
  castt erefl_ud t = t.
Proof. by apply/val_inj; rewrite val_castt castmx_id. Qed.

Lemma castt_comp {k1 l1 k2 l2 k3 l3 : nat}
    {u1 : {posnum nat} ^ k1} {d1 : {posnum nat} ^ l1}
    {u2 : {posnum nat} ^ k2} {d2 : {posnum nat} ^ l2}
    {u3 : {posnum nat} ^ k3} {d3 : {posnum nat} ^ l3}
    (eq_u1 : \prod_(i < k1) (u1 i)%:num = \prod_(i < k2) (u2 i)%:num)
    (eq_d1 : \prod_(j < l1) (d1 j)%:num = \prod_(j < l2) (d2 j)%:num)
    (eq_u2 : \prod_(i < k2) (u2 i)%:num = \prod_(i < k3) (u3 i)%:num)
    (eq_d2 : \prod_(j < l2) (d2 j)%:num = \prod_(j < l3) (d3 j)%:num)
    (t : 'T[R]_(u1, d1)) :
  castt (eq_u2, eq_d2) (castt (eq_u1, eq_d1) t)
    = castt (etrans eq_u1 eq_u2, etrans eq_d1 eq_d2) t.
Proof. by apply/val_inj; rewrite !val_castt castmx_comp. Qed.

Lemma casttK {k1 l1 k2 l2 : nat}
    {u1 : {posnum nat} ^ k1} {d1 : {posnum nat} ^ l1}
    {u2 : {posnum nat} ^ k2} {d2 : {posnum nat} ^ l2}
    (eq_u : \prod_(i < k1) (u1 i)%:num = \prod_(i < k2) (u2 i)%:num)
    (eq_d : \prod_(j < l1) (d1 j)%:num = \prod_(j < l2) (d2 j)%:num) :
  cancel (castt (u_' := u2) (d_' := d2) (eq_u, eq_d))
         (castt (esym eq_u, esym eq_d)).
Proof. by move=> t; apply/val_inj; rewrite !val_castt castmxK. Qed.

Lemma casttKV {k1 l1 k2 l2 : nat}
    {u1 : {posnum nat} ^ k1} {d1 : {posnum nat} ^ l1}
    {u2 : {posnum nat} ^ k2} {d2 : {posnum nat} ^ l2}
    (eq_u : \prod_(i < k1) (u1 i)%:num = \prod_(i < k2) (u2 i)%:num)
    (eq_d : \prod_(j < l1) (d1 j)%:num = \prod_(j < l2) (d2 j)%:num) :
  cancel (castt (u_ := u2) (d_ := d2) (u_' := u1) (d_' := d1)
                (esym eq_u, esym eq_d))
         (castt (eq_u, eq_d)).
Proof. by move=> t; apply/val_inj; rewrite !val_castt castmxKV. Qed.

End TensorCast.


Section TensorRing.


Context {l k : nat} (u_ : {posnum nat} ^ k) (d_ : {posnum nat} ^ l).
Local Notation "''T[' R ]" := 'T[R]_(u_, d_).

Section TensorSemiRing.

Context {R : pzSemiRingType}.

Definition tensor1 := @const_t _ _ _ u_ d_ (GRing.one R).

(* Hadamard product: element-wise multiplication *)
Definition hmul (t u : 'T[R]_(u_, d_)) :=
  @Tensor _ _ u_ d_ R (map2_mx *%R (\val t) (\val u)).

Let hmulA : associative hmul.
Proof. by move=> x y z; rewrite /hmul map2_mxA. Qed.
Let hmul1t : left_id tensor1 hmul.
Proof. by move=> [x]; rewrite /hmul map2_1mx. Qed.
Let hmul1 : right_id tensor1 hmul.
Proof. by move=> [x]; rewrite /hmul map2_mx1. Qed.
Let hmulDl : left_distributive hmul +%R.
Proof. by move=> x y z; rewrite /hmul map2_mxDl. Qed.
Let hmulDr : right_distributive hmul +%R.
Proof. by move=> x y z; rewrite /hmul map2_mxDr. Qed.
Let hmul0t : left_zero 0%R hmul.
Proof. by move=> x; rewrite /hmul map2_0mx. Qed.
Let hmul0 : right_zero 0%R hmul.
Proof. by move=> x; rewrite /hmul map2_mx0. Qed.

HB.instance Definition _ := GRing.Nmodule_isPzSemiRing.Build
  'T[R] hmulA hmul1t hmul1 hmulDl hmulDr hmul0t hmul0.

End TensorSemiRing.

Let hmulC {R : comPzSemiRingType} : @commutative 'T[R] _ hmul.
Proof. by move=> x y; rewrite /hmul map2_mxC. Qed.


HB.instance Definition _ {R : comPzSemiRingType} :=
  GRing.SemiRing_hasCommutativeMul.Build 'T[R] hmulC.

Let onet_neq0 {R : nzSemiRingType} : (1%R : 'T[R]) != 0%R.
Proof.
apply/eqP; case=> /matrixP.
set i := \prod_(i < k) (u_ i)%:num; set j := \prod_(i < l) (d_ i)%:num.
have: 0 < i by apply/prodn_gt0 => ?; rewrite gtn0.
have: 0 < j by apply/prodn_gt0 => ?; rewrite gtn0.
case: i j => [|i] [|j]// _ _ /(_ ord0 ord0).
by apply/eqP; rewrite !mxE oner_neq0.
Qed.

HB.instance Definition _ {R : nzSemiRingType} := 
  GRing.PzSemiRing_isNonZero.Build
  'T[R] onet_neq0.

(* FIXME: HB.saturate *)
HB.instance Definition _ {R : pzRingType} := GRing.PzSemiRing.on 'T[R].
HB.instance Definition _ {R : nzRingType} := GRing.NzSemiRing.on 'T[R].
HB.instance Definition _ {R : comPzRingType} := GRing.PzRing.on 'T[R].
HB.instance Definition _ {R : comNzRingType} := GRing.NzRing.on 'T[R].

Definition unitt {R : unitRingType} (t : 'T[R]) :=
  [forall ij, (\val t ij.1 ij.2) \is a GRing.unit].

Definition invt {R : unitRingType} (t : 'T[R]) := 
  if t \in unitt then Tensor (map_mx GRing.inv (\val t)) else t.

Let mulVt {R : unitRingType} : {in @unitt R, left_inverse 1%R invt *%R}.
Proof.
move=> t t_unit; apply/val_inj/matrixP=> i j/=.
rewrite /invt t_unit !mxE mulVr//=.
by move: t_unit; rewrite /unitt=> /forallP /(_ (i, j)).
Qed.

Let divtt {R : unitRingType} : {in @unitt R, right_inverse 1%R invt *%R}.
Proof.
move=> t t_unit; apply/val_inj/matrixP=> i j/=.
rewrite /invt t_unit !mxE divrr//.
by move: t_unit; rewrite /unitt=> /forallP /(_ (i, j)).
Qed.

Let unittP {R : unitRingType}
  : forall x y, y * x = 1%R /\ x * y = 1 -> @unitt R x.
Proof.
move=> x y [/eqP + /eqP]; rewrite /eq_op/==> /eqP/matrixP yx1 /eqP/matrixP xy1.
apply/forallP=> ij; apply/unitrP; exists (\val y ij.1 ij.2).
move: (conj (yx1 ij.1 ij.2) (xy1 ij.1 ij.2)).
by rewrite !mxE.
Qed.

Let invt_out {R : unitRingType} : {in [predC @unitt R], invt =1 id}.
Proof. by move=> t /negbTE t_not_unit; rewrite /invt t_not_unit. Qed.

HB.instance Definition _ {R : unitRingType} :=
  GRing.NzRing_hasMulInverse.Build 'T[R] mulVt divtt unittP invt_out.

End TensorRing.

(* Notations for Hadamard product *)
Notation "*h%R" := hmul : function_scope.
Notation "x *h y" := (hmul x y) : ring_scope.

Section NilTensor.

Context (R : Type).

Lemma prod_nil : 1%N = \prod_(i < 0) (([tuple] : 0.-tuple {posnum nat}) i)%:num.
Proof. by rewrite big_ord0. Qed.

Lemma ord_prod_nil : all_equal_to (cast_ord prod_nil ord0).
Proof.
case=> [[?|n n_ord]]; apply: val_inj=>//=.
by move: n_ord; rewrite -prod_nil.
Qed.

Definition tensor_nil (t : 'sT[R]) : R :=
  \val t (cast_ord prod_nil ord0) (cast_ord prod_nil ord0).

Lemma const_tK : cancel const_t tensor_nil.
Proof. by move=> t; rewrite /tensor_nil mxE. Qed.

Lemma tensor_nilK : cancel tensor_nil const_t.
Proof.
by move=> t; apply/val_inj/matrixP => i j; rewrite mxE !ord_prod_nil.
Qed.

End NilTensor.


Notation "t .[::]" := (tensor_nil t) : ring_scope. 


Section NilTensorTheory.

Lemma tensor_nil_eqP {R : Type} t u : t.[::] = u.[::] :> R <-> t = u.
Proof.
by split=> [?|->//]; apply/val_inj/matrixP=> i j; rewrite !ord_prod_nil.
Qed.


Fact tensor_nil_is_nmod_morphism {U : nmodType} : nmod_morphism (@tensor_nil U).
Proof. by split=> [|? ?]; rewrite /tensor_nil mxE. Qed.

HB.instance Definition _ {U : nmodType} :=
  GRing.isNmodMorphism.Build 'sT[U] U (@tensor_nil U)
    tensor_nil_is_nmod_morphism.

Fact tensor_nil_is_monoid_morphism {R : pzSemiRingType} :
  monoid_morphism (@tensor_nil R).
Proof. by split=> [|? ?]; rewrite /tensor_nil mxE. Qed.

HB.instance Definition _ {R : pzSemiRingType} :=
  GRing.isMonoidMorphism.Build 'sT[R] R (@tensor_nil R)
    tensor_nil_is_monoid_morphism.

Lemma tensor_nilV {R : unitRingType} t
  : (t^-1).[::] = t.[::]^-1 :> R.
Proof.
rewrite /tensor_nil {1}/GRing.inv/=/invt.
case (t \in @unitt _ _ [tuple] [tuple] R) eqn:t_unit; rewrite t_unit.
  by rewrite mxE.
apply/esym/invr_out; move: t_unit=> /negbT /forallP not_all_unit.
apply/negP=> ?; apply: not_all_unit=> ij.
by rewrite !ord_prod_nil.
Qed.

End NilTensorTheory.


Section ConstTensorTheory.

Context {l k : nat} (u_ : {posnum nat} ^ k) (d_ : {posnum nat} ^ l).


Fact const_t_is_nmod_morphism {U : nmodType} :
  nmod_morphism (@const_t U _ _ u_ d_).
Proof. by split=> [|? ?]; apply/val_inj/matrixP=> i j; rewrite !mxE. Qed.

HB.instance Definition _ {U : nmodType} :=
  GRing.isNmodMorphism.Build U 'T[U]_(u_, d_) (@const_t U _ _ u_ d_)
    const_t_is_nmod_morphism.

Fact const_t_is_monoid_morphism {R : pzSemiRingType} :
  monoid_morphism (@const_t R _ _ u_ d_).
Proof. by split=> [|? ?]; apply/val_inj/matrixP=> i j; rewrite !mxE. Qed.

HB.instance Definition _ {R : pzSemiRingType} :=
  GRing.isMonoidMorphism.Build R 'T[R]_(u_, d_) (@const_t R _ _ u_ d_)
    const_t_is_monoid_morphism.

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


Context {k : nat} (u_ : {posnum nat} ^ k).

Local Notation fprod_u := (fprod (fun i : 'I_k => 'I_(u_ i)%:num)).

Lemma card_fprod_u : #|fprod_u| = \prod_(i < k) (u_ i)%:num.
Proof. by rewrite card_fprod; apply: eq_bigr => i _; rewrite card_ord. Qed.


Definition tensor_index (f : fprod_u) : 'I_(\prod_(i < k) (u_ i)%:num) :=
  cast_ord card_fprod_u (enum_rank f).

Definition tensor_unindex (i : 'I_(\prod_(i < k) (u_ i)%:num)) : fprod_u :=
  enum_val (cast_ord (esym card_fprod_u) i).

Lemma tensor_indexK : cancel tensor_index tensor_unindex.
Proof.
by move=> f; rewrite /tensor_index /tensor_unindex cast_ordK enum_rankK.
Qed.

Lemma tensor_unindexK : cancel tensor_unindex tensor_index.
Proof.
by move=> i; rewrite /tensor_index /tensor_unindex enum_valK cast_ordKV.
Qed.

Lemma tensor_index_bij : bijective tensor_index.
Proof.
by exists tensor_unindex; [exact: tensor_indexK | exact: tensor_unindexK].
Qed.

Definition tensor_dffun_index : 'I_(\prod_(i < k) (u_ i)%:num) ->
    {dffun forall i : 'I_k, 'I_(u_ i)%:num} :=
  @dffun_of_fprod _ _ \o tensor_unindex.

Definition tensor_dffun_unindex : {dffun forall i : 'I_k, 'I_(u_ i)%:num} ->
    'I_(\prod_(i < k) (u_ i)%:num) :=
  tensor_index \o @fprod_of_dffun _ _.

Lemma tensor_dffun_indexK : cancel tensor_dffun_index tensor_dffun_unindex.
Proof.
by move=> i; rewrite /tensor_dffun_index /tensor_dffun_unindex/=
    dffun_of_fprodK tensor_unindexK.
Qed.

Lemma tensor_dffun_unindexK : cancel tensor_dffun_unindex tensor_dffun_index.
Proof.
by move=> f; rewrite /tensor_dffun_index /tensor_dffun_unindex/=
    tensor_indexK fprod_of_dffunK.
Qed.

Lemma tensor_dffun_index_bij : bijective tensor_dffun_index.
Proof.
by exists tensor_dffun_unindex;
    [exact: tensor_dffun_indexK | exact: tensor_dffun_unindexK].
Qed.

End IndexTensorBij.

Section IndexTensorConsBij.


Context (u : {posnum nat}) {k : nat} (u_ : k.-tuple {posnum nat}).

Local Notation u_cons := [tuple of u :: u_].

Lemma tensormx_cast : #|{:'I_u%:num * 'I_(\prod_(i < k) (u_ i)%:num)}|
                        = \prod_(i < k.+1) (u_cons i)%:num.
Proof.
rewrite card_prod !card_ord big_ord_recl ffunE [tnth _ _]tnth0.
by congr (_ * _); apply: eq_bigr => i _; rewrite !ffunE tnthS.
Qed.

Definition tensormx_index (ij : 'I_u%:num * 'I_(\prod_(i < k) (u_ i)%:num))
  : 'I_(\prod_(i < k.+1) (u_cons i)%:num) :=
  cast_ord tensormx_cast (enum_rank ij).

Definition tensormx_unindex (i : 'I_(\prod_(i < k.+1) (u_cons i)%:num))
  : 'I_u%:num * 'I_(\prod_(i < k) (u_ i)%:num) :=
  enum_val (cast_ord (esym tensormx_cast) i).

Lemma tensormx_indexK : cancel tensormx_index tensormx_unindex.
Proof. by move=> ij; rewrite /tensormx_unindex cast_ordK enum_rankK. Qed.

Lemma tensormx_unindexK : cancel tensormx_unindex tensormx_index.
Proof. by move=> i; rewrite /tensormx_index enum_valK cast_ordKV. Qed.

End IndexTensorConsBij.


Context (R : Type) (u d : {posnum nat}) (k l : nat).
Context (u_ : k.-tuple {posnum nat}) (d_ : l.-tuple {posnum nat}).
Local Notation u_cons := [tuple of u :: u_].
Local Notation d_cons := [tuple of d :: d_].

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

Notation "t ^^ i" := (nindex t i) : ring_scope.
Notation "t \_ i" := (oindex t i) : ring_scope.
Notation "t ^^= i" := ((t^^i).[::]) : ring_scope.
Notation "t \_= i" := ((t\_i).[::]) : ring_scope.

Notation "\tensor ^^ ( i < u ) E" := (nstack (fun i : 'I_u => E))
  (only parsing) : ring_scope.
Notation "\tensor \_ ( i < d ) E" := (ostack (fun i : 'I_d => E))
  (only parsing) : ring_scope.
Notation "\tensor ^^ i E" := (\tensor^^(i < _) E) : ring_scope.
Notation "\tensor \_ i E" := (\tensor\_(i < _) E) : ring_scope.
Notation "\tensor ^^ ( i < u ) => E" := (\tensor^^(i < u) const_t E)
  (only parsing) : ring_scope.
Notation "\tensor \_ ( i < d ) => E" := (\tensor\_(i < d) const_t E)
  (only parsing) : ring_scope.
Notation "\tensor ^^ i => E" := (\tensor^^i const_t E) : ring_scope.
Notation "\tensor \_ i => E" := (\tensor\_i const_t E) : ring_scope.

Section TensorIndexTheory.
Context (R : Type).

Lemma ntensorP (u : {posnum nat}) (k l : nat)
    (u_ : k.-tuple {posnum nat}) (d_ : l.-tuple {posnum nat})
    (t v : 'T[R]_([tuple of u :: u_], d_))
  : t = v <-> forall i, t^^i = v^^i.
Proof.
split=> [->//|eq_i]; apply/val_inj/matrixP=> i j.
move: (eq_i (tensormx_unindex i).1)=> [/matrixP] /(_ (tensormx_unindex i).2 j).
by rewrite !mxE -surjective_pairing tensormx_unindexK.
Qed.

Lemma otensorP (d : {posnum nat}) (k l : nat)
    (u_ : k.-tuple {posnum nat}) (d_ : l.-tuple {posnum nat})
    (t v : 'T[R]_(u_, [tuple of d :: d_]))
  : t = v <-> forall i, t\_i = v\_i.
Proof.
split=> [->//|eq_i]; apply/val_inj/matrixP=> i j.
move: (eq_i (tensormx_unindex j).1)=> [/matrixP] /(_ i (tensormx_unindex j).2).
by rewrite !mxE -surjective_pairing tensormx_unindexK.
Qed.

Lemma ntensor_eqP (u : {posnum nat}) (t v : 'nT[R]_([tuple u]))
  : t = v <-> forall i, t^^=i = v^^=i.
Proof.
split=> [->//|eq_i]; apply/ntensorP=> i.
by move: (eq_i i)=> /tensor_nil_eqP.
Qed.

Lemma otensor_eqP (d : {posnum nat}) (t v : 'oT[R]_([tuple d]))
  : t = v <-> forall i, t\_=i = v\_=i.
Proof.
split=> [->//|eq_i]; apply/otensorP=> i.
by move: (eq_i i)=> /tensor_nil_eqP.
Qed.

Lemma nstackE {u : {posnum nat}} {k l}
    {u_ : k.-tuple {posnum nat}} {d_ : l.-tuple {posnum nat}}
    (f : 'I_u%:num%R -> 'T[R]_(u_, d_)) i
  : (nstack f)^^i = f i.
Proof. by apply/val_inj/matrixP => x y; rewrite !mxE tensormx_indexK. Qed.

Lemma ostackE {d : {posnum nat}} {k l}
    {u_ : k.-tuple {posnum nat}} {d_ : l.-tuple {posnum nat}}
    (f : 'I_d%:num%R -> 'T[R]_(u_, d_)) i
  : (ostack f)\_i = f i.
Proof. by apply/val_inj/matrixP => x y; rewrite !mxE tensormx_indexK. Qed.

Lemma nstack_eqE {u : {posnum nat}} (f : 'I_u%:num%R -> R) i
  : (\tensor^^i0 => f i0)^^=i = f i.
Proof. by rewrite nstackE const_tK. Qed.

Lemma ostack_eqE {d : {posnum nat}} (f : 'I_d%:num%R -> R) i
  : (\tensor\_i0 => f i0)\_=i = f i.
Proof. by rewrite ostackE const_tK. Qed.

End TensorIndexTheory.


Section TensorTuple.

Context {R : Type} {x : {posnum nat}} (k l : nat).
Context (u_ : k.-tuple {posnum nat}) (d_ : l.-tuple {posnum nat}).

Definition ntensor_of_tuple (t : x%:num%R.-tuple R)
  : 'nT[R]_([tuple x]) := \tensor^^i => (tnth t i).

Definition otensor_of_tuple (t : x%:num%R.-tuple R)
  : 'oT[R]_([tuple x]) := \tensor\_i => (tnth t i).

Definition tuple_of_ntensor (t : 'nT[R]_([tuple x])) :=
  [tuple t^^=i | i < x%:num%R].

Definition tuple_of_otensor (t : 'oT[R]_([tuple x])) :=
  [tuple t\_=i | i < x%:num%R].

Lemma ntensor_of_tupleE t i : (ntensor_of_tuple t)^^=i = tnth t i.
Proof. exact: nstack_eqE. Qed.

Lemma otensor_of_tupleE t i : (otensor_of_tuple t)\_=i = tnth t i.
Proof. exact: ostack_eqE. Qed.

Definition nstack_tuple (t : x%:num%R.-tuple 'T[R]_(u_, d_)) :=
  \tensor^^i tnth t i.

Definition ostack_tuple (t : x%:num%R.-tuple 'T[R]_(u_, d_)) :=
  \tensor\_i tnth t i.

Lemma nstack_tupleE t i : (nstack_tuple t)^^i = tnth t i.
Proof. exact: nstackE. Qed.

Lemma ostack_tupleE t i : (ostack_tuple t)\_i = tnth t i.
Proof. exact: ostackE. Qed.
Lemma ntensor_of_tupleK : cancel ntensor_of_tuple tuple_of_ntensor.
Proof.
by move=> t; apply/eq_from_tnth=> i; rewrite tnth_mktuple nstack_eqE.
Qed.

Lemma tuple_of_ntensorK : cancel tuple_of_ntensor ntensor_of_tuple.
Proof.
by move=> t; apply/ntensor_eqP=> i; rewrite nstackE const_tK tnth_mktuple.
Qed.

Lemma otensor_of_tupleK : cancel otensor_of_tuple tuple_of_otensor.
Proof.
by move=> t; apply/eq_from_tnth=> i; rewrite tnth_mktuple ostack_eqE.
Qed.

Lemma tuple_of_otensorK : cancel tuple_of_otensor otensor_of_tuple.
Proof.
by move=> t; apply/otensor_eqP=> i; rewrite ostackE const_tK tnth_mktuple.
Qed.

End TensorTuple.


Notation "[ 'tensor' ^^ t ; .. ; tn ]" :=
  (nstack_tuple [tuple of t :: .. [:: tn] ..]) : ring_scope.
Notation "[ 'tensor' ^^= x ; .. ; xn ]" :=
  (ntensor_of_tuple [tuple of x :: .. [:: xn] ..]) : ring_scope.
Notation "[ 'tensor' \_ t ; .. ; tn ]" :=
  (ostack_tuple [tuple of t :: .. [:: tn] ..]) : ring_scope.
Notation "[ 'tensor' \_= x ; .. ; xn ]" :=
  (otensor_of_tuple [tuple of x :: .. [:: xn] ..]) : ring_scope.


Section TensorMatrix.

Context {R : Type} {n m : {posnum nat}}.

Definition tensor_of_matrix (M : 'M_(_, _)) :
  'T[R]_([tuple n], [tuple m]) :=
    \tensor^^i \tensor\_j => M i j.

Definition matrix_of_tensor t : 'M[R]_(n%:num%R, m%:num%R) :=
  \matrix_(i, j) (t^^i)\_=j.

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

Lemma prod_fcat {n m : nat} (f : {posnum nat} ^ n) (g : {posnum nat} ^ m) :
  (\prod_(i < n) (f i)%:num%R) * (\prod_(i < m) (g i)%:num%R)
    = \prod_(i < n + m) ((f +++ g) i)%:num%R.
Proof.
rewrite big_split_ord; congr (_ * _); apply: eq_bigr => i _.
  by rewrite fcat_lshift.
by rewrite fcat_rshift.
Qed.

Lemma prod_card (m n : nat) : #|{:'I_m * 'I_n}| = (m * n)%N.
Proof. by rewrite card_prod !card_ord. Qed.

Let prod_split (m n : nat) (i : 'I_(m * n)) : 'I_m * 'I_n :=
  enum_val (cast_ord (esym (prod_card m n)) i).

Definition prod_unsplit (m n : nat) (ij : 'I_m * 'I_n) : 'I_(m * n) :=
  cast_ord (prod_card m n) (enum_rank ij).

Definition mults (t : 'T[R]_(u1_, d1_)) (u : 'T[R]_(u2_, d2_))
  : 'T[R]_((u1_ +++ u2_), (d1_ +++ d2_)) :=
  Tensor (\matrix_(i, j) 
    let ii := prod_split (cast_ord (esym (prod_fcat _ _)) i) in
    let jj := prod_split (cast_ord (esym (prod_fcat _ _)) j) in
    (\val t ii.1 jj.1) * (\val u ii.2 jj.2))%R.


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

Notation "*t%R" := mults : function_scope.
Notation "x *t y" := (mults x y) : ring_scope.

Section TensorProductBilinear.


Context {R : comNzRingType}.
Context {k1 l1 k2 l2 : nat}.
Context (u1_ : {posnum nat} ^ k1) (d1_ : {posnum nat} ^ l1).
Context (u2_ : {posnum nat} ^ k2) (d2_ : {posnum nat} ^ l2).


Let mults_linear_l (u : 'T[R]_(u2_, d2_)) :
  GRing.linear_for *:%R (fun t : 'T[R]_(u1_, d1_) => t *t u).
Proof.
move=> a x y; apply/val_inj/matrixP=> i j; rewrite /tensor_val/= !mxE/=.
rewrite mulrDl; congr (_ + _);
  by rewrite mulrA.
Qed.

Let mults_linear_r (t : 'T[R]_(u1_, d1_)) :
  GRing.linear_for *:%R (fun u : 'T[R]_(u2_, d2_) => t *t u).
Proof.
move=> a x y; apply/val_inj/matrixP=> i j; rewrite /tensor_val/= !mxE/=.
by rewrite mulrDr; congr (_ + _); rewrite mulrA (mulrCA a) mulrA.
Qed.

HB.instance Definition _ := bilinear_isBilinear.Build
  R
  'T[R]_(u1_, d1_) 'T[R]_(u2_, d2_)
  'T[R]_((u1_ +++ u2_), (d1_ +++ d2_))
  *:%R *:%R (@mults _ _ _ _ _ _ _ _ _) (conj mults_linear_l mults_linear_r).

End TensorProductBilinear.

Section TensorProductHadamard.


Context {R : comPzRingType}.
Context {k1 l1 k2 l2 : nat}.
Context (u1_ : {posnum nat} ^ k1) (d1_ : {posnum nat} ^ l1).
Context (u2_ : {posnum nat} ^ k2) (d2_ : {posnum nat} ^ l2).


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

Lemma mults_scale {R : comPzSemiRingType} (a b : R)
    (t : 'T[R]_(u1_, d1_)) (u : 'T[R]_(u2_, d2_))
  : (const_t a *h t) *t (const_t b *h u) = const_t (a * b)%R *h (t *t u).
Proof.
by apply/val_inj/matrixP => i j; rewrite /tensor_val /= !mxE /= mulrACA.
Qed.

Lemma mults_hmul_compat {R : comPzSemiRingType} 
    (t1 t2 : 'T[R]_(u1_, d1_)) (u1 u2 : 'T[R]_(u2_, d2_))
  : (t1 *h t2) *t (u1 *h u2) = (t1 *t u1) *h (t2 *t u2).
Proof.
by apply/val_inj/matrixP => i j; rewrite /tensor_val /= !mxE /= mulrACA.
Qed.

End TensorProductRing.

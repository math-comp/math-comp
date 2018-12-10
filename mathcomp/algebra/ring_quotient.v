(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import eqtype choice ssreflect ssrbool ssrnat ssrfun seq.
From mathcomp
Require Import ssralg generic_quotient.


(******************************************************************************)
(*          This file describes quotients of algebraic structures.            *)
(*                                                                            *)
(* It defines a  join hierarchy mxing the structures defined  in file ssralg  *)
(* (up to  unit ring type)  and the  quotType quotient structure  defined in  *)
(* file  generic_quotient.   Every structure  in  that  (join) hierarchy  is  *)
(* parametrized by  a base type  T and the  constants and operations  on the  *)
(* base type  that will  be used  to confer its  algebraic structure  to the  *)
(* quotient.  Note  that T  itself  is  in general  not  an  instance of  an  *)
(* algebraic structure.  The  canonical surjection from T  onto its quotient  *)
(* should be compatible with the parameter operations.                        *)
(*                                                                            *)
(* The  second part  of  the file  provides a  definition  of (non  trivial)  *)
(* decidable ideals  (resp. prime ideals)  of an arbitrary instance  of ring  *)
(* structure and a construction of the quotient  of a ring by such an ideal.  *)
(* These definitions extend the hierarchy  of sub-structures defined in file  *)
(* ssralg (see Module Pred in ssralg), following a similar methodology.       *)
(* Although the definition of the (structure of) quotient of a ring by an     *)
(* ideal is a general one, we do not provide infrastructure for the case of   *)
(* non commutative ring and left or two-sided ideals.                         *)
(*                                                                            *)
(* The file defines the following Structures:                                 *)
(* zmodQuotType T e z n a     == Z-module  obtained  by  quotienting type  T  *)
(*                               with  the  relation  e  and  whose neutral,  *)
(*                               opposite and addition are the images in the  *)
(*                               quotient  of  the  parameters  z,  n and a,  *)
(*                               respectively.                                *)
(* ringQuotType T e z n a o m == ring  obtained  by quotienting  type T with  *)
(*                               the relation e  and  whose zero opposite,    *)
(*                               addition, one, and multiplication are  the   *)
(*                               images  in  the  quotient  of the parameters *)
(*                               z, n, a, o, m, respectively.                 *)
(*   unitRingQuotType ... u i == As in the previous cases, instance of unit   *)
(*                               ring whose unit predicate  is obtained from  *)
(*                               u and the inverse from i.                    *)
(*                 idealr R S == (S : pred R) is a non-trivial, decidable,    *)
(*                               right ideal of the ring R.                   *)
(*           prime_idealr R S == (S : pred R) is a non-trivial, decidable,    *)
(*                               right, prime ideal of the ring R.            *)
(*                                                                            *)
(* The formalization of ideals features the following constructions:          *)
(*       proper_ideal S == the  collective predicate (S : pred R) on the      *)
(*                             ring R is stable by the ring product and does  *)
(*                             contain R's one.                               *)
(*   prime_idealr_closed S  := u * v \in S -> (u \in S) || (v \in S)          *)
(*          idealr_closed S == the collective predicate (S : pred R) on the   *)
(*                             ring  R  represents  a  (right) ideal.  This   *)
(*                             implies its being a proper_ideal.              *)
(*                                                                            *)
(*           MkIdeal idealS == packs   idealS : proper_ideal S   into  an     *)
(*                             idealr S  interface structure  associating the *)
(*                             idealr_closed   property   to  the   canonical *)
(*                             pred_key S  (see ssrbool), which  must already *)
(*                             be an zmodPred (see ssralg).                   *)
(*     MkPrimeIdeal pidealS == packs  pidealS : prime_idealr_closed S  into a *)
(*                             prime_idealr S interface structure associating *)
(*                             the  prime_idealr_closed   property   to   the *)
(*                             canonical pred_key S (see ssrbool), which must *)
(*                             already be an idealr (see above).              *)
(*          {ideal_quot kI} == quotient by the keyed (right) ideal predicate  *)
(*                             kI of a commutative ring R. Note that we indeed*)
(*                             only provide canonical structures of ring      *)
(*                             quotients for the case of commutative rings,   *)
(*                             for which a right ideal is obviously a         *)
(*                             two-sided ideal.                               *)
(*                                                                            *)
(* Note :                                                                     *)
(* if (I : pred R) is a predicate over a ring R and (ideal : idealr I) is an  *)
(* instance of (right) ideal, in order to quantify over an arbitrary (keyed)  *)
(* predicate describing  ideal, use  type (keyed_pred  ideal), as  in:        *)
(*     forall (kI : keyed_pred ideal),...                                     *)
(******************************************************************************)


Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope quotient_scope.

Reserved Notation "{ideal_quot I }" (at level 0, format "{ideal_quot  I }").
Reserved Notation "m = n %[mod_ideal I ]" (at level 70, n at next level,
  format "'[hv ' m '/'  =  n '/'  %[mod_ideal  I ] ']'").
Reserved Notation "m == n %[mod_ideal I ]" (at level 70, n at next level,
  format "'[hv ' m '/'  ==  n '/'  %[mod_ideal  I ] ']'").
Reserved Notation "m <> n %[mod_ideal I ]" (at level 70, n at next level,
  format "'[hv ' m '/'  <>  n '/'  %[mod_ideal  I ] ']'").
Reserved Notation "m != n %[mod_ideal I ]" (at level 70, n at next level,
  format "'[hv ' m '/'  !=  n '/'  %[mod_ideal  I ] ']'").


Section ZmodQuot.

Variable (T : Type).
Variable eqT : rel T.
Variables (zeroT : T) (oppT : T -> T) (addT : T -> T -> T).

Record zmod_quot_mixin_of (Q : Type) (qc : quot_class_of T Q)
  (zc : GRing.Zmodule.class_of Q) := ZmodQuotMixinPack {
    zmod_eq_quot_mixin :> eq_quot_mixin_of eqT qc zc;
    _ : \pi_(QuotTypePack qc) zeroT = 0 :> GRing.Zmodule.Pack zc;
    _ : {morph \pi_(QuotTypePack qc) : x /
         oppT x >-> @GRing.opp (GRing.Zmodule.Pack zc) x};
    _ : {morph \pi_(QuotTypePack qc) : x y /
         addT x y >-> @GRing.add (GRing.Zmodule.Pack zc) x y}
}.

Record zmod_quot_class_of (Q : Type) : Type := ZmodQuotClass {
  zmod_quot_quot_class :> quot_class_of T Q;
  zmod_quot_zmod_class :> GRing.Zmodule.class_of Q;
  zmod_quot_mixin :> zmod_quot_mixin_of
    zmod_quot_quot_class zmod_quot_zmod_class
}.

Structure zmodQuotType : Type := ZmodQuotTypePack {
  zmod_quot_sort :> Type;
  _ : zmod_quot_class_of zmod_quot_sort;
 
}.

Implicit Type zqT : zmodQuotType.

Definition zmod_quot_class zqT : zmod_quot_class_of zqT :=
  let: ZmodQuotTypePack _ cT as qT' := zqT return zmod_quot_class_of qT' in cT.

Definition zmod_eq_quot_class zqT (zqc : zmod_quot_class_of zqT) :
  eq_quot_class_of eqT zqT := EqQuotClass zqc.

Canonical zmodQuotType_eqType zqT := Equality.Pack (zmod_quot_class zqT).
Canonical zmodQuotType_choiceType zqT :=
  Choice.Pack (zmod_quot_class zqT).
Canonical zmodQuotType_zmodType zqT :=
  GRing.Zmodule.Pack (zmod_quot_class zqT).
Canonical zmodQuotType_quotType zqT := QuotTypePack (zmod_quot_class zqT).
Canonical zmodQuotType_eqQuotType zqT := EqQuotTypePack
  (zmod_eq_quot_class (zmod_quot_class zqT)).

Coercion zmodQuotType_eqType : zmodQuotType >-> eqType.
Coercion zmodQuotType_choiceType : zmodQuotType >-> choiceType.
Coercion zmodQuotType_zmodType : zmodQuotType >-> zmodType.
Coercion zmodQuotType_quotType : zmodQuotType >-> quotType.
Coercion zmodQuotType_eqQuotType : zmodQuotType >-> eqQuotType.

Definition ZmodQuotType_pack Q :=
  fun (qT : quotType T) (zT : zmodType) qc zc
  of phant_id (quot_class qT) qc & phant_id (GRing.Zmodule.class zT) zc =>
    fun m => ZmodQuotTypePack (@ZmodQuotClass Q qc zc m).

Definition ZmodQuotMixin_pack Q :=
  fun (qT : eqQuotType eqT) (qc : eq_quot_class_of eqT Q)
      of phant_id (eq_quot_class qT) qc =>
  fun (zT : zmodType) zc of phant_id (GRing.Zmodule.class zT) zc =>
    fun e m0 mN mD => @ZmodQuotMixinPack Q qc zc e m0 mN mD.

Definition ZmodQuotType_clone (Q : Type) qT cT
  of phant_id (zmod_quot_class qT) cT := @ZmodQuotTypePack Q cT.

Lemma zmod_quot_mixinP zqT :
  zmod_quot_mixin_of (zmod_quot_class zqT) (zmod_quot_class zqT).
Proof. by case: zqT => [] ? [] ? ? []. Qed.

Lemma pi_zeror zqT : \pi_zqT zeroT = 0.
Proof. by case: zqT => [] ? [] ? ? []. Qed.

Lemma pi_oppr zqT : {morph \pi_zqT : x / oppT x >-> - x}.
Proof. by case: zqT => [] ? [] ? ? []. Qed.

Lemma pi_addr zqT : {morph \pi_zqT : x y / addT x y >-> x + y}.
Proof. by case: zqT => [] ? [] ? ? []. Qed.

Canonical pi_zero_quot_morph zqT := PiMorph (pi_zeror zqT).
Canonical pi_opp_quot_morph zqT := PiMorph1 (pi_oppr zqT).
Canonical pi_add_quot_morph zqT := PiMorph2 (pi_addr zqT).

End ZmodQuot.

Notation ZmodQuotType z o a Q m :=
  (@ZmodQuotType_pack _ _ z o a Q _ _ _ _ id id m).
Notation "[ 'zmodQuotType' z , o & a 'of' Q ]" :=
  (@ZmodQuotType_clone _ _ z o a Q _ _ id)
  (at level 0, format "[ 'zmodQuotType'  z ,  o  &  a  'of'  Q ]") : form_scope.
Notation ZmodQuotMixin Q m0 mN mD :=
  (@ZmodQuotMixin_pack _ _ _ _ _ Q _ _ id _ _ id (pi_eq_quot _) m0 mN mD).

Section PiAdditive.

Variables (V : zmodType) (equivV : rel V) (zeroV : V).
Variable Q : @zmodQuotType V equivV zeroV -%R +%R.

Lemma pi_is_additive : additive \pi_Q.
Proof. by move=> x y /=; rewrite !piE. Qed.

Canonical pi_additive := Additive pi_is_additive.

End PiAdditive.

Section RingQuot.

Variable (T : Type).
Variable eqT : rel T.
Variables (zeroT : T) (oppT : T -> T) (addT : T -> T -> T).
Variables (oneT : T) (mulT : T -> T -> T).

Record ring_quot_mixin_of (Q : Type) (qc : quot_class_of T Q)
  (rc : GRing.Ring.class_of Q) := RingQuotMixinPack {
    ring_zmod_quot_mixin :> zmod_quot_mixin_of eqT zeroT oppT addT qc rc;
    _ : \pi_(QuotTypePack qc) oneT = 1 :> GRing.Ring.Pack rc;
    _ : {morph \pi_(QuotTypePack qc) : x y /
         mulT x y >-> @GRing.mul (GRing.Ring.Pack rc) x y}
}.

Record ring_quot_class_of (Q : Type) : Type := RingQuotClass {
  ring_quot_quot_class :> quot_class_of T Q;
  ring_quot_ring_class :> GRing.Ring.class_of Q;
  ring_quot_mixin :> ring_quot_mixin_of
    ring_quot_quot_class ring_quot_ring_class
}.

Structure ringQuotType : Type := RingQuotTypePack {
  ring_quot_sort :> Type;
  _ : ring_quot_class_of ring_quot_sort;
 
}.

Implicit Type rqT : ringQuotType.

Definition ring_quot_class rqT : ring_quot_class_of rqT :=
  let: RingQuotTypePack _ cT as qT' := rqT return ring_quot_class_of qT' in cT.

Definition ring_zmod_quot_class rqT (rqc : ring_quot_class_of rqT) :
  zmod_quot_class_of eqT zeroT oppT addT rqT := ZmodQuotClass rqc.
Definition ring_eq_quot_class rqT (rqc : ring_quot_class_of rqT) :
  eq_quot_class_of eqT rqT := EqQuotClass rqc.

Canonical ringQuotType_eqType rqT := Equality.Pack (ring_quot_class rqT).
Canonical ringQuotType_choiceType rqT := Choice.Pack (ring_quot_class rqT).
Canonical ringQuotType_zmodType rqT :=
  GRing.Zmodule.Pack (ring_quot_class rqT).
Canonical ringQuotType_ringType rqT :=
  GRing.Ring.Pack (ring_quot_class rqT).
Canonical ringQuotType_quotType rqT := QuotTypePack (ring_quot_class rqT).
Canonical ringQuotType_eqQuotType rqT :=
  EqQuotTypePack (ring_eq_quot_class (ring_quot_class rqT)).
Canonical ringQuotType_zmodQuotType rqT :=
  ZmodQuotTypePack (ring_zmod_quot_class (ring_quot_class rqT)).

Coercion ringQuotType_eqType : ringQuotType >-> eqType.
Coercion ringQuotType_choiceType : ringQuotType >-> choiceType.
Coercion ringQuotType_zmodType : ringQuotType >-> zmodType.
Coercion ringQuotType_ringType : ringQuotType >-> ringType.
Coercion ringQuotType_quotType : ringQuotType >-> quotType.
Coercion ringQuotType_eqQuotType : ringQuotType >-> eqQuotType.
Coercion ringQuotType_zmodQuotType : ringQuotType >-> zmodQuotType.

Definition RingQuotType_pack Q :=
  fun (qT : quotType T) (zT : ringType) qc rc
  of phant_id (quot_class qT) qc & phant_id (GRing.Ring.class zT) rc =>
    fun m => RingQuotTypePack (@RingQuotClass Q qc rc m).

Definition RingQuotMixin_pack Q :=
  fun (qT : zmodQuotType eqT zeroT oppT addT) =>
  fun (qc : zmod_quot_class_of eqT zeroT oppT addT Q)
      of phant_id (zmod_quot_class qT) qc =>
  fun (rT : ringType) rc of phant_id (GRing.Ring.class rT) rc =>
    fun mZ m1 mM => @RingQuotMixinPack Q qc rc mZ m1 mM.

Definition RingQuotType_clone (Q : Type) qT cT
  of phant_id (ring_quot_class qT) cT := @RingQuotTypePack Q cT.

Lemma ring_quot_mixinP rqT :
  ring_quot_mixin_of (ring_quot_class rqT) (ring_quot_class rqT).
Proof. by case: rqT => [] ? [] ? ? []. Qed.

Lemma pi_oner rqT : \pi_rqT oneT = 1.
Proof. by case: rqT => [] ? [] ? ? []. Qed.

Lemma pi_mulr rqT : {morph \pi_rqT : x y / mulT x y >-> x * y}.
Proof. by case: rqT => [] ? [] ? ? []. Qed.

Canonical pi_one_quot_morph rqT := PiMorph (pi_oner rqT).
Canonical pi_mul_quot_morph rqT := PiMorph2 (pi_mulr rqT).

End RingQuot.

Notation RingQuotType o mul Q mix :=
  (@RingQuotType_pack _ _ _ _ _ o mul Q _ _ _ _ id id mix).
Notation "[ 'ringQuotType' o & m 'of' Q ]" :=
  (@RingQuotType_clone _ _ _ _ _ o m Q _ _ id)
  (at level 0, format "[ 'ringQuotType'  o  &  m  'of'  Q ]") : form_scope.
Notation RingQuotMixin Q m1 mM :=
  (@RingQuotMixin_pack _ _ _ _ _ _ _ Q _ _ id _ _ id (zmod_quot_mixinP _) m1 mM).

Section PiRMorphism.

Variables (R : ringType) (equivR : rel R) (zeroR : R).

Variable Q : @ringQuotType R equivR zeroR -%R +%R 1 *%R.

Lemma pi_is_multiplicative : multiplicative \pi_Q.
Proof. by split; do ?move=> x y /=; rewrite !piE. Qed.

Canonical pi_rmorphism := AddRMorphism pi_is_multiplicative.

End PiRMorphism.

Section UnitRingQuot.

Variable (T : Type).
Variable eqT : rel T.
Variables (zeroT : T) (oppT : T -> T) (addT : T -> T -> T).
Variables (oneT : T) (mulT : T -> T -> T).
Variables (unitT : pred T) (invT : T -> T).

Record unit_ring_quot_mixin_of (Q : Type) (qc : quot_class_of T Q)
  (rc : GRing.UnitRing.class_of Q) := UnitRingQuotMixinPack {
    unit_ring_zmod_quot_mixin :>
        ring_quot_mixin_of eqT zeroT oppT addT oneT mulT qc rc;
    _ : {mono \pi_(QuotTypePack qc) : x /
         unitT x >-> x \in @GRing.unit (GRing.UnitRing.Pack rc)};
    _ : {morph \pi_(QuotTypePack qc) : x /
         invT x >-> @GRing.inv (GRing.UnitRing.Pack rc) x}
}.

Record unit_ring_quot_class_of (Q : Type) : Type := UnitRingQuotClass {
  unit_ring_quot_quot_class :> quot_class_of T Q;
  unit_ring_quot_ring_class :> GRing.UnitRing.class_of Q;
  unit_ring_quot_mixin :> unit_ring_quot_mixin_of
    unit_ring_quot_quot_class unit_ring_quot_ring_class
}.

Structure unitRingQuotType : Type := UnitRingQuotTypePack {
  unit_ring_quot_sort :> Type;
  _ : unit_ring_quot_class_of unit_ring_quot_sort;
 
}.

Implicit Type rqT : unitRingQuotType.

Definition unit_ring_quot_class rqT : unit_ring_quot_class_of rqT :=
  let: UnitRingQuotTypePack _ cT as qT' := rqT
    return unit_ring_quot_class_of qT' in cT.

Definition unit_ring_ring_quot_class rqT (rqc : unit_ring_quot_class_of rqT) :
  ring_quot_class_of eqT zeroT oppT addT oneT mulT rqT := RingQuotClass rqc.
Definition unit_ring_zmod_quot_class rqT (rqc : unit_ring_quot_class_of rqT) :
  zmod_quot_class_of eqT zeroT oppT addT rqT := ZmodQuotClass rqc.
Definition unit_ring_eq_quot_class rqT (rqc : unit_ring_quot_class_of rqT) :
  eq_quot_class_of eqT rqT := EqQuotClass rqc.

Canonical unitRingQuotType_eqType rqT :=
  Equality.Pack (unit_ring_quot_class rqT).
Canonical unitRingQuotType_choiceType rqT :=
  Choice.Pack (unit_ring_quot_class rqT).
Canonical unitRingQuotType_zmodType rqT :=
  GRing.Zmodule.Pack (unit_ring_quot_class rqT).
Canonical unitRingQuotType_ringType rqT :=
  GRing.Ring.Pack (unit_ring_quot_class rqT).
Canonical unitRingQuotType_unitRingType rqT :=
  GRing.UnitRing.Pack (unit_ring_quot_class rqT).
Canonical unitRingQuotType_quotType rqT :=
  QuotTypePack (unit_ring_quot_class rqT).
Canonical unitRingQuotType_eqQuotType rqT :=
  EqQuotTypePack (unit_ring_eq_quot_class (unit_ring_quot_class rqT)).
Canonical unitRingQuotType_zmodQuotType rqT :=
  ZmodQuotTypePack (unit_ring_zmod_quot_class (unit_ring_quot_class rqT)).
Canonical unitRingQuotType_ringQuotType rqT :=
  RingQuotTypePack (unit_ring_ring_quot_class (unit_ring_quot_class rqT)).

Coercion unitRingQuotType_eqType : unitRingQuotType >-> eqType.
Coercion unitRingQuotType_choiceType : unitRingQuotType >-> choiceType.
Coercion unitRingQuotType_zmodType : unitRingQuotType >-> zmodType.
Coercion unitRingQuotType_ringType : unitRingQuotType >-> ringType.
Coercion unitRingQuotType_unitRingType : unitRingQuotType >-> unitRingType.
Coercion unitRingQuotType_quotType : unitRingQuotType >-> quotType.
Coercion unitRingQuotType_eqQuotType : unitRingQuotType >-> eqQuotType.
Coercion unitRingQuotType_zmodQuotType : unitRingQuotType >-> zmodQuotType.
Coercion unitRingQuotType_ringQuotType : unitRingQuotType >-> ringQuotType.

Definition UnitRingQuotType_pack Q :=
  fun (qT : quotType T) (rT : unitRingType) qc rc
  of phant_id (quot_class qT) qc & phant_id (GRing.UnitRing.class rT) rc =>
    fun m => UnitRingQuotTypePack (@UnitRingQuotClass Q qc rc m).

Definition UnitRingQuotMixin_pack Q :=
  fun (qT : ringQuotType eqT zeroT oppT addT oneT mulT) =>
  fun (qc : ring_quot_class_of eqT zeroT oppT addT oneT mulT Q)
      of phant_id (zmod_quot_class qT) qc =>
  fun (rT : unitRingType) rc of phant_id (GRing.UnitRing.class rT) rc =>
    fun mR mU mV => @UnitRingQuotMixinPack Q qc rc mR mU mV.

Definition UnitRingQuotType_clone (Q : Type) qT cT
  of phant_id (unit_ring_quot_class qT) cT := @UnitRingQuotTypePack Q cT.

Lemma unit_ring_quot_mixinP rqT :
  unit_ring_quot_mixin_of (unit_ring_quot_class rqT) (unit_ring_quot_class rqT).
Proof. by case: rqT => [] ? [] ? ? []. Qed.

Lemma pi_unitr rqT : {mono \pi_rqT : x / unitT x >-> x \in GRing.unit}.
Proof. by case: rqT => [] ? [] ? ? []. Qed.

Lemma pi_invr rqT : {morph \pi_rqT : x / invT x >-> x^-1}.
Proof. by case: rqT => [] ? [] ? ? []. Qed.

Canonical pi_unit_quot_morph rqT := PiMono1 (pi_unitr rqT).
Canonical pi_inv_quot_morph rqT := PiMorph1 (pi_invr rqT).

End UnitRingQuot.

Notation UnitRingQuotType u i Q mix :=
  (@UnitRingQuotType_pack _ _ _ _ _ _ _ u i Q _ _ _ _ id id mix).
Notation "[ 'unitRingQuotType' u & i 'of' Q ]" :=
  (@UnitRingQuotType_clone _ _ _ _ _ _ _ u i Q _ _ id)
  (at level 0, format "[ 'unitRingQuotType'  u  &  i  'of'  Q ]") : form_scope.
Notation UnitRingQuotMixin Q mU mV :=
  (@UnitRingQuotMixin_pack _ _ _ _ _ _ _ _ _ Q
    _ _ id _ _ id (zmod_quot_mixinP _) mU mV).

Section IdealDef.

Definition proper_ideal (R : ringType) (S : predPredType R) : Prop :=
  1 \notin S /\ forall a, {in S, forall u, a * u \in S}.

Definition prime_idealr_closed (R : ringType) (S : predPredType R) : Prop :=
  forall u v, u * v \in S -> (u \in S) || (v \in S).

Definition idealr_closed (R : ringType) (S : predPredType R) :=
  [/\ 0 \in S, 1 \notin S & forall a, {in S &, forall u v, a * u + v \in S}].

Lemma idealr_closed_nontrivial R S : @idealr_closed R S -> proper_ideal S.
Proof. by case=> S0 S1 hS; split => // a x xS; rewrite -[_ * _]addr0 hS. Qed.

Lemma idealr_closedB R S : @idealr_closed R S -> zmod_closed S.
Proof. by case=> S0 _ hS; split=> // x y xS yS; rewrite -mulN1r addrC hS. Qed.

Coercion idealr_closedB : idealr_closed >-> zmod_closed.
Coercion idealr_closed_nontrivial : idealr_closed >-> proper_ideal.

Structure idealr (R : ringType) (S : predPredType R) := MkIdeal {
  idealr_zmod :> zmodPred S;
  _ : proper_ideal S
}.

Structure prime_idealr (R : ringType) (S : predPredType R) := MkPrimeIdeal {
  prime_idealr_zmod :> idealr S;
  _ : prime_idealr_closed S
}.

Definition Idealr (R : ringType) (I : predPredType R) (zmodI : zmodPred I)
            (kI : keyed_pred zmodI) : proper_ideal I -> idealr I.
Proof. by move=> kI1; split => //. Qed.

Section IdealTheory.
Variables (R : ringType) (I : predPredType R)
          (idealrI : idealr I) (kI : keyed_pred idealrI).

Lemma idealr1 : 1 \in kI = false.
Proof. by apply: negPf; case: idealrI kI => ? /= [? _] [] /= _ ->. Qed.

Lemma idealMr a u : u \in kI -> a * u \in kI.
Proof.
by case: idealrI kI=> ? /= [? hI] [] /= ? hkI; rewrite !hkI; apply: hI.
Qed.

Lemma idealr0 : 0 \in kI. Proof. exact: rpred0. Qed.

End IdealTheory.

Section PrimeIdealTheory.

Variables (R : comRingType) (I : predPredType R)
          (pidealrI : prime_idealr I) (kI : keyed_pred pidealrI).

Lemma prime_idealrM u v : (u * v \in kI) = (u \in kI) || (v \in kI).
Proof.
apply/idP/idP; last by case/orP => /idealMr hI; rewrite // mulrC.
by case: pidealrI kI=> ? /= hI [] /= ? hkI; rewrite !hkI; apply: hI.
Qed.

End PrimeIdealTheory.

End IdealDef.

Module Quotient.
Section ZmodQuotient.
Variables (R : zmodType) (I : predPredType R)
          (zmodI : zmodPred I) (kI : keyed_pred zmodI).

Definition equiv (x y : R) := (x - y) \in kI.

Lemma equivE x y : (equiv x y) = (x - y \in kI). Proof. by []. Qed.

Lemma equiv_is_equiv : equiv_class_of equiv.
Proof.
split=> [x|x y|y x z]; rewrite !equivE ?subrr ?rpred0 //.
   by rewrite -opprB rpredN.
by move=> *; rewrite -[x](addrNK y) -addrA rpredD.
Qed.

Canonical equiv_equiv := EquivRelPack equiv_is_equiv.
Canonical equiv_encModRel := defaultEncModRel equiv.

Definition type := {eq_quot equiv}.
Definition type_of of phant R := type.

Canonical rquot_quotType := [quotType of type].
Canonical rquot_eqType := [eqType of type].
Canonical rquot_choiceType := [choiceType of type].
Canonical rquot_eqQuotType := [eqQuotType equiv of type].

Lemma idealrBE x y : (x - y) \in kI = (x == y %[mod type]).
Proof. by rewrite piE equivE. Qed.

Lemma idealrDE x y : (x + y) \in kI = (x == - y %[mod type]).
Proof. by rewrite -idealrBE opprK. Qed.

Definition zero : type := lift_cst type 0.
Definition add := lift_op2 type +%R.
Definition opp := lift_op1 type -%R.

Canonical pi_zero_morph := PiConst zero.

Lemma pi_opp : {morph \pi : x / - x >-> opp x}.
Proof.
move=> x; unlock opp; apply/eqP; rewrite piE equivE.
by rewrite -opprD rpredN idealrDE opprK reprK.
Qed.

Canonical pi_opp_morph := PiMorph1 pi_opp.

Lemma pi_add : {morph \pi : x y / x + y >-> add x y}.
Proof.
move=> x y /=; unlock add; apply/eqP; rewrite piE equivE.
rewrite opprD addrAC addrA -addrA.
by rewrite rpredD // (idealrBE, idealrDE) ?pi_opp ?reprK.
Qed.
Canonical pi_add_morph := PiMorph2 pi_add.

Lemma addqA: associative add.
Proof. by move=> x y z; rewrite -[x]reprK -[y]reprK -[z]reprK !piE addrA. Qed.

Lemma addqC: commutative add.
Proof. by move=> x y; rewrite -[x]reprK -[y]reprK !piE addrC. Qed.

Lemma add0q: left_id zero add.
Proof. by move=> x; rewrite -[x]reprK !piE add0r. Qed.

Lemma addNq: left_inverse zero opp add.
Proof. by move=> x; rewrite -[x]reprK !piE addNr. Qed.

Definition rquot_zmodMixin := ZmodMixin addqA addqC add0q addNq.
Canonical rquot_zmodType := Eval hnf in ZmodType type rquot_zmodMixin.

Definition rquot_zmodQuotMixin := ZmodQuotMixin type (lock _) pi_opp pi_add.
Canonical rquot_zmodQuotType := ZmodQuotType 0 -%R +%R type rquot_zmodQuotMixin.

End ZmodQuotient.

Notation "{quot I }" := (@type_of _ _ _ I (Phant _)).

Section RingQuotient.

Variables (R : comRingType) (I : predPredType R)
          (idealI : idealr I) (kI : keyed_pred idealI).

Local Notation type := {quot kI}.

Definition one: type := lift_cst type 1.
Definition mul := lift_op2 type *%R.

Canonical pi_one_morph := PiConst one.

Lemma pi_mul: {morph \pi : x y / x * y >-> mul x y}.
Proof.
move=> x y; unlock mul; apply/eqP; rewrite piE equivE.
rewrite -[_ * _](addrNK (x * repr (\pi_type y))) -mulrBr.
rewrite -addrA -mulrBl rpredD //.
  by rewrite idealMr // idealrDE opprK reprK.
by rewrite mulrC idealMr // idealrDE opprK reprK.
Qed.
Canonical pi_mul_morph := PiMorph2 pi_mul.

Lemma mulqA: associative mul.
Proof. by move=> x y z; rewrite -[x]reprK -[y]reprK -[z]reprK !piE mulrA. Qed.

Lemma mulqC: commutative mul.
Proof. by move=> x y; rewrite -[x]reprK -[y]reprK !piE mulrC. Qed.

Lemma mul1q: left_id one mul.
Proof. by move=> x; rewrite -[x]reprK !piE mul1r. Qed.

Lemma mulq_addl: left_distributive mul +%R.
Proof.
move=> x y z; rewrite -[x]reprK -[y]reprK -[z]reprK.
by apply/eqP; rewrite piE /= mulrDl equiv_refl.
Qed.

Lemma nonzero1q: one != 0.
Proof. by rewrite piE equivE subr0 idealr1. Qed.

Definition rquot_comRingMixin :=
  ComRingMixin mulqA mulqC mul1q mulq_addl nonzero1q.

Canonical rquot_ringType    := Eval hnf in RingType type rquot_comRingMixin.
Canonical rquot_comRingType := Eval hnf in ComRingType type mulqC.

Definition rquot_ringQuotMixin := RingQuotMixin type (lock _) pi_mul.
Canonical rquot_ringQuotType := RingQuotType 1 *%R type rquot_ringQuotMixin.

End RingQuotient.

Section IDomainQuotient.

Variables (R : comRingType) (I : predPredType R)
          (pidealI : prime_idealr I) (kI : keyed_pred pidealI).

Lemma rquot_IdomainAxiom (x y : {quot kI}): x * y = 0 -> (x == 0) || (y == 0).
Proof.
by move=> /eqP; rewrite -[x]reprK -[y]reprK !piE !equivE !subr0 prime_idealrM.
Qed.

End IDomainQuotient.

End Quotient.

Notation "{ideal_quot I }" := (@Quotient.type_of _ _ _ I (Phant _)).
Notation "x == y %[mod_ideal I ]" :=
  (x == y %[mod {ideal_quot I}]) : quotient_scope.
Notation "x = y %[mod_ideal I ]" :=
  (x = y %[mod {ideal_quot I}]) : quotient_scope.
Notation "x != y %[mod_ideal I ]" :=
  (x != y %[mod {ideal_quot I}]) : quotient_scope.
Notation "x <> y %[mod_ideal I ]" :=
  (x <> y %[mod {ideal_quot I}]) : quotient_scope.

Canonical Quotient.rquot_eqType.
Canonical Quotient.rquot_choiceType.
Canonical Quotient.rquot_zmodType.
Canonical Quotient.rquot_ringType.
Canonical Quotient.rquot_comRingType.
Canonical Quotient.rquot_quotType.
Canonical Quotient.rquot_eqQuotType.
Canonical Quotient.rquot_zmodQuotType.
Canonical Quotient.rquot_ringQuotType.

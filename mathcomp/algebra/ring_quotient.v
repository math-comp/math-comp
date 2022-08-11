(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect eqtype choice ssreflect ssrbool ssrnat.
From mathcomp Require Import ssrfun seq ssralg generic_quotient.

(******************************************************************************)
(*          This file describes quotients of algebraic structures.            *)
(*                                                                            *)
(* It defines a join hierarchy mixing the structures defined  in file ssralg  *)
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
(*                 idealr R S == S : {pred R} is a non-trivial, decidable,    *)
(*                               right ideal of the ring R.                   *)
(*           prime_idealr R S == S : {pred R} is a non-trivial, decidable,    *)
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
(*           MkIdeal idealS == packs idealS : proper_ideal S into an idealr S *)
(*                             interface structure associating the            *)
(*                             idealr_closed   property   to  the   canonical *)
(*                             pred_key S  (see ssrbool), which  must already *)
(*                             be a zmodPred (see ssralg).                    *)
(*     MkPrimeIdeal pidealS == packs  pidealS : prime_idealr_closed S  into a *)
(*                             prime_idealr S interface structure associating *)
(*                             the  prime_idealr_closed   property   to   the *)
(*                             canonical pred_key S (see ssrbool), which must *)
(*                             already be an idealr (see above).              *)
(*          {ideal_quot kI} == quotient by the keyed (right) ideal predicate  *)
(*                             kI of a commutative ring R. Note that we only  *)
(*                             provide canonical structures of ring quotients *)
(*                             for commutative rings, in which a right ideal  *)
(*                             is obviously a two-sided ideal.                *)
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

Reserved Notation "{ 'ideal_quot' I }"
  (at level 0, format "{ 'ideal_quot'  I }").
Reserved Notation "m = n %[ 'mod_ideal' I ]" (at level 70, n at next level,
  format "'[hv ' m '/'  =  n '/'  %[ 'mod_ideal'  I ] ']'").
Reserved Notation "m == n %[ 'mod_ideal' I ]" (at level 70, n at next level,
  format "'[hv ' m '/'  ==  n '/'  %[ 'mod_ideal'  I ] ']'").
Reserved Notation "m <> n %[ 'mod_ideal' I ]" (at level 70, n at next level,
  format "'[hv ' m '/'  <>  n '/'  %[ 'mod_ideal'  I ] ']'").
Reserved Notation "m != n %[ 'mod_ideal' I ]" (at level 70, n at next level,
  format "'[hv ' m '/'  !=  n '/'  %[ 'mod_ideal'  I ] ']'").

(* Variable (T : Type).
Variable eqT : rel T.
Variables (zeroT : T) (oppT : T -> T) (addT : T -> T -> T). *)

HB.mixin Record IsZmodQuotient T eqT (zeroT : T) (oppT : T -> T) (addT : T -> T -> T)
(Q : Type) of GRing.Zmodule Q & EqQuotient T eqT Q := {
  pi_zeror : \pi_Q zeroT = 0;
  pi_oppr : {morph \pi_Q : x / oppT x >-> - x};
  pi_addr : {morph \pi_Q : x y / addT x y >-> x + y}
}.

#[short(type="zmodQuotType")]
HB.structure Definition ZmodQuotient T eqT zeroT oppT addT :=
  {Q of IsZmodQuotient T eqT zeroT oppT addT Q &
        GRing.Zmodule Q & EqQuotient T eqT Q}.

Section ZModQuotient.

Variable (T : Type).
Variable eqT : rel T.
Variables (zeroT : T) (oppT : T -> T) (addT : T -> T -> T).
Implicit Type zqT : ZmodQuotient.type eqT zeroT oppT addT.

Canonical pi_zero_quot_morph zqT := PiMorph (@pi_zeror _ _ _ _ _ zqT).
Canonical pi_opp_quot_morph zqT := PiMorph1 (@pi_oppr _ _ _ _ _ zqT).
Canonical pi_add_quot_morph zqT := PiMorph2 (@pi_addr _ _ _ _ _ zqT).

End ZModQuotient.

Module ZModQuotientExports.
Notation "[ 'zmodQuotType' z , o & a 'of' Q ]" :=
  (@ZmodQuotient.clone _ _ z o a Q _)
  (at level 0, format "[ 'zmodQuotType'  z ,  o  &  a  'of'  Q ]") : form_scope.
End ZModQuotientExports.
HB.export ZModQuotientExports.

Section PiAdditive.

Variables (V : zmodType) (equivV : rel V) (zeroV : V).
Variable Q : @zmodQuotType V equivV zeroV -%R +%R.

Lemma pi_is_additive : additive \pi_Q.
Proof. by move=> x y /=; rewrite !piE. Qed.

Canonical pi_additive := Additive pi_is_additive.

End PiAdditive.

(* Variable (T : Type).
Variable eqT : rel T.
Variables (zeroT : T) (oppT : T -> T) (addT : T -> T -> T).
Variables (oneT : T) (mulT : T -> T -> T).
 *)
HB.mixin Record IsRingQuotient T eqT zeroT oppT
addT (oneT : T) (mulT : T -> T -> T) (Q : Type)
  of ZmodQuotient T eqT zeroT oppT addT Q & GRing.Ring Q:=
  {
    pi_oner : \pi_Q oneT = 1;
    pi_mulr : {morph \pi_Q : x y / mulT x y >-> x * y}
  }.

#[short(type="ringQuotType")]
HB.structure Definition RingQuotient T eqT zeroT oppT addT oneT mulT :=
  {Q of IsRingQuotient T eqT zeroT oppT addT oneT mulT Q &
   ZmodQuotient T eqT zeroT oppT addT Q & GRing.Ring Q }.

Section ringQuotient.
(*Clash with the module name RingQuotient*)

Variable (T : Type).
Variable eqT : rel T.
Variables (zeroT : T) (oppT : T -> T) (addT : T -> T -> T) (oneT : T) (mulT : T -> T -> T).
Implicit Type rqT : RingQuotient.type eqT zeroT oppT addT oneT mulT.

Canonical pi_one_quot_morph rqT := PiMorph (@pi_oner _ _ _ _ _ _ _ rqT).
Canonical pi_mul_quot_morph rqT := PiMorph2 (@pi_mulr _ _ _ _ _ _ _ rqT).

End ringQuotient.
Module RingQuotientExports.
(* FIXME: broken *)
(* Notation "[ 'ringQuotType' o & m 'of' Q ]" := *)
(*   (@RingQuotient.clone _ _ _ _ _ o m Q _) *)
(*   (at level 0, format "[ 'ringQuotType'  o  &  m  'of'  Q ]") : form_scope. *)
End RingQuotientExports.
HB.export RingQuotientExports.

Section PiRMorphism.

Variables (R : ringType) (equivR : rel R) (zeroR : R).

Variable Q : @ringQuotType R equivR zeroR -%R +%R 1 *%R.

Lemma pi_is_multiplicative : multiplicative \pi_Q.
Proof. by split; do ?move=> x y /=; rewrite !piE. Qed.

Canonical pi_rmorphism := AddRMorphism pi_is_multiplicative.

End PiRMorphism.

HB.mixin Record IsUnitRingQuotient T eqT zeroT oppT addT oneT mulT (unitT : pred T) (invT : T -> T)
  (Q : Type) of RingQuotient T eqT zeroT oppT addT oneT mulT Q & GRing.UnitRing Q :=
  {
    pi_unitr : {mono \pi_Q : x / unitT x >-> x \in GRing.unit};
    pi_invr : {morph \pi_Q : x / invT x >-> x^-1}
  }.

#[short(type="unitRingQuotType")]
HB.structure Definition UnitRingQuotient T eqT zeroT oppT addT oneT mulT unitT invT :=
  {Q of IsUnitRingQuotient T eqT zeroT oppT addT oneT mulT unitT invT Q & GRing.UnitRing Q & IsQuotient T Q & IsEqQuotient T eqT Q & IsZmodQuotient T eqT zeroT oppT addT Q & IsRingQuotient T eqT zeroT oppT addT oneT mulT Q}.

Section UnitRingQuot.
Variable (T : Type).
Variable eqT : rel T.
Variables (zeroT : T) (oppT : T -> T) (addT : T -> T -> T).
Variables (oneT : T) (mulT : T -> T -> T).
Variables (unitT : pred T) (invT : T -> T).
Implicit Type urqT : UnitRingQuotient.type eqT zeroT oppT addT oneT mulT unitT invT.

Canonical pi_unit_quot_morph urqT := PiMono1 (@pi_unitr _ _ _ _ _ _ _ _ _ urqT).
Canonical pi_inv_quot_morph urqT := PiMorph1 (@pi_invr _ _ _ _ _ _ _ _ _ urqT).

End UnitRingQuot.

Module UnitRingQuotientExports.
Notation "[ 'unitRingQuotType' u & i 'of' Q ]" :=
  (@UnitRingQuotient.clone _ _ _ _ _ _ _ u i Q _)
  (at level 0, format "[ 'unitRingQuotType'  u  &  i  'of'  Q ]") : form_scope.
End UnitRingQuotientExports.
HB.export UnitRingQuotientExports.

Section IdealDef.

Definition proper_ideal (R : ringType) (S : {pred R}) : Prop :=
  1 \notin S /\ forall a, {in S, forall u, a * u \in S}.

Definition prime_idealr_closed (R : ringType) (S : {pred R}) : Prop :=
  forall u v, u * v \in S -> (u \in S) || (v \in S).

Definition idealr_closed (R : ringType) (S : {pred R}) :=
  [/\ 0 \in S, 1 \notin S & forall a, {in S &, forall u v, a * u + v \in S}].

Lemma idealr_closed_nontrivial R S : @idealr_closed R S -> proper_ideal S.
Proof. by case=> S0 S1 hS; split => // a x xS; rewrite -[_ * _]addr0 hS. Qed.

Lemma idealr_closedB R S : @idealr_closed R S -> zmod_closed S.
Proof. by case=> S0 _ hS; split=> // x y xS yS; rewrite -mulN1r addrC hS. Qed.

Coercion idealr_closedB : idealr_closed >-> zmod_closed.
Coercion idealr_closed_nontrivial : idealr_closed >-> proper_ideal.

Structure idealr (R : ringType) (S : {pred R}) := MkIdeal {
  idealr_zmod :> zmodPred S;
  _ : proper_ideal S
}.

Structure prime_idealr (R : ringType) (S : {pred R}) := MkPrimeIdeal {
  prime_idealr_zmod :> idealr S;
  _ : prime_idealr_closed S
}.

Definition Idealr (R : ringType) (I : {pred R}) (zmodI : zmodPred I)
            (kI : keyed_pred zmodI) : proper_ideal I -> idealr I.
Proof. by move=> kI1; split => //. Qed.

Section IdealTheory.
Variables (R : ringType) (I : {pred R})
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

Variables (R : comRingType) (I : {pred R})
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
Variables (R : zmodType) (I : {pred R})
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
Local Notation quot := (type_of (Phant R)).

#[export]
HB.instance Definition _ : EqQuotient R equiv type := EqQuotient.on type.
#[export]
HB.instance Definition _ := Choice.on type.
#[export]
HB.instance Definition _ := EqQuotient.on quot.
#[export]
HB.instance Definition _ := Choice.on quot.

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

#[export]
HB.instance Definition _ := ZmodMixin type addqA addqC add0q addNq.
#[export]
HB.instance Definition _ := GRing.Zmodule.on quot.
#[export]
HB.instance Definition _ := @IsZmodQuotient.Build R equiv 0 -%R +%R type
  (lock _) pi_opp pi_add.
#[export]
HB.instance Definition _ := @ZmodQuotient.on quot.

End ZmodQuotient.

Notation "{ 'quot' I }" := (@type_of _ _ _ I (Phant _)) : type_scope.

Section RingQuotient.

Variables (R : comRingType) (I : {pred R})
          (idealI : idealr I) (kI : keyed_pred idealI).

Definition one : {quot kI} := lift_cst {quot kI} 1.
Definition mul := lift_op2 {quot kI} *%R.

Canonical pi_one_morph := PiConst one.

Lemma pi_mul: {morph \pi : x y / x * y >-> mul x y}.
Proof.
move=> x y; unlock mul; apply/eqP; rewrite piE equivE.
rewrite -[_ * _](addrNK (x * repr (\pi_{quot kI} y))) -mulrBr.
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

#[export]
HB.instance Definition _ := GRing.Zmodule_isComRing.Build (type kI)
  mulqA mulqC mul1q mulq_addl nonzero1q.
#[export]
HB.instance Definition _ := GRing.ComRing.on {quot kI}.

#[export]
HB.instance Definition _ := @IsRingQuotient.Build
  R (equiv kI) 0 -%R +%R 1%R *%R (type kI) (lock _) pi_mul.
#[export]
HB.instance Definition _ := @RingQuotient.on {quot kI}.

End RingQuotient.

Section IDomainQuotient.

Variables (R : comRingType) (I : {pred R})
          (pidealI : prime_idealr I) (kI : keyed_pred pidealI).

Lemma rquot_IdomainAxiom (x y : {quot kI}): x * y = 0 -> (x == 0) || (y == 0).
Proof.
by move=> /eqP; rewrite -[x]reprK -[y]reprK !piE !equivE !subr0 prime_idealrM.
Qed.

End IDomainQuotient.

Module Exports. HB.reexport. End Exports.
End Quotient.

Export Quotient.Exports.

Notation "{ 'ideal_quot' I }" :=
  (@Quotient.type_of _ _ _ I (Phant _)) : type_scope.
Notation "x == y %[ 'mod_ideal' I ]" :=
  (x == y %[mod {ideal_quot I}]) : quotient_scope.
Notation "x = y %[ 'mod_ideal' I ]" :=
  (x = y %[mod {ideal_quot I}]) : quotient_scope.
Notation "x != y %[ 'mod_ideal' I ]" :=
  (x != y %[mod {ideal_quot I}]) : quotient_scope.
Notation "x <> y %[ 'mod_ideal' I ]" :=
  (x <> y %[mod {ideal_quot I}]) : quotient_scope.

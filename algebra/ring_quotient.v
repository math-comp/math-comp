(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype choice ssrnat.
From mathcomp Require Import seq ssralg generic_quotient.

(******************************************************************************)
(*                   Quotients of algebraic structures                        *)
(*                                                                            *)
(* This file defines a join hierarchy mixing the structures defined in file   *)
(* ssralg (up to unit ring type) and the quotType quotient structure defined  *)
(* in generic_quotient.v.   Every structure  in  that  (join) hierarchy  is   *)
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
(*     zmodQuotType T e z n a == Z-module  obtained  by  quotienting type  T  *)
(*                               with  the  relation  e  and  whose neutral,  *)
(*                               opposite and addition are the images in the  *)
(*                               quotient  of  the  parameters  z,  n and a,  *)
(*                               respectively                                 *)
(*                               The HB class is called ZmodQuotient.         *)
(* nzRingQuotType T e z n a o m == non trivial ring  obtained  by quotienting *)
(*                               type T with the relation e  and  whose zero  *)
(*                               opposite, addition, one, and multiplication  *)
(*                               are  the images  in  the  quotient  of the   *)
(*                               parameters z, n, a, o, m, respectively       *)
(*                               The HB class is called NzRingQuotient.       *)
(*   unitRingQuotType ... u i == As in the previous cases, instance of unit   *)
(*                               ring whose unit predicate  is obtained from  *)
(*                               u and the inverse from i                     *)
(*                               The HB class is called UnitRingQuotient.     *)
(*                   idealr R == {pred R} is a non-trivial, decidable,        *)
(*                               right ideal of the ring R                    *)
(*                               (join of GRing.ZmodClosed and ProperIdeal)   *)
(*                               The HB class is called Idealr.               *)
(*             prime_idealr R == {pred R} is a non-trivial, decidable,        *)
(*                               right, prime ideal of the ring R             *)
(*                               The HB class is called PrimeIdealr.          *)
(*                                                                            *)
(* The formalization of ideals features the following constructions:          *)
(*           proper_ideal R == the  collective predicate (S : pred R) on the  *)
(*                             ring R is stable by the ring product and does  *)
(*                             contain R's one                                *)
(*                             The HB class is called ProperIdeal.            *)
(*                 idealr R == join of GRing.ZmodClosed and ProperIdeal       *)
(*   prime_idealr_closed S  := u * v \in S -> (u \in S) || (v \in S)          *)
(*          idealr_closed S == the collective predicate (S : pred R) on the   *)
(*                             ring  R  represents  a  (right) ideal          *)
(*                             This implies its being a proper_ideal.         *)
(*          {ideal_quot kI} == quotient by the keyed (right) ideal predicate  *)
(*                             kI of a commutative ring R. Note that we only  *)
(*                             provide canonical structures of ring quotients *)
(*                             for commutative rings, in which a right ideal  *)
(*                             is obviously a two-sided ideal                 *)
(******************************************************************************)

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope quotient_scope.

Reserved Notation "{ 'ideal_quot' I }" (format "{ 'ideal_quot'  I }").
#[warning="-postfix-notation-not-level-1"]
Reserved Notation "m = n %[ 'mod_ideal' I ]"
  (format "'[hv ' m '/'  =  n '/'  %[ 'mod_ideal'  I ] ']'").
#[warning="-postfix-notation-not-level-1"]
Reserved Notation "m == n %[ 'mod_ideal' I ]"
  (format "'[hv ' m '/'  ==  n '/'  %[ 'mod_ideal'  I ] ']'").
#[warning="-postfix-notation-not-level-1"]
Reserved Notation "m <> n %[ 'mod_ideal' I ]"
  (format "'[hv ' m '/'  <>  n '/'  %[ 'mod_ideal'  I ] ']'").
#[warning="-postfix-notation-not-level-1"]
Reserved Notation "m != n %[ 'mod_ideal' I ]"
  (format "'[hv ' m '/'  !=  n '/'  %[ 'mod_ideal'  I ] ']'").

(* Variable (T : Type).
Variable eqT : rel T.
Variables (zeroT : T) (oppT : T -> T) (addT : T -> T -> T). *)

HB.mixin Record isZmodQuotient T eqT (zeroT : T) (oppT : T -> T) (addT : T -> T -> T)
(Q : Type) of GRing.Zmodule Q & EqQuotient T eqT Q := {
  pi_zeror : \pi_Q zeroT = 0;
  pi_oppr : {morph \pi_Q : x / oppT x >-> - x};
  pi_addr : {morph \pi_Q : x y / addT x y >-> x + y}
}.

#[short(type="zmodQuotType")]
HB.structure Definition ZmodQuotient T eqT zeroT oppT addT :=
  {Q of isZmodQuotient T eqT zeroT oppT addT Q &
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

Section PiAdditive.

Variables (V : zmodType) (equivV : rel V) (zeroV : V).
Variable Q : @zmodQuotType V equivV zeroV -%R +%R.

Lemma pi_is_zmod_morphism : zmod_morphism \pi_Q.
Proof. by move=> x y /=; rewrite !piE. Qed.
#[deprecated(since="mathcomp 2.5.0", use=pi_is_zmod_morphism)]
Definition pi_is_additive := pi_is_zmod_morphism.

HB.instance Definition _ := GRing.isZmodMorphism.Build V Q \pi_Q pi_is_zmod_morphism.

End PiAdditive.

(* Variable (T : Type).
Variable eqT : rel T.
Variables (zeroT : T) (oppT : T -> T) (addT : T -> T -> T).
Variables (oneT : T) (mulT : T -> T -> T).
 *)
HB.mixin Record isNzRingQuotient T eqT zeroT oppT
addT (oneT : T) (mulT : T -> T -> T) (Q : Type)
  of ZmodQuotient T eqT zeroT oppT addT Q & GRing.NzRing Q:=
  {
    pi_oner : \pi_Q oneT = 1;
    pi_mulr : {morph \pi_Q : x y / mulT x y >-> x * y}
  }.

Module isRingQuotient.
#[deprecated(since="mathcomp 2.4.0", use=isNzRingQuotient.Build)]
Notation Build T eqT zeroT oppT addT oneT mulT Q :=
  (isNzRingQuotient.Build T eqT zeroT oppT addT oneT mulT Q) (only parsing).
End isRingQuotient.

#[deprecated(since="mathcomp 2.4.0", use=isNzRingQuotient)]
Notation isRingQuotient T eqT zeroT oppT addT oneT mulT Q :=
  (isNzRingQuotient T eqT zeroT oppT addT oneT mulT Q) (only parsing).

#[short(type="nzRingQuotType")]
HB.structure Definition NzRingQuotient T eqT zeroT oppT addT oneT mulT :=
  {Q of isNzRingQuotient T eqT zeroT oppT addT oneT mulT Q &
   ZmodQuotient T eqT zeroT oppT addT Q & GRing.NzRing Q }.

#[deprecated(since="mathcomp 2.4.0", use=nzRingQuotType)]
Notation ringQuotType := (nzRingQuotType) (only parsing).

Section nzRingQuotient.
(*Clash with the module name NzRingQuotient*)

Variable (T : Type).
Variable eqT : rel T.
Variables (zeroT : T) (oppT : T -> T) (addT : T -> T -> T) (oneT : T) (mulT : T -> T -> T).
Implicit Type rqT : NzRingQuotient.type eqT zeroT oppT addT oneT mulT.

Canonical pi_one_quot_morph rqT := PiMorph (@pi_oner _ _ _ _ _ _ _ rqT).
Canonical pi_mul_quot_morph rqT := PiMorph2 (@pi_mulr _ _ _ _ _ _ _ rqT).

End nzRingQuotient.

Section PiRMorphism.

Variables (R : nzRingType) (equivR : rel R) (zeroR : R).

Variable Q : @nzRingQuotType R equivR zeroR -%R +%R 1 *%R.

Lemma pi_is_monoid_morphism : monoid_morphism \pi_Q.
Proof. by split; do ?move=> x y /=; rewrite !piE. Qed.
#[deprecated(since="mathcomp 2.5.0", use=pi_is_monoid_morphism)]
Definition pi_is_multiplicative :=
  (fun g => (g.2,g.1)) pi_is_monoid_morphism.
HB.instance Definition _ := GRing.isMonoidMorphism.Build R Q \pi_Q
  pi_is_monoid_morphism.

End PiRMorphism.

HB.mixin Record isUnitRingQuotient T eqT zeroT oppT addT oneT mulT (unitT : pred T) (invT : T -> T)
  (Q : Type) of NzRingQuotient T eqT zeroT oppT addT oneT mulT Q & GRing.UnitRing Q :=
  {
    pi_unitr : {mono \pi_Q : x / unitT x >-> x \in GRing.unit};
    pi_invr : {morph \pi_Q : x / invT x >-> x^-1}
  }.

#[short(type="unitRingQuotType")]
HB.structure Definition UnitRingQuotient T eqT zeroT oppT addT oneT mulT unitT invT :=
  {Q of isUnitRingQuotient T eqT zeroT oppT addT oneT mulT unitT invT Q & GRing.UnitRing Q & isQuotient T Q & isEqQuotient T eqT Q & isZmodQuotient T eqT zeroT oppT addT Q & isNzRingQuotient T eqT zeroT oppT addT oneT mulT Q}.

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

Definition proper_ideal (R : nzRingType) (S : {pred R}) : Prop :=
  1 \notin S /\ forall a, {in S, forall u, a * u \in S}.

Definition prime_idealr_closed (R : nzRingType) (S : {pred R}) : Prop :=
  forall u v, u * v \in S -> (u \in S) || (v \in S).

Definition idealr_closed (R : nzRingType) (S : {pred R}) :=
  [/\ 0 \in S, 1 \notin S & forall a, {in S &, forall u v, a * u + v \in S}].

Lemma idealr_closed_nontrivial R S : @idealr_closed R S -> proper_ideal S.
Proof. by case=> S0 S1 hS; split => // a x xS; rewrite -[_ * _]addr0 hS. Qed.

Lemma idealr_closedB R S : @idealr_closed R S -> zmod_closed S.
Proof. by case=> S0 _ hS; split=> // x y xS yS; rewrite -mulN1r addrC hS. Qed.

HB.mixin Record isProperIdeal (R : nzRingType) (S : R -> bool) := {
  proper_ideal_subproof : proper_ideal S
}.

#[short(type="proper_ideal")]
HB.structure Definition ProperIdeal R := {S of isProperIdeal R S}.

#[short(type="idealr")]
HB.structure Definition Idealr (R : nzRingType) :=
  {S of GRing.ZmodClosed R S & ProperIdeal R S}.

HB.mixin Record isPrimeIdealrClosed (R : nzRingType) (S : R -> bool) := {
  prime_idealr_closed_subproof : prime_idealr_closed S
}.

#[short(type="prime_idealr")]
HB.structure Definition PrimeIdealr (R : nzRingType) :=
  {S of Idealr R S & isPrimeIdealrClosed R S}.

HB.factory Record isIdealr (R : nzRingType) (S : R -> bool) := {
  idealr_closed_subproof : idealr_closed S
}.

HB.builders Context R S of isIdealr R S.
HB.instance Definition _ := GRing.isZmodClosed.Build R S
  (idealr_closedB idealr_closed_subproof).
HB.instance Definition _ := isProperIdeal.Build R S
  (idealr_closed_nontrivial idealr_closed_subproof).
HB.end.

Section IdealTheory.
Variables (R : nzRingType) (idealrI : idealr R).
Local Notation I := (idealrI : pred R).

Lemma idealr1 : (1 \in I) = false.
Proof. apply: negPf; exact: proper_ideal_subproof.1. Qed.

Lemma idealMr a u : u \in I -> a * u \in I.
Proof. exact: proper_ideal_subproof.2. Qed.

Lemma idealr0 : 0 \in I. Proof. exact: rpred0. Qed.

End IdealTheory.

Section PrimeIdealTheory.

Variables (R : comNzRingType) (pidealI : prime_idealr R).
Local Notation I := (pidealI : pred R).

Lemma prime_idealrM u v : (u * v \in I) = (u \in I) || (v \in I).
Proof.
apply/idP/idP; last by case/orP => /idealMr hI; rewrite // mulrC.
exact: prime_idealr_closed_subproof.
Qed.

End PrimeIdealTheory.

Module Quotient.
Section ZmodQuotient.
Variables (R : zmodType) (I : zmodClosed R).

Definition equiv (x y : R) := (x - y) \in I.

Lemma equivE x y : (equiv x y) = (x - y \in I). Proof. by []. Qed.

Lemma equiv_is_equiv : equiv_class_of equiv.
Proof.
split=> [x|x y|y x z]; rewrite !equivE ?subrr ?rpred0 //.
   by rewrite -opprB rpredN.
by move=> *; rewrite -[x](addrNK y) -addrA rpredD.
Qed.

Canonical equiv_equiv := EquivRelPack equiv_is_equiv.
Canonical equiv_encModRel := defaultEncModRel equiv.

Definition quot := {eq_quot equiv}.

#[export]
HB.instance Definition _ : EqQuotient R equiv quot := EqQuotient.on quot.
#[export]
HB.instance Definition _ := Choice.on quot.

Lemma idealrBE x y : ((x - y) \in I) = (x == y %[mod quot]).
Proof. by rewrite piE equivE. Qed.

Lemma idealrDE x y : ((x + y) \in I) = (x == - y %[mod quot]).
Proof. by rewrite -idealrBE opprK. Qed.

Definition zero : quot := lift_cst quot 0.
Definition add := lift_op2 quot +%R.
Definition opp := lift_op1 quot -%R.

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
HB.instance Definition _ := GRing.isZmodule.Build quot addqA addqC add0q addNq.
#[export]
HB.instance Definition _ := @isZmodQuotient.Build R equiv 0 -%R +%R quot
  (lock _) pi_opp pi_add.

End ZmodQuotient.

Arguments quot R%_type I%_type.
Notation "{ 'quot' I }" := (quot I) : type_scope.

Section RingQuotient.

Variables (R : comNzRingType) (idealI : idealr R).
Local Notation I := (idealI : pred R).

Definition one : {quot idealI} := lift_cst {quot idealI} 1.
Definition mul := lift_op2 {quot idealI} *%R.

Canonical pi_one_morph := PiConst one.

Lemma pi_mul: {morph \pi : x y / x * y >-> mul x y}.
Proof.
move=> x y; unlock mul; apply/eqP; rewrite piE equivE.
rewrite -[_ * _](addrNK (x * repr (\pi_{quot idealI} y))) -mulrBr.
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
HB.instance Definition _ := GRing.Zmodule_isComNzRing.Build (quot idealI)
  mulqA mulqC mul1q mulq_addl nonzero1q.

#[export]
HB.instance Definition _ := @isNzRingQuotient.Build
  R (equiv idealI) 0 -%R +%R 1%R *%R (quot idealI) (lock _) pi_mul.

End RingQuotient.

Section IDomainQuotient.

Variables (R : comNzRingType) (I : prime_idealr R).

Lemma rquot_IdomainAxiom (x y : {quot I}): x * y = 0 -> (x == 0) || (y == 0).
Proof.
by move=> /eqP; rewrite -[x]reprK -[y]reprK !piE !equivE !subr0 prime_idealrM.
Qed.

End IDomainQuotient.

Module Exports. HB.reexport. End Exports.
End Quotient.

Export Quotient.Exports.

Notation "{ 'ideal_quot' I }" := (@Quotient.quot _ I) : type_scope.
Notation "x == y %[ 'mod_ideal' I ]" :=
  (x == y %[mod {ideal_quot I}]) : quotient_scope.
Notation "x = y %[ 'mod_ideal' I ]" :=
  (x = y %[mod {ideal_quot I}]) : quotient_scope.
Notation "x != y %[ 'mod_ideal' I ]" :=
  (x != y %[mod {ideal_quot I}]) : quotient_scope.
Notation "x <> y %[ 'mod_ideal' I ]" :=
  (x <> y %[mod {ideal_quot I}]) : quotient_scope.

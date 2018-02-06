(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype.
From mathcomp
Require Import bigop ssralg ssrint div ssrnum rat poly closed_field polyrcf.
From mathcomp
Require Import matrix mxalgebra tuple mxpoly zmodp binomial realalg.

(**********************************************************************)
(*   This files defines the extension R[i] of a real field R,         *)
(* and provide it a structure of numeric field with a norm operator.  *)
(* When R is a real closed field, it also provides a structure of     *)
(* algebraically closed field for R[i], using a proof by Derksen      *)
(* (cf comments below, thanks to Pierre Lairez for finding the paper) *)
(**********************************************************************)

Import GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Obligation Tactic := idtac.

Local Open Scope ring_scope.

Reserved Notation "x +i* y"
  (at level 40, left associativity, format "x  +i*  y").
Reserved Notation "x -i* y"
  (at level 40, left associativity, format "x  -i*  y").
Reserved Notation "R [i]"
  (at level 2, left associativity, format "R [i]").

Local Notation sgr := Num.sg.
Local Notation sqrtr := Num.sqrt.

CoInductive complex (R : Type) : Type := Complex { Re : R; Im : R }.

Delimit Scope complex_scope with C.
Local Open Scope complex_scope.

Definition real_complex_def (F : ringType) (phF : phant F) (x : F) :=
  Complex x 0.
Notation real_complex F := (@real_complex_def _ (Phant F)).
Notation "x %:C" := (real_complex _ x)
  (at level 2, left associativity, format "x %:C")  : complex_scope.
Notation "x +i* y" := (Complex x y) : complex_scope.
Notation "x -i* y" := (Complex x (- y)) : complex_scope.
Notation "x *i " := (Complex 0 x) (at level 8, format "x *i") : complex_scope.
Notation "''i'" := (Complex 0 1) : complex_scope.
Notation "R [i]" := (complex R)
  (at level 2, left associativity, format "R [i]").

(* Module ComplexInternal. *)
Module ComplexEqChoice.
Section ComplexEqChoice.

Variable R : Type.

Definition sqR_of_complex (x : R[i]) := let: a +i* b := x in [:: a; b].
Definition complex_of_sqR (x : seq R) :=
  if x is [:: a; b] then Some (a +i* b) else None.

Lemma complex_of_sqRK : pcancel sqR_of_complex complex_of_sqR.
Proof. by case. Qed.

End ComplexEqChoice.
End ComplexEqChoice.

Definition complex_eqMixin (R : eqType) :=
  PcanEqMixin (@ComplexEqChoice.complex_of_sqRK R).
Definition complex_choiceMixin  (R : choiceType) :=
  PcanChoiceMixin (@ComplexEqChoice.complex_of_sqRK R).
Definition complex_countMixin  (R : countType) :=
  PcanCountMixin (@ComplexEqChoice.complex_of_sqRK R).

Canonical complex_eqType (R : eqType) :=
  EqType R[i] (complex_eqMixin R).
Canonical complex_choiceType (R : choiceType) :=
  ChoiceType R[i] (complex_choiceMixin R).
Canonical complex_countType (R : countType) :=
  CountType R[i] (complex_countMixin R).

Lemma eq_complex : forall (R : eqType) (x y : complex R),
  (x == y) = (Re x == Re y) && (Im x == Im y).
Proof.
move=> R [a b] [c d] /=.
apply/eqP/andP; first by move=> [-> ->]; split.
by case; move/eqP->; move/eqP->.
Qed.

Lemma complexr0 : forall (R : ringType) (x : R), x +i* 0 = x%:C. Proof. by []. Qed.

Module ComplexField.
Section ComplexField.

Variable R : rcfType.
Local Notation C := R[i].
Local Notation C0 := ((0 : R)%:C).
Local Notation C1 := ((1 : R)%:C).

Definition addc (x y : R[i]) := let: a +i* b := x in let: c +i* d := y in
  (a + c) +i* (b + d).
Definition oppc (x : R[i]) := let: a +i* b := x in (- a) +i* (- b).

Program Definition complex_zmodMixin := @ZmodMixin _ C0 oppc addc _ _ _ _.
Next Obligation. by move=> [a b] [c d] [e f] /=; rewrite !addrA. Qed.
Next Obligation. by move=> [a b] [c d] /=; congr (_ +i* _); rewrite addrC. Qed.
Next Obligation. by move=> [a b] /=; rewrite !add0r. Qed.
Next Obligation. by move=> [a b] /=; rewrite !addNr. Qed.
Canonical complex_zmodType := ZmodType R[i] complex_zmodMixin.

Definition scalec (a : R) (x : R[i]) := 
  let: b +i* c := x in (a * b) +i* (a * c).

Program Definition complex_lmodMixin := @LmodMixin _ _ scalec _ _ _ _.
Next Obligation. by move=> a b [c d] /=; rewrite !mulrA. Qed.
Next Obligation. by move=> [a b] /=; rewrite !mul1r. Qed.
Next Obligation. by move=> a [b c] [d e] /=; rewrite !mulrDr. Qed.
Next Obligation. by move=> [a b] c d /=; rewrite !mulrDl. Qed.
Canonical complex_lmodType := LmodType R R[i] complex_lmodMixin.

Definition mulc (x y : R[i]) := let: a +i* b := x in let: c +i* d := y in
  ((a * c) - (b * d)) +i* ((a * d) + (b * c)).

Lemma mulcC : commutative mulc.
Proof.
move=> [a b] [c d] /=.
by rewrite [c * b + _]addrC ![_ * c]mulrC ![_ * d]mulrC.
Qed.

Lemma mulcA : associative mulc.
Proof.
move=> [a b] [c d] [e f] /=.
rewrite !mulrDr !mulrDl !mulrN !mulNr !mulrA !opprD -!addrA.
by congr ((_ + _) +i* (_ + _)); rewrite !addrA addrAC;
  congr (_ + _); rewrite addrC.
Qed.

Definition invc (x : R[i]) := let: a +i* b := x in let n2 := (a ^+ 2 + b ^+ 2) in
  (a / n2) -i* (b / n2).

Lemma mul1c : left_id C1 mulc.
Proof. by move=> [a b] /=; rewrite !mul1r !mul0r subr0 addr0. Qed.

Lemma mulc_addl : left_distributive mulc addc.
Proof.
move=> [a b] [c d] [e f] /=; rewrite !mulrDl !opprD -!addrA.
by congr ((_ + _) +i* (_ + _)); rewrite addrCA.
Qed.

Lemma nonzero1c : C1 != C0. Proof. by rewrite eq_complex /= oner_eq0. Qed.

Definition complex_comRingMixin :=
  ComRingMixin mulcA mulcC mul1c mulc_addl nonzero1c.
Canonical complex_ringType :=RingType R[i] complex_comRingMixin.
Canonical complex_comRingType := ComRingType R[i] mulcC.

Lemma mulVc : forall x, x != C0 -> mulc (invc x) x = C1.
Proof.
move=> [a b]; rewrite eq_complex => /= hab; rewrite !mulNr opprK.
rewrite ![_ / _ * _]mulrAC [b * a]mulrC subrr complexr0 -mulrDl mulfV //.
by rewrite paddr_eq0 -!expr2 ?expf_eq0 ?sqr_ge0.
Qed.

Lemma invc0 : invc C0 = C0. Proof. by rewrite /= !mul0r oppr0. Qed.

Definition complex_fieldUnitMixin := FieldUnitMixin mulVc invc0.
Canonical complex_unitRingType := UnitRingType C complex_fieldUnitMixin.
Canonical complex_comUnitRingType := Eval hnf in [comUnitRingType of R[i]].

Lemma field_axiom : GRing.Field.mixin_of complex_unitRingType.
Proof. by []. Qed.

Definition ComplexFieldIdomainMixin := (FieldIdomainMixin field_axiom).
Canonical complex_idomainType := IdomainType R[i] (FieldIdomainMixin field_axiom).
Canonical complex_fieldType := FieldType R[i] field_axiom.

Ltac simpc := do ?
  [ rewrite -[(_ +i* _) - (_ +i* _)]/(_ +i* _)
  | rewrite -[(_ +i* _) + (_ +i* _)]/(_ +i* _)
  | rewrite -[(_ +i* _) * (_ +i* _)]/(_ +i* _)].

Lemma real_complex_is_rmorphism : rmorphism (real_complex R).
Proof.
split; [|split=> //] => a b /=; simpc; first by rewrite subrr.
by rewrite !mulr0 !mul0r addr0 subr0.
Qed.

Canonical real_complex_rmorphism :=
  RMorphism real_complex_is_rmorphism.
Canonical real_complex_additive :=
  Additive real_complex_is_rmorphism.

Lemma Re_is_scalar : scalar (@Re R).
Proof. by move=> a [b c] [d e]. Qed.

Canonical Re_additive := Additive Re_is_scalar.
Canonical Re_linear := Linear Re_is_scalar.

Lemma Im_is_scalar : scalar (@Im R).
Proof. by move=> a [b c] [d e]. Qed.

Canonical Im_additive := Additive Im_is_scalar.
Canonical Im_linear := Linear Im_is_scalar.

Definition lec (x y : R[i]) :=
  let: a +i* b := x in let: c +i* d := y in
    (d == b) && (a <= c).

Definition ltc (x y : R[i]) :=
  let: a +i* b := x in let: c +i* d := y in
    (d == b) && (a < c).

Definition normc (x : R[i]) : R :=
  let: a +i* b := x in sqrtr (a ^+ 2 + b ^+ 2).

Notation normC x := (normc x)%:C.

Lemma ltc0_add : forall x y, ltc 0 x -> ltc 0 y -> ltc 0 (x + y).
Proof.
move=> [a b] [c d] /= /andP [/eqP-> ha] /andP [/eqP-> hc].
by rewrite addr0 eqxx addr_gt0.
Qed.

Lemma eq0_normc x : normc x = 0 -> x = 0.
Proof.
case: x => a b /= /eqP; rewrite sqrtr_eq0 ler_eqVlt => /orP [|]; last first.
  by rewrite ltrNge addr_ge0 ?sqr_ge0.
by rewrite paddr_eq0 ?sqr_ge0 ?expf_eq0 //= => /andP[/eqP -> /eqP ->].
Qed.

Lemma eq0_normC x : normC x = 0 -> x = 0. Proof. by case=> /eq0_normc. Qed.

Lemma ge0_lec_total x y : lec 0 x -> lec 0 y -> lec x y || lec y x.
Proof.
move: x y => [a b] [c d] /= /andP[/eqP -> a_ge0] /andP[/eqP -> c_ge0].
by rewrite eqxx ler_total.
Qed.

Lemma normcM x y : normc (x * y) = normc x * normc y.
Proof.
move: x y => [a b] [c d] /=; rewrite -sqrtrM ?addr_ge0 ?sqr_ge0 //.
rewrite sqrrB sqrrD mulrDl !mulrDr -!exprMn.
rewrite mulrAC [b * d]mulrC !mulrA.
suff -> : forall (u v w z t : R), (u - v + w) + (z + v + t) = u + w + (z + t).
  by rewrite addrAC !addrA.
by move=> u v w z t; rewrite [_ - _ + _]addrAC [z + v]addrC !addrA addrNK.
Qed.

Lemma normCM x y : normC (x * y) = normC x * normC y.
Proof. by rewrite -rmorphM normcM. Qed.

Lemma subc_ge0 x y : lec 0 (y - x) = lec x y.
Proof. by move: x y => [a b] [c d] /=; simpc; rewrite subr_ge0 subr_eq0. Qed.

Lemma lec_def x y : lec x y = (normC (y - x) == y - x).
Proof.
rewrite -subc_ge0; move: (_ - _) => [a b]; rewrite eq_complex /= eq_sym.
have [<- /=|_] := altP eqP; last by rewrite andbF.
by rewrite [0 ^+ _]mul0r addr0 andbT sqrtr_sqr ger0_def.
Qed.

Lemma ltc_def x y : ltc x y = (y != x) && lec x y.
Proof.
move: x y => [a b] [c d] /=; simpc; rewrite eq_complex /=.
by have [] := altP eqP; rewrite ?(andbF, andbT) //= ltr_def.
Qed.

Lemma lec_normD x y : lec (normC (x + y)) (normC x + normC y).
Proof.
move: x y => [a b] [c d] /=; simpc; rewrite addr0 eqxx /=.
rewrite -(@ler_pexpn2r _ 2) -?topredE /= ?(ler_paddr, sqrtr_ge0) //.
rewrite [X in _ <= X] sqrrD ?sqr_sqrtr;
   do ?by rewrite ?(ler_paddr, sqrtr_ge0, sqr_ge0, mulr_ge0) //.
rewrite -addrA addrCA (monoRL (addrNK _) (ler_add2r _)) !sqrrD.
set u := _ *+ 2; set v := _ *+ 2.
rewrite [a ^+ _ + _ + _]addrAC [b ^+ _ + _ + _]addrAC -addrA.
rewrite [u + _] addrC [X in _ - X]addrAC [b ^+ _ + _]addrC.
rewrite [u]lock [v]lock !addrA; set x := (a ^+ 2 + _ + _ + _).
rewrite -addrA addrC addKr -!lock addrC.
have [huv|] := ger0P (u + v); last first.
  by move=> /ltrW /ler_trans -> //; rewrite pmulrn_lge0 // mulr_ge0 ?sqrtr_ge0.
rewrite -(@ler_pexpn2r _ 2) -?topredE //=; last first.
  by rewrite ?(pmulrn_lge0, mulr_ge0, sqrtr_ge0) //.
rewrite -mulr_natl !exprMn !sqr_sqrtr ?(ler_paddr, sqr_ge0) //.
rewrite -mulrnDl -mulr_natl !exprMn ler_pmul2l ?exprn_gt0 ?ltr0n //.
rewrite sqrrD mulrDl !mulrDr -!exprMn addrAC -!addrA ler_add2l !addrA.
rewrite [_ + (b * d) ^+ 2]addrC -addrA ler_add2l.
have: 0 <= (a * d - b * c) ^+ 2 by rewrite sqr_ge0.
by rewrite sqrrB addrAC subr_ge0 [_ * c]mulrC mulrACA [d * _]mulrC.
Qed.

Definition complex_numMixin := NumMixin lec_normD ltc0_add eq0_normC
     ge0_lec_total normCM lec_def ltc_def.
Canonical complex_numDomainType := NumDomainType R[i] complex_numMixin.

End ComplexField.
End ComplexField.

Canonical ComplexField.complex_zmodType.
Canonical ComplexField.complex_lmodType.
Canonical ComplexField.complex_ringType.
Canonical ComplexField.complex_comRingType.
Canonical ComplexField.complex_unitRingType.
Canonical ComplexField.complex_comUnitRingType.
Canonical ComplexField.complex_idomainType.
Canonical ComplexField.complex_fieldType.
Canonical ComplexField.complex_numDomainType.
Canonical complex_numFieldType (R : rcfType) := [numFieldType of complex R].
Canonical ComplexField.real_complex_rmorphism.
Canonical ComplexField.real_complex_additive.
Canonical ComplexField.Re_additive.
Canonical ComplexField.Im_additive.

Definition conjc {R : ringType} (x : R[i]) := let: a +i* b := x in a -i* b.
Notation "x ^*" := (conjc x) (at level 2, format "x ^*") : complex_scope.
Local Open Scope complex_scope.
Delimit Scope complex_scope with C.

Ltac simpc := do ?
  [ rewrite -[- (_ +i* _)%C]/(_ +i* _)%C
  | rewrite -[(_ +i* _)%C - (_ +i* _)%C]/(_ +i* _)%C
  | rewrite -[(_ +i* _)%C + (_ +i* _)%C]/(_ +i* _)%C
  | rewrite -[(_ +i* _)%C * (_ +i* _)%C]/(_ +i* _)%C
  | rewrite -[(_ +i* _)%C ^*]/(_ +i* _)%C
  | rewrite -[_ *: (_ +i* _)%C]/(_ +i* _)%C
  | rewrite -[(_ +i* _)%C <= (_ +i* _)%C]/((_ == _) && (_ <= _))
  | rewrite -[(_ +i* _)%C < (_ +i* _)%C]/((_ == _) && (_ < _))
  | rewrite -[`|(_ +i* _)%C|]/(sqrtr (_ + _))%:C%C
  | rewrite (mulrNN, mulrN, mulNr, opprB, opprD, mulr0, mul0r,
    subr0, sub0r, addr0, add0r, mulr1, mul1r, subrr, opprK, oppr0,
    eqxx) ].


Section ComplexTheory.

Variable R : rcfType.

Lemma ReiNIm : forall x : R[i], Re (x * 'i%C) = - Im x.
Proof. by case=> a b; simpc. Qed.

Lemma ImiRe : forall x : R[i], Im (x * 'i%C) = Re x.
Proof. by case=> a b; simpc. Qed.

Lemma complexE x : x = (Re x)%:C + 'i%C * (Im x)%:C :> R[i].
Proof. by case: x => *; simpc. Qed.

Lemma real_complexE x : x%:C = x +i* 0 :> R[i]. Proof. done. Qed.

Lemma sqr_i : 'i%C ^+ 2 = -1 :> R[i].
Proof. by rewrite exprS; simpc; rewrite -real_complexE rmorphN. Qed.

Lemma complexI : injective (real_complex R). Proof. by move=> x y []. Qed.

Lemma ler0c (x : R) : (0 <= x%:C) = (0 <= x). Proof. by simpc. Qed.

Lemma lecE : forall x y : R[i], (x <= y) = (Im y == Im x) && (Re x <= Re y).
Proof. by move=> [a b] [c d]. Qed.

Lemma ltcE : forall x y : R[i], (x < y) = (Im y == Im x) && (Re x < Re y).
Proof. by move=> [a b] [c d]. Qed.

Lemma lecR : forall x y : R, (x%:C <= y%:C) = (x <= y).
Proof. by move=> x y; simpc. Qed.

Lemma ltcR : forall x y : R, (x%:C < y%:C) = (x < y).
Proof. by move=> x y; simpc. Qed.

Lemma conjc_is_rmorphism : rmorphism (@conjc R).
Proof.
split=> [[a b] [c d]|] /=; first by simpc; rewrite [d - _]addrC.
by split=> [[a b] [c d]|] /=; simpc.
Qed.

Lemma conjc_is_scalable : scalable (@conjc R).
Proof. by move=> a [b c]; simpc. Qed.

Canonical conjc_rmorphism := RMorphism conjc_is_rmorphism.
Canonical conjc_additive := Additive conjc_is_rmorphism.
Canonical conjc_linear := AddLinear conjc_is_scalable.

Lemma conjcK : involutive (@conjc R).
Proof. by move=> [a b] /=; rewrite opprK. Qed.

Lemma mulcJ_ge0 (x : R[i]) : 0 <= x * x^*%C.
Proof.
by move: x=> [a b]; simpc; rewrite mulrC addNr eqxx addr_ge0 ?sqr_ge0.
Qed.

Lemma conjc_real (x : R) : x%:C^* = x%:C.
Proof. by rewrite /= oppr0. Qed.

Lemma ReJ_add (x : R[i]) : (Re x)%:C =  (x + x^*%C) / 2%:R.
Proof.
case: x => a b; simpc; rewrite [0 ^+ 2]mul0r addr0 /=.
rewrite -!mulr2n -mulr_natr -mulrA [_ * (_ / _)]mulrA.
by rewrite divff ?mulr1 // -natrM pnatr_eq0.
Qed.

Lemma ImJ_sub (x : R[i]) : (Im x)%:C =  (x^*%C - x) / 2%:R * 'i%C.
Proof.
case: x => a b; simpc; rewrite [0 ^+ 2]mul0r addr0 /=.
rewrite -!mulr2n -mulr_natr -mulrA [_ * (_ / _)]mulrA.
by rewrite divff ?mulr1 ?opprK // -natrM pnatr_eq0.
Qed.

Lemma ger0_Im (x : R[i]) : 0 <= x -> Im x = 0.
Proof. by move: x=> [a b] /=; simpc => /andP [/eqP]. Qed.

(* Todo : extend theory of : *)
(*   - signed exponents *)

Lemma conj_ge0 : forall x : R[i], (0 <= x ^*) = (0 <= x).
Proof. by move=> [a b] /=; simpc; rewrite oppr_eq0. Qed.

Lemma conjc_nat : forall n, (n%:R : R[i])^* = n%:R.
Proof. exact: rmorph_nat. Qed.

Lemma conjc0 : (0 : R[i]) ^* = 0.
Proof. exact: (conjc_nat 0). Qed.

Lemma conjc1 : (1 : R[i]) ^* = 1.
Proof. exact: (conjc_nat 1). Qed.

Lemma conjc_eq0 : forall x : R[i], (x ^* == 0) = (x == 0).
Proof. by move=> [a b]; rewrite !eq_complex /= eqr_oppLR oppr0. Qed.

Lemma conjc_inv: forall x : R[i], (x^-1)^* = (x^*%C )^-1.
Proof. exact: fmorphV. Qed.

Lemma complex_root_conj (p : {poly R[i]}) (x : R[i]) :
  root (map_poly conjc p) x = root p x^*.
Proof. by rewrite /root -{1}[x]conjcK horner_map /= conjc_eq0. Qed.

Lemma complex_algebraic_trans (T : comRingType) (toR : {rmorphism T -> R}) :
  integralRange toR -> integralRange (real_complex R \o toR).
Proof.
set f := _ \o _ => R_integral [a b].
have integral_real x : integralOver f (x%:C) by apply: integral_rmorph.
rewrite [_ +i* _]complexE.
apply: integral_add => //; apply: integral_mul => //=.
exists ('X^2 + 1).
  by rewrite monicE lead_coefDl ?size_polyXn ?size_poly1 ?lead_coefXn.
by rewrite rmorphD rmorph1 /= ?map_polyXn rootE !hornerE -expr2 sqr_i addNr.
Qed.

Lemma normc_def (z : R[i]) : `|z| = (sqrtr ((Re z)^+2 + (Im z)^+2))%:C.
Proof. by case: z. Qed.

Lemma add_Re2_Im2 (z : R[i]) : ((Re z)^+2 + (Im z)^+2)%:C = `|z|^+2.
Proof. by rewrite normc_def -rmorphX sqr_sqrtr ?addr_ge0 ?sqr_ge0. Qed.

Lemma addcJ (z : R[i]) : z + z^*%C = 2%:R * (Re z)%:C.
Proof. by rewrite ReJ_add mulrC mulfVK ?pnatr_eq0. Qed.

Lemma subcJ (z : R[i]) : z - z^*%C = 2%:R * (Im z)%:C * 'i%C.
Proof.
rewrite ImJ_sub mulrCA mulrA mulfVK ?pnatr_eq0 //.
by rewrite -mulrA ['i%C * _]sqr_i mulrN1 opprB.
Qed.

Lemma complex_real (a b : R) : a +i* b \is Num.real = (b == 0).
Proof.
rewrite realE; simpc; rewrite [0 == _]eq_sym.
by have [] := ltrgtP 0 a; rewrite ?(andbF, andbT, orbF, orbb).
Qed.

Lemma complex_realP (x : R[i]) : reflect (exists y, x = y%:C) (x \is Num.real).
Proof.
case: x=> [a b] /=; rewrite complex_real.
by apply: (iffP eqP) => [->|[c []//]]; exists a.
Qed.

Lemma RRe_real (x : R[i]) : x \is Num.real -> (Re x)%:C = x.
Proof. by move=> /complex_realP [y ->]. Qed.

Lemma RIm_real (x : R[i]) : x \is Num.real -> (Im x)%:C = 0.
Proof. by move=> /complex_realP [y ->]. Qed.

End ComplexTheory.

(* Section RcfDef. *)

(* Variable R : realFieldType. *)
(* Notation C := (complex R). *)

(* Definition rcf_odd := forall (p : {poly R}), *)
(*   ~~odd (size p) -> {x | p.[x] = 0}. *)
(* Definition rcf_square := forall x : R, *)
(*   {y | (0 <= y) && if 0 <= x then (y ^ 2 == x) else y == 0}. *)

(* Lemma rcf_odd_sqr_from_ivt : rcf_axiom R -> rcf_odd * rcf_square. *)
(* Proof. *)
(* move=> ivt. *)
(* split. *)
(*   move=> p sp. *)
(*   move: (ivt p). *)
(*   admit. *)
(* move=> x. *)
(* case: (boolP (0 <= x)) (@ivt ('X^2 - x%:P) 0 (1 + x))=> px; last first. *)
(*   by move=> _; exists 0; rewrite lerr eqxx. *)
(* case. *)
(* * by rewrite ler_paddr ?ler01. *)
(* * rewrite !horner_lin oppr_le0 px /=. *)
(*   rewrite subr_ge0 (@ler_trans _ (1 + x)) //. *)
(*     by rewrite ler_paddl ?ler01 ?lerr. *)
(*   by rewrite ler_pemulr // addrC -subr_ge0 ?addrK // subr0 ler_paddl ?ler01. *)
(* * move=> y hy; rewrite /root !horner_lin; move/eqP. *)
(*   move/(canRL (@addrNK _ _)); rewrite add0r=> <-. *)
(* by exists y; case/andP: hy=> -> _; rewrite eqxx. *)
(* Qed. *)

(* Lemma ivt_from_closed : GRing.ClosedField.axiom [ringType of C] -> rcf_axiom R. *)
(* Proof. *)
(* rewrite /GRing.ClosedField.axiom /= => hclosed. *)
(* move=> p a b hab. *)
(* Admitted. *)

(* Lemma closed_form_rcf_odd_sqr : rcf_odd -> rcf_square *)
(*   -> GRing.ClosedField.axiom [ringType of C]. *)
(* Proof. *)
(* Admitted. *)

(* Lemma closed_form_ivt : rcf_axiom R -> GRing.ClosedField.axiom [ringType of C]. *)
(* Proof. *)
(* move/rcf_odd_sqr_from_ivt; case. *)
(* exact: closed_form_rcf_odd_sqr. *)
(* Qed. *)

(* End RcfDef. *)

Section ComplexClosed.

Variable R : rcfType.

Definition sqrtc (x : R[i]) : R[i] :=
  let: a +i* b := x in
  let sgr1 b := if b == 0 then 1 else sgr b in
  let r := sqrtr (a^+2 + b^+2) in
  (sqrtr ((r + a)/2%:R)) +i* (sgr1 b * sqrtr ((r - a)/2%:R)).

Lemma sqr_sqrtc : forall x, (sqrtc x) ^+ 2 = x.
Proof.
have sqr: forall x : R, x ^+ 2 = x * x.
  by move=> x; rewrite exprS expr1.
case=> a b; rewrite exprS expr1; simpc.
have F0: 2%:R != 0 :> R by rewrite pnatr_eq0.
have F1: 0 <= 2%:R^-1 :> R by rewrite invr_ge0 ler0n.
have F2: `|a| <= sqrtr (a^+2 + b^+2).
  rewrite -sqrtr_sqr ler_wsqrtr //.
  by rewrite addrC -subr_ge0 addrK exprn_even_ge0.
have F3: 0 <= (sqrtr (a ^+ 2 + b ^+ 2) - a) / 2%:R.
  rewrite mulr_ge0 // subr_ge0 (ler_trans _ F2) //.
  by rewrite -(maxrN a) ler_maxr lerr.
have F4: 0 <= (sqrtr (a ^+ 2 + b ^+ 2) + a) / 2%:R.
  rewrite mulr_ge0 // -{2}[a]opprK subr_ge0 (ler_trans _ F2) //.
  by rewrite -(maxrN a) ler_maxr lerr orbT.
congr (_ +i* _); set u := if _ then _ else _.
  rewrite mulrCA !mulrA.
  have->: (u * u) = 1.
    rewrite /u; case: (altP (_ =P _)); rewrite ?mul1r //.
    by rewrite -expr2 sqr_sg => ->.
  rewrite mul1r -!sqr !sqr_sqrtr //.
  rewrite [_+a]addrC -mulrBl opprD addrA addrK.
  by rewrite opprK -mulr2n -mulr_natl [_*a]mulrC mulfK.
rewrite mulrCA -mulrA -mulrDr [sqrtr _ * _]mulrC.
rewrite -mulr2n -sqrtrM // mulrAC !mulrA ?[_ * (_ - _)]mulrC -subr_sqr.
rewrite sqr_sqrtr; last first.
  by rewrite ler_paddr // exprn_even_ge0.
rewrite [_^+2 + _]addrC addrK -mulrA -expr2 sqrtrM ?exprn_even_ge0 //.
rewrite !sqrtr_sqr -mulr_natr.
rewrite [`|_^-1|]ger0_norm // -mulrA [_ * _%:R]mulrC divff //.
rewrite mulr1 /u; case: (_ =P _)=>[->|].
  by rewrite normr0 mulr0.
by rewrite mulr_sg_norm.
Qed.

Lemma sqrtc_sqrtr :
  forall (x : R[i]), 0 <= x -> sqrtc x = (sqrtr (Re x))%:C.
Proof.
move=> [a b] /andP [/eqP->] /= a_ge0.
rewrite eqxx mul1r [0 ^+ _]exprS mul0r addr0 sqrtr_sqr.
rewrite ger0_norm // subrr mul0r sqrtr0 -mulr2n.
by rewrite -[_*+2]mulr_natr mulfK // pnatr_eq0.
Qed.

Lemma sqrtc0 : sqrtc 0 = 0.
Proof. by rewrite sqrtc_sqrtr ?lerr // sqrtr0. Qed.

Lemma sqrtc1 : sqrtc 1 = 1.
Proof. by rewrite sqrtc_sqrtr ?ler01 // sqrtr1. Qed.

Lemma sqrtN1 : sqrtc (-1) = 'i.
Proof.
rewrite /sqrtc /= oppr0 eqxx [0^+_]exprS mulr0 addr0.
rewrite exprS expr1 mulN1r opprK sqrtr1 subrr mul0r sqrtr0.
by rewrite mul1r -mulr2n divff ?sqrtr1 // pnatr_eq0.
Qed.

Lemma sqrtc_ge0 (x : R[i]) : (0 <= sqrtc x) = (0 <= x).
Proof.
apply/idP/idP=> [psx|px]; last first.
  by rewrite sqrtc_sqrtr // lecR sqrtr_ge0.
by rewrite -[x]sqr_sqrtc exprS expr1 mulr_ge0.
Qed.

Lemma sqrtc_eq0 (x : R[i]) : (sqrtc x == 0) = (x == 0).
Proof.
apply/eqP/eqP=> [eqs|->]; last by rewrite sqrtc0.
by rewrite -[x]sqr_sqrtc eqs exprS mul0r.
Qed.

Lemma normcE x : `|x| = sqrtc (x * x^*%C).
Proof.
case: x=> a b; simpc; rewrite [b * a]mulrC addNr sqrtc_sqrtr //.
by simpc; rewrite /= addr_ge0 ?sqr_ge0.
Qed.

Lemma sqr_normc (x : R[i]) : (`|x| ^+ 2) = x * x^*%C.
Proof. by rewrite normcE sqr_sqrtc. Qed.

Lemma normc_ge_Re (x : R[i]) : `|Re x|%:C <= `|x|.
Proof.
by case: x => a b; simpc; rewrite -sqrtr_sqr ler_wsqrtr // ler_addl sqr_ge0.
Qed.

Lemma normcJ (x : R[i]) :  `|x^*%C| = `|x|.
Proof. by case: x => a b; simpc; rewrite /= sqrrN. Qed.

Lemma invc_norm (x : R[i]) : x^-1 = `|x|^-2 * x^*%C.
Proof.
case: (altP (x =P 0)) => [->|dx]; first by rewrite rmorph0 mulr0 invr0.
apply: (mulIf dx); rewrite mulrC divff // -mulrA [_^*%C * _]mulrC -(sqr_normc x).
by rewrite mulVf // expf_neq0 ?normr_eq0.
Qed.

Lemma canonical_form (a b c : R[i]) :
  a != 0 ->
  let d := b ^+ 2 - 4%:R * a * c in
  let r1 := (- b - sqrtc d) / 2%:R / a in
  let r2 := (- b + sqrtc d) / 2%:R / a in
  a *: 'X^2 + b *: 'X + c%:P = a *: (('X - r1%:P) * ('X - r2%:P)).
Proof.
move=> a_neq0 d r1 r2.
rewrite !(mulrDr, mulrDl, mulNr, mulrN, opprK, scalerDr).
rewrite [_ * _%:P]mulrC !mul_polyC !scalerN !scalerA -!addrA; congr (_ + _).
rewrite addrA; congr (_ + _).
  rewrite -opprD -scalerDl -scaleNr; congr(_ *: _).
  rewrite ![a * _]mulrC !divfK // !mulrDl addrACA !mulNr addNr addr0.
  by rewrite -opprD opprK -mulrDr -mulr2n -mulr_natl divff ?mulr1 ?pnatr_eq0.
symmetry; rewrite -!alg_polyC scalerA; congr (_%:A).
rewrite [a * _]mulrC divfK // /r2 mulrA mulrACA -invfM -natrM -subr_sqr.
rewrite sqr_sqrtc sqrrN /d opprB addrC addrNK -2!mulrA.
by rewrite mulrACA -natf_div // mul1r mulrAC divff ?mul1r.
Qed.

Lemma monic_canonical_form (b c : R[i]) :
  let d := b ^+ 2 - 4%:R * c in
  let r1 := (- b - sqrtc d) / 2%:R in
  let r2 := (- b + sqrtc d) / 2%:R in
  'X^2 + b *: 'X + c%:P = (('X - r1%:P) * ('X - r2%:P)).
Proof.
by rewrite /= -['X^2]scale1r canonical_form ?oner_eq0 // scale1r mulr1 !divr1.
Qed.

Section extramx.
(* missing lemmas from matrix.v or mxalgebra.v *)

Lemma mul_mx_rowfree_eq0 (K : fieldType) (m n p: nat)
                         (W : 'M[K]_(m,n)) (V : 'M[K]_(n,p)) :
  row_free V -> (W *m V == 0) = (W == 0).
Proof. by move=> free; rewrite -!mxrank_eq0 mxrankMfree ?mxrank_eq0. Qed.

Lemma sub_sums_genmxP (F : fieldType) (I : finType) (P : pred I) (m n : nat)
 (A : 'M[F]_(m, n)) (B_ : I -> 'M_(m, n)) :
reflect (exists u_ : I -> 'M_m, A = \sum_(i | P i) u_ i *m B_ i)
  (A <= \sum_(i | P i) <<B_ i>>)%MS.
Proof.
apply: (iffP idP); last first.
  by move=> [u_ ->]; rewrite summx_sub_sums // => i _; rewrite genmxE submxMl.
move=> /sub_sumsmxP [u_ hA].
have Hu i : exists v, u_ i *m  <<B_ i>>%MS = v *m B_ i.
  by apply/submxP; rewrite (submx_trans (submxMl _ _)) ?genmxE.
exists (fun i => projT1 (sig_eqW (Hu i))); rewrite hA.
by apply: eq_bigr => i /= P_i; case: sig_eqW.
Qed.

Lemma mulmxP (K : fieldType) (m n : nat) (A B : 'M[K]_(m, n)) :
  reflect (forall u : 'rV__, u *m A = u *m B) (A == B).
Proof.
apply: (iffP eqP) => [-> //|eqAB].
apply: (@row_full_inj _ _ _ _ 1%:M); first by rewrite row_full_unit unitmx1.
by apply/row_matrixP => i; rewrite !row_mul eqAB.
Qed.

Section Skew.

Variable (K : numFieldType).

Implicit Types (phK : phant K) (n : nat).

Definition skew_vec n i j : 'rV[K]_(n * n) :=
   (mxvec ((delta_mx i j)) - (mxvec (delta_mx j i))).

Definition skew_def phK n : 'M[K]_(n * n) :=
  (\sum_(i | ((i.2 : 'I__) < (i.1 : 'I__))%N) <<skew_vec i.1 i.2>>)%MS.

Variable (n : nat).
Local Notation skew := (@skew_def (Phant K) n).


Lemma skew_direct_sum : mxdirect skew.
Proof.
apply/mxdirect_sumsE => /=; split => [i _|]; first exact: mxdirect_trivial.
apply/mxdirect_sumsP => [] [i j] /= lt_ij; apply/eqP; rewrite -submx0.
apply/rV_subP => v; rewrite sub_capmx => /andP []; rewrite !genmxE.
move=> /submxP [w ->] /sub_sums_genmxP [/= u_].
move/matrixP => /(_ 0 (mxvec_index i j)); rewrite !mxE /= big_ord1.
rewrite /skew_vec /= !mxvec_delta !mxE !eqxx /=.
have /(_ _ _ (_, _) (_, _)) /= eq_mviE :=
  inj_eq (bij_inj (onT_bij (curry_mxvec_bij _ _))).
rewrite eq_mviE xpair_eqE -!val_eqE /= eq_sym andbb.
rewrite ltn_eqF // subr0 mulr1 summxE big1.
  rewrite [w as X in X *m _]mx11_scalar => ->.
  by rewrite mul_scalar_mx scale0r submx0.
move=> [i' j'] /= /andP[lt_j'i'].
rewrite xpair_eqE /= => neq'_ij.
rewrite /= !mxvec_delta !mxE big_ord1 !mxE !eqxx !eq_mviE.
rewrite !xpair_eqE /= [_ == i']eq_sym [_ == j']eq_sym (negPf neq'_ij) /=.
set z := (_ && _); suff /negPf -> : ~~ z by rewrite subrr mulr0.
by apply: contraL lt_j'i' => /andP [/eqP <- /eqP <-]; rewrite ltnNge ltnW.
Qed.
Hint Resolve skew_direct_sum.

Lemma rank_skew : \rank skew = (n * n.-1)./2.
Proof.
rewrite /skew (mxdirectP _) //= -bin2 -triangular_sum big_mkord.
rewrite (eq_bigr (fun _ => 1%N)); last first.
  move=> [i j] /= lt_ij; rewrite genmxE.
  apply/eqP; rewrite eqn_leq rank_leq_row /= lt0n mxrank_eq0.
  rewrite /skew_vec /= !mxvec_delta /= subr_eq0.
  set j1 := mxvec_index _ _.
  apply/negP => /eqP /matrixP /(_ 0 j1) /=; rewrite !mxE eqxx /=.
  have /(_ _ _ (_, _) (_, _)) -> :=
    inj_eq (bij_inj (onT_bij (curry_mxvec_bij _ _))).
  rewrite xpair_eqE -!val_eqE /= eq_sym andbb ltn_eqF //.
  by move/eqP; rewrite oner_eq0.
transitivity (\sum_(i < n) (\sum_(j < n | j < i) 1))%N.
  by rewrite pair_big_dep.
apply: eq_bigr => [] [[|i] Hi] _ /=; first by rewrite big1.
rewrite (eq_bigl _ _ (fun _ => ltnS _ _)).
have [n_eq0|n_gt0] := posnP n; first by move: Hi (Hi); rewrite {1}n_eq0.
rewrite -[n]prednK // big_ord_narrow_leq /=.
  by rewrite -ltnS prednK // (leq_trans _ Hi).
by rewrite sum_nat_const card_ord muln1.
Qed.

Lemma skewP (M : 'rV_(n * n)) :
  reflect ((vec_mx M)^T = - vec_mx M) (M <= skew)%MS.
Proof.
apply: (iffP idP).
  move/sub_sumsmxP => [v ->]; rewrite !linear_sum /=.
  apply: eq_bigr => [] [i j] /= lt_ij; rewrite !mulmx_sum_row !linear_sum /=.
  apply: eq_bigr => k _; rewrite !linearZ /=; congr (_ *: _) => {v}.
  set r := << _ >>%MS; move: (row _ _) (row_sub k r) => v.
  move: @r; rewrite /= genmxE => /sub_rVP [a ->]; rewrite !linearZ /=.
  by rewrite /skew_vec !linearB /= !mxvecK !scalerN opprK addrC !trmx_delta.
move=> skewM; pose M' := vec_mx M.
pose xM i j := (M' i j - M' j i) *: skew_vec i j.
suff -> : M = 2%:R^-1 *:
   (\sum_(i | true && ((i.2 : 'I__) < (i.1 : 'I__))%N) xM i.1 i.2).
  rewrite scalemx_sub // summx_sub_sums // => [] [i j] /= lt_ij.
  by rewrite scalemx_sub // genmxE.
rewrite /xM /= /skew_vec (eq_bigr _ (fun _ _ => scalerBr _ _ _)).
rewrite big_split /= sumrN !(eq_bigr _ (fun _ _ => scalerBl _ _ _)).
rewrite !big_split /= !sumrN opprD ?opprK addrACA [- _ + _]addrC.
rewrite -!sumrN -2!big_split /=.
rewrite /xM /= /skew_vec -!(eq_bigr _ (fun _ _ => scalerBr _ _ _)).
apply: (can_inj vec_mxK); rewrite !(linearZ, linearB, linearD, linear_sum) /=.
have -> /= : vec_mx M = 2%:R^-1 *: (M' - M'^T).
  by rewrite skewM opprK -mulr2n -scaler_nat scalerA mulVf ?pnatr_eq0 ?scale1r.
rewrite {1 2}[M']matrix_sum_delta; congr (_ *: _).
rewrite pair_big /= !linear_sum /= -big_split /=.
rewrite (bigID (fun ij => (ij.2 : 'I__) < (ij.1 : 'I__))%N) /=; congr (_ + _).
  apply: eq_bigr => [] [i j] /= lt_ij.
  by rewrite !linearZ linearB /= ?mxvecK trmx_delta scalerN scalerBr.
rewrite (bigID (fun ij => (ij.1 : 'I__) == (ij.2 : 'I__))%N) /=.
rewrite big1 ?add0r; last first.
  by move=> [i j] /= /andP[_ /eqP ->]; rewrite linearZ /= trmx_delta subrr.
rewrite (@reindex_inj _ _ _ _ (fun ij => (ij.2, ij.1))) /=; last first.
  by move=> [? ?] [? ?] [] -> ->.
apply: eq_big => [] [i j] /=; first by rewrite -leqNgt ltn_neqAle andbC.
by rewrite !linearZ linearB /= ?mxvecK trmx_delta scalerN scalerBr.
Qed.

End Skew.

Notation skew K n := (@skew_def _ (Phant K) n).

Section Companion.

Variable (K : fieldType).

Lemma companion_subproof (p : {poly K}) :
  {M : 'M[K]_((size p).-1)| p \is monic -> char_poly M = p}.
Proof.
have simp := (castmxE, mxE, castmx_id, cast_ord_id).
case Hsp: (size p) => [|sp] /=.
  move/eqP: Hsp; rewrite size_poly_eq0 => /eqP ->.
  by exists 0; rewrite qualifE lead_coef0 eq_sym oner_eq0.
case: sp => [|sp] in Hsp *.
  move: Hsp => /eqP/size_poly1P/sig2_eqW [c c_neq0 ->].
  by exists ((-c)%:M); rewrite monicE lead_coefC => /eqP ->; apply: det_mx00.
have addn1n n : (n + 1 = 1 + n)%N by rewrite addn1.
exists (castmx (erefl _, addn1n _)
       (block_mx (\row_(i < sp) - p`_(sp - i)) (-p`_0)%:M
                 1%:M                        0)).
elim/poly_ind: p sp Hsp (addn1n _) => [|p c IHp] sp; first by rewrite size_poly0.
rewrite size_MXaddC.
have [->|p_neq0] //= := altP eqP; first by rewrite size_poly0; case: ifP.
move=> [Hsp] eq_cast.
rewrite monicE lead_coefDl ?size_polyC ?size_mul ?polyX_eq0 //; last first.
  by rewrite size_polyX addn2 Hsp ltnS (leq_trans (leq_b1 _)).
rewrite lead_coefMX -monicE => p_monic.
rewrite -/_`_0 coefD coefMX coefC eqxx add0r.
case: sp => [|sp] in Hsp p_neq0 p_monic eq_cast *.
  move: Hsp p_monic => /eqP/size_poly1P [l l_neq0 ->].
  rewrite monicE lead_coefC => /eqP ->; rewrite mul1r.
  rewrite /char_poly /char_poly_mx thinmx0 flatmx0 castmx_id.
  set b := (block_mx _ _ _ _); rewrite [map_mx _ b]map_block_mx => {b}.
  rewrite !map_mx0 map_scalar_mx (@opp_block_mx _ 1 0 0 1) !oppr0.
  set b := block_mx _ _ _ _; rewrite (_ : b = c%:P%:M); last first.
    apply/matrixP => i j; rewrite !mxE; case: splitP => k /= Hk; last first.
      by move: (ltn_ord i); rewrite Hk.
    rewrite !ord1 !mxE; case: splitP => {k Hk} k /= Hk; first by move: (ltn_ord k).
    by rewrite ord1 !mxE mulr1n rmorphN opprK.
  by rewrite -rmorphD det_scalar.
rewrite /char_poly /char_poly_mx (expand_det_col _ ord_max).
rewrite big_ord_recr /= big_ord_recl //= big1 ?simp; last first.
  move=> i _; rewrite !simp.
  case: splitP => k /=; first by rewrite /bump leq0n ord1.
  rewrite /bump leq0n => [] [Hik]; rewrite !simp.
  case: splitP => l /=; first by move/eqP; rewrite gtn_eqF.
  rewrite !ord1 addn0 => _ {l}; rewrite !simp -!val_eqE /=.
  by rewrite /bump leq0n ltn_eqF ?ltnS ?add1n // mulr0n subrr mul0r.
case: splitP => i //=; rewrite !ord1 !simp => _ {i}.
case: splitP => i //=; first by move/eqP; rewrite gtn_eqF.
rewrite ord1 !simp => {i}.
case: splitP => i //=; rewrite ?ord1 ?simp // => /esym [eq_i_sp] _.
case: splitP => j //=; first by move/eqP; rewrite gtn_eqF.
rewrite ord1 !simp => {j} _.
rewrite eqxx mulr0n ?mulr1n rmorphN ?opprK !add0r !addr0 subr0 /=.
rewrite -[c%:P in X in _ = X]mulr1 addrC mulrC.
rewrite /cofactor -signr_odd addnn odd_double expr0 mul1r /=.
rewrite !linearB /= -!map_col' -!map_row'.
congr (_ * 'X + c%:P * _).
  have coefE := (coefD, coefMX, coefC, eqxx, add0r, addr0).
  rewrite -[X in _ = X](IHp sp Hsp _ p_monic) /char_poly /char_poly_mx.
   congr (\det (_ - _)).
    apply/matrixP => k l; rewrite !simp -val_eqE /=;
    by rewrite /bump ![(sp < _)%N]ltnNge ?leq_ord.
  apply/matrixP => k l; rewrite !simp.
  case: splitP => k' /=; rewrite ?ord1 /bump ltnNge leq_ord add0n.
    case: splitP => [k'' /= |k'' -> //]; rewrite ord1 !simp => k_eq0 _.
    case: splitP => l' /=; rewrite ?ord1 /bump ltnNge leq_ord add0n !simp;
      last by move/eqP; rewrite ?addn0 ltn_eqF.
    move<-; case: splitP => l'' /=; rewrite ?ord1 ?addn0 !simp.
      by move<-; rewrite subSn ?leq_ord ?coefE.
    move->; rewrite eqxx mulr1n ?coefE subSn ?subrr //=.
    by rewrite !rmorphN ?subnn addr0.
  case: splitP => k'' /=; rewrite ?ord1 => -> // []; rewrite !simp.
  case: splitP => l' /=; rewrite /bump ltnNge leq_ord add0n !simp -?val_eqE /=;
    last by rewrite ord1 addn0 => /eqP; rewrite ltn_eqF.
  by case: splitP => l'' /= -> <- <-; rewrite !simp // ?ord1 ?addn0 ?ltn_eqF.
move=> {IHp Hsp p_neq0 p_monic}; rewrite add0n; set s := _ ^+ _;
apply: (@mulfI _ s); first by rewrite signr_eq0.
rewrite mulrA -expr2 sqrr_sign mulr1 mul1r /s.
pose fix D n : 'M[{poly K}]_n.+1 :=
     if n is n'.+1  then block_mx (-1 :'M_1)   ('X *: pid_mx 1)
                                  0            (D n')           else -1.
pose D' n : 'M[{poly K}]_n.+1 := \matrix_(i, j) ('X *+ (i.+1 == j) - (i == j)%:R).
set M := (_ - _); have -> : M = D' sp.
  apply/matrixP => k l; rewrite !simp.
  case: splitP => k' /=; rewrite ?ord1 !simp // /bump leq0n add1n; case.
  case: splitP => l' /=; rewrite /bump ltnNge leq_ord add0n; last first.
    by move/eqP; rewrite ord1 addn0 ltn_eqF.
  rewrite !simp -!val_eqE /= /bump leq0n ltnNge leq_ord [(true + _)%N]add1n ?add0n.
  by move=> -> ->; rewrite polyC_muln.
have -> n : D' n = D n.
  clear -simp; elim: n => [|n IHn] //=; apply/matrixP => i j; rewrite !simp.
    by rewrite !ord1 /= ?mulr0n sub0r.
  case: splitP => i' /=; rewrite -!val_eqE /= ?ord1 !simp => -> /=.
    case: splitP => j' /=; rewrite ?ord1 !simp => -> /=; first by rewrite sub0r.
    by rewrite eqSS andbT subr0 mulr_natr.
  by case: splitP => j' /=; rewrite ?ord1 -?IHn ?simp => -> //=; rewrite subr0.
elim: sp {eq_cast i M eq_i_sp s} => [|n IHn].
  by rewrite /= (_ : -1 = (-1)%:M) ?det_scalar // rmorphN.
rewrite /= (@det_ublock _ 1 n.+1) IHn.
by rewrite (_ : -1 = (-1)%:M) ?det_scalar // rmorphN.
Qed.

Definition companion (p : {poly K}) : 'M[K]_((size p).-1) :=
  projT1 (companion_subproof p).

Lemma companionK (p : {poly K}) : p \is monic -> char_poly (companion p) = p.
Proof. exact: projT2 (companion_subproof _). Qed.

End Companion.

Section Restriction.

Variable K : fieldType.
Variable m : nat.
Variables (V : 'M[K]_m).

Implicit Types f : 'M[K]_m.

Definition restrict f : 'M_(\rank V) := row_base V *m f *m (pinvmx (row_base V)).

Lemma stable_row_base f :
  (row_base V *m f <= row_base V)%MS = (V *m f <= V)%MS.
Proof.
rewrite eq_row_base.
by apply/idP/idP=> /(submx_trans _) ->; rewrite ?submxMr ?eq_row_base.
Qed.

Lemma eigenspace_restrict f : (V *m f <= V)%MS ->
  forall n a (W : 'M_(n, \rank V)),
  (W <= eigenspace (restrict f) a)%MS =
  (W *m row_base V <= eigenspace f a)%MS.
Proof.
move=> f_stabV n a W; apply/eigenspaceP/eigenspaceP; rewrite scalemxAl.
  by move<-; rewrite -mulmxA -[X in _ = X]mulmxA mulmxKpV ?stable_row_base.
move/(congr1 (mulmx^~ (pinvmx (row_base V)))).
rewrite -2!mulmxA [_ *m (f *m _)]mulmxA => ->.
by apply: (row_free_inj (row_base_free V)); rewrite mulmxKpV ?submxMl.
Qed.

Lemma eigenvalue_restrict  f : (V *m f <= V)%MS ->
  {subset eigenvalue (restrict f) <= eigenvalue f}.
Proof.
move=> f_stabV a /eigenvalueP [x /eigenspaceP]; rewrite eigenspace_restrict //.
move=> /eigenspaceP Hf x_neq0; apply/eigenvalueP.
by exists (x *m row_base V); rewrite ?mul_mx_rowfree_eq0 ?row_base_free.
Qed.

Lemma restrictM : {in [pred f | (V *m f <= V)%MS] &,
                      {morph restrict : f g / f *m g}}.
Proof.
move=> f g; rewrite !inE => Vf Vg /=.
by rewrite /restrict 2!mulmxA mulmxA mulmxKpV ?stable_row_base.
Qed.

End Restriction.

End extramx.
Notation skew K n := (@skew_def _ (Phant K) n).

Section Paper_HarmDerksen.

(* Following    http://www.math.lsa.umich.edu/~hderksen/preprints/linalg.pdf *)
(* quite literally except for Lemma5 where we don't use  hermitian matrices. *)
(* Instead we encode the morphism by hand in 'M[R]_(n * n), which turns  out *)
(* to  be very clumsy for  formalizing commutation and the end  of Lemma  4. *)
(* Moreover, the Qed takes time, so it would be far much better to formalize *)
(* Herm C n and use it instead !                                             *)

Implicit Types (K : fieldType).

Definition CommonEigenVec_def K (phK : phant K) (d r : nat) :=
  forall (m : nat) (V : 'M[K]_m), ~~ (d %| \rank V) ->
  forall (sf :  seq 'M_m), size sf = r ->
  {in sf, forall f, (V *m f <= V)%MS} ->
  {in sf &, forall f g, f *m g = g *m f} ->
  exists2 v : 'rV_m, (v != 0) & forall f, f \in sf ->
  exists a, (v <= eigenspace f a)%MS.
Notation CommonEigenVec K d r := (@CommonEigenVec_def _ (Phant K) d r).

Definition Eigen1Vec_def K (phK : phant K) (d : nat) :=
  forall (m : nat) (V : 'M[K]_m), ~~ (d %| \rank V) ->
  forall (f : 'M_m), (V *m f <= V)%MS -> exists a, eigenvalue f a.
Notation Eigen1Vec K d := (@Eigen1Vec_def _ (Phant K) d).

Lemma Eigen1VecP (K : fieldType) (d : nat) :
  CommonEigenVec K d 1%N <-> Eigen1Vec K d.
Proof.
split=> [Hd m V HV f|Hd m V HV [] // f [] // _ /(_ _ (mem_head _ _))] f_stabV.
  have [] := Hd _ _ HV [::f] (erefl _).
  + by move=> ?; rewrite in_cons orbF => /eqP ->.
  + by move=> ? ?; rewrite /= !in_cons !orbF => /eqP -> /eqP ->.
  move=> v v_neq0 /(_ f (mem_head _ _)) [a /eigenspaceP].
  by exists a; apply/eigenvalueP; exists v.
have [a /eigenvalueP [v /eigenspaceP v_eigen v_neq0]] := Hd _ _ HV _ f_stabV.
by exists v => // ?; rewrite in_cons orbF => /eqP ->; exists a.
Qed.

Lemma Lemma3 K d : Eigen1Vec K d -> forall r, CommonEigenVec K d r.+1.
Proof.
move=> E1V_K_d; elim=> [|r IHr m V]; first exact/Eigen1VecP.
move: (\rank V) {-2}V (leqnn (\rank V)) => n {V}.
elim: n m => [|n IHn] m V.
  by rewrite leqn0 => /eqP ->; rewrite dvdn0.
move=> le_rV_Sn HrV [] // f sf /= [] ssf f_sf_stabV f_sf_comm.
have [->|f_neq0] := altP (f =P 0).
  have [||v v_neq0 Hsf] := (IHr _ _ HrV _ ssf).
  + by move=> g f_sf /=; rewrite f_sf_stabV // in_cons f_sf orbT.
  + move=> g h g_sf h_sf /=.
    by apply: f_sf_comm; rewrite !in_cons ?g_sf ?h_sf ?orbT.
  exists v => // g; rewrite in_cons => /orP [/eqP->|]; last exact: Hsf.
  by exists 0; apply/eigenspaceP; rewrite mulmx0 scale0r.
have f_stabV : (V *m f <= V)%MS by rewrite f_sf_stabV ?mem_head.
have sf_stabV : {in sf, forall f, (V *m f <= V)%MS}.
  by move=> g g_sf /=; rewrite f_sf_stabV // in_cons g_sf orbT.
pose f' := restrict V f; pose sf' := map (restrict V) sf.
have [||a a_eigen_f'] := E1V_K_d _ 1%:M _ f'; do ?by rewrite ?mxrank1 ?submx1.
pose W := (eigenspace f' a)%MS; pose Z := (f' - a%:M).
have rWZ : (\rank W + \rank Z)%N = \rank V.
  by rewrite (mxrank_ker (f' - a%:M)) subnK // rank_leq_row.
have f'_stabW : (W *m f' <= W)%MS.
  by rewrite (eigenspaceP (submx_refl _)) scalemx_sub.
have f'_stabZ : (Z *m f' <= Z)%MS.
  rewrite (submx_trans _ (submxMl f' _)) //.
  by rewrite mulmxDl mulmxDr mulmxN mulNmx scalar_mxC.
have sf'_comm : {in [::f' & sf'] &, forall f g, f *m g = g *m f}.
  move=> g' h' /=; rewrite -!map_cons.
  move=> /mapP [g g_s_sf -> {g'}] /mapP [h h_s_sf -> {h'}].
  by rewrite -!restrictM ?inE /= ?f_sf_stabV // f_sf_comm.
have sf'_stabW : {in sf', forall f, (W *m f <= W)%MS}.
  move=> g g_sf /=; apply/eigenspaceP.
  rewrite -mulmxA -[g *m _]sf'_comm ?(mem_head, in_cons, g_sf, orbT) //.
  by rewrite mulmxA scalemxAl (eigenspaceP (submx_refl _)).
have sf'_stabZ : {in sf', forall f, (Z *m f <= Z)%MS}.
  move=> g g_sf /=.
  rewrite mulmxBl sf'_comm ?(mem_head, in_cons, g_sf, orbT) //.
  by rewrite -scalar_mxC -mulmxBr submxMl.
have [eqWV|neqWV] := altP (@eqmxP _ _ _ _ W 1%:M).
  have [] // := IHr _ W _ sf'; do ?by rewrite ?eqWV ?mxrank1 ?size_map.
    move=> g h g_sf' h_sf'; apply: sf'_comm;
    by rewrite in_cons (g_sf', h_sf') orbT.
  move=> v v_neq0 Hv; exists (v *m row_base V).
    by rewrite mul_mx_rowfree_eq0 ?row_base_free.
  move=> g; rewrite in_cons => /orP [/eqP ->|g_sf]; last first.
    have [|b] := Hv (restrict V g); first by rewrite map_f.
    by rewrite eigenspace_restrict // ?sf_stabV //; exists b.
  by exists a; rewrite -eigenspace_restrict // eqWV submx1.
have lt_WV : (\rank W < \rank V)%N.
  rewrite -[X in (_ < X)%N](@mxrank1 K) rank_ltmx //.
  by rewrite ltmxEneq neqWV // submx1.
have ltZV : (\rank Z < \rank V)%N.
  rewrite -[X in (_ < X)%N]rWZ -subn_gt0 addnK lt0n mxrank_eq0 -lt0mx.
  move: a_eigen_f' => /eigenvalueP [v /eigenspaceP] sub_vW v_neq0.
  by rewrite (ltmx_sub_trans _ sub_vW) // lt0mx.
have [] // := IHn _ (if d %| \rank Z then W else Z) _ _ [:: f' & sf'].
+ by rewrite -ltnS (@leq_trans (\rank V)) //; case: ifP.
+ by apply: contra HrV; case: ifP => [*|-> //]; rewrite -rWZ dvdn_add.
+ by rewrite /= size_map ssf.
+ move=> g; rewrite in_cons => /= /orP [/eqP -> {g}|g_sf']; case: ifP => _ //;
  by rewrite (sf'_stabW, sf'_stabZ).
move=> v v_neq0 Hv; exists (v *m row_base V).
  by rewrite mul_mx_rowfree_eq0 ?row_base_free.
move=> g Hg; have [|b] := Hv (restrict V g); first by rewrite -map_cons map_f.
rewrite eigenspace_restrict //; first by exists b.
by move: Hg; rewrite in_cons => /orP [/eqP -> //|/sf_stabV].
Qed.

Lemma Lemma4 r : CommonEigenVec R 2 r.+1.
Proof.
apply: Lemma3=> m V hV f f_stabV.
have [|a] := @odd_poly_root _ (char_poly (restrict V f)).
  by rewrite size_char_poly /= -dvdn2.
rewrite -eigenvalue_root_char => /eigenvalueP [v] /eigenspaceP v_eigen v_neq0.
exists a; apply/eigenvalueP; exists (v *m row_base V).
  by apply/eigenspaceP; rewrite -eigenspace_restrict.
by rewrite mul_mx_rowfree_eq0 ?row_base_free.
Qed.

Notation toC := (real_complex R).
Notation MtoC := (map_mx toC).

Lemma Lemma5 : Eigen1Vec R[i] 2.
Proof.
move=> m V HrV f f_stabV.
suff: exists a, eigenvalue (restrict V f) a.
  by move=> [a /eigenvalue_restrict Hf]; exists a; apply: Hf.
move: (\rank V) (restrict V f) => {f f_stabV V m} n f in HrV *.
pose u := map_mx (@Re R) f; pose v := map_mx (@Im R) f.
have fE : f = MtoC u + 'i%C *: MtoC v.
  rewrite /u /v [f]lock; apply/matrixP => i j; rewrite !mxE /=.
  by case: (locked f i j) => a b; simpc.
move: u v => u v in fE *.
pose L1fun : 'M[R]_n -> _ :=
  2%:R^-1 \*: (mulmxr u       \+ (mulmxr v \o trmx)
           \+ ((mulmx (u^T)) \- (mulmx (v^T) \o trmx))).
pose L1 := lin_mx [linear of L1fun].
pose L2fun : 'M[R]_n -> _ :=
  2%:R^-1 \*: (((@GRing.opp _) \o (mulmxr u \o trmx) \+ mulmxr v)
           \+ ((mulmx (u^T) \o trmx)               \+ (mulmx (v^T)))).
pose L2 := lin_mx [linear of L2fun].
have [] := @Lemma4 _ _ 1%:M _ [::L1; L2] (erefl _).
+ by move: HrV; rewrite mxrank1 !dvdn2 ?negbK odd_mul andbb.
+ by move=> ? _ /=; rewrite submx1.
+ suff {f fE}: L1 *m L2 = L2 *m L1.
    move: L1 L2 => L1 L2 commL1L2 La Lb.
    rewrite !{1}in_cons !{1}in_nil !{1}orbF.
    by move=> /orP [] /eqP -> /orP [] /eqP -> //; symmetry.
  apply/eqP/mulmxP => x; rewrite [X in X = _]mulmxA [X in _ = X]mulmxA.
  rewrite 4!mul_rV_lin !mxvecK /= /L1fun /L2fun /=; congr (mxvec (_ *: _)).
  move=> {L1 L2 L1fun L2fun}.
  case: n {x} (vec_mx x) => [//|n] x in HrV u v *.
  do ?[rewrite -(scalemxAl, scalemxAr, scalerN, scalerDr)
      |rewrite (mulmxN, mulNmx, trmxK, trmx_mul)
      |rewrite ?[(_ *: _)^T]linearZ ?[(_ + _)^T]linearD ?[(- _)^T]linearN /=].
  congr (_ *: _).
  rewrite !(mulmxDr, mulmxDl, mulNmx, mulmxN, mulmxA, opprD, opprK).
  do ![move: (_ *m _ *m _)] => t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12.
  rewrite [X in X + _ + _]addrC [X in X + _ = _]addrACA.
  rewrite [X in _ = (_ + _ + X) + _]addrC [X in _ = X + _]addrACA.
  rewrite [X in _ + (_ + _ + X)]addrC [X in _ + X = _]addrACA.
  rewrite [X in _ = _ + (X + _)]addrC [X in _ = _ + X]addrACA.
  rewrite [X in X = _]addrACA [X in _ = X]addrACA; congr (_ + _).
  by rewrite addrC [X in X + _ = _]addrACA [X in _ + X = _]addrACA.
move=> g g_neq0 Hg; have [] := (Hg L1, Hg L2).
rewrite !(mem_head, in_cons, orbT) => [].
move=> [//|a /eigenspaceP g_eigenL1] [//|b /eigenspaceP g_eigenL2].
rewrite !mul_rV_lin /= /L1fun /L2fun /= in g_eigenL1 g_eigenL2.
do [move=> /(congr1 vec_mx); rewrite mxvecK linearZ /=] in g_eigenL1.
do [move=> /(congr1 vec_mx); rewrite mxvecK linearZ /=] in g_eigenL2.
move=> {L1 L2 L1fun L2fun Hg HrV}.
set vg := vec_mx g in g_eigenL1 g_eigenL2.
exists (a +i* b); apply/eigenvalueP.
pose w := (MtoC vg - 'i%C *: MtoC vg^T).
exists (nz_row w); last first.
  rewrite nz_row_eq0 subr_eq0; apply: contraNneq g_neq0 => Hvg.
  rewrite -vec_mx_eq0; apply/eqP/matrixP => i j; rewrite !mxE /=.
  move: Hvg => /matrixP /(_ i j); rewrite !mxE /=; case.
  by rewrite !(mul0r, mulr0, add0r, mul1r, oppr0) => ->.
apply/eigenspaceP.
case: n f => [|n] f in u v g g_neq0 vg w fE g_eigenL1 g_eigenL2 *.
  by rewrite thinmx0 eqxx in g_neq0.
rewrite (submx_trans (nz_row_sub _)) //; apply/eigenspaceP.
rewrite fE [a +i* b]complexE /=.
rewrite !(mulmxDr, mulmxBl, =^~scalemxAr, =^~scalemxAl) -!map_mxM.
rewrite !(scalerDl, scalerDr, scalerN, =^~scalemxAr, =^~scalemxAl).
rewrite !scalerA /= mulrAC ['i%C * _]sqr_i ?mulN1r scaleN1r scaleNr !opprK.
rewrite [_ * 'i%C]mulrC -!scalerA -!map_mxZ /=.
do 2!rewrite [X in (_ - _) + X]addrC [_ - 'i%C *: _ + _]addrACA.
rewrite ![- _ + _]addrC -!scalerBr -!(rmorphB, rmorphD) /=.
congr (_ + 'i%C *: _); congr map_mx; rewrite -[_ *: _^T]linearZ /=;
rewrite -g_eigenL1 -g_eigenL2 linearZ -(scalerDr, scalerBr);
do ?rewrite ?trmxK ?trmx_mul ?[(_ + _)^T]linearD ?[(- _)^T]linearN /=;
rewrite -[in X in _ *: (_ + X)]addrC 1?opprD 1?opprB ?mulmxN ?mulNmx;
rewrite [X in _ *: X]addrACA.
  rewrite -mulr2n [X in _ *: (_ + X)]addrACA subrr addNr !addr0.
  by rewrite -scaler_nat scalerA mulVf ?pnatr_eq0 // scale1r.
rewrite subrr addr0 addrA addrAC -addrA -mulr2n addrC.
by rewrite -scaler_nat scalerA mulVf ?pnatr_eq0 // scale1r.
Qed.

Lemma Lemma6 k r : CommonEigenVec R[i] (2^k.+1) r.+1.
Proof.
elim: k {-2}k (leqnn k) r => [|k IHk] l.
  by rewrite leqn0 => /eqP ->; apply: Lemma3; apply: Lemma5.
rewrite leq_eqVlt ltnS => /orP [/eqP ->|/IHk //] r {l}.
apply: Lemma3 => m V Hn f f_stabV {r}.
have [dvd2n|Ndvd2n] := boolP (2 %| \rank V); last first.
  exact: @Lemma5 _ _ Ndvd2n _ f_stabV.
suff: exists a, eigenvalue (restrict V f) a.
  by move=> [a /eigenvalue_restrict Hf]; exists a; apply: Hf.
case: (\rank V) (restrict V f) => {f f_stabV V m} [|n] f in Hn dvd2n *.
  by rewrite dvdn0 in Hn.
pose L1 := lin_mx [linear of mulmxr f \+ (mulmx f^T)].
pose L2 := lin_mx [linear of mulmxr f \o mulmx f^T].
have [] /= := IHk _ (leqnn _) _  _ (skew R[i] n.+1) _ [::L1; L2] (erefl _).
+ rewrite rank_skew; apply: contra Hn.
  rewrite -(@dvdn_pmul2r 2) //= -expnSr muln2 -[_.*2]add0n.
  have n_odd : odd n by rewrite dvdn2 /= ?negbK in dvd2n *.
  have {2}<- : odd (n.+1 * n) = 0%N :> nat by rewrite odd_mul /= andNb.
  by rewrite odd_double_half Gauss_dvdl // coprime_pexpl // coprime2n.
+ move=> L; rewrite 2!in_cons in_nil orbF => /orP [] /eqP ->;
  apply/rV_subP => v /submxP [s -> {v}]; rewrite mulmxA; apply/skewP;
  set u := _ *m skew _ _;
  do [have /skewP : (u <= skew R[i] n.+1)%MS by rewrite submxMl];
  rewrite mul_rV_lin /= !mxvecK => skew_u.
    by rewrite opprD linearD /= !trmx_mul skew_u mulmxN mulNmx addrC trmxK.
  by rewrite !trmx_mul trmxK skew_u mulNmx mulmxN mulmxA.
+ suff commL1L2: L1 *m L2 = L2 *m L1.
    move=> La Lb; rewrite !in_cons !in_nil !orbF.
    by move=> /orP [] /eqP -> /orP [] /eqP -> //; symmetry.
  apply/eqP/mulmxP => u; rewrite !mulmxA !mul_rV_lin ?mxvecK /=.
  by rewrite !(mulmxDr, mulmxDl, mulmxA).
move=> v v_neq0 HL1L2; have [] := (HL1L2 L1, HL1L2 L2).
rewrite !(mem_head, in_cons) orbT => [] [] // a vL1 [] // b vL2 {HL1L2}.
move/eigenspaceP in vL1; move/eigenspaceP in vL2.
move: vL2 => /(congr1 vec_mx); rewrite linearZ mul_rV_lin /= mxvecK.
move: vL1 => /(congr1 vec_mx); rewrite linearZ mul_rV_lin /= mxvecK.
move=> /(canRL (addKr _)) ->; rewrite mulmxDl mulNmx => Hv.
pose p := 'X^2 + (- a) *: 'X + b%:P.
have : vec_mx v *m (horner_mx f p) = 0.
  rewrite !(rmorphN, rmorphB, rmorphD, rmorphM) /= linearZ /=.
  rewrite horner_mx_X horner_mx_C !mulmxDr mul_mx_scalar -Hv.
  rewrite addrAC addrA mulmxA addrN add0r.
  by rewrite -scalemxAl -scalemxAr scaleNr addrN.
rewrite [p]monic_canonical_form; move: (_ / 2%:R) (_ / 2%:R).
move=> r2 r1 {Hv p a b L1 L2 Hn}.
rewrite rmorphM !rmorphB /= horner_mx_X !horner_mx_C mulmxA => Hv.
have: exists2 w : 'M_n.+1, w != 0 & exists a, (w <= eigenspace f a)%MS.
  move: Hv; set w := vec_mx _ *m _.
  have [w_eq0 _|w_neq0 r2_eigen] := altP (w =P 0).
    exists (vec_mx v); rewrite ?vec_mx_eq0 //; exists r1.
    apply/eigenspaceP/eqP.
    by rewrite -mul_mx_scalar -subr_eq0 -mulmxBr -/w w_eq0.
  exists w => //; exists r2; apply/eigenspaceP/eqP.
  by rewrite -mul_mx_scalar -subr_eq0 -mulmxBr r2_eigen.
move=> [w w_neq0 [a /(submx_trans (nz_row_sub _)) /eigenspaceP Hw]].
by exists a; apply/eigenvalueP; exists (nz_row w); rewrite ?nz_row_eq0.
Qed.

(* We enunciate a corollary of Theorem 7 *)
Corollary Theorem7' (m : nat) (f : 'M[R[i]]_m) : (0 < m)%N -> exists a, eigenvalue f a.
Proof.
case: m f => // m f _; have /Eigen1VecP := @Lemma6 m 0.
move=> /(_ m.+1 1 _ f) []; last by move=> a; exists a.
+ by rewrite mxrank1 (contra (dvdn_leq _)) // -ltnNge ltn_expl.
+ by rewrite submx1.
Qed.

Lemma complex_acf_axiom : GRing.ClosedField.axiom [ringType of R[i]].
Proof.
move=> n c n_gt0; pose p := 'X^n - \poly_(i < n) c i.
suff [x rpx] : exists x, root p x.
  exists x; move: rpx; rewrite /root /p hornerD hornerN hornerXn subr_eq0.
  by move=> /eqP ->; rewrite horner_poly.
have p_monic : p \is monic.
  rewrite qualifE lead_coefDl ?lead_coefXn //.
  by rewrite size_opp size_polyXn ltnS size_poly.
have sp_gt1 : (size p > 1)%N.
  by rewrite size_addl size_polyXn // size_opp ltnS size_poly.
case: n n_gt0 p => //= n _ p in p_monic sp_gt1 *.
have [] := Theorem7' (companion p); first by rewrite -(subnK sp_gt1) addn2.
by move=> x; rewrite eigenvalue_root_char companionK //; exists x.
Qed.

Definition complex_decFieldMixin := closed_fields_QEMixin complex_acf_axiom.
Canonical complex_decField := DecFieldType R[i] complex_decFieldMixin.
Canonical complex_closedField := ClosedFieldType R[i] complex_acf_axiom.

Definition complex_numClosedFieldMixin :=
  ImaginaryMixin (sqr_i R) (fun x=> esym (sqr_normc x)).

Canonical complex_numClosedFieldType :=
  NumClosedFieldType R[i] complex_numClosedFieldMixin.

End Paper_HarmDerksen.

End ComplexClosed.

(* End ComplexInternal. *)

(* Canonical ComplexInternal.complex_eqType. *)
(* Canonical ComplexInternal.complex_choiceType. *)
(* Canonical ComplexInternal.complex_countType. *)
(* Canonical ComplexInternal.complex_ZmodType. *)
(* Canonical ComplexInternal.complex_Ring. *)
(* Canonical ComplexInternal.complex_comRing. *)
(* Canonical ComplexInternal.complex_unitRing. *)
(* Canonical ComplexInternal.complex_comUnitRing. *)
(* Canonical ComplexInternal.complex_iDomain. *)
(* Canonical ComplexInternal.complex_fieldType. *)
(* Canonical ComplexInternal.ComplexField.real_complex_rmorphism. *)
(* Canonical ComplexInternal.ComplexField.real_complex_additive. *)
(* Canonical ComplexInternal.ComplexField.Re_additive. *)
(* Canonical ComplexInternal.ComplexField.Im_additive. *)
(* Canonical ComplexInternal.complex_numDomainType. *)
(* Canonical ComplexInternal.complex_numFieldType. *)
(* Canonical ComplexInternal.conjc_rmorphism. *)
(* Canonical ComplexInternal.conjc_additive. *)
(* Canonical ComplexInternal.complex_decField. *)
(* Canonical ComplexInternal.complex_closedField. *)
(* Canonical ComplexInternal.complex_numClosedFieldType. *)

(* Definition complex_algebraic_trans := ComplexInternal.complex_algebraic_trans. *)

Section ComplexClosedTheory.

Variable R : rcfType.

Lemma complexiE : 'i%C = 'i%R :> R[i].
Proof. by []. Qed.

Lemma complexRe (x : R[i]) : (Re x)%:C = 'Re x.
Proof.
rewrite {1}[x]Crect raddfD /= mulrC ReiNIm rmorphB /=.
by rewrite ?RRe_real ?RIm_real ?Creal_Im ?Creal_Re // subr0.
Qed.

Lemma complexIm (x : R[i]) : (Im x)%:C = 'Im x.
Proof.
rewrite {1}[x]Crect raddfD /= mulrC ImiRe rmorphD /=.
by rewrite ?RRe_real ?RIm_real ?Creal_Im ?Creal_Re // add0r.
Qed.

End ComplexClosedTheory.

Definition complexalg := realalg[i].

Canonical complexalg_eqType := [eqType of complexalg].
Canonical complexalg_choiceType := [choiceType of complexalg].
Canonical complexalg_countype := [choiceType of complexalg].
Canonical complexalg_zmodType := [zmodType of complexalg].
Canonical complexalg_ringType := [ringType of complexalg].
Canonical complexalg_comRingType := [comRingType of complexalg].
Canonical complexalg_unitRingType := [unitRingType of complexalg].
Canonical complexalg_comUnitRingType := [comUnitRingType of complexalg].
Canonical complexalg_idomainType := [idomainType of complexalg].
Canonical complexalg_fieldType := [fieldType of complexalg].
Canonical complexalg_decDieldType := [decFieldType of complexalg].
Canonical complexalg_closedFieldType := [closedFieldType of complexalg].
Canonical complexalg_numDomainType := [numDomainType of complexalg].
Canonical complexalg_numFieldType := [numFieldType of complexalg].
Canonical complexalg_numClosedFieldType := [numClosedFieldType of complexalg].

Lemma complexalg_algebraic : integralRange (@ratr [unitRingType of complexalg]).
Proof.
move=> x; suff [p p_monic] : integralOver (real_complex _ \o realalg_of _) x.
  by rewrite (eq_map_poly (fmorph_eq_rat _)); exists p.
by apply: complex_algebraic_trans; apply: realalg_algebraic.
Qed.

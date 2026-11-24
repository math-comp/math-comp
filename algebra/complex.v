(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import boot nmodule order orderedzmod algebraic_hierarchy.
From mathcomp Require Import poly matrix mxalgebra mxpoly numeric_hierarchy rat.
From mathcomp Require Import vector zmodp ssrint archimedean.
From mathcomp Require Import closed_field polyrcf realalg.

(******************************************************************************)
(* This file defines complex numbers R[i] over a field R, equips them with    *)
(* a numeric field structure when R is a real field. When R is a real closed  *)
(* field, it also proves R[i] is algebraically closed (fundamental theorem    *)
(* of algebra), following a proof by Derksen.                                 *)
(*                   R[i] == the complex numbers over field R, equipped with  *)
(*                           an R[i]-module structure                         *)
(*                   x%:C == embedding of R into R[i]                         *)
(*             Re z, Im z == real and imaginary parts of (z : R[i])           *)
(*                     'i == the imaginary unit, squaring to -1               *)
(* x +i* y, x -i* y, x *i == constructors of R[i]                             *)
(*                    z^* == complex conjugate of z                           *)
(*                  simpc == tactic to simplify arithmetic in R[i]            *)
(*             Rcomplex R == alias of R[i] with an R-module structure         *)
(*                           and an R-valued norm                             *)
(* Thanks to Pierre Lairez for finding Derksen's paper.                       *)
(******************************************************************************)

Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
#[local] Obligation Tactic := idtac.

Local Open Scope ring_scope.

Reserved Notation "x +i* y"
  (at level 40, left associativity, format "x  +i*  y").
Reserved Notation "x -i* y"
  (at level 40, left associativity, format "x  -i*  y").
Reserved Notation "R [i]"
  (at level 1, left associativity, format "R [i]").

Local Notation sgr := Num.sg.
Local Notation sqrtr := Num.sqrt.

Record complex (R : Type) : Type := Complex { Re : R; Im : R }.
Definition Rcomplex := complex.

Declare Scope complex_scope.
Delimit Scope complex_scope with C.
Local Open Scope complex_scope.

Definition real_complex_def (F : ringType) (phF : phant F) (x : F) :=
  Complex x 0.
Notation real_complex F := (@real_complex_def _ (Phant F)).
Notation "x %:C" := (real_complex _ x) (format "x %:C")  : complex_scope.
Notation "x +i* y" := (Complex x y) : complex_scope.
Notation "x -i* y" := (Complex x (- y)) : complex_scope.
Notation "x *i " := (Complex 0 x) (at level 1, format "x *i") : complex_scope.
Notation "''i'" := (Complex 0 1) : complex_scope.
Notation "R [i]" := (complex R) (format "R [i]").

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

HB.instance Definition _ (R : eqType) := Equality.copy R[i]
  (pcan_type (@ComplexEqChoice.complex_of_sqRK R)).
HB.instance Definition _ (R : choiceType) := Choice.copy R[i]
  (pcan_type (@ComplexEqChoice.complex_of_sqRK R)).
HB.instance Definition _ (R : countType) := Countable.copy R[i]
  (pcan_type (@ComplexEqChoice.complex_of_sqRK R)).
HB.instance Definition _ (R : eqType) := Equality.on (Rcomplex R).
HB.instance Definition _ (R : choiceType) := Choice.on (Rcomplex R).
HB.instance Definition _ (R : countType) := Countable.on (Rcomplex R).

Lemma eq_complex : forall (R : eqType) (x y : complex R),
  (x == y) = (Re x == Re y) && (Im x == Im y).
Proof.
move=> R [a b] [c d] /=.
apply/eqP/andP; first by move=> [-> ->]; split.
by case; move/eqP->; move/eqP->.
Qed.

Lemma complexr0 (R : ringType) (x : R) : x +i* 0 = x%:C. Proof. by []. Qed.

Module ComplexField.
Section ComplexField_ringType.

Variable R : ringType.
Local Notation C := R[i].
Local Notation C0 := ((0 : R)%:C).

Definition addc (x y : R[i]) := let: a +i* b := x in let: c +i* d := y in
  (a + c) +i* (b + d).
Definition oppc (x : R[i]) := let: a +i* b := x in (- a) +i* (- b).

Program Definition complex_zmodMixin := @GRing.isZmodule.Build R[i]
  C0 oppc addc _ _ _ _.
Next Obligation. by move=> [a b] [c d] [e f] /=; rewrite !addrA. Qed.
Next Obligation. by move=> [a b] [c d] /=; congr (_ +i* _); rewrite addrC. Qed.
Next Obligation. by move=> [a b] /=; rewrite !add0r. Qed.
Next Obligation. by move=> [a b] /=; rewrite !addNr. Qed.
HB.instance Definition _ := complex_zmodMixin.
HB.instance Definition _ := GRing.Zmodule.on (Rcomplex R).

Definition scalec (a : R) (x : R[i]) :=
  let: b +i* c := x in (a * b) +i* (a * c).

Program Definition complex_lmodMixin :=
  @GRing.Zmodule_isLmodule.Build R (Rcomplex R) scalec _ _ _ _.
Next Obligation. by move=> a b [c d] /=; rewrite !mulrA. Qed.
Next Obligation. by move=> [a b] /=; rewrite !mul1r. Qed.
Next Obligation. by move=> a [b c] [d e] /=; rewrite !mulrDr. Qed.
Next Obligation. by move=> [a b] c d /=; rewrite !mulrDl. Qed.
HB.instance Definition _ := complex_lmodMixin.

End ComplexField_ringType.

Section ComplexField_comRingType.
Variable R : comRingType.
Local Notation C := R[i].

Definition mulc (x y : C) := let: a +i* b := x in let: c +i* d := y in
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

End ComplexField_comRingType.

Section ComplexField_fieldType.
Variable R : fieldType.
Local Notation C := R[i].
Local Notation C0 := ((0 : R)%:C).
Local Notation C1 := ((1 : R)%:C).

Definition invc (x : R[i]) := let: a +i* b := x in let n2 := (a ^+ 2 + b ^+ 2) in
  (a / n2) -i* (b / n2).

Lemma mul1c : left_id C1 (@mulc R).
Proof. by move=> [a b] /=; rewrite !mul1r !mul0r subr0 addr0. Qed.

Lemma mulc_addl : left_distributive (@mulc R) (@addc R).
Proof.
move=> [a b] [c d] [e f] /=; rewrite !mulrDl !opprD -!addrA.
by congr ((_ + _) +i* (_ + _)); rewrite addrCA.
Qed.

Lemma nonzero1c : C1 != C0. Proof. by rewrite eq_complex /= oner_eq0. Qed.

HB.instance Definition _ := GRing.Zmodule_isComNzRing.Build R[i]
  (@mulcA R) (@mulcC R) mul1c mulc_addl nonzero1c.
HB.instance Definition _ := GRing.ComNzRing.on (Rcomplex R).
HB.instance Definition _ := GRing.Lalgebra.copy C C^o.

Program Definition complex_lalgMixin :=
  @GRing.LSemiModule_isLSemiAlgebra.Build R (Rcomplex R) _.
Next Obligation.
by move=> a [ru iu] [rv iv]; apply/eqP; do 2?[apply/andP; split];
  rewrite // mulrDr ?mulrN !mulrA.
Qed.
HB.instance Definition _ := complex_lalgMixin.

Let complex_vector : Vector.axiom 2 (Rcomplex R).
Proof.
exists (fun '(a +i* b) => \row_(j < 2) if (j == 0) then a else b).
- move=> a [b c] [d e] /=.
  apply/matrixP => i [j hj]; rewrite !ord1 !mxE.
  by case: ifP.
- exists (fun m : 'rV_2 => m 0 0 +i* m 0 1).
    by move=> [a b]; rewrite !mxE.
  move=> m; apply/matrixP => i j; rewrite mxE !ord1.
  case: ifP => [/eqP -> //|].
  case: j => [[//|[hj _|//]]].
  by congr (m _ _); apply: ord_inj.
Qed.

HB.instance Definition _ :=
  Lmodule_hasFinDim.Build R (Rcomplex R) complex_vector.
HB.instance Definition _ := 
  SemiVector_isProper.Build R (Rcomplex R) erefl.
HB.instance Definition _ := NzVector.copy C C^o.

Lemma complex_Rbasis : basis_of (@fullv _ (Rcomplex R)) [:: 1 ; 'i].
Proof.
rewrite basisEfree subvf /= dimvf andbT.
rewrite free_cons span_seq1 seq1_free eq_complex eq_refl oner_neq0 andbT.
by apply/vlineP => -[k /eqP]; rewrite eq_complex /= mulr0 oner_eq0.
Qed.

End ComplexField_fieldType.

Local Ltac simpc := do ?
  [ rewrite -[(_ +i* _) - (_ +i* _)]/(_ +i* _)
  | rewrite -[(_ +i* _) + (_ +i* _)]/(_ +i* _)
  | rewrite -[(_ +i* _) * (_ +i* _)]/(_ +i* _)].

Section ComplexField_realFieldType.

Variable R : realFieldType.
Local Notation C := R[i].
Local Notation C0 := ((0 : R)%:C).
Local Notation C1 := ((1 : R)%:C).

Lemma mulVc : forall x, x != C0 -> mulc (invc x) x = C1.
Proof.
move=> [a b]; rewrite eq_complex => /= hab; rewrite !mulNr opprK.
rewrite ![_ / _ * _]mulrAC [b * a]mulrC subrr complexr0 -mulrDl mulfV //.
by rewrite paddr_eq0 -!expr2 ?expf_eq0 ?sqr_ge0.
Qed.

Lemma invc0 : invc C0 = C0. Proof. by rewrite /= !mul0r oppr0. Qed.

HB.instance Definition _ := GRing.ComNzRing_isField.Build C mulVc invc0.
HB.instance Definition _ := GRing.Field.on (Rcomplex R).

Lemma real_complex_zmod_morphism : zmod_morphism (real_complex R).
Proof. by move=> a b /=; simpc; rewrite subrr. Qed.

Lemma real_complex_monoid_morphism : monoid_morphism (real_complex R).
Proof. by split=> // a b /=; simpc; rewrite !mulr0 !mul0r addr0 subr0. Qed.

HB.instance Definition _ := Algebra.isZmodMorphism.Build R R[i]
  (real_complex R) real_complex_zmod_morphism.

HB.instance Definition _ := GRing.isMonoidMorphism.Build R R[i]
  (real_complex R) real_complex_monoid_morphism.

Lemma complex_basis : basis_of (@fullv _ C) [:: 1].
Proof. by rewrite basisEfree subvf dimvf /= andbT seq1_free oner_neq0. Qed.

End ComplexField_realFieldType.

Module Normc.
Section Normc.
(*  TODO: when Pythagorean Fields are added, weaken to Pythagorean Field *)
Variable R : rcfType.
Implicit Types x : R[i].

Definition normc x :=
  let: a +i* b := x in sqrtr (a ^+ 2 + b ^+ 2).

Lemma normc0 : normc 0%C = 0 :> R.
Proof. by rewrite /normc /= expr0n/= addr0 sqrtr0. Qed.

Lemma normc1 : normc 1%C = 1 :> R.
Proof. by rewrite /normc /= expr0n/= expr1n addr0 sqrtr1. Qed.

Lemma eq0_normc x : normc x = 0 -> x = 0.
Proof.
case: x => a b /= /eqP; rewrite sqrtr_eq0 le_eqVlt => /orP[|]; last first.
  by rewrite ltNge addr_ge0 ?sqr_ge0.
by rewrite paddr_eq0 ?sqr_ge0 ?expf_eq0 //= => /andP[/eqP -> /eqP ->].
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

Lemma normcV x : normc x^-1 = (normc x)^-1.
Proof.
have [->|x0] := eqVneq x 0; first by rewrite ?(invr0,normc0).
have nx0 : normc x != 0 by apply: contra x0 => /eqP/eq0_normc ->.
by apply: (mulfI nx0); rewrite -normcM !divrr ?unitfE// normc1.
Qed.

End Normc.
End Normc.

Section ComplexField.
Variable R : rcfType.
Implicit Types x y : R[i].

Local Notation C := R[i].
Local Notation C0 := ((0 : R)%:C).
Local Notation C1 := ((1 : R)%:C).

Lemma Re_is_scalar : scalar (@Re R : Rcomplex R -> R).
Proof. by move=> a [b c] [d e]. Qed.

HB.instance Definition _ :=
  GRing.isLinear.Build R (Rcomplex R) R _ (@Re R : Rcomplex R -> R)
    Re_is_scalar.

Lemma Im_is_scalar : scalar (@Im R : Rcomplex R -> R).
Proof. by move=> a [b c] [d e]. Qed.

HB.instance Definition _ :=
  GRing.isLinear.Build R (Rcomplex R) R _ (@Im R : Rcomplex R -> R)
    Im_is_scalar.

Definition lec x y :=
  let: a +i* b := x in let: c +i* d := y in
    (d == b) && (a <= c).

Definition ltc x y :=
  let: a +i* b := x in let: c +i* d := y in
    (d == b) && (a < c).

Lemma ltc0_add x y : ltc 0 x -> ltc 0 y -> ltc 0 (x + y).
Proof.
move: x y => [a b] [c d] /= /andP [/eqP-> ha] /andP [/eqP-> hc].
by rewrite addr0 eqxx addr_gt0.
Qed.

Lemma ge0_lec_total x y : lec 0 x -> lec 0 y -> lec x y || lec y x.
Proof.
move: x y => [a b] [c d] /= /andP[/eqP -> a_ge0] /andP[/eqP -> c_ge0].
by rewrite eqxx le_total.
Qed.

Lemma subc_ge0 x y : lec 0 (y - x) = lec x y.
Proof. by move: x y => [a b] [c d] /=; simpc; rewrite subr_ge0 subr_eq0. Qed.

Lemma ltc_def x y : ltc x y = (y != x) && lec x y.
Proof.
move: x y => [a b] [c d] /=; simpc; rewrite eq_complex /=.
by have [] := altP eqP; rewrite ?(andbF, andbT) //= lt_def.
Qed.

Import Normc.

Notation normC x := (normc x)%:C.

Lemma eq0_normC x : normC x = 0 -> x = 0. Proof. by case=> /eq0_normc. Qed.

Lemma normCM x y : normC (x * y) = normC x * normC y.
Proof. by rewrite -rmorphM normcM. Qed.

Lemma lec_def x y : lec x y = (normC (y - x) == y - x).
Proof.
rewrite -subc_ge0; move: (_ - _) => [a b]; rewrite eq_complex /= eq_sym.
have [<- /=|_] := altP eqP; last by rewrite andbF.
by rewrite [0 ^+ _]mul0r addr0 andbT sqrtr_sqr ger0_def.
Qed.

Lemma lec_normD x y : lec (normC (x + y)) (normC x + normC y).
Proof.
move: x y => [a b] [c d] /=; simpc; rewrite addr0 eqxx /=.
rewrite -(@ler_pXn2r _ 2) -?topredE /= ?(ler_wpDr, sqrtr_ge0) //.
rewrite [X in _ <= X] sqrrD ?sqr_sqrtr;
   do ?by rewrite ?(ler_wpDr, sqrtr_ge0, sqr_ge0, mulr_ge0) //.
rewrite -addrA addrCA (monoRL (addrNK _) (lerD2r _)) !sqrrD.
set u := _ *+ 2; set v := _ *+ 2.
rewrite [a ^+ _ + _ + _]addrAC [b ^+ _ + _ + _]addrAC -[X in X - _]addrA.
rewrite [u + _]addrC [X in _ - X]addrAC [b ^+ _ + _]addrC.
rewrite [u]lock [v]lock !addrA; set x := (a ^+ 2 + _ + _ + _).
rewrite -[_ + locked u]addrA [leLHS]addrC addKr -!lock addrC.
have [huv|] := ger0P (u + v); last first.
  by move=> /ltW /le_trans -> //; rewrite pmulrn_lge0 // mulr_ge0 ?sqrtr_ge0.
rewrite -(@ler_pXn2r _ 2) -?topredE //=.
  by rewrite ?(pmulrn_lge0, mulr_ge0, sqrtr_ge0) //.
rewrite -mulr_natl !exprMn !sqr_sqrtr ?(ler_wpDr, sqr_ge0) //.
rewrite -mulrnDl -[in leLHS]mulr_natl !exprMn ler_pM2l ?exprn_gt0 ?ltr0n //.
rewrite sqrrD mulrDl !mulrDr -!exprMn addrAC -!addrA lerD2l !addrA.
rewrite [_ + (b * d) ^+ 2]addrC -addrA lerD2l.
have: 0 <= (a * d - b * c) ^+ 2 by rewrite sqr_ge0.
by rewrite sqrrB addrAC subr_ge0 [_ * c]mulrC mulrACA [d * _]mulrC.
Qed.

HB.instance Definition _ := Num.IntegralDomain_isNumRing.Build C
  lec_normD ltc0_add eq0_normC ge0_lec_total normCM lec_def ltc_def.

End ComplexField.
End ComplexField.
HB.export ComplexField.

Definition conjc {R : ringType} (x : R[i]) := let: a +i* b := x in a -i* b.
Notation "x ^*" := (conjc x) : complex_scope.
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
Implicit Types (k : R) (x y z : R[i]).

Lemma ReiNIm : forall x, Re (x * 'i%C) = - Im x.
Proof. by case=> a b; simpc. Qed.

Lemma ImiRe : forall x, Im (x * 'i%C) = Re x.
Proof. by case=> a b; simpc. Qed.

Lemma complexE x : x = (Re x)%:C + 'i%C * (Im x)%:C :> R[i].
Proof. by case: x => *; simpc. Qed.

Local Lemma real_complexE_deprecated k : k%:C = k +i* 0 :> R[i]. Proof. done. Qed.
#[deprecated(since="1.1.3", note="Use complexr0 instead.")]
Notation real_complexE := real_complexE_deprecated.

Lemma sqr_i : 'i%C ^+ 2 = -1 :> R[i].
Proof. by rewrite exprS; simpc; rewrite complexr0 rmorphN. Qed.

Lemma complexI : injective (real_complex R). Proof. by move=> x y []. Qed.

Lemma ler0c k : (0 <= k%:C) = (0 <= k). Proof. by simpc. Qed.

Lemma lecE : forall x y, (x <= y) = (Im y == Im x) && (Re x <= Re y).
Proof. by move=> [a b] [c d]. Qed.

Lemma ltcE : forall x y, (x < y) = (Im y == Im x) && (Re x < Re y).
Proof. by move=> [a b] [c d]. Qed.

Lemma lecR : forall k k', (k%:C <= k'%:C) = (k <= k').
Proof. by move=> k k'; simpc. Qed.

Lemma ltcR : forall k k', (k%:C < k'%:C) = (k < k').
Proof. by move=> k k'; simpc. Qed.

Lemma conjc_zmod_morphism : zmod_morphism (@conjc R).
Proof. by move=> [a b] [c d] /=; simpc; rewrite [d - _]addrC. Qed.

Lemma conjc_monoid_morphism : monoid_morphism (@conjc R).
Proof. by split=> [|[a b] [c d]] /=; simpc. Qed.

HB.instance Definition _ := GRing.isZmodMorphism.Build R[i] R[i] conjc
    conjc_zmod_morphism.

HB.instance Definition _ := GRing.isMonoidMorphism.Build R[i] R[i] conjc
    conjc_monoid_morphism.

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

Lemma conj_ge0 : forall x, (0 <= x ^*) = (0 <= x).
Proof. by move=> [a b] /=; simpc; rewrite oppr_eq0. Qed.

Lemma conjc_nat : forall n, (n%:R : R[i])^* = n%:R.
Proof. exact: rmorph_nat. Qed.

Lemma conjc0 : (0 : R[i]) ^* = 0.
Proof. exact: (conjc_nat 0). Qed.

Lemma conjc1 : (1 : R[i]) ^* = 1.
Proof. exact: (conjc_nat 1). Qed.

Lemma conjc_eq0 : forall x, (x ^* == 0) = (x == 0).
Proof. by move=> [a b]; rewrite !eq_complex /= eqr_oppLR oppr0. Qed.

Lemma conjc_inv: forall x, (x^-1)^* = (x^*%C )^-1.
Proof. exact: fmorphV. Qed.

Lemma complex_root_conj (p : {poly R[i]}) (x : R[i]) :
  root (map_poly conjc p) x = root p x^*.
Proof. by rewrite /root -{1}[x]conjcK horner_map /= conjc_eq0. Qed.

Lemma complex_algebraic_trans (T : comNzRingType) (toR : {rmorphism T -> R}) :
  integralRange toR -> integralRange (real_complex R \o toR).
Proof.
set f := _ \o _ => R_integral [a b].
have integral_real k : integralOver f (k%:C) by apply: integral_rmorph.
rewrite [_ +i* _]complexE.
apply: integral_add => //; apply: integral_mul => //=.
exists ('X^2 + 1).
  by rewrite monicE lead_coefDl ?size_polyXn ?size_poly1 ?lead_coefXn.
by rewrite rmorphD rmorph1 /= ?map_polyXn rootE !hornerE sqr_i addNr.
Qed.

Lemma normc_def (z : R[i]) : `|z| = (sqrtr ((Re z)^+2 + (Im z)^+2))%:C.
Proof. by case: z. Qed.

Lemma add_Re2_Im2 (z : R[i]) : ((Re z)^+2 + (Im z)^+2)%:C = `|z|^+2.
Proof. by rewrite normc_def -rmorphXn sqr_sqrtr ?addr_ge0 ?sqr_ge0. Qed.

Lemma addcJ (z : R[i]) : z + z^*%C = 2%:R * (Re z)%:C.
Proof. by rewrite ReJ_add mulrC mulfVK ?pnatr_eq0. Qed.

Lemma subcJ (z : R[i]) : z - z^*%C = 2%:R * (Im z)%:C * 'i%C.
Proof.
rewrite ImJ_sub mulrCA mulrA mulfVK ?pnatr_eq0 //.
by rewrite -mulrA ['i%C * _]sqr_i mulrN1 opprB.
Qed.

Lemma complex_real (a b : R) : (a +i* b \is Num.real) = (b == 0).
Proof.
rewrite realE; simpc; rewrite [0 == _]eq_sym.
by have [] := ltrgtP 0 a; rewrite ?(andbF, andbT, orbF, orbb).
Qed.

Lemma complex_realP x : reflect (exists k, x = k%:C) (x \is Num.real).
Proof.
case: x=> [a b] /=; rewrite complex_real.
by apply: (iffP eqP) => [->|[c []//]]; exists a.
Qed.

Lemma RRe_real x : x \is Num.real -> (Re x)%:C = x.
Proof. by move=> /complex_realP [y ->]. Qed.

Lemma RIm_real x : x \is Num.real -> (Im x)%:C = 0.
Proof. by move=> /complex_realP [y ->]. Qed.

End ComplexTheory.

Section Rcomplex_normedZmodType.
Variable R : rcfType.
Implicit Types x y : Rcomplex R.

Import Normc.

Lemma le_normcD x y : (normc (x + y)) <= (normc x + normc y).
Proof. by rewrite -lecR rmorphD/=; exact: (@ler_normD _ R[i]). Qed.

Lemma normcMn x n : normc (x *+ n) = normc x *+ n.
Proof.
rewrite -[LHS]/(Re (_%:C)) -[RHS]/(Re (_%:C)) rmorphMn; congr Re. 
exact: (@normrMn _ R[i]).
Qed.

Lemma normcN x : normc (- x) = normc x.
Proof.
rewrite -[LHS]/(Re (_%:C)) -[RHS]/(Re (_%:C)); congr Re.
exact: (@normrN R[i] R[i]).
Qed.

HB.instance Definition _ := Num.Zmodule_isNormed.Build R (Rcomplex R)
  le_normcD (@eq0_normc R) normcMn normcN.
  
End Rcomplex_normedZmodType.

(* TODO: make R[i] and Rcomplex normed fields once codomains are generalized *)

Tactic Notation "simpc" := do ?
  [ rewrite -[- (_ +i* _)%C]/(_ +i* _)%C
  | rewrite -[(_ +i* _)%C - (_ +i* _)%C]/(_ +i* _)%C
  | rewrite -[(_ +i* _)%C + (_ +i* _)%C]/(_ +i* _)%C
  | rewrite -[(_ +i* _)%C * (_ +i* _)%C]/(_ +i* _)%C
  | rewrite -[(_ +i* _)%C ^*]/(_ +i* _)%C
  | rewrite -[_ *: (_ +i* _)%C]/(_ +i* _)%C
  | rewrite -[@GRing.scale _ (Rcomplex _) _ (_ +i* _)%C]/(_ +i* _)%C
  | rewrite -[(_ +i* _)%C <= (_ +i* _)%C]/((_ == _) && (_ <= _))
  | rewrite -[(_ +i* _)%C < (_ +i* _)%C]/((_ == _) && (_ < _))
  | rewrite -[`|(_ +i* _)%C|]/(sqrtr (_ + _))%:C%C
  | rewrite (mulrNN, mulrN, mulNr, opprB, opprD, mulr0, mul0r,
    subr0, sub0r, addr0, add0r, mulr1, mul1r, subrr, opprK, oppr0,
    eqxx) ].

Section RComplexLMod.
Variable R : rcfType.
Implicit Types (k : R) (x y z : Rcomplex R).

Lemma conjc_is_scalable : scalable (@conjc R : Rcomplex R -> Rcomplex R).
Proof. by move=> a [b c]; simpc. Qed.

HB.instance Definition _ :=
  GRing.isScalable.Build R (Rcomplex R) (Rcomplex R) *:%R (@conjc R : Rcomplex R -> Rcomplex R) conjc_is_scalable.

End RComplexLMod.

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
  rewrite mulr_ge0 // subr_ge0 (le_trans _ F2) //.
  by rewrite -(maxrN a) le_max lexx.
have F4: 0 <= (sqrtr (a ^+ 2 + b ^+ 2) + a) / 2%:R.
  rewrite mulr_ge0 // -{2}[a]opprK subr_ge0 (le_trans _ F2) //.
  by rewrite -(maxrN a) le_max lexx orbT.
congr (_ +i* _); set u := if _ then _ else _.
  rewrite mulrCA !mulrA.
  have->: (u * u) = 1.
    rewrite /u; case: (altP (_ =P _)); rewrite ?mul1r //.
    by rewrite -expr2 sqr_sg => ->.
  rewrite mul1r -!sqr !sqr_sqrtr //.
  rewrite [_+a]addrC -mulrBl opprD addrA addrK.
  by rewrite opprK -mulr2n -[a *+ 2]mulr_natl [_*a]mulrC mulfK.
rewrite mulrCA -mulrA -mulrDr [sqrtr _ * _]mulrC.
rewrite -mulr2n -sqrtrM // mulrAC !mulrA ?[_ * (_ - _)]mulrC -subr_sqr.
rewrite sqr_sqrtr.
  by rewrite ler_wpDr // exprn_even_ge0.
rewrite [_^+2 + _]addrC addrK -mulrA -expr2 sqrtrM ?exprn_even_ge0 //.
rewrite !sqrtr_sqr -(mulr_natr (_ * _)).
rewrite [`|_^-1|]ger0_norm // -mulrA [_ * _%:R]mulrC divff //.
rewrite mulr1 /u; case: (_ =P _)=>[->|].
  by rewrite normr0 mulr0.
by rewrite -numEsg.
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
Proof. by rewrite sqrtc_sqrtr ?lexx // sqrtr0. Qed.

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
by case: x => a b; simpc; rewrite -sqrtr_sqr ler_wsqrtr // lerDl sqr_ge0.
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
  rewrite -opprD opprK -mulrDr -mulr2n.
  by rewrite -(mulr_natl (_^-1)) divff ?mulr1 ?pnatr_eq0.
symmetry; rewrite -!alg_polyC scalerA; congr (_%:A).
rewrite [a * _]mulrC divfK // /r2 mulrA mulrACA -invfM -natrM -subr_sqr.
rewrite sqr_sqrtc sqrrN /d opprB addrC addrNK -(mulrA 4) -mulrA.
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
rewrite ltn_eqF // subr0 mulr1 summxE big1; last first.
  rewrite [w as X in X *m _]mx11_scalar => ->.
  by rewrite mul_scalar_mx scale0r submx0.
move=> [i' j'] /= /andP[lt_j'i'].
rewrite xpair_eqE /= => neq'_ij.
rewrite /= !mxvec_delta !mxE big_ord1 !mxE !eqxx !eq_mviE.
rewrite !xpair_eqE /= [_ == i']eq_sym [_ == j']eq_sym (negPf neq'_ij) /=.
set z := (_ && _); suff /negPf -> : ~~ z by rewrite subrr mulr0.
by apply: contraL lt_j'i' => /andP [/eqP <- /eqP <-]; rewrite ltnNge ltnW.
Qed.
Hint Resolve skew_direct_sum : core.

Lemma rank_skew : \rank skew = (n * n.-1)./2.
Proof.
rewrite /skew (mxdirectP _) //= -bin2 -bin2_sum big_mkord.
rewrite (eq_bigr (fun _ => 1%N)).
  move=> [i j] /= lt_ij; rewrite genmxE.
  apply/eqP; rewrite eqn_leq rank_leq_row /= lt0n mxrank_eq0.
  rewrite /skew_vec /= !mxvec_delta /= subr_eq0.
  set j1 := mxvec_index _ _.
  apply/negP => /eqP /matrixP /(_ 0 j1) /=; rewrite !mxE /= eqxx.
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
  by rewrite sum_nat_const card_ord muln1.
by rewrite -ltnS prednK // (leq_trans _ Hi).
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
rewrite [M' in LHS]matrix_sum_delta; congr (_ *: _).
rewrite pair_big /= !linear_sum /= -big_split /=.
rewrite (bigID (fun ij => (ij.2 : 'I__) < (ij.1 : 'I__))%N) /=; congr (_ + _).
  apply: eq_bigr => [] [i j] /= lt_ij.
  by rewrite !linearZ linearB /= ?mxvecK trmx_delta scalerN scalerBr.
rewrite (bigID (fun ij => (ij.1 : 'I__) == (ij.2 : 'I__))%N) /=.
rewrite big1 ?add0r.
  by move=> [i j] /= /andP[_ /eqP ->]; rewrite linearZ /= trmx_delta subrr.
rewrite (@reindex_inj _ _ _ _ (fun ij => (ij.2, ij.1))) /=.
  by move=> [? ?] [? ?] [] -> ->.
apply: eq_big => [] [i j] /=; first by rewrite -leqNgt ltn_neqAle andbC.
by rewrite !linearZ linearB /= ?mxvecK trmx_delta scalerN scalerBr.
Qed.

End Skew.

Notation skew K n := (@skew_def _ (Phant K) n).

Section Restriction.

Variable K : fieldType.
Variable m : nat.
Variable (V : 'M[K]_m).

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
rewrite eigenspace_restrict //; last by exists b.
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
pose L1 := lin_mx L1fun.
pose L2fun : 'M[R]_n -> _ :=
  2%:R^-1 \*: (((@GRing.opp _) \o (mulmxr u \o trmx) \+ mulmxr v)
           \+ ((mulmx (u^T) \o trmx)               \+ (mulmx (v^T)))).
pose L2 := lin_mx L2fun.
have [] := @Lemma4 _ _ 1%:M _ [::L1; L2] (erefl _).
+ by move: HrV; rewrite mxrank1 !dvdn2 ?negbK oddM andbb.
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
  rewrite [X in _ + (_ + _ + X) = _]addrC [X in _ + X = _]addrACA.
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
rewrite ['i%C *: _ + _]addrC [LHS]addrACA ['i%C *: _ + _]addrC [RHS]addrACA.
rewrite [X in _ + _ + X]addrC -scalerBr -!(rmorphB, rmorphD)/=.
rewrite [- _ + _ in RHS]addrC -scalerBr -!(rmorphB, rmorphD)/=.
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
pose L1 := lin_mx (mulmxr f \+ mulmx f^T).
pose L2 := lin_mx (mulmxr f \o mulmx f^T).
have [] /= := IHk _ (leqnn _) _  _ (skew R[i] n.+1) _ [::L1; L2] (erefl _).
+ rewrite rank_skew; apply: contra Hn.
  rewrite -(@dvdn_pmul2r 2) //= -expnSr muln2 -[_.*2]add0n.
  have n_odd : odd n by rewrite dvdn2 /= ?negbK in dvd2n *.
  have {2}<- : odd (n.+1 * n) = 0%N :> nat by rewrite oddM /= andNb.
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
rewrite rmorphM /= !rmorphB /= horner_mx_X !horner_mx_C mulmxA => Hv.
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

Lemma complex_acf_axiom : GRing.closed_field_axiom R[i].
Proof.
move=> n c n_gt0; pose p := 'X^n - \poly_(i < n) c i.
suff [x rpx] : exists x, root p x.
  exists x; move: rpx; rewrite /root /p hornerD hornerN hornerXn subr_eq0.
  by move=> /eqP ->; rewrite horner_poly.
have p_monic : p \is monic.
  rewrite qualifE/= lead_coefDl ?lead_coefXn //.
  by rewrite size_polyN size_polyXn ltnS size_poly.
have sp_gt1 : (size p > 1)%N.
  by rewrite size_polyDl size_polyXn // size_polyN ltnS size_poly.
case: n n_gt0 p => //= n _ p in p_monic sp_gt1 *.
have [] := Theorem7' (companionmx p); first by rewrite -(subnK sp_gt1) addn2.
by move=> x; rewrite eigenvalue_root_char companionmxK //; exists x.
Qed.

HB.instance Definition _ := Field_isAlgClosed.Build R[i] complex_acf_axiom.

HB.instance Definition _ := Num.NumField_isImaginary.Build R[i]
  (sqr_i R) sqr_normc.
HB.instance Definition _ := GRing.ClosedField.on (Rcomplex R).

End Paper_HarmDerksen.

End ComplexClosed.

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

HB.instance Definition _ := Num.ClosedField.on complexalg.

Lemma complexalg_algebraic : integralRange (@ratr complexalg).
Proof.
move=> x; suff [p p_monic] : integralOver (real_complex _ \o realalg_of _) x.
  by rewrite (eq_map_poly (fmorph_eq_rat _)); exists p.
by apply: complex_algebraic_trans; apply: realalg_algebraic.
Qed.
(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
From mathcomp Require Import ssrAC choice tuple bigop ssralg poly polydiv.
From mathcomp Require Import generic_quotient.

(* This file builds the field of fraction of any integral domain. *)
(* The main result of this file is the existence of the field *)
(* and of the tofrac function which is a injective ring morphism from R *)
(* to its fraction field {fraction R} *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope quotient_scope.

Reserved Notation "{ 'ratio' T }" (at level 0, format "{ 'ratio'  T }").
Reserved Notation "{ 'fraction' T }" (at level 0, format "{ 'fraction'  T }").
Reserved Notation "x %:F" (at level 2, format "x %:F").

Section FracDomain.
Variable R : ringType.

(* ratios are pairs of R, such that the second member is nonzero *)
Inductive ratio := mkRatio { frac :> R * R; _ : frac.2 != 0 }.
Definition ratio_of of phant R := ratio.
Local Notation "{ 'ratio' T }" := (ratio_of (Phant T)).

HB.instance Definition _ := [isSub for frac].
HB.instance Definition _ := [Choice of ratio by <:].
HB.instance Definition _ := Sub.on {ratio R}.
HB.instance Definition _ := Choice.on {ratio R}.

Lemma denom_ratioP : forall f : ratio, f.2 != 0. Proof. by case. Qed.

Definition ratio0 := (@mkRatio (0, 1) (oner_neq0 _)).
Definition Ratio x y : {ratio R} := insubd ratio0 (x, y).

Lemma numer_Ratio x y : y != 0 -> (Ratio x y).1 = x.
Proof. by move=> ny0; rewrite /Ratio /insubd insubT. Qed.

Lemma denom_Ratio x y : y != 0 -> (Ratio x y).2 = y.
Proof. by move=> ny0; rewrite /Ratio /insubd insubT. Qed.

Definition numden_Ratio := (numer_Ratio, denom_Ratio).

Variant Ratio_spec (n d : R) : {ratio R} -> R -> R -> Type :=
  | RatioNull of d = 0 : Ratio_spec n d ratio0 n 0
  | RatioNonNull (d_neq0 : d != 0) :
    Ratio_spec n d (@mkRatio (n, d) d_neq0) n d.

Lemma RatioP n d : Ratio_spec n d (Ratio n d) n d.
Proof.
rewrite /Ratio /insubd; case: insubP=> /= [x /= d_neq0 hx|].
  have ->: x = @mkRatio (n, d) d_neq0 by apply: val_inj.
  by constructor.
by rewrite negbK=> /eqP hx; rewrite {2}hx; constructor.
Qed.

Lemma Ratio0 x : Ratio x 0 = ratio0.
Proof. by rewrite /Ratio /insubd; case: insubP; rewrite //= eqxx. Qed.

End FracDomain.

Notation "{ 'ratio' T }" := (ratio_of (Phant T)) : type_scope.
Identity Coercion type_fracdomain_of : ratio_of >-> ratio.

Notation "'\n_' x"  := (frac x).1
  (at level 8, x at level 2, format "'\n_' x").
Notation "'\d_' x"  := (frac x).2
  (at level 8, x at level 2, format "'\d_' x").

Module FracField.
Section FracField.

Variable R : idomainType.

Local Notation frac := (R * R).
Local Notation dom := (ratio R).
Local Notation domP := denom_ratioP.

Implicit Types x y z : dom.

(* We define a relation in ratios *)
Local Notation equivf_notation x y := (\n_x * \d_y == \d_x * \n_y).
Definition equivf x y := equivf_notation x y.

Lemma equivfE x y : equivf x y = equivf_notation x y.
Proof. by []. Qed.

Lemma equivf_refl : reflexive equivf.
Proof. by move=> x; rewrite /equivf mulrC. Qed.

Lemma equivf_sym : symmetric equivf.
Proof. by move=> x y; rewrite /equivf eq_sym; congr (_==_); rewrite mulrC. Qed.

Lemma equivf_trans : transitive equivf.
Proof.
move=> [x Px] [y Py] [z Pz]; rewrite /equivf /= mulrC => /eqP xy /eqP yz.
by rewrite -(inj_eq (mulfI Px)) mulrA xy -mulrA yz mulrCA.
Qed.

(* we show that equivf is an equivalence *)
Canonical equivf_equiv := EquivRel equivf equivf_refl equivf_sym equivf_trans.

Definition type := {eq_quot equivf}.
Definition type_of of phant R := type.
Notation "{ 'fraction' T }" := (type_of (Phant T)) : type_scope.

(* we recover some structure for the quotient *)
HB.instance Definition _ : EqQuotient _ equivf type := EqQuotient.on type.
HB.instance Definition _ := Choice.on type.
HB.instance Definition _ := EqQuotient.on {fraction R}.
HB.instance Definition _ := Choice.on {fraction R}.

(* we explain what was the equivalence on the quotient *)
Lemma equivf_def (x y : ratio R) : x == y %[mod type]
                                    = (\n_x * \d_y == \d_x * \n_y).
Proof. by rewrite eqmodE. Qed.

Lemma equivf_r x : \n_x * \d_(repr (\pi_type x)) = \d_x * \n_(repr (\pi_type x)).
Proof. by apply/eqP; rewrite -equivf_def reprK. Qed.

Lemma equivf_l x : \n_(repr (\pi_type x)) * \d_x = \d_(repr (\pi_type x)) * \n_x.
Proof. by apply/eqP; rewrite -equivf_def reprK. Qed.

Lemma numer0 x : (\n_x == 0) = (x == (ratio0 R) %[mod_eq equivf]).
Proof. by rewrite eqmodE /= !equivfE // mulr1 mulr0. Qed.

Lemma Ratio_numden : forall x, Ratio \n_x \d_x = x.
Proof.
case=> [[n d] /= nd]; rewrite /Ratio /insubd; apply: val_inj=> /=.
by case: insubP=> //=; rewrite nd.
Qed.

Definition tofrac := lift_embed {fraction R} (fun x : R => Ratio x 1).
Canonical tofrac_pi_morph := PiEmbed tofrac.

Notation "x %:F"  := (@tofrac x).

Implicit Types a b c : type.

Definition addf x y : dom := Ratio (\n_x * \d_y + \n_y * \d_x) (\d_x * \d_y).
Definition add := lift_op2 {fraction R} addf.

Lemma pi_add : {morph \pi : x y / addf x y >-> add x y}.
Proof.
move=> x y; unlock add; apply/eqmodP; rewrite /= equivfE /addf /=.
rewrite !numden_Ratio ?mulf_neq0 ?domP // mulrDr mulrDl; apply/eqP.
symmetry; rewrite (AC (2*2) (3*1*2*4)) (AC (2*2) (3*2*1*4))/=.
by rewrite !equivf_l (ACl ((2*3)*(1*4))) (ACl ((2*3)*(4*1)))/=.
Qed.
Canonical pi_add_morph := PiMorph2 pi_add.

Definition oppf x : dom := Ratio (- \n_x) \d_x.
Definition opp := lift_op1 {fraction R} oppf.
Lemma pi_opp : {morph \pi : x / oppf x >-> opp x}.
Proof.
move=> x; unlock opp; apply/eqmodP; rewrite /= /equivf /oppf /=.
by rewrite !numden_Ratio ?(domP,mulf_neq0) // mulNr mulrN -equivf_r.
Qed.
Canonical pi_opp_morph := PiMorph1 pi_opp.

Definition mulf x y : dom := Ratio (\n_x * \n_y) (\d_x * \d_y).
Definition mul := lift_op2 {fraction R} mulf.

Lemma pi_mul : {morph \pi : x y / mulf x y >-> mul x y}.
Proof.
move=> x y; unlock mul; apply/eqmodP=> /=.
rewrite equivfE /= /addf /= !numden_Ratio ?mulf_neq0 ?domP //.
by rewrite mulrACA !equivf_r mulrACA.
Qed.
Canonical pi_mul_morph := PiMorph2 pi_mul.

Definition invf x : dom := Ratio \d_x \n_x.
Definition inv := lift_op1 {fraction R} invf.

Lemma pi_inv : {morph \pi : x / invf x >-> inv x}.
Proof.
move=> x; unlock inv; apply/eqmodP=> /=; rewrite equivfE /invf eq_sym.
do 2?case: RatioP=> /= [/eqP|];
  rewrite ?mul0r ?mul1r -?equivf_def ?numer0 ?reprK //.
  by move=> hx /eqP hx'; rewrite hx' eqxx in hx.
by move=> /eqP ->; rewrite eqxx.
Qed.
Canonical pi_inv_morph := PiMorph1 pi_inv.

Lemma addA : associative add.
Proof.
elim/quotW=> x; elim/quotW=> y; elim/quotW=> z; rewrite !piE.
rewrite /addf /= !numden_Ratio ?mulf_neq0 ?domP // !mulrDl.
by rewrite !mulrA !addrA ![_ * _ * \d_x]mulrAC.
Qed.

Lemma addC : commutative add.
Proof.
by elim/quotW=> x; elim/quotW=> y; rewrite !piE /addf addrC [\d__ * _]mulrC.
Qed.

Lemma add0_l : left_id 0%:F add.
Proof.
elim/quotW=> x; rewrite !piE /addf !numden_Ratio ?oner_eq0 //.
by rewrite mul0r mul1r mulr1 add0r Ratio_numden.
Qed.

Lemma addN_l : left_inverse 0%:F opp add.
Proof.
elim/quotW=> x; apply/eqP; rewrite piE /equivf.
rewrite /addf /oppf !numden_Ratio ?(oner_eq0, mulf_neq0, domP) //.
by rewrite mulr1 mulr0 mulNr addNr.
Qed.

(* fracions form an abelian group *)
HB.instance Definition _ := GRing.isZmodule.Build type addA addC add0_l addN_l.

Lemma mulA : associative mul.
Proof.
elim/quotW=> x; elim/quotW=> y; elim/quotW=> z; rewrite !piE.
by rewrite /mulf !numden_Ratio ?mulf_neq0 ?domP // !mulrA.
Qed.

Lemma mulC : commutative mul.
Proof.
elim/quotW=> x; elim/quotW=> y; rewrite !piE /mulf.
by rewrite [_ * (\d_x)]mulrC [_ * (\n_x)]mulrC.
Qed.

Lemma mul1_l : left_id 1%:F mul.
Proof.
elim/quotW=> x; rewrite !piE /mulf.
by rewrite !numden_Ratio ?oner_eq0 // !mul1r Ratio_numden.
Qed.

Lemma mul_addl : left_distributive mul add.
Proof.
elim/quotW=> x; elim/quotW=> y; elim/quotW=> z; apply/eqP.
rewrite !piE /equivf /mulf /addf !numden_Ratio ?mulf_neq0 ?domP //; apply/eqP.
rewrite !(mulrDr, mulrDl) (AC (3*(2*2)) (4*2*7*((1*3)*(6*5))))/=.
by rewrite [X in _ + X](AC (3*(2*2)) (4*6*7*((1*3)*(2*5))))/=.
Qed.

Lemma nonzero1 : 1%:F != 0%:F :> type.
Proof. by rewrite piE equivfE !numden_Ratio ?mul1r ?oner_eq0. Qed.

(* fractions form a commutative ring *)
HB.instance Definition _ :=
  GRing.Zmodule_isComRing.Build type mulA mulC mul1_l mul_addl nonzero1.

Lemma mulV_l : forall a, a != 0%:F -> mul (inv a) a = 1%:F.
Proof.
elim/quotW=> x /=; rewrite !piE.
rewrite /equivf !numden_Ratio ?oner_eq0 // mulr1 mulr0=> nx0.
apply/eqmodP; rewrite /= equivfE.
by rewrite !numden_Ratio ?(oner_eq0, mulf_neq0, domP) // !mulr1 mulrC.
Qed.

Lemma inv0 : inv 0%:F = 0%:F.
Proof.
rewrite !piE /invf !numden_Ratio ?oner_eq0 // /Ratio /insubd.
do 2?case: insubP; rewrite //= ?eqxx ?oner_eq0 // => u _ hu _.
by congr \pi; apply: val_inj; rewrite /= hu.
Qed.

(* fractions form a ring with explicit unit *)
(* fractions form a field *)
HB.instance Definition _ := GRing.ComRing_isField.Build type mulV_l inv0.

End FracField.
End FracField.
HB.export FracField.

Notation "{ 'fraction' T }" := (FracField.type_of (Phant T)).
Notation equivf := (@FracField.equivf _).
#[global] Hint Resolve denom_ratioP : core.

HB.instance Definition _ (R : idomainType) := GRing.Field.on {fraction R}.

Section FracFieldTheory.

Import FracField.

Variable R : idomainType.

Lemma Ratio_numden (x : {ratio R}) : Ratio \n_x \d_x = x.
Proof. exact: FracField.Ratio_numden. Qed.

(* exporting the embeding from R to {fraction R} *)
Local Notation tofrac := (@FracField.tofrac R).
Local Notation "x %:F" := (tofrac x).

Lemma tofrac_is_additive: additive tofrac.
Proof.
move=> p q /=; unlock tofrac.
rewrite -[X in _ = _ + X]pi_opp -[RHS]pi_add.
by rewrite /addf /oppf /= !numden_Ratio ?(oner_neq0, mul1r, mulr1).
Qed.

HB.instance Definition _ :=
  GRing.isAdditive.Build R [the zmodType of {fraction R}] tofrac
    tofrac_is_additive.

Lemma tofrac_is_multiplicative: multiplicative tofrac.
Proof.
split=> [p q|//]; unlock tofrac; rewrite -[RHS]pi_mul.
by rewrite /mulf /= !numden_Ratio ?(oner_neq0, mul1r, mulr1).
Qed.

HB.instance Definition _ :=
  GRing.isMultiplicative.Build R [the ringType of {fraction R}] tofrac
    tofrac_is_multiplicative.

(* tests *)
Lemma tofrac0 : 0%:F = 0. Proof. exact: rmorph0. Qed.
Lemma tofracN : {morph tofrac: x / - x}. Proof. exact: rmorphN. Qed.
Lemma tofracD : {morph tofrac: x y / x + y}. Proof. exact: rmorphD. Qed.
Lemma tofracB : {morph tofrac: x y / x - y}. Proof. exact: rmorphB. Qed.
Lemma tofracMn n : {morph tofrac: x / x *+ n}. Proof. exact: rmorphMn. Qed.
Lemma tofracMNn n : {morph tofrac: x / x *- n}. Proof. exact: rmorphMNn. Qed.
Lemma tofrac1 : 1%:F = 1. Proof. exact: rmorph1. Qed.
Lemma tofracM : {morph tofrac: x y  / x * y}. Proof. exact: rmorphM. Qed.
Lemma tofracX n : {morph tofrac: x / x ^+ n}. Proof. exact: rmorphX. Qed.

Lemma tofrac_eq (p q : R): (p%:F == q%:F) = (p == q).
Proof.
apply/eqP/eqP=> [|->//]; unlock tofrac=> /eqmodP /eqP /=.
by rewrite !numden_Ratio ?(oner_eq0, mul1r, mulr1).
Qed.

Lemma tofrac_eq0 (p : R): (p%:F == 0) = (p == 0).
Proof. by rewrite tofrac_eq. Qed.
End FracFieldTheory.

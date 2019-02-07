(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrfun ssrbool eqtype ssrnat div seq choice tuple.
From mathcomp
Require Import bigop ssralg poly polydiv generic_quotient.

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

Canonical ratio_subType := Eval hnf in [subType for frac].
Canonical ratio_of_subType := Eval hnf in [subType of {ratio R}].
Definition ratio_EqMixin := [eqMixin of ratio by <:].
Canonical ratio_eqType := EqType ratio ratio_EqMixin.
Canonical ratio_of_eqType := Eval hnf in [eqType of {ratio R}].
Definition ratio_ChoiceMixin := [choiceMixin of ratio by <:].
Canonical ratio_choiceType := ChoiceType ratio ratio_ChoiceMixin.
Canonical ratio_of_choiceType := Eval hnf in [choiceType of {ratio R}].

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

Notation "{ 'ratio' T }" := (ratio_of (Phant T)).
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
Notation "{ 'fraction' T }" := (type_of (Phant T)).

(* we recover some structure for the quotient *)
Canonical frac_quotType := [quotType of type].
Canonical frac_eqType := [eqType of type].
Canonical frac_choiceType := [choiceType of type].
Canonical frac_eqQuotType := [eqQuotType equivf of type].

Canonical frac_of_quotType := [quotType of {fraction R}].
Canonical frac_of_eqType := [eqType of {fraction R}].
Canonical frac_of_choiceType := [choiceType of {fraction R}].
Canonical frac_of_eqQuotType := [eqQuotType equivf of {fraction R}].

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
move=> x y; unlock add; apply/eqmodP; rewrite /= equivfE.
rewrite /addf /= !numden_Ratio ?mulf_neq0 ?domP //.
rewrite mulrDr mulrDl eq_sym; apply/eqP.
rewrite !mulrA ![_ * \n__]mulrC !mulrA equivf_l.
congr (_ + _); first by rewrite -mulrA mulrCA !mulrA.
rewrite -!mulrA [X in _ * X]mulrCA !mulrA equivf_l.
by rewrite mulrC !mulrA -mulrA mulrC mulrA.
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
rewrite mulrAC !mulrA -mulrA equivf_r -equivf_l.
by rewrite mulrA ![_ * \d_y]mulrC !mulrA.
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
rewrite /addf /= !numden_Ratio ?mulf_neq0 ?domP // !mulrDl !mulrA !addrA.
by congr (\pi (Ratio (_ + _ + _) _)); rewrite mulrAC.
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
Definition frac_zmodMixin :=  ZmodMixin addA addC add0_l addN_l.
Canonical frac_zmodType := Eval hnf in ZmodType type frac_zmodMixin.

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
rewrite !(mulrDr, mulrDl) !mulrA; congr (_ * _ + _ * _).
  rewrite ![_ * \n_z]mulrC -!mulrA; congr (_ * _).
  rewrite ![\d_y * _]mulrC !mulrA; congr (_ * _ * _).
  by rewrite [X in _ = X]mulrC mulrA.
rewrite ![_ * \n_z]mulrC -!mulrA; congr (_ * _).
rewrite ![\d_x * _]mulrC !mulrA; congr (_ * _ * _).
by rewrite -mulrA mulrC [X in X * _] mulrC.
Qed.

Lemma nonzero1 : 1%:F != 0%:F :> type.
Proof. by rewrite piE equivfE !numden_Ratio ?mul1r ?oner_eq0. Qed.

(* fracions form a commutative ring *)
Definition frac_comRingMixin := ComRingMixin mulA mulC mul1_l mul_addl nonzero1.
Canonical frac_ringType := Eval hnf in RingType type frac_comRingMixin.
Canonical frac_comRingType := Eval hnf in ComRingType type mulC.

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
Definition RatFieldUnitMixin := FieldUnitMixin mulV_l inv0.
Canonical frac_unitRingType := Eval hnf in UnitRingType type RatFieldUnitMixin.
Canonical frac_comUnitRingType := [comUnitRingType of type].

Lemma field_axiom : GRing.Field.mixin_of frac_unitRingType.
Proof. exact. Qed.

(* fractions form a field *)
Definition RatFieldIdomainMixin := (FieldIdomainMixin field_axiom).
Canonical frac_idomainType :=
  Eval hnf in IdomainType type (FieldIdomainMixin field_axiom).
Canonical frac_fieldType := FieldType type field_axiom.

End FracField.
End FracField.

Notation "{ 'fraction' T }" := (FracField.type_of (Phant T)).
Notation equivf := (@FracField.equivf _).
Hint Resolve denom_ratioP : core.

Section Canonicals.

Variable R : idomainType.

(* reexporting the structures *)
Canonical FracField.frac_quotType.
Canonical FracField.frac_eqType.
Canonical FracField.frac_choiceType.
Canonical FracField.frac_zmodType.
Canonical FracField.frac_ringType.
Canonical FracField.frac_comRingType.
Canonical FracField.frac_unitRingType.
Canonical FracField.frac_comUnitRingType.
Canonical FracField.frac_idomainType.
Canonical FracField.frac_fieldType.
Canonical FracField.tofrac_pi_morph.
Canonical frac_of_quotType := Eval hnf in [quotType of {fraction R}].
Canonical frac_of_eqType := Eval hnf  in [eqType of {fraction R}].
Canonical frac_of_choiceType := Eval hnf in [choiceType of {fraction R}].
Canonical frac_of_zmodType := Eval hnf in [zmodType of {fraction R}].
Canonical frac_of_ringType := Eval hnf in [ringType of {fraction R}].
Canonical frac_of_comRingType := Eval hnf in [comRingType of {fraction R}].
Canonical frac_of_unitRingType := Eval hnf in [unitRingType of {fraction R}].
Canonical frac_of_comUnitRingType := Eval hnf in [comUnitRingType of {fraction R}].
Canonical frac_of_idomainType := Eval hnf in [idomainType of {fraction R}].
Canonical frac_of_fieldType := Eval hnf in [fieldType of {fraction R}].

End Canonicals.

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
rewrite -[X in _ = _ + X]pi_opp -[X in _ = X]pi_add.
by rewrite /addf /oppf /= !numden_Ratio ?(oner_neq0, mul1r, mulr1).
Qed.

Canonical tofrac_additive := Additive tofrac_is_additive.

Lemma tofrac_is_multiplicative: multiplicative tofrac.
Proof.
split=> [p q|//]; unlock tofrac; rewrite -[X in _ = X]pi_mul.
by rewrite /mulf /= !numden_Ratio ?(oner_neq0, mul1r, mulr1).
Qed.

Canonical tofrac_rmorphism := AddRMorphism tofrac_is_multiplicative.

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

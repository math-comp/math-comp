(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrfun ssrbool eqtype ssrnat seq path choice div.
From mathcomp
Require Import fintype tuple finfun bigop prime ssralg ssrnum finset fingroup.
From mathcomp
Require Import morphism perm automorphism quotient action zmodp cyclic center.
From mathcomp
Require Import gproduct commutator gseries nilpotent pgroup sylow maximal.
From mathcomp
Require Import frobenius.
From mathcomp
Require Import matrix mxalgebra mxrepresentation vector algC classfun character.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(******************************************************************************)
(* This file contains the definitions and properties of inertia groups:       *)
(*   (phi ^ y)%CF == the y-conjugate of phi : 'CF(G), i.e., the class         *)
(*                   function mapping x ^ y to phi x provided y normalises G. *)
(*                   We take (phi ^ y)%CF = phi when y \notin 'N(G).          *)
(*  (phi ^: G)%CF == the sequence of all distinct conjugates of phi : 'CF(H)  *)
(*                   by all y in G.                                           *)
(*        'I[phi] == the inertia group of phi : CF(H), i.e., the set of y     *)
(*                   such that (phi ^ y)%CF = phi AND H :^ y = y.             *)
(*      'I_G[phi] == the inertia group of phi in G, i.e., G :&: 'I[phi].      *)
(* conjg_Iirr i y == the index j : Iirr G such that ('chi_i ^ y)%CF = 'chi_j. *)
(* cfclass_Iirr G i == the image of G under conjg_Iirr i, i.e., the set of j  *)
(*                   such that 'chi_j \in ('chi_i ^: G)%CF.                   *)
(*   mul_Iirr i j == the index k such that 'chi_j * 'chi_i = 'chi[G]_k,       *)
(*                   or 0 if 'chi_j * 'chi_i is reducible.                    *)
(* mul_mod_Iirr i j := mul_Iirr i (mod_Iirr j), for j : Iirr (G / H).         *)
(******************************************************************************)

Reserved Notation "''I[' phi ]"
  (at level 8, format "''I[' phi ]").
Reserved Notation "''I_' G [ phi ]"
  (at level 8, G at level 2, format "''I_' G [ phi ]").

Section ConjDef.

Variables (gT : finGroupType) (B : {set gT}) (y : gT) (phi : 'CF(B)).
Local Notation G := <<B>>.

Fact cfConjg_subproof :
  is_class_fun G [ffun x => phi (if y \in 'N(G) then x ^ y^-1 else x)].
Proof.
apply: intro_class_fun => [x z _ Gz | x notGx].
  have [nGy | _] := ifP; last by rewrite cfunJgen.
  by rewrite -conjgM conjgC conjgM cfunJgen // memJ_norm ?groupV.
by rewrite cfun0gen //; case: ifP => // nGy; rewrite memJ_norm ?groupV.
Qed.
Definition cfConjg := Cfun 1 cfConjg_subproof.

End ConjDef.

Prenex Implicits cfConjg.
Notation "f ^ y" := (cfConjg y f) : cfun_scope.

Section Conj.

Variables (gT : finGroupType) (G : {group gT}).
Implicit Type phi : 'CF(G).

Lemma cfConjgE phi y x : y \in 'N(G) -> (phi ^ y)%CF x = phi (x ^ y^-1)%g.
Proof. by rewrite cfunElock genGid => ->. Qed.

Lemma cfConjgEJ phi y x : y \in 'N(G) -> (phi ^ y)%CF (x ^ y) = phi x.
Proof. by move/cfConjgE->; rewrite conjgK. Qed.

Lemma cfConjgEout phi y : y \notin 'N(G) -> (phi ^ y = phi)%CF.
Proof.
by move/negbTE=> notNy; apply/cfunP=> x; rewrite !cfunElock genGid notNy.
Qed.

Lemma cfConjgEin phi y (nGy : y \in 'N(G)) :
  (phi ^ y)%CF = cfIsom (norm_conj_isom nGy) phi.
Proof.
apply/cfun_inP=> x Gx.
by rewrite cfConjgE // -{2}[x](conjgKV y) cfIsomE ?memJ_norm ?groupV.
Qed.

Lemma cfConjgMnorm phi :
  {in 'N(G) &, forall y z, phi ^ (y * z) = (phi ^ y) ^ z}%CF.
Proof.
move=> y z nGy nGz.
by apply/cfunP=> x; rewrite !cfConjgE ?groupM // invMg conjgM.
Qed.

Lemma cfConjg_id phi y : y \in G -> (phi ^ y)%CF = phi.
Proof.
move=> Gy; apply/cfunP=> x; have nGy := subsetP (normG G) y Gy.
by rewrite -(cfunJ _ _ Gy) cfConjgEJ.
Qed.

(* Isaacs' 6.1.b *)
Lemma cfConjgM L phi :
  G <| L -> {in L &, forall y z, phi ^ (y * z) = (phi ^ y) ^ z}%CF.
Proof. by case/andP=> _ /subsetP nGL; apply: sub_in2 (cfConjgMnorm phi). Qed.

Lemma cfConjgJ1 phi : (phi ^ 1)%CF = phi.
Proof. by apply/cfunP=> x; rewrite cfConjgE ?group1 // invg1 conjg1. Qed.

Lemma cfConjgK y : cancel (cfConjg y) (cfConjg y^-1 : 'CF(G) -> 'CF(G)).
Proof.
move=> phi; apply/cfunP=> x; rewrite !cfunElock groupV /=.
by case: ifP => -> //; rewrite conjgKV.
Qed.

Lemma cfConjgKV y : cancel (cfConjg y^-1) (cfConjg y : 'CF(G) -> 'CF(G)).
Proof. by move=> phi /=; rewrite -{1}[y]invgK cfConjgK. Qed.

Lemma cfConjg1 phi y : (phi ^ y)%CF 1%g = phi 1%g.
Proof. by rewrite cfunElock conj1g if_same. Qed.

Fact cfConjg_is_linear y : linear (cfConjg y : 'CF(G) -> 'CF(G)).
Proof. by move=> a phi psi; apply/cfunP=> x; rewrite !cfunElock. Qed.
Canonical cfConjg_additive y := Additive (cfConjg_is_linear y).
Canonical cfConjg_linear y := AddLinear (cfConjg_is_linear y).

Lemma cfConjg_cfuniJ A y : y \in 'N(G) -> ('1_A ^ y)%CF = '1_(A :^ y) :> 'CF(G).
Proof.
move=> nGy; apply/cfunP=> x; rewrite !cfunElock genGid nGy -sub_conjgV.
by rewrite -class_lcoset -class_rcoset norm_rlcoset ?memJ_norm ?groupV.
Qed.

Lemma cfConjg_cfuni A y : y \in 'N(A) -> ('1_A ^ y)%CF = '1_A :> 'CF(G).
Proof.
by have [/cfConjg_cfuniJ-> /normP-> | /cfConjgEout] := boolP (y \in 'N(G)).
Qed.

Lemma cfConjg_cfun1 y : (1 ^ y)%CF = 1 :> 'CF(G).
Proof.
by rewrite -cfuniG; have [/cfConjg_cfuni|/cfConjgEout] := boolP (y \in 'N(G)).
Qed.

Fact cfConjg_is_multiplicative y : multiplicative (cfConjg y : _ -> 'CF(G)).
Proof.
split=> [phi psi|]; last exact: cfConjg_cfun1.
by apply/cfunP=> x; rewrite !cfunElock.
Qed.
Canonical cfConjg_rmorphism y := AddRMorphism (cfConjg_is_multiplicative y).
Canonical cfConjg_lrmorphism y := [lrmorphism of cfConjg y].

Lemma cfConjg_eq1 phi y : ((phi ^ y)%CF == 1) = (phi == 1).
Proof. by apply: rmorph_eq1; apply: can_inj (cfConjgK y). Qed.

Lemma cfAutConjg phi u y : cfAut u (phi ^ y) = (cfAut u phi ^ y)%CF.
Proof. by apply/cfunP=> x; rewrite !cfunElock. Qed.

Lemma conj_cfConjg phi y : (phi ^ y)^*%CF = (phi^* ^ y)%CF.
Proof. exact: cfAutConjg. Qed.

Lemma cfker_conjg phi y : y \in 'N(G) -> cfker (phi ^ y) = cfker phi :^ y.
Proof.
move=> nGy; rewrite cfConjgEin // cfker_isom.
by rewrite morphim_conj (setIidPr (cfker_sub _)).
Qed.

Lemma cfDetConjg phi y : cfDet (phi ^ y) = (cfDet phi ^ y)%CF.
Proof.
have [nGy | not_nGy] := boolP (y \in 'N(G)); last by rewrite !cfConjgEout.
by rewrite !cfConjgEin cfDetIsom.
Qed.

End Conj.

Section Inertia.

Variable gT : finGroupType.

Definition inertia (B : {set gT}) (phi : 'CF(B)) :=  
  [set y in 'N(B) | (phi ^ y)%CF == phi].

Local Notation "''I[' phi ]" := (inertia phi) : group_scope.
Local Notation "''I_' G [ phi ]" := (G%g :&: 'I[phi]) : group_scope.

Fact group_set_inertia (H : {group gT}) phi : group_set 'I[phi : 'CF(H)].
Proof.
apply/group_setP; split; first by rewrite inE group1 /= cfConjgJ1.
move=> y z /setIdP[nHy /eqP n_phi_y] /setIdP[nHz n_phi_z].
by rewrite inE groupM //= cfConjgMnorm ?n_phi_y.
Qed.
Canonical inertia_group H phi := Group (@group_set_inertia H phi).

Local Notation "''I[' phi ]" := (inertia_group phi) : Group_scope.
Local Notation "''I_' G [ phi ]" := (G :&: 'I[phi])%G : Group_scope.

Variables G H : {group gT}.
Implicit Type phi : 'CF(H).

Lemma inertiaJ phi y : y \in 'I[phi] -> (phi ^ y)%CF = phi.
Proof. by case/setIdP=> _ /eqP->. Qed.

Lemma inertia_valJ phi x y : y \in 'I[phi] -> phi (x ^ y)%g = phi x.
Proof. by case/setIdP=> nHy /eqP {1}<-; rewrite cfConjgEJ. Qed.

(* To disambiguate basic inclucion lemma names we capitalize Inertia for      *)
(* lemmas concerning the localized inertia group 'I_G[phi].                   *)
Lemma Inertia_sub phi : 'I_G[phi] \subset G.
Proof. exact: subsetIl. Qed.

Lemma norm_inertia phi : 'I[phi] \subset 'N(H).
Proof. by rewrite ['I[_]]setIdE subsetIl. Qed.

Lemma sub_inertia phi : H \subset 'I[phi].
Proof.
by apply/subsetP=> y Hy; rewrite inE cfConjg_id ?(subsetP (normG H)) /=.
Qed.

Lemma normal_inertia phi : H <| 'I[phi].
Proof. by rewrite /normal sub_inertia norm_inertia. Qed.

Lemma sub_Inertia phi : H \subset G -> H \subset 'I_G[phi].
Proof. by rewrite subsetI sub_inertia andbT. Qed.

Lemma norm_Inertia phi : 'I_G[phi] \subset 'N(H).
Proof. by rewrite setIC subIset ?norm_inertia. Qed.

Lemma normal_Inertia phi : H \subset G -> H <| 'I_G[phi].
Proof. by rewrite /normal norm_Inertia andbT; apply: sub_Inertia. Qed.

Lemma cfConjg_eqE phi :
    H <| G ->
  {in G &, forall y z, (phi ^ y == phi ^ z)%CF = (z \in 'I_G[phi] :* y)}.
Proof.
case/andP=> _ nHG y z Gy; rewrite -{1 2}[z](mulgKV y) groupMr // mem_rcoset.
move: {z}(z * _)%g => z Gz; rewrite 2!inE Gz cfConjgMnorm ?(subsetP nHG) //=.
by rewrite eq_sym (can_eq (cfConjgK y)).
Qed.

Lemma cent_sub_inertia phi : 'C(H) \subset 'I[phi].
Proof.
apply/subsetP=> y cHy; have nHy := subsetP (cent_sub H) y cHy.
rewrite inE nHy; apply/eqP/cfun_inP=> x Hx; rewrite cfConjgE //.
by rewrite /conjg invgK mulgA (centP cHy) ?mulgK.
Qed.

Lemma cent_sub_Inertia phi : 'C_G(H) \subset 'I_G[phi].
Proof. exact: setIS (cent_sub_inertia phi). Qed.

Lemma center_sub_Inertia phi : H \subset G -> 'Z(G) \subset 'I_G[phi].
Proof.
by move/centS=> sHG; rewrite setIS // (subset_trans sHG) // cent_sub_inertia.
Qed.

Lemma conjg_inertia phi y : y \in 'N(H) -> 'I[phi] :^ y = 'I[phi ^ y].
Proof.
move=> nHy; apply/setP=> z; rewrite !['I[_]]setIdE conjIg conjGid // !in_setI.
apply/andb_id2l=> nHz; rewrite mem_conjg !inE.
by rewrite !cfConjgMnorm ?in_group ?(can2_eq (cfConjgKV y) (cfConjgK y)) ?invgK.
Qed.

Lemma inertia0 : 'I[0 : 'CF(H)] = 'N(H).
Proof. by apply/setP=> x; rewrite !inE linear0 eqxx andbT. Qed.

Lemma inertia_add phi psi : 'I[phi] :&: 'I[psi] \subset 'I[phi + psi].
Proof.
rewrite !['I[_]]setIdE -setIIr setIS //.
by apply/subsetP=> x; rewrite !inE linearD /= => /andP[/eqP-> /eqP->].
Qed.

Lemma inertia_sum I r (P : pred I) (Phi : I -> 'CF(H)) :
  'N(H) :&: \bigcap_(i <- r | P i) 'I[Phi i]
     \subset 'I[\sum_(i <- r | P i) Phi i].
Proof.
elim/big_rec2: _ => [|i K psi Pi sK_Ipsi]; first by rewrite setIT inertia0.
by rewrite setICA; apply: subset_trans (setIS _ sK_Ipsi) (inertia_add _ _).
Qed.

Lemma inertia_scale a phi : 'I[phi] \subset 'I[a *: phi].
Proof.
apply/subsetP=> x /setIdP[nHx /eqP Iphi_x].
by rewrite inE nHx linearZ /= Iphi_x.
Qed.

Lemma inertia_scale_nz a phi : a != 0 -> 'I[a *: phi] = 'I[phi].
Proof.
move=> nz_a; apply/eqP.
by rewrite eqEsubset -{2}(scalerK nz_a phi) !inertia_scale.
Qed.

Lemma inertia_opp phi : 'I[- phi] = 'I[phi].
Proof. by rewrite -scaleN1r inertia_scale_nz // oppr_eq0 oner_eq0. Qed.

Lemma inertia1 : 'I[1 : 'CF(H)] = 'N(H).
Proof. by apply/setP=> x; rewrite inE rmorph1 eqxx andbT. Qed.

Lemma Inertia1 : H <| G -> 'I_G[1 : 'CF(H)] = G.
Proof. by rewrite inertia1 => /normal_norm/setIidPl. Qed.

Lemma inertia_mul phi psi : 'I[phi] :&: 'I[psi] \subset 'I[phi * psi].
Proof.
rewrite !['I[_]]setIdE -setIIr setIS //.
by apply/subsetP=> x; rewrite !inE rmorphM /= => /andP[/eqP-> /eqP->].
Qed.

Lemma inertia_prod I r (P : pred I) (Phi : I -> 'CF(H)) :
  'N(H) :&: \bigcap_(i <- r | P i) 'I[Phi i]
     \subset 'I[\prod_(i <- r | P i) Phi i].
Proof.
elim/big_rec2: _ => [|i K psi Pi sK_psi]; first by rewrite inertia1 setIT.
by rewrite setICA; apply: subset_trans (setIS _ sK_psi) (inertia_mul _ _).
Qed.

Lemma inertia_injective (chi : 'CF(H)) :
  {in H &, injective chi} -> 'I[chi] = 'C(H).
Proof.
move=> inj_chi; apply/eqP; rewrite eqEsubset cent_sub_inertia andbT.
apply/subsetP=> y Ichi_y; have /setIdP[nHy _] := Ichi_y.
apply/centP=> x Hx; apply/esym/commgP/conjg_fixP.
by apply/inj_chi; rewrite ?memJ_norm ?(inertia_valJ _ Ichi_y).
Qed.

Lemma inertia_irr_prime p i :
  #|H| = p -> prime p -> i != 0 -> 'I['chi[H]_i] = 'C(H).
Proof. by move=> <- pr_H /(irr_prime_injP pr_H); apply: inertia_injective. Qed.

Lemma inertia_irr0 : 'I['chi[H]_0] = 'N(H).
Proof. by rewrite irr0 inertia1. Qed.

(* Isaacs' 6.1.c *)
Lemma cfConjg_iso y : isometry (cfConjg y : 'CF(H) -> 'CF(H)).
Proof.
move=> phi psi; congr (_ * _).
have [nHy | not_nHy] := boolP (y \in 'N(H)); last by rewrite !cfConjgEout.
rewrite (reindex_astabs 'J y) ?astabsJ //=.
by apply: eq_bigr=> x _; rewrite !cfConjgEJ.
Qed.
 
(* Isaacs' 6.1.d *)
Lemma cfdot_Res_conjg psi phi y :
  y \in G -> '['Res[H, G] psi, phi ^ y] = '['Res[H] psi, phi].
Proof.
move=> Gy; rewrite -(cfConjg_iso y _ phi); congr '[_, _]; apply/cfunP=> x.
rewrite !cfunElock !genGid; case nHy: (y \in 'N(H)) => //.
by rewrite !(fun_if psi) cfunJ ?memJ_norm ?groupV.
Qed.

(* Isaac's 6.1.e *)
Lemma cfConjg_char (chi : 'CF(H)) y :
  chi \is a character -> (chi ^ y)%CF \is a character.
Proof.
have [nHy Nchi | /cfConjgEout-> //] := boolP (y \in 'N(H)).
by rewrite cfConjgEin cfIsom_char.
Qed.

Lemma cfConjg_lin_char (chi : 'CF(H)) y :
  chi \is a linear_char -> (chi ^ y)%CF \is a linear_char.
Proof. by case/andP=> Nchi chi1; rewrite qualifE cfConjg1 cfConjg_char. Qed.

Lemma cfConjg_irr y chi : chi \in irr H -> (chi ^ y)%CF \in irr H.
Proof. by rewrite !irrEchar cfConjg_iso => /andP[/cfConjg_char->]. Qed.
 
Definition conjg_Iirr i y := cfIirr ('chi[H]_i ^ y)%CF.

Lemma conjg_IirrE i y : 'chi_(conjg_Iirr i y) = ('chi_i ^ y)%CF.
Proof. by rewrite cfIirrE ?cfConjg_irr ?mem_irr. Qed.

Lemma conjg_IirrK y : cancel (conjg_Iirr^~ y) (conjg_Iirr^~ y^-1%g).
Proof. by move=> i; apply/irr_inj; rewrite !conjg_IirrE cfConjgK. Qed.

Lemma conjg_IirrKV y : cancel (conjg_Iirr^~ y^-1%g) (conjg_Iirr^~ y).
Proof. by rewrite -{2}[y]invgK; apply: conjg_IirrK. Qed.

Lemma conjg_Iirr_inj y : injective (conjg_Iirr^~ y).
Proof. exact: can_inj (conjg_IirrK y). Qed.

Lemma conjg_Iirr_eq0 i y : (conjg_Iirr i y == 0) = (i == 0).
Proof. by rewrite -!irr_eq1 conjg_IirrE cfConjg_eq1. Qed.

Lemma conjg_Iirr0 x : conjg_Iirr 0 x = 0.
Proof. by apply/eqP; rewrite conjg_Iirr_eq0. Qed.

Lemma cfdot_irr_conjg i y :
  H <| G -> y \in G -> '['chi_i, 'chi_i ^ y]_H = (y \in 'I_G['chi_i])%:R.
Proof.
move=> nsHG Gy; rewrite -conjg_IirrE cfdot_irr -(inj_eq irr_inj) conjg_IirrE.
by rewrite -{1}['chi_i]cfConjgJ1 cfConjg_eqE ?mulg1.
Qed.

Definition cfclass (A : {set gT}) (phi : 'CF(A)) (B : {set gT}) := 
  [seq (phi ^ repr Tx)%CF | Tx in rcosets 'I_B[phi] B].

Local Notation "phi ^: G" := (cfclass phi G) : cfun_scope.

Lemma size_cfclass i : size ('chi[H]_i ^: G)%CF = #|G : 'I_G['chi_i]|.
Proof. by rewrite size_map -cardE. Qed.

Lemma cfclassP (A : {group gT}) phi psi :
  reflect (exists2 y, y \in A & psi = phi ^ y)%CF (psi \in phi ^: A)%CF.
Proof.
apply: (iffP imageP) => [[_ /rcosetsP[y Ay ->] ->] | [y Ay ->]].
  by case: repr_rcosetP => z /setIdP[Az _]; exists (z * y)%g; rewrite ?groupM.
without loss nHy: y Ay / y \in 'N(H).
  have [nHy | /cfConjgEout->] := boolP (y \in 'N(H)); first exact.
  by move/(_ 1%g); rewrite !group1 !cfConjgJ1; apply.
exists ('I_A[phi] :* y); first by rewrite -rcosetE mem_imset.
case: repr_rcosetP => z /setIP[_ /setIdP[nHz /eqP Tz]].
by rewrite cfConjgMnorm ?Tz.
Qed.

Lemma cfclassInorm phi : (phi ^: 'N_G(H) =i phi ^: G)%CF.
Proof.
move=> xi; apply/cfclassP/cfclassP=> [[x /setIP[Gx _] ->] | [x Gx ->]].
  by exists x.
have [Nx | /cfConjgEout-> //] := boolP (x \in 'N(H)).
  by exists x; first apply/setIP.
by exists 1%g; rewrite ?group1 ?cfConjgJ1.
Qed.

Lemma cfclass_refl phi : phi \in (phi ^: G)%CF.
Proof. by apply/cfclassP; exists 1%g => //; rewrite cfConjgJ1. Qed.

Lemma cfclass_transr phi psi :
  (psi \in phi ^: G)%CF -> (phi ^: G =i psi ^: G)%CF.
Proof.
rewrite -cfclassInorm; case/cfclassP=> x Gx -> xi; rewrite -!cfclassInorm.
have nHN: {subset 'N_G(H) <= 'N(H)} by apply/subsetP; apply: subsetIr.
apply/cfclassP/cfclassP=> [[y Gy ->] | [y Gy ->]].
  by exists (x^-1 * y)%g; rewrite -?cfConjgMnorm ?groupM ?groupV ?nHN // mulKVg.
by exists (x * y)%g; rewrite -?cfConjgMnorm ?groupM ?nHN.
Qed.

Lemma cfclass_sym phi psi : (psi \in phi ^: G)%CF = (phi \in psi ^: G)%CF.
Proof. by apply/idP/idP=> /cfclass_transr <-; apply: cfclass_refl. Qed.

Lemma cfclass_uniq phi : H <| G -> uniq (phi ^: G)%CF.
Proof.
move=> nsHG; rewrite map_inj_in_uniq ?enum_uniq // => Ty Tz; rewrite !mem_enum.
move=> {Ty}/rcosetsP[y Gy ->] {Tz}/rcosetsP[z Gz ->] /eqP.
case: repr_rcosetP => u Iphi_u; case: repr_rcosetP => v Iphi_v.
have [[Gu _] [Gv _]] := (setIdP Iphi_u, setIdP Iphi_v).
rewrite cfConjg_eqE ?groupM // => /rcoset_eqP.
by rewrite !rcosetM (rcoset_id Iphi_v) (rcoset_id Iphi_u).
Qed.

Lemma cfclass_invariant phi : G \subset 'I[phi] -> (phi ^: G)%CF = phi.
Proof.
move/setIidPl=> IGphi; rewrite /cfclass IGphi // rcosets_id.
by rewrite /(image _ _) enum_set1 /= repr_group cfConjgJ1.
Qed.

Lemma cfclass1 : H <| G -> (1 ^: G)%CF = [:: 1 : 'CF(H)].
Proof. by move/normal_norm=> nHG; rewrite cfclass_invariant ?inertia1.  Qed.

Definition cfclass_Iirr (A : {set gT}) i := conjg_Iirr i @: A.

Lemma cfclass_IirrE i j :
  (j \in cfclass_Iirr G i) = ('chi_j \in 'chi_i ^: G)%CF.
Proof.
apply/imsetP/cfclassP=> [[y Gy ->] | [y]]; exists y; rewrite ?conjg_IirrE //.
by apply: irr_inj; rewrite conjg_IirrE.
Qed.

Lemma eq_cfclass_IirrE i j :
  (cfclass_Iirr G j == cfclass_Iirr G i) = (j \in cfclass_Iirr G i).
Proof.
apply/eqP/idP=> [<- | iGj]; first by rewrite cfclass_IirrE cfclass_refl.
by apply/setP=> k; rewrite !cfclass_IirrE in iGj *; apply/esym/cfclass_transr.
Qed.

Lemma im_cfclass_Iirr i :
  H <| G -> perm_eq [seq 'chi_j | j in cfclass_Iirr G i] ('chi_i ^: G)%CF.
Proof.
move=> nsHG; have UchiG := cfclass_uniq 'chi_i nsHG.
apply: uniq_perm_eq; rewrite ?(map_inj_uniq irr_inj) ?enum_uniq // => phi.
apply/imageP/idP=> [[j iGj ->] | /cfclassP[y]]; first by rewrite -cfclass_IirrE.
by exists (conjg_Iirr i y); rewrite ?mem_imset ?conjg_IirrE.
Qed.

Lemma card_cfclass_Iirr i : H <| G -> #|cfclass_Iirr G i| = #|G : 'I_G['chi_i]|.
Proof.
move=> nsHG; rewrite -size_cfclass -(perm_eq_size (im_cfclass_Iirr i nsHG)).
by rewrite size_map -cardE.
Qed.

Lemma reindex_cfclass R idx (op : Monoid.com_law idx) (F : 'CF(H) -> R) i :
     H <| G ->
  \big[op/idx]_(chi <- ('chi_i ^: G)%CF) F chi
     = \big[op/idx]_(j | 'chi_j \in ('chi_i ^: G)%CF) F 'chi_j.
Proof.
move/im_cfclass_Iirr/(eq_big_perm _) <-; rewrite big_map big_filter /=.
by apply: eq_bigl => j; rewrite cfclass_IirrE.
Qed.

Lemma cfResInd j:
    H <| G ->
  'Res[H] ('Ind[G] 'chi_j) = #|H|%:R^-1 *: (\sum_(y in G) 'chi_j ^ y)%CF.
Proof.
case/andP=> [sHG /subsetP nHG].
rewrite (reindex_inj invg_inj); apply/cfun_inP=> x Hx.
rewrite cfResE // cfIndE // ?cfunE ?sum_cfunE; congr (_ * _).
by apply: eq_big => [y | y Gy]; rewrite ?cfConjgE ?groupV ?invgK ?nHG.
Qed.

(* This is Isaacs, Theorem (6.2) *)
Lemma Clifford_Res_sum_cfclass i j :
     H <| G -> j \in irr_constt ('Res[H, G] 'chi_i) ->
  'Res[H] 'chi_i = 
     '['Res[H] 'chi_i, 'chi_j] *: (\sum_(chi <- ('chi_j ^: G)%CF) chi).
Proof.
move=> nsHG chiHj; have [sHG /subsetP nHG] := andP nsHG.
rewrite reindex_cfclass //= big_mkcond.
rewrite {1}['Res _]cfun_sum_cfdot linear_sum /=; apply: eq_bigr => k _.
have [[y Gy ->] | ] := altP (cfclassP _ _ _); first by rewrite cfdot_Res_conjg.
apply: contraNeq; rewrite scaler0 scaler_eq0 orbC => /norP[_ chiHk].
have{chiHk chiHj}: '['Res[H] ('Ind[G] 'chi_j), 'chi_k] != 0.
  rewrite !inE !cfdot_Res_l in chiHj chiHk *.
  apply: contraNneq chiHk; rewrite cfdot_sum_irr => /psumr_eq0P/(_ i isT)/eqP.
  rewrite -cfdotC cfdotC mulf_eq0 conjC_eq0 (negbTE chiHj) /= => -> // i1.
  by rewrite -cfdotC Cnat_ge0 // rpredM ?Cnat_cfdot_char ?cfInd_char ?irr_char.
rewrite cfResInd // cfdotZl mulf_eq0 cfdot_suml => /norP[_].
apply: contraR => chiGk'j; rewrite big1 // => x Gx; apply: contraNeq chiGk'j.
rewrite -conjg_IirrE cfdot_irr pnatr_eq0; case: (_ =P k) => // <- _.
by rewrite conjg_IirrE; apply/cfclassP; exists x.
Qed.

Lemma cfRes_Ind_invariant psi :
  H <| G -> G \subset 'I[psi] -> 'Res ('Ind[G, H] psi) = #|G : H|%:R *: psi.
Proof.
case/andP=> sHG _ /subsetP IGpsi; apply/cfun_inP=> x Hx.
rewrite cfResE ?cfIndE ?natf_indexg // cfunE -mulrA mulrCA; congr (_ * _).
by rewrite mulr_natl -sumr_const; apply: eq_bigr => y /IGpsi/inertia_valJ->.
Qed.

(* This is Isaacs, Corollary (6.7). *)
Corollary constt0_Res_cfker i : 
  H <| G -> 0 \in irr_constt ('Res[H] 'chi[G]_i) -> H \subset cfker 'chi[G]_i.
Proof.
move=> nsHG /(Clifford_Res_sum_cfclass nsHG); have [sHG nHG] := andP nsHG.
rewrite irr0 cfdot_Res_l cfclass1 // big_seq1 cfInd_cfun1 //.
rewrite cfdotZr conjC_nat => def_chiH.
apply/subsetP=> x Hx; rewrite cfkerEirr inE -!(cfResE _ sHG) //.
by rewrite def_chiH !cfunE cfun11 cfun1E Hx.
Qed.

(* This is Isaacs, Lemma (6.8). *)
Lemma dvdn_constt_Res1_irr1 i j : 
    H <| G -> j \in irr_constt ('Res[H, G] 'chi_i) ->
  exists n, 'chi_i 1%g = n%:R * 'chi_j 1%g.
Proof.
move=> nsHG chiHj; have [sHG nHG] := andP nsHG; rewrite -(cfResE _ sHG) //.
rewrite {1}(Clifford_Res_sum_cfclass nsHG chiHj) cfunE sum_cfunE.
have /CnatP[n ->]: '['Res[H] 'chi_i, 'chi_j] \in Cnat.
  by rewrite Cnat_cfdot_char ?cfRes_char ?irr_char.
exists (n * size ('chi_j ^: G)%CF)%N; rewrite natrM -mulrA; congr (_ * _).
rewrite mulr_natl -[size _]card_ord big_tnth -sumr_const; apply: eq_bigr => k _.
by have /cfclassP[y Gy ->]:=  mem_tnth k (in_tuple _); rewrite cfConjg1.
Qed.

Lemma cfclass_Ind phi psi :
  H <| G -> psi \in (phi ^: G)%CF -> 'Ind[G] phi = 'Ind[G] psi.
Proof.
move=> nsHG /cfclassP[y Gy ->]; have [sHG /subsetP nHG] := andP nsHG.
apply/cfun_inP=> x Hx; rewrite !cfIndE //; congr (_ * _).
rewrite (reindex_acts 'R _ (groupVr Gy)) ?astabsR //=.
by apply: eq_bigr => z Gz; rewrite conjgM cfConjgE ?nHG.
Qed.

End Inertia.

Arguments inertia {gT B%g} phi%CF.
Arguments cfclass {gT A%g} phi%CF B%g.
Arguments conjg_Iirr_inj {gT H} y [i1 i2] : rename.

Notation "''I[' phi ] " := (inertia phi) : group_scope.
Notation "''I[' phi ] " := (inertia_group phi) : Group_scope.
Notation "''I_' G [ phi ] " := (G%g :&: 'I[phi]) : group_scope.
Notation "''I_' G [ phi ] " := (G :&: 'I[phi])%G : Group_scope.
Notation "phi ^: G" := (cfclass phi G) : cfun_scope.

Section ConjRestrict.

Variables (gT : finGroupType) (G H K : {group gT}).

Lemma cfConjgRes_norm phi y :
  y \in 'N(K) -> y \in 'N(H) -> ('Res[K, H] phi ^ y)%CF = 'Res (phi ^ y)%CF.
Proof.
move=> nKy nHy; have [sKH | not_sKH] := boolP (K \subset H); last first.
  by rewrite !cfResEout // linearZ rmorph1 cfConjg1.
by apply/cfun_inP=> x Kx; rewrite !(cfConjgE, cfResE) ?memJ_norm ?groupV.
Qed.

Lemma cfConjgRes phi y :
  H <| G -> K <| G -> y \in G -> ('Res[K, H] phi ^ y)%CF = 'Res (phi ^ y)%CF.
Proof.
move=> /andP[_ nHG] /andP[_ nKG] Gy.
by rewrite cfConjgRes_norm ?(subsetP nHG) ?(subsetP nKG).
Qed.

Lemma sub_inertia_Res phi :
  G \subset 'N(K) -> 'I_G[phi] \subset 'I_G['Res[K, H] phi].
Proof.
move=> nKG; apply/subsetP=> y /setIP[Gy /setIdP[nHy /eqP Iphi_y]].
by rewrite 2!inE Gy cfConjgRes_norm ?(subsetP nKG) ?Iphi_y /=.
Qed.

Lemma cfConjgInd_norm phi y :
  y \in 'N(K) -> y \in 'N(H) -> ('Ind[H, K] phi ^ y)%CF = 'Ind (phi ^ y)%CF.
Proof.
move=> nKy nHy; have [sKH | not_sKH] := boolP (K \subset H).
  by rewrite !cfConjgEin (cfIndIsom (norm_conj_isom nHy)).
rewrite !cfIndEout // linearZ -(cfConjg_iso y) rmorph1 /=; congr (_ *: _).
by rewrite cfConjg_cfuni ?norm1 ?inE.
Qed.

Lemma cfConjgInd phi y :
  H <| G -> K <| G -> y \in G -> ('Ind[H, K] phi ^ y)%CF = 'Ind (phi ^ y)%CF.
Proof.
move=> /andP[_ nHG] /andP[_ nKG] Gy.
by rewrite cfConjgInd_norm ?(subsetP nHG) ?(subsetP nKG).
Qed.

Lemma sub_inertia_Ind phi :
  G \subset 'N(H) -> 'I_G[phi] \subset 'I_G['Ind[H, K] phi].
Proof.
move=> nHG; apply/subsetP=> y /setIP[Gy /setIdP[nKy /eqP Iphi_y]].
by rewrite 2!inE Gy cfConjgInd_norm ?(subsetP nHG) ?Iphi_y /=.
Qed.

End ConjRestrict.

Section MoreInertia.

Variables (gT : finGroupType) (G H : {group gT}) (i : Iirr H).
Let T := 'I_G['chi_i].

Lemma inertia_id : 'I_T['chi_i] = T. Proof. by rewrite -setIA setIid. Qed.

Lemma cfclass_inertia : ('chi[H]_i ^: T)%CF = [:: 'chi_i].
Proof.
rewrite /cfclass inertia_id rcosets_id /(image _ _) enum_set1 /=.
by rewrite repr_group cfConjgJ1.
Qed.

End MoreInertia.

Section ConjMorph.

Variables (aT rT : finGroupType) (D G H : {group aT}) (f : {morphism D >-> rT}).

Lemma cfConjgMorph (phi : 'CF(f @* H)) y :
  y \in D -> y \in 'N(H) -> (cfMorph phi ^ y)%CF = cfMorph (phi ^ f y).
Proof.
move=> Dy nHy; have [sHD | not_sHD] := boolP (H \subset D); last first.
  by rewrite !cfMorphEout // linearZ rmorph1 cfConjg1.
apply/cfun_inP=> x Gx; rewrite !(cfConjgE, cfMorphE) ?memJ_norm ?groupV //.
  by rewrite morphJ ?morphV ?groupV // (subsetP sHD).
by rewrite (subsetP (morphim_norm _ _)) ?mem_morphim.
Qed.

Lemma inertia_morph_pre (phi : 'CF(f @* H)) :
  H <| G -> G \subset D -> 'I_G[cfMorph phi] = G :&: f @*^-1 'I_(f @* G)[phi].
Proof.
case/andP=> sHG nHG sGD; have sHD := subset_trans sHG sGD.
apply/setP=> y; rewrite !in_setI; apply: andb_id2l => Gy.
have [Dy nHy] := (subsetP sGD y Gy, subsetP nHG y Gy).
rewrite Dy inE nHy 4!inE mem_morphim // -morphimJ ?(normP nHy) // subxx /=.
rewrite cfConjgMorph //; apply/eqP/eqP=> [Iphi_y | -> //].
by apply/cfun_inP=> _ /morphimP[x Dx Hx ->]; rewrite -!cfMorphE ?Iphi_y.
Qed.

Lemma inertia_morph_im (phi : 'CF(f @* H)) :
  H <| G -> G \subset D -> f @* 'I_G[cfMorph phi] = 'I_(f @* G)[phi].
Proof.
move=> nsHG sGD; rewrite inertia_morph_pre // morphim_setIpre.
by rewrite (setIidPr _) ?Inertia_sub.
Qed.

Variables (R S : {group rT}).
Variables (g : {morphism G >-> rT}) (h : {morphism H >-> rT}).
Hypotheses (isoG : isom G R g) (isoH : isom H S h).
Hypotheses (eq_hg : {in H, h =1 g}) (sHG : H \subset G).

(* This does not depend on the (isoG : isom G R g) assumption. *)
Lemma cfConjgIsom phi y :
  y \in G -> y \in 'N(H) -> (cfIsom isoH phi ^ g y)%CF = cfIsom isoH (phi ^ y).
Proof.
move=> Gy nHy; have [_ defS] := isomP isoH.
rewrite morphimEdom (eq_in_imset eq_hg) -morphimEsub // in defS.
apply/cfun_inP=> gx; rewrite -{1}defS => /morphimP[x Gx Hx ->] {gx}.
rewrite cfConjgE; last by rewrite -defS inE -morphimJ ?(normP nHy).
by rewrite -morphV -?morphJ -?eq_hg ?cfIsomE ?cfConjgE ?memJ_norm ?groupV.
Qed.

Lemma inertia_isom phi : 'I_R[cfIsom isoH phi] = g @* 'I_G[phi].
Proof.
have [[_ defS] [injg <-]] := (isomP isoH, isomP isoG).
rewrite morphimEdom (eq_in_imset eq_hg) -morphimEsub // in defS.
rewrite /inertia !setIdE morphimIdom setIA -{1}defS -injm_norm ?injmI //.
apply/setP=> gy; rewrite !inE; apply: andb_id2l => /morphimP[y Gy nHy ->] {gy}.
rewrite cfConjgIsom // -sub1set -morphim_set1 // injmSK ?sub1set //= inE.
apply/eqP/eqP=> [Iphi_y | -> //].
by apply/cfun_inP=> x Hx; rewrite -!(cfIsomE isoH) ?Iphi_y.
Qed.

End ConjMorph.

Section ConjQuotient.

Variables gT : finGroupType.
Implicit Types G H K : {group gT}.

Lemma cfConjgMod_norm H K (phi : 'CF(H / K)) y :
  y \in 'N(K) -> y \in 'N(H) -> ((phi %% K) ^ y)%CF = (phi ^ coset K y %% K)%CF.
Proof. exact: cfConjgMorph. Qed.

Lemma cfConjgMod G H K (phi : 'CF(H / K)) y :
    H <| G -> K <| G -> y \in G ->
  ((phi %% K) ^ y)%CF = (phi ^ coset K y %% K)%CF.
Proof.
move=> /andP[_ nHG] /andP[_ nKG] Gy.
by rewrite cfConjgMod_norm ?(subsetP nHG) ?(subsetP nKG).
Qed.

Lemma cfConjgQuo_norm H K (phi : 'CF(H)) y :
  y \in 'N(K) -> y \in 'N(H) -> ((phi / K) ^ coset K y)%CF = (phi ^ y / K)%CF.
Proof.
move=> nKy nHy; have keryK: (K \subset cfker (phi ^ y)) = (K \subset cfker phi).
  by rewrite cfker_conjg // -{1}(normP nKy) conjSg.
have [kerK | not_kerK] := boolP (K \subset cfker phi); last first.
  by rewrite !cfQuoEout ?linearZ ?rmorph1 ?cfConjg1 ?keryK.
apply/cfun_inP=> _ /morphimP[x nKx Hx ->].
have nHyb: coset K y \in 'N(H / K) by rewrite inE -morphimJ ?(normP nHy).
rewrite !(cfConjgE, cfQuoEnorm) ?keryK // ?in_setI ?Hx //.
rewrite -morphV -?morphJ ?groupV // cfQuoEnorm //.
by rewrite inE memJ_norm ?Hx ?groupJ ?groupV.
Qed.

Lemma cfConjgQuo G H K (phi : 'CF(H)) y :
    H <| G -> K <| G -> y \in G ->
  ((phi / K) ^ coset K y)%CF = (phi ^ y / K)%CF.
Proof.
move=> /andP[_ nHG] /andP[_ nKG] Gy.
by rewrite cfConjgQuo_norm ?(subsetP nHG) ?(subsetP nKG).
Qed.

Lemma inertia_mod_pre G H K (phi : 'CF(H / K)) :
  H <| G -> K <| G -> 'I_G[phi %% K] = G :&: coset K @*^-1 'I_(G / K)[phi].
Proof. by move=> nsHG /andP[_]; apply: inertia_morph_pre. Qed.

Lemma inertia_mod_quo G H K (phi : 'CF(H / K)) :
  H <| G -> K <| G -> ('I_G[phi %% K] / K)%g = 'I_(G / K)[phi].
Proof. by move=> nsHG /andP[_]; apply: inertia_morph_im. Qed.

Lemma inertia_quo G H K (phi : 'CF(H)) :
    H <| G -> K <| G -> K \subset cfker phi ->
  'I_(G / K)[phi / K] = ('I_G[phi] / K)%g.
Proof.
move=> nsHG nsKG kerK; rewrite -inertia_mod_quo ?cfQuoK //.
by rewrite (normalS _ (normal_sub nsHG)) // (subset_trans _ (cfker_sub phi)).
Qed.

End ConjQuotient.

Section InertiaSdprod.

Variables (gT : finGroupType) (K H G : {group gT}).

Hypothesis defG : K ><| H = G.

Lemma cfConjgSdprod phi y :
    y \in 'N(K) -> y \in 'N(H) ->
  (cfSdprod defG phi ^ y = cfSdprod defG (phi ^ y))%CF.
Proof.
move=> nKy nHy.
have nGy: y \in 'N(G) by rewrite -sub1set -(sdprodW defG) normsM ?sub1set.
rewrite -{2}[phi](cfSdprodK defG) cfConjgRes_norm // cfRes_sdprodK //.
by rewrite cfker_conjg // -{1}(normP nKy) conjSg cfker_sdprod.
Qed.

Lemma inertia_sdprod (L : {group gT}) phi :
  L \subset 'N(K) -> L \subset 'N(H) -> 'I_L[cfSdprod defG phi] = 'I_L[phi].
Proof.
move=> nKL nHL; have nGL: L \subset 'N(G) by rewrite -(sdprodW defG) normsM.
apply/setP=> z; rewrite !in_setI ![z \in 'I[_]]inE; apply: andb_id2l => Lz.
rewrite cfConjgSdprod ?(subsetP nKL) ?(subsetP nHL) ?(subsetP nGL) //=.
by rewrite (can_eq (cfSdprodK defG)).
Qed.

End InertiaSdprod.

Section InertiaDprod.

Variables (gT : finGroupType) (G K H : {group gT}).
Implicit Type L : {group gT}.
Hypothesis KxH : K \x H = G.

Lemma cfConjgDprodl phi y :
    y \in 'N(K) -> y \in 'N(H) ->
  (cfDprodl KxH phi ^ y = cfDprodl KxH (phi ^ y))%CF.
Proof. by move=> nKy nHy; apply: cfConjgSdprod. Qed.

Lemma cfConjgDprodr psi y :
    y \in 'N(K) -> y \in 'N(H) ->
  (cfDprodr KxH psi ^ y = cfDprodr KxH (psi ^ y))%CF.
Proof. by move=> nKy nHy; apply: cfConjgSdprod. Qed.

Lemma cfConjgDprod phi psi y :
    y \in 'N(K) -> y \in 'N(H) ->
  (cfDprod KxH phi psi ^ y = cfDprod KxH (phi ^ y) (psi ^ y))%CF.
Proof. by move=> nKy nHy; rewrite rmorphM /= cfConjgDprodl ?cfConjgDprodr. Qed.

Lemma inertia_dprodl L phi :
  L \subset 'N(K) -> L \subset 'N(H) -> 'I_L[cfDprodl KxH phi] = 'I_L[phi].
Proof. by move=> nKL nHL; apply: inertia_sdprod. Qed.

Lemma inertia_dprodr L psi :
  L \subset 'N(K) -> L \subset 'N(H) -> 'I_L[cfDprodr KxH psi] = 'I_L[psi].
Proof. by move=> nKL nHL; apply: inertia_sdprod. Qed.

Lemma inertia_dprod L (phi : 'CF(K)) (psi : 'CF(H)) :
    L \subset 'N(K) -> L \subset 'N(H) -> phi 1%g != 0 -> psi 1%g != 0 -> 
  'I_L[cfDprod KxH phi psi] = 'I_L[phi] :&: 'I_L[psi].
Proof.
move=> nKL nHL nz_phi nz_psi; apply/eqP; rewrite eqEsubset subsetI.
rewrite -{1}(inertia_scale_nz psi nz_phi) -{1}(inertia_scale_nz phi nz_psi).
rewrite -(cfDprod_Resl KxH) -(cfDprod_Resr KxH) !sub_inertia_Res //=.
by rewrite -inertia_dprodl -?inertia_dprodr // -setIIr setIS ?inertia_mul.
Qed.

Lemma inertia_dprod_irr L i j :
    L \subset 'N(K) -> L \subset 'N(H) ->
  'I_L[cfDprod KxH 'chi_i 'chi_j] = 'I_L['chi_i] :&: 'I_L['chi_j].
Proof. by move=> nKL nHL; rewrite inertia_dprod ?irr1_neq0. Qed.

End InertiaDprod.

Section InertiaBigdprod.

Variables (gT : finGroupType) (I : finType) (P : pred I).
Variables (A : I -> {group gT}) (G : {group gT}).
Implicit Type L : {group gT}.
Hypothesis defG : \big[dprod/1%g]_(i | P i) A i = G.

Section ConjBig.

Variable y : gT.
Hypothesis nAy: forall i, P i -> y \in 'N(A i).

Lemma cfConjgBigdprodi i (phi : 'CF(A i)) :
   (cfBigdprodi defG phi ^ y = cfBigdprodi defG (phi ^ y))%CF.
Proof.
rewrite cfConjgDprodl; try by case: ifP => [/nAy// | _]; rewrite norm1 inE.
  congr (cfDprodl _ _); case: ifP => [Pi | _].
    by rewrite cfConjgRes_norm ?nAy.
  by apply/cfun_inP=> _ /set1P->; rewrite !(cfRes1, cfConjg1).
rewrite -sub1set norms_gen ?norms_bigcup // sub1set.
by apply/bigcapP=> j /andP[/nAy].
Qed.

Lemma cfConjgBigdprod phi :
  (cfBigdprod defG phi ^ y = cfBigdprod defG (fun i => phi i ^ y))%CF.
Proof.
by rewrite rmorph_prod /=; apply: eq_bigr => i _; apply: cfConjgBigdprodi.
Qed.

End ConjBig.

Section InertiaBig.

Variable L : {group gT}.
Hypothesis nAL : forall i, P i -> L \subset 'N(A i).

Lemma inertia_bigdprodi i (phi : 'CF(A i)) :
  P i -> 'I_L[cfBigdprodi defG phi] = 'I_L[phi].
Proof.
move=> Pi; rewrite inertia_dprodl ?Pi ?cfRes_id ?nAL //.
by apply/norms_gen/norms_bigcup/bigcapsP=> j /andP[/nAL].
Qed.

Lemma inertia_bigdprod phi (Phi := cfBigdprod defG phi) :
  Phi 1%g != 0 -> 'I_L[Phi] = L :&: \bigcap_(i | P i) 'I_L[phi i].
Proof.
move=> nz_Phi; apply/eqP; rewrite eqEsubset; apply/andP; split.
  rewrite subsetI Inertia_sub; apply/bigcapsP=> i Pi.
  have [] := cfBigdprodK nz_Phi Pi; move: (_ / _) => a nz_a <-.
  by rewrite inertia_scale_nz ?sub_inertia_Res //= ?nAL.
rewrite subsetI subsetIl; apply: subset_trans (inertia_prod _ _ _).
apply: setISS.
  by rewrite -(bigdprodWY defG) norms_gen ?norms_bigcup //; apply/bigcapsP.
apply/bigcapsP=> i Pi; rewrite (bigcap_min i) //.
by rewrite -inertia_bigdprodi ?subsetIr.
Qed.

Lemma inertia_bigdprod_irr Iphi (phi := fun i => 'chi_(Iphi i)) :
  'I_L[cfBigdprod defG phi] = L :&: \bigcap_(i | P i) 'I_L[phi i].
Proof.
rewrite inertia_bigdprod // -[cfBigdprod _ _]cfIirrE ?irr1_neq0 //.
by apply: cfBigdprod_irr => i _; apply: mem_irr.
Qed.

End InertiaBig.

End InertiaBigdprod.

Section ConsttInertiaBijection.

Variables (gT : finGroupType) (H G : {group gT}) (t : Iirr H).
Hypothesis nsHG : H <| G.

Local Notation theta := 'chi_t.
Local Notation T := 'I_G[theta]%G.
Local Notation "` 'T'" := 'I_(gval G)[theta]
  (at level 0, format "` 'T'") : group_scope.

Let calA := irr_constt ('Ind[T] theta).
Let calB := irr_constt ('Ind[G] theta).
Local Notation AtoB := (Ind_Iirr G).

(* This is Isaacs, Theorem (6.11). *)
Theorem constt_Inertia_bijection :
 [/\ (*a*) {in calA, forall s, 'Ind[G] 'chi_s \in irr G},
     (*b*) {in calA &, injective (Ind_Iirr G)},
           Ind_Iirr G @: calA =i calB,
     (*c*) {in calA, forall s (psi := 'chi_s) (chi := 'Ind[G] psi),
             [predI irr_constt ('Res chi) & calA] =i pred1 s}
   & (*d*) {in calA, forall s (psi := 'chi_s) (chi := 'Ind[G] psi),
             '['Res psi, theta] = '['Res chi, theta]}].
Proof.
have [sHG sTG]: H \subset G /\ T \subset G by rewrite subsetIl normal_sub.
have nsHT : H <| T := normal_Inertia theta sHG; have sHT := normal_sub nsHT.
have AtoB_P s (psi := 'chi_s) (chi := 'Ind[G] psi): s \in calA ->
  [/\ chi \in irr G, AtoB s \in calB & '['Res psi, theta] = '['Res chi, theta]].
- rewrite !constt_Ind_Res => sHt; have [r sGr] := constt_cfInd_irr s sTG.
  have rTs: s \in irr_constt ('Res[T] 'chi_r) by rewrite -constt_Ind_Res.
  have NrT: 'Res[T] 'chi_r \is a character by rewrite cfRes_char ?irr_char.
  have rHt: t \in irr_constt ('Res[H] 'chi_r).
    by have:= constt_Res_trans NrT rTs sHt; rewrite cfResRes.
  pose e := '['Res[H] 'chi_r, theta]; set f := '['Res[H] psi, theta].
  have DrH: 'Res[H] 'chi_r = e *: \sum_(xi <- (theta ^: G)%CF) xi.
    exact: Clifford_Res_sum_cfclass.
  have DpsiH: 'Res[H] psi = f *: theta.
    rewrite (Clifford_Res_sum_cfclass nsHT sHt).
    by rewrite cfclass_invariant ?subsetIr ?big_seq1.
  have ub_chi_r: 'chi_r 1%g <= chi 1%g ?= iff ('chi_r == chi).
    have Nchi: chi \is a character by rewrite cfInd_char ?irr_char.
    have [chi1 Nchi1->] := constt_charP _ Nchi sGr.
    rewrite addrC cfunE -lerif_subLR subrr eq_sym -subr_eq0 addrK.
    by split; rewrite ?char1_ge0 // eq_sym char1_eq0.
  have lb_chi_r: chi 1%g <= 'chi_r 1%g ?= iff (f == e).
    rewrite cfInd1 // -(cfRes1 H) DpsiH -(cfRes1 H 'chi_r) DrH !cfunE sum_cfunE.
    rewrite (eq_big_seq (fun _ => theta 1%g)) => [|i]; last first.
      by case/cfclassP=> y _ ->; rewrite cfConjg1.
    rewrite reindex_cfclass //= sumr_const -(eq_card (cfclass_IirrE _ _)).
    rewrite mulr_natl mulrnAr card_cfclass_Iirr //.
    rewrite (mono_lerif (ler_pmuln2r (indexg_gt0 G T))).
    rewrite (mono_lerif (ler_pmul2r (irr1_gt0 t))); apply: lerif_eq.
    by rewrite /e -(cfResRes _ sHT) ?cfdot_Res_ge_constt.
  have [_ /esym] := lerif_trans ub_chi_r lb_chi_r; rewrite eqxx.
  by case/andP=> /eqP Dchi /eqP->; rewrite cfIirrE -/chi -?Dchi ?mem_irr.
have part_c: {in calA, forall s (chi := 'Ind[G] 'chi_s),
  [predI irr_constt ('Res[T] chi) & calA] =i pred1 s}.
- move=> s As chi s1; have [irr_chi _ /eqP Dchi_theta] := AtoB_P s As.
  have chiTs: s \in irr_constt ('Res[T] chi).
    by rewrite irr_consttE cfdot_Res_l irrWnorm ?oner_eq0.
  apply/andP/eqP=> [[/= chiTs1 As1] | -> //].
  apply: contraTeq Dchi_theta => s's1; rewrite ltr_eqF // -/chi.
  have [|phi Nphi DchiT] := constt_charP _ _ chiTs.
    by rewrite cfRes_char ?cfInd_char ?irr_char.
  have [|phi1 Nphi1 Dphi] := constt_charP s1 Nphi _.
    rewrite irr_consttE -(canLR (addKr _) DchiT) addrC cfdotBl cfdot_irr.
    by rewrite mulrb ifN_eqC ?subr0.
  rewrite -(cfResRes chi sHT sTG) DchiT Dphi !rmorphD !cfdotDl /=.
  rewrite -ltr_subl_addl subrr ltr_paddr ?ltr_def //;
    rewrite Cnat_ge0 ?Cnat_cfdot_char ?cfRes_char ?irr_char //.
  by rewrite andbT -irr_consttE -constt_Ind_Res.
do [split=> //; try by move=> s /AtoB_P[]] => [s1 s2 As1 As2 | r].
  have [[irr_s1G _ _] [irr_s2G _ _]] := (AtoB_P _ As1, AtoB_P _ As2).
  move/(congr1 (tnth (irr G))); rewrite !cfIirrE // => eq_s12_G.
  apply/eqP; rewrite -[_ == _]part_c // inE /= As1 -eq_s12_G.
  by rewrite -As1 [_ && _]part_c // inE /=.
apply/imsetP/idP=> [[s /AtoB_P[_ BsG _] -> //] | Br].
have /exists_inP[s rTs As]: [exists s in irr_constt ('Res 'chi_r), s \in calA].
  rewrite -negb_forall_in; apply: contra Br => /eqfun_inP => o_tT_rT.
  rewrite -(cfIndInd _ sTG sHT) -cfdot_Res_r ['Res _]cfun_sum_constt.
  by rewrite cfdot_sumr big1 // => i rTi; rewrite cfdotZr o_tT_rT ?mulr0.
exists s => //; have [/irrP[r1 DsG] _ _] := AtoB_P s As.
by apply/eqP; rewrite /AtoB -constt_Ind_Res DsG irrK constt_irr in rTs *.
Qed.

End ConsttInertiaBijection.

Section ExtendInvariantIrr.

Variable gT : finGroupType.
Implicit Types G H K L M N : {group gT}.

Section ConsttIndExtendible.

Variables (G N : {group gT}) (t : Iirr N) (c : Iirr G).
Let theta := 'chi_t.
Let chi := 'chi_c.

Definition mul_Iirr b := cfIirr ('chi_b * chi).
Definition mul_mod_Iirr (b : Iirr (G / N)) := mul_Iirr (mod_Iirr b).

Hypotheses (nsNG : N <| G) (cNt : 'Res[N] chi = theta).
Let sNG : N \subset G. Proof. exact: normal_sub. Qed.
Let nNG : G \subset 'N(N). Proof. exact: normal_norm. Qed.

Lemma extendible_irr_invariant : G \subset 'I[theta].
Proof.
apply/subsetP=> y Gy; have nNy := subsetP nNG y Gy.
rewrite inE nNy; apply/eqP/cfun_inP=> x Nx; rewrite cfConjgE // -cNt.
by rewrite !cfResE ?memJ_norm ?cfunJ ?groupV.
Qed.
Let IGtheta := extendible_irr_invariant.

(* This is Isaacs, Theorem (6.16) *)
Theorem constt_Ind_mul_ext f (phi := 'chi_f) (psi := phi * theta) :
  G \subset 'I[phi] -> psi \in irr N ->
  let calS := irr_constt ('Ind phi) in
  [/\ {in calS, forall b, 'chi_b * chi \in irr G},
      {in calS &, injective mul_Iirr},
      irr_constt ('Ind psi) =i [seq mul_Iirr b | b in calS]
    & 'Ind psi = \sum_(b in calS) '['Ind phi, 'chi_b] *: 'chi_(mul_Iirr b)].
Proof.
move=> IGphi irr_psi calS.
have IGpsi: G \subset 'I[psi].
  by rewrite (subset_trans _ (inertia_mul _ _)) // subsetI IGphi.
pose e b := '['Ind[G] phi, 'chi_b]; pose d b g := '['chi_b * chi, 'chi_g * chi].
have Ne b: e b \in Cnat by rewrite Cnat_cfdot_char ?cfInd_char ?irr_char.
have egt0 b: b \in calS -> e b > 0 by rewrite Cnat_gt0.
have DphiG: 'Ind phi = \sum_(b in calS) e b *: 'chi_b := cfun_sum_constt _.
have DpsiG: 'Ind psi = \sum_(b in calS) e b *: 'chi_b * chi.
  by rewrite /psi -cNt cfIndM // DphiG mulr_suml.
pose d_delta := [forall b in calS, forall g in calS, d b g == (b == g)%:R].
have charMchi b: 'chi_b * chi \is a character by rewrite rpredM ?irr_char.
have [_]: '['Ind[G] phi] <= '['Ind[G] psi] ?= iff d_delta.
  pose sum_delta := \sum_(b in calS) e b * \sum_(g in calS) e g * (b == g)%:R.
  pose sum_d := \sum_(b in calS) e b * \sum_(g in calS) e g * d b g.
  have ->: '['Ind[G] phi] = sum_delta.
    rewrite DphiG cfdot_suml; apply: eq_bigr => b _; rewrite cfdotZl cfdot_sumr.
    by congr (_ * _); apply: eq_bigr => g; rewrite cfdotZr cfdot_irr conj_Cnat.
  have ->: '['Ind[G] psi] = sum_d.
    rewrite DpsiG cfdot_suml; apply: eq_bigr => b _.
    rewrite -scalerAl cfdotZl cfdot_sumr; congr (_ * _).
    by apply: eq_bigr => g _; rewrite -scalerAl cfdotZr conj_Cnat.
  have eMmono := mono_lerif (ler_pmul2l (egt0 _ _)).
  apply: lerif_sum => b /eMmono->; apply: lerif_sum => g /eMmono->.
  split; last exact: eq_sym.
  have /CnatP[n Dd]: d b g \in Cnat by rewrite Cnat_cfdot_char.
  have [Db | _] := eqP; rewrite Dd leC_nat // -ltC_nat -Dd Db cfnorm_gt0.
  by rewrite -char1_eq0 // cfunE mulf_neq0 ?irr1_neq0.
rewrite -!cfdot_Res_l ?cfRes_Ind_invariant // !cfdotZl cfnorm_irr irrWnorm //.
rewrite eqxx => /esym/forall_inP/(_ _ _)/eqfun_inP; rewrite /d /= => Dd.
have irrMchi: {in calS, forall b, 'chi_b * chi \in irr G}.
  by move=> b Sb; rewrite /= irrEchar charMchi Dd ?eqxx.
have injMchi: {in calS &, injective mul_Iirr}.
  move=> b g Sb Sg /(congr1 (fun s => '['chi_s, 'chi_(mul_Iirr g)]))/eqP.
  by rewrite cfnorm_irr !cfIirrE ?irrMchi ?Dd // pnatr_eq1; case: (b =P g).
have{DpsiG} ->: 'Ind psi = \sum_(b in calS) e b *: 'chi_(mul_Iirr b).
  by rewrite DpsiG; apply: eq_bigr => b Sb; rewrite -scalerAl cfIirrE ?irrMchi.
split=> // i; rewrite irr_consttE cfdot_suml;
apply/idP/idP=> [|/imageP[b Sb ->]].
  apply: contraR => N'i; rewrite big1 // => b Sb.
  rewrite cfdotZl cfdot_irr mulrb ifN_eqC ?mulr0 //.
  by apply: contraNneq N'i => ->; apply: image_f.
rewrite gtr_eqF // (bigD1 b) //= cfdotZl cfnorm_irr mulr1 ltr_paddr ?egt0 //.
apply: sumr_ge0 => g /andP[Sg _]; rewrite cfdotZl cfdot_irr.
by rewrite mulr_ge0 ?ler0n ?Cnat_ge0.
Qed.
  
(* This is Isaacs, Corollary (6.17) (due to Gallagher). *)
Corollary constt_Ind_ext :
  [/\ forall b : Iirr (G / N), 'chi_(mod_Iirr b) * chi \in irr G,
      injective mul_mod_Iirr,
      irr_constt ('Ind theta) =i codom mul_mod_Iirr
    & 'Ind theta = \sum_b 'chi_b 1%g *: 'chi_(mul_mod_Iirr b)].
Proof.
have IHchi0: G \subset 'I['chi[N]_0] by rewrite inertia_irr0.
have [] := constt_Ind_mul_ext IHchi0; rewrite irr0 ?mul1r ?mem_irr //.
set psiG := 'Ind 1 => irrMchi injMchi constt_theta {2}->.
have dot_psiG b: '[psiG, 'chi_(mod_Iirr b)] = 'chi[G / N]_b 1%g.
  rewrite mod_IirrE // -cfdot_Res_r cfRes_sub_ker ?cfker_mod //.
  by rewrite cfdotZr cfnorm1 mulr1 conj_Cnat ?cfMod1 ?Cnat_irr1.
have mem_psiG (b : Iirr (G / N)): mod_Iirr b \in irr_constt psiG.
  by rewrite irr_consttE dot_psiG irr1_neq0.
have constt_psiG b: (b \in irr_constt psiG) = (N \subset cfker 'chi_b).
  apply/idP/idP=> [psiGb | /quo_IirrK <- //].
  by rewrite constt0_Res_cfker // -constt_Ind_Res irr0.
split=> [b | b g /injMchi/(can_inj (mod_IirrK nsNG))-> // | b0 | ].
- exact: irrMchi.
- rewrite constt_theta.
  apply/imageP/imageP=> [][b psiGb ->]; last by exists (mod_Iirr b).
  by exists (quo_Iirr N b) => //; rewrite /mul_mod_Iirr quo_IirrK -?constt_psiG.
rewrite (reindex_onto _ _ (in1W (mod_IirrK nsNG))) /=.
apply/esym/eq_big => b; first by rewrite constt_psiG quo_IirrKeq.
by rewrite -dot_psiG /mul_mod_Iirr => /eqP->.
Qed.

End ConsttIndExtendible.

(* This is Isaacs, Theorem (6.19). *)
Theorem invariant_chief_irr_cases G K L s (theta := 'chi[K]_s) :
    chief_factor G L K -> abelian (K / L) -> G \subset 'I[theta] ->
  let t := #|K : L| in
  [\/ 'Res[L] theta \in irr L,
      exists2 e, exists p, 'Res[L] theta = e%:R *: 'chi_p & (e ^ 2)%N = t
   |  exists2 p, injective p & 'Res[L] theta = \sum_(i < t) 'chi_(p i)].
Proof.
case/andP=> /maxgroupP[/andP[ltLK nLG] maxL] nsKG abKbar IGtheta t.
have [sKG nKG] := andP nsKG; have sLG := subset_trans (proper_sub ltLK) sKG.
have nsLG: L <| G by apply/andP.
have nsLK := normalS (proper_sub ltLK) sKG nsLG; have [sLK nLK] := andP nsLK.
have [p0 sLp0] := constt_cfRes_irr L s; rewrite -/theta in sLp0.
pose phi := 'chi_p0; pose T := 'I_G[phi].
have sTG: T \subset G := subsetIl G _.
have /eqP mulKT: (K * T)%g == G.
  rewrite eqEcard mulG_subG sKG sTG -LagrangeMr -indexgI -(Lagrange sTG) /= -/T.
  rewrite mulnC leq_mul // setIA (setIidPl sKG) -!size_cfclass // -/phi.
  rewrite uniq_leq_size ?cfclass_uniq // => _ /cfclassP[x Gx ->].
  have: conjg_Iirr p0 x \in irr_constt ('Res theta).
    have /inertiaJ <-: x \in 'I[theta] := subsetP IGtheta x Gx.
    by rewrite -(cfConjgRes _ nsKG) // irr_consttE conjg_IirrE // cfConjg_iso.
  apply: contraR; rewrite -conjg_IirrE // => not_sLp0x.
  rewrite (Clifford_Res_sum_cfclass nsLK sLp0) cfdotZl cfdot_suml.
  rewrite big1_seq ?mulr0 // => _ /cfclassP[y Ky ->]; rewrite -conjg_IirrE //.
  rewrite cfdot_irr mulrb ifN_eq ?(contraNneq _ not_sLp0x) // => <-.
  by rewrite conjg_IirrE //; apply/cfclassP; exists y.
have nsKT_G: K :&: T <| G.
  rewrite /normal subIset ?sKG // -mulKT setIA (setIidPl sKG) mulG_subG.
  rewrite normsIG // sub_der1_norm ?subsetIl //.
  exact: subset_trans (der1_min nLK abKbar) (sub_Inertia _ sLK).
have [e DthL]: exists e, 'Res theta = e%:R *: \sum_(xi <- (phi ^: K)%CF) xi.
  rewrite (Clifford_Res_sum_cfclass nsLK sLp0) -/phi; set e := '[_, _].
  by exists (truncC e); rewrite truncCK ?Cnat_cfdot_char ?cfRes_char ?irr_char.
have [defKT | ltKT_K] := eqVneq (K :&: T) K; last first.
  have defKT: K :&: T = L.
    apply: maxL; last by rewrite subsetI sLK sub_Inertia.
    by rewrite normal_norm // properEneq ltKT_K subsetIl.
  have t_cast: size (phi ^: K)%CF = t.
    by rewrite size_cfclass //= -{2}(setIidPl sKG) -setIA defKT.
  pose phiKt := Tuple (introT eqP t_cast); pose p i := cfIirr (tnth phiKt i).
  have pK i: 'chi_(p i) = (phi ^: K)%CF`_i.
    rewrite cfIirrE; first by rewrite (tnth_nth 0).
    by have /cfclassP[y _ ->] := mem_tnth i phiKt; rewrite cfConjg_irr ?mem_irr.
  constructor 3; exists p => [i j /(congr1 (tnth (irr L)))/eqP| ].
    by apply: contraTeq; rewrite !pK !nth_uniq ?t_cast ?cfclass_uniq.
  have{DthL} DthL: 'Res theta = e%:R *: \sum_(i < t) (phi ^: K)%CF`_i.
    by rewrite DthL (big_nth 0) big_mkord t_cast.
  suffices /eqP e1: e == 1%N by rewrite DthL e1 scale1r; apply: eq_bigr.
  have Dth1: theta 1%g = e%:R * t%:R * phi 1%g.
    rewrite -[t]card_ord -mulrA -(cfRes1 L) DthL cfunE; congr (_ * _).
    rewrite mulr_natl -sumr_const sum_cfunE -t_cast; apply: eq_bigr => i _.
    by have /cfclassP[y _ ->] := mem_nth 0 (valP i); rewrite cfConjg1.
  rewrite eqn_leq lt0n (contraNneq _ (irr1_neq0 s)); last first.
    by rewrite Dth1 => ->; rewrite !mul0r.
  rewrite -leC_nat -(ler_pmul2r (gt0CiG K L)) -/t -(ler_pmul2r (irr1_gt0 p0)).
  rewrite mul1r -Dth1 -cfInd1 //.
  by rewrite char1_ge_constt ?cfInd_char ?irr_char ?constt_Ind_Res.
have IKphi: 'I_K[phi] = K by rewrite -{1}(setIidPl sKG) -setIA.
have{DthL} DthL: 'Res[L] theta = e%:R *: phi.
  by rewrite DthL -[rhs in (_ ^: rhs)%CF]IKphi cfclass_inertia big_seq1.
pose mmLth := @mul_mod_Iirr K L s.
have linKbar := char_abelianP _ abKbar.
have LmodL i: ('chi_i %% L)%CF \is a linear_char := cfMod_lin_char (linKbar i).
have mmLthE i: 'chi_(mmLth i) = ('chi_i %% L)%CF * theta.
  by rewrite cfIirrE ?mod_IirrE // mul_lin_irr ?mem_irr.
have mmLthL i: 'Res[L] 'chi_(mmLth i) = 'Res[L] theta.
  rewrite mmLthE rmorphM /= cfRes_sub_ker ?cfker_mod ?lin_char1 //.
  by rewrite scale1r mul1r.
have [inj_Mphi | /injectivePn[i [j i'j eq_mm_ij]]] := boolP (injectiveb mmLth).
  suffices /eqP e1: e == 1%N by constructor 1; rewrite DthL e1 scale1r mem_irr.
  rewrite eqn_leq lt0n (contraNneq _ (irr1_neq0 s)); last first.
    by rewrite -(cfRes1 L) DthL cfunE => ->; rewrite !mul0r.
  rewrite -leq_sqr -leC_nat natrX -(ler_pmul2r (irr1_gt0 p0)) -mulrA mul1r.
  have ->: e%:R * 'chi_p0 1%g = 'Res[L] theta 1%g by rewrite DthL cfunE.
  rewrite cfRes1 -(ler_pmul2l (gt0CiG K L)) -cfInd1 // -/phi.
  rewrite -card_quotient // -card_Iirr_abelian // mulr_natl.
  rewrite ['Ind phi]cfun_sum_cfdot sum_cfunE (bigID (mem (codom mmLth))) /=.
  rewrite ler_paddr ?sumr_ge0 // => [i _|].
    by rewrite char1_ge0 ?rpredZ_Cnat ?Cnat_cfdot_char ?cfInd_char ?irr_char.
  rewrite -big_uniq //= big_map big_filter -sumr_const ler_sum // => i _.
  rewrite cfunE -[in rhs in _ <= rhs](cfRes1 L) -cfdot_Res_r mmLthL cfRes1.
  by rewrite DthL cfdotZr rmorph_nat cfnorm_irr mulr1.
constructor 2; exists e; first by exists p0.
pose mu := (('chi_i / 'chi_j)%R %% L)%CF; pose U := cfker mu.
have lin_mu: mu \is a linear_char by rewrite cfMod_lin_char ?rpred_div.
have Uj := lin_char_unitr (linKbar j).
have ltUK: U \proper K.
  rewrite /proper cfker_sub /U; have /irrP[k Dmu] := lin_char_irr lin_mu.
  rewrite Dmu subGcfker -irr_eq1 -Dmu cfMod_eq1 //.
  by rewrite (can2_eq (divrK Uj) (mulrK Uj)) mul1r (inj_eq irr_inj).
suffices: theta \in 'CF(K, L).
  rewrite -cfnorm_Res_lerif // DthL cfnormZ !cfnorm_irr !mulr1 normr_nat.
  by rewrite -natrX eqC_nat => /eqP.
have <-: gcore U G = L.
  apply: maxL; last by rewrite sub_gcore ?cfker_mod.
  by rewrite gcore_norm (sub_proper_trans (gcore_sub _ _)).
apply/cfun_onP=> x; apply: contraNeq => nz_th_x.
apply/bigcapP=> y /(subsetP IGtheta)/setIdP[nKy /eqP th_y].
apply: contraR nz_th_x; rewrite mem_conjg -{}th_y cfConjgE {nKy}//.
move: {x y}(x ^ _) => x U'x; have [Kx | /cfun0-> //] := boolP (x \in K).
have /eqP := congr1 (fun k => (('chi_j %% L)%CF^-1 * 'chi_k) x) eq_mm_ij.
rewrite -rmorphV // !mmLthE !mulrA -!rmorphM mulVr //= rmorph1 !cfunE.
rewrite (mulrC _^-1) -/mu -subr_eq0 -mulrBl cfun1E Kx mulf_eq0 => /orP[]//.
rewrite mulrb subr_eq0 -(lin_char1 lin_mu) [_ == _](contraNF _ U'x) //.
by rewrite /U cfkerEchar ?lin_charW // inE Kx.
Qed.

(* This is Isaacs, Corollary (6.19). *)
Corollary cfRes_prime_irr_cases G N s p (chi := 'chi[G]_s) :
    N <| G -> #|G : N| = p -> prime p ->
  [\/ 'Res[N] chi \in irr N
   |  exists2 c, injective c & 'Res[N] chi = \sum_(i < p) 'chi_(c i)].
Proof.
move=> /andP[sNG nNG] iGN pr_p.
have chiefGN: chief_factor G N G.
  apply/andP; split=> //; apply/maxgroupP.
  split=> [|M /andP[/andP[sMG ltMG] _] sNM].
    by rewrite /proper sNG -indexg_gt1 iGN prime_gt1.
  apply/esym/eqP; rewrite eqEsubset sNM -indexg_eq1 /= eq_sym.
  rewrite -(eqn_pmul2l (indexg_gt0 G M)) muln1 Lagrange_index // iGN.
  by apply/eqP/prime_nt_dvdP; rewrite ?indexg_eq1 // -iGN indexgS.
have abGbar: abelian (G / N).
  by rewrite cyclic_abelian ?prime_cyclic ?card_quotient ?iGN.
have IGchi: G \subset 'I[chi] by apply: sub_inertia.
have [] := invariant_chief_irr_cases chiefGN abGbar IGchi; first by left.
  case=> e _ /(congr1 (fun m => odd (logn p m)))/eqP/idPn[].
  by rewrite lognX mul2n odd_double iGN logn_prime // eqxx.
by rewrite iGN; right.
Qed.

(* This is Isaacs, Corollary (6.20). *)
Corollary prime_invariant_irr_extendible G N s p :
    N <| G -> #|G : N| = p -> prime p -> G \subset 'I['chi_s] ->
  {t | 'Res[N, G] 'chi_t = 'chi_s}.
Proof.
move=> nsNG iGN pr_p IGchi.
have [t sGt] := constt_cfInd_irr s (normal_sub nsNG); exists t.
have [e DtN]: exists e, 'Res 'chi_t = e%:R *: 'chi_s.
  rewrite constt_Ind_Res in sGt.
  rewrite (Clifford_Res_sum_cfclass nsNG sGt); set e := '[_, _].
  rewrite cfclass_invariant // big_seq1.
  by exists (truncC e); rewrite truncCK ?Cnat_cfdot_char ?cfRes_char ?irr_char.
have [/irrWnorm/eqP | [c injc DtNc]] := cfRes_prime_irr_cases t nsNG iGN pr_p.
  rewrite DtN cfnormZ cfnorm_irr normr_nat mulr1 -natrX pnatr_eq1.
  by rewrite muln_eq1 andbb => /eqP->; rewrite scale1r.
have nz_e: e != 0%N.
  have: 'Res[N] 'chi_t != 0 by rewrite cfRes_eq0 // ?irr_char ?irr_neq0.
  by rewrite DtN; apply: contraNneq => ->; rewrite scale0r.
have [i s'ci]: exists i, c i != s.
  pose i0 := Ordinal (prime_gt0 pr_p); pose i1 := Ordinal (prime_gt1 pr_p).
  have [<- | ] := eqVneq (c i0) s; last by exists i0.
  by exists i1; rewrite (inj_eq injc).
have /esym/eqP/idPn[] := congr1 (cfdotr 'chi_(c i)) DtNc; rewrite {1}DtN /=.
rewrite cfdot_suml cfdotZl cfdot_irr mulrb ifN_eqC // mulr0.
rewrite (bigD1 i) //= cfnorm_irr big1 ?addr0 ?oner_eq0 // => j i'j.
by rewrite cfdot_irr mulrb ifN_eq ?(inj_eq injc).
Qed.

(* This is Isaacs, Lemma (6.24). *)
Lemma extend_to_cfdet G N s c0 u :
    let theta := 'chi_s in let lambda := cfDet theta in let mu := 'chi_u in
    N <| G -> coprime #|G : N| (truncC (theta 1%g)) ->
    'Res[N, G] 'chi_c0 = theta -> 'Res[N, G] mu = lambda ->
  exists2 c, 'Res 'chi_c = theta /\ cfDet 'chi_c = mu
          & forall c1, 'Res 'chi_c1 = theta -> cfDet 'chi_c1 = mu -> c1 = c.
Proof.
move=> theta lambda mu nsNG; set e := #|G : N|; set f := truncC _.
set eta := 'chi_c0 => co_e_f etaNth muNlam; have [sNG nNG] := andP nsNG.
have fE: f%:R = theta 1%g by rewrite truncCK ?Cnat_irr1.
pose nu := cfDet eta; have lin_nu: nu \is a linear_char := cfDet_lin_char _.
have nuNlam: 'Res nu = lambda by rewrite -cfDetRes ?irr_char ?etaNth.
have lin_lam: lambda \is a linear_char := cfDet_lin_char _.
have lin_mu: mu \is a linear_char.
  by have:= lin_lam; rewrite -muNlam; apply: cfRes_lin_lin; apply: irr_char.
have [Unu Ulam] := (lin_char_unitr lin_nu, lin_char_unitr lin_lam).
pose alpha := mu / nu.
have alphaN_1: 'Res[N] alpha = 1 by rewrite rmorph_div //= muNlam nuNlam divrr.
have lin_alpha: alpha \is a linear_char by apply: rpred_div.
have alpha_e: alpha ^+ e = 1.
  have kerNalpha: N \subset cfker alpha.
    by rewrite -subsetIidl -cfker_Res ?lin_charW // alphaN_1 cfker_cfun1.
  apply/eqP; rewrite -(cfQuoK nsNG kerNalpha) -rmorphX cfMod_eq1 //.
  rewrite -dvdn_cforder /e -card_quotient //.
  by rewrite cforder_lin_char_dvdG ?cfQuo_lin_char.
have det_alphaXeta b: cfDet (alpha ^+ b * eta) = alpha ^+ (b * f) * nu.
  by rewrite cfDet_mul_lin ?rpredX ?irr_char // -exprM -(cfRes1 N) etaNth.
have [b bf_mod_e]: exists b, b * f = 1 %[mod e].
  rewrite -(chinese_modl co_e_f 1 0) /chinese !mul0n addn0 !mul1n mulnC.
  by exists (egcdn f e).1.
have alpha_bf: alpha ^+ (b * f) = alpha.
  by rewrite -(expr_mod _ alpha_e) bf_mod_e expr_mod.
have /irrP[c Dc]: alpha ^+ b * eta \in irr G.
  by rewrite mul_lin_irr ?rpredX ?mem_irr.
have chiN: 'Res 'chi_c = theta.
  by rewrite -Dc rmorphM rmorphX /= alphaN_1 expr1n mul1r.
have det_chi: cfDet 'chi_c = mu by rewrite -Dc det_alphaXeta alpha_bf divrK.
exists c => // c2 c2Nth det_c2_mu; apply: irr_inj.
have [irrMc _ imMc _] := constt_Ind_ext nsNG chiN.
have /codomP[s2 Dc2]: c2 \in codom (@mul_mod_Iirr G N c).
  by rewrite -imMc constt_Ind_Res c2Nth constt_irr ?inE.
have{Dc2} Dc2: 'chi_c2 = ('chi_s2 %% N)%CF * 'chi_c.
  by rewrite Dc2 cfIirrE // mod_IirrE.
have s2_lin: 'chi_s2 \is a linear_char.
  rewrite qualifE irr_char; apply/eqP/(mulIf (irr1_neq0 c)).
  rewrite mul1r -[in rhs in _ = rhs](cfRes1 N) chiN -c2Nth cfRes1.
  by rewrite Dc2 cfunE cfMod1.
have s2Xf_1: 'chi_s2 ^+ f = 1.
  apply/(can_inj (cfModK nsNG))/(mulIr (lin_char_unitr lin_mu))/esym.
  rewrite rmorph1 rmorphX /= mul1r -{1}det_c2_mu Dc2 -det_chi.
  by rewrite cfDet_mul_lin ?cfMod_lin_char ?irr_char // -(cfRes1 N) chiN.
suffices /eqP s2_1: 'chi_s2 == 1 by rewrite Dc2 s2_1 rmorph1 mul1r.
rewrite -['chi_s2]expr1 -dvdn_cforder -(eqnP co_e_f) dvdn_gcd.
by rewrite /e -card_quotient ?cforder_lin_char_dvdG //= dvdn_cforder s2Xf_1.
Qed.

(* This is Isaacs, Theorem (6.25). *)
Theorem solvable_irr_extendible_from_det G N s (theta := 'chi[N]_s) :
    N <| G -> solvable (G / N) ->
    G \subset 'I[theta] -> coprime #|G : N| (truncC (theta 1%g)) -> 
  [exists c, 'Res 'chi[G]_c == theta]
    = [exists u, 'Res 'chi[G]_u == cfDet theta].
Proof.
set e := #|G : N|; set f := truncC _ => nsNG solG IGtheta co_e_f.
apply/exists_eqP/exists_eqP=> [[c cNth] | [u uNdth]].
  have /lin_char_irr/irrP[u Du] := cfDet_lin_char 'chi_c.
  by exists u; rewrite -Du -cfDetRes ?irr_char ?cNth.
move: {2}e.+1 (ltnSn e) => m.
elim: m => // m IHm in G u e nsNG solG IGtheta co_e_f uNdth *.
rewrite ltnS => le_e; have [sNG nNG] := andP nsNG.
have [<- | ltNG] := eqsVneq N G; first by exists s; rewrite cfRes_id.
have [G0 maxG0 sNG0]: {G0 | maxnormal (gval G0) G G & N \subset G0}.
  by apply: maxgroup_exists; rewrite properEneq ltNG sNG.
have [/andP[ltG0G nG0G] maxG0_P] := maxgroupP maxG0.
set mu := 'chi_u in uNdth; have lin_mu: mu \is a linear_char.
  by rewrite qualifE irr_char -(cfRes1 N) uNdth /= lin_char1 ?cfDet_lin_char.
have sG0G := proper_sub ltG0G; have nsNG0 := normalS sNG0 sG0G nsNG.
have nsG0G: G0 <| G by apply/andP.
have /lin_char_irr/irrP[u0 Du0] := cfRes_lin_char G0 lin_mu.
have u0Ndth: 'Res 'chi_u0 = cfDet theta by rewrite -Du0 cfResRes.
have IG0theta: G0 \subset 'I[theta].
  by rewrite (subset_trans sG0G) // -IGtheta subsetIr.
have coG0f: coprime #|G0 : N| f by rewrite (coprime_dvdl _ co_e_f) ?indexSg.
have{m IHm le_e} [c0 c0Ns]: exists c0, 'Res 'chi[G0]_c0 = theta.
  have solG0: solvable (G0 / N) := solvableS (quotientS N sG0G) solG.
  apply: IHm nsNG0 solG0 IG0theta coG0f u0Ndth (leq_trans _ le_e).
  by rewrite -(ltn_pmul2l (cardG_gt0 N)) !Lagrange ?proper_card.
have{c0 c0Ns} [c0 [c0Ns dc0_u0] Uc0] := extend_to_cfdet nsNG0 coG0f c0Ns u0Ndth.
have IGc0: G \subset 'I['chi_c0].
  apply/subsetP=> x Gx; rewrite inE (subsetP nG0G) //= -conjg_IirrE.
  apply/eqP; congr 'chi__; apply: Uc0; rewrite conjg_IirrE.
    by rewrite -(cfConjgRes _ nsG0G nsNG) // c0Ns inertiaJ ?(subsetP IGtheta).
  by rewrite cfDetConjg dc0_u0 -Du0 (cfConjgRes _ _ nsG0G) // cfConjg_id.
have prG0G: prime #|G : G0|.
  have [h injh im_h] := third_isom sNG0 nsNG nsG0G.
  rewrite -card_quotient // -im_h // card_injm //.
  rewrite simple_sol_prime 1?quotient_sol //.
  by rewrite /simple -(injm_minnormal injh) // im_h // maxnormal_minnormal.
have [t tG0c0] := prime_invariant_irr_extendible nsG0G (erefl _) prG0G IGc0.
by exists t; rewrite /theta -c0Ns -tG0c0 cfResRes.
Qed.

(* This is Isaacs, Theorem (6.26). *)
Theorem extend_linear_char_from_Sylow G N (lambda : 'CF(N)) :
    N <| G -> lambda \is a linear_char -> G \subset 'I[lambda] ->
    (forall p, p \in \pi('o(lambda)%CF) ->
       exists2 Hp : {group gT},
         [/\ N \subset Hp, Hp \subset G & p.-Sylow(G / N) (Hp / N)%g]
       & exists u, 'Res 'chi[Hp]_u = lambda) ->
  exists u, 'Res[N, G] 'chi_u = lambda.
Proof.
set m := 'o(lambda)%CF => nsNG lam_lin IGlam p_ext_lam.
have [sNG nNG] := andP nsNG; have linN := @cfRes_lin_lin _ _ N.
wlog [p p_lam]: lambda @m lam_lin IGlam p_ext_lam /
  exists p : nat, \pi(m) =i (p : nat_pred).
- move=> IHp; have [linG [cf [inj_cf _ lin_cf onto_cf]]] := lin_char_group N.
  case=> cf1 cfM cfX _ cf_order; have [lam cf_lam] := onto_cf _ lam_lin.
  pose mu p := cf lam.`_p; pose pi_m p := p \in \pi(m).
  have Dm: m = #[lam] by rewrite /m cfDet_order_lin // cf_lam cf_order.
  have Dlambda: lambda = \prod_(p < m.+1 | pi_m p) mu p.
    rewrite -(big_morph cf cfM cf1) big_mkcond cf_lam /pi_m Dm; congr (cf _).
    rewrite -{1}[lam]prod_constt big_mkord; apply: eq_bigr => p _.
    by case: ifPn => // p'lam; apply/constt1P; rewrite /p_elt p'natEpi.
  have lin_mu p: mu p \is a linear_char by rewrite /mu cfX -cf_lam rpredX.
  suffices /fin_all_exists [u uNlam] (p : 'I_m.+1):
    exists u, pi_m p -> 'Res[N, G] 'chi_u = mu p.
  - pose nu := \prod_(p < m.+1 | pi_m p) 'chi_(u p).
    have lin_nu: nu \is a linear_char.
      by apply: rpred_prod => p m_p; rewrite linN ?irr_char ?uNlam.
    have /irrP[u1 Dnu] := lin_char_irr lin_nu.
    by exists u1; rewrite Dlambda -Dnu rmorph_prod; apply: eq_bigr.
  have [m_p | _] := boolP (pi_m p); last by exists 0.
  have o_mu: \pi('o(mu p)%CF) =i (p : nat_pred).
    rewrite cfDet_order_lin // cf_order orderE /=.
    have [|pr_p _ [k ->]] := pgroup_pdiv (p_elt_constt p lam).
      by rewrite cycle_eq1 (sameP eqP constt1P) /p_elt p'natEpi // negbK -Dm.
    by move=> q; rewrite pi_of_exp // pi_of_prime.
  have IGmu: G \subset 'I[mu p].
    rewrite (subset_trans IGlam) // /mu cfX -cf_lam.
    elim: (chinese _ _ _ _) => [|k IHk]; first by rewrite inertia1 norm_inertia.
    by rewrite exprS (subset_trans _ (inertia_mul _ _)) // subsetIidl.
  have [q||u] := IHp _ (lin_mu p) IGmu; [ | by exists p | by exists u].
  rewrite o_mu => /eqnP-> {q}.
  have [Hp sylHp [u uNlam]] := p_ext_lam p m_p; exists Hp => //.
  rewrite /mu cfX -cf_lam -uNlam -rmorphX /=; set nu := _ ^+ _.
  have /lin_char_irr/irrP[v ->]: nu \is a linear_char; last by exists v.
  by rewrite rpredX // linN ?irr_char ?uNlam.
have pi_m_p: p \in \pi(m) by rewrite p_lam !inE.
have [pr_p mgt0]: prime p /\ (m > 0)%N.
  by have:= pi_m_p; rewrite mem_primes => /and3P[].
have p_m: p.-nat m by rewrite -(eq_pnat _ p_lam) pnat_pi.
have{p_ext_lam} [H [sNH sHG sylHbar] [v vNlam]] := p_ext_lam p pi_m_p.
have co_p_GH: coprime p #|G : H|.
  rewrite -(index_quotient_eq _ sHG nNG) ?subIset ?sNH ?orbT //.
  by rewrite (pnat_coprime (pnat_id pr_p)) //; have [] := and3P sylHbar.
have lin_v: 'chi_v \is a linear_char by rewrite linN ?irr_char ?vNlam.
pose nuG := 'Ind[G] 'chi_v.
have [c vGc co_p_f]: exists2 c, c \in irr_constt nuG & ~~ (p %| 'chi_c 1%g)%C.
  apply/exists_inP; rewrite -negb_forall_in.
  apply: contraL co_p_GH => /forall_inP p_dv_v1.
  rewrite prime_coprime // negbK -dvdC_nat -[rhs in (_ %| rhs)%C]mulr1.
  rewrite -(lin_char1 lin_v) -cfInd1 // ['Ind _]cfun_sum_constt /=.
  rewrite sum_cfunE rpred_sum // => i /p_dv_v1 p_dv_chi1i.
  rewrite cfunE dvdC_mull // rpred_Cnat //.
  by rewrite Cnat_cfdot_char ?cfInd_char ?irr_char.
pose f := truncC ('chi_c 1%g); pose b := (egcdn f m).1.
have fK: f%:R = 'chi_c 1%g by rewrite truncCK ?Cnat_irr1.
have fb_mod_m: f * b = 1 %[mod m].
  have co_m_f: coprime m f.
    by rewrite (pnat_coprime p_m) ?p'natE // -dvdC_nat CdivE fK.
  by rewrite -(chinese_modl co_m_f 1 0) /chinese !mul0n addn0 mul1n.
have /irrP[s Dlam] := lin_char_irr lam_lin.
have cHv: v \in irr_constt ('Res[H] 'chi_c) by rewrite -constt_Ind_Res.
have{cHv} cNs: s \in irr_constt ('Res[N] 'chi_c).
  rewrite -(cfResRes _ sNH) ?(constt_Res_trans _ cHv) ?cfRes_char ?irr_char //.
  by rewrite vNlam Dlam constt_irr !inE.
have DcN: 'Res[N] 'chi_c = lambda *+ f.
  have:= Clifford_Res_sum_cfclass nsNG cNs.
  rewrite cfclass_invariant -Dlam // big_seq1 Dlam => DcN.
  have:= cfRes1 N 'chi_c; rewrite DcN cfunE -Dlam lin_char1 // mulr1 => ->.
  by rewrite -scaler_nat fK.
have /lin_char_irr/irrP[d Dd]: cfDet 'chi_c ^+ b \is a linear_char.
  by rewrite rpredX // cfDet_lin_char.
exists d; rewrite -{}Dd rmorphX /= -cfDetRes ?irr_char // DcN.
rewrite cfDetMn ?lin_charW // -exprM cfDet_id //.
rewrite -(expr_mod _ (exp_cforder _)) -cfDet_order_lin // -/m.
by rewrite fb_mod_m /m cfDet_order_lin // expr_mod ?exp_cforder.
Qed.

(* This is Isaacs, Corollary (6.27). *)
Corollary extend_coprime_linear_char G N (lambda : 'CF(N)) :
    N <| G -> lambda \is a linear_char -> G \subset 'I[lambda] ->
    coprime #|G : N| 'o(lambda)%CF ->
  exists u, [/\ 'Res 'chi[G]_u = lambda, 'o('chi_u)%CF = 'o(lambda)%CF
              & forall v,
                  'Res 'chi_v = lambda -> coprime #|G : N| 'o('chi_v)%CF ->
                v = u].
Proof.
set e := #|G : N| => nsNG lam_lin IGlam co_e_lam; have [sNG nNG] := andP nsNG.
have [p lam_p | v vNlam] := extend_linear_char_from_Sylow nsNG lam_lin IGlam.
  exists N; last first.
    by have /irrP[u ->] := lin_char_irr lam_lin; exists u; rewrite cfRes_id.
  split=> //; rewrite trivg_quotient /pHall sub1G pgroup1 indexg1.
  rewrite card_quotient //= -/e (pi'_p'nat _ lam_p) //.
  rewrite -coprime_pi' ?indexg_gt0 1?coprime_sym //.
  by have:= lam_p; rewrite mem_primes => /and3P[].
set nu := 'chi_v in vNlam.
have lin_nu: nu \is a linear_char.
  by rewrite (@cfRes_lin_lin _ _ N) ?vNlam ?irr_char.
have [b be_mod_lam]: exists b, b * e = 1 %[mod 'o(lambda)%CF].
  rewrite -(chinese_modr co_e_lam 0 1) /chinese !mul0n !mul1n mulnC.
  by set b := _.1; exists b.
have /irrP[u Du]: nu ^+ (b * e) \in irr G by rewrite lin_char_irr ?rpredX.
exists u; set mu := 'chi_u in Du *.
have uNlam: 'Res mu = lambda.
  rewrite cfDet_order_lin // in be_mod_lam.
  rewrite -Du rmorphX /= vNlam -(expr_mod _ (exp_cforder _)) //.
  by rewrite be_mod_lam expr_mod ?exp_cforder.
have lin_mu: mu \is a linear_char by rewrite -Du rpredX.
have o_mu: ('o(mu) = 'o(lambda))%CF.
  have dv_o_lam_mu: 'o(lambda)%CF %| 'o(mu)%CF.
    by rewrite !cfDet_order_lin // -uNlam cforder_Res.
  have kerNnu_olam: N \subset cfker (nu ^+ 'o(lambda)%CF).
    rewrite -subsetIidl -cfker_Res ?rpredX ?irr_char //.
    by rewrite rmorphX /= vNlam cfDet_order_lin // exp_cforder cfker_cfun1.
  apply/eqP; rewrite eqn_dvd dv_o_lam_mu andbT cfDet_order_lin //.
  rewrite dvdn_cforder -Du exprAC -dvdn_cforder dvdn_mull //.
  rewrite -(cfQuoK nsNG kerNnu_olam) cforder_mod // /e -card_quotient //.
  by rewrite cforder_lin_char_dvdG ?cfQuo_lin_char ?rpredX.
split=> // t tNlam co_e_t.
have lin_t: 'chi_t \is a linear_char.
  by rewrite (@cfRes_lin_lin _ _ N) ?tNlam ?irr_char.
have Ut := lin_char_unitr lin_t.
have kerN_mu_t: N \subset cfker (mu / 'chi_t)%R.
  rewrite -subsetIidl -cfker_Res ?lin_charW ?rpred_div ?rmorph_div //.
  by rewrite /= uNlam tNlam divrr ?lin_char_unitr ?cfker_cfun1.
have co_e_mu_t: coprime e #[(mu / 'chi_t)%R]%CF.
  suffices dv_o_mu_t: #[(mu / 'chi_t)%R]%CF %| 'o(mu)%CF * 'o('chi_t)%CF.
    by rewrite (coprime_dvdr dv_o_mu_t) // coprime_mulr o_mu co_e_lam.
  rewrite !cfDet_order_lin //; apply/dvdn_cforderP=> x Gx.
  rewrite invr_lin_char // !cfunE exprMn -rmorphX {2}mulnC.
  by rewrite !(dvdn_cforderP _) ?conjC1 ?mulr1 // dvdn_mulr.
have /eqP mu_t_1: mu / 'chi_t == 1.
  rewrite -(dvdn_cforder (_ / _)%R 1) -(eqnP co_e_mu_t) dvdn_gcd dvdnn andbT.
  rewrite -(cfQuoK nsNG kerN_mu_t) cforder_mod // /e -card_quotient //.
  by rewrite cforder_lin_char_dvdG ?cfQuo_lin_char ?rpred_div.
by apply: irr_inj; rewrite -['chi_t]mul1r -mu_t_1 divrK.
Qed.

(* This is Isaacs, Corollary (6.28). *)
Corollary extend_solvable_coprime_irr G N t (theta := 'chi[N]_t) :
    N <| G -> solvable (G / N) -> G \subset 'I[theta] ->
    coprime #|G : N| ('o(theta)%CF * truncC (theta 1%g)) ->
  exists c, [/\ 'Res 'chi[G]_c = theta, 'o('chi_c)%CF = 'o(theta)%CF
              & forall d,
                  'Res 'chi_d = theta -> coprime #|G : N| 'o('chi_d)%CF ->
                d = c].
Proof.
set e := #|G : N|; set f := truncC _ => nsNG solG IGtheta.
rewrite coprime_mulr => /andP[co_e_th co_e_f].
have [sNG nNG] := andP nsNG; pose lambda := cfDet theta.
have lin_lam: lambda \is a linear_char := cfDet_lin_char theta.
have IGlam: G \subset 'I[lambda].
  apply/subsetP=> y /(subsetP IGtheta)/setIdP[nNy /eqP th_y].
  by rewrite inE nNy /= -cfDetConjg th_y.
have co_e_lam: coprime e 'o(lambda)%CF by rewrite cfDet_order_lin.
have [//|u [uNlam o_u Uu]] := extend_coprime_linear_char nsNG lin_lam IGlam.
have /exists_eqP[c cNth]: [exists c, 'Res 'chi[G]_c == theta].
  rewrite solvable_irr_extendible_from_det //.
  by apply/exists_eqP; exists u.
have{c cNth} [c [cNth det_c] Uc] := extend_to_cfdet nsNG co_e_f cNth uNlam.
have lin_u: 'chi_u \is a linear_char by rewrite -det_c cfDet_lin_char.
exists c; split=> // [|c0 c0Nth co_e_c0].
  by rewrite !cfDet_order_lin // -det_c in o_u.
have lin_u0: cfDet 'chi_c0 \is a linear_char := cfDet_lin_char 'chi_c0.
have /irrP[u0 Du0] := lin_char_irr lin_u0.
have co_e_u0: coprime e 'o('chi_u0)%CF by rewrite -Du0 cfDet_order_lin.
have eq_u0u: u0 = u by apply: Uu; rewrite // -Du0 -cfDetRes ?irr_char ?c0Nth.
by apply: Uc; rewrite // Du0 eq_u0u.
Qed.

End ExtendInvariantIrr.

Section Frobenius.

Variables (gT : finGroupType) (G K : {group gT}).

(* Because he only defines Frobenius groups in chapter 7, Isaacs does not     *)
(* state these theorems using the Frobenius property.                         *)
Hypothesis frobGK : [Frobenius G with kernel K].

(* This is Isaacs, Theorem 6.34(a1). *)
Theorem inertia_Frobenius_ker i : i != 0 -> 'I_G['chi[K]_i] = K.
Proof.
have [_ _ nsKG regK] := Frobenius_kerP frobGK; have [sKG nKG] := andP nsKG.
move=> nzi; apply/eqP; rewrite eqEsubset sub_Inertia // andbT.
apply/subsetP=> x /setIP[Gx /setIdP[nKx /eqP x_stab_i]].
have actIirrK: is_action G (@conjg_Iirr _ K).
  split=> [y j k eq_jk | j y z Gy Gz].
    by apply/irr_inj/(can_inj (cfConjgK y)); rewrite -!conjg_IirrE eq_jk.
  by apply: irr_inj; rewrite !conjg_IirrE (cfConjgM _ nsKG).
pose ito := Action actIirrK; pose cto := ('Js \ (subsetT G))%act.
have acts_Js : [acts G, on classes K | 'Js].
  apply/subsetP=> y Gy; have nKy := subsetP nKG y Gy.
  rewrite !inE; apply/subsetP=> _ /imsetP[z Gz ->]; rewrite !inE /=.
  rewrite -class_rcoset norm_rlcoset // class_lcoset.
  by apply: mem_imset; rewrite memJ_norm.
have acts_cto : [acts G, on classes K | cto] by rewrite astabs_ract subsetIidl.
pose m := #|'Fix_(classes K | cto)[x]|.
have def_m: #|'Fix_ito[x]| = m.
  apply: card_afix_irr_classes => // j y _ Ky /imsetP[_ /imsetP[z Kz ->] ->].
  by rewrite conjg_IirrE cfConjgEJ // cfunJ.
have: (m != 1)%N.
  rewrite -def_m (cardD1 (0 : Iirr K)) (cardD1 i) !(inE, sub1set) /=.
  by rewrite conjg_Iirr0 nzi eqxx -(inj_eq irr_inj) conjg_IirrE x_stab_i eqxx.
apply: contraR => notKx; apply/cards1P; exists 1%g; apply/esym/eqP.
rewrite eqEsubset !(sub1set, inE) classes1 /= conjs1g eqxx /=.
apply/subsetP=> _ /setIP[/imsetP[y Ky ->] /afix1P /= cyKx].
have /imsetP[z Kz def_yx]: y ^ x \in y ^: K.
  by rewrite -cyKx; apply: mem_imset; apply: class_refl.
rewrite inE classG_eq1; apply: contraR notKx => nty.
rewrite -(groupMr x (groupVr Kz)).
apply: (subsetP (regK y _)); first exact/setD1P.
rewrite !inE groupMl // groupV (subsetP sKG) //=.
by rewrite conjg_set1 conjgM def_yx conjgK.
Qed.

(* This is Isaacs, Theorem 6.34(a2) *)
Theorem irr_induced_Frobenius_ker i : i != 0 -> 'Ind[G, K] 'chi_i \in irr G.
Proof.
move/inertia_Frobenius_ker/group_inj=> defK.
have [_ _ nsKG _] := Frobenius_kerP frobGK.
have [] := constt_Inertia_bijection i nsKG; rewrite defK cfInd_id => -> //.
by rewrite constt_irr !inE.
Qed.

(* This is Isaacs, Theorem 6.34(b) *)
Theorem Frobenius_Ind_irrP j :
  reflect (exists2 i, i != 0 & 'chi_j = 'Ind[G, K] 'chi_i)
          (~~ (K \subset cfker 'chi_j)).
Proof.
have [_ _ nsKG _] := Frobenius_kerP frobGK; have [sKG nKG] := andP nsKG.
apply: (iffP idP) => [not_chijK1 | [i nzi ->]]; last first.
  by rewrite cfker_Ind_irr ?sub_gcore // subGcfker.
have /neq0_has_constt[i chijKi]: 'Res[K] 'chi_j != 0 by apply: Res_irr_neq0.
have nz_i: i != 0.
  by apply: contraNneq not_chijK1 => i0; rewrite constt0_Res_cfker // -i0.
have /irrP[k def_chik] := irr_induced_Frobenius_ker nz_i.
have: '['chi_j, 'chi_k] != 0 by rewrite -def_chik -cfdot_Res_l.
by rewrite cfdot_irr pnatr_eq0; case: (j =P k) => // ->; exists i.
Qed.

End Frobenius.

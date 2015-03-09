(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice div fintype.
Require Import path bigop finset prime fingroup morphism perm automorphism.
Require Import quotient action gproduct gfunctor pgroup cyclic commutator.
Require Import center gseries nilpotent sylow abelian maximal hall frobenius.
Require Import BGsection1 BGsection3 BGsection4 BGsection5 BGsection6.
Require Import BGsection7 BGsection9 BGsection10 BGsection11.

(******************************************************************************)
(*   This file covers B & G, section 12; it defines the prime sets for the    *)
(* complements of M`_\sigma in a maximal group M:                             *)
(*    \tau1(M) == the set of p not in \pi(M^`(1)) (thus not in \sigma(M)),    *)
(*                such that M has p-rank 1.                                   *)
(*    \tau2(M) == the set of p not in \sigma(M), such that M has p-rank 2.    *)
(*    \tau3(M) == the set of p not in \sigma(M), but in \pi(M^`(1)), such     *)
(*                that M has p-rank 1.                                        *)
(*   We also define the following helper predicate, which encapsulates the    *)
(* notation conventions defined at the beginning of B & G, Section 12:        *)
(*   sigma_complement M E E1 E2 E3 <=>                                        *)
(*                E is a Hall \sigma(M)^'-subgroup of M, the Ei are Hall      *)
(*                \tau_i(M)-subgroups of E, and E2 * E1 is a group.           *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.
Section Definitions.

Variables (gT : finGroupType) (M : {set gT}).
Local Notation sigma' := \sigma(M)^'.

Definition tau1 := [pred p in sigma' | 'r_p(M) == 1%N & ~~ (p %| #|M^`(1)|)].
Definition tau2 := [pred p in sigma' | 'r_p(M) == 2].
Definition tau3 := [pred p in sigma' | 'r_p(M) == 1%N & p %| #|M^`(1)|].

Definition sigma_complement E E1 E2 E3 :=
  [/\ sigma'.-Hall(M) E, tau1.-Hall(E) E1, tau2.-Hall(E) E2, tau3.-Hall(E) E3
    & group_set (E2 * E1)].

End Definitions.

Notation "\tau1 ( M )" := (tau1 M)
  (at level 2, format "\tau1 ( M )") : group_scope.
Notation "\tau2 ( M )" := (tau2 M)
  (at level 2, format "\tau2 ( M )") : group_scope.
Notation "\tau3 ( M )" := (tau3 M)
  (at level 2, format "\tau3 ( M )") : group_scope.

Section Section12.

Variable gT : minSimpleOddGroupType.
Local Notation G := (TheMinSimpleOddGroup gT).
Implicit Types p q r : nat.
Implicit Types A E H K M Mstar N P Q R S T U V W X Y Z : {group gT}.

Section Introduction.

Variables M E : {group gT}.
Hypotheses (maxM : M \in 'M) (hallE : \sigma(M)^'.-Hall(M) E).

Lemma tau1J x : \tau1(M :^ x) =i \tau1(M).
Proof. by move=> p; rewrite 3!inE sigmaJ p_rankJ derg1 -conjsRg cardJg. Qed.

Lemma tau2J x : \tau2(M :^ x) =i \tau2(M).
Proof. by move=> p; rewrite 3!inE sigmaJ p_rankJ. Qed.

Lemma tau3J x : \tau3(M :^ x) =i \tau3(M).
Proof. by move=> p; rewrite 3!inE sigmaJ p_rankJ derg1 -conjsRg cardJg. Qed.

Lemma tau2'1 : {subset \tau1(M) <= \tau2(M)^'}.
Proof. by move=> p; rewrite !inE; case/and3P=> ->; move/eqP->. Qed.

Lemma tau3'1 : {subset \tau1(M) <= \tau3(M)^'}.
Proof. by move=> p; rewrite !inE; case/and3P=> -> ->. Qed.

Lemma tau3'2 : {subset \tau2(M) <= \tau3(M)^'}.
Proof. by move=> p; rewrite !inE; case/andP=> ->; move/eqP->. Qed.

Lemma ex_sigma_compl : exists F : {group gT}, \sigma(M)^'.-Hall(M) F.
Proof. exact: Hall_exists (mmax_sol maxM). Qed.

Let s'E : \sigma(M)^'.-group E := pHall_pgroup hallE.
Let sEM : E \subset M := pHall_sub hallE.

(* For added convenience, this lemma does NOT depend on the maxM assumption. *)
Lemma sigma_compl_sol : solvable E.
Proof.
have [-> | [p p_pr pE]] := trivgVpdiv E; first exact: solvable1.
rewrite (solvableS sEM) // mFT_sol // properT.
apply: contraNneq (pgroupP s'E p p_pr pE) => ->.
have [P sylP] := Sylow_exists p [set: gT].
by apply/exists_inP; exists P; rewrite ?subsetT.
Qed. 
Let solE := sigma_compl_sol.

Let exHallE pi := exists Ei : {group gT}, pi.-Hall(E) Ei.
Lemma ex_tau13_compl : exHallE \tau1(M) /\ exHallE \tau3(M).
Proof. by split; exact: Hall_exists. Qed.

Lemma ex_tau2_compl E1 E3 :
    \tau1(M).-Hall(E) E1 -> \tau3(M).-Hall(E) E3 ->
  exists2 E2 : {group gT}, \tau2(M).-Hall(E) E2 & sigma_complement M E E1 E2 E3.
Proof.
move=> hallE1 hallE3; have [sE1E t1E1 _] := and3P hallE1.
pose tau12 := [predU \tau1(M) & \tau2(M)].
have t12E1: tau12.-group E1 by apply: sub_pgroup t1E1 => p t1p; apply/orP; left.
have [E21 hallE21 sE1E21] := Hall_superset solE sE1E t12E1.
have [sE21E t12E21 _] := and3P hallE21.
have [E2 hallE2] := Hall_exists \tau2(M) (solvableS sE21E solE).
have [sE2E21 t2E2 _] := and3P hallE2.
have hallE2_E: \tau2(M).-Hall(E) E2.
  by apply: subHall_Hall hallE21 _ hallE2 => p t2p; apply/orP; right.
exists E2 => //; split=> //.
suffices ->: E2 * E1 = E21 by apply: groupP.
have coE21: coprime #|E2| #|E1| := sub_pnat_coprime tau2'1 t2E2 t1E1.
apply/eqP; rewrite eqEcard mul_subG ?coprime_cardMg //=.
rewrite -(partnC \tau1(M) (cardG_gt0 E21)) (card_Hall hallE2) mulnC.
rewrite (card_Hall (pHall_subl sE1E21 sE21E hallE1)) leq_pmul2r //.
rewrite dvdn_leq // sub_in_partn // => p t12p t1'p.
by apply: contraLR (pnatPpi t12E21 t12p) => t2'p; apply/norP.
Qed.

Lemma coprime_sigma_compl : coprime #|M`_\sigma| #|E|.
Proof. exact: pnat_coprime (pcore_pgroup _ _) (pHall_pgroup hallE). Qed.
Let coMsE := coprime_sigma_compl.

Lemma pi_sigma_compl : \pi(E) =i [predD \pi(M) & \sigma(M)].
Proof. by move=> p; rewrite /= (card_Hall hallE) pi_of_part // !inE andbC. Qed.

Lemma sdprod_sigma : M`_\sigma ><| E = M.
Proof.
rewrite sdprodE ?coprime_TIg ?(subset_trans sEM) ?gFnorm //.
apply/eqP; rewrite eqEcard mul_subG ?pcore_sub ?coprime_cardMg //=.
by rewrite (card_Hall (Msigma_Hall maxM)) (card_Hall hallE) partnC.
Qed.

(* The preliminary remarks in the introduction of B & G, section 12. *)

Remark der1_sigma_compl : M^`(1) :&: E = E^`(1).
Proof.
have [nsMsM _ defM _ _] := sdprod_context sdprod_sigma.
by rewrite setIC (pprod_focal_coprime defM _ (subxx E)) ?(setIidPr _) ?der_sub.
Qed.

Remark partition_pi_mmax p :
  (p \in \pi(M)) =
     [|| p \in \tau1(M), p \in \tau2(M), p \in \tau3(M) | p \in \sigma(M)].
Proof.
symmetry; rewrite 2!orbA -!andb_orr orbAC -andb_orr orNb andbT.
rewrite orb_andl orNb /= -(orb_idl ((alpha_sub_sigma maxM) p)) orbA orbC -orbA.
rewrite !(eq_sym 'r_p(M)) -!leq_eqVlt p_rank_gt0 orb_idl //.
exact: sigma_sub_pi.
Qed.

Remark partition_pi_sigma_compl p :
  (p \in \pi(E)) = [|| p \in \tau1(M), p \in \tau2(M) | p \in \tau3(M)].
Proof.
rewrite pi_sigma_compl inE /= partition_pi_mmax !andb_orr /=.
by rewrite andNb orbF !(andbb, andbA) -2!andbA.
Qed.

Remark tau2E p : (p \in \tau2(M)) = (p \in \pi(E)) && ('r_p(E) == 2).
Proof.
have [P sylP] := Sylow_exists p E.
rewrite -(andb_idl (pnatPpi s'E)) -p_rank_gt0 -andbA; apply: andb_id2l => s'p.
have sylP_M := subHall_Sylow hallE s'p sylP.
by rewrite -(p_rank_Sylow sylP_M) (p_rank_Sylow sylP); case: posnP => // ->.
Qed.

Remark tau3E p : (p \in \tau3(M)) = (p \in \pi(E^`(1))) && ('r_p(E) == 1%N).
Proof.
have [P sylP] := Sylow_exists p E.
have hallE': \sigma(M)^'.-Hall(M^`(1)) E^`(1).
  by rewrite -der1_sigma_compl setIC (Hall_setI_normal _ hallE) ?der_normal.
rewrite 4!inE -(andb_idl (pnatPpi (pHall_pgroup hallE'))) -andbA.
apply: andb_id2l => s'p; have sylP_M := subHall_Sylow hallE s'p sylP.
rewrite -(p_rank_Sylow sylP_M) (p_rank_Sylow sylP) andbC; apply: andb_id2r.
rewrite eqn_leq p_rank_gt0 mem_primes => /and3P[_ p_pr _].
rewrite (card_Hall hallE') pi_of_part 3?inE ?mem_primes ?cardG_gt0 //=.
by rewrite p_pr inE /= s'p andbT.
Qed.

Remark tau1E p :
  (p \in \tau1(M)) = [&& p \in \pi(E), p \notin \pi(E^`(1)) & 'r_p(E) == 1%N].
Proof.
rewrite partition_pi_sigma_compl; apply/idP/idP=> [t1p|].
  have [s'p rpM _] := and3P t1p; have [P sylP] := Sylow_exists p E.
  have:= tau3'1 t1p; rewrite t1p /= inE /= tau3E -(p_rank_Sylow sylP).
  by rewrite (p_rank_Sylow (subHall_Sylow hallE s'p sylP)) rpM !andbT.
rewrite orbC andbC -andbA => /and3P[not_piE'p /eqP rpE].
by rewrite tau3E tau2E rpE (negPf not_piE'p) andbF.
Qed.

(* Generate a rank 2 elementary abelian tau2 subgroup in a given complement.  *)
Lemma ex_tau2Elem p :
  p \in \tau2(M) -> exists2 A, A \in 'E_p^2(E) & A \in 'E_p^2(M).
Proof.
move=> t2p; have [A Ep2A] := p_rank_witness p E.
have <-: 'r_p(E) = 2 by apply/eqP; move: t2p; rewrite tau2E; case/andP.
by exists A; rewrite // (subsetP (pnElemS p _ sEM)).
Qed.

(* A converse to the above Lemma: if E has an elementary abelian subgroup of  *)
(* order p^2, then p must be in tau2.                                         *)
Lemma sigma'2Elem_tau2 p A : A \in 'E_p^2(E) -> p \in \tau2(M).
Proof.
move=> Ep2A; have rE: 'r_p(E) > 1 by apply/p_rank_geP; exists A.
have: p \in \pi(E) by rewrite -p_rank_gt0 ltnW.
rewrite partition_pi_sigma_compl orbCA => /orP[] //.
by rewrite -!andb_orr eqn_leq leqNgt (leq_trans rE) ?andbF ?p_rankS.
Qed.

(* This is B & G, Lemma 12.1(a). *)
Lemma der1_sigma_compl_nil : nilpotent E^`(1).
Proof.
have sE'E := der_sub 1 E.
have nMaE: E \subset 'N(M`_\alpha) by rewrite (subset_trans sEM) ?gFnorm.
have tiMaE':  M`_\alpha :&: E^`(1) = 1.
  by apply/trivgP; rewrite -(coprime_TIg coMsE) setISS ?Malpha_sub_Msigma.
rewrite (isog_nil (quotient_isog (subset_trans sE'E nMaE) tiMaE')).
by rewrite (nilpotentS (quotientS _ (dergS 1 sEM))) ?Malpha_quo_nil.
Qed.

(* This is B & G, Lemma 12.1(g). *)
Lemma tau2_not_beta p :
  p \in \tau2(M) -> p \notin \beta(G) /\ {subset 'E_p^2(M) <= 'E*_p(G)}. 
Proof.
case/andP=> s'p /eqP rpM; split; first exact: sigma'_rank2_beta' rpM.
by apply/subsetP; exact: sigma'_rank2_max.
Qed.

End Introduction.

Implicit Arguments tau2'1 [[M] x].
Implicit Arguments tau3'1 [[M] x].
Implicit Arguments tau3'2 [[M] x].

(* This is the rest of B & G, Lemma 12.1 (parts b, c, d,e, and f). *)
Lemma sigma_compl_context M E E1 E2 E3 :
    M \in 'M -> sigma_complement M E E1 E2 E3 ->
  [/\ (*b*) E3 \subset E^`(1) /\ E3 <| E,
      (*c*) E2 :==: 1 -> E1 :!=: 1,
      (*d*) cyclic E1 /\ cyclic E3,
      (*e*) E3 ><| (E2 ><| E1) = E /\ E3 ><| E2 ><| E1 = E 
    & (*f*) 'C_E3(E) = 1].
Proof.
move=> maxM [hallE hallE1 hallE2 hallE3 groupE21].
have [sEM solM] := (pHall_sub hallE, mmax_sol maxM). 
have [[sE1E t1E1 _] [sE3E t3E3 _]] := (and3P hallE1, and3P hallE3).
have tiE'E1: E^`(1) :&: E1 = 1.
  rewrite coprime_TIg // coprime_pi' ?cardG_gt0 //.
  by apply: sub_pgroup t1E1 => p; rewrite (tau1E maxM hallE) => /and3P[].
have cycE1: cyclic E1.
  apply: nil_Zgroup_cyclic.
    rewrite odd_rank1_Zgroup ?mFT_odd //; apply: wlog_neg; rewrite -ltnNge.
    have [p p_pr ->]:= rank_witness E1; move/ltnW; rewrite p_rank_gt0.
    move/(pnatPpi t1E1); rewrite (tau1E maxM hallE) => /and3P[_ _ /eqP <-].
    by rewrite p_rankS.
  rewrite abelian_nil // /abelian (sameP commG1P trivgP) -tiE'E1.
  by rewrite subsetI (der_sub 1) (dergS 1).
have solE: solvable E := solvableS sEM solM.
have nilE': nilpotent E^`(1) := der1_sigma_compl_nil maxM hallE.
have nsE'piE pi: 'O_pi(E^`(1)) <| E.
  exact: char_normal_trans (pcore_char _ _) (der_normal _ _).
have SylowE3 P: Sylow E3 P -> [/\ cyclic P, P \subset E^`(1) & 'C_P(E) = 1].
- case/SylowP=> p p_pr sylP; have [sPE3 pP _] := and3P sylP.
  have [-> | ntP] := eqsVneq P 1.
    by rewrite cyclic1 sub1G (setIidPl (sub1G _)).
  have t3p: p \in \tau3(M).
    rewrite (pnatPpi t3E3) // -p_rank_gt0 -(p_rank_Sylow sylP) -rank_pgroup //.
    by rewrite rank_gt0.
  have sPE: P \subset E := subset_trans sPE3 sE3E.
  have cycP: cyclic P.
    rewrite (odd_pgroup_rank1_cyclic pP) ?mFT_odd //.
    rewrite (tau3E maxM hallE) in t3p.
    by case/andP: t3p => _ /eqP <-; rewrite p_rankS.
  have nEp'E: E \subset 'N('O_p^'(E)) by exact: gFnorm.
  have nEp'P := subset_trans sPE nEp'E.
  have sylP_E := subHall_Sylow hallE3 t3p sylP.
  have nsEp'P_E: 'O_p^'(E) <*> P <| E.
    rewrite sub_der1_normal ?join_subG ?pcore_sub //=.
    rewrite norm_joinEr // -quotientSK //=; last first.
      by rewrite (subset_trans (der_sub 1 E)).
    have [_ /= <- _ _] := dprodP (nilpotent_pcoreC p nilE').
    rewrite -quotientMidr -mulgA (mulSGid (pcore_max _ _)) ?pcore_pgroup //=.
    rewrite quotientMidr quotientS //.
    apply: subset_trans (pcore_sub_Hall sylP_E).
    by rewrite pcore_max ?pcore_pgroup /=.
  have nEP_sol: solvable 'N_E(P) by rewrite (solvableS _ solE) ?subsetIl.
  have [K hallK] := Hall_exists p^' nEP_sol; have [sKNEP p'K _] := and3P hallK.
  have coPK: coprime #|P| #|K| := pnat_coprime pP p'K.
  have sP_NEP: P \subset 'N_E(P) by rewrite subsetI sPE normG.
  have mulPK: P * K = 'N_E(P).
    apply/eqP; rewrite eqEcard mul_subG //= coprime_cardMg // (card_Hall hallK).
    by rewrite (card_Hall (pHall_subl sP_NEP (subsetIl E _) sylP_E)) partnC.
  rewrite subsetI in sKNEP; case/andP: sKNEP => sKE nPK.
  have nEp'K := subset_trans sKE nEp'E.
  have defE: 'O_p^'(E) <*> K * P = E.
    have sP_Ep'P: P \subset 'O_p^'(E) <*> P := joing_subr _ _.
    have sylP_Ep'P := pHall_subl sP_Ep'P (normal_sub nsEp'P_E) sylP_E.
    rewrite -{2}(Frattini_arg nsEp'P_E sylP_Ep'P) /= !norm_joinEr //.
    by rewrite -mulgA (normC nPK) -mulPK -{1}(mulGid P) !mulgA.
  have ntPE': P :&: E^`(1) != 1.
    have sylPE' := Hall_setI_normal (der_normal 1 E) sylP_E. 
    rewrite -rank_gt0 (rank_Sylow sylPE') p_rank_gt0.
    by rewrite (tau3E maxM hallE) in t3p; case/andP: t3p.
  have defP := coprime_abelian_cent_dprod nPK coPK (cyclic_abelian cycP).
  have{defP} [[PK1 _]|[regKP defP]] := cyclic_pgroup_dprod_trivg pP cycP defP.
    have coP_Ep'K: coprime #|P| #|'O_p^'(E) <*> K|.
      rewrite (pnat_coprime pP) // -pgroupE norm_joinEr //.
      by rewrite pgroupM pcore_pgroup.
    rewrite -subG1 -(coprime_TIg coP_Ep'K) setIS ?der1_min // in ntPE'.
      rewrite -{1}defE mulG_subG normG normsY // cents_norm //.
      exact/commG1P.
    by rewrite -{2}defE quotientMidl quotient_abelian ?cyclic_abelian.
  split=> //; first by rewrite -defP commgSS.
  by apply/trivgP; rewrite -regKP setIS ?centS.
have sE3E': E3 \subset E^`(1).
  by rewrite -(Sylow_gen E3) gen_subG; apply/bigcupsP=> P; case/SylowE3.
have cycE3: cyclic E3.
  rewrite nil_Zgroup_cyclic ?(nilpotentS sE3E') //.
  by apply/forall_inP => P; case/SylowE3.
have regEE3: 'C_E3(E) = 1.
  have [// | [p p_pr]] := trivgVpdiv 'C_E3(E).
  case/Cauchy=> // x /setIP[]; rewrite -!cycle_subG => sXE3 cEX ox.
  have pX: p.-elt x by rewrite /p_elt ox pnat_id.
  have [P sylP sXP] := Sylow_superset sXE3 pX.
  suffices: <[x]> == 1 by case/idPn; rewrite cycle_eq1 -order_gt1 ox prime_gt1.
  rewrite -subG1; case/SylowE3: (p_Sylow sylP) => _ _ <-.
  by rewrite subsetI sXP.
have nsE3E: E3 <| E.
  have hallE3_E' := pHall_subl sE3E'  (der_sub 1 E) hallE3.
  by rewrite (nilpotent_Hall_pcore nilE' hallE3_E') /=.
have [sE2E t2E2 _] := and3P hallE2; have [_ nE3E] := andP nsE3E.
have coE21: coprime #|E2| #|E1| := sub_pnat_coprime tau2'1 t2E2 t1E1.
have coE31: coprime #|E3| #|E1| := sub_pnat_coprime tau3'1 t3E3 t1E1.
have coE32: coprime #|E3| #|E2| := sub_pnat_coprime tau3'2 t3E3 t2E2.
have{groupE21} defE: E3 ><| (E2 ><| E1) = E.
  have defE21: E2 * E1 = E2 <*> E1 by rewrite -genM_join gen_set_id.
  have sE21E: E2 <*> E1 \subset E by rewrite join_subG sE2E.
  have nE3E21 := subset_trans sE21E nE3E.
  have coE312: coprime #|E3| #|E2 <*> E1|.
    by rewrite -defE21 coprime_cardMg // coprime_mulr coE32.
  have nE21: E1 \subset 'N(E2).
    rewrite (subset_trans (joing_subr E2 E1)) ?sub_der1_norm ?joing_subl //.
    rewrite /= -{2}(mulg1 E2) -(setIidPr (der_sub 1 _)) /=.
    rewrite -(coprime_mulG_setI_norm defE21) ?gFnorm //.
    by rewrite mulgSS ?subsetIl // -tiE'E1 setIC setSI ?dergS.
  rewrite (sdprodEY nE21) ?sdprodE ?coprime_TIg //=.
  apply/eqP; rewrite eqEcard mul_subG // coprime_cardMg //= -defE21.
  rewrite -(partnC \tau3(M) (cardG_gt0 E)) (card_Hall hallE3) leq_mul //.
  rewrite coprime_cardMg // (card_Hall hallE1) (card_Hall hallE2).
  rewrite -[#|E|`__](partnC \tau2(M)) ?leq_mul ?(partn_part _ tau3'2) //.
  rewrite -partnI dvdn_leq // sub_in_partn // => p piEp; apply/implyP.
  rewrite inE /= -negb_or /= orbC implyNb orbC.
  by rewrite -(partition_pi_sigma_compl maxM hallE).
split=> // [/eqP E2_1|]; last split=> //.
  apply: contraTneq (sol_der1_proper solM (subxx _) (mmax_neq1 maxM)) => E1_1.
  case/sdprodP: (sdprod_sigma maxM hallE) => _ defM _ _.
  rewrite properE der_sub /= negbK -{1}defM mulG_subG Msigma_der1 //.
  by rewrite -defE E1_1 E2_1 !sdprodg1 (subset_trans sE3E') ?dergS //.
case/sdprodP: defE => [[_ E21 _ defE21]]; rewrite defE21 => defE nE321 tiE321.
have{defE21} [_ defE21 nE21 tiE21] := sdprodP defE21.
have [nE32 nE31] := (subset_trans sE2E nE3E, subset_trans sE1E nE3E).
rewrite [E3 ><| _]sdprodEY ? sdprodE ?coprime_TIg ?normsY //=.
  by rewrite norm_joinEr // -mulgA defE21.
by rewrite norm_joinEr // coprime_cardMg // coprime_mull coE31.
Qed.

(* This is B & G, Lemma 12.2(a). *)
Lemma prime_class_mmax_norm M p X :
     M \in 'M -> p.-group X -> 'N(X) \subset M ->
  (p \in \sigma(M)) || (p \in \tau2(M)).
Proof.
move=> maxM pX sNM; rewrite -implyNb; apply/implyP=> sM'p. 
by rewrite 3!inE /= sM'p (sigma'_norm_mmax_rank2 _ _ pX).
Qed.

(* This is B & G, Lemma 12.2(b). *)
Lemma mmax_norm_notJ M Mstar p X :
    M \in 'M -> Mstar \in 'M ->
    p.-group X -> X \subset M -> 'N(X) \subset Mstar ->
    [|| [&& p \in \sigma(M) & M :!=: Mstar], p \in \tau1(M) | p \in \tau3(M)] ->
  gval Mstar \notin M :^: G.
Proof.
move: Mstar => H maxM maxH pX sXM sNH; apply: contraL => MG_H.
have [x Gx defH] := imsetP MG_H.
have [sMp | sM'p] := boolP (p \in \sigma(M)); last first.
  have:= prime_class_mmax_norm maxH pX sNH.
  rewrite defH /= sigmaJ tau2J !negb_or (negPf sM'p) /= => t2Mp.
  by rewrite (contraL (@tau2'1 _ p)) // [~~ _]tau3'2.
rewrite 3!inE sMp 3!inE sMp orbF negbK.
have [_ transCX _] := sigma_group_trans maxM sMp pX.
set maxMX := finset _ in transCX.
have maxMX_H: gval H \in maxMX by rewrite inE MG_H (subset_trans (normG X)).
have maxMX_M: gval M \in maxMX by rewrite inE orbit_refl.
have [y cXy ->] := atransP2 transCX maxMX_H maxMX_M.
by rewrite /= conjGid // (subsetP sNH) // (subsetP (cent_sub X)).
Qed.

(* This is B & G, Lemma 12.3. *)
Lemma nonuniq_p2Elem_cent_sigma M Mstar p A A0 :
    M \in 'M -> Mstar \in 'M -> Mstar :!=: M -> A \in 'E_p^2(M) ->
    A0 \in 'E_p^1(A) -> 'N(A0) \subset Mstar ->
 [/\ (*a*) p \notin \sigma(M) -> A \subset 'C(M`_\sigma :&: Mstar)
   & (*b*) p \notin \alpha(M) -> A \subset 'C(M`_\alpha :&: Mstar)].
Proof.
move: Mstar => H maxM maxH neqMH Ep2A EpA0 sNH.
have p_pr := pnElem_prime Ep2A.
have [sAM abelA dimA] := pnElemP Ep2A; have [pA cAA _] := and3P abelA.
have [sA0A _ _] := pnElemP EpA0; have pA0 := pgroupS sA0A pA.
have sAH: A \subset H.
  by apply: subset_trans (cents_norm _) sNH; exact: subset_trans (centS sA0A).
have nsHsH: H`_\sigma <| H by exact: pcore_normal.
have [sHsH nHsH] := andP nsHsH; have nHsA := subset_trans sAH nHsH.
have nsHsA_H: H`_\sigma <*> A <| H.
  have [sHp | sH'p] := boolP (p \in \sigma(H)).
    rewrite (joing_idPl _) ?pcore_normal //.
    by rewrite (sub_Hall_pcore (Msigma_Hall _)) // (pi_pgroup pA).
  have [P sylP sAP] := Sylow_superset sAH pA.
  have excH: exceptional_FTmaximal p H A0 A by split=> //; apply/pnElemP.
  exact: exceptional_mul_sigma_normal excH sylP sAP.
have cAp' K:
    p^'.-group K -> A \subset 'N(K) -> K \subset H ->
  [~: K, A] \subset K :&: H`_\sigma.
- move=> p'K nKA sKH; have nHsK := subset_trans sKH nHsH.
  rewrite subsetI commg_subl nKA /= -quotient_sub1 ?comm_subG // quotientR //=.
  have <-: K / H`_\sigma :&: A / H`_\sigma = 1.
    by rewrite setIC coprime_TIg ?coprime_morph ?(pnat_coprime pA p'K).
  rewrite subsetI commg_subl commg_subr /= -{2}(quotientYidr nHsA).
  by rewrite !quotient_norms //= joingC (subset_trans sKH) ?normal_norm.
have [sMp | sM'p] := boolP (p \in \sigma(M)).
  split=> // aM'p; have notMGH: gval H \notin M :^: G.
    apply: mmax_norm_notJ maxM maxH pA0 (subset_trans sA0A sAM) sNH _.
    by rewrite sMp eq_sym neqMH.
  rewrite centsC (sameP commG1P trivgP).
  apply: subset_trans (cAp' _ _ _ (subsetIr _ _)) _.
  - exact: pi_p'group (pgroupS (subsetIl _ _) (pcore_pgroup _ _)) aM'p.
  - by rewrite (normsI _ (normsG sAH)) // (subset_trans sAM) ?gFnorm.
  by rewrite setIAC; case/sigma_disjoint: notMGH => // -> _ _; exact: subsetIl.
suffices cMaA: A \subset 'C(M`_\sigma :&: H).
  by rewrite !{1}(subset_trans cMaA) ?centS ?setSI // Malpha_sub_Msigma.
have [sHp | sH'p] := boolP (p \in \sigma(H)); last first.
  apply/commG1P; apply: contraNeq neqMH => ntA_MsH.
  have [P sylP sAP] := Sylow_superset sAH pA.
  have excH: exceptional_FTmaximal p H A0 A by split=> //; exact/pnElemP.
  have maxAM: M \in 'M(A) by exact/setIdP.
  rewrite (exceptional_sigma_uniq maxH excH sylP sAP maxAM) //.
  apply: contraNneq ntA_MsH => tiMsHs; rewrite -subG1.
  have [sHsA_H nHsA_H] := andP nsHsA_H.
  have <-: H`_\sigma <*> A :&: M`_\sigma = 1.
    apply/trivgP; rewrite -tiMsHs subsetI subsetIr /=.
    rewrite -quotient_sub1 ?subIset ?(subset_trans sHsA_H) //.
    rewrite quotientGI ?joing_subl //= joingC quotientYidr //.
    rewrite setIC coprime_TIg ?coprime_morph //.
    rewrite (pnat_coprime (pcore_pgroup _ _)) // (card_pnElem Ep2A).
    by rewrite pnat_exp ?orbF ?pnatE.
  rewrite commg_subI // subsetI ?joing_subr ?subsetIl. 
    by rewrite (subset_trans sAM) ?gFnorm.
  by rewrite setIC subIset ?nHsA_H.
have sAHs: A \subset H`_\sigma.
  by rewrite (sub_Hall_pcore (Msigma_Hall maxH)) // (pi_pgroup pA).
have [S sylS sAS] := Sylow_superset sAHs pA; have [sSHs pS _] := and3P sylS.
have nsHaH: H`_\alpha <| H := pcore_normal _ _; have [_ nHaH] := andP nsHaH.
have nHaS := subset_trans (subset_trans sSHs sHsH) nHaH.
have nsHaS_H: H`_\alpha <*> S <| H.
  rewrite -{2}(quotientGK nsHaH) (norm_joinEr nHaS) -quotientK //.
  rewrite cosetpre_normal; apply: char_normal_trans (quotient_normal _ nsHsH).
  rewrite /= (nilpotent_Hall_pcore _ (quotient_pHall _ sylS)) ?pcore_char //.
  exact: nilpotentS (quotientS _ (Msigma_der1 maxH)) (Malpha_quo_nil maxH).
rewrite (sameP commG1P trivgP).
have <-: H`_\alpha <*> S :&: M`_\sigma = 1.
  have: gval M \notin H :^: G.
    by apply: contra sM'p; case/imsetP=> x _ ->; rewrite sigmaJ.
  case/sigma_disjoint=> // _ ti_aHsM _.
  rewrite setIC coprime_TIg ?(pnat_coprime (pcore_pgroup _ _)) //=.
  rewrite norm_joinEr // [pnat _ _]pgroupM (pi_pgroup pS) // andbT.
  apply: sub_pgroup (pcore_pgroup _ _) => q aHq.
  by apply: contraFN (ti_aHsM q) => sMq; rewrite inE /= aHq.
rewrite commg_subI // subsetI ?subsetIl.
  by rewrite (subset_trans sAS) ?joing_subr ?(subset_trans sAM) ?gFnorm.
by rewrite setIC subIset 1?normal_norm.
Qed.

(* This is B & G, Proposition 12.4. *)
Proposition p2Elem_mmax M p A :
      M \in 'M -> A \in 'E_p^2(M) ->
    (*a*) 'C(A) \subset M
 /\ (*b*) ([forall A0 in 'E_p^1(A), 'M('N(A0)) != [set M]] ->
           [/\ p \in \sigma(M), M`_\alpha = 1 & nilpotent M`_\sigma]).
Proof.
move=> maxM Ep2A; have p_pr := pnElem_prime Ep2A.
have [sAM abelA dimA] := pnElemP Ep2A; have [pA cAA _] := and3P abelA.
have [EpAnonuniq |] := altP forall_inP; last first.
  rewrite negb_forall_in; case/exists_inP=> A0 EpA0; rewrite negbK.
  case/eqP/mem_uniq_mmax=> _ sNA0_M; rewrite (subset_trans _ sNA0_M) //.
  by have [sA0A _ _] := pnElemP EpA0; rewrite cents_norm // centS.
have{EpAnonuniq} sCMkApCA y: y \in A^# ->
  [/\ 'r('C_M(<[y]>)) <= 2,
      p \in \sigma(M)^' -> 'C_(M`_\sigma)[y] \subset 'C_M(A)
    & p \in \alpha(M)^' -> 'C_(M`_\alpha)[y] \subset 'C_M(A)].
- case/setD1P=> nty Ay; pose Y := <[y]>%G.
  rewrite -cent_cycle -[<[y]>]/(gval Y).
  have EpY: Y \in 'E_p^1(A).
    by rewrite p1ElemE // 2!inE cycle_subG Ay -orderE (abelem_order_p abelA) /=.
  have [sYA abelY dimY] := pnElemP EpY; have [pY _] := andP abelY.
  have [H maxNYH neqHM]: exists2 H, H \in 'M('N(Y)) & H \notin [set M].
    apply/subsetPn; rewrite subset1 negb_or EpAnonuniq //=.
    apply/set0Pn; have [|H] := (@mmax_exists _ 'N(Y)); last by exists H.
    rewrite mFT_norm_proper ?(mFT_pgroup_proper pY) //.
    by rewrite -rank_gt0 (rank_abelem abelY) dimY.
  have{maxNYH} [maxH sNYH] := setIdP maxNYH; rewrite inE -val_eqE /= in neqHM.
  have ->: 'r('C_M(Y)) <= 2.
    apply: contraR neqHM; rewrite -ltnNge => rCMYgt2.
    have uniqCMY: 'C_M(Y)%G \in 'U.
      by rewrite rank3_Uniqueness ?(sub_mmax_proper maxM) ?subsetIl.
    have defU: 'M('C_M(Y)) = [set M] by apply: def_uniq_mmax; rewrite ?subsetIl.
    rewrite (eq_uniq_mmax defU maxH) ?subIset //.
    by rewrite orbC (subset_trans (cent_sub Y)).
  have [cAMs cAMa] := nonuniq_p2Elem_cent_sigma maxM maxH neqHM Ep2A EpY sNYH.
  rewrite !{1}subsetI !{1}(subset_trans (subsetIl _ _) (pcore_sub _ _)).
  by split=> // [/cAMs | /cAMa]; rewrite centsC; apply: subset_trans;
     rewrite setIS ?(subset_trans (cent_sub Y)).
have ntA: A :!=: 1 by rewrite -rank_gt0 (rank_abelem abelA) dimA.
have ncycA: ~~ cyclic A by rewrite (abelem_cyclic abelA) dimA.
have rCMAle2: 'r('C_M(A)) <= 2.
  have [y Ay]: exists y, y \in A^# by apply/set0Pn; rewrite setD_eq0 subG1.
  have [rCMy _ _] := sCMkApCA y Ay; apply: leq_trans rCMy.
  by rewrite rankS // setIS // centS // cycle_subG; case/setIdP: Ay.
have sMp: p \in \sigma(M).
  apply: contraFT (ltnn 1) => sM'p; rewrite -dimA -(rank_abelem abelA).
  suffices cMsA: A \subset 'C(M`_\sigma).
    by rewrite -(setIidPl cMsA) sub'cent_sigma_rank1 // (pi_pgroup pA).
  have nMsA: A \subset 'N(M`_\sigma) by rewrite (subset_trans sAM) ?gFnorm.
  rewrite centsC /= -(coprime_abelian_gen_cent1 _ _ nMsA) //; last first.
    exact: pnat_coprime (pcore_pgroup _ _) (pi_pnat pA _).
  rewrite gen_subG; apply/bigcupsP=> y; case/sCMkApCA=> _ sCMsyCA _.
  by rewrite (subset_trans (sCMsyCA sM'p)) ?subsetIr.
have [P sylP sAP] := Sylow_superset sAM pA; have [sPM pP _] := and3P sylP.
pose Z := 'Ohm_1('Z(P)).
have sZA: Z \subset A.
  have maxA: A \in 'E*_p('C_M(A)).
    have sACMA: A \subset 'C_M(A) by rewrite subsetI sAM.
    rewrite (subsetP (p_rankElem_max _ _)) // !inE abelA sACMA.
    rewrite eqn_leq logn_le_p_rank /=; last by rewrite !inE sACMA abelA.
    by rewrite dimA (leq_trans (p_rank_le_rank _ _)).
  rewrite [Z](OhmE 1 (pgroupS (center_sub P) pP)) gen_subG.
  rewrite -(pmaxElem_LdivP p_pr maxA) -(setIA M) setIid setSI //=.
  by rewrite setISS // centS.
have{ntA} ntZ: Z != 1.
  by rewrite Ohm1_eq1 (center_nil_eq1 (pgroup_nil pP)) (subG1_contra sAP).
have rPle2: 'r(P) <= 2.
  have [z Zz ntz]: exists2 z, z \in Z & z \notin [1].
    by apply/subsetPn; rewrite subG1.
  have [|rCMz _ _] := sCMkApCA z; first by rewrite inE ntz (subsetP sZA).
  rewrite (leq_trans _ rCMz) ?rankS // subsetI sPM centsC cycle_subG.
  by rewrite (subsetP _ z Zz) // (subset_trans (Ohm_sub 1 _)) ?subsetIr.
have aM'p: p \in \alpha(M)^'.
   by rewrite !inE -leqNgt -(p_rank_Sylow sylP) -rank_pgroup.
have sMaCMA: M`_\alpha \subset 'C_M(A).
have nMaA: A \subset 'N(M`_\alpha) by rewrite (subset_trans sAM) ?gFnorm.
  rewrite -(coprime_abelian_gen_cent1 _ _ nMaA) //; last first.
    exact: (pnat_coprime (pcore_pgroup _ _) (pi_pnat pA _)).
  rewrite gen_subG; apply/bigcupsP=> y; case/sCMkApCA=> _ _ sCMayCA.
  by rewrite (subset_trans (sCMayCA aM'p)) ?subsetIr.
have Ma1: M`_\alpha = 1.
  have [q q_pr rMa]:= rank_witness M`_\alpha.
  apply: contraTeq rCMAle2; rewrite -ltnNge -rank_gt0 rMa p_rank_gt0 => piMa_q.
  have aMq: q \in \alpha(M) := pnatPpi (pcore_pgroup _ _) piMa_q.
  apply: leq_trans (rankS sMaCMA); rewrite rMa.
  have [Q sylQ] := Sylow_exists q M`_\alpha; rewrite -(p_rank_Sylow sylQ).
  by rewrite (p_rank_Sylow (subHall_Sylow (Malpha_Hall maxM) aMq sylQ)).
have nilMs: nilpotent M`_\sigma.
  rewrite (nilpotentS (Msigma_der1 maxM)) // (isog_nil (quotient1_isog _)).
  by rewrite -Ma1 Malpha_quo_nil.
rewrite (subset_trans (cents_norm (centS sZA))) ?(mmax_normal maxM) //.
apply: char_normal_trans (char_trans (Ohm_char 1 _) (center_char P)) _.
have{sylP} sylP: p.-Sylow(M`_\sigma) P.
  apply: pHall_subl _ (pcore_sub _ _) sylP.
  by rewrite (sub_Hall_pcore (Msigma_Hall maxM)) // (pi_pgroup pP).
by rewrite (nilpotent_Hall_pcore _ sylP) ?(char_normal_trans (pcore_char _ _)).
Qed.

(* This is B & G, Theorem 12.5(a) -- this part does not mention a specific   *)
(* rank 2 elementary abelian \tau_2(M) subgroup of M.                        *)

Theorem tau2_Msigma_nil M p : M \in 'M -> p \in \tau2(M) -> nilpotent M`_\sigma.
Proof.
move=> maxM t2Mp; have [sM'p /eqP rpM] := andP t2Mp.
have [A Ep2A] := p_rank_witness p M; rewrite rpM in Ep2A.
have [_]:= p2Elem_mmax maxM Ep2A; rewrite -negb_exists_in [p \in _](negPf sM'p).
have [[A0 EpA0 /eqP/mem_uniq_mmax[_ sNA0M _]] | _ [] //] := exists_inP.
have{EpA0 sNA0M} excM: exceptional_FTmaximal p M A0 A by [].
have [sAM abelA _] := pnElemP Ep2A; have [pA _] := andP abelA.
have [P sylP sAP] := Sylow_superset sAM pA.
exact: exceptional_sigma_nil maxM excM sylP sAP.
Qed.

(* This is B & G, Theorem 12.5 (b-f) -- the bulk of the Theorem. *)
Theorem tau2_context M p A (Ms := M`_\sigma) :
    M \in 'M -> p \in \tau2(M) -> A \in 'E_p^2(M) ->
  [/\ (*b*) forall P, p.-Sylow(M) P ->
                abelian P
             /\ (A \subset P -> 'Ohm_1(P) = A /\ ~~ ('N(P) \subset M)),
      (*c*)  Ms <*> A <| M,
      (*d*) 'C_Ms(A) = 1,
      (*e*) forall Mstar, Mstar \in 'M(A) :\ M -> Ms :&: Mstar = 1
    & (*f*) exists2 A1, A1 \in 'E_p^1(A) & 'C_Ms(A1) = 1].
Proof.
move=> maxM t2Mp Ep2A; have [sM'p _] := andP t2Mp.
have [_]:= p2Elem_mmax maxM Ep2A; rewrite -negb_exists_in [p \in _](negPf sM'p).
have [[A0 EpA0 /eqP/mem_uniq_mmax[_ sNA0M _]] | _ [] //] := exists_inP.
have{EpA0 sNA0M} excM: exceptional_FTmaximal p M A0 A by [].
have strM := exceptional_structure maxM excM.
have [sAM abelA dimA] := pnElemP Ep2A; have [pA cAA _] := and3P abelA.
have [P sylP sAP] := Sylow_superset sAM pA.
have nsMsA_M : Ms <*> A <| M := exceptional_mul_sigma_normal maxM excM sylP sAP.
have [_ regA [A1 EpA1 [_ _ [_ regA1 _]]]] := strM P sylP sAP.
split=> // [P1 sylP1 | {P sylP sAP A0 excM}H| ]; last by exists A1.
  split=> [|sAP1]; first exact: (exceptional_Sylow_abelian _ excM sylP).
  split; first by case/strM: sylP1.
  by apply: contra sM'p => sNP1M; apply/exists_inP; exists P1; rewrite // ?inE.
case/setD1P; rewrite -val_eqE /= => neqHM /setIdP[maxH sAH].
apply/trivgP; rewrite -regA subsetI subsetIl /=.
have Ep2A_H: A \in 'E_p^2(H) by apply/pnElemP.
have [_]:= p2Elem_mmax maxH Ep2A_H; rewrite -negb_exists_in.
have [[A0 EpA0 /eqP/mem_uniq_mmax[_ sNA0H _]]|_ [//|sHp _ nilHs]] := exists_inP.
  have [cMSH_A _]:= nonuniq_p2Elem_cent_sigma maxM maxH neqHM Ep2A EpA0 sNA0H.
  by rewrite centsC cMSH_A.
have [P sylP sAP] := Sylow_superset sAH pA; have [sPH pP _] := and3P sylP.
have sylP_Hs: p.-Sylow(H`_\sigma) P.
  rewrite (pHall_subl _ (pcore_sub _ _) sylP) //.
  by rewrite (sub_Hall_pcore (Msigma_Hall maxH)) // (pi_pgroup pP).
have nPH: H \subset 'N(P).
  rewrite (nilpotent_Hall_pcore nilHs sylP_Hs).
  by rewrite !(char_norm_trans (pcore_char _ _)) ?normG.
have coMsP: coprime #|M`_\sigma| #|P|.
  exact: pnat_coprime (pcore_pgroup _ _) (pi_pnat pP _).
rewrite (sameP commG1P trivgP) -(coprime_TIg coMsP) commg_subI ?setIS //.
by rewrite subsetI sAP (subset_trans sAM) ?gFnorm.
Qed.

(* This is B & G, Corollary 12.6 (a, b, c & f) -- i.e., the assertions that   *)
(* do not depend on the decomposition of the complement.                      *)
Corollary tau2_compl_context M E p A (Ms := M`_\sigma) :
    M \in 'M -> \sigma(M)^'.-Hall(M) E -> p \in \tau2(M) -> A \in 'E_p^2(E) ->
  [/\ (*a*) A <| E /\ 'E_p^1(E) = 'E_p^1(A),
      (*b*) [/\ 'C(A) \subset E, 'N_M(A) = E & ~~ ('N(A) \subset M)],
      (*c*) forall X, X \in 'E_p^1(E) -> 'C_Ms(X) != 1 -> 'M('C(X)) = [set M]
    & (*f*) forall Mstar,
              Mstar \in 'M -> gval Mstar \notin M :^: G ->
            Ms :&: Mstar`_\sigma = 1
         /\ [predI \sigma(M) & \sigma(Mstar)] =i pred0].
Proof.
move=> maxM hallE t2Mp Ep2A; have [sEM sM'E _] := and3P hallE.
have [p_pr [sM'p _]] := (pnElem_prime Ep2A, andP t2Mp).
have [sAE abelA dimA] := pnElemP Ep2A; have [pA cAA _] := and3P abelA.
have [_ mulMsE nMsE tiMsE] := sdprodP (sdprod_sigma maxM hallE).
have Ep2A_M: A \in 'E_p^2(M) by rewrite (subsetP (pnElemS _ _ sEM)).
have [syl_p_M nsMsAM regA tiMsMA _] := tau2_context maxM t2Mp Ep2A_M.
have nMsA: A \subset 'N(Ms) := subset_trans sAE nMsE.
have nsAE: A <| E.
  rewrite /normal sAE -(mul1g A) -tiMsE setIC group_modr // normsI ?normG //.
  by rewrite (subset_trans sEM) // -(norm_joinEr nMsA) normal_norm.
have sAsylE P: p.-Sylow(E) P -> 'Ohm_1(P) = A /\ ~~ ('N(P) \subset M).
  move=> sylP; have sylP_M: p.-Sylow(M) P by apply: (subHall_Sylow hallE).
  have [_] := syl_p_M P sylP_M; apply.
  exact: subset_trans (pcore_max pA nsAE) (pcore_sub_Hall sylP).
have not_sNA_M: ~~ ('N(A) \subset M).
  have [P sylP] := Sylow_exists p E; have [<-]:= sAsylE P sylP.
  exact: contra (subset_trans (char_norms (Ohm_char 1 P))).
have{sAsylE syl_p_M} defEpE: 'E_p^1(E) = 'E_p^1(A).
  apply/eqP; rewrite eqEsubset andbC pnElemS //.
  apply/subsetP=> X /pnElemP[sXE abelX dimX]; apply/pnElemP; split=> //.
  have [pX _ eX] := and3P abelX; have [P sylP sXP] := Sylow_superset sXE pX.
  have [<- _]:= sAsylE P sylP; have [_ pP _] := and3P sylP.
  by rewrite (OhmE 1 pP) sub_gen // subsetI sXP sub_LdivT.
have defNMA: 'N_M(A) = E.
  rewrite -mulMsE setIC -group_modr ?normal_norm //= setIC.
  rewrite coprime_norm_cent ?regA ?mul1g //.
  exact: (pnat_coprime (pcore_pgroup _ _) (pi_pnat pA _)).
have [sCAM _]: 'C(A) \subset M /\ _  := p2Elem_mmax maxM Ep2A_M.
have sCAE: 'C(A) \subset E by rewrite -defNMA subsetI sCAM cent_sub.
split=> // [X EpX | H maxH not_MGH]; last first.
  by case/sigma_disjoint: not_MGH => // _ _; apply; apply: tau2_Msigma_nil t2Mp.
rewrite defEpE in EpX; have [sXA abelX dimX] := pnElemP EpX.
have ntX: X :!=: 1 by rewrite -rank_gt0 (rank_abelem abelX) dimX.
apply: contraNeq => neq_maxCX_M.
have{neq_maxCX_M} [H]: exists2 H, H \in 'M('C(X)) & H \notin [set M].
  apply/subsetPn; rewrite subset1 negb_or neq_maxCX_M.
  by have [H maxH]:= mmax_exists (mFT_cent_proper ntX); apply/set0Pn; exists H.
case/setIdP=> maxH sCXH neqHM.
rewrite -subG1 -(tiMsMA H) ?setIS // inE neqHM inE maxH.
exact: subset_trans (sub_abelian_cent cAA sXA) sCXH.
Qed.

(* This is B & G, Corollary 12.6 (d, e) -- the parts that apply to a          *)
(* particular decomposition of the complement. We included an easy consequece *)
(* of part (a), that A is a subgroup of E2, as this is used implicitly later  *)
(* in sections 12 and 13.                                                     *)
Corollary tau2_regular M E E1 E2 E3 p A (Ms := M`_\sigma) :
    M \in 'M -> sigma_complement M E E1 E2 E3 ->
    p \in \tau2(M) -> A \in 'E_p^2(E) ->
  [/\ (*d*) semiregular Ms E3,
      (*e*) semiregular Ms 'C_E1(A)
          & A \subset E2].
Proof.
move=> maxM complEi t2Mp Ep2A; have p_pr := pnElem_prime Ep2A.
have [hallE hallE1 hallE2 hallE3 _] := complEi.
have [sEM sM'E _] := and3P hallE; have [sM'p _] := andP t2Mp.
have [sAE abelA dimA] := pnElemP Ep2A; have [pA cAA _] := and3P abelA.
have Ep2A_M: A \in 'E_p^2(M) by rewrite (subsetP (pnElemS _ _ sEM)).
have [_ _ _ tiMsMA _] := tau2_context maxM t2Mp Ep2A_M.
have [[nsAE _] _ _ _] := tau2_compl_context maxM hallE t2Mp Ep2A.
have [sCAM _]: 'C(A) \subset M /\ _  := p2Elem_mmax maxM Ep2A_M.
have sAE2: A \subset E2.
  exact: normal_sub_max_pgroup (Hall_max hallE2) (pi_pnat pA _) nsAE.
split=> // x /setD1P[ntx]; last first.
  case/setIP; rewrite -cent_cycle -!cycle_subG => sXE1 cAX.
  pose q := pdiv #[x]; have piXq: q \in \pi(#[x]) by rewrite pi_pdiv order_gt1.
  have [Q sylQ] := Sylow_exists q <[x]>; have [sQX qQ _] := and3P sylQ.
  have [sE1E t1E1 _] := and3P hallE1; have sQE1 := subset_trans sQX sXE1.
  have sQM := subset_trans sQE1 (subset_trans sE1E sEM).
  have [H /setIdP[maxH sNQH]]: {H | H \in 'M('N(Q))}.
    apply: mmax_exists; rewrite mFT_norm_proper ?(mFT_pgroup_proper qQ) //.
    by rewrite -rank_gt0 (rank_pgroup qQ) (p_rank_Sylow sylQ) p_rank_gt0.
  apply/trivgP; rewrite -(tiMsMA H) ?setIS //.
    by rewrite (subset_trans _ sNQH) ?cents_norm ?centS.
  rewrite 3!inE maxH /=; apply/andP; split.
    apply: contra_orbit (mmax_norm_notJ maxM maxH qQ sQM sNQH _).
    by rewrite (pnatPpi (pgroupS sXE1 t1E1)) ?orbT.
  by rewrite (subset_trans _ sNQH) ?cents_norm // centsC (subset_trans sQX).
rewrite -cent_cycle -cycle_subG => sXE3.
pose q := pdiv #[x]; have piXq: q \in \pi(#[x]) by rewrite pi_pdiv order_gt1.
have [Q sylQ] := Sylow_exists q <[x]>; have [sQX qQ _] := and3P sylQ.
have [sE3E t3E3 _] := and3P hallE3; have sQE3 := subset_trans sQX sXE3.
have sQM := subset_trans sQE3 (subset_trans sE3E sEM).
have [H /setIdP[maxH sNQH]]: {H | H \in 'M('N(Q))}.
  apply: mmax_exists; rewrite mFT_norm_proper ?(mFT_pgroup_proper qQ) //.
  by rewrite -rank_gt0 (rank_pgroup qQ) (p_rank_Sylow sylQ) p_rank_gt0.
apply/trivgP; rewrite -(tiMsMA H) ?setIS //.
  by rewrite (subset_trans _ sNQH) ?cents_norm ?centS.
rewrite 3!inE maxH /=; apply/andP; split.
  apply: contra_orbit (mmax_norm_notJ maxM maxH qQ sQM sNQH _).
  by rewrite (pnatPpi (pgroupS sXE3 t3E3)) ?orbT.
rewrite (subset_trans _ sNQH) ?cents_norm // (subset_trans _ (centS sQE3)) //.
have coE3A: coprime #|E3| #|A|.
  by rewrite (pnat_coprime t3E3 (pi_pnat pA _)) ?tau3'2.
rewrite (sameP commG1P trivgP) -(coprime_TIg coE3A) subsetI commg_subl.
have [[_ nsE3E] _ _ _ _] := sigma_compl_context maxM complEi.
by rewrite commg_subr (subset_trans sE3E) ?(subset_trans sAE) ?normal_norm.
Qed.

(* This is B & G, Theorem 12.7. *)
Theorem nonabelian_tau2 M E p A P0 (Ms := M`_\sigma) (A0 := 'C_A(Ms)%G) :
    M \in 'M -> \sigma(M)^'.-Hall(M) E -> p \in \tau2(M) -> A \in 'E_p^2(E) ->
    p.-group P0 -> ~~ abelian P0 ->
 [/\ (*a*) \tau2(M) =i (p : nat_pred),
     (*b*) #|A0| = p /\ Ms \x A0 = 'F(M),
     (*c*) forall X,
             X \in 'E_p^1(E) :\ A0 -> 'C_Ms(X) = 1 /\ ~~ ('C(X) \subset M)
   & (*d*) exists2 E0 : {group gT}, A0 ><| E0 = E
   & (*e*) forall x, x \in Ms^# -> {subset \pi('C_E0[x]) <= \tau1(M)}].
Proof.
rewrite {}/A0 => maxM hallE t2Mp Ep2A pP0 not_cP0P0 /=.
have p_pr := pnElem_prime Ep2A.
have [sEM sM'E _] := and3P hallE; have [sM'p _] := andP t2Mp.
have [sAE abelA dimA] := pnElemP Ep2A; have [pA cAA _] := and3P abelA.
have Ep2A_M: A \in 'E_p^2(M) by rewrite (subsetP (pnElemS _ _ sEM)).
have [[E1 hallE1] [E3 hallE3]] := ex_tau13_compl hallE.
have [E2 hallE2 complEi] := ex_tau2_compl hallE hallE1 hallE3.
have [regE3 _ sAE2] := tau2_regular maxM complEi t2Mp Ep2A.
have [P sylP sAP] := Sylow_superset sAE2 pA; have [sPE2 pP _] := and3P sylP.
have [S /= sylS sPS] := Sylow_superset (subsetT P) pP.
have pS := pHall_pgroup sylS; have sAS := subset_trans sAP sPS.
have sylP_E: p.-Sylow(E) P := subHall_Sylow hallE2 t2Mp sylP.
have sylP_M: p.-Sylow(M) P := subHall_Sylow hallE sM'p sylP_E.
have [syl_p_M _ regA _ _] := tau2_context maxM t2Mp Ep2A_M.
have{syl_p_M} cPP: abelian P by case: (syl_p_M P).
have{P0 pP0 not_cP0P0} not_cSS: ~~ abelian S.
  have [x _ sP0Sx] := Sylow_subJ sylS (subsetT P0) pP0.
  by apply: contra not_cP0P0 => cSS; rewrite (abelianS sP0Sx) ?abelianJ.
have [defP | ltPS] := eqVproper sPS; first by rewrite -defP cPP in not_cSS.
have [[nsAE defEp] [sCAE _ _] nregA _] :=
  tau2_compl_context maxM hallE t2Mp Ep2A.
have defCSA: 'C_S(A) = P.
  apply: (sub_pHall sylP_E (pgroupS (subsetIl _ _) pS)).
    by rewrite subsetI sPS (sub_abelian_cent2 cPP).
  by rewrite subIset // sCAE orbT.
have max2A: A \in 'E_p^2(G) :&: 'E*_p(G).
  by rewrite 3!inE subsetT abelA dimA; case: (tau2_not_beta maxM t2Mp) => _ ->.
have def_t2: \tau2(M) =i (p : nat_pred).
  move=> q; apply/idP/idP=> [t2Mq |]; last by move/eqnP->.
  apply: contraLR (proper_card ltPS); rewrite !inE /= eq_sym -leqNgt => q'p.
  apply: wlog_neg => p'q; have [B EqB] := p_rank_witness q E.
  have{EqB} Eq2B: B \in 'E_q^2(E).
    by move: t2Mq; rewrite (tau2E hallE) => /andP[_ /eqP <-].
  have [sBE abelB dimB]:= pnElemP Eq2B; have [qB _] := andP abelB.
  have coBA: coprime #|B| #|A| by exact: pnat_coprime qB (pi_pnat pA _).
  have [[nsBE _] [sCBE _ _] _ _] := tau2_compl_context maxM hallE t2Mq Eq2B.
  have nBA: A \subset 'N(B) by rewrite (subset_trans sAE) ?normal_norm.
  have cAB: B \subset 'C(A).
    rewrite (sameP commG1P trivgP) -(coprime_TIg coBA) subsetI commg_subl nBA.
    by rewrite commg_subr (subset_trans sBE) ?normal_norm.
  have{cAB} qCA: q %| #|'C(A)|.
    by apply: dvdn_trans (cardSg cAB); rewrite (card_pnElem Eq2B) dvdn_mull.
  have [Q maxQ sBQ] := max_normed_exists qB nBA.
  have nnQ: q.-narrow Q.
    apply/implyP=> _; apply/set0Pn; exists B.
    rewrite 3!inE sBQ abelB dimB (subsetP (pmaxElemS q (subsetT Q))) //=.
    rewrite setIC 2!inE sBQ; case: (tau2_not_beta maxM t2Mq) => _ -> //.
    by rewrite (subsetP (pnElemS _ _ sEM)).
  have [P1 [sylP1 _] [_ _]] := max_normed_2Elem_signaliser q'p max2A maxQ qCA.
  move/(_ nnQ)=> cQP1; have sylP1_E: p.-Sylow(E) P1.
    apply: pHall_subl (subset_trans _ sCBE) (subsetT E) sylP1.
    exact: subset_trans (centS sBQ).
  rewrite (card_Hall sylS) -(card_Hall sylP1).
  by rewrite (card_Hall sylP_E) -(card_Hall sylP1_E).
have coMsA: coprime #|Ms| #|A|.
  by exact: pnat_coprime (pcore_pgroup _ _) (pi_pnat pA _).
have defMs: <<\bigcup_(X in 'E_p^1(A)) 'C_Ms(X)>> = Ms.
  have ncycA: ~~ cyclic A by rewrite (abelem_cyclic abelA) dimA.
  have [sAM _ _] := pnElemP Ep2A_M.
  have{sAM} nMsA: A \subset 'N(Ms) by rewrite (subset_trans sAM) ?gFnorm.
  apply/eqP; rewrite eqEsubset andbC gen_subG.
  rewrite -{1}[Ms](coprime_abelian_gen_cent1 cAA ncycA nMsA coMsA).
  rewrite genS; apply/bigcupsP=> x; rewrite ?subsetIl //; case/setD1P=> ntx Ax.
  rewrite /= -cent_cycle (bigcup_max <[x]>%G) // p1ElemE // .
  by rewrite 2!inE cycle_subG Ax /= -orderE (abelem_order_p abelA).
have [A0 EpA0 nregA0]: exists2 A0, A0 \in 'E_p^1(A) & 'C_Ms(A0) != 1.
  apply/exists_inP; rewrite -negb_forall_in.
  apply: contra (Msigma_neq1 maxM); move/forall_inP => regAp.
  rewrite -/Ms -defMs -subG1 gen_subG; apply/bigcupsP=> X EpX.
  by rewrite subG1 regAp.
have uniqCA0: 'M('C(A0)) = [set M].
  by rewrite nregA // (subsetP (pnElemS _ _ sAE)).
have defSM: S :&: M = P.
  apply: sub_pHall (pgroupS (subsetIl S M) pS) _ (subsetIr S M) => //.
  by rewrite subsetI sPS (pHall_sub sylP_M).
have{ltPS} not_sSM: ~~ (S \subset M).
  by rewrite (sameP setIidPl eqP) defSM proper_neq.
have not_sA0Z: ~~ (A0 \subset 'Z(S)).
  apply: contra not_sSM; rewrite subsetI centsC; case/andP=> _ sS_CA0.
  by case/mem_uniq_mmax: uniqCA0 => _; exact: subset_trans sS_CA0.
have [EpZ0 dxCSA transNSA] := basic_p2maxElem_structure max2A pS sAS not_cSS.
do [set Z0 := 'Ohm_1('Z(S))%G; set EpA' := _ :\ Z0] in EpZ0 dxCSA transNSA.
have sZ0Z: Z0 \subset 'Z(S) := Ohm_sub 1 _.
have [sA0A _ _] := pnElemP EpA0; have sA0P := subset_trans sA0A sAP.
have EpA'_A0: A0 \in EpA'.
  by rewrite 2!inE EpA0 andbT; apply: contraNneq not_sA0Z => ->.
have{transNSA sAP not_sSM defSM} regA0' X:
  X \in 'E_p^1(E) :\ A0 -> 'C_Ms(X) = 1 /\ ~~ ('C(X) \subset M).
- case/setD1P=> neqXA0 EpX.
  suffices not_sCXM: ~~ ('C(X) \subset M).
    split=> //; apply: contraNeq not_sCXM => nregX.
    by case/mem_uniq_mmax: (nregA X EpX nregX).
  have [sXZ | not_sXZ] := boolP (X \subset 'Z(S)).
    apply: contra (subset_trans _) not_sSM.
    by rewrite centsC (subset_trans sXZ) ?subsetIr.
  have EpA'_X: X \in EpA'.
    by rewrite 2!inE -defEp EpX andbT; apply: contraNneq not_sXZ => ->.
  have [g NSAg /= defX] := atransP2 transNSA EpA'_A0 EpA'_X.
  have{NSAg} [Sg nAg] := setIP NSAg.
  have neqMgM: M :^ g != M.
    rewrite (sameP eqP normP) (norm_mmax maxM); apply: contra neqXA0 => Mg.
    rewrite defX [_ == _](sameP eqP normP) (subsetP (cent_sub A0)) //.
    by rewrite (subsetP (centSS (subxx _) sA0P cPP)) // -defSM inE Sg.
  apply: contra neqMgM; rewrite defX centJ sub_conjg.
  by move/(eq_uniq_mmax uniqCA0) => defM; rewrite -{1}defM ?mmaxJ ?actKV.
have{defMs} defA0: 'C_A(Ms) = A0.
  apply/eqP; rewrite eq_sym eqEcard subsetI sA0A (card_pnElem EpA0).
  have pCA: p.-group 'C_A(Ms) := pgroupS (subsetIl A _) pA.
  rewrite andbC (card_pgroup pCA) leq_exp2l ?prime_gt1 // -ltnS -dimA.
  rewrite properG_ltn_log //=; last first.
    rewrite properE subsetIl /= subsetI subxx centsC -(subxx Ms) -subsetI.
    by rewrite regA subG1 Msigma_neq1.
  rewrite centsC -defMs gen_subG (big_setD1 A0) //= subUset subsetIr /=.
  by apply/bigcupsP=> X; rewrite -defEp; case/regA0'=> -> _; rewrite sub1G.
rewrite defA0 (group_inj defA0) (card_pnElem EpA0).
have{dxCSA} [Y [cycY sZ0Y]] := dxCSA; move/(_ _ EpA'_A0)=> dxCSA.
have defCP_Ms: 'C_P(Ms) = A0.
  move: dxCSA; rewrite defCSA => /dprodP[_ mulA0Y cA0Y tiA0Y].
  rewrite -mulA0Y -group_modl /=; last by rewrite -defA0 subsetIr.
  rewrite setIC TI_Ohm1 ?mulg1 // setIC.
  have pY: p.-group Y by rewrite (pgroupS _ pP) // -mulA0Y mulG_subr.
  have cYY: abelian Y := cyclic_abelian cycY.
  have ->: 'Ohm_1(Y) = Z0.
    apply/eqP; rewrite eq_sym eqEcard (card_pnElem EpZ0) /= -['Ohm_1(_)]Ohm_id.
    rewrite OhmS // (card_pgroup (pgroupS (Ohm_sub 1 Y) pY)).
    rewrite leq_exp2l ?prime_gt1 -?p_rank_abelian // -rank_pgroup //.
    by rewrite -abelian_rank1_cyclic.
  rewrite prime_TIg ?(card_pnElem EpZ0) // centsC (sameP setIidPl eqP) eq_sym.
  case: (regA0' Z0) => [|-> _]; last exact: Msigma_neq1.
  by rewrite 2!inE defEp EpZ0 andbT; apply: contraNneq not_sA0Z => <-.
have [sPM pA0] := (pHall_sub sylP_M, pgroupS sA0A pA).
have cMsA0: A0 \subset 'C(Ms) by rewrite -defA0 subsetIr.
have nsA0M: A0 <| M.
  have [_ defM nMsE _] := sdprodP (sdprod_sigma maxM hallE).
  rewrite /normal (subset_trans sA0P) // -defM mulG_subG cents_norm 1?centsC //.
  by rewrite -defA0 normsI ?norms_cent // normal_norm.
have defFM: Ms \x A0 = 'F(M).
  have nilF := Fitting_nil M.
  rewrite dprodE ?(coprime_TIg (coprimegS sA0A coMsA)) //.
  have [_ /= defFM cFpp' _] := dprodP (nilpotent_pcoreC p nilF).
  have defFp': 'O_p^'('F(M)) = Ms.
    apply/eqP; rewrite eqEsubset.
    rewrite (sub_Hall_pcore (Msigma_Hall maxM)); last first.
      exact: subset_trans (pcore_sub _ _) (Fitting_sub _).
    rewrite /pgroup (sub_in_pnat _ (pcore_pgroup _ _)) => [|q piFq]; last first.
      have [Q sylQ] := Sylow_exists q 'F(M); have [sQF qQ _] := and3P sylQ.
      have ntQ: Q :!=: 1.
        rewrite -rank_gt0 (rank_pgroup qQ) (p_rank_Sylow sylQ) p_rank_gt0.
        by rewrite (piSg _ piFq) ?pcore_sub.
      have sNQM: 'N(Q) \subset M.
        rewrite (mmax_normal maxM) // (nilpotent_Hall_pcore nilF sylQ).
        by rewrite p_core_Fitting pcore_normal.
      apply/implyP; rewrite implyNb /= -def_t2 orbC. 
      by rewrite (prime_class_mmax_norm maxM qQ).
    rewrite pcore_max ?(pi_p'group (pcore_pgroup _ _)) //.
    rewrite /normal (subset_trans (Fitting_sub M)) ?gFnorm //.
    rewrite Fitting_max ?pcore_normal ?(tau2_Msigma_nil _ t2Mp) //.
  rewrite p_core_Fitting defFp' centsC in defFM cFpp'.
  rewrite -defFM (centC cFpp'); congr (Ms * _).
  apply/eqP; rewrite eqEsubset pcore_max //.
  by rewrite -defCP_Ms subsetI cFpp' pcore_sub_Hall.
split=> {defFM}//.
have [[sE1E t1E1 _] t2E2] := (and3P hallE1, pHall_pgroup hallE2).
have defE2: E2 :=: P by rewrite (sub_pHall sylP) // -(eq_pgroup _ def_t2) t2E2.
have [[_ nsE3E] _ _ [defEr _] _] := sigma_compl_context maxM complEi.
have [sE3E nE3E] := andP nsE3E; have{nE3E} nE3E := subset_trans _ nE3E.
have [[_ E21 _ defE21]] := sdprodP defEr; rewrite defE21 => defE nE321 tiE321.
rewrite defE2 in defE21; have{defE21} [_ defPE1 nPE1 tiPE1] := sdprodP defE21.
have [P0 defP nP0E1]: exists2 P0 : {group gT}, A0 \x P0 = P & E1 \subset 'N(P0).
  have p'E1b: p^'.-group (E1 / 'Phi(P)).
    rewrite quotient_pgroup //; apply: sub_pgroup t1E1 => q /tau2'1.
    by rewrite inE /= def_t2.
  have defPhiP: 'Phi(P) = 'Phi(Y).
    have [_ _ cA0Y tiA0Y] := dprodP dxCSA.
    rewrite defCSA dprodEcp // in dxCSA.
    have [_ abelA0 _] := pnElemP EpA0; rewrite -trivg_Phi // in abelA0.
    by rewrite -(Phi_cprod pP dxCSA) (eqP abelA0) cprod1g.
  have abelPb := Phi_quotient_abelem pP; have sA0Pb := quotientS 'Phi(P) sA0P.
  have [||P0b] := Maschke_abelem abelPb p'E1b sA0Pb; rewrite ?quotient_norms //.
    by rewrite (subset_trans (subset_trans sE1E sEM)) ?normal_norm.
  case/dprodP=> _ defPb _ tiAP0b nP0E1b.
  have sP0Pb: P0b \subset P / 'Phi(P) by rewrite -defPb mulG_subr.
  have [P0 defP0b sPhiP0 sP0P] := inv_quotientS (Phi_normal P) sP0Pb.
  exists P0; last first.
    rewrite -(quotientSGK (char_norm_trans (Phi_char P) nPE1)); last first.
      by rewrite cents_norm ?(sub_abelian_cent2 cPP (Phi_sub P) sP0P).
    by rewrite quotient_normG -?defP0b ?(normalS _ _ (Phi_normal P)).
  rewrite dprodEY ?(sub_abelian_cent2 cPP) //.
    apply/eqP; rewrite eqEsubset join_subG sA0P sP0P /=.
    rewrite -(quotientSGK (normal_norm (Phi_normal P))) //=; last first.
      by rewrite sub_gen // subsetU // sPhiP0 orbT.
    rewrite cent_joinEr ?(sub_abelian_cent2 cPP) //.
    rewrite quotientMr //; last by rewrite (subset_trans sP0P) ?gFnorm.
    by rewrite -defP0b defPb.
  apply/trivgP; case/dprodP: dxCSA => _ _ _ <-.
  rewrite subsetI subsetIl (subset_trans _ (Phi_sub Y)) // -defPhiP.
  rewrite -quotient_sub1 ?subIset ?(subset_trans sA0P) ?gFnorm //.
  by rewrite quotientIG // -defP0b tiAP0b.
have nA0E := subset_trans _ (subset_trans sEM (normal_norm nsA0M)).
have{defP} [_ defAP0 _ tiAP0] := dprodP defP.
have sP0P: P0 \subset P by rewrite -defAP0 mulG_subr.
have sP0E := subset_trans sP0P (pHall_sub sylP_E).
pose E0 := (E3 <*> (P0 <*> E1))%G.
have sP0E1_E: P0 <*> E1 \subset E by rewrite join_subG sP0E.
have sE0E:  E0 \subset E by rewrite join_subG sE3E.
have mulA0E0: A0 * E0 = E.
  rewrite /= (norm_joinEr (nE3E _ sP0E1_E)) mulgA -(normC (nA0E _ sE3E)).
  by rewrite /= -mulgA (norm_joinEr nP0E1) (mulgA A0) defAP0 defPE1.
have tiA0E0: A0 :&: E0 = 1.
  rewrite cardMg_TI // mulA0E0 -defE /= (norm_joinEr (nE3E _ sP0E1_E)).
  rewrite !TI_cardMg //; last first.
    by apply/trivgP; rewrite -tiE321 setIS //= ?norm_joinEr // -defPE1 mulSg.
  rewrite mulnCA /= leq_mul // norm_joinEr //= -defPE1.
  rewrite !TI_cardMg //; last by apply/trivgP; rewrite -tiPE1 setSI.
  by rewrite mulnA -(TI_cardMg tiAP0) defAP0.
have defAE0: A0 ><| E0 = E by rewrite sdprodE ?nA0E.
exists E0 => // x /setD1P[ntx Ms_x] q piCE0x_q.
have: q \in \pi(E) by apply: piSg piCE0x_q; rewrite subIset ?sE0E.
rewrite mem_primes in piCE0x_q; case/and3P: piCE0x_q => q_pr _.
case/Cauchy=> // z /setIP[E0z cxz] oz.
have ntz: z != 1 by rewrite -order_gt1 oz prime_gt1.
have ntCMs_z: 'C_Ms[z] != 1.
  apply: contraNneq ntx => reg_z; rewrite (sameP eqP set1gP) -reg_z inE Ms_x.
  by rewrite cent1C.
rewrite (partition_pi_sigma_compl maxM hallE) def_t2.
case/or3P => [-> // | pq | t3Mq].
  have EpA0'_z: <[z]>%G \in 'E_p^1(E) :\ A0.
    rewrite p1ElemE // !inE -orderE oz (eqnP pq) eqxx cycle_subG.
    rewrite (subsetP sE0E) // !andbT; apply: contraNneq ntz => eqA0z.
    by rewrite (sameP eqP set1gP) -tiA0E0 inE -eqA0z cycle_id E0z.
  have [reg_z _] := regA0' _ EpA0'_z.
  by rewrite -cent_cycle reg_z eqxx in ntCMs_z.
rewrite regE3 ?eqxx // !inE ntz /= in ntCMs_z.
by rewrite (mem_normal_Hall hallE3 nsE3E) ?(subsetP sE0E) // /p_elt oz pnatE.
Qed.

(* This is B & G, Theorem 12.8(c). This part does not use the decompotision   *)
(* of the complement, and needs to be proved ahead because it is used with    *)
(* different primes in \tau_2(M) in the main argument. We also include an     *)
(* auxiliary identity, which is needed in another part of the proof of 12.8.  *)
Theorem abelian_tau2_sub_Fitting M E p A S :
    M \in 'M -> \sigma(M)^'.-Hall(M) E ->
    p \in \tau2(M) -> A \in 'E_p^2(E) ->
    p.-Sylow(G) S -> A \subset S -> abelian S ->
  [/\        S \subset 'N(S)^`(1),
    'N(S)^`(1) \subset 'F(E),
         'F(E) \subset 'C(S),
         'C(S) \subset E
   &     'F('N(A)) = 'F(E)].
Proof.
move=> maxM hallE t2Mp Ep2A sylS sAS cSS.
have [sAE abelA dimA]:= pnElemP Ep2A; have [pA cAA _] := and3P abelA.
have [sEM sM'E _] := and3P hallE.
have Ep2A_M := subsetP (pnElemS p 2 sEM) A Ep2A.
have eqFC H: A <| H -> 'C(A) \subset H -> 'F(H) = 'F('C(A)).
  move=> nsAH sCH; have [_ nAH] := andP nsAH.
  apply/eqP; rewrite eqEsubset !Fitting_max ?Fitting_nil //.
    by rewrite (char_normal_trans (Fitting_char _)) // /normal sCH norms_cent.
  apply: normalS sCH (Fitting_normal H).
  have [_ defF cFpFp' _] := dprodP (nilpotent_pcoreC p (Fitting_nil H)).
  have sAFp: A \subset 'O_p('F(H)) by rewrite p_core_Fitting pcore_max.
  have [x _ sFpSx] := Sylow_subJ sylS (subsetT _) (pcore_pgroup p 'F(H)).
  have cFpFp: abelian 'O_p('F(H)) by rewrite (abelianS sFpSx) ?abelianJ.
  by rewrite -defF mulG_subG (centSS _ _ cFpFp) // (centSS _ _ cFpFp').
have [[nsAE _] [sCAE _] _ _ _] := tau2_compl_context maxM hallE t2Mp Ep2A.
have eqFN_FE: 'F('N(A)) = 'F(E) by rewrite (eqFC E) // eqFC ?cent_sub ?normalG.
have sN'FN: 'N(A)^`(1) \subset 'F('N(A)).
  rewrite rank2_der1_sub_Fitting ?mFT_odd //.
    rewrite ?mFT_sol // mFT_norm_proper ?(mFT_pgroup_proper pA) //.
    by rewrite -rank_gt0 (rank_abelem abelA) dimA.
  rewrite eqFN_FE (leq_trans (rankS (Fitting_sub E))) //.
  have [q q_pr ->]:= rank_witness E; apply: wlog_neg; rewrite -ltnNge => rEgt2.
  rewrite (leq_trans (p_rankS q sEM)) // leqNgt.
  apply: contra ((alpha_sub_sigma maxM) q) (pnatPpi sM'E _).
  by rewrite -p_rank_gt0 (leq_trans _ rEgt2).
have sSE: S \subset E by rewrite (subset_trans _ sCAE) // (centSS _ _ cSS).
have nA_NS: 'N(S) \subset 'N(A).
  have [ ] := tau2_context maxM t2Mp Ep2A_M; have sSM := subset_trans sSE sEM.
  have sylS_M: p.-Sylow(M) S := pHall_subl sSM (subsetT M) sylS.
  by case/(_ S) => // _ [// |<- _] _ _ _ _; exact: char_norms (Ohm_char 1 _).
have sS_NS': S \subset 'N(S)^`(1) := mFT_Sylow_der1 sylS.
have sNS'_FE: 'N(S)^`(1) \subset 'F(E).
  by rewrite -eqFN_FE (subset_trans (dergS 1 nA_NS)).
split=> //; last by rewrite (subset_trans (centS sAS)).
have sSFE := subset_trans sS_NS' sNS'_FE; have nilFE := Fitting_nil E.
have sylS_FE := pHall_subl sSFE (subsetT 'F(E)) sylS.
suff sSZF: S \subset 'Z('F(E)) by rewrite centsC (subset_trans sSZF) ?subsetIr.
have [_ <- _ _] := dprodP (center_dprod (nilpotent_pcoreC p nilFE)).
by rewrite -(nilpotent_Hall_pcore nilFE sylS_FE) (center_idP cSS) mulG_subl.
Qed.

(* This is B & G, Theorem 12.8(a,b,d,e) -- the bulk of the Theorem. We prove  *)
(* part (f) separately below, as it does not depend on a decomposition of the *)
(* complement.                                                                *)
Theorem abelian_tau2 M E E1 E2 E3 p A S (Ms := M`_\sigma) :
    M \in 'M -> sigma_complement M E E1 E2 E3 ->
    p \in \tau2(M) -> A \in 'E_p^2(E) ->
    p.-Sylow(G) S -> A \subset S -> abelian S ->
  [/\ (*a*) E2 <| E /\ abelian E2,
      (*b*) \tau2(M).-Hall(G) E2,
      (*d*) [/\       'N(A) = 'N(S),
                      'N(S) = 'N(E2),
                     'N(E2) = 'N(E3 <*> E2)
            & 'N(E3 <*> E2) = 'N('F(E))]
    & (*e*) forall X, X \in 'E^1(E1) -> 'C_Ms(X) = 1 -> X \subset 'Z(E)].
Proof.
move=> maxM complEi t2Mp Ep2A sylS sAS cSS.
have [hallE hallE1 hallE2 hallE3 _] := complEi.
have [sEM sM'E _] := and3P hallE.
have [sE1E t1E1 _] := and3P hallE1.
have [sE2E t2E2 _] := and3P hallE2.
have [sE3E t3E3 _] := and3P hallE3.
have nilF: nilpotent 'F(E) := Fitting_nil E.
have sylE2_sylG_ZFE q Q:
  q.-Sylow(E2) Q -> Q :!=: 1 -> q.-Sylow(G) Q /\ Q \subset 'Z('F(E)).
- move=> sylQ ntQ; have [sQE2 qQ _] := and3P sylQ.
  have piQq: q \in \pi(Q) by rewrite -p_rank_gt0 -rank_pgroup // rank_gt0.
  have t2Mq: q \in \tau2(M) by rewrite (pnatPpi t2E2) // (piSg sQE2).
  have sylQ_E: q.-Sylow(E) Q := subHall_Sylow hallE2 t2Mq sylQ.
  have rqQ: 'r_q(Q) = 2.
    rewrite (tau2E hallE) !inE -(p_rank_Sylow sylQ_E) in t2Mq.
    by case/andP: t2Mq => _ /eqP.
  have [B Eq2B sBQ]: exists2 B, B \in 'E_q^2(E) & B \subset Q.
    have [B Eq2B] := p_rank_witness q Q; have [sBQ abelB rBQ] := pnElemP Eq2B.
    exists B; rewrite // !inE rBQ rqQ abelB !andbT.
    exact: subset_trans sBQ (pHall_sub sylQ_E).
  have [T /= sylT sQT] := Sylow_superset (subsetT Q) qQ.
  have qT: q.-group T := pHall_pgroup sylT.
  have cTT: abelian T.
    apply: wlog_neg => not_cTT.
    have [def_t2 _ _ _] := nonabelian_tau2 maxM hallE t2Mq Eq2B qT not_cTT.
    rewrite def_t2 !inE in t2Mp; rewrite (eqP t2Mp) in sylS.
    by have [x _ ->] := Sylow_trans sylS sylT; rewrite abelianJ.
  have sTF: T \subset 'F(E).
    have subF := abelian_tau2_sub_Fitting maxM hallE t2Mq Eq2B sylT.
    have [sTN' sN'F _ _ _] := subF (subset_trans sBQ sQT) cTT.
    exact: subset_trans sTN' sN'F.
  have sTE: T \subset E := subset_trans sTF (Fitting_sub E).
  have <-: T :=: Q by apply: (sub_pHall sylQ_E).
  have sylT_F: q.-Sylow('F(E)) T := pHall_subl sTF (subsetT _) sylT.
  have [_ <- _ _] := dprodP (center_dprod (nilpotent_pcoreC q nilF)).
  by rewrite -(nilpotent_Hall_pcore nilF sylT_F) (center_idP cTT) mulG_subl.
have hallE2_G: \tau2(M).-Hall(G) E2.
  rewrite pHallE subsetT /= -(part_pnat_id t2E2); apply/eqnP.
  rewrite !(widen_partn _ (subset_leq_card (subsetT _))).
  apply: eq_bigr => q t2q; rewrite -!p_part.
  have [Q sylQ] := Sylow_exists q E2; have qQ := pHall_pgroup sylQ.
  have sylQ_E: q.-Sylow(E) Q := subHall_Sylow hallE2 t2q sylQ.
  have ntQ: Q :!=: 1.
    rewrite -rank_gt0 (rank_pgroup qQ) (p_rank_Sylow sylQ_E) p_rank_gt0.
    by rewrite (tau2E hallE) in t2q; case/andP: t2q.
  have [sylQ_G _] := sylE2_sylG_ZFE q Q sylQ ntQ.
  by rewrite -(card_Hall sylQ) -(card_Hall sylQ_G).
have sE2_ZFE: E2 \subset 'Z('F(E)).
  rewrite -Sylow_gen gen_subG; apply/bigcupsP=> Q; case/SylowP=> q q_pr sylQ.
  have [-> | ntQ] := eqsVneq Q 1; first exact: sub1G.
  by have [_ ->] := sylE2_sylG_ZFE q Q sylQ ntQ.
have cE2E2: abelian E2 := abelianS sE2_ZFE (center_abelian _).
have sE2FE: E2 \subset 'F(E) := subset_trans sE2_ZFE (center_sub _).
have nsE2E: E2 <| E.
  have hallE2_F := pHall_subl sE2FE (Fitting_sub E) hallE2.
  rewrite (nilpotent_Hall_pcore nilF hallE2_F).
  exact: char_normal_trans (pcore_char _ _) (Fitting_normal E).
have [_ _ [cycE1 cycE3] [_ defEl] _] := sigma_compl_context maxM complEi.
have [[K _ defK _] _ _ _] := sdprodP defEl; rewrite defK in defEl.
have [nsKE _ mulKE1 nKE1 _] := sdprod_context defEl; have [sKE _] := andP nsKE.
have [nsE3K sE2K _ nE32 tiE32] := sdprod_context defK.
rewrite -sdprodEY // defK.
have{defK} defK: E3 \x E2 = K.
  rewrite dprodEsd // (sameP commG1P trivgP) -tiE32 subsetI commg_subr nE32.
  by rewrite commg_subl (subset_trans sE3E) ?normal_norm.
have cKK: abelian K.
  by have [_ <- cE23 _] := dprodP defK; rewrite abelianM cE2E2 cyclic_abelian.
have [_ sNS'F _ sCS_E defFN] :=
  abelian_tau2_sub_Fitting maxM hallE t2Mp Ep2A sylS sAS cSS.
have{sCS_E} sSE2: S \subset E2.
  rewrite (sub_normal_Hall hallE2 nsE2E (subset_trans cSS sCS_E)).
  by rewrite (pi_pgroup (pHall_pgroup sylS)).
have charS: S \char E2.
  have sylS_E2: p.-Sylow(E2) S := pHall_subl sSE2 (subsetT E2) sylS.
  by rewrite (nilpotent_Hall_pcore (abelian_nil cE2E2) sylS_E2) pcore_char.
have nsSE: S <| E := char_normal_trans charS nsE2E; have [sSE nSE] := andP nsSE.
have charA: A \char S.
  have Ep2A_M := subsetP (pnElemS p 2 sEM) A Ep2A.
  have sylS_M := pHall_subl (subset_trans sSE sEM) (subsetT M) sylS.
  have [] := tau2_context maxM t2Mp Ep2A_M; case/(_ S sylS_M)=> _ [//|<- _].
  by rewrite Ohm_char.
have charE2: E2 \char K.
  have hallE2_K := pHall_subl sE2K sKE hallE2.
  by rewrite (nilpotent_Hall_pcore (abelian_nil cKK) hallE2_K) pcore_char.
have coKE1: coprime #|K| #|E1|.
  rewrite -(dprod_card defK) coprime_mull (sub_pnat_coprime tau3'1 t3E3 t1E1).
  by rewrite (sub_pnat_coprime tau2'1 t2E2 t1E1).
have hallK: Hall 'F(E) K.
  have hallK: Hall E K.
    by rewrite /Hall -divgS sKE //= -(sdprod_card defEl) mulKn.
  have sKFE: K \subset 'F(E) by rewrite Fitting_max ?abelian_nil.
  exact: pHall_Hall (pHall_subl sKFE (Fitting_sub E) (Hall_pi hallK)).
have charK: K \char 'F(E).
  by rewrite (nilpotent_Hall_pcore nilF (Hall_pi hallK)) pcore_char.
have{defFN} [eqNAS eqNSE2 eqNE2K eqNKF]:
  [/\ 'N(A) = 'N(S), 'N(S) = 'N(E2), 'N(E2) = 'N(K) & 'N(K) = 'N('F(E))].
  have: #|'N(A)| <= #|'N('F(E))|.
    by rewrite subset_leq_card // -defFN gFnorm.
  have leCN := subset_leqif_cards (@char_norms gT _ _ _).
  have trCN := leqif_trans (leCN _ _ _).
  have leq_KtoA := trCN _ _ _ _ charE2 (trCN _ _ _ _ charS (leCN _ _ charA)).
  rewrite (geq_leqif (trCN _ _ _ _ charK leq_KtoA)).
  by case/and4P; do 4!move/eqP->.
split=> // X E1_1_X regX.
have cK_NK': 'N(K)^`(1) \subset 'C(K).
  suffices sKZ: K \subset 'Z('F(E)).
    by rewrite -eqNE2K -eqNSE2 (centSS sNS'F sKZ) // centsC subsetIr.
  have{hallK} [pi hallK] := HallP hallK.
  have [_ <- _ _] := dprodP (center_dprod (nilpotent_pcoreC pi nilF)).
  by rewrite -(nilpotent_Hall_pcore nilF hallK) (center_idP cKK) mulG_subl.
have [q EqX] := nElemP E1_1_X; have [sXE1 abelX dimX] := pnElemP EqX.
have sXE := subset_trans sXE1 sE1E.
have nKX := subset_trans sXE (normal_norm nsKE).
have nCSX_NS: 'N(K) \subset 'N('C(K) * X).
  rewrite -(quotientGK (cent_normal _)) -quotientK ?norms_cent //.
  by rewrite morphpre_norms // sub_abelian_norm ?quotientS ?sub_der1_abelian.
have nKX_NS: 'N(S) \subset 'N([~: K, X]).
  have CK_K_1: [~: 'C(K), K] = 1 by apply/commG1P.
  rewrite eqNSE2 eqNE2K commGC -[[~: X, K]]mul1g -CK_K_1.
  by rewrite -commMG ?CK_K_1 ?norms1 ?normsR.
have not_sNKX_M: ~~ ('N([~: K, X]) \subset M).
  have [[sM'p _] sSM] := (andP t2Mp, subset_trans sSE sEM).
  apply: contra sM'p => sNKX_M; apply/existsP; exists S.
  by rewrite (pHall_subl sSM (subsetT _) sylS) // (subset_trans _ sNKX_M).
have cKX: K \subset 'C(X).
  apply: contraR not_sNKX_M; rewrite (sameP commG1P eqP) => ntKX.
  rewrite (mmax_normal maxM) //.
  have [sKM sM'K] := (subset_trans sKE sEM, pgroupS sKE sM'E).
  have piE1q: q \in \pi(E1).
    by rewrite -p_rank_gt0 -dimX logn_le_p_rank // inE sXE1.
  have sM'q: q \in \sigma(M)^' by rewrite (pnatPpi sM'E) // (piSg sE1E).
  have EpX_NK: X \in 'E_q^1('N_M(K)).
    by apply: subsetP EqX; rewrite pnElemS // subsetI (subset_trans sE1E).
  have q'K: q^'.-group K.
    by rewrite p'groupEpi ?coprime_pi' // in coKE1 *; apply: (pnatPpi coKE1).
  by have []:= commG_sigma'_1Elem_cyclic maxM sKM sM'K sM'q EpX_NK regX.
rewrite subsetI sXE /= -mulKE1 centM subsetI centsC cKX.
exact: subset_trans sXE1 (cyclic_abelian cycE1).
Qed.

(* This is B & G, Theorem 12.8(f). *)
Theorem abelian_tau2_norm_Sylow M E p A S :
    M \in 'M -> \sigma(M)^'.-Hall(M) E -> p \in \tau2(M) -> A \in 'E_p^2(E) ->
    p.-Sylow(G) S -> A \subset S -> abelian S ->
  forall X, X \subset 'N(S) -> 'C_S(X) <| 'N(S) /\ [~: S, X] <| 'N(S).
Proof.
move=> maxM hallE t2Mp Ep2A sylS sAS cSS X nSX.
have [_ sNS'F sFCS _ _] :=
   abelian_tau2_sub_Fitting maxM hallE t2Mp Ep2A sylS sAS cSS.
have{sNS'F sFCS} sNS'CS: 'N(S)^`(1) \subset 'C(S) := subset_trans sNS'F sFCS.
have nCSX_NS: 'N(S) \subset 'N('C(S) * X).
  rewrite -quotientK ?norms_cent // -{1}(quotientGK (cent_normal S)).
  by rewrite morphpre_norms // sub_abelian_norm ?quotientS ?sub_der1_abelian.
rewrite /normal subIset ?comm_subG ?normG //=; split.
  have ->: 'C_S(X) = 'C_S('C(S) * X).
    by rewrite centM setIA; congr (_ :&: _); rewrite (setIidPl _) // centsC.
  by rewrite normsI ?norms_cent.
have CS_S_1: [~: 'C(S), S] = 1 by exact/commG1P.
by rewrite commGC -[[~: X, S]]mul1g -CS_S_1 -commMG ?CS_S_1 ?norms1 ?normsR.
Qed.

(* This is B & G, Corollary 12.9. *)
Corollary tau1_act_tau2 M E p A q Q (Ms := M`_\sigma) :
    M \in 'M -> \sigma(M)^'.-Hall(M) E -> p \in \tau2(M) -> A \in 'E_p^2(E) ->
    q \in \tau1(M) -> Q \in 'E_q^1(E) -> 'C_Ms(Q) = 1 -> [~: A, Q] != 1 ->
 let A0 := [~: A, Q]%G in let A1 := ('C_A(Q))%G in
 [/\ (*a*) [/\ A0 \in 'E_p^1(A), 'C_A(Ms) = A0 & A0 <| M],
     (*b*) gval A0 \notin A1 :^: G
   & (*c*) A1 \in 'E_p^1(A) /\ ~~ ('C(A1) \subset M)].
Proof.
move=> maxM hallE t2Mp Ep2A t1Mq EqQ regQ ntA0 A0 A1.
have [sEM sM'E _] := and3P hallE.
have [sAE abelA dimA] := pnElemP Ep2A; have [pA cAA _] := and3P abelA.
have [sQE abelQ dimQ] := pnElemP EqQ; have [qQ _ _] := and3P abelQ.
have [p_pr q_pr] := (pnElem_prime Ep2A, pnElem_prime EqQ).
have p_gt1 := prime_gt1 p_pr.
have Ep2A_M := subsetP (pnElemS p 2 sEM) A Ep2A.
have [_ _ regA _ _] := tau2_context maxM t2Mp Ep2A_M.
have [[nsAE _] _ _ _] := tau2_compl_context maxM hallE t2Mp Ep2A.
have [_ nAE] := andP nsAE; have nAQ := subset_trans sQE nAE.
have coAQ: coprime #|A| #|Q|.
  exact: sub_pnat_coprime tau2'1 (pi_pnat pA t2Mp) (pi_pnat qQ t1Mq).
have defA: A0 \x A1 = A := coprime_abelian_cent_dprod nAQ coAQ cAA.
have [_ _ _ tiA01] := dprodP defA.
have [sAM sM'A] := (subset_trans sAE sEM, pgroupS sAE sM'E).
have sM'q: q \in \sigma(M)^' by case/andP: t1Mq.
have EqQ_NA: Q \in 'E_q^1('N_M(A)).
  by apply: subsetP EqQ; rewrite pnElemS // subsetI sEM.
have q'A: q^'.-group A.
  rewrite p'groupEpi ?coprime_pi' // in coAQ *.
  by apply: (pnatPpi coAQ); rewrite -p_rank_gt0 (p_rank_abelem abelQ) dimQ.
have [] := commG_sigma'_1Elem_cyclic maxM sAM sM'A sM'q EqQ_NA regQ q'A cAA.
rewrite -[[~: A, Q]]/(gval A0) -/Ms => cMsA0 cycA0 nsA0M.
have sA0A: A0 \subset A by rewrite commg_subl.
have EpA0: A0 \in 'E_p^1(A).
  have abelA0 := abelemS sA0A abelA; have [pA0 _] := andP abelA0.
  rewrite p1ElemE // !inE sA0A -(Ohm1_id abelA0) /=.
  by rewrite (Ohm1_cyclic_pgroup_prime cycA0 pA0).
have defA0: 'C_A(Ms) = A0.
  apply/eqP; rewrite eq_sym eqEcard subsetI sA0A cMsA0 (card_pnElem EpA0).
  have pCAMs: p.-group 'C_A(Ms) := pgroupS (subsetIl A _) pA.
  rewrite (card_pgroup pCAMs) leq_exp2l //= leqNgt.
  apply: contra (Msigma_neq1 maxM) => dimCAMs.
  rewrite eq_sym -regA (sameP eqP setIidPl) centsC (sameP setIidPl eqP).
  by rewrite eqEcard subsetIl (card_pnElem Ep2A) (card_pgroup pCAMs) leq_exp2l.
have EpA1: A1 \in 'E_p^1(A).
  rewrite p1ElemE // !inE subsetIl -(eqn_pmul2l (ltnW p_gt1)).
  by rewrite -{1}[p](card_pnElem EpA0) (dprod_card defA) (card_pnElem Ep2A) /=.
have defNA0: 'N(A0) = M by apply: mmax_normal.
have not_cA0Q: ~~ (Q \subset 'C(A0)).
  apply: contra ntA0 => cA0Q.
  by rewrite -subG1 -tiA01 !subsetI subxx sA0A centsC cA0Q.
have rqM: 'r_q(M) = 1%N by apply/eqP; case/and3P: t1Mq.
have q'CA0: q^'.-group 'C(A0).
  have [S sylS sQS] := Sylow_superset (subset_trans sQE sEM) qQ.
  have qS := pHall_pgroup sylS; rewrite -(p_rank_Sylow sylS) in rqM.
  have cycS: cyclic S by rewrite (odd_pgroup_rank1_cyclic qS) ?mFT_odd ?rqM.
  have ntS: S :!=: 1 by rewrite -rank_gt0 (rank_pgroup qS) rqM.
  have defS1: 'Ohm_1(S) = Q.
    apply/eqP; rewrite eq_sym eqEcard -{1}(Ohm1_id abelQ) OhmS //=.
    by rewrite (card_pnElem EqQ) (Ohm1_cyclic_pgroup_prime cycS qS).
  have sylSC: q.-Sylow('C(A0)) 'C_S(A0).
    by rewrite (Hall_setI_normal _ sylS) // -defNA0 cent_normal.
  rewrite -partG_eq1 ?cardG_gt0 // -(card_Hall sylSC) -trivg_card1 /=.
  by rewrite setIC TI_Ohm1 // defS1 setIC prime_TIg ?(card_pnElem EqQ).
do 2?split=> //.
  have: ~~ q^'.-group Q by rewrite /pgroup (card_pnElem EqQ) pnatE ?inE ?negbK.
  apply: contra; case/imsetP=> x _ defA01.
  rewrite defA01 centJ pgroupJ in q'CA0.
  by apply: pgroupS q'CA0; rewrite centsC subsetIr.
have [S sylS sAS] := Sylow_superset (subsetT A) pA.
have [cSS | not_cSS] := boolP (abelian S).
  have solE := sigma_compl_sol hallE.
  have [E1 hallE1 sQE1] := Hall_superset solE sQE (pi_pnat qQ t1Mq).
  have [E3 hallE3] := Hall_exists \tau3(M) solE.
  have [E2 _ complEi] := ex_tau2_compl hallE hallE1 hallE3.
  have [_ _ _ reg1Z] := abelian_tau2 maxM complEi t2Mp Ep2A sylS sAS cSS.
  have E1Q: Q \in 'E^1(E1).
    by apply/nElemP; exists q; rewrite // !inE sQE1 abelQ dimQ.
  rewrite (subset_trans (reg1Z Q E1Q regQ)) ?subIset // in not_cA0Q.
  by rewrite centS ?orbT // (subset_trans sA0A).
have pS := pHall_pgroup sylS.
have [_ _ not_cent_reg _] := nonabelian_tau2 maxM hallE t2Mp Ep2A pS not_cSS.
case: (not_cent_reg A1); rewrite // 2!inE (subsetP (pnElemS p 1 sAE)) // andbT.
by rewrite -val_eqE /= defA0 eq_sym; apply/(TIp1ElemP EpA0 EpA1).
Qed.

(* This is B & G, Corollary 12.10(a). *)
Corollary sigma'_nil_abelian M N :
  M \in 'M -> N \subset M -> \sigma(M)^'.-group N -> nilpotent N -> abelian N.
Proof.
move=> maxM sNM sM'N /nilpotent_Fitting defN.
apply/center_idP; rewrite -{2}defN -{defN}(center_bigdprod defN).
apply: eq_bigr => p _; apply/center_idP; set P := 'O_p(N).
have [-> | ntP] := eqVneq P 1; first exact: abelian1.
have [pP sPN]: p.-group P /\ P \subset N by rewrite pcore_sub pcore_pgroup.
have{sPN sNM sM'N} [sPM sM'P] := (subset_trans sPN sNM, pgroupS sPN sM'N).
have{sPM sM'P} [E hallE sPE] := Hall_superset (mmax_sol maxM) sPM sM'P.
suffices [S sylS cSS]: exists2 S : {group gT}, p.-Sylow(E) S & abelian S.
  by have [x _ sPS] := Sylow_subJ sylS sPE pP; rewrite (abelianS sPS) ?abelianJ.
have{N P sPE pP ntP} piEp: p \in \pi(E).
  by rewrite (piSg sPE) // -p_rank_gt0 -rank_pgroup // rank_gt0.
rewrite (partition_pi_sigma_compl maxM hallE) orbCA orbC -orbA in piEp.
have [[E1 hallE1] [E3 hallE3]] := ex_tau13_compl hallE.
have [E2 hallE2 complEi] := ex_tau2_compl hallE hallE1 hallE3.
have{complEi} [_ _ [cycE1 cycE3] _ _] := sigma_compl_context maxM complEi.
have{piEp} [t1p | t3p | t2p] := or3P piEp.
- have [S sylS] := Sylow_exists p E1.
  exists S; first exact: subHall_Sylow hallE1 t1p sylS.
  exact: abelianS (pHall_sub sylS) (cyclic_abelian cycE1).
- have [S sylS] := Sylow_exists p E3.
  exists S; first exact: subHall_Sylow hallE3 t3p sylS.
  exact: abelianS (pHall_sub sylS) (cyclic_abelian cycE3).
have [s'p rpM] := andP t2p; have [S sylS] := Sylow_exists p E; exists S => //.
have sylS_M := subHall_Sylow hallE s'p sylS.
have [A _ Ep2A] := ex_tau2Elem hallE t2p.
by have [/(_ S sylS_M)[]] := tau2_context maxM t2p Ep2A.
Qed.

(* This is B & G, Corollary 12.10(b), first assertion. *)
Corollary der_mmax_compl_abelian M E :
  M \in 'M -> \sigma(M)^'.-Hall(M) E -> abelian E^`(1).
Proof.
move=> maxM hallE; have [sEM s'E _] := and3P hallE.
have sE'E := der_sub 1 E; have sE'M := subset_trans sE'E sEM.
exact: sigma'_nil_abelian (pgroupS _ s'E) (der1_sigma_compl_nil maxM hallE).
Qed.

(* This is B & G, Corollary 12.10(b), second assertion. *)
(* Note that we do not require the full decomposition of the complement. *)
Corollary tau2_compl_abelian M E E2 :
   M \in 'M -> \sigma(M)^'.-Hall(M) E -> \tau2(M).-Hall(E) E2 -> abelian E2.
Proof.
move: E2 => F2 maxM hallE hallF2; have [sEM s'E _] := and3P hallE.
have [[E1 hallE1] [E3 hallE3]] := ex_tau13_compl hallE.
have [E2 hallE2 complEi] := ex_tau2_compl hallE hallE1 hallE3.
have solE: solvable E := sigma_compl_sol hallE.
have{solE hallF2} [x _ ->{F2}] := Hall_trans solE hallF2 hallE2.
have [-> | ntE] := eqsVneq E2 1; rewrite {x}abelianJ ?abelian1 //.
have [[p p_pr rpE2] [sE2E t2E2 _]] := (rank_witness E2, and3P hallE2).
have piE2p: p \in \pi(E2) by rewrite -p_rank_gt0 -rpE2 rank_gt0.
have t2p := pnatPpi t2E2 piE2p; have [A Ep2A _] := ex_tau2Elem hallE t2p.
have [_ abelA _] := pnElemP Ep2A; have [pA _] := andP abelA.
have [S /= sylS sAS] := Sylow_superset (subsetT A) pA.
have [cSS | not_cSS] := boolP (abelian S).
  by have [[_ cE2E2] _ _ _] := abelian_tau2 maxM complEi t2p Ep2A sylS sAS cSS.
have pS := pHall_pgroup sylS.
have [def_t2 _ _ _] := nonabelian_tau2 maxM hallE t2p Ep2A pS not_cSS.
apply: sigma'_nil_abelian (subset_trans _ sEM) (pgroupS _ s'E) _ => //.
by rewrite (eq_pgroup _ def_t2) in t2E2; exact: pgroup_nil t2E2.
Qed.

(* This is B & G, Corollary 12.10(c). *)
(* We do not really need a full decomposition of the complement in the first  *)
(* part, but this reduces the number of assumptions.                          *)
Corollary tau1_cent_tau2Elem_factor M E p A :
    M \in 'M -> \sigma(M)^'.-Hall(M) E -> p \in \tau2(M) -> A \in 'E_p^2(E) ->
  [/\ forall E1 E2 E3, sigma_complement M E E1 E2 E3 -> E3 * E2 \subset 'C_E(A),
      'C_E(A) <| E
    & \tau1(M).-group (E / 'C_E(A))].
Proof.
move=> maxM hallE t2p Ep2A; have sEM: E \subset M := pHall_sub hallE.
have nsAE: A <| E by case/(tau2_compl_context maxM): Ep2A => //; case.
have [sAE nAE]: A \subset E /\ E \subset 'N(A) := andP nsAE.
have nsCAE: 'C_E(A) <| E by rewrite norm_normalI ?norms_cent.
have [[E1 hallE1] [E3 hallE3]] := ex_tau13_compl hallE.
have [E2 hallE2 complEi] := ex_tau2_compl hallE hallE1 hallE3.
have{hallE1} [t1E1 sE3E] := (pHall_pgroup hallE1, pHall_sub hallE3).
have{nsAE} sAE2: A \subset E2.
  apply: subset_trans (pcore_max _ nsAE) (pcore_sub_Hall hallE2).
  by apply: pi_pnat t2p; case/pnElemP: Ep2A => _; case/andP.
have{complEi} defE: (E3 ><| E2) ><| E1 = E.
  by case/sigma_compl_context: complEi => // _ _ _ [_ ->].
have [[K _ defK _] _ _ _] := sdprodP defE; rewrite defK in defE.
have nsKE: K <| E by case/sdprod_context: defE.
have [[sKE nKE] [_ mulE32 nE32 tiE32]] := (andP nsKE, sdprodP defK).
have{sE3E} sK_CEA: K \subset 'C_E(A).
  have cE2E2: abelian E2 := tau2_compl_abelian maxM hallE hallE2.
  rewrite subsetI sKE -mulE32 mulG_subG (centsS sAE2 cE2E2) (sameP commG1P eqP).
  rewrite -subG1 -tiE32 subsetI commg_subl (subset_trans sAE2) //=.
  by rewrite (subset_trans _ sAE2) // commg_subr (subset_trans sE3E).
split=> // [_ F2 F3 [_ _ hallF2 hallF3 _] | ].
  have solE: solvable E := solvableS sEM (mmax_sol maxM).
  have [x2 Ex2 ->] := Hall_trans solE hallF2 hallE2. 
  have [x3 Ex3 ->] := Hall_trans solE hallF3 hallE3.
  rewrite mulG_subG !sub_conjg !(normsP (normal_norm nsCAE)) ?groupV //.
  by rewrite -mulG_subG mulE32.
have [f <-] := homgP (homg_quotientS nKE (normal_norm nsCAE) sK_CEA).
by rewrite morphim_pgroup // /pgroup -divg_normal // -(sdprod_card defE) mulKn.
Qed.

(* This is B & G, Corollary 12.10(d). *)
Corollary norm_noncyclic_sigma M p P :
    M \in 'M -> p \in \sigma(M) -> p.-group P -> P \subset M -> ~~ cyclic P ->
  'N(P) \subset M.
Proof.
move=> maxM sMp pP sPM ncycP.
have [A Ep2A]: exists A, A \in 'E_p^2(P).
  by apply/p_rank_geP; rewrite ltnNge -odd_pgroup_rank1_cyclic ?mFT_odd.
have [[sAP _ _] Ep2A_M] := (pnElemP Ep2A, subsetP (pnElemS p 2 sPM) A Ep2A).
have sCAM: 'C(A) \subset M by case/p2Elem_mmax: Ep2A_M.
have [_ _ <- //] := sigma_group_trans maxM sMp pP.
by rewrite mulG_subG subsetIl (subset_trans (centS sAP)).
Qed.

(* This is B & G, Corollary 12.10(e). *)
Corollary cent1_nreg_sigma_uniq M (Ms := M`_\sigma) x :
    M \in 'M -> x \in M^# -> \tau2(M).-elt x -> 'C_Ms[x] != 1 ->
 'M('C[x]) = [set M].
Proof.
move=> maxM /setD1P[ntx]; rewrite -cycle_subG => sMX t2x.
apply: contraNeq => MCx_neqM.
have{MCx_neqM} [H maxCxH neqHM]: exists2 H, H \in 'M('C[x]) & H \notin [set M].
  apply/subsetPn; have [H MCxH] := mmax_exists (mFT_cent1_proper ntx).
  by rewrite eqEcard cards1 (cardD1 H) MCxH andbT in MCx_neqM.
have sCxH: 'C[x] \subset H by case/setIdP: maxCxH.
have s'x: \sigma(M)^'.-elt x by apply: sub_pgroup t2x => p; case/andP.
have [E hallE sXE] := Hall_superset (mmax_sol maxM) sMX s'x.
have [sEM solE] := (pHall_sub hallE, sigma_compl_sol hallE).
have{sXE} [E2 hallE2 sXE2] := Hall_superset solE sXE t2x.
pose p := pdiv #[x].
have t2p: p \in \tau2(M) by rewrite (pnatPpi t2x) ?pi_pdiv ?order_gt1.
have [A Ep2A sAE2]: exists2 A, A \in 'E_p^2(M) & A \subset E2.
  have [A Ep2A_E EpA] := ex_tau2Elem hallE t2p.
  have [sAE abelA _] := pnElemP Ep2A_E; have [pA _] := andP abelA.
  have [z Ez sAzE2] := Hall_Jsub solE hallE2 sAE (pi_pnat pA t2p).
  by exists (A :^ z)%G; rewrite // -(normsP (normsG sEM) z Ez) pnElemJ.
have cE2E2: abelian E2 := tau2_compl_abelian maxM hallE hallE2.
have cxA: A \subset 'C[x] by rewrite -cent_cycle (sub_abelian_cent2 cE2E2).
have maxAH: H \in 'M(A) :\ M by rewrite inE neqHM (subsetP (mmax_ofS cxA)).
have [_ _ _ tiMsMA _] := tau2_context maxM t2p Ep2A.
by rewrite -subG1 -(tiMsMA H maxAH) setIS.
Qed.

(* This is B & G, Lemma 12.11. *)
Lemma primes_norm_tau2Elem M E p A Mstar :
    M \in 'M -> \sigma(M)^'.-Hall(M) E -> p \in \tau2(M) -> A \in 'E_p^2(E) ->
    Mstar \in 'M('N(A)) ->
 [/\ (*a*) {subset \tau2(M) <= [predD \sigma(Mstar) & \beta(Mstar)]},
     (*b*) [predU \tau1(Mstar) & \tau2(Mstar)].-group (E / 'C_E(A))
   & (*c*) forall q, q \in \pi(E / 'C_E(A)) -> q \in \pi('C_E(A)) ->
           [/\ q \in \tau2(Mstar),
               exists2 P, P \in 'Syl_p(G) & P <| Mstar
             & exists Q, [/\ Q \in 'Syl_q(G), Q \subset Mstar & abelian Q]]].
Proof.
move=> maxM hallE t2Mp Ep2A; move: Mstar.
have [sAE abelA dimA] := pnElemP Ep2A; have [pA cAA _] := and3P abelA.
have ntA: A :!=: 1 by exact: (nt_pnElem Ep2A).
have [sEM solE] := (pHall_sub hallE, sigma_compl_sol hallE).
have [_ nsCA_E t1CEAb] := tau1_cent_tau2Elem_factor maxM hallE t2Mp Ep2A.
have [sAM nCA_E] := (subset_trans sAE sEM, normal_norm nsCA_E).
have part_a H:
  H \in 'M('N(A)) -> {subset \tau2(M) <= [predD \sigma(H) & \beta(H)]}.
- case/setIdP=> maxH sNA_H q t2Mq.
  have sCA_H: 'C(A) \subset H := subset_trans (cent_sub A) sNA_H.
  have sAH := subset_trans cAA sCA_H.
  have sHp: p \in \sigma(H).
    have [// | t2Hp] := orP (prime_class_mmax_norm maxH pA sNA_H).
    apply: contraLR sNA_H => sH'p.
    have sH'A: \sigma(H)^'.-group A by apply: pi_pnat pA _.
    have [F hallF sAF] := Hall_superset (mmax_sol maxH) sAH sH'A.
    have Ep2A_F: A \in 'E_p^2(F) by apply/pnElemP.
    by have [_ [_ _ ->]]:= tau2_compl_context maxH hallF t2Hp Ep2A_F.
  rewrite inE /= -predI_sigma_beta //= negb_and /= orbC.
  have [-> /= _] := tau2_not_beta maxM t2Mq.
  have [B Eq2B]: exists B, B \in 'E_q^2('C(A)).
    have [E2 hallE2 sAE2] := Hall_superset solE sAE (pi_pnat pA t2Mp).
    have cE2E2: abelian E2 := tau2_compl_abelian maxM hallE hallE2.
    have [Q sylQ] := Sylow_exists q E2; have sQE2 := pHall_sub sylQ.
    have sylQ_E := subHall_Sylow hallE2 t2Mq sylQ.
    apply/p_rank_geP; apply: leq_trans (p_rankS q (centsS sAE2 cE2E2)).
    rewrite -(p_rank_Sylow sylQ) (p_rank_Sylow sylQ_E).
    by move: t2Mq; rewrite (tau2E hallE) => /andP[_ /eqP->].
  have [cAB abelB dimB] := pnElemP Eq2B; have sBH := subset_trans cAB sCA_H.
  have{Eq2B} Eq2B: B \in 'E_q^2(H) by apply/pnElemP.
  have rqHgt1: 'r_q(H) > 1 by apply/p_rank_geP; exists B.
  have piHq: q \in \pi(H) by rewrite -p_rank_gt0 ltnW.
  rewrite partition_pi_mmax // in piHq.
  case/or4P: piHq rqHgt1 => // [|t2Hq _|]; try by case/and3P=> _ /eqP->.
  have [_ _ regB _ _] := tau2_context maxH t2Hq Eq2B.
  case/negP: ntA; rewrite -subG1 -regB subsetI centsC cAB andbT.
  by rewrite (sub_Hall_pcore (Msigma_Hall maxH)) // (pi_pgroup pA).
have part_b H:
  H \in 'M('N(A)) -> [predU \tau1(H) & \tau2(H)].-group (E / 'C_E(A)).
- move=> maxNA_H; have [maxH sNA_H] := setIdP maxNA_H.
  have [/= bH'p sHp] := andP (part_a H maxNA_H p t2Mp).
  have sCA_H: 'C(A) \subset H := subset_trans (cent_sub A) sNA_H.
  have sAH := subset_trans cAA sCA_H.
  apply/pgroupP=> q q_pr q_dv_CEAb; apply: contraR bH'p => t12H'q.
  have [Q sylQ] := Sylow_exists q E; have [sQE qQ _] := and3P sylQ.
  have nsAE: A <| E by case/(tau2_compl_context maxM): Ep2A => //; case.
  have nAE := normal_norm nsAE; have nAQ := subset_trans sQE nAE.
  have sAQ_A: [~: A, Q] \subset A by rewrite commg_subl.
  have ntAQ: [~: A, Q] != 1.
    apply: contraTneq q_dv_CEAb => /commG1P cAQ.
    have nCEA_Q := subset_trans sQE nCA_E.
    rewrite -p'natE // -partn_eq1 ?cardg_gt0 //.
    rewrite -(card_Hall (quotient_pHall nCEA_Q sylQ)) -trivg_card1 -subG1.
    by rewrite quotient_sub1 // subsetI sQE centsC.
  have sQH: Q \subset H := subset_trans nAQ sNA_H.
  have sHsubH' r X:
    r \in \sigma(H) -> X \subset H -> r.-group X -> X \subset H^`(1).
  + move=> sHr sXH rX; apply: subset_trans (Msigma_der1 maxH).
    by rewrite (sub_Hall_pcore (Msigma_Hall maxH)) // (pi_pgroup rX sHr).
  have sAH': A \subset H^`(1) by apply: sHsubH' pA.
  have{t12H'q} sQH': Q \subset H^`(1).
    have [sHq | sH'q] := boolP (q \in \sigma(H)); first exact: sHsubH' qQ.
    have{sH'q} sH'Q: \sigma(H)^'.-group Q by apply: (pi_pnat qQ).
    have{sH'Q} [F hallF sQF] := Hall_superset (mmax_sol maxH) sQH sH'Q.
    have [-> | ntQ] := eqsVneq Q 1; first exact: sub1G.
    have{t12H'q} t3Hq: q \in \tau3(H).
      apply: implyP t12H'q; rewrite implyNb -orbA.
      rewrite -(partition_pi_sigma_compl maxH hallF) -p_rank_gt0.
      by rewrite (leq_trans _ (p_rankS q sQF)) // -rank_pgroup // rank_gt0.
    have solF: solvable F := sigma_compl_sol hallF.
    have [F3 hallF3 sQF3] := Hall_superset solF sQF (pi_pnat qQ t3Hq).
    have [[F1 hallF1] _] := ex_tau13_compl hallF.
    have [F2 _ complFi] := ex_tau2_compl hallF hallF1 hallF3.
    have [[sF3H' _] _ _ _ _] := sigma_compl_context maxH complFi.
    exact: subset_trans sQF3 (subset_trans sF3H' (dergS 1 (pHall_sub hallF))).
  have hallHb: \beta(H).-Hall(H) H`_\beta := Mbeta_Hall maxH.
  have nilH'b: nilpotent (H^`(1) / H`_\beta) := Mbeta_quo_nil maxH.
  have{nilH'b} sAQ_Hb: [~: A, Q] \subset H`_\beta.
    rewrite -quotient_cents2 ?(subset_trans _ (gFnorm _ _)) // centsC.
    rewrite (sub_nilpotent_cent2 nilH'b) ?quotientS ?coprime_morph //.
    rewrite (pnat_coprime (pi_pnat pA t2Mp) (pi_pnat qQ _)) ?tau2'1 //.
    by rewrite (pnatPpi t1CEAb) // mem_primes q_pr cardG_gt0.
  rewrite (pnatPpi (pHall_pgroup hallHb)) // (piSg sAQ_Hb) // -p_rank_gt0.
  by rewrite -(rank_pgroup (pgroupS sAQ_A pA)) rank_gt0.
move=> H maxNA_H; split; last 1 [move=> q piCEAb_q piCEAq] || by auto.
have [_ sHp]: _ /\ p \in \sigma(H) := andP (part_a H maxNA_H p t2Mp).
have{maxNA_H} [maxH sNA_H] := setIdP maxNA_H.
have{sNA_H} sCA_H: 'C(A) \subset H := subset_trans (cent_sub A) sNA_H.
have{piCEAq} [Q0 EqQ0]: exists Q0, Q0 \in 'E_q^1('C_E(A)).
  by apply/p_rank_geP; rewrite p_rank_gt0.
have [sQ0_CEA abelQ0 dimQ0]:= pnElemP EqQ0; have [qQ0 cQ0Q0 _] := and3P abelQ0.
have{sQ0_CEA} [sQ0E cAQ0]: Q0 \subset E /\ Q0 \subset 'C(A).
  by apply/andP; rewrite -subsetI.
have ntQ0: Q0 :!=: 1 by apply: (nt_pnElem EqQ0).
have{t1CEAb} t1Mq: q \in \tau1(M) := pnatPpi t1CEAb piCEAb_q.
have [Q sylQ sQ0Q] := Sylow_superset sQ0E qQ0; have [sQE qQ _] := and3P sylQ.
have [E1 hallE1 sQE1] := Hall_superset solE sQE (pi_pnat qQ t1Mq).
have rqE: 'r_q(E) = 1%N.
  by move: t1Mq; rewrite (tau1E maxM hallE) andbA andbC; case: eqP.
have cycQ: cyclic Q.
  by rewrite (odd_pgroup_rank1_cyclic qQ) ?mFT_odd // (p_rank_Sylow sylQ) rqE.
have sCAE: 'C(A) \subset E by case/(tau2_compl_context maxM): Ep2A => // _ [].
have{sCAE} sylCQA: q.-Sylow('C(A)) 'C_Q(A).
  by apply: Hall_setI_normal sylQ; rewrite /= -(setIidPr sCAE).
have{sylCQA} defNA: 'C(A) * 'N_('N(A))(Q0) = 'N(A).
  apply/eqP; rewrite eqEsubset mulG_subG cent_sub subsetIl /=.
  rewrite -{1}(Frattini_arg (cent_normal A) sylCQA) mulgS ?setIS ?char_norms //.
  by rewrite (sub_cyclic_char Q0 (cyclicS (subsetIl Q _) cycQ)) subsetI sQ0Q.
have [L maxNQ0_L]: {L | L \in 'M('N(Q0))}.
  by apply: mmax_exists; rewrite mFT_norm_proper ?(mFT_pgroup_proper qQ0).
have{maxNQ0_L} [maxL sNQ0_L] := setIdP maxNQ0_L.
have sCQ0_L: 'C(Q0) \subset L := subset_trans (cent_sub Q0) sNQ0_L.
have sAL: A \subset L by rewrite (subset_trans _ sCQ0_L) // centsC.
have sCA_L: 'C(A) \subset L.
  by have /p2Elem_mmax[]: A \in 'E_p^2(L) by apply/pnElemP.
have{sCA_L defNA} maxNA_L: L \in 'M('N(A)).
  by rewrite inE maxL -defNA setIC mul_subG // subIset ?sNQ0_L.
have t2Lq: q \in \tau2(L).
  have /orP[sLq | //] := prime_class_mmax_norm maxL qQ0 sNQ0_L.
  by have /orP[/andP[/negP] | ] := pnatPpi (part_b L maxNA_L) piCEAb_q.
have [cQQ [/= sL'q _]] := (cyclic_abelian cycQ, andP t2Lq).
have sQL: Q \subset L := subset_trans (centsS sQ0Q cQQ) sCQ0_L. 
have [F hallF sQF] := Hall_superset (mmax_sol maxL) sQL (pi_pnat qQ sL'q).
have [B Eq2B _] := ex_tau2Elem hallF t2Lq.
have [_ sLp]: _ /\ p \in \sigma(L) := andP (part_a L maxNA_L p t2Mp).
have{H sHp maxH sCA_H} <-: L :=: H.
  have sLHp: p \in [predI \sigma(L) & \sigma(H)] by apply/andP.
  have [_ transCA _] := sigma_group_trans maxH sHp pA.
  set S := finset _ in transCA; have sAH := subset_trans cAA sCA_H.
  suffices [SH SL]: gval H \in S /\ gval L \in S.
    have [c cAc -> /=]:= atransP2 transCA SH SL.
    by rewrite conjGid // (subsetP sCA_H).
  have [_ _ _ TIsL] := tau2_compl_context maxL hallF t2Lq Eq2B.
  apply/andP; rewrite !inE sAH sAL orbit_refl orbit_sym /= andbT.
  by apply: contraLR sLHp => /TIsL[] // _ ->.
split=> //.
  exists ('O_p(L`_\sigma))%G; last by rewrite /= -pcoreI pcore_normal.
  rewrite inE (subHall_Sylow (Msigma_Hall_G maxL) sLp) //.
  by rewrite nilpotent_pcore_Hall // (tau2_Msigma_nil maxL t2Lq).
have [Q1 sylQ1 sQQ1] := Sylow_superset (subsetT Q) qQ.
have [sQ0Q1 qQ1] := (subset_trans sQ0Q sQQ1, pHall_pgroup sylQ1).
have [cQ1Q1 | not_cQ1Q1] := boolP (abelian Q1).
  by exists Q1; rewrite inE (subset_trans (centsS sQ0Q1 cQ1Q1)).
have [_ _ regB [F0 /=]] := nonabelian_tau2 maxL hallF t2Lq Eq2B qQ1 not_cQ1Q1.
have{regB} ->: 'C_B(L`_\sigma) = Q0; last move=> defF _.
  apply: contraTeq sCQ0_L => neqQ0B; case: (regB Q0) => //.
  by rewrite 2!inE eq_sym neqQ0B; apply/pnElemP; rewrite (subset_trans sQ0Q).
have{defF} defQ: Q0 \x (F0 :&: Q) = Q.
  rewrite dprodEsd ?(centSS (subsetIr F0 Q) sQ0Q) //.
  by rewrite (sdprod_modl defF sQ0Q) (setIidPr sQF).
have [[/eqP/idPn//] | [_ eqQ0Q]] := cyclic_pgroup_dprod_trivg qQ cycQ defQ.
have nCEA_Q := subset_trans sQE nCA_E.
case/idPn: piCEAb_q; rewrite -p'natEpi -?partn_eq1 ?cardG_gt0 //.
rewrite -(card_Hall (quotient_pHall nCEA_Q sylQ)) -trivg_card1 -subG1.
by rewrite quotient_sub1 // subsetI sQE -eqQ0Q.
Qed.

(* This is a generalization of B & G, Theorem 12.12. *)
(* In the B & G text, Theorem 12.12 only establishes the type F structure     *)
(* for groups of type I, whereas it is required for the derived groups of     *)
(* groups of type II (in the sense of Peterfalvi). Indeed this is exactly     *)
(* what is stated in Lemma 15.15(e) and then Theorem B(3). The proof of       *)
(* 15.15(c) cites 12.12 in the type I case (K = 1) and then loosely invokes   *)
(* a "short and easy argument" inside the proof of 12.12 for the K != 1 case. *)
(* In fact, this involves copying roughly 25% of the proof, whereas the proof *)
(* remains essentially unchanged when Theorem 12.12 is generalized to a       *)
(* normal Hall subgroup of E as below.                                        *)
(*   Also, we simplify the argument for central tau2 Sylow subgroup S of U by *)
(* by replacing the considerations on the abelian structure of S by a         *)
(* comparison of Mho^n-1(S) and Ohm_1(S) (with exponent S = p ^ n), as the    *)
(* former is needed anyway to prove regularity when S is not homocyclic.      *)
Theorem FTtypeF_complement M (Ms := M`_\sigma) E U :
    M \in 'M -> \sigma(M)^'.-Hall(M) E -> Hall E U -> U <| E -> U :!=: 1 ->
  {in U^#, forall e, [predU \tau1(M) & \tau3(M)].-elt e -> 'C_Ms[e] = 1} ->
  [/\ (*a*) exists A0 : {group gT},
             [/\ A0 <| U, abelian A0 & {in Ms^#, forall x, 'C_U[x] \subset A0}]
    & (*b*) exists E0 : {group gT},
             [/\ E0 \subset U, exponent E0 = exponent U
               & [Frobenius Ms <*> E0 = Ms ><| E0]]].
Proof.
set p13 := predU _ _  => maxM hallE /Hall_pi hallU nsUE ntU regU13.
have [[E1 hallE1] [E3 hallE3]] := ex_tau13_compl hallE.
have [E2 hallE2 complEi] := ex_tau2_compl hallE hallE1 hallE3.
have [[sE1E _] [sE2E t2E2 _]] := (andP hallE1, and3P hallE2).
have [[_ nsE3E] _ [cycE1 _] [defE _] _] := sigma_compl_context maxM complEi.
have [[[sE3E t3E3 _][_ nE3E]] [sUE _]] := (and3P hallE3, andP nsE3E, andP nsUE).
have defM: Ms ><| E = M := sdprod_sigma maxM hallE.
have [nsMsM sEM mulMsE nMsE tiMsE] := sdprod_context defM.
have ntMs: Ms != 1 := Msigma_neq1 maxM.
have{defM} defMsU: Ms ><| U = Ms <*> U := sdprod_subr defM sUE.
pose U2 := (E2 :&: U)%G.
have hallU2: \tau2(M).-Hall(U) U2 := Hall_setI_normal nsUE hallE2.
have [U2_1 | ntU2] := eqsVneq U2 1.
  have frobMsU: [Frobenius Ms <*> U = Ms ><| U].
    apply/Frobenius_semiregularP=> // e Ue.
    apply: regU13 => //; case/setD1P: Ue => _; apply: mem_p_elt.
    have: \tau2(M)^'.-group U.
      by rewrite -partG_eq1 -(card_Hall hallU2) U2_1 cards1.
    apply: sub_in_pnat => p /(piSg sUE).
    by rewrite (partition_pi_sigma_compl maxM hallE) orbCA => /orP[] // /idPn.
  split; [exists 1%G; rewrite normal1 abelian1 | by exists U].
  by split=> //= x Ux; rewrite (Frobenius_reg_compl frobMsU).
have [[sU2U t2U2 _] [p p_pr rU2]] := (and3P hallU2, rank_witness U2).
have piU2p: p \in \pi(U2) by rewrite -p_rank_gt0 -rU2 rank_gt0.
have t2p: p \in \tau2(M) := pnatPpi t2U2 piU2p.
have [A Ep2A Ep2A_M] := ex_tau2Elem hallE t2p.
have [sAE abelA _] := pnElemP Ep2A; have{abelA} [pA cAA _] := and3P abelA.
have [S sylS sAS] := Sylow_superset (subsetT A) pA.
have [cSS | not_cSS] := boolP (abelian S); last first.
  have [_] := nonabelian_tau2 maxM hallE t2p Ep2A (pHall_pgroup sylS) not_cSS.
  set A0 := ('C_A(_))%G => [] [oA0 _] _ {defE} [E0 defE regE0].
  have [nsA0E sE0E mulAE0 nAE0 tiAE0] := sdprod_context defE.
  have [P sylP] := Sylow_exists p U; have [sPU _] := andP sylP.
  have sylP_E := subHall_Sylow hallU (piSg sU2U piU2p) sylP.
  have pA0: p.-group A0 by rewrite /pgroup oA0 pnat_id.
  have sA0P: A0 \subset P.
    by apply: subset_trans (pcore_sub_Hall sylP_E); apply: pcore_max.
  have sA0U: A0 \subset U := subset_trans sA0P sPU.
  pose U0 := (E0 :&: U)%G.
  have defU: A0 ><| U0 = U by rewrite (sdprod_modl defE) // (setIidPr sUE).
  have piU0p: p \in \pi(U0).
    have:= lognSg p sAE; rewrite (card_pnElem Ep2A) pfactorK //.
    rewrite -logn_part -(card_Hall sylP_E) (card_Hall sylP) logn_part.
    rewrite -(sdprod_card defU) oA0 lognM // ?prime_gt0 // logn_prime // eqxx.
    by rewrite ltnS logn_gt0.
  have defM0: Ms ><| U0 = Ms <*> U0 := sdprod_subr defMsU (subsetIr _ _).
  have frobM0: [Frobenius Ms <*> U0 = Ms ><| U0].
    apply/Frobenius_semiregularP=> // [|e /setD1P[nte /setIP[E0e Ue]]].      
      by rewrite -rank_gt0 (leq_trans _ (p_rank_le_rank p _)) ?p_rank_gt0.    
    have [ | ] := boolP (p13.-elt e); first by apply: regU13; rewrite !inE nte.
    apply: contraNeq => /trivgPn[x /setIP[Ms_x cex] ntx].
    apply/pgroupP=> q q_pr q_dv_x ; rewrite inE /= (regE0 x) ?inE ?ntx //.
    rewrite mem_primes q_pr cardG_gt0 (dvdn_trans q_dv_x) ?order_dvdG //.
    by rewrite inE E0e cent1C.
  have [nsA0U sU0U _ _ _] := sdprod_context defU.
  split; [exists A0 | exists U0].
    split=> // [|x Ms_x]; first by rewrite (abelianS (subsetIl A _) cAA).
    rewrite -(sdprodW defU) -group_modl ?(Frobenius_reg_compl frobM0) ?mulg1 //.
    by rewrite subIset //= orbC -cent_set1 centS // sub1set; case/setD1P: Ms_x.
  split=> //; apply/eqP; rewrite eqn_dvd exponentS //=.
  rewrite -(partnC p (exponent_gt0 U0)) -(partnC p (exponent_gt0 U)).
  apply: dvdn_mul; last first.
    rewrite (partn_exponentS sU0U) // -(sdprod_card defU) partnM ?cardG_gt0 //.
    by rewrite part_p'nat ?pnatNK // mul1n dvdn_part.
  have cPP: abelian P.
    have [/(_ P)[] //] := tau2_context maxM t2p Ep2A_M.
    by apply: subHall_Sylow hallE _ sylP_E; case/andP: t2p.
  have defP: A0 \x (U0 :&: P) = P.
    rewrite dprodEsd ?(sub_abelian_cent2 cPP) ?subsetIr //.
    by rewrite (sdprod_modl defU) // (setIidPr sPU).
  have sylP_U0: p.-Sylow(U0) (U0 :&: P).
    rewrite pHallE subsetIl /= -(eqn_pmul2l (cardG_gt0 A0)).
    rewrite (dprod_card defP) (card_Hall sylP) -(sdprod_card defU).
    by rewrite partnM // part_pnat_id.
  rewrite -(exponent_Hall sylP) -(dprod_exponent defP) (exponent_Hall sylP_U0).
  rewrite dvdn_lcm (dvdn_trans (exponent_dvdn A0)) //= oA0.
  apply: contraLR piU0p; rewrite -p'natE // -partn_eq1 // partn_part //.
  by rewrite partn_eq1 ?exponent_gt0 // pnat_exponent -p'groupEpi.
have{t2p Ep2A sylS sAS cSS} [[nsE2E cE2E2] hallE2_G _ _]
  := abelian_tau2 maxM complEi t2p Ep2A sylS sAS cSS.
clear p p_pr rU2 piU2p A S Ep2A_M sAE pA cAA.
have nsU2U: U2 <| U by rewrite (normalS sU2U sUE) ?normalI.
have cU2U2: abelian U2 := abelianS (subsetIl _ _) cE2E2.
split.
  exists U2; rewrite -set1gE; split=> // x /setDP[Ms_x ntx].
  rewrite (sub_normal_Hall hallU2) ?subsetIl //=.
  apply: sub_in_pnat (pgroup_pi _) => q /(piSg (subsetIl U _))/(piSg sUE).
  rewrite (partition_pi_sigma_compl maxM) // orbCA => /orP[] // t13q.
  rewrite mem_primes => /and3P[q_pr _ /Cauchy[] // y /setIP[Uy cxy] oy].
  case/negP: ntx; rewrite -(regU13 y); first by rewrite inE Ms_x cent1C.
    by rewrite !inE -order_gt1 oy prime_gt1.
  by rewrite /p_elt oy pnatE.
pose sylU2 S := (S :!=: 1) && Sylow U2 S.
pose cyclicRegular Z S :=
   [/\ Z <| U, cyclic Z, 'C_Ms('Ohm_1(Z)) = 1 & exponent Z = exponent S].
suffices /fin_all_exists[Z_ Z_P] S: exists Z, sylU2 S -> cyclicRegular Z S.
  pose Z2 := <<\bigcup_(S | sylU2 S) Z_ S>>.
  have sZU2: Z2 \subset U2.
    rewrite gen_subG; apply/bigcupsP=> S sylS.
    have [[/andP[sZE _] _ _ eq_expZS] [_ _ sSU2 _]] := (Z_P S sylS, and4P sylS).
    rewrite (sub_normal_Hall hallU2) // -pnat_exponent eq_expZS.
    by rewrite pnat_exponent (pgroupS sSU2 t2U2).
  have nZ2U: U \subset 'N(Z2).
    by rewrite norms_gen ?norms_bigcup //; apply/bigcapsP => S /Z_P[/andP[]].
  have solU: solvable U := solvableS sUE (sigma_compl_sol hallE).
  have [U31 hallU31] := Hall_exists \tau2(M)^' solU.
  have [[sU31U t2'U31 _] t2Z2] := (and3P hallU31, pgroupS sZU2 t2U2).
  pose U0 := (Z2 <*> U31)%G; have /joing_sub[sZ2U0 sU310] := erefl (gval U0).
  have sU0U: U0 \subset U by rewrite join_subG (subset_trans sZU2).
  have nsZ2U0: Z2 <| U0 by rewrite /normal sZ2U0 (subset_trans sU0U).
  have defU0: Z2 * U31 = U0 by rewrite -norm_joinEr // (subset_trans sU31U).
  have [hallZ2 hallU31_0] := coprime_mulpG_Hall defU0 t2Z2 t2'U31.
  have expU0U: exponent U0 = exponent U.
    have exp_t2c U' := partnC \tau2(M) (exponent_gt0 U').
    rewrite -(exp_t2c U) -(exponent_Hall hallU31) -(exponent_Hall hallU2).
    rewrite -{}exp_t2c -(exponent_Hall hallU31_0) -(exponent_Hall hallZ2).
    congr (_ * _)%N; apply/eqP; rewrite eqn_dvd exponentS //=.
    apply/dvdn_partP=> [|p]; first exact: exponent_gt0.
    have [S sylS] := Sylow_exists p U2; rewrite -(exponent_Hall sylS).
    rewrite pi_of_exponent -p_rank_gt0 -(rank_Sylow sylS) rank_gt0 => ntS.
    have{sylS} sylS: sylU2 S by rewrite /sylU2 ntS (p_Sylow sylS).
    by have /Z_P[_ _ _ <-] := sylS; rewrite exponentS ?sub_gen ?(bigcup_max S).
  exists U0; split=> //.
  have ntU0: U0 :!=: 1 by rewrite trivg_exponent expU0U -trivg_exponent.
  apply/Frobenius_semiregularP=> //; first by rewrite (sdprod_subr defMsU).
  apply: semiregular_sym => x /setD1P[ntx Ms_x]; apply: contraNeq ntx.
  rewrite -rank_gt0; have [p p_pr ->] := rank_witness [group of 'C_U0[x]].
  rewrite -in_set1 -set1gE p_rank_gt0 => piCp.
  have [e /setIP[U0e cxe] oe]: {e | e \in 'C_U0[x] & #[e] = p}.
    by move: piCp; rewrite mem_primes p_pr cardG_gt0; apply: Cauchy.
  have nte: e != 1 by rewrite -order_gt1 oe prime_gt1.
  have{piCp} piUp: p \in \pi(U).
    by rewrite -pi_of_exponent -expU0U pi_of_exponent (piSg _ piCp) ?subsetIl.
  have:= piSg sUE piUp; rewrite (partition_pi_sigma_compl maxM) // orbCA orbC.
  case/orP=> [t13p | t2p].
    rewrite -(regU13 e) 1?inE ?Ms_x 1?cent1C //.
      by rewrite inE nte (subsetP sU0U).
    by rewrite /p_elt oe pnatE.
  have Z2e: e \in Z2 by rewrite (mem_normal_Hall hallZ2) // /p_elt oe pnatE.
  have [S sylS] := Sylow_exists p U2; have [sSU2 pS _] := and3P sylS.
  have sylS_U: p.-Sylow(U) S := subHall_Sylow hallU2 t2p sylS.
  have ntS: S :!=: 1 by rewrite -rank_gt0 (rank_Sylow sylS_U) p_rank_gt0.
  have sylS_U2: sylU2 S by rewrite /sylU2 ntS (p_Sylow sylS).
  have [nsZU cycZ regZ1 eqexpZS] := Z_P S sylS_U2.
  suffices defZ1: 'Ohm_1(Z_ S) == <[e]>.
    by rewrite -regZ1 (eqP defZ1) cent_cycle inE Ms_x cent1C.
  have pZ: p.-group (Z_ S) by rewrite -pnat_exponent eqexpZS pnat_exponent.
  have sylZ: p.-Sylow(Z2) (Z_ S).
    have:= sZU2; rewrite pHallE /Z2 /= -bigprodGE (bigD1 S) //=.
    set Z2' := (\prod_(T | _) _)%G => /joing_subP[sZ_U2 sZ2'_U2].
    rewrite joing_subl cent_joinEl ?(sub_abelian_cent2 cU2U2) //=.
    suffices p'Z2': p^'.-group Z2'.
      rewrite coprime_cardMg ?(pnat_coprime pZ) //.
      by rewrite partnM // part_pnat_id // part_p'nat // muln1.
    elim/big_ind: Z2' sZ2'_U2 => [_||T /andP[sylT neqTS]]; first exact: pgroup1.
      move=> X Y IHX IHY /joing_subP[sXU2 sYU2] /=.
      by rewrite cent_joinEl ?(sub_abelian_cent2 cU2U2) // pgroupM IHX ?IHY.
    have /Z_P[_ _ _ expYT _] := sylT.
    have{sylT} [_ /SylowP[q _ sylT]] := andP sylT.
    rewrite -pnat_exponent expYT pnat_exponent.
    apply: (pi_pnat (pHall_pgroup sylT)); apply: contraNneq neqTS => eq_qp.
    have defOE2 := nilpotent_Hall_pcore (abelian_nil cU2U2).
    by rewrite -val_eqE /= (defOE2 _ _ sylS) (defOE2 _ _ sylT) eq_qp.
  have nZZ2 := normalS (pHall_sub sylZ) (subset_trans sZU2 sU2U) nsZU.
  have Ze: e \in Z_ S by rewrite (mem_normal_Hall sylZ) // /p_elt oe pnat_id.
  rewrite (eq_subG_cyclic cycZ) ?Ohm_sub ?cycle_subG // -orderE oe.
  by rewrite (Ohm1_cyclic_pgroup_prime _ pZ) //; apply/trivgPn; exists e.
case: (sylU2 S) / andP => [[ntS /SylowP[p p_pr sylS_U2]]|]; last by exists E.
have [sSU2 pS _] := and3P sylS_U2; have [sSE2 sSU] := subsetIP sSU2.
have piSp: p \in \pi(S) by rewrite -p_rank_gt0 -rank_pgroup ?rank_gt0.
have t2p: p \in \tau2(M) := pnatPpi t2U2 (piSg sSU2 piSp).
have sylS_U: p.-Sylow(U) S := subHall_Sylow hallU2 t2p sylS_U2.
have sylS_E: p.-Sylow(E) S := subHall_Sylow hallU (piSg sSU piSp) sylS_U.
have sylS: p.-Sylow(E2) S := pHall_subl sSE2 sE2E sylS_E.
have sylS_G: p.-Sylow(G) S := subHall_Sylow hallE2_G t2p sylS.
have [cSS [/= s'p rpM]] := (abelianS sSU2 cU2U2, andP t2p).
have sylS_M: p.-Sylow(M) S := subHall_Sylow hallE s'p sylS_E.
have rpS: 'r_p(S) = 2 by apply/eqP; rewrite (p_rank_Sylow sylS_M).
have [A] := p_rank_witness p S; rewrite rpS -(setIidPr (pHall_sub sylS_E)).
rewrite pnElemI setIC 2!inE => /andP[sAS Ep2A].
have [[nsAE defEp] _ nregEp_uniq _] := tau2_compl_context maxM hallE t2p Ep2A.
have [_ sNS'FE _ sCSE _]
  := abelian_tau2_sub_Fitting maxM hallE t2p Ep2A sylS_G sAS cSS.
have [_ _ [defNS _ _ _] regE1subZ]
  := abelian_tau2 maxM complEi t2p Ep2A sylS_G sAS cSS.
have nSE: E \subset 'N(S) by rewrite -defNS normal_norm.
have [sSE nSU] := (subset_trans sSE2 sE2E, subset_trans sUE nSE).
have n_subNS := abelian_tau2_norm_Sylow maxM hallE t2p Ep2A sylS_G sAS cSS.
have not_sNS_M: ~~ ('N(S) \subset M).
  by apply: contra s'p => sNS_M; apply/exists_inP; exists S; rewrite // inE.
have regNNS Z (Z1 := 'Ohm_1(Z)%G):
  Z \subset S -> cyclic Z -> Z :!=: 1 -> 'N(S) \subset 'N(Z1) -> 'C_Ms(Z1) = 1.
- move=> sZS cycZ ntZ nZ1_NS; apply: contraNeq not_sNS_M => nregZ1.
  have sZ1S: Z1 \subset S := subset_trans (Ohm_sub 1 Z) sZS.
  have EpZ1: Z1 \in 'E_p^1(E).
    rewrite p1ElemE // !inE (subset_trans sZ1S) //=.
    by rewrite (Ohm1_cyclic_pgroup_prime _ (pgroupS sZS pS)).
  have /= uCZ1 := nregEp_uniq _ EpZ1 nregZ1.
  apply: (subset_trans nZ1_NS); apply: (sub_uniq_mmax uCZ1 (cent_sub _)).
  by rewrite mFT_norm_proper ?(mFT_pgroup_proper (pgroupS sZ1S pS)) ?Ohm1_eq1.
have [_ nsCEA t1CEAb] := tau1_cent_tau2Elem_factor maxM hallE t2p Ep2A.
have [cSU | not_cSU] := boolP (U \subset 'C(S)).
  pose n := logn p (exponent S); pose Sn := 'Mho^n.-1(S)%G.
  have n_gt0: 0 < n by rewrite -pi_of_exponent -logn_gt0 in piSp.
  have expS: (exponent S = p ^ n.-1 * p)%N.
    rewrite -expnSr prednK -?p_part //.
    by rewrite part_pnat_id ?pnat_exponent ?expg_exponent.
  have sSnS1: Sn \subset 'Ohm_1(S).
    rewrite (OhmE 1 pS) /= (MhoE _ pS); apply/genS/subsetP=> _ /imsetP[x Sx ->].
    by rewrite !inE groupX //= -expgM -expS expg_exponent.
  have sSZ: S \subset 'Z(U) by rewrite subsetI sSU centsC.
  have{sSZ} nsZU z: z \in S -> <[z]> <| U.
    by move/(subsetP sSZ)=> ZUz; rewrite sub_center_normal ?cycle_subG.
  have [homoS | ltSnS1] := eqVproper sSnS1.
    have Ep2A_M := subsetP (pnElemS p 2 sEM) A Ep2A.
    have [_ _ _ _ [A1 EpA1 regA1]] := tau2_context maxM t2p Ep2A_M.
    have [sA1A _ oA1] := pnElemPcard EpA1.
    have /cyclicP[zn defA1]: cyclic A1 by rewrite prime_cyclic ?oA1.
    have [z Sz def_zn]: exists2 z, z \in S & zn = z ^+ (p ^ n.-1).
      apply/imsetP; rewrite -(MhoEabelian _ pS cSS) homoS (OhmE 1 pS).
      rewrite mem_gen // !inE -cycle_subG -defA1 (subset_trans sA1A) //=.
      by rewrite -oA1 defA1 expg_order.
    have oz: #[z] = exponent S.
      by rewrite expS; apply: orderXpfactor; rewrite // -def_zn orderE -defA1.
    exists <[z]>%G; split; rewrite ?cycle_cyclic ?exponent_cycle ?nsZU //.
    by rewrite (Ohm_p_cycle _ (mem_p_elt pS Sz)) subn1 oz -def_zn -defA1.
  have [z Sz /esym oz] := exponent_witness (abelian_nil cSS).
  exists <[z]>%G; split; rewrite ?cycle_cyclic ?exponent_cycle ?nsZU //.
  have ntz: <[z]> != 1 by rewrite trivg_card1 -orderE oz -dvdn1 -trivg_exponent.
  rewrite regNNS ?cycle_cyclic ?cycle_subG //=.
  suffices /eqP->: 'Ohm_1(<[z]>) == Sn by apply: char_norms; apply: gFchar.
  have [p_z pS1] := (mem_p_elt pS Sz, pgroupS (Ohm_sub 1 S) pS). 
  rewrite eqEcard (Ohm1_cyclic_pgroup_prime _ p_z) ?cycle_cyclic //.
  rewrite (Ohm_p_cycle _ p_z) oz -/n subn1 cycle_subG Mho_p_elt //=.
  rewrite (card_pgroup (pgroupS sSnS1 pS1)) (leq_exp2l _ 1) ?prime_gt1 //.
  by rewrite -ltnS -rpS p_rank_abelian ?properG_ltn_log.
have{not_cSU} [q q_pr piUq]: {q | prime q & q \in \pi(U / 'C(S))}.
  have [q q_pr rCE] := rank_witness (U / 'C(S)); exists q => //.
  by rewrite -p_rank_gt0 -rCE rank_gt0 -subG1 quotient_sub1 ?norms_cent.
have{piUq} [piCESbq piUq]: q \in \pi(E / 'C_E(S)) /\ q \in \pi(U).
  rewrite /= setIC (card_isog (second_isog (norms_cent nSE))).
  by rewrite (piSg _ piUq) ?quotientS // (pi_of_dvd _ _ piUq) ?dvdn_quotient.
have [Q1 sylQ1_U] := Sylow_exists q U; have [sQ1U qQ1 _] := and3P sylQ1_U.
have sylQ1: q.-Sylow(E) Q1 := subHall_Sylow hallU piUq sylQ1_U.
have sQ1E := subset_trans sQ1U sUE; have nSQ1 := subset_trans sQ1E nSE.
have [Q sylQ sQ1Q] := Sylow_superset nSQ1 qQ1; have [nSQ qQ _] := and3P sylQ.
have Ep2A_M := subsetP (pnElemS p 2 sEM) A Ep2A.
have ltCQ1_S: 'C_S(Q1) \proper S.
  rewrite properE subsetIl /= subsetI subxx centsC -sQ1E -subsetI.
  have nCES_Q1: Q1 \subset 'N('C_E(S)) by rewrite (setIidPr sCSE) norms_cent.
  rewrite -quotient_sub1 // subG1 -rank_gt0.
  by rewrite (rank_Sylow (quotient_pHall nCES_Q1 sylQ1)) p_rank_gt0.
have coSQ: coprime #|S| #|Q|.
  suffices p'q: q != p by rewrite (pnat_coprime pS) // (pi_pnat qQ).
  apply: contraNneq (proper_subn ltCQ1_S) => eq_qp; rewrite subsetI subxx.
  rewrite (sub_abelian_cent2 cE2E2) // (sub_normal_Hall hallE2) //.
  by rewrite (pi_pgroup qQ1) ?eq_qp.
have not_sQ1CEA: ~~ (Q1 \subset 'C_E(A)).
  rewrite subsetI sQ1E; apply: contra (proper_subn ltCQ1_S) => /= cAQ1.
  rewrite subsetIidl centsC coprime_abelian_faithful_Ohm1 ?(coprimegS sQ1Q) //.
  by case: (tau2_context maxM t2p Ep2A_M); case/(_ S sylS_M)=> _ [|->] //.
have t1q: q \in \tau1(M).
  rewrite (pnatPpi t1CEAb) // -p_rank_gt0.
  have nCEA_Q1: Q1 \subset 'N('C_E(A)) := subset_trans sQ1E (normal_norm nsCEA).
  rewrite -(rank_Sylow (quotient_pHall nCEA_Q1 sylQ1)) rank_gt0.
  by rewrite -subG1 quotient_sub1.
have cycQ1: cyclic Q1.
  have [x _ sQ1E1x] := Hall_psubJ hallE1 t1q sQ1E qQ1.
  by rewrite (cyclicS sQ1E1x) ?cyclicJ.
have defQ1: Q :&: E = Q1.
  apply: (sub_pHall sylQ1) (subsetIr Q E); last by rewrite subsetI sQ1Q.
  by rewrite (pgroupS (subsetIl Q _)).
pose Q0 := 'C_Q(S); have nsQ0Q: Q0 <| Q by rewrite norm_normalI ?norms_cent.
have [sQ0Q nQ0Q] := andP nsQ0Q; have nQ01 := subset_trans sQ1Q nQ0Q.
have coSQ0: coprime #|S| #|Q0| := coprimegS sQ0Q coSQ.
have ltQ01: Q0 \proper Q1.
  rewrite /proper -{1}defQ1 setIS //.
  apply: contra (proper_subn ltCQ1_S) => sQ10.
  by rewrite subsetIidl (centsS sQ10) // centsC subsetIr.
have [X]: exists2 X, X \in subgroups Q & ('C_S(X) != 1) && ([~: S, X] != 1).
  apply/exists_inP; apply: contraFT (ltnn 1); rewrite negb_exists_in => irrS.
  have [sQ01 not_sQ10] := andP ltQ01.
  have qQb: q.-group (Q / Q0) by exact: quotient_pgroup.
  have ntQ1b: Q1 / Q0 != 1 by rewrite -subG1 quotient_sub1.
  have ntQb: Q / Q0 != 1 := subG1_contra (quotientS _ sQ1Q) ntQ1b.
  have{irrS} regQ: semiregular (S / Q0) (Q / Q0).
    move=> Q0x; rewrite 2!inE -cycle_subG -cycle_eq1 -cent_cycle andbC.
    case/andP; case/(inv_quotientS nsQ0Q)=> X /= -> {Q0x} sQ0X sXQ ntXb.
    have [nSX nQ0X] := (subset_trans sXQ nSQ, subset_trans sXQ nQ0Q).
    rewrite -quotient_TI_subcent ?(coprime_TIg coSQ0) //.
    apply: contraTeq (forallP irrS X) => ntCSXb; rewrite inE sXQ negbK.
    apply/andP; split.
      by apply: contraNneq ntCSXb => ->; rewrite quotient1.
    apply: contraNneq ntXb; move/commG1P => cXS.
    by rewrite quotientS1 // subsetI sXQ centsC.
  have{regQ} cycQb: cyclic (Q / Q0).
    have nSQb: Q / Q0 \subset 'N(S / Q0) by exact: quotient_norms.
    apply: odd_regular_pgroup_cyclic qQb (mFT_quo_odd _ _) _ nSQb regQ.
    rewrite -(isog_eq1 (quotient_isog _ _)) ?coprime_TIg 1?coprime_sym //.
    by rewrite cents_norm // centsC subsetIr.
  have rQ1: 'r(Q1) = 1%N.
    apply/eqP; rewrite (rank_Sylow sylQ1).
    by rewrite (tau1E maxM hallE) in t1q; case/and3P: t1q.
  have: 'r(Q) <= 1; last apply: leq_trans.
    have nQ0_Ohm1Q := subset_trans (Ohm_sub 1 Q) nQ0Q.
    rewrite -rQ1 -rank_Ohm1 rankS // -(quotientSGK _ sQ01) //.
    rewrite (subset_trans (morphim_Ohm _ _ nQ0Q)) //= -quotientE -/Q0.
    rewrite -(cardSg_cyclic cycQb) ?Ohm_sub ?quotientS //.
    have [_ q_dv_Q1b _] := pgroup_pdiv (pgroupS (quotientS _ sQ1Q) qQb) ntQ1b.
    by rewrite (Ohm1_cyclic_pgroup_prime cycQb qQb ntQb).
  have ltNA_G: 'N(A) \proper G.
    by rewrite defNS mFT_norm_proper // (mFT_pgroup_proper pS).
  have [H maxNA_H] := mmax_exists ltNA_G.
  have nCEA_Q1 := subset_trans sQ1E (normal_norm nsCEA). 
  have [_ _] := primes_norm_tau2Elem maxM hallE t2p Ep2A maxNA_H.
  case/(_ q)=> [||t2Hq [S2 sylS2 nsS2H] _].
  - rewrite -p_rank_gt0 -(rank_Sylow (quotient_pHall _ sylQ1)) //.
    by rewrite rank_gt0 -subG1 quotient_sub1.
  - rewrite -p_rank_gt0 -rQ1 (rank_pgroup qQ1) -p_rank_Ohm1 p_rankS //.
    have: 'Z(E) \subset 'C_E(A); last apply: subset_trans.
      by rewrite setIS ?centS // normal_sub.
    have [x Ex sQ1xE1] := Hall_pJsub hallE1 t1q sQ1E qQ1.
    rewrite -(conjSg _ _ x) (normsP (normal_norm (center_normal E))) //.
    set Q11x := _ :^ x; have oQ11x: #|Q11x| = q.
      by rewrite cardJg (Ohm1_cyclic_pgroup_prime _ qQ1) // -rank_gt0 rQ1.
    apply: regE1subZ.
      apply/nElemP; exists q; rewrite p1ElemE // !inE oQ11x.
      by rewrite (subset_trans _ sQ1xE1) //= conjSg Ohm_sub.
    have: cyclic Q11x by rewrite prime_cyclic ?oQ11x.
    case/cyclicP=> y defQ11x; rewrite /= -/Q11x defQ11x cent_cycle regU13 //.
      rewrite !inE -order_gt1 -cycle_subG /order -defQ11x oQ11x prime_gt1 //.
      rewrite sub_conjg (subset_trans (Ohm_sub 1 Q1)) //.
      by rewrite (normsP (normal_norm nsUE)) ?groupV.
    by rewrite /p_elt /order -defQ11x oQ11x pnatE //; apply/orP; left.
  rewrite inE in sylS2; have [sS2H _]:= andP nsS2H.
  have sylS2_H := pHall_subl sS2H (subsetT H) sylS2.
  have [maxH sNS_H] := setIdP maxNA_H; rewrite /= defNS in sNS_H.
  have sylS_H := pHall_subl (subset_trans (normG S) sNS_H) (subsetT H) sylS_G.
  have defS2: S :=: S2 := uniq_normal_Hall sylS2_H nsS2H (Hall_max sylS_H).
  have sylQ_H: q.-Sylow(H) Q by rewrite -(mmax_normal maxH nsS2H) -defS2.
  by rewrite (rank_Sylow sylQ_H); case/andP: t2Hq => _ /eqP->.
rewrite inE => sXQ /=; have nSX := subset_trans sXQ nSQ.
set S1 := [~: S, X]; set S2 := 'C_S(X) => /andP[ntS2 ntS1].
have defS12: S1 \x S2 = S.
  by apply: coprime_abelian_cent_dprod; rewrite ?(coprimegS sXQ).
have /mulG_sub[sS1S sS2S] := dprodW defS12.
have [cycS1 cycS2]: cyclic S1 /\ cyclic S2.
  apply/andP; rewrite !(abelian_rank1_cyclic (abelianS _ cSS)) //.
  rewrite -(leqif_add (leqif_geq _) (leqif_geq _)) ?rank_gt0 // addn1 -rpS.
  rewrite !(rank_pgroup (pgroupS _ pS)) ?(p_rank_abelian p (abelianS _ cSS)) //.
  by rewrite -lognM ?cardG_gt0 // (dprod_card (Ohm_dprod 1 defS12)).
have [nsS2NS nsS1NS]: S2 <| 'N(S) /\ S1 <| 'N(S) := n_subNS X nSX.
pose Z := if #|S1| < #|S2| then [group of S2] else [group of S1].
have [ntZ sZS nsZN cycZ]: [/\ Z :!=: 1, Z \subset S, Z <| 'N(S) & cyclic Z].
  by rewrite /Z; case: ifP.
have nsZU: Z <| U := normalS (subset_trans sZS sSU) nSU nsZN.
exists Z; split=> //=.
  by rewrite regNNS // (char_norm_trans (Ohm_char 1 Z)) // normal_norm.
rewrite -(dprod_exponent defS12) /= (fun_if val) fun_if !exponent_cyclic //=.
rewrite (card_pgroup (pgroupS sS1S pS)) (card_pgroup (pgroupS sS2S pS)) //.
by rewrite /= -/S1 -/S2 ltn_exp2l ?prime_gt1 // -fun_if expn_max.
Qed.

(* This is B & G, Theorem 12.13. *)
Theorem nonabelian_Uniqueness p P : p.-group P -> ~~ abelian P -> P \in 'U.
Proof.
move=> pP not_cPP; have [M maxP_M] := mmax_exists (mFT_pgroup_proper pP).
have sigma_p L: L \in 'M(P) -> p \in \sigma(L).
  case/setIdP=> maxL sPL; apply: contraR not_cPP => sL'p.
  exact: sigma'_nil_abelian maxL sPL (pi_pnat pP _) (pgroup_nil pP).
have{maxP_M} [[maxM sPM] sMp] := (setIdP maxP_M, sigma_p M maxP_M).
rewrite (uniq_mmax_subset1 maxM sPM); apply/subsetP=> H maxP_H; rewrite inE.
have{sigma_p maxP_H} [[maxH sPH] sHp] := (setIdP maxP_H, sigma_p H maxP_H).
without loss{pP sPH sPM} sylP: P not_cPP / p.-Sylow(M :&: H) P.
  move=> IH; have sP_MH: P \subset M :&: H by rewrite subsetI sPM.
  have [S sylS sPS] := Sylow_superset sP_MH pP.
  exact: IH (contra (abelianS sPS) not_cPP) sylS.
have [sP_MH pP _] := and3P sylP; have [sPM sPH] := subsetIP sP_MH.
have ncycP := contra (@cyclic_abelian _ _) not_cPP.
have{sHp} sNMH: 'N(P) \subset M :&: H.
  by rewrite subsetI !(@norm_noncyclic_sigma _ p).
have{sylP} sylP_M: p.-Sylow(M) P.
  have [S sylS sPS] := Sylow_superset sPM pP; have pS := pHall_pgroup sylS.
  have [-> // | ltPS] := eqVproper sPS.
  have /andP[sNP] := nilpotent_proper_norm (pgroup_nil pS) ltPS.
  rewrite (sub_pHall sylP _ sNP) ?subxx ?(pgroupS (subsetIl _ _)) //.
  by rewrite subIset // orbC sNMH.
have{sMp} sylP_G: p.-Sylow(G) P := sigma_Sylow_G maxM sMp sylP_M.
have sylP_H: p.-Sylow(H) P := pHall_subl sPH (subsetT H) sylP_G.
have [rPgt2 | rPle2] := ltnP 2 'r(P).
  have uniqP: P \in 'U by rewrite rank3_Uniqueness ?(mFT_pgroup_proper pP).
  have defMP: 'M(P) = [set M] := def_uniq_mmax uniqP maxM sPM.
  by rewrite -val_eqE /= (eq_uniq_mmax defMP maxH).
have rpP: 'r_p(P) = 2.
  apply/eqP; rewrite eqn_leq -{1}rank_pgroup // rPle2 ltnNge.
  by rewrite -odd_pgroup_rank1_cyclic ?mFT_odd.
have:= mFT_rank2_Sylow_cprod sylP_G rPle2 not_cPP.
case=> Q [not_cQQ dimQ eQ] [R cycR [defP defR1]].
have sQP: Q \subset P by have /mulG_sub[] := cprodW defP.
have pQ: p.-group Q := pgroupS sQP pP.
have oQ: #|Q| = (p ^ 3)%N by rewrite (card_pgroup pQ) dimQ.
have esQ: extraspecial Q by apply: (p3group_extraspecial pQ); rewrite ?dimQ.
have p_pr := extraspecial_prime pQ esQ; have p_gt1 := prime_gt1 p_pr.
pose Z := 'Z(Q)%G; have oZ: #|Z| = p := card_center_extraspecial pQ esQ.
have nsZQ: Z <| Q := center_normal Q; have [sZQ nZQ] := andP nsZQ.
have [[defPhiQ defQ'] _]: ('Phi(Q) = Z /\ Q^`(1) = Z) /\ _ := esQ.
have defZ: 'Ohm_1 ('Z(P)) = Z.
  have [_ <- _] := cprodP (center_cprod defP).
  by rewrite (center_idP (cyclic_abelian cycR)) -defR1 mulSGid ?Ohm_sub.
have ncycQ: ~~ cyclic Q := contra (@cyclic_abelian _ Q) not_cQQ.
have rQgt1: 'r_p(Q) > 1.
  by rewrite ltnNge -(odd_pgroup_rank1_cyclic pQ) ?mFT_odd.
have [A Ep2A]: exists A, A \in 'E_p^2(Q) by exact/p_rank_geP.
wlog uniqNEpA: M H maxM maxH sP_MH sNMH sPM sPH sylP_M sylP_H /
    ~~ [exists A0 in 'E_p^1(A) :\ Z, 'M('N(A0)) == [set M]].
- move=> IH; case: exists_inP (IH M H) => [[A0 EpA0 defMA0] _ | _ -> //].
  case: exists_inP {IH}(IH H M) => [[A1 EpA1 defMA1] _ | _]; last first.
    by rewrite setIC eq_sym => ->.
  have [sAQ abelA dimA] := pnElemP Ep2A; have sAP := subset_trans sAQ sQP.
  have transNP: [transitive 'N_P(A), on 'E_p^1(A) :\ Z | 'JG].
    have [|_ _] :=  basic_p2maxElem_structure _ pP sAP not_cPP.
      have Ep2A_G := subsetP (pnElemS p 2 (subsetT Q)) A Ep2A.
      rewrite inE Ep2A_G (subsetP (p_rankElem_max p G)) //.
      by rewrite -(p_rank_Sylow sylP_G) rpP.
    by rewrite (group_inj defZ).
  have [x NPx defA1] := atransP2 transNP EpA0 EpA1.
  have Mx: x \in M by rewrite (subsetP sPM) //; case/setIP: NPx.
  rewrite eq_sym -in_set1 -(group_inj (conjGid Mx)).
  by rewrite -(eqP defMA1) defA1 /= normJ mmax_ofJ (eqP defMA0) set11.
apply: contraR uniqNEpA => neqHM; have sQM := subset_trans sQP sPM.
suffices{A Ep2A} [ntMa nonuniqNZ]: M`_\alpha != 1 /\ 'M('N(Z)) != [set M].
  have [A0 EpA0 defMNA0]: exists2 A0, A0 \in 'E_p^1(A) & 'M('N(A0)) == [set M].
    apply/exists_inP; apply: contraR ntMa; rewrite negb_exists_in => uniqNA1.
    have{Ep2A} Ep2A: A \in 'E_p^2(M) := subsetP (pnElemS p 2 sQM) A Ep2A.
    by have [_ [//|_ ->]] := p2Elem_mmax maxM Ep2A.
  apply/exists_inP; exists A0; rewrite // 2!inE EpA0 andbT.
  by apply: contraNneq nonuniqNZ => <-.
have coMaQ: coprime #|M`_\alpha| #|Q|.
  apply: pnat_coprime (pcore_pgroup _ _) (pi_pnat pQ _).
  by rewrite !inE -(p_rank_Sylow sylP_M) rpP.
have nMaQ: Q \subset 'N(M`_\alpha) by rewrite (subset_trans sQM) ?gFnorm.
have [coMaZ nMaZ] := (coprimegS sZQ coMaQ, subset_trans sZQ nMaQ).
pose K := 'N_(M`_\alpha)(Z).
have defKC: 'C_(M`_\alpha)(Z) = K by rewrite -coprime_norm_cent.
have coKQ: coprime #|K| #|Q| := coprimeSg (subsetIl _ _) coMaQ.
have nKQ: Q \subset 'N(K) by rewrite normsI ?norms_norm.
have [coKZ nKZ] := (coprimegS sZQ coKQ, subset_trans sZQ nKQ).
have sKH: K \subset H.
  have sZH := subset_trans sZQ (subset_trans sQP sPH).
  rewrite -(quotientSGK (subsetIr _ _) sZH) /= -/Z -/K.
  have cQQb: abelian (Q / Z) by rewrite -defQ' sub_der1_abelian.
  rewrite -(coprime_abelian_gen_cent cQQb) ?coprime_morph ?quotient_norms //.
  rewrite gen_subG /= -/K -/Z; apply/bigcupsP=> Ab; rewrite andbC; case/andP.
  case/(inv_quotientN nsZQ)=> A -> sZA nsAQ; have sAQ := normal_sub nsAQ.
  rewrite (isog_cyclic (third_isog _ _ _)) // -/Z => cycQA.
  have pA: p.-group A := pgroupS sAQ pQ.
  have rAgt1: 'r_p(A) > 1.
    have [-> // | ltAQ] := eqVproper sAQ.
    rewrite ltnNge -(odd_pgroup_rank1_cyclic pA) ?mFT_odd //.
    apply: contraL cycQA => cycA /=; have cAA := cyclic_abelian cycA.
    suff <-: Z :=: A by rewrite -defPhiQ (contra (@Phi_quotient_cyclic _ Q)).
    apply/eqP; rewrite eqEcard sZA /= oZ (card_pgroup pA) (leq_exp2l _ 1) //.
    by rewrite -abelem_cyclic // /abelem pA cAA (dvdn_trans (exponentS sAQ)).
  have [A1 EpA1] := p_rank_geP rAgt1.
  rewrite -(setIidPr (subset_trans sAQ (subset_trans sQP sPH))) pnElemI in EpA1.
  have{EpA1} [Ep2A1 sA1A]:= setIdP EpA1; rewrite inE in sA1A.
  have [sCA1_H _]: 'C(A1) \subset H /\ _ := p2Elem_mmax maxH Ep2A1.
  rewrite -quotient_TI_subcent ?(subset_trans sAQ) ?(coprime_TIg coKZ) //= -/K.
  by rewrite quotientS // subIset // orbC (subset_trans (centS sA1A)).
have defM: M`_\alpha * (M :&: H) = M.
  rewrite setIC in sNMH *.
  have [defM eq_aM_bM] := nonuniq_norm_Sylow_pprod maxM maxH neqHM sylP_G sNMH.
  by rewrite [M`_\alpha](eq_pcore M eq_aM_bM).
do [split; apply: contraNneq neqHM] => [Ma1 | uniqNZ].
  by rewrite -val_eqE /= (eq_mmax maxM maxH) // -defM Ma1 mul1g subsetIr.
have [_ sNZM]: _ /\ 'N(Z) \subset M := mem_uniq_mmax uniqNZ.
rewrite -val_eqE /= (eq_uniq_mmax uniqNZ maxH) //= -(setIidPr sNZM).
have sZ_MH: Z \subset M :&: H := subset_trans sZQ (subset_trans sQP sP_MH).
rewrite -(pprod_norm_coprime_prod defM) ?pcore_normal ?mmax_sol //.
by rewrite mulG_subG /= defKC sKH setIAC subsetIr.
Qed.

(* This is B & G, Corollary 12.14. We have removed the redundant assumption   *)
(* p \in \sigma(M), and restricted the quantification over P to the part of   *)
(* the conclusion where it is mentioned.                                      *)
(* Usage note: it might be more convenient to state that P is a Sylow         *)
(* subgroup of M rather than M`_\sigma; check later use.                      *)
Corollary cent_der_sigma_uniq M p X (Ms := M`_\sigma) :
    M \in 'M -> X \in 'E_p^1(M) -> (p \in \beta(M)) || (X \subset Ms^`(1)) ->
  'M('C(X)) = [set M] /\ (forall P, p.-Sylow(Ms) P -> 'M(P) = [set M]).
Proof.
move=> maxM EpX bMp_sXMs'; have p_pr := pnElem_prime EpX.
have [sXM abelX oX] := pnElemPcard EpX; have [pX _] := andP abelX.
have ntX: X :!=: 1 := nt_pnElem EpX isT; have ltCXG := mFT_cent_proper ntX.
have sMp: p \in \sigma(M).
  have [bMp | sXMs'] := orP bMp_sXMs'; first by rewrite beta_sub_sigma.
  rewrite -pnatE // -[p]oX; apply: pgroupS (subset_trans sXMs' (der_sub 1 _)) _.
  exact: pcore_pgroup.
have hallMs: \sigma(M).-Hall(M) Ms by exact: Msigma_Hall.
have sXMs: X \subset Ms by rewrite (sub_Hall_pcore hallMs) // /pgroup oX pnatE.
have [P sylP sXP]:= Sylow_superset sXMs pX.
have sylP_M: p.-Sylow(M) P := subHall_Sylow hallMs sMp sylP.
have sylP_G := sigma_Sylow_G maxM sMp sylP_M.
have [sPM pP _] := and3P sylP_M; have ltPG := mFT_pgroup_proper pP.
suffices [-> uniqP]: 'M('C(X)) = [set M] /\ 'M(P) = [set M].
  split=> // Py sylPy; have [y Ms_y ->] := Sylow_trans sylP sylPy.
  rewrite (def_uniq_mmaxJ _ uniqP) (group_inj (conjGid _)) //.
  exact: subsetP (pcore_sub _ _) y Ms_y.
have [rCPXgt2 | rCPXle2] := ltnP 2 'r_p('C_P(X)).
  have [sCPX_P sCPX_CX] := subsetIP (subxx 'C_P(X)).
  have [ltP ltCX] := (mFT_pgroup_proper pP, mFT_cent_proper ntX).
  have sCPX_M := subset_trans sCPX_P sPM.
  have ltCPX_G := sub_proper_trans sCPX_P ltPG.
  suff uniqCPX: 'M('C_P(X)) = [set M] by rewrite !(def_uniq_mmaxS _ _ uniqCPX).
  apply: (def_uniq_mmax (rank3_Uniqueness _ _)) => //.
  exact: leq_trans (p_rank_le_rank p _).
have nnP: p.-narrow P.
  apply: wlog_neg; rewrite negb_imply; case/andP=> rP _.
  by apply/narrow_centP; rewrite ?mFT_odd //; exists X.
have{bMp_sXMs'} [bM'p sXMs']: p \notin \beta(M) /\ X \subset Ms^`(1).
  move: bMp_sXMs'; rewrite !inE -negb_exists_in.
  by case: exists_inP => // [[]]; exists P.
have defMs: 'O_p^'(Ms) ><| P = Ms.
  by have [_ hallMp' _] := beta_max_pdiv maxM bM'p; exact/sdprod_Hall_p'coreP.
have{defMs} sXP': X \subset P^`(1).
  have{defMs} [_ defMs nMp'P tiMp'P] := sdprodP defMs.
  have [injMp'P imMp'P] := isomP (quotient_isom nMp'P tiMp'P).
  rewrite -(injmSK injMp'P) // morphim_der // {injMp'P}imMp'P morphim_restrm.
  rewrite (setIidPr sXP) /= -quotientMidl defMs -quotient_der ?quotientS //.
  by rewrite -defMs mul_subG ?normG.
have [rPgt2 | rPle2] := ltnP 2 'r_p(P).
  case/eqP: ntX; rewrite -(setIidPl sXP').
  by case/(narrow_cent_dprod pP (mFT_odd P)): rCPXle2.
have not_cPP: ~~ abelian P.
  by rewrite (sameP derG1P eqP) (subG1_contra sXP') ?ntX.
have sXZ: X \subset 'Z(P).
  rewrite -rank_pgroup // in rPle2.
  have := mFT_rank2_Sylow_cprod sylP_G rPle2 not_cPP.
  case=> Q [not_cQQ dimQ _] [R]; move/cyclic_abelian=> cRR [defP _].
  have [_ mulQR _] := cprodP defP; have [sQP _] := mulG_sub mulQR.
  rewrite (subset_trans sXP') // -(der_cprod 1 defP) (derG1P cRR) cprodg1.
  have{dimQ} dimQ: logn p #|Q| <= 3 by rewrite dimQ.
  have [[_ ->] _] := p3group_extraspecial (pgroupS sQP pP) not_cQQ dimQ.
  by case/cprodP: (center_cprod defP) => _ <- _; exact: mulG_subl.
have uniqP: 'M(P) = [set M].
  exact: def_uniq_mmax (nonabelian_Uniqueness pP not_cPP) maxM sPM.
rewrite (def_uniq_mmaxS _ ltCXG uniqP) //.
by rewrite centsC (subset_trans sXZ) // subsetIr.
Qed.

(* This is B & G, Proposition 12.15. *)
Proposition sigma_subgroup_embedding M q X Mstar :
    M \in 'M -> q \in \sigma(M) -> X \subset M -> q.-group X -> X :!=: 1 ->
    Mstar \in 'M('N(X)) :\ M -> 
 [/\ (*a*) gval Mstar \notin M :^: G,
           forall S, q.-Sylow(M :&: Mstar) S -> X \subset S ->
       (*b*) 'N(S) \subset M
    /\ (*c*) q.-Sylow(Mstar) S
    & if q \in \sigma(Mstar)
     (*d*) then 
     [/\ (*1*) Mstar`_\beta * (M :&: Mstar) = Mstar,
         (*2*) {subset \tau1(Mstar) <= [predU \tau1(M) & \alpha(M)]}
       & (*3*) M`_\beta = M`_\alpha /\ M`_\alpha != 1]
     (*e*) else
     [/\ (*1*) q \in \tau2(Mstar),
         (*2*) {subset [predI \pi(M) & \sigma(Mstar)] <= \beta(Mstar)}
       & (*3*) \sigma(Mstar)^'.-Hall(Mstar) (M :&: Mstar)]].
Proof.
move: Mstar => H maxM sMq sXM qX ntX /setD1P[neqHM maxNX_H].
have [q_pr _ _] := pgroup_pdiv qX ntX; have [maxH sNX_H] := setIdP maxNX_H.
have sXH := subset_trans (normG X) sNX_H.
have sX_MH: X \subset M :&: H by apply/subsetIP.
have parts_bc S:
  q.-Sylow(M :&: H) S -> X \subset S -> 'N(S) \subset M /\ q.-Sylow(H) S.
- move=> sylS sXS; have [sS_MH qS _] := and3P sylS.
  have [sSM sSH] := subsetIP sS_MH.
  have sNS_M: 'N(S) \subset M.
    have [cycS|] := boolP (cyclic S); last exact: norm_noncyclic_sigma qS _.
    have [T sylT sST] := Sylow_superset sSM qS; have [sTM qT _] := and3P sylT.
    rewrite -(nilpotent_sub_norm (pgroup_nil qT) sST).
      exact: norm_sigma_Sylow sylT.
    rewrite (sub_pHall sylS (pgroupS (subsetIl T _) qT)) //.
      by rewrite subsetI sST normG.
    by rewrite setISS // (subset_trans (char_norms _) sNX_H) // sub_cyclic_char.
  split=> //; have [T sylT sST] := Sylow_superset sSH qS.
  have [sTH qT _] := and3P sylT.
  rewrite -(nilpotent_sub_norm (pgroup_nil qT) sST) //.
  rewrite (sub_pHall sylS (pgroupS (subsetIl T _) qT)) //=.
    by rewrite subsetI sST normG.
  by rewrite /= setIC setISS.
have [S sylS sXS] := Sylow_superset sX_MH qX; have [sS_MH qS _] := and3P sylS.
have [sSM sSH] := subsetIP sS_MH; have [sNS_M sylS_H] := parts_bc S sylS sXS.
have notMGH: gval H \notin M :^: G.
  by apply: mmax_norm_notJ maxM maxH qX sXM sNX_H _; rewrite sMq eq_sym neqHM.
have /orP[sHq | t2Hq] := prime_class_mmax_norm maxH qX sNX_H; last first.
  have [/= sH'q rqH] := andP t2Hq; rewrite [q \in _](negPf sH'q); split=> //.
  have [A Eq2A] := p_rank_witness q S; have [sAS abelA dimA] := pnElemP Eq2A.
  rewrite (p_rank_Sylow sylS_H) (eqP rqH) in dimA; have [qA _] := andP abelA.
  have [sAH sAM] := (subset_trans sAS sSH, subset_trans sAS sSM).
  have [F hallF sAF] := Hall_superset (mmax_sol maxH) sAH (pi_pnat qA sH'q).
  have tiHsM: H`_\sigma :&: M = 1.
    have{Eq2A} Eq2A: A \in 'E_q^2(H) by apply/pnElemP.
    have [_ _ _ -> //] := tau2_context maxH t2Hq Eq2A.
    by rewrite 3!inE eq_sym neqHM maxM.
  have{Eq2A} Eq2A_F: A \in 'E_q^2(F) by apply/pnElemP.
  have [[nsAF _] [sCA_F _ _] _ TIsH]
    := tau2_compl_context maxH hallF t2Hq Eq2A_F.
  have sNA_M: 'N(A) \subset M.
    apply: norm_noncyclic_sigma maxM sMq qA sAM _.
    by rewrite (abelem_cyclic abelA) dimA.
  have ->: M :&: H = F.
    have [[_ <- _ _] [_ nAF]] := (sdprodP (sdprod_sigma maxH hallF), andP nsAF).
    by rewrite -(group_modr _ (subset_trans nAF sNA_M)) setIC tiHsM mul1g.
  split=> // p /andP[/= piMp sHp]; apply: wlog_neg => bH'p.
  have bM'q: q \notin \beta(M).
    by rewrite -predI_sigma_beta // inE /= sMq; case/tau2_not_beta: t2Hq.
  have sM'p: p \notin \sigma(M).
    rewrite orbit_sym in notMGH; have [_ TIsHM] := TIsH M maxM notMGH.
    by have:= TIsHM p; rewrite inE /= sHp /= => ->.
  have p'CA: p^'.-group 'C(A).
    by rewrite (pgroupS sCA_F) // (pi'_p'group (pHall_pgroup hallF)).
  have p_pr: prime p by rewrite mem_primes in piMp; case/andP: piMp.
  have [lt_pq | lt_qp | eq_pq] := ltngtP p q; last 1 first.
  - by rewrite eq_pq sMq in sM'p.
  - have bH'q: q \notin \beta(H) by apply: contra sH'q; apply: beta_sub_sigma.
    have [|[P sylP cPA] _ _] := beta'_cent_Sylow maxH bH'p bH'q qA.
      by rewrite lt_pq sAH orbT.
    have sylP_H := subHall_Sylow (Msigma_Hall maxH) sHp sylP.
    have piPp: p \in \pi(P).
      by rewrite -p_rank_gt0 (p_rank_Sylow sylP_H) p_rank_gt0 sigma_sub_pi.
    by rewrite centsC in cPA; case/eqnP: (pnatPpi (pgroupS cPA p'CA) piPp).
  have bM'p: p \notin \beta(M) by apply: contra sM'p; apply: beta_sub_sigma.
  have [P sylP] := Sylow_exists p M; have [sMP pP _] := and3P sylP.
  have [|[Q1 sylQ1 cQ1P] _ _] := beta'_cent_Sylow maxM bM'q bM'p pP.
    by rewrite lt_qp sMP orbT.
  have sylQ1_M := subHall_Sylow (Msigma_Hall maxM) sMq sylQ1.
  have [x Mx sAQ1x] := Sylow_subJ sylQ1_M sAM qA.
  have sPxCA: P :^ x \subset 'C(A) by rewrite (centsS sAQ1x) // centJ conjSg.
  have piPx_p: p \in \pi(P :^ x).
    by rewrite /= cardJg -p_rank_gt0 (p_rank_Sylow sylP) p_rank_gt0.
  by case/eqnP: (pnatPpi (pgroupS sPxCA p'CA) piPx_p).
rewrite sHq; split=> //.
have sNS_HM: 'N(S) \subset H :&: M by rewrite subsetI (norm_sigma_Sylow sHq).
have sylS_G: q.-Sylow(G) S := sigma_Sylow_G maxH sHq sylS_H.
have [defM eq_abM] := nonuniq_norm_Sylow_pprod maxM maxH neqHM sylS_G sNS_HM.
rewrite setIC eq_sym in sNS_HM neqHM defM.
have [defH eq_abH] := nonuniq_norm_Sylow_pprod maxH maxM neqHM sylS_G sNS_HM.
rewrite [M`_\alpha](eq_pcore M eq_abM) -/M`_\beta.
split=> // [r t1Hr|]; last first.
  split=> //; apply: contraNneq neqHM => Mb1.
  by rewrite -val_eqE /= (eq_mmax maxM maxH) // -defM Mb1 mul1g subsetIr.
have [R sylR] := Sylow_exists r (M :&: H); have [sR_MH rR _] := and3P sylR.
have [sRM sRH] := subsetIP sR_MH; have [sH'r rrH not_rH'] := and3P t1Hr.
have bH'r: r \notin \beta(H).
  by apply: contra sH'r; rewrite -eq_abH; apply: alpha_sub_sigma.
have sylR_H: r.-Sylow(H) R.
  rewrite pHallE sRH -defH -LagrangeMr partnM ?cardG_gt0 //.
  rewrite -(card_Hall sylR) part_p'nat ?mul1n ?(pnat_dvd (dvdn_indexg _ _)) //=.
  by rewrite (pi_p'nat (pcore_pgroup _ _)).
rewrite inE /= orbC -implyNb eq_abM; apply/implyP=> bM'r.
have sylR_M: r.-Sylow(M) R.
  rewrite pHallE sRM -defM -LagrangeMr partnM ?cardG_gt0 //.
  rewrite -(card_Hall sylR) part_p'nat ?mul1n ?(pnat_dvd (dvdn_indexg _ _)) //=.
  by rewrite (pi_p'nat (pcore_pgroup _ _)).
have rrR: 'r_r(R) = 1%N by rewrite (p_rank_Sylow sylR_H) (eqP rrH).
have piRr: r \in \pi(R) by rewrite -p_rank_gt0 rrR.
suffices not_piM'r: r \notin \pi(M^`(1)).
  rewrite inE /= -(p_rank_Sylow sylR_M) rrR /= -negb_or /=.
  apply: contra not_piM'r; case/orP=> [sMr | rM'].
    have sRMs: R \subset M`_\sigma.
      by rewrite (sub_Hall_pcore (Msigma_Hall maxM)) ?(pi_pgroup rR).
    by rewrite (piSg (Msigma_der1 maxM)) // (piSg sRMs).
  by move: piRr; rewrite !mem_primes !cardG_gt0; case/andP=> ->.
have coMbR: coprime #|M`_\beta| #|R|.
  exact: pnat_coprime (pcore_pgroup _ _) (pi_pnat rR _).
have sylRM': r.-Sylow(M^`(1)) _ := Hall_setI_normal (der_normal 1 M) sylR_M.
rewrite -p'groupEpi -partG_eq1 -(card_Hall sylRM') -trivg_card1 /=.
rewrite (pprod_focal_coprime defM (pcore_normal _ _)) //.
rewrite coprime_TIg ?(pnat_coprime rR (pgroupS (dergS 1 (subsetIr _ _)) _)) //.
by rewrite p'groupEpi mem_primes (negPf not_rH') !andbF.
Qed.

(* This is B & G, Corollary 12.16. *)
Corollary sigma_Jsub M Y :
    M \in 'M -> \sigma(M).-group Y -> Y :!=: 1 ->
  [/\ exists x, Y :^ x \subset M`_\sigma
    & forall E p H,
        \sigma(M)^'.-Hall(M) E -> p \in \pi(E) -> p \notin \beta(G) ->
        H \in 'M(Y) -> gval H \notin M :^: G ->
    [/\ (*a*) 'r_p('N_H(Y)) <= 1
      & (*b*) p \in \tau1(M) -> p \notin \pi(('N_H(Y))^`(1))]].
Proof.
move=> maxM sM_Y ntY.
have ltYG: Y \proper G.
  have ltMsG: M`_\sigma \proper G.
    exact: sub_proper_trans (pcore_sub _ _) (mmax_proper maxM).
  rewrite properEcard subsetT (leq_ltn_trans _ (proper_card ltMsG)) //.
  rewrite dvdn_leq ?cardG_gt0 // (card_Hall (Msigma_Hall_G maxM)).
  by rewrite -(part_pnat_id sM_Y) partn_dvd // cardSg ?subsetT.
have [q q_pr rFY] := rank_witness 'F(Y).
have [X [ntX qX charX]]: exists X, [/\ gval X :!=: 1, q.-group X & X \char Y].
  exists ('O_q(Y))%G; rewrite pcore_pgroup pcore_char //.
  rewrite -rank_gt0 /= -p_core_Fitting.
  rewrite (rank_Sylow (nilpotent_pcore_Hall q (Fitting_nil Y))) -rFY.
  by rewrite rank_gt0 (trivg_Fitting (mFT_sol ltYG)).
have sXY: X \subset Y := char_sub charX.
have sMq: q \in \sigma(M).
  apply: (pnatPpi (pgroupS sXY sM_Y)).
  by rewrite -p_rank_gt0 -(rank_pgroup qX) rank_gt0.
without loss sXMs: M maxM sM_Y sMq / X \subset M`_\sigma.
  move=> IH; have [Q sylQ] := Sylow_exists q M`_\sigma.
  have sQMs := pHall_sub sylQ.
  have sylQ_G := subHall_Sylow (Msigma_Hall_G maxM) sMq sylQ.
  have [x Gx sXQx] := Sylow_subJ sylQ_G (subsetT X) qX.
  have: X \subset M`_\sigma :^ x by rewrite (subset_trans sXQx) ?conjSg.
  rewrite -MsigmaJ => /IH; rewrite sigmaJ mmaxJ (eq_pgroup _ (sigmaJ _ _)).
  case => // [[y sYyMx] parts_ab].
  split=> [|E p H hallE piEp bG'p maxY_H notMGH].
    by exists (y * x^-1); rewrite conjsgM sub_conjgV -MsigmaJ.
  have:= parts_ab (E :^ x)%G p H; rewrite tau1J /= cardJg pHallJ2.
  rewrite (eq_pHall _ _ (eq_negn (sigmaJ _ _))).
  by rewrite 2!orbit_sym (orbit_transl (mem_orbit _ _ _)) //; apply.
have pre_part_a E p H:
     \sigma(M)^'.-Hall(M) E -> p \in \pi(E) ->
  H \in 'M(Y) -> gval H \notin M :^: G -> 'r_p(H :&: M) <= 1.
- move=> hallE piEp /setIdP[maxH sYH] notMGH; rewrite leqNgt.
  apply: contra ntX => /p_rank_geP[A /pnElemP[/subsetIP[sAH sAM] abelA dimA]].
  have{abelA dimA} Ep2A: A \in 'E_p^2(M) by apply/pnElemP.
  have rpMgt1: 'r_p(M) > 1 by apply/p_rank_geP; exists A.
  have t2Mp: p \in \tau2(M).
    move: piEp; rewrite (partition_pi_sigma_compl maxM hallE) orbCA orbC.
    by rewrite -2!andb_orr orNb eqn_leq leqNgt rpMgt1 !andbF.
  have sM'p := pnatPpi (pHall_pgroup hallE) piEp.
  have [_ _ _ tiMsH _] := tau2_context maxM t2Mp Ep2A.
  rewrite -subG1 -(tiMsH H); first by rewrite subsetI sXMs (subset_trans sXY).
  by rewrite 3!inE maxH (contra_orbit _ _ notMGH).
have [sNX_M | not_sNX_M] := boolP ('N(X) \subset M).
  have sNY_M: 'N(Y) \subset M := subset_trans (char_norms charX) sNX_M.
  split=> [|E p H hallE piEp bG'p maxY_H notMGH]; last split.
  - exists 1; rewrite act1 (sub_Hall_pcore (Msigma_Hall maxM)) //.
    exact: subset_trans (normG Y) sNY_M.
  - rewrite (leq_trans (p_rankS p (setIS H sNY_M))) ?(pre_part_a E) //.
  case/and3P=> _ _; apply: contra; rewrite mem_primes => /and3P[_ _ pM'].
  by apply: dvdn_trans pM' (cardSg (dergS 1 _)); rewrite subIset ?sNY_M ?orbT.
have [L maxNX_L] := mmax_exists (mFT_norm_proper ntX (mFT_pgroup_proper qX)).
have [maxL sNX_L] := setIdP maxNX_L.
have{maxNX_L} maxNX_L: L \in 'M('N(X)) :\ M.
  by rewrite 2!inE maxNX_L andbT; apply: contraNneq not_sNX_M => <-.
have sXM := subset_trans sXMs (pcore_sub _ M).
have [notMGL _ embedL] := sigma_subgroup_embedding maxM sMq sXM qX ntX maxNX_L.
pose K := (if q \in \sigma(L) then L`_\beta else L`_\sigma)%G.
have sM'K: \sigma(M)^'.-group K.
  rewrite orbit_sym in notMGL.
  rewrite /K; case: (boolP (q \in _)) embedL => [sLq _ | sL'q [t2Lq _ _]].
    have [_ TIaLsM _] := sigma_disjoint maxL maxM notMGL.
    apply: sub_pgroup (pcore_pgroup _ _) => p bLp.
    by apply: contraFN (TIaLsM p) => /= sMp; rewrite inE /= beta_sub_alpha.
  have [F hallF] := ex_sigma_compl maxL.
  have [A Ep2A _] := ex_tau2Elem hallF t2Lq.
  have [_ _ _ TIsLs] := tau2_compl_context maxL hallF t2Lq Ep2A.
  have{TIsLs} [_ TIsLsM] := TIsLs M maxM notMGL.
  apply: sub_pgroup (pcore_pgroup _ _) => p sLp.
  by apply: contraFN (TIsLsM p) => /= sMp; rewrite inE /= sLp.
have defL: K * (M :&: L) = L.
  rewrite /K; case: (q \in _) embedL => [] [] // _ _.
  by move/(sdprod_Hall_pcoreP (Msigma_Hall maxL)); case/sdprodP.
have sYL := subset_trans (char_norm charX) sNX_L.
have [x sYxMs]: exists x, Y :^ x \subset M`_\sigma.
  have solML := solvableS (subsetIl M L) (mmax_sol maxM).
  have [H hallH] := Hall_exists \sigma(M) solML.
  have [sHM sHL] := subsetIP (pHall_sub hallH).
  have hallH_L: \sigma(M).-Hall(L) H.
    rewrite pHallE sHL -defL -LagrangeMr partnM ?cardG_gt0 //.
    rewrite -(card_Hall hallH) part_p'nat ?mul1n //=.
    exact: pnat_dvd (dvdn_indexg _ _) sM'K.
  have [x _ sYxH]:= Hall_Jsub (mmax_sol maxL) hallH_L sYL sM_Y.
  exists x; rewrite (sub_Hall_pcore (Msigma_Hall maxM)) ?pgroupJ //.
  exact: subset_trans sYxH sHM.
split=> [|E p H hallE piEp bG'p maxY_H notMGH]; first by exists x.
have p'K: p^'.-group K.
  have bL'p: p \notin \beta(L).
    by rewrite -predI_sigma_beta // negb_and bG'p orbT.
  rewrite /K; case: (q \in _) embedL => [_ | [_ bLp _]].
    by rewrite (pi_p'group (pcore_pgroup _ _)).
  rewrite (pi_p'group (pcore_pgroup _ _)) //; apply: contra bL'p => /= sLp.
  by rewrite bLp // inE /= (piSg (pHall_sub hallE)).
have sNHY_L: 'N_H(Y) \subset L.
  by rewrite subIset ?(subset_trans (char_norms charX)) ?orbT.
rewrite (leq_trans (p_rankS p sNHY_L)); last first.
  have [P sylP] := Sylow_exists p (M :&: L).
  have [_ sPL] := subsetIP (pHall_sub sylP).
  have{sPL} sylP_L: p.-Sylow(L) P.
    rewrite pHallE sPL -defL -LagrangeMr partnM ?cardG_gt0 //.
    rewrite -(card_Hall sylP) part_p'nat ?mul1n //=.
    exact: pnat_dvd (dvdn_indexg _ _) p'K.
  rewrite -(p_rank_Sylow sylP_L) {P sylP sylP_L}(p_rank_Sylow sylP).
  by rewrite /= setIC (pre_part_a E) // inE maxL.
split=> // t1Mp; rewrite (contra ((piSg (dergS 1 sNHY_L)) p)) // -p'groupEpi.
have nsKL: K <| L by rewrite /K; case: ifP => _; apply: pcore_normal.
have [sKL nKL] := andP nsKL; have nKML := subset_trans (subsetIr M L) nKL.
suffices: p^'.-group (K * (M :&: L)^`(1)).
  have sder := subset_trans (der_sub 1 _).
  rewrite -norm_joinEr ?sder //; apply: pgroupS => /=.
  rewrite norm_joinEr -?quotientSK ?sder //= !quotient_der //.
  by rewrite -{1}defL quotientMidl.
rewrite pgroupM p'K (pgroupS (dergS 1 (subsetIl M L))) // p'groupEpi.
by rewrite mem_primes andbA andbC negb_and; case/and3P: t1Mp => _ _ ->.
Qed.

(* This is B & G, Lemma 12.17. *)
Lemma sigma_compl_embedding M E (Ms := M`_\sigma) :
    M \in 'M -> \sigma(M)^'.-Hall(M) E ->
 [/\ 'C_Ms(E) \subset Ms^`(1), [~: Ms, E] = Ms
   & forall g (MsMg := Ms :&: M :^ g), g \notin M ->
     [/\ cyclic MsMg, \beta(M)^'.-group MsMg & MsMg :&: Ms^`(1) = 1]].
Proof.
move=> maxM hallE; have [sEM s'E _] := and3P hallE.
have solMs: solvable Ms := solvableS (pcore_sub _ _) (mmax_sol maxM).
have defM := coprime_der1_sdprod (sdprod_sigma maxM hallE).
have{s'E} coMsE: coprime #|Ms| #|E| := pnat_coprime (pcore_pgroup _ _) s'E.
have{defM coMsE} [-> ->] := defM coMsE solMs (Msigma_der1 maxM).
split=> // g MsMg notMg.
have sMsMg: \sigma(M).-group MsMg := pgroupS (subsetIl _ _) (pcore_pgroup _ _).
have EpMsMg p n X: X \in 'E_p^n(MsMg) -> n > 0 ->
  n = 1%N /\ ~~ ((p \in \beta(M)) || (X \subset Ms^`(1))).
- move=> EpX n_gt0; have [sXMsMg abelX dimX] := pnElemP EpX.
  have [[sXMs sXMg] [pX _]] := (subsetIP sXMsMg, andP abelX).
  have sXM := subset_trans sXMs (pcore_sub _ _).
  have piXp: p \in \pi(X) by rewrite -p_rank_gt0 p_rank_abelem ?dimX.
  have sMp: p \in \sigma(M) := pnatPpi (pgroupS sXMs (pcore_pgroup _ _)) piXp.
  have not_sCX_M: ~~ ('C(X) \subset M).
    apply: contra notMg => sCX_M; rewrite -groupV.
    have [transCX _ _] := sigma_group_trans maxM sMp pX.
    have [|c CXc [m Mm ->]] := transCX g^-1 sXM; rewrite ?sub_conjgV //.
    by rewrite groupM // (subsetP sCX_M).
  have cycX: cyclic X.
    apply: contraR not_sCX_M => ncycX; apply: subset_trans (cent_sub _) _.
    exact: norm_noncyclic_sigma maxM sMp pX sXM ncycX.
  have n1: n = 1%N by apply/eqP; rewrite eqn_leq -{1}dimX -abelem_cyclic ?cycX.
  rewrite n1 in dimX *; split=> //; apply: contra not_sCX_M.
  by case/cent_der_sigma_uniq=> //; [apply/pnElemP | case/mem_uniq_mmax].
have tiMsMg_Ms': MsMg :&: Ms^`(1) = 1.
  apply/eqP/idPn; rewrite -rank_gt0 => /rank_geP[X /nElemP[p]].
  case/pnElemP=> /subsetIP[sXMsMg sXMs'] abelX dimX.
  by case: (EpMsMg p 1%N X) => //; [apply/pnElemP | rewrite sXMs' orbT].
split=> //; last first.
  apply: sub_in_pnat sMsMg => p.
  by rewrite -p_rank_gt0 => /p_rank_geP[X /EpMsMg[] // _ /norP[]].
rewrite abelian_rank1_cyclic.
  by rewrite leqNgt; apply/rank_geP=> [[X /nElemP[p /EpMsMg[]]]].
by rewrite (sameP derG1P trivgP) -tiMsMg_Ms' subsetI der_sub dergS ?subsetIl.
Qed.

(* This is B & G, Lemma 12.18. *)
(* We corrected an omission in the text, which fails to quote Lemma 10.3 to   *)
(* justify the two p-rank inequalities (12.5) and (12.6), and indeed          *)
(* erroneously refers to 12.2(a) for (12.5). Note also that the loosely       *)
(* justified equalities of Ohm_1 subgroups are in fact unnecessary.           *)
Lemma cent_Malpha_reg_tau1 M p q P Q (Ma := M`_\alpha) :
    M \in 'M -> p \in \tau1(M) -> q \in p^' -> P \in 'E_p^1(M) -> Q :!=: 1 ->
    P \subset 'N(Q) -> 'C_Q(P) = 1 -> 'M('N(Q)) != [set M] ->
  [/\ (*a*) Ma != 1 -> q \notin \alpha(M) -> q.-group Q -> Q \subset M ->
            'C_Ma(P) != 1 /\ 'C_Ma(Q <*> P) = 1
    & (*b*) q.-Sylow(M) Q ->
            [/\ \alpha(M) =i \beta(M), Ma != 1, q \notin \alpha(M),
                'C_Ma(P) != 1 & 'C_Ma(Q <*> P) = 1]].
Proof.
move=> maxM t1p p'q EpP ntQ nQP regPQ nonuniqNQ.
set QP := Q <*> P; set CaQP := 'C_Ma(QP); set part_a := _ -> _.
have ssolM := solvableS _ (mmax_sol maxM).
have [sPM abelP oP] := pnElemPcard EpP; have{abelP} [pP _] := andP abelP.
have p_pr := pnElem_prime EpP; have [s'p _] := andP t1p.
have a'p: p \in \alpha(M)^' by apply: contra s'p; apply: alpha_sub_sigma.
have{a'p} [a'P t2'p] := (pi_pgroup pP a'p, tau2'1 t1p).
have uniqCMX: 'M('C_M(_)) = [set M] := def_uniq_mmax _ maxM (subsetIl _ _).
have nQ_CMQ: 'C_M(Q) \subset 'N(Q) by rewrite setIC subIset ?cent_sub.
have part_a_holds: part_a.
  move=> ntMa a'q qQ sQM; have{p'q} p'Q := pi_pgroup qQ p'q.
  have{p'Q} coQP: coprime #|Q| #|P| by rewrite coprime_sym (pnat_coprime pP).
  have{a'q} a'Q: \alpha(M)^'.-group Q by rewrite (pi_pgroup qQ).
  have rCMaQle1: 'r('C_Ma(Q)) <= 1.
    rewrite leqNgt; apply: contra nonuniqNQ => rCMaQgt1; apply/eqP.
    apply: def_uniq_mmaxS (uniqCMX Q _) => //; last exact: cent_alpha'_uniq.
    exact: mFT_norm_proper (mFT_pgroup_proper qQ).
  have rCMaPle1: 'r('C_Ma(P)) <= 1.
    have: ~~ ('N(P) \subset M).
      by apply: contra (prime_class_mmax_norm maxM pP) _; apply/norP.
    rewrite leqNgt; apply: contra => rCMaPgt1.
    apply: (sub_uniq_mmax (uniqCMX P _)); first exact: cent_alpha'_uniq.
      by rewrite /= setIC subIset ?cent_sub.
    exact: mFT_norm_proper (nt_pnElem EpP _) (mFT_pgroup_proper pP).
  have [sMaM nMaM] := andP (pcore_normal _ M : Ma <| M).
  have aMa: \alpha(M).-group Ma by rewrite pcore_pgroup.
  have nMaQP: QP \subset 'N(Ma) by rewrite join_subG !(subset_trans _ nMaM).
  have{nMaM} coMaQP: coprime #|Ma| #|QP|.
    by rewrite (pnat_coprime aMa) ?[QP]norm_joinEr // [pnat _ _]pgroupM ?a'Q.
  pose r := pdiv #|if CaQP == 1 then Ma else CaQP|.
  have{ntMa} piMar: r \in \pi(Ma).
    rewrite /r; case: ifPn => [_| ntCaQP]; first by rewrite pi_pdiv cardG_gt1.
    by rewrite (piSg (subsetIl Ma 'C(QP))) // pi_pdiv cardG_gt1.
  have{aMa} a_r: r \in \alpha(M) := pnatPpi aMa piMar.
  have [r'Q r'P] : r^'.-group Q /\ r^'.-group P by rewrite !(pi'_p'group _ a_r).
  have [Rc /= sylRc] := Sylow_exists r [group of CaQP].
  have [sRcCaQP rRc _] := and3P sylRc; have [sRcMa cQPRc] := subsetIP sRcCaQP.
  have nRcQP: QP \subset 'N(Rc) by rewrite cents_norm // centsC.
  have{nMaQP rRc coMaQP sRcCaQP sRcMa nRcQP} [R [sylR nR_QP sRcR]] :=
    coprime_Hall_subset nMaQP coMaQP (ssolM _ sMaM) sRcMa rRc nRcQP.
  have{nR_QP} [[sRMa rR _] [nRQ nRP]] := (and3P sylR, joing_subP nR_QP).
  have{piMar} ntR: R :!=: 1 by rewrite -rank_gt0 (rank_Sylow sylR) p_rank_gt0.
  have [r_pr _ _] := pgroup_pdiv rR ntR.
  have sylR_M := subHall_Sylow (Malpha_Hall maxM) a_r sylR.
  have{rCMaQle1 a_r} not_cRQ: ~~ (Q \subset 'C(R)).
    apply: contraL rCMaQle1; rewrite centsC => cQR; rewrite -ltnNge ltnW //.
    by rewrite (leq_trans a_r) // -(rank_Sylow sylR_M) rankS // subsetI sRMa.
  have [R1 [charR1 _ _ expR1 rCR1_AutR]] := critical_odd rR (mFT_odd R) ntR.
  have [sR1R nR1R] := andP (char_normal charR1); have rR1 := pgroupS sR1R rR.
  have [nR1P nR1Q] := (char_norm_trans charR1 nRP, char_norm_trans charR1 nRQ).
  have [coR1Q coR1P] := (pnat_coprime rR1 r'Q, pnat_coprime rR1 r'P).
  have {rCR1_AutR not_cRQ} not_cR1Q: ~~ (Q \subset 'C(R1)).
    apply: contra not_cRQ => cR1Q; rewrite -subsetIidl.
    rewrite -quotient_sub1 ?normsI ?normG ?norms_cent // subG1 trivg_card1.
    rewrite (pnat_1 _ (quotient_pgroup _ r'Q)) //= -ker_conj_aut.
    rewrite (card_isog (first_isog_loc _ _)) //; apply: pgroupS rCR1_AutR.
    apply/subsetP=> za; case/morphimP=> z nRz Qz ->; rewrite inE Aut_aut inE.
    apply/subsetP=> x R1x; rewrite inE [_ x _]norm_conj_autE ?(subsetP sR1R) //.
    by rewrite /conjg -(centsP cR1Q z) ?mulKg.
  pose R0 := 'C_R1(Q); have sR0R1: R0 \subset R1 := subsetIl R1 'C(Q).
  have nR0P: P \subset 'N(R0) by rewrite normsI ?norms_cent.
  have nR0Q: Q \subset 'N(R0) by rewrite normsI ?norms_cent ?normG.
  pose R1Q := R1 <*> Q; have defR1Q: R1 * Q = R1Q by rewrite -norm_joinEr.
  have [[sR1_R1Q sQ_R1Q] tiR1Q] := (joing_sub (erefl R1Q), coprime_TIg coR1Q).
  have not_nilR1Q: ~~ nilpotent R1Q.
    by apply: contra not_cR1Q => /sub_nilpotent_cent2; apply.
  have not_nilR1Qb: ~~ nilpotent (R1Q / R0).
    apply: contra not_cR1Q => nilR1Qb.
    have [nilR1 solR1] := (pgroup_nil rR1, pgroup_sol rR1).
    rewrite centsC -subsetIidl -(nilpotent_sub_norm nilR1 sR0R1) //= -/R0.
    rewrite -(quotientSGK (subsetIr R1 _)) ?coprime_quotient_cent  //= -/R0.
    rewrite quotientInorm subsetIidl /= centsC -/R0.
    by rewrite (sub_nilpotent_cent2 nilR1Qb) ?quotientS ?coprime_morph.
  have coR1QP: coprime #|R1Q| #|P|.
    by rewrite -defR1Q TI_cardMg // coprime_mull coR1P.
  have defR1QP: R1Q ><| P = R1Q <*> P.
    by rewrite sdprodEY ?normsY ?coprime_TIg.
  have sR1Ma := subset_trans sR1R sRMa; have sR1M := subset_trans sR1Ma sMaM.
  have solR1Q: solvable R1Q by rewrite ssolM // !join_subG sR1M.
  have solR1QP: solvable (R1Q <*> P) by rewrite ssolM // !join_subG sR1M sQM.
  have defCR1QP: 'C_R1Q(P) = 'C_R1(P).
    by rewrite -defR1Q -subcent_TImulg ?regPQ ?mulg1 //; apply/subsetIP.
  have ntCR1P: 'C_R1(P) != 1.
    apply: contraNneq not_nilR1Q => regPR1.
    by rewrite (prime_Frobenius_sol_kernel_nil defR1QP) ?oP ?defCR1QP.
  split; first exact: subG1_contra (setSI _ sR1Ma) ntCR1P.
  have{rCMaPle1} cycCRP: cyclic 'C_R(P).
    have rCRP: r.-group 'C_R(P) := pgroupS (subsetIl R _) rR.
    rewrite (odd_pgroup_rank1_cyclic rCRP) ?mFT_odd -?rank_pgroup {rCRP}//.
    by rewrite (leq_trans (rankS _) rCMaPle1) ?setSI.
  have{ntCR1P} oCR1P: #|'C_R1(P)| = r.
    have cycCR1P: cyclic 'C_R1(P) by rewrite (cyclicS _ cycCRP) ?setSI.
    apply: cyclic_abelem_prime ntCR1P => //.
    by rewrite abelemE ?cyclic_abelian // -expR1 exponentS ?subsetIl.
  apply: contraNeq not_nilR1Qb => ntCaQP.
  have{Rc sRcR sylRc cQPRc ntCaQP} ntCRQP: 'C_R(QP) != 1.
    suffices: Rc :!=: 1 by apply: subG1_contra; apply/subsetIP.
    rewrite -rank_gt0 (rank_Sylow sylRc) p_rank_gt0.
    by rewrite /r (negPf ntCaQP) pi_pdiv cardG_gt1.
  have defR1QPb: (R1Q / R0) ><| (P / R0) = R1Q <*> P / R0.
    have [_ <- nR1QP _] := sdprodP defR1QP; rewrite quotientMr //.
    by rewrite sdprodE ?quotient_norms // coprime_TIg ?coprime_morph.
  have tiPR0: R0 :&: P = 1 by rewrite coprime_TIg // (coprimeSg sR0R1).
  have prPb: prime #|P / R0| by rewrite -(card_isog (quotient_isog _ _)) ?oP.
  rewrite (prime_Frobenius_sol_kernel_nil defR1QPb) ?quotient_sol //.
  rewrite -coprime_quotient_cent ?(subset_trans sR0R1) // quotientS1 //=.
  rewrite defCR1QP -{2}(setIidPl sR1R) -setIA subsetI subsetIl.
  apply: subset_trans (setIS R (centS (joing_subl Q P))).
  rewrite -(cardSg_cyclic cycCRP) ?setIS ?setSI ?centS ?joing_subr // oCR1P.
  by have [_ -> _] := pgroup_pdiv (pgroupS (subsetIl R _) rR) ntCRQP.
split=> // sylQ; have [sQM qQ _] := and3P sylQ.
have ltQG := mFT_pgroup_proper qQ; have ltNQG := mFT_norm_proper ntQ ltQG.
have{p'q} p'Q := pi_pgroup qQ p'q.
have{p'Q} coQP: coprime #|Q| #|P| by rewrite coprime_sym (pnat_coprime pP).
have sQM': Q \subset M^`(1).
  by rewrite -(coprime_cent_prod nQP) ?ssolM // regPQ mulg1 commgSS.
have ntMa: Ma != 1.
  apply: contraNneq nonuniqNQ => Ma1.
  rewrite (mmax_normal maxM _ ntQ) ?mmax_sup_id //.
  apply: char_normal_trans (der_normal 1 M).
  have sylQ_M': q.-Sylow(M^`(1)) Q := pHall_subl sQM' (der_sub 1 M) sylQ.
  rewrite (nilpotent_Hall_pcore _ sylQ_M') ?pcore_char //.
  by rewrite (isog_nil (quotient1_isog _)) -Ma1 Malpha_quo_nil.
have a'q: q \notin \alpha(M).
  apply: contra nonuniqNQ => a_q.
  have uniqQ: Q \in 'U by rewrite rank3_Uniqueness ?(rank_Sylow sylQ).
  by rewrite (def_uniq_mmaxS _ _ (def_uniq_mmax _ _ sQM)) ?normG.
have b'q := contra (@beta_sub_alpha _ M _) a'q.
case: part_a_holds => // ntCaP regQP; split=> {ntCaP regQP}// r.
apply/idP/idP=> [a_r | ]; last exact: beta_sub_alpha.
apply: contraR nonuniqNQ => b'r; apply/eqP.
apply: def_uniq_mmaxS (uniqCMX Q _) => //.
have q'r: r != q by apply: contraNneq a'q => <-.
by have [|_ -> //] := beta'_cent_Sylow maxM b'r b'q qQ; rewrite q'r sQM'.
Qed.

(* This is B & G, Lemma 12.19. *)
(* We have used lemmas 10.8(b) and 10.2(c) rather than 10.9(a) as suggested   *)
(* in the text; this avoids a quantifier inversion!                           *)
Lemma der_compl_cent_beta' M E :
    M \in 'M -> \sigma(M)^'.-Hall(M) E -> 
  exists2 H : {group gT}, \beta(M)^'.-Hall(M`_\sigma) H & E^`(1) \subset 'C(H).
Proof.
move=> maxM hallE; have [sEM s'E _] := and3P hallE.
have s'E': \sigma(M)^'.-group E^`(1) := pgroupS (der_sub 1 E) s'E.
have b'E': \beta(M)^'.-group E^`(1).
  by apply: sub_pgroup s'E' => p; apply: contra; apply: beta_sub_sigma.
have solM': solvable M^`(1) := solvableS (der_sub 1 M) (mmax_sol maxM).
have [K hallK sE'K] := Hall_superset solM' (dergS 1 sEM) b'E'.
exists (K :&: M`_\sigma)%G.
  apply: Hall_setI_normal hallK.
  exact: normalS (Msigma_der1 maxM) (der_sub 1 M) (pcore_normal _ M).
have nilK: nilpotent K.
  by have [sKM' b'K _] := and3P hallK; apply: beta'_der1_nil sKM'.
rewrite (sub_nilpotent_cent2 nilK) ?subsetIl ?(coprimeSg (subsetIr _ _)) //.
exact: pnat_coprime (pcore_pgroup _ _) s'E'.
Qed.

End Section12.

Implicit Arguments tau2'1 [[gT] [M] x].
Implicit Arguments tau3'1 [[gT] [M] x].
Implicit Arguments tau3'2 [[gT] [M] x].


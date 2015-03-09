(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset center.
Require Import fingroup morphism perm automorphism quotient action finalg zmodp.
Require Import gfunctor gproduct cyclic commutator gseries nilpotent pgroup.
Require Import sylow hall abelian maximal frobenius.
Require Import matrix mxalgebra mxrepresentation mxabelem vector.
Require Import BGsection1 BGsection3 BGsection7 BGsection15 BGsection16.
Require Import ssrnum ssrint algC classfun character inertia vcharacter.
Require Import PFsection1 PFsection2 PFsection3 PFsection4 PFsection5.
Require Import PFsection6 PFsection7 PFsection8 PFsection9 PFsection10.

(******************************************************************************)
(* This file covers Peterfalvi, Section 11: Maximal subgroups of Types        *)
(* III and IV.                                                                *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory FinRing.Theory Num.Theory.

Section Eleven.

(* This is Peterfalvi (11.1). *)
Lemma lbound_expn_odd_prime p q : 
   odd p -> odd q -> prime p -> prime q -> p != q -> 4 * q ^ 2 + 1 < p ^ q.
Proof.
move=> odd_p odd_q pr_p pr_q p_neq_q.
have{pr_p pr_q} [pgt2 qgt2] : 2 < p /\ 2 < q by rewrite !odd_prime_gt2.
have [qlt5 | qge5 {odd_q qgt2 p_neq_q}] := ltnP q 5.
  have /eqP q3: q == 3 by rewrite eqn_leq qgt2 andbT -ltnS -(odd_ltn 5).
  apply: leq_trans (_ : 5 ^ q <= p ^ q); first by rewrite q3.
  by rewrite leq_exp2r // odd_geq // ltn_neqAle pgt2 eq_sym -q3 p_neq_q.
apply: leq_trans (_ : 3 ^ q <= p ^ q); last by rewrite -(subnKC qge5) leq_exp2r.
elim: q qge5 => // q IHq; rewrite ltnS leq_eqVlt => /predU1P[<- // | qge5].
rewrite (expnS 3); apply: leq_trans {IHq}(leq_mul (leqnn 3) (IHq qge5)).
rewrite -!addnS mulnDr leq_add // mulnCA leq_mul // !(mul1n, mulSnr).
by rewrite -addn1 sqrnD muln1 -(subnKC qge5) !leq_add ?leq_mul.
Qed.

Local Open Scope ring_scope.

Variable gT : minSimpleOddGroupType.
Local Notation G := (TheMinSimpleOddGroup gT).
Implicit Types H K L N P Q R S T U V W : {group gT}.

Variables M U W W1 W2 : {group gT}.
Hypotheses (maxM : M \in 'M) (defW : W1 \x W2 = W) (MtypeP : of_typeP M U defW).
Hypothesis notMtype2 : FTtype M != 2.

Let notMtype5 : FTtype M != 5. Proof. exact: FTtype5_exclusion. Qed.
Let notMtype1 : FTtype M != 1%N. Proof. exact: FTtypeP_neq1 MtypeP. Qed.
Let Mtype34 : FTtype M \in pred2 3 4.
Proof.
by have:= FTtype_range M; rewrite -mem_iota !inE !orbA orbC 3?[_ == _](negPf _).
Qed.
Let Mtype_gt2 : (FTtype M > 2)%N. Proof. by case/pred2P: Mtype34 => ->. Qed.

Local Notation H0 := (Ptype_Fcore_kernel MtypeP).
Local Notation "` 'H0'" := (gval H0) (at level 0, only parsing) : group_scope.
Local Notation "` 'M'" := (gval M) (at level 0, only parsing) : group_scope.
Local Notation "` 'U'" := (gval U) (at level 0, only parsing) : group_scope.
Local Notation "` 'W'" := (gval W) (at level 0, only parsing) : group_scope.
Local Notation "` 'W1'" := (gval W1) (at level 0, only parsing) : group_scope.
Local Notation "` 'W2'" := (gval W2) (at level 0, only parsing) : group_scope.
Local Notation H := `M`_\F%G.
Local Notation "` 'H'" := `M`_\F (at level 0) : group_scope.
Local Notation HU := M^`(1)%G.
Local Notation "` 'HU'" := `M^`(1)%g (at level 0) : group_scope.
Local Notation U' := U^`(1)%G.
Local Notation "` 'U''" := `U^`(1)%g (at level 0) : group_scope.
Local Notation C := 'C_U(`H)%G.
Local Notation "` 'C'" := 'C_`U(`H) (at level 0) : group_scope.
Local Notation HC := (`H <*> `C)%G.
Local Notation "` 'HC'" := (`H <*> `C) (at level 0) : group_scope.
Local Notation H0C := (`H0 <*> `C)%G.
Local Notation "` 'H0C'" := (`H0 <*> `C) (at level 0) : group_scope.
Local Notation Hbar := (`H / `H0)%g.

Local Notation S_ := (seqIndD HU M HU).
Local Notation tau := (FT_Dade0 maxM).
Local Notation R := (FTtypeP_coh_base maxM MtypeP).
Local Notation V := (cyclicTIset defW).

Let Mtype24 := compl_of_typeII_IV maxM MtypeP notMtype5.

Let defMs : M`_\s = HU. Proof. exact: FTcore_type_gt2. Qed.
Let defA1 : 'A1(M) = HU^#. Proof. by rewrite /= -defMs. Qed.
Let defA : 'A(M) = HU^#. Proof. by rewrite FTsupp_eq1. Qed.
Let sHU_A0 : HU^# \subset 'A0(M). Proof. by rewrite -defA FTsupp_sub0. Qed.

Let calS := seqIndD HU M M`_\s 1.
Let scohM : subcoherent calS tau R. Proof. exact: FTtypeP_subcoherent. Qed.
Let scoh1 : subcoherent (S_ 1) tau R.
Proof. by rewrite -{2}(group_inj defMs). Qed.

Let p := #|W2|.
Let pr_p : prime p. Proof. by have [] := FTtypeP_primes maxM MtypeP. Qed.
Let ntW2 : W2 :!=: 1%g. Proof. by rewrite -cardG_gt1 prime_gt1. Qed.
Let cycW2 : cyclic W2. Proof. exact: prime_cyclic. Qed.
Let def_p : pdiv #|Hbar| = p. Proof. exact: typeIII_IV_core_prime. Qed.

Let q := #|W1|.
Let pr_q : prime q. Proof. by have [] := FTtypeP_primes maxM MtypeP. Qed.
Let ntW1 : W1 :!=: 1%g. Proof. by rewrite -cardG_gt1 prime_gt1. Qed.
Let cycW1 : cyclic W1. Proof. exact: prime_cyclic. Qed.

Let defM : HU ><| W1 = M. Proof. by have [[]] := MtypeP. Qed.
Let defHU : H ><| U = HU. Proof. by have [_ []] := MtypeP. Qed.

Let nsHUM : HU <| M. Proof. exact: gFnormal. Qed.
Let sHUM : HU \subset M. Proof. exact: gFsub. Qed.
Let sHHU : H \subset HU. Proof. by have /mulG_sub[] := sdprodW defHU. Qed.
Let sUHU : U \subset HU. Proof. by have /mulG_sub[] := sdprodW defHU. Qed.
Let sUM : U \subset M. Proof. exact: subset_trans sUHU sHUM. Qed.

Let coHUq : coprime #|HU| q.
Proof. by rewrite (coprime_sdprod_Hall_r defM); have [[]] := MtypeP. Qed.
Let coUq : coprime #|U| q. Proof. exact: coprimeSg coHUq. Qed.
	
Let neq_pq : p != q.
Proof.
apply: contraTneq coHUq => <-; rewrite coprime_sym prime_coprime ?cardSg //.
by rewrite -(typeP_cent_compl MtypeP) subsetIl.
Qed.

Let solHU : solvable HU. Proof. exact: solvableS sHUM (mmax_sol maxM). Qed.
Let solH : solvable H. Proof. exact: solvableS sHHU solHU. Qed.

Let ltM''HU :  M^`(2)%g \proper HU.
Proof. by rewrite (sol_der1_proper solHU) // -defMs FTcore_neq1. Qed.

Let frobMtilde : [Frobenius M / M^`(2) = (HU / M^`(2)) ><| (W1 / M^`(2))].
Proof.
have [[_ _ _ _] _ _ [_ _ _ sW2M'' prHUW1 ] _] := MtypeP.
by rewrite Frobenius_coprime_quotient ?gFnormal //; split=> // _ /prHUW1->.
Qed.

Let defHC : H \x C = HC.
Proof. 
by have [defHC _ _ _] := typeP_context MtypeP; rewrite /= (dprodWY defHC).
Qed.

Let nC_UW1 : U <*> W1 \subset 'N(C).
Proof.
have /sdprodP[_ _ nHUW1 _] := Ptype_Fcore_sdprod MtypeP.
by rewrite normsI ?norms_cent // join_subG normG; have [_ []] := MtypeP.
Qed.

Let nsCM : C <| M.
Proof.
rewrite /normal subIset ?sUM //= -{1}(sdprodW (Ptype_Fcore_sdprod MtypeP)).
by rewrite mulG_subG cents_norm // centsC subsetIr.
Qed.

Let nsCU : C <| U. Proof. exact: normalS (subsetIl _ _) sUM nsCM. Qed.
Let nsHC_M : HC <| M. Proof. by rewrite normalY ?gFnormal. Qed.
Let sHC_HU : HC \subset HU. Proof. by rewrite join_subG sHHU subIset ?sUHU. Qed.
Let nsHC_HU : HC <| HU. Proof. exact: normalS nsHC_M. Qed.

Let chiefH0 : chief_factor M H0 H.
Proof. by have [] := Ptype_Fcore_kernel_exists maxM MtypeP notMtype5. Qed.

Let minHbar : minnormal Hbar (M / H0).
Proof. exact: chief_factor_minnormal. Qed.

Let abelHbar : p.-abelem Hbar.
Proof.
have solHbar : solvable (H / H0) by rewrite quotient_sol.
have [_ _] := minnormal_solvable minHbar (subxx _) solHbar.
by rewrite /is_abelem def_Ptype_factor_prime.
Qed.

Let sH0H : H0 \subset H.
Proof. by have/andP[/maxgroupp/andP[/proper_sub]]:= chiefH0. Qed.

Let nH0M: M \subset 'N(H0).
Proof. by have /andP[/maxgroupp/andP[]] := chiefH0. Qed.

Let nsH0H : H0 <| H.
Proof. by rewrite /normal sH0H (subset_trans (Fcore_sub _)). Qed.

Let nsH0C_M : H0C <| M.
Proof. by rewrite !normalY ?gFnormal /normal ?(subset_trans sH0H) ?gFsub. Qed.

Let defH0C : H0 \x C = H0C.
Proof.
have /dprodP[_ _ cHC tiHC] := defHC.
by rewrite dprodEY ?(centsS sH0H) //; apply/trivgP; rewrite -tiHC setSI.
Qed.

(* Group-theoretic consequences of the coherence and non-coherence theorems   *)
(* of Sections 5, 9 and 10 for maximal subgroups of type III and IV.          *)

(* This is Peterfalvi (11.3). *)
Lemma FTtype34_noncoherence : ~ coherent (S_ H0C) M^# tau.
Proof.
move=> cohH0C; suff: coherent (S_ 1) M^# tau by apply: FTtype345_noncoherence.
have /mulG_sub[_ sW1M] := sdprodW defM.
have [nsHHU _ _ nHU tiHU] := sdprod_context defHU.
have sHM: H \subset M := gFsub _ _.
have [sCM sH0C_M]: C \subset M /\ H0C \subset M by rewrite !normal_sub.
have nH0_C := subset_trans sCM nH0M.
have sH0C_HC: H0C \subset HC by apply: genS (setSU _ _).
have defF: HC :=: 'F(M) by have [/dprodWY] := typeP_context MtypeP.
have{defF} nilHC: nilpotent (HC / 1) by rewrite defF quotient_nil ?Fitting_nil.
have /bounded_seqIndD_coherent-bounded_coh1 := scoh1.
apply: bounded_coh1 nilHC cohH0C _; rewrite ?sub1G ?normal1 //.
have[_ _ /= oHbar] := Ptype_Fcore_factor_facts maxM MtypeP notMtype5.
rewrite -(index_sdprod defM) -divgS // -(dprod_card defHC) -(dprod_card defH0C).
rewrite divnMr ?cardG_gt0 // divg_normal // oHbar def_p -/q.
by rewrite lbound_expn_odd_prime ?mFT_odd.
Qed.

(* This is Peterfalvi (11.4). *)
Lemma bounded_proper_coherent H1 :
  H1 <| M -> H1 \proper HU -> coherent (S_ H1) M^# tau ->
    (#|HU : H1| <= 2 * q * #|U : C| + 1)%N.
Proof.
move=> nsH1_M psH1_M' cohH1; have [nsHHU _ _ _ _] := sdprod_context defHU.
rewrite -leC_nat natrD -ler_subl_addr.
have ->: (2 * q * #|U : C|)%:R = 2%:R * #|M : HC|%:R * sqrtC #|HC : HC|%:R.
  rewrite indexgg sqrtC1 mulr1 -mulnA natrM; congr (_ * _%:R).
  apply/eqP; rewrite // -(eqn_pmul2l (cardG_gt0 HC)) Lagrange ?normal_sub //.
  rewrite mulnCA -(dprod_card defHC) -mulnA (Lagrange (subsetIl _ _)).
  by rewrite -(sdprod_card defM) -(sdprod_card defHU) mulnC.
have ns_M: [/\ H1 <| M, H0C <| M, HC <| M & HC <| M] by [].
case: (coherent_seqIndD_bound _ _ scoh1 ns_M) FTtype34_noncoherence => //.
suffices /center_idP->: abelian (HC / H0C) by rewrite genS ?setSU. 
suffices /isog_abelian->: HC / H0C \isog H / H0 by apply: abelem_abelian p _ _.
by rewrite /= (joingC H0) isog_sym quotient_sdprodr_isog ?(dprodWsdC defHC).
Qed.

(* This is Peterfalvi (11.5). *)
Lemma FTtype34_der2 : M^`(2)%g = HC.
Proof.
have [defFM [_ not_cHU] _ _] := typeP_context MtypeP.
have [_ sW1M _ _ tiHU_W1] := sdprod_context defM.
have{defFM} sM''_HC: M^`(2)%g \subset HC.
  by rewrite -defHC defFM; have [_ _ []] := MtypeP.
have scohM'': subcoherent (S_ M^`(2)) tau R.
  exact/(subset_subcoherent scoh1)/seqInd_conjC_subset1.
have cohM'': coherent (S_ M^`(2)) M^# tau.
  apply: uniform_degree_coherence scohM'' _.
  apply: all_pred1_constant #|M : HU|%:R _ _; rewrite all_map.
  apply/allP=> _ /seqIndP[s /setDP[kerM'' _] ->] /=; rewrite inE in kerM''.
  by rewrite cfInd1 ?gFsub // lin_char1 ?mulr1 ?lin_irr_der1.
have ubHC: (#|HC : M^`(2)| < 2 * q + 1)%N.
  rewrite -(ltn_pmul2r (indexg_gt0 U C)) mulnDl mul1n.
  apply: leq_ltn_trans (_ : 2 * q * #|U : C| + 1 < _)%N; last first.
    by rewrite ltn_add2l indexg_gt1 subsetIidl not_cHU //; have [] := Mtype24.
  have {1}->: #|U : C| = #|HU : HC| by apply: index_sdprodr (subsetIl _ _).
  by rewrite mulnC (Lagrange_index sHC_HU) // bounded_proper_coherent ?gFnormal.
have regHC_W1: semiregular (HC / M^`(2)) (W1 / M^`(2)).
  by apply: semiregularS (Frobenius_reg_ker frobMtilde); rewrite quotientS.
suffices /dvdnP[k Dk]: 2 * q %| #|HC : M^`(2)|.-1.
  apply: contraTeq ubHC; rewrite -leqNgt eqEsubset sM''_HC -indexg_gt1 addn1.
  by rewrite -[#|_:_|]prednK // {}Dk !ltnS muln_gt0 => /andP[/leq_pmull->].
rewrite Gauss_dvd; last by rewrite coprime2n mFT_odd.
rewrite dvdn2 -subn1 odd_sub // addbT negbK subn1.
rewrite -card_quotient; last by rewrite (subset_trans sHC_HU) // (der_norm 1).
have Dq: q = #|W1 / M^`(2)|%g.
  apply/card_isog/quotient_isog; first by rewrite (subset_trans sW1M) ?gFnorm.
  by apply/trivgP; rewrite -tiHU_W1 setSI // (der_sub 1).
rewrite quotient_odd ?mFT_odd //= Dq regular_norm_dvd_pred ?quotient_norms //.
by rewrite (subset_trans sW1M) ?normal_norm.
Qed.
Local Notation defM'' := FTtype34_der2.

(* This is Peterfalvi (11.6). *)
Lemma FTtype34_facts (H' := H^`(1)%g):
  [/\ p.-group H, U \subset 'C(H0), H0 :=: H' & C :=: U']. 
Proof.
have nilH: nilpotent H := Fcore_nil M.
have /sdprod_context[/andP[_ nHM] sUW1M _ _ _] := Ptype_Fcore_sdprod MtypeP.
have coH_UW1: coprime #|H| #|U <*> W1| := Ptype_Fcore_coprime MtypeP.
have [[_ mulHU _ tiHU] [nHU isomHU]] := (sdprodP defHU, sdprod_isom defHU).
have{sUW1M} cH0U: U \subset 'C(H0).
  have frobUW1 := Ptype_compl_Frobenius maxM MtypeP notMtype5.
  have nH0_UW1 := subset_trans sUW1M nH0M; have [_ nH0W1] := joing_subP nH0_UW1.
  have [coH0_UW1 solH0] := (coprimeSg sH0H coH_UW1, solvableS sH0H solH).
  have [_ -> //] := Frobenius_Wielandt_fixpoint frobUW1 nH0_UW1 coH0_UW1 solH0.
  have ->: 'C_H0(W1) = H0 :&: 'C_H(W1) by rewrite setIA (setIidPl sH0H).
  have nH0C: 'C_H(W1) \subset 'N(H0) by rewrite subIset // normal_norm.
  rewrite cardMg_TI // -LagrangeMl -card_quotient {nH0C}//.
  rewrite coprime_quotient_cent ?(coprimeSg sHHU) //=.
  have [_ -> _] := Ptype_Fcore_factor_facts maxM MtypeP notMtype5.
  by rewrite (typeP_cent_core_compl MtypeP) def_p.
have{isomHU} defC: C :=: U'.
  have [injHquo defHUb] := isomP isomHU.
  apply: (injm_morphim_inj injHquo); rewrite ?subsetIl ?morphim_der ?der_sub //.
  rewrite defHUb morphim_restrm -quotientE setIA setIid -quotientMidl /=.
  by rewrite (dprodW defHC) -defM'' -quotient_der // -mulHU mul_subG ?normG.
have{coH_UW1} defH0: H0 :=: H'.
  pose Hhat := (H / H')%g; pose Uhat := (U / H')%g; pose HUhat := (HU / H')%g.
  have nH'H: H \subset 'N(H') := gFnorm _ _.
  have nH'U: U \subset 'N(H') := char_norm_trans (der_char _ _) nHU.
  apply/eqP; rewrite eqEsubset andbC.
  rewrite der1_min ?(abelem_abelian abelHbar) ?normal_norm //=.
  rewrite -quotient_sub1 /= -/H'; last exact: subset_trans sH0H nH'H.
  suffices <-: 'C_Hhat(Uhat) = 1%g.
    by rewrite subsetI quotientS //= quotient_cents // centsC.
  suffices: ~~ ('C_Hhat(Uhat)^`(1)%g \proper 'C_Hhat(Uhat)).
    exact: contraNeq (sol_der1_proper (quotient_sol _ solH) (subsetIl Hhat _)).
  have {2}<-: HUhat^`(1)%g :&: 'C_Hhat(Uhat) = 'C_Hhat(Uhat).
    rewrite -quotient_der ?[HU^`(1)%g]defM''; last by rewrite -mulHU mul_subG.
    by rewrite (setIidPr _) ?subIset // quotientS ?joing_subl.
  suffices defHUhat: 'C_Hhat(Uhat) \x ([~: Hhat, Uhat] <*> Uhat) = HUhat.
    rewrite -(dprod_modl (der_dprod 1 defHUhat)) ?der_sub //= -/Hhat.
    rewrite [rhs in _ \x rhs](trivgP _) ?dprodg1 ?properxx //= -/Hhat.
    by have [_ _ _ <-] := dprodP defHUhat; rewrite setIC setIS ?der_sub.
  have coHUhat: coprime #|Hhat| #|Uhat|.
    by rewrite coprime_morph ?(coprimegS _ coH_UW1) ?joing_subl.
  have defHhat: 'C_Hhat(Uhat) \x [~: Hhat, Uhat] = Hhat. 
    by rewrite dprodC coprime_abelian_cent_dprod ?der_abelian ?quotient_norms.
  rewrite /HUhat -(sdprodWY defHU) quotientY //= -(dprodWY defHhat).
  have [_ _ cCRhat tiCRhat] := dprodP defHhat.
  rewrite dprodEY ?joingA //; first by rewrite join_subG cCRhat centsC subsetIr.
  apply/trivgP; rewrite /= joingC norm_joinEl ?commg_normr //= -/Hhat -/Uhat.
  rewrite -tiCRhat !(setIAC _ 'C(_)) setSI // subsetI subsetIl /=.
  by rewrite -group_modr ?commg_subl ?quotient_norms //= coprime_TIg ?mul1g.
suffices{defC defH0}: p.-group H by [].
pose R := 'O_p^'(H); have hallR: p^'.-Hall(H) R := nilpotent_pcore_Hall _ nilH.
have defRHp: R \x 'O_p(H) = H by rewrite dprodC nilpotent_pcoreC.
suffices R_1: R :=: 1%g by rewrite -defRHp R_1 dprod1g pcore_pgroup.
have /subsetIP[sRH cUR]: R \subset 'C_H(U).
  have oH: #|H| = (p ^ q * #|'C_H(U)|)%N.
    by have:= typeII_IV_core maxM MtypeP notMtype5 => /=; rewrite ifN => // -[].
  apply/setIidPl/eqP; rewrite eqEcard subsetIl /= (card_Hall hallR) {}oH.
  rewrite (card_Hall (setI_normal_Hall _ hallR _)) ?subsetIl ?gFnormal //.
  rewrite partnM ?expn_gt0 ?cardG_gt0 //= part_p'nat ?mul1n ?pnatNK //.
  by rewrite pnat_exp ?pnat_id.
suffices: ~~ (R^`(1)%g \proper R) by apply: contraNeq (sol_der1_proper solH _). 
have /setIidPr {2}<-: R \subset HU^`(1)%g.
  by rewrite [HU^`(1)%g]defM'' -(dprodWY defHC) sub_gen ?subsetU ?sRH.
suffices defRHpU: R \x ('O_p(H) <*> U) = HU.
  rewrite -(dprod_modl (der_dprod 1 defRHpU)) ?der_sub //= -/R setIC.
  rewrite [rhs in _ \x rhs](trivgP _) ?dprodg1 ?properxx //= -/R.
  by have /dprodP[_ _ _ <-] := defRHpU; rewrite setIS ?der_sub.
rewrite -(sdprodWY defHU) -[in RHS](dprodWY defRHp) -joingA.
have [_ _ cRHp tiRHp] := dprodP defRHp.
rewrite dprodEY //= -/R; first by rewrite join_subG cRHp centsC.
rewrite joingC (norm_joinEl (char_norm_trans (pcore_char p H) nHU)).
by rewrite -(setIidPl sRH) -setIA -group_modr ?gFsub // tiHU mul1g.
Qed.

Let frobUW1bar : [Frobenius U <*> W1 / C = (U / C) ><| (W1 / C)].
Proof.
have frobUW1: [Frobenius U <*> W1 = U ><| W1].
  exact: Ptype_compl_Frobenius MtypeP notMtype5.
have [defUW1 ntU _ _ _] := Frobenius_context frobUW1.
have [[_ _ _ defC] regUW1] := (FTtype34_facts, Frobenius_reg_ker frobUW1).
rewrite Frobenius_coprime_quotient // /normal ?subIset ?joing_subl //.
by split=> [|x /regUW1->]; rewrite ?sub1G //= defC (sol_der1_proper solHU).
Qed.

(* This is Peterfalvi (11.7).                                                 *)
(* We have recast the linear algebra arguments in the original text in pure-  *)
(* group-theoretic terms: the overhead of the abelem_rV correspondence is not *)
(* justifiable here, as the Ssreflect linear algebra library lacks specific   *)
(* support for bilinear forms: we use D y z := [~ coset Q y, coset Q z] as    *)
(* our "linear form". D is antisymmetric as D z y = (D y z)^-1, so we only    *)
(* show that D is "linear" in z, that is, that D y is a group morphism with   *)
(* domain H whose kernel contains H0, when y \in H, and we do not bother to   *)
(* factor D to obtain a form over Hbar = H / H0.                              *)
(*   We further rework the argument to support this change in perspective:    *)
(*  - We remove any reference to linear algebra in the "Galois" (9.7b) case,  *)
(*    where U acts irreducibly on Hbar: we revert to the proof of the         *)
(*    original Odd Order paper, using the fact that H / Q is extraspecial.    *)
(*  - In the "non-Galois" (9.7a) case, we use the W1-conjugation class of a   *)
(*    generator of H1 as an explicit basis of Hbar, indexed by W1, and we     *)
(*    use the elements xbar_ w = coset H0 (x_ w) of this basis instead of     *)
(*    arbitrary y in H_i, as the same argument then justifies extending       *)
(*    commutativity to all of Hbar.                                           *)
(*  - We construct phi as the morphism mapping ubar in Ubar to the n such     *)
(*    that the action of ubar on H1 is exponentiation by n. We derive a       *)
(*    morphism phi_ w ubar for the action of Ubar on H1 ^ w, for w in W1, by  *)
(*    composign with the action QV of W1 on Ubar by inverse conjugation.      *)
(*  - We exchange the two alternatives in the (9.7a) case; most of proof is   *)
(*    thus by contradiction with the C_U(Hbar) != u assertion in (9.6),       *)
(*    first establishing case 9.7a (as 9.7b contradicts q odd), then that D   *)
(*    is nontrivial for some x_ w1 and x_ w2 (as (H / Q)' = H0 / Q != 1),     *)
(*    whence (phi_ w1 u)(phi_ w2 u) = 1, whence (phi u)^-1 = phi u and        *)
(*    phi = 1, i.e., Ubar centralises Wbar.                                   *)
(* Note finally that we simply construct U as a maximal subgroup of H0 normal *)
(* in H, as the nilpotence of H / Q implies that H0 / Q lies in its center.   *)
Lemma FTtype34_Fcore_kernel_trivial :
  [/\ p.-abelem H, #|H| = (p ^ q)%N & `H0 = 1%g].
Proof.
have [[_ _ nHU tiHU] [pH cH0U defH' _]] := (sdprodP defHU, FTtype34_facts).
have [/mulG_sub[_ sW1M] nH0H] := (sdprodW defM, normal_norm nsH0H).
have nHW1: W1 \subset 'N(H) := subset_trans sW1M (gFnorm _ M).
have nUW1: W1 \subset 'N(U) by have [_ []] := MtypeP.
pose bar := coset_morphism H0; pose Hbar := (H / H0)%g; pose Ubar := (U / H0)%g.
have [Cbar_neqU _ /= oHbar] := Ptype_Fcore_factor_facts maxM MtypeP notMtype5.
rewrite -/Hbar def_p // -/q in oHbar.
have [nH0U nH0W1] := (subset_trans sUM nH0M, subset_trans sW1M nH0M).
suffices H0_1 : `H0 = 1%g.
  have isoHbar: H \isog H / H0 by rewrite H0_1 quotient1_isog.
  by rewrite (isog_abelem isoHbar) (card_isog isoHbar).
apply: contraNeq Cbar_neqU => ntH0; rewrite [Ptype_Fcompl_kernel _]unlock.
suffices: Hbar \subset 'C(Ubar).
  by rewrite (sameP eqP setIidPl) sub_astabQ nH0U centsC.
have pH0 := pgroupS sH0H pH; have{ntH0} [_ _ [k oH0]] := pgroup_pdiv pH0 ntH0.
have{k oH0} [Q maxQ nsQH]: exists2 Q : {group gT}, maximal Q H0 & Q <| H.
  have [Q [sQH0 nsQH oQ]] := normal_pgroup pH nsH0H (leq_pred _).
  exists Q => //; apply: p_index_maximal => //.
  by rewrite -divgS // oQ oH0 pfactorK //= expnS mulnK ?expn_gt0 ?cardG_gt0.
have nsQH0: Q <| H0 := p_maximal_normal (pgroupS sH0H pH) maxQ.
have [[sQH0 nQH0] nQH] := (andP nsQH0, normal_norm nsQH).
have nQU: U \subset 'N(Q) by rewrite cents_norm ?(centsS sQH0).
pose hat := coset_morphism Q; pose Hhat := (H / Q)%g; pose H0hat := (H0 / Q)%g.
have{maxQ} oH0hat: #|H0hat| = p by rewrite card_quotient ?(p_maximal_index pH0).
have defHhat': Hhat^`(1)%g = H0hat by rewrite -quotient_der -?defH'.
have ntH0hat: H0hat != 1%g by rewrite -cardG_gt1 oH0hat prime_gt1.
have pHhat: p.-group Hhat by apply: quotient_pgroup.
have nsH0Hhat: H0hat <| Hhat by apply: quotient_normal.
have sH0hatZ: H0hat \subset 'Z(Hhat).
  by rewrite prime_meetG ?oH0hat // meet_center_nil ?(pgroup_nil pHhat).
have{pHhat} gal'M: ~~ typeP_Galois MtypeP.
  have sZHhat: 'Z(Hhat) \subset Hhat := center_sub _.
  have nsH0hatZ: H0hat <| 'Z(Hhat) := normalS sH0hatZ sZHhat nsH0Hhat.
  have [f injf im_f] := third_isom sQH0 nsQH nsH0H.
  have fHhat: f @* (Hhat / H0hat) = Hbar by rewrite im_f.
  apply: contra (odd (logn p #|Hhat|)) _ _; last first.
    rewrite -(divnK (cardSg (quotientS Q sH0H))) divg_normal // oH0hat.
    by rewrite -(card_injm injf) // fHhat oHbar -expnSr pfactorK //= mFT_odd.
  rewrite /typeP_Galois acts_irrQ // => /mingroupP[_ minUHbar].
  suffices /(card_extraspecial pHhat)[n _ ->]: extraspecial Hhat.
    by rewrite pfactorK //= odd_double.
  have abelH: p.-abelem (Hhat / H0hat)%g by rewrite -(injm_abelem injf) ?fHhat.
  suffices{abelH} defZHhat: 'Z(Hhat) = H0hat.
    do 2?split; rewrite defZHhat ?oH0hat //.
    apply/eqP; rewrite eqEsubset (Phi_min pHhat) ?normal_norm //=.
    by rewrite (Phi_joing pHhat) defHhat' joing_subl.
  apply: contraNeq ntH0hat; rewrite eqEsubset sH0hatZ andbT => not_esHhat.
  rewrite -defHhat'; apply/eqP/derG1P/center_idP/(quotient_inj nsH0hatZ)=> //.
  apply: (injm_morphim_inj injf); rewrite ?quotientS //= fHhat -/Hhat -/H0hat.
  rewrite minUHbar //= -/Hbar -?fHhat 1?morphim_injm_eq1 ?morphimS // -subG1.
  rewrite quotient_sub1 ?(normal_norm nsH0hatZ) // not_esHhat -['Z(_)]cosetpreK.
  rewrite im_f ?sub_cosetpre_quo // quotient_norms ?norm_quotient_pre //.
  by rewrite (char_norm_trans (center_char _)) ?quotient_norms.
have [H1 []] := typeP_Galois_Pn maxM notMtype5 gal'M.
rewrite def_p => oH1 nH1Ubar _ /bigdprodWY-defHbar _.
have /cyclicP[xbar defH1]: cyclic H1 by rewrite prime_cyclic ?oH1.
have H1xbar: xbar \in H1 by rewrite defH1 cycle_id.
have sH1_Hbar: H1 \subset Hbar.
  by rewrite -[Hbar]defHbar (bigD1 1%g) ?group1 ?conjsg1 ?joing_subl.
have{sH1_Hbar} Hxbar: xbar \in Hbar := subsetP sH1_Hbar xbar H1xbar.
have /morphimP[x nH0x Hx /= Dxbar] := Hxbar.
have{oH1} oxbar: #[xbar] = p by rewrite orderE -defH1.
have memH0: {in H &, forall y z, [~ y, z] \in H0}.
  by rewrite defH'; apply: mem_commg.
have [_ /centsP-cHH0hat] := subsetIP sH0hatZ; move/subsetP in nQH.
pose D y z := [~ hat z, hat y].
have D_H0_1 y z: y \in H -> z \in H0 -> D y z = 1%g.
  by move=> Hy H0z; apply/eqP/commgP/cHH0hat; apply: mem_quotient.
have H0_D: {in H &, forall y z, D y z \in H0hat}.
  by move=> y z Hy Hz; rewrite -defHhat' mem_commg ?mem_quotient.
have Dsym y z: (D y z)^-1%g = D z y by rewrite invg_comm.
have Dmul y: y \in H -> {in H &, {morph D y: z t / z * t}}%g.
  move=> Hy z t Hz Ht; rewrite {1}/D morphM ?nQH // commMgR; congr (_ * _)%g.
  by rewrite -{2}morphR ?nQH // -/(D t _) D_H0_1 ?memH0 // mulg1.
pose Dm y Hy : {morphism H >-> coset_of Q} := Morphism (Dmul y Hy).
have{D_H0_1} kerDmH0 y Hy: H0 \subset 'ker (Dm y Hy).
  by rewrite subsetI sH0H; apply/subsetP=> z H0z; rewrite !inE /= D_H0_1.
pose x_ w := (x ^ w)%g; pose xbar_ w := (xbar ^ bar w)%g.
move/subsetP in nHW1; move/subsetP in nHU.
have Hx_ w: w \in W1 -> (x_ w \in H) * {in U, forall u, x_ w ^ u \in H}%g.
  by move/nHW1=> nHw; split=> [|u /nHU-nHu]; rewrite !memJ_norm.
have Dx: {in H &, forall y z, {in W1, forall w, D (x_ w) y = 1} -> D y z = 1}%g.
  move=> y z Hy Hz Dxy1; apply/(kerP (Dm y Hy) Hz); apply: subsetP z Hz.
  rewrite -(quotientSGK nH0H) ?kerDmH0 // -defHbar gen_subG.
  apply/bigcupsP=> _ /morphimP[w nH0w W1w ->] /=.
  rewrite defH1 Dxbar -quotient_cycle -?quotientJ ?quotientS // -cycleJ.
  by rewrite cycle_subG !inE /= Hx_ //= -Dsym eq_invg1 Dxy1.
pose ntrivD := [exists w in [predX W1 & W1], #[D (x_ w.1) (x_ w.2)] == p].
have{ntrivD Dx} /exists_inP[[w1 w2] /andP/=[Ww1 Ww2] /eqP-oDx12]: ntrivD.
  apply: contraR ntH0hat => Dx_1; rewrite -defHhat' -subG1 gen_subG.
  apply/subsetP=> _ /imset2P[_ _ /morphimP[y ? Hy ->] /morphimP[z ? Hz ->] ->].
  apply/set1P/Dx=> // w2 Ww2; rewrite Dx ?Hx_ // => w1 Ww1.
  have abelH0hat: p.-abelem H0hat by apply: prime_abelem.
  apply: contraNeq Dx_1 => /(abelem_order_p abelH0hat)oDx12.
  by apply/exists_inP; exists (w1, w2); rewrite ?inE ?Ww1 // oDx12 ?H0_D ?Hx_.
have /subsetP-nUW1bar: (W1 / H0)%g \subset 'N(Ubar) := quotient_norms H0 nUW1.
move/subsetP in nH0H; move/subsetP in nH0W1.
pose n (phi : {morphism Ubar >-> {unit 'F_p}}) ubar : nat := val (phi ubar).
have [phi Dphi]: {phi | {in Ubar, forall ub, xbar ^ ub =xbar ^+ n phi ub}}%g.
  pose xbar_Autm := invm (injm_Zp_unitm xbar).
  have /restrmP[phi [Dphi _ _ _]]: Ubar \subset 'dom (xbar_Autm \o conj_aut H1).
    by rewrite -sub_morphim_pre //= im_Zp_unitm -defH1 Aut_conj_aut.
  rewrite /n pdiv_id // -oxbar; exists phi => ubar /(subsetP nH1Ubar)Uubar.
  transitivity (Zp_unitm (phi ubar) xbar); last by rewrite autE /= -?defH1.
  by rewrite Dphi invmK ?im_Zp_unitm -?defH1 ?Aut_aut ?norm_conj_autE.
pose QV ubar w := (ubar ^ (bar w)^-1)%g.
have UbarQV: {in Ubar & W1, forall ubar w, QV ubar w \in Ubar}.
  by move=> ub w Uub W1w; rewrite /= memJ_norm ?groupV ?nUW1bar ?mem_quotient.
pose phi_ w ub := phi (QV ub w); pose nphi_ w ub := n phi (QV ub w).
have xbarJ: {in W1 & Ubar, forall w ub, xbar_ w ^ ub = xbar_ w ^+ nphi_ w ub}%g.
  by move=> w ubar * /=; rewrite -conjgM conjgCV conjgM Dphi ?UbarQV // conjXg.
have{oDx12} phi_w12 ubar: ubar \in Ubar -> (phi_ w1 ubar * phi_ w2 ubar = 1)%g.
  pose n_u := nphi_ ^~ ubar => Uubar; have [u nH0u Uu Dubar] := morphimP Uubar.
  suffices: n_u w1 * n_u w2 == 1 %[mod #[D (x_ w1) (x_ w2)]].
    by apply: contraTeq; rewrite oDx12 -!val_Fp_nat // natrM !natr_Zp.
  have DXn: {in H & W1, forall y w, D y (x_ w) ^+ n_u w = D y (x_ w ^ u)}%g.
    move=> y w Hy W1w; set z := x_ w; have [Hz /(_ u Uu) Hzu] := Hx_ w W1w.
    rewrite -(morphX (Dm y Hy)) //; apply/rcoset_kerP; rewrite ?groupX //.
    have /subsetP: H0 :* z ^ u \subset 'ker (Dm y Hy) :* z ^ u by rewrite mulSg.
    apply; apply/rcoset_kercosetP; rewrite ?groupX ?nH0H //.
    by rewrite morphX ?morphJ ?(nH0W1 w) // ?nH0H //= -Dubar -Dxbar xbarJ.
  rewrite -eq_expg_mod_order -{1}Dsym expgM expgVn ?(DXn, Dsym) ?Hx_ //.
  rewrite /D -!morphR ?nQH ?Hx_ // -conjRg (conjg_fixP _) //. 
  by apply/commgP/esym/(centsP cH0U); rewrite ?memH0 ?Hx_.
pose wbar := bar (w1 * w2 ^-1)%g; pose W1bar := (W1 / H0)%g.
have W1wbar: wbar \in W1bar by rewrite mem_quotient ?groupM ?groupV.
have{phi_w12} phiJ: {in Ubar, forall ubar, phi (ubar ^ wbar) = (phi ubar)^-1}%g.
  move=> ubar Uubar; apply/esym/eqP; rewrite eq_invg_mul.
  rewrite [wbar]morphM ?morphV ?nH0W1 ?groupV // -{1}[ubar](conjgK (bar w1)).
  by rewrite conjgM phi_w12 // memJ_norm ?nUW1bar ?mem_quotient.
have coW1bar2: coprime #|W1bar| 2 by rewrite coprimen2 quotient_odd ?mFT_odd.
have coUbar2: coprime #|Ubar| 2 by rewrite coprimen2 quotient_odd ?mFT_odd.
have{wbar phiJ W1wbar} phiV: {in Ubar, forall ubar, phi ubar = (phi ubar)^-1}%g.
  move=> ubar Uubar; rewrite /= -phiJ // -(expgK coW1bar2 W1wbar) -expgM mul2n.
  elim: (expg_invn _ _) => [|k IHk]; first by rewrite conjg1.
  by do 2!rewrite expgSr conjgM phiJ ?memJ_norm ?nUW1bar ?groupX // ?invgK.
rewrite -[Hbar]defHbar gen_subG defH1; apply/bigcupsP=> _ /morphimP[w _ Ww ->].
rewrite -cycleJ cycle_subG -/(xbar_ _); apply/centP=> ubar Uubar; apply/commgP.
apply/conjg_fixP; rewrite xbarJ // /nphi_ -[QV _ w](expgK coUbar2) ?UbarQV //.
by rewrite /n !morphX ?groupX 1?expgS 1?{1}phiV ?UbarQV // mulVg expg1n.
Qed.

Let defU' : C :=: U'. Proof. by have [] := FTtype34_facts. Qed.
Let H0_1 : H0 :=: 1%g. Proof. by have [] := FTtype34_Fcore_kernel_trivial. Qed.

Lemma Ptype_Fcompl_kernel_cent : Ptype_Fcompl_kernel MtypeP :=: C.
Proof.
rewrite [Ptype_Fcompl_kernel MtypeP]unlock /= (group_inj H0_1).
by rewrite astabQ -morphpreIim -injm_cent ?injmK ?ker_coset ?norms1.
Qed.
Local Notation defC := Ptype_Fcompl_kernel_cent.

(* Character theory proper. *)

Let pddM := FT_prDade_hyp maxM MtypeP.
Let ptiWM : primeTI_hypothesis M HU defW := FT_primeTI_hyp MtypeP.
Let ctiWG : cyclicTI_hypothesis G defW := pddM.
Let ctiWM : cyclicTI_hypothesis M defW := prime_cycTIhyp ptiWM.

Local Notation sigma := (cyclicTIiso ctiWG).
Local Notation w_ i j := (cyclicTIirr defW i j).
Local Notation eta_ i j := (sigma (w_ i j)).
Local Notation mu_ := (primeTIred ptiWM).
Local Notation Idelta := (primeTI_Isign ptiWM).
Local Notation delta_ j := (primeTIsign ptiWM j).
Local Notation d := (FTtype345_TIirr_degree MtypeP).
Local Notation n := (FTtype345_ratio MtypeP).
Local Notation delta := (FTtype345_TIsign MtypeP).

Implicit Types zeta xi lambda : 'CF(M).

Let u := #|U / C|%g.
Let mu2_ i j := primeTIirr ptiWM i j.
Let etaW := map sigma (irr W).
Let eq_proj_eta (alpha gamma : 'CF(G)) := orthogonal (alpha - gamma) etaW.
Let eta_col j := \sum_i eta_ i j.
Let bridge0 zeta := mu_ 0 - zeta.

Let proj_col_eta j0 i j : '[eta_col j0, eta_ i j] = (j == j0)%:R.
Proof.
rewrite cfdot_suml (bigD1 i) //= cfdot_cycTIiso eqxx eq_sym.
by rewrite big1 ?addr0 // => k /negPf-i'k; rewrite cfdot_cycTIiso i'k.
Qed.

Let nirrW1 : #|Iirr W1| = q. Proof. by rewrite card_Iirr_cyclic. Qed.
Let NirrW1 : Nirr W1 = q. Proof. by rewrite -nirrW1 card_ord. Qed.

Let nirrW2 : #|Iirr W2| = p. Proof. by rewrite card_Iirr_cyclic. Qed.
Let NirrW2 : Nirr W2 = p. Proof. by rewrite -nirrW2 card_ord. Qed.

Let calT := seqIndT HU M.
Let S1 := S_ HC.
Let S2 := seqIndD HU M HC C.

Let sS10 : cfConjC_subset S1 calS.
Proof. by apply: seqInd_conjC_subset1; rewrite /= ?defMs. Qed.

Let sS20 : cfConjC_subset S2 calS.
Proof. by apply: seqInd_conjC_subset1; rewrite /= ?defMs. Qed.

Let scohS1 : subcoherent S1 tau R. Proof. exact: subset_subcoherent sS10. Qed.
Let scohS2 : subcoherent S2 tau R. Proof. exact: subset_subcoherent sS20. Qed.

Let S1_1 : {in S1, forall zeta, zeta 1%g = q%:R}.
Proof.
move=> _ /seqIndP[s /setDP[kerM'' _] ->]; rewrite !inE -defM'' in kerM''.
by rewrite cfInd1 ?gFsub // -(index_sdprod defM) lin_char1 ?mulr1 ?lin_irr_der1.
Qed.

Let cohS1 : coherent S1 M^# tau.
Proof.
apply: uniform_degree_coherence scohS1 _.
by apply/(@all_pred1_constant _ q%:R)/allP=> _ /=/mapP[zeta /S1_1<- ->].
Qed.

Let irrS1 : {subset S1 <= irr M}.
Proof.
move=> _ /seqIndP[s /setDP[kerHC kerHU] ->]; rewrite !inE in kerHC kerHU.
rewrite -(quo_IirrK _ kerHC) // mod_IirrE // cfIndMod // cfMod_irr //.
have /irr_induced_Frobenius_ker := FrobeniusWker frobMtilde; rewrite defM''.
by apply; rewrite quo_Iirr_eq0 // -subGcfker.
Qed.

Let o1S1 : orthonormal S1.
Proof. exact: sub_orthonormal (seqInd_uniq _ _) (irr_orthonormal _). Qed.

Let cfdotS1 : {in S1 &, forall zeta xi, '[zeta, xi] = (zeta == xi)%:R}.
Proof. by case/orthonormalP: o1S1. Qed.

Let omu2S1 i j : {in S1, forall zeta, '[mu2_ i j, zeta] = 0}.
Proof.
move=> zeta S1zeta; have [s _ Dzeta] := seqIndP S1zeta.
rewrite Dzeta -cfdot_Res_l cfRes_prTIirr cfdot_irr mulrb ifN_eq //.
apply: contraNneq (prTIred_not_irr ptiWM j) => Ds.
by rewrite -cfInd_prTIres Ds -Dzeta irrS1.
Qed.

Let Tmu j : mu_ j \in calT. Proof. by rewrite -cfInd_prTIres mem_seqIndT. Qed.

Let omuS1 j : {in S1, forall zeta,  '[mu_ j, zeta] = 0}.
Proof.
by move=> zeta S1zeta /=; rewrite cfdot_suml big1 // => i _; apply: omu2S1.
Qed.

Let Zbridge0 : {in S1, forall zeta, bridge0 zeta \in 'Z[irr M, HU^#]}.
Proof.
have mu0_1: mu_ 0 1%g = q%:R by rewrite prTIred_1 prTIirr0_1 mulr1.
move=> zeta S1zeta; rewrite /= zcharD1 !cfunE subr_eq0 mu0_1 S1_1 // eqxx. 
by rewrite rpredB ?(seqInd_vchar _ (Tmu 0)) ?(seqInd_vchar _ S1zeta).
Qed.

Let A0bridge0 : {in S1, forall zeta, bridge0 zeta \in 'CF(M, 'A0(M))}.
Proof. by move=> zeta /Zbridge0/zchar_on/cfun_onS->. Qed.

Let sS1S2' : {subset S1 <= [predC S2]}.
Proof.  
by move=> _ /seqIndP[s /setDP[kHCs _] ->]; rewrite !inE mem_seqInd // inE kHCs.
Qed.

Let defS2: S2 = seqIndD HU M H H0C.
Proof. by rewrite /S2 H0_1 -!joinGE join1G joinGC seqIndDY. Qed.

Let cohS2: coherent S2 M^# tau.
Proof.
apply: subset_coherent (Ptype_core_coherence maxM MtypeP notMtype5).
by rewrite defC defS2; apply: seqIndS; rewrite Iirr_kerDS ?genS ?setUS ?der_sub.
Qed.

Let Smu := [seq mu_ j | j in predC1 0].
Let Sred := filter [predC irr M] (seqIndD HU M H H0).

Let memSred : Sred =i Smu.
Proof.
have [szSred _ memSred _] := typeP_reducible_core_Ind maxM MtypeP notMtype5.
have uSred: uniq Sred by apply: filter_uniq (seqInd_uniq _ _).
suffices{uSred}: (size Smu <= size Sred)%N by case/leq_size_perm.
by rewrite szSred def_p size_map -cardE cardC1 nirrW2.
Qed.

Let mu_1 j : j != 0 -> mu_ j 1%g = (q * u)%:R.
Proof.
move=> nzj; have Smuj: mu_ j \in Sred by rewrite memSred image_f.
have [_ _ _ /(_ _ Smuj)[]] := typeP_reducible_core_Ind maxM MtypeP notMtype5.
by rewrite defC.
Qed.

Let memS2red : [predD S2 & irr M] =i Smu.
Proof.
move=> xi; rewrite defS2 -memSred mem_filter; apply: andb_id2l => /= red_xi.
apply/idP/idP=> [|Sxi]; first by apply: seqIndS; rewrite Iirr_kerDS ?joing_subl.
have [_ _ _ /(_ xi)] := typeP_reducible_core_Ind maxM MtypeP notMtype5.
by rewrite defC mem_filter /= red_xi; case.
Qed.

Let i1 : Iirr W1 := inord 1.
Let nz_i1 : i1 != 0. Proof. by rewrite Iirr1_neq0. Qed.
Let j1 : Iirr W2 := inord 1.
Let nz_j1 : j1 != 0. Proof. by rewrite Iirr1_neq0. Qed.

(* This is Peterfalvi (11.8). *)
(* We have rearranged the argument somewhat:                                  *)
(* - Step (11.8.4) was out of sequence as it involves changing the definition *)
(*   of tau2, which requires showing that (11.8.2-3) are preserved by this    *)
(*   change; since (11.8.4) does not use (11.8.2-3) we avoid this by proving  *)
(*   (11.8.4) first.                                                          *)
(* - The first part of step (11.8.3) is the last fact that needs to be proved *)
(*   for an arbitrary j != 0; (11.8.1, 5-6) can all use the same fixed j != 0 *)
(*   (we take j = 1), provided (11.8.3) is proved before (11.8.2), which it   *)
(*   doe not use.                                                             *)
(* - Steps (11.8.2) and (11.8.5) are really as combination, to provide an     *)
(*   expression for tau (alpha i j) for an arbitrary i. We merge their proofs *)
(*   so we can use a fixed i for the whole combined step and hide some        *)
(*   intermediate technical facts.                                            *)
(* - We also reorganise the contents of the superstep, proving most of        *)
(*   (11.8.5) between the first and last two parts of (11.8.2); this          *)
(*   simplifies the latter because a is then known to be even, so we can show *)
(*   directly that a is 0 or 2, and then that X = eta i j - eta i 0.          *)
Lemma FTtype34_not_ortho_cycTIiso zeta :
  zeta \in S1 -> ~~ eq_proj_eta (tau (bridge0 zeta)) (eta_col 0).
Proof.
move=> S1zeta; set psi := tau _; apply/negP=> proj_psi_eta.
have irr_zeta: zeta \in irr M := irrS1 S1zeta.
have Szeta: zeta \in S_ 1 by apply: seqInd_sub S1zeta.
have Zzeta_S1: {in S1, forall xi, zeta - xi \in 'Z[S1, M^#]}.
  by move=> * /=; rewrite zcharD1E rpredB ?mem_zchar //= !cfunE !S1_1 ?subrr.
have n1S1: {in S1, forall xi, '[xi] = 1} by move=> xi /irrS1/irrWnorm.
have Z_S1: {in S1, forall xi, xi \in 'Z[S1]} by apply: mem_zchar.
have [p_gt0 q_gt0 u_gt0]: [/\ p > 0, q > 0 & u > 0]%N by rewrite !cardG_gt0.
have q_gt2: (q > 2)%N by rewrite odd_prime_gt2 ?mFT_odd.
have mu2_1 i j: j != 0 -> mu2_ i j 1%g = d%:R.
  by have [/(_ i j)] := FTtype345_constants maxM MtypeP notMtype2.
(* This is (11.8.1). *)
have [Dd delta1 Dn]: [/\ d = u, delta = 1 & n = (size S1)%:R].
  have size_S1 : (size S1 * q = u - 1)%N.
    rewrite mulnC [q](index_sdprod defM).
      rewrite (size_irr_subseq_seqInd _ (subseq_refl _)) //.
    transitivity #|[set mod_Iirr t | t : Iirr (HU / HC) in predC1 0]|.
      apply/eq_card=> s; rewrite inE mem_seqInd // !inE subGcfker.
      apply/andP/imsetP=> [[nzs kHCs] | [t nzt ->]].
        by exists (quo_Iirr HC s); rewrite ?quo_IirrK // inE quo_Iirr_eq0.
      by rewrite mod_Iirr_eq0 // mod_IirrE // cfker_mod.
    rewrite card_imset; last exact: can_inj (mod_IirrK _).
    have isoUC: U / C \isog HU / HC by apply: quotient_sdprodr_isog.
    rewrite subn1 cardC1 card_Iirr_abelian -?(card_isog isoUC) //.
    by rewrite -(isog_abelian isoUC) defU' der_abelian.
  have Dd: d = u.
    apply/eqP; rewrite -(eqn_pmul2l q_gt0) -eqC_nat -(mu_1 nz_j1).
    by rewrite natrM prTIred_1 mu2_1.
  suffices delta1: delta = 1.
    by rewrite /n Dd delta1 -(@natrB _  _ 1) // -size_S1 natrM mulfK ?neq0CG.
  have: (delta == 1 %[mod q])%C.
    rewrite -(eqCmod_transl _ (prTIirr1_mod ptiWM 0 j1)) mu2_1 // -/q Dd.
    by rewrite /eqCmod -(@natrB _ u 1) // dvdC_nat -size_S1 dvdn_mull.
  rewrite -[1]subr0 [delta]signrE -/ptiWM eqCmodDl eqCmodN opprK.
  by rewrite eqCmod0_nat; case: (Idelta j1); first rewrite gtnNdvd.
have deltaZ gamma: delta *: gamma = gamma by rewrite delta1 scale1r.
have [tau1 coh_tau1] := cohS1; pose zeta1 := tau1 zeta.
(* This is (11.8.4). *)
without loss Dpsi: tau1 coh_tau1 @zeta1 / psi = eta_col 0 - zeta1.
  move=> IHtau1; have [[Itau1 Ztau1] Dtau1] := coh_tau1.
  have tau1_dirr: {in S1, forall xi, tau1 xi \in dirr G}.
    by move=> xi S1xi; rewrite /= dirrE Ztau1 ?Itau1 ?mem_zchar //= n1S1.
  pose chi : 'CF(G) := eta_col 0 - psi.
  have Dpsi: psi = eta_col 0 - chi by rewrite opprD opprK addNKr.
  have chi'zeta1: chi <> zeta1.
    by move=> Dchi; case: (IHtau1 tau1); rewrite -/zeta1 -?Dchi.
  have dirr_chi: chi \in dirr G.
    apply: dirr_norm1.
      rewrite rpredB ?rpred_sum // => [i _|]; first exact: cycTIiso_vchar.
      rewrite Dade_vchar // zchar_split A0bridge0 //.
      by rewrite rpredB ?char_vchar ?prTIred_char ?irrWchar.
    apply: (addrI q%:R); transitivity '[psi]; last first.
      rewrite Dade_isometry ?A0bridge0 // (cfnormBd (omuS1 _ _)) //. 
      by rewrite cfnorm_prTIred n1S1.
    rewrite Dpsi [RHS]cfnormDd; last first.
      rewrite opprB cfdotC cfdot_sumr big1 ?conjC0 // => i _.
      by rewrite (orthoPl proj_psi_eta) ?map_f ?mem_irr.
    rewrite cfnormN -nirrW1 -sumr_const cfdot_sumr.
    by congr (_ + _); apply: eq_bigr => i _; rewrite proj_col_eta.
  have Dchi: {in S1, forall xi, xi != zeta -> chi = - tau1 xi}.
    move=> xi S1xi /negPf-zeta'xi; have irr_xi := irrS1 S1xi.
    suffices: '[zeta1 - tau1 xi, chi] = 1.
      by case/cfdot_add_dirr_eq1; rewrite ?rpredN ?tau1_dirr.
    rewrite /= cfdotBr cfdot_sumr big1 => [|i _]; last first.
      have oS1eta := coherent_ortho_cycTIiso MtypeP sS10 coh_tau1.
      by rewrite cfdotBl !oS1eta ?irrS1 ?subrr.
    rewrite -raddfB Dtau1 ?Zzeta_S1 // Dade_isometry ?A0bridge0 //; last first.
      exact: cfun_onS sHU_A0 (zcharD1_seqInd_on _ (Zzeta_S1 xi S1xi)).
    rewrite cfdotBr cfdotC cfdotBr 2?omuS1 // subrr conjC0 !sub0r opprK.
    by rewrite cfdotBl n1S1 // cfdotS1 // zeta'xi subr0.
  have S1zetaC: zeta^*%CF \in S1 by rewrite cfAut_seqInd.
  have Dchi_zetaC: chi = - tau1 zeta^*%CF.
    by rewrite -Dchi ?(seqInd_conjC_neq _ _ _ S1zeta) ?mFT_odd.
  suffices S1le2: (size S1 <= size [:: zeta; zeta^*%CF])%N.
    case: (IHtau1 (dual_iso tau1)); last by rewrite /= -Dchi_zetaC.
    exact: dual_coherence scohS1 coh_tau1 S1le2.
  rewrite uniq_leq_size ?seqInd_uniq // => xi S1xi.
  rewrite !inE -implyNb; apply/implyP=> zeta'xi; apply/eqP.
  apply: (Zisometry_inj Itau1); rewrite ?mem_zchar ?cfAut_seqInd //.
  by apply: oppr_inj; rewrite -Dchi.
have [[Itau1 Ztau1] Dtau1] := coh_tau1.
have tau1_dirr: {in S1, forall xi, tau1 xi \in dirr G}.
  by move=> xi S1xi; rewrite /= dirrE Ztau1 ?Itau1 ?mem_zchar //= n1S1.
have oS1eta i j: {in S1, forall xi, '[tau1 xi, eta_ i j] = 0}.
  by move=> xi S1xi /=; rewrite (coherent_ortho_cycTIiso _ _ coh_tau1) ?irrS1.
pose alpha_ := FTtype345_bridge MtypeP zeta.
have A0alpha i j : j != 0 -> alpha_ i j \in 'CF(M, 'A0(M)).
  by move/supp_FTtype345_bridge->; rewrite ?S1_1.
have alpha_S1 i j: {in S1, forall xi, '[alpha_ i j, xi] = n *- (xi == zeta)}.
  move=> xi S1xi; rewrite /= !cfdotBl !cfdotZl !omu2S1 // mulr0 subrr add0r.
  by rewrite cfdotS1 // eq_sym mulr_natr.
pose beta_ i j := tau (alpha_ i j) - (eta_ i j - eta_ i 0) + n *: zeta1.
pose beta := beta_ 0 j1.
(* This is the first part of (11.8.3). *)
have betaE i j: j != 0 -> beta_ i j = beta.
  move=> nz_j; transitivity (beta_ i j1); congr (_ + _); apply/eqP.
    rewrite eq_sym -subr_eq0 [rhs in _ + rhs]opprD addrACA -opprD subr_eq0.
    rewrite -linearB /= !opprB !addrA !subrK -!/(mu2_ i _).
    by rewrite [Dade pddM _]prDade_sub_TIirr ?mu2_1 //= deltaZ.
  rewrite -subr_eq0 !opprD addrACA -3!opprD opprK subr_eq0 addrACA addrA.
  rewrite -(prDade_sub2_TIirr pddM) -!/(mu2_ _ _) !deltaZ -linearB /=.
  by rewrite opprB addrA subrK !deltaZ opprD opprK addrACA addrA.
pose j := j1. (* The remainder of the proof only uses j = 1. *)
(* This is the second part of (11.8.3). *)
have Rbeta: cfReal beta.
  rewrite /cfReal eq_sym -subr_eq0 rmorphD !rmorphB /= opprB 2!opprD opprB -/j.
  rewrite 2![(eta_ 0 _)^*%CF]cfAut_cycTIiso -!cycTIirr_aut !aut_Iirr0 -Dade_aut.
  set k := aut_Iirr conjC j; rewrite -(betaE 0 k) ?aut_Iirr_eq0 // addrACA.
  rewrite addrC addr_eq0 addrCA subrK opprD opprK Dn raddfZnat -!raddfB /= -Dn. 
  apply/eqP; rewrite (cfConjC_Dade_coherent coh_tau1) ?mFT_odd // -raddfB.
  rewrite Dtau1 ?Zzeta_S1 ?cfAut_seqInd //= -linearZ scalerBr; congr (tau _).
  rewrite opprD !rmorphB !deltaZ /= -!prTIirr_aut !aut_Iirr0 addrACA subrr.
  by rewrite add0r opprK addrC Dn -raddfZnat.
(* This is the consequence of Peterfalvi (11.8.2) and (11.8.5). *)
have tau_alpha i: tau (alpha_ i j) = eta_ i j - eta_ i 0 - n *: zeta1.
  set phi := tau (alpha_ i j); pose sum_tau1 := \sum_(xi <- S1) tau1 xi.
  have A0alpha_j k: alpha_ k j \in 'CF(M, 'A0(M)) by apply: A0alpha.
  have Zphi: phi \in 'Z[irr G].
    by rewrite Dade_vchar // zchar_split vchar_FTtype345_bridge /=.
  have [Y S1_Y [X [Dphi oYX oXS1]]] := orthogonal_split (map tau1 S1) phi.
  (* This is the first part of 11.8.2 *)
  have [a Za defY]: exists2 a, a \in Cint & Y = a *: sum_tau1 - n *: zeta1.
    have [a_ Da defY] := orthonormal_span (map_orthonormal Itau1 o1S1) S1_Y.
    have{Da} Da: {in S1, forall xi, a_ (tau1 xi) = '[phi, tau1 xi]}.
      by move=> xi Sxi; rewrite Da Dphi cfdotDl (orthoPl oXS1) ?map_f ?addr0.
    exists (a_ (tau1 zeta) + n).
      by rewrite Dn rpredD ?rpred_nat // Da // Cint_cfdot_vchar ?Ztau1 ?Z_S1.
    rewrite defY big_map scaler_sumr !(bigD1_seq _ S1zeta) ?seqInd_uniq //=.
    rewrite addrAC scalerDl addrK !(big_seq_cond (predC1 _)) /=; congr (_ + _).
    apply: eq_bigr => xi /andP[S1xi zeta'xi]; congr (_ *: _); rewrite !Da //.
    apply: canRL (addNKr _) _; rewrite addrC -opprB -!raddfB Dtau1 ?Zzeta_S1//=.
    rewrite Dade_isometry //; last first.
      exact: cfun_onS (zcharD1_seqInd_on _ (Zzeta_S1 _ S1xi)).
    by rewrite cfdotBr !alpha_S1 // !mulrb eqxx ifN_eq // !(addr0, opprK).
  have psi_phi: '[psi, phi] = -1 + n. (* This is part of (11.8.5). *)
    rewrite cfdotC Dade_isometry ?A0bridge0 //.
    rewrite cfdotBr !cfdotBl deltaZ !cfdotZl n1S1 // mulr1.
    rewrite !cfdot_prTIirr_red (negPf nz_j1) eqxx !omu2S1 //= cfdotC omuS1 //.
    by rewrite conjC0 mulr0 opprB !subr0 add0r rmorphD rmorphN Dn !rmorph_nat.
  have{psi_phi} col0_beta: '[eta_col 0, beta] = a. (* Also part of (11.8.5). *)
    apply/(addIr (-1 + n))/(canRL (addNKr _)).
    rewrite addrCA addrA addrACA -{}psi_phi Dpsi cfdotBl; congr (_ + _).
      rewrite -(betaE i j) // cfdotDr !cfdotBr -/phi cfdotZr -!addrA.
      apply/(canLR (addNKr _)); rewrite addNr !cfdot_suml.
      rewrite big1 ?add0r ?opprK => [|k _]; last first.
        by rewrite cfdot_cycTIiso andbC eq_sym (negPf nz_j1).
      rewrite addrCA big1 ?mulr0 ?add0r => [|k _]; last first.
        by rewrite cfdotC oS1eta ?conjC0.
      rewrite addrC (bigD1 i) // cfnorm_cycTIiso /= addKr big1 // => k i'k.
      by rewrite cfdot_cycTIiso (negPf i'k).
    rewrite cfdotC Dphi cfdotDl (orthoPl oXS1) ?map_f // addr0.
    rewrite defY cfdotBl scaler_sumr cfproj_sum_orthonormal //.
    rewrite cfdotZl Itau1 ?mem_zchar ?n1S1 // mulr1 rmorphB opprD opprK.
    by rewrite Dn rmorph_nat conj_Cint.
    have a_even: (2 %| a)%C. (* Third internal part of (11.8.5). *)
    have Zbeta: beta \in 'Z[irr G].
      rewrite -{1}(betaE i j) // rpredD ?rpredB ?Zphi ?cycTIiso_vchar //.
      by rewrite Dn rpredZnat // Ztau1 ?mem_zchar.
    rewrite -col0_beta cfdot_real_vchar_even ?mFT_odd //; first 1 last.
      split; first by apply/rpred_sum=> k _; apply: cycTIiso_vchar.
      apply/eqP; rewrite [RHS](reindex_inj (can_inj (@conjC_IirrK _ _))) /=.
      rewrite rmorph_sum; apply/eq_bigr=> k _ /=.
      by rewrite cfAut_cycTIiso -cycTIirr_aut aut_Iirr0.
    have eta00: eta_ 0 0 = 1 by rewrite cycTIirr00 cycTIiso1.
    rewrite orbC cfdotDl 2!cfdotBl cfdotZl -eta00 oS1eta // mulr0 addr0.
    rewrite opprB addrC 2!{1}cfdot_cycTIiso (negPf nz_j1) subr0 /= eta00.
    rewrite Dade_reciprocity // => [|x _ y _]; last by rewrite !cfun1E !inE.
    rewrite cfRes_cfun1 !cfdotBl deltaZ !cfdotZl -!/(mu2_ 0 _).
    rewrite -(prTIirr00 ptiWM) !cfdot_prTIirr cfdotC omu2S1 // conjC0 mulr0.
    by rewrite (negPf nz_j1) add0r subr0 subrr rpred0.
  have nY: '[Y] = n * a * (a - 2%:R) + n ^+ 2. (* Resuming step (11.8.2). *)
    rewrite defY cfnormD cfnormN !cfnormZ cfdotNr cfdotZr.
    rewrite cfnorm_map_orthonormal // -Dn Itau1 ?mem_zchar ?n1S1 // mulr1.
    rewrite scaler_sumr cfproj_sum_orthonormal // rmorphN addrAC.
    rewrite Dn rmorphM !Cint_normK ?rpred_nat // !rmorph_nat conj_Cint // -Dn.
    by rewrite -mulr2n mulrC mulrA -mulr_natr mulNr -mulrBr.
  have{a_even} Da: (a == 0) || (a == 2%:R). (* Second part of (11.8.2). *)
    suffices (b := a - 1): b ^+ 2 == 1.
      by rewrite -!(can_eq (subrK 1) a) add0r addrK orbC -eqf_sqr expr1n.
    have S1gt0: (0 < size S1)%N by case: (S1) S1zeta.
    have: n * b ^+ 2 <= n *+ 3.
      have: 2%:R + n <= n *+ 3 by rewrite addrC ler_add2l ler_muln2r Dn ler1n.
      apply: ler_trans; rewrite sqrrB1 -mulr_natr -mulrBr mulrDr mulrA mulr1.
      rewrite ler_add2r -(ler_add2r (n ^+ 2 + '[X])) !addrA -nY -cfnormDd //.
      by rewrite -Dphi norm_FTtype345_bridge ?S1_1 // ler_addl cfnorm_ge0.
    have Zb: b \in Cint by rewrite rpredB ?rpred1 ?Za.
    have nz_b: b != 0 by rewrite subr_eq0 (memPn _ a a_even) ?(dvdC_nat 2 1).
    rewrite eqr_le sqr_Cint_ge1 {nz_b}//= andbT -Cint_normK // Dn -mulrnA.
    have /CnatP[m ->] := Cnat_norm_Cint Zb; rewrite -natrX -natrM leC_nat.
    by rewrite leq_pmul2l // lern1 -ltnS (ltn_sqr m 2) (leq_sqr m 1).
  have{nY Da} defX: X = eta_ i j - eta_ i 0. (* Last part of (11.8.2). *)
    have{nY Da} /eqP-nY: '[Y] == n ^+ 2.
      by rewrite -subr_eq0 nY addrK -mulrA !mulf_eq0 !subr_eq0 Da orbT.
    have coh_zeta_phi := FTtype345_bridge_coherence _ _ Szeta _ coh_tau1.
    have:= Dphi; rewrite addrC => /coh_zeta_phi->; rewrite ?S1_1 ?deltaZ //.
    rewrite defY scaler_sumr big_seq rpredB ?rpred_sum // => [xi Sxi|].
      by rewrite rpredZ_Cint ?mem_zchar ?map_f.
    by rewrite Dn rpredZnat ?mem_zchar ?map_f.
  have{col0_beta} a0: a = 0. (* This is the conclusion of (11.8.5). *)
    rewrite cfdot_suml big1 // in col0_beta => k _.
    rewrite -(betaE i j) // /beta_ -/phi Dphi -defX addrK defY subrK.
    rewrite cfdotZr cfdot_sumr big1_seq ?mulr0 // => xi S1xi.
    by rewrite cfdotC oS1eta ?conjC0.
  by rewrite Dphi defY defX a0 ?inE ?eqxx // scale0r sub0r addrC.
(* This is step (11.8.6). *)
pose theta := mu_ j - d%:R *: zeta.
have /andP/=[red_muj S2muj]: mu_ j \in [predD S2 & irr M].
  by rewrite memS2red image_f.
have HUtheta: theta \in 'CF(M, HU^#).
  rewrite cfun_onD1 !cfunE mu_1 ?S1_1 // Dd mulrC natrM subrr eqxx.
  by rewrite rpredB ?rpredZ ?(seqInd_on _ S1zeta) ?(seqInd_on _ S2muj).
have Dtheta: theta = mu_ 0 - zeta + \sum_i alpha_ i j.
  rewrite !sumrB -scaler_sumr delta1 scale1r.
  rewrite [X in _ = X]addrC -!addrA -/(mu_ 0); congr (_ + _).
  rewrite [X in _ = _ + X]addrC !addrA addNr add0r -opprD; congr (- _).
  rewrite sumr_const nirrW1 -scaler_nat scalerA mulrC.
  by rewrite divfK ?neq0CG // delta1 addrC scalerBl scale1r subrK.
have tau_theta: tau theta = eta_col j - d%:R *: zeta1.
  pose psi1 i := eta_ i j1 - eta_ i 0 - n *: zeta1.
  have Dpsi1 i: tau (alpha_ i j) = psi1 i by apply: tau_alpha.
  rewrite Dtheta [tau _]raddfD raddf_sum (eq_bigr psi1) //= {Dpsi1}/psi1 -/psi.
  rewrite Dpsi !sumrB  [X in X = _]addrC -!addrA; congr (_ + _).
  rewrite -opprB -opprD -opprB -/(eta_col 0) addrA addrK; congr (- _).
  rewrite sumr_const nirrW1 -scaler_nat scalerA mulrC.
  by rewrite divfK ?neq0CG // delta1 scalerBl scale1r subrK.
have [tau2 coh_tau2] := cohS2.
without loss tau2muj: tau2 coh_tau2 / tau2 (mu_ j) = eta_col j; last first.
  case: FTtype34_noncoherence; rewrite H0_1 -joinGE join1G.
  have uS12: uniq (S2 ++ S1).
    by rewrite cat_uniq ?seqInd_uniq ?andbT //=; apply/hasPn.
  have /perm_eq_coherent: perm_eq (S2 ++ S1) (S_ C); last apply.
    apply: uniq_perm_eq; rewrite ?seqInd_uniq // => xi; rewrite mem_cat.
    apply/idP/idP=> [/orP | /seqIndP[i /setDP[kCi k'HUi] ->]].
      by case; apply/seqIndS/Iirr_kerDS; rewrite ?joing_subr.
    by rewrite !mem_seqInd // inE orbC inE kCi k'HUi andbT orbN.
  move: tau_theta; rewrite -tau2muj // -raddfZnat.
  apply: (bridge_coherent scohM) sS20 coh_tau2 sS10 coh_tau1 sS1S2' _. 
  by rewrite (cfun_onS _ HUtheta) ?setSD // rpredZnat ?Z_S1.
move=> IHtau2; apply: (IHtau2 tau2 coh_tau2); have [IZtau2 Dtau2] := coh_tau2.
have{IHtau2} /hasP[xi S2xi /=irr_xi]: has [mem irr M] S2.
  apply/hasPn=> redS2 {tau2 coh_tau2 IZtau2 Dtau2}.
  have muS2: {subset S2 <= Smu} by move=> xi S2xi; rewrite -memS2red !inE redS2.
  have [_ [tau2 tau2mu coh_tau2]] := uniform_prTIred_coherent pddM nz_j1.
  have S2uniform: {subset S2 <= uniform_prTIred_seq pddM j}.
    move=> _ /muS2/imageP[k nz_k ->]; apply: image_f.
    by rewrite !inE [_ != 0]nz_k /= !mu_1.
  apply: (IHtau2 tau2); first exact: subset_coherent_with coh_tau2.
  have [_ /(_ _ nz_j1) Ez _ _] := FTtype345_constants maxM MtypeP notMtype2.
  by have:= tau2mu j; rewrite Ez -/delta delta1 scale1r.
suffices: '[tau2 (mu_ j), eta_col j] != 0.
  have:= FTtypeP_coherent_TIred sS20 coh_tau2 irr_xi S2xi S2muj.
  case=> _ -> [[-> ->] | [-> -> _] /eqP[]]; first by rewrite deltaZ.
  rewrite -[cyclicTIiso _]/sigma cfdot_sumr big1 ?mulr0 // => i _.
  rewrite cfdotZl proj_col_eta -(inj_eq irr_inj) conjC_IirrE eq_sym.
  by rewrite odd_eq_conj_irr1 ?mFT_odd // irr_eq1 (negPf nz_j1) mulr0.
pose gamma := xi 1%g *: mu_ j - mu_ j 1%g *: xi.
have: '[tau2 gamma, tau theta] != 0.
  have [Txi Tzeta] := (seqInd_subT S2xi, seqInd_subT S1zeta).
  have S2gamma: gamma \in 'Z[S2, HU^#] by apply: sub_seqInd_zchar.
  rewrite Dtau2 ?zcharD1_seqInd //; move/zchar_on in S2gamma.
  rewrite Dade_isometry ?(cfun_onS sHU_A0) // cfdotBr cfdotZr !cfdotBl !cfdotZl.
  rewrite cfnorm_prTIred omuS1 // (seqInd_ortho _ _ S2muj) ?(memPn red_muj) //.
  rewrite (seqInd_ortho _ Txi) ?(memPn (sS1S2' _)) // !(mulr0, subr0) mulf_eq0.
  by rewrite char1_eq0 ?irrWchar // -cfnorm_eq0 irrWnorm ?oner_eq0 ?neq0CG.
apply: contraNneq => o_muj_etaj; rewrite {}tau_theta !{gamma}raddfB subr_eq0 /=.
have /CnatP[xi1 ->]: xi 1%g \in Cnat by rewrite Cnat_char1 ?irrWchar.
rewrite mu_1 // cfdotZr !cfdotBl !raddfZnat !cfdotZl {}o_muj_etaj cfdot_sumr.
have /orthogonalP oS2_S1: orthogonal (map tau2 S2) (map tau1 S1).
  exact: (coherent_ortho scohM) sS20 coh_tau2 sS10 coh_tau1 sS1S2'.
rewrite !oS2_S1 ?map_f // big1 ?(mulr0, subr0) // => k _.
exact: (coherent_ortho_cycTIiso _ _ coh_tau2).
Qed.

(* This is Peterfalvi (11.9). *)
(* Note that in the proof of part (a), the text improperly suggests using     *)
(* (5.3.b) to show then tau (zeta - zeta^alpha) is orthogonal to the eta i j. *)
(* Since alpha might not be conjugation, this is not obvious. Indeed the best *)
(* way to derive this is to use (5.5) together with the coherence of S(HC).   *)
(* In part (c) we start by reducing the proof to q <= p - 1; we also don't    *)
(* compute [tau (mu0 - zeta), tau2 lambda] = [chi, tau2 lambda] since this    *)
(* is not needed to prove than u = a: one only needs to show that the         *)
(* the left-hand side is an integer, which is in fact required to show that   *)
(* the right-hand is an integer.                                              *)
Lemma FTtype34_structure (eta0row := \sum_j eta_ 0 j) :
  [/\ (*a*) {in S1, forall zeta, eq_proj_eta (tau (bridge0 zeta)) eta0row},
      (*b*) (p < q)%N
    & (*c*) FTtype M == 3 /\ typeP_Galois MtypeP].
Proof.
have sum_etaW F: \sum_(eta <- etaW) F eta = \sum_i \sum_j F (eta_ i j).
  rewrite big_map big_tuple (reindex (dprod_Iirr defW)) /=.
    by rewrite pair_bigA; apply: eq_bigr => -[i j].
  by exists (inv_dprod_Iirr defW) => ij; rewrite ?dprod_IirrK ?inv_dprod_IirrK.
have bridgeS1: {in S1, forall zeta, eq_proj_eta (tau (bridge0 zeta)) eta0row}.
  move=> zeta S1zeta; set phi := bridge0 zeta; have irr_zeta := irrS1 S1zeta.
  have [X etaX [chi [Dchi oXchi o_chi_eta]]] := orthogonal_split etaW (tau phi).
  have [Isigma Zsigma] := cycTI_Zisometry ctiWG.
  have{o_chi_eta} o_chi_eta i j: '[chi, eta_ i j] = 0.
    by rewrite (orthoPl o_chi_eta) ?map_f ?mem_irr.
  have o1etaW: orthonormal etaW by rewrite map_orthonormal ?irr_orthonormal.
  have [a Da defX] := orthonormal_span o1etaW etaX; pose a_ := a (eta_ _ _).
  have{Da} Da i j: a_ i j = '[tau phi, eta_ i j].
    by rewrite Dchi cfdotDl o_chi_eta addr0 /a_ Da.
  have Zphi: phi \in 'Z[irr M, HU^#] by apply: Zbridge0.
  have A0phi: phi \in 'CF(M, 'A0(M)) by apply: A0bridge0.
  have a00_1 : a_ 0 0 = 1.
    rewrite Da cycTIirr00 [sigma 1]cycTIiso1.
    rewrite Dade_reciprocity // => [|x _ y _]; last by rewrite !cfun1E !inE.
    rewrite rmorph1 /= -(prTIirr00 ptiWM) -/(mu2_ 0 0) cfdotC.
    by rewrite cfdotBr cfdot_prTIirr_red omu2S1 // subr0 rmorph1.
  have aut_phi nu: cfAut nu (tau phi) = tau phi + tau (zeta - cfAut nu zeta).
    rewrite -Dade_aut !rmorphB !raddfB /= !addrA subrK.
    by rewrite -prTIred_aut aut_Iirr0.
  have Za i j: a_ i j \in Cint.
    rewrite Da Cint_cfdot_vchar ?cycTIiso_vchar //.
    by rewrite Dade_vchar ?(zchar_onS sHU_A0).
  have [tau1 coh_tau1] := cohS1; have [_ Dtau1] := coh_tau1.
  have o_tau1_eta := coherent_ortho_cycTIiso MtypeP sS10 coh_tau1.
  have a_aut nu i j: a (cfAut nu (eta_ i j)) = a_ i j.
    symmetry; transitivity '[cfAut nu (tau phi), cfAut nu (eta_ i j)].
      by rewrite cfdot_aut_vchar ?cycTIiso_vchar // -Da aut_Cint.
    rewrite aut_phi cfAut_cycTIiso -cycTIirr_aut [a _]Da cfdotDl addrC.
    rewrite -Dtau1 ?zcharD1_seqInd ?seqInd_sub_aut_zchar // raddfB cfdotBl.
    by rewrite !o_tau1_eta ?cfAut_seqInd ?cfAut_irr // subr0 add0r.
  pose a10 := a_ i1 0; pose a01 := a_ 0 j1; pose a11 := a_ i1 j1.
  have Da10 i: i != 0 -> a_ i 0 = a10.
    case/(cfExp_prime_transitive pr_q nz_i1) => k co_k_wi1 Dwi.
    rewrite -(cforder_dprodl defW) -dprod_IirrEl in co_k_wi1.
    have [[nu eta10nu] _] := cycTIiso_aut_exists ctiWG co_k_wi1.
    by rewrite /a_ dprod_IirrEl Dwi rmorphX /= -dprod_IirrEl eta10nu a_aut.
  have Da01 j: j != 0 -> a_ 0 j = a01.
    case/(cfExp_prime_transitive pr_p nz_j1) => k co_k_wj1 Dwj.
    rewrite -(cforder_dprodr defW) -dprod_IirrEr in co_k_wj1.
    have [[nu eta01nu] _] := cycTIiso_aut_exists ctiWG co_k_wj1.
    by rewrite /a_ dprod_IirrEr Dwj rmorphX /= -dprod_IirrEr eta01nu a_aut.
  have DaB1 i j: a_ i j = a_ i 0 + a_ 0 j - a_ 0 0.
    apply: (canRL (addrK _)); rewrite !Da cycTIiso_cfdot_exchange // => x Vx.
    have /setDP[A0x A'x]: x \in 'A0(M) :\: 'A(M).
      by rewrite (FTsupp0_typeP maxM MtypeP) // mem_class_support.
    by rewrite Dade_id // (cfun_on0 (zchar_on Zphi)) // -defA.
  pose p1 : algC := p.-1%:R; pose q1 : algC := q.-1%:R.
  have normX: '[X] = 1 + q1 * a10 ^+ 2 + p1 * a01 ^+ 2 + p1 * q1 * a11 ^+ 2.
    transitivity (\sum_i \sum_j a_ i j ^+ 2).
      rewrite defX cfnorm_sum_orthonormal // sum_etaW.
      by apply/eq_bigr=> i _; apply/eq_bigr=> j _; rewrite Cint_normK ?Za.
    rewrite -addrA addrACA (bigD1 0) //= (bigD1 0) //= a00_1 expr1n.
    rewrite -natrM !mulr_natl mulrnA -mulrnDl.
    rewrite -nirrW1 -nirrW2 -!(cardC1 0) -!sumr_const.
    congr (1 + _ + _); first by apply: eq_bigr => j /Da01->.
    apply: eq_bigr => i /Da10-Dai0; rewrite (bigD1 0) //= Dai0; congr (_ + _).
    by apply: eq_bigr => j /Da01-Da0j; rewrite DaB1 Dai0 Da0j -DaB1.
  have normX_le_q: '[X] <= q%:R.
    rewrite -(ler_add2r '[chi]) -cfnormDd // -Dchi -ler_subl_addl.
    have ->: '[tau phi] - q%:R = 1.
      rewrite Dade_isometry ?A0bridge0 // cfnormBd; last by rewrite omuS1.
      by rewrite cfnorm_prTIred cfdotS1 // eqxx addrC addKr.
    suffices: '[chi] != 0.
      suffices /CnatP[nchi ->]: '[chi] \in Cnat by rewrite ler1n lt0n -eqC_nat.
      rewrite Cnat_cfnorm_vchar // -(canLR (addKr _) Dchi) defX addrC rpredB //.
         by rewrite Dade_vchar // (zchar_onS (FTsupp_sub0 M)) ?defA.
       rewrite big_map big_seq rpred_sum // => _ /(cycTIirrP defW)[i [j ->]].
       by rewrite rpredZ_Cint ?Za ?cycTIiso_vchar.
    pose theta := zeta - zeta^*%CF.
    have Ztheta: theta \in 'Z[S1, HU^#] by apply: seqInd_sub_aut_zchar.
    have: '[tau phi, tau theta] != 0.
      rewrite Dade_isometry //; last by rewrite (cfun_onS _ (zchar_on Ztheta)).
      rewrite cfdotBl !cfdotBr ?omuS1 ?cfAut_seqInd // subr0 add0r oppr_eq0.
      rewrite irrWnorm // (seqInd_conjC_ortho _ _ _ S1zeta) ?mFT_odd //.
      by rewrite subr0 oner_eq0.
    rewrite cfnorm_eq0 Dchi; apply: contraNneq => ->; rewrite addr0 defX.
    rewrite -Dtau1 ?zcharD1_seqInd //.
    rewrite cfdot_suml big_map big1_seq // => _ /(cycTIirrP defW)[i [j ->]].
    apply/eqP; rewrite cfdotC fmorph_eq0 cfdotZr raddfB cfdotBl.
    by rewrite !o_tau1_eta ?cfAut_seqInd ?irr_aut // subrr mulr0.
  have a2_ge0 i j: 0 <= a_ i j ^+ 2 by rewrite -realEsqr Creal_Cint.
  have a11_0: a11 = 0.
    have: ('[X] < (2 * q.-1)%:R).
      rewrite (ler_lt_trans normX_le_q) // ltC_nat -subn1 mulnBr ltn_subRL.
      by rewrite !mul2n -!addnn ltn_add2r odd_prime_gt2 ?mFT_odd.
    apply: contraTeq => nz_a11; rewrite ler_gtF // normX ler_paddl //.
      by rewrite !mulr_natl ?addr_ge0 ?ler01 ?mulrn_wge0 ?a2_ge0.
    rewrite -mulr_natl -natrM ?ler_pmul ?natr_ge0 ?sqr_Cint_ge1 ?Za //.
    by rewrite leC_nat leq_mul // -subn1 ltn_subRL odd_prime_gt2 ?mFT_odd.
  rewrite a11_0 expr0n /= mulr0 addr0 in normX.
  have a10_a01: a10 + a01 = 1.
    by apply/eqP; rewrite -subr_eq0 -a00_1 -DaB1 -/a11 a11_0.
  have{o_chi_eta} o_chi_eta: orthogonal chi etaW.
    by apply/orthoPl=> _ /mapP[_ /(cycTIirrP defW)[i [j ->]] ->].
  have a10_0: a10 = 0.
    apply: contraNeq (FTtype34_not_ortho_cycTIiso S1zeta) => nz_a10.
    have a01_0: a01 = 0.
      apply: contraTeq normX_le_q => nz_a01; rewrite normX ltr_geF //.
      rewrite ltr_spaddr 1?mulr_gt0 ?ltr0n -?subn1 ?subn_gt0 ?prime_gt1 //.
        by rewrite ltr_def sqrf_eq0 nz_a01 a2_ge0.
      rewrite -ler_subl_addl -(natrB _ (prime_gt0 pr_q)) subn1 -mulr_natl.
      by rewrite ler_wpmul2l ?ler0n // sqr_Cint_ge1 ?Za.
    suffices <-: X = eta_col 0 by rewrite Dchi /eq_proj_eta addrC addKr.
    rewrite defX sum_etaW exchange_big (bigD1 0) //= addrC.
    rewrite big1 ?add0r => [|j nz_j]; first apply: eq_bigr => i _; last first.
      rewrite (bigD1 0) // [a _]Da01 //= a01_0 scale0r add0r big1 // => i nz_i.
      by rewrite [a _]DaB1 Da10 // Da01 // a10_a01 a00_1 subrr scale0r.
    have [-> | nz_i] := eqVneq i 0; first by rewrite [a _]a00_1 scale1r.
    by rewrite [a _]Da10 // (canRL (addrK _) a10_a01) a01_0 subr0 scale1r.
  suffices <-: X = eta0row by rewrite Dchi /eq_proj_eta addrC addKr.
  rewrite defX sum_etaW (bigD1 0) //= addrC.
  rewrite big1 ?add0r => [|i nz_i]; first apply: eq_bigr => j _; last first.
    rewrite (bigD1 0) // [a _]Da10 //= a10_0 scale0r add0r big1 // => j nz_j.
    by rewrite [a _]DaB1 Da10 // Da01 // a10_a01 a00_1 subrr scale0r.
  have [-> | nz_j] := eqVneq j 0; first by rewrite [a _]a00_1 scale1r.
  by rewrite [a _]Da01 // (canRL (addKr _) a10_a01) a10_0 oppr0 add0r scale1r.
have [zeta [irr_zeta Szeta zeta1]] := FTtypeP_ref_irr maxM MtypeP.
have{zeta1} [S1zeta zeta1]: zeta \in S1 /\ zeta 1%g = q%:R.
  split=> //; have [k nz_k Dzeta] := seqIndC1P Szeta.
  rewrite Dzeta mem_seqInd // !inE subGcfker nz_k -defM'' lin_char_der1 //.
  rewrite -mulr_natl Dzeta cfInd1 //= -(index_sdprod defM) in zeta1.
  by apply/andP; rewrite irr_char -(mulfI _ zeta1) ?neq0CG.
have{Szeta} ltpq: (p < q)%N.
  rewrite ltn_neqAle neq_pq leqNgt /=.
  apply: contra (FTtype34_not_ortho_cycTIiso S1zeta) => ltqp.
  case/(FTtype345_Dade_bridge0 _ MtypeP): Szeta => // chi [-> _ _ o_chi_eta].
  rewrite /eq_proj_eta addrC addKr (orthogonal_oppl chi).
  by apply/orthoPl=> _ /mapP[_ /(cycTIirrP defW)[i [j ->]] ->].
suffices galM: typeP_Galois MtypeP.
  have [_ [_ _ _ [/= cycUbar _ _]]] := typeP_Galois_P maxM notMtype5 galM.
  have{cycUbar} cycUbar: cyclic (U / U') by rewrite -defU' -defC.
  have nilU: nilpotent U by have [_ []] := MtypeP.
  case/orP: Mtype34 => // /(compl_of_typeIV maxM MtypeP)[_ /negP[]].
  exact/cyclic_abelian/cyclic_nilpotent_quo_der1_cyclic.
apply: contraLR ltpq => gal'M; rewrite -leqNgt (leq_trans _ (leq_pred _)) //.
have [_ _ _] := typeP_nonGalois_characters maxM notMtype5 gal'M.
case: (_ gal'M) => H1 /= [_ _ nH1U _ []]; set a := #|U : _| => a_gt1.
rewrite def_p -/q -defU' -defS2 => a_dv_p1 cycUhat _.
set irr_qa := [pred lambda in irr M | lambda 1%g == (q * a)%:R] => S2_qa.
have{S2_qa}/hasP[lambda S2lambda /andP[irr_lambda /eqP-lambda1]]: has irr_qa S2.
  have [a2_dv_pu] := S2_qa; rewrite has_count; apply: leq_trans.
  rewrite -(@ltn_pmul2r (a ^ 2 * #|C|)); last first.
    by rewrite !muln_gt0 (ltnW a_gt1) cardG_gt0.
  by rewrite mul0n divnK // muln_gt0 cardG_gt0 -subn1 subn_gt0 prime_gt1.
have{nH1U cycUhat} a_dv_u: a %| u.
  rewrite /u card_quotient ?normal_norm // indexgS // defU'.
  rewrite der1_min ?cyclic_abelian // normsI ?normG //.
  by rewrite (subset_trans nH1U) // astab_norm.
pose j := j1; pose psi := mu_ j - (u %/ a)%:R *: lambda.
have /andP/=[red_muj S2muj]: mu_ j \in [predD S2 & irr M].
  by rewrite memS2red image_f.
have S2psi: psi \in 'Z[S2, M^#].
  rewrite zcharD1E rpredB ?rpredZnat ?mem_zchar //=.
  by rewrite !cfunE mu_1 // lambda1 -natrM mulnCA divnK ?subrr.
pose phi := tau (mu_ 0 - zeta).
have o_phi_psi: '[phi, tau psi] = 0.
  have Apsi: psi \in 'CF(M, 'A(M)) by rewrite defA (zcharD1_seqInd_on _ S2psi).
  have [Tzeta Tlambda] := (seqInd_subT  S1zeta, seqInd_subT S2lambda).
  rewrite Dade_isometry ?A0bridge0 ?(cfun_onS (FTsupp_sub0 M)) //.
  rewrite cfdotBl !cfdotBr !cfdotZr cfdot_prTIred eq_sym (negPf nz_j1) add0r.
  rewrite !(seqInd_ortho _ Tzeta) ?Tmu ?(memPnC (sS1S2' S1zeta)) // add0r.
  rewrite (seqInd_ortho _ (Tmu 0)) ?(memPnC (prTIred_not_irr _ _)) // !mulr0.
  by rewrite subrr.
have [tau2 coh_tau2] := cohS2; have [[_ Ztau2] Dtau2] := coh_tau2.
have ua_1: (u %/ a)%:R * `|'[phi, tau2 lambda]| == 1.
  rewrite -normr_nat -normrM mulr_natl -!raddfMn -[_ *+ _](subrK (mu_ j)) /=.
  rewrite -opprB addrC raddfB cfdotBr -scaler_nat (Dtau2 _ S2psi) o_phi_psi.
  case: (FTtypeP_coherent_TIred _ coh_tau2 _ S2lambda S2muj) => // -[b k] -> _.
  rewrite -/(eta_col k) cfdotZr rmorph_sign subr0 normrMsign.
  rewrite -[phi](subrK eta0row) cfdotDl cfdot_sumr big1 => [|j' _]; last first.
    by rewrite (orthoPl (bridgeS1 _ _)) ?map_f ?mem_irr.
  rewrite add0r cfdotC norm_conjC cfdot_sumr (bigD1 k) //= proj_col_eta eqxx.
  by rewrite big1 ?addr0 ?normr1 // => i k'i; rewrite proj_col_eta (negPf k'i).
have Du: u = a.
  apply/eqP; rewrite -[a]mul1n eqn_mul ?(ltnW a_gt1) // -eqC_nat.
  move: ua_1; rewrite Cnat_mul_eq1 ?rpred_nat //; first by case/andP.
  rewrite Cnat_norm_Cint ?Cint_cfdot_vchar //; last by rewrite Ztau2 ?mem_zchar.
  rewrite Dade_vchar // zchar_split A0bridge0 //.
  by rewrite rpredB ?char_vchar ?prTIred_char ?irrWchar.
have lequ: (q <= u)%N.
  have u1_gt0: (0 < u.-1)%N by rewrite -subn1 subn_gt0 Du.
  rewrite (leq_trans _ (leq_pred u)) // dvdn_leq //.
  suffices ->: q = #|W1 / C|%g by apply: Frobenius_dvd_ker1 frobUW1bar.
  apply/card_isog/quotient_isog; first by have [] := joing_subP nC_UW1.
  by rewrite setIAC (coprime_TIg coUq) setI1g.
by rewrite (leq_trans lequ) // Du dvdn_leq // -subn1 subn_gt0 prime_gt1.
Qed.

End Eleven.

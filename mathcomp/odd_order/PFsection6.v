(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrbool ssrfun eqtype ssrnat seq path div choice.
From mathcomp
Require Import fintype tuple finfun bigop prime ssralg poly finset center.
From mathcomp
Require Import fingroup morphism perm automorphism quotient action zmodp.
From mathcomp
Require Import gfunctor gproduct cyclic pgroup commutator gseries nilpotent.
From mathcomp
Require Import sylow abelian maximal hall frobenius.
From mathcomp
Require Import matrix mxalgebra mxrepresentation vector ssrnum algC algnum.
From mathcomp
Require Import classfun character inertia vcharacter integral_char.
From mathcomp
Require Import PFsection1 PFsection2 PFsection3 PFsection4 PFsection5.

(******************************************************************************)
(* This file covers Peterfalvi, Section 6:                                    *)
(* Some Coherence Theorems                                                    *)
(* Defined here:                                                              *)
(*   odd_Frobenius_quotient K L M <->                                         *)
(*      L has odd order, M <| L, K with K / M nilpotent, and L / H1 is a      *)
(*      Frobenius group with kernel K / H1, where H1 / M = (K / M)^(1).       *)
(*      This is the statement of Peterfalvi, Hypothesis (6.4), except for     *)
(*      the K <| L and subcoherence assumptions, to be required separately.   *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(* The main section *)
Section Six.

Variables (gT : finGroupType) (G : {group gT}).
Implicit Types H K L P M W Z : {group gT}.

(* Grouping lemmas that assume Hypothesis (6.1). *)
Section GeneralCoherence.

Variables K L : {group gT}.
Local Notation S M := (seqIndD K L K M).
Local Notation calS := (S 1).

Variables (R : 'CF(L) -> seq 'CF(G)) (tau : {linear 'CF(L) -> 'CF(G)}).

(* These may need to be grouped, in order to make the proofs of 6.8, 10.10, *)
(* and 12.6 more manageable.                                                *)
Hypotheses (nsKL : K <| L) (solK : solvable K).
Hypothesis Itau : {in 'Z[calS, L^#] &, isometry tau}.
Hypothesis scohS : subcoherent calS tau R.

Let sKL : K \subset L. Proof. exact: normal_sub. Qed.
Let nKL : L \subset 'N(K). Proof. exact: normal_norm. Qed.
Let orthS: pairwise_orthogonal calS. Proof. by case: scohS. Qed.
Let sSS M : {subset S M <= calS}. Proof. exact: seqInd_sub. Qed.
Let ccS M : cfConjC_closed (S M). Proof. exact: cfAut_seqInd. Qed.
Let uniqS M : uniq (S M). Proof. exact: seqInd_uniq. Qed.
Let nrS : ~~ has cfReal calS. Proof. by case: scohS => [[]]. Qed.

Lemma exists_linInd M :
  M \proper K -> M <| K -> exists2 phi, phi \in S M & phi 1%g = #|L : K|%:R.
Proof.
move=> ltMK nsMK; have [sMK nMK] := andP nsMK.
have ntKM: (K / M)%g != 1%g by rewrite -subG1 quotient_sub1 // proper_subn.
have [r lin_r ntr] := solvable_has_lin_char ntKM (quotient_sol M solK).
pose i := mod_Iirr r; exists ('Ind[L] 'chi_i); last first.
  by rewrite cfInd1 ?mod_IirrE // cfMod1 lin_char1 ?mulr1.
apply/seqIndP; exists i; rewrite // !inE subGcfker mod_IirrE ?cfker_mod //=.
by rewrite mod_Iirr_eq0 // -irr_eq1 ntr.
Qed.

(* This is Peterfalvi (6.2). *)
Lemma coherent_seqIndD_bound (A B C D : {group gT}) :
        [/\ A <| L, B <| L, C <| L & D <| L] ->
  (*a*) [/\ A \proper K, B \subset D, D \subset C, C \subset K
          & D / B \subset 'Z(C / B)]%g ->
  (*b*) coherent (S A) L^# tau -> \unless coherent (S B) L^# tau,
  #|K : A|%:R - 1 <= 2%:R * #|L : C|%:R * sqrtC #|C : D|%:R :> algC.
Proof.
move=> [nsAL nsBL nsCL nsDL] [ltAK sBD sDC sCK sDbZC] cohA.
have sBC := subset_trans sBD sDC; have sBK := subset_trans sBC sCK.
have [sAK nsBK] := (proper_sub ltAK, normalS sBK sKL nsBL).
have{sBC} [nsAK nsBC] := (normalS sAK sKL nsAL, normalS sBC sCK nsBK).
rewrite real_lerNgt ?rpredB ?ger0_real ?mulr_ge0 ?sqrtC_ge0 ?ler0n ?ler01 //.
apply/unless_contra; rewrite negbK -(Lagrange_index sKL sCK) natrM => lb_KA.
pose S2 : seq 'CF(L) := [::]; pose S1 := S2 ++ S A; rewrite -[S A]/S1 in cohA.
have ccsS1S: cfConjC_subset S1 calS by apply: seqInd_conjC_subset1.
move: {2}_.+1 (leq_addr (size S1) (size calS).+1) => n.
elim: n => [|n IHn] in (S2) S1 ccsS1S cohA * => lb_n.
  by rewrite ltnNge uniq_leq_size // in lb_n; case: ccsS1S.
without loss /allPn[psi /= SBpsi S1'psi]: / ~~ all (mem S1) (S B).
  by case: allP => [sAB1 _ | _]; [apply: subset_coherent cohA | apply].
have [[_ sS1S _] Spsi] := (ccsS1S, sSS SBpsi).
apply (IHn [:: psi, psi^* & S2]%CF); rewrite ?addnS 1?leqW {n lb_n IHn}//= -/S1.
  exact: extend_cfConjC_subset.
have [phi SAphi phi1] := exists_linInd ltAK nsAK.
have{SAphi} S1phi: phi \in S1 by rewrite mem_cat SAphi orbT.
apply: (extend_coherent scohS) ccsS1S S1phi Spsi S1'psi _.
have{SBpsi} /seqIndP[i /setDP[kBi _] {psi}->] := SBpsi; rewrite inE in kBi.
rewrite {phi}phi1 cfInd1 // dvdC_mulr //; last by rewrite CintE Cnat_irr1.
split; rewrite // big_cat sum_seqIndD_square // big_seq ltr_paddl //=.
  apply/sumr_ge0=> xi S2xi; rewrite divr_ge0 ?cfnorm_ge0 ?exprn_ge0 //.
  by rewrite Cnat_ge0 // (Cnat_seqInd1 (sS1S _ _)) // mem_cat S2xi.
rewrite mulrC ltr_pmul2l ?gt0CiG //; apply: ler_lt_trans lb_KA.
by rewrite -!mulrA !ler_wpmul2l ?ler0n // (irr1_bound_quo nsBC).
Qed.

(* This is Peterfalvi, Theorem (6.3). *)
Theorem bounded_seqIndD_coherence M H H1 :
   [/\ M <| L, H <| L & H1 <| L] ->
   [/\ M \subset H1, H1 \subset H & H \subset K] ->
 (*a*) nilpotent (H / M) ->
 (*b*) coherent (S H1) L^# tau ->
 (*c*) (#|H : H1| > 4 * #|L : K| ^ 2 + 1)%N ->
 coherent (S M) L^# tau.
Proof.
move: H1 => A [nsML nsHL nsAL] [sMA sAH sHK] nilHb cohA lbHA.
elim: {A}_.+1 {-2}A (ltnSn #|A|) => // m IHm A leAm in nsAL sMA sAH cohA lbHA *.
have [/group_inj-> // | ltMA] := eqVproper sMA; have [sAL nAL] := andP nsAL.
have{ltMA} [B maxB sMB]: {B : {group gT} | maxnormal B A L & M \subset B}.
  by apply: maxgroup_exists; rewrite ltMA normal_norm.
have /andP[ltBA nBL] := maxgroupp maxB; have [sBA not_sAB] := andP ltBA.
have [sBH sBL] := (subset_trans sBA sAH, subset_trans sBA sAL).
have nsBL: B <| L by apply/andP.
suffices{m IHm leAm} cohB: coherent (S B) L^# tau.
  apply: IHm cohB _ => //; first exact: leq_trans (proper_card ltBA) _.
  by rewrite (leq_trans lbHA) // dvdn_leq // indexgS.
have /andP[sHL nHL] := nsHL.
have sAbZH: (A / B \subset 'Z(H / B))%g.
  have nBA := subset_trans sAL nBL; have nsBA : B <| A by apply/andP.
  set Zbar := 'Z(H / B); set Abar := (A / B)%g; pose Lbar := (L / B)%g.
  have nZHbar: Lbar \subset 'N(Zbar) by rewrite gFnorm_trans ?quotient_norms.
  have /mingroupP[/andP[ntAbar nALbar] minBbar]: minnormal Abar Lbar.
    apply/mingroupP; split=> [|Dbar /andP[ntDbar nDLbar] sDAbar].
      by rewrite -subG1 quotient_sub1 // not_sAB quotient_norms.
    have: Dbar <| Lbar by rewrite /normal (subset_trans sDAbar) ?quotientS.
    case/(inv_quotientN nsBL)=> D defDbar sBD /andP[sDL nDL].
    apply: contraNeq ntDbar => neqDAbar; rewrite defDbar quotientS1 //.
    have [_ /(_ D) {1}<- //] := maxgroupP maxB.
    rewrite -(quotient_proper (normalS sBD sDL nsBL)) // -defDbar.
    by rewrite properEneq sDAbar neqDAbar.
  apply/setIidPl/minBbar; rewrite ?subsetIl {minBbar}//= andbC -/Abar -/Zbar.
  rewrite normsI ?meet_center_nil ?quotient_normal ?(normalS sAH sHL) //=.
  suffices /homgP[f /= <-]: (H / B)%g \homg (H / M)%g by rewrite morphim_nil.
  by apply: homg_quotientS; rewrite ?(subset_trans sHL) ?normal_norm.
have ltAH: A \proper H.
  by rewrite properEneq sAH (contraTneq _ lbHA) // => ->; rewrite indexgg addn1.
set x : algC := sqrtC #|H : A|%:R.
have [nz_x x_gt0]: x != 0 /\ 0 < x by rewrite gtr_eqF sqrtC_gt0 gt0CiG.
without loss{cohA} ubKA: / #|K : A|%:R - 1 <= 2%:R * #|L : H|%:R * x.
  have [sAK ltAK] := (subset_trans sAH sHK, proper_sub_trans ltAH sHK).
  exact: coherent_seqIndD_bound id.
suffices{lbHA}: (x - x^-1) ^+ 2 <= (2 * #|L : K|)%:R ^+ 2.
  rewrite ltr_geF // sqrrB divff // sqrtCK ltr_spaddr ?exprn_gt0 ?invr_gt0 //.
  by rewrite ler_subr_addr -natrX -natrD ler_nat expnMn addnS lbHA.
rewrite ler_pexpn2r ?unfold_in /= ?ler0n //; last first.
  by rewrite subr_ge0 -div1r ler_pdivr_mulr // -expr2 sqrtCK ler1n.
rewrite -(ler_pmul2l x_gt0) -(ler_pmul2l (gt0CiG K H)) 2!mulrBr -expr2 sqrtCK.
rewrite !mulrA mulfK // mulrAC natrM mulrCA -2!natrM [in _ * x]mulnC.
by rewrite !Lagrange_index // (ler_trans _ ubKA) // ler_add2l ler_opp2 ler1n.
Qed.

(* This is the statement of Peterfalvi, Hypothesis (6.4). *)
Definition odd_Frobenius_quotient M (H1 := K^`(1) <*> M) :=
  [/\ (*a*) odd #|L|,
      (*b*) [/\ M <| L, M \subset K & nilpotent (K / M)]
    & (*c*) [Frobenius L / H1 with kernel K / H1] ]%g.

(* This is Peterfalvi (6.5). *)
Lemma non_coherent_chief M (H1 := (K^`(1) <*> M)%G) :
     odd_Frobenius_quotient M -> \unless coherent (S M) L^# tau,
   [/\ (*a*) chief_factor L H1 K /\ (#|K : H1| <= 4 * #|L : K| ^ 2 + 1)%N
     & (*b*) exists2 p : nat, p.-group (K / M)%g /\ ~~ abelian (K / M)
     & (*c*) ~~ (#|L : K| %| p - 1)].
Proof.
case=> oddL [nsML sMK nilKM]; rewrite /= -(erefl (gval H1)) => frobLb.
set e := #|L : K|; have odd_e: odd e := dvdn_odd (dvdn_indexg L K) oddL.
have{odd_e} mod1e_lb m: odd m -> m == 1 %[mod e] -> (m > 1 -> 2 * e + 1 <= m)%N.
  move=> odd_m e_dv_m1 m_gt1; rewrite eqn_mod_dvd 1?ltnW // subn1 in e_dv_m1.
  by rewrite mul2n addn1 dvdn_double_ltn.
have nsH1L: H1 <| L by rewrite normalY // gFnormal_trans.
have nsH1K: H1 <| K by rewrite (normalS _ sKL nsH1L) // join_subG der_sub.
have [sH1K nH1K] := andP nsH1K; have sMH1: M \subset H1 by apply: joing_subr.
have cohH1: coherent (S H1) L^# tau.
  apply: uniform_degree_coherence (subset_subcoherent scohS _) _ => //.
  apply/(@all_pred1_constant _ e%:R)/allP=> _ /mapP[chi Schi ->] /=.
  have [i /setIdP[_]] := seqIndP Schi; rewrite inE join_subG -lin_irr_der1.
  by case/andP=> lin_chi _ ->; rewrite cfInd1 ?lin_char1 ?mulr1.
apply/unlessP; have [/val_inj-> | ltMH1] := eqVproper sMH1; first by left.
have [lbK|ubK] := ltnP; [by left; apply: bounded_seqIndD_coherence lbK | right].
have{ubK} ubK: (#|K : H1| < (2 * e + 1) ^ 2)%N.
  apply: leq_ltn_trans ubK _; rewrite -subn_gt0 sqrnD expnMn addKn.
  by rewrite !muln_gt0 indexg_gt0.
have{frobLb} [[E1b frobLb] [sH1L nH1L]] := (existsP frobLb, andP nsH1L).
have [defLb ntKb _ _ /andP[sE1L _]] := Frobenius_context frobLb.
have iH1_mod1e H2:
  H1 \subset H2 -> H2 \subset K -> L \subset 'N(H2) -> #|H2 : H1| == 1 %[mod e].
- move=> sH12 sH2K nPL; have sH2L := subset_trans sH2K sKL.
  rewrite eqn_mod_dvd // subn1 -card_quotient ?(subset_trans sH2L) //.
  have [-> | ntH2b] := eqVneq (H2 / H1)%g 1%g; first by rewrite cards1.
  have ->: e = #|E1b|.
    by rewrite (index_sdprod defLb) index_quotient_eq ?(setIidPr sH1L).
  have /Frobenius_subl/Frobenius_dvd_ker1-> := frobLb; rewrite ?quotientS //.
  by rewrite (subset_trans sE1L) ?quotient_norms.
have{iH1_mod1e} chiefH1: chief_factor L H1 K.
  have ltH1K: H1 \proper K by rewrite /proper sH1K -quotient_sub1 ?subG1.
  rewrite /chief_factor nsKL andbT; apply/maxgroupP; rewrite ltH1K.
  split=> // H2 /andP[ltH2K nH2L] sH12; have sH2K := proper_sub ltH2K.
  have /eqVproper[// | ltH21] := sH12; case/idPn: ubK; rewrite -leqNgt.
  have iKH1: (#|K : H2| * #|H2 : H1|)%N = #|K : H1| by apply: Lagrange_index.
  have iH21_mod1e: #|H2 : H1| == 1 %[mod e] by apply/iH1_mod1e.
  have iKH1_mod1e: #|K : H1| = 1 %[mod e] by apply/eqP/iH1_mod1e.
  have iKH2_mod1e: #|K : H2| == 1 %[mod e].
    by rewrite -iKH1_mod1e -iKH1 -modnMmr (eqP iH21_mod1e) modnMmr muln1.
  have odd_iK := dvdn_odd (dvdn_indexg _ _) (oddSg (subset_trans _ sKL) oddL).
  by rewrite -iKH1 leq_mul ?mod1e_lb ?odd_iK ?indexg_gt1 ?proper_subn.
have nMK: K \subset 'N(M) := subset_trans sKL (normal_norm nsML).
have nMK1: K^`(1)%g \subset 'N(M) by apply: gFsub_trans.
have not_abKb: ~~ abelian (K / M).
  apply: contra (proper_subn ltMH1) => /derG1P/trivgP/=.
  by rewrite join_subG subxx andbT -quotient_der ?quotient_sub1.
have /is_abelemP[p p_pr /and3P[pKb _ _]]: is_abelem (K / H1).
  have: solvable (K / H1)%g by apply: quotient_sol solK.
  by case/(minnormal_solvable (chief_factor_minnormal chiefH1)).
have [[_ p_dv_Kb _] nsMK] := (pgroup_pdiv pKb ntKb, normalS sMK sKL nsML).
have isoKb: K / M / (H1 / M) \isog K / H1 := third_isog sMH1 nsMK nsH1K.
have{nilKM} pKM: p.-group (K / M)%g.
  pose Q := 'O_p^'(K / M); have defKM: _ \x Q = _ := nilpotent_pcoreC p nilKM.
  have nH1Q: Q \subset 'N(H1 / M) by rewrite gFsub_trans ?quotient_norms.
  have hallQb := quotient_pHall nH1Q (nilpotent_pcore_Hall p^' nilKM).
  have{nH1Q hallQb pKb} sQH1: (Q \subset H1 / M)%g.
    rewrite -quotient_sub1 // subG1 trivg_card1 /= (card_Hall hallQb).
    by rewrite partG_eq1 pgroupNK (isog_pgroup p isoKb).
  suffices Q_1: Q = 1%g by rewrite -defKM Q_1 dprodg1 pcore_pgroup.
  apply: contraTeq sQH1 => ntQ; rewrite quotientYidr ?quotient_der //.
  rewrite (sameP setIidPl eqP) -(dprod_modr (der_dprod 1 defKM)) ?gFsub //= -/Q.
  rewrite setIC coprime_TIg ?(coprimeSg (der_sub 1 _)) ?coprime_pcoreC //.
  by rewrite dprod1g proper_neq ?(sol_der1_proper (nilpotent_sol nilKM)) ?gFsub.
split=> //; exists p => //; apply: contra not_abKb => e_dv_p1.
rewrite cyclic_abelian // Phi_quotient_cyclic //.
have /homgP[f <-]: (K / M / 'Phi(K / M) \homg K / H1)%g.
  apply: homg_trans (isog_hom isoKb).
  rewrite homg_quotientS ?gFnorm ?quotient_norms //= quotientYidr //.
  by rewrite quotient_der // (Phi_joing pKM) joing_subl.
rewrite {f}morphim_cyclic // abelian_rank1_cyclic; last first.
  by rewrite sub_der1_abelian ?joing_subl.
rewrite (rank_pgroup pKb) (leq_trans (p_rank_le_logn _ _)) //.
rewrite -ltnS -(ltn_exp2l _ _ (prime_gt1 p_pr)) -p_part part_pnat_id //.
rewrite card_quotient // (leq_trans ubK) // leq_exp2r //.
have odd_p: odd p by rewrite (dvdn_odd p_dv_Kb) ?quotient_odd ?(oddSg sKL).
by rewrite mod1e_lb ?eqn_mod_dvd ?prime_gt0 ?prime_gt1.
Qed.

(* This is Peterfalvi (6.6). *)
Lemma seqIndD_irr_coherence Z (calX := seqIndD K L Z 1) :
    odd_Frobenius_quotient 1 ->
    [/\ Z <| L, Z :!=: 1 & Z \subset 'Z(K)]%g ->
    {subset calX <= irr L} ->
  calX =i [pred chi in irr L | ~~ (Z \subset cfker chi)]
  /\ coherent calX L^#tau.
Proof.
move=> Frob_quo1 [nsZL ntZ sZ_ZK] irrX; have [sZL nZL] := andP nsZL.
have abZ: abelian Z by rewrite (abelianS sZ_ZK) ?center_abelian.
have /andP[sZK nZK]: Z <| K := sub_center_normal sZ_ZK.
split=> [chi|].
  apply/idP/andP=> [Xchi | [/irrP[r ->{chi}] nkerZr]].
    rewrite irrX //; case/seqIndP: Xchi => t /setIdP[nkerZt _] ->.
    by rewrite inE in nkerZt; rewrite sub_cfker_Ind_irr.
  have [t Res_r_t] := neq0_has_constt (Res_irr_neq0 K r).
  pose chi := 'Ind[L] 'chi_t; have chi_r: '[chi, 'chi_r] != 0.
    by rewrite -cfdot_Res_r cfdotC fmorph_eq0 -irr_consttE.
  have Xchi: chi \in calX.
    apply/seqIndP; exists t; rewrite // !inE sub1G andbT.
    rewrite -(sub_cfker_Ind_irr t sKL nZL).
    apply: contra nkerZr => /subset_trans-> //.
    by rewrite cfker_constt // cfInd_char ?irr_char //.
  case/irrX/irrP: Xchi chi_r (Xchi) => r' ->.
  by rewrite cfdot_irr pnatr_eq0 -lt0n; case: eqP => // ->.
apply: non_coherent_chief (subset_coherent (seqInd_sub sZK)) _ => //= -[_ [p]].
have [oddL _] := Frob_quo1; rewrite joingG1 -/calX => frobLb [].
rewrite -(isog_pgroup p (quotient1_isog K)) => pK ab'K.
set e := #|L : K| => not_e_dv_p1; have e_gt0: (e > 0)%N by apply: indexg_gt0.
have ntK: K != 1%G by apply: contraNneq ab'K => ->; rewrite quotient1 abelian1.
have{ab'K ntK} [p_pr p_dv_K _] := pgroup_pdiv pK ntK.
set Y := calX; pose d (xi : 'CF(L)) := logn p (truncC (xi 1%g) %/ e).
have: cfConjC_closed Y by apply: cfAut_seqInd.
have: perm_eq (Y ++ [::]) calX by rewrite cats0.
have: {in Y & [::], forall xi1 xi2, d xi1 <= d xi2}%N by [].
elim: {Y}_.+1 {-2}Y [::] (ltnSn (size Y)) => // m IHm Y X' leYm leYX' defX ccY.
have sYX: {subset Y <= calX}.
  by move=> xi Yxi; rewrite -(perm_eq_mem defX) mem_cat Yxi.
have sX'X: {subset X' <= calX}.
  by move=> xi X'xi; rewrite -(perm_eq_mem defX) mem_cat X'xi orbT.
have uniqY: uniq Y.
  have: uniq calX := seqInd_uniq L _.
  by rewrite -(perm_eq_uniq defX) cat_uniq => /and3P[].
have sYS: {subset Y <= calS} by move=> xi /sYX/seqInd_sub->.
case homoY: (constant [seq xi 1%g | xi : 'CF(L) <- Y]).
  exact: uniform_degree_coherence (subset_subcoherent scohS _) homoY.
have Ndg: {in calX, forall xi : 'CF(L), xi 1%g = (e * p ^ d xi)%:R}.
  rewrite /d => _ /seqIndP[i _ ->]; rewrite cfInd1 // -/e.
  have:= dvd_irr1_cardG i; have /CnatP[n ->] := Cnat_irr1 i.
  rewrite -natrM natCK dvdC_nat mulKn // -p_part => dv_n_K.
  by rewrite part_pnat_id // (pnat_dvd dv_n_K).
have [chi Ychi leYchi]: {chi | chi \in Y & {in Y, forall xi, d xi <= d chi}%N}.
  have [/eqP/nilP Y0 | ntY] := posnP (size Y); first by rewrite Y0 in homoY.
  pose i := [arg max_(i > Ordinal ntY) d Y`_i].
  exists Y`_i; [exact: mem_nth | rewrite {}/i; case: arg_maxP => //= i _ max_i].
  by move=> _ /(nthP 0)[j ltj <-]; apply: (max_i (Ordinal ltj)).
have{homoY} /hasP[xi1 Yxi1 lt_xi1_chi]: has (fun xi => d xi < d chi)%N Y.
  apply: contraFT homoY => geYchi; apply: (@all_pred1_constant _ (chi 1%g)).
  rewrite all_map; apply/allP=> xi Yxi; rewrite /= !Ndg ?sYX // eqr_nat.
  rewrite eqn_pmul2l // eqn_exp2l ?prime_gt1 //.
  by rewrite eqn_leq leYchi //= leqNgt (hasPn geYchi).
pose Y' := rem chi^*%CF (rem chi Y); pose X'' := [:: chi, chi^*%CF & X'].
have ccY': cfConjC_closed Y'.
  move=> xi; rewrite !(inE, mem_rem_uniq) ?rem_uniq //.
  by rewrite !(inv_eq (@cfConjCK _ _)) cfConjCK => /and3P[-> -> /ccY->].
have Xchi := sYX _ Ychi; have defY: perm_eq [:: chi, chi^*%CF & Y'] Y.
  rewrite (perm_eqrP (perm_to_rem Ychi)) perm_cons perm_eq_sym perm_to_rem //.
  by rewrite mem_rem_uniq ?inE ?ccY // (seqInd_conjC_neq _ _ _ Xchi).
apply: perm_eq_coherent (defY) _.
have d_chic: d chi^*%CF = d chi.
  by rewrite /d cfunE conj_Cnat // (Cnat_seqInd1 Xchi).
have /and3P[uniqY' Y'xi1 notY'chi]: [&& uniq Y', xi1 \in Y' & chi \notin Y'].
  rewrite !(inE, mem_rem_uniq) ?rem_uniq // Yxi1 eqxx andbF !andbT -negb_or.
  by apply: contraL lt_xi1_chi => /pred2P[] ->; rewrite ?d_chic ltnn.
have sY'Y: {subset Y' <= Y} by move=> xi /mem_rem/mem_rem.
have sccY'S: cfConjC_subset Y' calS by split=> // xi /sY'Y/sYS.
apply: (extend_coherent scohS _ Y'xi1); rewrite ?sYS {sccY'S notY'chi}//.
have{defX} defX: perm_eq (Y' ++ X'') calX.
  by rewrite (perm_catCA Y' [::_; _]) catA -(perm_eqrP defX) perm_cat2r.
have{d_chic} le_chi_X'': {in X'', forall xi, d chi <= d xi}%N.
  by move=> xi /or3P[/eqP-> | /eqP-> | /leYX'->] //; rewrite d_chic.
rewrite !Ndg ?sYX // dvdC_nat dvdn_pmul2l // dvdn_exp2l 1?ltnW //; split=> //.
  apply: IHm defX ccY' => [|xi xi' /sY'Y/leYchi-le_xi_chi /le_chi_X''].
    by rewrite -ltnS // (leq_trans _ leYm) // -(perm_eq_size defY) ltnW.
  exact: leq_trans.
have p_gt0 n: (0 < p ^ n)%N by rewrite expn_gt0 prime_gt0.
rewrite -!natrM; apply: (@ltr_le_trans _ (e ^ 2 * (p ^ d chi) ^ 2)%:R).
  rewrite ltr_nat -expnMn -mulnn mulnAC !mulnA 2?ltn_pmul2r //.
  rewrite -mulnA mulnCA ltn_pmul2l // -(subnK lt_xi1_chi) addnS expnS.
  rewrite expnD mulnA ltn_pmul2r // -(muln1 3) leq_mul //.
  rewrite ltn_neqAle prime_gt1 // eq_sym (sameP eqP (prime_oddPn p_pr)).
  by rewrite (dvdn_odd p_dv_K) // (oddSg sKL).
have [r] := seqIndP (sYX _ Ychi); rewrite !inE => /andP[nkerZr _] def_chi.
have d_r: 'chi_r 1%g = (p ^ d chi)%:R.
  by apply: (mulfI (neq0CiG L K)); rewrite -cfInd1 // -def_chi -natrM Ndg.
pose sum_p2d S := (\sum_(xi <- S) p ^ (d xi * 2))%N.
pose sum_xi1 (S : seq 'CF(L)) := \sum_(xi <- S) xi 1%g ^+ 2 / '[xi].
have def_sum_xi1 S: {subset S <= calX} -> sum_xi1 S = (e ^ 2 * sum_p2d S)%:R.
  move=> sSX; rewrite big_distrr natr_sum /=; apply: eq_big_seq => xi /sSX Xxi.
  rewrite expnM -expnMn natrX -Ndg //.
  by have /irrP[i ->] := irrX _ Xxi; rewrite cfnorm_irr divr1.
rewrite -/(sum_xi1 _) def_sum_xi1 ?leC_nat 1?dvdn_leq => [|||_ /sY'Y/sYX] //.
  by rewrite muln_gt0 expn_gt0 e_gt0 [_ Y'](bigD1_seq xi1) //= addn_gt0 p_gt0.
have coep: coprime e p.
  have:= Frobenius_ker_coprime frobLb; rewrite coprime_sym.
  have /andP[_ nK'L]: K^`(1) <| L by apply: gFnormal_trans.
  rewrite index_quotient_eq ?subIset ?der_sub ?orbT {nK'L}// -/e.
  have ntKb: (K / K^`(1))%g != 1%g by case/Frobenius_kerP: frobLb.
  have [_ _ [k ->]] := pgroup_pdiv (quotient_pgroup _ pK) ntKb.
  by rewrite coprime_pexpr.
rewrite -expnM Gauss_dvd ?coprime_expl ?coprime_expr {coep}// dvdn_mulr //=.
have /dvdn_addl <-: p ^ (d chi * 2) %| e ^ 2 * sum_p2d X''.
  rewrite big_distrr big_seq dvdn_sum //= => xi /le_chi_X'' le_chi_xi.
  by rewrite dvdn_mull // dvdn_exp2l ?leq_pmul2r.
rewrite -mulnDr -big_cat (eq_big_perm _ defX) -(natCK (e ^ 2 * _)) /=.
rewrite -def_sum_xi1 // /sum_xi1 sum_seqIndD_square ?normal1 ?sub1G //.
rewrite indexg1 -(natrB _ (cardG_gt0 Z)) -natrM natCK.
rewrite -(Lagrange_index sKL sZK) mulnAC dvdn_mull //.
have /p_natP[k defKZ]: p.-nat #|K : Z| by rewrite (pnat_dvd (dvdn_indexg K Z)).
rewrite defKZ dvdn_exp2l // -(leq_exp2l _ _ (prime_gt1 p_pr)) -{k}defKZ.
rewrite -leC_nat expnM natrX -d_r ?(ler_trans (irr1_bound r).1) //.
rewrite ler_nat dvdn_leq ?indexgS ?(subset_trans sZ_ZK) //=.
by rewrite -cap_cfcenter_irr bigcap_inf.
Qed.

End GeneralCoherence.

(* This is Peterfalvi (6.7). *)
(* In (6.8) we only know initially the P group is Sylow in L; perhaps this    *)
(* lemma should be stated with this equivalent (but weaker) assumption.       *)
Lemma constant_irr_mod_TI_Sylow Z L P p i :
     p.-Sylow(G) P -> odd #|L| -> normedTI P^# G L ->
     [/\ Z <| L, Z :!=: 1%g & Z \subset 'Z(P)] ->
     {in Z^# &, forall x y, #|'C_L[x]| = #|'C_L[y]| } ->
     let phi := 'chi[G]_i in
     {in Z^# &, forall x y, phi x = phi y} ->
   {in Z^#, forall x, phi x \in Cint /\ (#|P| %| phi x - phi 1%g)%C}.
Proof.
move=> sylP oddL tiP [/andP[sZL nZL] ntZ sZ_ZP] prZL; move: i.
pose a := @gring_classM_coef _ G; pose C (i : 'I_#|classes G|) := enum_val i.
have [[sPG pP p'PiG] [sZP cPZ]] := (and3P sylP, subsetIP sZ_ZP).
have [ntP sLG memJ_P1] := normedTI_memJ_P tiP; rewrite setD_eq0 subG1 in ntP.
have nsPL: P <| L.
  by have [_ _ /eqP<-] := and3P tiP; rewrite normD1 normal_subnorm.
have [p_pr _ [e oP]] := pgroup_pdiv pP ntP.
have [sZG [sPL _]] := (subset_trans sZP sPG, andP nsPL).
pose dC i (A : {set gT}) := [disjoint C i & A].
have actsGC i: {acts G, on C i | 'J}.
  apply/actsP; rewrite astabsJ /C; have /imsetP[x _ ->] := enum_valP i.
  by apply/normsP; apply: classGidr.
have{actsGC} PdvKa i j s:
  ~~ dC i Z^# -> ~~ dC j Z^# -> dC s Z -> (#|P| %| a i j s * #|C s|)%N.
- pose Omega := [set uv in [predX C i & C j] | mulgm uv \in C s]%g.
  pose to_fn uv x := prod_curry (fun u v : gT => (u ^ x, v ^ x)%g) uv.
  have toAct: is_action setT to_fn.
    by apply: is_total_action => [[u v]|[u v] x y] /=; rewrite ?conjg1 ?conjgM.
  move=> Zi Zj Z's; pose to := Action toAct.
  have actsPO: [acts P, on Omega | to].
    apply/(subset_trans sPG)/subsetP=> x Gx; rewrite !inE.
    apply/subsetP=> [[u v] /setIdP[/andP/=[Ciu Cjv] Csuv]].
    by rewrite !inE /= -conjMg !actsGC // Ciu Cjv.
  have <-: #|Omega| = (a i j s * #|C s|)%N.
    have /repr_classesP[_ defCs] := enum_valP s; rewrite -/(C s) in defCs.
    rewrite -sum1_card mulnC -sum_nat_const.
    rewrite (partition_big mulgm (mem (C s))) => [|[u v] /setIdP[]//].
    apply: eq_bigr; rewrite /= defCs => _ /imsetP[z Gz ->].
    rewrite -[a i j s]sum1_card -!/(C _) (reindex_inj (act_inj to z)) /=.
    apply: eq_bigl => [[u v]]; rewrite !inE /= -conjMg (inj_eq (conjg_inj _)).
    by apply: andb_id2r => /eqP->; rewrite {2}defCs mem_imset ?andbT ?actsGC.
  suffices regPO: {in Omega, forall uv, 'C_P[uv | to] = 1%g}.
    rewrite -(acts_sum_card_orbit actsPO) dvdn_sum // => _ /imsetP[uv Ouv ->].
    by rewrite card_orbit regPO // indexg1.
  case=> u v /setIdP[/andP[/= Ciu Cjv] Csuv]; apply: contraTeq Z's.
  case/trivgPn=> x /setIP[Px /astab1P[/= cux cvx]] nt_x.
  suffices inZ k y: y \in C k -> ~~ dC k Z^# -> y ^ x = y -> y \in Z.
    apply/exists_inP; exists (u * v)%g => //=.
    by rewrite groupM // (inZ i u, inZ j v).
  rewrite /dC /C; have /imsetP[_ _ ->{k} /class_eqP <-] := enum_valP k.
  case/exists_inP=> _ /imsetP[g Gg ->] /setD1P[nt_yg Zyg] yx.
  have xy: (x ^ y = x)%g by rewrite /conjg (conjgCV x) -{2}yx conjgK mulKg.
  rewrite -(memJ_conjg _ g) (normsP nZL) //.
  rewrite -(memJ_P1 y) ?inE //=; first by rewrite nt_yg (subsetP sZP).
  rewrite -order_eq1 -(orderJ y g) order_eq1 nt_yg.
  rewrite (mem_normal_Hall (pHall_subl sPL sLG sylP)) //.
    by rewrite -(p_eltJ _ _ g) (mem_p_elt pP) ?(subsetP sZP).
  rewrite -(memJ_P1 x) // ?xy ?inE ?nt_x // -[y](conjgK g) groupJ ?groupV //.
  by rewrite (subsetP sZG).
pose a2 i j := (\sum_(s | ~~ dC s Z^#) a i j s)%N.
pose kerZ l := {in Z^# &, forall x y, 'chi[G]_l x = 'chi_l y}.
move=> l phi kerZl z Z1z; move: l @phi {kerZl}(kerZl : kerZ l).
have [ntz Zz] := setD1P Z1z.
have [[Pz Lz] Gz] := (subsetP sZP z Zz, subsetP sZL z Zz, subsetP sZG z Zz).
pose inC y Gy := enum_rank_in (@mem_classes _ y G Gy) (y ^: G).
have CE y Gy: C (inC y Gy) = y ^: G by rewrite /C enum_rankK_in ?mem_classes.
pose i0 := inC _ (group1 G); pose i1 := inC z Gz; pose i2 := inC _ (groupVr Gz).
suffices Ea2 l (phi := 'chi[G]_l) (kerZphi : kerZ l):
  (phi z *+ a2 i1 i1 == phi 1%g + phi z *+ a2 i1 i2 %[mod #|P|])%A.
- move=> l phi kerZphi.
  have Zphi1: phi 1%g \in Cint by rewrite irr1_degree rpred_nat.
  have chi0 x: x \in Z -> 'chi[G]_0 x = 1.
    by rewrite irr0 cfun1E => /(subsetP sZG) ->.
  have: kerZ 0 by move=> x y /setD1P[_ Zx] /setD1P[_ Zy]; rewrite !chi0.
  move/Ea2/(eqAmodMl (Aint_irr l z)); rewrite !{}chi0 // -/phi eqAmod_sym.
  rewrite mulrDr mulr1 !mulr_natr => /eqAmod_trans/(_ (Ea2 l kerZphi)).
  rewrite eqAmodDr -/phi eqAmod_rat ?rpred_nat ?(rpred_Cint _ Zphi1) //.
    move=> PdvDphi; split; rewrite // -[phi z](subrK (phi 1%g)) rpredD //.
    by have /dvdCP[b Zb ->] := PdvDphi; rewrite rpredM ?rpred_nat.
  have nz_Z1: #|Z^#|%:R != 0 :> algC.
    by rewrite pnatr_eq0 cards_eq0 setD_eq0 subG1.
  rewrite -[phi z](mulfK nz_Z1) rpred_div ?rpred_nat // mulr_natr.
  rewrite -(rpredDl _ (rpred_Cint _ Zphi1)) //.
  rewrite -[_ + _](mulVKf (neq0CG Z)) rpredM ?rpred_nat //.
  have: '['Res[Z] phi, 'chi_0] \in Crat.
    by rewrite rpred_Cnat ?Cnat_cfdot_char ?cfRes_char ?irr_char.
  rewrite irr0 cfdotE (big_setD1 _ (group1 Z)) cfun1E cfResE ?group1 //=.
  rewrite rmorph1 mulr1; congr (_ * (_ + _) \in Crat).
  rewrite -sumr_const; apply: eq_bigr => x Z1x; have [_ Zx] := setD1P Z1x.
  by rewrite cfun1E cfResE ?Zx // rmorph1 mulr1; apply: kerZphi.
pose alpha := 'omega_l['K_i1]; pose phi1 := phi 1%g.
have tiZG: {in Z^#, forall y, 'C_G[y] \subset L}.
  move=> y /setD1P[nty /(subsetP sZP)Py].
  apply/subsetP=> u /setIP[Gu /cent1P-cuy].
  by rewrite -(memJ_P1 y) // /conjg -?cuy ?mulKg !inE nty.
have Dalpha s: ~~ dC s Z^# -> alpha = 'omega_l['K_s].
  case/exists_inP=> x /= /gring_mode_class_sum_eq-> Z1x.
  have Ci1z: z \in C i1 by rewrite CE class_refl.
  rewrite [alpha](gring_mode_class_sum_eq _ Ci1z) -/phi (kerZphi z x) //.
  have{tiZG} tiZG: {in Z^#, forall y, 'C_G[y] = 'C_L[y]}.
    by move=> y /tiZG/setIidPr; rewrite setIA (setIidPl sLG).
  by rewrite -!index_cent1 -!divgS ?subsetIl //= !tiZG ?(prZL z x).
have Ci01: 1%g \in C i0 by rewrite CE class_refl.
have rCi10: repr (C i0) = 1%g by rewrite CE class1G repr_set1.
have Dalpha2 i j: ~~ dC i Z^# ->  ~~ dC j Z^# ->
  (phi1 * alpha ^+ 2 == phi1 * ((a i j i0)%:R + alpha *+ a2 i j) %[mod #|P|])%A.
- move=> Z1i Z1j.
  have ->: phi1 * alpha ^+ 2 = \sum_s (phi1 *+ a i j s) * 'omega_l['K_s].
    rewrite expr2 {1}(Dalpha i Z1i) (Dalpha j Z1j).
    rewrite -gring_irr_modeM ?gring_class_sum_central //.
    rewrite gring_classM_expansion raddf_sum mulr_sumr; apply: eq_bigr => s _.
    by rewrite scaler_nat raddfMn mulrnAl mulrnAr.
  rewrite (bigID (fun s => dC s Z^#)) (bigD1 i0) //=; last first.
    by rewrite [dC _ _]disjoints_subset CE class1G sub1set !inE eqxx.
  rewrite (gring_mode_class_sum_eq _ Ci01) mulfK ?irr1_neq0 //.
  rewrite class1G cards1 mulr1 mulrDr mulr_natr -addrA eqAmodDl.
  rewrite /eqAmod -addrA rpredD //; last first.
    rewrite -mulr_natr natr_sum !mulr_sumr -sumrB rpred_sum // => s Z1s.
    by rewrite -Dalpha // mulr_natr mulrnAl mulrnAr subrr rpred0.
  apply: rpred_sum => // s /andP[Z1'Cs ntCs]; rewrite mulrnAl mulrC.
  have /imsetP[x _ defCs] := enum_valP s.
  have Cs_x: x \in C s by rewrite /C defCs class_refl.
  rewrite (gring_mode_class_sum_eq _ Cs_x) divfK ?irr1_neq0 // -defCs -/(C s).
  rewrite -mulrnAl -mulrnA mulnC -[_%:R]subr0 mulrBl.
  apply: eqAmodMr; first exact: Aint_irr.
  rewrite eqAmod0_rat ?rpred_nat // dvdC_nat PdvKa //.
  rewrite -(setD1K (group1 Z)) [dC _ _]disjoint_sym disjoints_subset.
  rewrite subUset sub1set inE -disjoints_subset disjoint_sym.
  rewrite (contra _ ntCs) // [C s]defCs => /class_eqP.
  by rewrite -(inj_eq enum_val_inj) defCs -/(C _) CE => ->.
have zG'z1: (z^-1 \notin z ^: G)%g.
  have genL2 y: y \in L -> <[y]> = <[y ^+ 2]>.
    move=> Ly; apply/eqP; rewrite [_ == _]generator_coprime.
    by rewrite coprime_sym prime_coprime // dvdn2 (oddSg _ oddL) ?cycle_subG.
  apply: contra (ntz) => /imsetP[y Gy zy].
  have cz_y2: (y ^+ 2 \in 'C[z])%g.
    by rewrite !inE conjg_set1 conjgM -zy conjVg -zy invgK.
  rewrite -cycle_eq1 genL2 // cycle_eq1 -eq_invg_mul zy (sameP eqP conjg_fixP).
  rewrite (sameP commgP cent1P) cent1C -cycle_subG genL2 ?cycle_subG //.
  by rewrite -(memJ_P1 z) -?zy ?in_setD ?groupV ?inE ?ntz.
have a110: a i1 i1 i0 = 0%N.
  apply: contraNeq zG'z1 => /existsP[[u v] /setIdP[/andP[/=]]].
  rewrite rCi10 -!/(C _) !CE -eq_invg_mul => /imsetP[x Gx ->] /class_eqP <-.
  by move/eqP <-; rewrite -conjVg classGidl ?class_refl.
have a120: a i1 i2 i0 = #|C i1|.
  rewrite -(card_imset _ (@can_inj _ _ (fun y => (y, y^-1)%g) (@fst _ _) _)) //.
  apply/eq_card=> [[u v]]; rewrite !inE rCi10 -eq_invg_mul -!/(C _) !CE -andbA.
  apply/and3P/imsetP=> /= [[zGu _ /eqP<-] | [y zGy [-> ->]]]; first by exists u.
  by rewrite classVg inE invgK.
have Z1i1: ~~ dC i1 Z^#.
  by apply/exists_inP; exists z; rewrite //= CE class_refl.
have Z1i2: ~~ dC i2 Z^#.
  apply/exists_inP; exists z^-1%g; first by rewrite /= CE class_refl.
  by rewrite /= in_setD !groupV !inE ntz.
have{Dalpha2}: (phi1 * (alpha *+ a2 i1 i1)
                  == phi1 * (#|C i1|%:R + alpha *+ a2 i1 i2) %[mod #|P|])%A.
- rewrite -a120; apply: eqAmod_trans (Dalpha2 i1 i2 Z1i1 Z1i2).
  by have:= Dalpha2 _ _ Z1i1 Z1i1; rewrite a110 add0r eqAmod_sym.
rewrite mulrDr !mulrnAr mulr1 -/phi1.
have ->: phi1 * alpha = phi z *+ #|C i1|.
  have Ci1z: z \in C i1 by rewrite CE class_refl.
  rewrite [alpha](gring_mode_class_sum_eq _ Ci1z) mulrC divfK ?irr1_neq0 //.
  by rewrite mulr_natl CE.
rewrite -!mulrnA !(mulnC #|C _|) !mulrnA -mulrnDl.
have [|r _ /dvdnP[q Dqr]] := @Bezoutl #|C i1| #|P|.
  by rewrite CE -index_cent1.
have Zq: q%:R \in Aint by apply: rpred_nat.
move/(eqAmodMr Zq); rewrite ![_ *+ #|C _| * _]mulrnAl -!mulrnAr -mulrnA -Dqr.
have /eqnP->: coprime #|C i1| #|P|.
  rewrite (p'nat_coprime _ pP) // (pnat_dvd _ p'PiG) // CE -index_cent1.
  by rewrite indexgS // subsetI sPG sub_cent1 (subsetP cPZ).
rewrite add1n !mulrS !mulrDr !mulr1 natrM !mulrA.
set u := _ * r%:R; set v := _ * r%:R; rewrite -[u](subrK v) mulrDl addrA.
rewrite eqAmodDr; apply: eqAmod_trans; rewrite eqAmod_sym addrC.
rewrite eqAmod_addl_mul // -mulrBl mulr_natr.
by rewrite !(rpredB, rpredD, rpredMn, Aint_irr).
Qed.

(* This is Peterfalvi, Theorem (6.8). *)
(* We omit the semi-direct structure of L in assumption (a), since it is      *)
(* implied by our statement of assumption (c).                                *)
Theorem Sibley_coherence L H W1 :
  (*a*) [/\ odd #|L|, nilpotent H & normedTI H^# G L] ->
  (*b*) let calS := seqIndD H L H 1 in let tau := 'Ind[G, L] in
  (*c*) [\/ (*c1*) [Frobenius L = H ><| W1]
         |  (*c2*) exists2 W2 : {group gT}, prime #|W2| /\ W2 \subset H^`(1)%G
               & exists A0, exists W : {group gT}, exists defW : W1 \x W2 = W,
                 prime_Dade_hypothesis G L H H H^# A0 defW] ->
  coherent calS L^# tau.
Proof.
set case_c1 := [Frobenius L = H ><| W1]; pose case_c2 := ~~ case_c1.
set A := H^#; set H' := H^`(1)%G => -[oddL nilH tiA] S tau hyp_c.
have sLG: L \subset G by have [] := normedTI_memJ_P tiA.
have ntH: H :!=: 1%g by have [] := normedTI_P tiA; rewrite setD_eq0 subG1.
have [defL ntW1]: H ><| W1 = L /\ W1 :!=: 1%g.
  by have [/Frobenius_context[] | [? _ [? [? [? [_ [[]]]]]]]] := hyp_c.
have [nsHL _ /mulG_sub[sHL sW1L] _ _] := sdprod_context defL.
have [uccS nrS]: cfConjC_subset S S /\ ~~ has cfReal S.
  by do 2?split; rewrite ?seqInd_uniq ?seqInd_notReal //; apply: cfAut_seqInd.
have defZS: 'Z[S, L^#] =i 'Z[S, A] by apply: zcharD1_seqInd.
have c1_irrS: case_c1 -> {subset S <= irr L}.
  move/FrobeniusWker=> frobL _ /seqIndC1P[i nz_i ->].
  exact: irr_induced_Frobenius_ker.
move defW2: 'C_H(W1)%G => W2; move defW: (W1 <*> W2)%G => W.
have{defW} defW: W1 \x W2 = W.
  rewrite -defW dprodEY // -defW2 ?subsetIr // setICA setIA.
  by have [_ _ _ ->] := sdprodP defL; rewrite setI1g.
pose V := cyclicTIset defW; pose A0 := A :|: class_support V L.
pose ddA0hyp := prime_Dade_hypothesis G L H H A A0 defW.
have c1W2: case_c1 -> W2 = 1%G by move/Frobenius_trivg_cent/group_inj <-.
have{hyp_c} hyp_c2: case_c2 -> [/\ prime #|W2|, W2 \subset H' & ddA0hyp].
  case: hyp_c => [/idPn// | [W2_ [prW2_ sW2_H'] [A0_ [W_ [defW_ ddA0_]]]] _].
  have idW2_: W2_ = W2.
    have [[_ _ _ /cyclicP[x defW1]] [_ _ _ prW12] _] := prDade_prTI ddA0_.
    have W1x: x \in W1^# by rewrite !inE -cycle_eq1 -defW1 ntW1 defW1 cycle_id.
    by apply/group_inj; rewrite -defW2 /= defW1 cent_cycle prW12.
  have idW_: W_ = W by apply/group_inj; rewrite -defW_ idW2_.
  rewrite {}/ddA0hyp {}/A0 {}/V; rewrite -idW2_ -idW_ in defW *.
  by rewrite (eq_irrelevance defW defW_); have [_ _ <-] := prDade_def ddA0_.
have{hyp_c2} [c2_prW2 c2_sW2H' c2_ddA0] := all_and3 hyp_c2.
have c2_ptiL c2 := prDade_prTI (c2_ddA0 c2).
have{c2_sW2H'} sW2H': W2 \subset H'.
  by have [/c1W2-> | /c2_sW2H'//] := boolP case_c1; apply: sub1G.
pose sigma c2 := cyclicTIiso (c2_ddA0 c2).
have [R scohS oRW]: exists2 R, subcoherent S tau R & forall c2 : case_c2,
  {in [predI S & irr L] & irr W, forall phi w, orthogonal (R phi) (sigma c2 w)}.
- have sAG: A \subset G^# by rewrite setSD // (subset_trans sHL).
  have Itau: {in 'Z[S, L^#], isometry tau, to 'Z[irr G, G^#]}.
    split=> [xi1 xi2|xi]; first rewrite !defZS => /zchar_on-Axi1 /zchar_on-Axi2.
      exact: normedTI_isometry Axi1 Axi2.
    rewrite !zcharD1E cfInd1 // => /andP[Zxi /eqP->]; rewrite mulr0.
    by rewrite cfInd_vchar ?(zchar_trans_on _ Zxi) //=; apply: seqInd_vcharW.
  have [/= c1 | /c2_ddA0-ddA0] := boolP (idfun case_c1).
    suffices [R scohS]: {R | subcoherent S tau R} by exists R => // /negP[].
    by apply: irr_subcoherent; first have [[]] := (uccS, c1_irrS c1).
  have Dtau: {in 'CF(L, A), tau =1 Dade ddA0}.
    have nAL: L \subset 'N(A) by have [_ /subsetIP[]] := normedTI_P tiA.
    have sAA0: A \subset A0 by apply: subsetUl.
    by move=> phi Aphi /=; rewrite -(restr_DadeE _ sAA0) // [RHS]Dade_Ind.
  have [R [subcohR oRW _]] := prDade_subcoherent ddA0 uccS nrS.
  exists R => [|c2 phi w irrSphi irr_w]; last first.
    by rewrite /sigma -(cycTIiso_irrel ddA0) oRW.
  have [Sok _ oSS Rok oRR] := subcohR; split=> {Sok oSS oRR}// phi Sphi.
  have [ZR oNR <-] := Rok _ Sphi; split=> {ZR oNR}//.
  exact/Dtau/(zchar_on (seqInd_sub_aut_zchar _ _ Sphi)).
have solH := nilpotent_sol nilH; have nsH'H: H' <| H := der_normal 1 H.
have ltH'H: H' \proper H by rewrite (sol_der1_proper solH).
have nsH'L: H' <| L by apply: gFnormal_trans.
have [sH'H [sH'L nH'L]] := (normal_sub nsH'H, andP nsH'L).
have coHW1: coprime #|H| #|W1|.
  suffices: Hall L W1 by rewrite (coprime_sdprod_Hall_r defL).
  by have [/Frobenius_compl_Hall | /c2_ddA0/prDade_prTI[[]]] := boolP case_c1.
have oW1: #|W1| = #|L : H| by rewrite (index_sdprod defL).
have frobL1: [Frobenius L / H' = (H / H') ><| (W1 / H')].
  apply: (Frobenius_coprime_quotient defL nsH'L) => //; split=> // x W1x.
  have [frobL | /c2_ptiL[_ [_ _ _ -> //]]] := boolP case_c1.
  by rewrite (Frobenius_reg_ker frobL) ?sub1G.
have odd_frobL1: odd_Frobenius_quotient H L 1.
  split=> //=; last by rewrite joingG1 (FrobeniusWker frobL1).
  by rewrite normal1 sub1G quotient_nil.
without loss [/p_groupP[p p_pr pH] not_cHH]: / p_group H /\ ~~ abelian H.
  apply: (non_coherent_chief _ _ scohS odd_frobL1) => // -[_ [p [pH ab'H] _]].
  have isoH := quotient1_isog H; rewrite -(isog_pgroup p isoH) in pH.
  by apply; rewrite (isog_abelian isoH) (pgroup_p pH).
have sylH: p.-Sylow(G) H. (* required for (6.7) *)
  rewrite -Sylow_subnorm -normD1; have [_ _ /eqP->] := and3P tiA.
  by apply/and3P; rewrite -oW1 -pgroupE (coprime_p'group _ pH) // coprime_sym.
pose caseA := 'Z(H) :&: W2 \subset [1]%g; pose caseB := ~~ caseA.
have caseB_P: caseB -> [/\ case_c2, W2 :!=: 1%g & W2 \subset 'Z(H)].
  rewrite /caseB /caseA; have [->|] := eqP; first by rewrite subsetIr.
  rewrite /case_c2; have [/c1W2->// | /c2_prW2-prW2 _] := boolP case_c1.
  by rewrite setIC subG1 => /prime_meetG->.
pose Z := (if caseA then 'Z(H) :&: H' else W2)%G.
have /subsetIP[sZZH sZH']: Z \subset 'Z(H) :&: H'.
  by rewrite /Z; case: ifPn => // /caseB_P[_ _ sZZH]; apply/subsetIP.
have caseB_sZZL: caseB -> Z \subset 'Z(L).
  move=> in_caseB; have [_ _ /subsetIP[sW2H cW2H]] := caseB_P in_caseB.
  rewrite /Z ifN // subsetI (subset_trans sW2H sHL).
  by rewrite -(sdprodW defL) centM subsetI cW2H -defW2 subsetIr.
have nsZL: Z <| L; last have [sZL nZL] := andP nsZL.
  have [in_caseA | /caseB_sZZL/sub_center_normal//] := boolP caseA.
  by rewrite /Z in_caseA normalI ?gFnormal_trans.
have ntZ: Z :!=: 1%g.
  rewrite /Z; case: ifPn => [_ | /caseB_P[] //].
  by rewrite /= setIC meet_center_nil // (sameP eqP derG1P).
have nsZH: Z <| H := sub_center_normal sZZH; have [sZH nZH] := andP nsZH.
have regZL: {in Z^# &, forall x y, #|'C_L[x]| = #|'C_L[y]| }.
  have [in_caseA | /caseB_sZZL/subsetIP[_ cZL]] := boolP caseA; last first.
    suffices defC x: x \in Z^# -> 'C_L[x] = L by move=> x y /defC-> /defC->.
    by case/setD1P=> _ /(subsetP cZL); rewrite -sub_cent1 => /setIidPl.
  suffices defC x: x \in Z^# -> 'C_L[x] = H by move=> x y /defC-> /defC->.
  case/setD1P=> ntx Zx; have /setIP[Hx cHx] := subsetP sZZH x Zx.
  have [_ <- _ _] := sdprodP defL; rewrite -group_modl ?sub_cent1 //=.
  suffices ->: 'C_W1[x] = 1%g by rewrite mulg1.
  have [/Frobenius_reg_compl-> // | c2] := boolP case_c1; first exact/setD1P.
  have [_ [_ _ _ regW1] _] := c2_ptiL c2.
  apply: contraTeq in_caseA => /trivgPn[y /setIP[W1y cxy] nty]; apply/subsetPn.
  by exists x; rewrite inE // -(regW1 y) 2!inE ?nty // Hx cHx cent1C.
have{regZL} irrZmodH :=
  constant_irr_mod_TI_Sylow sylH oddL tiA (And3 nsZL ntZ sZZH) regZL.
pose X := seqIndD H L Z 1; pose Y := seqIndD H L H H'.
have ccsXS: cfConjC_subset X S by apply: seqInd_conjC_subset1.
have ccsYS: cfConjC_subset Y S by apply: seqInd_conjC_subset1.
have [[uX sXS ccX] [uY sYS ccY]] := (ccsXS, ccsYS).
have X'Y: {subset Y <= [predC X]}.
  move=> _ /seqIndP[i /setIdP[_ kH'i] ->]; rewrite inE in kH'i.
  by rewrite !inE mem_seqInd ?normal1 // !inE (subset_trans sZH').
have oXY: orthogonal X Y.
  apply/orthogonalP=> xi eta Xxi Yeta; apply: orthoPr xi Xxi.
  exact: (subset_ortho_subcoherent scohS sXS (sYS _ Yeta) (X'Y _ Yeta)).
have irrY: {subset Y <= irr L}.
  move=> _ /seqIndP[i /setIdP[not_kHi kH'i] ->]; rewrite !inE in not_kHi kH'i.
  rewrite -(cfQuo_irr nsH'L) ?sub_cfker_Ind_irr -?cfIndQuo -?quo_IirrE //.
  apply: (irr_induced_Frobenius_ker (FrobeniusWker frobL1)).
  by rewrite quo_Iirr_eq0 -?subGcfker.
have oY: orthonormal Y by apply: sub_orthonormal (irr_orthonormal L).
have uniY: {in Y, forall phi : 'CF(L), phi 1%g = #|W1|%:R}.
  move=> _ /seqIndP[i /setIdP[_ kH'i] ->]; rewrite inE -lin_irr_der1 in kH'i.
  by rewrite cfInd1 // -divgS // -(sdprod_card defL) mulKn // lin_char1 ?mulr1.
have scohY: subcoherent Y tau R by apply: (subset_subcoherent scohS).
have [tau1 cohY]: coherent Y L^# tau.
  apply/(uniform_degree_coherence scohY)/(@all_pred1_constant _ #|W1|%:R).
  by apply/allP=> _ /mapP[phi Yphi ->]; rewrite /= uniY.
have [[Itau1 Ztau1] Dtau1] := cohY.
have oYtau: orthonormal (map tau1 Y) by apply: map_orthonormal.
have [[_ oYY] [_ oYYt]] := (orthonormalP oY, orthonormalP oYtau).
have [eta1 Yeta1]: {eta1 | eta1 \in Y} by apply: seqIndD_nonempty.
pose m : algC := (size Y)%:R; pose m_ub2 a := (a - 1) ^+ 2 + (m - 1) * a ^+ 2.
have m_ub2_lt2 a: a \in Cint -> m_ub2 a < 2%:R -> a = 0 \/ a = 1 /\ size Y = 2.
  move=> Za ub_a; have [|nza] := eqVneq a 0; [by left | right].
  have ntY: (1 < size Y)%N by apply: seqInd_nontrivial Yeta1.
  have m1_ge1: 1 <= m - 1 by rewrite ler_subr_addr (ler_nat _ 2).
  have a1: a = 1.
    apply: contraFeq (ltr_geF ub_a); rewrite -subr_eq0 /m_ub2 => nz_a1.
    by rewrite ler_add ?(mulr_ege1 m1_ge1) // sqr_Cint_ge1 ?rpredB.
  rewrite /m_ub2 a1 subrr expr0n add0r expr1n mulr1 in ub_a.
  rewrite ltr_subl_addr -mulrSr ltr_nat ltnS in ub_a.
  by split; last apply/anti_leq/andP.
have{odd_frobL1} caseA_cohXY: caseA -> coherent (X ++ Y) L^# tau.
  move=> in_caseA.
  have scohX: subcoherent X tau R by apply: subset_subcoherent ccsXS.
  have irrX: {subset X <= irr L}.
    have [c1 | c2] := boolP case_c1; first by move=> phi /sXS/c1_irrS->.
    have ptiL := c2_ptiL c2; have [_ [ntW2 sW2H _ _] _] := ptiL.
    have{sW2H} isoW2: W2 / Z \isog W2.
      apply/isog_symr/quotient_isog; first exact: subset_trans sW2H nZH.
      exact/trivgP/(subset_trans _ in_caseA)/setSI.
    have{ntW2} ntW2bar: (W2 / Z != 1)%g by rewrite (isog_eq1 isoW2).
    have{ntW2bar} [defWbar ptiLZ] := primeTIhyp_quotient ptiL ntW2bar sZH nsZL.
    pose IchiZ := [set mod_Iirr (primeTI_Ires ptiLZ j) | j : Iirr (W2 / Z)].
    suffices /eqP-eq_Ichi: IchiZ == [set primeTI_Ires ptiL j | j : Iirr W2].
      move=> _ /seqIndP[k /setDP[_ kZ'k] ->].
      have [[j /irr_inj-Dk] | [] //] := prTIres_irr_cases ptiL k.
      have{j Dk} /imsetP[j _ Dk]: k \in IchiZ by rewrite eq_Ichi Dk mem_imset.
      by rewrite !inE Dk mod_IirrE ?cfker_mod in kZ'k.
    rewrite eqEcard !card_imset; last exact: prTIres_inj; first last.
      exact: inj_comp (morph_Iirr_inj _) (prTIres_inj _).
    apply/andP; split; last by rewrite !card_ord !NirrE (nclasses_isog isoW2).
    apply/subsetP=> k /imsetP[j _ Dk].
    have [[j1 /irr_inj->]|] := prTIres_irr_cases ptiL k; first exact: mem_imset.
    case=> /idPn[]; rewrite {k}Dk mod_IirrE ?cfIndMod ?cfMod_irr //.
    by rewrite cfInd_prTIres prTIred_not_irr.
  have [//|defX [tau2 cohX]]: X =i _ /\ coherent X L^# tau :=
    seqIndD_irr_coherence nsHL solH scohS odd_frobL1 _ irrX.
  have [[Itau2 Ztau2] Dtau2] := cohX.
  pose dvd_degrees_X (d : algC) := {in X, forall xi : 'CF(L), d %| xi 1%g}%C.
  have [xi1 Xxi1 dvd_xi1_1]: exists2 xi1, xi1 \in X & dvd_degrees_X (xi1 1%g).
    have /all_sig[e De] i: {e | 'chi[H]_i 1%g = (p ^ e)%:R}.
      have:= dvd_irr1_cardG i; rewrite irr1_degree dvdC_nat => dv_chi1_H.
      by have /p_natP[e ->] := pnat_dvd dv_chi1_H pH; exists e.
    have [_ /seqIndP[i0 IXi0 _]]: {phi | phi \in X}.
      by apply: seqIndD_nonempty; rewrite ?normal1 ?proper1G.
    pose xi1 := 'Ind[L] 'chi_[arg min_(i < i0 in Iirr_kerD H Z 1%G) e i].
    case: arg_minP => {i0 IXi0}//= i1 IXi1 min_i1 in xi1.
    exists xi1 => [|_ /seqIndP[i IXi ->]]; first by apply/seqIndP; exists i1.
    rewrite !cfInd1 // !De -!natrM dvdC_nat dvdn_pmul2l //.
    by rewrite dvdn_Pexp2l ?min_i1 ?prime_gt1.
  have nz_xi1_1: xi1 1%g != 0 by apply: seqInd1_neq0 Xxi1.
  pose d (xi : 'CF(L)) : algC := (truncC (xi 1%g / xi1 1%g))%:R.
  have{dvd_xi1_1} def_d xi: xi \in X -> xi 1%g = d xi * xi1 1%g.
    rewrite /d => Xxi; have Xge0 := Cnat_ge0 (Cnat_seqInd1 (_ : _ \in X)).
    by have /dvdCP_nat[||q ->] := dvd_xi1_1 xi Xxi; rewrite ?Xge0 ?mulfK ?natCK.
  have d_xi1: d xi1 = 1 by rewrite /d divff ?truncC1.
  have [_ [Itau /(_ _ _)/zcharW-Ztau] _ _ _] := scohS.
  have o_tauXY: orthogonal (map tau2 X) (map tau1 Y).
    exact: (coherent_ortho scohS).
  have [a Na xi1_1]: exists2 a, a \in Cnat & xi1 1%g = a * #|W1|%:R.
    have [i _ ->] := seqIndP Xxi1; rewrite cfInd1 // -oW1 mulrC.
    by exists ('chi_i 1%g); first apply: Cnat_irr1.
  pose psi1 := xi1 - a *: eta1.
  have Zpsi1: psi1 \in 'Z[S, L^#].
    rewrite zcharD1E !cfunE (uniY _ Yeta1) -xi1_1 subrr eqxx andbT.
    by rewrite rpredB ?rpredZ_Cnat ?mem_zchar ?(sXS _ Xxi1) // sYS.
  have [Y1 dY1 [X1 [dX1 _ oX1tauY]]] := orthogonal_split (map tau1 Y)(tau psi1).
  have{dX1 Y1 dY1 oYtau} [b Zb tau_psi1]: {b | b \in Cint &
    tau psi1 = X1 - a *: tau1 eta1 + b *: (\sum_(eta <- Y) tau1 eta)}.
  - exists ('[tau psi1, tau1 eta1] + a).
      by rewrite rpredD ?Cint_cfdot_vchar ?Cint_Cnat ?Ztau ?Ztau1 ?mem_zchar.
    rewrite [LHS]dX1 addrC -addrA; congr (_ + _).
    have{dY1} [_ -> ->] := orthonormal_span oYtau dY1.
    transitivity (\sum_(xi <- map tau1 Y) '[tau psi1, xi] *: xi).
      by apply/eq_big_seq=> xi ?; rewrite dX1 cfdotDl (orthoPl oX1tauY) ?addr0.
    rewrite big_map scaler_sumr !(big_rem eta1 Yeta1) /= addrCA addrA scalerDl.
    rewrite addrK; congr (_ + _); apply: eq_big_seq => eta.
    rewrite mem_rem_uniq // => /andP[eta1'eta /= Yeta]; congr (_ *: _).
    apply/(canRL (addNKr _)); rewrite addrC -2!raddfB /=.
    have Zeta: eta - eta1 \in 'Z[Y, L^#].
      by rewrite zcharD1E rpredB ?seqInd_zcharW //= !cfunE !uniY ?subrr.
    rewrite Dtau1 // Itau // ?(zchar_subset sYS) // cfdotBl cfdotZl.
    rewrite (span_orthogonal oXY) ?rpredB ?memv_span // add0r cfdotBr.
    by rewrite !oYY // !mulrb eqxx ifN_eqC // sub0r mulrN1 opprK.
  have oX: orthonormal X by apply: sub_orthonormal (irr_orthonormal L).
  have [_ oXX] := orthonormalP oX.
  have Zxi1Xd xi: xi \in X -> xi - d xi *: xi1 \in 'Z[X, L^#].
    move=> Xxi; rewrite zcharD1E !cfunE -def_d // subrr eqxx.
    by rewrite rpredB ?rpredZnat ?mem_zchar.
  pose psi := 'Res[L] (tau1 eta1); move Dc: '[psi, xi1] => c.
  have Zpsi: psi \in 'Z[irr L] by rewrite cfRes_vchar ?Ztau1 ?seqInd_zcharW.
  pose sumXd : 'CF(L) := \sum_(xi <- X) d xi *: xi.
  have{Dc} [xi2 Dpsi oxi2X]: {xi2 | psi = c *: sumXd + xi2 & orthogonal xi2 X}.
    exists (psi - c *: sumXd); first by rewrite addrC subrK.
    apply/orthoPl=> xi Xxi; rewrite cfdotBl cfdotZl cfproj_sum_orthonormal //.
    rewrite mulrC -[d xi]conjCK -Dc -cfdotZr -cfdotBr cfdot_Res_l -conjC0.
    rewrite -/tau rmorph_nat -Dtau2 ?Zxi1Xd // raddfB raddfZnat -/(d xi) cfdotC.
    by rewrite (span_orthogonal o_tauXY) ?rpredB ?rpredZ ?memv_span ?map_f.
  have Exi2 z: z \in Z -> xi2 z = xi2 1%g.
    rewrite [xi2]cfun_sum_constt => Zz; apply/cfker1; apply: subsetP z Zz.
    apply: subset_trans (cfker_sum _ _ _); rewrite subsetI sZL.
    apply/bigcapsP=> i; rewrite inE => xi2_i; rewrite cfker_scale_nz //.
    by apply: contraR xi2_i => X_i; rewrite (orthoPl oxi2X) // defX inE mem_irr.
  have Eba: '[psi, psi1] = b - a.
    rewrite cfdotC cfdot_Res_r -/tau tau_psi1 cfdotDl cfdotBl cfdotZl.
    rewrite (orthoPl oX1tauY) 1?oYYt ?map_f // eqxx sub0r addrC mulr1 rmorphB.
    by rewrite scaler_sumr cfproj_sum_orthonormal // aut_Cint // aut_Cnat.
  have{Eba oxi2X} Ebc: (a %| b - c)%C.
    rewrite -[b](subrK a) -Eba cfdotBr {1}Dpsi cfdotDl cfdotZl.
    rewrite cfproj_sum_orthonormal // (orthoPl oxi2X) // addr0 d_xi1 mulr1.
    rewrite addrC -addrA addKr addrC rpredB ?dvdC_refl //= cfdotZr aut_Cnat //.
    by rewrite dvdC_mulr // Cint_cfdot_vchar ?(seqInd_vcharW Yeta1).
  have DsumXd: sumXd = (xi1 1%g)^-1 *: (cfReg L - cfReg (L / Z) %% Z)%CF.
    apply/(canRL (scalerK nz_xi1_1))/(canRL (addrK _)); rewrite !cfReg_sum.
    pose kerZ := [pred i : Iirr L | Z \subset cfker 'chi_i].
    rewrite 2!linear_sum (bigID kerZ) (reindex _ (mod_Iirr_bij nsZL)) /= addrC.
    congr (_ + _).
      apply: eq_big => [i | i _]; first by rewrite mod_IirrE ?cfker_mod.
      by rewrite linearZ mod_IirrE // cfMod1.
    transitivity (\sum_(xi <- X) xi 1%g *: xi).
      by apply: eq_big_seq => xi Xxi; rewrite scalerA mulrC -def_d.
    rewrite (eq_big_perm [seq 'chi_i | i in [predC kerZ]]).
      by rewrite big_map big_filter.
    apply: uniq_perm_eq => // [|xi].
      by rewrite (map_inj_uniq irr_inj) ?enum_uniq.
    rewrite defX; apply/andP/imageP=> [[/irrP[i ->]] | [i]]; first by exists i.
    by move=> kerZ'i ->; rewrite mem_irr.
  have nz_a: a != 0 by have:= nz_xi1_1; rewrite xi1_1 mulf_eq0 => /norP[].
  have{psi Dpsi Zpsi xi2 Exi2 sumXd DsumXd} tau_eta1_Z z:
    z \in Z^# -> tau1 eta1 z - tau1 eta1 1%g = - c * #|H|%:R / a.
  - case/setD1P=> /negPf-ntz Zz; have Lz := subsetP sZL z Zz.
    transitivity (psi z - psi 1%g); first by rewrite !cfResE.
    rewrite Dpsi DsumXd !(cfRegE, cfunE) eqxx -opprB 2!mulrDr -[_ + xi2 _]addrA.
    rewrite Exi2 ?cfModE ?morph1 ?coset_id // ntz add0r addrK -mulNr mulrAC.
    by rewrite xi1_1 invfM -(sdprod_card defL) mulnC natrM !mulrA divfK ?neq0CG.
  have{tau_eta1_Z} dvH_cHa: (#|H| %| c * #|H|%:R / a)%C.
    have /dirrP[e [i /(canLR (signrZK e))Deta1]]: tau1 eta1 \in dirr G.
      by rewrite dirrE Ztau1 ?seqInd_zcharW //= oYYt ?map_f ?eqxx.
    have /set0Pn[z Zz]: Z^# != set0 by rewrite setD_eq0 subG1.
    have [z1 z2 Zz1 Zz2|_] := irrZmodH i _ z Zz.
      rewrite -Deta1 !cfunE; congr (_ * _); apply/(addIr (- tau1 eta1 1%g)).
      by rewrite !tau_eta1_Z.
    by rewrite -Deta1 !cfunE -mulrBr rpredMsign ?tau_eta1_Z ?mulNr ?rpredN.
  have{dvH_cHa} dv_ac: (a %| c)%C.
    by rewrite -(@dvdC_mul2r _ a) ?divfK // mulrC dvdC_mul2l ?neq0CG in dvH_cHa.
  have{c Ebc dv_ac} /dvdCP[q Zq Db]: (a %| b)%C by rewrite rpredBr in Ebc.
  have norm_psi1: '[psi1] = 1 + a ^+ 2.
    rewrite cfnormBd; last by rewrite cfdotZr (orthogonalP oXY) ?mulr0.
    by rewrite cfnormZ norm_Cnat // oXX // oYY // !eqxx mulr1.
  have{Zb oYYt} norm_tau_psi1: '[tau psi1] = '[X1] + a ^+ 2 * m_ub2 q.
    rewrite tau_psi1 -addrA cfnormDd /m_ub2; last first.
      rewrite addrC big_seq (span_orthogonal oX1tauY) ?memv_span1 //.
      by rewrite rpredB ?rpredZ ?rpred_sum // => *; rewrite memv_span ?map_f.
    congr (_ + _); transitivity (b ^+ 2 * m + a ^+ 2 - a * b *+ 2); last first.
      rewrite [RHS]mulrC [in RHS]addrC mulrBl sqrrB1 !addrA mulrDl !mul1r subrK.
      by rewrite mulrBl [m * _]mulrC mulrnAl mulrAC Db exprMn (mulrCA a) addrAC.
    rewrite addrC cfnormB !cfnormZ Cint_normK ?norm_Cnat // cfdotZr.
    rewrite cfnorm_map_orthonormal // -/m linear_sum cfproj_sum_orthonormal //.
    by rewrite oYYt ?map_f // eqxx mulr1 rmorphM conjCK aut_Cnat ?aut_Cint.
  have{norm_tau_psi1} mq2_lt2: m_ub2 q < 2%:R.
    suffices a2_gt1: a ^+ 2 > 1.
      have /ltr_pmul2l <-: a ^+ 2 > 0 by apply: ltr_trans a2_gt1.
      rewrite -(ltr_add2l '[X1]) -norm_tau_psi1 ltr_paddl ?cfnorm_ge0 //.
      by rewrite Itau // mulr_natr norm_psi1 ltr_add2r.
    suffices a_neq1: a != 1.
      rewrite expr_gt1 ?Cnat_ge0 // ltr_neqAle eq_sym a_neq1.
      by rewrite -(norm_Cnat Na) norm_Cint_ge1 ?Cint_Cnat.
    have /seqIndP[i1 /setDP[_ not_kerH'i1] Dxi1] := Xxi1.
    apply: contraNneq not_kerH'i1 => a_eq1; rewrite inE (subset_trans sZH') //.
    rewrite -lin_irr_der1 qualifE irr_char /= -(inj_eq (mulfI (neq0CiG L H))).
    by rewrite -cfInd1 // -Dxi1 xi1_1 a_eq1 mul1r mulr1 oW1.
  without loss{tau_psi1 Itau1 Ztau1 Dtau1 b q Db mq2_lt2 Zq} tau_psi1:
    tau1 cohY o_tauXY oX1tauY / tau psi1 = X1 - a *: tau1 eta1.
  - move=> IH; have [q0 | [q1 /eq_leq-szY2]] := m_ub2_lt2 q Zq mq2_lt2.
      by apply: (IH tau1) => //; rewrite tau_psi1 Db q0 mul0r scale0r addr0.
    have defY: perm_eq Y (eta1 :: eta1^*)%CF.
      have uYeta: uniq (eta1 :: eta1^*)%CF.
        by rewrite /= inE eq_sym (hasPn nrS) ?sYS.
      rewrite perm_eq_sym uniq_perm_eq //.
      have [|//]:= leq_size_perm uYeta _ szY2.
      by apply/allP; rewrite /= Yeta1 ccY.
    have memYtau1c: {subset [seq tau1 eta^* | eta <- Y]%CF <= map tau1 Y}.
      by move=> _ /mapP[eta Yeta ->]; rewrite /= map_f ?ccY.
    apply: IH (dual_coherence scohY cohY szY2) _ _ _.
    - rewrite (map_comp -%R) orthogonal_oppr.
      by apply/orthogonalP=> phi psi ? /memYtau1c; apply: (orthogonalP o_tauXY).
    - rewrite (map_comp -%R) orthogonal_oppr.
      by apply/orthoPl=> psi /memYtau1c; apply: (orthoPl oX1tauY).
    rewrite tau_psi1 (eq_big_perm _ defY) Db q1 /= mul1r big_cons big_seq1.
    by rewrite scalerDr addrA subrK -scalerN opprK.
  have [[Itau1 Ztau1] Dtau1] := cohY.
  have n1X1: '[X1] = 1.
    rewrite -(canLR (addrK _) norm_psi1) -Itau // tau_psi1.
    rewrite cfnormBd; last by rewrite cfdotZr (orthoPl oX1tauY) ?map_f ?mulr0.
    by rewrite cfnormZ norm_Cnat // Itau1 ?mem_zchar ?oYY // eqxx mulr1 addrK.
  without loss{Itau2 Ztau2 Dtau2} defX1: tau2 cohX o_tauXY / X1 = tau2 xi1.
    move=> IH; have ZX: {subset X <= 'Z[X]} by apply: seqInd_zcharW.
    have dirrXtau xi: xi \in X -> tau2 xi \in dirr G.
      by move=> Xxi; rewrite dirrE Ztau2 1?Itau2 ?ZX //= oXX ?eqxx.
    have dirrX1: X1 \in dirr G.
      rewrite dirrE n1X1 eqxx -(canLR (subrK _) tau_psi1).
      by rewrite rpredD ?rpredZ_Cnat ?(zcharW (Ztau _ _)) ?Ztau1 ?seqInd_zcharW.
    have{Zxi1Xd} oXdX1 xi: xi \in X -> xi != xi1 ->
      '[d xi *: tau2 xi1 - tau2 xi, X1] = d xi.
    - move=> Xxi xi1'xi; have ZXxi := Zxi1Xd xi Xxi.
      rewrite -(canLR (subrK _) tau_psi1) cfdotDr addrC.
      rewrite (span_orthogonal o_tauXY) ?rpredB ?rpredZ ?memv_span ?map_f //.
      rewrite add0r -opprB cfdotNl -{1}raddfZ_Cnat ?Cnat_nat // -raddfB.
      rewrite Dtau2 // Itau ?cfdotBr ?opprB //; last exact: zchar_subset ZXxi.
      rewrite (span_orthogonal oXY) ?rpredB ?rpredZ ?memv_span // sub0r.
      by rewrite cfdotBl cfdotZl opprB !oXX // eqxx mulr1 mulrb ifN ?subr0.
    pose xi3 := xi1^*%CF; have Xxi3: xi3 \in X by apply: ccX.
    have xi1'3: xi3 != xi1 by rewrite (hasPn nrS) ?sXS.
    have [| defX1]: X1 = tau2 xi1 \/ X1 = - tau2 xi3; first 2 [exact : IH].
      have d_xi3: d xi3 = 1 by rewrite /d cfunE conj_Cnat ?(Cnat_seqInd1 Xxi1).
      have:= oXdX1 xi3 Xxi3 xi1'3; rewrite d_xi3 scale1r.
      by apply: cfdot_add_dirr_eq1; rewrite // ?rpredN dirrXtau.
    have szX2: (size X <= 2)%N.
      apply: uniq_leq_size (xi1 :: xi3) uX _ => // xi4 Xxi4; rewrite !inE.
      apply: contraR (seqInd1_neq0 nsHL Xxi4) => /norP[xi1'4 xi3'4].
      rewrite def_d // -oXdX1 // defX1 cfdotNr cfdotBl cfdotZl opprB.
      by rewrite !Itau2 ?ZX ?oXX // !mulrb ifN ?ifN_eqC // mulr0 subr0 mul0r.
    apply: (IH _ (dual_coherence scohX cohX szX2)) defX1.
    apply/orthogonalP=> _ psi2 /mapP[xi Xxi -> /=] Ytau_psi2.
    by rewrite cfdotNl (orthogonalP o_tauXY) ?oppr0 // map_f ?ccX.
  rewrite -raddfZ_Cnat // defX1 in tau_psi1.
  apply: (bridge_coherent scohS ccsXS cohX ccsYS cohY X'Y) tau_psi1.
  by rewrite (zchar_on Zpsi1) rpredZ_Cnat ?mem_zchar.
have{caseA_cohXY Itau1 Ztau1 Dtau1 oYYt} cohXY: coherent (X ++ Y) L^# tau.
  have [in_caseA | in_caseB] := boolP caseA; first exact: caseA_cohXY.
  have defZ: Z = W2 by rewrite /Z ifN.
  have /subsetIP[_ cZL] := caseB_sZZL in_caseB.
  have{in_caseB} [c2 _ _] := caseB_P in_caseB; move/(_ c2) in oRW.
  pose PtypeL := c2_ddA0 c2; pose w2 := #|W2|.
  have{c2_prW2} pr_w2: prime w2 := c2_prW2 c2.
  have /cyclicP[z0 cycZ]: cyclic Z by rewrite defZ prime_cyclic.
  have oz0: #[z0] = w2 by rewrite /w2 -defZ cycZ.
  have regYZ: {in Y & Z^#, forall (eta : 'CF(L)) x, tau1 eta x = tau1 eta z0}.
    rewrite cycZ => eta x Yeta /setD1P[ntx /cyclePmin[k lt_k_z0 Dx]].
    have{ntx} k_gt0: (0 < k)%N by case: (k) Dx ntx => // -> /eqP[].
    have{lt_k_z0} [cokw2 zz0_dv_w2]: coprime k w2 /\ #[z0] %| w2.
      by rewrite coprime_sym prime_coprime // -oz0 // gtnNdvd.
    have [u Du _]:= make_pi_cfAut G cokw2; rewrite Dx -Du ?Ztau1 ?mem_zchar //.
    have nAL: L \subset 'N(A) by have [_ /subsetIP[]] := normedTI_P tiA.
    pose ddA := restr_Dade_hyp PtypeL (subsetUl _ _) nAL.
    have{Dtau1} Dtau1: {in 'Z[Y, L^#], tau1 =1 Dade ddA}.
      by move=> phi Yphi/=; rewrite Dtau1 ?Dade_Ind ?(zcharD1_seqInd_on _ Yphi).
    have cohY_Dade: coherent_with Y L^# (Dade ddA) tau1 by [].
    rewrite (cfAut_Dade_coherent cohY_Dade) ?irrY //; last first.
      split; last exact: cfAut_seqInd.
      exact: seqInd_nontrivial_irr (irrY _ Yeta) (Yeta).
    rewrite -[cfAut u _](subrK eta) -opprB addrC raddfB !cfunE -[RHS]subr0.
    congr (_ - _); rewrite Dtau1 ?zcharD1_seqInd ?seqInd_sub_aut_zchar //.
    rewrite Dade_id; last by rewrite !inE -cycle_eq1 -cycle_subG -cycZ ntZ.
    rewrite !cfunE cfker1 ?aut_Cnat ?subrr ?(Cnat_seqInd1 Yeta) //.
    have [j /setDP[kerH'j _] Deta] := seqIndP Yeta; rewrite inE in kerH'j.
    by rewrite -cycle_subG -cycZ (subset_trans sZH') // Deta sub_cfker_Ind_irr.
  have [_ [Itau /(_ _ _)/zcharW-Ztau] oSS _ _] := scohS.
  pose gamma i : 'CF(L) := 'Ind[L] 'chi[Z]_i - #|H : Z|%:R *: eta1.
  have [Y1 tau_gamma defY1]: exists2 Y1 : 'CF(G), forall i : Iirr Z, i != 0 ->
      exists2 X1 : 'CF(G), orthogonal X1 (map tau1 Y)
      & tau (gamma i) = X1 - #|H : Z|%:R *: Y1
      & Y1 = tau1 eta1 \/ size Y = 2 /\ Y1 = dual_iso tau1 eta1.
  - pose psi1 := tau1 eta1; pose b := psi1 z0.
    pose a :=  (psi1 1%g - b) / #|Z|%:R.
    have sZG := subset_trans sZL sLG.
    have Dpsi1: 'Res[Z] psi1 = a *: cfReg Z + b%:A.
      apply/cfun_inP=> z Zz; rewrite cfResE // !(cfRegE, cfunE) cfun1E Zz mulr1.
      have [-> | ntz] := altP eqP; first by rewrite divfK ?neq0CG ?subrK.
      by rewrite mulr0 add0r regYZ // !inE ntz.
    have /dvdCP[x0 Zx0 Dx0]: (#|H : Z| %| a)%C.
      suffices dvH_p_psi1: (#|H| %| b - psi1 1%g)%C.
        rewrite -(@dvdC_mul2r _ #|Z|%:R) ?divfK ?neq0CG // -opprB rpredN /=.
        by rewrite -natrM mulnC Lagrange.
      have psi1Z z: z \in Z^# -> psi1 z = b by apply: regYZ.
      have /dirrP[e [i /(canLR (signrZK e))-Epsi1]]: psi1 \in dirr G.
        have [_ oYt] := orthonormalP oYtau.
        by rewrite dirrE oYt ?map_f // !eqxx Ztau1 ?seqInd_zcharW.
      have Zz: z0 \in Z^# by rewrite !inE -cycle_eq1 -cycle_subG -cycZ ntZ /=.
      have [z1 z2 Zz1 Zz2 |_] := irrZmodH i _ _ Zz.
        by rewrite -Epsi1 !cfunE !psi1Z.
      by rewrite -Epsi1 !cfunE -mulrBr rpredMsign psi1Z.
    pose x1 := '[eta1, 'Res psi1]; pose x := x0 + 1 - x1.
    have Zx: x \in Cint.
      rewrite rpredB ?rpredD // Cint_cfdot_vchar // ?(seqInd_vcharW Yeta1) //.
      by rewrite cfRes_vchar // Ztau1 ?seqInd_zcharW.
    pose Y1 := - \sum_(eta <- Y) (x - (eta == eta1)%:R) *: tau1 eta.
    have IndZfacts i: i != 0 ->
      [/\ 'chi_i 1%g = 1, 'Ind 'chi_i \in 'Z[X] & gamma i \in 'Z[S, L^#]].
    - move=> nzi; have /andP[_ /eqP-lin_i]: 'chi_i \is a linear_char.
        by rewrite lin_irr_der1 (derG1P _) ?sub1G // cycZ cycle_abelian.
      have Xchi: 'Ind 'chi_i \in 'Z[X].
        rewrite -(cfIndInd _ sHL) // ['Ind[H] _]cfun_sum_constt linear_sum.
        apply: rpred_sum => k k_i; rewrite linearZ rpredZ_Cint ?mem_zchar //=.
          by rewrite Cint_cfdot_vchar_irr // cfInd_vchar ?irr_vchar.
        rewrite mem_seqInd ?normal1 // !inE sub1G andbT.
        by rewrite -(sub_cfker_constt_Ind_irr k_i) // subGcfker.
      split=> //; rewrite zcharD1E !cfunE cfInd1 // uniY // lin_i mulr1.
      rewrite oW1 -natrM mulnC Lagrange_index // subrr eqxx andbT.
      by rewrite rpredB ?rpredZnat ?(zchar_subset sXS Xchi) ?mem_zchar ?sYS.
    have Dgamma (i : Iirr Z) (nzi : i != 0):
      exists2 X1 : 'CF(G), orthogonal X1 (map tau1 Y)
            & tau (gamma i) = X1 - #|H : Z|%:R *: Y1.
    - have [lin_i Xchi Zgamma] := IndZfacts i nzi.
      have Da: '[tau (gamma i), psi1] = a - #|H : Z|%:R * x1.
        rewrite !(=^~ cfdot_Res_r, cfdotBl) cfResRes // cfdotZl -/x1 Dpsi1.
        congr (_ - _); rewrite cfdotDr cfReg_sum cfdotC cfdotZl cfdotZr.
        rewrite -(big_tuple _ _ _ xpredT (fun xi : 'CF(Z) => xi 1%g *: xi)).
        rewrite cfproj_sum_orthonormal ?irr_orthonormal ?mem_irr // lin_i mulr1.
        rewrite -irr0 cfdot_irr (negPf nzi) mulr0 addr0.
        by rewrite aut_Cint // Dx0 rpredM ?rpred_nat.
      exists (tau (gamma i) + #|H : Z|%:R *: Y1); last by rewrite addrK.
      apply/orthoPl=> _ /mapP[eta Yeta ->].
      rewrite scalerN cfdotBl cfdotZl cfproj_sum_orthonormal // [x]addrAC.
      rewrite -addrA mulrDr mulrBr mulrC -Dx0 -Da opprD addrA -!raddfB /=.
      have Yeta_1: eta - eta1 \in 'Z[Y, L^#].
        by rewrite zcharD1E rpredB ?seqInd_zcharW //= !cfunE !uniY ?subrr.
      rewrite Dtau1 ?Itau // ?(zchar_subset sYS) // cfdotBl cfdotZl.
      rewrite (span_orthogonal oXY) ?(zchar_span Xchi) ?(zchar_span Yeta_1) //.
      by rewrite cfdotBr -mulrN opprB !oYY // eqxx eq_sym addrK.
    have [i0 nz_i0] := has_nonprincipal_irr ntZ.
    exists Y1 => //; have{Dgamma} [X1 oX1Y Dgamma] := Dgamma i0 nz_i0.
    have [lin_i Xchi Zgamma] := IndZfacts i0 nz_i0.
    have norm_gamma: '[tau (gamma i0)] = (#|L : Z| + #|H : Z| ^ 2)%:R.
      rewrite natrD Itau // cfnormBd; last first.
        rewrite (span_orthogonal oXY) ?(zchar_span Xchi) //.
        by rewrite memvZ ?memv_span.
      rewrite cfnorm_Ind_irr //; congr (#|_ : Z|%:R + _); last first.
        by rewrite cfnormZ oYY // eqxx mulr1 normCK rmorph_nat -natrM.
      by apply/setIidPl; rewrite (subset_trans _ (cent_sub_inertia _)) 1?centsC.
    have{norm_gamma} ub_norm_gamma: '[tau (gamma i0)] < (#|H : Z| ^ 2).*2%:R.
      rewrite norm_gamma -addnn ltr_nat ltn_add2r.
      rewrite -(Lagrange_index sHL) ?ltn_pmul2r // -[#|H : Z| ]prednK // ltnS.
      have frobL2: [Frobenius L / Z = (H / Z) ><| (W1 / Z)]%g.
        apply: (Frobenius_coprime_quotient defL nsZL) => //.
        split=> [|y W1y]; first exact: sub_proper_trans ltH'H.
        by rewrite defZ; have [/= ? [_ [_ _ _ ->]]] := PtypeL.
      have nZW1 := subset_trans sW1L nZL.
      have tiZW1: Z :&: W1 = 1%g by rewrite coprime_TIg ?(coprimeSg sZH).
      rewrite -oW1 (card_isog (quotient_isog nZW1 tiZW1)) -card_quotient //.
      rewrite dvdn_leq ?(Frobenius_dvd_ker1 frobL2) // -subn1 subn_gt0.
      by rewrite cardG_gt1; case/Frobenius_context: frobL2.
    have{ub_norm_gamma} ub_xm: m_ub2 x < 2%:R.
      have: '[Y1] < 2%:R.
        rewrite -2!(ltr_pmul2l (gt0CiG H Z)) -!natrM mulnA muln2.
        apply: ler_lt_trans ub_norm_gamma; rewrite Dgamma cfnormBd.
          by rewrite cfnormZ normCK rmorph_nat mulrA -subr_ge0 addrK cfnorm_ge0.
        rewrite (span_orthogonal oX1Y) ?memv_span1 ?rpredZ // rpredN big_seq.
        by apply/rpred_sum => eta Yeta; rewrite rpredZ ?memv_span ?map_f.
      rewrite cfnormN cfnorm_sum_orthonormal // (big_rem eta1) //= eqxx.
      congr (_ + _ < _); first by rewrite Cint_normK 1?rpredB ?rpred1.
      transitivity (\sum_(eta <- rem eta1 Y) x ^+ 2).
        rewrite rem_filter // !big_filter; apply/eq_bigr => eta /negPf->.
        by rewrite subr0 Cint_normK.
      rewrite big_const_seq count_predT // -Monoid.iteropE -[LHS]mulr_natl.
      by rewrite /m (perm_eq_size (perm_to_rem Yeta1)) /= mulrSr addrK.
    have [x_eq0 | [x_eq1 szY2]] := m_ub2_lt2 x Zx ub_xm.
      left; rewrite /Y1 x_eq0 (big_rem eta1) //= eqxx sub0r scaleN1r.
      rewrite big_seq big1 ?addr0 ?opprK => // eta.
      by rewrite mem_rem_uniq // => /andP[/negPf-> _]; rewrite subrr scale0r.
    have eta1'2: eta1^*%CF != eta1 by apply: seqInd_conjC_neq Yeta1.
    have defY: perm_eq Y (eta1 :: eta1^*%CF).
      have uY2: uniq (eta1 :: eta1^*%CF) by rewrite /= inE eq_sym eta1'2.
      rewrite perm_eq_sym uniq_perm_eq //.
      have sY2Y: {subset (eta1 :: eta1^*%CF) <= Y}.
        by apply/allP; rewrite /= cfAut_seqInd ?Yeta1.
      by have [|//]:= leq_size_perm uY2 sY2Y; rewrite szY2.
    right; split=> //; congr (- _); rewrite (eq_big_perm _ defY) /= x_eq1.
    rewrite big_cons big_seq1 eqxx (negPf eta1'2) subrr scale0r add0r subr0.
    by rewrite scale1r.
  have normY1: '[Y1] = 1.
    have [-> | [_ ->]] := defY1; first by rewrite oYYt ?eqxx ?map_f.
    by rewrite cfnormN oYYt ?eqxx ?map_f ?ccY.
  have YtauY1: Y1 \in 'Z[map tau1 Y].
    have [-> | [_ ->]] := defY1; first by rewrite mem_zchar ?map_f.
    by rewrite rpredN mem_zchar ?map_f ?ccY.
  have spanYtau1 := zchar_span YtauY1.
  have norm_eta1: '[eta1] = 1 by rewrite oYY ?eqxx.
  have /all_sig2[a Za Dxa] xi: {a | a \in Cnat
                  & xi \in X -> xi 1%g = a * #|W1|%:R
                    /\ (exists2 X1 : 'CF(G), orthogonal X1 (map tau1 Y)
                              & tau (xi - a *: eta1) = X1 - a *: Y1)}.
  - case Xxi: (xi \in X); last by exists 0; rewrite ?rpred0.
    have /sig2_eqW[k /setDP[_ kerZ'k] def_xi] := seqIndP Xxi.
    rewrite inE in kerZ'k.
    pose a := 'chi_k 1%g; have Na: a \in Cnat by apply: Cnat_irr1.
    have Dxi1: xi 1%g = a * #|W1|%:R by rewrite mulrC oW1 def_xi cfInd1.
    exists a => // _; split=> //.
    have [i0 nzi0 Res_k]: exists2 i, i != 0 & 'Res[Z] 'chi_k = a *: 'chi_i.
      have [chi lin_chi defRkZ] := cfcenter_Res 'chi_k.
      have sZ_Zk: Z \subset 'Z('chi_k)%CF.
        by rewrite (subset_trans sZZH) // -cap_cfcenter_irr bigcap_inf.
      have{lin_chi} /irrP[i defRk]: 'Res chi \in irr Z.
        by rewrite lin_char_irr ?cfRes_lin_char.
      have{chi defRk defRkZ} defRk: 'Res[Z] 'chi_k = a *: 'chi_i.
        by rewrite -defRk -linearZ -defRkZ /= cfResRes ?cfcenter_sub.
      exists i => //; apply: contra kerZ'k => i_0; apply/constt0_Res_cfker=> //.
      by rewrite inE defRk cfdotZl cfdot_irr i_0 mulr1 irr1_neq0.
    set phi := 'chi_i0 in Res_k; pose a_ i := '['Ind[H] phi, 'chi_i].
    pose rp := irr_constt ('Ind[H] phi).
    have defIphi: 'Ind phi = \sum_(i in rp) a_ i *: 'chi_i.
      exact: cfun_sum_constt.
    have a_k: a_ k = a.
      by rewrite /a_ -cfdot_Res_r Res_k cfdotZr cfnorm_irr mulr1 conj_Cnat.
    have rp_k: k \in rp by rewrite inE ['[_, _]]a_k irr1_neq0.
    have resZr i: i \in rp -> 'Res[Z] 'chi_i = a_ i *: phi.
      rewrite constt_Ind_Res -/phi => /Clifford_Res_sum_cfclass-> //.
      have Na_i: a_ i \in Cnat by rewrite Cnat_cfdot_char ?cfInd_char ?irr_char.
      rewrite -/phi cfdot_Res_l cfdotC conj_Cnat {Na_i}//; congr (_ *: _).
      have <-: 'I_H['Res[Z] 'chi_k] = H.
        apply/eqP; rewrite eqEsubset subsetIl.
        by apply: subset_trans (sub_inertia_Res _ _); rewrite ?sub_Inertia.
      by rewrite Res_k inertia_scale_nz ?irr1_neq0 // cfclass_inertia big_seq1.
    have lin_phi: phi 1%g = 1.
      apply: (mulfI (irr1_neq0 k)); have /resZr/cfunP/(_ 1%g) := rp_k.
      by rewrite cfRes1 // cfunE mulr1 a_k.
    have Da_ i: i \in rp -> 'chi_i 1%g = a_ i.
      move/resZr/cfunP/(_ 1%g); rewrite cfRes1 // cfunE => ->.
      by rewrite lin_phi mulr1.
    pose chi i := 'Ind[L] 'chi[H]_i; pose alpha i := chi i - a_ i *: eta1.
    have Aalpha i: i \in rp -> alpha i \in 'CF(L, A).
      move=> r_i; rewrite cfun_onD1 !cfunE cfInd1 // (uniY _ Yeta1) -oW1.
      rewrite Da_ // mulrC subrr eqxx.
      by rewrite memvB ?cfInd_normal ?memvZ // (seqInd_on _ Yeta1).
    have [sum_alpha sum_a2]: gamma i0 = \sum_(i in rp) a_ i *: alpha i
                          /\ \sum_(i in rp) a_ i ^+ 2 = #|H : Z|%:R.
    + set lhs1 := LHS; set lhs2 := (lhs in _ /\ lhs = _).
      set rhs1 := RHS; set rhs2 := (rhs in _ /\ _ = rhs).
      have eq_diff: lhs1 - rhs1 = (lhs2 - rhs2) *: eta1.
        rewrite scalerBl addrAC; congr (_ - _).
        rewrite -(cfIndInd _ sHL sZH) defIphi linear_sum -sumrB scaler_suml.
        apply: eq_bigr => i rp_i; rewrite linearZ scalerBr opprD addNKr.
        by rewrite opprK scalerA.
      have: (lhs1 - rhs1) 1%g == 0.
        rewrite !cfunE -(cfIndInd _ sHL sZH) !cfInd1 // lin_phi mulr1.
        rewrite -divgS // -(sdprod_card defL) mulKn // mulrC uniY // subrr.
        rewrite sum_cfunE big1 ?subrr // => i rp_i.
        by rewrite cfunE (cfun_on0 (Aalpha i rp_i)) ?mulr0 // !inE eqxx.
      rewrite eq_diff cfunE mulf_eq0 subr_eq0 (negPf (seqInd1_neq0 _ Yeta1)) //.
      rewrite orbF => /eqP-sum_a2; split=> //; apply/eqP; rewrite -subr_eq0.
      by rewrite eq_diff sum_a2 subrr scale0r.
    have Xchi i: i \in rp -> chi i \in X.
      move=> rp_i; apply/seqIndP; exists i => //; rewrite !inE sub1G andbT.
      apply: contra rp_i => kerZi; rewrite -cfdot_Res_r cfRes_sub_ker //.
      by rewrite cfdotZr -irr0 cfdot_irr (negPf nzi0) mulr0.
    have oRY i: i \in rp -> orthogonal (R (chi i)) (map tau1 Y).
      move/Xchi=> Xchi_i; rewrite orthogonal_sym.
      by rewrite (coherent_ortho_supp scohS) // ?sXS // (contraL (X'Y _)).
    have Za_ i: a_ i \in Cint.
      by rewrite Cint_cfdot_vchar_irr // cfInd_vchar ?irr_vchar.
    have Zeta1: eta1 \in 'Z[irr L] := seqInd_vcharW Yeta1.
    have Ztau_alpha i: tau (alpha i) \in 'Z[irr G].
      by rewrite !(cfInd_vchar, rpredB) ?irr_vchar ?rpredZ_Cint.
    have /all_tag2[X1 R_X1 /all_tag2[b Rb /all_sig2[Z1 oZ1R]]] i:
         {X1 : 'CF(G) & i \in rp -> X1 \in 'Z[R (chi i)]
       & {b : algC & i \in rp -> b \is Creal
       & {Z1 : 'CF(G) | i \in rp -> orthogonal Z1 (R (chi i))
                      & tau (alpha i) = X1 - b *: Y1 + Z1 /\ '[Z1, Y1] = 0}}}.
    + have [X1 dX1 [YZ1 [dXYZ _ oYZ1R]]] :=
        orthogonal_split (R (chi i)) (tau (alpha i)).
      exists X1.
        have [_ _ _ Rok _] := scohS => /Xchi/sXS/Rok[ZR oRR _].
        have [_ -> ->] := orthonormal_span oRR dX1.
        rewrite big_seq rpred_sum // => aa Raa.
        rewrite rpredZ_Cint ?mem_zchar // -(canLR (addrK _) dXYZ) cfdotBl.
        by rewrite (orthoPl oYZ1R) // subr0 Cint_cfdot_vchar ?(ZR aa).
      pose b := - '[YZ1, Y1]; exists b => [rp_i|].
        rewrite Creal_Cint // rpredN -(canLR (addKr _) dXYZ) cfdotDl.
        rewrite (span_orthogonal (oRY i rp_i)) ?rpredN ?(zchar_span YtauY1) //.
        rewrite add0r Cint_cfdot_vchar // (zchar_trans_on _ YtauY1) //.
        by move=> _ /mapP[eta Yeta ->]; rewrite Ztau1 ?mem_zchar.
      exists (YZ1 + b *: Y1) => [/oRY-oRiY|]; last first.
        by rewrite addrCA subrK addrC cfdotDl cfdotZl normY1 mulr1 addrN.
      apply/orthoPl=> aa Raa; rewrite cfdotDl (orthoPl oYZ1R) // add0r.
      by rewrite cfdotC (span_orthogonal oRiY) ?conjC0 ?rpredZ // memv_span.
    case/all_and2=> defXbZ oZY1; have spanR_X1 := zchar_span (R_X1 _ _).
    have ub_alpha i: i \in rp ->
       [/\ '[chi i] <= '[X1 i]
         & '[a_ i *: eta1] <= '[b i *: Y1 - Z1 i] ->
           [/\ '[X1 i] = '[chi i], '[b i *: Y1 - Z1 i] = '[a_ i *: eta1]
             & exists2 E, subseq E (R (chi i)) & X1 i = \sum_(aa <- E) aa]].
    + move=> rp_i; apply: (subcoherent_norm scohS) (erefl _) _.
      * rewrite sXS ?Xchi ?rpredZ_Cint /orthogonal //; split=> //=.
        by rewrite !cfdotZr !(orthogonalP oXY) ?mulr0 ?eqxx ?ccX // Xchi.
      * have [[/(_ _ _)/char_vchar-Z_S _ _] IZtau _ _ _] := scohS.
        apply: sub_iso_to IZtau; [apply: zchar_trans_on | exact: zcharW].
        apply/allP; rewrite /= zchar_split (cfun_onS (setSD _ sHL)) ?Aalpha //.
        rewrite rpredB ?rpredZ_Cint ?mem_zchar ?(sYS eta1) // ?sXS ?Xchi //=.
        by rewrite sub_aut_zchar ?zchar_onG ?mem_zchar ?sXS ?ccX ?Xchi.
      suffices oYZ_R: orthogonal (b i *: Y1 - Z1 i) (R (chi i)).
        rewrite opprD opprK addrA -defXbZ cfdotC.
        by rewrite (span_orthogonal oYZ_R) ?memv_span1 ?spanR_X1 ?conjC0.
      apply/orthoPl=> aa Raa; rewrite cfdotBl (orthoPl (oZ1R i _)) // cfdotC.
      by rewrite subr0 (span_orthogonal (oRY i _)) ?conjC0 ?rpredZ // memv_span.
    have leba i: i \in rp -> b i <= a_ i.
      move=> rp_i; have ai_gt0: a_ i > 0 by rewrite -Da_ ?irr1_gt0.
      rewrite (ler_trans (real_ler_norm (Rb i _))) //.
      rewrite -(@ler_pexpn2r _ 2) ?qualifE ?(ltrW ai_gt0) ?norm_ger0 //.
      apply: ler_trans (_ : '[b i *: Y1 - Z1 i] <= _).
        rewrite cfnormBd; last by rewrite cfdotZl cfdotC oZY1 ?conjC0 ?mulr0.
        by rewrite cfnormZ normY1 mulr1 ler_addl cfnorm_ge0.
      rewrite -(ler_add2l '[X1 i]) -cfnormBd; last first.
        rewrite cfdotBr cfdotZr (span_orthogonal (oRY i _)) ?spanR_X1 //.
        rewrite mulr0 sub0r cfdotC.
        by rewrite (span_orthogonal (oZ1R i _)) ?raddf0 ?memv_span1 ?spanR_X1.
      have Salpha: alpha i \in 'Z[S, L^#].
        rewrite zcharD1_seqInd // zchar_split Aalpha // andbT.
        by rewrite rpredB ?rpredZ_Cint ?mem_zchar ?(sYS eta1) ?sXS ?Xchi.
      rewrite opprD opprK addrA -defXbZ ?Itau //.
      rewrite cfnormBd; last by rewrite cfdotZr (orthogonalP oXY) ?mulr0 ?Xchi.
      rewrite cfnormZ Cint_normK ?(oYY eta1) // eqxx mulr1 ler_add2r.
      by have lbX1i: '[chi i] <= '[X1 i] by have [] := ub_alpha i rp_i.
    have{leba} eq_ab: {in rp, a_ =1 b}.
      move=> i rp_i; apply/eqP; rewrite -subr_eq0; apply/eqP.
      apply: (mulfI (irr1_neq0 i)); rewrite mulr0 Da_ // mulrBr.
      move: i rp_i; apply: psumr_eq0P => [i rp_i | ].
        by rewrite subr_ge0 ler_pmul2l ?leba // -Da_ ?irr1_gt0.
      have [X2 oX2Y /(congr1 (cfdotr Y1))] := tau_gamma i0 nzi0.
      rewrite sumrB sum_a2 sum_alpha /tau linear_sum /= cfdot_suml cfdotBl.
      rewrite (span_orthogonal oX2Y) ?memv_span1 ?(zchar_span YtauY1) // add0r.
      rewrite cfdotZl normY1 mulr1 => /(canLR (@opprK _)) <-.
      rewrite -opprD -big_split big1 ?oppr0 //= => i rp_i.
      rewrite linearZ cfdotZl /= -/tau defXbZ addrC cfdotDl oZY1 addr0.
      rewrite cfdotBl cfdotZl normY1 mulr1 mulrBr addrC subrK.
      by rewrite (span_orthogonal (oRY i _)) ?spanR_X1 ?mulr0.
     exists (X1 k).
      apply/orthoPl=> psi /memv_span Ypsi.
      by rewrite (span_orthogonal (oRY k _)) // (zchar_span (R_X1 k rp_k)).
    apply/eqP; rewrite -/a def_xi -a_k defXbZ addrC -subr_eq0 eq_ab // addrK.
    rewrite -cfnorm_eq0 -(inj_eq (addrI '[b k *: Y1])).
    have [_ [|_]] := ub_alpha k rp_k.
      rewrite cfnormBd; last by rewrite cfdotZl cfdotC oZY1 conjC0 mulr0.
      by rewrite addrC !cfnormZ eq_ab // normY1 norm_eta1 ler_addr cfnorm_ge0.
    rewrite cfnormBd; last by rewrite cfdotZl cfdotC oZY1 conjC0 mulr0.
    by move=> -> _; rewrite addr0 !cfnormZ eq_ab // normY1 norm_eta1.
  have scohXY: subcoherent (X ++ Y) tau R.
    apply/(subset_subcoherent scohS).
    split; first by rewrite cat_uniq uX uY andbT; apply/hasPn.
      by move=> xi; rewrite mem_cat => /orP[/sXS | /sYS].
    by move=> xi; rewrite !mem_cat => /orP[/ccX-> | /ccY->]; rewrite ?orbT.
  have XYeta1: eta1 \in X ++ Y by rewrite mem_cat Yeta1 orbT.
  have Z_Y1: Y1 \in 'Z[irr G].
    by case: defY1 => [|[_]] ->; rewrite ?rpredN Ztau1 ?mem_zchar ?ccY.
  apply: pivot_coherence scohXY XYeta1 Z_Y1 _ _; rewrite norm_eta1 //.
  move=> xi /andP[eta1'xi]; rewrite /= mem_cat => /orP[Xxi | Yxi].
    have [Da1 [X1 oX1Y tauX1]] := Dxa _ Xxi.
    exists (a xi); first by rewrite (uniY _ Yeta1).
    rewrite -/tau {}tauX1 cfdotBl cfdotZl normY1 !mulr1.
    by rewrite (span_orthogonal oX1Y) ?add0r ?memv_span1.
  exists 1; first by rewrite rpred1 mul1r !uniY.
  rewrite scale1r mulr1 -/tau -Dtau1 ?raddfB ?cfdotBl; last first.
    by rewrite zcharD1E rpredB ?mem_zchar //= !cfunE !uniY ?subrr.
  have [-> | [szY2 ->]] := defY1; rewrite ?cfdotNr !Itau1 ?mem_zchar ?ccY //.
    by rewrite !oYY // eqxx (negPf eta1'xi) add0r.
  pose Y2 := eta1 :: eta1^*%CF; suffices: xi \in Y2.
    rewrite opprK !inE (negPf eta1'xi) /= => /eqP->.
    by rewrite !oYY ?ccY // !mulrb eqxx ifN_eqC ?(hasPn nrS) ?sYS ?addr0.
  have /leq_size_perm: {subset Y2 <= Y} by apply/allP; rewrite /= Yeta1 ccY.
  by case=> [||->]; rewrite ?szY2 //= inE eq_sym (hasPn nrS) ?sYS.
pose S1 := [::] ++ X ++ Y; set S2 := [::] in S1; rewrite -[X ++ Y]/S1 in cohXY.
have ccsS1S: cfConjC_subset S1 S.
  rewrite /S1 /=; split; first by rewrite cat_uniq uX uY andbT; apply/hasPn.
    by apply/allP; rewrite all_cat !(introT allP).
  by move=> xi; rewrite !mem_cat => /orP[/ccX|/ccY]->; rewrite ?orbT.
move: {2}_.+1 (leq_addr (size S1) (size S).+1) => n.
elim: n => // [|n IHn] in (S2) S1 ccsS1S cohXY * => lb_n.
  by rewrite ltnNge ?uniq_leq_size // in lb_n; have [] := ccsS1S.
have sXYS1: {subset X ++ Y <= S1} by apply/mem_subseq/suffix_subseq.
without loss /allPn[psi /= Spsi notS1psi]: / ~~ all (mem S1) S.
  by case: allP => [/subset_coherent-cohS _ | _ cohS]; apply: cohS.
apply: (IHn [:: psi, psi^* & S2]%CF) => [|{lb_n}|]; last by rewrite !addnS leqW.
  by have [_ _ ccS] := uccS; apply: extend_cfConjC_subset.
have /seqIndC1P[i nzi Dpsi] := Spsi.
have ltZH': Z \proper H'.
  rewrite properEneq (contraNneq _ notS1psi) // => eqZH'; apply: sXYS1.
  rewrite mem_cat Dpsi !mem_seqInd ?normal1 //.
  by rewrite !inE sub1G andbT subGcfker nzi eqZH' orNb.
have Seta1: eta1 \in S1 by rewrite !mem_cat Yeta1 !orbT.
apply: (extend_coherent scohS ccsS1S Seta1) => {Seta1}//; split=> //.
  rewrite (uniY _ Yeta1) Dpsi cfInd1 // oW1 dvdC_mulr //.
  by rewrite Cint_Cnat ?Cnat_irr1.
rewrite !big_cat /= addrCA sum_seqIndD_square ?normal1 ?sub1G // ltr_spaddr //.
  have /irrY/irrP[j Deta1] := Yeta1; have [_ sS1S _] := ccsS1S.
  rewrite (big_rem eta1 Yeta1) addrCA -big_cat big_seq ltr_spaddl //=.
    by rewrite Deta1 cfnorm_irr divr1 exprn_gt0 ?irr1_gt0.
  apply/sumr_ge0=> phi YS2phi; rewrite divr_ge0 ?cfnorm_ge0 ?exprn_ge0 //.
  rewrite char1_ge0 ?(seqInd_char (sS1S _ _)) //.
  by move: YS2phi; rewrite !mem_cat => /orP[-> | /mem_rem->]; rewrite ?orbT.
rewrite indexg1 -(Lagrange_index sHL sZH) -oW1 natrM mulrC -mulrA.
rewrite uniY ?ler_wpmul2l ?ler0n -?(@natrB _ _ 1) // -natrM.
suffices ubW1: (#|W1|.*2 ^ 2 <= #|H : Z| * (#|Z| - 1) ^ 2)%N.
  have chi1_ge0: 0 <= 'chi_i 1%g by rewrite char1_ge0 ?irr_char.
  rewrite Dpsi cfInd1 // -oW1 -(@ler_pexpn2r _ 2) ?rpredM ?rpred_nat //.
  rewrite -natrX expnMn mulnAC natrM mulrA -natrM exprMn -natrX mul2n.
  rewrite ler_pmul ?ler0n ?exprn_ge0 ?(ler_trans (irr1_bound i)) ?ler_nat //.
  rewrite dvdn_leq ?indexgS ?(subset_trans sZZH) //=.
  by rewrite -cap_cfcenter_irr bigcap_inf.
have nZW1 := subset_trans sW1L nZL.
have tiZW1: Z :&: W1 = 1%g by rewrite coprime_TIg ?(coprimeSg sZH).
have [in_caseA | in_caseB] := boolP caseA.
  rewrite (leq_trans _ (leq_pmull _ _)) ?leq_exp2r // subn1 -ltnS prednK //.
  suffices frobZW1: [Frobenius Z <*> W1 = Z ><| W1].
    by apply: ltn_odd_Frobenius_ker frobZW1 (oddSg _ oddL); apply/joing_subP.
  have [|/c2_ptiL[_ _ prW1H _]] := boolP case_c1; first exact: Frobenius_subl.
  apply/Frobenius_semiregularP; rewrite ?sdprodEY // => x W1x; apply/trivgP.
  by rewrite /= -(setIidPl sZH) -setIA -(trivgP in_caseA) prW1H ?setSI.
rewrite (leq_trans _ (leq_pmulr _ _)) ?expn_gt0 ?orbF ?subn_gt0 ?cardG_gt1 //.
rewrite -(Lagrange_index sH'H sZH') leq_mul // ltnW //.
  have tiH'W1: H' :&: W1 = 1%g by rewrite coprime_TIg ?(coprimeSg sH'H).
  rewrite (card_isog (quotient_isog (subset_trans sW1L nH'L) tiH'W1)).
  rewrite -card_quotient ?gFnorm // (ltn_odd_Frobenius_ker frobL1) //.
  exact: quotient_odd.
suffices frobHW1Z: [Frobenius (H' / Z) <*> (W1 / Z) = (H' / Z) ><| (W1 / Z)].
  rewrite (card_isog (quotient_isog nZW1 tiZW1)).
  rewrite -card_quotient ?(subset_trans sH'H) //.
  apply: ltn_odd_Frobenius_ker frobHW1Z (oddSg _ (quotient_odd Z oddL)).
  by rewrite join_subG !quotientS.
suffices: [Frobenius (L / Z) = (H / Z) ><| (W1 / Z)].
  apply: Frobenius_subl (quotientS Z sH'H) _.
    by rewrite quotient_neq1 // (normalS sZH' sH'H).
  by rewrite quotient_norms ?(subset_trans sW1L).
apply: (Frobenius_coprime_quotient defL nsZL) => //.
split=> [|x W1x]; first exact: sub_proper_trans sZH' ltH'H.
by rewrite /Z ifN //; have /caseB_P[/c2_ptiL[_ _ ->]] := in_caseB.
Qed.

End Six.



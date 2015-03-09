(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset center.
Require Import fingroup morphism perm automorphism quotient action zmodp.
Require Import gfunctor gproduct cyclic pgroup commutator gseries nilpotent.
Require Import sylow abelian maximal hall frobenius.
Require Import matrix mxalgebra mxrepresentation vector ssrnum algC algnum.
Require Import classfun character inertia vcharacter integral_char. 
Require Import PFsection1 PFsection2 PFsection3 PFsection4 PFsection5.

(******************************************************************************)
(* This file covers Peterfalvi, Section 6:                                    *)
(* Some Coherence Theorems                                                    *)
(* Defined here:                                                              *)
(*   odd_Frobenius_quotient K L M <->                                         *)
(*      L has odd order, M <| L, K with K / M is nilpotent, and L / H1 is a   *)
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
Implicit Types H K L M : {group gT}.

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
Let ccS M : conjC_closed (S M). Proof. exact: cfAut_seqInd. Qed.
Let uniqS M : uniq (S M). Proof. exact: seqInd_uniq. Qed.
Let nrS : ~~ has cfReal calS. Proof. by case: scohS => [[]]. Qed.

Lemma exists_linInd M :
  M \proper K -> M <| K -> exists2 phi, phi \in S M & phi 1%g = #|L : K|%:R.
Proof.
move=> ltMK nsMK; have [sMK nMK] := andP nsMK.
have ntKM: (K / M)%g != 1%g by rewrite -subG1 quotient_sub1 // proper_subn.
have [r /andP[_ r1] ntr] := solvable_has_lin_char ntKM (quotient_sol M solK).
exists ('Ind[L, K] ('chi_r %% M)%CF); last first.
  by rewrite cfInd1 // cfModE // morph1 (eqP r1) mulr1.
apply/seqIndP; exists (mod_Iirr r); last by rewrite mod_IirrE.
rewrite !inE subGcfker mod_IirrE ?cfker_mod //= andbT.
apply: contraNneq ntr => /(canRL (mod_IirrK nsMK))->.
by rewrite quo_IirrE // irr0 ?cfker_cfun1 ?cfQuo_cfun1.
Qed.

(* This is Peterfalvi (6.2). *)
Lemma coherent_seqIndD_bound (A B C D : {group gT}) :
        [/\ A <| L, B <| L, C <| L & D <| L] ->
  (*a*) [/\ A \proper K, B \subset D, D \subset C, C \subset K
          & D / B \subset 'Z(C / B)]%g ->
  (*b1*) coherent (S A) L^# tau ->
  (*b2*) coherent (S B) L^# tau
  \/ #|K : A|%:R - 1 <= 2%:R * #|L : C|%:R * sqrtC #|C : D|%:R.
Proof.
move=> [nsAL nsBL nsCL nsDL] [ltAK sBD sDC sCK sDbZC] cohA.
have [|not_ineq] := boolP (_ <= _); [by right | left].
have sBC := subset_trans sBD sDC; have sBK := subset_trans sBC sCK.
have [sAK nsBK] := (proper_sub ltAK, normalS sBK sKL nsBL).
have{sBC} [nsAK nsBC] := (normalS sAK sKL nsAL, normalS sBC sCK nsBK).
pose wf S1 := [/\ uniq S1, {subset S1 <= calS} & conjC_closed S1].
pose S1 := [::] ++ S A; set S2 := [::] in S1; rewrite -[S A]/S1 in cohA.
have wfS1: wf S1 by split; [apply: uniqS | apply: sSS | apply: ccS].
move: {2}_.+1 (ltnSn (size calS - size S1)) => n.
elim: n => // n IHn in (S2) S1 wfS1 cohA *; rewrite ltnS => leSnS1.
have [uniqS1 sS1S ccS1] := wfS1.
have [sAB1 | /allPn[psi /= SBpsi notS1psi]] := altP (@allP _ (mem S1) (S B)).
  by apply: subset_coherent cohA.
have [neq_psi_c SBpsic] := (hasPn nrS _ (sSS SBpsi), ccS SBpsi).
have wfS1': wf [:: psi, psi^* & S1]%CF.
  split=> [|xi|xi]; rewrite /= !inE 1?andbC.
  - rewrite negb_or eq_sym neq_psi_c notS1psi uniqS1 (contra (ccS1 _)) //.
    by rewrite cfConjCK.
  - by case/predU1P=> [|/predU1P[|/sS1S]] -> //; rewrite (@sSS B).
  do 2![case/predU1P=> [-> |]; first by rewrite ?cfConjCK eqxx ?orbT // eq_sym].
  by move/ccS1=> ->; rewrite !orbT.
apply: (IHn [:: psi, psi^* & S2]%CF) => //; last first.
  rewrite -subSn ?uniq_leq_size //; try by case: wfS1'.
  by rewrite /= subSS (leq_trans _ leSnS1) // leq_sub2l ?leqW.
have [phi SAphi phi1] := exists_linInd ltAK nsAK.
have: [/\ phi \in S1, psi \in calS & psi \notin S1].
  by rewrite mem_cat SAphi orbT (@sSS B).
have /seqIndP[i /setDP[kBi _] def_psi] := SBpsi; rewrite inE in kBi.
move/(extend_coherent scohS); apply; rewrite // {phi SAphi}phi1; split=> //.
  by rewrite def_psi cfInd1 // dvdC_mulr // CintE Cnat_irr1.
have Spos xi: xi \in calS -> 0 <= xi 1%g by move/Cnat_seqInd1/Cnat_ge0.
rewrite big_cat sum_seqIndD_square //= -subr_gt0 -addrA ltr_paddl //=.
  rewrite big_seq sumr_ge0 // => xi S2xi.
  by rewrite !mulr_ge0 ?invr_ge0 ?cfnorm_ge0 ?Spos ?sS1S // mem_cat S2xi.
rewrite mulrC -mulrBl pmulr_rgt0 ?gt0CiG // subr_gt0.
rewrite real_ltrNge ?rpredB ?rpredM ?rpred_nat ?rpred1 //; last first.
  by rewrite realE Spos ?(sSS SBpsi).
apply: contra not_ineq => /ler_trans-> //.
rewrite -mulrA ler_pmul2l ?ltr0n // def_psi cfInd1 //.
rewrite -(Lagrange_index sKL sCK) natrM -mulrA ler_pmul2l ?gt0CiG //.
exact: irr1_bound_quo sDbZC.
Qed.

(* This is Peterfalvi, Theorem (6.3). *)
Theorem bounded_seqIndD_coherent M H H1 :
   [/\ M <| L, H <| L & H1 <| L] ->
   [/\ M \subset H1, H1 \subset H & H \subset K] ->
 (*a*) nilpotent (H / M)%g ->
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
  have minBb: minnormal (A / B)%g (L / B)%g.
    apply/mingroupP; split=> [|Db /andP[ntDb nDLb] sDAb].
      by rewrite -subG1 quotient_sub1 // not_sAB quotient_norms.
    have: Db <| (L / B)%g by rewrite /normal (subset_trans sDAb) ?quotientS.
    case/(inv_quotientN nsBL)=> D defDb sBD /andP[sDL nDL].
    apply: contraNeq ntDb => neqDAb; rewrite defDb quotientS1 //.
    case/maxgroupP: maxB => /= _ /(_ D) {1}<- //.
    rewrite -(quotient_proper (normalS sBD sDL nsBL)) // -defDb.
    by rewrite properEneq sDAb neqDAb.
  apply/setIidPl; case/mingroupP: minBb => /andP[ntAb nALb].
  apply; rewrite ?subsetIl //.
  have nZHb := char_norm_trans (center_char (H / B)) (quotient_norms _ nHL).
  rewrite andbC normsI //= meet_center_nil //=; last first.
    by rewrite quotient_normal // (normalS sAH sHL).
  suffices /homgP[f /= <-]: (H / B)%g \homg (H / M)%g by rewrite morphim_nil.
  by apply: homg_quotientS; rewrite ?(subset_trans sHL) ?normal_norm.
have [defA | ltAH] := eqVproper sAH.
  by rewrite addn1 defA indexgg in lbHA.
have [sAK ltAK] := (subset_trans sAH sHK, proper_sub_trans ltAH sHK).
case: (@coherent_seqIndD_bound A B H A) => // /idPn[].
apply: contraL lbHA; rewrite -ltnNge -ltC_nat -(Lagrange_index sHK sAH) natrM.
set x := #|H : A|%:R => ub_x.
have nz_x2: sqrtC x != 0 by rewrite sqrtC_eq0 neq0CiG.
have x2_gt0: 0 < sqrtC x by rewrite ltr_def nz_x2 sqrtC_ge0 ler0n.
have{ub_x}: sqrtC x - (sqrtC x)^-1 <= (2 * #|L : K|)%:R.
  rewrite -(ler_pmul2r (gt0CiG K H)) -natrM -mulnA Lagrange_index //.
  rewrite natrM -(ler_pmul2r x2_gt0) mulrC mulrBl mulrBr.
  rewrite !mulrA -expr2 sqrtCK divff // (ler_trans _ ub_x) // mulrC.
  by rewrite ler_add2l ler_opp2 mul1r ler1n.
rewrite -(@ler_pexpn2r _ 2) -?topredE /= ?ler0n //; last first.
  rewrite subr_ge0 -(ler_pmul2r x2_gt0) -expr2 mulVf // sqrtCK.
  by rewrite ler1n.
rewrite -natrX expnMn -(ler_add2r 2%:R) -addnS natrD.
apply: ltr_le_trans; rewrite sqrrB // exprVn sqrtCK divff //.
by rewrite addrAC subrK addrC -subr_gt0 addrK invr_gt0 gt0CiG.
Qed.

(* This is the statement of Peterfalvi, Hypothesis (6.4). *)
Definition odd_Frobenius_quotient M (H1 := K^`(1) <*> M) :=
  [/\ (*a*) odd #|L|,
      (*b*) [/\ M <| L, M \subset K & nilpotent (K / M)]
    & (*c*) [Frobenius L / H1 with kernel K / H1] ]%g.

(* This is Peterfalvi (6.5). *)
Lemma non_coherent_chief M (H1 := (K^`(1) <*> M)%G) :
   odd_Frobenius_quotient M ->
   coherent (S M) L^# tau
\/ [/\ (*a*) chief_factor L H1 K /\ (#|K : H1| <= 4 * #|L : K| ^ 2 + 1)%N
     & (*b*) exists2 p : nat, p.-group (K / M)%g /\ ~~ abelian (K / M)%g
     & (*c*) ~~ (#|L : K| %| p - 1)].
Proof.
case=> oddL [nsML sMK nilKb]; rewrite /= -(erefl (gval H1)) => frobLb.
set e := #|L : K|; have odd_e: odd e := dvdn_odd (dvdn_indexg L K) oddL.
have{odd_e} mod1e_lb m: (odd m -> m > 1 -> m == 1 %[mod e] -> 2 * e + 1 <= m)%N.
  move=> odd_m m_gt1; rewrite eqn_mod_dvd ?(ltnW m_gt1) //.
  rewrite -[m]odd_double_half odd_m subn1 /= -mul2n addn1 ltnS leq_pmul2l //.
  rewrite Gauss_dvdr; last by rewrite coprime_sym prime_coprime // dvdn2 odd_e.
  by apply: dvdn_leq; rewrite -(subnKC m_gt1).
have nsH1L: H1 <| L by rewrite normalY // (char_normal_trans (der_char 1 K)).
have sH1K: H1 \subset K by rewrite join_subG der_sub.
have cohH1: coherent (S H1) L^# tau.
  apply: uniform_degree_coherence (subset_subcoherent scohS _) _ => //.
  apply/(@all_pred1_constant _ #|L : K|%:R)/allP=> _ /mapP[chi Schi ->] /=.
  have [i /setIdP[_]] := seqIndP Schi; rewrite inE join_subG -lin_irr_der1.
  by do 2![case/andP]=> _ /eqP chi1 _ ->; rewrite cfInd1 // chi1 mulr1.
have sMH1: M \subset H1 by apply: joing_subr.
have [ubK | lbK] := leqP; last by left; apply: bounded_seqIndD_coherent lbK.
have{ubK} ubK: (#|K : H1| < (2 * e + 1) ^ 2)%N.
  rewrite sqrnD expnMn (leq_ltn_trans ubK) // -subn_gt0 addKn.
  by rewrite !muln_gt0 indexg_gt0.
have [-> | neqMH1] := eqVneq M H1; [by left | right].
have{neqMH1} ltMH1: M \proper H1 by rewrite properEneq neqMH1.
have{frobLb} [[E1b frobLb] [sH1L nH1L]] := (existsP frobLb, andP nsH1L).
have [defLb ntKb _ _ /andP[sE1L _]] := Frobenius_context frobLb.
have nH1K: K \subset 'N(H1) := subset_trans sKL nH1L.
have chiefH1: chief_factor L H1 K.
  have ltH1K: H1 \proper K by rewrite /proper sH1K -quotient_sub1 ?subG1.
  rewrite /chief_factor nsKL andbT; apply/maxgroupP; rewrite ltH1K.
  split=> // H2 /andP[ltH2K nH2L] sH12; have sH2K := proper_sub ltH2K.
  have /eqVproper[// | ltH21] := sH12; case/idPn: ubK; rewrite -leqNgt.
  have dv_e H3: H1 \subset H3 -> H3 \subset K -> L \subset 'N(H3) ->
    #|H3 : H1| == 1 %[mod e].
  - move=> sH13 sH3K nH3L; rewrite eqn_mod_dvd // subn1.
    rewrite /e -(index_quotient_eq _ sKL nH1L) ?subIset ?sH1K ?orbT //.
    rewrite -[#|_ : _|]divgS ?quotientS // -(sdprod_card defLb) mulKn //.
    rewrite -card_quotient ?(subset_trans (subset_trans sH3K sKL)) //.
    rewrite regular_norm_dvd_pred ?(subset_trans sE1L) ?quotient_norms //.
    apply: semiregular_sym; apply: sub_in1 (Frobenius_reg_compl frobLb).
    by apply/subsetP; rewrite setSD ?quotientS.
  have dv_H21 := dv_e H2 sH12 sH2K nH2L.
  have dv_KH2: #|K : H2| == 1 %[mod e].
    have:= dv_e K sH1K (subxx K) nKL; rewrite -(Lagrange_index sH2K sH12).
    by rewrite -modnMmr (eqP dv_H21) modnMmr muln1.
  have odd_iK := dvdn_odd (dvdn_indexg _ _) (oddSg (subset_trans _ sKL) oddL).
  have iK_gt1 H3 H4: H4 \proper H3 -> (#|H3 : H4| > 1)%N.
    by rewrite indexg_gt1 => /andP[].
  by rewrite -(Lagrange_index sH2K sH12) leq_mul ?mod1e_lb ?odd_iK ?iK_gt1.
split=> //; have nMK := subset_trans sKL (normal_norm nsML).
have not_abKb: ~~ abelian (K / M).
  apply: contra (proper_subn ltMH1) => /derG1P/trivgP.
  rewrite /= join_subG subxx andbT -quotient_der ?quotient_sub1 //.
  exact: subset_trans (der_sub 1 K) nMK.
have /is_abelemP[p p_pr /and3P[pKb _ _]]: is_abelem (K / H1)%g.
  have: solvable (K / H1)%g by apply: quotient_sol solK.
  by case/(minnormal_solvable (chief_factor_minnormal chiefH1)).  
have [_ p_dv_Kb _] := pgroup_pdiv pKb ntKb.
have iso3M := third_isog sMH1 (normalS sMK sKL nsML) (normalS sH1K sKL nsH1L).
have pKM: p.-group (K / M)%g.
  have /dprodP[_ defKM cKMpp' tiKMpp'] := nilpotent_pcoreC p nilKb.
  rewrite -defKM (eqP (forall_inP (nilpotent_sol nilKb) 'O_p^'(_)%G _)).
    by rewrite mulg1 pcore_pgroup.
  have /isomP[inj_quo im_quo] := quotient_isom (cents_norm cKMpp') tiKMpp'.
  rewrite subsetI pcore_sub /= -(injmSK inj_quo) // (morphim_der _ 1) //.
  rewrite {inj_quo}im_quo /= -[Q in Q^`(1)%g]quotientMidl defKM.
  rewrite -quotient_der ?gFnorm ?quotientS //.
  rewrite -quotient_sub1 ?(subset_trans (pcore_sub _ _) (der_norm _ _)) //.
  rewrite -[(_ / _)%g]setIid coprime_TIg //.
  apply: pnat_coprime (quotient_pgroup _ (pcore_pgroup _ _)).
  apply: pgroupS (quotientS _ (pcore_sub _ _)) _.
  rewrite /= -quotient_der // -(quotientYidr (subset_trans (der_sub 1 K) nMK)).
  by rewrite (isog_pgroup _ iso3M) ?(normalS sMK sKL nsML).
exists p => //; apply: contra not_abKb => e_dv_p1.
rewrite cyclic_abelian // Phi_quotient_cyclic //.
have /homgP[f <-]: (K / M / 'Phi(K / M) \homg K / H1)%g.
  apply: homg_trans (isog_hom iso3M).
  rewrite homg_quotientS ?gFnorm ?quotient_norms //=.
  rewrite quotientYidr ?(subset_trans (der_sub 1 K)) // quotient_der //.
  by rewrite (Phi_joing pKM) joing_subl.
rewrite {f}morphim_cyclic // abelian_rank1_cyclic; last first.
  by rewrite sub_der1_abelian ?joing_subl.
rewrite (rank_pgroup pKb) (leq_trans (p_rank_le_logn _ _)) //.
rewrite -ltnS -(ltn_exp2l _ _ (prime_gt1 p_pr)) -p_part part_pnat_id //.
rewrite card_quotient // (leq_trans ubK) // leq_exp2r //.
have odd_p: odd p := dvdn_odd p_dv_Kb (quotient_odd _ (oddSg sKL oddL)).
by rewrite mod1e_lb // ?eqn_mod_dvd ?prime_gt0 ?prime_gt1.
Qed.

(* This is Peterfalvi (6.6). *)
Lemma seqIndD_irr_coherence (Z : {group gT}) (calX := seqIndD K L Z 1) :
    odd_Frobenius_quotient 1%G ->
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
have [|[]] := non_coherent_chief Frob_quo1.
  by apply: subset_coherent; apply: seqInd_sub.
have [oddL _] := Frob_quo1; rewrite /= joingG1 => frobLb _ [p []].
set e := #|L : K|; have e_gt0: (e > 0)%N by apply: indexg_gt0.
have isoK1 := isog_symr (quotient1_isog K).
rewrite (isog_abelian isoK1) {isoK1}(isog_pgroup _ isoK1).
have [-> | ntK pK _ not_e_dv_p1] := eqsVneq K [1]; first by rewrite abelian1.
have{ntK} [p_pr p_dv_K _] := pgroup_pdiv pK ntK.
set Y := calX; pose d (xi : 'CF(L)) := logn p (truncC (xi 1%g) %/ e).
have: conjC_closed Y by apply: cfAut_seqInd.
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
have ccY': conjC_closed Y'.
  move=> xi; rewrite !(inE, mem_rem_uniq) ?rem_uniq //.
  by rewrite !(inv_eq (@cfConjCK _ _)) cfConjCK => /and3P[-> -> /ccY->].
have Xchi := sYX _ Ychi; have defY: perm_eq [:: chi, chi^*%CF & Y'] Y.
  rewrite (perm_eqrP (perm_to_rem Ychi)) perm_cons perm_eq_sym perm_to_rem //.
  by rewrite mem_rem_uniq ?inE ?ccY // (seqInd_conjC_neq _ _ _ Xchi).
apply: perm_eq_coherent (defY) _.
have d_chic: d chi^*%CF = d chi.
  by rewrite /d cfunE conj_Cnat // (Cnat_seqInd1 Xchi).
have /andP[uniqY' Y'x1]: uniq Y' && (xi1 \in Y').
  rewrite !(inE, mem_rem_uniq) ?rem_uniq // Yxi1 andbT -negb_or.
  by apply: contraL lt_xi1_chi => /pred2P[] ->; rewrite ?d_chic ltnn.
have xi1P: [/\ xi1 \in Y', chi \in calS & chi \notin Y'].
  by rewrite Y'x1 sYS ?(inE, mem_rem_uniq) ?rem_uniq // eqxx andbF.
have sY'Y: {subset Y' <= Y} by move=> xi /mem_rem/mem_rem.
apply: (extend_coherent scohS) xi1P _; first by split=> // xi /sY'Y/sYS. 
have{defX} defX: perm_eq (Y' ++ X'') calX.
  by rewrite (perm_catCA Y' [::_; _]) catA -(perm_eqrP defX) perm_cat2r.
have{d_chic} le_chi_X'': {in X'', forall xi, d chi <= d xi}%N.
  by move=> xi /or3P[/eqP-> | /eqP-> | /leYX'->] //; rewrite d_chic.
rewrite !Ndg ?sYX // dvdC_nat dvdn_pmul2l // dvdn_exp2l 1?ltnW //; split=> //.
  apply: IHm defX ccY' => [|xi xi' /sY'Y/leYchi le_xi_chi /le_chi_X''].
    by rewrite -ltnS // (leq_trans _ leYm) // -(perm_eq_size defY) ltnW.
  exact: leq_trans.
have pos_p n: (0 < p ^ n)%N by rewrite expn_gt0 prime_gt0.
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
  by rewrite muln_gt0 expn_gt0 e_gt0 [_ Y'](bigD1_seq xi1) //= addn_gt0 pos_p.
have coep: coprime e p.
  have:= Frobenius_ker_coprime frobLb; rewrite coprime_sym.
  have /andP[_ nK'L] := char_normal_trans (der_char 1 K) nsKL.
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
(* In (6.8) we only know initially the P is Sylow in L; perhaps the lemma     *)
(* should be stated with this equivalent (but weaker) assumption.             *)
Lemma constant_irr_mod_TI_Sylow (Z L P : {group gT}) p i :
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
  rewrite /dC /C; have /imsetP[_ _ ->{k} /class_transr <-] := enum_valP k.
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
suffices Ea2 l (phi := 'chi[G]_l):
  kerZ l -> (phi z *+ a2 i1 i1 == phi 1%g + phi z *+ a2 i1 i2 %[mod #|P|])%A.
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
move=> kerZphi; pose alpha := 'omega_l['K_i1]; pose phi1 := phi 1%g.
have tiZG: {in Z^#, forall y, 'C_G[y] \subset L}.
  move=> y /setD1P[nty /(subsetP sZP)Py].
  apply/subsetP=> u /setIP[Gu /cent1P cuy].
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
  rewrite (contra _ ntCs) // [C s]defCs => /class_transr.
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
  rewrite rCi10 -!/(C _) !CE -eq_invg_mul => /imsetP[x Gx ->] /class_transr <-.
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
Theorem Sibley_coherence (L H W1 : {group gT}) :
  (*a*) [/\ odd #|L|, nilpotent H & normedTI H^# G L] ->
  (*b*) let calS := seqIndD H L H 1 in let tau := 'Ind[G, L] in
  (*c*) [\/ (*c1*) [Frobenius L = H ><| W1]
         |  (*c2*) exists2 W2 : {group gT}, prime #|W2| /\ W2 \subset H^`(1)%G
               & exists A0, exists W : {group gT}, exists defW : W1 \x W2 = W,
                 prime_Dade_hypothesis G L H H H^# A0 defW] ->
  coherent calS L^# tau.
Proof.
set A := H^# => [][oddL nilH tiA] S tau structL.
set case_c1 := [Frobenius L = H ><| W1] in structL.
have sLG: L \subset G by have [_ _ /eqP <-] := and3P tiA; apply: subsetIl.
have [defL ntH ntW1]: [/\ H ><| W1 = L, H :!=: 1 & W1 :!=: 1]%g.
  have [/Frobenius_context[]// | [W2 _ [A0 [W [defW []]]]]] := structL.
  by move=> _ [[-> -> _ _] [ntW2 /subG1_contra->]].
have [nsHL _ /mulG_sub[sHL sW1L] _ _] := sdprod_context defL.
have [uccS nrS]: cfConjC_subset S S /\ ~~ has cfReal S.
  by do 2?split; rewrite ?seqInd_uniq ?seqInd_notReal //; apply: cfAut_seqInd.
have defZS: 'Z[S, L^#] =i 'Z[S, A] by apply: zcharD1_seqInd.
have c1_irr: case_c1 -> {subset S <= irr L}.
  move/FrobeniusWker=> frobL _ /seqIndC1P[i nz_i ->].
  exact: irr_induced_Frobenius_ker.
move defW2: 'C_H(W1)%G => W2; move defW: (W1 <*> W2)%G => W.
have{defW} defW: W1 \x W2 = W.
  rewrite -defW dprodEY // -defW2 ?subsetIr // setICA setIA.
  by have [_ _ _ ->] := sdprodP defL; rewrite setI1g.
pose V := cyclicTIset defW; pose A0 := A :|: class_support V L.
pose c2hyp := prime_Dade_hypothesis G L H H A A0 defW.
have c1W2: case_c1 -> W2 = 1%G by move/Frobenius_trivg_cent/group_inj <-.
have{structL} c2W2: ~~ case_c1 -> [/\ prime #|W2|, W2 \subset H^`(1)%G & c2hyp].
  case: structL => [-> // | [W20 [prW20 sW20H'] W20hyp] _].
  have{W20hyp} [A00 [W0 [defW0 W20hyp]]] := W20hyp.
  suffices /group_inj defW20: W2 :=: W20.
    have eqW0: W0 = W by apply: group_inj; rewrite -defW0 -defW20.
    rewrite -defW20 eqW0 in prW20 sW20H' defW0 W20hyp; split=> //.
    rewrite /c2hyp (eq_irrelevance defW defW0) /A0.
    by have [_ _ <-] := prDade_def W20hyp.
  have [[_ _ _ cycW1] [_ _ _ prW120] _] := prDade_prTI W20hyp.
  have [x defW1] := cyclicP cycW1; rewrite -defW2 /= defW1 cent_cycle prW120 //.
  by rewrite !inE defW1 cycle_id -cycle_eq1 -defW1 ntW1.
have{c2W2} [prW2 sW2H' c2W2] := all_and3 c2W2.
have{sW2H'} sW2H': W2 \subset H^`(1)%G.
  by have [/c1W2-> | /sW2H'//] := boolP case_c1; apply: sub1G.
pose sigma := cyclicTIiso (c2W2 _).
have [R scohS oRW]: exists2 R, subcoherent S tau R & forall c2 : ~~ case_c1,
  {in [predI S & irr L] & irr W, forall phi w, orthogonal (R phi) (sigma c2 w)}.
- have sAG: A \subset G^# by rewrite setSD // (subset_trans (normal_sub nsHL)).
  have Itau: {in 'Z[S, L^#], isometry tau, to 'Z[irr G, G^#]}.
    split=> [xi1 xi2 | xi].
      rewrite !defZS => /zchar_on Axi1 /zchar_on Axi2.
      exact: normedTI_isometry Axi1 Axi2.
    rewrite !zcharD1E => /andP[Zxi /eqP xi1_0].
    rewrite cfInd1 // xi1_0 mulr0 eqxx cfInd_vchar //.
    by apply: zchar_trans_on Zxi; apply: seqInd_vcharW.
  have [/= Hc1 | Hc2] := boolP (idfun case_c1).
    suffices [R]: {R | subcoherent S tau R} by exists R => // /negP[].
    by apply: irr_subcoherent => //; first by case: uccS (c1_irr Hc1).
  have ddA0 := c2W2 Hc2.
  have [R [subcohR oRW _]] := prDade_subcoherent ddA0 uccS nrS.
  exists R => [|not_c1 phi w irrSphi irr_w]; last first.
    by rewrite /sigma -(cycTIiso_irrel ddA0) oRW.
  set tau0 := Dade _ in subcohR.
  have Dtau: {in 'CF(L, A), tau =1 tau0}.
    have nAL: L \subset 'N(A) by rewrite normD1 normal_norm.
    move=> phi Aphi; rewrite /tau0 -(restr_DadeE ddA0 (subsetUl _ _) nAL) //.
    by rewrite /restr_Dade Dade_Ind.
  have [Sok _ oSS Rok oRR] := subcohR; split=> // phi Sphi.
  have [ZR oNR <-] := Rok _ Sphi; split=> //.
  by rewrite Dtau ?irr_vchar_on ?sub_conjC_vchar ?(seqInd_vchar nsHL Sphi).
have [nsH'H nsH'L] := (der_normal 1 H, char_normal_trans (der_char 1 H) nsHL).
have [nH'L solH] := (normal_norm nsH'L, nilpotent_sol nilH).
have ltH'H: H^`(1)%g \proper H by rewrite ?(nil_comm_properl nilH) ?subsetIidl.
have coHW1: coprime #|H| #|W1|.
  have [/Frobenius_coprime// | /c2W2[_ [[_ _]]]] := boolP case_c1.
  by rewrite (coprime_sdprod_Hall_r defL).
have oW1: #|W1| = #|L : H| by rewrite -divgS // -(sdprod_card defL) mulKn.
have frobL1: [Frobenius L / H^`(1) = (H / H^`(1)) ><| (W1 / H^`(1))]%g.
  apply: (Frobenius_coprime_quotient defL nsH'L) => //; split=> // x W1x.
  have [/Frobenius_reg_ker-> //|] := boolP case_c1; first exact: sub1G.
  by case/c2W2=> _ [_ [_ _ _ ->]].
have odd_frobL1: odd_Frobenius_quotient H L 1.
  have ? := FrobeniusWker frobL1.
  by split=> //=; rewrite ?joingG1 // normal1 sub1G quotient_nil.
without loss [/p_groupP[p p_pr pH] not_cHH]: / p_group H /\ ~~ abelian H.
  have [//| [_] [p []]] := non_coherent_chief nsHL solH scohS odd_frobL1.
  rewrite (isog_abelian (quotient1_isog H)) -(isog_pgroup p (quotient1_isog H)).
  by move=> /pgroup_p-> -> _; apply.
have sylH: p.-Sylow(G) H. (* required for (6.7) *)
  have sylH: p.-Sylow(L) H.
    apply/and3P; split=> //; rewrite -oW1 p'natE // -prime_coprime //.
    by case/pgroup_pdiv: pH coHW1 => // _ _ [m ->]; rewrite coprime_pexpl.
  have [P sylP sHP] := Sylow_superset (subset_trans sHL sLG) pH.
  have [sPG pP _] := and3P sylP; have nilP := pgroup_nil pP.
  rewrite -(nilpotent_sub_norm nilP sHP) // (sub_normal_Hall sylH) //.
    exact: pgroupS (subsetIl P _) pP.
  by have [_ _ /eqP <-] := and3P tiA; rewrite normD1 setSI.
pose caseA := 'Z(H) :&: W2 == [1].
have caseB_P: ~~ caseA -> [/\ ~~ case_c1, W2 :!=: [1] & W2 \subset 'Z(H)].
  rewrite /caseA; have [-> |] := eqsVneq W2 [1]; first by rewrite setIg1 eqxx.
  have [/c1W2->/eqP[]// | /prW2 pW2 ->] := boolP case_c1.
  by rewrite setIC => /prime_meetG->.
pose Z := if caseA then ('Z(H) :&: H^`(1))%G else W2.
have /subsetIP[sZZ sZH']: Z \subset 'Z(H) :&: H^`(1)%g.
  by rewrite /Z; case: ifPn => // /caseB_P[/c2W2[]] *; apply/subsetIP.
have caseB_cZL: ~~ caseA -> Z \subset 'Z(L).
  move=> inB; have [_ _ /subsetIP[sW2H cW2H]] := caseB_P inB.
  have [_ mulHW1 _ _] := sdprodP defL.
  rewrite /Z (negPf inB) subsetI (subset_trans sW2H) //.
  by rewrite -mulHW1 centM subsetI cW2H -defW2 subsetIr.
have nsZL: Z <| L.
  have [inA | /caseB_cZL/sub_center_normal//] := boolP caseA.
  by rewrite /Z inA (char_normal_trans _ nsHL) // charI ?gFchar.
have ntZ: Z :!=: 1%g.
  rewrite /Z; case: ifPn => [_ | /caseB_P[]//].
  by rewrite /= setIC meet_center_nil // (sameP eqP derG1P).
have nsZH := sub_center_normal sZZ; have [sZH nZH] := andP nsZH.
have regZL: {in Z^# &, forall x y, #|'C_L[x]| = #|'C_L[y]| }.
  have [inA | /caseB_cZL cZL] := boolP caseA; last first.
    suffices defC x: x \in Z^# -> 'C_L[x] = L by move=> x y /defC-> /defC->.
    by case/setD1P=> _ /(subsetP cZL)/setIP[_]; rewrite -sub_cent1 => /setIidPl.
  suffices defC x: x \in Z^# -> 'C_L[x] = H by move=> x y /defC-> /defC->.
  case/setD1P=> ntx Zx; have /setIP[Hx cHx] := subsetP sZZ x Zx.
  have [_ <- _ _] := sdprodP defL; rewrite -group_modl ?sub_cent1 //=.
  suffices ->: 'C_W1[x] = 1%g by rewrite mulg1.
  have [/Frobenius_reg_compl-> // | in_c2] := boolP case_c1; first exact/setD1P.
  have [_ [_ [_ _ _ regW1] _] _ _] := c2W2 in_c2.
  apply: contraNeq ntx => /trivgPn[y /setIP[W1y cxy] nty].
  rewrite -in_set1 -set1gE -((_ =P [1]) inA) -(regW1 y) 2!inE ?nty //.
  by rewrite inE cent1C cHx Hx.
have Zconst_modH :=
  constant_irr_mod_TI_Sylow sylH oddL tiA (And3 nsZL ntZ sZZ) regZL.
pose X := seqIndD H L Z 1; pose Y := seqIndD H L H H^`(1).
have ccsXS: cfConjC_subset X S by apply: seqInd_conjC_subset1.
have ccsYS: cfConjC_subset Y S by apply: seqInd_conjC_subset1.
have [[uX sXS ccX] [uY sYS ccY]] := (ccsXS, ccsYS).
have X'Y: {subset Y <= [predC X]}.
  move=> _ /seqIndP[i /setIdP[_ kH'i] ->]; rewrite inE in kH'i.
  by rewrite !inE mem_seqInd ?normal1 // !inE sub1G (subset_trans sZH').
have irrY: {subset Y <= irr L}.
  move=> _ /seqIndP[i /setIdP[not_kHi kH'i] ->]; rewrite !inE in not_kHi kH'i.
  have kH'iInd: H^`(1)%g \subset cfker ('Ind[L] 'chi_i).
    by rewrite sub_cfker_Ind_irr ?normal_norm.
  rewrite -(cfQuoK nsH'L kH'iInd) -cfIndQuo // -quo_IirrE //.
  set i1 := quo_Iirr _ i; have /irrP[k ->]: 'Ind 'chi_i1 \in irr (L / H^`(1)).
    apply: irr_induced_Frobenius_ker; first exact: FrobeniusWker frobL1.
    apply: contraNneq not_kHi; rewrite -(quo_IirrK nsH'H kH'i) -/i1 => ->.
    by rewrite mod_IirrE // irr0 cfMod_cfun1 ?cfker_cfun1.
  by rewrite -mod_IirrE ?mem_irr.
have uniY: {in Y, forall phi : 'CF(L), phi 1%g = #|W1|%:R}.
  move=> _ /seqIndP[i /setIdP[_ kH'i] ->]; rewrite inE -lin_irr_der1 in kH'i.
  rewrite cfInd1 // -divgS // -(sdprod_card defL) mulKn //.
  by case/andP: kH'i => _ /eqP->; rewrite mulr1.
have scohY: subcoherent Y tau R by apply: (subset_subcoherent scohS).
have [tau1 cohY]: coherent Y L^# tau.
  apply/(uniform_degree_coherence scohY)/(@all_pred1_constant _ #|W1|%:R).
  by apply/allP=> _ /mapP[phi Yphi ->]; rewrite /= uniY.
have [[Itau1 Ztau1] Dtau1] := cohY.
have [eta1 Yeta1]: exists eta1, eta1 \in Y.
  pose IY := Iirr_kerD H H H^`(1)%G.
  have [IY0 | [j IYj]] := set_0Vmem IY; last first.
    by exists ('Ind 'chi_j); apply/seqIndP; exists j.
  have /idPn[]: \sum_(j in IY) ('chi_j 1%g) ^+ 2 == 0 by rewrite IY0 big_set0.
  rewrite sum_Iirr_kerD_square ?der_sub // indexgg mul1r subr_eq0.
  by rewrite pnatr_eq1 indexg_eq1 proper_subn.
have caseA_coh12: caseA -> coherent (X ++ Y) L^# tau.
  move=> haveA.
  have scohX: subcoherent X tau R by apply: subset_subcoherent ccsXS.
  have irrX: {subset X <= irr L}.
    have [/c1_irr irrS | in_c2] := boolP case_c1.
      move=> phi Xphi; apply: irrS; apply: seqIndS phi Xphi.
      by rewrite Iirr_kerDS // (subset_trans sZH') ?der_sub.
    move/(_ in_c2) in prW2; have [_ ptiL _ _] := c2W2 in_c2.
    have [[_ _ _ cycW1] [ntW2 sW2H cycW2 prW1H] oddW] := ptiL.
    have nZL := normal_norm nsZL; have nZW1 := subset_trans sW1L nZL.
    have isoW2: (W2 / Z)%g \isog W2.
      apply/isog_symr/quotient_isog; first exact: subset_trans sW2H nZH.
      by rewrite -(setIidPr sZZ) setIAC ((_ =P [1]) haveA) setI1g.
    have [|defWb ptiLZ] := primeTIhyp_quotient ptiL _ sZH nsZL.
      by rewrite (isog_eq1 isoW2).
    pose Ichi := primeTI_Ires ptiL; pose IchiZ := primeTI_Ires ptiLZ.
    have eq_Ichi: codom (fun j1 => mod_Iirr (IchiZ j1)) =i codom Ichi.
      apply/subset_cardP.
        rewrite !card_codom; last first; try exact: prTIres_inj.
        apply: inj_comp (prTIres_inj ptiLZ).
          exact: can_inj (mod_IirrK (sub_center_normal sZZ)).
        by rewrite !card_ord !NirrE (nclasses_isog isoW2).
      apply/subsetP=> _ /codomP[/= j1 ->].
      have [[j2 /irr_inj->] | ] := prTIres_irr_cases ptiL (mod_Iirr (IchiZ j1)).
        exact: codom_f.
      case=> /idPn[]; rewrite mod_IirrE // cfIndMod // cfInd_prTIres.
      apply: contra (prTIred_not_irr ptiLZ j1) => /irrP[ell Dell].
      by rewrite -[_ j1]cfModK // Dell -quo_IirrE ?mem_irr // -Dell cfker_mod.
    move=> _ /seqIndP[k /setDP[_ kZ'k] ->].
    have [[j /irr_inj Dk] | [] //] := prTIres_irr_cases ptiL k.
    case/negP: kZ'k; have: k \in codom Ichi by rewrite Dk codom_f.
    by rewrite -eq_Ichi => /codomP[j1 ->]; rewrite !inE mod_IirrE ?cfker_mod.
  have [//|] := seqIndD_irr_coherence nsHL solH scohS odd_frobL1 _ irrX.
  rewrite -/X => defX [tau2 cohX]; have [[Itau2 Ztau2] Dtau2] := cohX.
  have [xi1 Xxi1 Nd]:
    exists2 xi1, xi1 \in X & forall xi, xi \in X -> (xi1 1%g %| xi 1%g)%C.
  - pose IX := Iirr_kerD H Z 1%G; have [i0 IXi0]: exists i0, i0 \in IX.
      apply/set0Pn; apply: contraNneq ntZ => IX_0.
      have: \sum_(i in IX) ('chi_i 1%g) ^+ 2 == 0 by rewrite IX_0 big_set0.
      rewrite sum_Iirr_kerD_square ?normal1 ?sub1G // indexg1 mulf_eq0.
      by rewrite (negPf (neq0CiG H Z)) subr_eq0 trivg_card1 -eqC_nat.
    have:= erefl [arg min_(i < i0 in IX) truncC ('chi_i 1%g)].
    have [//|{i0 IXi0} i1 IXi1 min_i1 _] := arg_minP.
    exists ('Ind 'chi_i1); first by apply/seqIndP; exists i1.
    move=> _ /seqIndP[i /min_i1 le_i1_i] ->; rewrite !cfInd1 //.
    have pHP := p_natP (pnat_dvd _ pH).
    move: (dvd_irr1_cardG i1) (dvd_irr1_cardG i) le_i1_i.
    rewrite !irr1_degree -!natrM !dvdC_nat => /pHP[m1 ->] /pHP[m ->].
    rewrite !natCK leq_exp2l ?prime_gt1 // => /subnKC <-.
    by rewrite expnD mulnA dvdn_mulr.
  pose d (xi : 'CF(L)) : algC := (truncC (xi 1%g / xi1 1%g))%:R.
  have{Nd} def_d xi: xi \in X -> xi 1%g = d xi * xi1 1%g.
    rewrite /d => Xxi; move: Xxi (Nd _ Xxi) => /irrX/irrP[i ->].
    have /irrX/irrP[i1 ->] := Xxi1.
    rewrite !irr1_degree dvdC_nat => /dvdnP[q ->].
    by rewrite natrM -irr1_degree mulfK ?irr1_neq0 // natCK.
  have d_xi1: d xi1 = 1.
    by apply: (mulIf (seqInd1_neq0 nsHL Xxi1)); rewrite mul1r -def_d.
  have oXY: orthogonal X Y.
    apply/orthogonalP=> xi eta Xxi Yeta; apply: orthoPr xi Xxi.
    exact: (subset_ortho_subcoherent scohS sXS (sYS _ Yeta) (X'Y _ Yeta)).
  have [_ [Itau Ztau] /orthogonal_free freeS _ _] := scohS.
  have o_tauXY: orthogonal (map tau2 X) (map tau1 Y).
    exact: (coherent_ortho scohS).
  have [a Na Dxi11]: exists2 a, a \in Cnat & xi1 1%g = a * #|W1|%:R.
    have [i1 _ ->] := seqIndP Xxi1.
    exists ('chi_i1 1%g); first exact: Cnat_irr1.
    by rewrite cfInd1 // -divgS // -(sdprod_card defL) ?mulKn // mulrC.
  pose psi1 := xi1 - a *: eta1; have Za: a \in Cint by rewrite CintE Na.
  have Zpsi1: psi1 \in 'Z[S, L^#].
    rewrite zcharD1E !cfunE (uniY _ Yeta1) -Dxi11 subrr eqxx.
    by rewrite rpredB ?scale_zchar ?mem_zchar ?(sXS _ Xxi1) // sYS.    
  have [Y1 dY1 [X1 [dX1 _ oX1tauY]]] := orthogonal_split (map tau1 Y)(tau psi1).
  have oY: orthonormal Y by apply: sub_orthonormal (irr_orthonormal L).
  have oYtau: orthonormal (map tau1 Y) by apply: map_orthonormal.
  have{dX1 Y1 dY1} [b Zb Dpsi1]: {b | b \in Cint &
    tau psi1 = X1 - a *: tau1 eta1 + b *: (\sum_(eta <- Y) tau1 eta)}.
  - exists ('[tau psi1, tau1 eta1] + a).
      rewrite rpredD // Cint_cfdot_vchar ?Ztau1 ?seqInd_zcharW //.
      exact: zcharW (Ztau _ Zpsi1).
    rewrite {1}dX1  addrC -addrA; congr (_ + _).
    have [_ -> ->] := orthonormal_span oYtau dY1.
    rewrite -[Y1](addrK X1) -dX1 big_map !(big_rem eta1 Yeta1) /=.
    rewrite cfdotBl (orthoPl oX1tauY) ?map_f // subr0.
    rewrite scalerDr addrA; congr (_ + _).
      by rewrite addrC -scaleNr -scalerDl addrK.
    rewrite raddf_sum; apply: eq_big_seq => eta.
    rewrite mem_rem_uniq ?seqInd_uniq // => /andP[eta1'eta /= Yeta].
    congr (_ *: _); rewrite cfdotBl (orthoPl oX1tauY) ?map_f // subr0 addrC.
    apply: canRL (subrK _) _; rewrite -2!raddfB /=.
    have Zeta: (eta - eta1) \in 'Z[Y, L^#].
      by rewrite zcharD1E rpredB ?seqInd_zcharW //= !cfunE !uniY ?subrr.
    rewrite Dtau1 // Itau // ?(zchar_subset sYS) //.
    rewrite cfdotBl cfdotZl !cfdotBr 2?(orthogonalP oXY) // subr0 add0r.
    have [_ oYY] := orthonormalP oY; rewrite !oYY // eqxx.
    by rewrite eq_sym (negPf eta1'eta) add0r mulrN mulr1 opprK.
  pose psi := 'Res[L] (tau1 eta1).
  have [X2 dX2 [xi' [dxi' _ oxi'X]]] := orthogonal_split X psi.
  have oX: orthonormal X by apply: sub_orthonormal (irr_orthonormal L).
  have Zpsi: psi \in 'Z[irr L] by rewrite cfRes_vchar ?Ztau1 ?seqInd_zcharW.
  pose sumXd := \sum_(xi <- X) d xi *: xi.
  have Zxi1Xd xi: xi \in X -> xi - d xi *: xi1 \in 'Z[X, L^#].
    move=> Xxi; rewrite zcharD1E !cfunE -def_d // subrr eqxx.
    by rewrite rpredB ?scale_zchar ?seqInd_zcharW ?rpred_nat.
  have{dxi' X2 dX2} [c Zc Dpsi]: {c | c \in Cint & psi = c *: sumXd + xi'}.
    exists '[psi, xi1]; first by rewrite Cint_cfdot_vchar ?(seqInd_vcharW Xxi1).
    rewrite {1}dxi'; congr (_ + _); have [_ -> ->] := orthonormal_span oX dX2.
    rewrite -[X2](addrK xi') -dxi' raddf_sum; apply: eq_big_seq => /= xi Xxi.
    rewrite cfdotBl (orthoPl oxi'X) // subr0 scalerA; congr (_ *: _).
    apply/eqP; rewrite -subr_eq0 mulrC -[d xi]conj_Cnat ?Cnat_nat //.
    rewrite -cfdotZr -cfdotBr cfdot_Res_l -Dtau2 ?Zxi1Xd //.
    rewrite cfdotC raddfB raddfZ_Cnat ?Cnat_nat // cfdotBl cfdotZl.
    by rewrite !(orthogonalP o_tauXY) ?map_f // mulr0 subr0 conjC0.
  have Exi' z: z \in Z -> xi' z = xi' 1%g.
    move=> Zz; rewrite [xi']cfun_sum_cfdot !sum_cfunE; apply: eq_bigr => ell _.
    have [Xell |] := boolP ('chi_ell \in X).
      by rewrite !cfunE (orthoPl oxi'X) ?mul0r.
    by rewrite !cfunE defX inE /= mem_irr negbK => /subsetP/(_ z Zz)/cfker1->.
  have Eba: '[psi, psi1] = b - a.
    rewrite cfdot_Res_l -/tau Dpsi1 -addrA !cfdotDr cfdotNr cfdotZr.
    rewrite cfdotC (orthoPl oX1tauY) ?map_f // conjC0 add0r addrC.
    rewrite cfdotC raddf_sum cfproj_sum_orthonormal // !aut_Cint //.
    by have [_ ->] := orthonormalP oYtau; rewrite ?map_f // eqxx mulr1.
  have nz_xi11: xi1 1%g != 0 by have /irrX/irrP[i ->] := Xxi1; apply: irr1_neq0.
  have {Eba} Ebc: (a %| b - c)%C.
    rewrite -[b](subrK a) -Eba cfdotBr {1}Dpsi cfdotDl cfdotZl.
    rewrite cfproj_sum_orthonormal // (orthoPl oxi'X) // addr0 d_xi1 mulr1.
    rewrite addrC -addrA addKr addrC rpredB ?dvdC_refl //= cfdotZr aut_Cint //.
    by rewrite dvdC_mulr // Cint_cfdot_vchar ?(seqInd_vcharW Yeta1).
  have DsumXd: sumXd = (xi1 1%g)^-1 *: (cfReg L - (cfReg (L / Z)%g %% Z)%CF).
    apply: canRL (scalerK nz_xi11) _; rewrite !cfReg_sum 2!linear_sum /=.
    pose F (xi : 'CF(L)) := xi 1%g *: xi; transitivity (\sum_(xi <- X) F xi).
      by apply: eq_big_seq => xi Xxi; rewrite scalerA mulrC -def_d.
    rewrite (bigID (mem (Iirr_ker L Z))) /=; apply: canRL (addrK _) _.
    rewrite addrC; congr (_ + _).
      rewrite (eq_bigl _ _ (in_set _)) (reindex _ (mod_Iirr_bij nsZL)) /=.
      apply: eq_big => [i | i _]; first by rewrite mod_IirrE ?cfker_mod.
      by rewrite linearZ mod_IirrE // cfMod1.
    transitivity (\sum_(xi <- [seq 'chi_i | i in [predC Iirr_ker L Z]]) F xi).
      apply: eq_big_perm; apply: uniq_perm_eq => // [|xi].
        by rewrite (map_inj_uniq irr_inj) ?enum_uniq.
      rewrite defX inE /=; apply/andP/imageP=> [[/irrP[i ->] kerZ'i] | [i]].
        by exists i; rewrite ?inE.
      by rewrite !inE => ? ->; rewrite mem_irr.
    by rewrite big_map big_filter; apply: eq_bigl => i; rewrite !inE.
  have eta1tauZ z: z \in Z^# -> tau1 eta1 z - tau1 eta1 1%g = - c * #|H|%:R / a.
    case/setD1P=> ntz Zz; transitivity (psi z - psi 1%g).
      by rewrite !cfResE ?(subsetP (normal_sub nsZL)).
    rewrite Dpsi DsumXd !cfunE Exi' ?cfuniE ?normal1 // set11 inE (negPf ntz).
    rewrite mulr0 mulr1 sub0r Dxi11 cfker1 ?cfker_reg_quo //.
    set cc := c * _ + _; rewrite 2!mulrDr -[rhs in _ - rhs]addrA -/cc.
    rewrite addrC opprD {cc}subrK -(sdprod_card defL) mulnC natrM.
    by rewrite invfM !mulrA divfK ?neq0CG // mulrAC -2!mulNr.
  have{eta1tauZ} dvHpsi: (#|H| %| - c * #|H|%:R / a)%C.
    have /dirrP[e [i Deta1]]: tau1 eta1 \in dirr G.
      rewrite dirrE Ztau1 ?Itau1 ?seqInd_zcharW //=.
      by have [_ ->] := orthonormalP oY; rewrite ?eqxx.
    have [z ntz Zz] := trivgPn _ ntZ; have Z1z: z \in Z^# by apply/setD1P.
    have /(Zconst_modH i)[|_] := Z1z.
      move=> z1 z2 Zz1 Zz2; rewrite -(canLR (signrZK e) Deta1) !cfunE.
      by apply/eqP; do 2!rewrite eq_sym (canRL (subrK _) (eta1tauZ _ _)) //.
    by rewrite -(canLR (signrZK e) Deta1) !cfunE -mulrBr eta1tauZ // rpredMsign.
  have nz_a: a != 0 by rewrite Dxi11 mulf_eq0 negb_or neq0CG andbT in nz_xi11.
  have{dvHpsi} dv_ac: (a %| c)%C.
    move: dvHpsi; rewrite !mulNr mulrAC rpredN => /dvdCP[q Zq].
    by move/(mulIf (neq0CG H))/(canRL (divfK nz_a))->; apply: dvdC_mull.
  have{Ebc dv_ac} /dvdCP[q Zq Db]: (a %| b)%C by rewrite -[b](subrK c) rpredD.
  pose m : algC := (size Y)%:R.
  have Da1: 1 + a ^+ 2 = '[X1] + a ^+ 2 * ((q - 1) ^+ 2 + (m - 1) * q ^+ 2).
    transitivity '[psi1].
      rewrite cfnormBd; last by rewrite cfdotZr (orthogonalP oXY) ?mulr0. 
      rewrite cfnormZ Cint_normK //.
      have [[_ -> //] [_ -> //]]:= (orthonormalP oX, orthonormalP oY).
      by rewrite !eqxx mulr1.
    rewrite -Itau // Dpsi1 -addrA cfnormDd; last first.
      rewrite addrC cfdotBr !cfdotZr cfdot_sumr (orthoPl oX1tauY) ?map_f //.
      rewrite big_seq big1 ?mulr0 ?subrr // => eta Yeta.
      by rewrite (orthoPl oX1tauY) ?map_f //.
    congr (_ + _); rewrite cfnormD cfnormN !cfnormZ.
    have [_ ->] := orthonormalP oYtau; rewrite ?map_f // eqxx mulr1.
    rewrite cfnorm_map_orthonormal // -/m !Cint_normK // cfdotNl cfdotZl.
    rewrite linear_sum cfdotC cfproj_sum_orthonormal // rmorphN rmorphM.
    rewrite conjCK !aut_Cint // -mulr2n mulNrn -[_ - _]addrAC.
    rewrite mulrDr -{1}[m](addNKr 1) mulrDr mulr1 addrA -sqrrB.
    congr (_ + _); last by rewrite mulrCA -exprMn (mulrC a) addrC -Db mulrC.
    by rewrite -exprMn -sqrrN opprB mulrBr mulr1 (mulrC a) -Db.
  have{Da1} maxq: ~~ (2%:R <= (q - 1) ^+ 2 + (m - 1) * q ^+ 2).
    have a2_gt1: a ^+ 2 > 1.
      have /seqIndP[i1 /setDP[_ not_kerH'i1] Dxi1] := Xxi1.
      apply: contraR not_kerH'i1; rewrite inE expr_gt1 ?Cnat_ge0 //.
      have [n Da] := CnatP a Na; rewrite Da ltr1n -leqNgt leq_eqVlt.
      rewrite ltnNge lt0n -!eqC_nat -{n}Da nz_a orbF => /eqP a_eq1.
      rewrite (subset_trans sZH') // -lin_irr_der1 qualifE irr_char.
      rewrite -(inj_eq (mulfI (neq0CiG L H))) -cfInd1 // -Dxi1 Dxi11 a_eq1.
      by rewrite mul1r mulr1 -divgS //= -(sdprod_card defL) mulKn.
    rewrite -(ler_pmul2l (ltr_trans ltr01 a2_gt1)) ltr_geF // mulr_natr.
    apply: ler_lt_trans (_ : 1 + a ^+ 2 < _); last by rewrite ltr_add2r.
    by rewrite Da1 -subr_ge0 addrK cfnorm_ge0.
  clear psi Dpsi Zpsi Zb c sumXd DsumXd Zc xi' Exi' oxi'X.
  wlog{Dpsi1 Itau1 Ztau1 Dtau1 oYtau b q maxq Db Zq} Dpsi1:
    tau1 cohY o_tauXY oX1tauY / tau psi1 = X1 - a *: tau1 eta1.
  - move=> IH; have [q0 | nz_q] := eqVneq q 0.
      by apply: (IH tau1) => //; rewrite Dpsi1 Db q0 mul0r scale0r addr0.
    have m1_ge1: 1 <= m - 1.
      rewrite -(@ler_add2r _ 1) subrK (ler_nat _ 2).
      exact: seqInd_nontrivial (irrY _ Yeta1) (Yeta1).
    have q1: q = 1.
      apply: contraNeq maxq; rewrite -subr_eq0 => nz_q1.
      rewrite ler_add // ?sqr_Cint_ge1 ?rpredB //.
      rewrite (ler_trans m1_ge1) // -{1}[m - 1]mulr1.
      by rewrite ler_pmul2l ?sqr_Cint_ge1 // (ltr_le_trans ltr01).
    have szY2: (size Y <= 2)%N.
      move: maxq; rewrite q1 subrr exprS mul0r add0r mulrA !mulr1.
      by rewrite -(ler_add2r 1) subrK -mulrSr ler_nat -leqNgt.
    have defY: perm_eq Y (eta1 :: eta1^*)%CF.
      have uYeta: uniq (eta1 :: eta1^*)%CF.
        by rewrite /= andbT inE eq_sym; have [[_ /hasPn/=->]] := scohY.
      rewrite perm_eq_sym uniq_perm_eq //.
      have [|//]:= leq_size_perm uYeta _ szY2.
      by apply/allP; rewrite /= Yeta1 ccY.
    have memYtau1c: {subset map (tau1 \o cfAut conjC) Y <= map tau1 Y}.
      by move=> _ /mapP[eta Yeta ->]; rewrite /= map_f ?ccY.     
    apply: (IH _ (dual_coherence scohY cohY szY2)).
    - rewrite (map_comp -%R) orthogonal_oppr.
      by apply/orthogonalP=> phi psi ? /memYtau1c; apply: (orthogonalP o_tauXY).
    - rewrite (map_comp -%R) orthogonal_oppr.
      by apply/orthoPl=> psi /memYtau1c; apply: (orthoPl oX1tauY).
    rewrite Dpsi1 (eq_big_perm _ defY) Db q1 /= mul1r big_cons big_seq1.
    by rewrite scalerDr addrA subrK -scalerN opprK.
  have [[[Itau1 Ztau1] Dtau1] [_ oXX]] := (cohY, orthonormalP oX).
  have n1X1: '[X1] = 1.
    apply: (addIr '[a *: tau1 eta1]); rewrite -cfnormBd; last first.
      by rewrite cfdotZr (orthoPl oX1tauY) ?mulr0 ?map_f.
    rewrite -Dpsi1 Itau // cfnormBd; last first.
      by rewrite cfdotZr (orthogonalP oXY) ?mulr0.
    by rewrite !cfnormZ Itau1 ?seqInd_zcharW // oXX ?eqxx.
  without loss{Itau2 Ztau2 Dtau2} defX1: tau2 cohX o_tauXY / X1 = tau2 xi1.
    move=> IH; have ZX: {subset X <= 'Z[X]} by apply: seqInd_zcharW.
    have dirrXtau xi: xi \in X -> tau2 xi \in dirr G.
      by move=> Xxi; rewrite dirrE Ztau2 1?Itau2 ?ZX //= oXX ?eqxx.
    have dirrX1: X1 \in dirr G.
      rewrite dirrE n1X1 eqxx -[X1](subrK (a *: tau1 eta1)) -Dpsi1.
      rewrite rpredD ?scale_zchar ?(zcharW (Ztau _ _)) //.
      by rewrite Ztau1 ?seqInd_zcharW.
    have oX1_Xd xi:
      xi \in X -> xi != xi1 -> '[d xi *: tau2 xi1 - tau2 xi, X1] = d xi.
    - move=> Xxi xi1'xi; have ZXxi := Zxi1Xd xi Xxi.
      rewrite -[X1](subrK (a *: tau1 eta1)) -Dpsi1 cfdotDr cfdotZr addrC.
      rewrite cfdotBl cfdotZl 2?(orthogonalP o_tauXY) ?map_f //.
      rewrite !(mulr0, subr0, conjC0) add0r -{1}raddfZ_Cnat ?Cnat_nat //.
      rewrite -opprB cfdotNl -raddfB Dtau2 //.
      rewrite Itau //; last exact: zchar_subset ZXxi.
      rewrite cfdotBr cfdotZr addrC !cfdotBl !cfdotZl.
      rewrite 2?(orthogonalP oXY) // !(mulr0, oppr0, add0r, conjC0).
      by rewrite !oXX // eqxx (negPf xi1'xi) add0r opprK mulr1.
    have Xxi2: xi1^*%CF \in X by apply: ccX.
    have xi1'2: xi1^*%CF != xi1 by have [[_ /hasPn->]] := scohX.
    have xi2tau_irr: - tau2 xi1^*%CF \in dirr G by rewrite dirr_opp dirrXtau.
    have d_xi2: d xi1^*%CF = 1.
      by rewrite /d cfunE conj_Cnat // (Cnat_seqInd1 Xxi1).
    have [||def_X1]:= cfdot_add_dirr_eq1 (dirrXtau _ Xxi1) xi2tau_irr dirrX1.
    - by rewrite -[tau2 xi1]scale1r -d_xi2 oX1_Xd.
    - exact: IH.
    have sX_xi12: {subset X <= xi1 :: xi1^*%CF}.
      apply/allP/allPn=> [[xi3 Xxi3 /norP[xi1'3 /norP[xi2'3 _]]]].
      suffices d3_0: d xi3 = 0.
        by have:= seqInd1_neq0 nsHL Xxi3; rewrite def_d // d3_0 mul0r eqxx.
      rewrite -oX1_Xd // def_X1 cfdotNr cfdotBl cfdotZl !Itau2 ?ZX //.
      by rewrite !oXX // (negPf xi2'3) eq_sym (negPf xi1'2) mulr0 add0r opprK.
    have{sX_xi12 defX} defX: perm_eq X (xi1 :: xi1^*%CF).
      have uXxi: uniq (xi1 :: xi1^*)%CF by rewrite /= andbT inE eq_sym.
      rewrite perm_eq_sym uniq_perm_eq // => xi.
      by apply/idP/idP; [rewrite !inE => /pred2P[]-> | apply: sX_xi12].
    have szX2: (size X <= 2)%N by rewrite (perm_eq_size defX).
    apply: (IH _ (dual_coherence scohX cohX szX2)) def_X1.
    rewrite (map_comp -%R) orthogonal_oppl.
    apply/orthogonalP=> _ eta /mapP[xi Xxi ->].
    by apply: (orthogonalP o_tauXY); rewrite map_f ?ccX.
  move: Dpsi1; rewrite -raddfZ_Cnat // defX1.
  apply: (bridge_coherent scohS ccsXS cohX ccsYS cohY X'Y).
  by rewrite (zchar_on Zpsi1) rpredZ_Cnat ?mem_zchar.
have{caseA_coh12} cohXY: coherent (X ++ Y) L^# tau.
  have [/caseA_coh12// | caseB] := boolP caseA.
  have defZ: Z = W2 by rewrite /Z (negPf caseB).
  have{caseB} [case_c2 _ _] := caseB_P caseB.
  move/(_ case_c2) in oRW; pose PtypeL := c2W2 case_c2.
  have{prW2} pr_w2 := prW2 case_c2; set w2 := #|W2| in pr_w2.
  have /cyclicP[z0 cycZ]: cyclic Z by rewrite defZ prime_cyclic.
  have idYZ: {in Y & Z^#, forall (eta : 'CF(L)) x, tau1 eta x = tau1 eta z0}.
    move=> eta x Yeta; rewrite !inE andbC cycZ => /andP[/cyclePmin[k]].
    rewrite orderE -cycZ defZ -/w2 => lt_k_w2 -> nt_z0k.
    have k_gt0: (0 < k)%N by rewrite lt0n (contraNneq _ nt_z0k) // => ->.
    have cokw2: coprime k w2 by rewrite coprime_sym prime_coprime // gtnNdvd.
    have sW2G: W2 \subset G by rewrite -defW2 subIset // (subset_trans sHL).
    have [u Du _]:= make_pi_cfAut G cokw2.
    rewrite -Du ?Ztau1 ?seqInd_zcharW //; last by rewrite orderE -cycZ defZ.
    have nAL: L \subset 'N(A) by rewrite normD1 normal_norm.
    pose ddA := restr_Dade_hyp PtypeL (subsetUl _ _) nAL.
    have cohY_Dade: coherent_with Y L^# (Dade ddA) tau1.
      split=> // phi Yphi; rewrite Dtau1 ?Dade_Ind //.
      by rewrite (@zchar_on _ _ Y) -?zcharD1_seqInd.
    rewrite (cfAut_Dade_coherent cohY_Dade) ?irrY //; last first.
      split; last exact: cfAut_seqInd.
      exact: seqInd_nontrivial_irr (irrY _ Yeta) (Yeta).
    rewrite -[cfAut u _](subrK eta) raddfD cfunE.
    apply: canLR (subrK _) _; rewrite subrr.
    have [_ ->] := cohY_Dade; last first.
      by rewrite -opprB rpredN zcharD1_seqInd // seqInd_sub_aut_zchar.
    rewrite Dade_id; last first.
      by rewrite !inE -cycle_eq1 -cycle_subG -cycZ ntZ.
    rewrite !cfunE cfker1 ?aut_Cnat ?subrr ?(Cnat_seqInd1 Yeta) //.
    rewrite -cycle_subG -cycZ (subset_trans sZH') //.
    have [j /setDP[kerH'j _] ->] := seqIndP Yeta.
    by rewrite inE in kerH'j; rewrite sub_cfker_Ind_irr.
  have [_ [Itau _] oSS _ _] := scohS.
  have oY: orthonormal Y by apply: sub_orthonormal (irr_orthonormal L).
  have oYtau: orthonormal (map tau1 Y) by apply: map_orthonormal.
  have oXY: orthogonal X Y.
    apply/orthogonalP=> xi eta Xxi Yeta; apply: orthoPr xi Xxi.
    exact: (subset_ortho_subcoherent scohS sXS (sYS _ Yeta) (X'Y _ Yeta)).
  have [Y1 Dpsi1 defY1]: exists2 Y1,
    forall i : Iirr Z, i != 0 ->
      exists2 X1 : 'CF(G), orthogonal X1 (map tau1 Y)
            & tau ('Ind 'chi_i - #|H : Z|%:R *: eta1) = X1 - #|H : Z|%:R *: Y1
      & Y1 = tau1 eta1 \/ size Y = 2 /\ Y1 = dual_iso tau1 eta1.
  - have [i0 nz_i0]: exists i0 : Iirr Z, i0 != 0.
      by apply: (ex_intro _ (Sub 1%N _)) => //; rewrite NirrE classes_gt1.
    pose psi1 := tau1 eta1; pose b := psi1 z0.
    pose a :=  (psi1 1%g - b) / #|Z|%:R.
    have sZL := normal_sub nsZL; have sZG := subset_trans sZL sLG.
    have Dpsi1: 'Res psi1 = a *: cfReg Z + b%:A.
      apply/cfun_inP=> z Zz.
      rewrite cfResE // !cfunE cfun1E Zz mulr1 cfuniE ?normal1 // inE.
      have [-> | ntz] := altP eqP; first by rewrite mulr1 divfK ?neq0CG ?subrK.
      by rewrite !mulr0 add0r idYZ // !inE ntz.
    have /dvdCP[x0 Zx0 Dx0]: (#|H : Z| %| a)%C.
      have /dvdCP[x Zx Dx]: (#|H| %| b - psi1 1%g)%C.
        have psi1Z z: z \in Z^# -> psi1 z = b.
          case/setD1P=> ntz Zz; rewrite -(cfResE _ _ Zz) // Dpsi1 !cfunE cfun1E.
          by rewrite cfuniE ?normal1 // Zz inE (negPf ntz) !mulr0 mulr1 add0r.
        have /dirrP[e [i /(canLR (signrZK e)) Epsi1]]: psi1 \in dirr G.
          have [_ oYt] := orthonormalP oYtau.
          by rewrite dirrE oYt ?map_f // !eqxx Ztau1 ?seqInd_zcharW.
        have Zz: z0 \in Z^# by rewrite !inE -cycle_eq1 -cycle_subG -cycZ ntZ /=.
        have/(Zconst_modH i)[z1 Zz1 z2 Zz2 |_] := Zz.
          by rewrite -Epsi1 !cfunE !psi1Z.
        by rewrite -Epsi1 !cfunE -mulrBr rpredMsign psi1Z.
      apply/dvdCP; exists (- x); first by rewrite rpredN.
      rewrite /a -opprB Dx -(Lagrange sZH) mulnC [p in x * p]natrM -!mulNr.
      by rewrite !mulrA !mulfK ?neq0CG.
    pose x1 := '[eta1, 'Res psi1]; pose x := x0 + 1 - x1.
    have Zx: x \in Cint.
      rewrite rpredB ?rpredD // Cint_cfdot_vchar // ?(seqInd_vcharW Yeta1) //.
      by rewrite cfRes_vchar // Ztau1 ?seqInd_zcharW.
    pose Y1 := - \sum_(eta <- Y) (x - (eta == eta1)%:R) *: tau1 eta.
    pose alpha i := 'Ind[L, Z] 'chi_i - #|H : Z|%:R *: eta1.
    have IZfacts i: i != 0 ->
      [/\ 'chi_i 1%g = 1, 'Ind[L, Z] 'chi_i \in 'Z[X] & alpha i \in 'Z[S, L^#]].
    - move=> nzi; have /andP[_ /eqP lin_i]: 'chi_i \is a linear_char.
        by rewrite lin_irr_der1 (derG1P _) ?sub1G // cycZ cycle_abelian.
      have Xchi: 'Ind 'chi_i \in 'Z[X].
        rewrite -(cfIndInd _ sHL) // ['Ind[H] _]cfun_sum_constt linear_sum.
        apply: rpred_sum => k k_i; rewrite linearZ; apply: scale_zchar.
          by rewrite Cint_cfdot_vchar_irr // cfInd_vchar ?irr_vchar.
        rewrite seqInd_zcharW //; apply/seqIndP; exists k => //.
        rewrite !inE sub1G andbT; apply: contra k_i => kerZk.
        rewrite -Frobenius_reciprocity.
        have ->: 'Res[Z] 'chi_k = ('chi_k 1%g)%:A.
          apply: cfun_inP => z Zz; rewrite cfunE cfun1E Zz mulr1 cfResE //.
          by rewrite cfker1 ?(subsetP kerZk).
        by rewrite cfdotZr -irr0 cfdot_irr (negPf nzi) mulr0.
      split=> //; rewrite zcharD1E !cfunE cfInd1 // uniY // lin_i mulr1.
      rewrite -divgS // -(sdprod_card defL) -(Lagrange sZH) -mulnA mulKn //.
      rewrite -natrM subrr rpredB //=; first by rewrite (zchar_subset sXS).
      by rewrite scale_zchar ?rpred_nat // seqInd_zcharW ?sYS. 
    have Dalpha (i : Iirr Z) (nzi : i != 0) :
      exists2 X1 : 'CF(G), orthogonal X1 (map tau1 Y)
            & tau (alpha i) = X1 - #|H : Z|%:R *: Y1.
    - have [lin_i Xchi Zalpha] := IZfacts i nzi.
      have Da: '[tau (alpha i), psi1] = a - #|H : Z|%:R * x1.
        rewrite !(=^~ Frobenius_reciprocity, cfdotBl) cfResRes // cfdotZl.
        congr (_ - _); rewrite cfdotC Dpsi1 cfdotDl cfdotZl cfReg_sum.
        rewrite cfdot_suml (bigD1 i) //= big1 => [|j i'j]; last first.
          by rewrite cfdotZl cfdot_irr (negPf i'j) mulr0.
        rewrite !cfdotZl cfnorm_irr lin_i addr0 !mulr1.
        rewrite -irr0 cfdot_irr eq_sym (negPf nzi) mulr0 addr0.
        by rewrite aut_Cint // Dx0 rpredM ?rpred_nat.
      have [Y2 dY2 [X1 [dX1 _ oX1Yt]]] :=
        orthogonal_split (map tau1 Y) (tau (alpha i)).
      exists X1 => //; rewrite dX1 addrC scalerN opprK scaler_sumr.
      congr (_ + _); have [_ -> ->] := orthonormal_span oYtau dY2.
      rewrite big_map; apply: eq_big_seq => eta Yeta.
      rewrite scalerA -[Y2](addrK X1) -dX1 cfdotBl (orthoPl oX1Yt) ?map_f //.
      congr (_ *: _); rewrite subr0 !mulrBr mulrDr mulrC -Dx0.
      rewrite (addrAC a) -Da -addrA -mulrBr addrC; apply: canRL (subrK _) _.
      have Zeta: eta - eta1 \in 'Z[Y, L^#].
        by rewrite zcharD1E rpredB ?seqInd_zcharW //= !cfunE !uniY ?subrr.
      rewrite -cfdotBr -raddfB Dtau1 // Itau //; last first.
        by rewrite (zchar_subset sYS) ?seqInd_free.
      rewrite cfdotBl (span_orthogonal oXY) ?(zchar_span Xchi)//; last first.
        by rewrite memvB ?memv_span.
      have [_ oYY] := orthonormalP oY; rewrite cfdotZl cfdotBr !oYY //.
      by rewrite eqxx sub0r -mulrN opprB eq_sym.
    exists Y1 => //; have{Dalpha} [X1 oX1Y Dalpha] := Dalpha i0 nz_i0.
    have [lin_i Xchi Zalpha] := IZfacts i0 nz_i0.
    have norm_alpha: '[tau (alpha i0)] = (#|L : Z| + #|H : Z| ^ 2)%:R.
      rewrite natrD Itau // cfnormBd; last first.
        rewrite (span_orthogonal oXY) ?(zchar_span Xchi) //.
        by rewrite memvZ ?memv_span.
      rewrite cfnorm_Ind_irr //; congr (#|_ : _|%:R + _).
        apply/setIidPl; apply: subset_trans (cent_sub_inertia _).
        rewrite -(sdprodW defL) mulG_subG (centsS sZZ) centsC ?subsetIr //=.
        by rewrite defZ -defW2 subsetIr.
      have [_ oYY] := orthonormalP oY; rewrite cfnormZ oYY // eqxx mulr1.
      by rewrite normCK rmorph_nat -natrM.
    have{norm_alpha} ub_norm_alpha: '[tau (alpha i0)] < (#|H : Z| ^ 2).*2%:R.
      rewrite norm_alpha -addnn ltr_nat ltn_add2r.
      rewrite -divgS // -(sdprod_card defL) -(Lagrange sZH) -mulnA mulKn //.
      rewrite ltn_pmul2l //.
      have frobL2: [Frobenius L / Z = (H / Z) ><| (W1 / Z)]%g.
        apply: (Frobenius_coprime_quotient defL nsZL) => //.
        split=> [|y W1y]; first exact: sub_proper_trans ltH'H.
        by rewrite defZ; have [/= ? [_ [_ _ _ ->]]] := PtypeL.
      have nZW1 := subset_trans sW1L (normal_norm nsZL).
      rewrite (card_isog (quotient_isog nZW1 _)); last first.
        by rewrite coprime_TIg ?(coprimeSg sZH).
      rewrite -(prednK (indexg_gt0 H Z)) ltnS -card_quotient //.
      rewrite dvdn_leq ?(Frobenius_dvd_ker1 frobL2) // -subn1 subn_gt0.
      by rewrite cardG_gt1; case/Frobenius_context: frobL2.
    pose m : algC := (size Y)%:R.
    have{ub_norm_alpha} ub_xm: ~~ (2%:R <= (x - 1) ^+ 2 + (m - 1) * x ^+ 2).
      have: ~~ (2%:R <= '[Y1]).
        rewrite -2!(ler_pmul2l (gt0CiG H Z)) -!natrM mulnA muln2.
        rewrite ltr_geF //; apply: ler_lt_trans ub_norm_alpha.
        rewrite Dalpha cfnormBd.
          by rewrite cfnormZ normCK rmorph_nat mulrA -subr_ge0 addrK cfnorm_ge0.
        rewrite scalerN -scaleNr cfdotZr cfdot_sumr big_seq.
        rewrite big1 ?mulr0 // => eta Yeta.
        by rewrite cfdotZr (orthoPl oX1Y) ?map_f ?mulr0.
      rewrite cfnormN cfnorm_sum_orthonormal // (big_rem eta1) //= eqxx.
      rewrite big_seq (eq_bigr (fun _ => (x ^+ 2))) => [|eta]; last first.
        rewrite mem_rem_uniq // => /andP[/negPf-> _].
        by rewrite subr0 Cint_normK.
      rewrite Cint_normK 1?rpredB //= -big_seq; congr (~~ (_ <= _ + _)).
      rewrite big_const_seq count_predT // -Monoid.iteropE.
      rewrite /m (perm_eq_size (perm_to_rem Yeta1)) /=.
      by rewrite mulrSr addrK mulr_natl.
    have [x_eq0 | nz_x] := eqVneq x 0.
      left; rewrite /Y1 x_eq0 (big_rem eta1) //= eqxx sub0r scaleN1r.
      rewrite big_seq big1 => [|eta]; last first.
        by rewrite mem_rem_uniq // => /andP[/negPf-> _]; rewrite subrr scale0r.
      by rewrite addr0 opprK.
    have m1_ge1: 1 <= m - 1.
      rewrite -(@ler_add2r _ 1) subrK (ler_nat _ 2).
      exact: seqInd_nontrivial (irrY _ Yeta1) (Yeta1).
    right; have x_eq1: x = 1.
      apply: contraNeq ub_xm; rewrite -subr_eq0 => nz_x1; apply: ler_add.
        by rewrite sqr_Cint_ge1 // rpredB.
      rewrite (ler_trans m1_ge1) // -{1}[m - 1]mulr1 ler_pmul2l.
        exact: sqr_Cint_ge1.
      exact: ltr_le_trans ltr01 m1_ge1.
    have szY2: size Y = 2.
      apply: contraNeq ub_xm => Yneq2; rewrite x_eq1 /m subrr !exprS mul0r.
      rewrite add0r !mul1r mulr1 -(ler_add2r 1) subrK -mulrSr ler_nat.
      by rewrite ltn_neqAle eq_sym Yneq2 -leC_nat -/m -[m](subrK 1) ler_add2r.
    have eta1'2: eta1^*%CF != eta1 by apply: seqInd_conjC_neq Yeta1.
    have defY: perm_eq Y (eta1 :: eta1^*%CF).
      have uY2: uniq (eta1 :: eta1^*%CF) by rewrite /= inE eq_sym eta1'2.
      rewrite perm_eq_sym uniq_perm_eq //.
      have sY2Y: {subset (eta1 :: eta1^*%CF) <= Y}.
        by apply/allP; rewrite /= cfAut_seqInd ?Yeta1.
      by have [|//]:= leq_size_perm uY2 sY2Y; rewrite szY2.
    split=> //; congr (- _); rewrite (eq_big_perm _ defY) /= x_eq1.
    rewrite big_cons big_seq1 eqxx (negPf eta1'2) subrr scale0r add0r.
    by rewrite subr0 scale1r.
  have [a Za Dxa]: exists2 a, forall xi, a xi \in Cint
                  & forall xi, xi \in X -> xi 1%g = a xi * #|W1|%:R
                    /\ (exists2 X1 : 'CF(G), orthogonal X1 (map tau1 Y)
                              & tau (xi - a xi *: eta1) = X1 - a xi *: Y1).
  - pose aX (xi : 'CF(L)) : algC := (truncC (xi 1%g / #|W1|%:R))%:R.
    exists aX => [xi | xi Xxi]; first exact: rpred_nat.
    have [k kerZ'k def_xi] := seqIndP Xxi; rewrite !inE sub1G andbT in kerZ'k.
    set a := aX xi; have Dxi1: xi 1%g = a * #|W1|%:R.
      rewrite /a /aX def_xi cfInd1 // -divgS // -(sdprod_card defL) mulKn //.
      by rewrite mulrC mulfK ?neq0CG // irr1_degree natCK.
    split=> //; have Da: a = 'chi_k 1%g.
       apply: (mulIf (neq0CG W1)); rewrite -Dxi1 def_xi cfInd1 //.
       by rewrite mulrC -divgS // -(sdprod_card defL) mulKn.
    have [i0 nzi0 Res_k]: exists2 i: Iirr Z, i != 0 & 'Res 'chi_k = a *: 'chi_i.
      have [chi /andP[Nchi lin_chi] defRkZ] := cfcenter_Res 'chi_k.
      have sZ_Zk: Z \subset 'Z('chi_k)%CF.
        by rewrite (subset_trans sZZ) // -cap_cfcenter_irr bigcap_inf.
      have{Nchi lin_chi} /irrP[i defRk] : 'Res chi \in irr Z.
        by rewrite lin_char_irr // qualifE cfRes_char // cfRes1.
      have{chi defRk defRkZ} defRk: 'Res 'chi_k = a *: 'chi_i.
        by rewrite -defRk -linearZ -/a Da -defRkZ /= cfResRes ?cfcenter_sub.
      exists i => //; apply: contra kerZ'k.
      rewrite -subGcfker => /subsetP sZker.
      apply/subsetP=> t Zt; rewrite cfkerEirr inE.
      by rewrite -!(cfResE _ sZH) // defRk !cfunE cfker1 ?sZker.
    set phi := 'chi_i0 in Res_k; pose a_ i := '['Ind[H] phi, 'chi_i].
    pose rp := irr_constt ('Ind[H] phi).
    have defIphi: 'Ind phi = \sum_(i in rp) a_ i *: 'chi_i.
      exact: cfun_sum_constt.
    have a_k: a_ k = a.
      by rewrite /a_ -cfdot_Res_r Res_k cfdotZr cfnorm_irr mulr1 rmorph_nat.
    have rp_k: k \in rp by rewrite inE ['[_, _]]a_k Da irr1_neq0.
    have resZr i: i \in rp -> 'Res[Z] 'chi_i = a_ i *: phi.
      move=> r_i; rewrite ['Res _]cfun_sum_cfdot.
      rewrite (bigD1 i0) // big1 => /= [|j i0'j].
        rewrite cfdot_Res_l addr0 -/phi cfdotC conj_Cnat //.
        by rewrite Cnat_cfdot_char_irr ?cfInd_char ?irr_char.
      apply/eqP; rewrite scaler_eq0 cfdot_Res_l.
      rewrite -(inj_eq (mulfI r_i)) mulr0 -/(a_ i) -cfdotZl.
      have: '['Ind[H] phi, 'Ind[H] 'chi_j] = 0.
        apply: not_cfclass_Ind_ortho => //.
        have defIj: 'I_H['chi_j] = H.
          apply/setIidPl; apply: subset_trans (cent_sub_inertia _).
          by rewrite centsC (subset_trans sZZ) ?subsetIr.
        rewrite -(congr1 (cfclass _) defIj) cfclass_inertia inE.
        by rewrite eq_sym (inj_eq irr_inj).
      rewrite defIphi cfdot_suml => /psumr_eq0P-> //; first by rewrite eqxx.
      move=> i1 _; rewrite cfdotZl.
      by rewrite mulr_ge0 ?Cnat_ge0 ?Cnat_cfdot_char ?cfInd_char ?irr_char.
    have lin_phi: phi 1%g = 1.
      apply: (mulfI (irr1_neq0 k)); have /resZr/cfunP/(_ 1%g) := rp_k.
      by rewrite cfRes1 // cfunE mulr1 a_k Da.
    have Da_ i: i \in rp -> 'chi_i 1%g = a_ i.
      move/resZr/cfunP/(_ 1%g); rewrite cfRes1 // cfunE => ->.
      by rewrite lin_phi mulr1.
    pose chi i := 'Ind[L, H] 'chi_i; pose alpha i := chi i - a_ i *: eta1.
    have Aalpha i: i \in rp -> alpha i \in 'CF(L, A).
      move=> r_i; rewrite cfun_onD1 !cfunE cfInd1 // (uniY _ Yeta1).
      rewrite -divgS // -(sdprod_card defL) mulKn // Da_ // mulrC subrr eqxx.
      by rewrite memvB ?cfInd_normal ?memvZ // (seqInd_on _ Yeta1).
    have [sum_alpha sum_a2]:
         'Ind phi - #|H : Z|%:R *: eta1 = \sum_(i in rp) a_ i *: alpha i
      /\ \sum_(i in rp) a_ i ^+ 2 = #|H : Z|%:R.
    + set rhs2 := _%:R; set lhs1 := _ - _; set rhs1 := \sum_(i | _) _.
      set lhs2 := \sum_(i | _) _.
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
      rewrite orbF => /eqP sum_a2; split=> //; apply/eqP; rewrite -subr_eq0.
      by rewrite eq_diff sum_a2 subrr scale0r.
    have Xchi i: i \in rp -> chi i \in X.
      move=> rp_i; apply/seqIndP; exists i => //; rewrite !inE sub1G andbT.
      apply: contra rp_i => kerZi; rewrite -cfdot_Res_r.
      suffices ->: 'Res[Z] 'chi_i = ('chi_i 1%g)%:A.
         by rewrite cfdotZr -irr0 cfdot_irr (negPf nzi0) mulr0.
      apply/cfun_inP=> t Zt; rewrite cfResE // cfunE cfun1E Zt mulr1.
      by rewrite cfker1 ?(subsetP kerZi).
    have oRY i: i \in rp -> orthogonal (R (chi i)) (map tau1 Y).
      move/Xchi=> Xchi_i; rewrite orthogonal_sym.
      by rewrite (coherent_ortho_supp scohS) // ?sXS // (contraL (X'Y _)).
    have n1Y1: '[Y1] = 1.
      have [_ oYYt] := orthonormalP oYtau.
      have [-> | [_ ->]] := defY1;
        by rewrite ?cfnormN oYYt ?eqxx ?map_f // cfAut_seqInd.
    have YtauY1: Y1 \in 'Z[map tau1 Y].
      have [-> | [_ ->]] := defY1;
        by rewrite ?rpredN mem_zchar ?map_f ?cfAut_seqInd.
    have /fin_all_exists[XbZ defXbZ] i: exists XbZ, let: (X1, b, Z1) := XbZ in
      [/\ tau (alpha i) = X1 - b *: Y1 + Z1,
          i \in rp -> X1 \in 'Z[R (chi i)], i \in rp -> b \is Creal,
          '[Z1, Y1] = 0 & i \in rp -> orthogonal Z1 (R (chi i))].
    - have [X1 dX1 [YZ1 [dXYZ _ oYZ1R]]] :=
        orthogonal_split (R (chi i)) (tau (alpha i)).
      have [Y1b dY1b [Z1 [dYZ1 _ oZY1]]] := orthogonal_split Y1 YZ1.
      have{dY1b} [|b Db dY1b] := orthogonal_span _ dY1b.
        by rewrite /pairwise_orthogonal /= inE eq_sym -cfnorm_eq0 n1Y1 oner_eq0.
      exists (X1, - b Y1, Z1); split.
      + by rewrite dXYZ dYZ1 dY1b scaleNr big_seq1 opprK addrA.
      + have [_ _ _ Rok _] := scohS => /Xchi/sXS/Rok[ZR oRR _].
        have [_ -> ->] := orthonormal_span oRR dX1.
        rewrite big_seq rpred_sum // => aa Raa.
        rewrite scale_zchar ?mem_zchar //.
        rewrite -[X1](addrK YZ1) -dXYZ cfdotBl (orthoPl oYZ1R) // subr0.
        rewrite Cint_cfdot_vchar ?(ZR aa) //.
        rewrite !(rpredB, cfInd_vchar) ?irr_vchar //.
        rewrite scale_zchar ?(seqInd_vcharW Yeta1) // Cint_cfdot_vchar_irr //.
        by rewrite cfInd_vchar ?irr_vchar.
      + move=> rp_i; rewrite Db -[Y1b](addrK Z1) -dYZ1 cfdotBl (orthoP oZY1).
        rewrite subr0 n1Y1 divr1 -[YZ1](addKr X1) -dXYZ cfdotDl cfdotNl.
        rewrite (span_orthogonal (oRY i rp_i)) ?(zchar_span YtauY1) //.
        rewrite oppr0 add0r Creal_Cint // rpredN Cint_cfdot_vchar //.
          rewrite !(cfInd_vchar, rpredB) ?irr_vchar //.
          rewrite -Da_ // scale_zchar ?Cint_Cnat ?Cnat_irr1 //.
          exact: (seqInd_vcharW Yeta1).
        apply: zchar_trans_on YtauY1 => _ /mapP[eta Yeta ->].
        by rewrite Ztau1 ?seqInd_zcharW.
      + exact: (orthoP oZY1).
      move/oRY=> oRiY; apply/orthoPl=> aa Raa.
      rewrite -[Z1](addKr Y1b) -dYZ1 cfdotDl cfdotNl cfdotC (orthoPl oYZ1R) //.
      rewrite dY1b addr0 big_seq1 cfdotZr.
      by have [-> | [_ ->]] := defY1;
        rewrite ?cfdotNr (orthogonalP oRiY) ?map_f ?cfAut_seqInd //;
        rewrite ?(oppr0, mulr0, rmorph0).
    pose X1 i := (XbZ i).1.1; pose b i := (XbZ i).1.2; pose Z1 i := (XbZ i).2.
    have R_X1 i: i \in rp -> X1 i \in 'Z[R (chi i)].
      by rewrite /X1; case: (XbZ i) (defXbZ i) => [[? ?] ?] [].
    have Rb i: i \in rp -> b i \is Creal.
      by rewrite /b; case: (XbZ i) (defXbZ i) => [[? ?] ?] [].
    have oZY1 i: '[Z1 i, Y1] = 0.
      by rewrite /Z1; case: (XbZ i) (defXbZ i) => [[? ?] ?] [].
    have oZ1R i: i \in rp -> orthogonal (Z1 i) (R (chi i)).
      by rewrite /Z1; case: (XbZ i) (defXbZ i) => [[? ?] ?] [].
    have{defXbZ} defXbZ i: tau (alpha i) = X1 i - b i *: Y1 + Z1 i.
      by rewrite /X1 /b /Z1; case: (XbZ i) (defXbZ i) => [[? ?] ?] [].
    have ub_alpha i: i \in rp ->
       [/\ '[chi i] <= '[X1 i]
         & '[a_ i *: eta1] <= '[b i *: Y1 - Z1 i] ->
           [/\ '[X1 i] = '[chi i], '[b i *: Y1 - Z1 i] = '[a_ i *: eta1]
             & exists2 E, subseq E (R (chi i)) & X1 i = \sum_(aa <- E) aa]].
    - move=> rp_i; apply: (subcoherent_norm scohS) (erefl _) _.
      + rewrite sXS ?Xchi // scale_zchar ?(seqInd_vcharW Yeta1) //; last first.
          by rewrite Cint_cfdot_vchar_irr // cfInd_vchar ?irr_vchar.
        split=> //; apply/orthoPr=> xi2; rewrite !inE => Dxi2.
        rewrite cfdotZr (orthogonalP oXY) ?mulr0 //.
        by case/pred2P: Dxi2 => ->; rewrite ?cfAut_seqInd ?Xchi.
      + have [_ IZtau _ _ _] := scohS.
        apply: sub_iso_to IZtau; [apply: zchar_trans_on | exact: zcharW].
        apply/allP; rewrite /= zchar_split (cfun_onS (setSD _ sHL)) ?Aalpha //.
        rewrite rpredB ?scale_zchar ?seqInd_zcharW ?(sYS eta1) ?sXS ?Xchi //.
          by rewrite sub_aut_zchar ?zchar_onG ?seqInd_zcharW ?cfAut_seqInd;
            rewrite ?sXS ?Xchi //; apply: seqInd_vcharW.
        by rewrite -Da_ // irr1_degree rpred_nat.
      suffices oYZ_R: orthogonal (b i *: Y1 - Z1 i) (R (chi i)).
        rewrite opprD opprK addrA -defXbZ cfdotC.
        rewrite (span_orthogonal oYZ_R) ?memv_span1 ?conjC0 //.
        exact: (zchar_span (R_X1 i rp_i)).
      apply/orthoPl=> aa Raa.
      rewrite cfdotBl cfdotZl (orthoPl (oZ1R i _)) //.
      by rewrite subr0 cfdotC; have [-> | [_ ->]] := defY1;
        rewrite ?cfdotNr (orthogonalP (oRY i _)) ?map_f ?cfAut_seqInd //;
        by rewrite ?(mulr0, oppr0, rmorph0).
    have leba i: i \in rp -> b i <= a_ i.
      move=> rp_i; have ai_gt0: a_ i > 0 by rewrite -Da_ ?irr1_gt0.
      have /orP [b_le0|b_ge0] := Rb i rp_i; last first.
        by rewrite (ler_trans b_ge0) ?ltrW.
      rewrite -(@ler_pexpn2r _ 2) //; last exact: ltrW.
      apply: ler_trans (_ : '[b i *: Y1 - Z1 i] <= _).
        rewrite cfnormBd; last by rewrite cfdotZl cfdotC oZY1 ?conjC0 ?mulr0.
        rewrite cfnormZ (normr_idP _) // n1Y1 mulr1 addrC -subr_ge0 addrK.
        exact: cfnorm_ge0.
      rewrite -(ler_add2l '[X1 i]) -cfnormBd; last first.
        rewrite cfdotBr cfdotZr (span_orthogonal (oRY i _)) //; last first.
        - exact: (zchar_span YtauY1).
        - exact: (zchar_span (R_X1 i rp_i)).
        rewrite mulr0 sub0r cfdotC (span_orthogonal (oZ1R i _)) ?raddf0 //.
          exact: memv_span1.
        exact: (zchar_span (R_X1 i rp_i)).
      have Salpha: alpha i \in 'Z[S, L^#].
        rewrite zchar_split (cfun_onS (setSD _ sHL)) ?Aalpha //.
        rewrite rpredB ?scale_zchar ?seqInd_zcharW
                   ?(sYS _ Yeta1) ?sXS ?Xchi //.
        by rewrite -Da_ // irr1_degree rpred_nat.
      rewrite  opprD opprK addrA -defXbZ // Itau ?Salpha //.
      rewrite cfnormBd; last first.
        by rewrite cfdotZr (orthogonalP oXY) ?mulr0 ?Xchi.
      rewrite cfnormZ (normr_idP _) ?(ltrW ai_gt0) //.
      have [_ /(_ eta1)->//] := orthonormalP oY; rewrite eqxx mulr1 ler_add2r.
      by have [] := ub_alpha i rp_i.
    have{leba} eq_ab: {in rp, a_ =1 b}.
      move=> i rp_i; apply/eqP; rewrite -subr_eq0; apply/eqP.
      apply: (mulfI (irr1_neq0 i)); rewrite mulr0 Da_ // mulrBr.
      move: i rp_i; apply: psumr_eq0P => [i rp_i | ].
        by rewrite subr_ge0 ler_pmul2l ?leba // -Da_ ?irr1_gt0.
      have [X2 oX2Y /(congr1 (cfdotr Y1))] := Dpsi1 i0 nzi0.
      rewrite sumrB sum_a2 sum_alpha /tau linear_sum /= cfdot_suml cfdotBl.
      rewrite (span_orthogonal oX2Y) ?memv_span1 ?(zchar_span YtauY1) // add0r.
      rewrite cfdotZl n1Y1 mulr1 => /(canLR (@opprK _)) <-.
      rewrite -opprD -big_split big1 ?oppr0 //= => i rp_i.
      rewrite linearZ cfdotZl /= -/tau defXbZ addrC cfdotDl oZY1 addr0.
      rewrite cfdotBl cfdotZl n1Y1 mulr1.
      rewrite (span_orthogonal (oRY i _)) ?(zchar_span YtauY1) //.
        by rewrite add0r mulrN subrr.
      exact: (zchar_span (R_X1 i rp_i)).
    exists (X1 k).
      apply/orthoPl=> psi /memv_span Ypsi.
      by rewrite (span_orthogonal (oRY k _)) // (zchar_span (R_X1 k rp_k)).
    apply/eqP; rewrite -/a def_xi -a_k defXbZ addrC -subr_eq0 eq_ab // addrK.
    have n1eta1: '[eta1] = 1 by have [_ -> //] := orthonormalP oY; rewrite eqxx.
    rewrite -cfnorm_eq0 -(inj_eq (addrI '[b k *: Y1])).
    have [_ [|_]] := ub_alpha k rp_k.
      rewrite cfnormBd; last by rewrite cfdotZl cfdotC oZY1 conjC0 mulr0.
      by rewrite addrC !cfnormZ eq_ab // n1Y1 n1eta1 -subr_ge0 addrK cfnorm_ge0.
    rewrite cfnormBd; last by rewrite cfdotZl cfdotC oZY1 conjC0 mulr0.
    by move=> -> _; rewrite addr0 !cfnormZ eq_ab // n1Y1 n1eta1.
  have oX: pairwise_orthogonal X by rewrite (sub_pairwise_orthogonal sXS).
  have [_ oYY] := orthonormalP oY.
  have [[N_S _ _] [_ /(_ _ _)/zcharW/=Ztau] _ _ _] := scohS.
  have n1eta: '[eta1] = 1 by rewrite oYY ?eqxx.
  have n1Y1: '[Y1] = 1.
    have [_ oYYt] := orthonormalP oYtau.
    have [-> | [_ ->]] := defY1;
      by rewrite ?cfnormN oYYt ?eqxx ?map_f // cfAut_seqInd.
  have YtauY1: Y1 \in <<map tau1 Y>>%VS.
    by have [-> | [_ ->]] := defY1;
      rewrite ?memvN memv_span ?map_f ?cfAut_seqInd.
  have Z_Y1: Y1 \in 'Z[irr G].
    by case: defY1 => [|[_]] ->; rewrite ?rpredN Ztau1 ?mem_zchar ?ccY.
  have Zalpha xi: xi \in X -> xi - a xi *: eta1 \in 'Z[S, L^#].
    move=> Xxi; rewrite zcharD1E rpredB ?scale_zchar;
                rewrite ?seqInd_zcharW ?(sXS xi) ?sYS //.
    by rewrite !cfunE (uniY eta1) //= subr_eq0; have [<-] := Dxa xi Xxi.
  have Zbeta eta: eta \in Y -> eta - eta1 \in 'Z[S, L^#].
    move=> Yeta; rewrite zcharD1E rpredB ?seqInd_zcharW ?sYS //=.
    by rewrite !cfunE !uniY ?subrr.
  have nza xi: xi \in X -> a xi != 0.
    move=> Xxi; have [/eqP Dxi1 _] := Dxa _ Xxi; apply: contraTneq Dxi1 => ->.
    by rewrite mul0r (seqInd1_neq0 _ Xxi).
  have alphaY xi: xi \in X -> '[tau (xi - a xi *: eta1), Y1] = - a xi.
    case/Dxa=> _ [X1 oX1Y ->]; rewrite cfdotBl cfdotZl n1Y1 mulr1.
    by rewrite (span_orthogonal oX1Y) ?memv_span1 ?add0r.
  have betaY eta: eta \in Y -> '[tau (eta - eta1), Y1] = (eta == eta1)%:R - 1.
    move=> Yeta; rewrite -Dtau1; last first.
      by rewrite zchar_split (zchar_on (Zbeta eta _)) ?rpredB ?seqInd_zcharW.
    rewrite raddfB cfdotBl.
    have [-> | [szY2 ->]] := defY1.
      by rewrite !{1}Itau1 ?seqInd_zcharW // !oYY // !eqxx.
    rewrite !cfdotNr opprK !{1}Itau1 ?oYY ?seqInd_zcharW ?cfAut_seqInd //.
    have defY: (eta1 :: eta1^*)%CF =i Y.
      apply: proj1 (leq_size_perm _ _ _); last by rewrite szY2.
        by rewrite /= inE eq_sym (seqInd_conjC_neq _ _ _ Yeta1).
      by apply/allP; rewrite /= Yeta1 cfAut_seqInd.
    rewrite -defY !inE in Yeta; case/pred2P: Yeta => ->.
      rewrite eqxx eq_sym (negPf (seqInd_conjC_neq _ _ _ Yeta1)) //.
      by rewrite addrC !subrr.
    by rewrite eqxx eq_sym (negPf (seqInd_conjC_neq _ _ _ Yeta1)) ?add0r ?addr0.
  pose tau2_X xi := tau (xi - a xi *: eta1) + a xi *: Y1.
  pose tau3_Y eta := tau (eta - eta1) + Y1.
  have Itau2_X: {in X, isometry tau2_X, to 'Z[irr G]}.
    split=> [xi1 xi2 Xxi1 Xxi2 | xi Xxi]; last first.
      by rewrite rpredD ?rpredZ_Cint ?Za ?Ztau ?Zalpha.
    rewrite /= cfdotDl !cfdotDr Itau ?Zalpha // cfdotBl !cfdotBr opprB !cfdotZr.
    rewrite !aut_Cint ?Za // !cfdotZl (cfdotC Y1) !alphaY // n1Y1 n1eta rmorphN.
    rewrite aut_Cint // (cfdotC eta1) !(orthogonalP oXY _ eta1) // conjC0.
    by rewrite  !mulr0 !subr0 !mulr1 !mulrN mulrC !addrA subrK addrK.
  have{Itau2_X} [tau2 Dtau2 Itau2] := Zisometry_of_iso oX Itau2_X.
  have{Itau2} cohX: coherent_with X L^# tau tau2.
    split=> // xi; rewrite zcharD1E => /andP[/zchar_expansion[]// z Zz ->{xi}].
    pose sum_za := \sum_(xi <- X) z xi * a xi => /eqP sum_xi_0.
    have{sum_xi_0} sum_za_0: sum_za = 0.
      apply: (mulIf (neq0CG W1)); rewrite mul0r -{}sum_xi_0 sum_cfunE mulr_suml.
      by apply: eq_big_seq => xi /Dxa[xi_1 _]; rewrite !cfunE xi_1 mulrA.
    rewrite -[rhs in tau rhs](subrK (sum_za *: eta1)) {1}scaler_suml -sumrB.
    rewrite -[tau _](addrK (sum_za *: Y1)) {1 3}sum_za_0 !scale0r addr0 subr0.
    rewrite scaler_suml !raddf_sum [tau _]raddf_sum -big_split /= -/tau.
    apply: eq_big_seq => xi Xxi; rewrite raddfZ_Cint //= Dtau2 //.
    by rewrite -!scalerA -scalerBr [tau _]linearZ -scalerDr.
  have Itau3_Y: {in Y, isometry tau3_Y, to 'Z[irr G]}.
    split=> [eta3 eta4 Yeta3 Yeta4 | eta Yeta]; last first.
      by rewrite rpredD // Ztau ?Zbeta.
    rewrite /= cfdotDl !cfdotDr n1Y1 (cfdotC Y1) !betaY // Itau ?Zbeta //.
    rewrite  cfdotBl !cfdotBr !oYY // eqxx rmorphB rmorph1 rmorph_nat subrK.
    rewrite (eq_sym eta1) opprB !addrA 3!(addrAC _ (- _)) addrK.
    by rewrite(addrAC _ 1) subrK addrK.
  have{oY} oY := orthonormal_orthogonal oY.
  have{Itau3_Y} [tau3 Dtau3 Itau3] := Zisometry_of_iso oY Itau3_Y.
  have{Itau3 cohY} cohY: coherent_with Y L^# tau tau3.
    split=> // eta; rewrite zcharD1E => /andP[/zchar_expansion[]//z Zz ->{eta}].
    pose sum_z := \sum_(eta <- Y) z eta => /eqP sum_eta_0.
    have{sum_eta_0} sum_z_0: sum_z = 0.
      apply: (mulIf (neq0CG W1)); rewrite mul0r -sum_eta_0 sum_cfunE mulr_suml.
      by apply: eq_big_seq => xi /uniY eta_1; rewrite !cfunE eta_1.
    rewrite -[rhs in tau rhs](subrK (sum_z *: eta1)) {1}scaler_suml -sumrB.
    rewrite -[tau _](addrK (sum_z *: Y1)) {1 3}sum_z_0 !scale0r addr0 subr0.
    rewrite scaler_suml !raddf_sum [tau _]raddf_sum -big_split /= -/tau.
    apply: eq_big_seq => eta Yeta; rewrite raddfZ_Cint //= Dtau3 //.
    by rewrite -scalerBr [tau _]linearZ -scalerDr.
  have [-> | ] := altP (@nilP _ X); first by exists tau3.
  rewrite -lt0n -has_predT => /hasP[xi1 Xxi1 _].
  have: tau (xi1 - a xi1 *: eta1) = tau2 xi1 - tau3 (a xi1 *: eta1).
    rewrite [tau3 _]linearZ Dtau2 //= Dtau3 // /tau3_Y subrr [tau 0]linear0.
    by rewrite add0r addrK.
  apply: (bridge_coherent scohS ccsXS cohX ccsYS cohY X'Y).
  by rewrite (zchar_on (Zalpha _ Xxi1)) // rpredZ_Cint ?mem_zchar.
pose wf S1 := cfConjC_subset S1 S /\ {subset X ++ Y <= S1}.
pose S1 := [::] ++ X ++ Y; set S2 := [::] in S1; rewrite -[X ++ Y]/S1 in cohXY.
have wfS1: wf S1.
  do 2!split=> //; rewrite /S1 /= ?cat_uniq ?uX ?uY ?(introT hasPn) //.
    by apply/allP; rewrite all_cat !(introT allP).
  by move=> phi; rewrite !mem_cat => /orP[/ccX|/ccY]->; rewrite ?orbT.
move: {2}_.+1 (ltnSn (size S - size S1)) => n.
elim: n => // n IHn in (S2) S1 wfS1 cohXY *; rewrite ltnS => leSnS1.
have [ccsS1S sXYS1] := wfS1; have [uS1 sS1S ccS1] := ccsS1S.
have [sSS1 | /allPn[psi /= Spsi notS1psi]] := altP (@allP _ (mem S1) S).
  exact: subset_coherent cohXY.
have [_ _ ccS] := uccS.
have [neq_psi_c Spsic] := (hasPn nrS _ Spsi, ccS _ Spsi).
have wfS1': wf [:: psi, psi^* & S1]%CF.
  split; last by move=> xi XYxi; rewrite !inE sXYS1 ?orbT.
  split=> [|xi|xi]; rewrite /= !inE.
  - by rewrite negb_or eq_sym neq_psi_c notS1psi (contra (ccS1 _)) ?cfConjCK.
  - by do 2?[case/predU1P=> [-> //|]] => /sS1S.
  rewrite (inv_eq (@cfConjCK _ _)) (can_eq (@cfConjCK _ _)) orbCA !orbA.
  by case: pred2P => // _ /ccS1.
apply: (IHn [:: psi, psi^* & S2]%CF) => //; last first.
  rewrite -subSn ?uniq_leq_size //; try by have [[]] := wfS1'.
  by rewrite /= subSS (leq_trans _ leSnS1) // leq_sub2l ?leqW.
have ltZH': Z \proper H^`(1)%g.
  rewrite properEneq sZH' andbT; apply: contraNneq notS1psi => eqZH'.
  have [i /setDP[_ nt_i] ->] := seqIndP Spsi; rewrite sXYS1 // mem_cat.
  rewrite !mem_seqInd ?normal1 //= -eqZH' !inE in nt_i *.
  by rewrite sub1G nt_i andbT orNb.
have: [/\ eta1 \in S1, psi \in S & psi \notin S1].
  by rewrite Spsi sXYS1 //  mem_cat Yeta1 orbT.
have /seqIndC1P[i nzi Dpsi] := Spsi.
move/(extend_coherent scohS ccsS1S); apply; split=> //.
  rewrite (uniY _ Yeta1) Dpsi cfInd1 // (index_sdprod defL) dvdC_mulr //.
  by rewrite Cint_Cnat ?Cnat_irr1.
rewrite !big_cat //= (big_rem _ Yeta1) /= addrC -!addrA -big_cat //=.
rewrite sum_seqIndD_square ?normal1 ?sub1G // indexg1 addrC.
rewrite -subr_gt0 -!addrA ltr_spaddl //.
  have /irrY/irrP[j ->] := Yeta1.
  by rewrite cfnorm_irr divr1 exprn_gt0 ?irr1_gt0.
rewrite big_seq addr_ge0 ?sumr_ge0 // => [phi Sphi|].
  rewrite mulr_ge0 ?invr_ge0 ?cfnorm_ge0 ?exprn_ge0 // ?char1_pos //.
  suffices /seqInd_char: phi \in S by apply: char1_ge0.
  rewrite sS1S // !mem_cat; rewrite mem_cat in Sphi.
  by case/orP: Sphi => [/mem_rem-> | ->]; rewrite ?orbT.
rewrite subr_ge0 -(Lagrange_index sHL sZH) -oW1 natrM mulrC -mulrA.
rewrite uniY ?ler_pmul2l ?gt0CG //.
rewrite  -(prednK (cardG_gt0 Z)) [zz in zz - 1]mulrSr addrK -natrM.
rewrite Dpsi cfInd1 // -oW1.
rewrite -(@ler_pexpn2r _ 2) -?topredE /= ?mulr_ge0 ?ler0n //; last first.
  by rewrite char1_ge0 ?irr_char.
rewrite !exprMn -!natrX mulrA -natrM.
apply: ler_trans (_ : (4 * #|W1| ^ 2)%:R * #|H : Z|%:R <= _).
  rewrite ler_pmul2l; last by rewrite ltr0n muln_gt0 !expn_gt0 cardG_gt0.
  rewrite (ler_trans (irr1_bound i)) // ler_nat dvdn_leq // indexgS //.
  by rewrite (subset_trans sZZ) // -cap_cfcenter_irr bigcap_inf.
rewrite -natrM ler_nat expnMn mulnC -mulnA leq_pmul2l //.
have [in_caseA | in_caseB] := boolP caseA.
  have regW1Z: semiregular Z W1.
    have [in_c1 | in_c2] := boolP case_c1.
      move=> x /(Frobenius_reg_ker in_c1) regHx; apply/trivgP.
      by rewrite -regHx setSI.
    have [/= _ [_ [_ _ _ prW1H] _] _ _] := c2W2 in_c2.
    move=> x /prW1H prHx; apply/trivgP; rewrite -((_ =P [1]) in_caseA) -prHx.
    by rewrite subsetI subIset ?sZZ // setSI.
  rewrite -(mul1n (4 * _)%N) leq_mul // -(expnMn 2 _ 2) leq_exp2r //.
  rewrite dvdn_leq //; first by rewrite -subn1 subn_gt0 cardG_gt1.
  rewrite Gauss_dvd ?(@pnat_coprime 2) -?odd_2'nat ?(oddSg sW1L) //.
  rewrite dvdn2 -{1}subn1 odd_sub // (oddSg (normal_sub nsZL)) //=.
  by rewrite regular_norm_dvd_pred // (subset_trans sW1L) ?normal_norm.
rewrite -(muln1 (4 * _)%N) leq_mul //; last first.
  by rewrite expn_gt0 -subn1 subn_gt0 orbF cardG_gt1.
rewrite -(expnMn 2 _ 2) -(Lagrange_index (der_sub 1 H) sZH') leq_mul //.
  rewrite -(prednK (indexg_gt0 _ _)) leqW // dvdn_leq //.
    by rewrite -subn1 subn_gt0 indexg_gt1 proper_subn.
  rewrite Gauss_dvd ?(@pnat_coprime 2) -?odd_2'nat ?(oddSg sW1L) //.
  rewrite dvdn2 -{1}subn1 odd_sub // -card_quotient ?der_norm //.
  rewrite quotient_odd ?(oddSg sHL) //=.
  rewrite (card_isog (quotient_isog (subset_trans sW1L nH'L) _)); last first.
    by rewrite coprime_TIg ?(coprimeSg (der_sub 1 H)).
  exact: Frobenius_dvd_ker1 frobL1.
rewrite -(prednK (indexg_gt0 _ _)) leqW // dvdn_leq //.
  by rewrite -subn1 subn_gt0 indexg_gt1 proper_subn.
rewrite Gauss_dvd ?(@pnat_coprime 2) -?odd_2'nat ?(oddSg sW1L) //.
rewrite dvdn2 -{1}subn1 odd_sub //.
rewrite -card_quotient ?(subset_trans (der_sub 1 H)) //.
rewrite quotient_odd ?(oddSg (der_sub 1 H)) ?(oddSg sHL) //=.
have /andP[sZL nZL] := nsZL.
rewrite (card_isog (quotient_isog (subset_trans sW1L nZL) _)); last first.
  by rewrite coprime_TIg ?(coprimeSg sZH).
suffices: [Frobenius (H^`(1) / Z) <*> (W1 / Z) = (H^`(1) / Z) ><| (W1 / Z)]%g.
  exact: Frobenius_dvd_ker1.
suffices: [Frobenius (L / Z) = (H / Z) ><| (W1 / Z)]%g.
  apply: Frobenius_subl (quotientS Z (der_sub 1 H)) _.
    by rewrite quotient_neq1 // (normalS sZH' (der_sub 1 H)).
  by rewrite quotient_norms ?(subset_trans sW1L).
apply: (Frobenius_coprime_quotient defL nsZL) => //; split=> [|x W1x].
  exact: sub_proper_trans sZH' ltH'H.
have /caseB_P[/c2W2[_ [_ [_ _ _ -> //] _] _ _] _ _] := in_caseB.
by rewrite /Z (negPf in_caseB).
Qed.

End Six.



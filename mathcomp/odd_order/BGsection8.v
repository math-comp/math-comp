(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div fintype path.
Require Import finset prime fingroup automorphism action gproduct gfunctor.
Require Import center commutator pgroup gseries nilpotent sylow abelian maximal.
Require Import BGsection1 BGsection5 BGsection6 BGsection7.

(******************************************************************************)
(*   This file covers B & G, section 8, i.e., the proof of two special cases  *)
(* of the Uniqueness Theorem, for maximal groups with Fitting subgroups of    *)
(* rank at least 3.                                                           *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Section Eight.

Variable gT : minSimpleOddGroupType.
Local Notation G := (TheMinSimpleOddGroup gT).
Implicit Types H M A X P : {group gT}.
Implicit Types p q r : nat.

Local Notation "K ` p" := 'O_(nat_pred_of_nat p)(K)
  (at level 8, p at level 2, format "K ` p") : group_scope.
Local Notation "K ` p" := 'O_(nat_pred_of_nat p)(K)%G : Group_scope.

(* This is B & G, Theorem 8.1(a). *)
Theorem non_pcore_Fitting_Uniqueness p M A0 :
    M \in 'M -> ~~ p.-group ('F(M)) -> A0 \in 'E*_p('F(M)) -> 'r_p(A0) >= 3 ->
  'C_('F(M))(A0)%G \in 'U.
Proof.
set F := 'F(M) => maxM p'F /pmaxElemP[/=/setIdP[sA0F abelA0] maxA0].
have [pA0 cA0A0 _] := and3P abelA0; rewrite (p_rank_abelem abelA0) => dimA0_3.
rewrite (uniq_mmax_subset1 maxM) //= -/F; last by rewrite subIset ?Fitting_sub.
set A := 'C_F(A0); pose pi := \pi(A).
have [sZA sAF]: 'Z(F) \subset A /\ A \subset F by rewrite subsetIl setIS ?centS.
have nilF: nilpotent F := Fitting_nil _.
have nilZ := nilpotentS (center_sub _) nilF.
have piZ: \pi('Z(F)) = \pi(F) by rewrite pi_center_nilpotent.
have def_pi: pi = \pi(F).
  by apply/eq_piP=> q; apply/idP/idP; last rewrite -piZ; exact: piSg.
have def_nZq: forall q, q \in pi -> 'N('Z(F)`q) = M.
  move=> q; rewrite def_pi -piZ -p_part_gt1.
  rewrite -(card_Hall (nilpotent_pcore_Hall _ nilZ)) cardG_gt1 /= -/F => ntZ.
  apply: mmax_normal => //=; apply: char_normal_trans (Fitting_normal _).
  exact: char_trans (pcore_char _ _) (center_char _).
have sCqM: forall q, q \in pi -> 'C(A`q) \subset M.
  move=> q; move/def_nZq <-; rewrite cents_norm // centS //.
  rewrite (sub_Hall_pcore (nilpotent_pcore_Hall _ _)) ?pcore_pgroup //.
    by apply: nilpotentS (Fitting_nil M); exact: subsetIl.
  exact: subset_trans (pcore_sub _ _) _.
have sA0A: A0 \subset A by rewrite subsetI sA0F.
have pi_p: p \in pi.
  by apply: (piSg sA0A); rewrite -[p \in _]logn_gt0 (leq_trans _ dimA0_3).
have sCAM: 'C(A) \subset M.
  by rewrite (subset_trans (centS (pcore_sub p _))) ?sCqM.
have prM: M \proper G := mmax_proper maxM; have solM := mFT_sol prM.
have piCA: pi.-group('C(A)).
  apply/pgroupP=> q q_pr; case/Cauchy=> // x cAx oxq; apply/idPn=> pi'q.
  have Mx := subsetP sCAM x cAx; pose C := 'C_F(<[x]>).
  have sAC: A \subset C by rewrite subsetI sAF centsC cycle_subG.
  have sCFC_C: 'C_F(C) \subset C.
    by rewrite (subset_trans _ sAC) ?setIS // centS ?(subset_trans _ sAC). 
  have cFx: x \in 'C_M(F).
    rewrite inE Mx -cycle_subG coprime_nil_faithful_cent_stab //=.
      by rewrite cycle_subG (subsetP (gFnorm _ _)).
    by rewrite -orderE coprime_pi' ?cardG_gt0 // -def_pi oxq pnatE.
  case/negP: pi'q; rewrite def_pi mem_primes q_pr cardG_gt0 -oxq cardSg //.
  by rewrite cycle_subG (subsetP (cent_sub_Fitting _)).
have{p'F} pi_alt q: exists2 r, r \in pi & r != q.
  have [<-{q} | ] := eqVneq p q; last by exists p.
  rewrite def_pi; apply/allPn; apply: contra p'F => /allP/=pF.
  by apply/pgroupP=> q q_pr qF; rewrite !inE pF // mem_primes q_pr cardG_gt0.
have sNZqXq' q X:
  A \subset X -> X \proper G -> 'O_q^'('N_X('Z(F)`q)) \subset 'O_q^'(X).
- move=> sAX prX; have sZqX: 'Z(F)`q \subset X.
    exact: subset_trans (pcore_sub _ _) (subset_trans sZA sAX).
  have cZqNXZ: 'O_q^'('N_X('Z(F)`q)) \subset 'C('Z(F)`q).
    have coNq'Zq: coprime #|'O_q^'('N_X('Z(F)`q))| #|'Z(F)`q|.
      by rewrite coprime_sym coprime_pcoreC.
    rewrite (sameP commG1P trivgP) -(coprime_TIg coNq'Zq) subsetI commg_subl /=.
    rewrite commg_subr /= andbC (subset_trans (pcore_sub _ _)) ?subsetIr //=.
    by rewrite (char_norm_trans (pcore_char _ _)) ?normsG // subsetI sZqX normG.
  have: 'O_q^'('C_X(('Z(F))`q)) \subset 'O_q^'(X).
    by rewrite p'core_cent_pgroup ?mFT_sol // /psubgroup sZqX pcore_pgroup.
  apply: subset_trans; apply: subset_trans (pcoreS _ (subcent_sub _ _)).
  by rewrite !subsetI subxx cZqNXZ (subset_trans (pcore_sub _ _)) ?subsetIl.
have sArXq' q r X:
  q \in pi -> q != r -> A \subset X -> X \proper G -> A`r \subset 'O_q^'(X).
- move=> pi_q r'q sAX prX; apply: subset_trans (sNZqXq' q X sAX prX).
  apply: subset_trans (pcoreS _ (subsetIr _ _)).
  rewrite -setIA (setIidPr (pcore_sub _ _)) subsetI.
  rewrite (subset_trans (pcore_sub _ _)) //= def_nZq //.
  apply: subset_trans (pcore_Fitting _ _); rewrite -/F.
  rewrite (sub_Hall_pcore (nilpotent_pcore_Hall _ nilF)) //; last first.
    exact: subset_trans (pcore_sub _ _) sAF.
  by apply: (pi_pnat (pcore_pgroup _ _)); rewrite !inE eq_sym.
have cstrA: normed_constrained A.
  split=> [||X Y sAX prX].
  - by apply/eqP=> A1; rewrite /pi /= A1 cards1 in pi_p.
  - exact: sub_proper_trans (subset_trans sAF (Fitting_sub _)) prM.
  rewrite !inE -/pi -andbA; case/and3P=> sYX pi'Y nYA.
  rewrite -bigcap_p'core subsetI sYX; apply/bigcapsP=> [[q /= _] pi_q].
  have [r pi_r q'r] := pi_alt q.
  have{sArXq'} sArXq': A`r \subset 'O_q^'(X) by apply: sArXq'; rewrite 1?eq_sym.
  have cA_CYr: 'C_Y(A`r) \subset 'C(A).
    have coYF: coprime #|Y| #|F|.
      by rewrite coprime_sym coprime_pi' ?cardG_gt0 // -def_pi.
    rewrite (sameP commG1P trivgP) -(coprime_TIg coYF) commg_subI //.
      by rewrite setIS // (subset_trans (sCqM r pi_r)) // gFnorm.
    by rewrite subsetI subsetIl.
  have{cA_CYr} CYr1: 'C_Y(A`r) = 1.
    rewrite -(setIid Y) setIAC coprime_TIg // (coprimeSg cA_CYr) //.
    by rewrite (pnat_coprime piCA).
  have{CYr1} ->: Y :=: [~: Y, A`r].
    rewrite -(mulg1 [~: Y, _]) -CYr1 coprime_cent_prod //.
    - by rewrite (subset_trans (pcore_sub _ _)).
    - rewrite coprime_sym (coprimeSg (pcore_sub _ _)) //= -/A.
      by rewrite coprime_pi' ?cardG_gt0.
    by rewrite mFT_sol // (sub_proper_trans sYX).
  rewrite (subset_trans (commgS _ sArXq')) // commg_subr.
  by rewrite (char_norm_trans (pcore_char _ _)) ?normsG.
have{cstrA} nbyApi'1 q: q \in pi^' -> |/|*(A; q) = [set 1%G].
  move=> pi'q; have trA: [transitive 'O_pi^'('C(A)), on |/|*(A; q) | 'JG].
    apply: normed_constrained_rank3_trans; rewrite //= -/A.
    rewrite -rank_abelem // in dimA0_3; apply: leq_trans dimA0_3 (rankS _).
    by rewrite /= -/A subsetI sA0A centsC subsetIr.
  have [Q maxQ defAmax]: exists2 Q, Q \in |/|*(A; q) & |/|*(A; q) = [set Q].
    case/imsetP: trA => Q maxQ defAmax; exists Q; rewrite // {maxQ}defAmax.
    suffices ->: 'O_pi^'('C(A)) = 1 by rewrite /orbit imset_set1 act1.
    rewrite -(setIidPr (pcore_sub _ _)) coprime_TIg //.
    exact: pnat_coprime piCA (pcore_pgroup _ _).
  have{maxQ} qQ: q.-group Q by move: maxQ; rewrite inE => /maxgroupp/andP[].
  have [<- // |] := eqVneq Q 1%G; rewrite -val_eqE /= => ntQ.
  have{defAmax trA} defFmax: |/|*(F; q) = [set Q].
    apply/eqP; rewrite eqEcard cards1 -defAmax.
    have snAF: A <|<| F by rewrite nilpotent_subnormal ?Fitting_nil.
    have piF: pi.-group F by rewrite def_pi /pgroup pnat_pi ?cardG_gt0.
    case/(normed_trans_superset _ _ snAF): trA => //= _ /imsetP[R maxR _] -> _.
    by rewrite (cardsD1 R) maxR.
  have nQM: M \subset 'N(Q).
    apply/normsP=> x Mx; apply: congr_group; apply/set1P.
    rewrite -defFmax (acts_act (norm_acts_max_norm _ _)) ?defFmax ?set11 //.
    by apply: subsetP Mx; exact: gFnorm.
  have{nQM} nsQM: Q <| M.
    rewrite inE in maxM; case/maxgroupP: maxM => _ maxM.
    rewrite -(maxM 'N(Q)%G) ?normalG ?mFT_norm_proper //.
    exact: mFT_pgroup_proper qQ.
  have sQF: Q \subset F by rewrite Fitting_max ?(pgroup_nil qQ).
  rewrite -(setIidPr sQF) coprime_TIg ?eqxx // in ntQ.
  by rewrite coprime_pi' ?cardG_gt0 // -def_pi (pi_pnat qQ).
apply/subsetP=> H /setIdP[maxH sAH]; rewrite inE -val_eqE /=.
have prH: H \proper G := mmax_proper maxH; have solH := mFT_sol prH.
pose D := 'F(H); have nilD: nilpotent D := Fitting_nil H.
have card_pcore_nil := card_Hall (nilpotent_pcore_Hall _ _).
have piD: \pi(D) = pi.
  set sigma := \pi(_); have pi_sig: {subset sigma <= pi}.
    move=> q; rewrite -p_part_gt1 -card_pcore_nil // cardG_gt1 /= -/D.
    apply: contraR => /nbyApi'1 defAmax.
    have nDqA: A \subset 'N(D`q).
      rewrite (char_norm_trans (pcore_char _ _)) //.
      by rewrite (subset_trans sAH) ?gFnorm.
    have [Q]:= max_normed_exists (pcore_pgroup _ _) nDqA.
    by rewrite defAmax -subG1; move/set1P->.
  apply/eq_piP=> q; apply/idP/idP=> [|pi_q]; first exact: pi_sig.
  apply: contraLR (pi_q) => sig'q; have nilA := nilpotentS sAF nilF.
  rewrite -p_part_eq1 -card_pcore_nil // -trivg_card1 -subG1 /= -/A.
  have <-: 'O_sigma^'(H) = 1.
    apply/eqP; rewrite -trivg_Fitting ?(solvableS (pcore_sub _ _)) //.
    rewrite Fitting_pcore -(setIidPr (pcore_sub _ _)) coprime_TIg //.
    by rewrite coprime_pi' ?cardG_gt0 //; exact: pcore_pgroup.
  rewrite -bigcap_p'core subsetI (subset_trans (pcore_sub _ _)) //=.
  apply/bigcapsP=> [[r /= _] sig_r]; apply: sArXq' => //; first exact: pi_sig.
  by apply: contra sig'q; move/eqP <-.
have cAD q r: q != r -> D`q \subset 'C(A`r).
  move=> r'q; have [-> |] := eqVneq D`q 1; first by rewrite sub1G.
  rewrite -cardG_gt1 card_pcore_nil // p_part_gt1 piD => pi_q.
  have sArHq': A`r \subset 'O_q^'(H) by rewrite sArXq'.
  have coHqHq': coprime #|D`q| #|'O_q^'(H)| by rewrite coprime_pcoreC.
  rewrite (sameP commG1P trivgP) -(coprime_TIg coHqHq') commg_subI //.
    rewrite subsetI subxx /= p_core_Fitting (subset_trans (pcore_sub _ _)) //.
    exact: gFnorm.
  rewrite subsetI sArHq' (subset_trans (subset_trans (pcore_sub _ _) sAH)) //.
  by rewrite /= p_core_Fitting gFnorm.
have sDM: D \subset M.
  rewrite [D]FittingEgen gen_subG; apply/bigcupsP=> [[q /= _] _].
  rewrite -p_core_Fitting -/D; have [r pi_r r'q] := pi_alt q.
  by apply: subset_trans (sCqM r pi_r); apply: cAD; rewrite eq_sym.
have cApHp': A`p \subset 'C('O_p^'(H)).
  have coApHp': coprime #|'O_p^'(H)| #|A`p|.
    by rewrite coprime_sym coprime_pcoreC.
  have solHp': solvable 'O_p^'(H) by rewrite (solvableS (pcore_sub _ _)).
  have nHp'Ap: A`p \subset 'N('O_p^'(H)).
    by rewrite (subset_trans (subset_trans (pcore_sub _ _) sAH)) ?gFnorm.
  apply: subset_trans (coprime_cent_Fitting nHp'Ap coApHp' solHp').
  rewrite subsetI subxx centsC /= FittingEgen gen_subG.
  apply/bigcupsP=> [[q /= _] _]; have [-> | /cAD] := eqVneq q p.
    by rewrite -(setIidPl (pcore_sub p _)) TI_pcoreC sub1G.
  apply: subset_trans; rewrite p_core_Fitting -pcoreI.
  by apply: sub_pcore => r /andP[].
have sHp'M: 'O_p^'(H) \subset M.
  by apply: subset_trans (sCqM p pi_p); rewrite centsC.
have ntDp: D`p != 1 by rewrite -cardG_gt1 card_pcore_nil // p_part_gt1 piD.
have sHp'_NMDp': 'O_p^'(H) \subset 'O_p^'('N_M(D`p)).
  apply: subset_trans (pcoreS _ (subsetIr _ _)).
  rewrite -setIA (setIidPr (pcore_sub _ _)) /= (mmax_normal maxH) //.
    by rewrite subsetI sHp'M subxx.
  by rewrite /= p_core_Fitting pcore_normal.
have{sHp'_NMDp'} sHp'Mp': 'O_p^'(H) \subset 'O_p^'(M).
  have pM_D: p.-subgroup(M) D`p.
    by rewrite /psubgroup pcore_pgroup (subset_trans (pcore_sub _ _)).
  apply: subset_trans (p'core_cent_pgroup pM_D (mFT_sol prM)).
  apply: subset_trans (pcoreS _ (subcent_sub _ _)).
  rewrite !subsetI sHp'_NMDp' sHp'M andbT /= (sameP commG1P trivgP).
  have coHp'Dp: coprime #|'O_p^'(H)| #|D`p|.
    by rewrite coprime_sym coprime_pcoreC.
  rewrite -(coprime_TIg coHp'Dp) subsetI commg_subl commg_subr /=.
  by rewrite p_core_Fitting !(subset_trans (pcore_sub _ _)) ?gFnorm.
have sMp'H: 'O_p^'(M) \subset H.
  rewrite -(mmax_normal maxH (pcore_normal p H)) /= -p_core_Fitting //.
  rewrite -/D (subset_trans _ (cent_sub _)) // centsC.
  have solMp' := solvableS (pcore_sub p^' _) (mFT_sol prM).
  have coMp'Dp: coprime #|'O_p^'(M)| #|D`p|.
    by rewrite coprime_sym coprime_pcoreC.
  have nMp'Dp: D`p \subset 'N('O_p^'(M)).
    by rewrite (subset_trans (subset_trans (pcore_sub _ _) sDM)) ?gFnorm.
  apply: subset_trans (coprime_cent_Fitting nMp'Dp coMp'Dp solMp').
  rewrite subsetI subxx centsC /= FittingEgen gen_subG.
  apply/bigcupsP=> [[q /= _] _]; have [<- | /cAD] := eqVneq p q.
    by rewrite -(setIidPl (pcore_sub p _)) TI_pcoreC sub1G.
  rewrite centsC; apply: subset_trans.
  rewrite -p_core_Fitting Fitting_pcore pcore_max ?pcore_pgroup //=.
  rewrite /normal subsetI -pcoreI pcore_sub subIset ?gFnorm //=.
  rewrite pcoreI (subset_trans (pcore_sub _ _)) //= -/F centsC.
  case/dprodP: (nilpotent_pcoreC p nilF) => _ _ /= cFpp' _.
  rewrite centsC (subset_trans cFpp' (centS _)) //.
  have hallFp := nilpotent_pcore_Hall p nilF.
  by rewrite (sub_Hall_pcore hallFp).
have{sHp'Mp' sMp'H} eqHp'Mp': 'O_p^'(H) = 'O_p^'(M).
  apply/eqP; rewrite eqEsubset sHp'Mp'.
  apply: subset_trans (sNZqXq' p H sAH prH).
  apply: subset_trans (pcoreS _ (subsetIr _ _)).
  rewrite -setIA (setIidPr (pcore_sub _ _)) subsetI sMp'H /=.
  rewrite (mmax_normal maxM (char_normal_trans (pcore_char _ _) _)) //.
    by rewrite (char_normal_trans (center_char _)) ?Fitting_normal.
  by rewrite -cardG_gt1 card_pcore_nil // p_part_gt1 piZ -def_pi.
have ntHp': 'O_p^'(H) != 1.
  have [q pi_q p'q] := pi_alt p; have: D`q \subset 'O_p^'(H).
    by rewrite p_core_Fitting sub_pcore // => r; move/eqnP->.
  rewrite -proper1G; apply: proper_sub_trans; rewrite proper1G.
  by rewrite -cardG_gt1 card_pcore_nil // p_part_gt1 piD.
rewrite -(mmax_normal maxH (pcore_normal p^' H)) //= eqHp'Mp'.
by rewrite (mmax_normal maxM (pcore_normal _ _)) //= -eqHp'Mp'.
Qed.

(* This is B & G, Theorem 8.1(b). *)
Theorem SCN_Fitting_Uniqueness p M P A :
    M \in 'M -> p.-group ('F(M)) -> p.-Sylow(M) P ->
    'r_p('F(M)) >= 3 -> A \in 'SCN_3(P) ->
  [/\ p.-Sylow(G) P, A \subset 'F(M) & A \in 'U].
Proof.
set F := 'F(M) => maxM pF sylP dimFp3 scn3_A.
have [scnA dimA3] := setIdP scn3_A; have [nsAP defCA] := SCN_P scnA.
have cAA := SCN_abelian scnA; have sAP := normal_sub nsAP.
have [sPM pP _] := and3P sylP; have sAM := subset_trans sAP sPM.
have{dimA3} ntA: A :!=: 1 by case: eqP dimA3 => // ->; rewrite rank1.
have prM := mmax_proper maxM; have solM := mFT_sol prM.
have{pF} Mp'1: 'O_p^'(M) = 1.
  apply/eqP; rewrite -trivg_Fitting ?(solvableS (pcore_sub _ _)) //.
  rewrite Fitting_pcore -(setIidPr (pcore_sub _ _)) coprime_TIg //.
  exact: pnat_coprime (pcore_pgroup _ _).
have defF: F = M`p := Fitting_eq_pcore Mp'1.
have sFP: F \subset P by rewrite defF (pcore_sub_Hall sylP).
have sAF: A \subset F.
  rewrite defF -(pseries_pop2 _ Mp'1).
  exact: (odd_p_abelian_constrained (mFT_odd _) solM sylP cAA nsAP).
have sZA: 'Z(F) \subset A.
  by rewrite -defCA setISS ?centS // defF pcore_sub_Hall.
have sCAM: 'C(A) \subset M.
  have nsZM: 'Z(F) <| M := char_normal_trans (center_char _) (Fitting_normal _).
  rewrite -(mmax_normal maxM nsZM); last first.
    rewrite /= -(setIidPr (center_sub _)) meet_center_nil ?Fitting_nil //.
    by rewrite -proper1G (proper_sub_trans _ sAF) ?proper1G.
  by rewrite (subset_trans _ (cent_sub _)) ?centS.
have nsZL_M: 'Z('L(P)) <| M.
  by rewrite (Puig_center_normal (mFT_odd _) solM sylP).
have sNPM: 'N(P) \subset M.
  rewrite -(mmax_normal maxM nsZL_M).
    by rewrite (char_norm_trans (center_Puig_char P)).
  apply/eqP; move/(trivg_center_Puig_pgroup (pHall_pgroup sylP))=> P1.
  by rewrite -subG1 -P1 sAP in ntA.
have sylPG: p.-Sylow(G) P := mmax_sigma_Sylow maxM sylP sNPM.
split; rewrite // (uniq_mmax_subset1 maxM sAM).
have{scn3_A} scn3_A: A \in 'SCN_3[p] by apply/bigcupP; exists P; rewrite // inE.
pose K := 'O_p^'('C(A)); have sKF: K \subset F.
  have sKM: K \subset M := subset_trans (pcore_sub _ _) sCAM.
  apply: subset_trans (cent_sub_Fitting solM).
  rewrite subsetI sKM coprime_nil_faithful_cent_stab ?Fitting_nil //.
  - by rewrite (subset_trans (subset_trans (pcore_sub _ _) sCAM)) ?gFnorm.
  - by rewrite /= -/F defF coprime_pcoreC.
  have sACK: A \subset 'C_F(K) by rewrite subsetI sAF centsC pcore_sub.
  by rewrite /= -/F -/K (subset_trans _ sACK) //= -defCA setISS ?centS.
have{sKF} K1: K = 1 by rewrite -(setIidPr sKF) defF TI_pcoreC.
have p'nbyA_1 q: q != p -> |/|*(A; q) = [set 1%G].
  move=> p'q.
  have: [transitive K, on |/|*(A; q) | 'JG] by apply: Thompson_transitivity.
  case/imsetP=> Q maxQ; rewrite K1 /orbit imset_set1 act1 => defAmax.
  have nQNA: 'N(A) \subset 'N(Q).
    apply/normsP=> x Nx; apply: congr_group; apply/set1P; rewrite -defAmax.
    by rewrite (acts_act (norm_acts_max_norm _ _)).
  have{nQNA} nQF: F \subset 'N(Q).
    exact: subset_trans (subset_trans (normal_norm nsAP) nQNA).
  have defFmax: |/|*(F; q) = [set Q] := max_normed_uniq defAmax sAF nQF.
  have nQM: M \subset 'N(Q).
    apply/normsP=> x Mx; apply: congr_group; apply/set1P; rewrite -defFmax.
    rewrite (acts_act (norm_acts_max_norm _ _)) ?defFmax ?set11 //.
    by rewrite (subsetP (gFnorm _ _)).
  have [<- // | ntQ] := eqVneq Q 1%G.
  rewrite inE in maxQ; have [qQ _] := andP (maxgroupp maxQ).
  have{nQM} defNQ: 'N(Q) = M.
    by rewrite (mmax_norm maxM) // (mFT_pgroup_proper qQ).
  case/negP: ntQ; rewrite -[_ == _]subG1 -Mp'1 -defNQ pcore_max ?normalG //.
  exact: pi_pnat qQ _.
have{p'nbyA_1} p'nbyA_1 X:
  X \proper G -> p^'.-group X -> A \subset 'N(X) -> X :=: 1.
- move=> prX p'X nXA; have solX := mFT_sol prX.
  apply/eqP; rewrite -trivg_Fitting // -subG1 /= FittingEgen gen_subG.
  apply/bigcupsP=> [[q /= _] _]; have [-> | p'q] := eqVneq q p.
    rewrite -(setIidPl (pcore_sub _ _)) coprime_TIg //.
    by rewrite (pnat_coprime (pcore_pgroup _ _)).
  have [|R] := max_normed_exists (pcore_pgroup q X) (char_norm_trans _ nXA).
    exact: pcore_char.
  by rewrite p'nbyA_1 // => /set1P->.
apply/subsetPn=> [[H0 MA_H0 neH0M]].
have:= erefl [arg max_(H > H0 | (H \in 'M(A)) && (H != M)) #|H :&: M|`_p].
case: arg_maxP => [|H {H0 MA_H0 neH0M}]; first by rewrite MA_H0 -in_set1.
rewrite /= inE -andbA; case/and3P=> maxH sAH neHM maxHM _.
have prH: H \proper G by rewrite inE in maxH; exact: maxgroupp maxH.
have sAHM: A \subset H :&: M by rewrite subsetI sAH.
have [R sylR_HM sAR]:= Sylow_superset sAHM (pgroupS sAP pP).
have [/subsetIP[sRH sRM] pR _] := and3P sylR_HM.
have{sylR_HM} sylR_H: p.-Sylow(H) R. 
  have [Q sylQ] := Sylow_superset sRM pR; have [sQM pQ _] := and3P sylQ.
  case/eqVproper=> [defR | /(nilpotent_proper_norm (pgroup_nil pQ)) sRN].
    apply: (pHall_subl sRH (subsetT _)); rewrite pHallE subsetT /=.
    by rewrite -(card_Hall sylPG) (card_Hall sylP) defR (card_Hall sylQ).
  case/maximal_exists: (subsetT 'N(R)) => [nRG | [D maxD sND]].
    case/negP: (proper_irrefl (mem G)); rewrite -{1}nRG.
    rewrite mFT_norm_proper ?(mFT_pgroup_proper pR) //.
    by rewrite -proper1G (proper_sub_trans _ sAR) ?proper1G.
  move/implyP: (maxHM D); rewrite 2!inE {}maxD leqNgt.
  case: eqP sND => [->{D} sNM _ | _ sND].
    rewrite -Sylow_subnorm (pHall_subl _ _ sylR_HM) ?setIS //.
    by rewrite subsetI sRH normG.
  rewrite (subset_trans (subset_trans sAR (normG R)) sND); case/negP.
  rewrite -(card_Hall sylR_HM) (leq_trans (proper_card sRN)) //.
  rewrite -(part_pnat_id (pgroupS (subsetIl _ _) pQ)) dvdn_leq //.
  by rewrite partn_dvd ?cardG_gt0 // cardSg //= setIC setISS.
have Hp'1: 'O_p^'(H) = 1.
  apply: p'nbyA_1 (pcore_pgroup _ _) (subset_trans sAH (gFnorm _ _)).
  exact: sub_proper_trans (pcore_sub _ _) prH.
have nsZLR_H: 'Z('L(R)) <| H.
  exact: Puig_center_normal (mFT_odd _) (mFT_sol prH) sylR_H _.
have ntZLR: 'Z('L(R)) != 1.
  apply/eqP=> /(trivg_center_Puig_pgroup pR) R1.
  by rewrite -subG1 -R1 sAR in ntA.
have defH: 'N('Z('L(R))) = H := mmax_normal maxH nsZLR_H ntZLR.
have{sylR_H} sylR: p.-Sylow(G) R.
  rewrite -Sylow_subnorm setTI (pHall_subl _ _ sylR_H) ?normG //=.
  by rewrite -defH (char_norm_trans (center_Puig_char R)).
have nsZLR_M: 'Z('L(R)) <| M.
  have sylR_M := pHall_subl sRM (subsetT _) sylR.
  exact: Puig_center_normal (mFT_odd _) solM sylR_M _.
case/eqP: neHM; apply: group_inj.
by rewrite -defH (mmax_normal maxM nsZLR_M).
Qed.

(* This summarizes the two branches of B & G, Theorem 8.1. *)
Theorem Fitting_Uniqueness M : M \in 'M -> 'r('F(M)) >= 3 -> 'F(M)%G \in 'U.
Proof.
move=> maxM; have [p _ -> dimF3] := rank_witness 'F(M).
have prF: 'F(M) \proper G := sub_mmax_proper maxM (Fitting_sub M).
have [pF | npF] := boolP (p.-group 'F(M)).
  have [P sylP] := Sylow_exists p M; have [sPM pP _] := and3P sylP.
  have dimP3: 'r_p(P) >= 3.
    rewrite (p_rank_Sylow sylP) (leq_trans dimF3) //.
    by rewrite p_rankS ?Fitting_sub.
  have [A] := rank3_SCN3 pP (mFT_odd _) dimP3.
  by case/(SCN_Fitting_Uniqueness maxM pF)=> // _ sAF; exact: uniq_mmaxS.
case/p_rank_geP: dimF3 => A /setIdP[EpA dimA3].
have [A0 maxA0 sAA0] := @maxgroup_exists _ [pred X in 'E_p('F(M))] _ EpA.
have [_ abelA] := pElemP EpA; have pmaxA0: A0 \in 'E*_p('F(M)) by rewrite inE.
case/pElemP: (maxgroupp maxA0) => sA0F; case/and3P=> _ cA0A0 _.
have dimA0_3: 'r_p(A0) >= 3.
  by rewrite -(eqP dimA3) -(p_rank_abelem abelA) p_rankS.
have:= non_pcore_Fitting_Uniqueness maxM npF pmaxA0 dimA0_3.
exact: uniq_mmaxS (subsetIl _ _) prF.
Qed.

End Eight.


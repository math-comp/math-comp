(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div path fintype.
Require Import bigop finset prime fingroup morphism perm automorphism quotient.
Require Import action gproduct gfunctor pgroup cyclic center commutator.
Require Import gseries nilpotent sylow abelian maximal hall frobenius.
Require Import BGsection1 BGsection3 BGsection4 BGsection5 BGsection6.
Require Import BGsection7 BGsection9 BGsection10 BGsection12.

(******************************************************************************)
(*   This file covers B & G, section 13; the title subject of the section,    *)
(* prime and regular actions, was defined in the frobenius.v file.            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Section Section13.

Variable gT : minSimpleOddGroupType.
Local Notation G := (TheMinSimpleOddGroup gT).
Implicit Types p q q_star r : nat.
Implicit Types A E H K L M Mstar N P Q Qstar R S T U V W X Y Z : {group gT}.

Section OneComplement.

Variables M E : {group gT}.
Hypotheses (maxM : M \in 'M) (hallE : \sigma(M)^'.-Hall(M) E).

Let sEM : E \subset M := pHall_sub hallE.
Let sM'E : \sigma(M)^'.-group E := pHall_pgroup hallE.

(* This is B & G, Lemma 13.1. *)
Lemma Msigma_setI_mmax_central p H :
   H \in 'M -> p \in \pi(E) -> p \in \pi(H) -> p \notin \tau1(H) ->
   [~: M`_\sigma :&: H, M :&: H] != 1 -> gval H \notin M :^: G ->
 [/\ (*a*) forall P, P \subset M :&: H -> p.-group P ->
           P \subset 'C(M`_\sigma :&: H),
     (*b*) p \notin \tau2(H)
   & (*c*) p \in \tau1(M) -> p \in \beta(G)].
Proof.
move=> maxH piEp piHp t1H'p; set R := [~: _, _] => ntR notMGH.
have [q sMq piH'q]: exists2 q, q \in \sigma(M) & q \in \pi(H^`(1)).
  pose q := pdiv #|R|; have q_pr: prime q by rewrite pdiv_prime ?cardG_gt1.
  have q_dv : q %| _ := dvdn_trans (pdiv_dvd _) (cardSg _).
  exists q; last by rewrite mem_primes q_pr cardG_gt0 q_dv ?commgSS ?subsetIr.
  rewrite (pgroupP (pcore_pgroup _ M)) ?q_dv //.
  have sR_MsM: R \subset [~: M`_\sigma, M] by rewrite commgSS ?subsetIl.
  by rewrite (subset_trans sR_MsM) // commg_subl gFnorm.
have [Y sylY] := Sylow_exists q H^`(1); have [sYH' qY _] := and3P sylY.
have nsHbH: H`_\beta <| H := pcore_normal _ _; have [_ nHbH] := andP nsHbH.
have sYH := subset_trans sYH' (der_sub 1 H); have nHbY := subset_trans sYH nHbH.
have nsHbY_H: H`_\beta <*> Y <| H.
  rewrite -{2}(quotientGK nsHbH) -quotientYK ?cosetpre_normal //.
  rewrite (char_normal_trans _ (der_normal 1 _)) //= -quotient_der //.
  rewrite (nilpotent_Hall_pcore _ (quotient_pHall nHbY sylY)) ?pcore_char //.
  exact: Mbeta_quo_nil.
have sYNY: Y \subset 'N_H(Y) by rewrite subsetI sYH normG.
have{nsHbY_H} defH: H`_\beta * 'N_H(Y) = H.
  rewrite -(mulSGid sYNY) mulgA -(norm_joinEr nHbY).
  rewrite (Frattini_arg _ (pHall_subl _ _ sylY)) ?joing_subr //.
  by rewrite join_subG Mbeta_der1.
have ntY: Y :!=: 1 by rewrite -cardG_gt1 (card_Hall sylY) p_part_gt1.
have{ntY} [_] := sigma_Jsub maxM (pi_pgroup qY sMq) ntY.
have maxY_H: H \in 'M(Y) by apply/setIdP.
move/(_ E p H hallE piEp _ maxY_H notMGH) => b'p_t3Hp.
case t2Hp: (p \in \tau2(H)).
  have b'p: p \notin \beta(G) by case/tau2_not_beta: t2Hp.
  have rpH: 'r_p(H) = 2 by apply/eqP; case/andP: t2Hp.
  have p'Hb: p^'.-group H`_\beta.
    rewrite (pi_p'group (pcore_pgroup _ H)) // inE /=.
    by rewrite -predI_sigma_beta // negb_and b'p orbT.
  case: b'p_t3Hp; rewrite // -(p_rank_p'quotient p'Hb) ?subIset ?nHbH //=.
  by rewrite -quotientMidl defH p_rank_p'quotient ?rpH.
have [S sylS] := Sylow_exists p H; have [sSH pS _] := and3P sylS.
have sSH': S \subset H^`(1).
  have [sHp | sH'p] := boolP (p \in \sigma(H)).
    apply: subset_trans (Msigma_der1 maxH).
    by rewrite (sub_Hall_pcore (Msigma_Hall _)) // (pi_pgroup pS).
  have sH'_S: \sigma(H)^'.-group S by rewrite (pi_pgroup pS).
  have [F hallF sSF] := Hall_superset (mmax_sol maxH) sSH sH'_S.
  have t3Hp: p \in \tau3(H).
    have:= partition_pi_sigma_compl maxH hallF p.
    by rewrite (pi_sigma_compl hallF) inE /= sH'p piHp (negPf t1H'p) t2Hp.
  have [[F1 hallF1] [F3 hallF3]] := ex_tau13_compl hallF.
  have [F2 _ complFi] := ex_tau2_compl hallF hallF1 hallF3.
  have [[sF3F' nsF3F] _ _ _ _] := sigma_compl_context maxH complFi.
  apply: subset_trans (subset_trans sF3F' (dergS 1 (pHall_sub hallF))). 
  by rewrite (sub_normal_Hall hallF3) ?(pi_pgroup pS).
have sylS_H' := pHall_subl sSH' (der_sub 1 H) sylS.
split=> // [P sPMH pP | t1Mp]; last first.
  apply/idPn=> b'p; have [_ /(_ t1Mp)/negP[]] := b'p_t3Hp b'p.
  have p'Hb: p^'.-group H`_\beta.
    rewrite (pi_p'group (pcore_pgroup _ H)) // inE /=.
    by rewrite -predI_sigma_beta // negb_and b'p orbT.
  rewrite -p_rank_gt0 -(p_rank_p'quotient p'Hb) ?comm_subG ?subIset ?nHbH //=.
  rewrite quotient_der ?subIset ?nHbH // -quotientMidl defH -quotient_der //=.
  rewrite p_rank_p'quotient ?comm_subG // -(rank_Sylow sylS_H').
  by rewrite (rank_Sylow sylS) p_rank_gt0.
have nsHaH: H`_\alpha <| H := pcore_normal _ _; have [_ nHaH] := andP nsHaH.
have [sPM sPH] := subsetIP sPMH; have nHaS := subset_trans sSH nHaH.
have nsHaS_H: H`_\alpha <*> S <| H.
  rewrite -{2}(quotientGK nsHaH) -quotientYK ?cosetpre_normal //.
  rewrite (char_normal_trans _ (der_normal 1 _)) //= -quotient_der //.
  rewrite (nilpotent_Hall_pcore _ (quotient_pHall nHaS sylS_H')) ?pcore_char //.
  exact: Malpha_quo_nil.
have [sHaS_H nHaS_H] := andP nsHaS_H.
have sP_HaS: P \subset H`_\alpha <*> S.
  have [x Hx sPSx] := Sylow_subJ sylS sPH pP; apply: subset_trans sPSx _.
  by rewrite sub_conjg (normsP nHaS_H) ?groupV ?joing_subr.
have coHaS_Ms: coprime #|H`_\alpha <*> S| #|M`_\sigma|.
  rewrite (p'nat_coprime _ (pcore_pgroup _ _)) // -pgroupE norm_joinEr //.
  rewrite pgroupM andbC (pi_pgroup pS) ?(pnatPpi (pHall_pgroup hallE)) //=.
  apply: sub_pgroup (pcore_pgroup _ _) => r aHr.
  have [|_ ti_aH_sM _] := sigma_disjoint maxH maxM; first by rewrite orbit_sym.
  by apply: contraFN (ti_aH_sM r) => sMr; apply/andP.
rewrite (sameP commG1P trivgP) -(coprime_TIg coHaS_Ms) commg_subI ?setIS //.
by rewrite subsetI sP_HaS (subset_trans sPM) ?gFnorm.
Qed.

(* This is B & G, Corollary 13.2. *)
Corollary cent_norm_tau13_mmax p P H :
    (p \in \tau1(M)) || (p \in \tau3(M)) ->
    P \subset M -> p.-group P -> H \in 'M('N(P)) ->
 [/\ (*a*) forall P1, P1 \subset M :&: H -> p.-group P1 ->
           P1 \subset 'C(M`_\sigma :&: H),
     (*b*) forall X, X \subset E :&: H -> \tau1(H)^'.-group X ->
           X \subset 'C(M`_\sigma :&: H)
   & (*c*) [~: M`_\sigma :&: H, M :&: H] != 1 ->
           p \in \sigma(H) /\ (p \in \tau1(M) -> p \in \beta(H))].
Proof.
move=> t13Mp sPM pP /setIdP[maxH sNP_H].
have ntP: P :!=: 1.
  by apply: contraTneq sNP_H => ->; rewrite norm1 proper_subn ?mmax_proper.
have st2Hp: (p \in \sigma(H)) || (p \in \tau2(H)).
  exact: (prime_class_mmax_norm maxH pP sNP_H).
have not_MGH: gval H \notin M :^: G.
  apply: contraL st2Hp => /imsetP[x _ ->]; rewrite sigmaJ tau2J negb_or.
  by have:= t13Mp; rewrite -2!andb_orr !inE => /and3P[-> /eqP->].
set R := [~: _, _]; have [/commG1P | ntR] := altP (R =P 1).
  rewrite centsC => cMH; split=> // X sX_EH _; apply: subset_trans cMH => //.
  by rewrite (subset_trans sX_EH) ?setSI.
have piEp: p \in \pi(E).
  by rewrite (partition_pi_sigma_compl maxM) // orbCA t13Mp orbT.
have piHp: p \in \pi(H).
  by rewrite (partition_pi_mmax maxH) orbCA orbC -!orbA st2Hp !orbT.
have t1H'p: p \notin \tau1(H).
  by apply: contraL st2Hp; rewrite negb_or !inE => /and3P[-> /eqP->].
case: (Msigma_setI_mmax_central maxH piEp) => // cMsH t2H'p b_p.
split=> // [X sX_EH t1'X | _].
  have [sXE sXH] := subsetIP sX_EH.
  rewrite -(Sylow_gen X) gen_subG; apply/bigcupsP=> Q; case/SylowP=> q _ sylQ.
  have [-> | ntQ] := eqsVneq Q 1; first exact: sub1G.
  have piXq: q \in \pi(X) by rewrite -p_rank_gt0 -(rank_Sylow sylQ) rank_gt0.
  have [[piEq piHq] t1H'q] := (piSg sXE piXq, piSg sXH piXq, pnatPpi t1'X piXq).
  have [sQX qQ _] := and3P sylQ; have sXM := subset_trans sXE sEM.
  case: (Msigma_setI_mmax_central maxH piEq) => // -> //.
  by rewrite subsetI !(subset_trans sQX).
rewrite (negPf t2H'p) orbF in st2Hp.
by rewrite -predI_sigma_beta // {3}/in_mem /= st2Hp.
Qed.

(* This is B & G, Corollary 13.3(a). *)
Lemma cyclic_primact_Msigma p P :
  p.-Sylow(E) P -> cyclic P -> semiprime M`_\sigma P.
Proof.
move=> sylP cycP x /setD1P[]; rewrite -cycle_eq1 -cycle_subG => ntX sXP.
have [sPE pP _] := and3P sylP; rewrite -cent_cycle.
have sPM := subset_trans sPE sEM; have sXM := subset_trans sXP sPM.
have pX := pgroupS sXP pP; have ltXG := mFT_pgroup_proper pX.
have t13p: (p \in \tau1(M)) || (p \in \tau3(M)).
  rewrite (tau1E maxM hallE) (tau3E maxM hallE) -p_rank_gt0 -(rank_Sylow sylP).
  rewrite eqn_leq rank_gt0 (subG1_contra sXP) //= andbT -andb_orl orNb.
  by rewrite -abelian_rank1_cyclic ?cyclic_abelian.
have [H maxNH] := mmax_exists (mFT_norm_proper ntX ltXG).
have [cMsX _ _] := cent_norm_tau13_mmax t13p sXM pX maxNH.
have [_ sNH] := setIdP maxNH.
apply/eqP; rewrite eqEsubset andbC setIS ?centS // subsetI subsetIl /= centsC.
apply: subset_trans (cMsX P _ pP) (centS _).
  rewrite subsetI sPM (subset_trans (cents_norm _) sNH) //.
  by rewrite sub_abelian_cent // cyclic_abelian.
by rewrite setIS // (subset_trans (cent_sub _) sNH).
Qed.

(* This is B & G, Corollary 13.3(b). *)
Corollary tau3_primact_Msigma E3 :
  \tau3(M).-Hall(E) E3 -> semiprime M`_\sigma E3.
Proof.
move=> hallE3 x /setD1P[]; rewrite -cycle_eq1 -cycle_subG => ntX sXE3.
have [sE3E t3E3 _] := and3P hallE3; rewrite -cent_cycle.
have [[E1 hallE1] _] := ex_tau13_compl hallE.
have [E2 _ complEi] := ex_tau2_compl hallE hallE1 hallE3.
have [[sE3E' nsE3E] _ [_ cycE3] _ _] := sigma_compl_context maxM complEi.
apply/eqP; rewrite eqEsubset andbC setIS ?centS // subsetI subsetIl /= centsC.
pose p := pdiv #[x]; have p_pr: prime p by rewrite pdiv_prime ?cardG_gt1.
have t3p: p \in \tau3(M) by rewrite (pgroupP (pgroupS sXE3 t3E3)) ?pdiv_dvd.
have t13p: [|| p \in \tau1(M) | p \in \tau3(M)] by rewrite t3p orbT.
have [y Xy oy]:= Cauchy p_pr (pdiv_dvd _).
have ntY: <[y]> != 1 by rewrite -cardG_gt1 -orderE oy prime_gt1.
have pY: p.-group <[y]> by rewrite /pgroup -orderE oy pnat_id.
have [H maxNH] := mmax_exists (mFT_norm_proper ntY (mFT_pgroup_proper pY)).
have sYE3: <[y]> \subset E3 by rewrite cycle_subG (subsetP sXE3).
have sYE := subset_trans sYE3 sE3E; have sYM := subset_trans sYE sEM.
have [_ cMsY _] := cent_norm_tau13_mmax t13p sYM pY maxNH.
have [_ sNH] := setIdP maxNH.
have sE3H': E3 \subset H^`(1).
  rewrite (subset_trans sE3E') ?dergS // (subset_trans _ sNH) ?normal_norm //.
  by rewrite (char_normal_trans _ nsE3E) // sub_cyclic_char.
apply: subset_trans (cMsY E3 _ _) (centS _).
- rewrite subsetI sE3E (subset_trans (cents_norm _) sNH) //.
  by rewrite sub_abelian_cent ?cyclic_abelian.
- rewrite (pgroupS sE3H') //; apply/pgroupP=> q _ q_dv_H'.
  by rewrite !inE q_dv_H' !andbF.
by rewrite setIS // (subset_trans _ sNH) // cents_norm ?centS ?cycle_subG.
Qed.

(* This is B & G, Theorem 13.4. *)
(* Note how the non-structural steps in the proof (top of p. 99, where it is  *)
(* deduced that C_M_alpha(P) <= C_M_alpha(R) from q \notin \alpha, and then   *)
(* C_M_alpha(P) = C_M_alpha(R) from r \in tau_1(M) !!), are handled cleanly   *)
(* on lines 5-12 of the proof by a conditional expression for the former, and *)
(* a without loss tactic for the latter.                                      *)
(*   Also note that the references to 10.12 and 12.2 are garbled (some are    *)
(* missing, and some are exchanged!).                                         *)
Theorem cent_tau1Elem_Msigma p r P R (Ms := M`_\sigma) :
    p \in \tau1(M) -> P \in 'E_p^1(E) -> R \in 'E_r^1('C_E(P)) ->
  'C_Ms(P) \subset 'C_Ms(R).
Proof.
have /andP[sMsM nMsM]: Ms <| M := pcore_normal _ M.
have coMsE: coprime #|Ms| #|E| := coprime_sigma_compl hallE.
pose Ma := M`_\alpha; have sMaMs: Ma \subset Ms := Malpha_sub_Msigma maxM.
rewrite pnElemI -setIdE => t1Mp EpP /setIdP[ErR cPR].
without loss symPR: p r P R EpP ErR cPR t1Mp /
  r \in \tau1(M) -> 'C_Ma(P) \subset 'C_Ma(R) -> 'C_Ma(P) = 'C_Ma(R).
- move=> IH; apply: (IH p r) => // t1Mr sCaPR; apply/eqP; rewrite eqEsubset.
  rewrite sCaPR -(setIidPl sMaMs) -!setIA setIS ?(IH r p) 1?centsC // => _.
  by case/eqVproper; rewrite // /proper sCaPR andbF.
do [rewrite !subsetI !subsetIl /=; set cRCaP := _ \subset _] in symPR *.
pose Mz := 'O_(if cRCaP then \sigma(M) else \alpha(M))(M); pose C := 'C_Mz(P). 
suffices: C \subset 'C(R) by rewrite /C /Mz /cRCaP; case: ifP => // ->.
have sMzMs: Mz \subset Ms by rewrite /Mz; case: ifP => // _.
have sCMs: C \subset Ms by rewrite subIset ?sMzMs.
have [[sPE abelP dimP] [sRE abelR dimR]] := (pnElemP EpP, pnElemP ErR).
have [sPM sRM] := (subset_trans sPE sEM, subset_trans sRE sEM).
have [[pP cPP _] [rR _]] := (and3P abelP, andP abelR).
have coCR: coprime #|C| #|R| := coprimeSg sCMs (coprimegS sRE coMsE).
have ntP: P :!=: 1 by exact: nt_pnElem EpP _.
pose ST := [set S | Sylow C (gval S) & R \subset 'N(S)].
have sST_CP S: S \in ST -> S \subset C by case/setIdP=> /SylowP[q _ /andP[]].
rewrite -{sST_CP}[C](Sylow_transversal_gen sST_CP)  => [|q _]; last first.
  have nMzR: R \subset 'N(Mz) by rewrite (subset_trans sRM) // gFnorm.
  have{nMzR} nCR: R \subset 'N(C) by rewrite normsI // norms_cent // cents_norm.
  have solC := solvableS (subset_trans sCMs sMsM) (mmax_sol maxM).
  have [S sylS nSR] := coprime_Hall_exists q nCR coCR solC.
  by exists S; rewrite // inE (p_Sylow sylS) nSR.
rewrite gen_subG; apply/bigcupsP=> S /setIdP[/SylowP[q _ sylS] nSR] {ST}.
have [sSC qS _] := and3P sylS.
have [sSMs [sSMz cPS]] := (subset_trans sSC sCMs, subsetIP sSC).
rewrite (sameP commG1P eqP) /=; set Q := [~: S, R]; apply/idPn => ntQ.
have sQS: Q \subset S by [rewrite commg_subl]; have qQ := pgroupS sQS qS.
have piQq: q \in \pi(Q) by rewrite -p_rank_gt0 -(rank_pgroup qQ) rank_gt0.
have{piQq} [nQR piSq] := (commg_normr R S : R \subset 'N(Q), piSg sQS piQq).
have [H maxNH] := mmax_exists (mFT_norm_proper ntP (mFT_pgroup_proper pP)).
have [maxH sNH] := setIdP maxNH; have sCPH := subset_trans (cent_sub _) sNH.
have [sPH sRH] := (subset_trans cPP sCPH, subset_trans cPR sCPH).
have [sSM sSH] := (subset_trans sSMs sMsM, subset_trans cPS sCPH).
have [sQM sQH] := (subset_trans sQS sSM, subset_trans sQS sSH).
have ntMsH_R: [~: Ms :&: H, R] != 1.
  by rewrite (subG1_contra _ ntQ) ?commSg // subsetI sSMs. 
have sR_EH: R \subset E :&: H by apply/subsetIP.
have ntMsH_MH: [~: Ms :&: H, M :&: H] != 1.
  by rewrite (subG1_contra _ ntMsH_R) ?commgS // (subset_trans sR_EH) ?setSI.
have t13Mp: p \in [predU \tau1(M) & \tau3(M)] by apply/orP; left.
have [_ cMsH_t1H' [//|sHp bHp]] := cent_norm_tau13_mmax t13Mp sPM pP maxNH.
have{cMsH_t1H'} t1Hr: r \in \tau1(H).
  apply: contraR ntMsH_R => t1H'r; rewrite (sameP eqP commG1P) centsC.
  by rewrite cMsH_t1H' // (pi_pgroup rR).
have ntCHaRQ: 'C_(H`_\alpha)(R <*> Q) != 1.
  rewrite centY (subG1_contra _ ntP) ?subsetI //= centsC cPR centsC.
  rewrite (subset_trans sQS cPS) (subset_trans _ (Mbeta_sub_Malpha H)) //.
  by rewrite (sub_Hall_pcore (Mbeta_Hall maxH)) // (pi_pgroup pP) ?bHp.
have not_MGH: gval H \notin M :^: G.
  by apply: contraL sHp => /imsetP[x _ ->]; rewrite sigmaJ; case/andP: t1Mp.
have neqHM: H :!=: M := contra_orbit _ _ not_MGH.
have cSS: abelian S.
  apply: contraR neqHM => /(nonabelian_Uniqueness qS)uniqS.
  by rewrite (eq_uniq_mmax (def_uniq_mmax uniqS maxM sSM) maxH sSH).
have tiQcR: 'C_Q(R) = 1 by rewrite coprime_abel_cent_TI // (coprimeSg sSC).
have sMq: q \in \sigma(M) := pnatPpi (pcore_pgroup _ M) (piSg sSMs piSq).
have aH'q: q \notin \alpha(H).
  have [|_ tiHaMs _] := sigma_disjoint maxH maxM; first by rewrite orbit_sym.
  by apply: contraFN (tiHaMs q) => aHq; apply/andP.
have piRr: r \in \pi(R) by rewrite -p_rank_gt0 p_rank_abelem ?dimR.
have ErH_R: R \in 'E_r^1(H) by rewrite !inE sRH abelR dimR.
have{piRr} sM'r: r \in \sigma(M)^' := pnatPpi (pgroupS sRE sM'E) piRr.
have r'q: q \in r^' by apply: contraTneq sMq => ->.
have ntHa: H`_\alpha != 1 by rewrite (subG1_contra _ ntCHaRQ) ?subsetIl.
have uniqNQ: 'M('N(Q)) = [set H].
  apply: contraNeq ntCHaRQ; rewrite joingC.
  by case/(cent_Malpha_reg_tau1 _ _ r'q ErH_R) => //; case=> //= _ -> _.
have maxNQ_H: H \in 'M('N(Q)) :\ M by rewrite uniqNQ !inE neqHM /=. 
have{maxNQ_H} [_ _] := sigma_subgroup_embedding maxM sMq sQM qQ ntQ maxNQ_H.
have [sHq [_ st1HM [_ ntMa]] | _ [_ _ sM'MH]] := ifP; last first.
  have piPp: p \in \pi(P) by rewrite -p_rank_gt0 p_rank_abelem ?dimP.
  have sPMH: P \subset M :&: H by apply/subsetIP.
  by have/negP[] := pnatPpi (pgroupS sPMH (pHall_pgroup sM'MH)) piPp.
have{st1HM} t1Mr: r \in \tau1(M).
  by case/orP: (st1HM r t1Hr); rewrite //= (contraNF ((alpha_sub_sigma _) r)).
have aM'q: q \notin \alpha(M).
  have [_ tiMaHs _] := sigma_disjoint maxM maxH not_MGH.
  by apply: contraFN (tiMaHs q) => aMq; apply/andP.
have ErM_R: R \in 'E_r^1(M) by rewrite !inE sRM abelR dimR.
have: 'M('N(Q)) != [set M] by rewrite uniqNQ (inj_eq (@set1_inj _)).
case/(cent_Malpha_reg_tau1 _ _ r'q ErM_R) => //.
case=> //= ntCMaP tiCMaPQ _; case/negP: ntCMaP.
rewrite -subG1 -{}tiCMaPQ centY setICA subsetIidr /= -/Ma -/Q centsC.
apply/commG1P/three_subgroup; apply/commG1P.
  by rewrite commGC (commG1P _) ?sub1G ?subsetIr.
apply: subset_trans (subsetIr Ma _); rewrite /= -symPR //.
  rewrite commg_subl normsI //; last by rewrite norms_cent // cents_norm.
  by rewrite (subset_trans sSM) ?gFnorm.
apply: contraR aM'q => not_cRCaP; apply: pnatPpi (pgroupS sSMz _) piSq.
by rewrite (negPf not_cRCaP) pcore_pgroup.
Qed.

(* This is B & G, Theorem 13.5. *)
Theorem tau1_primact_Msigma E1 : \tau1(M).-Hall(E) E1 -> semiprime M`_\sigma E1.
Proof.
move=> hallE1 x /setD1P[]; rewrite -cycle_eq1 -cycle_subG => ntX sXE1.
rewrite -cent_cycle; have [sE1E t1E1 _] := and3P hallE1.
have [_ [E3 hallE3]] := ex_tau13_compl hallE.
have{hallE3} [E2 _ complEi] := ex_tau2_compl hallE hallE1 hallE3.
have [_ _ [cycE1 _] _ _ {E2 E3 complEi}] := sigma_compl_context maxM complEi.
apply/eqP; rewrite eqEsubset andbC setIS ?centS //= subsetI subsetIl /=.
have [p _ rX] := rank_witness <[x]>; rewrite -rank_gt0 {}rX in ntX.
have t1p: p \in \tau1(M) by rewrite (pnatPpi t1E1) // (piSg sXE1) -?p_rank_gt0.
have{ntX} [P EpP] := p_rank_geP ntX; have{EpP} [sPX abelP dimP] := pnElemP EpP.
have{sXE1} sPE1 := subset_trans sPX sXE1.
have{dimP} EpP: P \in 'E_p^1(E) by rewrite !inE abelP dimP (subset_trans sPE1).
apply: {x sPX abelP} subset_trans (setIS _ (centS sPX)) _; rewrite centsC.
rewrite -(Sylow_gen E1) gen_subG; apply/bigcupsP=> S; case/SylowP=> r _ sylS.
have [[sSE1 rS _] [-> | ntS]] := (and3P sylS, eqsVneq S 1); first exact: sub1G.
have [cycS sSE] := (cyclicS sSE1 cycE1, subset_trans sSE1 sE1E).
have /p_rank_geP[R ErR]: 0 < 'r_r(S) by rewrite -rank_pgroup ?rank_gt0.
have{ErR} [sRS abelR dimR] := pnElemP ErR; have sRE1 := subset_trans sRS sSE1.
have{abelR dimR} ErR: R \in 'E_r^1('C_E(P)).
  rewrite !inE abelR dimR (subset_trans sRE1) // subsetI sE1E.
  by rewrite sub_abelian_cent ?cyclic_abelian.
rewrite centsC (subset_trans (cent_tau1Elem_Msigma t1p EpP ErR)) //.
have [y defR]: exists y, R :=: <[y]> by apply/cyclicP; exact: cyclicS cycS.
have sylS_E: r.-Sylow(E) S.
  apply: subHall_Sylow hallE1 (pnatPpi t1E1 _) (sylS).
  by rewrite -p_rank_gt0 -(rank_Sylow sylS) rank_gt0.
rewrite defR cent_cycle (cyclic_primact_Msigma sylS_E cycS) ?subsetIr //.
by rewrite !inE -cycle_subG -cycle_eq1 -defR (nt_pnElem ErR).
Qed.

(* This is B & G, Lemma 13.6. *)
(* The wording at the top of the proof is misleading: it should say: by       *)
(* Corollary 12.14, it suffices to show that we can't have both q \in beta(M) *)
(* and X \notsubset M_sigma^(1). Also, the reference to 12.13 should be 12.19 *)
(* or 10.9 (we've used 12.19 here).                                           *)
Lemma cent_cent_Msigma_tau1_uniq E1 P q X (Ms := M`_\sigma) :
    \tau1(M).-Hall(E) E1 -> P \subset E1 -> P :!=: 1 ->
     X \in 'E_q^1('C_Ms(P)) ->
 'M('C(X)) = [set M] /\ (forall S, q.-Sylow(Ms) S -> 'M(S) = [set M]).
Proof.
move=> hallE1 sPE1 ntP EqX; have [sE1E t1E1 _] := and3P hallE1.
rewrite (cent_semiprime (tau1_primact_Msigma hallE1)) //= -/Ms in EqX.
have{P ntP sPE1} ntE1 := subG1_contra sPE1 ntP.
have /andP[sMsM nMsM]: Ms <| M := pcore_normal _ M.
have coMsE: coprime #|Ms| #|E| := coprime_sigma_compl hallE.
have [solMs nMsE] := (solvableS sMsM (mmax_sol maxM), subset_trans sEM nMsM).
apply: cent_der_sigma_uniq => //.
  by move: EqX; rewrite -(setIidPr sMsM) -setIA pnElemI => /setIP[].
have{EqX} [[sXcMsE1 abelX _] ntX] := (pnElemP EqX, nt_pnElem EqX isT).
apply: contraR ntX => /norP[b'q not_sXMs']; rewrite -subG1.
have [S sylS nSE] := coprime_Hall_exists q nMsE coMsE solMs.
have{abelX} [[sSMs qS _] [qX _]] := (and3P sylS, andP abelX).
have sScMsE': S \subset 'C_Ms(E^`(1)).
  have [H hallH cHE'] := der_compl_cent_beta' maxM hallE.
  have [Q sylQ] := Sylow_exists q H; have [sQH qQ _] := and3P sylQ.
  have{cHE' sQH} cQE' := centsS sQH cHE'; have sE'E := der_sub 1 E.
  have [nMsE' coMsE'] := (coprimegS sE'E coMsE, subset_trans sE'E nMsE).
  have{H hallH sylQ} sylQ := subHall_Sylow hallH b'q sylQ.
  have nSE' := subset_trans sE'E nSE; have nQE' := cents_norm cQE'.
  have [x cE'x ->] := coprime_Hall_trans coMsE' nMsE' solMs sylS nSE' sylQ nQE'.
  by rewrite conj_subG // subsetI (pHall_sub sylQ) centsC.
without loss{qX} sXS: X sXcMsE1 not_sXMs' / X \subset S.
  have [nMsE1 coMsE1 IH] := (subset_trans sE1E nMsE, coprimegS sE1E coMsE).
  have [nSE1 [sXMs cE1X]] := (subset_trans sE1E nSE, subsetIP sXcMsE1).
  have [|Q [sylQ nQE1 sXQ]] := coprime_Hall_subset nMsE1 coMsE1 solMs sXMs qX.
    by rewrite cents_norm // centsC.
  have [//|x cE1x defS] := coprime_Hall_trans nMsE1 _ solMs sylS nSE1 sylQ nQE1.
  have Ms_x: x \in Ms by case/setIP: cE1x.
  rewrite -(conjs1g x^-1) -sub_conjg IH //; last by rewrite defS conjSg.
    by rewrite -(conjGid cE1x) conjSg.
  by rewrite -(normsP (der_norm 1 _) x) ?conjSg.
have [sXMs cE1X] := subsetIP sXcMsE1.
have [_ [E3 hallE3]] := ex_tau13_compl hallE.
have{hallE3} [E2 hallE2 complEi] := ex_tau2_compl hallE hallE1 hallE3.
have{not_sXMs' E3 complEi} ntE2: E2 :!=: 1.
  apply: contraNneq not_sXMs' => E2_1.
  have [[sE3E' _] _ _ [defE _] _] := sigma_compl_context maxM complEi.
  have [sCMsE_Ms' _ _] := sigma_compl_embedding maxM hallE.
  have{defE} [_ defE _ _] := sdprodP defE; rewrite E2_1 sdprod1g in defE.
  rewrite (subset_trans _ sCMsE_Ms') // -defE centM setIA subsetI.
  by rewrite (subset_trans (subset_trans sXS sScMsE')) ?setIS ?centS.
have{ntE2 E2 hallE2} [p p_pr t2p]: exists2 p, prime p & p \in \tau2(M).
  have [[p p_pr rE2] [_ t2E2 _]] := (rank_witness E2, and3P hallE2).
  by exists p; rewrite ?(pnatPpi t2E2) // -p_rank_gt0 -rE2 rank_gt0.
have [A Ep2A Ep2A_M] := ex_tau2Elem hallE t2p.
have [_ _ tiCMsA _ _] := tau2_context maxM t2p Ep2A_M.
have [[nsAE _] _ _ _] := tau2_compl_context maxM hallE t2p Ep2A.
have [sAE abelA _] := pnElemP Ep2A; have [pA cAA _] := and3P abelA.
have cCAE1_X: X \subset 'C('C_A(E1)).
  rewrite centsC; apply/subsetP=> y; case/setIP=> Ay cE1y.
  have [-> | nty] := eqVneq y 1; first exact: group1.
  have oY: #[y] = p := abelem_order_p abelA Ay nty.
  have [r _ rE1] := rank_witness E1.
  have{rE1} rE1: 'r_r(E1) > 0 by rewrite -rE1 rank_gt0.
  have [R ErR] := p_rank_geP rE1; have{ErR} [sRE1 abelR dimR] := pnElemP ErR.
  have t1r: r \in \tau1(M) by rewrite (pnatPpi t1E1) -?p_rank_gt0.
  have ErR: R \in 'E_r^1(E) by rewrite !inE abelR dimR (subset_trans sRE1).
  have EpY: <[y]>%G \in 'E_p^1('C_E(R)).
    rewrite p1ElemE // !inE -oY eqxx subsetI (centsS sRE1) cycle_subG //=.
    by rewrite (subsetP sAE).
  rewrite -sub_cent1 -cent_cycle (subset_trans sXcMsE1) //.
  apply: subset_trans (setIS _ (centS sRE1)) _.
  rewrite -subsetIidl setIAC subsetI subsetIr andbT.
  exact: cent_tau1Elem_Msigma t1r ErR EpY.
have nAE1 := subset_trans sE1E (normal_norm nsAE).
have coAE1: coprime #|A| #|E1|.
  by apply: pnat_coprime pA (pi_p'group t1E1 (contraL _ t2p)); apply: tau2'1.
rewrite -tiCMsA -(coprime_cent_prod nAE1 coAE1) ?abelian_sol // centM setIA.
rewrite subsetI cCAE1_X (subset_trans (subset_trans sXS sScMsE')) ?setIS //.
by rewrite centS ?commgSS.
Qed.

End OneComplement.

(* This is B & G, Lemma 13.7. *)
(* We've had to plug a gap in this proof: on p. 100, l. 6-7 it is asserted    *)
(* the conclusion (E1 * E3 acts in a prime manner on M_sigma) follows from    *)
(* the fact that E1 and E3 have coprime orders and act in a prime manner with *)
(* the same set of fixed points. This seems to imply the following argument:  *)
(*   For any x \in M_sigma,                                                   *)
(*       C_(E1 * E3)[x] = C_E1[x] * C_E3[x] is either E1 * E3 or 1,           *)
(*   i.e., E1 * E3 acts in a prime manner on M_sigma.                         *)
(* This is improper because the distributivity of centralisers over coprime   *)
(* products only hold under normality conditions that do not hold in this     *)
(* instance. The correct argument, which involves using the prime action      *)
(* assumption a second time, only relies on the fact that E1 and E3 are Hall  *)
(* subgroups of the group E1 * E3. The fact that E3 <| E (Lemma 12.1(a)),     *)
(* implicitly needed to justify that E1 * E3 is a group, can also be used to  *)
(* simplify the argument, and we do so.                                       *)
Lemma tau13_primact_Msigma M E E1 E2 E3 :
    M \in 'M -> sigma_complement M E E1 E2 E3 -> ~ semiregular E3 E1 ->
  semiprime M`_\sigma (E3 <*> E1).
Proof.
move=> maxM complEi not_regE13; set Ms := M`_\sigma.
have [hallE hallE1 hallE2 hallE3 _] := complEi.
have [[sE1E t1E1 _] [sE3E t3E3 _]] := (and3P hallE1, and3P hallE3).
have [[sEM _ _] [_ t2E2 _]] := (and3P hallE, and3P hallE2).
have [[_ nsE3E] _ [_ cycE3] [defE _] tiE3cE]:= sigma_compl_context maxM complEi.
have [[_ nE3E] [sMsM nMsM]] := (andP nsE3E, andP (pcore_normal _ M : Ms <| M)).
have [P]: exists2 P, P \in 'E^1(E1) & 'C_E3(P) != 1.
  apply/exists_inP; rewrite -negb_forall_in; apply/forall_inP=> regE13.
  apply: not_regE13 => x /setD1P[]; rewrite -cycle_subG -cycle_eq1 -rank_gt0.
  case/rank_geP=> P E1xP sXE1; apply/trivgP; move: E1xP.
  rewrite /= -(setIidPr sXE1) nElemI -setIdE => /setIdP[E1_P sPX].
  by rewrite -(eqP (regE13 P E1_P)) -cent_cycle setIS ?centS.
rewrite -{1}(setIidPr sE1E) nElemI -setIdE => /setIdP[/nElemP[p EpP] sPE1].
rewrite -{1}(setIidPl sE3E) -setIA setIC -rank_gt0 => /rank_geP[R].
rewrite nElemI -setIdE => /setIdP[/nElemP[r ErR] sRE3].
have t1p: p \in \tau1(M).
  rewrite (pnatPpi (pgroupS sPE1 t1E1)) //= (card_p1Elem EpP).
  by rewrite pi_of_prime ?inE ?(pnElem_prime EpP) //.
have prE1 := tau1_primact_Msigma maxM hallE hallE1.
have prE3 := tau3_primact_Msigma maxM hallE hallE3.
have sCsPR: 'C_Ms(P) \subset 'C_Ms(R) by apply: cent_tau1Elem_Msigma EpP ErR.
have [eqCsPR | ltCsPR] := eqVproper sCsPR.
  move=> x; case/setD1P; rewrite -cycle_eq1 -cycle_subG => ntX sXE31.
  apply/eqP; rewrite -cent_cycle eqEsubset andbC setIS ?centS //=.
  have eqCsE13: 'C_Ms(E1) = 'C_Ms(E3).
    rewrite -(cent_semiprime prE1 sPE1) ?(nt_pnElem EpP) //.
    by rewrite -(cent_semiprime prE3 sRE3) ?(nt_pnElem ErR).
  rewrite centY setICA eqCsE13 -setICA setIid.
  have sE31E: E3 <*> E1 \subset E by apply/joing_subP.
  have nE3E1 := subset_trans sE1E nE3E.
  pose y := x.`_\tau1(M); have sYX: <[y]> \subset <[x]> := cycleX x _.
  have sXE := subset_trans sXE31 sE31E; have sYE := subset_trans sYX sXE.
  have [t1'x | not_t1'x] := boolP (\tau1(M)^'.-elt x).
    rewrite (cent_semiprime prE3 _ ntX) // (sub_normal_Hall hallE3) //.
    apply: pnat_dvd t3E3; rewrite -(Gauss_dvdr _ (p'nat_coprime t1'x t1E1)).
    by rewrite mulnC (dvdn_trans _ (dvdn_cardMg _ _)) -?norm_joinEr ?cardSg.
  have{not_t1'x} ntY: #[y] != 1%N by rewrite order_constt partn_eq1.
  apply: subset_trans (setIS _ (centS sYX)) _.
  have [solE nMsE] := (sigma_compl_sol hallE, subset_trans sEM nMsM).
  have [u Eu sYuE1] := Hall_Jsub solE hallE1 sYE (p_elt_constt _ _).
  rewrite -(conjSg _ _ u) !conjIg -!centJ (normsP nMsE) ?(normsP nE3E) //=.
  by rewrite -eqCsE13 (cent_semiprime prE1 sYuE1) // trivg_card1 cardJg.
have ntCsR: 'C_Ms(R) != 1.
  by rewrite -proper1G (sub_proper_trans _ ltCsPR) ?sub1G.
have ntR: R :!=: 1 by rewrite (nt_pnElem ErR).
have [cEPR abelR dimR] := pnElemP ErR; have [rR _ _] := and3P abelR.
have{cEPR} [sRE cPR] := subsetIP cEPR; have sRM := subset_trans sRE sEM.
have E2_1: E2 :=: 1.
  have [x defR] := cyclicP (cyclicS sRE3 cycE3).
  apply: contraNeq ntCsR; rewrite -rank_gt0; have [q _ ->] := rank_witness E2.
  rewrite p_rank_gt0 defR cent_cycle. move/(pnatPpi t2E2) => t2q.
  have [A Eq2A _] := ex_tau2Elem hallE t2q.
  have [-> //] := tau2_regular maxM complEi t2q Eq2A.
  by rewrite !inE -cycle_subG -cycle_eq1 -defR sRE3 (nt_pnElem ErR).
have nRE: E \subset 'N(R) by rewrite (char_norm_trans _ nE3E) ?sub_cyclic_char.
have [H maxNH] := mmax_exists (mFT_norm_proper ntR (mFT_pgroup_proper rR)).
have [maxH sNH] := setIdP maxNH; have sEH := subset_trans nRE sNH.
have ntCsR_P: [~: 'C_Ms(R), P] != 1.
  rewrite (sameP eqP commG1P); apply: contra (proper_subn ltCsPR).
  by rewrite subsetI subsetIl.
have sCsR_MsH: 'C_Ms(R) \subset Ms :&: H.
  exact: setIS Ms (subset_trans (cent_sub R) sNH).
have ntMsH_P: [~: Ms :&: H, P] != 1 by rewrite (subG1_contra _ ntCsR_P) ?commSg.
have tiE1cMsH: 'C_E1(Ms :&: H) = 1.
  apply: contraNeq (proper_subn ltCsPR) => ntCE1MsH.
  rewrite (cent_semiprime prE1 sPE1) ?(nt_pnElem EpP) //.
  rewrite -(cent_semiprime prE1 (subsetIl _ _) ntCE1MsH) /=.
  by rewrite subsetI subsetIl centsC subIset // orbC centS.
have t3r: r \in \tau3(M).
  by rewrite (pnatPpi t3E3) ?(piSg sRE3) // -p_rank_gt0 p_rank_abelem ?dimR.
have t13r: (r \in \tau1(M)) || (r \in \tau3(M)) by rewrite t3r orbT.
have [sE1H sRH] := (subset_trans sE1E sEH, subset_trans sRE sEH).
have [_ ct1H'R [|sHr _]] := cent_norm_tau13_mmax maxM hallE t13r sRM rR maxNH.
  rewrite (subG1_contra _ ntMsH_P) // commgS // (subset_trans sPE1) //.
  by rewrite subsetI (subset_trans sE1E).
have t1H_E1: \tau1(H).-group E1.
  apply/pgroupP=> q q_pr /Cauchy[] // x E1x ox.
  apply: contraLR (prime_gt1 q_pr) => t1H'q; rewrite -ox cardG_gt1 negbK.
  rewrite -subG1 -tiE1cMsH subsetI cycle_subG E1x /= ct1H'R //.
    by rewrite (setIidPl sEH) cycle_subG (subsetP sE1E).
  by rewrite /pgroup -orderE ox pnatE.
have sH'_E1: \sigma(H)^'.-group E1 by apply: sub_pgroup t1H_E1 => q /andP[].
have [F hallF sE1F] := Hall_superset (mmax_sol maxH) sE1H sH'_E1.
have [F1 hallF1 sE1F1] := Hall_superset (sigma_compl_sol hallF) sE1F t1H_E1.
have{sHr} sRHs: R \subset H`_\sigma.
  by rewrite (sub_Hall_pcore (Msigma_Hall maxH)) ?(pi_pgroup rR).
have cRE1: E1 \subset 'C(R).
  rewrite centsC (centsS sE1F1) // -subsetIidl subsetI subxx -sRHs -subsetI.
  have prF1 := tau1_primact_Msigma maxH hallF hallF1.
  rewrite -(cent_semiprime prF1 (subset_trans sPE1 sE1F1)); last first.
    exact: nt_pnElem EpP _.
  by rewrite subsetI sRHs.
case/negP: ntR; rewrite -subG1 -tiE3cE subsetI sRE3 centsC -(sdprodW defE).
by rewrite E2_1 sdprod1g mul_subG // sub_abelian_cent ?cyclic_abelian.
Qed.

(* This is B & G, Lemma 13.8. *)
(* We had to plug a significant hole in the proof text: in the sixth          *)
(* paragraph of the proof, it is asserted that because M = N_M(Q)M_alpha and  *)
(* r is in pi(C_M(P)), P centralises some non-trivial r-subgroup of N_M(Q).   *)
(* This does not seem to follow directly, even taking into account that r is  *)
(* not in alpha(M): while it is true that N_M(Q) contains a Sylow r-subgroup  *)
(* of M, this subgroup does not need to contain an r-group centralized by P.  *)
(* We can only establish the required result by making use of the fact that M *)
(* has a normal p-complement K (because p is in tau_1(M)), as then N_K(Q)     *)
(* will contain a p-invariant Sylow r-subgroup S of K and M (coprime action)  *)
(* and then any r-subgroup of M centralised by P will be in K, and hence      *)
(* conjugate in C_K(P) to a subgroup of S (coprime action again).             *)
Lemma tau1_mmaxI_asymmetry M Mstar p P q Q q_star Qstar :
  (*1*) [/\ M \in 'M, Mstar \in 'M & gval Mstar \notin M :^: G] ->
  (*2*) [/\ p \in \tau1(M), p \in \tau1(Mstar) & P \in 'E_p^1(M :&: Mstar)] ->
  (*3*) [/\ q.-Sylow(M :&: Mstar) Q, q_star.-Sylow(M :&: Mstar) Qstar,
            P \subset 'N(Q) & P \subset 'N(Qstar)] ->
  (*4*) 'C_Q(P) = 1 /\ 'C_Qstar(P) = 1 ->
  (*5*) 'N(Q) \subset Mstar /\ 'N(Qstar) \subset M ->
  False.
Proof.
move: Mstar q_star Qstar => L u U. (* Abbreviate Mstar by L, Qstar by U. *)
move=> [maxM maxL notMGL] [t1Mp t1Lp EpP] [sylQ sylU nQP nUP].
move=> [regPQ regPU] [sNQL sNUM]; rewrite setIC in sylU. (* for symmetry *)
have notLGM: gval M \notin L :^: G by rewrite orbit_sym. (* for symmetry *)
have{EpP} [ntP [sPML abelP dimP]] := (nt_pnElem EpP isT, pnElemP EpP).
have{sPML} [[sPM sPL] [pP _ _]] := (subsetIP sPML, and3P abelP). 
have solCP: solvable 'C(P) by rewrite mFT_sol ?mFT_cent_proper.
pose Qprops M q Q := [&& q.-Sylow(M) Q, q != p, q \notin \beta(M),
                          'C_(M`_\beta)(P) != 1 & 'C_(M`_\beta)(P <*> Q) == 1].
have{sylQ sylU} [hypQ hypU]: Qprops M q Q /\ Qprops L u U.
  apply/andP; apply/nandP=> not_hypQ.
  without loss{not_hypQ}: L u U M q Q maxM maxL notMGL notLGM t1Mp t1Lp sPM sPL
                  sylQ sylU nQP nUP regPQ regPU sNQL sNUM / ~~ Qprops M q Q.
  - by move=> IH; case: not_hypQ; [apply: (IH L u U) | apply: (IH M q Q)].
  case/and5P; have [_ qQ _] := and3P sylQ.
  have{sylQ} sylQ: q.-Sylow(M) Q.
    by rewrite -Sylow_subnorm -(setIidPr sNQL) setIA Sylow_subnorm.
  have ntQ: Q :!=: 1.
    by apply: contraTneq sNQL => ->; rewrite norm1 proper_subn ?mmax_proper.
  have p'q: q != p.
    apply: contraNneq ntQ => def_q; rewrite (trivg_center_pgroup qQ) //.
    apply/trivgP; rewrite -regPQ setIS // centS //.
    by rewrite (norm_sub_max_pgroup (Hall_max sylQ)) ?def_q.
  have EpP: P \in 'E_p^1(M) by apply/pnElemP.
  have [|_ [// | abM]] := cent_Malpha_reg_tau1 maxM t1Mp p'q EpP ntQ nQP regPQ.
    apply: contraNneq notMGL => uniqNQ.
    by rewrite (eq_uniq_mmax uniqNQ) ?orbit_refl.
  by rewrite joingC /alpha_core abM !(eq_pcore _ abM) => _ -> -> ->.
have bML_CMbP: forall M L, [predU \beta(M) & \beta(L)].-group 'C_(M`_\beta)(P).
  move=> ? ?; apply: pgroupS (subsetIl _ _) (sub_pgroup _ (pcore_pgroup _ _)).
  by move=> ?; rewrite !inE => ->.
have [H hallH sCMbP_H] := Hall_superset solCP (subsetIr _ _) (bML_CMbP M L).
have [[s _ rFH] [cPH bH _]] := (rank_witness 'F(H), and3P hallH).
have{sCMbP_H rFH cPH} piFHs: s \in \pi('F(H)).
  rewrite -p_rank_gt0 -rFH rank_gt0 (trivg_Fitting (solvableS cPH solCP)).
  by rewrite (subG1_contra sCMbP_H) //; case/and5P: hypQ.
without loss{bH} bMs: L u U M q Q maxM maxL notMGL notLGM t1Mp t1Lp sPM sPL
               nQP nUP regPQ regPU sNQL sNUM hypQ hypU hallH / s \in \beta(M).
- move=> IH; have:= pnatPpi bH (piSg (Fitting_sub H) piFHs).
  case/orP; [apply: IH hypQ hypU hallH | apply: IH hypU hypQ _] => //.
  by apply: etrans (eq_pHall _ _ _) hallH => ?; apply: orbC.
without loss{bML_CMbP} sCMbP_H: H hallH piFHs / 'C_(M`_\beta)(P) \subset H.
  have [x cPx sCMbP_Hx] := Hall_subJ solCP hallH (subsetIr _ _) (bML_CMbP M L).
  by move=> IH; apply: IH sCMbP_Hx; rewrite ?pHallJ //= FittingJ cardJg.
pose X := 'O_s(H); have sylX := nilpotent_pcore_Hall s (Fitting_nil H).
have{piFHs sylX} ntX: X != 1.
  by rewrite -rank_gt0 /= -p_core_Fitting (rank_Sylow sylX) p_rank_gt0.
have [[cPH bH _] [sXH nXH]] := (and3P hallH, andP (pcore_normal s H : X <| H)).
have [cPX sX] := (subset_trans sXH cPH, pcore_pgroup s H : s.-group X).
have{hypQ} [sylQ p'q bM'q ntCMbP] := and5P hypQ; apply: negP.
apply: subG1_contra (ntX); rewrite /= centY !subsetI (subset_trans _ cPH) //=.
have nsMbM : M`_\beta <| M := pcore_normal _ M; have [sMbM nMbM] := andP nsMbM.
have hallMb := Mbeta_Hall maxM; have [_ bMb _] := and3P hallMb.
have{ntX} sHM: H \subset M.
  have [g sXMg]: exists g, X \subset M :^ g.
    have [S sylS] := Sylow_exists s M`_\beta; have [sSMb _ _] := and3P sylS.
    have sylS_G := subHall_Sylow (Mbeta_Hall_G maxM) bMs sylS.
    have [g _ sXSg] := Sylow_subJ sylS_G (subsetT X) sX.
    by exists g; rewrite (subset_trans sXSg) // conjSg (subset_trans sSMb).
  have [t _ rFC] := rank_witness 'F('C_(M`_\beta)(P)).
  pose Y := 'O_t('C_(M`_\beta)(P)).
  have [sYC tY] := (pcore_sub t _ : Y \subset _, pcore_pgroup t _ : t.-group Y).
  have sYMb := subset_trans sYC (subsetIl _ _); have bMY := pgroupS sYMb bMb.
  have{rFC} ntY: Y != 1.
    rewrite -rank_gt0 /= -p_core_Fitting.
    rewrite (rank_Sylow (nilpotent_pcore_Hall t (Fitting_nil _))) -rFC.
    by rewrite rank_gt0 (trivg_Fitting (solvableS (subsetIr _ _) solCP)).
  have bMt: t \in \beta(M).
    by rewrite (pnatPpi bMY) // -p_rank_gt0 -rank_pgroup ?rank_gt0.
  have sHMg: H \subset M :^ g.
    rewrite (subset_trans nXH) // beta_norm_sub_mmax ?mmaxJ // /psubgroup sXMg.
    by rewrite (pi_pgroup sX) 1?betaJ.
  have sYMg: Y \subset M :^ g := subset_trans (subset_trans sYC sCMbP_H) sHMg.
  have sNY_M: 'N(Y) \subset M.
    by rewrite beta_norm_sub_mmax // /psubgroup (subset_trans sYMb).
  have [_ trCY _] := sigma_group_trans maxM (beta_sub_sigma maxM bMt) tY.
  have [|| h cYh /= defMg] := (atransP2 trCY) M (M :^ g).
  - by rewrite inE orbit_refl (subset_trans (normG _) sNY_M). 
  - by rewrite inE mem_orbit ?in_setT.
  by rewrite defMg conjGid // (subsetP sNY_M) ?(subsetP (cent_sub _)) in sHMg.
have sXMb: X \subset M`_\beta.
  by rewrite (sub_Hall_pcore hallMb) ?(subset_trans sXH sHM) ?(pi_pgroup sX).
rewrite sXMb (sameP commG1P eqP) /= -/X -subG1.
have [sQL [sQM qQ _]] := (subset_trans (normG Q) sNQL, and3P sylQ).
have nsLbL : L`_\beta <| L := pcore_normal _ L; have [sLbL nLbL] := andP nsLbL.
have nLbQ := subset_trans sQL nLbL.
have [<- ti_aLsM _] := sigma_disjoint maxL maxM notLGM.
rewrite subsetI (subset_trans _ (Mbeta_sub_Msigma maxM)) ?andbT; last first.
  by rewrite (subset_trans (commgSS sXMb sQM)) // commg_subl nMbM.
have defQ: [~: Q, P] = Q.
  rewrite -{2}(coprime_cent_prod nQP) ?(pgroup_sol qQ) ?regPQ ?mulg1 //.
  by rewrite (p'nat_coprime (pi_pnat qQ _) pP).
suffices sXL: X \subset L.
  apply: subset_trans (Mbeta_sub_Malpha L).
  rewrite -quotient_sub1 ?comm_subG  ?quotientR ?(subset_trans _ nLbL) //.
  have <-: (M`_\beta :&: L) / L`_\beta :&: 'O_q(L^`(1) / L`_\beta) = 1.
    rewrite coprime_TIg // coprime_morphl // (coprimeSg (subsetIl _ _)) //.
    exact: pnat_coprime (pcore_pgroup _ _) (pi_pnat (pcore_pgroup _ _) _).
  rewrite commg_subI // subsetI.
    rewrite quotientS; last by rewrite subsetI sXMb.
    rewrite (char_norm_trans (pcore_char _ _)) ?quotient_norms //.
    by rewrite (subset_trans sXL) ?der_norm.
  rewrite (sub_Hall_pcore (nilpotent_pcore_Hall _ (Mbeta_quo_nil _))) //.
    rewrite quotient_pgroup ?quotient_norms //.
    by rewrite normsI ?(subset_trans sQM nMbM) ?normsG.
  by rewrite quotientS // -defQ commgSS // (subset_trans nQP).
have{hypU} [r bLr piHr]: exists2 r, r \in \beta(L) & r \in \pi(H).
  have [_ _ _] := and5P hypU; rewrite -rank_gt0.
  have [r _ ->] := rank_witness 'C_(L`_\beta)(P); rewrite p_rank_gt0 => piCr _.
  have [piLb_r piCPr] := (piSg (subsetIl _ _) piCr, piSg (subsetIr _ _) piCr).
  have bLr: r \in \beta(L) := pnatPpi (pcore_pgroup _ L) piLb_r.
  exists r; rewrite //= (card_Hall hallH) pi_of_part // inE /= piCPr.
  by rewrite inE /= bLr orbT.
have sM'r: r \notin \sigma(M).
  by apply: contraFN (ti_aLsM r) => sMr; rewrite inE /= beta_sub_alpha.
have defM: M`_\beta * 'N_M(Q) = M.
  have nMbQ := subset_trans sQM nMbM.
  have nsMbQ_M: M`_\beta <*> Q <| M.
    rewrite -{2}(quotientGK nsMbM) -quotientYK ?cosetpre_normal //.
    rewrite (eq_Hall_pcore (nilpotent_pcore_Hall q (Mbeta_quo_nil _))) //.
      apply: char_normal_trans (pcore_char _ _) (quotient_normal _ _).
      exact: der_normal.
    rewrite quotient_pHall // (pHall_subl _ (der_sub 1 M) sylQ) //.
    by rewrite -defQ commgSS // (subset_trans nUP).
  have sylQ_MbQ := pHall_subl (joing_subr _ Q) (normal_sub nsMbQ_M) sylQ.
  rewrite -{3}(Frattini_arg nsMbQ_M sylQ_MbQ) /= norm_joinEr // -mulgA.
  by congr (_ * _); rewrite mulSGid // subsetI sQM normG.
have [[sM'p _ not_pM'] [sL'p _]] := (and3P t1Mp, andP t1Lp).
have{not_pM'} [R ErR nQR]: exists2 R, R \in 'E_r^1('C_M(P)) & R \subset 'N(Q).
  have p'r: r \in p^' by apply: contraNneq sL'p => <-; apply: beta_sub_sigma.
  have p'M': p^'.-group M^`(1).
    by rewrite p'groupEpi mem_primes (negPf not_pM') !andbF.
  pose K := 'O_p^'(M); have [sKM nKM] := andP (pcore_normal _ M : K <| M).
  have hallK: p^'.-Hall(M) K.
    rewrite -(pquotient_pHall _ (der_normal 1 M)) ?quotient_pgroup //.
      rewrite -pquotient_pcore ?der_normal // nilpotent_pcore_Hall //.
      by rewrite abelian_nil ?der_abelian.
    by rewrite (normalS _ sKM) ?pcore_max ?der_normal.
  have sMbK: M`_\beta \subset K.
    by rewrite (subset_trans (Mbeta_der1 maxM)) // pcore_max ?der_normal.
  have coKP: coprime #|K| #|P| := p'nat_coprime (pcore_pgroup _ M) pP.
  have [solK sNK] := (solvableS sKM (mmax_sol maxM), subsetIl K 'N(Q)).
  have [nKP coNP] := (subset_trans sPM nKM, coprimeSg sNK coKP).
  have nNP: P \subset 'N('N_K(Q)) by rewrite normsI // norms_norm.
  have [S sylS nSP] := coprime_Hall_exists r nNP coNP (solvableS sNK solK).
  have /subsetIP[sSK nQS]: S \subset 'N_K(Q) := pHall_sub sylS.
  have sylS_K: r.-Sylow(K) S.
    rewrite pHallE sSK /= -/K -(setIidPr sKM) -defM -group_modl // setIAC.
    rewrite (setIidPr sKM) -LagrangeMr partnM // -(card_Hall sylS).
    rewrite part_p'nat ?mul1n 1?(pnat_dvd (dvdn_indexg _ _)) //.
    by apply: (pi_p'nat bMb); apply: contra sM'r; exact: beta_sub_sigma.
  have rC: 'r_r('C_M(P)) > 0 by rewrite p_rank_gt0 (piSg _ piHr) // subsetI sHM.
  have{rC} [R ErR] := p_rank_geP rC; have [sRcMP abelR _] := pnElemP ErR.
  have{sRcMP abelR} [[sRM cPR] [rR _]] := (subsetIP sRcMP, andP abelR).
  have nRP: P \subset 'N(R) by rewrite cents_norm 1?centsC.
  have sRK: R \subset K by rewrite sub_Hall_pcore ?(pi_pgroup rR).
  have [T [sylT nTP sRT]] := coprime_Hall_subset nKP coKP solK sRK rR nRP.
  have [x cKPx defS] := coprime_Hall_trans nKP coKP solK sylS_K nSP sylT nTP.
  rewrite -(conjGid (subsetP (setSI _ sKM) x cKPx)).
  by exists (R :^ x)%G; rewrite ?pnElemJ ?(subset_trans _ nQS) // defS conjSg. 
have [sRcMP abelR _] := pnElemP ErR; have ntR := nt_pnElem ErR isT.
have{sRcMP abelR} [[sRM cPR] [rR _]] := (subsetIP sRcMP, andP abelR).
have sNR_L: 'N(R) \subset L.
  by rewrite beta_norm_sub_mmax /psubgroup ?(subset_trans nQR) ?(pi_pgroup rR).
have sPR_M: P <*> R \subset M by rewrite join_subG (subset_trans nUP).
have sM'_PR: \sigma(M)^'.-group (P <*> R).
  by rewrite cent_joinEr // pgroupM (pi_pgroup rR) // (pi_pgroup pP).
have [E hallE sPRE] := Hall_superset (mmax_sol maxM) sPR_M sM'_PR.
have{sPRE} [sPE sRE] := joing_subP sPRE.
have EpP: P \in 'E_p^1(E) by apply/pnElemP.
have{ErR} ErR: R \in 'E_r^1('C_E(P)).
  by rewrite -(setIidPr (pHall_sub hallE)) setIAC pnElemI inE ErR inE.
apply: subset_trans (cents_norm (subset_trans _ (subsetIr M`_\sigma _))) sNR_L.
apply: subset_trans (cent_tau1Elem_Msigma maxM hallE t1Mp EpP ErR).
by rewrite subsetI cPX (subset_trans sXMb) ?Mbeta_sub_Msigma.
Qed.

(* This is B & G, Theorem 13.9. *)
Theorem sigma_partition M Mstar :
    M \in 'M -> Mstar \in 'M -> gval Mstar \notin M :^: G ->
  [predI \sigma(M) & \sigma(Mstar)] =i pred0.
Proof.
move: Mstar => L maxM maxL notMGL q; apply/andP=> [[/= sMq sLq]].
have [E hallE] := ex_sigma_compl maxM; have [sEM sM'E _] := and3P hallE.
have [_ _ nMsE _] := sdprodP (sdprod_sigma maxM hallE).
have coMsE: coprime #|M`_\sigma| #|E| := pnat_coprime (pcore_pgroup _ _) sM'E.
have [|S sylS nSE] := coprime_Hall_exists q nMsE coMsE.
  exact: solvableS (pcore_sub _ _) (mmax_sol maxM).
have [sSMs qS _] := and3P sylS.
have sylS_M := subHall_Sylow (Msigma_Hall maxM) sMq sylS.
have ntS: S :!=: 1.
  by rewrite -rank_gt0 (rank_Sylow sylS_M) p_rank_gt0 sigma_sub_pi.
without loss sylS_L: L maxL sLq notMGL / q.-Sylow(L) S.
  have sylS_G := sigma_Sylow_G maxM sMq sylS_M.
  have [T sylT] := Sylow_exists q L; have sylT_G := sigma_Sylow_G maxL sLq sylT.
  have [x Gx ->] := Sylow_trans sylT_G (sigma_Sylow_G maxM sMq sylS_M).
  case/(_ (L :^ x)%G); rewrite ?mmaxJ ?sigmaJ ?pHallJ2 //.
  by rewrite (orbit_transr _ (mem_orbit 'Js L Gx)).
have [[sSL _] [[E1 hallE1] [E3 hallE3]]] := (andP sylS_L, ex_tau13_compl hallE).
have [E2 hallE2 complEi] := ex_tau2_compl hallE hallE1 hallE3.
have E2_1: E2 :==: 1.
  apply: contraR ntS; rewrite -rank_gt0; have [p _ ->] := rank_witness E2.
  rewrite p_rank_gt0 => /(pnatPpi (pHall_pgroup hallE2))t2p.
  have [A Ep2A _] := ex_tau2Elem hallE t2p.
  have [_ _ _ ti_sM] := tau2_compl_context maxM hallE t2p Ep2A.
  rewrite -subG1; have [<- _] := ti_sM L maxL notMGL; rewrite subsetI sSMs /=.
  by rewrite (sub_Hall_pcore (Msigma_Hall maxL) sSL) (pi_pgroup qS).
have: E1 :!=: 1 by have [_ -> //] := sigma_compl_context maxM complEi.
rewrite -rank_gt0; have [p _ ->] := rank_witness E1; case/p_rank_geP=> P EpP.
have [[sPE1 abelP dimP] [sE1E t1E1 _]] := (pnElemP EpP, and3P hallE1).
have ntP: P :!=: 1 by rewrite (nt_pnElem EpP).
have piPp: p \in \pi(P) by rewrite -p_rank_gt0 ?p_rank_abelem ?dimP.
have t1Mp: p \in \tau1(M) by rewrite (pnatPpi _ (piSg sPE1 _)).
have sPE := subset_trans sPE1 sE1E; have sPM := subset_trans sPE sEM.
have [sNM sNL] := (norm_sigma_Sylow sMq sylS_M, norm_sigma_Sylow sLq sylS_L).
have nSP := subset_trans sPE nSE; have sPL := subset_trans nSP sNL.
have regPS: 'C_S(P) = 1.
  apply: contraNeq (contra_orbit _ _ notMGL); rewrite -rank_gt0.
  rewrite (rank_pgroup (pgroupS _ qS)) ?subsetIl //; case/p_rank_geP=> Q /=.
  rewrite -(setIidPr sSMs) setIAC pnElemI; case/setIdP=> EqQ _.
  have [_ uniqSq] := cent_cent_Msigma_tau1_uniq maxM hallE hallE1 sPE1 ntP EqQ.
  by rewrite (eq_uniq_mmax (uniqSq S sylS) maxL sSL).
have t1Lp: p \in \tau1(L).
  have not_cMsL_P: ~~ (P \subset 'C(M`_\sigma :&: L)).
    apply: contra ntS => cMsL_P; rewrite -subG1 -regPS subsetIidl centsC.
    by rewrite (subset_trans cMsL_P) ?centS // subsetI sSMs.
  apply: contraR (not_cMsL_P) => t1L'p.
  have [piEp piLp] := (piSg sPE piPp, piSg sPL piPp).
  have [] := Msigma_setI_mmax_central maxM hallE maxL piEp piLp t1L'p _ notMGL.
    apply: contraNneq not_cMsL_P; move/commG1P; rewrite centsC.
    by apply: subset_trans; rewrite subsetI sPM.
  by move->; rewrite ?(abelem_pgroup abelP) // subsetI sPM.
case: (@tau1_mmaxI_asymmetry M L p P q S q S) => //.
  by rewrite !inE subsetI sPM sPL abelP dimP.
by rewrite (pHall_subl _ (subsetIl M L) sylS_M) // subsetI (pHall_sub sylS_M).
Qed.

(* This is B & G, Theorem 13.10. *)
Theorem tau13_regular M E E1 E2 E3 p P :
    M \in 'M -> sigma_complement M E E1 E2 E3 ->
    P \in 'E_p^1(E1) -> ~~ (P \subset 'C(E3)) ->
  [/\ (*a*) semiregular E3 E1,
      (*b*) semiregular M`_\sigma E3
    & (*c*) 'C_(M`_\sigma)(P) != 1].
Proof.
move=> maxM complEi EpP not_cE3P.
have nsMsM: M`_\sigma <| M := pcore_normal _ M; have [sMsM nMsM] := andP nsMsM.
have [hallMs sMaMs] := (Msigma_Hall maxM, Malpha_sub_Msigma maxM).
have [[sE3E' nsE3E] _ [_ cycE3] _ _] := sigma_compl_context maxM complEi.
have [hallE hallE1 _ hallE3] := complEi.
have [[_ sM_Ms _] [sEM sM'E _]] := (and3P hallMs, and3P hallE).
have [[sE1E t1E1 _] [sE3E t3E3 _] _] := (and3P hallE1, and3P hallE3).
have [sPE1 abelP dimP] := pnElemP EpP; have [pP _ _] := and3P abelP.
have [ntP t1MP] := (nt_pnElem EpP isT, pgroupS sPE1 t1E1).
have sPE := subset_trans sPE1 sE1E; have sPM := subset_trans sPE sEM.
have piPp: p \in \pi(P) by rewrite -p_rank_gt0 p_rank_abelem ?dimP.
have t1Mp: p \in \tau1(M) := pnatPpi t1MP piPp.
have [Q sylQ not_cPQ]: exists2 Q, Sylow E3 (gval Q) & ~~ (P \subset 'C(Q)).
  apply/exists_inP; rewrite -negb_forall_in; apply: contra not_cE3P.
  move/forall_inP=> cPE3; rewrite centsC -(Sylow_gen E3) gen_subG.
  by apply/bigcupsP=> Q sylQ; rewrite centsC cPE3.
have{sylQ} [q q_pr sylQ] := SylowP _ _ sylQ; have [sQE3 qQ _] := and3P sylQ.
have ntQ: Q :!=: 1 by apply: contraNneq not_cPQ => ->; apply: cents1.
have t3Mq: q \in \tau3(M).
  by rewrite (pnatPpi t3E3) // -p_rank_gt0 -(rank_Sylow sylQ) rank_gt0.
have nQP: P \subset 'N(Q).
  rewrite (subset_trans sPE) ?normal_norm //.
  by rewrite (char_normal_trans _ nsE3E) ?sub_cyclic_char.
have regPQ: 'C_Q(P) = 1.
  apply: contraNeq not_cPQ; rewrite setIC => /meet_Ohm1.
  rewrite setIC => /prime_meetG/=/implyP.
  rewrite (Ohm1_cyclic_pgroup_prime (cyclicS sQE3 cycE3) qQ) // q_pr centsC.
  apply: (coprime_odd_faithful_Ohm1 qQ) nQP _ (mFT_odd _).
  exact: sub_pnat_coprime tau3'1 (pgroupS sQE3 t3E3) t1MP.
have sQE' := subset_trans sQE3 sE3E'.
have sQM := subset_trans (subset_trans sQE3 sE3E) sEM.
have [L maxNL] := mmax_exists (mFT_norm_proper ntQ (mFT_pgroup_proper qQ)).
have [maxL sNQL] := setIdP maxNL; have sQL := subset_trans (normG Q) sNQL.
have notMGL: gval L \notin M :^: G.
  by apply: mmax_norm_notJ maxM maxL qQ sQM sNQL _; rewrite t3Mq !orbT.
have [ntCMaP tiCMaQP]: 'C_(M`_\alpha)(P) != 1 /\ 'C_(M`_\alpha)(Q <*> P) = 1.
  have EpMP: P \in 'E_p^1(M) by apply/pnElemP.
  have p'q: q != p by apply: contraNneq (tau3'1 t1Mp) => <-.
  have [|_ [] //] := cent_Malpha_reg_tau1 maxM t1Mp p'q EpMP ntQ nQP regPQ.
    by apply: contraTneq maxNL => ->; rewrite inE (contra_orbit _ _ notMGL).
  have sM'q: q \in \sigma(M)^' by case/andP: t3Mq.
  exact: subHall_Sylow hallE sM'q (subHall_Sylow hallE3 t3Mq sylQ).
split=> [x E1x | x E3x |]; last exact: subG1_contra (setSI _ sMaMs) ntCMaP.
  apply: contraNeq ntCMaP => ntCE3X.
  have prE31: semiprime M`_\sigma (E3 <*> E1).
    apply: tau13_primact_Msigma maxM complEi _ => regE13.
    by rewrite regE13 ?eqxx in ntCE3X.
  rewrite -subG1 -tiCMaQP /= -(setIidPl sMaMs) -!setIA setIS //.
  rewrite (cent_semiprime prE31 _ ntP) ?setIS ?centS //=.
    by rewrite -!genM_join genS ?mulgSS.
  by rewrite sub_gen // subsetU // sPE1 orbT.
have prE3 := tau3_primact_Msigma maxM hallE hallE3.
apply/eqP; apply/idPn; rewrite prE3 {x E3x}// -rank_gt0.
have [u _ -> ruC] := rank_witness 'C_(M`_\sigma)(E3).
have sCMs := subsetIl M`_\sigma 'C(E3).
have sMu: u \in \sigma(M) by rewrite (pnatPpi (pgroupS sCMs _)) -?p_rank_gt0.
have nCE: E \subset 'N('C_(M`_\sigma)(E3)).
  by rewrite normsI ?norms_cent ?(normal_norm nsE3E) // (subset_trans sEM).
have coCE := coprimeSg sCMs (pnat_coprime (pcore_pgroup _ _) sM'E).
have solC := solvableS (subset_trans sCMs sMsM) (mmax_sol maxM).
have{nCE coCE solC} [U sylU nUE] := coprime_Hall_exists u nCE coCE solC.
have ntU: U :!=: 1 by rewrite -rank_gt0 (rank_Sylow sylU).
have cMsL_Q: Q \subset 'C(M`_\sigma :&: L).
  have t13q: (q \in \tau1(M)) || (q \in \tau3(M)) by rewrite t3Mq orbT.
  have [-> //] := cent_norm_tau13_mmax maxM hallE t13q sQM qQ maxNL.
  by rewrite subsetI sQM.
rewrite /= -(cent_semiprime prE3 sQE3 ntQ) in sylU.
have [sUMs cQU] := subsetIP (pHall_sub sylU).
have{cMsL_Q} sylU_MsL: u.-Sylow(M`_\sigma :&: L) U.
  apply: pHall_subl sylU; last by rewrite subsetI subsetIl centsC.
  by rewrite subsetI sUMs (subset_trans (cents_norm _) sNQL).
have sylU_ML: u.-Sylow(M :&: L) U.
  apply: subHall_Sylow sMu sylU_MsL.
  by rewrite /= -(setIidPl sMsM) -setIA (setI_normal_Hall nsMsM) ?subsetIl.
have [sUML uU _] := and3P sylU_ML; have{sUML} [sUM sUL] := subsetIP sUML.
have [sNUM regPU]: 'N(U) \subset M /\ 'C_U(P) = 1.
  have [bMu | bM'u] := boolP (u \in \beta(M)).
    have [bM_U sMbMa] := (pi_pgroup uU bMu, Mbeta_sub_Malpha M).
    split; first by rewrite beta_norm_sub_mmax /psubgroup ?sUM.
    apply/trivgP; rewrite -tiCMaQP centY setIA setSI // subsetI cQU.
    by rewrite (subset_trans _ sMbMa) // (sub_Hall_pcore (Mbeta_Hall maxM)).
  have sylU_Ms: u.-Sylow(M`_\sigma) U.
    have [H hallH cHE'] := der_compl_cent_beta' maxM hallE.
    rewrite pHallE sUMs (card_Hall sylU) eqn_dvd.
    rewrite partn_dvd ?cardG_gt0 ?cardSg ?subsetIl //=.
    rewrite -(@partn_part u \beta(M)^') => [|v /eqnP-> //].
    rewrite -(card_Hall hallH) partn_dvd ?cardG_gt0 ?cardSg //.
    by rewrite subsetI (pHall_sub hallH) centsC (subset_trans sQE').
  split; first exact: norm_sigma_Sylow (subHall_Sylow hallMs sMu sylU_Ms).
  apply: contraNeq (contra_orbit _ _ notMGL); rewrite -rank_gt0.
  rewrite (rank_pgroup (pgroupS _ uU)) ?subsetIl // => /p_rank_geP[X] /=.
  rewrite -(setIidPr sUMs) setIAC pnElemI -setIdE => /setIdP[EuX sXU].
  have [_ uniqU] := cent_cent_Msigma_tau1_uniq maxM hallE hallE1 sPE1 ntP EuX.
  by rewrite (eq_uniq_mmax (uniqU U sylU_Ms) maxL).
have sPL := subset_trans nQP sNQL.
have sPML: P \subset M :&: L by apply/subsetIP.
have t1Lp: p \in \tau1(L).
  have not_cMsL_P: ~~ (P \subset 'C(M`_\sigma :&: L)).
    apply: contra ntU => cMsL_P; rewrite -subG1 -regPU subsetIidl.
    by rewrite centsC (centsS (pHall_sub sylU_MsL)).
  apply: contraR (not_cMsL_P) => t1L'p.
  have [piEp piLp] := (piSg sPE piPp, piSg sPL piPp).
  case: (Msigma_setI_mmax_central maxM hallE maxL piEp piLp) => // [|->] //.
  apply: contraNneq not_cMsL_P => /commG1P.
  by rewrite centsC; apply: subset_trans sPML.
have EpMLP: P \in 'E_p^1(M :&: L) by apply/pnElemP.
case: (@tau1_mmaxI_asymmetry M L p P q Q u U) => //.
have [sylQ_E [sM'q _]] := (subHall_Sylow hallE3 t3Mq sylQ, andP t3Mq).
have sylQ_M := subHall_Sylow hallE sM'q sylQ_E.
have sQML: Q \subset M :&: L by apply/subsetIP.
by rewrite (subset_trans sPE nUE) (pHall_subl sQML _ sylQ_M) ?subsetIl.
Qed.

(* This is B & G, Corollary 13.11. *)
Corollary tau13_nonregular M E E1 E2 E3 :
    M \in 'M -> sigma_complement M E E1 E2 E3 -> ~ semiregular M`_\sigma E3 ->
  [/\ (*a*) E1 :!=: 1,
      (*b*) E3 ><| E1 = E,
      (*c*) semiprime M`_\sigma E
    & (*d*) forall X, X \in 'E^1(E) -> X <| E].
Proof.
move=> maxM complEi not_regE3Ms.
have [hallE hallE1 hallE2 hallE3 _] := complEi.
have [[sE1E t1E1 _] [sE3E t3E3 _]] := (and3P hallE1, and3P hallE3).
have{hallE2} E2_1: E2 :==: 1.
  apply/idPn; rewrite -rank_gt0; have [p _ ->] := rank_witness E2.
  rewrite p_rank_gt0 => /(pnatPpi (pHall_pgroup hallE2))t2p.
  have [A Ep2A _] := ex_tau2Elem hallE t2p.
  by apply: not_regE3Ms; case: (tau2_regular maxM complEi t2p Ep2A). 
have [_ ntE1 [cycE1 cycE3] [defE _] _] := sigma_compl_context maxM complEi.
rewrite (eqP E2_1) sdprod1g in defE; have{ntE1} ntE1 := ntE1 E2_1.
have [nsE3E _ mulE31 nE31 _] := sdprod_context defE.
have cE3E1 P: P \in 'E^1(E1) -> P \subset 'C(E3).
  by case/nElemP=> p EpP; apply/idPn => /(tau13_regular maxM complEi EpP)[].
split=> // [|X EpX].
  rewrite -mulE31 -norm_joinEr //.
  have [-> | ntE3] := eqsVneq E3 1.
    by rewrite joing1G; apply: (tau1_primact_Msigma maxM hallE hallE1).
  apply: tau13_primact_Msigma maxM complEi _ => regE13.
  have:= ntE1; rewrite -rank_gt0; case/rank_geP=> P EpP.
  have cPE3: E3 \subset 'C(P) by rewrite centsC cE3E1.
  have [p Ep1P] := nElemP EpP; have [sPE1 _ _] := pnElemP Ep1P.
  have ntP: P :!=: 1 by apply: (nt_pnElem Ep1P).
  by case/negP: ntE3; rewrite -(setIidPl cPE3) (cent_semiregular regE13 _ ntP).
have [p Ep1X] := nElemP EpX; have [sXE abelX oX] := pnElemPcard Ep1X.
have [p_pr ntX] := (pnElem_prime Ep1X, nt_pnElem Ep1X isT).
have tau31p: p \in [predU \tau3(M) & \tau1(M)].
  rewrite (pgroupP (pgroupS sXE _)) ?oX // -mulE31 pgroupM.
  rewrite (sub_pgroup _ t3E3) => [|q t3q]; last by rewrite inE /= t3q. 
  by rewrite (sub_pgroup _ t1E1) // => q t1q; rewrite inE /= t1q orbT.
have [/= t3p | t1p] := orP tau31p.
  rewrite (char_normal_trans _ nsE3E) ?sub_cyclic_char //.
  by rewrite (sub_normal_Hall hallE3) // (pi_pgroup (abelem_pgroup abelX)).
have t1X := pi_pgroup (abelem_pgroup abelX) t1p.
have [e Ee sXeE1] := Hall_Jsub (sigma_compl_sol hallE) hallE1 sXE t1X.
rewrite /normal sXE -(conjSg _ _ e) conjGid //= -normJ -mulE31 mulG_subG.
rewrite andbC sub_abelian_norm ?cyclic_abelian ?cents_norm // centsC cE3E1 //.
rewrite -(setIidPr sE1E) nElemI !inE sXeE1 andbT.
by rewrite -(pnElemJ e) conjGid // def_pnElem in Ep1X; case/setIP: Ep1X.
Qed.

(* This is B & G, Lemma 13.12. *)
Lemma tau12_regular M E p q P A :
    M \in 'M -> \sigma(M)^'.-Hall(M) E ->
    p \in \tau1(M) -> P \in 'E_p^1(E) -> q \in \tau2(M) -> A \in 'E_q^2(E) ->
    'C_A(P) != 1 ->
  'C_(M`_\sigma)(P) = 1.
Proof.
move=> maxM hallE t1p EpP t2q Eq2A ntCAP; apply: contraNeq (ntCAP) => ntCMsP.
have [[nsAE _] _ uniq_cMs _] := tau2_compl_context maxM hallE t2q Eq2A.
have [sPE abelP dimP] := pnElemP EpP; have [pP _] := andP abelP.
have ntP: P :!=: 1 by apply: nt_pnElem EpP _.
have [solE t1P] := (sigma_compl_sol hallE, pi_pgroup pP t1p).
have [E1 hallE1 sPE1] := Hall_superset solE sPE t1P.
have [_ [E3 hallE3]] := ex_tau13_compl hallE.
have [E2 _ complEi] := ex_tau2_compl hallE hallE1 hallE3.
have not_cAP: ~~ (P \subset 'C(A)).
  have [_ regCE1A _] := tau2_regular maxM complEi t2q Eq2A.
  apply: contra ntCMsP => cAP; rewrite (cent_semiregular regCE1A _ ntP) //.
  exact/subsetIP.
have [sAE abelA dimA] := pnElemP Eq2A; have [qA _] := andP abelA.
pose Y := 'C_A(P)%G; have{abelA dimA} EqY: Y \in 'E_q^1('C_E(P)).
  have sYA: Y \subset A := subsetIl A _; have abelY := abelemS sYA abelA.
  rewrite !inE setSI // abelY eqn_leq -{2}rank_abelem // rank_gt0 -ltnS -dimA.
  by rewrite properG_ltn_log //= /proper subsetIl subsetIidl centsC.
have ntCMsY: 'C_(M`_\sigma)(Y) != 1.
  by apply: subG1_contra ntCMsP; apply: cent_tau1Elem_Msigma t1p EpP EqY.
have EqEY: Y \in 'E_q^1(E) by rewrite pnElemI in EqY; case/setIP: EqY.
have uniqCY := uniq_cMs _ EqEY ntCMsY.
have [ntA nAE] := (nt_pnElem Eq2A isT, normal_norm nsAE).
have [L maxNL] := mmax_exists (mFT_norm_proper ntA (mFT_pgroup_proper qA)).
have [sLq t12Lp]: q \in \sigma(L) /\ (p \in \tau1(L)) || (p \in \tau2(L)).
  have [sLt2 t12cA' _] := primes_norm_tau2Elem maxM hallE t2q Eq2A maxNL.
  split; first by have /andP[] := sLt2 q t2q.
  apply: pnatPpi (pgroupS (quotientS _ sPE) t12cA') _.
  rewrite -p_rank_gt0 -rank_pgroup ?quotient_pgroup // rank_gt0.
  rewrite -subG1 quotient_sub1 ?subsetI ?sPE // (subset_trans sPE) //.
  by rewrite normsI ?normG ?norms_cent.
have [maxL sNL] := setIdP maxNL; have sEL := subset_trans nAE sNL.
have sL'p: p \in \sigma(L)^' by move: t12Lp; rewrite -andb_orr => /andP[]. 
have [sPL sL'P] := (subset_trans sPE sEL, pi_pgroup pP sL'p).
have{sL'P} [F hallF sPF] := Hall_superset (mmax_sol maxL) sPL sL'P.
have solF := sigma_compl_sol hallF.
have [sAL sL_A] := (subset_trans (normG A) sNL, pi_pgroup qA sLq).
have sALs: A \subset L`_\sigma by rewrite (sub_Hall_pcore (Msigma_Hall maxL)).
have neqLM: L != M by apply: contraTneq sLq => ->; case/andP: t2q.
have{t12Lp} [t1Lp | t2Lp] := orP t12Lp.
  have [F1 hallF1 sPF1] := Hall_superset solF sPF (pi_pgroup pP t1Lp).
  have EqLsY: Y \in 'E_q^1('C_(L`_\sigma)(P)).
    by rewrite !inE setSI //; case/pnElemP: EqY => _ -> ->.
  have [defL _] := cent_cent_Msigma_tau1_uniq maxL hallF hallF1 sPF1 ntP EqLsY.
  by rewrite -in_set1 -uniqCY defL set11 in neqLM.
have sCPL: 'C(P) \subset L.
  have [B Ep2B _] := ex_tau2Elem hallF t2Lp.
  have EpFP: P \in 'E_p^1(F) by apply/pnElemP.
  have [_ _ uniq_cLs _] := tau2_compl_context maxL hallF t2Lp Ep2B.
  by case/mem_uniq_mmax: (uniq_cLs _ EpFP (subG1_contra (setSI _ sALs) ntCAP)).
have Eq2MA: A \in 'E_q^2(M).
  by move: Eq2A; rewrite -(setIidPr (pHall_sub hallE)) pnElemI => /setIP[].
have [_ _ _ tiMsL _] := tau2_context maxM t2q Eq2MA.
by case/negP: ntCMsP; rewrite -subG1 -(tiMsL L) ?setIS // 3!inE neqLM maxL.
Qed.

(* This is B & G, Lemma 13.13. *)
Lemma tau13_nonregular_sigma M E p P :
    M \in 'M -> \sigma(M)^'.-Hall(M) E ->
    P \in 'E_p^1(E) -> (p \in \tau1(M)) || (p \in \tau3(M)) ->
    'C_(M`_\sigma)(P) != 1 ->
  {in 'M('N(P)), forall Mstar, p \in \sigma(Mstar)}.
Proof.
move=> maxM hallE EpP t13Mp ntCMsP L maxNL /=.
have [maxL sNL] := setIdP maxNL.
have [sPE abelP dimP] := pnElemP EpP; have [pP _] := andP abelP.
have [solE ntP] := (sigma_compl_sol hallE, nt_pnElem EpP isT).
have /orP[// | t2Lp] := prime_class_mmax_norm maxL pP sNL.
have:= ntCMsP; rewrite -rank_gt0 => /rank_geP[Q /nElemP[q EqQ]].
have [sQcMsP abelQ dimQ] := pnElemP EqQ; have [sQMs cPQ] := subsetIP sQcMsP.
have piQq: q \in \pi(Q) by rewrite -p_rank_gt0 p_rank_abelem ?dimQ.
have sMq: q \in \sigma(M) := pnatPpi (pgroupS sQMs (pcore_pgroup _ M)) piQq.
have rpM: 'r_p(M) = 1%N by move: t13Mp; rewrite -2!andb_orr andbCA; case: eqP.
have sL'q: q \notin \sigma(L).
  have notMGL: gval L \notin M :^: G.
    by apply: contraL t2Lp => /imsetP[x _ ->]; rewrite tau2J 2!inE rpM andbF.
  by apply: contraFN (sigma_partition maxM maxL notMGL q) => sLq; apply/andP.
have [[sL'p _] [qQ _]] := (andP t2Lp, andP abelQ).
have sL'PQ: \sigma(L)^'.-group (P <*> Q).
  by rewrite cent_joinEr // pgroupM (pi_pgroup pP) // (pi_pgroup qQ).
have sPQ_L: P <*> Q \subset L.
  by rewrite (subset_trans _ sNL) // join_subG normG cents_norm.
have{sPQ_L sL'PQ} [F hallF sPQF] := Hall_superset (mmax_sol maxL) sPQ_L sL'PQ.
have{sPQF} [sPF sQF] := joing_subP sPQF.
have [A Ep2A _] := ex_tau2Elem hallF t2Lp.
have [[nsAF defA1] _ _ _] := tau2_compl_context maxL hallF t2Lp Ep2A.
have EpAP: P \in 'E_p^1(A) by rewrite -defA1; apply/pnElemP.
have{EpAP} sPA: P \subset A by case/pnElemP: EpAP.
have sCQM: 'C(Q) \subset M.
  suffices: 'M('C(Q)) = [set M] by case/mem_uniq_mmax.
  have [t1Mp | t3Mp] := orP t13Mp.
    have [E1 hallE1 sPE1] := Hall_superset solE sPE (pi_pgroup pP t1Mp).
    by have [] := cent_cent_Msigma_tau1_uniq maxM hallE hallE1 sPE1 ntP EqQ.
  have [E3 hallE3 sPE3] := Hall_superset solE sPE (pi_pgroup pP t3Mp).
  have [[E1 hallE1] _] := ex_tau13_compl hallE; have [sE1E _] := andP hallE1.
  have [E2 _ complEi] := ex_tau2_compl hallE hallE1 hallE3.
  have [regE3 | ntE1 _ prE _] := tau13_nonregular maxM complEi.
    by rewrite (cent_semiregular regE3 sPE3 ntP) eqxx in ntCMsP.
  rewrite /= (cent_semiprime prE) // -(cent_semiprime prE sE1E ntE1) in EqQ.
  by have [] := cent_cent_Msigma_tau1_uniq maxM hallE hallE1 _ ntE1 EqQ.
have not_cQA: ~~ (A \subset 'C(Q)).
  have [_ abelA dimA] := pnElemP Ep2A; apply: contraFN (ltnn 1) => cQA.
  by rewrite -dimA -p_rank_abelem // -rpM p_rankS ?(subset_trans cQA sCQM).
have t1Lq: q \in \tau1(L).
  have [_ nsCF t1Fb] :=  tau1_cent_tau2Elem_factor maxL hallF t2Lp Ep2A.
  rewrite (pnatPpi (pgroupS (quotientS _ sQF) t1Fb)) //.
  rewrite -p_rank_gt0 -rank_pgroup ?quotient_pgroup // rank_gt0.
  rewrite -subG1 quotient_sub1 ?(subset_trans _ (normal_norm nsCF)) //.
  by rewrite subsetI sQF centsC.
have defP: 'C_A(Q) = P.
  apply/eqP; rewrite eq_sym eqEcard subsetI sPA centsC cPQ /=.
  have [_ abelA dimA] := pnElemP Ep2A; have [pA _] := andP abelA.
  rewrite (card_pgroup (pgroupS _ pA)) ?subsetIl // (card_pgroup pP) dimP.
  rewrite leq_exp2l ?prime_gt1 ?(pnElem_prime EpP) //.
  by rewrite -ltnS -dimA properG_ltn_log // /proper subsetIl subsetIidl.
have EqFQ: Q \in 'E_q^1(F) by exact/pnElemP.
have regQLs: 'C_(L`_\sigma)(Q) = 1.
  by rewrite (tau12_regular maxL hallF t1Lq EqFQ t2Lp Ep2A) // defP.
have ntAQ: [~: A, Q] != 1 by rewrite (sameP eqP commG1P).
have [_ _ [_]] := tau1_act_tau2 maxL hallF t2Lp Ep2A t1Lq EqFQ regQLs ntAQ.
by case/negP; rewrite /= defP (subset_trans (cent_sub P)).
Qed.

End Section13.


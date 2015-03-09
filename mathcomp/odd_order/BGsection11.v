(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div path fintype.
Require Import bigop finset prime fingroup morphism perm automorphism quotient.
Require Import action gproduct gfunctor pgroup cyclic center commutator.
Require Import gseries nilpotent sylow abelian maximal hall.
Require Import BGsection1 BGsection3 BGsection4 BGsection5 BGsection6.
Require Import BGsection7 BGsection10.

(******************************************************************************)
(*   This file covers B & G, section 11; it has only one definition:          *)
(*    exceptional_FTmaximal p M A0 A <=>                                      *)
(*      p, M and A0 satisfy the conditions of Hypothesis 11.1 in B & G, i.e., *)
(*      M is an "exceptional" maximal subgroup in the terminology of B & G.   *)
(*      In addition, A is elementary abelian p-subgroup of M of rank 2, that  *)
(*      contains A0. The existence of A is guaranteed by Lemma 10.5, but as   *)
(*      in the only two lemmas that make use of the results in this section   *)
(*      (Lemma 12.3 and Theorem 12.5) A is known, we elected to make the      *)
(*      dependency on A explicit.                                             *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Section Section11.

Variable gT : minSimpleOddGroupType.
Local Notation G := (TheMinSimpleOddGroup gT).

Implicit Types p q r : nat.
Implicit Types A E H K M N P Q R S T U V W X Y : {group gT}.

Variables (p : nat) (M A0 A P : {group gT}).

(* This definition corresponsd to Hypothesis 11.1, where the condition on A   *)
(* has been made explicit.                                                    *)
Definition exceptional_FTmaximal :=
  [/\ p \in \sigma(M)^', A \in 'E_p^2(M), A0 \in 'E_p^1(A) & 'N(A0) \subset M].

Hypotheses (maxM : M \in 'M) (excM : exceptional_FTmaximal).
Hypotheses (sylP : p.-Sylow(M) P) (sAP : A \subset P).

(* Splitting the excM hypothesis. *)
Let sM'p : p \in \sigma(M)^'. Proof. by case: excM. Qed.
Let Ep2A : A \in 'E_p^2(M). Proof. by case: excM. Qed.
Let Ep1A0 : A0 \in 'E_p^1(A). Proof. by case: excM. Qed.
Let sNA0_M : 'N(A0) \subset M. Proof. by case: excM. Qed.

(* Arithmetics of p. *)
Let p_pr : prime p := pnElem_prime Ep2A.
Let p_gt1 : p > 1 := prime_gt1 p_pr.
Let p_gt0 : p > 0 := prime_gt0 p_pr.

(* Group orders. *)
Let oA : #|A| = (p ^ 2)%N := card_pnElem Ep2A.
Let oA0 : #|A0| = p := card_pnElem Ep1A0.

(* Structure of A. *)
Let abelA : p.-abelem A. Proof. by case/pnElemP: Ep2A. Qed.
Let pA : p.-group A := abelem_pgroup abelA.
Let cAA : abelian A := abelem_abelian abelA.

(* Various set inclusions. *)
Let sA0A : A0 \subset A. Proof. by case/pnElemP: Ep1A0. Qed.
Let sPM : P \subset M := pHall_sub sylP.
Let sAM : A \subset M := subset_trans sAP sPM.
Let sCA0_M : 'C(A0) \subset M := subset_trans (cent_sub A0) sNA0_M.
Let sCA_M : 'C(A) \subset M := subset_trans (centS sA0A) sCA0_M.

(* Alternative E_p^1 memberships for A0; the first is the one used to state   *)
(* Hypothesis 11.1 in B & G, the second is the form expected by Lemma 10.5.   *)
(* Note that #|A0| = p (oA0 above) would wokr just as well.                   *)
Let Ep1A0_M : A0 \in 'E_p^1(M) := subsetP (pnElemS p 1 sAM) A0 Ep1A0.
Let Ep1A0_G : A0 \in 'E_p^1(G) := subsetP (pnElemS p 1 (subsetT M)) A0 Ep1A0_M.

(* This does not depend on exceptionalM, and could move to Section 10. *)
Lemma sigma'_Sylow_contra : p \in \sigma(M)^' -> ~~ ('N(P) \subset M).
Proof. by apply: contra => sNM; apply/exists_inP; exists P. Qed.

(* First preliminary remark of Section 11; only depends on sM'p and sylP. *)
Let not_sNP_M: ~~ ('N(P) \subset M) := sigma'_Sylow_contra sM'p.

(* Second preliminary remark of Section 11; only depends on sM'p, Ep1A0_M,    *)
(* and sNA0_M.                                                                *)
Lemma p_rank_exceptional : 'r_p(M) = 2.
Proof. exact: sigma'_norm_mmax_rank2 (pgroupS sA0A pA) _. Qed.
Let rM := p_rank_exceptional.

(* Third preliminary remark of Section 11. *)
Lemma exceptional_pmaxElem : A \in 'E*_p(G).
Proof.
have [_ _ dimA]:= pnElemP Ep2A.
apply/pmaxElemP; split=> [|E EpE sAE]; first by rewrite !inE subsetT.
have [//|ltAE]: A :=: E \/ A \proper E := eqVproper sAE.
have [_ abelE] := pElemP EpE; have [pE cEE _] := and3P abelE.
suffices: logn p #|E| <= 'r_p(M) by rewrite leqNgt rM -dimA properG_ltn_log.
by rewrite logn_le_p_rank // inE (subset_trans cEE) ?(subset_trans (centS sAE)).
Qed.
Let EpmA := exceptional_pmaxElem.

(* This is B & G, Lemma 11.1. *)
Lemma exceptional_TIsigmaJ g q Q1 Q2 :
    g \notin M -> A \subset M :^ g ->
    q.-Sylow(M`_\sigma) Q1 ->  A \subset 'N(Q1) ->
    q.-Sylow(M`_\sigma :^ g) Q2 -> A \subset 'N(Q2) ->
     (*a*) Q1 :&: Q2 = 1
  /\ (*b*) (forall X, X \in 'E_p^1(A) -> 'C_Q1(X) = 1 \/ 'C_Q2(X) = 1).
Proof.
move=> notMg sAMg sylQ1 nQ1A sylQ2 nQ2A.
have [-> | ntQ1] := eqsVneq Q1 1.
  by split=> [|? _]; last left; apply: (setIidPl (sub1G _)).
have [sQ1Ms qQ1 _] := and3P sylQ1.
have{qQ1} [q_pr q_dv_Q1 _] := pgroup_pdiv qQ1 ntQ1.
have{sQ1Ms q_dv_Q1} sMq: q \in \sigma(M).
  exact: pgroupP (pgroupS sQ1Ms (pcore_pgroup _ _)) q q_pr q_dv_Q1.
have{sylQ1} sylQ1: q.-Sylow(M) Q1.
  by rewrite (subHall_Sylow (Msigma_Hall maxM)).
have sQ1M := pHall_sub sylQ1.
have{sylQ2} sylQ2g': q.-Sylow(M) (Q2 :^ g^-1).
  by rewrite (subHall_Sylow (Msigma_Hall _)) // -(pHallJ2 _ _ _ g) actKV.
have sylQ2: q.-Sylow(G) Q2.
  by rewrite -(pHallJ _ _ (in_setT g^-1)) (sigma_Sylow_G maxM).
suffices not_Q1_CA_Q2: gval Q2 \notin Q1 :^: 'O_\pi(A)^'('C(A)).
  have ncA: normed_constrained A.
    have ntA: A :!=: 1 by rewrite -cardG_gt1 oA (ltn_exp2l 0).
    exact: plength_1_normed_constrained ntA EpmA (mFT_proper_plength1 _).
  have q'A: q \notin \pi(A).
    by apply: contraL sMq; move/(pnatPpi pA); move/eqnP->.
  have maxnAq Q: q.-Sylow(G) Q -> A \subset 'N(Q) -> Q \in |/|*(A; q).
    move=> sylQ; case/(max_normed_exists (pHall_pgroup sylQ)) => R maxR sQR.
    have [qR _] := mem_max_normed maxR.
    by rewrite -(group_inj (sub_pHall sylQ qR sQR (subsetT R))).
  have maxQ1 := maxnAq Q1 (sigma_Sylow_G maxM sMq sylQ1) nQ1A.
  have maxQ2 := maxnAq Q2 sylQ2 nQ2A.
  have transCAQ := normed_constrained_meet_trans ncA q'A _ _ maxQ1 maxQ2.
  split=> [|X EpX].
    apply: contraNeq not_Q1_CA_Q2 => ntQ12; apply/imsetP.
    apply: transCAQ (sAM) (mmax_proper maxM) _ _.
      by rewrite (setIidPl sQ1M).
    by apply: contraNneq ntQ12 => tiQ2M; rewrite setIC -subG1 -tiQ2M setIS.
  apply/pred2P; apply: contraR not_Q1_CA_Q2; case/norP=> ntCQ1 ntCQ2.
  have [sXA _ oX] := pnElemPcard EpX.
  apply/imsetP; apply: transCAQ (centSS _ sXA cAA) _ ntCQ1 ntCQ2 => //.
  by rewrite mFT_cent_proper // -cardG_gt1 oX prime_gt1.
apply: contra notMg; case/imsetP=> k cAk defQ2.
have{cAk} Mk := subsetP sCA_M k (subsetP (pcore_sub _ _) k cAk).
have{k Mk defQ2} sQ2M: Q2 \subset M by rewrite defQ2 conj_subG.
have [sQ2g'M qQ2g' _] := and3P sylQ2g'.
by rewrite (sigma_Sylow_trans _ sylQ2g') // actKV.
Qed.

(* This is B & G, Corollary 11.2. *)
Corollary exceptional_TI_MsigmaJ g :
  g \notin M -> A \subset M :^ g ->
    (*a*) M`_\sigma :&: M :^ g = 1
 /\ (*b*) M`_\sigma :&: 'C(A0 :^ g) = 1.
Proof.
move=> notMg sAMg; set Ms := M`_\sigma; set H := [group of Ms :&: M :^ g].
have [H1 | ntH] := eqsVneq H 1.
  by split=> //; apply/trivgP; rewrite -H1 setIS //= centJ conjSg.
pose q := pdiv #|H|.
suffices: #|H|`_q == 1%N by rewrite p_part_eq1 pi_pdiv cardG_gt1 ntH.
have nsMsM: Ms <| M := pcore_normal _ _; have [_ nMsM] := andP nsMsM.
have sHMs: H \subset Ms := subsetIl _ _.
have sHMsg: H \subset Ms :^ g.
  rewrite -sub_conjgV (sub_Hall_pcore (Msigma_Hall _)) //.
    by rewrite pgroupJ (pgroupS sHMs) ?pcore_pgroup.
  by rewrite sub_conjgV subsetIr.
have nMsA := subset_trans sAM nMsM.
have nHA: A \subset 'N(H) by rewrite normsI // normsG.
have nMsgA: A \subset 'N(Ms :^ g) by rewrite normJ (subset_trans sAMg) ?conjSg.
have coMsA: coprime #|Ms| #|A|.
  by rewrite oA coprime_expr ?(pnat_coprime (pcore_pgroup _ _)) ?pnatE.
have coHA: coprime #|H| #|A| := coprimeSg sHMs coMsA.
have coMsgA: coprime #|Ms :^ g| #|A| by rewrite cardJg.
have solA: solvable A := abelian_sol cAA.
have [Q0 sylQ0 nQ0A] := sol_coprime_Sylow_exists q solA nHA coHA.
have [sQ0H qQ0 _] := and3P sylQ0.
have supQ0 := sol_coprime_Sylow_subset _ _ solA (subset_trans sQ0H _) qQ0 nQ0A.
have [Q1 [sylQ1 nQ1A sQ01]] := supQ0 _ nMsA coMsA sHMs.
have [Q2 [sylQ2 nQ2A sQ02]] := supQ0 _ nMsgA coMsgA sHMsg.
have tiQ12: Q1 :&: Q2 = 1.
  by have [-> _] := exceptional_TIsigmaJ notMg sAMg sylQ1 nQ1A sylQ2 nQ2A.
by rewrite -(card_Hall sylQ0) -trivg_card1 -subG1 -tiQ12 subsetI sQ01.
Qed.

(* This is B & G, Theorem 11.3. *)
Theorem exceptional_sigma_nil : nilpotent M`_\sigma.
Proof.
have [g nPg notMg] := subsetPn not_sNP_M.
set Ms := M`_\sigma; set F := Ms <*> A0 :^ g.
have sA0gM: A0 :^ g \subset M.
  by rewrite (subset_trans _ sPM) // -(normP nPg) conjSg (subset_trans sA0A).
have defF: Ms ><| A0 :^ g = F.
  rewrite sdprodEY ?coprime_TIg //.
    by rewrite (subset_trans sA0gM) ?gFnorm.
  by rewrite cardJg oA0 (pnat_coprime (pcore_pgroup _ _)) ?pnatE.
have regA0g: 'C_Ms(A0 :^ g) = 1.
  case/exceptional_TI_MsigmaJ: notMg => //.
  by rewrite -sub_conjgV (subset_trans _ sPM) // sub_conjgV (normP _).
rewrite (prime_Frobenius_sol_kernel_nil defF) ?cardJg ?oA0 //.
by rewrite (solvableS _ (mmax_sol maxM)) // join_subG pcore_sub.
Qed.

(* This is B & G, Corollary 11.4. *)
Corollary exceptional_sigma_uniq H :
  H \in 'M(A) -> H`_\sigma :&: M `_\sigma != 1 -> H :=: M.
Proof.
rewrite setIC => /setIdP[maxH sAH] ntMsHs.
have [g _ defH]: exists2 g, g \in G & H :=: M :^ g.
  apply/imsetP; apply: contraR ntMsHs => /sigma_disjoint[] // _ _.
  by case/(_ exceptional_sigma_nil)=> ->.
rewrite defH conjGid //; apply: contraR ntMsHs => notMg.
have [|tiMsMg _] := exceptional_TI_MsigmaJ notMg; first by rewrite -defH.
by rewrite -subG1 -tiMsMg -defH setIS ?pcore_sub.
Qed.

(* This is B & G, Theorem 11.5. *)
Theorem exceptional_Sylow_abelian P1 : p.-Sylow(M) P1 -> abelian P1.
Proof.
have nregA Q: gval Q != 1 -> A \subset 'N(Q) -> coprime #|Q| #|A| ->
  exists2 X, X \in 'E_p^1(A) & 'C_Q(X) != 1.
- move=> ntQ nQA coQA; apply/exists_inP; apply: contraR ntQ.
  rewrite negb_exists_in -subG1; move/forall_inP=> regA.
  have ncycA: ~~ cyclic A by rewrite (abelem_cyclic abelA) oA pfactorK.
  rewrite -(coprime_abelian_gen_cent1 _ _ nQA) // gen_subG.
  apply/bigcupsP=> x /setD1P[ntx Ax].
  apply/negPn; rewrite /= -cent_cycle subG1 regA // p1ElemE // !inE.
  by rewrite cycle_subG Ax /= -orderE (abelem_order_p abelA).
suffices{P1} cPP: abelian P.
  by move=> sylP1; have [m _ ->] := Sylow_trans sylP sylP1; rewrite abelianJ.
have [g nPg notMg] := subsetPn not_sNP_M.
pose Ms := M`_\sigma; pose q := pdiv #|Ms|; have pP := pHall_pgroup sylP.
have nMsP: P \subset 'N(Ms) by rewrite (subset_trans sPM) ?gFnorm.
have coMsP: coprime #|Ms| #|P|.
  exact: pnat_coprime (pcore_pgroup _ _) (pi_pnat pP sM'p).
have [Q1 sylQ1 nQ1P]:= sol_coprime_Sylow_exists q (pgroup_sol pP) nMsP coMsP.
have ntQ1: Q1 :!=: 1.
  rewrite -cardG_gt1 (card_Hall sylQ1) p_part_gt1 pi_pdiv cardG_gt1.
  by rewrite Msigma_neq1.
have nQ1A: A \subset 'N(Q1) := subset_trans sAP nQ1P.
have coQ1A: coprime #|Q1| #|A|.
  by rewrite (coprimeSg (pHall_sub sylQ1)) // (coprimegS sAP).
have [X1 EpX1 nregX11] := nregA _ ntQ1 nQ1A coQ1A.
pose Q2 := Q1 :^ g; have sylQ2: q.-Sylow(Ms :^ g) Q2 by rewrite pHallJ2.
have{ntQ1} ntQ2: Q2 != 1 by rewrite -!cardG_gt1 cardJg in ntQ1 *.
have nQ2A: A \subset 'N(Q2) by rewrite (subset_trans sAP) ?norm_conj_norm.
have{coQ1A} coQ2A: coprime #|Q2| #|A| by rewrite cardJg. 
have{nregA ntQ2 coQ2A} [X2 EpX2 nregX22] := nregA _ ntQ2 nQ2A coQ2A.
have [|_ regA]:= exceptional_TIsigmaJ notMg _ sylQ1 nQ1A sylQ2 nQ2A.
  by rewrite (subset_trans sAP) // -(normP nPg) conjSg.
have regX21: 'C_Q1(X2) = 1 by case: (regA X2) nregX22 => // ->; rewrite eqxx.
have regX12: 'C_Q2(X1) = 1 by case: (regA X1) nregX11 => // ->; rewrite eqxx.
pose X := 'Ohm_1('Z(P))%G.
have eqCQ12_X: ('C_Q1(X) == 1) = ('C_Q2(X) == 1).
  rewrite -(inj_eq (@conjsg_inj _ g)) conjs1g conjIg -/Q2 -centJ (normP _) //.
  rewrite (subsetP (char_norm_trans (Ohm_char 1 _) _) g nPg) //.
  by rewrite char_norms ?center_char.
have{EpX1} EpX1: X1 \in 'E_p^1(A) :\ X.
  rewrite 2!inE EpX1 andbT; apply: contraNneq nregX11 => defX1.
  by rewrite defX1 eqCQ12_X -defX1 regX12.
have{EpX2 eqCQ12_X} EpX2: X2 \in 'E_p^1(A) :\ X.
  rewrite 2!inE EpX2 andbT; apply: contraNneq nregX22 => defX2.
  by rewrite defX2 -eqCQ12_X -defX2 regX21.
apply: contraR nregX11 => not_cPP.
have{not_cPP} transNPA: [transitive 'N_P(A), on 'E_p^1(A) :\ X | 'JG].
  have [|_ _]:= basic_p2maxElem_structure _ pP sAP not_cPP; last by [].
  by rewrite inE (subsetP (pnElemS p 2 (subsetT M))).
have [y PnAy ->] := atransP2 transNPA EpX2 EpX1; have [Py _] := setIP PnAy.
by rewrite centJ -(normsP nQ1P y Py) -conjIg regX21 conjs1g.
Qed.

(* This is B & G, Corollary 11.6. *)
Corollary exceptional_structure (Ms := M`_\sigma) :
  [/\ (*a*) A :=: 'Ohm_1(P),
      (*b*) 'C_Ms(A) = 1
    & (*c*) exists2 A1, A1 \in 'E_p^1(A) & exists2 A2, A2 \in 'E_p^1(A) &
            [/\ A1 :!=: A2, 'C_Ms(A1) = 1 & 'C_Ms(A2) = 1]].
Proof.
pose iMNA := #|'N(A) : M|.
have defA: A :=: 'Ohm_1(P).
  apply/eqP; rewrite eqEcard -{1}(Ohm1_id abelA) OhmS //= oA -rM.
  rewrite -(p_rank_Sylow sylP) p_rank_abelian ?exceptional_Sylow_abelian //.
  by rewrite -card_pgroup // (pgroupS _ (pHall_pgroup sylP)) ?Ohm_sub.
have iMNAgt1: iMNA > 1.
  rewrite indexg_gt1 defA; apply: contra (subset_trans _) not_sNP_M.
  by rewrite char_norms ?Ohm_char.
have iMNAgt2: iMNA > 2.
  pose q := pdiv iMNA; have q_iMNA: q %| iMNA := pdiv_dvd iMNA.
  rewrite (leq_trans _ (dvdn_leq (ltnW _) q_iMNA)) // ltn_neqAle eq_sym.
  rewrite (sameP eqP (prime_oddPn _)) ?prime_gt1 ?pdiv_prime //.
  by rewrite (dvdn_odd q_iMNA) // (dvdn_odd (dvdn_indexg _ _)) ?mFT_odd.
rewrite [iMNA](cardD1 (gval M)) orbit_refl !ltnS lt0n in iMNAgt1 iMNAgt2.
have{iMNAgt1} [Mg1 /= NM_Mg1] := pred0Pn iMNAgt1.
rewrite (cardD1 Mg1) inE /= NM_Mg1 ltnS lt0n in iMNAgt2.
have{iMNAgt2} [Mg2 /= NM_Mg2] := pred0Pn iMNAgt2.
case/andP: NM_Mg1 => neM_Mg1 /rcosetsP[g1 nAg1 defMg1].
have{neM_Mg1} notMg1: g1 \notin M.
  by apply: contra neM_Mg1 => M_g1; rewrite defMg1 rcoset_id.
case/and3P: NM_Mg2 => neMg12 neM_Mg2 /rcosetsP[g2 nAg2 defMg2].
have{neM_Mg2} notMg2: g2 \notin M.
  by apply: contra neM_Mg2 => M_g2; rewrite defMg2 rcoset_id.
pose A1 := (A0 :^ g1)%G; pose A2 := (A0 :^ g2)%G.
have EpA1: A1 \in 'E_p^1(A) by rewrite -(normP nAg1) pnElemJ.
have EpA2: A2 \in 'E_p^1(A) by rewrite -(normP nAg2) pnElemJ.
have{neMg12} neqA12: A1 :!=: A2.
  rewrite -(canF_eq (conjsgKV g2)) -conjsgM (sameP eqP normP).
  rewrite (contra (subsetP sNA0_M _)) // -mem_rcoset.
  by apply: contra neMg12 => g1Mg2; rewrite defMg1 defMg2 (rcoset_transl g1Mg2).
have{notMg1 nAg1} regA1: 'C_Ms(A1) = 1.
  by case/exceptional_TI_MsigmaJ: notMg1; rewrite // -(normP nAg1) conjSg.
have{notMg2 nAg2} regA2: 'C_Ms(A2) = 1.
  by case/exceptional_TI_MsigmaJ: notMg2; rewrite // -(normP nAg2) conjSg.
split=> //; last by exists A1 => //; exists A2 => //.
by apply/trivgP; rewrite -regA1 setIS ?centS //; case/pnElemP: EpA1.
Qed.

(* This is B & G, Theorem 11.7 (the main result on exceptional subgroups). *)
Theorem exceptional_mul_sigma_normal : M`_\sigma <*> A <| M.
Proof.
set Ms := M`_\sigma; have pP := pHall_pgroup sylP; have solM := mmax_sol maxM.
have [E hallE sPE] := Hall_superset solM sPM (pi_pnat pP sM'p).
have sAE := subset_trans sAP sPE; have [sEM s'E _] := and3P hallE.
have [_ _ dimA] := pnElemP Ep2A.
have rE: 'r(E) = 2.
  apply/eqP; rewrite eqn_leq -{2}dimA -rank_abelem ?rankS // andbT leqNgt.
  have [q q_pr ->]:= rank_witness E; apply/negP=> rqEgt2.
  have piEq: q \in \pi(E) by rewrite -p_rank_gt0 -(subnKC rqEgt2).
  case/negP: (pnatPpi s'E piEq); rewrite /= alpha_sub_sigma // !inE.
  by rewrite (leq_trans rqEgt2) ?p_rankS.
have rFEle2: 'r('F(E)) <= 2 by rewrite -rE rankS ?Fitting_sub.
have solE := solvableS sEM solM; have oddE := mFT_odd E.
pose tau : nat_pred := [pred q | q > p]; pose K := 'O_tau(E).
have hallK: tau.-Hall(E) K by rewrite rank2_ge_pcore_Hall.
pose ptau : nat_pred := [pred q | q >= p]; pose KP := K <*> P.
have nKP: P \subset 'N(K) by rewrite (subset_trans sPE) ?gFnorm.
have coKP: coprime #|K| #|P|.
  by rewrite (pnat_coprime (pcore_pgroup _ _)) ?(pi_pnat pP) //= !inE ltnn.
have hallKP: ptau.-Hall(E) KP.
  rewrite pHallE join_subG pcore_sub sPE /= norm_joinEr ?coprime_cardMg //.
  apply/eqP; rewrite -(partnC tau (part_gt0 _ _)) (card_Hall sylP).
  rewrite (card_Hall hallK) partn_part => [|q]; last exact: leqW.
  rewrite (card_Hall hallE) -!partnI; congr (_ * _)%N; apply: eq_partn => q.
  by rewrite 4!inE andbC /= 8!inE -leqNgt -eqn_leq eq_sym; case: eqP => // <-.
have nsKP_E: KP <| E.
  by rewrite [KP](eq_Hall_pcore _ hallKP) ?pcore_normal ?rank2_ge_pcore_Hall.
have [cKA | not_cKA]:= boolP (A \subset 'C(K)).
  pose KA := K <*> A; have defKA: K \x A = KA.
    by rewrite dprodEY // coprime_TIg // (coprimegS sAP).
  have defA: 'Ohm_1(P) = A by case exceptional_structure.
  have{defA} defA: 'Ohm_1('O_p(KP)) = A.
    apply/eqP; rewrite -defA eqEsubset OhmS /=; last first.
      rewrite pcore_sub_Hall ?(pHall_subl _ _ sylP) ?joing_subr //.
      exact: subset_trans (pHall_sub hallKP) sEM.
    rewrite -Ohm_id defA OhmS // pcore_max // /normal join_subG.
    rewrite (subset_trans sAP) ?joing_subr // cents_norm 1?centsC //=.
    by rewrite -defA gFnorm.
  have nMsE: E \subset 'N(Ms) by rewrite (subset_trans sEM) ?gFnorm.
  have tiMsE: Ms :&: E = 1.
    by rewrite coprime_TIg ?(pnat_coprime (pcore_pgroup _ _)).
  have <-: Ms * E = M.
    apply/eqP; rewrite eqEcard mulG_subG pcore_sub sEM /= TI_cardMg //.
    by rewrite (card_Hall hallE) (card_Hall (Msigma_Hall maxM)) ?partnC.
  rewrite norm_joinEr -?quotientK ?(subset_trans sAE) //= cosetpre_normal.
  rewrite quotient_normal // -defA (char_normal_trans (Ohm_char _ _)) //.
  by rewrite (char_normal_trans (pcore_char p _)).
pose q := pdiv #|K : 'C_K(A)|.
have q_pr: prime q by rewrite pdiv_prime // indexg_gt1 subsetI subxx centsC.
have [nKA coKA] := (subset_trans sAP nKP, coprimegS sAP coKP).
have [Q sylQ nQA]: exists2 Q : {group gT}, q.-Sylow(K) Q & A \subset 'N(Q).
  by apply: sol_coprime_Sylow_exists => //; exact: (pgroup_sol pA).
have [sQK qQ q'iQK] := and3P sylQ; have [sKE tauK _]:= and3P hallK.
have{q'iQK} not_cQA: ~~ (A \subset 'C(Q)).
  apply: contraL q'iQK => cQA; rewrite p'natE // negbK.
  rewrite -(Lagrange_index (subsetIl K 'C(A))) ?dvdn_mulr ?pdiv_dvd //.
  by rewrite subsetI sQK centsC.
have ntQ: Q :!=: 1 by apply: contraNneq not_cQA => ->; exact: cents1.
have q_dv_K: q %| #|K| := dvdn_trans (pdiv_dvd _) (dvdn_indexg _ _).
have sM'q: q \in (\sigma(M))^' := pgroupP (pgroupS sKE s'E) q q_pr q_dv_K.
have{q_dv_K} tau_q: q \in tau := pgroupP tauK q q_pr q_dv_K.
have sylQ_E: q.-Sylow(E) Q := subHall_Sylow hallK tau_q sylQ.
have sylQ_M: q.-Sylow(M) Q := subHall_Sylow hallE sM'q sylQ_E.
have q'p: p != q by rewrite neq_ltn [p < q]tau_q.
have [regQ | nregQ] := eqVneq 'C_Q(A) 1; last first.
  have ncycQ: ~~ cyclic Q.
    apply: contra not_cQA => cycQ.
    rewrite (coprime_odd_faithful_Ohm1 qQ) ?mFT_odd ?(coprimeSg sQK) //.
    rewrite centsC; apply: contraR nregQ => not_sQ1_CA.
    rewrite setIC TI_Ohm1 // setIC prime_TIg //.
    by rewrite (Ohm1_cyclic_pgroup_prime cycQ qQ ntQ).
  have {ncycQ} rQ: 'r_q(Q) = 2.
    apply/eqP; rewrite eqn_leq ltnNge -odd_pgroup_rank1_cyclic ?mFT_odd //.
    by rewrite -rE  -rank_pgroup ?rankS // (pHall_sub sylQ_E).
  have [B Eq2B]: exists B, B \in 'E_q^2(Q) by apply/p_rank_geP; rewrite rQ.
  have maxB: B \in 'E*_q(G).
    apply: subsetP (subsetP (pnElemS q 2 (pHall_sub sylQ_M)) B Eq2B).
    by rewrite sigma'_rank2_max // -(p_rank_Sylow sylQ_M).
  have CAq: q %| #|'C(A)|.
    apply: dvdn_trans (cardSg (subsetIr Q _)).
    by have [_ ? _] := pgroup_pdiv (pgroupS (subsetIl Q _) qQ) nregQ.
  have [Qstar maxQstar sQ_Qstar] := max_normed_exists qQ nQA.
  have [|Qm] := max_normed_2Elem_signaliser q'p _ maxQstar CAq.
    by rewrite inE (subsetP (pnElemS p 2 (subsetT M))).
  case=> _ sAQm [_ _ cQstarQm]; rewrite (centSS sAQm sQ_Qstar) // in not_cQA.
  apply: cQstarQm; apply/implyP=> _; apply/set0Pn; exists B.
  have{Eq2B} Eq2B := subsetP (pnElemS q 2 sQ_Qstar) B Eq2B.
  rewrite inE Eq2B (subsetP (pmaxElemS q (subsetT _))) // inE maxB inE.
  by have [? _ _] := pnElemP Eq2B.
pose Q0 := 'Z(Q); have charQ0: Q0 \char Q := center_char Q.
have nQ0A: A \subset 'N(Q0) := char_norm_trans charQ0 nQA.
have defQ0: [~: A, Q0] = Q0. 
  rewrite -{2}[Q0](coprime_abelian_cent_dprod nQ0A) ?center_abelian //.
    by rewrite setIAC regQ (setIidPl (sub1G _)) dprodg1 commGC.
  by rewrite (coprimeSg (subset_trans (center_sub Q) sQK)).
have [_ _ [A1 EpA1 [A2 EpA2 [neqA12 regA1 regA2]]]] := exceptional_structure.
have defA: A1 \x A2 = A by apply/(p2Elem_dprodP Ep2A EpA1 EpA2).
have{defQ0} defQ0: [~: A1, Q0] * [~: A2, Q0] = Q0.
  have{defA} [[_ defA cA12 _] [sA2A _ _]] := (dprodP defA, pnElemP EpA2).
  by rewrite -commMG ?defA // normsR ?(cents_norm cA12) // (subset_trans sA2A).
have nsQ0M: Q0 <| M.
  have sQ0M: Q0 \subset M := subset_trans (center_sub Q) (pHall_sub sylQ_M).
  have qQ0: q.-group Q0 := pgroupS (center_sub Q) qQ.
  have p'Q0: p^'.-group Q0 by apply: (pi_pnat qQ0); rewrite eq_sym in q'p.
  have sM'Q0: \sigma(M)^'.-group Q0 := pi_pnat qQ0 sM'q.
  have cQ0Q0: abelian Q0 := center_abelian Q.
  have sA_NQ0: A \subset 'N_M(Q0) by rewrite subsetI sAM.
  have sEpA_EpN := subsetP (pnElemS p 1 sA_NQ0).
  have nsRQ0 := commG_sigma'_1Elem_cyclic maxM sQ0M sM'Q0 sM'p (sEpA_EpN _ _).
  rewrite -defQ0 -!(commGC Q0).
  by apply: normalM; [case/nsRQ0: EpA1 | case/nsRQ0: EpA2].
case/exists_inP: sM'q; exists Q => //.
rewrite (subset_trans (char_norms charQ0)) ?(mmax_normal maxM nsQ0M) //= -/Q0.
by apply: contraNneq ntQ; move/(trivg_center_pgroup qQ)->.
Qed.

End Section11.

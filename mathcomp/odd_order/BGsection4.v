(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
Require Import fintype finfun bigop ssralg finset prime binomial.
Require Import fingroup morphism automorphism perm quotient action gproduct.
Require Import gfunctor commutator zmodp cyclic center pgroup gseries nilpotent.
Require Import sylow abelian maximal extremal hall.
Require Import matrix mxalgebra mxrepresentation mxabelem.
Require Import BGsection1 BGsection2.

(******************************************************************************)
(*   This file covers B & G, Section 4, i.e., the proof of structure theorems *)
(* for solvable groups with a small (of rank at most 2) Fitting subgroup.     *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Section Section4.

Implicit Type gT : finGroupType.
Implicit Type p : nat.

(* B & G, Lemma 4.1 (also, Gorenstein, 1.3.4, and Aschbacher, ex. 2.4) is     *)
(* covered by Lemma center_cyclic_abelian, in center.v.                       *)

(* B & G, Lemma 4.2 is covered by Lemmas commXg, commgX, commXXg (for 4.2(a)) *)
(* and expMg_Rmul (for 4.2(b)) in commutators.v.                              *)

(* This is B & G, Proposition 4.3. *)
Proposition exponent_odd_nil23 gT (R : {group gT}) p :
   p.-group R -> odd #|R| -> nil_class R <= 2 + (p > 3) ->
 [/\ (*a*) exponent 'Ohm_1(R) %| p
   & (*b*) R^`(1) \subset 'Ohm_1(R) ->
           {in R &, {morph expgn^~ p : x y / x * y}}].
Proof.
move=> pR oddR classR.
pose f n := 'C(n, 3); pose g n := 'C(n, 3).*2 + 'C(n, 2).
have fS n: f n.+1 = 'C(n, 2) + f n by rewrite /f binS addnC. 
have gS n: g n.+1 = 'C(n, 2).*2 + 'C(n, 1) + g n.
  by rewrite /g !binS doubleD -!addnA; do 3!nat_congr.
have [-> | ntR] := eqsVneq R 1.
  rewrite Ohm1 exponent1 der_sub dvd1n; split=> // _ _ _ /set1P-> /set1P->.
  by rewrite !(mulg1, expg1n).
have{ntR} [p_pr p_dv_R _] := pgroup_pdiv pR ntR.
have pdivbin2: p %| 'C(p, 2).
  by rewrite prime_dvd_bin //= odd_prime_gt2 // (dvdn_odd p_dv_R).
have p_dv_fp: p > 3 -> p %| f p by move=> pgt3; apply: prime_dvd_bin.
have p_dv_gp: p > 3 -> p %| g p.
  by move=> pgt3; rewrite dvdn_add // -muln2 dvdn_mulr // p_dv_fp.
have exp_dv_p x m (S : {group gT}):
  exponent S %| p -> p %| m -> x \in S -> x ^+ m = 1.
- move=> expSp p_dv_m Sx; apply/eqP; rewrite -order_dvdn.
  by apply: dvdn_trans (dvdn_trans expSp p_dv_m); apply: dvdn_exponent.
have p3_L21: p <= 3 -> {in R & &, forall u v w, [~ u, v, w] = 1}.
  move=> lep3 u v w Ru Rv Rw; rewrite (ltnNge 3) lep3 nil_class2 in classR. 
  by apply/eqP/commgP; red; rewrite (centerC Rw) // (subsetP classR) ?mem_commg.
have{fS gS} expMR_fg: {in R &, forall u v n (r := [~ v, u]),
  (u * v) ^+ n = u ^+ n * v ^+ n * r ^+ 'C(n, 2)
                  * [~ r, u] ^+ f n * [~ r, v] ^+ g n}.
- move=> u v Ru Rv n r; have Rr: r \in R by exact: groupR.
  have cRr: {in R &, forall x y, commute x [~ r, y]}.
    move=> x y Rx Ry /=; red; rewrite (centerC Rx) //.
    have: [~ r, y] \in 'L_3(R) by rewrite !mem_commg.
    by apply: subsetP; rewrite -nil_class3 (leq_trans classR) // !ltnS leq_b1.
  elim: n => [|n IHn]; first by rewrite !mulg1.
  rewrite 3!expgSr {}IHn -!mulgA (mulgA (_ ^+ f n)); congr (_ * _).
  rewrite -commuteM; try by apply: commuteX; red; rewrite cRr ?groupM.
  rewrite -mulgA; do 2!rewrite (mulgA _ u) (commgC _ u) -2!mulgA.
  congr (_ * (_ * _)); rewrite (mulgA _ v).
  have ->: [~ v ^+ n, u] = r ^+ n * [~ r, v] ^+ 'C(n, 2). 
    elim: n => [|n IHn]; first by rewrite comm1g mulg1.
    rewrite !expgS commMgR -/r {}IHn commgX; last exact: cRr.
    rewrite binS bin1 addnC expgD -2!mulgA; congr (_ * _); rewrite 2!mulgA.
    by rewrite commuteX2 // /commute cRr.
  rewrite commXg 1?commuteX2 -?[_ * v]commuteX; try exact: cRr.
  rewrite mulgA {1}[mulg]lock mulgA -mulgA -(mulgA v) -!expgD -fS -lock.
  rewrite -{2}(bin1 n) addnC -binS -2!mulgA (mulgA _ v) (commgC _ v).
  rewrite -commuteX; last by red; rewrite cRr ?(Rr, groupR, groupX, groupM).
  rewrite -3!mulgA; congr (_ * (_ * _)); rewrite 2!mulgA.
  rewrite commXg 1?commuteX2; try by red; rewrite cRr 1?groupR.
  by rewrite -!mulgA -!expgD addnCA binS addnAC addnn addnC -gS.
have expR1p: exponent 'Ohm_1(R) %| p.
  elim: _.+1 {-2 4}R (ltnSn #|R|) (subxx R) => // n IHn Q leQn sQR.
  rewrite (OhmE 1 (pgroupS sQR pR)) expn1 -sub_LdivT.
  rewrite gen_set_id ?subsetIr //.
  apply/group_setP; rewrite !inE group1 expg1n /=.
  split=> // x y /LdivP[Qx xp1] /LdivP[Qy yp1]; rewrite !inE groupM //=.
  have sxQ: <[x]> \subset Q by rewrite cycle_subG.
  have [{sxQ}defQ|[S maxS /= sxS]] := maximal_exists sxQ.
    rewrite expgMn; first by rewrite xp1 yp1 mulg1.
    by apply: (centsP (cycle_abelian x)); rewrite ?defQ.
  have:= maxgroupp maxS; rewrite properEcard => /andP[sSQ ltSQ].
  have pQ := pgroupS sQR pR; have pS := pgroupS sSQ pQ.
  have{ltSQ leQn} ltSn: #|S| < n by exact: leq_trans ltSQ _.
  have expS1p := IHn _ ltSn (subset_trans sSQ sQR).
  have defS1 := Ohm1Eexponent p_pr expS1p; move/exp_dv_p: expS1p => expS1p.
  have nS1Q: [~: Q, 'Ohm_1(S)] \subset 'Ohm_1(S).
    rewrite commg_subr (char_norm_trans (Ohm_char 1 S)) ?normal_norm //.
    exact: p_maximal_normal pQ maxS.
  have S1x : x \in 'Ohm_1(S) by rewrite defS1 !inE -cycle_subG sxS xp1 /=.
  have S1yx : [~ y, x] \in 'Ohm_1(S) by rewrite (subsetP nS1Q) ?mem_commg.
  have S1yxx : [~ y, x, x] \in 'Ohm_1(S) by rewrite groupR.
  have S1yxy : [~ y, x, y] \in 'Ohm_1(S).
    by rewrite -invg_comm groupV (subsetP nS1Q) 1?mem_commg.
  rewrite expMR_fg ?(subsetP sQR) //= xp1 yp1 expS1p ?mul1g //.
  case: (leqP p 3) => [p_le3 | p_gt3]; last by rewrite ?expS1p ?mul1g; auto.
  by rewrite !p3_L21 // ?(subsetP sQR) // !expg1n mulg1.
split=> // sR'R1 x y Rx Ry; rewrite -[x ^+ p * _]mulg1 expMR_fg // -2!mulgA //.
have expR'p := exp_dv_p _ _ _ (dvdn_trans (exponentS sR'R1) expR1p).
congr (_ * _); rewrite expR'p ?mem_commg // mul1g.
case: (leqP p 3) => [p_le3 | p_gt3].
  by rewrite !p3_L21 // ?(subsetP sQR) // !expg1n mulg1.
by rewrite !expR'p 1?mem_commg ?groupR ?mulg1; auto.
Qed.

(* Part (a) of B & G, Proposition 4.4 is covered in file maximal.v by lemmas  *)
(* max_SCN and SCN_max.                                                       *)

(* This is B & G, Proposition 4.4(b), or Gorenstein 7.6.5. *)
Proposition SCN_Sylow_cent_dprod gT (R G A : {group gT}) p :
  p.-Sylow(G) R -> A \in 'SCN(R) -> 'O_p^'('C_G(A)) \x A = 'C_G(A).
Proof.
move=> sylR scnA; have [[sRG _] [nAR CRA_A]] := (andP sylR, SCN_P scnA).
set C := 'C_G(A); have /maxgroupP[/andP[nAG abelA] maxA] := SCN_max scnA.
have CiP_eq : C :&: R = A by rewrite -CRA_A setIC setIA (setIidPl sRG).
have sylA: p.-Sylow(C) A.
  rewrite -CiP_eq; apply: (Sylow_setI_normal (subcent_normal _ _)).
  by apply: pHall_subl sylR; rewrite ?subsetIl // subsetI sRG normal_norm.
rewrite dprodEsd; last first.
  by rewrite centsC (subset_trans (pcore_sub _ _)) ?subsetIr.
by apply: Burnside_normal_complement; rewrite // subIset ?subsetIr.
Qed.

(* This is B & G, Lemma 4.5(b), or Gorenstein, 5.4.4 and 5.5.5. *)
Lemma Ohm1_extremal_odd gT (R : {group gT}) p x :
    p.-group R -> odd #|R| -> ~~ cyclic R -> x \in R -> #|R : <[x]>| = p ->
  ('Ohm_1(R))%G \in 'E_p^2(R).
Proof.
move=> pR oddR ncycR Rx ixR; rewrite -cycle_subG in Rx.
have ntR: R :!=: 1 by apply: contra ncycR; move/eqP->; exact: cyclic1.
have [p_pr _ [e oR]]:= pgroup_pdiv pR ntR.
case p2: (p == 2); first by rewrite oR odd_exp (eqP p2) in oddR.
have [cRR | not_cRR] := orP (orbN (abelian R)).
  rewrite 2!inE Ohm_sub Ohm1_abelem // -p_rank_abelian //= eqn_leq.
  rewrite -rank_pgroup // ltnNge -abelian_rank1_cyclic // ncycR andbT.
  have maxX: maximal <[x]> R by rewrite (p_index_maximal Rx) ?ixR.
  have nsXR: <[x]> <| R := p_maximal_normal pR maxX.
  have [_ [y Ry notXy]] := properP (maxgroupp maxX).
  have defR: <[x]> * <[y]> = R.
    by apply: mulg_normal_maximal; rewrite ?cycle_subG.
  rewrite -grank_abelian // -(genGid R) -defR genM_join joing_idl joing_idr.
  by rewrite (leq_trans (grank_min _)) // cards2 ltnS leq_b1.
have{x Rx ixR} [e_gt1 isoR]: 2 < e.+1 /\ R \isog 'Mod_(p ^ e.+1).
  have:= maximal_cycle_extremal pR not_cRR (cycle_cyclic x) Rx ixR.
  rewrite p2 orbF /extremal_class oR pfactorKpdiv // pdiv_pfactor //.
  by do 4!case: andP => //.
have [[x y] genR modR] := generators_modular_group p_pr e_gt1 isoR.
have [_ _ _ _] := modular_group_structure p_pr e_gt1 genR isoR modR.
rewrite xpair_eqE p2; case/(_ 1%N) => // _ oR1.
by rewrite 2!inE Ohm_sub oR1 pfactorK ?abelem_Ohm1 ?(card_p2group_abelian p_pr).
Qed.  

Section OddNonCyclic.

Variables (gT : finGroupType) (p : nat) (R : {group gT}).
Hypotheses (pR : p.-group R) (oddR : odd #|R|) (ncycR : ~~ cyclic R).

(* This is B & G, Lemma 4.5(a), or Gorenstein 5.4.10. *)
Lemma ex_odd_normal_p2Elem : {S : {group gT} | S <| R & S \in 'E_p^2(R)}.
Proof.
have [M minM]: {M | [min M | M <| R & ~~ cyclic M]}.
  by apply: ex_mingroup; exists R; rewrite normal_refl.
have{minM} [[nsMR ncycM] [_ minM]] := (andP (mingroupp minM), mingroupP minM).
have [sMR _] := andP nsMR; have pM := pgroupS sMR pR.
exists ('Ohm_1(M))%G; first exact: char_normal_trans (Ohm_char 1 M) nsMR.
apply: (subsetP (pnElemS _ _ sMR)).
have [M1 | ntM] := eqsVneq M 1; first by rewrite M1 cyclic1 in ncycM.
have{ntM} [p_pr _ [e oM]] := pgroup_pdiv pM ntM.
have le_e_M: e <= logn p #|M| by rewrite ltnW // oM pfactorK.
have{le_e_M} [N [sNM nsNR] oN] := normal_pgroup pR nsMR le_e_M.
have ltNM: ~~ (#|N| >= #|M|) by rewrite -ltnNge oM oN ltn_exp2l ?prime_gt1.
have cycN : cyclic N by apply: contraR ltNM => ncycN; rewrite minM //= nsNR.
case/cyclicP: cycN => x defN; have Mx : x \in M by rewrite -cycle_subG -defN.
apply: Ohm1_extremal_odd Mx _; rewrite ?(oddSg sMR) //.
by rewrite -divgS /= -defN // oM oN expnS mulnK // expn_gt0 prime_gt0.
Qed.

(* This is B & G, Lemma 4.5(c). *)
Lemma Ohm1_odd_ucn2 (Z := 'Ohm_1('Z_2(R))) : ~~ cyclic Z /\ exponent Z %| p.
Proof. 
have [S nsSR Ep2S] := ex_odd_normal_p2Elem; have p_pr := pnElem_prime Ep2S.
have [sSR abelS dimS] := pnElemP Ep2S; have [pS cSS expSp]:= and3P abelS.
pose SR := [~: S, R]; pose SRR := [~: SR, R].
have nilR := pgroup_nil pR.
have ntS: S :!=: 1 by rewrite -rank_gt0 (rank_abelem abelS) dimS.
have sSR_S: SR \subset S by rewrite commg_subl normal_norm.
have sSRR_SR: SRR \subset SR by rewrite commSg.
have sSR_R := subset_trans sSR_S sSR.
have{ntS} prSR: SR \proper S.
  by rewrite (nil_comm_properl nilR) // subsetI subxx -commg_subl.
have SRR1: SRR = 1.
  have [SR1 | ntSR] := eqVneq SR 1; first by rewrite /SRR SR1 comm1G. 
  have prSRR: SRR \proper SR.
    rewrite /proper sSRR_SR; apply: contra ntSR => sSR_SRR.
    by rewrite (forall_inP nilR) // subsetI sSR_R.
  have pSR := pgroupS sSR_R pR; have pSRR := pgroupS sSRR_SR pSR.
  have [_ _ [e oSR]] := pgroup_pdiv pSR ntSR; have [f oSRR] := p_natP pSRR.
  have e0: e = 0.
    have:= proper_card prSR; rewrite oSR (card_pnElem Ep2S).
    by rewrite ltn_exp2l ?prime_gt1 // !ltnS leqn0; move/eqP.
  apply/eqP; have:= proper_card prSRR; rewrite trivg_card1 oSR oSRR e0.
  by rewrite ltn_exp2l ?prime_gt1 // ltnS; case f.
have sSR_ZR: [~: S, R] \subset 'Z(R).
  by rewrite subsetI sSR_R /=; apply/commG1P.
have sS_Z2R: S \subset 'Z_2(R).
  rewrite ucnSnR; apply/subsetP=> s Ss; rewrite inE (subsetP sSR) //= ucn1.
  by rewrite (subset_trans _ sSR_ZR) ?commSg ?sub1set.
have sZ2R_R := ucn_sub 2 R; have pZ2R := pgroupS sZ2R_R pR.
have pZ: p.-group Z. 
  apply: pgroupS pR; apply: subset_trans (Ohm_sub _ _) (ucn_sub 2 R).
have sSZ: S \subset Z.
  by rewrite /Z (OhmE 1 pZ2R) sub_gen // subsetI sS_Z2R sub_LdivT.
have ncycX: ~~ cyclic S by rewrite (abelem_cyclic abelS) dimS.
split; first by apply: contra ncycX; exact: cyclicS.
have nclZ2R : nil_class 'Z_2(R) <= 2 + _ := leq_trans (nil_class_ucn _ _) _.
by have [] := exponent_odd_nil23 pZ2R (oddSg sZ2R_R oddR) (nclZ2R _ _).
Qed.

End OddNonCyclic.

(* Some "obvious" consequences of the above, which are used casually and      *)
(* pervasively throughout B & G.                                              *)
Definition odd_pgroup_rank1_cyclic := odd_pgroup_rank1_cyclic. (* in extremal *)

Lemma odd_rank1_Zgroup gT (G : {group gT}) :
  odd #|G| -> Zgroup G = ('r(G) <= 1).
Proof.
move=> oddG; apply/forallP/idP=> [ZgG | rG_1 P].
  have [p p_pr ->]:= rank_witness G; have [P sylP]:= Sylow_exists p G.
  have [sPG pP _] := and3P sylP; have oddP := oddSg sPG oddG.
  rewrite -(p_rank_Sylow sylP) -(odd_pgroup_rank1_cyclic pP) //.
  by apply: (implyP (ZgG P)); apply: (p_Sylow sylP).
apply/implyP=> /SylowP[p p_pr /and3P[sPG pP _]].
rewrite (odd_pgroup_rank1_cyclic pP (oddSg sPG oddG)).
by apply: leq_trans (leq_trans (p_rank_le_rank p G) rG_1); apply: p_rankS.
Qed.

(* This is B & G, Proposition 4.6 (a stronger version of Lemma 4.5(a)). *)
Proposition odd_normal_p2Elem_exists gT p (R S : {group gT}) :
    p.-group R -> odd #|R| -> S <| R -> ~~ cyclic S ->
  exists E : {group gT}, [/\ E \subset S, E <| R & E \in 'E_p^2(R)].
Proof.
move=> pR oddR nsSR ncycS; have sSR := normal_sub nsSR.
have{sSR ncycS} []:= Ohm1_odd_ucn2 (pgroupS sSR pR) (oddSg sSR oddR) ncycS.
set Z := 'Ohm_1(_) => ncycZ expZp.
have chZS: Z \char S := char_trans (Ohm_char 1 _) (ucn_char 2 S).
have{nsSR} nsZR: Z <| R := char_normal_trans chZS nsSR.
have [sZR _] := andP nsZR; have pZ: p.-group Z := pgroupS sZR pR.
have geZ2: 2 <= logn p #|Z|.
  rewrite (odd_pgroup_rank1_cyclic pZ (oddSg sZR oddR)) -ltnNge /= -/Z in ncycZ.
  by case/p_rank_geP: ncycZ => E; case/pnElemP=> sEZ _ <-; rewrite lognSg.
have [E [sEZ nsER oE]] := normal_pgroup pR nsZR geZ2.
have [sER _] := andP nsER; have{pR} pE := pgroupS sER pR.
have{geZ2} p_pr: prime p by move: geZ2; rewrite lognE; case: (prime p).
have{oE p_pr} dimE2: logn p #|E| = 2 by rewrite oE pfactorK.
exists E; split; rewrite ?(subset_trans _ (char_sub chZS)) {chZS nsZR}//.
rewrite !inE /abelem sER pE (p2group_abelian pE) dimE2 //= andbT.
by apply: (dvdn_trans _ expZp); apply: exponentS.
Qed.

(* This is B & G, Lemma 4.7, and (except for the trivial converse) Gorenstein *)
(* 5.4.15 and Aschbacher 23.17.                                               *)
Lemma rank2_SCN3_empty gT p (R : {group gT}) :
  p.-group R -> odd #|R| -> ('r(R) <= 2) = ('SCN_3(R) == set0).
Proof.
move=> pR oddR; apply/idP/idP=> [leR2 | SCN_3_empty].
  apply/set0Pn=> [[A /setIdP[/SCN_P[/andP[sAR _] _]]]].
  by rewrite ltnNge (leq_trans (rankS sAR)).
rewrite (rank_pgroup pR) leqNgt; apply/negP=> gtR2.
have ncycR: ~~ cyclic R by rewrite (odd_pgroup_rank1_cyclic pR) // -ltnNge ltnW.
have{ncycR} [Z nsZR] := ex_odd_normal_p2Elem pR oddR ncycR.
case/pnElemP=> sZR abelZ dimZ2; have [pZ cZZ _] := and3P abelZ.
have{SCN_3_empty} defZ: 'Ohm_1('C_R(Z)) = Z.
  apply: (Ohm1_cent_max_normal_abelem _ pR).
    by have:= oddSg sZR oddR; rewrite (card_pgroup pZ) dimZ2 odd_exp.
  apply/maxgroupP; split=> [|H /andP[nsHR abelH] sZH]; first exact/andP.
  have [pH cHH _] := and3P abelH; apply/eqP; rewrite eq_sym eqEproper sZH /=.
  pose normal_abelian := [pred K : {group gT} | K <| R & abelian K].
  have [|K maxK sHK] := @maxgroup_exists _ normal_abelian H; first exact/andP.
  apply: contraL SCN_3_empty => ltZR; apply/set0Pn; exists K.
  rewrite inE (max_SCN pR) {maxK}//= -dimZ2 (leq_trans _ (rankS sHK)) //.
  by rewrite (rank_abelem abelH) properG_ltn_log.
have{gtR2} [A] := p_rank_geP gtR2; pose H := 'C_A(Z); pose K := H <*> Z.
case/pnElemP=> sAR abelA dimA3; have [pA cAA _] := and3P abelA.
have{nsZR} nZA := subset_trans sAR (normal_norm nsZR).
have sHA: H \subset A := subsetIl A _; have abelH := abelemS sHA abelA.
have geH2: logn p #|H| >= 2. 
  rewrite -ltnS -dimA3 -(Lagrange sHA) lognM // -addn1 leq_add2l /= -/H.
  by rewrite logn_quotient_cent_abelem ?dimZ2.
have{abelH} abelK : p.-abelem K.
  by rewrite (cprod_abelem _ (cprodEY _)) 1?centsC ?subsetIr ?abelH.
suffices{sZR cZZ defZ}: 'r(Z) < 'r(K).
  by rewrite ltnNge -defZ rank_Ohm1 rankS // join_subG setSI // subsetI sZR.
rewrite !(@rank_abelem _ p) // properG_ltn_log ?abelem_pgroup //= -/K properE.
rewrite joing_subr join_subG subxx andbT subEproper; apply: contraL geH2.
case/predU1P=> [defH | ltHZ]; last by rewrite -ltnNge -dimZ2 properG_ltn_log.
rewrite -defH [H](setIidPl _) ?dimA3 // in dimZ2.
by rewrite centsC -defH subIset // -abelianE cAA.
Qed.

(* This is B & G, Proposition 4.8(a). *)
Proposition rank2_exponent_p_p3group gT (R : {group gT}) p :
  p.-group R -> rank R <= 2 -> exponent R %| p -> logn p #|R| <= 3.
Proof.
move=> pR rankR expR.
have [A max_na_A]: {A | [max A | A <| R & abelian A]}.
  by apply: ex_maxgroup; exists 1%G; rewrite normal1 abelian1.
have {max_na_A} SCN_A := max_SCN pR max_na_A.
have cAA := SCN_abelian SCN_A; case/SCN_P: SCN_A => nAR cRAA.
have sAR := normal_sub nAR; have pA := pgroupS sAR pR.
have abelA : p.-abelem A.
  by rewrite /abelem pA cAA /= (dvdn_trans (exponentS sAR) expR).
have cardA : logn p #|A| <= 2.
  by rewrite -rank_abelem // (leq_trans (rankS sAR) rankR). 
have cardRA : logn p #|R : A| <= 1.
  by rewrite -cRAA logn_quotient_cent_abelem // (normal_norm nAR).
rewrite -(Lagrange sAR) lognM ?cardG_gt0 //.
by apply: (leq_trans (leq_add cardA cardRA)).
Qed.

(* This is B & G, Proposition 4.8(b). *)
Proposition exponent_Ohm1_rank2 gT p (R : {group gT}) :
  p.-group R -> 'r(R) <= 2 -> p > 3 -> exponent 'Ohm_1(R) %| p.
Proof.
move=> pR rR p_gt3; wlog p_pr: / prime p.
  have [-> | ntR] := eqsVneq R 1; first by rewrite Ohm1 exponent1 dvd1n.
  by apply; have [->] := pgroup_pdiv pR ntR.
wlog minR: R pR rR / forall S, gval S \proper R -> exponent 'Ohm_1(S) %| p.
  elim: {R}_.+1 {-2}R (ltnSn #|R|) => // m IHm R leRm in pR rR * => IH.
  apply: (IH) => // S; rewrite properEcard; case/andP=> sSR ltSR.
  exact: IHm (leq_trans ltSR _) (pgroupS sSR pR) (leq_trans (rankS sSR) rR) IH.
wlog not_clR_le3: / ~~ (nil_class R <= 3).
  case: leqP => [clR_le3 _ | _ -> //].
  have [||-> //] := exponent_odd_nil23 pR; last by rewrite p_gt3.
  by apply: odd_pgroup_odd pR; case/even_prime: p_pr p_gt3 => ->.
rewrite -sub_LdivT (OhmE 1 pR) gen_set_id ?subsetIr //.
apply/group_setP; rewrite !inE group1 expg1n.
split=> //= x y; case/LdivP=> Rx xp1; case/LdivP=> Ry yp1.
rewrite !inE groupM //=; apply: contraR not_clR_le3 => nt_xyp.
pose XY := <[x]> <*> <[y]>.
have [XYx XYy]: x \in XY /\ y \in XY by rewrite -!cycle_subG; exact/joing_subP.
have{nt_xyp} defR: XY = R.
  have sXY_R : XY \subset R by rewrite join_subG !cycle_subG Rx Ry.
  have pXY := pgroupS sXY_R pR; have [// | ltXY_R] := eqVproper sXY_R.
  rewrite (exponentP (minR _ ltXY_R)) ?eqxx // in nt_xyp.
  by rewrite (OhmE 1 pXY) groupM ?mem_gen ?inE ?XYx ?XYy /= ?xp1 ?yp1.
have sXR: <[x]> \subset R by rewrite cycle_subG.
have [<- | ltXR] := eqVproper sXR.
  by rewrite 2?leqW // nil_class1 cycle_abelian.
have [S maxS sXS]: {S : {group gT} | maximal S R & <[x]> \subset S}.
  exact: maxgroup_exists.
have nsSR: S <| R := p_maximal_normal pR maxS; have [sSR _] := andP nsSR.
have{nsSR} nsS1R: 'Ohm_1(S) <| R := char_normal_trans (Ohm_char 1 S) nsSR.
have [sS1R nS1R] := andP nsS1R; have pS1 := pgroupS sS1R pR.
have expS1p: exponent 'Ohm_1(S) %| p := minR S (maxgroupp maxS).
have{expS1p} dimS1: logn p #|'Ohm_1(S)| <= 3.
  exact: rank2_exponent_p_p3group pS1 (leq_trans (rankS sS1R) rR) expS1p.
have sXS1: <[x]> \subset 'Ohm_1(S).
  rewrite cycle_subG /= (OhmE 1 (pgroupS sSR pR)) mem_gen //.
  by rewrite !inE -cycle_subG sXS xp1 /=.
have dimS1b: logn p #|R / 'Ohm_1(S)| <= 1.
  rewrite -quotientYidl // -defR joingA (joing_idPl sXS1).
  rewrite quotientYidl ?cycle_subG ?(subsetP nS1R) //.
  rewrite (leq_trans (logn_quotient _ _ _)) // -(pfactorK 1 p_pr).
  by rewrite dvdn_leq_log ?prime_gt0 // order_dvdn yp1.
rewrite (leq_trans (nil_class_pgroup pR)) // geq_max /= -subn1 leq_subLR.
by rewrite -(Lagrange sS1R) lognM // -card_quotient // addnC leq_add.
Qed. 

(* This is B & G, Lemma 4.9. *)
Lemma quotient_p2_Ohm1 gT p (R : {group gT}) :
    p.-group R -> p > 3 -> logn p #|'Ohm_1(R)| <= 2 ->
  forall T : {group gT}, T <| R -> logn p #|'Ohm_1(R / T)| <= 2.
Proof.
move=> pR p_gt3 dimR1; move: {2}_.+1 (ltnSn #|R|) => n.
elim: n => // n IHn in gT R pR dimR1 *; rewrite ltnS => leRn.
apply/forall_inP/idPn; rewrite negb_forall_in.
case/existsP/ex_mingroup=> T /mingroupP[/andP[nsTR dimRb1] minT].
have [sTR nTR] := andP nsTR; have pT: p.-group T := pgroupS sTR pR.
pose card_iso_Ohm := card_isog (gFisog [igFun of Ohm 1] _).
have ntT: T :!=: 1; last have p_pr: prime p by have [] := pgroup_pdiv pT ntT.
  apply: contraNneq dimRb1 => ->.
  by rewrite -(card_iso_Ohm _ _ _ _ (quotient1_isog R)).
have{minT} dimT: logn p #|T| = 1%N.
  have [Z EpZ]: exists Z, Z \in 'E_p^1(T :&: 'Z(R)).
    apply/p_rank_geP; rewrite -rank_pgroup ?(pgroupS (subsetIl T _)) //.
    by rewrite rank_gt0 (meet_center_nil (pgroup_nil pR)).
  have [sZ_ZT _ dimZ] := pnElemP EpZ; have [sZT sZZ] := subsetIP sZ_ZT.
  have{sZZ} nsZR: Z <| R := sub_center_normal sZZ.
  rewrite -(minT Z) // nsZR; apply: contra dimRb1 => dimRz1.
  rewrite -(card_iso_Ohm _ _ _ _ (third_isog sZT nsZR nsTR)) /=.
  rewrite IHn ?quotient_pgroup ?quotient_normal ?(leq_trans _ leRn) //.
  by rewrite ltn_quotient ?(subset_trans sZT) // (nt_pnElem EpZ).
have pRb: p.-group (R / T) by apply: quotient_pgroup.
have{IHn} minR (Ub : {group coset_of T}):
  Ub \subset R / T -> ~~ (logn p #|'Ohm_1(Ub)| <= 2) -> R / T = Ub.
- case/inv_quotientS=> // U -> sTU sUR dimUb; congr (_ / T).
  apply/eqP; rewrite eq_sym eqEcard sUR leqNgt; apply: contra dimUb => ltUR.
  rewrite IHn ?(pgroupS sUR) ?(normalS _ sUR) ?(leq_trans ltUR) //.
  by rewrite (leq_trans _ dimR1) ?lognSg ?OhmS.
have [dimRb eRb]: logn p #|R / T| = 3 /\ exponent (R / T) %| p.
  have [Rb_gt2 | Rb_le2] := ltnP 2 'r_p(R / T).
    have [Ub Ep3Ub] := p_rank_geP Rb_gt2.
    have [sUbR abelUb dimUb] := pnElemP Ep3Ub; have [_ _ eUb] := and3P abelUb.
    by rewrite (minR Ub) // (Ohm1_id abelUb) dimUb.
  rewrite -rank_pgroup // in Rb_le2.
  have eRb: exponent (R / T) %| p.
    by rewrite (minR _ (Ohm_sub 1 _)) ?exponent_Ohm1_rank2 ?Ohm_id.
  split=> //; apply/eqP; rewrite eqn_leq rank2_exponent_p_p3group // ltnNge.
  by apply: contra (leq_trans _) dimRb1; rewrite lognSg ?Ohm_sub.
have ntRb: (R / T) != 1.
  by rewrite -cardG_gt1 (card_pgroup pRb) dimRb (ltn_exp2l 0) ?prime_gt1.
have{dimRb} dimR: logn p #|R| = 4.
  by rewrite -(Lagrange sTR) lognM ?cardG_gt0 // dimT -card_quotient ?dimRb.
have nsR1R: 'Ohm_1(R) <| R := Ohm_normal 1 R; have [sR1R nR1R] := andP nsR1R.
have pR1: p.-group 'Ohm_1(R) := pgroupS sR1R pR.
have p_odd: odd p by case/even_prime: p_pr p_gt3 => ->.
have{p_odd} oddR: odd #|R| := odd_pgroup_odd p_odd pR.
have{dimR1} dimR1: logn p #|'Ohm_1(R)| = 2.
  apply/eqP; rewrite eqn_leq dimR1 -p_rank_abelem; last first.
    by rewrite abelem_Ohm1 // (p2group_abelian pR1).
  rewrite ltnNge p_rank_Ohm1 -odd_pgroup_rank1_cyclic //.
  apply: contra dimRb1 => cycR; have cycRb := quotient_cyclic T cycR.
  by rewrite (Ohm1_cyclic_pgroup_prime cycRb pRb ntRb) (pfactorK 1).
have pRs: p.-group (R / 'Ohm_1(R)) by rewrite quotient_pgroup.
have dimRs: logn p #|R / 'Ohm_1(R)| = 2.
  by rewrite -divg_normal // logn_div ?cardSg // dimR1 dimR.
have sR'R1: R^`(1) \subset 'Ohm_1(R).
  by rewrite der1_min // (p2group_abelian pRs) ?dimRs.
have [|_ phiM] := exponent_odd_nil23 pR oddR.
  by rewrite (leq_trans (nil_class_pgroup pR)) // dimR p_gt3.
pose phi := Morphism (phiM sR'R1).
suffices: logn p #|R / 'Ohm_1(R)| <= logn p #|T| by rewrite dimT dimRs.
have ->: 'Ohm_1(R) = 'ker phi.
  rewrite -['ker phi]genGid (OhmE 1 pR); congr <<_>>.
  by apply/setP=> x; rewrite !inE.
rewrite (card_isog (first_isog phi)) lognSg //=.
apply/subsetP=> _ /morphimP[x _ Rx ->] /=.
apply: coset_idr; first by rewrite groupX ?(subsetP nTR).
by rewrite morphX ?(subsetP nTR) // (exponentP eRb) // mem_quotient.
Qed.

(* This is B & G, Lemma 4.10. *)
Lemma Ohm1_metacyclic_p2Elem gT p (R : {group gT}) :
    metacyclic R -> p.-group R -> odd #|R| -> ~~ cyclic R -> 
  'Ohm_1(R)%G \in 'E_p^2(R).
Proof.
case/metacyclicP=> S [cycS nsSR cycRb] pR oddR ncycR.
have [[sSR nSR] [s defS]] := (andP nsSR, cyclicP cycS).
have [T defTb sST sTR] := inv_quotientS nsSR (Ohm_sub 1 (R / S)).
have [pT oddT] := (pgroupS sTR pR, oddSg sTR oddR).
have Ts: s \in T by rewrite -cycle_subG -defS.
have iTs: #|T : <[s]>| = p.
  rewrite -defS -card_quotient ?(subset_trans sTR) // -defTb.
  rewrite (Ohm1_cyclic_pgroup_prime cycRb (quotient_pgroup _ pR)) // -subG1.
  by rewrite quotient_sub1 ?(contra (fun sRS => cyclicS sRS cycS)).
have defR1: 'Ohm_1(R) = 'Ohm_1(T).
  apply/eqP; rewrite eqEsubset (OhmS _ sTR) andbT -Ohm_id OhmS //.
  rewrite -(quotientSGK _ sST); last by rewrite (subset_trans _ nSR) ?Ohm_sub.
  by rewrite -defTb morphim_Ohm.
rewrite (subsetP (pnElemS _ _ sTR)) // (group_inj defR1).
apply: Ohm1_extremal_odd iTs => //; apply: contra ncycR.
by rewrite !(@odd_pgroup_rank1_cyclic _ p) // -p_rank_Ohm1 -defR1 p_rank_Ohm1.
Qed.

(* This is B & G, Proposition 4.11 (due to Huppert). *)
Proposition p2_Ohm1_metacyclic gT p (R : {group gT}) :
  p.-group R -> p > 3 -> logn p #|'Ohm_1(R)| <= 2 -> metacyclic R.
Proof.
move=> pR p_gt3 dimR1; move: {2}_.+1 (ltnSn #|R|) => n.
elim: n => // n IHn in gT R pR dimR1 *; rewrite ltnS => leRn.
have pR1: p.-group 'Ohm_1(R) := pgroupS (Ohm_sub 1 R) pR.
have [cRR | not_cRR] := boolP (abelian R).
  have [b defR typeR] := abelian_structure cRR; move: dimR1 defR.
  rewrite -(rank_abelian_pgroup pR cRR) -(size_abelian_type cRR) -{}typeR.
  case: b => [|a [|b []]] //= _; first by move <-; rewrite big_nil metacyclic1.
    by rewrite big_seq1 => <-; rewrite cyclic_metacyclic ?cycle_cyclic.
  rewrite big_cons big_seq1; case/dprodP=> _ <- cAB _.
  apply/existsP; exists <[a]>%G; rewrite cycle_cyclic /=.
  rewrite /normal mulG_subl mulG_subG normG cents_norm //= quotientMidl. 
  by rewrite quotient_cycle ?cycle_cyclic // -cycle_subG cents_norm.
pose R' := R^`(1); pose e := 'Mho^1(R') != 1.
have nsR'R: R' <| R := der_normal 1 R; have [sR'R nR'R] := andP nsR'R.
have [T EpT]: exists T, T \in 'E_p^1('Mho^e(R') :&: 'Z(R)).
  apply/p_rank_geP; rewrite -rank_pgroup; last first.
    by rewrite (pgroupS _ pR) //= setIC subIset ?center_sub.
  rewrite rank_gt0 (meet_center_nil (pgroup_nil pR)) //.
    exact: char_normal_trans (Mho_char e _) nsR'R.
  by case ntR'1: e; rewrite //= Mho0 (sameP eqP derG1P).
have [p_gt1 p_pr] := (ltnW (ltnW p_gt3), pnElem_prime EpT).
have p_odd: odd p by case/even_prime: p_pr p_gt3 => ->.
have{p_odd} oddR: odd #|R| := odd_pgroup_odd p_odd pR.
have [sTR'eZ abelT oT] := pnElemPcard EpT; rewrite expn1 in oT.
have{sTR'eZ abelT} [[sTR'e sTZ] [pT cTT eT]] := (subsetIP sTR'eZ, and3P abelT).
have sTR': T \subset R' := subset_trans sTR'e (Mho_sub e _).
have nsTR := sub_center_normal sTZ; have [sTR cRT] := subsetIP sTZ.
have cTR: R \subset 'C(T) by rewrite centsC.
have{n IHn leRn EpT} metaRb: metacyclic (R / T).
  have pRb: p.-group (R / T) := quotient_pgroup T pR.
  have dimRb: logn p #|'Ohm_1(R / T)| <= 2 by apply: quotient_p2_Ohm1.
  by rewrite IHn ?(leq_trans (ltn_quotient _ _)) ?(nt_pnElem EpT).
have{metaRb} [Xb [cycXb nsXbR cycRs]] := metacyclicP metaRb.
have{cycRs} [yb defRb]: exists yb, R / T = Xb <*> <[yb]>.
  have [ys defRs] := cyclicP cycRs; have [yb nXyb def_ys] := cosetP ys.
  exists yb; rewrite -quotientYK ?cycle_subG ?quotient_cycle // -def_ys -defRs.
  by rewrite quotientGK.
have{sTZ} ntXb: Xb :!=: 1.
  apply: contraNneq not_cRR => Xb1.
  by rewrite (cyclic_factor_abelian sTZ) // defRb Xb1 joing1G cycle_cyclic.
have [TX defTXb sTTX nsTXR] := inv_quotientN nsTR nsXbR.
have{cycXb} [[sTXR nTXR] [xb defXb]] := (andP nsTXR, cyclicP cycXb).
have [[x nTx def_xb] [y nTy def_yb]] := (cosetP xb, cosetP yb).
have{defTXb} defTX: T <*> <[x]> = TX.
  rewrite -quotientYK ?cycle_subG ?quotient_cycle // -def_xb -defXb defTXb.
  by rewrite quotientGK // (normalS _ sTXR).
have{yb defRb def_yb} defR: TX <*> <[y]> = R.
  rewrite -defTX -joingA -quotientYK ?join_subG ?quotientY ?cycle_subG ?nTx //.
  by rewrite !quotient_cycle // -def_xb -def_yb -defXb -defRb quotientGK.
have sXYR: <[x]> <*> <[y]> \subset R by rewrite -defR -defTX -joingA joing_subr.
have [Rx Ry]: x \in R /\ y \in R by rewrite -!cycle_subG; exact/joing_subP.
have cTXY := subset_trans sXYR cTR; have [cTX cTY] := joing_subP cTXY.
have [R'1_1 {e sTR'e} | ntR'1] := eqVneq 'Mho^1(R') 1; last first.
  have sR'TX: R' \subset TX.
    rewrite der1_min // -defR quotientYidl ?cycle_subG ?(subsetP nTXR) //.
    by rewrite quotient_abelian // cycle_abelian.
  have sTX : T \subset <[x]>.
    rewrite (subset_trans (subset_trans sTR'e (MhoS e sR'TX))) // /e ntR'1.
    have{defTX} defTX: T \* <[x]> = TX by rewrite cprodEY // centsC.
    rewrite -(Mho_cprod 1 defTX) ['Mho^1(_)](trivgP _) ?cprod1g ?Mho_sub //=.
    rewrite (MhoE 1 pT) gen_subG; apply/subsetP=> tp; case/imsetP=> t Tt ->{tp}.
    by rewrite inE (exponentP eT).
  apply/metacyclicP; exists TX; split=> //.
    by rewrite -defTX (joing_idPr sTX) cycle_cyclic.
  rewrite -defR quotientYidl ?cycle_subG ?(subsetP nTXR) //.
  by rewrite quotient_cyclic ?cycle_cyclic.
have{R'1_1} eR': exponent R' %| p.
  have <-: 'Ohm_1(R') = R' by apply/eqP; rewrite trivg_Mho ?R'1_1.
  rewrite -sub_LdivT (OhmEabelian (pgroupS sR'R pR)) ?subsetIr //.
  by rewrite (abelianS (OhmS 1 sR'R)) // (p2group_abelian pR1).
pose r := [~ x, y]; have Rr: r \in R by exact: groupR.
have{defXb ntXb nsXbR} [i def_rb]: exists i, coset T r = (xb ^+ p) ^+ i.
  have p_xb: p.-elt xb by rewrite def_xb morph_p_elt ?(mem_p_elt pR).
  have pRbb: p.-group (R / T / 'Mho^1(Xb)) by rewrite !quotient_pgroup.
  have [_ nXb1R] := andP (char_normal_trans (Mho_char 1 Xb) nsXbR).
  apply/cycleP; rewrite -(Mho_p_cycle 1 p_xb) -defXb.
  apply: coset_idr; first by rewrite (subsetP nXb1R) ?mem_quotient.
  apply/eqP; rewrite !morphR ?(subsetP nXb1R) ?mem_quotient //=; apply/commgP.
  red; rewrite -(@centerC _ (R / T / _)) ?mem_quotient // -cycle_subG.
  rewrite -quotient_cycle ?(subsetP nXb1R) ?mem_quotient // -def_xb -defXb.
  suffices oXbb: #|Xb / 'Mho^1(Xb)| = p.
    apply: prime_meetG; first by rewrite oXbb.
    rewrite (meet_center_nil (pgroup_nil pRbb)) ?quotient_normal //.
    by rewrite -cardG_gt1 oXbb.
  rewrite -divg_normal ?Mho_normal //= defXb.
  rewrite -(mul_card_Ohm_Mho_abelian 1) ?cycle_abelian ?mulnK ?cardG_gt0 //.
  by rewrite (Ohm1_cyclic_pgroup_prime _ p_xb) ?cycle_cyclic //= -defXb.
have{xb def_xb def_rb} [t Tt def_r]: exists2 t, t \in T & r = t * x ^+ (p * i).
  apply/rcosetP; rewrite -val_coset ?groupX ?morphX //= -def_xb.
  by rewrite expgM -def_rb val_coset ?groupR // rcoset_refl.
have{eR' def_r cTT} defR': R' = <[r]>.
  have R'r : r \in R' by exact: mem_commg.
  have cxt: t \in 'C[x] by apply/cent1P; exact: (centsP cRT).
  have crx: x \in 'C[r] by rewrite cent1C def_r groupM ?groupX ?cent1id.
  have def_xy: x ^ y = t * x ^+ (p * i).+1.
    by rewrite conjg_mulR -/r def_r expgS !mulgA (cent1P cxt).
  have crR : R \subset 'C[r].
    rewrite -defR -defTX !join_subG sub_cent1 (subsetP cTR) //= !cycle_subG.
    rewrite crx cent1C (sameP cent1P commgP); apply/conjg_fixP.
    rewrite def_r conjMg conjXg conjgE (centsP cRT t) // mulKg conjg_mulR -/r.
    by rewrite (expgMn _ (cent1P crx)) (expgM r) (exponentP eR') ?expg1n ?mulg1.
  apply/eqP; rewrite eqEsubset cycle_subG R'r andbT.
  have nrR : R \subset 'N(<[r]>) by rewrite cents_norm ?cent_cycle.
  rewrite der1_min // -defR -defTX -joingA.
  rewrite norm_joinEr ?(subset_trans sXYR) ?normal_norm //.
  rewrite quotientMl ?(subset_trans sTR) // abelianM quotient_abelian //=.
  rewrite quotient_cents //= -der1_joing_cycles ?der_abelian //.
  by rewrite -sub_cent1 (subset_trans sXYR).
have [S maxS sR'S] : {S | [max S | S \subset R & cyclic S] & R' \subset S}.
  by apply: maxgroup_exists; rewrite sR'R /= -/R' defR' cycle_cyclic.
case/maxgroupP: maxS; case/andP=> sSR cycS maxS.
have nsSR: S <| R := sub_der1_normal sR'S sSR; have [_ nSR] := andP nsSR.
apply/existsP; exists S; rewrite cycS nsSR //=.
suffices uniqRs1 Us: Us \in 'E_p^1(R / S) -> 'Ohm_1(R) / S = Us.
  have pRs: p.-group (R / S) := quotient_pgroup S pR.
  rewrite abelian_rank1_cyclic ?sub_der1_abelian ?(rank_pgroup pRs) // leqNgt.
  apply: contraFN (ltnn 1) => rRs; have [Us EpUs] := p_rank_geP (ltnW rRs).
  have [Vs EpVs] := p_rank_geP rRs; have [sVsR abelVs <-] := pnElemP EpVs.
  have [_ _ <-] := pnElemP EpUs; apply: lognSg; apply/subsetP=> vs Vvs.
  apply: wlog_neg => notUvs; rewrite -cycle_subG -(uniqRs1 _ EpUs).
  rewrite (uniqRs1 <[vs]>%G) ?p1ElemE // !inE cycle_subG (subsetP sVsR) //=.
  by rewrite -orderE (abelem_order_p abelVs Vvs (group1_contra notUvs)).
case/pnElemPcard; rewrite expn1 => sUsR _ oUs.
have [U defUs sSU sUR] := inv_quotientS nsSR sUsR.
have [cycU | {maxS} ncycU] := boolP (cyclic U).
  by rewrite -[p]oUs defUs (maxS U) ?sUR // trivg_quotient cards1 in p_gt1.
have EpU1: 'Ohm_1(U)%G \in 'E_p^2(U).
  have [u defS] := cyclicP cycS; rewrite defS cycle_subG in sSU.
  rewrite (Ohm1_extremal_odd (pgroupS sUR pR) (oddSg sUR oddR) _ sSU) //.
  by rewrite -defS -card_quotient -?defUs // (subset_trans sUR).
have defU1: 'Ohm_1(U) = 'Ohm_1(R).
  apply/eqP; rewrite eqEcard OhmS // (card_pnElem EpU1).
  by rewrite (card_pgroup pR1) leq_exp2l.
apply/eqP; rewrite eqEcard oUs defUs -{1}defU1 quotientS ?Ohm_sub //.
rewrite dvdn_leq ?cardG_gt0 //; case/pgroup_pdiv: (quotient_pgroup S pR1) => //.
rewrite -subG1 quotient_sub1 ?(subset_trans (Ohm_sub 1 R) nSR) //.
apply: contraL (cycS) => sR1S; rewrite abelian_rank1_cyclic ?cyclic_abelian //.
rewrite -ltnNge (rank_pgroup (pgroupS sSR pR)); apply/p_rank_geP.
by exists 'Ohm_1(U)%G; rewrite -(setIidPr sSU) pnElemI inE EpU1 inE /= defU1.
Qed.

(* This is B & G, Theorem 4.12 (also due to Huppert), for internal action. *)
Theorem coprime_metacyclic_cent_sdprod gT p (R A : {group gT}) :
    p.-group R -> odd #|R| -> metacyclic R -> p^'.-group A -> A \subset 'N(R) ->
    let T := [~: R, A] in let C := 'C_R(A) in
  [/\ (*a*) abelian T,
      (*b*) T ><| C = R
    & (*c*) ~~ abelian R -> T != 1 ->
            [/\ C != 1, cyclic T, cyclic C & R^`(1) \subset T]].
Proof.
move=> pR oddR metaR p'A nRA T C.
suffices{C T} cTT: abelian [~: R, A].
  have sTR: T \subset R by rewrite commg_subl.
  have nTR: R \subset 'N(T) by rewrite commg_norml.
  have coRA: coprime #|R| #|A| := pnat_coprime pR p'A.
  have solR: solvable R := pgroup_sol pR.
  have defR: T * C = R by rewrite coprime_cent_prod.
  have sCR: C \subset R := subsetIl _ _; have nTC := subset_trans sCR nTR.
  have tiTC: T :&: C = 1.
    have defTA: [~: T, A] = T by rewrite coprime_commGid.
    have coTA: coprime #|T| #|A| := coprimeSg sTR coRA.
    by rewrite setIA (setIidPl sTR) -defTA coprime_abel_cent_TI ?commg_normr.
  split=> // [|not_cRR ntT]; first by rewrite sdprodE.
  have ntC: C != 1 by apply: contraNneq not_cRR => C1; rewrite -defR C1 mulg1.
  suffices [cycT cycC]: cyclic T /\ cyclic C.
    split=> //; rewrite der1_min //= -/T -defR quotientMidl.
    by rewrite cyclic_abelian ?quotient_cyclic.
  have [pT pC]:  p.-group T /\ p.-group C by rewrite !(pgroupS _ pR).
  apply/andP; rewrite (odd_pgroup_rank1_cyclic pC (oddSg sCR oddR)).
  rewrite abelian_rank1_cyclic // -rank_pgroup //.
  rewrite -(geq_leqif (leqif_add (leqif_geq _) (leqif_geq _))) ?rank_gt0 //.
  have le_rTC_dimTC1: 'r(T) + 'r(C) <= logn p #|'Ohm_1(T) * 'Ohm_1(C)|.
    rewrite (rank_pgroup pC) -p_rank_Ohm1 (rank_abelian_pgroup pT cTT).
    rewrite TI_cardMg; last by apply/trivgP; rewrite -tiTC setISS ?Ohm_sub.
    by rewrite lognM ?cardG_gt0 // leq_add2l p_rank_le_logn.
  apply: leq_trans le_rTC_dimTC1 _; rewrite add1n.
  have ncycR: ~~ cyclic R by apply: contra not_cRR; apply: cyclic_abelian.
  have: 'Ohm_1(R)%G \in 'E_p^2(R) by apply: Ohm1_metacyclic_p2Elem.
  have nT1C1: 'Ohm_1(C) \subset 'N('Ohm_1(T)).
    by rewrite (subset_trans (Ohm_sub 1 _)) ?(char_norm_trans (Ohm_char 1 _)).
  by case/pnElemP=> _ _ <-; rewrite -norm_joinEr ?lognSg // join_subG !OhmS.
without loss defR: R pR oddR metaR nRA / [~: R, A] = R.
  set T := [~: R, A] => IH; have sTR: T \subset R by rewrite commg_subl.
  have defTA: [~: T, A] = T.
    by rewrite coprime_commGid ?(pgroup_sol pR) ?(pnat_coprime pR).
  rewrite -defTA IH ?(pgroupS sTR) ?(oddSg sTR) ?(metacyclicS sTR) //.
  exact: commg_normr.
rewrite defR; apply: wlog_neg => not_cRR.
have ncycR: ~~ cyclic R := contra (@cyclic_abelian _ R) not_cRR.
pose cycR_nA S := [&& cyclic S, S \subset R & A \subset 'N(S)].
have [S maxS sR'S] : {S | [max S | cycR_nA S] & R^`(1) \subset S}.
  apply: maxgroup_exists; rewrite {}/cycR_nA der_sub /=.
  rewrite (char_norm_trans (der_char 1 _)) // andbT.
  have [K [cycK nsKR cycKR]] := metacyclicP metaR.
  by rewrite (cyclicS _ cycK) // der1_min ?normal_norm // cyclic_abelian.
case/maxgroupP: maxS; case/and3P=> cycS sSR nSA maxS.
have ntS: S :!=: 1 by rewrite (subG1_contra sR'S) // (sameP eqP derG1P).
have nSR: R \subset 'N(S) := sub_der1_norm sR'S sSR.
have nsSR: S <| R by exact/andP.
have sSZ: S \subset 'Z(R).
  have sR_NS': R \subset 'N(S)^`(1) by rewrite -{1}defR commgSS.
  rewrite subsetI sSR centsC (subset_trans sR_NS') // der1_min ?cent_norm //=.
  rewrite -ker_conj_aut (isog_abelian (first_isog _)).
  by rewrite (abelianS (Aut_conj_aut _ _)) ?Aut_cyclic_abelian.
have cRbRb: abelian (R / S) by rewrite sub_der1_abelian.
have pRb: p.-group (R / S) := quotient_pgroup S pR.
pose R1 := 'Ohm_1(R); pose Rb1 := 'Ohm_1(R / S).
have [Xb]: exists2 Xb, R1 / S \x gval Xb = Rb1 & A / S \subset 'N(Xb).
  have MaschkeRb1 := Maschke_abelem (Ohm1_abelem pRb cRbRb).
  pose normOhm1 := (char_norm_trans (Ohm_char 1 _), quotient_norms S).
  by apply: MaschkeRb1; rewrite ?quotient_pgroup ?morphim_Ohm ?normOhm1.
case/dprodP=> _ defRb1 _ tiR1bX nXbA.
have sXbR: Xb \subset R / S.
  by apply: subset_trans (Ohm_sub 1 _); rewrite -defRb1 mulG_subr.
have{sXbR} [X defXb sSX sXR] := inv_quotientS nsSR sXbR.
have{nXbA nsSR} nXA: A \subset 'N(X).
  rewrite (subset_trans (mulG_subr S A)) // -quotientK //.
  by rewrite -(quotientGK (normalS sSX sXR nsSR)) -defXb morphpre_norms.
have{tiR1bX} cycX: cyclic X.
  have sX1_XR1: 'Ohm_1(X) \subset X :&: R1 by rewrite subsetI Ohm_sub OhmS.
  have cyc_sR := odd_pgroup_rank1_cyclic (pgroupS _ pR) (oddSg _ oddR).
  have:= cycS; rewrite !{}cyc_sR //; apply: leq_trans.
  rewrite -p_rank_Ohm1 p_rankS // (subset_trans sX1_XR1) //.
  rewrite -quotient_sub1 ?subIset ?(subset_trans sXR) //.
  by rewrite quotientGI // setIC -defXb tiR1bX.
rewrite (cyclic_factor_abelian sSZ) // abelian_rank1_cyclic //.
rewrite (rank_abelian_pgroup pRb cRbRb) -defRb1 defXb.
rewrite (maxS X) ?trivg_quotient ?mulg1 //; last exact/and3P.
have EpR1: 'Ohm_1(R)%G \in 'E_p^2(R) by exact: Ohm1_metacyclic_p2Elem.
have [sR1R _ dimR1] := pnElemP EpR1; have pR1 := pgroupS sR1R pR.
rewrite -(card_isog (second_isog _)) ?(subset_trans sR1R) // -ltnS -dimR1.
by rewrite (ltn_log_quotient pR1) ?subsetIr //= meet_Ohm1 // (setIidPl sSR).
Qed.

(* This covers B & G, Lemmas 4.13 and 4.14. *)
Lemma pi_Aut_rank2_pgroup gT p q (R : {group gT}) :
    p.-group R -> odd #|R| -> 'r(R) <= 2 -> q \in \pi(Aut R) -> q != p ->
  [/\ q %| (p ^ 2).-1, q < p & q %| p.+1./2 \/ q %| p.-1./2].
Proof.
move=> pR oddR rR q_Ar p'q; rewrite /= in q_Ar.
have [R1 | ntR] := eqsVneq R 1; first by rewrite R1 Aut1 cards1 in q_Ar.
have{ntR} [p_pr p_dv_R _] := pgroup_pdiv pR ntR.
have{oddR p_dv_R} [p_odd p_gt1] := (dvdn_odd p_dv_R oddR, prime_gt1 p_pr).
have{q_Ar} [q_pr q_dv_Ar]: prime q /\ q %| #|Aut R|.
  by move: q_Ar; rewrite mem_primes; case/and3P.
suffices q_dv_p2: q %| (p ^ 2).-1.
  have q_dv_p1: q %| p.+1./2 \/ q %| p.-1./2.
    apply/orP; have:= q_dv_p2; rewrite -subn1 (subn_sqr p 1).
    rewrite -[p]odd_double_half p_odd /= !doubleK addKn addn1 -doubleS -!mul2n.
    rewrite mulnC !Euclid_dvdM // dvdn_prime2 // -orbA; case: eqP => // -> _.
    by rewrite -Euclid_dvdM // /dvdn modn2 mulnC odd_mul andbN.
  have p_gt2: p > 2 by rewrite ltn_neqAle; case: eqP p_odd => // <-.
  have p1_ltp: p.+1./2 < p.
    by rewrite -divn2 ltn_divLR // muln2 -addnn -addn2 leq_add2l.
  split=> //; apply: leq_ltn_trans p1_ltp.
  move/orP: q_dv_p1; rewrite -(subnKC p_gt2) leqNgt.
  by apply: contraL => lt_p1q; rewrite negb_or !gtnNdvd // ltnW.
wlog{q_dv_Ar} [a oa nRa]: gT R pR rR / {a | #[a] = q & a \in 'N(R) :\: 'C(R)}.
  have [a Ar_a oa] := Cauchy q_pr q_dv_Ar.
  rewrite -(injm_rank (injm_sdpair1 [Aut R])) // in rR.
  move=> IH; apply: IH rR _; rewrite ?morphim_pgroup ?morphim_odd //.
  exists (sdpair2 [Aut R] a); rewrite ?(order_injm (injm_sdpair2 _)) //.
  rewrite inE (subsetP (im_sdpair_norm _)) ?mem_morphim //= andbT.
  apply: contraL (prime_gt1 q_pr) => cRa; rewrite -oa order_gt1 negbK.
  apply/eqP; apply: (eq_Aut Ar_a (group1 _)) => x Rx.
  by rewrite perm1 [a x](@astab_act _ _ _ [Aut R] R) ?astabEsd ?mem_morphpre.
move: {2}_.+1 (ltnSn #|R|) => n.
elim: n => // n IHn in gT a R pR rR nRa oa *; rewrite ltnS => leRn.
case recR: [exists (S : {group gT} | S \proper R), a \in 'N(S) :\: 'C(S)].
  have [S ltSR nSa] := exists_inP recR; rewrite properEcard in ltSR.
  have{ltSR} [sSR ltSR] := andP ltSR; have rS := leq_trans (rankS sSR) rR.
  by apply: IHn nSa oa _; rewrite ?(pgroupS sSR) ?(leq_trans ltSR).
do [rewrite inE -!cycle_subG orderE; set A := <[a]>] in nRa oa.
have{nRa oa} [[not_cRA nRA] oA] := (andP nRa, oa).
have coRA : coprime #|R| #|A| by rewrite oA (pnat_coprime pR) ?pnatE. 
have{recR} IH: forall S, gval S \proper R -> A \subset 'N(S) -> A \subset 'C(S).
  move=> S ltSR; rewrite !cycle_subG => nSa; apply: contraFT recR => not_cSa.
  by apply/exists_inP; exists S; rewrite // inE not_cSa nSa.
have defR1: 'Ohm_1(R) = R.
apply: contraNeq not_cRA; rewrite eqEproper Ohm_sub negbK => ltR1R.
  rewrite (coprime_odd_faithful_Ohm1 pR) ?IH ?(odd_pgroup_odd p_odd) //.
  by rewrite (char_norm_trans (Ohm_char 1 R)).
have defRA: [~: R, A] = R.
  apply: contraNeq not_cRA; rewrite eqEproper commg_subl nRA negbK => ltRAR.
  rewrite centsC; apply/setIidPl.
  rewrite -{2}(coprime_cent_prod nRA) ?(pgroup_sol pR) //.
  by rewrite mulSGid // subsetI commg_subl nRA centsC IH ?commg_normr.
have [cRR | not_cRR] := boolP (abelian R).
  rewrite -subn1 (subn_sqr p 1) Euclid_dvdM //.
  have abelR: p.-abelem R by rewrite -defR1 Ohm1_abelem.
  have ntR: R :!=: 1 by apply: contraNneq not_cRA => ->; apply: cents1.
  pose rAR := reprGLm (abelem_repr abelR ntR nRA).
  have:= cardSg (subsetT (rAR @* A)); rewrite card_GL ?card_Fp //.
  rewrite card_injm ?ker_reprGLm ?rker_abelem ?prime_TIg ?oA // unlock.
  rewrite Gauss_dvdr; last by rewrite coprime_expr ?prime_coprime ?dvdn_prime2.
  move: rR; rewrite -ltnS -[_ < _](mem_iota 0) !inE eqn0Ngt rank_gt0 ntR.
  rewrite (dim_abelemE abelR ntR) (rank_abelem abelR).
  do [case/pred2P=> ->; rewrite /= muln1] => [-> // | ].
  by rewrite (subn_sqr p 1) mulnA !Euclid_dvdM ?orbb.
have [[defPhi defR'] _]: special R /\ 'C_R(A) = 'Z(R).
  apply: (abelian_charsimple_special pR) => //.
  apply/bigcupsP=> S; case/andP=> charS cSS.
  rewrite centsC IH ?(char_norm_trans charS) // properEneq char_sub // andbT.
  by apply: contraNneq not_cRR => <-.
have ntZ: 'Z(R) != 1 by rewrite -defR' (sameP eqP derG1P).
have ltRbR: #|R / 'Z(R)| < #|R| by rewrite ltn_quotient ?center_sub.
have pRb: p.-group (R / 'Z(R)) by apply: quotient_pgroup.
have nAZ: A \subset 'N('Z(R)) by rewrite (char_norm_trans (center_char R)).
have defAb: A / 'Z(R) = <[coset _ a]> by rewrite quotient_cycle -?cycle_subG.
have oab: #[coset 'Z(R) a] = q.
  rewrite orderE -defAb -(card_isog (quotient_isog _ _)) //.
  by rewrite coprime_TIg ?(coprimeSg (center_sub R)).
have rRb: 'r(R / 'Z(R)) <= 2.
  rewrite (rank_pgroup pRb) (leq_trans (p_rank_le_logn _ _)) // -ltnS.
  apply: leq_trans (rank2_exponent_p_p3group pR rR _).
    by rewrite -(ltn_exp2l _ _ p_gt1) -!card_pgroup.
  by rewrite -defR1 (exponent_Ohm1_class2 p_odd) // nil_class2 defR'.
apply: IHn oab (leq_trans ltRbR leRn) => //.
rewrite inE -!cycle_subG -defAb quotient_norms ?andbT //.
apply: contra not_cRA => cRAb; rewrite (coprime_cent_Phi pR coRA) // defPhi.
by rewrite commGC -quotient_cents2 ?gFnorm.
Qed.

(* B & G, Lemma 4.15 is covered by maximal/critical_extraspecial. *)

(* This is B & G, Theorem 4.16 (due to Blackburn). *)
Theorem rank2_coprime_comm_cprod gT p (R A : {group gT}) :
    p.-group R -> odd #|R| -> R :!=: 1 -> 'r(R) <= 2 ->
    [~: R, A] = R -> p^'.-group A -> odd #|A| ->
  [/\ p > 3
    & [\/ abelian R 
        | exists2 S : {group gT},
             [/\ ~~ abelian S, logn p #|S| = 3 & exponent S %| p]
        & exists C : {group gT},
             [/\ S \* C = R, cyclic C & 'Ohm_1(C) = S^`(1)]]].
Proof.
move=> pR oddR ntR rR defRA p'A oddA.
have [p_pr _ _] := pgroup_pdiv pR ntR; have p_gt1 := prime_gt1 p_pr.
have nilR: nilpotent R := pgroup_nil pR.
have nRA: A \subset 'N(R) by rewrite -commg_subl defRA.
have p_gt3: p > 3; last split => //.
  have [Ab1 | [q q_pr q_dv_Ab]] := trivgVpdiv (A / 'C_A(R)).
    case/eqP: ntR; rewrite -defRA commGC; apply/commG1P.
    by rewrite -subsetIidl -quotient_sub1 ?Ab1 ?normsI ?norms_cent ?normG.
  have odd_q := dvdn_odd q_dv_Ab (quotient_odd _ oddA).
  have p'q := pgroupP (quotient_pgroup _ p'A) q q_pr q_dv_Ab.
  have q_gt1: q > 1 := prime_gt1 q_pr.
  have q_gt2: q > 2 by rewrite ltn_neqAle; case: eqP odd_q => // <-.
  apply: leq_ltn_trans q_gt2 _.
  rewrite /= -ker_conj_aut (card_isog (first_isog_loc _ _)) // in q_dv_Ab.
  have q_dv_A := dvdn_trans q_dv_Ab (cardSg (Aut_conj_aut _ _)).
  by case/(pi_Aut_rank2_pgroup pR): (pgroupP (pgroup_pi _) q q_pr q_dv_A).
pose S := 'Ohm_1(R); pose S' := S^`(1); pose C := 'C_R(S).
have pS: p.-group S := pgroupS (Ohm_sub 1 _) pR.
have nsSR: S <| R := Ohm_normal 1 R.
have nsS'R: S' <| R := char_normal_trans (der_char 1 _) nsSR.
have [sSR nSR] := andP nsSR; have [_ nS'R] := andP nsS'R.
have [Sle2 | Sgt2] := leqP (logn p #|S|) 2.
  have metaR: metacyclic R := p2_Ohm1_metacyclic pR p_gt3 Sle2.
  have [cRR _ _] := coprime_metacyclic_cent_sdprod pR oddR metaR p'A nRA.
  by left; rewrite -defRA.
have{p_gt3} eS: exponent S %| p by apply: exponent_Ohm1_rank2.
have{rR} rS: 'r(S) <= 2 by rewrite rank_Ohm1.
have{Sgt2} dimS: logn p #|S| = 3.
  by apply/eqP; rewrite eqn_leq rank2_exponent_p_p3group.
have{rS} not_cSS: ~~ abelian S.
  by apply: contraL rS => cSS; rewrite -ltnNge -dimS -rank_abelem ?abelem_Ohm1.
have esS: extraspecial S by apply: (p3group_extraspecial pS); rewrite ?dimS.
have defS': S' = 'Z(S) by case: esS; case.
have oS': #|S'| = p by rewrite defS' (card_center_extraspecial pS esS).
have dimS': logn p #|S'| = 1%N by rewrite oS' (pfactorK 1).
have nsCR: C <| R := normalGI nSR (cent_normal _); have [sCR nCR] := andP nsCR.
have [pC oddC]: p.-group C * odd #|C| := (pgroupS sCR pR, oddSg sCR oddR).
have defC1: 'Ohm_1(C) = S'.
  apply/eqP; rewrite eqEsubset defS' subsetI OhmS ?(OhmE 1 pC) //= -/C.
  by rewrite gen_subG setIAC subsetIr sub_gen ?setSI // subsetI sSR sub_LdivT.
have{pC oddC} cycC: cyclic C.
  rewrite (odd_pgroup_rank1_cyclic pC) //.
  by rewrite -p_rank_Ohm1 defC1 -dimS' p_rank_le_logn.
pose T := [~: S, R]; have nsTR: T <| R by rewrite /normal commg_normr comm_subG.
have [sTR nTR] := andP nsTR; have pT: p.-group T := pgroupS sTR pR.
have [sTS' | not_sTS' {esS}] := boolP (T \subset S').
  right; exists [group of S] => //; exists [group of C].
  by rewrite (critical_extraspecial pR sSR esS sTS').
have ltTS: T \proper S by rewrite (nil_comm_properl nilR) ?Ohm1_eq1 ?subsetIidl.
have sTS: T \subset S := proper_sub ltTS.
have [sS'T ltS'T]: S' \subset T /\ S' \proper T by rewrite /proper commgS.
have{ltS'T ltTS} dimT: logn p #|T| = 2.
  by apply/eqP; rewrite eqn_leq -ltnS -dimS -dimS' !properG_ltn_log.
have{eS} eT: exponent T %| p := dvdn_trans (exponentS sTS) eS.
have cTT: abelian T by rewrite (p2group_abelian pT) ?dimT.
have abelT: p.-abelem T by apply/and3P.
pose B := 'C_R(T); have sTB: T \subset B by rewrite subsetI sTR.
have nsBR: B <| R := normalGI nTR (cent_normal _); have [sBR nBR] := andP nsBR.
have not_sSB: ~~ (S \subset B).
  by rewrite defS' !subsetI sTS sSR centsC in not_sTS' *.
have maxB: maximal B R.
  rewrite p_index_maximal // (_ : #|R : B| = p) //; apply/prime_nt_dvdP=> //.
    by apply: contra not_sSB; rewrite indexg_eq1; apply: subset_trans.
  rewrite -(part_pnat_id (pnat_dvd (dvdn_indexg _ _) pR)) p_part.
  by rewrite (@dvdn_exp2l _ _ 1) // logn_quotient_cent_abelem ?dimT //.
have{maxB nsBR} defR: B * S = R := mulg_normal_maximal nsBR maxB sSR not_sSB.
have cBbBb: abelian (B / C).
  rewrite sub_der1_abelian // subsetI comm_subG ?subsetIl //=; apply/commG1P.
  suff cB_SB: [~: S, B, B] = 1 by rewrite three_subgroup // [[~: _, S]]commGC.
  by apply/commG1P; rewrite centsC subIset // centS ?orbT // commgS.
have{cBbBb} abelBb: p.-abelem (B / C).
  apply/abelemP=> //; split=> // Cg; case/morphimP=> x Nx Bx /= ->.
  have [Rx cTx] := setIP Bx; rewrite -morphX //= coset_id // inE groupX //=.
  apply/centP=> y Sy; symmetry; have Tyx : [~ y, x] \in T by apply: mem_commg.
  by apply/commgP; rewrite commgX ?(exponentP eT) //; apply: (centP cTx).
have nsCB: C <| B by rewrite (normalS _ _ nsCR) ?setIS ?subsetIl // centS.
have p'Ab: p^'.-group (A / C) by apply: quotient_pgroup.
have sTbB: T / C \subset B / C by rewrite quotientS.
have nSA: A \subset 'N(S) := char_norm_trans (Ohm_char 1 _) nRA.
have nTA: A \subset 'N(T) := normsR nSA nRA.
have nTbA: A / C \subset 'N(T / C) := quotient_norms _ nTA.
have nBbA: A / C \subset 'N(B / C).
  by rewrite quotient_norms ?normsI ?norms_cent.
have{p'Ab sTbB nBbA abelBb nTbA}
  [Xb defBb nXbA] := Maschke_abelem abelBb p'Ab sTbB nBbA nTbA.
have{defBb} [_] := dprodP defBb; rewrite /= -/T -/B => defBb _ tiTbX.
have sXbB: Xb \subset B / C by rewrite -defBb mulG_subr.
have{sXbB} [X] := inv_quotientS nsCB sXbB; rewrite /= -/C -/B => defXb sCX sXB.
have sXR: X \subset R := subset_trans sXB sBR; have pX := pgroupS sXR pR.
have nsCX: C <| X := normalS sCX sXR nsCR.
have{tiTbX} ziTX: T :&: X \subset C.
  rewrite -quotient_sub1 ?subIset ?(subset_trans sTR) ?normal_norm //= -/C.
  by rewrite quotientIG -?defXb ?tiTbX.
have{nXbA} nXA: A \subset 'N(X).
  have nCA: A \subset 'N(C) by rewrite normsI ?norms_cent.
  by rewrite -(quotientSGK nCA) ?normsG // quotient_normG -?defXb.
have{abelT} defB1: 'Ohm_1(B) = T.
  apply/eqP; rewrite eq_sym eqEcard -{1}[T](Ohm1_id abelT) OhmS //.
  have pB1: p.-group 'Ohm_1(B) := pgroupS (subset_trans (Ohm_sub 1 _) sBR) pR.
  rewrite (card_pgroup pT) (card_pgroup pB1) leq_exp2l //= -/T -/B.
  rewrite dimT -ltnS -dimS properG_ltn_log // properEneq OhmS ?subsetIl //= -/S.
  by case: eqP not_sSB => // <-; rewrite Ohm_sub.
have{ziTX defB1} cycX: cyclic X; last have [x defX]:= cyclicP cycX.
  rewrite (odd_pgroup_rank1_cyclic pX (oddSg sXR oddR)) -p_rank_Ohm1.
  have:= cycC; rewrite abelian_rank1_cyclic ?cyclic_abelian //= -/C.
  apply: leq_trans (leq_trans (p_rank_le_rank p _) (rankS _)).
  by apply: subset_trans ziTX; rewrite subsetI Ohm_sub -defB1 OhmS.
have{Xb defXb defBb nsCX} mulSX: S * X = R.
  have nCT: T \subset 'N(C) := subset_trans sTR nCR.
  rewrite -defR -(normC (subset_trans sSR nBR)) -[B](quotientGK nsCB) -defBb.
  rewrite cosetpreM quotientK // defXb quotientGK // -(normC nCT). 
  by rewrite -mulgA (mulSGid sCX) mulgA (mulGSid sTS).
have{mulSX} not_sXS_S': ~~ ([~: X, S] \subset S'). 
  apply: contra not_sTS' => sXS_S'; rewrite /T -mulSX.
  by rewrite commGC commMG ?(subset_trans sXR) // mul_subG.
have [oSb oTb] : #|S / T| = p /\ #|T / S'| = p.
  rewrite (card_pgroup (quotient_pgroup _ pS)) -divg_normal ?(normalS _ sSR) //.
  rewrite (card_pgroup (quotient_pgroup _ pT)) -divg_normal ?(normalS _ sTR) //.
  by rewrite !logn_div ?cardSg // dimS dimT dimS'.
have [Ty defSb]: exists Ty, S / T = <[Ty]>.
  by apply/cyclicP; rewrite prime_cyclic ?oSb.
have SbTy: Ty \in S / T by rewrite defSb cycle_id.
have{SbTy} [y nTy Sy defTy] := morphimP SbTy.
have [S'z defTb]: exists S'z, T / S' = <[S'z]>.
  apply/cyclicP; rewrite prime_cyclic ?oTb //.
have TbS'z: S'z \in T / S' by rewrite defTb cycle_id.
have{TbS'z} [z nS'z Tz defS'z] := morphimP TbS'z.
have [Ta AbTa not_cSbTa]: exists2 Ta, Ta \in A / T & Ta \notin 'C(S / T).
  apply: subsetPn; rewrite quotient_cents2 ?commg_norml //= -/T commGC.
  apply: contra not_sSB => sSA_T; rewrite (subset_trans sSR) // -defRA -defR.
  rewrite -(normC (subset_trans sSR nBR)) commMG /= -/S -/B; last first.
    by rewrite cents_norm ?subIset ?centS ?orbT.
  by rewrite mul_subG ?commg_subl ?normsI ?norms_cent // (subset_trans sSA_T).
have [a nTa Aa defTa] := morphimP AbTa.
have nS'a: a \in 'N(S') := subsetP (char_norm_trans (der_char 1 _) nSA) a Aa.
have [i xa]: exists i, x ^ a = x ^+ i.
  by apply/cycleP; rewrite -cycle_subG cycleJ /= -defX (normsP nXA).
have [j Tya]: exists j, Ty ^ Ta = Ty ^+ j.
  apply/cycleP; rewrite -cycle_subG cycleJ /= -defSb.
  by rewrite (normsP (quotient_norms _ nSA)).
suffices {oSb oddA not_cSbTa} j2_1: j ^ 2 == 1 %[mod p].
  have Tya2: Ty ^ coset T (a ^+ 2) = Ty ^+ (j ^ 2).
    by rewrite morphX // conjgM -defTa Tya conjXg Tya expgM.
  have coA2: coprime #|A| 2 by rewrite coprime_sym prime_coprime // dvdn2 oddA.
  case/negP: not_cSbTa; rewrite defTa -(expgK coA2 Aa) morphX groupX //=.
  rewrite defSb cent_cycle inE conjg_set1 Tya2 sub1set inE.
  by rewrite (eq_expg_mod_order _ _ 1) orderE -defSb oSb.
have {Tya Ta defTa AbTa} [u Tu yj]: exists2 u, u \in T & y ^+ j = u * y ^ a.
  apply: rcosetP; apply/rcoset_kercosetP; rewrite ?groupX ?groupJ //.
  by rewrite morphX ?morphJ -?defTy // -defTa.
have{Ty defTy defSb} defS: T * <[y]> = S.
  rewrite -quotientK ?cycle_subG ?quotient_cycle // -defTy -defSb /= -/T.
  by rewrite quotientGK // /normal sTS /= commg_norml.
have{nTA} [k S'zk]: exists k, S'z ^ coset S' a = S'z ^+ k.
  apply/cycleP; rewrite -cycle_subG cycleJ /= -defTb.
  by rewrite (normsP (quotient_norms _ nTA)) ?mem_quotient.
have S'yz: [~ y, z] \in S' by rewrite mem_commg // (subsetP sTS).
have [v Zv zk]: exists2 v, v \in 'Z(S) & z ^+ k = v * z ^ a.
  apply: rcosetP; rewrite -defS'.
  by apply/rcoset_kercosetP; rewrite ?groupX ?groupJ ?morphX ?morphJ -?defS'z.
have defT: S' * <[z]> = T.
  rewrite -quotientK ?cycle_subG ?quotient_cycle // -defS'z -defTb /= -/S'.
  by rewrite quotientGK // (normalS _ sTR) // proper_sub.
have nt_yz: [~ y, z] != 1.
  apply: contra not_cSS; rewrite (sameP commgP cent1P) => cyz.
  rewrite -defS abelianM cTT cycle_abelian /= -/T -defT centM /= -/S' defS'.
  by rewrite cent_cycle subsetI centsC subIset ?centS ?cycle_subG ?orbT.
have sS'X1: S' \subset 'Ohm_1(X) by rewrite -defC1 OhmS.
have i_neq0: i != 0 %[mod p].
  have: 'Ohm_1(X) != 1 by rewrite (subG1_contra sS'X1) //= -cardG_gt1 oS'.
  rewrite defX in pX *; rewrite (Ohm_p_cycle 1 pX) subn1 trivg_card1 -orderE.
  rewrite -(orderJ _ a) conjXg xa order_eq1 -expgM -order_dvdn mod0n.
  apply: contra; case/dvdnP=> m ->; rewrite -mulnA -expnS dvdn_mull //.
  by rewrite {1}[#[x]](card_pgroup pX) dvdn_exp2l ?leqSpred.
have Txy: [~ x, y] \in T by rewrite [T]commGC mem_commg // -cycle_subG -defX. 
have [Rx Ry]: x \in R /\ y \in R by rewrite -cycle_subG -defX (subsetP sSR).
have [nS'x nS'y] := (subsetP nS'R x Rx, subsetP nS'R y Ry).
have{not_sXS_S'} not_S'xy: [~ x, y] \notin S'.
  apply: contra not_sXS_S' => S'xy.
  rewrite -quotient_cents2 ?(subset_trans _ nS'R) //= -/S'.
  rewrite -defS quotientMl ?(subset_trans _ nS'R) // centM /= -/S' -/T.
  rewrite subsetI quotient_cents; last by rewrite (subset_trans sXB) ?subsetIr.
  rewrite defX !quotient_cycle // cent_cycle cycle_subG /= -/S'.
  by rewrite (sameP cent1P commgP) -morphR /= ?coset_id.
have jk_eq_i: j * k = i %[mod p].
  have Zyz: [~ y, z] \in 'Z(S) by rewrite -defS'.
  have Sz: z \in S := subsetP sTS z Tz.
  have yz_p: [~ y, z] ^+ p == 1 by rewrite -order_dvdn -oS' order_dvdG.
  have <-: #[[~ y, z]] = p by apply: nt_prime_order => //; apply: eqP.
  apply: eqP; rewrite -eq_expg_mod_order -commXXg; try exact: centerC Zyz.
  have cyv: [~ y ^+ j, v] = 1 by apply/eqP/commgP/(centerC (groupX j Sy) Zv).
  have cuz: [~ u, z ^ a] = 1.
    by apply/eqP/commgP/(centsP cTT); rewrite ?memJ_norm.
  rewrite zk commgMJ cyv yj commMgJ cuz !conj1g mulg1 mul1g -conjRg.
  suffices [m ->]: exists m, [~ y, z] = x ^+ m by rewrite conjXg xa expgAC.
  by apply/cycleP; rewrite -defX (subsetP (Ohm_sub 1 X)) ?(subsetP sS'X1).
have ij_eq_k: i * j = k %[mod p].
  have <-: #[coset S' [~ x, y]] = p.
    apply: nt_prime_order => //.
      by apply: eqP; rewrite -order_dvdn -oTb order_dvdG 1?mem_quotient.
    by apply: contraNneq not_S'xy; apply: coset_idr; rewrite groupR.
  have sTbZ: T / S' \subset 'Z(R / S').
    rewrite prime_meetG ?oTb // (meet_center_nil (quotient_nil _ nilR)) //.
      by rewrite quotient_normal //; apply/andP.
    by rewrite -cardG_gt1 oTb.
  have ZRxyb: [~ coset S' x, coset S' y] \in 'Z(R / S').
    by rewrite -morphR // (subsetP sTbZ) ?mem_quotient.
  apply: eqP; rewrite -eq_expg_mod_order {1}morphR //.
  rewrite -commXXg; try by apply: centerC ZRxyb; apply: mem_quotient.
  have [Ru nRa] := (subsetP sTR u Tu, subsetP nRA a Aa).
  rewrite -2?morphX // yj morphM ?(subsetP nS'R) ?memJ_norm //.
  have cxu_b: [~ coset S' (x ^+ i), coset S' u] = 1.
    apply: eqP; apply/commgP.
    by apply: centerC (subsetP sTbZ _ _); rewrite mem_quotient ?groupX.
  rewrite commgMJ cxu_b conj1g mulg1 -xa !morphJ // -conjRg -morphR //=.
  have: coset S' [~ x, y] \in <[S'z]> by rewrite -defTb mem_quotient.
  by case/cycleP=> m ->; rewrite conjXg S'zk expgAC.
have j2_gt0: j ^ 2 > 0.
  rewrite expn_gt0 orbF lt0n; apply: contraNneq i_neq0 => j0.
  by rewrite -jk_eq_i j0.
have{i_neq0} co_p_i: coprime p i by rewrite mod0n prime_coprime in i_neq0 *.
rewrite eqn_mod_dvd // -(Gauss_dvdr _ co_p_i) mulnBr -eqn_mod_dvd ?leq_mul //.
by rewrite muln1 mulnCA -modnMmr ij_eq_k modnMmr jk_eq_i.
Qed.

(* This is B & G, Theorem 4.17. *)
Theorem der1_Aut_rank2_pgroup gT p (R : {group gT}) (A : {group {perm gT}}) :
    p.-group R -> odd #|R| -> 'r(R) <= 2 ->
    A \subset Aut R -> solvable A -> odd #|A| ->
  p.-group A^`(1).
Proof.
move=> pR oddR rR AutA solA oddA.
without loss ntR: / R :!=: 1.
  case: eqP AutA => [-> | ntR _ -> //]; rewrite Aut1.
  by move/trivgP=> ->; rewrite derg1 commG1 pgroup1.
have [p_pr _ _] := pgroup_pdiv pR ntR; have p_gt1 := prime_gt1 p_pr.
have{ntR oddR} [H [charH _] _ eH pCH] := critical_odd pR oddR ntR.
have sHR := char_sub charH; have pH := pgroupS sHR pR.
have{rR} rH: 'r(H) <= 2 := leq_trans (rankS (char_sub charH)) rR.
have dimH: logn p #|H| <= 3 by rewrite rank2_exponent_p_p3group ?eH.
have{eH} ntH: H :!=: 1 by rewrite trivg_exponent eH gtnNdvd.
have charP := Phi_char H; have [sPH nPH] := andP (Phi_normal H : 'Phi(H) <| H).
have nHA: {acts A, on group H | [Aut R]} := gacts_char _ AutA charH.
pose B := 'C(H | <[nHA]>); pose V := H / 'Phi(H); pose C := 'C(V | <[nHA]> / _).
have{pCH} pB: p.-group B.
  by rewrite (pgroupS _ pCH) //= astab_actby setIid subsetIr.
have s_p'C_B X: gval X \subset C -> p^'.-group X -> X \subset B.
  move=> sXC p'X; have [sDX _] := subsetIP sXC; have [sXA _] := subsetIP sDX.
  rewrite -gacentC //; apply/setIidPl; rewrite -[H :&: _]genGid //.
  apply: Phi_nongen; apply/eqP; rewrite eqEsubset join_subG sPH subsetIl.
  rewrite -quotientYK 1?subIset ?nPH //= -sub_quotient_pre //= -/V gacentIim.
  have pP := pgroupS sPH pH; have coPX := pnat_coprime pP p'X.
  rewrite -(setIid X) -(gacent_ract _ sXA).
  rewrite ext_coprime_quotient_cent ?(pgroup_sol pP) ?acts_char //.
  have domXb: X \subset qact_dom (<[nHA]> \ sXA) 'Phi(H).
    by rewrite qact_domE ?acts_char.
  rewrite gacentE // subsetIidl -/V; apply/subsetP=> v Vv; apply/afixP=> a Xa.
  have [cVa dom_a] := (subsetP sXC a Xa, subsetP domXb a Xa).
  have [x Nx Hx def_v] := morphimP Vv;  rewrite {1}def_v qactE //=.
  by rewrite -qactE ?(astab_dom cVa) ?(astab_act cVa) -?def_v.
have{B pB s_p'C_B} pC : p.-group C.
  apply/pgroupP=> q q_pr; case/Cauchy=> // a Ca oa; apply: wlog_neg => p'q.
  apply: (pgroupP pB) => //; rewrite -oa cardSg // s_p'C_B ?cycle_subG //.
  by rewrite /pgroup -orderE oa pnatE.
have nVA: A \subset qact_dom <[nHA]> 'Phi(H) by rewrite qact_domE // acts_char.
have nCA: A \subset 'N(C).
  by rewrite (subset_trans _ (astab_norm _ _)) // astabs_range.
suffices{pC nCA}: p.-group (A / C)^`(1).
  by rewrite -quotient_der ?pquotient_pgroup // (subset_trans (der_sub 1 A)).
pose toAV := ((<[nHA]> / 'Phi(H)) \ nVA)%gact.
have defC: C = 'C(V | toAV).
  by symmetry; rewrite astab_ract; apply/setIidPr; rewrite subIset ?subsetIl.
have abelV: p.-abelem V := Phi_quotient_abelem pH.
have ntV: V != 1 by rewrite -subG1 quotient_sub1 // proper_subn ?Phi_proper.
have: 'r(V) \in iota 1 2.
  rewrite mem_iota rank_gt0 ntV (rank_abelem abelV).
  have [abelH | not_abelH] := boolP (p.-abelem H).
    by rewrite ltnS (leq_trans _ rH) // (rank_abelem abelH) logn_quotient.
  by rewrite (leq_trans _ dimH) // ltn_log_quotient // (trivg_Phi pH).
rewrite !inE; case/pred2P=> dimV.
  have isoAb: A / C \isog actperm toAV @* A.
    by rewrite defC astab_range -ker_actperm first_isog.
  rewrite (derG1P _) ?pgroup1 // (isog_abelian isoAb).
  apply: abelianS (im_actperm_Aut _) (Aut_cyclic_abelian _).
  by rewrite (abelem_cyclic abelV) -rank_abelem ?dimV.
pose Vb := sdpair1 toAV @* V; pose Ab := sdpair2 toAV @* A.
have [injV injA] := (injm_sdpair1 toAV, injm_sdpair2 toAV).
have abelVb: p.-abelem Vb := morphim_abelem _ abelV.
have ntVb: Vb != 1 by rewrite morphim_injm_eq1. 
have nVbA: Ab \subset 'N(Vb) := im_sdpair_norm toAV.
pose rV := morphim_repr (abelem_repr abelVb ntVb nVbA) (subxx A).
have{defC} <-: rker rV = C; last move: rV.
  rewrite rker_morphim rker_abelem morphpreI morphimK //=.
  by rewrite (trivgP injA) mul1g -astabEsd // defC astab_ract 2!setIA !setIid.
have ->: 'dim Vb = 2 by rewrite (dim_abelemE abelVb) // card_injm -?rank_abelem.
move=> rV; rewrite -(eq_pgroup _ (GRing.charf_eq (char_Fp p_pr))).
by apply: der1_odd_GL2_charf (kquo_mx_faithful rV); rewrite !morphim_odd.
Qed.

(* This is B & G, Theorem 4.18(a). *)
Theorem rank2_max_pdiv gT p q (G : {group gT}) :
  solvable G -> odd #|G| -> 'r_p(G) <= 2 -> q \in \pi(G / 'O_p^'(G)) -> q <= p.
Proof.
rewrite mem_primes => solG oddG rG /and3P[pr_q _ /= q_dv_G].
without loss Gp'1: gT G solG oddG rG q_dv_G / 'O_p^'(G) = 1.
  move/(_ _ (G / 'O_p^'(G))%G); rewrite quotient_odd ?quotient_sol //.
  rewrite trivg_pcore_quotient -(card_isog (quotient1_isog _)).
  by rewrite p_rank_p'quotient ?pcore_pgroup ?gFnorm //; apply.
set R := 'O_p(G); have pR: p.-group R := pcore_pgroup p G.
have [sRG nRG] := andP (pcore_normal p G : R <| G). 
have oddR: odd #|R| := oddSg sRG oddG. 
have rR: 'r(R) <= 2 by rewrite (rank_pgroup pR) (leq_trans _ rG) ?p_rankS.
rewrite leq_eqVlt -implyNb; apply/implyP=> p'q.
have [|//] := pi_Aut_rank2_pgroup pR oddR rR _ p'q; rewrite eq_sym in p'q.
apply: (piSg (Aut_conj_aut _ G)); apply: contraLR q_dv_G.
rewrite -p'groupEpi -p'natE // Gp'1 -(card_isog (quotient1_isog _)) /pgroup.
rewrite -(card_isog (first_isog_loc _ _)) // -!pgroupE ker_conj_aut /= -/R.
set C := 'C_G(R); rewrite pquotient_pgroup ?normsI ?norms_cent ?normG //= -/C.
suffices sCR: C \subset R by rewrite (pgroupS sCR (pi_pnat pR _)).
by rewrite /C /R -(Fitting_eq_pcore _) ?cent_sub_Fitting.
Qed.

(* This is B & G, Theorem 4.18(c,e) *)
Theorem rank2_der1_complement gT p (G : {group gT}) : 
    solvable G -> odd #|G| -> 'r_p(G) <= 2 ->
  [/\ (*c*) p^'.-Hall(G^`(1)) 'O_p^'(G^`(1)), 
     (*e1*) abelian (G / 'O_{p^',p}(G))
   & (*e2*) p^'.-group (G / 'O_{p^',p}(G))].
Proof.
move=> solG oddG rG; rewrite /pHall pcore_sub pcore_pgroup /= pnatNK.
rewrite -(pcore_setI_normal _ (der_normal 1 G)) // setIC indexgI /=.
without loss Gp'1: gT G solG oddG rG / 'O_p^'(G) = 1.
  have nsGp': 'O_p^'(G) <| G := pcore_normal p^' G; have [_ nGp'] := andP nsGp'.
  move/(_ _ (G / 'O_p^'(G))%G); rewrite quotient_sol // quotient_odd //=.
  have Gp'1 := trivg_pcore_quotient p^' G.
  rewrite p_rank_p'quotient ?pcore_pgroup // Gp'1 indexg1; case=> //=.
  rewrite -quotient_der // card_quotient ?(subset_trans (der_sub 1 G)) // => ->.
  rewrite (pseries_pop2 _ Gp'1) /= -pseries1 -quotient_pseries /= /pgroup.
  pose isos := (isog_abelian (third_isog _ _ _), card_isog (third_isog _ _ _)).
  by rewrite !{}isos ?pseries_normal ?pseries_sub_catl.
rewrite pseries_pop2 // Gp'1 indexg1 -pgroupE /=.
set R := 'O_p(G); pose C := 'C_G(R).
have [sRG nRG] := andP (pcore_normal p G : R <| G).
have sCR: C \subset R by rewrite /C /R -(Fitting_eq_pcore _) ?cent_sub_Fitting.
have pR: p.-group R := pcore_pgroup p G; have pC: p.-group C := pgroupS sCR pR.
have nCG: G \subset 'N(C) by rewrite normsI ?normG ?norms_cent.
have nsG'G: G^`(1) <| G := der_normal 1 G; have [sG'G nG'G] := andP nsG'G.
suffices sG'R: G^`(1) \subset R.
  have cGbGb: abelian (G / R) := sub_der1_abelian sG'R.
  rewrite -{2}(nilpotent_pcoreC p (abelian_nil cGbGb)) trivg_pcore_quotient.
  by rewrite dprod1g pcore_pgroup (pgroupS sG'R pR).
rewrite pcore_max // -(pquotient_pgroup pC (subset_trans sG'G nCG)) /= -/C.
pose A := conj_aut 'O_p(G) @* G; have AutA: A \subset Aut R := Aut_conj_aut _ G.
have isoGbA: G / C \isog A by rewrite /C -ker_conj_aut first_isog_loc.
have{isoGbA} [f injf defA] := isogP isoGbA; rewrite /= -/A in defA.
rewrite quotient_der // /pgroup -(card_injm injf) ?der_sub ?morphim_der //.
have [? ?]: odd #|A| /\ solvable A by rewrite -defA !morphim_odd ?morphim_sol.
have rR: 'r(R) <= 2 by rewrite (rank_pgroup pR) (leq_trans (p_rankS p sRG)).
by rewrite defA -pgroupE (der1_Aut_rank2_pgroup pR) ?(oddSg sRG).
Qed.

(* This is B & G, Theorem 4.18(b) *)
Theorem rank2_min_p_complement gT (G : {group gT}) (p := pdiv #|G|) :
  solvable G -> odd #|G| -> 'r_p(G) <= 2 -> p^'.-Hall(G) 'O_p^'(G).
Proof.
move=> solG oddG rG; rewrite /pHall pcore_pgroup pcore_sub pnatNK /=.
rewrite -card_quotient ?gFnorm //; apply/pgroupP=> q q_pr q_dv_Gb.
rewrite inE /= eqn_leq (rank2_max_pdiv _ _ rG) ?mem_primes ?q_pr ?cardG_gt0 //.
by rewrite pdiv_min_dvd ?prime_gt1 ?(dvdn_trans q_dv_Gb) ?dvdn_quotient.
Qed.

(* This is B & G, Theorem 4.18(d) *)
Theorem rank2_sub_p'core_der1 gT (G A : {group gT}) p :
    solvable G -> odd #|G| -> 'r_p(G) <= 2 -> p^'.-subgroup(G^`(1)) A ->
  A \subset 'O_p^'(G^`(1)). 
Proof.
move=> solG oddG rG /andP[sAG' p'A]; rewrite sub_Hall_pcore //.
by have [-> _ _] := rank2_der1_complement solG oddG rG.
Qed.

(* This is B & G, Corollary 4.19 *)
Corollary rank2_der1_cent_chief gT p (G Gs U V : {group gT}) :
    odd #|G| -> solvable G -> Gs <| G -> 'r_p(Gs) <= 2 -> 
    chief_factor G V U -> p.-group (U / V) -> U \subset Gs ->
  G^`(1) \subset 'C(U / V | 'Q).
Proof.
move=> oddG solG nsGsG rGs chiefUf pUf sUGs.
wlog Gs_p'_1: gT G Gs U V oddG solG nsGsG rGs chiefUf pUf sUGs / 'O_p^'(Gs) = 1.
  pose K := 'O_p^'(Gs)%G; move/(_ _ (G / K) (Gs / K) (U / K) (V / K))%G.
  rewrite trivg_pcore_quotient quotient_odd ?quotient_sol ?quotientS //.
  have p'K: p^'.-group K := pcore_pgroup p^' Gs.
  have tiUfK := coprime_TIg (pnat_coprime pUf (quotient_pgroup V p'K)).
  have nsKG: K <| G := char_normal_trans (pcore_char p^' Gs) nsGsG.
  have [[sG'G sGsG] nKG] := (der_sub 1 G, normal_sub nsGsG, normal_norm nsKG).
  have{sGsG} [nKG' nKGs] := (subset_trans sG'G nKG, subset_trans sGsG nKG).
  case/andP: chiefUf; case/maxgroupP; case/andP=> ltVU nVG maxV nsUG.
  have [sUG nUG] := andP nsUG; have [sVU not_sUV] := andP ltVU.
  have [nUG' nVG'] := (subset_trans sG'G nUG, subset_trans sG'G nVG).
  have [sVG nVU] := (subset_trans sVU sUG, subset_trans sUG nVG).
  have [nKU nKV] := (subset_trans sUG nKG, subset_trans sVG nKG).
  have nsVU: V <| U by apply/andP.
  rewrite p_rank_p'quotient // /chief_factor -quotient_der ?quotient_normal //.
  rewrite andbT !sub_astabQR ?quotient_norms // -quotientR // => IH.
  rewrite -quotient_sub1 ?comm_subG // -tiUfK subsetI quotientS ?commg_subr //.
  rewrite quotientSK ?(comm_subG nVG') // (normC nKV) -quotientSK ?comm_subG //.
  apply: IH => //=; last first.
    rewrite -(setIid U) -(setIidPr sVU) -![_ / K](morphim_restrm nKU).
    by rewrite -(morphim_quotm _ nsVU) morphim_pgroup.
  apply/maxgroupP; rewrite /proper quotientS ?quotient_norms //= andbT.
  rewrite quotientSK // -(normC nKV) -quotientSK // -subsetIidl tiUfK.
  split=> [|Wb]; first by rewrite quotient_sub1.
  do 2![case/andP]=> sWbU not_sUWb nWbG sVWb; apply/eqP; rewrite eqEsubset sVWb.
  have nsWbG: Wb <| G / K by rewrite /normal (subset_trans sWbU) ?quotientS.
  have [W defWb sKW] := inv_quotientN nsKG nsWbG; case/andP=> sWG nWG.
  rewrite -(setIidPl sWbU) defWb -quotientGI // quotientS //.
  rewrite (maxV (W :&: U))%G ?normsI //; last first.
    by rewrite subsetI sVU andbT -(quotientSGK nKV sKW) -defWb.
  by rewrite andbT /proper subsetIr subsetIidr -(quotientSGK nKU sKW) -defWb.
pose R := 'O_p(Gs); have pR: p.-group R := pcore_pgroup p Gs.
have nsRG: R <| G := char_normal_trans (pcore_char p Gs) nsGsG.
have [[sGsG nGsG] [sRG nRG]] := (andP nsGsG, andP nsRG).
have nsRGs: R <| Gs := pcore_normal p Gs; have [sRGs nRGs] := andP nsRGs.
have sylR: p.-Sylow(Gs) R.
  have [solGs oddGs] := (solvableS sGsG solG, oddSg sGsG oddG).
  have [_ _ p'Gsb] := rank2_der1_complement solGs oddGs rGs.
  by rewrite /pHall pcore_sub pR -card_quotient //= -(pseries_pop2 p Gs_p'_1).
case/andP: (chiefUf); case/maxgroupP; case/andP=> ltVU nVG maxV nsUG.
have [sUG nUG] := andP nsUG; have [sVU not_sUV] := andP ltVU.
have [sVG nVU] := (subset_trans sVU sUG, subset_trans sUG nVG).
have nsVU: V <| U by apply/andP.
have nVGs := subset_trans sGsG nVG; have nVR := subset_trans sRGs nVGs.
have{sylR} sUfR: U / V \subset R / V.
  have sylRb: p.-Sylow(Gs / V) (R / V) by rewrite quotient_pHall.
  by rewrite (sub_normal_Hall sylRb) ?quotientS ?quotient_normal.
have pGb: p.-group((G / 'C_G(R))^`(1)).
  pose A := conj_aut 'O_p(Gs) @* G.
  have AA: A \subset Aut R := Aut_conj_aut _ G.
  have isoGbA: G / 'C_G(R) \isog A by rewrite -ker_conj_aut first_isog_loc.
  have{isoGbA} [f injf defA] := isogP isoGbA; rewrite /= -/A in defA.
  rewrite /pgroup -(card_injm injf) ?der_sub ?morphim_der //.
  have [? ?]: odd #|A| /\ solvable A by rewrite -defA !morphim_odd ?morphim_sol.
  have rR: 'r(R) <= 2 by rewrite (rank_pgroup pR) (leq_trans (p_rankS p sRGs)).
  by rewrite defA -pgroupE (der1_Aut_rank2_pgroup pR) ?(oddSg sRG).
set C := 'C_G(U / V | 'Q).
have nUfG: [acts G, on U / V | 'Q] by rewrite actsQ.
have nCG: G \subset 'N(C) by rewrite -(setIidPl nUfG) normsGI ?astab_norm. 
have{pGb sUfR} pGa': p.-group (G / C)^`(1).
  have nCRG : G \subset 'N('C_G(R)) by rewrite normsI ?normG ?norms_cent.
  have sCR_C: 'C_G(R) \subset C.
    rewrite subsetI subsetIl sub_astabQ ?subIset ?nVG ?(centsS sUfR) //=.
    by rewrite quotient_cents ?subsetIr.
  have [f /= <-]:= homgP (homg_quotientS nCRG nCG sCR_C).
  by rewrite -morphim_der //= morphim_pgroup.
have irrG: acts_irreducibly (G / C) (U / V) ('Q %% _).
  by rewrite acts_irr_mod_astab // acts_irrQ // chief_factor_minnormal.
have Ga_p_1: 'O_p(G / C) = 1.
  rewrite (pcore_faithful_irr_act pUf _ irrG) ?modact_faithful //.
  by rewrite gacentC ?quotientS ?subsetT ?subsetIr //= setICA subsetIl.
have sG'G := der_sub 1 G; have nCG' := subset_trans sG'G nCG.
rewrite -subsetIidl -{2}(setIidPl sG'G) -setIA subsetIidl -/C.
by rewrite -quotient_sub1 /= ?quotient_der //= -Ga_p_1 pcore_max ?der_normal.
Qed.

(* This is B & G, Theorem 4.20(a) *)
Theorem rank2_der1_sub_Fitting gT (G : {group gT}) :
  odd #|G| -> solvable G -> 'r('F(G)) <= 2 -> G^`(1) \subset 'F(G).
Proof.
move=> oddG solG Fle2; have nsFG := Fitting_normal G.
apply: subset_trans (chief_stab_sub_Fitting solG _) => //.
rewrite subsetI der_sub; apply/bigcapsP=> [[U V] /= /andP[chiefUV sUF]].
have [p p_pr /andP[pUV _]] := is_abelemP (sol_chief_abelem solG chiefUV).
apply: rank2_der1_cent_chief nsFG _ _ pUV sUF => //.
exact: leq_trans (p_rank_le_rank p _) Fle2.
Qed.

(* This is B & G, Theorem 4.20(b) *)
Theorem rank2_char_Sylow_normal gT (G S T : {group gT}) :
    odd #|G| -> solvable G -> 'r('F(G)) <= 2 -> 
  Sylow G S -> T \char S -> T \subset S^`(1) -> T <| G.
Proof.
set F := 'F(G) => oddG solG Fle2 /SylowP[p p_pr sylS] charT sTS'.
have [sSG pS _] := and3P sylS.
have nsFG: F <| G := Fitting_normal G; have [sFG nFG] := andP nsFG.
have nFS := subset_trans sSG nFG; have nilF: nilpotent F := Fitting_nil _.
have cGGq: abelian (G / F).
  by rewrite sub_der1_abelian ?rank2_der1_sub_Fitting.
have nsFS_G: F <*> S <| G.
  rewrite -(quotientGK nsFG) norm_joinEr // -(quotientK nFS) cosetpre_normal.
  by rewrite -sub_abelian_normal ?quotientS.
have sylSF: p.-Sylow(F <*> S) S.
  by rewrite (pHall_subl _ _ sylS) ?joing_subr // join_subG sFG.
have defG: G :=: F * 'N_G(S).
  rewrite -{1}(Frattini_arg nsFS_G sylSF) /= norm_joinEr // -mulgA.
  by congr (_ * _); rewrite mulSGid // subsetI sSG normG.
rewrite /normal (subset_trans (char_sub charT)) //= defG mulG_subG /= -/F.
rewrite setIC andbC subIset /=; last by rewrite (char_norm_trans charT).
case/dprodP: (nilpotent_pcoreC p nilF); rewrite /= -/F => _ defF cFpFp' _.
have defFp: 'O_p(F) = F :&: S.
  rewrite -{2}defF -group_modl ?coprime_TIg ?mulg1 //.
    by rewrite coprime_sym (pnat_coprime pS (pcore_pgroup _ _)).
  by rewrite p_core_Fitting pcore_sub_Hall.
rewrite -defF mulG_subG /= -/F defFp setIC subIset ?(char_norm charT) //=.
rewrite cents_norm // (subset_trans cFpFp') // defFp centS // subsetI.
rewrite (char_sub charT) (subset_trans (subset_trans sTS' (dergS 1 sSG))) //.
exact: rank2_der1_sub_Fitting.
Qed.

(* This is B & G, Theorem 4.20(c), for the last factor of the series. *)
Theorem rank2_min_p'core_Hall gT (G : {group gT}) (p := pdiv #|G|) :
  odd #|G| -> solvable G -> 'r('F(G)) <= 2 -> p^'.-Hall(G) 'O_p^'(G).
Proof.
set F := 'F(G) => oddG solG Fle2.
have nsFG: F <| G := Fitting_normal G; have [sFG nFG] := andP nsFG.
have [H] := inv_quotientN nsFG  (pcore_normal p^' _).
rewrite /= -/F => defH sFH nsHG; have [sHG nHG] := andP nsHG.
have [P sylP] := Sylow_exists p H; have [sPH pP _] := and3P sylP.
have sPF: P \subset F.
  rewrite -quotient_sub1 ?(subset_trans (subset_trans sPH sHG)) //.
  rewrite -(setIidPl (quotientS _ sPH)) -defH coprime_TIg //.
  by rewrite coprime_morphl // (pnat_coprime pP (pcore_pgroup _ _)).
have nilGq: nilpotent (G / F).
  by rewrite abelian_nil ?sub_der1_abelian ?rank2_der1_sub_Fitting.
have pGq: p.-group (G / H).
  rewrite /pgroup -(card_isog (third_isog sFH nsFG nsHG)) /= -/F -/(pgroup _ _).
  rewrite -(dprodW (nilpotent_pcoreC p nilGq)) defH quotientMidr.
  by rewrite quotient_pgroup ?pcore_pgroup.
rewrite pHallE pcore_sub -(Lagrange sHG) partnM // -card_quotient //=.
have hallHp': p^'.-Hall(H) 'O_p^'(H).
  case p'H: (p^'.-group H).
    by rewrite pHallE /= pcore_pgroup_id ?subxx //= part_pnat_id.
  have def_p: p = pdiv #|H|.
    have [p_pr pH]: prime p /\ p %| #|H|.
      apply/andP; apply: contraFT p'H => p'H; apply/pgroupP=> q q_pr qH.
      by apply: contraNneq p'H => <-; rewrite q_pr qH.
    apply/eqP; rewrite eqn_leq ?pdiv_min_dvd ?prime_gt1 //.
      rewrite pdiv_prime // cardG_gt1.
      by case: eqP p'H => // ->; rewrite pgroup1.
    exact: dvdn_trans (pdiv_dvd _) (cardSg (normal_sub nsHG)).
  rewrite def_p rank2_min_p_complement ?(oddSg sHG) ?(solvableS sHG) -?def_p //.
  rewrite -(p_rank_Sylow sylP) (leq_trans (p_rank_le_rank _ _)) //.
  exact: leq_trans (rankS sPF) Fle2.
rewrite -(card_Hall hallHp') part_p'nat ?pnatNK ?muln1 // subset_leqif_card.
  by rewrite pcore_max ?pcore_pgroup ?(char_normal_trans (pcore_char _ _)).
rewrite pcore_max ?pcore_pgroup // (normalS _ _ (pcore_normal _ _)) //.
rewrite -quotient_sub1 ?(subset_trans (pcore_sub _ _)) //.
rewrite -(setIidPr (quotientS _ (pcore_sub _ _))) coprime_TIg //.
by rewrite coprime_morphr // (pnat_coprime pGq (pcore_pgroup _ _)).
Qed.

(* This is B & G, Theorem 4.20(c), for intermediate factors. *)
Theorem rank2_ge_pcore_Hall gT m (G : {group gT}) (pi := [pred p | p >= m]) :
  odd #|G| -> solvable G -> 'r('F(G)) <= 2 -> pi.-Hall(G) 'O_pi(G).
Proof.
elim: {G}_.+1 {-2}G (ltnSn #|G|) => // n IHn G.
rewrite ltnS => leGn oddG solG Fle2; pose p := pdiv #|G|.
have [defGpi | not_pi_G] := eqVneq 'O_pi(G) G.
  by rewrite /pHall pcore_sub pcore_pgroup defGpi indexgg.
have pi'_p: (p \in pi^').
  apply: contra not_pi_G => pi_p; rewrite eqEsubset pcore_sub pcore_max //.
  apply/pgroupP=> q q_pr qG; apply: leq_trans pi_p _.
  by rewrite pdiv_min_dvd ?prime_gt1.
pose Gp' := 'O_p^'(G); have sGp'G: Gp' \subset G := pcore_sub _ _.
have hallGp'pi: pi.-Hall(Gp') 'O_pi(Gp').
  apply: IHn; rewrite ?(oddSg sGp'G) ?(solvableS sGp'G) //; last first.
    by apply: leq_trans (rankS _) Fle2; rewrite /= Fitting_pcore pcore_sub.
  apply: leq_trans (proper_card _) leGn.
  rewrite properEneq pcore_sub andbT; apply/eqP=> defG.
  suff: p \in p^' by case/eqnP.
  have p'G: p^'.-group G by rewrite -defG pcore_pgroup.
  rewrite (pgroupP p'G) ?pdiv_dvd ?pdiv_prime // cardG_gt1.
  by apply: contra not_pi_G; move/eqP->; rewrite (trivgP (pcore_sub _ _)).
have defGp'pi: 'O_pi(Gp') = 'O_pi(G).
  rewrite -pcoreI; apply: eq_pcore => q; apply: andb_idr.
  by apply: contraL => /=; move/eqnP->.
have hallGp': p^'.-Hall(G) Gp' by rewrite rank2_min_p'core_Hall.
rewrite pHallE pcore_sub /= -defGp'pi (card_Hall hallGp'pi) (card_Hall hallGp').
by rewrite partn_part // => q; apply: contraL => /=; move/eqnP->.
Qed.

(* This is B & G, Theorem 4.20(c), for the first factor of the series. *)
Theorem rank2_max_pcore_Sylow gT (G : {group gT}) (p := max_pdiv #|G|) :
  odd #|G| -> solvable G -> 'r('F(G)) <= 2 -> p.-Sylow(G) 'O_p(G).
Proof.
move=> oddG solG Fle2; pose pi := [pred q | p <= q].
rewrite pHallE pcore_sub eqn_leq -{1}(part_pnat_id (pcore_pgroup _ _)).
rewrite dvdn_leq ?partn_dvd ?cardSg ?pcore_sub // /=.
rewrite (@eq_in_partn _ pi) => [|q piGq]; last first.
  by rewrite !inE eqn_leq; apply: andb_idl => le_q_p; exact: max_pdiv_max.
rewrite -(card_Hall (rank2_ge_pcore_Hall p oddG solG Fle2)) -/pi.
rewrite subset_leq_card // pcore_max ?pcore_normal //.
apply: sub_in_pnat (pcore_pgroup _ _) => q; move/(piSg (pcore_sub _ _)) => piGq.
by rewrite !inE eqn_leq max_pdiv_max.
Qed.

End Section4.

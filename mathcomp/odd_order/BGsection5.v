(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
Require Import fintype finset prime fingroup morphism perm automorphism action.
Require Import quotient cyclic gfunctor pgroup gproduct center commutator.
Require Import gseries nilpotent sylow abelian maximal hall.
Require Import BGsection1 BGsection4.

(******************************************************************************)
(*   This file covers Section 5 of B & G, except for some technical results   *)
(* that are not actually used in the proof of the Odd Order Theorem, namely   *)
(* part (c) of Theorem 5.5, parts (b), (d) and (e) of Theorem 5.5, and all of *)
(* Theorem 5.7. We also make the following change: in B & G, narrow p-groups  *)
(* of rank at least 3 are defined by the structure of the centralisers of     *)
(* their prime subgroups, then characterized by their rank 2 elementary       *)
(* abelian subgroups in Theorem 5.3. We exchange the two, because the latter  *)
(* condition is easier to check, and is the only one used later in the proof. *)
(*                                                                            *)
(*          p.-narrow G == G has a maximal elementary abelian p-subgroup of   *)
(*                         p-rank at most 2.                                  *)
(*                      := ('r_p(G) > 2) ==> ('E_p^2(G) :&: 'E*_p(G) != set0) *)
(*                                                                            *)
(* narrow_structure p G <-> G has a subgroup S of order p whose centraliser   *)
(*                         is the direct product of S and a cyclic group C,   *)
(*                         i.e., S \x C = 'C_G(S). This is the condition used *)
(*                         in the definition of "narrow" in B & G, p. 2.      *)
(*                         Theorem 5.3 states that for odd p this definition  *)
(*                         is equivalent to ours, and this property is not    *)
(*                         used outside of Section 5.                         *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Reserved Notation "p .-narrow" (at level 2, format "p .-narrow").

Section Definitions.

Variables (gT : finGroupType) (p : nat) (A : {set gT}).

Definition narrow := ('r_p(A) > 2) ==> ('E_p^2(A) :&: 'E*_p(A) != set0).

Inductive narrow_structure : Prop :=
  NarrowStructure (S C : {group gT}) of
    S \subset A & C \subset A & #|S| = p & cyclic C & S \x C = 'C_A(S).

End Definitions.

Notation "p .-narrow" := (narrow p) : group_scope.

Section IsoDef.

Variables (gT rT : finGroupType) (p : nat).
Implicit Types G H : {group gT}.
Implicit Type R : {group rT}.

Lemma injm_narrow G H (f : {morphism G >-> rT}) :
  'injm f -> H \subset G -> p.-narrow (f @* H) = p.-narrow H.
Proof.
move=> injf sHG; rewrite /narrow injm_p_rank //; congr (_ ==> _).
apply/set0Pn/set0Pn=> [] [E /setIP[Ep2E maxE]].
  exists (invm injf @* E)%G; rewrite -[H](group_inj (morphim_invm injf _)) //.
  have sEfG: E \subset f @* G. 
    by rewrite (subset_trans _ (morphimS _ sHG)) //; case/pnElemP: Ep2E.
  by rewrite inE injm_pnElem ?injm_pmaxElem ?injm_invm ?morphimS // Ep2E.
have sEG: E \subset G by rewrite (subset_trans _ sHG) //; case/pnElemP: Ep2E.
by exists (f @* E)%G; rewrite inE injm_pnElem ?injm_pmaxElem // Ep2E.
Qed.

Lemma isog_narrow G R : G \isog R -> p.-narrow G = p.-narrow R.
Proof. by case/isogP=> f injf <-; rewrite injm_narrow. Qed.

(* No isomorphism theorems for narrow_structure, which is not used outside of *)
(* this file.                                                                 *)

End IsoDef.

Section Five.

Implicit Type gT : finGroupType.
Implicit Type p : nat.

Section OneGroup.

Variables (gT : finGroupType) (p : nat) (R : {group gT}).
Implicit Types B E S : {group gT}.

Lemma narrowJ x : p.-narrow (R :^ x) = p.-narrow R.
Proof. by apply: isog_narrow (isog_symr (conj_isog R x)). Qed.

Hypotheses (pR : p.-group R) (oddR : odd #|R|).

Section Rank3.

Hypothesis rR : 2 < 'r_p(R).

(* This lemma uses only the rR hypothesis. *)
Lemma narrow_pmaxElem : p.-narrow R -> exists E, E \in 'E_p^2(R) :&: 'E*_p(R).
Proof. by move=> nnP; apply: set0Pn; apply: implyP rR. Qed.

Let ntR : R :!=: 1. Proof. by case: eqP rR => // ->; rewrite p_rank1. Qed.
Let p_pr : prime p. Proof. by case: (pgroup_pdiv pR ntR). Qed.
Let p_gt1 : p > 1. Proof. exact: prime_gt1. Qed.

(* This is B & G, Lemma 5.1(a). *)
Lemma rank3_SCN3 : exists B, B \in 'SCN_3(R).
Proof.
by apply/set0Pn; rewrite -(rank2_SCN3_empty pR oddR) leqNgt (rank_pgroup pR) rR.
Qed.

(* This is B & G, Lemma 5.1(b). *)
Lemma normal_p2Elem_SCN3 E :
  E \in 'E_p^2(R) -> E <| R -> exists2 B, B \in 'SCN_3(R) & E \subset B.
Proof.
move=> Ep2E /andP[sER nER]; have [_ abelE dimE] := pnElemP Ep2E.
have [B Ep3B nBR]: exists2 B, B \in 'E_p^3(R) & R \subset 'N(B).
  have [C] := rank3_SCN3; case/setIdP=> SCN_C rC.
  have [nsCR cCC] := andP (maxgroupp (SCN_max SCN_C)).
  have [sCR _] := andP nsCR; have pC: p.-group C := pgroupS sCR pR.
  have{pC cCC} abelC1: p.-abelem 'Ohm_1(C) := Ohm1_abelem pC cCC.
  have dimC1: 3 <= logn p #|'Ohm_1(C)| by rewrite -rank_abelem // rank_Ohm1.
  have nsC1R: 'Ohm_1(C) <| R := char_normal_trans (Ohm_char 1 _) nsCR.
  have [B [sBC1 nsBR oB]] := normal_pgroup pR nsC1R dimC1.
  have [sBR nBR] := andP nsBR; exists B => //; apply/pnElemP.
  by rewrite oB pfactorK // (abelemS sBC1).
have [sBR abelB dimB] := pnElemP Ep3B; have [pB cBB _] := and3P abelB.
have [oB oE] := (card_pnElem Ep3B, card_pnElem Ep2E).
pose Bs := (E <*> 'C_B(E))%G; have sCB: 'C_B(E) \subset B := subsetIl B _.
have sBsR: Bs \subset R by rewrite join_subG sER subIset ?sBR.
suffices Bs_gt2: 2 < logn p #|Bs|.
  have nBsR: Bs <| R by rewrite /normal sBsR // normsY ?normsI ?norms_cent.
  have abelBs: p.-abelem Bs.
    by rewrite (cprod_abelem p (cprodEY _)) ?subsetIr // abelE (abelemS sCB).
  have [C maxC sBsC] : {H | [max H | H <| R & abelian H ] & Bs \subset H}.
    by apply: maxgroup_exists; rewrite nBsR (abelem_abelian abelBs).
  exists C; last by rewrite (subset_trans _ sBsC) ?joing_subl.
  by rewrite inE (max_SCN pR) ?(leq_trans Bs_gt2) // -rank_abelem ?rankS.
apply: contraFT (ltnn 2); rewrite -leqNgt => Bs_le2.
have{Bs_le2} sCE: 'C_B(E) \subset E.
  rewrite (sameP joing_idPl eqP) eq_sym eqEcard joing_subl /=.
  by rewrite (card_pgroup (pgroupS sBsR pR)) oE leq_exp2l.
have dimCBE: 2 <= logn p #|'C_B(E)|.
  rewrite -ltnS -dimB -addn1 -leq_subLR -logn_div ?divgS ?cardSg //.
  by rewrite logn_quotient_cent_abelem ?dimE ?(subset_trans sBR nER).
have defE: 'C_B(E) = E.
  apply/eqP; rewrite eqEcard sCE oE /=.
  by rewrite (card_pgroup (pgroupS sCB pB)) leq_exp2l.
by rewrite -dimB -dimE -defE lognSg // subsetIidl sub_abelian_cent // -defE.
Qed.

Let Z := 'Ohm_1('Z(R)).
Let W := 'Ohm_1('Z_2(R)).
Let T := 'C_R(W).

Let ntZ : Z != 1.
Proof. by rewrite Ohm1_eq1 (center_nil_eq1 (pgroup_nil pR)). Qed.

Let sZR : Z \subset R. 
Proof. exact: subset_trans (Ohm_sub 1 _) (center_sub R). Qed.

Let abelZ : p.-abelem (Z). 
Proof. by rewrite (Ohm1_abelem (pgroupS _ pR)) ?center_sub ?center_abelian. Qed.

Let pZ : p.-group Z.
Proof. exact: abelem_pgroup abelZ. Qed.

Let defCRZ : 'C_R(Z) = R.
Proof.
apply/eqP; rewrite eqEsubset subsetIl subsetIidl centsC.
by rewrite (subset_trans (Ohm_sub 1 _)) ?subsetIr.
Qed.

Let sWR : W \subset R. 
Proof. exact: subset_trans (Ohm_sub 1 _) (ucn_sub 2 R). Qed.

Let nWR : R \subset 'N(W). 
Proof. exact: char_norm_trans (Ohm_char 1 _) (char_norm (ucn_char 2 R)). Qed.

(* This is B & G, Lemma 5.2. *)
Lemma Ohm1_ucn_p2maxElem E :
    E \in 'E_p^2(R) :&: 'E*_p(R) ->
  [/\ (*a*) ~~ (E \subset T),
      (*b*) #|Z| = p /\ [group of W] \in 'E_p^2(R)
    & (*c*) T \char R /\ #|R : T| = p ].
Proof.
case/setIP=> Ep2E maxE; have defCRE1 := Ohm1_cent_max maxE pR.
have [[sER abelE dimE] oE] := (pnElemP Ep2E, card_pnElem Ep2E).
have [[sZR_R nZR_R] [pE _ eE]] := (andP (center_normal R), and3P abelE).
have{nZR_R} nZR: R \subset 'N(Z) := char_norm_trans (Ohm_char 1 _) nZR_R.
have{sZR_R} [pZR pW] := (pgroupS sZR_R pR, pgroupS sWR pR).
have sZE: Z \subset E by rewrite -defCRE1 OhmS ?setIS // centS.
have rCRE : 'r_p('C_R(E)) = 2 by rewrite -p_rank_Ohm1 defCRE1 p_rank_abelem.
have oZ: #|Z| = p.
  apply/prime_nt_dvdP; rewrite -?trivg_card1 // (card_pgroup pZ) /= -/Z.
  rewrite (@dvdn_exp2l _ _ 1) // -ltnS -dimE properG_ltn_log //= -/Z.
  by case/eqVproper: sZE rR => // defZ; rewrite -defCRZ defZ rCRE ltnn.
have ncycR: ~~ cyclic R by rewrite (odd_pgroup_rank1_cyclic pR) // -(subnKC rR).
have [ncycW eW] := Ohm1_odd_ucn2 pR oddR ncycR; rewrite -/W in ncycW eW.
have sWRZ: [~: W, R] \subset Z.
  rewrite [Z](OhmE 1 pZR) sub_gen //= -ucn1 subsetI.
  rewrite (subset_trans _ (ucn_comm 1 _)) ?commSg ?Ohm_sub //.
  by move: nWR eW; rewrite -commg_subl -sub_LdivT; apply: subset_trans.
have sZW: Z \subset W by rewrite OhmS /= -?ucn1 ?ucn_subS //.
have ltZW: Z \proper W.
  by rewrite properEneq; case: eqP ncycW => // <-; rewrite prime_cyclic ?oZ.
have sWRE := subset_trans sWRZ sZE.
have nEW: W \subset 'N(E) by rewrite -commg_subr (subset_trans _ sWRE) ?commgSS.
have defZ: 'C_W(E) = Z.
  have sCE: 'C_W(E) \subset E.
    rewrite -{2}defCRE1 (OhmE 1 (pgroupS (subsetIl R _) pR)) sub_gen //.
    by rewrite subsetI setSI // subIset // sub_LdivT eW.
  have [defC | ltCE] := eqVproper sCE.
    have sEW: E \subset W by rewrite -defC subsetIl.
    have nsER: E <| R.
      by rewrite /normal sER -commg_subl (subset_trans (commSg R sEW)).
    have [B scn3B sEB] := normal_p2Elem_SCN3 Ep2E nsER.
    have [scnB dimB] := setIdP scn3B; have [_ scBR] := SCN_P scnB.
    rewrite ltnNge -rank_Ohm1 -dimE -rank_abelem ?rankS // in dimB.
    by rewrite -scBR -defCRE1 OhmS // setIS ?centS.
  apply/eqP; rewrite eq_sym eqEcard oZ (card_pgroup (pgroupS sCE pE)) /= -/W.
  rewrite subsetI sZW (centsS sER); last by rewrite centsC -subsetIidl defCRZ.
  by rewrite (leq_exp2l _ 1) // -ltnS -dimE properG_ltn_log.
have dimW: logn p #|W| = 2.
  apply/eqP; rewrite -(Lagrange sZW) lognM ?cardG_gt0 // oZ (pfactorK 1) //=.
  rewrite -/Z eqSS eqn_leq -{1}defZ logn_quotient_cent_abelem ?dimE // -/W.
  by rewrite -divgS // logn_div ?cardSg // subn_gt0 properG_ltn_log.
have abelW: p.-abelem W.
  by rewrite (abelem_Ohm1 (pgroupS _ pR)) ?(p2group_abelian pW) ?dimW ?ucn_sub.
have charT: T \char R.
  by rewrite subcent_char ?char_refl //= (char_trans (Ohm_char 1 _)) ?ucn_char.
rewrite 2!inE sWR abelW dimW; do 2?split => //.
  by apply: contra (proper_subn ltZW); rewrite -defZ !subsetI subxx sER centsC.
apply/prime_nt_dvdP=> //.
  rewrite indexg_eq1 subsetIidl centsC; apply: contraFN (ltnn 1) => cRW.
  by rewrite -dimW -(setIidPl (centsS sER cRW)) defZ oZ (pfactorK 1).
rewrite -(part_pnat_id (pnat_dvd (dvdn_indexg _ _) pR)) p_part.
by rewrite (@dvdn_exp2l p _ 1) ?logn_quotient_cent_abelem ?dimW.
Qed.

(* This is B & G, Theorem 5.3(d); we omit parts (a)-(c) as they are mostly   *)
(* redundant with Lemma 5.2, given our definition of "narrow".               *)
Theorem narrow_cent_dprod S :
    p.-narrow R -> #|S| = p -> S \subset R -> 'r_p('C_R(S)) <= 2 -> 
  [/\ cyclic 'C_T(S), S :&: R^`(1) = 1, S :&: T = 1 & S \x 'C_T(S) = 'C_R(S)].
Proof.
move=> nnR oS sSR rS; have pS : p.-group S := pgroupS sSR pR.
have [E maxEp2E] := narrow_pmaxElem nnR; have [Ep2E maxE] := setIP maxEp2E.
have [not_sET [oZ Ep2W] [charT maxT]] := Ohm1_ucn_p2maxElem maxEp2E.
have cZS : S \subset 'C(Z) by rewrite (subset_trans sSR) // -defCRZ subsetIr.
have nZS : S \subset 'N(Z) by rewrite cents_norm.
have cSS : abelian S by rewrite cyclic_abelian ?prime_cyclic // oS.
pose SZ := (S <*> [group of Z])%G; have sSSZ: S \subset SZ := joing_subl _ _.
have sSZ_R: SZ \subset R by rewrite join_subG sSR sZR.
have abelSZ : p.-abelem SZ.
  by rewrite /= joingC (cprod_abelem p (cprodEY cZS)) abelZ prime_abelem.
have tiSZ: S :&: Z = 1.
  rewrite prime_TIg ?oS //= -/Z; apply: contraL rR => sZS.
  by rewrite -leqNgt (leq_trans _ rS) ?p_rankS // -{1}defCRZ setIS ?centS.
have{tiSZ} oSZ: #|SZ| = (p ^ 2)%N by rewrite /= norm_joinEl ?TI_cardMg ?oS ?oZ.
have Ep2SZ: SZ \in 'E_p^2(R) by rewrite pnElemE // !inE sSZ_R abelSZ oSZ eqxx.
have{oSZ Ep2SZ abelSZ sSZ_R} maxSZ: SZ \in 'E_p^2(R) :&: 'E*_p(R).
  rewrite inE Ep2SZ; apply/pmaxElemP; rewrite inE sSZ_R abelSZ.
  split=> // H /setIdP[sHR abelH] sSZH.
  have [[_ _ dimSZ] [cHH pH _]] := (pnElemP Ep2SZ, and3P abelH).
  have sSH: S \subset H := subset_trans sSSZ sSZH.
  have{sSH} sH_CRS: H \subset 'C_R(S) by rewrite subsetI sHR (centsS sSH).
  have{sH_CRS}: 'r_p(H) <= 2 by rewrite (leq_trans _ rS) ?p_rankS.
  apply: contraTeq; rewrite eq_sym eqEproper sSZH negbK => lSZH.
  by rewrite -ltnNge p_rank_abelem // -dimSZ properG_ltn_log.
have sZT: Z \subset T.
  by rewrite subsetI sZR (centsS sWR) // centsC -defCRZ subsetIr.
have{SZ sSSZ maxSZ} not_sST: ~~ (S \subset T).
  have: ~~ (SZ \subset T) by case/Ohm1_ucn_p2maxElem: maxSZ.
  by rewrite join_subG sZT andbT.
have tiST: S :&: T :=: 1 by rewrite prime_TIg ?oS. 
have defST: S * T = R.
  apply/eqP; rewrite eqEcard TI_cardMg ?mul_subG ?subsetIl //=.
  by rewrite  mulnC oS -maxT Lagrange ?subsetIl.
have cRRb: abelian (R / T) by rewrite -defST quotientMidr quotient_abelian.
have sR'T: R^`(1) \subset T by rewrite der1_min ?char_norm. 
have TI_SR': S :&: R^`(1) :=: 1.
  by rewrite prime_TIg ?oS // (contra _ not_sST) //; move/subset_trans->.
have defCRS : S \x 'C_T(S) = 'C_R(S).
  rewrite (dprodE _ _) ?subsetIr //= -/T; last by rewrite setIA tiST setI1g.
  rewrite -{1}(center_idP cSS) subcent_TImulg ?defST //.
  by rewrite subsetI normG (subset_trans sSR) ?char_norm.
have sCTSR: 'C_T(S) \subset R by rewrite subIset ?subsetIl.
split; rewrite ?(odd_pgroup_rank1_cyclic (pgroupS _ pR) (oddSg _ oddR)) //= -/T.
rewrite -ltnS (leq_trans _ rS) //= -(p_rank_dprod p defCRS) -add1n leq_add2r.
by rewrite -rank_pgroup // rank_gt0 -cardG_gt1 oS.
Qed.

(* This is B & G, Corollary 5.4. Given our definition of narrow, this is used *)
(* directly in the proof of the main part of Theorem 5.3.                     *)
Corollary narrow_centP : 
  reflect (exists S, [/\ gval S \subset R, #|S| = p & 'r_p('C_R(S)) <= 2])
          (p.-narrow R).
Proof.
rewrite /narrow rR; apply: (iffP (set0Pn _)) => [[E maxEp2E]|[S [sSR oS rCRS]]].
  have [Ep2E maxE] := setIP maxEp2E.
  have{maxEp2E} [_ [oZ _] _] := Ohm1_ucn_p2maxElem maxEp2E.
  have [sER abelE dimE] := pnElemP Ep2E; have oE := card_pnElem Ep2E.
  have sZE: Z \subset E by rewrite -(Ohm1_cent_max maxE pR) OhmS ?setIS ?centS.
  have [S defE] := abelem_split_dprod abelE sZE; exists S.
  have{defE} [[_ defZS _ _] oZS] := (dprodP defE, dprod_card defE).
  split; first by rewrite (subset_trans _ sER) // -defZS mulG_subr.
    by apply/eqP; rewrite -(eqn_pmul2l (ltnW p_gt1)) -{1}oZ oZS oE.
  rewrite -dimE -p_rank_abelem // -(Ohm1_cent_max maxE pR) p_rank_Ohm1.
  by rewrite -defZS /= centM setIA defCRZ.
have abelS := prime_abelem p_pr oS.
have cSZ: Z \subset 'C(S) by rewrite (centsS sSR) // centsC -defCRZ subsetIr.
have sSZR: S <*> Z \subset R by rewrite join_subG sSR.
have defSZ: S \x Z = S <*> Z.
  rewrite dprodEY ?prime_TIg ?oS //= -/Z; apply: contraL rR => sSZ.
  by rewrite -leqNgt (leq_trans _ rCRS) ?p_rankS // -{1}defCRZ setIS ?centS.
have abelSZ: p.-abelem (S <*> Z) by rewrite (dprod_abelem p defSZ) abelS.
have [pSZ cSZSZ _] := and3P abelSZ.
have dimSZ: logn p #|S <*> Z| = 2.
  apply/eqP; rewrite -p_rank_abelem // eqn_leq (leq_trans (p_rankS _ _) rCRS).
    rewrite -(p_rank_dprod p defSZ) p_rank_abelem // oS (pfactorK 1) // ltnS.
    by rewrite -rank_pgroup // rank_gt0.
  by rewrite subsetI sSZR sub_abelian_cent ?joing_subl.
exists [group of S <*> Z]; rewrite 3!inE sSZR abelSZ dimSZ /=.
apply/pmaxElemP; rewrite inE sSZR; split=> // E; case/pElemP=> sER abelE sSZE.
apply: contraTeq rCRS; rewrite eq_sym -ltnNge -dimSZ => neqSZE.
have [[pE cEE _] sSE] := (and3P abelE, subset_trans (joing_subl S Z) sSZE).
rewrite (leq_trans (properG_ltn_log pE _)) ?properEneq ?neqSZE //.
by rewrite -p_rank_abelem ?p_rankS // subsetI sER sub_abelian_cent.
Qed.

(* This is the main statement of B & G, Theorem 5.3, stating the equivalence  *)
(* of the structural and rank characterizations of the "narrow" property. Due *)
(* to our definition of "narrow", the equivalence is the converse of that in  *)
(* B & G (we define narrow in terms of maximal elementary abelian subgroups). *)
Lemma narrow_structureP : reflect (narrow_structure p R) (p.-narrow R).
Proof.
apply: (iffP idP) => [nnR | [S C sSR sCR oS cycC defSC]].
  have [S [sSR oS rCRS]] := narrow_centP nnR.
  have [cycC _ _ defCRS] := narrow_cent_dprod nnR oS sSR rCRS.
  by exists S [group of 'C_T(S)]; rewrite //= -setIA subsetIl.
apply/narrow_centP; exists S; split=> //.
have cycS: cyclic S by rewrite prime_cyclic ?oS.
rewrite -(p_rank_dprod p defSC) -!(rank_pgroup (pgroupS _ pR)) // -addn1.
rewrite leq_add -?abelian_rank1_cyclic ?cyclic_abelian //.
Qed.

End Rank3.

(* This is B & G, Theoren 5.5 (a) and (b). Part (c), which is not used in the *)
(* proof of the Odd Order Theorem, is omitted.                                *)
Theorem Aut_narrow (A : {group {perm gT}}) : 
    p.-narrow R -> solvable A -> A \subset Aut R -> odd #|A| ->
  [/\ (*a*) p^'.-group (A / 'O_p(A)), abelian (A / 'O_p(A))
    & (*b*) 2 < 'r(R) -> forall x, x \in A -> p^'.-elt x -> #[x] %| p.-1].
Proof.
move=> nnR solA AutA oddA; have nilR := pgroup_nil pR.
have [rR | rR] := leqP 'r(R) 2.
  have pA' := der1_Aut_rank2_pgroup pR oddR rR AutA solA oddA.
  have sA'Ap: A^`(1) \subset 'O_p(A) by rewrite pcore_max ?der_normal.
  have cAbAb: abelian (A / 'O_p(A)) by rewrite sub_der1_abelian.
  split; rewrite // -(nilpotent_pcoreC p (abelian_nil cAbAb)).
  by rewrite trivg_pcore_quotient dprod1g pcore_pgroup.
have ntR: R :!=: 1 by rewrite -rank_gt0 2?ltnW.
rewrite (rank_pgroup pR) in rR.
have [H [charH sHRZ] _ eH pCH] := critical_odd pR oddR ntR.
have{ntR} [[p_pr _ _] sHR] := (pgroup_pdiv pR ntR, char_sub charH).
have ntH: H :!=: 1 by rewrite trivg_exponent eH -prime_coprime ?coprimen1.
have{nnR} [S C sSR sCR oS cycC defSC] := narrow_structureP rR nnR.
have [_ mulSC cSC tiSC] := dprodP defSC.
have abelS: p.-abelem S := prime_abelem p_pr oS; have [pS cSS _] := and3P abelS.
have cycS: cyclic S by rewrite prime_cyclic ?oS.
have tiHS: H :&: S = 1.
  have rCRS: 'r_p('C_R(S)) <= 2.
    rewrite -(p_rank_dprod p defSC) -addn1 -!rank_pgroup ?(pgroupS _ pR) //.
    by rewrite leq_add -?abelian_rank1_cyclic ?cyclic_abelian.
  rewrite setIC prime_TIg ?oS //; apply: contraL (rCRS) => sSH; rewrite -ltnNge.
  have cZHS: S \subset 'C('Z(H)) by rewrite centsC (centsS sSH) ?subsetIr.
  pose U := S <*> 'Z(H).
  have sUH: U \subset H by rewrite join_subG sSH subsetIl.
  have cUU: abelian U  by rewrite abelianY cSS center_abelian centsC.
  have abelU: p.-abelem U by rewrite abelemE // cUU -eH exponentS.
  have sUR: U \subset R := subset_trans sUH sHR.
  have rU: 'r_p(U) <= 'r_p('C_R(S)).
    by rewrite p_rankS //= subsetI sUR (centsS (joing_subl S 'Z(H))).
  have nsUR: U <| R.
    rewrite /normal sUR -commg_subl (subset_trans (commSg _ sUH)) //= -/U.
    by rewrite (subset_trans sHRZ) // joing_subr.
  have{rU}:= leq_trans rU rCRS; rewrite leq_eqVlt => /predU1P[] rU. 
    have Ep2U: [group of U] \in 'E_p^2(R).
      by rewrite !inE /= sUR abelU -(p_rank_abelem abelU) rU.
    have [F scn3F sUF] := normal_p2Elem_SCN3 rR Ep2U nsUR.
    have [scnF rF] := setIdP scn3F; have [_ scF] := SCN_P scnF. 
    rewrite (leq_trans rF) // -scF -rank_pgroup ?(pgroupS (subsetIl _ _)) //. 
    by rewrite rankS ?setIS ?centS // (subset_trans _ sUF) ?joing_subl.
  have defU: S :=: U.
    apply/eqP; rewrite eqEcard oS joing_subl (card_pgroup (pgroupS sUR pR)).
    by rewrite -p_rank_abelem // (leq_exp2l _ 1) // prime_gt1.
  have ntS: S :!=: 1 by rewrite -cardG_gt1 oS prime_gt1.
  have sSZ: S \subset 'Z(R) by rewrite prime_meetG ?oS ?meet_center_nil // defU.
  by rewrite (setIidPl _) // centsC (subset_trans sSZ) ?subsetIr.
have{tiHS eH} oCHS: #|'C_H(S)| = p.
  have ntCHS: 'C_H(S) != 1.
    have: H :&: 'Z(R) != 1 by rewrite meet_center_nil ?char_normal.
    by apply: subG1_contra; rewrite setIS // (centsS sSR) ?subsetIr.
  have cycCHS: cyclic 'C_H(S).
    have tiS_CHS: S :&: 'C_H(S) = 1 by rewrite setICA setIA tiHS setI1g.
    rewrite (isog_cyclic (quotient_isog _ tiS_CHS)) ?subIset ?cent_sub ?orbT //.
    rewrite (cyclicS _ (quotient_cyclic S cycC)) //= -(quotientMidl S C).
    by rewrite mulSC quotientS // setSI // char_sub.
  have abelCHS: p.-abelem 'C_H(S).
    by rewrite abelemE ?cyclic_abelian // -eH exponentS ?subsetIl.
  rewrite -(Ohm1_id abelCHS).
  by rewrite (Ohm1_cyclic_pgroup_prime _ (abelem_pgroup abelCHS)).
pose B := A^`(1) <*> [set a ^+ p.-1 | a in A].
have sBA: B \subset A.
  rewrite join_subG (der_sub 1 A) /=.
  by apply/subsetP=> _ /imsetP[a Aa ->]; rewrite groupX.
have AutB: B \subset Aut R := subset_trans sBA AutA.
suffices pB (X : {group {perm gT}}): X \subset B -> p^'.-group X -> X :=: 1.
  have cAbAb: abelian (A / 'O_p(A)).
    rewrite sub_der1_abelian // pcore_max ?der_normal //.
    apply/pgroupP=> q q_pr; apply: contraLR => p'q; rewrite -p'natE //.
    have [X sylX] := Sylow_exists q A^`(1); have [sXA' qX _] := and3P sylX.
    rewrite -partn_eq1 ?cardG_gt0 // -(card_Hall sylX).
    by rewrite (pB X) ?cards1 ?(pi_pgroup qX) ?(subset_trans sXA') ?joing_subl.
  rewrite cAbAb -(nilpotent_pcoreC p (abelian_nil cAbAb)) trivg_pcore_quotient.
  rewrite dprod1g pcore_pgroup; split=> //_ a Aa p'a. 
  rewrite order_dvdn -cycle_eq1 [<[_]>]pB ?(pgroupS (cycleX _ _) p'a) //.
  by rewrite genS // sub1set inE orbC (mem_imset (expgn^~ _)).
move=> sXB p'X; have AutX := subset_trans sXB AutB.
pose toX := ([Aut R] \ AutX)%gact; pose CX := 'C_(H | toX)(X).
suffices sHCX: H \subset CX.
  rewrite -(setIid X) coprime_TIg ?(pnat_coprime (pgroupS _ pCH)) //.
  by rewrite subsetIidl gacent_ract setIid gacentC in sHCX.
elim: _.+1 {1 2 4 6}H (charH) (subxx H) (ltnSn #|H|) => // n IHn L charL sLH.
rewrite ltnS => leLn; have sLR := char_sub charL; pose K := [~: L, R].
wlog ntL: / L :!=: 1 by case: eqP => [-> | _ -> //]; rewrite sub1G.
have charK: K \char R by rewrite charR ?char_refl.
have ltKL: K \proper L.
  have nLR: R \subset 'N_R(L) by rewrite subsetIidl char_norm.
  exact: nil_comm_properl nilR sLR ntL nLR.
have [sKL sKR] := (proper_sub ltKL, char_sub charK).
have [sKH pK] := (subset_trans sKL sLH, pgroupS sKR pR : p.-group K).
have nsKH: K <| H := normalS sKH sHR (char_normal charK).
have sKCX: K \subset CX by rewrite IHn ?(leq_trans (proper_card ltKL)) ?leLn.
have pL := pgroupS sLR pR; have nKL: L \subset 'N(K) := commg_norml _ _.
have{pS cSS} oLb: #|L / K| = p.
  have [v defS] := cyclicP cycS; rewrite defS cycle_subG in sSR.
  have ntLb: L / K != 1 by rewrite -subG1 quotient_sub1 ?proper_subn.
  have [_ p_dv_Lb _] := pgroup_pdiv (quotient_pgroup _ pL) ntLb.
  apply/eqP; rewrite eqn_leq {p_dv_Lb}(dvdn_leq _ p_dv_Lb) // andbT.
  rewrite -divg_normal ?(normalS sKL sLH nsKH) // leq_divLR ?cardSg //= -/K.
  rewrite -(card_lcoset K v) -(LagrangeI L 'C(S)) -indexgI /= -oCHS /K commGC.
  rewrite {2}defS cent_cycle index_cent1 leq_mul ?subset_leq_card ?setSI //.
  by apply/subsetP=> vx; case/imsetP=> x Lx ->; rewrite mem_lcoset mem_commg.
have cycLb: cyclic (L / K) by rewrite prime_cyclic ?oLb.
rewrite -(quotientSGK _ sKCX) // quotientGI // subsetI quotientS //= -/K.
have actsXK: [acts X, on K | toX] by rewrite acts_ract subxx acts_char.
rewrite ext_coprime_quotient_cent ?(pnat_coprime pK p'X) ?(pgroup_sol pK) //.
have actsAL : {acts A, on group L | [Aut R]} by exact: gacts_char.
have sAD: A \subset qact_dom <[actsAL]> [~: L, R].
  by rewrite qact_domE // acts_actby subxx (setIidPr sKL) acts_char.
suffices cLbX: X \subset 'C(L / K | <[actsAL]> / _).
  rewrite gacentE ?qact_domE // subsetI quotientS //=.
  apply/subsetP=> Ku LbKu; rewrite inE; apply/subsetP=> x Xx; rewrite inE.
  have [Dx cLx] := setIdP (subsetP cLbX x Xx); have [Ax _] := setIdP Dx.
  rewrite inE in cLx; have:= subsetP cLx Ku LbKu; rewrite inE /=.
  have [u Nu Lu ->] := morphimP LbKu.
  by rewrite !{1}qactE // ?actbyE // qact_domE ?(subsetP actsXK).
rewrite (subset_trans sXB) // astab_range -ker_actperm gen_subG.
rewrite -sub_morphim_pre; last by rewrite -gen_subG ?(subset_trans sBA).
rewrite morphimU subUset morphim_der // (sameP trivgP derG1P).
rewrite (abelianS _ (Aut_cyclic_abelian cycLb)); last first.
  exact: subset_trans (morphim_sub _ _) (im_actperm_Aut _).
apply/subsetP=> _ /morphimP[_ _ /imsetP[x Ax ->] ->].
have Dx := subsetP sAD x Ax; rewrite inE morphX //= -order_dvdn.
apply: dvdn_trans (order_dvdG (actperm_Aut _ Dx)) _.
by rewrite card_Aut_cyclic // oLb (@totient_pfactor p 1) ?muln1.
Qed.

End OneGroup. 

(* This is B & G, Theorem 5.6, parts (a) and (c). We do not prove parts (b),  *)
(* (d) and (e), as they are not used in the proof of the Odd Order Theorem.   *)
Theorem narrow_der1_complement_max_pdiv gT p (G S : {group gT}) : 
    odd #|G| -> solvable G -> p.-Sylow(G) S -> p.-narrow S ->
    (2 < 'r(S)) ==> p.-length_1 G -> 
  [/\ (*a*) p^'.-Hall(G^`(1)) 'O_p^'(G^`(1))
    & (*c*) forall q, q \in \pi(G / 'O_p^'(G)) -> q <= p].
Proof.
move=> oddG solG sylS nnS; case: (leqP 'r(S) 2) => /= rS pl1G.
  have rG: 'r_p(G) <= 2 by rewrite -(rank_Sylow sylS).
  split=> [|q]; first by have [-> _ _] := rank2_der1_complement solG oddG rG.
  exact: rank2_max_pdiv solG oddG rG.
rewrite /pHall pcore_sub pcore_pgroup pnatNK /=.
rewrite -(pcore_setI_normal p^' (der_normal 1 G)) // setIC indexgI /=.
wlog Gp'1: gT G S oddG nnS solG sylS rS pl1G / 'O_p^'(G) = 1.
  set K := 'O_p^'(G); have [_ nKG] := andP (pcore_normal _ G : K <| G).
  move/(_ _ (G / K) (S / K))%G; rewrite quotient_sol ?quotient_odd //.
  have [[sSG pS _] p'K] := (and3P sylS, pcore_pgroup _ G : p^'.-group K).
  have [nKS nKG'] := (subset_trans sSG nKG, subset_trans (der_sub 1 G) nKG).
  have tiKS: K :&: S = 1 := coprime_TIg (p'nat_coprime p'K pS).
  have isoS := isog_symr (quotient_isog nKS tiKS).
  rewrite (isog_narrow p isoS) {isoS}(isog_rank isoS) quotient_pHall //.
  rewrite plength1_quo // trivg_pcore_quotient indexg1 /= -quotient_der //.
  by rewrite card_quotient //= -/K -(card_isog (quotient1_isog _)); exact.
rewrite Gp'1 indexg1 -(card_isog (quotient1_isog _)) -pgroupE.
have [sSG pS _] := and3P sylS; have oddS: odd #|S| := oddSg sSG oddG.
have ntS: S :!=: 1 by rewrite -rank_gt0 (leq_trans _ rS).
have [p_pr _ _] := pgroup_pdiv pS ntS; have p_gt1 := prime_gt1 p_pr.
have{pl1G} defS: 'O_p(G) = S.
  by rewrite (eq_Hall_pcore _ sylS) -?plength1_pcore_Sylow.
have nSG: G \subset 'N(S) by rewrite -defS gFnorm.
pose fA := restrm nSG (conj_aut S); pose A := fA @* G.
have AutA: A \subset Aut S by rewrite [A]im_restrm Aut_conj_aut.
have [solA oddA]: solvable A /\ odd #|A| by rewrite morphim_sol ?morphim_odd.
have [/= _ cAbAb p'A_dv_p1] := Aut_narrow pS oddS nnS solA AutA oddA.
have{defS} pKfA: p.-group ('ker fA).
  rewrite (pgroupS _ pS) //= ker_restrm ker_conj_aut.
  by rewrite -defS -Fitting_eq_pcore ?cent_sub_Fitting.
split=> [|q].
  rewrite -(pmorphim_pgroup pKfA) ?der_sub // morphim_der //.
  by rewrite (pgroupS (der1_min (char_norm _) cAbAb)) ?pcore_pgroup ?pcore_char.
rewrite mem_primes; case/and3P=> q_pr _; case/Cauchy=> // x Gx ox.
rewrite leq_eqVlt -implyNb; apply/implyP=> p'q; rewrite -(ltn_predK p_gt1) ltnS.
have ofAx: #[fA x] = q.
  apply/prime_nt_dvdP=> //; last by rewrite -ox morph_order.
  rewrite order_eq1; apply: contraNneq p'q => fAx1.
  by apply: (pgroupP pKfA); rewrite // -ox order_dvdG //; exact/kerP.
have p'fAx: p^'.-elt (fA x) by rewrite /p_elt ofAx pnatE.
by rewrite -ofAx dvdn_leq ?p'A_dv_p1 ?mem_morphim // -(subnKC p_gt1).
Qed.

End Five.

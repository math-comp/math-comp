(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div fintype finset.
Require Import prime fingroup morphism automorphism quotient gproduct gfunctor.
Require Import cyclic center commutator pgroup nilpotent sylow abelian hall.
Require Import maximal.
Require Import BGsection1 BGappendixAB.

(******************************************************************************)
(*   This file covers most of B & G section 6.                                *)
(* Theorem 6.4 is not proved, since it is not needed for the revised proof of *)
(* the odd order theorem.                                                     *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Section Six.

Implicit Type gT : finGroupType.
Implicit Type p : nat.

Section OneType.

Variable gT : finGroupType. 
Implicit Types G H K S U : {group gT}.

(* This is B & G, Theorem A.4(b) and 6.1, or Gorenstein 6.5.2, the main Hall- *)
(* Higman style p-stability result used in the proof of the Odd Order Theorem *)
Theorem odd_p_abelian_constrained p G :
  odd #|G| -> solvable G -> p.-abelian_constrained G.
Proof.
move/odd_p_stable=> stabG /solvable_p_constrained constrG.
exact: p_stable_abelian_constrained.
Qed.

(* Auxiliary results from AppendixAB, necessary to exploit the results below. *)
Definition center_Puig_char := BGappendixAB.center_Puig_char.
Definition trivg_center_Puig_pgroup := BGappendixAB.trivg_center_Puig_pgroup.

(* The two parts of B & G, Theorem 6.2 are established in BGappendixAB. *)
Theorem Puig_factorisation p G S :
  odd #|G| -> solvable G -> p.-Sylow(G) S -> 'O_p^'(G) * 'N_G('Z('L(S))) = G.
Proof. exact: BGappendixAB.Puig_factorization. Qed.

(* This is the main statement of B & G, Theorem 6.2. It is not used in the    *)
(* actual proof.                                                              *)
Theorem Puig_center_p'core_normal p G S :
  odd #|G| -> solvable G -> p.-Sylow(G) S -> 'O_p^'(G) * 'Z('L(S)) <| G.
Proof.
move=> oddG solG sylS; rewrite -{2}(Puig_factorisation _ _ sylS) //.
have sZL_G := subset_trans (char_sub (center_Puig_char S)) (pHall_sub sylS).
rewrite -!quotientK ?(subset_trans _ (gFnorm _ _)) ?subsetIl //.
by rewrite cosetpre_normal quotient_normal // normalSG.
Qed.

(* This is the second part (special case) of B & G, Theorem 6.2.              *)
Theorem Puig_center_normal p G S :
  odd #|G| -> solvable G -> p.-Sylow(G) S -> 'O_p^'(G) = 1 -> 'Z('L(S)) <| G.
Proof. exact: BGappendixAB.Puig_center_normal. Qed.

(* This is B & G, Lemma 6.3(a). *)
Lemma coprime_der1_sdprod K H G :
    K ><| H = G -> coprime #|K| #|H| -> solvable K -> K \subset G^`(1) -> 
  [~: K, H] = K /\ 'C_K(H) \subset K^`(1).
Proof.
case/sdprodP=> _ defG nKH tiKH coKH solK sKG'.
set K' := K^`(1); have [sK'K nK'K] := andP (der_normal 1 K : K' <| K).
have nK'H: H \subset 'N(K') := char_norm_trans (der_char 1 K) nKH.
set R := [~: K, H]; have sRK: R \subset K by rewrite commg_subl.
have [nRK nRH] := joing_subP (commg_norm K H : K <*> H \subset 'N(R)). 
have sKbK'H': K / R \subset (K / R)^`(1) * (H / R)^`(1).
  have defGb: (K / R) \* (H / R) = G / R.
    by rewrite -defG quotientMl ?cprodE // centsC quotient_cents2r.
  have [_ -> _ /=] := cprodP (der_cprod 1 defGb).
  by rewrite -quotient_der ?quotientS // -defG mul_subG.
have tiKbHb': K / R :&: (H / R)^`(1) = 1.
  by rewrite coprime_TIg // (coprimegS (der_sub 1 _)) ?coprime_morph.
have{sKbK'H' tiKbHb'} derKb: (K / R)^`(1) = K / R.
  by rewrite -{2}(setIidPr sKbK'H') -group_modl ?der_sub // setIC tiKbHb' mulg1.
have{derKb} Kb1: K / R = 1.
  rewrite (contraNeq (sol_der1_proper _ (subxx (K / R)))) ?quotient_sol //.
  by rewrite derKb properxx.
have{Kb1 sRK} defKH: [~: K, H] = K. 
  by apply/eqP; rewrite eqEsubset sRK -quotient_sub1 ?Kb1 //=.
split=> //; rewrite -quotient_sub1 ?subIset ?nK'K //= -/K'.
have cKaKa: abelian (K / K') := der_abelian 0 K.
rewrite coprime_quotient_cent ?quotient_norms ?coprime_morph //= -/K' -defKH.
by rewrite quotientR // coprime_abel_cent_TI ?quotient_norms ?coprime_morph.
Qed.

(* This is B & G, Lemma 6.3(b). It is apparently not used later. *)
Lemma prime_nil_der1_factor G :
    nilpotent G^`(1) -> prime #|G / G^`(1)| -> 
  Hall G G^`(1) /\ (forall H, G^`(1) ><| H = G -> G^`(1) = [~: G, H]).
Proof.
move=> nilG' /=; set G' := G^`(1); set p := #|G / G'| => p_pr.
have nsG'G: G' <| G := der_normal 1 G; have [sG'G nG'G] := andP nsG'G.
have nsG'p'G: 'O_p^'(G') <| G := char_normal_trans (pcore_char _ _) nsG'G.
have nG'p'G := normal_norm nsG'p'G; have solG' := nilpotent_sol nilG'.
have{nilG'} pGb: p.-group (G / 'O_p^'(G')).
  rewrite /pgroup card_quotient -?(Lagrange_index sG'G (pcore_sub _ _)) //=.
  rewrite pnat_mul // -card_quotient // pnat_id //= -pnatNK.
  by case/and3P: (nilpotent_pcore_Hall p^' nilG').
have{pGb} cycGb: cyclic (G / 'O_p^'(G')).
  apply: (cyclic_nilpotent_quo_der1_cyclic (pgroup_nil pGb)).
  rewrite -quotient_der // (isog_cyclic (third_isog _ _ _)) ?pcore_sub //.
  by apply: prime_cyclic.
have defG': G' = 'O_p^'(G').
  by apply/eqP; rewrite eqEsubset pcore_sub der1_min ?cyclic_abelian.
have hallG': Hall G G'.
  rewrite /Hall sG'G -?card_quotient // defG' //= -/p.
  by rewrite (p'nat_coprime (pcore_pgroup _ _)) ?pnat_id.
split=> // H defG; have [_ mulG'H nG'H tiG'H] := sdprodP defG.
rewrite -mulG'H commMG ?commg_normr // -derg1 (derG1P _) ?mulg1 //.
  by case/coprime_der1_sdprod: (defG); rewrite ?(coprime_sdprod_Hall_l defG).
rewrite (isog_abelian (quotient_isog nG'H tiG'H)) /= -/G'.
by rewrite -quotientMidl mulG'H der_abelian.
Qed.

Section PprodSubCoprime.

Variables K U H G : {group gT}.
Hypotheses (defG : K * U = G) (nsKG : K <| G).
Hypotheses (sHU : H \subset U) (coKH : coprime #|K| #|H|).
Let nKG : G \subset 'N(K). Proof. by case/andP: nsKG. Qed.
Let sKG : K \subset G. Proof. by case/mulG_sub: defG. Qed.
Let sUG : U \subset G. Proof. by case/mulG_sub: defG. Qed.
Let nKU : U \subset 'N(K). Proof. exact: subset_trans sUG nKG. Qed.
Let nKH : H \subset 'N(K). Proof. exact: subset_trans sHU nKU. Qed.

(* This is B & G, Lemma 6.5(a); note that we do not assume solvability. *)
Lemma pprod_focal_coprime : H :&: G^`(1) = H :&: U^`(1).
Proof.
set G' :=  G^`(1); set U' := U^`(1).
have [sU'U nU'U] := andP (der_normal 1 U : U' <| U).
have{nU'U} nU_U': U :&: _ \subset 'N(U') by move=> A; rewrite subIset ?nU'U.
suffices sHG'U': H :&: G' \subset U'.
  by rewrite -(setIidPl sHG'U') -setIA (setIidPr (dergS 1 sUG)).
rewrite -(setIidPr sHU) -setIA -quotient_sub1 // setICA setIC.
rewrite quotientGI ?subsetI ?sU'U ?dergS ?coprime_TIg //= -/G' -/U'.
have sUG'_UKb: (U :&: G') / U' \subset (U :&: K) / U'.
  rewrite quotientSK // -normC ?group_modr ?setIS //.
  by rewrite -quotientSK ?comm_subG ?quotient_der // -defG quotientMidl.
rewrite (coprimeSg sUG'_UKb) // -(card_isog (second_isog _)) //=.
rewrite setIA (setIidPl sU'U) coprime_morphl ?coprime_morphr //.
exact: coprimeSg (subsetIr U K) coKH.
Qed.

Hypothesis solG : solvable G.

(* This is B & G, Lemma 6.5(c). *)
Lemma pprod_trans_coprime g :
    g \in G -> H :^ g \subset U ->
  exists2 c, c \in 'C_K(H) & exists2 u, u \in U & g = c * u.
Proof.
rewrite -{1}defG => /mulsgP[k u Kk Uu defg] sHgU.
have [sK_KH sH_KH] := joing_sub (erefl (K <*> H)).
have hallH: \pi(H).-Hall(K <*> H :&: U) H.
  rewrite (pHall_subl _ (subsetIl _ _)) ?subsetI ?sH_KH //.
  rewrite /pHall sH_KH pgroup_pi /= joingC norm_joinEl // indexMg -indexgI.
  by rewrite -coprime_pi' ?cardG_gt0 //= coprime_sym coprime_TIg ?indexg1.
have{sHgU} hallHk: \pi(H).-Hall(K <*> H :&: U) (H :^ k).
  rewrite pHallE cardJg (card_Hall hallH) eqxx andbT subsetI andbC.
  rewrite -(conjSg _ _ u) (conjGid Uu) -conjsgM -defg sHgU.
  by rewrite sub_conjg conjGid // groupV (subsetP sK_KH).
have{hallH hallHk} [w KUw defHk]: exists2 w, w \in K :&: U & H :^ k = H :^ w.
  have sKHU_G: K <*> H :&: U \subset G by rewrite setIC subIset ?sUG.
  have [hw KHUhw ->] := Hall_trans (solvableS sKHU_G solG) hallHk hallH.
  have: hw \in H * (K :&: U) by rewrite group_modl // -norm_joinEl // joingC.
  by case/mulsgP=> h w Hh KUw ->; exists w; rewrite // conjsgM (conjGid Hh).
have{KUw} [Kw Uw] := setIP KUw.
exists (k * w^-1); last by exists (w * u); rewrite ?groupM // -mulgA mulKg.
by rewrite -coprime_norm_cent // !inE groupM ?groupV //= conjsgM defHk conjsgK.
Qed.

(* This is B & G, Lemma 6.5(b). *)
Lemma pprod_norm_coprime_prod : 'C_K(H) * 'N_U(H) = 'N_G(H).
Proof.
apply/eqP; rewrite eqEsubset mul_subG ?setISS ?cent_sub //=.
apply/subsetP=> g /setIP[Gg /normP nHg].
have [|c Cc [u Uu defg]] := pprod_trans_coprime Gg; first by rewrite nHg.
rewrite defg mem_mulg // !inE Uu -{2}nHg defg conjsgM conjSg (normP _) //=.
by case/setIP: Cc => _; exact: (subsetP (cent_sub H)).
Qed.

End PprodSubCoprime.

Section Plength1Prod.

Variables (p : nat) (G S : {group gT}).
Hypotheses (sylS : p.-Sylow(G) S) (pl1G : p.-length_1 G).
Let K := 'O_p^'(G).
Let sSG : S \subset G. Proof. by case/andP: sylS. Qed.
Let nsKG : K <| G. Proof. exact: pcore_normal. Qed.
Let sKG : K \subset G. Proof. by case/andP: nsKG. Qed.
Let nKG : G \subset 'N(K). Proof. by case/andP: nsKG. Qed.
Let nKS : S \subset 'N(K). Proof. exact: subset_trans sSG nKG. Qed.
Let coKS : coprime #|K| #|S|.
Proof. exact: p'nat_coprime (pcore_pgroup _ G) (pHall_pgroup sylS). Qed.
Let sSN : S \subset 'N_G(S). Proof. by rewrite subsetI sSG normG. Qed.

Let sylGbp : p.-Sylow(G / K) 'O_p(G / K).
Proof. by rewrite -plength1_pcore_quo_Sylow. Qed.

(* This is B & G, Lemma 6.6(a1); note that we do not assume solvability. *)
Lemma plength1_Sylow_prod : K * S = 'O_{p^',p}(G).
Proof.
by rewrite -quotientK 1?(eq_Hall_pcore sylGbp) ?quotient_pHall //= /K -pseries1.
Qed.

Let sylS_Gp'p : p.-Sylow('O_{p^',p}(G)) S.
Proof.
have [_ sSGp'p] := mulG_sub plength1_Sylow_prod.
exact: pHall_subl sSGp'p (pseries_sub _ _) sylS.
Qed.

(* This is B & G, Lemma 6.6(a2); note that we do not assume solvability. *)
Lemma plength1_Frattini : K * 'N_G(S) = G.
Proof.
rewrite -{2}(Frattini_arg _ sylS_Gp'p) ?pseries_normal //= -plength1_Sylow_prod.
by rewrite -mulgA [S * _]mulSGid // subsetI sSG normG.
Qed.
Local Notation defG := plength1_Frattini.

(* This is B & G, Lemma 6.6(b); note that we do not assume solvability. *)
Lemma plength1_Sylow_sub_der1 : S \subset G^`(1) -> S \subset ('N_G(S))^`(1).
Proof.
by move/setIidPl=> sSG'; apply/setIidPl; rewrite -(pprod_focal_coprime defG).
Qed.

Hypothesis solG : solvable G.

(* This is B & G, Lemma 6.6(c). *)
Lemma plength1_Sylow_trans (Y : {set gT}) g :
    Y \subset S -> g \in G -> Y :^ g \subset S -> 
  exists2 c, c \in 'C_G(Y) & exists2 u, u \in 'N_G(S) & g = c * u.
Proof.
rewrite -gen_subG -(gen_subG (Y :^ g)) genJ => sYS Gg sYgS.
have coKY := coprimegS sYS coKS.
have [sYN sYgN] := (subset_trans sYS sSN, subset_trans sYgS sSN).
have [c Cc defg] := pprod_trans_coprime defG nsKG sYN coKY solG Gg sYgN.
by exists c => //; apply: subsetP Cc; rewrite cent_gen setSI.
Qed.

(* This is B & G, Lemma 6.6(d). *)
Lemma plength1_Sylow_Jsub (Q : {group gT}) : 
    Q \subset G -> p.-group Q ->
  exists2 x, x \in 'C_G(Q :&: S) & Q :^ x \subset S. 
Proof.
move=> sQG pQ; have sQ_Gp'p: Q \subset 'O_{p^',p}(G).
  rewrite -sub_quotient_pre /= pcore_mod1 ?(subset_trans sQG) //.
  by rewrite (sub_Hall_pcore sylGbp) ?quotientS ?quotient_pgroup.
have [xy /= KSxy sQxyS] := Sylow_Jsub sylS_Gp'p sQ_Gp'p pQ.
rewrite -plength1_Sylow_prod in KSxy; have [x y Kx Sy def_xy] := mulsgP KSxy.
have{sQxyS} sQxS: Q :^ x \subset S.
  by rewrite -(conjSg _ _ y) (conjGid Sy) -conjsgM -def_xy.
exists x; rewrite // inE (subsetP sKG) //; apply/centP=> z; case/setIP=> Qz Sz.
apply/commgP; rewrite -in_set1 -set1gE -(coprime_TIg coKS) inE.
rewrite groupMl ?groupV ?memJ_norm ?(subsetP nKS) ?Kx //=.
by rewrite commgEr groupMr // (subsetP sQxS) ?memJ_conjg ?groupV.
Qed.

End Plength1Prod.

End OneType.

(* This is B & G, Theorem 6.7 *)
Theorem plength1_norm_pmaxElem gT p (G E L : {group gT}) :
    E \in 'E*_p(G) -> odd p -> solvable G -> p.-length_1 G ->
    L \subset G -> E \subset 'N(L) -> p^'.-group L -> 
  L \subset 'O_p^'(G). 
Proof.
move=> maxE p_odd solG pl1G sLG nEL p'L.
case p_pr: (prime p); last first.
  by rewrite pcore_pgroup_id // p'groupEpi mem_primes p_pr.
wlog Gp'1: gT G E L maxE solG pl1G sLG nEL p'L / 'O_p^'(G) = 1.
  set K := 'O_p^'(G); have [sKG nKG] := andP (pcore_normal _ G : K <| G).
  move/(_ _ (G / K) (E / K) (L / K))%G; rewrite morphim_sol ?plength1_quo //.
  rewrite morphimS ?morphim_norms ?quotient_pgroup // trivg_pcore_quotient.
  rewrite (quotient_sub1 (subset_trans sLG nKG)) => -> //.
  have [EpE _] := pmaxElemP maxE; have{EpE} [sEG abelE] := pElemP EpE.
  apply/pmaxElemP; rewrite inE quotient_abelem ?quotientS //.
  split=> // Fb; case/pElemP=> sFbG abelFb; have [pFb _ _] := and3P abelFb.
  have [S sylS sES] := Sylow_superset sEG (abelem_pgroup abelE).
  have [sSG pS _] := and3P sylS; have nKS := subset_trans sSG nKG.
  have: (E / K)%G \in 'E*_p(S / K).
    have: E \in 'E*_p(S) by rewrite (subsetP (pmaxElemS p sSG)) // inE maxE inE.
    have coKS: coprime #|K| #|S| := p'nat_coprime (pcore_pgroup _ _) pS.
    have [injK imK] := isomP (quotient_isom nKS (coprime_TIg coKS)).
    by rewrite -(injm_pmaxElem injK) ?imK ?inE //= morphim_restrm (setIidPr _).
  case/pmaxElemP=> _; apply; rewrite inE abelFb andbT.
  rewrite (sub_normal_Hall (quotient_pHall _ sylS)) //= -quotientMidl /= -/K.
  by rewrite plength1_Sylow_prod // quotient_pseries2 pcore_normal.
have [EpE _] := pmaxElemP maxE; have{EpE} [sEG abelE] := pElemP EpE.
have [S sylS sES] := Sylow_superset sEG (abelem_pgroup abelE).
have [sSG pS _] := and3P sylS; have oddS: odd #|S| := odd_pgroup_odd p_odd pS.
have defS: S :=: 'O_p(G) by apply eq_Hall_pcore; rewrite -?plength1_pcore_Sylow.
have coSL: coprime #|S| #|L| := pnat_coprime pS p'L.
have tiSL: S :&: L = 1 := coprime_TIg coSL.
have{solG} scSG: 'C_G(S) \subset S.
  by rewrite defS -Fitting_eq_pcore ?cent_sub_Fitting.
rewrite Gp'1 -tiSL subsetIidr (subset_trans _ scSG) // subsetI sLG /=.
have nSL: L \subset 'N(S) by rewrite (subset_trans sLG) // defS gFnorm.
have cLE: L \subset 'C(E).
  by rewrite (sameP commG1P trivgP) -tiSL setIC commg_subI ?(introT subsetIP).
have maxES: E \in 'E*_p(S) by rewrite (subsetP (pmaxElemS p sSG)) ?(maxE, inE).
have EpE: E \in 'E_p(S) by apply/setIdP.
by rewrite (coprime_odd_faithful_cent_abelem EpE) ?(pmaxElem_LdivP p_pr maxES).
Qed.

End Six.


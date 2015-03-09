(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div path fintype.
Require Import bigop finset prime fingroup morphism perm automorphism quotient.
Require Import action gproduct gfunctor pgroup cyclic center commutator.
Require Import gseries nilpotent sylow abelian maximal hall.
Require Import BGsection1 BGsection3 BGsection4 BGsection5 BGsection6.
Require Import BGsection7 BGsection9.

(******************************************************************************)
(*   This file covers B & G, section 10, including with the definitions:      *)
(*   \alpha(M) == the primes p such that M has p-rank at least 3.             *)
(*   \beta(M)  == the primes p in \alpha(M) such that Sylow p-subgroups of M  *)
(*                are not narrow (see BGsection5), i.e., such that M contains *)
(*                no maximal elementary abelian subgroups of rank 2. In a     *)
(*                minimal counter-example G, \beta(M) is the intersection of  *)
(*                \alpha(M) and \beta(G). Note that B & G refers to primes in *)
(*                \beta(G) as ``ideal'' primes, somewhat inconsistently.      *)
(*   \sigma(M) == the primes p such that there exists a p-Sylow subgroup P    *)
(*                of M whose normaliser (in the minimal counter-example) is   *)
(*                contained in M.                                             *)
(*   M`_\alpha == the \alpha(M)-core of M.                                    *)
(*   M`_\beta  == the \beta(M)-core of M.                                     *)
(*   M`_\sigma == the \sigma(M)-core of M.                                    *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Reserved Notation "\alpha ( M )" (at level 2, format "\alpha ( M )").
Reserved Notation "\beta ( M )" (at level 2, format "\beta ( M )").
Reserved Notation "\sigma ( M )" (at level 2, format "\sigma ( M )").

Reserved Notation "M `_ \alpha" (at level 3, format "M `_ \alpha").
Reserved Notation "M `_ \beta" (at level 3, format "M `_ \beta").
Reserved Notation "M `_ \sigma" (at level 3, format "M `_ \sigma").

Section Def.

Variable gT : finGroupType.
Implicit Type p : nat.

Variable M : {set gT}.

Definition alpha := [pred p | 2 < 'r_p(M)].
Definition alpha_core := 'O_alpha(M).
Canonical Structure alpha_core_group := Eval hnf in [group of alpha_core].

Definition beta :=
  [pred p | [forall (P : {group gT} | p.-Sylow(M) P), ~~ p.-narrow P]].
Definition beta_core := 'O_beta(M).
Canonical Structure beta_core_group := Eval hnf in [group of beta_core].

Definition sigma :=
  [pred p | [exists (P : {group gT} | p.-Sylow(M) P), 'N(P) \subset M]].
Definition sigma_core := 'O_sigma(M).
Canonical Structure sigma_core_group := Eval hnf in [group of sigma_core].

End Def.

Notation "\alpha ( M )" := (alpha M) : group_scope.
Notation "M `_ \alpha" := (alpha_core M) : group_scope.
Notation "M `_ \alpha" := (alpha_core_group M) : Group_scope.

Notation "\beta ( M )" := (beta M) : group_scope.
Notation "M `_ \beta" := (beta_core M) : group_scope.
Notation "M `_ \beta" := (beta_core_group M) : Group_scope.

Notation "\sigma ( M )" := (sigma M) : group_scope.
Notation "M `_ \sigma" := (sigma_core M) : group_scope.
Notation "M `_ \sigma" := (sigma_core_group M) : Group_scope.

Section CoreTheory.

Variable gT : minSimpleOddGroupType.
Local Notation G := (TheMinSimpleOddGroup gT).
Implicit Type x : gT.
Implicit Type P : {group gT}.

Section GenericCores.

Variables H K : {group gT}.

Lemma sigmaJ x : \sigma(H :^ x) =i \sigma(H).
Proof.
move=> p; apply/exists_inP/exists_inP=> [] [P sylP sNH]; last first.
  by exists (P :^ x)%G; rewrite ?pHallJ2 // normJ conjSg.
by exists (P :^ x^-1)%G; rewrite ?normJ ?sub_conjgV // -(pHallJ2 _ _ _ x) actKV.
Qed.

Lemma MsigmaJ x : (H :^ x)`_\sigma = H`_\sigma :^ x.
Proof. by rewrite /sigma_core -(eq_pcore H (sigmaJ x)) pcoreJ. Qed.

Lemma alphaJ x : \alpha(H :^ x) =i \alpha(H).
Proof. by move=> p; rewrite !inE /= p_rankJ. Qed.

Lemma MalphaJ x : (H :^ x)`_\alpha = H`_\alpha :^ x.
Proof. by rewrite /alpha_core -(eq_pcore H (alphaJ x)) pcoreJ. Qed.

Lemma betaJ x : \beta(H :^ x) =i \beta(H).
Proof.  
move=> p; apply/forall_inP/forall_inP=> nnSylH P sylP.
  by rewrite -(@narrowJ _ _ _ x) nnSylH ?pHallJ2.
by rewrite -(@narrowJ _ _ _ x^-1) nnSylH // -(pHallJ2 _ _ _ x) actKV.
Qed.

Lemma MbetaJ x : (H :^ x)`_\beta = H`_\beta :^ x.
Proof. by rewrite /beta_core -(eq_pcore H (betaJ x)) pcoreJ. Qed.

End GenericCores.

(* This remark appears at the start (p. 70) of B & G, Section 10, just after  *)
(* the definition of ideal, which we do not include, since it is redundant    *)
(* with the notation p \in \beta(G) that is used later.                       *)
Remark not_narrow_ideal p P : p.-Sylow(G) P -> ~~ p.-narrow P -> p \in \beta(G).
Proof.
move=> sylP nnP; apply/forall_inP=> Q sylQ.
by have [x _ ->] := Sylow_trans sylP sylQ; rewrite narrowJ.
Qed.

Section MaxCores.

Variables M : {group gT}.
Hypothesis maxM : M \in 'M.

(* This is the first inclusion in the remark following the preliminary        *)
(* definitions in B & G, p. 70.                                               *)
Remark beta_sub_alpha : {subset \beta(M) <= \alpha(M)}.
Proof. 
move=> p; rewrite !inE /= => /forall_inP nnSylM.
have [P sylP] := Sylow_exists p M; have:= nnSylM P sylP.
by rewrite negb_imply (p_rank_Sylow sylP) => /andP[].
Qed.

Remark alpha_sub_sigma : {subset \alpha(M) <= \sigma(M)}.
Proof.
move=> p a_p; have [P sylP] := Sylow_exists p M; have [sPM pP _ ] := and3P sylP.
have{a_p} rP: 2 < 'r(P) by rewrite (rank_Sylow sylP).
apply/exists_inP; exists P; rewrite ?uniq_mmax_norm_sub //.
exact: def_uniq_mmax (rank3_Uniqueness (mFT_pgroup_proper pP) rP) maxM sPM.
Qed.

Remark beta_sub_sigma : {subset \beta(M) <= \sigma(M)}.
Proof. by move=> p; move/beta_sub_alpha; exact: alpha_sub_sigma. Qed.

Remark Mbeta_sub_Malpha : M`_\beta \subset M`_\alpha.
Proof. exact: sub_pcore beta_sub_alpha. Qed.

Remark Malpha_sub_Msigma : M`_\alpha \subset M`_\sigma.
Proof. exact: sub_pcore alpha_sub_sigma. Qed.

Remark Mbeta_sub_Msigma : M`_\beta \subset M`_\sigma.
Proof. exact: sub_pcore beta_sub_sigma. Qed.

(* This is the first part of the remark just above B & G, Theorem 10.1. *)
Remark norm_sigma_Sylow p P :
  p \in \sigma(M) -> p.-Sylow(M) P -> 'N(P) \subset M.
Proof.
case/exists_inP=> Q sylQ sNPM sylP.
by case: (Sylow_trans sylQ sylP) => m mM ->; rewrite normJ conj_subG.
Qed.

(* This is the second part of the remark just above B & G, Theorem 10.1. *)
Remark sigma_Sylow_G p P : p \in \sigma(M) -> p.-Sylow(M) P -> p.-Sylow(G) P.
Proof.
move=> sMp sylP; apply: (mmax_sigma_Sylow maxM) => //.
exact: norm_sigma_Sylow sMp sylP.
Qed.

Lemma sigma_Sylow_neq1 p P : p \in \sigma(M) -> p.-Sylow(M) P -> P :!=: 1.
Proof.
move=> sMp /(norm_sigma_Sylow sMp); apply: contraTneq => ->.
by rewrite norm1 subTset -properT mmax_proper.
Qed.

Lemma sigma_sub_pi : {subset \sigma(M) <= \pi(M)}.
Proof.
move=> p sMp; have [P sylP]:= Sylow_exists p M.
by rewrite -p_rank_gt0 -(rank_Sylow sylP) rank_gt0 (sigma_Sylow_neq1 sMp sylP).
Qed.

Lemma predI_sigma_alpha : [predI \sigma(M) & \alpha(G)] =i \alpha(M).
Proof.
move=> p; rewrite inE /= -(andb_idl (@alpha_sub_sigma p)).
apply: andb_id2l => sMp; have [P sylP] := Sylow_exists p M.
by rewrite !inE -(rank_Sylow sylP) -(rank_Sylow (sigma_Sylow_G sMp sylP)).
Qed.

Lemma predI_sigma_beta : [predI \sigma(M) & \beta(G)] =i \beta(M).
Proof.
move=> p; rewrite inE /= -(andb_idl (@beta_sub_sigma p)).
apply: andb_id2l => sMp; apply/idP/forall_inP=> [bGp P sylP | nnSylM].
  exact: forall_inP bGp P (sigma_Sylow_G sMp sylP).
have [P sylP] := Sylow_exists p M.
exact: not_narrow_ideal (sigma_Sylow_G sMp sylP) (nnSylM P sylP).
Qed.

End MaxCores.

End CoreTheory.

Section Ten.

Variable gT : minSimpleOddGroupType.
Local Notation G := (TheMinSimpleOddGroup gT).

Implicit Type p : nat.
Implicit Type A E H K M N P Q R S V W X Y : {group gT}.

(* This is B & G, Theorem 10.1(d); note that we do not assume M is maximal. *)
Theorem sigma_Sylow_trans M p X g :
  p \in \sigma(M) -> p.-Sylow(M) X -> X :^ g \subset M -> g \in M.
Proof.
move=> sMp sylX sXgM; have pX := pHall_pgroup sylX. 
have [|h hM /= sXghX] := Sylow_Jsub sylX sXgM; first by rewrite pgroupJ.
by rewrite -(groupMr _ hM) (subsetP (norm_sigma_Sylow _ sylX)) ?inE ?conjsgM.
Qed.

(* This is B & G, Theorem 10.1 (a, b, c). *)
(* Part (e) of Theorem 10.1 is obviously stated incorrectly, and this is      *)
(* difficult to correct because it is not used in the rest of the proof.      *)
Theorem sigma_group_trans M p X :
     M \in 'M -> p \in \sigma(M) -> p.-group X ->
  [/\ (*a*) forall g, X \subset M -> X :^ g \subset M ->
            exists2 c, c \in 'C(X) & exists2 m, m \in M & g = c * m,
      (*b*) [transitive 'C(X), on [set Mg in M :^: G | X \subset Mg] | 'Js ]
    & (*c*) X \subset M -> 'C(X) * 'N_M(X) = 'N(X)].
Proof.
move=> maxM sMp pX; have defNM := norm_mmax maxM.
pose OM (Y : {set gT}) : {set {set gT}} := [set Mg in M :^: G | Y \subset Mg].
pose trM (Y : {set gT}) := [transitive 'C(Y), on OM Y | 'Js].
have actsOM Y: [acts 'N(Y), on OM Y | 'Js].
  apply/actsP=> z nYz Q; rewrite !inE -{1}(normP nYz) conjSg.
  by rewrite (acts_act (acts_orbit _ _ _)) ?inE.
have OMid Y: (gval M \in OM Y) = (Y \subset M) by rewrite inE orbit_refl.
have ntOM Y: p.-group Y -> exists B, gval B \in OM Y.
  have [S sylS] := Sylow_exists p M; have sSM := pHall_sub sylS.
  have sylS_G := sigma_Sylow_G maxM sMp sylS.
  move=> pY; have [g Gg sXSg] := Sylow_subJ sylS_G (subsetT Y) pY.
  by exists (M :^ g)%G; rewrite inE mem_orbit // (subset_trans sXSg) ?conjSg.
have maxOM Y H: gval H \in OM Y -> H \in 'M.
  by case/setIdP=> /imsetP[g _ /val_inj->]; rewrite mmaxJ.
have part_c Y H: trM Y -> gval H \in OM Y -> 'C(Y) * 'N_H(Y) = 'N(Y).
  move=> trMY O_H; rewrite -(norm_mmax (maxOM Y H O_H)) -(astab1Js H) setIC.
  have [sCN nCN] := andP (cent_normal Y); rewrite -normC 1?subIset ?nCN //.
  by apply/(subgroup_transitiveP O_H); rewrite ?(atrans_supgroup sCN) ?actsOM.
suffices trMX: trM X.
  do [split; rewrite // -OMid] => [g O_M sXgM |]; last exact: part_c.
  have O_Mg': M :^ g^-1 \in OM X by rewrite inE mem_orbit -?sub_conjg ?inE.
  have [c Cc /= Mc] := atransP2 trMX O_M O_Mg'; exists c^-1; rewrite ?groupV //.
  by exists (c * g); rewrite ?mulKg // -defNM inE conjsgM -Mc conjsgKV.
elim: {X}_.+1 {-2}X (ltnSn (#|G| - #|X|)) => // n IHn X geXn in pX *.
have{n IHn geXn} IHX Y: X \proper Y -> p.-group Y -> trM Y.
  move=> ltXY; apply: IHn; rewrite -ltnS (leq_trans _ geXn) // ltnS.
  by rewrite ltn_sub2l ?(leq_trans (proper_card ltXY)) // cardsT max_card.
have [-> | ntX] := eqsVneq X 1.
  rewrite /trM cent1T /OM setIdE (setIidPl _) ?atrans_orbit //.
  by apply/subsetP=> Mg; case/imsetP=> g _ ->; rewrite inE sub1G.
pose L := 'N(X)%G; have ltLG := mFT_norm_proper ntX (mFT_pgroup_proper pX).
have IH_L: {in OM X &, forall B B',
  B != B' -> exists2 X1, X \proper gval X1 & p.-Sylow(B :&: L) X1}.
- move=> _ _ /setIdP[/imsetP[a Ga ->] sXMa] /setIdP[/imsetP[b Gb ->] sXMb].
  move=> neqMab.
  have [S sylS sXS] := Sylow_superset sXMa pX; have [sSMa pS _] := and3P sylS.
  have [defS | ltXS] := eqVproper sXS.
    case/eqP: neqMab; apply: (canRL (actKV _ _)); apply: (act_inj 'Js a).
    rewrite /= -conjsgM [_ :^ _]conjGid ?(sigma_Sylow_trans _ sylS) ?sigmaJ //.
    by rewrite -defS conjsgM conjSg sub_conjgV.
  have pSL: p.-group (S :&: L) := pgroupS (subsetIl _ _) pS.
  have [X1 sylX1 sNX1] := Sylow_superset (setSI L sSMa) pSL; exists X1 => //.
  by rewrite (proper_sub_trans (nilpotent_proper_norm (pgroup_nil pS) _)).
have [M1 O_M1] := ntOM X pX; apply/imsetP; exists (gval M1) => //; apply/eqP.
rewrite eqEsubset andbC acts_sub_orbit ?(subset_trans (cent_sub X)) // O_M1 /=.
apply/subsetP=> M2 O_M2.
have [-> | neqM12] := eqsVneq M1 M2; first exact: orbit_refl.
have [|X2 ltXX2 sylX2] := IH_L _ _ O_M2 O_M1; first by rewrite eq_sym.
have{IH_L neqM12} [X1 ltXX1 sylX1] := IH_L _ _ O_M1 O_M2 neqM12.
have [[sX1L1 pX1 _] [sX2L2 pX2 _]] := (and3P sylX1, and3P sylX2).
have [[sX1M1 sX1L] [sX2M2 sX2L]] := (subsetIP sX1L1, subsetIP sX2L2).
have [P sylP sX1P] := Sylow_superset sX1L pX1; have [sPL pP _] := and3P sylP.
have [M0 O_M0] := ntOM P pP; have [MG_M0 sPM0] := setIdP O_M0.
have [t Lt sX2Pt] := Sylow_subJ sylP sX2L pX2.
have [sX1M0 ltXP] := (subset_trans sX1P sPM0, proper_sub_trans ltXX1 sX1P).
have M0C_M1: gval M1 \in orbit 'Js 'C(X) M0.
  rewrite (subsetP (imsetS _ (centS (proper_sub ltXX1)))) // -orbitE.
  by rewrite (atransP (IHX _ ltXX1 pX1)) inE ?MG_M0 //; case/setIdP: O_M1 => ->.
have M0tC_M2: M2 \in orbit 'Js 'C(X) (M0 :^ t).
  rewrite (subsetP (imsetS _ (centS (proper_sub ltXX2)))) // -orbitE.
  rewrite (atransP (IHX _ ltXX2 pX2)) inE; first by case/setIdP: O_M2 => ->.
  rewrite (acts_act (acts_orbit _ _ _)) ?inE ?MG_M0 //.
  by rewrite (subset_trans sX2Pt) ?conjSg.
rewrite (orbit_transl M0C_M1) (orbit_transr _ M0tC_M2).
have maxM0 := maxOM _ _ O_M0; have ltMG := mmax_proper maxM0.
have [rPgt2 | rPle2] := ltnP 2 'r(P).
  have uP: P \in 'U by rewrite rank3_Uniqueness ?(mFT_pgroup_proper pP).
  have uP_M0: 'M(P) = [set M0] := def_uniq_mmax uP maxM0 sPM0.
  by rewrite conjGid ?orbit_refl ?(subsetP (sub_uniq_mmax uP_M0 sPL ltLG)).
have pl1L: p.-length_1 L.
  have [oddL]: odd #|L| /\ 'r_p(L) <= 2 by rewrite mFT_odd -(rank_Sylow sylP).
  by case/rank2_der1_complement; rewrite ?mFT_sol ?plength1_pseries2_quo.
have [|u v nLPu Lp'_v ->] := imset2P (_ : t \in 'N_L(P) * 'O_p^'(L)).
  by rewrite normC ?plength1_Frattini // subIset ?gFnorm.
rewrite actM (orbit_transr _ (mem_orbit _ _ _)); last first.
  have coLp'X: coprime #|'O_p^'(L)| #|X| := p'nat_coprime (pcore_pgroup _ _) pX.
  apply: subsetP Lp'_v; have [sLp'L nLp'L] := andP (pcore_normal p^' L).
  rewrite -subsetIidl -coprime_norm_cent ?subsetIidl //.
  exact: subset_trans (normG X) nLp'L.
have [|w x nM0Pw cPx ->] := imset2P (_ : u \in 'N_M0(P) * 'C(P)).
  rewrite normC ?part_c ?IHX //; first by case/setIP: nLPu.
  by rewrite setIC subIset ?cent_norm.
rewrite actM /= conjGid ?mem_orbit //; last by case/setIP: nM0Pw.
by rewrite (subsetP (centS (subset_trans (proper_sub ltXX1) sX1P))).
Qed.

Section OneMaximal.

Variable M : {group gT}.
Hypothesis maxM : M \in 'M.

Let ltMG := mmax_proper maxM.
Let solM := mmax_sol maxM.

Let aMa : \alpha(M).-group (M`_\alpha). Proof. exact: pcore_pgroup. Qed.
Let nsMaM : M`_\alpha <| M. Proof. exact: pcore_normal. Qed.
Let sMaMs : M`_\alpha \subset M`_\sigma. Proof. exact: Malpha_sub_Msigma. Qed.

Let F := 'F(M / M`_\alpha).
Let nsFMa : F <| M / M`_\alpha. Proof. exact: Fitting_normal. Qed.

Let alpha'F : \alpha(M)^'.-group F.
Proof.
rewrite -[F](nilpotent_pcoreC \alpha(M) (Fitting_nil _)) -Fitting_pcore /=.
by rewrite trivg_pcore_quotient (trivgP (Fitting_sub 1)) dprod1g pcore_pgroup.
Qed.

Let Malpha_quo_sub_Fitting : M^`(1) / M`_\alpha \subset F.
Proof.
have [/= K defF sMaK nsKM] := inv_quotientN nsMaM nsFMa; rewrite -/F in defF.
have [sKM _] := andP nsKM; have nsMaK: M`_\alpha <| K := normalS sMaK sKM nsMaM.
have [[_ nMaK] [_ nMaM]] := (andP nsMaK, andP nsMaM).
have hallMa: \alpha(M).-Hall(K) M`_\alpha.
  by rewrite /pHall sMaK pcore_pgroup -card_quotient -?defF.
have [H hallH] := Hall_exists \alpha(M)^' (solvableS sKM solM).
have{hallH} defK := sdprod_normal_p'HallP nsMaK hallH hallMa.
have{defK} [_ sHK defK nMaH tiMaH] := sdprod_context defK.
have{defK} isoHF: H \isog F by rewrite [F]defF -defK quotientMidl quotient_isog.
have{sHK nMaH} sHM := subset_trans sHK sKM.
have{tiMaH isoHF sHM H} rF: 'r(F) <= 2.
  rewrite -(isog_rank isoHF); have [p p_pr -> /=] := rank_witness H.
  have [|a_p] := leqP 'r_p(M) 2; first exact: leq_trans (p_rankS p sHM).
  rewrite 2?leqW // leqNgt p_rank_gt0 /= (card_isog isoHF) /= -/F.
  exact: contraL (pnatPpi alpha'F) a_p.
by rewrite quotient_der // rank2_der1_sub_Fitting ?mFT_quo_odd ?quotient_sol.
Qed.

Let sigma_Hall_sub_der1 H : \sigma(M).-Hall(M) H -> H \subset M^`(1).
Proof.
move=> hallH; have [sHM sH _] := and3P hallH.
rewrite -(Sylow_gen H) gen_subG; apply/bigcupsP=> P /SylowP[p p_pr sylP].
have [-> | ntP] := eqsVneq P 1; first by rewrite sub1G.
have [sPH pP _] := and3P sylP; have{ntP} [_ p_dv_P _] := pgroup_pdiv pP ntP.
have{p_dv_P} s_p: p \in \sigma(M) := pgroupP (pgroupS sPH sH) p p_pr p_dv_P. 
have{sylP} sylP: p.-Sylow(M) P := subHall_Sylow hallH s_p sylP.
have [sPM nMP] := (pHall_sub sylP, norm_sigma_Sylow s_p sylP).
have sylP_G := sigma_Sylow_G maxM s_p sylP.
have defG': G^`(1) = G.
  have [_ simpG] := simpleP _ (mFT_simple gT).
  by have [?|//] := simpG _ (der_normal 1 _); case/derG1P: (mFT_nonAbelian gT).
rewrite -subsetIidl -{1}(setIT P) -defG'.
rewrite (focal_subgroup_gen sylP_G) (focal_subgroup_gen sylP) genS //.
apply/subsetP=> _ /imset2P[x g Px /setIdP[Gg Pxg] ->]. 
pose X := <[x]>; have sXM : X \subset M by rewrite cycle_subG (subsetP sPM).
have sXgM: X :^ g \subset M by rewrite -cycleJ cycle_subG (subsetP sPM).
have [trMX _ _] := sigma_group_trans maxM s_p (mem_p_elt pP Px).
have [c cXc [m Mm def_g]] := trMX _ sXM sXgM; rewrite cent_cycle in cXc.
have def_xg: x ^ g = x ^ m by rewrite def_g conjgM /conjg -(cent1P cXc) mulKg.
by rewrite commgEl def_xg -commgEl mem_imset2 // inE Mm -def_xg.
Qed.

(* This is B & G, Theorem 10.2(a1). *) 
Theorem Malpha_Hall : \alpha(M).-Hall(M) M`_\alpha.
Proof.
have [H hallH] := Hall_exists \sigma(M) solM; have [sHM sH _] := and3P hallH.
rewrite (subHall_Hall hallH (alpha_sub_sigma maxM)) // /pHall pcore_pgroup /=.
rewrite -(card_quotient (subset_trans sHM (normal_norm nsMaM))) -pgroupE.
rewrite (subset_trans sMaMs) ?pcore_sub_Hall ?(pgroupS _ alpha'F) //=.
exact: subset_trans (quotientS _ (sigma_Hall_sub_der1 hallH)) _.
Qed.

(* This is B & G, Theorem 10.2(b1). *) 
Theorem Msigma_Hall : \sigma(M).-Hall(M) M`_\sigma.
Proof. 
have [H hallH] := Hall_exists \sigma(M) solM; have [sHM sH _] := and3P hallH.
rewrite /M`_\sigma (normal_Hall_pcore hallH) // -(quotientGK nsMaM).
rewrite -(quotientGK (normalS _ sHM nsMaM)) ?cosetpre_normal //; last first.
  by rewrite (subset_trans sMaMs) ?pcore_sub_Hall.
have hallHa: \sigma(M).-Hall(F) (H / M`_\alpha).
  apply: pHall_subl (subset_trans _ Malpha_quo_sub_Fitting) (Fitting_sub _) _.
    by rewrite quotientS ?sigma_Hall_sub_der1.
  exact: quotient_pHall (subset_trans sHM (normal_norm nsMaM)) hallH.
rewrite (nilpotent_Hall_pcore (Fitting_nil _) hallHa) /=.
exact: char_normal_trans (pcore_char _ _) nsFMa.
Qed.

Lemma pi_Msigma : \pi(M`_\sigma) =i \sigma(M).
Proof.
move=> p; apply/idP/idP=> [|s_p /=]; first exact: pnatPpi (pcore_pgroup _ _).
by rewrite (card_Hall Msigma_Hall) pi_of_part // inE /= sigma_sub_pi.
Qed.

(* This is B & G, Theorem 10.2(b2). *) 
Theorem Msigma_Hall_G : \sigma(M).-Hall(G) M`_\sigma.
Proof. 
rewrite pHallE subsetT /= eqn_dvd {1}(card_Hall Msigma_Hall).
rewrite partn_dvd ?cardG_gt0 ?cardSg ?subsetT //=.
apply/dvdn_partP; rewrite ?part_gt0 // => p.
rewrite pi_of_part ?cardG_gt0 // => /andP[_ s_p].
rewrite partn_part => [|q /eqnP-> //].
have [P sylP] := Sylow_exists p M; have [sPM pP _] := and3P sylP.
rewrite -(card_Hall (sigma_Sylow_G _ _ sylP)) ?cardSg //.
by rewrite (sub_Hall_pcore Msigma_Hall) ?(pi_pgroup pP).
Qed.

(* This is B & G, Theorem 10.2(a2). *) 
Theorem Malpha_Hall_G : \alpha(M).-Hall(G) M`_\alpha.
Proof.
apply: subHall_Hall Msigma_Hall_G (alpha_sub_sigma maxM) _.
exact: pHall_subl sMaMs (pcore_sub _ _) Malpha_Hall.
Qed.

(* This is B & G, Theorem 10.2(c). *)
Theorem Msigma_der1 : M`_\sigma \subset M^`(1).
Proof. exact: sigma_Hall_sub_der1 Msigma_Hall. Qed.

(* This is B & G, Theorem 10.2(d1). *)
Theorem Malpha_quo_rank2 : 'r(M / M`_\alpha) <= 2.
Proof.
have [p p_pr ->] := rank_witness (M / M`_\alpha).
have [P sylP] := Sylow_exists p M; have [sPM pP _] := and3P sylP.
have nMaP := subset_trans sPM (normal_norm nsMaM).
rewrite -(rank_Sylow (quotient_pHall nMaP sylP)) /= leqNgt.
have [a_p | a'p] := boolP (p \in \alpha(M)).
  by rewrite quotientS1 ?rank1 ?(sub_Hall_pcore Malpha_Hall) ?(pi_pgroup pP).
rewrite -(isog_rank (quotient_isog _ _)) ?coprime_TIg ?(rank_Sylow sylP) //.
exact: pnat_coprime aMa (pi_pnat pP _).
Qed.

(* This is B & G, Theorem 10.2(d2). *)
Theorem Malpha_quo_nil : nilpotent (M^`(1) / M`_\alpha).
Proof. exact: nilpotentS Malpha_quo_sub_Fitting (Fitting_nil _). Qed.

(* This is B & G, Theorem 10.2(e). *)
Theorem Msigma_neq1 : M`_\sigma :!=: 1.
Proof.
without loss Ma1: / M`_\alpha = 1.
  by case: eqP => // Ms1 -> //; apply/trivgP; rewrite -Ms1 Malpha_sub_Msigma.
have{Ma1} rFM: 'r('F(M)) <= 2.
  rewrite (leq_trans _ Malpha_quo_rank2) // Ma1.
  by rewrite -(isog_rank (quotient1_isog _)) rankS ?Fitting_sub.
pose q := max_pdiv #|M|; pose Q := 'O_q(M)%G.
have sylQ: q.-Sylow(M) Q := rank2_max_pcore_Sylow (mFT_odd M) solM rFM.
have piMq: q \in \pi(M) by rewrite pi_max_pdiv cardG_gt1 mmax_neq1.
have{piMq} ntQ: Q :!=: 1 by rewrite -rank_gt0 (rank_Sylow sylQ) p_rank_gt0.
rewrite (subG1_contra _ ntQ) ?(sub_Hall_pcore Msigma_Hall) ?pcore_sub //.
rewrite (pi_pgroup (pcore_pgroup _ _)) //; apply/exists_inP; exists Q => //.
by rewrite (mmax_normal maxM) ?pcore_normal.
Qed.

(* This is B & G, Lemma 10.3. *)
Theorem cent_alpha'_uniq X :
     X \subset M -> \alpha(M)^'.-group X -> 'r('C_(M`_\alpha)(X)) >= 2 ->
  'C_M(X)%G \in 'U.
Proof.
have ltM_G := sub_proper_trans (subsetIl M _) ltMG.
move=> sXM a'X; have [p p_pr -> rCX] := rank_witness 'C_(M`_\alpha)(X).
have{rCX} [B EpB] := p_rank_geP rCX; have{EpB} [sBCX abelB dimB] := pnElemP EpB.
have [[sBMa cXB] [pB cBB _]] := (subsetIP sBCX, and3P abelB).
have rMa: 1 < 'r_p(M`_\alpha) by rewrite -dimB -p_rank_abelem ?p_rankS.
have{rMa} a_p: p \in \alpha(M) by rewrite (pnatPpi aMa) // -p_rank_gt0 ltnW.
have nBX: X \subset 'N(B) by rewrite cents_norm // centsC.
have coMaX: coprime #|M`_\alpha| #|X| := pnat_coprime aMa a'X.
have [sMaM nMaM] := andP nsMaM; have solMa := solvableS sMaM solM.
have nMaX := subset_trans sXM nMaM.
have [P [sylP nPX sBP]] := coprime_Hall_subset nMaX coMaX solMa sBMa pB nBX.
have [sPMa pP _] := and3P sylP; have sPM := subset_trans sPMa sMaM.
have EpCB: B \in 'E_p^2('C_P(B)) by rewrite !inE subsetI sBP abelB dimB !andbT.
have: 1 < 'r_p('C_P(B)) by apply/p_rank_geP; exists B.
rewrite leq_eqVlt; case: ltngtP => // rCPB _.
  apply: (uniq_mmaxS (subset_trans sBCX (setSI _ sMaM))) => //=.
  have pCPB := pgroupS (subsetIl P 'C(B)) pP; rewrite -rank_pgroup // in rCPB.
  have: 2 < 'r('C(B)) by rewrite (leq_trans rCPB) ?rankS ?subsetIr.
  by apply: cent_rank3_Uniqueness; rewrite -dimB -rank_abelem.
have cPX: P \subset 'C(X).
  have EpPB: B \in 'E_p(P) by exact/pElemP. 
  have coPX: coprime #|P| #|X| := coprimeSg sPMa coMaX.
  rewrite centsC (coprime_odd_faithful_cent_abelem EpPB) ?mFT_odd //.
  rewrite -(setIid 'C(B)) setIA (pmaxElem_LdivP p_pr _) 1?centsC //.
  by rewrite (subsetP (p_rankElem_max _ _)) -?rCPB.
have sylP_M := subHall_Sylow Malpha_Hall a_p sylP.
have{sylP_M} rP: 2 < 'r(P) by rewrite (rank_Sylow sylP_M).
by rewrite rank3_Uniqueness ?(leq_trans rP (rankS _)) //= subsetI sPM.
Qed.

Variable p : nat.

(* This is B & G, Lemma 10.4(a). *)
(* We omit the redundant assumption p \in \pi(M). *)
Lemma der1_quo_sigma' : p %| #|M / M^`(1)| -> p \in \sigma(M)^'.
Proof.
apply: contraL => /= s_p; have piMp := sigma_sub_pi maxM s_p.
have p_pr: prime p by move: piMp; rewrite mem_primes; case/andP.
rewrite -p'natE ?(pi'_p'nat _ s_p) // -pgroupE -partG_eq1.
rewrite -(card_Hall (quotient_pHall _ Msigma_Hall)) /=; last first.
  exact: subset_trans (pcore_sub _ _) (der_norm _ _).
by rewrite quotientS1 ?cards1 // Msigma_der1.
Qed.

Hypothesis s'p : p \in \sigma(M)^'.

(* This is B & G, Lemma 10.4(b). *)
(* We do not need the assumption M`_\alpha != 1; the assumption p \in \pi(M)  *)
(* is restated as P != 1.                                                     *)
Lemma cent1_sigma'_Zgroup P :
    p.-Sylow(M) P -> P :!=: 1 ->
  exists x,
    [/\ x \in 'Ohm_1('Z(P))^#, 'M('C[x]) != [set M] & Zgroup 'C_(M`_\alpha)[x]].
Proof.
move=> sylP ntP; set T := 'Ohm_1(_); have [sPM pP _] := and3P sylP.
have [charT nilP] := (char_trans (Ohm_char 1 _) (center_char P), pgroup_nil pP).
suffices [x Tx not_uCx]: exists2 x, x \in T^# & 'M('C[x]) != [set M].
  exists x; split=> //; rewrite odd_rank1_Zgroup ?mFT_odd //= leqNgt.
  apply: contra not_uCx; rewrite -cent_cycle; set X := <[x]> => rCMaX.
  have{Tx} [ntX Tx] := setD1P Tx; rewrite -cycle_eq1 -/X in ntX.
  have sXP: X \subset P by rewrite cycle_subG (subsetP (char_sub charT)).
  rewrite (@def_uniq_mmaxS _ M 'C_M(X)) ?subsetIr ?mFT_cent_proper //.
  apply: def_uniq_mmax; rewrite ?subsetIl //.
  rewrite cent_alpha'_uniq ?(subset_trans sXP) ?(pi_pgroup (pgroupS sXP pP)) //.
  by apply: contra s'p; apply: alpha_sub_sigma.
apply/exists_inP; rewrite -negb_forall_in; apply: contra s'p.
move/forall_inP => uCT; apply/exists_inP; exists P => //.
apply/subsetP=> u nPu; have [y Ty]: exists y, y \in T^#.
  by apply/set0Pn; rewrite setD_eq0 subG1 Ohm1_eq1 center_nil_eq1.
rewrite -(norm_mmax maxM) (sameP normP eqP) (inj_eq (@group_inj gT)) -in_set1.
have Tyu: y ^ u \in T^#.
  by rewrite memJ_norm // normD1 (subsetP (char_norms charT)).
by rewrite -(eqP (uCT _ Tyu)) -conjg_set1 normJ mmax_ofJ (eqP (uCT _ Ty)) set11.
Qed.

(* This is B & G, Lemma 10.4(c), part 1. *)
(* The redundant assumption p \in \pi(M) is omitted. *)
Lemma sigma'_rank2_max : 'r_p(M) = 2 -> 'E_p^2(M) \subset 'E*_p(G).
Proof.
move=> rpM; apply: contraR s'p => /subsetPn[A Ep2A not_maxA].
have{Ep2A} [sAM abelA dimA] := pnElemP Ep2A; have [pA _ _] := and3P abelA.
have [P sylP sAP] := Sylow_superset sAM pA; have [_ pP _] := and3P sylP.
apply/exists_inP; exists P; rewrite ?uniq_mmax_norm_sub //.
apply: def_uniq_mmaxS (mFT_pgroup_proper pP) (def_uniq_mmax _ _ sAM) => //.
by rewrite (@nonmaxElem2_Uniqueness _ p) // !(not_maxA, inE) abelA dimA subsetT.
Qed.

(* This is B & G, Lemma 10.4(c), part 2 *)
(* The redundant assumption p \in \pi(M) is omitted. *)
Lemma sigma'_rank2_beta' : 'r_p(M) = 2 -> p \notin \beta(G).
Proof.
move=> rpM; rewrite -[p \in _]negb_exists_in negbK; apply/exists_inP.
have [A Ep2A]: exists A, A \in 'E_p^2(M) by apply/p_rank_geP; rewrite rpM.
have [_ abelA dimA] := pnElemP Ep2A; have [pA _] := andP abelA.
have [P sylP sAP] := Sylow_superset (subsetT _) pA.
exists P; rewrite ?inE //; apply/implyP=> _; apply/set0Pn.
exists A; rewrite 3!inE abelA dimA sAP (subsetP (pmaxElemS _ (subsetT P))) //.
by rewrite inE (subsetP (sigma'_rank2_max rpM)) // inE.
Qed.

(* This is B & G, Lemma 10.5, part 1; the condition on X has been weakened,   *)
(* because the proof of Lemma 12.2(a) requires the stronger result.           *)
Lemma sigma'_norm_mmax_rank2 X : p.-group X -> 'N(X) \subset M -> 'r_p(M) = 2.
Proof.
move=> pX sNX_M; have sXM: X \subset M := subset_trans (normG X) sNX_M.
have [P sylP sXP] := Sylow_superset sXM pX; have [sPM pP _] := and3P sylP.
apply: contraNeq s'p; case: ltngtP => // rM _; last exact: alpha_sub_sigma.
apply/exists_inP; exists P; rewrite ?(subset_trans _ sNX_M) ?char_norms //.
rewrite sub_cyclic_char // (odd_pgroup_rank1_cyclic pP) ?mFT_odd //.
by rewrite (p_rank_Sylow sylP).
Qed.

(* This is B & G, Lemma 10.5, part 2. We omit the second claim of B & G 10.5  *)
(* as it is an immediate consequence of sigma'_rank2_beta' (i.e., 10.4(c)).   *)
Lemma sigma'1Elem_sub_p2Elem X :
    X \in 'E_p^1(G) -> 'N(X) \subset M -> 
  exists2 A, A \in 'E_p^2(G) & X \subset A.
Proof.
move=> EpX sNXM; have sXM := subset_trans (normG X) sNXM.
have [[_ abelX dimX] p_pr] := (pnElemP EpX, pnElem_prime EpX).
have pX := abelem_pgroup abelX; have rpM2 := sigma'_norm_mmax_rank2 pX sNXM.
have [P sylP sXP] := Sylow_superset sXM pX; have [sPM pP _] := and3P sylP.
pose T := 'Ohm_1('Z(P)); pose A := X <*> T; have nilP := pgroup_nil pP.
have charT: T \char P := char_trans (Ohm_char 1 _) (center_char P).
have neqTX: T != X.
  apply: contraNneq s'p => defX; apply/exists_inP; exists P => //. 
  by rewrite (subset_trans _ sNXM) // -defX char_norms.
have rP: 'r(P) = 2 by rewrite (rank_Sylow sylP) rpM2.
have ntT: T != 1 by rewrite Ohm1_eq1 center_nil_eq1 // -rank_gt0 rP.
have sAP: A \subset P by rewrite join_subG sXP char_sub.
have cTX: T \subset 'C(X) := centSS (Ohm_sub 1 _) sXP (subsetIr P _).
have{cTX} defA: X \* T = A by rewrite cprodEY.
have{defA} abelA : p.-abelem A.
  have pZ: p.-group 'Z(P) := pgroupS (center_sub P) pP.
  by rewrite (cprod_abelem _ defA) abelX Ohm1_abelem ?center_abelian.
exists [group of A]; last exact: joing_subl.
rewrite !inE subsetT abelA eqn_leq -{1}rP -{1}(rank_abelem abelA) rankS //=.
rewrite -dimX (properG_ltn_log (pgroupS sAP pP)) // /proper join_subG subxx.
rewrite joing_subl /=; apply: contra ntT => sTX; rewrite eqEsubset sTX in neqTX.
by rewrite -(setIidPr sTX) prime_TIg ?(card_pnElem EpX).
Qed.

End OneMaximal.

(* This is B & G, Theorem 10.6. *)
Theorem mFT_proper_plength1 p H : H \proper G -> p.-length_1 H. 
Proof.
case/mmax_exists=> M /setIdP[maxM sHM].
suffices{H sHM}: p.-length_1 M by apply: plength1S.
have [solM oddM] := (mmax_sol maxM, mFT_odd M).
have [rpMle2 | a_p] := leqP 'r_p(M) 2.
  by rewrite plength1_pseries2_quo; case/rank2_der1_complement: rpMle2.
pose Ma := M`_\alpha; have hallMa: \alpha(M).-Hall(M) Ma := Malpha_Hall maxM.
have [[K hallK] [sMaM aMa _]] := (Hall_exists \alpha(M)^' solM, and3P hallMa).
have defM: Ma ><| K = M by apply/sdprod_Hall_pcoreP.
have{aMa} coMaK: coprime #|Ma| #|K| := pnat_coprime aMa (pHall_pgroup hallK).
suffices{a_p hallMa}: p.-length_1 Ma.
  rewrite !p_elt_gen_length1 /p_elt_gen setIdE /= -/Ma -(setIidPl sMaM) -setIA.
  rewrite -(setIdE M) (setIidPr _) //; apply/subsetP=> x; case/setIdP=> Mx p_x.
  by rewrite (mem_Hall_pcore hallMa) /p_elt ?(pi_pnat p_x).
have{sMaM} <-: [~: Ma, K] = Ma.
  have sMaMs: Ma \subset M`_\sigma := Malpha_sub_Msigma maxM.
  have sMaM': Ma \subset M^`(1) := subset_trans sMaMs (Msigma_der1 maxM).
  by have [] := coprime_der1_sdprod defM coMaK (solvableS sMaM solM) sMaM'.
have [q q_pr q_dv_Mq]: {q | prime q & q %| #|M / M^`(1)| }.
  apply: pdivP; rewrite card_quotient ?der_norm // indexg_gt1 proper_subn //.
  by rewrite (sol_der1_proper solM) ?mmax_neq1.
have s'q: q \in \sigma(M)^' by apply: der1_quo_sigma' q_dv_Mq.
have [Q sylQ] := Sylow_exists q K; have [sQK qQ _] := and3P sylQ.
have a'q: q \in \alpha(M)^' by apply: contra s'q; apply: alpha_sub_sigma.
have{a'q sylQ hallK} sylQ: q.-Sylow(M) Q := subHall_Sylow hallK a'q sylQ.
have{q_dv_Mq} ntQ: Q :!=: 1.
  rewrite -rank_gt0 (rank_Sylow sylQ) p_rank_gt0 mem_primes q_pr cardG_gt0.
  exact: dvdn_trans q_dv_Mq (dvdn_quotient _ _).
have{s'q sylQ ntQ} [x [Q1x _ ZgCx]] := cent1_sigma'_Zgroup maxM s'q sylQ ntQ.
have{Q1x} [ntx Q1x] := setD1P Q1x.
have sZQ := center_sub Q; have{sQK} sZK := subset_trans sZQ sQK.
have{sZK} Kx: x \in K by rewrite (subsetP sZK) // (subsetP (Ohm_sub 1 _)).
have{sZQ qQ} abelQ1 := Ohm1_abelem (pgroupS sZQ qQ) (center_abelian Q).
have{q q_pr Q abelQ1 Q1x} ox: prime #[x] by rewrite (abelem_order_p abelQ1).
move: Kx ox ZgCx; rewrite -cycle_subG -cent_cycle.
exact: odd_sdprod_Zgroup_cent_prime_plength1 solM oddM defM coMaK.
Qed.

Section OneSylow.

Variables (p : nat) (P : {group gT}).
Hypothesis sylP_G: p.-Sylow(G) P.
Let pP : p.-group P := pHall_pgroup sylP_G.

(* This is an B & G, Corollary 10.7(a), second part (which does not depend on *)
(* a particular complement).                                                  *)
Corollary mFT_Sylow_der1 : P \subset 'N(P)^`(1).
Proof.
have [-> | ntP] := eqsVneq P 1; first exact: sub1G.
have ltNG: 'N(P) \proper G := mFT_norm_proper ntP (mFT_pgroup_proper pP).
have [M] := mmax_exists ltNG; case/setIdP=> /= maxM sNM.
have [ltMG solM] := (mmax_proper maxM, mmax_sol maxM).
have [pl1M sPM] := (mFT_proper_plength1 p ltMG, subset_trans (normG P) sNM).
have sylP := pHall_subl sPM (subsetT M) sylP_G.
have sMp: p \in \sigma(M) by apply/exists_inP; exists P.
apply: subset_trans (dergS 1 (subsetIr M 'N(P))) => /=.
apply: plength1_Sylow_sub_der1 sylP pl1M (subset_trans _ (Msigma_der1 maxM)).
by rewrite (sub_Hall_pcore (Msigma_Hall maxM)) ?(pi_pgroup pP).
Qed.

(* This is B & G, Corollary 10.7(a), first part. *)
Corollary mFT_Sylow_sdprod_commg V : P ><| V = 'N(P) -> [~: P, V] = P.
Proof.
move=> defV; have sPN' := mFT_Sylow_der1.
have sylP := pHall_subl (normG P) (subsetT 'N(P)) sylP_G.
have [|//] := coprime_der1_sdprod defV _ (pgroup_sol pP) sPN'.
by rewrite (coprime_sdprod_Hall_l defV) // (pHall_Hall sylP).
Qed.

(* This is B & G, Corollary 10.7(b). *)
Corollary mFT_rank2_Sylow_cprod :
    'r(P) < 3 -> ~~ abelian P ->
  exists2 S, [/\ ~~ abelian (gval S), logn p #|S| = 3 & exponent S %| p]
  & exists2 C, cyclic (gval C) & S \* C = P /\ 'Ohm_1(C) = 'Z(S).
Proof.
move=> rP not_cPP; have sylP := pHall_subl (normG P) (subsetT 'N(P)) sylP_G.
have ntP: P :!=: 1 by apply: contraNneq not_cPP => ->; apply: abelian1.
have ltNG: 'N(P) \proper G := mFT_norm_proper ntP (mFT_pgroup_proper pP).
have [V hallV] := Hall_exists p^' (mFT_sol ltNG); have [_ p'V _] := and3P hallV.
have defNP: P ><| V = 'N(P) := sdprod_normal_p'HallP (normalG P) hallV sylP.
have defP: [~: P, V] = P := mFT_Sylow_sdprod_commg defNP.
have [_] := rank2_coprime_comm_cprod pP (mFT_odd _) ntP rP defP p'V (mFT_odd _).
case=> [/idPn// | [S esS [C [mulSC cycC defC1]]]].
exists S => //; exists C => //; split=> //; rewrite defC1.
have sSP: S \subset P by case/cprodP: mulSC => _ /mulG_sub[].
have [[not_cSS dimS _] pS] := (esS, pgroupS sSP pP).
by have [||[]] := p3group_extraspecial pS; rewrite ?dimS.
Qed.

(* This is B & G, Corollary 10.7(c). *)
Corollary mFT_sub_Sylow_trans : forall Q x,
  Q \subset P -> Q :^ x \subset P -> exists2 y, y \in 'N(P) & Q :^ x = Q :^ y.
Proof.
move=> Q x; have [-> /trivgP-> /trivgP-> | ntP sQP sQxP] := eqsVneq P 1.
  by exists 1; rewrite ?group1 ?conjs1g.
have ltNG: 'N(P) \proper G := mFT_norm_proper ntP (mFT_pgroup_proper pP).
have [M /=] := mmax_exists ltNG; case/setIdP=> maxM sNM.
have [ltMG solM] := (mmax_proper maxM, mmax_sol maxM).
have [pl1M sPM] := (mFT_proper_plength1 p ltMG, subset_trans (normG P) sNM).
have sylP := pHall_subl sPM (subsetT M) sylP_G.
have sMp: p \in \sigma(M) by apply/exists_inP; exists P.
have [transCQ _ _] := sigma_group_trans maxM sMp (pgroupS sQP pP).
have [||q cQq [u Mu defx]] := transCQ x; try exact: subset_trans _ sPM.
have nQC := normP (subsetP (cent_sub Q) _ _).
have [|q' cMQq' [y nMPy defu]] := plength1_Sylow_trans sylP pl1M solM sQP Mu.
  by rewrite defx conjsgM nQC in sQxP.
have [[_ nPy] [_ cQq']] := (setIP nMPy, setIP cMQq').
by exists y; rewrite // defx defu !conjsgM 2?nQC.
Qed.

(* This is B & G, Corollary 10.7(d). *)
Corollary mFT_subnorm_Sylow Q : Q \subset P -> p.-Sylow('N(Q)) 'N_P(Q).
Proof.
move=> sQP; have pQ := pgroupS sQP pP.
have [S /= sylS] := Sylow_exists p 'N(Q); have [sNS pS _] := and3P sylS.
have sQS: Q \subset S := normal_sub_max_pgroup (Hall_max sylS) pQ (normalG Q).
have [x _ sSxP] := Sylow_Jsub sylP_G (subsetT S) pS.
have sQxP: Q :^ x \subset P by rewrite (subset_trans _ sSxP) ?conjSg.
have [y nPy defQy] := mFT_sub_Sylow_trans sQP sQxP.
have nQxy: x * y^-1 \in 'N(Q) by rewrite inE conjsgM defQy actK.
have sSxyP: S :^ (x * y^-1) \subset P by rewrite conjsgM sub_conjgV (normP nPy).
have sylSxy: p.-Sylow('N(Q)) (S :^ (x * y^-1)) by rewrite pHallJ.
have pNPQ: p.-group 'N_P(Q) := pgroupS (subsetIl P 'N(Q)) pP.
by rewrite (sub_pHall sylSxy pNPQ) ?subsetIr // subsetI sSxyP (@pHall_sub _ p).
Qed.

(* This is B & G, Corollary 10.7(e). *)
Corollary mFT_Sylow_normalS Q R :
  p.-group R -> Q \subset P :&: R -> Q <| 'N(P) -> Q <| 'N(R).
Proof.
move=> pR /subsetIP[sQP sQR] /andP[nQP nQ_NP].
have [x _ sRxP] := Sylow_Jsub sylP_G (subsetT R) pR.
rewrite /normal normsG //; apply/subsetP=> y nRy.
have sQxP: Q :^ x \subset P by rewrite (subset_trans _ sRxP) ?conjSg.
have sQyxP: Q :^ (y * x) \subset P.
  by rewrite actM (subset_trans _ sRxP) // -(normP nRy) !conjSg.
have [t tNP defQx] := mFT_sub_Sylow_trans sQP sQxP.
have [z zNP defQxy] := mFT_sub_Sylow_trans sQP sQyxP.
by rewrite inE -(conjSg _ _ x) -actM /= defQx defQxy !(normsP nQ_NP). 
Qed.

End OneSylow.

Section AnotherMaximal.

Variable M : {group gT}.
Hypothesis maxM : M \in 'M.

Let solM : solvable M := mmax_sol maxM.
Let ltMG : M \proper G := mmax_proper maxM.

Let sMbMs : M`_\beta \subset M`_\sigma := Mbeta_sub_Msigma maxM.
Let nsMbM : M`_\beta <| M := pcore_normal _ _.

Let hallMs : \sigma(M).-Hall(M) M`_\sigma := Msigma_Hall maxM.
Let nsMsM : M`_\sigma <| M := pcore_normal _ M.
Let sMsM' : M`_\sigma \subset M^`(1) := Msigma_der1 maxM.

Lemma Mbeta_der1 : M`_\beta \subset M^`(1).
Proof. exact: subset_trans sMbMs sMsM'. Qed.

Let sM'M : M^`(1) \subset M := der_sub 1 M.
Let nsMsM' : M`_\sigma <| M^`(1) := normalS sMsM' sM'M nsMsM.
Let nsMbM' : M`_\beta <| M^`(1) := normalS Mbeta_der1 sM'M nsMbM.
Let nMbM' := normal_norm nsMbM'.

(* This is B & G, Lemma 10.8(c). *)
Lemma beta_max_pdiv p :
    p \notin \beta(M) ->
  [/\ p^'.-Hall(M^`(1)) 'O_p^'(M^`(1)),
      p^'.-Hall(M`_\sigma) 'O_p^'(M`_\sigma)
    & forall q, q \in \pi(M / 'O_p^'(M)) -> q <= p].
Proof.
rewrite !inE -negb_exists_in negbK => /exists_inP[P sylP nnP].
have [|ncM' p_max] := narrow_der1_complement_max_pdiv (mFT_odd M) solM sylP nnP.
  by rewrite mFT_proper_plength1 ?implybT.
by rewrite -(pcore_setI_normal _ nsMsM') (Hall_setI_normal nsMsM').
Qed.

(* This is B & G, Lemma 10.8(a), first part. *)
Lemma Mbeta_Hall : \beta(M).-Hall(M) M`_\beta.
Proof.
have [H hallH] := Hall_exists \beta(M) solM; have [sHM bH _]:= and3P hallH.
rewrite [M`_\beta](sub_pHall hallH) ?pcore_pgroup ?pcore_sub //=.
rewrite -(setIidPl sMbMs) pcore_setI_normal ?pcore_normal //.
have sH: \sigma(M).-group H := sub_pgroup (beta_sub_sigma maxM) bH.
have sHMs: H \subset M`_\sigma by rewrite (sub_Hall_pcore hallMs).
rewrite -pcoreNK -bigcap_p'core subsetI sHMs.
apply/bigcapsP=> p b'p; have [_ hallKp' _] := beta_max_pdiv b'p.
by rewrite (sub_Hall_pcore hallKp') ?(pi_p'group bH).
Qed.

(* This is B & G, Lemma 10.8(a), second part. *)
Lemma Mbeta_Hall_G : \beta(M).-Hall(G) M`_\beta.
Proof.
apply: (subHall_Hall (Msigma_Hall_G maxM) (beta_sub_sigma maxM)).
exact: pHall_subl sMbMs (pcore_sub _ _) Mbeta_Hall.
Qed.

(* This is an equivalent form of B & G, Lemma 10.8(b), which is used directly *)
(* later in the proof (e.g., Corollary 10.9a below, and Lemma 12.11), and is  *)
(* proved as an intermediate step of the proof of of 12.8(b).                 *)
Lemma Mbeta_quo_nil : nilpotent (M^`(1) / M`_\beta).
Proof.
have /and3P[_ bMb b'M'Mb] := pHall_subl Mbeta_der1 sM'M Mbeta_Hall.
apply: nilpotentS (Fitting_nil (M^`(1) / M`_\beta)) => /=.
rewrite -{1}[_ / _]Sylow_gen gen_subG.
apply/bigcupsP=> Q /SylowP[q _ /and3P[sQM' qQ _]].
apply: subset_trans (pcore_sub q _).
rewrite p_core_Fitting -pcoreNK -bigcap_p'core subsetI sQM' /=.
apply/bigcapsP=> [[p /= _] q'p]; have [b_p | b'p] := boolP (p \in \beta(M)).
  by rewrite pcore_pgroup_id ?(pi'_p'group _ b_p) // /pgroup card_quotient.
have p'Mb: p^'.-group M`_\beta := pi_p'group bMb b'p.
rewrite sub_Hall_pcore ?(pi_p'group qQ) {Q qQ sQM'}//.
rewrite pquotient_pcore ?quotient_pHall ?(subset_trans (pcore_sub _ _)) //.
by have [-> _ _] := beta_max_pdiv b'p.
Qed.

(* This is B & G, Lemma 10.8(b), generalized to arbitrary beta'-subgroups of  *)
(* M^`(1) (which includes Hall beta'-subgroups of M^`(1) and M`_\beta).       *)
Lemma beta'_der1_nil H : \beta(M)^'.-group H -> H \subset M^`(1) -> nilpotent H.
Proof.
move=> b'H sHM'; have [_ bMb _] := and3P Mbeta_Hall.
have{b'H} tiMbH: M`_\beta :&: H = 1 := coprime_TIg (pnat_coprime bMb b'H).
rewrite {tiMbH}(isog_nil (quotient_isog (subset_trans sHM' nMbM') tiMbH)).
exact: nilpotentS (quotientS _ sHM') Mbeta_quo_nil.
Qed.

(* This is B & G, Corollary 10.9(a). *)
Corollary beta'_cent_Sylow p q X :
     p \notin \beta(M) -> q \notin \beta(M) -> q.-group X ->
     (p != q) && (X \subset M^`(1)) || (p < q) && (X \subset M) ->
  [/\ (*a1*) exists2 P, p.-Sylow(M`_\sigma) (gval P) & X \subset 'C(P),
      (*a2*) p \in \alpha(M) -> 'C_M(X)%G \in 'U
    & (*a3*) q.-Sylow(M^`(1)) X -> 
          exists2 P, p.-Sylow(M^`(1)) (gval P) & P \subset 'N_M(X)^`(1)].
Proof.
move=> b'p b'q qX q'p_sXM'; pose pq : nat_pred := pred2 p q.
have [q'p sXM]: p \in q^' /\ X \subset M.
  case/orP: q'p_sXM' => /andP[q'p /subset_trans-> //].
  by rewrite !inE neq_ltn q'p.
have sXM'M: X <*> M^`(1) \subset M by rewrite join_subG sXM.
have solXM': solvable (X <*> M^`(1)) := solvableS sXM'M solM.
have pqX: pq.-group X by rewrite (pi_pgroup qX) ?inE ?eqxx ?orbT.
have{solXM' pqX} [W /= hallW sXW] := Hall_superset solXM' (joing_subl _ _) pqX.
have [sWXM' pqW _] := and3P hallW; have sWM := subset_trans sWXM' sXM'M.
have{b'q} b'W: \beta(M)^'.-group W. (* GG -- Coq diverges on b'p <> b'q *)
  by apply: sub_pgroup pqW => r /pred2P[]->; [exact: b'p | exact: b'q].
have nilM'W: nilpotent (M^`(1) :&: W).
  by rewrite beta'_der1_nil ?subsetIl ?(pgroupS (subsetIr _ _)).
have{nilM'W} nilW: nilpotent W.
  do [case/orP: q'p_sXM'=> /andP[]] => [_ sXM' | lt_pq _].
    by rewrite -(setIidPr sWXM') (joing_idPr sXM').
  pose Wq := 'O_p^'(M) :&: W; pose Wp := 'O_p(M^`(1) :&: W).
  have nMp'M := char_norm (pcore_char p^' M).
  have nMp'W := subset_trans sWM nMp'M.
  have sylWq: q.-Sylow(W) Wq.
    have [sWqMp' sWp'W] := subsetIP (subxx Wq).
    have [Q sylQ] := Sylow_exists q W; have [sQW qQ _] := and3P sylQ.
    rewrite [Wq](sub_pHall sylQ _ _ (subsetIr _ W)) //= -/Wq.
      apply/pgroupP=> r r_pr r_dv_Wp'.
      have:= pgroupP (pgroupS sWqMp' (pcore_pgroup _ _)) r r_pr r_dv_Wp'.
      by apply/implyP; rewrite implyNb; exact: (pgroupP (pgroupS sWp'W pqW)).
    have [[_ _ max_p] sQM] := (beta_max_pdiv b'p, subset_trans sQW sWM).
    rewrite subsetI sQW -quotient_sub1 ?(subset_trans sQM nMp'M) //.
    apply: contraLR lt_pq; rewrite -leqNgt andbT subG1 -rank_gt0.
    rewrite (rank_pgroup (quotient_pgroup _ qQ)) p_rank_gt0 => piQb_q.
    exact: max_p (piSg (quotientS _ sQM) piQb_q).
  have nM'W: W \subset 'N(M^`(1)) by rewrite (subset_trans sWM) ?der_norm.
  have qWWM': q.-group (W / (M^`(1) :&: W)).
    rewrite (isog_pgroup _ (second_isog _)) ?(pgroupS (quotientS _ sWXM')) //=.
    by rewrite (quotientYidr (subset_trans sXW nM'W)) quotient_pgroup.
  have{qWWM'} sylWp: p.-Sylow(W) Wp.
    rewrite /pHall pcore_pgroup (subset_trans (pcore_sub _ _)) ?subsetIr //=.
    rewrite -(Lagrange_index (subsetIr _ _) (pcore_sub _ _)) pnat_mul //.
    rewrite -(divgS (pcore_sub _ _)) -card_quotient ?normsI ?normG //= -pgroupE.
    rewrite (pi_p'group qWWM') //= -(dprod_card (nilpotent_pcoreC p nilM'W)).
    by rewrite  mulKn ?cardG_gt0 // -pgroupE pcore_pgroup.
  have [[sWqW qWq _] [sWpW pWp _]] := (and3P sylWq, and3P sylWp).
  have <-: Wp * Wq = W.
    apply/eqP; rewrite eqEcard mul_subG //= -(partnC q (cardG_gt0 W)).
    rewrite (coprime_cardMg (p'nat_coprime (pi_pnat pWp _) qWq)) //.
    rewrite (card_Hall sylWp) (card_Hall sylWq) -{2}(part_pnat_id pqW) -partnI.
    rewrite mulnC (@eq_partn _ p) // => r.
    by rewrite !inE andb_orl andbN orbF; apply: andb_idr; move/eqP->.
  apply: nilpotentS (mul_subG _ _) (Fitting_nil W).
    rewrite Fitting_max ?(pgroup_nil pWp) //.
    by rewrite (char_normal_trans (pcore_char _ _)) //= setIC norm_normalI.
  by rewrite Fitting_max ?(pgroup_nil qWq) //= setIC norm_normalI.
have part1: exists2 P : {group gT}, p.-Sylow(M`_\sigma) P & X \subset 'C(P).
  have sMsXM' := subset_trans sMsM' (joing_subr X _).
  have nsMsXM': M`_\sigma <| X <*> M^`(1) := normalS sMsXM' sXM'M nsMsM.
  have sylWp: p.-Hall(M`_\sigma) ('O_p(W) :&: M`_\sigma).
    rewrite setIC (Sylow_setI_normal nsMsXM') //.
    exact: subHall_Sylow hallW (predU1l _ _) (nilpotent_pcore_Hall p nilW).
  have [_ _ cWpWp' _] := dprodP (nilpotent_pcoreC p nilW).
  exists ('O_p(W) :&: M`_\sigma)%G; rewrite ?(centSS _ _ cWpWp') ?subsetIl //.
  by rewrite (sub_Hall_pcore (nilpotent_pcore_Hall _ _)) ?(pi_p'group qX).
split=> // [a_p | {part1}sylX].
  have ltCMX_G := sub_proper_trans (subsetIl M 'C(X)) ltMG.
  have [P sylP cPX] := part1; have s_p := alpha_sub_sigma maxM a_p.
  have{sylP} sylP := subHall_Sylow hallMs s_p sylP.
  apply: rank3_Uniqueness ltCMX_G (leq_trans a_p _). 
  by rewrite -(rank_Sylow sylP) rankS //= subsetI (pHall_sub sylP) // centsC.
do [move: sWXM'; rewrite (joing_idPr (pHall_sub sylX)) => sWM'] in hallW.
have nMbX: X \subset 'N(M`_\beta) := subset_trans sXM (normal_norm nsMbM).
have nsMbXM : M`_\beta <*> X <| M.
  rewrite -{2}(quotientGK nsMbM) -quotientYK ?cosetpre_normal //=.
  rewrite (eq_Hall_pcore _ (quotient_pHall nMbX sylX)); last first.
    exact: nilpotent_pcore_Hall Mbeta_quo_nil.
  by rewrite (char_normal_trans (pcore_char _ _)) ?quotient_normal ?der_normal.
pose U := 'N_M(X); have defM: M`_\beta * U = M.
  have sXU : X \subset U by rewrite subsetI sXM normG.
  rewrite -[U](mulSGid sXU) /= -/U mulgA -norm_joinEr //.
  apply: Frattini_arg nsMbXM (pHall_subl (joing_subr _ X) _ sylX).
  by rewrite join_subG Mbeta_der1 (pHall_sub sylX).
have sWpU: 'O_p(W) \subset U.
  rewrite (subset_trans (pcore_sub _ _)) // subsetI sWM normal_norm //=.
  have sylX_W: q.-Sylow(W) X := pHall_subl sXW sWM' sylX.
  by rewrite (eq_Hall_pcore (nilpotent_pcore_Hall q nilW) sylX_W) pcore_normal.
have sylWp: p.-Sylow(M^`(1)) 'O_p(W).
  exact: subHall_Sylow hallW (predU1l _ _) (nilpotent_pcore_Hall p nilW).
exists 'O_p(W)%G; rewrite //= -(setIidPl (pHall_sub sylWp)).
rewrite (pprod_focal_coprime defM) ?pcore_normal ?subsetIr //.
exact: pnat_coprime (pcore_pgroup _ _) (pi_pnat (pcore_pgroup _ _) _).
Qed.

(* This is B & G, Corollary 10.9(b). *)
Corollary nonuniq_norm_Sylow_pprod p H S :
    H \in 'M -> H :!=: M -> p.-Sylow(G) S -> 'N(S) \subset H :&: M -> 
  M`_\beta * (H :&: M) = M /\ \alpha(M) =i \beta(M).
Proof.
move=> maxH neqHM sylS_G sN_HM; have [sNH sNM] := subsetIP sN_HM.
have [sSM sSH] := (subset_trans (normG S) sNM, subset_trans (normG S) sNH).
have [sylS pS] := (pHall_subl sSM (subsetT M) sylS_G, pHall_pgroup sylS_G).
have sMp: p \in \sigma(M) by apply/exists_inP; exists S.
have aM'p: p \in \alpha(M)^'.
  apply: contra neqHM; rewrite !inE -(rank_Sylow sylS) => rS.
  have uniqS: S \in 'U := rank3_Uniqueness (mFT_pgroup_proper pS) rS.
  by rewrite (eq_uniq_mmax (def_uniq_mmax uniqS maxM sSM) maxH sSH).
have sSM': S \subset M^`(1).
  by rewrite (subset_trans _ sMsM') ?(sub_Hall_pcore hallMs) ?(pi_pgroup pS).
have nMbS := subset_trans sSM (normal_norm nsMbM).
have nMbSM: M`_\beta <*> S <| M.
  rewrite -{2}(quotientGK nsMbM) -quotientYK ?cosetpre_normal //=.
  have sylS_M' := pHall_subl sSM' sM'M sylS.
  rewrite (eq_Hall_pcore _ (quotient_pHall nMbS sylS_M')); last first.
    exact: nilpotent_pcore_Hall Mbeta_quo_nil.
  by rewrite (char_normal_trans (pcore_char _ _)) ?quotient_normal ?der_normal.
have defM: M`_\beta * 'N_M(S) = M.
  have sSNM: S \subset 'N_M(S) by rewrite subsetI sSM normG.
  rewrite -(mulSGid sSNM) /= mulgA -norm_joinEr //.
  by rewrite (Frattini_arg _ (pHall_subl _ _ sylS_G)) ?joing_subr ?subsetT.
split=> [|q].
  apply/eqP; rewrite setIC eqEsubset mulG_subG subsetIl pcore_sub /=.
  by rewrite -{1}defM mulgS ?setIS.
apply/idP/idP=> [aMq|]; last exact: beta_sub_alpha.
apply: contraR neqHM => bM'q; have bM'p := contra (@beta_sub_alpha _ M p) aM'p.
have [|_ uniqNM _] := beta'_cent_Sylow bM'q bM'p pS.
  by apply: contraR aM'p; rewrite sSM'; case: eqP => //= <- _.
rewrite (eq_uniq_mmax (def_uniq_mmax (uniqNM aMq) maxM (subsetIl _ _)) maxH) //.
by rewrite subIset ?(subset_trans (cent_sub _)) ?orbT.
Qed.

(* This is B & G, Proposition 10.10. *)
Proposition max_normed_2Elem_signaliser p q (A Q : {group gT}) :
    p != q -> A \in 'E_p^2(G) :&: 'E*_p(G) -> Q \in |/|*(A; q) ->
    q %| #|'C(A)| ->
  exists2 P : {group gT}, p.-Sylow(G) P /\ A \subset P
          & [/\ (*a*) 'O_p^'('C(P)) * ('N(P) :&: 'N(Q)) = 'N(P),
                (*b*) P \subset 'N(Q)^`(1)
              & (*c*) q.-narrow Q -> P \subset 'C(Q)].
Proof.
move=> neq_pq /setIP[Ep2A EpmA] maxQ piCAq.
have [_ abelA dimA] := pnElemP Ep2A; have [pA cAA _] := and3P abelA.
have [p_pr oA] := (pnElem_prime Ep2A, card_pnElem Ep2A).
have{dimA} rA2: 'r(A) = 2 by rewrite (rank_abelem abelA).
have{EpmA} ncA: normed_constrained A.
  have ntA: A :!=: 1 by rewrite -rank_gt0 rA2.
  exact: plength_1_normed_constrained ntA EpmA (mFT_proper_plength1 _).
pose pi := \pi(A); pose K := 'O_pi^'('C(A)).
have def_pi : pi =i (p : nat_pred).
  by move=> r; rewrite !inE /= oA primes_exp ?primes_prime ?inE.
have pi'q : q \notin pi by rewrite def_pi !inE eq_sym.
have transKA: [transitive K, on |/|*(A; q) | 'JG].
  by rewrite normed_constrained_rank2_trans // (center_idP cAA) rA2.
have [P0 sylP0 sAP0] := Sylow_superset (subsetT _) pA.
have pP0: p.-group P0 := pHall_pgroup sylP0.
have piP0: pi.-group P0 by rewrite (eq_pgroup _ def_pi).
have{pP0} snAP0: A <|<| P0 := nilpotent_subnormal (pgroup_nil pP0) sAP0.
have{pi'q snAP0 ncA piP0} [//|] := normed_trans_superset ncA pi'q snAP0 piP0.
rewrite /= -/pi -/K => -> transKP submaxPA maxPfactoring.
have{transKP} [Q0 maxQ0 _] := imsetP transKP.
have{transKA} [k Kk defQ] := atransP2 transKA (subsetP submaxPA _ maxQ0) maxQ.
set P := P0 :^ k; have{sylP0} sylP: p.-Sylow(G) P by rewrite pHallJ ?in_setT.
have nAK: K \subset 'N(A) by rewrite cents_norm ?pcore_sub.
have{sAP0 nAK K Kk} sAP: A \subset P by rewrite -(normsP nAK k Kk) conjSg.
exists [group of P] => //.
have{maxPfactoring} [sPNQ' defNP] := maxPfactoring _ maxQ0.
move/(congr1 ('Js%act^~ k)): defNP sPNQ'; rewrite -(conjSg _ _ k) /=.
rewrite conjsMg !conjIg !conjsRg -!derg1 -!normJ -pcoreJ -centJ -/P.
rewrite -(congr_group defQ) (eq_pcore _ (eq_negn def_pi)) => defNP sPNQ'.
have{sPNQ'} sPNQ': P \subset 'N(Q)^`(1).
  by rewrite (setIidPl (mFT_Sylow_der1 sylP)) in sPNQ'.
split=> // narrowQ; have [-> | ntQ] := eqsVneq Q 1; first exact: cents1.
pose AutQ := conj_aut Q @* 'N(Q).
have qQ: q.-group Q by case/mem_max_normed: maxQ.
have ltNG: 'N(Q) \proper G by rewrite mFT_norm_proper // (mFT_pgroup_proper qQ).
have{ltNG} qAutQ': q.-group AutQ^`(1).
  have qAutQq: q.-group 'O_q(AutQ) := pcore_pgroup _ _.
  rewrite (pgroupS _ qAutQq) // der1_min ?gFnorm //.
  have solAutQ: solvable AutQ by rewrite morphim_sol -?mFT_sol_proper.
  have [oddQ oddAutQ]: odd #|Q| /\ odd #|AutQ| by rewrite morphim_odd mFT_odd.
  by have /(Aut_narrow qQ)[] := Aut_conj_aut Q 'N(Q).
have nQP: P \subset 'N(Q) := subset_trans sPNQ' (der_sub 1 _).
rewrite (sameP setIidPl eqP) eqEsubset subsetIl /=.
rewrite -quotient_sub1 ?normsI ?normG ?norms_cent //= -ker_conj_aut subG1.
rewrite trivg_card1 (card_isog (first_isog_loc _ _)) //= -trivg_card1 -subG1.
have q'AutP: q^'.-group (conj_aut Q @* P).
  by rewrite morphim_pgroup //; apply: pi_pnat (pHall_pgroup sylP) _.
rewrite -(coprime_TIg (pnat_coprime qAutQ' q'AutP)) subsetI subxx.
by rewrite /= -morphim_der // morphimS.
Qed.

(* Notation for Proposition 11, which is the last to appear in this segment. *)
Local Notation sigma' := \sigma(gval M)^'.

(* This is B & G, Proposition 10.11(a). *)
Proposition sigma'_not_uniq K : K \subset M -> sigma'.-group K -> K \notin 'U.
Proof.
move=> sKM sg'K; have [E hallE sKE] := Hall_superset solM sKM sg'K.
have [sEM sg'E _] := and3P hallE.
have rEle2: 'r(E) <= 2.
  have [q _ ->] := rank_witness E; rewrite leqNgt; apply/negP=> rEgt2.
  have: q \in sigma' by rewrite (pnatPpi sg'E) // -p_rank_gt0 -(subnKC rEgt2).
  by rewrite inE /= alpha_sub_sigma //; apply: leq_trans (p_rankS q sEM).
have [E1 | ntE]:= eqsVneq E 1.
  by apply: contraL (@uniq_mmax_neq1 _ K) _; rewrite -subG1 -E1.
pose p := max_pdiv #|E|; pose P := 'O_p(E).
have piEp: p \in \pi(E) by rewrite pi_max_pdiv cardG_gt1.
have sg'p: p \in sigma' by rewrite (pnatPpi sg'E).
have sylP: p.-Sylow(E) P.
  rewrite rank2_max_pcore_Sylow ?mFT_odd ?(solvableS sEM solM) //.
  exact: leq_trans (rankS (Fitting_sub E)) rEle2.
apply: contra (sg'p) => uniqK; apply/existsP; exists [group of P].
have defMK := def_uniq_mmax uniqK maxM (subset_trans sKE sEM).
rewrite (subHall_Sylow hallE) // (sub_uniq_mmax defMK) //; last first.
  rewrite mFT_norm_proper ?(mFT_pgroup_proper (pcore_pgroup _ _)) //.
  by rewrite -cardG_gt1 (card_Hall sylP) p_part_gt1.
by rewrite (subset_trans sKE) // gFnorm.
Qed.

(* This is B & G, Proposition 10.11(b). *)
Proposition sub'cent_sigma_rank1 K :
  K \subset M -> sigma'.-group K -> 'r('C_K(M`_\sigma)) <= 1.
Proof.
move=> sKM sg'K; rewrite leqNgt; apply/rank_geP=> [[A /nElemP[p Ep2A]]].
have p_pr := pnElem_prime Ep2A.
have [sACKMs abelA dimA] := pnElemP Ep2A; rewrite subsetI centsC in sACKMs.
have{sACKMs} [sAK cAMs]: A \subset K /\ M`_\sigma \subset 'C(A) := andP sACKMs.
have sg'p: p \in sigma'.
  by rewrite (pgroupP (pgroupS sAK sg'K)) // (card_pnElem Ep2A) dvdn_mull.
have [Ms1 | [q q_pr q_dvd_Ms]] := trivgVpdiv M`_\sigma.
  by case/eqP: (Msigma_neq1 maxM).
have sg_q: q \in \sigma(M) := pgroupP (pcore_pgroup _ _) _ q_pr q_dvd_Ms.
have neq_pq: p != q by apply: contraNneq sg'p => ->.
have [Q sylQ] := Sylow_exists q M`_\sigma; have [sQMs qQ _] := and3P sylQ.
have cAQ: Q \subset 'C(A) := subset_trans sQMs cAMs.
have{q_dvd_Ms} q_dv_CA: q %| #|'C(A)|.
  rewrite (dvdn_trans _ (cardSg cAQ)) // -(part_pnat_id (pnat_id q_pr)).
  by rewrite (card_Hall sylQ) partn_dvd.
have{cAQ} maxQ: Q \in |/|*(A; q).
  rewrite inE; apply/maxgroupP; rewrite qQ cents_norm 1?centsC //.
  split=> // Y /andP[qY _] sQY; apply: sub_pHall qY sQY (subsetT Y).
  by rewrite (subHall_Sylow (Msigma_Hall_G maxM)).
have sNQM: 'N(Q) \subset M.
  by rewrite (norm_sigma_Sylow sg_q) // (subHall_Sylow hallMs).
have rCAle2: 'r('C(A)) <= 2.
  apply: contraR (sigma'_not_uniq sKM sg'K); rewrite -ltnNge => rCAgt2.
  apply: uniq_mmaxS sAK (sub_mmax_proper maxM sKM) _.
  by apply: cent_rank3_Uniqueness rCAgt2; rewrite (rank_abelem abelA) dimA.
have max2A: A \in 'E_p^2(G) :&: 'E*_p(G).
  rewrite 3!inE subsetT abelA dimA; apply/pmaxElemP; rewrite inE subsetT.
  split=> // Y /pElemP[_ abelY /eqVproper[]//ltAY].
  have [pY cYY _] := and3P abelY.
  suffices: 'r_p('C(A)) > 2 by rewrite ltnNge (leq_trans (p_rank_le_rank p _)).
  rewrite -dimA (leq_trans (properG_ltn_log pY ltAY)) //.
  by rewrite logn_le_p_rank // inE centsC (subset_trans (proper_sub ltAY)).
have{rCAle2 cAMs} Ma1: M`_\alpha = 1.
  apply: contraTeq rCAle2; rewrite -rank_gt0 -ltnNge.
  have [r _ ->] := rank_witness M`_\alpha; rewrite p_rank_gt0.
  move/(pnatPpi (pcore_pgroup _ _))=> a_r; apply: (leq_trans a_r).
  have [R sylR] := Sylow_exists r M`_\sigma.
  have sylR_M: r.-Sylow(M) R.
    by rewrite (subHall_Sylow (Msigma_Hall maxM)) ?alpha_sub_sigma.
  rewrite -(p_rank_Sylow sylR_M) (p_rank_Sylow sylR).
  by rewrite (leq_trans (p_rank_le_rank r _)) // rankS // centsC.
have{Ma1} nilM': nilpotent M^`(1).
  by rewrite (isog_nil (quotient1_isog _)) -Ma1 Malpha_quo_nil.
have{max2A maxQ neq_pq q_dv_CA} [P [sylP sAP] sPNQ']:
  exists2 P : {group gT}, p.-Sylow(G) P /\ A \subset P & P \subset 'N(Q)^`(1).
- by case/(max_normed_2Elem_signaliser neq_pq): maxQ => // P ? []; exists P.
have{sNQM} defP: 'O_p(M^`(1)) = P.
  rewrite (nilpotent_Hall_pcore nilM' (pHall_subl _ _ sylP)) ?subsetT //.
  by rewrite (subset_trans sPNQ') ?dergS.
have charP: P \char M by rewrite -defP (char_trans (pcore_char p _)) ?der_char.
have [sPM nsPM] := (char_sub charP, char_normal charP).
case/exists_inP: sg'p; exists P; first exact: pHall_subl (subsetT M) sylP.
by rewrite (mmax_normal maxM) // -rank_gt0 ltnW // -dimA -rank_abelem ?rankS.
Qed.

(* This is B & G, Proposition 10.11(c). *)
Proposition sub'cent_sigma_cyclic K (Y := 'C_K(M`_\sigma) :&: M^`(1)) :
  K \subset M -> sigma'.-group K -> cyclic Y /\ Y <| M.
Proof.
move=> sKM sg'K; pose Z := 'O_sigma'('F(M)).
have nsZM: Z <| M := char_normal_trans (pcore_char _ _) (Fitting_normal M).
have [sZM nZM] := andP nsZM; have Fnil := Fitting_nil M.
have rZle1: 'r(Z) <= 1.
  apply: leq_trans (rankS _) (sub'cent_sigma_rank1 sZM (pcore_pgroup _ _)).
  rewrite subsetI subxx (sameP commG1P trivgP) /=.
  rewrite -(TI_pcoreC \sigma(M) M 'F(M)) subsetI commg_subl commg_subr.
  by rewrite (subset_trans sZM) ?gFnorm ?(subset_trans (pcore_sub _ _)).
have{rZle1} cycZ: cyclic Z.
  have nilZ: nilpotent Z := nilpotentS (pcore_sub _ _) Fnil. 
  by rewrite nil_Zgroup_cyclic // odd_rank1_Zgroup // mFT_odd.
have cZM': M^`(1) \subset 'C_M(Z).
  rewrite der1_min ?normsI ?normG ?norms_cent //= -ker_conj_aut.
  rewrite (isog_abelian (first_isog_loc _ _)) //.
  by rewrite (abelianS (Aut_conj_aut _ _)) // Aut_cyclic_abelian.
have sYF: Y \subset 'F(M).
  apply: subset_trans (cent_sub_Fitting (mmax_sol maxM)).
  have [_ /= <- _ _] := dprodP (nilpotent_pcoreC \sigma(M) Fnil).
  by rewrite centM setICA setISS // setIC subIset ?centS // pcore_Fitting.
have{sYF} sYZ: Y \subset Z.
  rewrite (sub_Hall_pcore (nilpotent_pcore_Hall _ Fnil)) //=.
  by rewrite -setIA (pgroupS (subsetIl K _)).
by rewrite (cyclicS sYZ cycZ) (char_normal_trans _ nsZM) // sub_cyclic_char.
Qed.

(* This is B & G, Proposition 10.11(d). *)
Proposition commG_sigma'_1Elem_cyclic p K P (K0 := [~: K, P]) :
    K \subset M -> sigma'.-group K -> p \in sigma' -> P \in 'E_p^1('N_M(K)) ->
    'C_(M`_\sigma)(P) = 1 -> p^'.-group K -> abelian K ->
  [/\ K0 \subset 'C(M`_\sigma), cyclic K0 & K0 <| M].
Proof.
move=> sKM sg'K sg'p EpP regP p'K cKK.
have nK0P: P \subset 'N(K0) := commg_normr P K.
have p_pr := pnElem_prime EpP; have [sPMN _ oP] := pnElemPcard EpP.
have [sPM nKP]: P \subset M /\ P \subset 'N(K) by apply/subsetIP.
have /andP[sMsM nMsM]: M`_\sigma <| M := pcore_normal _ _.
have sK0K: K0 \subset K by rewrite commg_subl.
have [sK0M sg'K0]:= (subset_trans sK0K sKM, pgroupS sK0K sg'K).
have [nMsK0 nMsP] := (subset_trans sK0M nMsM, subset_trans sPM nMsM).
have coKP: coprime #|K| #|P| by rewrite oP coprime_sym prime_coprime -?p'natE.
have coK0Ms: coprime #|K0| #|M`_\sigma|.
  by rewrite coprime_sym (pnat_coprime (pcore_pgroup _ _)).
have nilK0Ms: nilpotent (K0 <*> M`_\sigma).
  have mulK0MsP: K0 <*> M`_\sigma ><| P = K0 <*> M`_\sigma <*> P.
    rewrite sdprodEY ?normsY // coprime_TIg //= norm_joinEl //.
    rewrite coprime_cardMg // coprime_mull (coprimeSg sK0K) //.
    by rewrite oP (pnat_coprime (pcore_pgroup _ _)) ?pnatE.
  apply: (prime_Frobenius_sol_kernel_nil mulK0MsP); rewrite ?oP //=.
    by rewrite (solvableS _ solM) // !join_subG sK0M pcore_sub.
  rewrite norm_joinEl // -subcent_TImulg ?subsetI ?nK0P //.
    by rewrite coprime_abel_cent_TI ?mul1g.
  exact: coprime_TIg.
have cMsK0: K0 \subset 'C(M`_\sigma).
  rewrite (sub_nilpotent_cent2 nilK0Ms) ?joing_subl ?joing_subr //.
  exact: pnat_coprime (pcore_pgroup _ _) sg'K0.
have [cycY nsYM] := sub'cent_sigma_cyclic sK0M sg'K0.
set Y := _ :&: _ in cycY nsYM.
have sK0Y: K0 \subset Y by rewrite !subsetI subxx cMsK0 commgSS.
split=> //; first exact: cyclicS sK0Y cycY.
by apply: char_normal_trans nsYM; rewrite sub_cyclic_char.
Qed.

End AnotherMaximal.

(* This is B & G, Lemma 10.12. *)
Lemma sigma_disjoint M H :
    M \in 'M -> H \in 'M -> gval H \notin M :^: G ->
  [/\ (*a*) M`_\alpha :&: H`_\sigma = 1,
            [predI \alpha(M) & \sigma(H)] =i pred0
    & (*b*) nilpotent M`_\sigma ->
            M`_\sigma :&: H`_\sigma = 1
         /\ [predI \sigma(M) & \sigma(H)] =i pred0].
Proof.
move=> maxM maxH notjMH.
suffices sigmaMHnil p: p \in [predI \sigma(M) & \sigma(H)] ->
  p \notin \alpha(M) /\ ~~ nilpotent M`_\sigma.
- have a2: [predI \alpha(M) & \sigma(H)] =i pred0.
    move=> p; apply/andP=> [[/= aMp sHp]].
    by case: (sigmaMHnil p); rewrite /= ?aMp // inE /= alpha_sub_sigma.
  split=> // [|nilMs].
    rewrite coprime_TIg // (pnat_coprime (pcore_pgroup _ _)) //.
    apply: sub_in_pnat (pcore_pgroup _ _) => p _ sHp.
    by apply: contraFN (a2 p) => aMp; rewrite inE /= sHp andbT.
  have b2: [predI \sigma(M) & \sigma(H)] =i pred0.
    by move=> p; apply/negP; case/sigmaMHnil => _; rewrite nilMs.
  rewrite coprime_TIg // (pnat_coprime (pcore_pgroup _ _)) //.
  apply: sub_in_pnat (pcore_pgroup _ _) => p _ sHp.
  by apply: contraFN (b2 p) => bMp; rewrite inE /= sHp andbT.
case/andP=> sMp sHp; have [S sylS]:= Sylow_exists p M.
have [sSM pS _] := and3P sylS.
have sylS_G: p.-Sylow(G) S := sigma_Sylow_G maxM sMp sylS.
have [g sSHg]: exists g, S \subset H :^ g.
  have [Sg' sylSg']:= Sylow_exists p H.
  have [g _ ->] := Sylow_trans (sigma_Sylow_G maxH sHp sylSg') sylS_G.
  by exists g; rewrite conjSg (pHall_sub sylSg').
have{notjMH} neqHgM: H :^ g != M.
  by apply: contraNneq notjMH => <-; rewrite orbit_sym mem_orbit ?in_setT.
do [split; apply: contra neqHgM] => [|nilMs].
  rewrite !inE -(p_rank_Sylow sylS) -rank_pgroup //= => rS_gt3.
  have uniqS: S \in 'U := rank3_Uniqueness (mFT_pgroup_proper pS) rS_gt3.
  have defUS: 'M(S) = [set M] := def_uniq_mmax uniqS maxM sSM.
  by rewrite (eq_uniq_mmax defUS _ sSHg) ?mmaxJ.
have nsSM: S <| M.
  have nsMsM: M`_\sigma <| M by exact: pcore_normal.
  have{sylS} sylS: p.-Sylow(M`_\sigma) S.
    apply: pHall_subl (pcore_sub _ _) sylS => //.
    by rewrite (sub_Hall_pcore (Msigma_Hall maxM)) ?(pi_pgroup pS).
  rewrite (nilpotent_Hall_pcore nilMs sylS).
  by rewrite (char_normal_trans (pcore_char _ _)).
have sNS_Hg: 'N(S) \subset H :^ g.
  rewrite -sub_conjgV -normJ (norm_sigma_Sylow sHp) //.
  by rewrite (pHall_subl _ (subsetT _)) ?sub_conjgV // pHallJ ?in_setT.
have ltHg: H :^ g \proper G by rewrite mmax_proper ?mmaxJ //.
rewrite (mmax_max maxM ltHg) // -(mmax_normal maxM nsSM) //.
by apply: contraTneq sNS_Hg => ->; rewrite norm1 proper_subn.
Qed.

(* This is B & G, Lemma 10.13. *)
Lemma basic_p2maxElem_structure p A P :
    A \in 'E_p^2(G) :&: 'E*_p(G) -> p.-group P -> A \subset P -> ~~ abelian P ->
  let Z0 := ('Ohm_1('Z(P)))%G in
  [/\ (*a*) Z0 \in 'E_p^1(A),
      (*b*) exists Y : {group gT},
            [/\ cyclic Y, Z0 \subset Y
              & forall A0, A0 \in 'E_p^1(A) :\ Z0 -> A0 \x Y = 'C_P(A)]
    & (*c*) [transitive 'N_P(A), on 'E_p^1(A) :\ Z0| 'JG]].
Proof.
case/setIP=> Ep2A maxA pP sAP not_cPP Z0; set E1A := 'E_p^1(A).
have p_pr: prime p := pnElem_prime Ep2A; have [_ abelA dimA] := pnElemP Ep2A.
have [oA [pA cAA _]] := (card_pnElem Ep2A, and3P abelA).
have [p_gt0 p_gt1] := (prime_gt0 p_pr, prime_gt1 p_pr).
have{maxA} maxA S:
  p.-group S -> A \subset S -> A \in 'E*_p(S) /\ 'Ohm_1('C_S(A)) = A.
- move=> pS sAS; suff maxAS: A \in 'E*_p(S) by rewrite (Ohm1_cent_max maxAS).
  by rewrite (subsetP (pmaxElemS p (subsetT S))) // inE maxA inE.
have [S sylS sPS] := Sylow_superset (subsetT P) pP.
pose Z1 := 'Ohm_1('Z(S))%G; have sZ1Z: Z1 \subset 'Z(S) := Ohm_sub 1 _.
have [pS sAS] := (pHall_pgroup sylS, subset_trans sAP sPS).
have [maxAS defC1] := maxA S pS sAS; set C := 'C_S(A) in defC1.
have sZ0A: Z0 \subset A by rewrite -defC1 OhmS // setISS // centS.
have sZ1A: Z1 \subset A by rewrite -defC1 OhmS // setIS // centS.
have [pZ0 pZ1]: p.-group Z0 /\ p.-group Z1 by split; exact: pgroupS pA.
have sZ10: Z1 \subset Z0.
  rewrite -[gval Z1]Ohm_id OhmS // subsetI (subset_trans sZ1A) //=.
  by rewrite (subset_trans sZ1Z) // subIset // centS ?orbT.
have ntZ1: Z1 :!=: 1.
  have: A :!=: 1 by rewrite -cardG_gt1 oA (ltn_exp2l 0).
  apply: contraNneq; rewrite -subG1 -(setIidPr sZ1Z) => /TI_Ohm1.
  by rewrite setIid => /(trivg_center_pgroup pS) <-.
have EpZ01: abelian C -> Z1 = Z0 /\ Z0 \in E1A.
  move=> cCC; have [eqZ0A | ltZ0A] := eqVproper sZ0A.
    rewrite (abelianS _ cCC) // in not_cPP.
    by rewrite subsetI sPS centsC -eqZ0A (subset_trans (Ohm_sub _ _)) ?subsetIr.
  have leZ0p: #|Z0| <= p ^ 1.
    by rewrite (card_pgroup pZ0) leq_exp2l // -ltnS -dimA properG_ltn_log.
  have [_ _ [e oZ1]] := pgroup_pdiv pZ1 ntZ1.
  have{e oZ1}: #|Z1| >= p by rewrite oZ1 (leq_exp2l 1).
  rewrite (geq_leqif (leqif_trans (subset_leqif_card sZ10) (leqif_eq leZ0p))).
  rewrite [E1A]p1ElemE // !inE sZ0A; case/andP=> sZ01 ->.
  by split=> //; apply/eqP; rewrite -val_eqE eqEsubset sZ10.
have [A1 neqA1Z EpA1]: exists2 A1, A1 != Z1 & #|Z1| = p -> A1 \in E1A.
  have [oZ1 |] := #|Z1| =P p; last by exists 1%G; rewrite // eq_sym.
  have [A1 defA]:= abelem_split_dprod abelA sZ1A.
  have{defA} [_ defA _ tiA1Z1] := dprodP defA.
  have EpZ1: Z1 \in E1A by rewrite [E1A]p1ElemE // !inE sZ1A /= oZ1.
  suffices: A1 \in E1A by exists A1; rewrite // eq_sym; exact/(TIp1ElemP EpZ1).
  rewrite [E1A]p1ElemE // !inE -defA mulG_subr /=.
  by rewrite -(mulKn #|A1| p_gt0) -{1}oZ1 -TI_cardMg // defA oA mulKn.
pose cplA1C Y := [/\ cyclic Y, Z0 \subset Y, A1 \x Y = C & abelian C].
have [Y [{cplA1C} cycY sZ0Y defC cCC]]: exists Y, cplA1C Y.
  have [rSgt2 | rSle2] := ltnP 2 'r(S).
    rewrite (rank_pgroup pS) in rSgt2; have oddS := mFT_odd S.
    have max2AS: A \in 'E_p^2(S) :&: 'E*_p(S) by rewrite 3!inE sAS abelA dimA.
    have oZ1: #|Z1| = p by case/Ohm1_ucn_p2maxElem: max2AS => // _ [].
    have{EpA1} EpA1 := EpA1 oZ1; have [sA1A abelA1 oA1] := pnElemPcard EpA1.
    have EpZ1: Z1 \in E1A by rewrite [E1A]p1ElemE // !inE sZ1A /= oZ1.
    have [_ defA cA1Z tiA1Z] := dprodP (p2Elem_dprodP Ep2A EpA1 EpZ1 neqA1Z).
    have defC: 'C_S(A1) = C.
      rewrite /C -defA centM setICA setIC ['C_S(Z1)](setIidPl _) // centsC.
      by rewrite (subset_trans sZ1Z) ?subsetIr.
    have rCSA1: 'r_p('C_S(A1)) <= 2.
      by rewrite defC -p_rank_Ohm1 defC1 (p_rank_abelem abelA) dimA.
    have sA1S := subset_trans sA1A sAS.
    have nnS: p.-narrow S by apply/implyP=> _; apply/set0Pn; exists A.
    have [] := narrow_cent_dprod pS oddS rSgt2 nnS oA1 sA1S rCSA1.
    set Y := _ :&: _; rewrite {}defC => cycY _ _ defC; exists [group of Y].
    have cCC: abelian C; last split=> //.
      apply/center_idP; rewrite -(center_dprod defC).
      rewrite (center_idP (abelem_abelian abelA1)).
      by rewrite (center_idP (cyclic_abelian cycY)).
    have{EpZ01} [<- _] := EpZ01 cCC; rewrite subsetI (subset_trans sZ1Z) //.
    by rewrite setIS ?centS // (subset_trans (Ohm_sub 1 _)) ?ucn_sub.
  have not_cSS := contra (abelianS sPS) not_cPP.
  have:= mFT_rank2_Sylow_cprod sylS rSle2 not_cSS.
  case=> E [_ dimE3 eE] [Y cycY [defS defY1]].
  have [[_ mulEY cEY] cYY] := (cprodP defS, cyclic_abelian cycY).
  have defY: 'Z(S) = Y.
    case/cprodP: (center_cprod defS) => _ <- _.
    by rewrite (center_idP cYY) -defY1 mulSGid ?Ohm_sub.
  have pY: p.-group Y by rewrite -defY (pgroupS (center_sub S)).
  have sES: E \subset S by rewrite -mulEY mulG_subl.
  have pE := pgroupS sES pS.
  have defS1: 'Ohm_1(S) = E.
    apply/eqP; rewrite (OhmE 1 pS) eqEsubset gen_subG andbC.
    rewrite sub_gen; last by rewrite subsetI sES sub_LdivT.
    apply/subsetP=> ey /LdivP[]; rewrite -mulEY.
    case/imset2P=> e y Ee Yy -> eyp; rewrite groupM //.
    rewrite (subsetP (center_sub E)) // -defY1 (OhmE 1 pY) mem_gen //.
    rewrite expgMn in eyp; last by red; rewrite -(centsP cEY).
    by rewrite (exponentP eE) // mul1g in eyp; rewrite !inE Yy eyp eqxx.
  have sAE: A \subset E by rewrite -defS1 -(Ohm1_id abelA) OhmS.
  have defC: A * Y = C.
    rewrite /C -mulEY setIC -group_modr; last first.
      by rewrite -defY subIset // orbC centS.
    congr (_ * _); apply/eqP; rewrite /= setIC eqEcard subsetI sAE.
    have pCEA: p.-group 'C_E(A) := pgroupS (subsetIl E _) pE.
    rewrite -abelianE cAA (card_pgroup pCEA) oA leq_exp2l //= leqNgt.
    apply: contraL cycY => dimCEA3.
    have sAZE: A \subset 'Z(E).
      rewrite subsetI sAE // centsC (sameP setIidPl eqP) eqEcard subsetIl /=.
      by rewrite (card_pgroup pE) (card_pgroup pCEA) dimE3 leq_exp2l.
    rewrite abelian_rank1_cyclic // -ltnNge (rank_pgroup pY).
    by rewrite (p_rank_abelian p cYY) defY1 -dimA lognSg.
  have cAY: Y \subset 'C(A) by apply: centSS cEY.
  have cCC: abelian C by rewrite -defC abelianM cAA cYY.
  have{EpZ01} [eqZ10 EpZ1] := EpZ01 cCC; rewrite -eqZ10 in EpZ1.
  have sZ0Y: Z0 \subset Y by rewrite -eqZ10 -defY Ohm_sub.
  have{EpA1} EpA1 := EpA1 (card_pnElem EpZ1).
  have [sA1A _ oA1] := pnElemPcard EpA1.
  have [_ defA _ tiA1Z] := dprodP (p2Elem_dprodP Ep2A EpA1 EpZ1 neqA1Z).
  exists Y; split; rewrite // dprodE ?(centSS _ sA1A cAY) ?prime_TIg ?oA1 //.
    by rewrite -(mulSGid sZ0Y) -eqZ10 mulgA defA.
  apply: contraL cycY => sA1Y; rewrite abelian_rank1_cyclic // -ltnNge.
  by rewrite -dimA -rank_abelem ?rankS // -defA eqZ10 mul_subG.
have{EpZ01} [eqZ10 EpZ0] := EpZ01 cCC; have oZ0 := card_pnElem EpZ0.
have{EpA1} EpA1: A1 \in E1A by rewrite EpA1 ?eqZ10.
have [sA1A _ oA1] := pnElemPcard EpA1; rewrite {}eqZ10 in neqA1Z.
have [_ defA _ tiA1Z] := dprodP (p2Elem_dprodP Ep2A EpA1 EpZ0 neqA1Z).
split=> //; first exists (P :&: Y)%G.
  have sPY_Y := subsetIr P Y; rewrite (cyclicS sPY_Y) //.
  rewrite subsetI (subset_trans sZ0A) //= sZ0Y.
  split=> // A0 /setD1P[neqA0Z EpA0]; have [sA0A _ _] := pnElemP EpA0.
  have [_ mulA0Z _ tiA0Z] := dprodP (p2Elem_dprodP Ep2A EpA0 EpZ0 neqA0Z).
  have{defC} [_ defC cA1Y tiA1Y] := dprodP defC.
  rewrite setIC -{2}(setIidPr sPS) setIAC.
  apply: dprod_modl (subset_trans sA0A sAP); rewrite -defC dprodE /=.
  - by rewrite -(mulSGid sZ0Y) !mulgA mulA0Z defA.
  - rewrite (centSS (subxx Y) sA0A) // -defA centM subsetI cA1Y /=.
    by rewrite sub_abelian_cent ?cyclic_abelian.
  rewrite setIC -(setIidPr sA0A) setIA -defA -group_modr //.
  by rewrite (setIC Y) tiA1Y mul1g setIC.
apply/imsetP; exists A1; first by rewrite 2!inE neqA1Z.
apply/eqP; rewrite eq_sym eqEcard; apply/andP; split.
  apply/subsetP=> _ /imsetP[x /setIP[Px nAx] ->].
  rewrite 2!inE /E1A -(normP nAx) pnElemJ EpA1 andbT -val_eqE /=.
  have nZ0P: P \subset 'N(Z0).
    by rewrite (char_norm_trans (Ohm_char 1 _)) // gFnorm.
  by rewrite -(normsP nZ0P x Px) (inj_eq (@conjsg_inj _ x)).
have pN: p.-group 'N_P(_) := pgroupS (subsetIl P _) pP.
have defCPA: 'N_('N_P(A))(A1) = 'C_P(A).
  apply/eqP; rewrite eqEsubset andbC subsetI setIS ?cent_sub //.
  rewrite subIset /=; last by rewrite orbC cents_norm ?centS.
  rewrite setIAC (subset_trans (subsetIl _ _)) //= subsetI subsetIl /=.
  rewrite -defA centM subsetI andbC subIset /=; last first.
    by rewrite centsC (subset_trans (Ohm_sub 1 _)) ?subsetIr.
  have nC_NP: 'N_P(A1) \subset 'N('C(A1)) by rewrite norms_cent ?subsetIr.
  rewrite -quotient_sub1 // subG1 trivg_card1.
  rewrite (pnat_1 (quotient_pgroup _ (pN _))) //.
  rewrite -(card_isog (second_isog nC_NP)) /= (setIC 'C(A1)).
  by apply: p'group_quotient_cent_prime; rewrite ?subsetIr ?oA1.
have sCN: 'C_P(A) \subset 'N_P(A) by rewrite setIS ?cent_sub.
have nA_NCPA: 'N_P('C_P(A)) \subset 'N_P(A).
  have [_ defCPA1] := maxA P pP sAP.
  by rewrite -{2}defCPA1 setIS // (char_norm_trans (Ohm_char 1 _)).
rewrite card_orbit astab1JG /= {}defCPA.
rewrite -(leq_add2l (Z0 \in E1A)) -cardsD1 EpZ0 (card_p1Elem_p2Elem Ep2A) ltnS.
rewrite dvdn_leq ?(pfactor_dvdn 1) ?indexg_gt0 // -divgS // logn_div ?cardSg //.
rewrite subn_gt0  properG_ltn_log ?pN //= (proper_sub_trans _ nA_NCPA) //.
rewrite (nilpotent_proper_norm (pgroup_nil pP)) // properEneq subsetIl andbT.
by apply: contraNneq not_cPP => <-; rewrite (abelianS (setSI _ sPS)).
Qed.

(* This is B & G, Proposition 10.14(a). *)
Proposition beta_not_narrow p : p \in \beta(G) ->
      [disjoint 'E_p^2(G) & 'E*_p(G)]
  /\ (forall P, p.-Sylow(G) P -> [disjoint 'E_p^2(P) & 'E*_p(P)]).
Proof.
move/forall_inP=> nnG.
have nnSyl P: p.-Sylow(G) P -> [disjoint 'E_p^2(P) & 'E*_p(P)].
  by move/nnG; rewrite negb_imply negbK setI_eq0 => /andP[].
split=> //; apply/pred0Pn=> [[E /andP[/= Ep2E EpmE]]].
have [_ abelE dimE]:= pnElemP Ep2E; have pE := abelem_pgroup abelE.
have [P sylP sEP] := Sylow_superset (subsetT E) pE.
case/pred0Pn: (nnSyl P sylP); exists E; rewrite /= 2!inE sEP abelE dimE /=.
by rewrite (subsetP (pmaxElemS p (subsetT P))) // inE EpmE inE.
Qed.

(* This is B & G, Proposition 10.14(b). *)
Proposition beta_noncyclic_uniq p R :
  p \in \beta(G) -> p.-group R -> 'r(R) > 1 -> R \in 'U.
Proof.
move=> b_p pR rRgt1; have [P sylP sRP] := Sylow_superset (subsetT R) pR.
rewrite (rank_pgroup pR) in rRgt1; have [A Ep2A] := p_rank_geP rRgt1.
have [sAR abelA dimA] := pnElemP Ep2A; have p_pr := pnElem_prime Ep2A.
case: (pickP [pred F in 'E_p(P) | A \proper F]) => [F | maxA]; last first.
  have [_ nnSyl] := beta_not_narrow b_p; case/pred0Pn: (nnSyl P sylP).
  exists A; rewrite /= (subsetP (pnElemS p 2 sRP)) //.
  apply/pmaxElemP; split=> [|F EpF]; first by rewrite inE (subset_trans sAR).
  by case/eqVproper=> [// | ltAF]; case/andP: (maxA F).
case/andP=> /pElemP[_ abelF] ltAF; have [pF cFF _] := and3P abelF.
apply: uniq_mmaxS sAR (mFT_pgroup_proper pR) _.
have rCAgt2: 'r('C(A)) > 2.
  rewrite -dimA (leq_trans (properG_ltn_log pF ltAF)) // -(rank_abelem abelF).
  by rewrite rankS // centsC (subset_trans (proper_sub ltAF)).    
by apply: cent_rank3_Uniqueness rCAgt2; rewrite (rank_abelem abelA) dimA.
Qed.

(* This is B & G, Proposition 10.14(c). *)
Proposition beta_subnorm_uniq p P X :
  p \in \beta(G) -> p.-Sylow(G) P -> X \subset P -> 'N_P(X)%G \in 'U.
Proof.
move=> b_p sylP sXP; set Q := 'N_P(X)%G.
have pP := pHall_pgroup sylP; have pQ: p.-group Q := pgroupS (subsetIl _ _) pP.
have [| rQle1] := ltnP 1 'r(Q); first exact: beta_noncyclic_uniq pQ.
have cycQ: cyclic Q.
  by rewrite (odd_pgroup_rank1_cyclic pQ) ?mFT_odd -?rank_pgroup.
have defQ: P :=: Q.
  apply: (nilpotent_sub_norm (pgroup_nil pP) (subsetIl _ _)).
  by rewrite setIS // char_norms // sub_cyclic_char // subsetI sXP normG.
have:= forall_inP b_p P; rewrite inE negb_imply ltnNge; move/(_ sylP).
by rewrite defQ -(rank_pgroup pQ) (leq_trans rQle1).
Qed.

(* This is B & G, Proposition 10.14(d). *)
Proposition beta_norm_sub_mmax M Y :
  M \in 'M -> \beta(M).-subgroup(M) Y -> Y :!=: 1 -> 'N(Y) \subset M.
Proof.
move=> maxM /andP[sYM bY] ntY.
have [F1 | [q q_pr q_dv_FY]] := trivgVpdiv 'F(Y).
  by rewrite -(trivg_Fitting (solvableS sYM (mmax_sol maxM))) F1 eqxx in ntY.
pose X := 'O_q(Y); have qX: q.-group X := pcore_pgroup q _.
have ntX: X != 1.
  apply: contraTneq q_dv_FY => X1; rewrite -p'natE // -partn_eq1 //.
  rewrite -(card_Hall (nilpotent_pcore_Hall q (Fitting_nil Y))).
  by rewrite /= p_core_Fitting -/X X1 cards1.
have bMq: q \in \beta(M) by apply: (pgroupP (pgroupS (Fitting_sub Y) bY)).
have b_q: q \in \beta(G) by move: bMq; rewrite -predI_sigma_beta //; case/andP.
have sXM: X \subset M := subset_trans (pcore_sub q Y) sYM.
have [P sylP sXP] := Sylow_superset sXM qX; have [sPM qP _] := and3P sylP.
have sylPG: q.-Sylow(G) P by rewrite (sigma_Sylow_G maxM) ?beta_sub_sigma.
have uniqNX: 'M('N_P(X)) = [set M].
  apply: def_uniq_mmax => //; last by rewrite subIset ?sPM.
  exact: (beta_subnorm_uniq b_q).
rewrite (subset_trans (char_norms (pcore_char q Y))) //.
rewrite (sub_uniq_mmax uniqNX) ?subsetIr // mFT_norm_proper //.
by rewrite (sub_mmax_proper maxM).
Qed.

End Ten.



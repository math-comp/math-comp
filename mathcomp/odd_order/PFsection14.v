(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime binomial ssralg poly finset.
Require Import fingroup morphism perm automorphism quotient action finalg zmodp.
Require Import gfunctor gproduct center cyclic commutator gseries nilpotent.
Require Import pgroup sylow hall abelian maximal frobenius.
Require Import matrix mxalgebra mxrepresentation mxabelem vector.
Require Import BGsection1 BGsection3 BGsection7.
Require Import BGsection14 BGsection15 BGsection16 BGappendixC.
Require Import ssrnum rat algC cyclotomic algnum.
Require Import classfun character integral_char inertia vcharacter.
Require Import PFsection1 PFsection2 PFsection3 PFsection4.
Require Import PFsection5 PFsection6 PFsection7 PFsection8 PFsection9.
Require Import PFsection10 PFsection11 PFsection12 PFsection13.

(******************************************************************************)
(* This file covers Peterfalvi, Section 14: Non_existence of G.               *)
(* It completes the proof of the Odd Order theorem.                           *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory FinRing.Theory Num.Theory.

Section Fourteen.

Variable gT : minSimpleOddGroupType.
Local Notation G := (TheMinSimpleOddGroup gT).
Implicit Types (p q : nat) (x y z : gT).
Implicit Types H K L N P Q R S T U W : {group gT}.

Local Notation "#1" := (inord 1) (at level 0).

(* Supplementary results that apply to both S and T, but that are not         *)
(* formally stated as such; T, V, L, tau1L and phi are only used at the end   *)
(* of this section, to state and prove FTtype2_support_coherence.             *)
Section MoreSTlemmas.

Local Open Scope ring_scope.
Variables W W1 W2 S T U V L : {group gT}.
Variables (tau1L : {additive 'CF(L) -> 'CF(G)}) (phi : 'CF(L)).

(* Implicit (dependent) forward assuptions. *)
Hypotheses (defW : W1 \x W2 = W) (xdefW : W2 \x W1 = W) (maxL : L \in 'M).

Local Notation "` 'S'" := (gval S) (at level 0, only parsing) : group_scope.
Local Notation P := `S`_\F%G.
Local Notation "` 'P'" := `S`_\F (at level 0) : group_scope.
Local Notation PU := S^`(1)%G.
Local Notation "` 'PU'" := `S^`(1)%g (at level 0) : group_scope.
Local Notation "` 'L'" := (gval L) (at level 0, only parsing).
Local Notation H := `L`_\F%G.
Local Notation "` 'H'" := `L`_\F%g (at level 0, format "` 'H'") : group_scope.

Let p := #|W2|.
Let q := #|W1|.
Let u := #|U|.
Let v := #|V|.
Let h := #|H|.
Let e := #|L : H|.
Let ccG A := class_support A G.

Let calL := seqIndD H L H 1.
Let betaL := 'Ind[L, H] 1 - phi.
Local Notation tauL := (FT_DadeF maxL).

(* Explicit (non-dependent) forward assumptions. *)
Hypotheses (StypeP : of_typeP S U defW) (TtypeP : of_typeP T V xdefW).
Hypothesis (cohL : coherent_with calL L^# tauL tau1L) (Lphi : phi \in calL).

(* The remaining assumptions can be generated as backchaining gools. *)
Hypotheses (maxS : S \in 'M) (maxT : T \in 'M).

Let pddS := FT_prDade_hypF maxS StypeP.
Let pddT := FT_prDade_hypF maxT TtypeP.
Let ctiWG : cyclicTI_hypothesis G defW := pddS.
Let sigma := cyclicTIiso ctiWG.
Let w_ i j := cyclicTIirr defW i j.

(* An inequality used in the proof of (14.11.4), at the bottom of page 90, to *)
(* show that 1/uq and 1/vp are less that 1/2q^2 (so Wn is either W1 or W2).   *)
Lemma FTtypeP_complV_ltr (Wn : {group gT}) :
  (#|Wn| <= q)%N -> (u * q)%:R^-1 < (2 * #|Wn| ^ 2)%:R^-1 :> algC.
Proof.
move=> leWn_q; rewrite !natrM ltf_pinv ?rpredM ?qualifE ?gt0CG ?ltr0n //.
rewrite -!natrM ltr_nat (@leq_ltn_trans (2 * q ^ 2)) ?mulnA ?leq_mul // mul2n.
have: [Frobenius U <*> W1 = U ><| W1] by have [[]] := FTtypeP_facts maxS StypeP.
by move/ltn_odd_Frobenius_ker/implyP; rewrite mFT_odd ltn_pmul2r ?cardG_gt0.
Qed.

(* This formalizes the loose symmetry used in (14.11.3) to show that #[g] is  *)
(* coprime to pq.                                                             *)
Lemma coprime_typeP_Galois_core g :
  typeP_Galois StypeP -> g \notin ccG W^# -> g \notin ccG P^# -> coprime #[g] p.
Proof.
move=> galS W'g; apply: contraR => p_g.
have ntg: g != 1%g by apply: contraNneq p_g => ->; rewrite order1 coprime1n.
have [pr_q pr_p]: prime q /\ prime p := FTtypeP_primes maxS StypeP.
have [[_ hallW1 _ defS] [_ _ _ defPU] _ [_ _ sW2P _ regPUW1] _] := StypeP.
have coPUq: coprime #|PU| q by rewrite (coprime_sdprod_Hall_r defS).
have [[_ _ nPUW1 _] [_ _ nPU _]] := (sdprodP defS, sdprodP defPU).
have ntP: P :!=: 1%g := mmax_Fcore_neq1 maxS.
have frobPU: [Frobenius PU = P ><| U].
  have notS5 := FTtype5_exclusion maxS.
  have inN1 x: x \in 'N(1) by rewrite norm1 inE.
  have [_ ntU _ _] := compl_of_typeII_IV maxS StypeP notS5.
  have [] := typeP_Galois_P maxS notS5 galS; rewrite Ptype_factor_prime //.
  rewrite (group_inj (Ptype_Fcore_kernel_trivial _ _)) // => F [fP [fU _]].
  rewrite Ptype_Fcompl_kernel_trivial //.
  case=> /trivgP injfU fJ [_ /isomP[injfP _] _] _.
  apply/Frobenius_semiregularP=> // y /setD1P[nty Uy].
  apply/trivgP/subsetP=> x /setIP[Px /cent1P-cxy]; apply: contraR nty.
  rewrite -(morph_injm_eq1 injfU) // -val_eqE -(cosetpre1 1) !(inN1, inE) /=.
  rewrite -(morph_injm_eq1 injfP) ?mem_quotient //= => /mulfI/inj_eq <-.
  rewrite mulr1 -[_ * _]fJ ?mem_quotient //= qactE ?dom_qactJ //=.
  by rewrite conjgE cxy mulKg.
have pP: p.-group P by have [_ [/andP[]]] := FTtypeP_facts _ StypeP.
have{p_g}[y [a P1a cagy]]: exists y, exists2 a, a \in P^# & g ^ y \in 'C[a].
  have sylP: p.-Sylow(G) P.
    have [/Hall_pi/= hallP _ _] := FTcore_facts maxS; apply: etrans hallP.
    have [_ _ [n ->]] := pgroup_pdiv pP (mmax_Fcore_neq1 maxS).
    by apply/eq_pHall => r1; rewrite pi_of_exp ?pi_of_prime.
  have [y _ Pa] := Sylow_Jsub sylP (subsetT _) (p_elt_constt p g).
  pose a := g.`_p ^ y; have{Pa} Pa: a \in P by rewrite -cycle_subG cycleJ.
  exists y, a; last by rewrite cent1C /a conjXg groupX ?cent1id.
  rewrite !inE conjg_eq1 (contraNneq _ p_g) // => /constt1P/p'nat_coprime-> //.
  exact: pnat_id.
have /(mem_sdprod defS)[x [w [PUx W1w Dgy _]]]: g ^ y \in S.
  have A0a: a \in 'A0(S) := subsetP (Fcore_sub_FTsupp0 maxS) a P1a.
  have [_ _ _ _ [tiA0 _]] := FTtypeP_facts _ StypeP.
  by rewrite (subsetP (cent1_normedTI tiA0 A0a)) // 2!inE.
suffices w_eq1: w = 1%g.
  have sCaP: 'C_PU[a] \subset P := Frobenius_cent1_ker frobPU P1a.
  rewrite -[g](conjgK y) mem_imset2 ?inE //= conjg_eq1 ntg /=.
  by rewrite (subsetP sCaP) // inE cagy Dgy w_eq1 mulg1 PUx.
apply: contraNeq W'g => ntw; have nPUw := subsetP nPUW1 w W1w.
have{x PUx Dgy} /imset2P[x z W2w_x _ Dgy]: g ^ y \in class_support (W2 :* w) PU.
  rewrite -(regPUW1 w) ?inE ?ntw // class_supportEr -cover_imset.
  have coPUw := coprime_dvdr (order_dvdG W1w) coPUq.
  have [/cover_partition-> _] := partition_cent_rcoset nPUw coPUw.
  by rewrite Dgy mem_rcoset mulgK.
rewrite -[g](conjgK (y * z^-1)%g) mem_imset2 ?inE //= conjg_eq1 ntg /= conjgM.
by rewrite Dgy conjgK -(dprodWC defW) -[x](mulgKV w) mem_mulg -?mem_rcoset.
Qed.

Hypothesis Stype2 : FTtype S == 2.

(* This is used to bound #|ccG P^#| and #|ccG Q^#| in the proof of (14.11.4). *)
Lemma FTtype2_cc_core_ler : #|G|%:R^-1 * #|ccG P^#|%:R <= (u * q)%:R^-1 :> algC.
Proof.
have ->: (u * q)%:R^-1 = #|S|%:R^-1 * #|P|%:R :> algC.
  have [[_ _ _ /sdprod_card <-] [_ _ _ /sdprod_card <-] _ _ _] := StypeP.
  by rewrite mulrC -mulnA [in RHS]natrM invfM mulVKf ?neq0CG.
have [_ _] := FTtypeII_ker_TI maxS Stype2; rewrite FTsupp1_type2 // => tiP1.
rewrite {tiP1}(card_support_normedTI tiP1) natrM natf_indexg ?subsetT //.
rewrite mulrCA mulKf ?neq0CG // mulrC ler_pmul2l ?invr_gt0 ?gt0CG // leC_nat.
by rewrite cardsDS ?sub1G ?leq_subr.
Qed.

Hypotheses (maxNU_L : L \in 'M('N(U))) (phi1 : phi 1%g = e%:R).

(* This is Peterfalvi (14.11.2), stated for S and L rather than T and M; it  *)
(* is loosely used in this form at the very end of the proof of (14.16).     *)
Lemma FTtype2_support_coherence :
    (u.-1 %/ q < h.-1 %/ e)%N -> (v.-1 %/ p < h.-1 %/ e)%N -> 
  [/\ e = (p * q)%N
    & exists nb, exists2 chi, chi = tau1L phi \/ chi = - tau1L phi^*%CF
    & tauL betaL = \sum_ij (-1)^+ nb ij *: sigma 'chi_ij - chi].
Proof.
move=> ub_u ub_v; have nsHL : H <| L := gFnormal _ _.
have pairST := of_typeP_pair maxS StypeP maxT TtypeP.
have [//|frobL sUH defL] := FTtypeII_support_facts maxS StypeP _ pairST maxNU_L.
have Ltype1 := FT_Frobenius_type1 maxL frobL.
have irr_phi: phi \in irr L by apply: FTtype1_Ind_irr Lphi.
have betaL_P := FTtypeI_bridge_facts _ _ Ltype1 cohL Lphi phi1.
have e_dv_h1: e %| h.-1 by apply: Frobenius_ker_dvd_ker1.
pose a i j := '[tauL betaL, sigma (w_ i j)].
have a0j j: j != 0 -> (a 0 j == 1 %[mod 2])%C.
  rewrite /a => nz_j; case/betaL_P: StypeP => _ _ -> //.
  by case=> [[_ /idPn[]] | [//]]; rewrite -natf_div // leC_nat -ltnNge.
have ai0 i: i != 0 -> (a i 0 == 1 %[mod 2])%C.
  rewrite /a (cycTIisoC _ pddT) => nz_i; case/betaL_P: TtypeP => _ _ -> //.
  by case=> [[_ /idPn[]] | [//]]; rewrite -natf_div // leC_nat -ltnNge.
have HbetaL: betaL \in 'CF(L, H^#) by apply: cfInd1_sub_lin_on Lphi phi1.
have betaL_W_0: {in cyclicTIset defW, tauL betaL =1 \0}.
  move=> z; case/betaL_P: StypeP => tiAM_W _ _ _.
  rewrite !inE -(setCK W) inE => /andP[_]; apply: cfun_onP z.
  apply: cfun_onS (Dade_cfunS _ _); rewrite FT_DadeF_supportE -disjoints_subset.
  rewrite -FTsupp_Frobenius // -setI_eq0 -subset0 -tiAM_W setIS //.
  by rewrite setUC subsetU ?sub_class_support.
have calL_gt1: (1 < size calL)%N.
  by apply: seqInd_nontrivial Lphi; rewrite ?mFT_odd.
have [] := Dade_Ind1_sub_lin cohL calL_gt1 irr_phi Lphi phi1; rewrite -/betaL.
rewrite -/calL odd_Frobenius_index_ler ?mFT_odd //= -/e -/h.
case=> _ a00 ZbetaL [Gamma [o_tau1_Ga o_1_Ga [aa Zaa Dbeta] []// _ ubGa _]].
have{a00} a00: a 0 0 = 1 by rewrite /a /w_ cycTIirr00 cycTIiso1.
have{a0j ai0} a_odd i j: (a i j == 1 %[mod 2])%C.
  have [[-> | /ai0 ai01] [-> | /a0j a0j1] //] := (eqVneq i 0, eqVneq j 0).
    by rewrite a00 (eqCmod_nat 2 1 1).
  by rewrite -(eqCmodDr _ 1) -{1}a00 cycTIiso_cfdot_exchange // eqCmodD.
have [_ o_tauLeta _ _] := FTtypeI_bridge_facts _ StypeP Ltype1 cohL Lphi phi1.
pose etaW := map sigma (irr W).
have o1eta: orthonormal etaW := cycTIiso_orthonormal _.
have [X etaX [Y [defGa oXY oYeta]]] := orthogonal_split etaW (Gamma + 1).
have lbY: 0 <= '[Y] ?= iff (Y == 0).
  by split; rewrite ?cfnorm_ge0 // eq_sym cfnorm_eq0.
have [b Db defX] := orthonormal_span o1eta etaX.
do [rewrite addrC !addrA addrAC -addrA; set Z := _ - _] in Dbeta.
have oZeta: orthogonal Z etaW.
  apply/orthoPl=> xi /memv_span; apply: {xi}(span_orthogonal o_tauLeta).
  rewrite rpredB ?rpredZ ?big_seq ?rpred_sum ?memv_span ?map_f // => xi Lxi.
  by rewrite rpredZ ?memv_span ?map_f.
have lb_b ij (b_ij := b (sigma 'chi_ij)):
  1 <= `|b_ij| ^+ 2 ?= iff [exists n : bool, b_ij == (-1) ^+ n].
- have /codomP[[i j] Dij] := dprod_Iirr_onto defW ij.
  have{b_ij} ->: b_ij = a i j.
    rewrite /a /w_ -Dij Dbeta defGa 2!cfdotDl. 
    have ->: '[X, sigma 'chi_ij] = b_ij by rewrite /b_ij Db.
    by rewrite (orthoPl oYeta) ?(orthoPl oZeta) ?map_f ?mem_irr // !addr0.
  have Zaij: a i j \in Cint by rewrite Cint_cfdot_vchar ?cycTIiso_vchar.
  rewrite Cint_normK //; split.
    rewrite sqr_Cint_ge1 //; apply: contraTneq (a_odd i j) => ->.
    by rewrite (eqCmod_nat 2 0 1).
  apply/eqP/exists_eqP=> [a2_1|[n ->]]; last by rewrite sqrr_sign.
  rewrite (CintEsign Zaij) normC_def conj_Cint // -expr2 -a2_1 sqrtC1 mulr1.
  by exists (a i j < 0).
have ub_e: e%:R <= #|Iirr W|%:R ?= iff (e == p * q)%N :> algC.
  rewrite lerif_nat card_Iirr_cyclic //; last by have [] := ctiWG.
  rewrite -(dprod_card xdefW); apply: leqif_eq.
  case: defL => [|[y Qy]] defL; rewrite /e -(index_sdprod defL).
    by rewrite leq_pmull ?cardG_gt0.
  suffices /normP <-: y \in 'N(W1).
    by rewrite -conjYg !cardJg (dprodWY defW) -(dprod_card xdefW).
  have cQQ: abelian T`_\F by have [_ [/and3P[]]] := FTtypeP_facts maxT TtypeP.
  have sW1Q: W1 \subset T`_\F by have [_ _ _ []] := TtypeP.
  by rewrite (subsetP _ y Qy) // sub_abelian_norm.
have /(_ predT) := lerif_add (lerif_sum (in1W lb_b)) lbY.
rewrite sumr_const addr0 => /(lerif_trans ub_e)/ger_lerif/esym.
have ->: \sum_i `|b (sigma 'chi_i)| ^+ 2 = '[X].
  rewrite defX cfnorm_sum_orthonormal // big_map (big_nth 0) big_mkord.
  by rewrite size_tuple; apply: eq_bigr => ij _; rewrite -tnth_nth.
rewrite -cfnormDd // -defGa cfnormDd // cfnorm1 -ler_subr_addr ubGa.
case/and3P=> /eqP-De /'forall_exists_eqP/fin_all_exists[/= n Dn] /eqP-Y0.
pose chi := X - tauL betaL; split=> //; exists n, chi; last first.
  apply: canRL (addrK _) _; rewrite addrC subrK defX big_map (big_nth 0).
  by rewrite big_mkord size_tuple; apply: eq_bigr => ij; rewrite -tnth_nth Dn.
have Z1chi: chi \in dirr G.
  rewrite dirrE rpredB //=; last first.
    rewrite defX big_map (big_nth 0) big_mkord size_tuple rpred_sum //= => ij.
    have [_ Zsigma] := cycTI_Zisometry ctiWG.
    by rewrite -tnth_nth Dn rpredZsign ?Zsigma ?irr_vchar.
  apply/eqP/(addIr '[X]); rewrite -cfnormBd; last first.
    rewrite /chi Dbeta defGa Y0 addr0 opprD addNKr cfdotNl.
    by rewrite (span_orthogonal oZeta) ?oppr0 // memv_span ?mem_head.
  rewrite addrAC subrr add0r cfnormN Dade_isometry // cfnormBd; last first.
    by rewrite cfdotC (seqInd_ortho_Ind1 _ _ Lphi) ?conjC0.
  rewrite cfnorm_Ind_cfun1 // -/e irrWnorm // addrC; congr (1 + _).
  rewrite defX cfnorm_sum_orthonormal // big_map big_tuple.
  rewrite De (dprod_card xdefW) -card_Iirr_cyclic //; last by have[]:= ctiWG.
  by rewrite -sumr_const; apply: eq_bigr => ij _; rewrite Dn normr_sign expr1n.
have [[Itau1 Ztau1] Dtau1] := cohL.
suffices /cfdot_add_dirr_eq1: '[tau1L phi - tau1L phi^*%CF, chi] = 1.
  rewrite -(cfConjC_Dade_coherent cohL) ?mFT_odd // rpredN dirr_aut.
  by apply; rewrite // dirrE Ztau1 ?Itau1 ?mem_zchar ?irrWnorm /=.
rewrite cfdotBr (span_orthogonal o_tauLeta) ?add0r //; last first.
  by rewrite rpredB ?memv_span ?map_f ?cfAut_seqInd.
have Zdphi := seqInd_sub_aut_zchar nsHL conjC Lphi.
rewrite -raddfB Dtau1 ?zcharD1_seqInd // Dade_isometry ?(zchar_on Zdphi) //. 
rewrite cfdotBr !cfdotBl cfdot_conjCl cfAutInd rmorph1 irrWnorm //.
rewrite (seqInd_ortho_Ind1 _ _ Lphi) // conjC0 subrr add0r opprK.
by rewrite cfdot_conjCl (seqInd_conjC_ortho _ _ _ Lphi) ?mFT_odd ?conjC0 ?subr0.
Qed.

End MoreSTlemmas.

Section NonconjType1.
(* Properties of non-conjugate type I groups, used symmetrically for L and M  *)
(* in the proofs of (14.14) and (14.16).                                      *)

Local Open Scope ring_scope.
Variables (M L : {group gT}) (phi : 'CF(L)) (psi : 'CF(M)).
Variable (tau1L : {additive 'CF(L) -> 'CF(G)}).
Variable (tau1M : {additive 'CF(M) -> 'CF(G)}).
Hypotheses (maxL : L \in 'M) (maxM : M \in 'M).
Let ddL := FT_DadeF_hyp maxL.
Let ddM := FT_DadeF_hyp maxM.
Let tauL := Dade ddL.
Let tauM := Dade ddM.
Let H := L`_\F%G.
Let K := M`_\F%G.
Let calL := seqIndD H L H 1.
Let calM := seqIndD K M K 1.
Let u : algC := #|L : H|%:R.
Let v : algC := #|M : K|%:R.
Let betaL := 'Ind[L, H] 1 - phi.
Let a := '[tauL betaL, tau1M psi].

Hypothesis (cohL : coherent_with calL L^# tauL tau1L).
Hypothesis (cohM : coherent_with calM M^# tauM tau1M).
Hypotheses (Lphi : phi \in calL) (Mpsi : psi \in calM).
Hypotheses (phi1 : phi 1%g = u) (psi1 : psi 1%g = v).
Hypotheses (Ltype1 : FTtype L == 1%N) (Mtype1 : FTtype M == 1%N).
Hypothesis not_MG_L : gval L \notin M :^: G.

Let irrL := FTtype1_Ind_irr maxL Ltype1.
Let irrM := FTtype1_Ind_irr maxM Mtype1.

Lemma disjoint_Dade_FTtype1 : [disjoint Dade_support ddM & Dade_support ddL].
Proof.
by rewrite !FT_DadeF_supportE -!FTsupp1_type1 ?FT_Dade1_support_disjoint.
Qed.
Let TItauML := disjoint_Dade_FTtype1.

Lemma coherent_FTtype1_ortho : orthogonal (map tau1M calM) (map tau1L calL).
Proof.
apply/orthogonalP=> _ _ /mapP[xiM Mxi ->] /mapP[xiL Lxi ->].
have [irrLxi irrMxi] := (irrL Lxi, irrM Mxi).
exact: (disjoint_coherent_ortho (mFT_odd _) _ cohM cohL).
Qed.
Let oML := coherent_FTtype1_ortho.

(* This is the inequality used in both branches of (14.14). *)
Lemma coherent_FTtype1_core_ltr : a != 0 -> #|K|.-1%:R / v <= u - 1.
Proof.
have [nsHL nsKM]: H <| L /\ K <| M by rewrite !gFnormal.
have [irr_phi irr_psi] := (irrL Lphi, irrM Mpsi).
have frobL: [Frobenius L with kernel H] := FTtype1_Frobenius maxL Ltype1.
have [[Itau1 Ztau1] Dtau1] := cohM.
have o1M: orthonormal (map tau1M calM).
  apply: map_orthonormal Itau1 _.
  exact: sub_orthonormal (undup_uniq _) (irr_orthonormal M).
have Lgt1: (1 < size calL)%N by apply: seqInd_nontrivial (mFT_odd _ ) _ _ Lphi.
have [[_ _]] := Dade_Ind1_sub_lin cohL Lgt1 irr_phi Lphi phi1.
rewrite -/tauL -/betaL -/calL => ZbetaL [Gamma [_ _ [b _ Dbeta]]]. 
rewrite odd_Frobenius_index_ler ?mFT_odd // -/u => -[]// [_ ub_Ga] _ nz_a.
have Za: a \in Cint by rewrite Cint_cfdot_vchar // ?Ztau1 ?mem_zchar.
have [X M_X [Del [defGa oXD oDM]]] := orthogonal_split (map tau1M calM) Gamma.
apply: ler_trans ub_Ga; rewrite defGa cfnormDd // ler_paddr ?cfnorm_ge0 //.
suffices ->: '[X] = (a / v) ^+ 2 * (\sum_(xi <- calM) xi 1%g ^+ 2 / '[xi]).
  rewrite sum_seqIndC1_square // -(natrB _ (cardG_gt0 K)) subn1.
  rewrite exprMn !mulrA divfK ?neq0CiG // mulrAC -mulrA.
  by rewrite ler_pemull ?sqr_Cint_ge1 // divr_ge0 ?ler0n.
have [_ -> defX] := orthonormal_span o1M M_X.
have Mgt1: (1 < size calM)%N by apply: seqInd_nontrivial (mFT_odd _ ) _ _ Mpsi.
have [[oM1 _ _] _ _] := Dade_Ind1_sub_lin cohM Mgt1 irr_psi Mpsi psi1.
rewrite exprMn -(Cint_normK Za) -[v]normr_nat -normfV -/v mulr_sumr.
rewrite defX cfnorm_sum_orthonormal // big_map; apply: eq_big_seq => xi Mxi.
have Zxi1 := Cint_seqInd1 Mxi; rewrite -(Cint_normK Zxi1) -(conj_Cint Zxi1).
rewrite irrWnorm ?irrM // divr1 -!exprMn -!normrM; congr (`|_| ^+ 2).
rewrite -mulrA mulrC -mulrA; apply: canRL (mulKf (neq0CiG _ _)) _.
rewrite -(canLR (addrK _) defGa) cfdotBl (orthoPl oDM) ?map_f // subr0.
rewrite -(canLR (addKr _) Dbeta) cfdotDl cfdotNl cfdotC cfdotDr cfdotBr.
rewrite (orthoPr oM1) ?map_f // (orthogonalP oML) ?map_f // subrr add0r.
rewrite cfdotZr cfdot_sumr big1_seq ?mulr0 ?oppr0 => [|nu Mnu]; last first.
  by rewrite cfdotZr (orthogonalP oML) ?map_f ?mulr0.
apply/eqP; rewrite conjC0 oppr0 add0r -subr_eq0 -conjC_nat -!cfdotZr.
rewrite -raddfZnat -raddfZ_Cint // -cfdotBr -raddfB -/v -psi1.
rewrite Dtau1 ?zcharD1_seqInd ?sub_seqInd_zchar //.
rewrite (cfdotElr (Dade_cfunS _ _) (Dade_cfunS _ _)) setIC.
by have:= TItauML; rewrite -setI_eq0 => /eqP->; rewrite big_set0 mulr0.
Qed.

End NonconjType1.

(* This is the context associated with Hypothesis (13.1). *)
Variables S T U V W W1 W2 : {group gT}.
Hypotheses (defW : W1 \x W2 = W) (xdefW : W2 \x W1 = W).
Hypotheses (pairST : typeP_pair S T defW) (maxS : S \in 'M) (maxT : T \in 'M).
Hypotheses (StypeP : of_typeP S U defW) (TtypeP : of_typeP T V xdefW).

Local Notation "` 'W1'" := (gval W1) (at level 0, only parsing) : group_scope.
Local Notation "` 'W2'" := (gval W2) (at level 0, only parsing) : group_scope.
Local Notation "` 'W'" := (gval W) (at level 0, only parsing) : group_scope.
Local Notation What := (cyclicTIset defW).

Local Notation "` 'S'" := (gval S) (at level 0, only parsing) : group_scope.
Local Notation P := `S`_\F%G.
Local Notation "` 'P'" := `S`_\F (at level 0) : group_scope.
Local Notation PU := S^`(1)%G.
Local Notation "` 'PU'" := `S^`(1) (at level 0) : group_scope.
Local Notation "` 'U'" := (gval U) (at level 0, only parsing) : group_scope.

Local Notation "` 'T'" := (gval T) (at level 0, only parsing) : group_scope.
Local Notation Q := `T`_\F%G.
Local Notation "` 'Q'" := `T`_\F (at level 0) : group_scope.
Local Notation QV := T^`(1)%G.
Local Notation "` 'QV'" := `T^`(1) (at level 0) : group_scope.
Local Notation "` 'V'" := (gval V) (at level 0, only parsing) : group_scope.

Let defS : PU ><| W1 = S. Proof. by have [[]] := StypeP. Qed.
Let defPU : P ><| U = PU. Proof. by have [_ []] := StypeP. Qed.

Let defT : QV ><| W2 = T. Proof. by have [[]] := TtypeP. Qed.
Let defQV : Q ><| V = QV. Proof. by have [_ []] := TtypeP. Qed.

Let notStype1 : FTtype S != 1%N. Proof. exact: FTtypeP_neq1 StypeP. Qed.
Let notStype5 : FTtype S != 5%N. Proof. exact: FTtype5_exclusion maxS. Qed.

Let pddS := FT_prDade_hypF maxS StypeP.
Let ptiWS : primeTI_hypothesis S PU defW := FT_primeTI_hyp StypeP.
Let ctiWG : cyclicTI_hypothesis G defW := pddS.

Let pddT := FT_prDade_hypF maxT TtypeP.
Let ptiWT : primeTI_hypothesis T QV xdefW := FT_primeTI_hyp TtypeP.

Let ntW1 : W1 :!=: 1. Proof. by have [[]] := StypeP. Qed.
Let ntW2 : W2 :!=: 1. Proof. by have [_ _ _ []] := StypeP. Qed.
Let cycW1 : cyclic W1. Proof. by have [[]] := StypeP. Qed.
Let cycW2 : cyclic W2. Proof. by have [_ _ _ []] := StypeP. Qed.

Let p := #|W2|.
Let q := #|W1|.
Let u := #|U|.
Let v := #|V|.
Let nU := (p ^ q).-1 %/ p.-1.
Let nV := (q ^ p).-1 %/ q.-1.

Let pr_p : prime p. Proof. by have [] := FTtypeP_primes maxS StypeP. Qed.
Let pr_q : prime q. Proof. by have [] := FTtypeP_primes maxS StypeP. Qed.

Local Open Scope ring_scope.

Let qgt2 : (q > 2)%N. Proof. by rewrite odd_gt2 ?mFT_odd ?cardG_gt1. Qed.
Let pgt2 : (p > 2)%N. Proof. by rewrite odd_gt2 ?mFT_odd ?cardG_gt1. Qed.

Let coPUq : coprime #|PU| q.
Proof. by rewrite (coprime_sdprod_Hall_r defS); have [[]] := StypeP. Qed.

Let nirrW1 : #|Iirr W1| = q. Proof. by rewrite card_Iirr_cyclic. Qed.
Let nirrW2 : #|Iirr W2| = p. Proof. by rewrite card_Iirr_cyclic. Qed.
Let NirrW1 : Nirr W1 = q. Proof. by rewrite -nirrW1 card_ord. Qed.
Let NirrW2 : Nirr W2 = p. Proof. by rewrite -nirrW2 card_ord. Qed.

Let sigma := (cyclicTIiso ctiWG).
Let w_ i j := (cyclicTIirr defW i j).
Local Notation eta_ i j := (sigma (w_ i j)).

Local Notation Imu2 := (primeTI_Iirr ptiWS).
Let mu2_ i j := primeTIirr ptiWS i j.
Let mu_ := primeTIred ptiWS.
Local Notation chi_ j := (primeTIres ptiWS j).

Local Notation Inu2 := (primeTI_Iirr ptiWT).
Let nu2_ i j := primeTIirr ptiWT j i.
Let nu_ := primeTIred ptiWT.

Local Notation tauS := (FT_Dade0 maxS).
Local Notation tauT := (FT_Dade0 maxT).

Let calS0 := seqIndD PU S S`_\s 1.
Let rmR_S := FTtypeP_coh_base maxS StypeP.
Let scohS0 : subcoherent calS0 tauS rmR_S.
Proof. exact: FTtypeP_subcoherent StypeP. Qed.

Let calS := seqIndD PU S P 1.
Let sSS0 : cfConjC_subset calS calS0.
Proof. exact/seqInd_conjC_subset1/Fcore_sub_FTcore. Qed.

Let calT := seqIndD QV T Q 1.

(* This is Hypothesis (14.1). *)
Hypothesis ltqp: (q < p)%N.

(* This corresponds to Peterfalvi, Theorem (14.2). *)
(* As we import the conclusion of BGappendixC, which covers Appendix C of the *)
(* Bender and Glauberman text, we can state this theorem negatively. This     *)
(* will avoid having to repeat its statement thoughout the proof : we will    *)
(* simply end each nested set of assumptions (corresponding to (14.3) and     *)
(* (14.10)) with a contradiction.                                             *)
Theorem no_full_FT_Galois_structure :
 ~ [/\ (*a*) exists Fpq : finFieldImage P W2 U,
               [/\ #|P| = (p ^ q)%N, #|U| = nU & coprime nU p.-1]
    & (*b*) [/\ q.-abelem Q, W2 \subset 'N(Q)
              & exists2 y, y \in Q & W2 :^ y \subset 'N(U)]].
Proof.
case=> [[Fpq [oP oU coUp1]] [abelQ nQW2 nU_W2Q]].
have /idPn[] := ltqp; rewrite -leqNgt.
exact: (prime_dim_normed_finField _ _ _ defPU) nU_W2Q.
Qed.

(* Justification for Hypothesis (14.3). *)
Fact FTtypeP_max_typeII : FTtype S == 2.
Proof. by have [[_ ->]] := FTtypeP_facts maxS StypeP. Qed.
Let Stype2 := FTtypeP_max_typeII.

(* These correspond to Peterfalvi, Hypothesis (14.3). *)
Variables (L : {group gT}) (tau1L : {additive 'CF(L) -> 'CF(G)}) (phi : 'CF(L)).
Local Notation "` 'L'" := (gval L) (at level 0, only parsing).
Local Notation H := `L`_\F%G.
Local Notation "` 'H'" := `L`_\F%g (at level 0, format "` 'H'") : group_scope.

Hypothesis maxNU_L : L \in 'M('N(U)).

(* Consequences of the above. *)
Hypotheses (maxL : L \in 'M) (sNUL : 'N(U) \subset L) (sUH : U \subset H).
Hypotheses (frobL : [Frobenius L with kernel H]) (Ltype1 : FTtype L == 1%N).

Let calL := seqIndD H L H 1.
Local Notation tauL := (FT_DadeF maxL).
Let nsHL : H <| L. Proof. exact: gFnormal. Qed.
Let irrL : {subset calL <= irr L}. Proof. exact: FTtype1_Ind_irr. Qed.

Hypothesis cohL : coherent_with calL L^# tauL tau1L.
Hypotheses (Lphi : phi \in calL) (phi1 : phi 1%g = #|L : H|%:R).

Let betaS := FTtypeP_bridge StypeP #1.
Let betaT := FTtypeP_bridge TtypeP #1.
Let betaL := 'Ind[L, H] 1 - phi.

(* This is the first assertion of Peterfalvi (14.4). *)
Let galT : typeP_Galois TtypeP.
Proof.
apply: contraLR ltqp => /(FTtypeP_nonGalois_facts maxT)[].
by rewrite -/p -leqNgt => ->.
Qed.

(* This is the second assertion of Peterfalvi (14.4). *)
Let oV : v = nV.
Proof.
rewrite /v (card_FTtypeP_Galois_compl maxT galT) -/nV.
by rewrite !modn_small ?gtn_eqF // ltnW.
Qed.

(* This is Peterfalvi (14.5). *)
Let defL : exists2 y, y \in Q & H ><| (W1 <*> W2 :^ y) = L.
Proof.
have [//|_ _ []// defL] := FTtypeII_support_facts maxS StypeP _ pairST maxNU_L.
have [_ _ /negP[]] := compl_of_typeII maxS StypeP Stype2.
have [_ _ _] := FTtypeI_bridge_facts maxS StypeP Ltype1 cohL Lphi phi1.
case=> [[_ ubH] | [_ /idPn[]]]; last by rewrite -(index_sdprod defL) -ltnNge.
have{ubH} /eqP defH: `H == U.
  rewrite eq_sym eqEcard sUH /= -(prednK (cardG_gt0 U)) -add1n -leq_subLR subn1.
  have [_ _ _ _ /divnK <-] := FTtypeP_bridge_facts maxS StypeP.
  by rewrite -leC_nat natrM -ler_pdivr_mulr ?gt0CG // {1}(index_sdprod defL).
rewrite (subset_trans sNUL) // -(sdprodW defL) -(sdprodW defS) mulSg //.
by rewrite -(sdprodW defPU) defH mulG_subr.
Qed.

Let indexLH : #|L : H| = (p * q)%N.
Proof.
have [y Qy /index_sdprod <-] := defL; rewrite (dprod_card xdefW).
suffices /normP <-: y \in 'N(W1) by rewrite -conjYg cardJg (dprodWY defW).
have cQQ: abelian Q by have [_ [/and3P[]]] := FTtypeP_facts _ TtypeP.
by apply: (subsetP (sub_abelian_norm cQQ _)) => //; have [_ _ _ []] := TtypeP.
Qed.

(* This is Peterfalvi (14.6). *)
Let galS : typeP_Galois StypeP.
Proof.
apply/idPn=> gal'S; have [q3 oU] := FTtypeP_nonGalois_facts maxS gal'S.
have [H1 [_ _ _ _]] := typeP_Galois_Pn maxS (FTtype5_exclusion maxS) gal'S.
rewrite def_Ptype_factor_prime // Ptype_Fcompl_kernel_trivial // -/p q3 /=.
set a := #|U : _| => [] [a_gt1 a_dv_p1 _ [U1 isoU1]].
have{isoU1} isoU: U \isog U1 := isog_trans (quotient1_isog U) isoU1.
have{a_gt1 a_dv_p1} defU1: U1 :=: [set: 'rV_2].
  apply/eqP; rewrite eqEcard subsetT -(card_isog isoU) oU.
  rewrite cardsT card_matrix card_ord Zp_cast // leq_sqr -/p.
  apply: dvdn_leq; first by rewrite -(subnKC pgt2).
  rewrite -divn2 -(@Gauss_dvdl a _ 2) ?divnK //.
    by rewrite dvdn2 -subn1 odd_sub ?odd_gt0 ?mFT_odd.
  by rewrite coprimen2 (dvdn_odd (dvdn_indexg U _)) ?mFT_odd.
have [r pr_r r_r_U] := rank_witness U.
have [R0 sylR0] := Sylow_exists r U; have [sR0U rR0 _] := and3P sylR0.
have [R sylR sR0R] := Sylow_superset (subset_trans sR0U sUH) rR0.
have [sRH rR _] := and3P sylR.
have cUU: abelian U by have [[]] := FTtypeP_facts maxS StypeP.
have tiA0: normedTI 'A0(S) G S by have [_ _ _ _ []] := FTtypeP_facts _ StypeP.
have [_ sUPU _ nPU _] := sdprod_context defPU.
have coPU := coprimegS (joing_subl U W1) (Ptype_Fcore_coprime StypeP).
have abR0: abelian R0 := abelianS sR0U cUU.
have{a U1 defU1 isoU r_r_U} rR0_2: 'r(R0) = 2.
  by rewrite (rank_Sylow sylR0) -r_r_U (isog_rank isoU) defU1 rank_mx_group.
have piUr: r \in \pi(U) by rewrite -p_rank_gt0 -(rank_Sylow sylR0) rR0_2.
have /exists_inP[x /setD1P[ntx R0x] ntCPx]: [exists x in R0^#, 'C_P[x] != 1%g].
  have ncycR0: ~~ cyclic R0 by rewrite abelian_rank1_cyclic ?rR0_2.
  have coPR0: coprime #|P| #|R0| := coprimegS sR0U coPU.
  rewrite -negb_forall_in; apply: contra (mmax_Fcore_neq1 maxS) => regR0P.
  rewrite -subG1 -(coprime_abelian_gen_cent1 abR0 _ (subset_trans sR0U nPU)) //.
  by rewrite gen_subG; apply/bigcupsP=> x /(eqfun_inP regR0P)->.
have{x ntx R0x ntCPx} sZR_R0: 'Z(R) \subset R0.
  have A0x: x \in 'A0(S).
    have [z /setIP[Pz cyz] ntz] := trivgPn _ ntCPx. 
    apply/setUP; left; apply/bigcupP; exists z.
      by rewrite !inE ntz (subsetP (Fcore_sub_FTcore maxS)).
    by rewrite (eqP Stype2) 3!inE ntx cent1C (subsetP sUPU) ?(subsetP sR0U).
  have sCxS: 'C[x] \subset S by rewrite -['C[x]]setTI (cent1_normedTI tiA0).
  suffices <-: 'C_R[x] = R0.
    by rewrite -cent_set1 setIS ?centS // sub1set (subsetP sR0R).
  have /Hall_pi hallU: Hall PU U by rewrite -(coprime_sdprod_Hall_r defPU).
  have /Hall_pi hallPU: Hall S PU by rewrite -(coprime_sdprod_Hall_l defS).
  have sylR0_S: r.-Sylow(S) R0.
    by apply: subHall_Sylow piUr sylR0; apply: subHall_Hall (piSg sUPU) hallU.
  rewrite ['C_R[x]](sub_pHall sylR0_S) ?(pgroupS _ rR) ?subsetIl //.
    by rewrite subsetI sR0R sub_cent1 (subsetP abR0).
  by rewrite subIset ?sCxS ?orbT.
pose R1 := 'Ohm_1('Z(R))%G; pose m := logn r #|R1|.
have sR10: R1 \subset R0 by rewrite (subset_trans (Ohm_sub 1 _)).
have oR1: #|R1| = (r ^ m)%N by rewrite -card_pgroup ?(pgroupS sR10).
have{sZR_R0 rR0_2} m12: pred2 1%N 2 m.
  transitivity (0 < m < 1 + 2)%N; first by rewrite -mem_iota !inE.
  rewrite -[m]p_rank_abelian ?center_abelian -?rank_pgroup ?(pgroupS sZR_R0) //.
  rewrite rank_gt0 ltnS -rR0_2 rankS // center_nil_eq1 ?(pgroup_nil rR) //.
  by rewrite (subG1_contra sR0R) // -rank_gt0 rR0_2.
have [y Qy defLy] := defL; have [_ _ /joing_subP[_ nHW2y] _] := sdprodP defLy.
have chR1H: R1 \char H.
  apply: char_trans (char_trans (Ohm_char 1 _) (center_char R)) _.
  by rewrite (nilpotent_Hall_pcore (Fcore_nil L) sylR) gFchar.
have nR1W2y: W2 :^ y \subset 'N(R1) := char_norm_trans chR1H nHW2y.
have regR1W2y: semiregular R1 (W2 :^ y).
  have /Frobenius_reg_ker regHW12y := set_Frobenius_compl defLy frobL.
  exact: semiregularS (char_sub chR1H) (joing_subr _ _) regHW12y.
have /idPn[]: r %| p.-1./2.
  have:= piUr; rewrite mem_primes => /and3P[_ _ /=].
  by rewrite oU Euclid_dvdX ?andbT.
rewrite gtnNdvd //; first by rewrite -(subnKC pgt2).
apply: leq_trans (_ : p.-1 <= r)%N.
  by rewrite -divn2 ltn_divLR // -{1}[p.-1]muln1 -(subnKC pgt2) ltn_pmul2l.
have: p %| (r ^ m).-1.
  by have:= regular_norm_dvd_pred nR1W2y regR1W2y; rewrite cardJg oR1.
rewrite -[p.-1]subn1 leq_subLR  predn_exp Euclid_dvdM // => /orP[]/dvdn_leq.
  by rewrite -(subnKC (prime_gt1 pr_r)) => /implyP/leq_trans->; rewrite 2?ltnW.
move/implyP; case/pred2P: m12 => ->; rewrite !big_ord_recl big_ord0 ?addn0 //=.
by rewrite -(subnKC pgt2).
Qed.

(* This is Peterfalvi (14.7). *)
Let not_charUH : ~~ (U \char H).
Proof.
have [y Qy defLy] := defL; have [_ _ /joing_subP[_ nHW2y] _] := sdprodP defLy.
apply/negP=> chUH; have nUW2y := char_norm_trans chUH nHW2y.
case: no_full_FT_Galois_structure; split; last first.
  split; [by have [_ []] := FTtypeP_facts _ TtypeP | | by exists y].
  by have /sdprodP[_ _ /joing_subP[]] := Ptype_Fcore_sdprod TtypeP.
have <-: #|U| = nU.
  have regUW2y: semiregular U (W2 :^ y).
    have /Frobenius_reg_ker regHW12y := set_Frobenius_compl defLy frobL.
    exact: semiregularS (char_sub chUH) (joing_subr _ _) regHW12y.
  case: ifP (card_FTtypeP_Galois_compl maxS galS) => //.
  rewrite -/p -/q -/nU => p_modq_1 oU.
  have{p_modq_1 oU} oU: (#|U| * q)%N = nU.
    by rewrite oU divnK //; have [|_ ->] := FTtypeP_primes_mod_cases _ StypeP.
  have /eqP Umodp: #|U| == 1 %[mod p].
    have:= regular_norm_dvd_pred nUW2y regUW2y.
    by rewrite cardJg -/p -subn1 eqn_mod_dvd.
  have: nU == 1 %[mod p].
    rewrite /nU predn_exp mulKn; last by rewrite -(subnKC pgt2).
    rewrite -(ltn_predK qgt2) big_ord_recl addnC -modnDml -modn_summ modnDml.
    by rewrite big1 // => i _; rewrite expnS modnMr.
  by rewrite -oU -modnMml Umodp modnMml mul1n !modn_small ?gtn_eqF ?prime_gt1.
have [F []] := typeP_Galois_P maxS (FTtype5_exclusion maxS) galS.
rewrite Ptype_factor_prime ?(group_inj (Ptype_Fcore_kernel_trivial _ _)) //.
rewrite Ptype_Fcompl_kernel_trivial // => psiP [psiU _ [/trivgP inj_psiU psiJ]].
rewrite /= -injm_subcent ?coset1_injm ?norms1 // -morphim_comp -/p.
rewrite (typeP_cent_core_compl StypeP) => [[_ /isomP[inj_psiP im_psiP] psiW2]].
rewrite -(card_isog (quotient1_isog U)) => [[_ coUp1 _]].
suffices FPU: finFieldImage P W2 U.
  by exists FPU; have [_ []] := FTtypeP_facts maxS StypeP.
have /domP[sig [Dsig Ksig _ im_sig]]: 'dom (psiP \o coset 1) = P.
  by apply: injmK; rewrite ?coset1_injm ?norms1.
have{Ksig} inj_sig: 'injm sig by rewrite Ksig injm_comp ?coset1_injm.
exists F sig; first by apply/isomP; rewrite im_sig morphim_comp.
  by rewrite -psiW2 -im_sig injmK // -(typeP_cent_core_compl StypeP) subsetIl.
exists psiU => // z x Pz Ux /=; have inN1 x1: x1 \in 'N(1) by rewrite norm1 inE.
by rewrite !Dsig -psiJ ?mem_morphim //= qactE ?dom_qactJ.
Qed.

(* This is Peterfalvi (14.8)(a). *)
(* In order to avoid the use of real analysis and logarithms we bound the     *)
(* binomial expansion of n.+1 ^ q.+1 directly.                                *)
Let qp1_gt_pq1 : (q ^ p.+1 > p ^ q.+1)%N.
Proof.
have: (4 < p)%N by rewrite odd_geq ?mFT_odd ?(leq_trans _ ltqp).
elim: p ltqp => // n IHn; rewrite !ltnS => ngeq.
rewrite leq_eqVlt => /predU1P[/esym n4 | ngt4].
  suffices /eqP <-: 3 == q by rewrite n4.
  by rewrite eqn_leq qgt2 -ltnS -(odd_ltn 5) ?mFT_odd // -n4.
apply: leq_trans (_ : q * n ^ q.+1 <= _)%N; last first.
  rewrite (expnS q) leq_mul //.
  by move: ngeq; rewrite leq_eqVlt => /predU1P[-> | /IHn/(_ ngt4)/ltnW].
apply: leq_trans (_ : (2 * q.+1 + n) * n ^ q <= _)%N; last first.
  rewrite expnS mulnA leq_mul // addnC.
  move: ngeq; rewrite leq_eqVlt => /predU1P[-> | n_gtq].
    apply: leq_trans (_ : 4 * n <= _)%N; last by rewrite leq_mul // ltnW.
    by rewrite mulnSr addnA -mulSn (mulSnr 3) leq_add2l 3?ltnW.
  by rewrite -{2}(subnKC qgt2) addSn (mulSn _ n) leq_add2l leq_mul.
rewrite mulnDl -expnS -[n.+1]add1n expnDn big_ord_recr binn subnn !mul1n /=.
rewrite ltn_add2r -(@ltn_pmul2l (2 ^ q)) ?expn_gt0 // !mulnA -expnSr.
apply: leq_ltn_trans (_ : (2 ^ q.+1).-1 * q.+1 * n ^ q < _)%N; last first.
  by rewrite -(subnKC ngt4) !ltn_pmul2r ?prednK ?expn_gt0.
rewrite -mulnA predn_exp mul1n big_distrr big_distrl leq_sum // => [[i]] /=.
rewrite ltnS exp1n mul1n => leiq _; rewrite -{1 4}(subnKC leiq) !expnD.
rewrite -mulnA leq_mul // mulnA mulnCA mulnC leq_mul // -bin_sub ?leqW //.
rewrite -(leq_pmul2r (fact_gt0 (q.+1 - i))) -mulnA bin_ffact mulnC subSn //.
rewrite ffactnS /= -!mulnA leq_mul //=; elim: {i leiq}(q - i)%N => //= i IHi.
rewrite ffactnSr expnSr mulnACA expnS factS (mulnACA n) mulnC leq_mul //.
by rewrite leq_mul // (leq_trans (leq_subr _ _)).
Qed.

(* This is Peterfalvi (14.8)(b). *)
Let v1p_gt_u1q : (v.-1 %/ p > u.-1 %/ q)%N.
Proof.
have ub_u: (u.-1 <= nU - 1)%N.
  rewrite -subn1 leq_sub2r //; have [_ _] := FTtypeP_facts maxS StypeP.
  by rewrite (FTtypeP_reg_Fcore maxS StypeP) indexg1.
rewrite ltn_divLR ?prime_gt0 // {ub_u}(leq_ltn_trans ub_u) //.
have p_dv_v1: p %| v.-1 by have [] := FTtypeP_bridge_facts maxT TtypeP.
rewrite divn_mulAC // ltn_divRL ?dvdn_mulr // oV -subn1.
rewrite -(@ltn_pmul2l q.-1) ?(mulnCA q.-1); last by rewrite -(subnKC qgt2).
rewrite !mulnA -(@ltn_pmul2l p.-1); last by rewrite -(subnKC pgt2).
rewrite -mulnA mulnCA mulnA !(mulnBl _ _ _.-1) !divnK ?dvdn_pred_predX //.
rewrite !mul1n mulnCA -!subn1 ltn_mul ?ltn_sub2r ?prime_gt1 //.
rewrite -!subnDA !subnKC ?prime_gt0 // !mulnBl -!expnSr !mulnn.
by rewrite -subSn ?leq_exp2l ?leqW ?prime_gt1 ?leq_sub ?leq_exp2r // ltnW.
Qed.

Let calT0 := seqIndD QV T T`_\s 1.
Let rmR_T := FTtypeP_coh_base maxT TtypeP.
Let scohT0 : subcoherent calT0 tauT rmR_T.
Proof. exact: FTtypeP_subcoherent. Qed.

Let sTT0 : cfConjC_subset calS calS0.
Proof. exact/seqInd_conjC_subset1/Fcore_sub_FTcore. Qed.

(* This is Peterfalvi (14.9). *)
Lemma FTtypeP_min_typeII : FTtype T == 2.
Proof.
apply: contraLR v1p_gt_u1q => notTtype2; rewrite -leqNgt -leC_nat.
have [o_betaT0_eta _ [Ttype3 _]] := FTtype34_structure maxT TtypeP notTtype2.
have Ttype_gt2: (2 < FTtype T)%N by rewrite (eqP Ttype3).
have [[_ _ frobVW2 cVV] _ _ _ _] := FTtypeP_facts _ TtypeP.
pose calT1 := seqIndD QV T QV Q; have sT10: cfConjC_subset calT1 calT0.
  by apply/seqInd_conjC_subset1; rewrite /= FTcore_eq_der1.
rewrite (FTtypeP_reg_Fcore maxT TtypeP) (group_inj (joingG1 _)) in o_betaT0_eta.
do [rewrite -/calT1; set eta_0 := \sum_j _] in o_betaT0_eta.
have scohT1: subcoherent calT1 tauT rmR_T := subset_subcoherent scohT0 sT10.
have [nsQQV sVQV _ _ _] := sdprod_context defQV.
have nsQVT: QV <| T := der_normal 1 T.
have calT1_1p zeta: zeta \in calT1 -> zeta 1%g = p%:R.
  case/seqIndP=> s /setDP[kerQs _] -> /=; rewrite inE in kerQs.
  rewrite cfInd1 ?gFsub // -(index_sdprod defT) lin_char1 ?mulr1 //.
  rewrite lin_irr_der1 (subset_trans _ kerQs) // der1_min ?normal_norm //.
  by rewrite -(isog_abelian (sdprod_isog defQV)).
have [tau1T cohT1]: coherent calT1 T^# tauT.
  apply/(uniform_degree_coherence scohT1)/(@all_pred1_constant _ p%:R).
  by apply/allP=> _ /mapP[zeta T1zeta ->]; rewrite /= calT1_1p.
have irrT1: {subset calT1 <= irr T}.
  move=> _ /seqIndP[s /setDP[kerQs nz_s] ->]; rewrite inE in kerQs.
  rewrite inE subGcfker in nz_s; rewrite -(quo_IirrK nsQQV kerQs) mod_IirrE //.
  rewrite cfIndMod ?normal_sub ?cfMod_irr ?gFnormal //.
  rewrite irr_induced_Frobenius_ker ?quo_Iirr_eq0 //=.
  have /sdprod_isom[nQ_VW1 /isomP[injQ <-]] := Ptype_Fcore_sdprod TtypeP.
  have ->: (QV / Q)%g = (V / Q)%g by rewrite -(sdprodW defQV) quotientMidl.
  have ->: (V / Q)%g = restrm nQ_VW1 (coset Q) @* V.
    by rewrite morphim_restrm (setIidPr _) // joing_subl.
  by rewrite injm_Frobenius_ker // (FrobeniusWker frobVW2).
have [[A0betaS PVbetaS] _ [_]] := FTtypeP_bridge_facts maxS StypeP.
rewrite -/q -/u; set Gamma := FTtypeP_bridge_gap _ _ => oGa1 R_Ga lb_Ga _.
have oT1eta: orthogonal (map tau1T calT1) (map sigma (irr W)).
  apply/orthogonalP=> _ _ /mapP[zeta T1zeta ->] /mapP[omega Womega ->].
  have{omega Womega} [i [j ->]] := cycTIirrP defW Womega.
  by rewrite (cycTIisoC _ pddT) (coherent_ortho_cycTIiso _ sT10 cohT1) ?irrT1.
have [[Itau1T Ztau1T] Dtau1T] := cohT1.
have nzT1_Ga zeta: zeta \in calT1 -> `|'[Gamma, tau1T zeta]| ^+ 2 >= 1.
  have Z_Ga: Gamma \in 'Z[irr G].
    rewrite rpredD ?cycTIiso_vchar // rpredB ?rpred1 ?Dade_vchar // zchar_split.
    by rewrite A0betaS ?Iirr1_neq0 // rpredB ?cfInd_vchar ?rpred1 ?irr_vchar.
  move=> T1zeta; rewrite expr_ge1 ?normr_ge0 // norm_Cint_ge1 //.
    by rewrite Cint_cfdot_vchar ?Ztau1T ?(mem_zchar T1zeta).
  suffices: ('[Gamma, tau1T zeta] == 1 %[mod 2])%C.
    by apply: contraTneq => ->; rewrite (eqCmod_nat 2 0 1).
  pose betaT0 := nu_ 0 - zeta.
  have{o_betaT0_eta} o_eta0_betaT0 j: '[eta_ 0 j, tauT betaT0] = (j == 0)%:R.
    transitivity '[eta_ 0 j, eta_0]; rewrite (cycTIisoC _ pddT).
      apply/eqP; rewrite -subr_eq0 -cfdotBr cfdotC.
      by rewrite (orthoPl (o_betaT0_eta _ _)) ?conjC0 // map_f ?mem_irr.
    rewrite cfdot_sumr (bigD1 0) //= cfdot_cycTIiso andbT big1 ?addr0 //.
    by move=> i /negPf nz_i; rewrite cfdot_cycTIiso andbC eq_sym nz_i.
  have QVbetaT0: betaT0 \in 'CF(T, QV^#).
    rewrite cfun_onD1 rpredB ?(seqInd_on _ T1zeta) //=; last first.
      by rewrite /nu_ -cfInd_prTIres cfInd_normal.
    by rewrite !cfunE prTIred_1 prTIirr0_1 mulr1 calT1_1p ?subrr.
  have A0betaT0: betaT0 \in 'CF(T, 'A0(T)).
    by rewrite (cfun_onS (FTsupp1_sub0 _)) // /'A1(T) ?FTcore_eq_der1.
  have ZbetaT0: betaT0 \in 'Z[irr T].
    by rewrite rpredB ?char_vchar ?(seqInd_char T1zeta) ?prTIred_char.      
  pose Delta := tauT betaT0 - 1 + tau1T zeta.
  have nz_i1: #1 != 0 := Iirr1_neq0 ntW2.
  rewrite -(canLR (addKr _) (erefl Delta)) opprB cfdotDr cfdotBr oGa1 add0r.
  rewrite cfdotDl cfdotBl -/betaS o_eta0_betaT0 (negPf nz_i1) // addr0 opprB.
  rewrite -(cycTIiso1 pddS) -(cycTIirr00 defW) {}o_eta0_betaT0 mulr1n.
  have QV'betaS: tauS betaS \in 'CF(G, ~: class_support QV^# G).
    have [_ [pP _] _ _ [_ ->]] := FTtypeP_facts _ StypeP; rewrite ?A0betaS //.
    apply: cfun_onS (cfInd_on (subsetT S) (PVbetaS _ nz_i1)).
    apply/subsetP=> x PWx; rewrite inE.
    have{PWx}: p \in \pi(#[x]).
      case/imset2P: PWx => {x}x y PWx _ ->; rewrite {y}orderJ.
      case/setUP: PWx => [/setD1P[ntx Px] | /imset2P[{x}x y Wx _ ->]].
        rewrite -p_rank_gt0 -rank_pgroup ?rank_gt0 ?cycle_eq1 //.
        exact: mem_p_elt (abelem_pgroup pP) Px.
      case/setDP: Wx; rewrite {y}orderJ; have [_ <- cW12 _] := dprodP defW.
      case/mulsgP=> {x}x y W1x W2y ->; have cyx := centsP cW12 _ W2y _ W1x.
      have [-> | nty _] := eqVneq y 1%g; first by rewrite inE mulg1 W1x.
      have p'x: p^'.-elt x.
        by rewrite (mem_p_elt _ W1x) /pgroup ?pnatE ?inE ?ltn_eqF.
      have p_y: p.-elt y by rewrite (mem_p_elt (pnat_id _)).
      rewrite -cyx orderM ?(pnat_coprime p_y) // pi_ofM // inE /=.
      by rewrite -p_rank_gt0 -rank_pgroup // rank_gt0 cycle_eq1 nty.
    apply: contraL => /imset2P[z y /setD1P[_ QVz] _ ->]; rewrite {x y}orderJ.
    rewrite -p'natEpi // [_.-nat _](mem_p_elt _ QVz) // /pgroup ?p'natE //.
    rewrite -prime_coprime // coprime_sym (coprime_sdprod_Hall_r defT).
    by have [[]] := TtypeP.
  have [_ _ _ _ [_ -> //]] := FTtypeP_facts _ TtypeP.
  rewrite (cfdotElr QV'betaS (cfInd_on _ QVbetaT0)) ?subsetT //=.
  rewrite setIC setICr big_set0 mulr0 subr0 addrC /eqCmod addrK.
  rewrite cfdot_real_vchar_even ?mFT_odd ?oGa1 ?rpred0 //; split.
    rewrite rpredD ?Ztau1T ?(mem_zchar T1zeta) // rpredB ?rpred1 //.
    by rewrite Dade_vchar // zchar_split ZbetaT0.
  rewrite /cfReal -subr_eq0 opprD opprB rmorphD rmorphB rmorph1 /= addrACA.
  rewrite !addrA subrK -Dade_aut -linearB /= -/tauT rmorphB opprB /=.
  rewrite -prTIred_aut aut_Iirr0 -/nu_ [sum in tauT sum]addrC addrA subrK.
  rewrite -Dtau1T; last first.
    by rewrite (zchar_onS _ (seqInd_sub_aut_zchar _ _ _)) // setSD ?der_sub.
  rewrite raddfB -addrA addrC addrA subrK subr_eq0.
  by rewrite (cfConjC_Dade_coherent cohT1) ?mFT_odd ?irrT1.
have [Y T1_Y [X [defGa oYX oXT1]]] := orthogonal_split (map tau1T calT1) Gamma.
apply: ler_trans (lb_Ga X Y _ _ _); first 1 last; rewrite 1?addrC //.
- by rewrite cfdotC oYX conjC0.
- by apply/orthoPl=> eta Weta; rewrite (span_orthogonal oT1eta) // memv_span.
have ->: v.-1 = (p * size calT1)%N; last rewrite mulKn ?prime_gt0 //.
  rewrite [p](index_sdprod defT); have isoV := sdprod_isog defQV.
  rewrite [v](card_isog isoV) -card_Iirr_abelian -?(isog_abelian isoV) //.
  rewrite -(card_imset _ (can_inj (mod_IirrK nsQQV))) (cardD1 0) /=.
  rewrite -{1}(mod_Iirr0 QV Q) mem_imset //=.
  rewrite (size_irr_subseq_seqInd _ (subseq_refl _)) //=.
  apply: eq_card => s; rewrite !inE mem_seqInd ?gFnormal // !inE subGcfker.
  congr (_ && _); apply/idP/idP=> [/imsetP[r _ ->] | kerQs].
    by rewrite mod_IirrE ?cfker_mod.
  by rewrite -(quo_IirrK nsQQV kerQs) mem_imset.
have o1T1: orthonormal (map tau1T calT1).
  rewrite map_orthonormal ?(sub_orthonormal irrT1) ?seqInd_uniq //.
  exact: irr_orthonormal.
have [_ -> ->] := orthonormal_span o1T1 T1_Y.
rewrite cfnorm_sum_orthonormal // big_map -sum1_size natr_sum !big_seq.
apply: ler_sum => // zeta T1zeta; rewrite -(canLR (addrK X) defGa).
by rewrite cfdotBl (orthoPl oXT1) ?subr0 ?nzT1_Ga ?map_f.
Qed.
Let Ttype2 := FTtypeP_min_typeII.

(* These declarations correspond to Hypothesis (14.10). *)
Variables (M : {group gT}) (tau1M : {additive 'CF(M) -> 'CF(G)}) (psi : 'CF(M)).
Hypothesis maxNV_M : M \in 'M('N(V)).

Local Notation "` 'M'" := (gval M) (at level 0, only parsing).
Local Notation K := `M`_\F%G.
Local Notation "` 'K'" := `M`_\F%g (at level 0, format "` 'K'") : group_scope.

(* Consequences of the above. *)
Hypotheses (maxM : M \in 'M) (sNVM : 'N(V) \subset M).
Hypotheses (frobM : [Frobenius M with kernel K]) (Mtype1 : FTtype M == 1%N).

Let calM := seqIndD K M K 1.
Local Notation tauM := (FT_DadeF maxM).
Let nsKM : K <| M. Proof. exact: gFnormal. Qed.
Let irrM : {subset calM <= irr M}. Proof. exact: FTtype1_Ind_irr. Qed.

Hypothesis cohM : coherent_with calM M^# tauM tau1M.
Hypotheses (Mpsi : psi \in calM) (psi1 : psi 1%g = #|M : K|%:R).

Let betaM := 'Ind[M, K] 1 - psi.

Let pairTS : typeP_pair T S xdefW. Proof. exact: typeP_pair_sym pairST. Qed.

Let pq : algC := (p * q)%:R.
Let h := #|H|.

(* This is the first (and main) part of Peterfalvi (14.11). *)
Let defK : `K = V.
Proof.
pose e := #|M : K|; pose k := #|K|; apply: contraTeq isT => notKV.
have [_ sVK defM] := FTtypeII_support_facts maxT TtypeP Ttype2 pairTS maxNV_M.
have ltVK: V \proper K by rewrite properEneq eq_sym notKV.
have e_dv_k1: e %| k.-1 := Frobenius_ker_dvd_ker1 frobM.
have [e_lepq regKW2]: (e <= p * q)%N /\ semiregular K W2.
  case: defM => [|[y Py]] defM; rewrite /e -(index_sdprod defM).
    have /Frobenius_reg_ker regHW1 := set_Frobenius_compl defM frobM.
    by rewrite leq_pmulr ?cardG_gt0.
  have /Frobenius_reg_ker regHW21y := set_Frobenius_compl defM frobM.
  split; last exact: semiregularS (joing_subl _ _) regHW21y.
  suffices /normP <-: y \in 'N(W2).
    by rewrite -conjYg cardJg (dprodWY xdefW) -(dprod_card xdefW).
  have cPP: abelian P by have [_ [/and3P[]]] := FTtypeP_facts maxS StypeP.
  have sW2P: W2 \subset P by have [_ _ _ []] := StypeP.
  by rewrite (subsetP _ y Py) // sub_abelian_norm.
(* This is (14.11.1). *)
have{regKW2} [lb_k lb_k1e_v]: (2 * p * v < k /\ v.-1 %/ p < k.-1 %/ e)%N.
  have /dvdnP[x Dk]: v %| k := cardSg sVK.
  have lb_x: (p.*2 < x)%N.
    have x_gt1: (1 < x)%N.
      by rewrite -(ltn_pmul2r (cardG_gt0 V)) -Dk mul1n proper_card.
    have x_gt0 := ltnW x_gt1; rewrite -(prednK x_gt0) ltnS -subn1.
    rewrite dvdn_leq ?subn_gt0 // -mul2n Gauss_dvd ?coprime2n ?mFT_odd //.
    rewrite dvdn2 odd_sub // (dvdn_odd _ (mFT_odd K)) -/k ?Dk ?dvdn_mulr //=.
    rewrite -eqn_mod_dvd // -[x]muln1 -modnMmr.
    have nVW2: W2 \subset 'N(V) by have [_ []] := TtypeP.
    have /eqP{1} <-: (v == 1 %[mod p]).
      rewrite eqn_mod_dvd ?cardG_gt0 // subn1 regular_norm_dvd_pred //.
      exact: semiregularS regKW2.
    rewrite modnMmr -Dk /k eqn_mod_dvd // subn1 regular_norm_dvd_pred //.
    by rewrite (subset_trans (subset_trans nVW2 sNVM)) ?gFnorm.
  have lb_k: (2 * p * v < k)%N by rewrite mul2n Dk ltn_pmul2r ?cardG_gt0.
  split=> //; rewrite ltn_divLR ?cardG_gt0 // divn_mulAC ?prednK ?cardG_gt0 //.
  rewrite leq_divRL ?indexg_gt0 // (leq_trans (leq_mul (leqnn v) e_lepq)) //.
  rewrite mulnA mulnAC leq_mul // -ltnS prednK ?cardG_gt0 //.
  apply: leq_ltn_trans lb_k; rewrite mulnC leq_mul // ltnW ?(leq_trans ltqp) //.
  by rewrite mul2n -addnn leq_addl.
have lb_k1e_u := ltn_trans v1p_gt_u1q lb_k1e_v; have irr_psi := irrM Mpsi.
have Mgt1: (1 < size calM)%N by apply: seqInd_nontrivial Mpsi; rewrite ?mFT_odd.
(* This is (14.11.2). *)
have [] // := FTtype2_support_coherence TtypeP StypeP cohM Mpsi.
rewrite -/e -/p -/q mulnC /= => De [nb [chi Dchi]].
rewrite cycTIiso_irrelC -/sigma -/betaM => DbetaM.
pose ddMK := FT_DadeF_hyp maxM; pose AM := Dade_support ddMK.
have defAM: AM = 'A~(M) by rewrite FTsupp_Frobenius -?FT_DadeF_supportE.
pose ccG A := class_support A G.
pose G0 := ~: ('A~(M) :|: ccG What :|: ccG P^# :|: ccG Q^#).
have sW2P: W2 \subset P by have [_ _ _ []] := StypeP.
have sW1Q: W1 \subset Q by have [_ _ _ []] := TtypeP.
(* This is (14.11.3). *)
have lbG0 g: g \in G0 -> 1 <= `|tau1M psi g| ^+ 2.
  rewrite !inE ?expr_ge1 ?normr_ge0 // => /norP[/norP[/norP[AM'g W'g P'g Q'g]]].
  have{W'g} /coprime_typeP_Galois_core-co_p_g: g \notin ccG W^#.
    apply: contra W'g => /imset2P[x y /setD1P[ntx Wx] Gy Dg].
    rewrite Dg mem_imset2 // !inE Wx andbT; apply/norP; split.
      by apply: contra Q'g => /(subsetP sW1Q)?; rewrite Dg mem_imset2 ?inE ?ntx.
    by apply: contra P'g => /(subsetP sW2P)Px; rewrite Dg mem_imset2 ?inE ?ntx.
  have{AM'g} betaMg0: tauM betaM g = 0.
    by apply: cfun_on0 AM'g; rewrite -defAM Dade_cfunS.
  suffices{betaMg0}: 1 <= `|(\sum_ij (-1) ^+ nb ij *: sigma 'chi_ij) g|.
    rewrite -[\sum_i _](subrK chi) -DbetaM !cfunE betaMg0 add0r.
    case: Dchi => -> //; rewrite cfunE normrN.
    by rewrite -(cfConjC_Dade_coherent cohM) ?mFT_odd ?cfunE ?norm_conjC.
  have{co_p_g} Zeta_g ij: sigma 'chi_ij g \in Cint.
    apply/Cint_cycTIiso_coprime/(coprime_dvdr (cforder_lin_char_dvdG _)).
      by apply: irr_cyclic_lin; have [] := ctiWG.
    rewrite -(dprod_card defW) coprime_mulr.
    by apply/andP; split; [apply: co_p_g galT _ | apply: co_p_g galS _].
  rewrite sum_cfunE norm_Cint_ge1 ?rpred_sum // => [ij _|].
    by rewrite cfunE rpredMsign.
  set a := \sum_i _; suffices: (a == 1 %[mod 2])%C.
    by apply: contraTneq=> ->; rewrite (eqCmod_nat 2 0 1).
  have signCmod2 n ij (b := sigma 'chi_ij g): ((-1) ^+ n * b == b %[mod 2])%C.
    rewrite -signr_odd mulr_sign eqCmod_sym; case: ifP => // _.
    by rewrite -(eqCmodDl _ b) subrr -[b + b](mulr_natr b 2) eqCmodMl0 /b.
  rewrite -[1]addr0 [a](bigD1 0) {a}//= cfunE eqCmodD //.
    by rewrite (eqCmod_trans (signCmod2 _ _)) // irr0 cycTIiso1 cfun1E inE.
  rewrite (partition_big_imset (fun ij => [set ij; conjC_Iirr ij])) /= eqCmod0.
  apply: rpred_sum => _ /=/imsetP[ij /negPf nz_ij ->].
  rewrite (bigD1 ij) /=; last by rewrite unfold_in nz_ij eqxx.
  rewrite (big_pred1 (conjC_Iirr ij)) => [|ij1 /=]; last first.
    rewrite unfold_in eqEsubset !subUset !sub1set !inE !(eq_sym ij).
    rewrite !(can_eq (@conjC_IirrK _ _)) (canF_eq (@conjC_IirrK _ _)).
    rewrite -!(eq_sym ij1) -!(orbC (_ == ij)) !andbb andbAC -andbA.
    rewrite andb_orr andNb andbA andb_idl // => /eqP-> {ij1}.
    rewrite conjC_Iirr_eq0 nz_ij -(inj_eq irr_inj) conjC_IirrE.
    by rewrite odd_eq_conj_irr1 ?mFT_odd // irr_eq1 nz_ij.
  rewrite -signr_odd -[odd _]negbK signrN !cfunE mulNr addrC.
  apply: eqCmod_trans (signCmod2 _ _) _.
  by rewrite eqCmod_sym conjC_IirrE -cfAut_cycTIiso cfunE conj_Cint.
have cardG_D1 R: #|R^#| = #|R|.-1 by rewrite [#|R|](cardsD1 1%g) group1.
pose rho := invDade ddMK; pose nG : algC := #|G|%:R.
pose sumG0 := \sum_(g in G0) `|tau1M psi g| ^+ 2.
pose sumG0_diff := sumG0 - (#|G0| + #|ccG What| + #|ccG P^#| + #|ccG Q^#|)%:R.
have ub_rho: '[rho (tau1M psi)] <= k.-1%:R / #|M|%:R - nG^-1 * sumG0_diff.
  have NtauMpsi: '[tau1M psi] = 1.
    by have [[Itau1 _] _] := cohM; rewrite Itau1 ?mem_zchar //= irrWnorm.
  rewrite ler_subr_addl -subr_le0 -addrA.
  have ddM_ i j: i != j :> 'I_1 -> [disjoint AM & AM] by rewrite !ord1.
  apply: ler_trans (Dade_cover_inequality ddM_ NtauMpsi); rewrite -/nG -/AM.
  rewrite !big_ord1 cardG_D1 ler_add2r ler_pmul2l ?invr_gt0 ?gt0CG //= defAM.
  rewrite setTD ler_add ?ler_opp2 ?leC_nat //; last first.
    do 3!rewrite -?addnA -cardsUI ?addnA (leq_trans _ (leq_addr _ _)) //.
    by rewrite subset_leq_card // -setCD setCS -!setUA subDset setUC.
  rewrite (big_setID G0) /= (setIidPr _) ?setCS -?setUA ?subsetUl // ler_addl.
  by apply: sumr_ge0 => g _; rewrite ?exprn_ge0 ?normr_ge0.
have lb_rho: 1 - pq / k%:R <= '[rho (tau1M psi)].
  have [_] := Dade_Ind1_sub_lin cohM Mgt1 irr_psi Mpsi psi1; rewrite -/e -/k.
  rewrite odd_Frobenius_index_ler ?mFT_odd // => -[_ _ [|/(ler_trans _)->] //].
  by rewrite ler_add2l ler_opp2 ler_pmul2r ?invr_gt0 ?gt0CG // leC_nat.
have{rho sumG0 sumG0_diff ub_rho lb_rho} []:
  ~ pq / k%:R + 2%:R / pq + (u * q)%:R^-1 + (v * p)%:R^-1 < p%:R^-1 + q%:R^-1.
- rewrite ler_gtF // -!addrA -ler_subl_addl -ler_subr_addl -(ler_add2l 1).
  apply: ler_trans {ub_rho lb_rho}(ler_trans lb_rho ub_rho) _.
  rewrite /sumG0_diff -!addnA natrD opprD addrA mulrBr opprB addrA.
  rewrite ler_subl_addr ler_paddr //.
    by rewrite mulr_ge0 ?invr_ge0 ?ler0n // subr_ge0 -sumr_const ler_sum.
  rewrite mulrDl -!addrA addrCA [1 + _]addrA [_ + (_ - _)]addrA ler_add //.
    rewrite -(Lagrange (normal_sub nsKM)) natrM invfM mulrA -/k -/e /pq -De.
    rewrite ler_pmul2r ?invr_gt0 ?gt0CiG // ler_pdivr_mulr ?gt0CG //.
    by rewrite mul1r leC_nat leq_pred.
  rewrite [1 + _ + _]addrA addrAC !natrD !mulrDr !ler_add //; first 1 last.
  + exact: (FTtype2_cc_core_ler StypeP).
  + exact: (FTtype2_cc_core_ler TtypeP).
  have [_ _ /card_support_normedTI->] := ctiWG.
  rewrite natrM natf_indexg ?subsetT // mulrCA mulKf ?neq0CG // card_cycTIset.
  rewrite mulnC -(dprod_card xdefW) /pq !natrM -!subn1 !natrB // -/p -/q invfM.
  rewrite mulrACA !mulrBl ?divff ?neq0CG // !mul1r mulrBr mulr1 opprB.
  by rewrite addrACA -opprB opprK.
rewrite -!addrA ler_lt_add //; last first.
  pose q2 : algC := (q ^ 2)%:R.
  apply: ltr_le_trans (_ : 2%:R / q2 + (2%:R * q2)^-1 *+ 2 <= _); last first.
    rewrite addrC -[_ *+ 2]mulr_natl invfM mulVKf ?pnatr_eq0 //.
    rewrite mulr_natl -mulrS -mulr_natl [q2]natrM.
    by rewrite ler_pdivr_mulr ?mulr_gt0 ?gt0CG // mulKf ?neq0CG ?leC_nat.
  rewrite -natrM !addrA ltr_add ?(FTtypeP_complV_ltr TtypeP) 1?ltnW //.
  rewrite ltr_add ?(FTtypeP_complV_ltr StypeP) // /pq mulnC /q2 !natrM !invfM.
  by rewrite !ltr_pmul2l ?ltf_pinv ?invr_gt0 ?qualifE ?gt0CG ?ltr0n ?ltr_nat.
rewrite ler_pdivr_mulr ?ler_pdivl_mull ?gt0CG // -natrM leC_nat.
apply: leq_trans lb_k; rewrite leqW // mulnAC mulnC leq_mul //.
have [[_ _ frobVW2 _] _ _ _ _] := FTtypeP_facts maxT TtypeP.
rewrite -[(p * q)%N]mul1n leq_mul // (leq_trans _ (leq_pred v)) // dvdn_leq //.
  by rewrite -subn1 subn_gt0 cardG_gt1; have[] := Frobenius_context frobVW2.
rewrite Gauss_dvd ?prime_coprime ?(dvdn_prime2 pr_p pr_q) ?gtn_eqF //.
rewrite (Frobenius_dvd_ker1 frobVW2) /= oV /nV predn_exp.
rewrite -(subnKC qgt2) -(ltn_predK pgt2) mulKn // subnKC //.
by rewrite big_ord_recl dvdn_sum // => i _; rewrite expnS dvdn_mulr.
Qed.

(* This is the first part of Peterfalvi (14.11). *)
Let indexMK : #|M : K| = (p * q)%N.
Proof.
have [_ _ [defM|]] := FTtypeII_support_facts maxT TtypeP Ttype2 pairTS maxNV_M.
  have:= Ttype2; rewrite (mmax_max maxM (mmax_proper maxT)) ?(eqP Mtype1) //.
  rewrite -(sdprodW (Ptype_Fcore_sdprod TtypeP)) -defK (sdprodWY defM).
  exact: mulG_subr.
case=> y Py /index_sdprod <-; rewrite (dprod_card xdefW) -(dprodWY xdefW).
suffices /normP {1}<-: y \in 'N(W2) by rewrite -conjYg cardJg.
have cPP: abelian P by have [_ [/and3P[]]] := FTtypeP_facts maxS StypeP.
by rewrite (subsetP (sub_abelian_norm cPP _)) //; have [_ _ _ []] := StypeP.
Qed.

(* This is Peterfalvi (14.12), and also (14.13) since we have already proved  *)
(* the negation of Theorem (14.2).                                            *)
Let not_MG_L : (L : {set gT}) \notin M :^: G.
Proof.
rewrite orbit_sym; apply: contra not_charUH => /imsetP[z _ /= defLz].
rewrite sub_cyclic_char // -(cyclicJ _ z) -FcoreJ -defLz defK.
have [_ _ [cycV _ _]] := typeP_Galois_P maxT (FTtype5_exclusion maxT) galT.
rewrite Ptype_Fcompl_kernel_trivial // in cycV.
by rewrite -(isog_cyclic (quotient1_isog V)) in cycV.
Qed.

(* This is Peterfalvi (14.14). *)
Let LM_cases :
    '[tauM betaM, tau1L phi] != 0 /\ h.-1%:R / pq <= pq - 1
 \/ '[tauL betaL, tau1M psi] != 0 /\ q = 3 /\ p = 5.
Proof.
have [irr_phi irr_psi] := (irrL Lphi, irrM Mpsi).
have:= Dade_sub_lin_nonorthogonal (mFT_odd _) _ cohM cohL _ Mpsi _ _ Lphi.
rewrite -/betaL -/betaM disjoint_Dade_FTtype1 //.
case=> //; set a := '[_, _] => nz_a; [left | right]; split=> //.
  rewrite {1}/pq -indexLH /pq -indexMK.
  by rewrite (coherent_FTtype1_core_ltr cohM cohL Mpsi Lphi) // orbit_sym.
have ub_v: v.-1%:R / pq <= pq - 1.
  rewrite {1}/pq -indexMK /pq -indexLH /v -defK.
  exact: (coherent_FTtype1_core_ltr cohL cohM Lphi Mpsi).
have{ub_v} ub_qp: (q ^ (p - 3) < p ^ 2)%N.
  rewrite -(@ltn_pmul2l (q ^ 3)) ?expn_gt0 ?cardG_gt0 // -expnD subnKC //.
  have: v.-1%:R < pq ^+ 2.
    rewrite -ltr_pdivr_mulr ?ltr0n ?muln_gt0 ?cardG_gt0 //.
    by rewrite (ler_lt_trans ub_v) // ltr_subl_addl -mulrS ltC_nat.
  rewrite -natrX ltC_nat prednK ?cardG_gt0 // mulnC expnMn oV.
  rewrite leq_divLR ?dvdn_pred_predX // mulnC -subn1 leq_subLR.
  move/leq_ltn_trans->; rewrite // -addSn addnC -(leq_add2r (q ^ 2 * p ^ 2)).
  rewrite addnAC -mulSnr prednK ?cardG_gt0 // mulnA leq_add2l -expnMn.
  by rewrite (ltn_sqr 1) (@ltn_mul 1 1) ?prime_gt1.
have q3: q = 3.
  apply/eqP; rewrite eqn_leq qgt2 -ltnS -(odd_ltn 5) ?mFT_odd // -ltnS.
  rewrite -(ltn_exp2l _ _ (ltnW pgt2)) (leq_trans qp1_gt_pq1) // ltnW //.
  by rewrite -{1}(subnK pgt2) -addnS expnD (expnD p 2 4) ltn_mul ?ltn_exp2r.
split=> //; apply/eqP; rewrite eqn_leq -ltnS andbC.
rewrite (odd_geq 5) -1?(odd_ltn 7) ?mFT_odd //= doubleS -{1}q3 ltqp /=.
move: ub_qp; rewrite 2!ltnNge q3; apply: contra.
elim: p => // x IHx; rewrite ltnS leq_eqVlt => /predU1P[<- // | xgt6].
apply: (@leq_trans (3 * x ^ 2)); last first.
  rewrite subSn ?(leq_trans _ xgt6) //.
  by rewrite [rhs in (_ <= rhs)%N]expnS leq_mul ?IHx.
rewrite -addn1 sqrnD -addnA (mulSn 2) leq_add2l muln1.
rewrite (@leq_trans (2 * (x * 7))) ?leq_mul //.
by rewrite mulnCA (mulnDr x 12 2) mulnC leq_add2r -(subnKC xgt6).
Qed.

(* This is Peterfalvi (14.15). *)
Let oU : u = nU.
Proof.
case: ifP (card_FTtypeP_Galois_compl maxS galS) => // p1modq oU.
pose x := #|H : U|; rewrite -/u -/nU -/p -/q in p1modq oU.
have DnU: (q * u)%N = nU.
  rewrite mulnC oU divnK //.
  by have [_ ->] := FTtypeP_primes_mod_cases maxS StypeP.
have oH: h = (u * x)%N by rewrite Lagrange.
have xmodp: x = q %[mod p].
  have hmodp: h = 1 %[mod p].
    apply/eqP; rewrite eqn_mod_dvd ?cardG_gt0 // subn1.
    apply: dvdn_trans (Frobenius_ker_dvd_ker1 frobL).
    have [y _ /index_sdprod <-] := defL.
    by rewrite -[p](cardJg _ y) cardSg ?joing_subr.
  rewrite -[q]muln1 -modnMmr -hmodp modnMmr oH mulnA DnU -modnMml.
  suffices ->: nU = 1 %[mod p] by rewrite modnMml mul1n.
  rewrite /nU predn_exp mulKn; last by rewrite -(subnKC pgt2).
  apply/eqP; rewrite -(ltn_predK qgt2) big_ord_recl eqn_mod_dvd ?subn1 //=.
  by apply: dvdn_sum => i _; rewrite expnS dvdn_mulr.
have{xmodp} [n Dx]: {n | x = q + n * p}%N.
  by exists (x %/ p); rewrite -(modn_small ltqp) addnC -xmodp -divn_eq.
have nmodq: n = 1 %[mod q].
  have [y _ defLy] := defL; have [_ _ /joing_subP[nHW1 _] _] := sdprodP defLy.
  have regHW1: semiregular H W1.
    have /Frobenius_reg_ker := set_Frobenius_compl defLy frobL.
    by apply: semiregularS; rewrite ?joing_subl.
  have hmodq: h = 1 %[mod q].
    apply/eqP; rewrite eqn_mod_dvd ?cardG_gt0 // subn1.
    exact: regular_norm_dvd_pred regHW1.
  have umodq: u = 1 %[mod q].
    apply/eqP; rewrite eqn_mod_dvd ?cardG_gt0 // subn1.
    apply: regular_norm_dvd_pred; first by have [_ []] := StypeP.
    exact: semiregularS regHW1.
  rewrite -hmodq oH -modnMml umodq modnMml mul1n Dx modnDl.
  by rewrite -modnMmr (eqP p1modq) modnMmr muln1.
have{n nmodq Dx} lb_x: (q + q.+1 * p <= x)%N.
  rewrite (divn_eq n q) nmodq (modn_small (ltnW qgt2)) addn1 in Dx.
  rewrite Dx leq_add2l leq_mul // ltnS leq_pmull // lt0n.
  have: odd x by rewrite (dvdn_odd (dvdn_indexg _ _)) ?mFT_odd.
  by rewrite Dx odd_add odd_mul !mFT_odd; apply: contraNneq => ->.
have lb_h: (p ^ q < h)%N.
  rewrite (@leq_trans (p * nU)) //; last first.
    rewrite -DnU oH mulnA mulnC leq_mul // (leq_trans _ lb_x) //.
    by rewrite mulSn addnA mulnC leq_addl.
  rewrite /nU predn_exp mulKn; last by rewrite -(subnKC pgt2).
  rewrite -(subnKC (ltnW qgt2)) subn2 big_ord_recr big_ord_recl /=.
  by rewrite -add1n !mulnDr -!expnS -addnA leq_add ?leq_addl // cardG_gt0.
have ub_h: (h <= p ^ 2 * q ^ 2)%N.
  have [[_ ub_h] | [_ [q3 p5]]] := LM_cases; last by rewrite q3 p5 in p1modq.
  rewrite -expnMn -(ltn_predK lb_h) -ltC_nat natrM -/pq.
  rewrite -ltr_pdivr_mulr ?ltr0n ?muln_gt0 ?cardG_gt0 //.
  by rewrite (ler_lt_trans ub_h) // ltr_subl_addl -mulrS ltC_nat.
have{lb_h} lb_q2: (p ^ q.-2 < q ^ 2)%N.
  rewrite -(@ltn_pmul2l (p ^ 2)) ?expn_gt0 ?cardG_gt0 // (leq_trans _ ub_h) //.
  by rewrite -subn2 -expnD subnKC // ltnW.
have q3: q = 3.
  apply/eqP; rewrite eqn_leq qgt2 -(subnKC (ltnW qgt2)) subn2 ltnS.
  by rewrite -(ltn_exp2l _ _ (ltnW pgt2)) (ltn_trans lb_q2) ?ltn_exp2r.
have{lb_q2 p1modq} p7: p = 7.
  suff: p \in [seq n <- iota 4 5 | prime n & n == 1 %[mod 3]] by case/predU1P.
  by rewrite mem_filter pr_p mem_iota -q3 p1modq ltqp; rewrite q3 in lb_q2 *.
rewrite oH mulnC oU /nU q3 p7 -leq_divRL //= in ub_h lb_x.
by have:= leq_trans lb_x ub_h.
Qed.

(* This is Peterfalvi (14.16), the last step towards the final contradiction. *)
Let defH : `H = U.
Proof.
pose x := #|H : U|; have oH: h = (u * x)%N by rewrite Lagrange.
apply/eqP/idPn; rewrite eqEsubset sUH andbT -indexg_gt1 -/x => xgt1.
have hmodpq: h = 1 %[mod p * q].
  apply/eqP; rewrite eqn_mod_dvd ?cardG_gt0 // -indexLH subn1.
  exact: Frobenius_ker_dvd_ker1.
have [[_ _ frobUW1 _] _ _ _ _] := FTtypeP_facts maxS StypeP.
have /eqP umodpq: u == 1 %[mod p * q].
  rewrite chinese_remainder ?prime_coprime ?dvdn_prime2 ?(gtn_eqF ltqp) //.
  rewrite !eqn_mod_dvd ?cardG_gt0 // subn1 (Frobenius_dvd_ker1 frobUW1).
  rewrite oU /nU predn_exp mulKn; last by rewrite -(subnKC pgt2).
  by rewrite -(ltn_predK qgt2) big_ord_recl dvdn_sum //= => i; rewrite dvdn_exp.
have{hmodpq} lb_x: (p * q < x)%N.
  rewrite -(subnKC (ltnW xgt1)) ltnS dvdn_leq ?subn_gt0 //.
  by rewrite -eqn_mod_dvd 1?ltnW // -hmodpq oH -modnMml umodpq modnMml mul1n.
have [[_ ub_h] | [nz_a [q3 p5]]] := LM_cases.
  have /idPn[]: (p * q < u)%N.
    have ugt1: (1 < u)%N.
      by rewrite cardG_gt1; have [] := Frobenius_context frobUW1.
    rewrite -(subnKC (ltnW ugt1)) ltnS dvdn_leq ?subn_gt0 //.
    by rewrite -eqn_mod_dvd ?umodpq 1?ltnW.
  rewrite -leqNgt -(leq_pmul2r (indexg_gt0 L H)) indexLH.
  apply: (@leq_trans h.-1).
    by rewrite -ltnS prednK ?cardG_gt0 // oH ltn_pmul2l ?cardG_gt0.
  rewrite -indexLH -leC_nat natrM -ler_pdivr_mulr ?gt0CiG // indexLH -/pq.
  by rewrite (ler_trans ub_h) // ler_subl_addl -mulrS leC_nat ltnW.
have lb_h1e_v: (v.-1 %/ p < h.-1 %/ #|L : H|)%N.
  rewrite -(@ltn_pmul2l u) ?cardG_gt0 // -oH oU /nU q3 p5 /= in lb_x.
  rewrite -(ltn_subRL 1) /= subn1 in lb_x.
  by rewrite leq_divRL ?indexG_gt0 // oV /nV indexLH q3 p5 (leq_trans _ lb_x).
have oLM: orthogonal (map tau1L calL) (map tau1M calM).
  by rewrite orthogonal_sym coherent_FTtype1_ortho.
case/eqP: nz_a; have lb_h1e_u := ltn_trans v1p_gt_u1q lb_h1e_v.
have [] // := FTtype2_support_coherence StypeP TtypeP cohL Lphi.
rewrite -/tauL -/sigma => _ [nb [chi Dchi ->]].
rewrite cfdotBl cfdot_suml big1 => [|ij _]; last first.
  have [_ o_tauMeta _ _] := FTtypeI_bridge_facts _ StypeP Mtype1 cohM Mpsi psi1.
  rewrite cfdotZl cfdotC (orthogonalP o_tauMeta) ?map_f ?mem_irr //.
  by rewrite conjC0 mulr0.
case: Dchi => ->; first by rewrite (orthogonalP oLM) ?map_f // subr0.
by rewrite cfdotNl opprK add0r (orthogonalP oLM) ?map_f // cfAut_seqInd.
Qed.

Lemma FTtype2_exclusion : False.
Proof. by have /negP[] := not_charUH; rewrite /= defH char_refl. Qed.

End Fourteen.

Lemma no_minSimple_odd_group (gT : minSimpleOddGroupType) : False.
Proof.
have [/forall_inP | [S [T [_ W W1 W2 defW pairST]]]] := FTtypeP_pair_cases gT.
  exact/negP/not_all_FTtype1.
have xdefW: W2 \x W1 = W by rewrite dprodC.
have pairTS := typeP_pair_sym xdefW pairST.
pose p := #|W2|; pose q := #|W1|.
have p'q: q != p.
  have [[[ctiW _ _] _ _ _ _] /mulG_sub[sW1W sW2W]] := (pairST, dprodW defW).
  have [cycW _ _] := ctiW; apply: contraTneq (cycW) => eq_pq.
  rewrite (cyclic_dprod defW) ?(cyclicS _ cycW) // -/q eq_pq.
  by rewrite /coprime gcdnn -trivg_card1; have [] := cycTI_nontrivial ctiW.
without loss{p'q} ltqp: S T W1 W2 defW xdefW pairST pairTS @p @q / q < p.
  move=> IH_ST; rewrite neq_ltn in p'q.
  by case/orP: p'q; [apply: (IH_ST S T) | apply: (IH_ST T S)].
have [[_ maxS maxT] _ _ _ _] := pairST.
have [[U StypeP] [V TtypeP]] := (typeP_pairW pairST, typeP_pairW pairTS).
have Stype2: FTtype S == 2 := FTtypeP_max_typeII maxS StypeP ltqp.
have Ttype2: FTtype T == 2 := FTtypeP_min_typeII maxS maxT StypeP TtypeP ltqp.
have /mmax_exists[L maxNU_L]: 'N(U) \proper setT.
  have [[_ ntU _ _] cUU _ _ _] := compl_of_typeII maxS StypeP Stype2.
  by rewrite mFT_norm_proper // mFT_sol_proper abelian_sol.
have /mmax_exists[M maxNV_M]: 'N(V) \proper setT.
  have [[_ ntV _ _] cVV _ _ _] := compl_of_typeII maxT TtypeP Ttype2.
  by rewrite mFT_norm_proper // mFT_sol_proper abelian_sol.
have [[maxL sNU_L] [maxM sNV_M]] := (setIdP maxNU_L, setIdP maxNV_M).
have [frobL sUH _] := FTtypeII_support_facts maxS StypeP Stype2 pairST maxNU_L.
have [frobM _ _] := FTtypeII_support_facts maxT TtypeP Ttype2 pairTS maxNV_M.
have Ltype1 := FT_Frobenius_type1 maxL frobL.
have Mtype1 := FT_Frobenius_type1 maxM frobM.
have [tau1L cohL] := FTtype1_coherence maxL Ltype1.
have [tau1M cohM] := FTtype1_coherence maxM Mtype1.
have [phi Lphi phi1] := FTtype1_ref_irr maxL.
have [psi Mpsi psi1] := FTtype1_ref_irr maxM.
exact: (FTtype2_exclusion pairST maxS maxT StypeP TtypeP ltqp
                          maxNU_L sNU_L sUH frobL Ltype1 cohL Lphi phi1
                          maxNV_M sNV_M frobM Mtype1 cohM Mpsi psi1).
Qed.

Theorem Feit_Thompson (gT : finGroupType) (G : {group gT}) :
  odd #|G| -> solvable G.
Proof. exact: (minSimpleOdd_ind no_minSimple_odd_group). Qed.

Theorem simple_odd_group_prime (gT : finGroupType) (G : {group gT}) :
  odd #|G| -> simple G -> prime #|G|.
Proof. exact: (minSimpleOdd_prime no_minSimple_odd_group). Qed.



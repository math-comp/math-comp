(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset center.
Require Import fingroup morphism perm automorphism quotient action finalg zmodp.
Require Import gfunctor gproduct cyclic commutator gseries nilpotent pgroup.
Require Import sylow hall abelian maximal frobenius.
Require Import matrix mxalgebra mxrepresentation mxabelem vector.
Require Import BGsection1 BGsection3 BGsection7 BGsection15 BGsection16.
Require Import ssrnum algC classfun character integral_char inertia vcharacter.
Require Import PFsection1 PFsection2 PFsection3 PFsection4.
Require Import PFsection5 PFsection6 PFsection7 PFsection8 PFsection9.

(******************************************************************************)
(* This file covers Peterfalvi, Section 10: Maximal subgroups of Types III,   *)
(* IV and V. For defW : W1 \x W2 = W and MtypeP : of_typeP M U defW, and      *)
(* setting ptiW := FT_primeTI_hyp MtypeP, mu2_ i j := primeTIirr ptiW i j and *)
(* delta_ j := primeTIsign j, we define here, for M of type III-V:            *)
(*  FTtype345_TIirr_degree MtypeP == the common degree of the components of   *)
(*             (locally) d  the images of characters of irr W that don't have *)
(*                          W2 in their kernel by the cyclicTI isometry to M. *)
(*                          Thus mu2_ i j 1%g = d%:R for all j != 0.          *)
(*  FTtype345_TIsign MtypeP == the common sign of the images of characters    *)
(*         (locally) delta  of characters of irr W that don't have W2 in      *)
(*                          their kernel by the cyclicTI isometry to M.       *)
(*                          Thus delta_ j = delta for all j != 0.             *)
(*   FTtype345_ratio MtypeP == the ratio (d - delta) / #|W1|. Even though it  *)
(*             (locally) n  is always a positive integer we take n : algC.    *)
(* FTtype345_bridge MtypeP s i j == a virtual character that can be used to   *)
(*    (locally) alpha_ i j  bridge coherence between the mu2_ i j and other   *)
(*                          irreducibles of M; here s should be the index of  *)
(*                          an irreducible character of M induced from M^(1). *)
(*                          := mu2_ i j - delta *: mu2_ i 0 -n *: 'chi_s.     *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory Num.Theory.

Section Ten.

Variable gT : minSimpleOddGroupType.
Local Notation G := (TheMinSimpleOddGroup gT).
Implicit Types (p q : nat) (x y z : gT).
Implicit Types H K L N P Q R S T U W : {group gT}.

Local Notation "#1" := (inord 1) (at level 0).

Section OneMaximal.

(* These assumptions correspond to Peterfalvi, Hypothesis (10.1).             *)
(* We also declare the group U_M, even though it is not used in this section, *)
(* because it is a parameter to the theorems and definitions of PFsection8    *)
(* and PFsection9.                                                            *)
Variables M U_M W W1 W2 : {group gT}.
Hypotheses (maxM : M \in 'M) (defW : W1 \x W2 = W).
Hypotheses (MtypeP : of_typeP M U_M defW) (notMtype2: FTtype M != 2).

Local Notation "` 'M'" := (gval M) (at level 0, only parsing) : group_scope.
Local Notation "` 'W1'" := (gval W1) (at level 0, only parsing) : group_scope.
Local Notation "` 'W2'" := (gval W2) (at level 0, only parsing) : group_scope.
Local Notation "` 'W'" := (gval W) (at level 0, only parsing) : group_scope.
Local Notation V := (cyclicTIset defW).
Local Notation M' := M^`(1)%G.
Local Notation "` 'M''" := `M^`(1) (at level 0) : group_scope.
Local Notation M'' := M^`(2)%G.
Local Notation "` 'M'''" := `M^`(2) (at level 0) : group_scope.

Let defM : M' ><| W1 = M. Proof. by have [[]] := MtypeP. Qed.
Let nsM''M' : M'' <| M'. Proof. exact: (der_normal 1 M'). Qed.
Let nsM'M : M' <| M. Proof. exact: (der_normal 1 M). Qed.
Let sM'M : M' \subset M. Proof. exact: der_sub. Qed.
Let nsM''M : M'' <| M. Proof. exact: der_normal 2 M. Qed.

Let notMtype1 : FTtype M != 1%N. Proof. exact: FTtypeP_neq1 MtypeP. Qed.
Let typeMgt2 : FTtype M > 2.
Proof. by move: (FTtype M) (FTtype_range M) notMtype1 notMtype2=> [|[|[]]]. Qed.

Let defA1 : 'A1(M) = M'^#. Proof. by rewrite /= -FTcore_eq_der1. Qed.
Let defA : 'A(M) = M'^#. Proof. by rewrite FTsupp_eq1 ?defA1. Qed.
Let defA0 : 'A0(M) = M'^# :|: class_support V M.
Proof. by rewrite -defA (FTtypeP_supp0_def _ MtypeP). Qed.
Let defMs : M`_\s :=: M'. Proof. exact: FTcore_type_gt2. Qed.

Let pddM := FT_prDade_hyp maxM MtypeP.
Let ptiWM : primeTI_hypothesis M M' defW := FT_primeTI_hyp MtypeP.
Let ctiWG : cyclicTI_hypothesis G defW := pddM.
Let ctiWM : cyclicTI_hypothesis M defW := prime_cycTIhyp ptiWM.

Let ntW1 : W1 :!=: 1. Proof. by have [[]] := MtypeP. Qed.
Let ntW2 : W2 :!=: 1. Proof. by have [_ _ _ []] := MtypeP. Qed.
Let cycW1 : cyclic W1. Proof. by have [[]] := MtypeP. Qed.
Let cycW2 : cyclic W2. Proof. by have [_ _ _ []] := MtypeP. Qed.

Let w1 := #|W1|.
Let w2 := #|W2|.
Let nirrW1 : #|Iirr W1| = w1. Proof. by rewrite card_Iirr_cyclic. Qed.
Let nirrW2 : #|Iirr W2| = w2. Proof. by rewrite card_Iirr_cyclic. Qed.
Let NirrW1 : Nirr W1 = w1. Proof. by rewrite -nirrW1 card_ord. Qed.
Let NirrW2 : Nirr W2 = w2. Proof. by rewrite -nirrW2 card_ord. Qed.

Let w1gt2 : w1 > 2. Proof. by rewrite odd_gt2 ?mFT_odd ?cardG_gt1. Qed.
Let w2gt2 : w2 > 2. Proof. by rewrite odd_gt2 ?mFT_odd ?cardG_gt1. Qed.

Let coM'w1 : coprime #|M'| w1.
Proof. by rewrite (coprime_sdprod_Hall_r defM); have [[]] := MtypeP. Qed.

(* This is used both in (10.2) and (10.8). *)
Let frobMbar : [Frobenius M / M'' = (M' / M'') ><| (W1 / M'')].
Proof.
have [[_ hallW1 _ _] _ _ [_ _ _ sW2M'' regM'W1 ] _] := MtypeP.
apply: Frobenius_coprime_quotient => //.
split=> [|w /regM'W1-> //]; apply: (sol_der1_proper (mmax_sol maxM)) => //.
by apply: subG1_contra ntW2; apply: subset_trans sW2M'' (der_sub 1 M').
Qed.

Local Open Scope ring_scope.

Let sigma := (cyclicTIiso ctiWG).
Let w_ i j := (cyclicTIirr defW i j).
Local Notation eta_ i j := (sigma (w_ i j)).

Local Notation Imu2 := (primeTI_Iirr ptiWM).
Let mu2_ i j := primeTIirr ptiWM i j.
Let mu_ := primeTIred ptiWM.
Local Notation chi_ j := (primeTIres ptiWM j).

Local Notation Idelta := (primeTI_Isign ptiWM).
Local Notation delta_ j := (primeTIsign ptiWM j).

Local Notation tau := (FT_Dade0 maxM).
Local Notation "chi ^\tau" := (tau chi).

Let calS0 := seqIndD M' M M`_\s 1.
Let rmR := FTtypeP_coh_base maxM MtypeP.
Let scohS0 : subcoherent calS0 tau rmR.
Proof. exact: FTtypeP_subcoherent MtypeP. Qed.

Let calS := seqIndD M' M M' 1.
Let sSS0 : cfConjC_subset calS calS0.
Proof. by apply: seqInd_conjC_subset1; rewrite /= ?defMs. Qed.

Let mem_calS s : ('Ind 'chi[M']_s \in calS) = (s != 0).
Proof.
rewrite mem_seqInd ?normal1 ?FTcore_normal //=.
by rewrite !inE sub1G subGcfker andbT.
Qed.

Let calSmu j : j != 0 -> mu_ j \in calS.
Proof.
move=> nz_j; rewrite -[mu_ j]cfInd_prTIres mem_calS -irr_eq1.
by rewrite -(prTIres0 ptiWM) (inj_eq irr_inj) (inj_eq (prTIres_inj _)).
Qed.

Let tauM' : {subset 'Z[calS, M'^#] <= 'CF(M, 'A0(M))}.
Proof. by rewrite defA0 => phi /zchar_on/(cfun_onS (subsetUl _ _))->. Qed.

(* This is Peterfalvi (10.2). *)
(* Note that this result is also valid for type II groups. *)
Lemma FTtypeP_ref_irr :
  {zeta | [/\ zeta \in irr M, zeta \in calS & zeta 1%g = w1%:R]}.
Proof.
have [_ /has_nonprincipal_irr[s nz_s] _ _ _] := Frobenius_context frobMbar.
exists ('Ind 'chi_s %% M'')%CF; split.
- exact/cfMod_irr/(irr_induced_Frobenius_ker (FrobeniusWker frobMbar)).
- by rewrite -cfIndMod ?normal_sub // -mod_IirrE // mem_calS mod_Iirr_eq0.
rewrite -cfIndMod ?cfInd1 ?normal_sub // -(index_sdprod defM) cfMod1.
by rewrite lin_char1 ?mulr1 //; apply/char_abelianP/sub_der1_abelian.
Qed.

(* This is Peterfalvi (10.3), first assertion. *)
Lemma FTtype345_core_prime : prime w2.
Proof.
have [S pairMS [xdefW [U StypeP]]] := FTtypeP_pair_witness maxM MtypeP.
have [[_ _ maxS] _] := pairMS; rewrite {1}(negPf notMtype2) /= => Stype2 _ _.
by have [[]] := compl_of_typeII maxS StypeP Stype2.
Qed.
Let w2_pr := FTtype345_core_prime.

Definition FTtype345_TIirr_degree := truncC (mu2_ 0 #1 1%g).
Definition FTtype345_TIsign := delta_ #1.
Local Notation d := FTtype345_TIirr_degree.
Local Notation delta := FTtype345_TIsign.
Definition FTtype345_ratio := (d%:R - delta) / w1%:R.
Local Notation n := FTtype345_ratio.

(* This is the remainder of Peterfalvi (10.3). *)
Lemma FTtype345_constants :
  [/\ forall i j, j != 0 -> mu2_ i j 1%g = d%:R,
    forall j, j != 0 -> delta_ j = delta,
      (d > 1)%N
    & n \in Cnat].
Proof.
have nz_j1 : #1 != 0 :> Iirr W2 by rewrite Iirr1_neq0.
have invj j: j != 0 -> mu2_ 0 j 1%g = d%:R /\ delta_ j = delta.
  move=> nz_j; have [k co_k_j1 Dj] := cfExp_prime_transitive w2_pr nz_j1 nz_j.
  rewrite -(cforder_dprodr defW) -dprod_IirrEr in co_k_j1.
  have{co_k_j1} [[u Dj1u] _] := cycTIiso_aut_exists ctiWM co_k_j1.
  rewrite dprod_IirrEr -rmorphX -Dj /= -!dprod_IirrEr -!/(w_ _ _) in Dj1u.
  rewrite truncCK ?Cnat_irr1 //.
  have: delta_ j *: mu2_ 0 j == cfAut u (delta_ #1 *: mu2_ 0 #1).
    by rewrite -!(cycTIiso_prTIirr pddM) -/ctiWM -Dj1u.
  rewrite raddfZsign /= -prTIirr_aut eq_scaled_irr signr_eq0 /= /mu2_.
  by case/andP=> /eqP-> /eqP->; rewrite prTIirr_aut cfunE aut_Cnat ?Cnat_irr1.
have d_gt1: (d > 1)%N.
  rewrite ltn_neqAle andbC -eqC_nat -ltC_nat truncCK ?Cnat_irr1 //.
  rewrite irr1_gt0 /= eq_sym; apply: contraNneq nz_j1 => mu2_lin.
  have: mu2_ 0 #1 \is a linear_char by rewrite qualifE irr_char /= mu2_lin.
  by rewrite lin_irr_der1 => /(prTIirr0P ptiWM)[i /irr_inj/prTIirr_inj[_ ->]].
split=> // [i j /invj[<- _] | _ /invj[//] | ]; first by rewrite prTIirr_1.
have: (d%:R == delta %[mod w1])%C by rewrite truncCK ?Cnat_irr1 ?prTIirr1_mod.
rewrite /eqCmod unfold_in -/n (negPf (neq0CG W1)) CnatEint => ->.
rewrite divr_ge0 ?ler0n // [delta]signrE opprB addrA -natrD subr_ge0 ler1n.
by rewrite -(subnKC d_gt1).
Qed.

Let o_mu2_irr zeta i j :
  zeta \in calS -> zeta \in irr M -> '[mu2_ i j, zeta] = 0.
Proof.
case/seqIndP=> s _ -> irr_sM; rewrite -cfdot_Res_l cfRes_prTIirr cfdot_irr.
rewrite (negPf (contraNneq _ (prTIred_not_irr ptiWM j))) // => Ds.
by rewrite -cfInd_prTIres Ds.
Qed.

Let ZmuBzeta zeta j :
    zeta \in calS -> zeta 1%g = w1%:R -> j != 0 ->
  mu_ j - d%:R *: zeta \in 'Z[calS, M'^#].
Proof.
move=> Szeta zeta1w1 nz_j; have [mu1 _ _ _] := FTtype345_constants.
rewrite -[d%:R](mulKf (neq0CiG M M')) mulrC -(mu1 0 j nz_j).
rewrite -(cfResE _ sM'M) // cfRes_prTIirr -cfInd1 // cfInd_prTIres.
by rewrite (seqInd_sub_lin_vchar _ Szeta) ?calSmu // -(index_sdprod defM).
Qed.

Let mu0Bzeta_on zeta :
  zeta \in calS -> zeta 1%g = w1%:R -> mu_ 0 - zeta \in 'CF(M, 'A(M)).
Proof.
move/seqInd_on=> M'zeta zeta1w1; rewrite [mu_ 0]prTIred0 defA cfun_onD1.
rewrite !cfunE zeta1w1 cfuniE // group1 mulr1 subrr rpredB ?M'zeta //=.
by rewrite rpredZ ?cfuni_on.
Qed.

(* We need to prove (10.5) - (10.7) for an arbitrary choice of zeta, to allow *)
(* part of the proof of (10.5) to be reused in that of (11.8).                *)
Variable zeta : 'CF(M).
Hypotheses (irr_zeta : zeta \in irr M) (Szeta : zeta \in calS).
Hypothesis (zeta1w1 : zeta 1%g = w1%:R).

Let o_mu2_zeta i j : '[mu2_ i j, zeta] = 0. Proof. exact: o_mu2_irr. Qed.

Let o_mu_zeta j : '[mu_ j, zeta] = 0.
Proof. by rewrite cfdot_suml big1 // => i _; apply: o_mu2_zeta. Qed.

Definition FTtype345_bridge i j :=  mu2_ i j - delta *: mu2_ i 0 - n *: zeta.
Local Notation alpha_ := FTtype345_bridge.

(* This is the first part of Peterfalvi (10.5), which does not depend on the  *)
(* coherence assumption that will ultimately be refuted by (10.8).            *)
Lemma supp_FTtype345_bridge i j : j != 0 -> alpha_ i j \in 'CF(M, 'A0(M)).
Proof.
move=> nz_j; have [Dd Ddelta _ _] := FTtype345_constants.
have Dmu2 := prTIirr_id pddM.
have W1a0 x: x \in W1 -> alpha_ i j x = 0.
  move=> W1x; rewrite !cfunE; have [-> | ntx] := eqVneq x 1%g.
    by rewrite Dd // prTIirr0_1 mulr1 zeta1w1 divfK ?neq0CG ?subrr.
  have notM'x: x \notin M'.
    apply: contra ntx => M'x; have: x \in M' :&: W1 by apply/setIP.
    by rewrite coprime_TIg ?inE.
  have /sdprod_context[_ sW1W _ _ tiW21] := dprodWsdC defW.
  have abW2: abelian W2 := cyclic_abelian cycW2.
  have Wx: x \in W :\: W2.
    rewrite inE (contra _ ntx) ?(subsetP sW1W) // => W2x.
    by rewrite -in_set1 -set1gE -tiW21 inE W2x.
  rewrite !Dmu2 {Wx}// Ddelta // prTIsign0 scale1r !dprod_IirrE cfunE.
  rewrite -!(cfResE _ sW1W) ?cfDprodKl_abelian // subrr.
  have [s _ ->] := seqIndP Szeta.
  by rewrite (cfun_on0 (cfInd_normal _ _)) ?mulr0 ?subrr.
apply/cfun_onP=> x; rewrite !inE defA notMtype1 /= => /norP[notM'x].
set pi := \pi(M'); have [Mx /= pi_x | /cfun0->//] := boolP (x \in M).
have hallM': pi.-Hall(M) M' by rewrite Hall_pi -?(coprime_sdprod_Hall_l defM).
have hallW1: pi^'.-Hall(M) W1 by rewrite -(compl_pHall _ hallM') sdprod_compl.
have{pi_x} pi'x: pi^'.-elt x.
  apply: contraR notM'x => not_pi'x; rewrite !inE (mem_normal_Hall hallM') //.
  rewrite not_pi'x andbT negbK in pi_x.
  by rewrite (contraNneq _ not_pi'x) // => ->; apply: p_elt1.
have [|y My] := Hall_subJ (mmax_sol maxM) hallW1 _ pi'x; rewrite cycle_subG //.
by case/imsetP=> z Wz ->; rewrite cfunJ ?W1a0.
Qed.
Local Notation alpha_on := supp_FTtype345_bridge.

Lemma vchar_FTtype345_bridge i j : alpha_ i j \in 'Z[irr M].
Proof.
have [_ _ _ Nn] := FTtype345_constants.
by rewrite !rpredB ?rpredZsign ?rpredZ_Cnat ?irr_vchar ?mem_zchar.
Qed.
Local Notation Zalpha := vchar_FTtype345_bridge.
Local Hint Resolve Zalpha.

Lemma vchar_Dade_FTtype345_bridge i j :
  j != 0 -> (alpha_ i j)^\tau \in 'Z[irr G].
Proof. by move=> nz_j; rewrite Dade_vchar // zchar_split Zalpha alpha_on. Qed.
Local Notation Zalpha_tau := vchar_Dade_FTtype345_bridge.

(* This covers the last paragraph in the proof of (10.5); it's isolated here  *)
(* because it is reused in the proof of (10.10) and (11.8).                   *)

Lemma norm_FTtype345_bridge i j :
  j != 0 -> '[(alpha_ i j)^\tau] = 2%:R + n ^+ 2.
Proof.
move=> nz_j; rewrite Dade_isometry ?alpha_on // cfnormBd ?cfnormZ; last first.
  by rewrite cfdotZr cfdotBl cfdotZl !o_mu2_zeta !(mulr0, subr0).
have [_ _ _ /Cnat_ge0 n_ge0] := FTtype345_constants.
rewrite ger0_norm // cfnormBd ?cfnorm_sign ?cfnorm_irr ?irrWnorm ?mulr1 //.
by rewrite cfdotZr (cfdot_prTIirr pddM) (negPf nz_j) andbF ?mulr0.
Qed.
Local Notation norm_alpha := norm_FTtype345_bridge.

Implicit Type tau : {additive 'CF(M) -> 'CF(G)}.

(* This exported version is adapted to its use in (11.8). *)
Lemma FTtype345_bridge_coherence calS1 tau1 i j X Y :
     coherent_with calS1 M^# tau tau1 -> (alpha_ i j)^\tau = X + Y ->
     cfConjC_subset calS1 calS0 -> {subset calS1 <= irr M} ->
     j != 0 -> Y \in 'Z[map tau1 calS1] -> '[Y, X] = 0 -> '[Y] = n ^+ 2 ->
  X = delta *: (eta_ i j - eta_ i 0).
Proof.
move=> cohS1 Dalpha sS10 irrS1 nz_j S1_Y oYX nY_n2.
have [[_ Ddelta _ Nn] [[Itau1 Ztau1] _]] := (FTtype345_constants, cohS1).
have [|z Zz defY] := zchar_expansion _ S1_Y.
  rewrite map_inj_in_uniq; first by case: sS10.
  by apply: sub_in2 (Zisometry_inj Itau1); apply: mem_zchar.
have nX_2: '[X] = 2%:R.
  apply: (addrI '[Y]); rewrite -cfnormDd // addrC -Dalpha norm_alpha //.
  by rewrite addrC nY_n2.
have Z_X: X \in 'Z[irr G].
  rewrite -[X](addrK Y) -Dalpha rpredB ?Zalpha_tau // defY big_map big_seq.
  by apply: rpred_sum => psi S1psi; rewrite rpredZ_Cint // Ztau1 ?mem_zchar.
apply: eq_signed_sub_cTIiso => // y Vy; rewrite -[X](addrK Y) -Dalpha -/delta.
rewrite !cfunE !cycTIiso_restrict //; set rhs := delta * _.
rewrite Dade_id ?defA0 //; last by rewrite setUC inE mem_class_support.
have notM'y: y \notin M'.
  by have:= subsetP (prDade_supp_disjoint pddM) y Vy; rewrite inE.
have Wy: y \in W :\: W2 by move: Vy; rewrite !inE => /andP[/norP[_ ->]].
rewrite !cfunE 2?{1}prTIirr_id // prTIsign0 scale1r Ddelta // cfunE -mulrBr.
rewrite -/rhs (cfun_on0 (seqInd_on _ Szeta)) // mulr0 subr0.
rewrite (ortho_cycTIiso_vanish ctiWG) ?subr0 // -/sigma.
apply/orthoPl=> _ /mapP[_ /(cycTIirrP defW)[i1 [j1 ->]] ->].
rewrite defY cfdot_suml big_map big1_seq //= => psi S1psi.
by rewrite cfdotZl (coherent_ortho_cycTIiso MtypeP sS10) ?irrS1 ?mulr0.
Qed.

(* This is a specialization of the above, used in (10.5) and (10.10). *)
Let def_tau_alpha calS1 tau1 i j :
     coherent_with calS1 M^# tau tau1 -> cfConjC_subset calS1 calS0 ->
     j != 0 -> zeta \in calS1 -> '[(alpha_ i j)^\tau, tau1 zeta] = - n ->
  (alpha_ i j)^\tau = delta *: (eta_ i j - eta_ i 0) - n *: tau1 zeta.
Proof.
move=> cohS1 [_ sS10 ccS1] nz_j S1zeta alpha_zeta_n.
have [[_ _ _ Nn] [[Itau1 _] _]] := (FTtype345_constants, cohS1).
set Y := - (n *: _); apply: canRL (addrK _) _; set X := _ + _.
have Dalpha: (alpha_ i j)^\tau = X + Y by rewrite addrK.
have nY_n2: '[Y] = n ^+ 2.
  by rewrite cfnormN cfnormZ norm_Cnat // Itau1 ?mem_zchar // irrWnorm ?mulr1.
pose S2 := zeta :: zeta^*%CF; pose S2tau1 := map tau1 S2.
have S2_Y: Y \in 'Z[S2tau1] by rewrite rpredN rpredZ_Cnat ?mem_zchar ?mem_head.
have sS21: {subset S2 <= calS1} by apply/allP; rewrite /= ccS1 ?S1zeta.
have cohS2 : coherent_with S2 M^# tau tau1 := subset_coherent_with sS21 cohS1.
have irrS2: {subset S2 <= irr M} by apply/allP; rewrite /= cfAut_irr irr_zeta.
rewrite (FTtype345_bridge_coherence cohS2 Dalpha) //; last first.
  rewrite -[X]opprK cfdotNr opprD cfdotDr nY_n2 cfdotNl cfdotNr opprK cfdotZl.
  by rewrite cfdotC alpha_zeta_n rmorphN conj_Cnat // mulrN addNr oppr0.
split=> [|_ /sS21/sS10//|]; last first.
  by apply/allP; rewrite /= !inE cfConjCK !eqxx orbT.
by rewrite /= inE eq_sym; have [[_ /hasPn-> //]] := scohS0; apply: sS10.
Qed.

Section NonCoherence.

(* We will ultimately contradict these assumptions. *)
(* Note that we do not need to export any lemma save the final contradiction. *)
Variable tau1 : {additive 'CF(M) -> 'CF(G)}.
Hypothesis cohS : coherent_with calS M^# tau tau1.

Local Notation "mu ^\tau1" := (tau1 mu%CF)
  (at level 2, format "mu ^\tau1") : ring_scope.

Let Dtau1 : {in 'Z[calS, M'^#], tau1 =1 tau}.
Proof. by case: cohS => _; apply: sub_in1; apply: zchar_onS; apply: setSD. Qed.

Let o_zeta_s: '[zeta, zeta^*] = 0.
Proof. by rewrite (seqInd_conjC_ortho _ _ _ Szeta) ?mFT_odd /= ?defMs. Qed.

Import ssrint rat.

(* This is the second part of Peterfalvi (10.5). *)
Let tau_alpha i j : j != 0 ->
  (alpha_ i j)^\tau = delta *: (eta_ i j - eta_ i 0) - n *: zeta^\tau1.
Proof.
move=> nz_j; set al_ij := alpha_ i j; have [[Itau1 Ztau1] _] := cohS.
have [mu1 Ddelta d_gt1 Nn] := FTtype345_constants.
pose a := '[al_ij^\tau, zeta^\tau1] + n.
have al_ij_zeta_s: '[al_ij^\tau, zeta^*^\tau1] = a.
  apply: canRL (addNKr _) _; rewrite addrC -opprB -cfdotBr -raddfB.
  have M'dz: zeta - zeta^*%CF \in 'Z[calS, M'^#] by apply: seqInd_sub_aut_zchar.
  rewrite Dtau1 // Dade_isometry ?alpha_on ?tauM' //.
  rewrite cfdotBr opprB cfdotBl cfdot_conjCr rmorphB linearZ /=.
  rewrite -!prTIirr_aut !cfdotBl !cfdotZl !o_mu2_zeta o_zeta_s !mulr0. 
  by rewrite opprB !(subr0, rmorph0) add0r irrWnorm ?mulr1.
have Zal_ij: al_ij^\tau \in 'Z[irr G] by apply: Zalpha_tau.
have Za: a \in Cint.
  by rewrite rpredD ?(Cint_Cnat Nn) ?Cint_cfdot_vchar ?Ztau1 ?(mem_zchar Szeta).
have{al_ij_zeta_s} ub_da2: (d ^ 2)%:R * a ^+ 2 <= (2%:R + n ^+ 2) * w1%:R.
  have [k nz_k j'k]: exists2 k, k != 0 & k != j.
    have:= w2gt2; rewrite -nirrW2 (cardD1 0) (cardD1 j) !inE nz_j !ltnS lt0n. 
    by case/pred0Pn=> k /and3P[]; exists k.
  have muk_1: mu_ k 1%g = (d * w1)%:R.
    by rewrite (prTIred_1 pddM) mu1 // mulrC -natrM.
  rewrite natrX -exprMn; have <-: '[al_ij^\tau, (mu_ k)^\tau1] = d%:R * a.
    rewrite mulrDr mulr_natl -raddfMn /=; apply: canRL (addNKr _) _.
    rewrite addrC -cfdotBr -raddfMn -raddfB -scaler_nat.
    rewrite Dtau1 ?Dade_isometry ?alpha_on ?tauM' ?ZmuBzeta // cfdotBr cfdotZr.
    rewrite rmorph_nat !cfdotBl !cfdotZl !o_mu2_zeta irrWnorm //.
    rewrite !(cfdot_prTIirr_red pddM) cfdotC o_mu_zeta conjC0 !mulr0 mulr1.
    by rewrite 2![_ == k](negPf _) 1?eq_sym // mulr0 -mulrN opprB !subr0 add0r.
  have ZSmuk: mu_ k \in 'Z[calS] by rewrite mem_zchar ?calSmu.
  have <-: '[al_ij^\tau] * '[(mu_ k)^\tau1] = (2%:R + n ^+ 2) * w1%:R.
    by rewrite Itau1 // cfdot_prTIred eqxx mul1n norm_alpha. 
  by rewrite -Cint_normK ?cfCauchySchwarz // Cint_cfdot_vchar // Ztau1.
suffices a0 : a = 0.
  by apply: (def_tau_alpha _ sSS0); rewrite // -sub0r -a0 addrK.
apply: contraTeq (d_gt1) => /(sqr_Cint_ge1 Za) a2_ge1.
suffices: n == 0.
  rewrite mulf_eq0 invr_eq0 orbC -implyNb neq0CG /= subr_eq0 => /eqP Dd.
  by rewrite -ltC_nat -(normr_nat _ d) Dd normr_sign ltrr.
suffices: n ^+ 2 < n + 1.
  have d_dv_M: (d%:R %| #|M|)%C by rewrite -(mu1 0 j) // ?dvd_irr1_cardG.
  have{d_dv_M} d_odd: odd d by apply: dvdn_odd (mFT_odd M); rewrite -dvdC_nat.
  have: (2 %| n * w1%:R)%C.
    rewrite divfK ?neq0CG // -signrN signrE addrA -(natrD _ d 1).
    by rewrite rpredB // dvdC_nat dvdn2 ?odd_double // odd_add d_odd.
  rewrite -(truncCK Nn) -mulrSr -natrM -natrX ltC_nat (dvdC_nat 2) pnatr_eq0.
  rewrite dvdn2 odd_mul mFT_odd; case: (truncC n) => [|[|n1]] // _ /idPn[].
  by rewrite -leqNgt (ltn_exp2l 1).
apply: ltr_le_trans (_ : n * - delta + 1 <= _); last first.
  have ->: n + 1 = n * `|- delta| + 1 by rewrite normrN normr_sign mulr1.
  rewrite ler_add2r ler_wpmul2l ?Cnat_ge0 ?real_ler_norm //.
  by rewrite rpredN ?rpred_sign.
rewrite -(ltr_pmul2r (ltC_nat 0 2)) mulrDl mul1r -[rhs in rhs + _]mulrA.
apply: ler_lt_trans (_ : n ^+ 2 * (w1%:R - 1) < _).
  rewrite -(subnKC w1gt2) -(@natrB _ _ 1) // ler_wpmul2l ?leC_nat //.
  by rewrite Cnat_ge0 ?rpredX.
rewrite -(ltr_pmul2l (gt0CG W1)) -/w1 2!mulrBr mulr1 mulrCA -exprMn.
rewrite mulrDr ltr_subl_addl addrCA -mulrDr mulrCA mulrA -ltr_subl_addl.
rewrite -mulrBr mulNr opprK divfK ?neq0CG // mulr_natr addrA subrK -subr_sqr.
rewrite sqrr_sign mulrC [_ + 2%:R]addrC (ltr_le_trans _ ub_da2) //.
apply: ltr_le_trans (ler_wpmul2l (ler0n _ _) a2_ge1).
by rewrite mulr1 ltr_subl_addl -mulrS -natrX ltC_nat.
Qed.

(* This is the first part of Peterfalvi (10.6)(a). *)
Let tau1mu j : j != 0 -> (mu_ j)^\tau1 = delta *: \sum_i eta_ i j.
Proof.
move=> nz_j; have [[[Itau1 _] _] Smu_j] := (cohS, calSmu nz_j).
have eta_mu i: '[delta *: (eta_ i j - eta_ i 0), (mu_ j)^\tau1] = 1.
  have Szeta_s: zeta^*%CF \in calS by rewrite cfAut_seqInd.
  have o_zeta_s_w k: '[eta_ i k, d%:R *: zeta^*^\tau1] = 0.
    have o_S_eta_ := coherent_ortho_cycTIiso MtypeP sSS0 cohS.
    by rewrite cfdotZr cfdotC o_S_eta_ ?conjC0 ?mulr0 // cfAut_irr.
  pose psi := mu_ j -  d%:R *: zeta^*%CF; rewrite (canRL (subrK _) (erefl psi)).
  rewrite (raddfD tau1) raddfZnat cfdotDr addrC cfdotZl cfdotBl !{}o_zeta_s_w.
  rewrite subr0 mulr0 add0r -(canLR (subrK _) (tau_alpha i nz_j)).
  have Zpsi: psi \in 'Z[calS, M'^#].
    by rewrite ZmuBzeta // cfunE zeta1w1 rmorph_nat.
  rewrite cfdotDl cfdotZl Itau1 ?(zcharW Zpsi) ?mem_zchar // -cfdotZl Dtau1 //.
  rewrite Dade_isometry ?alpha_on ?tauM' {Zpsi}// -cfdotDl cfdotBr cfdotZr.
  rewrite subrK !cfdotBl !cfdotZl !cfdot_prTIirr_red eq_sym (negPf nz_j).
  by rewrite !o_mu2_irr ?cfAut_irr // !(mulr0, subr0) eqxx.
have [_ Ddel _ _] := FTtype345_constants.
have [[d1 k] Dtau1mu] := FTtypeP_coherent_TIred sSS0 cohS irr_zeta Szeta Smu_j.
case=> [[Dd1 Dk] | [_ Dk _]]; first by rewrite Dtau1mu Dd1 Dk [_ ^+ _]Ddel.
have /esym/eqP/idPn[] := eta_mu 0; rewrite Dtau1mu Dk /= cfdotZl cfdotZr.
rewrite cfdot_sumr big1 ?mulr0 ?oner_eq0 // => i _; rewrite -/sigma -/(w_ i _).
rewrite cfdotBl !(cfdot_cycTIiso pddM) !(eq_sym 0) conjC_Iirr_eq0 -!irr_eq1.
rewrite (eq_sym j) -(inj_eq irr_inj) conjC_IirrE.
by rewrite odd_eq_conj_irr1 ?mFT_odd ?subrr.
Qed.

(* This is the second part of Peterfalvi (10.6)(a). *)
Let tau1mu0 : (mu_ 0 - zeta)^\tau = \sum_i eta_ i 0 - zeta^\tau1.
Proof.
have [j nz_j] := has_nonprincipal_irr ntW2.
have sum_al: \sum_i alpha_ i j = mu_ j - d%:R *: zeta - delta *: (mu_ 0 - zeta).
  rewrite scalerBr opprD addrACA scaler_sumr !sumrB sumr_const; congr (_ + _).
  by rewrite -opprD -scalerBl nirrW1 -scaler_nat scalerA mulrC divfK ?neq0CG.
have ->: mu_ 0 - zeta = delta *: (mu_ j - d%:R *: zeta - \sum_i alpha_ i j).
  by rewrite sum_al opprD addNKr opprK signrZK.
rewrite linearZ linearB; apply: canLR (signrZK _) _; rewrite -/delta /=.
rewrite linear_sum -Dtau1 ?ZmuBzeta //= raddfB raddfZnat addrAC scalerBr.
rewrite (eq_bigr _ (fun i _ => tau_alpha i nz_j)) sumrB sumr_const nirrW1 opprD.
rewrite -scaler_sumr sumrB scalerBr -tau1mu // opprD !opprK -!addrA addNKr.
congr (_ + _); rewrite -scaler_nat scalerA mulrC divfK ?neq0CG //.
by rewrite addrC -!scaleNr -scalerDl addKr.
Qed.

(* This is Peterfalvi (10.6)(b). *)
Let zeta_tau1_coprime g :
  g \notin 'A~(M) -> coprime #[g] w1 -> `|zeta^\tau1 g| >= 1.
Proof.
move=> notAg co_g_w1; have Amu0zeta := mu0Bzeta_on Szeta zeta1w1.
have mu0_zeta_g: (mu_ 0 - zeta)^\tau g = 0.
  have [ | ] := boolP (g \in 'A0~(M)); rewrite -FT_Dade0_supportE; last first.
    by apply: cfun_on0; apply: Dade_cfunS.
  case/bigcupP=> x A0x xRg; rewrite (DadeE _ A0x) // (cfun_on0 Amu0zeta) //.
  apply: contra notAg => Ax; apply/bigcupP; exists x => //.
  by rewrite -def_FTsignalizer0.
have{mu0_zeta_g} zeta_g: zeta^\tau1 g = \sum_i eta_ i 0 g.
  by apply/esym/eqP; rewrite -subr_eq0 -{2}mu0_zeta_g tau1mu0 !cfunE sum_cfunE.
have Zwg i: eta_ i 0 g \in Cint.
  have Lchi: 'chi_i \is a linear_char by apply: irr_cyclic_lin.
  rewrite Cint_cycTIiso_coprime // dprod_IirrE irr0 cfDprod_cfun1r.
  rewrite (coprime_dvdr _ co_g_w1) // dvdn_cforder.
  rewrite -rmorphX cfDprodl_eq1 -dvdn_cforder; apply/dvdn_cforderP=> x W1x.
  by rewrite -lin_charX // -expg_mod_order (eqnP (order_dvdG W1x)) lin_char1.
have odd_zeta_g: (zeta^\tau1 g == 1 %[mod 2])%C.
  rewrite zeta_g (bigD1 0) //= [w_ 0 0]cycTIirr00 cycTIiso1 cfun1E inE.
  pose eW1 := [pred i : Iirr W1 | conjC_Iirr i < i]%N.
  rewrite (bigID eW1) (reindex_inj (can_inj (@conjC_IirrK _ _))) /=.
  set s1 := \sum_(i | _) _; set s2 := \sum_(i | _) _; suffices ->: s1 = s2.
    by rewrite -mulr2n addrC -(mulr_natr _ 2) eqCmod_addl_mul ?rpred_sum.
  apply/eq_big=> [i | i _].
    rewrite (canF_eq (@conjC_IirrK _ _)) conjC_Iirr0 conjC_IirrK -leqNgt.
    rewrite ltn_neqAle val_eqE -irr_eq1 (eq_sym i) -(inj_eq irr_inj) andbA.
    by rewrite aut_IirrE odd_eq_conj_irr1 ?mFT_odd ?andbb.
  rewrite -{1}conjC_Iirr0 [w_ _ _]cycTIirr_aut -cfAut_cycTIiso.
  by rewrite cfunE conj_Cint ?Zwg.
rewrite norm_Cint_ge1 //; first by rewrite zeta_g rpred_sum.
apply: contraTneq odd_zeta_g => ->.
by rewrite eqCmod_sym /eqCmod subr0 /= (dvdC_nat 2 1).
Qed.

(* This is Peterfalvi (10.7). *)
Let Frob_der1_type2 S :
  S \in 'M -> FTtype S == 2 -> [Frobenius S^`(1) with kernel S`_\F].
Proof.
move: S => L maxL /eqP Ltype2.
have [S pairMS [xdefW [U StypeP]]] := FTtypeP_pair_witness maxM MtypeP.
have [[_ _ maxS] _] := pairMS; rewrite {1}(negPf notMtype2) /= => Stype2 _.
move/(_ L maxL)/implyP; rewrite Ltype2 /= => /setUP[] /imsetP[x0 _ defL].
   by case/eqP/idPn: Ltype2; rewrite defL FTtypeJ.
pose H := (S`_\F)%G; pose HU := (S^`(1))%G.
suffices{L Ltype2 maxL x0 defL}: [Frobenius HU = H ><| U].
  by rewrite defL derJ FcoreJ FrobeniusJker; apply: FrobeniusWker.
have sHHU: H \subset HU by have [_ [_ _ _ /sdprodW/mulG_sub[]]] := StypeP.
pose calT := seqIndD HU S H 1; pose tauS := FT_Dade0 maxS.
have DcalTs: calT = seqIndD HU S S`_\s 1.
  by congr (seqIndD _ _ _ _); apply: val_inj; rewrite /= FTcore_type2.
have notFrobM: ~~ [Frobenius M with kernel M`_\F].
  by apply/existsP=> [[U1 /Frobenius_of_typeF/(typePF_exclusion MtypeP)]].
have{notFrobM} notSsupportM: ~~ [exists x, FTsupports M (S :^ x)].
  apply: contra notFrobM => /'exists_existsP[x [y /and3P[Ay not_sCyM sCySx]]].
  have [_ [_ /(_ y)uMS] /(_ y)] := FTsupport_facts maxM.
  rewrite inE (subsetP (FTsupp_sub0 _)) //= in uMS *.
  rewrite -(eq_uniq_mmax (uMS not_sCyM) _ sCySx) ?mmaxJ // FTtypeJ.
  by case=> // _ _ _ [_ ->].
have{notSsupportM} tiA1M_AS: [disjoint 'A1~(M) & 'A~(S)].
  have notMG_S: gval S \notin M :^: G.
    by apply: contraL Stype2 => /imsetP[x _ ->]; rewrite FTtypeJ.
  by apply: negbNE; have [_ <- _] := FT_Dade_support_disjoint maxM maxS notMG_S.
pose pddS := FT_prDade_hypF maxS StypeP; pose nu := primeTIred pddS.
have{tiA1M_AS} oST phi psi:
  phi \in 'Z[calS, M^#] -> psi \in 'Z[calT, S^#] -> '[phi^\tau, tauS psi] = 0.
- rewrite zcharD1_seqInd // -[seqInd _ _]/calS => Sphi.
  rewrite zcharD1E => /andP[Tpsi psi1_0].
  rewrite -FT_Dade1E ?defA1 ?(zchar_on Sphi) //.
  apply: cfdot_complement (Dade_cfunS _ _) _; rewrite FT_Dade1_supportE setTD.
  rewrite -[tauS _]FT_DadeE ?(cfun_onS _ (Dade_cfunS _ _)) ?FT_Dade_supportE //.
    by rewrite -disjoints_subset disjoint_sym.
  have /subsetD1P[_ /setU1K <-] := FTsupp_sub S; rewrite cfun_onD1 {}psi1_0.
  rewrite -Tpsi andbC -zchar_split {psi Tpsi}(zchar_trans_on _ Tpsi) //.
  move=> psi Tpsi; rewrite zchar_split mem_zchar //=.
  have [s /setDP[_ kerH's] ->] := seqIndP Tpsi.
  by rewrite inE in kerH's; rewrite (prDade_Ind_irr_on pddS).
have notStype5: FTtype S != 5 by rewrite (eqP Stype2).
have [|[_ _ _ _ -> //]] := typeP_reducible_core_cases maxS StypeP notStype5.
case=> t []; set lambda := 'chi_t => T0C'lam lam_1 _.
have{T0C'lam} Tlam: lambda \in calT.
  by apply: seqIndS T0C'lam; rewrite Iirr_kerDS ?sub1G.
have{lam_1} [r [nz_r Tnu_r nu_r_1]]:
  exists r, [/\ r != 0, nu r \in calT & nu r 1%g = lambda 1%g].
- have [_] := typeP_reducible_core_Ind maxS StypeP notStype5.
  set H0 := Ptype_Fcore_kernel _; set nuT := filter _ _; rewrite -/nu.
  case/hasP=> nu_r nuTr _ /(_ _ nuTr)/imageP[r nz_r Dr] /(_ _ nuTr)[nu_r1 _ _].
  have{nuTr} Tnu_r := mem_subseq (filter_subseq _ _) nuTr.
  by exists r; rewrite -Dr nu_r1 (seqIndS _ Tnu_r) // Iirr_kerDS ?sub1G.
pose T2 := [:: lambda; lambda^*; nu r; (nu r)^*]%CF.
have [rmRS scohT]: exists rmRS, subcoherent calT tauS rmRS.
  move: (FTtypeP_coh_base _ _) (FTtypeP_subcoherent maxS StypeP) => RS scohT.
  by rewrite DcalTs; exists RS.
have [lam_irr nu_red]: lambda \in irr S /\ nu r \notin irr S.
  by rewrite mem_irr prTIred_not_irr.
have [lam'nu lams'nu]: lambda != nu r /\ lambda^*%CF != nu r.
  by rewrite -conjC_IirrE !(contraNneq _ nu_red) // => <-; apply: mem_irr.
have [[_ nRT ccT] _ _ _ _] := scohT.
have{ccT} sT2T: {subset T2 <= calT} by apply/allP; rewrite /= ?Tlam ?Tnu_r ?ccT.
have{nRT} uccT2: cfConjC_subset T2 calT.
  split; last 1 [by [] | by apply/allP; rewrite /= !inE !cfConjCK !eqxx !orbT].
  rewrite /uniq /T2 !inE !negb_or -!(inv_eq (@cfConjCK _ S)) !cfConjCK.
  by rewrite lam'nu lams'nu !(hasPn nRT).
have scohT2 := subset_subcoherent scohT uccT2.
have [tau2 cohT2]: coherent T2 S^# tauS.
  apply: (uniform_degree_coherence scohT2); rewrite /= !cfunE nu_r_1 eqxx.
  by rewrite conj_Cnat ?Cnat_irr1 ?eqxx.
have [s nz_s] := has_nonprincipal_irr ntW2; have Smu_s := calSmu nz_s.
pose alpha := mu_ s - d%:R *: zeta; pose beta := nu r - lambda.
have Salpha: alpha \in 'Z[calS, M^#] by rewrite zcharD1_seqInd ?ZmuBzeta.
have [T2lam T2nu_r]: lambda \in T2 /\ nu r \in T2 by rewrite !inE !eqxx !orbT.
have Tbeta: beta \in 'Z[T2, S^#].
  by rewrite zcharD1E rpredB ?mem_zchar //= !cfunE nu_r_1 subrr.
have /eqP/idPn[] := oST _ _ Salpha (zchar_subset sT2T Tbeta).
have [[_ <- //] [_ <- //]] := (cohS, cohT2).
rewrite !raddfB raddfZnat /= subr_eq0 !cfdotBl !cfdotZl.
have [|[dr r'] -> _] := FTtypeP_coherent_TIred _ cohT2 lam_irr T2lam T2nu_r.
  by rewrite -DcalTs.
set sigS := cyclicTIiso _ => /=.
have etaC i j: sigS (cyclicTIirr xdefW j i) = eta_ i j by apply: cycTIisoC.
rewrite !cfdotZr addrC cfdot_sumr big1 => [|j _]; last first.
  by rewrite etaC (coherent_ortho_cycTIiso _ sSS0) ?mem_irr.
rewrite !mulr0 oppr0 add0r rmorph_sign.
have ->: '[zeta^\tau1, tau2 lambda] = 0.
  pose X1 := (zeta :: zeta^*)%CF; pose X2 := (lambda :: lambda^*)%CF.
  pose Y1 := map tau1 X1; pose Y2 := map tau2 X2; have [_ _ ccS] := sSS0.
  have [sX1S sX2T]: {subset X1 <= calS} /\ {subset X2 <= T2}.
    by split; apply/allP; rewrite /= ?inE ?eqxx ?orbT // Szeta ccS.
  have [/(sub_iso_to (zchar_subset sX1S) sub_refl)[Itau1 Ztau1] Dtau1L] := cohS.
  have [/(sub_iso_to (zchar_subset sX2T) sub_refl)[Itau2 Ztau2] Dtau2] := cohT2.
  have Z_Y12: {subset Y1 <= 'Z[irr G]} /\ {subset Y2 <= 'Z[irr G]}.
    by rewrite /Y1 /Y2; split=> ? /mapP[xi /mem_zchar] => [/Ztau1|/Ztau2] ? ->.
  have o1Y12: orthonormal Y1 && orthonormal Y2.
    rewrite !map_orthonormal //.
      by apply: seqInd_conjC_ortho2 Tlam; rewrite ?gFnormal ?mFT_odd.
    by apply: seqInd_conjC_ortho2 Szeta; rewrite ?gFnormal ?mFT_odd ?mem_irr.
  apply: orthonormal_vchar_diff_ortho Z_Y12 o1Y12 _; rewrite -2!raddfB.
  have SzetaBs: zeta - zeta^*%CF \in 'Z[calS, M^#].
    by rewrite zcharD1_seqInd // seqInd_sub_aut_zchar.
  have T2lamBs: lambda - lambda^*%CF \in 'Z[T2, S^#].
    rewrite sub_aut_zchar ?zchar_onG ?mem_zchar ?inE ?eqxx ?orbT //.
    by move=> xi /sT2T/seqInd_vcharW.
  by rewrite Dtau1L // Dtau2 // !Dade1 oST ?(zchar_subset sT2T) ?eqxx.
have [[ds s'] /= -> _] := FTtypeP_coherent_TIred sSS0 cohS irr_zeta Szeta Smu_s.
rewrite mulr0 subr0 !cfdotZl mulrA -signr_addb !cfdot_suml.
rewrite (bigD1 r') //= cfdot_sumr (bigD1 s') //=.
rewrite etaC cfdot_cycTIiso !eqxx big1 => [|j ne_s'_j]; last first.
  by rewrite etaC cfdot_cycTIiso andbC eq_sym (negPf ne_s'_j).
rewrite big1 => [|i ne_i_r']; last first.
  rewrite cfdot_sumr big1 // => j _.
  by rewrite etaC cfdot_cycTIiso (negPf ne_i_r').
rewrite !addr0 mulr1 big1 ?mulr0 ?signr_eq0 // => i _.
by rewrite -etaC cfdotC (coherent_ortho_cycTIiso _ _ cohT2) ?conjC0 -?DcalTs.
Qed.

(* This is the bulk of the proof of Peterfalvi (10.8); however the result     *)
(* will be restated below to avoid the quantification on zeta and tau1.       *)
Lemma FTtype345_noncoherence_main : False.
Proof.
have [S pairMS [xdefW [U StypeP]]] := FTtypeP_pair_witness maxM MtypeP.
have [[_ _ maxS] _] := pairMS; rewrite {1}(negPf notMtype2) /= => Stype2 _ _.
pose H := (S`_\F)%G; pose HU := (S^`(1))%G.
have [[_ hallW2 _ defS] [_ _ nUW2 defHU] _ [_ _ sW1H _ _] _] := StypeP.
have ntU: U :!=: 1%g by have [[]] := compl_of_typeII maxS StypeP Stype2.
pose G01 := [set g : gT | coprime #[g] w1].
pose G0 := ~: 'A~(M) :&: G01; pose G1 := ~: 'A~(M) :\: G01.
pose chi := zeta^\tau1; pose ddAM := FT_Dade_hyp maxM; pose rho := invDade ddAM.
have Suzuki:
   #|G|%:R^-1 * (\sum_(g in ~: 'A~(M)) `|chi g| ^+ 2 - #|~: 'A~(M)|%:R)
         + '[rho chi] - #|'A(M)|%:R / #|M|%:R <= 0.
- pose A_ (_ : 'I_1) := ddAM; pose Atau i := Dade_support (A_ i).
  have tiA i j : i != j -> [disjoint Atau i & Atau j] by rewrite !ord1.
  have Nchi1: '[chi] = 1 by have [[->]] := cohS; rewrite ?mem_zchar ?irrWnorm.
  have:= Dade_cover_inequality tiA Nchi1; rewrite /= !big_ord1 -/rho -addrA.
  by congr (_ * _ + _ <= 0); rewrite FT_Dade_supportE setTD.
have{Suzuki} ub_rho: '[rho chi] <= #|'A(M)|%:R / #|M|%:R + #|G1|%:R / #|G|%:R.
  rewrite addrC -subr_le0 opprD addrCA (ler_trans _ Suzuki) // -addrA.
  rewrite ler_add2r -(cardsID G01 (~: _)) (big_setID G01) -/G0 -/G1 /=.
  rewrite mulrC mulrBr ler_subr_addl -mulrBr natrD addrK.
  rewrite ler_wpmul2l ?invr_ge0 ?ler0n // -sumr_const ler_paddr //.
    by apply: sumr_ge0 => g; rewrite exprn_ge0 ?normr_ge0.
  apply: ler_sum => g; rewrite !inE => /andP[notAg] /(zeta_tau1_coprime notAg).
  by rewrite expr_ge1 ?normr_ge0.
have lb_M'bar: (w1 * 2 <= #|M' / M''|%g.-1)%N.
  suffices ->: w1 = #|W1 / M''|%g.
    rewrite muln2 -ltnS prednK ?cardG_gt0 //.
    by rewrite (ltn_odd_Frobenius_ker frobMbar) ?quotient_odd ?mFT_odd.
  have [_ sW1M _ _ tiM'W1] := sdprod_context defM.
  apply/card_isog/quotient_isog; first exact: subset_trans (der_norm 2 M).
  by apply/trivgP; rewrite -tiM'W1 setSI ?normal_sub.
have lb_rho: 1 - w1%:R / #|M'|%:R <= '[rho chi].
  have cohS_A: coherent_with calS M^# (Dade ddAM) tau1.
    have [Itau1 _] := cohS; split=> // phi; rewrite zcharD1_seqInd // => Sphi.
    by rewrite Dtau1 // FT_DadeE // defA (zchar_on Sphi).
  rewrite {ub_rho}/rho [w1](index_sdprod defM); rewrite defA in (ddAM) cohS_A *.
  have [||_ [_ _ [] //]] := Dade_Ind1_sub_lin cohS_A _  irr_zeta Szeta.
  - by apply: seqInd_nontrivial Szeta; rewrite ?mem_irr ?mFT_odd.
  - by rewrite -(index_sdprod defM).
  rewrite -(index_sdprod defM) ler_pdivl_mulr ?ltr0n // -natrM.
  rewrite -leC_nat in lb_M'bar; apply: ler_trans lb_M'bar _.
  rewrite ler_subr_addl -mulrS prednK ?cardG_gt0 // leC_nat.
  by rewrite dvdn_leq ?dvdn_quotient.
have{lb_rho ub_rho}: 1 - #|G1|%:R/ #|G|%:R - w1%:R^-1 < w1%:R / #|M'|%:R :> algC.
  rewrite -addrA -opprD ltr_subl_addr -ltr_subl_addl.
  apply: ler_lt_trans (ler_trans lb_rho ub_rho) _; rewrite addrC ltr_add2l.
  rewrite ltr_pdivr_mulr ?gt0CG // mulrC -(sdprod_card defM) natrM.
  by rewrite mulfK ?neq0CG // defA ltC_nat (cardsD1 1%g M') group1.
have frobHU: [Frobenius HU with kernel H] by apply: Frob_der1_type2.
have tiH: normedTI H^# G S.
  by have [_ _] := FTtypeII_ker_TI maxS Stype2; rewrite FTsupp1_type2.
have sG1_HVG: G1 \subset class_support H^# G :|: class_support V G.
  apply/subsetP=> x; rewrite !inE coprime_has_primes ?cardG_gt0 // negbK.
  case/andP=> /hasP[p W1p]; rewrite /= mem_primes => /and3P[p_pr _ p_dv_x] _.
  have [a x_a a_p] := Cauchy p_pr p_dv_x.
  have nta: a != 1%g by rewrite -order_gt1 a_p prime_gt1.
  have ntx: x != 1%g by apply: contraTneq x_a => ->; rewrite /= cycle1 inE.
  have cxa: a \in 'C[x] by rewrite -cent_cycle (subsetP (cycle_abelian x)).
  have hallH: \pi(H).-Hall(G) H by apply: Hall_pi; have [] := FTcore_facts maxS.
  have{a_p} p_a: p.-elt a by rewrite /p_elt a_p pnat_id.
  have piHp: p \in \pi(H) by rewrite (piSg _ W1p).
  have [y _ Hay] := Hall_pJsub hallH piHp (subsetT _) p_a.
  do [rewrite -cycleJ cycle_subG; set ay := (a ^ y)%g] in Hay.
  rewrite -[x](conjgK y); set xy := (x ^ y)%g.
  have caxy: xy \in 'C[ay] by rewrite cent1J memJ_conjg cent1C.
  have [ntxy ntay]: xy != 1%g /\ ay != 1%g by rewrite !conjg_eq1.
  have Sxy: xy \in S.
    have H1ay: ay \in H^# by apply/setD1P.
    by rewrite (subsetP (cent1_normedTI tiH H1ay)) ?setTI.
  have [HUxy | notHUxy] := boolP (xy \in HU).
    rewrite memJ_class_support ?inE ?ntxy //=.
    have [_ _ _ regHUH] := Frobenius_kerP frobHU.
    by rewrite (subsetP (regHUH ay _)) // inE ?HUxy // inE ntay.
  suffices /imset2P[xyz z Vxzy _ ->]: xy \in class_support V S.
    by rewrite -conjgM orbC memJ_class_support.
  rewrite /V setUC -(FTsupp0_typeP maxS StypeP) !inE Sxy.
  rewrite andb_orr andNb (contra (subsetP _ _) notHUxy) /=; last first.
    by apply/bigcupsP=> z _; rewrite (eqP Stype2) setDE -setIA subsetIl.
  have /Hall_pi hallHU: Hall S HU by rewrite (sdprod_Hall defS).
  rewrite (eqP Stype2) -(mem_normal_Hall hallHU) ?gFnormal // notHUxy.
  have /mulG_sub[sHHU _] := sdprodW defHU.
  rewrite (contra (fun p'xy => pi'_p'group p'xy (piSg sHHU piHp))) //.
  by rewrite pgroupE p'natE // cycleJ cardJg p_dv_x.
have ub_G1: #|G1|%:R / #|G|%:R <= #|H|%:R / #|S|%:R + #|V|%:R / #|W|%:R :> algC.
  rewrite ler_pdivr_mulr ?ltr0n ?cardG_gt0 // mulrC mulrDr !mulrA.
  rewrite ![_ * _ / _]mulrAC -!natf_indexg ?subsetT //= -!natrM -natrD ler_nat.
  apply: leq_trans (subset_leq_card sG1_HVG) _.
  rewrite cardsU (leq_trans (leq_subr _ _)) //.
  have unifJG B C: C \in B :^: G -> #|C| = #|B|.
    by case/imsetP=> z _ ->; rewrite cardJg.
  have oTI := card_uniform_partition (unifJG _) (partition_class_support _ _).
  have{tiH} [ntH tiH /eqP defNH] := and3P tiH.
  have [_ _ /and3P[ntV tiV /eqP defNV]] := ctiWG.
  rewrite !oTI // !card_conjugates defNH defNV /= leq_add2r ?leq_mul //.
  by rewrite subset_leq_card ?subsetDl.
rewrite ler_gtF // addrAC ler_subr_addl -ler_subr_addr (ler_trans ub_G1) //.
rewrite -(sdprod_card defS) -(sdprod_card defHU) addrC.
rewrite -mulnA !natrM invfM mulVKf ?natrG_neq0 // -/w1 -/w2.
have sW12_W: W1 :|: W2 \subset W by rewrite -(dprodWY defW) sub_gen.
rewrite cardsD (setIidPr sW12_W) natrB ?subset_leq_card // mulrBl.
rewrite divff ?natrG_neq0 // -!addrA ler_add2l.
rewrite cardsU -(dprod_card defW) -/w1 -/w2; have [_ _ _ ->] := dprodP defW.
rewrite cards1 natrB ?addn_gt0 ?cardG_gt0 // addnC natrD -addrA mulrDl mulrBl.
rewrite {1}mulnC !natrM !invfM !mulVKf ?natrG_neq0 // opprD -addrA ler_add2l.
rewrite mul1r -{1}[_^-1]mul1r addrC ler_oppr [- _]opprB -!mulrBl.
rewrite -addrA -opprD ler_pdivl_mulr; last by rewrite natrG_gt0.
apply: ler_trans (_ : 1 - (3%:R^-1 + 7%:R^-1) <= _); last first.
  rewrite ler_add2l ler_opp2.
  rewrite ler_add // lef_pinv ?qualifE ?gt0CG ?ltr0n ?ler_nat //.
  have notStype5: FTtype S != 5 by rewrite (eqP Stype2).
  have frobUW2 := Ptype_compl_Frobenius maxS StypeP notStype5.
  apply: leq_ltn_trans (ltn_odd_Frobenius_ker frobUW2 (mFT_odd _)).
  by rewrite (leq_double 3).
apply: ler_trans (_ : 2%:R^-1 <= _); last by rewrite -!CratrE; compute.
rewrite mulrAC ler_pdivr_mulr 1?gt0CG // ler_pdivl_mull ?ltr0n //.
rewrite -!natrM ler_nat mulnA -(Lagrange (normal_sub nsM''M')) mulnC leq_mul //.
  by rewrite subset_leq_card //; have [_ _ _ []] := MtypeP.
by rewrite -card_quotient ?normal_norm // mulnC -(prednK (cardG_gt0 _)) leqW.
Qed.

End NonCoherence.

(* This is Peterfalvi (10.9). *)
Lemma FTtype345_Dade_bridge0 :
    (w1 < w2)%N ->
  {chi | [/\ (mu_ 0 - zeta)^\tau = \sum_i eta_ i 0 - chi,
             chi \in 'Z[irr G], '[chi] = 1
           & forall i j, '[chi, eta_ i j] = 0]}.
Proof.
move=> w1_lt_w2; set psi := mu_ 0 - zeta; pose Wsig := map sigma (irr W).
have [X wsigX [chi [DpsiG _ o_chiW]]] := orthogonal_split Wsig psi^\tau.
exists (- chi); rewrite opprK rpredN cfnormN.
have o_chi_w i j: '[chi, eta_ i j] = 0.
  by rewrite (orthoPl o_chiW) ?map_f ?mem_irr.
have [Isigma Zsigma] := cycTI_Zisometry ctiWG.
have o1Wsig: orthonormal Wsig by rewrite map_orthonormal ?irr_orthonormal.
have [a_ Da defX] := orthonormal_span o1Wsig wsigX.
have{Da} Da i j: a_ (eta_ i j) = '[psi^\tau, eta_ i j].
  by rewrite DpsiG cfdotDl o_chi_w addr0 Da.
have sumX: X = \sum_i \sum_j a_ (eta_ i j) *: eta_ i j.
  rewrite pair_bigA defX big_map (big_nth 0) size_tuple big_mkord /=.
  rewrite (reindex (dprod_Iirr defW)) /=.
    by apply: eq_bigr => [[i j] /= _]; rewrite -tnth_nth.
  by exists (inv_dprod_Iirr defW) => ij; rewrite (inv_dprod_IirrK, dprod_IirrK).
have Zpsi: psi \in 'Z[irr M].
  by rewrite rpredB ?irr_vchar ?(mem_zchar irr_zeta) ?char_vchar ?prTIred_char.
have{Zpsi} M'psi: psi \in 'Z[irr M, M'^#].
  by rewrite -defA zchar_split Zpsi mu0Bzeta_on.
have A0psi: psi \in 'CF(M, 'A0(M)).
  by apply: cfun_onS (zchar_on M'psi); rewrite defA0 subsetUl.
have a_00: a_ (eta_ 0 0) = 1.
  rewrite Da [w_ 0 0](cycTIirr00 defW) [sigma 1]cycTIiso1.
  rewrite Dade_reciprocity // => [|x _ y _]; last by rewrite !cfun1E !inE.
  rewrite rmorph1 /= -(prTIirr00 ptiWM) -/(mu2_ 0 0) cfdotC.
  by rewrite cfdotBr o_mu2_zeta subr0 cfdot_prTIirr_red rmorph1.
have n2psiG: '[psi^\tau] = w1.+1%:R.
  rewrite Dade_isometry // cfnormBd ?o_mu_zeta //.
  by rewrite cfnorm_prTIred irrWnorm // -/w1 mulrSr.
have psiG_V0 x: x \in V -> psi^\tau x = 0.
  move=> Vx; rewrite Dade_id ?defA0; last first.
    by rewrite inE orbC mem_class_support.
  rewrite (cfun_on0 (zchar_on M'psi)) // -defA.
  suffices /setDP[]: x \in 'A0(M) :\: 'A(M) by [].
  by rewrite (FTsupp0_typeP maxM MtypeP) // mem_class_support.
have ZpsiG: psi^\tau \in 'Z[irr G].
  by rewrite Dade_vchar // zchar_split (zcharW M'psi).
have n2psiGsum: '[psi^\tau] = \sum_i \sum_j `|a_ (eta_ i j)| ^+ 2 + '[chi].
  rewrite DpsiG addrC cfnormDd; last first.
    by rewrite (span_orthogonal o_chiW) ?memv_span1.
  rewrite addrC defX cfnorm_sum_orthonormal // big_map pair_bigA; congr (_ + _).
  rewrite big_tuple /= (reindex (dprod_Iirr defW)) //.
  by exists (inv_dprod_Iirr defW) => ij; rewrite (inv_dprod_IirrK, dprod_IirrK).
have NCpsiG: (cyclicTI_NC ctiWG psi^\tau < 2 * minn w1 w2)%N.
  apply: (@leq_ltn_trans w1.+1); last first.
    by rewrite /minn w1_lt_w2 mul2n -addnn (leq_add2r w1 2) cardG_gt1.
  pose z_a := [pred ij | a_ (eta_ ij.1 ij.2) == 0].
  have ->: cyclicTI_NC ctiWG psi^\tau = #|[predC z_a]|.
    by apply: eq_card => ij; rewrite !inE -Da.
  rewrite -leC_nat -n2psiG n2psiGsum ler_paddr ?cfnorm_ge0 // pair_bigA.
  rewrite (bigID z_a) big1 /= => [|ij /eqP->]; last by rewrite normCK mul0r.
  rewrite add0r -sumr_const ler_sum // => [[i j] nz_ij].
  by rewrite expr_ge1 ?norm_Cint_ge1 // Da Cint_cfdot_vchar ?Zsigma ?irr_vchar.
have nz_psiG00: '[psi^\tau, eta_ 0 0] != 0 by rewrite -Da a_00 oner_eq0.
have [a_i|a_j] := small_cycTI_NC psiG_V0 NCpsiG nz_psiG00.
  have psiGi: psi^\tau = \sum_i eta_ i 0 + chi.
    rewrite DpsiG sumX; congr (_ + _); apply: eq_bigr => i _.
    rewrite big_ord_recl /= Da a_i -Da a_00 mul1r scale1r.
    by rewrite big1 ?addr0 // => j1 _; rewrite Da a_i mul0r scale0r.
  split=> // [||i j]; last by rewrite cfdotNl o_chi_w oppr0.
    rewrite -(canLR (addKr _) psiGi) rpredD // rpredN rpred_sum // => j _.
    by rewrite Zsigma ?irr_vchar.
  apply: (addrI w1%:R); rewrite -mulrSr -n2psiG n2psiGsum; congr (_ + _).
  rewrite -nirrW1 // -sumr_const; apply: eq_bigr => i _.
  rewrite big_ord_recl /= Da a_i -Da a_00 mul1r normr1.
  by rewrite expr1n big1 ?addr0 // => j1 _; rewrite Da a_i normCK !mul0r.
suffices /idPn[]: '[psi^\tau] >= w2%:R.
  rewrite odd_geq /= ?uphalf_half mFT_odd //= in w1_lt_w2.
  by rewrite n2psiG leC_nat -ltnNge odd_geq ?mFT_odd.
rewrite n2psiGsum exchange_big /= ler_paddr ?cfnorm_ge0 //.
rewrite -nirrW2 -sumr_const; apply: ler_sum => i _.
rewrite big_ord_recl /= Da a_j -Da a_00 mul1r normr1.
by rewrite expr1n big1 ?addr0 // => j1 _; rewrite Da a_j normCK !mul0r.
Qed.

Local Notation H := M'.
Local Notation "` 'H'" := `M' (at level 0) : group_scope.
Local Notation H' := M''.
Local Notation "` 'H''" := `M'' (at level 0) : group_scope.

(* This is the bulk of the proof of Peterfalvi, Theorem (10.10); as with      *)
(* (10.8), it will be restated below in order to remove dependencies on zeta, *)
(* U_M and W1.                                                                *)
Lemma FTtype5_exclusion_main : FTtype M != 5.
Proof.
apply/negP=> Mtype5.
suffices [tau1]: coherent calS M^# tau by case/FTtype345_noncoherence_main.
have [[_ U_M_1] MtypeV] := compl_of_typeV maxM MtypeP Mtype5.
have [_ [_ _ _ defH] _ [_ _ _ sW2H' _] _] := MtypeP.
have{U_M_1 defH} defMF: M`_\F = H by rewrite /= -defH U_M_1 sdprodg1.
have nilH: nilpotent `H by rewrite -defMF Fcore_nil.
have scohS := subset_subcoherent scohS0 sSS0.
have [|//|[[_]]] := (non_coherent_chief nsM'M (nilpotent_sol nilH) scohS) 1%G.
  split; rewrite ?mFT_odd ?normal1 ?sub1G ?quotient_nil //.
  by rewrite joingG1 (FrobeniusWker frobMbar).
rewrite /= joingG1 -(index_sdprod defM) /= -/w1 -[H^`(1)%g]/`H' => ubHbar [p[]].
rewrite -(isog_abelian (quotient1_isog H)) -(isog_pgroup p (quotient1_isog H)).
rewrite subn1 => pH not_cHH /negP not_w1_dv_p'1.
have ntH: H :!=: 1%g by apply: contraNneq not_cHH => ->; apply: abelian1.
have [sH'H nH'H] := andP nsM''M'; have sW2H := subset_trans sW2H' sH'H.
have def_w2: w2 = p by apply/eqP; have:= pgroupS sW2H pH; rewrite pgroupE pnatE.
have [p_pr _ [e oH]] := pgroup_pdiv pH ntH.
rewrite -/w1 /= defMF oH pi_of_exp {e oH}// /pi_of primes_prime // in MtypeV.
have [tiHG | [_ /predU1P[->[]|]]// | [_ /predU1P[->|//] [oH w1p1 _]]] := MtypeV.
  suffices [tau1 [Itau1 Dtau1]]: coherent (seqIndD H M H 1) M^# 'Ind[G].
    exists tau1; split=> // phi Sphi; rewrite {}Dtau1 //.
    rewrite zcharD1_seqInd // -subG1 -setD_eq0 -defA in Sphi tiHG ntH.
    by have Aphi := zchar_on Sphi; rewrite -FT_DadeE // Dade_Ind.
  apply: (@Sibley_coherence _ [set:_] M H W1); first by rewrite mFT_odd.
  right; exists W2 => //; exists 'A0(M), W, defW.
  by rewrite -defA -{2}(group_inj defMs).
rewrite pcore_pgroup_id // in oH.
have esH: extraspecial H.
  by apply: (p3group_extraspecial pH); rewrite // oH pfactorK.
have oH': #|H'| = p.
  by rewrite -(card_center_extraspecial pH esH); have [[_ <-]] := esH.
have defW2: W2 :=: H' by apply/eqP; rewrite eqEcard sW2H' oH' -def_w2 /=.
have iH'H: #|H : H'|%g = (p ^ 2)%N by rewrite -divgS // oH oH' mulKn ?prime_gt0.
have w1_gt0: (0 < w1)%N by apply: cardG_gt0.
(* This is step (10.10.1). *)
have{ubHbar} [def_p_w1 w1_lt_w2]: (p = 2 * w1 - 1 /\ w1 < w2)%N.
  have /dvdnP[k def_p]: 2 * w1 %| p.+1.
    by rewrite Gauss_dvd ?coprime2n ?mFT_odd ?dvdn2 //= -{1}def_w2 mFT_odd.
  suffices k1: k = 1%N.
    rewrite k1 mul1n in def_p; rewrite -ltn_double -mul2n -def_p -addn1 addnK.
    by rewrite -addnS -addnn def_w2 leq_add2l prime_gt1.
  have [k0 | k_gt0] := posnP k; first by rewrite k0 in def_p.
  apply/eqP; rewrite eqn_leq k_gt0 andbT -ltnS -ltn_double -mul2n.
  rewrite -[(2 * k)%N]prednK ?muln_gt0 // ltnS -ltn_sqr 3?leqW //=.
  rewrite -subn1 sqrn_sub ?muln_gt0 // expnMn muln1 mulnA ltnS leq_subLR.
  rewrite addn1 addnS ltnS -mulnSr leq_pmul2l // -(leq_subLR _ 1).
  rewrite (leq_trans (leq_pmulr _ w1_gt0)) // -(leq_pmul2r w1_gt0).
  rewrite -mulnA mulnBl mul1n -2!leq_double -!mul2n mulnA mulnBr -!expnMn.
  rewrite -(expnMn 2 _ 2) mulnCA -def_p -addn1 leq_subLR sqrnD muln1.
  by rewrite (addnC p) mulnDr addnA leq_add2r addn1 addnS -iH'H.
(* This is step (10.10.2). *)
pose S1 := seqIndD H M H H'.
have sS1S: {subset S1 <= calS} by apply: seqIndS; rewrite Iirr_kerDS ?sub1G.
have irrS1: {subset S1 <= irr M}.
  move=> _ /seqIndP[s /setDP[kerH' ker'H] ->]; rewrite !inE in kerH' ker'H.
  rewrite -(quo_IirrK _ kerH') // mod_IirrE // cfIndMod // cfMod_irr //.
  rewrite (irr_induced_Frobenius_ker (FrobeniusWker frobMbar)) //.
  by rewrite quo_Iirr_eq0 // -subGcfker.
have S1w1: {in S1, forall xi : 'CF(M), xi 1%g = w1%:R}.
  move=> _ /seqIndP[s /setDP[kerH' _] ->]; rewrite !inE in kerH'.
  by rewrite cfInd1 // -(index_sdprod defM) lin_char1 ?mulr1 // lin_irr_der1.
have sS10: cfConjC_subset S1 calS0.
  by apply: seqInd_conjC_subset1; rewrite /= defMs.
pose S2 := [seq mu_ j | j in predC1 0].
have szS2: size S2 = p.-1.
  by rewrite -def_w2 size_map -cardE cardC1 card_Iirr_abelian ?cyclic_abelian.
have uS2: uniq S2 by apply/dinjectiveP; apply: in2W (prTIred_inj pddM).
have redS2: {subset S2 <= [predC irr M]}.
  by move=> _ /imageP[j _ ->]; apply: (prTIred_not_irr pddM).
have sS2S: {subset S2 <= calS} by move=> _ /imageP[j /calSmu Smu_j ->].
have S1'2: {subset S2 <= [predC S1]}.
  by move=> xi /redS2; apply: contra (irrS1 _).
have w1_dv_p21: w1 %| p ^ 2 - 1 by rewrite (subn_sqr p 1) addn1 dvdn_mull.
have [j nz_j] := has_nonprincipal_irr ntW2.
have [Dmu2_1 Ddelta_ lt1d Nn] := FTtype345_constants.
have{lt1d} [defS szS1 Dd Ddel Dn]:
        [/\ perm_eq calS (S1 ++ S2), size S1 = (p ^ 2 - 1) %/ w1,
            d = p, delta = -1 & n = 2%:R].
- pose X_ (S0 : seq 'CF(M)) := [set s | 'Ind[M, H] 'chi_s \in S0].
  pose sumX_ cS0 := \sum_(s in X_ cS0) 'chi_s 1%g ^+ 2.
  have defX1: X_ S1 = Iirr_kerD H H H'.
    by apply/setP=> s; rewrite !inE mem_seqInd // !inE.
  have defX: X_ calS = Iirr_kerD H H 1%g.
    by apply/setP=> s; rewrite !inE mem_seqInd ?normal1 //= !inE.
  have sumX1: sumX_ S1 = (p ^ 2)%:R - 1.
    by rewrite /sumX_ defX1 sum_Iirr_kerD_square // iH'H indexgg mul1r.
  have ->: size S1 = (p ^ 2 - 1) %/ w1.
    apply/eqP; rewrite eqn_div // -eqC_nat mulnC [w1](index_sdprod defM).
    rewrite (size_irr_subseq_seqInd _ (subseq_refl S1)) //.
    rewrite natrB ?expn_gt0 ?prime_gt0 // -sumr_const -sumX1.
    apply/eqP/esym/eq_bigr => s.
    by rewrite defX1 !inE -lin_irr_der1 => /and3P[_ _ /eqP->]; rewrite expr1n.
  have oX2: #|X_ S2| = p.-1.
    by rewrite -(size_red_subseq_seqInd_typeP MtypeP uS2 sS2S).
  have sumX2: (p ^ 2 * p.-1)%:R <= sumX_ S2 ?= iff (d == p).
    rewrite /sumX_ (eq_bigr (fun _ => d%:R ^+ 2)) => [|s]; last first.
      rewrite inE => /imageP[j1 nz_j1 Dj1]; congr (_ ^+ 2).
      apply: (mulfI (neq0CiG M H)); rewrite -cfInd1 // -(index_sdprod defM).
      by rewrite Dj1 (prTIred_1 pddM) Dmu2_1.
    rewrite sumr_const oX2 mulrnA (mono_lerif (ler_pmuln2r _)); last first.
      by rewrite -def_w2 -(subnKC w2gt2).
    rewrite natrX (mono_in_lerif ler_sqr) ?rpred_nat // eq_sym lerif_nat.
    apply/leqif_eq; rewrite dvdn_leq 1?ltnW //.
    have: (mu2_ 0 j 1%g %| (p ^ 3)%N)%C.
      by rewrite -(cfRes1 H) cfRes_prTIirr -oH dvd_irr1_cardG.
    rewrite Dmu2_1 // dvdC_nat => /dvdn_pfactor[//|[_ d1|e _ ->]].
      by rewrite d1 in lt1d.
    by rewrite expnS dvdn_mulr.
  pose S3 := filter [predC S1 ++ S2] calS.
  have sumX3: 0 <= sumX_ S3 ?= iff nilp S3.
    rewrite /sumX_; apply/lerifP.
    have [-> | ] := altP nilP; first by rewrite big_pred0 // => s; rewrite !inE.
    rewrite -lt0n -has_predT => /hasP[xi S3xi _].
    have /seqIndP[s _ Dxi] := mem_subseq (filter_subseq _ _) S3xi.
    rewrite (bigD1 s) ?inE -?Dxi //= ltr_spaddl ?sumr_ge0 // => [|s1 _].
      by rewrite exprn_gt0 ?irr1_gt0.
    by rewrite ltrW ?exprn_gt0 ?irr1_gt0.
  have [_ /esym] := lerif_add sumX2 sumX3.
  have /(canLR (addKr _)) <-: sumX_ calS = sumX_ S1 + (sumX_ S2 + sumX_ S3).
    rewrite [sumX_ _](big_setID (X_ S1)); congr (_ + _).
      by apply: eq_bigl => s; rewrite !inE andb_idl // => /sS1S.
    rewrite (big_setID (X_ S2)); congr (_ + _); apply: eq_bigl => s.
      by rewrite !inE andb_idl // => S2s; rewrite [~~ _]S1'2 ?sS2S.
    by rewrite !inE !mem_filter /= mem_cat orbC negb_or andbA.
  rewrite sumX1 /sumX_ defX sum_Iirr_kerD_square ?sub1G ?normal1 // indexgg.
  rewrite addr0 mul1r indexg1 oH opprD addrACA addNr addr0 addrC.
  rewrite (expnSr p 2) -[p in (_ ^ 2 * p)%:R - _]prednK ?prime_gt0 // mulnSr.
  rewrite natrD addrK eqxx => /andP[/eqP Dd /nilP S3nil].
  have uS12: uniq (S1 ++ S2).
    by rewrite cat_uniq seqInd_uniq uS2 andbT; apply/hasPn.
  rewrite uniq_perm_eq ?seqInd_uniq {uS12}// => [|xi]; last first.
    apply/idP/idP; apply: allP xi; last by rewrite all_cat !(introT allP _).
    by rewrite -(canLR negbK (has_predC _ _)) has_filter -/S3 S3nil.
  have: (w1 %| d%:R - delta)%C.
    by rewrite unfold_in pnatr_eq0 eqn0Ngt w1_gt0 rpred_Cnat.
  rewrite /n Dd def_p_w1 /delta; case: (Idelta _) => [_|/idPn[] /=].
    by rewrite opprK -(natrD _ _ 1) subnK ?muln_gt0 // natrM mulfK ?neq0CG.
  rewrite mul2n -addnn -{1}(subnKC (ltnW w1gt2)) !addSn mulrSr addrK dvdC_nat.
  by rewrite add0n dvdn_addl // -(subnKC w1gt2) gtnNdvd // leqW.
have scohS1 := subset_subcoherent scohS0 sS10.
have o1S1: orthonormal S1.
  rewrite orthonormalE andbC; have [_ _ -> _ _] := scohS1.
  by apply/allP=> xi /irrS1/irrP[t ->]; rewrite /= cfnorm_irr.
have [tau1 cohS1]: coherent S1 M^# tau.
  apply: uniform_degree_coherence scohS1 _; apply: all_pred1_constant w1%:R _ _.
  by rewrite all_map; apply/allP=> xi /S1w1/= ->.
have [[Itau1 Ztau1] Dtau1] := cohS1.
have o1S1tau: orthonormal (map tau1 S1) by apply: map_orthonormal.
have S1zeta: zeta \in S1.
  by have:= Szeta; rewrite (perm_eq_mem defS) mem_cat => /orP[//|/redS2/negP].
(* This is the main part of step 10.10.3; as the definition of alpha_ remains *)
(* valid we do not need to reprove alpha_on.                                  *)
have Dalpha i (al_ij := alpha_ i j) :
  al_ij^\tau = delta *: (eta_ i j - eta_ i 0) - n *: tau1 zeta.
- have [Y S1_Y [X [Dal_ij _ oXY]]] := orthogonal_split (map tau1 S1) al_ij^\tau.
  have [a_ Da_ defY] := orthonormal_span o1S1tau S1_Y.
  have oXS1 lam : lam \in S1 -> '[X, tau1 lam] = 0.
    by move=> S1lam; rewrite (orthoPl oXY) ?map_f.
  have{Da_} Da_ lam : lam \in S1 -> a_ (tau1 lam) = '[al_ij^\tau, tau1 lam].
    by move=> S1lam; rewrite Dal_ij cfdotDl oXS1 // addr0 Da_.
  pose a := n + a_ (tau1 zeta); have [_ oS1S1] := orthonormalP o1S1.
  have Da_z: a_ (tau1 zeta) = - n + a by rewrite addKr.
  have Za: a \in Cint.
    rewrite rpredD ?Dn ?rpred_nat // Da_ // Cint_cfdot_vchar ?Zalpha_tau //=.
    by rewrite Ztau1 ?mem_zchar.
  have Da_z' lam: lam \in S1 -> lam != zeta -> a_ (tau1 lam) = a.
    move=> S1lam zeta'lam; apply: canRL (subrK _) _.
    rewrite !Da_ // -cfdotBr -raddfB.
    have S1dlam: lam - zeta \in 'Z[S1, M^#].
      by rewrite zcharD1E rpredB ?mem_zchar //= !cfunE !S1w1 ?subrr.
    rewrite Dtau1 // Dade_isometry ?alpha_on ?tauM' //; last first.
      by rewrite -zcharD1_seqInd ?(zchar_subset sS1S).
    have o_mu2_lam k: '[mu2_ i k, lam] = 0 by rewrite o_mu2_irr ?sS1S ?irrS1.
    rewrite !cfdotBl !cfdotZl !cfdotBr !o_mu2_lam !o_mu2_zeta !(subr0, mulr0).
    by rewrite irrWnorm ?oS1S1 // eq_sym (negPf zeta'lam) !add0r mulrN1 opprK.
  have lb_n2alij: (a - n) ^+ 2 + (size S1 - 1)%:R * a ^+ 2 <= '[al_ij^\tau].
    rewrite Dal_ij cfnormDd; last first.
      by rewrite cfdotC (span_orthogonal oXY) ?rmorph0 // memv_span1.
    rewrite ler_paddr ?cfnorm_ge0 // defY cfnorm_sum_orthonormal //.
    rewrite (big_rem (tau1 zeta)) ?map_f //= ler_eqVlt; apply/predU1P; left.
    congr (_ + _).
      by rewrite Da_z addrC Cint_normK 1?rpredD // rpredN Dn rpred_nat.
    rewrite (eq_big_seq (fun _ => a ^+ 2)) => [|tau1lam]; last first.
      rewrite rem_filter ?free_uniq ?orthonormal_free // filter_map.
      case/mapP=> lam; rewrite mem_filter /= andbC => /andP[S1lam].
      rewrite (inj_in_eq (Zisometry_inj Itau1)) ?mem_zchar // => zeta'lam ->.
      by rewrite Da_z' // Cint_normK.
    rewrite big_tnth sumr_const card_ord size_rem ?map_f // size_map.
    by rewrite mulr_natl subn1.
  have{lb_n2alij} ub_a2: (size S1)%:R * a ^+ 2 <= 2%:R * a * n + 2%:R.
    rewrite norm_alpha // addrC sqrrB !addrA ler_add2r in lb_n2alij.
    rewrite mulr_natl -mulrSr ler_subl_addl subn1 in lb_n2alij.
    by rewrite -mulrA !mulr_natl; case: (S1) => // in S1zeta lb_n2alij *.
  have{ub_a2} ub_8a2: 8%:R * a ^+ 2 <= 4%:R * a + 2%:R.
    rewrite mulrAC Dn -natrM in ub_a2; apply: ler_trans ub_a2.
    rewrite -Cint_normK // ler_wpmul2r ?exprn_ge0 ?normr_ge0 // leC_nat szS1. 
    rewrite (subn_sqr p 1) def_p_w1 subnK ?muln_gt0 // mulnA mulnK // mulnC.
    by rewrite -subnDA -(mulnBr 2 _ 1%N) mulnA (@leq_pmul2l 4 2) ?ltn_subRL.
  have Z_4a1: 4%:R * a - 1%:R \in Cint by rewrite rpredB ?rpredM ?rpred_nat.
  have{ub_8a2} ub_4a1: `|4%:R * a - 1| < 3%:R.
    rewrite -ltr_sqr ?rpred_nat ?qualifE ?normr_ge0 // -natrX Cint_normK //.
    rewrite sqrrB1 exprMn -natrX -mulrnAl -mulrnA (natrD _ 8 1) ltr_add2r.
    rewrite (natrM _ 2 4) (natrM _ 2 8) -!mulrA -mulrBr ltr_pmul2l ?ltr0n //.
    by rewrite ltr_subl_addl (ler_lt_trans ub_8a2) // ltr_add2l ltr_nat.
  have{ub_4a1} a0: a = 0.
    apply: contraTeq ub_4a1 => a_nz; have:= norm_Cint_ge1 Za a_nz.
    rewrite real_ltr_norml ?real_ler_normr ?Creal_Cint //; apply: contraL.
    case/andP; rewrite ltr_subl_addr -(natrD _ 3 1) gtr_pmulr ?ltr0n //.
    rewrite ltr_oppl opprB -mulrN => /ltr_le_trans/=/(_ _ (leC_nat 3 5)).
    by rewrite (natrD _ 1 4) ltr_add2l gtr_pmulr ?ltr0n //; do 2!move/ltr_geF->.
  apply: (def_tau_alpha cohS1 sS10 nz_j S1zeta).
  by rewrite -Da_ // Da_z a0 addr0.
have o_eta__zeta i j1: '[tau1 zeta, eta_ i j1] = 0.
   by rewrite (coherent_ortho_cycTIiso _ sS10 cohS1) ?mem_irr.
(* This is step (10.4), the final one. *)
have Dmu0zeta: (mu_ 0 - zeta)^\tau = \sum_i eta_ i 0 - tau1 zeta.
  have A0mu0tau: mu_ 0 - zeta \in 'CF(M, 'A0(M)).
    rewrite /'A0(M) defA; apply: (cfun_onS (subsetUl _ _)).
    rewrite cfun_onD1 [mu_ 0](prTIred0 pddM) !cfunE zeta1w1 cfuniE // group1.
    by rewrite mulr1 subrr rpredB ?rpredZnat ?cfuni_on ?(seqInd_on _ Szeta) /=.
  have [chi [Dmu0 Zchi n1chi o_chi_w]] := FTtype345_Dade_bridge0 w1_lt_w2.
  have dirr_chi: chi \in dirr G by rewrite dirrE Zchi n1chi /=.
  have dirr_zeta: tau1 zeta \in dirr G.
    by rewrite dirrE Ztau1 ?Itau1 ?mem_zchar //= irrWnorm.
  have: '[(alpha_ 0 j)^\tau, (mu_ 0 - zeta)^\tau] == - delta + n.
    rewrite Dade_isometry ?alpha_on // !cfdotBl !cfdotZl !cfdotBr.
    rewrite !o_mu2_zeta 2!cfdot_prTIirr_red (negPf nz_j) cfdotC o_mu_zeta.
    by rewrite eqxx irrWnorm // conjC0 !(subr0, add0r) mulr1 mulrN1 opprK.
  rewrite Dalpha // Dmu0 !{1}(cfdotBl, cfdotZl) !cfdotBr 2!{1}(cfdotC _ chi).
  rewrite !o_chi_w conjC0 !cfdot_sumr big1 => [|i]; first last.
    by rewrite (cfdot_cycTIiso pddM) (negPf nz_j) andbF.
  rewrite (bigD1 0) //= cfdot_cycTIiso big1 => [|i nz_i]; first last.
    by rewrite cfdot_cycTIiso eq_sym (negPf nz_i).
  rewrite big1 // !subr0 !add0r addr0 mulrN1 mulrN opprK (can_eq (addKr _)).
  rewrite {2}Dn -mulr_natl Dn (inj_eq (mulfI _)) ?pnatr_eq0 //.
  by rewrite cfdot_dirr_eq1 // => /eqP->.
have [] := uniform_prTIred_coherent pddM nz_j; rewrite -/sigma.
have ->: uniform_prTIred_seq pddM j = S2.
  congr (map _ _); apply: eq_enum => k; rewrite !inE -!/(mu_ _).
  by rewrite andb_idr // => nz_k; rewrite 2!{1}prTIred_1 2?Dmu2_1.
case=> _ _ ccS2 _ _ [tau2 Dtau2 cohS2].
have{cohS2} cohS2: coherent_with S2 M^# tau tau2 by apply: cohS2.
have sS20: cfConjC_subset S2 calS0.
  by split=> // xi /sS2S Sxi; have [_ ->] := sSS0.
rewrite perm_eq_sym perm_catC in defS; apply: perm_eq_coherent defS _.
suffices: (mu_ j - d%:R *: zeta)^\tau = tau2 (mu_ j) - tau1 (d%:R *: zeta).
  apply: (bridge_coherent scohS0 sS20 cohS2 sS10 cohS1) => [phi|].
    by apply: contraL => /S1'2.
  rewrite cfunD1E !cfunE zeta1w1 prTIred_1 mulrC Dmu2_1 // subrr.
  by rewrite image_f // rpredZnat ?mem_zchar.
have sumA: \sum_i alpha_ i j = mu_ j - delta *: mu_ 0 - (d%:R - delta) *: zeta.
  rewrite !sumrB sumr_const /= -scaler_sumr; congr (_ - _ - _).
  rewrite card_Iirr_abelian ?cyclic_abelian // -/w1 -scaler_nat.
  by rewrite scalerA mulrC divfK ?neq0CG.
rewrite scalerBl opprD opprK addrACA in sumA.
rewrite -{sumA}(canLR (addrK _) sumA) opprD opprK -scalerBr.
rewrite linearD linearZ linear_sum /= Dmu0zeta scalerBr.
rewrite (eq_bigr _ (fun i _ => Dalpha i)) sumrB sumr_const nirrW1.
rewrite -!scaler_sumr sumrB addrAC !addrA scalerBr subrK -addrA -opprD.
rewrite raddfZnat Dtau2 Ddelta_ //; congr (_ - _).
by rewrite addrC -scaler_nat scalerA mulrC divfK ?neq0CG // -scalerDl subrK.
Qed.

End OneMaximal.

Implicit Type M : {group gT}.

(* This is the exported version of Peterfalvi, Theorem (10.8). *)
Theorem FTtype345_noncoherence M (M' := M^`(1)%G) (maxM : M \in 'M) :
  (FTtype M > 2)%N -> ~ coherent (seqIndD M' M M' 1) M^# (FT_Dade0 maxM).
Proof.
rewrite ltnNge 2!leq_eqVlt => /norP[notMtype2 /norP[notMtype1 _]] [tau1 cohS].
have [U W W1 W2 defW MtypeP] := FTtypeP_witness maxM notMtype1.
have [zeta [irr_zeta Szeta zeta1w1]] := FTtypeP_ref_irr maxM MtypeP.
exact: (FTtype345_noncoherence_main MtypeP _ irr_zeta Szeta zeta1w1 cohS).
Qed.

(* This is the exported version of Peterfalvi, Theorem (10.10). *)
Theorem FTtype5_exclusion M : M \in 'M -> FTtype M != 5.
Proof.
move=> maxM; apply: wlog_neg; rewrite negbK => Mtype5.
have notMtype2: FTtype M != 2 by rewrite (eqP Mtype5).
have [U W W1 W2 defW [[MtypeP _] _]] := FTtypeP 5 maxM Mtype5.
have [zeta [irr_zeta Szeta zeta1w1]] := FTtypeP_ref_irr maxM MtypeP.
exact: (FTtype5_exclusion_main _ MtypeP _ irr_zeta).
Qed.

(* This the first assertion of Peterfalvi (10.11). *)
Lemma FTtypeP_pair_primes S T W W1 W2 (defW : W1 \x W2 = W) :
  typeP_pair S T defW -> prime #|W1| /\ prime #|W2|.
Proof.
move=> pairST; have [[_ maxS maxT] _ _ _ _] := pairST.
have type24 maxM := compl_of_typeII_IV maxM _ (FTtype5_exclusion maxM).
split; first by have [U /type24[]] := typeP_pairW pairST.
have xdefW: W2 \x W1 = W by rewrite dprodC.
by have [U /type24[]] := typeP_pairW (typeP_pair_sym xdefW pairST).
Qed.

Corollary FTtypeP_primes M U W W1 W2 (defW : W1 \x W2 = W) :
  M \in 'M -> of_typeP M U defW -> prime #|W1| /\ prime #|W2|.
Proof.
move=> maxM MtypeP; have [T pairMT _] := FTtypeP_pair_witness maxM MtypeP.
exact: FTtypeP_pair_primes pairMT.
Qed.

(* This is the remainder of Peterfalvi (10.11). *)
Lemma FTtypeII_prime_facts M U W W1 W2 (defW : W1 \x W2 = W) (maxM : M \in 'M) :
    of_typeP M U defW -> FTtype M == 2 ->
    let H := M`_\F%G in let HU := M^`(1)%G in
    let calS := seqIndD HU M H 1 in let tau := FT_Dade0 maxM in
    let p := #|W2| in let q := #|W1| in
  [/\ p.-abelem H, (#|H| = p ^ q)%N & coherent calS M^# tau].
Proof.
move=> MtypeP Mtype2 H HU calS tau p q.
have Mnot5: FTtype M != 5 by rewrite (eqP Mtype2).
have [_ cUU _ _ _] := compl_of_typeII maxM MtypeP Mtype2.
have [q_pr p_pr]: prime q /\ prime p := FTtypeP_primes maxM MtypeP.
have:= typeII_IV_core maxM MtypeP Mnot5; rewrite Mtype2 -/p -/q => [[_ oH]].
have [] := Ptype_Fcore_kernel_exists maxM MtypeP Mnot5.
have [_ _] := Ptype_Fcore_factor_facts maxM MtypeP Mnot5.
rewrite -/H; set H0 := Ptype_Fcore_kernel _; set Hbar := (H / H0)%G.
rewrite def_Ptype_factor_prime // -/p -/q => oHbar chiefHbar _.
have trivH0: H0 :=: 1%g.
  have [/maxgroupp/andP[/andP[sH0H _] nH0M] /andP[sHM _]] := andP chiefHbar.
  apply: card1_trivg; rewrite -(setIidPr sH0H) -divg_index.
  by rewrite -card_quotient ?(subset_trans sHM) // oHbar -oH divnn cardG_gt0.
have abelHbar: p.-abelem Hbar.
  have pHbar: p.-group Hbar by rewrite /pgroup oHbar pnat_exp pnat_id.
  by rewrite -is_abelem_pgroup // (sol_chief_abelem _ chiefHbar) ?mmax_sol.
rewrite /= trivH0 -(isog_abelem (quotient1_isog _)) in abelHbar.
have:= Ptype_core_coherence maxM MtypeP Mnot5; rewrite trivH0.
set C := _ MtypeP; have sCU: C \subset U by rewrite [C]unlock subsetIl.
by rewrite (derG1P (abelianS sCU cUU)) [(1 <*> 1)%G]join1G.
Qed.

End Ten.

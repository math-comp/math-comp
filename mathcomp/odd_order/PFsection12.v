(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg finset center.
Require Import fingroup morphism perm automorphism quotient action finalg zmodp.
Require Import gfunctor gproduct cyclic commutator gseries nilpotent pgroup.
Require Import sylow hall abelian maximal frobenius.
Require Import matrix mxalgebra mxpoly mxrepresentation mxabelem vector.
Require Import falgebra fieldext finfield.
Require Import BGsection1 BGsection2 BGsection3 BGsection4 BGsection7.
Require Import BGsection14 BGsection15 BGsection16.
Require Import ssrnum ssrint algC cyclotomic algnum.
Require Import classfun character inertia vcharacter.
Require Import PFsection1 PFsection2 PFsection3 PFsection4 PFsection5.
Require Import PFsection6 PFsection7 PFsection8 PFsection9 PFsection10.
Require Import PFsection11.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory FinRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section PFTwelve.

Variable gT : minSimpleOddGroupType.
Local Notation G := (TheMinSimpleOddGroup gT).
Implicit Types (p q : nat) (x y z : gT).
Implicit Types H K L M N P Q R S T U V W : {group gT}.

Section Twelve2.

(* Hypothesis 12.1 *)
Variable L : {group gT}.

Hypotheses (maxL : L \in 'M) (Ltype1 : FTtype L == 1%N).

Local Notation "` 'L'" := (gval L) (at level 0, only parsing) : group_scope.
Local Notation H := `L`_\F%G.
Local Notation "` 'H'" := `L`_\F (at level 0) : group_scope.

Let nsHL : H <| L. Proof. exact: gFnormal. Qed.
Let calS := seqIndD H L H 1%G.
Let tau := FT_Dade maxL.
Let S_ (chi : 'CF(L)) := [set i in irr_constt chi].
Let calX : {set Iirr L} := Iirr_kerD L H 1%g.
Let calI := [seq 'chi_i | i in calX].

(* This does not actually use the Ltype1 assumption. *)
Lemma FTtype1_ref_irr : exists2 phi, phi \in calS & phi 1%g = #|L : H|%:R.
Proof.
have [solH ntH] := (nilpotent_sol (Fcore_nil L), mmax_Fcore_neq1 maxL).
have [s Ls nzs] := solvable_has_lin_char ntH solH.
exists ('Ind 'chi_s); last by rewrite cfInd1 ?gFsub // lin_char1 ?mulr1.
by rewrite mem_seqInd ?gFnormal ?normal1 // !inE sub1G subGcfker -irr_eq1 nzs.
Qed.

Let mem_calI i : i \in calX -> 'chi_i \in calI.
Proof. by move=> i_Iirr; apply/imageP; exists i. Qed.

Lemma FTtype1_irrP i : 
  reflect (exists2 chi, chi \in calS & i \in S_ chi) (i \in calX).
Proof.
have [sHL nHL] := andP nsHL; rewrite !inE sub1G andbT.
apply/(iffP idP) => [kerH'i | [_ /seqIndC1P[t nz_t ->]]]; last first.
  by rewrite inE => /sub_cfker_constt_Ind_irr <-; rewrite ?subGcfker.
have [t] := constt_cfRes_irr H i; rewrite -constt_Ind_Res => tLi.
rewrite -(sub_cfker_constt_Ind_irr tLi) // in kerH'i.
suffices: 'Ind 'chi_t \in calS by exists ('Ind 'chi_t); rewrite // inE.
by rewrite mem_seqInd ?normal1 // !inE sub1G kerH'i.
Qed.

Lemma FTtype1_irr_partition :
  partition [set Si in [seq S_ chi | chi <- calS]] calX.
Proof.
apply/and3P; split; last 1 first.
- rewrite inE; apply/mapP=> [[chi Schi /esym/setP S_0]].
  have /eqP[] := seqInd_neq0 nsHL Schi.
  rewrite [chi]cfun_sum_constt big1 // => i chi_i.
  by have:= S_0 i; rewrite inE chi_i inE.
- apply/eqP/setP=> i; apply/bigcupP/FTtype1_irrP=> [[S_chi] | [chi Schi Si]].
    by rewrite inE => /mapP[chi Schi ->]; exists chi.
  by exists (S_ chi); rewrite // inE map_f.
apply/trivIsetP=> S_chi1 S_chi2.
rewrite !inE => /mapP[chi1 Schi1 ->] /mapP[chi2 Schi2 ->] {S_chi1 S_chi2}chi2'1.
apply/pred0P=> i; rewrite /= !inE; apply/andP=> [[chi1_i chi2_i]].
suffices: '['chi_i] == 0 by rewrite cfnorm_irr oner_eq0.
rewrite (constt_ortho_char (seqInd_char Schi1) (seqInd_char Schi2)) //.
by rewrite (seqInd_ortho _ Schi1 Schi2) // (contraNneq _ chi2'1) // => ->.
Qed.

(* This is Peterfalvi (12.2)(a), first part *)
Lemma FTtype1_seqInd_facts chi :
    chi \in calS ->
  [/\ chi = \sum_(i in S_ chi) 'chi_i,
      constant [seq 'chi_i 1%g | i in S_ chi]
    & {in S_ chi, forall i, 'chi_i \in 'CF(L, 1%g |: 'A(L))}].
Proof.
move=> calS_chi; have [t nz_t Dchi] := seqIndC1P calS_chi.
pose T := 'I_L['chi_t]%g.
have sTL: T \subset L by apply: Inertia_sub.
have sHT: H \subset T by apply/sub_Inertia/gFsub.
have sHL: H \subset L by apply: normal_sub.
have hallH: Hall T H := pHall_Hall (pHall_subl sHT sTL (Fcore_Hall L)).
have [U [LtypeF _]] := FTtypeP _ maxL Ltype1.
have [[_ _ sdHU] [U1 inertU1] _] := LtypeF.
have defT: H ><| 'I_U['chi_t] = T := sdprod_modl sdHU (sub_inertia 'chi_t).
have abTbar : abelian (T / H).
  have [_ _ /(_ _ _ inertU1 nz_t)sItU1] := typeF_context LtypeF.
  by rewrite -(isog_abelian (sdprod_isog defT)) (abelianS sItU1); case: inertU1.
have [DtL _ X_1] := cfInd_Hall_central_Inertia nsHL abTbar hallH.
have Dchi_sum : chi = \sum_(i in S_ chi) 'chi_i.
  by rewrite {1}Dchi DtL -Dchi; apply: eq_bigl => i; rewrite !inE.
have lichi : constant [seq 'chi_i 1%g | i in S_ chi].
  pose c := #|L : T|%:R * 'chi_t 1%g; apply: (@all_pred1_constant _ c).
  by apply/allP=> _ /imageP[s tLs ->] /=; rewrite inE Dchi in tLs; rewrite X_1.
split=> // j Schi_j /=; apply/cfun_onP=> y A'y.
have [Ly | /cfun0->//] := boolP (y \in L).
have CHy1: 'C_H[y] = 1%g.
  apply: contraNeq A'y => /trivgPn[z /setIP[Hz cyz] ntz].
  rewrite !inE -implyNb; apply/implyP=> nty; apply/bigcupP.
  rewrite FTsupp1_type1 Ltype1 //=; exists z; first by rewrite !inE ntz.
  by rewrite 3!inE nty Ly cent1C.
have: j \in calX by apply/FTtype1_irrP; exists chi.
by rewrite !inE => /andP[/not_in_ker_char0->].
Qed.

(* This is Peterfalvi (12.2)(a), second part. *)
Lemma FPtype1_irr_isometry :
  {in 'Z[calI, L^#], isometry tau, to 'Z[irr G, G^#]}.
Proof.
apply: (sub_iso_to _ _ (Dade_Zisometry _)) => // phi.
rewrite zcharD1E => /andP[S_phi phi1_0].
have /subsetD1P[_ /setU1K <-] := FTsupp_sub L; rewrite zcharD1 {}phi1_0 andbT.
apply: zchar_trans_on phi S_phi => _ /imageP[i /FTtype1_irrP[j calSj Sj_i] ->].
by rewrite zchar_split irr_vchar; have [_ _ ->] := FTtype1_seqInd_facts calSj.
Qed.

Lemma FPtype1_irr_subcoherent : 
  {R : 'CF(L) -> seq 'CF(G) | subcoherent calI tau R}.
Proof.
apply: irr_subcoherent; last exact: FPtype1_irr_isometry.
  have UcalI: uniq calI by apply/dinjectiveP; apply: in2W irr_inj.
  split=> // _ /imageP[i Ii ->]; rewrite !inE in Ii; first exact: mem_irr.
  by apply/imageP; exists (conjC_Iirr i); rewrite ?inE conjC_IirrE ?cfker_aut.
apply/hasPn=> psi; case/imageP => i; rewrite !inE => /andP[kerH'i _] ->.
rewrite /cfReal odd_eq_conj_irr1 ?mFT_odd // irr_eq1 -subGcfker.
by apply: contra kerH'i; apply: subset_trans; apply: gFsub.
Qed.
Local Notation R1gen := FPtype1_irr_subcoherent.

(* This is Peterfalvi (12.2)(b). *)
Lemma FPtype1_subcoherent (R1 := sval R1gen) :
  {R : 'CF(L) -> seq 'CF(G) |
    [/\ subcoherent calS tau R,
        {in Iirr_kerD L H 1%G, forall i (phi := 'chi_i),
         [/\ orthonormal (R1 phi),
             size (R1 phi) = 2
           & tau (phi - phi^*%CF) = \sum_(mu <- R1 phi) mu]}
    & forall chi, R chi = flatten [seq R1 'chi_i | i in S_ chi]]}.
Proof.
have nrS: ~~ has cfReal calS by apply: seqInd_notReal; rewrite ?mFT_odd.
have U_S: uniq calS by apply: seqInd_uniq.
have ccS: conjC_closed calS by apply: cfAut_seqInd.
have conjCS: cfConjC_subset calS (seqIndD H L H 1) by split.
case: R1gen @R1 => /= R1 subc1. 
have [[chi_char nrI ccI] tau_iso oI h1 hortho] := subc1.
pose R chi := flatten [seq R1 'chi_i | i in S_ chi].
have memI phi i: phi \in calS -> i \in S_ phi -> 'chi_i \in calI.
  by move=> Sphi Sphi_i; apply/image_f/FTtype1_irrP; exists phi.
have aux phi psi i j mu nu:
    phi \in calS -> psi \in calS -> i \in S_ phi -> j \in S_ psi -> 
    mu \in R1 'chi_i -> nu \in R1 'chi_j -> 
  orthogonal 'chi_i ('chi_j :: ('chi_j)^*%CF) -> '[mu, nu] = 0.
- move=> Sphi Spsi Sphi_i Spsi_j R1i_mu R1i_nu o_ij.
  apply: orthogonalP R1i_mu R1i_nu.
  by apply: hortho o_ij; [apply: memI Spsi Spsi_j | apply: memI Sphi Sphi_i].
exists R; split => //= => [| i Ii]; last first.
  have mem_i := mem_calI Ii; have{h1} [Zirr oR1 tau_im] := h1  _ mem_i.
  split=> //; apply/eqP; rewrite -eqC_nat -cfnorm_orthonormal // -{}tau_im.
  have ?: 'chi_i - ('chi_i)^*%CF \in 'Z[calI, L^#].
    have hchi : 'chi_i \in 'Z[calI, L] by rewrite mem_zchar_on // cfun_onG.
    rewrite sub_aut_zchar ?cfAut_zchar // => _ /mapP[j _ ->]; exact: irr_vchar.
  have [-> // _] := tau_iso; rewrite cfnormBd ?cfnorm_conjC ?cfnorm_irr //.
  by have [_ ->] := pairwise_orthogonalP oI; rewrite ?ccI // eq_sym (hasPn nrI).
have calS_portho : pairwise_orthogonal calS by apply: seqInd_orthogonal.
have calS_char : {subset calS <= character} by apply: seqInd_char.
have calS_chi_ortho :
  {in calS &, forall phi psi i j,
     i \in irr_constt phi -> j \in irr_constt psi ->
  '[phi, psi] = 0 -> '['chi_i, 'chi_j] = 0}.
- by move=> phi psi Sphi Spsi /= i j; apply: constt_ortho_char; apply/calS_char.
have ZisoS_tau: {in 'Z[calS, L^#], isometry tau, to 'Z[irr G, G^#]}.
  apply: (sub_iso_to _ _ (Dade_Zisometry _)) => // phi.
  have /subsetD1P[_ /setU1K <-] := FTsupp_sub L.
  rewrite zcharD1E zcharD1 => /andP[S_phi ->]; rewrite andbT.
  apply: zchar_trans_on phi S_phi => psi calS_psi.
  have [Dpsi _ hCF] := FTtype1_seqInd_facts calS_psi.
  by rewrite zchar_split (seqInd_vcharW calS_psi) /= Dpsi rpred_sum.
split=> {ZisoS_tau}//= [phi calS_phi | phi psi calS_phi calS_psi].
  rewrite /R /[seq _ | i in _]; set e := enum _; have: uniq e := enum_uniq _.
  have: all (mem (S_ phi)) e by apply/allP=> i; rewrite mem_enum.
  have ->: phi - phi^*%CF = \sum_(i <- e) ('chi_i - ('chi_i)^*%CF).
    rewrite big_filter sumrB -rmorph_sum.
    by have [<-] := FTtype1_seqInd_facts calS_phi.
  elim: e => /= [_ _ | i e IHe /andP[Si Se] /andP[e'i Ue]].
    by rewrite !big_nil /tau linear0.
  rewrite big_cons [tau _]linearD big_cat /= -/tau orthonormal_cat.
  have{IHe Ue} [/allP Ze -> ->] := IHe Se Ue.
  have{h1} /h1[/allP Z_R1i -> -> /=] := memI _ _ calS_phi Si.
  split=> //; first by apply/allP; rewrite all_cat Z_R1i.
  apply/orthogonalP=> mu nu R1i_mu /flatten_mapP[j e_j R1j_nu].
  have /= Sj := allP Se j e_j; apply: (aux phi phi i j) => //.
  rewrite /orthogonal /= !andbT !cfdot_irr mulrb ifN_eqC ?(memPn e'i) ?eqxx //=.
  rewrite !inE in Si Sj; rewrite -conjC_IirrE; set k := conjC_Iirr j.
  rewrite (calS_chi_ortho phi phi^*%CF) ?calS_char ?ccS //.
    by rewrite irr_consttE conjC_IirrE cfdot_conjC fmorph_eq0.
  by rewrite (seqInd_conjC_ortho _ _ _ calS_phi) ?mFT_odd.
case/andP=> /and3P[/eqP opsi_phi /eqP opsi_phiC _] _; apply/orthogonalP.
move=> nu mu /flatten_imageP[j Spsi_j R1j_nu] /flatten_imageP[i Sphi_i R1i_mu].
apply: (aux psi phi j i) => //; rewrite /orthogonal /= !andbT -conjC_IirrE.
rewrite !inE in Sphi_i Spsi_j; rewrite (calS_chi_ortho psi phi) ?calS_char //.
rewrite (calS_chi_ortho psi phi^*%CF) ?calS_char ?ccS ?eqxx //.
by rewrite irr_consttE conjC_IirrE cfdot_conjC fmorph_eq0.
Qed.

End Twelve2.

Local Notation R1gen := FPtype1_irr_subcoherent.
Local Notation Rgen := FPtype1_subcoherent.

(* This is Peterfalvi (12.3) *)
Lemma FTtype1_seqInd_ortho L1 L2 (maxL1 : L1 \in 'M) (maxL2 : L2 \in 'M)
    (L1type1 : FTtype L1 == 1%N) (L2type1 : FTtype L2 == 1%N)
    (H1 := L1`_\F%G) (H2 := L2`_\F%G) 
    (calS1 := seqIndD H1 L1 H1 1) (calS2 := seqIndD H2 L2 H2 1) 
    (R1 := sval (Rgen maxL1 L1type1)) (R2 := sval (Rgen maxL2 L2type1)) : 
    gval L2 \notin L1 :^: G ->
  {in calS1 & calS2, forall chi1 chi2, orthogonal (R1 chi1) (R2 chi2)}.
Proof.
move=> notL1G_L2; without loss{notL1G_L2} disjointA1A:
     L1 L2 maxL1 maxL2 L1type1 L2type1 @H1 @H2 @calS1 @calS2 @R1 @R2 / 
  [disjoint 'A1~(L2) & 'A~(L1)].
- move=> IH_L; have [_ _] := FT_Dade_support_disjoint maxL1 maxL2 notL1G_L2.
  by case=> /IH_L-oS12 chi1 chi2 *; first rewrite orthogonal_sym; apply: oS12.
case: (Rgen _ _) @R1 => /= R1; set R1' := sval _ => [[subcoh1 hR1' defR1]].
case: (Rgen _ _) @R2 => /= R2; set R2' := sval _ => [[subcoh2 hR2' defR2]].
pose tau1 := FT_Dade maxL1; pose tau2 := FT_Dade maxL2.
move=> chi1 chi2 calS1_chi1 calS2_chi2. 
have [_ _ _ /(_ chi1 calS1_chi1)[Z_R1 o1R1 dtau1_chi1] _] := subcoh1.
have{o1R1} [uR1 oR1] := orthonormalP o1R1.
apply/orthogonalP=> a b R1a R2b; pose psi2 := tau2 (chi2 - chi2^*%CF).
have Z1a: a \in dirr G by rewrite dirrE Z_R1 //= oR1 ?eqxx.
suffices{b R2b}: '[a, psi2] == 0.
  apply: contraTeq => nz_ab; rewrite /psi2 /tau2. 
  have [_ _ _ /(_ chi2 calS2_chi2)[Z_R2 o1R2 ->] _] := subcoh2.
  suffices [e ->]: {e | a = if e then - b else b}.
    rewrite -scaler_sign cfdotC cfdotZr -cfdotZl scaler_sumr.
    by rewrite cfproj_sum_orthonormal // conjCK signr_eq0.
  have [_ oR2] := orthonormalP o1R2.
  have Z1b: b \in dirr G by rewrite dirrE Z_R2 //= oR2 ?eqxx.
  move/eqP: nz_ab; rewrite cfdot_dirr //.
  by do 2?[case: eqP => [-> | _]]; [exists true | exists false | ].
have [chi1D _ Achi1] := FTtype1_seqInd_facts maxL1 L1type1 calS1_chi1.
pose S_chi1 := [set i0 in irr_constt chi1].
pose bchi i := 'chi[_ : {set gT}]_i - ('chi_i)^*%CF.
have [t S_chi1t et]: exists2 t, t \in S_chi1 & tau1 (bchi _ t) = a - a^*%CF.
  suffices: ~~ [forall i in S_chi1, '[tau1 (bchi L1 i), a] <= 0].
    rewrite negb_forall_in => /exists_inP[i Si tau1i_a]; exists i => //.
    case/dIrrP: Z1a tau1i_a => ia ->.
    have [k ->]: exists k, tau1 (bchi _ i) = bchi G k.
      exact: Dade_irr_sub_conjC (mem_irr _) (Achi1 i Si).
    have {1}->: bchi G k = dchi (false, k) + dchi (true, conjC_Iirr k).
      by rewrite /dchi !scaler_sign conjC_IirrE.
    rewrite cfdotDl !cfdot_dchi addrACA -opprD subr_le0 -!natrD leC_nat.
    do 2?case: (_ =P ia) => [<-|] _ //; first by rewrite /dchi scale1r.
    by rewrite /dchi scaleN1r conjC_IirrE rmorphN /= cfConjCK opprK addrC.
  have: '[tau1 (chi1 - chi1^*%CF), a] == 1.
    rewrite /tau1 dtau1_chi1 (bigD1_seq a) //= cfdotDl cfdot_suml oR1 // eqxx.
    by rewrite big1_seq ?addr0 // => xi /andP[/negPf a'xi ?]; rewrite oR1 ?a'xi.
  apply: contraL => /forall_inP tau1a_le0.
  rewrite (ltr_eqF (ler_lt_trans _ ltr01)) // chi1D rmorph_sum /= -/S_chi1.
  rewrite -sumrB [tau1 _]linear_sum /= -/tau1 cfdot_suml.
  by rewrite -oppr_ge0 -sumrN sumr_ge0 // => i /tau1a_le0; rewrite oppr_ge0.
clear Achi1 dtau1_chi1 uR1 defR1.
suffices: '[a, psi2] == - '[a, psi2] by rewrite -addr_eq0 (mulrn_eq0 _ 2).
have A1bchi2: chi2 - (chi2^*)%CF \in 'Z[calS2, 'A1(L2)].
  by rewrite FTsupp1_type1 // seqInd_sub_aut_zchar ?gFnormal.
have{t S_chi1t et} /eqP{2}->: '[a, psi2] == '[a^*%CF, psi2].
  move/zchar_on in A1bchi2; rewrite -subr_eq0 -cfdotBl.
  rewrite [psi2]FT_DadeE ?(cfun_onS (FTsupp1_sub _)) // -FT_Dade1E // -et.
  rewrite (cfdot_complement (Dade_cfunS _ _)) ?(cfun_onS _ (Dade_cfunS _ _)) //.
  by rewrite FT_Dade_supportE FT_Dade1_supportE setTD -disjoints_subset.
rewrite -2!raddfN opprB /= cfdot_conjCl -Dade_conjC rmorphB /= cfConjCK -/tau2.
rewrite conj_Cint ?Cint_cfdot_vchar ?(Z_R1 a) // Dade_vchar //.
rewrite (zchar_onS (FTsupp1_sub _)) // (zchar_sub_irr _ A1bchi2) //.
exact: seqInd_vcharW.
Qed.

Section Twelve_4_to_6.

Variable L : {group gT}.
Hypothesis maxL : L \in 'M .

Local Notation "` 'L'" := (gval L) (at level 0, only parsing) : group_scope.
Local Notation H := `L`_\F%G.
Local Notation "` 'H'" := `L`_\F (at level 0) : group_scope.
Local Notation H' := H^`(1)%G.
Local Notation "` 'H''" := `H^`(1) (at level 0) : group_scope.

Let calS := seqIndD H L H 1%G.
Let tau := FT_Dade maxL.
Let rho := invDade (FT_DadeF_hyp maxL).

Section Twelve_4_5.

Hypothesis Ltype1 : FTtype L == 1%N.

Let R := sval (Rgen maxL Ltype1).
Let S_ (chi : 'CF(L)) := [set i in irr_constt chi].

(* This is Peterfalvi (12.4). *)
Lemma FTtype1_ortho_constant (psi : 'CF(G)) x : 
    {in calS, forall phi, orthogonal psi (R phi)} -> x \in L :\: H ->
  {in x *: H, forall y, psi y = psi x}%g.
Proof. 
move=> opsiR /setDP[Lx H'x]; pose Rpsi := 'Res[L] psi.
have nsHL: H <| L := gFnormal _ _; have [sHL _] := andP nsHL.
have [U [[[_ _ sdHU] [U1 inertU1] _] _]] := FTtypeP 1 maxL Ltype1.
have /= [_ _ TIsub]:= FTtypeI_II_facts maxL Ltype1 sdHU.
pose ddL := FT_Dade_hyp maxL.
have A1Hdef : 'A1(L) = H^# by apply: FTsupp1_type1.
have dot_irr xi j : xi \in calS -> j \in S_ xi -> '['chi_j, xi] = 1.
  move=> xi_calS Sj.
  have -> : xi = \sum_(i <- enum (S_ xi)) 'chi_i.
    by rewrite big_filter; have [] := FTtype1_seqInd_facts maxL Ltype1 xi_calS.
  rewrite (bigD1_seq j) ?mem_enum ?enum_uniq //= cfdotDr cfdot_sumr cfnorm_irr.
  by rewrite big1 ?addr0 // => k i'k; rewrite cfdot_irr eq_sym (negPf i'k).
have {dot_irr} supp12B y xi j1 j2 : xi \in calS -> j1 \in S_ xi -> 
  j2 \in S_ xi ->  y \notin ('A(L) :\: H^#) -> ('chi_j1 - 'chi_j2) y = 0.
- move=> calS_xi Sj1 Sj2 yADHn.
  have [xiD xi_cst sup_xi] := FTtype1_seqInd_facts maxL Ltype1 calS_xi.
  have [Hy | H'y] := boolP (y \in H); last first.
    suffices /cfun_on0->: y \notin 1%g |: 'A(L) by rewrite ?rpredB ?sup_xi.
    by rewrite !inE negb_or negb_and (group1_contra H'y) ?H'y in yADHn *.
  have [s _ xiIndD] := seqIndP calS_xi.
  pose sum_sL := \sum_(xi_z <- ('chi_s ^: L)%CF) xi_z.
  suffices Dxi: {in S_ xi, forall i, 'chi_i y = sum_sL y}.
    by rewrite !cfunE !Dxi ?subrr.
  move=> k Sk; pose phiH := 'Res[H] 'chi_k.
  transitivity (phiH y); first by rewrite cfResE ?normal_sub.
  have phiH_s_1: '[phiH, 'chi_s] = 1 by rewrite cfdot_Res_l -xiIndD dot_irr.
  have phiH_s: s \in irr_constt phiH by rewrite irr_consttE phiH_s_1 oner_eq0.
  by rewrite [phiH](Clifford_Res_sum_cfclass _ phiH_s) // phiH_s_1 scale1r.
have {supp12B} oResD xi i1 i2 : xi \in calS -> i1 \in S_ xi -> i2 \in S_ xi ->
  '['Res[L] psi, 'chi_i1 - 'chi_i2] = 0.
- move=> calS_xi Si1 Si2; rewrite cfdotC Frobenius_reciprocity -cfdotC.
  case: (altP (i1 =P i2))=> [-> | d12]; first by rewrite subrr linear0 cfdot0r.
  have {supp12B} supp12B y: y \notin 'A(L) :\: H^# -> ('chi_i1 - 'chi_i2) y = 0.
    exact: (supp12B _ xi _ _ calS_xi).
  case: (FTtype1_seqInd_facts maxL Ltype1 calS_xi) => _ cst1 supA.
  move/(_ _ Si1): (supA) => /cfun_onP s1; case/(constantP 0): (cst1) => [n].
  move/all_pred1P /allP => nseqD; move/(_ _ Si2): (supA) => /cfun_onP s2.
  have nchi11: 'chi_i1 1%g = n by apply/eqP/nseqD/image_f.
  have{nseqD} nchi12: 'chi_i2 1%g = n by apply/eqP/nseqD/image_f.
  have i12_1: 'chi_i1 1%g == 'chi_i2 1%g by rewrite nchi11 nchi12.
  have sH1A: H^# \subset 'A(L) by rewrite Fcore_sub_FTsupp.
  have nzAH: 'A(L) :\: H^# != set0.
    apply: contra d12 => /eqP tADH; apply/eqP; apply: irr_inj; apply/cfunP=> w.
    apply/eqP; rewrite -subr_eq0; have := supp12B w; rewrite !cfunE => -> //.
    by rewrite tADH in_set0.
  have{nzAH} tiH: normedTI ('A(L) :\: H^#) G L by rewrite -A1Hdef TIsub ?A1Hdef.
  have{supp12B} supp12B : 'chi_i1 - 'chi_i2 \in 'CF(L, 'A(L) :\: H^#). 
    by apply/cfun_onP; apply: supp12B.
  have [_ /subsetIP[_ nAHL] _] := normedTI_P tiH.
  pose tau1 := restr_Dade ddL (subsetDl _ _) nAHL.
  have tauInd: {in 'CF(L, 'A(L) :\: H^#), tau1 =1 'Ind} := Dade_Ind _ tiH.
  rewrite -{}tauInd // [tau1 _]restr_DadeE {tau1 nAHL}//.
  suffices Rtau12: Dade ddL ('chi_i1 - 'chi_i2) \in 'Z[R xi].
    by rewrite (span_orthogonal (opsiR xi _)) ?memv_span1 ?(zchar_span Rtau12).
  case: (Rgen _ _) @R => rR [scohS]; case: (R1gen _ _) => /= R1 scohI ? DrR.
  rewrite -/calS in scohS; set calI := image _ _ in scohI.
  have [Ii1 Ii2]: 'chi_i1 \in calI /\ 'chi_i2 \in calI.
    by split; apply/image_f/FTtype1_irrP; exists xi.
  have [calI2 [I2i1 I2i2 sI2I] []] := pair_degree_coherence scohI Ii1 Ii2 i12_1.
  move=> tau2 cohI2; have [_ <-] := cohI2; last first.
    by rewrite zcharD1E rpredB ?mem_zchar // 2!cfunE subr_eq0.
  suffices R_I2 j: j \in S_ xi -> 'chi_j \in calI2 -> tau2 'chi_j \in 'Z[rR xi].
    by rewrite raddfB rpredB ?R_I2.
  move=> Sj /(mem_coherent_sum_subseq scohI sI2I cohI2)[e R1e ->].
  rewrite DrR big_seq rpred_sum // => phi /(mem_subseq R1e) R1phi.
  by apply/mem_zchar/flatten_imageP; exists j.
suffices ResL: {in x *: H, forall y, Rpsi y = Rpsi x}%g.
  move=> w xHw; case/lcosetP: xHw (ResL w xHw) => h Hh -> {w}.
  by rewrite !cfResE ?subsetT ?groupM // ?(subsetP sHL).
move=> _ /lcosetP[h Hh ->] /=; rewrite (cfun_sum_cfdot Rpsi).
pose calX := Iirr_kerD L H 1%g; rewrite (bigID (mem calX) xpredT) /= !cfunE.
set sumX := \sum_(i in _) _; suffices HsumX: sumX \in 'CF(L, H).
  rewrite !(cfun_on0 HsumX) ?groupMr // !sum_cfunE.
  rewrite !add0r; apply: eq_bigr => i;rewrite !inE sub1G andbT negbK => kerHi.
  by rewrite !cfunE  cfkerMr ?(subsetP kerHi).
rewrite [sumX](set_partition_big _ (FTtype1_irr_partition L)) /=.
apply: rpred_sum => A; rewrite inE => /mapP[xi calS_xi defA].
have [-> | [j Achij]] := set_0Vmem A; first by rewrite big_set0 rpred0.
suffices ->: \sum_(i in A) '[Rpsi, 'chi_i] *: 'chi_i = '[Rpsi, 'chi_j] *: xi.
  by rewrite rpredZ // (seqInd_on _ calS_xi).
have [-> _ _] := FTtype1_seqInd_facts maxL Ltype1 calS_xi; rewrite -defA.
rewrite scaler_sumr; apply: eq_bigr => i Ai; congr (_ *: _); apply/eqP.
by rewrite -subr_eq0 -cfdotBr (oResD xi) /S_ -?defA.
Qed.

(* This is Peterfalvi (12.5) *)
Lemma FtypeI_invDade_ortho_constant (psi : 'CF(G)) : 
    {in calS, forall phi, orthogonal psi (R phi)} ->
  {in H :\: H' &, forall x y, rho psi x = rho psi y}.
Proof.
have [nsH'H nsHL]: H' <| H /\ H <| L by rewrite !gFnormal.
have [[sH'H _] [sHL _]] := (andP nsH'H, andP nsHL).
case: (Rgen _ _) @R => /= rR [scohS _ _] opsiR; set rpsi := rho psi.
have{rR scohS opsiR} o_rpsi_S xi1 xi2:
  xi1 \in calS -> xi2 \in calS -> xi1 1%g = xi2 1%g -> '[rpsi, xi1 - xi2] = 0.
- move=> Sxi1 Sxi2 /eqP deg12.
  have [calS2 [S2xi1 S2xi2]] := pair_degree_coherence scohS Sxi1 Sxi2 deg12.
  move=> ccsS2S [tau2 cohS2]; have [[_ Dtau2] [_ sS2S _]] := (cohS2, ccsS2S).
  have{deg12} L1xi12: (xi1 - xi2) 1%g == 0 by rewrite !cfunE subr_eq0.
  have{ccsS2S cohS2} tau2E := mem_coherent_sum_subseq scohS ccsS2S cohS2.
  have o_psi_tau2 xi: xi \in calS2 -> '[psi, tau2 xi] = 0.
    move=> S2xi; have [e /mem_subseq Re ->] := tau2E xi S2xi.
    by rewrite cfdot_sumr big1_seq // => _ /Re/orthoPl->; rewrite ?opsiR ?sS2S.
  have A1xi12: xi1 - xi2 \in 'CF(L, H^#).
    by rewrite (@zchar_on _ _ calS) ?zcharD1 ?rpredB ?seqInd_zchar.
  rewrite cfdotC -invDade_reciprocity // -cfdotC.
  rewrite FT_DadeF_E -?FT_DadeE ?(cfun_onS (Fcore_sub_FTsupp maxL)) //.
  rewrite -Dtau2; last by rewrite zcharD1E rpredB ?mem_zchar.
  by rewrite !raddfB /= !o_psi_tau2 ?subrr.
pose P_ i : {set Iirr H} := [set j in irr_constt ('Ind[H, H'] 'chi_i)].
pose P : {set {set Iirr H}} := [set P_ i | i : Iirr H'].
have tiP: trivIset P.
  apply/trivIsetP=> _ _ /imsetP[i1 _ ->] /imsetP[i2 _ ->] chi2'1.
  apply/pred0P=> j; rewrite !inE; apply: contraNF chi2'1 => /andP[i1Hj i2Hj].
  case: ifP (cfclass_Ind_cases i1 i2 nsH'H) => _; first by rewrite /P_ => ->.
  have NiH i: 'Ind[H,H'] 'chi_i \is a character by rewrite cfInd_char ?irr_char.
  case/(constt_ortho_char (NiH i1) (NiH i2) i1Hj i2Hj)/eqP/idPn.
  by rewrite cfnorm_irr oner_eq0.  
have coverP: cover P =i predT.
  move=> j; apply/bigcupP; have [i jH'i] := constt_cfRes_irr H' j.
  by exists (P_ i); [apply: mem_imset | rewrite inE constt_Ind_Res].
have /(all_sig_cond 0)[lambda lambdaP] A: A \in P -> {i | A = P_ i}.
  by case/imsetP/sig2_eqW=> i; exists i.
pose theta A : Iirr H := odflt 0 [pick j in A :\ 0]; pose psiH := 'Res[H] rpsi.
pose a_ A := '[psiH, 'chi_(theta A)] / '['Ind 'chi_(lambda A), 'chi_(theta A)].
pose a := '[psiH, 1 - 'chi_(theta (pblock P 0))].
suffices Da: {in H :\: H', rpsi =1 (fun=> a)} by move=> /= *; rewrite !Da.
suffices DpsiH: psiH = \sum_(A in P) a_ A *: 'Ind 'chi_(lambda A) + a%:A.
  move=> x /setDP[Hx notH'x]; transitivity (psiH x); first by rewrite cfResE.
  rewrite DpsiH !cfunE sum_cfunE cfun1E Hx mulr1 big1 ?add0r // => A _.
  by rewrite cfunE (cfun_onP (cfInd_normal _ _)) ?mulr0.
apply: canRL (subrK _) _; rewrite [_ - _]cfun_sum_cfdot.
rewrite -(eq_bigl _ _ coverP) big_trivIset //=; apply: eq_bigr => A P_A.
rewrite {}/a_; set i := lambda A; set k := theta A; pose Ii := 'I_H['chi_i]%G.
have /cfInd_central_Inertia[//|e _ [DiH _ DiH_1]]: abelian (Ii / H').
  by rewrite (abelianS _ (der_abelian 0 H)) ?quotientS ?subsetIl.
have defA: A = P_ i := lambdaP A P_A.
have Ak: k \in A; last 1 [have iHk := Ak; rewrite defA inE in Ak].
  have [j iHj] := constt_cfInd_irr i sH'H.
  rewrite {}/k /theta; case: pickP => [k /setDP[]//| /(_ j)/=].
  by rewrite defA !in_set iHj andbT => /negbFE/eqP <-.
have{DiH} DiH: 'Ind 'chi_i = e *: \sum_(j in A) 'chi_j.
  by congr (_ = _ *: _): DiH; apply: eq_bigl => j; rewrite [in RHS]defA !inE.
rewrite {2}DiH; have{DiH} ->: e = '['Ind 'chi_i, 'chi_k].
  rewrite DiH cfdotZl cfdot_suml (bigD1 k) //= cfnorm_irr big1 ?addr0 ?mulr1 //.
  by move=> j /andP[_ k'j]; rewrite cfdot_irr (negPf k'j).
rewrite scalerA scaler_sumr divfK //; apply: eq_bigr => j Aj; congr (_ *: _).
rewrite cfdotBl cfdotZl -irr0 cfdot_irr mulr_natr mulrb eq_sym.
apply/(canLR (addrK _))/(canRL (addNKr _)); rewrite addrC -cfdotBr.
have [j0 | nzj] := altP eqP; first by rewrite j0 irr0 /a -j0 (def_pblock _ P_A).
have iHj := Aj; rewrite defA inE in iHj; rewrite cfdot_Res_l linearB /=.
do [rewrite o_rpsi_S ?cfInd1 ?DiH_1 //=; apply/seqIndC1P]; first by exists j.
by exists k; rewrite // /k /theta; case: pickP => [? | /(_ j)] /setD1P[].
Qed.

End Twelve_4_5.

Hypothesis frobL : [Frobenius L with kernel H].
  
Lemma FT_Frobenius_type1 : FTtype L == 1%N.
Proof.
have [E /Frobenius_of_typeF LtypeF] := existsP frobL.
by apply/idPn=> /FTtypeP_witness[]// _ _ _ _ _ /typePF_exclusion/(_ E).
Qed.
Let Ltype1 := FT_Frobenius_type1.

Lemma FTsupp_Frobenius : 'A(L) = H^#.
Proof.
apply/eqP; rewrite eqEsubset Fcore_sub_FTsupp // andbT.
apply/bigcupsP=> y; rewrite Ltype1 FTsupp1_type1 //= => H1y.
by rewrite setSD //; have [_ _ _ ->] := Frobenius_kerP frobL.
Qed.

(* This is Peterfalvi (12.6). *)
Lemma FT_Frobenius_coherence : {subset calS <= irr L} /\ coherent calS L^# tau.
Proof.
have irrS: {subset calS <= irr L}.
  by move=> _ /seqIndC1P[s nz_s ->]; apply: irr_induced_Frobenius_ker.
split=> //; have [U [MtypeF MtypeI]] := FTtypeP 1 maxL Ltype1.
have [[ntH ntU defL] _ _] := MtypeF; have nsHL: H <| L := gFnormal _ L.
have nilH: nilpotent H := Fcore_nil L; have solH := nilpotent_sol nilH.
have frobHU: [Frobenius L = H ><| U] := set_Frobenius_compl defL frobL.
pose R := sval (Rgen maxL Ltype1).
have scohS: subcoherent calS tau R by case: (svalP (Rgen maxL Ltype1)).
have [tiH | [cHH _] | [expUdvH1 _]] := MtypeI.
- have /Sibley_coherence := And3 (mFT_odd L) nilH tiH.
  case/(_ U)=> [|tau1 [IZtau1 Dtau1]]; first by left. 
  exists tau1; split=> // chi Schi; rewrite Dtau1 //.
  by rewrite /tau Dade_Ind ?FTsupp_Frobenius ?(zcharD1_seqInd_on _ Schi).
- apply/(uniform_degree_coherence scohS)/(@all_pred1_constant _ #|L : H|%:R).
  apply/allP=> _ /mapP[_ /seqIndP[s _ ->] ->] /=.
  by rewrite cfInd1 ?gFsub // lin_char1 ?mulr1 //; apply/char_abelianP.
have isoHbar := quotient1_isog H.
have /(_ 1%G)[|//|[_ [p [pH _] /negP[]]]] := non_coherent_chief nsHL solH scohS.
  split; rewrite ?mFT_odd ?normal1 ?sub1G -?(isog_nil isoHbar) //= joingG1.
  apply/existsP; exists (U / H')%G.
  rewrite Frobenius_proper_quotient ?(sol_der1_proper solH) //.
  exact: char_normal_trans (der_char 1 H) nsHL.
rewrite -(isog_pgroup p isoHbar) in pH.
have [pr_p p_dv_H _] := pgroup_pdiv pH ntH.
rewrite subn1 -(index_sdprod defL).
have [-> *] := typeF_context MtypeF; last by split; rewrite ?(sdprodWY defL).
by rewrite expUdvH1 // mem_primes pr_p cardG_gt0.
Qed.

End Twelve_4_to_6.

Section Twelve_8_to_16.

Variable p : nat.

(* Equivalent reformultaion of Hypothesis (12.8), avoiding quotients. *)
Hypothesis IHp :
  forall q M, (q < p)%N -> M \in 'M -> FTtype M == 1%N -> ('r_q(M) > 1)%N ->
  q \in \pi(M`_\F).

Variables M P0 : {group gT}.

Let K := M`_\F%G.
Let K' := K^`(1)%G.
Let nsKM : K <| M. Proof. exact: gFnormal. Qed.

Hypothesis maxM : M \in 'M.
Hypothesis Mtype1 : FTtype M == 1%N.
Hypothesis prankM : ('r_p(M) > 1)%N.
Hypothesis p'K : p^'.-group K.

Hypothesis sylP0 : p.-Sylow(M) P0.

(* This is Peterfalvi (12.9). *)
Lemma non_Frobenius_FTtype1_witness :
  [/\ abelian P0, 'r_p(P0) = 2
    & exists2 L, L \in 'M /\ P0 \subset L`_\s
    & exists2 x, x \in 'Ohm_1(P0)^#
    & [/\ ~~ ('C_K[x] \subset K'), 'N(<[x]>) \subset M & ~~ ('C[x] \subset L)]].
Proof.
have ntK: K :!=: 1%g := mmax_Fcore_neq1 maxM; have [sP0M pP0 _] := and3P sylP0.
have hallK: \pi(K).-Hall(M) K := Fcore_Hall M.
have K'p: p \notin \pi(K) by rewrite -p'groupEpi.
have K'P0: \pi(K)^'.-group P0 by rewrite (pi_pgroup pP0).
have [U hallU sP0U] := Hall_superset (mmax_sol maxM) sP0M K'P0.
have sylP0_U: p.-Sylow(U) P0 := pHall_subl sP0U (pHall_sub hallU) sylP0.
have{hallU} defM: K ><| U = M by apply/(sdprod_normal_p'HallP nsKM hallU).
have{K'P0} coKP0: coprime #|K| #|P0| by rewrite coprime_pi'.
have [/(_ _ _ sylP0_U)[abP0 rankP0] uCK _] := FTtypeI_II_facts maxM Mtype1 defM.
have{rankP0} /eqP prankP0: 'r_p(P0) == 2.
  by rewrite eqn_leq -{1}rank_pgroup // rankP0 (p_rank_Sylow sylP0).
have piP0p: p \in \pi(P0) by rewrite -p_rank_gt0 prankP0.
have [L maxL sP0Ls]: exists2 L, L \in 'M & P0 \subset L`_\s.
  have [DpiG _ _ _] := FT_Dade_support_partition gT.
  have:= piSg (subsetT P0) piP0p; rewrite DpiG => /exists_inP[L maxL piLs_p].
  have [_ /Hall_pi hallLs _] := FTcore_facts maxL.
  have [P sylP] := Sylow_exists p L`_\s; have [sPLs _] := andP sylP.
  have sylP_G: p.-Sylow(G) P := subHall_Sylow hallLs piLs_p sylP.
  have [y _ sP0_Py] := Sylow_subJ sylP_G (subsetT P0) pP0.
  by exists (L :^ y)%G; rewrite ?mmaxJ // FTcoreJ (subset_trans sP0_Py) ?conjSg.
split=> //; exists L => //; set P1 := 'Ohm_1(P0).
have abelP1: p.-abelem P1 := Ohm1_abelem pP0 abP0.
have [pP1 abP1 _] := and3P abelP1.
have sP10: P1 \subset P0 := Ohm_sub 1 P0; have sP1M := subset_trans sP10 sP0M.
have nKP1: P1 \subset 'N(K) by rewrite (subset_trans sP1M) ?gFnorm.
have nK'P1: P1 \subset 'N(K') := char_norm_trans (der_char 1 K) nKP1.
have{coKP0} coKP1: coprime #|K| #|P1| := coprimegS sP10 coKP0.
have solK: solvable K := nilpotent_sol (Fcore_nil M).
have isoP1: P1 \isog P1 / K'.
  by rewrite quotient_isog // coprime_TIg ?(coprimeSg (der_sub 1 K)).
have{ntK} ntKK': (K / K' != 1)%g.
  by rewrite -subG1 quotient_sub1 ?gFnorm ?proper_subn ?(sol_der1_proper solK).
have defKK': (<<\bigcup_(xbar in (P1 / K')^#) 'C_(K / K')[xbar]>> = K / K')%g.
  rewrite coprime_abelian_gen_cent1 ?coprime_morph ?quotient_norms //.
    by rewrite quotient_abelian.
  rewrite -(isog_cyclic isoP1) (abelem_cyclic abelP1).
  by rewrite -(p_rank_abelem abelP1) p_rank_Ohm1 prankP0.
have [xb P1xb ntCKxb]: {xb | xb \in (P1 / K')^# & 'C_(K / K')[xb] != 1}%g.
  apply/sig2W/exists_inP; rewrite -negb_forall_in.
  apply: contra ntKK' => /eqfun_inP regKP1bar.
  by rewrite -subG1 /= -defKK' gen_subG; apply/bigcupsP=> xb /regKP1bar->.
have [ntxb /morphimP[x nK'x P1x Dxb]] := setD1P P1xb.
have ntx: x != 1%g by apply: contraNneq ntxb => x1; rewrite Dxb x1 morph1.
have ntCKx: ~~ ('C_K[x] \subset K').
  rewrite -quotient_sub1 ?subIset ?gFnorm // -cent_cycle subG1 /=.
  have sXP1: <[x]> \subset P1 by rewrite cycle_subG.
  rewrite coprime_quotient_cent ?(coprimegS sXP1) ?(subset_trans sXP1) ?gFsub//.
  by rewrite quotient_cycle ?(subsetP nK'P1) // -Dxb cent_cycle.
have{uCK} UCx: 'M('C[x]) = [set M].
  rewrite -cent_set1 uCK -?card_gt0 ?cards1 // ?sub1set ?cent_set1.
    by rewrite !inE ntx (subsetP sP0U) ?(subsetP sP10).
  by apply: contraNneq ntCKx => ->; rewrite sub1G.
exists x; [by rewrite !inE ntx | split=> //].
  rewrite (sub_uniq_mmax UCx) /= -?cent_cycle ?cent_sub //.
  rewrite mFT_norm_proper ?cycle_eq1 //.
  by rewrite mFT_sol_proper abelian_sol ?cycle_abelian.
apply: contraL (leqW (p_rankS p sP0Ls)) => /(eq_uniq_mmax UCx)-> //.
by rewrite prankP0 FTcore_type1 //= ltnS p_rank_gt0.
Qed.

Variables (L : {group gT}) (x : gT).
Hypotheses (abP0 : abelian P0) (prankP0 : 'r_p(P0) = 2).
Hypotheses (maxL : L \in 'M) (sP0_Ls : P0 \subset L`_\s).
Hypotheses (P0_1s_x : x \in 'Ohm_1(P0)^#) (not_sCxK' : ~~ ('C_K[x] \subset K')).
Hypotheses (sNxM : 'N(<[x]>) \subset M) (not_sCxL : ~~ ('C[x] \subset L)).

Let H := L`_\F%G.
Let nsHL : H <| L. Proof. exact: gFnormal. Qed.

(* This is Peterfalvi (12.10). *)
Let frobL : [Frobenius L with kernel H].
Proof.
have [sP0M pP0 _] := and3P sylP0.
have [ntx /(subsetP (Ohm_sub 1 _))P0x] := setD1P P0_1s_x.
have [Ltype1 | notLtype1] := boolP (FTtype L == 1)%N; last first.
  have [U W W1 W2 defW LtypeP] := FTtypeP_witness maxL notLtype1.
  suffices sP0H: P0 \subset H.
    have [Hx notLtype5] := (subsetP sP0H x P0x, FTtype5_exclusion maxL).
    have [_ _ _ tiFL] := compl_of_typeII_IV maxL LtypeP notLtype5.
    have Fx: x \in 'F(L)^# by rewrite !inE ntx (subsetP (Fcore_sub_Fitting L)).
    by have /idPn[] := cent1_normedTI tiFL Fx; rewrite setTI.
  have [/=/FTcore_type2<- // | notLtype2] := boolP (FTtype L == 2).
  have [_ _ [Ltype3 galL]] := FTtype34_structure maxL LtypeP notLtype2.
  have cycU: cyclic U.
    suffices regHU: Ptype_Fcompl_kernel LtypeP :=: 1%g.
      rewrite (isog_cyclic (quotient1_isog U)) -regHU.
      by have [|_ _ [//]] := typeP_Galois_P maxL _ galL; rewrite (eqP Ltype3).
    rewrite /Ptype_Fcompl_kernel unlock /= astabQ /=.
    have [_ _ ->] := FTtype34_Fcore_kernel_trivial maxL LtypeP notLtype2.
    rewrite -morphpreIim -injm_cent ?injmK ?ker_coset ?norms1 //.
    have [_ _ _ ->] := FTtype34_facts maxL LtypeP notLtype2.
    by apply/derG1P; have [] := compl_of_typeIII maxL LtypeP Ltype3.
  have sP0L': P0 \subset L^`(1) by rewrite -FTcore_type_gt2 ?(eqP Ltype3).
  have [_ [_ _ _ defL'] _ _ _] := LtypeP.
  have [nsHL' _ /mulG_sub[sHL' _] _ _] := sdprod_context defL'.
  have hallH := pHall_subl sHL' (der_sub 1 L) (Fcore_Hall L).
  have hallU: \pi(H)^'.-Hall(L^`(1)) U.
    by rewrite -(compl_pHall U hallH) sdprod_compl.
  rewrite (sub_normal_Hall hallH) // (pi_pgroup pP0) //.
  have: ~~ cyclic P0; last apply: contraR => piK'p.
    by rewrite abelian_rank1_cyclic // (rank_pgroup pP0) prankP0.
  by have [|y _ /cyclicS->] := Hall_psubJ hallU piK'p _ pP0; rewrite ?cyclicJ.
have sP0H: P0 \subset H by rewrite /= -FTcore_type1.
have [U [LtypeF /= LtypeI]] := FTtypeP 1 maxL Ltype1.
have [[_ _ defL] _ _] := LtypeF; have [_ sUL _ nHU _] := sdprod_context defL.
have not_tiH: ~ normedTI H^# G L.
  have H1x: x \in H^# by rewrite !inE ntx (subsetP sP0H).
  by case/cent1_normedTI/(_ x H1x)/idPn; rewrite setTI.
apply/existsP; exists U; have [_ -> _] := typeF_context LtypeF.
apply/forall_inP=> Q /SylowP[q pr_q sylQ]; have [sQU qQ _] := and3P sylQ.
rewrite (odd_pgroup_rank1_cyclic qQ) ?mFT_odd //.
apply: wlog_neg; rewrite -ltnNge => /ltnW; rewrite p_rank_gt0 => piQq.
have hallU: \pi(H)^'.-Hall(L) U.
  by rewrite -(compl_pHall U (Fcore_Hall L)) sdprod_compl.
have H'q := pnatPpi (pHall_pgroup hallU) (piSg sQU piQq).
rewrite leqNgt; apply: contra (H'q) => qrankQ; apply: IHp => //; last first.
  by rewrite (leq_trans qrankQ) ?p_rankS ?(subset_trans sQU).
have piHp: p \in \pi(H) by rewrite (piSg sP0H) // -p_rank_gt0 prankP0.
have pr_p: prime p by have:= piHp; rewrite mem_primes => /andP[].
have piUq: q \in \pi(exponent U) by rewrite pi_of_exponent (piSg sQU).
have [odd_p odd_q]: odd p /\ odd q.
  rewrite !odd_2'nat !pnatE //.
  by rewrite (pnatPpi _ piHp) ?(pnatPpi _ piQq) -?odd_2'nat ?mFT_odd.
have pgt2 := odd_prime_gt2 odd_p pr_p.
suffices [b dv_q_bp]: exists b : bool, q %| (b.*2 + p).-1.
  rewrite -ltn_double (@leq_ltn_trans (p + b.*2).-1) //; last first.
    by rewrite -!addnn -(subnKC pgt2) prednK // leq_add2l; case: (b).
  rewrite -(subnKC pgt2) dvdn_leq // -mul2n Gauss_dvd ?coprime2n // -{1}subn1.
  by rewrite dvdn2 odd_sub // subnKC // odd_add odd_p odd_double addnC.
have [// | [cHH rankH] | [/(_ p piHp)Udvp1 _]] := LtypeI; last first.
  exists false; apply: dvdn_trans Udvp1.
  by have:= piUq; rewrite mem_primes => /and3P[].
suffices: q %| p ^ 2 - 1 ^ 2.
  rewrite subn_sqr addn1 subn1 Euclid_dvdM //.
  by case/orP; [exists false | exists true].
pose P := 'O_p(H); pose P1 := 'Ohm_1(P).
have chP1H: P1 \char H := char_trans (Ohm_char 1 _) (pcore_char p H).
have sylP: p.-Sylow(H) P := nilpotent_pcore_Hall p (Fcore_nil L).
have [sPH pP _] := and3P sylP.
have abelP1: p.-abelem P1 by rewrite Ohm1_abelem ?(abelianS sPH).
have [pP1 _] := andP abelP1.
have prankP1: 'r_p(P1) = 2.
  apply/eqP; rewrite p_rank_Ohm1 eqn_leq -{1}rank_pgroup // -{1}rankH rankS //=.
  by rewrite -prankP0 (p_rank_Sylow sylP) p_rankS.
have ntP1: P1 != 1%g by rewrite -rank_gt0 (rank_pgroup pP1) prankP1.
have [_ _ [U0 [sU0U expU0 frobHU0]]] := LtypeF.
have nP1U0: U0 \subset 'N(P1).
  by rewrite (char_norm_trans chP1H) ?(subset_trans sU0U).
rewrite subn1 -prankP1 p_rank_abelem // -card_pgroup //.
have frobP1U0 := Frobenius_subl ntP1 (char_sub chP1H) nP1U0 frobHU0.
apply: dvdn_trans (Frobenius_dvd_ker1 frobP1U0).
by have:= piUq; rewrite -expU0 pi_of_exponent mem_primes => /and3P[].
Qed.

Let Ltype1 : FTtype L == 1%N. Proof. exact: FT_Frobenius_type1 frobL. Qed.
Let defAL : 'A(L) = H^#. Proof. exact: FTsupp_Frobenius frobL. Qed.
Let sP0H : P0 \subset H. Proof. by rewrite /= -FTcore_type1. Qed.

(* This is the first part of Peterfalvi (12.11). *)
Let defM : K ><| (M :&: L) = M.
Proof.
have [ntx /(subsetP (Ohm_sub 1 _))P0x] := setD1P P0_1s_x.
have Dx: x \in [set y in 'A0(L) | ~~ ('C[y] \subset L)].
  by rewrite inE FTsupp0_type1 // defAL !inE ntx (subsetP sP0H).
have [_ [_ /(_ x Dx)uCx] /(_ x Dx)[[defM _] _ _ _]] := FTsupport_facts maxL.
rewrite /K /= setIC (eq_uniq_mmax uCx maxM) //= -cent_cycle.
exact: subset_trans (cent_sub <[x]>) sNxM.
Qed.

(* This is the second part of Peterfalvi (12.11). *)
Let sML_H : M :&: L \subset H.
Proof.
have [sP0M pP0 _] := and3P sylP0.
rewrite (sub_normal_Hall (Fcore_Hall L)) ?subsetIr //.
apply/pgroupP=> q pr_q /Cauchy[]// z /setIP[Mz Lz] oz; pose A := <[z]>%G.
have z_gt1: (#[z] > 1)%N by rewrite oz prime_gt1.
have sylP0_HM: p.-Sylow(H :&: M) P0.
  by rewrite (pHall_subl _ _ sylP0) ?subsetIr // subsetI sP0H.
have nP0A: A \subset 'N(P0).
  have sylHp: p.-Sylow(H) 'O_p(H) := nilpotent_pcore_Hall p (Fcore_nil L).
  have sP0Hp: P0 \subset 'O_p(H) by rewrite sub_Hall_pcore.
  have <-: 'O_p(H) :&: M = P0.
    rewrite [_ :&: _](sub_pHall sylP0_HM) ?setSI ?pcore_sub //.
      by rewrite (pgroupS (subsetIl _ _)) ?pcore_pgroup.
    by rewrite subsetI sP0Hp.
  have chHpL: 'O_p(H) \char L := char_trans (pcore_char p H) (Fcore_char L).
  by rewrite normsI ?(char_norm_trans chHpL) ?normsG // cycle_subG.
apply: wlog_neg => piH'q.
have coHQ: coprime #|H| #|A| by rewrite -orderE coprime_pi' // oz pnatE.
have frobP0A: [Frobenius P0 <*> A = P0 ><| A].
  have defHA: H ><| A = H <*> A.
    by rewrite sdprodEY ?coprime_TIg // cycle_subG (subsetP (gFnorm _ _)).
  have ltH_HA: H \proper H <*> A.
    by rewrite /proper joing_subl -indexg_gt1 -(index_sdprod defHA).
  have: [Frobenius H <*> A = H ><| A].
    apply: set_Frobenius_compl defHA _.
    by apply: Frobenius_kerS frobL; rewrite // join_subG gFsub cycle_subG.
  by apply: Frobenius_subl => //; rewrite -rank_gt0 (rank_pgroup pP0) prankP0.
have sP0A_M: P0 <*> A \subset M by rewrite join_subG sP0M cycle_subG.
have nKP0a: P0 <*> A \subset 'N(K) := subset_trans sP0A_M (gFnorm _ _).
have solK: solvable K := nilpotent_sol (Fcore_nil M).
have [_ [/(compl_of_typeF defM) MtypeF _]] := FTtypeP 1 maxM Mtype1.
have nreg_KA: 'C_K(A) != 1%g.
  have [Kq | K'q] := boolP (q \in \pi(K)).
    apply/trivgPn; exists z; rewrite -?order_gt1 //= cent_cycle inE cent1id.
    by rewrite andbT (mem_normal_Hall (Fcore_Hall M)) // /p_elt oz pnatE.
  have [defP0A ntP0 _ _ _] := Frobenius_context frobP0A.
  have coK_P0A: coprime #|K| #|P0 <*> A|.
    rewrite -(sdprod_card defP0A) coprime_mulr (p'nat_coprime p'K) //=.
    by rewrite -orderE coprime_pi' // oz pnatE.
  have: ~~ (P0 \subset 'C(K)); last apply: contraNneq.
    have [[ntK _ _] _ [U0 [sU0ML expU0 frobKU0]]] := MtypeF.
    have [P1 /pnElemP[sP1U0 abelP1 dimP1]] := p_rank_witness p U0.
    have ntP1: P1 :!=: 1%g.
      rewrite -rank_gt0 (rank_abelem abelP1) dimP1 p_rank_gt0 -pi_of_exponent.
      rewrite expU0 pi_of_exponent (piSg (setIS M (Fcore_sub L))) //=.
      by rewrite setIC -p_rank_gt0 -(p_rank_Sylow sylP0_HM) prankP0.
    have frobKP1: [Frobenius K <*> P1 = K ><| P1].
      exact: Frobenius_subr ntP1 sP1U0 frobKU0.
    have sP1M: P1 \subset M.
      by rewrite (subset_trans (subset_trans sP1U0 sU0ML)) ?subsetIl.
    have [y My sP1yP0] := Sylow_Jsub sylP0 sP1M (abelem_pgroup abelP1).
    apply: contra ntK => cP0K; rewrite -(Frobenius_trivg_cent frobKP1).
    rewrite (setIidPl _) // -(conjSg _ _ y) (normsP _ y My) ?gFnorm //.
    by rewrite -centJ centsC (subset_trans sP1yP0).
  by have [] := Frobenius_Wielandt_fixpoint frobP0A nKP0a coK_P0A solK.
have [_ [U1 [_ abU1 sCK_U1]] _] := MtypeF.
have [ntx /(subsetP (Ohm_sub 1 _))P0x] := setD1P P0_1s_x.
have cAx: A \subset 'C[x].
  rewrite -cent_set1 (sub_abelian_cent2 abU1) //.
    have [y /setIP[Ky cAy] nty] := trivgPn _ nreg_KA.
    apply: subset_trans (sCK_U1 y _); last by rewrite !inE nty.
    by rewrite subsetI sub_cent1 cAy cycle_subG !inE Mz Lz.
  have [y /setIP[Ky cxy] notK'y] := subsetPn not_sCxK'.
  apply: subset_trans (sCK_U1 y _); last by rewrite !inE (group1_contra notK'y).
  rewrite sub1set inE cent1C cxy (subsetP _ x P0x) //.
  by rewrite subsetI sP0M (subset_trans sP0H) ?gFsub.
have [_ _ _ regHL] := Frobenius_kerP frobL.
rewrite (piSg (regHL x _)) //; first by rewrite !inE ntx (subsetP sP0H).
by rewrite mem_primes pr_q cardG_gt0 -oz cardSg // subsetI cycle_subG Lz.
Qed.

Let E := sval (sigW (existsP frobL)).
Let e := #|E|.

Let defL : H ><| E = L.
Proof. by rewrite /E; case: (sigW _) => E0 /=/Frobenius_context[]. Qed.

Let Ecyclic_le_p : cyclic E /\ (e %| p.-1) || (e %| p.+1).
Proof.
pose P := 'O_p(H)%G; pose T := 'Ohm_1('Z(P))%G.
have sylP: p.-Sylow(H) P := nilpotent_pcore_Hall p (Fcore_nil L).
have [[sPH pP _] [sP0M pP0 _]] := (and3P sylP, and3P sylP0). 
have sP0P: P0 \subset P by rewrite (sub_normal_Hall sylP) ?pcore_normal.
have defP0: P :&: M = P0.
  rewrite [P :&: M](sub_pHall sylP0 (pgroupS _ pP)) ?subsetIl ?subsetIr //.
  by rewrite subsetI sP0P.
have [ntx P01x] := setD1P P0_1s_x; have P0x := subsetP (Ohm_sub 1 P0) x P01x.
have sZP0: 'Z(P) \subset P0.
  apply: subset_trans (_ : 'C_P[x] \subset P0).
    by rewrite -cent_set1 setIS ?centS // sub1set (subsetP sP0P).
  by rewrite -defP0 setIS // (subset_trans _ sNxM) // cents_norm ?cent_cycle.
have ntT: T :!=: 1%g.
  rewrite Ohm1_eq1 center_nil_eq1 ?(pgroup_nil pP) // (subG1_contra sP0P) //.
  by apply/trivgPn; exists x.
have [_ sEL _ nHE tiHE] := sdprod_context defL.
have charTP: T \char P := char_trans (Ohm_char 1 _) (center_char P).
have{ntT} [V minV sVT]: {V : {group gT} | minnormal V E & V \subset T}.
  apply: mingroup_exists; rewrite ntT (char_norm_trans charTP) //.
  exact: char_norm_trans (pcore_char p H) nHE.
have abelT: p.-abelem T by rewrite Ohm1_abelem ?center_abelian ?(pgroupS sZP0).
have sTP := subset_trans (Ohm_sub 1 _) sZP0.
have rankT: ('r_p(T) <= 2)%N by rewrite -prankP0 p_rankS.
have [abelV /andP[ntV nVE]] := (abelemS sVT abelT, mingroupp minV).
have pV := abelem_pgroup abelV; have [pr_p _ [n oV]] := pgroup_pdiv pV ntV.
have frobHE: [Frobenius L = H ><| E] by rewrite /E; case: (sigW _).
have: ('r_p(V) <= 2)%N by rewrite (leq_trans (p_rankS p sVT)).
rewrite (p_rank_abelem abelV) // oV pfactorK // ltnS leq_eqVlt ltnS leqn0 orbC.
have sVH := subset_trans sVT (subset_trans (char_sub charTP) sPH).
have regVE: 'C_E(V) = 1%g.
  exact: cent_semiregular (Frobenius_reg_compl frobHE) sVH ntV.
case/pred2P=> dimV; rewrite {n}dimV in oV.
  pose f := [morphism of restrm nVE (conj_aut V)].
  have injf: 'injm f by rewrite ker_restrm ker_conj_aut regVE.
  rewrite /e -(injm_cyclic injf) // -(card_injm injf) //.
  have AutE: f @* E \subset Aut V by rewrite im_restrm Aut_conj_aut.
  rewrite (cyclicS AutE) ?Aut_prime_cyclic ?oV // (dvdn_trans (cardSg AutE)) //.
  by rewrite card_Aut_cyclic ?prime_cyclic ?oV // totient_pfactor ?muln1.
have defV: V :=: 'Ohm_1(P0).
  apply/eqP; rewrite eqEcard (subset_trans sVT) ?OhmS //= oV -prankP0.
  by rewrite p_rank_abelian // -card_pgroup ?(pgroupS (Ohm_sub 1 _)).
pose rE := abelem_repr abelV ntV nVE.
have ffulE: mx_faithful rE by apply: abelem_mx_faithful.
have p'E: [char 'F_p]^'.-group E.
  rewrite (eq_p'group _ (charf_eq (char_Fp pr_p))) (coprime_p'group _ pV) //.
  by rewrite coprime_sym (coprimeSg sVH) ?(Frobenius_coprime frobHE).
have dimV: 'dim V = 2 by rewrite (dim_abelemE abelV) // oV pfactorK. 
have cEE: abelian E.
  by rewrite dimV in (rE) ffulE; apply: charf'_GL2_abelian (mFT_odd E) ffulE _.
have Enonscalar y: y \in E -> y != 1%g -> ~~ is_scalar_mx (rE y).
  move=> Ey; apply: contra => /is_scalar_mxP[a rEy]; simpl in a.
  have nXy: y \in 'N(<[x]>).
    rewrite !inE -cycleJ cycle_subG; apply/cycleP; exists a.
    have [Vx nVy]: x \in V /\ y \in 'N(V) by rewrite (subsetP nVE) ?defV.
    apply: (@abelem_rV_inj p _ V); rewrite ?groupX ?memJ_norm ?morphX //=.
    by rewrite zmodXgE -scaler_nat natr_Zp -mul_mx_scalar -rEy -abelem_rV_J.
  rewrite -in_set1 -set1gE -tiHE inE (subsetP sML_H) //.
  by rewrite inE (subsetP sEL) // (subsetP sNxM).
have /trivgPn[y nty Ey]: E != 1%G by have [] := Frobenius_context frobHE.
have cErEy: centgmx rE (rE y).
  by apply/centgmxP=> z Ez; rewrite -!repr_mxM // (centsP cEE).
have irrE: mx_irreducible rE by apply/abelem_mx_irrP.
have charFp2: p \in [char MatrixGenField.gen_finFieldType irrE cErEy].
  apply: (rmorph_char (MatrixGenField.gen_rmorphism irrE cErEy)).
  exact: char_Fp.
pose Fp2 := primeChar_finFieldType charFp2.
pose n1 := MatrixGenField.gen_dim (rE y).
pose rEp2 : mx_representation Fp2 E n1 := MatrixGenField.gen_repr irrE cErEy.
have n1_gt0: (0 < n1)%N := MatrixGenField.gen_dim_gt0 irrE cErEy.
have n1_eq1: n1 = 1%N.
  pose d := degree_mxminpoly (rE y).
  have dgt0: (0 < d)%N := mxminpoly_nonconstant _.
  apply/eqP; rewrite eqn_leq n1_gt0 andbT -(leq_pmul2r dgt0).
  rewrite (MatrixGenField.gen_dim_factor irrE cErEy) mul1n dimV.
  by rewrite ltnNge mxminpoly_linear_is_scalar Enonscalar.
have oFp2: #|Fp2| = (p ^ 2)%N.
  rewrite card_sub card_matrix card_Fp // -{1}n1_eq1.
  by rewrite (MatrixGenField.gen_dim_factor irrE cErEy) dimV.
have [f rfK fK]: bijective (@scalar_mx Fp2 n1).
  rewrite n1_eq1.
  by exists (fun A : 'M_1 => A 0 0) => ?; rewrite ?mxE -?mx11_scalar.
pose g z : {unit Fp2} := insubd (1%g : {unit Fp2}) (f (rEp2 z)).
have val_g z : z \in E -> (val (g z))%:M = rEp2 z.
  move=> Ez; rewrite insubdK ?fK //; have:= repr_mx_unit rEp2 Ez.
  by rewrite -{1}[rEp2 z]fK unitmxE det_scalar !unitfE expf_eq0 n1_gt0.
have ffulEp2: mx_faithful rEp2 by rewrite MatrixGenField.gen_mx_faithful.
have gM: {in E &, {morph g: z1 z2 / z1 * z2}}%g.
  move=> z1 z2 Ez1 Ez2 /=; apply/val_inj/(can_inj rfK).
  rewrite {1}(val_g _ (groupM Ez1 Ez2)) scalar_mxM.
  by rewrite {1}(val_g _ Ez1) (val_g _ Ez2) repr_mxM.
have inj_g: 'injm (Morphism gM).
  apply/injmP=> z1 z2 Ez1 Ez2 /(congr1 (@scalar_mx _ n1 \o val)).
  by rewrite /= {1}(val_g _ Ez1) (val_g _ Ez2); apply: mx_faithful_inj.
split; first by rewrite -(injm_cyclic inj_g) ?field_unit_group_cyclic.
have: e %| #|[set: {unit Fp2}]|.
  by rewrite /e -(card_injm inj_g) ?cardSg ?subsetT.
rewrite card_finField_unit oFp2 -!subn1 (subn_sqr p 1) addn1.
rewrite orbC Gauss_dvdr; first by move->.
rewrite coprime_sym coprime_has_primes ?subn_gt0 ?prime_gt1 ?cardG_gt0 //.
apply/hasPn=> r; rewrite /= !mem_primes subn_gt0 prime_gt1 ?cardG_gt0 //=.
case/andP=> pr_r /Cauchy[//|z Ez oz]; rewrite pr_r /= subn1.
apply: contra (Enonscalar z Ez _); last by rewrite -order_gt1 oz prime_gt1.
rewrite -oz -(order_injm inj_g) // order_dvdn -val_eqE => /eqP gz_p1_eq1.
have /vlineP[a Dgz]: val (g z) \in 1%VS.
  rewrite Fermat's_little_theorem dimv1 card_Fp //=.
  by rewrite -[(p ^ 1)%N]prednK ?prime_gt0 // exprS -val_unitX gz_p1_eq1 mulr1.
apply/is_scalar_mxP; exists a; apply/row_matrixP=> i.
apply: (can_inj ((MatrixGenField.in_genK irrE cErEy) _)).
rewrite !rowE mul_mx_scalar MatrixGenField.in_genZ MatrixGenField.in_genJ //.
rewrite -val_g // Dgz mul_mx_scalar; congr (_ *: _).
rewrite -(natr_Zp a) scaler_nat.
by rewrite -(rmorph_nat (MatrixGenField.gen_rmorphism irrE cErEy)).
Qed.

Let calS := seqIndD H L H 1.
Notation tauL := (FT_Dade maxL).
Notation tauL_H := (FT_DadeF maxL).
Notation rhoL := (invDade (FT_DadeF_hyp maxL)).

Section Twelve_13_to_16.

Variables (tau1 : {additive 'CF(L) -> 'CF(G)}) (chi : 'CF(L)).
Hypothesis cohS : coherent_with calS L^# tauL tau1.
Hypotheses (Schi : chi \in calS) (chi1 : chi 1%g = e%:R).
Let psi := tau1 chi.

Let cohS_H : coherent_with calS L^# tauL_H tau1.
Proof.
have [? Dtau] := cohS; split=> // xi Sxi; have /zcharD1_seqInd_on Hxi := Sxi.
by rewrite Dtau // FT_DadeF_E ?FT_DadeE ?(cfun_onS (Fcore_sub_FTsupp _)) ?Hxi.
Qed.

(* This is Peterfalvi (12.14). *)
Let rhoL_psi : {in K, forall g, psi (x * g)%g = chi x} /\ rhoL psi x = chi x.
Proof.
have not_LGM: gval M \notin L :^: G.
  apply: contraL p'K => /= /imsetP[z _ ->]; rewrite FcoreJ pgroupJ.
  by rewrite p'groupEpi (piSg sP0H) // -p_rank_gt0 prankP0.
pose rmR := sval (Rgen maxL Ltype1).
have Zpsi: psi \in 'Z[rmR chi].
  case: (Rgen _ _) @rmR => /= rmR []; rewrite -/calS => scohS _ _.
  have sSS: cfConjC_subset calS calS by apply: seqInd_conjC_subset1.
  have [B /mem_subseq sBR Dpsi] := mem_coherent_sum_subseq scohS sSS cohS Schi.
  by rewrite [psi]Dpsi big_seq rpred_sum // => xi /sBR/mem_zchar->.
have [ntx /(subsetP (Ohm_sub 1 P0))P0x] := setD1P P0_1s_x.
have Mx: x \in M by rewrite (subsetP sNxM) // -cycle_subG normG.
have psi_xK: {in K, forall g, psi (x * g)%g = psi x}.
  move=> g Kg; have{Kg}: (x * g \in x *: K)%g by rewrite mem_lcoset mulKg.
  apply: FTtype1_ortho_constant => [phi calMphi|].
    apply/orthoPl=> nu /memv_span; apply: {nu}span_orthogonal (zchar_span Zpsi).
    exact: FTtype1_seqInd_ortho.
  rewrite inE -/K (contra _ ntx) // => Kx.
  rewrite -(consttC p x) !(constt1P _) ?mulg1 ?(mem_p_elt p'K) //.
  by rewrite p_eltNK (mem_p_elt (pHall_pgroup sylP0)).
have H1x: x \in H^# by rewrite !inE ntx (subsetP sP0H).
have rhoL_psi_x: rhoL psi x = psi x.
  rewrite cfunElock mulrb def_FTsignalizerF H1x //=.
  apply: canLR (mulKf (neq0CG _)) _; rewrite mulr_natl -sumr_const /=.
  apply: eq_bigr => g; rewrite /'R_L (negPf not_sCxL) /= setIC => /setIP[cxz].
  have Dx: x \in [set y in 'A0(L) | ~~ ('C[y] \subset L)].
    by rewrite inE (subsetP (Fcore_sub_FTsupp0 _)).
  have [_ [_ /(_ x Dx)defNx] _] := FTsupport_facts maxL.
  rewrite (cent1P cxz) -(eq_uniq_mmax defNx maxM) => [/psi_xK//|].
  by rewrite /= -cent_cycle (subset_trans (cent_sub _)).
suffices <-: rhoL psi x = chi x by split=> // g /psi_xK->.
have irrS: {subset calS <= irr L} by have [] := FT_Frobenius_coherence maxL.
have irr_chi := irrS _ Schi.
have Sgt1: (1 < size calS)%N by apply: seqInd_nontrivial Schi; rewrite ?mFT_odd.
have De: #|L : H| = e by rewrite -(index_sdprod defL).
have [] := Dade_Ind1_sub_lin cohS_H Sgt1 irr_chi Schi; rewrite ?De //.
rewrite -/tauL_H -/calS -/psi /=; set alpha := 'Ind 1 - chi.
case=>  o_tau_1 tau_alpha_1 _ [Gamma [o_tau1_Ga _ [a Za tau_alpha] _] _].
have [[Itau1 _] Dtau1] := cohS_H.
have o1calS: orthonormal calS.
  by rewrite (sub_orthonormal irrS) ?seqInd_uniq ?irr_orthonormal.
have norm_alpha: '[tauL_H alpha] = e%:R + 1.
  rewrite Dade_isometry ?(cfInd1_sub_lin_on _ Schi) ?De //.
  rewrite cfnormBd; last by rewrite cfdotC (seqInd_ortho_Ind1 _ _ Schi) ?conjC0.
  by rewrite cfnorm_Ind_cfun1 // De irrWnorm.
pose h := #|H|; have ub_a: a ^+ 2 * ((h%:R - 1) / e%:R) - 2%:R * a <= e%:R - 1.
  rewrite -[h%:R - 1](mulKf (neq0CiG L H)) -sum_seqIndC1_square // De -/calS.
  rewrite -[lhs in lhs - 1](addrK 1) -norm_alpha -[tauL_H _](subrK 1).
  rewrite cfnormDd; last by rewrite cfdotBl tau_alpha_1 cfnorm1 subrr.
  rewrite cfnorm1 addrK [in '[_]]addrC {}tau_alpha -!addrA addKr addrCA addrA.
  rewrite ler_subr_addr cfnormDd ?ler_paddr ?cfnorm_ge0 //; last first.
    rewrite cfdotBl cfdotZl cfdot_suml (orthoPr o_tau1_Ga) ?map_f // subr0.
    rewrite big1_seq ?mulr0 // => xi Sxi; rewrite cfdotZl.
    by rewrite (orthoPr o_tau1_Ga) ?map_f ?mulr0.
  rewrite cfnormB cfnormZ Cint_normK // cfdotZl cfproj_sum_orthonormal //.
  rewrite cfnorm_sum_orthonormal // Itau1 ?mem_zchar // irrWnorm ?irrS // divr1.
  rewrite chi1 divff ?neq0CG // mulr1 conj_Cint // addrAC mulr_natl.
  rewrite !ler_add2r !(mulr_suml, mulr_sumr) !big_seq ler_sum // => xi Sxi.
  rewrite irrWnorm ?irrS // !divr1 (mulrAC _^-1) -expr2 -!exprMn (mulrC _^-1).
  by rewrite normf_div normr_nat norm_Cnat // (Cnat_seqInd1 Sxi).
have [pr_p p_dv_M]: prime p /\ p %| #|M|.
  have: p \in \pi(M) by rewrite -p_rank_gt0 ltnW.
  by rewrite mem_primes => /and3P[].
have odd_p: odd p by rewrite (dvdn_odd p_dv_M) ?mFT_odd.
have pgt2: (2 < p)%N := odd_prime_gt2 odd_p pr_p.
have ub_e: e%:R <= (p%:R + 1) / 2%:R :> algC.
  rewrite ler_pdivl_mulr ?ltr0n // -natrM -mulrSr leC_nat muln2.
  have [b e_dv_pb]: exists b : bool, e %| (b.*2 + p).-1.
    by have [_ /orP[]] := Ecyclic_le_p; [exists false | exists true].
  rewrite -ltnS (@leq_trans (b.*2 + p)) //; last first.
    by rewrite (leq_add2r p _ 2) (leq_double _ 1) leq_b1.
  rewrite dvdn_double_ltn ?mFT_odd //; first by rewrite odd_add odd_double.
  by rewrite -(subnKC pgt2) !addnS.
have lb_h: p%:R ^+ 2 <= h%:R :> algC.
  rewrite -natrX leC_nat dvdn_leq ?pfactor_dvdn ?cardG_gt0 //.
  by rewrite -prankP0 (leq_trans (p_rankS p sP0H)) ?p_rank_le_logn.
have{ub_a ub_e} ub_a: p.-1.*2%:R * a ^+ 2 - 2%:R * a <= p.-1%:R / 2%:R :> algC.
  apply: ler_trans (ler_trans ub_a _); last first.
    rewrite -subn1 -subSS natrB ?ltnS ?prime_gt0 // mulrSr mulrBl.
    by rewrite divff ?pnatr_eq0 ?ler_add2r.
  rewrite ler_add2r mulrC -Cint_normK // -!mulrA !ler_wpmul2l ?normr_ge0 //.
  rewrite ler_pdivl_mulr ?gt0CG // ler_subr_addr (ler_trans _ lb_h) //.
  rewrite -muln2 natrM -mulrA -ler_subr_addr subr_sqr_1.
  rewrite -(natrB _ (prime_gt0 pr_p)) subn1 ler_wpmul2l ?ler0n //.
  by rewrite mulrC -ler_pdivl_mulr ?ltr0n.
have a0: a = 0.
  apply: contraTeq ub_a => nz_a; rewrite ltr_geF // ltr_pdivr_mulr ?ltr0n //.
  rewrite mulrC -{1}mulr_natl -muln2 natrM -mulrA mulrBr mulrCA ltr_subr_addl.
  rewrite -ltr_subr_addr -mulrBr mulr_natl mulrA -expr2 -exprMn.
  apply: ltr_le_trans (_ : 2%:R * ((a *+ 2) ^+ 2 - 1) <= _); last first.
    rewrite (mulr_natl a 2) ler_wpmul2r // ?subr_ge0.
      by rewrite sqr_Cint_ge1 ?rpredMn // mulrn_eq0.
    by rewrite leC_nat -subn1 ltn_subRL.
  rewrite -(@ltr_pmul2l _ 2%:R) ?ltr0n // !mulrA -expr2 mulrBr -exprMn mulr1.
  rewrite -natrX 2!mulrnAr -[in rhs in _ < rhs]mulrnAl -mulrnA.
  rewrite ltr_subr_addl -ltr_subr_addr -(ltr_add2r 1) -mulrSr -sqrrB1.
  rewrite -Cint_normK ?rpredB ?rpredM ?rpred_nat ?rpred1 //.
  rewrite (@ltr_le_trans _ (3 ^ 2)%:R) ?ltC_nat // natrX.
  rewrite ler_sqr ?qualifE ?ler0n ?normr_ge0 //.
  rewrite (ler_trans _ (ler_sub_dist _ _)) // normr1 normrM normr_nat.
  by rewrite ler_subr_addl -mulrS mulr_natl ler_pmuln2r ?norm_Cint_ge1.
pose chi0 := 'Ind[L, H] 1.
have defS1: perm_eq (seqIndT H L) (chi0 :: calS).
  by rewrite [calS]seqIndC1_rem // perm_to_rem ?seqIndT_Ind1.
have [c _ -> // _] := invDade_seqInd_sum (FT_DadeF_hyp maxL) psi defS1.
have psi_alpha_1: '[psi, tauL_H alpha] = -1.
  rewrite tau_alpha a0 scale0r addr0 addrC addrA cfdotBr cfdotDr.
  rewrite (orthoPr o_tau_1) ?(orthoPr o_tau1_Ga) ?map_f // !add0r.
  by rewrite Itau1 ?mem_zchar ?map_f // irrWnorm ?irrS.
rewrite (bigD1_seq chi) ?seqInd_uniq //= big1_seq => [|xi /andP[chi'xi Sxi]].
  rewrite addr0 -cfdotC chi1 cfInd1 ?gFsub // cfun11 mulr1 De divff ?neq0CG //.
  rewrite scale1r -opprB linearN cfdotNr psi_alpha_1 opprK.
  by rewrite irrWnorm ?irrS // divr1 mul1r.
rewrite -cfdotC cfInd1 ?gFsub // cfun11 mulr1.
rewrite /chi0 -(canLR (subrK _) (erefl alpha)) scalerDr opprD addrCA -scaleNr.
rewrite linearD linearZ /= cfdotDr cfdotZr psi_alpha_1 mulrN1 rmorphN opprK.
rewrite -/tauL_H -Dtau1 ?zcharD1_seqInd ?(seqInd_sub_lin_vchar _ Schi) ?De //.
have [_ ooS] := orthonormalP o1calS.
rewrite raddfB cfdotBr Itau1 ?mem_zchar // ooS // mulrb ifN_eqC // add0r.
rewrite -De raddfZ_Cnat ?(dvd_index_seqInd1 _ Sxi) // De cfdotZr.
by rewrite Itau1 ?mem_zchar ?ooS // eqxx mulr1 subrr !mul0r.
Qed.

Let rhoM := invDade (FT_DadeF_hyp maxM).

Let rhoM_psi :
  [/\ {in K^#, rhoM psi =1 psi},
      {in K :\: K' &, forall g1 g2, psi g1 = psi g2}
    & {in K :\: K', forall g, psi g \in Cint}].
Proof.
have pr_p: prime p.
  by have:= ltnW prankM; rewrite p_rank_gt0 mem_primes => /andP[].
have [sP0M pP0 _] := and3P sylP0; have abelP01 := Ohm1_abelem pP0 abP0.
have not_frobM: ~~ [Frobenius M with kernel K].
  apply: contraL prankM => /(set_Frobenius_compl defM)frobM.
  rewrite -leqNgt -(p_rank_Sylow sylP0) -p_rank_Ohm1 p_rank_abelem //.
  rewrite -abelem_cyclic // (cyclicS (Ohm_sub _ _)) //.
  have sP0ML: P0 \subset M :&: L.
    by rewrite subsetI sP0M (subset_trans sP0H) ?gFsub.
  rewrite nil_Zgroup_cyclic ?(pgroup_nil pP0) // (ZgroupS sP0ML) //.
  have [U [MtypeF _]] := FTtypeP 1 maxM Mtype1.
  by have{MtypeF} /typeF_context[_ <- _] := compl_of_typeF defM MtypeF.
pose rmR := sval (Rgen maxL Ltype1).
have Zpsi: psi \in 'Z[rmR chi].
  case: (Rgen _ _) @rmR => /= rmR []; rewrite -/calS => scohS _ _.
  have sSS: cfConjC_subset calS calS by apply: seqInd_conjC_subset1.
  have [B /mem_subseq sBR Dpsi] := mem_coherent_sum_subseq scohS sSS cohS Schi.
  by rewrite [psi]Dpsi big_seq rpred_sum // => xi /sBR/mem_zchar->.
have part1: {in K^#, rhoM psi =1 psi}.
  move=> g K1g; rewrite /= cfunElock mulrb def_FTsignalizerF K1g //= /'R_M.
  have [_ | sCg'M] := ifPn; first by rewrite cards1 big_set1 invr1 mul1r mul1g.
  have Dg: g \in [set z in 'A0(M) | ~~ ('C[z] \subset M)].
    by rewrite inE (subsetP (Fcore_sub_FTsupp0 _)).
  have [_ [_ /(_ g Dg)maxN] /(_ g Dg)[_ _ ANg Ntype12]] := FTsupport_facts maxM.
  have{maxN} [maxN sCgN] := mem_uniq_mmax maxN.
  have{Ntype12} Ntype1: FTtype 'N[g] == 1%N.
    have [] := Ntype12; rewrite -(mem_iota 1 2) !inE => /orP[// | Ntype2] frobM.
    by have /negP[] := not_frobM; apply/frobM/Ntype2.
  have not_frobN: ~~ [Frobenius 'N[g] with kernel 'N[g]`_\F].
    apply/Frobenius_kerP=> [[_ _ _ regFN]].
    have [/bigcupP[y]] := setDP ANg; rewrite FTsupp1_type1 Ntype1 //.
    by move=> /regFN sCyF /setD1P[ntg cNy_g]; rewrite 2!inE ntg (subsetP sCyF).
  have LG'N: gval 'N[g] \notin L :^: G.
    by apply: contra not_frobN => /imsetP[y _ ->]; rewrite FcoreJ FrobeniusJker.
  suff /(eq_bigr _)->: {in 'C_('N[g]`_\F)[g], forall z, psi (z * g)%g = psi g}.
    by rewrite sumr_const -[psi g *+ _]mulr_natl mulKf ?neq0CG.
  move=> z /setIP[Fz /cent1P cgz].
  have{Fz cgz}: (z * g \in g *: 'N[g]`_\F)%g by rewrite cgz mem_lcoset mulKg.
  apply: FTtype1_ortho_constant => [phi calMphi|].
    apply/orthoPl=> nu /memv_span; apply: span_orthogonal (zchar_span Zpsi).
    exact: FTtype1_seqInd_ortho.
  have [/(subsetP (FTsupp_sub _))/setD1P[ntg Ng]] := setDP ANg.
  by rewrite FTsupp1_type1 //= !inE ntg Ng andbT.
have part2: {in K :\: K' &, forall g1 g2, psi g1 = psi g2}.
  have /subsetP sK1_K: K :\: K' \subset K^# by rewrite setDS ?sub1G.
  have LG'M: gval M \notin L :^: G.
    apply: contra not_frobM => /imsetP[y _ /= ->].
    by rewrite FcoreJ FrobeniusJker.
  move=> g1 g2 Kg1 Kg2; rewrite /= -!part1 ?sK1_K //.
  apply: FtypeI_invDade_ortho_constant => // phi calMphi.
  apply/orthoPl=> nu /memv_span; apply: span_orthogonal (zchar_span Zpsi).
  exact: FTtype1_seqInd_ortho.
split=> // g KK'g; pose nKK' : algC := #|K :\: K'|%:R.
pose nK : algC := #|K|%:R; pose nK' : algC := #|K'|%:R.
have nzKK': nKK' != 0 by rewrite pnatr_eq0 cards_eq0; apply/set0Pn; exists g.
have Dpsi_g: nK * '['Res[K] psi, 1] = nK' * '['Res[K'] psi, 1] + nKK' * psi g.
  rewrite !mulVKf ?neq0CG // (big_setID K') (setIidPr (gFsub _ _)) /=.
  rewrite mulr_natl -sumr_const; congr (_ + _); apply: eq_bigr => z K'z.
    by rewrite !cfun1E !cfResE ?subsetT ?(subsetP (der_sub 1 K)) ?K'z.
  have [Kz _] := setDP K'z; rewrite cfun1E Kz conjC1 mulr1 cfResE ?subsetT //.
  exact: part2.
have{Zpsi} Zpsi: psi \in 'Z[irr G] by have [[_ ->//]] := cohS; apply: mem_zchar.
have Qpsi1 R: '['Res[R] psi, 1] \in Crat.
  by rewrite rpred_Cint ?Cint_cfdot_vchar ?rpred1 ?cfRes_vchar.
apply: Cint_rat_Aint (Aint_vchar g Zpsi).
rewrite -[psi g](mulKf nzKK') -(canLR (addKr _) Dpsi_g) addrC mulrC.
by rewrite rpred_div ?rpredB 1?rpredM ?rpred_nat ?Qpsi1.
Qed.

(* This is the main part of Peterfalvi (12.16). *)
Lemma FTtype1_nonFrobenius_witness_contradiction : False.
Proof.
have pr_p: prime p.
  by have:= ltnW prankM; rewrite p_rank_gt0 mem_primes => /andP[].
have [sP0M pP0 _] := and3P sylP0; have abelP01 := Ohm1_abelem pP0 abP0.
have [ntx P01x] := setD1P P0_1s_x.
have ox: #[x] = p := abelem_order_p abelP01 P01x ntx.
have odd_p: odd p by rewrite -ox mFT_odd.
have pgt2 := odd_prime_gt2 odd_p pr_p.
have Zpsi: psi \in 'Z[irr G] by have [[_ ->//]] := cohS; apply: mem_zchar.
have lb_psiM: '[rhoM psi] >= #|K :\: K'|%:R / #|M|%:R * e.-1%:R ^+ 2.
  have [g /setIP[Kg cxg] notK'g] := subsetPn not_sCxK'.
  have KK'g: g \in K :\: K' by rewrite !inE notK'g.
  have [rhoMid /(_ _ g _ KK'g)psiKK'_id /(_ g KK'g)Zpsig] := rhoM_psi.
  rewrite -mulrA mulrCA ler_pmul2l ?invr_gt0 ?gt0CG // mulr_natl.
  rewrite (big_setID (K :\: K')) (setIidPr _) ?subDset ?subsetU ?gFsub ?orbT //.
  rewrite ler_paddr ?sumr_ge0 // => [z _|]; first exact: mul_conjC_ge0.
  rewrite -sumr_const ler_sum // => z KK'z.
  rewrite {}rhoMid ?(subsetP _ z KK'z) ?setDS ?sub1G // {}psiKK'_id {z KK'z}//.
  rewrite -normCK ler_sqr ?qualifE ?ler0n ?normr_ge0 //.
  have [eps prim_eps] := C_prim_root_exists (prime_gt0 pr_p).
  have psi_xg: (psi (x * g)%g == e%:R %[mod 1 - eps])%A.
    have [-> // _] := rhoL_psi; rewrite -[x]mulg1 -chi1.
    rewrite (vchar_ker_mod_prim prim_eps) ?group1 ?(seqInd_vcharW Schi) //.
    rewrite (subsetP _ _ P01x) // (subset_trans (Ohm_sub 1 _)) //.
    by rewrite (subset_trans sP0H) ?gFsub.
  have{psi_xg} /dvdCP[a Za /(canRL (subrK _))->]: (p %| psi g - e%:R)%C.
    rewrite (int_eqAmod_prime_prim prim_eps) ?rpredB ?rpred_nat // eqAmod0.
    apply: eqAmod_trans psi_xg; rewrite eqAmod_sym.
    by rewrite (vchar_ker_mod_prim prim_eps) ?in_setT.
  have [-> | nz_a] := eqVneq a 0.
    by rewrite mul0r add0r normr_nat leC_nat leq_pred.
  rewrite -[e%:R]opprK (ler_trans _ (ler_sub_dist _ _)) // normrN normrM.
  rewrite ler_subr_addl !normr_nat -natrD.
  apply: ler_trans (_ : 1 * p%:R <= _); last first.
    by rewrite ler_wpmul2r ?ler0n ?norm_Cint_ge1.
  rewrite mul1r leC_nat -subn1 addnBA ?cardG_gt0 // leq_subLR addnn -ltnS.
  have [b e_dv_pb]: exists b : bool, e %| (b.*2 + p).-1.
    by have [_ /orP[]] := Ecyclic_le_p; [exists false | exists true].
  apply: (@leq_trans (b.*2 + p)); last first.
    by rewrite (leq_add2r p _ 2) (leq_double b 1) leq_b1.
  rewrite dvdn_double_ltn ?odd_add ?mFT_odd ?odd_double //.
  by rewrite addnC -(subnKC pgt2).
have irrS: {subset calS <= irr L} by have [] := FT_Frobenius_coherence maxL.
have lb_psiL: '[rhoL psi] >= 1 - e%:R / #|H|%:R.
  have irr_chi := irrS _ Schi.
  have Sgt1: (1 < size calS)%N by apply: seqInd_nontrivial (mFT_odd _) _ _ Schi.
  have De: #|L : H| = e by rewrite -(index_sdprod defL).
  have [|_] := Dade_Ind1_sub_lin cohS_H Sgt1 irr_chi Schi; rewrite De //=.
  by rewrite -De odd_Frobenius_index_ler ?mFT_odd // => -[_ _ []//].
have tiA1_LM: [disjoint 'A1~(L) & 'A1~(M)].
  apply: FT_Dade1_support_disjoint => //.
  apply: contraL p'K => /= /imsetP[z _ ->]; rewrite FcoreJ pgroupJ.
  by rewrite p'groupEpi (piSg sP0H) // -p_rank_gt0 prankP0.
have{tiA1_LM} ub_rhoML: '[rhoM psi] + '[rhoL psi] < 1.
  have [[Itau1 Ztau1] _] := cohS.
  have n1psi: '[psi] = 1 by rewrite Itau1 ?mem_zchar ?irrWnorm ?irrS.
  rewrite -n1psi (cfnormE (cfun_onG psi)) (big_setD1 1%g) ?group1 //=.
  rewrite mulrDr ltr_spaddl 1?mulr_gt0 ?invr_gt0 ?gt0CG ?exprn_gt0 //.
    have /dirrP[s [i ->]]: psi \in dirr G.
      by rewrite dirrE Ztau1 ?mem_zchar ?n1psi /=.
    by rewrite cfunE normrMsign normr_gt0 irr1_neq0.
  rewrite (big_setID 'A1~(M)) mulrDr ler_add //=.
    rewrite FTsupp1_type1 // -FT_DadeF_supportE.
    by rewrite (setIidPr _) ?Dade_support_subD1 ?leC_cfnorm_invDade_support.
  rewrite (big_setID 'A1~(L)) mulrDr ler_paddr //=.
    rewrite mulr_ge0 ?invr_ge0 ?ler0n ?sumr_ge0 // => z _.
    by rewrite exprn_ge0 ?normr_ge0.
  rewrite (setIidPr _); last first.
    by rewrite subsetD tiA1_LM -FT_Dade1_supportE Dade_support_subD1.
  by rewrite FTsupp1_type1 // -FT_DadeF_supportE leC_cfnorm_invDade_support.
have ubM: (#|M| <= #|K| * #|H|)%N.
  by rewrite -(sdprod_card defM) leq_mul // subset_leq_card.
have{lb_psiM lb_psiL ub_rhoML ubM} ubK: (#|K / K'|%g < 4)%N.
  rewrite card_quotient ?gFnorm -?ltC_nat //.
  rewrite -ltf_pinv ?qualifE ?gt0CiG ?ltr0n // natf_indexg ?gFsub //.
  rewrite invfM invrK mulrC -(subrK #|K|%:R #|K'|%:R) mulrDl divff ?neq0CG //.
  rewrite -opprB mulNr addrC ltr_subr_addl -ltr_subr_addr.
  have /Frobenius_context[_ _ ntE _ _] := set_Frobenius_compl defL frobL.
  have egt2: (2 < e)%N by rewrite odd_geq ?mFT_odd ?cardG_gt1. 
  have e1_gt0: 0 < e.-1%:R :> algC by rewrite ltr0n -(subnKC egt2).
  apply: ltr_le_trans (_ : e%:R / e.-1%:R ^+ 2 <= _).
    rewrite ltr_pdivl_mulr ?exprn_gt0 //.
    rewrite -(@ltr_pmul2r _ #|H|%:R^-1) ?invr_gt0 ?gt0CG // mulrAC.
    rewrite -(ltr_add2r 1) -ltr_subl_addl -addrA.
    apply: ler_lt_trans ub_rhoML; rewrite ler_add //.
    apply: ler_trans lb_psiM; rewrite -natrX ler_wpmul2r ?ler0n //.
    rewrite cardsD (setIidPr _) ?gFsub // -natrB ?subset_leq_card ?gFsub //.
    rewrite -mulrA ler_wpmul2l ?ler0n //.
    rewrite ler_pdivr_mulr ?gt0CG // ler_pdivl_mull ?gt0CG //.
    by rewrite ler_pdivr_mulr ?gt0CG // mulrC -natrM leC_nat.
  rewrite -(ler_pmul2l (gt0CG E)) -/e mulrA -expr2 invfM -exprMn.
  apply: ler_trans (_ : (1 + 2%:R^-1) ^+ 2 <= _).
    rewrite ler_sqr ?rpred_div ?rpredD ?rpred1 ?rpredV ?rpred_nat //.
    rewrite -{1}(ltn_predK egt2) mulrSr mulrDl divff ?gtr_eqF // ler_add2l.
    rewrite ler_pdivr_mulr // ler_pdivl_mull ?ltr0n //.
    by rewrite mulr1 leC_nat -(subnKC egt2).
  rewrite -(@ler_pmul2r _ (2 ^ 2)%:R) ?ltr0n // {1}natrX -exprMn -mulrA.
  rewrite mulrDl mulrBl !mul1r !mulVf ?pnatr_eq0 // (mulrSr _ 3) addrK.
  by rewrite -mulrSr ler_wpmul2r ?ler0n ?ler_nat.
have [U [MtypeF _]] := FTtypeP 1 maxM Mtype1.
have{U MtypeF} [_ _ [U0 [sU0ML expU0 frobU0]]] := compl_of_typeF defM MtypeF.
have [/sdprodP[_ _ nKU0 tiKU0] ntK _ _ _] := Frobenius_context frobU0.
have nK'U0: U0 \subset 'N(K') := char_norm_trans (der_char 1 K) nKU0.
have frobU0K': [Frobenius K <*> U0 / K' = (K / K') ><| (U0 / K')]%g.
  have solK: solvable K by rewrite ?nilpotent_sol ?Fcore_nil.
  rewrite  Frobenius_proper_quotient ?(sol_der1_proper solK) // /(_ <| _).
  by rewrite (subset_trans (der_sub 1 _)) ?joing_subl // join_subG gFnorm.
have isoU0: U0 \isog U0 / K'.
  by rewrite quotient_isog //; apply/trivgP; rewrite -tiKU0 setSI ?gFsub.
have piU0p: p \in \pi(U0 / K')%g.
  rewrite /= -(card_isog isoU0) -pi_of_exponent expU0 pi_of_exponent.
  rewrite mem_primes pr_p cardG_gt0 /= -ox order_dvdG // (subsetP _ _ P01x) //.
  rewrite (subset_trans (Ohm_sub 1 _)) // subsetI sP0M.
  by rewrite (subset_trans sP0H) ?gFsub.
have /(Cauchy pr_p)[z U0z oz]: p %| #|U0 / K'|%g.
  by rewrite mem_primes in piU0p; case/and3P: piU0p.
have frobKz: [Frobenius (K / K') <*> <[z]> = (K / K') ><| <[z]>]%g.
  rewrite (Frobenius_subr _ _ frobU0K') ?cycle_subG //.
  by rewrite cycle_eq1 -order_gt1 oz ltnW.
have: p %| #|K / K'|%g.-1 by rewrite -oz (Frobenius_dvd_ker1 frobKz) //.
have [_ ntKK' _ _ _] := Frobenius_context frobKz.
rewrite -subn1 gtnNdvd ?subn_gt0 ?cardG_gt1 // subn1 prednK ?cardG_gt0 //.
by rewrite -ltnS (leq_trans ubK).
Qed.

End Twelve_13_to_16.

Lemma FTtype1_nonFrobenius_contradiction : False.
Proof.
have [_ [tau1 cohS]] := FT_Frobenius_coherence maxL frobL.
have [chi] := FTtype1_ref_irr maxL; rewrite -(index_sdprod defL).
exact: FTtype1_nonFrobenius_witness_contradiction cohS.
Qed.

End Twelve_8_to_16.

(* This is Peterfalvi, Theorem (12.7). *)
Theorem FTtype1_Frobenius M :
  M \in 'M -> FTtype M == 1%N -> [Frobenius M with kernel M`_\F].
Proof.
set K := M`_\F => maxM Mtype1; have [U [MtypeF _]] := FTtypeP 1 maxM Mtype1.
have hallU: \pi(K)^'.-Hall(M) U.
  by rewrite -(compl_pHall U (Fcore_Hall M)) sdprod_compl; have [[]] := MtypeF.
apply: FrobeniusWker (U) _ _; have{MtypeF} [_ -> _] := typeF_context MtypeF.
apply/forall_inP=> P0 /SylowP[p _ sylP0].
rewrite (odd_pgroup_rank1_cyclic (pHall_pgroup sylP0)) ?mFT_odd // leqNgt.
apply/negP=> prankP0.
have piUp: p \in \pi(U) by rewrite -p_rank_gt0 -(p_rank_Sylow sylP0) ltnW.
have{piUp} K'p: p \in \pi(K)^' := pnatPpi (pHall_pgroup hallU) piUp.
have{U hallU sylP0} sylP0: p.-Sylow(M) P0 := subHall_Sylow hallU K'p sylP0.
have{P0 sylP0 prankP0} prankM: (1 < 'r_p(M))%N by rewrite -(p_rank_Sylow sylP0).
case/negP: K'p => /=.
elim: {p}_.+1 {-2}p M @K (ltnSn p) maxM Mtype1 prankM => // p IHp q M K.
rewrite ltnS leq_eqVlt => /predU1P[->{q} | /(IHp q M)//] maxM Mtype1 prankM.
apply/idPn; rewrite -p'groupEpi /= -/K => p'K.
have [P0 sylP0] := Sylow_exists p M.
have [] := non_Frobenius_FTtype1_witness maxM Mtype1 prankM p'K sylP0.
move=> abP0 prankP0 [L [maxL sP0_Ls [x P01s_x []]]].
exact: (FTtype1_nonFrobenius_contradiction IHp) P01s_x. 
Qed.

(* This is Peterfalvi, Theorem (12.17). *)
Theorem not_all_FTtype1 : ~~ all_FTtype1 gT.
Proof.
apply/negP=> allT1; pose k := #|'M^G|.
have [partGpi coA1 _ [injA1 /(_ allT1)partG _]] := FT_Dade_support_partition gT.
move/forall_inP in allT1.
have [/subsetP maxMG _ injMG exMG] := mmax_transversalP gT.
have{partGpi exMG} kge2: (k >= 2)%N.
  have [L MG_L]: exists L, L \in 'M^G.
    by have [L maxL] := any_mmax gT; have [x] := exMG L maxL; exists (L :^ x)%G.
  have maxL := maxMG L MG_L; have Ltype1 := allT1 L maxL.
  have /Frobenius_kerP[_ ltHL nsHL _] := FTtype1_Frobenius maxL Ltype1.
  rewrite ltnNge; apply: contra (proper_subn ltHL) => leK1.
  rewrite (sub_normal_Hall (Fcore_Hall L)) // (pgroupS (subsetT L)) //=.
  apply: sub_pgroup (pgroup_pi _) => p; rewrite partGpi => /exists_inP[M maxM].
  have /eqP defMG: [set L] == 'M^G by rewrite eqEcard sub1set MG_L cards1.
  have [x] := exMG M maxM; rewrite -defMG => /set1P/(canRL (actK 'JG _))-> /=.
  by rewrite FTcoreJ cardJg FTcore_type1.
pose L (i : 'I_k) : {group gT} := enum_val i; pose H i := (L i)`_\F%G.
have MG_L i: L i \in 'M^G by apply: enum_valP.
have maxL i: L i \in 'M by apply: maxMG.
have defH i: (L i)`_\s = H i by rewrite FTcore_type1 ?allT1.
pose frobL_P i E := [Frobenius L i = H i ><| gval E].
have /fin_all_exists[E frobHE] i: exists E, frobL_P i E.
  by apply/existsP/FTtype1_Frobenius; rewrite ?allT1.
have frobL i: [/\ L i \subset G, solvable (L i) & frobL_P i (E i)].
  by rewrite subsetT mmax_sol.
have{coA1} coH_ i j: i != j -> coprime #|H i| #|H j|.
  move=> j'i; rewrite -!defH coA1 //; apply: contra j'i => /imsetP[x Gx defLj].
  apply/eqP/enum_val_inj; rewrite -/(L i) -/(L j); apply: injMG => //.
  by rewrite defLj; apply/esym/orbit_act.
have tiH i: normedTI (H i)^# G (L i).
  have ntA: (H i)^# != set0 by rewrite setD_eq0 subG1 mmax_Fcore_neq1.
  apply/normedTI_memJ_P=> //=; rewrite subsetT; split=> // x z H1x Gz.
  apply/idP/idP=> [H1xz | Lz]; last first.
    by rewrite memJ_norm // (subsetP _ z Lz) // normD1 gFnorm.
  have /subsetP sH1A0: (H i)^# \subset 'A0(L i) by apply: Fcore_sub_FTsupp0.
  have [/(sub_in2 sH1A0)wccH1 [_ maxN] Nfacts] := FTsupport_facts (maxL i).
  suffices{z Gz H1xz wccH1} sCxLi: 'C[x] \subset L i.
    have /imsetP[y Ly defxz] := wccH1 _ _ H1x H1xz (mem_imset _ Gz).
    rewrite -[z](mulgKV y) groupMr // (subsetP sCxLi) // !inE conjg_set1.
    by rewrite conjgM defxz conjgK.
  apply/idPn=> not_sCxM; pose D := [set y in 'A0(L i) | ~~ ('C[y] \subset L i)].
  have Dx: x \in D by rewrite inE sH1A0.
  have{maxN} /mem_uniq_mmax[maxN sCxN] := maxN x Dx.
  have Ntype1 := allT1 _ maxN.
  have [_ _ /setDP[/bigcupP[y NFy /setD1P[ntx cxy]] /negP[]]] := Nfacts x Dx.
  rewrite FTsupp1_type1 Ntype1 // in NFy cxy *.
  have /Frobenius_kerP[_ _ _ regFN] := FTtype1_Frobenius maxN Ntype1.
  by rewrite 2!inE ntx (subsetP (regFN y NFy)).
have /negP[] := no_coherent_Frobenius_partition (mFT_odd _) kge2 frobL tiH coH_.
rewrite eqEsubset sub1set !inE andbT; apply/andP; split; last first.
  apply/bigcupP=> [[i _ /imset2P[x y /setD1P[ntx _] _ Dxy]]].
  by rewrite -(conjg_eq1 x y) -Dxy eqxx in ntx.
rewrite subDset setUC -subDset -(cover_partition partG).
apply/bigcupsP=> _ /imsetP[Li MG_Li ->]; pose i := enum_rank_in MG_Li Li.
rewrite (bigcup_max i) //=; have ->: Li = L i by rewrite /L enum_rankK_in.
rewrite -FT_Dade1_supportE //; apply/bigcupsP=> x A1x; apply: imset2S => //.
move: (FT_Dade1_hyp _) (tiH i); rewrite -defH => _ /Dade_normedTI_P[_ -> //].
by rewrite mul1g sub1set -/(H i) -defH.
Qed.

End PFTwelve.

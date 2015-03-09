(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime binomial ssralg poly finset.
Require Import fingroup morphism perm automorphism quotient action finalg zmodp.
Require Import gfunctor gproduct center cyclic commutator gseries nilpotent.
Require Import pgroup sylow hall abelian maximal frobenius.
Require Import matrix mxalgebra mxrepresentation mxabelem vector.
Require Import BGsection1 BGsection3 BGsection7.
Require Import BGsection14 BGsection15 BGsection16.
Require Import ssrnum rat algC cyclotomic algnum.
Require Import classfun character integral_char inertia vcharacter.
Require Import PFsection1 PFsection2 PFsection3 PFsection4.
Require Import PFsection5 PFsection6 PFsection7 PFsection8 PFsection9.
Require Import PFsection10 PFsection11 PFsection12.

(******************************************************************************)
(* This file covers Peterfalvi, Section 13: The Subgroups S and T.            *)
(* The following definitions will be used in PFsection14:                     *)
(*  FTtypeP_bridge StypeP j == a virtual character of S that mixes characters *)
(* (locally) beta_ j, betaS    that do and do not contain P = S`_\F in their  *)
(*                             kernels, for StypeP : of_typeP S U defW.       *)
(*                          := 'Ind[S, P <*> W1] 1 - mu2_ 0 j.                *)
(*  FTtypeP_bridge_gap StypeP == the difference between the image of beta_ j  *)
(*  (locally) Gamma, GammaS   under the Dade isometry for S, and its natural  *)
(*                            value, 1 - eta_ 0 j (this does not actually     *)
(*                            depend on j != 0).                              *)
(* The following definitions are only used locally across sections:           *)
(*                      #1 == the irreducible index 1 (i.e., inord 1).        *)
(*   irr_Ind_Fittinq S chi <=>  chi is an irreducible character of S induced  *)
(*    (locally) irrIndH       from an irreducible character of 'F(S) (which   *)
(*                            will be linear here, as 'F(S) is abelian).      *)
(*   typeP_TIred_coherent StypeP tau1 <=> tau1 maps the reducible induced     *)
(*                            characters mu_ j of a type P group S, which are *)
(*                            the image under the cyclic TI isometry to S of  *)
(*                            row sums of irreducibles of W = W1 x W2, to     *)
(*                            the image of that sum under the cyclic TI       *)
(*                            isometry to G (except maybe for a sign change   *)
(*                            if p = #|W2| = 3).                              *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory FinRing.Theory Num.Theory.

Section Thirteen.

Variable gT : minSimpleOddGroupType.
Local Notation G := (TheMinSimpleOddGroup gT).
Implicit Types (p q : nat) (x y z : gT).
Implicit Types H K L N P Q R S T U W : {group gT}.

Definition irr_Ind_Fitting S := [predI irr S & seqIndT 'F(S) S].

Local Notation irrIndH := (irr_Ind_Fitting _).
Local Notation "#1" := (inord 1) (at level 0).

Section Thirteen_2_3_5_to_9.

(* These assumptions correspond to the part of Peterfalvi, Hypothesis (13.1)  *)
(* that is used to prove (13.2-3) and (13.5-9). Because of the shortcomings   *)
(* of Coq's Section and Module features we will need to repeat most of these  *)
(* assumptions twice down this file to exploit the symmetry between S and T.  *)
(*   We anticipate the use of the letter 'H' to designate the Fitting group   *)
(* of S, which Peterfalvi does only locally in (13.5-9), in order not to      *)
(* conflict with (13.17-19), where H denotes the F-core of a Frobenius group. *)
(* This is not a problem for us, since these lemmas will only appear in the   *)
(* last section of this file, and we will have no use for H at that point     *)
(* since we will have shown in (13.12) that H coincides with P = S`_\F.       *)

Variables S U W W1 W2 : {group gT}.
Hypotheses (maxS : S \in 'M) (defW : W1 \x W2 = W).
Hypotheses (StypeP : of_typeP S U defW).

Local Notation "` 'W1'" := (gval W1) (at level 0, only parsing) : group_scope.
Local Notation "` 'W2'" := (gval W2) (at level 0, only parsing) : group_scope.
Local Notation "` 'W'" := (gval W) (at level 0, only parsing) : group_scope.
Local Notation V := (cyclicTIset defW).

Local Notation "` 'S'" := (gval S) (at level 0, only parsing) : group_scope.
Local Notation P := `S`_\F%G.
Local Notation "` 'P'" := `S`_\F (at level 0) : group_scope.
Local Notation PU := S^`(1)%G.
Local Notation "` 'PU'" := `S^`(1) (at level 0) : group_scope.
Local Notation "` 'U'" := (gval U) (at level 0, only parsing) : group_scope.
Local Notation C := 'C_U(`P)%G.
Local Notation "` 'C'" := 'C_`U(`P) (at level 0) : group_scope.
Local Notation H := 'F(S)%G.
Local Notation "` 'H'" := 'F(`S) (at level 0) : group_scope.

Let defS : PU ><| W1 = S. Proof. by have [[]] := StypeP. Qed.
Let defPU : P ><| U = PU. Proof. by have [_ []] := StypeP. Qed.
Let defH : P \x C = H. Proof. by have [] := typeP_context StypeP. Qed.

Let notStype1 : FTtype S != 1%N. Proof. exact: FTtypeP_neq1 StypeP. Qed.
Let notStype5 : FTtype S != 5%N. Proof. exact: FTtype5_exclusion maxS. Qed.

Let pddS := FT_prDade_hypF maxS StypeP.
Let ptiWS : primeTI_hypothesis S PU defW := FT_primeTI_hyp StypeP.
Let ctiWG : cyclicTI_hypothesis G defW := pddS.

Let ntW1 : W1 :!=: 1. Proof. by have [[]] := StypeP. Qed.
Let ntW2 : W2 :!=: 1. Proof. by have [_ _ _ []] := StypeP. Qed.
Let cycW1 : cyclic W1. Proof. by have [[]] := StypeP. Qed.
Let cycW2 : cyclic W2. Proof. by have [_ _ _ []] := StypeP. Qed.

Let p := #|W2|.
Let q := #|W1|.
Let c := #|C|.
Let u := #|U : C|.

Let oU : #|U| = (u * c)%N. Proof. by rewrite mulnC Lagrange ?subsetIl. Qed.

Let pr_p : prime p. Proof. by have [] := FTtypeP_primes maxS StypeP. Qed.
Let pr_q : prime q. Proof. by have [] := FTtypeP_primes maxS StypeP. Qed.

Let qgt2 : q > 2. Proof. by rewrite odd_gt2 ?mFT_odd ?cardG_gt1. Qed.
Let pgt2 : p > 2. Proof. by rewrite odd_gt2 ?mFT_odd ?cardG_gt1. Qed.

Let coPUq : coprime #|PU| q.
Proof. by rewrite (coprime_sdprod_Hall_r defS); have [[]] := StypeP. Qed.

Let nirrW1 : #|Iirr W1| = q. Proof. by rewrite card_Iirr_cyclic. Qed.
Let nirrW2 : #|Iirr W2| = p. Proof. by rewrite card_Iirr_cyclic. Qed.
Let NirrW1 : Nirr W1 = q. Proof. by rewrite -nirrW1 card_ord. Qed.
Let NirrW2 : Nirr W2 = p. Proof. by rewrite -nirrW2 card_ord. Qed.

Local Open Scope ring_scope.

Let sigma := (cyclicTIiso ctiWG).
Let w_ i j := (cyclicTIirr defW i j).
Local Notation eta_ i j := (sigma (w_ i j)).

Local Notation Imu2 := (primeTI_Iirr ptiWS).
Let mu2_ i j := primeTIirr ptiWS i j.
Let mu_ := primeTIred ptiWS.
Local Notation chi_ j := (primeTIres ptiWS j).

Local Notation Idelta := (primeTI_Isign ptiWS).
Local Notation delta_ j := (primeTIsign ptiWS j).

Local Notation tau := (FT_Dade0 maxS).
Local Notation "chi ^\tau" := (tau chi).

Let calS0 := seqIndD PU S S`_\s 1.
Let rmR := FTtypeP_coh_base maxS StypeP.
Let scohS0 : subcoherent calS0 tau rmR.
Proof. exact: FTtypeP_subcoherent StypeP. Qed.

Let calS := seqIndD PU S P 1.
Let sSS0 : cfConjC_subset calS calS0.
Proof. exact/seqInd_conjC_subset1/Fcore_sub_FTcore. Qed.

Local Notation type34ker1 := (FTtype34_Fcore_kernel_trivial maxS StypeP).
Local Notation type34facts := (FTtype34_structure maxS StypeP).
Local Notation type2facts := (FTtypeII_prime_facts maxS StypeP).
Local Notation compl2facts := (compl_of_typeII maxS StypeP).
Local Notation compl3facts := (compl_of_typeIII maxS StypeP).

Local Notation H0 := (Ptype_Fcore_kernel StypeP).

Lemma Ptype_factor_prime : pdiv #|P / H0|%g = p.
Proof. exact: def_Ptype_factor_prime. Qed.
Local Notation pHbar_p := Ptype_factor_prime.

Lemma Ptype_Fcore_kernel_trivial : H0 :=: 1%g.
Proof.
have [/type2facts[_ oP _]| /type34ker1[]//] := boolP (FTtype S == 2).
have [/and3P[]] := Ptype_Fcore_kernel_exists maxS StypeP notStype5.
case/maxgroupp/andP=> /proper_sub sH0P nH0S /subset_trans/(_ nH0S)nH0P _ _.
apply: card1_trivg; rewrite -(divg_indexS sH0P) -card_quotient //.
have [_ _ ->] := Ptype_Fcore_factor_facts maxS StypeP notStype5.
by rewrite pHbar_p -{}oP divnn ?cardG_gt0.
Qed.
Local Notation H0_1 := Ptype_Fcore_kernel_trivial.

Lemma Ptype_Fcompl_kernel_cent : Ptype_Fcompl_kernel StypeP :=: C.
Proof.
rewrite [Ptype_Fcompl_kernel StypeP]unlock /= (group_inj H0_1).
by rewrite astabQ -morphpreIim -injm_cent ?injmK ?ker_coset ?norms1.
Qed.
Local Notation CHbar_C := Ptype_Fcompl_kernel_cent.

(* This is Peterfalvi (13.2). *)
Lemma FTtypeP_facts :
  [/\ (*a*) [/\ pred2 2 3 (FTtype S), q < p -> FTtype S == 2,
                [Frobenius U <*> W1 = U ><| W1] & abelian U],
      (*b*) p.-abelem P /\ #|P| = p ^ q,
      (*c*) u <= (p ^ q).-1 %/ p.-1,
      (*d*) coherent calS S^# tau
    & (*e*) normedTI 'A0(S) G S /\ {in 'CF(S, 'A0(S)), tau =1 'Ind}]%N.
Proof.
have type23: pred2 2 3 (FTtype S).
  by rewrite /= -implyNb; apply/implyP=> /type34facts[_ _ [->]].
have [_ ntU _ tiFS] := compl_of_typeII_IV maxS StypeP notStype5.
have [_ /mulG_sub[_ sUPU] nPU tiPU] := sdprodP defPU.
have cUU: abelian U by case/orP: type23 => [/compl2facts | /compl3facts] [_ ->].
split.
- split=> //; last exact: Ptype_compl_Frobenius StypeP _.
  by rewrite ltnNge; apply: contraR => /type34facts[_ /ltnW].
- by have [/type2facts[] | /type34ker1[]] := boolP (FTtype S == 2).
- have ->: u = #|U / C|%g by rewrite card_quotient ?normsI ?normG ?norms_cent.
  have p1gt0: (0 < p.-1)%N by rewrite -(subnKC pgt2).
  have [/typeP_Galois_P[]| /typeP_Galois_Pn[]]// := boolP (typeP_Galois StypeP).
    move=> _ _ [_ _]; rewrite pHbar_p CHbar_C // -/u -/q; apply: dvdn_leq.
    by rewrite divn_gt0 // -!subn1 leq_sub2r // (leq_exp2l 1) ltnW // ltnW.
  rewrite -/q CHbar_C pHbar_p => H1 [_ _ _ _ [agt1 a_dv_p1 _ [V /card_isog->]]].
  apply: leq_trans (_ : p.-1 ^ q.-1 <= _)%N; last first.
    have ltp1q: (p.-1 ^ q < p ^ q)%N by rewrite ltn_exp2r ?prednK // 2?ltnW.
    by rewrite leq_divRL // -expnSr (ltn_predK qgt2) -ltnS (ltn_predK ltp1q).
  rewrite dvdn_leq ?expn_gt0 ?p1gt0 // (dvdn_trans (cardSg (subsetT V))) //.
  by rewrite cardsT card_matrix mul1n dvdn_exp2r //= card_ord Zp_cast.
- have:= Ptype_core_coherence maxS StypeP notStype5; rewrite H0_1 CHbar_C.
  by rewrite (derG1P (abelianS _ cUU)) ?subsetIl ?(group_inj (joing1G _)).
have ntA0: 'A0(S) != set0 := FTsupp0_neq0 maxS.
suffices tiA0: normedTI 'A0(S) G S by split=> //; apply: Dade_Ind.
apply/normedTI_memJ_P=> //; rewrite subsetT; split=> // x g A0x Gg.
apply/idP/idP=> [A0xg | /(subsetP (FTsupp0_norm S))/memJ_norm->//].
apply/idPn=> S'g; have Dx: x \in [set y in 'A0(S) | ~~ ('C[y] \subset S)].
  rewrite inE A0x; have [_ _ [_ _ _ wccA0 _] _] := pddS.
  have /imsetP[y Sy Dxy]: x ^ g \in x ^: S by rewrite wccA0 // mem_orbit.
  apply/subsetPn; exists (g * y^-1)%g; last by rewrite groupMr ?groupV.
  by rewrite !inE conjg_set1 conjgM Dxy conjgK.
have [_ [_ /(_ x Dx) defL] /(_ x Dx)[_ _]] := FTsupport_facts maxS.
have{defL} [maxL _] := mem_uniq_mmax defL; set L := 'N[x] in maxL *.
rewrite -mem_iota !inE => ALx [/orP[Ltype1 _ | Ltype2]]; last first.
  by case/(_ _)/existsP=> // ? /Frobenius_of_typeF/(typePF_exclusion StypeP).
have /Frobenius_kerP[_ _ _ regLF_L] := FTtype1_Frobenius maxL Ltype1.
case/andP: ALx => A1'x /bigcupP[z A1z /setD1P[ntx cLz_z]]; case/negP: A1'x.
rewrite ntx /'A1(L) -(Fcore_eq_FTcore _ _) ?(eqP Ltype1) //= in cLz_z A1z *.
exact: subsetP (regLF_L z A1z) _ cLz_z.
Qed.

Lemma FTseqInd_TIred j : j != 0 -> mu_ j \in calS.
Proof.
move=> nz_j; rewrite -[mu_ j]cfInd_prTIres mem_seqInd ?gFnormal ?normal1 //=.
by rewrite !inE sub1G (cfker_prTIres pddS).
Qed.

Lemma FTtypeP_Fitting_abelian : abelian H.
Proof.
rewrite -(dprodW defH) abelianM subsetIr.
have [[_ _ _ cUU] [/abelem_abelian-> _] _ _ _] := FTtypeP_facts.
by rewrite (abelianS _ cUU) ?subsetIl.
Qed.
Hint Resolve FTtypeP_Fitting_abelian.

Local Notation calH := (seqIndT H S).

Lemma FTtypeP_Ind_Fitting_1 lambda : lambda \in calH -> lambda 1%g = (u * q)%:R.
Proof.
case/seqIndP=> i _ ->; rewrite cfInd1 -?divgS ?gFsub //; set theta := 'chi_i.
have Ltheta: theta \is a linear_char by apply/char_abelianP.
rewrite -(sdprod_card defS) -(sdprod_card defPU) -/q -(dprod_card defH) oU.
by rewrite -mulnA divnMl // mulnAC mulnK ?cardG_gt0 // lin_char1 ?mulr1.
Qed.
Local Notation calHuq := FTtypeP_Ind_Fitting_1.

(* This is Peterfalvi (13.3)(a). *)
Lemma FTprTIred_Ind_Fitting j : j != 0 -> mu_ j \in calH.
Proof.
move=> nz_j; have [//|_ _ _] := typeP_reducible_core_Ind maxS StypeP.
rewrite (group_inj H0_1) CHbar_C -/q /= (dprodWY defH) -/calS => /(_ (mu_ j)).
case=> [|_ _ [_ /lin_char_irr/irrP[r ->] ->]]; last exact: mem_seqIndT.
by rewrite mem_filter /= prTIred_not_irr FTseqInd_TIred.
Qed.
Local Notation Hmu := FTprTIred_Ind_Fitting.

Lemma FTprTIred1 j : j != 0 -> mu_ j 1%g = (u * q)%:R.
Proof. by move/Hmu/calHuq. Qed.
Local Notation mu1uq := FTprTIred1.

(* This is the first assertion of Peterfalvi (13.3)(c). *)
Lemma FTprTIsign j : delta_ j = 1.
Proof.
have [[_ _ frobUW1 cUU] _ _ cohS _] := FTtypeP_facts.
have [-> | nz_j] := eqVneq j 0; first exact: prTIsign0.
suffices: (1 == delta_ j %[mod q])%C.
  rewrite signrE /eqCmod addrC opprB subrK dvdC_nat.
  by case: (Idelta j); rewrite ?subr0 // gtnNdvd.
apply: eqCmod_trans (prTIirr1_mod ptiWS 0 j); rewrite -/(mu2_ 0 j) -/q.
have ->: mu2_ 0 j 1%g = u%:R.
  by apply: (mulfI (neq0CG W1)); rewrite -prTIred_1 -/mu_ mu1uq // mulnC natrM.
rewrite eqCmod_sym /eqCmod -(@natrB _ u 1) ?indexg_gt0 // subn1 dvdC_nat.
have nC_UW1: U <*> W1 \subset 'N(C).
  have /sdprodP[_ _ nPUW1 _] := Ptype_Fcore_sdprod StypeP.
  by rewrite normsI ?norms_cent // join_subG normG; have [_ []] := StypeP.
have coUq: coprime #|U| q by have /sdprod_context[_ /coprimeSg->] := defPU.
have /Frobenius_dvd_ker1: [Frobenius U <*> W1 / C = (U / C) ><| (W1 / C)].
  have [defUW1 _ _ _ _] := Frobenius_context frobUW1.
  rewrite Frobenius_coprime_quotient // /normal ?subIset ?joing_subl //.
  split=> [|x /(Frobenius_reg_ker frobUW1)->]; last exact: sub1G.
  rewrite properEneq subsetIl -CHbar_C andbT.
  by have [] := Ptype_Fcore_factor_facts maxS StypeP notStype5.
have [nCU nCW1] := joing_subP nC_UW1; rewrite !card_quotient // -/u.
by rewrite -indexgI setIC setIAC (coprime_TIg coUq) setI1g indexg1.
Qed.
Local Notation delta1 := FTprTIsign.

(* This is Peterfalvi (13.3)(b). *)
Lemma FTtypeP_no_Ind_Fitting_facts :
     ~~ has irrIndH calS ->
  [/\ typeP_Galois StypeP, `C = 1%g & u = (p ^ q).-1 %/ p.-1].
Proof.
move=> noIndH; have [[_ _ _ cUU] _ _ _ _] := FTtypeP_facts.
have [[t []] | [->]] := typeP_reducible_core_cases maxS StypeP notStype5.
  rewrite CHbar_C H0_1 (derG1P (abelianS _ cUU)) ?subsetIl //=.
  rewrite (group_inj (joing1G 1)) -/calS /= (dprodWY defH) => calSt _.
  case=> _ /lin_char_irr/irrP[r ->] Dt; case/hasP: noIndH.
  by exists 'chi_t; rewrite //= mem_irr; apply/seqIndP; exists r; rewrite ?inE.
rewrite /= pHbar_p H0_1 oU /c => frobPU _ <- _ /=.
suffices /eqP->: C :==: 1%g by rewrite cards1 muln1.
suffices: 'C_(U / 1)(P / 1) == 1%g.
  by rewrite -injm_subcent ?morphim_injm_eq1 ?norms1 ?ker_coset.
have [_ ntP _ _ _] := Frobenius_context frobPU.
by rewrite (cent_semiregular (Frobenius_reg_compl frobPU)).
Qed.

(* Helper function for (13.3)(c). *)
Let signW2 (b : bool) := iter b (@conjC_Iirr _ W2).

Let signW2K b : involutive (signW2 b).
Proof. by case: b => //; apply: conjC_IirrK. Qed.

Let signW2_eq0 b : {mono signW2 b: j / j == 0}.
Proof. by case: b => //; apply: conjC_Iirr_eq0. Qed.

(* This is a reformulation of the definition condition part of (13.3)(c) that *)
(* better fits its actual use in (13.7), (13.8) and (13.9) (note however that *)
(* the p = 3 part will in fact not be used).                                  *)
Definition typeP_TIred_coherent tau1 :=
  exists2 b : bool, b -> p = 3
  & forall j, j != 0 -> tau1 (mu_ j) = (-1) ^+ b *: \sum_i eta_ i (signW2 b j).

(* This is the main part of Peterfalvi (13.3)(c), using the definition above. *)
(* Note that the text glosses over the quantifier inversion in the second use *)
(* of (5.8) in the p = 3 case. We must rule out tau1 (mu_ k) = - tau1 (mu_ j) *)
(* by using the isometry property of tau1 (alternatively, we could use (4.8)  *)
(* to compute tau1 (mu_ k) = tau (mu_ k - mu_ j) + tau1 (mu_ j) directly).    *)
Lemma FTtypeP_coherence :
   exists2 tau1 : {additive 'CF(S) -> 'CF(G)},
     coherent_with calS S^# tau tau1 & typeP_TIred_coherent tau1.
Proof.
have [redS|] := altP (@allP _ [predC irr S] calS).
  have [k nz_k] := has_nonprincipal_irr ntW2.
  have [_ [tau1 Dtau1]] := uniform_prTIred_coherent pddS nz_k.
  set calT := uniform_prTIred_seq pddS k => cohT.
  exists tau1; last by exists false => // j _; rewrite /= Dtau1 delta1.
  apply: subset_coherent_with cohT => xi Sxi.
  have [_ _ /(_ xi)] := typeP_reducible_core_Ind maxS StypeP notStype5.
  rewrite (group_inj H0_1) mem_filter redS // => /(_ Sxi)/imageP[j nz_j ->] _.
  by rewrite image_f // inE -/mu_ [~~ _]nz_j /= !mu1uq.
rewrite all_predC negbK => /hasP[xi Sxi irr_xi].
have [_ _ _ [tau1 cohS] _] := FTtypeP_facts; exists tau1 => //.
have [|] := boolP [forall (j | j != 0), tau1 (mu_ j) == \sum_i eta_ i j].
  by move/eqfun_inP=> Dtau1; exists false => // j /Dtau1; rewrite scale1r.
rewrite negb_forall_in => /exists_inP[j nz_j /eqP tau1muj_neq_etaj].
have:= FTtypeP_coherent_TIred sSS0 cohS irr_xi Sxi (FTseqInd_TIred _).
rewrite -/mu_ -/sigma -/ptiWS => tau1mu; have [dk tau1muj Ddk] := tau1mu j nz_j.
case: Ddk tau1muj => [][-> ->]{dk}; rewrite ?signrN delta1 ?scaleNr scale1r //.
set k := conjC_Iirr j => Dmu tau1muj.
have{Dmu} defIW2 l: l != 0 -> pred2 j k l.
  by move=> nz_l; rewrite Dmu ?FTseqInd_TIred ?mu1uq.
have [nz_k j'k]: k != 0 /\ k != j.
  rewrite conjC_Iirr_eq0 nz_j -(inj_eq irr_inj) conjC_IirrE.
  by rewrite odd_eq_conj_irr1 ?mFT_odd ?irr_eq1.
have /eqP p3: p == 3.
  rewrite -nirrW2 (cardD1 0) (cardD1 j) (cardD1 k) !inE nz_j nz_k j'k !eqSS.
  by apply/pred0Pn=> [[l /and4P[k'l j'l /defIW2/norP[]]]].
exists true => // _ /defIW2/pred2P[]->; first by rewrite scaler_sign.
have [[[Itau1 _] _] [d t1muk Dd]] := (cohS, tau1mu k nz_k); move: Dd t1muk.
case=> [][-> ->] => [|_]; rewrite ?signrN delta1 // scale1r.
case/(congr1 (cfdotr (tau1 (mu_ j)) \o -%R))/eqP/idPn => /=.
rewrite -tau1muj cfdotNl eq_sym !Itau1 ?mem_zchar ?FTseqInd_TIred //.
by rewrite !cfdot_prTIred (negPf j'k) eqxx mul1n oppr0 neq0CG.
Qed.

(* We skip over (13.4), whose proof uses (13.2) and (13.3) for both groups of *)
(* a type P pair.                                                             *)

Let calS1 := seqIndD H S P 1.

(* Some facts about calS1 used implicitly throughout (13.5-8). *)
Let S1mu j : j != 0 -> mu_ j \in calS1.
Proof.
move=> nz_j; have /seqIndP[s _ Ds] := Hmu nz_j.
rewrite Ds mem_seqInd ?gFnormal ?normal1 // !inE sub1G andbT.
rewrite -(sub_cfker_Ind_irr s (gFsub _ _) (gFnorm _ _)) -Ds /=.
rewrite -[mu_ j](cfInd_prTIres (FT_prDade_hypF maxS StypeP)).
by rewrite sub_cfker_Ind_irr ?cfker_prTIres ?gFsub ?gFnorm.
Qed.

Let calSirr := [seq phi <- calS | phi \in irr S].
Let S1cases zeta :
  zeta \in calS1 -> {j | j != 0 & zeta = mu_ j} + (zeta \in 'Z[calSirr]).
Proof.
move=> S1zeta; have /sig2_eqW[t /setDP[_ kerP't] Dzeta] := seqIndP S1zeta.
rewrite inE in kerP't; have /mulG_sub[sPH _] := dprodW defH.
have [/andP[sPPU nPPU] sUPU _ _ _] := sdprod_context defPU.
have sHPU: H \subset PU by rewrite /= -(dprodWC defH) mulG_subG subIset ?sUPU.
have [/eqfunP mu'zeta|] := boolP [forall j, '['Ind 'chi_t, chi_ j] == 0].
  right; rewrite Dzeta -(cfIndInd _ _ sHPU) ?gFsub //.
  rewrite ['Ind 'chi_t]cfun_sum_constt linear_sum /= rpred_sum // => s tPUs.
  rewrite linearZ rpredZ_Cnat ?Cnat_cfdot_char ?cfInd_char ?irr_char //=.
  have [[j Ds] | [irr_zeta _]] := prTIres_irr_cases ptiWS s.
    by case/eqP: tPUs; rewrite Ds mu'zeta.
  rewrite mem_zchar // mem_filter irr_zeta mem_seqInd ?gFnormal ?normal1 //=.
  by rewrite !inE sub1G andbT -(sub_cfker_constt_Ind_irr tPUs).
rewrite negb_forall => /existsP/sigW[j].
rewrite -irr_consttE constt_Ind_Res => jHt.
have nz_j: j != 0; last do [left; exists j => //].
  apply: contraTneq jHt => ->; rewrite prTIres0 rmorph1 -irr0 constt_irr.
  by apply: contraNneq kerP't => ->; rewrite irr0 cfker_cfun1.
have /pairwise_orthogonalP[_ ooS1]: pairwise_orthogonal calS1.
  by rewrite seqInd_orthogonal ?gFnormal.
rewrite -(cfRes_prTIirr _ 0) cfResRes ?gFsub //= in jHt.
have muj_mu0j: Imu2 (0, j) \in irr_constt (mu_ j).
  by rewrite irr_consttE cfdotC cfdot_prTIirr_red eqxx conjC1 oner_eq0.
apply: contraNeq (constt_Res_trans (prTIred_char _ _) muj_mu0j jHt).
by rewrite cfdot_Res_l /= -Dzeta eq_sym => /ooS1-> //; rewrite S1mu.
Qed.

Let sS1S : {subset calS1 <= 'Z[calS]}.
Proof.
move=> zeta /S1cases[[j nz_j ->]|]; first by rewrite mem_zchar ?FTseqInd_TIred.
by apply: zchar_subset; apply: mem_subseq (filter_subseq _ _).
Qed.

(* This is Peterfalvi (13.5). *)
(* We have adapted the statement to its actual use by replacing the Dade      *)
(* (partial) isometry by a (total) coherent isometry, and strengthening the   *)
(* orthogonality condition. This simplifies the assumptions as zeta0 is no    *)
(* longer needed. Note that this lemma is only used to establish various      *)
(* inequalities (13.6-8) that contribute to (13.10), so it does not need to   *)
(* be exported from this section.                                             *)
Let calS1_split1 (tau1 : {additive _}) zeta1 chi :
   coherent_with calS S^# tau tau1 -> zeta1 \in calS1 -> chi \in 'Z[irr G] ->
   {in calS1, forall zeta, zeta != zeta1 -> '[tau1 zeta, chi] = 0} -> 
  let a := '[tau1 zeta1, chi] in
  exists2 alpha,
     alpha \in 'Z[irr H] /\ {subset irr_constt alpha <= Iirr_ker H P} &
  [/\ (*a*) {in H^#, forall x, chi x = a / '[zeta1] * zeta1 x + alpha x}, 
      (*b*)
         \sum_(x in H^#) `|chi x| ^+ 2 =
             a ^+ 2 / '[zeta1] * (#|S|%:R - zeta1 1%g ^+ 2 / '[zeta1])
             - 2%:R * a * (zeta1 1%g * alpha 1%g / '[zeta1])
             + (\sum_(x in H^#) `|alpha x| ^+ 2)              
    & (*c*)
         \sum_(x in H^#) `|alpha x| ^+ 2 >= #|P|.-1%:R * alpha 1%g ^+ 2].
Proof.
case=> _ Dtau1 S1zeta1 Zchi o_tau1S_chi a.
have sW2P: W2 \subset P by have [_ _ _ []] := StypeP.
have /mulG_sub[sPH _] := dprodW defH.
have ntH: H :!=: 1%g by apply: subG1_contra ntW2; apply: subset_trans sPH.
have sH1S: H^# \subset G^# by rewrite setSD ?subsetT.
have[nsHS nsPS ns1S]: [/\ H <| S, P <| S & 1 <| S] by rewrite !gFnormal normal1.
have [[sHS nHS] [sPS nPS]] := (andP nsHS, andP nsPS).
have tiH: normedTI H^# G S by have [] := compl_of_typeII_IV maxS StypeP.
have ddH := normedTI_Dade tiH sH1S; have [_ ddH_1] := Dade_normedTI_P ddH tiH.
pose tauH := Dade ddH.
have DtauH: {in 'CF(S, H^#), tauH =1 'Ind} := Dade_Ind ddH tiH.
have sS1H: {subset calS1 <= calH} by apply: seqInd_subT.
pose zeta0 := zeta1^*%CF.
have S1zeta0: zeta0 \in calS1 by rewrite cfAut_seqInd.
have zeta1'0: zeta0 != zeta1.
  by rewrite (hasPn (seqInd_notReal _ _ _ _) _ S1zeta1) ?gFnormal ?mFT_odd.
have Hzeta0 := sS1H _ S1zeta0.
have dH_1 zeta: zeta \in calH -> (zeta - zeta0) 1%g == 0.
  by move=> Tzeta; rewrite 2!cfunE !calHuq // subrr eqxx.
have H1dzeta zeta: zeta \in calH -> zeta - zeta0 \in 'CF(S, H^#).
  have HonH: {subset calH <= 'CF(S, H)} by exact: seqInd_on.
  by move=> Hzeta; rewrite cfun_onD1 rpredB ?HonH ?dH_1.
pose calH1 := rem zeta1 (rem zeta0 (filter [mem calS1] calH)).
pose calH2 := filter [predC calS1] calH.
have DcalH: perm_eq calH (zeta0 :: zeta1 :: calH1 ++ calH2).
  rewrite -(perm_filterC [mem calS1]) -!cat_cons perm_cat2r.
  rewrite (perm_eqlP (@perm_to_rem _ zeta0 _ _)) ?mem_filter /= ?S1zeta0 //.
  rewrite perm_cons perm_to_rem // mem_rem_uniq ?filter_uniq ?seqInd_uniq //.
  by rewrite !inE mem_filter /= eq_sym zeta1'0 S1zeta1 sS1H.
have{DcalH} [a_ _ Dchi _] := invDade_seqInd_sum ddH chi DcalH.
have Da_ zeta: zeta \in calH -> a_ zeta = '['Ind (zeta - zeta0), chi].
  move=> Tzeta; rewrite /a_ !calHuq // divff ?scale1r; last first.
    by rewrite pnatr_eq0 -lt0n muln_gt0 indexg_gt0 cardG_gt0.
  by rewrite [Dade _ _]DtauH ?H1dzeta.
have Za_ zeta: zeta \in calH -> a_ zeta \in Cint.
  move=> Hzeta; rewrite Da_ // Cint_cfdot_vchar ?cfInd_vchar //.
  by rewrite rpredB ?char_vchar ?(seqInd_char Hzeta) ?(seqInd_char Hzeta0).
have{Da_} Da_ zeta: zeta \in calS1 -> a_ zeta = '[tau1 zeta, chi].
  move=> S1zeta; have Hzeta := sS1H _ S1zeta.
  rewrite Da_ //; have [_ _ _ _ [_ <-]] := FTtypeP_facts.
    rewrite -Dtau1; last by rewrite zcharD1E rpredB ?sS1S ?dH_1.
    by rewrite raddfB cfdotBl (o_tau1S_chi zeta0) ?subr0.
  by rewrite (cfun_onS (Fitting_sub_FTsupp0 maxS)) ?H1dzeta.
pose alpha := 'Res[H] (\sum_(zeta <- calH2) (a_ zeta)^* / '[zeta] *: zeta).
have{Dchi} Dchi: {in H^#, forall x, chi x = a / '[zeta1] * zeta1 x + alpha x}.
  move=> x H1x; have [_ Hx] := setD1P H1x.
  transitivity (invDade ddH chi x).
    by rewrite cfunElock ddH_1 // big_set1 H1x mul1g cards1 invr1 mul1r.
  rewrite cfResE ?gFsub ?Dchi // big_cons conj_Cint ?Za_ ?Da_ ?sS1H //= -/a.
  congr (_ + _); rewrite big_cat /= sum_cfunE big1_seq ?add0r //= => [|zeta].
    by apply: eq_bigr => zeta; rewrite cfunE.
  rewrite ?(mem_rem_uniq, inE) ?rem_uniq ?filter_uniq ?seqInd_uniq //=.
  rewrite mem_filter => /and4P[/= zeta1'z _ S1zeta _].
  by rewrite Da_ ?o_tau1S_chi // conjC0 !mul0r.
have kerHalpha: {subset irr_constt alpha <= Iirr_ker H P}.
  move=> s; apply: contraR => kerP's; rewrite [alpha]rmorph_sum cfdot_suml.
  rewrite big1_seq // => psi; rewrite mem_filter /= andbC => /andP[].
  case/seqIndP=> r _ ->; rewrite mem_seqInd // !inE sub1G andbT negbK => kerPr.
  rewrite cfdot_Res_l cfdotZl mulrC cfdot_sum_irr big1 ?mul0r // => t _.
  apply: contraNeq kerP's; rewrite mulf_eq0 fmorph_eq0 inE => /norP[rSt sSt].
  by rewrite (sub_cfker_constt_Ind_irr sSt) -?(sub_cfker_constt_Ind_irr rSt).
have Zalpha: alpha \in 'Z[irr H].
  rewrite [alpha]rmorph_sum big_seq rpred_sum // => zeta; rewrite mem_filter /=.
  case/andP=> S1'zeta Tzeta; rewrite linearZ /= -scalerA.
  rewrite rpredZ_Cint ?conj_Cint ?Za_ //; have [s _ ->] := seqIndP Tzeta.
  rewrite cfResInd_sum_cfclass ?reindex_cfclass -?cfnorm_Ind_irr //=.
  rewrite scalerK ?cfnorm_eq0 ?cfInd_eq0 ?irr_neq0 ?irr_char ?gFsub //.
  by apply: rpred_sum => i _; apply: irr_vchar.
have{Da_ Za_} Za: a \in Cint by rewrite -[a]Da_ ?Za_ ?sS1H. 
exists alpha => //; split=> //.
  set a1 := a / _ in Dchi; pose phi := a1 *: 'Res zeta1 + alpha.
  transitivity (#|H|%:R * '[phi] - `|phi 1%g| ^+ 2).
    rewrite (cfnormE (cfun_onG phi)) mulVKf ?neq0CG // addrC.
    rewrite (big_setD1 _ (group1 H)) addKr; apply: eq_bigr => x H1x.
    by have [_ Hx] := setD1P H1x; rewrite !cfunE cfResE // Dchi.
  have Qa1: a1 \in Creal.
    apply: rpred_div; first by rewrite rpred_Cint.
    by rewrite rpred_Cnat // Cnat_cfdot_char ?(seqInd_char S1zeta1).
  rewrite cfnormDd; last first.
    rewrite [alpha]cfun_sum_constt cfdotZl cfdot_sumr big1 ?mulr0 // => s.
    move/kerHalpha; rewrite inE cfdotZr mulrC cfdot_Res_l => kerPs.
    have [r kerP'r ->] := seqIndP S1zeta1; rewrite cfdot_sum_irr big1 ?mul0r //.
    move=> t _; apply: contraTeq kerP'r; rewrite !inE sub1G andbT negbK.
    rewrite mulf_eq0 fmorph_eq0 => /norP[]; rewrite -!irr_consttE.
    by move=> /sub_cfker_constt_Ind_irr-> // /sub_cfker_constt_Ind_irr <-.
  rewrite cfnormZ 2!cfunE cfRes1 2?real_normK //; last first.
    rewrite rpredD 1?rpredM // Creal_Cint ?Cint_vchar1 // ?char_vchar //.
    by rewrite (seqInd_char S1zeta1).
  rewrite mulrDr mulrCA sqrrD opprD addrACA; congr (_ + _); last first.
    rewrite (cfnormE (cfun_onG _)) mulVKf ?neq0CG //.
    by rewrite (big_setD1 1%g) // Cint_normK ?Cint_vchar1 // addrC addKr.
  rewrite opprD addrA; congr (_ - _); last first.
    rewrite -[_ * a * _]mulrA -mulr_natl; congr (_ * _).
    by rewrite -[a1 * _]mulrA -(mulrA a); congr (_ * _); rewrite -mulrA mulrC.
  rewrite mulrBr; congr (_ - _); last first.
    by rewrite mulrACA -expr2 -!exprMn mulrAC.
  rewrite -mulrA exprMn -mulrA; congr (_ * _); rewrite expr2 -mulrA.
  congr (_ * _); apply: canLR (mulKf (cfnorm_seqInd_neq0 nsHS S1zeta1)) _.
  rewrite (cfnormE (cfun_onG _)) mulVKf ?neq0CG // mulrC.
  rewrite (cfnormE (seqInd_on nsHS S1zeta1)) mulVKf ?neq0CG //.
  by apply: eq_bigr => x Hx; rewrite cfResE.
rewrite -subn1 natrB // -Cint_normK ?Cint_vchar1 // mulrBl mul1r ler_subl_addl.
apply: ler_trans (_ : \sum_(x in H) `|alpha x| ^+ 2 <= _); last first.
  by rewrite (big_setD1 1%g).
rewrite (big_setID P) /= (setIidPr sPH) ler_paddr ?sumr_ge0 // => [x _|].
  by rewrite mulr_ge0 ?normr_ge0.
rewrite mulr_natl -sumr_const ler_sum // => y Py.
suffices ->: alpha y = alpha 1%g by apply: lerr.
rewrite [alpha]cfun_sum_constt !sum_cfunE; apply: eq_bigr => i.
by rewrite !cfunE => /kerHalpha; rewrite inE => /subsetP/(_ y Py)/cfker1->.
Qed.

Local Notation eta10 := (eta_ #1 0).
Local Notation eta01 := (eta_ 0 #1).

Let o_tau1_eta (tau1 : {additive _}) i j:
    coherent_with calS S^# tau tau1 -> 
  {in 'Z[calSirr], forall zeta, '[tau1 zeta, eta_ i j] = 0}.
Proof.
move=> cohS _ /zchar_expansion[|z Zz ->].
  by rewrite filter_uniq ?seqInd_uniq.
rewrite raddf_sum cfdot_suml big1_seq //= => phi; rewrite mem_filter.
case/andP=> irr_phi /(coherent_ortho_cycTIiso StypeP sSS0 cohS) o_phi_eta.
by rewrite raddfZ_Cint {Zz}//= cfdotZl o_phi_eta ?mulr0.
Qed.

Let P1_int2_lb b : b \in Cint -> 2%:R * u%:R * b <= #|P|.-1%:R * b ^+ 2.
Proof.
move=> Zb; rewrite -natrM; apply: ler_trans (_ : (2 * u)%:R * b ^+ 2 <= _).
  by rewrite ler_wpmul2l ?ler0n ?Cint_ler_sqr.
rewrite ler_wpmul2r -?realEsqr ?Creal_Cint // leC_nat mulnC -leq_divRL //.
have [_ [_ ->] /leq_trans-> //] := FTtypeP_facts.
by rewrite leq_div2l // -subn1 ltn_subRL.
Qed.

(* This is Peterfalvi (13.6). *)
Lemma FTtypeP_sum_Ind_Fitting_lb (tau1 : {additive _}) lambda :
    coherent_with calS S^# tau tau1 -> lambda \in irrIndH -> lambda \in calS ->
  \sum_(x in H^#) `|tau1 lambda x| ^+ 2 >= #|S|%:R - lambda 1%g ^+ 2.
Proof.
move=> cohS /andP[Ilam Hlam] Slam; have [[Itau1 Ztau1] _] := cohS.
have Zlam1: tau1 lambda \in 'Z[irr G] by rewrite Ztau1 ?mem_zchar.
have S1lam: lambda \in calS1.
  have [[s kerP's Ds] [r _ Dr]] := (seqIndP Slam, seqIndP Hlam).
  rewrite Dr mem_seqInd ?gFnormal ?normal1 // !inE !sub1G !andbT in kerP's *.
  rewrite -(sub_cfker_Ind_irr r (gFsub _ _) (gFnorm _ _)) /= -Dr.
  by rewrite Ds sub_cfker_Ind_irr ?gFsub ?gFnorm.
have [|alpha [Zalpha kerPalpha]] := calS1_split1 cohS S1lam Zlam1.
  move=> zeta S1zeta lam'zeta; rewrite Itau1 ?sS1S //.
  suffices: pairwise_orthogonal calS1 by case/pairwise_orthogonalP=> _ ->.
  by rewrite seqInd_orthogonal ?gFnormal.
rewrite Itau1 ?mem_zchar // irrWnorm // expr1n !divr1 mul1r => [[Dlam ->]].
rewrite mulr1 -ler_subl_addl addrC opprB subrK calHuq //; apply: ler_trans.
have [[x W2x ntx] [y W1y nty]] := (trivgPn _ ntW2, trivgPn _ ntW1).
have [_ _ _ [_ _ sW2P _ _] _] := StypeP; have Px := subsetP sW2P x W2x.
have [eps pr_eps] := C_prim_root_exists (prime_gt0 pr_q).
have{y W1y W2x nty} lamAmod: (tau1 lambda x == lambda x %[mod 1 - eps])%A.
  have [_ /mulG_sub[_ sW1S] _ tiPUW1] := sdprodP defS.
  have [_ /mulG_sub[sW1W sW2W] cW12 _] := dprodP defW.
  have /mulG_sub[sPPU _] := sdprodW defPU.
  have [o_y cxy]: #[y] = q /\ x \in 'C[y].
    split; last by apply/cent1P; red; rewrite (centsP cW12).
    by apply: nt_prime_order => //; apply/eqP; rewrite -order_dvdn order_dvdG.
  have lam1yx: (tau1 lambda (y * x)%g == tau1 lambda x %[mod 1 - eps])%A.
    by rewrite (vchar_ker_mod_prim pr_eps) ?in_setT.
  have [Sx Sy] := (subsetP (gFsub _ _) x Px, subsetP sW1S y W1y).
  have PUx := subsetP sPPU x Px.
  have lam_yx: (lambda (y * x)%g == lambda x %[mod 1 - eps])%A.
    by rewrite (vchar_ker_mod_prim pr_eps) ?char_vchar ?(seqInd_char Slam).
  apply: eqAmod_trans lam_yx; rewrite eqAmod_sym; apply: eqAmod_trans lam1yx.
  have PUlam: lambda \in 'CF(S, PU) by rewrite (seqInd_on _ Slam) ?gFnormal.
  have PU'yx: (y * x)%g \notin PU.
    by rewrite groupMr //= -[y \in PU]andbT -W1y -in_setI tiPUW1 !inE.
  rewrite (cfun_on0 PUlam PU'yx) (ortho_cycTIiso_vanish pddS) //.
    apply/orthoPl=> _ /mapP[_ /(cycTIirrP defW)[i [j ->]] ->].
    by rewrite (coherent_ortho_cycTIiso StypeP sSS0).
  rewrite !inE (groupMl x (subsetP sW1W y _)) // (subsetP sW2W) // andbT.
  rewrite groupMl // -[x \in _]andTb -PUx -in_setI tiPUW1 !inE negb_or ntx /=.
  by rewrite (contra _ PU'yx) // => /(subsetP sW2P)/(subsetP sPPU).
have{x ntx Px lamAmod} alphaAmod: (alpha 1%g == 0 %[mod 1 - eps])%A.
  have Hx: x \in H by have/mulG_sub[/subsetP->] := dprodW defH.
  have:= lamAmod; rewrite -[lambda x]addr0 Dlam ?inE ?ntx // mul1r eqAmodDl.
  rewrite cfker1 // [alpha]cfun_sum_constt (subsetP (cfker_sum _ _ _)) //.
  rewrite !inE Hx (subsetP _ x Px) //; apply/bigcapsP=> i /kerPalpha.
  by rewrite !inE => /subset_trans-> //; apply: cfker_scale.
have /dvdCP[b Zb ->]: (q %| alpha 1%g)%C.
  by rewrite (int_eqAmod_prime_prim pr_eps) // Cint_vchar1.
rewrite natrM mulrACA exprMn !mulrA 2?ler_pmul2r ?gt0CG //.
by rewrite -[_ * b * b]mulrA P1_int2_lb.
Qed.

(* This is Peterfalvi (13.7). *)
Lemma FTtypeP_sum_cycTIiso10_lb : \sum_(x in H^#) `|eta10 x| ^+ 2 >= #|H^#|%:R.
Proof.
pose mu1 := mu_ #1; have S1mu1: mu1 \in calS1 by rewrite S1mu ?Iirr1_neq0.
have Zeta10: eta10 \in 'Z[irr G] by rewrite cycTIiso_vchar.
have [tau1 cohS [b _ Dtau1]] := FTtypeP_coherence.
have{b Dtau1} oS1eta10: {in calS1, forall zeta, '[tau1 zeta, eta10] = 0}.
  move=> zeta /S1cases[[j nz_j ->] | /o_tau1_eta-> //].
  rewrite Dtau1 // cfdotZl cfdot_suml big1 ?mulr0 // => i _.
  by rewrite cfdot_cycTIiso signW2_eq0 (negPf nz_j) andbF.
have [_ /oS1eta10//|alpha [Zalpha kerPalpha]] := calS1_split1 cohS S1mu1 Zeta10.
rewrite {}oS1eta10 // expr0n mulr0 !mul0r subrr add0r => [[Deta10 -> ub_alpha]].
have{Deta10} Deta10: {in H^#, eta10 =1 alpha}.
  by move=> x /Deta10; rewrite !mul0r add0r.
set a1_2 := alpha 1%g ^+ 2 in ub_alpha.
have Dsum_alpha: \sum_(x in H^#) `|alpha x| ^+ 2 = #|H|%:R * '[alpha] - a1_2.
  rewrite (cfnormE (cfun_onG _)) mulVKf ?neq0CG // (big_setD1 _ (group1 H)) /=.
  by rewrite addrC Cint_normK ?addKr ?Cint_vchar1.
have [/mulG_sub[sPH _] [_ _ _ [_ _ sW2P _ _] _]] := (dprodW defH, StypeP).
have nz_alpha: alpha != 0.
  have [[x W2x ntx] [y W1y nty]] := (trivgPn _ ntW2, trivgPn _ ntW1).
  have [eps pr_eps] := C_prim_root_exists (prime_gt0 pr_q).
  have [_ mulW12 cW12 tiW12] := dprodP defW.
  have [sW1W sW2W] := mulG_sub mulW12.
  have [o_y cxy]: #[y] = q /\ x \in 'C[y].
    split; last by apply/cent1P; red; rewrite (centsP cW12).
    by apply: nt_prime_order => //; apply/eqP; rewrite -order_dvdn order_dvdG.
  have eta10x: (eta10 x == eta10 (y * x)%g %[mod 1 - eps])%A.
    by rewrite eqAmod_sym (vchar_ker_mod_prim pr_eps) ?in_setT.
  have eta10xy: (eta10 (y * x)%g == 1 %[mod 1 - eps])%A.
    rewrite cycTIiso_restrict; last first.
      rewrite !inE -mulW12 mem_mulg // andbT groupMl ?groupMr // -[_ || _]andTb.
      by rewrite andb_orr -{1}W2x -W1y andbC -!in_setI tiW12 !inE (negPf ntx).
    have {2}<-: w_ #1 0 x = 1.
      rewrite -[x]mul1g /w_ dprod_IirrE cfDprodE // irr0 cfun1E W2x mulr1.
      by rewrite lin_char1 ?irr_cyclic_lin.
    rewrite (vchar_ker_mod_prim pr_eps) ?(subsetP sW1W y) ?(subsetP sW2W) //.
    by rewrite irr_vchar.
  have: (alpha x == 1 %[mod 1 - eps])%A.
    rewrite -Deta10; last by rewrite !inE ntx (subsetP sPH) ?(subsetP sW2P).
    exact: eqAmod_trans eta10x eta10xy.
  apply: contraTneq => ->; rewrite cfunE eqAmod_sym.
  apply/negP=> /(int_eqAmod_prime_prim pr_eps pr_q (rpred1 _))/idPn[].
  by rewrite (dvdC_nat q 1) -(subnKC qgt2).
apply: wlog_neg => suma_lt_H.
suffices{ub_alpha} lb_a1_2: a1_2 >= #|H^#|%:R.
  have Pgt2: (2 < #|P|)%N by apply: leq_trans (subset_leq_card sW2P).
  apply: ler_trans (ler_trans lb_a1_2 _) ub_alpha.
  rewrite ler_pmull ?(ltr_le_trans _ lb_a1_2) ?ler1n ?ltr0n //.
    by rewrite -(subnKC Pgt2).
  have:= leq_trans (ltnW Pgt2) (subset_leq_card sPH).
  by rewrite (cardsD1 1%g) group1.
have /CnatP[n Dn]: '[alpha] \in Cnat by rewrite Cnat_cfnorm_vchar.
have /CnatP[m Dm]: a1_2 \in Cnat by rewrite Cnat_exp_even ?Cint_vchar1.
rewrite Dm leC_nat leqNgt; apply: contra suma_lt_H => a1_2_lt_H.
rewrite {1}Dsum_alpha Dn Dm -natrM ler_subr_addl (cardsD1 1%g H) group1 /=.
case Dn1: n => [|[|n1]]; first by rewrite -cfnorm_eq0 Dn Dn1 eqxx in nz_alpha.
  have /dirrP[b [i Dalpha]]: alpha \in dirr H by rewrite dirrE Zalpha Dn Dn1 /=.
  rewrite -Dm /a1_2 Dalpha cfunE exprMn sqrr_sign mul1r muln1 mulrS ler_add2r.
  by rewrite lin_char1 ?expr1n //; apply/char_abelianP.
rewrite -natrD leC_nat -add2n mulnDr (addnC 1%N) mulnDl -addnA.
by apply: leq_trans (leq_addr _ _); rewrite muln2 -addnn leq_add2r ltnW.
Qed.

(* This is Peterfalvi (13.8). *)
(* We have filled a logical gap in the textbook, which quotes (13.3.c) to get *)
(* a j such that eta_01 is a component of mu_j^tau1, then asserts that the    *)
(* (orthogonality) assumptions of (13.5) have been checked, apparently        *)
(* implying that because for zeta in calS1 \ mu_j, zeta^tau1 is orthogonal to *)
(* mu_j^tau1, as per the proof of (13.6), zeta^tau1 must be orthogonal to     *)
(* eta_01. This is wrong, because zeta^tau1, mu_j^tau1 and eta_01 are not     *)
(* characters, but virtual characters. We need to use a more careful line of  *)
(* reasoning, using the more precise characterization of calS1 in the lemma   *)
(* S1cases above (which does use the orthogonal-constituent argument, but     *)
(* for chi_j and Res_H zeta), and the decomposition given in (13.3.c) for all *)
(* the mu_k.                                                                  *)
Lemma FTtypeP_sum_cycTIiso01_lb :
  \sum_(x in H^#) `|eta01 x| ^+ 2 >= #|PU|%:R - (u ^ 2)%:R.
Proof.
have [tau1 cohS [b _ Dtau1]] := FTtypeP_coherence.
have Zeta01: eta01 \in 'Z[irr G] by rewrite cycTIiso_vchar.
pose j1 := signW2 b #1; pose d : algC := (-1) ^+ b; pose mu1 := mu_ j1.
have nzj1: j1 != 0 by [rewrite signW2_eq0 ?Iirr1_neq0]; have S1mu1 := S1mu nzj1.
have o_mu_eta01 j: j != 0 -> '[tau1 (mu_ j), eta01] = d *+ (j == j1). 
  move/Dtau1->; rewrite -/d cfdotZl cfdot_suml big_ord_recl /=.
  rewrite cfdot_cycTIiso andTb (inv_eq (signW2K b)).
  by rewrite big1 ?addr0 ?mulr_natr // => i _; rewrite cfdot_cycTIiso.
have [zeta | alpha [Zalpha kerPalpha [_]]] := calS1_split1 cohS S1mu1 Zeta01.
  case/S1cases=> [[j nz_j ->] | /o_tau1_eta-> //].
  by rewrite o_mu_eta01 // (inj_eq (prTIred_inj _)) => /negPf->.
rewrite o_mu_eta01 // eqxx mulrb => -> lb_alpha.
rewrite -ler_subl_addl cfnorm_prTIred -/q mulrAC sqrr_sign mul1r.
rewrite mu1uq // natrM exprMn (mulrAC _ q%:R) (mulrA _ q%:R) !mulfK ?neq0CG //.
rewrite natrX -(sdprod_card defS) natrM -mulrBl mulfK ?neq0CG //.
rewrite addrC opprB subrK mulrACA; apply: ler_trans lb_alpha.
apply: ler_trans (P1_int2_lb _) _; first by rewrite rpredMsign Cint_vchar1.
by rewrite exprMn sqrr_sign mul1r lerr.
Qed.

(* These are the assumptions for (13.9); K will be set to 'F(T) in the only   *)
(* application of this lemma, in the proof of (13.10).                        *)

Variable K : {group gT}.
Let G0 := ~: (class_support H G :|: class_support K G).

Variables (tau1 : {additive 'CF(S) -> 'CF(G)}) (lambda : 'CF(S)).

Hypothesis cohS : coherent_with calS S^# tau tau1.
Hypothesis cohSmu : typeP_TIred_coherent tau1.

Hypotheses (Slam : lambda \in calS) (irrHlam : irrIndH lambda).

(* This is Peterfalvi (13.9)(a). *)
(* As this part is only used to establish (13.9.b) it can be Section-local.  *)
Let cover_G0 : {in G0, forall x, tau1 lambda x != 0 \/ eta_ #1 0 x != 0}.
Proof.
have [[b _ Dtau1_mu] [/= Ilam Hlam]] := (cohSmu, andP irrHlam).
pose sum_eta1 := (-1) ^+ b *: \sum_i eta_ i #1.
have{Dtau1_mu} [j nz_j tau1muj]: exists2 j, j != 0 & tau1 (mu_ j) = sum_eta1.
  pose j := signW2 b #1; have nz: j != 0 by rewrite signW2_eq0 Iirr1_neq0.
  by exists j; rewrite // Dtau1_mu // signW2K.
move=> x; rewrite !inE => /norP[H'x _].
have{tau1muj} ->: tau1 lambda x = sum_eta1 x.
  rewrite -[lambda](subrK (mu_ j)) raddfD cfunE tau1muj.
  rewrite [tau1 _ x](cfun_on0 _ H'x) ?add0r {x H'x}//=.
  have Hmuj: mu_ j \in calH := Hmu nz_j.
  have dmu1: (lambda - mu_ j) 1%g == 0 by rewrite !cfunE !calHuq ?subrr.
  have H1dmu: lambda - mu_ j \in 'CF(S, H^#).
    by rewrite cfun_onD1 rpredB ?((seqInd_on (gFnormal _ _)) setT). 
  have [_ ->] := cohS; last first.
    by rewrite zcharD1E ?rpredB ?mem_zchar ?FTseqInd_TIred /=.
  have A0dmu := cfun_onS (Fitting_sub_FTsupp0 maxS) H1dmu.
  have [_ _ _ _ [_ -> //]] := FTtypeP_facts.
  by rewrite cfInd_on ?subsetT // (cfun_onS _ H1dmu) ?imset2Sl ?subsetDl.
apply/nandP/andP=> [[/eqP sum_eta1x_0 /eqP eta1x_0]].
have cycW: cyclic W by have [] := ctiWG.
have W'x: x \notin class_support (cyclicTIset defW) G.
  apply: contra_eqN eta1x_0 => /imset2P[{x H'x sum_eta1x_0}x g Wx Gg ->].
  rewrite cfunJ {g Gg}// cycTIiso_restrict //.
  by rewrite lin_char_neq0 ?irr_cyclic_lin //; case/setDP: Wx.
have nz_i1 : #1 != 0 :> Iirr W1 by rewrite Iirr1_neq0.
have eta_x_0 i: i != 0 -> eta_ i 0 x = 0.
  rewrite /w_ dprod_IirrEl => /(cfExp_prime_transitive pr_q nz_i1)[k co_k_p ->].
  have: coprime k #[w_ #1 0]%CF by rewrite /w_ dprod_IirrEl cforder_sdprod.
  rewrite rmorphX /= -dprod_IirrEl => /(cycTIiso_aut_exists ctiWG)[[uu ->] _].
  by rewrite cfunE /= -/sigma eta1x_0 rmorph0.
have eta_i1 i: i != 0 -> eta_ i #1 x = eta_ 0 #1 x - 1.
  move=> nz_i; apply/eqP; pose alpha := cfCyclicTIset defW i #1.
  have Walpha: alpha \in 'CF(W, cyclicTIset defW).
    by rewrite (cfCycTI_on ctiWG) ?Iirr1_neq0.
  have: sigma alpha x == 0.
    by rewrite cycTIiso_Ind // (cfun_on0 _ W'x) ?cfInd_on ?subsetT.
  rewrite [alpha]cfCycTI_E linearD !linearB /= !cfunE cycTIiso1 cfun1E inE.
  by rewrite {1}eta_x_0 //= subr0 addrC addr_eq0 opprB.
have eta11x: eta_ #1 #1 x = - (q%:R)^-1.
  rewrite -mulN1r; apply: canRL (mulfK (neq0CG W1)) _.
  transitivity ((-1) ^+ b * sum_eta1 x - 1); last first.
    by rewrite sum_eta1x_0 mulr0 add0r.
  rewrite cfunE signrMK mulr_natr -/q -nirrW1 -sumr_const sum_cfunE.
  by rewrite !(bigD1 0 isT) /= addrAC eta_i1 // (eq_bigr _ eta_i1).
have: - eta_ #1 #1 x \in Cint.
  rewrite rpredN Cint_rat_Aint ?Aint_vchar ?cycTIiso_vchar //.
  by rewrite eta11x rpredN rpredV rpred_nat.
case/norm_Cint_ge1/implyP/idPn; rewrite eta11x opprK invr_eq0 neq0CG /=.
by rewrite normfV normr_nat invf_ge1 ?gt0CG // lern1 -ltnNge ltnW.
Qed.

(* This is Peterfalvi (13.9)(b). *)
Lemma FTtypeP_sum_nonFitting_lb :
  \sum_(x in G0) (`|tau1 lambda x| ^+ 2 + `|eta_ #1 0 x| ^+ 2) >= #|G0|%:R.
Proof.
pose A (xi : 'CF(G)) := [set x in G0 | xi x != 0].
suffices A_ub xi: xi \in dirr G -> #|A xi|%:R <= \sum_(x in G0) `|xi x| ^+ 2.
  apply: ler_trans (_ : (#|A (tau1 lambda)| + #|A (eta_ #1 0)|)%:R <= _).
    rewrite leC_nat -cardsUI /A !setIdE -setIUr (leq_trans _ (leq_addr _ _)) //.
    rewrite subset_leq_card // subsetIidl.
    by apply/subsetP=> x /cover_G0/orP; rewrite !inE.
  rewrite natrD big_split ler_add ?A_ub ?cycTIiso_dirr //.
  have [[[Itau1 Ztau1] _] [Ilam _]] := (cohS, andP irrHlam).
  by rewrite dirrE Ztau1 ?Itau1 ?mem_zchar //= irrWnorm.
case/dirrP=> d [t Dxi]; rewrite (big_setID [set x | xi x != 0]) /= addrC.
rewrite -setIdE -/(A _) big1 ?add0r => [|x]; last first.
  by rewrite !inE negbK => /andP[/eqP-> _]; rewrite normr0 expr0n.
rewrite -sum1_card !(partition_big_imset (@cycle _)) /= natr_sum.
apply: ler_sum => _ /imsetP[x Ax ->].
pose B := [pred y | generator <[x]> y]; pose phi := 'Res[<[x]>] 'chi_t.
have defA: [pred y in A xi | <[y]> == <[x]>] =i B.
  move=> y; rewrite inE /= eq_sym andb_idl // !inE => eq_xy.
  have LGxy L (LG := class_support L G): x \notin LG -> y \notin LG.
    rewrite /LG class_supportEr; apply: contra => /bigcupP[g Gg Lg_y].
    apply/bigcupP; exists g => //; move: Lg_y.
    by rewrite -!cycle_subG (eqP eq_xy).
  move: Ax; rewrite !inE !negb_or -andbA => /and3P[/LGxy-> /LGxy->].
  apply: contraNneq => chi_y_0.
  have [k co_k_y ->]: exists2 k, coprime k #[y] & x = (y ^+ k)%g.
    have Yx: generator <[y]> x by rewrite [generator _ _]eq_sym.
    have /cycleP[k Dx] := cycle_generator Yx; exists k => //.
    by rewrite coprime_sym -generator_coprime -Dx.
  have Zxi: xi \in 'Z[irr G] by rewrite Dxi rpredZsign irr_vchar.
  have [uu <- // _] := make_pi_cfAut [group of G] co_k_y.
  by rewrite cfunE chi_y_0 rmorph0.
have resB: {in B, forall y, `|xi y| ^+ 2 = `|phi y| ^+ 2}.
  move=> y /cycle_generator Xy.
  by rewrite Dxi cfunE normrMsign cfResE ?subsetT.
rewrite !(eq_bigl _ _ defA) sum1_card (eq_bigr _ resB).
apply: sum_norm2_char_generators => [|y By].
  by rewrite cfRes_char ?irr_char.
rewrite -normr_eq0 -sqrf_eq0 -resB // sqrf_eq0 normr_eq0.
by move: By; rewrite -defA !inE -andbA => /and3P[].
Qed.

End Thirteen_2_3_5_to_9.

Section Thirteen_4_10_to_16.

(* These assumptions correspond to Peterfalvi, Hypothesis (13.1), most of     *)
(* which gets used to prove (13.4) and (13.9-13).                             *)

Variables S U W W1 W2 : {group gT}.
Hypotheses (maxS : S \in 'M) (defW : W1 \x W2 = W).
Hypotheses (StypeP : of_typeP S U defW).

Local Notation "` 'W1'" := (gval W1) (at level 0, only parsing) : group_scope.
Local Notation "` 'W2'" := (gval W2) (at level 0, only parsing) : group_scope.
Local Notation "` 'W'" := (gval W) (at level 0, only parsing) : group_scope.
Local Notation V := (cyclicTIset defW).

Local Notation "` 'S'" := (gval S) (at level 0, only parsing) : group_scope.
Local Notation P := `S`_\F%G.
Local Notation "` 'P'" := `S`_\F (at level 0) : group_scope.
Local Notation PU := S^`(1)%G.
Local Notation "` 'PU'" := `S^`(1) (at level 0) : group_scope.
Local Notation "` 'U'" := (gval U) (at level 0, only parsing) : group_scope.
Local Notation C := 'C_U(`P)%G.
Local Notation "` 'C'" := 'C_`U(`P) (at level 0) : group_scope.
Local Notation H := 'F(S)%G.
Local Notation "` 'H'" := 'F(`S) (at level 0) : group_scope.

Let defS : PU ><| W1 = S. Proof. by have [[]] := StypeP. Qed.
Let defPU : P ><| U = PU. Proof. by have [_ []] := StypeP. Qed.
Let defH : P \x C = H. Proof. by have [] := typeP_context StypeP. Qed.

Let notStype1 : FTtype S != 1%N. Proof. exact: FTtypeP_neq1 StypeP. Qed.
Let notStype5 : FTtype S != 5%N. Proof. exact: FTtype5_exclusion maxS. Qed.

Let pddS := FT_prDade_hypF maxS StypeP.
Let ptiWS : primeTI_hypothesis S PU defW := FT_primeTI_hyp StypeP.
Let ctiWG : cyclicTI_hypothesis G defW := pddS.
Local Notation Sfacts := (FTtypeP_facts maxS StypeP).

Let ntW1 : W1 :!=: 1. Proof. by have [[]] := StypeP. Qed.
Let ntW2 : W2 :!=: 1. Proof. by have [_ _ _ []] := StypeP. Qed.
Let cycW1 : cyclic W1. Proof. by have [[]] := StypeP. Qed.
Let cycW2 : cyclic W2. Proof. by have [_ _ _ []] := StypeP. Qed.

Let p := #|W2|.
Let q := #|W1|.

Let pr_p : prime p. Proof. by have [] := FTtypeP_primes maxS StypeP. Qed.
Let pr_q : prime q. Proof. by have [] := FTtypeP_primes maxS StypeP. Qed.

Let qgt2 : q > 2. Proof. by rewrite odd_gt2 ?mFT_odd ?cardG_gt1. Qed.
Let pgt2 : p > 2. Proof. by rewrite odd_gt2 ?mFT_odd ?cardG_gt1. Qed.

Let coPUq : coprime #|PU| q.
Proof. by rewrite (coprime_sdprod_Hall_r defS); have [[]] := StypeP. Qed.

Let sW2P: W2 \subset P. Proof. by have [_ _ _ []] := StypeP. Qed.

Let p'q : q != p.
Proof.
by rewrite -dvdn_prime2 -?prime_coprime -?(cyclic_dprod defW) //; case: ctiWG.
Qed.

Let nirrW1 : #|Iirr W1| = q. Proof. by rewrite card_Iirr_cyclic. Qed.
Let nirrW2 : #|Iirr W2| = p. Proof. by rewrite card_Iirr_cyclic. Qed.
Let NirrW1 : Nirr W1 = q. Proof. by rewrite -nirrW1 card_ord. Qed.
Let NirrW2 : Nirr W2 = p. Proof. by rewrite -nirrW2 card_ord. Qed.

Local Open Scope ring_scope.

Let sigma := (cyclicTIiso ctiWG).
Let w_ i j := (cyclicTIirr defW i j).
Local Notation eta_ i j := (sigma (w_ i j)).

Let mu_ := primeTIred ptiWS.
Local Notation tau := (FT_Dade0 maxS).

Let calS0 := seqIndD PU S S`_\s 1.
Let rmR := FTtypeP_coh_base maxS StypeP.
Let scohS0 : subcoherent calS0 tau rmR.
Proof. exact: FTtypeP_subcoherent StypeP. Qed.

Let calS := seqIndD PU S P 1.
Let sSS0 : cfConjC_subset calS calS0.
Proof. exact/seqInd_conjC_subset1/Fcore_sub_FTcore. Qed.

Local Notation calH := (seqIndT H S).
Local Notation calHuq := (FTtypeP_Ind_Fitting_1 maxS StypeP).

Section Thirteen_10_to_13_15.

(* This section factors the assumption that S contains an irreducible induced *)
(* from a linear character of H. It does not actually export (13.4) and       *)
(* and (4.11) but instead uses them to carry out the bulk of the proofs of    *)
(* (4.12), (4.13) and (4.15). The combinatorial bound m is also local to this *)
(* Section, but (4.10) has to be exported from an inner Section that factors  *)
(* facts about T, the typeP pair associate of S.                              *)
(* Note that u and c are bound locally to this section; we will set u = #|U|  *)
(* after this section.                                                        *)

Variable lambda : 'CF(S).
Hypotheses (Slam : lambda \in calS) (irrHlam : irrIndH lambda).
Let Hlam : lambda \in calH. Proof. by have [] := andP irrHlam. Qed. 
Let Ilam : lambda \in irr S. Proof. by have [] := andP irrHlam. Qed. 

Let c := #|C|.
Let u := #|U : C|.
Let oU : #|U| = (u * c)%N. Proof. by rewrite mulnC Lagrange ?subsetIl. Qed.

Let m : algC := 1 - q.-1%:R^-1 - q.-1%:R / (q ^ p)%:R + (q.-1 * q ^ p)%:R^-1.

Section Thirteen_4_10.

(* This Section factors assumptions and facts about T, including Lemma (13.4) *)
(* is local to this Section.                                                  *)

Variables T V : {group gT}.
Hypotheses (maxT : T \in 'M) (xdefW : W2 \x W1 = W).
Hypothesis TtypeP : of_typeP T V xdefW.

Local Notation Q := (gval T)`_\F.
Local Notation D := 'C_(gval V)(Q).
Local Notation K := 'F(gval T).
Let v := #|V : D|.

Local Notation calT := (seqIndD T^`(1) T (gval T)`_\F 1).

(* This part of the proof of (13.4) is reused in (13.10). *)
Let tiHK: class_support H^# G :&: class_support K^# G = set0.
Proof.
apply/eqP/set0Pn => [[_ /setIP[/imset2P[x g1 H1x _ ->] /imset2P[xg g2]]]].
pose g := (g2 * g1^-1)%g => /setD1P[_ Kxg] _ Dxg.
have{Kxg Dxg} Kgx: x \in K :^ g by rewrite conjsgM mem_conjgV Dxg memJ_conjg.
have{Kgx} cxQg: Q :^ g \subset 'C[x].
  rewrite sub_cent1 (subsetP _ _ Kgx) // centJ conjSg centsC.
  have [/dprodW/mulG_sub[/subset_trans-> //=]] := typeP_context TtypeP.
  exact: FTtypeP_Fitting_abelian TtypeP.
have{cxQg} sQgS: Q :^ g \subset S.
  have sH1A0 := subset_trans (Fitting_sub_FTsupp maxS) (FTsupp_sub0 S).
  have{sH1A0} A0x: x \in 'A0(S) := subsetP sH1A0 x H1x.
  have [_ _ _ _ [tiA0 _]] := Sfacts.
  by have:= cent1_normedTI tiA0 A0x; rewrite setTI; apply: subset_trans.
have /pHallP[_ eq_Sq_q]: q.-Hall(S) W1.
  have qW1: q.-group W1 by rewrite /pgroup pnat_id.
  have [|//] := coprime_mulGp_Hall (sdprodW defS) _ qW1.
  by rewrite /pgroup p'natE // -prime_coprime // coprime_sym.
have:= partn_dvd q (cardG_gt0 _) (cardSg sQgS).
rewrite cardJg /= -eq_Sq_q => /(dvdn_leq_log q (cardG_gt0 _))/idPn[].
have [_ [_ ->] _ _ _] := FTtypeP_facts maxT TtypeP.
by rewrite -ltnNge p_part !pfactorK // logn_prime // eqxx ltnW.
Qed.

(* This is Peterfalvi (13.4). *)
Let T_Galois : [/\ typeP_Galois TtypeP, D = 1%g & v = (q ^ p).-1 %/ q.-1].
Proof.
apply: FTtypeP_no_Ind_Fitting_facts => //; apply/hasPn=> theta Ttheta.
apply/andP=> [[/= irr_theta Ktheta]]; set calK := seqIndT _ T in Ktheta.
have [tau1S cohS [bS _ Dtau1Smu]] := FTtypeP_coherence maxS StypeP.
have [tau1T cohT [bT _ Dtau1Tnu]] := FTtypeP_coherence maxT TtypeP.
have [[[Itau1S Ztau1S] Dtau1S] [[Itau1T Ztau1T] Dtau1T]] := (cohS, cohT).
have onF0 := cfun_onS (Fitting_sub_FTsupp0 _).
pose HG := class_support H^# G; pose KG := class_support K^# G.
have Hdlambda xi:
  xi \in calH -> xi \in calS -> tau1S (lambda - xi) \in 'CF(G, HG).
- move=> Hxi Sxi; have H1dxi: lambda - xi \in 'CF(S, H^#).
    rewrite cfun_onD1 rpredB ?((seqInd_on (gFnormal _ _)) setT) //=.
    by rewrite !cfunE !calHuq ?subrr.
  rewrite Dtau1S ?zcharD1E ?rpredB ?mem_zchar ?(cfun_on0 H1dxi) ?inE ?eqxx //=.
  by have [_ _ _ _ [_ ->]] := Sfacts; rewrite ?onF0 // cfInd_on ?subsetT.
have Kdtheta xi:
  xi \in calK -> xi \in calT -> tau1T (theta - xi) \in 'CF(G, KG).
- move=> Kxi Txi; have K1dxi: theta - xi \in 'CF(T, K^#).
    rewrite cfun_onD1 rpredB ?((seqInd_on (gFnormal _ _)) setT) //=.
    by rewrite !cfunE !(FTtypeP_Ind_Fitting_1 _ TtypeP) ?subrr.
  rewrite Dtau1T ?zcharD1E ?rpredB ?mem_zchar ?(cfun_on0 K1dxi) ?inE ?eqxx //=.
  have [_ _ _ _ [_ ->]] := FTtypeP_facts maxT TtypeP; last exact: onF0.
  by rewrite cfInd_on ?subsetT.
have oHK alpha beta:
  alpha \in 'CF(G, HG) -> beta \in 'CF(G, KG) -> '[alpha, beta] = 0.
- by move=> Halpha Kbeta;  rewrite (cfdotElr Halpha Kbeta) tiHK big_set0 mulr0.
have o_lambda_theta: '[tau1S lambda, tau1T theta] = 0.
  pose S1 := lambda :: lambda^*%CF; pose T1 := theta :: theta^*%CF.
  have sS1S: {subset S1 <= calS} by apply/allP; rewrite /= Slam cfAut_seqInd.
  have sT1T: {subset T1 <= calT} by apply/allP; rewrite /= Ttheta cfAut_seqInd.
  have ooS1: orthonormal (map tau1S S1).
    rewrite map_orthonormal //; first exact: (sub_in2 (zchar_subset sS1S)).
    apply: seqInd_conjC_ortho2 Slam; rewrite ?gFnormal ?mFT_odd //.
    by have /mulG_sub[] := sdprodW defPU.
  have ooT1: orthonormal (map tau1T T1).
    rewrite map_orthonormal //; first exact: (sub_in2 (zchar_subset sT1T)).
    apply: seqInd_conjC_ortho2 Ttheta; rewrite ?gFnormal ?mFT_odd //.
    by have [_ [_ _ _ /sdprodW/mulG_sub[]]] := TtypeP.
  have /andP/orthonormal_vchar_diff_ortho := conj ooS1 ooT1; apply.
    by split; apply/allP; rewrite /= ?Ztau1S ?Ztau1T ?mem_zchar ?cfAut_seqInd.
  have on1'G M beta: beta \in 'CF(G, class_support M^# G) -> beta 1%g = 0.
    move/cfun_on0->; rewrite // class_supportEr -cover_imset -class_supportD1.
    by rewrite !inE eqxx.
  rewrite -!raddfB; set alpha := tau1S _; set beta := tau1T _.
  have [Halpha Kbeta]: alpha \in 'CF(G, HG) /\ beta \in 'CF(G, KG).
    by rewrite Hdlambda ?Kdtheta ?cfAut_seqInd ?cfAut_seqIndT.
  by rewrite oHK // {1}(on1'G _ _ Halpha) (on1'G _ _ Kbeta) !eqxx.
pose ptiWT := FT_primeTI_hyp TtypeP; pose nu_ := primeTIred ptiWT.
have etaC := cycTIisoC (FT_cyclicTI_hyp StypeP) (FT_cyclicTI_hyp TtypeP).
have /idPn[]: '[tau1S (lambda - mu_ #1), tau1T (theta - nu_ #1)] == 0.
  rewrite oHK //.
    by rewrite Hdlambda ?FTseqInd_TIred ?FTprTIred_Ind_Fitting ?Iirr1_neq0.
  by rewrite Kdtheta ?FTseqInd_TIred ?FTprTIred_Ind_Fitting ?Iirr1_neq0.
rewrite !raddfB /= !cfdotBl o_lambda_theta Dtau1Smu ?Dtau1Tnu ?Iirr1_neq0 //.
rewrite !cfdotZl !cfdotZr rmorph_sign !cfdot_suml big1 => [|i _]; last first.
  rewrite cfdotC etaC (coherent_ortho_cycTIiso TtypeP _ cohT) ?conjC0 //.
  by apply: seqInd_conjC_subset1; apply: Fcore_sub_FTcore.
rewrite cfdot_sumr big1 ?mulr0 ?subr0 ?add0r ?opprK => [|j _]; last first.
  by rewrite -etaC (coherent_ortho_cycTIiso StypeP _ cohS).
set i1 := iter bT _ #1; set j1 := iter bS _ #1.
rewrite !mulf_eq0 !signr_eq0 (bigD1 i1) //= addrC big1 => [|i i1'i]; last first.
  rewrite etaC cfdot_sumr big1 // => j _; rewrite cfdot_cycTIiso.
  by rewrite (negPf i1'i) andbF.
rewrite etaC cfdot_sumr (bigD1 j1) //= cfdot_cycTIiso !eqxx addrCA.
rewrite big1 ?addr0 ?oner_eq0 // => j j1'j; rewrite cfdot_cycTIiso.
by rewrite eq_sym (negPf j1'j).
Qed.

(* This is Peterfalvi (13.10). *)
Lemma FTtypeP_compl_ker_ratio_lb : m * (p ^ q.-1)%:R / q%:R < u%:R / c%:R.
Proof.
have [tau1 cohS cohSmu] := FTtypeP_coherence maxS StypeP.
pose lam1 := tau1 lambda; pose eta10 := eta_ #1 0.
pose H1G := class_support H^# G; pose K1G := class_support K^# G.
pose G0 := ~: (class_support H G :|: class_support K G).
pose invJ (f : gT -> algC) := forall y x, f (x ^ y) = f x.
pose nm2 (chi : 'CF(G)) x := `|chi x| ^+ 2; pose g : algC := #|G|%:R.
have injJnm2 chi: invJ (nm2 chi) by move=> y x; rewrite /nm2 cfunJ ?inE.
have nm2_dirr chi: chi \in dirr G -> g^-1 <= nm2 chi 1%g / g.
  case/dIrrP=> d ->; rewrite -{1}[g^-1]mul1r ler_pmul2r ?invr_gt0 ?gt0CG //.
  rewrite expr_ge1 ?normr_ge0 // cfunE normrMsign.
  by rewrite irr1_degree normr_nat ler1n irr_degree_gt0.
pose mean (F M : {set gT}) (f : gT -> algC) := (\sum_(x in F) f x) / #|M|%:R.
have meanTI M (F := 'F(gval M)^#) (FG := class_support F G) f:
  M \in 'M -> normedTI F G M -> invJ f -> mean FG G f = mean F M f.
- move=> maxM /and3P[ntF tiF /eqP defN] fJ; apply: canLR (mulfK (neq0CG _)) _.
  rewrite (set_partition_big _ (partition_class_support ntF tiF)) /=.
  rewrite mulrAC -mulrA -natf_indexg ?subsetT //=.
  have ->: #|G : M| = #|F :^: G| by rewrite card_conjugates defN.
  rewrite mulr_natr -sumr_const; apply: eq_bigr => _ /imsetP[y _ ->].
  by rewrite (big_imset _ (in2W (conjg_inj _))) (eq_bigr _ (in1W (fJ y))).
have{meanTI} meanG f :
  invJ f -> mean G G f = f 1%g / g + mean H^# S f + mean K^# T f + mean G0 G f.
- have type24 maxM := compl_of_typeII_IV maxM _ (FTtype5_exclusion maxM).
  have tiH: normedTI H^# G S by have/type24[] := StypeP.
  have{type24} tiK: normedTI K^# G T by have/type24[] := TtypeP.
  move=> fJ; rewrite -!meanTI // {1}/mean (big_setD1 1%g) // (big_setID H1G) /=.
  rewrite [in rhs in _ + (_ + rhs)](big_setID K1G) /= -/g -!mulrDl !addrA.
  congr ((_ + _ + _ + _) / g); rewrite ?(setIidPr _) // /H1G /K1G. 
  + by rewrite class_supportEr -cover_imset -class_supportD1 setSD ?subsetT.
  + rewrite subsetD -setI_eq0 setIC tiHK eqxx andbT.
    by rewrite class_supportEr -cover_imset -class_supportD1 setSD ?subsetT.
  rewrite !class_supportEr -!cover_imset -!class_supportD1.
  apply: eq_bigl => x; rewrite !inE andbT -!negb_or orbCA orbA orbC.
  by case: (x =P 1%g) => //= ->; rewrite mem_class_support ?group1.
have lam1_ub: mean G0 G (nm2 lam1) <= lambda 1%g ^+ 2 / #|S|%:R - g^-1.
  have [[Itau1 Ztau1] _] := cohS. 
  have{Itau1} n1lam1: '[lam1] = 1 by rewrite Itau1 ?mem_zchar ?irrWnorm.
  have{Ztau1} Zlam1: lam1 \in 'Z[irr G] by rewrite Ztau1 ?mem_zchar.
  rewrite -ler_opp2 opprB -(ler_add2l '[lam1]) {1}n1lam1 addrCA.
  rewrite (cfnormE (cfun_onG _)) (mulrC g^-1) [_ / g](meanG (nm2 _)) // addrK.
  rewrite -addrA ler_add ?nm2_dirr //; first by rewrite dirrE Zlam1 n1lam1 /=.
  rewrite ler_paddr ?divr_ge0 ?ler0n //.
    by apply: sumr_ge0 => x _; rewrite exprn_ge0 ?normr_ge0.
  rewrite ler_pdivl_mulr ?gt0CG // mulrBl mul1r divfK ?neq0CG //.
  by rewrite (FTtypeP_sum_Ind_Fitting_lb StypeP).
pose ub_lam1 : algC := (#|T^`(1)%g|%:R - (v ^ 2)%:R - #|Q|.-1%:R) / #|T|%:R.
have [_ D_1 Dv] := T_Galois.
have defK : K = Q by have [<-] := typeP_context TtypeP; rewrite D_1 dprodg1.
have eta10_ub: mean G0 G (nm2 (eta_ #1 0)) <= #|G0|%:R / g - ub_lam1.
  rewrite -ler_opp2 opprB -(ler_add2l '[eta_ #1 0]) {2}(cfnormE (cfun_onG _)).
  rewrite (mulrC g^-1) [_ / g in rhs in _ <= rhs](meanG (nm2 _)) // addrK.
  have ->: '[eta_ #1 0] = mean G G (fun _ => 1).
    by rewrite /mean sumr_const cfdot_cycTIiso eqxx divff ?neq0CG.
  rewrite meanG // [in lhs in lhs <= _]/mean !sumr_const addrACA subrr addr0.
  rewrite [lhs in lhs <= _]addrAC -addrA -mulrDl (cardsD1 1%g Q) group1 -defK.
  rewrite mul1r subrK ?ler_add ?ler_pmul2r ?invr_gt0 ?gt0CG //.
  - by rewrite nm2_dirr ?cycTIiso_dirr.
  - exact: (FTtypeP_sum_cycTIiso10_lb _ StypeP).
  congr (_ <= _): (FTtypeP_sum_cycTIiso01_lb maxT TtypeP).
  by apply: eq_bigr => x _; congr (nm2 _ x); apply: cycTIisoC.
have: ub_lam1 < lambda 1%g ^+ 2 / #|S|%:R.
  rewrite -[_ / _](subrK g^-1) ltr_spaddr ?invr_gt0 ?gt0CG //.
  rewrite -(ler_add2r (#|G0|%:R / g)) -ler_subr_addl -addrA.
  apply: ler_trans (ler_add lam1_ub eta10_ub).
  rewrite -mulrDl -big_split /= ler_pmul2r ?invr_gt0 ?gt0CG //.
  exact: FTtypeP_sum_nonFitting_lb.
rewrite calHuq // -/u -(sdprod_card defS) -/q -(sdprod_card defPU) oU mulnC.
rewrite mulnCA mulnAC !natrM !invfM expr2 !mulrA !mulfK ?neq0CG ?neq0CiG //.
rewrite mulrAC ltr_pdivl_mulr ?ltr_pdivr_mulr ?gt0CG //.
congr (_ < _); last by rewrite -mulrA mulrC.
have [_ [_ ->] _ _ _] := Sfacts; rewrite -/p -/q.
rewrite -{1}(ltn_predK qgt2) expnS natrM mulrA; congr (_ * _).
have /sdprod_card oT: T^`(1) ><| W2 = T by have [[]] := TtypeP.
rewrite /ub_lam1 -{}oT natrM invfM mulrA divfK ?mulrBl ?divff ?neq0CG //.
have /sdprod_card <-: Q ><| V = T^`(1)%g by have [_ []] := TtypeP.
have ->: #|V| = v by rewrite /v D_1 indexg1.
rewrite mulnC !natrM invfM mulrA mulfK ?neq0CiG //.
have [_ [_ oQ] _ _ _] := FTtypeP_facts maxT TtypeP; rewrite -/p -/q /= in oQ.
rewrite Dv natf_div ?dvdn_pred_predX // oQ.
rewrite invfM invrK -mulrA -subn1 mulVKf ?gtr_eqF ?ltr0n //; last first.
  by rewrite subn_gt0 -(exp1n p) ltn_exp2r ltnW // ltnW.
rewrite -oQ natrB ?cardG_gt0 // !mulrBl mul1r mulrC mulKf ?neq0CG // -invfM.
by rewrite -natrM oQ opprD opprK addrA addrAC.
Qed.

End Thirteen_4_10.

(* This is (13.10) without the dependency on T. *)
Let gen_lb_uc : m * (p ^ q.-1)%:R / q%:R < u%:R / c%:R.
Proof.
have [T pairST [xdefW [V TtypeP]]] := FTtypeP_pair_witness maxS StypeP.
by apply: FTtypeP_compl_ker_ratio_lb TtypeP; have [[]] := pairST.
Qed.

Import ssrint.
(* This is Peterfalvi (13.11). *)
Let lb_m_cases :
 [/\ (*a*) (q >= 7)%N -> m > 8%:R / 10%:R,
     (*b*) (q >= 5)%N -> m > 7%:R / 10%:R
   & (*c*) q = 3 ->
           m > 49%:R / 100 %:R /\ u%:R / c%:R > (p ^ 2).-1%:R / 6%:R :> algC].
Proof.
pose mkrat b d := fracq (b, d%:Z).
pose test r b d := 1 - mkrat 1 r.-1 - mkrat 1 (r ^ 2)%N > mkrat b%:Z d.
have lb_m r b d: test r.+2 b d -> (q >= r.+2)%N -> m > b%:R / d%:R.
  rewrite /test /mkrat !fracqE !CratrE /= => ub_bd le_r_q.
  apply: ltr_le_trans ub_bd _; rewrite ler_paddr ?invr_ge0 ?ler0n //.
  rewrite -!addrA ler_add2l -!opprD ler_opp2 ler_add //.
    rewrite mul1r lef_pinv ?qualifE ?ltr0n //; last by rewrite -(subnKC qgt2).
    by rewrite leC_nat -ltnS (ltn_predK qgt2).
  rewrite -(ltn_predK pgt2) expnSr natrM invfM mulrA.
  rewrite ler_pdivr_mulr ?gt0CG // mulrAC mul1r -subn1.
  rewrite ler_pmul ?invr_ge0 ?ler0n ?leC_nat ?leq_subr //.
  rewrite lef_pinv ?qualifE ?ltr0n ?leC_nat ?expn_gt0 ?(prime_gt0 pr_q) //.
  apply: leq_trans (_ : q ^ 2 <= _)%N; first by rewrite leq_exp2r.
  by rewrite -(subnKC qgt2) leq_pexp2l // -subn1 ltn_subRL.
split=> [||q3]; try by apply: lb_m; compute.
pose d r : algC := (3 ^ r.-1)%:R^-1; pose f r := (r ^ 2)%:R * d r.
have Dm: m = (1 - d p) / 2%:R.
  rewrite mulrBl mul1r -mulrN mulrC /m q3 /= addrAC -addrA natrM invfM -mulrBl.
  rewrite -{1}(ltn_predK pgt2) expnS natrM invfM mulrA.
  by congr (_ + _ / _); apply/eqP; rewrite -!CratrE; compute.
split; last apply: ler_lt_trans gen_lb_uc.
  apply: ltr_le_trans (_ : (1 - d 5) / 2%:R <= _).
    by rewrite /d -!CratrE; compute.
  rewrite Dm ler_pmul2r ?invr_gt0 ?ltr0n // ler_add2l ler_opp2.
  rewrite lef_pinv ?qualifE ?ltr0n ?expn_gt0 // leC_nat leq_pexp2l //=.
  by rewrite -subn1 ltn_subRL odd_geq ?mFT_odd //= ltn_neqAle pgt2 andbT -q3.
rewrite -mulrA mulrCA Dm -mulrA -invfM -natrM mulrA q3 mulrBr mulr1.
rewrite ler_pmul2r ?invr_gt0 ?ltr0n //= -subn1 natrB ?expn_gt0 ?prime_gt0 //.
rewrite ler_add2l ler_opp2 -/(f p) -(subnKC pgt2).
elim: (p - 3)%N => [|r]; first by rewrite /f /d -!CratrE; compute.
apply: ler_trans; rewrite addnS /f /d; set x := (3 + r)%N.
rewrite ler_pdivr_mulr ?ltr0n ?expn_gt0 // mulrAC (expnS 3) (natrM _ 3).
rewrite mulrA mulfK ?gtr_eqF ?ltr0n ?expn_gt0 //.
rewrite -ler_pdivr_mull ?ltr0n // !natrX -exprVn -exprMn.
rewrite mulrS mulrDr mulr1 mulVf ?pnatr_eq0 //.
apply: ler_trans (_ : (3%:R^-1 + 1) ^+ 2 <= _); last by rewrite -!CratrE.
rewrite ler_sqr ?rpredD ?rpred1 ?rpredV ?rpred_nat // ler_add2r.
by rewrite lef_pinv ?qualifE ?ltr0n ?leC_nat.
Qed.

(* This corollary of (13.11) is used in both (13.12) and (13.15). *)
Let small_m_q3 : m < (q * p)%:R / (q.*2.+1 * p.-1)%:R -> q = 3 /\ (p >= 5)%N.
Proof.
move=> ub_m; have [lb7_m lb5_m _] := lb_m_cases.
have [p3 | p_neq3] := eqVneq p 3.
  have ub7_m: ~~ (8%:R / 10%:R < m).
    rewrite ltr_gtF // (ltr_le_trans ub_m) // p3 /=.
    apply: ler_trans (_ : 3%:R / 4%:R <= _); last first.
      by rewrite -!CratrE; compute.
    rewrite ler_pdivl_mulr ?ltr0n // mulrAC ler_pdivr_mulr ?ltr0n ?muln_gt0 //.
    by rewrite -!natrM leC_nat mulnCA mulSn -muln2 -!mulnA leq_addl.
  have{ub7_m} q5: q = 5.
    apply: contraNeq ub7_m; rewrite neq_ltn odd_ltn ?mFT_odd //= ltnS leqNgt.
    by rewrite ltn_neqAle qgt2 -{1}p3 eq_sym p'q -(odd_geq 7) ?mFT_odd.
  have /implyP := ltr_trans (lb5_m _) ub_m.
  by rewrite q5 p3 -!CratrE; compute.
have pge5: (5 <= p)%N by rewrite odd_geq ?mFT_odd // ltn_neqAle eq_sym p_neq3.
have ub5_m: ~~ (7%:R / 10%:R < m).
  rewrite ltr_gtF // (ltr_le_trans ub_m) //.
  apply: ler_trans (_ : 2%:R^-1 * (1 + 4%:R^-1) <= _); last first.
    by rewrite -!CratrE; compute.
  rewrite !natrM invfM mulrACA ler_pmul ?divr_ge0 ?ler0n //.
    rewrite ler_pdivr_mulr ?ler_pdivl_mull ?ltr0n // -natrM mul2n leC_nat.
    by rewrite ltnW.
  rewrite -(subnKC pge5) [_%:R]mulrSr mulrDl divff ?pnatr_eq0 // ler_add2l.
  by rewrite mul1r lef_pinv ?qualifE ?ltr0n // leC_nat.
split=> //; apply: contraNeq ub5_m.
by rewrite neq_ltn ltnNge qgt2 -(odd_geq 5) ?mFT_odd.
Qed.

(* A more usable form for (13.10). *)
Let gen_ub_m : m < (q * u)%:R / (c * p ^ q.-1)%:R.
Proof.
rewrite !natrM invfM mulrA ltr_pdivl_mulr ?ltr0n ?expn_gt0 ?cardG_gt0 //.
by rewrite -mulrA -ltr_pdivr_mull ?gt0CG // mulrC.
Qed.

(* This is the bulk of the proof of Peterfalvi (13.12). *)
Lemma FTtypeP_Ind_Fitting_reg_Fcore : c = 1%N.
Proof.
apply/eqP/wlog_neg; rewrite eqn_leq cardG_gt0 andbT -ltnNge => c_gt1.
have ub_m: m < (q * (p ^ q).-1)%:R / (c * p ^ q.-1 * p.-1)%:R.
  rewrite 2!natrM invfM mulrACA mulrAC -natf_div ?dvdn_pred_predX // -natrM.
  rewrite (ltr_le_trans gen_ub_m) // ler_pmul ?invr_ge0 ?ler0n // leC_nat.
  by rewrite leq_mul //; case: Sfacts.
have regCW1: semiregular C W1.
  have [[_ _ /Frobenius_reg_ker regUW1 _] _ _ _] := FTtypeP_facts maxS StypeP.
  by move=> _ y /regUW1 regUx; rewrite setIAC regUx setI1g.
have{regCW1} dv_2q_c1: q.*2 %| c.-1.
  rewrite -(subnKC c_gt1) -mul2n Gauss_dvd ?coprime2n ?dvdn2 ?mFT_odd //=.
  rewrite odd_sub ?mFT_odd -?subSn // subn2 regular_norm_dvd_pred //.
  have /mulG_sub[_ sW1S] := sdprodW defS.
  apply: normsI; first by have [_ []] := StypeP.
  by rewrite (subset_trans sW1S) ?norms_cent ?gFnorm.
have [q3 pge5]: q = 3 /\ (p >= 5)%N.
  apply: small_m_q3; apply: (ltr_le_trans ub_m).
  rewrite !natrM -!mulrA ler_pmul2l ?gt0CG //.
  rewrite !invfM !mulrA -(subnKC pgt2) ler_pmul2r ?invr_gt0 ?ltr0n //.
  rewrite ler_pdivr_mulr ?ltr0n ?expn_gt0 // mulrAC -natrM -expnS.
  rewrite prednK ?cardG_gt0 // ler_pmul ?invr_ge0 ?ler0n ?leC_nat ?leq_pred //.
  rewrite lef_pinv ?qualifE ?gt0CG ?ltr0n // leC_nat.
  by rewrite -(subnKC c_gt1) ltnS dvdn_leq //= -subSn ?subn2.
have [_ _ [//|lb_m lb_uc]] := lb_m_cases.
pose sum3 r : algC := (r.+1 ^ 2)%:R^-1 + r.+1%:R^-1 + 1.
have [b Dc1] := dvdnP dv_2q_c1; rewrite q3 in Dc1.
have [b0 | b_gt0] := posnP b; first by rewrite b0 -(subnKC c_gt1) in Dc1.
have ub3_m r a: (r < p)%N -> (a <= b)%N -> m < 3%:R / (a * 6).+1%:R * sum3 r.
  move=> lb_p lb_b; apply: ltr_le_trans ub_m _.
  rewrite !natrM !invfM mulrACA -!mulrA q3 ler_pmul2l ?ltr0n //.
  rewrite -(ltn_predK c_gt1) Dc1 ler_pmul ?mulr_ge0 ?invr_ge0 ?ler0n //.
    by rewrite lef_pinv ?qualifE ?ltr0n // leC_nat ltnS leq_mul.
  rewrite predn_exp mulnC natrM 2!big_ord_recl big_ord1 /= /bump /= expn1.
  rewrite -(subnKC (ltnW pgt2)) add2n in lb_p *.
  rewrite mulfK ?pnatr_eq0 // addnA 2!natrD 2!mulrDr mulr1 {-1}natrM invfM.
  rewrite mulrA divfK ?mulVf ?pnatr_eq0 // ler_add2r.
  by rewrite ler_add ?lef_pinv ?qualifE ?ltr0n ?leC_nat ?leq_sqr.
have beq1: b = 1%N.
  apply: contraTeq lb_m; rewrite neq_ltn ltnNge b_gt0 => /(ub3_m 4) ub41.
  by rewrite ltr_gtF // (ltr_trans (ub41 _)) // /sum3 -!CratrE; compute.
have c7: c = 7 by rewrite -(ltn_predK c_gt1) Dc1 beq1.
have plt11: (p < 11)%N.
  rewrite ltnNge; apply: contraL lb_m => /ub3_m/(_ b_gt0) ub100.
  by rewrite ltr_gtF // (ltr_trans ub100) // /sum3 -!CratrE; compute.
have{plt11} p5: p = 5.
  suffices: p \in [seq r <- iota q.+1 7 | prime r & coprime r c].
    by rewrite c7 q3 inE => /eqP.
  rewrite mem_filter mem_iota ltn_neqAle p'q q3 pgt2 pr_p (coprimeSg sW2P) //.
  by rewrite (coprimegS _ (Ptype_Fcore_coprime StypeP)) ?subIset ?joing_subl.
have [galS | gal'S] := boolP (typeP_Galois StypeP); last first.
  have [H1 [_ _ _ _ []]] := typeP_Galois_Pn maxS notStype5 gal'S.
  case/pdivP=> r pr_r r_dv_a /(dvdn_trans r_dv_a)/idPn[].
  rewrite Ptype_factor_prime // -/p p5 (Euclid_dvdM 2 2) // gtnNdvd //.
  rewrite odd_prime_gt2 ?(dvdn_odd (dvdn_trans r_dv_a (dvdn_indexg _ _))) //.
  by rewrite mFT_odd.
have{galS} u_dv_31: u %| 31.
  have [_ _ [_ _]] := typeP_Galois_P maxS notStype5 galS.
  rewrite Ptype_factor_prime ?Ptype_Fcompl_kernel_cent // -/p -/q p5 q3.
  rewrite card_quotient // normsI ?normG ?norms_cent //.
  by have [] := sdprodP defPU.
have hallH: Hall S H.
  rewrite /Hall -divgS ?gFsub //= -(sdprod_card defS) -(sdprod_card defPU).
  rewrite -(dprod_card defH) -mulnA divnMl ?cardG_gt0 // -/c oU mulnAC c7.
  have [_ [_ ->] _ _ _] := FTtypeP_facts maxS StypeP.
  by rewrite mulnK // -/q -/p q3 p5 coprime_mulr (coprime_dvdr u_dv_31).
rewrite -(leq_pmul2l (cardG_gt0 P)) muln1 (dprod_card defH) subset_leq_card //.
by rewrite (Fcore_max (Hall_pi hallH)) ?gFnormal ?Fitting_nil.
Qed.
Local Notation c1 := FTtypeP_Ind_Fitting_reg_Fcore.

(* This is the main part of the proof of Peterfalvi (13.13). *)
Lemma FTtypeP_Ind_Fitting_nonGalois_facts :
  ~~ typeP_Galois StypeP -> q = 3 /\ #|U| = (p.-1./2 ^ 2)%N.
Proof.
have even_p1: 2 %| p.-1 by rewrite -subn1 -subSS dvdn_sub ?dvdn2 //= mFT_odd.
move=> gal'S; have{gal'S} u_dv_p2q: u %| p.-1./2 ^ q.-1.
  have [H1 [_ _ _ _ []]] := typeP_Galois_Pn maxS notStype5 gal'S.
  rewrite Ptype_factor_prime ?Ptype_Fcompl_kernel_cent // -/p -/q.
  set a := #|U : _| => a_gt1 a_dv_p1 _ [Uhat isoUhat].
  have a_odd: odd a by rewrite (dvdn_odd (dvdn_indexg _ _)) ?mFT_odd.
  have [_ _ nPU _] := sdprodP defPU.
  rewrite /u -card_quotient ?normsI ?normG ?norms_cent // (card_isog isoUhat).
  apply: dvdn_trans (cardSg (subsetT _)) _; rewrite cardsT card_matrix mul1n.
  rewrite card_ord Zp_cast ?dvdn_exp2r // -(@Gauss_dvdl a _ 2) ?coprimen2 //.
  by rewrite -divn2 divnK.
have [_ lb5_m lb3_m] := lb_m_cases.
pose f r : algC := r%:R / (2 ^ r.-1)%:R.
have ub_m: m < f q.
  apply: ltr_le_trans gen_ub_m _; rewrite c1 mul1n.
  rewrite natrM ler_pdivr_mulr ?ltr0n ?expn_gt0 ?cardG_gt0 // -mulrA.
  rewrite ler_wpmul2l ?ler0n // mulrC !natrX -expr_div_n.
  apply: ler_trans (_ : (p.-1 %/ 2)%:R ^+ q.-1 <= _).
    by rewrite -natrX leC_nat divn2 dvdn_leq // expn_gt0 -(subnKC pgt2).
  rewrite -(subnKC qgt2) ler_pexpn2r ?rpred_div ?rpred_nat // natf_div //.
  by rewrite ler_wpmul2r ?invr_ge0 ?ler0n // leC_nat leq_pred.
have{ub_m} q3: q = 3.
  apply: contraTeq ub_m; rewrite neq_ltn ltnNge qgt2 -(odd_geq 5) ?mFT_odd //=.
  move=> qge5; rewrite ltr_gtF // -(subnKC qge5).
  elim: (q - 5)%N => [|r]; last apply: ler_lt_trans.
    by apply: ltr_trans (lb5_m qge5); rewrite /f -!CratrE; compute.
  rewrite addnS ler_pdivr_mulr ?ltr0n ?expn_gt0 // natrM mulrACA mulrA.
  by rewrite divfK ?pnatr_eq0 ?expn_eq0 // mulr_natr mulrS ler_add2r ler1n.
have [[]] := dvdnP u_dv_p2q; rewrite q3; first by rewrite -(subnKC pgt2).
case=> [|b] Du; first by rewrite oU c1 Du muln1 mul1n.
have [_ /idPn[]] := lb3_m q3; rewrite c1 divr1 ler_gtF //.
apply: ler_trans (_ : (p.-1 ^ 2)%:R / 8%:R <= _).
  rewrite (natrX _ 2 3) exprSr invfM mulrA natrX -expr_div_n -natf_div // divn2.
  by rewrite -natrX Du ler_pdivl_mulr ?ltr0n // mulrC -natrM leC_nat leq_mul.
rewrite -!subn1 (subn_sqr p 1) !natrM -!mulrA ler_wpmul2l ?ler0n //.
rewrite ler_pdivr_mulr 1?mulrAC ?ler_pdivl_mulr ?ltr0n // -!natrM leC_nat.
rewrite (mulnA _ 3 2) (mulnA _ 4 2) leq_mul // mulnBl mulnDl leq_subLR.
by rewrite addnCA (mulnSr p 3) -addnA leq_addr.
Qed.
 
(* This is the bulk of the proof of Peterfalvi (13.15). *)
(* We improve slightly on the end of the argument by maing better use of the  *)
(* bound on u to get p = 5 directly.                                          *)
Lemma FTtypeP_Ind_Fitting_Galois_ub b :
  (p ^ q).-1 %/ p.-1 = (b * u)%N -> (b <= q.*2)%N.
Proof.
move=> Dbu; have: U :!=: 1%g by have [[_ _ /Frobenius_context[]]] := Sfacts.
rewrite trivg_card1 oU c1 muln1 leqNgt; apply: contra => bgt2q.
have [|q3 pge5] := small_m_q3.
  apply: ltr_le_trans gen_ub_m _; rewrite c1 mul1n !natrM -!mulrA.
  rewrite ler_wpmul2l ?ler0n // ler_pdivr_mulr ?ltr0n ?expn_gt0 ?cardG_gt0 //.
  rewrite mulrAC invfM -natrM -expnS prednK ?cardG_gt0 // mulrCA.
  rewrite ler_pdivl_mull ?ltr0n // -natrM.
  apply: ler_trans (_ : (b * u)%:R <= _); first by rewrite leC_nat leq_mul.
  rewrite -Dbu natf_div ?dvdn_pred_predX // ler_wpmul2r ?invr_ge0 ?ler0n //.
  by rewrite leC_nat leq_pred.
have ub_p: ((p - 3) ^ 2 < 4 ^ 2)%N.
  have [_ _ [] // _] := lb_m_cases; rewrite c1 divr1 ltr_pdivr_mulr ?ltr0n //.
  rewrite -natrM ltC_nat prednK ?expn_gt0 ?cardG_gt0 // => /(leq_mul bgt2q).
  rewrite mulnC mulnA -Dbu q3 predn_exp mulKn; last by rewrite -(subnKC pgt2).
  rewrite 2!big_ord_recl big_ord1 /= /bump /= !mulnDl expn0 expn1.
  rewrite addnA mulnS leq_add2r -(leq_add2r 9) (mulnCA p 2 3) -addnA addnCA.
  by rewrite -leq_subLR -(sqrn_sub pgt2).
have{ub_p pge5} p5: p = 5.
  apply/eqP; rewrite eqn_leq pge5 andbT.
  by rewrite ltn_sqr ltnS leq_subLR -ltnS odd_ltn ?mFT_odd in ub_p.
have bgt1: (1 < b)%N by rewrite -(subnKC bgt2q) q3.
rewrite -(eqn_pmul2l (ltnW bgt1)) muln1 eq_sym.
by apply/eqP/prime_nt_dvdP; rewrite ?dvdn_mulr ?gtn_eqF // -Dbu q3 p5.
Qed.

End Thirteen_10_to_13_15.

(* This is Peterfalvi (13.12). *)
Lemma FTtypeP_reg_Fcore : C :=: 1%g.
Proof.
have [] := boolP (has irrIndH calS); last first.
  by case/(FTtypeP_no_Ind_Fitting_facts maxS StypeP).
by case/hasP=> lambda Slam /FTtypeP_Ind_Fitting_reg_Fcore/card1_trivg->.
Qed.

Lemma Ptype_Fcompl_kernel_trivial : Ptype_Fcompl_kernel StypeP :=: 1%g.
Proof. by rewrite Ptype_Fcompl_kernel_cent ?FTtypeP_reg_Fcore. Qed.

(* Since C is trivial, from here on u will denote #|U|. *)
Let u := #|U|.
Let ustar := (p ^ q).-1 %/ p.-1.

(* This is Peterfalvi (13.13). *)
Lemma FTtypeP_nonGalois_facts :
  ~~ typeP_Galois StypeP -> q = 3 /\ u = (p.-1./2 ^ 2)%N.
Proof.
move=> gal'S; have: has irrIndH calS.
  by apply: contraR gal'S => /(FTtypeP_no_Ind_Fitting_facts maxS StypeP)[].
by case/hasP=> lambda Slam /FTtypeP_Ind_Fitting_nonGalois_facts; apply.
Qed.

Import FinRing.Theory.

(* This is Peterfalvi (13.14). *)
Lemma FTtypeP_primes_mod_cases :
  [/\ odd ustar,
      p == 1 %[mod q] -> q %| ustar
    & p != 1 %[mod q] ->
      [/\ coprime ustar p.-1, ustar == 1 %[mod q]
        & forall b, b %| ustar -> b == 1 %[mod q]]].
Proof. 
have ustar_mod r: p = 1 %[mod r] -> ustar = q %[mod r].
  move=> pr1; rewrite -[q]card_ord -sum1_card /ustar predn_exp //.
  rewrite -(subnKC pgt2) mulKn // subnKC //.
  elim/big_rec2: _ => // i s1 s2 _ eq_s12.
  by rewrite -modnDm -modnXm pr1 eq_s12 modnXm modnDm exp1n.
have ustar_odd: odd ustar.
  by apply: (can_inj oddb); rewrite -modn2 ustar_mod ?modn2 ?mFT_odd.
split=> // [p1_q|p'1_q]; first by rewrite /dvdn ustar_mod ?modnn //; apply/eqP.
have ustar_gt0: (ustar > 0)%N by rewrite odd_geq.
have [p1_gt0 p_gt0]: (p.-1 > 0 /\ p > 0)%N by rewrite -(subnKC pgt2).
have co_ustar_p1: coprime ustar p.-1.
  rewrite coprime_pi' //; apply/pnatP=> //= r pr_r.
  rewrite inE -subn1 -eqn_mod_dvd //= mem_primes pr_r ustar_gt0 => /eqP rp1.
  rewrite /dvdn ustar_mod // [_ == _]dvdn_prime2 //.
  by apply: contraNneq p'1_q => <-; apply/eqP.
suffices ustar_mod_q b: b %| ustar -> b == 1 %[mod q].
  by split; rewrite // ustar_mod_q.
move=> b_dv_ustar; have b_gt0 := dvdn_gt0 ustar_gt0 b_dv_ustar.
rewrite (prod_prime_decomp b_gt0) prime_decompE big_map /= big_seq.
elim/big_rec: _ => // r s /(pi_of_dvd b_dv_ustar ustar_gt0).
rewrite mem_primes -modnMml -modnXm => /and3P[pr_r _ r_dv_ustar].
suffices{s} ->: r = 1 %[mod q] by rewrite modnXm modnMml exp1n mul1n.
apply/eqP; rewrite eqn_mod_dvd ?prime_gt0 // subn1.
have ->: r.-1 = #|[set: {unit 'F_r}]|.
  rewrite card_units_Zp ?prime_gt0 ?pdiv_id //.
  by rewrite -[r]expn1 totient_pfactor ?muln1.
have pq_r: p%:R ^+ q == 1 :> 'F_r.
  rewrite -subr_eq0 -natrX -(@natrB _ _ 1) ?expn_gt0 ?cardG_gt0 // subn1.
  rewrite -(divnK (dvdn_pred_predX p q)) -Fp_nat_mod //.
  by rewrite -modnMml (eqnP r_dv_ustar) mod0n.
have Up_r: (p%:R : 'F_r) \is a GRing.unit.
  by rewrite -(unitrX_pos _ (prime_gt0 pr_q)) (eqP pq_r) unitr1.
congr (_ %| _): (order_dvdG (in_setT (FinRing.unit 'F_r Up_r))).
apply/prime_nt_dvdP=> //; last by rewrite order_dvdn -val_eqE val_unitX.
rewrite -dvdn1 order_dvdn -val_eqE /= -subr_eq0 -val_eqE -(@natrB _ p 1) //=.
rewrite subn1 val_Fp_nat //; apply: contraFN (esym (mem_primes r 1)).
by rewrite pr_r /= -(eqnP co_ustar_p1) dvdn_gcd r_dv_ustar.
Qed.

(* This is Peterfalvi (13.15). *)
Lemma card_FTtypeP_Galois_compl :
  typeP_Galois StypeP -> u = (if p == 1 %[mod q] then ustar %/ q else ustar).
Proof.
case/typeP_Galois_P=> //= _ _ [_ _ /dvdnP[b]]; rewrite Ptype_factor_prime //.
rewrite -/ustar Ptype_Fcompl_kernel_trivial -(card_isog (quotient1_isog _)) -/u.
move=> Dbu; have ub_b: (b <= q.*2)%N.
  have [[lambda Slam irrHlam]| ] := altP (@hasP _ irrIndH calS).
    apply: (FTtypeP_Ind_Fitting_Galois_ub Slam irrHlam).
    by rewrite FTtypeP_reg_Fcore indexg1.
  case/(FTtypeP_no_Ind_Fitting_facts maxS StypeP) => _ /= ->.
  rewrite indexg1 -/ustar -(leq_pmul2r (cardG_gt0 U)) -/u => Du.
  by rewrite -Dbu -Du -(subnKC qgt2) leq_pmull.
have [ustar_odd p1_q p'1_q] := FTtypeP_primes_mod_cases.
have b_odd: odd b by rewrite Dbu odd_mul mFT_odd andbT in ustar_odd.
case: ifPn => [/p1_q q_dv_ustar | /p'1_q[_ _ /(_ b)]].
  have /dvdnP[c Db]: q %| b.
    rewrite Dbu Gauss_dvdl // coprime_sym in q_dv_ustar.
    by apply: coprimeSg coPUq;  have /mulG_sub[_ sUPU] := sdprodW defPU.
  have c_odd: odd c by rewrite Db odd_mul mFT_odd andbT in b_odd.
  suffices /eqP c1: c == 1%N by rewrite Dbu Db c1 mul1n mulKn ?prime_gt0.
  rewrite eqn_leq odd_gt0 // andbT -ltnS -(odd_ltn 3) // ltnS.
  by rewrite -(leq_pmul2r (ltnW (ltnW qgt2))) -Db mul2n.
have Db: b = (b - 1).+1 by rewrite subn1 prednK ?odd_gt0.
rewrite Dbu dvdn_mulr // eqn_mod_dvd Db // -Db => /(_ isT)/dvdnP[c Db1].
have c_even: ~~ odd c by rewrite Db Db1 /= odd_mul mFT_odd andbT in b_odd.
suffices /eqP->: b == 1%N by rewrite mul1n.
have:= ub_b; rewrite Db Db1 -mul2n ltn_pmul2r ?cardG_gt0 //.
by rewrite -ltnS odd_ltn //= !ltnS leqn0 => /eqP->.
Qed.

(* This is Peterfalvi (13.16). *)
(* We have transposed T and Q here so that the lemma does not require         *)
(* assumptions on the associate group.                                        *)
Lemma FTtypeP_norm_cent_compl : P ><| W1 = 'N(W2) /\ P ><| W1 = 'C(W2).
Proof.
have [/mulG_sub[_ sW1S]  /mulG_sub[sPPU sUPU]] := (sdprodW defS, sdprodW defPU).
have nPW1: W1 \subset 'N(P) by rewrite (subset_trans sW1S) ?gFnorm.
have [[_ _ frobUW1 cUU] [abelP _] _ _ _] := Sfacts.
have [pP cPP _] := and3P abelP; have [_ _ cW12 tiW12] := dprodP defW.
have cW2P: P \subset 'C(W2) by rewrite sub_abelian_cent.
suffices sNPW2: 'N(W2) \subset P <*> W1.
  have cW2PW1: P <*> W1 \subset 'C(W2) by rewrite join_subG cW2P centsC.
  rewrite sdprodEY ?coprime_TIg ?(coprimeSg sPPU) //.
  split; apply/eqP; rewrite eqEsubset ?(subset_trans cW2PW1) ?cent_sub //.
  by rewrite (subset_trans (cent_sub _)).
have tiP: normedTI P^# G S.
  have [_ _ _] := compl_of_typeII_IV maxS StypeP notStype5.
  by rewrite -defH FTtypeP_reg_Fcore dprodg1.
have ->: 'N(W2) = 'N_S(W2).
  apply/esym/setIidPr/subsetP=> y nW2y; have [x W2x ntx] := trivgPn _ ntW2.
  have [_ _ tiP_J] := normedTI_memJ_P tiP.
  by rewrite -(tiP_J x) ?inE ?conjg_eq1 // ntx (subsetP sW2P) ?memJ_norm.
rewrite -{1}(sdprodW defS) setIC -group_modr ?cents_norm 1?centsC //=.
rewrite mulG_subG joing_subr /= -(sdprodW defPU) setIC.
rewrite -group_modl ?cents_norm //= mulG_subG joing_subl /= andbT.
set K := 'N_U(W2).
have nPKW1: K <*> W1 \subset 'N(P).
  rewrite (subset_trans _ (gFnorm _ _)) // -(sdprodWY defS) genS ?setSU //.
  by rewrite subIset ?sUPU.
have nW2KW1: K <*> W1 \subset 'N(W2).
  by rewrite join_subG subsetIr cents_norm // centsC.
have coPKW1: coprime #|P| #|K <*> W1|.
  by rewrite (coprimegS _ (Ptype_Fcore_coprime StypeP)) ?genS ?setSU ?subsetIl.
have p'KW1: p^'.-group (K <*> W1).
  by rewrite /pgroup p'natE // -prime_coprime ?(coprimeSg sW2P).
have [Q1 defP nQ1KW1] := Maschke_abelem abelP p'KW1 sW2P nPKW1 nW2KW1.
have [-> | ntK] := eqVneq K 1%g; first by rewrite sub1G.
have frobKW1: [Frobenius K <*> W1 = K ><| W1].
  apply: Frobenius_subl frobUW1; rewrite ?subsetIl //.
  rewrite normsI ?norms_norm //; first by have [_ []] := StypeP.
  by rewrite cents_norm // centsC.
have regQ1W1: 'C_Q1(W1) = 1%g.
  have [_ /mulG_sub[_ /setIidPl defQ1] _ tiW2Q1] := dprodP defP.
  by rewrite -defQ1 -setIA (typeP_cent_core_compl StypeP) setIC.
have cQ1K: K \subset 'C(Q1).
  have /mulG_sub[_ sQ1P] := dprodW defP; have coQ1KW1 := coprimeSg sQ1P coPKW1.
  have solQ1 := solvableS sQ1P (abelian_sol cPP).
  by have [_ ->] := Frobenius_Wielandt_fixpoint frobKW1 nQ1KW1 coQ1KW1 solQ1.
have /subsetIP[_ cW1K]: K \subset 'C_(K <*> W1)(W2).
  have cCW1: W1 \subset 'C_(K <*> W1)(W2) by rewrite subsetI joing_subr centsC.
  apply: contraR ntW1 => /(Frobenius_normal_proper_ker frobKW1) ltCK.
  rewrite -subG1; have [/eqP/sdprodP[_ _ _ <-] _] := andP frobKW1.
  rewrite subsetIidr (subset_trans cCW1) // proper_sub //.
  rewrite ltCK //; last by rewrite norm_normalI ?norms_cent.
  by rewrite (solvableS _ (abelian_sol cUU)) ?subsetIl.
case/negP: ntK; rewrite -subG1 -FTtypeP_reg_Fcore subsetI subsetIl /=.
by rewrite -(dprodW defP) centM subsetI cW1K.
Qed.

End Thirteen_4_10_to_16.

Section Thirteen_17_to_19.

(* These assumptions repeat the part of Peterfalvi, Hypothesis (13.1)  used   *)
(* to prove (13.17-19).                                                       *)

Variables S U W W1 W2 : {group gT}.
Hypotheses (maxS : S \in 'M) (defW : W1 \x W2 = W).
Hypotheses (StypeP : of_typeP S U defW).

Local Notation "` 'W1'" := (gval W1) (at level 0, only parsing) : group_scope.
Local Notation "` 'W2'" := (gval W2) (at level 0, only parsing) : group_scope.
Local Notation "` 'W'" := (gval W) (at level 0, only parsing) : group_scope.
Local Notation V := (cyclicTIset defW).

Local Notation "` 'S'" := (gval S) (at level 0, only parsing) : group_scope.
Local Notation P := `S`_\F%G.
Local Notation "` 'P'" := `S`_\F (at level 0) : group_scope.
Local Notation PU := S^`(1)%G.
Local Notation "` 'PU'" := `S^`(1) (at level 0) : group_scope.
Local Notation "` 'U'" := (gval U) (at level 0, only parsing) : group_scope.

Let defS : PU ><| W1 = S. Proof. by have [[]] := StypeP. Qed.
Let defPU : P ><| U = PU. Proof. by have [_ []] := StypeP. Qed.

Let notStype1 : FTtype S != 1%N. Proof. exact: FTtypeP_neq1 StypeP. Qed.
Let notStype5 : FTtype S != 5%N. Proof. exact: FTtype5_exclusion maxS. Qed.

Let pddS := FT_prDade_hypF maxS StypeP.
Let ptiWS : primeTI_hypothesis S PU defW := FT_primeTI_hyp StypeP.
Let ctiWG : cyclicTI_hypothesis G defW := pddS.
Local Notation Sfacts := (FTtypeP_facts maxS StypeP).

Let ntW1 : W1 :!=: 1. Proof. by have [[]] := StypeP. Qed.
Let ntW2 : W2 :!=: 1. Proof. by have [_ _ _ []] := StypeP. Qed.
Let cycW1 : cyclic W1. Proof. by have [[]] := StypeP. Qed.
Let cycW2 : cyclic W2. Proof. by have [_ _ _ []] := StypeP. Qed.

Let p := #|W2|.
Let q := #|W1|.

Let pr_p : prime p. Proof. by have [] := FTtypeP_primes maxS StypeP. Qed.
Let pr_q : prime q. Proof. by have [] := FTtypeP_primes maxS StypeP. Qed.

Let qgt2 : q > 2. Proof. by rewrite odd_gt2 ?mFT_odd ?cardG_gt1. Qed.
Let pgt2 : p > 2. Proof. by rewrite odd_gt2 ?mFT_odd ?cardG_gt1. Qed.

Let coPUq : coprime #|PU| q.
Proof. by rewrite (coprime_sdprod_Hall_r defS); have [[]] := StypeP. Qed.

Let sW2P: W2 \subset P. Proof. by have [_ _ _ []] := StypeP. Qed.

Let p'q : q != p.
Proof.
by rewrite -dvdn_prime2 -?prime_coprime -?(cyclic_dprod defW) //; case: ctiWG.
Qed.

Let nirrW1 : #|Iirr W1| = q. Proof. by rewrite card_Iirr_cyclic. Qed.
Let nirrW2 : #|Iirr W2| = p. Proof. by rewrite card_Iirr_cyclic. Qed.
Let NirrW1 : Nirr W1 = q. Proof. by rewrite -nirrW1 card_ord. Qed.
Let NirrW2 : Nirr W2 = p. Proof. by rewrite -nirrW2 card_ord. Qed.

Local Open Scope ring_scope.

Let sigma := (cyclicTIiso ctiWG).
Let w_ i j := (cyclicTIirr defW i j).
Local Notation eta_ i j := (sigma (w_ i j)).

Let mu_ := primeTIred ptiWS.
Local Notation tau := (FT_Dade0 maxS).

Let calS0 := seqIndD PU S S`_\s 1.
Let rmR := FTtypeP_coh_base maxS StypeP.
Let scohS0 : subcoherent calS0 tau rmR.
Proof. exact: FTtypeP_subcoherent StypeP. Qed.

Let calS := seqIndD PU S P 1.
Let sSS0 : cfConjC_subset calS calS0.
Proof. exact/seqInd_conjC_subset1/Fcore_sub_FTcore. Qed.

(* This is Peterfalvi (13.17). *)
Lemma FTtypeII_support_facts T L (Q := T`_\F) (H := L`_\F) :
    FTtype S == 2 -> typeP_pair S T defW -> L \in 'M('N(U)) ->
  [/\ (*a*) [Frobenius L with kernel H],
      (*b*) U \subset H
    & (*c*) H ><| W1 = L \/ (exists2 y, y \in Q & H ><| (W1 <*> W2 :^ y) = L)].
Proof.
move=> Stype2 pairST /setIdP[maxL sNU_L].
have [pgt0 qgt0] := (ltnW (ltnW pgt2), ltnW (ltnW qgt2)).
have [[_ _ maxT] _ _ _ allST] := pairST.
have [[_ ntU _ _] _ not_sNU_S _ _] := compl_of_typeII maxS StypeP Stype2.
have [[_ _ frobUW1 cUU] _ _ _ _] := Sfacts.
have xdefW: W2 \x W1 = W by rewrite dprodC.
have [V TtypeP] := typeP_pairW (typeP_pair_sym xdefW pairST).
have [abelQ oQ]: q.-abelem Q /\ #|Q| = (q ^ p)%N.
  by have [] := FTtypeP_facts maxT TtypeP.
have sUL: U \subset L := subset_trans (normG U) sNU_L.
have [/mulG_sub[sPPU sUPU] sPUS] := (sdprodW defPU, der_sub 1 S).
have nUW1: W1 \subset 'N(U) by have [_ []] := StypeP.
have sW1L := subset_trans nUW1 sNU_L.
have Ltype1: FTtype L == 1%N.
  apply: contraR not_sNU_S => /allST/setUP[]// /imsetP[y _ defL].
    have hallU: \pi(U).-Hall(S) U.
      have /Hall_pi/(subHall_Hall _ (piSg sUPU)): Hall PU U.
        have /pHall_Hall:= pHall_subl sPPU sPUS (Fcore_Hall S).
        by rewrite (sdprod_Hall defPU).
      by apply; rewrite Hall_pi // -(coprime_sdprod_Hall_l defS).
    have hallUy: \pi(U).-Hall(S) (U :^ y^-1).
      by rewrite pHallE sub_conjgV -defL sUL /= cardJg -(card_Hall hallU).
    have [x /conjGid <- ->] := Hall_trans (mmax_sol maxS) hallU hallUy.
    by rewrite !normJ conjSg sub_conjgV -defL.
  have oH: #|H| = (q ^ p)%N by rewrite /H defL FcoreJ cardJg.
  have sW1H: W1 \subset H.
    rewrite (sub_normal_Hall (Fcore_Hall L)) ?gFnormal //=.
    by rewrite oH pi_of_exp ?prime_gt0 // pgroup_pi.
  have regUW1: 'C_U(W1) = 1%g := Frobenius_trivg_cent frobUW1.
  have /negP[] := ntU; rewrite -subG1 -regUW1 subsetIidl (sameP commG1P trivgP).
  have /coprime_TIg <-: coprime #|U| #|H|.
    by rewrite oH coprime_pexpr ?(coprimeSg sUPU).
  rewrite commg_subI //; last by rewrite subsetI sW1H.
  by rewrite subsetIidl (subset_trans sUL) ?gFnorm.
have frobL := FTtype1_Frobenius maxL Ltype1.
have solH: solvable H by rewrite nilpotent_sol ?Fcore_nil.
have coHW1: coprime #|H| #|W1|.
  rewrite -(coprime_pexpr _ _ pgt0) -oQ.
  apply/(coprimegS (Fcore_sub_FTcore maxT))/(coprimeSg (Fcore_sub_FTcore maxL)).
  have [_ -> //] := FT_Dade_support_partition gT.
  have: FTtype T != 1%N := FTtypeP_neq1 maxT TtypeP.
  by apply: contra => /imsetP[y _ ->] /=; rewrite FTtypeJ.
have tiHW1: H :&: W1 = 1%g := coprime_TIg coHW1.
have sUH: U \subset H; last split=> //.
  have [ntH _ /andP[sHL nHL] regHL] := Frobenius_kerP frobL.
  have regHE E: gval E != 1%g -> E \subset L -> H :&: E = 1%g -> 'C_H(E) = 1%g.
    move=> ntE sEL tiHE; apply: contraNeq ntE => /trivgPn[x /setIP[Hx cEx] ntx].
    rewrite -subG1 -tiHE subsetIidr (subset_trans _ (regHL x _)) ?inE ?ntx //.
    by rewrite subsetI sEL sub_cent1.
  suffices /trivgPn[x /setIP[Hx Ux] ntx]: H :&: U != 1%g.
    apply: subset_trans (regHL x _); last by rewrite !inE ntx.
    by rewrite subsetI sUL sub_cent1 (subsetP cUU).
  apply: contraNneq (ntH) => tiHU; rewrite trivg_card1.
  have [nHU nHW1] := (subset_trans sUL nHL, subset_trans sW1L nHL).
  have nHUW1: U <*> W1 \subset 'N(H) by rewrite join_subG nHU.
  have coHUW1: coprime #|H| #|U <*> W1|.
    have [/eqP defUW1 _] := andP frobUW1.
    rewrite (sdprodWY defUW1) -(sdprod_card defUW1) coprime_mulr coHW1 andbT.
    have defHU: H ><| U = H <*> U by rewrite sdprodEY.
    rewrite (coprime_sdprod_Hall_l defHU).
    apply: pHall_Hall (pHall_subl (joing_subl _ _) _ (Fcore_Hall L)).
    by rewrite join_subG sHL.
  have [_ _] := Frobenius_Wielandt_fixpoint frobUW1 nHUW1 coHUW1 solH.
  by move->; rewrite regHE // cards1 exp1n.
have [E sW1E frobHE]: exists2 E, W1 \subset gval E & [Frobenius L = H ><| E].
  have [E frobHE] := existsP frobL; have [/eqP defL _] := andP frobHE.
  have hallE: \pi(H)^'.-Hall(L) E.
    by rewrite -(compl_pHall E (Fcore_Hall L)) sdprod_compl.
  have [|x Lx sW1Ex] := Hall_subJ (mmax_sol maxL) hallE sW1L.
    by rewrite /pgroup -coprime_pi' ?cardG_gt0.
  rewrite -(FrobeniusJ x) conjGid // (normsP (gFnorm _ _)) // in frobHE.
  by exists (E :^ x)%G.
have [defL ntH ntE _ _] := Frobenius_context frobHE.
have [_ sEL _ nHE _] := sdprod_context defL.
have solE := solvableS sEL (mmax_sol maxL).
have [regHE regEH] := (Frobenius_reg_ker frobHE, Frobenius_reg_compl frobHE).
have qW1: q.-group W1 by apply: pnat_id.
have cycEr (r : nat) R: r.-group R -> R \subset E -> cyclic R.
  move=> rR sRE; have nHR := subset_trans sRE nHE.
  apply: odd_regular_pgroup_cyclic rR (mFT_odd _) ntH nHR _.
  by move=> y /setD1P[nty Ry]; rewrite regHE // !inE nty (subsetP sRE).
have /normal_norm nW1E: W1 <| E.
  exact: prime_odd_regular_normal (mFT_odd E) _ _ _ (Frobenius_reg_ker frobHE).
have defNW1: Q ><| W2 = 'N(W1).
  by have [] := FTtypeP_norm_cent_compl maxT TtypeP.
have [nsQN sW2N _ _ _] := sdprod_context defNW1.
have sylQ: q.-Sylow('N(W1)) Q.
  rewrite /pHall normal_sub // abelem_pgroup //=.
  by rewrite -(index_sdprod defNW1) pnatE //= !inE eq_sym.
have hallW2: q^'.-Hall('N(W1)) W2 by rewrite -(compl_pHall _ sylQ) sdprod_compl.
pose Q1 := Q :&: E; have sylQ1: q.-Sylow(E) Q1 by apply: setI_normal_Hall nW1E.
have defQ1: Q1 = W1.
  have abelQ1: q.-abelem Q1 := abelemS (subsetIl Q E) abelQ.
  have sW1Q: W1 \subset Q by have [_ _ _ []] := TtypeP.
  have sW1Q1: W1 \subset Q1 by apply/subsetIP.
  have ntQ1: Q1 != 1%g by apply: subG1_contra ntW1.
  apply/esym/eqP; rewrite eqEcard sW1Q1 (cyclic_abelem_prime abelQ1) //=.
  by rewrite (cycEr q) ?(pHall_pgroup sylQ1) ?subsetIr.
have [P2 hallP2] := Hall_exists q^' solE; have [sP2E q'P2 _] := and3P hallP2.
have defE: W1 ><| P2 = E.
  apply/(sdprod_normal_p'HallP _ hallP2); rewrite /= -defQ1 //.
  by rewrite /Q1 setIC norm_normalI // (subset_trans nW1E) ?normal_norm.
have [P2_1 | ntP2] := eqsVneq P2 1%g.
  by left; rewrite -defE P2_1 sdprodg1 in defL.
have solNW1: solvable 'N(W1).
  by rewrite mFT_sol ?mFT_norm_proper // mFT_sol_proper (solvableS sW1E).
have [zy /=] := Hall_subJ solNW1 hallW2 (subset_trans sP2E nW1E) q'P2.
rewrite -{1}(sdprodWC defNW1) => /mulsgP[z y W2z Qy ->{zy}].
rewrite conjsgM (conjGid W2z) {z W2z} => sP2W2y.
right; exists y => //; congr (_ ><| _ = _): defL.
rewrite -(sdprodWY defE); congr (W1 <*> _).
by apply/eqP; rewrite eqEsubset sP2W2y prime_meetG ?cardJg ?(setIidPr _).
Qed.

Local Notation Imu2 := (primeTI_Iirr ptiWS).
Local Notation mu2_ i j := (primeTIirr ptiWS i j).

Definition FTtypeP_bridge j := 'Ind[S, P <*> W1] 1 - mu2_ 0 j.
Local Notation beta_ := FTtypeP_bridge.
Definition FTtypeP_bridge_gap := tau (beta_ #1) - 1 + eta_ 0 #1.
Local Notation Gamma := FTtypeP_bridge_gap.

Let u := #|U|.

(* This is Peterfalvi (13.18). *)
(* Part (d) is stated with a slightly weaker hypothesis that fits better with *)
(* the usage pattern in (13.19) and (14.9).                                   *)
Lemma FTtypeP_bridge_facts (V_S := class_support (cyclicTIset defW) S) :
  [/\ (*a*) [/\ forall j, j != 0 -> beta_ j \in 'CF(S, 'A0(S))
              & forall j, j != 0 -> beta_ j \in 'CF(S, P^# :|: V_S)],
      (*b*) forall j, j != 0 -> '[beta_ j] = (u.-1 %/ q + 2)%:R,
      (*c*) [/\ forall j, j != 0 -> tau (beta_ j) - 1 + eta_ 0 j = Gamma,
                '[Gamma, 1] = 0 & cfReal Gamma],
      (*d*) forall X Y : 'CF(G),
              Gamma = X + Y -> '[X, Y] = 0 ->
              orthogonal Y (map sigma (irr W)) ->
            '[Y] <= (u.-1 %/ q)%:R
          & q %| u.-1].
Proof.
have [_ sW1S _ nPUW1 tiPUW1] := sdprod_context defS.
have /mulG_sub[sPPU sUPU] := sdprodW defPU.
have sPW1S: P <*> W1 \subset S by rewrite join_subG gFsub.
have /= defS_P := Ptype_Fcore_sdprod StypeP; have nsPS: P <| S := gFnormal _ _.
have defPW1: P ><| W1 = P <*> W1 := sdprod_subr defS_P (joing_subr U W1).
pose W1bar := (W1 / P)%g; pose Sbar := (S / P)%g; pose Ubar := (U / P)%g.
pose gamma := 'Ind[Sbar, W1bar] 1.
have Dgamma: 'Ind[S, P <*> W1] 1 = (gamma %% P)%CF.
  rewrite -(rmorph1 _ : 1 %% P = 1)%CF cfIndMod ?joing_subl //.
  by rewrite quotientYidl //; have [] := sdprodP defPW1.
have gamma1: gamma 1%g = u%:R.
  rewrite -cfMod1 -Dgamma cfInd1 // cfun11 -divgS // -(sdprod_card defPW1).
  by rewrite mulr1 -(sdprod_card defS) -(sdprod_card defPU) divnMr // mulKn. 
have frobUW1: [Frobenius U <*> W1 = U ><| W1] by have [[]] := Sfacts.
have q_dv_u1: q %| u.-1 := Frobenius_dvd_ker1 frobUW1.
have [nP_UW1 /isomP[/=]] := sdprod_isom defS_P; set h := restrm _ _ => injh hS.
have /joing_sub[sUUW1 sW1UW1] := erefl (U <*> W1).
have [hU hW1]: h @* U = Ubar /\ h @* W1 = W1bar.
  by rewrite !morphim_restrm /= !(setIidPr _).
have{hS} frobSbar: [Frobenius Sbar = Ubar ><| W1bar].
  by rewrite -[Sbar]hS -hU -hW1 injm_Frobenius.
have tiW1bar: normedTI W1bar^# Sbar W1bar by have /and3P[] := frobSbar.
have gammaW1 xbar: xbar \in W1bar^# -> gamma xbar = 1.
  move=> W1xbar; have [ntxbar _] := setD1P W1xbar.
  rewrite cfIndE ?quotientS //; apply: canLR (mulKf (neq0CG _)) _.
  have ->: #|W1bar| = #|Sbar :&: W1bar| by rewrite (setIidPr _) ?quotientS.
  rewrite mulr1 cardsE -sumr_const big_mkcondr; apply: eq_bigr => zbar Szbar.
  have [_ _ W1bar_xJ] := normedTI_memJ_P tiW1bar.
  by rewrite -mulrb -(W1bar_xJ xbar) // !inE conjg_eq1 ntxbar cfun1E.
have PVSbeta j: j != 0 -> beta_ j \in 'CF(S, P^# :|: V_S).
  move=> nzj; apply/cfun_onP=> z; rewrite !inE => /norP[P'z VS'z].
  have [Sz | /cfun0->//] := boolP (z \in S); apply/eqP; rewrite !cfunE subr_eq0.
  have [[_ mulW12 _ tiW12] C1] := (dprodP defW, FTtypeP_reg_Fcore maxS StypeP).
  have [PUz {VS'z} | PU'z {P'z}] := boolP (z \in PU).
    rewrite eq_sym -(cfResE _ _ PUz) ?gFsub // -['Res _](scalerK (neq0CG W1)).
    rewrite cfRes_prTIirr -cfRes_prTIred -/q cfunE cfResE ?gFsub // mulrC.
    case/nandP: P'z => [/negbNE/eqP-> | P'z].
      rewrite Dgamma cfModE // morph1 gamma1 FTprTIred1 // C1 indexg1.
      by rewrite natrM mulfK ?neq0CG.
    have:= seqInd_on (Fitting_normal S) (FTprTIred_Ind_Fitting maxS StypeP nzj).
    have [/= <- _ _ _] := typeP_context StypeP; rewrite C1 dprodg1 -/(mu_ j).
    move/cfun_on0->; rewrite // mul0r (cfun_on0 (cfInd_on _ (cfun_onG _))) //.
    rewrite -(sdprodW defPW1); apply: contra P'z => /imset2P[x t PW1x St Dz].
    rewrite Dz !memJ_norm ?(subsetP (gFnorm _ _)) // in PUz *.
    by rewrite -(mulg1 P) -tiPUW1 setIC group_modl // inE PW1x.
  have /imset2P[x t /setD1P[ntx W1x] St ->]: z \in class_support W1^# S.
    have /bigcupP[_ /rcosetsP[x W1x ->]]: z \in cover (rcosets PU W1).
      by rewrite (cover_partition (rcosets_partition_mul _ _)) (sdprodW defS).
    have [-> | ntx] := eqVneq x 1%g; first by rewrite mulg1 => /idPn[].
    have nPUx: x \in 'N(PU) by rewrite (subsetP nPUW1).
    have coPUx: coprime #|PU| #[x] by rewrite (coprime_dvdr (order_dvdG W1x)).
    have [/cover_partition <- _] := partition_cent_rcoset nPUx coPUx.
    have [_ _ _ [_ _ _ _ prPUW1] _] := StypeP; rewrite {}prPUW1 ?inE ?ntx //.
    rewrite cover_imset => /bigcupP[t PUt /imsetP[_ /rcosetP[y W2y ->] Dz]].
    have{PUt} St: t \in S by rewrite (subsetP _ _ PUt) ?der_sub.
    have [y1 | nty] := eqVneq y 1%g.
      by rewrite Dz y1 mul1g memJ_class_support // !inE ntx.
    rewrite Dz memJ_class_support // !inE groupMr // groupMl // in VS'z.
    rewrite -(dprodWC defW) mem_mulg // andbT; apply/norP.
    by rewrite -!in_set1 -set1gE -tiW12 !inE W1x W2y andbT in ntx nty.
  rewrite !cfunJ // Dgamma cfModE ?(subsetP sW1S) // gammaW1; last first.
    by rewrite !inE (morph_injm_eq1 injh) ?(subsetP sW1UW1) ?ntx ?mem_quotient.
  rewrite prTIirr_id ?FTprTIsign // ?scale1r ?dprod_IirrEr; last first.
    rewrite -in_set1 -set1gE -tiW12 inE W1x /= in ntx.
    by rewrite inE ntx -mulW12 (subsetP (mulG_subl W2 W1)).
  by rewrite -[x]mulg1 cfDprodEr ?lin_char1 ?irr_prime_lin.
have A0beta j: j != 0 -> beta_ j \in 'CF(S, 'A0(S)).
  move/PVSbeta; apply: cfun_onS; rewrite (FTtypeP_supp0_def _ StypeP) //.
  by rewrite setSU ?(subset_trans _ (FTsupp1_sub _)) ?setSD ?Fcore_sub_FTcore.
have norm_beta j: j != 0 -> '[beta_ j] = (u.-1 %/ q + 2)%:R.
  move=> nzj; rewrite cfnormBd ?Dgamma; last first.
    apply: contraNeq (cfker_prTIres pddS nzj); rewrite -irr_consttE => S1_mu0j.
    rewrite -(cfRes_prTIirr _ 0) sub_cfker_Res //.
    rewrite (subset_trans _ (cfker_constt _ S1_mu0j)) ?cfker_mod //.
    by rewrite -Dgamma cfInd_char ?rpred1.
  have [[/eqP defUW1 _] [/eqP defSbar _]] := (andP frobUW1, andP frobSbar).
  rewrite cfnorm_irr cfMod_iso //.
  rewrite (cfnormE (cfInd_on _ (cfun_onG _))) ?quotientS // -/gamma.
  rewrite card_quotient ?gFnorm // -(index_sdprod defS_P) -(sdprod_card defUW1).
  rewrite -/u -/q (big_setD1 1%g) ?mem_class_support ?group1 //=.
  have{tiW1bar} [_ tiW1bar /eqP defNW1bar] := and3P tiW1bar.
  rewrite gamma1 normr_nat class_supportD1 big_trivIset //=.
  rewrite (eq_bigr (fun xbar => #|W1bar|.-1%:R)) ?sumr_const; last first.
    rewrite (cardsD1 1%g) group1 /= => _ /imsetP[tbar Stbar ->].
    rewrite -sumr_const big_imset /=; last exact: in2W (conjg_inj tbar).
    by apply: eq_bigr => xbar W1xbar; rewrite cfunJ ?gammaW1 // normr1 expr1n.
  rewrite card_conjugates -divgS ?subsetIl //= -(sdprod_card defSbar) defNW1bar.
  rewrite mulnK ?cardG_gt0 // -hU -hW1 ?card_injm // -/q -/u natrM invfM mulrC.
  rewrite -[rhs in _ ^+ 2 + rhs]mulr_natr -mulrDl mulrA mulfK ?neq0CG //.
  rewrite -subn1 natrB ?cardG_gt0 // addrCA mulrDl divff ?neq0CG //.
  by rewrite -natrB ?cardG_gt0 // subn1 -natf_div // addrAC addrC natrD.
have nzj1: #1 != 0 :> Iirr W2 by apply: Iirr1_neq0.
have [_ _ _ _ [_ Dtau]] := Sfacts; pose eta01 := eta_ 0 #1.
have oeta01_1: '[eta01, 1] = 0.
  by rewrite -(cycTIiso1 ctiWG) -(cycTIirr00 defW) cfdot_cycTIiso (negPf nzj1).
have Deta01s: eta01^*%CF = eta_ 0 (conjC_Iirr #1).
  by rewrite cfAut_cycTIiso /w_ !dprod_IirrEr cfAutDprodr aut_IirrE.
have oGamma1: '[Gamma, 1] = 0.
  rewrite cfdotDl cfdotBl cfnorm1 oeta01_1 addr0 Dtau ?A0beta //.
  rewrite -cfdot_Res_r rmorph1 cfdotBl -cfdot_Res_r rmorph1 cfnorm1.
  by rewrite -(prTIirr00 ptiWS) cfdot_prTIirr (negPf nzj1) subr0 subrr.
have defGamma j: j != 0 -> tau (beta_ j) - 1 + eta_ 0 j = Gamma.
  move=> nzj; apply/eqP; rewrite -subr_eq0 opprD addrACA opprB !addrA subrK.
  rewrite -linearB opprD addrACA subrr add0r -opprD linearN /=.
  move/prDade_sub_TIirr: pddS => -> //; last first.
    by apply: (mulfI (neq0CG W1)); rewrite -!prTIred_1 !FTprTIred1.
  by rewrite -/sigma FTprTIsign // scale1r -addrA addNr.
have GammaReal: cfReal Gamma.
  rewrite /cfReal rmorphD rmorphB rmorph1 /= Deta01s Dtau ?A0beta // cfAutInd.
  rewrite rmorphB /= cfAutInd rmorph1 -prTIirr_aut aut_Iirr0 -/(beta_ _).
  by rewrite -Dtau ?A0beta ?defGamma ?aut_Iirr_eq0.
split=> // X Y defXY oXY oYeta; pose a := '[Gamma, eta01].
have Za: a \in Cint.
  rewrite Cint_cfdot_vchar ?(rpredB, rpredD, rpred1, cycTIiso_vchar) //.
  by rewrite Dtau ?A0beta // !(cfInd_vchar, rpredB) ?rpred1 ?irr_vchar.
have{oYeta} oYeta j: '[Y, eta_ 0 j] = 0.
  by rewrite (orthoPl oYeta) ?map_f ?mem_irr.
have o_eta1s1: '[eta01^*, eta01] = 0.
  rewrite Deta01s cfdot_cycTIiso /= -(inj_eq irr_inj) aut_IirrE.
  by rewrite odd_eq_conj_irr1 ?mFT_odd // irr_eq1 (negPf nzj1).
rewrite -(ler_add2r 2%:R) -natrD -(norm_beta #1) //.
have ->: '[beta_ #1] = '[Gamma - eta01 + 1].
  by rewrite addrK subrK Dade_isometry ?A0beta.
rewrite addrA cfnormDd ?cfnorm1 ?ler_add2r; last first.
  by rewrite cfdotBl oeta01_1 oGamma1 subrr.
rewrite defXY addrAC addrC cfnormDd ?ler_add2r; last first.
  by rewrite cfdotBl oXY cfdotC oYeta conjC0 subrr.
have oXeta j: '[X, eta_ 0 j] = '[Gamma, eta_ 0 j].
  by rewrite defXY cfdotDl oYeta addr0.
pose X1 := X - a *: eta01 - a *: eta01^*%CF.
have ->: X - eta01 = X1 + a *: eta01^*%CF + (a - 1) *: eta01.
  by rewrite scalerBl scale1r addrA !subrK.
rewrite cfnormDd; last first.
  rewrite cfdotZr subrK cfdotBl oXeta -/a cfdotZl cfnorm_cycTIiso mulr1.
  by rewrite subrr mulr0.
rewrite cfnormDd; last first.
  rewrite cfdotZr !cfdotBl !cfdotZl Deta01s cfnorm_cycTIiso oXeta -Deta01s.
  rewrite !cfdot_conjCr o_eta1s1 conjC0 mulr0 ((_ =P Gamma) GammaReal) -/a.
  by rewrite conj_Cint // mulr1 subr0 subrr mulr0.
rewrite -addrA ler_paddl ?cfnorm_ge0 // !cfnormZ Deta01s !cfnorm_cycTIiso.
rewrite !mulr1 !Cint_normK ?rpredB ?rpred1 // sqrrB1 !addrA -mulr2n.
by rewrite -subr_ge0 addrK subr_ge0 ler_pmuln2r ?Cint_ler_sqr.
Qed.

(* The assumptions of Peterfalvi (13.19). *)
(* We do not need to put these in a subsection as this is the last Lemma.    *)
Variable L : {group gT}.
Hypotheses (maxL : L \in 'M) (Ltype1 : FTtype L == 1%N).

Local Notation "` 'L'" := (gval L) (at level 0, only parsing) : group_scope.
Local Notation H := `L`_\F%G.
Local Notation "` 'H'" := `L`_\F (at level 0) : group_scope.

Let e :=  #|L : H|.
Let tauL := FT_DadeF maxL.
Let calL := seqIndD H L H 1.

Let frobL : [Frobenius L with kernel H]. Proof. exact: FTtype1_Frobenius. Qed.

(* The coherence part of the preamble of (13.19). *)
Lemma FTtype1_coherence : coherent calL L^# tauL.
Proof.
have [_ [tau1 [IZtau1 Dtau1]]] := FT_Frobenius_coherence maxL frobL.
exists tau1; split=> // phi Sphi; rewrite ?Dtau1 //.
move/(zcharD1_seqInd_on (Fcore_normal _)) in Sphi.
by rewrite /tauL FT_DadeF_E ?FT_DadeE ?(cfun_onS (Fcore_sub_FTsupp _)).
Qed.

Lemma FTtype1_Ind_irr : {subset calL <= irr L}.
Proof. by case: (FT_Frobenius_coherence maxL frobL). Qed.
Let irrL := FTtype1_Ind_irr.

(* We re-quantify over the witnesses so that the main part of the lemma can   *)
(* be used for Section variables in the very last part of Section 14.         *)
Variables (tau1 : {additive 'CF(L) -> 'CF(G)}) (phi : 'CF(L)).
Hypothesis cohL : coherent_with calL L^# tauL tau1.
Hypotheses (Lphi : phi \in calL) (phi1e : phi 1%g = e%:R).

Let betaL := 'Ind[L, H] 1 - phi.
Let betaS := beta_ #1.
Let eta01 := eta_ 0 #1.

(* This is Peterfalvi (13.19). *)
Lemma FTtypeI_bridge_facts :
  [/\ (*a*) 'A~(L) :&: (class_support P G :|: class_support W G) = set0,
      (*b*) orthogonal (map tau1 calL) (map sigma (irr W)),
      (*c*) forall j, j != 0 -> '[tauL betaL, eta_ 0 j] = '[tauL betaL, eta01]
       & (*c1*) ('[tau betaS, tau1 phi] == 1 %[mod 2])%C
                /\ #|H|.-1%:R / e%:R <= (u.-1 %/ q)%:R :> algC
      \/ (*c2*) ('[tauL betaL, eta01] == 1 %[mod 2])%C /\ (p <= e)%N].
Proof.
have nsHL: H <| L := gFnormal _ L; have [sHL nHL] := andP nsHL.
have coHr T r: T \in 'M -> FTtype T != 1%N -> r.-abelem T`_\F -> coprime #|H| r.
  move=> maxT notTtype1 /andP[rR _].
  have [_ _ [n oR]] := pgroup_pdiv rR (mmax_Fcore_neq1 maxT).
  rewrite -(coprime_pexpr _ r (ltn0Sn n)) -oR /= -FTcore_type1 //.
  apply: coprimegS (Fcore_sub_FTcore maxT) _.
  have [_ -> //] := FT_Dade_support_partition gT.
  by apply: contra notTtype1 => /imsetP[y _ ->] /=; rewrite FTtypeJ.
have coHp: coprime #|H| p by apply: (coHr S) => //; have [_ []] := Sfacts.
have{coHr} coHq: coprime #|H| q.
  have [T pairST [xdefW [V TtypeP]]] := FTtypeP_pair_witness maxS StypeP.
  have [[_ _ maxT] _ _ _ _] := pairST; have Ttype'1 := FTtypeP_neq1 maxT TtypeP.
  by rewrite (coHr T) ?Ttype'1 //; have [_ []] := FTtypeP_facts maxT TtypeP.
have defA: 'A(L) = H^# := FTsupp_Frobenius maxL frobL.
set PWG := class_support P G :|: class_support W G.
have tiA_PWG: 'A~(L) :&: PWG = set0.
  apply/setP=> x; rewrite !inE; apply/andP=> [[Ax PWGx]].
  suffices{Ax}: \pi(H)^'.-elt x.
    have [y Ay /imset2P[_ t /rcosetP[z Rz ->] _ ->]] := bigcupP Ax => H'zyt.
    do [rewrite -def_FTsignalizer //; set ddL := FT_Dade_hyp maxL] in Rz.
    have /setD1P[nty Hy]: y \in H^# by rewrite -defA.
    have /idPn[]: (z * y).`_\pi('C_H[y]) == 1%g.
      rewrite (constt1P _) // -(p_eltJ _ _ t); apply: sub_in_pnat H'zyt => r _.
      by apply: contra; apply: piSg; apply: subsetIl.
    rewrite consttM; last first.
      exact: cent1P (subsetP (Dade_signalizer_cent _ y) z Rz).
    rewrite (constt1P (mem_p_elt _ Rz)) ?mul1g; last first.
      rewrite /pgroup -coprime_pi' ?cardG_gt0 // coprime_sym.
      by rewrite (coprimegS _ (Dade_coprime _ Ay Ay)) ?setSI.
    by rewrite (constt_p_elt (mem_p_elt (pgroup_pi _) _)) // inE Hy cent1id.
  suffices /pnat_dvd: #[x] %| #|P| * #|W|.
    have [_ [_ ->] _ _ _] := Sfacts; rewrite -(dprod_card defW) -/p -/q.
    by apply; rewrite !pnat_mul pnat_exp -!coprime_pi' ?cardG_gt0 ?coHp ?coHq.
  case/orP: PWGx => /imset2P[y z PWy _ ->]; rewrite {z}orderJ.
    by rewrite dvdn_mulr ?order_dvdG.
  by rewrite dvdn_mull ?order_dvdG.
have ZsubL psi: psi \in calL -> psi - psi^*%CF \in 'Z[calL, L^#].
  have ZcalL: {subset calL <= 'Z[irr L]} by apply: seqInd_vcharW.
  by move=> Lpsi; rewrite sub_aut_zchar ?zchar_onG ?mem_zchar ?cfAut_seqInd.
have mem_eta j: eta_ 0 j \in map sigma (irr W) by rewrite map_f ?mem_irr.
have otau1eta: orthogonal (map tau1 calL) (map sigma (irr W)).
  apply/orthogonalP=> _ _ /mapP[psi Lpsi ->] /mapP[w irr_w ->].
  have{w irr_w} [i [j ->]] := cycTIirrP defW irr_w; rewrite -/(w_ i j). 
  pose Psi := tau1 (psi - psi^*%CF); pose NC := cyclicTI_NC ctiWG.
  have [[Itau1 Ztau1] Dtau1] := cohL.
  have Lpsis: psi^*%CF \in calL by rewrite cfAut_seqInd.
  have Z1dpsi := ZsubL _ Lpsi; have Zdpsi := zcharW Z1dpsi.
  have{Dtau1} PsiV0: {in V, Psi =1 \0}.
    move=> x /setDP[Wx _]; rewrite /Psi Dtau1 ?(cfun_on0 (Dade_cfunS _ _)) //.
    rewrite FT_DadeF_supportE -defA; apply: contra_eqN tiA_PWG => Ax.
    by apply/set0Pn; exists x; rewrite !inE Ax orbC mem_class_support.
  have opsi: '[psi, psi^*] = 0 by apply: seqInd_conjC_ortho (mFT_odd _) _ Lpsi.
  have n2Psi: '[Psi] = 2%:R.
    by rewrite Itau1 ?cfnormBd // cfnorm_conjC ?irrWnorm ?irrL.
  have NC_Psi: (NC Psi < minn q p)%N.
    by rewrite (@leq_ltn_trans 2) ?leq_min ?qgt2 // cycTI_NC_norm ?Ztau1 ?n2Psi.
  apply: contraTeq (NC_Psi) => t1psi_eta; rewrite -leqNgt cycTI_NC_minn //.
  rewrite mul2n -addnn (leq_trans NC_Psi) ?leq_addl // andbT card_gt0.
  suffices [b Deta]: exists b : bool, eta_ i j = (-1) ^+ b *: tau1 psi.
    apply/set0Pn; exists (i, j); rewrite !inE /= /Psi raddfB cfdotBl {2}Deta.
    by rewrite cfdotZr Itau1 ?mem_zchar // cfdot_conjCl opsi conjC0 mulr0 subr0.
  exists (tau1 psi == - eta_ i j); apply: (canRL (signrZK _)).
  move/eqP: t1psi_eta; rewrite cfdot_dirr ?cycTIiso_dirr //; last first.
    by rewrite dirrE Itau1 ?Ztau1 ?mem_zchar //= irrWnorm ?irrL.
  by rewrite scaler_sign; do 2!case: eqP => //.
have [[A0beta PVbeta] n2beta [defGa Ga1 R_Ga] ubGa dvu] := FTtypeP_bridge_facts.
have [_ _ _ _ [_ Dtau]] := Sfacts.
have o_tauL_S zeta j: j != 0 -> '[tauL zeta, tau (beta_ j)] = 0.
  move=> nzj; pose ABS := class_support (P^# :|: class_support V S) G.
  have ABSbeta: tau (beta_ j) \in 'CF(G, ABS).
    by rewrite Dtau ?A0beta // cfInd_on ?subsetT ?PVbeta.
  have{ABSbeta} PWGbeta: tau (beta_ j) \in 'CF(G, PWG).
    apply: cfun_onS ABSbeta; apply/subsetP=> _ /imset2P[x t PVSx _ ->].
    case/setUP: PVSx => [/setD1P[_ Px] | /imset2P[y z /setDP[Wy _] _ ->]].
      by rewrite inE memJ_class_support ?inE.
    by rewrite -conjgM inE orbC memJ_class_support ?inE.
  rewrite (cfdotElr (Dade_cfunS _ _) PWGbeta) big_pred0 ?mulr0 // => x.
  by rewrite FT_DadeF_supportE -defA tiA_PWG inE.
have betaLeta j: j != 0 -> '[tauL betaL, eta_ 0 j] = '[tauL betaL, eta01].
  move=> nzj; apply/eqP; rewrite -subr_eq0 -cfdotBr.
  rewrite (canRL (addKr _) (defGa j nzj)) !addrA addrK -addrA addrCA.
  by rewrite opprD subrK cfdotBr !o_tauL_S ?subrr ?Iirr1_neq0.
split=> //; have [[[Itau1 Ztau1] Dtau1] irr_phi] := (cohL, irrL Lphi).
pose GammaL := tauL betaL - (1 - tau1 phi).
have DbetaL: tauL betaL = 1 - tau1 phi + GammaL by rewrite addrC subrK.
have RealGammaL: cfReal GammaL.
  rewrite /cfReal -subr_eq0 !rmorphB rmorph1 /= !opprB !addrA subrK addrC.
  rewrite -addrA addrCA addrA addr_eq0 opprB -Dade_aut -linearB /= -/tauL.
  rewrite rmorphB /= cfAutInd rmorph1 addrC opprB addrA subrK.
  by rewrite (cfConjC_Dade_coherent cohL) ?mFT_odd // -raddfB Dtau1 // ZsubL.
have:= Dade_Ind1_sub_lin cohL _ irr_phi Lphi; rewrite -/betaL -/tauL -/calL.
rewrite (seqInd_nontrivial _ _ _ irr_phi) ?odd_Frobenius_index_ler ?mFT_odd //.
case=> // -[o_tauL_1 o_betaL_1 ZbetaL] ub_betaL _.
have{o_tauL_1 o_betaL_1} o_GaL_1: '[GammaL, 1] = 0.
  by rewrite !cfdotBl cfnorm1 o_betaL_1 (orthoPr o_tauL_1) ?map_f ?subr0 ?subrr.
have Zt1phi: tau1 phi \in 'Z[irr G] by rewrite Ztau1 ?mem_zchar.
have Zeta01: eta01 \in 'Z[irr G] by apply: cycTIiso_vchar.
have ZbetaS: tau betaS \in 'Z[irr G].
  rewrite Dade_vchar // zchar_split A0beta ?Iirr1_neq0 //.
  by rewrite rpredB ?irr_vchar ?cfInd_vchar ?rpred1.
have Z_Ga: Gamma \in 'Z[irr G] by rewrite rpredD ?rpredB ?rpred1.
have Z_GaL: GammaL \in 'Z[irr G] by rewrite !rpredB ?rpred1.
have{RealGammaL} Gamma_even: (2 %| '[GammaL, Gamma])%C.
  by rewrite cfdot_real_vchar_even ?mFT_odd // o_GaL_1 (dvdC_nat 2 0).
set bSphi := '[tau betaS, tau1 phi]; set bLeta := '[tauL betaL, eta01].
have [ZbSphi ZbLeta]: bSphi \in Cint /\ bLeta \in Cint.
  by rewrite !Cint_cfdot_vchar.
have{Gamma_even} odd_bSphi_bLeta: (bSphi + bLeta == 1 %[mod 2])%C.
  rewrite -(conj_Cint ZbSphi) -cfdotC /bLeta DbetaL cfdotDl cfdotBl.
  have: '[tauL betaL, tau betaS] == 0 by rewrite o_tauL_S ?Iirr1_neq0.
  have ->: tau betaS = 1 - eta01 + Gamma by rewrite addrCA !addrA !subrK.
  rewrite !['[tau1 _, _]]cfdotDr 2!cfdotDr !cfdotNr DbetaL.
  rewrite 2!cfdotDl 2!['[_, eta01]]cfdotDl 2!['[_, Gamma]]cfdotDl !cfdotNl.
  rewrite cfnorm1 o_GaL_1 ['[1, Gamma]]cfdotC Ga1 conjC0 addr0 add0r.
  have ->: 1 = eta_ 0 0 by rewrite /w_ cycTIirr00 cycTIiso1.
  rewrite cfdot_cycTIiso mulrb ifN_eqC ?Iirr1_neq0 // add0r. 
  rewrite 2?(orthogonalP otau1eta _ _ (map_f _ _) (mem_eta _)) // oppr0 !add0r.
  by rewrite addr0 addrA addrC addr_eq0 !opprB addrA /eqCmod => /eqP <-.
have abs_mod2 a: a \in Cint -> {b : bool | a == b%:R %[mod 2]}%C.
  move=> Za; pose n := truncC `|a|; exists (odd n).
  apply: eqCmod_trans (eqCmod_addl_mul _ (rpred_nat _ n./2) _).
  rewrite addrC -natrM -natrD muln2 odd_double_half truncCK ?Cnat_norm_Cint //.
  rewrite -{1}[a]mul1r -(canLR (signrMK _) (CintEsign Za)) eqCmodMr // signrE.
  by rewrite /eqCmod opprB addrC subrK dvdC_nat dvdn2 odd_double.
have [[bL DbL] [bS DbS]] := (abs_mod2 _ ZbLeta, abs_mod2 _ ZbSphi).
have{odd_bSphi_bLeta} xor_bS_bL: bS (+) bL.
  rewrite eqCmod_sym in odd_bSphi_bLeta.
  have:= eqCmod_trans odd_bSphi_bLeta (eqCmodD DbS DbL).
  rewrite -natrD eqCmod_sym -(eqCmodDr _ 1) -mulrSr => xor_bS_bL.
  have:= eqCmod_trans xor_bS_bL (eqCmodm0 _); rewrite /eqCmod subr0.
  by rewrite (dvdC_nat 2 _.+1) dvdn2 /= negbK odd_add !oddb; case: (_ (+) _).
have ?: (0 != 1 %[mod 2])%C by rewrite eqCmod_sym /eqCmod subr0 (dvdC_nat 2 1).
case is_c1: bS; [left | right].
  rewrite is_c1 in DbS; split=> //.
  pose a_ (psi : 'CF(L)) := psi 1%g / e%:R.
  have Na_ psi: psi \in calL -> a_ psi \in Cnat by apply: dvd_index_seqInd1.
  have [X tau1X [D [dGa oXD oDtau1]]] := orthogonal_split (map tau1 calL) Gamma.
  have oo_L: orthonormal calL.
    by apply: sub_orthonormal (irr_orthonormal L); rewrite ?seqInd_uniq.
  have oo_tau1L: orthonormal (map tau1 calL) by apply: map_orthonormal.
  have defX: X = bSphi *: (\sum_(psi <- calL) a_ psi *: tau1 psi).
    have [_ -> defX] := orthonormal_span oo_tau1L tau1X.
    rewrite defX big_map scaler_sumr; apply: eq_big_seq => psi Lpsi.
    rewrite scalerA; congr (_ *: _); apply/eqP; rewrite -subr_eq0 mulrC.
    rewrite -[X](addrK D) -dGa cfdotBl (orthoPl oDtau1) ?map_f // subr0.
    rewrite cfdotC cfdotDr cfdotBr -/betaS -/eta01.
    have ->: 1 = eta_ 0 0 by rewrite /w_ cycTIirr00 cycTIiso1.
    rewrite 2?(orthogonalP otau1eta _ _ (map_f _ _) (mem_eta _)) // subrK.
    rewrite -cfdotC -(conj_Cnat (Na_ _ Lpsi)) -cfdotZr -cfdotBr.
    rewrite -raddfZ_Cnat ?Na_ // -raddfB cfdotC.
    rewrite Dtau1; last by rewrite zcharD1_seqInd ?seqInd_sub_lin_vchar.
    by rewrite o_tauL_S ?Iirr1_neq0 ?conjC0.
  have nz_bSphi: bSphi != 0 by apply: contraTneq DbS => ->.
  have ub_a: \sum_(psi <- calL) a_ psi ^+ 2 <= (u.-1 %/ q)%:R.
    apply: ler_trans (ubGa D X _ _ _); first 1 last; first by rewrite addrC.
    - by rewrite cfdotC oXD conjC0.
    - apply/orthoPl=> eta Weta; rewrite (span_orthogonal otau1eta) //.
      exact: memv_span.
    rewrite defX cfnormZ cfnorm_sum_orthonormal // mulr_sumr !big_seq.
    apply: ler_sum => psi Lpsi; rewrite -{1}(norm_Cnat (Na_ _ _)) //.
    by rewrite ler_pemull ?exprn_ge0 ?normr_ge0 // Cint_normK // sqr_Cint_ge1.
  congr (_ <= _): ub_a; do 2!apply: (mulIf (neq0CiG L H)); rewrite -/e.
  rewrite divfK ?neq0CiG // -mulrA -expr2 mulr_suml.
  rewrite -subn1 natrB ?neq0CG // -indexg1 mulrC.
  rewrite -(sum_seqIndD_square nsHL) ?normal1 ?sub1G // -/calL.
  apply: eq_big_seq => psi Lpsi; rewrite irrWnorm ?irrL // divr1.
  by rewrite -exprMn divfK ?neq0CiG.
rewrite is_c1 /= in xor_bS_bL; rewrite xor_bS_bL in DbL; split=> //.
have nz_bL: bLeta != 0 by apply: contraTneq DbL => ->.
have{ub_betaL} [X [otau1X oX1 [a Za defX]] [//|_ ubX]] := ub_betaL.
rewrite -/e in defX; rewrite -leC_nat -(ler_add2r (-1)); apply: ler_trans ubX.
pose calX0 := [seq w_ 0 j | j in predC1 0].
have ooX0: orthonormal calX0.
  apply: sub_orthonormal (irr_orthonormal W).
    by move=> _ /imageP[j _ ->]; apply: mem_irr.
  by apply/dinjectiveP=> j1 j2 _ _ /irr_inj/dprod_Iirr_inj[].
have Isigma: {in 'Z[calX0] &, isometry sigma}.
  by apply: in2W; apply: cycTIisometry.
rewrite -[X](subrK (bLeta *: (\sum_(xi <- calX0) sigma xi))).
rewrite cfnormDd ?ler_paddl ?cfnorm_ge0 //; last first.
  rewrite cfdotZr cfdot_sumr big1_seq ?mulr0 // => xi X0xi.
  apply/eqP; rewrite cfdotBl scaler_sumr cfproj_sum_orthonormal // subr_eq0.
  have {xi X0xi}[j nzj ->] := imageP X0xi; rewrite inE /= in nzj.
  rewrite -[bLeta](betaLeta j nzj) defX cfdotDl -addrA cfdotDl.
  have ->: 1 = eta_ 0 0 by rewrite /w_ cycTIirr00 cycTIiso1.
  rewrite cfdot_cycTIiso mulrb (ifN_eqC _ _ nzj) add0r eq_sym -subr_eq0 addrK.
  rewrite (span_orthogonal otau1eta) //; last by rewrite memv_span ?mem_eta.
  rewrite big_seq rpredD ?(rpredN, rpredZ, rpred_sum) ?memv_span ?map_f //.
  by move=> xi Lxi; rewrite rpredZ ?memv_span ?map_f.
rewrite cfnormZ cfnorm_map_orthonormal // size_image cardC1 nirrW2.
rewrite -(natrB _ (prime_gt0 pr_p)) Cint_normK // subn1.
by rewrite ler_pemull ?ler0n ?sqr_Cint_ge1.
Qed.

End Thirteen_17_to_19.

End Thirteen.


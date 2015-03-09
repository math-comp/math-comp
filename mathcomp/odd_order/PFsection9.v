(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime binomial ssralg poly finset.
Require Import fingroup morphism perm automorphism quotient action finalg zmodp.
Require Import gfunctor gproduct cyclic commutator center gseries nilpotent.
Require Import pgroup sylow hall abelian maximal frobenius.
Require Import matrix mxalgebra mxrepresentation mxabelem vector.
Require Import BGsection1 BGsection3 BGsection7 BGsection15 BGsection16.
Require Import algC classfun character inertia vcharacter.
Require Import PFsection1 PFsection2 PFsection3 PFsection4.
Require Import PFsection5 PFsection6 PFsection8.

(******************************************************************************)
(* This file covers Peterfalvi, Section 9: On the maximal subgroups of Types  *)
(* II, III and IV. For defW : W1 \x W2 = W, MtypeP : of_typeP M U defW, and   *)
(* H := M`_\F we define :                                                     *)
(*  Ptype_Fcore_kernel MtypeP == a maximal normal subgroup of M contained     *)
(*               (locally) H0    in H and containing 'C_H(U), provided M is   *)
(*                               not a maximal subgroup of type V.            *)
(*  Ptype_Fcore_kernel MtypeP == the stabiliser of Hbar := H / H0 in U; this  *)
(*   (locally to this file) C    is locked for performance reasons.           *)
(*        typeP_Galois MtypeP <=> U acts irreducibly on Hbar; this implies    *)
(*                               that M / H0C is isomorphic to a Galois group *)
(*                               acting on the semidirect product of the      *)
(*                               additive group of a finite field with a      *)
(*                               a subgroup of its multiplicative group.      *)
(* --> This predicate reflects alternative (b) in Peterfalvi (9.7).           *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory FinRing.Theory.

Section Nine.

Variable gT : minSimpleOddGroupType.
Local Notation G := (TheMinSimpleOddGroup gT).
Implicit Types (p q : nat) (x y z : gT).
Implicit Types H K L N P Q R S T U V W : {group gT}.

(* Peterfalvi (9.1) is covered by BGsection3.Frobenius_Wielandt_fixpoint. *)

(* These assumptions correspond to Peterfalvi, Hypothesis (9.2). *)

Variables M U W W1 W2 : {group gT}.
Hypotheses (maxM : M \in 'M) (defW : W1 \x W2 = W) (MtypeP: of_typeP M U defW).
Hypothesis notMtype5 : FTtype M != 5.

Local Notation "` 'M'" := (gval M) (at level 0, only parsing) : group_scope.
Local Notation "` 'U'" := (gval U) (at level 0, only parsing) : group_scope.
Local Notation "` 'W1'" := (gval W1) (at level 0, only parsing) : group_scope.
Local Notation H := `M`_\F%G.
Local Notation "` 'H'" := `M`_\F (at level 0) : group_scope.
Local Notation "` 'W2'" := (gval W2) (at level 0, only parsing) : group_scope.
Local Notation HU := M^`(1)%G.
Local Notation "` 'HU'" := `M^`(1) (at level 0) : group_scope.
Local Notation U' := U^`(1)%G.
Local Notation "` 'U''" := `U^`(1) (at level 0) : group_scope.

Let q := #|W1|.

Let defM : HU ><| W1 = M. Proof. by have [[]] := MtypeP. Qed.
Let defHU : H ><| U = HU. Proof. by have [_ []] := MtypeP. Qed.
Let nUW1 : W1 \subset 'N(U). Proof. by have [_ []] := MtypeP. Qed.
Let cHU' : U' \subset 'C(H). Proof. by have [_ []] := typeP_context MtypeP. Qed.

Let notMtype1 : FTtype M != 1%N. Proof. exact: FTtypeP_neq1 MtypeP. Qed.

Local Notation Mtype24 := (compl_of_typeII_IV maxM MtypeP notMtype5).
Let ntU : U :!=: 1. Proof. by have [] := Mtype24. Qed.
Let pr_q : prime q. Proof. by have [] := Mtype24. Qed.
Let ntW2 : W2 :!=: 1. Proof. by have [_ _ _ []] := MtypeP. Qed.
Let sW2H : W2 \subset H. Proof. by have [_ _ _ []] := MtypeP. Qed.
Let defW2 : 'C_H(W1) = W2. Proof. exact: typeP_cent_core_compl MtypeP. Qed.

Lemma Ptype_Fcore_sdprod : H ><| (U <*> W1) = M.
Proof.
have [_ /= sW1M mulHUW1 _ tiHUW1] := sdprod_context defM. 
have [/= /andP[sHHU _] sUHU mulHU nHU tiHU] := sdprod_context defHU.
rewrite sdprodE /= norm_joinEr // ?mulgA ?mulHU //.
  by rewrite mulG_subG nHU (subset_trans sW1M) ?gFnorm.
rewrite setIC -(setIidPr sHHU) setIA -group_modl //.
by rewrite (setIC W1) tiHUW1 mulg1 setIC tiHU.
Qed.
Local Notation defHUW1 := Ptype_Fcore_sdprod.

Lemma Ptype_Fcore_coprime : coprime #|H| #|U <*> W1|.
Proof.
by rewrite (coprime_sdprod_Hall_l defHUW1) ?(pHall_Hall (Fcore_Hall M)).
Qed.
Let coH_UW1 := Ptype_Fcore_coprime.
Let coHU : coprime #|H| #|U|.
Proof. exact: coprimegS (joing_subl U W1) coH_UW1. Qed.

Let not_cHU : ~~ (U \subset 'C(H)).
Proof. by have [_ [_ ->]] := typeP_context MtypeP. Qed.

Lemma Ptype_compl_Frobenius : [Frobenius U <*> W1 = U ><| W1].
Proof.
have [[_ _ ntW1 _] _ _ [_ _ _ _ prHU_W1] _] := MtypeP.
have [[_ _ _ tiHUW1] [_ sUHU _ _ tiHU]] := (sdprodP defM, sdprod_context defHU).
apply/Frobenius_semiregularP=> // [|x /prHU_W1 defCx].
  by rewrite sdprodEY //; apply/trivgP; rewrite -tiHUW1 setSI.
by apply/trivgP; rewrite -tiHU /= -{1}(setIidPr sUHU) setIAC defCx setSI.
Qed.
Local Notation frobUW1 := Ptype_compl_Frobenius.

Let nilH : nilpotent H. Proof. exact: Fcore_nil. Qed.
Let solH : solvable H. Proof. exact: nilpotent_sol. Qed.

(* This is Peterfalvi (9.3). *)
Lemma typeII_IV_core (p := #|W2|) :
  if FTtype M == 2 then 'C_H(U) = 1 /\ #|H| = (#|W2| ^ q)%N
  else [/\ prime p, 'C_H(U <*> W1) = 1 & #|H| = (p ^ q * #|'C_H(U)|)%N].
Proof.
have [_ _ nHUW1 _] := sdprodP defHUW1.
have /= [oH _ oH1] := Frobenius_Wielandt_fixpoint frobUW1 nHUW1 coH_UW1 solH.
have [Mtype2 {oH}| notMtype2 {oH1}] := boolP (FTtype M == 2).
  suffices regHU: 'C_H(U) = 1 by rewrite -defW2 oH1.
  have [_ _ _ HUtypeF defHUF] := compl_of_typeII maxM MtypeP Mtype2.
  have [_ _ [U0 [sU0U _]]] := HUtypeF; rewrite {}defHUF => frobHU0.
  have /set0Pn[x U0x]: U0^# != set0.
    by rewrite setD_eq0 subG1; case/Frobenius_context: frobHU0.
  apply/trivgP; rewrite -(Frobenius_reg_ker frobHU0 U0x) setIS // -cent_cycle.
  by rewrite centS // cycle_subG (subsetP sU0U) //; case/setD1P: U0x.
have p_pr: prime p.
  have [S pairMS [xdefW [U_S StypeP]]] := FTtypeP_pair_witness maxM MtypeP.
  have [[_ _ maxS] _] := pairMS; rewrite {1}(negPf notMtype2) /= => Stype2 _ _.
  by have [[]] := compl_of_typeII maxS StypeP Stype2.
rewrite -/q -/p centY setICA defW2 setIC in oH *.
suffices regW2U: 'C_W2(U) = 1 by rewrite -oH regW2U cards1 exp1n mul1n.
apply: prime_TIg => //=; apply: contra not_cHU => /setIidPl cUW2.
rewrite centsC (sameP setIidPl eqP) eqEcard subsetIl.
by rewrite -(@leq_pmul2l (p ^ q)) -?oH ?cUW2 //= expn_gt0 cardG_gt0.
Qed.

(* Existential witnesses for Peterfalvi (9.4). *)
Definition Ptype_Fcore_kernel of of_typeP M U defW :=
  odflt 1%G [pick H0 : {group gT} | chief_factor M H0 H & 'C_H(U) \subset H0].
Let H0 := (Ptype_Fcore_kernel MtypeP).
Local Notation "` 'H0'" := (gval H0) (at level 0, only parsing) : group_scope.
Local Notation Hbar := (H / `H0)%G.
Local Notation "` 'Hbar'" := (`H / `H0)%g (at level 0) : group_scope.
Let p := pdiv #|Hbar|.

(* This corresponds to Peterfalvi (9.4). *)
Lemma Ptype_Fcore_kernel_exists : chief_factor M H0 H /\ 'C_H(U) \subset H0.
Proof.
pose S := <<class_support 'C_H(U) H>> .
suffices [H1 maxH sCH1]: {H1 : {group gT} | maxnormal H1 H M & S \subset H1}.
  apply/andP; rewrite /H0 /Ptype_Fcore_kernel; case: pickP => // /(_ H1)/idP[].
  rewrite /chief_factor maxH Fcore_normal (subset_trans _ sCH1) ?sub_gen //.
  exact: sub_class_support.
apply/maxgroup_exists/andP; split.
  have snCH: 'C_H(U) <|<| H by rewrite nilpotent_subnormal ?subsetIl.
  by have [/setIidPl/idPn[] | // ] := subnormalEsupport snCH; rewrite centsC.
have [_ {3}<- nHUW1 _] := (sdprodP defHUW1).
rewrite norms_gen // mulG_subG class_support_norm norms_class_support //.
by rewrite normsI ?norms_cent // join_subG normG.
Qed.

Let chiefH0 : chief_factor M H0 H.
Proof. by have [] := Ptype_Fcore_kernel_exists. Qed.
Let ltH0H : H0 \proper H.
Proof. by case/andP: chiefH0 => /maxgroupp/andP[]. Qed.
Let nH0M : M \subset 'N(H0).
Proof. by case/andP: chiefH0 => /maxgroupp/andP[]. Qed.
Let sH0H : H0 \subset H. Proof. exact: proper_sub ltH0H. Qed.
Let nsH0M : H0 <| M. Proof. by rewrite /normal (subset_trans sH0H) ?gFsub. Qed.
Let nsH0H : H0 <| H. Proof. by rewrite (normalS _ (Fcore_sub _)). Qed.
Let minHbar : minnormal Hbar (M / H0).
Proof. exact: chief_factor_minnormal. Qed.
Let ntHbar : Hbar :!=: 1. Proof. by case/mingroupp/andP: minHbar. Qed.
Let solHbar: solvable Hbar. Proof. by rewrite quotient_sol. Qed.
Let abelHbar : p.-abelem Hbar.
Proof. by have [] := minnormal_solvable minHbar _ solHbar. Qed.
Let p_pr : prime p. Proof. by have [/pgroup_pdiv[]] := and3P abelHbar. Qed.
Let abHbar : abelian Hbar. Proof. exact: abelem_abelian abelHbar. Qed.

(* This is Peterfalvi, Hypothesis (9.5). *)
Fact Ptype_Fcompl_kernel_key : unit. Proof. by []. Qed.
Definition Ptype_Fcompl_kernel :=
  locked_with Ptype_Fcompl_kernel_key 'C_U(Hbar | 'Q)%G.
Local Notation C := Ptype_Fcompl_kernel.
Local Notation "` 'C'" := (gval C) (at level 0, only parsing) : group_scope.
Local Notation Ubar := (U / `C)%G.
Local Notation "` 'Ubar'" := (`U / `C)%g (at level 0) : group_scope.
Local Notation W1bar := (W1 / `H0)%G.
Local Notation "` 'W1bar'" := (`W1 / `H0)%g (at level 0) : group_scope.
Local Notation W2bar := 'C_Hbar(`W1bar)%G.
Local Notation "` 'W2bar'" := 'C_`Hbar(`W1bar) (at level 0) : group_scope.
Let c := #|C|.
Let u := #|Ubar|.
Local Notation tau := (FT_Dade0 maxM).
Local Notation "chi ^\tau" := (tau chi).
Let calX := Iirr_kerD M^`(1) H 1.
Let calS := seqIndD M^`(1) M M`_\F 1.
Let X_ Y := Iirr_kerD M^`(1) H Y.
Let S_ Y := seqIndD M^`(1) M M`_\F Y.

Local Notation inMb := (coset (gval H0)).

Local Notation H0C := (`H0 <*> `C)%G.
Local Notation "` 'H0C'" := (`H0 <*> `C) (at level 0) : group_scope.
Local Notation HC := (`H <*> `C)%G.
Local Notation "` 'HC'" := (`H <*> `C) (at level 0) : group_scope.
Local Notation H0U' := (`H0 <*> `U')%G.
Local Notation "` 'H0U''" := (gval H0 <*> `U')%G (at level 0) : group_scope.
Local Notation H0C' := (`H0 <*> `C^`(1)%g)%G.
Local Notation "` 'H0C''" := (`H0 <*> `C^`(1)) (at level 0) : group_scope.

Let defW2bar : W2bar :=: W2 / H0.
Proof.
rewrite -defW2 coprime_quotient_cent ?(subset_trans _ nH0M) //.
  by have [_ /mulG_sub[]] := sdprodP defM.
exact: coprimegS (joing_subr _ _) coH_UW1.
Qed.

Let sCU : C \subset U. Proof. by rewrite [C]unlock subsetIl. Qed.

Let nsCUW1 : C <| U <*> W1.
Proof.
have [_ sUW1M _ nHUW1 _] := sdprod_context defHUW1.
rewrite /normal [C]unlock subIset ?joing_subl // normsI //.
  by rewrite join_subG normG.
rewrite /= astabQ norm_quotient_pre ?norms_cent ?quotient_norms //.
exact: subset_trans sUW1M nH0M.
Qed.

Lemma Ptype_Fcore_extensions_normal :
  [/\ H0C <| M, HC <| M, H0U' <| M & H0C' <| M].
Proof.
have [nsHUM sW1M /mulG_sub[sHUM _] nHUW1 tiHUW1] := sdprod_context defM.
have [nsHHU sUHU /mulG_sub[sHHU _] nHU tiHU] := sdprod_context defHU.
have [sHM sUM] := (subset_trans sHHU sHUM, subset_trans sUHU sHUM).
have sCM: C \subset M := subset_trans sCU sUM.
have sH0C_M: H0C \subset M by rewrite /normal join_subG (subset_trans sH0H).
have [nH0C nH0_H0C] := (subset_trans sCM nH0M, subset_trans sH0C_M nH0M).
have nsH0C: H0C <| M.
  rewrite /normal sH0C_M -{1}defM sdprodEY //= -defHU sdprodEY //= -joingA.
  rewrite join_subG andbC normsY ?(normal_norm nsCUW1) //=; last first.
    by rewrite (subset_trans _ nH0M) // join_subG sUM.
  rewrite -quotientYK // -{1}(quotientGK nsH0H) morphpre_norms //= [C]unlock.
  by rewrite cents_norm // centsC -quotient_astabQ quotientS ?subsetIr.
split=> //; first by rewrite /= -{1}(joing_idPl sH0H) -joingA normalY ?gFnormal.
  rewrite normalY // /normal (subset_trans (der_sub 1 U)) //=.
  rewrite -{1}defM sdprodEY //= -defHU sdprodEY //=.
  rewrite !join_subG gFnorm cents_norm 1?centsC //=.
  by rewrite (char_norm_trans (der_char _ _)).
suffices ->: H0C' :=: H0 <*> H0C^`(1).
  by rewrite normalY ?(char_normal_trans (der_char _ _)).
rewrite /= -?quotientYK ?(subset_trans (der_sub _ _)) ?subsetIl //=.
by rewrite !quotient_der ?cosetpreK ?subsetIl.
Qed.
Local Notation nsH0xx_M := Ptype_Fcore_extensions_normal.

Let Du : u = #|HU : HC|.
Proof.
have nCU := subset_trans (joing_subl U W1) (normal_norm nsCUW1).
by rewrite -(index_sdprodr defHU) -?card_quotient.
Qed.

(* This is Peterfalvi (9.6). *)
Lemma Ptype_Fcore_factor_facts :
  [/\ C :!=: U, #|W2bar| = p & #|Hbar| = p ^ q]%N.
Proof.
have [defUW1 _ ntW1 _ _] := Frobenius_context Ptype_compl_Frobenius.
have coHW1: coprime #|H| #|W1| := coprimegS (joing_subr U W1) coH_UW1.
have [_ sUW1M _ nHUW1 _] := sdprod_context defHUW1.
have nH0UW1 := subset_trans sUW1M nH0M; have [nH0U nH0W1] := joing_subP nH0UW1.
have regUHb: 'C_Hbar(U / H0) = 1.
  have [_ sCH0] := Ptype_Fcore_kernel_exists.
  by rewrite -coprime_quotient_cent ?(nilpotent_sol nilH) ?quotientS1.
have ->: C != U.
  apply: contraNneq ntHbar => defU; rewrite -subG1 -regUHb subsetIidl centsC.
  by rewrite -defU [C]unlock -quotient_astabQ quotientS ?subsetIr.
have frobUW1b: [Frobenius U <*> W1 / H0 = (U / H0) ><| W1bar].
  have tiH0UW1 := coprime_TIg (coprimeSg sH0H coH_UW1).
  have /isomP[inj_f im_f] := quotient_isom nH0UW1 tiH0UW1.
  have:= injm_Frobenius (subxx _) inj_f frobUW1.
  by rewrite im_f !morphim_restrm !(setIidPr _) ?joing_subl ?joing_subr.
have{frobUW1b} oHbar: #|Hbar| = (#|W2bar| ^ q)%N.
  have nHbUW1 : U <*> W1 / H0 \subset 'N(Hbar) := quotient_norms H0 nHUW1.
  have coHbUW1 : coprime #|Hbar| #|U <*> W1 / H0| by apply: coprime_morph.
  have [//|_ _ -> //] := Frobenius_Wielandt_fixpoint frobUW1b nHbUW1 coHbUW1 _.
  by rewrite -(card_isog (quotient_isog _ _)) // coprime_TIg ?(coprimeSg sH0H).
have abelW2bar: p.-abelem W2bar := abelemS (subsetIl _ _) abelHbar.
rewrite -(part_pnat_id (abelem_pgroup abelW2bar)) p_part in oHbar *.
suffices /eqP cycW2bar: logn p #|W2bar| == 1%N by rewrite oHbar cycW2bar.
have cycW2: cyclic W2 by have [_ _ _ []] := MtypeP.
rewrite eqn_leq -abelem_cyclic //= -/W2bar {1}defW2bar quotient_cyclic //=.
rewrite lt0n; apply: contraNneq ntHbar => W2bar1.
by rewrite trivg_card1 oHbar W2bar1 exp1n.
Qed.

Lemma def_Ptype_factor_prime : prime #|W2| -> p = #|W2|.
Proof.
move=> prW2; suffices: p \in \pi(W2) by rewrite !(primes_prime, inE) // => /eqP.
rewrite mem_primes p_pr cardG_gt0; have [_ <- _] := Ptype_Fcore_factor_facts.
by rewrite defW2bar dvdn_quotient.
Qed.

(* The first assertion of (9.4)(b) (the rest is subsumed by (9.6)). *)
Lemma typeIII_IV_core_prime : FTtype M != 2 -> p = #|W2|.
Proof.
by have:= typeII_IV_core => /=; case: ifP => // _ [/def_Ptype_factor_prime].
Qed.

Let frobUW1c : [Frobenius U <*> W1 / C = Ubar ><| W1 / C].
Proof.
apply: Frobenius_quotient frobUW1 _ nsCUW1 _.
  by apply: nilpotent_sol; have [_ []] := MtypeP.
by have [] := Ptype_Fcore_factor_facts; rewrite eqEsubset sCU.
Qed.  

Definition typeP_Galois := acts_irreducibly U Hbar 'Q.

(* This is Peterfalvi (9.7)(a). *)
Lemma typeP_Galois_Pn :
    ~~ typeP_Galois ->
  {H1 : {group coset_of H0} |
    [/\ #|H1| = p, U / H0 \subset 'N(H1), [acts U, on H1 | 'Q],
        \big[dprod/1]_(w in W1bar) H1 :^ w = Hbar
      & let a := #|U : 'C_U(H1 | 'Q)| in
        [/\ a > 1, a %| p.-1, cyclic (U / 'C_U(H1 | 'Q))
          & exists V : {group 'rV['Z_a]_q.-1}, Ubar \isog V]]}.
Proof.
have [_ sUW1M defHUW1 nHUW1 _] := sdprod_context defHUW1.
have [nHU nHW1] := joing_subP nHUW1.
have nH0UW1 := subset_trans sUW1M nH0M; have [nH0U nH0W1] := joing_subP nH0UW1.
rewrite /typeP_Galois acts_irrQ //= => not_minHbarU.
have [H1 minH1 sH1Hb]: {H1 | minnormal (gval H1) (U / H0) & H1 \subset Hbar}.
  by apply: mingroup_exists; rewrite ntHbar quotient_norms.
exists H1; have [defH1 | ltH1H] := eqVproper sH1Hb.
  by rewrite -defH1 minH1 in not_minHbarU.
have [/andP[ntH1 nH1U] _] := mingroupP minH1.
have actsUH1: [acts U, on H1 | 'Q].
  by rewrite -(cosetpreK H1) actsQ ?norm_quotient_pre.
have [nH0H [neqCU _ oHbar]] := (normal_norm nsH0H, Ptype_Fcore_factor_facts).
have nUW1b: W1bar \subset 'N(U / H0) by apply: quotient_norms.
have oW1b: #|W1bar| = q.
  rewrite -(card_isog (quotient_isog _ _)) // coprime_TIg //.
  by rewrite (coprimeSg sH0H) // (coprimegS (joing_subr U W1)).
have [oH1 defHbar]: #|H1| = p /\ \big[dprod/1]_(w in W1bar) H1 :^ w = Hbar.
  have nHbUW1: U <*> W1 / H0 \subset 'N(Hbar) by apply: quotient_norms.
  pose rUW1 := abelem_repr abelHbar ntHbar nHbUW1.
  have irrUW1: mx_irreducible rUW1.
    apply/abelem_mx_irrP/mingroupP; split=> [|H2]; first by rewrite ntHbar.
    case/andP=> ntH2 nH2UW1 sH2H; case/mingroupP: minHbar => _; apply=> //.
    by rewrite ntH2 -defHUW1 quotientMl // mulG_subG sub_abelian_norm.
  have nsUUW1: U / H0 <| U <*> W1 / H0 by rewrite quotient_normal // normalYl.
  pose rU := subg_repr rUW1 (normal_sub nsUUW1).
  pose V1 := rowg_mx (abelem_rV abelHbar ntHbar @* H1).
  have simV1: mxsimple rU V1 by apply/mxsimple_abelem_subg/mxsimple_abelemGP.
  have [W0 /subsetP sW01 [sumW0 dxW0]] := Clifford_basis irrUW1 simV1.
  have def_q: q = (#|W0| * \rank V1)%N.
    transitivity (\rank (\sum_(w in W0) V1 *m rUW1 w))%R.
      by rewrite sumW0 mxrank1 /= (dim_abelemE abelHbar) // oHbar pfactorK.
    rewrite (mxdirectP dxW0) -sum_nat_const; apply: eq_bigr => x /sW01/= Wx.
    by rewrite mxrankMfree ?row_free_unit ?repr_mx_unit.
  have oH1: #|H1| = (p ^ \rank V1)%N.
    by rewrite -{1}(card_Fp p_pr) -card_rowg rowg_mxK card_injm ?abelem_rV_injm.
  have oW0: #|W0| = q.
    apply/prime_nt_dvdP=> //; last by rewrite def_q dvdn_mulr.
    apply: contraTneq (proper_card ltH1H) => trivW0.
    by rewrite oHbar def_q trivW0 mul1n -oH1 ltnn.
  have q_gt0 := prime_gt0 pr_q.
  rewrite oH1 -(mulKn (\rank V1) q_gt0) -{1}oW0 -def_q divnn q_gt0.
  have defHbar: \big[dprod/1]_(w in W0) H1 :^ w = Hbar.
    have inj_rV_Hbar := rVabelem_injm abelHbar ntHbar.
    have/(injm_bigdprod _ inj_rV_Hbar)/= := bigdprod_rowg sumW0 dxW0.
    rewrite sub_im_abelem_rV rowg1 im_rVabelem => <- //=; apply: eq_bigr => w.
    by move/sW01=> Ww; rewrite abelem_rowgJ ?rowg_mxK ?abelem_rV_mK.
  have injW0: {in W0 &, injective (fun w => H1 :^ w)}.
    move=> x y Wx Wy /= eq_Hxy; apply: contraNeq ntH1 => neq_xy.
    rewrite -(conjsg_eq1 _ x) -[H1 :^ x]setIid {1}eq_Hxy; apply/eqP.
    rewrite (bigD1 y) // (bigD1 x) /= ?Wx // dprodA in defHbar.
    by case/dprodP: defHbar => [[_ _ /dprodP[_ _ _ ->] _]].
  have defH1W0: [set H1 :^ w | w in W0] = [set H1 :^ w | w in W1 / H0].
    apply/eqP; rewrite eqEcard (card_in_imset injW0) oW0 -oW1b leq_imset_card.
    rewrite andbT; apply/subsetP=> _ /imsetP[w /sW01/= Ww ->].
    move: Ww; rewrite norm_joinEr ?quotientMl // => /mulsgP[x w1 Ux Ww1 ->].
    by rewrite conjsgM (normsP nH1U) // mem_imset.
  have injW1: {in W1 / H0 &, injective (fun w => H1 :^ w)}.
    by apply/imset_injP; rewrite -defH1W0 (card_in_imset injW0) oW0 oW1b.
  by rewrite -(big_imset id injW1) -defH1W0 big_imset.
split=> //; set a := #|_ : _|; pose q1 := #|(W1 / H0)^#|.
have a_gt1: a > 1.
  rewrite indexg_gt1 subsetIidl /= astabQ -sub_quotient_pre //. 
  apply: contra neqCU => cH1U; rewrite [C]unlock (sameP eqP setIidPl) /= astabQ.
  rewrite -sub_quotient_pre // -(bigdprodWY defHbar) cent_gen centsC.
  by apply/bigcupsP=> w Ww; rewrite centsC centJ -(normsP nUW1b w) ?conjSg.
have Wb1: 1 \in W1bar := group1 _.
have ->: q.-1 = q1 by rewrite -oW1b (cardsD1 1) Wb1.
have /cyclicP[h defH1]: cyclic H1 by rewrite prime_cyclic ?oH1.
have o_h: #[h] = p by rewrite defH1 in oH1.
have inj_Zp_h w := injm_Zp_unitm (h ^ w).
pose phi w := invm (inj_Zp_h w) \o restr_perm <[h ^ w]> \o actperm 'Q.
have dU w: w \in W1bar -> {subset U <= 'dom (phi w)}.
  move=> Ww x Ux; have Qx := subsetP (acts_dom actsUH1) x Ux.
  rewrite inE Qx /= im_Zp_unitm inE mem_morphpre //=; last first.
    by apply: Aut_restr_perm (actperm_Aut 'Q _); rewrite //= quotientT.
  rewrite cycleJ -defH1 !inE /=; apply/subsetP=> z H1w_z; rewrite inE actpermK.
  rewrite qactJ (subsetP nH0U) ?memJ_norm // normJ mem_conjg.
  by rewrite (subsetP nH1U) // -mem_conjg (normsP nUW1b) ?mem_quotient.
have sUD := introT subsetP (dU _ _).
have Kphi w: 'ker (phi w) = 'C(H1 :^ w | 'Q).
  rewrite !ker_comp ker_invm -kerE ker_restr_perm defH1 -cycleJ.
  apply/setP=> x; rewrite !inE; congr (_ && _) => /=.
  by apply: eq_subset_r => h1; rewrite !inE actpermK.
have o_phiU w: w \in W1bar -> #|phi w @* U| = a.
  move=> Ww; have [w1 Nw1 Ww1 def_w] := morphimP Ww.
  rewrite card_morphim Kphi (setIidPr _) ?sUD // /a indexgI /= !astabQ.
  by rewrite centJ def_w morphpreJ // -{1}(normsP nUW1 w1 Ww1) indexJg.
have a_dv_p1: a %| p.-1.
  rewrite -(o_phiU 1) // (dvdn_trans (cardSg (subsetT _))) // card_units_Zp //.
  by rewrite conjg1 o_h (@totient_pfactor p 1) ?muln1.
have cycZhw w: cyclic (units_Zp #[h ^ w]).
  rewrite -(injm_cyclic (inj_Zp_h w)) // im_Zp_unitm Aut_prime_cyclic //=.
  by rewrite -orderE orderJ o_h.
have cyc_phi1U: cyclic (phi 1 @* U) := cyclicS (subsetT _) (cycZhw 1).
split=> //; last have{cyc_phi1U a_dv_p1} [z def_z] := cyclicP cyc_phi1U.
  by rewrite -(conjsg1 H1) -Kphi (isog_cyclic (first_isog_loc _ _)) ?sUD.
have o_hw w: #[h ^ w] = #[h ^ 1] by rewrite !orderJ.
pose phi1 w x := eq_rect _ (fun m => {unit 'Z_m}) (phi w x) _ (o_hw w).
have val_phi1 w x: val (phi1 w x) = val (phi w x) :> nat.
  by rewrite /phi1; case: _ / (o_hw _).
have mem_phi1 w x: w \in W1bar -> x \in U -> phi1 w x \in <[z]>%G.
  move=> Ww Ux; have: #|<[z]>%G| = a by rewrite /= -def_z o_phiU.
  rewrite /phi1; case: _ / (o_hw w) <[z]>%G => A oA /=.
  suffices <-: phi w @* U = A by rewrite mem_morphim // dU.
  by apply/eqP; rewrite (eq_subG_cyclic (cycZhw w)) ?subsetT // oA o_phiU.
have o_z: #[z] = a by rewrite orderE -def_z o_phiU.
pose phi0 w x := ecast m 'Z_m o_z (invm (injm_Zpm z) (phi1 w x)).
pose psi x := (\row_(i < q1) (phi0 (enum_val i) x * (phi0 1 x)^-1)%g)%R.
have psiM: {in U &, {morph psi: x y / x * y}}.
  have phi0M w: w \in W1bar -> {in U &, {morph phi0 w: x y / x * y}}.
    move=> Ww x y Ux Uy; rewrite /phi0; case: (a) / (o_z) => /=.
    rewrite -morphM; first 1 [congr (invm _ _)] || by rewrite im_Zpm mem_phi1.
    by rewrite /phi1; case: _ / (o_hw w); rewrite /= -morphM ?dU.
  move=> x y Ux Uy; apply/rowP=> i; have /setD1P[_ Ww] := enum_valP i.
  by rewrite !{1}mxE !{1}phi0M // addrCA -addrA -opprD addrCA addrA.
suffices Kpsi: 'ker (Morphism psiM) = C.
  by exists [group of Morphism psiM @* U]; rewrite /Ubar -Kpsi first_isog.
apply/esym/eqP; rewrite eqEsubset; apply/andP; split.
  rewrite [C]unlock -(bigdprodWY defHbar); apply/subsetP=> x /setIP[Ux cHx].
  suffices phi0x1 w: w \in W1bar -> phi0 w x = 1.
    rewrite !inE Ux; apply/eqP/rowP=> i; have /setD1P[_ Ww] := enum_valP i.
    by rewrite !mxE !phi0x1 ?mulgV.
  move=> Ww; apply: val_inj; rewrite /phi0; case: (a) / (o_z); congr (val _).
  suffices /eqP->: phi1 w x == 1 by rewrite morph1.
  rewrite -2!val_eqE [val _]val_phi1 -(o_hw w) [phi _ _]mker // Kphi.
  by apply: subsetP (astabS _ _) _ cHx; rewrite sub_gen // (bigcup_sup w).
have sKU: 'ker (Morphism psiM) \subset U by apply: subsetIl.
rewrite -quotient_sub1 -?(Frobenius_trivg_cent frobUW1c); last first.
  by apply: subset_trans (normal_norm nsCUW1); rewrite subIset ?joing_subl.
rewrite subsetI quotientS //= quotient_cents2r // [C]unlock subsetI.
rewrite (subset_trans (commSg W1 sKU)) ?commg_subl //= astabQ gen_subG /=.
apply/subsetP=> _ /imset2P[x w1 Kx Ww1 ->].
have:= Kx; rewrite -groupV 2!inE groupV => /andP[Ux /set1P/rowP psi_x'0].
have [nH0x Ux'] := (subsetP nH0U x Ux, groupVr Ux); pose x'b := (inMb x)^-1.
rewrite mem_morphpre ?groupR ?morphR //= ?(subsetP nH0W1) //.
have conj_x'b w: w \in W1bar -> (h ^ w) ^ x'b = (h ^ w) ^+ val (phi 1 x^-1).
  move=> Ww; transitivity (Zp_unitm (phi w x^-1) (h ^ w)).
    have /morphpreP[_ /morphpreP[Px' Rx']] := dU w Ww x^-1 Ux'.
    rewrite invmK ?restr_permE ?cycle_id //.
    by rewrite actpermE qactJ groupV nH0x morphV.
  have:= Ww; rewrite -(setD1K Wb1) autE ?cycle_id // => /setU1P[-> // | W'w].
  have /eqP := psi_x'0 (enum_rank_in W'w w); rewrite 2!mxE enum_rankK_in //.
  rewrite -eq_mulgV1 -val_eqE /phi0; case: (a) / (o_z); rewrite /= val_eqE.
  rewrite (inj_in_eq (injmP (injm_invm _))) /= ?im_Zpm ?mem_phi1 //.
  by rewrite -2!val_eqE /= !val_phi1 // => /eqP->.
rewrite -sub_cent1 -(bigdprodWY defHbar) gen_subG; apply/bigcupsP=> w2 Ww2.
rewrite defH1 -cycleJ cycle_subG cent1C inE conjg_set1 !conjgM // conj_x'b //.
rewrite conjXg -!conjgM -conj_x'b ?groupM ?groupV ?mem_quotient //.
by rewrite !conjgM !conjgKV.
Qed.

(* This is Peterfalvi (9.7)(b). *)
(* Note that part of this statement feeds directly into the final chapter of  *)
(* the proof (PFsection14 and BGappendixC) and is not used before; we have    *)
(* thus chosen to formulate the statement of (9.7)(b) accordingly.            *)
(*   For example, we supply separately the three component of the semi-direct *)
(* product isomorphism, because no use is made of the global isomorphism. We  *)
(* also state explicitly that the image of W2bar is Fp because this is the    *)
(* fact used in B & G, Appendix C, it is readily available during the proof,  *)
(* whereas it can only be derived from the original statement of (9.7)(b) by  *)
(* using Galois theory. Indeed the Galois part of the isomorphism is only     *)
(* needed for this -- so with the formulation below it will not be used.      *)
(*   In order to avoid the use of the Wedderburn theorem on finite division   *)
(* rings we build the field F from the enveloping algebra of the              *)
(* representation of U rather than its endomorphism ring: then the fact that  *)
(* Ubar is abelian yields commutativity directly.                              *)
Lemma typeP_Galois_P :
    typeP_Galois ->
  {F : finFieldType & {phi : {morphism Hbar >-> F}
     & {psi : {morphism U >-> {unit F}} & {eta : {morphism W1 >-> {perm F}}
   & forall alpha : {perm F}, reflect (rmorphism alpha) (alpha \in eta @* W1)
   & [/\ 'injm eta, {in Hbar & W1, morph_act 'Q 'P phi eta}
       & {in U & W1, forall x w, val (psi (x ^ w)) = eta w (val (psi x))}]}
   & 'ker psi = C /\ {in Hbar & U, morph_act 'Q 'U phi psi}}
   & [/\ #|F| = (p ^ q)%N, isom Hbar [set: F] phi & phi @* W2bar = <[1%R : F]>]}
   & [/\ cyclic Ubar, coprime u p.-1 & u %| (p ^ q).-1 %/ p.-1]}.
Proof.
move=> irrU; have [_ sUW1M _ /joing_subP[nHU nHW1] _] := sdprod_context defHUW1.
have [nHbU nHbW1] := (quotient_norms H0 nHU, quotient_norms H0 nHW1).
have{sUW1M} /joing_subP[nH0U nH0W1] := subset_trans sUW1M nH0M.
have [ltCU oW2b oHb] := Ptype_Fcore_factor_facts.
pose rU := abelem_repr abelHbar ntHbar nHbU.
pose inHb := rVabelem abelHbar ntHbar; pose outHb := abelem_rV abelHbar ntHbar.
have{irrU} irrU: mx_irreducible rU by apply/abelem_mx_irrP; rewrite -acts_irrQ.
pose E_U := [pred A | (A \in enveloping_algebra_mx rU)%MS].
have cEE A: A \in E_U -> centgmx rU A.
  case/envelop_mxP=> z_ ->{A}; rewrite -memmx_cent_envelop linear_sum.
  rewrite summx_sub // => x Ux; rewrite linearZ scalemx_sub {z_}//=.
  rewrite memmx_cent_envelop; apply/centgmxP=> y Uy.
  rewrite -repr_mxM // commgC 2?repr_mxM ?(groupR, groupM) // -/rU.
  apply/row_matrixP=> i; rewrite row_mul; move: (row i _) => h.
  have cHbH': (U / H0)^`(1) \subset 'C(Hbar).
    by rewrite -quotient_der ?quotient_cents.
  apply: rVabelem_inj; rewrite rVabelemJ ?groupR //.
  by apply: (canLR (mulKg _)); rewrite -(centsP cHbH') ?mem_commg ?mem_rVabelem.
have{cEE} [F [outF [inF outFK inFK] E_F]]:
  {F : finFieldType & {outF : {rmorphism F -> 'M(Hbar)%Mg}
   & {inF : {additive _} | cancel outF inF & {in E_U, cancel inF outF}}
   & forall a, outF a \in E_U}}%R.
- pose B := row_base (enveloping_algebra_mx rU).
  have freeB: row_free B by apply: row_base_free.
  pose outF := [additive of vec_mx \o mulmxr B].
  pose inF := [additive of mulmxr (pinvmx B) \o mxvec].
  have E_F a: outF a \in E_U by rewrite !inE vec_mxK mulmx_sub ?eq_row_base.
  have inK: {in E_U, cancel inF outF}.
    by move=> A E_A; rewrite /= mulmxKpV ?mxvecK ?eq_row_base.
  have outI: injective outF := inj_comp (can_inj vec_mxK) (row_free_inj freeB).
  have outK: cancel outF inF by move=> a; apply: outI; rewrite inK ?E_F.
  pose one := inF 1%R; pose mul a b := inF (outF a * outF b)%R.
  have outM: {morph outF: a b / mul a b >-> a * b}%R.
    by move=> a b; rewrite inK //; apply: envelop_mxM; exact: E_F.
  have out0: outF 0%R = 0%R by apply: raddf0.
  have out1: outF one = 1%R by rewrite inK //; exact: envelop_mx1.
  have nzFone: one != 0%R by rewrite -(inj_eq outI) out1 out0 oner_eq0.
  have mulA: associative mul by move=> *; apply: outI; rewrite !{1}outM mulrA.
  have mulC: commutative mul.
    move=> a b; apply: outI; rewrite !{1}outM.
    by apply: cent_mxP (E_F a); rewrite memmx_cent_envelop cEE ?E_F.
  have mul1F: left_id one mul by move=> a; apply: outI; rewrite outM out1 mul1r.
  have mulD: left_distributive mul +%R%R.
    by move=> a1 a2 b; apply: canLR outK _; rewrite !raddfD mulrDl -!{1}outM.
  pose Fring_NC := RingType 'rV__ (ComRingMixin mulA mulC mul1F mulD nzFone).
  pose Fring := ComRingType Fring_NC mulC.
  have outRM: multiplicative (outF : Fring -> _) by [].
  have mulI (nza : {a | a != 0%R :> Fring}): GRing.rreg (val nza).
    case: nza => a /=; rewrite -(inj_eq outI) out0 => nzA b1 b2 /(congr1 outF).
    rewrite !{1}outM => /row_free_inj eqB12; apply/outI/eqB12.
    by rewrite row_free_unit (mx_Schur irrU) ?cEE ?E_F.
  pose inv (a : Fring) := oapp (fun nza => invF (mulI nza) one) a (insub a).
  have inv0: (inv 0 = 0)%R by rewrite /inv insubF ?eqxx.
  have mulV: GRing.Field.axiom inv.
    by move=> a nz_a; rewrite /inv insubT /= (f_invF (mulI (exist _ _ _))).
  pose Funit := FieldUnitMixin mulV inv0.
  pose FringUcl := @GRing.ComUnitRing.Class _ (GRing.ComRing.class Fring) Funit.
  have Ffield := @FieldMixin (GRing.ComUnitRing.Pack FringUcl nat) _ mulV inv0.
  pose F := FieldType (IdomainType _ (FieldIdomainMixin Ffield)) Ffield.
  by exists [finFieldType of F], (AddRMorphism outRM); first exists inF.
pose in_uF (a : F) : {unit F} := insubd (1 : {unit F}) a.
have in_uF_E a: a != 1 -> val (in_uF a) = a.
  by move=> nt_a; rewrite insubdK /= ?unitfE.
have [psi psiK]: {psi : {morphism U >-> {unit F}}
                      | {in U, forall x, outF (val (psi x)) = rU (inMb x)}}.
- pose psi x := in_uF (inF (rU (inMb x))).
  have psiK x: x \in U -> outF (val (psi x)) = rU (inMb x).
    move/(mem_quotient H0)=> Ux; have EUx := envelop_mx_id rU Ux.
    rewrite in_uF_E ?inFK //; apply: contraTneq (repr_mx_unitr rU Ux).
    by move/(canRL_in inFK EUx)->; rewrite rmorph0 unitr0.
  suffices psiM: {in U &, {morph psi: x y / x * y}} by exists (Morphism psiM).
  move=> x y Ux Uy /=; apply/val_inj/(can_inj outFK); rewrite rmorphM //.
  by rewrite !{1}psiK ?groupM // morphM ?(subsetP nH0U) ?repr_mxM ?mem_quotient.
have /trivgPn/sig2W[s W2s nts]: W2bar != 1%G.
  by rewrite -cardG_gt1 oW2b prime_gt1.
pose sb := outHb s; have [Hs cW1s] := setIP W2s.
have nz_sb: sb != 0%R by rewrite morph_injm_eq1 ?abelem_rV_injm.
pose phi' a : coset_of H0 := inHb (sb *m outF a)%R.
have Hphi' a: phi' a \in Hbar by apply: mem_rVabelem.
have phi'D: {in setT &, {morph phi' : a b / a * b}}.
  by move=> a b _ _; rewrite /phi' !raddfD [inHb _]morphM ?mem_im_abelem_rV.
have inj_phi': injective phi'.
  move=> a b /rVabelem_inj eq_sab; apply: contraNeq nz_sb.
  rewrite -[sb]mulmx1 idmxE -(rmorph1 outF) -subr_eq0 => /divff <-.
  by rewrite rmorphM mulmxA !raddfB /= eq_sab subrr mul0mx.
have injm_phi': 'injm (Morphism phi'D) by apply/injmP; exact: in2W.
have Dphi: 'dom (invm injm_phi') = Hbar.
  apply/setP=> h; apply/morphimP/idP=> [[a _ _ ->] // | Hh].
  have /cyclic_mxP[A E_A def_h]: (outHb h <= cyclic_mx rU sb)%MS.
    by rewrite -(mxsimple_cyclic irrU) ?submx1.
  by exists (inF A); rewrite ?inE //= /phi' inFK // -def_h [inHb _]abelem_rV_K.
have [phi [def_phi Kphi _ im_phi]] := domP _ Dphi.
have{Kphi} inj_phi: 'injm phi by rewrite Kphi injm_invm.
have{im_phi} im_phi: phi @* Hbar = setT by rewrite im_phi -Dphi im_invm.
have phiK: {in Hbar, cancel phi phi'} by rewrite def_phi -Dphi; exact: invmK.
have{def_phi Dphi injm_phi'} phi'K: cancel phi' phi.
  by move=> a; rewrite def_phi /= invmE ?inE.
have phi'1: phi' 1%R = s by rewrite /phi' rmorph1 mulmx1 [inHb _]abelem_rV_K.
have phi_s: phi s = 1%R by rewrite -phi'1 phi'K.
have phiJ: {in Hbar & U, forall h x, phi (h ^ inMb x) = phi h * val (psi x)}%R.
  move=> h x Hh Ux; have Uxb := mem_quotient H0 Ux.
  apply: inj_phi'; rewrite phiK ?memJ_norm ?(subsetP nHbU) // /phi' rmorphM.
  by rewrite psiK // mulmxA [inHb _]rVabelemJ // -/inHb [inHb _]phiK.
have Kpsi: 'ker psi = C.
  apply/setP=> x; rewrite [C]unlock 2!in_setI /= astabQ; apply: andb_id2l => Ux.
  have Ubx := mem_quotient H0 Ux; rewrite 3!inE (subsetP nH0U) //= inE.
  apply/eqP/centP=> [psi_x1 h Hh | cHx]; last first.
    by apply/val_inj; rewrite -[val _]mul1r -phi_s -phiJ // conjgE -cHx ?mulKg.
  red; rewrite (conjgC h) -[h ^ _]phiK ?memJ_norm ?(subsetP nHbU) ?phiJ //.
  by rewrite psi_x1 mulr1 phiK.
have etaP (w : subg_of W1): injective (fun a => phi (phi' a ^ inMb (val w))).
  case: w => w /=/(mem_quotient H0)/(subsetP nHbW1) => nHw a b eq_ab.
  apply/inj_phi'/(conjg_inj (inMb w)).
  by apply: (injmP inj_phi) eq_ab; rewrite memJ_norm ?mem_rVabelem.
pose eta w : {perm F} := perm (etaP (subg W1 w)).
have etaK: {in Hbar & W1, forall h w, eta w (phi h) = phi (h ^ inMb w)}.
  by move=> h w Hh Ww; rewrite /= permE subgK ?phiK.
have eta1 w: w \in W1 -> eta w 1%R = 1%R.
  move=> Ww; rewrite -phi_s etaK //.
  by rewrite conjgE (centP cW1s) ?mulKg ?mem_quotient.
have etaM: {in W1 &, {morph eta: w1 w2 / w1 * w2}}.
  move=> w1 w2 Ww1 Ww2; apply/permP=> a; rewrite -[a]phi'K permM.
  rewrite !etaK ?memJ_norm ?groupM ?(subsetP nHbW1) ?mem_quotient //.
  by rewrite -conjgM -morphM ?(subsetP nH0W1).
have etaMpsi a: {in U & W1, forall x w, 
  eta w (a * val (psi x)) = eta w a * val (psi (x ^ w)%g)}%R.
- move=> x w Ux Ww; rewrite -[a]phi'K (etaK _ w (Hphi' a) Ww).
  rewrite -!phiJ // ?memJ_norm ?(subsetP nHbW1, subsetP nUW1) ?mem_quotient //.
  rewrite etaK ?memJ_norm ?(subsetP nHbU) ?mem_quotient // -!conjgM.
  by rewrite conjgC -morphJ ?(subsetP nH0U x Ux, subsetP nH0W1 w Ww).
have psiJ: {in U & W1, forall x w, val (psi (x ^ w)) = eta w (val (psi x))}.
  by move=> x w Ux Ww /=; rewrite -[val _]mul1r -(eta1 w Ww) -etaMpsi ?mul1r.
have etaRM w: w \in W1 -> rmorphism (eta w).
  move=> Ww; have nUw := subsetP nHbW1 _ (mem_quotient _ Ww).
  have etaD: additive (eta w).
    move=> a b; rewrite -[a]phi'K -[b]phi'K -!zmodMgE -!zmodVgE.
    rewrite -morphV // -morphM ?{1}etaK ?groupM ?groupV // conjMg conjVg.
    by rewrite morphM 1?morphV ?groupV // memJ_norm.
  do 2![split=> //] => [a b|]; last exact: eta1.
  rewrite -[a]outFK; have /envelop_mxP[d ->] := E_F a.
  rewrite raddf_sum mulr_suml ![eta w _](raddf_sum (Additive etaD)) mulr_suml.
  apply: eq_bigr => _ /morphimP[x Nx Ux ->]; move: {d}(d _) => dx.
  rewrite -[dx]natr_Zp scaler_nat !(mulrnAl, raddfMn); congr (_ *+ dx)%R.
  by rewrite -psiK //= outFK mulrC etaMpsi // mulrC psiJ.
have oF: #|F| = (p ^ q)%N by rewrite -cardsT -im_phi card_injm.
pose nF := <[1%R : F]>; have o_nF: #|nF| = p.
  by rewrite -orderE -phi_s (order_injm inj_phi) // (abelem_order_p abelHbar).
have cyc_uF := @field_unit_group_cyclic F.
exists F.
  exists phi; last first.
    split=> //; first exact/isomP; apply/esym/eqP; rewrite eqEcard o_nF -phi_s. 
    by rewrite (@cycle_subG F) mem_morphim //= card_injm ?subsetIl ?oW2b.
  exists psi => //; last first.
    by split=> // h x Hh Ux; rewrite qactJ (subsetP nH0U) ?phiJ.
  have inj_eta: 'injm (Morphism etaM).
    have /properP[_ [h Hh notW2h]]: W2bar \proper Hbar.
      by rewrite properEcard subsetIl oW2b oHb (ltn_exp2l 1) prime_gt1.
    apply/subsetP=> w /morphpreP[Ww /set1P/permP/(_ (phi h))].
    rewrite etaK // permE => /(injmP inj_phi) => chw.
    rewrite -(@prime_TIg _ W1 <[w]>) //; first by rewrite inE Ww cycle_id.
    rewrite proper_subn // properEneq cycle_subG Ww andbT.
    apply: contraNneq notW2h => defW1; rewrite inE Hh /= -defW1.
    rewrite quotient_cycle ?(subsetP nH0W1) // cent_cycle cent1C inE.
    by rewrite conjg_set1 chw ?memJ_norm // (subsetP nHbW1) ?mem_quotient.
  exists (Morphism etaM) => [alpha |]; last first.
    by split=> // h w Hh Ww /=; rewrite qactJ (subsetP nH0W1) -?etaK.
  pose autF (f : {perm F}) := rmorphism f. (* Bits of Galois theory... *)
  have [r prim_r]: {r : F | forall f g, autF f -> autF g -> f r = g r -> f = g}.
    have /cyclicP/sig_eqW[r def_uF] := cyc_uF [set: {unit F}]%G.
    exists (val r) => f g fRM gRM eq_fgr; apply/permP=> a.
    rewrite (_ : f =1 RMorphism fRM) // (_ : g =1 RMorphism gRM) //.
    have [-> | /in_uF_E <-] := eqVneq a 0%R; first by rewrite !rmorph0.
    have /cycleP[m ->]: in_uF a \in <[r]> by rewrite -def_uF inE.
    by rewrite val_unitX !rmorphX /= eq_fgr.
  have /sigW[P /and3P[Pr0 nP lePq]]:
    exists P: {poly F}, [&& root P r, all (mem nF) P & #|root P| <= q].
  - pose Mr := (\matrix_(i < q.+1) (sb *m outF (r ^+ i)))%R.
    have /rowV0Pn[v /sub_kermxP vMr0 nz_v]: kermx Mr != 0%R.
      rewrite kermx_eq0 neq_ltn ltnS (leq_trans (rank_leq_col Mr)) //.
      by rewrite (dim_abelemE abelHbar) // oHb pfactorK.
    pose P : {poly F} := (\poly_(i < q.+1) (v 0 (inord i))%:R)%R.
    have szP: size P <= q.+1 by apply: size_poly.
    exists P; apply/and3P; split.
    + apply/eqP/inj_phi'; congr (inHb _); rewrite rmorph0 mulmx0 -vMr0.
      rewrite horner_poly !raddf_sum mulmx_sum_row; apply: eq_bigr => i _.
      rewrite rowK inord_val //= mulr_natl rmorphMn -scaler_nat scalemxAr.
      by rewrite natr_Zp.
    + apply/(all_nthP 0%R)=> i /leq_trans/(_ szP) le_i_q.
      by rewrite coef_poly /= le_i_q mem_cycle.
    rewrite cardE -ltnS (leq_trans _ szP) //.
    rewrite max_poly_roots ?enum_uniq //; last first.
      by apply/allP=> r'; rewrite mem_enum.
    apply: contraNneq nz_v => /polyP P0; apply/eqP/rowP=> i; apply/eqP.
    have /eqP := P0 i; rewrite mxE coef0 coef_poly ltn_ord inord_val.
    have charF: p \in [char F]%R by rewrite !inE p_pr -order_dvdn -o_nF /=.
    by rewrite -(dvdn_charf charF) (dvdn_charf (char_Fp p_pr)) natr_Zp.
  have{Pr0 nP} fPr0 f: autF f -> root P (f r).
    move=> fRM; suff <-: map_poly (RMorphism fRM) P = P by apply: rmorph_root.
    apply/polyP=> i; rewrite coef_map.
    have [/(nth_default _)-> | lt_i_P] := leqP (size P) i; first exact: rmorph0.
    by have /cycleP[n ->] := all_nthP 0%R nP i lt_i_P; exact: rmorph_nat.
  apply: (iffP morphimP) => [[w _ Ww ->] | alphaRM]; first exact: etaRM.
  suffices /setP/(_ (alpha r)): [set (eta w) r | w in W1] = [set t | root P t].
    rewrite inE fPr0 // => /imsetP[w Ww def_wr]; exists w => //.
    by apply: prim_r => //; exact: etaRM.
  apply/eqP; rewrite eqEcard; apply/andP; split.
    by apply/subsetP=> _ /imsetP[w Ww ->]; rewrite inE fPr0 //; exact: etaRM.
  rewrite (@cardsE F) card_in_imset // => w1 w2 Ww1 Ww2 /= /prim_r eq_w12.
  by apply: (injmP inj_eta) => //; apply: eq_w12; exact: etaRM.
have isoUb: isog Ubar (psi @* U) by rewrite /Ubar -Kpsi first_isog.
pose unF := [set in_uF a | a in nF^#].
have unF_E: {in nF^#, cancel in_uF val} by move=> a /setD1P[/in_uF_E].
have unFg: group_set unF.
  apply/group_setP; split=> [|_ _ /imsetP[a nFa ->] /imsetP[b nFb ->]].
    have nF1: 1%R \in nF^# by rewrite !inE cycle_id oner_eq0.
    by apply/imsetP; exists 1%R => //; apply: val_inj; rewrite unF_E.
  have nFab: (a * b)%R \in nF^#.
    rewrite !inE mulf_eq0 negb_or.
    have [[-> /cycleP[m ->]] [-> /cycleP[n ->]]] := (setD1P nFa, setD1P nFb).
    by rewrite -natrM mem_cycle.
  by apply/imsetP; exists (a * b)%R => //; apply: val_inj; rewrite /= !unF_E.
have <-: #|Group unFg| = p.-1.
  by rewrite -o_nF (cardsD1 1 nF) group1 (card_in_imset (can_in_inj unF_E)).
have <-: #|[set: {unit F}]| = (p ^ q).-1.
  rewrite -oF -(cardC1 1) cardsT card_sub; apply: eq_card => a /=.
  by rewrite !inE unitfE.
rewrite /u (isog_cyclic isoUb) (card_isog isoUb) cyc_uF.
suffices co_u_p1: coprime #|psi @* U| #|Group unFg|.
  by rewrite -(Gauss_dvdr _ co_u_p1) mulnC divnK ?cardSg ?subsetT.
rewrite -(cyclic_dprod (dprodEY _ _)) ?cyc_uF //.
  by rewrite (sub_abelian_cent2 (cyclic_abelian (cyc_uF [set:_]%G))) ?subsetT.
apply/trivgP/subsetP=> _ /setIP[/morphimP[x Nx Ux ->] /imsetP[a nFa /eqP]].
have nCx: x \in 'N(C) by rewrite -Kpsi (subsetP (ker_norm _)).
rewrite -val_eqE (unF_E a) //; case/setD1P: nFa => _ /cycleP[n {a}->].
rewrite zmodXgE => /eqP def_psi_x; rewrite mker ?set11 // Kpsi coset_idr //.
apply/set1P; rewrite -set1gE -(Frobenius_trivg_cent frobUW1c) /= -/C.
rewrite inE mem_quotient //= -sub1set -quotient_set1 ?quotient_cents2r //.
rewrite gen_subG /= -/C -Kpsi; apply/subsetP=> _ /imset2P[_ w /set1P-> Ww ->].
have Uxw: x ^ w \in U by rewrite memJ_norm ?(subsetP nUW1).
apply/kerP; rewrite (morphM, groupM) ?morphV ?groupV //.
apply/(canLR (mulKg _))/val_inj; rewrite psiJ // mulg1 def_psi_x.
exact: (rmorph_nat (RMorphism (etaRM w Ww))).
Qed.

Local Open Scope ring_scope.

Let redM := [predC irr M].
Let mu_ := filter redM (S_ H0).

(* This subproof is shared between (9.8)(b) and (9.9)(b). *)
Let nb_redM_H0 : size mu_ = p.-1 /\ {subset mu_ <= S_ H0C}.
Proof.
have pddM := FT_prDade_hypF maxM MtypeP; pose ptiWM := prDade_prTI pddM.
have [nsHUM sW1M /mulG_sub[sHUM _] nHUW1 tiHUW1] := sdprod_context defM.
have [nsHHU sUHU /mulG_sub[sHHU _] nHU tiHU] := sdprod_context defHU.
have nb_redM K:
  K <| M -> K \subset HU -> K :&: H = H0 -> count redM (S_ K) = p.-1.
- move=> nsKM sKHU tiKHbar; have [sKM nKM] := andP nsKM; pose b L := (L / K)%G.
  have [nsKHU [_ [_ sW2HU cycW2 _] _]] := (normalS sKHU sHUM nsKM, ptiWM).
  have nKW2 := subset_trans sW2HU (normal_norm nsKHU).
  have oW2b: #|b W2| = p.
    have [_ <- _] := Ptype_Fcore_factor_facts; rewrite defW2bar.
    rewrite !card_quotient ?(subset_trans (subset_trans sW2HU sHUM)) //.
    by rewrite -indexgI -{2}(setIidPl sW2H) setIAC -setIA tiKHbar indexgI.
  have{cycW2} cycW2b: cyclic (b W2) by apply: quotient_cyclic.
  have ntW2b: (W2 / K != 1)%g by rewrite -cardG_gt1 oW2b prime_gt1.
  have{ntW2b} [defWb ptiWMb]:= primeTIhyp_quotient ptiWM ntW2b sKHU nsKM.
  pose muK j := (primeTIred ptiWMb j %% K)%CF.
  apply/eqP; have <-: size (image muK (predC1 0)) = p.-1.
    by rewrite size_map -cardE cardC1 card_Iirr_cyclic ?oW2b.
  rewrite -size_filter -uniq_size_uniq ?filter_uniq ?seqInd_uniq // => [|phi].
    by apply/dinjectiveP=> j1 j2 _ _ /(can_inj (cfModK nsKM))/prTIred_inj.
  rewrite mem_filter; apply/imageP/andP=> [[j nz_j ->] | [red_phi]]; last first.
    case/seqIndP=> s /setDP[kerK ker'H] Dphi; rewrite !inE in kerK ker'H.
    pose s1 := quo_Iirr K s; have Ds: s = mod_Iirr s1 by rewrite quo_IirrK.
    rewrite {phi}Dphi Ds mod_IirrE ?cfIndMod // in kerK ker'H red_phi *.
    have [[j Ds1] | [/idPn[]]] := prTIres_irr_cases ptiWMb s1.
      rewrite Ds1 cfInd_prTIres -/(muK j) in ker'H *; exists j => //.
      by apply: contraNneq ker'H => ->; rewrite prTIres0 rmorph1 cfker_cfun1.
    by apply: contra red_phi => /cfMod_irr/= ->.
  have red_j: redM (muK j).
    apply: contra (prTIred_not_irr ptiWMb j) => /(cfQuo_irr nsKM).
    by rewrite cfker_mod ?cfModK // => ->.
  have [s DmuKj]: exists s, muK j = 'Ind[M, HU] 'chi_s.
    exists (mod_Iirr (primeTI_Ires ptiWMb j)).
    by rewrite mod_IirrE // cfIndMod // cfInd_prTIres.
  split=> //; apply/seqIndP; exists s; rewrite // !inE andbC.
  rewrite -(@sub_cfker_Ind_irr _ M) ?gFnorm // -DmuKj cfker_mod //=.
  have [[j1 Ds] | [/idPn]] := prTIres_irr_cases ptiWM s; last by rewrite -DmuKj.
  rewrite Ds cfker_prTIres //; apply: contraNneq nz_j => j1_0.
  apply/eqP/(prTIred_inj ptiWMb)/(can_inj (cfModK nsKM)); rewrite -{1}/(muK j).
  by rewrite DmuKj Ds j1_0 -cfInd_prTIres !prTIres0 -cfIndMod ?rmorph1.
have [sH0HU sH0M] := (subset_trans sH0H sHHU, subset_trans sH0H (gFsub _ _)).
have sz_mu: size mu_ = p.-1.
  by rewrite size_filter nb_redM ?(setIidPl sH0H) // /normal sH0M.
have s_muC_mu: {subset filter redM (S_ H0C) <= mu_}.
  move=> phi; rewrite /= !mem_filter => /andP[->]; apply: seqIndS.
  by rewrite setSD // Iirr_kerS ?joing_subl.
have UmuC: uniq (filter redM (S_ H0C)) by rewrite filter_uniq ?seqInd_uniq.
have [|Dmu _] := leq_size_perm UmuC s_muC_mu; last first.
  by split=> // phi; rewrite -Dmu mem_filter => /andP[].
have [nsH0C_M _ _ _] := nsH0xx_M.
have sCHU := subset_trans sCU sUHU; have sCM := subset_trans sCHU sHUM.
have sHOC_HU: H0C \subset HU by apply/joing_subP.
rewrite sz_mu size_filter nb_redM //= norm_joinEr ?(subset_trans sCM) //.
by rewrite -group_modl //= setIC [C]unlock setIA tiHU setI1g mulg1.
Qed.

Let isIndHC (zeta : 'CF(M)) :=
  [/\ zeta 1%g = (q * u)%:R, zeta \in S_ H0C
    & exists2 xi : 'CF(HC), xi \is a linear_char & zeta = 'Ind xi].

(* This is Peterfalvi (9.8). *)
Lemma typeP_nonGalois_characters (not_Galois : ~~ typeP_Galois) :
    let a := #|U : 'C_U(sval (typeP_Galois_Pn not_Galois) | 'Q)| in
  [/\ (*a*) {in X_ H0, forall s, (a %| 'chi_s 1%g)%C},
      (*b*) size mu_ = p.-1 /\ {in mu_, forall mu_j, isIndHC mu_j},
      (*c*) exists t, isIndHC 'chi_t
    & (*d*) let irr_qa := [pred zeta in irr M | zeta 1%g == (q * a)%:R] in
            let lb_n := (p.-1 * #|U|)%N in let lb_d := (a ^ 2 * #|U'|)%N in
            (lb_d %| lb_n /\ lb_n %/ lb_d <= count irr_qa (S_ H0U'))%N].
Proof.
case: (typeP_Galois_Pn _) => H1 [oH1 nH1U nH1Uq defHbar aP]; rewrite [sval _]/=.
move => a; case: aP; rewrite -/a => a_gt1 a_dv_p1 cycUb1 isoUb.
set part_a := ({in _, _}); pose HCbar := (HC / H0)%G.
have [_ /mulG_sub[sHUM sW1M] nHUW1 tiHUW1] := sdprodP defM.
have [nsHHU _ /mulG_sub[sHHU sUHU] nHU tiHU] := sdprod_context defHU.
have [nH0H nHHU] := (normal_norm nsH0H, normal_norm nsHHU).
have sHHC: H \subset HC by rewrite joing_subl.
have [nH0HU sCHU] := (subset_trans sHUM nH0M, subset_trans sCU sUHU).
have nsH0_HU: H0 <| HU by rewrite /normal (subset_trans sH0H).
have nH0C := subset_trans sCHU nH0HU.
have [nsH0C_M nsHC_M nsH0U'_M _] := nsH0xx_M; have [sHC_M _] := andP nsHC_M.
have nsH0HC: H0 <| HC := normalS (subset_trans sH0H sHHC) sHC_M nsH0M.
have defHCbar: Hbar \x (C / H0) = HCbar.
  rewrite /= quotientY // [C]unlock /= astabQ quotient_setIpre.
  by rewrite dprodEY ?subsetIr // setIA -quotientGI // tiHU quotient1 setI1g.
have sHC_HU: HC \subset HU by rewrite join_subG sHHU.
have nsHC_HU: HC <| HU := normalS sHC_HU sHUM nsHC_M.
have defHb1 := defHbar; rewrite (big_setD1 1%g) ?group1 ?conjsg1 //= in defHb1.
have [[_ H1c _ defH1c] _ _ _] := dprodP defHb1; rewrite defH1c in defHb1.
have [nsH1H _] := dprod_normal2 defHb1; have [sH1H nH1H] := andP nsH1H.
have nHW1: W1 \subset 'N(H) := subset_trans sW1M (gFnorm _ _).
have nHbW1: W1bar \subset 'N(Hbar) by rewrite quotient_norms.
have sH1wH w: w \in W1bar -> H1 :^ w \subset Hbar.
  by move/(normsP nHbW1) <-; rewrite conjSg.
have nsH1wHUb w: w \in W1bar -> H1 :^ w <| HU / H0.
  move=> W1w; rewrite -(normsP (quotient_norms _ nHUW1) w W1w) normalJ.
  rewrite /normal (subset_trans sH1H) ?quotientS //.
  by rewrite -defHU sdprodE // quotientMl // mulG_subG nH1H.
have nH1wHUb := normal_norm (nsH1wHUb _ _).
have Part_a: part_a.
  move=> s; rewrite !inE => /andP[kers'H kersH0].
  have [t sHt] := constt_cfRes_irr H s; pose theta := ('chi_t / H0)%CF.
  have{kers'H} t_neq0: t != 0.
    by rewrite -subGcfker (sub_cfker_constt_Res_irr sHt).
  have{kersH0} kertH0: H0 \subset cfker 'chi_t.
    by rewrite (sub_cfker_constt_Res_irr sHt).
  have Ltheta: theta \is a linear_char.
    by rewrite /theta -quo_IirrE // (char_abelianP _ _). 
  have Dtheta : _ = theta := cfBigdprod_Res_lin defHbar Ltheta.
  set T := 'I_HU['chi_t]; have sHT: H \subset T by rewrite sub_Inertia.
  have sTHU: T \subset HU by rewrite Inertia_sub.
  suffices{s sHt} a_dv_iTHU: a %| #|HU : T|.
    have [_ defInd_t _ imInd_t _] := cfInd_sum_Inertia t nsHHU.
    have /imsetP[r tTr ->]: s \in Ind_Iirr HU @: irr_constt ('Ind[T] 'chi_t).
      by rewrite imInd_t constt_Ind_Res.
    by rewrite defInd_t ?cfInd1 // dvdC_mulr ?dvdC_nat // Cint_Cnat ?Cnat_irr1.
  have /exists_inP[w W1w nt_t_w]: [exists w in W1bar, 'Res[H1 :^ w] theta != 1].
    rewrite -negb_forall_in; apply: contra t_neq0 => /forall_inP=> tH1w1.
    rewrite -irr_eq1 -(cfQuoK nsH0H kertH0) -/theta -Dtheta.
    rewrite [cfBigdprod _ _]big1 ?rmorph1 // => w /tH1w1/eqP->.
    by rewrite /cfBigdprodi rmorph1.
  have defT: H ><| (U :&: T) = T.
    by rewrite (sdprod_modl defHU) // (setIidPr sTHU).
  have /irrP[k Dk]: 'Res theta \in irr (H1 :^ w).
    by rewrite lin_char_irr ?cfRes_lin_char.
  rewrite -divgS // -(sdprod_card defHU) -(sdprod_card defT) divnMl // divgI.
  rewrite -indexgI; have ->: a = #|U : 'C_U(H1 :^ w | 'Q)|.
    have [w1 nH0w1 W1w1 ->] := morphimP W1w; rewrite astabQ centJ morphpreJ //.
    by rewrite -astabQ indexgI -(normsP nUW1 _ W1w1) indexJg -indexgI.
  rewrite indexgS ?setIS // sub_astabQ ?(subset_trans sTHU) //= -inertia_quo //.
  apply: subset_trans (sub_inertia_Res _ (nH1wHUb w W1w)) _.
  by rewrite Dk (inertia_irr_prime _ p_pr) ?subsetIr ?cardJg // -irr_eq1 -Dk.
pose isoJ := conj_isom H1; pose cfJ w i := 'chi_(isom_Iirr (isoJ w) i).
pose thetaH (f : {ffun _}) := cfBigdprod defHbar (fun w => cfJ w (f w)).
pose theta f := cfDprodl defHCbar (thetaH f).
have abH1: abelian H1 by rewrite cyclic_abelian ?prime_cyclic ?oH1.
have linH1 i: 'chi[H1]_i \is a linear_char by apply/char_abelianP.
have lin_thetaH f: thetaH f \is a linear_char.
  by apply: cfBigdprod_lin_char => w _; rewrite /cfJ isom_IirrE cfIsom_lin_char.
have nz_thetaH f: thetaH f 1%g != 0 by rewrite lin_char_neq0.
have Dtheta f: {in W1bar & H1, forall w xb, theta f (xb ^ w) = 'chi_(f w) xb}.
  move=> w xb W1w H1xb /=; have sHHCb := quotientS H0 sHHC.
  transitivity ('Res[H1 :^ w] ('Res[Hbar] (theta f)) (xb ^ w)); last first.
    by rewrite cfDprodlK cfBigdprodKabelian // isom_IirrE cfIsomE.
  by rewrite cfResRes ?sH1wH // cfResE ?memJ_conjg ?(subset_trans (sH1wH w _)).
have lin_theta f: theta f \is a linear_char by apply: cfDprodl_lin_char.
pose Ftheta := pffun_on (0 : Iirr H1) W1bar (predC1 0).
have inj_theta: {in Ftheta &, injective theta}.
  move=> f1 f2 /pffun_onP[/supportP W1f1 _] /pffun_onP[/supportP W1f2 _] eq_f12.
  apply/ffunP=> w.
  have [W1w | W1'w] := boolP (w \in W1bar); last by rewrite W1f1 ?W1f2.
  by apply/irr_inj/cfun_inP=> x H1x; rewrite -!Dtheta ?eq_f12.
have irr_thetaH0 f: (theta f %% H0)%CF \in irr HC.
  by rewrite cfMod_irr ?lin_char_irr.
have def_Itheta f: f \in Ftheta -> 'I_HU[theta f %% H0]%CF = HC.
  case/pffun_onP=> _ nz_fW1; apply/eqP; rewrite eqEsubset sub_Inertia //.
  rewrite inertia_mod_pre //= -{1}(sdprodW defHU) -group_modl; last first.
    rewrite (subset_trans sHHC) // -sub_quotient_pre ?normal_norm //.
    by rewrite sub_Inertia ?quotientS.
  rewrite -gen_subG genM_join genS ?setUS //= {2}[C]unlock setIS //= astabQ.
  rewrite morphpreS // centsC -{1}(bigdprodWY defHbar) gen_subG.
  apply/bigcupsP=> w W1w; rewrite centsC.
  apply: subset_trans (sub_inertia_Res _ (quotient_norms _ nHHU)) _.
  rewrite cfDprodlK inertia_bigdprod_irr // subIset // orbC (bigcap_min w) //.
  rewrite (inertia_irr_prime _ p_pr) ?cardJg ?subsetIr // isom_Iirr_eq0.
  by apply: nz_fW1; apply: image_f.
have irrXtheta f: f \in Ftheta -> 'Ind (theta f %% H0)%CF \in irr HU.
  move/def_Itheta; rewrite -(cfIirrE (irr_thetaH0 f)) => I_f_HC.
  by rewrite inertia_Ind_irr ?I_f_HC //.
pose Mtheta := [set cfIirr (theta f %% H0)%CF | f in Ftheta].
pose Xtheta := [set cfIirr ('Ind[HU] 'chi_t) | t in Mtheta].
have oXtheta: (u * #|Xtheta| = p.-1 ^ q)%N.
  transitivity #|Ftheta|; last first.
    rewrite card_pffun_on cardC1 card_Iirr_abelian // oH1.
    rewrite -(card_isog (quotient_isog _ _)) ?oW1 ?(subset_trans sW1M) //.
    by apply/trivgP; rewrite -tiHUW1 setSI ?(subset_trans sH0H).
  rewrite Du -card_imset_Ind_irr ?card_in_imset //.
  - move=> f1 f2 Df1 Df2 /(congr1 (tnth (irr HC))); rewrite !{1}cfIirrE //.
    by move/(can_inj (cfModK nsH0HC)); apply: inj_theta.
  - by move=> _ /imsetP[f Df ->]; rewrite cfIirrE ?irrXtheta.
  move=> _ y /imsetP[f /familyP Ff ->] HUy; apply/imsetP.
  pose yb := inMb y; have HUyb: yb \in (HU / H0)%g by apply: mem_quotient.
  have nHb_y: inMb y \in 'N(Hbar) by rewrite (subsetP (quotient_norms _ nHHU)).
  have nH1b_y := subsetP (nH1wHUb _ _) yb HUyb.
  exists [ffun w => conjg_Iirr (f w) (inMb y ^ w^-1)].
    apply/familyP=> w; rewrite ffunE.
    by case: ifP (Ff w) => _; rewrite !inE conjg_Iirr_eq0.
  apply: irr_inj; rewrite !(cfIirrE, conjg_IirrE) // (cfConjgMod _ nsHC_HU) //.
  rewrite cfConjgDprodl //; first congr (cfDprodl _ _ %% H0)%CF; last first.
    rewrite /= -quotientYidl // (subsetP _ _ HUyb) ?quotient_norms //.
    by rewrite (subset_trans sHUM) ?normal_norm.
  rewrite cfConjgBigdprod //; apply: eq_bigr => w W1w; congr (cfBigdprodi _ _).
  rewrite ffunE /cfJ !isom_IirrE conjg_IirrE.
  apply/cfun_inP=> _ /imsetP[x Hx ->]; rewrite cfIsomE // cfConjgE ?nH1b_y //.
  rewrite -conjgM conjgCV conjVg conjgM cfIsomE //; last first.
    by rewrite -mem_conjg (normP _) // -mem_conjg -normJ ?nH1b_y.
  by rewrite cfConjgE // -mem_conjg -normJ ?nH1b_y.
have sXthXH0C: Xtheta \subset X_ H0C.
  apply/subsetP=> _ /imsetP[t Mt ->]; have{Mt} [f Ff Dt] := imsetP Mt.
  rewrite !inE cfIirrE; last by rewrite Dt cfIirrE ?irrXtheta.
  rewrite !sub_cfker_Ind_irr ?(subset_trans sHUM) ?normal_norm ?gFnormal //.
  rewrite {t}Dt cfIirrE // join_subG andbCA {1}cfker_mod //.
  rewrite !{1}sub_cfker_mod //= andbC {1}cfker_sdprod /=.
  apply: contraL (familyP Ff 1%g) => kerHb; rewrite group1 negbK.
  have:= sub_cfker_Res (subxx _) kerHb; rewrite cfDprodlK.
  move/(subset_trans (sH1wH _ (group1 _)))/(sub_cfker_Res (subxx _)).
  rewrite cfBigdprodKabelian // isom_IirrE cfker_isom morphim_conj /=.
  by rewrite !conjsg1 subsetIidl subGcfker.
pose mu_f (i : Iirr H1) := [ffun w => if w \in W1bar then i else 0].
have Fmu_f (i : Iirr H1): i != 0 -> mu_f i \in Ftheta.
  by move=> nz_i; apply/familyP=> w; rewrite ffunE; case: ifP; rewrite !inE.
pose mk_mu i := 'Ind[HU] (theta (mu_f i) %% H0)%CF.
have sW1_Imu i: W1 \subset 'I[theta (mu_f i) %% H0]%CF.
  apply/subsetP=> w W1w; have Mw := subsetP sW1M w W1w.
  have nHC_W1 := subset_trans sW1M (normal_norm nsHC_M).
  rewrite inE (subsetP nHC_W1) ?(cfConjgMod _ nsHC_M) //; apply/eqP.
  have W1wb: inMb w \in W1bar by rewrite mem_quotient.
  rewrite cfConjgDprodl ?(subsetP _ _ W1wb) ?quotient_norms //; last first.
    by rewrite (subset_trans (joing_subr U W1)) ?normal_norm.
  congr (cfDprodl _ _ %% H0)%CF.
  apply/cfun_inP=> _ /(mem_bigdprod defHbar)[x [H1x -> _]].
  have Hx w1: w1 \in W1bar -> x w1 \in Hbar.
    by move=> W1w1; rewrite (subsetP (sH1wH w1 _)) ?H1x.
  rewrite !lin_char_prod ?cfConjg_lin_char //; apply/eq_bigr=> w1 W1w1.
  rewrite cfConjgE ?(subsetP nHbW1) //.
  have W1w1w: (w1 * (inMb w)^-1)%g \in W1bar by rewrite !in_group.
  rewrite -(cfResE _ (sH1wH _ W1w1w)) -?mem_conjg -?conjsgM ?mulgKV ?H1x //.
  rewrite -(cfResE _ (sH1wH _ W1w1)) ?H1x ?cfBigdprodKabelian //.
  rewrite !ffunE W1w1 W1w1w -[x w1](conjgKV w1) -conjgM !isom_IirrE.
  by rewrite !cfIsomE -?mem_conjg ?H1x.
have inj_mu: {in predC1 0 &, injective (fun i => cfIirr (mk_mu i))}.
  move=> i1 i2 nz_i1 nz_i2 /(congr1 (tnth (irr HU))).
  rewrite !{1}cfIirrE ?irrXtheta ?Fmu_f // /mk_mu.
  do 2![move/esym; rewrite -{1}(cfIirrE (irr_thetaH0 _))].
  move/(cfclass_Ind_irrP _ _ nsHC_HU); rewrite !{1}cfIirrE //.
  case/cfclassP=> _ /(mem_sdprod defHU)[x [y [Hx Uy -> _]]].
  rewrite (cfConjgM _ nsHC_HU) ?(subsetP sHHU x) ?(subsetP sUHU) //.
  rewrite {x Hx}(cfConjg_id _ (subsetP sHHC x Hx)) => Dth1.
  suffices /setIP[_ /inertiaJ]: y \in 'I_HU[theta (mu_f i2) %% H0]%CF.
    rewrite -Dth1 => /(can_inj (cfModK nsH0HC))/inj_theta/ffunP/(_ 1%g).
    by rewrite !ffunE group1 => -> //; apply: Fmu_f.
  rewrite def_Itheta ?Fmu_f //= (subsetP (joing_subr _ _)) //.
  have nCy: y \in 'N(C).
    by rewrite (subsetP (normal_norm nsCUW1)) ?mem_gen ?inE ?Uy.
  have [_ _ /trivgPn[wb W1wb ntwb] _ _] := Frobenius_context frobUW1c.
  have /morphimP[w nCw W1w Dw] := W1wb; have Mw := subsetP sW1M w W1w.
  rewrite coset_idr //; apply/set1P; rewrite -set1gE; apply: wlog_neg => nty.
  rewrite -((Frobenius_reg_ker frobUW1c) wb); last by rewrite !inE ntwb.
  rewrite inE mem_quotient //=; apply/cent1P/commgP.
  rewrite Dw -morphR //= coset_id //.
  suffices: [~ y, w] \in U :&: HC.
    rewrite /= norm_joinEr ?(subset_trans sCU) // -group_modr ?subsetIl //=.
    by rewrite setIC tiHU mul1g.
  have Uyw: [~ y, w] \in U; last rewrite inE Uyw.
    by rewrite {1}commgEl groupMl ?groupV // memJ_norm ?(subsetP nUW1) // Uy.
  rewrite -(def_Itheta _ (Fmu_f _ nz_i1)) 2!inE /= andbA -in_setI.
  rewrite (setIidPl (normal_norm nsHC_HU)) (subsetP sUHU) //=.
  rewrite Dth1 -(cfConjgM _ nsHC_HU) ?(subsetP sUHU) //.
  have My: y \in M := subsetP (subset_trans sUHU sHUM) y Uy.
  rewrite mulKVg (cfConjgM _ nsHC_M) ?in_group //.
  have /inertiaJ-> := subsetP (sW1_Imu i2) _ (groupVr W1w).
  rewrite (cfConjgM _ nsHC_M) // -Dth1.
  by have /inertiaJ-> := subsetP (sW1_Imu i1) w W1w.
pose Xmu := [set cfIirr (mk_mu i) | i in predC1 0].
have def_IXmu: {in Xmu, forall s, 'I_M['chi_s] = M}.
  move=> _ /imsetP[i nz_i ->]; apply/setIidPl.
  rewrite -subsetIidl -{1}(sdprodW defM) mulG_subG sub_Inertia //.
  rewrite !cfIirrE ?irrXtheta ?Fmu_f //=.
  apply: subset_trans (sub_inertia_Ind _ (der_norm 1 M)).
  by rewrite subsetI sW1M /=.
pose Smu := [seq 'Ind[M] 'chi_s | s in Xmu].
have sSmu_mu: {subset Smu <= mu_}.
  move=> _ /imageP[s Xmu_s ->]; rewrite mem_filter /=.
  rewrite irrEchar cfnorm_Ind_irr ?gFnormal // def_IXmu //.
  rewrite -(index_sdprod defM) (eqC_nat _ 1) gtn_eqF ?prime_gt1 // andbF.
  rewrite mem_seqInd ?gFnormal /normal ?(subset_trans sH0H) ?gFsub //=.
  suffices /(subsetP sXthXH0C): s \in Xtheta.
    by apply: subsetP; rewrite setSD // Iirr_kerS ?joing_subl.
  have /imsetP[i nz_i ->] := Xmu_s; rewrite /Xtheta -imset_comp.
  by apply/imsetP; exists (mu_f i); rewrite /= ?cfIirrE ?Fmu_f.
have ResIndXmu: {in Xmu, forall s, 'Res ('Ind[M] 'chi_s) = q%:R *: 'chi_s}.
  move=> s /def_IXmu Imu_s; rewrite cfResInd_sum_cfclass ?gFnormal ?Imu_s //.
  by rewrite -(index_sdprod defM) -Imu_s cfclass_inertia big_seq1.
have uSmu: uniq Smu.
  apply/dinjectiveP=> s1 s2 Xs1 Xs2 /(congr1 'Res[HU]); rewrite !ResIndXmu //.
  by move/(can_inj (scalerK (neq0CG W1)))/irr_inj.
have sz_Smu: size Smu = p.-1.
  by rewrite size_map -cardE card_in_imset // cardC1 card_Iirr_abelian ?oH1.
have [sz_mu s_mu_H0C] := nb_redM_H0.
have Dmu: Smu =i mu_.
  by have [|//] := leq_size_perm uSmu sSmu_mu; rewrite sz_mu sz_Smu.
split=> {Part_a part_a}//.
- split=> // phi mu_phi; have S_HOC_phi := s_mu_H0C _ mu_phi.
  move: mu_phi; rewrite -Dmu => /imageP[_ /imsetP[i nz_i ->]].
  rewrite cfIirrE ?irrXtheta ?Fmu_f // => Dphi.
  split=> //; rewrite Dphi ?cfInd1 ?cfIndInd //.
    rewrite -(index_sdprod defM) -/q -Du mulrA -natrM.
    by rewrite lin_char1 1?cfMod_lin_char ?mulr1.
  by exists (theta (mu_f i) %% H0)%CF; rewrite 1?cfMod_lin_char.
- have /eqVproper: Xmu \subset Xtheta.
    apply/subsetP=> _ /imsetP[i nz_i ->]; rewrite -[Xtheta]imset_comp /=.
    by apply/imsetP; exists (mu_f i); rewrite /= ?cfIirrE ?Fmu_f.
  case=> [defXmu | /andP[_ /subsetPn[s theta_s Xmu'_s]]]; last first.
    have [_ /imsetP[f Dth_f ->] Ds] := imsetP theta_s; rewrite cfIirrE // in Ds.
    have /irrP[t Dt]: 'Ind 'chi_s \in irr M; last 1 [exists t; rewrite -{t}Dt].
      apply: contraR Xmu'_s => red_Ind_s.
      have: 'Ind 'chi_s \in mu_.
        rewrite mem_filter /= red_Ind_s mem_seqInd ?gFnormal //=.
        apply: subsetP theta_s; rewrite (subset_trans  sXthXH0C) ?setSD //.
        by rewrite Iirr_kerS ?joing_subl.
      rewrite -Dmu => /imageP[s1 Xmu_s1] /(congr1 (cfdot ('Ind 'chi_s1)))/eqP.
      rewrite cfnorm_Ind_irr ?gFnormal // eq_sym -cfdot_Res_l.
      rewrite ResIndXmu // cfdotZl cfdot_irr -natrM mulnC.
      by case: (s1 =P s) => [<- // | _] /idPn[]; apply: neq0CiG.
    split; first 2 [by rewrite mem_seqInd ?gFnormal ?(subsetP sXthXH0C)].
      rewrite Ds cfIirrE ?irrXtheta ?cfInd1 // -Du -(index_sdprod defM) -/q.
      by rewrite mulrA -natrM lin_char1 ?cfMod_lin_char ?mulr1.
    exists (theta f %% H0)%CF; first by rewrite cfMod_lin_char.
    by rewrite Ds  cfIirrE ?irrXtheta //= cfIndInd.
  suffices /(congr1 odd): u = (p.-1 ^ q.-1)%N.
    rewrite odd_exp -(subnKC (prime_gt1 pr_q)) /= -subn1 odd_sub ?prime_gt0 //.
    by rewrite -oH1 (oddSg sH1H) ?quotient_odd // mFT_odd.
  have p1_gt0: (0 < p.-1)%N by rewrite -(subnKC (prime_gt1 p_pr)).
  apply/eqP; rewrite -(eqn_pmul2r p1_gt0) -expnSr prednK ?prime_gt0 //. 
  by rewrite -oXtheta -defXmu card_in_imset // cardC1 card_Iirr_abelian ?oH1.
clear Xmu def_IXmu Smu sSmu_mu ResIndXmu uSmu sz_Smu sz_mu s_mu_H0C Dmu.
clear Mtheta Xtheta irrXtheta oXtheta sXthXH0C mu_f Fmu_f mk_mu sW1_Imu inj_mu.
clear nz_thetaH lin_thetaH lin_theta Ftheta inj_theta irr_thetaH0 def_Itheta. 
clear theta Dtheta => irr_qa lb_n lb_d.
have sU'U: U' \subset U := der_sub 1 U.
have nH0U := subset_trans sUHU nH0HU; have nH0U' := subset_trans sU'U nH0U.
have sU'CH1: U' \subset 'C_U(H1 | 'Q).
  by rewrite subsetI sU'U sub_astabQ nH0U' (centsS sH1H) ?quotient_cents.
have sCH1_U: 'C_U(H1 | 'Q) \subset U := subsetIl U _.
have dvd_lb: lb_d %| lb_n.
  rewrite -[lb_d]mulnA dvdn_mul // -(Lagrange sCH1_U).
  by rewrite mulnC dvdn_pmul2r ?cardSg ?indexg_gt0.
split; rewrite ?leq_divLR // /lb_n -(Lagrange sCH1_U) -/a -(Lagrange sU'CH1).
rewrite mulnCA -mulnA mulnC !mulnA !leq_pmul2r ?cardG_gt0 ?indexg_gt0 // mulnC.
pose H1CH1 := (H1 <*> 'C_(U / H0)(H1))%G; pose HCH1 := (H <*> 'C_U(H1 | 'Q))%G.
have defH1CH1: H1 \x 'C_(U / H0)(H1) = H1CH1.
  rewrite dprodEY ?subsetIr ?coprime_TIg ?(coprimeSg sH1H) //.
  by rewrite (coprimegS (subsetIl _ _)) ?coprime_morph.
have sHCH1_HU: HCH1 \subset HU by rewrite join_subG sHHU (subset_trans sCH1_U).
have nsHCH1_HU: HCH1 <| HU.
  rewrite /normal sHCH1_HU -(sdprodW defHU) mulG_subG normsG ?joing_subl //=.
  by rewrite normsY // sub_der1_norm.
have nsH0_HCH1: H0 <| HCH1.
  by rewrite (normalS _ sHCH1_HU) // (subset_trans sH0H) ?joing_subl.
have nsH1cHU: H1c <| HU / H0.
  rewrite -(bigdprodWY defH1c) /normal gen_subG norms_gen ?andbT //.
    by apply/bigcupsP=> w /setD1P[_ /nsH1wHUb/andP[]].
  by apply/norms_bigcup/bigcapsP=> w /setD1P[_ /nH1wHUb].
have defHCH1: H1c ><| H1CH1 = (HCH1 / H0)%G.
  have /sdprodP[_ /mulG_sub[sH1cH _] nH1cH1 tiH1cH1] := dprodWsdC defHb1.
  rewrite sdprodE /= -(dprodW defH1CH1).
  - rewrite mulgA (dprodWC defHb1) -morphim_setIpre -astabQ -quotientMl //.
    by rewrite norm_joinEr // (subset_trans sCH1_U).
  - rewrite mul_subG ?subIset // (subset_trans (quotientS _ sUHU)) //.
    exact: normal_norm nsH1cHU.
  rewrite -(setIidPl sH1cH) setIAC -setIA -group_modl // coprime_TIg ?mulg1 //.
  by rewrite coprime_sym (coprimegS (subsetIl _ _)) ?coprime_morph.
have [nsH1cHCH1 sH1CH1_HCH1 _ nH1cH1C _] := sdprod_context defHCH1.
pose Clam := ('C_(U / H0)(H1) / (U' / H0))%G.
pose lam (j : Iirr Clam) := 'chi_(mod_Iirr j).
pose theta i j := cfSdprod defHCH1 (cfDprod defH1CH1 'chi_i (lam j)).
have nsU'CH1: U' <| 'C_U(H1 | 'Q) by rewrite (normalS _ sCH1_U) ?gFnormal.
have nsU'CH1b: U' / H0 <| 'C_(U / H0)(H1).
  by rewrite -morphim_setIpre -astabQ quotient_normal.
have abClam: abelian Clam.
  by rewrite sub_der1_abelian //= quotient_der ?dergS ?subsetIl.
have lam_lin j: lam j \is a linear_char.
  by rewrite /lam mod_IirrE ?cfMod_lin_char //; apply/char_abelianP.
have theta_lin i j: theta i j \is a linear_char.
  by rewrite cfSdprod_lin_char ?cfDprod_lin_char.
have <-: #|Clam| = #|'C_U(H1 | 'Q) : U'|.
  rewrite -card_quotient ?normal_norm //= /= -morphim_setIpre -astabQ.
  have nsU'U : U' <| U by apply: der_normal.
  rewrite -(restrmEsub _ _ sCH1_U) -(restrm_quotientE _ sU'U) -morphim_quotm.
  rewrite card_injm ?quotientS ?injm_quotm ?(isom_inj (quotient_isom _ _)) //.
  by rewrite coprime_TIg ?(coprimeSg sH0H).
pose Mtheta := [set mod_Iirr (cfIirr (theta i j)) | i in [set~ 0], j in setT].
have ->: (p.-1 * #|Clam|)%N = #|Mtheta|.
  rewrite [Mtheta]curry_imset2X card_imset ?cardsX => [|[i1 j1] [i2 j2] /=/eqP].
    by rewrite cardsC1 cardsT !card_Iirr_abelian ?(abelianS sH1H) ?oH1.
  rewrite (can_eq (mod_IirrK _)) // -(inj_eq irr_inj) !cfIirrE ?lin_char_irr //.
  rewrite (can_eq (cfSdprodK _)) -!dprod_IirrE (inj_eq irr_inj).
  by rewrite (can_eq (dprod_IirrK _)) => /eqP[->] /(can_inj (mod_IirrK _))->.
have{lam_lin} thetaH1 i j: 'Res[H1] (theta i j) = 'chi_i.
  rewrite -(cfResRes _ _ sH1CH1_HCH1) ?joing_subl // cfSdprodK cfDprodKl //.
  exact: lin_char1.
have Itheta r: r \in Mtheta -> 'I_HU['chi_r]%CF = HCH1.
  case/imset2P=> i j; rewrite /= in_setC1 => nz_i _ Dr; apply/eqP.
  rewrite eqEsubset sub_Inertia //= Dr mod_IirrE // cfIirrE ?lin_char_irr //.
  rewrite andbT -(quotientSGK _ (normal_sub nsH0_HCH1)) ?subIset ?nH0HU //. 
  rewrite inertia_mod_quo //.
  apply: subset_trans (sub_inertia_Res _ (nH1wHUb _ (group1 _))) _.
  rewrite /= conjsg1 thetaH1 (inertia_irr_prime _ p_pr) //.
  rewrite -quotient_setIpre -astabQ quotientS // -{1}(sdprodW defHU).
  by rewrite -genM_join sub_gen // group_modl // sub_astabQ nH0H (centsS sH1H).
have irr_Xtheta: {in Mtheta, forall r, 'Ind[HU] 'chi_r \in irr HU}.
  by move=> r Mr; rewrite /= inertia_Ind_irr ?Itheta.
pose Xtheta := [set cfIirr ('Ind[HU] 'chi_r) | r in Mtheta].
have Da: a = #|HU : HCH1| by rewrite -(index_sdprodr defHU).
have Xtheta_1: {in Xtheta, forall s, 'chi_s 1%g = a%:R}.
  move=> _ /imsetP[r Mr ->]; have /imset2P[i j _ _ Dr] := Mr.
  rewrite cfIirrE ?irr_Xtheta ?cfInd1 //= -Da lin_char1 ?mulr1 //.
  by rewrite Dr mod_IirrE ?cfMod_lin_char // cfIirrE ?lin_char_irr.
have nsH0U'HU: H0U' <| HU.
  by apply: normalS nsH0U'_M; rewrite // -(sdprodWY defHU) genS ?setUSS.
have sXthetaXH0U': Xtheta \subset X_ H0U'.
  apply/subsetP=> _ /imsetP[r Mr ->]; have [i j nz_i _ Dr] := imset2P Mr.
  rewrite !inE cfIirrE ?irr_Xtheta ?sub_cfker_Ind_irr //= ?normal_norm //.
  rewrite Dr mod_IirrE // cfIirrE ?lin_char_irr // join_subG andbCA.
  rewrite {1}cfker_mod //= !{1}sub_cfker_mod //; apply/andP; split; last first.
    rewrite -(sdprodWY (sdprod_cfker _ _)) sub_gen ?subsetU // orbC.
    rewrite (subset_trans _ (cfker_dprod _ _ _)) // sub_gen ?subsetU // orbC.
    by rewrite /lam mod_IirrE ?cfker_mod.
  apply: contraL nz_i => /(subset_trans sH1H); rewrite !inE negbK.
  by move/(sub_cfker_Res (subxx _)); rewrite thetaH1 subGcfker.
have nsCH1_U: 'C_U(H1 | 'Q) <| U by rewrite sub_der1_normal.
have nH1cU: (U / H0)%g \subset 'N(H1c).
  rewrite -(bigdprodWY defH1c) norms_gen ?norms_bigcup //.
  apply/bigcapsP=> w /setD1P[_ W1w].
  by rewrite normJ -sub_conjgV (normsP (quotient_norms H0 nUW1)) ?groupV.
have ->: #|Mtheta| = (#|Xtheta| * a)%N.
  rewrite Da mulnC -card_imset_Ind_irr // => _ xy /imset2P[i j nz_i _ ->].
  case/(mem_sdprod defHU)=> x [y [Hx Uy -> _]]; have HUy := subsetP sUHU y Uy.
  pose yb := inMb y; have Uyb: yb \in (U / H0)%g by rewrite mem_quotient.
  pose iy := conjg_Iirr i yb; pose jy := conjg_Iirr j (coset (U' / H0)%g yb).
  apply/imset2P; exists iy jy; rewrite !inE ?conjg_Iirr_eq0 // in nz_i *.
  apply: irr_inj; have HCH1x: x \in HCH1 by rewrite mem_gen ?inE ?Hx.
  rewrite conjg_IirrE (cfConjgM _ nsHCH1_HU) ?(subsetP sHHU x) {Hx}//.
  rewrite {x HCH1x}(cfConjg_id _ HCH1x) !{1}mod_IirrE //.
  rewrite !{1}cfIirrE ?lin_char_irr //.
  rewrite cfConjgMod_norm ?(subsetP nH0U) ?(subsetP (normal_norm nsHCH1_HU)) //.
  have nCH1_Ub: (U / H0)%g \subset 'N('C_(U / H0)(H1)).
    by rewrite normsI ?normG ?norms_cent.
  rewrite cfConjgSdprod ?cfConjgDprod ?(subsetP _ _ Uyb) ?normsY //.
  rewrite /theta /lam !{1}mod_IirrE // !{1}conjg_IirrE.
  by rewrite cfConjgMod_norm ?(subsetP _ _ Uyb) // quotient_norms ?gFnorm.
rewrite leq_pmul2r ?indexg_gt0 // cardE -(size_map (fun s => 'Ind[M] 'chi_s)).
have kerH1c s: s \in Xtheta -> H1c \subset (cfker 'chi_s / H0)%g.
  case/imsetP=> r Mr ->; have [i j _ _ Dr] := imset2P Mr.
  rewrite -(setIidPr (normal_sub nsH1cHCH1)) -morphim_setIpre quotientS //.
  rewrite cfIirrE ?irr_Xtheta ?sub_cfker_Ind_irr //; last first.
    by rewrite normsI ?normal_norm // -(quotientGK nsH0_HU) cosetpre_normal.
  rewrite Dr mod_IirrE // cfker_morph ?normal_norm // cfIirrE ?lin_char_irr //.
  by rewrite setIS ?joing_subl ?morphpreS // cfker_sdprod.
have injXtheta:
  {in M & Xtheta &, forall w s1 s2, 'chi_s1 = 'chi_s2 ^ w -> w \in HU}%CF.
- move=> _ s1 s2 /(mem_sdprod defM)[y [w [HUy W1w -> _]]] Xs1 Xs2.
  rewrite groupMl // cfConjgMnorm ?(subsetP (normG _) y) ?(subsetP nHUW1) //.
  rewrite {y HUy}(cfConjg_id _ HUy) => Ds1.
  have nH0w: w \in 'N(H0) by rewrite ?(subsetP nH0M) ?(subsetP sW1M).
  rewrite (subsetP (normal_sub nsH0_HU)) // coset_idr //.
  have /setDP[]:= subsetP sXthetaXH0U' s1 Xs1; rewrite !inE join_subG /=.
  case/andP=> kerH0s1 _; apply: contraNeq; rewrite -eq_invg1 => ntw.
  rewrite -(quotientSGK nH0H) // -(dprodW defHb1) mul_subG ?kerH1c //=.
  rewrite Ds1 cfker_conjg ?(subsetP nHUW1) // quotientJ // -sub_conjgV.
  rewrite (subset_trans _ (kerH1c s2 Xs2)) // -(bigdprodWY defH1c) sub_gen //.
  by rewrite (bigcup_max (inMb w)^-1%g) // !inE ntw groupV mem_quotient.
rewrite -size_filter uniq_leq_size //.
  apply/dinjectiveP=> s1 s2 Xs1 Xs2.
  case/(cfclass_Ind_irrP _ _ (der_normal 1 M))/cfclassP=> y My Ds2.
  by apply: irr_inj; rewrite Ds2 cfConjg_id ?(injXtheta y s1 s2).
move=> _ /imageP[s Xs ->]; rewrite mem_filter /= cfInd1 // -(index_sdprod defM).
rewrite Xtheta_1 // -natrM eqxx mem_seqInd ?gFnormal //.
rewrite (subsetP sXthetaXH0U') // !andbT inertia_Ind_irr ?gFnormal //.
by apply/subsetP=> y /setIP[My /inertiaJ/esym/injXtheta->].
Qed.

Import ssrnum Num.Theory.

(* This is Peterfalvi (9.9); we have exported the fact that HU / H0 is a      *)
(* Frobenius group in case (c), as this is directly used in (9.10).           *)
Lemma typeP_Galois_characters (is_Galois : typeP_Galois) :
  [/\ (*a*) {in X_ H0, forall s, (u %| 'chi_s 1%g)%Cx},
            {in X_ H0C', forall s, 'chi_s 1%g = u%:R /\
             (exists2 xi : 'CF(HC), xi \is a linear_char & 'chi_s = 'Ind xi)},
      (*b*) size mu_ = p.-1 /\ {in mu_, forall mu_j, isIndHC mu_j}
    & (*c*) all redM (S_ H0C') ->
            [/\ C :=: 1%g, u = (p ^ q).-1 %/ p.-1
              & [Frobenius HU / H0 = Hbar ><| (U / H0)]]].
Proof.
have [F [phi [psi _ [Kpsi phiJ]]]] := typeP_Galois_P is_Galois.
case=> [oF /isomP[inj_phi im_phi] phiW2] [cycUbar co_u_p1 u_dv_pq1].
have [nsHUM sW1M /mulG_sub[sHUM _] nHUW1 tiHUW1] := sdprod_context defM.
have [nsHHU sUHU /mulG_sub[sHHU _] nHU tiHU] := sdprod_context defHU.
have [nsH0C_M nsHC_M _ nsH0C'_M] := nsH0xx_M; have nH0H := normal_norm nsH0H.
have nsH0HU: H0 <| HU := normalS (subset_trans sH0H sHHU) sHUM nsH0M.
have nH0U: U \subset 'N(H0) := subset_trans sUHU (normal_norm nsH0HU).
have nH0C := subset_trans sCU nH0U.
have sH0C_HU: H0C \subset HU by rewrite -(sdprodWY defHU) genS ?setUSS.
have nsH0C_HU: H0C <| HU := normalS sH0C_HU sHUM nsH0C_M.
have nH0C_HU := normal_norm nsH0C_HU.
have [coH0U coHC] := (coprimeSg sH0H coHU, coprimegS sCU coHU).
have [nH0C_H nH0C_U] := (subset_trans sHHU nH0C_HU, subset_trans sUHU nH0C_HU).
have tiHOC_H: H0C :&: H = H0.
  by rewrite /= norm_joinEr // -group_modl // setIC coprime_TIg ?mulg1.
have{coH0U} tiHOC_U: H0C :&: U = C.
  by rewrite /= norm_joinEr // setIC -group_modr // setIC coprime_TIg ?mul1g.
have isoHbar: Hbar \isog H / H0C.
  by have:= second_isog nH0C_H; rewrite tiHOC_H.
have isoUbar: Ubar \isog U / H0C.
  by have:= second_isog nH0C_U; rewrite tiHOC_U.
have frobHU: [Frobenius HU / H0C = (H / H0C) ><| (U / H0C)].
  have defHUbar: (H / H0C) ><| (U / H0C) = (HU / H0C)%g.
    exact: quotient_coprime_sdprod.
  apply/Frobenius_semiregularP=> //; first by rewrite -(isog_eq1 isoHbar).
    by rewrite -(isog_eq1 isoUbar); have [] := Frobenius_context frobUW1c.
  move=> yb /setD1P[ntyb /morphimP[y nH0Cy Uy] Dyb] /=; rewrite Dyb.
  apply/trivgP/subsetP=> _ /setIP[/morphimP[/= x nHOCx Hx ->] /cent1P/commgP].
  rewrite -morphR //; set xy := [~ x, y] => /eqP/coset_idr/=H0Cxy.
  have [nH0x nH0y] := (subsetP nH0H x Hx, subsetP nH0U y Uy).
  rewrite inE coset_id ?mem_gen // inE coset_idr //; apply: contraNeq ntyb.
  rewrite -(morph_injm_eq1 inj_phi) ?mem_quotient // => nz_x.
  rewrite {yb}Dyb /= coset_id ?mem_gen // -Kpsi !inE Uy orbC /= -val_eqE.
  rewrite -(inj_eq (mulfI nz_x)) mulr1 -[_ * _]phiJ ?mem_quotient // qactJ nH0y.
  rewrite -morphJ // conjg_mulR -/xy mkerr ?eqxx // ker_coset -tiHOC_H inE.
  by rewrite andbC groupM ?groupV ?memJ_norm ?(subsetP nHU) //= H0Cxy ?groupR.
have{coHC} tiHbC: (Hbar :&: C / H0 = 1)%g by rewrite coprime_TIg ?coprime_morph.
have{tiHbC} defHCbar: Hbar \x (C / H0) = (HC / H0)%g.
  by rewrite dprodEY ?quotientY // [C]unlock/= astabQ quotient_setIpre subsetIr.
have sHCHU: HC \subset HU by rewrite -(sdprodWY defHU) genS ?setUS.
have nsHCHU: HC <| HU := normalS sHCHU sHUM nsHC_M.
have sH0HC: H0 \subset HC := subset_trans sH0H (joing_subl H C).
have nsH0HC: H0 <| HC := normalS sH0HC sHCHU nsH0HU.
have nsHHUb: Hbar <| HU / H0 by rewrite quotient_normal.
have I_XH0_C i: i != 0 -> 'I_HU['chi[Hbar]_i %% H0]%CF = HC.
  move=> /= nz_i; apply/esym/eqP.
  have nsCHUb: C / H0 <| HU / H0 by rewrite -quotientYidl ?quotient_normal.
  have sH0C_HC: H0C \subset HC by rewrite genS ?setSU.
  have nsH0C_HC: H0C <| HC := normalS sH0C_HC sHCHU nsH0C_HU.
  have [j Dj]: exists j, 'chi_j = (cfDprodl defHCbar 'chi_i %% H0)%CF.
    by rewrite -dprodl_IirrE -mod_IirrE //; set j := mod_Iirr _; exists j.
  have kerH0Cj: H0C \subset cfker 'chi_j.
    by rewrite Dj sub_cfker_mod ?join_subG ?normG // quotientYidl ?cfker_sdprod.
  rewrite inertia_mod_pre // -(inertia_dprodl defHCbar) ?normal_norm //.
  rewrite -inertia_mod_pre // -Dj eqEsubset sub_Inertia //=.
  rewrite -(quotientSGK _ sH0C_HC) ?subIset ?nH0C_HU -?inertia_quo //.
  rewrite -(quotientYidr nH0C_H) joingA (joing_idPl sH0H) in frobHU.
  rewrite -?quo_IirrE ?(inertia_Frobenius_ker (FrobeniusWker frobHU)) //.
  by rewrite quo_Iirr_eq0 // -irr_eq1 Dj cfMod_eq1 // cfDprodl_eq1 irr_eq1.
have{I_XH0_C} irr_IndHC r: r \in Iirr_kerD HC H H0 -> 'Ind 'chi_r \in irr HU.
  rewrite !inE => /andP[ker'H kerH0]; apply: inertia_Ind_irr => //.
  apply: subset_trans (sub_inertia_Res _ (normal_norm nsHHU)) _.
  rewrite -{kerH0}(quo_IirrK _ kerH0) // mod_IirrE // in ker'H *.
  have /codomP[[i j] Dr] := dprod_Iirr_onto defHCbar (quo_Iirr H0 r).
  rewrite {r}Dr dprod_IirrE cfResMod ?joing_subl ?sub_cfker_mod //= in ker'H *.
  rewrite cfDprod_Resl linearZ inertia_scale_nz ?irr1_neq0 ?I_XH0_C //.
  by apply: contraNneq ker'H => ->; rewrite irr0 cfDprod_cfun1l cfker_sdprod.
have [nb_mu H0C_mu] := nb_redM_H0; set part_a' := ({in X_ H0C', _}).
have Part_a s: s \in X_ H0 -> exists r, 'chi_s = 'Ind[HU, HC] 'chi_r.
  rewrite !inE => /andP[Ks'H KsH0]; have [r sHCr] := constt_cfRes_irr HC s.
  have{KsH0} KrH0: H0 \subset cfker 'chi_r.
    by rewrite (sub_cfker_constt_Res_irr sHCr) // ?normal_norm.
  have{Ks'H} Kr'H: ~~ (H \subset cfker 'chi_r).
    by rewrite (sub_cfker_constt_Res_irr sHCr) ?joing_subl // ?normal_norm.
  have [|s1 Ds1] := irrP _ (irr_IndHC r _); first by rewrite !inE Kr'H.
  rewrite -constt_Ind_Res Ds1 constt_irr inE in sHCr.
  by rewrite (eqP sHCr) -Ds1; exists r.
have [nH0HC nH0C'] := (normal_norm nsH0HC, subset_trans (der_sub 1 _) nH0C).
have Part_a': part_a'.
  move=> s /setDP[KsH0C' Ks'H]; have [|r Ds] := Part_a s.
    by rewrite inE Ks'H (subsetP (Iirr_kerS _ _) _ KsH0C') ?joing_subl.
  suffices lin_r: 'chi_r \is a linear_char.
    by split; [rewrite Du Ds cfInd1 ?lin_char1 ?mulr1 | exists 'chi_r].
  have KrH0C': H0C' \subset cfker 'chi_r.
    rewrite inE Ds sub_cfker_Ind_irr // in KsH0C'.
    by rewrite (subset_trans sHUM) ?normal_norm.
  rewrite lin_irr_der1 (subset_trans _ KrH0C') //= (norm_joinEr nH0C').
  rewrite -quotientSK ?(subset_trans (der_sub 1 _)) ?quotient_der //= -/C.
  by rewrite -(der_dprod 1 defHCbar) (derG1P abHbar) dprod1g.
split=> // [s /Part_a[r ->] | | {Part_a' part_a'}red_H0C'].
- by rewrite Du cfInd1 // dvdC_mulr // Cint_Cnat ?Cnat_irr1.
- split=> // mu_j /H0C_mu H0C_mu_j; have [s XH0Cs Dmuj] := seqIndP H0C_mu_j.
  have [|s1u [xi lin_xi Ds]] := Part_a' s.
    by rewrite (subsetP _ _ XH0Cs) ?Iirr_kerDS // genS ?setUS ?der_sub.
  split=> //; first by rewrite Dmuj cfInd1 // s1u -natrM -(index_sdprod defM).
  by rewrite Dmuj Ds cfIndInd //; exists xi.
have C1: C :=: 1%g.
  apply: contraTeq red_H0C' => ntC; apply/allPn.
  have sCM: C \subset M := subset_trans sCU (subset_trans sUHU sHUM).
  have{sCM} solCbar: solvable (C / H0).
    by rewrite quotient_sol ?(solvableS sCM) ?mmax_sol.
  have [|{ntC solCbar} j lin_j nz_j] := solvable_has_lin_char _ solCbar.
    rewrite -(isog_eq1 (quotient_isog _ _)) ?(subset_trans sCU) //.
    by rewrite coprime_TIg ?(coprimegS sCU) ?(coprimeSg sH0H).
  have [i lin_i nz_i] := solvable_has_lin_char ntHbar solHbar.
  pose r := mod_Iirr (dprod_Iirr defHCbar (i, j)).
  have KrH0: H0 \subset cfker 'chi_r by rewrite mod_IirrE ?cfker_mod.
  have Kr'H: ~~ (H \subset cfker 'chi_r).
    rewrite -subsetIidl -cfker_Res ?joing_subl ?irr_char // mod_IirrE //.
    rewrite cfResMod ?joing_subl // sub_cfker_mod // dprod_IirrE.
    by rewrite cfDprodKl ?lin_char1 // subGcfker -irr_eq1.
  have [|s Ds] := irrP _ (irr_IndHC r _); first by rewrite !inE Kr'H.
  have Ks'H: s \notin Iirr_ker HU H.
    by rewrite inE -Ds sub_cfker_Ind_irr ?normal_norm.
  exists ('Ind 'chi_s).
    rewrite mem_seqInd ?gFnormal // inE Ks'H inE -Ds.
    rewrite sub_cfker_Ind_irr // ?(subset_trans sHUM) ?normal_norm //=.
    rewrite mod_IirrE // join_subG cfker_mod // sub_cfker_mod ?quotient_der //.
    apply: subset_trans (dergS 1 (quotientS H0 (joing_subr H C))) _.
    by rewrite -lin_irr_der1 dprod_IirrE cfDprod_lin_char.
  apply: contra nz_j => red_j; have /implyP := H0C_mu ('Ind 'chi_s).
  rewrite mem_filter red_j !mem_seqInd ?gFnormal // !in_setD Ks'H !inE -Ds.
  rewrite irr_eq1 !sub_cfker_Ind_irr ?(normal_norm nsH0HU) //.
  rewrite mod_IirrE // join_subG cfker_mod //= sub_cfker_mod // dprod_IirrE.
  by move/(sub_cfker_Res (subxx _)); rewrite cfDprodKr ?lin_char1 ?subGcfker.
rewrite /= -/C C1 joingG1 in frobHU; split=> //; move/FrobeniusWker in frobHU.
have nsHbHU: Hbar <| (HU / H0) by rewrite quotient_normal.
have ->: (p ^ q).-1 = (#|X_ H0| * u)%N.
  rewrite -oF -cardsT -im_phi card_injm // -(card_Iirr_abelian abHbar).
  rewrite -(cardsC1 0) (card_imset_Ind_irr nsHbHU) => [|i|i y]; last first.
  - by rewrite !inE conjg_Iirr_eq0.
  - by rewrite !inE => nz_i; rewrite inertia_Ind_irr ?inertia_Frobenius_ker.
  rewrite index_quotient_eq ?(subset_trans sHUM) ?subIset ?sH0H ?orbT //.
  apply/eqP; rewrite Du /= C1 joingG1 mulnC eqn_pmul2r //.
  rewrite -(card_imset _ (can_inj (mod_IirrK _))) // -imset_comp.
  apply/eqP/eq_card=> s; apply/imsetP/idP=> [[i nz_i -> /=] | Xs].
    rewrite !inE mod_IirrE 1?{1}cfker_mod // andbT in nz_i *.
    rewrite cfIirrE ?inertia_Ind_irr ?inertia_Frobenius_ker // sub_cfker_mod //.
    by rewrite sub_cfker_Ind_irr ?quotientS ?normal_norm // subGcfker.
  have [[]] := (Part_a s Xs, setDP Xs).
  rewrite /= C1 joingG1 !inE => r Ds [kerH0s].
  have:= kerH0s; rewrite Ds !sub_cfker_Ind_irr ?normal_norm // => kerH0 ker'H.
  exists (quo_Iirr H0 r).
    by rewrite !inE -subGcfker quo_IirrE // cfker_quo ?quotientSGK.
  by rewrite quo_IirrE // cfIndQuo // -Ds -quo_IirrE // irrK quo_IirrK.
suffices ->: #|X_ H0| = p.-1 by rewrite -(subnKC (prime_gt1 p_pr)) mulKn.
rewrite -nb_mu (size_red_subseq_seqInd_typeP MtypeP _ H0C_mu) //; last first.
- exact/allP/filter_all.
- by rewrite filter_uniq ?seqInd_uniq.
apply/esym/eq_card => i; rewrite inE mem_filter mem_seqInd ?gFnormal //.
rewrite andb_idl // => Xi; rewrite (allP red_H0C') //.
by rewrite mem_seqInd ?gFnormal //= C1 (trivgP (der_sub 1 _)) joingG1.
Qed.

(* This combination of (9.8)(b) and (9.9)(b) covers most uses of these lemmas *)
(* in sections 10-14.                                                         *)
Lemma typeP_reducible_core_Ind (ptiWM := FT_primeTI_hyp MtypeP) :
  [/\ size mu_ = p.-1, has predT mu_,
      {subset mu_ <= [seq primeTIred ptiWM j | j in predC1 0]}
    & {in mu_, forall mu_j, isIndHC mu_j}].
Proof.
have [[sz_mu _] /mulG_sub[sHHU _]] := (nb_redM_H0, sdprodW defHU).
rewrite has_predT sz_mu -subn1 subn_gt0 prime_gt1 //; split=> // [mu_j|].
  rewrite mem_filter => /andP[red_chi /seqIndP[s /setDP[_ kerH's] Dchi]].
  have [[j Ds] | [/idPn[]]] := prTIres_irr_cases ptiWM s; last by rewrite -Dchi.
  rewrite Dchi Ds cfInd_prTIres image_f ?inE //=.
  by apply: contraNneq kerH's => j0; rewrite inE Ds j0 prTIres0 cfker_cfun1.
have[/typeP_Galois_characters[_ _ []] // | Gal'M] := boolP typeP_Galois.
by have [_ []] := typeP_nonGalois_characters Gal'M.
Qed.

(* This is Peterfalvi (9.10), formulated as a constructive alternative. *)
Lemma typeP_reducible_core_cases :
  {t : Iirr M & 'chi_t \in S_ H0C' /\ 'chi_t 1%g = (q * u)%:R
              & {xi | xi \is a linear_char & 'chi_t = 'Ind[M, HC] xi}}
  + [/\ typeP_Galois, [Frobenius HU / H0 = Hbar ><| (U / H0)],
        cyclic U, #|U| = (p ^ q).-1 %/ p.-1
      & FTtype M == 2 -> [Frobenius HU = H ><| U]].
Proof.
have [GalM | Gal'M] := boolP typeP_Galois; last first.
  pose eqInHCb nu r := ('chi_r \is a linear_char) && (nu == 'Ind[M, HC] 'chi_r).
  pose isIndHCb (nu : 'CF(M)) :=
    (nu 1%g == (q * u)%:R) && [exists r, eqInHCb nu r].
  suffices /sig2W[t H0C't]: exists2 t, 'chi_t \in S_ H0C' & isIndHCb 'chi_t.
    case/andP=> /eqP t1qu /exists_inP/sig2W[r lin_r /eqP def_t].
    by left; exists t => //; exists 'chi_r.
  have [_ _ [t [t1qu H0Ct IndHCt]] _] := typeP_nonGalois_characters Gal'M.
  exists t; first by rewrite (seqIndS _ H0Ct) ?Iirr_kerDS ?genS ?setUS ?der_sub.
  rewrite /isIndHCb t1qu eqxx; have [xi lin_xi ->] := IndHCt.
  by apply/exists_inP; exists (cfIirr xi); rewrite cfIirrE ?lin_char_irr.
have [_ IndHC_SH0C' _] := typeP_Galois_characters GalM; rewrite all_predC.
case: hasP => [/sig2W[eta H0C'eta /irrP/sig_eqW[t Dt]] _ | _ [//|C1 <- frobHU]].
  have /sig2_eqW[s /IndHC_SH0C'[s1u IndHCs] Deta] := seqIndP H0C'eta.
  have [joinHU [xi lin_xi Ds]] := (sdprodWY defHU, sig2_eqW IndHCs).
  left; exists t; first split; rewrite -Dt // Deta.
    by rewrite cfInd1 ?der_sub // -(index_sdprod defM) s1u -natrM.
  by exists xi; rewrite ?Ds ?cfIndInd ?der_sub // -joinHU genS ?setUS ?subsetIl.
have cycU: cyclic U.
  rewrite (isog_cyclic (quotient1_isog _)) -C1.
  by have [_ _ []] := typeP_Galois_P GalM.
right; split=> //; first by rewrite /u /Ubar C1 -(card_isog (quotient1_isog _)).
case/(compl_of_typeII maxM MtypeP) => /= _ _ _ UtypeF <-.
have [_ -> _] := typeF_context UtypeF.
by apply/forall_inP=> S /and3P[_ /cyclicS->].
Qed.

Import ssrint.

(* This is Peterfalvi (9.11) *)
(* We had to cover a small gap in step (9.11.4) of the proof, which starts by *)
(* proving that U1 \subset {1} u A(M), then asserts this obviously implies    *)
(* HU1 \subset {1} u A(M). It is not, as while {1} u A(M) does contain H, it  *)
(* is not (necessarily) a subgroup. We had to use the solvability of HU1 in a *)
(* significant way (using Philip Hall's theorems) to bridge the gap; it's     *)
(* also possible to exploit lemma (2.1) (partition_cent_rcoset in PFsection1) *)
(* in a slightly different argument, but the inference is nontrivial in       *)
(* either case.                                                               *)
Lemma Ptype_core_coherence : coherent (S_ H0C') M^# tau.
Proof.
have [nsHUM sW1M /mulG_sub[sHUM _] nHUW1 tiHUW1] := sdprod_context defM.
have [nsHHU sUHU /mulG_sub[sHHU _] nHU tiHU] := sdprod_context defHU.
have nsCU: C <| U := normalS sCU (joing_subl _ _) nsCUW1.
have [_ nCU] := andP nsCU; have sC'C: C^`(1)%g \subset C := der_sub 1 _.
have coHC := coprimegS sCU coHU; have coH0C := coprimeSg sH0H coHC.
have [nsH0C_M nsHC_M nsH0U'_M nsH0C'_M] := nsH0xx_M; have [_ nH0H]:= andP nsH0H.
have nH0HU := subset_trans sHUM nH0M; have nH0U := subset_trans sUHU nH0HU.
have nH0C := subset_trans sCU nH0U; have nH0C' := subset_trans sC'C nH0C.
have sHCHU: HC \subset HU by rewrite join_subG sHHU (subset_trans sCU).
have [nsHCHU nHC] := (normalS sHCHU sHUM nsHC_M, subset_trans sCU nHU).
have tiHCbar: Hbar :&: (C / H0)%g = 1%g by rewrite coprime_TIg ?coprime_morph.
have defHCbar: Hbar \x (C / H0) = (HC / H0)%g.
  by rewrite dprodEY ?quotientY // [C]unlock/= astabQ quotient_setIpre subsetIr.
have{tiHCbar} defHC'bar: (HC / H0)^`(1)%g = (C^`(1) / H0)%g.
  by rewrite -(der_dprod 1 defHCbar) (derG1P abHbar) dprod1g quotient_der.
have sU'U := der_sub 1 U; have nH0U' := subset_trans sU'U nH0U.
have sU'C: U' \subset C.
  by rewrite [C]unlock subsetI sub_astabQ sU'U nH0U' quotient_cents.
have uS0: uniq (S_ H0C') by apply: seqInd_uniq.
have [rmR scohS0]: exists R : 'CF(M) -> seq 'CF(G), subcoherent (S_ H0C') tau R.
  move: (FTtypeP_coh_base _ _) (FTtypeP_subcoherent maxM MtypeP) => R scohR.
  exists R; apply: (subset_subcoherent scohR).
  split=> //; last exact: cfAut_seqInd.
  by apply: seqIndS; rewrite Iirr_kerDS ?sub1G ?Fcore_sub_FTcore.
have [GalM | Gal'M] := boolP typeP_Galois.
  have [_ XOC'u _ _] := typeP_Galois_characters GalM.
  apply: uniform_degree_coherence scohS0 _.
  apply: all_pred1_constant (#|M : HU| * u)%:R _ _; rewrite all_map.
  by apply/allP=> _ /seqIndP[s /XOC'u[s1u _] ->] /=; rewrite natrM cfInd1 ?s1u.
have:= typeP_nonGalois_characters Gal'M.
set U1 := 'C_U(_ | _); set a := #|_ : _|.
case: (_ Gal'M) => /= H1 [oH1 nH1U _ defHbar aP] in U1 a *.
rewrite -/U1 -/a in aP; case: aP => a_gt1 a_dv_p1 cycU1 _.
case=> [a_dv_XH0 [nb_mu IndHCmu] has_irrHC lb_Sqa]; rewrite -[S_ _]/(S_ H0C').
have defHb1 := defHbar; rewrite (big_setD1 1%g) ?group1 ?conjsg1 //= in defHb1.
have [[_ H1c _ defH1c] _ _ _] := dprodP defHb1; rewrite defH1c in defHb1.
have [nsH1H _] := dprod_normal2 defHb1; have [sH1H _] := andP nsH1H.
have nsU1U: U1 <| U; last have [sU1U nU1U] := andP nsU1U.
  by rewrite norm_normalI // astabQ norm_quotient_pre ?norms_cent.
have Da: a = #|HU : H <*> U1|.
  rewrite /a -!divgS /= ?join_subG ?sHHU ?norm_joinEr ?(subset_trans sU1U) //=.
  by rewrite -(sdprod_card defHU) coprime_cardMg ?(coprimegS sU1U) ?divnMl.
have sCU1: C \subset U1 by rewrite [C]unlock setIS ?astabS.
have a_dv_u: a %| u by rewrite Da Du indexgS ?genS ?setUS.
have [a_gt0 q_gt0 u_gt0 p1_gt0]: [/\ 0 < a, 0 < q, 0 < u & 0 < p.-1]%N.
  rewrite !cardG_gt0 ltnW // -subn1 subn_gt0 prime_gt1 //.
have [odd_p odd_q odd_a]: [/\ odd p, odd q & odd a].
  by rewrite mFT_odd -oH1 (oddSg sH1H) ?(dvdn_odd a_dv_u) ?mFT_quo_odd.
have Dp: p = (2 * p.-1./2 + 1)%N.
  by rewrite mul2n -[p]odd_double_half odd_p half_double addn1.
(* Start of main proof. *)
pose S1 := filter [pred zeta : 'CF(M) | zeta 1%g == (q * a)%:R] (S_ H0C').
have ntS1: (0 < size S1)%N.
  have [lb_dv lbS1] := lb_Sqa; apply: leq_trans (leq_trans lbS1 _).
    by rewrite ltn_divRL // mul0n muln_gt0 p1_gt0 cardG_gt0.
  rewrite -size_filter uniq_leq_size ?filter_uniq ?seqInd_uniq // => chi.
  rewrite !mem_filter -andbA /= => /and3P[_ ->].
  by apply: seqIndS; rewrite Iirr_kerDS // genS ?setUS ?dergS ?subsetIl.
have sS10: cfConjC_subset S1 (S_ H0C').
  split=> [||chi]; first by rewrite filter_uniq.
    by apply: mem_subseq; apply: filter_subseq.
  rewrite !mem_filter !inE cfunE => /andP[/eqP <- S0chi].
  by rewrite cfAut_seqInd // andbT conj_Cnat ?(Cnat_seqInd1 S0chi).
have cohS1: coherent S1 M^# tau.
  apply: uniform_degree_coherence (subset_subcoherent scohS0 sS10) _.
  by apply: all_pred1_constant (q * a)%:R _ _; rewrite all_map filter_all.
pose S3 := filter [predC S1] (S_ H0C'); move: {2}_.+1 (ltnSn (size S3)) => nS. 
move: @S3 (sS10) (cohS1); have: {subset S1 <= S1} by [].
elim: nS {-1}S1 => // nS IHnS S2 => sS12 S3 sS20 cohS2; rewrite ltnS => leS3nS.
have [ntS3|] := boolP (size S3 > 0)%N; last first.
  rewrite size_filter -has_count has_predC negbK => /allP sS02.
  exact: subset_coherent sS02 cohS2.
(* Ultimateley we'll contradict the maximality of S2 in (9.11.1) & (9.11.8). *)
suff [chi]: exists2 chi, chi \in S3 & coherent (chi :: chi^* :: S2)%CF M^# tau.
  rewrite mem_filter => /andP[/= S2'chi S0chi]; have [uS2 sS2S0 ccS2] := sS20.
  move/IHnS; apply=> [psi /sS12 S1psi||]; first by rewrite 2?mem_behead.
    split.
    - rewrite /= !inE negb_or S2'chi (contra (ccS2 _)) ?cfConjCK // eq_sym.
      by rewrite (seqInd_conjC_neq _ _ _ S0chi) ?mFT_odd.
    - by apply/allP; rewrite /= S0chi cfAut_seqInd //=; apply/allP.
    apply/allP; rewrite /= !inE cfConjCK !eqxx orbT /=.
    by apply/allP=> psi /ccS2; rewrite !inE orbA orbC => ->.
  apply: leq_trans leS3nS; rewrite ltnNge; apply: contra S2'chi.
  case/leq_size_perm=> [|psi|/(_ chi)]; first by rewrite filter_uniq.
    by rewrite !mem_filter !inE orbA negb_or -andbA => /andP[].
  by rewrite !mem_filter !inE eqxx S0chi !andbT => /esym/negbFE.
(* This is step (9.11.1). *) clear nS IHnS leS3nS.
without loss [[eqS12 irrS1 H0C_S1] [Da_p defC] [S3qu ne_qa_qu] [oS1 oS1ua]]:
  / [/\ [/\ S1 =i S2, {subset S1 <= irr M} & {subset S1 <= S_ H0C}],
        a = p.-1./2 /\ C :=: U',
        (forall chi, chi \in S3 -> chi 1%g == (q * u)%:R) /\ (q * u != q * a)%N
      & size S1 = (p.-1 * u %/ a ^ 2)%N /\ size S1 = (2 * u %/ a)%N].
- move=> IHwlog; have{sS20} [[uS2 sS20 ccS2] [uS1 _ _]] := (sS20, sS10).
  pose is_qu := [pred chi : 'CF(M) | chi 1%g == (q * u)%:R].
  pose isn't_qu := [pred chi | is_qu chi ==> all is_qu S3].
  have /hasP[chi S3chi qu'chi]: has isn't_qu S3.
    rewrite /isn't_qu; have [_|] := boolP (all _ _); last by rewrite has_predC. 
    by rewrite (eq_has (fun _ => implybT _)) has_predT.
  have [S2'chi S0chi]: chi \notin S2 /\ chi \in S_ H0C'.
    by apply/andP; rewrite mem_filter in S3chi.
  have [s X0C's Dchi] := seqIndP S0chi.
  have Dchi1: chi 1%g = q%:R * 'chi_s 1%g.
    by rewrite Dchi cfInd1 // -(index_sdprod defM).
  (* We'll show lb0 <= lb1 <= lb <= lb3 <= sumnS S1' <= sumnS S2 <= lb0,   *)
  (* with equality under conditions that imply the conclusion of (9.11.1). *)
  pose lb0 := (2 * q * a)%:R * chi 1%g.
  pose lb1 : algC := (2 * a * q ^ 2 * u)%:R.
  pose lb2 : algC := (p.-1 * q ^ 2 * u)%:R.
  pose lb3 : algC := (p.-1 * q ^ 2 * #|U : U'|)%:R.
  pose S1' := filter [predI irr M & S_ H0U'] S1.
  pose szS1' := ((p.-1 * #|U : U'|) %/ a ^ 2)%N; set lbS1' := _ %/ _ in lb_Sqa.
  pose Snorm (psi : 'CF(M)) := psi 1%g ^+ 2 / '[psi].
  pose sumnS Si := \sum_(psi <- Si) Snorm psi.
  have lb01: lb0 <= lb1 ?= iff (chi 1%g == (q * u)%:R).
    rewrite /lb1 mulnA -mulnA natrM /lb0 mulnAC mono_lerif; last first.
      by apply: ler_pmul2l; rewrite ltr0n !muln_gt0 a_gt0.
    apply: lerif_eq; rewrite Dchi1 natrM ler_pmul2l ?gt0CG //.
    have [KsH0C' _] := setDP X0C's; rewrite inE in KsH0C'.
    have [t sHCt] := constt_cfRes_irr HC s.
    have KtH0C': H0C' \subset cfker 'chi_t.
      apply: subset_trans (cfker_constt (cfRes_char _ (irr_char s)) sHCt).
      by rewrite cfker_Res ?irr_char // subsetI genS ?setUSS.
    rewrite -constt_Ind_Res in sHCt.
    apply: ler_trans (char1_ge_constt (cfInd_char _ (irr_char t)) sHCt) _.
    rewrite cfInd1 // -Du lin_char1 ?mulr1 // lin_irr_der1.
    apply: subset_trans KtH0C'; rewrite /= (norm_joinEr nH0C') /= -/C.
    rewrite -quotientSK ?(subset_trans (der_sub _ _)) ?(subset_trans sHCHU) //.
    by rewrite -defHC'bar quotient_der ?(subset_trans sHCHU).
  have lb12: lb1 <= lb2 ?= iff (a == p.-1./2).
    rewrite -(@eqn_pmul2l 2) // -(canLR (addnK 1) Dp) subn1 lerif_nat.
    rewrite !(mono_leqif (fun _ _ => leq_pmul2r _)) ?expn_gt0 ?q_gt0 //.
    apply: leqif_eq; rewrite dvdn_leq // Gauss_dvd //.
       by rewrite {1}Dp addn1 dvdn_mulr.
    by rewrite prime_coprime ?dvdn2 ?negbK.
  have lb23: lb2 <= lb3 ?= iff (C :==: U') :> algC.
    rewrite lerif_nat [u]card_quotient //.
    rewrite (mono_leqif (fun _ _ => leq_pmul2l _)) ?muln_gt0 ?p1_gt0 ?q_gt0 //.
    rewrite -(mono_leqif (fun _ _ => leq_pmul2l (cardG_gt0 C))) Lagrange //.
    rewrite -(Lagrange sU'U) (mono_leqif (fun _ _ => leq_pmul2r _)) //.
    by rewrite eq_sym; apply: subset_leqif_cards.
  have lb3S1': lb3 <= sumnS S1' ?= iff (size S1' == szS1').
    rewrite /szS1' -(divnMr (cardG_gt0 U')) mulnAC -mulnA Lagrange // -/lbS1'.
    have{lb_Sqa} [dv_lb lbSqa] := lb_Sqa; rewrite [sumnS S1']big_seq.
    rewrite (eq_bigr (fun _ => ((q * a) ^ 2)%:R)) => [|psi]; last first.
      rewrite !mem_filter -!andbA => /and4P[/irrP[r ->] _ /=/eqP r1qa _].
      by rewrite /Snorm cfnorm_irr divr1 r1qa natrX.
    rewrite -big_seq (big_nth 0) -natr_sum sum_nat_const_nat subn0.
    rewrite mulnC natrM [*%R]lock /lb3 natrM natf_indexg ?der_sub // mulrA.
    rewrite -natrM mulnAC -(divnK dv_lb) mulnAC mulnA natrM mulfK ?neq0CG //.
    rewrite -/lbS1' -mulnA -expnMn natrM mulrC -lock mono_lerif; last first.
      by apply: ler_pmul2l; rewrite ltr0n !muln_gt0 a_gt0 q_gt0.
    rewrite eq_sym lerif_nat; apply: leqif_eq; rewrite (leq_trans lbSqa) //.
    rewrite -size_filter uniq_leq_size ?filter_uniq ?seqInd_uniq // => psi.
    rewrite !mem_filter -!andbA /= => /and3P[-> -> S0psi]; rewrite S0psi.
    by apply: seqIndS S0psi; rewrite Iirr_kerDS //= genS ?setUS ?dergS.
  have lbS1'2: sumnS S1' <= sumnS S2 ?= iff ~~ has [predC S1'] S2.
    have Ds2: perm_eq S2 (S1' ++ filter [predC S1'] S2).
      rewrite -(perm_filterC (mem S1')) perm_cat2r.
      rewrite uniq_perm_eq ?filter_uniq // => psi.
      by rewrite mem_filter andb_idr //= mem_filter => /andP[_ /sS12].
    rewrite [sumnS S2](eq_big_perm _ Ds2) big_cat /= -/(sumnS S1') big_filter.
    rewrite -all_predC -big_all_cond !(big_tnth _ _ S2) big_andE.
    rewrite -{1}[_ S1']addr0 mono_lerif; last exact: ler_add2l.
    set sumS2' := \sum_(i | _) _; rewrite -[0]/(sumS2' *+ 0) -sumrMnl.
    apply: lerif_sum => i _; apply/lerifP; rewrite lt0r !mulf_eq0 invr_eq0.
    set psi := tnth _ i; have Spsi := sS20 psi (mem_tnth _ _).
    rewrite !negb_or (seqInd1_neq0 _ Spsi) //= (cfnorm_seqInd_neq0 _ Spsi) //=.
    by rewrite divr_ge0 ?exprn_ge0 ?cfnorm_ge0 ?Cnat_ge0 ?(Cnat_seqInd1 Spsi).
  have [lb0S2 | ] := boolP (lb0 < sumnS S2).
    exists chi => //; have /hasP[xi S1xi _]: has predT S1 by rewrite has_predT.
    have xi1: xi 1%g = (q * a)%:R.
      by rewrite mem_filter in S1xi; have [/eqP] := andP S1xi.
    apply: ((extend_coherent scohS0) _ xi) => //; first by rewrite S0chi sS12.
    split=> //; last by rewrite mulrAC xi1 -natrM mulnA.
    rewrite xi1 Dchi1 irr1_degree -natrM dvdC_nat dvdn_pmul2l ?cardG_gt0 //.
    rewrite -dvdC_nat /= !nCdivE -irr1_degree a_dv_XH0 //.
    by rewrite (subsetP (Iirr_kerDS _ _ _) _ X0C's) ?joing_subl.
  have lb1S2 := lerif_trans lb12 (lerif_trans lb23 (lerif_trans lb3S1' lbS1'2)).
  rewrite ltr_neqAle !(lerif_trans lb01 lb1S2) andbT has_predC !negbK.
  case/and5P=> /eqP chi1qu /eqP Da_p /eqP defC /eqP sz_S1' /allP sS21'.
  have defS1': S1' = S1.
    apply/eqP; rewrite -(geq_leqif (size_subseq_leqif (filter_subseq _ S1))).
    by rewrite uniq_leq_size // => psi /sS12/sS21'.
  apply: IHwlog; split=> //.
  + split=> psi; do 1?[rewrite -defS1' mem_filter andbC => /and3P[_ _] //=].
      by apply/idP/idP=> [/sS12 | /sS21']; rewrite ?defS1'.
    by congr (_ \in S_ _); apply/group_inj; rewrite /= defC.
  + split; first by apply/allP; apply: contraLR qu'chi; rewrite /= chi1qu eqxx.
    rewrite -eqC_nat -chi1qu; apply: contra S2'chi => chi1qa.
    by rewrite sS12 // mem_filter /= chi1qa.
  rewrite -defS1' sz_S1' /szS1' -defC -card_quotient // -/u.
  by split=> //; rewrite -mulnn {1}Dp addn1 -Da_p mulnAC divnMr.
have nCW1: W1 \subset 'N(C).
  by rewrite (subset_trans (joing_subr U W1)) ?normal_norm.
(* This is step (9.11.2). *) clear sS20 cohS2 sS12 has_irrHC lb_Sqa sU'C.
have [tiU1 le_u_a2]: {in W1^#, forall w, U1 :&: U1 :^ w = C} /\ (u <= a ^ 2)%N.
  have tiU1 w: w \in W1^# -> U1 :&: U1 :^ w = C; last split => //.
    case/setD1P=> ntw W1w; have nH0w := subsetP (subset_trans sW1M nH0M) w W1w.
    pose wb := coset H0 w; have W1wb: wb \in W1bar^#.
      rewrite !inE mem_quotient ?(contraNneq _ ntw) // => /coset_idr H0w.
      rewrite -in_set1 -set1gE -tiHUW1 inE (subsetP sHHU) // (subsetP sH0H) //.
      by rewrite H0w.
    have ntH1 w1: H1 :^ w1 :!=: 1%g by rewrite -cardG_gt1 cardJg oH1 prime_gt1.
    pose t_ w1 :=
      if pred2 1%g wb w1 then sval (has_nonprincipal_irr (ntH1 w1)) else 0.
    pose theta :=
      cfDprodl defHCbar (cfBigdprod defHbar (fun w1 => 'chi_(t_ w1))).
    have lin_theta : theta \is a linear_char.
      rewrite cfDprodl_lin_char ?cfBigdprod_lin_char // => w1 _.
      by rewrite irr_prime_lin ?cardJg ?oH1.
    have nsH0HC: H0 <| HC.
      by rewrite /normal join_subG nH0H sub_gen ?subsetU ?sH0H.
    move defK: H0C => K. (* to avoid divergence in Coq kernel *)
    have kerK: K \subset cfker (theta %% H0).
      rewrite -defK sub_cfker_mod ?join_subG ?normG ?quotientYidl //.
      exact: cfker_sdprod.
    have sKHC: K \subset HC by rewrite -defK genS ?setSU.
    have nsKHC: K <| HC by rewrite (normalS sKHC (normal_sub nsHC_M)) -?defK.
    have sH0K: H0 \subset K by rewrite -defK joing_subl.
    have nsKHU: K <| HU.
      by rewrite (normalS (subset_trans sKHC sHCHU) sHUM) -?defK.
    have [t2 Dt2]: {t2 : Iirr (HC / K) | 'chi_t2 %% K = theta %% H0}%CF.
      exists (cfIirr ((theta %% H0) / K)).
      by rewrite cfIirrE ?cfQuoK ?cfQuo_irr ?cfMod_irr ?lin_char_irr.
    have nsHChatHU: HC / K <| HU / K by rewrite quotient_normal.
    have sHChatHU := normal_sub nsHChatHU.
    pose That := 'I_(HU / K)['chi_t2]%G.
    have sThatHU: That \subset (HU / K)%G := Inertia_sub _ _.
    have abThatHC: abelian (That / (HC / K)).
      rewrite (abelianS (quotientS _ sThatHU)) //.
      rewrite (isog_abelian (third_isog _ _ _)) // defC.
      rewrite -(isog_abelian (quotient_sdprodr_isog defHU _)) ?gFnormal //.
      by rewrite sub_der1_abelian.
    have hallHChat: Hall That (HC / K).
      rewrite /Hall -(card_isog (third_isog sH0K nsH0HC nsKHC)) /=.
      rewrite sub_Inertia // -[in #|_|]defK /= quotientYidl //.
      rewrite -(card_isog (sdprod_isog (dprodWsdC defHCbar))).
      apply: coprime_dvdr (indexSg (sub_Inertia _ sHChatHU) sThatHU) _.
      apply: coprime_dvdr (index_quotient _) _.
        by rewrite subIset // normal_norm.
      by rewrite -Du coprime_morphl // coprime_morphr.
    have [s t2HUs] := constt_cfInd_irr t2 sHChatHU.
    have s_1: ('chi_s %% K)%CF 1%g = #|U : U1 :&: U1 :^ w|%:R.
      rewrite cfMod1.
      have [||_ _ ->] // := cfInd_Hall_central_Inertia _ abThatHC.
      rewrite -cfMod1 Dt2 cfMod1 lin_char1 //= mulr1 -inertia_mod_quo // Dt2.
      rewrite index_quotient_eq ?normal_norm ?Inertia_sub ?setIS //; last first.
        by rewrite (subset_trans sKHC) ?sub_inertia.
      rewrite /= inertia_morph_pre //= -quotientE inertia_dprodl; first 1 last.
      - by rewrite quotient_norms ?normal_norm.
      - rewrite /= -(quotientYidl nH0C) quotient_norms ?normal_norm //.
        by rewrite -defK in nsKHU.
      have nH1wHU w1: w1 \in (W1 / H0)%g -> (HU / H0)%g \subset 'N(H1 :^ w1).
        move=> W1w1; rewrite -(normsP (quotient_norms H0 nHUW1) _ W1w1) normJ.
        rewrite conjSg /= -(sdprodW defHU) quotientMl ?mul_subG //.
        exact: normal_norm.
      rewrite indexgI /= inertia_bigdprod_irr // (big_setD1 1%g) ?group1 //=.
      rewrite 2!{1}setIA setIid (bigD1 wb) //= {1 2}/t_ /= !eqxx ?orbT /=.
      rewrite !(inertia_irr_prime _ p_pr) ?cardJg //=;
        try by case: (has_nonprincipal_irr _).
      rewrite conjsg1 centJ setIA -setIIr /=.
      elim/big_rec: _ => [|w1 Uk /andP[/setD1P[ntw1 Ww1] w'w1] IHk]; last first.
        rewrite /t_ -if_neg negb_or ntw1 w'w1 irr0 Inertia1 -?setIIr 1?setIA //.
        rewrite /normal nH1wHU //= -(normsP (quotient_norms H0 nHUW1) _ Ww1).
        by rewrite conjSg (subset_trans sH1H) ?quotientS.
      rewrite setIT !morphpreI morphpreJ ?(subsetP nH0W1) //= -astabQ.
      rewrite quotientGK //; last by rewrite /normal (subset_trans sH0H).
      rewrite -(sdprodWY (sdprod_modl defHU _)); last first.
        rewrite subsetI -sub_conjgV.
        rewrite (normsP (gFnorm _ _)) ?groupV ?(subsetP sW1M) //= andbb.
        by rewrite sub_astabQ nH0H sub_abelian_cent.
      rewrite -(index_sdprodr defHU) ?subsetIl // conjIg (normsP nUW1) //.
      by rewrite -setIIr.
    apply/esym/eqP; rewrite eqEcard subsetI -sub_conjgV.
    rewrite (normsP _ _ (groupVr W1w)) ?sCU1 /=; last first.
      by rewrite (subset_trans (joing_subr U W1)) ?normal_norm.
    have{s_1} : pred2 u a #|U : U1 :&: U1 :^ w|.
      rewrite /= -!eqC_nat -{}s_1 -mod_IirrE //.
      pose phi := 'Ind[M] 'chi_(mod_Iirr s).
      have Sphi: phi \in S_ H0C'.
        rewrite mem_seqInd ?gFnormal // !inE mod_IirrE //.
        rewrite andbC (subset_trans _ (cfker_mod _ _)) //=; last first.
          by rewrite -defK genS ?setUS ?der_sub.
        rewrite sub_cfker_mod ?(subset_trans sHHU) ?normal_norm //.
        have sHHC: H \subset HC by rewrite joing_subl.
        rewrite -(sub_cfker_constt_Ind_irr t2HUs) ?quotientS //; last first.
          by rewrite quotient_norms ?normal_norm.
        rewrite -sub_cfker_mod ?(subset_trans sHHU (normal_norm nsKHU)) //.
        rewrite Dt2 sub_cfker_mod //.
        apply: contra (valP (has_nonprincipal_irr (ntH1 1%g))).
        move/eq_cfker_Res; rewrite cfDprodlK => kerHbar.
        have:= sH1H; rewrite -{1}(conjsg1 H1) -kerHbar => /eq_cfker_Res.
        by rewrite cfBigdprodKabelian ?group1 // /t_ /= eqxx -subGcfker => ->.
      have [/S3qu | ] := boolP (phi \in S3).
        rewrite cfInd1 // natrM -(index_sdprod defM).
        by rewrite (inj_eq (mulfI (neq0CG _))) => ->.
      rewrite mem_filter Sphi andbT negbK /= -eqS12 mem_filter Sphi andbT /=.
      rewrite cfInd1 // natrM -(index_sdprod defM) (inj_eq (mulfI (neq0CG _))).
      by rewrite orbC => ->.
    case/pred2P=> [iUCu | iUCa].
      rewrite -(leq_pmul2r u_gt0) -{1}iUCu /u card_quotient ?Lagrange //.
      by rewrite /= -setIA subsetIl.
    rewrite subset_leq_card // subIset // [C]unlock subsetI subsetIl sub_astabQ.
    rewrite subIset ?nH0U //= centsC -(bigdprodWY defHbar) gen_subG.
    apply/orP; left; apply/bigcupsP=> w1 Ww1; rewrite centsC centJ -sub_conjgV.
    rewrite (normsP _ _ (groupVr Ww1)) ?quotient_norms //.
      by rewrite /U1 astabQ quotient_setIpre subsetIr.
    rewrite prime_meetG //; apply/trivgPn; exists w; rewrite // !inE W1w.
    rewrite (sameP setIidPr eqP) eqEcard subsetIr /= cardJg.
    by rewrite -(leq_pmul2r a_gt0) -{2}iUCa !Lagrange //= -setIA subsetIl.
  have /trivgPn[w W1w ntw]: W1 :!=: 1%g by rewrite -cardG_gt1 prime_gt1.
  rewrite -(leq_pmul2l u_gt0) mulnn.
  have nCU1 := subset_trans sU1U nCU.
  have {1}->: u = (#|(U1 / C)%g| * a)%N.
    by rewrite mulnC /u !card_quotient // Lagrange_index.
  rewrite expnMn leq_pmul2r ?expn_gt0 ?orbF // -mulnn.
  rewrite -{2}[U1](conjsgK w) quotientJ ?groupV ?(subsetP nCW1) //.
  rewrite cardJg -TI_cardMg /= -/U1 ?subset_leq_card //.
    rewrite mul_subG ?quotientS ?subsetIl //.
    by rewrite -(normsP nUW1 w W1w) conjSg subsetIl.
  by rewrite -quotientGI // tiU1 ?trivg_quotient // !inE ntw.
pose S4 := filter [predD S_ H0C & redM] S3.
have sS43: {subset S4 <= S3} by apply: mem_subseq; apply: filter_subseq.
(* This is step (9.11.3). *)
have nsHM: H <| M by apply: gFnormal.
have oS4: (q * u * size S4 + p.-1 * (q + u))%N = (p ^ q).-1.
  rewrite mulnAC {1}[q](index_sdprod defM) -[S4]filter_predI.
  rewrite (size_irr_subseq_seqInd _ (filter_subseq _ _)) //; last first.
    by move=> xi; rewrite mem_filter -!andbA negbK => /andP[].
  set Xn := finset _; pose sumH0C := \sum_(s in X_ H0C) 'chi_s 1%g ^+ 2.
  have /eqP: sumH0C = (q * size S1 * a ^ 2 + (#|Xn| + p.-1) * u ^ 2)%:R.
    rewrite [q](index_sdprod defM) natrD natrM natrX.
    rewrite (size_irr_subseq_seqInd _ (filter_subseq _ _)) //= -/S1.
    have sH0CC': {subset S_ H0C <= S_ H0C'}.
      by apply: seqIndS; rewrite Iirr_kerDS // genS ?setUS ?der_sub.
    rewrite [sumH0C](big_setID [set s | 'Ind 'chi_s \in S1]) /=; congr (_ + _).
      rewrite mulr_natl -[rhs in _ = rhs]sumr_const; apply: eq_big => s.
        by rewrite in_setI inE andb_idl // => /H0C_S1; rewrite mem_seqInd.
      rewrite 2!inE mem_filter andbCA /= cfInd1 //  -(index_sdprod defM) natrM.
      by case/andP=> /eqP/(mulfI (neq0CG _))->.
    rewrite (eq_bigr (fun _ => u%:R ^+ 2)) => [|s]; last first.
      rewrite 2!inE eqS12 => /andP[S2's H0Cs]; congr (_ ^+ 2).
      have /S3qu/eqP: 'Ind 'chi_s \in S3.
        by rewrite mem_filter /= S2's sH0CC' ?mem_seqInd.
      by rewrite natrM cfInd1 // -(index_sdprod defM) => /(mulfI (neq0CG _)).
    rewrite sumr_const -mulr_natl natrM natrX -nb_mu; congr (_%:R * _).
    have [_ s_mu_H0C] := nb_redM_H0.
    rewrite (size_red_subseq_seqInd_typeP MtypeP _ s_mu_H0C); last first.
    - by apply/allP; apply: filter_all.
    - by rewrite filter_uniq ?seqInd_uniq.
    rewrite -/mu_ -[#|_|](cardsID Xn) (setIidPr _); last first.
      apply/subsetP=> s; rewrite inE in_setD mem_filter /= -!andbA -eqS12.
      rewrite mem_seqInd ?gFnormal // => /and4P[_ -> S1'xi _].
      by rewrite inE S1'xi.
    congr (_ + _)%N; apply: eq_card => i; rewrite inE -/mu_ 2!inE.
    rewrite -[seqInd M _]/(S_ H0C') mem_filter /= andbC 2!inE eqS12 -!andbA.
    rewrite -(mem_seqInd nsHUM) // -/(S_ H0C); set xi := 'Ind _.
    apply/idP/idP=> [/and3P[-> H0Cxi] | mu_xi].
      rewrite H0Cxi sH0CC' //= andbT negbK mem_filter unfold_in => ->.
      by rewrite (seqIndS _ H0Cxi) // Iirr_kerDS ?joing_subl.
    have [xi1u H0Cxi _] := IndHCmu _ mu_xi.
    rewrite H0Cxi -eqS12 mem_filter sH0CC' //= !andbT xi1u eqC_nat ne_qa_qu.
    by rewrite andbT negbK mem_filter in mu_xi *; case/andP: mu_xi.
  rewrite oS1 -mulnA divnK ?dvdn_mul // !mulnA -mulnDl mulnC natrM {}/sumH0C.
  rewrite /X_ -Iirr_kerDY joingC joingA (joing_idPl sH0H) /=.
  rewrite sum_Iirr_kerD_square ?genS ?setSU //; last first.
    by apply: normalS nsH0C_M; rewrite // -(sdprodWY defHU) genS ?setUSS.
  rewrite -Du (inj_eq (mulfI (neq0CG _))) -(prednK (indexg_gt0 _ _)).
  rewrite mulrSr addrK eqC_nat addnC mulnDl addnAC (mulnC q) -addnA -mulnDr.
  move/eqP <-; congr _.-1.
  have nH0HC: HC \subset 'N(H0) by rewrite join_subG nH0H.
  rewrite -(index_quotient_eq _ _ nH0HC) ?genS ?setSU //; last first.
    by rewrite setIC subIset ?joing_subl.
  rewrite quotientYidl // -(index_sdprod (dprodWsdC defHCbar)).
  by case: Ptype_Fcore_factor_facts.
have /hasP[psi1 S1psi1 _]: has predT S1 by rewrite has_predT.
pose gamma := 'Ind[M, H <*> U1] 1; pose alpha := gamma - psi1.
(* This is step (9.11.4). *)
pose nm_alpha : algC := a%:R + 1 + (q.-1 * a ^ 2)%:R / u%:R.
have [Aalpha Nalpha]: alpha \in 'CF(M, 'A(M)) /\ '[alpha] = nm_alpha.
  have sHU1_HU: H <*> U1 \subset HU by rewrite -(sdprodWY defHU) genS ?setUS.
  have sHU1_M := subset_trans sHU1_HU sHUM.
  have sHU1_A1: H <*> U1 \subset 1%g |: 'A(M).
    pose pi := \pi(H); rewrite -subDset; apply/subsetP=> y /setD1P[nty HU1y].
    apply/bigcupP; rewrite notMtype1 /=; have sHMs := Fcore_sub_FTcore maxM.
    have defHU1: H ><| U1 = H <*> U1 := sdprod_subr defHU sU1U.
    have nsH_HU1: H <| H <*> U1 by have [] := sdprod_context defHU1.
    have [HUy [_ nH_HU1]] := (subsetP sHU1_HU y HU1y, normalP nsH_HU1).
    have hallH: pi.-Hall(H <*> U1) H.
      by rewrite Hall_pi // -(coprime_sdprod_Hall_l defHU1) (coprimegS sU1U).
    have hallU1: pi^'.-Hall(H <*> U1) U1.
      by rewrite -(compl_pHall _ hallH) sdprod_compl.
    have [pi'y | pi_y] := boolP (pi^'.-elt y); last first.
      exists y.`_pi; last by rewrite 3!inE nty HUy cent1C groupX ?cent1id.
      rewrite !inE (sameP eqP constt1P) pi_y (subsetP sHMs) //.
      by rewrite (mem_normal_Hall hallH) ?groupX ?p_elt_constt.
    have solHU1: solvable (H <*> U1) by rewrite (solvableS sHU1_M) ?mmax_sol.
    have [||z HU1z U1yz] := Hall_Jsub _ hallU1 _ pi'y; rewrite ?cycle_subG //.
    have /trivgPn[x /setIP[Hx cxyz] ntx]: 'C_H[y ^ z] != 1%g.
      apply: contraTneq (prime_gt1 p_pr) => regHy; rewrite -oH1 cardG_gt1 negbK.
      move: U1yz; rewrite -cycleJ subsetI sub_astabQ => /and3P[sYU nHY cH1Y].
      rewrite centsC in cH1Y; rewrite -(setIidPl cH1Y) -(setIidPl sH1H) -setIA.
      rewrite -coprime_quotient_cent ?(coprimegS sYU) // cent_cycle regHy.
      by rewrite quotient1 setIg1.
    exists (x ^ z^-1)%g; last by rewrite 3!inE nty HUy cent1J mem_conjgV cent1C.
    by rewrite 2!inE conjg_eq1 ntx (subsetP sHMs) // -mem_conjg nH_HU1.
  have{sHU1_A1} Aalpha: alpha \in 'CF(M, 'A(M)).
    have A'1: 1%g \notin 'A(M) by have /subsetD1P[] := FTsupp_sub M.
    rewrite -['A(M)](setU1K A'1) cfun_onD1 !cfunE subr_eq0 cfInd1 // cfun11.
    rewrite mulr1 -(Lagrange_index sHUM) // -(index_sdprod defM) -/q.
    rewrite -(index_sdprodr defHU) ?subsetIl // -/a eq_sym andbC.
    have:= S1psi1; rewrite mem_filter /= => /andP[-> _] /=.
    rewrite rpredB //.
      apply: cfun_onS (cfInd_on sHU1_M (cfun_onG _)).
      rewrite class_supportEr; apply/bigcupsP=> w Mw.
      by rewrite sub_conjg conjUg conjs1g (normsP (FTsupp_norm M)) ?groupV.
    have /seqIndP[s /setDP[_ ker'H ] ->] := H0C_S1 _ S1psi1.
    rewrite (prDade_Ind_irr_on (FT_prDade_hypF maxM MtypeP)) //.
    by rewrite inE in ker'H.
  have ->: '[alpha] = '[gamma] + 1.
    have /irrP[t Dt] := irrS1 _ S1psi1.
    rewrite cfnormBd; first by rewrite Dt cfnorm_irr.
    have /seqIndP[s /setDP[_ ker'H ] Dpsi1] := H0C_S1 _ S1psi1.
    apply: contraNeq ker'H; rewrite Dt /gamma -irr0 -irr_consttE => tHU1_0.
    rewrite inE -(sub_cfker_Ind_irr _ sHUM) ?gFnorm // -Dpsi1 Dt.
    rewrite -(sub_cfker_constt_Ind_irr tHU1_0) ?gFnorm ?joing_subl //.
    by rewrite irr0 cfker_cfun1 joing_subl.
  split=> //; rewrite /nm_alpha addrAC natrM mulrAC mulrC; congr (_ + 1).
  rewrite -{1}(mulnK a a_gt0) natf_div ?dvdn_mull // -mulrDr mulnn natrX.
  have /sdprod_isom[nH_UW1 isomMH]: H ><| (U <*> W1) = M.
    rewrite sdprodEY ?join_subG ?nHU ?(subset_trans sW1M) ?gFnorm //.
      by rewrite joingA (sdprodWY defHU) (sdprodWY defM).
    rewrite /= -(setIidPl sHHU) norm_joinEr // setIAC -setIA -group_modl //.
    by rewrite (setIC W1) tiHUW1 mulg1.
  have sU1_UW1: U1 \subset U <*> W1 by rewrite subIset ?joing_subl.
  rewrite /gamma -(cfMod_cfun1 _ H) cfIndMod ?joing_subl //.
  rewrite cfMod_iso //= quotientYidl ?(subset_trans sU1_UW1) //.
  rewrite -(restrm_quotientE _ sU1_UW1) -(cfIsom_cfun1 (restr_isom _ isomMH)).
  rewrite (cfIndIsom isomMH) // {nH_UW1 isomMH}cfIsom_iso.
  rewrite -(cfIndInd _ (joing_subl U W1)) // cfInd_cfun1 //= -/U1 -/a.
  rewrite linearZ cfnormZ normr_nat /=; congr (_ * _).
  have defUW1: U ><| W1 = U <*> W1.
    by rewrite sdprodEY // -(setIidPl sUHU) -setIA tiHUW1 setIg1.
  apply: canLR (mulKf (neq0CG _)) _; rewrite -(sdprod_card defUW1) natrM -/q.
  rewrite mulrAC mulrDr mulrCA -{1}(Lagrange sU1U) /= -/U1 -/a -(Lagrange sCU).
  rewrite -card_quotient // !natrM !mulfK ?neq0CiG ?neq0CG //.
  transitivity (\sum_(x in U <*> W1) \sum_(w1 in W1) \sum_(w2 in W1)
                  (x ^ w1 \in U1 :&: U1 :^ w2)%g%:R : algC).
  - apply: eq_bigr => x _; rewrite (cfIndEsdprod _ _ defUW1) mulr_suml.
    apply: eq_bigr => w1 W1w1; rewrite rmorph_sum mulr_sumr.
    rewrite (reindex_inj invg_inj) (eq_bigl _ _ (groupV W1)) /=.
    rewrite (reindex_acts 'R _ (groupVr W1w1)) ?astabsR //=.
    apply: eq_bigr => w2 _; rewrite inE !cfuniE // rmorph_nat -natrM mulnb.
    by congr (_ && _)%:R; rewrite invMg invgK conjgM -mem_conjg.
  rewrite exchange_big /= mulr_natr -sumr_const; apply: eq_bigr => w1 W1w1.
  transitivity (\sum_(w in W1) #|U1 :&: U1 :^ w|%:R : algC).
    rewrite exchange_big /=; apply: eq_bigr => w W1w.
    rewrite (reindex_acts 'J _ (groupVr W1w1)) ?astabsJ ?normsG ?joing_subr //=.
    symmetry; rewrite big_mkcond -sumr_const /= big_mkcond /=.
    apply: eq_bigr => x _; rewrite conjgKV.
    by case: setIP => [[/(subsetP sU1_UW1)-> //] | _]; rewrite if_same.
  rewrite (big_setD1 1%g) //= conjsg1 setIid; congr (_ + _).
  rewrite [q](cardsD1 1%g) group1 /= mulr_natl -sumr_const.
  by apply: eq_bigr => w W1w; rewrite tiU1.
(* This is step (9.11.5). *)
have [gtS4alpha s4gt0]: (size S4)%:R > '[alpha] /\ (size S4 > 0)%N.
  suffices gtS4alpha: (size S4)%:R > '[alpha].
    by split=> //; rewrite -ltC_nat (ler_lt_trans (cfnorm_ge0 alpha)).
  rewrite Nalpha -(@ltr_pmul2r _ u%:R) ?ltr0n // mulrDl divfK ?neq0CG //.
  rewrite -(ltr_pmul2l (gt0CG W1)) -/q -mulrSr -!(natrM, natrD) ltC_nat.
  rewrite mulnA mulnAC -(ltn_add2r (p.-1 * (q + u))) oS4 {1}Dp addn1 -Da_p /=.
  apply: leq_ltn_trans (_ : q.+2 * a ^ 3 + q ^ 2 * a ^ 2 + 2 * q * a < _)%N.
    rewrite (addnC q) 2!mulnDr addnA (mulnAC _ a q) leq_add2r.
    rewrite mulnA addnAC -mulnDl mulnS -addnA -mulnDl addn2 mulnCA -mulnA.
    rewrite -[q in (_ <= _ + q * _)%N](prednK q_gt0) (mulSn q.-1) addnA.
     by rewrite leq_add2r mulnA -mulnDl addnC leq_mul.
  have q_gt2: (2 < q)%N.
    by rewrite ltn_neqAle prime_gt1 ?(contraTneq _ odd_q) => // <-.
  apply: leq_trans (_ : a.*2 ^ q + 'C(q, 2) * a.*2 ^ 2 + q * a.*2 <= _)%N.
    rewrite -mul2n (mulnCA q) (mulnA 2) ltn_add2r !expnMn -addSn leq_add //.
      apply: leq_ltn_trans (_ : q.-1.*2.+1 * a ^ q < _)%N.
        rewrite leq_mul ?leq_pexp2l //.
        by rewrite -(subnKC q_gt2) -addnn !addnS !ltnS leq_addl.
      rewrite ltn_pmul2r ?expn_gt0 ?a_gt0 // -doubleS.
      by rewrite -(prednK q_gt0) expnS mul2n leq_double ltn_expl.
    rewrite mulnA leq_pmul2r ?expn_gt0 ?a_gt0 // -(subnKC q_gt2).
    rewrite mulnCA mulnA addSn -mul_Sm_binm bin1 -mulnA leq_pmul2l //.
    by rewrite mulnS -addSnnS leq_addr.
  rewrite Dp -Da_p mul2n (addnC a.*2) expnDn -(subnKC q_gt2) !addSn add0n.
  rewrite 3!big_ord_recl big_ord_recr /= !exp1n /= bin1 binn !mul1n /bump /=.
  by do 2!rewrite addnC leq_add2l; apply: leq_addl.
have{cohS1} [tau1 cohS1] := cohS1; have [[Itau1 Ztau1] Dtau1] := cohS1.
have sS30: cfConjC_subset S3 (S_ H0C').
  split=> [|chi|chi]; first by rewrite filter_uniq ?seqInd_uniq.
    by rewrite mem_filter => /andP[].
  rewrite !mem_filter /= -!eqS12 => /andP[S1'chi S_chi].
  rewrite cfAut_seqInd // (contra _ S1'chi) //.
  by have [_ _ ccS1] := sS10; move/ccS1; rewrite cfConjCK.
have scohS3: subcoherent S3 tau rmR := subset_subcoherent scohS0 sS30.
have [tau3 cohS3]: coherent S3 M^# tau.
  apply: uniform_degree_coherence scohS3 _.
  apply: all_pred1_constant (q * u)%:R _ _.
  by rewrite all_map; apply/allP=> chi /S3qu.
have [IZtau3 Dtau3] := cohS3; have [Itau3 Ztau3] := IZtau3.
have notA1: 1%g \notin 'A(M) by have /subsetD1P[] := FTsupp_sub M.
have sS0_1A: {subset S_ H0C' <= 'CF(M, 1%g |: 'A(M))}.
  move=> _ /seqIndP[s /setDP[_ ker'H] ->]; rewrite inE in ker'H.
  by rewrite (prDade_Ind_irr_on (FT_prDade_hypF maxM MtypeP)).
have sS0A: {subset 'Z[S_ H0C', M^#] <= 'Z[irr M, 'A(M)]}.
  move=> chi; rewrite (zcharD1_seqInd_Dade _ notA1) //.
  by apply: zchar_sub_irr; apply: seqInd_vcharW.
have Zalpha: alpha \in 'Z[irr M].
  rewrite rpredB ?char_vchar ?cfInd_char ?rpred1 //.
  exact: seqInd_char (H0C_S1 _ S1psi1).
have ZAalpha: alpha \in 'Z[irr M, 'A(M)] by rewrite zchar_split Zalpha.
have [Itau Ztau]: {in 'Z[irr M, 'A(M)], isometry tau, to 'Z[irr G]}.
  apply: sub_iso_to (Dade_Zisometry _); last exact: zcharW.
  by apply: zchar_onS; apply: FTsupp_sub0.
have oSgamma: {in S_ H0C', forall lam, '[gamma, lam] = 0}.
  move=> _ /seqIndP[s /setDP[_ ker'H ] ->].
  rewrite ['Ind _]cfun_sum_constt cfdot_sumr big1 // => t sMt.
  rewrite cfdotZr [gamma]cfun_sum_constt cfdot_suml big1 ?mulr0 // => t0 gMt0.
  rewrite cfdotZl cfdot_irr (negPf (contraNneq _ ker'H)) ?mulr0 // => Dt0.
  rewrite inE (sub_cfker_constt_Ind_irr sMt) ?gFnorm // -Dt0.
  rewrite /gamma -irr0 in gMt0.
  rewrite -(sub_cfker_constt_Ind_irr gMt0) ?gFnorm ?joing_subl //.
    by rewrite irr0 cfker_cfun1 joing_subl.
  by rewrite (subset_trans _ sHUM) // join_subG sHHU subIset ?sUHU.
(* This is step (9.11.6). *)
have [/eqP psi1qa Spsi1]: psi1 1%g == (q * a)%:R /\ psi1 \in S_ H0C'.
  by move: S1psi1; rewrite mem_filter => /andP[].
have o_alpha_S3: orthogonal alpha^\tau (map tau3 S3).
  rewrite /orthogonal /= andbT all_map.
  apply: contraFT (ltr_geF gtS4alpha) => /allPn[lam0 S3lam0 /= alpha_lam0].
  set ca := '[_, _] in alpha_lam0; pose al0 := (-1) ^+ (ca < 0)%R *: alpha.
  have{alpha_lam0} al0_lam0: '[al0^\tau, tau3 lam0] > 0.
    have Zca: ca \in Cint by rewrite Cint_cfdot_vchar ?Ztau // Ztau3 ?mem_zchar.
    by rewrite linearZ cfdotZl (canLR (signrMK _) (CintEsign Zca)) normr_gt0.
  rewrite -Itau // -(cfnorm_sign (ca < 0)%R) -linearZ /= -/al0.
  have S4_dIirrK: {in map tau3 S4, cancel (dirr_dIirr id) (@dchi _ _)}.
    apply: dirr_dIirrPE => _ /mapP[lam S4lam ->].
    rewrite mem_filter -andbA negbK in S4lam.
    have [/irrP[i Dlam] _ S3lam] := and3P S4lam.
    by rewrite dirrE Itau3 ?Ztau3 ?mem_zchar //= Dlam cfnorm_irr.
  rewrite -(size_map tau3) -(size_map (dirr_dIirr id)).
  rewrite -(card_uniqP _); last first.
    rewrite !map_inj_in_uniq ?filter_uniq ?seqInd_uniq //.
      apply: sub_in2 (Zisometry_inj Itau3) => lam.
      by rewrite mem_filter => /andP[_ /mem_zchar->].
    exact: can_in_inj S4_dIirrK.
  apply: ler_trans (_ : #|dirr_constt al0^\tau|%:R <= _); last first.
    have Zal0: al0^\tau \in 'Z[irr G] by rewrite Ztau ?rpredZsign.
    rewrite cnorm_dconstt // -sumr_const ler_sum // => i al0_i.
    by rewrite sqr_Cint_ge1 ?gtr_eqF -?dirr_consttE // Cint_Cnat ?Cnat_dirr.
  rewrite leC_nat subset_leq_card //; apply/subsetP=> _ /mapP[nu S4nu ->].
  rewrite dirr_consttE S4_dIirrK //; congr (_ > 0): al0_lam0.
  rewrite {al0}linearZ !cfdotZl /=; congr (_ * _) => {ca}; apply/eqP.
  have{nu S4nu} [lam S4lam ->] := mapP S4nu.
  rewrite mem_filter in S4lam; have{S4lam} [_ S3lam] := andP S4lam.
  have Zdlam: lam0 - lam \in 'Z[S3, M^#].
    rewrite zcharD1E rpredB ?mem_zchar //= !cfunE subr_eq0.
    by have [/eqP->] := (S3qu _ S3lam, S3qu _ S3lam0).
  rewrite -subr_eq0 -cfdotBr -raddfB Dtau3 //.
  rewrite Itau // ?sS0A //; last exact: zchar_filter Zdlam.
  suffices{lam S3lam Zdlam} oS3a: {in S3, forall lam, '[alpha, lam] = 0}.
    by rewrite cfdotBr subr_eq0 !oS3a.
  move=> lam; rewrite mem_filter /= -eqS12 => /andP[S1'lam H0C'lam].
  by rewrite cfdotBl oSgamma // (seqInd_ortho _ Spsi1) ?(memPn S1'lam) // subr0.
have{s4gt0 gtS4alpha} /hasP[lam1 S4lam1 _]: has predT S4 by rewrite has_predT.
have [/irrP[l1 Dl1] S3lam1]: lam1 \in irr M /\ lam1 \in S3.
  by move: S4lam1; rewrite mem_filter -andbA negbK => /and3P[].
have [S1'lam1 Slam1]: lam1 \notin S1 /\ lam1 \in S_ H0C'.
  by move: S3lam1; rewrite mem_filter eqS12 => /andP[].
have S3lam1s: lam1^*%CF \in S3 by have [[_ _ ->]] := scohS3.
have ZS3dlam1: lam1 - lam1^*%CF \in 'Z[S3, M^#].
  rewrite zcharD1E rpredB ?mem_zchar //.
  by have:= seqInd_sub_aut_zchar nsHUM conjC Slam1; rewrite zcharD1 => /andP[].
have ZAdlam1: lam1 - lam1^*%CF \in 'Z[irr M, 'A(M)].
  rewrite sS0A // zchar_split rpredB ?mem_zchar ?cfAut_seqInd //.
  by rewrite (zchar_on ZS3dlam1).
pose beta := lam1 - (u %/ a)%:R *: psi1.
have ZAbeta: beta \in 'Z[irr M, 'A(M)].
  apply: sS0A; rewrite zcharD1E rpredB ?scaler_nat ?rpredMn ?mem_zchar //=.
  by rewrite !cfunE subr_eq0 psi1qa -natrM mulnCA divnK // S3qu.
have [_ _ poSS _ _] := scohS0; have [_ oSS] := pairwise_orthogonalP poSS.
have o1S1: orthonormal S1.
  rewrite orthonormalE filter_pairwise_orthogonal // andbT.
  by apply/allP=> _ /irrS1/irrP[t ->]; rewrite /= cfnorm_irr.
have o1S4: orthonormal S4.
  rewrite orthonormalE !filter_pairwise_orthogonal // andbT.
  apply/allP=> nu; rewrite mem_filter /= -andbA negbK.
  by case/andP=> /irrP[t ->]; rewrite cfnorm_irr.
have n1psi1: '[psi1] = 1 by have [_ -> //] := orthonormalP o1S1; rewrite eqxx.
have n1lam1: '[lam1] = 1 by have [_ -> //] := orthonormalP o1S4; rewrite eqxx.
have oS14tau: orthogonal (map tau1 S1) (map tau3 S4).
  apply/orthogonalP=> psi _ S1psi /mapP[lam /sS43 S3lam ->].
  apply: {psi lam S3lam}orthogonalP S1psi (map_f tau3 S3lam).
  apply: (coherent_ortho scohS0 sS10 cohS1 sS30 cohS3) => psi /=.
  by rewrite mem_filter !inE eqS12 => /andP[-> _].
have [Gamma [S4_Gamma normGamma [b Dbeta]]]:
  exists Gamma, [/\ Gamma \in 'Z[map tau3 S4], '[Gamma] = 1
    & exists b : bool, beta^\tau
        = Gamma - (u %/ a)%:R *: tau1 psi1 + b%:R *: \sum_(psi <- S1) tau1 psi].
- have [G S4G [G' [Dbeta _ oG'4]]] := orthogonal_split (map tau3 S4) beta^\tau.
  have [B S1B [Delta [dG' _ oD1]]] := orthogonal_split (map tau1 S1) G'.
  have sZS43: {subset 'Z[S4] <= 'Z[S3]} := zchar_subset sS43.
  have [Itau34 Ztau34] := sub_iso_to sZS43 sub_refl IZtau3.
  have Z_G: G \in 'Z[map tau3 S4].
    have [_ -> ->] := orthonormal_span (map_orthonormal Itau34 o1S4) S4G.
    rewrite big_seq rpred_sum // => xi S4xi; rewrite rpredZ_Cint ?mem_zchar //.
    rewrite -(addrK G' G) -Dbeta cfdotBl (orthoPl oG'4) // subr0.
    rewrite Cint_cfdot_vchar ?Ztau //.
    by have{xi S4xi} [xi S4xi ->] := mapP S4xi; rewrite Ztau34 ?mem_zchar.
  have oD4: orthogonal Delta (map tau3 S4).
    apply/orthoPl=> xi S4xi; rewrite -(addKr B Delta) addrC -dG' cfdotBl.
    by rewrite (orthoPl oG'4) // (span_orthogonal oS14tau) ?subrr // memv_span.
  have [_ -> dB] := orthonormal_span (map_orthonormal Itau1 o1S1) S1B.
  pose b := (u %/ a)%:R + '[B, tau1 psi1].
  have betaS1_B: {in S1, forall psi, '[beta^\tau, tau1 psi] = '[B, tau1 psi]}.
    move=> psi S1psi; rewrite Dbeta dG' !cfdotDl (orthoPl oD1) ?map_f // addr0.
    rewrite cfdotC (span_orthogonal oS14tau) ?rmorph0 ?add0r //.
    by rewrite memv_span ?map_f.
  have Zb: b \in Cint.
    rewrite rpredD ?rpred_nat // -betaS1_B // Cint_cfdot_vchar ?Ztau //.
    by rewrite Ztau1 ?mem_zchar.
  have{dB} dB: B = - (u %/ a)%:R *: tau1 psi1 + b *: \sum_(psi <- S1) tau1 psi.
    rewrite dB big_map !(big_rem _ S1psi1) /= scalerDr addrA -scalerDl addKr.
    rewrite scaler_sumr; congr (_ + _); apply: eq_big_seq => psi.
    rewrite mem_rem_uniq ?filter_uniq ?seqInd_uniq // => /andP[/= psi_1' S1psi].
    apply/esym/eqP; rewrite -subr_eq0 -scalerBl -addrA -!betaS1_B // -cfdotBr.
    have [/eqP psi_qa Spsi]: psi 1%g == (q * a)%:R /\ psi \in S_ H0C'.
      by move: S1psi; rewrite mem_filter => /andP[].
    have Z1dpsi: psi1 - psi \in 'Z[S1, M^#].
      by rewrite zcharD1E rpredB ?mem_zchar //= !cfunE psi1qa psi_qa subrr.
    rewrite -raddfB Dtau1 // Itau //; last first.
      by rewrite sS0A // zchar_split rpredB ?mem_zchar ?(zchar_on Z1dpsi).
    rewrite cfdotC cfdotBr cfdotZr !cfdotBl 2?oSS ?(memPn S1'lam1) // subrr.
    by rewrite add0r n1psi1 oSS // subr0 mulr1 rmorphN conjCK subrr scale0r.
  have Gge1: 1 <= '[G] ?= iff ('[G] == 1).
    rewrite eq_sym; apply: lerif_eq.
    have N_G: '[G] \in Cnat.
      apply: Cnat_cfnorm_vchar; apply: zchar_sub_irr Z_G => _ /mapP[nu S4nu ->].
      by rewrite Ztau34 ?mem_zchar.
    rewrite -(truncCK N_G) ler1n lt0n -eqC_nat truncCK {N_G}// cfnorm_eq0.
    have: '[beta^\tau, (lam1 - lam1^*%CF)^\tau] != 0.
      rewrite Itau // cfdotBl cfdotZl !cfdotBr n1lam1.
      rewrite (seqInd_conjC_ortho _ _ _ Slam1) ?mFT_odd // subr0.
      rewrite !oSS ?cfAut_seqInd -?(inv_eq (@cfConjCK _ _)) ?(memPn S1'lam1) //.
        by rewrite !(subr0, mulr0) oner_eq0.
      by have [_ _ ->] := sS10.
    rewrite Dbeta -Dtau3 //; apply: contraNneq => ->.
    rewrite add0r raddfB cfdotBr !(orthoPl oG'4) ?map_f ?subr0 //.
    rewrite mem_filter /= negbK /= S3lam1s irr_aut.
    move: S4lam1; rewrite mem_filter /= negbK /= -andbA => /and3P[-> H0Clam1 _].
    by rewrite cfAut_seqInd.
  have ubG: '[G] + (b ^+ 2 - b) * (u %/ a).*2%:R + '[Delta] = 1.
    apply: (addrI ((u %/ a) ^ 2)%:R); transitivity '[beta^\tau].
      rewrite -!addrA addrCA Dbeta cfnormDd; last first.
        by rewrite cfdotC (span_orthogonal oG'4) ?rmorph0 // memv_span ?inE.
      congr (_ + _); rewrite !addrA dG' cfnormDd; last first.
        by rewrite cfdotC (span_orthogonal oD1) ?rmorph0 // memv_span ?inE.
      congr (_ + _); rewrite dB scaleNr [- _ + _]addrC cfnormB !cfnormZ.
      rewrite normr_nat Cint_normK // scaler_sumr cfdotZr rmorph_nat.
      rewrite cfnorm_map_orthonormal // cfproj_sum_orthonormal //.
      rewrite Itau1 ?mem_zchar // n1psi1 mulr1 rmorphM rmorph_nat conj_Cint //.
      rewrite -mulr2n oS1ua -muln_divA // mul2n -addrA addrCA -natrX mulrBl.
      by congr (_ + (_ - _)); rewrite -mulrnAl -mulrnA muln2 mulrC.
    rewrite Itau // cfnormBd; last first.
      by rewrite cfdotZr oSS ?mulr0 // (memPnC S1'lam1).
    by rewrite cfnormZ normr_nat n1psi1 n1lam1 mulr1 addrC -natrX.
  have ubDelta: '[G] <= '[G] + '[Delta] ?= iff (Delta == 0).
    rewrite addrC -lerif_subLR subrr -cfnorm_eq0 eq_sym.
    by apply: lerif_eq; apply: cfnorm_ge0.
  have{ubG} ubDeltaG: '[G] + '[Delta] <= 1 ?= iff pred2 0 1 b.
    rewrite -{1}ubG addrAC [_ + _ + _] addrC -lerif_subLR subrr /=.
    set n := _%:R; rewrite mulrC -{1}(mulr0 n) mono_lerif; last first.
      by apply: ler_pmul2l; rewrite ltr0n double_gt0 divn_gt0 // dvdn_leq.
    rewrite /= -(subr_eq0 b 1) -mulf_eq0 mulrBr mulr1 eq_sym.
    apply: lerif_eq; rewrite subr_ge0.
    have [-> | nz_b] := eqVneq b 0; first by rewrite expr2 mul0r.
    rewrite (ler_trans (real_ler_norm _)) ?Creal_Cint // -[`|b|]mulr1.
    by rewrite -Cint_normK // ler_pmul2l ?normr_gt0 // norm_Cint_ge1.
  have [_ /esym] := lerif_trans Gge1 (lerif_trans ubDelta ubDeltaG).
  rewrite eqxx => /and3P[/eqP normG1 /eqP Delta0 /pred2P b01].
  exists G; split=> //; exists (b != 0).
  rewrite Dbeta dG' Delta0 addr0 dB scaleNr addrA; congr (_ + _ *: _).
  by case: b01 => ->; rewrite ?eqxx ?oner_eq0.
(* Final step (9.11.8). *)
have alpha_beta: '[alpha^\tau, beta^\tau] = (u %/ a)%:R.
  rewrite Itau // cfdotBr cfdotZr rmorph_nat !cfdotBl !oSgamma // !sub0r.
  by rewrite n1psi1 mulrN opprK mulr1 addrC oSS ?subr0 // (memPn S1'lam1).
have [X S1X [Delta [Dalpha _ oD1]]]:= orthogonal_split (map tau1 S1) alpha^\tau.
pose x := 1 + '[X, tau1 psi1].
have alphaS1_X: {in S1, forall psi, '[alpha^\tau, tau1 psi] = '[X, tau1 psi]}.
  by move=> psi S1psi; rewrite Dalpha cfdotDl (orthoPl oD1) ?map_f // addr0.
have Zx: x \in Cint.
  rewrite rpredD ?rpred1 // -alphaS1_X // Cint_cfdot_vchar ?Ztau //.
  by rewrite Ztau1 ?mem_zchar.
have{alphaS1_X S1X} defX: X = x *: (\sum_(psi <- S1) tau1 psi) - tau1 psi1.
  have [_ -> ->] := orthonormal_span (map_orthonormal Itau1 o1S1) S1X.
  rewrite addrC -scaleN1r big_map !(big_rem _ S1psi1) /= scalerDr addrA.
  rewrite -scalerDl addKr scaler_sumr; congr (_ + _); apply: eq_big_seq => psi.
  rewrite mem_rem_uniq ?filter_uniq ?seqInd_uniq // => /andP[/= psi_1' S1psi].
  apply/esym/eqP; rewrite -subr_eq0 -scalerBl -addrA -!alphaS1_X // -cfdotBr.
  have [/eqP psi_qa Spsi]: psi 1%g == (q * a)%:R /\ psi \in S_ H0C'.
    by move: S1psi; rewrite mem_filter => /andP[].
  have Z1dpsi: psi1 - psi \in 'Z[S1, M^#].
    by rewrite zcharD1E rpredB ?mem_zchar //= !cfunE psi1qa psi_qa subrr.
  rewrite -raddfB Dtau1 // Itau //; last first.
    by rewrite sS0A // zchar_split rpredB ?mem_zchar ?(zchar_on Z1dpsi).
  rewrite cfdotBr !cfdotBl !oSgamma // n1psi1 cfdotC oSS // rmorph0.
  by rewrite !subr0 add0r subrr scale0r.
have{x Zx X defX Delta Dalpha oD1} b_mod_ua: (b == 0 %[mod u %/ a])%C.
  rewrite -oppr0 -eqCmodN (eqCmod_trans _ (eqCmodm0 _)) // {2}nCdivE.
  rewrite -alpha_beta Dbeta -addrA cfdotDr.
  rewrite (span_orthogonal o_alpha_S3) ?add0r; first 1 last.
  - by rewrite memv_span ?inE.
  - apply: subvP (zchar_span S4_Gamma); apply: sub_span; apply: mem_subseq.
    by rewrite map_subseq ?filter_subseq.
  rewrite Dalpha addrC cfdotDl (span_orthogonal oD1); first 1 last.
  - by rewrite memv_span ?inE.
  - rewrite addrC rpredB ?rpredZ //; last by rewrite memv_span ?map_f.
    by rewrite big_seq rpred_sum // => psi S1psi; rewrite memv_span ?map_f.
  rewrite add0r addrC defX cfdotBr cfdotBl cfdotZl cfdotZr !scaler_sumr.
  rewrite cfdotZr !rmorph_nat cfdotBl Itau1 ?mem_zchar // n1psi1.
  rewrite cfnorm_map_orthonormal // cfdotC !cfproj_sum_orthonormal //.
  rewrite rmorph_nat oS1ua -muln_divA // natrM !mulrA addrC mulrC addrA.
  rewrite -mulNr -mulrDl eqCmod_sym eqCmod_addl_mul // addrC !rpredB ?rpred1 //.
  by rewrite !rpredM ?rpred_nat.
have{b_mod_ua alpha_beta} b0: b = 0%N :> nat.
  have:= b_mod_ua; rewrite /eqCmod subr0 dvdC_nat => /eqnP.
  rewrite modn_small // (leq_ltn_trans (leq_b1 b)) // ltn_divRL // mul1n.
  by rewrite ltn_neqAle -(eqn_pmul2l q_gt0) eq_sym ne_qa_qu dvdn_leq.
exists lam1 => //; suffices: coherent (lam1 :: lam1^* :: S1)%CF M^# tau.
  by apply: subset_coherent => phi; rewrite !inE eqS12.
move: Dbeta; rewrite b0 scale0r addr0.
apply: (extend_coherent_with scohS0 sS10 cohS1); first by [].
rewrite rpred_nat psi1qa -natrM mulnCA (eqP (S3qu _ S3lam1)) divnK //.
rewrite cfdotC (span_orthogonal oS14tau) ?(zchar_span S4_Gamma) ?conjC0 //.
by rewrite rpredZ ?memv_span ?map_f.
Qed.

End Nine.

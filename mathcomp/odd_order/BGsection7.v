(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div fintype bigop.
Require Import finset prime fingroup morphism automorphism action quotient.
Require Import gfunctor cyclic pgroup center commutator gseries nilpotent.
Require Import sylow abelian maximal hall.
Require Import BGsection1 BGsection6.

(******************************************************************************)
(*   This file covers B & G, section 7, i.e., the proof of the Thompson       *)
(* Transitivity Theorem, as well as some generalisations used later in the    *)
(* proof.                                                                     *)
(*   This is the first section of the proof that applies to a (hypothetical)  *)
(* minimally simple odd group, so we also introduce at this point some        *)
(* infrastructure to carry over this assumption into the rest of the proof.   *)
(*   minSimpleOddGroupType == a finGroupType that ranges exactly over the     *)
(*                            elements of a minimal counter-example to the    *)
(*                            Odd Order Theorem.                              *)
(*                       G == the group of all the elements in a              *)
(*                            minSimpleOddGroupType (this is a local notation *)
(*                            that must be reestablished for each such Type). *)
(*                      'M == the set of all (proper) maximal subgroups of G  *)
(*                   'M(H) == the set of all elements of 'M that contain H    *)
(*                      'U == the set of all H such that 'M(H) contains a     *)
(*                            single (unique) maximal subgroup of G.          *)
(*               'SCN_n[p] == the set of all SCN subgroups of rank at least n *)
(*                            of all the Sylow p-subgroups of G.              *)
(*            |/|_H(A, pi) == the set of all pi-subgroups of H that are       *)
(*                            normalised by A.                                *)
(*             |/|*(A, pi) == the set of pi-subgroups of G, normalised by A,  *)
(*                            and maximal subject to this condition.          *)
(*    normed_constrained A == A is a nontrivial proper subgroup of G, such    *)
(*                            that for any proper subgroup X containing A,    *)
(*                            all Y in |/|_X(A, pi') lie in the pi'-core of X *)
(*                            (here pi is the set of prime divisors of #|A|). *)
(*                            This is Hypothesis 7.1 in B & G.                *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Reserved Notation "''M'" (at level 8, format "''M'").
Reserved Notation "''M' ( H )" (at level 8, format "''M' ( H )").
Reserved Notation "''U'" (at level 8).
Reserved Notation "''SCN_' n [ p ]"
  (at level 8, n at level 2, format "''SCN_' n [ p ]").
Reserved Notation "|/|_ X ( A ; pi )"
  (at level 8, X at level 2, format "|/|_ X ( A ;  pi )").
Reserved Notation "|/|* ( A ; pi )"
  (at level 8, format "|/|* ( A ;  pi )").

(* The generic setup for the whole Odd Order Theorem proof. *)
Section InitialReduction.

Implicit Type gT : finGroupType.

Record minSimpleOddGroupMixin gT : Prop := MinSimpleOddGroupMixin {
  _ : odd #|[set: gT]|;
  _ : simple [set: gT];
  _ : ~~ solvable [set: gT];
  _ : forall M : {group gT}, M \proper [set: gT] -> solvable M
}.

Structure minSimpleOddGroupType := MinSimpleOddGroupType {
  minSimpleOddGroupType_base :> finGroupType;
  _ : minSimpleOddGroupMixin minSimpleOddGroupType_base
}.

Hypothesis IH_FT : minSimpleOddGroupType -> False.

Lemma minSimpleOdd_ind gT (G : {group gT}) : odd #|G| -> solvable G.
Proof.
move: {2}_.+1 (ltnSn #|G|) => n.
elim: n => // n IHn in gT G *; rewrite ltnS => leGn oddG.
have oG: #|[subg G]| = #|G| by rewrite (card_isog (isog_subg G)).
apply/idPn=> nsolG; case: IH_FT; exists [finGroupType of subg_of G].
do [split; rewrite ?oG //=] => [||M].
- rewrite -(isog_simple (isog_subg _)); apply/simpleP; split=> [|H nsHG].
    by apply: contra nsolG; move/eqP->; rewrite abelian_sol ?abelian1.
  have [sHG _]:= andP nsHG; apply/pred2P; apply: contraR nsolG; case/norP=> ntH.
  rewrite eqEcard sHG -ltnNge (series_sol nsHG) => ltHG.
  by rewrite !IHn ?(oddSg sHG) ?quotient_odd ?(leq_trans _ leGn) ?ltn_quotient.
- by apply: contra nsolG => solG; rewrite -(im_sgval G) morphim_sol.
rewrite properEcard oG; case/andP=> sMG ltMG.
by apply: IHn (leq_trans ltMG leGn) (oddSg sMG _); rewrite oG.
Qed.

Lemma minSimpleOdd_prime gT (G : {group gT}) :
  odd #|G| -> simple G -> prime #|G|.
Proof. by move/minSimpleOdd_ind; apply: simple_sol_prime. Qed.

End InitialReduction.

Notation TheMinSimpleOddGroup gT :=
    [set: FinGroup.arg_sort (FinGroup.base (minSimpleOddGroupType_base gT))]
  (only parsing).

(* Elementary properties of the minimal counter example. *)
Section MinSimpleOdd.

Variable gT : minSimpleOddGroupType.
Notation G := (TheMinSimpleOddGroup gT).
Implicit Types H K D M P U V X : {group gT}.
Local Notation sT := {set gT}.
Implicit Type p : nat.

Lemma mFT_odd H : odd #|H|.
Proof. by apply: (oddSg (subsetT H)); case: gT => ? []. Qed.

Lemma mFT_simple : simple G.
Proof. by case: gT => ? []. Qed.

Lemma mFT_nonSolvable : ~~ solvable G.
Proof. by case: gT => ? []. Qed.

Lemma mFT_sol M : M \proper G -> solvable M.
Proof. by case: gT M => ? []. Qed.

Lemma mFT_nonAbelian : ~~ abelian G.
Proof. apply: contra mFT_nonSolvable; exact: abelian_sol. Qed.

Lemma mFT_neq1 : G != 1.
Proof. by apply: contraNneq mFT_nonAbelian => ->; exact: abelian1. Qed.

Lemma mFT_gt1 : [1] \proper G. Proof. by rewrite proper1G mFT_neq1. Qed.

Lemma mFT_quo_odd M H : odd #|M / H|.
Proof. by rewrite quotient_odd ?mFT_odd. Qed.

Lemma mFT_sol_proper M : (M \proper G) = solvable M.
Proof.
apply/idP/idP; first exact: mFT_sol.
by rewrite properT; apply: contraL; move/eqP->; exact: mFT_nonSolvable.
Qed.

Lemma mFT_pgroup_proper p P : p.-group P -> P \proper G.
Proof. by move/pgroup_sol; rewrite mFT_sol_proper. Qed.

Lemma mFT_norm_proper H : H :!=: 1 -> H \proper G -> 'N(H) \proper G.
Proof.
move=> ntH; rewrite !properT; apply: contra; move/eqP=> nHG; apply/eqP.
move/eqP: ntH; case/simpleP: mFT_simple => _; case/(_ H) => //=.
by rewrite -nHG normalG.
Qed.

Lemma cent_mFT_trivial : 'C(G) = 1.
Proof.
apply/eqP; apply: contraR mFT_nonAbelian => ntC.
rewrite /abelian subTset /= eqEproper subsetT /=; apply/negP=> prC.
have:= mFT_norm_proper ntC prC.
by rewrite /proper subsetT norms_cent ?normG.
Qed.

Lemma mFT_cent_proper H : H :!=: 1 -> 'C(H) \proper G.
Proof.
case: (eqsVneq H G) => [-> | ].
  by rewrite cent_mFT_trivial properT eq_sym.
rewrite -properT => prH ntH; apply: sub_proper_trans (cent_sub H) _.
exact: mFT_norm_proper.
Qed.

Lemma mFT_cent1_proper x : x != 1 -> 'C[x] \proper G.
Proof. by rewrite -cycle_eq1 -cent_cycle; exact: mFT_cent_proper. Qed.

Lemma mFT_quo_sol M H : H :!=: 1 -> solvable (M / H).
Proof.
move=> ntH; case: (eqsVneq H G) => [-> |].
  rewrite [_ / _](trivgP _) ?abelian_sol ?abelian1 //.
  by rewrite quotient_sub1 ?normsG ?subsetT.
rewrite -properT => prH; rewrite -quotientInorm morphim_sol //.
by apply: solvableS (subsetIr _ _) (mFT_sol _); rewrite mFT_norm_proper.
Qed.

(* Maximal groups of the minimal FT counterexample, as defined at the start   *)
(* of B & G, section 7.                                                       *)
Definition minSimple_max_groups := [set M : {group gT} | maximal M G].
Local Notation "'M" := minSimple_max_groups : group_scope.

Definition minSimple_max_groups_of (H : sT) := [set M in 'M | H \subset M].
Local Notation "''M' ( H )" := (minSimple_max_groups_of H) : group_scope.

Definition minSimple_uniq_max_groups := [set U : {group gT} | #|'M(U)| == 1%N].
Local Notation "'U" := minSimple_uniq_max_groups : group_scope.

Definition minSimple_SCN_at n p := \bigcup_(P in 'Syl_p(G)) 'SCN_n(P).

Lemma mmax_exists H : H \proper G -> {M | M \in 'M(H)}.
Proof.
case/(@maxgroup_exists _ (fun M => M \proper G)) => M maxM sHM.
by exists M; rewrite !inE sHM andbT.
Qed.

Lemma any_mmax : {M : {group gT} | M \in 'M}.
Proof. by have [M] := mmax_exists mFT_gt1; case/setIdP; exists M. Qed.

Lemma mmax_proper M : M \in 'M -> M \proper G.
Proof. by rewrite inE; apply: maxgroupp. Qed.

Lemma mmax_sol M : M \in 'M -> solvable M.
Proof. by move/mmax_proper/mFT_sol. Qed.

Lemma mmax_max M H : M \in 'M -> H \proper G -> M \subset H -> H :=: M.
Proof. by rewrite inE; case/maxgroupP=> _; apply. Qed.

Lemma eq_mmax : {in 'M &, forall M H, M \subset H -> M :=: H}.
Proof. by move=> M H Mmax; move/mmax_proper=> prH; move/mmax_max->. Qed.

Lemma sub_mmax_proper M H : M \in 'M -> H \subset M -> H \proper G.
Proof. by move=> maxM sHM; apply: sub_proper_trans (mmax_proper maxM). Qed.

Lemma mmax_norm X M :
  M \in 'M -> X :!=: 1 -> X \proper G -> M \subset 'N(X) -> 'N(X) = M.
Proof. by move=> maxM ntX prX; exact: mmax_max (mFT_norm_proper _ _). Qed.

Lemma mmax_normal_subset A M :
  M \in 'M -> A <| M -> ~~ (A \subset [1]) -> 'N(A) = M.
Proof.
rewrite -gen_subG subG1 => maxM /andP[sAM nAM] ntGA.
rewrite (mmax_max maxM) // (sub_proper_trans (norm_gen _)) ?mFT_norm_proper //.
by rewrite (sub_mmax_proper maxM) // gen_subG.
Qed.

Lemma mmax_normal M H : M \in 'M -> H <| M -> H :!=: 1 -> 'N(H) = M.
Proof. by rewrite -subG1; apply: mmax_normal_subset. Qed.

Lemma mmax_sigma_Sylow p P M :
  M \in 'M -> p.-Sylow(M) P -> 'N(P) \subset M -> p.-Sylow(G) P.
Proof.
by move=> maxM sylP sNM; rewrite -Sylow_subnorm setTI (pHall_subl _ sNM) ?normG.
Qed.

Lemma mmax_neq1 M : M \in 'M -> M :!=: 1.
Proof.
move=> maxM; apply: contra mFT_nonAbelian; move/eqP=> M1.
case: (eqVneq G 1) => [-> | ]; first exact: abelian1.
case/trivgPn=> x; rewrite -cycle_subG -cycle_eq1 subEproper /=.
case/predU1P=> [<- | ]; first by rewrite cycle_abelian.
by move/(mmax_max maxM)=> ->; rewrite M1 ?sub1G ?eqxx.
Qed.

Lemma norm_mmax M : M \in 'M -> 'N(M) = M.
Proof.
move=> maxM; apply: mmax_max (normG M) => //.
exact: (mFT_norm_proper (mmax_neq1 maxM) (mmax_proper maxM)).
Qed.

Lemma mmaxJ M x : (M :^ x \in 'M)%G = (M \in 'M).
Proof. by rewrite !inE /= -{1}[G](@conjGid _ _ x) ?maximalJ ?inE. Qed.

Lemma mmax_ofS H K : H \subset K -> 'M(K) \subset 'M(H).
Proof.
move=> sHK; apply/subsetP=> M; rewrite !inE => /andP[->].
exact: subset_trans.
Qed.

Lemma mmax_ofJ K x M : ((M :^ x)%G \in 'M(K :^ x)) = (M \in 'M(K)).
Proof. by rewrite inE mmaxJ conjSg !inE. Qed.

Lemma uniq_mmaxP U : reflect (exists M, 'M(U) = [set M]) (U \in 'U).
Proof. by rewrite inE; apply: cards1P. Qed.
Implicit Arguments uniq_mmaxP [U].

Lemma mem_uniq_mmax U M : 'M(U) = [set M] -> M \in 'M /\ U \subset M.
Proof. by move/setP/(_ M); rewrite set11 => /setIdP. Qed.

Lemma eq_uniq_mmax U M H :
  'M(U) = [set M] -> H \in 'M -> U \subset H -> H :=: M.
Proof.
by move=> uU_M maxH sUH; apply/congr_group/set1P; rewrite -uU_M inE maxH.
Qed.

Lemma def_uniq_mmax U M :
  U \in 'U -> M \in 'M -> U \subset M -> 'M(U) = [set M].
Proof.
case/uniq_mmaxP=> D uU_D maxM sUM.
by rewrite (group_inj (eq_uniq_mmax uU_D maxM sUM)).
Qed.

Lemma uniq_mmax_subset1 U M :
  M \in 'M -> U \subset M -> (U \in 'U) = ('M(U) \subset [set M]).
Proof.
move=> maxM sUM; apply/idP/idP=> uU; first by rewrite -(def_uniq_mmax uU).
by apply/uniq_mmaxP; exists M; apply/eqP; rewrite eqEsubset uU sub1set inE maxM.
Qed.

Lemma sub_uniq_mmax U M H :
  'M(U) = [set M] -> U \subset H -> H \proper G -> H \subset M.
Proof.
move=> uU_M sUH; case/mmax_exists=> D; case/setIdP=> maxD sHD.
by rewrite -(eq_uniq_mmax uU_M maxD) ?(subset_trans sUH).
Qed.

Lemma mmax_sup_id M : M \in 'M -> 'M(M) = [set M].
Proof.
move=> maxM; apply/eqP; rewrite eqEsubset sub1set inE maxM subxx !andbT.
apply/subsetP=> H; case/setIdP=> maxH; rewrite inE -val_eqE /=.
by move/eq_mmax=> ->.
Qed.

Lemma mmax_uniq_id : {subset 'M <= 'U}.
Proof. by move=> M maxM; apply/uniq_mmaxP; exists M; exact: mmax_sup_id. Qed.

Lemma def_uniq_mmaxJ M K x : 'M(K) = [set M] -> 'M(K :^ x) = [set M :^ x]%G.
Proof.
move=> uK_M; apply/setP=> L; rewrite -(actKV 'JG x L) mmax_ofJ uK_M.
by rewrite !inE (inj_eq (act_inj 'JG x)).
Qed.

Lemma uniq_mmaxJ K x :((K :^ x)%G \in 'U) = (K \in 'U).
Proof.
apply/uniq_mmaxP/uniq_mmaxP=> [] [M uK_M].
  exists (M :^ x^-1)%G; rewrite -(conjsgK x K); exact: def_uniq_mmaxJ.
by exists (M :^ x)%G; exact: def_uniq_mmaxJ.
Qed.

Lemma uniq_mmax_norm_sub (M U : {group gT}) :
  'M(U) = [set M] -> 'N(U) \subset M.
Proof.
move=> uU_M; have [maxM _] := mem_uniq_mmax uU_M.
apply/subsetP=> x nUx; rewrite -(norm_mmax maxM) inE.
have:= set11 M; rewrite -uU_M -(mmax_ofJ _ x) (normP nUx) uU_M.
by move/set1P/congr_group->.
Qed.

Lemma uniq_mmax_neq1 (U : {group gT}) : U \in 'U -> U :!=: 1.
Proof.
case/uniq_mmaxP=> M uU_M; have [maxM _] := mem_uniq_mmax uU_M.
apply: contraL (uniq_mmax_norm_sub uU_M); move/eqP->.
by rewrite norm1 subTset -properT mmax_proper.
Qed.

Lemma def_uniq_mmaxS M U V :
  U \subset V -> V \proper G -> 'M(U) = [set M] -> 'M(V) = [set M].
Proof.
move=> sUV prV uU_M; apply/eqP; rewrite eqEsubset sub1set -uU_M.
rewrite mmax_ofS //= inE (sub_uniq_mmax uU_M) //.
by case/mem_uniq_mmax: uU_M => ->.
Qed.

Lemma uniq_mmaxS U V : U \subset V -> V \proper G -> U \in 'U -> V \in 'U.
Proof.
move=> sUV prV /uniq_mmaxP[M uU_M]; apply/uniq_mmaxP; exists M.
exact: def_uniq_mmaxS uU_M.
Qed.

End MinSimpleOdd.

Implicit Arguments uniq_mmaxP [gT U].
Prenex Implicits uniq_mmaxP.

Notation "''M'" := (minSimple_max_groups _) : group_scope.
Notation "''M' ( H )" := (minSimple_max_groups_of H) : group_scope.
Notation "''U'" := (minSimple_uniq_max_groups _) : group_scope.
Notation "''SCN_' n [ p ]" := (minSimple_SCN_at _ n p) : group_scope.

Section Hypothesis7_1.

Variable gT : finGroupType.
Implicit Types X Y A P Q : {group gT}.
Local Notation G := [set: gT].

Definition normed_pgroups (X A : {set gT}) pi :=
  [set Y : {group gT} | pi.-subgroup(X) Y & A \subset 'N(Y)].
Local Notation "|/|_ X ( A ; pi )" := (normed_pgroups X A pi) : group_scope.

Definition max_normed_pgroups (A : {set gT}) pi :=
  [set Y : {group gT} | [max Y | pi.-group Y & A \subset 'N(Y)]].
Local Notation "|/|* ( A ; pi )" := (max_normed_pgroups A pi) : group_scope.

(* This is the statement for B & G, Hypothesis 7.1. *)
Inductive normed_constrained (A : {set gT}) :=
  NormedConstrained (pi := \pi(A)) of A != 1 & A \proper G
  & forall X Y : {group gT},
    A \subset X -> X \proper G -> Y \in |/|_X(A; pi^') -> Y \subset 'O_pi^'(X).

Variable pi : nat_pred.

Lemma max_normed_exists A X :
  pi.-group X -> A \subset 'N(X) -> {Y | Y \in |/|*(A; pi) & X \subset Y}.
Proof.
move=> piX nXA; pose piAn Y := pi.-group(Y) && (A \subset 'N(Y)).
have [|Y] := @maxgroup_exists _ piAn X; first by rewrite /piAn piX.
by exists Y; rewrite // inE.
Qed.

Lemma mem_max_normed A X : X \in |/|*(A; pi) -> pi.-group X /\ A \subset 'N(X).
Proof. by rewrite inE; move/maxgroupp; move/andP. Qed.

Lemma norm_acts_max_norm P : [acts 'N(P), on |/|*(P; pi) | 'JG].
Proof.
apply/subsetP=> z Nz; rewrite !inE; apply/subsetP=> Q; rewrite !inE.
case/maxgroupP=> qQ maxQ; apply/maxgroupP; rewrite pgroupJ norm_conj_norm //.
split=> // Y; rewrite sub_conjg /= => qY; move/maxQ=> <-; rewrite ?conjsgKV //.
by rewrite pgroupJ norm_conj_norm ?groupV.
Qed.

Lemma trivg_max_norm P : 1%G \in |/|*(P; pi) -> |/|*(P; pi) = [set 1%G].
Proof.
move=> max1; apply/eqP; rewrite eqEsubset sub1set max1 andbT.
apply/subsetP=> Q; rewrite !inE -val_eqE /= in max1 *.
by case/maxgroupP: max1 => _ max1; move/maxgroupp; move/max1->; rewrite ?sub1G.
Qed.

Lemma max_normed_uniq A P Q :
    |/|*(A; pi) = [set Q] -> A \subset P -> P \subset 'N(Q) ->
  |/|*(P; pi) = [set Q].
Proof.
move=> defAmax sAP nQP; have: Q \in |/|*(A; pi) by rewrite defAmax set11.
rewrite inE; case/maxgroupP; case/andP=> piQ _ maxQ.
apply/setP=> X; rewrite !inE -val_eqE /=; apply/maxgroupP/eqP=> [[]|->{X}].
  case/andP=> piX nXP maxX; have nXA := subset_trans sAP nXP.
  have [Y] := max_normed_exists piX nXA.
  by rewrite defAmax; move/set1P->; move/maxX=> -> //; rewrite piQ.
rewrite piQ; split=> // X; case/andP=> piX nXP sQX.
by rewrite (maxQ X) // piX (subset_trans sAP).
Qed.

End Hypothesis7_1.

Notation "|/|_ X ( A ; pi )" := (normed_pgroups X A pi) : group_scope.
Notation "|/|* ( A ; pi )" := (max_normed_pgroups A pi) : group_scope.

Section Seven.

Variable gT : minSimpleOddGroupType.
Local Notation G := (TheMinSimpleOddGroup gT).
Local Notation grT := {group gT}.
Implicit Types H P Q R K M A B : grT.
Implicit Type p q : nat.

Section NormedConstrained.

Variables (q : nat) (A : grT).
Let pi := Eval simpl in \pi(A).
Let K := 'O_pi^'('C(A)).
Let nsKC : K <| 'C(A) := pcore_normal _ _.

Lemma cent_core_acts_max_norm : [acts K, on |/|*(A; q) | 'JG].
Proof.
by rewrite (subset_trans _ (norm_acts_max_norm _ _)) ?cents_norm ?pcore_sub.
Qed.
Let actsKmax := actsP cent_core_acts_max_norm.

Hypotheses (cstrA : normed_constrained A) (pi'q : q \notin pi).

Let hyp71 H R :
  A \subset H -> H \proper G -> R \in |/|_H(A; pi^') -> R \subset 'O_pi^'(H).
Proof. by case: cstrA H R. Qed.

(* This is the observation between B & G, Hypothesis 7.1 and Lemma 7.1. *)
Remark normed_constrained_Hall : pi^'.-Hall('C(A)) K.
Proof.
have [_ ntA prA _] := cstrA; rewrite -[setT]/G in prA.
rewrite /pHall pcore_pgroup pcore_sub pnatNK /=.
rewrite -card_quotient ?gFnorm //= -/K.
apply/pgroupP=> p p_pr; case/Cauchy=> // Kx; case/morphimP=> x Nx Cx ->{Kx}.
rewrite /order -quotient_cycle //= -/K => def_p; apply/idPn=> pi'p.
have [P sylP] := Sylow_exists p <[x]>; have [sPx pP _]:= and3P sylP.
suffices: P \subset K.
  have nKP: P \subset 'N(K) by rewrite (subset_trans sPx) ?cycle_subG.
  rewrite -quotient_sub1 //= -/K (sameP trivgP eqP) trivg_card1.
  rewrite (card_Hall (morphim_pHall _ nKP sylP)) def_p part_pnat_id ?pnat_id //.
  by case: eqP p_pr => // ->.
suffices sP_pAC: P \subset 'O_pi^'(A <*> 'C(A)).
  rewrite (subset_trans sP_pAC) ?pcore_max ?pcore_pgroup //.
  rewrite /normal (char_norm_trans (pcore_char _ _)) ?normsG ?joing_subr //.
  rewrite andbT -quotient_sub1; last first.
    rewrite (subset_trans (pcore_sub _ _)) // join_subG normG cents_norm //.
    by rewrite centsC.
  rewrite /= -(setIidPr (pcore_sub _ _)) quotientGI ?joing_subr //=.
  rewrite {1}cent_joinEr // quotientMidr coprime_TIg // coprime_morph //.
  by rewrite coprime_pi' ?cardG_gt0 //= -/pi [pnat _ _]pcore_pgroup.
apply: hyp71; first exact: joing_subl.
  apply: sub_proper_trans (mFT_norm_proper ntA prA).
  by rewrite join_subG normG cent_sub.
have sPC: P \subset 'C(A) by rewrite (subset_trans sPx) ?cycle_subG.
rewrite inE /psubgroup cents_norm 1?centsC // andbT.
rewrite (subset_trans sPC) ?joing_subr //=.
by apply: sub_in_pnat pP => p' _; move/eqnP->.
Qed.
Let hallK := normed_constrained_Hall.

(* This is B & G, Lemma 7.1. *)
Lemma normed_constrained_meet_trans Q1 Q2 H :
    A \subset H -> H \proper G -> Q1 \in |/|*(A; q) -> Q2 \in |/|*(A; q) ->
    Q1 :&: H != 1 -> Q2 :&: H != 1 ->
  exists2 k, k \in K & Q2 :=: Q1 :^ k.
Proof.
move: {2}_.+1 (ltnSn (#|G| - #|Q1 :&: Q2|)) => m.
elim: m => // m IHm in H Q1 Q2 * => geQ12m sAH prHG maxQ1 maxQ2 ntHQ1 ntHQ2.
have:= maxQ1; rewrite inE => /maxgroupP[/andP[qQ1 nQ1A] maxQ1P].
have:= maxQ2; rewrite inE => /maxgroupP[/andP[qQ2 nQ2A] maxQ2P].
have prQ12: Q1 :&: Q2 \proper G.
  rewrite properT; apply: contraNneq (mFT_nonSolvable gT) => <-.
  by apply: pgroup_sol (pgroupS _ qQ1); rewrite subsetIl.
wlog defH: H prHG sAH ntHQ1 ntHQ2 / Q1 :&: Q2 != 1 -> H :=: 'N(Q1 :&: Q2).
  case: (eqVneq (Q1 :&: Q2) 1) => [-> | ntQ12] IH.
    by apply: (IH H) => //; case/eqP.
  apply: (IH 'N(Q1 :&: Q2)%G); rewrite ?normsI ?mFT_norm_proper //;
    apply: contra ntQ12; rewrite -!subG1; apply: subset_trans;
    by rewrite subsetI normG (subsetIl, subsetIr).
pose L := 'O_pi^'(H); have sLH: L \subset H := pcore_sub _ _.
have [nLA coLA solL]: [/\ A \subset 'N(L), coprime #|L| #|A| & solvable L].
- rewrite (char_norm_trans (pcore_char _ _)) ?normsG //.
  rewrite coprime_sym coprime_pi' ?cardG_gt0 ?[pnat _ _]pcore_pgroup //.
  by rewrite (solvableS sLH) ?mFT_sol.
have Qsyl Q: Q \in |/|*(A; q) -> Q :&: H != 1 ->
  exists R : {group _}, [/\ q.-Sylow(L) R, A \subset 'N(R) & Q :&: H \subset R].
- case/mem_max_normed=> qQ nQA ntQH.
  have qQH: q.-group (Q :&: H) by rewrite (pgroupS _ qQ) ?subsetIl.
  have nQHA: A \subset 'N(Q :&: H) by rewrite normsI // normsG.
  apply: coprime_Hall_subset => //; apply: (hyp71) => //.
  rewrite inE nQHA /psubgroup subsetIr andbT.
  by apply: sub_in_pnat qQH => p _; move/eqnP->.
have [R1 [sylR1 nR1A sQR1]] := Qsyl _ maxQ1 ntHQ1.
have [R2 [sylR2 nR2A sQR2]] := Qsyl _ maxQ2 ntHQ2.
have [h Ch defR2] := coprime_Hall_trans nLA coLA solL sylR2 nR2A sylR1 nR1A.
have{Ch} [Hh Kh]: h \in H /\ h \in K.
  case/setIP: Ch => Lh Ch; rewrite (subsetP sLH) //.
  rewrite (mem_normal_Hall hallK (pcore_normal _ _)) //.
  by rewrite (mem_p_elt _ Lh) ?pcore_pgroup.
have [Q3 maxQ3 sR2Q3] := max_normed_exists (pHall_pgroup sylR2) nR2A.
have maxQ1h: (Q1 :^ h)%G \in |/|*(A; q) by rewrite actsKmax.
case: (eqsVneq Q1 Q2) => [| neQ12]; first by exists 1; rewrite ?group1 ?conjsg1.
have ntHQ3: Q3 :&: H != 1.
  apply: contra ntHQ2; rewrite -!subG1; apply: subset_trans.
  by rewrite subsetI subsetIr (subset_trans sQR2).
have ntHQ1h: (Q1 :^ h) :&: H != 1.
  by move: ntHQ1; rewrite !trivg_card1 -(cardJg _ h) conjIg (conjGid Hh).
suff [prI1 prI2]: Q1 :&: Q2 \proper Q1 :&: R1 /\ Q1 :&: Q2 \proper Q2 :&: R2.
  have: #|G| - #|(Q1 :^ h) :&: Q3| < m.
    rewrite ltnS in geQ12m; apply: leq_trans geQ12m.
    rewrite ltn_sub2l ?(proper_card prQ12) // -(cardJg _ h) proper_card //.
    by rewrite (proper_sub_trans _ (setIS _ sR2Q3)) // defR2 -conjIg properJ.
  have: #|G| - #|Q3 :&: Q2| < m.
    rewrite ltnS in geQ12m; apply: leq_trans geQ12m.
    rewrite ltn_sub2l ?proper_card // (proper_sub_trans prI2) //.
    by rewrite setIC setISS.
  case/(IHm H) => // k2 Kk2 defQ2; case/(IHm H) => // k3 Kk3 defQ3.
  by exists (h * k3 * k2); rewrite ?groupM ?conjsgM // -defQ3.
case: (eqVneq (Q1 :&: Q2) 1) => [-> | ntQ12].
  rewrite !proper1G; split; [apply: contra ntHQ1 | apply: contra ntHQ2];
    by rewrite -!subG1; apply: subset_trans; rewrite subsetI subsetIl.
rewrite -(setIidPr (subset_trans (pHall_sub sylR1) sLH)) setIA.
rewrite -(setIidPr (subset_trans (pHall_sub sylR2) sLH)) setIA.
rewrite (setIidPl sQR1) (setIidPl sQR2) {}defH //.
have nilQ1 := pgroup_nil qQ1; have nilQ2 := pgroup_nil qQ2.
rewrite !nilpotent_proper_norm /proper ?subsetIl ?subsetIr ?subsetI ?subxx //=.
  by rewrite andbT; apply: contra neQ12 => sQ21; rewrite (maxQ2P Q1) ?qQ1.
by apply: contra neQ12 => sQ12; rewrite (maxQ1P Q2) ?qQ2.
Qed.

(* This is B & G, Theorem 7.2. *)
Theorem normed_constrained_rank3_trans :
  'r('Z(A)) >= 3 -> [transitive K, on |/|*(A; q) | 'JG].
Proof.
case/rank_geP=> B /nElemP[p]; rewrite !inE subsetI -2!andbA.
case/and4P=> sBA cAB abelB mB3; have [_ cBB _] := and3P abelB.
have q'B: forall Q, q.-group Q -> coprime #|Q| #|B|.
  move=> Q qQ; rewrite coprime_sym (coprimeSg sBA) ?coprime_pi' //.
  exact: pi_pnat qQ _.
have [Q1 maxQ1 _] := max_normed_exists (pgroup1 _ q) (norms1 A).
apply/imsetP; exists Q1 => //; apply/setP=> Q2.
apply/idP/imsetP=> [maxQ2|[k Kk] ->]; last by rewrite actsKmax.
have [qQ1 nQ1A]:= mem_max_normed maxQ1; have [qQ2 nQ2A]:= mem_max_normed maxQ2.
case: (eqVneq Q1 1%G) => [trQ1 | ntQ1].
  exists 1; rewrite ?group1 // act1; apply/eqP.
  by rewrite trivg_max_norm -trQ1 // inE in maxQ2.
case: (eqVneq Q2 1%G) => [trQ2 | ntQ2].
  by case/negP: ntQ1; rewrite trivg_max_norm -trQ2 // inE in maxQ1 *.
have: [exists (C : grT | 'C_Q1(C) != 1), cyclic (B / C) && (C <| B)].
  apply: contraR ntQ1 => trQ1; have: B \subset 'N(Q1) := subset_trans sBA nQ1A.
  rewrite -val_eqE -subG1 /=; move/coprime_abelian_gen_cent <-; rewrite ?q'B //.
  rewrite gen_subG; apply/bigcupsP=> C cocyC; rewrite subG1.
  by apply: contraR trQ1 => ntCC; apply/existsP; exists C; rewrite ntCC.
case/existsP=> C /and3P[ntCQ1 cycBC nsCB]; have [sCB nCB]:= andP nsCB.
have{mB3} ncycC: ~~ cyclic C.
  rewrite (abelem_cyclic (quotient_abelem _ abelB)) ?card_quotient // in cycBC.
  rewrite -divgS // logn_div ?cardSg // leq_subLR addn1 (eqP mB3) in cycBC.
  by rewrite (abelem_cyclic (abelemS sCB abelB)) -ltnNge.
have: [exists (z | 'C_Q2[z] != 1), z \in C^#].
  apply: contraR ntQ2 => trQ2; have:= subset_trans sCB (subset_trans sBA nQ2A).
  rewrite -[_ == _]subG1 /=.
  move/coprime_abelian_gen_cent1 <-; rewrite ?(abelianS sCB) //; last first.
    by rewrite (coprimegS sCB) ?q'B.
  rewrite gen_subG; apply/bigcupsP=> z Cz.
  by apply: contraR trQ2 => ntCz; apply/existsP; exists z; rewrite -subG1 ntCz.
case/existsP=> z; rewrite !inE => /and3P[ntzQ2 ntz Cz].
have prCz: 'C[z] \proper G by rewrite -cent_cycle mFT_cent_proper ?cycle_eq1.
have sACz: A \subset 'C[z] by rewrite sub_cent1 (subsetP cAB) ?(subsetP sCB).
have [|//|k Kk defQ2]:= normed_constrained_meet_trans sACz prCz maxQ1 maxQ2.
  apply: contra ntCQ1; rewrite -!subG1; apply: subset_trans.
  by rewrite setIS //= -cent_cycle centS ?cycle_subG.
exists k => //; exact: val_inj.
Qed.

(* This is B & G, Theorem 7.3. *)
Theorem normed_constrained_rank2_trans :
  q %| #|'C(A)| -> 'r('Z(A)) >= 2 -> [transitive K, on |/|*(A; q) | 'JG].
Proof.
move=> qC; case/rank_geP=> B; case/nElemP=> p; do 2![case/setIdP].
rewrite subsetI; case/andP=> sBA cAB abelB mB2; have [_ cBB _] := and3P abelB.
have{abelB mB2} ncycB: ~~ cyclic B by rewrite (abelem_cyclic abelB) (eqP mB2).
have [R0 sylR0] := Sylow_exists q 'C(A); have [cAR0 qR0 _] := and3P sylR0.
have nR0A: A \subset 'N(R0) by rewrite cents_norm // centsC.
have{nR0A} [R maxR sR0R] := max_normed_exists qR0 nR0A.
apply/imsetP; exists R => //; apply/setP=> Q.
apply/idP/imsetP=> [maxQ|[k Kk] ->]; last by rewrite actsKmax.
have [qR nRA]:= mem_max_normed maxR; have [qQ nQA]:= mem_max_normed maxQ.
have [R1 | ntR] := eqVneq R 1%G.
  rewrite trivg_max_norm -R1 // in maxQ.
  by exists 1; rewrite ?group1 ?act1 ?(set1P maxQ).
have ntQ: Q != 1%G.
  by apply: contra ntR => Q1; rewrite trivg_max_norm -(eqP Q1) // inE in maxR *.
have ntRC: 'C_R(A) != 1.
  have sR0CR: R0 \subset 'C_R(A) by rewrite subsetI sR0R.
  suffices: R0 :!=: 1 by rewrite -!proper1G; move/proper_sub_trans->.
  move: ntR; rewrite -!cardG_gt1 -(part_pnat_id qR) (card_Hall sylR0).
  by rewrite !p_part_gt1 !mem_primes !cardG_gt0 qC; case/and3P=> ->.
have: [exists (z | 'C_Q[z] != 1), z \in B^#].
  apply: contraR ntQ => trQ; have:= subset_trans sBA nQA.
  rewrite -[_ == _]subG1; move/coprime_abelian_gen_cent1 <- => //; last first.
    by rewrite coprime_sym (coprimeSg sBA) ?coprime_pi' /pgroup ?(pi_pnat qQ).
  rewrite gen_subG; apply/bigcupsP=> z Cz; rewrite subG1.
  by apply: contraR trQ => ntCz; apply/existsP; exists z; rewrite ntCz.
case/existsP=> z; rewrite 2!inE => /and3P[ntzQ ntz Bz].
have prCz: 'C[z] \proper G by rewrite -cent_cycle mFT_cent_proper ?cycle_eq1.
have sACz: A \subset 'C[z] by rewrite sub_cent1 (subsetP cAB).
have [|//|k Kk defQ2]:= normed_constrained_meet_trans sACz prCz maxR maxQ.
  apply: contra ntRC; rewrite -!subG1; apply: subset_trans.
  by rewrite setIS //= -cent_cycle centS // cycle_subG (subsetP sBA).
exists k => //; exact: val_inj.
Qed.

(* This is B & G, Theorem 7.4. *)
Theorem normed_trans_superset P :
    A <|<| P -> pi.-group P -> [transitive K, on |/|*(A; q) | 'JG] ->
 [/\ 'C_K(P) = 'O_pi^'('C(P)),
     [transitive 'O_pi^'('C(P)), on |/|*(P; q) | 'JG],
     |/|*(P; q) \subset |/|*(A; q)
   & {in |/|*(P; q), forall Q, P :&: 'N(P)^`(1) \subset 'N(Q)^`(1)
                            /\ 'N(P) = 'C_K(P) * 'N_('N(P))(Q)}].
Proof.
move=> snAP piP trnK; set KP := 'O_pi^'('C(P)).
have defK: forall B, A \subset B -> 'C_K(B) = 'O_pi^'('C(B)).
  move=> B sAB; apply/eqP; rewrite eqEsubset {1}setIC pcoreS ?centS //.
  rewrite subsetI pcore_sub (sub_Hall_pcore hallK) ?pcore_pgroup //.
  by rewrite (subset_trans (pcore_sub _ _)) ?centS.
suffices: [transitive KP, on |/|*(P; q) | 'JG] /\ |/|*(P; q) \subset |/|*(A; q).
  have nsKPN: KP <| 'N(P) := char_normal_trans (pcore_char _ _) (cent_normal _).
  case=> trKP smnPA; rewrite (defK _ (subnormal_sub snAP)); split=> // Q maxQ.
  have defNP: KP * 'N_('N(P))(Q) = 'N(P).
    rewrite -(astab1JG Q) -normC; last by rewrite subIset 1?normal_norm.
    apply/(subgroup_transitiveP maxQ); rewrite ?normal_sub //=.
    by rewrite (atrans_supgroup _ trKP) ?norm_acts_max_norm ?normal_sub.
  split=> //; move/pprod_focal_coprime: defNP => -> //.
  - by rewrite subIset // orbC commgSS ?subsetIr.
  - by rewrite subsetI normG; case/mem_max_normed: maxQ.
  by rewrite (p'nat_coprime (pcore_pgroup _ _)).
elim: {P}_.+1 {-2}P (ltnSn #|P|) => // m IHm P lePm in KP piP snAP *.
wlog{snAP} [B maxnB snAB]: / {B : grT | maxnormal B P P & A <|<| B}.
  case/subnormalEr: snAP => [|[D [snAD nDP prDP]]]; first by rewrite /KP => <-.
  have [B maxnB sDB]: {B : grT | maxnormal B P P & D \subset B}.
    by apply: maxgroup_exists; rewrite prDP normal_norm.
  apply; exists B => //; apply: subnormal_trans snAD (normal_subnormal _).
  by apply: normalS sDB _ nDP; case/andP: (maxgroupp maxnB); case/andP.
have [prBP nBP] := andP (maxgroupp maxnB); have sBP := proper_sub prBP.
have{lePm}: #|B| < m by exact: leq_trans (proper_card prBP) _.
case/IHm=> {IHm}// [|trnB smnBA]; first by rewrite (pgroupS sBP).
have{maxnB} abelPB: is_abelem (P / B).
  apply: charsimple_solvable (maxnormal_charsimple _ maxnB) _ => //.
  have [_ ntA _ _] := cstrA; have sAB := subnormal_sub snAB.
  by apply: mFT_quo_sol; apply: contraL sAB; move/eqP->; rewrite subG1.
have{abelPB} [p p_pr pPB]: exists2 p, prime p & p.-group (P / B).
  by case/is_abelemP: abelPB => p p_pr; case/andP; exists p.
have{prBP} pi_p: p \in pi.
  case/pgroup_pdiv: pPB => [|_ pPB _].
    by rewrite -subG1 quotient_sub1 // proper_subn.
  by apply: pgroupP p_pr pPB; exact: quotient_pgroup.
pose S := |/|*(B; q); have p'S: #|S| %% p != 0.
  have pi'S: pi^'.-nat #|S| := pnat_dvd (atrans_dvd trnB) (pcore_pgroup _ _).
  by rewrite -prime_coprime // (pnat_coprime _ pi'S) ?pnatE.
have{p'S} [Q S_Q nQP]: exists2 Q, Q \in S & P \subset 'N(Q).
  have sTSB: setT \subset G / B by rewrite -im_quotient quotientS ?subsetT.
  have modBE: {in P & S, forall x Q, ('JG %% B) Q (coset B x) = 'JG Q x}%act.
    move=> x Q Px; rewrite inE; move/maxgroupp; case/andP=> _ nQB.
    by rewrite /= modactE ?(subsetP nBP) ?afixJG ?setTI ?inE.
  have actsPB: [acts P / B, on S | 'JG %% B \ sTSB].
    apply/subsetP=> _ /morphimP[x Nx Px ->].
    rewrite !inE; apply/subsetP=> Q S_Q; rewrite inE /= modBE //.
    by rewrite (actsP (norm_acts_max_norm q B)).
  move: p'S; rewrite (pgroup_fix_mod pPB actsPB); set nQ := #|_|.
  case: (posnP nQ) => [->|]; first by rewrite mod0n.
  rewrite lt0n; case/existsP=> Q /setIP[Q_S fixQ]; exists Q => //.
  apply/normsP=> x Px; apply: congr_group; have Nx := subsetP nBP x Px.
  by have:= afixP fixQ (coset B x); rewrite /= modBE ?mem_morphim //= => ->.
have [qQ _]:= mem_max_normed S_Q.
have{qQ nQP} [Q0 maxQ0 sQQ0] := max_normed_exists qQ nQP.
have [_ nQ0P]:= mem_max_normed maxQ0.
have actsKmnP: [acts 'O_pi^'('C(P)), on |/|*(P; q) | 'JG].
  by rewrite (subset_trans _ (norm_acts_max_norm q P)) // cents_norm ?pcore_sub.
case nt_mnP: (1%G \in |/|*(P; q)) => [|{Q S_Q sQQ0}].
  rewrite atrans_acts_card actsKmnP trivg_max_norm // imset_set1 in maxQ0 *.
  have <-: Q = 1%G by apply/trivGP; rewrite -(congr_group (set1P maxQ0)).
  by rewrite cards1 sub1set (subsetP smnBA).
have sAB := subnormal_sub snAB; have sAP := subset_trans sAB sBP.
have smnP_S: |/|*(P; q) \subset S.
  apply/subsetP=> Q1 maxQ1; have [qQ1 nQ1P] := mem_max_normed maxQ1.
  have ntQ1: Q1 != 1%G by case: eqP nt_mnP maxQ1 => // -> ->.
  have prNQ1: 'N(Q1) \proper G := mFT_norm_proper ntQ1 (mFT_pgroup_proper qQ1).
  have nQ1A: A \subset 'N(Q1) := subset_trans sAP nQ1P.
  have [Q2 maxQ2 sQ12] := max_normed_exists qQ1 (subset_trans sBP nQ1P).
  have [qQ2 nQ2B] := mem_max_normed maxQ2; apply: etrans maxQ2; congr in_mem.
  apply: val_inj; suffices: q.-Sylow(Q2) Q1 by move/pHall_id=> /= ->.
  have qNQ2: q.-group 'N_Q2(Q1) by rewrite (pgroupS _ qQ2) ?subsetIl.
  pose KN := 'O_pi^'('N(Q1)); have sNQ2_KN: 'N_Q2(Q1) \subset KN.
    rewrite hyp71 // inE normsI ?norms_norm ?(subset_trans sAB nQ2B) //=.
    by rewrite /psubgroup subsetIr andbT; exact: pi_pnat qNQ2 _.
  rewrite -Sylow_subnorm (pHall_subl _ sNQ2_KN) ?subsetI ?sQ12 ?normG //= -/KN.
  suff: exists Q3 : grT, [/\ q.-Sylow(KN) Q3, P \subset 'N(Q3) & Q1 \subset Q3].
    move: maxQ1; rewrite inE; case/maxgroupP=> _ maxQ1 [Q3 [sylQ3 nQ3P sQ13]].
    by rewrite -(maxQ1 Q3) // (pHall_pgroup sylQ3).
  apply: coprime_Hall_subset; rewrite //= -/KN.
  - by rewrite (char_norm_trans (pcore_char _ _)) ?norms_norm.
  - by rewrite coprime_sym (pnat_coprime piP (pcore_pgroup _ _)).
  - by rewrite (solvableS (pcore_sub _ _)) ?mFT_sol.
  by rewrite pcore_max ?normalG // /pgroup (pi_pnat qQ1).
split; last exact: subset_trans smnP_S smnBA.
apply/imsetP; exists Q0 => //; apply/setP=> Q2.
apply/idP/imsetP=> [maxQ2 | [k Pk ->]]; last by rewrite (actsP actsKmnP).
have [S_Q0 S_Q2]: Q0 \in S /\ Q2 \in S by rewrite !(subsetP smnP_S).
pose KB := 'O_pi^'('C(B)); pose KBP := KB <*> P.
have pi'KB: pi^'.-group KB by exact: pcore_pgroup.
have nKB_P: P \subset 'N(KB).
  by rewrite (char_norm_trans (pcore_char _ _)) ?norms_cent.
have [k KBk defQ2]:= atransP2 trnB S_Q0 S_Q2.
have [qQ2 nQ2P] := mem_max_normed maxQ2.
have hallP: pi.-Hall('N_KBP(Q2)) P.
  have sPN: P \subset 'N_KBP(Q2) by rewrite subsetI joing_subr.
  rewrite pHallE eqn_leq -{1}(part_pnat_id piP) dvdn_leq ?partn_dvd ?cardSg //.
  have ->: #|P| = #|KBP|`_pi.
    rewrite /KBP joingC norm_joinEl // coprime_cardMg ?(pnat_coprime piP) //.
    by rewrite partnM // part_pnat_id // part_p'nat // muln1.
  by rewrite sPN dvdn_leq ?partn_dvd ?cardSg ?cardG_gt0 ?subsetIl.
have hallPk: pi.-Hall('N_KBP(Q2)) (P :^ k).
  rewrite pHallE -(card_Hall hallP) cardJg eqxx andbT subsetI /=.
  by rewrite defQ2 normJ conjSg conj_subG ?joing_subr // mem_gen // inE KBk.
have [gz]: exists2 gz, gz \in 'N_KBP(Q2) & P :=: (P :^ k) :^ gz.
  apply: Hall_trans (solvableS (subsetIr _ _) _) hallP hallPk.
  have ntQ2: Q2 != 1%G by case: eqP nt_mnP maxQ2 => // -> ->.
  exact: mFT_sol (mFT_norm_proper ntQ2 (mFT_pgroup_proper qQ2)).
rewrite [KBP]norm_joinEr //= setIC -group_modr //= setIC -/KB.
case/imset2P=> g z; case/setIP=> KBg nQ2g Pz ->{gz} defP.
exists (k * g); last first.
  by apply: val_inj; rewrite /= conjsgM -(normP nQ2g) defQ2.
rewrite /KP -defK // (subsetP (subsetIl _ 'C(B))) //= setIAC defK // -/KB.
rewrite -coprime_norm_cent 1?coprime_sym ?(pnat_coprime piP) //= -/KB.
rewrite inE groupM //; apply/normP.
by rewrite -{2}(conjsgK z P) (conjGid Pz) {2}defP /= !conjsgM conjsgK.
Qed.

End NormedConstrained.

(* This is B & G, Proposition 7.5(a). As this is only used in Proposition    *)
(* 10.10, under the assumption A \in E*_p(G), we avoid the in_pmaxElemE      *)
(* detour A = [set x in 'C_G(A) | x ^+ p == 1], and just use A \in E*_p(G).  *)
Proposition plength_1_normed_constrained p A :
    A :!=: 1 -> A \in 'E*_p(G) -> (forall M, M \proper G -> p.-length_1 M) ->
  normed_constrained A.
Proof. 
move=> ntA EpA pl1subG.
case/pmaxElemP: (EpA); case/pElemP=> sAG; case/and3P=> pA cAA _ _. 
have prA: A \proper G := sub_proper_trans cAA (mFT_cent_proper ntA).
split=> // X Y sAX prX; case/setIdP; case/andP=> sYX p'Y nYA.
have pl1X := pl1subG _ prX; have solX := mFT_sol prX.
have [p_pr _ [r oApr]] := pgroup_pdiv pA ntA.
have oddp: odd p by move: (mFT_odd A); rewrite oApr odd_exp.
have def_pi: \pi(A)^' =i p^'.
  by move=> q; rewrite inE /= oApr pi_of_exp // pi_of_prime.
have{p'Y} p'Y : p^'.-group Y by rewrite -(eq_pgroup _ def_pi).
rewrite (eq_pcore _ def_pi) (@plength1_norm_pmaxElem _ p X A) //.
by rewrite (subsetP (pmaxElemS p (subsetT _))) // setIC 2!inE sAX.
Qed.

(* This is B & G, Proposition 7.5(b). *)
Proposition SCN_normed_constrained p P A :
  p.-Sylow(G) P -> A \in 'SCN_2(P) -> normed_constrained A.
Proof.
move=> sylP; rewrite 2!inE -andbA => /and3P[nsAP /eqP defCA lt1mA].
have [sAP nAP]:= andP nsAP.
have pP := pHall_pgroup sylP; have pA := pgroupS sAP pP.
have abA: abelian A by rewrite /abelian -{1}defCA subsetIr.
have prP: P \proper G := mFT_pgroup_proper pP.
have ntA: A :!=: 1 by rewrite -rank_gt0 ltnW.
pose pi := \pi(A); simpl in pi.
have [p_pr pdvA [r oApr]] := pgroup_pdiv pA ntA.
have{r oApr} def_pi: pi =i (p : nat_pred).
  by move=> p'; rewrite !inE oApr primes_exp // primes_prime ?inE.
have def_pi' := eq_negn def_pi; have defK := eq_pcore _ def_pi'.
pose Z := 'Ohm_1('Z(P)); have sZ_ZP: Z \subset 'Z(P) by exact: Ohm_sub.
have sZP_A: 'Z(P) \subset A by rewrite -defCA setIS ?centS.
have sZA := subset_trans sZ_ZP sZP_A.
have nsA1: 'Ohm_1(A) <| P by exact: (char_normal_trans (Ohm_char _ _)).
pose inZor1 B := B \subset Z \/ #|Z| = p /\ Z \subset B.
have [B [E2_B nsBP sBZ]]: exists B, [/\ B \in 'E_p^2(A), B <| P & inZor1 B].
  have pZP: p.-group 'Z(P) by exact: pgroupS (center_sub _) pP.
  have pZ: p.-group Z by exact: pgroupS sZ_ZP pZP.
  have abelZ: p.-abelem Z by rewrite Ohm1_abelem ?center_abelian.
  have nsZP: Z <| P := sub_center_normal sZ_ZP; have [sZP nZP] := andP nsZP.
  case: (eqVneq Z 1).
    rewrite -(setIidPr sZ_ZP); move/TI_Ohm1; rewrite setIid.
    by move/(trivg_center_pgroup pP)=> P1; rewrite -subG1 -P1 sAP in ntA.
  case/(pgroup_pdiv pZ)=> _ _ [[|k] /=]; rewrite -/Z => oZ; last first.
    have: 2 <= 'r_p(Z) by rewrite p_rank_abelem // oZ pfactorK.
    case/p_rank_geP=> B; rewrite /= -/Z => Ep2Z_B; exists B.
    rewrite (subsetP (pnElemS _ _ sZA)) //.
    case/setIdP: Ep2Z_B; case/setIdP=> sBZ _ _; split=> //; last by left.
    by rewrite sub_center_normal ?(subset_trans sBZ).
  pose BZ := ('Ohm_1(A) / Z) :&: 'Z(P / Z).
  have ntBz: BZ != 1.
    rewrite meet_center_nil ?quotient_nil ?(pgroup_nil pP) ?quotient_normal //.
    rewrite -subG1 quotient_sub1 ?(subset_trans (normal_sub nsA1) nZP) //= -/Z.
    apply: contraL lt1mA => sA1Z; rewrite -(pfactorK 1 p_pr) -oZ -rank_Ohm1.
    by rewrite -(rank_abelem abelZ) -leqNgt rankS.
  have lt1A1: 1 < logn p #|'Ohm_1(A)| by rewrite -p_rank_abelian -?rank_pgroup.
  have [B [sBA1 nsBP oB]] := normal_pgroup pP nsA1 lt1A1.
  exists B; split=> //; last do [right; split=> //].
    rewrite 2!inE (subset_trans sBA1) ?Ohm_sub // oB pfactorK //.
    by rewrite (abelemS sBA1) ?Ohm1_abelem.
  apply/idPn=> s'BZ; have: B :&: Z = 1 by rewrite setIC prime_TIg ?oZ.
  move/TI_Ohm1; apply/eqP; rewrite meet_center_nil ?(pgroup_nil pP) //.
  by rewrite -cardG_gt1 oB (ltn_exp2l 0 _ (prime_gt1 p_pr)).
split; rewrite ?(sub_proper_trans sAP) // => X Y sAX prX.
rewrite inE defK -andbA (eq_pgroup _ def_pi'); case/and3P=> sYX p'Y nYA.
move: E2_B; rewrite 2!inE -andbA; case/and3P=> sBA abelB dimB2.
have [pB cBB _] := and3P abelB.
have ntB: B :!=: 1 by case: (eqsVneq B 1) dimB2 => // ->; rewrite cards1 logn1.
have cBA b: b \in B -> A \subset 'C[b].
  by move=> Bb; rewrite -cent_set1 centsC sub1set (subsetP abA) ?(subsetP sBA).
have solCB (b : gT): b != 1 -> solvable 'C[b].
  by move=> ntb; rewrite mFT_sol ?mFT_cent1_proper.
wlog{sAX prX} [b B'b defX]: X Y p'Y nYA sYX / exists2 b, b \in B^# & 'C[b] = X.
  move=> IH; have nYB := subset_trans sBA nYA.
  rewrite -(coprime_abelian_gen_cent1 cBB _ nYB); last first.
  - by rewrite coprime_sym (pnat_coprime pB).
  - apply: contraL dimB2 => /cyclicP[x defB].
    have Bx: x \in B by rewrite defB cycle_id.
    rewrite defB -orderE (abelem_order_p abelB Bx) ?(pfactorK 1) //.
    by rewrite -cycle_eq1 -defB.
  rewrite gen_subG; apply/bigcupsP=> b B'b.
  have [ntb Bb]:= setD1P B'b; have sYbY: 'C_Y[b] \subset Y := subsetIl _ _.
  have{IH} sYbKb: 'C_Y[b] \subset 'O_p^'('C[b]).
    rewrite IH ?(pgroupS sYbY) ?subsetIr //; last by exists b.
    by rewrite normsI // ?normsG ?cBA.
  have{sYbKb} sYbKXb: 'C_Y[b] \subset 'O_p^'('C_X(<[b]>)).
    apply: subset_trans (pcoreS _ (subsetIr _ _)).
    by rewrite /= cent_gen cent_set1 subsetI setSI.
  rewrite (subset_trans sYbKXb) // p'core_cent_pgroup ?mFT_sol //.
  rewrite /psubgroup ?(pgroupS _ pB) cycle_subG //.
  by rewrite (subsetP sAX) ?(subsetP sBA).
wlog Zb: b X Y defX B'b p'Y nYA sYX / b \in Z.
  move=> IH; case Zb: (b \in Z); first exact: IH Zb.
  case/setD1P: B'b => ntb Bb; have solX := solCB b ntb; rewrite defX in solX.
  case: sBZ => [sBZ | [oZ sZB]]; first by rewrite (subsetP sBZ) in Zb.
  have defB: Z * <[b]> = B.
    apply/eqP; rewrite eqEcard mulG_subG sZB cycle_subG Bb.
    have obp := abelem_order_p abelB Bb ntb.
    rewrite (card_pgroup pB) /= (eqP dimB2) TI_cardMg -/#[_] ?oZ ?obp //.
    rewrite -obp in p_pr; case: (prime_subgroupVti [group of Z] p_pr) => //.
    by rewrite cycle_subG Zb.
  pose P1 := P :&: X; have sP1P: P1 \subset P := subsetIl _ _.
  have pP1 := pgroupS sP1P pP.
  have [P2 sylP2 sP12] := Sylow_superset (subsetIr _ _) pP1.
  have defP1: P1 = 'C_P(B).
    rewrite -defB centM /= -/Z setIA /cycle cent_gen cent_set1 defX.
    by rewrite [P :&: _](setIidPl _) // centsC (subset_trans sZ_ZP) ?subsetIr.
  have dimPP1: logn p #|P : P1| <= 1.
    by rewrite defP1 logn_quotient_cent_abelem ?normal_norm ?(eqP dimB2).
  have{dimPP1} nsP12: P1 <| P2.
    have pP2 := pHall_pgroup sylP2.
    have: logn p #|P2 : P1| <= 1.
      apply: leq_trans dimPP1; rewrite dvdn_leq_log //.
      rewrite -(dvdn_pmul2l (cardG_gt0 [group of P1])) !Lagrange ?subsetIl //.
      rewrite -(part_pnat_id pP2) (card_Hall sylP).
      by rewrite partn_dvd ?cardSg ?subsetT.
    rewrite -(pfactorK 1 p_pr) -pfactor_dvdn ?prime_gt0 // -p_part.
    rewrite part_pnat_id ?(pnat_dvd (dvdn_indexg _ _)) //=.
    case: (primeP p_pr) => _ dv_p; move/dv_p=> {dv_p}.
    case/pred2P=> oP21; first by rewrite -(index1g sP12 oP21) normal_refl.
    by rewrite (p_maximal_normal pP2) ?p_index_maximal ?oP21.
  have nsZP1_2: 'Z(P1) <| P2 by rewrite (char_normal_trans (center_char _)).
  have sZKp: Z \subset 'O_{p^', p}(X).
    suff: 'Z(P1) \subset 'O_{p^', p}(X).
      apply: subset_trans; rewrite subsetI {1}defP1 (subset_trans sZB).
        by rewrite (subset_trans sZ_ZP) ?subIset // orbC centS.
      by rewrite subsetI normal_sub.
    apply: odd_p_abelian_constrained sylP2 (center_abelian _) nsZP1_2 => //.
    exact: mFT_odd.
  have coYZ: coprime #|Y| #|Z|.
    by rewrite oZ coprime_sym (pnat_coprime _ p'Y) ?pnatE ?inE.
  have nYZ := subset_trans sZA nYA.
  have <-: [~: Y, Z] * 'C_Y(Z) = Y.
    exact: coprime_cent_prod (solvableS sYX solX).
  set K := 'O_p^'(X); have [nKY nKZ]: Y \subset 'N(K) /\ Z \subset 'N(K).
    rewrite !(char_norm_trans (pcore_char _ _)) ?(subset_trans sZA) ?normsG //.
    by rewrite -defX cBA.
  rewrite mul_subG //.
    have coYZK: coprime #|Y / K| #|'O_p(X / K)|.
      by rewrite coprime_sym coprime_morphr ?(pnat_coprime (pcore_pgroup _ _)).
    rewrite -quotient_sub1 ?comm_subG // -(coprime_TIg coYZK) subsetI.
    rewrite /= -quotient_pseries2 !quotientS ?commg_subl //.
    by rewrite (subset_trans (commgSS sYX sZKp)) ?commg_subr //= gFnorm.
  have: 'O_p^'('C_X(Z)) \subset K.
    rewrite p'core_cent_pgroup // /psubgroup /pgroup oZ pnat_id //.
    by rewrite -defX (subset_trans sZA) ?cBA.
  apply: subset_trans; apply: subset_trans (pcoreS _ (subsetIr _ _)).
  have: cyclic Z by rewrite prime_cyclic ?oZ.
  case/cyclicP=> z defZ; have Zz: z \in Z by rewrite defZ cycle_id.
  rewrite subsetI setSI //= (IH z) ?subsetIr ?(pgroupS (subsetIl _ _)) //.
  - by rewrite defZ /= cent_gen cent_set1.
  - rewrite !inE -cycle_eq1 -defZ trivg_card_le1 oZ -ltnNge prime_gt1 //=.
    by rewrite (subsetP sZB).
  by rewrite normsI // norms_cent // cents_norm // centsC (subset_trans sZA).
set K := 'O_p^'(X); have nsKX: K <| X by exact: pcore_normal.
case/setD1P: B'b => ntb Bb.
have [sAX solX]: A \subset X /\ solvable X by rewrite -defX cBA ?solCB.
have sPX: P \subset X.
  by rewrite -defX -cent_set1 centsC sub1set; case/setIP: (subsetP sZ_ZP b Zb).
have [nKA nKY nKP]: [/\ A \subset 'N(K), Y \subset 'N(K) & P \subset 'N(K)].
  by rewrite !(subset_trans _ (normal_norm nsKX)).
have sylPX: p.-Sylow(X) P by exact: pHall_subl (subsetT _) sylP.
have sAKb: A \subset 'O_{p^', p}(X).
  exact: (odd_p_abelian_constrained (mFT_odd _)) abA nsAP.
have coYZK: coprime #|Y / K| #|'O_p(X / K)|.
  by rewrite coprime_sym coprime_morphr ?(pnat_coprime (pcore_pgroup _ _)).
have cYAq: A / K \subset 'C_('O_p(X / K))(Y / K).
  rewrite subsetI -quotient_pseries2 quotientS //= (sameP commG1P trivgP).
  rewrite /= -quotientR // -(coprime_TIg coYZK) subsetI /= -quotient_pseries2.
  rewrite !quotientS ?commg_subr // (subset_trans (commgSS sAKb sYX)) //.
  by rewrite commg_subl /= gFnorm.
have cYKq: Y / K \subset 'C('O_p(X / K)).
  apply: coprime_nil_faithful_cent_stab => /=.
  - by rewrite (char_norm_trans (pcore_char _ _)) ?normsG ?quotientS.
  - by rewrite coprime_morphr ?(pnat_coprime (pcore_pgroup _ _)).
  - exact: pgroup_nil (pcore_pgroup _ _).
  apply: subset_trans (cYAq); rewrite -defCA -['C_P(A) / K](morphim_restrm nKP).
  rewrite injm_cent ?ker_restrm ?ker_coset ?morphim_restrm -?quotientE //.
    rewrite setIid (setIidPr sAP) setISS ?centS //.
    by rewrite pcore_sub_Hall ?morphim_pHall.
  by rewrite coprime_TIg ?(pnat_coprime _ (pcore_pgroup _ _)).
rewrite -quotient_sub1 //= -/K -(coprime_TIg coYZK) subsetI subxx /=.
rewrite -Fitting_eq_pcore ?trivg_pcore_quotient // in cYKq *.
apply: subset_trans (cent_sub_Fitting (quotient_sol _ solX)).
by rewrite subsetI quotientS.
Qed.

(* This is B & G, Theorem 7.6 (the Thompson Transitivity Theorem). *)
Theorem Thompson_transitivity p q A :
    A \in 'SCN_3[p] -> q \in p^' ->
  [transitive 'O_p^'('C(A)), on |/|*(A; q) | 'JG].
Proof.
case/bigcupP=> P; rewrite 2!inE => sylP /andP[SCN_A mA3].
have [defZ def_pi']: 'Z(A) = A /\ \pi(A)^' =i p^'.
  rewrite inE -andbA in SCN_A; case/and3P: SCN_A => sAP _ /eqP defCA.
  case: (eqsVneq A 1) mA3 => /= [-> | ntA _].
    rewrite /rank big1_seq // => p1 _; rewrite /p_rank big1 // => E.
    by rewrite inE; case/andP; move/trivgP->; rewrite cards1 logn1.
  have [p_pr _ [k ->]] := pgroup_pdiv (pgroupS sAP (pHall_pgroup sylP)) ntA.
  split=> [|p1]; last by rewrite !inE primes_exp // primes_prime ?inE.
  by apply/eqP; rewrite eqEsubset subsetIl subsetI subxx -{1}defCA subsetIr.
rewrite -(eq_pcore _ def_pi') -def_pi' => pi'q.
apply: normed_constrained_rank3_trans; rewrite ?defZ //.
by apply: SCN_normed_constrained sylP _; rewrite inE SCN_A ltnW.
Qed.

End Seven.


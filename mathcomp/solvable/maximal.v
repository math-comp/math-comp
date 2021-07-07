(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice.
From mathcomp Require Import div fintype finfun bigop finset prime binomial.
From mathcomp Require Import fingroup morphism perm automorphism quotient.
From mathcomp Require Import action commutator gproduct gfunctor ssralg.
From mathcomp Require Import finalg zmodp cyclic pgroup center gseries.
From mathcomp Require Import nilpotent sylow abelian finmodule.

(******************************************************************************)
(*   This file establishes basic properties of several important classes of   *)
(* maximal subgroups: maximal, max and min normal, simple, characteristically *)
(* simple subgroups, the Frattini and Fitting subgroups, the Thompson         *)
(* critical subgroup, special and extra-special groups, and self-centralising *)
(* normal (SCN) subgroups. In detail, we define:                              *)
(*      charsimple G == G is characteristically simple (it has no nontrivial  *)
(*                      characteristic subgroups, and is nontrivial)          *)
(*           'Phi(G) == the Frattini subgroup of G, i.e., the intersection of *)
(*                      all its maximal proper subgroups.                     *)
(*             'F(G) == the Fitting subgroup of G, i.e., the largest normal   *)
(*                      nilpotent subgroup of G (defined as the (direct)      *)
(*                      product of all the p-cores of G).                     *)
(*      critical C G == C is a critical subgroup of G: C is characteristic    *)
(*                      (but not functorial) in G, the center of C contains   *)
(*                      both its Frattini subgroup and the commutator [G, C], *)
(*                      and is equal to the centraliser of C in G. The        *)
(*                      Thompson_critical theorem provides critical subgroups *)
(*                      for p-groups; we also show that in this case the      *)
(*                      centraliser of C in Aut G is a p-group as well.       *)
(*         special G == G is a special group: its center, Frattini, and       *)
(*                      derived sugroups coincide (we follow Aschbacher in    *)
(*                      not considering nontrivial elementary abelian groups  *)
(*                      as special); we show that a p-group factors under     *)
(*                      coprime action into special groups (Aschbacher 24.7). *)
(*    extraspecial G == G is a special group whose center has prime order     *)
(*                      (hence G is non-abelian).                             *)
(*           'SCN(G) == the set of self-centralising normal abelian subgroups *)
(*                      of G (the A <| G such that 'C_G(A) = A).              *)
(*         'SCN_n(G) == the subset of 'SCN(G) containing all groups with rank *)
(*                      at least n (i.e., A \in 'SCN(G) and 'm(A) >= n).      *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Section Defs.

Variable gT : finGroupType.
Implicit Types (A B D : {set gT}) (G : {group gT}).

Definition charsimple A := [min A of G | G :!=: 1 & G \char A].

Definition Frattini A := \bigcap_(G : {group gT} | maximal_eq G A) G.

Canonical Frattini_group A : {group gT} := Eval hnf in [group of Frattini A].

Definition Fitting A := \big[dprod/1]_(p <- primes #|A|) 'O_p(A).

Lemma Fitting_group_set G : group_set (Fitting G).
Proof.
suffices [F ->]: exists F : {group gT}, Fitting G = F by apply: groupP.
rewrite /Fitting; elim: primes (primes_uniq #|G|) => [_|p r IHr] /=.
  by exists [1 gT]%G; rewrite big_nil.
case/andP=> rp /IHr[F defF]; rewrite big_cons defF.
suffices{IHr} /and3P[p'F sFG nFG]: p^'.-group F && (F <| G).
  have nFGp: 'O_p(G) \subset 'N(F) := gFsub_trans _ nFG.
  have pGp: p.-group('O_p(G)) := pcore_pgroup p G.
  have{pGp} tiGpF: 'O_p(G) :&: F = 1 by rewrite coprime_TIg ?(pnat_coprime pGp).
  exists ('O_p(G) <*> F)%G; rewrite dprodEY // (sameP commG1P trivgP) -tiGpF.
  by rewrite subsetI commg_subl commg_subr (subset_trans sFG) // gFnorm.
move/bigdprodWY: defF => <- {F}; elim: r rp => [_|q r IHr] /=.
  by rewrite big_nil gen0 pgroup1 normal1.
rewrite inE eq_sym big_cons -joingE -joing_idr => /norP[qp /IHr {IHr}].
set F := <<_>> => /andP[p'F nsFG].
rewrite norm_joinEl /= -/F; last exact/gFsub_trans/normal_norm.
by rewrite pgroupM p'F normalM ?pcore_normal //= (pi_pgroup (pcore_pgroup q G)).
Qed.

Canonical Fitting_group G := group (Fitting_group_set G).

Definition critical A B :=
  [/\ A \char B,
      Frattini A \subset 'Z(A),
      [~: B, A] \subset 'Z(A)
   & 'C_B(A) = 'Z(A)].

Definition special A := Frattini A = 'Z(A) /\  A^`(1) = 'Z(A).

Definition extraspecial A := special A /\ prime #|'Z(A)|.

Definition SCN B := [set A : {group gT} | A <| B & 'C_B(A) == A].

Definition SCN_at n B := [set A in SCN B | n <= 'r(A)].

End Defs.

Arguments charsimple {gT} A%g.
Arguments Frattini {gT} A%g.
Arguments Fitting {gT} A%g.
Arguments critical {gT} A%g B%g.
Arguments special {gT} A%g.
Arguments extraspecial {gT} A%g.
Arguments SCN {gT} B%g.
Arguments SCN_at {gT} n%N B%g.

Notation "''Phi' ( A )" := (Frattini A)
  (at level 8, format "''Phi' ( A )") : group_scope.
Notation "''Phi' ( G )" := (Frattini_group G) : Group_scope.

Notation "''F' ( G )" := (Fitting G)
  (at level 8, format "''F' ( G )") : group_scope.
Notation "''F' ( G )" := (Fitting_group G) : Group_scope.

Notation "''SCN' ( B )" := (SCN B)
  (at level 8, format "''SCN' ( B )") : group_scope.
Notation "''SCN_' n ( B )" := (SCN_at n B)
  (at level 8, n at level 2, format "''SCN_' n ( B )") : group_scope.

Section PMax.

Variables (gT : finGroupType) (p : nat) (P M : {group gT}).
Hypothesis pP : p.-group P.

Lemma p_maximal_normal : maximal M P -> M <| P.
Proof.
case/maxgroupP=> /andP[sMP sPM] maxM; rewrite /normal sMP.
have:= subsetIl P 'N(M); rewrite subEproper.
case/predU1P=> [/setIidPl-> // | /maxM/= SNM]; case/negP: sPM.
rewrite (nilpotent_sub_norm (pgroup_nil pP) sMP) //.
by rewrite SNM // subsetI sMP normG.
Qed.

Lemma p_maximal_index : maximal M P -> #|P : M| = p.
Proof.
move=> maxM; have nM := p_maximal_normal maxM.
rewrite -card_quotient ?normal_norm //.
rewrite -(quotient_maximal _ nM) ?normal_refl // trivg_quotient in maxM.
case/maxgroupP: maxM; rewrite properEneq eq_sym sub1G andbT /=.
case/(pgroup_pdiv (quotient_pgroup M pP)) => p_pr /Cauchy[] // xq.
rewrite /order -cycle_subG subEproper => /predU1P[-> // | sxPq oxq_p _].
by move/(_ _ sxPq (sub1G _)) => xq1; rewrite -oxq_p xq1 cards1 in p_pr.
Qed.

Lemma p_index_maximal : M \subset P -> prime #|P : M| -> maximal M P.
Proof.
move=> sMP /primeP[lt1PM pr_PM].
apply/maxgroupP; rewrite properEcard sMP -(Lagrange sMP).
rewrite -{1}(muln1 #|M|) ltn_pmul2l //; split=> // H sHP sMH.
apply/eqP; rewrite eq_sym eqEcard sMH.
case/orP: (pr_PM _ (indexSg sMH (proper_sub sHP))) => /eqP iM.
  by rewrite -(Lagrange sMH) iM muln1 /=.
by have:= proper_card sHP; rewrite -(Lagrange sMH) iM Lagrange ?ltnn.
Qed.

End PMax.

Section Frattini.

Variables gT : finGroupType.
Implicit Type G M : {group gT}.

Lemma Phi_sub G : 'Phi(G) \subset G.
Proof. by rewrite bigcap_inf // /maximal_eq eqxx. Qed.

Lemma Phi_sub_max G M : maximal M G -> 'Phi(G) \subset M.
Proof. by move=> maxM; rewrite bigcap_inf // /maximal_eq predU1r. Qed.

Lemma Phi_proper G : G :!=: 1 -> 'Phi(G) \proper G.
Proof.
move/eqP; case/maximal_exists: (sub1G G) => [<- //| [M maxM _] _].
exact: sub_proper_trans (Phi_sub_max maxM) (maxgroupp maxM).
Qed.

Lemma Phi_nongen G X : 'Phi(G) <*> X = G -> <<X>> = G.
Proof.
move=> defG; have: <<X>> \subset G by rewrite -{1}defG genS ?subsetUr.
case/maximal_exists=> //= [[M maxM]]; rewrite gen_subG => sXM.
case/andP: (maxgroupp maxM) => _ /negP[].
by rewrite -defG gen_subG subUset Phi_sub_max.
Qed.

Lemma Frattini_continuous (rT : finGroupType) G (f : {morphism G >-> rT}) :
  f @* 'Phi(G) \subset 'Phi(f @* G).
Proof.
apply/bigcapsP=> M maxM; rewrite sub_morphim_pre ?Phi_sub // bigcap_inf //.
have {2}<-: f @*^-1 (f @* G) = G by rewrite morphimGK ?subsetIl.
by rewrite morphpre_maximal_eq ?maxM //; case/maximal_eqP: maxM.
Qed.

End Frattini.

Canonical Frattini_igFun := [igFun by Phi_sub & Frattini_continuous].
Canonical Frattini_gFun := [gFun by Frattini_continuous].

Section Frattini0.

Variable gT : finGroupType.
Implicit Types (rT : finGroupType) (D G : {group gT}).

Lemma Phi_char G : 'Phi(G) \char G.
Proof. exact: gFchar. Qed.

Lemma Phi_normal G : 'Phi(G) <| G.
Proof. exact: gFnormal. Qed.

Lemma injm_Phi rT D G (f : {morphism D >-> rT}) :
  'injm f -> G \subset D -> f @* 'Phi(G) = 'Phi(f @* G).
Proof. exact: injmF. Qed.

Lemma isog_Phi rT G (H : {group rT}) : G \isog H -> 'Phi(G) \isog 'Phi(H).
Proof. exact: gFisog. Qed.

Lemma PhiJ G x : 'Phi(G :^ x) = 'Phi(G) :^ x.
Proof.
rewrite -{1}(setIid G) -(setIidPr (Phi_sub G)) -!morphim_conj.
by rewrite injm_Phi ?injm_conj.
Qed.

End Frattini0.

Section Frattini2.

Variables gT : finGroupType.
Implicit Type G : {group gT}.

Lemma Phi_quotient_id G : 'Phi (G / 'Phi(G)) = 1.
Proof.
apply/trivgP; rewrite -cosetpreSK cosetpre1 /=; apply/bigcapsP=> M maxM.
have nPhi := Phi_normal G; have nPhiM: 'Phi(G) <| M.
  by apply: normalS nPhi; [apply: bigcap_inf | case/maximal_eqP: maxM].
by rewrite sub_cosetpre_quo ?bigcap_inf // quotient_maximal_eq.
Qed.

Lemma Phi_quotient_cyclic G : cyclic (G / 'Phi(G)) -> cyclic G.
Proof.
case/cyclicP=> /= Px; case: (cosetP Px) => x nPx ->{Px} defG.
apply/cyclicP; exists x; symmetry; apply: Phi_nongen.
rewrite -joing_idr norm_joinEr -?quotientK ?cycle_subG //.
by rewrite /quotient morphim_cycle //= -defG quotientGK ?Phi_normal.
Qed.

Variables (p : nat) (P : {group gT}).

Lemma trivg_Phi : p.-group P -> ('Phi(P) == 1) = p.-abelem P.
Proof.
move=> pP; case: (eqsVneq P 1) => [P1 | ntP].
  by rewrite P1 abelem1 -subG1 -P1 Phi_sub.
have [p_pr _ _] := pgroup_pdiv pP ntP.
apply/eqP/idP=> [trPhi | abP].
  apply/abelemP=> //; split=> [|x Px].
    apply/commG1P/trivgP; rewrite -trPhi.
    apply/bigcapsP=> M /predU1P[-> | maxM]; first exact: der1_subG.
    have /andP[_ nMP]: M <| P := p_maximal_normal pP maxM.
    rewrite der1_min // cyclic_abelian // prime_cyclic // card_quotient //.
    by rewrite (p_maximal_index pP).
  apply/set1gP; rewrite -trPhi; apply/bigcapP=> M.
  case/predU1P=> [-> | maxM]; first exact: groupX.
  have /andP[_ nMP] := p_maximal_normal pP maxM.
  have nMx : x \in 'N(M) by apply: subsetP Px.
  apply: coset_idr; rewrite ?groupX ?morphX //=; apply/eqP.
  rewrite -(p_maximal_index pP maxM) -card_quotient // -order_dvdn cardSg //=.
  by rewrite cycle_subG mem_quotient.
apply/trivgP/subsetP=> x Phi_x; rewrite -cycle_subG.
have Px: x \in P by apply: (subsetP (Phi_sub P)).
have sxP: <[x]> \subset P by rewrite cycle_subG.
case/splitsP: (abelem_splits abP sxP) => K /complP[tiKx defP].
have [-> | nt_x] := eqVneq x 1; first by rewrite cycle1.
have oxp := abelem_order_p abP Px nt_x.
rewrite /= -tiKx subsetI subxx cycle_subG.
apply: (bigcapP Phi_x); apply/orP; right.
apply: p_index_maximal; rewrite -?divgS -defP ?mulG_subr //.
by rewrite (TI_cardMg tiKx) mulnK // [#|_|]oxp.
Qed.

End Frattini2.

Section Frattini3.

Variables (gT : finGroupType) (p : nat) (P : {group gT}).
Hypothesis pP : p.-group P.

Lemma Phi_quotient_abelem : p.-abelem (P / 'Phi(P)).
Proof. by rewrite -trivg_Phi ?morphim_pgroup //= Phi_quotient_id. Qed.

Lemma Phi_joing : 'Phi(P) = P^`(1) <*> 'Mho^1(P).
Proof.
have [sPhiP nPhiP] := andP (Phi_normal P).
apply/eqP; rewrite eqEsubset join_subG.
case: (eqsVneq P 1) => [-> | ntP] in sPhiP *.
  by rewrite /= (trivgP sPhiP) sub1G der_subS Mho_sub.
have [p_pr _ _] := pgroup_pdiv pP ntP.
have [abP x1P] := abelemP p_pr Phi_quotient_abelem.
apply/andP; split.
  have nMP: P \subset 'N(P^`(1) <*> 'Mho^1(P)) by rewrite normsY // !gFnorm.
  rewrite -quotient_sub1 ?gFsub_trans //=.
  suffices <-: 'Phi(P / (P^`(1) <*> 'Mho^1(P))) = 1 by apply: morphimF.
  apply/eqP; rewrite (trivg_Phi (morphim_pgroup _ pP)) /= -quotientE.
  apply/abelemP=> //; rewrite [abelian _]quotient_cents2 ?joing_subl //.
  split=> // _ /morphimP[x Nx Px ->] /=.
  rewrite -morphX //= coset_id // (MhoE 1 pP) joing_idr expn1.
  by rewrite mem_gen //; apply/setUP; right; apply: imset_f.
rewrite -quotient_cents2 // [_ \subset 'C(_)]abP (MhoE 1 pP) gen_subG /=.
apply/subsetP=> _ /imsetP[x Px ->]; rewrite expn1.
have nPhi_x: x \in 'N('Phi(P)) by apply: (subsetP nPhiP).
by rewrite coset_idr ?groupX ?morphX ?x1P ?mem_morphim.
Qed.

Lemma Phi_Mho : abelian P -> 'Phi(P) = 'Mho^1(P).
Proof. by move=> cPP; rewrite Phi_joing (derG1P cPP) joing1G. Qed.

End Frattini3.

Section Frattini4.

Variables (p : nat) (gT : finGroupType).
Implicit Types (rT : finGroupType) (P G H K D : {group gT}).

Lemma PhiS G H : p.-group H -> G \subset H -> 'Phi(G) \subset 'Phi(H).
Proof.
move=> pH sGH; rewrite (Phi_joing pH) (Phi_joing (pgroupS sGH pH)).
by rewrite genS // setUSS ?dergS ?MhoS.
Qed.

Lemma morphim_Phi rT P D (f : {morphism D >-> rT}) :
  p.-group P -> P \subset D -> f @* 'Phi(P) = 'Phi(f @* P).
Proof.
move=> pP sPD; rewrite !(@Phi_joing _ p) ?morphim_pgroup //.
rewrite morphim_gen ?subUset ?gFsub_trans // morphimU -joingE.
by rewrite morphimR ?morphim_Mho.
Qed.

Lemma quotient_Phi P H :
  p.-group P -> P \subset 'N(H) -> 'Phi(P) / H = 'Phi(P / H).
Proof. exact: morphim_Phi. Qed.

(* This is Aschbacher (23.2) *)
Lemma Phi_min G H :
  p.-group G -> G \subset 'N(H) -> p.-abelem (G / H) -> 'Phi(G) \subset H.
Proof.
move=> pG nHG; rewrite -trivg_Phi ?quotient_pgroup // -subG1 /=.
by rewrite -(quotient_Phi pG) ?quotient_sub1 // gFsub_trans.
Qed.

Lemma Phi_cprod G H K :
  p.-group G -> H \* K = G -> 'Phi(H) \* 'Phi(K) = 'Phi(G).
Proof.
move=> pG defG; have [_ /mulG_sub[sHG sKG] cHK] := cprodP defG.
rewrite cprodEY /=; last by rewrite (centSS (Phi_sub _) (Phi_sub _)).
rewrite !(Phi_joing (pgroupS _ pG)) //=.
have /cprodP[_ <- /cent_joinEr <-] := der_cprod 1 defG.
have /cprodP[_ <- /cent_joinEr <-] := Mho_cprod 1 defG.
by rewrite !joingA /= -!(joingA H^`(1)) (joingC K^`(1)).
Qed.

Lemma Phi_mulg H K :
    p.-group H -> p.-group K -> K \subset 'C(H) ->
  'Phi(H * K) = 'Phi(H) * 'Phi(K).
Proof.
move=> pH pK cHK; have defHK := cprodEY cHK.
have [|_ ->] /= := cprodP (Phi_cprod _ defHK); rewrite cent_joinEr //.
by rewrite pgroupM pH.
Qed.

Lemma charsimpleP G :
  reflect (G :!=: 1 /\ forall K, K :!=: 1 -> K \char G -> K :=: G)
          (charsimple G).
Proof.
apply: (iffP mingroupP); rewrite char_refl andbT => -[ntG simG].
  by split=> // K ntK chK; apply: simG; rewrite ?ntK // char_sub.
by split=> // K /andP[ntK chK] _; apply: simG.
Qed.

End Frattini4.

Section Fitting.

Variable gT : finGroupType.
Implicit Types (p : nat) (G H : {group gT}).

Lemma Fitting_normal G : 'F(G) <| G.
Proof.
rewrite -['F(G)](bigdprodWY (erefl 'F(G))).
elim/big_rec: _ => [|p H _ nsHG]; first by rewrite gen0 normal1.
by rewrite -[<<_>>]joing_idr normalY ?pcore_normal.
Qed.

Lemma Fitting_sub G : 'F(G) \subset G.
Proof. by rewrite normal_sub ?Fitting_normal. Qed.

Lemma Fitting_nil G : nilpotent 'F(G).
Proof.
apply: (bigdprod_nil (erefl 'F(G))) => p _.
exact: pgroup_nil (pcore_pgroup p G).
Qed.

Lemma Fitting_max G H : H <| G -> nilpotent H -> H \subset 'F(G).
Proof.
move=> nsHG nilH; rewrite -(Sylow_gen H) gen_subG.
apply/bigcupsP=> P /SylowP[p _ sylP].
case Gp: (p \in \pi(G)); last first.
  rewrite card1_trivg ?sub1G // (card_Hall sylP).
  rewrite part_p'nat // (pnat_dvd (cardSg (normal_sub nsHG))) //.
  by rewrite /pnat cardG_gt0 all_predC has_pred1 Gp.
rewrite {P sylP}(nilpotent_Hall_pcore nilH sylP).
rewrite -(bigdprodWY (erefl 'F(G))) sub_gen //.
rewrite -(filter_pi_of (ltnSn _)) big_filter big_mkord.
apply: (bigcup_max (Sub p _)) => //= [|_].
  by have:= Gp; rewrite ltnS mem_primes => /and3P[_ ntG /dvdn_leq->].
by rewrite pcore_max ?pcore_pgroup ?gFnormal_trans.
Qed.

Lemma pcore_Fitting pi G : 'O_pi('F(G)) \subset 'O_pi(G).
Proof. by rewrite pcore_max ?pcore_pgroup ?gFnormal_trans ?Fitting_normal. Qed.

Lemma p_core_Fitting p G : 'O_p('F(G)) = 'O_p(G).
Proof.
apply/eqP; rewrite eqEsubset pcore_Fitting pcore_max ?pcore_pgroup //.
apply: normalS (normal_sub (Fitting_normal _)) (pcore_normal _ _).
exact: Fitting_max (pcore_normal _ _) (pgroup_nil (pcore_pgroup _ _)).
Qed.

Lemma nilpotent_Fitting G : nilpotent G -> 'F(G) = G.
Proof.
by move=> nilG; apply/eqP; rewrite eqEsubset Fitting_sub Fitting_max.
Qed.

Lemma Fitting_eq_pcore p G : 'O_p^'(G) = 1 -> 'F(G) = 'O_p(G).
Proof.
move=> p'G1; have /dprodP[_  /= <- _ _] := nilpotent_pcoreC p (Fitting_nil G).
by rewrite p_core_Fitting ['O_p^'(_)](trivgP _) ?mulg1 // -p'G1 pcore_Fitting.
Qed.

Lemma FittingEgen G :
  'F(G) = <<\bigcup_(p < #|G|.+1 | (p : nat) \in \pi(G)) 'O_p(G)>>.
Proof.
apply/eqP; rewrite eqEsubset gen_subG /=.
rewrite -{1}(bigdprodWY (erefl 'F(G))) (big_nth 0) big_mkord genS.
  by apply/bigcupsP=> p _; rewrite -p_core_Fitting pcore_sub.
apply/bigcupsP=> [[i /= lti]] _; set p := nth _ _ i.
have pi_p: p \in \pi(G) by rewrite mem_nth.
have p_dv_G: p %| #|G| by rewrite mem_primes in pi_p; case/and3P: pi_p.
have lepG: p < #|G|.+1 by rewrite ltnS dvdn_leq.
by rewrite (bigcup_max (Ordinal lepG)).
Qed.

End Fitting.

Section FittingFun.

Implicit Types gT rT : finGroupType.

Lemma morphim_Fitting : GFunctor.pcontinuous (@Fitting).
Proof.
move=> gT rT G D f; apply: Fitting_max.
  by rewrite morphim_normal ?Fitting_normal.
by rewrite morphim_nil ?Fitting_nil.
Qed.

Lemma FittingS gT (G H : {group gT}) : H \subset G -> H :&: 'F(G) \subset 'F(H).
Proof.
move=> sHG; rewrite -{2}(setIidPl sHG).
do 2!rewrite -(morphim_idm (subsetIl H _)) morphimIdom; apply: morphim_Fitting.
Qed.

Lemma FittingJ gT (G : {group gT}) x : 'F(G :^ x) = 'F(G) :^ x.
Proof.
rewrite !FittingEgen -genJ /= cardJg; symmetry; congr <<_>>.
rewrite (big_morph (conjugate^~ x) (fun A B => conjUg A B x) (imset0 _)).
by apply: eq_bigr => p _; rewrite pcoreJ.
Qed.

End FittingFun.

Canonical Fitting_igFun := [igFun by Fitting_sub & morphim_Fitting].
Canonical Fitting_gFun := [gFun by morphim_Fitting].
Canonical Fitting_pgFun := [pgFun by morphim_Fitting].

Section IsoFitting.

Variables (gT rT : finGroupType) (G D : {group gT}) (f : {morphism D >-> rT}).

Lemma Fitting_char : 'F(G) \char G. Proof. exact: gFchar. Qed.

Lemma injm_Fitting : 'injm f -> G \subset D -> f @* 'F(G) = 'F(f @* G).
Proof. exact: injmF. Qed.

Lemma isog_Fitting (H : {group rT}) : G \isog H -> 'F(G) \isog 'F(H).
Proof. exact: gFisog. Qed.

End IsoFitting.

Section CharSimple.

Variable gT : finGroupType.
Implicit Types (rT : finGroupType) (G H K L : {group gT}) (p : nat).

Lemma minnormal_charsimple G H : minnormal H G -> charsimple H.
Proof.
case/mingroupP=> /andP[ntH nHG] minH.
apply/charsimpleP; split=> // K ntK chK.
by apply: minH; rewrite ?ntK (char_sub chK, char_norm_trans chK).
Qed.

Lemma maxnormal_charsimple G H L :
  G <| L -> maxnormal H G L -> charsimple (G / H).
Proof.
case/andP=> sGL nGL /maxgroupP[/andP[/andP[sHG not_sGH] nHL] maxH].
have nHG: G \subset 'N(H) := subset_trans sGL nHL.
apply/charsimpleP; rewrite -subG1 quotient_sub1 //; split=> // HK ntHK chHK.
case/(inv_quotientN _): (char_normal chHK) => [|K defHK sHK]; first exact/andP.
case/andP; rewrite subEproper defHK => /predU1P[-> // | ltKG] nKG.
have nHK: H <| K by rewrite /normal sHK (subset_trans (proper_sub ltKG)).
case/negP: ntHK; rewrite defHK -subG1 quotient_sub1 ?normal_norm //.
rewrite (maxH K) // ltKG -(quotientGK nHK) -defHK norm_quotient_pre //.
by rewrite (char_norm_trans chHK) ?quotient_norms.
Qed.

Lemma abelem_split_dprod rT p (A B : {group rT}) :
  p.-abelem A -> B \subset A -> exists C : {group rT}, B \x C = A.
Proof.
move=> abelA sBA; have [_ cAA _]:= and3P abelA.
case/splitsP: (abelem_splits abelA sBA) => C /complP[tiBC defA].
by exists C; rewrite dprodE // (centSS _ sBA cAA) // -defA mulG_subr.
Qed.

Lemma p_abelem_split1 rT p (A : {group rT}) x :
     p.-abelem A -> x \in A ->
  exists B : {group rT}, [/\ B \subset A, #|B| = #|A| %/ #[x] & <[x]> \x B = A].
Proof.
move=> abelA Ax; have sxA: <[x]> \subset A by rewrite cycle_subG.
have [B defA] := abelem_split_dprod abelA sxA.
have [_ defxB _ ti_xB] := dprodP defA.
have sBA: B \subset A by rewrite -defxB mulG_subr.
by exists B; split; rewrite // -defxB (TI_cardMg ti_xB) mulKn ?order_gt0.
Qed.

Lemma abelem_charsimple p G : p.-abelem G -> G :!=: 1 -> charsimple G.
Proof.
move=> abelG ntG; apply/charsimpleP; split=> // K ntK /charP[sKG chK].
case/eqVproper: sKG => // /properP[sKG [x Gx notKx]].
have ox := abelem_order_p abelG Gx (group1_contra notKx).
have [A [sAG oA defA]] := p_abelem_split1 abelG Gx.
case/trivgPn: ntK => y Ky nty; have Gy := subsetP sKG y Ky.
have{nty} oy := abelem_order_p abelG Gy nty.
have [B [sBG oB defB]] := p_abelem_split1 abelG Gy.
have: isog A B; last case/isogP=> fAB injAB defAB.
  rewrite (isog_abelem_card _ (abelemS sAG abelG)) (abelemS sBG) //=.
  by rewrite oA oB ox oy.
have: isog <[x]> <[y]>; last case/isogP=> fxy injxy /= defxy.
  by rewrite isog_cyclic_card ?cycle_cyclic // [#|_|]oy -ox eqxx.
have cfxA: fAB @* A \subset 'C(fxy @* <[x]>).
  by rewrite defAB defxy; case/dprodP: defB.
have injf: 'injm (dprodm defA cfxA).
  by rewrite injm_dprodm injAB injxy defAB defxy; apply/eqP; case/dprodP: defB.
case/negP: notKx; rewrite -cycle_subG -(injmSK injf) ?cycle_subG //=.
rewrite morphim_dprodml // defxy cycle_subG /= chK //.
have [_ {4}<- _ _] := dprodP defB; have [_ {3}<- _ _] := dprodP defA.
by rewrite morphim_dprodm // defAB defxy.
Qed.

Lemma charsimple_dprod G : charsimple G ->
  exists H : {group gT}, [/\ H \subset G, simple H
                         & exists2 I : {set {perm gT}}, I \subset Aut G
                         & \big[dprod/1]_(f in I) f @: H = G].
Proof.
case/charsimpleP=> ntG simG.
have [H minH sHG]: {H : {group gT} | minnormal H G & H \subset G}.
  by apply: mingroup_exists; rewrite ntG normG.
case/mingroupP: minH => /andP[ntH nHG] minH.
pose Iok (I : {set {perm gT}}) :=
  (I \subset Aut G) &&
  [exists (M : {group gT} | M <| G), \big[dprod/1]_(f in I) f @: H == M].
have defH: (1 : {perm gT}) @: H = H.
  apply/eqP; rewrite eqEcard card_imset ?leqnn; last exact: perm_inj.
  by rewrite andbT; apply/subsetP=> _ /imsetP[x Hx ->]; rewrite perm1.
have [|I] := @maxset_exists _ Iok 1.
  rewrite /Iok sub1G; apply/existsP; exists H.
  by rewrite /normal sHG nHG (big_pred1 1) => [|f]; rewrite ?defH /= ?inE.
case/maxsetP=> /andP[Aut_I /exists_eq_inP[M /andP[sMG nMG] defM]] maxI.
rewrite sub1set=> ntI; case/eqVproper: sMG => [defG | /andP[sMG not_sGM]].
  exists H; split=> //; last by exists I; rewrite ?defM.
  apply/mingroupP; rewrite ntH normG; split=> // N /andP[ntN nNH] sNH.
  apply: minH => //; rewrite ntN /= -defG.
  move: defM; rewrite (bigD1 1) //= defH; case/dprodP=> [[_ K _ ->] <- cHK _].
  by rewrite mul_subG // cents_norm // (subset_trans cHK) ?centS.
have defG: <<\bigcup_(f in Aut G) f @: H>> = G.
  have sXG: \bigcup_(f in Aut G) f @: H \subset G.
    by apply/bigcupsP=> f Af; rewrite -(im_autm Af) morphimEdom imsetS.
  apply: simG.
    apply: contra ntH; rewrite -!subG1; apply: subset_trans.
    by rewrite sub_gen // (bigcup_max 1) ?group1 ?defH.
  rewrite /characteristic gen_subG sXG; apply/forall_inP=> f Af.
  rewrite -(autmE Af) -morphimEsub ?gen_subG ?morphim_gen // genS //.
  rewrite morphimEsub //= autmE.
  apply/subsetP=> _ /imsetP[_ /bigcupP[g Ag /imsetP[x Hx ->]] ->].
  apply/bigcupP; exists (g * f); first exact: groupM.
  by apply/imsetP; exists x; rewrite // permM.
have [f Af sfHM]: exists2 f, f \in Aut G & ~~ (f @: H \subset M).
  move: not_sGM; rewrite -{1}defG gen_subG; case/subsetPn=> x.
  by case/bigcupP=> f Af fHx Mx; exists f => //; apply/subsetPn; exists x.
case If: (f \in I).
  by case/negP: sfHM; rewrite -(bigdprodWY defM) sub_gen // (bigcup_max f).
case/idP: (If); rewrite -(maxI ([set f] :|: I)) ?subsetUr ?inE ?eqxx //.
rewrite {maxI}/Iok subUset sub1set Af {}Aut_I; apply/existsP.
have sfHG: autm Af @* H \subset G by rewrite -{4}(im_autm Af) morphimS.
have{minH nHG} /mingroupP[/andP[ntfH nfHG] minfH]: minnormal (autm Af @* H) G.
  apply/mingroupP; rewrite andbC -{1}(im_autm Af) morphim_norms //=.
  rewrite -subG1 sub_morphim_pre // -kerE ker_autm subG1.
  split=> // N /andP[ntN nNG] sNfH.
  have sNG: N \subset G := subset_trans sNfH sfHG.
  apply/eqP; rewrite eqEsubset sNfH sub_morphim_pre //=.
  rewrite -(morphim_invmE (injm_autm Af)) [_ @* N]minH //=.
    rewrite -subG1 sub_morphim_pre /= ?im_autm // morphpre_invm morphim1 subG1.
    by rewrite ntN -{1}(im_invm (injm_autm Af)) /= {2}im_autm morphim_norms.
  by rewrite sub_morphim_pre /= ?im_autm // morphpre_invm.
have{minfH sfHM} tifHM: autm Af @* H :&: M = 1.
  apply/eqP/idPn=> ntMfH; case/setIidPl: sfHM.
  rewrite -(autmE Af) -morphimEsub //.
  by apply: minfH; rewrite ?subsetIl // ntMfH normsI.
have cfHM: M \subset 'C(autm Af @* H).
  rewrite centsC (sameP commG1P trivgP) -tifHM subsetI commg_subl commg_subr.
  by rewrite (subset_trans sMG) // (subset_trans sfHG).
exists (autm Af @* H <*> M)%G; rewrite /normal /= join_subG sMG sfHG normsY //=.
rewrite (bigD1 f) ?inE ?eqxx // (eq_bigl (mem I)) /= => [|g]; last first.
  by rewrite /= !inE andbC; case: eqP => // ->.
by rewrite defM -(autmE Af) -morphimEsub // dprodE // cent_joinEr ?eqxx.
Qed.

Lemma simple_sol_prime G : solvable G -> simple G -> prime #|G|.
Proof.
move=> solG /simpleP[ntG simG].
have{solG} cGG: abelian G.
  apply/commG1P; case/simG: (der_normal 1 G) => // /eqP/idPn[].
  by rewrite proper_neq // (sol_der1_proper solG).
case: (trivgVpdiv G) ntG => [-> | [p p_pr]]; first by rewrite eqxx.
case/Cauchy=> // x Gx oxp _; move: p_pr; rewrite -oxp orderE.
have: <[x]> <| G by rewrite -sub_abelian_normal ?cycle_subG.
by case/simG=> -> //; rewrite cards1.
Qed.

Lemma charsimple_solvable G : charsimple G -> solvable G -> is_abelem G.
Proof.
case/charsimple_dprod=> H [sHG simH [I Aut_I defG]] solG.
have p_pr: prime #|H| by apply: simple_sol_prime (solvableS sHG solG) simH.
set p := #|H| in p_pr; apply/is_abelemP; exists p => //.
elim/big_rec: _ (G) defG => [_ <-|f B If IH_B M defM]; first exact: abelem1.
have [Af [[_ K _ defB] _ _ _]] := (subsetP Aut_I f If, dprodP defM).
rewrite (dprod_abelem p defM) defB IH_B // andbT -(autmE Af) -morphimEsub //=.
rewrite morphim_abelem ?abelemE // exponent_dvdn.
by rewrite cyclic_abelian ?prime_cyclic.
Qed.

Lemma minnormal_solvable L G H :
    minnormal H L -> H \subset G -> solvable G ->
  [/\ L \subset 'N(H), H :!=: 1 & is_abelem H].
Proof.
move=> minH sHG solG; have /andP[ntH nHL] := mingroupp minH.
split=> //; apply: (charsimple_solvable (minnormal_charsimple minH)).
exact: solvableS solG.
Qed.

Lemma solvable_norm_abelem L G :
    solvable G -> G <| L -> G :!=: 1 ->
  exists H : {group gT}, [/\ H \subset G, H <| L, H :!=: 1 & is_abelem H].
Proof.
move=> solG /andP[sGL nGL] ntG.
have [H minH sHG]: {H : {group gT} | minnormal H L & H \subset G}.
  by apply: mingroup_exists; rewrite ntG.
have [nHL ntH abH] := minnormal_solvable minH sHG solG.
by exists H; split; rewrite // /normal (subset_trans sHG).
Qed.

Lemma trivg_Fitting G : solvable G -> ('F(G) == 1) = (G :==: 1).
Proof.
move=> solG; apply/idP/idP=> [F1 | /eqP->]; last by rewrite gF1.
apply/idPn=> /(solvable_norm_abelem solG (normal_refl _))[M [_ nsMG ntM]].
case/is_abelemP=> p _ /and3P[pM _ _]; case/negP: ntM.
by rewrite -subG1 -(eqP F1) Fitting_max ?(pgroup_nil pM).
Qed.

Lemma Fitting_pcore pi G : 'F('O_pi(G)) = 'O_pi('F(G)).
Proof.
apply/eqP; rewrite eqEsubset.
rewrite (subset_trans _ (pcoreS _ (Fitting_sub _))); last first.
  by rewrite subsetI Fitting_sub Fitting_max ?Fitting_nil ?gFnormal_trans.
rewrite (subset_trans _ (FittingS (pcore_sub _ _))) // subsetI pcore_sub.
by rewrite pcore_max ?pcore_pgroup ?gFnormal_trans.
Qed.

End CharSimple.

Section SolvablePrimeFactor.

Variables (gT : finGroupType) (G : {group gT}).

Lemma index_maxnormal_sol_prime (H : {group gT}) :
  solvable G -> maxnormal H G G -> prime #|G : H|.
Proof.
move=> solG maxH; have nsHG := maxnormal_normal maxH.
rewrite -card_quotient ?normal_norm // simple_sol_prime ?quotient_sol //.
by rewrite quotient_simple.
Qed.

Lemma sol_prime_factor_exists :
  solvable G -> G :!=: 1 -> {H : {group gT} | H <| G & prime #|G : H| }.
Proof.
move=> solG /ex_maxnormal_ntrivg[H maxH].
by exists H; [apply: maxnormal_normal | apply: index_maxnormal_sol_prime].
Qed.

End SolvablePrimeFactor.

Section Special.

Variables (gT : finGroupType) (p : nat) (A G : {group gT}).

(* This is Aschbacher (23.7) *)
Lemma center_special_abelem : p.-group G -> special G -> p.-abelem 'Z(G).
Proof.
move=> pG [defPhi defG'].
have [-> | ntG] := eqsVneq G 1; first by rewrite center1 abelem1.
have [p_pr _ _] := pgroup_pdiv pG ntG.
have fM: {in 'Z(G) &, {morph expgn^~ p : x y / x * y}}.
  by move=> x y /setIP[_ /centP cxG] /setIP[/cxG cxy _]; apply: expgMn.
rewrite abelemE //= center_abelian; apply/exponentP=> /= z Zz.
apply: (@kerP _ _ _ (Morphism fM)) => //; apply: subsetP z Zz.
rewrite -{1}defG' gen_subG; apply/subsetP=> _ /imset2P[x y Gx Gy ->].
have Zxy: [~ x, y] \in 'Z(G) by rewrite -defG' mem_commg.
have Zxp: x ^+ p \in 'Z(G).
  rewrite -defPhi (Phi_joing pG) (MhoE 1 pG) joing_idr mem_gen // !inE.
  by rewrite expn1 orbC (imset_f (expgn^~ p)).
rewrite mem_morphpre /= ?defG' ?Zxy // inE -commXg; last first.
  by red; case/setIP: Zxy => _ /centP->.
by apply/commgP; red; case/setIP: Zxp => _ /centP->.
Qed.

Lemma exponent_special : p.-group G -> special G -> exponent G %| p ^ 2.
Proof.
move=> pG spG; have [defPhi _] := spG.
have /and3P[_ _ expZ] := center_special_abelem pG spG.
apply/exponentP=> x Gx; rewrite expgM (exponentP expZ) // -defPhi.
by rewrite (Phi_joing pG) mem_gen // inE orbC (Mho_p_elt 1) ?(mem_p_elt pG).
Qed.

(* Aschbacher 24.7 (replaces Gorenstein 5.3.7) *)
Theorem abelian_charsimple_special :
    p.-group G -> coprime #|G| #|A| -> [~: G, A] = G ->
    \bigcup_(H : {group gT} | (H \char G) && abelian H) H \subset 'C(A) ->
  special G /\ 'C_G(A) = 'Z(G).
Proof.
move=> pG coGA defG /bigcupsP cChaA.
have cZA: 'Z(G) \subset 'C_G(A).
  by rewrite subsetI center_sub cChaA // center_char center_abelian.
have cChaG (H : {group gT}): H \char G -> abelian H -> H \subset 'Z(G).
  move=> chH abH; rewrite subsetI char_sub //= centsC -defG.
  rewrite comm_norm_cent_cent ?(char_norm chH) -?commg_subl ?defG //.
  by rewrite centsC cChaA ?chH.
have cZ2GG: [~: 'Z_2(G), G, G] = 1.
  by apply/commG1P; rewrite (subset_trans (ucn_comm 1 G)) // ucn1 subsetIr.
have{cZ2GG} cG'Z: 'Z_2(G) \subset 'C(G^`(1)).
  by rewrite centsC; apply/commG1P; rewrite three_subgroup // (commGC G).
have{cG'Z} sZ2G'_Z: 'Z_2(G) :&: G^`(1) \subset 'Z(G).
  apply: cChaG; first by rewrite charI ?ucn_char ?der_char.
  by rewrite /abelian subIset // (subset_trans cG'Z) // centS ?subsetIr.
have{sZ2G'_Z} sG'Z: G^`(1) \subset 'Z(G).
  rewrite der1_min ?gFnorm //; apply/derG1P.
  have /TI_center_nil: nilpotent (G / 'Z(G)) := quotient_nil _ (pgroup_nil pG).
  apply; first exact: gFnormal; rewrite /= setIC -ucn1 -ucn_central.
  rewrite -quotient_der ?gFnorm // -quotientGI ?ucn_subS ?quotientS1 //=.
  by rewrite ucn1.
have sCG': 'C_G(A) \subset G^`(1).
  rewrite -quotient_sub1 //; last by rewrite subIset ?gFnorm.
  rewrite (subset_trans (quotient_subcent _ G A)) //= -[G in G / _]defG.
  have nGA: A \subset 'N(G) by rewrite -commg_subl defG.
  rewrite quotientR ?gFnorm_trans ?normG //.
  rewrite coprime_abel_cent_TI ?quotient_norms ?coprime_morph //.
  exact: sub_der1_abelian.
have defZ: 'Z(G) = G^`(1) by apply/eqP; rewrite eqEsubset (subset_trans cZA).
split; last by apply/eqP; rewrite eqEsubset cZA defZ sCG'.
split=> //; apply/eqP; rewrite eqEsubset defZ (Phi_joing pG) joing_subl.
have:= pG; rewrite -pnat_exponent => /p_natP[n expGpn].
rewrite join_subG subxx andbT /= -defZ -(subnn n.-1).
elim: {2}n.-1 => [|m IHm].
  rewrite (MhoE _ pG) gen_subG; apply/subsetP=> _ /imsetP[x Gx ->].
  rewrite subn0 -subn1 -add1n -maxnE maxnC maxnE expnD.
  by rewrite expgM -expGpn expg_exponent ?groupX ?group1.
rewrite cChaG ?Mho_char //= (MhoE _ pG) /abelian cent_gen gen_subG.
apply/centsP=> _ /imsetP[x Gx ->] _ /imsetP[y Gy ->].
move: sG'Z; rewrite subsetI centsC => /andP[_ /centsP cGG'].
apply/commgP; rewrite {1}expnSr expgM.
rewrite commXg -?commgX; try by apply: cGG'; rewrite ?mem_commg ?groupX.
apply/commgP; rewrite subsetI Mho_sub centsC in IHm.
apply: (centsP IHm); first by rewrite groupX.
rewrite -add1n -(addn1 m) subnDA -maxnE maxnC maxnE.
rewrite -expgM -expnSr -addSn expnD expgM groupX //=.
by rewrite Mho_p_elt ?(mem_p_elt pG).
Qed.

End Special.

Section Extraspecial.

Variables (p : nat) (gT rT : finGroupType).
Implicit Types D E F G H K M R S T U : {group gT}.

Section Basic.

Variable S : {group gT}.
Hypotheses (pS : p.-group S) (esS : extraspecial S).

Let pZ : p.-group 'Z(S) := pgroupS (center_sub S) pS.
Lemma extraspecial_prime : prime p.
Proof.
by case: esS => _ /prime_gt1; rewrite cardG_gt1; case/(pgroup_pdiv pZ).
Qed.

Lemma card_center_extraspecial : #|'Z(S)| = p.
Proof. by apply/eqP; apply: (pgroupP pZ); case: esS. Qed.

Lemma min_card_extraspecial : #|S| >= p ^ 3.
Proof.
have p_gt1 := prime_gt1 extraspecial_prime.
rewrite leqNgt (card_pgroup pS) ltn_exp2l // ltnS.
case: esS => [[_ defS']]; apply: contraL => /(p2group_abelian pS)/derG1P S'1.
by rewrite -defS' S'1 cards1.
Qed.

End Basic.

Lemma card_p3group_extraspecial E :
  prime p -> #|E| = (p ^ 3)%N -> #|'Z(E)| = p -> extraspecial E.
Proof.
move=> p_pr oEp3 oZp; have p_gt0 := prime_gt0 p_pr.
have pE: p.-group E by rewrite /pgroup oEp3 pnatX pnat_id.
have pEq: p.-group (E / 'Z(E))%g by rewrite quotient_pgroup.
have /andP[sZE nZE] := center_normal E.
have oEq: #|E / 'Z(E)|%g = (p ^ 2)%N.
  by rewrite card_quotient -?divgS // oEp3 oZp expnS mulKn.
have cEEq: abelian (E / 'Z(E))%g by apply: card_p2group_abelian oEq.
have not_cEE: ~~ abelian E.
  have: #|'Z(E)| < #|E| by rewrite oEp3 oZp (ltn_exp2l 1) ?prime_gt1.
  by apply: contraL => cEE; rewrite -leqNgt subset_leq_card // subsetI subxx.
have defE': E^`(1) = 'Z(E).
  apply/eqP; rewrite eqEsubset der1_min //=; apply: contraR not_cEE => not_sE'Z.
  apply/commG1P/(TI_center_nil (pgroup_nil pE) (der_normal 1 _)).
  by rewrite setIC prime_TIg ?oZp.
split; [split=> // | by rewrite oZp]; apply/eqP.
rewrite eqEsubset andbC -{1}defE' {1}(Phi_joing pE) joing_subl.
rewrite -quotient_sub1 ?gFsub_trans ?subG1 //=.
rewrite (quotient_Phi pE) //= (trivg_Phi pEq).
apply/abelemP=> //; split=> // Zx EqZx; apply/eqP; rewrite -order_dvdn /order.
rewrite (card_pgroup (mem_p_elt pEq EqZx)) (@dvdn_exp2l _ _ 1) //.
rewrite leqNgt -pfactor_dvdn // -oEq; apply: contra not_cEE => sEqZx.
rewrite cyclic_center_factor_abelian //; apply/cyclicP.
exists Zx; apply/eqP; rewrite eq_sym eqEcard cycle_subG EqZx -orderE.
exact: dvdn_leq sEqZx.
Qed.

Lemma p3group_extraspecial G :
  p.-group G -> ~~ abelian G -> logn p #|G| <= 3 -> extraspecial G.
Proof.
move=> pG not_cGG; have /andP[sZG nZG] := center_normal G.
have ntG: G :!=: 1 by apply: contraNneq not_cGG => ->; apply: abelian1.
have ntZ: 'Z(G) != 1 by rewrite (center_nil_eq1 (pgroup_nil pG)).
have [p_pr _ [n oG]] := pgroup_pdiv pG ntG; rewrite oG pfactorK //.
have [_ _ [m oZ]] := pgroup_pdiv (pgroupS sZG pG) ntZ.
have lt_m1_n: m.+1 < n.
  suffices: 1 < logn p #|(G / 'Z(G))|.
    rewrite card_quotient // -divgS // logn_div ?cardSg //.
    by rewrite oG oZ !pfactorK // ltn_subRL addn1.
  rewrite ltnNge; apply: contra not_cGG => cycGs.
  apply: cyclic_center_factor_abelian; rewrite (dvdn_prime_cyclic p_pr) //.
  by rewrite (card_pgroup (quotient_pgroup _ pG)) (dvdn_exp2l _ cycGs).
rewrite -{lt_m1_n}(subnKC lt_m1_n) !addSn !ltnS leqn0 in oG *.
case: m => // in oZ oG * => /eqP n2; rewrite {n}n2 in oG.
exact: card_p3group_extraspecial oZ.
Qed.

Lemma extraspecial_nonabelian G : extraspecial G -> ~~ abelian G.
Proof.
case=> [[_ defG'] oZ]; rewrite /abelian (sameP commG1P eqP).
by rewrite -derg1 defG' -cardG_gt1 prime_gt1.
Qed.

Lemma exponent_2extraspecial G : 2.-group G -> extraspecial G -> exponent G = 4.
Proof.
move=> p2G esG; have [spG _] := esG.
case/dvdn_pfactor: (exponent_special p2G spG) => // k.
rewrite leq_eqVlt ltnS => /predU1P[-> // | lek1] expG.
case/negP: (extraspecial_nonabelian esG).
by rewrite (@abelem_abelian _ 2) ?exponent2_abelem // expG pfactor_dvdn.
Qed.

Lemma injm_special D G (f : {morphism D >-> rT}) :
  'injm f -> G \subset D -> special G -> special (f @* G).
Proof.
move=> injf sGD [defPhiG defG'].
by rewrite /special -morphim_der // -injm_Phi // defPhiG defG' injm_center.
Qed.

Lemma injm_extraspecial D G (f : {morphism D >-> rT}) :
  'injm f -> G \subset D -> extraspecial G -> extraspecial (f @* G).
Proof.
move=> injf sGD [spG ZG_pr]; split; first exact: injm_special spG.
by rewrite -injm_center // card_injm // subIset ?sGD.
Qed.

Lemma isog_special G (R : {group rT}) :
  G \isog R -> special G -> special R.
Proof. by case/isogP=> f injf <-; apply: injm_special. Qed.

Lemma isog_extraspecial G (R : {group rT}) :
  G \isog R -> extraspecial G -> extraspecial R.
Proof. by case/isogP=> f injf <-; apply: injm_extraspecial. Qed.

Lemma cprod_extraspecial G H K :
    p.-group G -> H \* K = G -> H :&: K = 'Z(H) ->
  extraspecial H -> extraspecial K -> extraspecial G.
Proof.
move=> pG defG ziHK [[PhiH defH'] ZH_pr] [[PhiK defK'] ZK_pr].
have [_ defHK cHK]:= cprodP defG.
have sZHK: 'Z(H) \subset 'Z(K).
  by rewrite subsetI -{1}ziHK subsetIr subIset // centsC cHK.
have{sZHK} defZH: 'Z(H) = 'Z(K).
  by apply/eqP; rewrite eqEcard sZHK leq_eqVlt eq_sym -dvdn_prime2 ?cardSg.
have defZ: 'Z(G) = 'Z(K).
  by case/cprodP: (center_cprod defG) => /= _ <- _; rewrite defZH mulGid.
split; first split; rewrite defZ //.
  by have /cprodP[_ <- _] := Phi_cprod pG defG; rewrite PhiH PhiK defZH mulGid.
by have /cprodP[_ <- _] := der_cprod 1 defG; rewrite defH' defK' defZH mulGid.
Qed.

(* Lemmas bundling Aschbacher (23.10) with (19.1), (19.2), (19.12) and (20.8) *)
Section ExtraspecialFormspace.

Variable G : {group gT}.
Hypotheses (pG : p.-group G) (esG : extraspecial G).

Let p_pr := extraspecial_prime pG esG.
Let oZ := card_center_extraspecial pG esG.
Let p_gt1 := prime_gt1 p_pr.
Let p_gt0 := prime_gt0 p_pr.

(* This encasulates Aschbacher (23.10)(1). *)
Lemma cent1_extraspecial_maximal x :
  x \in G -> x \notin 'Z(G) -> maximal 'C_G[x] G.
Proof.
move=> Gx notZx; pose f y := [~ x, y]; have [[_ defG'] prZ] := esG.
have{defG'} fZ y: y \in G -> f y \in 'Z(G).
  by move=> Gy; rewrite -defG' mem_commg.
have fM: {in G &, {morph f : y z / y * z}}%g.
  move=> y z Gy Gz; rewrite {1}/f commgMJ conjgCV -conjgM (conjg_fixP _) //.
  rewrite (sameP commgP cent1P); apply: subsetP (fZ y Gy).
  by rewrite subIset // orbC -cent_set1 centS // sub1set !(groupM, groupV).
pose fm := Morphism fM.
have fmG: fm @* G = 'Z(G).
  have sfmG: fm @* G \subset 'Z(G).
    by apply/subsetP=> _ /morphimP[z _ Gz ->]; apply: fZ.
  apply/eqP; rewrite eqEsubset sfmG; apply: contraR notZx => /(prime_TIg prZ).
  rewrite (setIidPr _) // => fmG1; rewrite inE Gx; apply/centP=> y Gy.
  by apply/commgP; rewrite -in_set1 -[[set _]]fmG1; apply: mem_morphim.
have ->: 'C_G[x] = 'ker fm.
  apply/setP=> z; rewrite inE (sameP cent1P commgP) !inE.
  by rewrite -invg_comm eq_invg_mul mulg1.
rewrite p_index_maximal ?subsetIl // -card_quotient ?ker_norm //.
by rewrite (card_isog (first_isog fm)) /= fmG.
Qed.

(* This is the tranposition of the hyperplane dimension theorem (Aschbacher   *)
(* (19.1)) to subgroups of an extraspecial group.                             *)
Lemma subcent1_extraspecial_maximal U x :
  U \subset G -> x \in G :\: 'C(U) -> maximal 'C_U[x] U.
Proof.
move=> sUG /setDP[Gx not_cUx]; apply/maxgroupP; split=> [|H ltHU sCxH].
  by rewrite /proper subsetIl subsetI subxx sub_cent1.
case/andP: ltHU => sHU not_sHU; have sHG := subset_trans sHU sUG.
apply/eqP; rewrite eqEsubset sCxH subsetI sHU /= andbT.
apply: contraR not_sHU => not_sHCx.
have maxCx: maximal 'C_G[x] G.
  rewrite cent1_extraspecial_maximal //; apply: contra not_cUx.
  by rewrite inE Gx; apply: subsetP (centS sUG) _.
have nsCx := p_maximal_normal pG maxCx.
rewrite -(setIidPl sUG) -(mulg_normal_maximal nsCx maxCx sHG) ?subsetI ?sHG //.
by rewrite -group_modr //= setIA (setIidPl sUG) mul_subG.
Qed.

(* This is the tranposition of the orthogonal subspace dimension theorem      *)
(* (Aschbacher (19.2)) to subgroups of an extraspecial group.                 *)
Lemma card_subcent_extraspecial U :
  U \subset G -> #|'C_G(U)| = (#|'Z(G) :&: U| * #|G : U|)%N.
Proof.
move=> sUG; rewrite setIAC (setIidPr sUG).
have [m leUm] := ubnP #|U|; elim: m => // m IHm in U leUm sUG *.
have [cUG | not_cUG]:= orP (orbN (G \subset 'C(U))).
  by rewrite !(setIidPl _) ?Lagrange // centsC.
have{not_cUG} [x Gx not_cUx] := subsetPn not_cUG.
pose W := 'C_U[x]; have sCW_G: 'C_G(W) \subset G := subsetIl G _.
have maxW: maximal W U by rewrite subcent1_extraspecial_maximal // inE not_cUx.
have nsWU: W <| U := p_maximal_normal (pgroupS sUG pG) maxW.
have ltWU: W \proper U by apply: maxgroupp maxW.
have [sWU [u Uu notWu]] := properP ltWU; have sWG := subset_trans sWU sUG.
have defU: W * <[u]> = U by rewrite (mulg_normal_maximal nsWU) ?cycle_subG.
have iCW_CU: #|'C_G(W) : 'C_G(U)| = p.
  rewrite -defU centM cent_cycle setIA /=; rewrite inE Uu cent1C in notWu.
  apply: p_maximal_index (pgroupS sCW_G pG) _.
  apply: subcent1_extraspecial_maximal sCW_G _.
  rewrite inE andbC (subsetP sUG) //= -sub_cent1.
  by apply/subsetPn; exists x; rewrite // inE Gx -sub_cent1 subsetIr.
apply/eqP; rewrite -(eqn_pmul2r p_gt0) -{1}iCW_CU Lagrange ?setIS ?centS //.
rewrite IHm ?(leq_trans (proper_card ltWU)) // -setIA -mulnA.
rewrite -(Lagrange_index sUG sWU) (p_maximal_index (pgroupS sUG pG)) //=.
by rewrite -cent_set1 (setIidPr (centS _)) ?sub1set.
Qed.

(* This is the tranposition of the proof that a singular vector is contained  *)
(* in a hyperbolic plane (Aschbacher (19.12)) to subgroups of an extraspecial *)
(* group.                                                                     *)
Lemma split1_extraspecial x :
    x \in G :\: 'Z(G) ->
  {E : {group gT} & {R : {group gT} |
    [/\ #|E| = (p ^ 3)%N /\ #|R| = #|G| %/ p ^ 2,
        E \* R = G /\ E :&: R = 'Z(E),
        'Z(E) = 'Z(G) /\ 'Z(R) = 'Z(G),
        extraspecial E /\ x \in E
      & if abelian R then R :=: 'Z(G) else extraspecial R]}}.
Proof.
case/setDP=> Gx notZx; rewrite inE Gx /= in notZx.
have [[defPhiG defG'] prZ] := esG.
have maxCx: maximal 'C_G[x] G.
  by rewrite subcent1_extraspecial_maximal // inE notZx.
pose y := repr (G :\: 'C[x]).
have [Gy not_cxy]: y \in G /\ y \notin 'C[x].
  move/maxgroupp: maxCx => /properP[_ [t Gt not_cyt]].
  by apply/setDP; apply: (mem_repr t); rewrite !inE Gt andbT in not_cyt *.
pose E := <[x]> <*> <[y]>; pose R := 'C_G(E).
exists [group of E]; exists [group of R] => /=.
have sEG: E \subset G by rewrite join_subG !cycle_subG Gx.
have [Ex Ey]: x \in E /\ y \in E by rewrite !mem_gen // inE cycle_id ?orbT.
have sZE: 'Z(G) \subset E.
  rewrite (('Z(G) =P E^`(1)) _) ?der_sub // eqEsubset -{2}defG' dergS // andbT.
  apply: contraR not_cxy => /= not_sZE'.
  rewrite (sameP cent1P commgP) -in_set1 -[[set 1]](prime_TIg prZ not_sZE').
  by rewrite /= -defG' inE !mem_commg.
have ziER: E :&: R = 'Z(E) by rewrite setIA (setIidPl sEG).
have cER: R \subset 'C(E) by rewrite subsetIr.
have iCxG: #|G : 'C_G[x]| = p by apply: p_maximal_index.
have maxR: maximal R 'C_G[x].
  rewrite /R centY !cent_cycle setIA.
  rewrite subcent1_extraspecial_maximal ?subsetIl // inE Gy andbT -sub_cent1.
  by apply/subsetPn; exists x; rewrite 1?cent1C // inE Gx cent1id.
have sRCx: R \subset 'C_G[x] by rewrite -cent_cycle setIS ?centS ?joing_subl.
have sCxG: 'C_G[x] \subset G by rewrite subsetIl.
have sRG: R \subset G by rewrite subsetIl.
have iRCx: #|'C_G[x] : R| = p by rewrite (p_maximal_index (pgroupS sCxG pG)).
have defG: E * R = G.
  rewrite -cent_joinEr //= -/R joingC joingA.
  have cGx_x: <[x]> \subset 'C_G[x] by rewrite cycle_subG inE Gx cent1id.
  have nsRcx := p_maximal_normal (pgroupS sCxG pG) maxR.
  rewrite (norm_joinEr (subset_trans cGx_x (normal_norm nsRcx))).
  rewrite (mulg_normal_maximal nsRcx) //=; last first.
    by rewrite centY !cent_cycle cycle_subG !in_setI Gx cent1id cent1C.
  have nsCxG := p_maximal_normal pG maxCx.
  have syG: <[y]> \subset G by rewrite cycle_subG.
  rewrite (norm_joinEr (subset_trans syG (normal_norm nsCxG))).
  by rewrite (mulg_normal_maximal nsCxG) //= cycle_subG inE Gy.
have defZR: 'Z(R) = 'Z(G) by rewrite -['Z(R)]setIA -centM defG.
have defZE: 'Z(E) = 'Z(G).
  by rewrite -defG -center_prod ?mulGSid //= -ziER subsetI center_sub defZR sZE.
have [n oG] := p_natP pG.
have n_gt1: n > 1.
   by rewrite ltnW // -(@leq_exp2l p) // -oG min_card_extraspecial.
have oR: #|R| = (p ^ n.-2)%N.
  apply/eqP; rewrite -(divg_indexS sRCx) iRCx /= -(divg_indexS sCxG) iCxG /= oG.
  by rewrite -{1}(subnKC n_gt1) subn2 !expnS !mulKn.
have oE: #|E| = (p ^ 3)%N.
  apply/eqP; rewrite -(@eqn_pmul2r #|R|) ?cardG_gt0 // mul_cardG defG ziER.
  by rewrite defZE oZ oG -{1}(subnKC n_gt1) oR -expnSr -expnD subn2.
rewrite cprodE // oR oG -expnB ?subn2 //; split=> //.
  by split=> //; apply: card_p3group_extraspecial _ oE _; rewrite // defZE.
case: ifP => [cRR | not_cRR]; first by rewrite -defZR (center_idP _).
split; rewrite /special defZR //.
have ntR': R^`(1) != 1 by rewrite (sameP eqP commG1P) -abelianE not_cRR.
have pR: p.-group R := pgroupS sRG pG.
have pR': p.-group R^`(1) := pgroupS (der_sub 1 _) pR.
have defR': R^`(1) = 'Z(G).
  apply/eqP; rewrite eqEcard -{1}defG' dergS //= oZ.
  by have [_ _ [k ->]]:= pgroup_pdiv pR' ntR'; rewrite (leq_exp2l 1).
split=> //; apply/eqP; rewrite eqEsubset -{1}defPhiG -defR' (PhiS pG) //=.
by rewrite (Phi_joing pR) joing_subl.
Qed.

(* This is the tranposition of the proof that the dimension of any maximal    *)
(* totally singular subspace is equal to the Witt index (Aschbacher (20.8)),  *)
(* to subgroups of an extraspecial group (in a slightly more general form,    *)
(* since we allow for p != 2).                                                *)
(*   Note that Aschbacher derives this from the Witt lemma, which we avoid.   *)
Lemma pmaxElem_extraspecial : 'E*_p(G) = 'E_p^('r_p(G))(G).
Proof.
have sZmax: {in 'E*_p(G), forall E, 'Z(G) \subset E}.
  move=> E maxE; have defE := pmaxElem_LdivP p_pr maxE.
  have abelZ: p.-abelem 'Z(G) by rewrite prime_abelem ?oZ.
  rewrite -(Ohm1_id abelZ) (OhmE 1 (abelem_pgroup abelZ)) gen_subG -defE.
  by rewrite setSI // setIS ?centS // -defE !subIset ?subxx.
suffices card_max: {in 'E*_p(G) &, forall E F, #|E| <= #|F| }.
  have EprGmax: 'E_p^('r_p(G))(G) \subset 'E*_p(G) := p_rankElem_max p G.
  have [E EprE]:= p_rank_witness p G; have maxE := subsetP EprGmax E EprE.
  apply/eqP; rewrite eqEsubset EprGmax andbT; apply/subsetP=> F maxF.
  rewrite inE; have [-> _]:= pmaxElemP maxF; have [_ _ <-]:= pnElemP EprE.
  by apply/eqP; congr (logn p _); apply/eqP; rewrite eqn_leq !card_max.
move=> E F maxE maxF; set U := E :&: F.
have [sUE sUF]: U \subset E /\ U \subset F by apply/andP; rewrite -subsetI.
have sZU: 'Z(G) \subset U by rewrite subsetI !sZmax.
have [EpE _]:= pmaxElemP maxE; have{EpE} [sEG abelE] := pElemP EpE.
have [EpF _]:= pmaxElemP maxF; have{EpF} [sFG abelF] := pElemP EpF.
have [V] := abelem_split_dprod abelE sUE; case/dprodP=> _ defE cUV tiUV.
have [W] := abelem_split_dprod abelF sUF; case/dprodP=> _ defF _ tiUW.
have [sVE sWF]: V \subset E /\ W \subset F by rewrite -defE -defF !mulG_subr.
have [sVG sWG] := (subset_trans sVE sEG, subset_trans sWF sFG).
rewrite -defE -defF !TI_cardMg // leq_pmul2l ?cardG_gt0 //.
rewrite -(leq_pmul2r (cardG_gt0 'C_G(W))) mul_cardG.
rewrite card_subcent_extraspecial // mulnCA Lagrange // mulnC.
rewrite leq_mul ?subset_leq_card //; last by rewrite mul_subG ?subsetIl.
apply: subset_trans (sub1G _); rewrite -tiUV !subsetI subsetIl subIset ?sVE //=.
rewrite -(pmaxElem_LdivP p_pr maxF) -defF centM -!setIA -(setICA 'C(W)).
rewrite setIC setIA setIS // subsetI cUV sub_LdivT.
by case/and3P: (abelemS sVE abelE).
Qed.

End ExtraspecialFormspace.

(* This is B & G, Theorem 4.15, as done in Aschbacher (23.8) *)
Lemma critical_extraspecial R S :
    p.-group R -> S \subset R -> extraspecial S -> [~: S, R] \subset S^`(1) ->
  S \* 'C_R(S) = R.
Proof.
move=> pR sSR esS sSR_S'; have [[defPhi defS'] _] := esS.
have [pS [sPS nPS]] := (pgroupS sSR pR, andP (Phi_normal S : 'Phi(S) <| S)).
have{esS} oZS: #|'Z(S)| = p := card_center_extraspecial pS esS.
have nSR: R \subset 'N(S) by rewrite -commg_subl (subset_trans sSR_S') ?der_sub.
have nsCR: 'C_R(S) <| R by rewrite (normalGI nSR) ?cent_normal.
have nCS: S \subset 'N('C_R(S)) by rewrite cents_norm // centsC subsetIr.
rewrite cprodE ?subsetIr //= -{2}(quotientGK nsCR) normC -?quotientK //.
congr (_ @*^-1 _); apply/eqP; rewrite eqEcard quotientS //=.
rewrite -(card_isog (second_isog nCS)) setIAC (setIidPr sSR) /= -/'Z(S) -defPhi.
rewrite -ker_conj_aut (card_isog (first_isog_loc _ nSR)) //=; set A := _ @* R.
have{pS} abelSb := Phi_quotient_abelem pS; have [pSb cSSb _] := and3P abelSb.
have [/= Xb defSb oXb] := grank_witness (S / 'Phi(S)).
pose X := (repr \o val : coset_of _ -> gT) @: Xb.
have sXS: X \subset S; last have nPX := subset_trans sXS nPS.
  apply/subsetP=> x; case/imsetP=> xb Xxb ->; have nPx := repr_coset_norm xb.
  rewrite -sub1set -(quotientSGK _ sPS) ?sub1set ?quotient_set1 //= sub1set.
  by rewrite coset_reprK -defSb mem_gen.
have defS: <<X>> = S.
  apply: Phi_nongen; apply/eqP; rewrite eqEsubset join_subG sPS sXS -joing_idr.
  rewrite -genM_join sub_gen // -quotientSK ?quotient_gen // -defSb genS //.
  apply/subsetP=> xb Xxb; apply/imsetP; rewrite (setIidPr nPX).
  by exists (repr xb); rewrite /= ?coset_reprK //; apply: imset_f.
pose f (a : {perm gT}) := [ffun x => if x \in X then x^-1 * a x else 1].
have injf: {in A &, injective f}.
  move=> _ _ /morphimP[y nSy Ry ->] /morphimP[z nSz Rz ->].
  move/ffunP=> eq_fyz; apply: (@eq_Aut _ S); rewrite ?Aut_aut //= => x Sx.
  rewrite !norm_conj_autE //; apply: canRL (conjgKV z) _; rewrite -conjgM.
  rewrite /conjg -(centP _ x Sx) ?mulKg {x Sx}// -defS cent_gen -sub_cent1.
  apply/subsetP=> x Xx; have Sx := subsetP sXS x Xx.
  move/(_ x): eq_fyz; rewrite !ffunE Xx !norm_conj_autE // => /mulgI xy_xz.
  by rewrite cent1C inE conjg_set1 conjgM xy_xz conjgK.
have sfA_XS': f @: A \subset pffun_on 1 X S^`(1).
  apply/subsetP=> _ /imsetP[_ /morphimP[y nSy Ry ->] ->].
  apply/pffun_onP; split=> [|_ /imageP[x /= Xx ->]].
    by apply/subsetP=> x; apply: contraNT => /[!ffunE]/negPf->.
  have Sx := subsetP sXS x Xx.
  by rewrite ffunE Xx norm_conj_autE // (subsetP sSR_S') ?mem_commg.
rewrite -(card_in_imset injf) (leq_trans (subset_leq_card sfA_XS')) // defS'.
rewrite card_pffun_on (card_pgroup pSb) -rank_abelem -?grank_abelian // -oXb.
by rewrite -oZS ?leq_pexp2l ?cardG_gt0 ?leq_imset_card.
Qed.

(* This is part of Aschbacher (23.13) and (23.14). *)
Theorem extraspecial_structure S : p.-group S -> extraspecial S ->
  {Es | all (fun E => (#|E| == p ^ 3)%N && ('Z(E) == 'Z(S))) Es
      & \big[cprod/1%g]_(E <- Es) E \* 'Z(S) = S}.
Proof.
have [m] := ubnP #|S|; elim: m S => // m IHm S leSm pS esS.
have [x Z'x]: {x | x \in S :\: 'Z(S)}.
  apply/sigW/set0Pn; rewrite -subset0 subDset setU0.
  apply: contra (extraspecial_nonabelian esS) => sSZ.
  exact: abelianS sSZ (center_abelian S).
have [E [R [[oE oR]]]]:= split1_extraspecial pS esS Z'x.
case=> defS _ [defZE defZR] _; case: ifP => [_ defR | _ esR].
  by exists [:: E]; rewrite /= ?oE ?defZE ?eqxx // big_seq1 -defR.
have sRS: R \subset S by case/cprodP: defS => _ <- _; rewrite mulG_subr.
have [|Es esEs defR] := IHm _ _ (pgroupS sRS pS) esR.
  rewrite oR (leq_trans (ltn_Pdiv _ _)) ?cardG_gt0 // (ltn_exp2l 0) //.
  exact: prime_gt1 (extraspecial_prime pS esS).
exists (E :: Es); first by rewrite /= oE defZE !eqxx -defZR.
by rewrite -defZR big_cons -cprodA defR.
Qed.

Section StructureCorollaries.

Variable S : {group gT}.
Hypotheses (pS : p.-group S) (esS : extraspecial S).

Let p_pr := extraspecial_prime pS esS.
Let oZ := card_center_extraspecial pS esS.

(* This is Aschbacher (23.10)(2). *)
Lemma card_extraspecial : {n | n > 0 & #|S| = (p ^ n.*2.+1)%N}.
Proof.
set T := S; exists (logn p #|T|)./2.
  rewrite half_gt0 ltnW // -(leq_exp2l _ _ (prime_gt1 p_pr)) -card_pgroup //.
  exact: min_card_extraspecial.
have [Es] := extraspecial_structure pS esS; rewrite -[in RHS]/T.
elim: Es T => [_ _ <-| E s IHs T] /=.
  by rewrite big_nil cprod1g oZ (pfactorK 1).
rewrite -andbA big_cons -cprodA => /and3P[/eqP oEp3 /eqP defZE].
move=> /IHs{}IHs /cprodP[[_ U _ defU]]; rewrite defU => defT cEU.
rewrite -(mulnK #|T| (cardG_gt0 (E :&: U))) -defT -mul_cardG /=.
have ->: E :&: U = 'Z(S).
  apply/eqP; rewrite eqEsubset subsetI -{1 2}defZE subsetIl setIS //=.
  by case/cprodP: defU => [[V _ -> _]]  <- _; apply: mulG_subr.
rewrite (IHs U) // oEp3 oZ -expnD addSn expnS mulKn ?prime_gt0 //.
by rewrite pfactorK //= uphalf_double.
Qed.

Lemma Aut_extraspecial_full : Aut_in (Aut S) 'Z(S) \isog Aut 'Z(S).
Proof.
have [p_gt1 p_gt0] := (prime_gt1 p_pr, prime_gt0 p_pr).
have [Es] := extraspecial_structure pS esS.
elim: Es S oZ => [T _ _ <-| E s IHs T oZT] /=.
  rewrite big_nil cprod1g (center_idP (center_abelian T)).
  by apply/Aut_sub_fullP=> // g injg gZ; exists g.
rewrite -andbA big_cons -cprodA => /and3P[/eqP-oE /eqP-defZE es_s].
case/cprodP=> -[_ U _ defU]; rewrite defU => defT cEU.
have sUT: U \subset T by rewrite -defT mulG_subr.
have sZU: 'Z(T) \subset U.
  by case/cprodP: defU => [[V _ -> _] <- _]; apply: mulG_subr.
have defZU: 'Z(E) = 'Z(U).
  apply/eqP; rewrite eqEsubset defZE subsetI sZU subIset ?centS ?orbT //=.
  by rewrite subsetI subIset ?sUT //= -defT centM setSI.
apply: (Aut_cprod_full _ defZU); rewrite ?cprodE //; last first.
  by apply: IHs; rewrite -?defZU ?defZE.
have oZE: #|'Z(E)| = p by rewrite defZE.
have [p2 | odd_p] := even_prime p_pr.
  suffices <-: restr_perm 'Z(E) @* Aut E = Aut 'Z(E) by apply: Aut_in_isog.
  apply/eqP; rewrite eqEcard restr_perm_Aut ?center_sub //=.
  by rewrite card_Aut_cyclic ?prime_cyclic ?oZE // {1}p2 cardG_gt0.
have pE: p.-group E by rewrite /pgroup oE pnatX pnat_id.
have nZE: E \subset 'N('Z(E)) by rewrite normal_norm ?center_normal.
have esE: extraspecial E := card_p3group_extraspecial p_pr oE oZE.
have [[defPhiE defE'] prZ] := esE.
have{defPhiE} sEpZ x: x \in E -> (x ^+ p)%g \in 'Z(E).
  move=> Ex; rewrite -defPhiE (Phi_joing pE) mem_gen // inE orbC.
  by rewrite (Mho_p_elt 1) // (mem_p_elt pE).
have ltZE: 'Z(E) \proper E by rewrite properEcard subsetIl oZE oE (ltn_exp2l 1).
have [x [Ex notZx oxp]]: exists x, [/\ x \in E, x \notin 'Z(E) & #[x] %| p]%N.
  have [_ [x Ex notZx]] := properP ltZE.
  case: (prime_subgroupVti <[x ^+ p]> prZ) => [sZxp | ]; last first.
    move/eqP; rewrite (setIidPl _) ?cycle_subG ?sEpZ //.
    by rewrite cycle_eq1 -order_dvdn; exists x.
  have [y Ey notxy]: exists2 y, y \in E & y \notin <[x]>.
    apply/subsetPn; apply: contra (extraspecial_nonabelian esE) => sEx.
    by rewrite (abelianS sEx) ?cycle_abelian.
  have: (y ^+ p)%g \in <[x ^+ p]> by rewrite (subsetP sZxp) ?sEpZ.
  case/cycleP=> i def_yp; set xi := (x ^- i)%g.
  have Exi: xi \in E by rewrite groupV groupX.
  exists (y * xi)%g; split; first by rewrite groupM.
    have sxpx: <[x ^+ p]> \subset <[x]> by rewrite cycle_subG mem_cycle.
    apply: contra notxy; move/(subsetP (subset_trans sZxp sxpx)).
    by rewrite groupMr // groupV mem_cycle.
  pose z := [~ xi, y]; have Zz: z \in 'Z(E) by rewrite -defE' mem_commg.
  case: (setIP Zz) => _; move/centP=> cEz.
  rewrite order_dvdn expMg_Rmul; try by apply: commute_sym; apply: cEz.
  rewrite def_yp expgVn -!expgM mulnC mulgV mul1g -order_dvdn.
  by rewrite (dvdn_trans (order_dvdG Zz)) //= oZE bin2odd // dvdn_mulr.
have{oxp} ox: #[x] = p.
  apply/eqP; case/primeP: p_pr => _ dvd_p; case/orP: (dvd_p _ oxp) => //.
  by rewrite order_eq1; case: eqP notZx => // ->; rewrite group1.
have [y Ey not_cxy]: exists2 y, y \in E & y \notin 'C[x].
  by apply/subsetPn; rewrite sub_cent1; rewrite inE Ex in notZx.
have notZy: y \notin 'Z(E).
  apply: contra not_cxy; rewrite inE Ey; apply: subsetP.
  by rewrite -cent_set1 centS ?sub1set.
pose K := 'C_E[y]; have maxK: maximal K E by apply: cent1_extraspecial_maximal.
have nsKE: K <| E := p_maximal_normal pE maxK; have [sKE nKE] := andP nsKE.
have oK: #|K| = (p ^ 2)%N.
  by rewrite -(divg_indexS sKE) oE (p_maximal_index pE) ?mulKn.
have cKK: abelian K := card_p2group_abelian p_pr oK.
have sZK: 'Z(E) \subset K by rewrite setIS // -cent_set1 centS ?sub1set.
have defE: K ><| <[x]> = E.
  have notKx: x \notin K by rewrite inE Ex cent1C.
  rewrite sdprodE ?(mulg_normal_maximal nsKE) ?cycle_subG ?(subsetP nKE) //.
  by rewrite setIC prime_TIg -?orderE ?ox ?cycle_subG.
have /cyclicP[z defZ]: cyclic 'Z(E) by rewrite prime_cyclic ?oZE.
apply/(Aut_sub_fullP (center_sub E)); rewrite /= defZ => g injg gZ.
pose k := invm (injm_Zp_unitm z) (aut injg gZ).
have fM: {in K &, {morph expgn^~ (val k): u v / u * v}}.
  by move=> u v Ku Kv; rewrite /= expgMn // /commute (centsP cKK).
pose f := Morphism fM; have fK: f @* K = K.
  apply/setP=> u; rewrite morphimEdom.
  apply/imsetP/idP=> [[v Kv ->] | Ku]; first exact: groupX.
  exists (u ^+ expg_invn K (val k)); first exact: groupX.
  rewrite /f /= expgAC expgK // oK coprimeXl // -unitZpE //.
  by case: (k) => /=; rewrite orderE -defZ oZE => j; rewrite natr_Zp.
have fMact: {in K & <[x]>, morph_act 'J 'J f (idm <[x]>)}.
  by move=> u v _ _; rewrite /= conjXg.
exists (sdprodm_morphism defE fMact).
rewrite im_sdprodm injm_sdprodm injm_idm -card_im_injm im_idm fK.
have [_ -> _ ->] := sdprodP defE; rewrite !eqxx; split=> //= u Zu.
rewrite sdprodmEl ?(subsetP sZK) ?defZ // -(autE injg gZ Zu).
rewrite -[aut _ _](invmK (injm_Zp_unitm z)); first by rewrite permE Zu.
by rewrite im_Zp_unitm Aut_aut.
Qed.

(* These are the parts of Aschbacher (23.12) and exercise 8.5 that are later  *)
(* used in Aschbacher (34.9), which itself replaces the informal discussion   *)
(* quoted from Gorenstein in the proof of B & G, Theorem 2.5.                 *)
Lemma center_aut_extraspecial k : coprime k p ->
  exists2 f, f \in Aut S & forall z, z \in 'Z(S) -> f z = (z ^+ k)%g.
Proof.
have /cyclicP[z defZ]: cyclic 'Z(S) by rewrite prime_cyclic ?oZ.
have oz: #[z] = p by rewrite orderE -defZ.
rewrite coprime_sym -unitZpE ?prime_gt1 // -oz => u_k.
pose g := Zp_unitm (FinRing.unit 'Z_#[z] u_k).
have AutZg: g \in Aut 'Z(S) by rewrite defZ -im_Zp_unitm mem_morphim ?inE.
have ZSfull := Aut_sub_fullP (center_sub S) Aut_extraspecial_full.
have [f [injf fS fZ]] := ZSfull _ (injm_autm AutZg) (im_autm AutZg).
exists (aut injf fS) => [|u Zu]; first exact: Aut_aut.
have [Su _] := setIP Zu; have z_u: u \in <[z]> by rewrite -defZ.
by rewrite autE // fZ //= autmE permE /= z_u /cyclem expg_znat.
Qed.

End StructureCorollaries.

End Extraspecial.

Section SCN.

Variables (gT : finGroupType) (p : nat) (G : {group gT}).
Implicit Types A Z H : {group gT}.

Lemma SCN_P A : reflect (A <| G /\ 'C_G(A) = A) (A \in 'SCN(G)).
Proof. by apply: (iffP setIdP) => [] [->]; move/eqP. Qed.

Lemma SCN_abelian A : A \in 'SCN(G) -> abelian A.
Proof. by case/SCN_P=> _ defA; rewrite /abelian -{1}defA subsetIr. Qed.

Lemma exponent_Ohm1_class2 H :
  odd p -> p.-group H -> nil_class H <= 2 -> exponent 'Ohm_1(H) %| p.
Proof.
move=> odd_p pH; rewrite nil_class2 => sH'Z; apply/exponentP=> x /=.
rewrite (OhmE 1 pH) expn1 gen_set_id => {x} [/LdivP[] //|].
apply/group_setP; split=> [|x y]; first by rewrite !inE group1 expg1n //=.
case/LdivP=> Hx xp1 /LdivP[Hy yp1]; rewrite !inE groupM //=.
have [_ czH]: [~ y, x] \in H /\ centralises [~ y, x] H.
  by apply/centerP; rewrite (subsetP sH'Z) ?mem_commg.
rewrite expMg_Rmul ?xp1 ?yp1 /commute ?czH //= !mul1g.
by rewrite bin2odd // -commXXg ?yp1 /commute ?czH // comm1g.
Qed.

(* SCN_max and max_SCN cover Aschbacher 23.15(1) *)
Lemma SCN_max A : A \in 'SCN(G) -> [max A | A <| G & abelian A].
Proof.
case/SCN_P => nAG scA; apply/maxgroupP; split=> [|H].
  by rewrite nAG /abelian -{1}scA subsetIr.
do 2![case/andP]=> sHG _ abelH sAH; apply/eqP.
by rewrite eqEsubset sAH -scA subsetI sHG centsC (subset_trans sAH).
Qed.

Lemma max_SCN A :
  p.-group G -> [max A | A <| G & abelian A] -> A \in 'SCN(G).
Proof.
move/pgroup_nil=> nilG; rewrite /abelian.
case/maxgroupP=> /andP[nsAG abelA] maxA; have [sAG nAG] := andP nsAG.
rewrite inE nsAG eqEsubset /= andbC subsetI abelA normal_sub //=.
rewrite -quotient_sub1; last by rewrite subIset 1?normal_norm.
apply/trivgP; apply: (TI_center_nil (quotient_nil A nilG)).
  by rewrite quotient_normal // /normal subsetIl normsI ?normG ?norms_cent.
apply/trivgP/subsetP=> _ /setIP[/morphimP[x Nx /setIP[_ Cx]] ->].
rewrite -cycle_subG in Cx => /setIP[GAx CAx].
have{CAx GAx}: <[coset A x]> <| G / A.
  by rewrite /normal cycle_subG GAx cents_norm // centsC cycle_subG.
case/(inv_quotientN nsAG)=> B /= defB sAB nBG.
rewrite -cycle_subG defB (maxA B) ?trivg_quotient // nBG.
have{} defB : B :=: A * <[x]>.
  rewrite -quotientK ?cycle_subG ?quotient_cycle // defB quotientGK //.
  exact: normalS (normal_sub nBG) nsAG.
apply/setIidPl; rewrite ?defB -[_ :&: _]center_prod //=.
rewrite /center !(setIidPl _) //; apply: cycle_abelian.
Qed.

(* The two other assertions of Aschbacher 23.15 state properties of the       *)
(* normal series 1 <| Z = 'Ohm_1(A) <| A with A \in 'SCN(G).                  *)

Section SCNseries.

Variables A : {group gT}.
Hypothesis SCN_A : A \in 'SCN(G).

Let Z := 'Ohm_1(A).
Let cAA := SCN_abelian SCN_A.
Let sZA: Z \subset A := Ohm_sub 1 A.
Let nZA : A \subset 'N(Z) := sub_abelian_norm cAA sZA.

(* This is Aschbacher 23.15(2). *)
Lemma der1_stab_Ohm1_SCN_series : ('C(Z) :&: 'C_G(A / Z | 'Q))^`(1) \subset A.
Proof.
case/SCN_P: SCN_A => /andP[sAG nAG] {4} <-.
rewrite subsetI {1}setICA comm_subG ?subsetIl //= gen_subG.
apply/subsetP=> w /imset2P[u v].
rewrite -groupV -(groupV _ v) /= astabQR //= -/Z !inE groupV.
case/and4P=> cZu _ _ sRuZ /and4P[cZv' _ _ sRvZ] ->{w}.
apply/centP=> a Aa; rewrite /commute -!mulgA (commgCV v) (mulgA u).
rewrite (centP cZu); last by rewrite (subsetP sRvZ) ?mem_commg ?set11 ?groupV.
rewrite 2!(mulgA v^-1) mulKVg 4!mulgA invgK (commgC u^-1) mulgA.
rewrite -(mulgA _ _ v^-1) -(centP cZv') ?(subsetP sRuZ) ?mem_commg ?set11//.
by rewrite -!mulgA invgK mulKVg !mulKg.
Qed.

(* This is Aschbacher 23.15(3); note that this proof does not depend on the   *)
(* maximality of A.                                                           *)
Lemma Ohm1_stab_Ohm1_SCN_series :
  odd p -> p.-group G -> 'Ohm_1('C_G(Z)) \subset 'C_G(A / Z | 'Q).
Proof.
have [-> | ntG] := eqsVneq G 1; first by rewrite !(setIidPl (sub1G _)) Ohm1.
move=> p_odd pG; have{ntG} [p_pr _ _] := pgroup_pdiv pG ntG.
case/SCN_P: SCN_A => /andP[sAG nAG] _; have pA := pgroupS sAG pG.
have pCGZ : p.-group 'C_G(Z) by rewrite (pgroupS _ pG) // subsetIl.
rewrite {pCGZ}(OhmE 1 pCGZ) gen_subG; apply/subsetP=> x; rewrite 3!inE -andbA.
rewrite -!cycle_subG => /and3P[sXG cZX xp1] /=; have cXX := cycle_abelian x.
have nZX := cents_norm cZX; have{nAG} nAX := subset_trans sXG nAG.
pose XA := <[x]> <*> A; pose C := 'C(<[x]> / Z | 'Q); pose CA := A :&: C.
pose Y := <[x]> <*> CA; pose W := 'Ohm_1(Y).
have sXC: <[x]> \subset C by rewrite sub_astabQ nZX (quotient_cents _ cXX).
have defY : Y = <[x]> * CA by rewrite -norm_joinEl // normsI ?nAX ?normsG.
have{nAX} defXA: XA = <[x]> * A := norm_joinEl nAX.
suffices{sXC}: XA \subset Y.
  rewrite subsetI sXG /= sub_astabQ nZX centsC defY group_modl //= -/Z -/C.
  by rewrite subsetI sub_astabQ defXA quotientMl //= !mulG_subG; case/and4P.
have sZCA: Z \subset CA by rewrite subsetI sZA [C]astabQ sub_cosetpre.
have cZCA: CA \subset 'C(Z) by rewrite subIset 1?(sub_abelian_cent2 cAA).
have sZY: Z \subset Y by rewrite (subset_trans sZCA) ?joing_subr.
have{cZCA cZX} cZY: Y \subset 'C(Z) by rewrite join_subG cZX.
have{cXX nZX} sY'Z : Y^`(1) \subset Z.
  rewrite der1_min ?cents_norm //= -/Y defY quotientMl // abelianM /= -/Z -/CA.
  rewrite !quotient_abelian // ?(abelianS _ cAA) ?subsetIl //=.
  by rewrite /= quotientGI ?Ohm_sub // quotient_astabQ subsetIr.
have{sY'Z cZY} nil_classY: nil_class Y <= 2.
  by rewrite nil_class2 (subset_trans sY'Z ) // subsetI sZY centsC.
have pY: p.-group Y by rewrite (pgroupS _ pG) // join_subG sXG subIset ?sAG.
have sXW: <[x]> \subset W.
  by rewrite [W](OhmE 1 pY) ?genS // sub1set !inE -cycle_subG joing_subl.
have{nil_classY pY sXW sZY sZCA} defW: W = <[x]> * Z.
  rewrite -[W](setIidPr (Ohm_sub _ _)) /= -/Y {1}defY -group_modl //= -/Y -/W.
  congr (_ * _); apply/eqP; rewrite eqEsubset {1}[Z](OhmE 1 pA).
  rewrite subsetI setIAC subIset //; first by rewrite sZCA -[Z]Ohm_id OhmS.
  rewrite sub_gen ?setIS //; apply/subsetP=> w Ww; rewrite inE.
  by apply/eqP; apply: exponentP w Ww; apply: exponent_Ohm1_class2.
have{sXG sAG} sXAG: XA \subset G by rewrite join_subG sXG.
have{sXAG} nilXA: nilpotent XA := nilpotentS sXAG (pgroup_nil pG).
have sYXA: Y \subset XA by rewrite defY defXA mulgS ?subsetIl.
rewrite -[Y](nilpotent_sub_norm nilXA) {nilXA sYXA}//= -/Y -/XA.
suffices: 'N_XA('Ohm_1(Y)) \subset Y by apply/subset_trans/setIS/gFnorms.
rewrite {XA}defXA -group_modl ?normsG /= -/W ?{W}defW ?mulG_subl //.
rewrite {Y}defY mulgS // subsetI subsetIl {CA C}sub_astabQ subIset ?nZA //= -/Z.
rewrite (subset_trans (quotient_subnorm _ _ _)) //= quotientMidr /= -/Z.
rewrite -quotient_sub1 ?subIset ?cent_norm ?orbT //.
rewrite (subset_trans (quotientI _ _ _)) ?coprime_TIg //.
rewrite (@pnat_coprime p) // -/(p.-group _) ?quotient_pgroup {pA}//= -pgroupE.
rewrite -(setIidPr (cent_sub _)) p'group_quotient_cent_prime //.
by rewrite (dvdn_trans (dvdn_quotient _ _)) ?order_dvdn.
Qed.

End SCNseries.

(* This is Aschbacher 23.16. *)
Lemma Ohm1_cent_max_normal_abelem Z :
  odd p -> p.-group G -> [max Z | Z <| G & p.-abelem Z] -> 'Ohm_1('C_G(Z)) = Z.
Proof.
move=> p_odd pG; set X := 'Ohm_1('C_G(Z)).
case/maxgroupP=> /andP[nsZG abelZ] maxZ.
have [sZG nZG] := andP nsZG; have [_ cZZ expZp] := and3P abelZ.
have{nZG} nsXG: X <| G by rewrite gFnormal_trans ?norm_normalI ?norms_cent.
have cZX : X \subset 'C(Z) by apply/gFsub_trans/subsetIr.
have{sZG expZp} sZX: Z \subset X.
  rewrite [X](OhmE 1 (pgroupS _ pG)) ?subsetIl ?sub_gen //.
  apply/subsetP=> x Zx; rewrite !inE  ?(subsetP sZG) ?(subsetP cZZ) //=.
  by rewrite (exponentP expZp).
suffices{sZX} expXp: (exponent X %| p).
  apply/eqP; rewrite eqEsubset sZX andbT -quotient_sub1 ?cents_norm //= -/X.
  have pGq: p.-group (G / Z) by rewrite quotient_pgroup.
  rewrite (TI_center_nil (pgroup_nil pGq)) ?quotient_normal //= -/X setIC.
  apply/eqP/trivgPn=> [[Zd]]; rewrite inE -!cycle_subG -cycle_eq1 -subG1 /= -/X.
  case/andP=> /sub_center_normal nsZdG.
  have{nsZdG} [D defD sZD nsDG] := inv_quotientN nsZG nsZdG; rewrite defD.
  have sDG := normal_sub nsDG; have nsZD := normalS sZD sDG nsZG.
  rewrite quotientSGK ?quotient_sub1 ?normal_norm //= -/X => sDX /negP[].
  rewrite (maxZ D) // nsDG andbA (pgroupS sDG) ?(dvdn_trans (exponentS sDX)) //.
  have sZZD: Z \subset 'Z(D) by rewrite subsetI sZD centsC (subset_trans sDX).
  by rewrite (cyclic_factor_abelian sZZD) //= -defD cycle_cyclic.
pose normal_abelian := [pred A : {group gT} | A <| G & abelian A].
have{nsZG cZZ} normal_abelian_Z : normal_abelian Z by apply/andP.
have{normal_abelian_Z} [A maxA sZA] := maxgroup_exists normal_abelian_Z.
have SCN_A : A \in 'SCN(G) by apply: max_SCN pG maxA.
move/maxgroupp: maxA => /andP[nsAG cAA] {normal_abelian}.
have pA := pgroupS (normal_sub nsAG) pG.
have{abelZ maxZ nsAG cAA sZA} defA1: 'Ohm_1(A) = Z.
  have: Z \subset 'Ohm_1(A) by rewrite -(Ohm1_id abelZ) OhmS.
  by apply: maxZ; rewrite Ohm1_abelem ?gFnormal_trans.
have{SCN_A} sX'A: X^`(1) \subset A.
  have sX_CWA1 : X \subset 'C('Ohm_1(A)) :&: 'C_G(A / 'Ohm_1(A) | 'Q).
    rewrite subsetI /X -defA1 (Ohm1_stab_Ohm1_SCN_series _ p_odd) //=.
    by rewrite gFsub_trans ?subsetIr.
  by apply: subset_trans (der1_stab_Ohm1_SCN_series SCN_A); rewrite commgSS.
pose genXp := [pred U : {group gT} | 'Ohm_1(U) == U & ~~ (exponent U %| p)].
apply/idPn=> expXp'; have genXp_X: genXp [group of X] by rewrite /= Ohm_id eqxx.
have{genXp_X expXp'} [U] := mingroup_exists genXp_X; case/mingroupP; case/andP.
move/eqP=> defU1 expUp' minU sUX; case/negP: expUp'.
have{nsXG} pU := pgroupS (subset_trans sUX (normal_sub nsXG)) pG.
case gsetU1: (group_set 'Ldiv_p(U)).
  by rewrite -defU1 (OhmE 1 pU) gen_set_id // -sub_LdivT subsetIr.
move: gsetU1; rewrite /group_set 2!inE group1 expg1n eqxx; case/subsetPn=> xy.
case/imset2P=> x y /[!inE] /andP[Ux xp1] /andP[Uy yp1] ->{xy}.
rewrite groupM //= => nt_xyp; pose XY := <[x]> <*> <[y]>.
have{yp1 nt_xyp} defXY: XY = U.
  have sXY_U: XY \subset U by rewrite join_subG !cycle_subG Ux Uy.
  rewrite [XY]minU //= eqEsubset Ohm_sub (OhmE 1 (pgroupS _ pU)) //.
  rewrite /= joing_idl joing_idr genS; last first.
    by rewrite subsetI subset_gen subUset !sub1set !inE xp1 yp1.
  apply: contra nt_xyp => /exponentP-> //.
  by rewrite groupMl mem_gen // (set21, set22).
have: <[x]> <|<| U by rewrite nilpotent_subnormal ?(pgroup_nil pU) ?cycle_subG.
case/subnormalEsupport=> [defU | /=].
  by apply: dvdn_trans (exponent_dvdn U) _; rewrite -defU order_dvdn.
set V := <<class_support <[x]> U>>; case/andP=> sVU ltVU.
have{genXp minU xp1 sVU ltVU} expVp: exponent V %| p.
  apply: contraR ltVU => expVp'; rewrite [V]minU //= expVp' eqEsubset Ohm_sub.
  rewrite (OhmE 1 (pgroupS sVU pU)) genS //= subsetI subset_gen class_supportEr.
  apply/bigcupsP=> z _; apply/subsetP=> v Vv.
  by rewrite inE -order_dvdn (dvdn_trans (order_dvdG Vv)) // cardJg order_dvdn.
have{A pA defA1 sX'A V expVp} Zxy: [~ x, y] \in Z.
  rewrite -defA1 (OhmE 1 pA) mem_gen // !inE (exponentP expVp).
    by rewrite (subsetP sX'A) //= mem_commg ?(subsetP sUX).
  by rewrite groupMl -1?[x^-1]conjg1 mem_gen // imset2_f // ?groupV cycle_id.
have{Zxy sUX cZX} cXYxy: [~ x, y] \in 'C(XY).
  by rewrite centsC in cZX; rewrite defXY (subsetP (centS sUX)) ?(subsetP cZX).
rewrite -defU1 exponent_Ohm1_class2 // nil_class2 -defXY der1_joing_cycles //.
by rewrite subsetI {1}defXY !cycle_subG groupR.
Qed.

Lemma critical_class2 H : critical H G -> nil_class H <= 2.
Proof.
case=> [chH _ sRZ _].
by rewrite nil_class2 (subset_trans _ sRZ) ?commSg // char_sub.
Qed.

(* This proof of the Thompson critical lemma is adapted from Aschbacher 23.6 *)
Lemma Thompson_critical : p.-group G -> {K : {group gT} | critical K G}.
Proof.
move=> pG; pose qcr A := (A \char G) && ('Phi(A) :|: [~: G, A] \subset 'Z(A)).
have [|K]:= @maxgroup_exists _ qcr 1 _.
  by rewrite /qcr char1 center1 commG1 subUset Phi_sub subxx.
case/maxgroupP; rewrite {}/qcr subUset => /and3P[chK sPhiZ sRZ] maxK _.
have sKG := char_sub chK; have nKG := char_normal chK.
exists K; split=> //; apply/eqP; rewrite eqEsubset andbC setSI //=.
have chZ: 'Z(K) \char G by [apply: subcent_char]; have nZG := char_norm chZ.
have chC: 'C_G(K) \char G by apply: subcent_char chK.
rewrite -quotient_sub1; last by rewrite subIset // char_norm.
apply/trivgP; apply: (TI_center_nil (quotient_nil _ (pgroup_nil pG))).
  by rewrite quotient_normal ?norm_normalI ?norms_cent ?normal_norm.
apply: TI_Ohm1; apply/trivgP; rewrite -trivg_quotient -sub_cosetpre_quo //.
rewrite morphpreI quotientGK /=; last first.
  by apply: normalS (char_normal chZ); rewrite ?subsetIl ?setSI.
set X := _ :&: _; pose gX := [group of X].
have sXG: X \subset G by rewrite subIset ?subsetIl.
have cXK: K \subset 'C(gX) by rewrite centsC 2?subIset // subxx orbT.
rewrite subsetI centsC cXK andbT -(mul1g K) -mulSG mul1g -(cent_joinEr cXK).
rewrite [_ <*> K]maxK ?joing_subr //= andbC (cent_joinEr cXK).
rewrite -center_prod // (subset_trans _ (mulG_subr _ _)).
  rewrite charM 1?charI ?(char_from_quotient (normal_cosetpre _)) //.
  by rewrite cosetpreK !gFchar_trans.
rewrite (@Phi_mulg p) ?(pgroupS _ pG) // subUset commGC commMG; last first.
  by rewrite normsR ?(normsG sKG) // cents_norm // centsC.
rewrite !mul_subG 1?commGC //.
  apply: subset_trans (commgS _ (subsetIr _ _)) _.
  rewrite -quotient_cents2 ?subsetIl // centsC // cosetpreK //.
  exact/gFsub_trans/subsetIr.
have nZX := subset_trans sXG nZG; have pX : p.-group gX by apply: pgroupS pG.
rewrite -quotient_sub1 ?gFsub_trans //=.
have pXZ: p.-group (gX / 'Z(K)) by apply: morphim_pgroup.
rewrite (quotient_Phi pX nZX) subG1 (trivg_Phi pXZ).
apply: (abelemS (quotientS _ (subsetIr _ _))); rewrite /= cosetpreK /=.
have pZ: p.-group 'Z(G / 'Z(K)).
  by rewrite (pgroupS (center_sub _)) ?morphim_pgroup.
by rewrite Ohm1_abelem ?center_abelian.
Qed.

Lemma critical_p_stab_Aut H :
  critical H G -> p.-group G -> p.-group 'C(H | [Aut G]).
Proof.
move=> [chH sPhiZ sRZ eqCZ] pG; have sHG := char_sub chH.
pose G' := (sdpair1 [Aut G] @* G)%G; pose H' := (sdpair1 [Aut G] @* H)%G.
apply/pgroupP=> q pr_q; case/Cauchy=> //= f cHF; move: (cHF); rewrite astab_ract.
case/setIP=> Af cHFP ofq; rewrite -cycle_subG in cHF; apply: (pgroupP pG) => //.
pose F' := (sdpair2 [Aut G] @* <[f]>)%G.
have trHF: [~: H', F'] = 1.
  apply/trivgP; rewrite gen_subG; apply/subsetP=> u; case/imset2P=> x' a'.
  case/morphimP=> x Gx Hx ->; case/morphimP=> a Aa Fa -> -> {u x' a'}.
  by rewrite inE commgEl -sdpair_act ?(astab_act (subsetP cHF _ Fa) Hx) ?mulVg.
have sGH_H: [~: G', H'] \subset H'.
  by rewrite -morphimR ?(char_sub chH) // morphimS // commg_subr char_norm.
have{trHF sGH_H} trFGH: [~: F', G', H'] = 1.
  apply: three_subgroup; last by rewrite trHF comm1G.
  by apply/trivgP; rewrite -trHF commSg.
apply/negP=> qG; case: (qG); rewrite -ofq.
suffices ->: f = 1 by rewrite order1 dvd1n.
apply/permP=> x; rewrite perm1; case Gx: (x \in G); last first.
  by apply: out_perm (negbT Gx); case/setIdP: Af.
have Gfx: f x \in G by rewrite -(im_autm Af) -{1}(autmE Af) mem_morphim.
pose y := x^-1 * f x; have Gy: y \in G by rewrite groupMl ?groupV.
have [inj1 inj2] := (injm_sdpair1 [Aut G], injm_sdpair2 [Aut G]).
have Hy: y \in H.
  rewrite (subsetP (center_sub H)) // -eqCZ -cycle_subG.
  rewrite -(injmSK inj1) ?cycle_subG // injm_subcent // subsetI.
  rewrite morphimS ?morphim_cycle ?cycle_subG //=.
  suffices: sdpair1 [Aut G] y \in [~: G', F'].
    by rewrite commGC; apply: subsetP; apply/commG1P.
  rewrite morphM ?groupV ?morphV //= sdpair_act // -commgEl.
  by rewrite mem_commg ?mem_morphim ?cycle_id.
have fy: f y = y := astabP cHFP _ Hy.
have: (f ^+ q) x = x * y ^+ q.
  elim: (q) => [|i IHi]; first by rewrite perm1 mulg1.
  rewrite expgSr permM {}IHi -(autmE Af) morphM ?morphX ?groupX //= autmE.
  by rewrite fy expgS mulgA mulKVg.
move/eqP; rewrite -{1}ofq expg_order perm1 eq_mulVg1 mulKg -order_dvdn.
case/primeP: pr_q => _ pr_q /pr_q; rewrite order_eq1 -eq_mulVg1.
by case: eqP => //= _ /eqP oyq; case: qG; rewrite -oyq order_dvdG.
Qed.

End SCN.

Arguments SCN_P {gT G A}.

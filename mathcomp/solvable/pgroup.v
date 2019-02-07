(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp
Require Import fintype bigop finset prime fingroup morphism.
From mathcomp
Require Import gfunctor automorphism quotient action gproduct cyclic.

(******************************************************************************)
(* Standard group notions and constructions based on the prime decomposition  *)
(* of the order of the group or its elements:                                 *)
(*        pi.-group G <=> G is a pi-group, i.e., pi.-nat #|G|.                *)
(*    -> Recall that here and in the sequel pi can be a single prime p.       *)
(*  pi.-subgroup(H) G <=> H is a pi-subgroup of G.                            *)
(*                     := (H \subset G) && pi.-group H.                       *)
(*    -> This is provided mostly as a shorhand, with few associated lemmas.   *)
(*       However, we do establish some results on maximal pi-subgroups.       *)
(*          pi.-elt x <=> x is a pi-element.                                  *)
(*                     := pi.-nat #[x] or pi.-group <[x]>.                    *)
(*             x.`_pi == the pi-constituent of x: the (unique) pi-element     *)
(*                       y \in <[x]> such that x * y^-1 is a pi'-element.     *)
(*      pi.-Hall(G) H <=> H is a Hall pi-subgroup of G.                       *)
(*                    := [&& H \subset G, pi.-group H & pi^'.-nat #|G : H|].  *)
(*    -> This is also eqivalent to H \subset G /\ #|H| = #|G|`_pi.            *)
(*      p.-Sylow(G) P <=> P is a Sylow p-subgroup of G.                       *)
(*    -> This is the display and preferred input notation for p.-Hall(G) P.   *)
(*          'Syl_p(G) == the set of the p-Sylow subgroups of G.               *)
(*                    := [set P : {group _} | p.-Sylow(G) P].                 *)
(*          p_group P <=> P is a p-group for some prime p.                    *)
(*           Hall G H <=> H is a Hall pi-subgroup of G for some pi.           *)
(*                    := coprime #|H| #|G : H| && (H \subset G).              *)
(*          Sylow G P <=> P is a Sylow p-subgroup of G for some p.            *)
(*                    := p_group P && Hall G P.                               *)
(*           'O_pi(G) == the pi-core (largest normal pi-subgroup) of G.       *)
(*   pcore_mod pi G H == the pi-core of G mod H.                              *)
(*                    := G :&: (coset H @*^-1 'O_pi(G / H)).                  *)
(*   'O_{pi2, pi1}(G) == the pi1,pi2-core of G.                               *)
(*                    := the pi1-core of G mod 'O_pi2(G).                     *)
(*     -> We have 'O_{pi2, pi1}(G) / 'O_pi2(G) = 'O_pi1(G / 'O_pi2(G))        *)
(*        with 'O_pi2(G) <| 'O_{pi2, pi1}(G) <| G.                            *)
(* 'O_{pn, ..., p1}(G) == the p1, ..., pn-core of G.                          *)
(*                    := the p1-core of G mod 'O_{pn, ..., p2}(G).            *)
(* Note that notions are always defined on sets even though their name        *)
(* indicates "group" properties; the actual definition of the notion never    *)
(* tests for the group property, since this property will always be provided  *)
(* by a (canonical) group structure. Similarly, p-group properties assume     *)
(* without test that p is a prime.                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Section PgroupDefs.

(* We defer the definition of the functors ('0_p(G), etc) because they need *)
(* to quantify over the finGroupType explicitly.                            *)

Variable gT : finGroupType.
Implicit Type (x : gT) (A B : {set gT}) (pi : nat_pred) (p n : nat).

Definition pgroup pi A := pi.-nat #|A|.

Definition psubgroup pi A B := (B \subset A) && pgroup pi B.

Definition p_group A := pgroup (pdiv #|A|) A.

Definition p_elt pi x := pi.-nat #[x].

Definition constt x pi := x ^+ (chinese #[x]`_pi #[x]`_pi^' 1 0).

Definition Hall A B := (B \subset A) && coprime #|B| #|A : B|.

Definition pHall pi A B := [&& B \subset A, pgroup pi B & pi^'.-nat #|A : B|].

Definition Syl p A := [set P : {group gT} | pHall p A P].

Definition Sylow A B := p_group B && Hall A B.

End PgroupDefs.

Arguments pgroup {gT} pi%N A%g.
Arguments psubgroup {gT} pi%N A%g B%g.
Arguments p_group {gT} A%g.
Arguments p_elt {gT} pi%N x.
Arguments constt {gT} x%g pi%N.
Arguments Hall {gT} A%g B%g.
Arguments pHall {gT} pi%N A%g B%g.
Arguments Syl {gT} p%N A%g.
Arguments Sylow {gT} A%g B%g.

Notation "pi .-group" := (pgroup pi)
  (at level 2, format "pi .-group") : group_scope.

Notation "pi .-subgroup ( A )" := (psubgroup pi A)
  (at level 8, format "pi .-subgroup ( A )") : group_scope.

Notation "pi .-elt" := (p_elt pi)
  (at level 2, format "pi .-elt") : group_scope.

Notation "x .`_ pi" := (constt x pi)
  (at level 3, format "x .`_ pi") : group_scope.

Notation "pi .-Hall ( G )" := (pHall pi G)
  (at level 8, format "pi .-Hall ( G )") : group_scope.

Notation "p .-Sylow ( G )" := (nat_pred_of_nat p).-Hall(G)
  (at level 8, format "p .-Sylow ( G )") : group_scope.

Notation "''Syl_' p ( G )" := (Syl p G)
  (at level 8, p at level 2, format "''Syl_' p ( G )") : group_scope.

Section PgroupProps.

Variable gT : finGroupType.
Implicit Types (pi rho : nat_pred) (p : nat).
Implicit Types (x y z : gT) (A B C D : {set gT}) (G H K P Q R : {group gT}).

Lemma trivgVpdiv G : G :=: 1 \/ (exists2 p, prime p & p %| #|G|).
Proof.
have [leG1|lt1G] := leqP #|G| 1; first by left; apply: card_le1_trivg.
by right; exists (pdiv #|G|); rewrite ?pdiv_dvd ?pdiv_prime.
Qed.

Lemma prime_subgroupVti G H : prime #|G| -> G \subset H \/ H :&: G = 1.
Proof.
move=> prG; have [|[p p_pr pG]] := trivgVpdiv (H :&: G); first by right.
left; rewrite (sameP setIidPr eqP) eqEcard subsetIr.
suffices <-: p = #|G| by rewrite dvdn_leq ?cardG_gt0.
by apply/eqP; rewrite -dvdn_prime2 // -(LagrangeI G H) setIC dvdn_mulr.
Qed.

Lemma pgroupE pi A : pi.-group A = pi.-nat #|A|. Proof. by []. Qed.

Lemma sub_pgroup pi rho A : {subset pi <= rho} -> pi.-group A -> rho.-group A.
Proof. by move=> pi_sub_rho; apply: sub_in_pnat (in1W pi_sub_rho). Qed.

Lemma eq_pgroup pi rho A : pi =i rho -> pi.-group A = rho.-group A.
Proof. exact: eq_pnat. Qed.

Lemma eq_p'group pi rho A : pi =i rho -> pi^'.-group A = rho^'.-group A.
Proof. by move/eq_negn; apply: eq_pnat. Qed.

Lemma pgroupNK pi A : pi^'^'.-group A = pi.-group A.
Proof. exact: pnatNK. Qed.

Lemma pi_pgroup p pi A : p.-group A -> p \in pi -> pi.-group A.
Proof. exact: pi_pnat. Qed.

Lemma pi_p'group p pi A : pi.-group A -> p \in pi^' -> p^'.-group A.
Proof. exact: pi_p'nat. Qed.

Lemma pi'_p'group p pi A : pi^'.-group A -> p \in pi -> p^'.-group A.
Proof. exact: pi'_p'nat. Qed.

Lemma p'groupEpi p G : p^'.-group G = (p \notin \pi(G)).
Proof. exact: p'natEpi (cardG_gt0 G). Qed.

Lemma pgroup_pi G : \pi(G).-group G.
Proof. by rewrite /=; apply: pnat_pi. Qed.

Lemma partG_eq1 pi G : (#|G|`_pi == 1%N) = pi^'.-group G.
Proof. exact: partn_eq1 (cardG_gt0 G). Qed.

Lemma pgroupP pi G :
  reflect (forall p, prime p -> p %| #|G| -> p \in pi) (pi.-group G).
Proof. exact: pnatP. Qed.
Arguments pgroupP {pi G}.

Lemma pgroup1 pi : pi.-group [1 gT].
Proof. by rewrite /pgroup cards1. Qed.

Lemma pgroupS pi G H : H \subset G -> pi.-group G -> pi.-group H.
Proof. by move=> sHG; apply: pnat_dvd (cardSg sHG). Qed.

Lemma oddSg G H : H \subset G -> odd #|G| -> odd #|H|.
Proof. by rewrite !odd_2'nat; apply: pgroupS. Qed.

Lemma odd_pgroup_odd p G : odd p -> p.-group G -> odd #|G|.
Proof.
move=> p_odd pG; rewrite odd_2'nat (pi_pnat pG) // !inE.
by case: eqP p_odd => // ->.
Qed.

Lemma card_pgroup p G : p.-group G -> #|G| = (p ^ logn p #|G|)%N.
Proof. by move=> pG; rewrite -p_part part_pnat_id. Qed.

Lemma properG_ltn_log p G H :
  p.-group G -> H \proper G -> logn p #|H| < logn p #|G|.
Proof.
move=> pG; rewrite properEneq eqEcard andbC ltnNge => /andP[sHG].
rewrite sHG /= {1}(card_pgroup pG) {1}(card_pgroup (pgroupS sHG pG)).
by apply: contra; case: p {pG} => [|p] leHG; rewrite ?logn0 // leq_pexp2l.
Qed.

Lemma pgroupM pi G H : pi.-group (G * H) = pi.-group G && pi.-group H.
Proof.
have GH_gt0: 0 < #|G :&: H| := cardG_gt0 _.
rewrite /pgroup -(mulnK #|_| GH_gt0) -mul_cardG -(LagrangeI G H) -mulnA.
by rewrite mulKn // -(LagrangeI H G) setIC !pnat_mul andbCA; case: (pnat _).
Qed.

Lemma pgroupJ pi G x : pi.-group (G :^ x) = pi.-group G.
Proof. by rewrite /pgroup cardJg. Qed.

Lemma pgroup_p p P : p.-group P -> p_group P.
Proof.
case: (leqP #|P| 1); first by move=> /card_le1_trivg-> _; apply: pgroup1.
move/pdiv_prime=> pr_q pgP; have:= pgroupP pgP _ pr_q (pdiv_dvd _).
by rewrite /p_group => /eqnP->.
Qed.

Lemma p_groupP P : p_group P -> exists2 p, prime p & p.-group P.
Proof.
case: (ltnP 1 #|P|); first by move/pdiv_prime; exists (pdiv #|P|).
by move/card_le1_trivg=> -> _; exists 2 => //; apply: pgroup1.
Qed.

Lemma pgroup_pdiv p G :
    p.-group G -> G :!=: 1 ->
  [/\ prime p, p %| #|G| & exists m, #|G| = p ^ m.+1]%N.
Proof.
move=> pG; rewrite trivg_card1; case/p_groupP: (pgroup_p pG) => q q_pr qG.
move/implyP: (pgroupP pG q q_pr); case/p_natP: qG => // [[|m] ->] //.
by rewrite dvdn_exp // => /eqnP <- _; split; rewrite ?dvdn_exp //; exists m.
Qed.

Lemma coprime_p'group p K R :
  coprime #|K| #|R| -> p.-group R -> R :!=: 1 -> p^'.-group K.
Proof.
move=> coKR pR ntR; have [p_pr _ [e oK]] := pgroup_pdiv pR ntR.
by rewrite oK coprime_sym coprime_pexpl // prime_coprime // -p'natE in coKR.
Qed.

Lemma card_Hall pi G H : pi.-Hall(G) H -> #|H| = #|G|`_pi.
Proof.
case/and3P=> sHG piH pi'H; rewrite -(Lagrange sHG).
by rewrite partnM ?Lagrange // part_pnat_id ?part_p'nat ?muln1.
Qed.

Lemma pHall_sub pi A B : pi.-Hall(A) B -> B \subset A.
Proof. by case/andP. Qed.

Lemma pHall_pgroup pi A B : pi.-Hall(A) B -> pi.-group B.
Proof. by case/and3P. Qed.

Lemma pHallP pi G H : reflect (H \subset G /\ #|H| = #|G|`_pi) (pi.-Hall(G) H).
Proof.
apply: (iffP idP) => [piH | [sHG oH]].
  by split; [apply: pHall_sub piH | apply: card_Hall].
rewrite /pHall sHG -divgS // /pgroup oH.
by rewrite -{2}(@partnC pi #|G|) ?mulKn ?part_pnat.
Qed.

Lemma pHallE pi G H : pi.-Hall(G) H = (H \subset G) && (#|H| == #|G|`_pi).
Proof. by apply/pHallP/andP=> [] [->] /eqP. Qed.

Lemma coprime_mulpG_Hall pi G K R :
    K * R = G -> pi.-group K -> pi^'.-group R ->
  pi.-Hall(G) K /\ pi^'.-Hall(G) R.
Proof.
move=> defG piK pi'R; apply/andP.
rewrite /pHall piK -!divgS /= -defG ?mulG_subl ?mulg_subr //= pnatNK.
by rewrite coprime_cardMg ?(pnat_coprime piK) // mulKn ?mulnK //; apply/and3P.
Qed.

Lemma coprime_mulGp_Hall pi G K R :
    K * R = G -> pi^'.-group K -> pi.-group R ->
  pi^'.-Hall(G) K /\ pi.-Hall(G) R.
Proof.
move=> defG pi'K piR; apply/andP; rewrite andbC; apply/andP.
by apply: coprime_mulpG_Hall => //; rewrite -(comm_group_setP _) defG ?groupP.
Qed.

Lemma eq_in_pHall pi rho G H :
  {in \pi(G), pi =i rho} -> pi.-Hall(G) H = rho.-Hall(G) H.
Proof.
move=> eq_pi_rho; apply: andb_id2l => sHG.
congr (_ && _); apply: eq_in_pnat => p piHp.
  by apply: eq_pi_rho; apply: (piSg sHG).
by congr (~~ _); apply: eq_pi_rho; apply: (pi_of_dvd (dvdn_indexg G H)).
Qed.

Lemma eq_pHall pi rho G H : pi =i rho -> pi.-Hall(G) H = rho.-Hall(G) H.
Proof. by move=> eq_pi_rho; apply: eq_in_pHall (in1W eq_pi_rho). Qed.

Lemma eq_p'Hall pi rho G H : pi =i rho -> pi^'.-Hall(G) H = rho^'.-Hall(G) H.
Proof. by move=> eq_pi_rho; apply: eq_pHall (eq_negn _). Qed.

Lemma pHallNK pi G H : pi^'^'.-Hall(G) H = pi.-Hall(G) H.
Proof. exact: eq_pHall (negnK _). Qed.

Lemma subHall_Hall pi rho G H K :
  rho.-Hall(G) H -> {subset pi <= rho} -> pi.-Hall(H) K -> pi.-Hall(G) K.
Proof.
move=> hallH pi_sub_rho hallK.
rewrite pHallE (subset_trans (pHall_sub hallK) (pHall_sub hallH)) /=.
by rewrite (card_Hall hallK) (card_Hall hallH) partn_part.
Qed.

Lemma subHall_Sylow pi p G H P :
  pi.-Hall(G) H -> p \in pi -> p.-Sylow(H) P -> p.-Sylow(G) P.
Proof.
move=> hallH pi_p sylP; have [sHG piH _] := and3P hallH.
rewrite pHallE (subset_trans (pHall_sub sylP) sHG) /=.
by rewrite (card_Hall sylP) (card_Hall hallH) partn_part // => q; move/eqnP->.
Qed.

Lemma pHall_Hall pi A B : pi.-Hall(A) B -> Hall A B.
Proof. by case/and3P=> sBA piB pi'B; rewrite /Hall sBA (pnat_coprime piB). Qed.

Lemma Hall_pi G H : Hall G H -> \pi(H).-Hall(G) H.
Proof.
by case/andP=> sHG coHG /=; rewrite /pHall sHG /pgroup pnat_pi -?coprime_pi'.
Qed.

Lemma HallP G H : Hall G H -> exists pi, pi.-Hall(G) H.
Proof. by exists \pi(H); apply: Hall_pi. Qed.

Lemma sdprod_Hall G K H : K ><| H = G -> Hall G K = Hall G H.
Proof.
case/sdprod_context=> /andP[sKG _] sHG defG _ tiKH.
by rewrite /Hall sKG sHG -!divgS // -defG TI_cardMg // coprime_sym mulKn ?mulnK.
Qed.

Lemma coprime_sdprod_Hall_l G K H : K ><| H = G -> coprime #|K| #|H| = Hall G K.
Proof.
case/sdprod_context=> /andP[sKG _] _ defG _ tiKH.
by rewrite /Hall sKG -divgS // -defG TI_cardMg ?mulKn.
Qed.

Lemma coprime_sdprod_Hall_r G K H : K ><| H = G -> coprime #|K| #|H| = Hall G H.
Proof.
by move=> defG; rewrite (coprime_sdprod_Hall_l defG) (sdprod_Hall defG).
Qed.

Lemma compl_pHall pi K H G :
  pi.-Hall(G) K -> (H \in [complements to K in G]) = pi^'.-Hall(G) H.
Proof.
move=> hallK; apply/complP/idP=> [[tiKH mulKH] | hallH].
  have [_] := andP hallK; rewrite /pHall pnatNK -{3}(invGid G) -mulKH mulG_subr.
  by rewrite invMG !indexMg -indexgI andbC -indexgI setIC tiKH !indexg1.
have [[sKG piK _] [sHG pi'H _]] := (and3P hallK, and3P hallH).
have tiKH: K :&: H = 1 := coprime_TIg (pnat_coprime piK pi'H).
split=> //; apply/eqP; rewrite eqEcard mul_subG //= TI_cardMg //.
by rewrite (card_Hall hallK) (card_Hall hallH) partnC.
Qed.

Lemma compl_p'Hall pi K H G :
  pi^'.-Hall(G) K -> (H \in [complements to K in G]) = pi.-Hall(G) H.
Proof. by move/compl_pHall->; apply: eq_pHall (negnK pi). Qed.

Lemma sdprod_normal_p'HallP pi K H G :
  K <| G -> pi^'.-Hall(G) H -> reflect (K ><| H = G) (pi.-Hall(G) K).
Proof.
move=> nsKG hallH; rewrite -(compl_p'Hall K hallH).
exact: sdprod_normal_complP.
Qed.

Lemma sdprod_normal_pHallP pi K H G :
  K <| G -> pi.-Hall(G) H -> reflect (K ><| H = G) (pi^'.-Hall(G) K).
Proof.
by move=> nsKG hallH; apply: sdprod_normal_p'HallP; rewrite ?pHallNK.
Qed.

Lemma pHallJ2 pi G H x : pi.-Hall(G :^ x) (H :^ x) = pi.-Hall(G) H.
Proof. by rewrite !pHallE conjSg !cardJg. Qed.

Lemma pHallJnorm pi G H x : x \in 'N(G) -> pi.-Hall(G) (H :^ x) = pi.-Hall(G) H.
Proof. by move=> Nx; rewrite -{1}(normP Nx) pHallJ2. Qed.

Lemma pHallJ pi G H x : x \in G -> pi.-Hall(G) (H :^ x) = pi.-Hall(G) H.
Proof. by move=> Gx; rewrite -{1}(conjGid Gx) pHallJ2. Qed.

Lemma HallJ G H x : x \in G -> Hall G (H :^ x) = Hall G H.
Proof.
by move=> Gx; rewrite /Hall -!divgI -{1 3}(conjGid Gx) conjSg -conjIg !cardJg.
Qed.

Lemma psubgroupJ pi G H x :
  x \in G -> pi.-subgroup(G) (H :^ x) = pi.-subgroup(G) H.
Proof. by move=> Gx; rewrite /psubgroup pgroupJ -{1}(conjGid Gx) conjSg. Qed.

Lemma p_groupJ P x : p_group (P :^ x) = p_group P.
Proof. by rewrite /p_group cardJg pgroupJ. Qed.

Lemma SylowJ G P x : x \in G -> Sylow G (P :^ x) = Sylow G P.
Proof. by move=> Gx; rewrite /Sylow p_groupJ HallJ. Qed.

Lemma p_Sylow p G P : p.-Sylow(G) P -> Sylow G P.
Proof.
by move=> pP; rewrite /Sylow (pgroup_p (pHall_pgroup pP)) (pHall_Hall pP).
Qed.

Lemma pHall_subl pi G K H :
  H \subset K -> K \subset G -> pi.-Hall(G) H -> pi.-Hall(K) H.
Proof.
by move=> sHK sKG; rewrite /pHall sHK => /and3P[_ ->]; apply/pnat_dvd/indexSg.
Qed.

Lemma Hall1 G : Hall G 1.
Proof. by rewrite /Hall sub1G cards1 coprime1n. Qed.

Lemma p_group1 : @p_group gT 1.
Proof. by rewrite (@pgroup_p 2) ?pgroup1. Qed.

Lemma Sylow1 G : Sylow G 1.
Proof. by rewrite /Sylow p_group1 Hall1. Qed.

Lemma SylowP G P : reflect (exists2 p, prime p & p.-Sylow(G) P) (Sylow G P).
Proof.
apply: (iffP idP) => [| [p _]]; last exact: p_Sylow.
case/andP=> /p_groupP[p p_pr] /p_natP[[P1 _ | n oP /Hall_pi]]; last first.
  by rewrite /= oP pi_of_exp // (eq_pHall _ _ (pi_of_prime _)) //; exists p.
have{p p_pr P1} ->: P :=: 1 by apply: card1_trivg; rewrite P1.
pose p := pdiv #|G|.+1; have p_pr: prime p by rewrite pdiv_prime ?ltnS.
exists p; rewrite // pHallE sub1G cards1 part_p'nat //.
apply/pgroupP=> q pr_q qG; apply/eqnP=> def_q.
have: p %| #|G| + 1 by rewrite addn1 pdiv_dvd.
by rewrite dvdn_addr -def_q // Euclid_dvd1.
Qed.

Lemma p_elt_exp pi x m : pi.-elt (x ^+ m) = (#[x]`_pi^' %| m).
Proof.
apply/idP/idP=> [pi_xm | /dvdnP[q ->{m}]]; last first.
  rewrite mulnC; apply: pnat_dvd (part_pnat pi #[x]).
  by rewrite order_dvdn -expgM mulnC mulnA partnC // -order_dvdn dvdn_mulr.
rewrite -(@Gauss_dvdr _ #[x ^+ m]); last first.
  by rewrite coprime_sym (pnat_coprime pi_xm) ?part_pnat.
apply: (@dvdn_trans #[x]); first by rewrite -{2}[#[x]](partnC pi) ?dvdn_mull.
by rewrite order_dvdn mulnC expgM expg_order.
Qed.

Lemma mem_p_elt pi x G : pi.-group G -> x \in G -> pi.-elt x.
Proof. by move=> piG Gx; apply: pgroupS piG; rewrite cycle_subG. Qed.

Lemma p_eltM_norm pi x y :
  x \in 'N(<[y]>) -> pi.-elt x -> pi.-elt y -> pi.-elt (x * y).
Proof.
move=> nyx pi_x pi_y; apply: (@mem_p_elt pi _ (<[x]> <*> <[y]>)%G).
  by rewrite /= norm_joinEl ?cycle_subG // pgroupM; apply/andP.
by rewrite groupM // mem_gen // inE cycle_id ?orbT.
Qed.

Lemma p_eltM pi x y : commute x y -> pi.-elt x -> pi.-elt y -> pi.-elt (x * y).
Proof.
move=> cxy; apply: p_eltM_norm; apply: (subsetP (cent_sub _)).
by rewrite cent_gen cent_set1; apply/cent1P.
Qed.

Lemma p_elt1 pi : pi.-elt (1 : gT).
Proof. by rewrite /p_elt order1. Qed.

Lemma p_eltV pi x : pi.-elt x^-1 = pi.-elt x.
Proof. by rewrite /p_elt orderV. Qed.

Lemma p_eltX pi x n : pi.-elt x -> pi.-elt (x ^+ n).
Proof. by rewrite -{1}[x]expg1 !p_elt_exp dvdn1 => /eqnP->. Qed.

Lemma p_eltJ pi x y : pi.-elt (x ^ y) = pi.-elt x.
Proof. by congr pnat; rewrite orderJ. Qed.

Lemma sub_p_elt pi1 pi2 x : {subset pi1 <= pi2} -> pi1.-elt x -> pi2.-elt x.
Proof. by move=> pi12; apply: sub_in_pnat => q _; apply: pi12. Qed.

Lemma eq_p_elt pi1 pi2 x : pi1 =i pi2 -> pi1.-elt x = pi2.-elt x.
Proof. by move=> pi12; apply: eq_pnat. Qed.

Lemma p_eltNK pi x : pi^'^'.-elt x = pi.-elt x.
Proof. exact: pnatNK. Qed.

Lemma eq_constt pi1 pi2 x : pi1 =i pi2 -> x.`_pi1 = x.`_pi2.
Proof.
move=> pi12; congr (x ^+ (chinese _ _ 1 0)); apply: eq_partn => // a.
by congr (~~ _); apply: pi12.
Qed.

Lemma consttNK pi x : x.`_pi^'^' = x.`_pi.
Proof. by rewrite /constt !partnNK. Qed.

Lemma cycle_constt pi x : x.`_pi \in <[x]>.
Proof. exact: mem_cycle. Qed.

Lemma consttV pi x : (x^-1).`_pi = (x.`_pi)^-1.
Proof. by rewrite /constt expgVn orderV. Qed.

Lemma constt1 pi : 1.`_pi = 1 :> gT.
Proof. exact: expg1n. Qed.

Lemma consttJ pi x y : (x ^ y).`_pi = x.`_pi ^ y.
Proof. by rewrite /constt orderJ conjXg. Qed.

Lemma p_elt_constt pi x : pi.-elt x.`_pi.
Proof. by rewrite p_elt_exp /chinese addn0 mul1n dvdn_mulr. Qed.

Lemma consttC pi x : x.`_pi * x.`_pi^' = x.
Proof.
apply/eqP; rewrite -{3}[x]expg1 -expgD eq_expg_mod_order.
rewrite partnNK -{5 6}(@partnC pi #[x]) // /chinese !addn0.
by rewrite chinese_remainder ?chinese_modl ?chinese_modr ?coprime_partC ?eqxx.
Qed.

Lemma p'_elt_constt pi x : pi^'.-elt (x * (x.`_pi)^-1).
Proof. by rewrite -{1}(consttC pi^' x) consttNK mulgK p_elt_constt. Qed.

Lemma order_constt pi (x : gT) : #[x.`_pi] = #[x]`_pi.
Proof.
rewrite -{2}(consttC pi x) orderM; [|exact: commuteX2|]; last first.
  by apply: (@pnat_coprime pi); apply: p_elt_constt.
by rewrite partnM // part_pnat_id ?part_p'nat ?muln1 //; apply: p_elt_constt.
Qed.

Lemma consttM pi x y : commute x y -> (x * y).`_pi = x.`_pi * y.`_pi.
Proof.
move=> cxy; pose m := #|<<[set x; y]>>|; have m_gt0: 0 < m := cardG_gt0 _.
pose k := chinese m`_pi m`_pi^' 1 0.
suffices kXpi z: z \in <<[set x; y]>> -> z.`_pi = z ^+ k.
  by rewrite !kXpi ?expgMn // ?groupM ?mem_gen // !inE eqxx ?orbT.
move=> xyz; have{xyz} zm: #[z] %| m by rewrite cardSg ?cycle_subG.
apply/eqP; rewrite eq_expg_mod_order -{3 4}[#[z]](partnC pi) //.
rewrite chinese_remainder ?chinese_modl ?chinese_modr ?coprime_partC //.
rewrite -!(modn_dvdm k (partn_dvd _ m_gt0 zm)).
rewrite chinese_modl ?chinese_modr ?coprime_partC //.
by rewrite !modn_dvdm ?partn_dvd ?eqxx.
Qed.

Lemma consttX pi x n : (x ^+ n).`_pi = x.`_pi ^+ n.
Proof.
elim: n => [|n IHn]; first exact: constt1.
by rewrite !expgS consttM ?IHn //; apply: commuteX.
Qed.

Lemma constt1P pi x : reflect (x.`_pi = 1) (pi^'.-elt x).
Proof.
rewrite -{2}[x]expg1 p_elt_exp -order_constt consttNK order_dvdn expg1.
exact: eqP.
Qed.

Lemma constt_p_elt pi x : pi.-elt x -> x.`_pi = x.
Proof.
by rewrite -p_eltNK -{3}(consttC pi x) => /constt1P->; rewrite mulg1.
Qed.

Lemma sub_in_constt pi1 pi2 x :
  {in \pi(#[x]), {subset pi1 <= pi2}} -> x.`_pi2.`_pi1 = x.`_pi1.
Proof.
move=> pi12; rewrite -{2}(consttC pi2 x) consttM; last exact: commuteX2.
rewrite (constt1P _ x.`_pi2^' _) ?mulg1 //.
apply: sub_in_pnat (p_elt_constt _ x) => p; rewrite order_constt => pi_p.
apply: contra; apply: pi12.
by rewrite -[#[x]](partnC pi2^') // primes_mul // pi_p.
Qed.

Lemma prod_constt x : \prod_(0 <= p < #[x].+1) x.`_p = x.
Proof.
pose lp n := [pred p | p < n].
have: (lp #[x].+1).-elt x by apply/pnatP=> // p _; apply: dvdn_leq.
move/constt_p_elt=> def_x; symmetry; rewrite -{1}def_x {def_x}.
elim: _.+1 => [|p IHp].
  by rewrite big_nil; apply/constt1P; apply/pgroupP.
rewrite big_nat_recr //= -{}IHp -(consttC (lp p) x.`__); congr (_ * _).
  by rewrite sub_in_constt // => q _; apply: leqW.
set y := _.`__; rewrite -(consttC p y) (constt1P p^' _ _) ?mulg1.
  by rewrite 2?sub_in_constt // => q _; move/eqnP->; rewrite !inE ?ltnn.
rewrite /p_elt pnatNK !order_constt -partnI.
apply: sub_in_pnat (part_pnat _ _) => q _.
by rewrite !inE ltnS -leqNgt -eqn_leq.
Qed.

Lemma max_pgroupJ pi M G x :
    x \in G -> [max M | pi.-subgroup(G) M] ->
  [max M :^ x of M | pi.-subgroup(G) M].
Proof.
move=> Gx /maxgroupP[piM maxM]; apply/maxgroupP.
split=> [|H piH]; first by rewrite psubgroupJ.
by rewrite -(conjsgKV x H) conjSg => /maxM/=-> //; rewrite psubgroupJ ?groupV.
Qed.

Lemma comm_sub_max_pgroup pi H M G :
    [max M | pi.-subgroup(G) M] -> pi.-group H -> H \subset G ->
  commute H M -> H \subset M.
Proof.
case/maxgroupP=> /andP[sMG piM] maxM piH sHG cHM.
rewrite -(maxM (H <*> M)%G) /= comm_joingE ?(mulG_subl, mulG_subr) //.
by rewrite /psubgroup pgroupM piM piH mul_subG.
Qed.

Lemma normal_sub_max_pgroup pi H M G :
  [max M | pi.-subgroup(G) M] -> pi.-group H -> H <| G -> H \subset M.
Proof.
move=> maxM piH /andP[sHG nHG].
apply: comm_sub_max_pgroup piH sHG _ => //; apply: commute_sym; apply: normC.
by apply: subset_trans nHG; case/andP: (maxgroupp maxM).
Qed.

Lemma norm_sub_max_pgroup pi H M G :
    [max M | pi.-subgroup(G) M] -> pi.-group H -> H \subset G ->
  H \subset 'N(M) -> H \subset M.
Proof. by move=> maxM piH sHG /normC; apply: comm_sub_max_pgroup piH sHG. Qed.

Lemma sub_pHall pi H G K :
  pi.-Hall(G) H -> pi.-group K -> H \subset K -> K \subset G -> K :=: H.
Proof.
move=> hallH piK sHK sKG; apply/eqP; rewrite eq_sym eqEcard sHK.
by rewrite (card_Hall hallH) -(part_pnat_id piK) dvdn_leq ?partn_dvd ?cardSg.
Qed.

Lemma Hall_max pi H G : pi.-Hall(G) H -> [max H | pi.-subgroup(G) H].
Proof.
move=> hallH; apply/maxgroupP; split=> [|K /andP[sKG piK] sHK].
  by rewrite /psubgroup; case/and3P: hallH => ->.
exact: (sub_pHall hallH).
Qed.

Lemma pHall_id pi H G : pi.-Hall(G) H -> pi.-group G -> H :=: G.
Proof.
by move=> hallH piG; rewrite (sub_pHall hallH piG) ?(pHall_sub hallH).
Qed.

Lemma psubgroup1 pi G : pi.-subgroup(G) 1.
Proof. by rewrite /psubgroup sub1G pgroup1. Qed.

Lemma Cauchy p G : prime p -> p %| #|G| -> {x | x \in G & #[x] = p}.
Proof.
move=> p_pr; elim: {G}_.+1 {-2}G (ltnSn #|G|) => // n IHn G.
rewrite ltnS => leGn pG; pose xpG := [pred x in G | #[x] == p].
have [x /andP[Gx /eqP] | no_x] := pickP xpG; first by exists x.
have{pG n leGn IHn} pZ: p %| #|'C_G(G)|.
  suffices /dvdn_addl <-:  p %| #|G :\: 'C(G)| by rewrite cardsID.
  have /acts_sum_card_orbit <-: [acts G, on G :\: 'C(G) | 'J].
    by apply/actsP=> x Gx y; rewrite !inE -!mem_conjgV -centJ conjGid ?groupV.
  elim/big_rec: _ => // _ _ /imsetP[x /setDP[Gx nCx] ->] /dvdn_addl->.
  have ltCx: 'C_G[x] \proper G by rewrite properE subsetIl subsetIidl sub_cent1.
  have /negP: ~ p %| #|'C_G[x]|.
    case/(IHn _ (leq_trans (proper_card ltCx) leGn))=> y /setIP[Gy _] /eqP-oy.
    by have /andP[] := no_x y.
  by apply/implyP; rewrite -index_cent1 indexgI implyNb -Euclid_dvdM ?LagrangeI.
have [Q maxQ _]: {Q | [max Q | p^'.-subgroup('C_G(G)) Q] & 1%G \subset Q}.
  by apply: maxgroup_exists; apply: psubgroup1.
case/andP: (maxgroupp maxQ) => sQC; rewrite /pgroup p'natE // => /negP[].
apply: dvdn_trans pZ (cardSg _); apply/subsetP=> x /setIP[Gx Cx].
rewrite -sub1set -gen_subG (normal_sub_max_pgroup maxQ) //; last first.
  rewrite /normal subsetI !cycle_subG ?Gx ?cents_norm ?subIset ?andbT //=.
  by rewrite centsC cycle_subG Cx.
rewrite /pgroup p'natE //= -[#|_|]/#[x]; apply/dvdnP=> [[m oxm]].
have m_gt0: 0 < m by apply: dvdn_gt0 (order_gt0 x) _; rewrite oxm dvdn_mulr.
case/idP: (no_x (x ^+ m)); rewrite /= groupX //= orderXgcd //= oxm.
by rewrite gcdnC gcdnMr mulKn.
Qed.

(* These lemmas actually hold for maximal pi-groups, but below we'll *)
(* derive from the Cauchy lemma that a normal max pi-group is Hall.  *)

Lemma sub_normal_Hall pi G H K :
  pi.-Hall(G) H -> H <| G -> K \subset G -> (K \subset H) = pi.-group K.
Proof.
move=> hallH nsHG sKG; apply/idP/idP=> [sKH | piK].
  by rewrite (pgroupS sKH) ?(pHall_pgroup hallH).
apply: norm_sub_max_pgroup (Hall_max hallH) piK _ _ => //.
exact: subset_trans sKG (normal_norm nsHG).
Qed.

Lemma mem_normal_Hall pi H G x :
  pi.-Hall(G) H -> H <| G -> x \in G -> (x \in H) = pi.-elt x.
Proof. by rewrite -!cycle_subG; apply: sub_normal_Hall. Qed.

Lemma uniq_normal_Hall pi H G K :
  pi.-Hall(G) H -> H <| G -> [max K | pi.-subgroup(G) K] -> K :=: H.
Proof.
move=> hallH nHG /maxgroupP[/andP[sKG piK] /(_ H) -> //].
  exact: (maxgroupp (Hall_max hallH)).
by rewrite (sub_normal_Hall hallH).
Qed.

End PgroupProps.

Arguments pgroupP {gT pi G}.
Arguments constt1P {gT pi x}.

Section NormalHall.

Variables (gT : finGroupType) (pi : nat_pred).
Implicit Types G H K : {group gT}.

Lemma normal_max_pgroup_Hall G H :
  [max H | pi.-subgroup(G) H] -> H <| G -> pi.-Hall(G) H.
Proof.
case/maxgroupP=> /andP[sHG piH] maxH nsHG; have [_ nHG] := andP nsHG.
rewrite /pHall sHG piH; apply/pnatP=> // p p_pr.
rewrite inE /= -pnatE // -card_quotient //.
case/Cauchy=> //= Hx; rewrite -sub1set -gen_subG -/<[Hx]> /order.
case/inv_quotientS=> //= K -> sHK sKG {Hx}.
rewrite card_quotient ?(subset_trans sKG) // => iKH; apply/negP=> pi_p.
rewrite -iKH -divgS // (maxH K) ?divnn ?cardG_gt0 // in p_pr.
by rewrite /psubgroup sKG /pgroup -(Lagrange sHK) mulnC pnat_mul iKH pi_p.
Qed.

Lemma setI_normal_Hall G H K :
  H <| G -> pi.-Hall(G) H -> K \subset G -> pi.-Hall(K) (H :&: K).
Proof.
move=> nsHG hallH sKG; apply: normal_max_pgroup_Hall; last first.
  by rewrite /= setIC (normalGI sKG nsHG).
apply/maxgroupP; split=> [|M /andP[sMK piM] sHK_M].
  by rewrite /psubgroup subsetIr (pgroupS (subsetIl _ _) (pHall_pgroup hallH)).
apply/eqP; rewrite eqEsubset sHK_M subsetI sMK !andbT.
by rewrite (sub_normal_Hall hallH) // (subset_trans sMK).
Qed.

End NormalHall.

Section Morphim.

Variables (aT rT : finGroupType) (D : {group aT}) (f : {morphism D >-> rT}).
Implicit Types (pi : nat_pred) (G H P : {group aT}).

Lemma morphim_pgroup pi G : pi.-group G -> pi.-group (f @* G).
Proof. by apply: pnat_dvd; apply: dvdn_morphim. Qed.

Lemma morphim_odd G : odd #|G| -> odd #|f @* G|.
Proof. by rewrite !odd_2'nat; apply: morphim_pgroup. Qed.

Lemma pmorphim_pgroup pi G :
   pi.-group ('ker f) -> G \subset D -> pi.-group (f @* G) = pi.-group G.
Proof.
move=> piker sGD; apply/idP/idP=> [pifG|]; last exact: morphim_pgroup.
apply: (@pgroupS _ _ (f @*^-1 (f @* G))); first by rewrite -sub_morphim_pre.
by rewrite /pgroup card_morphpre ?morphimS // pnat_mul; apply/andP.
Qed.

Lemma morphim_p_index pi G H :
  H \subset D -> pi.-nat #|G : H| -> pi.-nat #|f @* G : f @* H|.
Proof.
by move=> sHD; apply: pnat_dvd; rewrite index_morphim ?subIset // sHD orbT.
Qed.

Lemma morphim_pHall pi G H :
  H \subset D -> pi.-Hall(G) H -> pi.-Hall(f @* G) (f @* H).
Proof.
move=> sHD /and3P[sHG piH pi'GH].
by rewrite /pHall morphimS // morphim_pgroup // morphim_p_index.
Qed.

Lemma pmorphim_pHall pi G H :
    G \subset D -> H \subset D -> pi.-subgroup(H :&: G) ('ker f) ->
  pi.-Hall(f @* G) (f @* H) = pi.-Hall(G) H.
Proof.
move=> sGD sHD /andP[/subsetIP[sKH sKG] piK]; rewrite !pHallE morphimSGK //.
apply: andb_id2l => sHG; rewrite -(Lagrange sKH) -(Lagrange sKG) partnM //.
by rewrite (part_pnat_id piK) !card_morphim !(setIidPr _) // eqn_pmul2l.
Qed.

Lemma morphim_Hall G H : H \subset D -> Hall G H -> Hall (f @* G) (f @* H).
Proof.
by move=> sHD /HallP[pi piH]; apply: (@pHall_Hall _ pi); apply: morphim_pHall.
Qed.

Lemma morphim_pSylow p G P :
  P \subset D -> p.-Sylow(G) P -> p.-Sylow(f @* G) (f @* P).
Proof. exact: morphim_pHall. Qed.

Lemma morphim_p_group P : p_group P -> p_group (f @* P).
Proof. by move/morphim_pgroup; apply: pgroup_p. Qed.

Lemma morphim_Sylow G P : P \subset D -> Sylow G P -> Sylow (f @* G) (f @* P).
Proof.
by move=> sPD /andP[pP hallP]; rewrite /Sylow morphim_p_group // morphim_Hall.
Qed.

Lemma morph_p_elt pi x : x \in D -> pi.-elt x -> pi.-elt (f x).
Proof. by move=> Dx; apply: pnat_dvd; apply: morph_order. Qed.

Lemma morph_constt pi x : x \in D -> f x.`_pi = (f x).`_pi.
Proof.
move=> Dx; rewrite -{2}(consttC pi x) morphM ?groupX //.
rewrite consttM; last by rewrite !morphX //; apply: commuteX2.
have: pi.-elt (f x.`_pi) by rewrite morph_p_elt ?groupX ?p_elt_constt //.
have: pi^'.-elt (f x.`_pi^') by rewrite morph_p_elt ?groupX ?p_elt_constt //.
by move/constt1P->; move/constt_p_elt->; rewrite mulg1.
Qed.

End Morphim.

Section Pquotient.

Variables (pi : nat_pred) (gT : finGroupType) (p : nat) (G H K : {group gT}).
Hypothesis piK : pi.-group K.

Lemma quotient_pgroup : pi.-group (K / H). Proof. exact: morphim_pgroup. Qed.

Lemma quotient_pHall :
  K \subset 'N(H) -> pi.-Hall(G) K -> pi.-Hall(G / H) (K / H).
Proof. exact: morphim_pHall. Qed.

Lemma quotient_odd : odd #|K| -> odd #|K / H|. Proof. exact: morphim_odd. Qed.

Lemma pquotient_pgroup : G \subset 'N(K) -> pi.-group (G / K) = pi.-group G.
Proof. by move=> nKG; rewrite pmorphim_pgroup ?ker_coset. Qed.

Lemma pquotient_pHall :
  K <| G -> K <| H -> pi.-Hall(G / K) (H / K) = pi.-Hall(G) H.
Proof.
case/andP=> sKG nKG; case/andP=> sKH nKH.
by rewrite pmorphim_pHall // ker_coset /psubgroup subsetI sKH sKG.
Qed.

Lemma ltn_log_quotient :
  p.-group G -> H :!=: 1 -> H \subset G -> logn p #|G / H| < logn p #|G|.
Proof.
move=> pG ntH sHG; apply: contraLR (ltn_quotient ntH sHG); rewrite -!leqNgt.
rewrite {2}(card_pgroup pG) {2}(card_pgroup (morphim_pgroup _ pG)).
by case: (posnP p) => [-> //|]; apply: leq_pexp2l.
Qed.

End Pquotient.

(* Application of card_Aut_cyclic to internal faithful action on cyclic *)
(* p-subgroups.                                                         *)
Section InnerAutCyclicPgroup.

Variables (gT : finGroupType) (p : nat) (G C : {group gT}).
Hypothesis nCG : G \subset 'N(C).

Lemma logn_quotient_cent_cyclic_pgroup : 
  p.-group C -> cyclic C -> logn p #|G / 'C_G(C)| <= (logn p #|C|).-1.
Proof.
move=> pC cycC; have [-> | ntC] := eqsVneq C 1.
  by rewrite cent1T setIT trivg_quotient cards1 logn1.
have [p_pr _ [e oC]] := pgroup_pdiv pC ntC.
rewrite -ker_conj_aut (card_isog (first_isog_loc _ _)) //.
apply: leq_trans (dvdn_leq_log _ _ (cardSg (Aut_conj_aut _ _))) _ => //.
rewrite card_Aut_cyclic // oC totient_pfactor //= logn_Gauss ?pfactorK //.
by rewrite prime_coprime // gtnNdvd // -(subnKC (prime_gt1 p_pr)).
Qed.

Lemma p'group_quotient_cent_prime :
  prime p -> #|C| %| p -> p^'.-group (G / 'C_G(C)).
Proof.
move=> p_pr pC; have pgC: p.-group C := pnat_dvd pC (pnat_id p_pr).
have [_ dv_p] := primeP p_pr; case/pred2P: {dv_p pC}(dv_p _ pC) => [|pC].
  by move/card1_trivg->; rewrite cent1T setIT trivg_quotient pgroup1.
have le_oGC := logn_quotient_cent_cyclic_pgroup pgC.
rewrite /pgroup -partn_eq1 ?cardG_gt0 // -dvdn1 p_part pfactor_dvdn // logn1.
by rewrite (leq_trans (le_oGC _)) ?prime_cyclic // pC ?(pfactorK 1).
Qed.

End InnerAutCyclicPgroup.

Section PcoreDef.

(* A functor needs to quantify over the finGroupType just beore the set. *)

Variables (pi : nat_pred) (gT : finGroupType) (A : {set gT}).

Definition pcore := \bigcap_(G | [max G | pi.-subgroup(A) G]) G.

Canonical pcore_group : {group gT} := Eval hnf in [group of pcore].

End PcoreDef.

Arguments pcore pi%N {gT} A%g.
Arguments pcore_group pi%N {gT} A%G.
Notation "''O_' pi ( G )" := (pcore pi G)
  (at level 8, pi at level 2, format "''O_' pi ( G )") : group_scope.
Notation "''O_' pi ( G )" := (pcore_group pi G) : Group_scope.

Section PseriesDefs.

Variables (pis : seq nat_pred) (gT : finGroupType) (A : {set gT}).

Definition pcore_mod pi B := coset B @*^-1 'O_pi(A / B).
Canonical pcore_mod_group pi B : {group gT} :=
  Eval hnf in [group of pcore_mod pi B].

Definition pseries := foldr pcore_mod 1 (rev pis).

Lemma pseries_group_set : group_set pseries.
Proof. by rewrite /pseries; case: rev => [|pi1 pi1']; apply: groupP. Qed.

Canonical pseries_group : {group gT} := group pseries_group_set.

End PseriesDefs.

Arguments pseries pis%SEQ {gT} _%g.
Local Notation ConsPred p := (@Cons nat_pred p%N) (only parsing).
Notation "''O_{' p1 , .. , pn } ( A )" :=
  (pseries (ConsPred p1 .. (ConsPred pn [::]) ..) A)
  (at level 8, format "''O_{' p1 , .. , pn } ( A )") : group_scope.
Notation "''O_{' p1 , .. , pn } ( A )" :=
  (pseries_group (ConsPred p1 .. (ConsPred pn [::]) ..) A) : Group_scope.

Section PCoreProps.

Variables (pi : nat_pred) (gT : finGroupType).
Implicit Types (A : {set gT}) (G H M K : {group gT}).

Lemma pcore_psubgroup G : pi.-subgroup(G) 'O_pi(G).
Proof.
have [M maxM _]: {M | [max M | pi.-subgroup(G) M] & 1%G \subset M}.
  by apply: maxgroup_exists; rewrite /psubgroup sub1G pgroup1.
have sOM: 'O_pi(G) \subset M by apply: bigcap_inf.
have /andP[piM sMG] := maxgroupp maxM.
by rewrite /psubgroup (pgroupS sOM) // (subset_trans sOM).
Qed.

Lemma pcore_pgroup G : pi.-group 'O_pi(G).
Proof. by case/andP: (pcore_psubgroup G). Qed.

Lemma pcore_sub G : 'O_pi(G) \subset G.
Proof. by case/andP: (pcore_psubgroup G). Qed.

Lemma pcore_sub_Hall G H : pi.-Hall(G) H -> 'O_pi(G) \subset H.
Proof. by move/Hall_max=> maxH; apply: bigcap_inf. Qed.

Lemma pcore_max G H : pi.-group H -> H <| G -> H \subset 'O_pi(G).
Proof.
move=> piH nHG; apply/bigcapsP=> M maxM.
exact: normal_sub_max_pgroup piH nHG.
Qed.

Lemma pcore_pgroup_id G : pi.-group G -> 'O_pi(G) = G.
Proof. by move=> piG; apply/eqP; rewrite eqEsubset pcore_sub pcore_max. Qed.

Lemma pcore_normal G : 'O_pi(G) <| G.
Proof.
rewrite /(_ <| G) pcore_sub; apply/subsetP=> x Gx.
rewrite inE; apply/bigcapsP=> M maxM; rewrite sub_conjg.
by apply: bigcap_inf; apply: max_pgroupJ; rewrite ?groupV.
Qed.

Lemma normal_Hall_pcore H G : pi.-Hall(G) H -> H <| G -> 'O_pi(G) = H.
Proof.
move=> hallH nHG; apply/eqP.
rewrite eqEsubset (sub_normal_Hall hallH) ?pcore_sub ?pcore_pgroup //=.
by rewrite pcore_max //= (pHall_pgroup hallH).
Qed.

Lemma eq_Hall_pcore G H :
   pi.-Hall(G) 'O_pi(G) -> pi.-Hall(G) H -> H :=: 'O_pi(G).
Proof.
move=> hallGpi hallH.
exact: uniq_normal_Hall (pcore_normal G) (Hall_max hallH).
Qed.

Lemma sub_Hall_pcore G K :
  pi.-Hall(G) 'O_pi(G) -> K \subset G -> (K \subset 'O_pi(G)) = pi.-group K.
Proof. by move=> hallGpi; apply: sub_normal_Hall (pcore_normal G). Qed.

Lemma mem_Hall_pcore G x :
  pi.-Hall(G) 'O_pi(G) -> x \in G -> (x \in 'O_pi(G)) = pi.-elt x.
Proof. by move=> hallGpi; apply: mem_normal_Hall (pcore_normal G). Qed.

Lemma sdprod_Hall_pcoreP H G :
  pi.-Hall(G) 'O_pi(G) -> reflect ('O_pi(G) ><| H = G) (pi^'.-Hall(G) H).
Proof.
move=> hallGpi; rewrite -(compl_pHall H hallGpi) complgC.
exact: sdprod_normal_complP (pcore_normal G).
Qed.

Lemma sdprod_pcore_HallP H G :
  pi^'.-Hall(G) H -> reflect ('O_pi(G) ><| H = G) (pi.-Hall(G) 'O_pi(G)).
Proof. exact: sdprod_normal_p'HallP (pcore_normal G). Qed.

Lemma pcoreJ G x : 'O_pi(G :^ x) = 'O_pi(G) :^ x.
Proof.
apply/eqP; rewrite eqEsubset -sub_conjgV.
rewrite !pcore_max ?pgroupJ ?pcore_pgroup ?normalJ ?pcore_normal //.
by rewrite -(normalJ _ _ x) conjsgKV pcore_normal.
Qed.

End PCoreProps.

Section MorphPcore.

Implicit Types (pi : nat_pred) (gT rT : finGroupType).

Lemma morphim_pcore pi : GFunctor.pcontinuous (@pcore pi).
Proof.
move=> gT rT D G f; apply/bigcapsP=> M /normal_sub_max_pgroup; apply.
  by rewrite morphim_pgroup ?pcore_pgroup.
by apply: morphim_normal; apply: pcore_normal.
Qed.

Lemma pcoreS pi gT (G H : {group gT}) :
  H \subset G -> H :&: 'O_pi(G) \subset 'O_pi(H).
Proof.
move=> sHG; rewrite -{2}(setIidPl sHG).
by do 2!rewrite -(morphim_idm (subsetIl H _)) morphimIdom; apply: morphim_pcore.
Qed.

Canonical pcore_igFun pi := [igFun by pcore_sub pi & morphim_pcore pi].
Canonical pcore_gFun pi := [gFun by morphim_pcore pi].
Canonical pcore_pgFun pi := [pgFun by morphim_pcore pi].

Lemma pcore_char pi gT (G : {group gT}) : 'O_pi(G) \char G.
Proof. exact: gFchar. Qed.

Section PcoreMod.

Variable F : GFunctor.pmap.

Lemma pcore_mod_sub pi gT (G : {group gT}) : pcore_mod G pi (F _ G) \subset G.
Proof.
by rewrite sub_morphpre_im ?gFsub_trans ?morphimS ?gFnorm //= ker_coset gFsub.
Qed.

Lemma quotient_pcore_mod pi gT (G : {group gT}) (B : {set gT}) :
  pcore_mod G pi B / B = 'O_pi(G / B).
Proof. exact/morphpreK/gFsub_trans/morphim_sub. Qed.

Lemma morphim_pcore_mod pi gT rT (D G : {group gT}) (f : {morphism D >-> rT}) :
  f @* pcore_mod G pi (F _ G) \subset pcore_mod (f @* G) pi (F _ (f @* G)).
Proof.
have sDF: D :&: G \subset 'dom (coset (F _ G)).
  by rewrite setIC subIset ?gFnorm.
have sDFf: D :&: G \subset 'dom (coset (F _ (f @* G)) \o f).
  by rewrite -sub_morphim_pre ?subsetIl // morphimIdom gFnorm.
pose K := 'ker (restrm sDFf (coset (F _ (f @* G)) \o f)).
have sFK: 'ker (restrm sDF (coset (F _ G))) \subset K.
  rewrite /K !ker_restrm ker_comp /= subsetI subsetIl /= -setIA.
  rewrite -sub_morphim_pre ?subsetIl //.
  by rewrite morphimIdom !ker_coset (setIidPr _) ?pmorphimF ?gFsub.
have sOF := pcore_sub pi (G / F _ G); have sDD: D :&: G \subset D :&: G by [].
rewrite -sub_morphim_pre -?quotientE; last first.
  by apply: subset_trans (gFnorm F _); rewrite morphimS ?pcore_mod_sub.
suffices im_fact (H : {group gT}) : F _ G \subset H -> H \subset G ->
  factm sFK sDD @* (H / F _ G) = f @* H / F _ (f @* G).
- rewrite -2?im_fact ?pcore_mod_sub ?gFsub //;
    try by rewrite -{1}[F _ G]ker_coset morphpreS ?sub1G.
  by rewrite quotient_pcore_mod morphim_pcore.
move=> sFH sHG; rewrite -(morphimIdom _ (H / _)) /= {2}morphim_restrm setIid.
rewrite -morphimIG ?ker_coset //.
rewrite -(morphim_restrm sDF) morphim_factm morphim_restrm.
by rewrite morphim_comp -quotientE -setIA morphimIdom (setIidPr _).
Qed.

Lemma pcore_mod_res pi gT rT (D : {group gT}) (f : {morphism D >-> rT}) :
  f @* pcore_mod D pi (F _ D) \subset pcore_mod (f @* D) pi (F _ (f @* D)).
Proof. exact: morphim_pcore_mod. Qed.

Lemma pcore_mod1 pi gT (G : {group gT}) : pcore_mod G pi 1 = 'O_pi(G).
Proof.
rewrite /pcore_mod; have inj1 := coset1_injm gT; rewrite -injmF ?norms1 //.
by rewrite -(morphim_invmE inj1) morphim_invm ?norms1.
Qed.

End PcoreMod.

Lemma pseries_rcons pi pis gT (A : {set gT}) :
  pseries (rcons pis pi) A = pcore_mod A pi (pseries pis A).
Proof. by rewrite /pseries rev_rcons. Qed.

Lemma pseries_subfun pis :
   GFunctor.closed (@pseries pis) /\  GFunctor.pcontinuous (@pseries pis).
Proof.
elim/last_ind: pis => [|pis pi [sFpi fFpi]].
  by split=> [gT G | gT rT D G f]; rewrite (sub1G, morphim1).
pose fF := [gFun by fFpi : GFunctor.continuous [igFun by sFpi & fFpi]].
pose F := [pgFun by fFpi : GFunctor.hereditary fF].
split=> [gT G | gT rT D G f]; rewrite !pseries_rcons ?(pcore_mod_sub F) //.
exact: (morphim_pcore_mod F).
Qed.

Lemma pseries_sub pis : GFunctor.closed (@pseries pis).
Proof. by case: (pseries_subfun pis). Qed.

Lemma morphim_pseries pis : GFunctor.pcontinuous (@pseries pis).
Proof. by case: (pseries_subfun pis). Qed.

Lemma pseriesS pis : GFunctor.hereditary (@pseries pis).
Proof. exact: (morphim_pseries pis). Qed.

Canonical pseries_igFun pis := [igFun by pseries_sub pis & morphim_pseries pis].
Canonical pseries_gFun pis := [gFun by morphim_pseries pis].
Canonical pseries_pgFun pis := [pgFun by morphim_pseries pis].

Lemma pseries_char pis gT (G : {group gT}) : pseries pis G \char G.
Proof. exact: gFchar. Qed.

Lemma pseries_normal pis gT (G : {group gT}) : pseries pis G <| G.
Proof. exact: gFnormal. Qed.

Lemma pseriesJ pis gT (G : {group gT}) x :
  pseries pis (G :^ x) = pseries pis G :^ x.
Proof.
rewrite -{1}(setIid G) -morphim_conj -(injmF _ (injm_conj G x)) //=.
by rewrite morphim_conj (setIidPr (pseries_sub _ _)).
Qed.

Lemma pseries1 pi gT (G : {group gT}) : 'O_{pi}(G) = 'O_pi(G).
Proof. exact: pcore_mod1. Qed.

Lemma pseries_pop pi pis gT (G : {group gT}) :
  'O_pi(G) = 1 -> pseries (pi :: pis) G = pseries pis G.
Proof.
by move=> OG1; rewrite /pseries rev_cons -cats1 foldr_cat /= pcore_mod1 OG1.
Qed.

Lemma pseries_pop2 pi1 pi2 gT (G : {group gT}) :
  'O_pi1(G) = 1 -> 'O_{pi1, pi2}(G) = 'O_pi2(G).
Proof. by move/pseries_pop->; apply: pseries1. Qed.

Lemma pseries_sub_catl pi1s pi2s gT (G : {group gT}) :
  pseries pi1s G \subset pseries (pi1s ++ pi2s) G.
Proof.
elim/last_ind: pi2s => [|pi pis IHpi]; rewrite ?cats0 //  -rcons_cat.
by rewrite pseries_rcons; apply: subset_trans IHpi _; rewrite sub_cosetpre.
Qed.

Lemma quotient_pseries pis pi gT (G : {group gT}) :
  pseries (rcons pis pi) G / pseries pis G = 'O_pi(G / pseries pis G).
Proof. by rewrite pseries_rcons quotient_pcore_mod. Qed.

Lemma pseries_norm2 pi1s pi2s gT (G : {group gT}) :
  pseries pi2s G \subset 'N(pseries pi1s G).
Proof. by rewrite gFsub_trans ?gFnorm. Qed.

Lemma pseries_sub_catr pi1s pi2s gT (G : {group gT}) :
  pseries pi2s G \subset pseries (pi1s ++ pi2s) G.
Proof.
elim: pi1s => //= pi1 pi1s /subset_trans; apply.
elim/last_ind: {pi1s pi2s}(_ ++ _) => [|pis pi IHpi]; first exact: sub1G.
rewrite -rcons_cons (pseries_rcons _ (pi1 :: pis)).
rewrite -sub_morphim_pre ?pseries_norm2 //.
apply: pcore_max; last by rewrite morphim_normal ?pseries_normal.
have: pi.-group (pseries (rcons pis pi) G / pseries pis G).
  by rewrite quotient_pseries pcore_pgroup.
by apply: pnat_dvd; rewrite !card_quotient ?pseries_norm2 // indexgS.
Qed.

Lemma quotient_pseries2 pi1 pi2 gT (G : {group gT}) :
  'O_{pi1, pi2}(G) / 'O_pi1(G) = 'O_pi2(G / 'O_pi1(G)).
Proof. by rewrite -pseries1 -quotient_pseries. Qed.

Lemma quotient_pseries_cat pi1s pi2s gT (G : {group gT}) :
  pseries (pi1s ++ pi2s) G / pseries pi1s G
    = pseries pi2s (G / pseries pi1s G).
Proof.
elim/last_ind: pi2s => [|pi2s pi IHpi]; first by rewrite cats0 trivg_quotient.
have psN := pseries_normal _ G; set K := pseries _ G.
case: (third_isom (pseries_sub_catl pi1s pi2s G) (psN _)) => //= f inj_f im_f.
have nH2H: pseries pi2s (G / K) <| pseries (pi1s ++ rcons pi2s pi) G / K.
  rewrite -IHpi morphim_normal // -cats1 catA.
  by apply/andP; rewrite pseries_sub_catl pseries_norm2.
apply: (quotient_inj nH2H).
  by apply/andP; rewrite /= -cats1 pseries_sub_catl pseries_norm2.
rewrite /= quotient_pseries /= -IHpi -rcons_cat.
rewrite -[G / _ / _](morphim_invm inj_f) //= {2}im_f //.
rewrite -(@injmF [igFun of @pcore pi]) /= ?injm_invm ?im_f // -quotient_pseries.
by rewrite -im_f ?morphim_invm ?morphimS ?normal_sub.
Qed.

Lemma pseries_catl_id pi1s pi2s gT (G : {group gT}) :
  pseries pi1s (pseries (pi1s ++ pi2s) G) = pseries pi1s G.
Proof.
elim/last_ind: pi1s => [//|pi1s pi IHpi] in pi2s *.
apply: (@quotient_inj _ (pseries_group pi1s G)).
- rewrite /= -(IHpi (pi :: pi2s)) cat_rcons /(_ <| _) pseries_norm2.
  by rewrite -cats1 pseries_sub_catl.
- by rewrite /= /(_ <| _) pseries_norm2 -cats1 pseries_sub_catl.
rewrite /= cat_rcons -(IHpi (pi :: pi2s)) {1}quotient_pseries IHpi.
apply/eqP; rewrite quotient_pseries eqEsubset !pcore_max ?pcore_pgroup //=.
  rewrite -quotient_pseries morphim_normal // /(_ <| _) pseries_norm2.
  by rewrite -cat_rcons pseries_sub_catl.
by rewrite gFnormal_trans ?quotient_normal ?gFnormal.
Qed.

Lemma pseries_char_catl pi1s pi2s gT (G : {group gT}) :
  pseries pi1s G \char pseries (pi1s ++ pi2s) G.
Proof. by rewrite -(pseries_catl_id pi1s pi2s G) pseries_char. Qed.

Lemma pseries_catr_id pi1s pi2s gT (G : {group gT}) :
  pseries pi2s (pseries (pi1s ++ pi2s) G) = pseries pi2s G.
Proof.
elim/last_ind: pi2s => [//|pi2s pi IHpi] in G *.
have Epis: pseries pi2s (pseries (pi1s ++ rcons pi2s pi) G) = pseries pi2s G.
  by rewrite -cats1 catA -2!IHpi pseries_catl_id.
apply: (@quotient_inj _ (pseries_group pi2s G)).
- by rewrite /= -Epis /(_ <| _) pseries_norm2 -cats1 pseries_sub_catl.
- by rewrite /= /(_ <| _) pseries_norm2 -cats1 pseries_sub_catl.
rewrite /= -Epis {1}quotient_pseries Epis quotient_pseries.
apply/eqP; rewrite eqEsubset !pcore_max ?pcore_pgroup //=.
  rewrite -quotient_pseries morphim_normal // /(_ <| _) pseries_norm2.
  by rewrite pseries_sub_catr.
by rewrite gFnormal_trans ?morphim_normal ?gFnormal.
Qed.

Lemma pseries_char_catr pi1s pi2s gT (G : {group gT}) :
  pseries pi2s G \char pseries (pi1s ++ pi2s) G.
Proof. by rewrite -(pseries_catr_id pi1s pi2s G) pseries_char. Qed.

Lemma pcore_modp pi gT (G H : {group gT}) :
  H <| G -> pi.-group H -> pcore_mod G pi H = 'O_pi(G).
Proof.
move=> nsHG piH; have nHG := normal_norm nsHG; apply/eqP.
rewrite eqEsubset andbC -sub_morphim_pre ?(gFsub_trans, morphim_pcore) //=.
rewrite -[G in 'O_pi(G)](quotientGK nsHG) pcore_max //.
  by rewrite -(pquotient_pgroup piH) ?subsetIl // cosetpreK pcore_pgroup.
by rewrite morphpre_normal ?gFnormal ?gFsub_trans ?morphim_sub.
Qed.

Lemma pquotient_pcore pi gT (G H : {group gT}) :
  H <| G -> pi.-group H -> 'O_pi(G / H) = 'O_pi(G) / H.
Proof. by move=> nsHG piH; rewrite -quotient_pcore_mod pcore_modp. Qed.

Lemma trivg_pcore_quotient pi gT (G : {group gT}) : 'O_pi(G / 'O_pi(G)) = 1.
Proof. by rewrite pquotient_pcore ?gFnormal ?pcore_pgroup ?trivg_quotient. Qed.

Lemma pseries_rcons_id pis pi gT (G : {group gT}) :
  pseries (rcons (rcons pis pi) pi) G = pseries (rcons pis pi) G.
Proof.
apply/eqP; rewrite -!cats1 eqEsubset pseries_sub_catl andbT -catA.
rewrite -(quotientSGK _ (pseries_sub_catl _ _ _)) ?pseries_norm2 //.
rewrite !quotient_pseries_cat -quotient_sub1 ?pseries_norm2 //.
by rewrite quotient_pseries_cat /= !pseries1 trivg_pcore_quotient.
Qed.

End MorphPcore.

Section EqPcore.

Variables gT : finGroupType.
Implicit Types (pi rho : nat_pred) (G H : {group gT}).

Lemma sub_in_pcore pi rho G :
  {in \pi(G), {subset pi <= rho}} -> 'O_pi(G) \subset 'O_rho(G).
Proof.
move=> pi_sub_rho; rewrite pcore_max ?pcore_normal //.
apply: sub_in_pnat (pcore_pgroup _ _) => p.
by move/(piSg (pcore_sub _ _)); apply: pi_sub_rho.
Qed.

Lemma sub_pcore pi rho G : {subset pi <= rho} -> 'O_pi(G) \subset 'O_rho(G).
Proof. by move=> pi_sub_rho; apply: sub_in_pcore (in1W pi_sub_rho). Qed.

Lemma eq_in_pcore pi rho G : {in \pi(G), pi =i rho} -> 'O_pi(G) = 'O_rho(G).
Proof.
move=> eq_pi_rho; apply/eqP; rewrite eqEsubset.
by rewrite !sub_in_pcore // => p /eq_pi_rho->.
Qed.

Lemma eq_pcore pi rho G : pi =i rho -> 'O_pi(G) = 'O_rho(G).
Proof. by move=> eq_pi_rho; apply: eq_in_pcore (in1W eq_pi_rho). Qed.

Lemma pcoreNK pi G : 'O_pi^'^'(G) = 'O_pi(G).
Proof. by apply: eq_pcore; apply: negnK. Qed.

Lemma eq_p'core pi rho G : pi =i rho -> 'O_pi^'(G) = 'O_rho^'(G).
Proof. by move/eq_negn; apply: eq_pcore. Qed.

Lemma sdprod_Hall_p'coreP pi H G :
  pi^'.-Hall(G) 'O_pi^'(G) -> reflect ('O_pi^'(G) ><| H = G) (pi.-Hall(G) H).
Proof. by rewrite -(pHallNK pi G H); apply: sdprod_Hall_pcoreP. Qed.

Lemma sdprod_p'core_HallP pi H G :
  pi.-Hall(G) H -> reflect ('O_pi^'(G) ><| H = G) (pi^'.-Hall(G) 'O_pi^'(G)).
Proof. by rewrite -(pHallNK pi G H); apply: sdprod_pcore_HallP. Qed.

Lemma pcoreI pi rho G : 'O_[predI pi & rho](G) = 'O_pi('O_rho(G)).
Proof.
apply/eqP; rewrite eqEsubset !pcore_max //.
- by rewrite /pgroup pnatI -!pgroupE !(pcore_pgroup, pgroupS (pcore_sub pi _)).
- by rewrite !gFnormal_trans.
- by apply: sub_pgroup (pcore_pgroup _ _) => p /andP[].
apply/andP; split; first by apply: sub_pcore => p /andP[].
by rewrite gFnorm_trans ?normsG ?gFsub.
Qed.

Lemma bigcap_p'core pi G :
  G :&: \bigcap_(p < #|G|.+1 | (p : nat) \in pi) 'O_p^'(G) = 'O_pi^'(G).
Proof.
apply/eqP; rewrite eqEsubset subsetI pcore_sub pcore_max /=.
- by apply/bigcapsP=> p pi_p; apply: sub_pcore => r; apply: contraNneq => ->.
- apply/pgroupP=> q q_pr qGpi'; apply: contraL (eqxx q) => /= pi_q.
  apply: (pgroupP (pcore_pgroup q^' G)) => //.
  have qG: q %| #|G| by rewrite (dvdn_trans qGpi') // cardSg ?subsetIl.
  have ltqG: q < #|G|.+1 by rewrite ltnS dvdn_leq.
  rewrite (dvdn_trans qGpi') ?cardSg ?subIset //= orbC.
  by rewrite (bigcap_inf (Ordinal ltqG)).
rewrite /normal subsetIl normsI ?normG // norms_bigcap //.
by apply/bigcapsP => p _; apply: gFnorm.
Qed.

Lemma coprime_pcoreC (rT : finGroupType) pi G (R : {group rT}) :
  coprime #|'O_pi(G)| #|'O_pi^'(R)|.
Proof. exact: pnat_coprime (pcore_pgroup _ _) (pcore_pgroup _ _). Qed.

Lemma TI_pcoreC pi G H : 'O_pi(G) :&: 'O_pi^'(H) = 1.
Proof. by rewrite coprime_TIg ?coprime_pcoreC. Qed.

Lemma pcore_setI_normal pi G H : H <| G -> 'O_pi(G) :&: H = 'O_pi(H).
Proof.
move=> nsHG; apply/eqP; rewrite eqEsubset subsetI pcore_sub setIC.
rewrite !pcore_max ?(pgroupS (subsetIr H _)) ?pcore_pgroup ?gFnormal_trans //=.
by rewrite norm_normalI ?gFnorm_trans ?normsG ?normal_sub.
Qed.

End EqPcore.

Arguments sdprod_Hall_pcoreP {pi gT H G}.
Arguments sdprod_Hall_p'coreP {gT pi H G}.

Section Injm.

Variables (aT rT : finGroupType) (D : {group aT}) (f : {morphism D >-> rT}).
Hypothesis injf : 'injm f.
Implicit Types (A : {set aT}) (G H : {group aT}).

Lemma injm_pgroup pi A : A \subset D -> pi.-group (f @* A) = pi.-group A.
Proof. by move=> sAD; rewrite /pgroup card_injm. Qed.

Lemma injm_pelt pi x : x \in D -> pi.-elt (f x) = pi.-elt x.
Proof. by move=> Dx; rewrite /p_elt order_injm. Qed.

Lemma injm_pHall pi G H :
  G \subset D -> H \subset D -> pi.-Hall(f @* G) (f @* H) = pi.-Hall(G) H.
Proof. by move=> sGD sGH; rewrite !pHallE injmSK ?card_injm. Qed.

Lemma injm_pcore pi G : G \subset D -> f @* 'O_pi(G) = 'O_pi(f @* G).
Proof. exact: injmF. Qed.

Lemma injm_pseries pis G :
  G \subset D -> f @* pseries pis G = pseries pis (f @* G).
Proof. exact: injmF. Qed.

End Injm.

Section Isog.

Variables (aT rT : finGroupType) (G : {group aT}) (H : {group rT}).

Lemma isog_pgroup pi : G \isog H -> pi.-group G = pi.-group H.
Proof. by move=> isoGH; rewrite /pgroup (card_isog isoGH). Qed.

Lemma isog_pcore pi : G \isog H -> 'O_pi(G) \isog 'O_pi(H).
Proof. exact: gFisog. Qed.

Lemma isog_pseries pis : G \isog H -> pseries pis G \isog pseries pis H.
Proof. exact: gFisog. Qed.

End Isog.

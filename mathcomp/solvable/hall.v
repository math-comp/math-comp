(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrbool ssrfun eqtype ssrnat seq div fintype finset.
From mathcomp
Require Import prime fingroup morphism automorphism quotient action gproduct.
From mathcomp
Require Import gfunctor commutator center pgroup finmodule nilpotent sylow.
From mathcomp
Require Import abelian maximal.

(*****************************************************************************)
(*  In this files we prove the Schur-Zassenhaus splitting and transitivity   *)
(* theorems (under solvability assumptions), then derive P. Hall's           *)
(* generalization of Sylow's theorem to solvable groups and its corollaries, *)
(* in particular the theory of coprime action. We develop both the theory of *)
(* coprime action of a solvable group on Sylow subgroups (as in Aschbacher   *)
(* 18.7), and that of coprime action on Hall subgroups of a solvable group   *)
(* as per B & G, Proposition 1.5; however we only support external group     *)
(* action (as opposed to internal action by conjugation) for the latter case *)
(* because it is much harder to apply in practice.                           *)
(*****************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Section Hall.

Implicit Type gT : finGroupType.

Theorem SchurZassenhaus_split gT (G H : {group gT}) :
  Hall G H -> H <| G -> [splits G, over H].
Proof.
move: {2}_.+1 (ltnSn #|G|) => n; elim: n => // n IHn in gT G H *.
rewrite ltnS => Gn hallH nsHG; have [sHG nHG] := andP nsHG.
have [-> | [p pr_p pH]] := trivgVpdiv H.
  by apply/splitsP; exists G; rewrite inE -subG1 subsetIl mul1g eqxx.
have [P sylP] := Sylow_exists p H.
case nPG: (P <| G); last first.
  pose N := ('N_G(P))%G; have sNG: N \subset G by rewrite subsetIl.
  have eqHN_G: H * N = G by apply: Frattini_arg sylP.
  pose H' := (H :&: N)%G.
  have nsH'N: H' <| N.
    by rewrite /normal subsetIr normsI ?normG ?(subset_trans sNG).
  have eq_iH: #|G : H| = #|N| %/ #|H'|.
    rewrite -divgS // -(divnMl (cardG_gt0 H')) mulnC -eqHN_G.
    by rewrite -mul_cardG (mulnC #|H'|) divnMl // cardG_gt0.
  have hallH': Hall N H'.
    rewrite /Hall -divgS subsetIr //= -eq_iH.
    by case/andP: hallH => _; apply: coprimeSg; apply: subsetIl.
  have: [splits N, over H'].
    apply: IHn hallH' nsH'N; apply: {n}leq_trans Gn.
    rewrite proper_card // properEneq sNG andbT; apply/eqP=> eqNG.
    by rewrite -eqNG normal_subnorm (subset_trans (pHall_sub sylP)) in nPG.
  case/splitsP=> K /complP[tiKN eqH'K].
  have sKN: K \subset N by rewrite -(mul1g K) -eqH'K mulSg ?sub1set.
  apply/splitsP; exists K; rewrite inE -subG1; apply/andP; split.
    by rewrite /= -(setIidPr sKN) setIA tiKN.
  by rewrite eqEsubset -eqHN_G mulgS // -eqH'K mulGS mulSg ?subsetIl.
pose Z := 'Z(P); pose Gbar := G / Z; pose Hbar := H / Z.
have sZP: Z \subset P by apply: center_sub.
have sZH: Z \subset H by apply: subset_trans (pHall_sub sylP).
have sZG: Z \subset G by apply: subset_trans sHG.
have nZG: Z <| G by apply: gFnormal_trans nPG.
have nZH: Z <| H by apply: normalS nZG.
have nHGbar: Hbar <| Gbar by apply: morphim_normal.
have hallHbar: Hall Gbar Hbar by apply: morphim_Hall (normal_norm _) _.
have: [splits Gbar, over Hbar].
  apply: IHn => //; apply: {n}leq_trans Gn; rewrite ltn_quotient //.
  apply/eqP=> /(trivg_center_pgroup (pHall_pgroup sylP))/eqP.
  rewrite trivg_card1 (card_Hall sylP) p_part -(expn0 p).
  by rewrite eqn_exp2l ?prime_gt1 // lognE pH pr_p cardG_gt0.
case/splitsP=> Kbar /complP[tiHKbar eqHKbar].
have: Kbar \subset Gbar by rewrite -eqHKbar mulG_subr.
case/inv_quotientS=> //= ZK quoZK sZZK sZKG.
have nZZK: Z <| ZK by apply: normalS nZG.
have cardZK: #|ZK| = (#|Z| * #|G : H|)%N.
  rewrite -(Lagrange sZZK); congr (_ * _)%N.
  rewrite -card_quotient -?quoZK; last by case/andP: nZZK.
  rewrite -(divgS sHG) -(Lagrange sZG) -(Lagrange sZH) divnMl //.
  rewrite -!card_quotient ?normal_norm //= -/Gbar -/Hbar.
  by rewrite -eqHKbar (TI_cardMg tiHKbar) mulKn.
have: [splits ZK, over Z].
  rewrite (Gaschutz_split nZZK _ sZZK) ?center_abelian //; last first.
    rewrite -divgS // cardZK mulKn ?cardG_gt0 //.
    by case/andP: hallH => _; apply: coprimeSg.
  by apply/splitsP; exists 1%G; rewrite inE -subG1 subsetIr mulg1 eqxx.
case/splitsP=> K /complP[tiZK eqZK].
have sKZK: K \subset ZK by rewrite -(mul1g K) -eqZK mulSg ?sub1G.
have tiHK: H :&: K = 1.
  apply/trivgP; rewrite /= -(setIidPr sKZK) setIA -tiZK setSI //.
  rewrite -quotient_sub1; last by rewrite subIset 1?normal_norm.
  by rewrite /= quotientGI //= -quoZK tiHKbar.
apply/splitsP; exists K; rewrite inE tiHK ?eqEcard subxx leqnn /=.
rewrite mul_subG ?(subset_trans sKZK) //= TI_cardMg //.
rewrite -(@mulKn #|K| #|Z|) ?cardG_gt0 // -TI_cardMg // eqZK.
by rewrite cardZK mulKn ?cardG_gt0 // Lagrange.
Qed.

Theorem SchurZassenhaus_trans_sol gT (H K K1 : {group gT}) :
    solvable H -> K \subset 'N(H) -> K1 \subset H * K ->
    coprime #|H| #|K| -> #|K1| = #|K| ->
  exists2 x, x \in H & K1 :=: K :^ x.
Proof.
move: {2}_.+1 (ltnSn #|H|) => n; elim: n => // n IHn in gT H K K1 *.
rewrite ltnS => leHn solH nHK; have [-> | ] := eqsVneq H 1.
  rewrite mul1g => sK1K _ eqK1K; exists 1; first exact: set11.
  by apply/eqP; rewrite conjsg1 eqEcard sK1K eqK1K /=.
pose G := (H <*> K)%G.
have defG: G :=: H * K by rewrite -normC // -norm_joinEl // joingC.
have sHG: H \subset G by apply: joing_subl.
have sKG: K \subset G by apply: joing_subr.
have nsHG: H <| G by rewrite /(H <| G) sHG join_subG normG.
case/(solvable_norm_abelem solH nsHG)=> M [sMH nsMG ntM] /and3P[_ abelM _].
have [sMG nMG] := andP nsMG; rewrite -defG => sK1G coHK oK1K.
have nMsG (L : {set gT}): L \subset G -> L \subset 'N(M).
  by move/subset_trans->.
have [coKM coHMK]: coprime #|M| #|K| /\ coprime #|H / M| #|K|.
  by apply/andP; rewrite -coprime_mull card_quotient ?nMsG ?Lagrange.
have oKM (K' : {group gT}): K' \subset G -> #|K'| = #|K| -> #|K' / M| = #|K|.
  move=> sK'G oK'.
  rewrite -quotientMidr -?norm_joinEl ?card_quotient ?nMsG //; last first.
    by rewrite gen_subG subUset sK'G.
  rewrite -divgS /=; last by rewrite -gen_subG genS ?subsetUr.
  by rewrite norm_joinEl ?nMsG // coprime_cardMg ?mulnK // oK' coprime_sym.
have [xb]: exists2 xb, xb \in H / M & K1 / M = (K / M) :^ xb.
  apply: IHn; try by rewrite (quotient_sol, morphim_norms, oKM K) ?(oKM K1).
    by apply: leq_trans leHn; rewrite ltn_quotient.
  by rewrite -morphimMl ?nMsG // -defG morphimS.
case/morphimP=> x nMx Hx ->{xb} eqK1Kx; pose K2 := (K :^ x)%G.
have{eqK1Kx} eqK12: K1 / M = K2 / M by rewrite quotientJ.
suff [y My ->]: exists2 y, y \in M & K1 :=: K2 :^ y.
  by exists (x * y); [rewrite groupMl // (subsetP sMH) | rewrite conjsgM].
have nMK1: K1 \subset 'N(M) by apply: nMsG.
have defMK: M * K1 = M <*> K1 by rewrite -normC // -norm_joinEl // joingC.
have sMKM: M \subset M <*> K1 by rewrite joing_subl.
have nMKM: M <| M <*> K1 by rewrite normalYl.
have trMK1: M :&: K1 = 1 by rewrite coprime_TIg ?oK1K.
have trMK2: M :&: K2 = 1 by rewrite coprime_TIg ?cardJg ?oK1K.
apply: (Gaschutz_transitive nMKM _ sMKM) => //=; last 2 first.
- by rewrite inE trMK1 defMK !eqxx.
- by rewrite -!(setIC M) trMK1.
- by rewrite -divgS //= -defMK coprime_cardMg oK1K // mulKn.
rewrite inE trMK2 eqxx eq_sym eqEcard /= -defMK andbC.
by rewrite !coprime_cardMg ?cardJg ?oK1K ?leqnn //= mulGS -quotientSK -?eqK12.
Qed.

Lemma SchurZassenhaus_trans_actsol gT (G A B : {group gT}) :
    solvable A -> A \subset 'N(G) -> B \subset A <*> G ->
    coprime #|G| #|A| -> #|A| = #|B| ->
  exists2 x, x \in G & B :=: A :^ x.
Proof.
set AG := A <*> G; move: {2}_.+1 (ltnSn #|AG|) => n.
elim: n => // n IHn in gT A B G AG *.
rewrite ltnS => leAn solA nGA sB_AG coGA oAB.
have [A1 | ntA] := eqsVneq A 1.
  by exists 1; rewrite // conjsg1 A1 (@card1_trivg _ B) // -oAB A1 cards1.
have [M [sMA nsMA ntM]] := solvable_norm_abelem solA (normal_refl A) ntA.
case/is_abelemP=> q q_pr /abelem_pgroup qM; have nMA := normal_norm nsMA.
have defAG: AG = A * G := norm_joinEl nGA.
have sA_AG: A \subset AG := joing_subl _ _.
have sG_AG: G \subset AG := joing_subr _ _.
have sM_AG := subset_trans sMA sA_AG.
have oAG: #|AG| = (#|A| * #|G|)%N by rewrite defAG coprime_cardMg 1?coprime_sym.
have q'G: #|G|`_q = 1%N.
  rewrite part_p'nat ?p'natE -?prime_coprime // coprime_sym.
  have [_ _ [k oM]] := pgroup_pdiv qM ntM.
  by rewrite -(@coprime_pexpr k.+1) // -oM (coprimegS sMA).
have coBG: coprime #|B| #|G| by rewrite -oAB coprime_sym.
have defBG: B * G = AG.
  by apply/eqP; rewrite eqEcard mul_subG ?sG_AG //= oAG oAB coprime_cardMg.
case nMG: (G \subset 'N(M)).
  have nsM_AG: M <| AG by rewrite /normal sM_AG join_subG nMA.
  have nMB: B \subset 'N(M) := subset_trans sB_AG (normal_norm nsM_AG).
  have sMB: M \subset B.
    have [Q sylQ]:= Sylow_exists q B; have sQB := pHall_sub sylQ.
    apply: subset_trans (normal_sub_max_pgroup (Hall_max _) qM nsM_AG) (sQB).
    rewrite pHallE (subset_trans sQB) //= oAG partnM // q'G muln1 oAB.
    by rewrite (card_Hall sylQ).
  have defAGq: AG / M = (A / M) <*> (G / M).
    by rewrite quotient_gen ?quotientU ?subUset ?nMA.
  have: B / M \subset (A / M) <*> (G / M) by rewrite -defAGq quotientS.
  case/IHn; rewrite ?morphim_sol ?quotient_norms ?coprime_morph //.
  - by rewrite -defAGq (leq_trans _ leAn) ?ltn_quotient.
  - by rewrite !card_quotient // -!divgS // oAB.
  move=> Mx; case/morphimP=> x Nx Gx ->{Mx} //; rewrite -quotientJ //= => defBq.
  exists x => //; apply: quotient_inj defBq; first by rewrite /normal sMB.
  by rewrite -(normsP nMG x Gx) /normal normJ !conjSg.
pose K := M <*> G; pose R := K :&: B; pose N := 'N_G(M).
have defK: K = M * G by rewrite -norm_joinEl ?(subset_trans sMA).
have oK: #|K| = (#|M| * #|G|)%N.
  by rewrite defK coprime_cardMg // coprime_sym (coprimegS sMA).
have sylM: q.-Sylow(K) M.
  by rewrite pHallE joing_subl /= oK partnM // q'G muln1 part_pnat_id.
have sylR: q.-Sylow(K) R.
  rewrite pHallE subsetIl /= -(card_Hall sylM) -(@eqn_pmul2r #|G|) // -oK.
  rewrite -coprime_cardMg ?(coprimeSg _ coBG) ?subsetIr //=.
  by rewrite group_modr ?joing_subr ?(setIidPl _) // defBG join_subG sM_AG.
have [mx] := Sylow_trans sylM sylR.
rewrite /= -/K defK; case/imset2P=> m x Mm Gx ->{mx}.
rewrite conjsgM conjGid {m Mm}// => defR.
have sNG: N \subset G := subsetIl _ _.
have pNG: N \proper G by rewrite /proper sNG subsetI subxx nMG.
have nNA: A \subset 'N(N) by rewrite normsI ?norms_norm.
have: B :^ x^-1 \subset A <*> N.
  rewrite norm_joinEl ?group_modl // -defAG subsetI !sub_conjgV -normJ -defR.
  rewrite conjGid ?(subsetP sG_AG) // normsI ?normsG // (subset_trans sB_AG) //.
  by rewrite join_subG normsM // -defK normsG ?joing_subr.
do [case/IHn; rewrite ?cardJg ?(coprimeSg _ coGA) //= -/N] => [|y Ny defB].
  rewrite joingC norm_joinEr // coprime_cardMg ?(coprimeSg sNG) //.
  by rewrite (leq_trans _ leAn) // oAG mulnC ltn_pmul2l // proper_card.
exists (y * x); first by rewrite groupM // (subsetP sNG).
by rewrite conjsgM -defB conjsgKV.
Qed.

Lemma Hall_exists_subJ pi gT (G : {group gT}) :
  solvable G -> exists2 H : {group gT}, pi.-Hall(G) H
                & forall K : {group gT}, K \subset G -> pi.-group K ->
                  exists2 x, x \in G & K \subset H :^ x.
Proof.
move: {2}_.+1 (ltnSn #|G|) => n.
elim: n gT G => // n IHn gT G; rewrite ltnS => leGn solG.
have [-> | ntG] := eqsVneq G 1.
  exists 1%G => [|_ /trivGP-> _]; last by exists 1; rewrite ?set11 ?sub1G.
  by rewrite pHallE sub1G cards1 part_p'nat.
case: (solvable_norm_abelem solG (normal_refl _)) => // M [sMG nsMG ntM].
case/is_abelemP=> p pr_p /and3P[pM cMM _].
pose Gb := (G / M)%G; case: (IHn _ Gb) => [||Hb]; try exact: quotient_sol.
  by rewrite (leq_trans (ltn_quotient _ _)).
case/and3P=> [sHbGb piHb pi'Hb'] transHb.
case: (inv_quotientS nsMG sHbGb) => H def_H sMH sHG.
have nMG := normal_norm nsMG; have nMH := subset_trans sHG nMG.
have{transHb} transH (K : {group gT}):
  K \subset G -> pi.-group K -> exists2 x, x \in G & K \subset H :^ x.
- move=> sKG piK; have nMK := subset_trans sKG nMG.
  case: (transHb (K / M)%G) => [||xb Gxb sKHxb]; first exact: morphimS.
    exact: morphim_pgroup.
  case/morphimP: Gxb => x Nx Gx /= def_x; exists x => //.
  apply/subsetP=> y Ky.
  have: y \in coset M y by rewrite val_coset (subsetP nMK, rcoset_refl).
  have: coset M y \in (H :^ x) / M.
    rewrite /quotient morphimJ //=.
    by rewrite def_x def_H in sKHxb; apply/(subsetP sKHxb)/mem_quotient.
  case/morphimP=> z Nz Hxz ->.
  rewrite val_coset //; case/rcosetP=> t Mt ->; rewrite groupMl //.
  by rewrite mem_conjg (subsetP sMH) // -mem_conjg (normP Nx).
have{pi'Hb'} pi'H': pi^'.-nat #|G : H|.
  move: pi'Hb'; rewrite -!divgS // def_H !card_quotient //.
  by rewrite -(divnMl (cardG_gt0 M)) !Lagrange.
have [pi_p | pi'p] := boolP (p \in pi).
  exists H => //; apply/and3P; split=> //; rewrite /pgroup.
  by rewrite -(Lagrange sMH) -card_quotient // pnat_mul -def_H (pi_pnat pM).
have [ltHG | leGH {n IHn leGn transH}] := ltnP #|H| #|G|.
  case: (IHn _ H (leq_trans ltHG leGn)) => [|H1]; first exact: solvableS solG.
  case/and3P=> sH1H piH1 pi'H1' transH1.
  have sH1G: H1 \subset G by apply: subset_trans sHG.
  exists H1 => [|K sKG piK].
    apply/and3P; split => //.
    rewrite -divgS // -(Lagrange sHG) -(Lagrange sH1H) -mulnA.
    by rewrite mulKn // pnat_mul pi'H1'.
  case: (transH K sKG piK) => x Gx def_K.
  case: (transH1 (K :^ x^-1)%G) => [||y Hy def_K1].
  - by rewrite sub_conjgV.
  - by rewrite /pgroup cardJg.
  exists (y * x); first by rewrite groupMr // (subsetP sHG).
  by rewrite -(conjsgKV x K) conjsgM conjSg.
have{leGH Gb sHbGb sHG sMH pi'H'} eqHG: H = G.
  by apply/eqP; rewrite -val_eqE eqEcard sHG.
have{H Hb def_H eqHG piHb nMH} hallM: pi^'.-Hall(G) M.
  rewrite /pHall /pgroup sMG pnatNK -card_quotient //=.
  by rewrite -eqHG -def_H (pi_pnat pM).
case/splitsP: (SchurZassenhaus_split (pHall_Hall hallM) nsMG) => H.
case/complP=> trMH defG.
have sHG: H \subset G by rewrite -defG mulG_subr.
exists H => [|K sKG piK].
  apply: etrans hallM; rewrite /pHall sMG sHG /= -!divgS // -defG andbC.
  by rewrite (TI_cardMg trMH) mulKn ?mulnK // pnatNK.
pose G1 := (K <*> M)%G; pose K1 := (H :&: G1)%G.
have nMK: K \subset 'N(M) by apply: subset_trans sKG nMG.
have defG1: M * K = G1 by rewrite -normC -?norm_joinEl.
have sK1G1: K1 \subset M * K by rewrite defG1 subsetIr.
have coMK: coprime #|M| #|K|.
  by rewrite coprime_sym (pnat_coprime piK) //; apply: (pHall_pgroup hallM).
case: (SchurZassenhaus_trans_sol _ nMK sK1G1 coMK) => [||x Mx defK1].
- exact: solvableS solG.
- apply/eqP; rewrite -(eqn_pmul2l (cardG_gt0 M)) -TI_cardMg //; last first.
    by apply/trivgP; rewrite -trMH /= setIA subsetIl.
  rewrite -coprime_cardMg // defG1; apply/eqP; congr #|(_ : {set _})|.
  rewrite group_modl; last by rewrite -defG1 mulG_subl.
  by apply/setIidPr; rewrite defG gen_subG subUset sKG.
exists x^-1; first by rewrite groupV (subsetP sMG).
by rewrite -(_ : K1 :^ x^-1 = K) ?(conjSg, subsetIl) // defK1 conjsgK.
Qed.

End Hall.

Section HallCorollaries.

Variable gT : finGroupType.

Corollary Hall_exists pi (G : {group gT}) :
  solvable G -> exists H : {group gT}, pi.-Hall(G) H.
Proof. by case/(Hall_exists_subJ pi) => H; exists H. Qed.

Corollary Hall_trans pi (G H1 H2 : {group gT}) :
  solvable G -> pi.-Hall(G) H1 -> pi.-Hall(G) H2 ->
  exists2 x, x \in G & H1 :=: H2 :^ x.
Proof.
move=> solG; have [H hallH transH] := Hall_exists_subJ pi solG.
have conjH (K : {group gT}):
  pi.-Hall(G) K -> exists2 x, x \in G & K = (H :^ x)%G.
- move=> hallK; have [sKG piK _] := and3P hallK.
  case: (transH K sKG piK) => x Gx sKH; exists x => //.
  apply/eqP; rewrite -val_eqE eqEcard sKH cardJg.
  by rewrite (card_Hall hallH) (card_Hall hallK) /=.
case/conjH=> x1 Gx1 ->{H1}; case/conjH=> x2 Gx2 ->{H2}.
exists (x2^-1 * x1); first by rewrite groupMl ?groupV.
by apply: val_inj; rewrite /= conjsgM conjsgK.
Qed.

Corollary Hall_superset pi (G K : {group gT}) :
  solvable G -> K \subset G -> pi.-group K ->
    exists2 H : {group gT}, pi.-Hall(G) H & K \subset H.
Proof.
move=> solG sKG; have [H hallH transH] := Hall_exists_subJ pi solG.
by case/transH=> // x Gx sKHx; exists (H :^ x)%G; rewrite ?pHallJ.
Qed.

Corollary Hall_subJ pi (G H K : {group gT}) :
    solvable G -> pi.-Hall(G) H -> K \subset G -> pi.-group K ->
  exists2 x, x \in G & K \subset H :^ x.
Proof.
move=> solG HallH sKG piK; have [M HallM sKM]:= Hall_superset solG sKG piK.
have [x Gx defM] := Hall_trans solG HallM HallH.
by exists x; rewrite // -defM.
Qed.

Corollary Hall_Jsub pi (G H K : {group gT}) :
    solvable G -> pi.-Hall(G) H -> K \subset G -> pi.-group K ->
  exists2 x, x \in G & K :^ x \subset H.
Proof.
move=> solG HallH sKG piK; have [x Gx sKHx] := Hall_subJ solG HallH sKG piK.
by exists x^-1; rewrite ?groupV // sub_conjgV.
Qed.

Lemma Hall_Frattini_arg pi (G K H : {group gT}) :
  solvable K -> K <| G -> pi.-Hall(K) H -> K * 'N_G(H) = G.
Proof.
move=> solK /andP[sKG nKG] hallH.
have sHG: H \subset G by apply: subset_trans sKG; case/andP: hallH.
rewrite setIC group_modl //; apply/setIidPr/subsetP=> x Gx.
pose H1 := (H :^ x^-1)%G.
have hallH1: pi.-Hall(K) H1 by rewrite pHallJnorm // groupV (subsetP nKG).
case: (Hall_trans solK hallH hallH1) => y Ky defH.
rewrite -(mulKVg y x) mem_mulg //; apply/normP.
by rewrite conjsgM {1}defH conjsgK conjsgKV.
Qed.

End HallCorollaries.

Section InternalAction.

Variables (pi : nat_pred) (gT : finGroupType).
Implicit Types G H K A X : {group gT}.

(* Part of Aschbacher (18.7.4). *)
Lemma coprime_norm_cent A G :
  A \subset 'N(G) -> coprime #|G| #|A| -> 'N_G(A) = 'C_G(A).
Proof.
move=> nGA coGA; apply/eqP; rewrite eqEsubset andbC setIS ?cent_sub //=.
rewrite subsetI subsetIl /= (sameP commG1P trivgP) -(coprime_TIg coGA).
rewrite subsetI commg_subr subsetIr andbT.
move: nGA; rewrite -commg_subl; apply: subset_trans.
by rewrite commSg ?subsetIl.
Qed.

(* This is B & G, Proposition 1.5(a) *)
Proposition coprime_Hall_exists A G :
    A \subset 'N(G) -> coprime #|G| #|A| -> solvable G ->
  exists2 H : {group gT}, pi.-Hall(G) H & A \subset 'N(H).
Proof.
move=> nGA coGA solG; have [H hallH] := Hall_exists pi solG.
have sG_AG: G \subset A <*> G by rewrite joing_subr.
have nG_AG: A <*> G \subset 'N(G) by rewrite join_subG nGA normG.
pose N := 'N_(A <*> G)(H)%G.
have nGN: N \subset 'N(G) by rewrite subIset ?nG_AG.
have nGN_N: G :&: N <| N by rewrite /(_ <| N) subsetIr normsI ?normG.
have NG_AG: G * N = A <*> G.
  by apply: Hall_Frattini_arg hallH => //; apply/andP.
have iGN_A: #|N| %/ #|G :&: N| = #|A|.
  rewrite setIC divgI -card_quotient // -quotientMidl NG_AG.
  rewrite card_quotient -?divgS //= norm_joinEl //.
  by rewrite coprime_cardMg 1?coprime_sym // mulnK.
have hallGN: Hall N (G :&: N).
  by rewrite /Hall -divgS subsetIr //= iGN_A (coprimeSg _ coGA) ?subsetIl.
case/splitsP: {hallGN nGN_N}(SchurZassenhaus_split hallGN nGN_N) => B.
case/complP=> trBGN defN.
have{trBGN iGN_A} oBA: #|B| = #|A|.
  by rewrite -iGN_A -{1}defN (TI_cardMg trBGN) mulKn.
have sBN: B \subset N by rewrite -defN mulG_subr.
case: (SchurZassenhaus_trans_sol solG nGA _ coGA oBA) => [|x Gx defB].
  by rewrite -(normC nGA) -norm_joinEl // -NG_AG -(mul1g B) mulgSS ?sub1G.
exists (H :^ x^-1)%G; first by rewrite pHallJ ?groupV.
apply/subsetP=> y Ay; have: y ^ x \in B by rewrite defB memJ_conjg.
move/(subsetP sBN)=> /setIP[_ /normP nHyx].
by apply/normP; rewrite -conjsgM conjgCV invgK conjsgM nHyx.
Qed.

(* This is B & G, Proposition 1.5(c) *)
Proposition coprime_Hall_trans A G H1 H2 :
    A \subset 'N(G) -> coprime #|G| #|A| -> solvable G ->
    pi.-Hall(G) H1 -> A \subset 'N(H1) ->
    pi.-Hall(G) H2 -> A \subset 'N(H2) ->
  exists2 x, x \in 'C_G(A) & H1 :=: H2 :^ x.
Proof.
move: H1 => H nGA coGA solG hallH nHA hallH2.
have{H2 hallH2} [x Gx -> nH1xA] := Hall_trans solG hallH2 hallH.
have sG_AG: G \subset A <*> G by rewrite -{1}genGid genS ?subsetUr.
have nG_AG: A <*> G \subset 'N(G) by rewrite gen_subG subUset nGA normG.
pose N := 'N_(A <*> G)(H)%G.
have nGN: N \subset 'N(G) by rewrite subIset ?nG_AG.
have nGN_N: G :&: N <| N.
  apply/normalP; rewrite subsetIr; split=> // y Ny.
  by rewrite conjIg (normP _) // (subsetP nGN, conjGid).
have NG_AG : G * N = A <*> G.
  by apply: Hall_Frattini_arg hallH => //; apply/andP.
have iGN_A: #|N : G :&: N| = #|A|.
  rewrite -card_quotient //; last by case/andP: nGN_N.
  rewrite (card_isog (second_isog nGN)) /= -quotientMidr (normC nGN) NG_AG.
  rewrite card_quotient // -divgS //= joingC norm_joinEr //.
  by rewrite coprime_cardMg // mulnC mulnK.
have solGN: solvable (G :&: N) by apply: solvableS solG; apply: subsetIl.
have oAxA: #|A :^ x^-1| = #|A| by apply: cardJg.
have sAN: A \subset N by rewrite subsetI -{1}genGid genS // subsetUl.
have nGNA: A \subset 'N(G :&: N).
  by apply/normsP=> y ?; rewrite conjIg (normsP nGA) ?(conjGid, subsetP sAN).
have coGNA: coprime #|G :&: N| #|A| := coprimeSg (subsetIl _ _) coGA.
case: (SchurZassenhaus_trans_sol solGN nGNA _ coGNA oAxA) => [|y GNy defAx].
  have ->: (G :&: N) * A = N.
    apply/eqP; rewrite eqEcard -{2}(mulGid N) mulgSS ?subsetIr //=.
    by rewrite coprime_cardMg // -iGN_A Lagrange ?subsetIr.
  rewrite sub_conjgV conjIg -normJ subsetI conjGid ?joing_subl //.
  by rewrite mem_gen // inE Gx orbT.
case/setIP: GNy => Gy; case/setIP=> _; move/normP=> nHy.
exists (y * x)^-1.
  rewrite -coprime_norm_cent // groupV inE groupM //=; apply/normP.
  by rewrite conjsgM -defAx conjsgKV.
by apply: val_inj; rewrite /= -{2}nHy -(conjsgM _ y) conjsgK.
Qed.

(* A complement to the above: 'C(A) acts on 'Nby(A) *)
Lemma norm_conj_cent A G x : x \in 'C(A) ->
  (A \subset 'N(G :^ x)) = (A \subset 'N(G)).
Proof. by move=> cAx; rewrite norm_conj_norm ?(subsetP (cent_sub A)). Qed.

(* Strongest version of the centraliser lemma -- not found in textbooks!  *)
(* Obviously, the solvability condition could be removed once we have the *)
(* Odd Order Theorem.                                                     *)
Lemma strongest_coprime_quotient_cent A G H :
      let R := H :&: [~: G, A] in
      A \subset 'N(H) -> R \subset G -> coprime #|R| #|A| ->
      solvable R || solvable A ->
  'C_G(A) / H = 'C_(G / H)(A / H).
Proof.
move=> R nHA sRG coRA solRA.
have nRA: A \subset 'N(R) by rewrite normsI ?commg_normr.
apply/eqP; rewrite eqEsubset subsetI morphimS ?subsetIl //=.
rewrite (subset_trans _ (morphim_cent _ _)) ?morphimS ?subsetIr //=.
apply/subsetP=> _ /setIP[/morphimP[x Nx Gx ->] cAHx].
have{cAHx} cAxR y: y \in A -> [~ x, y] \in R.
  move=> Ay; have Ny: y \in 'N(H) by apply: subsetP Ay.
  rewrite inE mem_commg // andbT coset_idr ?groupR // morphR //=.
  by apply/eqP; apply/commgP; apply: (centP cAHx); rewrite mem_quotient.
have AxRA: A :^ x \subset R * A.
  apply/subsetP=> _ /imsetP[y Ay ->].
  rewrite -normC // -(mulKVg y (y ^ x)) -commgEl mem_mulg //.
  by rewrite -groupV invg_comm cAxR.
have [y Ry def_Ax]: exists2 y, y \in R & A :^ x = A :^ y.
  have oAx: #|A :^ x| = #|A| by rewrite cardJg.
  have [solR | solA] := orP solRA; first exact: SchurZassenhaus_trans_sol.
  by apply: SchurZassenhaus_trans_actsol; rewrite // joingC norm_joinEr.
rewrite -imset_coset; apply/imsetP; exists (x * y^-1); last first.
  by rewrite conjgCV mkerl // ker_coset memJ_norm groupV; case/setIP: Ry.
rewrite /= inE groupMl // ?(groupV, subsetP sRG) //=.
apply/centP=> z Az; apply/commgP/eqP/set1P.
rewrite -[[set 1]](coprime_TIg coRA) inE {1}commgEl commgEr /= -/R.
rewrite invMg -mulgA invgK groupMl // conjMg mulgA -commgEl.
rewrite groupMl ?cAxR // memJ_norm ?(groupV, subsetP nRA) // Ry /=.
by rewrite groupMr // conjVg groupV conjgM -mem_conjg -def_Ax memJ_conjg.
Qed.

(* A weaker but more practical version, still stronger than the usual form *)
(* (viz. Aschbacher 18.7.4), similar to the one needed in Aschbacher's     *)
(* proof of Thompson factorization. Note that the coprime and solvability  *)
(* assumptions could be further weakened to H :&: G (and hence become      *)
(* trivial if H and G are TI). However, the assumption that A act on G is  *)
(* needed in this case.                                                    *)
Lemma coprime_norm_quotient_cent A G H :
    A \subset 'N(G) -> A \subset 'N(H) -> coprime #|H| #|A| -> solvable H ->
  'C_G(A) / H = 'C_(G / H)(A / H).
Proof.
move=> nGA nHA coHA solH; have sRH := subsetIl H [~: G, A].
rewrite strongest_coprime_quotient_cent ?(coprimeSg sRH) 1?(solvableS sRH) //.
by rewrite subIset // commg_subl nGA orbT.
Qed.

(* A useful consequence (similar to Ex. 6.1 in Aschbacher) of the stronger   *)
(* theorem. *)
Lemma coprime_cent_mulG A G H :
     A \subset 'N(G) -> A \subset 'N(H) -> G \subset 'N(H) ->
     coprime #|H| #|A| -> solvable H ->
  'C_(H * G)(A) = 'C_H(A) * 'C_G(A).
Proof.
move=> nHA nGA nHG coHA solH; rewrite -norm_joinEr //.
have nsHG: H <| H <*> G by rewrite /normal joing_subl join_subG normG.
rewrite -{2}(setIidPr (normal_sub nsHG)) setIAC.
rewrite group_modr ?setSI ?joing_subr //=; symmetry; apply/setIidPl.
rewrite -quotientSK ?subIset 1?normal_norm //.
by rewrite !coprime_norm_quotient_cent ?normsY //= norm_joinEr ?quotientMidl.
Qed.

(* Another special case of the strong coprime quotient lemma; not found in    *)
(* textbooks, but nevertheless used implicitly throughout B & G, sometimes    *)
(* justified by switching to external action.                                 *)
Lemma quotient_TI_subcent K G H :
    G \subset 'N(K) -> G \subset 'N(H) -> K :&: H = 1 ->
  'C_K(G) / H = 'C_(K / H)(G / H).
Proof.
move=> nGK nGH tiKH.
have tiHR: H :&: [~: K, G] = 1.
  by apply/trivgP; rewrite /= setIC -tiKH setSI ?commg_subl.
apply: strongest_coprime_quotient_cent; rewrite ?tiHR ?sub1G ?solvable1 //.
by rewrite cards1 coprime1n.
Qed.

(* This is B & G, Proposition 1.5(d): the more traditional form of the lemma *)
(* above, with the assumption H <| G weakened to H \subset G. The stronger   *)
(* coprime and solvability assumptions are easier to satisfy in practice.    *)
Proposition coprime_quotient_cent A G H :
    H \subset G -> A \subset 'N(H) -> coprime #|G| #|A| -> solvable G ->
  'C_G(A) / H = 'C_(G / H)(A / H).
Proof.
move=> sHG nHA coGA solG.
have sRG: H :&: [~: G, A] \subset G by rewrite subIset ?sHG.
by rewrite strongest_coprime_quotient_cent ?(coprimeSg sRG) 1?(solvableS sRG).
Qed.

(* This is B & G, Proposition 1.5(e). *)
Proposition coprime_comm_pcore A G K :
    A \subset 'N(G) -> coprime #|G| #|A| -> solvable G ->
    pi^'.-Hall(G) K -> K \subset 'C_G(A) ->
  [~: G, A] \subset 'O_pi(G).
Proof.
move=> nGA coGA solG hallK cKA.
case: (coprime_Hall_exists nGA) => // H hallH nHA.
have sHG: H \subset G by case/andP: hallH.
have sKG: K \subset G by case/andP: hallK.
have coKH: coprime #|K| #|H|.
  case/and3P: hallH=> _ piH _; case/and3P: hallK => _ pi'K _.
  by rewrite coprime_sym (pnat_coprime piH pi'K).
have defG: G :=: K * H.
  apply/eqP; rewrite eq_sym eqEcard coprime_cardMg //.
  rewrite -{1}(mulGid G) mulgSS //= (card_Hall hallH) (card_Hall hallK).
  by rewrite mulnC partnC.
have sGA_H: [~: G, A] \subset H.
  rewrite gen_subG defG.
  apply/subsetP=> _ /imset2P[_ a /imset2P[x y Kx Hy ->] Aa ->].
  rewrite commMgJ (([~ x, a] =P 1) _) ?(conj1g, mul1g).
    by rewrite groupMl ?groupV // memJ_norm ?(subsetP nHA).
  by rewrite subsetI sKG in cKA; apply/commgP/(centsP cKA).
apply: pcore_max; last first.
  by rewrite /(_ <| G) /=  commg_norml commGC commg_subr nGA.
by case/and3P: hallH => _ piH _; apply: pgroupS piH.
Qed.

End InternalAction.

(* This is B & G, Proposition 1.5(b). *)
Proposition coprime_Hall_subset pi (gT : finGroupType) (A G X : {group gT}) :
    A \subset 'N(G) -> coprime #|G| #|A| -> solvable G ->
    X \subset G -> pi.-group X -> A \subset 'N(X) ->
  exists H : {group gT}, [/\ pi.-Hall(G) H, A \subset 'N(H) & X \subset H].
Proof.
move: {2}_.+1 (ltnSn #|G|) => n.
elim: n => // n IHn in gT A G X * => leGn nGA coGA solG sXG piX nXA.
have [G1 | ntG] := eqsVneq G 1.
  case: (coprime_Hall_exists pi nGA) => // H hallH nHA.
  by exists H; split; rewrite // (subset_trans sXG) // G1 sub1G.
have sG_AG: G \subset A <*> G by rewrite joing_subr.
have sA_AG: A \subset A <*> G by rewrite joing_subl.
have nG_AG: A <*> G \subset 'N(G) by rewrite join_subG nGA normG.
have nsG_AG: G <| A <*> G by apply/andP.
case: (solvable_norm_abelem solG nsG_AG) => // M [sMG nsMAG ntM].
have{nsMAG} [nMA nMG]: A \subset 'N(M) /\ G \subset 'N(M).
  by apply/andP; rewrite -join_subG normal_norm.
have nMX: X \subset 'N(M) by apply: subset_trans nMG.
case/is_abelemP=> p pr_p; case/and3P=> pM cMM _.
have: #|G / M| < n by rewrite (leq_trans (ltn_quotient _ _)).
move/(IHn _ (A / M)%G _ (X / M)%G); rewrite !(quotient_norms, quotientS) //.
rewrite !(coprime_morph, quotient_sol, morphim_pgroup) //.
case=> //= Hq []; case/and3P=> sHGq piHq pi'Hq' nHAq sXHq.
case/inv_quotientS: (sHGq) => [|HM defHM sMHM sHMG]; first exact/andP.
have nMHM := subset_trans sHMG nMG.
have{sXHq} sXHM: X \subset HM by rewrite -(quotientSGK nMX) -?defHM.
have{pi'Hq' sHGq} pi'HM': pi^'.-nat #|G : HM|.
  move: pi'Hq'; rewrite -!divgS // defHM !card_quotient //.
  by rewrite -(divnMl (cardG_gt0 M)) !Lagrange.
have{nHAq} nHMA: A \subset 'N(HM).
  by rewrite -(quotientSGK nMA) ?normsG ?quotient_normG -?defHM //; apply/andP.
case/orP: (orbN (p \in pi)) => pi_p.
  exists HM; split=> //; apply/and3P; split; rewrite /pgroup //.
  by rewrite -(Lagrange sMHM) pnat_mul -card_quotient // -defHM (pi_pnat pM).
case: (ltnP #|HM| #|G|) => [ltHG | leGHM {n IHn leGn}].
  case: (IHn _ A HM X (leq_trans ltHG leGn)) => // [||H [hallH nHA sXH]].
  - exact: coprimeSg coGA.
  - exact: solvableS solG.
  case/and3P: hallH => sHHM piH pi'H'.
  have sHG: H \subset G by apply: subset_trans sHMG.
  exists H; split=> //; apply/and3P; split=> //.
  rewrite -divgS // -(Lagrange sHMG) -(Lagrange sHHM) -mulnA mulKn //.
  by rewrite pnat_mul pi'H'.
have{leGHM nHMA sHMG sMHM sXHM pi'HM'} eqHMG: HM = G.
  by apply/eqP; rewrite -val_eqE eqEcard sHMG.
have pi'M: pi^'.-group M by rewrite /pgroup (pi_pnat pM).
have{HM Hq nMHM defHM eqHMG piHq} hallM: pi^'.-Hall(G) M.
  apply/and3P; split; rewrite // /pgroup pnatNK.
  by rewrite -card_quotient // -eqHMG -defHM.
case: (coprime_Hall_exists pi nGA) => // H hallH nHA.
pose XM := (X <*> M)%G; pose Y := (H :&: XM)%G.
case/and3P: (hallH) => sHG piH _.
have sXXM: X \subset XM by rewrite joing_subl.
have co_pi_M (B : {group gT}): pi.-group B -> coprime #|B| #|M|.
  by move=> piB; rewrite (pnat_coprime piB).
have hallX: pi.-Hall(XM) X.
  rewrite /pHall piX sXXM -divgS //= norm_joinEl //.
  by rewrite coprime_cardMg ?co_pi_M // mulKn.
have sXMG: XM \subset G by rewrite join_subG sXG.
have hallY: pi.-Hall(XM) Y.
  have sYXM: Y \subset XM by rewrite subsetIr.
  have piY: pi.-group Y by apply: pgroupS piH; apply: subsetIl.
  rewrite /pHall sYXM piY -divgS // -(_ : Y * M = XM).
    by rewrite coprime_cardMg ?co_pi_M // mulKn //.
  rewrite /= setIC group_modr ?joing_subr //=; apply/setIidPl.
  rewrite ((H * M =P G) _) // eqEcard mul_subG //= coprime_cardMg ?co_pi_M //.
  by rewrite (card_Hall hallM) (card_Hall hallH) partnC.
have nXMA: A \subset 'N(XM) by rewrite normsY.
have:= coprime_Hall_trans nXMA _ _ hallX nXA hallY.
rewrite !(coprimeSg sXMG, solvableS sXMG, normsI) //.
case=> // x /setIP[XMx cAx] ->.
exists (H :^ x)%G; split; first by rewrite pHallJ ?(subsetP sXMG).
  by rewrite norm_conj_cent.
by rewrite conjSg subsetIl.
Qed.

Section ExternalAction.

Variables (pi : nat_pred) (aT gT : finGroupType).
Variables (A : {group aT}) (G : {group gT}) (to : groupAction A G).

Section FullExtension.

Local Notation inA := (sdpair2 to).
Local Notation inG := (sdpair1 to).
Local Notation A' := (inA @* gval A).
Local Notation G' := (inG @* gval G).
Let injG : 'injm inG := injm_sdpair1 _.
Let injA : 'injm inA := injm_sdpair2 _.

Hypotheses (coGA : coprime #|G| #|A|) (solG : solvable G).

Lemma external_action_im_coprime : coprime #|G'| #|A'|.
Proof. by rewrite !card_injm. Qed.

Let coGA' := external_action_im_coprime.

Let solG' : solvable G' := morphim_sol _ solG.

Let nGA' := im_sdpair_norm to.

Lemma ext_coprime_Hall_exists :
  exists2 H : {group gT}, pi.-Hall(G) H & [acts A, on H | to].
Proof.
have [H' hallH' nHA'] := coprime_Hall_exists pi nGA' coGA' solG'.
have sHG' := pHall_sub hallH'.
exists (inG @*^-1 H')%G => /=.
  by rewrite -(morphim_invmE injG) -{1}(im_invm injG) morphim_pHall.
by rewrite actsEsd ?morphpreK // subsetIl.
Qed.

Lemma ext_coprime_Hall_trans (H1 H2 : {group gT}) :
    pi.-Hall(G) H1 -> [acts A, on H1 | to] ->
    pi.-Hall(G) H2 -> [acts A, on H2 | to] ->
  exists2 x, x \in 'C_(G | to)(A) & H1 :=: H2 :^ x.
Proof.
move=> hallH1 nH1A hallH2 nH2A.
have sH1G := pHall_sub hallH1; have sH2G := pHall_sub hallH2.
rewrite !actsEsd // in nH1A nH2A.
have hallH1': pi.-Hall(G') (inG @* H1) by rewrite morphim_pHall.
have hallH2': pi.-Hall(G') (inG @* H2) by rewrite morphim_pHall.
have [x'] := coprime_Hall_trans nGA' coGA' solG' hallH1' nH1A hallH2' nH2A.
case/setIP=> /= Gx' cAx' /eqP defH1; pose x := invm injG x'.
have Gx: x \in G by rewrite -(im_invm injG) mem_morphim.
have def_x': x' = inG x by rewrite invmK.
exists x; first by rewrite inE Gx gacentEsd mem_morphpre /= -?def_x'.
apply/eqP; move: defH1; rewrite def_x' /= -morphimJ //=.
by rewrite !eqEsubset !injmSK // conj_subG.
Qed.

Lemma ext_norm_conj_cent (H : {group gT}) x :
    H \subset G -> x \in 'C_(G | to)(A) ->
  [acts A, on H :^ x | to] = [acts A, on H | to].
Proof.
move=> sHG /setIP[Gx].
rewrite gacentEsd !actsEsd ?conj_subG ?morphimJ // 2!inE Gx /=.
exact: norm_conj_cent.
Qed.

Lemma ext_coprime_Hall_subset (X : {group gT}) :
    X \subset G -> pi.-group X -> [acts A, on X | to] ->
  exists H : {group gT},
    [/\ pi.-Hall(G) H, [acts A, on H | to] & X \subset H].
Proof.
move=> sXG piX; rewrite actsEsd // => nXA'.
case: (coprime_Hall_subset nGA' coGA' solG' _ (morphim_pgroup _ piX) nXA').
  exact: morphimS.
move=> H' /= [piH' nHA' sXH']; have sHG' := pHall_sub piH'.
exists (inG @*^-1 H')%G; rewrite actsEsd ?subsetIl ?morphpreK // nHA'.
rewrite -sub_morphim_pre //= sXH'; split=> //.
by rewrite -(morphim_invmE injG) -{1}(im_invm injG) morphim_pHall.
Qed.

End FullExtension.

(* We only prove a weaker form of the coprime group action centraliser  *)
(* lemma, because it is more convenient in practice to make G the range *)
(* of the action, whence G both contains H and is stable under A.       *)
(*   However we do restrict the coprime/solvable assumptions to H, and  *)
(* we do not require that G normalize H.                                *)
Lemma ext_coprime_quotient_cent (H : {group gT}) :
    H \subset G -> [acts A, on H | to] -> coprime #|H| #|A| -> solvable H ->
 'C_(|to)(A) / H = 'C_(|to / H)(A).
Proof.
move=> sHG nHA coHA solH; pose N := 'N_G(H).
have nsHN: H <| N by rewrite normal_subnorm.
have [sHN nHn] := andP nsHN.
have sNG: N \subset G by apply: subsetIl.
have nNA: {acts A, on group N | to}.
  split; rewrite // actsEsd // injm_subnorm ?injm_sdpair1 //=.
  by rewrite normsI ?norms_norm ?im_sdpair_norm -?actsEsd.
rewrite -!(gacentIdom _ A) -quotientInorm -gacentIim setIAC.
rewrite -(gacent_actby nNA) gacentEsd -morphpreIim /= -/N.
have:= (injm_sdpair1 <[nNA]>, injm_sdpair2 <[nNA]>).
set inG := sdpair1 _; set inA := sdpair2 _ => [[injG injA]].
set G' := inG @* N; set A' := inA @* A; pose H' := inG @* H.
have defN: 'N(H | to) = A by apply/eqP; rewrite eqEsubset subsetIl.
have def_Dq: qact_dom to H = A by rewrite qact_domE.
have sAq: A \subset qact_dom to H by rewrite def_Dq.
rewrite {2}def_Dq -(gacent_ract _ sAq); set to_q := (_ \ _)%gact.
have:= And3 (sdprod_sdpair to_q) (injm_sdpair1 to_q) (injm_sdpair2 to_q).
rewrite gacentEsd; set inAq := sdpair2 _; set inGq := sdpair1 _ => /=.
set Gq := inGq @* _; set Aq := inAq @* _ => [[q_d iGq iAq]].
have nH': 'N(H') = setT.
  apply/eqP; rewrite -subTset -im_sdpair mulG_subG morphim_norms //=.
  by rewrite -actsEsd // acts_actby subxx /= (setIidPr sHN).
have: 'dom (coset H' \o inA \o invm iAq) = Aq.
  by rewrite ['dom _]morphpre_invm /= nH' morphpreT.
case/domP=> qA [def_qA ker_qA _ im_qA].
have{coHA} coHA': coprime #|H'| #|A'| by rewrite !card_injm.
have{ker_qA} injAq: 'injm qA.
  rewrite {}ker_qA !ker_comp ker_coset morphpre_invm -morphpreIim /= setIC.
  by rewrite coprime_TIg // -kerE (trivgP injA) morphim1.
have{im_qA} im_Aq : qA @* Aq = A' / H'.
  by rewrite {}im_qA !morphim_comp im_invm.
have: 'dom (quotm (sdpair1_morphism <[nNA]>) nsHN \o invm iGq) = Gq.
  by rewrite ['dom _]morphpre_invm /= quotientInorm.
case/domP=> qG [def_qG ker_qG _ im_qG].
have{ker_qG} injGq: 'injm qG.
  rewrite {}ker_qG ker_comp ker_quotm morphpre_invm (trivgP injG).
  by rewrite quotient1 morphim1.
have im_Gq: qG @* Gq = G' / H'.
  rewrite {}im_qG morphim_comp im_invm morphim_quotm //= -/inG -/H'.
  by rewrite -morphimIdom setIAC setIid.
have{def_qA def_qG} q_J : {in Gq & Aq, morph_act 'J 'J qG qA}.
  move=> x' a'; case/morphimP=> Hx; case/morphimP=> x nHx Gx -> GHx ->{Hx x'}.
  case/morphimP=> a _ Aa ->{a'} /=; rewrite -/inAq -/inGq.
  rewrite !{}def_qG {}def_qA /= !invmE // -sdpair_act //= -/inG -/inA.
  have Nx: x \in N by rewrite inE Gx.
  have Nxa: to x a \in N by case: (nNA); move/acts_act->.
  have [Gxa nHxa] := setIP Nxa.
  rewrite invmE qactE ?quotmE ?mem_morphim ?def_Dq //=.
  by rewrite -morphJ /= ?nH' ?inE // -sdpair_act //= actbyE.
pose q := sdprodm q_d q_J.
have{injAq injGq} injq: 'injm q.
  rewrite injm_sdprodm injAq injGq /= {}im_Aq {}im_Gq -/Aq .
  by rewrite -quotientGI ?im_sdpair_TI ?morphimS //= quotient1.
rewrite -[inGq @*^-1 _]morphpreIim -/Gq.
have sC'G: inG @*^-1 'C_G'(A') \subset G by rewrite !subIset ?subxx.
rewrite -[_ / _](injmK iGq) ?quotientS //= -/inGq; congr (_ @*^-1 _).
apply: (injm_morphim_inj injq); rewrite 1?injm_subcent ?subsetT //= -/q.
rewrite 2?morphim_sdprodml ?morphimS //= im_Gq.
rewrite morphim_sdprodmr ?morphimS //= im_Aq.
rewrite {}im_qG morphim_comp morphim_invm ?morphimS //.
rewrite morphim_quotm morphpreK ?subsetIl //= -/H'.
rewrite coprime_norm_quotient_cent ?im_sdpair_norm ?nH' ?subsetT //=.
exact: morphim_sol.
Qed.

End ExternalAction.

Section SylowSolvableAct.

Variables (gT : finGroupType) (p : nat).
Implicit Types A B G X : {group gT}.

Lemma sol_coprime_Sylow_exists A G :
    solvable A -> A \subset 'N(G) -> coprime #|G| #|A| ->
  exists2 P : {group gT}, p.-Sylow(G) P & A \subset 'N(P).
Proof.
move=> solA nGA coGA; pose AG := A <*> G.
have nsG_AG: G <| AG by rewrite /normal joing_subr join_subG nGA normG.
have [sG_AG nG_AG]:= andP nsG_AG.
have [P sylP] := Sylow_exists p G; pose N := 'N_AG(P); pose NG := G :&: N.
have nGN: N \subset 'N(G) by rewrite subIset ?nG_AG.
have sNG_G: NG \subset G := subsetIl G N.
have nsNG_N: NG <| N by rewrite /normal subsetIr normsI ?normG.
have defAG: G * N = AG := Frattini_arg nsG_AG sylP.
have oA : #|A| = #|N| %/ #|NG|.
  rewrite /NG setIC divgI -card_quotient // -quotientMidl defAG.
  rewrite card_quotient -?divgS //= norm_joinEl //.
  by rewrite coprime_cardMg 1?coprime_sym // mulnK.
have: [splits N, over NG].
  rewrite SchurZassenhaus_split // /Hall -divgS subsetIr //.
  by rewrite -oA (coprimeSg sNG_G).
case/splitsP=> B; case/complP=> tNG_B defN.
have [nPB]: B \subset 'N(P) /\ B \subset AG.
  by apply/andP; rewrite andbC -subsetI -/N -defN mulG_subr.
case/SchurZassenhaus_trans_actsol => // [|x Gx defB].
  by rewrite oA -defN TI_cardMg // mulKn.
exists (P :^ x^-1)%G; first by rewrite pHallJ ?groupV.
by rewrite normJ -sub_conjg -defB.
Qed.

Lemma sol_coprime_Sylow_trans A G :
    solvable A -> A \subset 'N(G) -> coprime #|G| #|A| ->
  [transitive 'C_G(A), on [set P in 'Syl_p(G) | A \subset 'N(P)] | 'JG].
Proof.
move=> solA nGA coGA; pose AG := A <*> G; set FpA := finset _.
have nG_AG: AG \subset 'N(G) by rewrite join_subG nGA normG.
have [P sylP nPA] := sol_coprime_Sylow_exists solA nGA coGA.
pose N := 'N_AG(P); have sAN: A \subset N by rewrite subsetI joing_subl.
have trNPA: A :^: AG ::&: N = A :^: N.
  pose NG := 'N_G(P); have sNG_G : NG \subset G := subsetIl _ _.
  have nNGA: A \subset 'N(NG) by rewrite normsI ?norms_norm.
  apply/setP=> Ax; apply/setIdP/imsetP=> [[]|[x Nx ->{Ax}]]; last first.
    by rewrite conj_subG //; case/setIP: Nx => AGx; rewrite mem_imset.
  have ->: N = A <*> NG by rewrite /N /AG !norm_joinEl // -group_modl.
  have coNG_A := coprimeSg sNG_G coGA; case/imsetP=> x AGx ->{Ax}.
  case/SchurZassenhaus_trans_actsol; rewrite ?cardJg // => y Ny /= ->.
  by exists y; rewrite // mem_gen 1?inE ?Ny ?orbT.
have{trNPA}: [transitive 'N_AG(A), on FpA | 'JG].
  have ->: FpA = 'Fix_('Syl_p(G) | 'JG)(A).
    by apply/setP=> Q; rewrite 4!inE afixJG.
  have SylP : P \in 'Syl_p(G) by rewrite inE.
  apply/(trans_subnorm_fixP _ SylP); rewrite ?astab1JG //.
  rewrite (atrans_supgroup _ (Syl_trans _ _)) ?joing_subr //= -/AG.
  by apply/actsP=> x /= AGx Q /=; rewrite !inE -{1}(normsP nG_AG x) ?pHallJ2.
rewrite {1}/AG norm_joinEl // -group_modl ?normG ?coprime_norm_cent //=.
rewrite -cent_joinEr ?subsetIr // => trC_FpA.
have FpA_P: P \in FpA by rewrite !inE sylP.
apply/(subgroup_transitiveP FpA_P _ trC_FpA); rewrite ?joing_subr //=.
rewrite astab1JG cent_joinEr ?subsetIr // -group_modl // -mulgA.
by congr (_ * _); rewrite mulSGid ?subsetIl.
Qed.

Lemma sol_coprime_Sylow_subset A G X :
  A \subset 'N(G) -> coprime #|G| #|A| -> solvable A ->
  X \subset G -> p.-group X -> A \subset 'N(X) ->
  exists P : {group gT}, [/\ p.-Sylow(G) P, A \subset 'N(P) & X \subset P].
Proof.
move=> nGA coGA solA sXG pX nXA.
pose nAp (Q : {group gT}) := [&& p.-group Q, Q \subset G & A \subset 'N(Q)].
have: nAp X by apply/and3P.
case/maxgroup_exists=> R; case/maxgroupP; case/and3P=> pR sRG nRA maxR sXR.
have [P sylP sRP]:= Sylow_superset sRG pR.
suffices defP: P :=: R by exists P; rewrite sylP defP.
case/and3P: sylP => sPG pP _; apply: (nilpotent_sub_norm (pgroup_nil pP)) => //.
pose N := 'N_G(R); have{sPG} sPN_N: 'N_P(R) \subset N by apply: setSI.
apply: norm_sub_max_pgroup (pgroupS (subsetIl _ _) pP) sPN_N (subsetIr _ _).
have nNA: A \subset 'N(N) by rewrite normsI ?norms_norm.
have coNA: coprime #|N| #|A| by apply: coprimeSg coGA; rewrite subsetIl.
have{solA coNA} [Q sylQ nQA] := sol_coprime_Sylow_exists solA nNA coNA.
suffices defQ: Q :=: R by rewrite max_pgroup_Sylow -{2}defQ.
apply: maxR; first by apply/and3P; case/and3P: sylQ; rewrite subsetI; case/andP.
by apply: normal_sub_max_pgroup (Hall_max sylQ) pR _; rewrite normal_subnorm.
Qed.

End SylowSolvableAct.

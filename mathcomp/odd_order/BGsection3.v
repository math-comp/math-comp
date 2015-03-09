(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div.
Require Import fintype tuple bigop prime binomial finset ssralg fingroup finalg.
Require Import morphism perm automorphism quotient action commutator gproduct.
Require Import zmodp cyclic gfunctor center pgroup gseries nilpotent sylow.
Require Import finmodule abelian frobenius maximal extremal hall.
Require Import matrix mxalgebra mxrepresentation mxabelem wielandt_fixpoint.
Require Import BGsection1 BGsection2.

(******************************************************************************)
(*   This file covers the material in B & G, Section 3.                       *)
(*   Note that in spite of the use of Gorenstein 2.7.6, the material in all   *)
(* of Section 3, and in all likelyhood the whole of B & G, does NOT depend on *)
(* the general proof of existence of Frobenius kernels, because results on    *)
(* Frobenius groups are only used when the semidirect product decomposition   *)
(* is already known, and (see file frobenius.v) in this case the kernel is    *)
(* equal to the normal complement of the Frobenius complement.                *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GroupScope GRing.Theory.

Section BGsection3.

Implicit Type F : fieldType.
Implicit Type gT : finGroupType.
Implicit Type p : nat.

(* B & G, Lemma 3.1 is covered by frobenius.Frobenius_semiregularP. *)

(* This is B & G, Lemma 3.2. *)
Section FrobeniusQuotient.

Variables (gT : finGroupType) (G K R : {group gT}).
Implicit Type N : {group gT}.

(* This is a special case of B & G, Lemma 3.2 (b). *)
Lemma Frobenius_proper_quotient N :
    [Frobenius G = K ><| R] -> solvable K -> N <| G -> N \proper K ->
  [Frobenius G / N = (K / N) ><| (R / N)].
Proof.
move=> frobG solK nsNG /andP[sNK ltNK].
have [defG _ ntR _ _] := Frobenius_context frobG.
have [nsKG sRG defKR nKR tiKR] := sdprod_context defG; have [sKG _]:= andP nsKG.
have nsNK := normalS sNK sKG nsNG.
apply/Frobenius_semiregularP=> [|||Nx].
- rewrite sdprodE ?quotient_norms //.
    by rewrite -quotientMl ?defKR ?normal_norm.
  by rewrite -quotientGI // tiKR quotient1.
- by rewrite -subG1 quotient_sub1 ?normal_norm.
- rewrite -subG1 quotient_sub1; last by rewrite (subset_trans sRG) ?normal_norm.
  apply: contra ntR => sRN.
  by rewrite -subG1 -tiKR subsetI (subset_trans sRN) /=.
rewrite !inE andbC => /andP[/morphimP[x nNx Rx ->{Nx}] notNx].
apply/trivgP; rewrite /= -cent_cycle -quotient_cycle //.
rewrite -coprime_quotient_cent ?cycle_subG //; last first.
  by apply: coprimegS (Frobenius_coprime frobG); rewrite cycle_subG.
rewrite cent_cycle (Frobenius_reg_ker frobG) ?quotient1 // !inE Rx andbT.
by apply: contraNneq notNx => ->; rewrite morph1.
Qed.

(* This is B & G, Lemma 3.2 (a). *)
Lemma Frobenius_normal_proper_ker N :
    [Frobenius G = K ><| R] -> solvable K -> N <| G -> ~~ (K \subset N) ->
  N \proper K.
Proof.
move=> frobG solK nsNG ltNK; have [sNG nNG] := andP nsNG; pose H := N :&: K.
have [defG _ ntR _ _] := Frobenius_context frobG.
have [nsKG _ /mulG_sub[sKG _] nKR tiKR] := sdprod_context defG.
have nsHG: H <| G := normalI nsNG nsKG; have [_ nHG] := andP nsHG.
have ltHK: H \proper K by rewrite /proper subsetIr subsetI subxx andbT.
suffices /eqP tiNR: N :&: R == 1.
  rewrite /proper ltNK andbT -(setIidPl sNG).
  rewrite -(cover_partition (Frobenius_partition frobG)) big_distrr /=.
  apply/bigcupsP=> _ /setU1P[->| /imsetP[x Kx ->]]; first exact: subsetIr.
  rewrite conjD1g setIDA subDset -(normsP (subset_trans sKG nNG) x) //.
  by rewrite -conjIg tiNR conjs1g subsetUl.
suffices: (N :&: R) / H \subset [1].
  by rewrite -subG1 quotient_sub1 ?normsGI // -subsetIidr setIACA tiKR setIg1.
have frobGq := Frobenius_proper_quotient frobG solK nsHG ltHK.
have [_ ntKq _ _ _] := Frobenius_context frobGq.
rewrite -(cent_semiregular (Frobenius_reg_compl frobGq) _ ntKq) //.
rewrite subsetI quotientS ?subsetIr // quotient_cents2r //.
by rewrite commg_subI ?setIS // subsetIidl (subset_trans sKG).
Qed.

(* This is B & G, Lemma 3.2 (b). *)
Lemma Frobenius_quotient N :
    [Frobenius G = K ><| R] -> solvable K -> N <| G -> ~~ (K \subset N) ->
  [Frobenius G / N = (K / N) ><| (R / N)].
Proof.
move=> frobG solK nsNG ltKN; apply: Frobenius_proper_quotient => //.
exact: (Frobenius_normal_proper_ker frobG).
Qed.

End FrobeniusQuotient.

(* This is B & G, Lemma 3.3. *)
Lemma Frobenius_rfix_compl F gT (G K R : {group gT}) n
                          (rG : mx_representation F G n) :
    [Frobenius G = K ><| R] -> [char F]^'.-group K ->
  ~~ (K \subset rker rG) -> rfix_mx rG R != 0.
Proof.
rewrite /pgroup charf'_nat => frobG nzK.
have [defG _ _ ltKG ltRG]:= Frobenius_context frobG.
have{ltKG ltRG} [sKG sRG]: K \subset G /\ R \subset G by rewrite !proper_sub.
apply: contraNneq => fixR0; rewrite rfix_mx_rstabC // -(eqmx_scale _ nzK).
pose gsum H := gring_op rG (gset_mx F G H).
have fixsum (H : {group gT}): H \subset G -> (gsum H <= rfix_mx rG H)%MS.
  move/subsetP=> sHG; apply/rfix_mxP=> x Hx; have Gx := sHG x Hx.
  rewrite -gring_opG // -gring_opM ?envelop_mx_id //; congr (gring_op _ _).
  rewrite {2}/gset_mx (reindex_acts 'R _ Hx) ?astabsR //= mulmx_suml.
  by apply:eq_bigr=> y; move/sHG=> Gy; rewrite repr_mxM.
have: gsum G + rG 1 *+ #|K| = gsum K + \sum_(x in K) gsum (R :^ x).
  rewrite -gring_opG // -sumr_const -!linear_sum -!linearD; congr gring_op.
  rewrite {1}/gset_mx (set_partition_big _ (Frobenius_partition frobG)) /=.
  rewrite big_setU1 -?addrA /=; last first.
    by apply: contraL (group1 K) => /imsetP[x _ ->]; rewrite conjD1g !inE eqxx.
  congr (_ + _); rewrite big_imset /= => [|x y Kx Ky /= eqRxy]; last first.
    have [/eqP/sdprodP[_ _ _ tiKR] _ _ _ /eqP snRG] := and5P frobG.
    apply/eqP; rewrite eq_mulgV1 -in_set1 -set1gE -tiKR -snRG setIA.
    by rewrite (setIidPl sKG) !inE conjsgM eqRxy actK groupM /= ?groupV.
  rewrite -big_split; apply: eq_bigr => x Kx /=.
  by rewrite addrC conjD1g -big_setD1 ?group1.
have ->: gsum G = 0.
  apply/eqP; rewrite -submx0 -fixR0; apply: submx_trans (rfix_mxS rG sRG).
  exact: fixsum.
rewrite repr_mx1 -scaler_nat add0r => ->.
rewrite big1 ?addr0 ?fixsum // => x Kx; have Gx := subsetP sKG x Kx.
apply/eqP; rewrite -submx0 (submx_trans (fixsum _ _)) ?conj_subG //.
by rewrite -(mul0mx _ (rG x)) -fixR0 rfix_mx_conjsg.
Qed.

(* This is Aschbacher (40.6)(3), or G. (3.14)(iii). *)
Lemma regular_pq_group_cyclic gT p q (H R : {group gT}) :
    [/\ prime p, prime q & p != q] -> #|R| = (p * q)%N ->
    H :!=: 1 -> R \subset 'N(H) -> semiregular H R ->
  cyclic R.
Proof.
case=> pr_p pr_q q'p oR ntH nHR regHR.
without loss{q'p} ltpq: p q pr_p pr_q oR / p < q.
  by move=> IH; case: ltngtP q'p => // /IH-> //; rewrite mulnC.
have [p_gt0 q_gt0]: 0 < p /\ 0 < q by rewrite !prime_gt0.
have [[P sylP] [Q sylQ]] := (Sylow_exists p R, Sylow_exists q R).
have [sPR sQR] := (pHall_sub sylP, pHall_sub sylQ).
have [oP oQ]: #|P| = p /\ #|Q| = q.
  rewrite (card_Hall sylQ) (card_Hall sylP) oR !p_part !lognM ?logn_prime //.
  by rewrite !eqxx eq_sym gtn_eqF.
have [ntP ntQ]: P :!=: 1 /\ Q :!=: 1 by rewrite -!cardG_gt1 oP oQ !prime_gt1.
have nQR: R \subset 'N(Q).
  rewrite -subsetIidl -indexg_eq1 -(card_Syl_mod R pr_q) (card_Syl sylQ) /=.
  rewrite modn_small // -divgS ?subsetIl ?ltn_divLR // mulnC oR ltn_pmul2r //.
  by rewrite (leq_trans ltpq) // -oQ subset_leq_card // subsetI sQR normG.
have coQP: coprime #|Q| #|P|.
  by rewrite oP oQ prime_coprime ?dvdn_prime2 ?gtn_eqF.
have defR: Q ><| P = R.
  rewrite sdprodE ?coprime_TIg ?(subset_trans sPR) //.
  by apply/eqP; rewrite eqEcard mul_subG //= oR coprime_cardMg // oP oQ mulnC.
have [cycP cycQ]: cyclic P /\ cyclic Q by rewrite !prime_cyclic ?oP ?oQ.
suffices cQP: P \subset 'C(Q) by rewrite (@cyclic_dprod _ Q P) ?dprodEsd.
without loss /is_abelemP[r pr_r abelH]: H ntH nHR regHR / is_abelem H.
  move=> IH; have [r _ rH] := rank_witness H.
  have solR: solvable R.
    apply/metacyclic_sol/metacyclicP; exists Q.
    by rewrite /(Q <| R) sQR -(isog_cyclic (sdprod_isog defR)).
  have coHR: coprime #|H| #|R| := regular_norm_coprime nHR regHR.
  have [H1 sylH1 nH1R] := sol_coprime_Sylow_exists r solR nHR coHR.
  have ntH1: H1 :!=: 1 by rewrite -rank_gt0 (rank_Sylow sylH1) -rH rank_gt0.
  have [H2 minH2 sH21] := minnormal_exists ntH1 nH1R.
  have [sH1H rH1 _] := and3P sylH1; have sH2H := subset_trans sH21 sH1H.
  have [nH2R ntH2 abelH2] := minnormal_solvable minH2 sH21 (pgroup_sol rH1).
  by apply: IH abelH2 => //; apply: semiregularS regHR.
have: rfix_mx (abelem_repr abelH ntH nHR) P == 0.
  rewrite -mxrank_eq0 rfix_abelem // mxrank_eq0 rowg_mx_eq0 /=.
  by rewrite (cent_semiregular regHR) ?morphim1.
apply: contraLR => not_cQP; have{not_cQP} frobR: [Frobenius R = Q ><| P].
  by apply/prime_FrobeniusP; rewrite ?prime_TIg ?oP ?oQ // centsC.
apply: (Frobenius_rfix_compl frobR).
  rewrite (eq_p'group _ (charf_eq (char_Fp pr_r))).
  rewrite (coprime_p'group _ (abelem_pgroup abelH)) //.
  by rewrite coprime_sym (coprimegS sQR) ?regular_norm_coprime.
rewrite rker_abelem subsetI sQR centsC.
by rewrite -subsetIidl (cent_semiregular regHR) ?subG1.
Qed.

(* This is B & G, Theorem 3.4. *)
Theorem odd_prime_sdprod_rfix0 F gT (G K R : {group gT}) n 
                               (rG : mx_representation F G n) :
    K ><| R = G -> solvable G -> odd #|G| -> coprime #|K| #|R| -> prime #|R| ->
    [char F]^'.-group G -> rfix_mx rG R = 0 ->
  [~: R, K] \subset rker rG.
Proof.
move: {2}_.+1 (ltnSn #|G|) => m; elim: m => // m IHm in gT G K R n rG *.
rewrite ltnS; set p := #|R| => leGm defG solG oddG coKR p_pr F'G regR.
have [nsKG sRG defKR nKR tiKR] := sdprod_context defG.
have [sKG nKG] := andP nsKG; have solK := solvableS sKG solG.
have [-> | ntK] := eqsVneq K 1; first by rewrite commG1 sub1G.
have ker_ltK (H : {group gT}):
  H \proper K -> R \subset 'N(H) -> [~: R, H] \subset rker rG.
- move=> ltKH nHR; have sHK := proper_sub ltKH; set G1 := H <*> R.
  have sG1G: G1 \subset G by rewrite join_subG (subset_trans sHK).
  have coHR := coprimeSg sHK coKR.
  have defG1: H ><| R = G1 by rewrite sdprodEY // coprime_TIg.
  apply: subset_trans (subsetIr G1 _); rewrite -(rker_subg _ sG1G).
  apply: IHm; rewrite ?(solvableS sG1G) ?(oddSg sG1G) ?(pgroupS sG1G) //.
  apply: leq_trans leGm; rewrite /= norm_joinEr // -defKR !coprime_cardMg //.
  by rewrite ltn_pmul2r ?proper_card.
without loss [q q_pr qK]: / exists2 q, prime q & q.-group K.
  move=> IH; set q := pdiv #|K|.
  have q_pr: prime q by rewrite pdiv_prime ?cardG_gt1.
  have exHall := coprime_Hall_exists _ nKR coKR solK.
  have [Q sylQ nQR] := exHall q; have [Q' hallQ' nQ'R] := exHall q^'.
  have [sQK qQ _] := and3P sylQ; have [sQ'K q'Q' _] := and3P hallQ'.
  without loss{IH} ltQK: / Q \proper K.
    by rewrite properEneq; case: eqP IH => [<- -> | _ _ ->] //; exists q.
  have ltQ'K: Q' \proper K.
    rewrite properEneq; case: eqP (pgroupP q'Q' q q_pr) => //= ->.
    by rewrite !inE pdiv_dvd eqxx; apply.
  have nkerG := subset_trans _ (rker_norm rG).
  rewrite -quotient_cents2 ?nkerG //.
  have <-: Q * Q' = K.
    apply/eqP; rewrite eqEcard mulG_subG sQK sQ'K.
    rewrite coprime_cardMg ?(pnat_coprime qQ) //=.
    by rewrite (card_Hall sylQ) (card_Hall hallQ') partnC.
  rewrite quotientMl ?nkerG ?(subset_trans sQK) // centM subsetI.
  by rewrite !quotient_cents2r ?ker_ltK.
without loss{m IHm leGm} [ffulG cycZ]: / rker rG = 1 /\ cyclic 'Z(G).
  move=> IH; wlog [I M /= simM sumM _]: / mxsemisimple rG 1%:M.
    exact: (mx_reducible_semisimple (mxmodule1 _) (mx_Maschke _ F'G)).
  pose not_cRK_M i := ~~ ([~: R, K] \subset rstab rG (M i)).
  case: (pickP not_cRK_M) => [i | cRK_M]; last first.
    rewrite rfix_mx_rstabC ?comm_subG // -sumM.
    apply/sumsmx_subP=> i _; move/negbFE: (cRK_M i).
    by rewrite rfix_mx_rstabC ?comm_subG.
  have [modM ntM _] := simM i; pose rM := kquo_repr (submod_repr modM).
  do [rewrite {+}/not_cRK_M -(rker_submod modM) /=; set N := rker _] in rM *.
  have [N1 _ | ntN] := eqVneq N 1.
    apply: IH; split.
      by apply/trivgP; rewrite -N1 /N rker_submod rstabS ?submx1.
    have: mx_irreducible (submod_repr modM) by exact/submod_mx_irr.
    by apply: mx_faithful_irr_center_cyclic; exact/trivgP.
  have tiRN: R :&: N = 1.
    by apply: prime_TIg; rewrite //= rker_submod rfix_mx_rstabC // regR submx0.
  have nsNG: N <| G := rker_normal _; have [sNG nNG] := andP nsNG.
  have nNR := subset_trans sRG nNG.
  have sNK: N \subset K.
    have [pi hallK]: exists pi, pi.-Hall(G) K.
      by apply: HallP; rewrite -(coprime_sdprod_Hall_l defG).
    rewrite (sub_normal_Hall hallK) //=.
    apply: pnat_dvd (pHall_pgroup hallK).
    rewrite -(dvdn_pmul2r (prime_gt0 p_pr)) -!TI_cardMg // 1?setIC // defKR.
    by rewrite -norm_joinEr // cardSg // join_subG sNG.
  have defGq: (K / N) ><| (R / N) = G / N.
    rewrite sdprodE ?quotient_norms -?quotientMr ?defKR //.
    by rewrite -quotientGI // tiKR quotient1.
  case/negP; rewrite -quotient_cents2  ?(subset_trans _ nNG) //= -/N.
  rewrite (sameP commG1P trivgP).
  apply: subset_trans (kquo_mx_faithful (submod_repr modM)).
  rewrite IHm ?quotient_sol ?coprime_morph ?morphim_odd ?quotient_pgroup //.
  - apply: leq_trans leGm; exact: ltn_quotient.
  - by rewrite card_quotient // -indexgI tiRN indexg1.
  apply/eqP; rewrite -submx0 rfix_quo // rfix_submod //.
  by rewrite regR capmx0 linear0 sub0mx.
without loss perfectK: / [~: K, R] = K.
  move=> IH; have: [~: K, R] \subset K by rewrite commg_subl.
  rewrite subEproper; case/predU1P=> //; move/ker_ltK.
  by rewrite commGC commg_normr coprime_commGid // commGC => ->.
have primeR: {in R^#, forall x, 'C_K[x] = 'C_K(R)}.
  move=> x; case/setD1P=> nt_x Rx; rewrite -cent_cycle ((<[x]> =P R) _) //.
  rewrite eqEsubset cycle_subG Rx; apply: contraR nt_x; move/prime_TIg.
  by rewrite -cycle_eq1 (setIidPr _) ?cycle_subG // => ->.
case cKK: (abelian K).
  rewrite commGC perfectK; move/eqP: regR; apply: contraLR.
  apply: Frobenius_rfix_compl => //; last exact: pgroupS F'G.
  rewrite -{2 4}perfectK coprime_abel_cent_TI // in primeR.
  by apply/Frobenius_semiregularP; rewrite // -cardG_gt1 prime_gt1.
have [spK defZK]: special K /\ 'C_K(R) = 'Z(K).
  apply: (abelian_charsimple_special qK) => //.
  apply/bigcupsP=> H; case/andP=> chHK cHH.
  have:= char_sub chHK; rewrite subEproper.
  case/predU1P=> [eqHK | ltHK]; first by rewrite eqHK cKK in cHH.
  have nHR: R \subset 'N(H) := char_norm_trans chHK nKR.
  by rewrite (sameP commG1P trivgP) /= commGC -ffulG ker_ltK.
have{spK} esK: extraspecial K.
  have abelZK := center_special_abelem qK spK; have [qZK _] := andP abelZK.
  have /(pgroup_pdiv qZK)[_ _ []]: 'Z(K) != 1.
    by case: spK => _ <-; rewrite (sameP eqP commG1P) -abelianE cKK.
  case=> [|e] oK; first by split; rewrite ?oK.
  suffices: cyclic 'Z(K) by rewrite (abelem_cyclic abelZK) oK pfactorK.
  rewrite (cyclicS _ cycZ) // subsetI subIset ?sKG //=.
  by rewrite -defKR centM subsetI -{2}defZK !subsetIr.
have [e e_gt0 oKqe] := card_extraspecial qK esK.
have cycR: cyclic R := prime_cyclic p_pr.
have co_q_p: coprime q p by rewrite oKqe coprime_pexpl in coKR.
move/eqP: regR; case/idPn.
rewrite defZK in primeR.
case: (repr_extraspecial_prime_sdprod_cycle _ _ defG _ oKqe) => // _.
apply=> //; last exact/trivgP.
apply: contraL (oddSg sRG oddG); move/eqP->; have:= oddSg sKG oddG.
by rewrite oKqe addn1 /= !odd_exp /= orbC => ->.
Qed.

(* Internal action version of B & G, Theorem 3.4. *)
Theorem odd_prime_sdprod_abelem_cent1 k gT (G K R V : {group gT}) :
    solvable G -> odd #|G| -> K ><| R = G -> coprime #|K| #|R| -> prime #|R| ->
    k.-abelem V -> G \subset 'N(V) -> k^'.-group G -> 'C_V(R) = 1 ->
  [~: R, K] \subset 'C_K(V).
Proof.
move=> solG oddG defG coKR prR abelV nVG k'G regR.
have [_ sRG _ nKR _] := sdprod_context defG; rewrite subsetI commg_subr nKR.
case: (eqsVneq V 1) => [-> | ntV]; first exact: cents1.
pose rV := abelem_repr abelV ntV nVG.
apply: subset_trans (_ : rker rV \subset _); last first.
  by rewrite rker_abelem subsetIr.
apply: odd_prime_sdprod_rfix0 => //.
  have k_pr: prime k by case/pgroup_pdiv: (abelem_pgroup abelV).
  by rewrite (eq_pgroup G (eq_negn (charf_eq (char_Fp k_pr)))).
by apply/eqP; rewrite -submx0 rfix_abelem //= regR morphim1 rowg_mx1.
Qed.

(* This is B & G, Theorem 3.5. *)
Theorem Frobenius_prime_rfix1 F gT (G K R : {group gT}) n
                              (rG : mx_representation F G n) :
    K ><| R = G -> solvable G -> prime #|R| -> 'C_K(R) = 1 ->
    [char F]^'.-group G -> \rank (rfix_mx rG R) = 1%N ->
  K^`(1) \subset rker rG.
Proof.
move=> defG solG p_pr regR F'G fixRlin.
wlog closF: F rG F'G fixRlin / group_closure_field F gT.
  move=> IH; apply: (@group_closure_field_exists gT F) => [[Fc f closFc]].
  rewrite -(rker_map f) IH //; last by rewrite -map_rfix_mx mxrank_map.
  by rewrite (eq_p'group _ (fmorph_char f)).
move: {2}_.+1 (ltnSn #|K|) => m.
elim: m => // m IHm in gT G K R rG solG p_pr regR F'G closF fixRlin defG *.
rewrite ltnS => leKm.
have [nsKG sRG defKR nKR tiKR] := sdprod_context defG.
have [sKG nKG] := andP nsKG; have solK := solvableS sKG solG.
have cycR := prime_cyclic p_pr.
case: (eqsVneq K 1) => [-> | ntK]; first by rewrite derg1 commG1 sub1G.
have defR x: x \in R^# -> <[x]> = R.  
  case/setD1P; rewrite -cycle_subG -cycle_eq1 => ntX sXR.
  apply/eqP; rewrite eqEsubset sXR; apply: contraR ntX => /(prime_TIg p_pr).
  by rewrite /= (setIidPr sXR) => ->.
have ntR: R :!=: 1 by rewrite -cardG_gt1 prime_gt1.
have frobG: [Frobenius G = K ><| R].
  by apply/Frobenius_semiregularP=> // x Rx; rewrite -cent_cycle defR.
case: (eqVneq (rker rG) 1) => [ffulG | ntC]; last first.
  set C := rker rG in ntC *; have nsCG: C <| G := rker_normal rG.
  have [sCG nCG] := andP nsCG.
  have nCK := subset_trans sKG nCG; have nCR := subset_trans sRG nCG.
  case sKC: (K \subset C); first exact: subset_trans (der_sub _ _) _.
  have sCK: C \subset K.
    by rewrite proper_sub // (Frobenius_normal_proper_ker frobG) ?sKC.
  have frobGq: [Frobenius G / C = (K / C) ><| (R / C)].
    by apply: Frobenius_quotient; rewrite ?sKC.
  have [defGq _ ntRq _ _] := Frobenius_context frobGq.
  rewrite -quotient_sub1 ?comm_subG ?quotient_der //= -/C.
  apply: subset_trans (kquo_mx_faithful rG).
  apply: IHm defGq _; rewrite 1?(quotient_sol, quotient_pgroup, rfix_quo) //.
  - rewrite card_quotient // -indexgI /= -/C setIC.
    by rewrite -(setIidPl sCK) -setIA tiKR (setIidPr (sub1G _)) indexg1.
  - have: cyclic (R / C) by [rewrite quotient_cyclic]; case/cyclicP=> Cx defRq.
    rewrite /= defRq cent_cycle (Frobenius_reg_ker frobGq) //= !inE defRq.
    by rewrite cycle_id -cycle_eq1 -defRq ntRq.
  - move=> Hq; rewrite -(group_inj (cosetpreK Hq)).
    by apply: quotient_splitting_field; rewrite ?subsetIl.
  by apply: leq_trans leKm; exact: ltn_quotient.
have ltK_abelian (N : {group gT}): R \subset 'N(N) -> N \proper K -> abelian N.
  move=> nNR ltNK; have [sNK _] := andP ltNK; apply/commG1P/trivgP.
  rewrite -(setIidPr (sub1G (N <*> R))) /= -ffulG; set G1 := N <*> R.
  have sG1: G1 \subset G by rewrite join_subG (subset_trans sNK).
  have defG1: N ><| R = G1.
    by rewrite sdprodEY //; apply/trivgP; rewrite -tiKR setSI.
  rewrite -(rker_subg _ sG1).
  apply: IHm defG1 _; rewrite ?(solvableS sG1) ?(pgroupS sG1) //.
    by apply/trivgP; rewrite -regR setSI.
  by apply: leq_trans leKm; exact: proper_card.
have cK'K': abelian K^`(1).
  apply: ltK_abelian; first exact: char_norm_trans (der_char _ _) nKR.
  exact: (sol_der1_proper solK).
pose fixG := rfix_mx rG; pose NRmod N (U : 'M_n) := N <*> R \subset rstabs rG U.
have dx_modK_rfix (N : {group gT}) U V:
    N \subset K -> R \subset 'N(N) -> NRmod N U -> NRmod N V ->
  mxdirect (U + V) -> (U <= fixG N)%MS || (V <= fixG N)%MS.
- move=> sNK nNR nUNR nVNR dxUV.
  have [-> | ntN] := eqsVneq N 1; first by rewrite -rfix_mx_rstabC sub1G.
  have sNRG: N <*> R \subset G by rewrite join_subG (subset_trans sNK).
  pose rNR := subg_repr rG sNRG.
  have nfixU W: NRmod N W -> ~~ (W <= fixG N)%MS -> (fixG R <= W)%MS.
    move=> nWN not_cWN; rewrite (sameP capmx_idPr eqmxP).
    rewrite -(geq_leqif (mxrank_leqif_eq (capmxSr _ _))) fixRlin lt0n.
    rewrite mxrank_eq0 -(in_submodK (capmxSl _ _)) val_submod_eq0.
    have modW: mxmodule rNR W by rewrite /mxmodule rstabs_subg subsetI subxx.
    rewrite -(eqmx_eq0 (rfix_submod modW _)) ?joing_subr //.
    apply: Frobenius_rfix_compl (pgroupS (subset_trans sNK sKG) F'G) _.
      apply/Frobenius_semiregularP=> // [|x Rx].
        by rewrite sdprodEY //; apply/trivgP; rewrite -tiKR setSI.
      by apply/trivgP; rewrite -regR /= -cent_cycle defR ?setSI.
    by rewrite rker_submod rfix_mx_rstabC ?joing_subl.
  have: fixG R != 0 by rewrite -mxrank_eq0 fixRlin.
  apply: contraR; case/norP=> not_fixU not_fixW.
  by rewrite -submx0 -(mxdirect_addsP dxUV) sub_capmx !nfixU.
have redG := mx_Maschke rG F'G.
wlog [U simU nfixU]: / exists2 U, mxsimple rG U & ~~ (U <= fixG K)%MS.
  move=> IH; wlog [I U /= simU sumU _]: / mxsemisimple rG 1%:M.
    exact: (mx_reducible_semisimple (mxmodule1 _) redG).
  case: (pickP (fun i => ~~ (U i <= fixG K))%MS) => [i nfixU | fixK].
    by apply: IH; exists (U i).
  apply: (subset_trans (der_sub _ _)); rewrite rfix_mx_rstabC // -sumU.
  by apply/sumsmx_subP=> i _; apply/idPn; rewrite fixK.
have [modU ntU minU] := simU; pose rU := submod_repr modU.
have irrU: mx_irreducible rU by exact/submod_mx_irr.
have [W modW sumUW dxUW] := redG U modU (submx1 U).
have cWK: (W <= fixG K)%MS.
  have:= dx_modK_rfix _ _ _ (subxx _) nKR _ _ dxUW.
  by rewrite /NRmod /= norm_joinEr // defKR (negPf nfixU); exact.
have nsK'G: K^`(1) <| G by exact: char_normal_trans (der_char _ _) nsKG.
have [sK'G nK'G] := andP nsK'G.
suffices nregK'U: (rfix_mx rU K^`(1))%MS != 0.
  rewrite rfix_mx_rstabC ?normal_sub // -sumUW addsmx_sub andbC.
  rewrite (submx_trans cWK) ?rfix_mxS ?der_sub //= (sameP capmx_idPl eqmxP).
  rewrite minU ?capmxSl ?capmx_module ?normal_rfix_mx_module //.
  apply: contra nregK'U => cUK'; rewrite (eqmx_eq0 (rfix_submod _ _)) //.
  by rewrite (eqP cUK') linear0.
pose rK := subg_repr rU (normal_sub nsKG); set p := #|R| in p_pr.
wlog sK: / socleType rK by exact: socle_exists.
have [i _ def_sK]: exists2 i, i \in setT & [set: sK] = orbit 'Cl G i.
  by apply/imsetP; exact: Clifford_atrans.
have card_sK: #|[set: sK]| =  #|G : 'C[i | 'Cl]|.
  by rewrite def_sK card_orbit_in ?indexgI.
have ciK: K \subset 'C[i | 'Cl].
  apply: subset_trans (astabS _ (subsetT _)).
  by apply: subset_trans (Clifford_astab _); exact: joing_subl.
pose M := socle_base i; have simM: mxsimple rK M := socle_simple i.
have [sKp | sK1 {ciK card_sK}]: #|[set: sK]| = p \/ #|[set: sK]| = 1%N.
- apply/pred2P; rewrite orbC card_sK; case/primeP: p_pr => _; apply.
  by rewrite (_ : p = #|G : K|) ?indexgS // -divgS // -(sdprod_card defG) mulKn.
- have{def_sK} def_sK: [set: sK] = orbit 'Cl R i.
    apply/eqP; rewrite eq_sym -subTset def_sK.
    apply/subsetP=> i_yz; case/imsetP=> yz; rewrite -{1}defKR.
    case/imset2P=> y z; move/(subsetP ciK); rewrite !inE sub1set inE.
    case/andP=> Gy; move/eqP=> ciy Rz -> ->{yz i_yz}.
    by rewrite actMin ?(subsetP sRG z Rz) // ciy mem_orbit.
  have inj_i: {in R &, injective ('Cl%act i)}.
    apply/dinjectiveP; apply/card_uniqP; rewrite size_map -cardE -/p.
    by rewrite -sKp def_sK /orbit Imset.imsetE cardsE.
  pose sM := (\sum_(y in R) M *m rU y)%MS.
  have dxM: mxdirect sM.
    apply/mxdirect_sumsP=> y Ry; have Gy := subsetP sRG y Ry.
    pose j := 'Cl%act i y.
    apply/eqP; rewrite -submx0 -{2}(mxdirect_sumsP (Socle_direct sK) j) //.
    rewrite capmxS ?val_Clifford_act // ?submxMr ?component_mx_id //.
    apply/sumsmx_subP => z; case/andP=> Rz ne_z_y; have Gz := subsetP sRG z Rz.
    rewrite (sumsmx_sup ('Cl%act i z)) ?(inj_in_eq inj_i) //.
    by rewrite val_Clifford_act // ?submxMr // ?component_mx_id.
  pose inCR := \sum_(x in R) rU x.
  have im_inCR: (inCR <= rfix_mx rU R)%MS.
    apply/rfix_mxP=> x Rx; have Gx := subsetP sRG x Rx.
    rewrite {2}[inCR](reindex_astabs 'R x) ?astabsR //= mulmx_suml.
    by apply: eq_bigr => y; move/(subsetP sRG)=> Gy; rewrite repr_mxM.
  pose inM := proj_mx M (\sum_(x in R | x != 1) M *m rU x)%MS.
  have dxM1 := mxdirect_sumsP dxM _ (group1 R).
  rewrite repr_mx1 mulmx1 in dxM1.
  have inCR_K: M *m inCR *m inM = M.
    rewrite mulmx_sumr (bigD1 1) //= repr_mx1 mulmx1 mulmxDl proj_mx_id //.
    by rewrite proj_mx_0 ?addr0 // summx_sub_sums.
  have [modM ntM _] := simM.
  have linM: \rank M = 1%N.
    apply/eqP; rewrite eqn_leq lt0n mxrank_eq0 ntM andbT.
    rewrite -inCR_K; apply: leq_trans (mxrankM_maxl _ _) _.
    apply: leq_trans (mxrankS (mulmx_sub _ im_inCR)) _.
    rewrite rfix_submod //; apply: leq_trans (mxrankM_maxl _ _) _.
    by rewrite -fixRlin mxrankS ?capmxSr.
  apply: contra (ntM); move/eqP; rewrite -submx0 => <-.
  by rewrite -(rfix_mx_rstabC rK) ?der_sub // -(rker_submod modM) rker_linear.
have{sK i M simM sK1 def_sK} irrK: mx_irreducible rK.
  have cycGq: cyclic (G / K) by rewrite -defKR quotientMidl quotient_cyclic.
  apply: (mx_irr_prime_index closF irrU cycGq simM) => x Gx /=.
  apply: (component_mx_iso simM); first exact: Clifford_simple.
  have jP: component_mx rK (M *m rU x) \in socle_enum sK.
    by apply: component_socle; exact: Clifford_simple.
  pose j := PackSocle jP; apply: submx_trans (_ : j <= _)%MS.
    by rewrite PackSocleK component_mx_id //; exact: Clifford_simple.
  have def_i: [set i] == [set: sK] by rewrite eqEcard subsetT cards1 sK1.
  by rewrite ((j =P i) _) // -in_set1 (eqP def_i) inE.
pose G' := K^`(1) <*> R.
have sG'G: G' \subset G by rewrite join_subG sK'G.
pose rG' := subg_repr rU sG'G.
wlog irrG': / mx_irreducible rG'.
  move=> IH; wlog [M simM sM1]: / exists2 M, mxsimple rG' M & (M <= 1%:M)%MS.
    by apply: mxsimple_exists; rewrite ?mxmodule1; case: irrK.
  have [modM ntM _] := simM.
  have [M' modM' sumM dxM] := mx_Maschke rG' (pgroupS sG'G F'G) modM sM1.
  wlog{IH} ntM': / M' != 0.
    case: eqP sumM => [-> M1 _ | _ _ -> //]; apply: IH.
    by apply: mx_iso_simple simM; apply: eqmx_iso; rewrite addsmx0_id in M1.
  suffices: (K^`(1) \subset rstab rG' M) || (K^`(1) \subset rstab rG' M').
    rewrite !rfix_mx_rstabC ?joing_subl //; rewrite -!submx0 in ntM ntM' *.
    by case/orP; move/submx_trans=> sM; apply: (contra (sM _ _)).
  rewrite !rstab_subg !rstab_submod !subsetI joing_subl !rfix_mx_rstabC //.
  rewrite /mxmodule !rstabs_subg !rstabs_submod !subsetI !subxx in modM modM'.
  do 2!rewrite orbC -genmxE.
  rewrite dx_modK_rfix // /NRmod ?(eqmx_rstabs _ (genmxE _)) ?der_sub //.
    exact: subset_trans sRG nK'G.
  apply/mxdirect_addsP; apply/eqP; rewrite -genmx_cap (eqmx_eq0 (genmxE _)).
  rewrite -(in_submodK (submx_trans (capmxSl _ _) (val_submodP _))).
  rewrite val_submod_eq0 in_submodE -submx0 (submx_trans (capmxMr _ _ _)) //.
  by rewrite -!in_submodE !val_submodK (mxdirect_addsP dxM).
have nsK'K: K^`(1) <| K by apply: der_normal.
pose rK'K := subg_repr rK (normal_sub nsK'K).
have irrK'K: mx_absolutely_irreducible rK'K.
  wlog sK'K: / socleType rK'K by apply: socle_exists.
  have sK'_dv_K: #|[set: sK'K]| %| #|K|.
    exact: atrans_dvd_in (Clifford_atrans _ _).
  have nsK'G': K^`(1) <| G' := normalS (joing_subl _ _) sG'G nsK'G.
  pose rK'G' := subg_repr rG' (normal_sub nsK'G').
  wlog sK'G': / socleType rK'G' by exact: socle_exists.
  have coKp: coprime #|K| p := Frobenius_coprime frobG.
  have nK'R := subset_trans sRG nK'G.
  have sK'_dv_p: #|[set: sK'G']| %| p.
    suffices: #|G' : 'C([set: sK'G'] | 'Cl)| %| #|G' : K^`(1)|.
      rewrite -(divgS (joing_subl _ _)) /= {2}norm_joinEr //.
      rewrite coprime_cardMg ?(coprimeSg (normal_sub nsK'K)) //.
      rewrite mulKn ?cardG_gt0 // -indexgI; apply: dvdn_trans.
      exact: atrans_dvd_index_in (Clifford_atrans _ _).
    rewrite indexgS //; apply: subset_trans (Clifford_astab sK'G').
    exact: joing_subl.
  have eq_sK': #|[set: sK'K]| = #|[set: sK'G']|.
    rewrite !cardsT !cardE -!(size_map (fun i => socle_val i)).
    apply: perm_eq_size.
    rewrite uniq_perm_eq 1?(map_inj_uniq val_inj) 1?enum_uniq // => V.
    apply/mapP/mapP=> [] [i _ ->{V}].
      exists (PackSocle (component_socle sK'G' (socle_simple i))).
        by rewrite mem_enum.
      by rewrite PackSocleK.
    exists (PackSocle (component_socle sK'K (socle_simple i))).
      by rewrite mem_enum.
    by rewrite PackSocleK.
  have [i def_i]: exists i, [set: sK'G'] = [set i].
    apply/cards1P; rewrite -dvdn1 -{7}(eqnP coKp) dvdn_gcd.
    by rewrite -{1}eq_sK' sK'_dv_K sK'_dv_p.
  pose M := socle_base i; have simM : mxsimple rK'G' M := socle_simple i.
  have cycGq: cyclic (G' / K^`(1)).
    by rewrite /G' joingC quotientYidr ?quotient_cyclic.
  apply closF; apply: (mx_irr_prime_index closF irrG' cycGq simM) => x K'x /=.
  apply: (component_mx_iso simM); first exact: Clifford_simple.
  have jP: component_mx rK'G' (M *m rG' x) \in socle_enum sK'G'.
    by apply: component_socle; exact: Clifford_simple.
  pose j := PackSocle jP; apply: submx_trans (_ : j <= _)%MS.
    by rewrite PackSocleK component_mx_id //; exact: Clifford_simple.
  by rewrite ((j =P i) _) // -in_set1 -def_i inE.
have linU: \rank U = 1%N by apply/eqP; rewrite abelian_abs_irr in irrK'K.
case: irrU => _ nz1 _; apply: contra nz1; move/eqP=> fix0.
by rewrite -submx0 -fix0 -(rfix_mx_rstabC rK) ?der_sub // rker_linear.
Qed.

(* Internal action version of B & G, Theorem 3.5. *)
Theorem Frobenius_prime_cent_prime k gT (G K R V : {group gT}) :
    solvable G -> K ><| R = G -> prime #|R| -> 'C_K(R) = 1 -> 
    k.-abelem V -> G \subset 'N(V) -> k^'.-group G -> #|'C_V(R)| = k ->
  K^`(1) \subset 'C_K(V).
Proof.
move=> solG defG prR regRK abelV nVG k'G primeRV.
have [_ sRG _ nKR _] := sdprod_context defG; rewrite subsetI der_sub.
have [-> | ntV] := eqsVneq V 1; first exact: cents1.
pose rV := abelem_repr abelV ntV nVG.
apply: subset_trans (_ : rker rV \subset _); last first.
  by rewrite rker_abelem subsetIr.
have k_pr: prime k by case/pgroup_pdiv: (abelem_pgroup abelV).
apply: (Frobenius_prime_rfix1 defG) => //.
  by rewrite (eq_pgroup G (eq_negn (charf_eq (char_Fp k_pr)))).
apply/eqP; rewrite rfix_abelem // -(eqn_exp2l _ _ (prime_gt1 k_pr)).
rewrite -{1}(card_Fp k_pr) -card_rowg rowg_mxK.
by rewrite card_injm ?abelem_rV_injm ?subsetIl ?primeRV.
Qed.

Section Theorem_3_6.
(* Limit the scope of the FiniteModule notations *)
Import FiniteModule.

(* This is B & G, Theorem 3.6. *)
Theorem odd_sdprod_Zgroup_cent_prime_plength1 p gT (G H R R0 : {group gT}) :
    solvable G -> odd #|G| -> H ><| R = G -> coprime #|H| #|R| ->
    R0 \subset R -> prime #|R0| -> Zgroup 'C_H(R0) ->
  p.-length_1 [~: H, R].
Proof.
move: {2}_.+1 (ltnSn #|G|) => n; elim: n => // n IHn in gT G H R R0 *.
rewrite ltnS; move oR0: #|R0| => r leGn solG oddG defG coHR sR0R r_pr ZgrCHR0.
have rR0: r.-group R0 by rewrite /pgroup oR0 pnat_id.
have [nsHG sRG mulHR nHR tiHR]:= sdprod_context defG.
have [sHG nHG] := andP nsHG; have solH := solvableS sHG solG.
have IHsub (H1 R1 : {group gT}):
    H1 \subset H -> H1 * R1 \subset 'N(H1) -> R0 \subset R1 -> R1 \subset R ->
  (#|H1| < #|H|) || (#|R1| < #|R|) -> p.-length_1 [~: H1, R1].
- move=> sH1 nH1 sR01 sR1 ltG1; set G1 := H1 <*> R1.
  have coHR1: coprime #|H1| #|R1| by rewrite (coprimeSg sH1) // (coprimegS sR1).
  have defG1: H1 ><| R1 = G1.
    by rewrite sdprodEY ?coprime_TIg ?(subset_trans (mulG_subr H1 R1)).
  have sG1: G1 \subset G by rewrite join_subG -mulG_subG -mulHR mulgSS.
  have{ltG1} ltG1n: #|G1| < n.
    rewrite (leq_trans _ leGn) // -(sdprod_card defG1) -(sdprod_card defG).
    have leqifS := leqif_geq (subset_leq_card _).
    rewrite ltn_neqAle !(leqif_mul (leqifS _ _ _ sH1) (leqifS _ _ _ sR1)).
    by rewrite muln_eq0 !negb_or negb_and -!ltnNge ltG1 -!lt0n !cardG_gt0.
  apply: IHn defG1 _ sR01 _ _; rewrite ?oR0 ?(solvableS sG1) ?(oddSg sG1) //.
  exact: ZgroupS (setSI _ sH1) ZgrCHR0.
without loss defHR: / [~: H, R] = H; last rewrite defHR.
  have sHR_H: [~: H, R] \subset H by rewrite commg_subl.
  have:= sHR_H; rewrite subEproper; case/predU1P=> [-> -> //|ltHR_H _].
  rewrite -coprime_commGid // IHsub 1?proper_card //.
  by apply: subset_trans (commg_norm H R); rewrite norm_joinEr ?mulSg.
have{n leGn IHn tiHR} IHquo (X : {group gT}):
  X :!=: 1 -> X \subset H -> G \subset 'N(X) -> p.-length_1 (H / X).
- move=> ntX sXH nXG; have nXH := subset_trans sHG nXG.
  have nXR := subset_trans sRG nXG; have nXR0 := subset_trans sR0R nXR.
  rewrite -defHR quotientE morphimR // -!quotientE.
  have ltGbn: #|G / X| < n.
    exact: leq_trans (ltn_quotient ntX (subset_trans sXH sHG)) _.
  have defGb: (H / X) ><| (R / X) = G / X by exact: quotient_coprime_sdprod.
  have pr_R0b: prime #|R0 / X|.
    have tiXR0: X :&: R0 = 1 by apply/trivgP; rewrite -tiHR setISS.
    by rewrite card_quotient // -indexgI setIC tiXR0 indexg1 oR0.
  have solGb: solvable (G / X) by exact: quotient_sol.
  have coHRb: coprime #|H / X| #|R / X| by exact: coprime_morph.
  apply: IHn defGb coHRb _ pr_R0b _; rewrite ?quotientS ?quotient_odd //.
  by rewrite -coprime_quotient_cent ?(coprimegS sR0R) // morphim_Zgroup.
without loss Op'H: / 'O_p^'(H) = 1.
  have [_ -> // | ntO _] := eqVneq 'O_p^'(H) 1.
  suffices: p.-length_1 (H / 'O_p^'(H)).
    by rewrite p'quo_plength1 ?pcore_normal ?pcore_pgroup.
  apply: IHquo => //; first by rewrite normal_sub ?pcore_normal.
  by rewrite normal_norm // (char_normal_trans (pcore_char _ _)).
move defV: 'F(H)%G => V.
have charV: V \char H by rewrite -defV Fitting_char.
have [sVH nVH]: V \subset H /\ H \subset 'N(V) := andP (char_normal charV).
have nsVG: V <| G := char_normal_trans charV nsHG.
have [_ nVG] := andP nsVG; have nVR: R \subset 'N(V) := subset_trans sRG nVG.
without loss ntV: / V :!=: 1.
  by rewrite -defV trivg_Fitting //; case: eqP => [|_] ->; rewrite ?plength1_1.
have scVHV: 'C_H(V) \subset V by rewrite -defV cent_sub_Fitting.
have{defV Op'H} defV: 'O_p(H) = V by rewrite -(Fitting_eq_pcore Op'H) -defV.
have pV: p.-group V by rewrite -defV pcore_pgroup.
have [p_pr p_dv_V _] := pgroup_pdiv pV ntV.
have p'r: r != p.
  rewrite eq_sym -dvdn_prime2 // -prime_coprime // (coprime_dvdl p_dv_V) //.
  by rewrite -oR0 (coprimegS sR0R) // (coprimeSg sVH).
without loss{charV} abelV: / p.-abelem V; last have [_ cVV eV] := and3P abelV.
  move/implyP; rewrite implybE -trivg_Phi //; case/orP=> // ntPhi.
  have charPhi: 'Phi(V) \char H := char_trans (Phi_char _) charV.
  have nsPhiH := char_normal charPhi; have [sPhiH nPhiH] := andP nsPhiH.
  have{charPhi} nPhiG: G \subset 'N('Phi(V)):= char_norm_trans charPhi nHG.
  rewrite -(pquo_plength1 nsPhiH) 1?IHquo ?(pgroupS (Phi_sub _)) //.
  have [/= W defW sPhiW nsWH] := inv_quotientN nsPhiH (pcore_normal p^' _).
  have p'Wb: p^'.-group (W / 'Phi(V)) by rewrite -defW pcore_pgroup.
  have{p'Wb} tiWb := coprime_TIg (pnat_coprime (quotient_pgroup _ _) p'Wb).
  suffices pW: p.-group W by rewrite -(tiWb W pW) setIid.
  apply/pgroupP=> q q_pr; case/Cauchy=> // x Wx ox; apply: wlog_neg => q'p.
  suffices Vx: x \in V by rewrite (pgroupP pV) // -ox order_dvdG.
  have [sWH nWH] := andP nsWH; rewrite (subsetP scVHV) // inE (subsetP sWH) //=.
  have coVx: coprime #|V| #[x] by rewrite ox (pnat_coprime pV) // pnatE.
  rewrite -cycle_subG (coprime_cent_Phi pV coVx) //.
  have: V :&: W \subset 'Phi(V); last apply: subset_trans.
    rewrite -quotient_sub1; last by rewrite subIset ?(subset_trans sWH) ?orbT.
    by rewrite quotientIG ?tiWb.
  rewrite commg_subI //; first by rewrite subsetI subxx (subset_trans sVH).
  by rewrite cycle_subG inE Wx (subsetP nVH) // (subsetP sWH).
have{scVHV} scVH: 'C_H(V) = V by apply/eqP; rewrite eqEsubset scVHV subsetI sVH.
without loss{IHquo} indecomposableV: / forall U W,
  U \x W = V -> G \subset 'N(U) :&: 'N(W) -> U = 1 \/ U = V.
- pose decV UW := let: (U, W) := UW in
    [&& U \x W == V, G \subset 'N(U) :&: 'N(W), U != 1 & W != 1].
  case: (pickP decV) => [[A B /=] | indecV]; last first.
    apply=> U W defUW nUW_G; have:= indecV (U, W); rewrite /= -defUW nUW_G eqxx.
    by rewrite -negb_or; case/pred2P=> ->; [left | right; rewrite dprodg1].
  rewrite subsetI -!andbA => /and5P[/eqP/dprodP[[U W -> ->{A B}]]].
  move=> defUW _ tiUW nUG nWG ntU ntW _.
  have [sUH sWH]: U \subset H /\ W \subset H.
    by apply/andP; rewrite -mulG_subG defUW.
  have [nsUH nsWH]: U <| H /\ W <| H.
    by rewrite /normal !(subset_trans sHG) ?andbT.
  by rewrite -(quo2_plength1 _ nsUH nsWH) ?tiUW ?IHquo.
have nsFb: 'F(H / V) <| G / V.
  exact: char_normal_trans (Fitting_char _) (morphim_normal _ _).
have{nsVG nsFb} [/= U defU sVU nsUG] := inv_quotientN nsVG nsFb.
have{nsUG} [sUG nUG] := andP nsUG.
have [solU nVU] := (solvableS sUG solG, subset_trans sUG nVG).
have sUH: U \subset H by rewrite -(quotientSGK nVU sVH) -defU Fitting_sub.
have [K hallK nKR]: exists2 K : {group gT}, p^'.-Hall(U) K & R \subset 'N(K).
  by apply: coprime_Hall_exists; rewrite ?(coprimeSg sUH) ?(subset_trans sRG).
have [sKU p'K _] := and3P hallK; have{sUG} sKG := subset_trans sKU sUG.
have coVK: coprime #|V| #|K| := pnat_coprime pV p'K.
have [sKH nVK] := (subset_trans sKU sUH, subset_trans sKU nVU).
have{defV} p'Ub: p^'.-group (U / V).
  rewrite -defU -['F(H / V)](nilpotent_pcoreC p (Fitting_nil _)) /=.
  by rewrite p_core_Fitting -defV trivg_pcore_quotient dprod1g pcore_pgroup.
have{p'Ub} sylV: p.-Sylow(U) V by rewrite /pHall sVU pV -card_quotient.
have{sKU} mulVK: V * K = U.
  apply/eqP; rewrite eqEcard mul_subG //= coprime_cardMg //.
  by rewrite (card_Hall sylV) (card_Hall hallK) partnC.
have [sKN sNH]: K \subset 'N_H(K) /\ 'N_H(K) \subset H.
  by rewrite subsetIl subsetI sKH normG.
have [solN nVN] := (solvableS sNH solH, subset_trans sNH nVH).
have{solU hallK sUH nUG} defH: V * 'N_H(K) = H.
  have nsUH: U <| H by apply/andP; rewrite (subset_trans sHG).
  by rewrite -(mulSGid sKN) mulgA mulVK (Hall_Frattini_arg solU nsUH hallK).
have [P sylP nPR]: exists2 P : {group _}, p.-Sylow('N_H(K)) P & R \subset 'N(P).
  apply: coprime_Hall_exists (coprimeSg sNH coHR) solN.
  by rewrite normsI ?norms_norm.
have [sPN pP _]: [/\ P \subset 'N_H(K), p.-group P & _] := and3P sylP.
have [sPH nKP]: P \subset H /\ P \subset 'N(K) by apply/andP; rewrite -subsetI.
have nVP := subset_trans sPH nVH.
have coKP: coprime #|K| #|P| by rewrite coprime_sym (pnat_coprime pP).
have{sylP} sylVP: p.-Sylow(H) (V <*> P).
  rewrite pHallE /= norm_joinEr ?mul_subG //= -defH -!LagrangeMl.
  rewrite partnM // part_pnat_id // -!card_quotient //.
  by apply/eqP; congr (_ * _)%N; apply: card_Hall; exact: quotient_pHall.
have [trKP | {sylV sVU nVU}ntKP] := eqVneq [~: K, P] 1.
  suffices sylVH: p.-Sylow(H) V.
    rewrite p_elt_gen_length1 // (_ : p_elt_gen p H = V).
      rewrite /pHall pcore_sub pcore_pgroup /= pnatNK.
      by apply: pnat_dvd pV; exact: dvdn_indexg.
    rewrite -(genGid V) -(setIidPr sVH); congr <<_>>; apply/setP=> x.
    rewrite !inE; apply: andb_id2l => Hx.
    by rewrite (mem_normal_Hall sylVH) /normal ?sVH.
  suffices sPV: P \subset V by rewrite -(joing_idPl sPV).
  suffices sPU: P \subset U by rewrite (sub_normal_Hall sylV) //; exact/andP.
  have cUPb: P / V \subset 'C_(H / V)(U / V).
    rewrite subsetI morphimS // -mulVK quotientMidl quotient_cents2r //.
    by rewrite commGC trKP sub1G.
  rewrite -(quotientSGK nVP sVU) (subset_trans cUPb) //.
  by rewrite -defU cent_sub_Fitting ?quotient_sol.
have{sylVP} dxV: [~: V, K] \x 'C_V(K) = V by exact: coprime_abelian_cent_dprod.
have tiVsub_VcK: 'C_V(K) = 1 \/ 'C_V(K) = V.
  apply: (indecomposableV _  [~: V, K]); first by rewrite dprodC.
  rewrite -mulHR -defH -mulgA mul_subG // subsetI.
    by rewrite commg_norml cents_norm // centsC subIset // -abelianE cVV.
  have nK_NR: 'N_H(K) * R \subset 'N(K) by rewrite mul_subG ?subsetIr.
  have nV_NR: 'N_H(K) * R \subset 'N(V) by rewrite mul_subG.
  by rewrite normsR // normsI ?norms_cent.
have{tiVsub_VcK dxV} [defVK tiVcK]: [~: V, K] = V /\ 'C_V(K) = 1.
  have [tiVcK | eqC] := tiVsub_VcK; first by rewrite -{2}dxV // tiVcK dprodg1.
  rewrite (card1_trivg (pnat_1 (pgroupS _ pV) p'K)) ?comm1G ?eqxx // in ntKP.
  by rewrite -scVH subsetI sKH centsC -eqC subsetIr.
have eqVncK: 'N_V(K) = 'C_V(K) := coprime_norm_cent nVK (pnat_coprime pV p'K).
have{eqVncK} tiVN: V :&: 'N_H(K) = 1 by rewrite setIA (setIidPl sVH) eqVncK.
have{sPN} tiVP: V :&: P = 1 by apply/trivgP; rewrite -tiVN setIS.
have{U defU mulVK} defK: 'F('N_H(K)) = K.
  have [injV imV] := isomP (quotient_isom nVN tiVN).
  rewrite -(im_invm injV) -injm_Fitting ?injm_invm //= {2}imV /=.
  rewrite -quotientMidl defH defU -mulVK quotientMidl morphim_invmE.
  by rewrite morphpre_restrm quotientK // -group_modr // setIC tiVN mul1g.
have scKH: 'C_H(K) \subset K.
  rewrite -{2}defK; apply: subset_trans (cent_sub_Fitting _) => //.
  by rewrite defK subsetI subsetIr setIS // cent_sub.
have{nVN} ntKR0: [~: K, R0] != 1.
  rewrite (sameP eqP commG1P); apply: contra ntKP => cR0K.
  have ZgrK: Zgroup K by apply: ZgroupS ZgrCHR0; rewrite subsetI sKH.
  have{ZgrK} cycK: cyclic K by rewrite nil_Zgroup_cyclic // -defK Fitting_nil.
  have{cycK} sNR_K: [~: 'N_H(K), R] \subset K.
    apply: subset_trans scKH; rewrite subsetI; apply/andP; split.
      by rewrite (subset_trans (commSg R sNH)) // commGC commg_subr.
    suffices: 'N(K)^`(1) \subset 'C(K).
      by apply: subset_trans; rewrite commgSS ?subsetIr.
    rewrite der1_min ?cent_norm //= -ker_conj_aut (isog_abelian (first_isog _)).
    exact: abelianS (Aut_conj_aut K 'N(K)) (Aut_cyclic_abelian cycK).
  suffices sPV: P \subset V by rewrite -(setIidPr sPV) tiVP commG1.
  have pPV: p.-group (P / V) := quotient_pgroup V pP.
  rewrite -quotient_sub1 // subG1 (card1_trivg (pnat_1 pPV _)) //.
  apply: pgroupS (quotient_pgroup V p'K).
  apply: subset_trans (quotientS V sNR_K).
  by rewrite quotientR // -quotientMidl defH -quotientR ?defHR ?quotientS.
have nKR0: R0 \subset 'N(K) := subset_trans sR0R nKR.
have mulKR0: K * R0 = K <*> R0 by rewrite norm_joinEr.
have sKR0_G : K <*> R0 \subset G by rewrite -mulKR0 -mulHR mulgSS.
have nV_KR0: K <*> R0 \subset 'N(V) := subset_trans sKR0_G nVG.
have solKR0: solvable (K <*> R0) by exact: solvableS solG.
have coKR0: coprime #|K| #|R0| by rewrite (coprimeSg sKH) ?(coprimegS sR0R).
have r'K: r^'.-group K.
  by rewrite /pgroup p'natE -?prime_coprime // coprime_sym -oR0.
have tiKcV: 'C_K(V) = 1.
  by apply/trivgP; rewrite -tiVN -{2}scVH -setIIr setICA setIC setSI.
have tiKR0cV: 'C_(K <*> R0)(V) = 1.
  set C := 'C_(K <*> R0)(V); apply/eqP; apply: contraR ntKR0 => ntC.
  have nC_KR0: K <*> R0 \subset 'N(C) by rewrite normsI ?normG ?norms_cent.
  rewrite -subG1 -(coprime_TIg coKR0) commg_subI ?subsetI ?subxx //=.
  suff defC: C == R0 by rewrite -(eqP defC) (subset_trans (joing_subl K R0)).
  have sC_R0: C \subset R0.
    rewrite -[C](coprime_mulG_setI_norm mulKR0) ?norms_cent //= tiKcV mul1g.
    exact: subsetIl.
  rewrite eqEsubset sC_R0; apply: contraR ntC => not_sR0C.
  by rewrite -(setIidPr sC_R0) prime_TIg ?oR0.
have{nKR0 mulKR0 sKR0_G solKR0 nV_KR0} oCVR0: #|'C_V(R0)| = p.
  case: (eqVneq 'C_V(R0) 1) => [tiVcR0 | ntCVR0].
    case/negP: ntKR0; rewrite -subG1/= commGC -tiKcV.
    have defKR0: K ><| R0 = K <*> R0 by rewrite sdprodE ?coprime_TIg.
    have odd_KR0: odd #|K <*> R0| := oddSg sKR0_G oddG.
    apply: odd_prime_sdprod_abelem_cent1 abelV nV_KR0 _ _; rewrite // ?oR0 //=.
    by rewrite -mulKR0 pgroupM p'K /pgroup oR0 pnatE.
  have [x defC]: exists x, 'C_V(R0) = <[x]>.
    have ZgrC: Zgroup 'C_V(R0) by apply: ZgroupS ZgrCHR0; exact: setSI.
    apply/cyclicP; apply: (forall_inP ZgrC); apply/SylowP; exists p => //.
    by rewrite /pHall subxx indexgg (pgroupS (subsetIl V _)).
  rewrite defC; apply: nt_prime_order => //; last by rewrite -cycle_eq1 -defC.
  by rewrite (exponentP eV) // -cycle_subG -defC subsetIl.
have tiPcR0: 'C_P(R0) = 1.
  rewrite -(setIidPl (joing_subl P V)) setIIl TI_Ohm1 //=.
  set C := 'C_(P <*> V)(R0); suffices <-: 'C_V(R0) = 'Ohm_1(C).
    by rewrite setIC -setIIl tiVP (setIidPl (sub1G _)).
  have pPV: p.-group (P <*> V) by rewrite norm_joinEl // pgroupM pP.
  have pC: p.-group C := pgroupS (subsetIl _ _) pPV.
  have abelCVR0: p.-abelem 'C_V(R0) by rewrite prime_abelem ?oCVR0.
  have sCV_C: 'C_V(R0) \subset C by rewrite setSI ?joing_subr.
  apply/eqP; rewrite eqEcard -(Ohm1_id abelCVR0) OhmS //=.
  have [-> | ntC] := eqVneq C 1; first by rewrite subset_leq_card ?OhmS ?sub1G.
  rewrite (Ohm1_id abelCVR0) oCVR0 (Ohm1_cyclic_pgroup_prime _ pC) //=.
  have ZgrC: Zgroup C by rewrite (ZgroupS _ ZgrCHR0) ?setSI // join_subG sPH.
  apply: (forall_inP ZgrC); apply/SylowP; exists p => //.
  by apply/pHallP; rewrite part_pnat_id.
have defP: [~: P, R0] = P.
  have solvP := pgroup_sol pP; have nPR0 := subset_trans sR0R nPR.
  have coPR0: coprime #|P| #|R0| by rewrite (coprimeSg sPH) ?(coprimegS sR0R).
  by rewrite -{2}(coprime_cent_prod nPR0) // tiPcR0 mulg1.
have{IHsub nVH} IHsub: forall X : {group gT},
  P <*> R0 \subset 'N(X) -> X \subset K ->
  (#|V <*> X <*> P| < #|H|) || (#|R0| < #|R|) -> [~: X, P] = 1.
- move=> X; rewrite join_subG; case/andP=> nXP nXR0 sXK.
  set H0 := V <*> X <*> P => ltG0G; have sXH := subset_trans sXK sKH.
  have sXH0: X \subset H0 by rewrite /H0 joingC joingA joing_subr.
  have sH0H: H0 \subset H by rewrite !join_subG sVH sXH.
  have nH0R0: R0 \subset 'N(H0).
    by rewrite 2?normsY ?nXR0 ?(subset_trans sR0R) // (subset_trans sRG).
  have Op'H0: 'O_p^'(H0) = 1.
    have [sOp' nOp'] := andP (pcore_normal _ _ : 'O_p^'(H0) <| H0).
    have p'Op': p^'.-group 'O_p^'(H0) by exact: pcore_pgroup.
    apply: card1_trivg (pnat_1 (pgroupS _ pV) p'Op').
    rewrite -scVH subsetI (subset_trans sOp') //= centsC; apply/setIidPl.
    rewrite -coprime_norm_cent ?(pnat_coprime pV p'Op') //.
      by rewrite (setIidPl (subset_trans _ nOp')) // /H0 -joingA joing_subl.
    exact: subset_trans (subset_trans sH0H nVH).
  have Op'HR0: 'O_p^'([~: H0, R0]) = 1.
    apply/trivgP; rewrite -Op'H0 pcore_max ?pcore_pgroup //.
    apply: char_normal_trans (pcore_char _ _) _.
    by rewrite /(_ <| _) commg_norml andbT commg_subl.
  have{ltG0G IHsub} p1_HR0: p.-length_1 [~: H0, R0].
    by apply: IHsub ltG0G => //=; rewrite mul_subG ?normG.
  have{p1_HR0} sPOpHR0: P \subset 'O_p([~: H0, R0]).
    rewrite sub_Hall_pcore //; last by rewrite -defP commSg ?joing_subr.
    rewrite /pHall pcore_sub pcore_pgroup /= -(pseries_pop2 _ Op'HR0).
    rewrite -card_quotient ?normal_norm ?pseries_normal // -/(pgroup _ _).
    by rewrite -{1}((_ :=P: _) p1_HR0) (quotient_pseries [::_;_]) pcore_pgroup.
  apply/trivgP; have <-: K :&: 'O_p([~: H0, R0]) = 1.
    by rewrite setIC coprime_TIg // (pnat_coprime (pcore_pgroup p _)).
  rewrite commg_subI // subsetI ?sPOpHR0 ?sXK //=.
  by rewrite (char_norm_trans (pcore_char _ _)) // normsRl.
have{defH sR0R} [defH defR0]: V * K * P = H /\ R0 :=: R.
  suffices: (V * K * P == H) && (R0 :==: R) by do 2!case: eqP => // ->.
  apply: contraR ntKP; rewrite -subG1 !eqEcard sR0R ?mul_subG //= negb_and.
  rewrite -!ltnNge -!norm_joinEr // 1?normsY //; move/IHsub=> -> //.
  by rewrite join_subG nKP (subset_trans sR0R).
move: IHsub defP oR0 rR0 ZgrCHR0 coKR0 ntKR0 tiKR0cV oCVR0 tiPcR0.
rewrite {R0}defR0 ltnn => IHsub defP oR rR ZgrCHR coKR ntKR tiKRcV oCVR tiPcR.
have mulVK: V * K = V <*> K by rewrite norm_joinEr.
have oVK: #|V <*> K| = (#|V| * #|K|)%N by rewrite -mulVK coprime_cardMg.
have tiVK_P: V <*> K :&: P = 1.
  have sylV: p.-Sylow(V <*> K) V.
    by rewrite /pHall pV -divgS joing_subl //= oVK mulKn.
  apply/trivgP; rewrite -tiVP subsetI subsetIr.
  rewrite (sub_normal_Hall sylV) ?subsetIl ?(pgroupS (subsetIr _ P)) //=.
  by rewrite /normal joing_subl join_subG normG.
have{mulVK oVK} oH: (#|H| = #|V| * #|K| * #|P|)%N.
  by rewrite -defH mulVK -oVK (TI_cardMg tiVK_P).
have{oH tiVK_P IHsub} IHsub: forall X : {group gT},
  P <*> R \subset 'N(X) -> X \subset K -> X :=: K \/ X \subset 'C(P).
- move=> X nX_PR sXK; have p'X: p^'.-group X := pgroupS sXK p'K.
  have nXP: P \subset 'N(X) := subset_trans (joing_subl P R) nX_PR.
  apply/predU1P; rewrite eqEcard sXK; case: leqP => //= ltXK.
  apply/commG1P; rewrite {}IHsub // orbF (norm_joinEr (normsY _ _)) //=.
  rewrite TI_cardMg /=; last first.
    by apply/trivgP; rewrite -tiVK_P setSI ?genS ?setUS.
  rewrite oH ltn_pmul2r ?cardG_gt0 // norm_joinEr ?(subset_trans sXK) //.
  by rewrite coprime_cardMg ?ltn_pmul2l ?(pnat_coprime pV).
have defKP: [~: K, P] = K.
  have sKP_K: [~: K, P] \subset K by rewrite commg_subl.
  have{sKP_K} [|//|cP_KP] := IHsub _ _ sKP_K.
    by rewrite join_subG /= commg_normr normsR.
  by case/eqP: ntKP; rewrite -coprime_commGid ?(commG1P cP_KP) ?(solvableS sKH).
have nKPR: P <*> R \subset 'N(K) by rewrite join_subG nKP.
have coPR: coprime #|P| #|R| by rewrite (coprimeSg sPH).
have{scKH} tiPRcK: 'C_(P <*> R)(K) = 1.
  have tiPK: P :&: K = 1 by rewrite setIC coprime_TIg.
  have tiPcK: 'C_P(K) = 1.
    by apply/trivgP; rewrite /= -{1}(setIidPl sPH) -setIA -tiPK setIS.
  have tiRcK: 'C_R(K) = 1.
    by rewrite prime_TIg ?oR // centsC (sameP commG1P eqP).
  have mulPR: P * R = P <*> R by rewrite norm_joinEr.
  by rewrite -(coprime_mulG_setI_norm mulPR) ?tiPcK ?mul1g ?norms_cent.
have [K1 | ntK]:= eqsVneq K 1; first by rewrite K1 comm1G eqxx in ntKR.
have [K1 | [q q_pr q_dv_K]] := trivgVpdiv K; first by case/eqP: ntK.
have q_gt1 := prime_gt1 q_pr.
have p'q: q != p by exact: (pgroupP p'K).
have{r'K} q'r: r != q by rewrite eq_sym; exact: (pgroupP r'K).
have{defK} qK: q.-group K.
  have{defK} nilK: nilpotent K by rewrite -defK Fitting_nil.
  have{nilK} [_ defK _ _] := dprodP (nilpotent_pcoreC q nilK).
  have{IHsub} IHpi: forall pi, 'O_pi(K) = K \/ 'O_pi(K) \subset 'C(P).
    move=> pi; apply: IHsub (pcore_sub _ _).
    by apply: char_norm_trans (pcore_char _ _) _; rewrite join_subG nKP.
  case: (IHpi q) => [<-| cPKq]; first exact: pcore_pgroup.
  case/eqP: ntKP; apply/commG1P; rewrite -{}defK mul_subG //.
  case: (IHpi q^') => // defK; case/idPn: q_dv_K.
  rewrite -p'natE // -defK; exact: pcore_pgroup.
pose K' := K^`(1); have charK': K' \char K := der_char 1 K.
have nsK'K: K' <| K := der_normal 1 K; have [sK'K nK'K] := andP nsK'K.
have nK'PR: P <*> R \subset 'N(K') := char_norm_trans charK' nKPR.
have iK'K: 'C_(P <*> R / K')(K / K') = 1 -> #|K / K'| > q ^ 2.
  have qKb: q.-group (K / K') by exact: morphim_pgroup qK.
  rewrite ltnNge => trCK'; apply: contra ntKP => Kq_le_q2.
  suffices sPR_K': [~: P, R] \subset K'.
    rewrite -defP -(setIidPl sPR_K') coprime_TIg ?commG1 //.
    by rewrite (pnat_coprime (pgroupS _ pP) (pgroupS sK'K p'K)) ?commg_subl.
  rewrite -quotient_cents2 ?(char_norm_trans charK') //.
  suffices cPRbPrb: abelian (P <*> R / K').
    by rewrite (sub_abelian_cent2 cPRbPrb) ?quotientS ?joing_subl ?joing_subr.
  have nKbPR: P <*> R / K' \subset 'N(K / K') by exact: quotient_norms.
  case cycK: (cyclic (K / K')).
    rewrite (isog_abelian (quotient1_isog _)) -trCK' -ker_conj_aut.
    rewrite (isog_abelian (first_isog_loc _ _)) //.
    by rewrite (abelianS (Aut_conj_aut _ _)) ?Aut_cyclic_abelian.
  have{cycK} [oKb abelKb]: #|K / K'| = (q ^ 2)%N /\ q.-abelem (K / K').
    have sKb1: 'Ohm_1(K / K') \subset K / K' by exact: Ohm_sub.
    have cKbKb: abelian (K / K') by rewrite sub_der1_abelian.
    have: #|'Ohm_1(K / K')| >= q ^ 2.
      rewrite (card_pgroup (pgroupS sKb1 qKb)) leq_exp2l // ltnNge.
      by rewrite -p_rank_abelian -?rank_pgroup // -abelian_rank1_cyclic ?cycK.
    rewrite (geq_leqif (leqif_trans (subset_leqif_card sKb1) (leqif_eq _))) //.
    by case/andP=> sKbKb1; move/eqP->; rewrite (abelemS sKbKb1) ?Ohm1_abelem.
  have ntKb: K / K' != 1 by rewrite -cardG_gt1 oKb (ltn_exp2l 0).
  pose rPR := abelem_repr abelKb ntKb nKbPR.
  have: mx_faithful rPR by rewrite abelem_mx_faithful.
  move: rPR; rewrite (dim_abelemE abelKb ntKb) oKb pfactorK // => rPR ffPR.
  apply: charf'_GL2_abelian ffPR _.
    by rewrite quotient_odd ?(oddSg _ oddG) // join_subG (subset_trans sPH).
  rewrite (eq_pgroup _ (eq_negn (charf_eq (char_Fp q_pr)))).
  rewrite quotient_pgroup //= norm_joinEr // pgroupM.
  by rewrite /pgroup (pi_pnat rR) // (pi_pnat pP) // !inE eq_sym.
case cKK: (abelian K); last first.
  have [|[dPhiK dK'] dCKP] := abelian_charsimple_special qK coKP defKP.
    apply/bigcupsP=> L; case/andP=> charL; have sLK := char_sub charL. 
    by case/IHsub: sLK cKK => // [|-> -> //]; exact: (char_norm_trans charL).
  have eK: exponent K %| q.
    have oddK: odd #|K| := oddSg sKG oddG.
    have [Q [charQ _ _ eQ qCKQ]] := critical_odd qK oddK ntK; rewrite -eQ.
    have sQK: Q \subset K := char_sub charQ.
    have [<- // | cQP] := IHsub Q (char_norm_trans charQ nKPR) sQK.
    case/negP: ntKP; rewrite (sameP eqP commG1P) centsC.
    rewrite -ker_conj_aut -sub_morphim_pre // subG1 trivg_card1.
    rewrite (pnat_1 (morphim_pgroup _ pP) (pi_pnat (pgroupS _ qCKQ) _)) //.
    apply/subsetP=> a; case/morphimP=> x nKx Px ->{a}.
    rewrite /= astab_ract inE /= Aut_aut; apply/astabP=> y Qy.
    rewrite [_ y _]norm_conj_autE ?(subsetP sQK) //.
    by rewrite /conjg (centsP cQP y) ?mulKg.
  have tiPRcKb: 'C_(P <*> R / K')(K / K') = 1.
    rewrite -quotient_astabQ -quotientIG /=; last first.
      by rewrite sub_astabQ normG trivg_quotient sub1G.
    apply/trivgP; rewrite -quotient1 quotientS // -tiPRcK subsetI subsetIl /=.
    rewrite (coprime_cent_Phi qK) ?(coprimegS (subsetIl _ _)) //=.
      by rewrite norm_joinEr // coprime_cardMg // coprime_mulr coKP.
    rewrite dPhiK -dK' -/K' (subset_trans (commgS _ (subsetIr _ _))) //.
    by rewrite astabQ -quotient_cents2 ?subsetIl // cosetpreK centsC /=.
  have [nK'P nK'R] := (char_norm_trans charK' nKP, char_norm_trans charK' nKR).
  have solK: solvable K := pgroup_sol qK.
  have dCKRb: 'C_K(R) / K' = 'C_(K / K')(R / K').
    by rewrite coprime_quotient_cent.
  have abelKb: q.-abelem (K / K') by rewrite [K']dK' -dPhiK Phi_quotient_abelem.
  have [qKb cKbKb _] := and3P abelKb.
  have [tiKcRb | ntCKRb]:= eqVneq 'C_(K / K')(R / K') 1.
    have coK'P: coprime #|K'| #|P| by rewrite (coprimeSg sK'K).
    suffices sPK': P \subset K'.
      by case/negP: ntKP; rewrite -(setIidPr sPK') coprime_TIg ?commG1.
    rewrite -quotient_sub1 // -defP commGC quotientR //= -/K'.
    have <-: 'C_(P / K')(K / K') = 1.
      by apply/trivgP; rewrite -tiPRcKb setSI ?morphimS ?joing_subl.
    have q'P: q^'.-group P by rewrite /pgroup (pi_pnat pP) // !inE eq_sym.
    move: tiKcRb; have: q^'.-group (P <*> R / K').
      rewrite quotient_pgroup //= norm_joinEr //.
      by rewrite pgroupM q'P /pgroup oR pnatE.
    have sPRG: P <*> R \subset G by rewrite join_subG sRG (subset_trans sPH).
    have coPRb: coprime #|P / K'| #|R / K'| by rewrite coprime_morph.
    apply: odd_prime_sdprod_abelem_cent1 abelKb _; rewrite ?quotient_norms //.
    - by rewrite quotient_sol // (solvableS sPRG).
    - by rewrite quotient_odd // (oddSg sPRG).
    - by rewrite /= quotientY // sdprodEY ?quotient_norms ?coprime_TIg.
    rewrite -(card_isog (quotient_isog nK'R _)) ?oR //.
    by rewrite coprime_TIg // (coprimeSg sK'K).
  have{ntCKRb} not_sCKR_K': ~~ ('C_K(R) \subset K').
    by rewrite -quotient_sub1 ?subIset ?nK'K // dCKRb subG1.
  have oCKR: #|'C_K(R)| = q.
    have [x defCKR]: exists x, 'C_K(R) = <[x]>.
      have ZgrCKR: Zgroup 'C_K(R) := ZgroupS (setSI _ sKH) ZgrCHR.
      have qCKR: q.-group 'C_K(R) by rewrite (pgroupS (subsetIl K _)).
      by apply/cyclicP; exact: nil_Zgroup_cyclic (pgroup_nil qCKR).
    have Kx: x \in K by rewrite -cycle_subG -defCKR subsetIl.
    rewrite defCKR cycle_subG in not_sCKR_K' *.
    exact: nt_prime_order (exponentP eK x Kx) (group1_contra not_sCKR_K').
  have tiCKR_K': 'C_K(R) :&: K' = 1 by rewrite prime_TIg ?oCKR.
  have sKR_K: [~: K, R] \subset K by rewrite commg_subl nKR.
  have ziKRcR: 'C_K(R) :&: [~: K, R] \subset K'.
    rewrite -quotient_sub1 ?subIset ?nK'K // setIC.
    rewrite (subset_trans (quotientI _ _ _)) // dCKRb setIA.
    rewrite (setIidPl (quotientS _ sKR_K)) // ?quotientR //= -/K'.
    by rewrite coprime_abel_cent_TI ?quotient_norms ?coprime_morph.
  have not_sK_KR: ~~ (K \subset [~: K, R]).
    by apply: contra not_sCKR_K' => sK_KR; rewrite -{1}(setIidPl sK_KR) setIAC.
  have tiKRcR: 'C_[~: K, R](R) = 1.
    rewrite -(setIidPr sKR_K) setIAC -(setIidPl ziKRcR) setIAC tiCKR_K'.
    by rewrite (setIidPl (sub1G _)).
  have cKR_KR: abelian [~: K, R].
    have: 'C_[~: K, R](V) \subset [1].
      rewrite -tiVN -{2}scVH -setIIr setICA setIC setIS //.
      exact: subset_trans sKR_K sKN.
    rewrite /abelian (sameP commG1P trivgP) /= -derg1; apply: subset_trans.
    have nKR_R: R \subset 'N([~: K, R]) by rewrite commg_normr.
    have sKRR_G: [~: K, R] <*> R \subset G by rewrite join_subG comm_subG.
    move: oCVR; have: p^'.-group ([~: K, R] <*> R).
      by rewrite norm_joinEr // pgroupM (pgroupS sKR_K p'K) /pgroup oR pnatE.
    have solKR_R := solvableS sKRR_G solG.
    apply: Frobenius_prime_cent_prime; rewrite ?oR ?(subset_trans _ nVG) //.
    by rewrite sdprodEY // coprime_TIg // (coprimeSg sKR_K).
  case nKR_P: (P \subset 'N([~: K, R])).
    have{nKR_P} nKR_PR: P <*> R \subset 'N([~: K, R]).
      by rewrite join_subG nKR_P commg_normr.
    have{nKR_PR} [dKR | cP_KR] := IHsub _ nKR_PR sKR_K.
      by rewrite dKR subxx in not_sK_KR.
    have{cP_KR} cKRb: R / K' \subset 'C(K / K').
      by rewrite quotient_cents2r //= dK' -dCKP commGC subsetI sKR_K.
    case/negP: ntKR; rewrite (sameP eqP commG1P) centsC.
    by rewrite (coprime_cent_Phi qK) // dPhiK -dK' commGC -quotient_cents2.
  have{nKR_P} [x Px not_nKRx] := subsetPn (negbT nKR_P).
  have iKR: #|K : [~: K, R]| = q.
    rewrite -divgS // -{1}(coprime_cent_prod nKR) // TI_cardMg ?mulKn //.
    by rewrite setIA (setIidPl sKR_K).
  have sKRx_K: [~: K, R] :^ x \subset K by rewrite -{2}(normsP nKP x Px) conjSg.
  have nKR_K: K \subset 'N([~: K, R]) by exact: commg_norml.
  have mulKR_Krx: [~: K, R] * [~: K, R] :^ x = K.
    have maxKR: maximal [~: K, R] K by rewrite p_index_maximal ?iKR.
    apply: mulg_normal_maximal; rewrite ?(p_maximal_normal qK) //.
    by rewrite inE in not_nKRx.
  have ziKR_KRx: [~: K, R] :&: [~: K, R] :^ x \subset K'.
    rewrite /K' dK' subsetI subIset ?sKR_K // -{3}mulKR_Krx centM centJ.
    by rewrite setISS ?conjSg.
  suffices: q ^ 2 >= #|K / K'| by rewrite leqNgt iK'K.
  rewrite -divg_normal // leq_divLR ?cardSg //.
  rewrite -(@leq_pmul2l (#|[~: K, R]| ^ 2)) ?expn_gt0 ?cardG_gt0 // mulnA.
  rewrite -expnMn -iKR Lagrange // -mulnn -{2}(cardJg _ x) mul_cardG.
  by rewrite mulKR_Krx mulnAC leq_pmul2l ?muln_gt0 ?cardG_gt0 ?subset_leq_card.
have tiKcP: 'C_K(P) = 1 by rewrite -defKP coprime_abel_cent_TI.
have{IHsub} abelK: q.-abelem K.
  have [|cPK1] := IHsub _ (char_norm_trans (Ohm_char 1 K) nKPR) (Ohm_sub 1 K).
    by move/abelem_Ohm1P->.
  rewrite -(setIid K) TI_Ohm1 ?eqxx // in ntK.
  by apply/eqP; rewrite -subG1 -tiKcP setIS.
have{K' iK'K charK' nsK'K sK'K nK'K nK'PR} oKq2: q ^ 2 < #|K|.
  have K'1: K' :=: 1 by exact/commG1P.
  rewrite -indexg1 -K'1 -card_quotient ?normal_norm // iK'K // K'1.
  by rewrite -injm_subcent ?coset1_injm ?norms1 //= tiPRcK morphim1.
pose S := [set Vi : {group gT} | 'C_V('C_K(Vi)) == Vi & maximal 'C_K(Vi) K].
have defSV Vi: Vi \in S -> 'C_V('C_K(Vi)) = Vi by rewrite inE; case: eqP.
have maxSK Vi: Vi \in S -> maximal 'C_K(Vi) K by case/setIdP.
have sSV Vi: Vi \in S -> Vi \subset V by move/defSV <-; rewrite subsetIl.
have ntSV Vi: Vi \in S -> Vi :!=: 1.
  move=> Si; apply: contraTneq (maxgroupp (maxSK _ Si)) => ->.
  by rewrite /= cent1T setIT proper_irrefl.
have nSK Vi: Vi \in S -> K \subset 'N(Vi).
  by move/defSV <-; rewrite normsI ?norms_cent // sub_abelian_norm ?subsetIl.
have defV: <<\bigcup_(Vi in S) Vi>> = V.
  apply/eqP; rewrite eqEsubset gen_subG.
  apply/andP; split; first by apply/bigcupsP; apply: sSV.
  rewrite -(coprime_abelian_gen_cent cKK nVK) ?(pnat_coprime pV) // gen_subG.
  apply/bigcupsP=> Kj /= /and3P[cycKbj sKjK nKjK].
  have [xb defKbj] := cyclicP cycKbj.
  have Kxb: xb \in K / Kj by rewrite defKbj cycle_id.
  set Vj := 'C_V(Kj); have [-> | ntVj] := eqsVneq Vj 1; first exact: sub1G.
  have nt_xb: xb != 1.
    apply: contra ntVj; rewrite -cycle_eq1 -defKbj -!subG1 -tiVcK.
    by rewrite quotient_sub1 // => sKKj; rewrite setIS ?centS.
  have maxKj: maximal Kj K.
    rewrite p_index_maximal // -card_quotient // defKbj -orderE.
    by rewrite (abelem_order_p (quotient_abelem Kj abelK) Kxb nt_xb).
  suffices defKj: 'C_K(Vj) = Kj.
    by rewrite sub_gen // (bigcup_max 'C_V(Kj))%G // inE defKj eqxx.
  have{maxKj} [_ maxKj] := maxgroupP maxKj.
  rewrite ['C_K(Vj)]maxKj //; last by rewrite subsetI sKjK centsC subsetIr.
  rewrite properEneq subsetIl andbT (sameP eqP setIidPl) centsC.
  by apply: contra ntVj; rewrite -subG1 -tiVcK subsetI subsetIl.
pose dxp := [fun D : {set {group gT}} => \big[dprod/1]_(Vi in D) Vi].
have{defV} defV: \big[dprod/1]_(Vi in S) Vi = V.
  have [D maxD]: {D | maxset [pred E | group_set (dxp E) & E \subset S] D}.
    by apply: ex_maxset; exists set0; rewrite /= sub0set big_set0 groupP.
  have [gW sDS] := andP (maxsetp maxD); have{maxD} [_ maxD] := maxsetP maxD.
  have{gW} [W /= defW]: {W : {group gT} | dxp D = W} by exists (Group gW).
  have [eqDS | ltDS] := eqVproper sDS.
    by rewrite eqDS in defW; rewrite defW -(bigdprodWY defW).
  have{ltDS} [_ [Vi Si notDi]] := properP ltDS.
  have sWV: W \subset V.
    rewrite -(bigdprodWY defW) gen_subG.
    by apply/bigcupsP=> Vj Dj; rewrite sSV ?(subsetP sDS).
  suffices{maxD sWV defV} tiWcKi: 'C_W('C_K(Vi)) = 1.
    have:= notDi; rewrite -(maxD (Vi |: D)) ?setU11 ?subsetUr //= subUset sDS.
    rewrite sub1set Si big_setU1 //= defW dprodEY ?groupP //.
      by rewrite (sub_abelian_cent2 cVV) // sSV.
    by rewrite -(defSV Vi Si) setIAC (setIidPr sWV).
  apply/trivgP/subsetP=> w /setIP[Ww cKi_w].
  have [v [Vv def_w v_uniq]] := mem_bigdprod defW Ww.
  rewrite def_w big1 ?inE // => Vj Dj; have Sj := subsetP sDS Vj Dj.
  have cKi_vj: v Vj \in 'C('C_K(Vi)).
    apply/centP=> x Ki_x; apply/commgP/conjg_fixP.
    apply: (v_uniq (fun Vk => v Vk ^ x)) => // [Vk Dk|].
      have [[Kx _] Sk]:= (setIP Ki_x, subsetP sDS Vk Dk).
      by rewrite memJ_norm ?Vv // (subsetP (nSK Vk Sk)).
    rewrite -(mulKg x w) -(centP cKi_w) // -conjgE def_w.
    by apply: (big_morph (conjg^~ x)) => [y z|]; rewrite ?conj1g ?conjMg.
  suffices mulKji: 'C_K(Vj) * 'C_K(Vi) = K.
    by apply/set1gP; rewrite -tiVcK -mulKji centM setIA defSV // inE Vv.
  have maxKj := maxSK Vj Sj; have [_ maxKi] := maxgroupP (maxSK Vi Si).
  rewrite (mulg_normal_maximal _ maxKj) -?sub_abelian_normal ?subsetIl //.
  have [eqVji|] := eqVneq Vj Vi; first by rewrite -eqVji Dj in notDi.
  apply: contra => /= sKiKj; rewrite -val_eqE /= -(defSV Vj Sj).
  by rewrite (maxKi _ (maxgroupp maxKj) sKiKj) defSV.
have nVPR: P <*> R \subset 'N(V) by rewrite join_subG nVP.
have actsPR: [acts P <*> R, on S | 'JG].
  apply/subsetP=> x PRx; rewrite !inE; apply/subsetP=> Vi.
  rewrite !inE /= => Si; rewrite -(normsP nKPR x PRx) !centJ -!conjIg centJ .
  by rewrite -(normsP nVPR x PRx) -conjIg (inj_eq (@conjsg_inj _ _)) maximalJ.
have transPR: [transitive P <*> R, on S | 'JG].
  pose ndxp D (U A B : {group gT}) := dxp (S :&: D) = U -> A * B \subset 'N(U).
  have nV_VK D U: ndxp D U V K.
    move/bigdprodWY <-; rewrite norms_gen ?norms_bigcup //.
    apply/bigcapsP=> Vi /setIP[Si _].
    by rewrite mulG_subG nSK // sub_abelian_norm // sSV.
  have nV_PR D U: [acts P <*> R, on S :&: D | 'JG] -> ndxp D U P R.
    move=> actsU /bigdprodWY<-; rewrite -norm_joinEr ?norms_gen //.
    apply/subsetP=> x PRx; rewrite inE sub_conjg; apply/bigcupsP=> Vi Di.
    by rewrite -sub_conjg (bigcup_max (Vi :^ x)%G) //= (acts_act actsU).
  have [S0 | [V1 S1]] := set_0Vmem S.
    by case/eqP: ntV; rewrite -defV S0 big_set0.
  apply/imsetP; exists V1 => //; set D := orbit _ _ _.
  rewrite (big_setID D) /= setDE in defV.
  have [[U W defU defW] _ _ tiUW] := dprodP defV.
  rewrite defU defW in defV tiUW.
  have [|U1|eqUV]:= indecomposableV _ _ defV.
  - rewrite -mulHR -defH -mulgA mul_subG //.
      by rewrite subsetI (nV_VK _ _ defU) (nV_VK _ _ defW).
    rewrite subsetI (nV_PR _ _ _ defU) ?actsI ?acts_orbit ?subsetT //=.
    by rewrite (nV_PR _ _ _ defW) // actsI ?astabsC ?acts_orbit ?subsetT /=.
  - case/negP: (ntSV V1 S1); rewrite -subG1 -U1 -(bigdprodWY defU) sub_gen //.
    by rewrite (bigcup_max V1) // inE S1 orbit_refl.
  apply/eqP; rewrite eqEsubset (acts_sub_orbit _ actsPR) S1 andbT.
  apply/subsetP=> Vi Si; apply: contraR (ntSV Vi Si) => D'i; rewrite -subG1.
  rewrite -tiUW eqUV subsetI sSV // -(bigdprodWY defW).
  by rewrite (bigD1 Vi) ?joing_subl // inE Si inE.
have [cSR | not_cSR] := boolP (R \subset 'C(S | 'JG)).
  have{cSR} sRnSV: R \subset \bigcap_(Vi in S) 'N(Vi).
    apply/bigcapsP=> Vi Si.
    by rewrite -astab1JG (subset_trans cSR) ?astabS ?sub1set.
  have sPRnSV: P <*> R \subset 'N(\bigcap_(Vi in S) 'N(Vi)).
    apply/subsetP=> x PRx; rewrite inE; apply/bigcapsP=> Vi Si.
    by rewrite sub_conjg -normJ bigcap_inf ?(acts_act actsPR) ?groupV.
  have [V1 S1] := imsetP transPR.
  have: P <*> R \subset 'N(V1).
    rewrite join_subG (subset_trans sRnSV) /= ?bigcap_inf // andbT -defP.
    apply: (subset_trans (commgS P sRnSV)).
    have:= subset_trans (joing_subl P R) sPRnSV; rewrite -commg_subr /=.
    move/subset_trans; apply; exact: bigcap_inf.
  rewrite -afixJG; move/orbit1P => -> allV1.
  have defV1: V1 = V by apply: group_inj; rewrite /= -defV allV1 big_set1.
  case/idPn: oKq2; rewrite -(Lagrange (subsetIl K 'C(V1))).
  rewrite (p_maximal_index qK (maxSK V1 S1)) defV1 /= tiKcV cards1 mul1n.
  by rewrite (ltn_exp2l 2 1).
have actsR: [acts R, on S | 'JG] := subset_trans (joing_subr P R) actsPR.
have ntSRcR Vi:
    Vi \in S -> ~~ (R \subset 'N(Vi)) ->
  #|Vi| = p /\ 'C_V(R) \subset <<class_support Vi R>>.
- move=> Si not_nViR; have [sVi nV] := (subsetP (sSV Vi Si), subsetP nVR).
  pose f v := fmval (\sum_(x in R) fmod cVV v ^@ x).
  have fM: {in Vi &, {morph f: u v / u * v}}.
    move=> u v /sVi Vu /sVi Vv; rewrite -fmvalA -big_split.
    by congr (fmval _); apply: eq_bigr => x Rx; rewrite /= -actAr fmodM.
  have injf: 'injm (Morphism fM).
    apply/subsetP=> v /morphpreP[Vi_v]; have Vv := sVi v Vi_v.
    rewrite (bigD1 Vi) //= in defV; have [[_ W _ dW] _ _ _] := dprodP defV.
    have [u [w [_ _ uw Uuw]]] := mem_dprod defV (group1 V).
    case: (Uuw 1 1) => // [||u1 w1]; rewrite ?dW ?mulg1 // !inE eq_sym /f /=.
    move/eqP; rewrite (big_setD1 1) // actr1 ?fmodK // fmvalA //= fmval_sum.
    do [case/Uuw; rewrite ?dW ?fmodK -?u1 ?group_prod //] => [x R'x | ->] //.
    rewrite (nt_gen_prime _ R'x) ?cycle_subG ?oR // inE in not_nViR nVR actsR.
    rewrite fmvalJ ?fmodK // -(bigdprodWY dW) ?mem_gen //; apply/bigcupP.
    exists (Vi :^ x)%G; rewrite ?memJ_conjg // (astabs_act _ actsR) Si.
    by apply: contraNneq not_nViR => /congr_group->.
  have im_f: Morphism fM @* Vi \subset 'C_V(R).
    apply/subsetP=> _ /morphimP[v _ Vi_v ->]; rewrite inE fmodP.
    apply/centP=> x Rx; red; rewrite conjgC -fmvalJ ?nV //; congr (x * fmval _).
    rewrite {2}(reindex_acts 'R _ Rx) ?astabsR //= actr_sum.
    by apply: eq_bigr => y Ry; rewrite actrM ?nV.
  have defCVR: Morphism fM @* Vi = 'C_V(R).
    apply/eqP; rewrite eqEcard im_f (prime_nt_dvdP _ _ (cardSg im_f)) ?oCVR //=.
    by rewrite -trivg_card1 morphim_injm_eq1 ?ntSV.
  rewrite -oCVR -defCVR; split; first by rewrite card_injm.
  apply/subsetP=> _ /morphimP[v _ Vi_v ->] /=; rewrite /f fmval_sum.
  have Vv := sVi v Vi_v; apply: group_prod => x Rx.
  by rewrite fmvalJ ?fmodK ?nV // mem_gen // mem_imset2.
have{not_cSR} [V1 S1 not_nV1R]: exists2 V1, V1 \in S & ~~ (R \subset 'N(V1)).
  by move: not_cSR; rewrite astabC; case/subsetPn=> v; rewrite afixJG; exists v.
set D := orbit 'JG%act R V1.
have oD: #|D| = r by rewrite card_orbit astab1JG prime_TIg ?indexg1 ?oR.
have oSV Vi: Vi \in S -> #|Vi| = p.
  move=> Si; have [z _ ->]:= atransP2 transPR S1 Si.
  by rewrite cardJg; case/ntSRcR: not_nV1R.
have cSnS' Vi: Vi \in S -> 'N(Vi)^`(1) \subset 'C(Vi).
  move=> Si; rewrite der1_min ?cent_norm //= -ker_conj_aut.
  rewrite (isog_abelian (first_isog _)) (abelianS (Aut_conj_aut _ _)) //.
  by rewrite Aut_cyclic_abelian // prime_cyclic // oSV.
have nVjR Vj: Vj \in S :\: D -> 'C_K(Vj) = [~: K, R].
  case/setDP=> Sj notDj; set Kj := 'C_K(Vj).
  have [nVjR|] := boolP (R \subset 'N(Vj)).
    have{nVjR} sKRVj: [~: K, R] \subset Kj.
      rewrite subsetI {1}commGC commg_subr nKR.
      by rewrite (subset_trans _ (cSnS' Vj Sj)) // commgSS ?nSK.
    have iKj: #|K : Kj| = q by rewrite (p_maximal_index qK (maxSK Vj Sj)).
    have dxKR: [~: K, R] \x 'C_K(R) = K by rewrite coprime_abelian_cent_dprod.
    have{dxKR} [_ defKR _ tiKRcR] := dprodP dxKR.
    have Z_CK: Zgroup 'C_K(R) by apply: ZgroupS ZgrCHR; exact: setSI.
    have abelCKR: q.-abelem 'C_K(R) := abelemS (subsetIl _ _) abelK.
    have [qCKR _] := andP abelCKR.
    apply/eqP; rewrite eq_sym eqEcard sKRVj -(leq_pmul2r (ltnW q_gt1)).
    rewrite -{1}iKj Lagrange ?subsetIl // -{1}defKR (TI_cardMg tiKRcR).
    rewrite leq_pmul2l ?cardG_gt0 //= (card_pgroup qCKR).
    rewrite (leq_exp2l _ 1) // -abelem_cyclic // (forall_inP Z_CK) //.
    by rewrite (@p_Sylow _ q) // /pHall subxx indexgg qCKR.
  case/ntSRcR=> // _ sCVj; case/ntSRcR: not_nV1R => // _ sCV1.
  suffices trCVR: 'C_V(R) = 1 by rewrite -oCVR trCVR cards1 in p_pr.
  apply/trivgP; rewrite (big_setID D) in defV.
  have{defV} [[W U /= defW defU] _ _ <-] := dprodP defV.
  rewrite defW defU subsetI (subset_trans sCV1) /=; last first.
    rewrite class_supportEr -(bigdprodWY defW) genS //.
    apply/bigcupsP=> x Rx; rewrite (bigcup_max (V1 :^ x)%G) // inE.
    by rewrite (actsP actsR) //= S1 mem_imset.
  rewrite (subset_trans sCVj) // class_supportEr -(bigdprodWY defU) genS //.
  apply/bigcupsP=> x Rx; rewrite (bigcup_max (Vj :^ x)%G) // inE.
  by rewrite (actsP actsR) // Sj andbT (orbit_transr _ (mem_orbit 'JG Vj Rx)).
have sDS: D \subset S.
  by rewrite acts_sub_orbit //; apply: subset_trans actsPR; exact: joing_subr.
have [eqDS | ltDS] := eqVproper sDS.
  have [fix0 | [Vj cVjP]] := set_0Vmem 'Fix_(S | 'JG)(P).
    case/negP: p'r; rewrite eq_sym -dvdn_prime2 // -oD eqDS /dvdn.
    rewrite (pgroup_fix_mod pP (subset_trans (joing_subl P R) actsPR)).
    by rewrite fix0 cards0 mod0n.
  have{cVjP} [Sj nVjP] := setIP cVjP; rewrite afixJG in nVjP.
  case/negP: (ntSV Vj Sj); rewrite -subG1 -tiVcK subsetI sSV // centsC -defKP.
  by rewrite (subset_trans _ (cSnS' Vj Sj)) // commgSS ?nSK.
have [_ [Vj Sj notDj]] := properP ltDS.
have defS: S = Vj |: D.
  apply/eqP; rewrite eqEsubset andbC subUset sub1set Sj sDS.
  apply/subsetP=> Vi Si; rewrite !inE orbC /= -val_eqE /= -(defSV Vi Si).
  have [//|notDi] := boolP (Vi \in _); rewrite -(defSV Vj Sj) /=.
  by rewrite !nVjR // inE ?notDi ?notDj.
suffices: odd #|S| by rewrite defS cardsU1 (negPf notDj) /= oD -oR (oddSg sRG).
rewrite (dvdn_odd (atrans_dvd transPR)) // (oddSg _ oddG) //.
by rewrite join_subG (subset_trans sPH).
Qed.

End Theorem_3_6.

(* This is B & G, Theorem 3.7. *)
Theorem prime_Frobenius_sol_kernel_nil gT (G K R : {group gT}) :
   K ><| R = G -> solvable G -> prime #|R| -> 'C_K(R) = 1 -> nilpotent K.
Proof.
move=> defG solG R_pr regR.
elim: {K}_.+1 {-2}K (ltnSn #|K|) => // m IHm K leKm in G defG solG regR *.
have [nsKG sRG defKR nKR tiKR] := sdprod_context defG.
have [sKG nKG] := andP nsKG.
wlog ntK: / K :!=: 1 by case: eqP => [-> _ | _ ->] //; exact: nilpotent1.
have [L maxL _]: {L : {group gT} | maxnormal L K G & [1] \subset L}.
  by apply: maxgroup_exists; rewrite proper1G ntK norms1.
have [ltLK nLG]:= andP (maxgroupp maxL); have [sLK not_sKL]:= andP ltLK.
have{m leKm IHm}nilL: nilpotent L.
  pose G1 := L <*> R; have nLR := subset_trans sRG nLG.
  have sG1G: G1 \subset G by rewrite join_subG (subset_trans sLK).
  have defG1: L ><| R = G1.
    by rewrite sdprodEY //; apply/eqP; rewrite -subG1 -tiKR setSI.
  apply: (IHm _ _ _ defG1); rewrite ?(solvableS sG1G) ?(oddSg sG1G) //.
    exact: leq_trans (proper_card ltLK) _.
  by apply/eqP; rewrite -subG1 -regR setSI.
have sLG := subset_trans sLK sKG; have nsLG: L <| G by apply/andP.
have sLF: L \subset 'F(G) by apply: Fitting_max.
have frobG: [Frobenius G = K ><| R] by apply/prime_FrobeniusP.
have solK := solvableS sKG solG.
have frobGq := Frobenius_quotient frobG solK nsLG not_sKL.
suffices sKF: K \subset 'F(K) by apply: nilpotentS sKF (Fitting_nil K).
apply: subset_trans (chief_stab_sub_Fitting solG nsKG).
rewrite subsetI subxx; apply/bigcapsP=> [[X Y] /= /andP[chiefXY sXF]].
set V := X / Y; have [maxY nsXG] := andP chiefXY.
have [ltYX nYG] := andP (maxgroupp maxY); have [sYX _]:= andP ltYX.
have [sXG nXG] := andP nsXG; have sXK := subset_trans sXF (Fitting_sub K).
have minV := chief_factor_minnormal chiefXY.
have cVL: L \subset 'C(V | 'Q).
  apply: subset_trans (subset_trans sLF (Fitting_stab_chief solG _)) _ => //.
  exact: (bigcap_inf (X, Y)).
have nVG: {acts G, on group V | 'Q}.
  by split; rewrite ?quotientS ?subsetT // actsQ // normal_norm.
pose V1 := sdpair1 <[nVG]> @* V.
have [p p_pr abelV]: exists2 p, prime p & p.-abelem V.
  apply/is_abelemP; apply: charsimple_solvable (quotient_sol _ _).
    exact: minnormal_charsimple minV.
  exact: nilpotent_sol (nilpotentS sXF (Fitting_nil _)).
have abelV1: p.-abelem V1 by rewrite morphim_abelem.
have injV1 := injm_sdpair1 <[nVG]>.
have ntV1: V1 :!=: 1.
  by rewrite -cardG_gt1 card_injm // cardG_gt1; case/andP: (mingroupp minV).
have nV1_G1 := im_sdpair_norm <[nVG]>.
pose rV := morphim_repr (abelem_repr abelV1 ntV1 nV1_G1) (subxx G).
have def_kerV: rker rV = 'C_G(V | 'Q).
  rewrite rker_morphim rker_abelem morphpreIdom morphpreIim -astabEsd //.
  by rewrite astab_actby setIid.
have kerL: L \subset rker rV by rewrite def_kerV subsetI sLG.
pose rVq := quo_repr kerL nLG.
suffices: K / L \subset rker rVq.
  rewrite rker_quo def_kerV quotientSGK //= 1?subsetI 1?(subset_trans sKG) //.
  by rewrite sLG.
have irrVq: mx_irreducible rVq.
  apply/quo_mx_irr; apply/morphim_mx_irr; apply/abelem_mx_irrP.
  apply/mingroupP; rewrite ntV1; split=> // U1; case/andP=> ntU1 nU1G sU1V.
  rewrite -(morphpreK sU1V); congr (_ @* _).
  case/mingroupP: minV => _; apply; last by rewrite sub_morphpre_injm.
  rewrite -subG1 sub_morphpre_injm ?sub1G // morphim1 subG1 ntU1 /=.
  set U := _ @*^-1 U1; rewrite -(cosetpreK U) quotient_norms //.
  have: [acts G, on U | <[nVG]>] by rewrite actsEsd ?subsetIl // morphpreK.
  rewrite astabs_actby subsetI subxx (setIidPr _) ?subsetIl //=.
  by rewrite -{1}(cosetpreK U) astabsQ ?normal_cosetpre //= -/U subsetI nYG.
have [q q_pr abelKq]: exists2 q, prime q & q.-abelem (K / L).
  apply/is_abelemP; apply: charsimple_solvable (quotient_sol _ solK).
  exact: maxnormal_charsimple maxL.
case (eqVneq q p) => [def_q | neq_qp].
  have sKGq: K / L \subset G / L by apply: quotientS.
  rewrite rfix_mx_rstabC //; have [_ _]:= irrVq; apply; rewrite ?submx1 //.
    by rewrite normal_rfix_mx_module ?quotient_normal.
  rewrite -(rfix_subg _ sKGq) (@rfix_pgroup_char _ p) ?char_Fp -?def_q //.
  exact: (abelem_pgroup abelKq).
suffices: rfix_mx rVq (R / L) == 0.
  apply: contraLR; apply: (Frobenius_rfix_compl frobGq).
  apply: pi_pnat (abelem_pgroup abelKq) _.
  by rewrite inE /= (charf_eq (char_Fp p_pr)).
rewrite -mxrank_eq0 (rfix_quo _ _ sRG) (rfix_morphim _ _ sRG).
rewrite (rfix_abelem _ _ _ (morphimS _ sRG)) mxrank_eq0 rowg_mx_eq0 -subG1.
rewrite (sub_abelem_rV_im _ _ _ (subsetIl _ _)) -(morphpreSK _ (subsetIl _ _)).
rewrite morphpreIim -gacentEsd gacent_actby gacentQ (setIidPr sRG) /=.
rewrite -coprime_quotient_cent ?(solvableS sXG) ?(subset_trans sRG) //.
  by rewrite {1}['C_X(R)](trivgP _) ?quotient1 ?sub1G // -regR setSI.
by apply: coprimeSg sXK _; apply: Frobenius_coprime frobG.
Qed.

Corollary Frobenius_sol_kernel_nil gT (G K H : {group gT}) :
  [Frobenius G = K ><| H] -> solvable G -> nilpotent K.
Proof.
move=> frobG solG; have [defG ntK ntH _ _] := Frobenius_context frobG.
have{defG} /sdprodP[_ defG nKH tiKH] := defG.
have[H1 | [p p_pr]] := trivgVpdiv H; first by case/eqP: ntH.
case/Cauchy=> // x Hx ox; rewrite -ox in p_pr.
have nKx: <[x]> \subset 'N(K) by rewrite cycle_subG (subsetP nKH).
have tiKx: K :&: <[x]> = 1 by apply/trivgP; rewrite -tiKH setIS ?cycle_subG.
apply: (prime_Frobenius_sol_kernel_nil (sdprodEY nKx tiKx)) => //.
  by rewrite (solvableS _ solG) // join_subG -mulG_subG -defG mulgS ?cycle_subG.
by rewrite cent_cycle (Frobenius_reg_ker frobG) // !inE -order_gt1 prime_gt1.
Qed.

(* This is B & G, Theorem 3.8. *)
Theorem odd_sdprod_primact_commg_sub_Fitting gT (G K R : {group gT}) :
    K ><| R = G -> odd #|G| -> solvable G ->
  (*1*) coprime #|K| #|R| ->
  (*2*) semiprime K R ->
  (*3*) 'C_('F(K))(R) = 1 ->
  [~: K, R] \subset 'F(K).
Proof.
elim: {G}_.+1 {-2}G (ltnSn #|G|) K R => // n IHn G.
rewrite ltnS => leGn K R defG oddG solG coKR primR regR_F.
have [nsKG sRG defKR nKR tiKR] := sdprod_context defG.
have [sKG nKG] := andP nsKG.
have chF: 'F(K) \char K := Fitting_char K; have nFR := char_norm_trans chF nKR.
have nsFK := char_normal chF; have [sFK nFK] := andP nsFK.
pose KqF := K / 'F(K); have solK := solvableS sKG solG.
without loss [p p_pr pKqF]: / exists2 p, prime p & p.-group KqF.
  move=> IHp;  apply: wlog_neg => IH_KR; rewrite -quotient_cents2 //= -/KqF.
  set Rq := R / 'F(K); have nKRq: Rq \subset 'N(KqF) by exact: quotient_norms.
  rewrite centsC.
  apply: subset_trans (coprime_cent_Fitting nKRq _ _); last first.
  - exact: quotient_sol.
  - exact: coprime_morph.
  rewrite subsetI subxx centsC -['F(KqF)]Sylow_gen gen_subG.
  apply/bigcupsP=> Pq /SylowP[p p_pr /= sylPq]; rewrite -/KqF in sylPq.
  have chPq: Pq \char KqF.
   apply: char_trans (Fitting_char _); rewrite /= -/KqF.
    by rewrite (nilpotent_Hall_pcore (Fitting_nil _) sylPq) ?pcore_char.
  have [P defPq sFP sPK] := inv_quotientS nsFK (char_sub chPq).
  have nsFP: 'F(K) <| P by rewrite /normal sFP (subset_trans sPK).
  have{chPq} chP: P \char K.
    by apply: char_from_quotient nsFP (Fitting_char _) _; rewrite -defPq.
  have defFP: 'F(P) = 'F(K).
    apply/eqP; rewrite eqEsubset !Fitting_max ?Fitting_nil //.
    by rewrite char_normal ?(char_trans (Fitting_char _)).
  have coPR := coprimeSg sPK coKR.
  have nPR: R \subset 'N(P) := char_norm_trans chP nKR.
  pose G1 := P <*> R.
  have sG1G: G1 \subset G by rewrite /G1 -defKR norm_joinEr ?mulSg.
  have defG1: P ><| R = G1 by rewrite sdprodEY ?coprime_TIg.
  rewrite defPq quotient_cents2r //= -defFP.
  have:= sPK; rewrite subEproper; case/predU1P=> [defP | ltPK].
    rewrite IHp // in IH_KR; exists p => //.
    by rewrite /KqF -{2}defP -defPq (pHall_pgroup sylPq).
  move/IHn: defG1 => ->; rewrite ?(oddSg sG1G) ?(solvableS sG1G) ?defFP //.
    apply: leq_trans leGn; rewrite /= norm_joinEr //.
    by rewrite -defKR !coprime_cardMg // ltn_pmul2r ?proper_card.
  by move=> x Rx; rewrite -(setIidPl sPK) -!setIA primR.
without loss r_pr: / prime #|R|; last set r := #|R| in r_pr.
  have [-> _ | [r r_pr]] := trivgVpdiv R; first by rewrite commG1 sub1G.
  case/Cauchy=> // x; rewrite -cycle_subG subEproper orderE; set X := <[x]>.
  case/predU1P=> [-> -> -> // | ltXR rX _]; have sXR := proper_sub ltXR.
  have defCX: 'C_K(X) = 'C_K(R).
    rewrite cent_cycle primR // !inE -order_gt1 orderE rX prime_gt1 //=.
    by rewrite -cycle_subG.
  have primX: semiprime K X.
    by move=> y; case/setD1P=> nty Xy; rewrite primR // !inE nty (subsetP sXR).
  have nKX := subset_trans sXR nKR; have coKX := coprimegS sXR coKR.
  pose H := K <*> X; have defH: K ><| X = H by rewrite sdprodEY ?coprime_TIg.
  have sHG: H \subset G by rewrite /H -defKR norm_joinEr ?mulgSS.
  have ltHn: #|H| < n.
    rewrite (leq_trans _ leGn) /H ?norm_joinEr // -defKR !coprime_cardMg //.
    by rewrite ltn_pmul2l ?proper_card.
  have oddH := oddSg sHG oddG; have solH := solvableS sHG solG.
  have regX_F: 'C_('F(K))(X) = 1.
   by rewrite -regR_F -(setIidPl sFK) -!setIA defCX.
  have:= IHn _ ltHn _ _ defH oddH solH coKX primX regX_F.
  rewrite -!quotient_cents2 ?(subset_trans sXR) //; move/setIidPl <-.
  rewrite -coprime_quotient_cent ?(subset_trans sXR) // defCX.
  by rewrite coprime_quotient_cent ?subsetIr.
apply: subset_trans (chief_stab_sub_Fitting solG nsKG) => //.
rewrite subsetI commg_subl nKR; apply/bigcapsP => [[U V]] /=.
case/andP=> chiefUV sUF; set W := U / V.
have minW := chief_factor_minnormal chiefUV.
have [ntW nWG] := andP (mingroupp minW).
have /andP[/maxgroupp/andP[/andP[sVU _] nVG] nsUG] := chiefUV.
have sUK := subset_trans sUF sFK; have sVK := subset_trans sVU sUK.
have nVK := subset_trans sKG nVG; have nVR := subset_trans sRG nVG.
have [q q_pr abelW]: exists2 q, prime q & q.-abelem W.
  apply/is_abelemP; apply: charsimple_solvable (minnormal_charsimple minW) _.
  by rewrite quotient_sol // (solvableS sUK).
have regR_W: 'C_(W)(R / V) = 1.
  rewrite -coprime_quotient_cent ?(coprimeSg sUK) ?(solvableS sUK) //.
  by rewrite -(setIidPl sUF) -setIA regR_F (setIidPr _) ?quotient1 ?sub1G.
rewrite sub_astabQ comm_subG ?quotientR //=.
have defGv: (K / V) * (R / V) = G / V by rewrite -defKR quotientMl.
have oRv: #|R / V| = r.
  rewrite card_quotient // -indexgI -(setIidPr sVK) setICA setIA tiKR.
  by rewrite (setIidPl (sub1G _)) indexg1.
have defCW: 'C_(G / V)(W) = 'C_(K / V)(W).
  apply/eqP; rewrite eqEsubset andbC setSI ?quotientS //=.
  rewrite subsetI subsetIr /= andbT.
  rewrite -(coprime_mulG_setI_norm defGv) ?coprime_morph ?norms_cent //=.
  suffices ->: 'C_(R / V)(W) = 1 by rewrite mulg1 subsetIl.
  apply/trivgP; apply/subsetP=> x; case/setIP=> Rx cWx.
  apply: contraR ntW => ntx; rewrite -subG1 -regR_W subsetI subxx centsC /= -/W.
  by apply: contraR ntx; move/prime_TIg <-; rewrite ?oRv // inE Rx.
have [P sylP nPR] := coprime_Hall_exists p nKR coKR solK.
have [sPK pP _] := and3P sylP.
have nVP := subset_trans sPK nVK; have nFP := subset_trans sPK nFK.
have sylPv: p.-Sylow(K / V) (P / V) by rewrite quotient_pHall.
have defKv: (P / V) * 'C_(G / V)(W) = (K / V).
  rewrite defCW; apply/eqP; rewrite eqEsubset mulG_subG subsetIl quotientS //=.
  have sK_PF: K \subset P * 'F(K).
    rewrite (normC nFP) -quotientSK // subEproper eq_sym eqEcard quotientS //=.
    by rewrite (card_Hall (quotient_pHall nFP sylP)) part_pnat_id ?leqnn.
  rewrite (subset_trans (quotientS _ sK_PF)) // quotientMl // mulgS //.
  rewrite subsetI -quotient_astabQ !quotientS //.
  by rewrite (subset_trans (Fitting_stab_chief solG nsKG)) ?(bigcap_inf (U, V)).
have nW_ := subset_trans (quotientS _ _) nWG; have nWK := nW_ _ sKG. 
rewrite -quotient_cents2 ?norms_cent ?(nW_ _ sRG) //.
have [eq_qp | p'q] := eqVneq q p.
  apply: subset_trans (sub1G _); rewrite -trivg_quotient quotientS // centsC.
  apply/setIidPl; case/mingroupP: minW => _; apply; last exact: subsetIl.
  rewrite andbC normsI ?norms_cent // ?quotient_norms //=.
  have nsWK: W <| K / V by rewrite /normal quotientS.
  have sWP: W \subset P / V.
    by rewrite (normal_sub_max_pgroup (Hall_max sylPv)) -?eq_qp ?abelem_pgroup.
  rewrite -defKv centM setIA setIAC /=.
  rewrite ['C_W(_)](setIidPl _); last by rewrite centsC subsetIr.
  have nilPv: nilpotent (P / V) := pgroup_nil (pHall_pgroup sylPv).
  rewrite -/W -(setIidPl sWP) -setIA meet_center_nil //.
  exact: normalS (quotientS V sPK) nsWK.
rewrite -defKv -quotientMidr -mulgA mulSGid ?subsetIr // quotientMidr.
have sPG := subset_trans sPK sKG.
rewrite quotient_cents2 ?norms_cent ?nW_ //= commGC.
pose Hv := (P / V) <*> (R / V).
have sHGv: Hv \subset G / V by rewrite join_subG !quotientS.
have solHv: solvable Hv := solvableS sHGv (quotient_sol V solG).
have sPHv: P / V \subset Hv by exact: joing_subl.
have nPRv: R / V \subset 'N(P / V) := quotient_norms _ nPR.
have coPRv: coprime #|P / V| #|R / V| := coprime_morph _ (coprimeSg sPK coKR).
apply: subset_trans (subsetIr (P / V) _).
have oHv: #|Hv| = (#|P / V| * #|R / V|)%N.
  by rewrite /Hv norm_joinEr // coprime_cardMg // oRv.
move/(odd_prime_sdprod_abelem_cent1 solHv): (abelW); apply=> //.
- exact: oddSg sHGv (quotient_odd _ _).
- by rewrite sdprodEY ?quotient_norms // coprime_TIg.
- by rewrite oRv.
- by rewrite (subset_trans _ nWG) ?join_subG ?quotientS.
rewrite /= norm_joinEr // pgroupM /pgroup.
rewrite (pi_pnat (quotient_pgroup _ pP)) ?inE 1?eq_sym //=.
apply: coprime_p'group (abelem_pgroup abelW) ntW.
by rewrite coprime_sym coprime_morph // (coprimeSg sUK).
Qed.

(* This is B & G, Proposition 3.9 (for external action), with the incorrectly *)
(* omitted nontriviality assumption reinstated.                               *)
Proposition ext_odd_regular_pgroup_cyclic (aT rT : finGroupType) p
              (D R : {group aT}) (K H : {group rT}) (to : groupAction D K) :
    p.-group R -> odd #|R| -> H :!=: 1 ->
    {acts R, on group H | to} -> {in R^#, forall x, 'C_(H | to)[x] = 1} ->
  cyclic R.
Proof.
move: R H => R0 H0 pR0 oddR0 ntH0 actsR0 regR0.
pose gT := sdprod_groupType <[actsR0]>.
pose H : {group gT} := (sdpair1 <[actsR0]> @* H0)%G.
pose R : {group gT} := (sdpair2 <[actsR0]> @* R0)%G.
pose G : {group gT} := [set: gT]%G.
have{pR0} pR: p.-group R by rewrite morphim_pgroup.
have{oddR0} oddR: odd #|R| by rewrite morphim_odd.
have [R1 | ntR] := eqsVneq R 1.
  by rewrite -(im_invm (injm_sdpair2 <[actsR0]>)) {2}R1 morphim1 cyclic1.
have{ntH0} ntH: H :!=: 1.
  apply: contraNneq ntH0 => H1.
  by rewrite -(im_invm (injm_sdpair1 <[actsR0]>)) {2}H1 morphim1.
have{regR0 ntR} frobG: [Frobenius G = H ><| R].
  apply/Frobenius_semiregularP => // [|x]; first exact: sdprod_sdpair.
  case/setD1P=> nt_x; case/morphimP=> x2 _ Rx2 def_x.
  apply/trivgP; rewrite -(morphpreSK _ (subsetIl _ _)) morphpreI.
  rewrite /= -cent_cycle def_x -morphim_cycle // -gacentEsd.
  rewrite injmK ?injm_sdpair1 // (trivgP (injm_sdpair1 _)).
  rewrite -(regR0 x2) ?inE ?Rx2 ?andbT; last first.
    by apply: contra nt_x; rewrite def_x; move/eqP->; rewrite morph1.
  have [sRD sHK]: R0 \subset D /\ H0 \subset K by case actsR0; move/acts_dom.
  have sx2R: <[x2]> \subset R0 by rewrite cycle_subG.
  rewrite gacent_actby setIA setIid (setIidPr sx2R).
  rewrite !gacentE ?cycle_subG ?sub1set ?(subsetP sRD) //.
  by rewrite !setIS ?afixS ?sub_gen.
suffices: cyclic R by rewrite (injm_cyclic (injm_sdpair2 _)).
move: gT H R G => {aT rT to D K H0 R0 actsR0} gT H R G in ntH pR oddR frobG *.
have [defG _ _ _ _] := Frobenius_context frobG; case/sdprodP: defG => _ _ nHR _.
have coHR := Frobenius_coprime frobG.
rewrite (odd_pgroup_rank1_cyclic pR oddR) leqNgt.
apply: contra ntH => /p_rank_geP[E /pnElemP[sER abelE dimE2]].
have ncycE: ~~ cyclic E by rewrite (abelem_cyclic abelE) dimE2.
have nHE := subset_trans sER nHR; have coHE := coprimegS sER coHR.
rewrite -subG1 -(coprime_abelian_gen_cent1 _ _ nHE) ?(abelem_abelian abelE) //.
rewrite -bigprodGE big1 // => x /setD1P[nt_x Ex]; apply: val_inj => /=.
by apply: (Frobenius_reg_ker frobG); rewrite !inE nt_x (subsetP sER).
Qed.

(* Internal action version of B & G, Proposition 3.9 (possibly, the only one  *)
(* we should keep). *)
Proposition odd_regular_pgroup_cyclic gT p (H R : {group gT}) :
    p.-group R -> odd #|R| -> H :!=: 1 -> R \subset 'N(H) -> semiregular H R ->
  cyclic R.
Proof.
move=> pR oddR ntH nHR regR.
have actsR: {acts R, on group H | 'J} by split; rewrite ?subsetT ?astabsJ.
apply: ext_odd_regular_pgroup_cyclic pR oddR ntH actsR _ => // x Rx.
by rewrite gacentJ cent_set1 regR.
Qed.

(* Another proof of Proposition 3.9, which avoids Frobenius groups entirely.  *)
Proposition simple_odd_regular_pgroup_cyclic gT p (H R : {group gT}) :
    p.-group R -> odd #|R| -> H :!=: 1 -> R \subset 'N(H) -> semiregular H R ->
  cyclic R.
Proof.
move=> pR oddR ntH nHR regR; rewrite (odd_pgroup_rank1_cyclic pR oddR) leqNgt.
apply: contra ntH => /p_rank_geP[E /pnElemP[sER abelE dimE2]].
have ncycE: ~~ cyclic E by rewrite (abelem_cyclic abelE) dimE2.
have nHE := subset_trans sER nHR.
have coHE := coprimegS sER (regular_norm_coprime nHR regR).
rewrite -subG1 -(coprime_abelian_gen_cent1 _ _ nHE) ?(abelem_abelian abelE) //.
rewrite -bigprodGE big1 // => x; case/setD1P=> nt_x Ex; apply: val_inj => /=.
by rewrite regR // !inE nt_x (subsetP sER).
Qed.

(* This is Aschbacher (40.6)(4). *)
Lemma odd_regular_metacyclic gT (H R : {group gT}) :
    odd #|R| -> H :!=: 1 -> R \subset 'N(H) -> semiregular H R ->
  metacyclic R.
Proof.
move=> oddR ntH nHR regHR.
apply/Zgroup_metacyclic/forall_inP=> P /SylowP[p pr_p /and3P[sPR pP _]].
have [oddP nHP] := (oddSg sPR oddR, subset_trans sPR nHR).
exact: odd_regular_pgroup_cyclic pP oddP ntH nHP (semiregularS _ sPR regHR).
Qed.

(* This is Huppert, Kapitel V, Satz 18.8 b (used in Peterfalvi, Section 13). *)
Lemma prime_odd_regular_normal gT (H R P : {group gT}) :
    prime #|P| -> odd #|R| -> P \subset R ->
    H :!=: 1 -> R \subset 'N(H) -> semiregular H R ->
  P <| R.
Proof.
set p := #|P| => pr_p oddR sPR ntH nHR regHR.
have pP: p.-group P := pnat_id pr_p.
have cycQ (q : nat) (Q : {group gT}) : q.-group Q -> Q \subset R -> cyclic Q.
  move=> qQ sQR; have [oddQ nHQ] := (oddSg sQR oddR, subset_trans sQR nHR).
  exact: odd_regular_pgroup_cyclic qQ oddQ ntH nHQ (semiregularS _ sQR regHR).
have cycRq (q : nat): cyclic 'O_q(R) by rewrite (cycQ q) ?pcore_pgroup ?gFsub.
suffices cFP: P \subset 'C('F(R)).
  have nilF: nilpotent 'F(R) := Fitting_nil R.
  have hallRp: p.-Hall('F(R)) 'O_p('F(R)) := nilpotent_pcore_Hall p nilF.
  apply: char_normal_trans (pcore_normal p R); rewrite sub_cyclic_char //=.
  rewrite -p_core_Fitting (sub_normal_Hall hallRp) ?gFnormal //.
  have solR: solvable R.
    by apply: metacyclic_sol; apply: odd_regular_metacyclic regHR.
  by apply: subset_trans (cent_sub_Fitting solR); rewrite subsetI sPR.
rewrite centsC -(bigdprodWY (erefl 'F(R))) gen_subG big_tnth.
apply/bigcupsP=> i _; move: {i}(tuple.tnth _ i) => q.
have [<- | q'p] := eqVneq p q.
  have [Q sylQ sPQ] := Sylow_superset sPR pP; have [sQR pQ _] := and3P sylQ.
  rewrite (sub_abelian_cent2 (cyclic_abelian (cycQ _ _ pQ sQR))) //.
  by rewrite pcore_sub_Hall.
have [-> | ntRq] := eqVneq 'O_q(R) 1%g; first exact: sub1G.
have /andP[sRqR qRq]: q.-subgroup(R) 'O_q(R) by apply: pcore_psubgroup.
have [pr_q _ _] := pgroup_pdiv qRq ntRq.
have coRqP: coprime #|'O_q(R)| p by rewrite (pnat_coprime qRq) // pnatE.
have nRqP: P \subset 'N('O_q(R)) by rewrite (subset_trans sPR) ?gFnorm.
rewrite centsC (coprime_odd_faithful_Ohm1 qRq) ?(oddSg sRqR) //.
apply: sub_abelian_cent2 (joing_subl _ _) (joing_subr _ _) => /=.
set PQ := P <*> _; have oPQ: #|PQ| = (p * q)%N.
  rewrite /PQ norm_joinEl ?(char_norm_trans (Ohm_char 1 _)) //.
  rewrite coprime_cardMg 1?coprime_sym ?(coprimeSg (Ohm_sub 1 _)) // -/p.
  by congr (p * _)%N; apply: Ohm1_cyclic_pgroup_prime => /=.
have sPQ_R: PQ \subset R by rewrite join_subG sPR (subset_trans (Ohm_sub 1 _)).
have nH_PQ := subset_trans sPQ_R nHR.
apply: cyclic_abelian; apply: regular_pq_group_cyclic oPQ ntH nH_PQ _ => //.
exact: semiregularS regHR.
Qed.

Section Wielandt_Frobenius.

Variables (gT : finGroupType) (G K R : {group gT}).
Implicit Type A : {group gT}.

(* This is Peterfalvi (9.1). *)
Lemma Frobenius_Wielandt_fixpoint (M : {group gT}) :
    [Frobenius G = K ><| R] ->
    G \subset 'N(M) -> coprime #|M| #|G| -> solvable M ->
 [/\ (#|'C_M(G)| ^ #|R| * #|M| = #|'C_M(R)| ^ #|R| * #|'C_M(K)|)%N,
     'C_M(R) = 1 -> K \subset 'C(M)
   & 'C_M(K) = 1 -> (#|M| = #|'C_M(R)| ^ #|R|)%N].
Proof.
move=> frobG nMG coMG solM; have [defG _ ntR _ _] := Frobenius_context frobG.
have [_ _ _ _ /eqP snRG] := and5P frobG.
have [nsKG sRG _ _ tiKR] := sdprod_context defG; have [sKG _] := andP nsKG.
pose m0 (_ : {group gT}) := 0%N.
pose Dm := [set 1%G; G]; pose Dn := K |: orbit 'JG K R.
pose m := [fun A => 0%N with 1%G |-> #|K|, G |-> 1%N].
pose n A : nat := A \in Dn.
have out_m: {in [predC Dm], m =1 m0}.
  by move=> A; rewrite !inE /=; case/norP; do 2!move/negbTE->.
have out_n: {in [predC Dn], n =1 m0}.
  by rewrite /n => A /=; move/negbTE=> /= ->.
have ntG: G != 1%G by case: eqP sRG => // -> <-; rewrite subG1.
have neqKR: K \notin orbit 'JG K R.
  apply/imsetP=> [[x _ defK]]; have:= Frobenius_dvd_ker1 frobG.
  by rewrite defK cardJg gtnNdvd // ?prednK // -subn1 subn_gt0 cardG_gt1.
have Gmn A: m A + n A > 0 -> A \subset G.
  rewrite /=; case: eqP => [-> | ] _; first by rewrite sub1G.
  rewrite /n 2!inE; do 2!case: eqP => [-> // | ] _.
  case R_A: (A \in _) => // _; case/imsetP: R_A => x Kx ->{A}.
  by rewrite conj_subG ?(subsetP sKG).
have partG: {in G, forall a,
  \sum_(A | a \in gval A) m A = \sum_(A | a \in gval A) n A}%N.
- move=> a Ga; have [-> | nt_a] := eqVneq a 1.
    rewrite (bigD1 1%G) ?inE ?eqxx //= (bigD1 G) ?inE ?group1 //=.
    rewrite (negbTE ntG) !eqxx big1 ?addn1 => [|A]; last first.
      by rewrite group1 -negb_or -in_set2; apply: out_m.
    rewrite (bigID (mem Dn)) /= addnC big1 => [|A]; last first.
      by rewrite group1; apply: out_n.
    transitivity #|Dn|.
      rewrite cardsU1 neqKR card_orbit astab1JG.
      by rewrite -{3}(setIidPl sKG) -setIA -normD1 snRG tiKR indexg1.
    by rewrite -sum1_card /n; apply: eq_big => [A | A ->]; rewrite ?group1.
  rewrite (bigD1 G) //= (negbTE ntG) eqxx big1 => [|A]; last first.
    case/andP=> Aa neAG; apply: out_m; rewrite !inE; case: eqP => // A1.
    by rewrite A1 inE (negbTE nt_a) in Aa.
  have [partG tiG _] := and3P (Frobenius_partition frobG).
  do [rewrite -(eqP partG); set pG := _ |: _] in Ga tiG.
  rewrite (bigD1 <<pblock pG a>>%G) /=; last by rewrite mem_gen // mem_pblock.
  rewrite big1 => [|B]; last first.
    case/andP=> Ba neqBA; rewrite -/(false : nat); congr (nat_of_bool _).
    apply: contraTF neqBA; rewrite negbK -val_eqE /=.
    case/setU1P=> [BK | /imsetP[x Kx defB]].
      by rewrite (def_pblock tiG _ Ba) BK ?setU11 ?genGid.
    have Rxa: a \in R^# :^ x by rewrite conjD1g !inE nt_a -(congr_group defB).
    rewrite (def_pblock tiG _ Rxa) ?setU1r ?mem_imset // conjD1g.
    by rewrite genD1 ?group1 // genGid defB.
  rewrite /n !inE -val_eqE /= -/(true : nat); congr ((_ : bool) + _)%N.
  case/setU1P: (pblock_mem Ga) => [-> |]; first by rewrite genGid eqxx.
  case/imsetP=> x Kx ->; symmetry; apply/orP; right.
  apply/imsetP; exists x => //.
  by apply: val_inj; rewrite conjD1g /= genD1 ?group1 // genGid.
move/eqP: (solvable_Wielandt_fixpoint Gmn nMG coMG solM partG).
rewrite (bigD1 1%G) // (bigD1 G) //= eqxx (setIidPl (cents1 _)) cards1 muln1.
rewrite (negbTE ntG) eqxx mul1n -(sdprod_card defG) (mulnC #|K|) expnM.
rewrite mulnA -expnMn big1 ?muln1 => [|A]; last first.
  by rewrite -negb_or -in_set2; move/out_m; rewrite /m => /= ->.
rewrite mulnC eq_sym (bigID (mem Dn)) /= mulnC.
rewrite big1 ?mul1n => [|A]; last by move/out_n->.
rewrite big_setU1 //= /n setU11 mul1n.
rewrite (eq_bigr (fun _ => #|'C_M(R)| ^ #|R|)%N) => [|A R_A]; last first.
  rewrite inE R_A orbT mul1n; case/imsetP: R_A => x Kx ->.
  suffices nMx: x \in 'N(M) by rewrite -{1}(normP nMx) centJ -conjIg !cardJg.
  exact: subsetP (subsetP sKG x Kx).
rewrite mulnC prod_nat_const card_orbit astab1JG.
have ->: 'N_K(R) = 1 by rewrite -(setIidPl sKG) -setIA -normD1 snRG tiKR.
rewrite indexg1 -expnMn eq_sym eqn_exp2r ?cardG_gt0 //; move/eqP=> eq_fix.
split=> // [regR | regK].
  rewrite centsC (sameP setIidPl eqP) eqEcard subsetIl /=.
  move: eq_fix; rewrite regR cards1 exp1n mul1n => <-.
  suffices ->: 'C_M(G) = 1 by rewrite cards1 exp1n mul1n.
  by apply/trivgP; rewrite -regR setIS ?centS //; case/sdprod_context: defG.
move: eq_fix; rewrite regK cards1 muln1 => <-.
suffices ->: 'C_M(G) = 1 by rewrite cards1 exp1n mul1n.
by apply/trivgP; rewrite -regK setIS ?centS.
Qed.

End Wielandt_Frobenius.

(* This is B & G, Theorem 3.10. *)
Theorem Frobenius_primact gT (G K R M : {group gT}) :
    [Frobenius G = K ><| R] -> solvable G ->
    G \subset 'N(M) -> solvable M -> M :!=: 1 ->
  (*1*) coprime #|M| #|G| ->
  (*2*) semiprime M R ->
  (*3*) 'C_M(K) = 1 ->
  [/\ prime #|R|,
      #|M| = (#|'C_M(R)| ^ #|R|)%N
    & cyclic 'C_M(R) -> K^`(1) \subset 'C_K(M)].
Proof.
move: {2}_.+1 (ltnSn #|M|) => n; elim: n => // n IHn in gT G K R M *.
rewrite ltnS => leMn frobG solG nMG solM ntM coMG primRM tcKM.
case: (Frobenius_Wielandt_fixpoint frobG nMG) => // _ _ /(_ tcKM) oM.
have [defG ntK ntR ltKG _]:= Frobenius_context frobG.
have Rpr: prime #|R|.
  have [R1 | [r r_pr]] := trivgVpdiv R; first by case/eqP: ntR.
  case/Cauchy=> // x Rx ox; pose R0 := <[x]>; pose G0 := K <*> R0.
  have [_ defKR nKR tiKR] := sdprodP defG.
  have sR0R: R0 \subset R by rewrite cycle_subG.
  have sG0G: G0 \subset G by rewrite /G0 -genM_join gen_subG -defKR mulgS.
  have nKR0 := subset_trans sR0R nKR; have nMG0 := subset_trans sG0G nMG.
  have ntx: <[x]> != 1 by rewrite cycle_eq1 -order_gt1 ox prime_gt1.
  have [tcRM | ntcRM] := eqVneq 'C_M(R) 1.
    by rewrite -cardG_gt1 oM tcRM cards1 exp1n in ntM.
  have frobG0: [Frobenius G0 = K ><| R0].
    apply/Frobenius_semiregularP=> // [|y /setD1P[nty x_y]].
      by apply: sdprodEY nKR0 (trivgP _); rewrite -tiKR setIS.
    by apply: (Frobenius_reg_ker frobG); rewrite !inE nty (subsetP sR0R).
  case: (Frobenius_Wielandt_fixpoint frobG0 nMG0 (coprimegS _ coMG)) => // _ _.
  move/(_ tcKM)/eqP; rewrite oM cent_cycle.
  rewrite primRM; last by rewrite !inE Rx andbT -cycle_eq1.
  by rewrite eqn_exp2l ?cardG_gt1 // -orderE ox => /eqP->.
split=> // cyc_cMR.
have nM_MG: M <*> G \subset 'N(M) by rewrite join_subG normG.
have [V minV sVM] := minnormal_exists ntM nM_MG.
have [] := minnormal_solvable minV sVM solM.
rewrite join_subG; case/andP=> nVM nVG ntV; case/is_abelemP=> [q q_pr abelV].
have coVG := coprimeSg sVM coMG; have solV := solvableS sVM solM.
have cVK': K^`(1) \subset 'C_K(V).
  case: (eqVneq 'C_V(R) 1) => [tcVR | ntcRV].
    case: (Frobenius_Wielandt_fixpoint frobG nVG) => // _.
    by move/(_ tcVR)=> cVK _; rewrite (setIidPl cVK) der_sub.
  have ocVR: #|'C_V(R)| = q.
    have [u def_u]: exists u, 'C_V(R) = <[u]>.
      by apply/cyclicP; apply: cyclicS (setSI _ sVM) cyc_cMR.
    rewrite def_u -orderE (abelem_order_p abelV) -?cycle_eq1 -?def_u //.
    by rewrite -cycle_subG -def_u subsetIl.
  apply: (Frobenius_prime_cent_prime _ defG _ _ abelV)  => //.
    by case/prime_FrobeniusP: frobG.
  by rewrite (coprime_p'group _ (abelem_pgroup abelV) ntV) // coprime_sym.
have cMK': K^`(1) / V \subset 'C_(K / V)(M / V).
  have [-> | ntMV] := eqVneq (M / V) 1.
    by rewrite subsetI cents1 quotientS ?der_sub.
  have coKR := Frobenius_coprime frobG.
  case/prime_FrobeniusP: frobG => //.
  case/sdprod_context=> nsKG sRG defKR nKR tiKR regR; have [sKG _] := andP nsKG.
  have nVK := subset_trans sKG nVG; have nVR := subset_trans sRG nVG.
  have RVpr: prime #|R / V|.
    rewrite card_quotient // -indexgI setIC coprime_TIg ?(coprimegS sRG) //.
    by rewrite indexg1.
  have frobGV: [Frobenius G / V = (K / V) ><| (R / V)].
    apply/prime_FrobeniusP; rewrite // -?cardG_gt1 ?card_quotient //.
      rewrite -indexgI setIC coprime_TIg ?(coprimegS sKG) //.
      by rewrite indexg1 cardG_gt1.
    rewrite -coprime_norm_quotient_cent ?(coprimegS sRG) //= regR quotient1.
    rewrite -defKR quotientMl // sdprodE ?quotient_norms //.
    by rewrite coprime_TIg ?coprime_morph.
  have ltMVn: #|M / V| < n by apply: leq_trans leMn; rewrite ltn_quotient.
  rewrite quotient_der //; move/IHn: frobGV.
  case/(_ _ ltMVn); rewrite ?quotient_sol ?quotient_norms ?coprime_morph //.
  - move=> Vx; case/setD1P=> ntVx; case/morphimP=> x nVx Rx defVx.
    rewrite defVx /= -cent_cycle -quotient_cycle //; congr 'C__(_ / V).
    apply/eqP; rewrite eqEsubset cycle_subG Rx /=.
    apply: contraR ntVx; move/(prime_TIg Rpr); move/trivgP.
    rewrite defVx /= (setIidPr _) cycle_subG //; move/set1P->.
    by rewrite morph1.
  - rewrite -coprime_norm_quotient_cent ?(coprimegS sKG) ?(subset_trans sKG) //.
    by rewrite tcKM quotient1.
  move=> _ _ -> //; rewrite -coprime_quotient_cent ?quotient_cyclic //.
  by rewrite (coprimegS sRG).
rewrite !subsetI in cVK' cMK' *.
case/andP: cVK' => sK'K cVK'; case/andP: cMK' => _ cMVK'; rewrite sK'K.
have sK'G: K^`(1) \subset G by rewrite (subset_trans sK'K) ?proper_sub.
have coMK': coprime #|M| #|K^`(1)| := coprimegS sK'G coMG.
rewrite (stable_factor_cent cVK') // /stable_factor /normal sVM nVM !andbT.
by rewrite commGC -quotient_cents2 // (subset_trans sK'G).
Qed.

End BGsection3.

(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrfun ssrbool eqtype ssrnat div fintype bigop prime.
From mathcomp
Require Import finset fingroup morphism perm action quotient gproduct.
From mathcomp
Require Import cyclic center pgroup nilpotent sylow hall abelian.

(******************************************************************************)
(*  Definition of Frobenius groups, some basic results, and the Frobenius     *)
(* theorem on the number of solutions of x ^+ n = 1.                          *)
(*    semiregular K H <->                                                     *)
(*       the internal action of H on K is semiregular, i.e., no nontrivial    *)
(*       elements of H and K commute; note that this is actually a symmetric  *)
(*       condition.                                                           *)
(*    semiprime K H <->                                                       *)
(*       the internal action of H on K is "prime", i.e., an element of K that *)
(*       centralises a nontrivial element of H must centralise all of H.      *)
(*    normedTI A G L <=>                                                      *)
(*       A is nonempty, strictly disjoint from its conjugates in G, and has   *)
(*       normaliser L in G.                                                   *)
(*    [Frobenius G = K ><| H] <=>                                             *)
(*       G is (isomorphic to) a Frobenius group with kernel K and complement  *)
(*       H. This is an effective predicate (in bool), which tests the         *)
(*       equality with the semidirect product, and then the fact that H is a  *)
(*       proper self-normalizing TI-subgroup of G.                            *)
(*    [Frobenius G with kernel H] <=>                                         *)
(*       G is (isomorphic to) a Frobenius group with kernel K; same as above, *)
(*       but without the semi-direct product.                                 *)
(*    [Frobenius G with complement H] <=>                                     *)
(*       G is (isomorphic to) a Frobenius group with complement H; same as    *)
(*       above, but without the semi-direct product. The proof that this form *)
(*       is equivalent to the above (i.e., the existence of Frobenius         *)
(*       kernels) requires character theory and will only be proved in the    *)
(*       vcharacter.v file.                                                   *)
(*    [Frobenius G] <=> G is a Frobenius group.                               *)
(*    Frobenius_action G H S to <->                                           *)
(*       The action to of G on S defines an isomorphism of G with a           *)
(*       (permutation) Frobenius group, i.e., to is faithful and transitive   *)
(*       on S, no nontrivial element of G fixes more than one point in S, and *)
(*       H is the stabilizer of some element of S, and non-trivial. Thus,     *)
(*        Frobenius_action G H S 'P                                           *)
(*       asserts that G is a Frobenius group in the classic sense.            *)
(*    has_Frobenius_action G H <->                                            *)
(*        Frobenius_action G H S to holds for some sT : finType, S : {set st} *)
(*        and to : {action gT &-> sT}. This is a predicate in Prop, but is    *)
(*        exactly reflected by [Frobenius G with complement H] : bool.        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Section Definitions.

Variable gT : finGroupType.
Implicit Types A G K H L : {set gT}.

(* Corresponds to "H acts on K in a regular manner" in B & G. *)
Definition semiregular K H := {in H^#, forall x, 'C_K[x] = 1}.

(* Corresponds to "H acts on K in a prime manner" in B & G. *)
Definition semiprime K H := {in H^#, forall x, 'C_K[x] = 'C_K(H)}.

Definition normedTI A G L := [&& A != set0, trivIset (A :^: G) & 'N_G(A) == L].

Definition Frobenius_group_with_complement G H := (H != G) && normedTI H^# G H.

Definition Frobenius_group G :=
  [exists H : {group gT}, Frobenius_group_with_complement G H].

Definition Frobenius_group_with_kernel_and_complement G K H :=
  (K ><| H == G) && Frobenius_group_with_complement G H.

Definition Frobenius_group_with_kernel G K :=
  [exists H : {group gT}, Frobenius_group_with_kernel_and_complement G K H].

Section FrobeniusAction.

Variables G H : {set gT}.
Variables (sT : finType) (S : {set sT}) (to : {action gT &-> sT}).

Definition Frobenius_action :=
  [/\ [faithful G, on S | to],
      [transitive G, on S | to],
      {in G^#, forall x, #|'Fix_(S | to)[x]| <= 1},
      H != 1
    & exists2 u, u \in S & H = 'C_G[u | to]].

End FrobeniusAction.

Variant has_Frobenius_action G H : Prop :=
  HasFrobeniusAction sT S to of @Frobenius_action G H sT S to.

End Definitions.

Arguments semiregular {gT} K%g H%g.
Arguments semiprime {gT} K%g H%g.
Arguments normedTI {gT} A%g G%g L%g.
Arguments Frobenius_group_with_complement {gT} G%g H%g.
Arguments Frobenius_group {gT} G%g.
Arguments Frobenius_group_with_kernel {gT} G%g K%g.
Arguments Frobenius_group_with_kernel_and_complement {gT} G%g K%g H%g.
Arguments Frobenius_action {gT} G%g H%g {sT} S%g to%act.
Arguments has_Frobenius_action {gT} G%g H%g.

Notation "[ 'Frobenius' G 'with' 'complement' H ]" :=
  (Frobenius_group_with_complement G H)
  (at level 0, G at level 50, H at level 35,
   format "[ 'Frobenius'  G  'with'  'complement'  H ]") : group_scope.

Notation "[ 'Frobenius' G 'with' 'kernel' K ]" :=
  (Frobenius_group_with_kernel G K)
  (at level 0, G at level 50, K at level 35,
   format "[ 'Frobenius'  G  'with'  'kernel'  K ]") : group_scope.

Notation "[ 'Frobenius' G ]" :=
  (Frobenius_group G)
  (at level 0, G at level 50,
   format "[ 'Frobenius'  G ]") : group_scope.

Notation "[ 'Frobenius' G = K ><| H ]" :=
  (Frobenius_group_with_kernel_and_complement G K H)
  (at level 0, G at level 50, K, H at level 35,
   format "[ 'Frobenius'  G  =  K  ><|  H ]") : group_scope.

Section FrobeniusBasics.

Variable gT : finGroupType.
Implicit Types (A B : {set gT}) (G H K L R X : {group gT}).

Lemma semiregular1l H : semiregular 1 H.
Proof. by move=> x _ /=; rewrite setI1g. Qed.

Lemma semiregular1r K : semiregular K 1.
Proof. by move=> x; rewrite setDv inE. Qed.

Lemma semiregular_sym H K : semiregular K H -> semiregular H K.
Proof.
move=> regH x /setD1P[ntx Kx]; apply: contraNeq ntx.
rewrite -subG1 -setD_eq0 -setIDAC => /set0Pn[y /setIP[Hy cxy]].
by rewrite (sameP eqP set1gP) -(regH y Hy) inE Kx cent1C.
Qed.

Lemma semiregularS K1 K2 A1 A2 :
  K1 \subset K2 -> A1 \subset A2 -> semiregular K2 A2 -> semiregular K1 A1.
Proof.
move=> sK12 sA12 regKA2 x /setD1P[ntx /(subsetP sA12)A2x].
by apply/trivgP; rewrite -(regKA2 x) ?inE ?ntx ?setSI.
Qed.

Lemma semiregular_prime H K : semiregular K H -> semiprime K H.
Proof.
move=> regH x Hx; apply/eqP; rewrite eqEsubset {1}regH // sub1G.
by rewrite -cent_set1 setIS ?centS // sub1set; case/setD1P: Hx.
Qed.

Lemma semiprime_regular H K : semiprime K H -> 'C_K(H) = 1 -> semiregular K H.
Proof. by move=> prKH tiKcH x Hx; rewrite prKH. Qed.

Lemma semiprimeS K1 K2 A1 A2 :
  K1 \subset K2 -> A1 \subset A2 -> semiprime K2 A2 -> semiprime K1 A1.
Proof.
move=> sK12 sA12 prKA2 x /setD1P[ntx A1x].
apply/eqP; rewrite eqEsubset andbC -{1}cent_set1 setIS ?centS ?sub1set //=.
rewrite -(setIidPl sK12) -!setIA prKA2 ?setIS ?centS //.
by rewrite !inE ntx (subsetP sA12).
Qed.

Lemma cent_semiprime H K X :
   semiprime K H -> X \subset H -> X :!=: 1 -> 'C_K(X) = 'C_K(H).
Proof.
move=> prKH sXH /trivgPn[x Xx ntx]; apply/eqP.
rewrite eqEsubset -{1}(prKH x) ?inE ?(subsetP sXH) ?ntx //=.
by rewrite -cent_cycle !setIS ?centS ?cycle_subG.
Qed.

Lemma stab_semiprime H K X :
   semiprime K H -> X \subset K -> 'C_H(X) != 1 -> 'C_H(X) = H.
Proof.
move=> prKH sXK ntCHX; apply/setIidPl; rewrite centsC -subsetIidl.
rewrite -{2}(setIidPl sXK) -setIA -(cent_semiprime prKH _ ntCHX) ?subsetIl //.
by rewrite !subsetI subxx sXK centsC subsetIr.
Qed.

Lemma cent_semiregular H K X :
   semiregular K H -> X \subset H -> X :!=: 1 -> 'C_K(X) = 1.
Proof.
move=> regKH sXH /trivgPn[x Xx ntx]; apply/trivgP.
rewrite -(regKH x) ?inE ?(subsetP sXH) ?ntx ?setIS //=.
by rewrite -cent_cycle centS ?cycle_subG.
Qed.

Lemma regular_norm_dvd_pred K H :
  H \subset 'N(K) -> semiregular K H -> #|H| %| #|K|.-1.
Proof.
move=> nKH regH; have actsH: [acts H, on K^# | 'J] by rewrite astabsJ normD1.
rewrite (cardsD1 1 K) group1 -(acts_sum_card_orbit actsH) /=.
rewrite (eq_bigr (fun _ => #|H|)) ?sum_nat_const ?dvdn_mull //.
move=> _ /imsetP[x /setIdP[ntx Kx] ->]; rewrite card_orbit astab1J.
rewrite ['C_H[x]](trivgP _) ?indexg1 //=.
apply/subsetP=> y /setIP[Hy cxy]; apply: contraR ntx => nty.
by rewrite -[[set 1]](regH y) inE ?nty // Kx cent1C.

Qed.

Lemma regular_norm_coprime K H :
  H \subset 'N(K) -> semiregular K H -> coprime #|K| #|H|.
Proof.
move=> nKH regH.
by rewrite (coprime_dvdr (regular_norm_dvd_pred nKH regH)) ?coprimenP.
Qed.

Lemma semiregularJ K H x : semiregular K H -> semiregular (K :^ x) (H :^ x).
Proof.
move=> regH yx; rewrite -conjD1g => /imsetP[y Hy ->].
by rewrite cent1J -conjIg regH ?conjs1g.
Qed.

Lemma semiprimeJ K H x : semiprime K H -> semiprime (K :^ x) (H :^ x).
Proof.
move=> prH yx; rewrite -conjD1g => /imsetP[y Hy ->].
by rewrite cent1J centJ -!conjIg prH.
Qed.

Lemma normedTI_P A G L : 
  reflect [/\ A != set0, L \subset 'N_G(A)
           & {in G, forall g, ~~ [disjoint A & A :^ g] -> g \in L}]
          (normedTI A G L).
Proof.
apply: (iffP and3P) => [[nzA /trivIsetP tiAG /eqP <-] | [nzA sLN tiAG]].
  split=> // g Gg; rewrite inE Gg (sameP normP eqP) /= eq_sym; apply: contraR.
  by apply: tiAG; rewrite ?mem_orbit ?orbit_refl.
have [/set0Pn[a Aa] /subsetIP[_ nAL]] := (nzA, sLN); split=> //; last first.
  rewrite eqEsubset sLN andbT; apply/subsetP=> x /setIP[Gx nAx].
  by apply/tiAG/pred0Pn=> //; exists a; rewrite /= (normP nAx) Aa.
apply/trivIsetP=> _ _ /imsetP[x Gx ->] /imsetP[y Gy ->]; apply: contraR.
rewrite -setI_eq0 -(mulgKV x y) conjsgM; set g := (y * x^-1)%g.
have Gg: g \in G by rewrite groupMl ?groupV.
rewrite -conjIg (inj_eq (act_inj 'Js x)) (eq_sym A) (sameP eqP normP).
by rewrite -cards_eq0 cardJg cards_eq0 setI_eq0 => /tiAG/(subsetP nAL)->.
Qed.
Arguments normedTI_P {A G L}.

Lemma normedTI_memJ_P A G L :
  reflect [/\ A != set0, L \subset G
            & {in A & G, forall a g, (a ^ g \in A) = (g \in L)}]
          (normedTI A G L).
Proof.
apply: (iffP normedTI_P) => [[-> /subsetIP[sLG nAL] tiAG] | [-> sLG tiAG]].
  split=> // a g Aa Gg; apply/idP/idP=> [Aag | Lg]; last first.
    by rewrite memJ_norm ?(subsetP nAL).
  by apply/tiAG/pred0Pn=> //; exists (a ^ g)%g; rewrite /= Aag memJ_conjg.
split=> // [ | g Gg /pred0Pn[ag /=]]; last first.
  by rewrite andbC => /andP[/imsetP[a Aa ->]]; rewrite tiAG.
apply/subsetP=> g Lg; have Gg := subsetP sLG g Lg.
by rewrite !inE Gg; apply/subsetP=> _ /imsetP[a Aa ->]; rewrite tiAG.
Qed.

Lemma partition_class_support A G :
  A != set0 -> trivIset (A :^: G) -> partition (A :^: G) (class_support A G).
Proof.
rewrite /partition cover_imset -class_supportEr eqxx => nzA ->.
by apply: contra nzA => /imsetP[x _ /eqP]; rewrite eq_sym -!cards_eq0 cardJg.
Qed.

Lemma partition_normedTI A G L :
  normedTI A G L -> partition (A :^: G) (class_support A G).
Proof. by case/and3P=> ntA tiAG _; apply: partition_class_support. Qed.

Lemma card_support_normedTI A G L :
  normedTI A G L -> #|class_support A G| = (#|A| * #|G : L|)%N.
Proof.
case/and3P=> ntA tiAG /eqP <-; rewrite -card_conjugates mulnC.
apply: card_uniform_partition (partition_class_support ntA tiAG).
by move=> _ /imsetP[y _ ->]; rewrite cardJg.
Qed.

Lemma normedTI_S A B G L : 
    A != set0 -> L \subset 'N(A) -> A \subset B -> normedTI B G L ->
  normedTI A G L.
Proof.
move=> nzA /subsetP nAL /subsetP sAB /normedTI_memJ_P[nzB sLG tiB].
apply/normedTI_memJ_P; split=> // a x Aa Gx.
by apply/idP/idP => [Aax | /nAL/memJ_norm-> //]; rewrite -(tiB a) ?sAB.
Qed.

Lemma cent1_normedTI A G L :
  normedTI A G L -> {in A, forall x, 'C_G[x] \subset L}.
Proof.
case/normedTI_memJ_P=> [_ _ tiAG] x Ax; apply/subsetP=> y /setIP[Gy cxy].
by rewrite -(tiAG x) // /(x ^ y) -(cent1P cxy) mulKg.
Qed.

Lemma Frobenius_actionP G H :
  reflect (has_Frobenius_action G H) [Frobenius G with complement H].
Proof.
apply: (iffP andP) => [[neqHG] | [sT S to [ffulG transG regG ntH [u Su defH]]]].
  case/normedTI_P=> nzH /subsetIP[sHG _] tiHG.
  suffices: Frobenius_action G H (rcosets H G) 'Rs by apply: HasFrobeniusAction.
  pose Hfix x := 'Fix_(rcosets H G | 'Rs)[x].
  have regG: {in G^#, forall x, #|Hfix x| <= 1}.
    move=> x /setD1P[ntx Gx].
    apply: wlog_neg; rewrite -ltnNge => /ltnW/card_gt0P/=[Hy].
    rewrite -(cards1 Hy) => /setIP[/imsetP[y Gy ->{Hy}] cHyx].
    apply/subset_leq_card/subsetP=> _ /setIP[/imsetP[z Gz ->] cHzx].
    rewrite -!sub_astab1 !astab1_act !sub1set astab1Rs in cHyx cHzx *.
    rewrite !rcosetE; apply/set1P/rcoset_eqP; rewrite mem_rcoset.
    apply: tiHG; [by rewrite !in_group | apply/pred0Pn; exists (x ^ y^-1)].
    by rewrite conjD1g !inE conjg_eq1 ntx -mem_conjg cHyx conjsgM memJ_conjg.
  have ntH: H :!=: 1 by rewrite -subG1 -setD_eq0.
  split=> //; first 1 last; first exact: transRs_rcosets.
    by exists (val H); rewrite ?orbit_refl // astab1Rs (setIidPr sHG).
  apply/subsetP=> y /setIP[Gy cHy]; apply: contraR neqHG => nt_y.
  rewrite (index1g sHG) //; apply/eqP; rewrite eqn_leq indexg_gt0 andbT.
  apply: leq_trans (regG y _); last by rewrite setDE 2!inE Gy nt_y /=.
  by rewrite /Hfix (setIidPl _) -1?astabC ?sub1set.
have sHG: H \subset G by rewrite defH subsetIl.
split.
  apply: contraNneq ntH => /= defG.
  suffices defS: S = [set u] by rewrite -(trivgP ffulG) /= defS defH.
  apply/eqP; rewrite eq_sym eqEcard sub1set Su.
  by rewrite -(atransP transG u Su) card_orbit -defH defG indexgg cards1.
apply/normedTI_P; rewrite setD_eq0 subG1 normD1 subsetI sHG normG.
split=> // x Gx; rewrite -setI_eq0 conjD1g defH inE Gx conjIg conjGid //.
rewrite -setDIl -setIIr -astab1_act setDIl => /set0Pn[y /setIP[Gy /setD1P[_]]].
case/setIP; rewrite 2!(sameP astab1P afix1P) => cuy cuxy; apply/astab1P.
apply: contraTeq (regG y Gy) => cu'x.
rewrite (cardD1 u) (cardD1 (to u x)) inE Su cuy inE /= inE cu'x cuxy.
by rewrite (actsP (atrans_acts transG)) ?Su.
Qed.

Section FrobeniusProperties.

Variables G H K : {group gT}.
Hypothesis frobG : [Frobenius G = K ><| H].

Lemma FrobeniusWker : [Frobenius G with kernel K].
Proof. by apply/existsP; exists H. Qed.

Lemma FrobeniusWcompl : [Frobenius G with complement H].
Proof. by case/andP: frobG. Qed.

Lemma FrobeniusW : [Frobenius G].
Proof. by apply/existsP; exists H; apply: FrobeniusWcompl. Qed.

Lemma Frobenius_context :
  [/\ K ><| H = G, K :!=: 1, H :!=: 1, K \proper G & H \proper G].
Proof.
have [/eqP defG neqHG ntH _] := and4P frobG; rewrite setD_eq0 subG1 in ntH.
have ntK: K :!=: 1 by apply: contraNneq neqHG => K1; rewrite -defG K1 sdprod1g.
rewrite properEcard properEneq neqHG; have /mulG_sub[-> ->] := sdprodW defG.
by rewrite -(sdprod_card defG) ltn_Pmulr ?cardG_gt1.
Qed.

Lemma Frobenius_partition : partition (gval K |: (H^# :^: K)) G.
Proof.
have [/eqP defG _ tiHG] := and3P frobG; have [_ tiH1G /eqP defN] := and3P tiHG.
have [[_ /mulG_sub[sKG sHG] nKH tiKH] mulHK] := (sdprodP defG, sdprodWC defG).
set HG := H^# :^: K; set KHG := _ |: _.
have defHG: HG = H^# :^: G.
  have: 'C_G[H^# | 'Js] * K = G by rewrite astab1Js defN mulHK.
  move/subgroup_transitiveP/atransP.
  by apply; rewrite ?atrans_orbit ?orbit_refl.
have /and3P[defHK _ nzHG] := partition_normedTI tiHG.
rewrite -defHG in defHK nzHG tiH1G.
have [tiKHG HG'K]: trivIset KHG /\ gval K \notin HG.
  apply: trivIsetU1 => // _ /imsetP[x Kx ->]; rewrite -setI_eq0.
  by rewrite -(conjGid Kx) -conjIg setIDA tiKH setDv conj0g.
rewrite /partition andbC tiKHG !inE negb_or nzHG eq_sym -card_gt0 cardG_gt0 /=.
rewrite eqEcard; apply/andP; split.
  rewrite /cover big_setU1 //= subUset sKG -/(cover HG) (eqP defHK).
  by rewrite class_support_subG // (subset_trans _ sHG) ?subD1set.
rewrite -(eqnP tiKHG) big_setU1 //= (eqnP tiH1G) (eqP defHK).
rewrite (card_support_normedTI tiHG) -(Lagrange sHG) (cardsD1 1) group1 mulSn.
by rewrite leq_add2r -mulHK indexMg -indexgI tiKH indexg1.
Qed.

Lemma Frobenius_cent1_ker : {in K^#, forall x, 'C_G[x] \subset K}.
Proof.
have [/eqP defG _ /normedTI_memJ_P[_ _ tiHG]] := and3P frobG.
move=> x /setD1P[ntx Kx]; have [_ /mulG_sub[sKG _] _ tiKH] := sdprodP defG.
have [/eqP <- _ _] := and3P Frobenius_partition; rewrite big_distrl /=.
apply/bigcupsP=> _ /setU1P[|/imsetP[y Ky]] ->; first exact: subsetIl.
apply: contraR ntx => /subsetPn[z]; rewrite inE mem_conjg => /andP[Hzy cxz] _.
rewrite -(conjg_eq1 x y^-1) -in_set1 -set1gE -tiKH inE andbC.
rewrite -(tiHG _ _ Hzy) ?(subsetP sKG) ?in_group // Ky andbT -conjJg.
by rewrite /(z ^ x) (cent1P cxz) mulKg.
Qed.

Lemma Frobenius_reg_ker : semiregular K H.
Proof.
move=> x /setD1P[ntx Hx].
apply/trivgP/subsetP=> y /setIP[Ky cxy]; apply: contraR ntx => nty.
have K1y: y \in K^# by rewrite inE nty.
have [/eqP/sdprod_context[_ sHG _ _ tiKH] _] := andP frobG.
suffices: x \in K :&: H by rewrite tiKH inE.
by rewrite inE (subsetP (Frobenius_cent1_ker K1y)) // inE cent1C (subsetP sHG).
Qed.

Lemma Frobenius_reg_compl : semiregular H K.
Proof. by apply: semiregular_sym; apply: Frobenius_reg_ker. Qed.

Lemma Frobenius_dvd_ker1 : #|H| %| #|K|.-1.
Proof.
apply: regular_norm_dvd_pred Frobenius_reg_ker.
by have[/sdprodP[]] := Frobenius_context.
Qed.

Lemma ltn_odd_Frobenius_ker : odd #|G| -> #|H|.*2 < #|K|.
Proof.
move/oddSg=> oddG.
have [/sdprodW/mulG_sub[sKG sHG] ntK _ _ _] := Frobenius_context.
by rewrite dvdn_double_ltn ?oddG ?cardG_gt1 ?Frobenius_dvd_ker1.
Qed.

Lemma Frobenius_index_dvd_ker1 : #|G : K| %| #|K|.-1.
Proof.
have[defG _ _ /andP[sKG _] _] := Frobenius_context.
by rewrite -divgS // -(sdprod_card defG) mulKn ?Frobenius_dvd_ker1.
Qed.

Lemma Frobenius_coprime : coprime #|K| #|H|.
Proof. by rewrite (coprime_dvdr Frobenius_dvd_ker1) ?coprimenP. Qed.

Lemma Frobenius_trivg_cent : 'C_K(H) = 1.
Proof.
by apply: (cent_semiregular Frobenius_reg_ker); case: Frobenius_context.
Qed.

Lemma Frobenius_index_coprime : coprime #|K| #|G : K|.
Proof. by rewrite (coprime_dvdr Frobenius_index_dvd_ker1) ?coprimenP. Qed.

Lemma Frobenius_ker_Hall : Hall G K.
Proof.
have [_ _ _ /andP[sKG _] _] := Frobenius_context.
by rewrite /Hall sKG Frobenius_index_coprime.
Qed.

Lemma Frobenius_compl_Hall : Hall G H.
Proof.
have [defG _ _ _ _] := Frobenius_context.
by rewrite -(sdprod_Hall defG) Frobenius_ker_Hall.
Qed.

End FrobeniusProperties.

Lemma normedTI_J x A G L : normedTI (A :^ x) (G :^ x) (L :^ x) = normedTI A G L.
Proof.
rewrite {1}/normedTI normJ -conjIg -(conj0g x) !(can_eq (conjsgK x)).
congr [&&  _, _ == _ & _]; rewrite /cover (reindex_inj (@conjsg_inj _ x)).
  by apply: eq_big => Hy; rewrite ?orbit_conjsg ?cardJg.
by rewrite bigcupJ cardJg (eq_bigl _ _ (orbit_conjsg _ _ _ _)).
Qed.

Lemma FrobeniusJcompl x G H :
  [Frobenius G :^ x with complement H :^ x] = [Frobenius G with complement H].
Proof.
by congr (_ && _); rewrite ?(can_eq (conjsgK x)) // -conjD1g normedTI_J.
Qed.

Lemma FrobeniusJ x G K H :
  [Frobenius G :^ x = K :^ x ><| H :^ x] = [Frobenius G = K ><| H].
Proof.
by congr (_ && _); rewrite ?FrobeniusJcompl // -sdprodJ (can_eq (conjsgK x)).
Qed.

Lemma FrobeniusJker x G K :
  [Frobenius G :^ x with kernel K :^ x] = [Frobenius G with kernel K].
Proof.
apply/existsP/existsP=> [] [H]; last by exists (H :^ x)%G; rewrite FrobeniusJ.
by rewrite -(conjsgKV x H) FrobeniusJ; exists (H :^ x^-1)%G.
Qed.

Lemma FrobeniusJgroup x G : [Frobenius G :^ x] = [Frobenius G].
Proof.
apply/existsP/existsP=> [] [H].
  by rewrite -(conjsgKV x H) FrobeniusJcompl; exists (H :^ x^-1)%G.
by exists (H :^ x)%G; rewrite FrobeniusJcompl.
Qed.

Lemma Frobenius_ker_dvd_ker1 G K :
  [Frobenius G with kernel K] -> #|G : K| %| #|K|.-1.
Proof. by case/existsP=> H; apply: Frobenius_index_dvd_ker1. Qed.

Lemma Frobenius_ker_coprime G K :
  [Frobenius G with kernel K] -> coprime #|K| #|G : K|.
Proof. by case/existsP=> H; apply: Frobenius_index_coprime. Qed.

Lemma Frobenius_semiregularP G K H :
    K ><| H = G -> K :!=: 1 -> H :!=: 1 ->
  reflect (semiregular K H) [Frobenius G = K ><| H].
Proof.
move=> defG ntK ntH.
apply: (iffP idP) => [|regG]; first exact: Frobenius_reg_ker.
have [nsKG sHG defKH nKH tiKH]:= sdprod_context defG; have [sKG _]:= andP nsKG.
apply/and3P; split; first by rewrite defG.
  by rewrite eqEcard sHG -(sdprod_card defG) -ltnNge ltn_Pmull ?cardG_gt1.
apply/normedTI_memJ_P; rewrite setD_eq0 subG1 sHG -defKH -(normC nKH).
split=> // z _ /setD1P[ntz Hz] /mulsgP[y x Hy Kx ->]; rewrite groupMl // !inE.
rewrite conjg_eq1 ntz; apply/idP/idP=> [Hzxy | Hx]; last by rewrite !in_group.
apply: (subsetP (sub1G H)); have Hzy: z ^ y \in H by apply: groupJ.
rewrite -(regG (z ^ y)); last by apply/setD1P; rewrite conjg_eq1.
rewrite inE Kx cent1C (sameP cent1P commgP) -in_set1 -[[set 1]]tiKH inE /=.
rewrite andbC groupM ?groupV -?conjgM //= commgEr groupMr //.
by rewrite memJ_norm ?(subsetP nKH) ?groupV.
Qed.

Lemma prime_FrobeniusP G K H :
    K :!=: 1 -> prime #|H| ->
  reflect (K ><| H = G /\ 'C_K(H) = 1) [Frobenius G = K ><| H].
Proof.
move=> ntK H_pr; have ntH: H :!=: 1 by rewrite -cardG_gt1 prime_gt1.
have [defG | not_sdG] := eqVneq (K ><| H) G; last first.
  by apply: (iffP andP) => [] [defG]; rewrite defG ?eqxx in not_sdG.
apply: (iffP (Frobenius_semiregularP defG ntK ntH)) => [regH | [_ regH x]].
  split=> //; have [x defH] := cyclicP (prime_cyclic H_pr).
  by rewrite defH cent_cycle regH // !inE defH cycle_id andbT -cycle_eq1 -defH.
case/setD1P=> nt_x Hx; apply/trivgP; rewrite -regH setIS //= -cent_cycle.
by rewrite centS // prime_meetG // (setIidPr _) ?cycle_eq1 ?cycle_subG.
Qed.

Lemma Frobenius_subl G K K1 H :
    K1 :!=: 1 -> K1 \subset K -> H \subset 'N(K1) -> [Frobenius G = K ><| H] ->
  [Frobenius K1 <*> H = K1 ><| H].
Proof.
move=> ntK1 sK1K nK1H frobG; have [_ _ ntH _ _] := Frobenius_context frobG.
apply/Frobenius_semiregularP=> //.
  by rewrite sdprodEY ?coprime_TIg ?(coprimeSg sK1K) ?(Frobenius_coprime frobG).
by move=> x /(Frobenius_reg_ker frobG) cKx1; apply/trivgP; rewrite -cKx1 setSI.
Qed.
 
Lemma Frobenius_subr G K H H1 :
    H1 :!=: 1 -> H1 \subset H -> [Frobenius G = K ><| H] ->
  [Frobenius K <*> H1 = K ><| H1].
Proof.
move=> ntH1 sH1H frobG; have [defG ntK _ _ _] := Frobenius_context frobG.
apply/Frobenius_semiregularP=> //.
  have [_ _ /(subset_trans sH1H) nH1K tiHK] := sdprodP defG.
  by rewrite sdprodEY //; apply/trivgP; rewrite -tiHK setIS.
by apply: sub_in1 (Frobenius_reg_ker frobG); apply/subsetP/setSD.
Qed.

Lemma Frobenius_kerP G K :
  reflect [/\ K :!=: 1, K \proper G, K <| G
            & {in K^#, forall x, 'C_G[x] \subset K}]
          [Frobenius G with kernel K].
Proof.
apply: (iffP existsP) => [[H frobG] | [ntK ltKG nsKG regK]].
  have [/sdprod_context[nsKG _ _ _ _] ntK _ ltKG _] := Frobenius_context frobG.
  by split=> //; apply: Frobenius_cent1_ker frobG.
have /andP[sKG nKG] := nsKG.
have hallK: Hall G K.
  rewrite /Hall sKG //= coprime_sym coprime_pi' //.
  apply: sub_pgroup (pgroup_pi K) => p; have [P sylP] := Sylow_exists p G.
  have [[sPG pP p'GiP] sylPK] := (and3P sylP, Hall_setI_normal nsKG sylP).
  rewrite -p_rank_gt0 -(rank_Sylow sylPK) rank_gt0 => ntPK.
  rewrite inE /= -p'natEpi // (pnat_dvd _ p'GiP) ?indexgS //.
  have /trivgPn[z]: P :&: K :&: 'Z(P) != 1.
    by rewrite meet_center_nil ?(pgroup_nil pP) ?(normalGI sPG nsKG).
  rewrite !inE -andbA -sub_cent1=> /and4P[_ Kz _ cPz] ntz.
  by apply: subset_trans (regK z _); [apply/subsetIP | apply/setD1P].
have /splitsP[H /complP[tiKH defG]] := SchurZassenhaus_split hallK nsKG.
have [_ sHG] := mulG_sub defG; have nKH := subset_trans sHG nKG.
exists H; apply/Frobenius_semiregularP; rewrite ?sdprodE //.
  by apply: contraNneq (proper_subn ltKG) => H1; rewrite -defG H1 mulg1.
apply: semiregular_sym => x Kx; apply/trivgP; rewrite -tiKH.
by rewrite subsetI subsetIl (subset_trans _ (regK x _)) ?setSI.
Qed.

Lemma set_Frobenius_compl G K H :
  K ><| H = G -> [Frobenius G with kernel K] -> [Frobenius G = K ><| H].
Proof.
move=> defG /Frobenius_kerP[ntK ltKG _ regKG].
apply/Frobenius_semiregularP=> //.
  by apply: contraTneq ltKG => H_1; rewrite -defG H_1 sdprodg1 properxx.
apply: semiregular_sym => y /regKG sCyK.
have [_ sHG _ _ tiKH] := sdprod_context defG.
by apply/trivgP; rewrite /= -(setIidPr sHG) setIAC -tiKH setSI.
Qed.

Lemma Frobenius_kerS G K G1 :
    G1 \subset G -> K \proper G1 ->
  [Frobenius G with kernel K] -> [Frobenius G1 with kernel K].
Proof.
move=> sG1G ltKG1 /Frobenius_kerP[ntK _ /andP[_ nKG] regKG].
apply/Frobenius_kerP; rewrite /normal proper_sub // (subset_trans sG1G) //.
by split=> // x /regKG; apply: subset_trans; rewrite setSI.
Qed.

Lemma Frobenius_action_kernel_def G H K sT S to :
    K ><| H = G -> @Frobenius_action _ G H sT S to ->
  K :=: 1 :|: [set x in G | 'Fix_(S | to)[x] == set0].
Proof.
move=> defG FrobG.
have partG: partition (gval K |: (H^# :^: K)) G.
  apply: Frobenius_partition; apply/andP; rewrite defG; split=> //.
  by apply/Frobenius_actionP; apply: HasFrobeniusAction FrobG.
have{FrobG} [ffulG transG regG ntH [u Su defH]]:= FrobG.
apply/setP=> x; rewrite !inE; have [-> | ntx] := altP eqP; first exact: group1.
rewrite /= -(cover_partition partG) /cover.
have neKHy y: gval K <> H^# :^ y.
  by move/setP/(_ 1); rewrite group1 conjD1g setD11.
rewrite big_setU1 /= ?inE; last by apply/imsetP=> [[y _ /neKHy]].
have [nsKG sHG _ _ tiKH] := sdprod_context defG; have [sKG nKG]:= andP nsKG.
symmetry; case Kx: (x \in K) => /=.
  apply/set0Pn=> [[v /setIP[Sv]]]; have [y Gy ->] := atransP2 transG Su Sv.
  rewrite -sub1set -astabC sub1set astab1_act mem_conjg => Hxy.
  case/negP: ntx; rewrite -in_set1 -(conjgKV y x) -mem_conjgV conjs1g -tiKH.
  by rewrite defH setIA inE -mem_conjg (setIidPl sKG) (normsP nKG) ?Kx.
apply/andP=> [[/bigcupP[_ /imsetP[y Ky ->] Hyx] /set0Pn[]]]; exists (to u y).
rewrite inE (actsP (atrans_acts transG)) ?(subsetP sKG) // Su.
rewrite -sub1set -astabC sub1set astab1_act.
by rewrite conjD1g defH conjIg !inE in Hyx; case/and3P: Hyx.
Qed.

End FrobeniusBasics.

Arguments normedTI_P {gT A G L}.
Arguments normedTI_memJ_P {gT A G L}.
Arguments Frobenius_kerP {gT G K}.

Lemma Frobenius_coprime_quotient (gT : finGroupType) (G K H N : {group gT}) :
    K ><| H = G -> N <| G -> coprime #|K| #|H| /\ H :!=: 1%g ->
    N \proper K /\ {in H^#, forall x, 'C_K[x] \subset N} ->
  [Frobenius G / N = (K / N) ><| (H / N)]%g.
Proof.
move=> defG nsNG [coKH ntH] [ltNK regH].
have [[sNK _] [_ /mulG_sub[sKG sHG] _ _]] := (andP ltNK, sdprodP defG).
have [_ nNG] := andP nsNG; have nNH := subset_trans sHG nNG.
apply/Frobenius_semiregularP; first exact: quotient_coprime_sdprod.
- by rewrite quotient_neq1 ?(normalS _ sKG).
- by rewrite -(isog_eq1 (quotient_isog _ _)) ?coprime_TIg ?(coprimeSg sNK).
move=> _ /(subsetP (quotientD1 _ _))/morphimP[x nNx H1x ->].
rewrite -cent_cycle -quotient_cycle //=.
rewrite -strongest_coprime_quotient_cent ?cycle_subG //.
- by rewrite cent_cycle quotientS1 ?regH.
- by rewrite subIset ?sNK.
- rewrite (coprimeSg (subsetIl N _)) ?(coprimeSg sNK) ?(coprimegS _ coKH) //.
  by rewrite cycle_subG; case/setD1P: H1x.
by rewrite orbC abelian_sol ?cycle_abelian.
Qed.

Section InjmFrobenius.

Variables (gT rT : finGroupType) (D G : {group gT}) (f : {morphism D >-> rT}).
Implicit Types (H K : {group gT}) (sGD : G \subset D) (injf : 'injm f).

Lemma injm_Frobenius_compl H sGD injf : 
  [Frobenius G with complement H] -> [Frobenius f @* G with complement f @* H].
Proof.
case/andP=> neqGH /normedTI_P[nzH /subsetIP[sHG _] tiHG].
have sHD := subset_trans sHG sGD; have sH1D := subset_trans (subD1set H 1) sHD.
apply/andP; rewrite (can_in_eq (injmK injf)) //; split=> //.
apply/normedTI_P; rewrite normD1 -injmD1 // -!cards_eq0 card_injm // in nzH *.
rewrite subsetI normG morphimS //; split=> // _ /morphimP[x Dx Gx ->] ti'fHx.
rewrite mem_morphim ?tiHG //; apply: contra ti'fHx; rewrite -!setI_eq0 => tiHx.
by rewrite -morphimJ // -injmI ?conj_subG // (eqP tiHx) morphim0.
Qed.

Lemma injm_Frobenius H K sGD injf : 
  [Frobenius G = K ><| H] -> [Frobenius f @* G = f @* K ><| f @* H].
Proof.
case/andP=> /eqP defG frobG.
by apply/andP; rewrite (injm_sdprod _ injf defG) // eqxx injm_Frobenius_compl.
Qed.

Lemma injm_Frobenius_ker K sGD injf : 
  [Frobenius G with kernel K] -> [Frobenius f @* G with kernel f @* K].
Proof.
case/existsP=> H frobG; apply/existsP.
by exists (f @* H)%G; apply: injm_Frobenius.
Qed.

Lemma injm_Frobenius_group sGD injf : [Frobenius G] -> [Frobenius f @* G].
Proof.
case/existsP=> H frobG; apply/existsP; exists (f @* H)%G.
exact: injm_Frobenius_compl.
Qed.

End InjmFrobenius.

Theorem Frobenius_Ldiv (gT : finGroupType) (G : {group gT}) n :
  n %| #|G| -> n %| #|'Ldiv_n(G)|.
Proof.
move=> nG; move: {2}_.+1 (ltnSn (#|G| %/ n)) => mq.
elim: mq => // mq IHm in gT G n nG *; case/dvdnP: nG => q oG.
have [q_gt0 n_gt0] : 0 < q /\ 0 < n by apply/andP; rewrite -muln_gt0 -oG.
rewrite ltnS oG mulnK // => leqm.
have:= q_gt0; rewrite leq_eqVlt => /predU1P[q1 | lt1q].
  rewrite -(mul1n n) q1 -oG (setIidPl _) //.
  by apply/subsetP=> x Gx; rewrite inE -order_dvdn order_dvdG.
pose p := pdiv q; have pr_p: prime p by apply: pdiv_prime.
have lt1p: 1 < p := prime_gt1 pr_p; have p_gt0 := ltnW lt1p.
have{leqm} lt_qp_mq: q %/ p < mq by apply: leq_trans leqm; rewrite ltn_Pdiv.
have: n %| #|'Ldiv_(p * n)(G)|.
  have: p * n %| #|G| by rewrite oG dvdn_pmul2r ?pdiv_dvd.
  move/IHm=> IH; apply: dvdn_trans (IH _); first exact: dvdn_mull.
  by rewrite oG divnMr.
rewrite -(cardsID 'Ldiv_n()) dvdn_addl.
  rewrite -setIA ['Ldiv_n(_)](setIidPr _) //.
  by apply/subsetP=> x; rewrite !inE -!order_dvdn; apply: dvdn_mull.
rewrite -setIDA; set A := _ :\: _.
have pA x: x \in A -> #[x]`_p = (n`_p * p)%N.
  rewrite !inE -!order_dvdn => /andP[xn xnp].
  rewrite !p_part // -expnSr; congr (p ^ _)%N; apply/eqP.
  rewrite eqn_leq -{1}addn1 -(pfactorK 1 pr_p) -lognM ?expn1 // mulnC.
  rewrite dvdn_leq_log ?muln_gt0 ?p_gt0 //= ltnNge; apply: contra xn => xn.
  move: xnp; rewrite -[#[x]](partnC p) //.
  rewrite !Gauss_dvd ?coprime_partC //; case/andP=> _.
  rewrite p_part ?pfactor_dvdn // xn Gauss_dvdr // coprime_sym.
  exact: pnat_coprime (pnat_id _) (part_pnat _ _).
rewrite -(partnC p n_gt0) Gauss_dvd ?coprime_partC //; apply/andP; split.
  rewrite -sum1_card (partition_big_imset (@cycle _)) /=.
  apply: dvdn_sum => _ /imsetP[x /setIP[Gx Ax] ->].
  rewrite (eq_bigl (generator <[x]>)) => [|y].
    rewrite sum1dep_card -totient_gen -[#[x]](partnC p) //.
    rewrite totient_coprime ?coprime_partC // dvdn_mulr // .
    by rewrite (pA x Ax) p_part // -expnSr totient_pfactor // dvdn_mull.
  rewrite /generator eq_sym andbC; case xy: {+}(_ == _) => //.
  rewrite !inE -!order_dvdn in Ax *.
  by rewrite -cycle_subG /order -(eqP xy) cycle_subG Gx.
rewrite -sum1_card (partition_big_imset (fun x => x.`_p ^: G)) /=.
apply: dvdn_sum => _ /imsetP[x /setIP[Gx Ax] ->].
set y := x.`_p; have oy: #[y] = (n`_p * p)%N by rewrite order_constt pA.
rewrite (partition_big (fun x => x.`_p) (mem (y ^: G))) /= => [|z]; last first.
  by case/andP=> _ /eqP <-; rewrite /= class_refl.
pose G' := ('C_G[y] / <[y]>)%G; pose n' := gcdn #|G'| n`_p^'.
have n'_gt0: 0 < n' by rewrite gcdn_gt0 cardG_gt0.
rewrite (eq_bigr (fun _ => #|'Ldiv_n'(G')|)) => [|_ /imsetP[a Ga ->]].
  rewrite sum_nat_const -index_cent1 indexgI.
  rewrite -(dvdn_pmul2l (cardG_gt0 'C_G[y])) mulnA LagrangeI.
  have oCy: #|'C_G[y]| = (#[y] * #|G'|)%N.
    rewrite card_quotient ?subcent1_cycle_norm // Lagrange //.
    by rewrite subcent1_cycle_sub ?groupX.
  rewrite oCy -mulnA -(muln_lcm_gcd #|G'|) -/n' mulnA dvdn_mul //.
    rewrite muln_lcmr -oCy order_constt pA // mulnAC partnC // dvdn_lcm.
    by rewrite cardSg ?subsetIl // mulnC oG dvdn_pmul2r ?pdiv_dvd.
  apply: IHm; [exact: dvdn_gcdl | apply: leq_ltn_trans lt_qp_mq].
  rewrite -(@divnMr n`_p^') // -muln_lcm_gcd mulnC divnMl //.
  rewrite leq_divRL // divn_mulAC ?leq_divLR ?dvdn_mulr ?dvdn_lcmr //.
  rewrite dvdn_leq ?muln_gt0 ?q_gt0 //= mulnC muln_lcmr dvdn_lcm.
  rewrite -(@dvdn_pmul2l n`_p) // mulnA -oy -oCy mulnCA partnC // -oG.
  by rewrite cardSg ?subsetIl // dvdn_mul ?pdiv_dvd.
pose h := [fun z => coset <[y]> (z ^ a^-1)].
pose h' := [fun Z : coset_of <[y]> => (y * (repr Z).`_p^') ^ a].
rewrite -sum1_card (reindex_onto h h') /= => [|Z]; last first.
  rewrite conjgK coset_kerl ?cycle_id ?morph_constt ?repr_coset_norm //.
  rewrite /= coset_reprK 2!inE -order_dvdn dvdn_gcd => /and3P[_ _ p'Z].
  by apply: constt_p_elt (pnat_dvd p'Z _); apply: part_pnat.
apply: eq_bigl => z; apply/andP/andP=> [[]|[]].
  rewrite inE -andbA => /and3P[Gz Az _] /eqP zp_ya.
  have czy: z ^ a^-1 \in 'C[y].
    rewrite -mem_conjg -normJ conjg_set1 -zp_ya.
    by apply/cent1P; apply: commuteX.
  have Nz:  z ^ a^-1 \in 'N(<[y]>) by apply: subsetP czy; apply: norm_gen.
  have G'z: h z \in G' by rewrite mem_morphim //= inE groupJ // groupV.
  rewrite inE G'z inE -order_dvdn dvdn_gcd order_dvdG //=.
  rewrite /order -morphim_cycle // -quotientE card_quotient ?cycle_subG //.
  rewrite -(@dvdn_pmul2l #[y]) // Lagrange; last first.
    by rewrite /= cycleJ cycle_subG mem_conjgV -zp_ya mem_cycle.
  rewrite oy mulnAC partnC // [#|_|]orderJ; split.
    by rewrite !inE -!order_dvdn mulnC in Az; case/andP: Az.
  set Z := coset _ _; have NZ := repr_coset_norm Z; have:= coset_reprK Z.
  case/kercoset_rcoset=> {NZ}// _ /cycleP[i ->] ->{Z}.
  rewrite consttM; last exact/commute_sym/commuteX/cent1P.
  rewrite (constt1P _) ?p_eltNK 1?p_eltX ?p_elt_constt // mul1g.
  by rewrite conjMg consttJ conjgKV -zp_ya consttC.
rewrite 2!inE -order_dvdn; set Z := coset _ _ => /andP[Cz n'Z] /eqP def_z.
have Nz: z ^ a^-1 \in 'N(<[y]>).
  rewrite -def_z conjgK groupMr; first by rewrite -(cycle_subG y) normG.
  by rewrite groupX ?repr_coset_norm.
have{Cz} /setIP[Gz Cz]: z ^ a^-1 \in 'C_G[y].
  case/morphimP: Cz => u Nu Cu /kercoset_rcoset[] // _ /cycleP[i ->] ->.
  by rewrite groupMr // groupX // inE groupX //; apply/cent1P.
have{def_z} zp_ya: z.`_p = y ^ a.
  rewrite -def_z consttJ consttM.
    rewrite constt_p_elt ?p_elt_constt //.
    by rewrite (constt1P _) ?p_eltNK ?p_elt_constt ?mulg1.
  apply: commute_sym; apply/cent1P.
  by rewrite -def_z conjgK groupMl // in Cz; apply/cent1P.
have ozp: #[z ^ a^-1]`_p = #[y] by rewrite -order_constt consttJ zp_ya conjgK.
split; rewrite zp_ya // -class_lcoset lcoset_id // eqxx andbT.
rewrite -(conjgKV a z) !inE groupJ //= -!order_dvdn orderJ; apply/andP; split.
  apply: contra (partn_dvd p n_gt0) _.
  by rewrite ozp -(muln1 n`_p) oy dvdn_pmul2l // dvdn1 neq_ltn lt1p orbT.
rewrite -(partnC p n_gt0) mulnCA mulnA -oy -(@partnC p #[_]) // ozp.
apply dvdn_mul => //; apply: dvdn_trans (dvdn_trans n'Z (dvdn_gcdr _ _)).
rewrite {2}/order -morphim_cycle // -quotientE card_quotient ?cycle_subG //.
rewrite -(@dvdn_pmul2l #|<[z ^ a^-1]> :&: <[y]>|) ?cardG_gt0 // LagrangeI.
rewrite -[#|<[_]>|](partnC p) ?order_gt0 // dvdn_pmul2r // ozp.
by rewrite cardSg ?subsetIr.
Qed.

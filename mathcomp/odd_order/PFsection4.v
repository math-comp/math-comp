(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset fingroup.
Require Import morphism perm automorphism quotient action gfunctor gproduct.
Require Import center commutator zmodp cyclic pgroup nilpotent hall frobenius.
Require Import matrix mxalgebra mxrepresentation vector ssrnum algC classfun.
Require Import character inertia vcharacter PFsection1 PFsection2 PFsection3.

(******************************************************************************)
(* This file covers Peterfalvi, Section 4: The Dade isometry of a certain     *)
(* type of subgroup.                                                          *)
(*   Given defW : W1 \x W2 = W, we define here:                               *)
(*  primeTI_hypothesis L K defW <->                                           *)
(*                   L = K ><| W1, where W1 acts in a prime manner on K (see  *)
(*                   semiprime in frobenius.v), and both W1 and W2 = 'C_K(W1) *)
(*                   are nontrivial and cyclic of odd order; these conditions *)
(*                   imply that cyclicTI_hypothesis L defW holds.             *)
(*  -> This is Peterfalvi, Hypothesis (4.2), or Feit-Thompson (13.2).         *)
(*  prime_Dade_definition L K H A A0 defW <->                                 *)
(*                   A0 = A :|: class_support (cyclicTIset defW) L where A is *)
(*                   an L-invariant subset of K^# containing all the elements *)
(*                   of K that do not act freely on H <| L; in addition       *)
(*                   W2 \subset H \subset K.                                  *)
(*  prime_Dade_hypothesis G L K H A A0 defW <->                               *)
(*                   The four assumptions primeTI_hypothesis L K defW,        *)
(*                   cyclicTI_hypothesis G defW, Dade_hypothesis G L A0 and   *)
(*                   prime_Dade_definition L K H A A0 defW hold jointly.      *)
(*  -> This is Peterfalvi, Hypothesis (4.6), or Feit-Thompson (13.3) (except  *)
(*     that H is not required to be nilpotent, and the "supporting groups"    *)
(*     assumptions have been replaced by Dade hypothesis).                    *)
(*  -> This hypothesis is one of the alternatives under which Sibley's        *)
(*     coherence theorem holds (see PFsection6.v), and is verified by all     *)
(*     maximal subgroups of type P in a minimal simple odd group.             *)
(*  -> prime_Dade_hypothesis coerces to Dade_hypothesis, cyclicTI_hypothesis, *)
(*     primeTI_hypothesis and prime_Dade_definition.                          *)
(* For ptiW : primeTI_hypothesis L K defW we also define:                     *)
(*  prime_cycTIhyp ptiW :: cyclicTI_hypothesis L defW (though NOT a coercion) *)
(*  primeTIirr ptiW i j == the (unique) irreducible constituent of the image  *)
(*   (locally) mu2_ i j    in 'CF(L) of w_ i j = cyclicTIirr defW i j under   *)
(*                         the sigma = cyclicTIiso (prime_cycTIhyp ptiW).     *)
(* primeTI_Iirr ptiW ij == the index of mu2_ ij.1 ij.2; indeed mu2_ i j is    *)
(*                         just notation for 'chi_(primeTI_Iirr ptiW (i, j)). *)
(*   primeTIsign ptiW j == the sign of mu2_ i j in sigma (w_ i j), which does *)
(*   (locally) delta_ j    not depend on i.                                   *)
(* primeTI_Isign ptiW j == the boolean b such that delta_ j := (-1) ^+ b.     *)
(*    primeTIres ptiW j == the restriction to K of mu2_ i j, which is an      *)
(*     (locally) chi_ j    irreducible character that does not depend on i.   *)
(*  primeTI_Ires ptiW j == the index of chi_ j := 'chi_(primeTI_Ires ptiW j). *)
(*    primeTIred ptiW j == the (reducible) character equal to the sum of all  *)
(*      (locally) mu_ j    the mu2_ i j, and also to 'Ind (chi_ j).           *)
(* uniform_prTIred_seq ptiW k == the sequence of all the mu_ j, j != 0, with  *)
(*                         the same degree as mu_ k (s.t. mu_ j 1 = mu_ k 1). *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Four_1_to_2.

(* This is Peterfalvi (4.1). *)

Variable gT : finGroupType.

Lemma vchar_pairs_orthonormal (X : {group gT}) (a b c d : 'CF(X)) u v :
    {subset (a :: b) <= 'Z[irr X]} /\ {subset (c :: d) <= 'Z[irr X]} ->
    orthonormal (a :: b) && orthonormal (c :: d) ->
    [&& u \is Creal, v \is Creal, u != 0 & v != 0] ->
    [&& '[a - b, u *: c - v *: d] == 0,
         (a - b) 1%g == 0 & (u *: c - v *: d) 1%g == 0] ->
    orthonormal [:: a; b; c; d].
Proof.
have osym2 (e f : 'CF(X)) : orthonormal (e :: f) -> orthonormal (f :: e).
  by rewrite !(orthonormal_cat [::_] [::_]) orthogonal_sym andbCA.
have def_o f S: orthonormal (f :: S) -> '[f : 'CF(X)] = 1.
  by case/andP=> /andP[/eqP].
case=> /allP/and3P[Za Zb _] /allP/and3P[Zc Zd _] /andP[o_ab o_cd].
rewrite (orthonormal_cat (a :: b)) o_ab o_cd /=.
case/and4P=> r_u r_v nz_u nz_v /and3P[o_abcd ab1 cd1].
wlog suff: a b c d u v Za Zb Zc Zd o_ab o_cd r_u r_v nz_u nz_v o_abcd ab1 cd1 /
  '[a, c]_X == 0.
- move=> IH; rewrite /orthogonal /= !andbT (IH a b c d u v) //=.
  have vc_sym (e f : 'CF(X)) : ((e - f) 1%g == 0) = ((f - e) 1%g == 0).
    by rewrite -opprB cfunE oppr_eq0.
  have ab_sym e: ('[b - a, e] == 0) = ('[a - b, e] == 0).
    by rewrite -opprB cfdotNl oppr_eq0.
  rewrite (IH b a c d u v) // 1?osym2 1?vc_sym ?ab_sym //=.
  rewrite -oppr_eq0 -cfdotNr opprB in o_abcd.
  by rewrite (IH a b d c v u) ?(IH b a d c v u) // 1?osym2 1?vc_sym ?ab_sym.
apply: contraLR cd1 => nz_ac.
have [/orthonormal2P[ab0 a1 b1] /orthonormal2P[cd0 c1 d1]] := (o_ab, o_cd).
have [ea [ia def_a]] := vchar_norm1P Za a1.
have{nz_ac} [e defc]: exists e : bool, c = (-1) ^+ e *: a.
  have [ec [ic def_c]] := vchar_norm1P Zc c1; exists (ec (+) ea).
  move: nz_ac; rewrite def_a def_c scalerA; rewrite -signr_addb addbK.
  rewrite cfdotZl cfdotZr cfdot_irr mulrA mulrC mulf_eq0.
  by have [-> // | _]:= ia =P ic; rewrite eqxx.
have def_vbd: v * '[b, d]_X = - ((-1) ^+ e * u).
  apply/eqP; have:= o_abcd; rewrite cfdotDl cfdotNl !raddfB /=.
  rewrite defc !cfdotZr a1 (cfdotC b) ab0 rmorph0 mulr1.
  rewrite -[a]scale1r -{2}[1]/((-1) ^+ false) -(addbb e) signr_addb -scalerA.
  rewrite -defc cfdotZl cd0 !mulr0 opprK addrA !subr0 mulrC addrC addr_eq0.
  by rewrite rmorph_sign !conj_Creal.
have nz_bd: '[b, d] != 0.
  move/esym/eqP: def_vbd; apply: contraTneq => ->.
  by rewrite mulr0 oppr_eq0 mulf_eq0 signr_eq0.
have{nz_bd} defd: d = '[b, d] *: b.
  move: nz_bd; have [eb [ib ->]] := vchar_norm1P Zb b1.
  have [ed [id ->]] := vchar_norm1P Zd d1.
  rewrite scalerA cfdotZl cfdotZr rmorph_sign mulrA cfdot_irr.
  have [-> _ | _] := ib =P id; last by rewrite !mulr0 eqxx.
  by rewrite mulr1 mulrAC -!signr_addb addbb.
rewrite defd scalerA def_vbd scaleNr opprK defc scalerA mulrC -raddfD cfunE.
rewrite !mulf_neq0 ?signr_eq0 // -(subrK a b) -opprB addrCA 2!cfunE.
rewrite (eqP ab1) oppr0 add0r cfunE -mulr2n -mulr_natl mulf_eq0 pnatr_eq0.
by rewrite /= def_a cfunE mulf_eq0 signr_eq0 /= irr1_neq0.
Qed.

Corollary orthonormal_vchar_diff_ortho (X : {group gT}) (a b c d : 'CF(X)) :
    {subset a :: b <= 'Z[irr X]} /\ {subset c :: d <= 'Z[irr X]} ->
    orthonormal (a :: b) && orthonormal (c :: d) ->
    [&& '[a - b, c - d] == 0, (a - b) 1%g == 0 & (c - d) 1%g == 0] ->
  '[a, c] = 0.
Proof.
move=> Zabcd Oabcd; rewrite -[c - d]scale1r scalerBr.
move/(vchar_pairs_orthonormal Zabcd Oabcd) => /implyP.
rewrite rpred1 oner_eq0 (orthonormal_cat (a :: b)) /=.
by case/and3P=> _ _ /andP[] /andP[] /eqP.
Qed.

(* This is Peterfalvi, Hypothesis (4.2), with explicit parameters. *)
Definition primeTI_hypothesis (L K W W1 W2 : {set gT}) of W1 \x W2 = W :=
  [/\ (*a*) [/\ K ><| W1 = L, W1 != 1, Hall L W1 & cyclic W1],
      (*b*) [/\ W2 != 1, W2 \subset K & cyclic W2],
            {in W1^#, forall x, 'C_K[x] = W2}
   &  (*c*) odd #|W|]%g.

End Four_1_to_2.

Arguments Scope primeTI_hypothesis
  [_ group_scope group_scope group_scope _ group_scope group_scope].

Section Four_3_to_5.

Variables (gT : finGroupType) (L K W W1 W2 : {group gT}) (defW : W1 \x W2 = W).
Hypothesis ptiWL : primeTI_hypothesis L K defW.

Let V := cyclicTIset defW.
Let w1 := #|W1|.
Let w2 := #|W2|.

Let defL : K ><| W1 = L. Proof. by have [[]] := ptiWL. Qed.
Let ntW1 : W1 :!=: 1%g. Proof. by have [[]] := ptiWL. Qed.
Let cycW1 : cyclic W1. Proof. by have [[]] := ptiWL. Qed.
Let hallW1 : Hall L W1. Proof. by have [[]] := ptiWL. Qed.

Let ntW2 : W2 :!=: 1%g. Proof. by have [_ []] := ptiWL. Qed.
Let sW2K : W2 \subset K. Proof. by have [_ []] := ptiWL. Qed.
Let cycW2 : cyclic W2. Proof. by have [_ []] := ptiWL. Qed.
Let prKW1 : {in W1^#, forall x, 'C_K[x] = W2}. Proof. by have [] := ptiWL. Qed.

Let oddW : odd #|W|. Proof. by have [] := ptiWL. Qed.

Let nsKL : K <| L. Proof. by case/sdprod_context: defL. Qed.
Let sKL : K \subset L. Proof. by case/andP: nsKL. Qed.
Let sW1L : W1 \subset L. Proof. by case/sdprod_context: defL. Qed.
Let sWL : W \subset L.
Proof. by rewrite -(dprodWC defW) -(sdprodW defL) mulgSS. Qed.
Let sW1W : W1 \subset W. Proof. by have /mulG_sub[] := dprodW defW. Qed.
Let sW2W : W2 \subset W. Proof. by have /mulG_sub[] := dprodW defW. Qed.

Let coKW1 : coprime #|K| #|W1|.
Proof. by rewrite (coprime_sdprod_Hall_r defL). Qed.
Let coW12 : coprime #|W1| #|W2|.
Proof. by rewrite coprime_sym (coprimeSg sW2K). Qed.

Let cycW : cyclic W. Proof. by rewrite (cyclic_dprod defW). Qed.
Let cWW : abelian W. Proof. exact: cyclic_abelian. Qed.
Let oddW1 : odd w1. Proof. exact: oddSg oddW. Qed.
Let oddW2 : odd w2. Proof. exact: oddSg oddW. Qed.

Let ntV : V != set0.
Proof.
by rewrite -card_gt0 card_cycTIset muln_gt0 -!subn1 !subn_gt0 !cardG_gt1 ntW1.
Qed.

Let sV_V2 : V \subset W :\: W2. Proof. by rewrite setDS ?subsetUr. Qed.

Lemma primeTIhyp_quotient (M : {group gT}) :
    (W2 / M != 1)%g -> M \subset K -> M <| L ->
  {defWbar : (W1 / M) \x (W2 / M) = W / M
           & primeTI_hypothesis (L / M) (K / M) defWbar}%g.
Proof.
move=> ntW2bar sMK /andP[_ nML].
have coMW1: coprime #|M| #|W1| by rewrite (coprimeSg sMK).
have [nMW1 nMW] := (subset_trans sW1L nML, subset_trans sWL nML).
have defWbar: (W1 / M) \x (W2 / M) = (W / M)%g.
  by rewrite (quotient_coprime_dprod nMW) ?quotient_odd.
exists defWbar; split; rewrite ?quotient_odd ?quotient_cyclic ?quotientS //.
  have isoW1: W1 \isog W1 / M by rewrite quotient_isog ?coprime_TIg.
  by rewrite -(isog_eq1 isoW1) ?morphim_Hall // (quotient_coprime_sdprod nML).
move=> Kx /setD1P[ntKx /morphimP[x nKx W1x defKx]] /=.
rewrite -cent_cycle -cycle_eq1 {Kx}defKx -quotient_cycle // in ntKx *.
rewrite -strongest_coprime_quotient_cent ?cycle_subG //; first 1 last.
- by rewrite subIset ?sMK.
- by rewrite (coprimeSg (subsetIl M _)) // (coprimegS _ coMW1) ?cycle_subG.
- by rewrite orbC abelian_sol ?cycle_abelian.
rewrite cent_cycle prKW1 // !inE W1x (contraNneq _ ntKx) // => ->.
by rewrite cycle1 quotient1.
Qed.

(* This is the first part of PeterFalvi, Theorem (4.3)(a). *)
Theorem normedTI_prTIset : normedTI (W :\: W2) L W.
Proof.
have [[_ _ cW12 _] [_ _ nKW1 tiKW1]] := (dprodP defW, sdprodP defL).
have nV2W: W \subset 'N(W :\: W2) by rewrite sub_abelian_norm ?subsetDl.
have piW1_W: {in W1 & W2, forall x y, (x * y).`_\pi(W1) = x}.
  move=> x y W1x W2y /=; rewrite consttM /commute ?(centsP cW12 y) //.
  rewrite constt_p_elt ?(mem_p_elt _ W1x) ?pgroup_pi // (constt1P _) ?mulg1 //.
  by rewrite /p_elt -coprime_pi' // (coprimegS _ coW12) ?cycle_subG.
have nzV2W: W :\: W2 != set0 by apply: contraNneq ntV; rewrite -subset0 => <-.
apply/normedTI_memJ_P; split=> // xy g V2xy Lg.
apply/idP/idP=> [| /(subsetP nV2W)/memJ_norm->//].
have{xy V2xy} [/(mem_dprod defW)[x [y [W1x W2y -> _]]] W2'xy] := setDP V2xy.
have{W2'xy} ntx: x != 1%g by have:= W2'xy; rewrite groupMr // => /group1_contra.
have{g Lg} [k [w [Kk /(subsetP sW1W)Ww -> _]]] := mem_sdprod defL Lg.
rewrite conjgM memJ_norm ?(subsetP nV2W) ?(groupMr k) // => /setDP[Wxyk _].
have{Wxyk piW1_W} W1xk: x ^ k \in W1.
  have [xk [yk [W1xk W2yk Dxyk _]]] := mem_dprod defW Wxyk.
  by rewrite -(piW1_W x y) // -consttJ Dxyk piW1_W.
rewrite (subsetP sW2W) // -(@prKW1 x) ?in_setD1 ?ntx // inE Kk /=.
rewrite cent1C (sameP cent1P commgP) -in_set1 -set1gE -tiKW1 inE.
by rewrite (subsetP _ _ (mem_commg W1x Kk)) ?commg_subr // groupM ?groupV.
Qed.

(* Second part of PeterFalvi, Theorem (4.3)(a). *)
Theorem prime_cycTIhyp : cyclicTI_hypothesis L defW.
Proof.
have nVW: W \subset 'N(V) by rewrite sub_abelian_norm ?subsetDl.
by split=> //; apply: normedTI_S normedTI_prTIset.
Qed.
Local Notation ctiW := prime_cycTIhyp.
Let sigma := cyclicTIiso ctiW.
Let w_ i j := cyclicTIirr defW i j.

Let Wlin k : 'chi[W]_k \is a linear_char. Proof. exact/irr_cyclic_lin. Qed.
Let W1lin i : 'chi[W1]_i \is a linear_char. Proof. exact/irr_cyclic_lin. Qed.
Let W2lin i : 'chi[W2]_i \is a linear_char. Proof. exact/irr_cyclic_lin. Qed.
Let w_lin i j : w_ i j \is a linear_char. Proof. exact: Wlin. Qed.

Let nirrW1 : #|Iirr W1| = w1. Proof. exact: card_Iirr_cyclic. Qed.
Let nirrW2 : #|Iirr W2| = w2. Proof. exact: card_Iirr_cyclic. Qed.
Let NirrW1 : Nirr W1 = w1. Proof. by rewrite -nirrW1 card_ord. Qed.
Let NirrW2 : Nirr W2 = w2. Proof. by rewrite -nirrW2 card_ord. Qed.
Let w1gt1 : (1 < w1)%N. Proof. by rewrite cardG_gt1. Qed.

Let cfdot_w i1 j1 i2 j2 : '[w_ i1 j1, w_ i2 j2] = ((i1 == i2) && (j1 == j2))%:R.
Proof. exact: cfdot_dprod_irr. Qed.

(* Witnesses for Theorem (4.3)(b). *)
Fact primeTIdIirr_key : unit. Proof. by []. Qed.
Definition primeTIdIirr_def := dirr_dIirr (sigma \o prod_curry w_).
Definition primeTIdIirr := locked_with primeTIdIirr_key primeTIdIirr_def.
Definition primeTI_Iirr ij := (primeTIdIirr ij).2.
Definition primeTI_Isign j := (primeTIdIirr (0, j)).1.
Local Notation Imu2 := primeTI_Iirr.
Local Notation mu2_ i j := 'chi_(primeTI_Iirr (i, j)).
Local Notation delta_ j := (GRing.sign algCring (primeTI_Isign j)).

Let ew_ i j := w_ i j - w_ 0 j.
Let V2ew i j : ew_ i j \in 'CF(W, W :\: W2).
Proof.
apply/cfun_onP=> x; rewrite !inE negb_and negbK => /orP[W2x | /cfun0->//].
by rewrite -[x]mul1g !cfunE /w_ !dprod_IirrE !cfDprodE ?lin_char1 ?subrr.
Qed.

(* This is Peterfalvi, Theorem (4.3)(b, c). *)
Theorem primeTIirr_spec :
 [/\ (*b*) injective Imu2,
           forall i j, 'Ind (ew_ i j) = delta_ j *: (mu2_ i j - mu2_ 0 j),
           forall i j, sigma (w_ i j) = delta_ j *: mu2_ i j,
     (*c*) forall i j, {in W :\: W2, mu2_ i j =1 delta_ j *: w_ i j}
         & forall k, k \notin codom Imu2 -> {in W :\: W2, 'chi_k =1 \0}].
Proof.
have isoV2 := normedTI_isometry normedTI_prTIset (setDSS sWL (sub1G W2)).
have /fin_all_exists2[dmu injl_mu Ddmu] j:
  exists2 dmu : bool * {ffun Iirr W1 -> Iirr L}, injective dmu.2
    & forall i, 'Ind (ew_ i j) = dchi (dmu.1, dmu.2 i) - dchi (dmu.1, dmu.2 0).
- pose Sj := [tuple w_ i j | i < Nirr W1].
  have Sj0: Sj`_0 = w_ 0 j by rewrite (nth_mktuple _ 0 0).
  have irrSj: {subset Sj <= irr W} by move=> ? /mapP[i _ ->]; apply: mem_irr.
  have: {in 'Z[Sj, W :\: W2], isometry 'Ind, to 'Z[irr L, L^#]}.
    split=> [|phi]; first by apply: sub_in2 isoV2; apply: zchar_on.
    move/(zchar_subset irrSj)/(zchar_onS (setDS W (sub1G W2))).
    by rewrite !zcharD1E cfInd1 // mulf_eq0 orbC => /andP[/cfInd_vchar-> // ->].
  case/vchar_isometry_base=> // [|||i|mu Umu [d Ddmu]]; first by rewrite NirrW1.
  + rewrite orthonormal_free // (sub_orthonormal irrSj) ?irr_orthonormal //.
    by apply/injectiveP=> i1 i2 /irr_inj/dprod_Iirr_inj[].
  + by move=> _ /mapP[i _ ->]; rewrite Sj0 !lin_char1.
  + by rewrite nth_mktuple Sj0 V2ew.
  exists (d, [ffun i => tnth mu i]) => [|i].
    apply/injectiveP; congr (uniq _): Umu.
    by rewrite (eq_map (ffunE _)) map_tnth_enum.
  by rewrite -scalerBr /= !ffunE !(tnth_nth 0 mu) -Ddmu nth_mktuple Sj0.
pose Imu ij := (dmu ij.2).2 ij.1; pose mu i j := 'chi_(Imu (i, j)).
pose d j : algC := (-1) ^+ (dmu j).1.
have{Ddmu} Ddmu i j: 'Ind (ew_ i j) = d j *: (mu i j - mu 0 j).
  by rewrite Ddmu scalerBr.
have{injl_mu} inj_Imu: injective Imu.
  move=> [i1 j1] [i2 j2]; rewrite /Imu /=; pose S i j k := mu i j :: mu k j.
  have [-> /injl_mu-> // | j2'1 /eqP/negPf[] /=] := eqVneq j1 j2.
  apply/(can_inj oddb)/eqP; rewrite -eqC_nat -cfdot_irr -!/(mu _ _) mulr0n.
  have oIew_j12 i k: '['Ind[L] (ew_ i j1), 'Ind[L] (ew_ k j2)] = 0.
    by rewrite isoV2 // cfdotBl !cfdotBr !cfdot_w (negPf j2'1) !andbF !subr0.
  have defSd i j k: mu i j - mu k j = d j *: ('Ind (ew_ i j) - 'Ind (ew_ k j)).
    by rewrite !Ddmu -scalerBr signrZK opprB addrA subrK.
  have Sd1 i j k: (mu i j - mu k j) 1%g == 0.
    by rewrite defSd !(cfunE, cfInd1) ?lin_char1 // !subrr mulr0.
  have exS i j: {k | {subset S i j k <= 'Z[irr L]} & orthonormal (S i j k)}.
    have:= w1gt1; rewrite -nirrW1 (cardD1 i) => /card_gt0P/sigW[k /andP[i'k _]].
    exists k; first by apply/allP; rewrite /= !irr_vchar.
    apply/andP; rewrite /= !cfdot_irr !eqxx !andbT /=.
    by rewrite (inj_eq (injl_mu j)) mulrb ifN_eqC.
  have [[k1 ZS1 o1S1] [k2 ZS2 o1S2]] := (exS i1 j1, exS i2 j2).
  rewrite (orthonormal_vchar_diff_ortho (conj ZS1 ZS2)) ?o1S1 ?Sd1 ?andbT //.
  by rewrite !defSd cfdotZl cfdotZr cfdotBl !cfdotBr !oIew_j12 !subrr !mulr0.
pose V2base := [tuple of [seq ew_ ij.1 ij.2 | ij in predX (predC1 0) predT]].
have V2basis: basis_of 'CF(W, W :\: W2) V2base.
  suffices V2free: free V2base.
    rewrite basisEfree V2free size_image /= cardX cardC1 nirrW1 nirrW2 -subn1.
    rewrite mulnBl mul1n dim_cfun_on_abelian ?subsetDl //.
    rewrite cardsD (setIidPr _) //  (dprod_card defW) leqnn andbT.
    by apply/span_subvP=> _ /mapP[ij _ ->].
  apply/freeP=> /= z zV2e0 k.
  move Dk: (enum_val k) (enum_valP k) => [i j] /andP[/= nz_i _].
  rewrite -(cfdot0l (w_ i j)) -{}zV2e0 cfdot_suml (bigD1 k) //= cfdotZl.
  rewrite nth_image Dk cfdotBl !cfdot_w !eqxx eq_sym (negPf nz_i) subr0 mulr1.
  rewrite big1 ?addr0 // => k1; rewrite -(inj_eq enum_val_inj) {}Dk nth_image.
  case: (enum_val k1) => /= i1 j1 ij'ij1.
  rewrite cfdotZl cfdotBl !cfdot_dprod_irr [_ && _](negPf ij'ij1).
  by rewrite eq_sym (negPf nz_i) subr0 mulr0.
have nsV2W: W :\: W2 <| W by rewrite -sub_abelian_normal ?subsetDl.
pose muW k := let: ij := inv_dprod_Iirr defW k in d ij.2 *: mu ij.1 ij.2.
have inW := codomP (dprod_Iirr_onto defW _).
have ImuW k1 k2: '[muW k1, muW k2] = (k1 == k2)%:R.
  have [[[i1 j1] -> {k1}] [[i2 j2] -> {k2}]] := (inW k1, inW k2).
  rewrite cfdotZl cfdotZr !dprod_IirrK (can_eq (dprod_IirrK _)) /= rmorph_sign.
  rewrite cfdot_irr (inj_eq inj_Imu (_, _) (_, _)) -/(d _).
  by case: eqP => [[_ ->] | _]; rewrite ?signrMK ?mulr0.
have [k|muV2 mu'V2] := equiv_restrict_compl_ortho sWL nsV2W V2basis ImuW.
  rewrite nth_image; case: (enum_val k) (enum_valP k) => /= i j /andP[/= nzi _].
  pose inWj i1 := dprod_Iirr defW (i1, j); rewrite (bigD1 (inWj 0)) //=.
  rewrite (bigD1 (inWj i)) ?(can_eq (dprod_IirrK _)) ?xpair_eqE ?(negPf nzi) //.
  rewrite /= big1 ?addr0 => [|k1 /andP[]]; last first.
    rewrite !(eq_sym k1); have [[i1 j1] -> {k1}] := inW k1.
    rewrite !(can_eq (dprod_IirrK _)) => ij1'i ij1'0.
    by rewrite cfdotBl !cfdot_w !mulrb !ifN // subrr scale0r.
  rewrite /muW !dprod_IirrK /= addrC !cfdotBl !cfdot_w !eqxx /= !andbT.
  by rewrite eq_sym (negPf nzi) subr0 add0r scaleNr !scale1r -scalerBr.
have Dsigma i j: sigma (w_ i j) = d j *: mu i j.
  apply/esym/eq_in_cycTIiso=> [|x Vx]; first exact: (dirr_dchi (_, _)).
  by rewrite -muV2 ?(subsetP sV_V2) // /muW dprod_IirrK.
have /all_and2[Dd Dmu] j: d j = delta_ j /\ forall i, Imu (i, j) = Imu2 (i, j).
  suffices DprTI i: primeTIdIirr (i, j) = ((dmu j).1, (dmu j).2 i).
    by split=> [|i]; rewrite /primeTI_Isign /Imu2 DprTI.
  apply: dirr_inj; rewrite /primeTIdIirr unlock_with dirr_dIirrE /= ?Dsigma //.
  by case=> i1 j1; apply: cycTIiso_dirr.
split=> [[i1 j1] [i2 j2] | i j | i j | i j x V2x | k mu2p'k].
- by rewrite -!Dmu => /inj_Imu.
- by rewrite -!Dmu -Dd -Ddmu.
- by rewrite -Dmu -Dd -Dsigma.
- by rewrite cfunE -muV2 // /muW dprod_IirrK Dd cfunE signrMK -Dmu.
apply: mu'V2 => k1; have [[i j] ->{k1}] := inW k1.
apply: contraNeq mu2p'k; rewrite cfdotZr rmorph_sign mulf_eq0 signr_eq0 /=.
rewrite /mu Dmu dprod_IirrK -irr_consttE constt_irr inE /= => /eqP <-.
exact: codom_f.
Qed.

(* These lemmas restate the various parts of Theorem (4.3)(b, c) separately. *)
Lemma prTIirr_inj : injective Imu2. Proof. by case: primeTIirr_spec. Qed.

Corollary cfdot_prTIirr i1 j1 i2 j2 :
  '[mu2_ i1 j1, mu2_ i2 j2] = ((i1 == i2) && (j1 == j2))%:R.
Proof. by rewrite cfdot_irr (inj_eq prTIirr_inj). Qed.

Lemma cfInd_sub_prTIirr i j :
  'Ind[L] (w_ i j - w_ 0 j) = delta_ j *: (mu2_ i j - mu2_ 0 j).
Proof. by case: primeTIirr_spec i j. Qed.

Lemma cycTIiso_prTIirr i j : sigma (w_ i j) = delta_ j *: mu2_ i j.
Proof. by case: primeTIirr_spec. Qed.

Lemma prTIirr_id i j : {in W :\: W2, mu2_ i j =1 delta_ j *: w_ i j}.
Proof. by case: primeTIirr_spec. Qed.

Lemma not_prTIirr_vanish k : k \notin codom Imu2 -> {in W :\: W2, 'chi_k =1 \0}.
Proof. by case: primeTIirr_spec k. Qed.

(* This is Peterfalvi, Theorem (4.3)(d). *)
Theorem prTIirr1_mod i j : (mu2_ i j 1%g == delta_ j %[mod w1])%C.
Proof.
rewrite -(cfRes1 W1) -['Res _](subrK ('Res (delta_ j *: w_ i j))) cfunE.
set phi := _ - _; pose a := '[phi, 1].
have phi_on_1: phi \in 'CF(W1, 1%g).
  apply/cfun_onP=> g; have [W1g | /cfun0-> //] := boolP (g \in W1).
  rewrite -(coprime_TIg coW12) inE W1g !cfunE !cfResE //= => W2'g.
  by rewrite prTIirr_id ?cfunE ?subrr // inE W2'g (subsetP sW1W).
have{phi_on_1} ->: phi 1%g = a * w1%:R.
  rewrite mulrC /a (cfdotEl _ phi_on_1) mulVKf ?neq0CG //.
  by rewrite big_set1 cfun11 conjC1 mulr1.
rewrite cfResE // cfunE lin_char1 // mulr1 eqCmod_addl_mul //.
by rewrite Cint_cfdot_vchar ?rpred1 ?rpredB ?cfRes_vchar ?rpredZsign ?irr_vchar.
Qed.

Lemma prTIsign_aut u j : delta_ (aut_Iirr u j) = delta_ j.
Proof.
have /eqP := cfAut_cycTIiso ctiW u (w_ 0 j).
rewrite -cycTIirr_aut aut_Iirr0 -/sigma !cycTIiso_prTIirr raddfZsign /=.
by rewrite -aut_IirrE eq_scaled_irr => /andP[/eqP].
Qed.

Lemma prTIirr_aut u i j :
  mu2_ (aut_Iirr u i) (aut_Iirr u j) = cfAut u (mu2_ i j).
Proof.
rewrite -!(canLR (signrZK _) (cycTIiso_prTIirr _ _)) -!/(delta_ _).
by rewrite prTIsign_aut raddfZsign /= cfAut_cycTIiso -cycTIirr_aut.
Qed.

(* The (reducible) column sums of the prime TI irreducibles. *)
Definition primeTIred j : 'CF(L) := \sum_i mu2_ i j.
Local Notation mu_ := primeTIred.

Definition uniform_prTIred_seq j0 :=
  image mu_ [pred j | j != 0 & mu_ j 1%g == mu_ j0 1%g].

Lemma prTIred_aut u j : mu_ (aut_Iirr u j) = cfAut u (mu_ j).
Proof.
rewrite raddf_sum [mu_ _](reindex_inj (aut_Iirr_inj u)).
by apply: eq_bigr => i _; rewrite /= prTIirr_aut.
Qed.

Lemma cfdot_prTIirr_red i j k : '[mu2_ i j, mu_ k] = (j == k)%:R.
Proof.
rewrite cfdot_sumr (bigD1 i) // cfdot_prTIirr eqxx /=.
rewrite big1 ?addr0 // => i1 neq_i1i.
by rewrite cfdot_prTIirr eq_sym (negPf neq_i1i).
Qed.

Lemma cfdot_prTIred j1 j2 : '[mu_ j1, mu_ j2] = ((j1 == j2) * w1)%:R.
Proof.
rewrite cfdot_suml (eq_bigr _ (fun i _ => cfdot_prTIirr_red i _ _)) sumr_const.
by rewrite mulrnA card_Iirr_cyclic.
Qed.

Lemma cfnorm_prTIred j : '[mu_ j] = w1%:R.
Proof. by rewrite cfdot_prTIred eqxx mul1n. Qed.

Lemma prTIred_neq0 j : mu_ j != 0.
Proof. by rewrite -cfnorm_eq0 cfnorm_prTIred neq0CG. Qed.

Lemma prTIred_char j : mu_ j \is a character.
Proof. by apply: rpred_sum => i _; apply: irr_char. Qed.

Lemma prTIred_1_gt0 j : 0 < mu_ j 1%g.
Proof. by rewrite char1_gt0 ?prTIred_neq0 ?prTIred_char. Qed.

Lemma prTIred_1_neq0 i : mu_ i 1%g != 0.
Proof. by rewrite char1_eq0 ?prTIred_neq0 ?prTIred_char. Qed.

Lemma prTIred_inj : injective mu_.
Proof.
move=> j1 j2 /(congr1 (cfdot (mu_ j1)))/esym/eqP; rewrite !cfdot_prTIred.
by rewrite eqC_nat eqn_pmul2r ?cardG_gt0 // eqxx; case: (j1 =P j2).
Qed. 

Lemma prTIred_not_real j : j != 0 -> ~~ cfReal (mu_ j).
Proof.
apply: contraNneq; rewrite -prTIred_aut -irr_eq1 -odd_eq_conj_irr1 //.
by rewrite -aut_IirrE => /prTIred_inj->.
Qed.

Lemma prTIsign0 : delta_ 0 = 1.
Proof.
have /esym/eqP := cycTIiso_prTIirr 0 0; rewrite -[sigma _]scale1r.
by rewrite /w_ /sigma cycTIirr00 cycTIiso1 -irr0 eq_scaled_irr => /andP[/eqP].
Qed.

Lemma prTIirr00 : mu2_ 0 0 = 1.
Proof.
have:= cycTIiso_prTIirr 0 0; rewrite prTIsign0 scale1r.
by rewrite /w_ /sigma cycTIirr00 cycTIiso1.
Qed.

(* This is PeterFalvi (4.4). *)
Lemma prTIirr0P k :
  reflect (exists i, 'chi_k = mu2_ i 0) (K \subset cfker 'chi_k).
Proof.
suff{k}: [set k | K \subset cfker 'chi_k] == [set Imu2 (i, 0) | i : Iirr W1].
  move/eqP/setP/(_ k); rewrite inE => ->.
  by apply: (iffP imsetP) => [[i _]|[i /irr_inj]] ->; exists i.
have [isoW1 abW1] := (sdprod_isog defL, cyclic_abelian cycW1).
have abLbar: abelian (L / K) by rewrite -(isog_abelian isoW1).
rewrite eqEcard andbC card_imset ?nirrW1 => [| i1 i2 /prTIirr_inj[] //].
rewrite [w1](card_isog isoW1) -card_Iirr_abelian //.
rewrite -(card_image (can_inj (mod_IirrK nsKL))) subset_leq_card; last first.
  by apply/subsetP=> _ /imageP[k1 _ ->]; rewrite inE mod_IirrE ?cfker_mod.
apply/subsetP=> k; rewrite inE => kerKk.
have /irrP[ij DkW]: 'Res 'chi_k \in irr W.
  rewrite lin_char_irr ?cfRes_lin_char // lin_irr_der1.
  by apply: subset_trans kerKk; rewrite der1_min ?normal_norm.
have{ij DkW} [i DkW]: exists i, 'Res 'chi_k = w_ i 0.
  have /codomP[[i j] Dij] := dprod_Iirr_onto defW ij; exists i.
  rewrite DkW Dij; congr (w_ i _); apply/eqP; rewrite -subGcfker.
  rewrite -['chi_j](cfDprodKr_abelian defW i) // -dprod_IirrE -{}Dij -{}DkW.
  by rewrite cfResRes // sub_cfker_Res // (subset_trans sW2K kerKk).
apply/imsetP; exists i => //=; apply/irr_inj.
suffices ->: 'chi_k = delta_ 0 *: mu2_ i 0 by rewrite prTIsign0 scale1r.
rewrite -cycTIiso_prTIirr -(eq_in_cycTIiso _ (irr_dirr k)) // => x /setDP[Wx _].
by rewrite -/(w_ i 0) -DkW cfResE.
Qed.

(* This is the first part of PeterFalvi, Theorem (4.5)(a). *)
Theorem cfRes_prTIirr_eq0 i j : 'Res[K] (mu2_ i j) = 'Res (mu2_ 0 j).
Proof.
apply/eqP; rewrite -subr_eq0 -rmorphB /=; apply/eqP/cfun_inP=> x0 Kx0.
rewrite -(canLR (signrZK _) (cfInd_sub_prTIirr i j)) -/(delta_ j).
rewrite cfResE // !cfunE (cfun_on0 (cfInd_on _ (V2ew i j))) ?mulr0 //.
apply: contraL Kx0 => /imset2P[x y /setDP[Wx W2'x] Ly ->] {x0}.
rewrite memJ_norm ?(subsetP (normal_norm nsKL)) //; apply: contra W2'x => Kx.
by rewrite -(mul1g W2) -(coprime_TIg coKW1) group_modr // inE Kx (dprodW defW).
Qed.

Lemma prTIirr_1 i j : mu2_ i j 1%g = mu2_ 0 j 1%g.
Proof. by rewrite -!(@cfRes1 _ K L) cfRes_prTIirr_eq0. Qed.

Lemma prTIirr0_1 i : mu2_ i 0 1%g = 1.
Proof. by rewrite prTIirr_1 prTIirr00 cfun11. Qed.

Lemma prTIirr0_linear i : mu2_ i 0 \is a linear_char.
Proof. by rewrite qualifE irr_char /= prTIirr0_1. Qed.

Lemma prTIred_1 j : mu_ j 1%g = w1%:R * mu2_ 0 j 1%g.
Proof.
rewrite mulr_natl -nirrW1 sum_cfunE.
by rewrite -sumr_const; apply: eq_bigr => i _; rewrite prTIirr_1.
Qed.

Definition primeTI_Ires j : Iirr K := cfIirr ('Res[K] (mu2_ 0 j)).
Local Notation Ichi := primeTI_Ires.
Local Notation chi_ j := 'chi_(Ichi j).

(* This is the rest of PeterFalvi, Theorem (4.5)(a). *)
Theorem prTIres_spec j : chi_ j = 'Res (mu2_ 0 j) /\ mu_ j = 'Ind (chi_ j).
Proof.
rewrite /Ichi; set chi_j := 'Res _.
have [k chi_j_k]: {k | k \in irr_constt chi_j} := constt_cfRes_irr K _.
have Nchi_j: chi_j \is a character by rewrite cfRes_char ?irr_char.
have lb_mu_1: w1%:R * 'chi_k 1%g <= mu_ j 1%g ?= iff (chi_j == 'chi_k).
  have [chi' Nchi' Dchi_j] := constt_charP _ Nchi_j chi_j_k.
  rewrite prTIred_1 (mono_lerif (ler_pmul2l (gt0CG W1))).
  rewrite -subr_eq0 Dchi_j addrC addKr -(canLR (addrK _) Dchi_j) !cfunE.
  rewrite lerif_subLR addrC -lerif_subLR cfRes1 subrr -char1_eq0 // eq_sym.
  by apply: lerif_eq; rewrite char1_ge0.
pose psi := 'Ind 'chi_k - mu_ j; have Npsi: psi \is a character.
  apply/forallP=> l; rewrite coord_cfdot cfdotBl; set a := '['Ind _, _].
  have Na: a \in Cnat by rewrite Cnat_cfdot_char_irr ?cfInd_char ?irr_char.
  have [[i /eqP Dl] | ] := altP (@existsP _ (fun i => 'chi_l == mu2_ i j)).
    have [n Da] := CnatP a Na; rewrite Da cfdotC Dl cfdot_prTIirr_red.
    rewrite rmorph_nat -natrB ?Cnat_nat // eqxx lt0n -eqC_nat -Da.
    by rewrite -irr_consttE constt_Ind_Res Dl cfRes_prTIirr_eq0.
  rewrite negb_exists => /forallP muj'l.
  rewrite cfdot_suml big1 ?subr0 // => i _.
  rewrite cfdot_irr -(inj_eq irr_inj) mulrb ifN_eqC ?muj'l //.
have ub_mu_1: mu_ j 1%g <= 'Ind[L] 'chi_k 1%g ?= iff ('Ind 'chi_k == mu_ j).
  rewrite -subr_eq0 -/psi (canRL (subrK _) (erefl psi)) cfunE -lerif_subLR.
  by rewrite subrr -char1_eq0 // eq_sym; apply: lerif_eq; rewrite char1_ge0.
have [_ /esym] := lerif_trans lb_mu_1 ub_mu_1; rewrite cfInd1 //.
by rewrite -(index_sdprod defL) eqxx => /andP[/eqP-> /eqP <-]; rewrite irrK.
Qed.

Lemma cfRes_prTIirr i j : 'Res[K] (mu2_ i j) = chi_ j.
Proof. by rewrite cfRes_prTIirr_eq0; case: (prTIres_spec j). Qed.

Lemma cfInd_prTIres j : 'Ind[L] (chi_ j) = mu_ j.
Proof. by have [] := prTIres_spec j. Qed.

Lemma cfRes_prTIred j : 'Res[K] (mu_ j) = w1%:R *: chi_ j.
Proof.
rewrite -nirrW1 scaler_nat -sumr_const linear_sum /=; apply: eq_bigr => i _.
exact: cfRes_prTIirr.
Qed.

Lemma prTIres_aut u j : chi_ (aut_Iirr u j) = cfAut u (chi_ j).
Proof.
by rewrite -(cfRes_prTIirr (aut_Iirr u 0)) prTIirr_aut -cfAutRes cfRes_prTIirr.
Qed.

Lemma prTIres0 : chi_ 0 = 1.
Proof. by rewrite -(cfRes_prTIirr 0) prTIirr00 cfRes_cfun1. Qed.

Lemma prTIred0 : mu_ 0 = w1%:R *: '1_K.
Proof.
by rewrite -cfInd_prTIres prTIres0 cfInd_cfun1 // -(index_sdprod defL).
Qed.

Lemma prTIres_inj : injective Ichi.
Proof. by move=> j1 j2 Dj; apply: prTIred_inj; rewrite -!cfInd_prTIres Dj. Qed.

(* This is the first assertion of Peterfalvi (4.5)(b). *)
Theorem prTIres_irr_cases k (theta := 'chi_k) (phi := 'Ind theta) :
  {j | theta = chi_ j} + {phi \in irr L /\ (forall i j, phi != mu2_ i j)}.
Proof.
pose imIchi := [set Ichi j | j : Iirr W2].
have [/imsetP/sig2_eqW[j _] | imIchi'k] := boolP (k \in imIchi).
  by rewrite /theta => ->; left; exists j.
suffices{phi} theta_inv: 'I_L[theta] = K.
  have irr_phi: phi \in irr L by apply: inertia_Ind_irr; rewrite ?theta_inv.
  right; split=> // i j; apply: contraNneq imIchi'k => Dphi; apply/imsetP.
  exists j => //; apply/eqP; rewrite -[k == _]constt_irr -(cfRes_prTIirr i).
  by rewrite -constt_Ind_Res -/phi Dphi irr_consttE cfnorm_irr oner_eq0.
rewrite -(sdprodW (sdprod_modl defL (sub_inertia _))); apply/mulGidPl.
apply/subsetP=> z /setIP[W1z Itheta_z]; apply: contraR imIchi'k => K'z.
have{K'z} [Lz ntz] := (subsetP sW1L z W1z, group1_contra K'z : z != 1%g).
have [p p_pr p_z]: {p | prime p & p %| #[z]} by apply/pdivP; rewrite order_gt1.
have coKp := coprime_dvdr (dvdn_trans p_z (order_dvdG W1z)) coKW1.
wlog{p_z} p_z: z W1z Lz Itheta_z ntz / p.-elt z.
  move/(_ z.`_p)->; rewrite ?groupX ?p_elt_constt //.
  by rewrite (sameP eqP constt1P) /p_elt p'natE ?negbK.
have JirrP: is_action L (@conjg_Iirr gT K); last pose Jirr := Action JirrP.
  split=> [y k1 k2 eq_k12 | k1 y1 y2 Gy1 Gy2]; apply/irr_inj.
    by apply/(can_inj (cfConjgK y)); rewrite -!conjg_IirrE eq_k12.
  by rewrite !conjg_IirrE (cfConjgM _ nsKL).
have [[_ nKL] [nKz _]] := (andP nsKL, setIdP Itheta_z).
suffices{k theta Itheta_z} /eqP->: imIchi == 'Fix_Jirr[z].
  by apply/afix1P/irr_inj; rewrite conjg_IirrE inertiaJ.
rewrite eqEcard; apply/andP; split.
  apply/subsetP=> _ /imsetP[j _ ->]; apply/afix1P/irr_inj. 
  by rewrite conjg_IirrE -(cfRes_prTIirr 0) (cfConjgRes _ _ nsKL) ?cfConjg_id.
have ->: #|imIchi| = w2 by rewrite card_imset //; apply: prTIres_inj.
have actsL_KK: [acts L, on classes K | 'Js \ subsetT L].
  rewrite astabs_ract subsetIidl; apply/subsetP=> y Ly; rewrite !inE /=.
  apply/subsetP=> _ /imsetP[x Kx ->]; rewrite !inE /= -class_rcoset.
  by rewrite norm_rlcoset ?class_lcoset ?mem_classes ?memJ_norm ?(subsetP nKL).
rewrite (card_afix_irr_classes Lz actsL_KK) => [|k x y Kx /=]; last first.
  by case/imsetP=> _ /imsetP[t Kt ->] ->; rewrite conjg_IirrE cfConjgEJ ?cfunJ.
apply: leq_trans (subset_leq_card _) (leq_imset_card (class^~ K) _).
apply/subsetP=> _ /setIP[/imsetP[x Kx ->] /afix1P/normP nxKz].
suffices{Kx} /pred0Pn[t /setIP[xKt czt]]: #|'C_(x ^: K)[z]| != 0%N.
  rewrite -(class_transr xKt); apply: mem_imset; have [y Ky Dt] := imsetP xKt.
  by rewrite -(@prKW1 z) ?(czt, inE) ?ntz // Dt groupJ.
have{coKp}: ~~ (p %| #|K|) by rewrite -prime_coprime // coprime_sym.
apply: contraNneq => /(congr1 (modn^~ p))/eqP; rewrite mod0n.
rewrite -cent_cycle -afixJ -sylow.pgroup_fix_mod ?astabsJ ?cycle_subG //.
by move/dvdn_trans; apply; rewrite -index_cent1 dvdn_indexg.
Qed.

(* Implicit elementary converse to the above. *)
Lemma prTIred_not_irr j : mu_ j \notin irr L.
Proof. by rewrite irrEchar cfnorm_prTIred pnatr_eq1 gtn_eqF ?andbF. Qed.

(* This is the second assertion of Peterfalvi (4.5)(b). *)
Theorem prTIind_irr_cases ell (phi := 'chi_ell) :
   {i : _ & {j | phi = mu2_ i j}}
     + {k | k \notin codom Ichi & phi = 'Ind 'chi_k}.
Proof.
have [k] := constt_cfRes_irr K ell; rewrite -constt_Ind_Res => kLell.
have [[j Dk] | [/irrP/sig_eqW[l1 DkL] chi'k]] := prTIres_irr_cases k.
  have [i /=/eqP <- | mu2j'l] := pickP (fun i => mu2_ i j == phi).
    by left; exists i, j.
  case/eqP: kLell; rewrite Dk cfInd_prTIres cfdot_suml big1 // => i _.
  by rewrite cfdot_irr -(inj_eq irr_inj) mu2j'l.
right; exists k; last by move: kLell; rewrite DkL constt_irr inE => /eqP <-.
apply/codomP=> [[j Dk]]; have/negP[] := prTIred_not_irr j.
by rewrite -cfInd_prTIres -Dk DkL mem_irr.
Qed.

End Four_3_to_5.

Notation primeTIsign ptiW j :=
  (GRing.sign algCring (primeTI_Isign ptiW j)) (only parsing).
Notation primeTIirr ptiW i j := 'chi_(primeTI_Iirr ptiW (i, j)) (only parsing).
Notation primeTIres ptiW j := 'chi_(primeTI_Ires ptiW j) (only parsing).

Implicit Arguments prTIirr_inj [gT L K W W1 W2 defW x1 x2].
Implicit Arguments prTIred_inj [gT L K W W1 W2 defW x1 x2].
Implicit Arguments prTIres_inj [gT L K W W1 W2 defW x1 x2].
Implicit Arguments not_prTIirr_vanish [gT L K W W1 W2 defW k].

Section Four_6_t0_10.

Variables (gT : finGroupType) (G L K H : {group gT}) (A A0 : {set gT}).
Variables (W W1 W2 : {group gT}) (defW : W1 \x W2 = W).

Local Notation V := (cyclicTIset defW).

(* These correspond to Peterfalvi, Hypothesis (4.6). *)
Definition prime_Dade_definition :=
  [/\ (*c*) [/\ H <| L, W2 \subset H & H \subset K],
      (*d*) [/\ A <| L, \bigcup_(h in H^#) 'C_K[h]^# \subset A & A \subset K^#]
    & (*e*) A0 = A :|: class_support V L].
 
Record prime_Dade_hypothesis : Prop := PrimeDadeHypothesis {
  prDade_cycTI :> cyclicTI_hypothesis G defW;
  prDade_prTI  :> primeTI_hypothesis L K defW;
  prDade_hyp   :> Dade_hypothesis G L A0;
  prDade_def   :> prime_Dade_definition
}.

Hypothesis prDadeHyp : prime_Dade_hypothesis.

Let ctiWG : cyclicTI_hypothesis G defW := prDadeHyp.
Let ptiWL : primeTI_hypothesis L K defW := prDadeHyp. 
Let ctiWL : cyclicTI_hypothesis L defW := prime_cycTIhyp ptiWL.
Let ddA0 : Dade_hypothesis G L A0 := prDadeHyp.
Local Notation ddA0def := (prDade_def prDadeHyp).

Local Notation w_ i j := (cyclicTIirr defW i j).
Local Notation sigma := (cyclicTIiso ctiWG).
Local Notation eta_ i j := (sigma (w_ i j)).
Local Notation mu2_ i j := (primeTIirr ptiWL i j).
Local Notation delta_ j := (primeTIsign ptiWL j).
Local Notation chi_ j := (primeTIres ptiWL j).
Local Notation mu_ := (primeTIred ptiWL).
Local Notation tau := (Dade ddA0).

Let defA0 : A0 = A :|: class_support V L. Proof. by have [] := ddA0def. Qed.
Let nsAL : A <| L. Proof. by have [_ []] := ddA0def. Qed.
Let sAA0 : A \subset A0. Proof. by rewrite defA0 subsetUl. Qed.

Let nsHL : H <| L. Proof. by have [[]] := ddA0def. Qed.
Let sHK : H \subset K. Proof. by have [[]] := ddA0def. Qed.
Let defL : K ><| W1 = L. Proof. by have [[]] := ptiWL. Qed.
Let sKL : K \subset L. Proof. by have /mulG_sub[] := sdprodW defL. Qed.
Let coKW1 : coprime #|K| #|W1|.
Proof. by rewrite (coprime_sdprod_Hall_r defL); have [[]] := ptiWL. Qed.

Let sIH_A : \bigcup_(h in H^#) 'C_K[h]^# \subset A.
Proof. by have [_ []] := ddA0def. Qed.

Let sW2H : W2 \subset H. Proof. by have [[]] := ddA0def. Qed.
Let ntW1 : W1 :!=: 1%g. Proof. by have [[]] := ptiWL. Qed.
Let ntW2 : W2 :!=: 1%g. Proof. by have [_ []] := ptiWL. Qed.

Let oddW : odd #|W|. Proof. by have [] := ctiWL. Qed.
Let sW1W : W1 \subset W. Proof. by have /mulG_sub[] := dprodW defW. Qed.
Let sW2W : W2 \subset W. Proof. by have /mulG_sub[] := dprodW defW. Qed.
Let tiW12 : W1 :&: W2 = 1%g. Proof. by have [] := dprodP defW. Qed.

Let cycW : cyclic W. Proof. by have [] := ctiWG. Qed.
Let cycW1 : cyclic W1. Proof. by have [[]] := ptiWL. Qed.
Let cycW2 : cyclic W2. Proof. by have [_ []] := ptiWL. Qed.
Let sLG : L \subset G. Proof. by case: ddA0. Qed.
Let sW2K : W2 \subset K. Proof. by have [_ []] := ptiWL. Qed.

Let sWL : W \subset L.
Proof. by rewrite -(dprodWC defW) -(sdprodW defL) mulgSS. Qed.
Let sWG : W \subset G. Proof. exact: subset_trans sWL sLG. Qed.

Let oddW1 : odd #|W1|. Proof. exact: oddSg oddW. Qed.
Let oddW2 : odd #|W2|. Proof. exact: oddSg oddW. Qed.

Let w1gt1 : (2 < #|W1|)%N. Proof. by rewrite odd_gt2 ?cardG_gt1. Qed.
Let w2gt2 : (2 < #|W2|)%N. Proof. by rewrite odd_gt2 ?cardG_gt1. Qed.

Let nirrW1 : #|Iirr W1| = #|W1|. Proof. exact: card_Iirr_cyclic. Qed.
Let nirrW2 : #|Iirr W2| = #|W2|. Proof. exact: card_Iirr_cyclic. Qed.
Let W1lin i : 'chi[W1]_i \is a linear_char. Proof. exact/irr_cyclic_lin. Qed.
Let W2lin i : 'chi[W2]_i \is a linear_char. Proof. exact/irr_cyclic_lin. Qed.
 
(* This is the first part of Peterfalvi (4.7). *) 
Lemma prDade_irr_on k : 
   ~~ (H \subset cfker 'chi[K]_k) -> 'chi_k \in 'CF(K, 1%g |: A).
Proof.
move=> kerH'i; apply/cfun_onP=> g; rewrite !inE => /norP[ntg A'g].
have [Kg | /cfun0-> //] := boolP (g \in K).
apply: not_in_ker_char0 (normalS _ _ nsHL) kerH'i _ => //.
apply/trivgP/subsetP=> h /setIP[Hh cgh]; apply: contraR A'g => nth.
apply/(subsetP sIH_A)/bigcupP; exists h; first exact/setDP.
by rewrite 3!inE ntg Kg cent1C.
Qed.

(* This is the second part of Peterfalvi (4.7). *) 
Lemma prDade_Ind_irr_on k : 
   ~~ (H \subset cfker 'chi[K]_k) -> 'Ind[L] 'chi_k \in 'CF(L, 1%g |: A).
Proof.
move/prDade_irr_on/(cfInd_on sKL); apply: cfun_onS; rewrite class_supportEr.
by apply/bigcupsP=> _ /normsP-> //; rewrite normsU ?norms1 ?normal_norm.
Qed.

(* Third part of Peterfalvi (4.7). *)
Lemma cfker_prTIres j : j != 0 ->  ~~ (H \subset cfker (chi_ j)).
Proof.
rewrite -(cfRes_prTIirr _ 0) cfker_Res ?irr_char // subsetI sHK /=.
apply: contra => kerHmu0j; rewrite -irr_eq1; apply/eqP/cfun_inP=> y W2y.
have [[x W1x ntx] mulW] := (trivgPn _ ntW1, dprodW defW).
rewrite cfun1E W2y -(cfDprodEr defW _ W1x W2y) -dprodr_IirrE -dprod_Iirr0l.
have{ntx} W2'x: x \notin W2 by rewrite -[x \in W2]andTb -W1x -in_setI tiW12 inE.
have V2xy: (x * y)%g \in W :\: W2 by rewrite inE -mulW mem_mulg ?groupMr ?W2'x.
rewrite -[w_ 0 j](signrZK (primeTI_Isign ptiWL j)) cfunE -prTIirr_id //.
have V2x: x \in W :\: W2 by rewrite inE W2'x (subsetP sW1W).
rewrite cfkerMr ?(subsetP (subset_trans sW2H kerHmu0j)) ?prTIirr_id // cfunE.
by rewrite signrMK -[x]mulg1 dprod_Iirr0l dprodr_IirrE cfDprodEr ?lin_char1.
Qed.

(* Fourth part of Peterfalvi (4.7). *)
Lemma prDade_TIres_on j : j != 0 -> chi_ j \in 'CF(K, 1%g |: A).
Proof. by move/cfker_prTIres/prDade_irr_on. Qed.

(* Last part of Peterfalvi (4.7). *)
Lemma prDade_TIred_on j : j != 0 -> mu_ j \in 'CF(L, 1%g |: A).
Proof. by move/cfker_prTIres/prDade_Ind_irr_on; rewrite cfInd_prTIres. Qed.

Import ssrint.

(* Second part of PeterFalvi (4.8). *)
Lemma prDade_TIsign_eq i j k : 
  mu2_ i j 1%g = mu2_ i k 1%g -> delta_ j = delta_ k.
Proof.
move=> eqjk; have{eqjk}: (delta_ j == delta_ k %[mod #|W1|])%C.
  apply: eqCmod_trans (prTIirr1_mod ptiWL i k).
  by rewrite eqCmod_sym -eqjk (prTIirr1_mod ptiWL).
have /negP: ~~ (#|W1| %| 2) by rewrite gtnNdvd.
rewrite /eqCmod -![delta_ _]intr_sign -rmorphB dvdC_int ?Cint_int //= intCK.
by do 2!case: (primeTI_Isign _ _).
Qed.

(* First part of PeterFalvi (4.8). *)
Lemma prDade_sub_TIirr_on i j k :
    j != 0 -> k != 0 -> mu2_ i j 1%g = mu2_ i k 1%g ->
  mu2_ i j - mu2_ i k \in 'CF(L, A0). 
Proof.
move=> nzj nzk eq_mu1.
apply/cfun_onP=> g; rewrite defA0 !inE negb_or !cfunE => /andP[A'g V'g].
have [Lg | L'g] := boolP (g \in L); last by rewrite !cfun0 ?subrr.
have{Lg} /bigcupP[_ /rcosetsP[x W1x ->] Kx_g]: g \in cover (rcosets K W1).
  by rewrite (cover_partition (rcosets_partition_mul W1 K)) (sdprodW defL).
have [x1 | ntx] := eqVneq x 1%g.
  have [-> | ntg] := eqVneq g 1%g; first by rewrite  eq_mu1 subrr.
  have{A'g} A1'g: g \notin 1%g |: A by rewrite !inE negb_or ntg.
  rewrite x1 mulg1 in Kx_g; rewrite -!(cfResE (mu2_ i _) sKL) ?cfRes_prTIirr //.
  by rewrite !(cfun_onP (prDade_TIres_on _)) ?subrr.
have coKx: coprime #|K| #[x] by rewrite (coprime_dvdr (order_dvdG W1x)).
have nKx: x \in 'N(K) by have [_ _ /subsetP->] := sdprodP defL.
have [/cover_partition defKx _] := partition_cent_rcoset nKx coKx.
have def_cKx: 'C_K[x] = W2 by have [_ _ -> //] := ptiWL; rewrite !inE ntx.
move: Kx_g; rewrite -defKx def_cKx cover_imset => /bigcupP[z /(subsetP sKL)Lz].
case/imsetP=> _ /rcosetP[y W2y ->] Dg; rewrite Dg !cfunJ //.
have V2yx: (y * x)%g \in W :\: W2.
  rewrite inE -(dprodWC defW) mem_mulg // andbT groupMl //.
  by rewrite -[x \in W2]andTb -W1x -in_setI tiW12 inE.
rewrite 2?{1}prTIirr_id //.
have /set1P->: y \in [1].
  rewrite -tiW12 inE W2y andbT; apply: contraR V'g => W1'y.
  by rewrite Dg mem_imset2 // !inE negb_or -andbA -in_setD groupMr ?W1'y.
rewrite -commute1 (prDade_TIsign_eq eq_mu1) !cfunE -mulrBr.
by rewrite !dprod_IirrE !cfDprodE // !lin_char1 // subrr mulr0.
Qed.

(* This is last part of PeterFalvi (4.8). *)
Lemma prDade_sub_TIirr i j k :
    j != 0 -> k != 0 -> mu2_ i j 1%g = mu2_ i k 1%g -> 
  tau (mu2_ i j - mu2_ i k) = delta_ j *: (eta_ i j - eta_ i k).
Proof.
move=> nz_j nz_k eq_mu2jk_1.
have [-> | k'j] := eqVneq j k; first by rewrite !subrr !raddf0.
have [[Itau Ztau] [_ Zsigma]] := (Dade_Zisometry ddA0, cycTI_Zisometry ctiWL).
set dmu2 := _ - _; set dsw := _ - _; have Dmu2 := prTIirr_id ptiWL.
have Zmu2: dmu2 \in 'Z[irr L, A0].
  by rewrite zchar_split rpredB ?irr_vchar ?prDade_sub_TIirr_on.
apply: eq_signed_sub_cTIiso => // [||x Vx].
- exact: zcharW (Ztau _ Zmu2).
- rewrite Itau // cfnormBd ?cfnorm_irr // (cfdot_prTIirr ptiWL).
  by rewrite (negPf k'j) andbF.
have V2x: x \in W :\: W2 by rewrite (subsetP _ x Vx) // setDS ?subsetUr.
rewrite !(cfunE, Dade_id) ?(cycTIiso_restrict _ _ Vx) //; last first.
  by rewrite defA0 inE orbC mem_class_support.
by rewrite !Dmu2 // (prDade_TIsign_eq eq_mu2jk_1) !cfunE -mulrBr.
Qed.

Lemma prDade_supp_disjoint : V \subset ~: K.
Proof.
rewrite subDset setUC -subDset setDE setCK setIC -(dprod_modr defW sW2K).
by rewrite coprime_TIg // dprod1g subsetUr.
Qed.

(* This is Peterfalvi (4.9).                                                  *)
(* We have added the "obvious" fact that calT is pairwise orthogonal, since   *)
(* we require this to prove membership in 'Z[calT], we encapsulate the        *)
(* construction of tau1, and state its conformance to tau on the "larger"     *)
(* domain 'Z[calT, L^#], so that clients can avoid using the domain equation  *)
(* in part (a).                                                               *)
Theorem uniform_prTIred_coherent k (calT := uniform_prTIred_seq ptiWL k) :
    k != 0 ->
  (*a*) [/\ pairwise_orthogonal calT, ~~ has cfReal calT, conjC_closed calT,
            'Z[calT, L^#] =i 'Z[calT, A]
          & exists2 psi, psi != 0 & psi \in 'Z[calT, A]]
  (*b*) /\ (exists2 tau1 : {linear 'CF(L) -> 'CF(G)},
           forall j, tau1 (mu_ j) = delta_ k *: (\sum_i sigma (w_ i j))
         & {in 'Z[calT], isometry tau1, to 'Z[irr G]}
        /\ {in 'Z[calT, L^#], tau1 =1 tau}).
Proof.
have uniqT: uniq calT by apply/dinjectiveP; apply: in2W; apply: prTIred_inj.
have sTmu: {subset calT <= codom mu_} by exact: image_codom.
have oo_mu: pairwise_orthogonal (codom mu_).
  apply/pairwise_orthogonalP; split=> [|_ _ /codomP[j1 ->] /codomP[j2 ->]].
    apply/andP; split; last by apply/injectiveP; apply: prTIred_inj.
    by apply/codomP=> [[i /esym/eqP/idPn[]]]; apply: prTIred_neq0.
  by rewrite cfdot_prTIred; case: (j1 =P j2) => // -> /eqP.
have real'T: ~~ has cfReal calT.
  by apply/hasPn=> _ /imageP[j /andP[nzj _] ->]; apply: prTIred_not_real.
have ccT: conjC_closed calT.
  move=> _ /imageP[j Tj ->]; rewrite -prTIred_aut image_f // inE aut_Iirr_eq0.
  by rewrite prTIred_aut cfunE conj_Cnat ?Cnat_char1 ?prTIred_char.
have TonA: 'Z[calT, L^#] =i 'Z[calT, A].
  have A'1: 1%g \notin A by apply: contra (subsetP sAA0 _) _; have [] := ddA0.
  move => psi; rewrite zcharD1E -(setU1K A'1) zcharD1; congr (_ && _).
  apply/idP/idP; [apply: zchar_trans_on psi => psi Tpsi | exact: zcharW].
  have [j /andP[nz_j _] Dpsi] := imageP Tpsi.
  by rewrite zchar_split mem_zchar // Dpsi prDade_TIred_on.
move=> nzk; split.
  split=> //; first exact: sub_pairwise_orthogonal oo_mu.
  have Tmuk: mu_ k \in calT by rewrite image_f // inE nzk /=.
  exists ((mu_ k)^*%CF - mu_ k); first by rewrite subr_eq0 (hasPn real'T).
  rewrite -TonA -rpredN opprB sub_aut_zchar ?zchar_onG ?mem_zchar ?ccT //.
  by move=> _ /mapP[j _ ->]; rewrite char_vchar ?prTIred_char.
pose f0 j := delta_ k *: (\sum_i eta_ i j); have in_mu := codom_f mu_.
pose f1 psi := f0 (iinv (valP (insigd (in_mu k) psi))).
have f1mu j: f1 (mu_ j) = f0 j.
  have in_muj := in_mu j.
  rewrite /f1 /insigd /insubd /= insubT /=; [idtac].
  by rewrite iinv_f //; apply: prTIred_inj.
have iso_f1: {in codom mu_, isometry f1, to 'Z[irr G]}.
  split=> [_ _ /codomP[j1 ->] /codomP[j2 ->] | _ /codomP[j ->]]; last first.
    by rewrite f1mu rpredZsign rpred_sum // => i _; apply: cycTIiso_vchar.
  rewrite !f1mu cfdotZl cfdotZr rmorph_sign signrMK !cfdot_suml.
  apply: eq_bigr => i1 _; rewrite !cfdot_sumr; apply: eq_bigr => i2 _.
  by rewrite cfdot_cycTIiso cfdot_prTIirr.
have [tau1 Dtau1 Itau1] := Zisometry_of_iso oo_mu iso_f1.
exists tau1 => [j|]; first by rewrite Dtau1 ?codom_f ?f1mu.
split=> [|psi]; first by apply: sub_iso_to Itau1 => //; apply: zchar_subset.
rewrite zcharD1E => /andP[/zchar_expansion[//|z _ Dpsi] /eqP psi1_0].
rewrite -[psi]subr0 -(scale0r (mu_ k)) -(mul0r (mu_ k 1%g)^-1) -{}psi1_0.
rewrite {psi}Dpsi sum_cfunE mulr_suml scaler_suml -sumrB !raddf_sum /=.
apply: eq_big_seq => _ /imageP[j /andP[nzj /eqP eq_mujk_1] ->].
rewrite cfunE eq_mujk_1 mulfK ?prTIred_1_neq0 // -scalerBr !linearZ /=.
congr (_ *: _); rewrite {z}linearB !Dtau1 ?codom_f // !f1mu -scalerBr -!sumrB.
rewrite !linear_sum; apply: eq_bigr => i _ /=.
have{eq_mujk_1} eq_mu2ijk_1: mu2_ i j 1%g = mu2_ i k 1%g.
  by apply: (mulfI (neq0CG W1)); rewrite !prTIirr_1 -!prTIred_1.
by rewrite -(prDade_TIsign_eq eq_mu2ijk_1) prDade_sub_TIirr.
Qed.

(* This is Peterfalvi (4.10). *)
Lemma prDade_sub2_TIirr i j :
  tau (delta_ j *: mu2_ i j - delta_ j *: mu2_ 0 j - mu2_ i 0 + mu2_ 0 0)
    = eta_ i j - eta_ 0 j - eta_ i 0 + eta_ 0 0.
Proof.
pose V0 := class_support V L; have sVV0: V \subset V0 := sub_class_support L V.
have sV0A0: V0 \subset A0 by rewrite defA0 subsetUr.
have nV0L: L \subset 'N(V0) := class_support_norm V L.
have [_ _ /normedTI_memJ_P[ntV _ tiV]] := ctiWG.
have [/andP[sA0L _] _ A0'1 _ _] := ddA0.
have{sA0L A0'1} sV0G: V0 \subset G^#.
  by rewrite (subset_trans sV0A0) // subsetD1 A0'1 (subset_trans sA0L).
have{sVV0} ntV0: V0 != set0 by apply: contraNneq ntV; rewrite -subset0 => <-.
have{ntV} tiV0: normedTI V0 G L.
  apply/normedTI_memJ_P; split=> // _ z /imset2P[u y Vu Ly ->] Gz.
  apply/idP/idP=> [/imset2P[u1 y1 Vu1 Ly1 Duyz] | Lz]; last first.
    by rewrite -conjgM mem_imset2 ?groupM.
  rewrite -[z](mulgKV y1) groupMr // -(groupMl _ Ly) (subsetP sWL) //.
  by rewrite -(tiV u) ?groupM ?groupV // ?(subsetP sLG) // !conjgM Duyz conjgK.
have{ntV0 sV0A0 nV0L tiV0} DtauV0: {in 'CF(L, V0), tau =1 'Ind}.
  by move=> beta V0beta; rewrite /= -(restr_DadeE _ sV0A0) //; apply: Dade_Ind.
pose alpha := cfCyclicTIset defW i j; set beta := _ *: mu2_ i j - _ - _ + _.
have Valpha: alpha \in 'CF(W, V) := cfCycTI_on ctiWL i j.
have Dalpha: alpha = w_ i j - w_ 0 j - w_ i 0 + w_ 0 0.
  by rewrite addrC {1}cycTIirr00 addrA addrAC addrA addrAC -cfCycTI_E.
rewrite -!(linearB sigma) -linearD -Dalpha cycTIiso_Ind //.
suffices ->: beta = 'Ind[L] alpha by rewrite DtauV0 ?cfInd_on ?cfIndInd.
rewrite Dalpha -addrA -[w_ 0 0]opprK -opprD linearB /= /beta -scalerBr.
by rewrite !(cfInd_sub_prTIirr ptiWL) prTIsign0 scale1r opprD opprK addrA.
Qed.
 
End Four_6_t0_10.

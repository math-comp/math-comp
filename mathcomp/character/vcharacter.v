(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrbool ssrfun eqtype ssrnat seq path div choice.
From mathcomp
Require Import fintype tuple finfun bigop prime ssralg poly finset.
From mathcomp
Require Import fingroup morphism perm automorphism quotient finalg action.
From mathcomp
Require Import gproduct zmodp commutator cyclic center pgroup sylow frobenius.
From mathcomp
Require Import vector ssrnum ssrint intdiv algC algnum.
From mathcomp
Require Import classfun character integral_char.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(******************************************************************************)
(* This file provides basic notions of virtual character theory:              *)
(*       'Z[S, A] == collective predicate for the phi that are Z-linear       *)
(*                   combinations of elements of S : seq 'CF(G) and have      *)
(*                   support in A : {set gT}.                                 *)
(*          'Z[S] == collective predicate for the Z-linear combinations of    *)
(*                   elements of S.                                           *)
(*      'Z[irr G] == the collective predicate for virtual characters.         *)
(*         dirr G == the collective predicate for normal virtual characters,  *)
(*                   i.e., virtual characters of norm 1:                      *)
(*               mu \in dirr G <=> m \in 'Z[irr G] and '[mu] = 1              *)
(*                             <=> mu or - mu \in irr G.                      *)
(* --> othonormal subsets of 'Z[irr G] are contained in dirr G.               *)
(*        dIirr G == an index type for normal virtual characters.             *)
(*         dchi i == the normal virtual character of index i.                 *)
(*       of_irr i == the (unique) irreducible constituent of dchi i:          *)
(*                   dchi i = 'chi_(of_irr i) or - 'chi_(of_irr i).           *)
(*        ndirr i == the index of - dchi i.                                   *)
(*        dirr1 G == the normal virtual character index of 1 : 'CF(G), the    *)
(*                   principal character.                                     *)
(* dirr_dIirr j f == the index i (or dirr1 G if it does not exist) such that  *)
(*                   dchi i = f j.                                            *)
(* dirr_constt phi == the normal virtual character constituents of phi:       *)
(*                    i \in dirr_constt phi <=> [dchi i, phi] > 0.            *)
(*  to_dirr phi i == the normal virtual character constituent of phi with an  *)
(*                   irreducible constituent i, when i \in irr_constt phi.    *)
(******************************************************************************)

Section Basics.

Variables (gT : finGroupType) (B : {set gT}) (S : seq 'CF(B)) (A : {set gT}).

Definition Zchar : pred_class :=
  [pred phi in 'CF(B, A) | dec_Cint_span (in_tuple S) phi].
Fact Zchar_key : pred_key Zchar. Proof. by []. Qed.
Canonical Zchar_keyed := KeyedPred Zchar_key.

Lemma cfun0_zchar : 0 \in Zchar.
Proof.
rewrite inE mem0v; apply/sumboolP; exists 0.
by rewrite big1 // => i _; rewrite ffunE.
Qed.

Fact Zchar_zmod : zmod_closed Zchar.
Proof.
split; first exact: cfun0_zchar.
move=> phi xi /andP[Aphi /sumboolP[a Da]] /andP[Axi /sumboolP[b Db]].
rewrite inE rpredB // Da Db -sumrB; apply/sumboolP; exists (a - b).
by apply: eq_bigr => i _; rewrite -mulrzBr !ffunE.
Qed.
Canonical Zchar_opprPred := OpprPred Zchar_zmod.
Canonical Zchar_addrPred := AddrPred Zchar_zmod.
Canonical Zchar_zmodPred := ZmodPred Zchar_zmod.

Lemma scale_zchar a phi : a \in Cint -> phi \in Zchar -> a *: phi \in Zchar.
Proof. by case/CintP=> m -> Zphi; rewrite scaler_int rpredMz. Qed.

End Basics.

Notation "''Z[' S , A ]" := (Zchar S A)
  (at level 8, format "''Z[' S ,  A ]") : group_scope. 
Notation "''Z[' S ]" := 'Z[S, setT]
  (at level 8, format "''Z[' S ]") : group_scope.

Section Zchar.

Variables (gT : finGroupType) (G : {group gT}).
Implicit Types (A B : {set gT}) (S : seq 'CF(G)).

Lemma zchar_split S A phi :
  phi \in 'Z[S, A] = (phi \in 'Z[S]) && (phi \in 'CF(G, A)).
Proof. by rewrite !inE cfun_onT andbC. Qed.

Lemma zcharD1E phi S : (phi \in 'Z[S, G^#]) = (phi \in 'Z[S]) && (phi 1%g == 0).
Proof. by rewrite zchar_split cfunD1E. Qed.

Lemma zcharD1 phi S A :
  (phi \in 'Z[S, A^#]) = (phi \in 'Z[S, A]) && (phi 1%g == 0).
Proof. by rewrite zchar_split cfun_onD1 andbA -zchar_split. Qed.

Lemma zcharW S A : {subset 'Z[S, A] <= 'Z[S]}.
Proof. by move=> phi; rewrite zchar_split => /andP[]. Qed.

Lemma zchar_on S A : {subset 'Z[S, A] <= 'CF(G, A)}.
Proof. by move=> phi /andP[]. Qed.

Lemma zchar_onS A B S : A \subset B -> {subset 'Z[S, A] <= 'Z[S, B]}.
Proof.
move=> sAB phi; rewrite zchar_split (zchar_split _ B) => /andP[->].
exact: cfun_onS.
Qed.

Lemma zchar_onG S : 'Z[S, G] =i 'Z[S].
Proof. by move=> phi; rewrite zchar_split cfun_onG andbT. Qed.

Lemma irr_vchar_on A : {subset 'Z[irr G, A] <= 'CF(G, A)}.
Proof. exact: zchar_on. Qed.

Lemma support_zchar S A phi : phi \in 'Z[S, A] -> support phi \subset A.
Proof. by move/zchar_on; rewrite cfun_onE. Qed.

Lemma mem_zchar_on S A phi : 
  phi \in 'CF(G, A) -> phi \in S -> phi \in 'Z[S, A].
Proof.
move=> Aphi /(@tnthP _ _ (in_tuple S))[i Dphi]; rewrite inE /= {}Aphi {phi}Dphi.
apply/sumboolP; exists [ffun j => (j == i)%:Z].
rewrite (bigD1 i) //= ffunE eqxx (tnth_nth 0) big1 ?addr0 // => j i'j.
by rewrite ffunE (negPf i'j).
Qed.

(* A special lemma is needed because trivial fails to use the cfun_onT Hint. *) 
Lemma mem_zchar S phi : phi \in S -> phi \in 'Z[S].
Proof. by move=> Sphi; rewrite mem_zchar_on ?cfun_onT. Qed.

Lemma zchar_nth_expansion S A phi :
    phi \in 'Z[S, A] ->
  {z | forall i, z i \in Cint & phi = \sum_(i < size S) z i *: S`_i}.
Proof.
case/andP=> _ /sumboolP/sig_eqW[/= z ->].
exists (intr \o z) => [i|]; first exact: Cint_int.
by apply: eq_bigr => i _; rewrite scaler_int.
Qed.

Lemma zchar_tuple_expansion n (S : n.-tuple 'CF(G)) A phi :
    phi \in 'Z[S, A] ->
  {z | forall i, z i \in Cint & phi = \sum_(i < n) z i *: S`_i}.
Proof. by move/zchar_nth_expansion; rewrite size_tuple. Qed.

(* A pure seq version with the extra hypothesis of S's unicity.  *)
Lemma zchar_expansion S A phi : uniq S -> 
    phi \in 'Z[S, A] ->
  {z | forall xi, z xi \in Cint & phi = \sum_(xi <- S) z xi *: xi}.
Proof.
move=> Suniq /zchar_nth_expansion[z Zz ->] /=.
pose zS xi := oapp z 0 (insub (index xi S)).
exists zS => [xi | ]; rewrite {}/zS; first by case: (insub _).
rewrite (big_nth 0) big_mkord; apply: eq_bigr => i _; congr (_ *: _).
by rewrite index_uniq // valK.
Qed.

Lemma zchar_span S A : {subset 'Z[S, A] <= <<S>>%VS}.
Proof.
move=> _ /zchar_nth_expansion[z Zz ->] /=.
by apply: rpred_sum => i _; rewrite rpredZ // memv_span ?mem_nth.
Qed.

Lemma zchar_trans S1 S2 A B :
  {subset S1 <= 'Z[S2, B]} -> {subset 'Z[S1, A] <= 'Z[S2, A]}.
Proof.
move=> sS12 phi; rewrite !(zchar_split _ A) andbC => /andP[->]; rewrite andbT.
case/zchar_nth_expansion=> z Zz ->; apply: rpred_sum => i _.
by rewrite scale_zchar // (@zcharW _ B) ?sS12 ?mem_nth.
Qed.

Lemma zchar_trans_on S1 S2 A :
  {subset S1 <= 'Z[S2, A]} -> {subset 'Z[S1] <= 'Z[S2, A]}.
Proof.
move=> sS12 _ /zchar_nth_expansion[z Zz ->]; apply: rpred_sum => i _.
by rewrite scale_zchar // sS12 ?mem_nth.
Qed.

Lemma zchar_sub_irr S A :
  {subset S <= 'Z[irr G]} -> {subset 'Z[S, A] <= 'Z[irr G, A]}.
Proof. exact: zchar_trans. Qed.

Lemma zchar_subset S1 S2 A :
  {subset S1 <= S2} -> {subset 'Z[S1, A] <= 'Z[S2, A]}.
Proof.
move=> sS12; apply: zchar_trans setT _ => // f /sS12 S2f.
by rewrite mem_zchar.
Qed.

Lemma zchar_subseq S1 S2 A :
  subseq S1 S2 -> {subset 'Z[S1, A] <= 'Z[S2, A]}.
Proof. by move/mem_subseq; apply: zchar_subset. Qed.

Lemma zchar_filter S A (p : pred 'CF(G)) :
  {subset 'Z[filter p S, A] <= 'Z[S, A]}.
Proof. by apply: zchar_subset=> f; apply/mem_subseq/filter_subseq. Qed.

End Zchar.

Section VChar.

Variables (gT : finGroupType) (G : {group gT}).
Implicit Types (A B : {set gT}) (phi chi : 'CF(G)) (S : seq 'CF(G)).

Lemma char_vchar chi : chi \is a character -> chi \in 'Z[irr G].
Proof.
case/char_sum_irr=> r ->; apply: rpred_sum => i _.
by rewrite mem_zchar ?mem_tnth.
Qed.

Lemma irr_vchar i : 'chi[G]_i \in 'Z[irr G].
Proof. exact/char_vchar/irr_char. Qed.

Lemma cfun1_vchar : 1 \in 'Z[irr G]. Proof. by rewrite -irr0 irr_vchar. Qed.

Lemma vcharP phi :
  reflect (exists2 chi1, chi1 \is a character
            & exists2 chi2, chi2 \is a character & phi = chi1 - chi2)
          (phi \in 'Z[irr G]).
Proof.
apply: (iffP idP) => [| [a Na [b Nb ->]]]; last by rewrite rpredB ?char_vchar.
case/zchar_tuple_expansion=> z Zz ->; rewrite (bigID (fun i => 0 <= z i)) /=.
set chi1 := \sum_(i | _) _; set nchi2 := \sum_(i | _) _.
exists chi1; last exists (- nchi2); last by rewrite opprK.
  apply: rpred_sum => i zi_ge0; rewrite -tnth_nth rpredZ_Cnat ?irr_char //.
  by rewrite CnatEint Zz.
rewrite -sumrN rpred_sum // => i zi_lt0; rewrite -scaleNr -tnth_nth.
rewrite rpredZ_Cnat ?irr_char // CnatEint rpredN Zz oppr_ge0 ltrW //.
by rewrite real_ltrNge ?Creal_Cint.
Qed.

Lemma Aint_vchar phi x : phi \in 'Z[irr G] -> phi x \in Aint.
Proof.
case/vcharP=> [chi1 Nchi1 [chi2 Nchi2 ->]].
by rewrite !cfunE rpredB ?Aint_char.
Qed.

Lemma Cint_vchar1 phi : phi \in 'Z[irr G] -> phi 1%g \in Cint.
Proof.
case/vcharP=> phi1 Nphi1 [phi2 Nphi2 ->].
by rewrite !cfunE rpredB // rpred_Cnat ?Cnat_char1.
Qed.

Lemma Cint_cfdot_vchar_irr i phi : phi \in 'Z[irr G] -> '[phi, 'chi_i] \in Cint.
Proof.
case/vcharP=> chi1 Nchi1 [chi2 Nchi2 ->].
by rewrite cfdotBl rpredB // rpred_Cnat ?Cnat_cfdot_char_irr.
Qed.

Lemma cfdot_vchar_r phi psi :
  psi \in 'Z[irr G] -> '[phi, psi] = \sum_i '[phi, 'chi_i] * '[psi, 'chi_i].
Proof.
move=> Zpsi; rewrite cfdot_sum_irr; apply: eq_bigr => i _; congr (_ * _).
by rewrite aut_Cint ?Cint_cfdot_vchar_irr.
Qed.

Lemma Cint_cfdot_vchar : {in 'Z[irr G] &, forall phi psi, '[phi, psi] \in Cint}.
Proof.
move=> phi psi Zphi Zpsi; rewrite /= cfdot_vchar_r // rpred_sum // => k _.
by rewrite rpredM ?Cint_cfdot_vchar_irr.
Qed.

Lemma Cnat_cfnorm_vchar : {in 'Z[irr G], forall phi, '[phi] \in Cnat}.
Proof.
by move=> phi Zphi; rewrite /= CnatEint cfnorm_ge0 Cint_cfdot_vchar.
Qed.

Fact vchar_mulr_closed : mulr_closed 'Z[irr G].
Proof.
split; first exact: cfun1_vchar.
move=> _ _ /vcharP[xi1 Nxi1 [xi2 Nxi2 ->]] /vcharP[xi3 Nxi3 [xi4 Nxi4 ->]].
by rewrite mulrBl !mulrBr !(rpredB, rpredD) // char_vchar ?rpredM.
Qed.
Canonical vchar_mulrPred := MulrPred vchar_mulr_closed.
Canonical vchar_smulrPred := SmulrPred vchar_mulr_closed.
Canonical vchar_semiringPred := SemiringPred vchar_mulr_closed.
Canonical vchar_subringPred := SubringPred vchar_mulr_closed.

Lemma mul_vchar A :
  {in 'Z[irr G, A] &, forall phi psi, phi * psi \in 'Z[irr G, A]}.
Proof.
move=> phi psi; rewrite zchar_split => /andP[Zphi Aphi] /zcharW Zpsi.
rewrite zchar_split rpredM //; apply/cfun_onP=> x A'x.
by rewrite cfunE (cfun_onP Aphi) ?mul0r.
Qed.

Section CfdotPairwiseOrthogonal.

Variables (M : {group gT}) (S : seq 'CF(G)) (nu : 'CF(G) -> 'CF(M)).
Hypotheses (Inu : {in 'Z[S] &, isometry nu}) (oSS : pairwise_orthogonal S).

Let freeS := orthogonal_free oSS.
Let uniqS : uniq S := free_uniq freeS.
Let Z_S : {subset S <= 'Z[S]}. Proof. by move=> phi; apply: mem_zchar. Qed.
Let notS0 : 0 \notin S. Proof. by case/andP: oSS. Qed.
Let dotSS := proj2 (pairwise_orthogonalP oSS).

Lemma map_pairwise_orthogonal : pairwise_orthogonal (map nu S).
Proof.
have inj_nu: {in S &, injective nu}.
  move=> phi psi Sphi Spsi /= eq_nu; apply: contraNeq (memPn notS0 _ Sphi).
  by rewrite -cfnorm_eq0 -Inu ?Z_S // {2}eq_nu Inu ?Z_S // => /dotSS->.
have notSnu0: 0 \notin map nu S.
  apply: contra notS0 => /mapP[phi Sphi /esym/eqP].
  by rewrite -cfnorm_eq0 Inu ?Z_S // cfnorm_eq0 => /eqP <-.
apply/pairwise_orthogonalP; split; first by rewrite /= notSnu0 map_inj_in_uniq.
move=> _ _ /mapP[phi Sphi ->] /mapP[psi Spsi ->].
by rewrite (inj_in_eq inj_nu) // Inu ?Z_S //; apply: dotSS.
Qed.

Lemma cfproj_sum_orthogonal P z phi :
    phi \in S ->
  '[\sum_(xi <- S | P xi) z xi *: nu xi, nu phi]
    = if P phi then z phi * '[phi] else 0.
Proof.
move=> Sphi; have defS := perm_to_rem Sphi.
rewrite cfdot_suml (eq_big_perm _ defS) big_cons /= cfdotZl Inu ?Z_S //.
rewrite big1_seq ?addr0 // => xi; rewrite mem_rem_uniq ?inE //.
by case/and3P=> _ neq_xi Sxi; rewrite cfdotZl Inu ?Z_S // dotSS ?mulr0.
Qed.

Lemma cfdot_sum_orthogonal z1 z2 :
  '[\sum_(xi <- S) z1 xi *: nu xi, \sum_(xi <- S) z2 xi *: nu xi]
    = \sum_(xi <- S) z1 xi * (z2 xi)^* * '[xi].
Proof.
rewrite cfdot_sumr; apply: eq_big_seq => phi Sphi.
by rewrite cfdotZr cfproj_sum_orthogonal // mulrCA mulrA.
Qed.

Lemma cfnorm_sum_orthogonal z :
  '[\sum_(xi <- S) z xi *: nu xi] = \sum_(xi <- S) `|z xi| ^+ 2 * '[xi].
Proof.
by rewrite cfdot_sum_orthogonal; apply: eq_bigr => xi _; rewrite normCK.
Qed.

Lemma cfnorm_orthogonal : '[\sum_(xi <- S) nu xi] = \sum_(xi <- S) '[xi].
Proof.
rewrite -(eq_bigr _ (fun _ _ => scale1r _)) cfnorm_sum_orthogonal.
by apply: eq_bigr => xi; rewrite normCK conjC1 !mul1r.
Qed.

End CfdotPairwiseOrthogonal.

Lemma orthogonal_span S phi :
    pairwise_orthogonal S -> phi \in <<S>>%VS ->
  {z | z = fun xi => '[phi, xi] / '[xi] & phi = \sum_(xi <- S) z xi *: xi}.
Proof.
move=> oSS /free_span[|c -> _]; first exact: orthogonal_free.
set z := fun _ => _ : algC; exists z => //; apply: eq_big_seq => u Su.
rewrite /z cfproj_sum_orthogonal // mulfK // cfnorm_eq0.
by rewrite (memPn _ u Su); case/andP: oSS.
Qed.

Section CfDotOrthonormal.

Variables (M : {group gT}) (S : seq 'CF(G)) (nu : 'CF(G) -> 'CF(M)).
Hypotheses (Inu : {in 'Z[S] &, isometry nu}) (onS : orthonormal S).
Let oSS := orthonormal_orthogonal onS.
Let freeS := orthogonal_free oSS.
Let nS1 : {in S, forall phi, '[phi] = 1}.
Proof. by move=> phi Sphi; case/orthonormalP: onS => _ -> //; rewrite eqxx. Qed.

Lemma map_orthonormal : orthonormal (map nu S).
Proof.
rewrite !orthonormalE map_pairwise_orthogonal // andbT.
by apply/allP=> _ /mapP[xi Sxi ->]; rewrite /= Inu ?nS1 // mem_zchar.
Qed.

Lemma cfproj_sum_orthonormal z phi :
  phi \in S -> '[\sum_(xi <- S) z xi *: nu xi, nu phi] = z phi.
Proof. by move=> Sphi; rewrite cfproj_sum_orthogonal // nS1 // mulr1. Qed.

Lemma cfdot_sum_orthonormal z1 z2 :
  '[\sum_(xi <- S) z1 xi *: xi, \sum_(xi <- S) z2 xi *: xi]
     = \sum_(xi <- S) z1 xi * (z2 xi)^*.
Proof.
rewrite cfdot_sum_orthogonal //; apply: eq_big_seq => phi /nS1->.
by rewrite mulr1.
Qed.

Lemma cfnorm_sum_orthonormal z :
  '[\sum_(xi <- S) z xi *: nu xi] = \sum_(xi <- S) `|z xi| ^+ 2.
Proof.
rewrite cfnorm_sum_orthogonal //.
by apply: eq_big_seq => xi /nS1->; rewrite mulr1.
Qed.

Lemma cfnorm_map_orthonormal : '[\sum_(xi <- S) nu xi] = (size S)%:R.
Proof.
by rewrite cfnorm_orthogonal // (eq_big_seq _ nS1) big_tnth sumr_const card_ord.
Qed.

Lemma orthonormal_span phi :
    phi \in <<S>>%VS ->
  {z | z = fun xi => '[phi, xi] & phi = \sum_(xi <- S) z xi *: xi}.
Proof.
case/orthogonal_span=> // _ -> {2}->; set z := fun _ => _ : algC.
by exists z => //; apply: eq_big_seq => xi /nS1->; rewrite divr1.
Qed.

End CfDotOrthonormal.

Lemma cfnorm_orthonormal S :
  orthonormal S -> '[\sum_(xi <- S) xi] = (size S)%:R.
Proof. exact: cfnorm_map_orthonormal. Qed.

Lemma vchar_orthonormalP S :
    {subset S <= 'Z[irr G]} ->
  reflect (exists I : {set Iirr G}, exists b : Iirr G -> bool,
           perm_eq S [seq (-1) ^+ b i *: 'chi_i | i in I])
          (orthonormal S).
Proof.
move=> vcS; apply: (equivP orthonormalP).
split=> [[uniqS oSS] | [I [b defS]]]; last first.
  split=> [|xi1 xi2]; rewrite ?(perm_eq_mem defS).
    rewrite (perm_eq_uniq defS) map_inj_uniq ?enum_uniq // => i j /eqP.
    by rewrite eq_signed_irr => /andP[_ /eqP].
  case/mapP=> [i _ ->] /mapP[j _ ->]; rewrite eq_signed_irr.
  rewrite cfdotZl cfdotZr rmorph_sign mulrA cfdot_irr -signr_addb mulr_natr.
  by rewrite mulrb andbC; case: eqP => //= ->; rewrite addbb eqxx.
pose I := [set i | ('chi_i \in S) || (- 'chi_i \in S)].
pose b i := - 'chi_i \in S; exists I, b.
apply: uniq_perm_eq => // [|xi].
  rewrite map_inj_uniq ?enum_uniq // => i j /eqP.
  by rewrite eq_signed_irr => /andP[_ /eqP].
apply/idP/mapP=> [Sxi | [i Ii ->{xi}]]; last first.
  move: Ii; rewrite mem_enum inE orbC -/(b i).
  by case b_i: (b i); rewrite (scale1r, scaleN1r).
have: '[xi] = 1 by rewrite oSS ?eqxx.
have vc_xi := vcS _ Sxi; rewrite cfdot_sum_irr.
case/Cnat_sum_eq1 => [i _ | i [_ /eqP norm_xi_i xi_i'_0]].
  by rewrite -normCK rpredX // Cnat_norm_Cint ?Cint_cfdot_vchar_irr.
suffices def_xi: xi = (-1) ^+ b i *: 'chi_i.
  exists i; rewrite // mem_enum inE -/(b i) orbC.
  by case: (b i) def_xi Sxi => // ->; rewrite scale1r.
move: Sxi; rewrite [xi]cfun_sum_cfdot (bigD1 i) //.
rewrite big1 //= ?addr0 => [|j ne_ji]; last first.
  apply/eqP; rewrite scaler_eq0 -normr_eq0 -[_ == 0](expf_eq0 _ 2) normCK.
  by rewrite xi_i'_0 ?eqxx.
have:= norm_xi_i; rewrite (aut_Cint _ (Cint_cfdot_vchar_irr _ _)) //.
rewrite -subr_eq0 subr_sqr_1 mulf_eq0 subr_eq0 addr_eq0 /b scaler_sign.
case/pred2P=> ->; last by rewrite scaleN1r => ->.
rewrite scale1r => Sxi; case: ifP => // SNxi.
have:= oSS _ _ Sxi SNxi; rewrite cfdotNr cfdot_irr eqxx; case: eqP => // _.
by move/eqP; rewrite oppr_eq0 oner_eq0.
Qed.

Lemma vchar_norm1P phi :
    phi \in 'Z[irr G] -> '[phi] = 1 ->
  exists b : bool, exists i : Iirr G, phi = (-1) ^+ b *: 'chi_i.
Proof.
move=> Zphi phiN1.
have: orthonormal phi by rewrite /orthonormal/= phiN1 eqxx.
case/vchar_orthonormalP=> [xi /predU1P[->|] // | I [b def_phi]].
have: phi \in (phi : seq _) := mem_head _ _.
by rewrite (perm_eq_mem def_phi) => /mapP[i _ ->]; exists (b i), i.
Qed.

Lemma zchar_small_norm phi n :
    phi \in 'Z[irr G] -> '[phi] = n%:R -> (n < 4)%N ->
  {S : n.-tuple 'CF(G) |
    [/\ orthonormal S, {subset S <= 'Z[irr G]} & phi = \sum_(xi <- S) xi]}.
Proof.
move=> Zphi def_n lt_n_4.
pose S := [seq '[phi, 'chi_i] *: 'chi_i | i in irr_constt phi].
have def_phi: phi = \sum_(xi <- S) xi.
  rewrite big_map /= big_filter big_mkcond {1}[phi]cfun_sum_cfdot.
  by apply: eq_bigr => i _; rewrite if_neg; case: eqP => // ->; rewrite scale0r.
have orthS: orthonormal S.
  apply/orthonormalP; split=> [|_ _ /mapP[i phi_i ->] /mapP[j _ ->]].
    rewrite map_inj_in_uniq ?enum_uniq // => i j; rewrite mem_enum => phi_i _.
    by move/eqP; rewrite eq_scaled_irr (negbTE phi_i) => /andP[_ /= /eqP].
  rewrite eq_scaled_irr cfdotZl cfdotZr cfdot_irr mulrA mulr_natr mulrb.
  rewrite mem_enum in phi_i; rewrite (negbTE phi_i) andbC; case: eqP => // <-.
  have /CnatP[m def_m] := Cnat_norm_Cint (Cint_cfdot_vchar_irr i Zphi).
  apply/eqP; rewrite eqxx /= -normCK def_m -natrX eqr_nat eqn_leq lt0n.
  rewrite expn_eq0 andbT -eqC_nat -def_m normr_eq0 [~~ _]phi_i andbT.
  rewrite (leq_exp2r _ 1) // -ltnS -(@ltn_exp2r _ _ 2) //.
  apply: leq_ltn_trans lt_n_4; rewrite -leC_nat -def_n natrX.
  rewrite cfdot_sum_irr (bigD1 i) //= -normCK def_m addrC -subr_ge0 addrK.
  by rewrite sumr_ge0 // => ? _; apply: mul_conjC_ge0.
have <-: size S = n.
  by apply/eqP; rewrite -eqC_nat -def_n def_phi cfnorm_orthonormal.
exists (in_tuple S); split=> // _ /mapP[i _ ->].
by rewrite scale_zchar ?irr_vchar // Cint_cfdot_vchar_irr.
Qed.

Lemma vchar_norm2 phi :
    phi \in 'Z[irr G, G^#] -> '[phi] = 2%:R ->
  exists i, exists2 j, j != i & phi = 'chi_i - 'chi_j.
Proof.
rewrite zchar_split cfunD1E => /andP[Zphi phi1_0].
case/zchar_small_norm => // [[[|chi [|xi [|?]]] //= S2]].
case=> /andP[/and3P[Nchi Nxi _] /= ochi] /allP/and3P[Zchi Zxi _].
rewrite big_cons big_seq1 => def_phi.
have [b [i def_chi]] := vchar_norm1P Zchi (eqP Nchi).
have [c [j def_xi]] := vchar_norm1P Zxi (eqP Nxi).
have neq_ji: j != i.
  apply: contraTneq ochi; rewrite !andbT def_chi def_xi => ->.
  rewrite cfdotZl cfdotZr rmorph_sign cfnorm_irr mulr1 -signr_addb.
  by rewrite signr_eq0.
have neq_bc: b != c.
  apply: contraTneq phi1_0; rewrite def_phi def_chi def_xi => ->.
  rewrite -scalerDr !cfunE mulf_eq0 signr_eq0 eqr_le ltr_geF //.
  by rewrite ltr_paddl ?ltrW ?irr1_gt0.
rewrite {}def_phi {}def_chi {}def_xi !scaler_sign.
case: b c neq_bc => [|] [|] // _; last by exists i, j.
by exists j, i; rewrite 1?eq_sym // addrC.
Qed.

End VChar.

Section Isometries.

Variables (gT : finGroupType) (L G : {group gT}) (S : seq 'CF(L)).
Implicit Type nu : {additive 'CF(L) -> 'CF(G)}.

Lemma Zisometry_of_cfnorm (tauS : seq 'CF(G)) :
    pairwise_orthogonal S -> pairwise_orthogonal tauS ->
    map cfnorm tauS = map cfnorm S -> {subset tauS <= 'Z[irr G]} ->
  {tau : {linear 'CF(L) -> 'CF(G)} | map tau S = tauS
       & {in 'Z[S], isometry tau, to 'Z[irr G]}}.
Proof.
move=> oSS oTT /isometry_of_cfnorm[||tau defT Itau] // Z_T; exists tau => //.
split=> [|_ /zchar_nth_expansion[u Zu ->]].
  by apply: sub_in2 Itau; apply: zchar_span.
rewrite big_seq linear_sum rpred_sum // => xi Sxi.
by rewrite linearZ scale_zchar ?Z_T // -defT map_f ?mem_nth.
Qed.

Lemma Zisometry_of_iso f :
    free S -> {in S, isometry f, to 'Z[irr G]} ->
  {tau : {linear 'CF(L) -> 'CF(G)} | {in S, tau =1 f}
       & {in 'Z[S], isometry tau, to 'Z[irr G]}}.
Proof.
move=> freeS [If Zf]; have [tau Dtau Itau] := isometry_of_free freeS If.
exists tau => //; split; first by apply: sub_in2 Itau; apply: zchar_span.
move=> _ /zchar_nth_expansion[a Za ->]; rewrite linear_sum rpred_sum // => i _.
by rewrite linearZ rpredZ_Cint ?Dtau ?Zf ?mem_nth.
Qed.

Lemma Zisometry_inj A nu :
  {in 'Z[S, A] &, isometry nu} -> {in 'Z[S, A] &, injective nu}.
Proof. by move/isometry_raddf_inj; apply; apply: rpredB. Qed.

Lemma isometry_in_zchar nu : {in S &, isometry nu} -> {in 'Z[S] &, isometry nu}.
Proof.
move=> Inu _ _ /zchar_nth_expansion[u Zu ->] /zchar_nth_expansion[v Zv ->].
rewrite !raddf_sum; apply: eq_bigr => j _ /=.
rewrite !cfdot_suml; apply: eq_bigr => i _.
by rewrite !raddfZ_Cint //= !cfdotZl !cfdotZr Inu ?mem_nth.
Qed.

End Isometries.

Section AutVchar.

Variables (u : {rmorphism algC -> algC}) (gT : finGroupType) (G : {group gT}).
Local Notation "alpha ^u" := (cfAut u alpha).
Implicit Type (S : seq 'CF(G)) (phi chi : 'CF(G)).

Lemma cfAut_zchar S A psi : 
  cfAut_closed u S -> psi \in 'Z[S, A] -> psi^u \in 'Z[S, A].
Proof.
rewrite zchar_split => SuS /andP[/zchar_nth_expansion[z Zz Dpsi] Apsi].
rewrite zchar_split cfAut_on {}Apsi {psi}Dpsi rmorph_sum rpred_sum //= => i _.
by rewrite cfAutZ_Cint // scale_zchar // mem_zchar ?SuS ?mem_nth.
Qed.

Lemma cfAut_vchar A psi : psi \in 'Z[irr G, A] -> psi^u \in 'Z[irr G, A].
Proof. by apply: cfAut_zchar; apply: irr_aut_closed. Qed.

Lemma sub_aut_zchar S A psi :
   {subset S <= 'Z[irr G]} -> psi \in 'Z[S, A] -> psi^u \in 'Z[S, A] ->
  psi - psi^u \in 'Z[S, A^#].
Proof.
move=> Z_S Spsi Spsi_u; rewrite zcharD1 !cfunE subr_eq0 rpredB //=.
by rewrite aut_Cint // Cint_vchar1 // (zchar_trans Z_S) ?(zcharW Spsi).
Qed.

Lemma conjC_vcharAut chi x : chi \in 'Z[irr G] -> (u (chi x))^* = u (chi x)^*.
Proof.
case/vcharP=> chi1 Nchi1 [chi2 Nchi2 ->].
by rewrite !cfunE !rmorphB !conjC_charAut.
Qed.

Lemma cfdot_aut_vchar phi chi :
  chi \in 'Z[irr G] -> '[phi^u , chi^u] = u '[phi, chi].
Proof.
case/vcharP=> chi1 Nchi1 [chi2 Nchi2 ->].
by rewrite !raddfB /= !cfdot_aut_char.
Qed.

Lemma vchar_aut A chi : (chi^u \in 'Z[irr G, A]) = (chi \in 'Z[irr G, A]).
Proof.
rewrite !(zchar_split _ A) cfAut_on; congr (_ && _).
apply/idP/idP=> [Zuchi|]; last exact: cfAut_vchar.
rewrite [chi]cfun_sum_cfdot rpred_sum // => i _.
rewrite scale_zchar ?irr_vchar //.
by rewrite -(Cint_aut u) -cfdot_aut_irr -aut_IirrE Cint_cfdot_vchar_irr.
Qed.

End AutVchar.

Definition cfConjC_vchar :=  cfAut_vchar conjC.

Section MoreVchar.

Variables (gT : finGroupType) (G H : {group gT}).

Lemma cfRes_vchar phi : phi \in 'Z[irr G] -> 'Res[H] phi \in 'Z[irr H].
Proof.
case/vcharP=> xi1 Nx1 [xi2 Nxi2 ->].
by rewrite raddfB rpredB ?char_vchar ?cfRes_char.
Qed.

Lemma cfRes_vchar_on A phi :
  H \subset G -> phi \in 'Z[irr G, A] -> 'Res[H] phi \in 'Z[irr H, A].
Proof.
rewrite zchar_split => sHG /andP[Zphi Aphi]; rewrite zchar_split cfRes_vchar //.
apply/cfun_onP=> x /(cfun_onP Aphi); rewrite !cfunElock !genGid sHG => ->.
exact: mul0rn.
Qed.

Lemma cfInd_vchar phi : phi \in 'Z[irr H] -> 'Ind[G] phi \in 'Z[irr G].
Proof.
move=> /vcharP[xi1 Nx1 [xi2 Nxi2 ->]].
by rewrite raddfB rpredB ?char_vchar ?cfInd_char.
Qed.

Lemma sub_conjC_vchar A phi :
  phi \in 'Z[irr G, A] -> phi - (phi^*)%CF \in 'Z[irr G, A^#].
Proof.
move=> Zphi; rewrite sub_aut_zchar ?cfAut_zchar // => _ /irrP[i ->].
  exact: irr_vchar.
exact: cfConjC_irr.
Qed.

Lemma Frobenius_kernel_exists :
  [Frobenius G with complement H] -> {K : {group gT} | [Frobenius G = K ><| H]}.
Proof.
move=> frobG; have [_ ntiHG] := andP frobG.
have [[_ sHG regGH][_ tiHG /eqP defNH]] := (normedTI_memJ_P ntiHG, and3P ntiHG).
suffices /sigW[K defG]: exists K, gval K ><| H == G by exists K; apply/andP.
pose K1 := G :\: cover (H^# :^: G).
have oK1: #|K1| = #|G : H|.
  rewrite cardsD (setIidPr _); last first.
    rewrite cover_imset; apply/bigcupsP=> x Gx.
    by rewrite sub_conjg conjGid ?groupV // (subset_trans (subsetDl _ _)).
  rewrite (cover_partition (partition_normedTI ntiHG)) -(Lagrange sHG).
  by rewrite (card_support_normedTI ntiHG) (cardsD1 1%g) group1 mulSn addnK.
suffices extG i: {j | {in H, 'chi[G]_j =1 'chi[H]_i} & K1 \subset cfker 'chi_j}.
  pose K := [group of \bigcap_i cfker 'chi_(s2val (extG i))].
  have nKH: H \subset 'N(K).
    by apply/norms_bigcap/bigcapsP=> i _; apply: subset_trans (cfker_norm _).
  have tiKH: K :&: H = 1%g.
    apply/trivgP; rewrite -(TI_cfker_irr H) /= setIC; apply/bigcapsP=> i _.
    apply/subsetP=> x /setIP[Hx /bigcapP/(_ i isT)/=]; rewrite !cfkerEirr !inE.
    by case: (extG i) => /= j def_j _; rewrite !def_j.
  exists K; rewrite sdprodE // eqEcard TI_cardMg // mul_subG //=; last first.
    by rewrite (bigcap_min (0 : Iirr H)) ?cfker_sub.
  rewrite -(Lagrange sHG) mulnC leq_pmul2r // -oK1 subset_leq_card //.
  by apply/bigcapsP=> i _; case: (extG i).
case i0: (i == 0).
  exists 0 => [x Hx|]; last by rewrite irr0 cfker_cfun1 subsetDl.
  by rewrite (eqP i0) !irr0 !cfun1E // (subsetP sHG) ?Hx.
have ochi1: '['chi_i, 1] = 0 by rewrite -irr0 cfdot_irr i0.
pose a := 'chi_i 1%g; have Za: a \in Cint by rewrite CintE Cnat_irr1.
pose theta := 'chi_i - a%:A; pose phi := 'Ind[G] theta + a%:A.
have /cfun_onP theta0: theta \in 'CF(H, H^#).
  by rewrite cfunD1E !cfunE cfun11 mulr1 subrr.
have RItheta: 'Res ('Ind[G] theta) = theta.
  apply/cfun_inP=> x Hx; rewrite cfResE ?cfIndE // (big_setID H) /= addrC.
  apply: canLR (mulKf (neq0CG H)) _; rewrite (setIidPr sHG) mulr_natl.
  rewrite big1 ?add0r => [|y /setDP[/regGH tiHy H'y]]; last first.
    have [-> | ntx] := eqVneq x 1%g; first by rewrite conj1g theta0 ?inE ?eqxx.
    by rewrite theta0 ?tiHy // !inE ntx.
  by rewrite -sumr_const; apply: eq_bigr => y Hy; rewrite cfunJ.
have ophi1: '[phi, 1] = 0.
  rewrite cfdotDl -cfdot_Res_r cfRes_cfun1 // cfdotBl !cfdotZl !cfnorm1.
  by rewrite ochi1 add0r addNr.
have{ochi1} n1phi: '[phi] = 1.
  have: '[phi - a%:A] = '[theta] by rewrite addrK -cfdot_Res_l RItheta.
  rewrite !cfnormBd ?cfnormZ ?cfdotZr ?ophi1 ?ochi1 ?mulr0 //.
  by rewrite !cfnorm1 cfnorm_irr => /addIr.
have Zphi: phi \in 'Z[irr G].
  by rewrite rpredD ?cfInd_vchar ?rpredB ?irr_vchar // scale_zchar ?rpred1.
have def_phi: {in H, phi =1 'chi_i}.
  move=> x Hx /=; rewrite !cfunE -[_ x](cfResE _ sHG) ?RItheta //.
  by rewrite !cfunE !cfun1E ?(subsetP sHG) ?Hx ?subrK.
have [j def_chi_j]: {j | 'chi_j = phi}.
  apply/sig_eqW; have [[] [j]] := vchar_norm1P Zphi n1phi; last first.
    by rewrite scale1r; exists j.
  move/cfunP/(_ 1%g)/eqP; rewrite scaleN1r def_phi // cfunE -addr_eq0 eqr_le.
  by rewrite ltr_geF // ltr_paddl ?ltrW ?irr1_gt0.
exists j; rewrite ?cfkerEirr def_chi_j //; apply/subsetP => x /setDP[Gx notHx].
rewrite inE cfunE def_phi // cfunE -/a cfun1E // Gx mulr1 cfIndE //.
rewrite big1 ?mulr0 ?add0r // => y Gy; apply/theta0/(contra _ notHx) => Hxy.
by rewrite -(conjgK y x) cover_imset -class_supportEr mem_imset2 ?groupV.
Qed.

End MoreVchar.

Definition dirr (gT : finGroupType) (B : {set gT}) : pred_class :=  
  [pred f : 'CF(B) | (f \in irr B) || (- f \in irr B)].
Arguments dirr {gT}.

Section Norm1vchar.

Variables (gT : finGroupType) (G : {group gT}).

Fact dirr_key : pred_key (dirr G). Proof. by []. Qed.
Canonical dirr_keyed := KeyedPred dirr_key.

Fact dirr_oppr_closed : oppr_closed (dirr G).
Proof. by move=> xi; rewrite !inE opprK orbC. Qed.
Canonical dirr_opprPred := OpprPred dirr_oppr_closed.

Lemma dirr_opp v : (- v \in dirr G) = (v \in dirr G). Proof. exact: rpredN. Qed.
Lemma dirr_sign n v : ((-1)^+ n *: v \in dirr G) = (v \in dirr G).
Proof. exact: rpredZsign. Qed.

Lemma irr_dirr i : 'chi_i \in dirr G.
Proof. by rewrite !inE mem_irr. Qed.

Lemma dirrP f :
  reflect (exists b : bool, exists i, f = (-1) ^+ b *: 'chi_i) (f \in dirr G).
Proof.
apply: (iffP idP) => [| [b [i ->]]]; last by rewrite dirr_sign irr_dirr.
case/orP=> /irrP[i Hf]; first by exists false, i; rewrite scale1r.
by exists true, i; rewrite scaleN1r -Hf opprK.
Qed.

(* This should perhaps be the definition of dirr. *)
Lemma dirrE phi : phi \in dirr G = (phi \in 'Z[irr G]) && ('[phi] == 1).
Proof.
apply/dirrP/andP=> [[b [i ->]] | [Zphi /eqP/vchar_norm1P]]; last exact.
by rewrite rpredZsign irr_vchar cfnorm_sign cfnorm_irr.
Qed.

Lemma cfdot_dirr f g : f \in dirr G -> g \in dirr G ->
  '[f, g] = (if f == - g then -1 else (f == g)%:R).
Proof.
case/dirrP=> [b1 [i1 ->]] /dirrP[b2 [i2 ->]].
rewrite cfdotZl cfdotZr rmorph_sign mulrA -signr_addb cfdot_irr.
rewrite -scaleNr -signrN !eq_scaled_irr signr_eq0 !(inj_eq signr_inj) /=.
by rewrite -!negb_add addbN mulr_sign -mulNrn mulrb; case: ifP.
Qed.

Lemma dirr_norm1 phi : phi \in 'Z[irr G] -> '[phi] = 1 -> phi \in dirr G.
Proof. by rewrite dirrE => -> -> /=. Qed.

Lemma dirr_aut u phi : (cfAut u phi \in dirr G) = (phi \in dirr G).
Proof.
rewrite !dirrE vchar_aut; apply: andb_id2l => /cfdot_aut_vchar->.
exact: fmorph_eq1.
Qed.

Definition dIirr (B : {set gT}) := (bool * (Iirr B))%type.

Definition dirr1 (B : {set gT}) : dIirr B := (false, 0).

Definition ndirr (B : {set gT}) (i : dIirr B) : dIirr B := 
  (~~ i.1, i.2).

Lemma ndirr_diff (i : dIirr G) : ndirr i != i.
Proof. by case: i => [] [|] i. Qed.

Lemma ndirrK : involutive (@ndirr G).
Proof. by move=> [b i]; rewrite /ndirr /= negbK. Qed.

Lemma ndirr_inj : injective (@ndirr G).
Proof. exact: (inv_inj ndirrK). Qed.

Definition dchi (B : {set gT}) (i : dIirr B) : 'CF(B) := 
  (-1)^+ i.1 *: 'chi_i.2.

Lemma dchi1 : dchi (dirr1 G) = 1.
Proof. by rewrite /dchi scale1r irr0. Qed.

Lemma dirr_dchi i : dchi i \in dirr G.
Proof. by apply/dirrP; exists i.1; exists i.2. Qed.

Lemma dIrrP phi : reflect (exists i, phi = dchi i) (phi \in dirr G).
Proof.
by apply: (iffP idP)=> [/dirrP[b]|] [i ->]; [exists (b, i) | apply: dirr_dchi].
Qed.

Lemma dchi_ndirrE (i : dIirr G) : dchi (ndirr i) = - dchi i.
Proof. by case: i => [b i]; rewrite /ndirr /dchi signrN scaleNr. Qed.

Lemma cfdot_dchi (i j : dIirr G) : 
  '[dchi i, dchi j] = (i == j)%:R - (i == ndirr j)%:R.
Proof.
case: i => bi i; case: j => bj j; rewrite cfdot_dirr ?dirr_dchi // !xpair_eqE.
rewrite -dchi_ndirrE !eq_scaled_irr signr_eq0 !(inj_eq signr_inj) /=.
by rewrite -!negb_add addbN negbK; case: andP => [[->]|]; rewrite ?subr0 ?add0r.
Qed.

Lemma dchi_vchar i : dchi i \in 'Z[irr G].
Proof. by case: i => b i; rewrite rpredZsign irr_vchar. Qed.

Lemma cfnorm_dchi (i : dIirr G) : '[dchi i] = 1.
Proof.  by case: i => b i; rewrite cfnorm_sign cfnorm_irr. Qed.

Lemma dirr_inj : injective (@dchi G).
Proof.
case=> b1 i1 [b2 i2] /eqP; rewrite eq_scaled_irr (inj_eq signr_inj) /=.
by rewrite signr_eq0 -xpair_eqE => /eqP.
Qed.

Definition dirr_dIirr (B : {set gT}) J (f : J -> 'CF(B)) j : dIirr B :=
  odflt (dirr1 B) [pick i | dchi i == f j].

Lemma dirr_dIirrPE J (f : J -> 'CF(G)) (P : pred J) :
    (forall j, P j -> f j \in dirr G) ->
  forall j, P j -> dchi (dirr_dIirr f j) = f j.
Proof.
rewrite /dirr_dIirr => dirrGf j Pj; case: pickP => [i /eqP //|].
by have /dIrrP[i-> /(_ i)/eqP] := dirrGf j Pj.
Qed.

Lemma dirr_dIirrE J (f : J -> 'CF(G)) :
  (forall j, f j \in dirr G) -> forall j, dchi (dirr_dIirr f j) = f j.
Proof. by move=> dirrGf j; apply: (@dirr_dIirrPE _ _ xpredT). Qed.

Definition dirr_constt (B : {set gT}) (phi: 'CF(B)) : {set (dIirr B)} :=  
  [set i | 0 < '[phi, dchi i]].

Lemma dirr_consttE (phi : 'CF(G)) (i : dIirr G) : 
  (i \in dirr_constt phi) = (0 < '[phi, dchi i]).
Proof. by rewrite inE. Qed.

Lemma Cnat_dirr (phi : 'CF(G)) i :
  phi \in 'Z[irr G] -> i \in dirr_constt phi -> '[phi, dchi i] \in Cnat.
Proof.
move=> PiZ; rewrite CnatEint dirr_consttE andbC => /ltrW -> /=.
by case: i => b i; rewrite cfdotZr rmorph_sign rpredMsign Cint_cfdot_vchar_irr.
Qed.
 
Lemma dirr_constt_oppr (i : dIirr G) (phi : 'CF(G)) : 
  (i \in dirr_constt (-phi)) = (ndirr i \in dirr_constt phi).
Proof. by rewrite !dirr_consttE dchi_ndirrE cfdotNl cfdotNr. Qed.

Lemma dirr_constt_oppI (phi: 'CF(G)) :
   dirr_constt phi :&: dirr_constt (-phi) = set0.
Proof.
apply/setP=> i; rewrite inE !dirr_consttE cfdotNl inE.
apply/idP=> /andP [L1 L2]; have := ltr_paddl (ltrW L1) L2.
by rewrite subrr ltr_def eqxx.
Qed.

Lemma dirr_constt_oppl (phi: 'CF(G)) i :
  i \in dirr_constt phi ->  (ndirr i) \notin dirr_constt phi.
Proof.
rewrite !dirr_consttE dchi_ndirrE cfdotNr oppr_gt0.
by move/ltrW=> /ler_gtF ->.
Qed.

Definition to_dirr  (B : {set gT}) (phi : 'CF(B)) (i : Iirr B) : dIirr B := 
  ('[phi, 'chi_i] < 0, i).

Definition of_irr (B : {set gT}) (i : dIirr B) : Iirr B := i.2.

Lemma irr_constt_to_dirr (phi: 'CF(G)) i : phi \in 'Z[irr G] ->
  (i \in irr_constt phi) = (to_dirr phi i \in dirr_constt phi).
Proof.
move=> Zphi; rewrite irr_consttE dirr_consttE cfdotZr rmorph_sign /=.
by rewrite -real_normrEsign ?normr_gt0 ?Creal_Cint // Cint_cfdot_vchar_irr.
Qed.

Lemma to_dirrK (phi: 'CF(G)) : cancel (to_dirr phi) (@of_irr G).
Proof. by []. Qed.

Lemma of_irrK (phi: 'CF(G)) :
  {in dirr_constt phi, cancel (@of_irr G) (to_dirr phi)}.
Proof.
case=> b i; rewrite dirr_consttE cfdotZr rmorph_sign /= /to_dirr mulr_sign.
by rewrite fun_if oppr_gt0; case: b => [|/ltrW/ler_gtF] ->.
Qed.

Lemma cfdot_todirrE (phi: 'CF(G)) i (phi_i := dchi (to_dirr phi i)) :
  '[phi, phi_i] *: phi_i = '[phi, 'chi_i] *: 'chi_i.
Proof. by rewrite cfdotZr rmorph_sign mulrC -scalerA signrZK. Qed.

Lemma cfun_sum_dconstt (phi : 'CF(G)) :
    phi \in 'Z[irr G] ->
  phi = \sum_(i in dirr_constt phi) '[phi, dchi i] *: dchi i.
Proof.
move=> PiZ; rewrite [LHS]cfun_sum_constt.
rewrite (reindex (to_dirr phi))=> [/= |]; last first.
  by exists (@of_irr _)=> //; apply: of_irrK .
by apply: eq_big => i; rewrite ?irr_constt_to_dirr // cfdot_todirrE.
Qed.

Lemma cnorm_dconstt (phi : 'CF(G)) :
  phi \in 'Z[irr G] ->
  '[phi] = \sum_(i in dirr_constt phi) '[phi, dchi i] ^+ 2.
Proof.
move=> PiZ; rewrite {1 2}(cfun_sum_dconstt PiZ).
rewrite cfdot_suml; apply: eq_bigr=> i IiD.
rewrite cfdot_sumr (bigD1 i) //= big1 ?addr0 => [|j /andP [JiD IdJ]].
  rewrite cfdotZr cfdotZl cfdot_dchi eqxx eq_sym (negPf (ndirr_diff i)).
  by rewrite subr0 mulr1 aut_Cnat ?Cnat_dirr.
rewrite cfdotZr cfdotZl cfdot_dchi eq_sym (negPf IdJ) -natrB ?mulr0 //.
by rewrite (negPf (contraNneq _ (dirr_constt_oppl JiD))) => // <-.
Qed.

Lemma dirr_small_norm (phi : 'CF(G)) n :
  phi \in 'Z[irr G] -> '[phi] = n%:R -> (n < 4)%N ->
  [/\ #|dirr_constt phi| = n, dirr_constt phi :&: dirr_constt (- phi) = set0 & 
      phi = \sum_(i in dirr_constt phi) dchi i].
Proof.
move=> PiZ Pln; rewrite ltnNge -leC_nat => Nl4.
suffices Fd i: i \in dirr_constt phi -> '[phi, dchi i] = 1.
  split; last 2 [by apply/setP=> u; rewrite !inE cfdotNl oppr_gt0 ltr_asym].
    apply/eqP; rewrite -eqC_nat -sumr_const -Pln (cnorm_dconstt PiZ).
    by apply/eqP/eq_bigr=> i Hi; rewrite Fd // expr1n.
  rewrite {1}[phi]cfun_sum_dconstt //.
  by apply: eq_bigr => i /Fd->; rewrite scale1r.
move=> IiD; apply: contraNeq Nl4 => phi_i_neq1.
rewrite -Pln cnorm_dconstt // (bigD1 i) ?ler_paddr ?sumr_ge0 //=.
  by move=> j /andP[JiD _]; rewrite exprn_ge0 ?Cnat_ge0 ?Cnat_dirr.
have /CnatP[m Dm] := Cnat_dirr PiZ IiD; rewrite Dm -natrX ler_nat (leq_sqr 2).
by rewrite ltn_neqAle eq_sym -eqC_nat -ltC_nat -Dm phi_i_neq1 -dirr_consttE.
Qed.

Lemma cfdot_sum_dchi (phi1 phi2 : 'CF(G)) :
  '[\sum_(i in dirr_constt phi1) dchi i,
    \sum_(i in dirr_constt phi2) dchi i] = 
  #|dirr_constt phi1 :&: dirr_constt phi2|%:R -
    #|dirr_constt phi1 :&: dirr_constt (- phi2)|%:R.
Proof.
rewrite addrC (big_setID (dirr_constt (- phi2))) /= cfdotDl; congr (_ + _).
  rewrite cfdot_suml -sumr_const -sumrN; apply: eq_bigr => i /setIP[p1i p2i].
  rewrite cfdot_sumr (bigD1 (ndirr i)) -?dirr_constt_oppr //= dchi_ndirrE.
  rewrite cfdotNr cfnorm_dchi big1 ?addr0 // => j /andP[p2j i'j].
  rewrite cfdot_dchi -(inv_eq ndirrK) [in rhs in - rhs]eq_sym (negPf i'j) subr0.
  rewrite (negPf (contraTneq _ p2i)) // => ->.
  by rewrite dirr_constt_oppr dirr_constt_oppl.
rewrite cfdot_sumr (big_setID (dirr_constt phi1)) setIC /= addrC.
rewrite big1 ?add0r => [|j /setDP[p2j p1'j]]; last first.
  rewrite cfdot_suml big1 // => i /setDP[p1i p2'i].
  rewrite cfdot_dchi (negPf (contraTneq _ p1i)) => [|-> //].
  rewrite (negPf (contraNneq _ p2'i)) ?subrr // => ->.
  by rewrite dirr_constt_oppr ndirrK.
rewrite -sumr_const; apply: eq_bigr => i /setIP[p1i p2i]; rewrite cfdot_suml.
rewrite (bigD1 i) /=; last by rewrite inE dirr_constt_oppr dirr_constt_oppl.
rewrite cfnorm_dchi big1 ?addr0 // => j /andP[/setDP[p1j _] i'j].
rewrite cfdot_dchi (negPf i'j) (negPf (contraTneq _ p1j)) ?subrr // => ->.
exact: dirr_constt_oppl.
Qed.

Lemma cfdot_dirr_eq1 :
  {in dirr G &, forall phi psi, ('[phi, psi] == 1) = (phi == psi)}.
Proof.
move=> _ _ /dirrP[b1 [i1 ->]] /dirrP[b2 [i2 ->]].
rewrite eq_signed_irr cfdotZl cfdotZr rmorph_sign cfdot_irr mulrA -signr_addb.
rewrite pmulrn -rmorphMsign (eqr_int _ _ 1) -negb_add.
by case: (b1 (+) b2) (i1 == i2) => [] [].
Qed.

Lemma cfdot_add_dirr_eq1 :
  {in dirr G & &, forall phi1 phi2 psi,
    '[phi1 + phi2, psi] = 1 -> psi = phi1 \/ psi = phi2}.
Proof.
move=> _ _ _ /dirrP[b1 [i1 ->]] /dirrP[b2 [i2 ->]] /dirrP[c [j ->]] /eqP.
rewrite cfdotDl !cfdotZl !cfdotZr !rmorph_sign !cfdot_irr !mulrA -!signr_addb.
rewrite 2!{1}signrE !mulrBl !mul1r -!natrM addrCA -subr_eq0 -!addrA.
rewrite -!opprD addrA subr_eq0 -mulrSr -!natrD eqr_nat => eq_phi_psi.
apply/pred2P; rewrite /= !eq_signed_irr -!negb_add !(eq_sym j) !(addbC c).
by case: (i1 == j) eq_phi_psi; case: (i2 == j); do 2!case: (_ (+) c).
Qed.

End Norm1vchar.

Prenex Implicits ndirr ndirrK to_dirr to_dirrK of_irr.
Arguments of_irrK {gT G phi} [i] phi_i : rename.

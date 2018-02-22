(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrbool ssrfun eqtype ssrnat seq path div choice.
From mathcomp
Require Import fintype tuple finfun bigop prime ssralg poly finset center.
From mathcomp
Require Import fingroup morphism perm automorphism quotient action zmodp.
From mathcomp
Require Import gfunctor gproduct cyclic pgroup frobenius.
From mathcomp
Require Import matrix mxalgebra mxrepresentation vector ssrint.
From mathcomp
Require Import ssrnum algC classfun character inertia vcharacter.
From mathcomp
Require Import PFsection1 PFsection2 PFsection3 PFsection4.

(******************************************************************************)
(* This file covers Peterfalvi, Section 5: Coherence.                         *)
(* Defined here:                                                              *)
(* coherent_with S A tau tau1 <-> tau1 is a Z-linear isometry from 'Z[S] to   *)
(*                         'Z[irr G] that coincides with tau on 'Z[S, A].     *)
(*    coherent S A tau <-> (S, A, tau) is coherent, i.e., there is a Z-linear *)
(*                         isometry tau1 s.t. coherent_with S A tau tau1.     *)
(* subcoherent S tau R <-> S : seq 'cfun(L) is non empty, pairwise orthogonal *)
(*                         and closed under complex conjugation, tau is an    *)
(*                         isometry from 'Z[S, L^#] to virtual characters in  *)
(*                         G that maps the difference chi - chi^*, for each   *)
(*                         chi \in S, to the sum of an orthonormal family     *)
(*                         R chi of virtual characters of G; also, R chi and  *)
(*                         R phi are orthogonal unless phi \in chi :: chi^*.  *)
(*          dual_iso nu == the Z-linear (additive) mapping phi |-> - nu phi^* *)
(*                         for nu : {additive 'CF(L) -> 'CF(G)}. If nu is an  *)
(*                         isometry extending a subcoherent tau on 'Z[S] with *)
(*                         size S = 2, then so is dual_iso nu.                *)
(* We provide a set of definitions that cover the various \cal S notations    *)
(* introduced in Peterfalvi sections 5, 6, 7, and 9 to 14.                    *)
(*         Iirr_ker K A == the set of all i : Iirr K such that the kernel of  *)
(*                         'chi_i contains A.                                 *)
(*      Iirr_kerD K B A == the set of all i : Iirr K such that the kernel of  *)
(*                         'chi_i contains A but not B.                       *)
(*        seqInd L calX == the duplicate-free sequence of characters of L     *)
(*                         induced from K by the 'chi_i for i in calX.        *)
(*          seqIndT K L == the duplicate-free sequence of all characters of L *)
(*                         induced by irreducible characters of K.            *)
(*      seqIndD K L H M == the duplicate-free sequence of characters of L     *)
(*                         induced by irreducible characters of K that have M *)
(*                         in their kernel, but not H.                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(* Results about the set of induced irreducible characters *)
Section InducedIrrs.

Variables (gT : finGroupType) (K L : {group gT}).
Implicit Types (A B : {set gT}) (H M : {group gT}).
Implicit Type u : {rmorphism algC -> algC}.

Section KerIirr.

Definition Iirr_ker A := [set i | A \subset cfker 'chi[K]_i].

Lemma Iirr_kerS A B : B \subset A -> Iirr_ker A \subset Iirr_ker B.
Proof. by move/subset_trans=> sBA; apply/subsetP=> i; rewrite !inE => /sBA. Qed.

Lemma sum_Iirr_ker_square H :
  H <| K -> \sum_(i in Iirr_ker H) 'chi_i 1%g ^+ 2 = #|K : H|%:R.
Proof.
move=> nsHK; rewrite -card_quotient ?normal_norm // -irr_sum_square.
rewrite (eq_bigl _ _ (in_set _)) (reindex _ (mod_Iirr_bij nsHK)) /=.
by apply: eq_big => [i | i _]; rewrite mod_IirrE ?cfker_mod ?cfMod1.
Qed.

Definition Iirr_kerD B A := Iirr_ker A :\: Iirr_ker B.

Lemma sum_Iirr_kerD_square H M :
    H <| K -> M <| K -> M \subset H ->
  \sum_(i in Iirr_kerD H M) 'chi_i 1%g ^+ 2 = #|K : H|%:R * (#|H : M|%:R - 1).
Proof.
move=> nsHK nsMK sMH; have [sHK _] := andP nsHK.
rewrite mulrBr mulr1 -natrM Lagrange_index // -!sum_Iirr_ker_square //.
apply/esym/(canLR (addrK _)); rewrite /= addrC (big_setID (Iirr_ker H)).
by rewrite (setIidPr _) ?Iirr_kerS //.
Qed.

Lemma Iirr_ker_aut u A i : (aut_Iirr u i \in Iirr_ker A) = (i \in Iirr_ker A).
Proof. by rewrite !inE aut_IirrE cfker_aut. Qed.

Lemma Iirr_ker_conjg A i x :
  x \in 'N(A) -> (conjg_Iirr i x \in Iirr_ker A) = (i \in Iirr_ker A).
Proof.
move=> nAx; rewrite !inE conjg_IirrE.
have [nKx | /cfConjgEout-> //] := boolP (x \in 'N(K)).
by rewrite cfker_conjg // -{1}(normP nAx) conjSg.
Qed.

Lemma Iirr_kerDS A1 A2 B1 B2 :
  A2 \subset A1 -> B1 \subset B2 -> Iirr_kerD B1 A1 \subset Iirr_kerD B2 A2.
Proof. by move=> sA12 sB21; rewrite setDSS ?Iirr_kerS. Qed.

Lemma Iirr_kerDY B A : Iirr_kerD (A <*> B) A = Iirr_kerD B A.
Proof. by apply/setP=> i; rewrite !inE join_subG; apply: andb_id2r => ->. Qed.

Lemma mem_Iirr_ker1 i : (i \in Iirr_kerD K 1%g) = (i != 0).
Proof. by rewrite !inE sub1G andbT subGcfker. Qed.

End KerIirr.

Hypothesis nsKL : K <| L.
Let sKL := normal_sub nsKL.
Let nKL := normal_norm nsKL.
Let e := #|L : K|%:R : algC.
Let nze : e != 0 := neq0CiG _ _.

Section SeqInd.

Variable calX : {set (Iirr K)}.

(* The set of characters induced from the irreducibles in calX. *)
Definition seqInd := undup [seq 'Ind[L] 'chi_i | i in calX].
Local Notation S := seqInd.

Lemma seqInd_uniq : uniq S. Proof. exact: undup_uniq. Qed.

Lemma seqIndP phi :
  reflect (exists2 i, i \in calX & phi = 'Ind[L] 'chi_i) (phi \in S).
Proof. by rewrite mem_undup; apply: imageP. Qed.

Lemma seqInd_on : {subset S <= 'CF(L, K)}.
Proof. by move=> _ /seqIndP[i _ ->]; apply: cfInd_normal. Qed.

Lemma seqInd_char : {subset S <= character}.
Proof. by move=> _ /seqIndP[i _ ->]; rewrite cfInd_char ?irr_char. Qed.

Lemma Cnat_seqInd1 phi : phi \in S -> phi 1%g \in Cnat.
Proof. by move/seqInd_char/Cnat_char1. Qed.

Lemma Cint_seqInd1 phi : phi \in S -> phi 1%g \in Cint.
Proof. by rewrite CintE; move/Cnat_seqInd1->. Qed.

Lemma seqInd_neq0 psi : psi \in S -> psi != 0.
Proof. by move=> /seqIndP[i _ ->]; apply: Ind_irr_neq0. Qed.

Lemma seqInd1_neq0 psi : psi \in S -> psi 1%g != 0.
Proof. by move=> Spsi; rewrite char1_eq0 ?seqInd_char ?seqInd_neq0. Qed.

Lemma cfnorm_seqInd_neq0 psi : psi \in S -> '[psi] != 0.
Proof. by move/seqInd_neq0; rewrite cfnorm_eq0. Qed.

Lemma seqInd_ortho : {in S &, forall phi psi, phi != psi -> '[phi, psi] = 0}.
Proof.
move=> _ _ /seqIndP[i _ ->] /seqIndP[j _ ->].
by case: ifP (cfclass_Ind_cases i j nsKL) => // _ -> /eqP.
Qed.

Lemma seqInd_orthogonal : pairwise_orthogonal S.
Proof.
apply/pairwise_orthogonalP; split; last exact: seqInd_ortho.
by rewrite /= undup_uniq andbT; move/memPn: seqInd_neq0.
Qed.

Lemma seqInd_free : free S.
Proof. exact: (orthogonal_free seqInd_orthogonal). Qed.

Lemma seqInd_zcharW : {subset S <= 'Z[S]}.
Proof. by move=> phi Sphi; rewrite mem_zchar ?seqInd_free. Qed.

Lemma seqInd_zchar : {subset S <= 'Z[S, K]}.
Proof. by move=> phi Sphi; rewrite zchar_split seqInd_zcharW ?seqInd_on. Qed.

Lemma seqInd_vcharW : {subset S <= 'Z[irr L]}.
Proof. by move=> phi Sphi; rewrite char_vchar ?seqInd_char. Qed.

Lemma seqInd_vchar : {subset S <= 'Z[irr L, K]}.
Proof. by move=> phi Sphi; rewrite zchar_split seqInd_vcharW ?seqInd_on. Qed.

Lemma zcharD1_seqInd : 'Z[S, L^#] =i 'Z[S, K^#].
Proof.
move=> phi; rewrite zcharD1E (zchar_split _ K^#) cfun_onD1.
by apply: andb_id2l => /(zchar_trans_on seqInd_zchar)/zchar_on->.
Qed.

Lemma zcharD1_seqInd_on : {subset 'Z[S, L^#] <= 'CF(L, K^#)}.
Proof. by move=> phi; rewrite zcharD1_seqInd => /zchar_on. Qed.

Lemma zcharD1_seqInd_Dade A :
  1%g \notin A -> {subset S <= 'CF(L, 1%g |: A)} -> 'Z[S, L^#] =i 'Z[S, A].
Proof.
move=> notA1 A_S phi; rewrite zcharD1E (zchar_split _ A).
apply/andb_id2l=> ZSphi; apply/idP/idP=> [phi10 | /cfun_on0-> //].
rewrite -(setU1K notA1) cfun_onD1 {}phi10 andbT.
have{phi ZSphi} [c -> _] := free_span seqInd_free (zchar_span ZSphi).
by rewrite big_seq memv_suml // => xi /A_S/memvZ.
Qed.

Lemma dvd_index_seqInd1 phi : phi \in S -> phi 1%g / e \in Cnat.
Proof.
by case/seqIndP=> i _ ->; rewrite cfInd1 // mulrC mulKf ?Cnat_irr1.
Qed.

Lemma sub_seqInd_zchar phi psi :
  phi \in S -> psi \in S -> psi 1%g *: phi - phi 1%g *: psi \in 'Z[S, K^#].
Proof.
move=> Sphi Spsi; rewrite zcharD1 !cfunE mulrC subrr eqxx.
by rewrite rpredB ?scale_zchar ?Cint_seqInd1 ?seqInd_zchar.
Qed.

Lemma sub_seqInd_on phi psi :
  phi \in S -> psi \in S -> psi 1%g *: phi - phi 1%g *: psi \in 'CF(L, K^#).
Proof. by move=> Sphi Spsi; apply: zchar_on (sub_seqInd_zchar Sphi Spsi). Qed.

Lemma size_irr_subseq_seqInd S1 :
    subseq S1 S -> {subset S1 <= irr L} ->
  (#|L : K| * size S1 = #|[set i | 'Ind 'chi[K]_i \in S1]|)%N.
Proof.
move=> sS1S irrS1; have uniqS1: uniq S1 := subseq_uniq sS1S seqInd_uniq.
rewrite (card_imset_Ind_irr nsKL) => [|i|i y]; first 1 last.
- by rewrite inE => /irrS1.
- by rewrite !inE => *; rewrite conjg_IirrE -(cfConjgInd _ _ nsKL) ?cfConjg_id.
congr (_ * _)%N; transitivity #|map cfIirr S1|.
  rewrite (card_uniqP _) ?size_map ?map_inj_in_uniq //.
  exact: sub_in2 irrS1 _ (can_in_inj (@cfIirrE _ _)).
apply: eq_card => s; apply/idP/imsetP=> [/mapP[phi S1phi] | [i S1iG]] {s}->.
  have /seqIndP[i _ Dphi]: phi \in S := mem_subseq sS1S S1phi.
  by exists i; rewrite ?inE -Dphi.
by apply: map_f; rewrite inE in S1iG.
Qed.

Section Beta.

Variable xi : 'CF(L).
Hypotheses (Sxi : xi \in S) (xi1 : xi 1%g = e).

Lemma cfInd1_sub_lin_vchar : 'Ind[L, K] 1 - xi \in 'Z[irr L, K^#].
Proof.
rewrite zcharD1 !cfunE xi1 cfInd1 // cfun11 mulr1 subrr eqxx andbT.
rewrite rpredB ?(seqInd_vchar Sxi) // zchar_split cfInd_normal ?char_vchar //.
by rewrite cfInd_char ?cfun1_char.
Qed.

Lemma cfInd1_sub_lin_on : 'Ind[L, K] 1 - xi \in 'CF(L, K^#).
Proof. exact: zchar_on cfInd1_sub_lin_vchar. Qed.

Lemma seqInd_sub_lin_vchar :
  {in S, forall phi : 'CF(L), phi - (phi 1%g / e) *: xi \in 'Z[S, K^#]}.
Proof.
move=> phi Sphi; rewrite /= zcharD1 !cfunE xi1 divfK // subrr eqxx.
by rewrite rpredB ?scale_zchar ?seqInd_zchar // CintE dvd_index_seqInd1.
Qed.

Lemma seqInd_sub_lin_on :
  {in S, forall phi : 'CF(L), phi - (phi 1%g / e) *: xi \in 'CF(L, K^#)}.
Proof. by move=> phi /seqInd_sub_lin_vchar/zchar_on. Qed.

End Beta.

End SeqInd.

Arguments seqIndP [calX phi].

Lemma seqIndS (calX calY : {set Iirr K}) :
 calX \subset calY -> {subset seqInd calX <= seqInd calY}.
Proof.
by move=> sXY _ /seqIndP[i /(subsetP sXY)Yi ->]; apply/seqIndP; exists i.
Qed.

Definition seqIndT := seqInd setT.

Lemma seqInd_subT calX : {subset seqInd calX <= seqIndT}.
Proof. exact: seqIndS (subsetT calX). Qed.

Lemma mem_seqIndT i : 'Ind[L, K] 'chi_i \in seqIndT.
Proof. by apply/seqIndP; exists i; rewrite ?inE. Qed.

Lemma seqIndT_Ind1 : 'Ind[L, K] 1 \in seqIndT.
Proof. by rewrite -irr0 mem_seqIndT. Qed.

Lemma cfAut_seqIndT u : cfAut_closed u seqIndT.
Proof.
by move=> _ /seqIndP[i _ ->]; rewrite cfAutInd -aut_IirrE mem_seqIndT.
Qed.

Definition seqIndD H M := seqInd (Iirr_kerD H M).

Lemma seqIndDY H M : seqIndD (M <*> H) M = seqIndD H M.
Proof. by rewrite /seqIndD Iirr_kerDY. Qed.

Lemma mem_seqInd H M i :
  H <| L -> M <| L -> ('Ind 'chi_i \in seqIndD H M) = (i \in Iirr_kerD H M).
Proof.
move=> nsHL nsML; apply/seqIndP/idP=> [[j Xj] | Xi]; last by exists i.
case/cfclass_Ind_irrP/cfclassP=> // y Ly; rewrite -conjg_IirrE => /irr_inj->.
by rewrite inE !Iirr_ker_conjg -?in_setD ?(subsetP _ y Ly) ?normal_norm.
Qed.

Lemma seqIndC1P phi :
  reflect (exists2 i, i != 0 & phi = 'Ind 'chi[K]_i) (phi \in seqIndD K 1).
Proof.
by apply: (iffP seqIndP) => [] [i nzi ->];
  exists i; rewrite // mem_Iirr_ker1 in nzi *.
Qed.

Lemma seqIndC1_filter : seqIndD K 1 = filter (predC1 ('Ind[L, K] 1)) seqIndT.
Proof.
rewrite filter_undup filter_map (eq_enum (in_set _)) enumT.
congr (undup (map _ _)); apply: eq_filter => i /=.
by rewrite mem_Iirr_ker1 cfInd_irr_eq1.
Qed.

Lemma seqIndC1_rem : seqIndD K 1 = rem ('Ind[L, K] 1) seqIndT.
Proof. by rewrite rem_filter ?seqIndC1_filter ?undup_uniq. Qed.

Section SeqIndD.

Variables H0 H M : {group gT}.

Local Notation S := (seqIndD H M).

Lemma cfAut_seqInd u : cfAut_closed u S.
Proof.
move=> _ /seqIndP[i /setDP[kMi not_kHi] ->]; rewrite cfAutInd -aut_IirrE.
by apply/seqIndP; exists (aut_Iirr u i); rewrite // inE !Iirr_ker_aut not_kHi.
Qed.

Lemma seqInd_conjC_subset1 : H \subset H0 -> cfConjC_subset S (seqIndD H0 1).
Proof.
move=> sHH0; split; [exact: seqInd_uniq | apply: seqIndS | exact: cfAut_seqInd].
by rewrite Iirr_kerDS ?sub1G.
Qed.

Lemma seqInd_sub_aut_zchar u :
  {in S, forall phi, phi - cfAut u phi \in 'Z[S, K^#]}.
Proof.
move=> phi Sphi /=; rewrite sub_aut_zchar ?seqInd_zchar ?cfAut_seqInd //.
exact: seqInd_vcharW.
Qed.

Lemma seqIndD_nonempty : H <| K -> M <| K -> M \proper H -> {phi | phi \in S}.
Proof.
move=> nsHK nsMK /andP[sMH ltMH]; pose X := Iirr_kerD H M.
suffices: \sum_(i in X) 'chi_i 1%g ^+ 2 > 0.
  have [->|[i Xi]] := set_0Vmem X; first by rewrite big_set0 ltrr.
  by exists ('Ind 'chi_i); apply/seqIndP; exists i.
by rewrite sum_Iirr_kerD_square ?mulr_gt0 ?gt0CiG ?subr_gt0 // ltr1n indexg_gt1.
Qed.

Hypothesis sHK : H \subset K.

Lemma seqInd_sub : {subset S <= seqIndD K 1}.
Proof. by apply: seqIndS; apply: Iirr_kerDS (sub1G M) sHK. Qed.

Lemma seqInd_ortho_Ind1 : {in S, forall phi, '[phi, 'Ind[L, K] 1] = 0}.
Proof.
move=> _ /seqInd_sub/seqIndC1P[i nzi ->].
by rewrite -irr0 not_cfclass_Ind_ortho // irr0 cfclass1 // inE irr_eq1.
Qed.

Lemma seqInd_ortho_cfuni : {in S, forall phi, '[phi, '1_K] = 0}.
Proof.
move=> phi /seqInd_ortho_Ind1/eqP; apply: contraTeq => not_o_phi_1K.
by rewrite cfInd_cfun1 // cfdotZr rmorph_nat mulf_neq0.
Qed.

Lemma seqInd_ortho_1 : {in S, forall phi, '[phi, 1] = 0}.
Proof.
move=> _ /seqInd_sub/seqIndC1P[i nzi ->].
by rewrite -cfdot_Res_r cfRes_cfun1 // -irr0 cfdot_irr (negbTE nzi).
Qed.

Lemma sum_seqIndD_square :
    H <| L -> M <| L -> M \subset H ->
  \sum_(phi <- S) phi 1%g ^+ 2 / '[phi] = #|L : H|%:R * (#|H : M|%:R - 1).
Proof.
move=> nsHL nsML sMH; rewrite -(Lagrange_index sKL sHK) natrM -/e -mulrA.
rewrite -sum_Iirr_kerD_square ?(normalS _ sKL) ?(subset_trans sMH) //.
pose h i := @Ordinal (size S).+1 _ (index_size ('Ind 'chi[K]_i) S).
rewrite (partition_big h (ltn^~ (size S))) => /= [|i Xi]; last first.
  by rewrite index_mem mem_seqInd.
rewrite big_distrr big_ord_narrow //= big_index_uniq ?seqInd_uniq //=.
apply: eq_big_seq => phi Sphi; rewrite /eq_op insubT ?index_mem //= => _.
have /seqIndP[i kHMi def_phi] := Sphi.
have/cfunP/(_ 1%g) := scaled_cfResInd_sum_cfclass i nsKL.
rewrite !cfunE sum_cfunE -def_phi cfResE // mulrAC => ->; congr (_ * _).
rewrite reindex_cfclass //=; apply/esym/eq_big => j; last by rewrite !cfunE.
rewrite (sameP (cfclass_Ind_irrP _ _ nsKL) eqP) -def_phi -mem_seqInd //.
by apply/andP/eqP=> [[Sj /eqP/(congr1 (nth 0 S))] | ->]; rewrite ?nth_index.
Qed.

Section Odd.

Hypothesis oddL : odd #|L|.

Lemma seqInd_conjC_ortho : {in S, forall phi, '[phi, phi^*] = 0}.
Proof.
by move=> _  /seqInd_sub/seqIndC1P[i nzi ->]; apply: odd_induced_orthogonal.
Qed.

Lemma seqInd_conjC_neq : {in S, forall phi, phi^* != phi}%CF.
Proof.
move=> phi Sphi; apply: contraNneq (cfnorm_seqInd_neq0 Sphi) => {2}<-.
by rewrite seqInd_conjC_ortho.
Qed.

Lemma seqInd_notReal : ~~ has cfReal S.
Proof. exact/hasPn/seqInd_conjC_neq. Qed.

Lemma seqInd_nontrivial chi : chi \in S -> (1 < size S)%N.
Proof.
move=> Schi; pose S2 := chi^*%CF :: chi.
have: {subset S2 <= S} by apply/allP/and3P; rewrite /= cfAut_seqInd.
by apply: uniq_leq_size; rewrite /= inE seqInd_conjC_neq.
Qed.

Variable chi : 'CF(L).
Hypotheses (irr_chi : chi \in irr L) (Schi : chi \in S).

Lemma seqInd_conjC_ortho2 : orthonormal (chi :: chi^*)%CF.
Proof.
by rewrite /orthonormal/= cfnorm_conjC irrWnorm ?seqInd_conjC_ortho ?eqxx.
Qed.

Lemma seqInd_nontrivial_irr : (#|[set i | 'chi_i \in S]| > 1)%N.
Proof.
have /irrP[i Dchi] := irr_chi; rewrite (cardsD1 i) (cardsD1 (conjC_Iirr i)).
rewrite !inE -(inj_eq irr_inj) conjC_IirrE -Dchi seqInd_conjC_neq //.
by rewrite cfAut_seqInd Schi.
Qed.

End Odd.

End SeqIndD.

Lemma sum_seqIndC1_square :
  \sum_(phi <- seqIndD K 1) phi 1%g ^+ 2 / '[phi] = e * (#|K|%:R - 1).
Proof. by rewrite sum_seqIndD_square ?normal1 ?sub1G // indexg1. Qed.

End InducedIrrs.

Arguments seqIndP [gT K L calX phi].
Arguments seqIndC1P [gT K L phi].

Section Five.

Variable gT : finGroupType.

Section Defs.

Variables L G : {group gT}.

(* This is Peterfalvi, Definition (5.1). *)
(* We depart from the text in Section 5 on three points:                      *)
(*   - We drop non-triviality condition in Z[S, A], which is not used         *)
(*     consistently in the rest of the proof. In particular, it is            *)
(*     incompatible with the use of "not coherent" in (6.2), and it is only   *)
(*     really used in (7.8), where it is equivalent to the simpler condition  *)
(*     (size S > 1). For us the empty S is coherent; this avoids duplicate    *)
(*     work in some inductive proofs, e.g., subcoherent_norm - Lemma (5.4) -  *)
(*     below.                                                                 *)
(*   - The preconditions for coherence (A < L, S < Z[irr L], and tau Z-linear *)
(*     on some E < Z[irr L]) are not part of the definition of "coherent".    *)
(*     These will be captured as separate requirements; in particular in the  *)
(*     Odd Order proof tau will always be C-linear on all of 'CF(L).          *)
(*   - By contrast, our "coherent" only supplies an additive (Z-linear)       *)
(*     isometry, where the source text ambiguously specifies a "linear" one.  *)
(*     When S consists of virtual characters this implies the existence of    *)
(*     a C-linear one: the linear extension of the restriction of the         *)
(*     isometry to a basis of the Z-module Z[S]. The latter can be found from *)
(*     the Smith normal form (see intdiv.v) of the coordinate matrix of S.    *)
(*     The weaker Z-linearity lets us use the dual_iso construction when      *)
(*     size S = 2.                                                            *)
(* Finally, note that although we have retained the A parameter, in the       *)
(* sequel we shall always take A = L^#, as in the text it is always the case  *)
(* that Z[S, A] = Z[S, L^#].                                                  *)
Definition coherent_with S A tau (tau1 : {additive 'CF(L) -> 'CF(G)}) :=
  {in 'Z[S], isometry tau1, to 'Z[irr G]} /\ {in 'Z[S, A], tau1 =1 tau}.

Definition coherent S A tau := exists tau1, coherent_with S A tau tau1.

(* This is Peterfalvi, Hypothesis (5.2). *)
(* The Z-linearity constraint on tau will be expressed by an additive or      *)
(* linear structure on tau.                                                   *)
Definition subcoherent S tau R :=
  [/\ (*a*) [/\ {subset S <= character}, ~~ has cfReal S & cfConjC_closed S],
      (*b*) {in 'Z[S, L^#], isometry tau, to 'Z[@irr gT G, G^#]},
      (*c*) pairwise_orthogonal S,
      (*d*) {in S, forall xi : 'CF(L : {set gT}),
              [/\ {subset R xi <= 'Z[irr G]}, orthonormal (R xi)
                & tau (xi - xi^*%CF) = \sum_(alpha <- R xi) alpha]}
    & (*e*) {in S &, forall xi phi : 'CF(L),
              orthogonal phi (xi :: xi^*%CF) -> orthogonal (R phi) (R xi)}].

Definition dual_iso (nu : {additive 'CF(L) -> 'CF(G)}) :=
  [additive of -%R \o nu \o cfAut conjC].

End Defs.

Section SubsetCoherent.

Variables L G : {group gT}.
Implicit Type tau : 'CF(L) -> 'CF(G).

Lemma subgen_coherent S1 S2 A tau:
  {subset S2 <= 'Z[S1]} -> coherent S1 A tau -> coherent S2 A tau.
Proof.
move/zchar_trans=> sS21 [tau1 [[Itau1 Ztau1] def_tau]].
exists tau1; split; last exact: sub_in1 def_tau.
by split; [apply: sub_in2 Itau1 | apply: sub_in1 Ztau1].
Qed.

Lemma subset_coherent S1 S2 A tau:
  {subset S2 <= S1} -> coherent S1 A tau -> coherent S2 A tau.
Proof.
by move=> sS21; apply: subgen_coherent => phi /sS21/mem_zchar->.
Qed.

Lemma subset_coherent_with S1 S2 A tau (tau1 : {additive 'CF(L) -> 'CF(G)}) :
    {subset S1 <= S2} -> coherent_with S2 A tau tau1 ->
  coherent_with S1 A tau tau1.
Proof.
move=> /zchar_subset sS12 [Itau1 Dtau1].
by split=> [|xi /sS12/Dtau1//]; apply: sub_iso_to Itau1.
Qed.

Lemma perm_eq_coherent S1 S2 A tau:
  perm_eq S1 S2 -> coherent S1 A tau -> coherent S2 A tau.
Proof.
by move=> eqS12; apply: subset_coherent => phi; rewrite (perm_eq_mem eqS12).
Qed.

Lemma dual_coherence S tau R nu :
    subcoherent S tau R -> coherent_with S L^# tau nu -> (size S <= 2)%N ->
  coherent_with S L^# tau (dual_iso nu).
Proof.
move=> [[charS nrS ccS] _ oSS _ _] [[Inu Znu] Dnu] szS2.
split=> [|{Inu Znu oSS} phi ZSphi].
  have{oSS} ccZS := cfAut_zchar ccS.
  have vcharS: {subset S <= 'Z[irr L]} by move=> phi /charS/char_vchar.
  split=> [phi1 phi2 Sphi1 Sphi2 | phi Sphi].
    rewrite cfdotNl cfdotNr opprK Inu ?ccZS // cfdot_conjC aut_Cint //.
    by rewrite Cint_cfdot_vchar ?(zchar_sub_irr vcharS).
  by rewrite rpredN Znu ?ccZS.
rewrite -{}Dnu //; move: ZSphi; rewrite zcharD1E => /andP[].
case/zchar_nth_expansion=> x Zx -> {phi} /=.
case: S charS nrS ccS szS2 x Zx => [_ _ _ _ x _| eta S1].
  by rewrite big_ord0 !raddf0.
case/allP/andP=> Neta _ /norP[eta'c _] /allP/andP[S1_etac _].
rewrite inE [_ == _](negPf eta'c) /= in S1_etac.
case S1E: S1 S1_etac => [|u []] // /predU1P[] //= <- _ z Zz.
rewrite big_ord_recl big_ord1 !raddfD !raddfZ_Cint //=.
rewrite !cfunE (conj_Cnat (Cnat_char1 Neta)) -mulrDl mulf_eq0.
rewrite addr_eq0 char1_eq0 // !scalerN /= cfConjCK addrC.
by case/pred2P => ->; rewrite ?raddf0 //= !scaleNr opprK.
Qed.

Lemma coherent_seqInd_conjCirr S tau R nu r :
    subcoherent S tau R -> coherent_with S L^# tau nu ->
    let chi := 'chi_r in let chi2 := (chi :: chi^*)%CF in
    chi \in S ->
  [/\ {subset map nu chi2 <= 'Z[irr G]}, orthonormal (map nu chi2),
      chi - chi^*%CF \in 'Z[S, L^#] & (nu chi - nu chi^*)%CF 1%g == 0].
Proof.
move=> [[charS nrS ccS] [_ Ztau] oSS _ _] [[Inu Znu] Dnu] chi chi2 Schi.
have sSZ: {subset S <= 'Z[S]} by apply: mem_zchar.
have vcharS: {subset S <= 'Z[irr L]} by move=> phi /charS/char_vchar.
have Schi2: {subset chi2 <= 'Z[S]} by apply/allP; rewrite /= !sSZ ?ccS.
have Schi_diff: chi - chi^*%CF \in 'Z[S, L^#].
  by rewrite sub_aut_zchar // zchar_onG sSZ ?ccS.
split=> // [_ /mapP[xi /Schi2/Znu ? -> //]||].
  apply: map_orthonormal; first by apply: sub_in2 Inu; apply: zchar_trans_on.
  rewrite orthonormalE (conjC_pair_orthogonal ccS) //=.
  by rewrite cfnorm_conjC !cfnorm_irr !eqxx.
by rewrite -raddfB -cfunD1E Dnu // irr_vchar_on ?Ztau.
Qed.

(* There is a simple, direct way of establishing that S is coherent when S    *)
(* has a pivot character eta1 whose degree divides the degree of all other    *)
(* eta_i in S, as then (eta_i - a_i *: eta1)_i>1 will be a basis of Z[S, L^#] *)
(* for some integers a_i. In that case we just need to find a virtual         *)
(* character zeta1 of G with the same norm as eta1, and the same dot product  *)
(* on the image of the eta_i - a_i *: eta1 under tau, for then the linear     *)
(* extension of tau that assigns zeta1 to eta1 is an isometry.                *)
(*   This is used casually by Peterfalvi, e.g., in (5.7), but a rigorous      *)
(* proof does require some work, which is best factored as a Lemma.           *)
Lemma pivot_coherence S (tau : {additive 'CF(L) -> 'CF(G)}) R eta1 zeta1 :
    subcoherent S tau R -> eta1 \in S -> zeta1 \in 'Z[irr G] ->
    {in [predD1 S & eta1], forall eta : 'CF(L),
      exists2 a, a \in Cnat /\ eta 1%g = a * eta1 1%g
              & '[tau (eta - a *: eta1), zeta1] = - a * '[eta1]} ->
   '[zeta1] = '[eta1] ->
  coherent S L^# tau.
Proof.
case=> -[N_S _ _] [Itau Ztau] oSS _ _ Seta1 Zzeta1 isoS Izeta1.
have freeS := orthogonal_free oSS; have uniqS := free_uniq freeS.
have{oSS} [/andP[S'0 _] oSS] := pairwise_orthogonalP oSS.
pose d := eta1 1%g; pose a (eta : 'CF(L)) := truncC (eta 1%g / d).
have{S'0} nzd: d != 0 by rewrite char1_eq0 ?N_S ?(memPn S'0).
pose S1 := eta1 :: [seq eta - eta1 *+ a eta | eta <- rem eta1 S].
have sS_ZS1: {subset S <= 'Z[S1]}; last apply: (subgen_coherent sS_ZS1).
  have Zeta1: eta1 \in 'Z[S1] by rewrite mem_zchar ?mem_head.
  apply/allP; rewrite (eq_all_r (perm_eq_mem (perm_to_rem Seta1))) /= Zeta1.
  apply/allP=> eta Seta; rewrite -(rpredBr eta (rpredMn (a eta) Zeta1)).
  exact/mem_zchar/mem_behead/map_f.
have{sS_ZS1} freeS1: free S1.
  have Sgt0: (0 < size S)%N by case: (S) Seta1.
  rewrite /free eqn_leq dim_span /= size_map size_rem ?prednK // -(eqnP freeS).
  by apply/dimvS/span_subvP => eta /sS_ZS1/zchar_span.
pose iso_eta1 zeta := zeta \in 'Z[S, L^#] /\ '[tau zeta, zeta1] = '[zeta, eta1].
have{isoS} isoS: {in behead S1, forall zeta, iso_eta1 zeta}.
  rewrite /iso_eta1 => _ /mapP[eta Seta ->]; rewrite mem_rem_uniq // in Seta.
  have{Seta} [/isoS[q [Nq Dq] Itau_eta1] [eta1'eta Seta]] := (Seta, andP Seta).
  rewrite zcharD1E rpredB ?rpredMn ?mem_zchar //= -scaler_nat /a Dq mulfK //.
  by rewrite truncCK // !cfunE Dq subrr cfdotBl cfdotZl -mulNr oSS ?add0r.
have isoS1: {in S1, isometry [eta tau with eta1 |-> zeta1], to 'Z[irr G]}.
  split=> [xi eta | eta]; rewrite !in_cons /=; last first.
    by case: eqP => [-> | _  /isoS[/Ztau/zcharW]].
  do 2!case: eqP => [-> _|_  /isoS[? ?]] //; last exact: Itau.
  by apply/(can_inj (@conjCK _)); rewrite -!cfdotC.
have [nu Dnu IZnu] := Zisometry_of_iso freeS1 isoS1.
exists nu; split=> // phi; rewrite zcharD1E => /andP[].
case/(zchar_expansion (free_uniq freeS1)) => b Zb {phi}-> phi1_0.
have{phi1_0} b_eta1_0: b eta1 = 0.
  have:= phi1_0; rewrite sum_cfunE big_cons big_seq big1 ?addr0 => [|zeta].
    by rewrite !cfunE (mulIr_eq0 _ (mulIf nzd)) => /eqP.
  by case/isoS; rewrite cfunE zcharD1E => /andP[_ /eqP->] _; rewrite mulr0.
rewrite !raddf_sum; apply/eq_big_seq=> xi S1xi; rewrite !raddfZ_Cint //=.
by rewrite Dnu //=; case: eqP => // ->; rewrite b_eta1_0 !scale0r.
Qed.

End SubsetCoherent.

(* This is Peterfalvi (5.3)(a). *)
Lemma irr_subcoherent (L G : {group gT}) S tau :
    cfConjC_subset S (irr L) -> ~~ has cfReal S ->
    {in 'Z[S, L^#], isometry tau, to 'Z[irr G, G^#]} ->
  {R | subcoherent S tau R}.
Proof.
case=> uniqS irrS ccS nrS [isoL Ztau].
have N_S: {subset S <= character} by move=> _ /irrS/irrP[i ->]; apply: irr_char.
have Z_S: {subset S <= 'Z[irr L]} by move=> chi /N_S/char_vchar.
have o1S: orthonormal S by apply: sub_orthonormal (irr_orthonormal L).
have [[_ dotSS] oS] := (orthonormalP o1S, orthonormal_orthogonal o1S).
pose beta chi := tau (chi - chi^*%CF); pose eqBP := _ =P beta _.
have Zbeta: {in S, forall chi, chi - (chi^*)%CF \in 'Z[S, L^#]}.
  move=> chi Schi; rewrite /= zcharD1E rpredB ?mem_zchar ?ccS //= !cfunE.
  by rewrite subr_eq0 conj_Cnat // Cnat_char1 ?N_S.
pose sum_beta chi R := \sum_(alpha <- R) alpha == beta chi.
pose Zortho R := all (mem 'Z[irr G]) R && orthonormal R.
have R chi: {R : 2.-tuple 'CF(G) | (chi \in S) ==> sum_beta chi R && Zortho R}.
  apply: sigW; case Schi: (chi \in S) => /=; last by exists [tuple 0; 0].
  move/(_ _ Schi) in Zbeta; have /irrP[i def_chi] := irrS _ Schi.
  have: '[beta chi] = 2%:R.
    rewrite isoL // cfnormBd ?dotSS ?ccS ?eqxx // eq_sym -/(cfReal _).
    by rewrite (negPf (hasPn nrS _ _)).
  case/zchar_small_norm; rewrite ?(zcharW (Ztau _ _)) // => R [oR ZR sumR].
  by exists R; apply/and3P; split; [apply/eqP | apply/allP | ].
exists (fun xi => val (val (R xi))); split=> // [chi Schi | chi phi Schi Sphi].
  by case: (R chi) => Rc /=; rewrite Schi => /and3P[/eqBP-> /allP].
case/andP => /and3P[/=/eqP-opx /eqP-opx' _] _.
have{opx opx'} obpx: '[beta phi, beta chi] = 0.
  rewrite isoL ?Zbeta // cfdotBl !cfdotBr -{3}[chi]cfConjCK.
  by rewrite !cfdot_conjC opx opx' rmorph0 !subr0.
case: (R phi) => [[[|a [|b []]] //= _]].
rewrite Sphi => /and3P[/eqBP sum_ab Zab o_ab].
case: (R chi) => [[[|c [|d []]] //= _]].
rewrite Schi => /and3P[/eqBP-sum_cd Zcd o_cd].
suffices: orthonormal [:: a; - b; c; d].
  rewrite (orthonormal_cat [:: a; _]) => /and3P[_ _].
  by rewrite /orthogonal /= !cfdotNl !oppr_eq0.
apply: vchar_pairs_orthonormal 1 (-1) _ _ _ _.
- by split; apply/allP; rewrite //= rpredN.
- by rewrite o_cd andbT /orthonormal/= cfnormN /orthogonal /= cfdotNr !oppr_eq0.
- by rewrite oppr_eq0 oner_eq0 rpredN rpred1.
rewrite !(big_seq1, big_cons) in sum_ab sum_cd.
rewrite scale1r scaleN1r !opprK sum_ab sum_cd obpx eqxx /=.
by rewrite !(cfun_on0 (zchar_on (Ztau _ _))) ?Zbeta ?inE ?eqxx.
Qed.

(* This is Peterfalvi (5.3)(b). *)
Lemma prDade_subcoherent (G L K H W W1 W2 : {group gT}) A A0 S
    (defW : W1 \x W2 = W) (ddA : prime_Dade_hypothesis G L K H A A0 defW)
    (w_ := fun i j => cyclicTIirr defW i j) (sigma := cyclicTIiso ddA)
    (mu := primeTIred ddA) (delta := fun j => primeTIsign ddA j)
    (tau := Dade ddA) :
    let dsw j k := [seq delta j *: sigma (w_ i k) | i : Iirr W1] in
    let Rmu j := dsw j j ++ map -%R (dsw j (conjC_Iirr j)) in
    cfConjC_subset S (seqIndD K L H 1) -> ~~ has cfReal S ->
  {R | [/\ subcoherent S tau R,
           {in [predI S & irr L] & irr W,
              forall phi w, orthogonal (R phi) (sigma w)}
         & forall j, R (mu j) = Rmu j ]}.
Proof.
pose mu2 i j := primeTIirr ddA i j.
set S0 := seqIndD K L H 1 => dsw Rmu [uS sSS0 ccS] nrS.
have nsKL: K <| L by have [[/sdprod_context[]]] := prDade_prTI ddA.
have /subsetD1P[sAK notA1]: A \subset K^# by have [_ []] := prDade_def ddA.
have [_ _ defA0] := prDade_def ddA.
have defSA: 'Z[S, L^#] =i 'Z[S, A].
  have sS0A1: {subset S0 <= 'CF(L, 1%g |: A)}.
    move=> _ /seqIndP[i /setDP[_ kerH'i] ->]; rewrite inE in kerH'i.
    exact: (prDade_Ind_irr_on ddA) kerH'i.
  move=> phi; have:= zcharD1_seqInd_Dade nsKL notA1 sS0A1 phi.
  rewrite !{1}(zchar_split _ A, zchar_split _ L^#) => eq_phiAL.
  by apply: andb_id2l => /(zchar_subset sSS0) S0phi; rewrite S0phi in eq_phiAL.
have Itau: {in 'Z[S, L^#], isometry tau, to 'Z[irr G, G^#]}.
  apply: sub_iso_to sub_refl (Dade_Zisometry _) => phi; rewrite defSA => SAphi.
  rewrite defA0; apply: zchar_onS (subsetUl _ _) _ _.
  by apply: zchar_sub_irr SAphi => ? /sSS0/seqInd_vcharW.
have orthoS: pairwise_orthogonal S.
  exact: sub_pairwise_orthogonal sSS0 uS (seqInd_orthogonal nsKL _).
pose S1 := filter (mem (irr L)) S.
have sS1S: {subset S1 <= S} by apply/mem_subseq/filter_subseq.
have sZS1S: {subset 'Z[S1, L^#] <= 'Z[S, L^#]}.
  by apply: zchar_subset sS1S; apply: orthogonal_free.
have [||R1 cohR1] := irr_subcoherent _ _ (sub_iso_to sZS1S sub_refl Itau).
- split=> [|phi|phi]; rewrite ?mem_filter ?filter_uniq //; try case/andP=> //.
  by case/irrP=> i {2}-> /=/ccS->; rewrite cfConjC_irr.
- by apply/hasPn=> phi /sS1S/(hasPn nrS).
have{cohR1} [[charS1 _ _] _ _ R1ok R1ortho] := cohR1.
pose R phi := oapp Rmu (R1 phi) [pick j | phi == mu j].
have inS1 phi: [pred j | phi == mu j] =1 pred0 -> phi \in S -> phi \in S1.
  move=> mu'phi Sphi; rewrite mem_filter Sphi andbT /=.
  have{Sphi} /seqIndP[ell _ Dphi] := sSS0 _ Sphi; rewrite Dphi.
  have [[j Dell] | [] //] := prTIres_irr_cases ddA ell.
  by have /=/eqP[] := mu'phi j; rewrite Dphi Dell cfInd_prTIres.
have Smu_nz j: mu j \in S -> j != 0.
  move/(hasPn nrS); apply: contraNneq => ->.
  by rewrite /cfReal -(prTIred_aut ddA) aut_Iirr0.
have oS1sigma phi: phi \in S1 -> orthogonal (R1 phi) (map sigma (irr W)).
  move=> S1phi; have [zR1 oR1] := R1ok _ S1phi; set psi := _ - _=> Dpsi.
  suffices o_psi_sigma: orthogonal (tau psi) (map sigma (irr W)).
    apply/orthogonalP=> aa sw R1aa Wsw; have:= orthoPl o_psi_sigma _ Wsw.
    have{sw Wsw} /dirrP[bw [lw ->]]: sw \in dirr G.
      have [_ /(cycTIirrP defW)[i [j ->]] ->] := mapP Wsw.
      exact: cycTIiso_dirr.
    have [|ba [la Daa]] := vchar_norm1P (zR1 _ R1aa).
      by have [_ -> //] := orthonormalP oR1; rewrite eqxx.
    rewrite Daa cfdotZl !cfdotZr cfdot_irr.
    case: eqP => [<-{lw} | _ _]; last by rewrite !mulr0.
    move/(congr1 ( *%R ((-1) ^+ (ba (+) bw))^*)); rewrite mulr0 => /eqP/idPn[].
    rewrite mulrA -rmorphM -signr_addb {bw}addbK -cfdotZr -{ba la}Daa.
    rewrite Dpsi -(eq_bigr _ (fun _ _ => scale1r _)).
    by rewrite cfproj_sum_orthonormal ?oner_eq0.
  apply/orthoPl=> _ /mapP[_ /(cycTIirrP defW)[i [j ->]] ->]; rewrite -/w_.
  pose w1 := #|W1|; pose w2 := #|W2|.
  have minw_gt2: (2 < minn w1 w2)%N.
    have [[_ ntW1 _ _] [ntW2 _ _] _] := prDade_prTI ddA.
    rewrite -(dprod_card defW) odd_mul => /andP[oddW1 oddW2].
    by rewrite leq_min !odd_gt2 ?cardG_gt1.
  apply: contraTeq (minw_gt2) => ntNC; rewrite -leqNgt.
  pose NC := cyclicTI_NC ddA.
  have /andP[/=/irrP[l Dphi] Sphi]: phi \in [predI irr L & S].
    by rewrite mem_filter in S1phi.
  have Zpsi: psi \in 'Z[S, L^#].
    rewrite sub_aut_zchar ?mem_zchar_on ?orthogonal_free ?ccS ?cfun_onG //.
    by move=> ? /sSS0/seqInd_vcharW.
  have NCpsi_le2: (NC (tau psi) <= 2)%N.
    have{Itau} [Itau Ztau] := Itau.
    suff: '[tau psi] <= 2%:R by apply: cycTI_NC_norm; apply: zcharW (Ztau _ _).
    rewrite Itau // cfnormBd; first by rewrite cfnorm_conjC Dphi cfnorm_irr.
    have /pairwise_orthogonalP[_ -> //] := orthoS; first exact: ccS.
    by rewrite eq_sym (hasPn nrS).
  apply: leq_trans (NCpsi_le2).
  have: (0 < NC (tau psi) < 2 * minn w1 w2)%N.
    rewrite -(subnKC minw_gt2) (leq_ltn_trans NCpsi_le2) // andbT lt0n.
    by apply/existsP; exists (i, j); rewrite /= topredE inE.
  apply: cycTI_NC_minn (ddA) _ _ => x Vx.
  rewrite Dade_id; last by rewrite defA0 inE orbC mem_class_support.
  rewrite defSA in Zpsi; rewrite (cfun_on0 (zchar_on Zpsi)) // -in_setC.
  by apply: subsetP (subsetP (prDade_supp_disjoint ddA) x Vx); rewrite setCS.
exists R; split=> [|phi w S1phi irr_w|j]; first 1 last.
- rewrite /R; case: pickP => [j /eqP Dphi | _ /=].
    by case/nandP: S1phi; right; rewrite /= Dphi (prTIred_not_irr ddA).
  apply/orthoPr=> aa R1aa; rewrite (orthogonalP (oS1sigma phi _)) ?map_f //.
  by rewrite mem_filter andbC.
- by rewrite /R; case: pickP => /= [k /eqP/(prTIred_inj ddA)-> | /(_ j)/eqP].
have Zw i j: w_ i j \in 'Z[irr W] by apply: irr_vchar.
have{oS1sigma} oS1dsw psi j: psi \in S1 -> orthogonal (R1 psi) (dsw _ j).
  move/oS1sigma/orthogonalP=> opsiW.
  apply/orthogonalP=> aa _ R1aa /codomP[i ->].
  by rewrite cfdotZr opsiW ?map_f ?mem_irr ?mulr0.
have odsw j1 j2: j1 != j2 -> orthogonal (dsw _ j1) (dsw _ j2).
  move/negPf=> j2'1; apply/orthogonalP=> _ _ /codomP[i1 ->] /codomP[i2 ->].
  by rewrite cfdotZl cfdotZr (cfdot_cycTIiso ddA) j2'1 andbF !mulr0.
split=> // [|phi Sphi|phi xi Sphi Sxi].
- by split=> // phi /sSS0; apply: seqInd_char.
- rewrite /R; case: pickP => [j /eqP Dphi /= | /inS1/(_ Sphi)/R1ok//].
  have nz_j: j != 0 by rewrite Smu_nz -?Dphi.
  have [Isig Zsig]: {in 'Z[irr W], isometry sigma, to 'Z[irr G]}.
    exact: cycTI_Zisometry.
  split=> [aa | |].
  - rewrite mem_cat -map_comp.
    by case/orP=> /codomP[i ->]; rewrite ?rpredN rpredZsign Zsig.
  - rewrite orthonormal_cat orthogonal_oppr odsw ?andbT; last first.
      rewrite -(inj_eq (prTIred_inj ddA)) (prTIred_aut ddA) -/mu -Dphi.
      by rewrite eq_sym (hasPn nrS).
    suffices oNdsw k: orthonormal (dsw j k).
      by rewrite map_orthonormal ?oNdsw //; apply: in2W; apply: opp_isometry.
    apply/orthonormalP; split=> [|_ _ /codomP[i1 ->] /codomP[i2 ->]].
      rewrite map_inj_uniq ?enum_uniq // => i1 i2 /(can_inj (signrZK _))/eqP.
      by rewrite (cycTIiso_eqE ddA) eqxx andbT => /eqP.
    rewrite cfdotZl cfdotZr rmorph_sign signrMK (cfdot_cycTIiso ddA).
    by rewrite -(cycTIiso_eqE ddA) (inj_eq (can_inj (signrZK _))).
  have [Tstruct [tau1 Dtau1 [_ Dtau]]] := uniform_prTIred_coherent ddA nz_j.
  have{Tstruct} [/orthogonal_free freeT _ ccT _ _] := Tstruct.
  have phi1c: (phi 1%g)^* = phi 1%g := conj_Cnat (Cnat_seqInd1 (sSS0 _ Sphi)).
  rewrite -[tau _]Dtau; last first.
    rewrite zcharD1E !cfunE phi1c subrr Dphi eqxx andbT.
    by rewrite rpredB ?mem_zchar ?ccT ?image_f ?inE // nz_j eqxx.
  rewrite linearB Dphi -(prTIred_aut ddA) !Dtau1 -/w_ -/sigma -/(delta j).
  by rewrite big_cat /= !big_map !raddf_sum.
rewrite /R; case: pickP => [j1 /eqP Dxi | /inS1/(_ Sxi)S1xi]; last first.
  case: pickP => [j2 _ _ | /inS1/(_ Sphi)S1phi]; last exact: R1ortho.
  by rewrite orthogonal_catr orthogonal_oppr !oS1dsw.
case: pickP => [j2 /eqP Dphi | /inS1/(_ Sphi)S1phi _]; last first.
  by rewrite orthogonal_sym orthogonal_catr orthogonal_oppr !oS1dsw.
case/andP=> /and3P[/= /eqP o_xi_phi /eqP o_xi_phi'] _ _.
have /eqP nz_xi: '[xi] != 0 := cfnorm_seqInd_neq0 nsKL (sSS0 _ Sxi).
have [Dj1 | j2'1] := eqVneq j1 j2.
  by rewrite {2}Dxi Dj1 -Dphi o_xi_phi in nz_xi.
have [Dj1 | j2c'1] := eqVneq j1 (conjC_Iirr j2).
  by rewrite {2}Dxi Dj1 /mu (prTIred_aut ddA) -/mu -Dphi o_xi_phi' in nz_xi.
rewrite orthogonal_catl orthogonal_oppl !orthogonal_catr !orthogonal_oppr.
by rewrite !odsw ?(inv_eq (@conjC_IirrK _ _)) ?conjC_IirrK.
Qed.

Section SubCoherentProperties.

Variables (L G : {group gT}) (S : seq 'CF(L)) (R : 'CF(L) -> seq 'CF(G)).
Variable tau : {linear 'CF(L) -> 'CF(G)}.
Hypothesis cohS : subcoherent S tau R.

Lemma nil_coherent A : coherent [::] A tau.
Proof.
exists [additive of 'Ind[G]]; split=> [|u /zchar_span]; last first.
  by rewrite span_nil memv0 => /eqP-> /=; rewrite !raddf0.
split=> [u v | u] /zchar_span; rewrite span_nil memv0 => /eqP->.
  by rewrite raddf0 !cfdot0l.
by rewrite raddf0 rpred0.
Qed.

Lemma subset_subcoherent S1 : cfConjC_subset S1 S -> subcoherent S1 tau R.
Proof.
case=> uS1 sS1 ccS1; have [[N_S nrS _] Itau oS defR oR] := cohS.
split; last 1 [exact: sub_in1 defR | exact: sub_in2 oR].
- split=> // [xi /sS1/N_S// | ].
  by apply/hasPn; apply: sub_in1 (hasPn nrS).
- by apply: sub_iso_to Itau => //; apply: zchar_subset.
exact: sub_pairwise_orthogonal oS.
Qed.

Lemma subset_ortho_subcoherent S1 chi :
  {subset S1 <= S} -> chi \in S -> chi \notin S1 -> orthogonal S1 chi.
Proof.
move=> sS1S Schi S1'chi; apply/orthoPr=> phi S1phi; have Sphi := sS1S _ S1phi.
have [_ _ /pairwise_orthogonalP[_ -> //]] := cohS.
by apply: contraNneq S1'chi => <-.
Qed.

Lemma subcoherent_split chi beta :
    chi \in S -> beta \in 'Z[irr G] ->
  exists2 X, X \in 'Z[R chi]
        & exists Y, [/\ beta = X - Y, '[X, Y] = 0 & orthogonal Y (R chi)].
Proof.
move=> Schi Zbeta; have [_ _ _ /(_ _ Schi)[ZR oRR _] _] := cohS.
have [X RX [Y [defXY oXY oYR]]] := orthogonal_split (R chi) beta.
exists X; last first.
  by exists (- Y); rewrite opprK (orthogonal_oppl Y) cfdotNr oXY oppr0.
have [_ -> ->] := orthonormal_span oRR RX; rewrite big_seq rpred_sum // => a Ra.
rewrite rpredZ_Cint ?mem_zchar // -(addrK Y X) -defXY.
by rewrite cfdotBl (orthoPl oYR) // subr0 Cint_cfdot_vchar // ZR.
Qed.

(* This is Peterfalvi (5.4). *)
(* The assumption X \in 'Z[R chi] has been weakened to '[X, Y] = 0; this      *)
(* stronger form of the lemma is needed to strengthen the proof of (5.6.3) so *)
(* that it can actually be reused in (9.11.8), as the text suggests.          *)
Lemma subcoherent_norm chi psi (tau1 : {additive 'CF(L) -> 'CF(G)}) X Y :
    [/\ chi \in S, psi \in 'Z[irr L] & orthogonal (chi :: chi^*)%CF psi] ->
    let S0 := chi - psi :: chi - chi^*%CF in
    {in 'Z[S0], isometry tau1, to 'Z[irr G]} ->
    tau1 (chi - chi^*%CF) = tau (chi - chi^*%CF) ->
    [/\ tau1 (chi - psi) = X - Y, '[X, Y] = 0 & orthogonal Y (R chi)] ->
 [/\ (*a*) '[chi] <= '[X]
   & (*b*) '[psi] <= '[Y] ->
           [/\ '[X] = '[chi], '[Y] = '[psi]
             & exists2 E, subseq E (R chi) & X = \sum_(xi <- E) xi]].
Proof.
case=> Schi Zpsi /and3P[/andP[/eqP-ochi_psi _] /andP[/eqP-ochic_psi _] _] S0.
move=> [Itau1 Ztau1] tau1dchi [defXY oXY oYR].
have [[ZS nrS ccS] [tS Zt] oS /(_ _ Schi)[ZR o1R tau_dchi] _] := cohS.
have [/=/andP[S'0 uS] oSS] := pairwise_orthogonalP oS.
have [nRchi Schic] := (hasPn nrS _ Schi, ccS _ Schi).
have ZtauS00: tau1 S0`_0 \in 'Z[irr G] by rewrite Ztau1 ?mem_zchar ?mem_head.
have{ZtauS00} [X1 R_X1 [Y1 [dXY1 oXY1 oY1R]]] := subcoherent_split Schi ZtauS00.
have [uR _] := orthonormalP o1R; have [a Za defX1] := zchar_expansion uR R_X1.
have dotS00R xi: xi \in R chi -> '[tau1 S0`_0, xi] = a xi.
  move=> Rxi; rewrite dXY1 cfdotBl (orthoPl oY1R) // subr0.
  by rewrite defX1 cfproj_sum_orthonormal.
have nchi: '[chi] = \sum_(xi <- R chi) a xi.
  transitivity '[tau1 S0`_0, tau1 S0`_1]; last first.
    by rewrite tau1dchi tau_dchi cfdot_sumr; apply: eq_big_seq dotS00R.
  rewrite [RHS]cfdotC Itau1 ?mem_zchar ?mem_nth // cfdotBl !cfdotBr.
  by rewrite ochi_psi ochic_psi (oSS chi^*%CF) // !subr0 -cfdotC.
have normX: '[X1] <= '[X] ?= iff (X == X1).
  rewrite -[in '[X]](subrK X1 X) -subr_eq0 cfnormDd.
    by rewrite -lerif_subLR subrr -cfnorm_eq0 eq_sym; apply/lerif_eq/cfnorm_ge0.
  rewrite defX1 cfdot_sumr big1_seq // => xi Rxi.
  rewrite cfdotZr cfdotBl cfproj_sum_orthonormal // -{2}dotS00R // defXY.
  by rewrite cfdotBl (orthoPl oYR) // subr0 subrr mulr0.
pose is01a xi := a xi == (a xi != 0)%:R.
have leXa xi: a xi <= `|a xi| ^+ 2 ?= iff is01a xi.
  rewrite Cint_normK //; split; first by rewrite Cint_ler_sqr.
  rewrite eq_sym -subr_eq0 -[lhs in _ - lhs]mulr1 -mulrBr mulf_eq0 subr_eq0.
  by rewrite /is01a; case a_xi_0: (a xi == 0).
have{nchi normX} part_a: '[chi] <= '[X] ?= iff all is01a (R chi) && (X == X1).
  apply: lerif_trans normX; rewrite nchi defX1 cfnorm_sum_orthonormal //.
  by rewrite -big_all !(big_tnth _ _ (R chi)) big_andE; apply: lerif_sum.
split=> [|/lerif_eq part_b]; first by case: part_a.
have [_ /esym] := lerif_add part_a part_b; rewrite -!cfnormBd // -defXY.
rewrite Itau1 ?mem_zchar ?mem_head // eqxx => /andP[a_eq /eqP->].
split=> //; first by apply/esym/eqP; rewrite part_a.
have{a_eq} [/allP a01 /eqP->] := andP a_eq; rewrite defX1.
exists [seq xi <- R chi | a xi != 0]; first exact: filter_subseq.
rewrite big_filter [rhs in _ = rhs]big_mkcond /=.
by apply: eq_big_seq => xi Rxi; rewrite -mulrb -scaler_nat -(eqP (a01 _ _)).
Qed.

(* This is Peterfalvi (5.5). *)
Lemma coherent_sum_subseq chi (tau1 : {additive 'CF(L) -> 'CF(G)}) :
    chi \in S ->
    {in 'Z[chi :: chi^*%CF], isometry tau1, to 'Z[irr G]} ->
    tau1 (chi - chi^*%CF) = tau (chi - chi^*%CF) ->
  exists2 E, subseq E (R chi) & tau1 chi = \sum_(a <- E) a.
Proof.
set S1 := chi :: _ => Schi [iso_t1 Zt1] t1cc'.
have freeS1: free S1.
  have [[_ nrS ccS] _ oS _ _] := cohS.
  by rewrite orthogonal_free ?(conjC_pair_orthogonal ccS).
have subS01: {subset 'Z[chi - 0 :: chi - chi^*%CF] <= 'Z[S1]}.
  apply: zchar_trans setT _; apply/allP; rewrite subr0 /= andbT.
  by rewrite rpredB !mem_zchar ?inE ?eqxx ?orbT.
have Zt1c: tau1 (chi - 0) \in 'Z[irr G].
  by rewrite subr0 Zt1 ?mem_zchar ?mem_head.
have [X R_X [Y defXY]] := subcoherent_split Schi Zt1c.
case/subcoherent_norm: (defXY); last 2 [by []].
- by rewrite Schi rpred0 /orthogonal /= !cfdot0r eqxx.
- by split; [apply: sub_in2 iso_t1 | apply: sub_in1 Zt1].
move=> _ [|_ /eqP]; rewrite cfdot0l ?cfnorm_ge0 // cfnorm_eq0 => /eqP Y0.
case=> E sER defX; exists E => //; rewrite -defX -[X]subr0 -Y0 -[chi]subr0.
by case: defXY.
Qed.

(* A reformulation of (5.5) that is more convenient to use. *)
Corollary mem_coherent_sum_subseq S1 chi (tau1 : {additive 'CF(L) -> 'CF(G)}) :
    cfConjC_subset S1 S -> coherent_with S1 L^# tau tau1 -> chi \in S1 ->
  exists2 E, subseq E (R chi) & tau1 chi = \sum_(a <- E) a.
Proof.
move=> uccS1 [Itau1 Dtau1] S1chi; have [uS1 sS1S ccS1] := uccS1.
have S1chi_s: chi^*%CF \in S1 by apply: ccS1.
apply: coherent_sum_subseq; first exact: sS1S.
  by apply: sub_iso_to Itau1 => //; apply: zchar_subset; apply/allP/and3P.
apply: Dtau1; rewrite sub_aut_zchar ?zchar_onG ?mem_zchar // => phi /sS1S-Sphi.
by apply: char_vchar; have [[->]] := cohS.
Qed.

(* A frequently used consequence of (5.5). *)
Corollary coherent_ortho_supp S1 chi (tau1 : {additive 'CF(L) -> 'CF(G)}) :
    cfConjC_subset S1 S -> coherent_with S1 L^# tau tau1 ->
    chi \in S -> chi \notin S1 -> 
  orthogonal (map tau1 S1) (R chi).
Proof.
move=> uccS1 cohS1 Schi S1'chi; have [uS1 sS1S ccS1] := uccS1.
apply/orthogonalP=> _ mu /mapP[phi S1phi ->] Rmu; have Sphi := sS1S _ S1phi.
have [e /mem_subseq Re ->] := mem_coherent_sum_subseq uccS1 cohS1 S1phi.
rewrite cfdot_suml big1_seq // => xi {e Re}/Re Rxi.
apply: orthogonalP xi mu Rxi Rmu; have [_ _ _ _ -> //] := cohS.
rewrite /orthogonal /= !andbT cfdot_conjCr fmorph_eq0.
by rewrite !(orthoPr (subset_ortho_subcoherent sS1S _ _)) ?ccS1 ?eqxx.
Qed.

(* An even more frequently used corollary of the corollary above. *)
Corollary coherent_ortho S1 S2 (tau1 tau2 : {additive 'CF(L) -> 'CF(G)}) :
    cfConjC_subset S1 S -> coherent_with S1 L^# tau tau1 ->
    cfConjC_subset S2 S -> coherent_with S2 L^# tau tau2 ->
    {subset S2 <= [predC S1]} ->
  orthogonal (map tau1 S1) (map tau2 S2).
Proof.
move=> uccS1 cohS1 uccS2 cohS2 S1'2; have [_ sS2S _] := uccS2.
apply/orthogonalP=> mu _ S1mu /mapP[phi S2phi ->].
have [e /mem_subseq Re ->] := mem_coherent_sum_subseq uccS2 cohS2 S2phi.
rewrite cfdot_sumr big1_seq // => xi {e Re}/Re; apply: orthogonalP mu xi S1mu.
by apply: coherent_ortho_supp; rewrite ?sS2S //; apply: S1'2.
Qed.

(* A glueing lemma exploiting the corollary above. *)
Lemma bridge_coherent S1 S2 (tau1 tau2 : {additive 'CF(L) -> 'CF(G)}) chi phi :
    cfConjC_subset S1 S -> coherent_with S1 L^# tau tau1 ->
    cfConjC_subset S2 S -> coherent_with S2 L^# tau tau2 ->
    {subset S2 <= [predC S1]} ->
    [/\ chi \in S1, phi \in 'Z[S2] & chi - phi \in 'CF(L, L^#)] ->
    tau (chi - phi) = tau1 chi - tau2 phi ->
  coherent (S1 ++ S2) L^# tau.
Proof.
move=> uccS1 cohS1 uccS2 cohS2 S1'2 [S1chi S2phi chi1_phi] tau_chi_phi.
do [rewrite cfunD1E !cfunE subr_eq0 => /eqP] in chi1_phi.
have [[uS1 sS1S _] [uS2 sS2S _]] := (uccS1, uccS2).
have [[[Itau1 Ztau1] Dtau1] [[Itau2 Ztau2] Dtau2]] := (cohS1, cohS2).
have [[N_S1 _ _] _ oS11 _ _] := subset_subcoherent uccS1.
have [_ _ oS22 _ _] := subset_subcoherent uccS2.
have nz_chi1: chi 1%g != 0; last move/mem_zchar in S1chi.
  by rewrite char1_eq0 ?N_S1 //; have [/memPn->] := andP oS11.
have oS12: orthogonal S1 S2.
  apply/orthogonalP=> xi1 xi2 Sxi1 Sxi2; apply: orthoPr xi1 Sxi1.
  by rewrite subset_ortho_subcoherent ?sS2S //; apply: S1'2.
set S3 := S1 ++ S2; pose Y := map tau1 S1 ++ map tau2 S2.
have oS3: pairwise_orthogonal S3 by rewrite pairwise_orthogonal_cat oS11 oS22.
have oY: pairwise_orthogonal Y.
  by rewrite pairwise_orthogonal_cat !map_pairwise_orthogonal ?coherent_ortho.
have Z_Y: {subset Y <= 'Z[irr G]}.
  move=> psi; rewrite mem_cat.
  by case/orP=> /mapP[xi /mem_zchar] => [/Ztau1 | /Ztau2]-Zpsi ->.
have normY: map cfnorm Y = map cfnorm (S1 ++ S2).
  rewrite !map_cat -!map_comp; congr (_ ++ _).
    by apply/eq_in_map => xi S1xi; rewrite /= Itau1 ?mem_zchar.
  by apply/eq_in_map => xi S2xi; rewrite /= Itau2 ?mem_zchar.
have [tau3 defY ZItau3] := Zisometry_of_cfnorm oS3 oY normY Z_Y.
have{defY} [defY1 defY2]: {in S1, tau3 =1 tau1} /\ {in S2, tau3 =1 tau2}.
  have/eqP := defY; rewrite map_cat eqseq_cat ?size_map //.
  by case/andP; split; apply/eq_in_map/eqP.
exists tau3; split=> {ZItau3}// eta; rewrite zcharD1E.
case/andP=> /(zchar_expansion (free_uniq (orthogonal_free oS3)))[b Zb {eta}->].
pose bS Si := \sum_(xi <- Si) b xi *: xi.
have ZbS Si: bS Si \in 'Z[Si].
  by rewrite /bS big_seq rpred_sum // => eta /mem_zchar/rpredZ_Cint->.
rewrite big_cat /= -!/(bS _) cfunE addrC addr_eq0 linearD => /eqP-bS2_1.
transitivity (tau1 (bS S1) + tau2 (bS S2)).
  by rewrite !raddf_sum; congr (_ + _); apply/eq_big_seq=> xi Si_xi;
     rewrite !raddfZ_Cint // -(defY1, defY2).
have Z_S1_1 psi: psi \in 'Z[S1] -> psi 1%g \in Cint.
  by move/zchar_sub_irr=> Zpsi; apply/Cint_vchar1/Zpsi => ? /N_S1/char_vchar.
apply/(scalerI nz_chi1)/(addIr (- bS S1 1%g *: tau (chi - phi))).
rewrite [in LHS]tau_chi_phi !scalerDr -!raddfZ_Cint ?rpredN ?Z_S1_1 //=.
rewrite addrACA -!raddfD -raddfB !scalerDr !scaleNr scalerN !opprK.
rewrite Dtau2 ?Dtau1 ?zcharD1E ?cfunE; first by rewrite -raddfD addrACA.
  by rewrite mulrC subrr rpredB ?rpredZ_Cint ?Z_S1_1 /=.
by rewrite mulrC bS2_1 -chi1_phi mulNr addNr rpredD ?rpredZ_Cint ?Z_S1_1 /=.
Qed.

(* This is essentially Peterfalvi (5.6.3), which gets reused in (9.11.8).     *)
(* While the assumptions are similar to those of the pivot_coherence lemma,   *)
(* the two results are mostly independent: here S1 need not have a pivot, and *)
(* extend_coherent_with does not apply to the base case (size S = 2) of       *)
(* pivot_coherence, which is almost as hard to prove as the general case.     *)
Lemma extend_coherent_with S1 (tau1 : {additive 'CF(L) -> 'CF(G)}) chi phi a X :
    cfConjC_subset S1 S -> coherent_with S1 L^# tau tau1 ->
    [/\ phi \in S1, chi \in S & chi \notin S1] ->
    [/\ a \in Cint, chi 1%g = a * phi 1%g & '[X, a *: tau1 phi] = 0] ->
    tau (chi - a *: phi) = X - a *: tau1 phi ->
  coherent (chi :: chi^*%CF :: S1) L^# tau.
Proof.
set beta := _ - _ => sS10 cohS1 [S1phi Schi S1'chi] [Za chi1 oXaphi] tau_beta.
have [[uS1 sS1S ccS1] [[Itau1 Ztau1] _]] := (sS10, cohS1).
have [[N_S nrS ccS] ZItau _ R_P _] := cohS; have [Itau Ztau] := ZItau.
have [Sphi [ZR o1R sumR]] := (sS1S _ S1phi, R_P _ Schi).
have Zbeta: beta \in 'Z[S, L^#].
  by rewrite zcharD1E !cfunE -chi1 subrr rpredB ?scale_zchar ?mem_zchar /=.
have o_aphi_R: orthogonal (a *: tau1 phi) (R chi).
  have /orthogonalP oS1R := coherent_ortho_supp sS10 cohS1 Schi S1'chi.
  by apply/orthoPl=> xi Rxi; rewrite cfdotZl oS1R ?map_f ?mulr0.
have /orthoPl o_chi_S1: orthogonal chi S1.
  by rewrite orthogonal_sym subset_ortho_subcoherent.
have Zdchi: chi - chi^*%CF \in 'Z[S, L^#].
  by rewrite sub_aut_zchar ?zchar_onG ?mem_zchar ?ccS // => xi /N_S/char_vchar.
have [||_] := subcoherent_norm _ _ (erefl _) (And3 tau_beta oXaphi o_aphi_R).
- rewrite Schi rpredZ_Cint ?char_vchar ?N_S /orthogonal //= !cfdotZr.
  by rewrite cfdot_conjCl !o_chi_S1 ?ccS1 // conjC0 !mulr0 !eqxx.
- apply: sub_iso_to ZItau; [apply: zchar_trans_on; apply/allP | exact: zcharW].
  by rewrite /= Zbeta Zdchi.
case=> [|nX _ [e Re defX]]; first by rewrite !cfnormZ Itau1 ?mem_zchar.
have uR: uniq (R chi) by have [] := orthonormalP o1R.
have{uR} De: e = filter (mem e) (R chi) by apply/subseq_uniqP.
pose ec := filter [predC e] (R chi); pose Xc := - \sum_(xi <- ec) xi.
have defR: perm_eq (e ++ ec) (R chi) by rewrite De perm_filterC.
pose S2 := chi :: chi^*%CF; pose X2 := X :: Xc.
have{nrS} uS2: uniq S2 by rewrite /= andbT inE eq_sym (hasPn nrS).
have sS20: cfConjC_subset S2 S.
  by split=> //; apply/allP; rewrite /= ?cfConjCK ?inE ?eqxx ?orbT // ccS Schi.
have oS2: pairwise_orthogonal S2 by have [] := subset_subcoherent sS20.
have nz_chi: chi != 0 by rewrite eq_sym; have [/norP[]] := andP oS2.
have o_chi_chic: '[chi, chi^*] = 0 by have [_ /andP[/andP[/eqP]]] := and3P oS2.
have def_XXc: X - Xc = tau (chi - chi^*%CF).
  by rewrite opprK defX -big_cat sumR; apply: eq_big_perm.
have oXXc: '[X, Xc] = 0.
  have /span_orthogonal o_e_ec: orthogonal e ec.
    by move: o1R; rewrite -(eq_orthonormal defR) orthonormal_cat => /and3P[].
  by rewrite defX /Xc !big_seq o_e_ec ?rpredN ?rpred_sum // => xi /memv_span.
have{o_chi_chic} nXc: '[Xc] = '[chi^*].
  by apply: (addrI '[X]); rewrite -cfnormBd // nX def_XXc Itau // cfnormBd.
have{oXXc} oX2: pairwise_orthogonal X2.
  rewrite /pairwise_orthogonal /= oXXc eqxx !inE !(eq_sym 0) -!cfnorm_eq0.
  by rewrite nX nXc cfnorm_conjC cfnorm_eq0 orbb nz_chi.
have{nX nXc} nX2: map cfnorm X2 = map cfnorm S2 by congr [:: _; _].
have [|tau2 [tau2X tau2Xc] Itau2] := Zisometry_of_cfnorm oS2 oX2 nX2.
  apply/allP; rewrite /= defX De rpredN !big_seq.
  by rewrite !rpred_sum // => xi; rewrite mem_filter => /andP[_ /ZR].
have{Itau2} cohS2: coherent_with S2 L^# tau tau2.
  split=> // psi; rewrite zcharD1E => /andP[/zchar_expansion[//|z Zz ->]].
  rewrite big_cons big_seq1 !cfunE conj_Cnat ?Cnat_char1 ?N_S // addrC addr_eq0.
  rewrite -mulNr (inj_eq (mulIf _)) ?char1_eq0 ?N_S // => /eqP->.
  by rewrite scaleNr -scalerBr !raddfZ_Cint // raddfB /= tau2X tau2Xc -def_XXc.
have: tau beta = tau2 chi - tau1 (a *: phi) by rewrite tau2X raddfZ_Cint.
apply: (bridge_coherent sS20 cohS2 sS10 cohS1) => //.
  by apply/hasPn; rewrite has_sym !negb_or S1'chi (contra (ccS1 _)) ?cfConjCK.
by rewrite mem_head (zchar_on Zbeta) rpredZ_Cint ?mem_zchar.
Qed.

(* This is Peterfalvi (5.6): Feit's result that a coherent set can always be  *)
(* extended by a character whose degree is below a certain threshold.         *)
Lemma extend_coherent S1 xi1 chi :
    cfConjC_subset S1 S -> xi1 \in S1 -> chi \in S -> chi \notin S1 ->
    [/\ (*a*) coherent S1 L^# tau,
        (*b*) (xi1 1%g %| chi 1%g)%C
      & (*c*) 2%:R * chi 1%g * xi1 1%g < \sum_(xi <- S1) xi 1%g ^+ 2 / '[xi]] ->
  coherent (chi :: chi^*%CF :: S1) L^# tau.
Proof.
move=> ccsS1S S1xi1 Schi notS1chi [[tau1 cohS1] xi1_dv_chi1 ub_chi1].
have [[uS1 sS1S ccS1] [[Itau1 Ztau1] Dtau1]] := (ccsS1S, cohS1).
have{xi1_dv_chi1} [a Za chi1] := dvdCP _ _ xi1_dv_chi1.
have [[N_S nrS ccS] ZItau oS R_P oR] := cohS; have [Itau Ztau] := ZItau.
have [Sxi1 [ZRchi o1Rchi sumRchi]] := (sS1S _ S1xi1, R_P _ Schi).
have ocS1 xi: xi \in S1 -> '[chi, xi] = 0.
  by apply: orthoPl; rewrite orthogonal_sym subset_ortho_subcoherent.
have /andP[/memPn/=nzS _] := oS; have [Nchi nz_chi] := (N_S _ Schi, nzS _ Schi).
have oS1: pairwise_orthogonal S1 by apply: sub_pairwise_orthogonal oS.
have [freeS freeS1] := (orthogonal_free oS, orthogonal_free oS1).
have nz_nS1 xi: xi \in S1 -> '[xi] != 0 by rewrite cfnorm_eq0 => /sS1S/nzS.
have nz_xi11: xi1 1%g != 0 by rewrite char1_eq0 ?N_S ?nzS.
have inj_tau1: {in 'Z[S1] &, injective tau1} := Zisometry_inj Itau1.
have Z_S1: {subset S1 <= 'Z[S1]} by move=> xi /mem_zchar->.
have inj_tau1_S1: {in S1 &, injective tau1} := sub_in2 Z_S1 inj_tau1.
pose a_ t1xi := S1`_(index t1xi (map tau1 S1)) 1%g / xi1 1%g / '[t1xi].
have a_E xi: xi \in S1 -> a_ (tau1 xi) = xi 1%g / xi1 1%g / '[xi].
  by move=> S1xi; rewrite /a_ nth_index_map // Itau1 ?Z_S1.
have a_xi1 : a_ (tau1 xi1) = '[xi1]^-1 by rewrite a_E // -mulrA mulVKf //.
have Zachi: chi - a *: xi1 \in 'Z[S, L^#].
  by rewrite zcharD1E !cfunE -chi1 subrr rpredB ?scale_zchar ?mem_zchar /=.
have Ztau_achi := zcharW (Ztau _ Zachi).
have [X R_X [Y defXY]] := subcoherent_split Schi Ztau_achi.
have [eqXY oXY oYRchi] := defXY; pose X1 := map tau1 (in_tuple S1).
suffices defY: Y = a *: tau1 xi1.
  by move: eqXY; rewrite defY; apply: extend_coherent_with; rewrite -?defY.
have oX1: pairwise_orthogonal X1 by apply: map_pairwise_orthogonal.
have N_S1_1 xi: xi \in S1 -> xi 1%g \in Cnat by move/sS1S/N_S/Cnat_char1.
have oRchiX1 psi: psi \in 'Z[R chi] -> orthogonal psi X1.
  move/zchar_span=> Rpsi; apply/orthoPl=> chi2 /memv_span.
  by apply: span_orthogonal Rpsi; rewrite orthogonal_sym coherent_ortho_supp.
have [lam Zlam [Z oZS1 defY]]:
  exists2 lam, lam \in Cint & exists2 Z : 'CF(G), orthogonal Z (map tau1 S1) &
    Y = a *: tau1 xi1 - lam *: (\sum_(xi <- X1) a_ xi *: xi) + Z.
- pose lam := a * '[xi1] - '[Y, tau1 xi1]; exists lam.
    rewrite rpredD ?mulr_natl ?rpredN //.
      by rewrite rpredM // CintE Cnat_cfdot_char ?N_S.
    rewrite Cint_cfdot_vchar ?Ztau1 ?Z_S1 // -(subrK X Y) -opprB -eqXY addrC.
    by rewrite rpredB // (zchar_trans ZRchi).
  set Z' := _ - _; exists (Y - Z'); last by rewrite addrC subrK.
  have oXtau1 xi: xi \in S1 -> '[Y, tau1 xi] = - '[X - Y, tau1 xi].
    move=> S1xi; rewrite cfdotBl opprB.
    by rewrite (orthogonalP (oRchiX1 X R_X) X) ?subr0 ?mem_head ?map_f.
  apply/orthogonalP=> _ _ /predU1P[-> | //] /mapP[xi S1xi ->].
  rewrite !cfdotBl !cfdotZl Itau1 ?mem_zchar //.
  rewrite cfproj_sum_orthogonal ?map_f // a_E // Itau1 ?Z_S1 //.
  apply: (mulIf nz_xi11); rewrite divfK ?nz_nS1 // 2!mulrBl mulrA divfK //.
  rewrite mul0r mulrBl opprB -addrA addrCA addrC !addrA !oXtau1 // !mulNr.
  rewrite -(conj_Cnat (N_S1_1 _ S1xi)) -(conj_Cnat (N_S1_1 _ S1xi1)).
  rewrite opprK [- _ + _]addrC -!(mulrC _^*) -!cfdotZr -cfdotBr.
  rewrite -!raddfZ_Cnat ?N_S1_1 // -raddfB; set beta : 'CF(L) := _ - _.
  have Zbeta: beta \in 'Z[S1, L^#].
    rewrite zcharD1E !cfunE mulrC subrr eqxx.
    by rewrite rpredB ?rpredZ_Cint ?Z_S1 // CintE N_S1_1.
  rewrite -eqXY Dtau1 // Itau // ?(zchar_subset sS1S) //.
  rewrite cfdotBl !cfdotBr !cfdotZr !ocS1 // !mulr0 subrr add0r !cfdotZl.
  by rewrite opprB addrAC subrK subrr.
have [||leXchi _] := subcoherent_norm _ _ (erefl _) defXY.
- rewrite Schi scale_zchar ?char_vchar ?N_S /orthogonal //= !cfdotZr ocS1 //.
  by rewrite -[xi1]cfConjCK cfdot_conjC ocS1 ?ccS1 // conjC0 mulr0 eqxx.
- apply: sub_iso_to ZItau; [apply: zchar_trans_on; apply/allP | exact: zcharW].
  rewrite /= Zachi sub_aut_zchar ?zchar_onG ?mem_zchar ?ccS //.
  by move=> xi /N_S/char_vchar.
have normXY: '[X] + '[Y] = '[chi] + '[a *: xi1].
  by rewrite -!cfnormBd // ?cfdotZr ?ocS1 ?mulr0 // -eqXY Itau.
have{leXchi normXY}: '[Y] <= a ^+ 2 * '[xi1].
  by rewrite -(ler_add2l '[X]) normXY cfnormZ Cint_normK // ler_add2r.
rewrite {}defY cfnormDd; last first.
  rewrite cfdotC (span_orthogonal oZS1) ?rmorph0 ?memv_span1 //.
  rewrite big_seq memvB ?memvZ ?memv_suml ?memv_span ?map_f //.
  by move=> theta S1theta; rewrite memvZ ?memv_span.
rewrite -cfnormN opprB cfnormB !cfnormZ !Cint_normK // addrAC ler_subl_addl.
rewrite cfdotZl cfdotZr cfnorm_sum_orthogonal ?cfproj_sum_orthogonal ?map_f //.
rewrite a_xi1 Itau1 ?Z_S1 // addrAC ler_add2r !(divfK, mulrA) ?nz_nS1 //.
rewrite !conj_Cint ?rpredM // => /ler_gtF-lb_2_lam_a.
suffices lam0: lam = 0; last apply: contraFeq lb_2_lam_a => nz_lam.
  suffices ->: Z = 0 by rewrite lam0 scale0r subrK.
  by apply: contraFeq lb_2_lam_a; rewrite -cfnorm_gt0 lam0 expr0n !mul0r !add0r.
rewrite ltr_paddr ?cfnorm_ge0 // -mulr2n -mulr_natl mulrCA.
have xi11_gt0: xi1 1%g > 0 by rewrite char1_gt0 ?N_S ?sS1S -?cfnorm_eq0 ?nz_nS1.
have a_gt0: a > 0 by rewrite -(ltr_pmul2r xi11_gt0) mul0r -chi1 char1_gt0.
apply: ler_lt_trans (_ : lam ^+ 2 * (2%:R * a) < _).
  by rewrite ler_pmul2r ?mulr_gt0 ?ltr0n ?Cint_ler_sqr.
rewrite ltr_pmul2l ?(ltr_le_trans ltr01) ?sqr_Cint_ge1 {lam Zlam nz_lam}//.
rewrite -(ltr_pmul2r xi11_gt0) -mulrA -chi1 -(ltr_pmul2r xi11_gt0).
congr (_ < _): ub_chi1; rewrite -mulrA -expr2 mulr_suml big_map.
apply/eq_big_seq=> xi S1xi; rewrite a_E // Itau1 ?mem_zchar //.
rewrite ger0_norm ?divr_ge0 ?cfnorm_ge0 ?char1_ge0 ?N_S ?sS1S //.
rewrite [_ / _ / _]mulrAC [RHS]mulrAC -exprMn divfK //.
by rewrite [RHS]mulrAC divfK ?nz_nS1 // mulrA.
Qed.

(* This is Peterfalvi (5.7). *)
(* This is almost a superset of (1.4): we could use it to get a coherent      *)
(* isometry, which would necessarily map irreducibles to signed irreducibles. *)
(* It would then only remain to show that the signs are chosen consistently,  *)
(* by considering the degrees of the differences.                             *)
(*   This result is complementary to (5.6): it follow from it when S has 4 or *)
(* fewer characters, or reducible characters. On the contrary, (5.7) can be   *)
(* used to provide an initial set of characters with a threshold high enough  *)
(* to enable (repeated) application of (5.6), as in seqIndD_irr_coherence.    *)
Lemma uniform_degree_coherence :
  constant [seq chi 1%g | chi : 'CF(L) <- S] -> coherent S L^# tau.
Proof.
case defS: {1}S => /= [|chi1 S1] szS; first by rewrite defS; apply nil_coherent.
have{szS} unifS xi: xi \in S -> xi 1%g = chi1 1%g.
  by rewrite defS => /predU1P[-> // | S'xi]; apply/eqP/(allP szS)/map_f.
have{S1 defS} Schi1: chi1 \in S by rewrite defS mem_head.
have [[N_S nrS ccS] IZtau oS R_P oR] := cohS; have [Itau Ztau] := IZtau.
have Zd: {in S &, forall xi1 xi2, xi1 - xi2 \in 'Z[S, L^#]}.
  move=> xi1 xi2 Sxi1 Sxi2 /=.
  by rewrite zcharD1E rpredB ?mem_zchar //= !cfunE !unifS ?subrr.
pose chi2 := chi1^*%CF; have Schi2: chi2 \in S by rewrite ccS.
have ch1'2: chi2 != chi1 by apply/(hasPn nrS).
have [_ oSS] := pairwise_orthogonalP oS.
pose S1 xi := [predD1 S & xi]; pose S2 xi := [predD1 (S1 xi) & xi^*%CF].
have{oR} oR xi1 xi2: xi1 \in S -> xi2 \in S2 xi1 -> orthogonal (R xi1) (R xi2).
  move=> Sxi1 /and3P[/= xi1J'2 xi1'2 Sxi2].
  by rewrite orthogonal_sym oR // /orthogonal /= !oSS ?eqxx // ccS.
have oSc xi: xi \in S -> '[xi, xi^*] = 0.
  by move=> Sxi; rewrite oSS ?ccS // eq_sym (hasPn nrS).
pose D xi := tau (chi1 - xi).
have Z_D xi: xi \in S -> D xi \in 'Z[irr G] by move/(Zd _ _ Schi1)/Ztau/zcharW.
have /CnatP[N defN]: '[chi1] \in Cnat by rewrite Cnat_cfdot_char ?N_S.
have dotD: {in S1 chi1 &, forall xi1 xi2, '[D xi1, D xi2] = N%:R + '[xi1, xi2]}.
  move=> xi1 xi2 /andP[ch1'xi1 Sxi1] /andP[chi1'xi2 Sxi2].
  rewrite Itau ?Zd // cfdotBl !cfdotBr defN.
  by rewrite 2?oSS // 1?eq_sym // opprB !subr0.
have /R_P[ZRchi oRchi defRchi] := Schi1.
have szRchi: size (R chi1) = (N + N)%N.
  apply: (can_inj natCK); rewrite -cfnorm_orthonormal // -defRchi.
  by rewrite dotD ?inE ?ccS ?(hasPn nrS) // cfnorm_conjC defN -natrD.
pose subRchi1 X := exists2 E, subseq E (R chi1) & X = \sum_(a <- E) a.
pose Xspec X := [/\ X \in 'Z[R chi1], '[X] = N%:R & subRchi1 X].
pose Xi_spec (X : 'CF(G)) xi := X - D xi \in 'Z[R xi] /\ '[X, D xi] = N%:R.
have haveX xi: xi \in S2 chi1 -> exists2 X, Xspec X & Xi_spec X xi.
  move=> S2xi; have /and3P[/= chi2'xi ch1'xi Sxi] := S2xi.
  have [neq_xi' Sxi'] := (hasPn nrS xi Sxi, ccS xi Sxi).
  have [X RchiX [Y1 defXY1]] := subcoherent_split Schi1 (Z_D _ Sxi).
  have [[eqXY1 oXY1 oY1chi] sRchiX] := (defXY1, zchar_span RchiX).
  have Z_Y1: Y1 \in 'Z[irr G].
    by rewrite -rpredN -(rpredDl _ (zchar_trans ZRchi RchiX)) -eqXY1 Z_D.
  have [X1 RxiX1 [Y defX1Y]] := subcoherent_split Sxi Z_Y1.
  have [[eqX1Y oX1Y oYxi] sRxiX1] := (defX1Y, zchar_span RxiX1).
  pose Y2 : 'CF(G) := X + Y; pose D2 : 'CF(G) := tau (xi - chi1).
  have oY2Rxi: orthogonal Y2 (R xi).
    apply/orthoPl=> phi Rxi_phi; rewrite cfdotDl (orthoPl oYxi) // addr0.
    by rewrite (span_orthogonal (oR chi1 xi _ _)) // memv_span.
  have{oY2Rxi} defX1Y2: [/\ D2 = X1 - Y2, '[X1, Y2] = 0 & orthogonal Y2 (R xi)].
    rewrite -opprB -addrA -opprB -eqX1Y -eqXY1 -linearN opprB cfdotC.
    by rewrite (span_orthogonal oY2Rxi) ?conjC0 ?memv_span1 ?(zchar_span RxiX1).
  have [||minX eqX1] := subcoherent_norm _ _ (erefl _) defXY1.
  - by rewrite char_vchar ?N_S /orthogonal //= !oSS ?eqxx // eq_sym.
  - apply: sub_iso_to IZtau; last exact: zcharW.
    by apply: zchar_trans_on; apply/allP; rewrite /= !Zd.
  have [||minX1 _]:= subcoherent_norm _ _ (erefl _) defX1Y2.
  - rewrite char_vchar ?N_S /orthogonal //= !oSS ?eqxx // inv_eq //.
    exact: cfConjCK.
  - apply: sub_iso_to IZtau; last exact: zcharW.
    by apply: zchar_trans_on; apply/allP; rewrite /= !Zd.
  rewrite eqX1Y cfnormBd // defN in eqX1.
  have{eqX1} [|nX n_xi defX] := eqX1; first by rewrite ler_paddr ?cfnorm_ge0.
  exists X => //; split; last by rewrite eqXY1 cfdotBr oXY1 subr0.
  suffices Y0: Y = 0 by rewrite eqXY1 eqX1Y Y0 subr0 opprB addrC subrK.
  apply/eqP; rewrite -cfnorm_eq0 lerif_le ?cfnorm_ge0 //.
  by rewrite -(ler_add2l '[X1]) addr0 n_xi.
pose XDspec X := {in S2 chi1, forall xi, '[X, D xi] = N%:R}.
have [X [RchiX nX defX] XD_N]: exists2 X, Xspec X & XDspec X.
  have [sSchi | /allPn[xi1 Sxi1]] := altP (@allP _ (pred2 chi1 chi2) S).
    pose E := take N (R chi1).
    exists (\sum_(a <- E) a) => [|xi]; last by case/and3P=> ? ? /sSchi/norP[].
    have defE: E ++ drop N (R chi1) = R chi1 by rewrite cat_take_drop.
    have sER: subseq E (R chi1) by rewrite -defE prefix_subseq.
    split; last by [exists E]; move/mem_subseq in sER.
      by rewrite big_seq rpred_sum // => a Ea; rewrite mem_zchar ?sER.
    rewrite cfnorm_orthonormal ?size_takel ?szRchi ?leq_addl //.
    by have:= oRchi; rewrite -defE orthonormal_cat => /andP[].
  case/norP=> chi1'xi1 chi2'xi1'; have S2xi1: xi1 \in S2 chi1 by apply/and3P.
  pose xi2 := xi1^*%CF; have /haveX[X [RchiX nX defX] [Rxi1X1 XD_N]] := S2xi1.
  exists X => // xi S2xi; have [chi1'xi chi2'xi /= Sxi] := and3P S2xi.
  have /R_P[_ _ defRxi1] := Sxi1; have [-> // | xi1'xi] := eqVneq xi xi1.
  have [sRchiX sRxi1X1] := (zchar_span RchiX, zchar_span Rxi1X1).
  have [-> | xi2'xi] := eqVneq xi xi2.
    rewrite /D -[chi1](subrK xi1) -addrA linearD cfdotDr XD_N defRxi1 big_seq.
    rewrite (span_orthogonal (oR chi1 xi1 _ _)) ?addr0 ?rpred_sum //.
    exact/memv_span.
  have /haveX[X' [RchiX' nX' _] [Rxi3X' X'D_N]] := S2xi.
  have [sRchiX' sRxi1X'] := (zchar_span RchiX', zchar_span Rxi3X').
  suffices: '[X - X'] == 0 by rewrite cfnorm_eq0 subr_eq0 => /eqP->.
  have ZXX': '[X, X'] \in Cint by rewrite Cint_cfdot_vchar ?(zchar_trans ZRchi).
  rewrite cfnormB subr_eq0 nX nX' aut_Cint {ZXX'}//; apply/eqP/esym.
  congr (_ *+ 2); rewrite -(addNKr (X - D xi1) X) cfdotDl cfdotC.
  rewrite (span_orthogonal (oR chi1 xi1 _ _)) // conjC0.
  rewrite -(subrK (D xi) X') cfdotDr cfdotDl cfdotNl opprB subrK.
  rewrite (span_orthogonal (oR xi1 xi _ _)) //; last exact/and3P.
  rewrite (span_orthogonal (oR chi1 xi _ _)) // oppr0 !add0r.
  by rewrite dotD ?oSS ?addr0 1?eq_sym //; apply/andP.
have{RchiX} ZX: X \in 'Z[irr G] := zchar_trans ZRchi RchiX.
apply: (pivot_coherence cohS Schi1 ZX); rewrite defN //.
move=> xi /andP[chi1'xi Sxi]; exists 1; first by rewrite rpred1 mul1r unifS.
rewrite scale1r mulN1r -conjC_nat -opprB raddfN cfdotNl cfdotC; congr (- _^*).
have [-> /= | chi2'xi] := eqVneq xi chi2; last exact/XD_N/and3P.
have{defX}[E ssER defX] := defX; pose Ec := filter [predC E] (R chi1).
have eqRchi: perm_eq (R chi1) (E ++ Ec).
  rewrite -(perm_filterC (mem E)) -(subseq_uniqP _ _) //.
  exact/free_uniq/orthonormal_free.
have /and3P[oE _ oEEc]: [&& orthonormal E, orthonormal Ec & orthogonal E Ec].
  by rewrite (eq_orthonormal eqRchi) orthonormal_cat in oRchi.
rewrite defRchi (eq_big_perm _ eqRchi) big_cat -defX cfdotDr nX defX !big_seq.
by rewrite (span_orthogonal oEEc) ?addr0 ?rpred_sum //; apply: memv_span.
Qed.

End SubCoherentProperties.

(* A corollary of Peterfalvi (5.7) used (sometimes implicitly!) in the proof  *)
(* of lemmas (11.9), (12.4) and (12.5).                                       *)
Lemma pair_degree_coherence L G S (tau : {linear _ -> 'CF(gval G)}) R :
    subcoherent S tau R ->
  {in S &, forall phi1 phi2 : 'CF(gval L), phi1 1%g == phi2 1%g ->
   exists S1 : seq 'CF(L),
     [/\ phi1 \in S1, phi2 \in S1, cfConjC_subset S1 S & coherent S1 L^# tau]}.
Proof.
move=> scohS phi1 phi2 Sphi1 Sphi2 /= eq_phi12_1.
have [[N_S _ ccS] _ _ _ _] := scohS.
pose S1 := undup (phi1 :: phi1^* :: phi2 :: phi2^*)%CF.
have sS1S: cfConjC_subset S1 S.
  split=> [|chi|chi]; rewrite ?undup_uniq //= !mem_undup; move: chi; apply/allP.
    by rewrite /= !ccS ?Sphi1 ?Sphi2.
  by rewrite /= !inE !cfConjCK !eqxx !orbT.
exists S1; rewrite !mem_undup !inE !eqxx !orbT; split=> //.
apply: uniform_degree_coherence (subset_subcoherent scohS sS1S) _.
apply/(@all_pred1_constant _ (phi2 1%g))/allP=> _ /mapP[chi S1chi ->] /=.
rewrite mem_undup in S1chi; move: chi S1chi; apply/allP.
by rewrite /= !cfAut_char1 ?N_S // eqxx eq_phi12_1.
Qed.

(* This is Peterfalvi (5.8). *)
Lemma coherent_prDade_TIred (G H L K W W1 W2 : {group gT}) S A A0
                            k (tau1 : {additive 'CF(L) -> 'CF(G)})
    (defW : W1 \x W2 = W) (ddA : prime_Dade_hypothesis G L K H A A0 defW)
    (sigma := cyclicTIiso ddA)
    (eta_ := fun i j => sigma (cyclicTIirr defW i j))
    (mu := primeTIred ddA) (dk := primeTIsign ddA k) (tau := Dade ddA) :
  cfConjC_subset S (seqIndD K L H 1) ->
  [/\ ~~ has cfReal S, has (mem (irr L)) S & mu k \in S] ->
  coherent_with S L^# tau tau1 ->
  let j := conjC_Iirr k in
     tau1 (mu k) = dk *: (\sum_i eta_ i k)
  \/ tau1 (mu k) = - dk *: (\sum_i eta_ i j)
  /\ (forall ell, mu ell \in S -> mu ell 1%g = mu k 1%g -> ell = k \/ ell = j).
Proof.
set phi := tau1 (mu k) => uccS [nrS /hasP[zeta Szeta irr_zeta] Sk] cohS j.
pose sum_eta a ell := \sum_i a i ell *: eta_ i ell.
have [R [subcohS oS1sig defR]] := prDade_subcoherent ddA uccS nrS.
have [[charS _ ccS] _ /orthogonal_free freeS Rok _] := subcohS.
have [[Itau1 _] Dtau1] := cohS.
have natS1 xi: xi \in S -> xi 1%g \in Cnat by move/charS/Cnat_char1.
have k'j: j != k by rewrite -(inj_eq (prTIred_inj ddA)) prTIred_aut (hasPn nrS).
have nzSmu l (Sl : mu l \in S): l != 0.
  apply: contraNneq (hasPn nrS _ Sl) => ->.
  by rewrite /cfReal -prTIred_aut aut_Iirr0.
have [nzk nzj]: k != 0 /\ j != 0 by rewrite !nzSmu // /mu (prTIred_aut ddA) ccS.
have sSS: cfConjC_subset S S by have:= free_uniq freeS; split.
have{sSS} Dtau1S:= mem_coherent_sum_subseq subcohS sSS cohS.
have o_sum_eta a j1 i j2: j1 != j2 -> '[sum_eta a j1, eta_ i j2] = 0.
  move/negPf=> neq_j; rewrite cfdot_suml big1 // => i1 _.
  by rewrite cfdotZl cfdot_cycTIiso neq_j andbF mulr0.
have proj_sum_eta a i j1: '[sum_eta a j1, eta_ i j1] = a i j1.
  rewrite cfdot_suml (bigD1 i) //= cfdotZl cfdot_cycTIiso !eqxx mulr1.
  rewrite big1 ?addr0 // => i1 /negPf i'i1.
  by rewrite cfdotZl cfdot_cycTIiso i'i1 mulr0.
have [a Dphi Da0]: exists2 a, phi = sum_eta a k + sum_eta a j
  & pred2 0 dk (a 0 k) /\ pred2 0 (- dk) (a 0 j).
- have uRk: uniq (R (mu k)) by have [_ /orthonormal_free/free_uniq] := Rok _ Sk.
  have [E sER Dphi] := Dtau1S _ Sk; rewrite /phi Dphi (subseq_uniqP uRk sER).
  pose a i ell (alpha := dk *: eta_ i ell) :=
    if alpha \in E then dk else if - alpha \in E then - dk else 0.
  have sign_eq := inj_eq (can_inj (signrZK _)).
  have E'Nsk i: (- (dk *: eta_ i k) \in E) = false.
    apply/idP=> /(mem_subseq sER); rewrite defR -/dk -/sigma mem_cat -map_comp.
    case/orP=> /codomP[i1 /esym/eqP/idPn[]].
      by rewrite -scalerN sign_eq cycTIiso_neqN.
    by rewrite (inj_eq oppr_inj) sign_eq cycTIiso_eqE (negPf k'j) andbF.
  have E'sj i: (dk *: eta_ i j \in E) = false.
    apply/idP=> /(mem_subseq sER); rewrite defR -/dk -/sigma mem_cat -map_comp.
    case/orP=> /codomP[i1 /eqP/idPn[]].
      by rewrite sign_eq cycTIiso_eqE (negPf k'j) andbF.
    by rewrite /= -scalerN sign_eq cycTIiso_neqN.
  exists a; last first.
    by rewrite !(fun_if (pred2 _ _)) /= !eqxx !orbT E'Nsk !(if_same, E'sj).
  rewrite big_filter big_mkcond defR big_cat !big_map -/dk -/sigma /=.
  congr (_ + _); apply: eq_bigr => i _; rewrite /a -/(eta_ i _).
    by rewrite E'Nsk; case: ifP => // _; rewrite scale0r.
  by rewrite E'sj; case: ifP => _; rewrite (scaleNr, scale0r).
pose V := cyclicTIset defW; have zetaV0: {in V, tau1 zeta =1 \0}.
  apply: (ortho_cycTIiso_vanish ddA); apply/orthoPl=> _ /mapP[ww Www ->].
  rewrite (span_orthogonal (oS1sig zeta ww _ _)) ?memv_span1 ?inE ?Szeta //.
  have [E sER ->] := Dtau1S _ Szeta; rewrite big_seq rpred_sum // => aa Raa.
  by rewrite memv_span ?(mem_subseq sER).
pose zeta1 := zeta 1%g *: mu k - mu k 1%g *: zeta.
have Zzeta1: zeta1 \in 'Z[S, L^#].
  rewrite zcharD1E !cfunE mulrC subrr eqxx andbT.
  by rewrite rpredB ?scale_zchar ?mem_zchar // CintE ?natS1.
have /cfun_onP A1zeta1: zeta1 \in 'CF(L, 1%g |: A).
  rewrite memvB ?memvZ ?prDade_TIred_on //; have [_ sSS0 _] := uccS.
  have /seqIndP[kz /setIdP[kerH'kz _] Dzeta] := sSS0 _ Szeta.
  by rewrite Dzeta (prDade_Ind_irr_on ddA) //; rewrite inE in kerH'kz.
have{A1zeta1} zeta1V0: {in V, zeta1 =1 \0}.
  move=> x Vx; rewrite /= A1zeta1 // -in_setC.
  apply: subsetP (subsetP (prDade_supp_disjoint ddA) x Vx); rewrite setCS.
  by rewrite subUset sub1G; have [/= _ _ _ [_ [_ _ /subsetD1P[->]]]] := ddA.
have o_phi_0 i: '[phi, eta_ i 0] = 0 by rewrite Dphi cfdotDl !o_sum_eta ?addr0.
have{o_phi_0 zeta1V0} proj_phi0 i ell: '[phi, eta_ i ell] = '[phi, eta_ 0 ell].
  rewrite -[LHS]add0r -(o_phi_0 0) -[RHS]addr0 -(o_phi_0 i).
  apply: (cycTIiso_cfdot_exchange ddA); rewrite -/V => x Vx.
  have: tau zeta1 x == 0.
    have [_ _ defA0] := prDade_def ddA; rewrite Dade_id ?zeta1V0 //.
    by rewrite defA0 inE orbC mem_class_support.
  rewrite -Dtau1 // raddfB !raddfZ_Cnat ?natS1 // !cfunE zetaV0 //.
  rewrite oppr0 mulr0 addr0 mulf_eq0 => /orP[/idPn[] | /eqP->//].
  by have /irrP[iz ->] := irr_zeta; apply: irr1_neq0.
have Dphi_j i: '[phi, eta_ i j] = a i j.
  by rewrite Dphi cfdotDl proj_sum_eta o_sum_eta 1?eq_sym ?add0r.
have Dphi_k i: '[phi, eta_ i k] = a i k.
  by rewrite Dphi cfdotDl proj_sum_eta o_sum_eta ?addr0.
have Da_j i: a i j = a 0 j by rewrite -!Dphi_j.
have{proj_phi0} Da_k i: a i k = a 0 k by rewrite -!Dphi_k.
have oW1: #|W1| = #|Iirr W1|.
  by rewrite card_Iirr_cyclic //; have [[]] := prDade_prTI ddA.
have{oW1}: `|a 0 j| ^+ 2 + `|a 0 k| ^+ 2 == 1.
  apply/eqP/(mulfI (neq0CG W1)); rewrite mulr1 {}[in LHS]oW1.
  transitivity '[phi]; last by rewrite Itau1 ?mem_zchar ?cfnorm_prTIred.
  rewrite {2}Dphi cfdotDr !cfdot_sumr mulrDr addrC !mulr_natl -!sumr_const.
  congr (_ + _); apply: eq_bigr => i _; rewrite cfdotZr mulrC normCK.
    by rewrite Dphi_k (Da_k i).
  by rewrite Dphi_j (Da_j i).
have{Da0}[/pred2P[]Da0k /pred2P[]Da0j] := Da0; rewrite Da0k Da0j; last 2 first.
- left; rewrite Dphi [sum_eta a j]big1 ?addr0 => [|i _]; last first.
    by rewrite Da_j Da0j scale0r.
  by rewrite scaler_sumr; apply: eq_bigr => i _; rewrite Da_k Da0k.
- by rewrite normrN normr_sign expr1n (eqr_nat _ 2 1).
- by rewrite normr0 expr0n add0r (eqr_nat _ 0 1).
have{Dphi} Dphi: phi = - dk *: (\sum_i eta_ i j).
  rewrite Dphi [sum_eta a k]big1 ?add0r => [|i _]; last first.
    by rewrite Da_k Da0k scale0r.
  by rewrite raddf_sum; apply: eq_bigr => i _; rewrite Da_j Da0j.
clear 1; right; split=> // l Sl deg_l; apply/pred2P.
have [_ [tau2 Dtau2 [_ Dtau]]] := uniform_prTIred_coherent ddA nzk.
have nz_l: l != 0 := nzSmu l Sl.
have Tmukl: mu k - mu l \in 'Z[uniform_prTIred_seq ddA k, L^#].
  rewrite zcharD1E !cfunE deg_l subrr eqxx andbT.
  by rewrite rpredB ?mem_zchar ?image_f // !inE ?nzk ?nz_l ?deg_l eqxx.
pose ak (_ : Iirr W1) (_ : Iirr W2) := dk.
have: phi - tau1 (mu l) = sum_eta ak k - sum_eta ak l.
  rewrite -raddfB Dtau1; last first.
    by rewrite zcharD1E rpredB ?mem_zchar //= !cfunE deg_l subrr.
  by rewrite -[tau _]Dtau // raddfB /= !Dtau2 2!raddf_sum.
have [E /mem_subseq sER ->] := Dtau1S _ Sl.
move/esym/(congr1 (cfdotr (eta_ 0 k))); apply: contra_eqT => /norP[k'l j'l] /=.
rewrite !cfdotBl Dphi_k Da0k proj_sum_eta o_sum_eta // cfdot_suml.
rewrite big_seq big1 ?subr0 ?signr_eq0 // => aa /sER; rewrite defR -map_comp.
rewrite mem_cat => /orP[]/codomP[/= i ->]; rewrite -/(eta_ i _).
  by rewrite cfdotZl cfdot_cycTIiso (negPf k'l) andbF mulr0.
rewrite cfdotNl cfdotZl cfdot_cycTIiso (inv_eq (@conjC_IirrK _ _)) -/j.
by rewrite (negPf j'l) andbF mulr0 oppr0.
Qed.

Section DadeAut.

Variables (L G : {group gT}) (A : {set gT}).
Implicit Types K H M : {group gT}.
Hypothesis ddA : Dade_hypothesis G L A.

Local Notation tau := (Dade ddA).
Local Notation "alpha ^\tau" := (tau alpha).

Section DadeAutIrr.
Variable u : {rmorphism algC -> algC}.
Local Notation "alpha ^u" := (cfAut u alpha).

(* This is Peterfalvi (5.9)(a), slightly reformulated to allow calS to also   *)
(* contain non-irreducible characters; for groups of odd order, the second    *)
(* assumption holds uniformly for all calS of the form seqIndD.               *)
(* We have stated the coherence assumption directly over L^#; this lets us    *)
(* drop the Z[S, A] = Z[S, L^#] assumption, and is more consistent with the   *)
(* rest of the proof.                                                         *)
Lemma cfAut_Dade_coherent calS tau1 chi : 
    coherent_with calS L^# tau tau1 ->
    (1 < #|[set i | 'chi_i \in calS]|)%N /\ cfAut_closed u calS ->
    chi \in irr L -> chi \in calS ->
  (tau1 chi)^u = tau1 (chi^u).
Proof.
case=> [[Itau1 Ztau1] tau1_tau] [irrS_gt1 sSuS] /irrP[i {chi}->] Schi.
have sSZS: {subset calS <= 'Z[calS]} by move=> phi Sphi; apply: mem_zchar.
pose mu j := 'chi_j 1%g *: 'chi_i - 'chi_i 1%g *: 'chi_j.
have ZAmu j: 'chi_j \in calS -> mu j \in 'Z[calS, L^#].
  move=> Sxj; rewrite zcharD1E !cfunE mulrC subrr.
  by rewrite rpredB //= scale_zchar ?sSZS // ?Cint_Cnat ?Cnat_irr1.
have Npsi j: 'chi_j \in calS -> '[tau1 'chi_j] = 1%:R.
  by move=> Sxj; rewrite Itau1 ?sSZS ?cfnorm_irr.
have{Npsi} Dtau1 Sxj := vchar_norm1P (Ztau1 _ (sSZS _ Sxj)) (Npsi _ Sxj).
have [e [r tau1_chi]] := Dtau1 _ Schi; set eps := (-1) ^+ e in tau1_chi.
have{Dtau1} Dtau1 j: 'chi_j \in calS -> exists t, tau1 'chi_j = eps *: 'chi_t.
  move=> Sxj; suffices: 0 <= (eps *: tau1 'chi_j) 1%g.
    have [f [t ->]] := Dtau1 j Sxj.
    have [-> | neq_f_eps] := eqVneq f e; first by exists t.
    rewrite scalerA -signr_addb scaler_sign addbC -negb_eqb neq_f_eps.
    by rewrite cfunE oppr_ge0 ltr_geF ?irr1_gt0.
  rewrite -(pmulr_rge0 _ (irr1_gt0 i)) cfunE mulrCA.
  have: tau1 (mu j) 1%g == 0 by rewrite tau1_tau ?ZAmu ?Dade1.
  rewrite raddfB 2?raddfZ_Cnat ?Cnat_irr1 // !cfunE subr_eq0 => /eqP <-.
  by rewrite tau1_chi cfunE mulrCA signrMK mulr_ge0 ?Cnat_ge0 ?Cnat_irr1.
have SuSirr j: 'chi_j \in calS -> 'chi_(aut_Iirr u j) \in calS.
  by rewrite aut_IirrE => /sSuS.
have [j Sxj neq_ij]: exists2 j, 'chi_j \in calS & 'chi_i != 'chi_j.
  move: irrS_gt1; rewrite (cardsD1 i) inE Schi ltnS card_gt0 => /set0Pn[j].
  by rewrite !inE -(inj_eq irr_inj) eq_sym => /andP[]; exists j.
have: (tau1 (mu j))^u == tau1 (mu j)^u.
  by rewrite !tau1_tau ?cfAut_zchar ?ZAmu ?Dade_aut.
rewrite !raddfB [-%R]lock !raddfZ_Cnat ?Cnat_irr1 //= -lock -!aut_IirrE.
have [/Dtau1[ru ->] /Dtau1[tu ->]] := (SuSirr i Schi, SuSirr j Sxj).
have: (tau1 'chi_i)^u != (tau1 'chi_j)^u.
  apply: contraNneq neq_ij => /cfAut_inj/(isometry_raddf_inj Itau1)/eqP.
  by apply; rewrite ?sSZS //; apply: rpredB.
have /Dtau1[t ->] := Sxj; rewrite tau1_chi !cfAutZ_Cint ?rpred_sign //.
rewrite !scalerA -!(mulrC eps) -!scalerA -!scalerBr -!aut_IirrE.
rewrite !(inj_eq (scalerI _)) ?signr_eq0 // (inj_eq irr_inj) => /negPf neq_urt.
have [/CnatP[a ->] /CnatP[b xj1]] := (Cnat_irr1 i, Cnat_irr1 j).
rewrite xj1 eq_subZnat_irr neq_urt orbF andbC => /andP[_].
by rewrite eqn0Ngt -ltC_nat -xj1 irr1_gt0 /= => /eqP->.
Qed.

End DadeAutIrr.

(* This covers all the uses of (5.9)(a) in the rest of Peterfalvi, except     *)
(* one instance in (6.8.2.1).                                                 *)
Lemma cfConjC_Dade_coherent K H M (calS := seqIndD K L H M) tau1 chi :
    coherent_with calS L^# (Dade ddA) tau1 ->
    [/\ odd #|G|, K <| L & H \subset K] -> chi \in irr L -> chi \in calS ->
  (tau1 chi)^*%CF = tau1 chi^*%CF.
Proof.
move=> cohS [oddG nsKL sHK] irr_chi Schi.
apply: (cfAut_Dade_coherent cohS) => //; split; last exact: cfAut_seqInd.
have oddL: odd #|L| by apply: oddSg oddG; have [_] := ddA.
exact: seqInd_nontrivial_irr Schi.
Qed.

(* This is Peterfalvi (5.9)(b). *)
Lemma Dade_irr_sub_conjC chi (phi := chi - chi^*%CF) :
    chi \in irr L -> chi \in 'CF(L, 1%g |: A) ->
  exists t, phi^\tau = 'chi_t - ('chi_t)^*%CF.
Proof.
case/irrP=> i Dchi Achi; rewrite {chi}Dchi in phi Achi *.
have [Rchi | notRchi] := eqVneq (conjC_Iirr i) i.
  by exists 0; rewrite irr0 cfConjC_cfun1 /phi -conjC_IirrE Rchi !subrr linear0.
have Zphi: phi \in 'Z[irr L, A].
  have notA1: 1%g \notin A by have [] := ddA.
  by rewrite -(setU1K notA1) sub_conjC_vchar // zchar_split irr_vchar.
have Zphi_tau: phi^\tau \in 'Z[irr G, G^#].
  by rewrite zchar_split Dade_cfun Dade_vchar ?Zphi.
have norm_phi_tau : '[phi^\tau] = 2%:R.
  rewrite Dade_isometry ?(zchar_on Zphi) // cfnormB -conjC_IirrE.
  by rewrite !cfdot_irr !eqxx eq_sym (negPf notRchi) rmorph0 addr0 subr0.
have [j [k ne_kj phi_tau]] := vchar_norm2 Zphi_tau norm_phi_tau.
suffices def_k: conjC_Iirr j = k by exists j; rewrite -conjC_IirrE def_k.
have/esym:= eq_subZnat_irr 1 1 k j (conjC_Iirr j) (conjC_Iirr k).
rewrite (negPf ne_kj) orbF /= !scale1r !conjC_IirrE -rmorphB.
rewrite -opprB -phi_tau /= -Dade_conjC // rmorphB /= cfConjCK.
by rewrite -linearN opprB eqxx => /andP[/eqP->].
Qed.

End DadeAut.

End Five.

Arguments coherent_prDade_TIred
  [gT G H L K W W1 W2 S0 A A0 k tau1 defW].
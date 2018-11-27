(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrfun ssrbool eqtype ssrnat seq path choice fintype.
From mathcomp
Require Import bigop finset fingroup morphism automorphism quotient action.
From mathcomp
Require Import gseries.

(******************************************************************************)
(* This files establishes Jordan-Holder theorems for finite groups. These     *)
(* theorems state the uniqueness up to permutation and isomorphism for the    *)
(* series of quotient built from the successive elements of any composition   *)
(* series of the same group. These quotients are also called factors of the   *)
(* composition series. To avoid the heavy use of highly polymorphic lists     *)
(* describing these quotient series, we introduce sections.                   *)
(* This library defines:                                                      *)
(*         (G1 / G2)%sec == alias for the pair (G1, G2) of groups in the same *)
(*                          finGroupType, coerced to the actual quotient group*)
(*                          group G1 / G2. We call this pseudo-quotient a     *)
(*                          section of G1 and G2.                             *)
(*    section_isog s1 s2 == s1 and s2 respectively coerce to isomorphic       *)
(*                          quotient groups.                                  *)
(*        section_repr s == canonical representative of the isomorphism class *)
(*                          of the section s.                                 *)
(*         mksrepr G1 G2 == canonical representative of the isomorphism class *)
(*                          of (G1 / G2)%sec.                                 *)
(*         mkfactors G s == if s is [:: s1, s2, ..., sn], constructs the list *)
(*                     [:: mksrepr G s1, mksrepr s1 s2, ..., mksrepr sn-1 sn] *)
(*             comps G s == s is a composition series for G i.e. s is a       *)
(*                          decreasing sequence of subgroups of G             *)
(*                          in which two adjacent elements are maxnormal one  *)
(*                          in the other and the last element of s is 1.      *)
(* Given aT and rT two finGroupTypes, (D : {group rT}), (A : {group aT}) and  *)
(* (to : groupAction A D) an external action.                                 *)
(*        maxainv to B C == C is a maximal proper normal subgroup of B        *)
(*                          invariant by (the external action of A via) to.   *)
(*          asimple to B == the maximal proper normal subgroup of B invariant *)
(*                          by the external action to is trivial.             *)
(*         acomps to G s == s is a composition series for G invariant by to,  *)
(*                          i.e. s is a decreasing sequence of subgroups of G *)
(*                          in which two adjacent elements are maximally      *)
(*                          invariant by to one in the other and the          *)
(*                          last element of s is 1.                           *)
(* We prove two versions of the result:                                       *)
(*    - JordanHolderUniqueness establishes the uniqueness up to permutation   *)
(*       and isomorphism of the lists of factors in composition series of a   *)
(*       given group.                                                         *)
(*    - StrongJordanHolderUniqueness extends the result to composition series *)
(*       invariant by an external group action.                               *)
(* See also "The Rooster and the Butterflies", proceedings of Calculemus 2013,*)
(* by Assia Mahboubi.                                                         *)
(******************************************************************************)


Import GroupScope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive section (gT : finGroupType) := GSection of {group gT} * {group gT}.

Delimit Scope section_scope with sec.
Bind Scope section_scope with section.

Definition mkSec (gT : finGroupType) (G1 G2 : {group gT}) := GSection (G1, G2).

Infix "/" := mkSec : section_scope.

Coercion pair_of_section gT (s : section gT) := let: GSection u := s in u.

Coercion quotient_of_section gT (s : section gT) : GroupSet.sort _ := s.1 / s.2.

Coercion section_group gT (s : section gT) : {group (coset_of s.2)} :=
  Eval hnf in [group of s].

Section Sections.

Variables (gT : finGroupType).
Implicit Types (G : {group gT}) (s : section gT).

Canonical section_subType := Eval hnf in [newType for @pair_of_section gT].
Definition section_eqMixin := Eval hnf in [eqMixin of section gT by <:].
Canonical section_eqType := Eval hnf in EqType (section gT) section_eqMixin.
Definition section_choiceMixin := [choiceMixin of section gT by <:].
Canonical section_choiceType :=
  Eval hnf in ChoiceType (section gT) section_choiceMixin.
Definition section_countMixin := [countMixin of section gT by <:].
Canonical section_countType :=
  Eval hnf in CountType (section gT) section_countMixin.
Canonical section_subCountType := Eval hnf in [subCountType of section gT].
Definition section_finMixin := [finMixin of section gT by <:].
Canonical section_finType := Eval hnf in FinType (section gT) section_finMixin.
Canonical section_subFinType := Eval hnf in [subFinType of section gT].
Canonical section_group.

(* Isomorphic sections *)

Definition section_isog := [rel x y : section gT | x \isog y].

(* A witness of the isomorphism class of a section *)
Definition section_repr s := odflt (1 / 1)%sec (pick (section_isog ^~ s)).

Definition mksrepr G1 G2 := section_repr (mkSec G1 G2).

Lemma section_reprP s : section_repr s \isog s.
Proof.
by rewrite /section_repr; case: pickP => //= /(_ s); rewrite isog_refl.
Qed.

Lemma section_repr_isog s1 s2 :
  s1 \isog s2 -> section_repr s1 = section_repr s2.
Proof.
by move=> iso12; congr (odflt _ _); apply: eq_pick => s; apply: isog_transr.
Qed.

Definition mkfactors (G : {group gT}) (s : seq {group gT}) :=
  map section_repr (pairmap (@mkSec _) G s).

End Sections.

Section CompositionSeries.

Variable gT : finGroupType.
Local Notation gTg := {group gT}.
Implicit Types (G : gTg) (s : seq gTg).

Local Notation compo := [rel x y : {set gT} | maxnormal y x x].

Definition comps G s := ((last G s) == 1%G) && compo.-series G s.

Lemma compsP G s :
  reflect (last G s = 1%G /\  path [rel x y : gTg | maxnormal y x x] G s)
          (comps G s).
Proof. by apply: (iffP andP) => [] [/eqP]. Qed.

Lemma trivg_comps G s : comps G s -> (G :==: 1) = (s == [::]).
Proof.
case/andP=> ls cs; apply/eqP/eqP=> [G1 | s1]; last first.
  by rewrite s1 /= in ls; apply/eqP.
by case: s {ls} cs => //= H s /andP[/maxgroupp]; rewrite G1 /proper sub1G andbF.
Qed.

Lemma comps_cons G H s : comps G (H :: s) -> comps H s.
Proof. by case/andP => /= ls /andP[_]; rewrite /comps ls. Qed.

Lemma simple_compsP G s : comps G s -> reflect (s = [:: 1%G]) (simple G).
Proof.
move=> cs; apply: (iffP idP) => [|s1]; last first.
  by rewrite s1 /comps eqxx /= andbT -simple_maxnormal in cs.
case: s cs => [/trivg_comps/eqP-> | H s]; first by case/simpleP; rewrite eqxx.
rewrite [comps _ _]andbCA /= => /andP[/maxgroupp maxH /trivg_comps/esym nil_s].
rewrite simple_maxnormal => /maxgroupP[_ simG].
have H1: H = 1%G by apply/val_inj/simG; rewrite // sub1G.
by move: nil_s; rewrite H1 eqxx => /eqP->.
Qed.

Lemma exists_comps (G : gTg) : exists s, comps G s.
Proof.
elim: {G} #|G| {1 3}G (leqnn #|G|) => [G | n IHn G cG].
  by rewrite leqNgt cardG_gt0.
have [sG | nsG] := boolP (simple G).
  by exists [:: 1%G]; rewrite /comps eqxx /=  -simple_maxnormal andbT.
have [-> | ntG] := eqVneq G 1%G; first by exists [::]; rewrite /comps eqxx.
have [N maxN] := ex_maxnormal_ntrivg ntG.
have [|s /andP[ls cs]] := IHn N.
  by rewrite -ltnS (leq_trans _ cG) // proper_card // (maxnormal_proper maxN).
by exists (N :: s); apply/and3P.
Qed.

(******************************************************************************)
(* The factors associated to two composition series of the same group are     *)
(* the same up to isomorphism and permutation                                 *)
(******************************************************************************)

Lemma JordanHolderUniqueness (G : gTg) (s1 s2 : seq gTg) :
  comps G s1 -> comps G s2 -> perm_eq (mkfactors G s1) (mkfactors G s2).
Proof.
elim: {G}#|G| {-2}G (leqnn #|G|) => [|n Hi] G cG in s1 s2 * => cs1 cs2.
  by rewrite leqNgt cardG_gt0 in cG.
have [G1 | ntG] := boolP (G :==: 1).
  have -> : s1 = [::] by apply/eqP; rewrite -(trivg_comps cs1).
  have -> : s2 = [::] by apply/eqP; rewrite -(trivg_comps cs2).
  by rewrite /= perm_eq_refl.
have [sG | nsG] := boolP (simple G).
  by rewrite (simple_compsP cs1 sG) (simple_compsP cs2 sG) perm_eq_refl.
case es1: s1 cs1 => [|N1 st1] cs1.
  by move: (trivg_comps cs1); rewrite eqxx; move/negP:ntG.
case es2: s2 cs2 => [|N2 st2] cs2 {s1 es1}.
  by move: (trivg_comps cs2); rewrite eqxx; move/negP:ntG.
case/andP: cs1 => /= lst1; case/andP=> maxN_1 pst1.
case/andP: cs2 => /= lst2; case/andP=> maxN_2 pst2.
have cN1 : #|N1| <= n.
  by rewrite -ltnS (leq_trans _ cG) ?proper_card ?(maxnormal_proper maxN_1).
have cN2 : #|N2| <= n.
  by rewrite -ltnS (leq_trans _ cG) ?proper_card ?(maxnormal_proper maxN_2).
case: (N1 =P N2) {s2 es2} => [eN12 |].
  by rewrite eN12 /= perm_cons Hi // /comps ?lst2 //= -eN12 lst1.
move/eqP; rewrite -val_eqE /=; move/eqP=> neN12.
have nN1G : N1 <| G by apply: maxnormal_normal.
have nN2G : N2 <| G by apply: maxnormal_normal.
pose N := (N1 :&: N2)%G.
have nNG : N <| G.
  by rewrite /normal subIset ?(normal_sub nN1G) //= normsI ?normal_norm.
have iso1 : (G / N1)%G \isog (N2 / N)%G.
  rewrite isog_sym /= -(maxnormalM maxN_1 maxN_2) //.
  rewrite (@normC _ N1 N2) ?(subset_trans (normal_sub nN1G)) ?normal_norm //.
  by rewrite weak_second_isog ?(subset_trans (normal_sub nN2G)) ?normal_norm.
have iso2 : (G / N2)%G \isog (N1 / N)%G.
  rewrite isog_sym /= -(maxnormalM maxN_1 maxN_2) // setIC.
  by rewrite weak_second_isog ?(subset_trans (normal_sub nN1G)) ?normal_norm.
have [sN /andP[lsN csN]] := exists_comps N.
have i1 : perm_eq (mksrepr G N1 :: mkfactors N1 st1)
                  [:: mksrepr G N1, mksrepr N1 N & mkfactors N sN].
  rewrite perm_cons -[mksrepr _ _ :: _]/(mkfactors N1 [:: N & sN]).
  apply: Hi=> //; rewrite /comps ?lst1 //= lsN csN andbT /=.
  rewrite -quotient_simple.
    by rewrite -(isog_simple iso2) quotient_simple.
  by rewrite (normalS (subsetIl N1 N2) (normal_sub nN1G)).
have i2 : perm_eq (mksrepr G N2 :: mkfactors N2 st2)
                  [:: mksrepr G N2, mksrepr N2 N & mkfactors N sN].
  rewrite perm_cons -[mksrepr _ _ :: _]/(mkfactors N2 [:: N & sN]).
  apply: Hi=> //; rewrite /comps ?lst2 //= lsN csN andbT /=.
  rewrite -quotient_simple.
    by rewrite -(isog_simple iso1) quotient_simple.
  by rewrite (normalS (subsetIr N1 N2) (normal_sub nN2G)).
pose fG1 := [:: mksrepr G N1, mksrepr N1 N & mkfactors N sN].
pose fG2 := [:: mksrepr G N2, mksrepr N2 N & mkfactors N sN].
have i3 : perm_eq fG1 fG2.
  rewrite (@perm_catCA _ [::_] [::_]) /mksrepr.
  rewrite (@section_repr_isog _ (mkSec _ _) (mkSec _ _) iso1).
  rewrite -(@section_repr_isog _ (mkSec _ _) (mkSec _ _) iso2).
  exact: perm_eq_refl.
apply: (perm_eq_trans i1); apply: (perm_eq_trans i3); rewrite perm_eq_sym.
by apply: perm_eq_trans i2; apply: perm_eq_refl.
Qed.

End CompositionSeries.

(******************************************************************************)
(* Helper lemmas for group actions.                                           *) 
(******************************************************************************)

Section MoreGroupAction.

Variables (aT rT : finGroupType).
Variables (A : {group aT}) (D : {group rT}).
Variable to : groupAction A D.

Lemma gactsP (G : {set rT}) : reflect {acts A, on G | to} [acts A, on G | to].
Proof.
apply: (iffP idP) => [nGA x|nGA]; first exact: acts_act.
apply/subsetP=> a Aa; rewrite !inE; rewrite Aa.
by  apply/subsetP=> x; rewrite inE nGA.
Qed.

Lemma gactsM (N1 N2 : {set rT}) : 
    N1 \subset D -> N2 \subset D ->
  [acts A, on N1 | to] -> [acts A, on N2 | to] -> [acts A, on N1 * N2 | to].
Proof.
move=> sN1D sN2D aAN1 aAN2; apply/gactsP=> x Ax y.
apply/idP/idP; case/mulsgP=> y1 y2 N1y1 N2y2 e.
  move: (actKin to Ax y); rewrite e; move<-.
  rewrite gactM ?groupV ?(subsetP sN1D y1) ?(subsetP sN2D) //.
  by apply: mem_mulg; rewrite ?(gactsP _ aAN1) ?(gactsP _ aAN2) // groupV.
rewrite e gactM // ?(subsetP sN1D y1) ?(subsetP sN2D) //.
by apply: mem_mulg; rewrite ?(gactsP _ aAN1) // ?(gactsP _ aAN2).
Qed.

Lemma gactsI (N1 N2 : {set rT}) : 
  [acts A, on N1 | to] -> [acts A, on N2 | to] -> [acts A, on N1 :&: N2 | to].
Proof.
move=> aAN1 aAN2.
apply/subsetP=> x Ax; rewrite !inE Ax /=; apply/subsetP=> y Ny; rewrite inE.
case/setIP: Ny=> N1y N2y; rewrite inE ?astabs_act  ?N1y ?N2y //.
- by move/subsetP: aAN2; move/(_ x Ax).
- by move/subsetP: aAN1; move/(_ x Ax).
Qed.
  
Lemma gastabsP (S : {set rT}) (a : aT) :
  a \in A -> reflect (forall x, (to x a \in S) = (x \in S)) (a \in 'N(S | to)).
Proof.
move=> Aa; apply: (iffP idP) => [nSa x|nSa]; first exact: astabs_act.
by rewrite !inE Aa; apply/subsetP=> x; rewrite inE nSa.
Qed.

End MoreGroupAction.

(******************************************************************************)
(* Helper lemmas for quotient actions.                                        *)
(******************************************************************************)

Section MoreQuotientAction.

Variables (aT rT : finGroupType).
Variables (A : {group aT})(D : {group rT}).
Variable to : groupAction A D.

Lemma qact_dom_doms (H : {group rT}) : H \subset D -> qact_dom to H \subset A.
Proof.
by move=> sHD; apply/subsetP=> x; rewrite qact_domE // inE; case/andP.
Qed.

Lemma acts_qact_doms (H : {group rT}) :
  H \subset D -> [acts A, on H | to] -> qact_dom to H :=: A.
Proof.
move=> sHD aH; apply/eqP; rewrite eqEsubset; apply/andP.
split; first exact: qact_dom_doms.
apply/subsetP=> x Ax; rewrite qact_domE //; apply/gastabsP=> //.
by move/gactsP: aH; move/(_ x Ax).
Qed.

Lemma qacts_cosetpre (H : {group rT}) (K' : {group coset_of H}) :
    H \subset D -> [acts A, on H | to] ->
    [acts qact_dom to H, on K' | to / H] ->
  [acts A, on coset H @*^-1 K' | to].
Proof.
move=> sHD aH aK'; apply/subsetP=> x Ax; move: (Ax) (subsetP aK').
rewrite -{1}(acts_qact_doms sHD aH) => qdx; move/(_ x qdx) => nx.
rewrite !inE Ax; apply/subsetP=> y; case/morphpreP=> Ny /= K'Hy; rewrite inE.
apply/morphpreP; split; first by rewrite acts_qact_dom_norm.
by move/gastabsP: nx; move/(_  qdx (coset H y)); rewrite K'Hy qactE.
Qed.

Lemma qacts_coset (H K : {group rT}) : 
    H \subset D -> [acts A, on K | to] ->
  [acts qact_dom to H, on (coset H) @* K | to / H].
Proof.
move=> sHD aK.
apply/subsetP=> x qdx; rewrite inE qdx inE; apply/subsetP=> y.
case/morphimP=> z Nz Kz /= e; rewrite e inE qactE // mem_imset // inE.
move/gactsP: aK; move/(_ x (subsetP (qact_dom_doms sHD) _ qdx) z); rewrite Kz.
move->; move/acts_act: (acts_qact_dom to H); move/(_ x qdx z).
by rewrite Nz andbT.
Qed.

End MoreQuotientAction.

Section StableCompositionSeries.

Variables (aT rT : finGroupType).
Variables (D : {group rT})(A : {group aT}).
Variable to : groupAction A D.

Definition maxainv (B C : {set rT}) :=
  [max C of H | 
    [&& (H <| B), ~~ (B \subset H) & [acts A, on H | to]]].

Section MaxAinvProps.

Variables K N : {group rT}.

Lemma maxainv_norm : maxainv K N -> N <| K.
Proof. by move/maxgroupp; case/andP. Qed.

Lemma maxainv_proper : maxainv K N -> N \proper K.
Proof.
by move/maxgroupp; case/andP; rewrite properE; move/normal_sub->; case/andP.
Qed.

Lemma maxainv_sub : maxainv K N -> N \subset K.
Proof. by move=> h; apply: proper_sub; apply: maxainv_proper. Qed.

Lemma maxainv_ainvar : maxainv K N -> A \subset 'N(N | to).
Proof. by move/maxgroupp; case/and3P. Qed.

Lemma maxainvS : maxainv K N -> N \subset K.
Proof. by move=> pNN; rewrite proper_sub // maxainv_proper. Qed.

Lemma maxainv_exists : K :!=: 1 -> {N : {group rT} | maxainv K N}.
Proof.
move=> nt; apply: ex_maxgroup. exists [1 rT]%G.
rewrite /= normal1 subG1 nt /=.
apply/subsetP=> a Da; rewrite !inE Da /= sub1set !inE.
by rewrite /= -actmE // morph1 eqxx.
Qed.

End MaxAinvProps.

Lemma maxainvM (G H K : {group rT}) :
    H \subset D -> K \subset D -> maxainv G H -> maxainv G K ->
  H :<>: K -> H * K = G.
Proof.
move: H K => N1 N2 sN1D sN2D pmN1 pmN2 neN12.
have cN12 : commute N1 N2.
  apply: normC; apply: (subset_trans (maxainv_sub pmN1)).
  by rewrite normal_norm ?maxainv_norm.
wlog nsN21 : G N1 N2 sN1D sN2D pmN1 pmN2 neN12 cN12/ ~~(N1 \subset N2).
  move/eqP: (neN12); rewrite eqEsubset negb_and; case/orP=> ns; first by apply.
  by rewrite cN12; apply=> //; apply: sym_not_eq.
have nP : N1 * N2 <| G by rewrite normalM ?maxainv_norm.
have sN2P : N2 \subset N1 * N2 by rewrite mulg_subr ?group1.
case/maxgroupP: (pmN1); case/andP=> nN1G pN1G mN1.
case/maxgroupP: (pmN2); case/andP=> nN2G pN2G mN2.
case/andP: pN1G=> nsGN1 ha1; case/andP: pN2G=> nsGN2 ha2.
case e : (G \subset N1 * N2).
  by apply/eqP; rewrite eqEsubset e mulG_subG !normal_sub.
have: N1 <*> N2 = N2 by apply: mN2; rewrite /= ?comm_joingE // nP e /= gactsM.
by rewrite comm_joingE // => h; move: nsN21; rewrite -h mulg_subl.
Qed.

Definition asimple (K : {set rT}) := maxainv K 1.

Implicit Types (H K : {group rT}) (s : seq {group rT}).

Lemma asimpleP K :
  reflect [/\ K :!=: 1
            & forall H, H <| K -> [acts A, on H | to] -> H :=: 1 \/ H :=: K]
          (asimple K).
Proof.
apply: (iffP idP).
  case/maxgroupP; rewrite normal1 /=; case/andP=> nsK1 aK H1.
  rewrite eqEsubset negb_and nsK1 /=; split => // H nHK ha.
  case eHK : (H :==: K); first by right; apply/eqP.
  left; apply: H1; rewrite ?sub1G // nHK; move/negbT: eHK.
  by rewrite eqEsubset negb_and normal_sub //=; move->.
case=> ntK h; apply/maxgroupP; split.
  move: ntK; rewrite eqEsubset sub1G andbT normal1; move->.
  apply/subsetP=> a Da; rewrite !inE Da /= sub1set !inE.
  by rewrite /= -actmE // morph1 eqxx.
move=> H /andP[nHK /andP[nsKH ha]] _.
case: (h _ nHK ha)=> // /eqP; rewrite eqEsubset.
by rewrite (negbTE nsKH) andbF.
Qed.

Definition acomps K s :=
  ((last K s) == 1%G) && path [rel x y : {group rT} | maxainv x y] K s.

Lemma acompsP K s :
  reflect (last K s = 1%G /\  path [rel x y : {group rT} | maxainv x y] K s)
          (acomps K s).
Proof. by apply: (iffP andP); case; move/eqP. Qed.

Lemma trivg_acomps K s : acomps K s -> (K :==: 1) = (s == [::]).
Proof.
case/andP=> ls cs; apply/eqP/eqP; last first.
  by move=> se; rewrite se /= in ls; apply/eqP.
move=> G1; case: s ls cs => // H s _ /=; case/andP; case/maxgroupP.
by rewrite G1 sub1G andbF.
Qed.

Lemma acomps_cons K H s : acomps K (H :: s) -> acomps H s.
Proof. by case/andP => /= ls; case/andP=> _ p; rewrite /acomps ls. Qed.

Lemma asimple_acompsP K s : acomps K s -> reflect (s = [:: 1%G]) (asimple K).
Proof.
move=> cs; apply: (iffP idP); last first.
  by move=> se; move: cs; rewrite se /=; case/andP=> /=; rewrite andbT.
case: s cs.
  by rewrite /acomps /= andbT; move/eqP->; case/asimpleP; rewrite eqxx.
move=> H s cs sG; apply/eqP.
rewrite eqseq_cons -(trivg_acomps (acomps_cons cs)) andbC andbb.
case/acompsP: cs => /= ls; case/andP=> mH ps.
case/maxgroupP: sG; case/and3P => _ ntG _ ->; rewrite ?sub1G //.
rewrite (maxainv_norm mH); case/andP: (maxainv_proper mH)=> _ ->.
exact: (maxainv_ainvar mH).
Qed.

Lemma exists_acomps K : exists s, acomps K s.
Proof.
elim: {K} #|K| {1 3}K (leqnn #|K|) => [K | n Hi K cK].
  by rewrite leqNgt cardG_gt0.
case/orP: (orbN (asimple K)) => [sK | nsK].
  by exists [:: (1%G : {group rT})]; rewrite /acomps eqxx /= andbT.
case/orP: (orbN (K :==: 1))=> [tK | ntK].
  by exists (Nil _); rewrite /acomps /= andbT.
case: (maxainv_exists ntK)=> N pmN.
have cN: #|N| <= n.
  by rewrite -ltnS (leq_trans _ cK) // proper_card // (maxainv_proper pmN).
case: (Hi _ cN)=> s; case/andP=> lasts ps; exists [:: N & s]; rewrite /acomps.
by rewrite last_cons lasts /= pmN.
Qed.

End StableCompositionSeries.

Arguments maxainv {aT rT D%G A%G} to%gact B%g C%g.
Arguments asimple {aT rT D%G A%G} to%gact K%g.

Section StrongJordanHolder.

Section AuxiliaryLemmas.

Variables aT rT : finGroupType.
Variables (A : {group aT}) (D : {group rT}) (to : groupAction A D).

Lemma maxainv_asimple_quo (G H : {group rT}) :
   H \subset D -> maxainv to G H -> asimple (to / H) (G / H).
Proof.
move=> sHD /maxgroupP[/and3P[nHG pHG aH] Hmax].
apply/asimpleP; split; first by rewrite -subG1 quotient_sub1 ?normal_norm.
move=> K' nK'Q aK'.
have: (K' \proper (G / H)) || (G / H == K').
  by rewrite properE eqEsubset andbC (normal_sub nK'Q) !andbT orbC orbN.
case/orP=> [ pHQ | eQH]; last by right; apply sym_eq; apply/eqP.
left; pose K := ((coset H) @*^-1 K')%G.
have eK'I : K' \subset (coset H) @* 'N(H).
  by rewrite (subset_trans (normal_sub nK'Q)) ?morphimS ?normal_norm.
have eKK' : K' :=: K / H by rewrite /(K / H) morphpreK //=.
suff eKH : K :=: H by rewrite -trivg_quotient eKK' eKH.
have sHK : H \subset K by rewrite -ker_coset kerE morphpreS // sub1set group1.
apply: Hmax => //; apply/and3P; split; last exact: qacts_cosetpre.
  by rewrite -(quotientGK nHG) cosetpre_normal.
by move: (proper_subn pHQ); rewrite sub_morphim_pre ?normal_norm.
Qed.


Lemma asimple_quo_maxainv (G H : {group rT}) :
    H \subset D -> G \subset D -> [acts A, on G | to] -> [acts A, on H | to] ->
    H <| G -> asimple (to / H) (G / H) ->
  maxainv to G H.
Proof.
move=> sHD sGD aG aH nHG /asimpleP[ntQ maxQ]; apply/maxgroupP; split.
  by rewrite nHG -quotient_sub1 ?normal_norm // subG1 ntQ.
move=> K /and3P[nKG nsGK aK] sHK.
pose K' := (K / H)%G.
have K'dQ : K' <| (G / H)%G by apply: morphim_normal.
have nKH : H <| K by rewrite (normalS _ _ nHG) // normal_sub.
have: K' :=: 1%G \/ K' :=: (G / H).
  apply: (maxQ K' K'dQ) => /=.
  apply/subsetP=> x Adx. rewrite inE Adx /= inE. apply/subsetP=> y.
  rewrite quotientE; case/morphimP=> z Nz Kz ->; rewrite /= !inE qactE //.
  have ntoyx :  to z x \in 'N(H) by  rewrite (acts_qact_dom_norm Adx).
  apply/morphimP; exists (to z x) => //.
  suff h: qact_dom to H \subset A.
    by rewrite astabs_act // (subsetP aK) //; apply: (subsetP h).
  by apply/subsetP=> t; rewrite qact_domE // inE; case/andP.
case; last first.
  move/quotient_injG; rewrite !inE /=; move/(_ nKH nHG)=> c; move: nsGK.
  by rewrite c subxx.
rewrite /= -trivg_quotient => tK'; apply: (congr1 (@gval _)); move: tK'.
by apply: (@quotient_injG _ H); rewrite ?inE /= ?normal_refl.
Qed.

Lemma asimpleI (N1 N2 : {group rT}) : 
    N2 \subset 'N(N1) -> N1 \subset D ->
    [acts A, on N1 | to] -> [acts A, on N2 | to] -> 
    asimple (to / N1) (N2 / N1) ->
  asimple (to / (N2 :&: N1)) (N2 / (N2 :&: N1)).
Proof.
move=> nN21 sN1D aN1 aN2 /asimpleP[ntQ1 max1].
have [f1 [f1e f1ker f1pre f1im]] := restrmP (coset_morphism N1) nN21.
have hf2' : N2 \subset 'N(N2 :&: N1) by apply: normsI => //; rewrite normG.
have hf2'' : 'ker (coset (N2 :&: N1)) \subset 'ker f1.
  by rewrite f1ker !ker_coset.
pose f2 := factm_morphism  hf2'' hf2'.
apply/asimpleP; split.
   rewrite /= setIC; apply/negP; move: (second_isog nN21); move/isog_eq1->.
   by apply/negP.
move=> H nHQ2 aH; pose K := f2 @* H.
have nKQ1 : K <| N2 / N1.
  rewrite (_ : N2 / N1 = f2 @* (N2 / (N2 :&: N1))) ?morphim_normal //.
  by rewrite morphim_factm f1im.
have sqA : qact_dom to N1 \subset A.
  by apply/subsetP=> t; rewrite qact_domE // inE; case/andP.
have nNN2 : (N2 :&: N1) <| N2.
  by rewrite /normal subsetIl; apply: normsI => //; apply: normG.
have aKQ1 : [acts qact_dom to N1, on K | to / N1].
  pose H':= coset (N2 :&: N1)@*^-1 H.
  have eHH' : H :=: H' / (N2 :&: N1) by rewrite cosetpreK.
  have -> : K :=: f1 @* H' by rewrite /K eHH' morphim_factm.
  have sH'N2 : H' \subset N2.
    rewrite /H' eHH' quotientGK ?normal_cosetpre //=.
    by rewrite sub_cosetpre_quo ?normal_sub.
  have -> : f1 @* H' = coset N1 @* H' by rewrite f1im //=.
  apply: qacts_coset => //; apply: qacts_cosetpre => //; last exact: gactsI.
  by apply: (subset_trans (subsetIr _ _)).
have injf2 : 'injm f2.
  by rewrite ker_factm f1ker /= ker_coset /= subG1 /= -quotientE trivg_quotient.
have iHK : H \isog K.
  apply/isogP; pose f3 := restrm_morphism (normal_sub nHQ2) f2.
  by exists f3; rewrite 1?injm_restrm // morphim_restrm setIid.
case: (max1 _ nKQ1 aKQ1).
  by move/eqP; rewrite -(isog_eq1 iHK); move/eqP->; left.
move=> he /=; right; apply/eqP; rewrite eqEcard normal_sub //=.
move: (second_isog nN21); rewrite setIC; move/card_isog->; rewrite -he.
by move/card_isog: iHK=> <-; rewrite leqnn.
Qed.

End AuxiliaryLemmas.

Variables (aT rT : finGroupType).
Variables (A : {group aT}) (D : {group rT}) (to : groupAction A D).

(******************************************************************************)
(* The factors associated to two A-stable composition series of the same      *)
(* group are the same up to isomorphism and permutation                       *)
(******************************************************************************)

Lemma StrongJordanHolderUniqueness (G : {group rT}) (s1 s2 : seq {group rT}) :
    G \subset D -> acomps to G s1 -> acomps to G s2 -> 
  perm_eq (mkfactors G s1) (mkfactors G s2).
Proof.
elim: {G} #|G| {-2}G (leqnn #|G|) => [|n Hi] G cG in s1 s2 * => hsD cs1 cs2.
  by rewrite leqNgt cardG_gt0 in cG.
case/orP: (orbN (G :==: 1)) => [tG | ntG].
  have -> : s1 = [::] by apply/eqP; rewrite -(trivg_acomps cs1).
  have -> : s2 = [::] by apply/eqP; rewrite -(trivg_acomps cs2).
  by rewrite /= perm_eq_refl.
case/orP: (orbN (asimple to G))=> [sG | nsG].
  have -> : s1 = [:: 1%G ] by apply/(asimple_acompsP cs1).
  have -> : s2 = [:: 1%G ] by apply/(asimple_acompsP cs2).
  by rewrite /= perm_eq_refl.
case es1: s1 cs1 => [|N1 st1] cs1.
  by move: (trivg_comps cs1); rewrite eqxx; move/negP:ntG.
case es2: s2 cs2 => [|N2 st2] cs2 {s1 es1}.
  by move: (trivg_comps cs2); rewrite eqxx; move/negP:ntG.
case/andP: cs1 => /= lst1; case/andP=> maxN_1 pst1.
case/andP: cs2 => /= lst2; case/andP=> maxN_2 pst2.
have sN1D : N1 \subset D.
  by apply: subset_trans hsD; apply: maxainv_sub maxN_1.
have sN2D : N2 \subset D.
  by apply: subset_trans hsD; apply: maxainv_sub maxN_2.
have cN1 : #|N1| <= n.
  by rewrite -ltnS (leq_trans _ cG) ?proper_card ?(maxainv_proper maxN_1).
have cN2 : #|N2| <= n.
  by rewrite -ltnS (leq_trans _ cG) ?proper_card ?(maxainv_proper maxN_2).
case: (N1 =P N2) {s2 es2} => [eN12 |].
  by rewrite eN12 /= perm_cons Hi // /acomps ?lst2 //= -eN12 lst1.
move/eqP; rewrite -val_eqE /=; move/eqP=> neN12.
have nN1G : N1 <| G by apply: (maxainv_norm maxN_1).
have nN2G : N2 <| G by apply: (maxainv_norm maxN_2).
pose N := (N1 :&: N2)%G.
have nNG : N <| G.
  by rewrite /normal subIset ?(normal_sub nN1G) //= normsI ?normal_norm.
have iso1 : (G / N1)%G \isog (N2 / N)%G.
  rewrite isog_sym /= -(maxainvM _ _ maxN_1 maxN_2) //.
  rewrite (@normC _ N1 N2) ?(subset_trans (normal_sub nN1G)) ?normal_norm //.
  by rewrite weak_second_isog ?(subset_trans (normal_sub nN2G)) ?normal_norm.
have iso2 : (G / N2)%G \isog (N1 / N)%G.
  rewrite isog_sym /= -(maxainvM _ _ maxN_1 maxN_2) // setIC.
  by rewrite weak_second_isog ?(subset_trans (normal_sub nN1G)) ?normal_norm.
case: (exists_acomps to N)=> sN; case/andP=> lsN csN.
have aN1 : [acts A, on N1 | to].
  by case/maxgroupP: maxN_1; case/and3P.
have aN2 : [acts A, on N2 | to].
  by case/maxgroupP: maxN_2; case/and3P.
have nNN1 : N <| N1.
  by apply: (normalS _ _ nNG); rewrite ?subsetIl ?normal_sub.
have nNN2 : N <| N2.
  by apply: (normalS _ _ nNG); rewrite ?subsetIr ?normal_sub.
have aN : [ acts A, on N1 :&: N2 | to].
  apply/subsetP=> x Ax; rewrite !inE Ax /=; apply/subsetP=> y Ny; rewrite inE.
  case/setIP: Ny=> N1y N2y. rewrite inE ?astabs_act  ?N1y ?N2y //.
    by move/subsetP: aN2; move/(_ x Ax).
  by move/subsetP: aN1; move/(_ x Ax).
have i1 : perm_eq (mksrepr G N1 :: mkfactors N1 st1)
                  [:: mksrepr G N1, mksrepr N1 N & mkfactors N sN].
  rewrite perm_cons -[mksrepr _ _ :: _]/(mkfactors N1 [:: N & sN]).
  apply: Hi=> //; rewrite /acomps ?lst1 //= lsN csN andbT /=.
  apply: asimple_quo_maxainv=> //; first by apply: subIset; rewrite sN1D.
  apply: asimpleI => //.
    by apply: subset_trans (normal_norm nN2G); apply: normal_sub.
  rewrite -quotientMidl (maxainvM _ _ maxN_2) //.
    by apply: maxainv_asimple_quo.
  by move=> e; apply: neN12.
have i2 : perm_eq (mksrepr G N2 :: mkfactors N2 st2)
                  [:: mksrepr G N2, mksrepr N2 N & mkfactors N sN].
  rewrite perm_cons -[mksrepr _ _ :: _]/(mkfactors N2 [:: N & sN]).
  apply: Hi=> //; rewrite /acomps ?lst2 //= lsN csN andbT /=.
  apply: asimple_quo_maxainv=> //; first by apply: subIset; rewrite sN1D.
  have e : N1 :&: N2 :=: N2 :&: N1 by rewrite setIC.
  rewrite (group_inj (setIC N1 N2)); apply: asimpleI => //.
    by apply: subset_trans (normal_norm nN1G); apply: normal_sub.
  rewrite -quotientMidl (maxainvM _ _ maxN_1) //.
  exact: maxainv_asimple_quo.
pose fG1 := [:: mksrepr G N1, mksrepr N1 N & mkfactors N sN].
pose fG2 := [:: mksrepr G N2, mksrepr N2 N & mkfactors N sN].
have i3 : perm_eq fG1 fG2.
  rewrite (@perm_catCA _ [::_] [::_]) /mksrepr.
  rewrite (@section_repr_isog _ (mkSec _ _) (mkSec _ _) iso1).
  rewrite -(@section_repr_isog _ (mkSec _ _) (mkSec _ _) iso2).
  exact: perm_eq_refl.
apply: (perm_eq_trans i1); apply: (perm_eq_trans i3); rewrite perm_eq_sym.
by apply: perm_eq_trans i2; apply: perm_eq_refl.
Qed.

End StrongJordanHolder.






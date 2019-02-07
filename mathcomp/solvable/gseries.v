(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrbool ssrfun eqtype ssrnat seq path fintype bigop.
From mathcomp
Require Import finset fingroup morphism automorphism quotient action.
From mathcomp
Require Import commutator center.
(******************************************************************************)
(*           H <|<| G   <=> H is subnormal in G, i.e., H <| ... <| G.         *)
(* invariant_factor A H G <=> A normalises both H and G, and H <| G.          *)
(*         A.-invariant <=> the (invariant_factor A) relation, in the context *)
(*                          of the g_rel.-series notation.                    *)
(*    g_rel.-series H s <=> H :: s is a sequence of groups whose projection   *)
(*                          to sets satisfies relation g_rel pairwise; for    *)
(*                          example H <|<| G iff G = last H s for some s such *)
(*                          that normal.-series H s.                          *)
(*   stable_factor A H G == H <| G and A centralises G / H.                   *)
(*             A.-stable == the stable_factor relation, in the scope of the   *)
(*                          r.-series notation.                               *)
(*            G.-central == the central_factor relation, in the scope of the  *)
(*                          r.-series notation.                               *)
(*           maximal M G == M is a maximal proper subgroup of G.              *)
(*        maximal_eq M G == (M == G) or (maximal M G).                        *)
(*       maxnormal M G N == M is a maximal subgroup of G normalized by N.     *)
(*         minnormal M N == M is a minimal nontrivial group normalized by N.  *)
(*              simple G == G is a (nontrivial) simple group.                 *)
(*                       := minnormal G G                                     *)
(*              G.-chief == the chief_factor relation, in the scope of the    *)
(*                          r.-series notation.                               *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Section GroupDefs.

Variable gT : finGroupType.
Implicit Types A B U V : {set gT}.

Local Notation groupT := (group_of (Phant gT)).

Definition subnormal A B :=
  (A \subset B) && (iter #|B| (fun N => generated (class_support A N)) B == A).

Definition invariant_factor A B C :=
  [&& A \subset 'N(B), A \subset 'N(C) & B <| C].

Definition group_rel_of (r : rel {set gT}) := [rel H G : groupT | r H G].

Definition stable_factor A V U :=
  ([~: U, A] \subset V) && (V <| U). (* this orders allows and3P to be used *)

Definition central_factor A V U :=
  [&& [~: U, A] \subset V, V \subset U & U \subset A].

Definition maximal A B := [max A of G | G \proper B].

Definition maximal_eq A B := (A == B) || maximal A B.

Definition maxnormal A B U := [max A of G | G \proper B & U \subset 'N(G)].

Definition minnormal A B := [min A of G | G :!=: 1 & B \subset 'N(G)].

Definition simple A := minnormal A A.

Definition chief_factor A V U := maxnormal V U A && (U <| A).
End GroupDefs.

Arguments subnormal {gT} A%g B%g.
Arguments invariant_factor {gT} A%g B%g C%g.
Arguments stable_factor {gT} A%g V%g U%g.
Arguments central_factor {gT} A%g V%g U%g.
Arguments maximal {gT} A%g B%g.
Arguments maximal_eq {gT} A%g B%g.
Arguments maxnormal {gT} A%g B%g U%g.
Arguments minnormal {gT} A%g B%g.
Arguments simple {gT} A%g.
Arguments chief_factor {gT} A%g V%g U%g.

Notation "H <|<| G" := (subnormal H G)
  (at level 70, no associativity) : group_scope.

Notation "A .-invariant" := (invariant_factor A)
  (at level 2, format "A .-invariant") : group_rel_scope.
Notation "A .-stable" := (stable_factor A)
  (at level 2, format "A .-stable") : group_rel_scope.
Notation "A .-central" := (central_factor A)
  (at level 2, format "A .-central") : group_rel_scope.
Notation "G .-chief" := (chief_factor G)
  (at level 2, format "G .-chief") : group_rel_scope.

Arguments group_rel_of {gT} r%group_rel_scope _%G _%G : extra scopes.

Notation "r .-series" := (path (rel_of_simpl_rel (group_rel_of r)))
  (at level 2, format "r .-series") : group_scope.

Section Subnormal.

Variable gT : finGroupType.
Implicit Types (A B C D : {set gT}) (G H K : {group gT}).

Let setIgr H G := (G :&: H)%G.
Let sub_setIgr G H : G \subset H -> G = setIgr H G.
Proof. by move/setIidPl/group_inj. Qed.

Let path_setIgr H G s :
   normal.-series H s -> normal.-series (setIgr G H) (map (setIgr G) s).
Proof.
elim: s H => //= K s IHs H /andP[/andP[sHK nHK] Ksn].
by rewrite /normal setSI ?normsIG ?IHs.
Qed.

Lemma subnormalP H G :
  reflect (exists2 s, normal.-series H s & last H s = G) (H <|<| G).
Proof.
apply: (iffP andP) => [[sHG snHG] | [s Hsn <-{G}]].
  elim: {G}#|G| {-2}G sHG snHG => [|m IHm] G sHG.
    by exists [::]; last by apply/eqP; rewrite eq_sym.
  rewrite iterSr => /IHm[|s Hsn defG].
    by rewrite sub_gen // class_supportEr (bigD1 1) //= conjsg1 subsetUl.
  exists (rcons s G); rewrite ?last_rcons // -cats1 cat_path Hsn defG /=.
  rewrite /normal gen_subG class_support_subG //=.
  by rewrite norms_gen ?class_support_norm.
set f := fun _ => <<_>>; have idf: iter _ f H == H.
  by elim=> //= m IHm; rewrite (eqP IHm) /f class_support_id genGid.
elim: {s}(size s) {-2}s (eqxx (size s)) Hsn => [[] //= | m IHm s].
case/lastP: s => // s G; rewrite size_rcons last_rcons -cats1 cat_path /=.
set K := last H s => def_m /and3P[Hsn /andP[sKG nKG] _].
have:= sKG; rewrite subEproper; case/predU1P=> [<-|prKG]; first exact: IHm.
pose L := [group of f G].
have sHK: H \subset K by case/IHm: Hsn.
have sLK: L \subset K by rewrite gen_subG class_support_sub_norm.
rewrite -(subnK (proper_card (sub_proper_trans sLK prKG))) iter_add iterSr.
have defH: H = setIgr L H by rewrite -sub_setIgr ?sub_gen ?sub_class_support.
have: normal.-series H (map (setIgr L) s) by rewrite defH path_setIgr.
case/IHm=> [|_]; first by rewrite size_map.
by rewrite {1 2}defH last_map (subset_trans sHK) //= (setIidPr sLK) => /eqP->.
Qed.

Lemma subnormal_refl G : G <|<| G.
Proof. by apply/subnormalP; exists [::]. Qed.

Lemma subnormal_trans K H G : H <|<| K -> K <|<| G -> H <|<| G.
Proof.
case/subnormalP=> [s1 Hs1 <-] /subnormalP[s2 Hs12 <-].
by apply/subnormalP; exists (s1 ++ s2); rewrite ?last_cat // cat_path Hs1.
Qed.

Lemma normal_subnormal H G : H <| G -> H <|<| G.
Proof. by move=> nsHG; apply/subnormalP; exists [:: G]; rewrite //= nsHG. Qed.

Lemma setI_subnormal G H K : K \subset G -> H <|<| G -> H :&: K <|<| K.
Proof.
move=> sKG /subnormalP[s Hs defG]; apply/subnormalP.
exists (map (setIgr K) s); first exact: path_setIgr.
rewrite (last_map (setIgr K)) defG.
by apply: val_inj; rewrite /= (setIidPr sKG).
Qed.

Lemma subnormal_sub G H : H <|<| G -> H \subset G.
Proof. by case/andP. Qed.

Lemma invariant_subnormal A G H :
    A \subset 'N(G) -> A \subset 'N(H) -> H <|<| G ->
  exists2 s, (A.-invariant).-series H s & last H s = G.
Proof.
move=> nGA nHA /andP[]; move: #|G| => m.
elim: m => [|m IHm] in G nGA * => sHG.
  by rewrite eq_sym; exists [::]; last apply/eqP.
rewrite iterSr; set K := <<_>>.
have nKA: A \subset 'N(K) by rewrite norms_gen ?norms_class_support.
have sHK: H \subset K by rewrite sub_gen ?sub_class_support.
case/IHm=> // s Hsn defK; exists (rcons s G); last by rewrite last_rcons.
rewrite rcons_path Hsn !andbA defK nGA nKA /= -/K.
by rewrite gen_subG class_support_subG ?norms_gen ?class_support_norm.
Qed.

Lemma subnormalEsupport G H :
  H <|<| G -> H :=: G \/ <<class_support H G>> \proper G.
Proof.
case/andP=> sHG; set K := <<_>> => /eqP <-.
have: K \subset G by rewrite gen_subG class_support_subG.
rewrite subEproper; case/predU1P=> [defK|]; [left | by right].
by elim: #|G| => //= _ ->.
Qed.

Lemma subnormalEr G H : H <|<| G -> 
  H :=: G \/ (exists K : {group gT}, [/\ H <|<| K, K <| G & K \proper G]).
Proof.
case/subnormalP=> s Hs <-{G}.
elim/last_ind: s Hs => [|s G IHs]; first by left.
rewrite last_rcons -cats1 cat_path /= andbT; set K := last H s.
case/andP=> Hs nsKG; have:= normal_sub nsKG; rewrite subEproper.
case/predU1P=> [<- | prKG]; [exact: IHs | right; exists K; split=> //].
by apply/subnormalP; exists s.
Qed.

Lemma subnormalEl G H : H <|<| G ->
  H :=: G \/ (exists K : {group gT}, [/\ H <| K, K <|<| G & H \proper K]).
Proof.
case/subnormalP=> s Hs <-{G}; elim: s H Hs => /= [|K s IHs] H; first by left.
case/andP=> nsHK Ks; have:= normal_sub nsHK; rewrite subEproper.
case/predU1P=> [-> | prHK]; [exact: IHs | right; exists K; split=> //].
by apply/subnormalP; exists s.
Qed.

End Subnormal.

Arguments subnormalP {gT H G}.

Section MorphSubNormal.

Variable gT : finGroupType.
Implicit Type G H K : {group gT}.

Lemma morphim_subnormal (rT : finGroupType) G (f : {morphism G >-> rT}) H K :
  H <|<| K -> f @* H <|<| f @* K.
Proof.
case/subnormalP => s Hs <-{K}; apply/subnormalP.
elim: s H Hs => [|K s IHs] H /=; first by exists [::].
case/andP=> nsHK /IHs[fs Hfs <-].
by exists ([group of f @* K] :: fs); rewrite /= ?morphim_normal.
Qed.

Lemma quotient_subnormal H G K : G <|<| K -> G / H <|<| K / H.
Proof. exact: morphim_subnormal. Qed.

End MorphSubNormal.

Section MaxProps.

Variable gT : finGroupType.
Implicit Types G H M : {group gT}.

Lemma maximal_eqP M G :
  reflect (M \subset G  /\
             forall H, M \subset H -> H \subset G -> H :=: M \/ H :=: G)
       (maximal_eq M G).
Proof.
rewrite subEproper /maximal_eq; case: eqP => [->|_]; first left.
  by split=> // H sGH sHG; right; apply/eqP; rewrite eqEsubset sHG.
apply: (iffP maxgroupP) => [] [sMG maxM]; split=> // H.
  by move/maxM=> maxMH; rewrite subEproper; case/predU1P; auto.
by rewrite properEneq => /andP[/eqP neHG sHG] /maxM[].
Qed.

Lemma maximal_exists H G :
    H \subset G ->
  H :=: G \/ (exists2 M : {group gT}, maximal M G & H \subset M).
Proof.
rewrite subEproper; case/predU1P=> sHG; first by left.
suff [M *]: {M : {group gT} | maximal M G & H \subset M} by right; exists M.
exact: maxgroup_exists.
Qed.

Lemma mulg_normal_maximal G M H :
  M <| G -> maximal M G -> H \subset G -> ~~ (H \subset M) -> (M * H = G)%g.
Proof.
case/andP=> sMG nMG /maxgroupP[_ maxM] sHG not_sHM.
apply/eqP; rewrite eqEproper mul_subG // -norm_joinEr ?(subset_trans sHG) //.
by apply: contra not_sHM => /maxM <-; rewrite ?joing_subl ?joing_subr.
Qed.

End MaxProps.

Section MinProps.

Variable gT : finGroupType.
Implicit Types G H M : {group gT}.

Lemma minnormal_exists G H : H :!=: 1 -> G \subset 'N(H) ->
  {M : {group gT} | minnormal M G & M \subset H}.
Proof. by move=> ntH nHG; apply: mingroup_exists (H) _; rewrite ntH. Qed.

End MinProps.

Section MorphPreMax.

Variables (gT rT : finGroupType) (D : {group gT}) (f : {morphism D >-> rT}).
Variables (M G : {group rT}).
Hypotheses (dM : M \subset f @* D) (dG : G \subset f @* D).

Lemma morphpre_maximal : maximal (f @*^-1 M) (f @*^-1 G) = maximal M G.
Proof.
apply/maxgroupP/maxgroupP; rewrite morphpre_proper //= => [] [ltMG maxM].
  split=> // H ltHG sMH; have dH := subset_trans (proper_sub ltHG) dG.
  rewrite -(morphpreK dH) [f @*^-1 H]maxM ?morphpreK ?morphpreSK //.
  by rewrite morphpre_proper.
split=> // H ltHG sMH.
have dH: H \subset D := subset_trans (proper_sub ltHG) (subsetIl D _).
have defH: f @*^-1 (f @* H) = H.
  by apply: morphimGK dH; apply: subset_trans sMH; apply: ker_sub_pre.
rewrite -defH morphpre_proper ?morphimS // in ltHG.
by rewrite -defH [f @* H]maxM // -(morphpreK dM) morphimS.
Qed.

Lemma morphpre_maximal_eq : maximal_eq (f @*^-1 M) (f @*^-1 G) = maximal_eq M G.
Proof. by rewrite /maximal_eq morphpre_maximal !eqEsubset !morphpreSK. Qed.

End MorphPreMax.

Section InjmMax.

Variables (gT rT : finGroupType) (D : {group gT}) (f : {morphism D >-> rT}).
Variables M G L : {group gT}.

Hypothesis injf : 'injm f.
Hypotheses (dM : M \subset D) (dG : G \subset D) (dL : L \subset D).

Lemma injm_maximal : maximal (f @* M) (f @* G) = maximal M G.
Proof.
rewrite -(morphpre_invm injf) -(morphpre_invm injf G).
by rewrite morphpre_maximal ?morphim_invm.
Qed.

Lemma injm_maximal_eq : maximal_eq (f @* M) (f @* G) = maximal_eq M G.
Proof. by rewrite /maximal_eq injm_maximal // injm_eq. Qed.

Lemma injm_maxnormal : maxnormal (f @* M) (f @* G) (f @* L) = maxnormal M G L.
Proof.
pose injfm := (injm_proper injf, injm_norms, injmSK injf, subsetIl).
apply/maxgroupP/maxgroupP; rewrite !injfm // => [[nML maxM]].
  split=> // H nHL sMH; have [/proper_sub sHG _] := andP nHL.
  have dH := subset_trans sHG dG; apply: (injm_morphim_inj injf) => //.
  by apply: maxM; rewrite !injfm.
split=> // fH nHL sMH; have [/proper_sub sfHG _] := andP nHL.
have{sfHG} dfH: fH \subset f @* D := subset_trans sfHG (morphim_sub f G).
by rewrite -(morphpreK dfH) !injfm // in nHL sMH *; rewrite (maxM _ nHL).
Qed.

Lemma injm_minnormal : minnormal (f @* M) (f @* G) = minnormal M G.
Proof.
pose injfm := (morphim_injm_eq1 injf, injm_norms, injmSK injf, subsetIl).
apply/mingroupP/mingroupP; rewrite !injfm // => [[nML minM]].
  split=> // H nHG sHM; have dH := subset_trans sHM dM.
  by apply: (injm_morphim_inj injf) => //; apply: minM; rewrite !injfm.
split=> // fH nHG sHM; have dfH := subset_trans sHM (morphim_sub f M).
by rewrite -(morphpreK dfH) !injfm // in nHG sHM *; rewrite (minM _ nHG).
Qed.

End InjmMax.

Section QuoMax.

Variables (gT : finGroupType) (K G H : {group gT}).

Lemma cosetpre_maximal (Q R : {group coset_of K}) :
  maximal (coset K @*^-1 Q) (coset K @*^-1 R) = maximal Q R.
Proof. by rewrite morphpre_maximal ?sub_im_coset. Qed.

Lemma cosetpre_maximal_eq (Q R : {group coset_of K}) :
  maximal_eq (coset K @*^-1 Q) (coset K @*^-1 R) = maximal_eq Q R.
Proof. by rewrite /maximal_eq !eqEsubset !cosetpreSK cosetpre_maximal. Qed.

Lemma quotient_maximal :
  K <| G -> K <| H -> maximal (G / K) (H / K) = maximal G H.
Proof. by move=> nKG nKH; rewrite -cosetpre_maximal ?quotientGK. Qed.

Lemma quotient_maximal_eq :
  K <| G -> K <| H -> maximal_eq (G / K) (H / K) = maximal_eq G H.
Proof. by move=> nKG nKH; rewrite -cosetpre_maximal_eq ?quotientGK. Qed.

Lemma maximalJ x : maximal (G :^ x) (H :^ x) = maximal G H.
Proof.
rewrite -{1}(setTI G) -{1}(setTI H) -!morphim_conj.
by rewrite injm_maximal ?subsetT ?injm_conj.
Qed.

Lemma maximal_eqJ x : maximal_eq (G :^ x) (H :^ x) = maximal_eq G H.
Proof. by rewrite /maximal_eq !eqEsubset !conjSg maximalJ. Qed.

End QuoMax.

Section MaxNormalProps.

Variables (gT : finGroupType).
Implicit Types (A B C : {set gT}) (G H K L M : {group gT}).

Lemma maxnormal_normal A B : maxnormal A B B -> A <| B.
Proof.
by case/maxsetP=> /and3P[/gen_set_id /= -> pAB nAB]; rewrite /normal proper_sub.
Qed.

Lemma maxnormal_proper A B C : maxnormal A B C -> A \proper B.
Proof.
by case/maxsetP=> /and3P[gA pAB _] _; apply: (sub_proper_trans (subset_gen A)).
Qed.

Lemma maxnormal_sub A B C : maxnormal A B C -> A \subset B.
Proof.
by move=> maxA; rewrite proper_sub //; apply: (maxnormal_proper maxA).
Qed.

Lemma ex_maxnormal_ntrivg G : G :!=: 1-> {N : {group gT} | maxnormal N G G}.
Proof.
move=> ntG; apply: ex_maxgroup; exists [1 gT]%G; rewrite norm1 proper1G.
by rewrite subsetT ntG.
Qed.

Lemma maxnormalM G H K :
  maxnormal H G G -> maxnormal K G G -> H :<>: K -> H * K = G.
Proof.
move=> maxH maxK /eqP; apply: contraNeq => ltHK_G.
have [nsHG nsKG] := (maxnormal_normal maxH, maxnormal_normal maxK).
have cHK: commute H K.
  exact: normC (subset_trans (normal_sub nsHG) (normal_norm nsKG)).
wlog suffices: H K {maxH} maxK nsHG nsKG cHK ltHK_G / H \subset K.
  by move=> IH; rewrite eqEsubset !IH // -cHK.
have{maxK} /maxgroupP[_ maxK] := maxK.
apply/joing_idPr/maxK; rewrite ?joing_subr //= comm_joingE //.
by rewrite properEneq ltHK_G; apply: normalM.
Qed.

Lemma maxnormal_minnormal G L M :
    G \subset 'N(M) -> L \subset 'N(G) ->  maxnormal M G L ->
  minnormal (G / M) (L / M).
Proof.
move=> nMG nGL /maxgroupP[/andP[/andP[sMG ltMG] nML] maxM]; apply/mingroupP.
rewrite -subG1 quotient_sub1 ?ltMG ?quotient_norms //.
split=> // Hb /andP[ntHb nHbL]; have nsMG: M <| G by apply/andP.
case/inv_quotientS=> // H defHb sMH sHG; rewrite defHb; congr (_ / M).
apply/eqP; rewrite eqEproper sHG /=; apply: contra ntHb => ltHG.
have nsMH: M <| H := normalS sMH sHG nsMG.
rewrite defHb quotientS1 // (maxM H) // ltHG /=  -(quotientGK nsMH) -defHb.
exact: norm_quotient_pre.
Qed.

Lemma minnormal_maxnormal G L M :
  M <| G -> L \subset 'N(M) -> minnormal (G / M) (L / M) -> maxnormal M G L.
Proof.
case/andP=> sMG nMG nML /mingroupP[/andP[/= ntGM _] minGM]; apply/maxgroupP.
split=> [|H /andP[/andP[sHG ltHG] nHL] sMH].
  by rewrite /proper sMG nML andbT; apply: contra ntGM => /quotientS1 ->.
apply/eqP; rewrite eqEsubset sMH andbT -quotient_sub1 ?(subset_trans sHG) //.
rewrite subG1; apply: contraR ltHG => ntHM; rewrite -(quotientSGK nMG) //.
by rewrite (minGM (H / M)%G) ?quotientS // ntHM quotient_norms.
Qed.

End MaxNormalProps.

Section Simple.

Implicit Types gT rT : finGroupType.

Lemma simpleP gT (G : {group gT}) :
  reflect (G :!=: 1 /\ forall H : {group gT}, H <| G -> H :=: 1 \/ H :=: G)
          (simple G).
Proof.
apply: (iffP mingroupP); rewrite normG andbT => [[ntG simG]].
  split=> // N /andP[sNG nNG].
  by case: (eqsVneq N 1) => [|ntN]; [left | right; apply: simG; rewrite ?ntN].
split=> // N /andP[ntN nNG] sNG.
by case: (simG N) ntN => // [|->]; [apply/andP | case/eqP].
Qed.

Lemma quotient_simple gT (G H : {group gT}) :
  H <| G -> simple (G / H) = maxnormal H G G.
Proof.
move=> nsHG; have nGH := normal_norm nsHG.
by apply/idP/idP; [apply: minnormal_maxnormal | apply: maxnormal_minnormal].
Qed.

Lemma isog_simple gT rT (G : {group gT}) (M : {group rT}) :
  G \isog M -> simple G = simple M.
Proof.
move=> eqGM; wlog suffices: gT rT G M eqGM / simple M -> simple G.
  by move=> IH; apply/idP/idP; apply: IH; rewrite // isog_sym.
case/isogP: eqGM => f injf <- /simpleP[ntGf simGf].
apply/simpleP; split=> [|N nsNG]; first by rewrite -(morphim_injm_eq1 injf).
rewrite -(morphim_invm injf (normal_sub nsNG)).
have: f @* N <| f @* G by rewrite morphim_normal.
by case/simGf=> /= ->; [left | right]; rewrite (morphim1, morphim_invm).
Qed.

Lemma simple_maxnormal gT (G : {group gT}) : simple G = maxnormal 1 G G.
Proof.
by rewrite -quotient_simple ?normal1 // -(isog_simple (quotient1_isog G)).
Qed.

End Simple.

Section Chiefs.

Variable gT : finGroupType.
Implicit Types G H U V : {group gT}.

Lemma chief_factor_minnormal G V U :
  chief_factor G V U -> minnormal (U / V) (G / V).
Proof.
case/andP=> maxV /andP[sUG nUG]; apply: maxnormal_minnormal => //.
by have /andP[_ nVG] := maxgroupp maxV; apply: subset_trans sUG nVG.
Qed.

Lemma acts_irrQ G U V :
    G \subset 'N(V) -> V <| U ->
  acts_irreducibly G (U / V) 'Q = minnormal (U / V) (G / V).
Proof.
move=> nVG nsVU; apply/mingroupP/mingroupP; case=> /andP[->] /=.
  rewrite astabsQ // subsetI nVG /= => nUG minUV.
  rewrite quotient_norms //; split=> // H /andP[ntH nHG] sHU.
  by apply: minUV (sHU); rewrite ntH -(cosetpreK H) actsQ // norm_quotient_pre.
rewrite sub_quotient_pre // => nUG minU; rewrite astabsQ //.
rewrite (subset_trans nUG); last first.
  by rewrite subsetI subsetIl /= -{2}(quotientGK nsVU) morphpre_norm.
split=> // H /andP[ntH nHG] sHU.
rewrite -{1}(cosetpreK H) astabsQ ?normal_cosetpre ?subsetI ?nVG //= in nHG.
apply: minU sHU; rewrite ntH; apply: subset_trans (quotientS _ nHG) _.
by rewrite -{2}(cosetpreK H) quotient_norm.
Qed.

Lemma chief_series_exists H G :
  H <| G -> {s | (G.-chief).-series 1%G s & last 1%G s = H}.
Proof.
elim: {H}_.+1 {-2}H (ltnSn #|H|) => // m IHm U leUm nsUG.
have [-> | ntU] := eqVneq U 1%G; first by exists [::].
have [V maxV]: {V : {group gT} | maxnormal V U G}.
  by apply: ex_maxgroup; exists 1%G; rewrite proper1G ntU norms1.
have /andP[ltVU nVG] := maxgroupp maxV.
have [||s ch_s defV] := IHm V; first exact: leq_trans (proper_card ltVU) _.
  by rewrite /normal (subset_trans (proper_sub ltVU) (normal_sub nsUG)).
exists (rcons s U); last by rewrite last_rcons.
by rewrite rcons_path defV /= ch_s /chief_factor; apply/and3P.
Qed.

End Chiefs.

Section Central.

Variables (gT : finGroupType) (G : {group gT}).
Implicit Types H K : {group gT}.

Lemma central_factor_central H K :
  central_factor G H K -> (K / H) \subset 'Z(G / H).
Proof. by case/and3P=> /quotient_cents2r *; rewrite subsetI quotientS. Qed.


Lemma central_central_factor H K :
  (K / H) \subset 'Z(G / H) -> H <| K -> H <| G -> central_factor G H K.
Proof.
case/subsetIP=> sKGb cGKb /andP[sHK nHK] /andP[sHG nHG].
by rewrite /central_factor -quotient_cents2 // cGKb sHK -(quotientSGK nHK).
Qed.

End Central.

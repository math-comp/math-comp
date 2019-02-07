(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrbool ssrfun eqtype ssrnat seq choice fintype finfun.
From mathcomp
Require Import bigop finset fingroup.

(******************************************************************************)
(* This file contains the definitions of:                                     *)
(*                                                                            *)
(*   {morphism D >-> rT} ==                                                   *)
(*     the structure type of functions that are group morphisms mapping a     *)
(*     domain set D : {set aT} to a type rT; rT must have a finGroupType      *)
(*     structure, and D is usually a group (most of the theory expects this). *)
(*            mfun == the coercion projecting {morphism D >-> rT} to aT -> rT *)
(*                                                                            *)
(* Basic examples:                                                            *)
(*            idm D == the identity morphism with domain D, or more precisely *)
(*                     the identity function, but with a canonical            *)
(*                     {morphism G -> gT} structure.                          *)
(*          trivm D == the trivial morphism with domain D.                    *)
(* If f has a {morphism D >-> rT} structure                                   *)
(*           'dom f == D, the domain of f.                                    *)
(*           f @* A == the image of A by f, where f is defined.               *)
(*                  := f @: (D :&: A)                                         *)
(*        f @*^-1 R == the pre-image of R by f, where f is defined.           *)
(*                  :=  D :&: f @^-1: R                                       *)
(*           'ker f == the kernel of f.                                       *)
(*                  :=  f @*^-1 1                                             *)
(*         'ker_G f == the kernel of f restricted to G.                       *)
(*                  :=  G :&: 'ker f (this is a pure notation)                *)
(*          'injm f <=> f injective on D.                                     *)
(*                  <-> ker f \subset 1 (this is a pure notation)             *)
(*        invm injf == the inverse morphism of f, with domain f @* D, when f  *)
(*                     is injective (injf : 'injm f).                         *)
(*    restrm f sDom == the restriction of f to a subset A of D, given         *)
(*                     (sDom : A \subset D); restrm f sDom is transparently   *)
(*                     identical to f; the restrmP and domP lemmas provide    *)
(*                     opaque restrictions.                                   *)
(*     invm f infj  == the inverse morphism for an injective f, with domain   *)
(*                     f @* D, given (injf : 'injm f).                        *)
(*                                                                            *)
(*      G \isog H  <=> G and H are isomorphic as groups.                      *)
(*       H \homg G <=> H is a homomorphic image of G.                         *)
(*      isom G H f <=> f maps G isomorphically to H, provided D contains G.   *)
(*                  := f @: G^# == H^#                                        *)
(*                                                                            *)
(* If, moreover, g : {morphism G >-> gT} with G : {group aT},                 *)
(*  factm sKer sDom == the (natural) factor morphism mapping f @* G to g @* G *)
(*                     with sDom : G \subset D, sKer : 'ker f \subset 'ker g. *)
(*    ifactm injf g == the (natural) factor morphism mapping f @* G to g @* G *)
(*                     when f is injective (injf : 'injm f); here g must      *)
(*                     denote an actual morphism structure, not its function  *)
(*                     projection.                                            *)
(*                                                                            *)
(* If g has a {morphism G >-> aT} structure for any G : {group gT}, then      *)
(*           f \o g has a canonical {morphism g @*^-1 D >-> rT} structure.    *)
(*                                                                            *)
(* Finally, for an arbitrary function f : aT -> rT                            *)
(*     morphic D f <=> f preserves group multiplication in D, i.e.,           *)
(*                     f (x * y) = (f x) * (f y) for all x, y in D.           *)
(*        morphm fM == a function identical to f, but with a canonical        *)
(*                     {morphism D >-> rT} structure, given fM : morphic D f. *)
(*      misom D C f <=> f is a morphism that maps D isomorphically to C.      *)
(*                  := morphic D f && isom D C f                              *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Reserved Notation "x \isog y" (at level 70).

Section MorphismStructure.

Variables aT rT : finGroupType.

Structure morphism (D : {set aT}) : Type := Morphism {
  mfun :> aT -> FinGroup.sort rT;
  _ : {in D &, {morph mfun : x y / x * y}}
}.

(* We give the 'lightest' possible specification to define morphisms: local   *)
(* congruence, in D, with the group law of aT. We then provide the properties *)
(* for the 'textbook' notion of morphism, when the required structures are    *)
(* available (e.g. its domain is a group).                                    *)

Definition morphism_for D of phant rT := morphism D.

Definition clone_morphism D f :=
  let: Morphism _ fM := f
    return {type of @Morphism D for f} -> morphism_for D (Phant rT)
  in fun k => k fM.

Variables (D A : {set aT}) (R : {set rT}) (x : aT) (y : rT) (f : aT -> rT).

Variant morphim_spec : Prop := MorphimSpec z & z \in D & z \in A & y = f z.

Lemma morphimP : reflect morphim_spec (y \in f @: (D :&: A)).
Proof.
apply: (iffP imsetP) => [] [z]; first by case/setIP; exists z.
by exists z; first apply/setIP.
Qed.

Lemma morphpreP : reflect (x \in D /\ f x \in R) (x \in D :&: f @^-1: R).
Proof. by rewrite !inE; apply: andP. Qed.

End MorphismStructure.

Notation "{ 'morphism' D >-> T }" := (morphism_for D (Phant T))
  (at level 0, format "{ 'morphism'  D  >->  T }") : group_scope.
Notation "[ 'morphism' D 'of' f ]" :=
     (@clone_morphism _ _ D _ (fun fM => @Morphism _ _ D f fM))
   (at level 0, format "[ 'morphism'  D  'of'  f ]") : form_scope.
Notation "[ 'morphism' 'of' f ]" := (clone_morphism (@Morphism _ _ _ f))
   (at level 0, format "[ 'morphism'  'of'  f ]") : form_scope.

Arguments morphimP {aT rT D A y f}.
Arguments morphpreP {aT rT D R x f}.

(* Domain, image, preimage, kernel, using phantom types to infer the domain. *)

Section MorphismOps1.

Variables (aT rT : finGroupType) (D : {set aT}) (f : {morphism D >-> rT}).

Lemma morphM : {in D &, {morph f : x y / x * y}}.
Proof. by case f. Qed.

Notation morPhantom := (phantom (aT -> rT)).
Definition MorPhantom := Phantom (aT -> rT).

Definition dom of morPhantom f := D.

Definition morphim of morPhantom f := fun A => f @: (D :&: A).

Definition morphpre of morPhantom f := fun R : {set rT} => D :&: f @^-1: R.

Definition ker mph := morphpre mph 1.

End MorphismOps1.

Arguments morphim _ _ _%g _ _ _%g.
Arguments morphpre _ _ _%g _ _ _%g.

Notation "''dom' f" := (dom (MorPhantom f))
  (at level 10, f at level 8, format "''dom'  f") : group_scope.

Notation "''ker' f" := (ker (MorPhantom f))
  (at level 10, f at level 8, format "''ker'  f") : group_scope.

Notation "''ker_' H f" := (H :&: 'ker f)
  (at level 10, H at level 2, f at level 8, format "''ker_' H  f")
  : group_scope.

Notation "f @* A" := (morphim (MorPhantom f) A)
  (at level 24, format "f  @*  A") : group_scope.

Notation "f @*^-1 R" := (morphpre (MorPhantom f) R)
  (at level 24, format "f  @*^-1  R") : group_scope.

Notation "''injm' f" := (pred_of_set ('ker f) \subset pred_of_set 1)
  (at level 10, f at level 8, format "''injm'  f") : group_scope.

Section MorphismTheory.

Variables aT rT : finGroupType.
Implicit Types A B : {set aT}.
Implicit Types G H : {group aT}.
Implicit Types R S : {set rT}.
Implicit Types M : {group rT}.

(* Most properties of morphims hold only when the domain is a group. *)
Variables (D : {group aT}) (f : {morphism D >-> rT}).

Lemma morph1 : f 1 = 1.
Proof. by apply: (mulgI (f 1)); rewrite -morphM ?mulg1. Qed.

Lemma morph_prod I r (P : pred I) F :
    (forall i, P i -> F i \in D) ->
  f (\prod_(i <- r | P i) F i) = \prod_( i <- r | P i) f (F i).
Proof.
move=> D_F; elim/(big_load (fun x => x \in D)): _.
elim/big_rec2: _ => [|i _ x Pi [Dx <-]]; first by rewrite morph1.
by rewrite groupM ?morphM // D_F.
Qed.

Lemma morphV : {in D, {morph f : x / x^-1}}.
Proof.
move=> x Dx; apply: (mulgI (f x)).
by rewrite -morphM ?groupV // !mulgV morph1.
Qed.

Lemma morphJ : {in D &, {morph f : x y / x ^ y}}.
Proof. by move=> * /=; rewrite !morphM ?morphV // ?groupM ?groupV. Qed.

Lemma morphX n : {in D, {morph f : x / x ^+ n}}.
Proof.
by elim: n => [|n IHn] x Dx; rewrite ?morph1 // !expgS morphM ?(groupX, IHn).
Qed.

Lemma morphR : {in D &, {morph f : x y / [~ x, y]}}.
Proof. by move=> * /=; rewrite morphM ?(groupV, groupJ) // morphJ ?morphV. Qed.

(* Morphic image, preimage properties w.r.t. set-theoretic operations. *)

Lemma morphimE A : f @* A = f @: (D :&: A). Proof. by []. Qed.
Lemma morphpreE R : f @*^-1 R = D :&: f @^-1: R. Proof. by []. Qed.
Lemma kerE : 'ker f = f @*^-1 1. Proof. by []. Qed.

Lemma morphimEsub A : A \subset D -> f @* A = f @: A.
Proof. by move=> sAD; rewrite /morphim (setIidPr sAD). Qed.

Lemma morphimEdom : f @* D = f @: D.
Proof. exact: morphimEsub. Qed.

Lemma morphimIdom A : f @* (D :&: A) = f @* A.
Proof. by rewrite /morphim setIA setIid. Qed.

Lemma morphpreIdom R : D :&: f @*^-1 R = f @*^-1 R.
Proof. by rewrite /morphim setIA setIid. Qed.

Lemma morphpreIim R : f @*^-1 (f @* D :&: R) = f @*^-1 R.
Proof.
apply/setP=> x; rewrite morphimEdom !inE.
by case Dx: (x \in D); rewrite // mem_imset.
Qed.

Lemma morphimIim A : f @* D :&: f @* A = f @* A.
Proof. by apply/setIidPr; rewrite imsetS // setIid subsetIl. Qed.

Lemma mem_morphim A x : x \in D -> x \in A -> f x \in f @* A.
Proof. by move=> Dx Ax; apply/morphimP; exists x. Qed.

Lemma mem_morphpre R x : x \in D -> f x \in R -> x \in f @*^-1 R.
Proof. by move=> Dx Rfx; apply/morphpreP. Qed.

Lemma morphimS A B : A \subset B -> f @* A \subset f @* B.
Proof. by move=> sAB; rewrite imsetS ?setIS. Qed.

Lemma morphim_sub A : f @* A \subset f @* D.
Proof. by rewrite imsetS // setIid subsetIl. Qed.

Lemma leq_morphim A : #|f @* A| <= #|A|.
Proof.
by apply: (leq_trans (leq_imset_card _ _)); rewrite subset_leq_card ?subsetIr.
Qed.

Lemma morphpreS R S : R \subset S -> f @*^-1 R \subset f @*^-1 S.
Proof. by move=> sRS; rewrite setIS ?preimsetS. Qed.

Lemma morphpre_sub R : f @*^-1 R \subset D.
Proof. exact: subsetIl. Qed.

Lemma morphim_setIpre A R : f @* (A :&: f @*^-1 R) = f @* A :&: R.
Proof.
apply/setP=> fa; apply/morphimP/setIP=> [[a Da] | [/morphimP[a Da Aa ->] Rfa]].
  by rewrite !inE Da /= => /andP[Aa Rfa] ->; rewrite mem_morphim.
by exists a; rewrite // !inE Aa Da.
Qed.

Lemma morphim0 : f @* set0 = set0.
Proof. by rewrite morphimE setI0 imset0. Qed.

Lemma morphim_eq0 A : A \subset D -> (f @* A == set0) = (A == set0).
Proof. by rewrite imset_eq0 => /setIidPr->. Qed.

Lemma morphim_set1 x : x \in D -> f @* [set x] = [set f x].
Proof. by rewrite /morphim -sub1set => /setIidPr->; apply: imset_set1. Qed.

Lemma morphim1 : f @* 1 = 1.
Proof. by rewrite morphim_set1 ?morph1. Qed.

Lemma morphimV A : f @* A^-1 = (f @* A)^-1.
Proof.
wlog suffices: A / f @* A^-1 \subset (f @* A)^-1.
  by move=> IH; apply/eqP; rewrite eqEsubset IH -invSg invgK -{1}(invgK A) IH.
apply/subsetP=> _ /morphimP[x Dx Ax' ->]; rewrite !inE in Ax' *.
by rewrite -morphV // mem_imset // inE groupV Dx.
Qed.

Lemma morphpreV R : f @*^-1 R^-1 = (f @*^-1 R)^-1.
Proof.
apply/setP=> x; rewrite !inE groupV; case Dx: (x \in D) => //=.
by rewrite morphV.
Qed.

Lemma morphimMl A B : A \subset D -> f @* (A * B) = f @* A * f @* B.
Proof.
move=> sAD; rewrite /morphim setIC -group_modl // (setIidPr sAD).
apply/setP=> fxy; apply/idP/idP.
  case/imsetP=> _ /imset2P[x y Ax /setIP[Dy By] ->] ->{fxy}.
  by rewrite morphM // (subsetP sAD, mem_imset2) // mem_imset // inE By.
case/imset2P=> _ _ /imsetP[x Ax ->] /morphimP[y Dy By ->] ->{fxy}.
by rewrite -morphM // (subsetP sAD, mem_imset) // mem_mulg // inE By.
Qed.

Lemma morphimMr A B : B \subset D -> f @* (A * B) = f @* A * f @* B.
Proof.
move=> sBD; apply: invg_inj.
by rewrite invMg -!morphimV invMg morphimMl // -invGid invSg.
Qed.

Lemma morphpreMl R S :
  R \subset f @* D -> f @*^-1 (R * S) = f @*^-1 R * f @*^-1 S.
Proof.
move=> sRfD; apply/setP=> x; rewrite !inE.
apply/andP/imset2P=> [[Dx] | [y z]]; last first.
  rewrite !inE => /andP[Dy Rfy] /andP[Dz Rfz] ->.
  by rewrite ?(groupM, morphM, mem_imset2).
case/imset2P=> fy fz Rfy Rfz def_fx.
have /morphimP[y Dy _ def_fy]: fy \in f @* D := subsetP sRfD fy Rfy.
exists y (y^-1 * x); last by rewrite mulKVg.
  by rewrite !inE Dy -def_fy.
by rewrite !inE groupM ?(morphM, morphV, groupV) // def_fx -def_fy mulKg.
Qed.

Lemma morphimJ A x : x \in D -> f @* (A :^ x) = f @* A :^ f x.
Proof.
move=> Dx; rewrite !conjsgE morphimMl ?(morphimMr, sub1set, groupV) //.
by rewrite !(morphim_set1, groupV, morphV).
Qed.

Lemma morphpreJ R x : x \in D -> f @*^-1 (R :^ f x) = f @*^-1 R :^ x.
Proof.
move=> Dx; apply/setP=> y; rewrite conjIg !inE conjGid // !mem_conjg inE.
by case Dy: (y \in D); rewrite // morphJ ?(morphV, groupV).
Qed.

Lemma morphim_class x A :
  x \in D -> A \subset D -> f @* (x ^: A) = f x ^: f @* A.
Proof.
move=> Dx sAD; rewrite !morphimEsub ?class_subG // /class -!imset_comp.
by apply: eq_in_imset => y Ay /=; rewrite morphJ // (subsetP sAD).
Qed.

Lemma classes_morphim A :
  A \subset D -> classes (f @* A) = [set f @* xA | xA in classes A].
Proof.
move=> sAD; rewrite morphimEsub // /classes -!imset_comp.
apply: eq_in_imset => x /(subsetP sAD) Dx /=.
by rewrite morphim_class ?morphimEsub.
Qed.

Lemma morphimT : f @* setT = f @* D.
Proof. by rewrite -morphimIdom setIT. Qed.

Lemma morphimU A B : f @* (A :|: B) = f @* A :|: f @* B.
Proof. by rewrite -imsetU -setIUr. Qed.

Lemma morphimI A B : f @* (A :&: B) \subset f @* A :&: f @* B.
Proof. by rewrite subsetI // ?morphimS ?(subsetIl, subsetIr). Qed.

Lemma morphpre0 : f @*^-1 set0 = set0.
Proof. by rewrite morphpreE preimset0 setI0. Qed.

Lemma morphpreT : f @*^-1 setT = D.
Proof. by rewrite morphpreE preimsetT setIT. Qed.

Lemma morphpreU R S : f @*^-1 (R :|: S) = f @*^-1 R :|: f @*^-1 S.
Proof. by rewrite -setIUr -preimsetU. Qed.

Lemma morphpreI R S : f @*^-1 (R :&: S) = f @*^-1 R :&: f @*^-1 S.
Proof. by rewrite -setIIr -preimsetI. Qed.

Lemma morphpreD R S : f @*^-1 (R :\: S) = f @*^-1 R :\: f @*^-1 S.
Proof. by apply/setP=> x; rewrite !inE; case: (x \in D). Qed.

(* kernel, domain properties *)

Lemma kerP x : x \in D -> reflect (f x = 1) (x \in 'ker f).
Proof. by move=> Dx; rewrite 2!inE Dx; apply: set1P. Qed.

Lemma dom_ker : {subset 'ker f <= D}.
Proof. by move=> x /morphpreP[]. Qed.

Lemma mker x : x \in 'ker f -> f x = 1.
Proof. by move=> Kx; apply/kerP=> //; apply: dom_ker. Qed.

Lemma mkerl x y : x \in 'ker f -> y \in D -> f (x * y) = f y.
Proof. by move=> Kx Dy; rewrite morphM // ?(dom_ker, mker Kx, mul1g). Qed.

Lemma mkerr x y : x \in D -> y \in 'ker f -> f (x * y) = f x.
Proof. by move=> Dx Ky; rewrite morphM // ?(dom_ker, mker Ky, mulg1). Qed.

Lemma rcoset_kerP x y :
  x \in D -> y \in D -> reflect (f x = f y) (x \in 'ker f :* y).
Proof.
move=> Dx Dy; rewrite mem_rcoset !inE groupM ?morphM ?groupV //=.
by rewrite morphV // -eq_mulgV1; apply: eqP.
Qed.

Lemma ker_rcoset x y :
  x \in D -> y \in D -> f x = f y -> exists2 z, z \in 'ker f & x = z * y.
Proof. by move=> Dx Dy eqfxy; apply/rcosetP; apply/rcoset_kerP. Qed.

Lemma ker_norm : D \subset 'N('ker f).
Proof.
apply/subsetP=> x Dx; rewrite inE; apply/subsetP=> _ /imsetP[y Ky ->].
by rewrite !inE groupJ ?morphJ // ?dom_ker //= mker ?conj1g.
Qed.

Lemma ker_normal : 'ker f <| D.
Proof. by rewrite /(_ <| D) subsetIl ker_norm. Qed.

Lemma morphimGI G A : 'ker f \subset G -> f @* (G :&: A) = f @* G :&: f @* A.
Proof.
move=> sKG; apply/eqP; rewrite eqEsubset morphimI setIC.
apply/subsetP=> _ /setIP[/morphimP[x Dx Ax ->] /morphimP[z Dz Gz]].
case/ker_rcoset=> {Dz}// y Ky def_x.
have{z Gz y Ky def_x} Gx: x \in G by rewrite def_x groupMl // (subsetP sKG).
by rewrite mem_imset ?inE // Dx Gx Ax.
Qed.

Lemma morphimIG A G : 'ker f \subset G -> f @* (A :&: G) = f @* A :&: f @* G.
Proof. by move=> sKG; rewrite setIC morphimGI // setIC. Qed.

Lemma morphimD A B : f @* A :\: f @* B \subset f @* (A :\: B).
Proof.
rewrite subDset -morphimU morphimS //.
by rewrite setDE setUIr setUCr setIT subsetUr.
Qed.

Lemma morphimDG A G : 'ker f \subset G -> f @* (A :\: G) = f @* A :\: f @* G.
Proof.
move=> sKG; apply/eqP; rewrite eqEsubset morphimD andbT !setDE subsetI.
rewrite morphimS ?subsetIl // -[~: f @* G]setU0 -subDset setDE setCK.
by rewrite -morphimIG //= setIAC -setIA setICr setI0 morphim0.
Qed.

Lemma morphimD1 A : (f @* A)^# \subset f @* A^#.
Proof. by rewrite -!set1gE -morphim1 morphimD. Qed.

(* group structure preservation *)

Lemma morphpre_groupset M : group_set (f @*^-1 M).
Proof.
apply/group_setP; split=> [|x y]; rewrite !inE ?(morph1, group1) //.
by case/andP=> Dx Mfx /andP[Dy Mfy]; rewrite morphM ?groupM.
Qed.

Lemma morphim_groupset G : group_set (f @* G).
Proof.
apply/group_setP; split=> [|_ _ /morphimP[x Dx Gx ->] /morphimP[y Dy Gy ->]].
  by rewrite -morph1 mem_imset ?group1.
by rewrite -morphM ?mem_imset ?inE ?groupM.
Qed.

Canonical morphpre_group fPh M :=
  @group _ (morphpre fPh M) (morphpre_groupset M).
Canonical morphim_group fPh G := @group _ (morphim fPh G) (morphim_groupset G).
Canonical ker_group fPh : {group aT} := Eval hnf in [group of ker fPh].

Lemma morph_dom_groupset : group_set (f @: D).
Proof. by rewrite -morphimEdom groupP. Qed.

Canonical morph_dom_group := group morph_dom_groupset.

Lemma morphpreMr R S :
  S \subset f @* D -> f @*^-1 (R * S) = f @*^-1 R * f @*^-1 S.
Proof.
move=> sSfD; apply: invg_inj.
by rewrite invMg -!morphpreV invMg morphpreMl // -invSg invgK invGid.
Qed.

Lemma morphimK A : A \subset D -> f @*^-1 (f @* A) = 'ker f * A.
Proof.
move=> sAD; apply/setP=> x; rewrite !inE.
apply/idP/idP=> [/andP[Dx /morphimP[y Dy Ay eqxy]] | /imset2P[z y Kz Ay ->{x}]].
  rewrite -(mulgKV y x) mem_mulg // !inE !(groupM, morphM, groupV) //.
  by rewrite morphV //= eqxy mulgV.
have [Dy Dz]: y \in D /\ z \in D by rewrite (subsetP sAD) // dom_ker.
by rewrite groupM // morphM // mker // mul1g mem_imset // inE Dy.
Qed.

Lemma morphimGK G : 'ker f \subset G -> G \subset D -> f @*^-1 (f @* G) = G.
Proof. by move=> sKG sGD; rewrite morphimK // mulSGid. Qed.

Lemma morphpre_set1 x : x \in D -> f @*^-1 [set f x] = 'ker f :* x.
Proof. by move=> Dx; rewrite -morphim_set1 // morphimK ?sub1set. Qed.

Lemma morphpreK R : R \subset f @* D -> f @* (f @*^-1 R) = R.
Proof.
move=> sRfD; apply/setP=> y; apply/morphimP/idP=> [[x _] | Ry].
  by rewrite !inE; case/andP=> _ Rfx ->.
have /morphimP[x Dx _ defy]: y \in f @* D := subsetP sRfD y Ry.
by exists x; rewrite // !inE Dx -defy.
Qed.

Lemma morphim_ker : f @* 'ker f = 1.
Proof. by rewrite morphpreK ?sub1G. Qed.

Lemma ker_sub_pre M : 'ker f \subset f @*^-1 M.
Proof. by rewrite morphpreS ?sub1G. Qed.

Lemma ker_normal_pre M : 'ker f <| f @*^-1 M.
Proof. by rewrite /normal ker_sub_pre subIset ?ker_norm. Qed.

Lemma morphpreSK R S :
  R \subset f @* D -> (f @*^-1 R \subset f @*^-1 S) = (R \subset S).
Proof.
move=> sRfD; apply/idP/idP=> [sf'RS|]; last exact: morphpreS.
suffices: R \subset f @* D :&: S by rewrite subsetI sRfD.
rewrite -(morphpreK sRfD) -[_ :&: S]morphpreK (morphimS, subsetIl) //.
by rewrite morphpreI morphimGK ?subsetIl // setIA setIid.
Qed.

Lemma sub_morphim_pre A R :
  A \subset D -> (f @* A \subset R) = (A \subset f @*^-1 R).
Proof.
move=> sAD; rewrite -morphpreSK (morphimS, morphimK) //.
apply/idP/idP; first by apply: subset_trans; apply: mulG_subr.
by move/(mulgS ('ker f)); rewrite -morphpreMl ?(sub1G, mul1g).
Qed.

Lemma morphpre_proper R S :
    R \subset f @* D -> S \subset f @* D ->
  (f @*^-1 R \proper f @*^-1 S) = (R \proper S).
Proof. by move=> dQ dR; rewrite /proper !morphpreSK. Qed.

Lemma sub_morphpre_im R G :
    'ker f \subset G -> G \subset D -> R \subset f @* D ->
  (f @*^-1 R \subset G) = (R \subset f @* G).
Proof. by symmetry; rewrite -morphpreSK ?morphimGK. Qed.

Lemma ker_trivg_morphim A :
  (A \subset 'ker f) = (A \subset D) && (f @* A \subset [1]).
Proof.
case sAD: (A \subset D); first by rewrite sub_morphim_pre.
by rewrite subsetI sAD.
Qed.

Lemma morphimSK A B :
  A \subset D -> (f @* A \subset f @* B) = (A \subset 'ker f * B).
Proof.
move=> sAD; transitivity (A \subset 'ker f * (D :&: B)).
  by rewrite -morphimK ?subsetIl // -sub_morphim_pre // /morphim setIA setIid.
by rewrite setIC group_modl (subsetIl, subsetI) // andbC sAD.
Qed.

Lemma morphimSGK A G :
  A \subset D -> 'ker f \subset G -> (f @* A \subset f @* G) = (A \subset G).
Proof. by move=> sGD skfK; rewrite morphimSK // mulSGid. Qed.

Lemma ltn_morphim A : [1] \proper 'ker_A f -> #|f @* A| < #|A|.
Proof.
case/properP; rewrite sub1set => /setIP[A1 _] [x /setIP[Ax kx] x1].
rewrite (cardsD1 1 A) A1 ltnS -{1}(setD1K A1) morphimU morphim1.
rewrite (setUidPr _) ?sub1set; last first.
  by rewrite -(mker kx) mem_morphim ?(dom_ker kx) // inE x1.
by rewrite (leq_trans (leq_imset_card _ _)) ?subset_leq_card ?subsetIr.
Qed.

(* injectivity of image and preimage *)

Lemma morphpre_inj :
  {in [pred R : {set rT} | R \subset f @* D] &, injective (fun R => f @*^-1 R)}.
Proof. exact: can_in_inj morphpreK. Qed.

Lemma morphim_injG :
  {in [pred G : {group aT} | 'ker f \subset G & G \subset D] &,
     injective (fun G => f @* G)}.
Proof.
move=> G H /andP[sKG sGD] /andP[sKH sHD] eqfGH.
by apply: val_inj; rewrite /= -(morphimGK sKG sGD) eqfGH morphimGK.
Qed.

Lemma morphim_inj G H :
    ('ker f \subset G) && (G \subset D) ->
    ('ker f \subset H) && (H \subset D) ->
  f @* G = f @* H -> G :=: H.
Proof. by move=> nsGf nsHf /morphim_injG->. Qed.

(* commutation with generated groups and cycles *)

Lemma morphim_gen A : A \subset D -> f @* <<A>> = <<f @* A>>.
Proof.
move=> sAD; apply/eqP.
rewrite eqEsubset andbC gen_subG morphimS; last exact: subset_gen.
by rewrite sub_morphim_pre gen_subG // -sub_morphim_pre // subset_gen.
Qed.

Lemma morphim_cycle x : x \in D -> f @* <[x]> = <[f x]>.
Proof. by move=> Dx; rewrite morphim_gen (sub1set, morphim_set1). Qed.

Lemma morphimY A B :
  A \subset D -> B \subset D -> f @* (A <*> B) = f @* A <*> f @* B.
Proof. by move=> sAD sBD; rewrite morphim_gen ?morphimU // subUset sAD. Qed.

Lemma morphpre_gen R :
  1 \in R -> R \subset f @* D -> f @*^-1 <<R>> = <<f @*^-1 R>>.
Proof.
move=> R1 sRfD; apply/eqP.
rewrite eqEsubset andbC gen_subG morphpreS; last exact: subset_gen.
rewrite -{1}(morphpreK sRfD) -morphim_gen ?subsetIl // morphimGK //=.
  by rewrite sub_gen // setIS // preimsetS ?sub1set.
by rewrite gen_subG subsetIl.
Qed.

(* commutator, normaliser, normal, center properties*)

Lemma morphimR A B :
  A \subset D -> B \subset D -> f @* [~: A, B] = [~: f @* A, f @* B].
Proof.
move/subsetP=> sAD /subsetP sBD.
rewrite morphim_gen; last first; last congr <<_>>.
  by apply/subsetP=> _ /imset2P[x y Ax By ->]; rewrite groupR; auto.
apply/setP=> fz; apply/morphimP/imset2P=> [[z _] | [fx fy]].
  case/imset2P=> x y Ax By -> -> {z fz}.
  have Dx := sAD x Ax; have Dy := sBD y By.
  by exists (f x) (f y); rewrite ?(mem_imset, morphR) // ?(inE, Dx, Dy).
case/morphimP=> x Dx Ax ->{fx}; case/morphimP=> y Dy By ->{fy} -> {fz}.
by exists [~ x, y]; rewrite ?(inE, morphR, groupR, mem_imset2).
Qed.

Lemma morphim_norm A : f @* 'N(A) \subset 'N(f @* A).
Proof.
apply/subsetP=> fx; case/morphimP=> x Dx Nx -> {fx}.
by rewrite inE -morphimJ ?(normP Nx).
Qed.

Lemma morphim_norms A B : A \subset 'N(B) -> f @* A \subset 'N(f @* B).
Proof.
by move=> nBA; apply: subset_trans (morphim_norm B); apply: morphimS.
Qed.

Lemma morphim_subnorm A B : f @* 'N_A(B) \subset 'N_(f @* A)(f @* B).
Proof. exact: subset_trans (morphimI A _) (setIS _ (morphim_norm B)). Qed.

Lemma morphim_normal A B : A <| B -> f @* A <| f @* B.
Proof. by case/andP=> sAB nAB; rewrite /(_ <| _) morphimS // morphim_norms. Qed.

Lemma morphim_cent1 x : x \in D -> f @* 'C[x] \subset 'C[f x].
Proof. by move=> Dx; rewrite -(morphim_set1 Dx) morphim_norm. Qed.

Lemma morphim_cent1s A x : x \in D -> A \subset 'C[x] -> f @* A \subset 'C[f x].
Proof.
by move=> Dx cAx; apply: subset_trans (morphim_cent1 Dx); apply: morphimS.
Qed.

Lemma morphim_subcent1 A x : x \in D -> f @* 'C_A[x] \subset 'C_(f @* A)[f x].
Proof. by move=> Dx; rewrite -(morphim_set1 Dx) morphim_subnorm. Qed.

Lemma morphim_cent A : f @* 'C(A) \subset 'C(f @* A).
Proof.
apply/bigcapsP=> fx; case/morphimP=> x Dx Ax ->{fx}.
by apply: subset_trans (morphim_cent1 Dx); apply: morphimS; apply: bigcap_inf.
Qed.

Lemma morphim_cents A B : A \subset 'C(B) -> f @* A \subset 'C(f @* B).
Proof.
by move=> cBA; apply: subset_trans (morphim_cent B); apply: morphimS.
Qed.

Lemma morphim_subcent A B : f @* 'C_A(B) \subset 'C_(f @* A)(f @* B).
Proof. exact: subset_trans (morphimI A _) (setIS _ (morphim_cent B)). Qed.

Lemma morphim_abelian A : abelian A -> abelian (f @* A).
Proof. exact: morphim_cents. Qed.

Lemma morphpre_norm R : f @*^-1 'N(R) \subset 'N(f @*^-1 R).
Proof.
apply/subsetP=> x; rewrite !inE => /andP[Dx Nfx].
by rewrite -morphpreJ ?morphpreS.
Qed.

Lemma morphpre_norms R S : R \subset 'N(S) -> f @*^-1 R \subset 'N(f @*^-1 S).
Proof.
by move=> nSR; apply: subset_trans (morphpre_norm S); apply: morphpreS.
Qed.

Lemma morphpre_normal R S :
  R \subset f @* D -> S \subset f @* D -> (f @*^-1 R <| f @*^-1 S) = (R <| S).
Proof.
move=> sRfD sSfD; apply/idP/andP=> [|[sRS nSR]].
  by move/morphim_normal; rewrite !morphpreK //; case/andP.
by rewrite /(_ <| _) (subset_trans _ (morphpre_norm _)) morphpreS.
Qed.

Lemma morphpre_subnorm R S : f @*^-1 'N_R(S) \subset 'N_(f @*^-1 R)(f @*^-1 S).
Proof. by rewrite morphpreI setIS ?morphpre_norm. Qed.

Lemma morphim_normG G :
  'ker f \subset G -> G \subset D -> f @* 'N(G) = 'N_(f @* D)(f @* G).
Proof.
move=> sKG sGD; apply/eqP; rewrite eqEsubset -{1}morphimIdom morphim_subnorm.
rewrite -(morphpreK (subsetIl _ _)) morphimS //= morphpreI subIset // orbC.
by rewrite -{2}(morphimGK sKG sGD) morphpre_norm.
Qed.

Lemma morphim_subnormG A G :
  'ker f \subset G -> G \subset D -> f @* 'N_A(G) = 'N_(f @* A)(f @* G).
Proof.
move=> sKB sBD; rewrite morphimIG ?normsG // morphim_normG //.
by rewrite setICA setIA morphimIim.
Qed.

Lemma morphpre_cent1 x : x \in D -> 'C_D[x] \subset f @*^-1 'C[f x].
Proof.
move=> Dx; rewrite -sub_morphim_pre ?subsetIl //.
by apply: subset_trans (morphim_cent1 Dx); rewrite morphimS ?subsetIr.
Qed.

Lemma morphpre_cent1s R x :
  x \in D -> R \subset f @* D -> f @*^-1 R \subset 'C[x] -> R \subset 'C[f x].
Proof. by move=> Dx sRfD; move/(morphim_cent1s Dx); rewrite morphpreK. Qed.

Lemma morphpre_subcent1 R x :
  x \in D -> 'C_(f @*^-1 R)[x] \subset f @*^-1 'C_R[f x].
Proof.
move=> Dx; rewrite -morphpreIdom -setIA setICA morphpreI setIS //.
exact: morphpre_cent1.
Qed.

Lemma morphpre_cent A : 'C_D(A) \subset f @*^-1 'C(f @* A).
Proof.
rewrite -sub_morphim_pre ?subsetIl // morphimGI ?(subsetIl, subIset) // orbC.
by rewrite (subset_trans (morphim_cent _)).
Qed.

Lemma morphpre_cents A R :
  R \subset f @* D -> f @*^-1 R \subset 'C(A) -> R \subset 'C(f @* A).
Proof. by move=> sRfD; move/morphim_cents; rewrite morphpreK. Qed.

Lemma morphpre_subcent R A : 'C_(f @*^-1 R)(A) \subset f @*^-1 'C_R(f @* A).
Proof.
by rewrite -morphpreIdom -setIA setICA morphpreI setIS //; apply: morphpre_cent.
Qed.

(* local injectivity properties *)

Lemma injmP : reflect {in D &, injective f} ('injm f).
Proof.
apply: (iffP subsetP) => [injf x y Dx Dy | injf x /= Kx].
  by case/ker_rcoset=> // z /injf/set1P->; rewrite mul1g.
have Dx := dom_ker Kx; apply/set1P/injf => //.
by apply/rcoset_kerP; rewrite // mulg1.
Qed.

Lemma card_im_injm : (#|f @* D| == #|D|) = 'injm f.
Proof. by rewrite morphimEdom (sameP imset_injP injmP). Qed.

Section Injective.

Hypothesis injf : 'injm f.

Lemma ker_injm : 'ker f = 1.
Proof. exact/trivgP. Qed.

Lemma injmK A : A \subset D -> f @*^-1 (f @* A) = A.
Proof. by move=> sAD; rewrite morphimK // ker_injm // mul1g. Qed.

Lemma injm_morphim_inj A B :
  A \subset D -> B \subset D -> f @* A = f @* B -> A = B.
Proof. by move=> sAD sBD eqAB; rewrite -(injmK sAD) eqAB injmK. Qed.

Lemma card_injm A : A \subset D -> #|f @* A| = #|A|.
Proof.
move=> sAD; rewrite morphimEsub // card_in_imset //.
exact: (sub_in2 (subsetP sAD) (injmP injf)).
Qed.

Lemma order_injm x : x \in D -> #[f x] = #[x].
Proof.
by move=> Dx; rewrite orderE -morphim_cycle // card_injm ?cycle_subG.
Qed.

Lemma injm1 x : x \in D -> f x = 1 -> x = 1.
Proof. by move=> Dx; move/(kerP Dx); rewrite ker_injm; move/set1P. Qed.

Lemma morph_injm_eq1 x : x \in D -> (f x == 1) = (x == 1).
Proof. by move=> Dx; rewrite -morph1 (inj_in_eq (injmP injf)) ?group1. Qed.

Lemma injmSK A B :
  A \subset D -> (f @* A \subset f @* B) = (A \subset B).
Proof. by move=> sAD; rewrite morphimSK // ker_injm mul1g. Qed.

Lemma sub_morphpre_injm R A :
    A \subset D -> R \subset f @* D ->
  (f @*^-1 R \subset A) = (R \subset f @* A).
Proof. by move=> sAD sRfD; rewrite -morphpreSK ?injmK. Qed.

Lemma injm_eq A B : A \subset D -> B \subset D -> (f @* A == f @* B) = (A == B).
Proof. by move=> sAD sBD; rewrite !eqEsubset !injmSK. Qed.

Lemma morphim_injm_eq1 A : A \subset D -> (f @* A == 1) = (A == 1).
Proof. by move=> sAD; rewrite -morphim1 injm_eq ?sub1G. Qed.

Lemma injmI A B : f @* (A :&: B) = f @* A :&: f @* B.
Proof.
rewrite -morphimIdom setIIr -4!(injmK (subsetIl D _), =^~ morphimIdom).
by rewrite -morphpreI morphpreK // subIset ?morphim_sub.
Qed.

Lemma injmD1 A : f @* A^# = (f @* A)^#.
Proof. by have:= morphimDG A injf; rewrite morphim1. Qed.

Lemma nclasses_injm A : A \subset D -> #|classes (f @* A)| = #|classes A|.
Proof.
move=> sAD; rewrite classes_morphim // card_in_imset //.
move=> _ _ /imsetP[x Ax ->] /imsetP[y Ay ->].
by apply: injm_morphim_inj; rewrite // class_subG ?(subsetP sAD).
Qed.

Lemma injm_norm A : A \subset D -> f @* 'N(A) = 'N_(f @* D)(f @* A).
Proof.
move=> sAD; apply/eqP; rewrite -morphimIdom eqEsubset morphim_subnorm.
rewrite -sub_morphpre_injm ?subsetIl // morphpreI injmK // setIS //.
by rewrite -{2}(injmK sAD) morphpre_norm.
Qed.

Lemma injm_norms A B :
  A \subset D -> B \subset D -> (f @* A \subset 'N(f @* B)) = (A \subset 'N(B)).
Proof. by move=> sAD sBD; rewrite -injmSK // injm_norm // subsetI morphimS. Qed.

Lemma injm_normal A B :
  A \subset D -> B \subset D -> (f @* A <| f @* B) = (A <| B).
Proof. by move=> sAD sBD; rewrite /normal injmSK ?injm_norms. Qed.

Lemma injm_subnorm A B : B \subset D -> f @* 'N_A(B) = 'N_(f @* A)(f @* B).
Proof. by move=> sBD; rewrite injmI injm_norm // setICA setIA morphimIim. Qed.

Lemma injm_cent1 x : x \in D -> f @* 'C[x] = 'C_(f @* D)[f x].
Proof. by move=> Dx; rewrite injm_norm ?morphim_set1 ?sub1set. Qed.

Lemma injm_subcent1 A x : x \in D -> f @* 'C_A[x] = 'C_(f @* A)[f x].
Proof. by move=> Dx; rewrite injm_subnorm ?morphim_set1 ?sub1set. Qed.

Lemma injm_cent A : A \subset D -> f @* 'C(A) = 'C_(f @* D)(f @* A).
Proof.
move=> sAD; apply/eqP; rewrite -morphimIdom eqEsubset morphim_subcent.
apply/subsetP=> fx; case/setIP; case/morphimP=> x Dx _ ->{fx} cAfx.
rewrite mem_morphim // inE Dx -sub1set centsC cent_set1 -injmSK //.
by rewrite injm_cent1 // subsetI morphimS // -cent_set1 centsC sub1set.
Qed.

Lemma injm_cents A B :
  A \subset D -> B \subset D -> (f @* A \subset 'C(f @* B)) = (A \subset 'C(B)).
Proof. by move=> sAD sBD; rewrite -injmSK // injm_cent // subsetI morphimS. Qed.

Lemma injm_subcent A B : B \subset D -> f @* 'C_A(B) = 'C_(f @* A)(f @* B).
Proof. by move=> sBD; rewrite injmI injm_cent // setICA setIA morphimIim. Qed.

Lemma injm_abelian A : A \subset D -> abelian (f @* A) = abelian A.
Proof.
by move=> sAD; rewrite /abelian -subsetIidl -injm_subcent // injmSK ?subsetIidl.
Qed.

End Injective.

Lemma eq_morphim (g : {morphism D >-> rT}):
  {in D, f =1 g} -> forall A, f @* A = g @* A.
Proof.
by move=> efg A; apply: eq_in_imset; apply: sub_in1 efg => x /setIP[].
Qed.

Lemma eq_in_morphim B A (g : {morphism B >-> rT}) :
  D :&: A = B :&: A -> {in A, f =1 g} -> f @* A = g @* A.
Proof.
move=> eqDBA eqAfg; rewrite /morphim /= eqDBA.
by apply: eq_in_imset => x /setIP[_]/eqAfg.
Qed.

End MorphismTheory.

Notation "''ker' f" := (ker_group (MorPhantom f)) : Group_scope.
Notation "''ker_' G f" := (G :&: 'ker f)%G : Group_scope.
Notation "f @* G" := (morphim_group (MorPhantom f) G) : Group_scope.
Notation "f @*^-1 M" := (morphpre_group (MorPhantom f) M) : Group_scope.
Notation "f @: D" := (morph_dom_group f D) : Group_scope.

Arguments injmP {aT rT D f}.
Arguments morphpreK {aT rT D f} [R] sRf.

Section IdentityMorphism.

Variable gT : finGroupType.
Implicit Types A B : {set gT}.
Implicit Type G : {group gT}.

Definition idm of {set gT} := fun x : gT => x : FinGroup.sort gT.

Lemma idm_morphM A : {in A & , {morph idm A : x y / x * y}}.
Proof. by []. Qed.

Canonical idm_morphism A := Morphism (@idm_morphM A).

Lemma injm_idm G : 'injm (idm G).
Proof. by apply/injmP=> x y _ _. Qed.

Lemma ker_idm G : 'ker (idm G) = 1.
Proof. by apply/trivgP; apply: injm_idm. Qed.

Lemma morphim_idm A B : B \subset A -> idm A @* B = B.
Proof.
rewrite /morphim /= /idm => /setIidPr->.
by apply/setP=> x; apply/imsetP/idP=> [[y By ->]|Bx]; last exists x.
Qed.

Lemma morphpre_idm A B : idm A @*^-1 B = A :&: B.
Proof. by apply/setP=> x; rewrite !inE. Qed.

Lemma im_idm A : idm A @* A = A.
Proof. exact: morphim_idm. Qed.

End IdentityMorphism.

Arguments idm {_} _%g _%g.

Section RestrictedMorphism.

Variables aT rT : finGroupType.
Variables A D : {set aT}.
Implicit Type B : {set aT}.
Implicit Type R : {set rT}.

Definition restrm of A \subset D := @id (aT -> FinGroup.sort rT).

Section Props.

Hypothesis sAD : A \subset D.
Variable f : {morphism D >-> rT}.
Local Notation fA := (restrm sAD (mfun f)).

Canonical restrm_morphism :=
  @Morphism aT rT A fA (sub_in2 (subsetP sAD) (morphM f)).

Lemma morphim_restrm B : fA @* B = f @* (A :&: B).
Proof. by rewrite {2}/morphim setIA (setIidPr sAD). Qed.

Lemma restrmEsub B : B \subset A -> fA @* B = f @* B.
Proof. by rewrite morphim_restrm => /setIidPr->. Qed.

Lemma im_restrm : fA @* A = f @* A.
Proof. exact: restrmEsub. Qed.

Lemma morphpre_restrm R : fA @*^-1 R = A :&: f @*^-1 R.
Proof. by rewrite setIA (setIidPl sAD). Qed.

Lemma ker_restrm : 'ker fA = 'ker_A f.
Proof. exact: morphpre_restrm. Qed.

Lemma injm_restrm : 'injm f -> 'injm fA.
Proof. by apply: subset_trans; rewrite ker_restrm subsetIr. Qed.

End Props.

Lemma restrmP (f : {morphism D >-> rT}) : A \subset 'dom f ->
  {g : {morphism A >-> rT} | [/\ g = f :> (aT -> rT), 'ker g = 'ker_A f,
                                 forall R, g @*^-1 R = A :&: f @*^-1 R
                               & forall B, B \subset A -> g @* B = f @* B]}.
Proof.
move=> sAD; exists (restrm_morphism sAD f).
split=> // [|R|B sBA]; first 1 [exact: ker_restrm | exact: morphpre_restrm].
by rewrite morphim_restrm (setIidPr sBA).
Qed.

Lemma domP (f : {morphism D >-> rT}) : 'dom f = A ->
  {g : {morphism A >-> rT} | [/\ g = f :> (aT -> rT), 'ker g = 'ker f,
                                 forall R, g @*^-1 R = f @*^-1 R
                               & forall B, g @* B = f @* B]}.
Proof. by move <-; exists f. Qed.

End RestrictedMorphism.

Arguments restrm {_ _ _%g _%g} _ _%g.
Arguments restrmP {aT rT A D}.
Arguments domP {aT rT A D}.

Section TrivMorphism.

Variables aT rT : finGroupType.

Definition trivm of {set aT} & aT := 1 : FinGroup.sort rT.

Lemma trivm_morphM (A : {set aT}) : {in A &, {morph trivm A : x y / x * y}}.
Proof. by move=> x y /=; rewrite mulg1. Qed.

Canonical triv_morph A := Morphism (@trivm_morphM A).

Lemma morphim_trivm (G H : {group aT}) : trivm G @* H = 1.
Proof.
apply/setP=> /= y; rewrite inE; apply/idP/eqP=> [|->]; first by case/morphimP.
by apply/morphimP; exists (1 : aT); rewrite /= ?group1.
Qed.

Lemma ker_trivm (G : {group aT}) : 'ker (trivm G) = G.
Proof. by apply/setIidPl/subsetP=> x _; rewrite !inE /=. Qed.

End TrivMorphism.

Arguments trivm {aT rT} _%g _%g.

(* The composition of two morphisms is a Canonical morphism instance. *)
Section MorphismComposition.

Variables gT hT rT : finGroupType.
Variables (G : {group gT}) (H : {group hT}).

Variable f : {morphism G >-> hT}.
Variable g : {morphism H >-> rT}.

Local Notation gof := (mfun g \o mfun f).

Lemma comp_morphM : {in f @*^-1 H &, {morph gof: x y / x * y}}.
Proof.
by move=> x y; rewrite /= !inE => /andP[? ?] /andP[? ?]; rewrite !morphM.
Qed.

Canonical comp_morphism := Morphism comp_morphM.

Lemma ker_comp : 'ker gof = f @*^-1 'ker g.
Proof. by apply/setP=> x; rewrite !inE andbA. Qed.

Lemma injm_comp : 'injm f -> 'injm g -> 'injm gof.
Proof. by move=> injf; rewrite ker_comp; move/trivgP=> ->. Qed.

Lemma morphim_comp (A : {set gT}) : gof @* A = g @* (f @* A).
Proof.
apply/setP=> z; apply/morphimP/morphimP=> [[x]|[y Hy fAy ->{z}]].
  rewrite !inE => /andP[Gx Hfx]; exists (f x) => //.
  by apply/morphimP; exists x.
by case/morphimP: fAy Hy => x Gx Ax ->{y} Hfx; exists x; rewrite ?inE ?Gx.
Qed.

Lemma morphpre_comp (C : {set rT}) : gof @*^-1 C = f @*^-1 (g @*^-1 C).
Proof. by apply/setP=> z; rewrite !inE andbA. Qed.

End MorphismComposition.

(* The factor morphism *)
Section FactorMorphism.

Variables aT qT rT : finGroupType.

Variables G H : {group aT}.
Variable f : {morphism G >-> rT}.
Variable q : {morphism H >-> qT}.

Definition factm of 'ker q \subset 'ker f  & G \subset H :=
  fun x => f (repr (q @*^-1 [set x])).

Hypothesis sKqKf : 'ker q \subset 'ker f.
Hypothesis sGH : G \subset H.

Notation ff := (factm sKqKf sGH).

Lemma factmE x : x \in G -> ff (q x) = f x.
Proof.
rewrite /ff => Gx; have Hx := subsetP sGH x Gx.
have /mem_repr: x \in q @*^-1 [set q x] by rewrite !inE Hx /=.
case/morphpreP; move: (repr _) => y Hy /set1P.
by case/ker_rcoset=> // z Kz ->; rewrite mkerl ?(subsetP sKqKf).
Qed.

Lemma factm_morphM : {in q @* G &, {morph ff : x y / x * y}}.
Proof.
move=> _ _ /morphimP[x Hx Gx ->] /morphimP[y Hy Gy ->].
by rewrite -morphM ?factmE ?groupM // morphM.
Qed.

Canonical factm_morphism := Morphism factm_morphM.

Lemma morphim_factm (A : {set aT}) : ff @* (q @* A) = f @* A.
Proof.
rewrite -morphim_comp /= {1}/morphim /= morphimGK //; last first.
  by rewrite (subset_trans sKqKf) ?subsetIl.
apply/setP=> y; apply/morphimP/morphimP;
  by case=> x Gx Ax ->{y}; exists x; rewrite //= factmE.
Qed.

Lemma morphpre_factm (C : {set rT}) : ff @*^-1 C =  q @* (f @*^-1 C).
Proof.
apply/setP=> y; rewrite !inE /=; apply/andP/morphimP=> [[]|[x Hx]]; last first.
  by case/morphpreP=> Gx Cfx ->; rewrite factmE ?mem_imset ?inE ?Hx.
case/morphimP=> x Hx Gx ->; rewrite factmE //.
by exists x; rewrite // !inE Gx.
Qed.

Lemma ker_factm : 'ker ff = q @* 'ker f.
Proof. exact: morphpre_factm. Qed.

Lemma injm_factm : 'injm f -> 'injm ff.
Proof. by rewrite ker_factm => /trivgP->; rewrite morphim1. Qed.

Lemma injm_factmP : reflect ('ker f = 'ker q) ('injm ff).
Proof.
rewrite ker_factm -morphimIdom sub_morphim_pre ?subsetIl //.
rewrite setIA (setIidPr sGH) (sameP setIidPr eqP) (setIidPl _) // eq_sym.
exact: eqP.
Qed.

Lemma ker_factm_loc (K : {group aT}) : 'ker_(q @* K) ff = q @* 'ker_K f.
Proof. by rewrite ker_factm -morphimIG. Qed.

End FactorMorphism.

Prenex Implicits factm.

Section InverseMorphism.

Variables aT rT : finGroupType.
Implicit Types A B : {set aT}.
Implicit Types C D : {set rT}.
Variables (G : {group aT}) (f : {morphism G >-> rT}).
Hypothesis injf : 'injm f.

Lemma invm_subker : 'ker f \subset 'ker (idm G).
Proof. by rewrite ker_idm. Qed.

Definition invm := factm invm_subker (subxx _).

Canonical invm_morphism := Eval hnf in [morphism of invm].

Lemma invmE : {in G, cancel f invm}.
Proof. exact: factmE. Qed.

Lemma invmK : {in f @* G, cancel invm f}.
Proof. by move=> fx; case/morphimP=> x _ Gx ->; rewrite invmE. Qed.

Lemma morphpre_invm A : invm @*^-1 A = f @* A.
Proof. by rewrite morphpre_factm morphpre_idm morphimIdom. Qed.

Lemma morphim_invm A : A \subset G -> invm @* (f @* A) = A.
Proof. by move=> sAG; rewrite morphim_factm morphim_idm. Qed.

Lemma morphim_invmE C : invm @* C = f @*^-1 C.
Proof.
rewrite -morphpreIdom -(morphim_invm (subsetIl _ _)).
by rewrite morphimIdom -morphpreIim morphpreK (subsetIl, morphimIdom).
Qed.

Lemma injm_proper A B :
  A \subset G -> B \subset G -> (f @* A \proper f @* B) = (A \proper B).
Proof.
move=> dA dB; rewrite -morphpre_invm -(morphpre_invm B).
by rewrite morphpre_proper ?morphim_invm.
Qed.

Lemma injm_invm : 'injm invm.
Proof. by move/can_in_inj/injmP: invmK. Qed.

Lemma ker_invm : 'ker invm = 1.
Proof. by move/trivgP: injm_invm. Qed.

Lemma im_invm : invm @* (f @* G) = G.
Proof. exact: morphim_invm. Qed.

End InverseMorphism.

Prenex Implicits invm.

Section InjFactm.

Variables (gT aT rT : finGroupType) (D G : {group gT}).
Variables (g : {morphism G >-> rT}) (f : {morphism D >-> aT}) (injf : 'injm f).

Definition ifactm :=
  tag (domP [morphism of g \o invm injf] (morphpre_invm injf G)).

Lemma ifactmE : {in D, forall x, ifactm (f x) = g x}.
Proof.
rewrite /ifactm => x Dx; case: domP => f' /= [def_f' _ _ _].
by rewrite {f'}def_f' //= invmE.
Qed.

Lemma morphim_ifactm (A : {set gT}) :
   A \subset D -> ifactm @* (f @* A) = g @* A.
Proof.
rewrite /ifactm => sAD; case: domP => _ /= [_ _ _ ->].
by rewrite morphim_comp morphim_invm.
Qed.

Lemma im_ifactm : G \subset D -> ifactm @* (f @* G) = g @* G.
Proof. exact: morphim_ifactm. Qed.

Lemma morphpre_ifactm C : ifactm @*^-1 C = f @* (g @*^-1 C).
Proof.
rewrite /ifactm; case: domP => _ /= [_ _ -> _].
by rewrite morphpre_comp morphpre_invm.
Qed.

Lemma ker_ifactm : 'ker ifactm = f @* 'ker g.
Proof. exact: morphpre_ifactm. Qed.

Lemma injm_ifactm : 'injm g -> 'injm ifactm.
Proof. by rewrite ker_ifactm => /trivgP->; rewrite morphim1. Qed.

End InjFactm.

(* Reflected (boolean) form of morphism and isomorphism properties. *)

Section ReflectProp.

Variables aT rT : finGroupType.

Section Defs.

Variables (A : {set aT}) (B : {set rT}).

(* morphic is the morphM property of morphisms seen through morphicP. *)
Definition morphic (f : aT -> rT) :=
  [forall u in [predX A & A], f (u.1 * u.2) == f u.1 * f u.2].

Definition isom f := f @: A^# == B^#.

Definition misom f := morphic f && isom f.

Definition isog := [exists f : {ffun aT -> rT}, misom f].

Section MorphicProps.

Variable f : aT -> rT.

Lemma morphicP : reflect {in A &, {morph f : x y / x * y}} (morphic f).
Proof.
apply: (iffP forallP) => [fM x y Ax Ay | fM [x y] /=].
  by apply/eqP; have:= fM (x, y); rewrite inE /= Ax Ay.
by apply/implyP=> /andP[Ax Ay]; rewrite fM.
Qed.

Definition morphm of morphic f := f : aT -> FinGroup.sort rT.

Lemma morphmE fM : morphm fM = f. Proof. by []. Qed.

Canonical morphm_morphism fM := @Morphism _ _ A (morphm fM) (morphicP fM).

End MorphicProps.

Lemma misomP f : reflect {fM : morphic f & isom (morphm fM)} (misom f).
Proof. by apply: (iffP andP) => [] [fM fiso] //; exists fM. Qed.

Lemma misom_isog f : misom f -> isog.
Proof.
case/andP=> fM iso_f; apply/existsP; exists (finfun f).
apply/andP; split; last by rewrite /misom /isom !(eq_imset _ (ffunE f)).
by apply/forallP=> u; rewrite !ffunE; apply: forallP fM u.
Qed.

Lemma isom_isog (D : {group aT}) (f : {morphism D >-> rT}) :
  A \subset D -> isom f -> isog.
Proof.
move=> sAD isof; apply: (@misom_isog f); rewrite /misom isof andbT.
by apply/morphicP; apply: (sub_in2 (subsetP sAD) (morphM f)).
Qed.

Lemma isog_isom : isog -> {f : {morphism A >-> rT} | isom f}.
Proof.
by case/existsP/sigW=> f /misomP[fM isom_f]; exists (morphm_morphism fM).
Qed.

End Defs.

Infix "\isog" := isog.

Arguments isom_isog [A B D].

(* The real reflection properties only hold for true groups and morphisms. *)

Section Main.

Variables (G : {group aT}) (H : {group rT}).

Lemma isomP (f : {morphism G >-> rT}) :
  reflect ('injm f /\ f @* G = H) (isom G H f).
Proof.
apply: (iffP eqP) => [eqfGH | [injf <-]]; last first.
  by rewrite -injmD1 // morphimEsub ?subsetDl.
split.
  apply/subsetP=> x /morphpreP[Gx fx1]; have: f x \notin H^# by rewrite inE fx1.
  by apply: contraR => ntx; rewrite -eqfGH mem_imset // inE ntx.
rewrite morphimEdom -{2}(setD1K (group1 G)) imsetU eqfGH.
by rewrite imset_set1 morph1 setD1K.
Qed.

Lemma isogP :
  reflect (exists2 f : {morphism G >-> rT}, 'injm f & f @* G = H) (G \isog H).
Proof.
apply: (iffP idP) => [/isog_isom[f /isomP[]] | [f injf fG]]; first by exists f.
by apply: (isom_isog f) => //; apply/isomP.
Qed.

Variable f : {morphism G >-> rT}.
Hypothesis isoGH : isom G H f.

Lemma isom_inj : 'injm f. Proof. by have /isomP[] := isoGH. Qed.
Lemma isom_im : f @* G = H. Proof. by have /isomP[] := isoGH. Qed.
Lemma isom_card : #|G| = #|H|.
Proof. by rewrite -isom_im card_injm ?isom_inj. Qed.
Lemma isom_sub_im : H \subset f @* G. Proof. by rewrite isom_im. Qed.
Definition isom_inv := restrm isom_sub_im (invm isom_inj).

End Main.

Variables (G : {group aT}) (f : {morphism G >-> rT}).

Lemma morphim_isom (H : {group aT}) (K : {group rT}) :
  H \subset G -> isom H K f -> f @* H = K.
Proof. by case/(restrmP f)=> g [gf _ _ <- //]; rewrite -gf; case/isomP. Qed.

Lemma sub_isom (A : {set aT}) (C : {set rT}) :
  A \subset G -> f @* A = C -> 'injm f -> isom A C f.
Proof.
move=> sAG; case: (restrmP f sAG) => g [_ _ _ img] <-{C} injf.
rewrite /isom -morphimEsub ?morphimDG ?morphim1 //.
by rewrite subDset setUC subsetU ?sAG.
Qed.

Lemma sub_isog (A : {set aT}) : A \subset G -> 'injm f -> isog A (f @* A).
Proof. by move=> sAG injf; apply: (isom_isog f sAG); apply: sub_isom. Qed.

Lemma restr_isom_to (A : {set aT}) (C R : {group rT}) (sAG : A \subset G) :
   f @* A = C -> isom G R f -> isom A C (restrm sAG f).
Proof. by move=> defC /isomP[inj_f _]; apply: sub_isom. Qed.

Lemma restr_isom (A : {group aT}) (R : {group rT}) (sAG : A \subset G) :
  isom G R f -> isom A (f @* A) (restrm sAG f).
Proof. exact: restr_isom_to. Qed.

End ReflectProp.

Arguments isom {_ _} _%g _%g _.
Arguments morphic {_ _} _%g _.
Arguments misom _ _ _%g _%g _.
Arguments isog {_ _} _%g _%g.

Arguments morphicP {aT rT A f}.
Arguments misomP {aT rT A B f}.
Arguments isom_isog [aT rT A B D].
Arguments isomP {aT rT G H f}.
Arguments isogP {aT rT G H}.
Prenex Implicits morphm.
Notation "x \isog y":= (isog x y).

Section Isomorphisms.

Variables gT hT kT : finGroupType.
Variables (G : {group gT}) (H : {group hT}) (K : {group kT}).

Lemma idm_isom : isom G G (idm G).
Proof. exact: sub_isom (im_idm G) (injm_idm G). Qed.

Lemma isog_refl : G \isog G. Proof. exact: isom_isog idm_isom. Qed.

Lemma card_isog : G \isog H -> #|G| = #|H|.
Proof. by case/isogP=> f injf <-; apply: isom_card (f) _; apply/isomP. Qed.

Lemma isog_abelian :  G \isog H -> abelian G = abelian H.
Proof. by case/isogP=> f injf <-; rewrite injm_abelian. Qed.

Lemma trivial_isog : G :=: 1 -> H :=: 1 -> G \isog H.
Proof.
move=> -> ->; apply/isogP.
exists [morphism of @trivm gT hT 1]; rewrite /= ?morphim1 //.
by rewrite ker_trivm; apply: subxx.
Qed.

Lemma isog_eq1 : G \isog H -> (G :==: 1) = (H :==: 1).
Proof. by move=> isoGH; rewrite !trivg_card1 card_isog. Qed.

Lemma isom_sym (f : {morphism G >-> hT}) (isoGH : isom G H f) :
  isom H G (isom_inv isoGH).
Proof.
rewrite sub_isom 1?injm_restrm ?injm_invm // im_restrm.
by rewrite -(isom_im isoGH) im_invm.
Qed.

Lemma isog_symr : G \isog H -> H \isog G.
Proof. by case/isog_isom=> f /isom_sym/isom_isog->. Qed.

Lemma isog_trans : G \isog H -> H \isog K -> G \isog K.
Proof.
case/isogP=> f injf <-; case/isogP=> g injg <-.
have defG: f @*^-1 (f @* G) = G by rewrite morphimGK ?subsetIl.
rewrite -morphim_comp -{1 8}defG.
by apply/isogP; exists [morphism of g \o f]; rewrite ?injm_comp.
Qed.

Lemma nclasses_isog : G \isog H -> #|classes G| = #|classes H|.
Proof. by case/isogP=> f injf <-; rewrite nclasses_injm. Qed.

End Isomorphisms.

Section IsoBoolEquiv.

Variables gT hT kT : finGroupType.
Variables (G : {group gT}) (H : {group hT}) (K : {group kT}).

Lemma isog_sym : (G \isog H) = (H \isog G).
Proof. by apply/idP/idP; apply: isog_symr. Qed.

Lemma isog_transl : G \isog H -> (G \isog K) = (H \isog K).
Proof.
by move=> iso; apply/idP/idP; apply: isog_trans; rewrite // -isog_sym.
Qed.

Lemma isog_transr : G \isog H -> (K \isog G) = (K \isog H).
Proof.
by move=> iso; apply/idP/idP; move/isog_trans; apply; rewrite // -isog_sym.
Qed.

End IsoBoolEquiv.

Section Homg.

Implicit Types rT gT aT : finGroupType.

Definition homg rT aT (C : {set rT}) (D : {set aT}) :=
  [exists (f : {ffun aT -> rT} | morphic D f), f @: D == C].

Lemma homgP rT aT (C : {set rT}) (D : {set aT}) : 
  reflect (exists f : {morphism D >-> rT}, f @* D = C) (homg C D).
Proof.
apply: (iffP exists_eq_inP) => [[f fM <-] | [f <-]].
  by exists (morphm_morphism fM); rewrite /morphim /= setIid.
exists (finfun f); first by apply/morphicP=> x y Dx Dy; rewrite !ffunE morphM.
by rewrite /morphim setIid; apply: eq_imset => x; rewrite ffunE.
Qed.

Lemma morphim_homg aT rT (A D : {set aT}) (f : {morphism D >-> rT}) :
  A \subset D -> homg (f @* A) A.
Proof.
move=> sAD; apply/homgP; exists (restrm_morphism sAD f).
by rewrite morphim_restrm setIid.
Qed.

Lemma leq_homg rT aT (C : {set rT}) (G : {group aT}) :
  homg C G -> #|C| <= #|G|.
Proof. by case/homgP=> f <-; apply: leq_morphim. Qed.

Lemma homg_refl aT (A : {set aT}) : homg A A.
Proof. by apply/homgP; exists (idm_morphism A); rewrite im_idm. Qed.

Lemma homg_trans aT (B : {set aT}) rT (C : {set rT}) gT (G : {group gT}) :
  homg C B -> homg B G -> homg C G.
Proof.
move=> homCB homBG; case/homgP: homBG homCB => fG <- /homgP[fK <-].
by rewrite -morphim_comp morphim_homg // -sub_morphim_pre.
Qed.

Lemma isogEcard rT aT (G : {group rT}) (H : {group aT}) :
  (G \isog H) = (homg G H) && (#|H| <= #|G|).
Proof.
rewrite isog_sym; apply/isogP/andP=> [[f injf <-] | []].
  by rewrite leq_eqVlt eq_sym card_im_injm injf morphim_homg.
case/homgP=> f <-; rewrite leq_eqVlt eq_sym card_im_injm.
by rewrite ltnNge leq_morphim orbF; exists f.
Qed.

Lemma isog_hom rT aT (G : {group rT}) (H : {group aT}) : G \isog H -> homg G H.
Proof. by rewrite isogEcard; case/andP. Qed.

Lemma isogEhom rT aT (G : {group rT}) (H : {group aT}) :
  (G \isog H) = homg G H && homg H G.
Proof.
apply/idP/andP=> [isoGH | [homGH homHG]].
  by rewrite !isog_hom // isog_sym.
by rewrite isogEcard homGH leq_homg.
Qed.

Lemma eq_homgl gT aT rT (G : {group gT}) (H : {group aT}) (K : {group rT}) :
  G \isog H -> homg G K = homg H K.
Proof.
by rewrite isogEhom => /andP[homGH homHG]; apply/idP/idP; apply: homg_trans.
Qed.

Lemma eq_homgr gT rT aT (G : {group gT}) (H : {group rT}) (K : {group aT}) :
  G \isog H -> homg K G = homg K H.
Proof.
rewrite isogEhom => /andP[homGH homHG].
by apply/idP/idP=> homK; apply: homg_trans homK _.
Qed.

End Homg.

Arguments homg _ _ _%g _%g.
Notation "G \homg H" := (homg G H)
  (at level 70, no associativity) : group_scope.

Arguments homgP {rT aT C D}.

(* Isomorphism between a group and its subtype. *)

Section SubMorphism.

Variables (gT : finGroupType) (G : {group gT}).

Canonical sgval_morphism := Morphism (@sgvalM _ G).
Canonical subg_morphism := Morphism (@subgM _ G).

Lemma injm_sgval : 'injm sgval.
Proof. exact/injmP/(in2W subg_inj). Qed.

Lemma injm_subg : 'injm (subg G).
Proof. exact/injmP/(can_in_inj subgK). Qed.
Hint Resolve injm_sgval injm_subg : core.

Lemma ker_sgval : 'ker sgval = 1. Proof. exact/trivgP. Qed.
Lemma ker_subg : 'ker (subg G) = 1. Proof. exact/trivgP. Qed.

Lemma im_subg : subg G @* G = [subg G].
Proof.
apply/eqP; rewrite -subTset morphimEdom.
by apply/subsetP=> u _; rewrite -(sgvalK u) mem_imset ?subgP.
Qed.

Lemma sgval_sub A : sgval @* A \subset G.
Proof. by apply/subsetP=> x; case/imsetP=> u _ ->; apply: subgP. Qed.

Lemma sgvalmK A : subg G @* (sgval @* A) = A.
Proof.
apply/eqP; rewrite eqEcard !card_injm ?subsetT ?sgval_sub // leqnn andbT.
rewrite -morphim_comp; apply/subsetP=> _ /morphimP[v _ Av ->] /=.
by rewrite sgvalK.
Qed.

Lemma subgmK (A : {set gT}) : A \subset G -> sgval @* (subg G @* A) = A.
Proof.
move=> sAG; apply/eqP; rewrite eqEcard !card_injm ?subsetT //.
rewrite leqnn andbT -morphim_comp morphimE /= morphpreT.
by apply/subsetP=> _ /morphimP[v Gv Av ->] /=; rewrite subgK.
Qed.

Lemma im_sgval : sgval @* [subg G] = G.
Proof. by rewrite -{2}im_subg subgmK. Qed.

Lemma isom_subg : isom G [subg G] (subg G).
Proof. by apply/isomP; rewrite im_subg. Qed.

Lemma isom_sgval : isom [subg G] G sgval.
Proof. by apply/isomP; rewrite im_sgval. Qed.

Lemma isog_subg : isog G [subg G].
Proof. exact: isom_isog isom_subg. Qed.

End SubMorphism.

Arguments sgvalmK {gT G} A.
Arguments subgmK {gT G} [A] sAG.


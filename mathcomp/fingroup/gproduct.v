(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrbool ssrfun eqtype ssrnat seq div choice fintype.
From mathcomp
Require Import bigop finset fingroup morphism quotient action.

(******************************************************************************)
(*  Partial, semidirect, central, and direct products.                        *)
(*  ++ Internal products, with A, B : {set gT}, are partial operations :      *)
(*  partial_product A B == A * B if A is a group normalised by the group B,   *)
(*                         and the empty set otherwise.                       *)
(*              A ><| B == A * B if this is a semi-direct product (i.e., if A *)
(*                         is normalised by B and intersects it trivially).   *)
(*               A \* B == A * B if this is a central product ([A, B] = 1).   *)
(*               A \x B == A * B if this is a direct product.                 *)
(* [complements to K in G] == set of groups H s.t. K * H = G and K :&: H = 1. *)
(*      [splits G, over K] == [complements to K in G] is not empty.           *)
(*             remgr A B x == the right remainder in B of x mod A, i.e.,      *)
(*                            some element of (A :* x) :&: B.                 *)
(*             divgr A B x == the "division" in B of x by A: for all x,       *)
(*                            x = divgr A B x * remgr A B x.                  *)
(* ++ External products :                                                     *)
(* pairg1, pair1g == the isomorphisms aT1 -> aT1 * aT2, aT2 -> aT1 * aT2.     *)
(*                    (aT1 * aT2 has a direct product group structure.)       *)
(*   sdprod_by to == the semidirect product defined by to : groupAction H K.  *)
(*                   This is a finGroupType; the actual semidirect product is *)
(*                   the total set [set: sdprod_by to] on that type.          *)
(*  sdpair[12] to == the isomorphisms injecting K and H into                  *)
(*                   sdprod_by to = sdpair1 to @* K ><| sdpair2 to @* H.      *)
(* External central products (with identified centers) will be defined later  *)
(* in file center.v.                                                          *)
(* ++ Morphisms on product groups:                                            *)
(*   pprodm nAB fJ fAB == the morphism extending fA and fB on A <*> B when    *)
(*                        nAB : B \subset 'N(A),                              *)
(*                        fJ : {in A & B, morph_actj fA fB}, and              *)
(*                        fAB : {in A :&: B, fA =1 fB}.                       *)
(*     sdprodm defG fJ == the morphism extending fA and fB on G, given        *)
(*                        defG : A ><| B = G and                              *)
(*                        fJ : {in A & B, morph_act 'J 'J fA fB}.             *)
(*     xsdprodm fHKact == the total morphism on sdprod_by to induced by       *)
(*                        fH : {morphism H >-> rT}, fK : {morphism K >-> rT}, *)
(*                        with to : groupAction K H,                          *)
(*                        given fHKact : morph_act to 'J fH fK.               *)
(* cprodm defG cAB fAB == the morphism extending fA and fB on G, when         *)
(*                        defG : A \* B = G,                                  *)
(*                        cAB : fB @* B \subset 'C(fB @* A),                  *)
(*                        and fAB : {in A :&: B, fA =1 fB}.                   *)
(*     dprodm defG cAB == the morphism extending fA and fB on G, when         *)
(*                        defG : A \x B = G and                               *)
(*                        cAB : fA @* B \subset 'C(fA @* A)                   *)
(*        mulgm (x, y) == x * y; mulgm is an isomorphism from setX A B to G   *)
(*                        iff A \x B = G .                                    *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Section Defs.

Variables gT : finGroupType.
Implicit Types A B C : {set gT}.

Definition partial_product A B :=
  if A == 1 then B else if B == 1 then A else
  if [&& group_set A, group_set B & B \subset 'N(A)] then A * B else set0.

Definition semidirect_product A B :=
  if A :&: B \subset 1%G then partial_product A B else set0.

Definition central_product A B :=
  if B \subset 'C(A) then partial_product A B else set0.

Definition direct_product A B :=
  if A :&: B \subset 1%G then central_product A B else set0.

Definition complements_to_in A B :=
  [set K : {group gT} | A :&: K == 1 & A * K == B].

Definition splits_over B A := complements_to_in A B != set0.

(* Product remainder functions -- right variant only. *)
Definition remgr A B x := repr (A :* x :&: B).
Definition divgr A B x := x * (remgr A B x)^-1.

End Defs.

Arguments partial_product _ _%g _%g : clear implicits.
Arguments semidirect_product _ _%g _%g : clear implicits.
Arguments central_product _ _%g _%g : clear implicits.
Arguments complements_to_in _ _%g _%g.
Arguments splits_over _ _%g _%g.
Arguments remgr _ _%g _%g _%g.
Arguments divgr _ _%g _%g _%g.
Arguments direct_product : clear implicits.
Notation pprod := (partial_product _).
Notation sdprod := (semidirect_product _).
Notation cprod := (central_product _).
Notation dprod := (direct_product _).

Notation "G ><| H" := (sdprod G H)%g (at level 40, left associativity).
Notation "G \* H" := (cprod G H)%g (at level 40, left associativity).
Notation "G \x H" := (dprod G H)%g (at level 40, left associativity).

Notation "[ 'complements' 'to' A 'in' B ]" := (complements_to_in A B)
  (at level 0, format "[ 'complements'  'to'  A  'in'  B ]") : group_scope.

Notation "[ 'splits' B , 'over' A ]" := (splits_over B A)
  (at level 0, format "[ 'splits'  B ,  'over'  A ]") : group_scope.

(* Prenex Implicits remgl divgl. *)
Prenex Implicits remgr divgr.

Section InternalProd.

Variable gT : finGroupType.
Implicit Types A B C : {set gT}.
Implicit Types G H K L M : {group gT}.

Local Notation pprod := (partial_product gT).
Local Notation sdprod := (semidirect_product gT) (only parsing).
Local Notation cprod := (central_product gT) (only parsing).
Local Notation dprod := (direct_product gT) (only parsing).

Lemma pprod1g : left_id 1 pprod.
Proof. by move=> A; rewrite /pprod eqxx. Qed.

Lemma pprodg1 : right_id 1 pprod.
Proof. by move=> A; rewrite /pprod eqxx; case: eqP. Qed.

Variant are_groups A B : Prop := AreGroups K H of A = K & B = H.

Lemma group_not0 G : set0 <> G.
Proof. by move/setP/(_ 1); rewrite inE group1. Qed.

Lemma mulg0 : right_zero (@set0 gT) mulg.
Proof.
by move=> A; apply/setP=> x; rewrite inE; apply/imset2P=> [[y z]]; rewrite inE.
Qed.

Lemma mul0g : left_zero (@set0 gT) mulg.
Proof.
by move=> A; apply/setP=> x; rewrite inE; apply/imset2P=> [[y z]]; rewrite inE.
Qed.

Lemma pprodP A B G :
  pprod A B = G -> [/\ are_groups A B, A * B = G & B \subset 'N(A)].
Proof.
have Gnot0 := @group_not0 G; rewrite /pprod; do 2?case: eqP => [-> ->| _].
- by rewrite mul1g norms1; split; first exists 1%G G.
- by rewrite mulg1 sub1G; split; first exists G 1%G.
by case: and3P => // [[gA gB ->]]; split; first exists (Group gA) (Group gB).
Qed.

Lemma pprodE K H : H \subset 'N(K) -> pprod K H = K * H.
Proof.
move=> nKH; rewrite /pprod nKH !groupP /=.
by do 2?case: eqP => [-> | _]; rewrite ?mulg1 ?mul1g.
Qed.

Lemma pprodEY K H : H \subset 'N(K) -> pprod K H = K <*> H.
Proof. by move=> nKH; rewrite pprodE ?norm_joinEr. Qed.

Lemma pprodW A B G : pprod A B = G -> A * B = G. Proof. by case/pprodP. Qed.

Lemma pprodWC A B G : pprod A B = G -> B * A = G.
Proof. by case/pprodP=> _ <- /normC. Qed.

Lemma pprodWY A B G : pprod A B = G -> A <*> B = G.
Proof. by case/pprodP=> [[K H -> ->] <- /norm_joinEr]. Qed.

Lemma pprodJ A B x : pprod A B :^ x = pprod (A :^ x) (B :^ x).
Proof.
rewrite /pprod !conjsg_eq1 !group_setJ normJ conjSg -conjsMg.
by do 3?case: ifP => // _; apply: conj0g.
Qed.

(* Properties of the remainders *)

Lemma remgrMl K B x y : y \in K -> remgr K B (y * x) = remgr K B x.
Proof. by move=> Ky; rewrite {1}/remgr rcosetM rcoset_id. Qed.

Lemma remgrP K B x : (remgr K B x \in K :* x :&: B) = (x \in K * B).
Proof.
set y := _ x; apply/idP/mulsgP=> [|[g b Kg Bb x_gb]].
  rewrite inE rcoset_sym mem_rcoset => /andP[Kxy' By].
  by exists (x * y^-1) y; rewrite ?mulgKV.
by apply: (mem_repr b); rewrite inE rcoset_sym mem_rcoset x_gb mulgK Kg.
Qed.

Lemma remgr1 K H x : x \in K -> remgr K H x = 1.
Proof. by move=> Kx; rewrite /remgr rcoset_id ?repr_group. Qed.

Lemma divgr_eq A B x : x = divgr A B x * remgr A B x.
Proof. by rewrite mulgKV. Qed.

Lemma divgrMl K B x y : x \in K -> divgr K B (x * y) = x * divgr K B y.
Proof. by move=> Hx; rewrite /divgr remgrMl ?mulgA. Qed.

Lemma divgr_id K H x : x \in K -> divgr K H x = x.
Proof. by move=> Kx; rewrite /divgr remgr1 // invg1 mulg1. Qed.

Lemma mem_remgr K B x : x \in K * B -> remgr K B x \in B.
Proof. by rewrite -remgrP => /setIP[]. Qed.

Lemma mem_divgr K B x : x \in K * B -> divgr K B x \in K.
Proof. by rewrite -remgrP inE rcoset_sym mem_rcoset => /andP[]. Qed.

Section DisjointRem.

Variables K H : {group gT}.

Hypothesis tiKH : K :&: H = 1.

Lemma remgr_id x : x \in H -> remgr K H x = x.
Proof.
move=> Hx; apply/eqP; rewrite eq_mulgV1 (sameP eqP set1gP) -tiKH inE.
rewrite -mem_rcoset groupMr ?groupV // -in_setI remgrP.
by apply: subsetP Hx; apply: mulG_subr.
Qed.

Lemma remgrMid x y : x \in K -> y \in H -> remgr K H (x * y) = y.
Proof. by move=> Kx Hy; rewrite remgrMl ?remgr_id. Qed.

Lemma divgrMid x y : x \in K -> y \in H -> divgr K H (x * y) = x.
Proof. by move=> Kx Hy; rewrite /divgr remgrMid ?mulgK. Qed.

End DisjointRem.

(* Intersection of a centraliser with a disjoint product. *)

Lemma subcent_TImulg K H A :
  K :&: H = 1 -> A \subset 'N(K) :&: 'N(H) -> 'C_K(A) * 'C_H(A) = 'C_(K * H)(A).
Proof.
move=> tiKH /subsetIP[nKA nHA]; apply/eqP.
rewrite group_modl ?subsetIr // eqEsubset setSI ?mulSg ?subsetIl //=.
apply/subsetP=> _ /setIP[/mulsgP[x y Kx Hy ->] cAxy].
rewrite inE cAxy mem_mulg // inE Kx /=.
apply/centP=> z Az; apply/commgP/conjg_fixP.
move/commgP/conjg_fixP/(congr1 (divgr K H)): (centP cAxy z Az).
by rewrite conjMg !divgrMid ?memJ_norm // (subsetP nKA, subsetP nHA).
Qed.

(* Complements, and splitting. *)

Lemma complP H A B :
  reflect (A :&: H = 1 /\ A * H = B) (H \in [complements to A in B]).
Proof. by apply: (iffP setIdP); case; split; apply/eqP. Qed.

Lemma splitsP B A :
  reflect (exists H, H \in [complements to A in B]) [splits B, over A].
Proof. exact: set0Pn. Qed.

Lemma complgC H K G :
  (H \in [complements to K in G]) = (K \in [complements to H in G]).
Proof.
rewrite !inE setIC; congr (_ && _).
by apply/eqP/eqP=> defG; rewrite -(comm_group_setP _) // defG groupP.
Qed.

Section NormalComplement.

Variables K H G : {group gT}.

Hypothesis complH_K : H \in [complements to K in G].

Lemma remgrM : K <| G -> {in G &, {morph remgr K H : x y / x * y}}.
Proof.
case/normalP=> _; case/complP: complH_K => tiKH <- nK_KH x y KHx KHy.
rewrite {1}(divgr_eq K H y) mulgA (conjgCV x) {2}(divgr_eq K H x) -2!mulgA.
rewrite mulgA remgrMid //; last by rewrite groupMl mem_remgr.
by rewrite groupMl !(=^~ mem_conjg, nK_KH, mem_divgr).
Qed.

Lemma divgrM : H \subset 'C(K) -> {in G &, {morph divgr K H : x y / x * y}}.
Proof.
move=> cKH; have /complP[_ defG] := complH_K.
have nsKG: K <| G by rewrite -defG -cent_joinEr // normalYl cents_norm.
move=> x y Gx Gy; rewrite {1}/divgr remgrM // invMg -!mulgA (mulgA y).
by congr (_ * _); rewrite -(centsP cKH) ?groupV ?(mem_remgr, mem_divgr, defG).
Qed.

End NormalComplement.

(* Semi-direct product *)

Lemma sdprod1g : left_id 1 sdprod.
Proof. by move=> A; rewrite /sdprod subsetIl pprod1g. Qed.

Lemma sdprodg1 : right_id 1 sdprod.
Proof. by move=> A; rewrite /sdprod subsetIr pprodg1. Qed.

Lemma sdprodP A B G :
  A ><| B = G -> [/\ are_groups A B, A * B = G, B \subset 'N(A) & A :&: B = 1].
Proof.
rewrite /sdprod; case: ifP => [trAB | _ /group_not0[] //].
case/pprodP=> gAB defG nBA; split=> {defG nBA}//.
by case: gAB trAB => H K -> -> /trivgP.
Qed.

Lemma sdprodE K H : H \subset 'N(K) -> K :&: H = 1 -> K ><| H = K * H.
Proof. by move=> nKH tiKH; rewrite /sdprod tiKH subxx pprodE. Qed.

Lemma sdprodEY K H : H \subset 'N(K) -> K :&: H = 1 -> K ><| H = K <*> H.
Proof. by move=> nKH tiKH; rewrite sdprodE ?norm_joinEr. Qed.

Lemma sdprodWpp A B G : A ><| B = G -> pprod A B = G.
Proof. by case/sdprodP=> [[K H -> ->] <- /pprodE]. Qed.

Lemma sdprodW A B G : A ><| B = G -> A * B = G.
Proof. by move/sdprodWpp/pprodW. Qed.

Lemma sdprodWC A B G : A ><| B = G -> B * A = G.
Proof. by move/sdprodWpp/pprodWC. Qed.

Lemma sdprodWY A B G : A ><| B = G -> A <*> B = G.
Proof. by move/sdprodWpp/pprodWY. Qed.

Lemma sdprodJ A B x : (A ><| B) :^ x = A :^ x ><| B :^ x.
Proof.
rewrite /sdprod -conjIg sub_conjg conjs1g -pprodJ.
by case: ifP => _ //; apply: imset0.
Qed.

Lemma sdprod_context G K H : K ><| H = G ->
  [/\ K <| G, H \subset G, K * H = G, H \subset 'N(K) & K :&: H = 1].
Proof.
case/sdprodP=> _ <- nKH tiKH.
by rewrite /normal mulG_subl mulG_subr mulG_subG normG.
Qed.

Lemma sdprod_compl G K H : K ><| H = G -> H \in [complements to K in G].
Proof. by case/sdprodP=> _ mulKH _ tiKH; apply/complP. Qed.

Lemma sdprod_normal_complP G K H :
  K <| G -> reflect (K ><| H = G) (K \in [complements to H in G]).
Proof.
case/andP=> _ nKG; rewrite complgC.
apply: (iffP idP); [case/complP=> tiKH mulKH | exact: sdprod_compl].
by rewrite sdprodE ?(subset_trans _ nKG) // -mulKH mulG_subr.
Qed.

Lemma sdprod_card G A B : A ><| B = G -> (#|A| * #|B|)%N = #|G|.
Proof. by case/sdprodP=> [[H K -> ->] <- _ /TI_cardMg]. Qed.

Lemma sdprod_isom G A B :
    A ><| B = G ->
 {nAB : B \subset 'N(A) | isom B (G / A) (restrm nAB (coset A))}.
Proof.
case/sdprodP=> [[K H -> ->] <- nKH tiKH].
by exists nKH; rewrite quotientMidl quotient_isom.
Qed.

Lemma sdprod_isog G A B : A ><| B = G -> B \isog G / A.
Proof. by case/sdprod_isom=> nAB; apply: isom_isog. Qed.

Lemma sdprod_subr G A B M : A ><| B = G -> M \subset B -> A ><| M = A <*> M.
Proof.
case/sdprodP=> [[K H -> ->] _ nKH tiKH] sMH.
by rewrite sdprodEY ?(subset_trans sMH) //; apply/trivgP; rewrite -tiKH setIS.
Qed.

Lemma index_sdprod G A B : A ><| B = G -> #|B| = #|G : A|.
Proof.
case/sdprodP=> [[K H -> ->] <- _ tiHK].
by rewrite indexMg -indexgI setIC tiHK indexg1.
Qed.

Lemma index_sdprodr G A B M :
  A ><| B = G -> M \subset B -> #|B : M| =  #|G : A <*> M|.
Proof.
move=> defG; case/sdprodP: defG (defG) => [[K H -> ->] mulKH nKH _] defG sMH.
rewrite -!divgS //=; last by rewrite -genM_join gen_subG -mulKH mulgS.
by rewrite -(sdprod_card defG) -(sdprod_card (sdprod_subr defG sMH)) divnMl.
Qed.

Lemma quotient_sdprodr_isom G A B M :
    A ><| B = G -> M <| B ->
  {f : {morphism B / M >-> coset_of (A <*> M)} |
    isom (B / M) (G / (A <*> M)) f
  & forall L, L \subset B -> f @* (L / M) = A <*> L / (A <*> M)}.
Proof.
move=> defG nsMH; have [defA defB]: A = <<A>>%G /\ B = <<B>>%G.
  by have [[K1 H1 -> ->] _ _ _] := sdprodP defG; rewrite /= !genGid.
do [rewrite {}defA {}defB; move: {A}<<A>>%G {B}<<B>>%G => K H] in defG nsMH *.
have [[nKH /isomP[injKH imKH]] sMH] := (sdprod_isom defG, normal_sub nsMH).
have [[nsKG sHG mulKH _ _] nKM] := (sdprod_context defG, subset_trans sMH nKH).
have nsKMG: K <*> M <| G.
  by rewrite -quotientYK // -mulKH -quotientK ?cosetpre_normal ?quotient_normal.
have [/= f inj_f im_f] := third_isom (joing_subl K M) nsKG nsKMG.
rewrite quotientYidl //= -imKH -(restrm_quotientE nKH sMH) in f inj_f im_f.
have /domP[h [_ ker_h _ im_h]]: 'dom (f \o quotm _ nsMH) = H / M.
  by rewrite ['dom _]morphpre_quotm injmK.
have{im_h} im_h L: L \subset H -> h @* (L / M) = K <*> L / (K <*> M).
  move=> sLH; have [sLG sKKM] := (subset_trans sLH sHG, joing_subl K M).
  rewrite im_h morphim_comp morphim_quotm [_ @* L]restrm_quotientE ?im_f //.
  rewrite quotientY ?(normsG sKKM) ?(subset_trans sLG) ?normal_norm //.
  by rewrite (quotientS1 sKKM) joing1G.
exists h => //; apply/isomP; split; last by rewrite im_h //= (sdprodWY defG).
by rewrite ker_h injm_comp ?injm_quotm.
Qed.

Lemma quotient_sdprodr_isog G A B M :
  A ><| B = G -> M <| B -> B / M \isog G / (A <*> M).
Proof.
move=> defG; case/sdprodP: defG (defG) => [[K H -> ->] _ _ _] => defG nsMH.
by have [h /isom_isog->] := quotient_sdprodr_isom defG nsMH.
Qed.

Lemma sdprod_modl A B G H :
  A ><| B = G -> A \subset H -> A ><| (B :&: H) = G :&: H.
Proof.
case/sdprodP=> {A B} [[A B -> ->]] <- nAB tiAB sAH.
rewrite -group_modl ?sdprodE ?subIset ?nAB //.
by rewrite setIA tiAB (setIidPl _) ?sub1G.
Qed.

Lemma sdprod_modr A B G H :
  A ><| B = G -> B \subset H -> (H :&: A) ><| B = H :&: G.
Proof.
case/sdprodP=> {A B}[[A B -> ->]] <- nAB tiAB sAH.
rewrite -group_modr ?sdprodE ?normsI // ?normsG //.
by rewrite -setIA tiAB (setIidPr _) ?sub1G.
Qed.

Lemma subcent_sdprod B C G A :
  B ><| C = G -> A \subset 'N(B) :&: 'N(C) -> 'C_B(A) ><| 'C_C(A) = 'C_G(A).
Proof.
case/sdprodP=> [[H K -> ->] <- nHK tiHK] nHKA {B C G}.
rewrite sdprodE ?subcent_TImulg ?normsIG //.
by rewrite -setIIl tiHK (setIidPl (sub1G _)).
Qed.

Lemma sdprod_recl n G K H K1 :
    #|G| <= n -> K ><| H = G -> K1 \proper K -> H \subset 'N(K1) ->
  exists G1 : {group gT}, [/\ #|G1| < n, G1 \subset G & K1 ><| H = G1].
Proof.
move=> leGn; case/sdprodP=> _ defG nKH tiKH ltK1K nK1H.
have tiK1H: K1 :&: H = 1 by apply/trivgP; rewrite -tiKH setSI ?proper_sub.
exists (K1 <*> H)%G; rewrite /= -defG sdprodE // norm_joinEr //.
rewrite ?mulSg ?proper_sub ?(leq_trans _ leGn) //=.
by rewrite -defG ?TI_cardMg // ltn_pmul2r ?proper_card.
Qed.

Lemma sdprod_recr n G K H H1 :
    #|G| <= n -> K ><| H = G -> H1 \proper H ->
  exists G1 : {group gT}, [/\ #|G1| < n, G1 \subset G & K ><| H1 = G1].
Proof.
move=> leGn; case/sdprodP=> _ defG nKH tiKH ltH1H.
have [sH1H _] := andP ltH1H; have nKH1 := subset_trans sH1H nKH.
have tiKH1: K :&: H1 = 1 by apply/trivgP; rewrite -tiKH setIS.
exists (K <*> H1)%G; rewrite /= -defG sdprodE // norm_joinEr //.
rewrite ?mulgS // ?(leq_trans _ leGn) //=.
by rewrite -defG ?TI_cardMg // ltn_pmul2l ?proper_card.
Qed.

Lemma mem_sdprod G A B x : A ><| B = G -> x \in G ->
  exists y, exists z,
    [/\ y \in A, z \in B, x = y * z &
        {in A & B, forall u t, x = u * t -> u = y /\ t = z}].
Proof.
case/sdprodP=> [[K H -> ->{A B}] <- _ tiKH] /mulsgP[y z Ky Hz ->{x}].
exists y; exists z; split=> // u t Ku Ht eqyzut.
move: (congr1 (divgr K H) eqyzut) (congr1 (remgr K H) eqyzut).
by rewrite !remgrMid // !divgrMid.
Qed.

(* Central product *)

Lemma cprod1g : left_id 1 cprod.
Proof. by move=> A; rewrite /cprod cents1 pprod1g. Qed.

Lemma cprodg1 : right_id 1 cprod.
Proof. by move=> A; rewrite /cprod sub1G pprodg1. Qed.

Lemma cprodP A B G :
  A \* B = G -> [/\ are_groups A B, A * B = G & B \subset 'C(A)].
Proof. by rewrite /cprod; case: ifP => [cAB /pprodP[] | _ /group_not0[]]. Qed.

Lemma cprodE G H : H \subset 'C(G) -> G \* H = G * H.
Proof. by move=> cGH; rewrite /cprod cGH pprodE ?cents_norm. Qed.

Lemma cprodEY G H : H \subset 'C(G) -> G \* H = G <*> H.
Proof. by move=> cGH; rewrite cprodE ?cent_joinEr. Qed.

Lemma cprodWpp A B G : A \* B = G -> pprod A B = G.
Proof. by case/cprodP=> [[K H -> ->] <- /cents_norm/pprodE]. Qed.

Lemma cprodW A B G : A \* B = G -> A * B = G.
Proof. by move/cprodWpp/pprodW. Qed.

Lemma cprodWC A B G : A \* B = G -> B * A = G.
Proof. by move/cprodWpp/pprodWC. Qed.

Lemma cprodWY A B G : A \* B = G -> A <*> B = G.
Proof. by move/cprodWpp/pprodWY. Qed.

Lemma cprodJ A B x : (A \* B) :^ x = A :^ x \* B :^ x.
Proof.
by rewrite /cprod centJ conjSg -pprodJ; case: ifP => _ //; apply: imset0.
Qed.

Lemma cprod_normal2 A B G : A \* B = G -> A <| G /\ B <| G.
Proof.
case/cprodP=> [[K H -> ->] <- cKH]; rewrite -cent_joinEr //.
by rewrite normalYl normalYr !cents_norm // centsC.
Qed.

Lemma bigcprodW I (r : seq I) P F G :
  \big[cprod/1]_(i <- r | P i) F i = G -> \prod_(i <- r | P i) F i = G.
Proof.
elim/big_rec2: _ G => // i A B _ IH G /cprodP[[_ H _ defB] <- _].
by rewrite (IH H) defB.
Qed.

Lemma bigcprodWY I (r : seq I) P F G :
  \big[cprod/1]_(i <- r | P i) F i = G -> << \bigcup_(i <- r | P i) F i >> = G.
Proof.
elim/big_rec2: _ G => [|i A B _ IH G]; first by rewrite gen0.
case/cprodP => [[K H -> defB] <- cKH].
by rewrite -[<<_>>]joing_idr (IH H) ?cent_joinEr -?defB.
Qed.

Lemma triv_cprod A B : (A \* B == 1) = (A == 1) && (B == 1).
Proof.
case A1: (A == 1); first by rewrite (eqP A1) cprod1g.
apply/eqP=> /cprodP[[G H defA ->]] /eqP.
by rewrite defA trivMg -defA A1.
Qed.

Lemma cprod_ntriv A B : A != 1 -> B != 1 ->
  A \* B =
    if [&& group_set A, group_set B & B \subset 'C(A)] then A * B else set0.
Proof.
move=> A1 B1; rewrite /cprod; case: ifP => cAB; rewrite ?cAB ?andbF //=.
by rewrite /pprod -if_neg A1 -if_neg B1 cents_norm.
Qed.

Lemma trivg0 : (@set0 gT == 1) = false.
Proof. by rewrite eqEcard cards0 cards1 andbF. Qed.

Lemma group0 : group_set (@set0 gT) = false.
Proof. by rewrite /group_set inE. Qed.

Lemma cprod0g A : set0 \* A = set0.
Proof. by rewrite /cprod centsC sub0set /pprod group0 trivg0 !if_same. Qed.

Lemma cprodC : commutative cprod.
Proof.
rewrite /cprod => A B; case: ifP => cAB; rewrite centsC cAB // /pprod.
by rewrite andbCA normC !cents_norm // 1?centsC //; do 2!case: eqP => // ->.
Qed.

Lemma cprodA : associative cprod.
Proof.
move=> A B C; case A1: (A == 1); first by rewrite (eqP A1) !cprod1g.
case B1: (B == 1); first by rewrite (eqP B1) cprod1g cprodg1.
case C1: (C == 1); first by rewrite (eqP C1) !cprodg1.
rewrite !(triv_cprod, cprod_ntriv) ?{}A1 ?{}B1 ?{}C1 //.
case: isgroupP => [[G ->{A}] | _]; last by rewrite group0.
case: (isgroupP B) => [[H ->{B}] | _]; last by rewrite group0.
case: (isgroupP C) => [[K ->{C}] | _]; last by rewrite group0 !andbF.
case cGH: (H \subset 'C(G)); case cHK: (K \subset 'C(H)); last first.
- by rewrite group0.
- by rewrite group0 /= mulG_subG cGH andbF.
- by rewrite group0 /= centM subsetI cHK !andbF.
rewrite /= mulgA mulG_subG centM subsetI cGH cHK andbT -(cent_joinEr cHK).
by rewrite -(cent_joinEr cGH) !groupP.
Qed.

Canonical cprod_law := Monoid.Law cprodA cprod1g cprodg1.
Canonical cprod_abelaw := Monoid.ComLaw cprodC.

Lemma cprod_modl A B G H :
  A \* B = G -> A \subset H -> A \* (B :&: H) = G :&: H.
Proof.
case/cprodP=> [[U V -> -> {A B}]] defG cUV sUH.
by rewrite cprodE; [rewrite group_modl ?defG | rewrite subIset ?cUV].
Qed.

Lemma cprod_modr A B G H :
  A \* B = G -> B \subset H -> (H :&: A) \* B = H :&: G.
Proof. by rewrite -!(cprodC B) !(setIC H); apply: cprod_modl. Qed.

Lemma bigcprodYP (I : finType) (P : pred I) (H : I -> {group gT}) :
  reflect (forall i j, P i -> P j -> i != j -> H i \subset 'C(H j))
          (\big[cprod/1]_(i | P i) H i == (\prod_(i | P i) H i)%G).
Proof.
apply: (iffP eqP) => [defG i j Pi Pj neq_ij | cHH].
  rewrite (bigD1 j) // (bigD1 i) /= ?cprodA in defG; last exact/andP.
  by case/cprodP: defG => [[K _ /cprodP[//]]].
set Q := P; have: subpred Q P by [].
elim: {Q}_.+1 {-2}Q (ltnSn #|Q|) => // n IHn Q leQn sQP.
have [i Qi | Q0] := pickP Q; last by rewrite !big_pred0.
rewrite (cardD1x Qi) add1n ltnS !(bigD1 i Qi) /= in leQn *.
rewrite {}IHn {n leQn}// => [|j /andP[/sQP //]].
rewrite bigprodGE cprodEY // gen_subG; apply/bigcupsP=> j /andP[neq_ji Qj].
by rewrite cHH ?sQP.
Qed.

Lemma bigcprodEY I r (P : pred I) (H : I -> {group gT}) G :
    abelian G -> (forall i, P i -> H i \subset G) ->
  \big[cprod/1]_(i <- r | P i) H i = (\prod_(i <- r | P i) H i)%G.
Proof.
move=> cGG sHG; apply/eqP; rewrite !(big_tnth _ _ r).
by apply/bigcprodYP=> i j Pi Pj _; rewrite (sub_abelian_cent2 cGG) ?sHG.
Qed.

Lemma perm_bigcprod (I : eqType) r1 r2 (A : I -> {set gT}) G x :
    \big[cprod/1]_(i <- r1) A i = G -> {in r1, forall i, x i \in A i} ->
    perm_eq r1 r2 ->
  \prod_(i <- r1) x i = \prod_(i <- r2) x i.
Proof.
elim: r1 r2 G => [|i r1 IHr] r2 G defG Ax eq_r12.
  by rewrite perm_eq_sym in eq_r12; rewrite (perm_eq_small _ eq_r12) ?big_nil.
have /rot_to[n r3 Dr2]: i \in r2 by rewrite -(perm_eq_mem eq_r12) mem_head.
transitivity (\prod_(j <- rot n r2) x j).
  rewrite Dr2 !big_cons in defG Ax *; have [[_ G1 _ defG1] _ _] := cprodP defG.
  rewrite (IHr r3 G1) //; first by case/allP/andP: Ax => _ /allP.
  by rewrite -(perm_cons i) -Dr2 perm_eq_sym perm_rot perm_eq_sym.
rewrite -{-2}(cat_take_drop n r2) in eq_r12 *.
rewrite (eq_big_perm _ eq_r12) !big_cat /= !(big_nth i) !big_mkord in defG *.
have /cprodP[[G1 G2 defG1 defG2] _ /centsP-> //] := defG.
  rewrite defG2 -(bigcprodW defG2) mem_prodg // => k _; apply: Ax.
  by rewrite (perm_eq_mem eq_r12) mem_cat orbC mem_nth.
rewrite defG1 -(bigcprodW defG1) mem_prodg // => k _; apply: Ax.
by rewrite (perm_eq_mem eq_r12) mem_cat mem_nth.
Qed.

Lemma reindex_bigcprod (I J : finType) (h : J -> I) P (A : I -> {set gT}) G x :
    {on SimplPred P, bijective h} -> \big[cprod/1]_(i | P i) A i = G -> 
    {in SimplPred P, forall i, x i \in A i} ->
  \prod_(i | P i) x i = \prod_(j | P (h j)) x (h j).
Proof.
case=> h1 hK h1K; rewrite -!(big_filter _ P) filter_index_enum => defG Ax.
rewrite -(big_map h P x) -(big_filter _ P) filter_map filter_index_enum.
apply: perm_bigcprod defG _ _ => [i|]; first by rewrite mem_enum => /Ax.
apply: uniq_perm_eq (enum_uniq P) _ _ => [|i].
  by apply/dinjectiveP; apply: (can_in_inj hK).
rewrite mem_enum; apply/idP/imageP=> [Pi | [j Phj ->//]].
by exists (h1 i); rewrite ?inE h1K.
Qed.

(* Direct product *)

Lemma dprod1g : left_id 1 dprod.
Proof. by move=> A; rewrite /dprod subsetIl cprod1g. Qed.

Lemma dprodg1 : right_id 1 dprod.
Proof. by move=> A; rewrite /dprod subsetIr cprodg1. Qed.

Lemma dprodP A B G :
  A \x B = G -> [/\ are_groups A B, A * B = G, B \subset 'C(A) & A :&: B = 1].
Proof.
rewrite /dprod; case: ifP => trAB; last by case/group_not0.
by case/cprodP=> gAB; split=> //; case: gAB trAB => ? ? -> -> /trivgP.
Qed.

Lemma dprodE G H : H \subset 'C(G) -> G :&: H = 1 -> G \x H = G * H.
Proof. by move=> cGH trGH; rewrite /dprod trGH sub1G cprodE. Qed.

Lemma dprodEY G H : H \subset 'C(G) -> G :&: H = 1 -> G \x H = G <*> H.
Proof. by move=> cGH trGH; rewrite /dprod trGH subxx cprodEY. Qed.

Lemma dprodEcp A B : A :&: B = 1 -> A \x B = A \* B.
Proof. by move=> trAB; rewrite /dprod trAB subxx. Qed.

Lemma dprodEsd A B : B \subset 'C(A) -> A \x B = A ><| B.
Proof. by rewrite /dprod /cprod => ->. Qed.

Lemma dprodWcp A B G : A \x B = G -> A \* B = G.
Proof. by move=> defG; have [_ _ _ /dprodEcp <-] := dprodP defG. Qed.

Lemma dprodWsd A B G : A \x B = G -> A ><| B = G.
Proof. by move=> defG; have [_ _ /dprodEsd <-] := dprodP defG. Qed.

Lemma dprodW A B G : A \x B = G -> A * B = G.
Proof. by move/dprodWsd/sdprodW. Qed.

Lemma dprodWC A B G : A \x B = G -> B * A = G.
Proof. by move/dprodWsd/sdprodWC. Qed.

Lemma dprodWY A B G : A \x B = G -> A <*> B = G.
Proof. by move/dprodWsd/sdprodWY. Qed.

Lemma cprod_card_dprod G A B :
  A \* B = G -> #|A| * #|B| <= #|G| -> A \x B = G.
Proof. by case/cprodP=> [[K H -> ->] <- cKH] /cardMg_TI; apply: dprodE. Qed.

Lemma dprodJ A B x : (A \x B) :^ x = A :^ x \x B :^ x.
Proof.
rewrite /dprod -conjIg sub_conjg conjs1g -cprodJ.
by case: ifP => _ //; apply: imset0.
Qed.

Lemma dprod_normal2 A B G : A \x B = G -> A <| G /\ B <| G.
Proof. by move/dprodWcp/cprod_normal2. Qed.

Lemma dprodYP K H : reflect (K \x H = K <*> H) (H \subset 'C(K) :\: K^#).
Proof.
rewrite subsetD -setI_eq0 setIDA setD_eq0 setIC subG1 /=.
by apply: (iffP andP) => [[cKH /eqP/dprodEY->] | /dprodP[_ _ -> ->]].
Qed.

Lemma dprodC : commutative dprod.
Proof. by move=> A B; rewrite /dprod setIC cprodC. Qed.

Lemma dprodWsdC A B G : A \x B = G -> B ><| A = G.
Proof. by rewrite dprodC => /dprodWsd. Qed.

Lemma dprodA : associative dprod.
Proof.
move=> A B C; case A1: (A == 1); first by rewrite (eqP A1) !dprod1g.
case B1: (B == 1); first by rewrite (eqP B1) dprod1g dprodg1.
case C1: (C == 1); first by rewrite (eqP C1) !dprodg1.
rewrite /dprod (fun_if (cprod A)) (fun_if (cprod^~ C)) -cprodA.
rewrite -(cprodC set0) !cprod0g cprod_ntriv ?B1 ?{}C1 //.
case: and3P B1 => [[] | _ _]; last by rewrite cprodC cprod0g !if_same.
case/isgroupP=> H ->; case/isgroupP=> K -> {B C}; move/cent_joinEr=> eHK H1.
rewrite cprod_ntriv ?trivMg ?{}A1 ?{}H1 // mulG_subG.
case: and4P => [[] | _]; last by rewrite !if_same.
case/isgroupP=> G ->{A} _ cGH _; rewrite cprodEY // -eHK.
case trGH: (G :&: H \subset _); case trHK: (H :&: K \subset _); last first.
- by rewrite !if_same.
- rewrite if_same; case: ifP => // trG_HK; case/negP: trGH.
  by apply: subset_trans trG_HK; rewrite setIS ?joing_subl.
- rewrite if_same; case: ifP => // trGH_K; case/negP: trHK.
  by apply: subset_trans trGH_K; rewrite setSI ?joing_subr.
do 2![case: ifP] => // trGH_K trG_HK; [case/negP: trGH_K | case/negP: trG_HK].
  apply: subset_trans trHK; rewrite subsetI subsetIr -{2}(mulg1 H) -mulGS.
  rewrite setIC group_modl ?joing_subr //= cent_joinEr // -eHK.
  by rewrite -group_modr ?joing_subl //= setIC -(normC (sub1G _)) mulSg.
apply: subset_trans trGH; rewrite subsetI subsetIl -{2}(mul1g H) -mulSG.
rewrite setIC group_modr ?joing_subl //= eHK -(cent_joinEr cGH).
by rewrite -group_modl ?joing_subr //= setIC (normC (sub1G _)) mulgS.
Qed.

Canonical dprod_law := Monoid.Law dprodA dprod1g dprodg1.
Canonical dprod_abelaw := Monoid.ComLaw dprodC.

Lemma bigdprodWcp I (r : seq I) P F G :
  \big[dprod/1]_(i <- r | P i) F i = G -> \big[cprod/1]_(i <- r | P i) F i = G.
Proof.
elim/big_rec2: _ G => // i A B _ IH G /dprodP[[K H -> defB] <- cKH _].
by rewrite (IH H) // cprodE -defB.
Qed.

Lemma bigdprodW I (r : seq I) P F G :
  \big[dprod/1]_(i <- r | P i) F i = G -> \prod_(i <- r | P i) F i = G.
Proof. by move/bigdprodWcp; apply: bigcprodW. Qed.

Lemma bigdprodWY I (r : seq I) P F G :
  \big[dprod/1]_(i <- r | P i) F i = G -> << \bigcup_(i <- r | P i) F i >> = G.
Proof. by move/bigdprodWcp; apply: bigcprodWY. Qed.

Lemma bigdprodYP (I : finType) (P : pred I) (F : I -> {group gT}) :
  reflect (forall i, P i ->
             (\prod_(j | P j && (j != i)) F j)%G \subset 'C(F i) :\: (F i)^#)
          (\big[dprod/1]_(i | P i) F i == (\prod_(i | P i) F i)%G).
Proof.
apply: (iffP eqP) => [defG i Pi | dxG].
  rewrite !(bigD1 i Pi) /= in defG; have [[_ G' _ defG'] _ _ _] := dprodP defG.
  by apply/dprodYP; rewrite -defG defG' bigprodGE (bigdprodWY defG').
set Q := P; have: subpred Q P by [].
elim: {Q}_.+1 {-2}Q (ltnSn #|Q|) => // n IHn Q leQn sQP.
have [i Qi | Q0] := pickP Q; last by rewrite !big_pred0.
rewrite (cardD1x Qi) add1n ltnS !(bigD1 i Qi) /= in leQn *.
rewrite {}IHn {n leQn}// => [|j /andP[/sQP //]].
apply/dprodYP; apply: subset_trans (dxG i (sQP i Qi)); rewrite !bigprodGE.
by apply: genS; apply/bigcupsP=> j /andP[Qj ne_ji]; rewrite (bigcup_max j) ?sQP.
Qed.

Lemma dprod_modl A B G H :
  A \x B = G -> A \subset H -> A \x (B :&: H) = G :&: H.
Proof.
case/dprodP=> [[U V -> -> {A B}]] defG cUV trUV sUH.
rewrite dprodEcp; first by apply: cprod_modl; rewrite ?cprodE.
by rewrite setIA trUV (setIidPl _) ?sub1G.
Qed.

Lemma dprod_modr A B G H :
  A \x B = G -> B \subset H -> (H :&: A) \x B = H :&: G.
Proof. by rewrite -!(dprodC B) !(setIC H); apply: dprod_modl. Qed.

Lemma subcent_dprod B C G A :
   B \x C = G -> A \subset 'N(B) :&: 'N(C) -> 'C_B(A) \x 'C_C(A) = 'C_G(A).
Proof.
move=> defG; have [_ _ cBC _] := dprodP defG; move: defG.
by rewrite !dprodEsd 1?(centSS _ _ cBC) ?subsetIl //; apply: subcent_sdprod.
Qed.

Lemma dprod_card A B G : A \x B = G -> (#|A| * #|B|)%N = #|G|.
Proof. by case/dprodP=> [[H K -> ->] <- _]; move/TI_cardMg. Qed.

Lemma bigdprod_card I r (P : pred I) E G :
    \big[dprod/1]_(i <- r | P i) E i = G ->
  (\prod_(i <- r | P i) #|E i|)%N = #|G|.
Proof.
elim/big_rec2: _ G => [G <- | i A B _ IH G defG]; first by rewrite cards1.
have [[_ H _ defH] _ _ _] := dprodP defG.
by rewrite -(dprod_card defG) (IH H) defH.
Qed.

Lemma bigcprod_card_dprod I r (P : pred I) (A : I -> {set gT}) G :
    \big[cprod/1]_(i <- r | P i) A i = G ->
    \prod_(i <- r | P i) #|A i| <= #|G| ->
  \big[dprod/1]_(i <- r | P i) A i = G.
Proof.
elim: r G => [|i r IHr]; rewrite !(big_nil, big_cons) //; case: ifP => _ // G.
case/cprodP=> [[K H -> defH]]; rewrite defH => <- cKH leKH_G.
have /implyP := leq_trans leKH_G (dvdn_leq _ (dvdn_cardMg K H)).
rewrite muln_gt0 leq_pmul2l !cardG_gt0 //= => /(IHr H defH){defH}defH.
by rewrite defH dprodE // cardMg_TI // -(bigdprod_card defH).
Qed.

Lemma bigcprod_coprime_dprod (I : finType) (P : pred I) (A : I -> {set gT}) G :
    \big[cprod/1]_(i | P i) A i = G ->
    (forall i j, P i -> P j -> i != j -> coprime #|A i| #|A j|) ->
  \big[dprod/1]_(i | P i) A i = G.
Proof.
move=> defG coA; set Q := P in defG *; have: subpred Q P by [].
elim: {Q}_.+1 {-2}Q (ltnSn #|Q|) => // m IHm Q leQm in G defG * => sQP.
have [i Qi | Q0] := pickP Q; last by rewrite !big_pred0 in defG *.
move: defG; rewrite !(bigD1 i Qi) /= => /cprodP[[Hi Gi defAi defGi] <-].
rewrite defAi defGi => cHGi.
have{defGi} defGi: \big[dprod/1]_(j | Q j && (j != i)) A j = Gi.
  by apply: IHm => [||j /andP[/sQP]] //; rewrite (cardD1x Qi) in leQm.
rewrite defGi dprodE // coprime_TIg // -defAi -(bigdprod_card defGi).
elim/big_rec: _ => [|j n /andP[neq_ji Qj] IHn]; first exact: coprimen1.
by rewrite coprime_mulr coprime_sym coA ?sQP.
Qed.

Lemma mem_dprod G A B x : A \x B = G -> x \in G ->
  exists y, exists z,
    [/\ y \in A, z \in B, x = y * z &
        {in A & B, forall u t, x = u * t -> u = y /\ t = z}].
Proof.
move=> defG; have [_ _ cBA _] := dprodP defG.
by apply: mem_sdprod; rewrite -dprodEsd.
Qed.

Lemma mem_bigdprod (I : finType) (P : pred I) F G x :
    \big[dprod/1]_(i | P i) F i = G -> x \in G ->
  exists c, [/\ forall i, P i -> c i \in F i, x = \prod_(i | P i) c i
              & forall e, (forall i, P i -> e i \in F i) ->
                          x = \prod_(i | P i) e i ->
                forall i, P i -> e i = c i].
Proof.
move=> defG; rewrite -(bigdprodW defG) => /prodsgP[c Fc ->].
exists c; split=> // e Fe eq_ce i Pi.
set r := index_enum _ in defG eq_ce.
have: i \in r by rewrite -[r]enumT mem_enum.
elim: r G defG eq_ce => // j r IHr G; rewrite !big_cons inE.
case Pj: (P j); last by case: eqP (IHr G) => // eq_ij; rewrite eq_ij Pj in Pi.
case/dprodP=> [[K H defK defH] _ _]; rewrite defK defH => tiFjH eq_ce.
suffices{i Pi IHr} eq_cej: c j = e j.
  case/predU1P=> [-> //|]; apply: IHr defH _.
  by apply: (mulgI (c j)); rewrite eq_ce eq_cej.
rewrite !(big_nth j) !big_mkord in defH eq_ce.
move/(congr1 (divgr K H)) : eq_ce; move/bigdprodW: defH => defH.
by rewrite !divgrMid // -?defK -?defH ?mem_prodg // => *; rewrite ?Fc ?Fe.
Qed.

End InternalProd.

Arguments complP {gT H A B}.
Arguments splitsP {gT B A}.
Arguments sdprod_normal_complP {gT G K H}.
Arguments dprodYP {gT K H}.
Arguments bigdprodYP {gT I P F}.

Section MorphimInternalProd.

Variables (gT rT : finGroupType) (D : {group gT}) (f : {morphism D >-> rT}).

Section OneProd.

Variables G H K : {group gT}.
Hypothesis sGD : G \subset D.

Lemma morphim_pprod : pprod K H = G -> pprod (f @* K) (f @* H) = f @* G.
Proof.
case/pprodP=> _ defG mKH; rewrite pprodE ?morphim_norms //.
by rewrite -morphimMl ?(subset_trans _ sGD) -?defG // mulG_subl.
Qed.

Lemma morphim_coprime_sdprod :
  K ><| H = G -> coprime #|K| #|H| -> f @* K ><| f @* H = f @* G.
Proof.
rewrite /sdprod => defG coHK; move: defG.
by rewrite !coprime_TIg ?coprime_morph // !subxx; apply: morphim_pprod.
Qed.

Lemma injm_sdprod : 'injm f -> K ><| H = G -> f @* K ><| f @* H = f @* G.
Proof.
move=> inj_f; case/sdprodP=> _ defG nKH tiKH.
by rewrite /sdprod -injmI // tiKH morphim1 subxx morphim_pprod // pprodE.
Qed.

Lemma morphim_cprod : K \* H = G -> f @* K \* f @* H = f @* G.
Proof.
case/cprodP=> _ defG cKH; rewrite /cprod morphim_cents // morphim_pprod //.
by rewrite pprodE // cents_norm // centsC.
Qed.

Lemma injm_dprod : 'injm f -> K \x H = G -> f @* K \x f @* H = f @* G.
Proof.
move=> inj_f; case/dprodP=> _ defG cHK tiKH.
by rewrite /dprod -injmI // tiKH morphim1 subxx morphim_cprod // cprodE.
Qed.

Lemma morphim_coprime_dprod :
  K \x H = G -> coprime #|K| #|H| -> f @* K \x f @* H = f @* G.
Proof.
rewrite /dprod => defG coHK; move: defG.
by rewrite !coprime_TIg ?coprime_morph // !subxx; apply: morphim_cprod.
Qed.

End OneProd.

Implicit Type G : {group gT}.

Lemma morphim_bigcprod I r (P : pred I) (H : I -> {group gT}) G :
    G \subset D -> \big[cprod/1]_(i <- r | P i) H i = G ->
  \big[cprod/1]_(i <- r | P i) f @* H i = f @* G.
Proof.
elim/big_rec2: _ G => [|i fB B Pi def_fB] G sGD defG.
  by rewrite -defG morphim1.
case/cprodP: defG (defG) => [[Hi Gi -> defB] _ _]; rewrite defB => defG.
rewrite (def_fB Gi) //; first exact: morphim_cprod.
by apply: subset_trans sGD; case/cprod_normal2: defG => _ /andP[].
Qed.

Lemma injm_bigdprod I r (P : pred I) (H : I -> {group gT}) G :
    G \subset D -> 'injm f -> \big[dprod/1]_(i <- r | P i) H i = G ->
  \big[dprod/1]_(i <- r | P i) f @* H i = f @* G.
Proof.
move=> sGD injf; elim/big_rec2: _ G sGD => [|i fB B Pi def_fB] G sGD defG.
  by rewrite -defG morphim1.
case/dprodP: defG (defG) => [[Hi Gi -> defB] _ _ _]; rewrite defB => defG.
rewrite (def_fB Gi) //; first exact: injm_dprod.
by apply: subset_trans sGD; case/dprod_normal2: defG => _ /andP[].
Qed.

Lemma morphim_coprime_bigdprod (I : finType) P (H : I -> {group gT}) G :
    G \subset D -> \big[dprod/1]_(i | P i) H i = G ->
    (forall i j, P i -> P j -> i != j -> coprime #|H i| #|H j|) ->
  \big[dprod/1]_(i | P i) f @* H i = f @* G.
Proof.
move=> sGD /bigdprodWcp defG coH; have def_fG := morphim_bigcprod sGD defG.
by apply: bigcprod_coprime_dprod => // i j *; rewrite coprime_morph ?coH.
Qed.

End MorphimInternalProd.

Section QuotientInternalProd.

Variables (gT : finGroupType) (G K H M : {group gT}).

Hypothesis nMG: G \subset 'N(M).

Lemma quotient_pprod : pprod K H = G -> pprod (K / M) (H / M) = G / M.
Proof. exact: morphim_pprod. Qed.

Lemma quotient_coprime_sdprod :
  K ><| H = G -> coprime #|K| #|H| -> (K / M) ><| (H / M) = G / M.
Proof. exact: morphim_coprime_sdprod. Qed.

Lemma quotient_cprod : K \* H = G -> (K / M) \* (H / M) = G / M.
Proof. exact: morphim_cprod. Qed.

Lemma quotient_coprime_dprod :
  K \x H = G -> coprime #|K| #|H| -> (K / M) \x (H / M) = G / M.
Proof. exact: morphim_coprime_dprod. Qed.

End QuotientInternalProd.

Section ExternalDirProd.

Variables gT1 gT2 : finGroupType.

Definition extprod_mulg (x y : gT1 * gT2) := (x.1 * y.1, x.2 * y.2).
Definition extprod_invg (x : gT1 * gT2) := (x.1^-1, x.2^-1).

Lemma extprod_mul1g : left_id (1, 1) extprod_mulg.
Proof. by case=> x1 x2; congr (_, _); apply: mul1g. Qed.

Lemma extprod_mulVg : left_inverse (1, 1) extprod_invg extprod_mulg.
Proof. by move=> x; congr (_, _); apply: mulVg. Qed.

Lemma extprod_mulgA : associative extprod_mulg.
Proof. by move=> x y z; congr (_, _); apply: mulgA. Qed.

Definition extprod_groupMixin :=
  Eval hnf in FinGroup.Mixin extprod_mulgA extprod_mul1g extprod_mulVg.
Canonical extprod_baseFinGroupType :=
  Eval hnf in BaseFinGroupType (gT1 * gT2) extprod_groupMixin.
Canonical prod_group := FinGroupType extprod_mulVg.

Lemma group_setX (H1 : {group gT1}) (H2 : {group gT2}) : group_set (setX H1 H2).
Proof.
apply/group_setP; split; first by rewrite inE !group1.
case=> [x1 x2] [y1 y2]; rewrite !inE; case/andP=> Hx1 Hx2; case/andP=> Hy1 Hy2.
by rewrite /= !groupM.
Qed.

Canonical setX_group H1 H2 := Group (group_setX H1 H2).

Definition pairg1 x : gT1 * gT2 := (x, 1).
Definition pair1g x : gT1 * gT2 := (1, x).

Lemma pairg1_morphM : {morph pairg1 : x y / x * y}.
Proof. by move=> x y /=; rewrite {2}/mulg /= /extprod_mulg /= mul1g. Qed.

Canonical pairg1_morphism := @Morphism _ _ setT _ (in2W pairg1_morphM).

Lemma pair1g_morphM : {morph pair1g : x y / x * y}.
Proof. by move=> x y /=; rewrite {2}/mulg /= /extprod_mulg /= mul1g. Qed.

Canonical pair1g_morphism := @Morphism _ _ setT _ (in2W pair1g_morphM).

Lemma fst_morphM : {morph (@fst gT1 gT2) : x y / x * y}.
Proof. by move=> x y. Qed.

Lemma snd_morphM : {morph (@snd gT1 gT2) : x y / x * y}.
Proof. by move=> x y. Qed.

Canonical fst_morphism := @Morphism _ _ setT _ (in2W fst_morphM).

Canonical snd_morphism := @Morphism _ _ setT _ (in2W snd_morphM).

Lemma injm_pair1g : 'injm pair1g.
Proof. by apply/subsetP=> x /morphpreP[_ /set1P[->]]; apply: set11. Qed.

Lemma injm_pairg1 : 'injm pairg1.
Proof. by apply/subsetP=> x /morphpreP[_ /set1P[->]]; apply: set11. Qed.

Lemma morphim_pairg1 (H1 : {set gT1}) : pairg1 @* H1 = setX H1 1.
Proof. by rewrite -imset2_pair imset2_set1r morphimEsub ?subsetT. Qed.

Lemma morphim_pair1g (H2 : {set gT2}) : pair1g @* H2 = setX 1 H2.
Proof. by rewrite -imset2_pair imset2_set1l morphimEsub ?subsetT. Qed.

Lemma morphim_fstX (H1: {set gT1}) (H2 : {group gT2}) : 
  [morphism of fun x => x.1] @* setX H1 H2 = H1.
Proof.
apply/eqP; rewrite eqEsubset morphimE setTI /=.
apply/andP; split; apply/subsetP=> x.
  by case/imsetP=> x0; rewrite inE; move/andP=> [Hx1 _] ->.
move=> Hx1; apply/imsetP; exists (x, 1); last by trivial.
by rewrite in_setX Hx1 /=.
Qed.

Lemma morphim_sndX (H1: {group gT1}) (H2 : {set gT2}) : 
  [morphism of fun x => x.2] @* setX H1 H2 = H2.
Proof.
apply/eqP; rewrite eqEsubset morphimE setTI /=.
apply/andP; split; apply/subsetP=> x.
  by case/imsetP=> x0; rewrite inE; move/andP=> [_ Hx2] ->.
move=> Hx2; apply/imsetP; exists (1, x); last by [].
by rewrite in_setX Hx2 andbT.
Qed.

Lemma setX_prod (H1 : {set gT1}) (H2 : {set gT2}) :
  setX H1 1 * setX 1 H2 = setX H1 H2.
Proof.
apply/setP=> [[x y]]; rewrite !inE /=.
apply/imset2P/andP=> [[[x1 u1] [v1 y1]] | [Hx Hy]].
  rewrite !inE /= => /andP[Hx1 /eqP->] /andP[/eqP-> Hx] [-> ->].
  by rewrite mulg1 mul1g.
exists (x, 1 : gT2) (1 : gT1, y); rewrite ?inE ?Hx ?eqxx //.
by rewrite /mulg /= /extprod_mulg /= mulg1 mul1g.
Qed.

Lemma setX_dprod (H1 : {group gT1}) (H2 : {group gT2}) :
  setX H1 1 \x setX 1 H2 = setX H1 H2.
Proof.
rewrite dprodE ?setX_prod //.
  apply/centsP=> [[x u]]; rewrite !inE /= => /andP[/eqP-> _] [v y].
  by rewrite !inE /= => /andP[_ /eqP->]; congr (_, _); rewrite ?mul1g ?mulg1.
apply/trivgP; apply/subsetP=> [[x y]]; rewrite !inE /= -!andbA.
by case/and4P=> _ /eqP-> /eqP->; rewrite eqxx.
Qed.

Lemma isog_setX1 (H1 : {group gT1}) : isog H1 (setX H1 1).
Proof.
apply/isogP; exists [morphism of restrm (subsetT H1) pairg1].
  by rewrite injm_restrm ?injm_pairg1.
by rewrite morphim_restrm morphim_pairg1 setIid.
Qed.

Lemma isog_set1X (H2 : {group gT2}) : isog H2 (setX 1 H2).
Proof.
apply/isogP; exists [morphism of restrm (subsetT H2) pair1g].
  by rewrite injm_restrm ?injm_pair1g.
by rewrite morphim_restrm morphim_pair1g setIid.
Qed.

Lemma setX_gen (H1 : {set gT1}) (H2 : {set gT2}) :
  1 \in H1 -> 1 \in H2 -> <<setX H1 H2>> = setX <<H1>> <<H2>>.
Proof.
move=> H1_1 H2_1; apply/eqP.
rewrite eqEsubset gen_subG setXS ?subset_gen //.
rewrite -setX_prod -morphim_pair1g -morphim_pairg1 !morphim_gen ?subsetT //.
by rewrite morphim_pair1g morphim_pairg1 mul_subG // genS // setXS ?sub1set.
Qed.

End ExternalDirProd.

Section ExternalSDirProd.

Variables (aT rT : finGroupType) (D : {group aT}) (R : {group rT}).

(* The pair (a, x) denotes the product sdpair2 a * sdpair1 x *)

Inductive sdprod_by (to : groupAction D R) : predArgType :=
   SdPair (ax : aT * rT) of ax \in setX D R.

Coercion pair_of_sd to (u : sdprod_by to) := let: SdPair ax _ := u in ax.

Variable to : groupAction D R.

Notation sdT := (sdprod_by to).
Notation sdval := (@pair_of_sd to).

Canonical sdprod_subType := Eval hnf in [subType for sdval].
Definition sdprod_eqMixin := Eval hnf in [eqMixin of sdT by <:].
Canonical sdprod_eqType := Eval hnf in EqType sdT sdprod_eqMixin.
Definition sdprod_choiceMixin := [choiceMixin of sdT by <:].
Canonical sdprod_choiceType := ChoiceType sdT sdprod_choiceMixin.
Definition sdprod_countMixin := [countMixin of sdT by <:].
Canonical sdprod_countType := CountType sdT sdprod_countMixin.
Canonical sdprod_subCountType := Eval hnf in [subCountType of sdT].
Definition sdprod_finMixin := [finMixin of sdT by <:].
Canonical sdprod_finType := FinType sdT sdprod_finMixin.
Canonical sdprod_subFinType := Eval hnf in [subFinType of sdT].

Definition sdprod_one := SdPair to (group1 _).

Lemma sdprod_inv_proof (u : sdT) : (u.1^-1, to u.2^-1 u.1^-1) \in setX D R.
Proof.
by case: u => [[a x]] /= /setXP[Da Rx]; rewrite inE gact_stable !groupV ?Da.
Qed.

Definition sdprod_inv u := SdPair to (sdprod_inv_proof u).

Lemma sdprod_mul_proof (u v : sdT) :
  (u.1 * v.1, to u.2 v.1 * v.2) \in setX D R.
Proof.
case: u v => [[a x] /= /setXP[Da Rx]] [[b y] /= /setXP[Db Ry]].
by rewrite inE !groupM //= gact_stable.
Qed.

Definition sdprod_mul u v := SdPair to (sdprod_mul_proof u v).

Lemma sdprod_mul1g : left_id sdprod_one sdprod_mul.
Proof.
move=> u; apply: val_inj; case: u => [[a x] /=]; case/setXP=> Da _.
by rewrite gact1 // !mul1g.
Qed.

Lemma sdprod_mulVg : left_inverse sdprod_one sdprod_inv sdprod_mul.
Proof.
move=> u; apply: val_inj; case: u => [[a x] /=]; case/setXP=> Da _.
by rewrite actKVin ?mulVg.
Qed.

Lemma sdprod_mulgA : associative sdprod_mul.
Proof.
move=> u v w; apply: val_inj; case: u => [[a x]] /=; case/setXP=> Da Rx.
case: v w => [[b y]] /=; case/setXP=> Db Ry [[c z]] /=; case/setXP=> Dc Rz.
by rewrite !(actMin to) // gactM ?gact_stable // !mulgA.
Qed.

Canonical sdprod_groupMixin :=
  FinGroup.Mixin sdprod_mulgA sdprod_mul1g sdprod_mulVg.

Canonical sdprod_baseFinGroupType :=
  Eval hnf in BaseFinGroupType sdT sdprod_groupMixin.

Canonical sdprod_groupType := FinGroupType sdprod_mulVg.

Definition sdpair1 x := insubd sdprod_one (1, x) : sdT.
Definition sdpair2 a := insubd sdprod_one (a, 1) : sdT.

Lemma sdpair1_morphM : {in R &, {morph sdpair1 : x y / x * y}}.
Proof.
move=> x y Rx Ry; apply: val_inj.
by rewrite /= !val_insubd !inE !group1 !groupM ?Rx ?Ry //= mulg1 act1.
Qed.

Lemma sdpair2_morphM : {in D &, {morph sdpair2 : a b / a * b}}.
Proof.
move=> a b Da Db; apply: val_inj.
by rewrite /= !val_insubd !inE !group1 !groupM ?Da ?Db //= mulg1 gact1.
Qed.

Canonical sdpair1_morphism := Morphism sdpair1_morphM.

Canonical sdpair2_morphism := Morphism sdpair2_morphM.

Lemma injm_sdpair1 : 'injm sdpair1.
Proof.
apply/subsetP=> x /setIP[Rx].
by rewrite !inE -val_eqE val_insubd inE Rx group1 /=; case/andP.
Qed.

Lemma injm_sdpair2 : 'injm sdpair2.
Proof.
apply/subsetP=> a /setIP[Da].
by rewrite !inE -val_eqE val_insubd inE Da group1 /=; case/andP.
Qed.

Lemma sdpairE (u : sdT) : u = sdpair2 u.1 * sdpair1 u.2.
Proof.
apply: val_inj; case: u => [[a x] /= /setXP[Da Rx]].
by rewrite !val_insubd !inE Da Rx !(group1, gact1) // mulg1 mul1g.
Qed.

Lemma sdpair_act : {in R & D,
  forall x a, sdpair1 (to x a) = sdpair1 x ^ sdpair2 a}.
Proof.
move=> x a Rx Da; apply: val_inj.
rewrite /= !val_insubd !inE !group1 gact_stable ?Da ?Rx //=.
by rewrite !mul1g mulVg invg1 mulg1 actKVin ?mul1g.
Qed.

Lemma sdpair_setact (G : {set rT}) a : G \subset R -> a \in D ->
  sdpair1 @* (to^~ a @: G) = (sdpair1 @* G) :^ sdpair2 a.
Proof.
move=> sGR Da; have GtoR := subsetP sGR; apply/eqP.
rewrite eqEcard cardJg !(card_injm injm_sdpair1) //; last first.
  by apply/subsetP=> _ /imsetP[x Gx ->]; rewrite gact_stable ?GtoR.
rewrite (card_imset _ (act_inj _ _)) leqnn andbT.
apply/subsetP=> _ /morphimP[xa Rxa /imsetP[x Gx def_xa ->]].
rewrite mem_conjg -morphV // -sdpair_act ?groupV // def_xa actKin //.
by rewrite mem_morphim ?GtoR.
Qed.

Lemma im_sdpair_norm : sdpair2 @* D \subset 'N(sdpair1 @* R).
Proof.
apply/subsetP=> _ /morphimP[a _ Da ->].
rewrite inE -sdpair_setact // morphimS //.
by apply/subsetP=> _ /imsetP[x Rx ->]; rewrite gact_stable.
Qed.

Lemma im_sdpair_TI : (sdpair1 @* R) :&: (sdpair2 @* D) = 1.
Proof.
apply/trivgP; apply/subsetP=> _ /setIP[/morphimP[x _ Rx ->]].
case/morphimP=> a _ Da /eqP; rewrite inE -!val_eqE.
by rewrite !val_insubd !inE Da Rx !group1 /eq_op /= eqxx; case/andP.
Qed.

Lemma im_sdpair : (sdpair1 @* R) * (sdpair2 @* D) = setT.
Proof.
apply/eqP; rewrite -subTset -(normC im_sdpair_norm).
apply/subsetP=> /= u _; rewrite [u]sdpairE.
by case: u => [[a x] /= /setXP[Da Rx]]; rewrite mem_mulg ?mem_morphim.
Qed.

Lemma sdprod_sdpair : sdpair1 @* R ><| sdpair2 @* D = setT.
Proof. by rewrite sdprodE ?(im_sdpair_norm, im_sdpair, im_sdpair_TI). Qed.

Variables (A : {set aT}) (G : {set rT}).

Lemma gacentEsd : 'C_(|to)(A) = sdpair1 @*^-1 'C(sdpair2 @* A).
Proof.
apply/setP=> x; apply/idP/idP.
  case/setIP=> Rx /afixP cDAx; rewrite mem_morphpre //.
  apply/centP=> _ /morphimP[a Da Aa ->]; red.
  by rewrite conjgC -sdpair_act // cDAx // inE Da.
case/morphpreP=> Rx cAx; rewrite inE Rx; apply/afixP=> a /setIP[Da Aa].
apply: (injmP injm_sdpair1); rewrite ?gact_stable /= ?sdpair_act //=.
by rewrite /conjg (centP cAx) ?mulKg ?mem_morphim.
Qed.

Hypotheses (sAD : A \subset D) (sGR : G \subset R).

Lemma astabEsd : 'C(G | to) = sdpair2 @*^-1 'C(sdpair1 @* G).
Proof.
have ssGR := subsetP sGR; apply/setP=> a; apply/idP/idP=> [cGa|].
  rewrite mem_morphpre ?(astab_dom cGa) //.
  apply/centP=> _ /morphimP[x Rx Gx ->]; symmetry.
  by rewrite conjgC -sdpair_act ?(astab_act cGa)  ?(astab_dom cGa).
case/morphpreP=> Da cGa; rewrite !inE Da; apply/subsetP=> x Gx; rewrite inE.
apply/eqP; apply: (injmP injm_sdpair1); rewrite ?gact_stable ?ssGR //=.
by rewrite sdpair_act ?ssGR // /conjg -(centP cGa) ?mulKg ?mem_morphim ?ssGR.
Qed.

Lemma astabsEsd : 'N(G | to) = sdpair2 @*^-1 'N(sdpair1 @* G).
Proof.
apply/setP=> a; apply/idP/idP=> [nGa|].
  have Da := astabs_dom nGa; rewrite mem_morphpre // inE sub_conjg.
  apply/subsetP=> _ /morphimP[x Rx Gx ->].
  by rewrite mem_conjgV -sdpair_act // mem_morphim ?gact_stable ?astabs_act.
case/morphpreP=> Da nGa; rewrite !inE Da; apply/subsetP=> x Gx.
have Rx := subsetP sGR _ Gx; have Rxa: to x a \in R by rewrite gact_stable.
rewrite inE -sub1set -(injmSK injm_sdpair1) ?morphim_set1 ?sub1set //=.
by rewrite sdpair_act ?memJ_norm ?mem_morphim.
Qed.

Lemma actsEsd : [acts A, on G | to] = (sdpair2 @* A \subset 'N(sdpair1 @* G)).
Proof. by rewrite sub_morphim_pre -?astabsEsd. Qed.

End ExternalSDirProd.

Section ProdMorph.

Variables gT rT : finGroupType.
Implicit Types A B : {set gT}.
Implicit Types G H K : {group gT}.
Implicit Types C D : {set rT}.
Implicit Type L : {group rT}.

Section defs.

Variables (A B : {set gT}) (fA fB : gT -> FinGroup.sort rT).

Definition pprodm of B \subset 'N(A) & {in A & B, morph_act 'J 'J fA fB}
                  & {in A :&: B, fA =1 fB} :=
  fun x => fA (divgr A B x) * fB (remgr A B x).

End defs.

Section Props.

Variables H K : {group gT}.
Variables (fH : {morphism H >-> rT}) (fK : {morphism K >-> rT}).
Hypothesis nHK : K \subset 'N(H).
Hypothesis actf : {in H & K, morph_act 'J 'J fH fK}.
Hypothesis eqfHK : {in H :&: K, fH =1 fK}.

Local Notation f := (pprodm nHK actf eqfHK).

Lemma pprodmE x a : x \in H -> a \in K -> f (x * a) = fH x * fK a.
Proof.
move=> Hx Ka; have: x * a \in H * K by rewrite mem_mulg.
rewrite -remgrP inE /f rcoset_sym mem_rcoset /divgr -mulgA groupMl //.
case/andP; move: (remgr H K _) => b Hab Kb; rewrite morphM // -mulgA.
have Kab: a * b^-1 \in K by rewrite groupM ?groupV.
by congr (_ * _); rewrite eqfHK 1?inE ?Hab // -morphM // mulgKV.
Qed.

Lemma pprodmEl : {in H, f =1 fH}.
Proof. by move=> x Hx; rewrite -(mulg1 x) pprodmE // morph1 !mulg1. Qed.

Lemma pprodmEr : {in K, f =1 fK}.
Proof. by move=> a Ka; rewrite -(mul1g a) pprodmE // morph1 !mul1g. Qed.

Lemma pprodmM : {in H <*> K &, {morph f: x y / x * y}}.
Proof.
move=> xa yb; rewrite norm_joinEr //.
move=> /imset2P[x a Ha Ka ->{xa}] /imset2P[y b Hy Kb ->{yb}].
have Hya: y ^ a^-1 \in H by rewrite -mem_conjg (normsP nHK).
rewrite mulgA -(mulgA x) (conjgCV a y) (mulgA x) -mulgA !pprodmE 1?groupMl //.
by rewrite morphM // actf ?groupV ?morphV // morphM // !mulgA mulgKV invgK.
Qed.

Canonical pprodm_morphism := Morphism pprodmM.

Lemma morphim_pprodm A B :
  A \subset H -> B \subset K -> f @* (A * B) = fH @* A * fK @* B.
Proof.
move=> sAH sBK; rewrite [f @* _]morphimEsub /=; last first.
  by rewrite norm_joinEr // mulgSS.
apply/setP=> y; apply/imsetP/idP=> [[_ /mulsgP[x a Ax Ba ->] ->{y}] |].
  have Hx := subsetP sAH x Ax; have Ka := subsetP sBK a Ba.
  by rewrite pprodmE // mem_imset2 ?mem_morphim.
case/mulsgP=> _ _ /morphimP[x Hx Ax ->] /morphimP[a Ka Ba ->] ->{y}.
by exists (x * a); rewrite ?mem_mulg ?pprodmE.
Qed.

Lemma morphim_pprodml A : A \subset H -> f @* A = fH @* A.
Proof.
by move=> sAH; rewrite -{1}(mulg1 A) morphim_pprodm ?sub1G // morphim1 mulg1.
Qed.

Lemma morphim_pprodmr B : B \subset K -> f @* B = fK @* B.
Proof.
by move=> sBK; rewrite -{1}(mul1g B) morphim_pprodm ?sub1G // morphim1 mul1g.
Qed.

Lemma ker_pprodm : 'ker f = [set x * a^-1 | x in H, a in K & fH x == fK a].
Proof.
apply/setP=> y; rewrite 3!inE {1}norm_joinEr //=.
apply/andP/imset2P=> [[/mulsgP[x a Hx Ka ->{y}]]|[x a Hx]].
  rewrite pprodmE // => fxa1.
  by exists x a^-1; rewrite ?invgK // inE groupVr ?morphV // eq_mulgV1 invgK.
case/setIdP=> Kx /eqP fx ->{y}.
by rewrite mem_imset2 ?pprodmE ?groupV ?morphV // fx mulgV.
Qed.

Lemma injm_pprodm :
  'injm f = [&& 'injm fH, 'injm fK & fH @* H :&: fK @* K == fH @* K].
Proof.
apply/idP/and3P=> [injf | [injfH injfK]].
  rewrite eq_sym -{1}morphimIdom -(morphim_pprodml (subsetIl _ _)) injmI //.
  rewrite morphim_pprodml // morphim_pprodmr //=; split=> //.
    apply/injmP=> x y Hx Hy /=; rewrite -!pprodmEl //.
    by apply: (injmP injf); rewrite ?mem_gen ?inE ?Hx ?Hy.
  apply/injmP=> a b Ka Kb /=; rewrite -!pprodmEr //.
  by apply: (injmP injf); rewrite ?mem_gen //; apply/setUP; right.
move/eqP=> fHK; rewrite ker_pprodm; apply/subsetP=> y.
case/imset2P=> x a Hx /setIdP[Ka /eqP fxa] ->.
have: fH x \in fH @* K by rewrite -fHK inE {2}fxa !mem_morphim.
case/morphimP=> z Hz Kz /(injmP injfH) def_x.
rewrite def_x // eqfHK ?inE ?Hz // in fxa.
by rewrite def_x // (injmP injfK _ _ Kz Ka fxa) mulgV set11.
Qed.

End Props.

Section Sdprodm.

Variables H K G : {group gT}.
Variables (fH : {morphism H >-> rT}) (fK : {morphism K >-> rT}).
Hypothesis eqHK_G : H ><| K = G.
Hypothesis actf : {in H & K, morph_act 'J 'J fH fK}.

Lemma sdprodm_norm : K \subset 'N(H).
Proof. by case/sdprodP: eqHK_G. Qed.

Lemma sdprodm_sub : G \subset H <*> K.
Proof. by case/sdprodP: eqHK_G => _ <- nHK _; rewrite norm_joinEr. Qed.

Lemma sdprodm_eqf : {in H :&: K, fH =1 fK}.
Proof.
by case/sdprodP: eqHK_G => _ _ _ -> _ /set1P->; rewrite !morph1.
Qed.

Definition sdprodm :=
  restrm sdprodm_sub (pprodm sdprodm_norm actf sdprodm_eqf).

Canonical sdprodm_morphism := Eval hnf in [morphism of sdprodm].

Lemma sdprodmE a b : a \in H -> b \in K -> sdprodm (a * b) = fH a * fK b.
Proof. exact: pprodmE. Qed.

Lemma sdprodmEl a : a \in H -> sdprodm a = fH a.
Proof. exact: pprodmEl. Qed.

Lemma sdprodmEr b : b \in K -> sdprodm b = fK b.
Proof. exact: pprodmEr. Qed.

Lemma morphim_sdprodm A B :
  A \subset H -> B \subset K -> sdprodm @* (A * B) = fH @* A * fK @* B.
Proof.
move=> sAH sBK; rewrite morphim_restrm /= (setIidPr _) ?morphim_pprodm //.
by case/sdprodP: eqHK_G => _ <- _ _; apply: mulgSS.
Qed.

Lemma im_sdprodm : sdprodm @* G = fH @* H * fK @* K.
Proof. by rewrite -morphim_sdprodm //; case/sdprodP: eqHK_G => _ ->. Qed.

Lemma morphim_sdprodml A : A \subset H -> sdprodm @* A = fH @* A.
Proof.
by move=> sHA; rewrite -{1}(mulg1 A) morphim_sdprodm ?sub1G // morphim1 mulg1.
Qed.

Lemma morphim_sdprodmr B : B \subset K -> sdprodm @* B = fK @* B.
Proof.
by move=> sBK; rewrite -{1}(mul1g B) morphim_sdprodm ?sub1G // morphim1 mul1g.
Qed.

Lemma ker_sdprodm :
  'ker sdprodm = [set a * b^-1 | a in H, b in K & fH a == fK b].
Proof.
rewrite ker_restrm (setIidPr _) ?subIset ?ker_pprodm //; apply/orP; left.
by case/sdprodP: eqHK_G => _ <- nHK _; rewrite norm_joinEr.
Qed.

Lemma injm_sdprodm :
  'injm sdprodm = [&& 'injm fH, 'injm fK & fH @* H :&: fK @* K == 1].
Proof.
rewrite ker_sdprodm -(ker_pprodm sdprodm_norm actf sdprodm_eqf) injm_pprodm.
congr [&& _, _ & _ == _]; have [_ _ _ tiHK] := sdprodP eqHK_G.
by rewrite -morphimIdom tiHK morphim1.
Qed.

End Sdprodm.

Section Cprodm.

Variables H K G : {group gT}.
Variables (fH : {morphism H >-> rT}) (fK : {morphism K >-> rT}).
Hypothesis eqHK_G : H \* K = G.
Hypothesis cfHK : fK @* K \subset 'C(fH @* H).
Hypothesis eqfHK : {in H :&: K, fH =1 fK}.

Lemma cprodm_norm : K \subset 'N(H).
Proof. by rewrite cents_norm //; case/cprodP: eqHK_G. Qed.

Lemma cprodm_sub : G \subset H <*> K.
Proof. by case/cprodP: eqHK_G => _ <- cHK; rewrite cent_joinEr. Qed.

Lemma cprodm_actf : {in H & K, morph_act 'J 'J fH fK}.
Proof.
case/cprodP: eqHK_G => _ _ cHK a b Ha Kb /=.
by rewrite /conjg -(centsP cHK b) // -(centsP cfHK (fK b)) ?mulKg ?mem_morphim.
Qed.

Definition cprodm := restrm cprodm_sub (pprodm cprodm_norm cprodm_actf eqfHK).

Canonical cprodm_morphism := Eval hnf in [morphism of cprodm].

Lemma cprodmE a b : a \in H -> b \in K -> cprodm (a * b) = fH a * fK b.
Proof. exact: pprodmE. Qed.

Lemma cprodmEl a : a \in H -> cprodm a = fH a.
Proof. exact: pprodmEl. Qed.

Lemma cprodmEr b : b \in K -> cprodm b = fK b.
Proof. exact: pprodmEr. Qed.

Lemma morphim_cprodm A B :
  A \subset H -> B \subset K -> cprodm @* (A * B) = fH @* A * fK @* B.
Proof.
move=> sAH sBK; rewrite morphim_restrm /= (setIidPr _) ?morphim_pprodm //.
by case/cprodP: eqHK_G => _ <- _; apply: mulgSS.
Qed.

Lemma im_cprodm : cprodm @* G = fH @* H * fK @* K.
Proof.
by have [_ defHK _] := cprodP eqHK_G; rewrite -{2}defHK morphim_cprodm.
Qed.

Lemma morphim_cprodml A : A \subset H -> cprodm @* A = fH @* A.
Proof.
by move=> sHA; rewrite -{1}(mulg1 A) morphim_cprodm ?sub1G // morphim1 mulg1.
Qed.

Lemma morphim_cprodmr B : B \subset K -> cprodm @* B = fK @* B.
Proof.
by move=> sBK; rewrite -{1}(mul1g B) morphim_cprodm ?sub1G // morphim1 mul1g.
Qed.

Lemma ker_cprodm : 'ker cprodm = [set a * b^-1 | a in H, b in K & fH a == fK b].
Proof.
rewrite ker_restrm (setIidPr _) ?subIset ?ker_pprodm //; apply/orP; left.
by case/cprodP: eqHK_G => _ <- cHK; rewrite cent_joinEr.
Qed.

Lemma injm_cprodm :
  'injm cprodm = [&& 'injm fH, 'injm fK & fH @* H :&: fK @* K == fH @* K].
Proof.
by rewrite ker_cprodm -(ker_pprodm cprodm_norm cprodm_actf eqfHK) injm_pprodm.
Qed.

End Cprodm.

Section Dprodm.

Variables G H K : {group gT}.
Variables (fH : {morphism H >-> rT}) (fK : {morphism K >-> rT}).
Hypothesis eqHK_G : H \x K = G.
Hypothesis cfHK : fK @* K \subset 'C(fH @* H).

Lemma dprodm_cprod : H \* K = G.
Proof.
by rewrite -eqHK_G /dprod; case/dprodP: eqHK_G => _ _ _ ->; rewrite subxx.
Qed.

Lemma dprodm_eqf : {in H :&: K, fH =1 fK}.
Proof. by case/dprodP: eqHK_G => _ _ _ -> _ /set1P->; rewrite !morph1. Qed.

Definition dprodm := cprodm dprodm_cprod cfHK dprodm_eqf.

Canonical dprodm_morphism := Eval hnf in [morphism of dprodm].

Lemma dprodmE a b : a \in H -> b \in K -> dprodm (a * b) = fH a * fK b.
Proof. exact: pprodmE. Qed.

Lemma dprodmEl a : a \in H -> dprodm a = fH a.
Proof. exact: pprodmEl. Qed.

Lemma dprodmEr b : b \in K -> dprodm b = fK b.
Proof. exact: pprodmEr. Qed.

Lemma morphim_dprodm A B :
  A \subset H -> B \subset K -> dprodm @* (A * B) = fH @* A * fK @* B.
Proof. exact: morphim_cprodm. Qed.

Lemma im_dprodm : dprodm @* G = fH @* H * fK @* K.
Proof. exact: im_cprodm. Qed.

Lemma morphim_dprodml A : A \subset H -> dprodm @* A = fH @* A.
Proof. exact: morphim_cprodml. Qed.

Lemma morphim_dprodmr B : B \subset K -> dprodm @* B = fK @* B.
Proof. exact: morphim_cprodmr. Qed.

Lemma ker_dprodm : 'ker dprodm = [set a * b^-1 | a in H, b in K & fH a == fK b].
Proof. exact: ker_cprodm. Qed.

Lemma injm_dprodm :
  'injm dprodm = [&& 'injm fH, 'injm fK & fH @* H :&: fK @* K == 1].
Proof.
rewrite injm_cprodm -(morphimIdom fH K).
by case/dprodP: eqHK_G => _ _ _ ->; rewrite morphim1.
Qed.

End Dprodm.

Lemma isog_dprod A B G C D L :
  A \x B = G -> C \x D = L -> isog A C -> isog B D -> isog G L.
Proof.
move=> defG {C D} /dprodP[[C D -> ->] defL cCD trCD].
case/dprodP: defG (defG) => {A B} [[A B -> ->] defG _ _] dG defC defD.
case/isogP: defC defL cCD trCD => fA injfA <-{C}.
case/isogP: defD => fB injfB <-{D} defL cCD trCD.
apply/isogP; exists (dprodm_morphism dG cCD).
  by rewrite injm_dprodm injfA injfB trCD eqxx.
by rewrite /= -{2}defG morphim_dprodm.
Qed.

End ProdMorph.

Section ExtSdprodm.

Variables gT aT rT : finGroupType.
Variables (H : {group gT}) (K : {group aT}) (to : groupAction K H).
Variables (fH : {morphism H >-> rT}) (fK : {morphism K >-> rT}).

Hypothesis actf : {in H & K, morph_act to 'J fH fK}.

Local Notation fsH := (fH \o invm (injm_sdpair1 to)).
Local Notation fsK := (fK \o invm (injm_sdpair2 to)).
Let DgH := sdpair1 to @* H.
Let DgK := sdpair2 to @* K.

Lemma xsdprodm_dom1 : DgH \subset 'dom fsH.
Proof. by rewrite ['dom _]morphpre_invm. Qed.
Local Notation gH := (restrm xsdprodm_dom1 fsH).

Lemma xsdprodm_dom2 : DgK \subset 'dom fsK.
Proof. by rewrite ['dom _]morphpre_invm. Qed.
Local Notation gK := (restrm xsdprodm_dom2 fsK).

Lemma im_sdprodm1 : gH @* DgH = fH @* H.
Proof. by rewrite morphim_restrm setIid morphim_comp im_invm. Qed.

Lemma im_sdprodm2 : gK @* DgK = fK @* K.
Proof. by rewrite morphim_restrm setIid morphim_comp im_invm. Qed.

Lemma xsdprodm_act : {in DgH & DgK, morph_act 'J 'J gH gK}.
Proof.
move=> fh fk; case/morphimP=> h _ Hh ->{fh}; case/morphimP=> k _ Kk ->{fk}.
by rewrite /= -sdpair_act // /restrm /= !invmE ?actf ?gact_stable.
Qed.

Definition xsdprodm := sdprodm (sdprod_sdpair to) xsdprodm_act.
Canonical xsdprod_morphism := [morphism of xsdprodm].

Lemma im_xsdprodm : xsdprodm @* setT = fH @* H * fK @* K.
Proof. by rewrite -im_sdpair morphim_sdprodm // im_sdprodm1 im_sdprodm2. Qed.

Lemma injm_xsdprodm :
  'injm xsdprodm = [&& 'injm fH, 'injm fK & fH @* H :&: fK @* K == 1].
Proof.
rewrite injm_sdprodm im_sdprodm1 im_sdprodm2 !subG1 /= !ker_restrm !ker_comp.
rewrite !morphpre_invm !morphimIim.
by rewrite !morphim_injm_eq1 ?subsetIl ?injm_sdpair1 ?injm_sdpair2.
Qed.

End ExtSdprodm.

Section DirprodIsom.

Variable gT : finGroupType.
Implicit Types G H : {group gT}.

Definition mulgm : gT * gT -> _ := prod_curry mulg.

Lemma imset_mulgm (A B : {set gT}) : mulgm @: setX A B = A * B.
Proof. by rewrite -curry_imset2X. Qed.

Lemma mulgmP H1 H2 G : reflect (H1 \x H2 = G) (misom (setX H1 H2) G mulgm).
Proof.
apply: (iffP misomP) => [[pM /isomP[injf /= <-]] | ].
  have /dprodP[_ /= defX cH12] := setX_dprod H1 H2.
  rewrite -{4}defX {}defX => /(congr1 (fun A => morphm pM @* A)).
  move/(morphimS (morphm_morphism pM)): cH12 => /=.
  have sH1H: setX H1 1 \subset setX H1 H2 by rewrite setXS ?sub1G.
  have sH2H: setX 1 H2 \subset setX H1 H2 by rewrite setXS ?sub1G.
  rewrite morphim1 injm_cent ?injmI //= subsetI => /andP[_].
  by rewrite !morphimEsub //= !imset_mulgm mulg1 mul1g; apply: dprodE.
case/dprodP=> _ defG cH12 trH12.
have fM: morphic (setX H1 H2) mulgm.
  apply/morphicP=> [[x1 x2] [y1 y2] /setXP[_ Hx2] /setXP[Hy1 _]].
  by rewrite /= mulgA -(mulgA x1) -(centsP cH12 x2) ?mulgA.
exists fM; apply/isomP; split; last by rewrite morphimEsub //= imset_mulgm.
apply/subsetP=> [[x1 x2]]; rewrite !inE /= andbC -eq_invg_mul.
case: eqP => //= <-; rewrite groupV -in_setI trH12 => /set1P->.
by rewrite invg1 eqxx.
Qed.

End DirprodIsom.

Arguments mulgmP {gT H1 H2 G}.
Prenex Implicits mulgm.

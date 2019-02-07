(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrbool ssrfun eqtype ssrnat seq path fintype div.
From mathcomp
Require Import bigop prime finset fingroup morphism automorphism quotient.
From mathcomp
Require Import commutator gproduct gfunctor center gseries cyclic.

(******************************************************************************)
(*   This file defines nilpotent and solvable groups, and give some of their  *)
(* elementary properties; more will be added later (e.g., the nilpotence of   *)
(* p-groups in sylow.v, or the fact that minimal normal subgroups of solvable *)
(* groups are elementary abelian in maximal.v). This file defines:            *)
(*   nilpotent G == G is nilpotent, i.e., [~: H, G] is a proper subgroup of H *)
(*                  for all nontrivial H <| G.                                *)
(*    solvable G == G is solvable, i.e., H^`(1) is a proper subgroup of H for *)
(*                  all nontrivial subgroups H of G.                          *)
(*       'L_n(G) == the nth term of the lower central series, namely          *)
(*                  [~: G, ..., G] (n Gs) if n > 0, with 'L_0(G) = G.         *)
(*                  G is nilpotent iff 'L_n(G) = 1 for some n.                *)
(*       'Z_n(G) == the nth term of the upper central series, i.e.,           *)
(*                  with 'Z_0(G) = 1, 'Z_n.+1(G) / 'Z_n(G) = 'Z(G / 'Z_n(G)). *)
(*   nil_class G == the nilpotence class of G, i.e., the least n such that    *)
(*                  'L_n.+1(G) = 1 (or, equivalently, 'Z_n(G) = G), if G is   *)
(*                  nilpotent; we take nil_class G = #|G| when G is not       *)
(*                  nilpotent, so nil_class G < #|G| iff G is nilpotent.      *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Section SeriesDefs.

Variables (n : nat) (gT : finGroupType) (A : {set gT}).

Definition lower_central_at_rec := iter n (fun B => [~: B, A]) A.

Definition upper_central_at_rec := iter n (fun B => coset B @*^-1 'Z(A / B)) 1.

End SeriesDefs.

(* By convention, the lower central series starts at 1 while the upper series *)
(* starts at 0 (sic).                                                         *)
Definition lower_central_at n := lower_central_at_rec n.-1.

(* Note: 'nosimpl' MUST be used outside of a section -- the end of section    *)
(* "cooking" destroys it.                                                     *)
Definition upper_central_at := nosimpl upper_central_at_rec.

Arguments lower_central_at n%N {gT} A%g.
Arguments upper_central_at n%N {gT} A%g.

Notation "''L_' n ( G )" := (lower_central_at n G)
  (at level 8, n at level 2, format "''L_' n ( G )") : group_scope.

Notation "''Z_' n ( G )" := (upper_central_at n G)
  (at level 8, n at level 2, format "''Z_' n ( G )") : group_scope.

Section PropertiesDefs.

Variables (gT : finGroupType) (A : {set gT}).

Definition nilpotent :=
  [forall (G : {group gT} | G \subset A :&: [~: G, A]), G :==: 1].

Definition nil_class := index 1 (mkseq (fun n => 'L_n.+1(A)) #|A|).

Definition solvable :=
  [forall (G : {group gT} | G \subset A :&: [~: G, G]), G :==: 1].

End PropertiesDefs.

Arguments nilpotent {gT} A%g.
Arguments nil_class {gT} A%g.
Arguments solvable {gT} A%g.

Section NilpotentProps.

Variable gT: finGroupType.
Implicit Types (A B : {set gT}) (G H : {group gT}).

Lemma nilpotent1 : nilpotent [1 gT].
Proof. by apply/forall_inP=> H; rewrite commG1 setIid -subG1. Qed.

Lemma nilpotentS A B : B \subset A -> nilpotent A -> nilpotent B.
Proof.
move=> sBA nilA; apply/forall_inP=> H sHR.
have:= forallP nilA H; rewrite (subset_trans sHR) //.
by apply: subset_trans (setIS _ _) (setSI _ _); rewrite ?commgS.
Qed.

Lemma nil_comm_properl G H A :
    nilpotent G -> H \subset G -> H :!=: 1 -> A \subset 'N_G(H) ->
  [~: H, A] \proper H.
Proof.
move=> nilG sHG ntH; rewrite subsetI properE; case/andP=> sAG nHA.
rewrite (subset_trans (commgS H (subset_gen A))) ?commg_subl ?gen_subG //.
apply: contra ntH => sHR; have:= forallP nilG H; rewrite subsetI sHG.
by rewrite (subset_trans sHR) ?commgS.
Qed.

Lemma nil_comm_properr G A H :
    nilpotent G -> H \subset G -> H :!=: 1 -> A \subset 'N_G(H) ->
  [~: A, H] \proper H.
Proof. by rewrite commGC; apply: nil_comm_properl. Qed.
 
Lemma centrals_nil (s : seq {group gT}) G :
  G.-central.-series 1%G s -> last 1%G s = G -> nilpotent G.
Proof.
move=> cGs defG; apply/forall_inP=> H /subsetIP[sHG sHR].
move: sHG; rewrite -{}defG -subG1 -[1]/(gval 1%G).
elim: s 1%G cGs => //= L s IHs K /andP[/and3P[sRK sKL sLG] /IHs sHL] sHs.
exact: subset_trans sHR (subset_trans (commSg _ (sHL sHs)) sRK).
Qed.

End NilpotentProps.

Section LowerCentral.

Variable gT : finGroupType.
Implicit Types (A B : {set gT}) (G H : {group gT}).

Lemma lcn0 A : 'L_0(A) = A. Proof. by []. Qed.
Lemma lcn1 A : 'L_1(A) = A. Proof. by []. Qed.
Lemma lcnSn n A : 'L_n.+2(A) = [~: 'L_n.+1(A), A]. Proof. by []. Qed.
Lemma lcnSnS n G : [~: 'L_n(G), G] \subset 'L_n.+1(G).
Proof. by case: n => //; apply: der1_subG. Qed.
Lemma lcnE n A : 'L_n.+1(A) = lower_central_at_rec n A.
Proof. by []. Qed.
Lemma lcn2 A : 'L_2(A) = A^`(1). Proof. by []. Qed.

Lemma lcn_group_set n G : group_set 'L_n(G).
Proof. by case: n => [|[|n]]; apply: groupP. Qed.

Canonical lower_central_at_group n G := Group (lcn_group_set n G).

Lemma lcn_char n G : 'L_n(G) \char G.
Proof. by case: n; last elim=> [|n IHn]; rewrite ?char_refl ?lcnSn ?charR. Qed.

Lemma lcn_normal n G : 'L_n(G) <|  G.
Proof. exact/char_normal/lcn_char. Qed.

Lemma lcn_sub n G : 'L_n(G) \subset G.
Proof. exact/char_sub/lcn_char. Qed.

Lemma lcn_norm n G : G \subset 'N('L_n(G)).
Proof. exact/char_norm/lcn_char. Qed.

Lemma lcn_subS n G : 'L_n.+1(G) \subset 'L_n(G).
Proof.
case: n => // n; rewrite lcnSn commGC commg_subr.
by case/andP: (lcn_normal n.+1 G).
Qed.

Lemma lcn_normalS n G : 'L_n.+1(G) <| 'L_n(G).
Proof. by apply: normalS (lcn_normal _ _); rewrite (lcn_subS, lcn_sub). Qed.

Lemma lcn_central n G : 'L_n(G) / 'L_n.+1(G) \subset 'Z(G / 'L_n.+1(G)).
Proof.
case: n => [|n]; first by rewrite trivg_quotient sub1G.
by rewrite subsetI quotientS ?lcn_sub ?quotient_cents2r.
Qed.

Lemma lcn_sub_leq m n G : n <= m -> 'L_m(G) \subset 'L_n(G).
Proof.
by move/subnK <-; elim: {m}(m - n) => // m; apply: subset_trans (lcn_subS _ _).
Qed.

Lemma lcnS n A B : A \subset B -> 'L_n(A) \subset 'L_n(B).
Proof.
by case: n => // n sAB; elim: n => // n IHn; rewrite !lcnSn genS ?imset2S.
Qed.

Lemma lcn_cprod n A B G : A \* B = G -> 'L_n(A) \* 'L_n(B) = 'L_n(G).
Proof.
case: n => // n /cprodP[[H K -> ->{A B}] defG cHK].
have sL := subset_trans (lcn_sub _ _); rewrite cprodE ?(centSS _ _ cHK) ?sL //.
symmetry; elim: n => // n; rewrite lcnSn => ->; rewrite commMG /=; last first.
  by apply: subset_trans (commg_normr _ _); rewrite sL // -defG mulG_subr.
rewrite -!(commGC G) -defG -{1}(centC cHK).
rewrite !commMG ?normsR ?lcn_norm ?cents_norm // 1?centsC //.
by rewrite -!(commGC 'L__(_)) -!lcnSn !(commG1P _) ?mul1g ?sL // centsC.
Qed.

Lemma lcn_dprod n A B G : A \x B = G -> 'L_n(A) \x 'L_n(B) = 'L_n(G).
Proof.
move=> defG; have [[K H defA defB] _ _ tiAB] := dprodP defG.
rewrite !dprodEcp // in defG *; first exact: lcn_cprod.
by rewrite defA defB; apply/trivgP; rewrite -tiAB defA defB setISS ?lcn_sub.
Qed.

Lemma der_cprod n A B G : A \* B = G -> A^`(n) \* B^`(n) = G^`(n).
Proof. by move=> defG; elim: n => {defG}// n; apply: (lcn_cprod 2). Qed.

Lemma der_dprod n A B G : A \x B = G -> A^`(n) \x B^`(n) = G^`(n).
Proof. by move=> defG; elim: n => {defG}// n; apply: (lcn_dprod 2). Qed.

Lemma lcn_bigcprod n I r P (F : I -> {set gT}) G :
    \big[cprod/1]_(i <- r | P i) F i = G ->
  \big[cprod/1]_(i <- r | P i) 'L_n(F i) = 'L_n(G).
Proof.
elim/big_rec2: _ G => [_ <- | i A Z _ IH G dG]; first exact/esym/trivgP/lcn_sub.
by rewrite -(lcn_cprod n dG); have [[_ H _ dH]] := cprodP dG; rewrite dH (IH H).
Qed.

Lemma lcn_bigdprod n I r P (F : I -> {set gT}) G :
    \big[dprod/1]_(i <- r | P i) F i = G ->
  \big[dprod/1]_(i <- r | P i) 'L_n(F i) = 'L_n(G).
Proof.
elim/big_rec2: _ G => [_ <- | i A Z _ IH G dG]; first exact/esym/trivgP/lcn_sub.
by rewrite -(lcn_dprod n dG); have [[_ H _ dH]] := dprodP dG; rewrite dH (IH H).
Qed.

Lemma der_bigcprod n I r P (F : I -> {set gT}) G :
    \big[cprod/1]_(i <- r | P i) F i = G ->
  \big[cprod/1]_(i <- r | P i) (F i)^`(n) = G^`(n).
Proof.
elim/big_rec2: _ G => [_ <- | i A Z _ IH G dG]; first by rewrite gF1.
by rewrite -(der_cprod n dG); have [[_ H _ dH]] := cprodP dG; rewrite dH (IH H).
Qed.

Lemma der_bigdprod n I r P (F : I -> {set gT}) G :
    \big[dprod/1]_(i <- r | P i) F i = G ->
  \big[dprod/1]_(i <- r | P i) (F i)^`(n) = G^`(n).
Proof.
elim/big_rec2: _ G => [_ <- | i A Z _ IH G dG]; first by rewrite gF1.
by rewrite -(der_dprod n dG); have [[_ H _ dH]] := dprodP dG; rewrite dH (IH H).
Qed.

Lemma nilpotent_class G : nilpotent G = (nil_class G < #|G|).
Proof.
rewrite /nil_class; set s := mkseq _ _.
transitivity (1 \in s); last by rewrite -index_mem size_mkseq.
apply/idP/mapP=> {s}/= [nilG | [n _ Ln1]]; last first.
  apply/forall_inP=> H /subsetIP[sHG sHR].
  rewrite -subG1 {}Ln1; elim: n => // n IHn.
  by rewrite (subset_trans sHR) ?commSg.
pose m := #|G|.-1; exists m; first by rewrite mem_iota /= prednK.
rewrite ['L__(G)]card_le1_trivg //= -(subnn m).
elim: {-2}m => [|n]; [by rewrite subn0 prednK | rewrite lcnSn subnS].
case: (eqsVneq 'L_n.+1(G) 1) => [-> | ntLn]; first by rewrite comm1G cards1.
case: (m - n) => [|m' /= IHn]; first by rewrite leqNgt cardG_gt1 ntLn.
rewrite -ltnS (leq_trans (proper_card _) IHn) //.
by rewrite (nil_comm_properl nilG) ?lcn_sub // subsetI subxx lcn_norm.
Qed.

Lemma lcn_nil_classP n G :
  nilpotent G -> reflect ('L_n.+1(G) = 1) (nil_class G <= n).
Proof.
rewrite nilpotent_class /nil_class; set s := mkseq _ _.
set c := index 1 s => lt_c_G; case: leqP => [le_c_n | lt_n_c].
  have Lc1: nth 1 s c = 1 by rewrite nth_index // -index_mem size_mkseq.
  by left; apply/trivgP; rewrite -Lc1 nth_mkseq ?lcn_sub_leq.
right; apply/eqP/negPf; rewrite -(before_find 1 lt_n_c) nth_mkseq //.
exact: ltn_trans lt_n_c lt_c_G.
Qed.

Lemma lcnP G : reflect (exists n, 'L_n.+1(G) = 1) (nilpotent G).
Proof.
apply: (iffP idP) => [nilG | [n Ln1]].
  by exists (nil_class G); apply/lcn_nil_classP.
apply/forall_inP=> H /subsetIP[sHG sHR]; rewrite -subG1 -{}Ln1.
by elim: n => // n IHn; rewrite (subset_trans sHR) ?commSg.
Qed.

Lemma abelian_nil G : abelian G -> nilpotent G.
Proof. by move=> abG; apply/lcnP; exists 1%N; apply/commG1P. Qed.

Lemma nil_class0 G : (nil_class G == 0) = (G :==: 1).
Proof.
apply/idP/eqP=> [nilG | ->].
  by apply/(lcn_nil_classP 0); rewrite ?nilpotent_class (eqP nilG) ?cardG_gt0.
by rewrite -leqn0; apply/(lcn_nil_classP 0); rewrite ?nilpotent1.
Qed.

Lemma nil_class1 G : (nil_class G <= 1) = abelian G.
Proof.
have [-> | ntG] := eqsVneq G 1.
  by rewrite abelian1 leq_eqVlt ltnS leqn0 nil_class0 eqxx orbT.
apply/idP/idP=> cGG.
  apply/commG1P; apply/(lcn_nil_classP 1); rewrite // nilpotent_class.
  by rewrite (leq_ltn_trans cGG) // cardG_gt1.
by apply/(lcn_nil_classP 1); rewrite ?abelian_nil //; apply/commG1P.
Qed.

Lemma cprod_nil A B G : A \* B = G -> nilpotent G = nilpotent A && nilpotent B.
Proof.
move=> defG; case/cprodP: defG (defG) => [[H K -> ->{A B}] defG _] defGc.
apply/idP/andP=> [nilG | [/lcnP[m LmH1] /lcnP[n LnK1]]].
  by rewrite !(nilpotentS _ nilG) // -defG (mulG_subr, mulG_subl).
apply/lcnP; exists (m + n.+1); apply/trivgP.
case/cprodP: (lcn_cprod (m.+1 + n.+1) defGc) => _ <- _.
by rewrite mulG_subG /= -{1}LmH1 -LnK1 !lcn_sub_leq ?leq_addl ?leq_addr.
Qed.

Lemma mulg_nil G H :
  H \subset 'C(G) -> nilpotent (G * H) = nilpotent G && nilpotent H.
Proof. by move=> cGH; rewrite -(cprod_nil (cprodEY cGH)) /= cent_joinEr. Qed.

Lemma dprod_nil A B G : A \x B = G -> nilpotent G = nilpotent A && nilpotent B.
Proof. by case/dprodP=> [[H K -> ->] <- cHK _]; rewrite mulg_nil.
Qed.

Lemma bigdprod_nil I r (P : pred I) (A_ : I -> {set gT}) G :
  \big[dprod/1]_(i <- r | P i) A_ i = G
  -> (forall i, P i -> nilpotent (A_ i)) -> nilpotent G.
Proof.
move=> defG nilA; elim/big_rec: _ => [|i B Pi nilB] in G defG *.
  by rewrite -defG nilpotent1.
have [[_ H _ defB] _ _ _] := dprodP defG.
by rewrite (dprod_nil defG) nilA //= defB nilB.
Qed.

End LowerCentral.

Notation "''L_' n ( G )" := (lower_central_at_group n G) : Group_scope.

Lemma lcn_cont n : GFunctor.continuous (@lower_central_at n).
Proof.
case: n => //; elim=> // n IHn g0T h0T H phi.
by rewrite !lcnSn morphimR ?lcn_sub // commSg ?IHn.
Qed.

Canonical lcn_igFun n := [igFun by lcn_sub^~ n & lcn_cont n].
Canonical lcn_gFun n := [gFun by lcn_cont n].
Canonical lcn_mgFun n := [mgFun by fun _ G H => @lcnS _ n G H].

Section UpperCentralFunctor.

Variable n : nat.
Implicit Type gT : finGroupType.

Lemma ucn_pmap : exists hZ : GFunctor.pmap, @upper_central_at n = hZ.
Proof.
elim: n => [|n' [hZ defZ]]; first by exists trivGfun_pgFun.
by exists [pgFun of @center %% hZ]; rewrite /= -defZ.
Qed.

(* Now extract all the intermediate facts of the last proof. *)

Lemma ucn_group_set gT (G : {group gT}) : group_set 'Z_n(G).
Proof. by have [hZ ->] := ucn_pmap; apply: groupP. Qed.

Canonical upper_central_at_group gT G := Group (@ucn_group_set gT G).

Lemma ucn_sub gT (G : {group gT}) : 'Z_n(G) \subset G.
Proof. by have [hZ ->] := ucn_pmap; apply: gFsub. Qed.

Lemma morphim_ucn : GFunctor.pcontinuous (@upper_central_at n).
Proof. by have [hZ ->] := ucn_pmap; apply: pmorphimF. Qed.

Canonical ucn_igFun := [igFun by ucn_sub & morphim_ucn].
Canonical ucn_gFun := [gFun by morphim_ucn].
Canonical ucn_pgFun := [pgFun by morphim_ucn].

Variable (gT : finGroupType) (G : {group gT}).

Lemma ucn_char : 'Z_n(G) \char G. Proof. exact: gFchar. Qed.
Lemma ucn_norm : G \subset 'N('Z_n(G)). Proof. exact: gFnorm. Qed.
Lemma ucn_normal : 'Z_n(G) <| G. Proof. exact: gFnormal. Qed.

End UpperCentralFunctor.

Notation "''Z_' n ( G )" := (upper_central_at_group n G) : Group_scope.

Section UpperCentral.

Variable gT : finGroupType.
Implicit Types (A B : {set gT}) (G H : {group gT}).

Lemma ucn0 A : 'Z_0(A) = 1.
Proof. by []. Qed.

Lemma ucnSn n A : 'Z_n.+1(A) = coset 'Z_n(A) @*^-1 'Z(A / 'Z_n(A)).
Proof. by []. Qed.

Lemma ucnE n A : 'Z_n(A) = upper_central_at_rec n A.
Proof. by []. Qed.

Lemma ucn_subS n G : 'Z_n(G) \subset 'Z_n.+1(G).
Proof. by rewrite -{1}['Z_n(G)]ker_coset morphpreS ?sub1G. Qed.

Lemma ucn_sub_geq m n G : n >= m -> 'Z_m(G) \subset 'Z_n(G).
Proof.
move/subnK <-; elim: {n}(n - m) => // n IHn.
exact: subset_trans (ucn_subS _ _).
Qed.

Lemma ucn_central n G : 'Z_n.+1(G) / 'Z_n(G) = 'Z(G / 'Z_n(G)).
Proof. by rewrite ucnSn cosetpreK. Qed.

Lemma ucn_normalS n G : 'Z_n(G) <| 'Z_n.+1(G).
Proof. by rewrite (normalS _ _ (ucn_normal n G)) ?ucn_subS ?ucn_sub. Qed.

Lemma ucn_comm n G : [~: 'Z_n.+1(G), G] \subset 'Z_n(G).
Proof.
rewrite -quotient_cents2 ?normal_norm ?ucn_normal ?ucn_normalS //.
by rewrite ucn_central subsetIr.
Qed.

Lemma ucn1 G : 'Z_1(G) = 'Z(G).
Proof.
apply: (quotient_inj (normal1 _) (normal1 _)).
by rewrite /= (ucn_central 0) -injmF ?norms1 ?coset1_injm.
Qed.

Lemma ucnSnR n G : 'Z_n.+1(G) = [set x in G | [~: [set x], G] \subset 'Z_n(G)].
Proof.
apply/setP=> x; rewrite inE -(setIidPr (ucn_sub n.+1 G)) inE ucnSn.
case Gx: (x \in G) => //=; have nZG := ucn_norm n G.
rewrite -sub1set -sub_quotient_pre -?quotient_cents2 ?sub1set ?(subsetP nZG) //.
by rewrite subsetI quotientS ?sub1set.
Qed.

Lemma ucn_cprod n A B G : A \* B = G -> 'Z_n(A) \* 'Z_n(B) = 'Z_n(G).
Proof.
case/cprodP=> [[H K -> ->{A B}] mulHK cHK].
elim: n => [|n /cprodP[_ /= defZ cZn]]; first exact: cprod1g.
set Z := 'Z_n(G) in defZ cZn; rewrite (ucnSn n G) /= -/Z.
have /mulGsubP[nZH nZK]: H * K \subset 'N(Z) by rewrite mulHK gFnorm.
have <-: 'Z(H / Z) * 'Z(K / Z) = 'Z(G / Z).
  by rewrite -mulHK quotientMl // center_prod ?quotient_cents.
have ZquoZ (B A : {group gT}):
  B \subset 'C(A) -> 'Z_n(A) * 'Z_n(B) = Z -> 'Z(A / Z) = 'Z_n.+1(A) / Z.
- move=> cAB {defZ}defZ; have cAZnB: 'Z_n(B) \subset 'C(A) := gFsub_trans _ cAB.
  have /second_isom[/=]: A \subset 'N(Z).
    by rewrite -defZ normsM ?gFnorm ?cents_norm // centsC.
  suffices ->: Z :&: A = 'Z_n(A).
    by move=> f inj_f im_f; rewrite -!im_f ?gFsub // ucn_central injm_center.
  rewrite -defZ -group_modl ?gFsub //; apply/mulGidPl.
  have [-> | n_gt0] := posnP n; first exact: subsetIl.
  by apply: subset_trans (ucn_sub_geq A n_gt0); rewrite /= setIC ucn1 setIS.
rewrite (ZquoZ H K) 1?centsC 1?(centC cZn) // {ZquoZ}(ZquoZ K H) //.
have cZn1: 'Z_n.+1(K) \subset 'C('Z_n.+1(H)) by apply: centSS cHK; apply: gFsub.
rewrite -quotientMl ?quotientK ?mul_subG ?gFsub_trans //=.
rewrite cprodE // -cent_joinEr ?mulSGid //= cent_joinEr //= -/Z.
by rewrite -defZ mulgSS ?ucn_subS.
Qed.

Lemma ucn_dprod n A B G : A \x B = G -> 'Z_n(A) \x 'Z_n(B) = 'Z_n(G).
Proof.
move=> defG; have [[K H defA defB] _ _ tiAB] := dprodP defG.
rewrite !dprodEcp // in defG *; first exact: ucn_cprod.
by rewrite defA defB; apply/trivgP; rewrite -tiAB defA defB setISS ?ucn_sub.
Qed.

Lemma ucn_bigcprod n I r P (F : I -> {set gT}) G :
    \big[cprod/1]_(i <- r | P i) F i = G ->
  \big[cprod/1]_(i <- r | P i) 'Z_n(F i) = 'Z_n(G).
Proof.
elim/big_rec2: _ G => [_ <- | i A Z _ IH G dG]; first by rewrite gF1.
by rewrite -(ucn_cprod n dG); have [[_ H _ dH]] := cprodP dG; rewrite dH (IH H).
Qed.

Lemma ucn_bigdprod n I r P (F : I -> {set gT}) G :
    \big[dprod/1]_(i <- r | P i) F i = G ->
  \big[dprod/1]_(i <- r | P i) 'Z_n(F i) = 'Z_n(G).
Proof.
elim/big_rec2: _ G => [_ <- | i A Z _ IH G dG]; first by rewrite gF1.
by rewrite -(ucn_dprod n dG); have [[_ H _ dH]] := dprodP dG; rewrite dH (IH H).
Qed.

Lemma ucn_lcnP n G : ('L_n.+1(G) == 1) = ('Z_n(G) == G).
Proof.
rewrite !eqEsubset sub1G ucn_sub /= andbT -(ucn0 G).
elim: {1 3}n 0 (addn0 n) => [j <- //|i IHi j].
rewrite addSnnS => /IHi <- {IHi}; rewrite ucnSn lcnSn.
rewrite -sub_morphim_pre ?gFsub_trans ?gFnorm_trans // subsetI.
by rewrite morphimS ?gFsub // quotient_cents2 ?gFsub_trans ?gFnorm_trans.
Qed.

Lemma ucnP G : reflect (exists n, 'Z_n(G) = G) (nilpotent G).
Proof.
apply: (iffP (lcnP G)) => -[n /eqP-clGn];
  by exists n; apply/eqP; rewrite ucn_lcnP in clGn *.
Qed.

Lemma ucn_nil_classP n G :
  nilpotent G -> reflect ('Z_n(G) = G) (nil_class G <= n).
Proof.
move=> nilG; rewrite (sameP (lcn_nil_classP n nilG) eqP) ucn_lcnP; apply: eqP.
Qed.

Lemma ucn_id n G : 'Z_n('Z_n(G)) = 'Z_n(G).
Proof. exact: gFid. Qed.

Lemma ucn_nilpotent n G : nilpotent 'Z_n(G).
Proof. by apply/ucnP; exists n; rewrite ucn_id. Qed.

Lemma nil_class_ucn n G : nil_class 'Z_n(G) <= n.
Proof. by apply/ucn_nil_classP; rewrite ?ucn_nilpotent ?ucn_id. Qed.

End UpperCentral.

Section MorphNil.

Variables (aT rT : finGroupType) (D : {group aT}) (f : {morphism D >-> rT}).
Implicit Type G : {group aT}.

Lemma morphim_lcn n G : G \subset D -> f @* 'L_n(G) = 'L_n(f @* G).
Proof.
move=> sHG; case: n => //; elim=> // n IHn.
by rewrite !lcnSn -IHn morphimR // (subset_trans _ sHG) // lcn_sub.
Qed.

Lemma injm_ucn n G : 'injm f -> G \subset D -> f @* 'Z_n(G) = 'Z_n(f @* G).
Proof. exact: injmF. Qed.

Lemma morphim_nil G : nilpotent G -> nilpotent (f @* G).
Proof.
case/ucnP=> n ZnG; apply/ucnP; exists n; apply/eqP.
by rewrite eqEsubset ucn_sub /= -{1}ZnG morphim_ucn.
Qed.

Lemma injm_nil G : 'injm f -> G \subset D -> nilpotent (f @* G) = nilpotent G.
Proof.
move=> injf sGD; apply/idP/idP; last exact: morphim_nil.
case/ucnP=> n; rewrite -injm_ucn // => /injm_morphim_inj defZ.
by apply/ucnP; exists n; rewrite defZ ?gFsub_trans.
Qed.

Lemma nil_class_morphim G : nilpotent G -> nil_class (f @* G) <= nil_class G.
Proof.
move=> nilG; rewrite (sameP (ucn_nil_classP _ (morphim_nil nilG)) eqP) /=.
by rewrite eqEsubset ucn_sub -{1}(ucn_nil_classP _ nilG (leqnn _)) morphim_ucn.
Qed.

Lemma nil_class_injm G :
  'injm f -> G \subset D -> nil_class (f @* G) = nil_class G.
Proof.
move=> injf sGD; case nilG: (nilpotent G).
  apply/eqP; rewrite eqn_leq nil_class_morphim //.
  rewrite (sameP (lcn_nil_classP _ nilG) eqP) -subG1.
  rewrite -(injmSK injf) ?gFsub_trans // morphim1.
  by rewrite morphim_lcn // (lcn_nil_classP _ _ (leqnn _)) //= injm_nil.
transitivity #|G|; apply/eqP; rewrite eqn_leq.
  rewrite -(card_injm injf sGD) (leq_trans (index_size _ _)) ?size_mkseq //.
  by rewrite leqNgt -nilpotent_class injm_nil ?nilG.
rewrite (leq_trans (index_size _ _)) ?size_mkseq // leqNgt -nilpotent_class.
by rewrite nilG.
Qed.

End MorphNil.

Section QuotientNil.

Variables gT : finGroupType.
Implicit Types (rT : finGroupType) (G H : {group gT}).

Lemma quotient_ucn_add m n G : 'Z_(m + n)(G) / 'Z_n(G) = 'Z_m(G / 'Z_n(G)).
Proof.
elim: m => [|m IHm]; first exact: trivg_quotient.
apply/setP=> Zx; have [x Nx ->{Zx}] := cosetP Zx.
have [sZG nZG] := andP (ucn_normal n G).
rewrite (ucnSnR m) inE -!sub1set -morphim_set1 //= -quotientR ?sub1set // -IHm.
rewrite !quotientSGK ?(ucn_sub_geq, leq_addl, comm_subG _ nZG, sub1set) //=.
by rewrite addSn /= ucnSnR inE.
Qed.

Lemma isog_nil rT G (L : {group rT}) : G \isog L -> nilpotent G = nilpotent L.
Proof. by case/isogP=> f injf <-; rewrite injm_nil. Qed.

Lemma isog_nil_class rT G (L : {group rT}) :
  G \isog L -> nil_class G = nil_class L.
Proof. by case/isogP=> f injf <-; rewrite nil_class_injm. Qed.

Lemma quotient_nil G H : nilpotent G -> nilpotent (G / H).
Proof. exact: morphim_nil. Qed.
  
Lemma quotient_center_nil G : nilpotent (G / 'Z(G)) = nilpotent G.
Proof.
rewrite -ucn1; apply/idP/idP; last exact: quotient_nil.
case/ucnP=> c nilGq; apply/ucnP; exists c.+1; have nsZ1G := ucn_normal 1 G.
apply: (quotient_inj _ nsZ1G); last by rewrite /= -(addn1 c) quotient_ucn_add.
by rewrite (normalS _ _ nsZ1G) ?ucn_sub ?ucn_sub_geq.
Qed.

Lemma nil_class_quotient_center G :
  nilpotent (G) -> nil_class (G / 'Z(G)) = (nil_class G).-1.
Proof.
move=> nilG; have nsZ1G := ucn_normal 1 G.
apply/eqP; rewrite -ucn1 eqn_leq; apply/andP; split.
  apply/ucn_nil_classP; rewrite ?quotient_nil //= -quotient_ucn_add ucn1.
  by rewrite (ucn_nil_classP _ _ _) ?addn1 ?leqSpred.
rewrite -subn1 leq_subLR addnC; apply/ucn_nil_classP => //=.
apply: (quotient_inj _ nsZ1G) => /=.
  by apply: normalS (ucn_sub _ _) nsZ1G; rewrite /= addnS ucn_sub_geq.
by rewrite quotient_ucn_add; apply/ucn_nil_classP; rewrite //= quotient_nil.
Qed.

Lemma nilpotent_sub_norm G H :
  nilpotent G -> H \subset G -> 'N_G(H) \subset H -> G :=: H.
Proof.
move=> nilG sHG sNH; apply/eqP; rewrite eqEsubset sHG andbT; apply/negP=> nsGH.
have{nsGH} [i sZH []]: exists2 i, 'Z_i(G) \subset H & ~ 'Z_i.+1(G) \subset H.
  case/ucnP: nilG => n ZnG; rewrite -{}ZnG in nsGH.
  elim: n => [|i IHi] in nsGH *; first by rewrite sub1G in nsGH.
  by case sZH: ('Z_i(G) \subset H); [exists i | apply: IHi; rewrite sZH].
apply: subset_trans sNH; rewrite subsetI ucn_sub -commg_subr.
by apply: subset_trans sZH; apply: subset_trans (ucn_comm i G); apply: commgS.
Qed.

Lemma nilpotent_proper_norm G H :
  nilpotent G -> H \proper G -> H \proper 'N_G(H).
Proof.
move=> nilG; rewrite properEneq properE subsetI normG => /andP[neHG sHG].
by rewrite sHG; apply: contra neHG => /(nilpotent_sub_norm nilG)->.
Qed.

Lemma nilpotent_subnormal G H : nilpotent G -> H \subset G -> H <|<| G.
Proof.
move=> nilG; elim: {H}_.+1 {-2}H (ltnSn (#|G| - #|H|)) => // m IHm H.
rewrite ltnS => leGHm sHG.
have [->|] := eqVproper sHG; first exact: subnormal_refl.
move/(nilpotent_proper_norm nilG); set K := 'N_G(H) => prHK.
have snHK: H <|<| K by rewrite normal_subnormal ?normalSG.
have sKG: K \subset G by rewrite subsetIl.
apply: subnormal_trans snHK (IHm _ (leq_trans _ leGHm) sKG).
by rewrite ltn_sub2l ?proper_card ?(proper_sub_trans prHK).
Qed.

Lemma TI_center_nil G H : nilpotent G -> H <| G -> H :&: 'Z(G) = 1 -> H :=: 1.
Proof.
move=> nilG /andP[sHG nHG] tiHZ.
rewrite -{1}(setIidPl sHG); have{nilG} /ucnP[n <-] := nilG.
elim: n => [|n IHn]; apply/trivgP; rewrite ?subsetIr // -tiHZ.
rewrite [H :&: 'Z(G)]setIA subsetI setIS ?ucn_sub //= (sameP commG1P trivgP).
rewrite -commg_subr commGC in nHG.
rewrite -IHn subsetI (subset_trans _ nHG) ?commSg ?subsetIl //=.
by rewrite (subset_trans _ (ucn_comm n G)) ?commSg ?subsetIr.
Qed.

Lemma meet_center_nil G H :
  nilpotent G -> H <| G -> H :!=: 1 -> H :&: 'Z(G) != 1.
Proof. by move=> nilG nsHG; apply: contraNneq => /TI_center_nil->. Qed.

Lemma center_nil_eq1 G : nilpotent G -> ('Z(G) == 1) = (G :==: 1).
Proof.
move=> nilG; apply/eqP/eqP=> [Z1 | ->]; last exact: center1.
by rewrite (TI_center_nil nilG) // (setIidPr (center_sub G)).
Qed.

Lemma cyclic_nilpotent_quo_der1_cyclic G :
  nilpotent G -> cyclic (G / G^`(1)) -> cyclic G.
Proof.
move=> nG; rewrite (isog_cyclic (quotient1_isog G)).
have [-> // | ntG' cGG'] := (eqVneq G^`(1) 1)%g.
suffices: 'L_2(G) \subset G :&: 'L_3(G) by move/(eqfun_inP nG)=> <-.
rewrite subsetI lcn_sub /= -quotient_cents2 ?lcn_norm //.
apply: cyclic_factor_abelian (lcn_central 2 G) _.
by rewrite (isog_cyclic (third_isog _ _ _)) ?lcn_normal // lcn_subS.
Qed.

End QuotientNil.

Section Solvable.

Variable gT : finGroupType.
Implicit Types G H : {group gT}.

Lemma nilpotent_sol G : nilpotent G -> solvable G.
Proof.
move=> nilG; apply/forall_inP=> H /subsetIP[sHG sHH'].
by rewrite (forall_inP nilG) // subsetI sHG (subset_trans sHH') ?commgS.
Qed.

Lemma abelian_sol G : abelian G -> solvable G.
Proof. by move/abelian_nil/nilpotent_sol. Qed.

Lemma solvable1 : solvable [1 gT]. Proof. exact: abelian_sol (abelian1 gT). Qed.

Lemma solvableS G H : H \subset G -> solvable G -> solvable H.
Proof.
move=> sHG solG; apply/forall_inP=> K /subsetIP[sKH sKK'].
by rewrite (forall_inP solG) // subsetI (subset_trans sKH).
Qed.

Lemma sol_der1_proper G H :
  solvable G -> H \subset G -> H :!=: 1 -> H^`(1) \proper H.
Proof.
move=> solG sHG ntH; rewrite properE comm_subG //; apply: implyP ntH.
by have:= forallP solG H; rewrite subsetI sHG implybNN.
Qed.

Lemma derivedP G : reflect (exists n, G^`(n) = 1) (solvable G).
Proof.
apply: (iffP idP) => [solG | [n solGn]]; last first.
  apply/forall_inP=> H /subsetIP[sHG sHH'].
  rewrite -subG1 -{}solGn; elim: n => // n IHn.
  exact: subset_trans sHH' (commgSS _ _).
suffices IHn n: #|G^`(n)| <= (#|G|.-1 - n).+1.
  by exists #|G|.-1; rewrite [G^`(_)]card_le1_trivg ?(leq_trans (IHn _)) ?subnn.
elim: n => [|n IHn]; first by rewrite subn0 prednK.
rewrite dergSn subnS -ltnS.
have [-> | ntGn] := eqVneq G^`(n) 1; first by rewrite commG1 cards1.
case: (_ - _) IHn => [|n']; first by rewrite leqNgt cardG_gt1 ntGn.
by apply: leq_trans (proper_card _); apply: sol_der1_proper (der_sub _ _) _.
Qed.

End Solvable.

Section MorphSol.

Variables (gT rT : finGroupType) (D : {group gT}) (f : {morphism D >-> rT}).
Variable G : {group gT}.

Lemma morphim_sol : solvable G -> solvable (f @* G).
Proof.
move/(solvableS (subsetIr D G)); case/derivedP=> n Gn1; apply/derivedP.
by exists n; rewrite /= -morphimIdom -morphim_der ?subsetIl // Gn1 morphim1.
Qed.

Lemma injm_sol : 'injm f -> G \subset D -> solvable (f @* G) = solvable G.
Proof.
move=> injf sGD; apply/idP/idP; last exact: morphim_sol.
case/derivedP=> n Gn1; apply/derivedP; exists n; apply/trivgP.
by rewrite -(injmSK injf) ?gFsub_trans ?morphim_der // Gn1 morphim1.
Qed.

End MorphSol.

Section QuotientSol.

Variables gT rT : finGroupType.
Implicit Types G H K : {group gT}.

Lemma isog_sol G (L : {group rT}) : G \isog L -> solvable G = solvable L.
Proof. by case/isogP=> f injf <-; rewrite injm_sol. Qed.

Lemma quotient_sol G H : solvable G -> solvable (G / H).
Proof. exact: morphim_sol. Qed.

Lemma series_sol G H : H <| G -> solvable G = solvable H && solvable (G / H).
Proof.
case/andP=> sHG nHG; apply/idP/andP=> [solG | [solH solGH]].
  by rewrite quotient_sol // (solvableS sHG).
apply/forall_inP=> K /subsetIP[sKG sK'K].
suffices sKH: K \subset H by rewrite (forall_inP solH) // subsetI sKH.
have nHK := subset_trans sKG nHG.
rewrite -quotient_sub1 // subG1 (forall_inP solGH) //.
by rewrite subsetI -morphimR ?morphimS.
Qed.

Lemma metacyclic_sol G : metacyclic G -> solvable G.
Proof.
case/metacyclicP=> K [cycK nsKG cycGq].
by rewrite (series_sol nsKG) !abelian_sol ?cyclic_abelian.
Qed.

End QuotientSol.

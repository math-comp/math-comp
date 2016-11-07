(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrfun ssrbool choice eqtype ssrnat seq div fintype.
From mathcomp
Require Import tuple finfun bigop fingroup perm ssralg zmodp matrix mxalgebra.
From mathcomp
Require Import poly polydiv mxpoly binomial.

(******************************************************************************)
(* This file provides additional primitives and theory for bivariate          *)
(* polynomials (polynomials of two variables), represented as polynomials     *)
(* with (univariate) polynomial coefficients :                                *)
(*            'Y == the (generic) second variable (:= 'X%:P).                 *)
(*          p^:P == the bivariate polynomial p['X], for p univariate.         *)
(*               := map_poly polyC p (this notation is defined in poly.v).    *)
(*      u.[x, y] == the bivariate polynomial u evaluated at 'X = x, 'Y = y.   *)
(*               := u.[x%:P].[y].                                             *)
(*       sizeY u == the size of u in 'Y (1 + the 'Y-degree of u, if u != 0).  *)
(*               := \max_(i < size u) size u`_i.                              *)
(*      swapXY u == the bivariate polynomial u['Y, 'X], for u bivariate.      *)
(*    poly_XaY p == the bivariate polynomial p['X + 'Y], for p univariate.    *)
(*               := p^:P \Po ('X + 'Y).                                       *)
(*    poly_XmY p == the bivariate polynomial p['X * 'Y], for p univariate.    *)
(*               := P^:P \Po ('X * 'Y).                                       *)
(* sub_annihilant p q == for univariate p, q != 0, a nonzero polynomial whose *)
(*                  roots include all the differences of roots of p and q, in *)
(*                  all field extensions (:= resultant (poly_XaY p) q^:P).    *)
(* div_annihilant p q == for polynomials p != 0, q with q.[0] != 0, a nonzero *)
(*                  polynomial whose roots include all the quotients of roots *)
(*                  of p by roots of q, in all field extensions               *)
(*                  (:= resultant (poly_XmY p) q^:P).                         *)
(* The latter two "annhilants" provide uniform witnesses for an alternative   *)
(* proof of the closure of the algebraicOver predicate (see mxpoly.v). The    *)
(* fact that the annhilant does not depend on the particular choice of roots  *)
(* of p and q is crucial for the proof of the Primitive Element Theorem (file *)
(* separable.v).                                                              *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory.

Local Notation "p ^ f" := (map_poly f p) : ring_scope.
Local Notation eval := horner_eval.

Notation "'Y" := 'X%:P : ring_scope.
Notation "p ^:P" := (p ^ polyC) (at level 2, format "p ^:P") : ring_scope.
Notation "p .[ x , y ]" := (p.[x%:P].[y])
  (at level 2, left associativity, format "p .[ x ,  y ]") : ring_scope.

Section PolyXY_Ring.

Variable R : ringType.
Implicit Types (u : {poly {poly R}}) (p q : {poly R}) (x : R).

Fact swapXY_key : unit. Proof. by []. Qed.
Definition swapXY_def u : {poly {poly R}} := (u ^ map_poly polyC).['Y].
Definition swapXY := locked_with swapXY_key swapXY_def.
Canonical swapXY_unlockable := [unlockable fun swapXY].

Definition sizeY u : nat := \max_(i < size u) (size u`_i).
Definition poly_XaY p : {poly {poly R}} := p^:P \Po ('X + 'Y).
Definition poly_XmY p : {poly {poly R}} := p^:P \Po ('X * 'Y).
Definition sub_annihilant p q := resultant (poly_XaY p) q^:P.
Definition div_annihilant p q := resultant (poly_XmY p) q^:P.

Lemma swapXY_polyC p : swapXY p%:P = p^:P.
Proof. by rewrite unlock map_polyC hornerC. Qed.

Lemma swapXY_X : swapXY 'X = 'Y.
Proof. by rewrite unlock map_polyX hornerX. Qed.

Lemma swapXY_Y : swapXY 'Y = 'X.
Proof. by rewrite swapXY_polyC map_polyX. Qed.

Lemma swapXY_is_additive : additive swapXY.
Proof. by move=> u v; rewrite unlock rmorphB !hornerE. Qed.
Canonical swapXY_addf := Additive swapXY_is_additive.

Lemma coef_swapXY u i j : (swapXY u)`_i`_j = u`_j`_i.
Proof.
elim/poly_ind: u => [|u p IHu] in i j *; first by rewrite raddf0 !coef0.
rewrite raddfD !coefD /= swapXY_polyC coef_map /= !coefC coefMX.
rewrite !(fun_if (fun q : {poly R} => q`_i)) coef0 -IHu; congr (_ + _).
by rewrite unlock rmorphM /= map_polyX hornerMX coefMC coefMX.
Qed.

Lemma swapXYK : involutive swapXY.
Proof. by move=> u; apply/polyP=> i; apply/polyP=> j; rewrite !coef_swapXY. Qed.

Lemma swapXY_map_polyC p : swapXY p^:P = p%:P.
Proof. by rewrite -swapXY_polyC swapXYK. Qed.

Lemma swapXY_eq0 u : (swapXY u == 0) = (u == 0).
Proof. by rewrite (inv_eq swapXYK) raddf0. Qed.

Lemma swapXY_is_multiplicative : multiplicative swapXY.
Proof.
split=> [u v|]; last by rewrite swapXY_polyC map_polyC.
apply/polyP=> i; apply/polyP=> j; rewrite coef_swapXY !coefM !coef_sum.
rewrite (eq_bigr _ (fun _ _ => coefM _ _ _)) exchange_big /=.
apply: eq_bigr => j1 _; rewrite coefM; apply: eq_bigr=> i1 _.
by rewrite !coef_swapXY.
Qed.
Canonical swapXY_rmorphism := AddRMorphism swapXY_is_multiplicative.

Lemma swapXY_is_scalable : scalable_for (map_poly polyC \; *%R) swapXY.
Proof. by move=> p u /=; rewrite -mul_polyC rmorphM /= swapXY_polyC. Qed.
Canonical swapXY_linear := AddLinear swapXY_is_scalable.
Canonical swapXY_lrmorphism := [lrmorphism of swapXY].

Lemma swapXY_comp_poly p u : swapXY (p^:P \Po u) = p^:P \Po swapXY u.
Proof.
rewrite -horner_map; congr _.[_]; rewrite -!map_poly_comp /=.
by apply: eq_map_poly => x; rewrite /= swapXY_polyC map_polyC.
Qed.

Lemma max_size_coefXY u i : size u`_i <= sizeY u.
Proof.
have [ltiu | /(nth_default 0)->] := ltnP i (size u); last by rewrite size_poly0.
exact: (bigmax_sup (Ordinal ltiu)).
Qed.

Lemma max_size_lead_coefXY u : size (lead_coef u) <= sizeY u.
Proof. by rewrite lead_coefE max_size_coefXY. Qed.

Lemma max_size_evalX u : size u.['X] <= sizeY u + (size u).-1.
Proof.
rewrite horner_coef (leq_trans (size_sum _ _ _)) //; apply/bigmax_leqP=> i _.
rewrite (leq_trans (size_mul_leq _ _)) // size_polyXn addnS.
by rewrite leq_add ?max_size_coefXY //= -ltnS (leq_trans _ (leqSpred _)).
Qed.

Lemma max_size_evalC u x : size u.[x%:P] <= sizeY u.
Proof.
rewrite horner_coef (leq_trans (size_sum _ _ _)) //; apply/bigmax_leqP=> i _.
rewrite (leq_trans (size_mul_leq _ _)) // -polyC_exp size_polyC addnC -subn1.
by rewrite (leq_trans _ (max_size_coefXY _ i)) // leq_subLR leq_add2r leq_b1.
Qed.

Lemma sizeYE u : sizeY u = size (swapXY u).
Proof.
apply/eqP; rewrite eqn_leq; apply/andP; split.
  apply/bigmax_leqP=> /= i _; apply/leq_sizeP => j /(nth_default 0) u_j_0.
  by rewrite -coef_swapXY u_j_0 coef0.
apply/leq_sizeP=> j le_uY_j; apply/polyP=> i; rewrite coef_swapXY coef0.
by rewrite nth_default // (leq_trans _ le_uY_j) ?max_size_coefXY.
Qed.

Lemma sizeY_eq0 u : (sizeY u == 0%N) = (u == 0).
Proof. by rewrite sizeYE size_poly_eq0 swapXY_eq0. Qed.

Lemma sizeY_mulX u : sizeY (u * 'X) = sizeY u.
Proof.
rewrite !sizeYE rmorphM /= swapXY_X rreg_size //.
by have /monic_comreg[_ /rreg_lead] := monicX R.
Qed.

Lemma swapXY_poly_XaY p : swapXY (poly_XaY p) = poly_XaY p.
Proof. by rewrite swapXY_comp_poly rmorphD /= swapXY_X swapXY_Y addrC. Qed.

Lemma swapXY_poly_XmY p : swapXY (poly_XmY p) = poly_XmY p.
Proof.
by rewrite swapXY_comp_poly rmorphM /= swapXY_X swapXY_Y commr_polyX.
Qed.

Lemma poly_XaY0 : poly_XaY 0 = 0.
Proof. by rewrite /poly_XaY rmorph0 comp_poly0. Qed.

Lemma poly_XmY0 : poly_XmY 0 = 0.
Proof. by rewrite /poly_XmY rmorph0 comp_poly0. Qed.

End PolyXY_Ring.

Prenex Implicits swapXY sizeY poly_XaY poly_XmY sub_annihilant div_annihilant.
Prenex Implicits swapXYK.

Lemma swapXY_map (R S : ringType) (f : {additive R -> S}) u :
  swapXY (u ^ map_poly f) = swapXY u ^ map_poly f.
Proof.
by apply/polyP=> i; apply/polyP=> j; rewrite !(coef_map, coef_swapXY).
Qed.

Section PolyXY_ComRing.

Variable R : comRingType.
Implicit Types (u : {poly {poly R}}) (p : {poly R}) (x y : R).

Lemma horner_swapXY u x : (swapXY u).[x%:P] = u ^ eval x.
Proof.
apply/polyP=> i /=; rewrite coef_map /= /eval horner_coef coef_sum -sizeYE.
rewrite (horner_coef_wide _ (max_size_coefXY u i)); apply: eq_bigr=> j _.
by rewrite -polyC_exp coefMC coef_swapXY.
Qed.

Lemma horner_polyC u x : u.[x%:P] = swapXY u ^ eval x.
Proof. by rewrite -horner_swapXY swapXYK. Qed.

Lemma horner2_swapXY u x y : (swapXY u).[x, y] = u.[y, x].
Proof. by rewrite horner_swapXY -{1}(hornerC y x) horner_map. Qed.

Lemma horner_poly_XaY p v : (poly_XaY p).[v] = p \Po (v + 'X).
Proof. by rewrite horner_comp !hornerE. Qed.

Lemma horner_poly_XmY p v : (poly_XmY p).[v] = p \Po (v * 'X).
Proof. by rewrite horner_comp !hornerE. Qed.

End PolyXY_ComRing.

Section PolyXY_Idomain.

Variable R : idomainType.
Implicit Types (p q : {poly R}) (x y : R).

Lemma size_poly_XaY p : size (poly_XaY p) = size p.
Proof. by rewrite size_comp_poly2 ?size_XaddC // size_map_polyC. Qed.

Lemma poly_XaY_eq0 p : (poly_XaY p == 0) = (p == 0).
Proof. by rewrite -!size_poly_eq0 size_poly_XaY. Qed.

Lemma size_poly_XmY p : size (poly_XmY p) = size p.
Proof. by rewrite size_comp_poly2 ?size_XmulC ?polyX_eq0 ?size_map_polyC. Qed.

Lemma poly_XmY_eq0 p : (poly_XmY p == 0) = (p == 0).
Proof. by rewrite -!size_poly_eq0 size_poly_XmY. Qed.

Lemma lead_coef_poly_XaY p : lead_coef (poly_XaY p) = (lead_coef p)%:P.
Proof.
rewrite lead_coef_comp ?size_XaddC // -['Y]opprK -polyC_opp lead_coefXsubC.
by rewrite expr1n mulr1 lead_coef_map_inj //; apply: polyC_inj.
Qed.

Lemma sub_annihilant_in_ideal p q :
    1 < size p -> 1 < size q ->
  {uv : {poly {poly R}} * {poly {poly R}}
   | size uv.1 < size q /\ size uv.2 < size p
   & forall x y,
     (sub_annihilant p q).[y] = uv.1.[x, y] * p.[x + y] + uv.2.[x, y] * q.[x]}.
Proof.
rewrite -size_poly_XaY -(size_map_polyC q) => p1_gt1 q1_gt1.
have [uv /= [ub_u ub_v Dr]] := resultant_in_ideal p1_gt1 q1_gt1.
exists uv => // x y; rewrite -[r in r.[y]](hornerC _ x%:P) Dr.
by rewrite !(hornerE, horner_comp).
Qed.

Lemma sub_annihilantP p q x y :
    p != 0 -> q != 0 -> p.[x] = 0 -> q.[y] = 0 ->
  (sub_annihilant p q).[x - y] = 0.
Proof.
move=> nz_p nz_q px0 qy0.
have p_gt1: size p > 1 by have /rootP/root_size_gt1-> := px0.
have q_gt1: size q > 1 by have /rootP/root_size_gt1-> := qy0.
have [uv /= _ /(_ y)->] := sub_annihilant_in_ideal p_gt1 q_gt1.
by rewrite (addrC y) subrK px0 qy0 !mulr0 addr0.
Qed.

Lemma sub_annihilant_neq0 p q : p != 0 -> q != 0 -> sub_annihilant p q != 0.
Proof.
rewrite resultant_eq0; set p1 := poly_XaY p => nz_p nz_q.
have [nz_p1 nz_q1]: p1 != 0 /\ q^:P != 0 by rewrite poly_XaY_eq0 map_polyC_eq0.
rewrite -leqNgt eq_leq //; apply/eqP/Bezout_coprimepPn=> // [[[u v]]] /=.
rewrite !size_poly_gt0 -andbA => /and4P[nz_u ltuq nz_v _] Duv.
have /eqP/= := congr1 (size \o (lead_coef \o swapXY)) Duv.
rewrite ltn_eqF // !rmorphM !lead_coefM (leq_trans (leq_ltn_trans _ ltuq)) //=.
  rewrite -{2}[u]swapXYK -sizeYE swapXY_poly_XaY lead_coef_poly_XaY.
  by rewrite mulrC mul_polyC size_scale ?max_size_lead_coefXY ?lead_coef_eq0.
rewrite swapXY_map_polyC lead_coefC size_map_polyC.
set v1 := lead_coef _; have nz_v1: v1 != 0 by rewrite lead_coef_eq0 swapXY_eq0.
rewrite [in rhs in _ <= rhs]polySpred ?mulf_neq0 // size_mul //.
by rewrite (polySpred nz_v1) addnC addnS polySpred // ltnS leq_addr.
Qed.

Lemma div_annihilant_in_ideal p q :
    1 < size p -> 1 < size q ->
  {uv : {poly {poly R}} * {poly {poly R}}
   | size uv.1 < size q /\ size uv.2 < size p
   & forall x y,
     (div_annihilant p q).[y] = uv.1.[x, y] * p.[x * y] + uv.2.[x, y] * q.[x]}.
Proof.
rewrite -size_poly_XmY -(size_map_polyC q) => p1_gt1 q1_gt1.
have [uv /= [ub_u ub_v Dr]] := resultant_in_ideal p1_gt1 q1_gt1.
exists uv => // x y; rewrite -[r in r.[y]](hornerC _ x%:P) Dr.
by rewrite !(hornerE, horner_comp).
Qed.

Lemma div_annihilant_neq0 p q : p != 0 -> q.[0] != 0 -> div_annihilant p q != 0.
Proof.
have factorX u: u != 0 -> root u 0 -> exists2 v, v != 0 & u = v * 'X.
  move=> nz_u /factor_theorem[v]; rewrite subr0 => Du; exists v => //.
  by apply: contraNneq nz_u => v0; rewrite Du v0 mul0r.
have nzX: 'X != 0 := monic_neq0 (monicX _); have rootC0 := root_polyC _ 0.
rewrite resultant_eq0 -leqNgt -rootE // => nz_p nz_q0; apply/eq_leq/eqP.
have nz_q: q != 0 by apply: contraNneq nz_q0 => ->; rewrite root0.
apply/Bezout_coprimepPn; rewrite ?map_polyC_eq0 ?poly_XmY_eq0 // => [[uv]].
rewrite !size_poly_gt0 -andbA ltnNge => /and4P[nz_u /negP ltuq nz_v _] Duv.
pose u := swapXY uv.1; pose v := swapXY uv.2.
suffices{ltuq}: size q <= sizeY u by rewrite sizeYE swapXYK -size_map_polyC.
have{nz_u nz_v} [nz_u nz_v Dvu]: [/\ u != 0, v != 0 & q *: v = u * poly_XmY p].
  rewrite !swapXY_eq0; split=> //; apply: (can_inj swapXYK).
  by rewrite linearZ rmorphM /= !swapXYK swapXY_poly_XmY Duv mulrC.
have{Duv} [n ltvn]: {n | size v < n} by exists (size v).+1.
elim: n {uv} => // n IHn in p (v) (u) nz_u nz_v Dvu nz_p ltvn *.
have Dp0: root (poly_XmY p) 0 = root p 0 by rewrite root_comp !hornerE rootC0.
have Dv0: root u 0 || root p 0 = root v 0 by rewrite -Dp0 -rootM -Dvu rootZ.
have [v0_0 | nz_v0] := boolP (root v 0); last first.
  have nz_p0: ~~ root p 0 by apply: contra nz_v0; rewrite -Dv0 orbC => ->.
  apply: (@leq_trans (size (q * v.[0]))).
    by rewrite size_mul // (polySpred nz_v0) addnS leq_addr.
  rewrite -hornerZ Dvu !(horner_comp, hornerE) horner_map mulrC size_Cmul //.
  by rewrite horner_coef0 max_size_coefXY.
have [v1 nz_v1 Dv] := factorX _ _ nz_v v0_0; rewrite Dv size_mulX // in ltvn.
have /orP[/factorX[//|u1 nz_u1 Du] | p0_0]: root u 0 || root p 0 by rewrite Dv0.
  rewrite Du sizeY_mulX; apply: IHn nz_u1 nz_v1 _ nz_p ltvn.
  by apply: (mulIf (nzX _)); rewrite mulrAC -scalerAl -Du -Dv.
have /factorX[|v2 nz_v2 Dv1]: root (swapXY v1) 0; rewrite ?swapXY_eq0 //.
  suffices: root (swapXY v1 * 'Y) 0 by rewrite mulrC mul_polyC rootZ ?polyX_eq0.
  have: root (swapXY (q *: v)) 0.
    by rewrite Dvu rmorphM rootM /= swapXY_poly_XmY Dp0 p0_0 orbT.
  by rewrite linearZ rootM rootC0 (negPf nz_q0) /= Dv rmorphM /= swapXY_X.
rewrite ltnS (canRL swapXYK Dv1) -sizeYE sizeY_mulX sizeYE in ltvn.
have [p1 nz_p1 Dp] := factorX _ _ nz_p p0_0.
apply: IHn nz_u _ _ nz_p1 ltvn; first by rewrite swapXY_eq0.
apply: (@mulIf _ ('X * 'Y)); first by rewrite mulf_neq0 ?polyC_eq0 ?nzX.
rewrite -scalerAl mulrA mulrAC -{1}swapXY_X -rmorphM /= -Dv1 swapXYK -Dv Dvu.
by rewrite /poly_XmY Dp rmorphM /= map_polyX comp_polyM comp_polyX mulrA.
Qed.

End PolyXY_Idomain.

Section PolyXY_Field.

Variables (F E : fieldType) (FtoE : {rmorphism F -> E}).

Local Notation pFtoE := (map_poly (GRing.RMorphism.apply FtoE)).

Lemma div_annihilantP (p q : {poly E}) (x y : E) :
    p != 0 -> q != 0 -> y != 0 -> p.[x] = 0 -> q.[y] = 0 ->
  (div_annihilant p q).[x / y] = 0.
Proof.
move=> nz_p nz_q nz_y px0 qy0.
have p_gt1: size p > 1 by have /rootP/root_size_gt1-> := px0.
have q_gt1: size q > 1 by have /rootP/root_size_gt1-> := qy0.
have [uv /= _ /(_ y)->] := div_annihilant_in_ideal p_gt1 q_gt1.
by rewrite (mulrC y) divfK // px0 qy0 !mulr0 addr0.
Qed.

Lemma map_sub_annihilantP (p q : {poly F}) (x y : E) :
     p != 0 -> q != 0 ->(p ^ FtoE).[x] = 0 -> (q ^ FtoE).[y] = 0 ->
  (sub_annihilant p q ^ FtoE).[x - y] = 0.
Proof.
move=> nz_p nz_q px0 qy0; have pFto0 := map_poly_eq0 FtoE.
rewrite map_resultant ?pFto0 ?lead_coef_eq0 ?map_poly_eq0 ?poly_XaY_eq0 //.
rewrite map_comp_poly rmorphD /= map_polyC /= !map_polyX -!map_poly_comp /=.
by rewrite !(eq_map_poly (map_polyC _)) !map_poly_comp sub_annihilantP ?pFto0.
Qed.

Lemma map_div_annihilantP (p q : {poly F}) (x y : E) :
     p != 0 -> q != 0 -> y != 0 -> (p ^ FtoE).[x] = 0 -> (q ^ FtoE).[y] = 0 ->
  (div_annihilant p q ^ FtoE).[x / y] = 0.
Proof.
move=> nz_p nz_q nz_y px0 qy0; have pFto0 := map_poly_eq0 FtoE.
rewrite map_resultant ?pFto0 ?lead_coef_eq0 ?map_poly_eq0 ?poly_XmY_eq0 //.
rewrite map_comp_poly rmorphM /= map_polyC /= !map_polyX -!map_poly_comp /=.
by rewrite !(eq_map_poly (map_polyC _)) !map_poly_comp div_annihilantP ?pFto0.
Qed.

Lemma root_annihilant x p (pEx := (p ^ pFtoE).[x%:P]) :
    pEx != 0 -> algebraicOver FtoE x ->
  exists2 r : {poly F}, r != 0 & forall y, root pEx y -> root (r ^ FtoE) y.
Proof.
move=> nz_px [q nz_q qx0].
have [/size1_polyC Dp | p_gt1] := leqP (size p) 1.
  by rewrite {}/pEx Dp map_polyC hornerC map_poly_eq0 in nz_px *; exists p`_0.
have nz_p: p != 0 by rewrite -size_poly_gt0 ltnW.
elim: {q}_.+1 {-2}q (ltnSn (size q)) => // m IHm q le_qm in nz_q qx0 *.
have nz_q1: q^:P != 0 by rewrite map_poly_eq0.
have sz_q1: size q^:P = size q by rewrite size_map_polyC.
have q1_gt1: size q^:P > 1.
  by rewrite sz_q1 -(size_map_poly FtoE) (root_size_gt1 _ qx0) ?map_poly_eq0.
have [uv _ Dr] := resultant_in_ideal p_gt1 q1_gt1; set r := resultant p _ in Dr.
have /eqP q1x0: (q^:P ^ pFtoE).[x%:P] == 0.
  by rewrite -swapXY_polyC -swapXY_map horner_swapXY !map_polyC polyC_eq0.
have [|r_nz] := boolP (r == 0); last first.
  exists r => // y pxy0; rewrite -[r ^ _](hornerC _ x%:P) -map_polyC Dr.
  by rewrite rmorphD !rmorphM !hornerE q1x0 mulr0 addr0 rootM pxy0 orbT.
rewrite resultant_eq0 => /gtn_eqF/Bezout_coprimepPn[]// [q2 p1] /=.
rewrite size_poly_gt0 sz_q1 => /andP[/andP[nz_q2 ltq2] _] Dq.
pose n := (size (lead_coef q2)).-1; pose q3 := map_poly (coefp n) q2.
have nz_q3: q3 != 0 by rewrite map_poly_eq0_id0 ?lead_coef_eq0.
apply: (IHm q3); rewrite ?(leq_ltn_trans (size_poly _ _)) ?(leq_trans ltq2) //.
have /polyP/(_ n)/eqP: (q2 ^ pFtoE).[x%:P] = 0.
apply: (mulIf nz_px); rewrite -hornerM -rmorphM Dq rmorphM hornerM /= q1x0.
  by rewrite mul0r mulr0.
rewrite coef0; congr (_ == 0); rewrite !horner_coef coef_sum.
rewrite size_map_poly !size_map_poly_id0 ?map_poly_eq0 ?lead_coef_eq0 //.
by apply: eq_bigr => i _; rewrite -rmorphX coefMC !coef_map.
Qed.

Lemma algebraic_root_polyXY x y :
    (let pEx p := (p ^ map_poly FtoE).[x%:P] in
    exists2 p, pEx p != 0 & root (pEx p) y) ->
  algebraicOver FtoE x -> algebraicOver FtoE y.
Proof. by case=> p nz_px pxy0 /(root_annihilant nz_px)[r]; exists r; auto. Qed.

End PolyXY_Field.

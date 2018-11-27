(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrbool ssrfun ssrnat eqtype seq choice div fintype.
From mathcomp
Require Import path tuple bigop finset prime ssralg poly polydiv mxpoly.
From mathcomp
Require Import countalg closed_field ssrnum ssrint rat intdiv.
From mathcomp
Require Import fingroup finalg zmodp cyclic pgroup sylow.
From mathcomp
Require Import vector falgebra fieldext separable galois.

(******************************************************************************)
(*   The main result in this file is the existence theorem that underpins the *)
(* construction of the algebraic numbers in file algC.v. This theorem simply  *)
(* asserts the existence of an algebraically closed field with an             *)
(* automorphism of order 2, and dubbed the Fundamental_Theorem_of_Algebraics  *)
(* because it is essentially the Fundamental Theorem of Algebra for algebraic *)
(* numbers (the more familiar version for complex numbers can be derived by   *)
(* continuity).                                                               *)
(*   Although our proof does indeed construct exactly the algebraics, we      *)
(* choose not to expose this in the statement of our Theorem. In algC.v we    *)
(* construct the norm and partial order of the "complex field" introduced by  *)
(* the Theorem; as these imply is has characteristic 0, we then get the       *)
(* algebraics as a subfield. To avoid some duplication a few basic properties *)
(* of the algebraics, such as the existence of minimal polynomials, that are  *)
(* required by the proof of the Theorem, are also proved here.                *)
(*  The main theorem of closed_field supplies us directly with an algebraic   *)
(* closure of the rationals (as the rationals are a countable field), so all  *)
(* we really need to construct is a conjugation automorphism that exchanges   *)
(* the two roots (i and -i) of X^2 + 1, and fixes a (real) subfield of        *)
(* index 2. This does not require actually constructing this field: the       *)
(* kHomExtend construction from galois.v supplies us with an automorphism     *)
(* conj_n of the number field Q[z_n] = Q[x_n, i] for any x_n such that Q[x_n] *)
(* does not contain i (e.g., such that Q[x_n] is real). As conj_n will extend *)
(* conj_m when Q[x_n] contains x_m, it therefore suffices to construct a      *)
(* sequence x_n such that                                                     *)
(* (1) For each n, Q[x_n] is a REAL field containing Q[x_m] for all m <= n.   *)
(* (2) Each z in C belongs to Q[z_n] = Q[x_n, i] for large enough n.          *)
(* This, of course, amounts to proving the Fundamental Theorem of Algebra.    *)
(*   Indeed, we use a constructive variant of Artin's algebraic proof of that *)
(* Theorem to replace (2) by                                                  *)
(* (3) Each monic polynomial over Q[x_m] whose constant term is -c^2 for some *)
(*     c in Q[x_m] has a root in Q[x_n] for large enough n.                   *)
(* We then ensure (3) by setting Q[x_n+1] = Q[x_n, y] where y is the root of  *)
(* of such a polynomial p found by dichotomy in some interval [0, b] with b   *)
(* suitably large (such that p[b] >= 0), and p is obtained by decoding n into *)
(* a triple (m, p, c) that satisfies the conditions of (3) (taking x_n+1=x_n  *)
(* if this is not the case), thereby ensuring that all such triples are       *)
(* ultimately considered.                                                     *)
(*   In more detail, the 600-line proof consists in six (uneven) parts:       *)
(* (A) - Construction of number fields (~ 100 lines): in order to make use of *)
(*     the theory developped in falgebra, fieldext, separable and galois we   *)
(*     construct a separate fielExtType Q z for the number field Q[z], with   *)
(*     z in C, the closure of rat supplied by countable_algebraic_closure.    *)
(*     The morphism (ofQ z) maps Q z to C, and the Primitive Element Theorem  *)
(*     lets us define a predicate sQ z characterizing the image of (ofQ z),   *)
(*     as well as a partial inverse (inQ z) to (ofQ z).                       *)
(* (B) - Construction of the real extension Q[x, y] (~ 230 lines): here y has *)
(*     to be a root of a polynomial p over Q[x] satisfying the conditions of  *)
(*     (3), and Q[x] should be real and archimedean, which we represent by    *)
(*     a morphism from Q x to some archimedean field R, as the ssrnum and     *)
(*     fieldext structures are not compatible. The construction starts by     *)
(*     weakening the condition p[0] = -c^2 to p[0] <= 0 (in R), then reducing *)
(*     to the case where p is the minimal polynomial over Q[x] of some y (in  *)
(*     some Q[w] that contains x and all roots of p). Then we only need to    *)
(*     construct a realFieldType structure for Q[t] = Q[x,y] (we don't even   *)
(*     need to show it is consistent with that of R). This amounts to fixing  *)
(*     the sign of all z != 0 in Q[t], consistently with arithmetic in Q[t].  *)
(*     Now any such z is equal to q[y] for some q in Q[x][X] coprime with p.  *)
(*     Then up + vq = 1 for Bezout coefficients u and v. As p is monic, there *)
(*     is some b0 >= 0 in R such that p changes sign in ab0 = [0; b0]. As R   *)
(*     is archimedean, some iteration of the binary search for a root of p in *)
(*     ab0 will yield an interval ab_n such that |up[d]| < 1/2 for d in ab_n. *)
(*     Then |q[d]| > 1/2M > 0 for any upper bound M on |v[X]| in ab0, so q    *)
(*     cannot change sign in ab_n (as then root-finding in ab_n would yield a *)
(*     d with |Mq[d]| < 1/2), so we can fix the sign of z to that of q in     *)
(*     ab_n.                                                                  *)
(* (C) - Construction of the x_n and z_n (~50 lines): x_ n is obtained by     *)
(*     iterating (B), starting with x_0 = 0, and then (A) and the PET yield   *)
(*     z_ n. We establish (1) and (3), and that the minimal polynomial of the *)
(*     preimage i_ n of i over the preimage R_ n of Q[x_n] is X^2 + 1.        *)
(* (D) - Establish (2), i.e., prove the FTA (~180 lines). We must depart from *)
(*     Artin's proof because deciding membership in the union of the Q[x_n]   *)
(*     requires the FTA, i.e., we cannot (yet) construct a maximal real       *)
(*     subfield of C. We work around this issue by first reducing to the case *)
(*     where Q[z] is Galois over Q and contains i, then using induction over  *)
(*     the degree of z over Q[z_ n] (i.e., the degree of a monic polynomial   *)
(*     over Q[z_n] that has z as a root). We can assume that z is not in      *)
(*     Q[z_n]; then it suffices to find some y in Q[z_n, z] \ Q[z_n] that is  *)
(*     also in Q[z_m] for some m > n, as then we can apply induction with the *)
(*     minimal polynomial of z over Q[z_n, y]. In any Galois extension Q[t]   *)
(*     of Q that contains both z and z_n, Q[x_n, z] = Q[z_n, z] is Galois     *)
(*     over both Q[x_n] and Q[z_n]. If Gal(Q[x_n,z] / Q[x_n]) isn't a 2-group *)
(*     take one of its Sylow 2-groups P; the minimal polynomial p of any      *)
(*     generator of the fixed field F of P over Q[x_n] has odd degree, hence  *)
(*     by (3) - p[X]p[-X] and thus p has a root y in some Q[x_m], hence in    *)
(*     Q[z_m]. As F is normal, y is in F, with minimal polynomial p, and y    *)
(*     is not in Q[z_n] = Q[x_n, i] since p has odd degree. Otherwise,        *)
(*     Gal(Q[z_n,z] / Q[z_n]) is a proper 2-group, and has a maximal subgroup *)
(*     P of index 2. The fixed field F of P has a generator w over Q[z_n]     *)
(*     with w^2 in Q[z_n] \ Q[x_n], i.e. w^2 = u + 2iv with v != 0. From (3)  *)
(*     X^4 - uX^2 - v^2 has a root x in some Q[x_m]; then x != 0 as v != 0,   *)
(*     hence w^2 = y^2 for y = x + iv/x in Q[z_m], and y generates F.         *)
(* (E) - Construct conj and conclude (~40 lines): conj z is defined as        *)
(*     conj_ n z with the n provided by (2); since each conj_ m is a morphism *)
(*     of order 2 and conj z = conj_ m z for any m >= n, it follows that conj *)
(*     is also a morphism of order 2.                                         *)
(* Note that (C), (D) and (E) only depend on Q[x_n] not containing i; the     *)
(* order structure is not used (hence we need not prove that the ordering of  *)
(* Q[x_m] is consistent with that of Q[x_n] for m >= n).                      *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Local Notation "p ^ f" := (map_poly f p) : ring_scope.
Local Notation "p ^@" := (p ^ in_alg _) (at level 2, format "p ^@"): ring_scope.
Local Notation "<< E ; u >>" := <<E; u>>%VS.
Local Notation Qmorphism C := {rmorphism rat -> C}.

Lemma rat_algebraic_archimedean (C : numFieldType) (QtoC : Qmorphism C) :
  integralRange QtoC -> Num.archimedean_axiom C.
Proof.
move=> algC x.
without loss x_ge0: x / 0 <= x by rewrite -normr_id; apply; apply: normr_ge0.
have [-> | nz_x] := eqVneq x 0; first by exists 1%N; rewrite normr0.
have [p mon_p px0] := algC x; exists (\sum_(j < size p) `|numq p`_j|)%N.
rewrite ger0_norm // real_ltrNge ?rpred_nat ?ger0_real //.
apply: contraL px0 => lb_x; rewrite rootE gtr_eqF // horner_coef size_map_poly.
have x_gt0 k: 0 < x ^+ k by rewrite exprn_gt0 // ltr_def nz_x.
move: lb_x; rewrite polySpred ?monic_neq0 // !big_ord_recr coef_map /=.
rewrite -lead_coefE (monicP mon_p) natrD rmorph1 mul1r => lb_x.
case: _.-1 (lb_x) => [|n]; first by rewrite !big_ord0 !add0r ltr01.
rewrite -ltr_subl_addl add0r -(ler_pmul2r (x_gt0 n)) -exprS.
apply: ltr_le_trans; rewrite mulrDl mul1r ltr_spaddr // -sumrN.
rewrite natr_sum mulr_suml ler_sum // => j _.
rewrite coef_map /= fmorph_eq_rat (ler_trans (real_ler_norm _)) //.
  by rewrite rpredN rpredM ?rpred_rat ?rpredX // ger0_real.
rewrite normrN normrM ler_pmul //=.
  rewrite normf_div -!intr_norm -!abszE ler_pimulr ?ler0n //.
  by rewrite invf_le1 ?ler1n ?ltr0n ?absz_gt0 ?denq_eq0.
rewrite normrX ger0_norm ?(ltrW x_gt0) // ler_weexpn2l ?leq_ord //.
by rewrite (ler_trans _ lb_x) // -natrD addn1 ler1n.
Qed.

Definition decidable_embedding sT T (f : sT -> T) :=
  forall y, decidable (exists x, y = f x).

Lemma rat_algebraic_decidable (C : fieldType) (QtoC : Qmorphism C) :
  integralRange QtoC -> decidable_embedding QtoC.
Proof.
have QtoCinj: injective QtoC by apply: fmorph_inj.
pose ZtoQ : int -> rat := intr; pose ZtoC : int -> C := intr.
have ZtoQinj: injective ZtoQ by apply: intr_inj.
have defZtoC: ZtoC =1 QtoC \o ZtoQ by move=> m; rewrite /= rmorph_int.
move=> algC x; have /sig2_eqW[q mon_q qx0] := algC x; pose d := (size q).-1.
have [n ub_n]: {n | forall y, root q y -> `|y| < n}.
  have [n1 ub_n1] := monic_Cauchy_bound mon_q.
  have /monic_Cauchy_bound[n2 ub_n2]: (-1) ^+ d *: (q \Po - 'X) \is monic.
    rewrite monicE lead_coefZ lead_coef_comp ?size_opp ?size_polyX // -/d.
    by rewrite lead_coef_opp lead_coefX (monicP mon_q) (mulrC 1) signrMK.
  exists (Num.max n1 n2) => y; rewrite ltrNge ler_normr !ler_maxl rootE.
  apply: contraL => /orP[]/andP[] => [/ub_n1/gtr_eqF->// | _ /ub_n2/gtr_eqF].
  by rewrite hornerZ horner_comp !hornerE opprK mulf_eq0 signr_eq0 => /= ->.
have [p [a nz_a Dq]] := rat_poly_scale q; pose N := Num.bound `|n * a%:~R|.
pose xa : seq rat := [seq (m%:R - N%:R) / a%:~R | m <- iota 0 N.*2].
have [/sig2_eqW[y _ ->] | xa'x] := @mapP _ _ QtoC xa x; first by left; exists y.
right=> [[y Dx]]; case: xa'x; exists y => //.
have{x Dx qx0} qy0: root q y by rewrite Dx fmorph_root in qx0.
have /dvdzP[b Da]: (denq y %| a)%Z.
  have /Gauss_dvdzl <-: coprimez (denq y) (numq y ^+ d).
    by rewrite coprimez_sym coprimez_expl //; apply: coprime_num_den.
  pose p1 : {poly int} := a *: 'X^d - p.
  have Dp1: p1 ^ intr = a%:~R *: ('X^d - q).
    by rewrite rmorphB linearZ /= map_polyXn scalerBr Dq scalerKV ?intr_eq0.
  apply/dvdzP; exists (\sum_(i < d) p1`_i * numq y ^+ i * denq y ^+ (d - i.+1)).
  apply: ZtoQinj; rewrite /ZtoQ rmorphM mulr_suml rmorph_sum /=.
  transitivity ((p1 ^ intr).[y] * (denq y ^+ d)%:~R).
    rewrite Dp1 !hornerE hornerXn (rootP qy0) subr0.
    by rewrite !rmorphX /= numqE exprMn mulrA.
  have sz_p1: (size (p1 ^ ZtoQ)%R <= d)%N.
    rewrite Dp1 size_scale ?intr_eq0 //; apply/leq_sizeP=> i.
    rewrite leq_eqVlt eq_sym -polySpred ?monic_neq0 // coefB coefXn.
    case: eqP => [-> _ | _ /(nth_default 0)->//].
    by rewrite -lead_coefE (monicP mon_q).
  rewrite (horner_coef_wide _ sz_p1) mulr_suml; apply: eq_bigr => i _.
  rewrite -!mulrA -exprSr coef_map !rmorphM !rmorphX /= numqE exprMn -mulrA.
  by rewrite -exprD -addSnnS subnKC.
pose m := `|(numq y * b + N)%R|%N.
have Dm: m%:R = `|y * a%:~R + N%:R|.
  by rewrite pmulrn abszE intr_norm Da rmorphD !rmorphM /= numqE mulrAC mulrA.
have ltr_Qnat n1 n2 : (n1%:R < n2%:R :> rat = _) := ltr_nat _ n1 n2.
have ub_y: `|y * a%:~R| < N%:R.
  apply: ler_lt_trans (archi_boundP (normr_ge0 _)); rewrite !normrM.
  by rewrite ler_pmul ?normr_ge0 // (ler_trans _ (ler_norm n)) ?ltrW ?ub_n.
apply/mapP; exists m.
  rewrite mem_iota /= add0n -addnn -ltr_Qnat Dm natrD.
  by rewrite (ler_lt_trans (ler_norm_add _ _)) // normr_nat ltr_add2r.
rewrite Dm ger0_norm ?addrK ?mulfK ?intr_eq0 // -ler_subl_addl sub0r.
by rewrite (ler_trans (ler_norm _)) ?normrN ?ltrW.
Qed.

Lemma minPoly_decidable_closure
  (F : fieldType) (L : closedFieldType) (FtoL : {rmorphism F -> L}) x :
    decidable_embedding FtoL -> integralOver FtoL x ->
  {p | [/\ p \is monic, root (p ^ FtoL) x & irreducible_poly p]}.
Proof.
move=> isF /sig2W[p /monicP mon_p px0].
have [r Dp] := closed_field_poly_normal (p ^ FtoL); pose n := size r.
rewrite lead_coef_map {}mon_p rmorph1 scale1r in Dp.
pose Fpx q := (q \is a polyOver isF) && root q x.
have FpxF q: Fpx (q ^ FtoL) = root (q ^ FtoL) x.
  by rewrite /Fpx polyOver_poly // => j _; apply/sumboolP; exists q`_j.
pose p_ (I : {set 'I_n}) := \prod_(i <- enum I) ('X - (r`_i)%:P).
have{px0 Dp} /ex_minset[I /minsetP[/andP[FpI pIx0] minI]]: exists I, Fpx (p_ I).
  exists setT; suffices ->: p_ setT = p ^ FtoL by rewrite FpxF.
  by rewrite Dp (big_nth 0) big_mkord /p_ (eq_enum (in_set _)) big_filter.
have{p} [p DpI]: {p | p_ I = p ^ FtoL}.
  exists (p_ I ^ (fun y => if isF y is left Fy then sval (sig_eqW Fy) else 0)).
  rewrite -map_poly_comp map_poly_id // => y /(allP FpI) /=.
  by rewrite unfold_in; case: (isF y) => // Fy _; case: (sig_eqW _).
have mon_pI: p_ I \is monic by apply: monic_prod_XsubC.
have mon_p: p \is monic by rewrite -(map_monic FtoL) -DpI.
exists p; rewrite -DpI; split=> //; split=> [|q nCq q_dv_p].
  by rewrite -(size_map_poly FtoL) -DpI (root_size_gt1 _ pIx0) ?monic_neq0.
rewrite -dvdp_size_eqp //; apply/eqP.
without loss mon_q: q nCq q_dv_p / q \is monic.
  move=> IHq; pose a := lead_coef q; pose q1 := a^-1 *: q.
  have nz_a: a != 0 by rewrite lead_coef_eq0 (dvdpN0 q_dv_p) ?monic_neq0.
  have /IHq IHq1: q1 \is monic by rewrite monicE lead_coefZ mulVf.
  by rewrite -IHq1 ?size_scale ?dvdp_scalel ?invr_eq0.
without loss{nCq} qx0: q mon_q q_dv_p / root (q ^ FtoL) x.
  have /dvdpP[q1 Dp] := q_dv_p; rewrite DpI Dp rmorphM rootM -implyNb in pIx0.
  have mon_q1: q1 \is monic by rewrite Dp monicMr in mon_p.
  move=> IH; apply: (IH) (implyP pIx0 _) => //; apply: contra nCq => /IH IHq1.
  rewrite -(subnn (size q1)) {1}IHq1 ?Dp ?dvdp_mulr // polySpred ?monic_neq0 //.
  by rewrite eqSS size_monicM ?monic_neq0 // -!subn1 subnAC addKn.
have /dvdp_prod_XsubC[m Dq]: q ^ FtoL %| p_ I by rewrite DpI dvdp_map.
pose B := [set j in mask m (enum I)]; have{Dq} Dq: q ^ FtoL = p_ B.
  apply/eqP; rewrite -eqp_monic ?monic_map ?monic_prod_XsubC //.
  congr (_ %= _): Dq; apply: eq_big_perm => //.
  by rewrite uniq_perm_eq ?mask_uniq ?enum_uniq // => j; rewrite mem_enum inE.
rewrite -!(size_map_poly FtoL) Dq -DpI (minI B) // -?Dq ?FpxF //.
by apply/subsetP=> j; rewrite inE => /mem_mask; rewrite mem_enum.
Qed.

Lemma alg_integral (F : fieldType) (L : fieldExtType F) :
  integralRange (in_alg L).
Proof.
move=> x; have [/polyOver1P[p Dp]] := (minPolyOver 1 x, monic_minPoly 1 x).
by rewrite Dp map_monic; exists p; rewrite // -Dp root_minPoly.
Qed.
Prenex Implicits alg_integral.

Import DefaultKeying GRing.DefaultPred.
Arguments map_poly_inj {F R} f [p1 p2].

Theorem Fundamental_Theorem_of_Algebraics :
  {L : closedFieldType &
     {conj : {rmorphism L -> L} | involutive conj & ~ conj =1 id}}.
Proof.
have maxn3 n1 n2 n3: {m | [/\ n1 <= m, n2 <= m & n3 <= m]%N}.
  by exists (maxn n1 (maxn n2 n3)); apply/and3P; rewrite -!geq_max.
have [C [/= QtoC algC]] := countable_algebraic_closure [countFieldType of rat].
exists C; have [i Di2] := GRing.imaginary_exists C.
pose Qfield := fieldExtType rat; pose Cmorph (L : Qfield) := {rmorphism L -> C}.
have charQ (L : Qfield): [char L] =i pred0 := ftrans (char_lalg L) (char_num _).
have sepQ  (L : Qfield) (K E : {subfield L}): separable K E.
  by apply/separableP=> u _; apply: charf0_separable.
pose genQfield z L := {LtoC : Cmorph L & {u | LtoC u = z & <<1; u>> = fullv}}.
have /all_tag[Q /all_tag[ofQ genQz]] z: {Qz : Qfield & genQfield z Qz}.
  have [|p [/monic_neq0 nzp pz0 irr_p]] := minPoly_decidable_closure _ (algC z).
    exact: rat_algebraic_decidable.
  pose Qz := SubFieldExtType pz0 irr_p.
  pose QzC := subfx_inj_rmorphism QtoC z p.
  exists Qz, QzC, (subfx_root QtoC z p); first exact: subfx_inj_root.
  apply/vspaceP=> u; rewrite memvf; apply/Fadjoin1_polyP.
  by have [q] := subfxEroot pz0 nzp u; exists q.
have pQof z p: p^@ ^ ofQ z = p ^ QtoC.
  by rewrite -map_poly_comp; apply: eq_map_poly => x; rewrite !fmorph_eq_rat.
have pQof2 z p u: ofQ z p^@.[u] = (p ^ QtoC).[ofQ z u].
  by rewrite -horner_map pQof.
have PET_Qz z (E : {subfield Q z}): {u | <<1; u>> = E}.
  exists (separable_generator 1 E).
  by rewrite -eq_adjoin_separable_generator ?sub1v.
pose gen z x := exists q, x = (q ^ QtoC).[z].
have PET2 x y: {z | gen z x & gen z y}.
  pose Gxy := (x, y) = let: (p, q, z) := _ in ((p ^ QtoC).[z], (q ^ QtoC).[z]).
  suffices [[[p q] z] []]: {w | Gxy w} by exists z; [exists p | exists q].
  apply/sig_eqW; have /integral_algebraic[px nz_px pxx0] := algC x.
  have /integral_algebraic[py nz_py pyy0] := algC y.
  have [n [[p Dx] [q Dy]]] := char0_PET nz_px pxx0 nz_py pyy0 (char_num _).
  by exists (p, q, y *+ n - x); congr (_, _).
have gen_inQ z x: gen z x -> {u | ofQ z u = x}.
  have [u Dz _] := genQz z => /sig_eqW[q ->].
  by exists q^@.[u]; rewrite pQof2 Dz.
have gen_ofP z u v: reflect (gen (ofQ z u) (ofQ z v)) (v \in <<1; u>>).
  apply: (iffP Fadjoin1_polyP) => [[q ->]|]; first by rewrite pQof2; exists q.
  by case=> q; rewrite -pQof2 => /fmorph_inj->; exists q.
have /all_tag[sQ genP] z: {s : pred C & forall x, reflect (gen z x) (x \in s)}.
  apply: all_tag (fun x => reflect (gen z x)) _ => x.
  have [w /gen_inQ[u <-] /gen_inQ[v <-]] := PET2 z x.
  by exists (v \in <<1; u>>)%VS; apply: gen_ofP.
have sQtrans: transitive (fun x z => x \in sQ z).
  move=> x y z /genP[p ->] /genP[q ->]; apply/genP; exists (p \Po q).
  by rewrite map_comp_poly horner_comp.
have sQid z: z \in sQ z by apply/genP; exists 'X; rewrite map_polyX hornerX.
have{gen_ofP} sQof2 z u v: (ofQ z u \in sQ (ofQ z v)) = (u \in <<1; v>>%VS).
  exact/genP/(gen_ofP z).
have sQof z v: ofQ z v \in sQ z.
  by have [u Dz defQz] := genQz z; rewrite -[in sQ z]Dz sQof2 defQz memvf.
have{gen_inQ} sQ_inQ z x z_x := gen_inQ z x (genP z x z_x).
have /all_sig[inQ inQ_K] z: {inQ | {in sQ z, cancel inQ (ofQ z)}}.
  by apply: all_sig_cond (fun x u => ofQ z u = x) 0 _ => x /sQ_inQ.
have ofQ_K z: cancel (ofQ z) (inQ z).
  by move=> x; have /inQ_K/fmorph_inj := sQof z x.
have sQring z: divring_closed (sQ z).
  have sQ_1: 1 \in sQ z by rewrite -(rmorph1 (ofQ z)) sQof.
  by split=> // x y /inQ_K<- /inQ_K<- /=; rewrite -(rmorphB, fmorph_div) sQof.
have sQopp z : oppr_closed (sQ z) := sQring z.
have sQadd z : addr_closed (sQ z) := sQring z.
have sQmul z : mulr_closed (sQ z) := sQring z.
have sQinv z : invr_closed (sQ z) := sQring z.
pose morph_ofQ x z Qxz := forall u, ofQ z (Qxz u) = ofQ x u.
have QtoQ z x: x \in sQ z -> {Qxz : 'AHom(Q x, Q z) | morph_ofQ x z Qxz}.
  move=> z_x; pose Qxz u := inQ z (ofQ x u).
  have QxzE u: ofQ z (Qxz u) = ofQ x u by apply/inQ_K/(sQtrans x).
  suffices /rat_lrmorphism QxzM: rmorphism Qxz.
    by exists (linfun_ahom (LRMorphism QxzM)) => u; rewrite lfunE QxzE.
  split=> [u v|]; first by apply: (canLR (ofQ_K z)); rewrite !rmorphB !QxzE.
  by split=> [u v|]; apply: (canLR (ofQ_K z)); rewrite ?rmorph1 ?rmorphM ?QxzE.
pose sQs z s := all (mem (sQ z)) s.
have inQsK z s: sQs z s -> map (ofQ z) (map (inQ z) s) = s.
  by rewrite -map_comp => /allP/(_ _ _)/inQ_K; apply: map_id_in.
have inQpK z p: p \is a polyOver (sQ z) -> (p ^ inQ z) ^ ofQ z = p.
  by move=> /allP/(_ _ _)/inQ_K/=/map_poly_id; rewrite -map_poly_comp.
have{gen PET2 genP} PET s: {z | sQs z s & <<1 & map (inQ z) s>>%VS = fullv}.
  have [y /inQsK Ds]: {y | sQs y s}.
    elim: s => [|x s /= [y IHs]]; first by exists 0.
    have [z /genP z_x /genP z_y] := PET2 x y.
    by exists z; rewrite /= {x}z_x; apply: sub_all IHs => x /sQtrans/= ->.
  have [w defQs] := PET_Qz _ <<1 & map (inQ y) s>>%AS; pose z := ofQ y w.
  have z_s: sQs z s.
    rewrite -Ds /sQs all_map; apply/allP=> u s_u /=.
    by rewrite sQof2 defQs seqv_sub_adjoin.
  have [[u Dz defQz] [Qzy QzyE]] := (genQz z, QtoQ y z (sQof y w)).
  exists z => //; apply/eqP; rewrite eqEsubv subvf /= -defQz.
  rewrite -(limg_ker0 _ _ (AHom_lker0 Qzy)) aimg_adjoin_seq aimg_adjoin aimg1.
  rewrite -[map _ _](mapK (ofQ_K y)) -(map_comp (ofQ y)) (eq_map QzyE) inQsK //.
  by rewrite -defQs -(canLR (ofQ_K y) Dz) -QzyE ofQ_K.
pose rp s := \prod_(z <- s) ('X - z%:P).
have map_rp (f : {rmorphism _}) s: rp _ s ^ f = rp _ (map f s).
  rewrite rmorph_prod /rp big_map; apply: eq_bigr => x _.
  by rewrite rmorphB /= map_polyX map_polyC.
pose is_Gal z := SplittingField.axiom (Q z).
have galQ x: {z | x \in sQ z & is_Gal z}.
  have /sig2W[p mon_p pz0] := algC x.
  have [s Dp] := closed_field_poly_normal (p ^ QtoC).
  rewrite (monicP _) ?monic_map // scale1r in Dp; have [z z_s defQz] := PET s.
  exists z; first by apply/(allP z_s); rewrite -root_prod_XsubC -Dp.
  exists p^@; first exact: alg_polyOver.
  exists (map (inQ z) s); last by apply/vspaceP=> u; rewrite defQz memvf.
  by rewrite -(eqp_map (ofQ z)) pQof Dp map_rp inQsK ?eqpxx.
pose is_realC x := {R : archiFieldType & {rmorphism Q x -> R}}.
pose realC := {x : C & is_realC x}.
pose has_Rroot (xR : realC) p c (Rx := sQ (tag xR)) :=
  [&& p \is a polyOver Rx, p \is monic, c \in Rx & p.[0] == - c ^+ 2].
pose root_in (xR : realC) p := exists2 w, w \in sQ (tag xR) & root p w.
pose extendsR (xR yR : realC) := tag xR \in sQ (tag yR).
have add_Rroot xR p c: {yR | extendsR xR yR & has_Rroot xR p c -> root_in yR p}.
  rewrite {}/extendsR; case: (has_Rroot xR p c) / and4P; last by exists xR.
  case: xR => x [R QxR] /= [/inQpK <-]; move: (p ^ _) => {p}p mon_p /inQ_K<- Dc.
  have{c Dc} p0_le0: (p ^ QxR).[0] <= 0.
    rewrite horner_coef0 coef_map -[p`_0]ofQ_K -coef_map -horner_coef0 (eqP Dc).
    by rewrite -rmorphX -rmorphN ofQ_K /= rmorphN rmorphX oppr_le0 sqr_ge0.
  have [s Dp] := closed_field_poly_normal (p ^ ofQ x).
  have{Dp} /all_and2[s_p p_s] y: root (p ^ ofQ x) y <-> (y \in s).
    by rewrite Dp (monicP mon_p) scale1r root_prod_XsubC.
  rewrite map_monic in mon_p; have [z /andP[z_x /allP/=z_s] _] := PET (x :: s).
  have{z_x} [[Qxz QxzE] Dx] := (QtoQ z x z_x, inQ_K z x z_x).
  pose Qx := <<1; inQ z x>>%AS; pose QxzM := [rmorphism of Qxz].
  have pQwx q1: q1 \is a polyOver Qx -> {q | q1 = q ^ Qxz}.
    move/polyOverP=> Qx_q1; exists ((q1 ^ ofQ z) ^ inQ x).
    apply: (map_poly_inj (ofQ z)); rewrite -map_poly_comp (eq_map_poly QxzE).
    by rewrite inQpK ?polyOver_poly // => j _; rewrite -Dx sQof2 Qx_q1.
  have /all_sig[t_ Dt] u: {t | <<1; t>> = <<Qx; u>>} by apply: PET_Qz.
  suffices{p_s}[u Ry px0]: {u : Q z & is_realC (ofQ z (t_ u)) & ofQ z u \in s}.
    exists (Tagged is_realC Ry) => [|_] /=.
      by rewrite -Dx sQof2 Dt subvP_adjoin ?memv_adjoin.
    by exists (ofQ z u); rewrite ?p_s // sQof2 Dt memv_adjoin.
  without loss{z_s s_p} [u Dp s_y]: p mon_p p0_le0 /
    {u | minPoly Qx u = p ^ Qxz & ofQ z u \in s}.
  - move=> IHp; move: {2}_.+1 (ltnSn (size p)) => d.
    elim: d => // d IHd in p mon_p s_p p0_le0 *; rewrite ltnS => le_p_d.
    have /closed_rootP/sig_eqW[y py0]: size (p ^ ofQ x) != 1%N.
      rewrite size_map_poly size_poly_eq1 eqp_monic ?rpred1 //.
      by apply: contraTneq p0_le0 => ->; rewrite rmorph1 hornerC ltr_geF ?ltr01.
    have /s_p s_y := py0; have /z_s/sQ_inQ[u Dy] := s_y.
    have /pQwx[q Dq] := minPolyOver Qx u.
    have mon_q: q \is monic by have:= monic_minPoly Qx u; rewrite Dq map_monic.
    have /dvdpP/sig_eqW[r Dp]: q %| p.
      rewrite -(dvdp_map QxzM) -Dq minPoly_dvdp //.
        by apply: polyOver_poly => j _; rewrite -sQof2 QxzE Dx.
      by rewrite -(fmorph_root (ofQ z)) Dy -map_poly_comp (eq_map_poly QxzE).
    have mon_r: r \is monic by rewrite Dp monicMr in mon_p.
    have [q0_le0 | q0_gt0] := lerP ((q ^ QxR).[0]) 0.
      by apply: (IHp q) => //; exists u; rewrite ?Dy.
    have r0_le0: (r ^ QxR).[0] <= 0.
      by rewrite -(ler_pmul2r q0_gt0) mul0r -hornerM -rmorphM -Dp.
    apply: (IHd r mon_r) => // [w rw0|].
      by rewrite s_p // Dp rmorphM rootM rw0.
    apply: leq_trans le_p_d; rewrite Dp size_Mmonic ?monic_neq0 // addnC.
    by rewrite -(size_map_poly QxzM q) -Dq size_minPoly !ltnS leq_addl.
  exists u => {s s_y}//; set y := ofQ z (t_ u); set p1 := minPoly Qx u in Dp.
  have /QtoQ[Qyz QyzE]: y \in sQ z := sQof z (t_ u).
  pose q1_ v := Fadjoin_poly Qx u (Qyz v).
  have{QyzE} QyzE v: Qyz v = (q1_ v).[u].
    by rewrite Fadjoin_poly_eq // -Dt -sQof2 QyzE sQof.
  have /all_sig2[q_ coqp Dq] v: {q | v != 0 -> coprimep p q & q ^ Qxz = q1_ v}.
    have /pQwx[q Dq]: q1_ v \is a polyOver Qx by apply: Fadjoin_polyOver.
    exists q => // nz_v; rewrite -(coprimep_map QxzM) -Dp -Dq -gcdp_eqp1.
    have /minPoly_irr/orP[] // := dvdp_gcdl p1 (q1_ v).
      by rewrite gcdp_polyOver ?minPolyOver ?Fadjoin_polyOver.
    rewrite -/p1 {1}/eqp dvdp_gcd => /and3P[_ _ /dvdp_leq/=/implyP].
    rewrite size_minPoly ltnNge size_poly (contraNneq _ nz_v) // => q1v0.
    by rewrite -(fmorph_eq0 [rmorphism of Qyz]) /= QyzE q1v0 horner0.
  pose h2 : R := 2%:R^-1; have nz2: 2%:R != 0 :> R by rewrite pnatr_eq0.
  pose itv ab := [pred c : R | ab.1 <= c <= ab.2].
  pose wid ab : R := ab.2 - ab.1; pose mid ab := (ab.1 + ab.2) * h2.
  pose sub_itv ab cd := cd.1 <= ab.1 :> R /\ ab.2 <= cd.2 :> R.
  pose xup q ab := [/\ q.[ab.1] <= 0, q.[ab.2] >= 0 & ab.1 <= ab.2 :> R].
  pose narrow q ab (c := mid ab) := if q.[c] >= 0 then (ab.1, c) else (c, ab.2).
  pose find k q := iter k (narrow q).
  have findP k q ab (cd := find k q ab):
    xup q ab -> [/\ xup q cd, sub_itv cd ab & wid cd = wid ab / (2 ^ k)%:R].
  - rewrite {}/cd; case: ab => a b xq_ab.
    elim: k => /= [|k]; first by rewrite divr1.
    case: (find k q _) => c d [[/= qc_le0 qd_ge0 le_cd] [/= le_ac le_db] Dcd].
    have [/= le_ce le_ed] := midf_le le_cd; set e := _ / _ in le_ce le_ed.
    rewrite expnSr natrM invfM mulrA -{}Dcd /narrow /= -[mid _]/e.
    have [qe_ge0 // | /ltrW qe_le0] := lerP 0 q.[e].
      do ?split=> //=; [exact: (ler_trans le_ed) | apply: canRL (mulfK nz2) _].
      by rewrite mulrBl divfK // mulr_natr opprD addrACA subrr add0r.
    do ?split=> //=; [exact: (ler_trans le_ac) | apply: canRL (mulfK nz2) _].
    by rewrite mulrBl divfK // mulr_natr opprD addrACA subrr addr0.
  have find_root r q ab:
    xup q ab -> {n | forall x, x \in itv (find n q ab) ->`|(r * q).[x]| < h2}.
  - move=> xab; have ub_ab := poly_itv_bound _ ab.1 ab.2.
    have [Mu MuP] := ub_ab r; have /all_sig[Mq MqP] j := ub_ab q^`N(j).
    pose d := wid ab; pose dq := \poly_(i < (size q).-1) Mq i.+1.
    have d_ge0: 0 <= d by rewrite subr_ge0; case: xab.
    have [Mdq MdqP] := poly_disk_bound dq d.
    pose n := Num.bound (Mu * Mdq * d); exists n => c /= /andP[].
    have{xab} [[]] := findP n _ _ xab; case: (find n q ab) => a1 b1 /=.
    rewrite -/d => qa1_le0 qb1_ge0 le_ab1 [/= le_aa1 le_b1b] Dab1 le_a1c le_cb1.
    have /MuP lbMu: c \in itv ab.
      by rewrite !inE (ler_trans le_aa1) ?(ler_trans le_cb1).
    have Mu_ge0: 0 <= Mu by rewrite (ler_trans _ lbMu) ?normr_ge0.
    have Mdq_ge0: 0 <= Mdq.
      by rewrite (ler_trans _ (MdqP 0 _)) ?normr_ge0 ?normr0.
    suffices lb1 a2 b2 (ab1 := (a1, b1)) (ab2 := (a2, b2)) :
      xup q ab2 /\ sub_itv ab2 ab1 -> q.[b2] - q.[a2] <= Mdq * wid ab1.
    + apply: ler_lt_trans (_ : Mu * Mdq * wid (a1, b1) < h2); last first.
        rewrite {}Dab1 mulrA ltr_pdivr_mulr ?ltr0n ?expn_gt0 //.
        rewrite (ltr_le_trans (archi_boundP _)) ?mulr_ge0 ?ltr_nat // -/n.
        rewrite ler_pdivl_mull ?ltr0n // -natrM ler_nat.
        by case: n => // n; rewrite expnS leq_pmul2l // ltn_expl.
      rewrite -mulrA hornerM normrM ler_pmul ?normr_ge0 //.
      have [/ltrW qc_le0 | qc_ge0] := ltrP q.[c] 0.
        by apply: ler_trans (lb1 c b1 _); rewrite ?ler0_norm ?ler_paddl.
      by apply: ler_trans (lb1 a1 c _); rewrite ?ger0_norm ?ler_paddr ?oppr_ge0.
    case{c le_a1c le_cb1 lbMu}=> [[/=qa2_le0 qb2_ge0 le_ab2] [/=le_a12 le_b21]].
    pose h := b2 - a2; have h_ge0: 0 <= h by rewrite subr_ge0.
    have [-> | nz_q] := eqVneq q 0.
      by rewrite !horner0 subrr mulr_ge0 ?subr_ge0.
    rewrite -(subrK a2 b2) (addrC h) (nderiv_taylor q (mulrC a2 h)).
    rewrite (polySpred nz_q) big_ord_recl /= mulr1 nderivn0 addrC addKr.
    have [le_aa2 le_b2b] := (ler_trans le_aa1 le_a12, ler_trans le_b21 le_b1b).
    have /MqP MqPx1: a2 \in itv ab by rewrite inE le_aa2 (ler_trans le_ab2).
    apply: ler_trans (ler_trans (ler_norm _) (ler_norm_sum _ _ _)) _.
    apply: ler_trans (_ : `|dq.[h] * h| <= _); last first.
      by rewrite normrM ler_pmul ?normr_ge0 ?MdqP // ?ger0_norm ?ler_sub ?h_ge0.
    rewrite horner_poly ger0_norm ?mulr_ge0 ?sumr_ge0 // => [|j _]; last first.
      by rewrite mulr_ge0 ?exprn_ge0 // (ler_trans _ (MqPx1 _)) ?normr_ge0.
    rewrite mulr_suml ler_sum // => j _; rewrite normrM -mulrA -exprSr.
    by rewrite ler_pmul ?normr_ge0 // normrX ger0_norm.
  have [ab0 xab0]: {ab | xup (p ^ QxR) ab}.
    have /monic_Cauchy_bound[b pb_gt0]: p ^ QxR \is monic by apply: monic_map.
    by exists (0, `|b|); rewrite /xup normr_ge0 p0_le0 ltrW ?pb_gt0 ?ler_norm.
  pose ab_ n := find n (p ^ QxR) ab0; pose Iab_ n := itv (ab_ n).
  pose lim v a := (q_ v ^ QxR).[a]; pose nlim v n := lim v (ab_ n).2.
  have lim0 a: lim 0 a = 0.
    rewrite /lim; suffices /eqP ->: q_ 0 == 0 by rewrite rmorph0 horner0.
    by rewrite -(map_poly_eq0 QxzM) Dq /q1_ !raddf0.
  have limN v a: lim (- v) a = - lim v a.
    rewrite /lim; suffices ->: q_ (- v) = - q_ v by rewrite rmorphN hornerN.
    by apply: (map_poly_inj QxzM); rewrite Dq /q1_ !raddfN /= Dq.
  pose lim_nz n v := exists2 e, e > 0 & {in Iab_ n, forall a, e < `|lim v a| }.
  have /(all_sig_cond 0%N)[n_ nzP] v: v != 0 -> {n | lim_nz n v}.
    move=> nz_v; do [move/(_ v nz_v); rewrite -(coprimep_map QxR)] in coqp.
    have /sig_eqW[r r_pq_1] := Bezout_eq1_coprimepP _ _ coqp.
    have /(find_root r.1)[n ub_rp] := xab0; exists n.
    have [M Mgt0 ubM]: {M | 0 < M & {in Iab_ n, forall a, `|r.2.[a]| <= M}}.
      have [M ubM] := poly_itv_bound r.2 (ab_ n).1 (ab_ n).2.
      exists (Num.max 1 M) => [|s /ubM vM]; first by rewrite ltr_maxr ltr01.
      by rewrite ler_maxr orbC vM.
    exists (h2 / M) => [|a xn_a]; first by rewrite divr_gt0 ?invr_gt0 ?ltr0n.
    rewrite ltr_pdivr_mulr // -(ltr_add2l h2) -mulr2n -mulr_natl divff //.
    rewrite -normr1 -(hornerC 1 a) -[1%:P]r_pq_1 hornerD.
    rewrite ?(ler_lt_trans (ler_norm_add _ _)) ?ltr_le_add ?ub_rp //.
    by rewrite mulrC hornerM normrM ler_wpmul2l ?ubM.
  have ab_le m n: (m <= n)%N -> (ab_ n).2 \in Iab_ m.
    move/subnKC=> <-; move: {n}(n - m)%N => n; rewrite /ab_.
    have /(findP m)[/(findP n)[[_ _]]] := xab0.
    rewrite /find -iter_add -!/(find _ _) -!/(ab_ _) addnC !inE.
    by move: (ab_ _) => /= ab_mn le_ab_mn [/ler_trans->].
  pose lt v w := 0 < nlim (w - v) (n_ (w - v)).
  have posN v: lt 0 (- v) = lt v 0 by rewrite /lt subr0 add0r.
  have posB v w: lt 0 (w - v) = lt v w by rewrite /lt subr0.
  have posE n v: (n_ v <= n)%N -> lt 0 v = (0 < nlim v n).
    rewrite /lt subr0 /nlim => /ab_le; set a := _.2; set b := _.2 => Iv_a.
    have [-> | /nzP[e e_gt0]] := eqVneq v 0; first by rewrite !lim0 ltrr.
    move: (n_ v) => m in Iv_a b * => v_gte.
    without loss lt0v: v v_gte / 0 < lim v b.
      move=> IHv; apply/idP/idP => [v_gt0 | /ltrW]; first by rewrite -IHv.
      rewrite ltr_def -normr_gt0 ?(ltr_trans _ (v_gte _ _)) ?ab_le //=.
      rewrite !lerNgt -!oppr_gt0 -!limN; apply: contra => v_lt0.
      by rewrite -IHv // => c /v_gte; rewrite limN normrN.
    rewrite lt0v (ltr_trans e_gt0) ?(ltr_le_trans (v_gte a Iv_a)) //.
    rewrite ger0_norm // lerNgt; apply/negP=> /ltrW lev0.
    have [le_a le_ab] : _ /\ a <= b := andP Iv_a.
    have xab: xup (q_ v ^ QxR) (a, b) by move/ltrW in lt0v.
    have /(find_root (h2 / e)%:P)[n1] := xab; have /(findP n1)[[_ _]] := xab.
    case: (find _ _ _) => c d /= le_cd [/= le_ac le_db] _ /(_ c)/implyP.
    rewrite inE lerr le_cd hornerM hornerC normrM ler_gtF //.
    rewrite ger0_norm ?divr_ge0 ?invr_ge0 ?ler0n ?(ltrW e_gt0) // mulrAC.
    rewrite ler_pdivl_mulr // ler_wpmul2l ?invr_ge0 ?ler0n // ltrW // v_gte //=.
    by rewrite inE -/b (ler_trans le_a) //= (ler_trans le_cd).
  pose lim_pos m v := exists2 e, e > 0 & forall n, (m <= n)%N -> e < nlim v n.
  have posP v: reflect (exists m, lim_pos m v) (lt 0 v).
    apply: (iffP idP) => [v_gt0|[m [e e_gt0 v_gte]]]; last first.
      by rewrite (posE _ _ (leq_maxl _ m)) (ltr_trans e_gt0) ?v_gte ?leq_maxr.
    have [|e e_gt0 v_gte] := nzP v.
      by apply: contraTneq v_gt0 => ->; rewrite /lt subr0 /nlim lim0 ltrr.
    exists (n_ v), e => // n le_vn; rewrite (posE n) // in v_gt0.
    by rewrite -(ger0_norm (ltrW v_gt0)) v_gte ?ab_le.
  have posNneg v: lt 0 v -> ~~ lt v 0.
    case/posP=> m [d d_gt0 v_gtd]; rewrite -posN.
    apply: contraL d_gt0 => /posP[n [e e_gt0 nv_gte]].
    rewrite ltr_gtF // (ltr_trans (v_gtd _ (leq_maxl m n))) // -oppr_gt0.
    by rewrite /nlim -limN (ltr_trans e_gt0) ?nv_gte ?leq_maxr.
  have posVneg v: v != 0 -> lt 0 v || lt v 0.
    case/nzP=> e e_gt0 v_gte; rewrite -posN; set w := - v.
    have [m [le_vm le_wm _]] := maxn3 (n_ v) (n_ w) 0%N; rewrite !(posE m) //.
    by rewrite /nlim limN -ltr_normr (ltr_trans e_gt0) ?v_gte ?ab_le.
  have posD v w: lt 0 v -> lt 0 w -> lt 0 (v + w).
    move=> /posP[m [d d_gt0 v_gtd]] /posP[n [e e_gt0 w_gte]].
    apply/posP; exists (maxn m n), (d + e) => [|k]; first exact: addr_gt0.
    rewrite geq_max => /andP[le_mk le_nk]; rewrite /nlim /lim.
    have ->: q_ (v + w) = q_ v + q_ w.
      by apply: (map_poly_inj QxzM); rewrite rmorphD /= !{1}Dq /q1_ !raddfD.
    by rewrite rmorphD hornerD ltr_add ?v_gtd ?w_gte.
  have posM v w: lt 0 v -> lt 0 w -> lt 0 (v * w).
    move=> /posP[m [d d_gt0 v_gtd]] /posP[n [e e_gt0 w_gte]].
    have /dvdpP[r /(canRL (subrK _))Dqvw]: p %| q_ (v * w) - q_ v * q_ w.
      rewrite -(dvdp_map QxzM) rmorphB rmorphM /= !Dq -Dp minPoly_dvdp //.
        by rewrite rpredB 1?rpredM ?Fadjoin_polyOver.
      by rewrite rootE !hornerE -!QyzE rmorphM subrr.
    have /(find_root ((d * e)^-1 *: r ^ QxR))[N ub_rp] := xab0.
    pose f := d * e * h2; apply/posP; exists (maxn N (maxn m n)), f => [|k].
      by rewrite !mulr_gt0 ?invr_gt0 ?ltr0n.
    rewrite !geq_max => /and3P[/ab_le/ub_rp{ub_rp}ub_rp le_mk le_nk].
    rewrite -(ltr_add2r f) -mulr2n -mulr_natr divfK // /nlim /lim Dqvw.
    rewrite rmorphD hornerD /= -addrA -ltr_subl_addl ler_lt_add //.
      by rewrite rmorphM hornerM ler_pmul ?ltrW ?v_gtd ?w_gte.
    rewrite -ltr_pdivr_mull ?mulr_gt0 // (ler_lt_trans _ ub_rp) //.
    by rewrite -scalerAl hornerZ -rmorphM mulrN -normrN ler_norm.
  pose le v w := (w == v) || lt v w.
  pose abs v := if le 0 v then v else - v.
  have absN v: abs (- v) = abs v.
    rewrite /abs /le oppr_eq0 opprK posN.
    have [-> | /posVneg/orP[v_gt0 | v_lt0]] := altP eqP; first by rewrite oppr0.
      by rewrite v_gt0 /= -if_neg posNneg.
    by rewrite v_lt0 /= -if_neg -(opprK v) posN posNneg ?posN.
  have absE v: le 0 v -> abs v = v by rewrite /abs => ->.
  pose QyNum := RealLtMixin posD posM posNneg posB posVneg absN absE (rrefl _).
  pose QyNumField := [numFieldType of NumDomainType (Q y) QyNum].
  pose Ry := [realFieldType of RealDomainType _ (RealLeAxiom QyNumField)].
  have archiRy := @rat_algebraic_archimedean Ry _ alg_integral.
  by exists (ArchiFieldType Ry archiRy); apply: [rmorphism of idfun].
have some_realC: realC.
  suffices /all_sig[f QfK] x: {a | in_alg (Q 0) a = x}.
    exists 0, [archiFieldType of rat], f.
    exact: can2_rmorphism (inj_can_sym QfK (fmorph_inj _)) QfK.
  have /Fadjoin1_polyP/sig_eqW[q]: x \in <<1; 0>>%VS by rewrite -sQof2 rmorph0.
  by exists q.[0]; rewrite -horner_map rmorph0.
pose fix xR n : realC :=
  if n isn't n'.+1 then some_realC else
  if unpickle (nth 0%N (CodeSeq.decode n') 1) isn't Some (p, c) then xR n' else
  tag (add_Rroot (xR n') p c).
pose x_ n := tag (xR n).
have sRle m n: (m <= n)%N -> {subset sQ (x_ m) <= sQ (x_ n)}.
  move/subnK <-; elim: {n}(n - m)%N => // n IHn x /IHn{IHn}Rx.
  rewrite addSn /x_ /=; case: (unpickle _) => [[p c]|] //=.
  by case: (add_Rroot _ _ _) => yR /= /(sQtrans _ x)->.
have xRroot n p c: has_Rroot (xR n) p c -> {m | n <= m & root_in (xR m) p}%N.
  case/and4P=> Rp mon_p Rc Dc; pose m := CodeSeq.code [:: n; pickle (p, c)].
  have le_n_m: (n <= m)%N by apply/ltnW/(allP (CodeSeq.ltn_code _))/mem_head.
  exists m.+1; rewrite ?leqW /x_ //= CodeSeq.codeK pickleK.
  case: (add_Rroot _ _ _) => yR /= _; apply; apply/and4P.
  by split=> //; first apply: polyOverS Rp; apply: (sRle n).
have /all_sig[z_ /all_and3[Ri_R Ri_i defRi]] n (x := x_ n):
  {z | [/\ x \in sQ z, i \in sQ z & <<<<1; inQ z x>>; inQ z i>> = fullv]}.
- have [z /and3P[z_x z_i _] Dzi] := PET [:: x; i].
  by exists z; rewrite -adjoin_seq1 -adjoin_cons.
pose i_ n := inQ (z_ n) i; pose R_ n := <<1; inQ (z_ n) (x_ n)>>%AS.
have memRi n: <<R_ n; i_ n>> =i predT by move=> u; rewrite defRi memvf.
have sCle m n: (m <= n)%N -> {subset sQ (z_ m) <= sQ (z_ n)}.
  move/sRle=> Rmn _ /sQ_inQ[u <-].
  have /Fadjoin_polyP[p /polyOverP Rp ->] := memRi m u.
  rewrite -horner_map inQ_K ?rpred_horner //=; apply/polyOver_poly=> j _.
  by apply: sQtrans (Ri_R n); rewrite Rmn // -(inQ_K _ _ (Ri_R m)) sQof2.
have R'i n: i \notin sQ (x_ n).
  rewrite /x_; case: (xR n) => x [Rn QxR] /=.
  apply: contraL (@ltr01 Rn) => /sQ_inQ[v Di].
  suffices /eqP <-: - QxR v ^+ 2 == 1 by rewrite oppr_gt0 -lerNgt sqr_ge0.
  rewrite -rmorphX -rmorphN fmorph_eq1 -(fmorph_eq1 (ofQ x)) rmorphN eqr_oppLR.
  by rewrite rmorphX Di Di2.
have szX2_1: size ('X^2 + 1) = 3.
  by move=> R; rewrite size_addl ?size_polyXn ?size_poly1.
have minp_i n (p_i := minPoly (R_ n) (i_ n)): p_i = 'X^2 + 1.
  have p_dv_X2_1: p_i %| 'X^2 + 1.
    rewrite minPoly_dvdp ?rpredD ?rpredX ?rpred1 ?polyOverX //.
    rewrite -(fmorph_root (ofQ _)) inQ_K // rmorphD rmorph1 /= map_polyXn.
    by rewrite rootE hornerD hornerXn hornerC Di2 addNr.
  apply/eqP; rewrite -eqp_monic ?monic_minPoly //; last first.
    by rewrite monicE lead_coefE szX2_1 coefD coefXn coefC addr0.
  rewrite -dvdp_size_eqp // eqn_leq dvdp_leq -?size_poly_eq0 ?szX2_1 //= ltnNge.
  by rewrite size_minPoly ltnS leq_eqVlt orbF adjoin_deg_eq1 -sQof2 !inQ_K.
have /all_sig[n_ FTA] z: {n | z \in sQ (z_ n)}.
  without loss [z_i gal_z]: z / i \in sQ z /\ is_Gal z.
    have [y /and3P[/sQtrans y_z /sQtrans y_i _] _] := PET [:: z; i].
    have [t /sQtrans t_y gal_t] := galQ y.
    by case/(_ t)=> [|n]; last exists n; rewrite ?y_z ?y_i ?t_y.
  apply/sig_eqW; have n := 0%N.
  have [p]: exists p, [&& p \is monic, root p z & p \is a polyOver (sQ (z_ n))].
    have [p mon_p pz0] := algC z; exists (p ^ QtoC).
    by rewrite map_monic mon_p pz0 -(pQof (z_ n)); apply/polyOver_poly.
  elim: {p}_.+1 {-2}p n (ltnSn (size p)) => // d IHd p n lepd pz0.
  have [t [t_C t_z gal_t]]: exists t, [/\ z_ n \in sQ t, z \in sQ t & is_Gal t].
    have [y /and3P[y_C y_z _]] := PET [:: z_ n; z].
    by have [t /(sQtrans y)t_y] := galQ y; exists t; rewrite !t_y.
  pose Qt := SplittingFieldType rat (Q t) gal_t; have /QtoQ[CnQt CnQtE] := t_C.
  pose Rn : {subfield Qt} := (CnQt @: R_ n)%AS; pose i_t : Qt := CnQt (i_ n).
  pose Cn : {subfield Qt} := <<Rn; i_t>>%AS.
  have defCn: Cn = limg CnQt :> {vspace Q t} by rewrite /= -aimg_adjoin defRi.
  have memRn u: (u \in Rn) = (ofQ t u \in sQ (x_ n)).
    by rewrite /= aimg_adjoin aimg1 -sQof2 CnQtE inQ_K.
  have memCn u: (u \in Cn) = (ofQ t u \in sQ (z_ n)).
    have [v Dv genCn] := genQz (z_ n).
    by rewrite -Dv -CnQtE sQof2 defCn -genCn aimg_adjoin aimg1.
  have Dit: ofQ t i_t = i by rewrite CnQtE inQ_K.
  have Dit2: i_t ^+ 2 = -1.
    by apply: (fmorph_inj (ofQ t)); rewrite rmorphX rmorphN1 Dit.
  have dimCn: \dim_Rn Cn = 2.
    rewrite -adjoin_degreeE adjoin_degree_aimg.
    by apply: succn_inj; rewrite -size_minPoly minp_i.
  have /sQ_inQ[u_z Dz] := t_z; pose Rz := <<Cn; u_z>>%AS.
  have{p lepd pz0} le_Rz_d: (\dim_Cn Rz < d)%N.
    rewrite -ltnS -adjoin_degreeE -size_minPoly (leq_trans _ lepd) // !ltnS.
    have{pz0} [mon_p pz0 Cp] := and3P pz0.
    have{Cp} Dp: ((p ^ inQ (z_ n)) ^ CnQt) ^ ofQ t = p.
      by rewrite -map_poly_comp (eq_map_poly CnQtE) inQpK.
    rewrite -Dp size_map_poly dvdp_leq ?monic_neq0 -?(map_monic (ofQ _)) ?Dp //.
    rewrite defCn minPoly_dvdp //; try by rewrite -(fmorph_root (ofQ t)) Dz Dp.
    by apply/polyOver_poly=> j _; rewrite memv_img ?memvf.
  have [sRCn sCnRz]: (Rn <= Cn)%VS /\ (Cn <= Rz)%VS by rewrite !subv_adjoin.
  have sRnRz := subv_trans sRCn sCnRz.
  have{gal_z} galRz: galois Rn Rz.
    apply/and3P; split=> //; apply/splitting_normalField=> //.
    pose u : SplittingFieldType rat (Q z) gal_z := inQ z z.
    have /QtoQ[Qzt QztE] := t_z; exists (minPoly 1 u ^ Qzt).
      have /polyOver1P[q ->] := minPolyOver 1 u; apply/polyOver_poly=> j _.
      by rewrite coef_map linearZZ rmorph1 rpredZ ?rpred1.
    have [s /eqP Ds] := splitting_field_normal 1 u.
    rewrite Ds; exists (map Qzt s); first by rewrite map_rp eqpxx.
    apply/eqP; rewrite eqEsubv; apply/andP; split.
      apply/Fadjoin_seqP; split=> // _ /mapP[w s_w ->].
      by rewrite (subvP (adjoinSl u_z (sub1v _))) // -sQof2 Dz QztE.
    rewrite /= adjoinC (Fadjoin_idP _) -/Rz; last first.
      by rewrite (subvP (adjoinSl _ (sub1v _))) // -sQof2 Dz Dit.
    rewrite /= -adjoin_seq1 adjoin_seqSr //; apply/allP=> /=; rewrite andbT.
    rewrite -(mem_map (fmorph_inj (ofQ _))) -map_comp (eq_map QztE); apply/mapP.
    by exists u; rewrite ?inQ_K // -root_prod_XsubC -Ds root_minPoly.
  have galCz: galois Cn Rz by rewrite (galoisS _ galRz) ?sRCn.
  have [Cz | C'z]:= boolP (u_z \in Cn); first by exists n; rewrite -Dz -memCn.
  pose G := 'Gal(Rz / Cn)%G; have{C'z} ntG: G :!=: 1%g.
    rewrite trivg_card1 -galois_dim 1?(galoisS _ galCz) ?subvv //=.
    by rewrite -adjoin_degreeE adjoin_deg_eq1.
  pose extRz m := exists2 w, ofQ t w \in sQ (z_ m) & w \in [predD Rz & Cn].
  suffices [m le_n_m [w Cw /andP[C'w Rz_w]]]: exists2 m, (n <= m)%N & extRz m.
    pose p := minPoly <<Cn; w>> u_z; apply: (IHd (p ^ ofQ t) m).
      apply: leq_trans le_Rz_d; rewrite size_map_poly size_minPoly ltnS.
      rewrite adjoin_degreeE adjoinC (addv_idPl Rz_w) agenv_id.
      rewrite ltn_divLR ?adim_gt0 // mulnC.
      rewrite muln_divCA ?field_dimS ?subv_adjoin // ltn_Pmulr ?adim_gt0 //.
      by rewrite -adjoin_degreeE ltnNge leq_eqVlt orbF adjoin_deg_eq1.
    rewrite map_monic monic_minPoly -Dz fmorph_root root_minPoly /=.
    have /polyOverP Cw_p: p \is a polyOver <<Cn; w>>%VS by apply: minPolyOver.
    apply/polyOver_poly=> j _; have /Fadjoin_polyP[q Cq {j}->] := Cw_p j.
    rewrite -horner_map rpred_horner //; apply/polyOver_poly=> j _.
    by rewrite (sCle n) // -memCn (polyOverP Cq).
  have [evenG | oddG] := boolP (2.-group G); last first.
    have [P /and3P[sPG evenP oddPG]] := Sylow_exists 2 'Gal(Rz / Rn).
    have [w defQw] := PET_Qz t [aspace of fixedField P].
    pose pw := minPoly Rn w; pose p := (- pw * (pw \Po - 'X)) ^ ofQ t.
    have sz_pw: (size pw).-1 = #|'Gal(Rz / Rn) : P|.
      rewrite size_minPoly adjoin_degreeE -dim_fixed_galois //= -defQw.
      congr (\dim_Rn _); apply/esym/eqP; rewrite eqEsubv adjoinSl ?sub1v //=.
      by apply/FadjoinP; rewrite memv_adjoin /= defQw -galois_connection.
    have mon_p: p \is monic.
      have mon_pw: pw \is monic := monic_minPoly _ _.
      rewrite map_monic mulNr -mulrN monicMl // monicE.
      rewrite !(lead_coef_opp, lead_coef_comp) ?size_opp ?size_polyX //.
      by rewrite lead_coefX sz_pw -signr_odd odd_2'nat oddPG mulrN1 opprK.
    have Dp0: p.[0] = - ofQ t pw.[0] ^+ 2.
      rewrite -(rmorph0 (ofQ t)) horner_map hornerM rmorphM.
      by rewrite horner_comp !hornerN hornerX oppr0 rmorphN mulNr.
    have Rpw: pw \is a polyOver Rn by apply: minPolyOver.
    have Rp: p \is a polyOver (sQ (x_ n)).
      apply/polyOver_poly=> j _; rewrite -memRn; apply: polyOverP j => /=.
      by rewrite rpredM 1?polyOver_comp ?rpredN ?polyOverX.
    have Rp0: ofQ t pw.[0] \in sQ (x_ n) by rewrite -memRn rpred_horner ?rpred0.
    have [|{mon_p Rp Rp0 Dp0}m lenm p_Rm_0] := xRroot n p (ofQ t pw.[0]).
      by rewrite /has_Rroot mon_p Rp Rp0 -Dp0 /=.
    have{p_Rm_0} [y Ry pw_y]: {y | y \in sQ (x_ m) & root (pw ^ ofQ t) y}.
      apply/sig2W; have [y Ry] := p_Rm_0.
      rewrite [p]rmorphM /= map_comp_poly !rmorphN /= map_polyX.
      rewrite rootM rootN root_comp hornerN hornerX.
      by case/orP; [exists y | exists (- y)]; rewrite ?rpredN.
    have [u Rz_u Dy]: exists2 u, u \in Rz & y = ofQ t u.
      have Rz_w: w \in Rz by rewrite -sub_adjoin1v defQw capvSl.
      have [sg [Gsg _ Dpw]] := galois_factors sRnRz galRz w Rz_w.
      set s := map _ sg in Dpw.
      have /mapP[u /mapP[g Gg Du] ->]: y \in map (ofQ t) s.
        by rewrite -root_prod_XsubC -/(rp C _) -map_rp -[rp _ _]Dpw.
      by exists u; rewrite // Du memv_gal.
    have{pw_y} pw_u: root pw u by rewrite -(fmorph_root (ofQ t)) -Dy.
    exists m => //; exists u; first by rewrite -Dy; apply: sQtrans Ry _.
    rewrite inE /= Rz_u andbT; apply: contra oddG => Cu.
    suffices: 2.-group 'Gal(Rz / Rn).
      apply: pnat_dvd; rewrite -!galois_dim // ?(galoisS _ galQr) ?sRCz //.
      rewrite dvdn_divLR ?field_dimS ?adim_gt0 //.
      by rewrite mulnC muln_divCA ?field_dimS ?dvdn_mulr.
    congr (2.-group _): evenP; apply/eqP.
    rewrite eqEsubset sPG -indexg_eq1 (pnat_1 _ oddPG) // -sz_pw.
    have (pu := minPoly Rn u): (pu %= pw) || (pu %= 1).
      by rewrite minPoly_irr ?minPoly_dvdp ?minPolyOver.
    rewrite /= -size_poly_eq1 {1}size_minPoly orbF => /eqp_size <-.
    rewrite size_minPoly /= adjoin_degreeE (@pnat_dvd _ 2) // -dimCn.
    rewrite dvdn_divLR ?divnK ?adim_gt0 ?field_dimS ?subv_adjoin //.
    exact/FadjoinP.
  have [w Rz_w deg_w]: exists2 w, w \in Rz & adjoin_degree Cn w = 2.
    have [P sPG iPG]: exists2 P : {group gal_of Rz}, P \subset G & #|G : P| = 2.
      have [_ _ [k oG]] := pgroup_pdiv evenG ntG.
      have [P [sPG _ oP]] := normal_pgroup evenG (normal_refl G) (leq_pred _).
      by exists P => //; rewrite -divgS // oP oG pfactorK // -expnB ?subSnn.
    have [w defQw] := PET_Qz _ [aspace of fixedField P].
    exists w; first by rewrite -sub_adjoin1v defQw capvSl.
    rewrite adjoin_degreeE -iPG -dim_fixed_galois // -defQw; congr (\dim_Cn _).
    apply/esym/eqP; rewrite eqEsubv adjoinSl ?sub1v //=; apply/FadjoinP.
    by rewrite memv_adjoin /= defQw -galois_connection.
  have nz2: 2%:R != 0 :> Qt by move/charf0P: (charQ (Q t)) => ->.
  without loss{deg_w} [C'w Cw2]: w Rz_w / w \notin Cn /\ w ^+ 2 \in Cn.
    pose p := minPoly Cn w; pose v := p`_1 / 2%:R.
    have /polyOverP Cp: p \is a polyOver Cn := minPolyOver Cn w.
    have Cv: v \in Cn by rewrite rpred_div ?rpred_nat ?Cp.
    move/(_ (v + w)); apply; first by rewrite rpredD // subvP_adjoin.
    split; first by rewrite rpredDl // -adjoin_deg_eq1 deg_w.
    rewrite addrC -[_ ^+ 2]subr0 -(rootP (root_minPoly Cn w)) -/p.
    rewrite sqrrD [_ - _]addrAC rpredD ?rpredX // -mulr_natr -mulrA divfK //.
    rewrite [w ^+ 2 + _]addrC mulrC -rpredN opprB horner_coef.
    have /monicP := monic_minPoly Cn w; rewrite lead_coefE size_minPoly deg_w.
    by rewrite 2!big_ord_recl big_ord1 => ->; rewrite mulr1 mul1r addrK Cp.
  without loss R'w2: w Rz_w C'w Cw2 / w ^+ 2 \notin Rn.
    move=> IHw; have [Rw2 | /IHw] := boolP (w ^+ 2 \in Rn); last exact.
    have R'it: i_t \notin Rn by rewrite memRn Dit.
    pose v := 1 + i_t; have R'v: v \notin Rn by rewrite rpredDl ?rpred1.
    have Cv: v \in Cn by rewrite rpredD ?rpred1 ?memv_adjoin.
    have nz_v: v != 0 by rewrite (memPnC R'v) ?rpred0.
    apply: (IHw (v * w)); last 1 [|] || by rewrite fpredMl // subvP_adjoin.
      by rewrite exprMn rpredM // rpredX.
    rewrite exprMn fpredMr //=; last by rewrite expf_eq0 (memPnC C'w) ?rpred0.
    by rewrite sqrrD Dit2 expr1n addrC addKr -mulrnAl fpredMl ?rpred_nat.
  pose rect_w2 u v := [/\ u \in Rn, v \in Rn & u + i_t * (v * 2%:R) = w ^+ 2].
  have{Cw2} [u [v [Ru Rv Dw2]]]: {u : Qt & {v | rect_w2 u v}}.
    rewrite /rect_w2 -(Fadjoin_poly_eq Cw2); set p := Fadjoin_poly Rn i_t _.
    have /polyOverP Rp: p \is a polyOver Rn by apply: Fadjoin_polyOver.
    exists p`_0, (p`_1 / 2%:R); split; rewrite ?rpred_div ?rpred_nat //.
    rewrite divfK // (horner_coef_wide _ (size_Fadjoin_poly _ _ _)) -/p.
    by rewrite adjoin_degreeE dimCn big_ord_recl big_ord1 mulr1 mulrC.
  pose p := Poly [:: - (ofQ t v ^+ 2); 0; - ofQ t u; 0; 1].
  have [|m lenm [x Rx px0]] := xRroot n p (ofQ t v).
    rewrite /has_Rroot 2!unfold_in lead_coefE horner_coef0 -memRn Rv.
    rewrite (@PolyK _ 1) ?oner_eq0 //= !eqxx !rpred0 ?rpred1 ?rpredN //=.
    by rewrite !andbT rpredX -memRn.
  suffices [y Cy Dy2]: {y | y \in sQ (z_ m) & ofQ t w ^+ 2 == y ^+ 2}.
    exists m => //; exists w; last by rewrite inE C'w.
    by move: Dy2; rewrite eqf_sqr => /pred2P[]->; rewrite ?rpredN.
  exists (x + i * (ofQ t v / x)).
    rewrite rpredD 1?rpredM ?rpred_div //= (sQtrans (x_ m)) //.
    by rewrite (sRle n) // -memRn.
  rewrite rootE /horner (@PolyK _ 1) ?oner_eq0 //= ?addr0 ?mul0r in px0.
  rewrite add0r mul1r -mulrA -expr2 subr_eq0 in px0.
  have nz_x2: x ^+ 2 != 0.
    apply: contraNneq R'w2 => y2_0; rewrite -Dw2 mulrCA.
    suffices /eqP->: v == 0 by rewrite mul0r addr0.
    by rewrite y2_0 mulr0 eq_sym sqrf_eq0 fmorph_eq0 in px0.
  apply/eqP/esym/(mulIf nz_x2); rewrite -exprMn -rmorphX -Dw2 rmorphD rmorphM.
  rewrite Dit mulrDl -expr2 mulrA divfK; last by rewrite expf_eq0 in nz_x2.
  rewrite mulr_natr addrC sqrrD exprMn Di2 mulN1r -(eqP px0) -mulNr opprB.
  by rewrite -mulrnAl -mulrnAr -rmorphMn -!mulrDl addrAC subrK.
have inFTA n z: (n_ z <= n)%N -> z = ofQ (z_ n) (inQ (z_ n) z).
  by move/sCle=> le_zn; rewrite inQ_K ?le_zn.
pose is_cj n cj := {in R_ n, cj =1 id} /\ cj (i_ n) = - i_ n.
have /all_sig[cj_ /all_and2[cj_R cj_i]] n: {cj : 'AEnd(Q (z_ n)) | is_cj n cj}.
  have cj_P: root (minPoly (R_ n) (i_ n) ^ \1%VF) (- i_ n).
    rewrite minp_i -(fmorph_root (ofQ _)) !rmorphD !rmorph1 /= !map_polyXn.
    by rewrite rmorphN inQ_K // rootE hornerD hornerXn hornerC sqrrN Di2 addNr.
  have cj_M: ahom_in fullv (kHomExtend (R_ n) \1 (i_ n) (- i_ n)).
    by rewrite -defRi -k1HomE kHomExtendP ?sub1v ?kHom1.
  exists (AHom cj_M); split=> [y /kHomExtend_id->|]; first by rewrite ?id_lfunE.
  by rewrite (kHomExtend_val (kHom1 1 _)).
pose conj_ n z := ofQ _ (cj_ n (inQ _ z)); pose conj z := conj_ (n_ z) z.
have conjK n m z: (n_ z <= n)%N -> (n <= m)%N -> conj_ m (conj_ n z) = z.
  move/sCle=> le_z_n le_n_m; have /le_z_n/sQ_inQ[u <-] := FTA z.
  have /QtoQ[Qmn QmnE]: z_ n \in sQ (z_ m) by rewrite (sCle n).
  rewrite /conj_ ofQ_K -!QmnE !ofQ_K -!comp_lfunE; congr (ofQ _ _).
  move: u (memRi n u); apply/eqlfun_inP/FadjoinP; split=> /=.
    apply/eqlfun_inP=> y Ry; rewrite !comp_lfunE !cj_R //.
    by move: Ry; rewrite -!sQof2 QmnE !inQ_K //; apply: sRle.
  apply/eqlfunP; rewrite !comp_lfunE cj_i !linearN /=.
  suffices ->: Qmn (i_ n) = i_ m by rewrite cj_i ?opprK.
  by apply: (fmorph_inj (ofQ _)); rewrite QmnE !inQ_K.
have conjE n z: (n_ z <= n)%N -> conj z = conj_ n z.
  move/leq_trans=> le_zn; set x := conj z; set y := conj_ n z.
  have [m [le_xm le_ym le_nm]] := maxn3 (n_ x) (n_ y) n.
  by have /conjK/=/can_in_inj := leqnn m; apply; rewrite ?conjK // le_zn.
suffices conjM: rmorphism conj.
  exists (RMorphism conjM) => [z | /(_ i)/eqP/idPn[]] /=.
    by have [n [/conjE-> /(conjK (n_ z))->]] := maxn3 (n_ (conj z)) (n_ z) 0%N.
  rewrite /conj/conj_ cj_i rmorphN inQ_K // eq_sym -addr_eq0 -mulr2n -mulr_natl.
  rewrite mulf_neq0 ?(memPnC (R'i 0%N)) ?rpred0 //.
  by have /charf0P-> := ftrans (fmorph_char QtoC) (char_num _).
do 2?split=> [x y|]; last pose n1 := n_ 1.
- have [m [le_xm le_ym le_xym]] := maxn3 (n_ x) (n_ y) (n_ (x - y)).
  by rewrite !(conjE m) // (inFTA m x) // (inFTA m y) -?rmorphB /conj_ ?ofQ_K.
- have [m [le_xm le_ym le_xym]] := maxn3 (n_ x) (n_ y) (n_ (x * y)).
  by rewrite !(conjE m) // (inFTA m x) // (inFTA m y) -?rmorphM /conj_ ?ofQ_K.
by rewrite /conj -/n1 -(rmorph1 (ofQ (z_ n1))) /conj_ ofQ_K !rmorph1.
Qed.

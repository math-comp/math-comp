(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype.
From mathcomp
Require Import bigop ssralg ssrnum ssrint rat poly polydiv polyorder.
From mathcomp
Require Import perm matrix mxpoly polyXY binomial bigenough.

(***************************************************************************)
(* This is a standalone construction of Cauchy reals over an arbitrary     *)
(* discrete archimedian field R.                                           *)
(*   creals R == setoid of Cauchy sequences, it is not discrete and        *)
(*               cannot be equipped with any ssreflect algebraic structure *)
(***************************************************************************)

Import GRing.Theory Num.Theory Num.Def BigEnough.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope creal_scope with CR.

Section poly_extra.

Local Open Scope ring_scope.

Lemma monic_monic_from_neq0  (F : fieldType) (p : {poly F}) :
  (p != 0)%B -> (lead_coef p) ^-1 *: p \is monic.
Proof. by move=> ?; rewrite monicE lead_coefZ mulVf ?lead_coef_eq0. Qed.

(* GG -- lemmas with ssrnum dependencies cannot go in poly! *)
Lemma size_derivn (R : realDomainType) (p : {poly R}) n :
  size p^`(n) = (size p - n)%N.
Proof.
elim: n=> [|n ihn]; first by rewrite derivn0 subn0.
by rewrite derivnS size_deriv ihn -subnS.
Qed.

Lemma size_nderivn (R : realDomainType) (p : {poly R}) n :
  size p^`N(n) = (size p - n)%N.
Proof.
rewrite -size_derivn nderivn_def -mulr_natl.
by rewrite -polyC1 -!polyC_muln size_Cmul // pnatr_eq0 -lt0n fact_gt0.
Qed.

End poly_extra.

Local Notation eval := horner_eval.

Section ordered_extra.

Definition gtr0E := (invr_gt0, exprn_gt0, ltr0n, @ltr01).
Definition ger0E := (invr_ge0, exprn_ge0, ler0n, @ler01).

End ordered_extra.

Section polyorder_extra.

Variable F : realDomainType.

Local Open Scope ring_scope.

Definition poly_bound (p : {poly F}) (a r : F) : F
  := 1 + \sum_(i < size p)  `|p`_i| * (`|a| + `|r|) ^+ i.

Lemma poly_boundP p a r x : `|x - a| <= r ->
  `|p.[x]| <= poly_bound p a r.
Proof.
have [r_ge0|r_lt0] := lerP 0 r; last first.
  by move=> hr; have := ler_lt_trans hr r_lt0; rewrite normr_lt0.
rewrite ler_distl=> /andP[lx ux].
rewrite ler_paddl //.
elim/poly_ind: p=> [|p c ihp].
  by rewrite horner0 normr0 size_poly0 big_ord0.
rewrite hornerMXaddC size_MXaddC.
have [->|p_neq0 /=] := altP eqP.
  rewrite horner0 !mul0r !add0r size_poly0.
  have [->|c_neq0] /= := altP eqP; first by rewrite normr0 big_ord0.
  rewrite big_ord_recl big_ord0 addr0 coefC /=.
  by rewrite ler_pmulr ?normr_gt0 // ler_addl ler_maxr !normr_ge0.
rewrite big_ord_recl coefD coefMX coefC eqxx add0r.
rewrite (ler_trans (ler_norm_add _ _)) // addrC ler_add //.
  by rewrite expr0 mulr1.
rewrite normrM.
move: ihp=> /(ler_wpmul2r (normr_ge0 x)) /ler_trans-> //.
rewrite mulr_suml ler_sum // => i _.
rewrite coefD coefC coefMX /= addr0 exprSr mulrA.
rewrite ler_wpmul2l //.
  by rewrite ?mulr_ge0 ?exprn_ge0 ?ler_maxr ?addr_ge0 ?normr_ge0 // ltrW.
rewrite (ger0_norm r_ge0) ler_norml opprD.
rewrite (ler_trans _ lx) ?(ler_trans ux) // ler_add2r.
  by rewrite ler_normr lerr.
by rewrite ler_oppl ler_normr lerr orbT.
Qed.

Lemma poly_bound_gt0 p a r : 0 < poly_bound p a r.
Proof.
rewrite ltr_paddr // sumr_ge0 // => i _.
by rewrite mulr_ge0 ?exprn_ge0 ?addr_ge0 ?ler_maxr ?normr_ge0 // ltrW.
Qed.

Lemma poly_bound_ge0 p a r : 0 <= poly_bound p a r.
Proof. by rewrite ltrW // poly_bound_gt0. Qed.

Definition poly_accr_bound (p : {poly F}) (a r : F) : F
  := (maxr 1 (2%:R * r)) ^+ (size p).-1
  * (1 + \sum_(i < (size p).-1) poly_bound p^`N(i.+1) a r).

Lemma poly_accr_bound1P p a r x y :
  `|x - a| <= r ->  `|y - a| <= r ->
  `|p.[y] - p.[x]| <= `|y - x| * poly_accr_bound p a r.
Proof.
have [|r_lt0] := lerP 0 r; last first.
  by move=> hr; have := ler_lt_trans hr r_lt0; rewrite normr_lt0.
rewrite le0r=> /orP[/eqP->|r_gt0 hx hy].
  by rewrite !normr_le0 !subr_eq0=> /eqP-> /eqP->; rewrite !subrr normr0 mul0r.
rewrite mulrA mulrDr mulr1 ler_paddl ?mulr_ge0 ?normr_ge0 //=.
  by rewrite exprn_ge0 ?ler_maxr ?mulr_ge0 ?ger0E ?ltrW.
rewrite -{1}(addNKr x y) [- _ + _]addrC /= -mulrA.
rewrite nderiv_taylor; last exact: mulrC.
have [->|p_neq0] := eqVneq p 0.
  rewrite size_poly0 big_ord0 horner0 subr0 normr0 mulr_ge0 ?normr_ge0 //.
  by rewrite big_ord0 mulr0 lerr.
rewrite -[size _]prednK ?lt0n ?size_poly_eq0 //.
rewrite big_ord_recl expr0 mulr1 nderivn0 addrC addKr !mulr_sumr.
have := ler_trans (ler_norm_sum _ _ _); apply.
rewrite ler_sum // => i _.
rewrite exprSr mulrA !normrM mulrC ler_wpmul2l ?normr_ge0 //.
suff /ler_wpmul2l /ler_trans :
  `|(y - x) ^+ i| <=  maxr 1 (2%:R * r) ^+ (size p).-1.
  apply; rewrite ?normr_ge0 // mulrC ler_wpmul2l ?poly_boundP //.
  by rewrite ?exprn_ge0 // ler_maxr ler01 mulr_ge0 ?ler0n ?ltrW.
case: maxrP=> hr.
  rewrite expr1n normrX exprn_ile1 ?normr_ge0 //.
  rewrite (ler_trans (ler_dist_add a _ _)) // addrC distrC.
  by rewrite (ler_trans _ hr) // mulrDl ler_add ?mul1r.
rewrite (@ler_trans _ ((2%:R * r) ^+ i)) //.
  rewrite normrX @ler_expn2r -?topredE /= ?normr_ge0 ?mulr_ge0 ?ler0n //.
    by rewrite ltrW.
  rewrite (ler_trans (ler_dist_add a _ _)) // addrC distrC.
  by rewrite mulrDl ler_add ?mul1r.
by rewrite ler_eexpn2l // ltnW.
Qed.

Lemma poly_accr_bound_gt0 p a r : 0 < poly_accr_bound p a r.
Proof.
rewrite /poly_accr_bound pmulr_rgt0 //.
  rewrite ltr_paddr ?ltr01 //.
  by rewrite sumr_ge0 // => i; rewrite poly_bound_ge0.
by rewrite exprn_gt0 // ltr_maxr ltr01 pmulr_rgt0 ?ltr0n.
Qed.

Lemma poly_accr_bound_ge0 p a r : 0 <= poly_accr_bound p a r.
Proof. by rewrite ltrW // poly_accr_bound_gt0. Qed.

(* Todo : move to polyorder => need char 0 *)
Lemma gdcop_eq0 (p q : {poly F}) :
  (gdcop p q == 0)%B = (q == 0)%B && (p != 0)%B.
Proof.
have [[->|q_neq0] [->|p_neq0] /=] := (altP (q =P 0), altP (p =P 0)).
+ by rewrite gdcop0 eqxx oner_eq0.
+ by rewrite gdcop0 (negPf p_neq0) eqxx.
+ apply/negP=> /eqP hg; have := coprimep_gdco 0 q_neq0.
  by rewrite hg coprimep0 eqp01.
by apply/negP=> /eqP hg; have := dvdp_gdco p q; rewrite hg dvd0p; apply/negP.
Qed.

End polyorder_extra.

Section polyXY_order_extra.

Variable F : realFieldType.
Local Open Scope ring_scope.

Local Notation "p ^ f" := (map_poly f p) : ring_scope.
Local Notation "'Y" := 'X%:P.

Definition norm_poly2 (p : {poly {poly F}}) := p ^ (map_poly (fun x => `|x|)).

Lemma coef_norm_poly2 p i j : (norm_poly2 p)`_i`_j = `|p`_i`_j|.
Proof.
rewrite !coef_map_id0 ?normr0 //; last first.
by rewrite /map_poly poly_def size_poly0 big_ord0.
Qed.

Lemma size_norm_poly2 p : size (norm_poly2 p) = size p.
Proof.
rewrite /norm_poly2; have [->|p0] := eqVneq p 0.
  by rewrite /map_poly poly_def !(size_poly0, big_ord0).
rewrite /map_poly size_poly_eq // -size_poly_eq0 size_poly_eq //.
  by rewrite -lead_coefE size_poly_eq0 lead_coef_eq0.
by rewrite -!lead_coefE normr_eq0 !lead_coef_eq0.
Qed.

End polyXY_order_extra.

Section polyorder_field_extra.

Variable F : realFieldType.

Local Open Scope ring_scope.

Definition poly_accr_bound2 (p : {poly F}) (a r : F) : F
  := (maxr 1 (2%:R * r)) ^+ (size p).-2
  * (1 + \sum_(i < (size p).-2) poly_bound p^`N(i.+2) a r).

Lemma poly_accr_bound2_gt0 p a r : 0 < poly_accr_bound2 p a r.
Proof.
rewrite /poly_accr_bound pmulr_rgt0 //.
  rewrite ltr_paddr ?ltr01 //.
  by rewrite sumr_ge0 // => i; rewrite poly_bound_ge0.
by rewrite exprn_gt0 // ltr_maxr ltr01 pmulr_rgt0 ?ltr0n.
Qed.

Lemma poly_accr_bound2_ge0 p a r : 0 <= poly_accr_bound2 p a r.
Proof. by rewrite ltrW // poly_accr_bound2_gt0. Qed.

Lemma poly_accr_bound2P p (a r x y : F) : (x != y)%B ->
  `|x - a| <= r ->  `|y - a| <= r ->
  `|(p.[y] - p.[x]) / (y - x) - p^`().[x]|
    <= `|y - x| * poly_accr_bound2 p a r.
Proof.
have [|r_lt0] := lerP 0 r; last first.
  by move=> _ hr; have := ler_lt_trans hr r_lt0; rewrite normr_lt0.
rewrite le0r=> /orP[/eqP->|r_gt0].
  rewrite !normr_le0 !subr_eq0.
  by move=> nxy /eqP xa /eqP xb; rewrite xa xb eqxx in nxy.
move=> neq_xy hx hy.
rewrite mulrA mulrDr mulr1 ler_paddl ?mulr_ge0 ?normr_ge0 //=.
  by rewrite exprn_ge0 ?ler_maxr ?mulr_ge0 ?ger0E ?ltrW.
rewrite -{1}(addNKr x y) [- _ + _]addrC /= -mulrA.
rewrite nderiv_taylor; last exact: mulrC.
have [->|p_neq0] := eqVneq p 0.
  by rewrite derivC !horner0 size_poly0 !(big_ord0, subrr, mul0r) normr0 !mulr0.
rewrite -[size _]prednK ?lt0n ?size_poly_eq0 //.
rewrite big_ord_recl expr0 mulr1 nderivn0 /= -size_deriv.
have [->|p'_neq0] := eqVneq p^`() 0.
  by rewrite horner0 size_poly0 !big_ord0 addr0 !(subrr, mul0r) normr0 !mulr0.
rewrite -[size _]prednK ?lt0n ?size_poly_eq0 // big_ord_recl expr1.
rewrite addrAC subrr add0r mulrDl mulfK; last by rewrite subr_eq0 eq_sym.
rewrite nderivn1 addrAC subrr add0r mulr_sumr normrM normfV.
rewrite ler_pdivr_mulr ?normr_gt0; last by rewrite subr_eq0 eq_sym.
rewrite mulrAC -expr2 mulrC mulr_suml.
have := ler_trans (ler_norm_sum _ _ _); apply.
rewrite ler_sum // => i _ /=; rewrite /bump /= !add1n.
rewrite normrM normrX 3!exprSr expr1 !mulrA !ler_wpmul2r ?normr_ge0 //.
suff /ler_wpmul2l /ler_trans :
  `|(y - x)| ^+ i <=  maxr 1 (2%:R * r) ^+ (size p^`()).-1.
  apply; rewrite ?normr_ge0 // mulrC ler_wpmul2l ?poly_boundP //.
  by rewrite ?exprn_ge0 // ler_maxr ler01 mulr_ge0 ?ler0n ?ltrW.
case: maxrP=> hr.
  rewrite expr1n exprn_ile1 ?normr_ge0 //.
  rewrite (ler_trans (ler_dist_add a _ _)) // addrC distrC.
  by rewrite (ler_trans _ hr) // mulrDl ler_add ?mul1r.
rewrite (@ler_trans _ ((2%:R * r) ^+ i)) //.
  rewrite @ler_expn2r -?topredE /= ?normr_ge0 ?mulr_ge0 ?ler0n //.
    by rewrite ltrW.
  rewrite (ler_trans (ler_dist_add a _ _)) // addrC distrC.
  by rewrite mulrDl ler_add ?mul1r.
by rewrite ler_eexpn2l // ltnW.
Qed.

End polyorder_field_extra.

Section monotony.

Variable F : realFieldType.

Local Open Scope ring_scope.

Definition accr_pos p (a r : F) :=
  ({ k | 0 < k & forall x y, (x != y)%B ->
    `|x - a| <= r -> `|y - a| <= r -> (p.[x] - p.[y]) / (x - y) > k }
      * forall x, `|x - a| <= r -> p^`().[x] > 0)%type.

Definition accr_neg p (a r : F) :=
  ({ k | 0 < k & forall x y, (x != y)%B ->
    `|x - a| <= r -> `|y - a| <= r -> (p.[x] - p.[y]) / (x - y) < - k}
      * forall x, `|x - a| <= r -> p^`().[x] < 0)%type.

Definition strong_mono p (a r : F) := (accr_pos p a r + accr_neg p a r)%type.

Lemma accr_pos_incr p a r : accr_pos p a r ->
  forall x y, `|x - a| <= r -> `|y - a| <= r -> (p.[x] <= p.[y]) = (x <= y).
Proof.
move=> [[k k_gt0 hk] _] x y hx hy.
have [->|neq_xy] := eqVneq x y; first by rewrite !lerr.
have hkxy := hk _ _ neq_xy hx hy.
have := ltr_trans k_gt0 hkxy.
have [lpxpy|lpypx|->] := ltrgtP p.[x] p.[y].
+ by rewrite nmulr_rgt0 ?subr_lt0 // ?invr_lt0 subr_lt0=> /ltrW->.
+ by rewrite pmulr_rgt0 ?subr_gt0 // ?invr_gt0 subr_gt0 lerNgt=> ->.
by rewrite subrr mul0r ltrr.
Qed.

Lemma accr_neg_decr p a r : accr_neg p a r ->
  forall x y, `|x - a| <= r -> `|y - a| <= r -> (p.[x] <= p.[y]) = (y <= x).
Proof.
move=> [] [k]; rewrite -oppr_lt0=> Nk_lt0 hk _ x y hx hy.
have [->|neq_xy] := eqVneq x y; first by rewrite !lerr.
have hkxy := hk _ _ neq_xy hx hy.
have := ltr_trans hkxy  Nk_lt0.
have [lpxpy|lpypx|->] := ltrgtP p.[x] p.[y].
+ by rewrite nmulr_rlt0 ?subr_lt0 // ?invr_gt0 subr_gt0=> /ltrW->.
+ by rewrite pmulr_rlt0 ?subr_gt0 // ?invr_lt0 subr_lt0 lerNgt=> ->.
by rewrite subrr mul0r ltrr.
Qed.

Lemma accr_negN p a r : accr_pos p a r -> accr_neg (- p) a r.
Proof.
case=> [[k k_gt0 hk] h].
split; [ exists k=> // x y nxy hx hy;
    by rewrite !hornerN -opprD mulNr ltr_opp2; apply: hk
  | by move=> x hx; rewrite derivN hornerN oppr_lt0; apply: h ].
Qed.

Lemma accr_posN p a r : accr_neg p a r -> accr_pos (- p) a r.
Proof.
case=> [[k k_gt0 hk] h].
split; [ exists k=> // x y nxy hx hy;
    by rewrite !hornerN -opprD mulNr ltr_oppr; apply: hk
  | by move=> x hx; rewrite derivN hornerN oppr_gt0; apply: h ].
Qed.

Lemma strong_monoN p a r : strong_mono p a r -> strong_mono (- p) a r.
Proof. by case=> [] hp; [right; apply: accr_negN|left; apply: accr_posN]. Qed.

Lemma strong_mono_bound p a r : strong_mono p a r
  -> {k | 0 < k & forall x y, `|x - a| <= r -> `|y - a| <= r ->
    `| x - y | <= k * `| p.[x] - p.[y] | }.
Proof.
case=> [] [[k k_gt0 hk] _]; exists k^-1; rewrite ?invr_gt0=> // x y hx hy;
have [->|neq_xy] := eqVneq x y; do ?[by rewrite !subrr normr0 mulr0];
move: (hk _ _ neq_xy hx hy); rewrite 1?ltr_oppr ler_pdivl_mull //;
rewrite -ler_pdivl_mulr ?normr_gt0 ?subr_eq0 // => /ltrW /ler_trans-> //;
by rewrite -normfV -normrM ler_normr lerr ?orbT.
Qed.

Definition merge_intervals (ar1 ar2 : F * F) :=
  let l := minr (ar1.1 - ar1.2) (ar2.1 - ar2.2) in
  let u := maxr (ar1.1 + ar1.2) (ar2.1 + ar2.2) in
    ((l + u) / 2%:R, (u - l) / 2%:R).
Local Notation center ar1 ar2 := ((merge_intervals ar1 ar2).1).
Local Notation radius ar1 ar2 := ((merge_intervals ar1 ar2).2).

Lemma split_interval (a1 a2 r1 r2 x : F) :
  0 < r1 -> 0 < r2 ->  `|a1 - a2| <= r1 + r2 ->
  (`|x - center (a1, r1) (a2, r2)| <= radius (a1, r1) (a2, r2))
  =  (`|x - a1| <= r1) || (`|x - a2| <= r2).
Proof.
move=> r1_gt0 r2_gt0 le_ar.
rewrite /merge_intervals /=.
set l := minr _ _; set u := maxr _ _.
rewrite ler_pdivl_mulr ?gtr0E // -{2}[2%:R]ger0_norm ?ger0E //.
rewrite -normrM mulrBl mulfVK ?pnatr_eq0 // ler_distl.
rewrite opprB addrCA addrK (addrC (l + u)) addrA addrNK.
rewrite -!mulr2n !mulr_natr !ler_muln2r !orFb.
rewrite ler_minl ler_maxr !ler_distl.
have [] := lerP=> /= a1N; have [] := lerP=> //= a1P;
have [] := lerP=> //= a2P; rewrite ?(andbF, andbT) //; symmetry.
  rewrite ltrW // (ler_lt_trans _ a1P) //.
  rewrite (monoLR (addrK _) (ler_add2r _)) -addrA.
  rewrite (monoRL (addNKr _) (ler_add2l _)) addrC.
  by rewrite (ler_trans _ le_ar) // ler_normr opprB lerr orbT.
rewrite ltrW // (ltr_le_trans a1N) //.
rewrite (monoLR (addrK _) (ler_add2r _)) -addrA.
rewrite (monoRL (addNKr _) (ler_add2l _)) addrC ?[r2 + _]addrC.
by rewrite (ler_trans _ le_ar) // ler_normr lerr.
Qed.

Lemma merge_mono p a1 a2 r1 r2 :
  0 < r1 -> 0 < r2 ->
  `|a1 - a2| <= (r1 + r2) ->
  strong_mono p a1 r1 -> strong_mono p a2 r2 ->
  strong_mono p (center (a1, r1) (a2, r2)) (radius (a1, r1) (a2, r2)).
Proof.
move=> r1_gt0 r2_gt0 har sm1; wlog : p sm1 / accr_pos p a1 r1.
  move=> hwlog; case: (sm1); first exact: hwlog.
  move=> accr_p smp; rewrite -[p]opprK; apply: strong_monoN.
  apply: hwlog=> //; do ?exact: strong_monoN.
  exact: accr_posN.
case=> [[k1 k1_gt0 hk1]] h1.
move=> [] accr2_p; last first.
  set m := (r2 * a1 + r1 * a2) / (r1 + r2).
  have pm_gt0 := h1 m.
  case: accr2_p=> [_] /(_ m) pm_lt0.
  suff: 0 < 0 :> F by rewrite ltrr.
  have r_gt0 : 0 < r1 + r2 by rewrite ?addr_gt0.
  apply: (ltr_trans (pm_gt0 _) (pm_lt0 _)).
    rewrite -(@ler_pmul2l _ (r1 + r2)) //.
    rewrite -{1}[r1 + r2]ger0_norm ?(ltrW r_gt0) //.
    rewrite -normrM mulrBr /m mulrC mulrVK ?unitfE ?gtr_eqF //.
    rewrite mulrDl opprD addrA addrC addrA addKr.
    rewrite distrC -mulrBr normrM ger0_norm ?(ltrW r1_gt0) //.
    by rewrite mulrC ler_wpmul2r // ltrW.
  rewrite -(@ler_pmul2l _ (r1 + r2)) //.
  rewrite -{1}[r1 + r2]ger0_norm ?(ltrW r_gt0) //.
  rewrite -normrM mulrBr /m mulrC mulrVK ?unitfE ?gtr_eqF //.
  rewrite mulrDl opprD addrA addrK.
  rewrite -mulrBr normrM ger0_norm ?(ltrW r2_gt0) //.
  by rewrite mulrC ler_wpmul2r // ltrW.
case: accr2_p=> [[k2 k2_gt0 hk2]] h2.
left; split; last by move=> x; rewrite split_interval // => /orP [/h1|/h2].
exists (minr k1 k2); first by rewrite ltr_minr k1_gt0.
move=> x y neq_xy; rewrite !split_interval //.
wlog lt_xy: x y neq_xy / y < x.
  move=> hwlog; have [] := ltrP y x; first exact: hwlog.
  rewrite ler_eqVlt (negPf neq_xy) /= => /hwlog hwlog' hx hy.
  rewrite -mulrNN -!invrN !opprB.
  by apply: hwlog'; rewrite // eq_sym.
move=> {h1} {h2} {sm1}.
wlog le_xr1 : a1 a2 r1 r2 k1 k2
  r1_gt0 r2_gt0 k1_gt0 k2_gt0 har hk1 hk2  / `|x - a1| <= r1.
  move=> hwlog h; move: (h)=> /orP [/hwlog|]; first exact.
  move=> /(hwlog a2 a1 r2 r1 k2 k1) hwlog' ley; rewrite minrC.
  by apply: hwlog'; rewrite 1?orbC // distrC [r2 + _]addrC.
move=> _.
have [le_yr1|gt_yr1] := (lerP _ r1)=> /= [_|le_yr2].
  by rewrite ltr_minl hk1.
rewrite ltr_pdivl_mulr ?subr_gt0 //.
pose z := a1 - r1.
have hz1 : `|z - a1| <= r1 by rewrite addrC addKr normrN gtr0_norm.
have gt_yr1' : y + r1 < a1.
  rewrite addrC; move: gt_yr1.
  rewrite (monoLR (addrNK _) (ltr_add2r _)).
 rewrite /z ltr_normr opprB=> /orP[|-> //].
  rewrite (monoRL (addrK a1) (ltr_add2r _))=> /ltr_trans /(_ lt_xy).
  by rewrite ltrNge addrC; move: le_xr1; rewrite ler_distl=> /andP [_ ->].
have lt_yz : y < z by rewrite (monoRL (addrK _) (ltr_add2r _)).
have hz2 : `|z - a2| <= r2.
  move: (har); rewrite ler_norml=> /andP [la ua].
  rewrite addrAC ler_distl ua andbT.
  rewrite -[a1](addrNK y) -[_ - _ + _ - _]addrA.
  rewrite ler_add //.
    by rewrite (monoRL (addrK _) (ler_add2r _)) addrC ltrW.
  by move: le_yr2; rewrite ler_norml=> /andP[].
have [<-|neq_zx] := eqVneq z x.
  by rewrite -ltr_pdivl_mulr ?subr_gt0 // ltr_minl hk2 ?orbT // gtr_eqF.
have lt_zx : z < x.
  rewrite ltr_neqAle neq_zx /=.
  move: le_xr1; rewrite distrC ler_norml=> /andP[_].
  by rewrite !(monoLR (addrK _) (ler_add2r _)) addrC.
rewrite -{1}[x](addrNK z) -{1}[p.[x]](addrNK p.[z]).
rewrite !addrA -![_ - _ + _ - _]addrA mulrDr ltr_add //.
  rewrite -ltr_pdivl_mulr ?subr_gt0 //.
  by rewrite ltr_minl hk1 ?gtr_eqF.
rewrite -ltr_pdivl_mulr ?subr_gt0 //.
by rewrite ltr_minl hk2 ?orbT ?gtr_eqF.
Qed.

End monotony.

Section CauchyReals.

Local Open Scope nat_scope.
Local Open Scope creal_scope.
Local Open Scope ring_scope.

Definition asympt1 (R : numDomainType) (P : R -> nat -> Prop)
  := {m : R -> nat | forall eps i, 0 < eps -> (m eps <= i)%N -> P eps i}.

Definition asympt2 (R : numDomainType)  (P : R -> nat -> nat -> Prop)
  := {m : R -> nat | forall eps i j, 0 < eps -> (m eps <= i)%N -> (m eps <= j)%N -> P eps i j}.

Notation "{ 'asympt' e : i / P }" := (asympt1 (fun e i => P))
  (at level 0, e ident, i ident, format "{ 'asympt'  e  :  i  /  P }") : type_scope.

Notation "{ 'asympt' e : i j / P }" := (asympt2 (fun e i j => P))
  (at level 0, e ident, i ident, j ident, format "{ 'asympt'  e  :  i  j  /  P }") : type_scope.

Lemma asympt1modP (R : numDomainType) P (a : asympt1 P) e i :
  0 < e :> R -> (projT1 a e <= i)%N -> P e i.
Proof. by case: a e i. Qed.

Lemma asympt2modP (R : numDomainType) P (a : asympt2 P) e i j :
  0 < e :> R -> (projT1 a e <= i)%N -> (projT1 a e <= j)%N -> P e i j.
Proof. by case: a e i j. Qed.

Variable F : realFieldType.

(* Lemma asympt_mulLR (k : F) (hk : 0 < k) (P : F -> nat -> Prop) : *)
(*   {asympt e : i / P e i} -> {asympt e : i / P (e * k) i}. *)
(* Proof. *)
(* case=> m hm; exists (fun e => m (e * k))=> e i he hi. *)
(* by apply: hm=> //; rewrite -ltr_pdivr_mulr // mul0r. *)
(* Qed. *)

(* Lemma asympt_mulRL (k : F) (hk : 0 < k) (P : F -> nat -> Prop) : *)
(*   {asympt e : i / P (e * k) i} -> {asympt e : i / P e i}. *)
(* Proof. *)
(* case=> m hm; exists (fun e => m (e / k))=> e i he hi. *)
(* rewrite -[e](@mulfVK _ k) ?gtr_eqF //. *)
(* by apply: hm=> //; rewrite -ltr_pdivr_mulr ?invr_gt0 // mul0r. *)
(* Qed. *)

Lemma asymptP (P1 : F -> nat -> Prop) (P2 : F -> nat -> Prop) :
  (forall e i, 0 < e -> P1 e i -> P2 e i) ->
  {asympt e : i / P1 e i} -> {asympt e : i / P2 e i}.
Proof.
by move=> hP; case=> m hm; exists m=> e i he me; apply: hP=> //; apply: hm.
Qed.

(* Lemma asympt2_mulLR (k : F) (hk : 0 < k) (P : F -> nat -> nat -> Prop) : *)
(*   {asympt e : i j / P e i j} -> {asympt e : i j / P (e * k) i j}. *)
(* Proof. *)
(* case=> m hm; exists (fun e => m (e * k))=> e i j he hi hj. *)
(* by apply: hm=> //; rewrite -ltr_pdivr_mulr // mul0r. *)
(* Qed. *)

(* Lemma asympt2_mulRL (k : F) (hk : 0 < k) (P : F -> nat -> nat -> Prop) : *)
(*   {asympt e : i j / P (e * k) i j} -> {asympt e : i j / P e i j}. *)
(* Proof. *)
(* case=> m hm; exists (fun e => m (e / k))=> e i j he hi hj. *)
(* rewrite -[e](@mulfVK _ k) ?gtr_eqF //. *)
(* by apply: hm=> //; rewrite -ltr_pdivr_mulr ?invr_gt0 // mul0r. *)
(* Qed. *)

(* Lemma asympt2P (P1 : F -> nat -> nat -> Prop) (P2 : F -> nat -> nat -> Prop) : *)
(*   (forall e i j, 0 < e -> P1 e i j -> P2 e i j) -> *)
(*   {asympt e : i j / P1 e i j} -> {asympt e : i j / P2 e i j}. *)
(* Proof. *)
(* move=> hP; case=> m hm; exists m=> e i j he mei mej. *)
(* by apply: hP=> //; apply: hm. *)
(* Qed. *)

Lemma splitf (n : nat) (e : F) : e = iterop n +%R (e / n%:R) e.
Proof.
case: n=> // n; set e' := (e / _).
have -> : e = e' * n.+1%:R by rewrite mulfVK ?pnatr_eq0.
move: e'=> {e} e; rewrite iteropS.
by elim: n=> /= [|n <-]; rewrite !mulr_natr ?mulr1n.
Qed.

Lemma splitD (x y e : F) : x < e / 2%:R -> y < e / 2%:R -> x + y < e.
Proof. by move=> hx hy; rewrite [e](splitf 2) ltr_add. Qed.

Lemma divrn_gt0 (e : F) (n : nat) : 0 < e -> (0 < n)%N -> 0 < e / n%:R.
Proof. by move=> e_gt0 n_gt0; rewrite pmulr_rgt0 ?gtr0E. Qed.

Lemma split_norm_add (x y e : F) :
  `|x| < e / 2%:R -> `|y| < e / 2%:R -> `|x + y| < e.
Proof. by move=> hx hy; rewrite (ler_lt_trans (ler_norm_add _ _)) // splitD. Qed.

Lemma split_norm_sub (x y e : F) :
  `|x| < e / 2%:R -> `|y| < e / 2%:R -> `|x - y| < e.
Proof. by move=> hx hy; rewrite (ler_lt_trans (ler_norm_sub _ _)) // splitD. Qed.

Lemma split_dist_add (z x y e : F) :
  `|x - z| < e / 2%:R -> `|z - y| < e / 2%:R -> `|x - y| < e.
Proof.
by move=> *; rewrite (ler_lt_trans (ler_dist_add z _ _)) ?splitD // 1?distrC.
Qed.

Definition creal_axiom (x : nat -> F) :=  {asympt e : i j / `|x i - x j| < e}.

CoInductive creal := CReal {cauchyseq :> nat -> F; _ : creal_axiom cauchyseq}.
Bind Scope creal_scope with creal.

Lemma crealP (x : creal) : {asympt e : i j / `|x i - x j| < e}.
Proof. by case: x. Qed.

Definition cauchymod :=
  nosimpl (fun (x : creal) => let: CReal _ m := x in projT1 m).

Lemma cauchymodP (x : creal) eps i j : 0 < eps ->
  (cauchymod x eps <= i)%N -> (cauchymod x eps <= j)%N -> `|x i - x j| < eps.
Proof. by case: x=> [x [m mP] //] /mP; apply. Qed.

Definition neq_creal (x y : creal) : Prop :=
  exists eps, (0 < eps) &&
    (eps * 3%:R <= `|x (cauchymod x eps) - y (cauchymod y eps)|).
Notation "!=%CR" := neq_creal : creal_scope.
Notation "x != y" := (neq_creal x  y) : creal_scope.

Definition eq_creal x y := (~ (x != y)%CR).
Notation "x == y" := (eq_creal x y) : creal_scope.

Lemma ltr_distl_creal (e : F) (i : nat) (x : creal) (j : nat) (a b : F) :
  0 < e -> (cauchymod x e <= i)%N -> (cauchymod x e <= j)%N ->
  `| x i - a | <= b - e -> `| x j - a | < b.
Proof.
move=> e_gt0 hi hj hb.
rewrite (ler_lt_trans (ler_dist_add (x i) _ _)) ?ltr_le_add //.
by rewrite -[b](addrNK e) addrC ler_lt_add ?cauchymodP.
Qed.

Lemma ltr_distr_creal (e : F) (i : nat) (x : creal) (j : nat) (a b : F) :
  0 < e -> (cauchymod x e <= i)%N -> (cauchymod x e <= j)%N ->
  a + e <= `| x i - b | -> a < `| x j - b |.
Proof.
move=> e_gt0 hi hj hb; apply: contraLR hb; rewrite -ltrNge -lerNgt.
by move=> ha; rewrite (@ltr_distl_creal e j) // addrK.
Qed.

(* Lemma asympt_neq (x y : creal) : x != y -> *)
(*   {e | 0 < e & forall i, (cauchymod x e <= i)%N -> *)
(*                          (cauchymod y e <= i)%N -> `|x i - y i| >= e}. *)
(* Proof. *)
(* case/sigW=> e /andP[e_gt0 hxy]. *)
(* exists e=> // i hi hj; move: hxy; rewrite !lerNgt; apply: contra=> hxy. *)
(* rewrite !mulrDr !mulr1 distrC (@ltr_distl_creal i) //. *)
(* by rewrite distrC ltrW // (@ltr_distl_creal i) // ltrW. *)
(* Qed. *)

Definition lbound (x y : creal) (neq_xy : x != y) : F :=
  projT1 (sigW neq_xy).

Lemma lboundP (x y : creal) (neq_xy : x != y) i :
  (cauchymod x (lbound neq_xy) <= i)%N ->
  (cauchymod y (lbound neq_xy) <= i)%N -> lbound neq_xy <= `|x i - y i|.
Proof.
rewrite /lbound; case: (sigW _)=> /= d /andP[d_gt0 hd] hi hj.
apply: contraLR hd; rewrite -!ltrNge=> hd.
rewrite (@ltr_distl_creal d i) // distrC ltrW // (@ltr_distl_creal d i) //.
by rewrite distrC ltrW // !mulrDr mulr1 !addrA !addrK.
Qed.

Notation lbound_of p := (@lboundP _ _ p _ _ _).

Lemma lbound_gt0 (x y : creal) (neq_xy : x != y) : lbound neq_xy > 0.
Proof. by rewrite /lbound; case: (sigW _)=> /= d /andP[]. Qed.

Definition lbound_ge0 x y neq_xy := (ltrW (@lbound_gt0 x y neq_xy)).

Lemma cst_crealP (x : F) : creal_axiom (fun _ => x).
Proof. by exists (fun _ => 0%N)=> *; rewrite subrr normr0. Qed.
Definition cst_creal (x : F) := CReal (cst_crealP x).
Notation "x %:CR" := (cst_creal x)
  (at level 2, left associativity, format "x %:CR") : creal_scope.
Notation "0" := (0 %:CR) : creal_scope.

Lemma lbound0P (x : creal) (x_neq0 : x != 0) i :
  (cauchymod x (lbound x_neq0) <= i)%N ->
  (cauchymod 0%CR (lbound x_neq0) <= i)%N -> lbound x_neq0 <= `|x i|.
Proof. by move=> cx c0; rewrite -[X in `|X|]subr0 -[0]/(0%CR i) lboundP. Qed.

Notation lbound0_of p := (@lbound0P _ p _ _ _).

Lemma neq_crealP e i j (e_gt0 : 0 < e) (x y : creal) :
  (cauchymod x (e / 5%:R) <= i)%N -> (cauchymod y (e / 5%:R) <= j)%N ->
  e <= `|x i - y j| ->  x != y.
Proof.
move=> hi hj he; exists (e / 5%:R); rewrite pmulr_rgt0 ?gtr0E //=.
rewrite distrC ltrW // (@ltr_distr_creal (e / 5%:R) j) ?pmulr_rgt0 ?gtr0E //.
rewrite distrC ltrW // (@ltr_distr_creal (e / 5%:R) i) ?pmulr_rgt0 ?gtr0E //.
by rewrite mulr_natr -!mulrSr -mulrnAr -mulr_natr mulVf ?pnatr_eq0 ?mulr1.
Qed.

Lemma eq_crealP (x y : creal) : {asympt e : i / `|x i - y i| < e} ->
  (x == y)%CR.
Proof.
case=> m hm neq_xy; pose d := lbound neq_xy.
pose_big_enough i.
  have := (hm d i); rewrite lbound_gt0; big_enough => /(_ isT isT).
  by apply/negP; rewrite -lerNgt lboundP.
by close.
Qed.

Lemma eq0_crealP (x : creal) : {asympt e : i / `|x i| < e} -> x == 0.
Proof.
by move=> hx; apply: eq_crealP; apply: asymptP hx=> e i; rewrite subr0.
Qed.

Lemma asympt_eq (x y : creal) (eq_xy : x == y) :
  {asympt e : i / `|x i - y i| < e}.
Proof.
exists_big_modulus m F.
   move=> e i e0 hi; rewrite ltrNge; apply/negP=> he; apply: eq_xy.
   by apply: (@neq_crealP e i i).
by close.
Qed.

Lemma asympt_eq0 (x : creal) : x == 0 -> {asympt e : i / `|x i| < e}.
Proof. by move/asympt_eq; apply: asymptP=> e i; rewrite subr0. Qed.

Definition eq_mod (x y : creal) (eq_xy : x == y) := projT1 (asympt_eq eq_xy).
Lemma eq_modP (x y : creal) (eq_xy : x == y) eps i : 0 < eps ->
                (eq_mod eq_xy eps <= i)%N -> `|x i - y i| < eps.
Proof.
by move=> eps_gt0; rewrite /eq_mod; case: (asympt_eq _)=> /= m hm /hm; apply.
Qed.
Lemma eq0_modP (x : creal) (x_eq0 : x == 0) eps i : 0 < eps ->
                (eq_mod x_eq0 eps <= i)%N -> `|x i| < eps.
Proof.
by move=> eps_gt0 hi; rewrite -[X in `|X|]subr0 -[0]/(0%CR i) eq_modP.
Qed.

Lemma eq_creal_refl x : x == x.
Proof.
apply: eq_crealP; exists (fun _ => 0%N).
by move=> e i e_gt0 _; rewrite subrr normr0.
Qed.
Hint Resolve eq_creal_refl.

Lemma neq_creal_sym x y : x != y -> y != x.
Proof.
move=> neq_xy; pose_big_enough i.
  apply: (@neq_crealP (lbound neq_xy) i i);
  by rewrite ?lbound_gt0 1?distrC ?(lbound_of neq_xy).
by close.
Qed.

Lemma eq_creal_sym x y : x == y -> y == x.
Proof. by move=> eq_xy /neq_creal_sym. Qed.

Lemma eq_creal_trans x y z : x == y -> y == z -> x == z.
Proof.
move=> eq_xy eq_yz; apply: eq_crealP; exists_big_modulus m F.
  by move=> e i *; rewrite (@split_dist_add (y i)) ?eq_modP ?divrn_gt0.
by close.
Qed.

Lemma creal_neq_always (x y : creal) i (neq_xy : x != y) :
  (cauchymod x (lbound neq_xy) <= i)%N ->
  (cauchymod y (lbound neq_xy) <= i)%N -> (x i != y i)%B.
Proof.
move=> hx hy; rewrite -subr_eq0 -normr_gt0.
by rewrite (ltr_le_trans _ (lbound_of neq_xy)) ?lbound_gt0.
Qed.

Definition creal_neq0_always (x : creal) := @creal_neq_always x 0.

Definition lt_creal (x y : creal) : Prop :=
  exists eps, (0 < eps) &&
    (x (cauchymod x eps) + eps * 3%:R <= y (cauchymod y eps)).
Notation "<%CR" := lt_creal : creal_scope.
Notation "x < y" := (lt_creal x y) : creal_scope.

Definition le_creal (x y : creal) : Prop := ~ (y < x)%CR.
Notation "<=%CR" := le_creal : creal_scope.
Notation "x <= y" := (le_creal x y) : creal_scope.

Lemma ltr_creal (e : F) (i : nat) (x : creal) (j : nat) (a : F) :
  0 < e -> (cauchymod x e <= i)%N -> (cauchymod x e <= j)%N ->
  x i <= a - e -> x j < a.
Proof.
move=> e_gt0 hi hj ha; have := cauchymodP e_gt0 hj hi.
rewrite ltr_distl=> /andP[_ /ltr_le_trans-> //].
by rewrite -(ler_add2r (- e)) addrK.
Qed.

Lemma gtr_creal (e : F) (i : nat) (x : creal) (j : nat) (a : F) :
  0 < e -> (cauchymod x e <= i)%N -> (cauchymod x e <= j)%N ->
  a + e <= x i-> a < x j.
Proof.
move=> e_gt0 hi hj ha; have := cauchymodP e_gt0 hj hi.
rewrite ltr_distl=> /andP[/(ler_lt_trans _)-> //].
by rewrite -(ler_add2r e) addrNK.
Qed.

Definition diff (x y : creal) (lt_xy : (x < y)%CR) : F := projT1 (sigW lt_xy).

Lemma diff_gt0 (x y : creal) (lt_xy : (x < y)%CR) : diff lt_xy > 0.
Proof. by rewrite /diff; case: (sigW _)=> /= d /andP[]. Qed.

Definition diff_ge0 x y lt_xy := (ltrW (@diff_gt0 x y lt_xy)).

Lemma diffP (x y : creal) (lt_xy : (x < y)%CR) i :
  (cauchymod x (diff lt_xy) <= i)%N ->
  (cauchymod y (diff lt_xy) <= i)%N -> x i + diff lt_xy <= y i.
Proof.
rewrite /diff; case: (sigW _)=> /= e /andP[e_gt0 he] hi hj.
rewrite ltrW // (@gtr_creal e (cauchymod y e)) // (ler_trans _ he) //.
rewrite !mulrDr mulr1 !addrA !ler_add2r ltrW //.
by rewrite (@ltr_creal e (cauchymod x e)) // addrK.
Qed.

Notation diff_of p := (@diffP _ _ p _ _ _).

Lemma diff0P (x : creal) (x_gt0 : (0 < x)%CR) i :
  (cauchymod x (diff x_gt0) <= i)%N ->
  (cauchymod 0%CR (diff x_gt0) <= i)%N -> diff x_gt0 <= x i.
Proof. by move=> cx c0; rewrite -[diff _]add0r -[0]/(0%CR i) diffP. Qed.

Notation diff0_of p := (@diff0P _ p _ _ _).

Lemma lt_crealP e i j (e_gt0 : 0 < e) (x y : creal) :
  (cauchymod x (e / 5%:R) <= i)%N -> (cauchymod y (e / 5%:R) <= j)%N ->
  x i + e <= y j ->  (x < y)%CR.
Proof.
move=> hi hj he; exists (e / 5%:R); rewrite pmulr_rgt0 ?gtr0E //=.
rewrite ltrW // (@gtr_creal (e / 5%:R) j) ?pmulr_rgt0 ?gtr0E //.
rewrite (ler_trans _ he) // -addrA (monoLR (addrNK _) (ler_add2r _)).
rewrite ltrW // (@ltr_creal (e / 5%:R) i) ?pmulr_rgt0 ?gtr0E //.
rewrite -!addrA ler_addl !addrA -mulrA -{1}[e]mulr1 -!(mulrBr, mulrDr).
rewrite pmulr_rge0 // {1}[1](splitf 5) /= !mul1r !mulrDr mulr1.
by rewrite !opprD !addrA !addrK addrN.
Qed.

Lemma le_crealP i (x y : creal) :
  (forall j, (i <= j)%N -> x j <= y j) -> (x <= y)%CR.
Proof.
move=> hi lt_yx; pose_big_enough j.
  have := hi j; big_enough => /(_ isT); apply/negP; rewrite -ltrNge.
  by rewrite (ltr_le_trans _ (diff_of lt_yx)) ?ltr_spaddr ?diff_gt0.
by close.
Qed.

Lemma le_creal_refl (x : creal) : (x <= x)%CR.
Proof. by apply: (@le_crealP 0%N). Qed.
Hint Resolve le_creal_refl.

Lemma lt_neq_creal (x y : creal) : (x < y)%CR -> x != y.
Proof.
move=> ltxy; pose_big_enough i.
  apply: (@neq_crealP (diff ltxy) i i) => //; first by rewrite diff_gt0.
  by rewrite distrC lerNgt ltr_distl negb_and -!lerNgt diffP ?orbT.
by close.
Qed.

Lemma creal_lt_always (x y : creal) i (lt_xy : (x < y)%CR) :
  (cauchymod x (diff lt_xy) <= i)%N ->
  (cauchymod y (diff lt_xy) <= i)%N -> x i < y i.
Proof.
by move=> hx hy; rewrite (ltr_le_trans _ (diff_of lt_xy)) ?ltr_addl ?diff_gt0.
Qed.

Definition creal_gt0_always := @creal_lt_always 0.

Lemma eq_le_creal (x y : creal) : x == y -> (x <= y)%CR.
Proof. by move=> /eq_creal_sym ? /lt_neq_creal. Qed.

Lemma asympt_le (x y : creal) (le_xy : (x <= y)%CR) :
  {asympt e : i / x i < y i + e}.
Proof.
exists_big_modulus m F.
  move=> e i e0 hm; rewrite ltrNge; apply/negP=> he; apply: le_xy.
  by apply: (@lt_crealP e i i).
by close.
Qed.

Lemma asympt_ge0 (x : creal) : (0 <= x)%CR -> {asympt e : i / - e < x i}.
Proof. by move/asympt_le; apply: asymptP=> *; rewrite -subr_gt0 opprK. Qed.

Definition le_mod (x y : creal) (le_xy : (x <= y)%CR) := projT1 (asympt_le le_xy).

Lemma le_modP (x y : creal) (le_xy : (x <= y)%CR) eps i : 0 < eps ->
                (le_mod le_xy eps <= i)%N -> x i < y i + eps.
Proof.
by move=> eps_gt0; rewrite /le_mod; case: (asympt_le _)=> /= m hm /hm; apply.
Qed.

Lemma ge0_modP (x : creal) (x_ge0 : (0 <= x)%CR) eps i : 0 < eps ->
                (le_mod x_ge0 eps <= i)%N -> - eps < x i.
Proof.
by move=> eps_gt0 hi; rewrite -(ltr_add2r eps) addNr -[0]/(0%CR i) le_modP.
Qed.

Lemma opp_crealP (x : creal) : creal_axiom (fun i => - x i).
Proof. by case: x=> [x [m mP]]; exists m=> *; rewrite /= -opprD normrN mP. Qed.
Definition opp_creal (x : creal) := CReal (opp_crealP x).
Notation "-%CR" := opp_creal : creal_scope.
Notation "- x" := (opp_creal x) : creal_scope.

Lemma add_crealP (x y : creal) :  creal_axiom (fun i => x i + y i).
Proof.
exists_big_modulus m F.
  move=> e i j he hi hj; rewrite opprD addrAC addrA -addrA [- _ + _]addrC.
  by rewrite split_norm_add ?cauchymodP ?divrn_gt0.
by close.
Qed.
Definition add_creal (x y : creal) := CReal (add_crealP x y).
Notation "+%CR" := add_creal : creal_scope.
Notation "x + y" := (add_creal x y) : creal_scope.
Notation "x - y" := (x + - y)%CR : creal_scope.


Lemma ubound_subproof (x : creal) : {b : F | b > 0 & forall i, `|x i| <= b}.
Proof.
pose_big_enough i; first set b := 1 + `|x i|.
  exists (foldl maxr b [seq `|x n| | n <- iota 0 i]) => [|n].
    have : 0 < b by rewrite ltr_spaddl.
    by elim: iota b => //= a l IHl b b_gt0; rewrite IHl ?ltr_maxr ?b_gt0.
  have [|le_in] := (ltnP n i).
    elim: i b => [|i IHi] b //.
    rewrite ltnS -addn1 iota_add add0n map_cat foldl_cat /= ler_maxr leq_eqVlt.
    by case/orP=> [/eqP->|/IHi->] //; rewrite lerr orbT.
  set xn := `|x n|; suff : xn <= b.
    by elim: iota xn b => //= a l IHl xn b Hxb; rewrite IHl ?ler_maxr ?Hxb.
  rewrite -ler_subl_addr (ler_trans (ler_norm _)) //.
  by rewrite (ler_trans (ler_dist_dist _ _)) ?ltrW ?cauchymodP.
by close.
Qed.

Definition ubound (x : creal) := 
  nosimpl (let: exist2 b _ _ := ubound_subproof x in b).

Lemma uboundP (x : creal) i : `|x i| <= ubound x.
Proof. by rewrite /ubound; case: ubound_subproof. Qed.

Lemma ubound_gt0 x : 0 < ubound x.
Proof. by rewrite /ubound; case: ubound_subproof. Qed.

Definition ubound_ge0 x := (ltrW (ubound_gt0 x)).

Lemma mul_crealP (x y : creal) :  creal_axiom (fun i => x i * y i).
Proof.
exists_big_modulus m F.
  move=> e i j e_gt0 hi hj.
  rewrite -[_ * _]subr0 -(subrr (x j * y i)) opprD opprK addrA.
  rewrite -mulrBl -addrA -mulrBr split_norm_add // !normrM.
    have /ler_wpmul2l /ler_lt_trans-> // := uboundP y i.
    rewrite -ltr_pdivl_mulr ?ubound_gt0 ?cauchymodP //.
    by rewrite !pmulr_rgt0 ?invr_gt0 ?ubound_gt0 ?ltr0n.
  rewrite mulrC; have /ler_wpmul2l /ler_lt_trans-> // := uboundP x j.
  rewrite -ltr_pdivl_mulr ?ubound_gt0 ?cauchymodP //.
  by rewrite !pmulr_rgt0 ?gtr0E ?ubound_gt0.
by close.
Qed.
Definition mul_creal (x y : creal) := CReal (mul_crealP x y).
Notation "*%CR" := mul_creal : creal_scope.
Notation "x * y" := (mul_creal x y) : creal_scope.

Lemma inv_crealP (x : creal) (x_neq0 : x != 0) : creal_axiom (fun i => (x i)^-1).
Proof.
pose d := lbound x_neq0.
exists_big_modulus m F.
 (* exists (fun e => [CC x # e * d ^+ 2; ! x_neq0]). *)
  move=> e i j e_gt0 hi hj.
  have /andP[xi_neq0 xj_neq0] : (x i != 0) && (x j != 0).
    by rewrite -!normr_gt0 !(ltr_le_trans _ (lbound0_of x_neq0)) ?lbound_gt0.
  rewrite -(@ltr_pmul2r _ `|x i * x j|); last by rewrite normr_gt0 mulf_neq0.
  rewrite -normrM !mulrBl mulrA mulVf // mulrCA mulVf // mul1r mulr1.
  apply: (@ltr_le_trans _ (e * d ^+ 2)).
    by apply: cauchymodP; rewrite // !pmulr_rgt0 ?lbound_gt0.
  rewrite ler_wpmul2l ?(ltrW e_gt0) // normrM.
  have /(_ j) hx := lbound0_of x_neq0; rewrite /=.
  have -> // := (ler_trans (@ler_wpmul2l _ d _ _ _ (hx _ _))).
    by rewrite ltrW // lbound_gt0.
  by rewrite ler_wpmul2r ?normr_ge0 // lbound0P.
by close.
Qed.
Definition inv_creal (x : creal) (x_neq0 : x != 0) := CReal (inv_crealP x_neq0).
Notation "x_neq0 ^-1" := (inv_creal x_neq0) : creal_scope.
Notation "x / y_neq0" := (x * (y_neq0 ^-1))%CR : creal_scope.

Lemma norm_crealP (x : creal) : creal_axiom (fun i => `|x i|).
Proof.
exists (cauchymod x).
by move=> *; rewrite (ler_lt_trans (ler_dist_dist _ _)) ?cauchymodP.
Qed.
Definition norm_creal x := CReal (norm_crealP x).
Local Notation "`| x |" := (norm_creal x) : creal_scope.

Lemma horner_crealP (p : {poly F}) (x : creal) :
  creal_axiom (fun i => p.[x i]).
Proof.
exists_big_modulus m F=> [e i j e_gt0 hi hj|].
  rewrite (ler_lt_trans (@poly_accr_bound1P _ p (x (cauchymod x 1)) 1 _ _ _ _));
    do ?[by rewrite ?e_gt0 | by rewrite ltrW // cauchymodP].
  rewrite -ltr_pdivl_mulr ?poly_accr_bound_gt0 ?cauchymodP //.
  by rewrite pmulr_rgt0 ?invr_gt0 ?poly_accr_bound_gt0.
by close.
Qed.
Definition horner_creal (p : {poly F}) (x : creal) := CReal (horner_crealP p x).
Notation "p .[ x ]" := (horner_creal p x) : creal_scope.

Lemma neq_creal_horner p (x y : creal) : p.[x] != p.[y] -> x != y.
Proof.
move=> neq_px_py.
pose d := lbound neq_px_py.
pose_big_enough i.
  pose k := 2%:R + poly_accr_bound p (y i) d.
  have /andP[d_gt0 k_gt0] : (0 < d) && (0 < k).
    rewrite ?(ltr_spaddl, poly_accr_bound_ge0);
    by rewrite ?ltr0n ?ltrW ?ltr01 ?lbound_gt0.
  pose_big_enough j.
    apply: (@neq_crealP (d / k) j j) => //.
      by rewrite ?(pmulr_lgt0, invr_gt0, ltr0n).
    rewrite ler_pdivr_mulr //.
    have /(_ j) // := (lbound_of neq_px_py).
    big_enough=> /(_ isT isT).
    apply: contraLR; rewrite -!ltrNge=> hxy.
    rewrite (ler_lt_trans (@poly_accr_bound1P _ _ (y i) d _ _ _ _)) //.
    + by rewrite ltrW // cauchymodP.
    + rewrite ltrW // (@split_dist_add (y j)) //; last first.
        by rewrite cauchymodP ?divrn_gt0.
      rewrite ltr_pdivl_mulr ?ltr0n // (ler_lt_trans _ hxy) //.
      by rewrite ler_wpmul2l ?normr_ge0 // ler_paddr // poly_accr_bound_ge0.
    rewrite (ler_lt_trans _ hxy) // ler_wpmul2l ?normr_ge0 //.
    by rewrite ler_paddl // ?ler0n.
  by close.
by close.
Qed.

Lemma eq_creal_horner p (x y : creal) : x == y -> p.[x] == p.[y].
Proof. by move=> hxy /neq_creal_horner. Qed.

Import Setoid Relation_Definitions.

Add Relation creal eq_creal
  reflexivity proved by eq_creal_refl
  symmetry proved by eq_creal_sym
  transitivity proved by eq_creal_trans
as eq_creal_rel.
Global Existing Instance eq_creal_rel.

Add Morphism add_creal with
  signature eq_creal ==> eq_creal ==> eq_creal as add_creal_morph.
Proof.
move=> x y eq_xy z t eq_zt; apply: eq_crealP.
exists_big_modulus m F.
  move=> e i e_gt0 hi; rewrite opprD addrA [X in X + _]addrAC -addrA.
  by rewrite split_norm_add ?eq_modP ?divrn_gt0.
by close.
Qed.
Global Existing Instance add_creal_morph_Proper.


Add Morphism opp_creal with
  signature eq_creal ==> eq_creal as opp_creal_morph.
Proof.
move=> x y /asympt_eq [m hm]; apply: eq_crealP; exists m.
by move=> e i e_gt0 hi /=; rewrite -opprD normrN hm.
Qed.
Global Existing Instance opp_creal_morph_Proper.

Add Morphism mul_creal with
  signature eq_creal ==> eq_creal ==> eq_creal as mul_creal_morph.
Proof.
move=> x y eq_xy z t eq_zt; apply: eq_crealP.
exists_big_modulus m F.
  move=> e i e_gt0 hi.
  rewrite (@split_dist_add (y i * z i)) // -(mulrBl, mulrBr) normrM.
    have /ler_wpmul2l /ler_lt_trans-> // := uboundP z i.
    rewrite -ltr_pdivl_mulr ?ubound_gt0 ?eq_modP //.
    by rewrite !pmulr_rgt0 ?invr_gt0 ?ubound_gt0 ?ltr0n.
  rewrite mulrC; have /ler_wpmul2l /ler_lt_trans-> // := uboundP y i.
  rewrite -ltr_pdivl_mulr ?ubound_gt0 ?eq_modP //.
  by rewrite !pmulr_rgt0 ?invr_gt0 ?ubound_gt0 ?ltr0n.
by close.
Qed.
Global Existing Instance mul_creal_morph_Proper.

Lemma eq_creal_inv (x y : creal) (x_neq0 : x != 0) (y_neq0 : y != 0) :
  (x == y) -> (x_neq0^-1 == y_neq0^-1).
Proof.
move=> eq_xy; apply: eq_crealP; exists_big_modulus m F.
  move=> e i e_gt0 hi /=.
  rewrite -(@ltr_pmul2r _ (lbound x_neq0 * lbound y_neq0));
    do ?by rewrite ?pmulr_rgt0 ?lbound_gt0.
  rewrite (@ler_lt_trans _ (`|(x i)^-1 - (y i)^-1| * (`|x i| * `|y i|))) //.
    rewrite ler_wpmul2l ?normr_ge0 //.
    rewrite (@ler_trans _ (`|x i| * lbound y_neq0)) //.
      by rewrite ler_wpmul2r ?lbound_ge0 ?lbound0P.
    by rewrite ler_wpmul2l ?normr_ge0 ?lbound0P.
  rewrite -!normrM mulrBl mulKf ?creal_neq0_always //.
  rewrite mulrCA mulVf ?mulr1 ?creal_neq0_always //.
  by rewrite distrC eq_modP ?pmulr_rgt0 ?lbound_gt0.
by close.
Qed.

Add Morphism horner_creal with
  signature (@eq _) ==> eq_creal ==> eq_creal as horner_creal_morph.
Proof. exact: eq_creal_horner. Qed.
Global Existing Instance horner_creal_morph_Proper.

Add Morphism lt_creal with
  signature eq_creal ==> eq_creal ==> iff as lt_creal_morph.
Proof.
move=> x y eq_xy z t eq_zt.
wlog lxz : x y z t eq_xy eq_zt / (x < z)%CR.
  move=> hwlog; split=> h1; move: (h1) => /hwlog; apply=> //;
  by apply: eq_creal_sym.
split=> // _.
pose e' := diff lxz / 4%:R.
have e'_gt0 : e' > 0 by rewrite pmulr_rgt0 ?gtr0E ?diff_gt0.
have le_zt : (z <= t)%CR by apply: eq_le_creal.
have le_xy : (y <= x)%CR by apply: eq_le_creal; apply: eq_creal_sym.
pose_big_enough i.
  apply: (@lt_crealP e' i i)=> //.
  rewrite ltrW // -(ltr_add2r e').
  rewrite (ler_lt_trans _ (@le_modP _ _ le_zt _ _ _ _)) //.
  rewrite -addrA (monoLR (@addrNK _ _) (@ler_add2r _ _)) ltrW //.
  rewrite (ltr_le_trans (@le_modP _ _ le_xy e' _ _ _)) //.
  rewrite -(monoLR (@addrNK _ _) (@ler_add2r _ _)) ltrW //.
  rewrite (ltr_le_trans _ (diff_of lxz)) //.
  rewrite -addrA ler_lt_add // /e' -!mulrDr gtr_pmulr ?diff_gt0 //.
  by rewrite [X in _ < X](splitf 4) /=  mul1r !ltr_addr ?gtr0E.
by close.
Qed.
Global Existing Instance lt_creal_morph_Proper.

Add Morphism le_creal with
  signature eq_creal ==> eq_creal ==> iff as le_creal_morph.
Proof. by move=> x y exy z t ezt; rewrite /le_creal exy ezt. Qed.
Global Existing Instance le_creal_morph_Proper.

Add Morphism norm_creal
 with signature eq_creal ==> eq_creal as norm_creal_morph.
Proof.
move=> x y hxy; apply: eq_crealP; exists_big_modulus m F.
  move=> e i e_gt0 hi.
  by rewrite (ler_lt_trans (ler_dist_dist _ _)) ?eq_modP.
by close.
Qed.
Global Existing Instance norm_creal_morph_Proper.

Lemma neq_creal_ltVgt (x y : creal) : x != y -> {(x < y)%CR} + {(y < x)%CR}.
Proof.
move=> neq_xy; pose_big_enough i.
  have := (@lboundP _ _ neq_xy i); big_enough => /(_ isT isT).
  have [le_xy|/ltrW le_yx'] := lerP (x i) (y i).
    rewrite -(ler_add2r (x i)) ?addrNK addrC.
    move=> /lt_crealP; rewrite ?lbound_gt0; big_enough.
    by do 3!move/(_ isT); left.
  rewrite -(ler_add2r (y i)) ?addrNK addrC.
  move=> /lt_crealP; rewrite ?lbound_gt0; big_enough.
  by do 3!move/(_ isT); right.
by close.
Qed.

Lemma lt_creal_neq (x y : creal) : (x < y -> x != y)%CR.
Proof.
move=> lxy; pose_big_enough i.
  apply: (@neq_crealP (diff lxy) i i); rewrite ?diff_gt0 //.
  rewrite distrC ler_normr (monoRL (addrK _) (ler_add2r _)) addrC.
  by rewrite (diff_of lxy).
by close.
Qed.

Lemma gt_creal_neq (x y : creal) : (y < x -> x != y)%CR.
Proof. by move/lt_creal_neq /neq_creal_sym. Qed.

Lemma lt_creal_trans (x y z : creal) : (x < y -> y < z -> x < z)%CR.
Proof.
move=> lt_xy lt_yz; pose_big_enough i.
  apply: (@lt_crealP (diff lt_xy + diff lt_yz) i i) => //.
    by rewrite addr_gt0 ?diff_gt0.
  rewrite (ler_trans _ (diff_of lt_yz)) //.
  by rewrite addrA ler_add2r (diff_of lt_xy).
by close.
Qed.

Lemma lt_crealW (x y : creal) : (x < y)%CR -> (x <= y)%CR.
Proof. by move=> /lt_creal_trans /(_ _) /le_creal_refl. Qed.

Add Morphism neq_creal with
  signature eq_creal ==> eq_creal ==> iff as neq_creal_morph.
Proof.
move=> x y eq_xy z t eq_zt; split=> /neq_creal_ltVgt [].
+ by rewrite eq_xy eq_zt=> /lt_creal_neq.
+ by rewrite eq_xy eq_zt=> /gt_creal_neq.
+ by rewrite -eq_xy -eq_zt=> /lt_creal_neq.
by rewrite -eq_xy -eq_zt=> /gt_creal_neq.
Qed.
Global Existing Instance neq_creal_morph_Proper.

Local Notation m0 := (fun (_ : F) => 0%N).

Lemma add_0creal x : 0 + x == x.
Proof. by apply: eq_crealP; exists m0=> * /=; rewrite add0r subrr normr0. Qed.

Lemma add_creal0 x : x + 0 == x.
Proof. by apply: eq_crealP; exists m0=> * /=; rewrite addr0 subrr normr0. Qed.

Lemma mul_creal0 x : x * 0 == 0.
Proof. by apply: eq_crealP; exists m0=> * /=; rewrite mulr0 subrr normr0. Qed.

Lemma mul_0creal x : 0 * x == 0.
Proof. by apply: eq_crealP; exists m0=> * /=; rewrite mul0r subrr normr0. Qed.

Lemma mul_creal1 x : x * 1%:CR == x.
Proof. by apply: eq_crealP; exists m0=> * /=; rewrite mulr1 subrr normr0. Qed.

Lemma mul_1creal x : 1%:CR * x == x.
Proof. by apply: eq_crealP; exists m0=> * /=; rewrite mul1r subrr normr0. Qed.

Lemma opp_creal0 : - 0 == 0.
Proof. by apply: eq_crealP; exists m0=> * /=; rewrite oppr0 addr0 normr0. Qed.

Lemma horner_crealX (x : creal) : 'X.[x] == x.
Proof. by apply: eq_crealP; exists m0=> *; rewrite /= hornerX subrr normr0. Qed.

Lemma horner_crealM (p q : {poly F}) (x : creal) :
  ((p * q).[x] == p.[x] * q.[x])%CR.
Proof.
by apply: eq_crealP; exists m0=> * /=; rewrite hornerM subrr normr0.
Qed.

Lemma neq_creal_cst x y : reflect (cst_creal x != cst_creal y) (x != y).
Proof.
apply: (iffP idP)=> neq_xy; pose_big_enough i.
+ by apply (@neq_crealP `|x - y| i i); rewrite ?normr_gt0 ?subr_eq0 .
+ by close.
+ by rewrite (@creal_neq_always _ _ i neq_xy).
+ by close.
Qed.

Lemma eq_creal_cst x y : reflect (cst_creal x == cst_creal y) (x == y).
Proof.
apply: (iffP idP)=> [|eq_xy]; first by move/eqP->.
by apply/negP=> /negP /neq_creal_cst; rewrite eq_xy; apply: eq_creal_refl.
Qed.

Lemma lt_creal_cst x y : reflect (cst_creal x < cst_creal y)%CR (x < y).
Proof.
apply: (iffP idP)=> lt_xy; pose_big_enough i.
+ apply: (@lt_crealP (y - x) i i); rewrite ?subr_gt0 //=.
  by rewrite addrCA subrr addr0.
+ by close.
+ by rewrite (@creal_lt_always _ _ i lt_xy).
+ by close.
Qed.

Lemma le_creal_cst x y : reflect (cst_creal x <= cst_creal y)%CR (x <= y).
Proof.
apply: (iffP idP)=> [le_xy /lt_creal_cst|eq_xy]; first by rewrite ltrNge le_xy.
by rewrite lerNgt; apply/negP=> /lt_creal_cst.
Qed.


Lemma mul_creal_neq0 x y : x != 0 -> y != 0 -> x * y != 0.
Proof.
move=> x_neq0 y_neq0.
pose d := lbound x_neq0 * lbound y_neq0.
have d_gt0 : 0 < d by rewrite pmulr_rgt0 lbound_gt0.
pose_big_enough i.
  apply: (@neq_crealP d i i)=> //; rewrite subr0 normrM.
  rewrite (@ler_trans _ (`|x i| * lbound y_neq0)) //.
    by rewrite ler_wpmul2r ?lbound_ge0 // lbound0P.
  by rewrite ler_wpmul2l ?normr_ge0 // lbound0P.
by close.
Qed.

Lemma mul_neq0_creal x y : x * y != 0 -> y != 0.
Proof.
move=> xy_neq0; pose_big_enough i.
  apply: (@neq_crealP ((ubound x)^-1 * lbound xy_neq0) i i) => //.
    by rewrite pmulr_rgt0 ?invr_gt0 ?lbound_gt0 ?ubound_gt0.
  rewrite subr0 ler_pdivr_mull ?ubound_gt0 //.
  have /(_ i)-> // := (ler_trans (lbound0_of xy_neq0)).
  by rewrite normrM ler_wpmul2r ?normr_ge0 ?uboundP.
by close.
Qed.

Lemma poly_mul_creal_eq0_coprime p q x :
  coprimep p q ->
  p.[x] * q.[x] == 0 -> {p.[x] == 0} + {q.[x] == 0}.
Proof.
move=> /Bezout_eq1_coprimepP /sig_eqW [[u v] /= hpq]; pose_big_enough i.
  have := (erefl ((1 : {poly F}).[x i])).
  rewrite -{1}hpq /= hornerD hornerC.
  set upxi := (u * _).[_].
  move=> hpqi.
  have [p_small|p_big] := lerP `|upxi| 2%:R^-1=> pqx0; [left|right].
    move=> px0; apply: pqx0; apply: mul_creal_neq0=> //.
    apply: (@mul_neq0_creal v.[x]).
    apply: (@neq_crealP 2%:R^-1 i i); rewrite ?gtr0E //.
    rewrite /= subr0 -hornerM -(ler_add2l `|upxi|).
    rewrite (ler_trans _ (ler_norm_add _ _)) // hpqi normr1.
    rewrite (monoLR (addrNK _) (ler_add2r _)).
    by rewrite {1}[1](splitf 2) /= mul1r addrK.
  move=> qx0; apply: pqx0; apply: mul_creal_neq0=> //.
  apply: (@mul_neq0_creal u.[x]).
  apply: (@neq_crealP 2%:R^-1 i i); rewrite ?gtr0E //.
  by rewrite /= subr0 -hornerM ltrW.
by close.
Qed.

Lemma dvdp_creal_eq0 p q x : p %| q -> p.[x] == 0 -> q.[x] == 0.
Proof.
by move=> dpq px0; rewrite -[q](divpK dpq) horner_crealM px0 mul_creal0.
Qed.

Lemma root_poly_expn_creal p k x : (0 < k)%N
  -> (p ^+ k).[x] == 0 -> p.[x] == 0.
Proof.
move=> k_gt0 pkx_eq0; apply: eq_crealP; exists_big_modulus m F.
  move=> e i e_gt0 hi; rewrite /= subr0.
  rewrite -(@ltr_pexpn2r _ k) -?topredE /= ?normr_ge0 ?ltrW //.
  by rewrite -normrX -horner_exp (@eq0_modP _ pkx_eq0) ?exprn_gt0 //.
by close.
Qed.

Lemma horner_cst_creal c x : c%:P.[x] == c%:CR.
Proof.
apply: eq_crealP; exists (fun _ => 0%N)=> e i e_gt0 _.
by rewrite /= hornerC subrr normr0.
Qed.

Lemma horner_creal_cst (p : {poly F}) (x : F) : p.[x%:CR] == p.[x]%:CR.
Proof. by apply: eq_crealP; exists m0=> *; rewrite /= subrr normr0. Qed.


Lemma poly_mul_creal_eq0 p q x :
  p.[x] * q.[x] == 0 -> {p.[x] == 0} + {q.[x] == 0}.
Proof.
move=> mul_px_qx_eq0.
have [->|p_neq0] := altP (p =P 0); first by left; rewrite horner_cst_creal.
have [->|q_neq0] := altP (q =P 0); first by right; rewrite horner_cst_creal.
pose d := gcdp p q; pose p' := gdcop d p; pose q' := gdcop d q.
have cop_q'_d': coprimep p' q'.
  rewrite /coprimep size_poly_eq1.
  apply: (@coprimepP _ p' d _).
  + by rewrite coprimep_gdco.
  + by rewrite dvdp_gcdl.
  rewrite dvdp_gcd (dvdp_trans (dvdp_gcdl _ _)) ?dvdp_gdco //.
  by rewrite (dvdp_trans (dvdp_gcdr _ _)) ?dvdp_gdco.
suff : (p' * q').[x]  * (d ^+ (size p + size q)).[x] == 0.
  case/poly_mul_creal_eq0_coprime.
  + by rewrite coprimep_expr // coprimep_mull ?coprimep_gdco.
  + move=> p'q'x_eq0.
    have : p'.[x] * q'.[x] == 0 by rewrite -horner_crealM.
    case/poly_mul_creal_eq0_coprime=> // /dvdp_creal_eq0 hp'q'.
      by left; apply: hp'q'; rewrite dvdp_gdco.
    by right; apply: hp'q'; rewrite dvdp_gdco.
  move/root_poly_expn_creal.
  rewrite addn_gt0 lt0n size_poly_eq0 p_neq0=> /(_ isT) dx_eq0.
  by left; apply: dvdp_creal_eq0 dx_eq0; rewrite dvdp_gcdl.
move: mul_px_qx_eq0; rewrite -!horner_crealM.
rewrite exprD mulrAC mulrA -mulrA [_ ^+ _ * _]mulrC.
apply: dvdp_creal_eq0; rewrite ?dvdp_mul // dvdp_gdcor //;
by rewrite gcdp_eq0 negb_and p_neq0.
Qed.

Lemma coprimep_root (p q : {poly F}) x :
  coprimep p q -> p.[x] == 0 -> q.[x] != 0.
Proof.
move=> /Bezout_eq1_coprimepP /sig_eqW [[u v] hpq] px0.
have upx_eq0 : u.[x] * p.[x] == 0 by rewrite px0 mul_creal0.
pose_big_enough i.
  have := (erefl ((1 : {poly F}).[x i])).
  rewrite -{1}hpq /= hornerD hornerC.
  set upxi := (u * _).[_] => hpqi.
  apply: (@neq_crealP ((ubound v.[x])%CR^-1 / 2%:R) i i) => //.
    by rewrite pmulr_rgt0 ?gtr0E // ubound_gt0.
  rewrite /= subr0 ler_pdivr_mull ?ubound_gt0 //.
  rewrite (@ler_trans _  `|(v * q).[x i]|) //; last first.
    by rewrite hornerM normrM ler_wpmul2r ?normr_ge0 ?(uboundP v.[x]).
  rewrite -(ler_add2l `|upxi|) (ler_trans _ (ler_norm_add _ _)) // hpqi normr1.
  rewrite (monoLR (addrNK _) (ler_add2r _)).
  rewrite {1}[1](splitf 2) /= mul1r addrK ltrW // /upxi hornerM.
  by rewrite (@eq0_modP _ upx_eq0) ?gtr0E.
by close.
Qed.

Lemma deriv_neq0_mono (p : {poly F}) (x : creal) : p^`().[x] != 0 ->
  { r : F & 0 < r &
    { i : nat & (cauchymod x r <= i)%N & (strong_mono p (x i) r)} }.
Proof.
move=> px_neq0.
wlog : p px_neq0 / (0 < p^`().[x])%CR.
  case/neq_creal_ltVgt: (px_neq0)=> px_lt0; last exact.
  case/(_ (- p)).
  + pose_big_enough i.
      apply: (@neq_crealP (lbound px_neq0) i i); do ?by rewrite ?lbound_gt0.
      rewrite /= derivN hornerN subr0 normrN.
      by rewrite (lbound0_of px_neq0).
    by close.
  + pose_big_enough i.
      apply: (@lt_crealP (diff px_lt0) i i); do ?by rewrite ?diff_gt0.
      rewrite /= add0r derivN hornerN -subr_le0 opprK addrC.
      by rewrite (diff_of px_lt0) //.
    by close.
  move=> r r_ge0 [i hi]; move/strong_monoN; rewrite opprK=> sm.
  by exists r=> //; exists i.
move=> px_gt0.
pose b1 := poly_accr_bound p^`() 0 (1 + ubound x).
pose b2 := poly_accr_bound2 p 0 (1 + ubound x).
pose r := minr 1 (minr
  (diff px_gt0 / 4%:R / b1)
  (diff px_gt0 / 4%:R / b2 / 2%:R)).
exists r.
  rewrite !ltr_minr ?ltr01 ?pmulr_rgt0 ?gtr0E ?diff_gt0;
  by rewrite ?poly_accr_bound2_gt0 ?poly_accr_bound_gt0.
pose_big_enough i.
  exists i => //; left; split; last first.
    move=> y hy; have := (@poly_accr_bound1P _ p^`() 0 (1 + ubound x) (x i) y).
    rewrite ?subr0 ler_paddl ?ler01 ?uboundP //.
    rewrite (@ler_trans _ (r + `|x i|)) ?subr0; last 2 first.
    + rewrite (monoRL (addrNK _) (ler_add2r _)).
      by rewrite (ler_trans (ler_sub_dist _ _)).
    + by rewrite ler_add ?ler_minl ?lerr ?uboundP.
    move=> /(_ isT isT).
    rewrite ler_distl=> /andP[le_py ge_py].
    rewrite (ltr_le_trans _ le_py) // subr_gt0 -/b1.
    rewrite (ltr_le_trans _ (diff0_of px_gt0)) //.
    rewrite (@ler_lt_trans _ (r * b1)) //.
      by rewrite ler_wpmul2r ?poly_accr_bound_ge0.
    rewrite -ltr_pdivl_mulr ?poly_accr_bound_gt0 //.
    rewrite !ltr_minl ltr_pmul2r ?invr_gt0 ?poly_accr_bound_gt0 //.
    by rewrite gtr_pmulr ?diff_gt0 // invf_lt1 ?gtr0E ?ltr1n ?orbT.
  exists (diff px_gt0 / 4%:R).
   by rewrite pmulr_rgt0 ?gtr0E ?diff_gt0.
  move=> y z neq_yz hy hz.
  have := (@poly_accr_bound1P _ p^`() 0 (1 + ubound x) (x i) z).
  have := @poly_accr_bound2P _ p 0 (1 + ubound x) z y; rewrite eq_sym !subr0.
  rewrite neq_yz ?ler01 ?ubound_ge0=> // /(_ isT).
  rewrite (@ler_trans _ (r + `|x i|)); last 2 first.
  + rewrite (monoRL (addrNK _) (ler_add2r _)).
    by rewrite (ler_trans (ler_sub_dist _ _)).
  + rewrite ler_add ?ler_minl ?lerr ?uboundP //.
  rewrite (@ler_trans _ (r + `|x i|)); last 2 first.
  + rewrite (monoRL (addrNK _) (ler_add2r _)).
    by rewrite (ler_trans (ler_sub_dist _ _)).
  + rewrite ler_add ?ler_minl ?lerr ?uboundP //.
  rewrite ler_paddl ?uboundP ?ler01 //.
  move=> /(_ isT isT); rewrite ler_distl=> /andP [haccr _].
  move=> /(_ isT isT); rewrite ler_distl=> /andP [hp' _].
  rewrite (ltr_le_trans _ haccr) // (monoRL (addrK _) (ltr_add2r _)).
  rewrite (ltr_le_trans _ hp') // (monoRL (addrK _) (ltr_add2r _)).
  rewrite (ltr_le_trans _ (diff0_of px_gt0)) //.
  rewrite {2}[diff _](splitf 4) /= -!addrA ltr_add2l ltr_spaddl //.
    by rewrite pmulr_rgt0 ?gtr0E ?diff_gt0.
  rewrite -/b1 -/b2 ler_add //.
    rewrite -ler_pdivl_mulr ?poly_accr_bound2_gt0 //.
    rewrite (@ler_trans _ (r * 2%:R)) //.
      rewrite (ler_trans (ler_dist_add (x i) _ _)) //.
        by rewrite mulrDr mulr1 ler_add // distrC.
      by rewrite -ler_pdivl_mulr ?ltr0n // !ler_minl lerr !orbT.
    rewrite -ler_pdivl_mulr ?poly_accr_bound_gt0 //.
    by rewrite (@ler_trans _ r) // !ler_minl lerr !orbT.
by close.
Qed.

Lemma smaller_factor (p q : {poly F}) x :
  p \is monic-> p.[x] == 0 ->
  ~~(p %| q) -> ~~ coprimep p q ->
  {r : {poly F} | (size r < size p)%N && (r \is monic) & r.[x] == 0}.
Proof.
move=> monic_p px0 ndvd_pq.
rewrite /coprimep; set d := gcdp _ _=> sd_neq1.
pose r1 : {poly F} := (lead_coef d)^-1 *: d.
pose r2 := p %/ r1.
have ld_neq0 : lead_coef d != 0 :> F.
  by rewrite lead_coef_eq0 gcdp_eq0 negb_and monic_neq0.
have monic_r1 : r1 \is monic.
  by rewrite monicE /r1 -mul_polyC lead_coefM lead_coefC mulVf.
have eq_p_r2r1: p = r2 * r1.
  by rewrite divpK // (@eqp_dvdl _ d) ?dvdp_gcdl // eqp_scale ?invr_eq0.
have monic_r2 : r2 \is monic by rewrite -(monicMr _ monic_r1) -eq_p_r2r1.
have eq_sr1_sd : size r1 = size d by rewrite size_scale ?invr_eq0.
have sr1 : (1 < size r1)%N.
  by rewrite ltn_neqAle eq_sym lt0n size_poly_eq0 monic_neq0 ?andbT ?eq_sr1_sd.
have sr2 : (1 < size r2)%N.
  rewrite size_divp ?size_dvdp ?monic_neq0 //.
  rewrite ltn_subRL addn1 prednK ?(leq_trans _ sr1) // eq_sr1_sd.
  rewrite ltn_neqAle dvdp_leq ?monic_neq0 ?andbT ?dvdp_size_eqp ?dvdp_gcdl //.
  by apply: contra ndvd_pq=> /eqp_dvdl <-; rewrite dvdp_gcdr.
move: (px0); rewrite eq_p_r2r1=> r2r1x_eq0.
have : (r2.[x] * r1.[x] == 0) by rewrite -horner_crealM.
case/poly_mul_creal_eq0=> [r2x_eq0|r1x_eq0].
  exists r2; rewrite ?monic_r2 ?andbT // mulrC.
  by rewrite -ltn_divpl ?divpp ?monic_neq0 // size_poly1.
exists r1; rewrite ?monic_r1 ?andbT //.
by rewrite -ltn_divpl ?divpp ?monic_neq0 // size_poly1.
Qed.

Lemma root_cst_creal (x : F) : ('X - x%:P).[cst_creal x] == 0.
Proof.
apply: eq_crealP; exists_big_modulus m F.
  by move=> e i e_gt0 hi; rewrite /= subr0 !hornerE subrr normr0.
by close.
Qed.

Lemma has_root_creal_size_gt1 (x : creal) (p : {poly F}) :
  (p != 0)%B -> p.[x] == 0 -> (1 < size p)%N.
Proof.
move=> p_neq0 rootpa.
rewrite ltnNge leq_eqVlt ltnS leqn0 size_poly_eq0 (negPf p_neq0) orbF.
apply/negP=> /size_poly1P [c c_neq0 eq_pc]; apply: rootpa.
by rewrite eq_pc horner_cst_creal; apply/neq_creal_cst.
Qed.

Definition bound_poly_bound (z : creal) (q : {poly {poly F}}) (a r : F) i :=
  (1 + \sum_(j < sizeY q)
    `|(norm_poly2 q).[(ubound z)%:P]^`N(i.+1)`_j| * (`|a| + `|r|) ^+ j).

Lemma bound_poly_boundP (z : creal) i (q : {poly {poly F}}) (a r : F) j :
  poly_bound q.[(z i)%:P]^`N(j.+1) a r <= bound_poly_bound z q a r j.
Proof.
rewrite /poly_bound.
pose f q (k : nat) :=  `|q^`N(j.+1)`_k| * (`|a| + `|r|) ^+ k.
rewrite ler_add //=.
rewrite (big_ord_widen (sizeY q) (f q.[(z i)%:P])); last first.
  rewrite size_nderivn leq_subLR (leq_trans (max_size_evalC _ _)) //.
  by rewrite leq_addl.
rewrite big_mkcond /= ler_sum // /f => k _.
case: ifP=> _; last by rewrite mulr_ge0 ?exprn_ge0 ?addr_ge0 ?normr_ge0.
rewrite ler_wpmul2r ?exprn_ge0 ?addr_ge0 ?normr_ge0 //.
rewrite !horner_coef.
rewrite !(@big_morph _ _ (fun p => p^`N(j.+1)) 0 +%R);
  do ?[by rewrite raddf0|by move=> x y /=; rewrite raddfD].
rewrite !coef_sum.
rewrite (ler_trans (ler_norm_sum _ _ _)) //.
rewrite ger0_norm; last first.
  rewrite sumr_ge0=> //= l _.
  rewrite coef_nderivn mulrn_wge0 ?natr_ge0 //.
  rewrite -polyC_exp coefMC coef_norm_poly2 mulr_ge0 ?normr_ge0 //.
  by rewrite exprn_ge0 ?ltrW ?ubound_gt0.
rewrite size_norm_poly2 ler_sum //= => l _.
rewrite !{1}coef_nderivn normrMn ler_pmuln2r ?bin_gt0 ?leq_addr //.
rewrite -!polyC_exp !coefMC coef_norm_poly2 normrM ler_wpmul2l ?normr_ge0 //.
rewrite normrX; case: (val l)=> // {l} l.
by rewrite ler_pexpn2r -?topredE //= ?uboundP ?ltrW ?ubound_gt0.
Qed.

Lemma bound_poly_bound_ge0 z q a r i : 0 <= bound_poly_bound z q a r i.
Proof.
by rewrite (ler_trans _ (bound_poly_boundP _ 0%N _ _ _ _)) ?poly_bound_ge0.
Qed.

Definition bound_poly_accr_bound (z : creal) (q : {poly {poly F}}) (a r : F) :=
   maxr 1 (2%:R * r) ^+ (sizeY q).-1 *
   (1 + \sum_(i < (sizeY q).-1) bound_poly_bound z q a r i).

Lemma bound_poly_accr_boundP (z : creal) i (q : {poly {poly F}}) (a r : F) :
  poly_accr_bound q.[(z i)%:P] a r <= bound_poly_accr_bound z q a r.
Proof.
rewrite /poly_accr_bound /bound_poly_accr_bound /=.
set ui := _ ^+ _; set u := _ ^+ _; set vi := 1 + _.
rewrite (@ler_trans _ (u * vi)) //.
  rewrite ler_wpmul2r //.
    by rewrite addr_ge0 ?ler01 // sumr_ge0 //= => j _; rewrite poly_bound_ge0.
  rewrite /ui /u; case: maxrP; first by rewrite !expr1n.
  move=> r2_gt1; rewrite ler_eexpn2l //.
  rewrite -subn1 leq_subLR add1n (leq_trans _ (leqSpred _)) //.
  by rewrite max_size_evalC.
rewrite ler_wpmul2l ?exprn_ge0 ?ler_maxr ?ler01 // ler_add //.
pose f j :=  poly_bound q.[(z i)%:P]^`N(j.+1) a r.
rewrite (big_ord_widen (sizeY q).-1 f); last first.
  rewrite -subn1 leq_subLR add1n (leq_trans _ (leqSpred _)) //.
  by rewrite max_size_evalC.
rewrite big_mkcond /= ler_sum // /f => k _.
by case: ifP=> _; rewrite ?bound_poly_bound_ge0 ?bound_poly_boundP.
Qed.

Lemma bound_poly_accr_bound_gt0 (z : creal) (q : {poly {poly F}}) (a r : F) :
  0 < bound_poly_accr_bound z q a r.
Proof.
rewrite (ltr_le_trans _ (bound_poly_accr_boundP _ 0%N _ _ _)) //.
by rewrite poly_accr_bound_gt0.
Qed.

Lemma horner2_crealP (p : {poly {poly F}}) (x y : creal) :
  creal_axiom (fun i => p.[x i, y i]).
Proof.
set a := x (cauchymod x 1).
exists_big_modulus m F.
  move=> e i j e_gt0 hi hj; rewrite (@split_dist_add p.[x i, y j]) //.
    rewrite (ler_lt_trans (@poly_accr_bound1P _ _ 0 (ubound y) _ _ _ _)) //;
      do ?by rewrite ?subr0 ?uboundP.
    rewrite (@ler_lt_trans _ (`|y i - y j|
                            * bound_poly_accr_bound x p 0 (ubound y))) //.
      by rewrite ler_wpmul2l ?normr_ge0 // bound_poly_accr_boundP.
    rewrite -ltr_pdivl_mulr ?bound_poly_accr_bound_gt0 //.
    by rewrite cauchymodP // !pmulr_rgt0 ?gtr0E ?bound_poly_accr_bound_gt0.
  rewrite -[p]swapXYK  ![(swapXY (swapXY _)).[_, _]]horner2_swapXY.
  rewrite (ler_lt_trans (@poly_accr_bound1P _ _ 0 (ubound x) _ _ _ _)) //;
    do ?by rewrite ?subr0 ?uboundP.
  rewrite (@ler_lt_trans _ (`|x i - x j|
                   * bound_poly_accr_bound y (swapXY p) 0 (ubound x))) //.
    by rewrite ler_wpmul2l ?normr_ge0 // bound_poly_accr_boundP.
  rewrite -ltr_pdivl_mulr ?bound_poly_accr_bound_gt0 //.
  by rewrite cauchymodP // !pmulr_rgt0 ?gtr0E ?bound_poly_accr_bound_gt0.
by close.
Qed.

Definition horner2_creal (p : {poly {poly F}}) (x y : creal) :=
  CReal (horner2_crealP p x y).
Notation "p .[ x , y ]" := (horner2_creal p x y)
  (at level 2, left associativity) : creal_scope.

Lemma root_monic_from_neq0 (p : {poly F}) (x : creal) :
  p.[x] == 0 -> ((lead_coef p) ^-1 *: p).[x] == 0.
Proof. by rewrite -mul_polyC horner_crealM; move->; rewrite mul_creal0. Qed.

Lemma root_sub_annihilant_creal (x y : creal) (p q : {poly F}) :
  (p != 0)%B -> (q != 0)%B -> p.[x] == 0 -> q.[y] == 0 ->
  (sub_annihilant p q).[x - y] == 0.
Proof.
move=> p_neq0 q_neq0 px_eq0 qy_eq0.
have [||[u v] /= [hu hv] hpq] := @sub_annihilant_in_ideal _ p q.
+ by rewrite (@has_root_creal_size_gt1 x).
+ by rewrite (@has_root_creal_size_gt1 y).
apply: eq_crealP; exists_big_modulus m F.
  move=> e i e_gt0 hi /=; rewrite subr0.
  rewrite (hpq (y i)) addrCA subrr addr0 split_norm_add // normrM.
    rewrite (@ler_lt_trans _ ((ubound u.[y, x - y]) * `|p.[x i]|)) //.
      by rewrite ler_wpmul2r ?normr_ge0 // (uboundP u.[y, x - y] i).
    rewrite -ltr_pdivl_mull ?ubound_gt0 //.
    by rewrite (@eq0_modP _ px_eq0) // !pmulr_rgt0 ?gtr0E ?ubound_gt0.
  rewrite (@ler_lt_trans _ ((ubound v.[y, x - y]) * `|q.[y i]|)) //.
    by rewrite ler_wpmul2r ?normr_ge0 // (uboundP v.[y, x - y] i).
  rewrite -ltr_pdivl_mull ?ubound_gt0 //.
  by rewrite (@eq0_modP _ qy_eq0) // !pmulr_rgt0 ?gtr0E ?ubound_gt0.
by close.
Qed.

Lemma root_div_annihilant_creal (x y : creal) (p q : {poly F}) (y_neq0 : y != 0) :
  (p != 0)%B -> (q != 0)%B -> p.[x] == 0 -> q.[y] == 0 ->
  (div_annihilant p q).[(x / y_neq0)%CR] == 0.
Proof.
move=> p_neq0 q_neq0 px_eq0 qy_eq0.
have [||[u v] /= [hu hv] hpq] := @div_annihilant_in_ideal _ p q.
+ by rewrite (@has_root_creal_size_gt1 x).
+ by rewrite (@has_root_creal_size_gt1 y).
apply: eq_crealP; exists_big_modulus m F.
  move=> e i e_gt0 hi /=; rewrite subr0.
  rewrite (hpq (y i)) mulrCA divff ?mulr1; last first.
    by rewrite -normr_gt0 (ltr_le_trans _ (lbound0_of y_neq0)) ?lbound_gt0.
  rewrite split_norm_add // normrM.
    rewrite (@ler_lt_trans _ ((ubound u.[y, x / y_neq0]) * `|p.[x i]|)) //.
      by rewrite ler_wpmul2r ?normr_ge0 // (uboundP u.[y, x / y_neq0] i).
    rewrite -ltr_pdivl_mull ?ubound_gt0 //.
    by rewrite (@eq0_modP _ px_eq0) // !pmulr_rgt0 ?gtr0E ?ubound_gt0.
  rewrite (@ler_lt_trans _ ((ubound v.[y, x / y_neq0]) * `|q.[y i]|)) //.
    by rewrite ler_wpmul2r ?normr_ge0 // (uboundP v.[y, x / y_neq0] i).
  rewrite -ltr_pdivl_mull ?ubound_gt0 //.
  by rewrite (@eq0_modP _ qy_eq0) // !pmulr_rgt0 ?gtr0E ?ubound_gt0.
by close.
Qed.

Definition exp_creal x n := (iterop n *%CR x 1%:CR).
Notation "x ^+ n" := (exp_creal x n) : creal_scope.

Add Morphism exp_creal with
  signature eq_creal ==> (@eq _) ==> eq_creal as exp_creal_morph.
Proof.
move=> x y eq_xy [//|n]; rewrite /exp_creal !iteropS.
by elim: n=> //= n ->; rewrite eq_xy.
Qed.
Global Existing Instance exp_creal_morph_Proper.

Lemma horner_coef_creal p x :
   p.[x] == \big[+%CR/0%:CR]_(i < size p) ((p`_i)%:CR * (x ^+ i))%CR.
Proof.
apply: eq_crealP; exists m0=> e n e_gt0 hn /=; rewrite horner_coef.
rewrite (@big_morph _ _ (fun u : creal => u n) 0%R +%R) //.
rewrite -sumrB /= big1 ?normr0=> //= i _.
apply/eqP; rewrite subr_eq0; apply/eqP; congr (_ * _).
case: val=> {i} // i; rewrite exprS /exp_creal iteropS.
by elim: i=> [|i ihi]; rewrite ?expr0 ?mulr1 //= exprS ihi.
Qed.

End CauchyReals.

Notation "x == y" := (eq_creal x y) : creal_scope.
Notation "!=%CR" := neq_creal : creal_scope.
Notation "x != y" := (neq_creal x  y) : creal_scope.

Notation "x %:CR" := (cst_creal x)
  (at level 2, left associativity, format "x %:CR") : creal_scope.
Notation "0" := (0 %:CR)%CR : creal_scope.

Notation "<%CR" := lt_creal : creal_scope.
Notation "x < y" := (lt_creal x y) : creal_scope.

Notation "<=%CR" := le_creal : creal_scope.
Notation "x <= y" := (le_creal x y) : creal_scope.

Notation "-%CR" := opp_creal : creal_scope.
Notation "- x" := (opp_creal x) : creal_scope.

Notation "+%CR" := add_creal : creal_scope.
Notation "x + y" := (add_creal x y) : creal_scope.
Notation "x - y" := (x + - y)%CR : creal_scope.

Notation "*%CR" := mul_creal : creal_scope.
Notation "x * y" := (mul_creal x y) : creal_scope.

Notation "x_neq0 ^-1" := (inv_creal x_neq0) : creal_scope.
Notation "x / y_neq0" := (x * (y_neq0 ^-1))%CR : creal_scope.
Notation "p .[ x ]" := (horner_creal p x) : creal_scope.
Notation "p .[ x , y ]" := (horner2_creal p x y)
  (at level 2, left associativity) : creal_scope.
Notation "x ^+ n" := (exp_creal x n) : creal_scope.

Notation "`| x |" := (norm_creal x) : creal_scope.

Hint Resolve eq_creal_refl.
Hint Resolve le_creal_refl.

Notation lbound_of p := (@lboundP _ _ _ p _ _ _).
Notation lbound0_of p := (@lbound0P _ _ p _ _ _).
Notation diff_of p := (@diffP _ _ _ p _ _ _).
Notation diff0_of p := (@diff0P _ _ p _ _ _).

Notation "{ 'asympt' e : i / P }" := (asympt1 (fun e i => P))
  (at level 0, e ident, i ident, format "{ 'asympt'  e  :  i  /  P }") : type_scope.
Notation "{ 'asympt' e : i j / P }" := (asympt2 (fun e i j => P))
  (at level 0, e ident, i ident, j ident, format "{ 'asympt'  e  :  i  j  /  P }") : type_scope.

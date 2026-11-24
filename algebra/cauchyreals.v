(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From Corelib Require Setoid.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice perm.
From mathcomp Require Import seq fintype bigop binomial near sets order nmodule.
From mathcomp Require Import monoid orderedzmod numeric_hierarchy.
From mathcomp Require Import rings_modules_and_algebras divalg.
From mathcomp Require Import poly polydiv polyXY matrix mxpoly rat ssrint.
From mathcomp Require Import intdiv archimedean arithmetic_tactic.

(***************************************************************************)
(* This is a standalone construction of Cauchy reals over an arbitrary     *)
(* discrete archimedian field R.                                           *)
(*   creals R == setoid of Cauchy sequences, it does not have decidable    *)
(*               equality thus cannot be equipped with any HB structure    *)
(***************************************************************************)

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

(* remove the line when requiring MathComp >= 2.6 *)
Unset SsrOldRewriteGoalsOrder. 
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "{ 'asympt' e : i / P }"
  (at level 0, e name, i name, format "{ 'asympt'  e  :  i  /  P }").
Reserved Notation "{ 'asympt' e : i j / P }"
  (at level 0, e name, i name, j name, format "{ 'asympt'  e  :  i  j  /  P }").

Declare Scope creal_scope.
Delimit Scope creal_scope with CR.

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

Lemma poly_boundP (p : {poly F}) (a r x : F) : `|x - a| <= r ->
  `|p.[x]| <= poly_bound p a r.
Proof.
have [r_ge0|r_lt0] := lerP 0 r; last first.
  by move=> hr; have := le_lt_trans hr r_lt0; rewrite normr_lt0.
rewrite ler_distl=> /andP[lx ux].
rewrite ler_wpDl //.
elim/poly_ind: p=> [|p c ihp].
  by rewrite horner0 normr0 size_poly0 big_ord0.
rewrite hornerMXaddC size_MXaddC.
have [->|p_neq0 /=] := altP eqP.
  rewrite horner0 !mul0r !add0r size_poly0.
  have [->|c_neq0] /= := altP eqP; first by rewrite normr0 big_ord0.
  rewrite big_ord_recl big_ord0 addr0 coefC /=.
  by rewrite ler_pMr ?normr_gt0 // lerDl ler_maxr !normr_ge0.
rewrite big_ord_recl coefD coefMX coefC eqxx add0r.
rewrite (le_trans (ler_normD _ _)) // addrC lerD //.
  by rewrite expr0 mulr1.
rewrite normrM.
move: ihp=> /(ler_wpM2r (normr_ge0 x)) /le_trans-> //.
rewrite mulr_suml ler_sum // => i _.
rewrite coefD coefC coefMX /= addr0 exprSr mulrA.
rewrite ler_wpM2l //.
  by rewrite ?mulr_ge0 ?exprn_ge0 ?ler_maxr ?addr_ge0 ?normr_ge0 // ltrW.
rewrite (ger0_norm r_ge0) ler_norml opprD.
rewrite (le_trans _ lx) ?(le_trans ux) // lerD2r.
  by rewrite lerNl ler_normr lexx orbT.
by rewrite ler_normr lexx.
Qed.

Lemma poly_bound_gt0 p a r : 0 < poly_bound p a r.
Proof.
rewrite ltr_wpDr // sumr_ge0 // => i _.
by rewrite mulr_ge0 ?exprn_ge0 ?addr_ge0 ?ler_maxr ?normr_ge0 // ltrW.
Qed.

Lemma poly_bound_ge0 p a r : 0 <= poly_bound p a r.
Proof. by rewrite ltW // poly_bound_gt0. Qed.

Definition poly_accr_bound (p : {poly F}) (a r : F) : F
  := (Num.max 1 (2 * r)) ^+ (size p).-1
  * (1 + \sum_(i < (size p).-1) poly_bound p^`N(i.+1) a r).

Lemma poly_accr_bound1P p a r x y :
  `|x - a| <= r -> `|y - a| <= r ->
  `|p.[y] - p.[x]| <= `|y - x| * poly_accr_bound p a r.
Proof.
have [|r_lt0] := lerP 0 r; last first.
  by move=> hr; have := le_lt_trans hr r_lt0; rewrite normr_lt0.
rewrite le0r=> /orP[/eqP->|r_gt0 hx hy].
  by rewrite !normr_le0 !subr_eq0=> /eqP-> /eqP->; rewrite !subrr normr0 mul0r.
rewrite mulrA mulrDr mulr1 ler_wpDl ?mulr_ge0 ?normr_ge0 //=.
  by rewrite exprn_ge0 ?le_max ?mulr_ge0 ?ger0E ?ltW.
rewrite -{1}(addNKr x y) [- _ + _]addrC /= -mulrA.
rewrite nderiv_taylor; first exact: mulrC.
have [->|p_neq0] := eqVneq p 0.
  rewrite size_poly0 big_ord0 horner0 subr0 normr0 mulr_ge0 ?normr_ge0 //.
  by rewrite big_ord0 mulr0 lexx.
rewrite -[size _]prednK ?lt0n ?size_poly_eq0 //.
rewrite big_ord_recl expr0 mulr1 nderivn0 [X in `|X|]addrC addKr !mulr_sumr.
have := le_trans (ler_norm_sum _ _ _); apply.
rewrite ler_sum // => i _.
rewrite exprSr mulrA !normrM mulrC ler_wpM2l ?normr_ge0 //.
suff /ler_wpM2l /le_trans :
  `|(y - x) ^+ i| <=  Num.max 1 (2 * r) ^+ (size p).-1.
  apply; rewrite ?normr_ge0 // mulrC ler_wpM2l ?poly_boundP //.
  by rewrite ?exprn_ge0 // le_max ler01 mulr_ge0 ?ler0n ?ltW.
case: (leP _ 1)=> hr.
  rewrite expr1n normrX exprn_ile1 ?normr_ge0 //.
  rewrite (le_trans (ler_distD a _ _)) // addrC distrC.
  by rewrite (le_trans _ hr) // mulrDl lerD ?mul1r.
apply: le_trans (_ : (2 * r) ^+ i <= _).
  rewrite normrX lerXn2r -?topredE /= ?normr_ge0 ?mulr_ge0 ?ler0n //.
    by rewrite ltW.
  rewrite (le_trans (ler_distD a _ _)) // addrC distrC.
  by rewrite mulrDl lerD ?mul1r.
by rewrite ler_eXn2l // ltnW.
Qed.

Lemma poly_accr_bound_gt0 p a r : 0 < poly_accr_bound p a r.
Proof.
rewrite /poly_accr_bound pmulr_rgt0 //.
  by rewrite exprn_gt0 // lt_max ltr01 pmulr_rgt0 ?ltr0n.
rewrite ltr_wpDr ?ltr01 //.
by rewrite sumr_ge0 // => i; rewrite poly_bound_ge0.
Qed.

Lemma poly_accr_bound_ge0 p a r : 0 <= poly_accr_bound p a r.
Proof. by rewrite ltW // poly_accr_bound_gt0. Qed.

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
  by rewrite -!lead_coefE normr_eq0 !lead_coef_eq0.
by rewrite -lead_coefE size_poly_eq0 lead_coef_eq0.
Qed.

End polyXY_order_extra.

Section polyorder_field_extra.

Variable F : realFieldType.

Local Open Scope ring_scope.

Definition poly_accr_bound2 (p : {poly F}) (a r : F) : F
  := (Num.max 1 (2 * r)) ^+ (size p).-2
  * (1 + \sum_(i < (size p).-2) poly_bound p^`N(i.+2) a r).

Lemma poly_accr_bound2_gt0 p a r : 0 < poly_accr_bound2 p a r.
Proof.
rewrite /poly_accr_bound pmulr_rgt0 //.
  by rewrite exprn_gt0 // lt_max ltr01 pmulr_rgt0 ?ltr0n.
rewrite ltr_wpDr ?ltr01 //.
by rewrite sumr_ge0 // => i; rewrite poly_bound_ge0.
Qed.

Lemma poly_accr_bound2_ge0 p a r : 0 <= poly_accr_bound2 p a r.
Proof. by rewrite ltW // poly_accr_bound2_gt0. Qed.

Lemma poly_accr_bound2P p (a r x y : F) : (x != y)%B ->
  `|x - a| <= r ->  `|y - a| <= r ->
  `|(p.[y] - p.[x]) / (y - x) - p^`().[x]|
    <= `|y - x| * poly_accr_bound2 p a r.
Proof.
have [|r_lt0] := lerP 0 r; last first.
  by move=> _ hr; have := le_lt_trans hr r_lt0; rewrite normr_lt0.
rewrite le0r=> /orP[/eqP->|r_gt0].
  rewrite !normr_le0 !subr_eq0.
  by move=> nxy /eqP xa /eqP xb; rewrite xa xb eqxx in nxy.
move=> neq_xy hx hy.
rewrite mulrA mulrDr mulr1 ler_wpDl ?mulr_ge0 ?normr_ge0 //=.
  by rewrite exprn_ge0 ?le_max ?mulr_ge0 ?ger0E ?ltW.
rewrite -{1}(addNKr x y) [- _ + _]addrC /= -mulrA.
rewrite nderiv_taylor; first exact: mulrC.
have [->|p_neq0] := eqVneq p 0.
  by rewrite derivC !horner0 size_poly0 !(big_ord0, subrr, mul0r) normr0 !mulr0.
rewrite -[size _]prednK ?lt0n ?size_poly_eq0 //.
rewrite big_ord_recl expr0 mulr1 nderivn0 /= -size_deriv.
have [->|p'_neq0] := eqVneq p^`() 0.
  by rewrite horner0 size_poly0 !big_ord0 addr0 !(subrr, mul0r) normr0 !mulr0.
rewrite -[size _]prednK ?lt0n ?size_poly_eq0 // big_ord_recl expr1.
rewrite addrAC subrr add0r mulrDl mulfK; first by rewrite subr_eq0 eq_sym.
rewrite nderivn1 addrAC subrr add0r mulr_sumr normrM normfV.
rewrite ler_pdivrMr ?normr_gt0; first by rewrite subr_eq0 eq_sym.
rewrite mulrAC -expr2 mulrC mulr_suml.
have := le_trans (ler_norm_sum _ _ _); apply.
rewrite ler_sum // => i _ /=; rewrite /bump /= !add1n.
rewrite normrM normrX 3!exprSr expr1 !mulrA !ler_wpM2r ?normr_ge0 //.
suff /ler_wpM2l /le_trans :
  `|(y - x)| ^+ i <= Num.max 1 (2 * r) ^+ (size p^`()).-1.
  apply; rewrite ?normr_ge0 // mulrC ler_wpM2l ?poly_boundP //.
  by rewrite ?exprn_ge0 // le_max ler01 mulr_ge0 ?ler0n ?ltW.
case: (leP _ 1)=> hr.
  rewrite expr1n exprn_ile1 ?normr_ge0 //.
  rewrite (le_trans (ler_distD a _ _)) // addrC distrC.
  by rewrite (le_trans _ hr) // mulrDl lerD ?mul1r.
apply: le_trans (_ : (2 * r) ^+ i <= _).
  rewrite lerXn2r -?topredE /= ?normr_ge0 ?mulr_ge0 ?ler0n //.
    by rewrite ltW.
  rewrite (le_trans (ler_distD a _ _)) // addrC distrC.
  by rewrite mulrDl lerD ?mul1r.
by rewrite ler_eXn2l // ltnW.
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
have [->|neq_xy] := eqVneq x y; first by rewrite !lexx.
have hkxy := hk _ _ neq_xy hx hy.
have := lt_trans k_gt0 hkxy.
have [lpxpy|lpypx|->] := ltrgtP p.[x] p.[y].
+ by rewrite nmulr_rgt0 ?subr_lt0 // ?invr_lt0 subr_lt0=> /ltW->.
+ by rewrite pmulr_rgt0 ?subr_gt0 // ?invr_gt0 subr_gt0 leNgt=> ->.
by rewrite subrr mul0r ltxx.
Qed.

Lemma accr_neg_decr p a r : accr_neg p a r ->
  forall x y, `|x - a| <= r -> `|y - a| <= r -> (p.[x] <= p.[y]) = (y <= x).
Proof.
move=> [] [k]; rewrite -oppr_lt0=> Nk_lt0 hk _ x y hx hy.
have [->|neq_xy] := eqVneq x y; first by rewrite !lexx.
have hkxy := hk _ _ neq_xy hx hy.
have := lt_trans hkxy  Nk_lt0.
have [lpxpy|lpypx|->] := ltrgtP p.[x] p.[y].
+ by rewrite nmulr_rlt0 ?subr_lt0 // ?invr_gt0 subr_gt0=> /ltW->.
+ by rewrite pmulr_rlt0 ?subr_gt0 // ?invr_lt0 subr_lt0 leNgt=> ->.
by rewrite subrr mul0r ltxx.
Qed.

Lemma accr_negN p a r : accr_pos p a r -> accr_neg (- p) a r.
Proof.
case=> [[k k_gt0 hk] h].
split; [ exists k=> // x y nxy hx hy;
    by rewrite !hornerN -opprD mulNr ltrN2; apply: hk
  | by move=> x hx; rewrite derivN hornerN oppr_lt0; apply: h ].
Qed.

Lemma accr_posN p a r : accr_neg p a r -> accr_pos (- p) a r.
Proof.
case=> [[k k_gt0 hk] h].
split; [ exists k=> // x y nxy hx hy;
    by rewrite !hornerN -opprD mulNr ltrNr; apply: hk
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
move: (hk _ _ neq_xy hx hy); rewrite 1?ltrNr ler_pdivlMl //;
rewrite -ler_pdivlMr ?normr_gt0 ?subr_eq0 // => /ltW /le_trans-> //;
by rewrite -normfV -normrM ler_normr lexx ?orbT.
Qed.

Definition merge_intervals (ar1 ar2 : F * F) :=
  let l := Num.min (ar1.1 - ar1.2) (ar2.1 - ar2.2) in
  let u := Num.max (ar1.1 + ar1.2) (ar2.1 + ar2.2) in
    ((l + u) / 2, (u - l) / 2).
Local Notation center ar1 ar2 := ((merge_intervals ar1 ar2).1).
Local Notation radius ar1 ar2 := ((merge_intervals ar1 ar2).2).

Lemma split_interval (a1 a2 r1 r2 x : F) :
  0 < r1 -> 0 < r2 ->  `|a1 - a2| <= r1 + r2 ->
  (`|x - center (a1, r1) (a2, r2)| <= radius (a1, r1) (a2, r2))
  =  (`|x - a1| <= r1) || (`|x - a2| <= r2).
Proof.
move=> r1_gt0 r2_gt0 le_ar.
rewrite /merge_intervals /=.
set l : F := Num.min _ _; set u : F := Num.max _ _.
rewrite ler_pdivlMr ?gtr0E // -{2}[2]ger0_norm ?ger0E //.
rewrite -normrM mulrBl mulfVK ?pnatr_eq0 // ler_distl.
rewrite opprB addrCA addrK (addrC (l + u)) addrA addrNK.
rewrite -!mulr2n !mulr_natr !lerMn2r !orFb.
rewrite ge_min le_max !ler_distl /=.
have [] := lerP=> /= a1N; have [] := lerP=> //= a1P;
have [] := lerP=> //= a2P; rewrite ?(andbF, andbT) //; symmetry.
  rewrite ltW // (le_lt_trans _ a1P) //.
  rewrite (monoLR (addrK _) (lerD2r _)) -addrA.
  rewrite (monoRL (addNKr _) (lerD2l _)) [leLHS]addrC.
  by rewrite (le_trans _ le_ar) // ler_normr opprB lexx orbT.
rewrite ltW // (lt_le_trans a1N) //.
rewrite (monoLR (addrK _) (lerD2r _)) -addrA.
rewrite (monoRL (addNKr _) (lerD2l _)) [leRHS]addrC [leLHS]addrC.
by rewrite (le_trans _ le_ar) // ler_normr lexx.
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
  suff: 0 < 0 :> F by rewrite ltxx.
  have r_gt0 : 0 < r1 + r2 by rewrite ?addr_gt0.
  apply: (lt_trans (pm_gt0 _) (pm_lt0 _)).
    rewrite -(@ler_pM2l _ (r1 + r2)) //.
    rewrite -{1}[r1 + r2]ger0_norm ?(ltW r_gt0) //.
    rewrite -normrM mulrBr /m mulrC mulrVK ?unitfE ?gt_eqF //.
    rewrite mulrDl opprD addrA addrC addrA addKr.
    rewrite distrC -mulrBr normrM ger0_norm ?(ltW r1_gt0) //.
    by rewrite mulrC ler_wpM2r // ltW.
  rewrite -(@ler_pM2l _ (r1 + r2)) //.
  rewrite -{1}[r1 + r2]ger0_norm ?(ltW r_gt0) //.
  rewrite -normrM mulrBr /m mulrC mulrVK ?unitfE ?gt_eqF //.
  rewrite mulrDl opprD addrA addrK.
  rewrite -mulrBr normrM ger0_norm ?(ltW r2_gt0) //.
  by rewrite mulrC ler_wpM2r // ltW.
case: accr2_p=> [[k2 k2_gt0 hk2]] h2.
left; split; last by move=> x; rewrite split_interval // => /orP [/h1|/h2].
exists (Num.min k1 k2); first by rewrite lt_min k1_gt0.
move=> x y neq_xy; rewrite !split_interval //.
wlog lt_xy: x y neq_xy / y < x.
  move=> hwlog; have [] := ltrP y x; first exact: hwlog.
  rewrite le_eqVlt (negPf neq_xy) /= => /hwlog hwlog' hx hy.
  rewrite -mulrNN -!invrN !opprB.
  by apply: hwlog'; rewrite // eq_sym.
move=> {h1} {h2} {sm1}.
wlog le_xr1 : a1 a2 r1 r2 k1 k2
  r1_gt0 r2_gt0 k1_gt0 k2_gt0 har hk1 hk2  / `|x - a1| <= r1.
  move=> hwlog h; move: (h)=> /orP [/hwlog|]; first exact.
  move=> /(hwlog a2 a1 r2 r1 k2 k1) hwlog' ley; rewrite minC.
  by apply: hwlog'; rewrite 1?orbC // distrC [r2 + _]addrC.
move=> _.
have [le_yr1|gt_yr1] := (lerP _ r1)=> /= [_|le_yr2].
  by rewrite gt_min hk1.
rewrite ltr_pdivlMr ?subr_gt0 //.
pose z := a1 - r1.
have hz1 : `|z - a1| <= r1 by rewrite addrC addKr normrN gtr0_norm.
have gt_yr1' : y + r1 < a1.
  rewrite addrC; move: gt_yr1.
  rewrite (monoLR (addrNK _) (ltrD2r _)).
 rewrite /z ltr_normr opprB=> /orP[|-> //].
  rewrite (monoRL (addrK a1) (ltrD2r _))=> /lt_trans /(_ lt_xy).
  by rewrite ltNge addrC; move: le_xr1; rewrite ler_distl=> /andP [_ ->].
have lt_yz : y < z by rewrite (monoRL (addrK _) (ltrD2r _)).
have hz2 : `|z - a2| <= r2.
  move: (har); rewrite ler_norml=> /andP [la ua].
  rewrite addrAC ler_distl ua andbT.
  rewrite -[a1](addrNK y) -[_ - _ + _ - _]addrA.
  rewrite lerD //.
    by rewrite (monoRL (addrK _) (lerD2r _)) addrC ltW.
  by move: le_yr2; rewrite ler_norml=> /andP[].
have [<-|neq_zx] := eqVneq z x.
  by rewrite -ltr_pdivlMr ?subr_gt0 // gt_min hk2 ?orbT // gt_eqF.
have lt_zx : z < x.
  rewrite lt_neqAle neq_zx /=.
  move: le_xr1; rewrite distrC ler_norml=> /andP[_].
  by rewrite !(monoLR (addrK _) (lerD2r _)) addrC.
rewrite -{1}[x](addrNK z) -{1}[p.[x]](addrNK p.[z]).
rewrite !addrA -![_ - _ + _ - _]addrA mulrDr ltrD //.
  rewrite -ltr_pdivlMr ?subr_gt0 //.
  by rewrite gt_min hk1 ?gt_eqF.
rewrite -ltr_pdivlMr ?subr_gt0 //.
by rewrite gt_min hk2 ?orbT ?gt_eqF.
Qed.

End monotony.

Section CauchyReals.

Local Open Scope creal_scope.
Local Open Scope ring_scope.
Local Open Scope near_scope.

Definition asympt1 (R : numDomainType) (P : R -> nat -> Prop) :=
  forall eps, 0 < eps -> \forall i \near \oo, P eps i.

Definition asympt2 (R : numDomainType) (P : R -> nat -> nat -> Prop) :=
  forall eps, 0 < eps -> \forall i \near \oo & j \near \oo, P eps i j.

Definition asympt2_sig (R : numDomainType) (P : R -> nat -> nat -> Prop) :=
  {m : R -> nat | forall eps i j, 0 < eps -> (m eps <= i)%N -> (m eps <= j)%N -> P eps i j}.

Lemma asympt2_sig_is_near (R : numDomainType) (P : R -> nat -> nat -> Prop) :
  asympt2_sig P -> asympt2 P.
Proof.
move=> [m /= mP] e e0.
near=> n.
apply: mP => //.
- near: n.
  exists ([set i | m e <= i]%N, [set j | m e <= j]%N).
    by split; exact: nbhs_infty_ge.
  by move=> [n1 n2]/= [].
- near: n.
  exists ([set i | m e <= i]%N, [set j | m e <= j]%N).
    by split; exact: nbhs_infty_ge.
  by move=> [n1 n2]/= [].
Unshelve. all: by end_near. Qed.

Local Notation "{ 'asympt' e : i / P }" :=
  (asympt1 (fun e i => P)) : type_scope.

Local Notation "{ 'asympt' e : i j / P }" :=
  (asympt2 (fun e i j => P)) : type_scope.

Local Open Scope creal_scope.
Local Open Scope ring_scope.

Variable F : realFieldType.

Lemma asymptP (P1 : F -> nat -> Prop) (P2 : F -> nat -> Prop) :
  (forall e i, 0 < e -> P1 e i -> P2 e i) ->
  {asympt e : i / P1 e i} -> {asympt e : i / P2 e i}.
Proof. by move=> hP h e e0; apply: filterS (h _ e0) => t; exact: hP. Qed.

Lemma splitf (n : nat) (e : F) : e = iterop n +%R (e / n%:R) e.
Proof.
case: n=> // n; set e' := (e / _).
have -> : e = e' * n.+1%:R by rewrite mulfVK ?pnatr_eq0.
move: e'=> {}e; rewrite iteropS.
by elim: n=> /= [|n <-]; rewrite !mulr_natr ?mulr1n.
Qed.

Lemma splitD (x y e : F) : x < e / 2 -> y < e / 2 -> x + y < e.
Proof. by move=> hx hy; rewrite [e](splitf 2) ltrD. Qed.

Lemma divrn_gt0 (e : F) (n : nat) : 0 < e -> (0 < n)%N -> 0 < e / n%:R.
Proof. by move=> e_gt0 n_gt0; rewrite pmulr_rgt0 ?gtr0E. Qed.

Lemma split_norm_add (x y e : F) :
  `|x| < e / 2 -> `|y| < e / 2 -> `|x + y| < e.
Proof. by move=> hx hy; rewrite (le_lt_trans (ler_normD _ _)) // splitD. Qed.

Lemma split_norm_sub (x y e : F) :
  `|x| < e / 2 -> `|y| < e / 2 -> `|x - y| < e.
Proof. by move=> hx hy; rewrite (le_lt_trans (ler_normB _ _)) // splitD. Qed.

Lemma split_dist_add (z x y e : F) :
  `|x - z| < e / 2 -> `|z - y| < e / 2 -> `|x - y| < e.
Proof.
by move=> *; rewrite (le_lt_trans (ler_distD z _ _)) ?splitD // 1?distrC.
Qed.

Definition creal_axiom (x : nat -> F) := {asympt e : i j / `|x i - x j| < e}.

Definition creal_axiom_sig (x : nat -> F) := asympt2_sig (fun e i j => `|x i - x j| < e).

Record creal := CReal {
  cauchyseq :> nat -> F;
  spec_cauchy : creal_axiom_sig cauchyseq }.
Bind Scope creal_scope with creal.

Definition cauchymod (x : creal) : F -> nat := projT1 (spec_cauchy x).

Lemma cauchymodP (x : creal) eps i j : 0 < eps ->
  (cauchymod x eps <= i)%N -> (cauchymod x eps <= j)%N -> `|x i - x j| < eps.
Proof. exact: (projT2 (spec_cauchy x)). Qed.

Lemma crealP (x : creal) : creal_axiom x.
Proof. by apply: asympt2_sig_is_near; case: x. Qed.

Lemma crealP_near (x : creal) e : 0 < e ->
  \forall i \near \oo, \forall k \near \oo, `|x i - x k| < e.
Proof. by move=> e0; apply: near_prod_nears => //; exact/crealP. Qed.


Definition neq_creal (x y : creal) : Prop :=
  exists2 e, 0 < e & \forall i \near \oo, e <= `|x i - y i|.
Notation "!=%CR" := neq_creal : creal_scope.
Notation "x != y" := (neq_creal x  y) : creal_scope.

Definition eq_creal x y := (~ (x != y)%CR).
Notation "x == y" := (eq_creal x y) : creal_scope.

Lemma ltr_distl_creal (e : F) (x : creal) (a b : F) : 0 < e ->
  \forall i \near \oo & j \near \oo, `|x i - a| <= b - e -> `|x j - a| < b.
Proof.
move=> e_gt0; apply: filterS (crealP x e_gt0) => -[i j] /= hij hb.
apply: le_lt_trans (ler_distD (x i) _ _) _.
by rewrite [_ + `|_ - a|]addrC -[b](subrK e) ler_ltD // distrC.
Qed.

Lemma cst_crealP (x : F) : creal_axiom_sig (fun => x).
Proof.
by exists (fun=> 0%N) => /= e i j e0 i0 j0; rewrite subrr normr0.
Defined.

Definition cst_creal (x : F) := CReal (cst_crealP x).

Notation "x %:CR" := (cst_creal x)
  (at level 1, left associativity, format "x %:CR") : creal_scope.
Notation "0" := (0 %:CR) : creal_scope.

Lemma neq_crealP e i j (e_gt0 : 0 < e) (x y : creal) :
  (\forall k \near \oo, `|x i - x k| < e / 5) ->
  (\forall k \near \oo, `|y j - y k| < e / 5) ->
  e <= `|x i - y j| -> x != y.
Proof.
move=> hi hj he; exists (e / 5); first by rewrite divr_gt0.
near=> k.
have [hxk hyk] : `|x i - x k| < e / 5 /\ `|y j - y k| < e / 5 by split; near: k.
have tri : `|x i - y j| <= `|x i - x k| + `|x k - y k| + `|y k - y j|.
  by rewrite -addrA (le_trans (ler_distD (x k) _ _))// lerD2l ler_distD.
rewrite distrC in hyk.
lra.
Unshelve. all: by end_near. Qed.

Lemma eq_crealP (x y : creal) : {asympt e : i / `|x i - y i| < e} ->
  (x == y)%CR.
Proof.
move=> h [d d0 hd].
near \oo => j.
have : d <= `|x j - y j| by near: j.
by rewrite leNgt => /negP; apply; near: j; exact: (h _ d0).
Unshelve. all: by end_near. Qed.

Lemma eq0_crealP (x : creal) : {asympt e : i / `|x i| < e} -> x == 0.
Proof.
by move=> hx; apply: eq_crealP; apply: asymptP hx=> e i; rewrite subr0.
Qed.

Lemma asympt_eq (x y : creal) (eq_xy : x == y) :
  {asympt e : i / `|x i - y i| < e}.
Proof.
move=> e e0; near=> i.
rewrite ltNge; apply/negP => he; apply: eq_xy.
by apply: (@neq_crealP e i i e0 x y _ _ he) => {he};
  near: i; apply: crealP_near; rewrite divr_gt0.
Unshelve. all: by end_near. Qed.

Lemma asympt_eq0 (x : creal) : x == 0 -> {asympt e : i / `|x i| < e}.
Proof. by move/asympt_eq; apply: asymptP=> e i; rewrite subr0. Qed.

Lemma eq_creal_refl x : x == x.
Proof.
by apply: eq_crealP => e e0; near=> i; rewrite subrr normr0.
Unshelve. all: end_near. Qed.
Hint Resolve eq_creal_refl : core.

Lemma neq_creal_sym x y : x != y -> y != x.
Proof.
move=> [d d0 hd]; exists d => //.
near=> i; rewrite distrC; near: i; exact: hd.
Unshelve. all: by end_near. Qed.

Lemma eq_creal_sym x y : x == y -> y == x.
Proof. by move=> eq_xy /neq_creal_sym. Qed.

Lemma eq_creal_trans x y z : x == y -> y == z -> x == z.
Proof.
move=> eq_xy eq_yz; apply: eq_crealP => e e0; near=> i.
by rewrite (@split_dist_add (y i))//;
  near: i; apply: asympt_eq => //; rewrite divr_gt0.
Unshelve. all: end_near. Qed.

Lemma creal_neq_always (x y : creal) (neq_xy : x != y) :
  \forall i \near \oo, (x i != y i)%B.
Proof.
case: neq_xy => d d0 hd.
by near do rewrite -subr_eq0 -normr_gt0 (lt_le_trans d0)//.
Unshelve. all: by end_near. Qed.

Definition creal_neq0_always (x : creal) := @creal_neq_always x 0.

Definition lt_creal (x y : creal) : Prop :=
  exists2 e, 0 < e & \forall i \near \oo, x i + e <= y i.
Notation "<%CR" := lt_creal : creal_scope.
Notation "x < y" := (lt_creal x y) : creal_scope.

Definition le_creal (x y : creal) : Prop := ~ (y < x)%CR.
Notation "<=%CR" := le_creal : creal_scope.
Notation "x <= y" := (le_creal x y) : creal_scope.

Lemma ltr_creal (e : F) (x : creal) (a : F) : 0 < e ->
  \forall i \near \oo, \forall j \near \oo, x i <= a - e -> x j < a.
Proof.
move=> e_gt0; apply: (filterS _ (crealP_near x e_gt0)) => i.
apply/filterS => j + ha.
rewrite distrC ltr_distl => /andP[_ /lt_le_trans-> //].
by rewrite -(lerD2r (- e)) addrK.
Qed.

Lemma gtr_creal (e : F) (x : creal) (a : F) : 0 < e ->
  \forall i \near \oo, \forall j \near \oo, a + e <= x i -> a < x j.
Proof.
move=> e_gt0; apply: (filterS _ (crealP_near x e_gt0)) => i.
apply/filterS => j + ha.
rewrite distrC ltr_distl => /andP[/(le_lt_trans _)-> //].
by rewrite -(lerD2r e) addrNK.
Qed.

Lemma lt_crealP e i j (e_gt0 : 0 < e) (x y : creal) :
  (\forall k \near \oo, `|x i - x k| < e / 5) ->
  (\forall k \near \oo, `|y j - y k| < e / 5) ->
  x i + e <= y j -> (x < y)%CR.
Proof.
move=> hi hj he; exists (e / 5); first by rewrite divr_gt0.
have h5 : e / 5 *+ 3 <= e.
  rewrite -[leRHS](@divfK _ 5) ?pnatr_eq0 // -mulr_natr.
  by rewrite ler_pM2l ?divr_gt0 // ler_nat.
have h3 : x i + e / 5 *+ 3 <= y j by rewrite (le_trans _ he) // lerD2l.
near=> k.
have [hxk hyk] : `|x i - x k| < e / 5 /\ `|y j - y k| < e / 5.
  by split; near: k.
move: hxk; rewrite distrC ltr_distl => /andP[_ hx].
move: hyk; rewrite ltr_distl => /andP[_ hy].
apply: ltW.
have : x k + e / 5 < x i + e / 5 *+ 2 by rewrite mulr2n addrA ltrD2r.
move/lt_le_trans; apply.
by rewrite -(lerD2r (e / 5)) -addrA -mulrSr (le_trans h3)// ltW.
Unshelve. all: by end_near. Qed.

Lemma le_crealP i (x y : creal) :
  (forall j, (i <= j)%N -> x j <= y j) -> (x <= y)%CR.
Proof.
move=> hi [d d0 hd]; near \oo => j.
have hj : y j + d <= x j by near: j.
have := hi j; rewrite leNgt => /(_ _)/negP; apply.
  by near: j.
by rewrite (lt_le_trans _ hj) // ltrDl.
Unshelve. all: by end_near. Qed.

Lemma le_creal_refl (x : creal) : (x <= x)%CR.
Proof. exact: (@le_crealP 0%N). Qed.
Hint Resolve le_creal_refl : core.

Lemma lt_neq_creal (x y : creal) : (x < y)%CR -> x != y.
Proof.
move=> [d d0 hd]; exists d => //.
by near do rewrite distrC (le_trans _ (ler_norm _))// lerBrDr addrC.
Unshelve. all: by end_near. Qed.

Lemma creal_lt_always (x y : creal) (lt_xy : (x < y)%CR) :
  \forall i \near \oo, x i < y i.
Proof.
case: lt_xy => d d0 hd.
by near do rewrite (@lt_le_trans _ _ ( x i + d)) ?ltrDl//.
Unshelve. all: by end_near. Qed.

Definition creal_gt0_always := @creal_lt_always 0.

Lemma eq_le_creal (x y : creal) : x == y -> (x <= y)%CR.
Proof. by move=> /eq_creal_sym ? /lt_neq_creal. Qed.

Lemma asympt_le (x y : creal) (le_xy : (x <= y)%CR) :
  {asympt e : i / x i < y i + e}.
Proof.
move=> e e0; near=> i.
rewrite ltNge; apply/negP => he; apply: le_xy.
by apply: (@lt_crealP _ i i e0 y x) => //;
  near: i; apply: crealP_near; rewrite divr_gt0.
Unshelve. all: by end_near. Qed.

Lemma asympt_ge0 (x : creal) : (0 <= x)%CR -> {asympt e : i / - e < x i}.
Proof. by move/asympt_le; apply: asymptP=> *; rewrite -subr_gt0 opprK. Qed.

Lemma opp_crealP (x : creal) : creal_axiom_sig (fun i => - x i).
Proof.
exists (cauchymod x) => e i j e0 hi hj.
by rewrite -opprD normrN cauchymodP.
Defined.
Definition opp_creal (x : creal) := CReal (opp_crealP x).
Notation "-%CR" := opp_creal : creal_scope.
Notation "- x" := (opp_creal x) : creal_scope.

Lemma add_crealP (x y : creal) : creal_axiom_sig (fun i => x i + y i).
Proof.
exists (fun e => maxn (cauchymod x (e / 2)) (cauchymod y (e / 2)))=> e i j e0.
rewrite !geq_max => /andP[xi yi] /andP[xj yj].
by rewrite opprD addrACA split_norm_add ?cauchymodP ?divr_gt0.
Defined.
Definition add_creal (x y : creal) := CReal (add_crealP x y).
Notation "+%CR" := add_creal : creal_scope.
Notation "x + y" := (add_creal x y) : creal_scope.
Notation "x - y" := (x + - y)%CR : creal_scope.

Lemma ubound_subproof_sig (x : creal) : {b : F | b > 0 & forall i, `|x i| <= b}.
Proof.
set i := cauchymod x 1.
have xi : (cauchymod x 1 <= i)%N by [].
move: i => i in xi *.
set b := 1 + `|x i|.
exists (foldl Num.max b [seq `|x n| | n <- iota 0 i]) => [|n].
  have : 0 < b by rewrite ltr_pwDl.
  by elim: iota b => //= a l IHl b b_gt0; rewrite IHl ?lt_max ?b_gt0.
have [|le_in] := ltnP n i.
  elim: {xi} i b => [|i IHi] b //.
  rewrite ltnS -addn1 iotaD add0n map_cat foldl_cat /= le_max leq_eqVlt.
  by case/predU1P => [->|/IHi->] //; rewrite lexx orbT.
set xn := `|x n|; suff : xn <= b.
  by elim: iota xn b => //= a l IHl xn b Hxb; rewrite IHl ?le_max ?Hxb.
rewrite -lerBlDr (le_trans (ler_norm _))//.
by rewrite (le_trans (ler_dist_dist _ _)) ?ltW ?cauchymodP// (leq_trans xi).
Defined.

Lemma ubound_subproof_ex (x : creal) : exists2 b, 0 < b & forall i, `|x i| <= b.
Proof. by have [b b0 xb] := ubound_subproof_sig x; exists b. Qed.

Lemma mul_crealP (x y : creal) : creal_axiom_sig (fun i => x i * y i).
Proof.
have [dx dx0 hbx] := ubound_subproof_sig x.
have [dy dy0 hby] := ubound_subproof_sig y.
exists (fun e => maxn (cauchymod x (e / 2 / dy)) (cauchymod y (e / 2 / dx))).
move=> e i j e0.
rewrite !geq_max => /andP[xi yi] /andP[xj yj].
rewrite -[_ * _]subr0 -(subrr (x j * y i)) opprD opprK addrA.
rewrite -mulrBl -addrA -mulrBr split_norm_add// !normrM.
  have /ler_wpM2l /le_lt_trans-> // := hby i.
  by rewrite -ltr_pdivlMr ?by0 ?cauchymodP// !pmulr_rgt0 ?invr_gt0 ?by0 ?ltr0n.
rewrite mulrC.
have /ler_wpM2l /le_lt_trans-> // := hbx j.
by rewrite -ltr_pdivlMr ?cauchymodP// !pmulr_rgt0 ?gtr0E.
Defined.
Definition mul_creal (x y : creal) := CReal (mul_crealP x y).
Notation "*%CR" := mul_creal : creal_scope.
Notation "x * y" := (mul_creal x y) : creal_scope.

Definition creal_2separated (x : creal) (dn : F * nat) : bool :=
  [&& (0 < dn.1), (cauchymod x dn.1 <= dn.2)%N & dn.1 *+ 2 <= `|x dn.2| ].

Lemma creal_2separated_ex (x : creal) : x != 0 ->
  exists dn : F * nat, creal_2separated x dn.
Proof.
move=> [D D0 hD].
have [M _ hM] : \forall i \near \oo, D <= `|x i|.
  by apply: filterS hD => i /=; rewrite subr0.
pose d := D / 2.
have d0 : 0 < d by rewrite /d divr_gt0.
pose N := maxn M (cauchymod x d).
exists (d, N).
rewrite /creal_2separated/= d0 leq_maxr/=.
by rewrite -mulr_natr divfK ?pnatr_eq0// hM//= leq_maxl.
Qed.

Lemma creal_2separatedW (x : creal) (d : F) (N i : nat) :
  creal_2separated x (d, N) -> (N <= i)%N -> d <= `|x i|.
Proof.
move=> /and3P[d0 hN hsep] hNi.
have : `| `|x N| - `|x i| | < d.
  by rewrite (le_lt_trans (ler_dist_dist _ _))// cauchymodP// (leq_trans hN).
rewrite ltr_distl => /andP[_ hupper].
by rewrite -(lerD2r d) ltW// (le_lt_trans _ hupper).
Qed.

Definition inv_crealP_subdef (x : creal) (x_neq0 : x != 0) :
  {dn : F * nat | creal_2separated x dn} := sigW (creal_2separated_ex x_neq0).

Lemma inv_crealP (x : creal) (x_neq0 : x != 0) :
  creal_axiom_sig (fun i => (x i)^-1).
Proof.
have [[d N] hsep] := inv_crealP_subdef x_neq0.
have /and3P[/= d0 _ _] := hsep.
exists (fun e => maxn N (cauchymod x (e * d ^+ 2))) => /= e i j e0.
rewrite !geq_max => /andP[hNi hci] /andP[hNj hcj].
have dxi : d <= `|x i| by exact: creal_2separatedW hsep hNi.
have dxj : d <= `|x j| by exact: creal_2separatedW hsep hNj.
have xi0 : (x i != 0)%B by rewrite -normr_gt0 (lt_le_trans d0 dxi).
have xj0 : (x j != 0)%B by rewrite -normr_gt0 (lt_le_trans d0 dxj).
rewrite -(@ltr_pM2r _ `|x i * x j|); first by rewrite normr_gt0 mulf_neq0.
rewrite -normrM !mulrBl mulrA mulVf // mulrCA mulVf // mul1r mulr1.
rewrite (@lt_le_trans _ _ (e * d ^+ 2))//.
- by rewrite distrC cauchymodP// mulr_gt0 ?exprn_gt0.
- by rewrite normrM ler_wpM2l ?(ltW e0)// expr2 ler_pM// ltW.
Defined.
Definition inv_creal (x : creal) (x_neq0 : x != 0) := CReal (inv_crealP x_neq0).
Notation "x_neq0 ^-1" := (inv_creal x_neq0) : creal_scope.
Notation "x / y_neq0" := (x * (y_neq0 ^-1))%CR : creal_scope.

Lemma norm_crealP (x : creal) : creal_axiom_sig (fun i => `|x i|).
Proof.
exists (cauchymod x) => /= e i j e0 hi hj.
by rewrite (le_lt_trans (ler_dist_dist _ _))// cauchymodP.
Defined.
Definition norm_creal (x : creal) := CReal (norm_crealP x).

Local Notation "`| x |" := (norm_creal x) : creal_scope.

Lemma horner_crealP (p : {poly F}) (x : creal) : creal_axiom_sig (fun i => p.[x i]).
Proof.
pose r := poly_accr_bound p (x (cauchymod x 1)) 1.
exists (fun e => maxn (cauchymod x 1) (cauchymod x (e / r))) => /= e i j e_gt0.
rewrite !geq_max => /andP[xi xei] /andP[xj xej].
rewrite (le_lt_trans (@poly_accr_bound1P _ p (x (cauchymod x 1)) 1 _ _ _ _))//.
- by rewrite ltW// cauchymodP.
- by rewrite ltW// cauchymodP.
rewrite -ltr_pdivlMr ?poly_accr_bound_gt0 ?cauchymodP//.
by rewrite pmulr_rgt0 ?invr_gt0 ?poly_accr_bound_gt0.
Defined.

Definition horner_creal (p : {poly F}) (x : creal) := CReal (horner_crealP p x).
Notation "p .[ x ]" := (horner_creal p x) : creal_scope.

Lemma neq_creal_horner p (x y : creal) : p.[x] != p.[y] -> x != y.
Proof.
case=> d d0 hd.
have [N _ /(_ N (leqnn N)) [M _ hM]] := crealP_near y ltr01.
(* hM : forall k, (M <= k)%N -> `|y N - y k| < 1 *)
pose a := y N; pose r := poly_accr_bound p a (1 + 1).
have r0 : 0 < r by rewrite poly_accr_bound_gt0.
exists (Num.min 1 (d / r)); first by rewrite lt_min ltr01 divr_gt0.
near=> k.
have [hdk hk] : d <= `|p.[x k] - p.[y k]| /\ (M <= k)%N.
  by split; near: k; [exact: hd | exact: nbhs_infty_ge].
have hyk : `|y k - a| <= 1 by rewrite distrC ltW // (hM k hk).
have [h1|h1] := leP 1 `|x k - y k|; first by rewrite ge_min h1.
rewrite ge_min ler_pdivrMr//; apply/orP; right.
rewrite (le_trans hdk)// poly_accr_bound1P//.
- by rewrite (le_trans hyk)// lerDl.
- rewrite -(subrK (y k) (x k)) -addrA (le_trans (ler_normD _ _))//.
  by rewrite lerD// ltW.
Unshelve. all: by end_near. Qed.

Lemma eq_creal_horner p (x y : creal) : x == y -> p.[x] == p.[y].
Proof. by move=> hxy /neq_creal_horner. Qed.

Require Setoid Relation_Definitions.

Local Notation "R ==> R'" := (Morphisms.respectful R R')
  (right associativity, at level 55) : signature_scope.

(**md NB: Require instead of Import and local notation because of the following error:
```
Error: Notation "_ --> _" is already defined at level 70 with arguments constr at next level, constr at next level
while it is now required to be at level 55 with arguments constr at next level, constr at level 55.
```
*)

Add Relation creal eq_creal
  reflexivity proved by eq_creal_refl
  symmetry proved by eq_creal_sym
  transitivity proved by eq_creal_trans
as eq_creal_rel.
Global Existing Instance eq_creal_rel.

Add Morphism add_creal with
  signature eq_creal ==> eq_creal ==> eq_creal as add_creal_morph.
Proof.
move=> x y eq_xy z t eq_zt [d d0 hd].
near \oo => i.
have hxy : `|x i - y i| < d / 2.
  by near: i; apply: asympt_eq => //; rewrite divr_gt0.
have hzt : `|z i - t i| < d / 2.
  by near: i; apply: asympt_eq => //; rewrite divr_gt0.
have : d <= `|(x i + z i) - (y i + t i)| by near: i.
rewrite opprD addrA [X in X + _]addrAC -addrA leNgt => /negP; apply.
by rewrite split_norm_add.
Unshelve. all: by end_near. Qed.
Global Existing Instance add_creal_morph_Proper.

Add Morphism opp_creal with
  signature eq_creal ==> eq_creal as opp_creal_morph.
Proof.
move=> x y eq_xy; apply: eq_crealP => e e0; near=> i.
rewrite /= -opprD normrN.
by near: i; exact: (asympt_eq eq_xy e0).
Unshelve. all: by end_near. Qed.
Global Existing Instance opp_creal_morph_Proper.

Add Morphism mul_creal with
  signature eq_creal ==> eq_creal ==> eq_creal as mul_creal_morph.
Proof.
move=> x y eq_xy z t eq_zt.
apply: eq_crealP => e e0.
have [bz bz0 hbz] := ubound_subproof_ex z.
have [b_y by0 hby] := ubound_subproof_ex y.
near=> i.
have [hxy hzt] : `|x i - y i| < e / 2 / bz /\ `|z i - t i| < e / 2 / b_y.
  by split; near: i; apply: asympt_eq => //; rewrite !divr_gt0.
rewrite (@split_dist_add (y i * z i)) // -(mulrBl, mulrBr) !normrM.
- have /ler_wpM2l /le_lt_trans-> // := hbz i.
  by rewrite -ltr_pdivlMr.
- rewrite mulrC.
  have /ler_wpM2l /le_lt_trans-> // := hby i.
  by rewrite -ltr_pdivlMr.
Unshelve. all: by end_near. Qed.
Global Existing Instance mul_creal_morph_Proper.

Lemma eq_creal_inv (x y : creal) (x_neq0 : x != 0) (y_neq0 : y != 0) :
  (x == y) -> (x_neq0^-1 == y_neq0^-1).
Proof.
move=> eq_xy.
case: x_neq0 => /= dx dx0 hdx.
case: y_neq0 => /= dy dy0 hdy.
apply: eq_crealP => e e0; near=> i.
have [[hxi hyi] hxy] : (dx <= `|x i| /\ dy <= `|y i|) /\
    `|x i - y i| < e * (dx * dy).
  split; first split.
  - by near: i; apply: filterS hdx => j /=; rewrite subr0.
  - by near: i; apply: filterS hdy => j /=; rewrite subr0.
  - by near: i; apply: asympt_eq => //; rewrite pmulr_rgt0 // pmulr_rgt0.
have xi_neq0 : ~~ (x i == 0) by rewrite -normr_gt0 (lt_le_trans dx0 hxi).
have yi_neq0 : ~~ (y i == 0) by rewrite -normr_gt0 (lt_le_trans dy0 hyi).
rewrite /= -(@ltr_pM2r _ `|x i * y i|).
  by rewrite normr_gt0 mulf_neq0.
rewrite -normrM !mulrBl mulrA mulVf // mulrCA mulVf // mul1r mulr1.
rewrite [in ltLHS]distrC (lt_le_trans hxy)// normrM ler_pM2l//.
by rewrite ler_pM// ltW.
Unshelve. all: by end_near. Qed.

Add Morphism horner_creal with
  signature (@eq _) ==> eq_creal ==> eq_creal as horner_creal_morph.
Proof. exact: eq_creal_horner. Qed.
Global Existing Instance horner_creal_morph_Proper.

Add Morphism lt_creal with
  signature eq_creal ==> eq_creal ==> iff as lt_creal_morph.
Proof.
move=> x y xy z t zt.
wlog lxz : x y z t xy zt / (x < z)%CR.
  move=> wlg; split=> h1; move: (h1) => /wlg; apply=> //;
  exact: eq_creal_sym.
split=> // _.
case: lxz => /= d d0 hd.
pose e' := d / 4.
have e'0 : 0 < e' by rewrite divr_gt0.
have le_zt : (z <= t)%CR by exact: eq_le_creal zt.
have le_yx : (y <= x)%CR by exact/eq_le_creal/eq_creal_sym.
exists e' => //.
near=> i.
have [hzt hyx hdxz] : [/\ z i < t i + e', y i < x i + e' & x i + d <= z i].
  split.
  - by near: i; exact: asympt_le.
  - by near: i; exact: asympt_le.
  - by near: i.
rewrite ltW // -(ltrD2r e') (le_lt_trans _ hzt)//.
rewrite -addrA -lerBrDr (le_trans (ltW hyx))//.
rewrite lerBrDr ltW // (lt_le_trans _ hdxz)//.
rewrite -addrA ler_ltD// /e' -!mulrDr gtr_pMr ?d0//.
by rewrite [X in _ < X](splitf 4) /= mul1r !ltrDr ?gtr0E.
Unshelve. all: by end_near. Qed.
Global Existing Instance lt_creal_morph_Proper.

Add Morphism le_creal with
  signature eq_creal ==> eq_creal ==> iff as le_creal_morph.
Proof. by move=> x y exy z t ezt; rewrite /le_creal exy ezt. Qed.
Global Existing Instance le_creal_morph_Proper.

Add Morphism norm_creal
 with signature eq_creal ==> eq_creal as norm_creal_morph.
Proof.
move=> x y xy; apply: eq_crealP => e e0.
near=> i.
rewrite (le_lt_trans (ler_dist_dist _ _))//.
by near: i; exact: (asympt_eq xy).
Unshelve. all: by end_near. Qed.
Global Existing Instance norm_creal_morph_Proper.

Lemma neq_creal_ltVgt (x y : creal) : x != y -> (x < y)%CR \/ (y < x)%CR.
Proof.
move=> [d d0 hd].
have d50 : 0 < d / 5 by rewrite divr_gt0.
near \oo => i.
have [hdi hxi hyi] : [/\ d <= `|x i - y i|,
                         \forall k \near \oo, `|x i - x k| < d / 5
                       & \forall k \near \oo, `|y i - y k| < d / 5].
  split.
  - by near: i.
  - by near: i; exact: crealP_near.
  - by near: i; exact: crealP_near.
have [le_xy|lt_yx] := lerP (x i) (y i).
- left; apply: (@lt_crealP _ i i d0 x y) => //.
  rewrite -lerBrDl.
  by move: hdi; rewrite distrC ger0_norm// subr_ge0.
- right; apply: (@lt_crealP _ i i d0 y x) => //.
  rewrite -lerBrDl.
  by move: hdi; rewrite gtr0_norm ?subr_gt0.
Unshelve. all: by end_near. Qed.

Lemma lt_creal_neq (x y : creal) : (x < y -> x != y)%CR.
Proof.
move=> [d d0 hd]; exists d => //.
by near do rewrite distrC (le_trans _ (ler_norm _))// lerBrDr addrC.
Unshelve. all: by end_near. Qed.

Lemma gt_creal_neq (x y : creal) : (y < x -> x != y)%CR.
Proof. by move/lt_creal_neq /neq_creal_sym. Qed.

Lemma lt_creal_trans (x y z : creal) : (x < y -> y < z -> x < z)%CR.
Proof.
move=> [d1 d10 hd1] [d2 d20 hd2].
exists (d1 + d2); first by rewrite addr_gt0.
near=> i.
have [hxy hyz] : x i + d1 <= y i /\ y i + d2 <= z i by split; near: i.
by rewrite addrA (le_trans _ hyz)// lerD2r.
Unshelve. all: by end_near. Qed.

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
Proof.
by apply/eq_crealP => /= e e0; near=> i; rewrite add0r subrr normr0.
Unshelve. all: by end_near. Qed.

Lemma add_creal0 x : x + 0 == x.
Proof.
by apply/eq_crealP => /= e e0; near=> i; rewrite addr0 subrr normr0.
Unshelve. all: by end_near. Qed.

Lemma mul_creal0 x : x * 0 == 0.
Proof.
by apply/eq_crealP => /= e e0; near=> i; rewrite mulr0 subrr normr0.
Unshelve. all: by end_near. Qed.

Lemma mul_0creal x : 0 * x == 0.
Proof.
by apply/eq_crealP => /= e e0; near=> i; rewrite mul0r subrr normr0.
Unshelve. all: by end_near. Qed.

Lemma mul_creal1 x : x * 1%:CR == x.
Proof.
by apply/eq_crealP => /= e e0; near=> i; rewrite mulr1 subrr normr0.
Unshelve. all: by end_near. Qed.

Lemma mul_1creal x : 1%:CR * x == x.
Proof.
by apply/eq_crealP => /= e e0; near=> i; rewrite mul1r subrr normr0.
Unshelve. all: by end_near. Qed.

Lemma opp_creal0 : - 0 == 0.
Proof.
by apply/eq_crealP => /= e e0; near=> i; rewrite oppr0 addr0 normr0.
Unshelve. all: by end_near. Qed.

Lemma horner_crealX (x : creal) : 'X.[x] == x.
Proof.
by apply/eq_crealP => /= e e0; near=> i; rewrite /= hornerX subrr normr0.
Unshelve. all: by end_near. Qed.

Lemma horner_crealM (p q : {poly F}) (x : creal) :
  ((p * q).[x] == p.[x] * q.[x])%CR.
Proof.
by apply/eq_crealP => /= e e0; near=> i; rewrite hornerM subrr normr0.
Unshelve. all: by end_near. Qed.

Lemma neq_creal_cst x y : reflect (cst_creal x != cst_creal y) (x != y).
Proof.
apply: (iffP idP) => neq_xy.
- exists `|x - y|.
  + by rewrite normr_gt0 subr_eq0.
  + by near=> i.
- apply/eqP => xy.
  case: neq_xy => /= e e0.
  rewrite xy subrr normr0 => -[n _ /=] /(_ n (leqnn _))/=.
  by rewrite leNgt e0.
Unshelve. all: by end_near. Qed.

Lemma eq_creal_cst x y : reflect (cst_creal x == cst_creal y) (x == y).
Proof.
apply: (iffP idP)=> [|eq_xy]; first by move/eqP => ->.
by apply/negP=> /negP /neq_creal_cst; rewrite eq_xy; exact: eq_creal_refl.
Qed.

Lemma lt_creal_cst x y : reflect (cst_creal x < cst_creal y)%CR (x < y).
Proof.
apply: (iffP idP) => hxy.
- exists (y - x); first by rewrite subr_gt0.
  by near=> i; rewrite /= addrC subrK.
- case: hxy => d d0 hd.
  rewrite ltNge; apply/negP => hyx.
  near \oo => i.
  have /= hdi : cst_creal x i + d <= cst_creal y i by near: i.
  have : x < x + d by rewrite ltrDl.
  by rewrite ltNge => /negP; apply; rewrite (le_trans hdi).
Unshelve. all: by end_near. Qed.

Lemma le_creal_cst x y : reflect (cst_creal x <= cst_creal y)%CR (x <= y).
Proof. by rewrite leNgt; apply: (iffP negP)=> ? /lt_creal_cst. Qed.

Lemma mul_creal_neq0 x y : x != 0 -> y != 0 -> x * y != 0.
Proof.
move=> [dx dx0 hdx] [dy dy0 hdy].
exists (dx * dy); first by rewrite pmulr_rgt0.
near=> i.
have [hxi hyi] : dx <= `|x i| /\ dy <= `|y i|.
  split.
  + by near: i; apply: filterS hdx => j /=; rewrite subr0.
  + by near: i; apply: filterS hdy => j /=; rewrite subr0.
by rewrite /= subr0 normrM ler_pM// ltW.
Unshelve. all: by end_near. Qed.

Lemma mul_neq0_creal x y : x * y != 0 -> y != 0.
Proof.
move=> [d d0 hd].
have [b b0 hb] := ubound_subproof_ex x.
exists (d / b); first by rewrite divr_gt0.
near=> i.
have : d <= `|(x * y)%CR i|.
  by near: i; apply: filterS hd => j /=; rewrite subr0.
rewrite /= normrM => hxy.
by rewrite subr0 ler_pdivrMr// (le_trans hxy)// mulrC ler_wpM2l.
Unshelve. all: by end_near. Qed.

Lemma poly_mul_creal_eq0_coprime p q x :
  coprimep p q ->
  p.[x] * q.[x] == 0 -> p.[x] == 0 \/ q.[x] == 0.
Proof.
move=> /Bezout_eq1_coprimepP /sig_eqW [[u v] /= hpq].
pose vqx : creal := (v.[x] * q.[x])%CR.
pose upx : creal := (u.[x] * p.[x])%CR.
pose z0 : creal := 0%CR.
near \oo => i.
have [hvq hup h0] : [/\ \forall k \near \oo, `|vqx i - vqx k| < 2^-1 / 5,
                        \forall k \near \oo, `|upx i - upx k| < 2^-1 / 5
                      & \forall k \near \oo, `|z0 i - z0 k| < 2^-1 / 5].
  split.
  - by near: i; apply: crealP_near; rewrite divr_gt0 ?invr_gt0.
  - by near: i; apply: crealP_near; rewrite divr_gt0 ?invr_gt0.
  - by near: i; apply: crealP_near; rewrite divr_gt0 ?invr_gt0.
have hpqi := erefl ((1 : {poly F}).[x i]).
rewrite -{1}hpq /= hornerD hornerC in hpqi.
set upxi := (u * p).[x i] in hpqi.
have [p_small | p_big] := lerP `|upxi| 2^-1 => pqx0; [left | right].
- move=> px0; apply: pqx0.
  apply: mul_creal_neq0 => //.
  apply: (@mul_neq0_creal v.[x]).
  apply: (@neq_crealP 2^-1 i i) => //.
  + by rewrite invr_gt0.
  + rewrite /= subr0 -hornerM -(lerD2l `|upxi|).
    rewrite (le_trans _ (ler_normD _ _)) // hpqi normr1.
    by rewrite -lerBrDr [X in X - _](splitr 1) div1r addrK.
- move=> qx0; apply: pqx0.
  apply: mul_creal_neq0 => //.
  apply: (@mul_neq0_creal u.[x]).
  apply: (@neq_crealP 2^-1 i i) => //.
  + by rewrite invr_gt0.
  + by rewrite /= subr0 -hornerM ltW.
Unshelve. all: by end_near. Qed.

Lemma dvdp_creal_eq0 p q x : p %| q -> p.[x] == 0 -> q.[x] == 0.
Proof.
by move=> dpq px0; rewrite -[q](divpK dpq) horner_crealM px0 mul_creal0.
Qed.

Lemma root_poly_expn_creal p k x : (0 < k)%N -> (p ^+ k).[x] == 0 -> p.[x] == 0.
Proof.
move=> k_gt0 pkx_eq0 [d d0 hd].
near \oo => i.
have [hpx hpkx] : d <= `|p.[x i]| /\ `|(p ^+ k).[x i]| < d ^+ k.
  split.
  - near: i; apply: filterS hd => j /=.
    by rewrite subr0.
  - near: i; apply: filterS (asympt_eq pkx_eq0 (exprn_gt0 k d0)) => j /=.
    by rewrite subr0.
rewrite horner_exp normrX in hpkx.
have : d ^+ k <= `|p.[x i]| ^+ k by rewrite lerXn2r // ?nnegrE // ltW.
by rewrite leNgt => /negP; apply.
Unshelve. all: by end_near. Qed.

Lemma horner_cst_creal c x : c%:P.[x] == c%:CR.
Proof.
by apply: eq_crealP => e e0; near=> i; rewrite /= hornerC subrr normr0.
Unshelve. all: by end_near. Qed.

Lemma horner_creal_cst (p : {poly F}) (x : F) :
  p.[x%:CR] == p.[x]%:CR.
Proof.
by apply: eq_crealP => e e0; near=> i; rewrite /= subrr normr0.
Unshelve. all: by end_near. Qed.

Lemma poly_mul_creal_eq0_or p q x :
  p.[x] * q.[x] == 0 -> p.[x] == 0 \/ q.[x] == 0.
Proof.
move=> mul_px_qx_eq0.
have [->|p_neq0] := altP (p =P 0).
  by left; rewrite horner_cst_creal.
have [->|q_neq0] := altP (q =P 0).
  by right; rewrite horner_cst_creal.
pose d := gcdp p q.
pose p' := gdcop d p.
pose q' := gdcop d q.
have cop_q'_d' : coprimep p' q'.
  rewrite /coprimep size_poly_eq1.
  apply: (@coprimepP _ p' d _).
  + by rewrite coprimep_gdco.
  + by rewrite dvdp_gcdl.
  rewrite dvdp_gcd (dvdp_trans (dvdp_gcdl _ _)) ?dvdp_gdco //.
  by rewrite (dvdp_trans (dvdp_gcdr _ _)) ?dvdp_gdco.
suff hprod : (p' * q').[x] * (d ^+ (size p + size q)).[x] == 0.
  have hcop : coprimep (p' * q') (d ^+ (size p + size q)).
    by rewrite coprimep_expr// coprimepMl ?coprimep_gdco.
  have [hpq0|hdexp0] := poly_mul_creal_eq0_coprime hcop hprod.
  - have hp'q'0 : p'.[x] * q'.[x] == 0.
      by rewrite -horner_crealM.
    have [hp'0|hq'0] := poly_mul_creal_eq0_coprime cop_q'_d' hp'q'0.
    + left.
      by rewrite (dvdp_creal_eq0 _ hp'0)// dvdp_gdco.
    + right.
      by rewrite (dvdp_creal_eq0 _ hq'0)// dvdp_gdco.
  - have hsz : (0 < size p + size q)%N.
      by rewrite addn_gt0 lt0n size_poly_eq0 p_neq0.
    have hd0 : d.[x] == 0 by exact: root_poly_expn_creal hsz hdexp0.
    left.
    by rewrite (dvdp_creal_eq0 _ hd0)// dvdp_gcdl.
move: mul_px_qx_eq0.
rewrite -!horner_crealM exprD mulrAC mulrA -mulrA [_ ^+ _ * _]mulrC.
apply: dvdp_creal_eq0.
by rewrite ?dvdp_mul // dvdp_gdcor // gcdp_eq0 negb_and p_neq0.
Qed.

Lemma poly_mul_creal_eq0_coprime_dec p q x :
  coprimep p q ->
  p.[x] * q.[x] == 0 ->
  {p.[x] == 0} + {q.[x] == 0}.
Proof.
move=> /Bezout_eq1_coprimepP /sig_eqW [[u v] /= hpq].
pose vqx : creal := (v.[x] * q.[x])%CR.
pose upx : creal := (u.[x] * p.[x])%CR.
pose z0 : creal := 0%CR.
pose e : F := 2%:R^-1 .
pose e5 : F := e / 5.
pose i := maxn (maxn (cauchymod vqx e5) (cauchymod upx e5)) (cauchymod z0 e5).
have hvqi : (cauchymod vqx e5 <= i)%N.
  by rewrite (leq_trans (leq_maxl _ _) (leq_maxl _ _)).
have hupi : (cauchymod upx e5 <= i)%N.
  by rewrite (leq_trans (leq_maxr _ _) (leq_maxl _ _)).
have h0i : (cauchymod z0 e5 <= i)%N by rewrite leq_maxr.
have hpqi := erefl ((1 : {poly F}).[x i]).
rewrite -{1}hpq /= hornerD hornerC in hpqi.
set upxi := (u * p).[x i] in hpqi.
have [p_small | p_big] := lerP `|upxi| e => pqx0; [left | right].
- move=> px0; apply: pqx0.
  apply: mul_creal_neq0 => //.
  apply: (@mul_neq0_creal v.[x]).
  apply: (@neq_crealP e i i).
  + by rewrite /e invr_gt0.
  + near=> k; apply: cauchymodP => //.
    * by rewrite divr_gt0 ?invr_gt0.
    * by near: k.
  + near=> k.
    apply: cauchymodP => //.
    * by rewrite divr_gt0 ?invr_gt0.
  + rewrite /= subr0 -hornerM -(lerD2l `|upxi|).
    rewrite (le_trans _ (ler_normD _ _)) // hpqi normr1.
    by rewrite -lerBrDr [X in X - _]splitr div1r addrK.
- move=> qx0; apply: pqx0.
  apply: mul_creal_neq0 => //.
  apply: (@mul_neq0_creal u.[x]).
  apply: (@neq_crealP e i i) => //.
  + by rewrite invr_gt0.
  + near=> k.
    rewrite cauchymodP ?divr_gt0 ?invr_gt0//.
    by near: k.
  + near=> k.
    by rewrite cauchymodP ?divr_gt0 ?invr_gt0.
  + by rewrite /= subr0 -hornerM ltW.
Unshelve. all: by end_near. Qed.

Lemma poly_mul_creal_eq0 p q x :
  p.[x] * q.[x] == 0 ->
  {p.[x] == 0} + {q.[x] == 0}.
Proof.
move=> mul_px_qx_eq0.
have [->|p_neq0] := altP (p =P 0).
  by left; rewrite horner_cst_creal.
have [->|q_neq0] := altP (q =P 0).
  by right; rewrite horner_cst_creal.
pose d := gcdp p q.
pose p' := gdcop d p.
pose q' := gdcop d q.
have cop_q'_d' : coprimep p' q'.
  rewrite /coprimep size_poly_eq1.
  apply: (@coprimepP _ p' d _).
  + by rewrite coprimep_gdco.
  + by rewrite dvdp_gcdl.
  rewrite dvdp_gcd (dvdp_trans (dvdp_gcdl _ _))/= ?dvdp_gdco//.
  by rewrite (dvdp_trans (dvdp_gcdr _ _)) ?dvdp_gdco.
suff hprod : (p' * q').[x] * (d ^+ (size p + size q)).[x] == 0.
  have hcop : coprimep (p' * q') (d ^+ (size p + size q)).
    by rewrite coprimep_expr // coprimepMl ?coprimep_gdco.
  have [hpq0 | hdexp0] := poly_mul_creal_eq0_coprime_dec hcop hprod.
  - have hp'q'0 : p'.[x] * q'.[x] == 0 by rewrite -horner_crealM.
    have [hp'0 | hq'0] := poly_mul_creal_eq0_coprime_dec cop_q'_d' hp'q'0.
    + left.
      by rewrite (dvdp_creal_eq0 _ hp'0)// dvdp_gdco.
    + right.
      by rewrite (dvdp_creal_eq0 _ hq'0)// dvdp_gdco.
  - have hsz : (0 < size p + size q)%N.
      by rewrite addn_gt0 lt0n size_poly_eq0 p_neq0.
    have hd0 : d.[x] == 0 by exact: root_poly_expn_creal hsz hdexp0.
    left.
    by rewrite (dvdp_creal_eq0 _ hd0)// dvdp_gcdl.
move: mul_px_qx_eq0.
rewrite -!horner_crealM.
rewrite exprD mulrAC mulrA -mulrA [_ ^+ _ * _]mulrC.
apply: dvdp_creal_eq0.
by rewrite ?dvdp_mul // dvdp_gdcor // gcdp_eq0 negb_and p_neq0.
Defined.

Lemma coprimep_root (p q : {poly F}) x :
  coprimep p q -> p.[x] == 0 -> q.[x] != 0.
Proof.
move=> /Bezout_eq1_coprimepP /sig_eqW [[u v] hpq] px0.
have upx_eq0 : u.[x] * p.[x] == 0 by rewrite px0 mul_creal0.
have [b b0 hb] := ubound_subproof_ex v.[x].
exists (b^-1 / 2); first by rewrite divr_gt0 // invr_gt0.
near=> i.
have hup : `|(u * p).[x i]| < 2%:R^-1.
  near: i.
  have gt02 : 0 < 2^-1 :> F by rewrite invr_gt0.
  apply: filterS (asympt_eq upx_eq0 gt02) => j /=.
  by rewrite subr0 -hornerM.
have hpqi := erefl ((1 : {poly F}).[x i]).
rewrite -{1}hpq /= hornerD hornerC in hpqi.
set upxi := (u * p).[x i] in hpqi hup.
rewrite /= subr0 ler_pdivrMl //.
apply: le_trans (_ : `|(v * q).[x i]| <= _); last first.
  by rewrite hornerM normrM ler_wpM2r ?normr_ge0// hb.
rewrite -(lerD2l `|upxi|).
rewrite (le_trans _ (ler_normD upxi (v * q).[x i]))// hpqi normr1.
by rewrite -lerBrDr [X in X - _](splitr 1) div1r addrK ltW.
Unshelve. all: by end_near. Qed.

(* NB: to avoid universe inconsistency *)
Definition strong_mono_prop (p : {poly F}) (a r : F) : Prop :=
  exists sm : strong_mono p a r, True.

Lemma deriv_neq0_mono (p : {poly F}) (x : creal) : p^`().[x] != 0 ->
  exists2 r : F, 0 < r & \forall i \near \oo, strong_mono_prop p (x i) r.
Proof.
move=> px_neq0.
wlog hpos : p px_neq0 / (0 < p^`().[x])%CR.
  move=> hpos.
  have [px_lt0 | px_gt0] := neq_creal_ltVgt px_neq0.
  - have npx_gt0 : (0 < (- p)^`().[x])%CR.
      case: px_lt0 => d d0 hd.
      exists d => //.
      apply: filterS hd => i /= hi.
      by rewrite add0r derivN hornerN -subr_le0 opprK addrC.
    have npx_neq0 : (- p)^`().[x] != 0.
      apply: neq_creal_sym.
      exact: lt_neq_creal npx_gt0.
    have [r r0 hr] := hpos (- p) npx_neq0 npx_gt0.
    exists r => //.
    apply: filterS hr => i [sm _].
    move/strong_monoN: sm; rewrite opprK => sm.
    by exists sm.
  - exact: hpos.
move: hpos => [d d0 hd].
have [b b0 hb] := ubound_subproof_ex x.
pose b1 := poly_accr_bound p^`() 0 (1 + b).
pose b2 := poly_accr_bound2 p 0 (1 + b).
pose r : F := Num.min 1 (Num.min (d / 4 / b1) (d / 4 / b2 / 2)).
exists r.
  rewrite /r !lt_min ?ltr01 ?pmulr_rgt0 ?gtr0E ?d0;
  by rewrite ?poly_accr_bound2_gt0 ?poly_accr_bound_gt0.
near=> i.
have hdi : d <= p^`().[x i].
  by near: i; apply: filterS hd => j /=; rewrite add0r.
suff sm : strong_mono p (x i) r by exists sm.
left; split => /=; last first.
  move=> y hy.
  have := @poly_accr_bound1P _ p^`() 0 (1 + b) (x i) y.
  rewrite ?subr0 ler_wpDl ?ler01 ?hb //.
  rewrite (@le_trans _ _ (r + `|x i|)) ?subr0.
  - by rewrite -lerBlDr (le_trans (lerB_dist _ _)).
  - by rewrite lerD ?ge_min ?lexx ?hb.
  move=> /(_ isT isT).
  rewrite ler_distl => /andP[le_py ge_py].
  rewrite (lt_le_trans _ le_py) // subr_gt0 -/b1.
  rewrite (lt_le_trans _ hdi) //.
  rewrite (@le_lt_trans _ _ (r * b1))//.
    by rewrite ler_wpM2r ?poly_accr_bound_ge0.
  rewrite -ltr_pdivlMr ?poly_accr_bound_gt0 //.
  rewrite /r !gt_min ltr_pM2r ?invr_gt0 ?poly_accr_bound_gt0 //.
  by rewrite gtr_pMr ?d0 // invf_lt1 ?gtr0E ?ltr1n ?orbT.
exists (d / 4); first by rewrite pmulr_rgt0 ?gtr0E ?d0.
move=> y z neq_yz hy hz.
have := @poly_accr_bound1P _ p^`() 0 (1 + b) (x i) z.
have := @poly_accr_bound2P _ p 0 (1 + b) z y.
rewrite eq_sym !subr0.
rewrite neq_yz ?ler01 ?(ltW b0) => // /(_ isT).
rewrite (@le_trans _ _ (r + `|x i|))//.
- by rewrite -lerBlDr (le_trans (lerB_dist _ _)).
- by rewrite lerD ?ge_min ?lexx ?hb.
rewrite (@le_trans _ _ (r + `|x i|))//.
- by rewrite -lerBlDr (le_trans (lerB_dist _ _)).
- by rewrite lerD ?ge_min ?lexx ?hb.
rewrite ler_wpDl ?hb ?ler01 //.
move=> /(_ isT isT); rewrite ler_distl => /andP[haccr _].
move=> /(_ isT isT); rewrite ler_distl => /andP[hp' _].
rewrite (lt_le_trans _ haccr) //.
rewrite -ltrBlDr opprK.
rewrite (lt_le_trans _ hp') // (monoRL (addrK _) (ltrD2r _)).
rewrite (lt_le_trans _ hdi) //.
rewrite {2}[d](splitf 4) /= -!addrA ltrD2l ltr_pwDl //.
  by rewrite pmulr_rgt0 ?gtr0E ?d0.
rewrite -/b1 -/b2 lerD //.
+ rewrite -ler_pdivlMr ?poly_accr_bound2_gt0 //.
  rewrite (le_trans (ler_distD (x i) _ _)) //.
  rewrite (@le_trans _ _ (r * 2))//.
    by rewrite mulrDr mulr1 lerD // distrC.
  by rewrite -ler_pdivlMr ?ltr0n // /r !ge_min lexx !orbT.
+ rewrite -ler_pdivlMr ?poly_accr_bound_gt0 //.
  by rewrite (le_trans hz) // /r !ge_min lexx !orbT.
Unshelve. all: by end_near. Qed.

Lemma smaller_factor (p q : {poly F}) x :
  p \is monic -> p.[x] == 0 ->
  ~~ (p %| q) -> ~~ coprimep p q ->
  {r : {poly F} | (size r < size p)%N && (r \is monic) & r.[x] == 0}.
Proof.
move=> monic_p px0 ndvd_pq.
rewrite /coprimep; set d := gcdp _ _ => sd_neq1.
pose r1 : {poly F} := (lead_coef d)^-1 *: d.
pose r2 := p %/ r1.
have ld_neq0 : lead_coef d != 0 :> F.
  by rewrite lead_coef_eq0 gcdp_eq0 negb_and monic_neq0.
have monic_r1 : r1 \is monic.
  by rewrite monicE /r1 -mul_polyC lead_coefM lead_coefC mulVf.
have eq_p_r2r1 : p = r2 * r1.
  by rewrite divpK // (@eqp_dvdl _ d) ?dvdp_gcdl// eqp_scale ?invr_eq0.
have monic_r2 : r2 \is monic by rewrite -(monicMr _ monic_r1) -eq_p_r2r1.
have eq_sr1_sd : size r1 = size d by rewrite size_scale ?invr_eq0.
have sr1 : (1 < size r1)%N.
  by rewrite ltn_neqAle eq_sym lt0n size_poly_eq0 monic_neq0 ?andbT ?eq_sr1_sd.
have sr2 : (1 < size r2)%N.
  rewrite size_divp ?size_dvdp ?monic_neq0 //.
  rewrite ltn_subRL addn1 prednK ?(leq_trans _ sr1) // eq_sr1_sd.
  rewrite ltn_neqAle dvdp_leq ?monic_neq0 ?andbT ?dvdp_size_eqp ?dvdp_gcdl //.
  by apply: contra ndvd_pq => /eqp_dvdl <-; rewrite dvdp_gcdr.
have hr2r1 : r2.[x] * r1.[x] == 0.
  move: px0.
  by rewrite eq_p_r2r1 horner_crealM.
have sr2p : (size r2 < size p)%N.
  by rewrite eq_p_r2r1 size_mul ?monic_neq0// -subn1 ltn_subRL addnC ltn_add2l.
have sr1p : (size r1 < size p)%N.
  by rewrite eq_p_r2r1 size_mul ?monic_neq0// -subn1 ltn_subRL ltn_add2r.
have [r2x_eq0 | r1x_eq0] := poly_mul_creal_eq0 hr2r1.
- by exists r2 => //; rewrite sr2p monic_r2.
- by exists r1 => //; rewrite sr1p monic_r1.
Defined.

Lemma root_cst_creal (x : F) : ('X - x%:P).[cst_creal x] == 0.
Proof.
by apply: eq_crealP => e e_gt0; near=> i; rewrite /= subr0 !hornerE subrr normr0.
Unshelve. all: by end_near. Qed.

Lemma has_root_creal_size_gt1 (x : creal) (p : {poly F}) :
  (p != 0)%B -> p.[x] == 0 -> (1 < size p)%N.
Proof.
move=> p_neq0 rootpa.
rewrite ltnNge leq_eqVlt ltnS leqn0 size_poly_eq0 (negPf p_neq0) orbF.
apply/negP=> /size_poly1P [c c_neq0 eq_pc]; apply: rootpa.
by rewrite eq_pc horner_cst_creal; apply/neq_creal_cst.
Qed.

Definition bound_poly_bound (b : F) (q : {poly {poly F}}) (a r : F) i :=
  1 + \sum_(j < sizeY q)
    `|(norm_poly2 q).[b%:P]^`N(i.+1)`_j| * (`|a| + `|r|) ^+ j.

Lemma bound_poly_boundP (z : creal) (b : F) (b0 : 0 < b)
    (zb : forall n, `|z n| <= b) i (q : {poly {poly F}}) (a r : F) j :
  poly_bound q.[(z i)%:P]^`N(j.+1) a r <= bound_poly_bound b q a r j.
Proof.
rewrite /poly_bound.
pose f (q : {poly F}) (k : nat) := `|q^`N(j.+1)`_k| * (`|a| + `|r|) ^+ k.
rewrite lerD //=.
rewrite (big_ord_widen (sizeY q) (f q.[(z i)%:P])).
  by rewrite size_nderivn leq_subLR (leq_trans (max_size_evalC _ _))// leq_addl.
rewrite big_mkcond /= ler_sum // /f => k _.
case: ifP => _; last by rewrite mulr_ge0 ?exprn_ge0 ?addr_ge0 ?normr_ge0.
rewrite ler_wpM2r ?exprn_ge0 ?addr_ge0 ?normr_ge0 //.
rewrite !horner_coef !(@big_morph _ _ (fun p => p^`N(j.+1)) 0 +%R) ?raddf0//;
   [by move=> x y /=; rewrite raddfD..|].
rewrite !coef_sum (le_trans (ler_norm_sum _ _ _))// ger0_norm.
  rewrite sumr_ge0 => //= l _.
  rewrite coef_nderivn mulrn_wge0 ?natr_ge0//.
  rewrite -polyC_exp coefMC coef_norm_poly2 mulr_ge0 ?normr_ge0 //.
  by rewrite exprn_ge0// ltW.
rewrite size_norm_poly2 ler_sum //= => l _.
rewrite !{1}coef_nderivn normrMn ler_pMn2r ?bin_gt0 ?leq_addr //.
rewrite -!polyC_exp !coefMC coef_norm_poly2 normrM ler_wpM2l ?normr_ge0//.
rewrite normrX; case: (val l) => // {}l.
by rewrite ler_pXn2r -?topredE//= ?hb// ltW.
Qed.

Lemma bound_poly_bound_ge0 (b : F) q a r i : 0 <= bound_poly_bound b q a r i.
Proof.
rewrite /bound_poly_bound addr_ge0//; apply: sumr_ge0 => j _.
by rewrite mulr_ge0 ?normr_ge0 ?exprn_ge0 ?addr_ge0.
Qed.

Definition bound_poly_accr_bound (b : F) (q : {poly {poly F}}) (a r : F) :=
  Num.max 1 (2%:R * r) ^+ (sizeY q).-1 *
  (1 + \sum_(i < (sizeY q).-1) bound_poly_bound b q a r i).

Lemma bound_poly_accr_boundP (z : creal) (b : F) (b0 : 0 < b)
    (hb : forall n, `|z n| <= b) i (q : {poly {poly F}}) (a r : F) :
  poly_accr_bound q.[(z i)%:P] a r <= bound_poly_accr_bound b q a r.
Proof.
rewrite /poly_accr_bound /bound_poly_accr_bound /=.
set ui := _ ^+ _; set u := _ ^+ _; set vi := 1 + _.
apply: le_trans (_ : u * vi <= _).
  rewrite ler_wpM2r //.
    by rewrite addr_ge0 ?ler01 // sumr_ge0 //= => j _; rewrite poly_bound_ge0.
  rewrite /ui /u; case: (ltP 1%R); last by rewrite !expr1n.
  move=> r2_gt1; rewrite ler_eXn2l//.
  rewrite -subn1 leq_subLR add1n (leq_trans _ (leqSpred _))//.
  by rewrite max_size_evalC.
rewrite ler_wpM2l ?exprn_ge0 ?le_max ?ler01 // lerD //.
pose f j := poly_bound q.[(z i)%:P]^`N(j.+1) a r.
rewrite (big_ord_widen (sizeY q).-1 f).
  by rewrite -subn1 leq_subLR add1n (leq_trans _ (leqSpred _))// max_size_evalC.
rewrite big_mkcond /= ler_sum // /f => k _.
case: ifP => _.
- exact: bound_poly_boundP.
- exact: bound_poly_bound_ge0.
Qed.

Lemma bound_poly_accr_bound_gt0 (b : F) (q : {poly {poly F}}) (a r : F) :
  0 < bound_poly_accr_bound b q a r.
Proof.
rewrite /bound_poly_accr_bound mulr_gt0//.
- by rewrite exprn_gt0// lt_max ltr01.
- have hs : 0 <= \sum_(i < (sizeY q).-1) bound_poly_bound b q a r i.
    by apply: sumr_ge0 => i _; exact: bound_poly_bound_ge0.
  by rewrite ltr_wpDr.
Qed.

Lemma horner2_crealP (p : {poly {poly F}}) (x y : creal) :
  creal_axiom_sig (fun i => p.[x i, y i]).
Proof.
have [dx dx0 xdx] := ubound_subproof_sig x.
have [dy dy0 ydy] := ubound_subproof_sig y.
exists (fun e => maxn
  (cauchymod y (e / 2 / bound_poly_accr_bound dx p 0 dy))
  (cauchymod x (e / 2 / bound_poly_accr_bound dy (swapXY p) 0 dx))).
move=> e i j e0.
rewrite !geq_max => /andP[hyi hxi] /andP[hyj hxj].
rewrite (@split_dist_add p.[x i, y j]) //.
- rewrite (le_lt_trans (@poly_accr_bound1P _ _ 0 dy _ _ _ _)) ?subr0 ?hby//.
  apply: (@le_lt_trans _ _ (`|y i - y j| * bound_poly_accr_bound dx p 0 dy)).
    by rewrite ler_wpM2l ?normr_ge0// bound_poly_accr_boundP.
  rewrite -ltr_pdivlMr ?bound_poly_accr_bound_gt0// cauchymodP//.
  by rewrite !divr_gt0 ?gtr0E ?bound_poly_accr_bound_gt0.
- rewrite -[p]swapXYK ![(swapXY (swapXY _)).[_, _]]horner2_swapXY.
  rewrite (le_lt_trans (@poly_accr_bound1P _ _ 0 dx _ _ _ _)) ?subr0 ?hbx//.
  apply: (@le_lt_trans _ _  (`|x i - x j| * bound_poly_accr_bound dy (swapXY p) 0 dx)).
    by rewrite ler_wpM2l ?normr_ge0// bound_poly_accr_boundP.
  rewrite -ltr_pdivlMr ?bound_poly_accr_bound_gt0// cauchymodP//.
  by rewrite !divr_gt0 ?gtr0E ?bound_poly_accr_bound_gt0.
Defined.

Definition horner2_creal (p : {poly {poly F}}) (x y : creal) :=
  CReal (horner2_crealP p x y).
Notation "p .[ x , y ]" := (horner2_creal p x y) : creal_scope.

Lemma root_monic_from_neq0 (p : {poly F}) (x : creal) :
  p.[x] == 0 -> ((lead_coef p) ^-1 *: p).[x] == 0.
Proof. by rewrite -mul_polyC horner_crealM; move->; rewrite mul_creal0. Qed.

Lemma root_sub_annihilant_creal (x y : creal) (p q : {poly F}) :
  (p != 0)%B -> (q != 0)%B -> p.[x] == 0 -> q.[y] == 0 ->
  (sub_annihilant p q).[x - y] == 0.
Proof.
move=> p_neq0 q_neq0 px_eq0 qy_eq0.
have [||[u v] /= [hu hv] hpq] := @sub_annihilant_in_ideal _ p q.
- by rewrite (@has_root_creal_size_gt1 x).
- by rewrite (@has_root_creal_size_gt1 y).
have [bu bu0 hbu] := ubound_subproof_ex (u.[y, x - y])%CR.
have [bv bv0 hbv] := ubound_subproof_ex (v.[y, x - y])%CR.
have hp0 eps : 0 < eps -> \forall i \near \oo, `|p.[x i]| < eps.
  move/(asympt_eq px_eq0).
  by apply: filterS => i /=; rewrite subr0.
have hq0 eps : 0 < eps -> \forall i \near \oo, `|q.[y i]| < eps.
  move/(asympt_eq qy_eq0).
  by apply: filterS => i /=; rewrite subr0.
apply: eq_crealP => e e0.
near=> i.
rewrite /= subr0 (hpq (y i)) addrCA subrr addr0 split_norm_add // normrM.
- apply: (@le_lt_trans _ _ (bu * `|p.[x i]|)).
    by rewrite ler_wpM2r ?normr_ge0 // (hbu i).
  rewrite -ltr_pdivlMl//.
  near: i; apply: hp0.
  by rewrite !pmulr_rgt0 ?invr_gt0 ?gtr0E.
- apply: (@le_lt_trans _ _ (bv * `|q.[y i]|)).
    by rewrite ler_wpM2r ?normr_ge0 // (hbv i).
  rewrite -ltr_pdivlMl//.
  near: i; apply: hq0.
  by rewrite !pmulr_rgt0 ?invr_gt0 ?gtr0E.
Unshelve. all: by end_near. Qed.

Lemma root_div_annihilant_creal (x y : creal) (p q : {poly F}) (y_neq0 : y != 0) :
  (p != 0)%B -> (q != 0)%B -> p.[x] == 0 -> q.[y] == 0 ->
  (div_annihilant p q).[(x / y_neq0)%CR] == 0.
Proof.
move=> p_neq0 q_neq0 px_eq0 qy_eq0.
have [||[u v] /= [hu hv] hpq] := @div_annihilant_in_ideal _ p q.
- by rewrite (@has_root_creal_size_gt1 x).
- by rewrite (@has_root_creal_size_gt1 y).
have [bu bu0 hbu] := ubound_subproof_ex (u.[y, x / y_neq0])%CR.
have [bv bv0 hbv] := ubound_subproof_ex (v.[y, x / y_neq0])%CR.
apply: eq_crealP => e e0.
have eu0 : 0 < e / 2 / bu by rewrite !divr_gt0 ?gtr0E.
have ev0 : 0 < e / 2 / bv by rewrite !divr_gt0 ?gtr0E.
near=> i.
have [hyi hpi hqi] :
    [/\ (y i != 0)%B, `|p.[x i]| < e / 2 / bu & `|q.[y i]| < e / 2 / bv].
  split.
  - by near: i; exact: filterS (creal_neq_always y_neq0).
  - near: i; apply: filterS (asympt_eq px_eq0 eu0) => j /=.
    by rewrite subr0.
  - near: i; apply: filterS (asympt_eq qy_eq0 ev0) => j /=.
    by rewrite subr0.
rewrite /= subr0.
rewrite (hpq (y i)) mulrCA divff ?hyi ?mulr1 //.
rewrite split_norm_add // normrM.
- apply: le_lt_trans (_ : bu * `|p.[x i]| < _).
    by rewrite ler_wpM2r ?normr_ge0 // (hbu i).
  by rewrite -ltr_pdivlMl// mulrC hpi.
- apply: le_lt_trans (_ : bv * `|q.[y i]| < _).
    by rewrite ler_wpM2r ?normr_ge0 // (hbv i).
  by rewrite -ltr_pdivlMl//  mulrC.
Unshelve. all: by end_near. Qed.

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
apply: eq_crealP => e e_gt0; near=> n; rewrite /= horner_coef.
rewrite (@big_morph _ _ (fun u : creal => u n) 0%R +%R) //.
rewrite -sumrB /= big1 ?normr0 => //= i _.
apply/eqP; rewrite subr_eq0; apply/eqP; congr (_ * _).
case: val => {i} // i; rewrite exprS /exp_creal iteropS.
by elim: i => [|i ihi]; rewrite ?expr0 ?mulr1 //= exprS ihi.
Unshelve. all: by end_near. Qed.

End CauchyReals.

Arguments cauchymod : simpl never.

Notation "x == y" := (eq_creal x y) : creal_scope.
Notation "!=%CR" := neq_creal : creal_scope.
Notation "x != y" := (neq_creal x  y) : creal_scope.

Notation "x %:CR" := (cst_creal x)
  (at level 1, left associativity, format "x %:CR") : creal_scope.
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
Notation "p .[ x , y ]" := (horner2_creal p x y) : creal_scope.
Notation "x ^+ n" := (exp_creal x n) : creal_scope.

Notation "`| x |" := (norm_creal x) : creal_scope.

#[global] Hint Resolve eq_creal_refl le_creal_refl : core.

Notation "{ 'asympt' e : i / P }" := (asympt1 (fun e i => P)) : type_scope.
Notation "{ 'asympt' e : i j / P }" := (asympt2 (fun e i j => P)) : type_scope.

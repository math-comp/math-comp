(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                   *)
(* Distributed under the terms of CeCILL-B.                                   *)
From mathcomp Require Import boot order orderedzmod algebraic_hierarchy.
From mathcomp Require Import numeric_hierarchy ssrint poly polydiv.

(*****************************************************************************)
(* This file contains a basic theory of polynomials over a real-closed field *)
(* From the IVT (from the rcfType structure), we derive Rolle's Theorem,     *)
(* the Mean Value Theorem, a root isolation procedure and a notion of        *)
(* neighborhood.                                                             *)
(*                                                                           *)
(*    sgp_minfty p == the sign of p in -oo                                   *)
(*    sgp_pinfty p == the sign of p in +oo                                   *)
(*  cauchy_bound p == the cauchy bound of p                                  *)
(*                    (this strictly bounds the norm of roots of p)          *)
(*     roots p a b == the ordered list of roots of p in  `[a, b]             *)
(*                    defaults to [::] when p == 0                           *)
(*        rootsR p == the ordered list of all roots of p, ([::] if p == 0).  *)
(* next_root p x b == the smallest root of p contained in `[x, maxn x b]     *)
(*                    if p has no root on `[x, maxn x b], we pick maxn x b.  *)
(* prev_root p x a == the smallest root of p contained in `[minn x a, x]     *)
(*                    if p has no root on `[minn x a, x], we pick minn x a.  *)
(*   neighpr p a b := `]a, next_root p a b[.                                 *)
(*                 == an open interval of the form `]a, x[, with x <= b      *)
(*                    in which p has no root.                                *)
(*   neighpl p a b := `]prev_root p a b, b[.                                 *)
(*                 == an open interval of the form `]x, b[, with a <= x      *)
(*                    in which p has no root.                                *)
(*   sgp_right p a == the sign of p on the right of a.                       *)
(*****************************************************************************)


Import Order.Theory GRing.Theory Num.Def Num.Theory Pdiv.Idomain.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Local Notation noroot p := (forall x, ~~ root p x).
Local Notation mid x y := ((x + y) / 2%:R).
Local Notation maxr := Num.max.
Local Notation minr := Num.min.
Local Notation sgr := Num.sg.

Section more.
Section SeqR.

Lemma last1_neq0 (R : nzRingType) (s : seq R) (c : R) :
  c != 0 -> (last c s != 0) = (last 1 s != 0).
Proof. by elim: s c => [|t s ihs] c cn0 //; rewrite oner_eq0 cn0. Qed.

End SeqR.

Section poly.
Import Pdiv.Ring Pdiv.ComRing.

Variable R : idomainType.

Implicit Types p q : {poly R}.

Lemma lead_coefDr p q :
  (size q > size p)%N -> lead_coef (p + q) = lead_coef q.
Proof. exact: lead_coefDr. Qed.

Lemma leq1_size_polyC (c : R) : (size c%:P <= 1)%N.
Proof. exact: size_polyC_leq1. Qed.

Lemma my_size_exp p n : p != 0 -> (size (p ^+ n)) = ((size p).-1 * n).+1%N.
Proof. by move=> hp; rewrite -size_exp prednK // size_poly_gt0 expf_neq0. Qed.

Lemma coef_comp_poly p q n :
  (p \Po q)`_n = \sum_(i < size p) p`_i * (q ^+ i)`_n.
Proof. exact: coef_comp_poly. Qed.

Lemma gt_size_poly p n : (size p > n)%N -> p != 0.
Proof. by rewrite -size_poly_gt0; apply: leq_trans. Qed.

Lemma lead_coef_comp_poly p q :
   (size q > 1)%N ->
  lead_coef (p \Po q) = (lead_coef p) * (lead_coef q) ^+ (size p).-1.
Proof. exact: lead_coef_comp. Qed.

End poly.
End more.

(******************************************************************)
(* Definitions and properties for polynomials in a numDomainType. *)
(******************************************************************)
Section PolyNumDomain.

Variable R : numDomainType.
Implicit Types (p q : {poly R}).

Definition sgp_pinfty (p : {poly R}) := Num.sg (lead_coef p).
Definition sgp_minfty (p : {poly R}) :=
  Num.sg ((-1) ^+ (size p).-1 * (lead_coef p)).

End PolyNumDomain.

(******************************************************************)
(* Definitions and properties for polynomials in a realFieldType. *)
(******************************************************************)
Section PolyRealField.

Variable R : realFieldType.
Implicit Types (p q : {poly R}).

Section SgpInfty.

Lemma sgp_pinfty_sym p : sgp_pinfty (p \Po -'X) = sgp_minfty p.
Proof.
rewrite /sgp_pinfty /sgp_minfty lead_coef_comp ?size_polyN ?size_polyX //.
by rewrite lead_coefN lead_coefX mulrC.
Qed.

Lemma poly_pinfty_gt_lc p :
   lead_coef p > 0 ->
  exists n, forall x, x >= n -> p.[x] >= lead_coef p.
Proof.
elim/poly_ind: p => [| q c IHq]; first by rewrite lead_coef0 ltxx.
have [->|q_neq0] := eqVneq q 0.
  by rewrite mul0r add0r lead_coefC => c_gt0; exists 0 => x _; rewrite hornerC.
rewrite lead_coefDl ?size_mulX ?size_polyC // ?lead_coefMX.
  by apply: (leq_trans (leq_b1 _)); rewrite size_poly_gt0.
move=> lq_gt0; have [y Hy] := IHq lq_gt0.
pose z := (1 + (lead_coef q) ^-1 * `|c|); exists (maxr y z) => x.
have z_gt0: 0 < z by rewrite ltr_pwDl ?ltr01 ?mulr_ge0 ?invr_ge0 // ltW.
rewrite !hornerE ge_max => /andP[/Hy Hq Hc].
apply: le_trans (_ : lead_coef q * z + c <= _); last first.
  rewrite lerD2r (le_trans (_ : _ <= q.[x] * z)) // ?ler_pM2r //.
  by rewrite ler_pM2l // (lt_le_trans _ Hq).
rewrite mulrDr mulr1 -addrA lerDl mulVKf ?gt_eqF //.
by rewrite -[c]opprK subr_ge0 normrN ler_norm.
Qed.

(* :REMARK: not necessary here ! *)
Lemma poly_lim_infty p m :
    lead_coef p > 0 -> (size p > 1)%N ->
  exists n, forall x, x >= n -> p.[x] >= m.
Proof.
elim/poly_ind: p m => [| q c _] m; first by rewrite lead_coef0 ltxx.
have [-> _|q_neq0] := eqVneq q 0.
  by rewrite mul0r add0r size_polyC ltnNge leq_b1.
rewrite lead_coefDl ?size_mulX ?size_polyC // ?lead_coefMX.
  by apply: (leq_trans (leq_b1 _)); rewrite size_poly_gt0.
move=> lq_gt0; have [y Hy _] := poly_pinfty_gt_lc lq_gt0.
pose z := (1 + (lead_coef q) ^-1 * (`|m| + `|c|)); exists (maxr y z) => x.
have z_gt0 : 0 < z.
  by rewrite ltr_pwDl ?ltr01 ?mulr_ge0 ?invr_ge0 ?addr_ge0 // ?ltW.
rewrite !hornerE ge_max => /andP[/Hy Hq Hc].
apply: le_trans (_ : lead_coef q * z + c <= _); last first.
  rewrite lerD2r (le_trans (_ : _ <= q.[x] * z)) // ?ler_pM2r //.
  by rewrite ler_pM2l // (lt_le_trans _ Hq).
rewrite mulrDr mulr1 mulVKf ?gt_eqF // addrA -(addrA _ _ c) ler_wpDr //.
  by rewrite -[c]opprK subr_ge0 normrN ler_norm.
by rewrite ler_wpDl ?ler_norm // ?ltW.
Qed.

End SgpInfty.

Section CauchyBound.

Definition cauchy_bound (p : {poly R}) :=
  1 + `|lead_coef p|^-1 * \sum_(i < size p) `|p`_i|.

(* Could be a sharp bound, and proof should shrink... *)
Lemma cauchy_boundP (p : {poly R}) x :
  p != 0 -> p.[x] = 0 -> `| x | < cauchy_bound p.
Proof.
move=> np0 rpx; rewrite ltr_pwDl ?ltr01 //.
have sp_gt0 : (size p > 0)%N by rewrite size_poly_gt0.
have lcn0 : `|lead_coef p| != 0 by rewrite normr_eq0 lead_coef_eq0.
have lcp : `|lead_coef p| > 0 by rewrite lt_def lcn0 /=.
have [x_le1|x_gt1] := lerP `|x| 1.
  rewrite (le_trans x_le1) // ler_pdivlMl // mulr1.
  by rewrite polySpred// big_ord_recr/= lerDr sumr_ge0.
have x_gt0 : `|x| > 0 by rewrite (lt_trans ltr01).
have [sp_le1|sp_gt1] := leqP (size p) 1.
  by move: rpx np0; rewrite [p]size1_polyC// hornerC polyC_eq0 => /eqP->.
rewrite ler_pdivlMl//.
pose n := (size p).-1; have n_gt0 : (n > 0)%N by rewrite /n -subn1 subn_gt0.
have : `|p`_n| * `|x| ^+ n <= \sum_(i < n) `|p`_i * x ^+ i|.
  rewrite (le_trans _ (ler_norm_sum _ _ _))//.
  have := rpx; rewrite horner_coef polySpred// !big_ord_recr/=.
  by move=> /(canRL (@addrK _ _))->; rewrite sub0r normrN normrM normrX.
rewrite -[n in _ ^+ n]prednK// exprS mulrA.
rewrite -[X in _ X -> _]ler_pdivlMr ?exprn_gt0// => /le_trans->//.
rewrite polySpred// big_ord_recr/= ler_wpDr// mulr_suml ler_sum => //i _.
rewrite normrM normrX ler_pdivrMr ?exprn_gt0// ler_pM ?exprn_ge0//.
by rewrite ler_weXn2l// 1?ltW// -ltnS prednK//.
Qed.

Lemma root_in_cauchy_bound (p : {poly R}) : p != 0 ->
  {subset root p <= `](- cauchy_bound p), (cauchy_bound p)[ }.
Proof. by move=> p_neq0 x /eqP /(cauchy_boundP p_neq0); rewrite ltr_norml. Qed.

Definition root_cauchy_boundP (p : {poly R}) pN0 x (rpx : root p x) :=
 itvP (root_in_cauchy_bound pN0 rpx).

Lemma le_cauchy_bound p : p != 0 -> {in `]-oo, (- cauchy_bound p)], noroot p}.
Proof.
move=> p_neq0 x; rewrite in_itv /=; apply/contra_leN.
by case/rootP/(cauchy_boundP p_neq0)/ltr_normlP; rewrite ltrNl.
Qed.
Hint Resolve le_cauchy_bound : core.

Lemma ge_cauchy_bound p : p != 0 -> {in `[cauchy_bound p, +oo[, noroot p}.
Proof.
move=> p_neq0 x; rewrite in_itv andbT /=; apply/contra_leN.
by case/rootP/(cauchy_boundP p_neq0)/ltr_normlP; rewrite ltrNl.
Qed.
Hint Resolve ge_cauchy_bound : core.

Lemma cauchy_bound_gt0 p : cauchy_bound p > 0.
Proof. by rewrite ltr_pwDl ?ltr01 // mulrC divr_ge0 ?normr_ge0 ?sumr_ge0. Qed.
Hint Resolve cauchy_bound_gt0 : core.

Lemma cauchy_bound_ge0 p : cauchy_bound p >= 0.
Proof. by rewrite ltW. Qed.
Hint Resolve cauchy_bound_ge0 : core.

Lemma cauchy_bound_neq0 p : cauchy_bound p != 0. Proof. by rewrite gt_eqF. Qed.
Hint Resolve cauchy_bound_neq0 : core.

End CauchyBound.

End PolyRealField.
#[export]
Hint Resolve le_cauchy_bound ge_cauchy_bound : core.
#[export]
Hint Resolve cauchy_bound_gt0 cauchy_bound_ge0 : core.
#[export]
Hint Resolve cauchy_bound_neq0 : core.

(************************************************************)
(* Definitions and properties for polynomials in a rcfType. *)
(************************************************************)
Section PolyRCF.

Variable R : rcfType.

Section Prelim.

Implicit Types a b c : R.
Implicit Types x y z t : R.
Implicit Types p q r : {poly R}.

(* we restate poly_ivt in a nicer way. Perhaps the def of PolyRCF should *)
(* be moved in this file, juste above this section                       *)

Definition poly_ivtW := poly_ivt.

Lemma poly_ivt p a b : a <= b -> p.[a] * p.[b] <= 0 ->
   {x | x \in `[a, b] & root p x}.
Proof.
move=> le_ab sgp; apply/sig2W; have []//= := @poly_ivt _ (p.[b] *: p) a b.
  by rewrite !hornerZ sqr_ge0 mulrC sgp.
move=> x axb; have [|?] := boolP (root p b); last by rewrite rootZ //; exists x.
by move=> rpb; exists b; rewrite // in_itv/= lexx andbT.
Qed.

Lemma poly_ivtoo p a b : a <= b -> p.[a] * p.[b] < 0 ->
   {x | x \in `]a, b[ & root p x}.
Proof.
move=> le_ab; rewrite lt_neqAle mulf_eq0 negb_or -andbA => /and3P[pa0 pb0].
move=> /(poly_ivt le_ab) [c cab rpc].
exists c => //; rewrite in_itv; apply/andP => /=.
by split; rewrite lt_neqAle (itvP cab) andbT; [move: pa0|move: pb0];
   apply: contraNneq; [move->|move<-].
Qed.

Lemma ivt_sign_deprecated (p : {poly R}) (a b : R) :
    a <= b -> sgr p.[a] * sgr p.[b] = -1 ->
  { x : R | x \in `]a, b[ & root p x}.
Proof.
move=> le_ab sgpab_eqN1; apply: poly_ivtoo => //.
by rewrite -sgr_cp0 sgrM sgpab_eqN1.
Qed.

Definition has_ivt_root p a b :=
  if (a <= b) && (p.[a] * p.[b] <= 0) =P true isn't ReflectT pp then None
  else Some (projT1 (poly_ivt (proj1 (andP pp)) (proj2 (andP pp)))).
Notation ivt_root p a b := (odflt 0 (has_ivt_root p a b)).

CoInductive has_itv_root_spec p a b : bool -> option R -> Type :=
| HasItvRoot x of (p.[a] * p.[b] <= 0) & x \in `[a, b] & root p x :
    has_itv_root_spec p a b true (Some x)
| NoItvRoot of (p.[a] * p.[b] > 0) : has_itv_root_spec p a b false None.

Lemma has_itv_rootP p a b : a <= b ->
  has_itv_root_spec p a b (p.[a] * p.[b] <= 0) (has_ivt_root p a b).
Proof.
move=> le_ab; rewrite /has_ivt_root; case: eqP => /= [pp|/negP].
  move: {-}(pp) => /andP[_ pab]; rewrite {1}pab; constructor => //;
  by case: poly_ivt.
by rewrite le_ab /= -ltNge => pab; rewrite lt_geF //; constructor.
Qed.

Lemma some_ivt_root p a b x : has_ivt_root p a b = Some x -> root p x.
Proof.
by rewrite /has_ivt_root; case: eqP => //= pp; case: poly_ivt => //= ??? [<-].
Qed.

Lemma has_ivt_rootE p a b :
   has_ivt_root p a b = (a <= b) && (p.[a] * p.[b] <= 0) :> bool.
Proof. by rewrite /has_ivt_root; case: eqP => //= /negP/negPf->. Qed.

Lemma ivt_root_in p a b : a <= b -> p.[a] * p.[b] <= 0 ->
  ivt_root p a b \in `[a, b].
Proof. by move=> ab; case: has_itv_rootP. Qed.

Lemma ivt_rootP p a b : a <= b -> p.[a] * p.[b] <= 0 ->
  root p (ivt_root p a b).
Proof. by move=> leab; case: has_itv_rootP. Qed.

Lemma sub_cc_itv a b (i : interval R) :
  (a \in i) -> (b \in i) -> (`[a, b] <= i)%O.
Proof.
case: i => [c d]; rewrite !inE/=  !/(_ <= Interval _ _)%O/=.
by move=> /andP[-> _] /andP[_ ->].
Qed.

Lemma sub_oo_itv a b (i : interval R) :
  (a \in i) -> (b \in i) -> (`]a, b[ <= i)%O.
Proof.
case: i => [c d]; rewrite !inE/=  !/(_ <= Interval _ _)%O/=.
move=> /andP[ca _] /andP[_ bd].
by rewrite (le_trans ca) ?bnd_simp// (le_trans _ bd) ?bnd_simp.
Qed.

Lemma polyrN0_itv (i : interval R) (p : {poly R}) : {in i, noroot p} ->
  {in i & , forall y x : R, sgr p.[x] = sgr p.[y]}.
Proof.
move=> hi y x hy hx; wlog xy: x y hx hy / x <= y => [hwlog|].
  by case/orP: (le_total x y)=> xy; [|symmetry]; apply: hwlog.
have hxyi: {subset `[x, y] <= i} by apply/subitvP; rewrite sub_cc_itv.
have [r _ rin|] := @has_itv_rootP p x y xy.
  by rewrite (negPf (hi _ _)) // hxyi.
rewrite -sgr_cp0 sgrM eq_sym; do 2!case: sgzP => //;
by rewrite ?(mul0r, mulr0, mul1r, mulr1, oner_eq0) // => _ _ /eqP.
Qed.

Lemma nth_root x n : x > 0 -> { y | y > 0 & y ^+ (n.+1) = x }.
Proof.
move=> x_gt0; apply/sig2_eqW; pose p := ('X ^+ n.+1 - x%:P).
have xS_ge1: x + 1 >= 1 by rewrite ler_wpDl // ltW.
have xS_ge0: x + 1 > 0 by rewrite (lt_le_trans (@ltr01 _)).
have [//||y /andP[y_ge0 _]] := @poly_ivtW _ p 0 (x + 1); first exact: ltW.
  rewrite !(hornerE, horner_exp) expr0n /= sub0r oppr_le0 (ltW x_gt0) /=.
  by rewrite subr_ge0 (le_trans _ (ler_eXnr _ _)) // ler_wpDr ?ler01.
rewrite /root !(hornerE, horner_exp) subr_eq0 => /eqP x_eq; exists y => //.
rewrite lt_neqAle y_ge0 andbT; apply: contra_eqN x_eq => /eqP<-.
by rewrite eq_sym expr0n gt_eqF.
Qed.

(* REMOVE or DISPLACE *)
Lemma poly_div_factor (a : R) (P : {poly R} -> Prop) : (forall k, P k%:P) ->
  (forall p n k, ~~ root p a -> P p -> P (p * ('X - a%:P) ^+ n.+1 + k%:P)%R) ->
  forall p, P p.
Proof.
move=> Pk Pq p; elim: size {-2}p (leqnn (size p)) => {p} [p|n ihn p size_p].
  by rewrite size_poly_leq0 => /eqP->; apply: Pk.
have [/size1_polyC->//|p_gt1] := leqP (size p) 1.
have p_neq0 : p != 0 by rewrite -size_poly_eq0 -lt0n ltnW.
rewrite (Pdiv.IdomainMonic.divp_eq (monicXsubC a) p).
have [n' [q /implyP rqa pmod_eq]] := multiplicity_XsubC (p %/ ('X - a%:P)) a.
have Xsuba_neq0 : 'X - a%:P != 0 by rewrite -size_poly_eq0 size_XsubC.
have /size1_polyC-> : (size (p %% ('X - a%:P))%R <= 1)%N.
  by rewrite -ltnS (leq_trans (ltn_modpN0 _ _))// ?size_XsubC.
rewrite pmod_eq -mulrA -exprSr; apply: Pq; last apply: ihn.
  by rewrite rqa// divpN0// ?size_XsubC.
have [->//|q_neq0] := eqVneq q 0; first by rewrite size_poly0.
rewrite (@leq_trans (size (q * ('X - a%:P) ^ n')))//.
  rewrite size_Mmonic// ?monic_exp ?monicXsubC//.
  by rewrite size_exp_XsubC addnS/= leq_addr.
rewrite -pmod_eq -ltnS (leq_trans _ size_p)// ltn_divpl//.
by rewrite size_Mmonic// ?monicXsubC// ?size_XsubC ?addn2.
Qed.

Lemma poly_ltsp_roots p (rs : seq R) :
  (size rs >= size p)%N -> uniq rs -> all (root p) rs -> p = 0.
Proof.
move=> hrs urs rrs; apply/eqP; apply: contraLR hrs=> np0.
by rewrite -ltnNge; apply: max_poly_roots.
Qed.

Theorem poly_rolle a b p :
  a < b -> p.[a] = p.[b] -> {c | c \in `]a, b[ & p^`().[c] = 0}.
Proof.
gen have rolle_weak : a b p / a < b -> p.[a] = 0 -> p.[b] = 0 ->
   {c | (c \in `]a, b[) & (p^`().[c] == 0) || (p.[c] == 0)}.
  move=> lab pa0 pb0; have ltab := ltW lab; apply/sig2W.
  have [->|p_neq0] := eqVneq p 0.
    by exists (mid a b); rewrite ?mid_in_itv// derivC horner0 eqxx.
  have [n [p' p'a0 hp]] := multiplicity_XsubC p a; rewrite p_neq0 /= in p'a0.
  case: n hp pa0 p_neq0 pb0 p'a0 => [ | n -> _ p0 pb0 p'a0].
    by rewrite {1}expr0 mulr1 rootE=> ->; move/eqP->.
  have [m [q qb0 hp']] := multiplicity_XsubC p' b.
  rewrite (contraNneq _ p'a0) /= in qb0 => [->|]; first exact: root0.
  case: m hp' pb0 p0 p'a0 qb0=> [|m].
    rewrite {1}expr0 mulr1=> ->; move/eqP.
    rewrite !(hornerE, horner_exp, mulf_eq0).
    by rewrite !expf_eq0 !subr_eq0 !(gt_eqF lab) !andbF !orbF !rootE=> ->.
  move=> -> _ p0 p'a0 qb0; case: (sgrP (q.[a] * q.[b])); first 2 last.
  - move=> /poly_ivtoo [] // c lacb rqc; exists c=> //.
    by rewrite !hornerM (eqP rqc) !mul0r eqxx orbT.
  - move/eqP; rewrite mulf_eq0 (rootPf qb0) orbF; move/eqP=> qa0.
    by move: p'a0; rewrite ?rootM rootE qa0 eqxx.
  move=> hspq; rewrite !derivCE /= !mul1r mulrDl !pmulrn.
  set xan := (('X - a%:P) ^+ n); set xbm := (('X - b%:P) ^+ m).
  have ->: ('X - a%:P) ^+ n.+1 = ('X - a%:P) * xan by rewrite exprS.
  have ->: ('X - b%:P) ^+ m.+1 = ('X - b%:P) * xbm by rewrite exprS.
  rewrite -mulrzl -[_ *~ n.+1]mulrzl.
  have fac : forall x y z : {poly R}, x * (y * xbm) * (z * xan)
    = (y * z * x) * (xbm * xan).
    by move=> x y z; rewrite mulrCA !mulrA [_ * y]mulrC mulrA.
  rewrite !fac -!mulrDl; set r := _ + _ + _.
  case: (@poly_ivtoo (sgr q.[b] *: r) a b) => // [|c lecb].
    rewrite !hornerZ mulrACA -expr2 sqr_sg (rootPf qb0) mul1r.
    rewrite !(subrr, mul0r, mulr0, addr0, add0r, hornerC, hornerXsubC,
      hornerD, hornerN, hornerM, hornerMn) [_ * _%:R]mulrC.
    rewrite mulrACA pmulr_llt0 // mulrACA pmulr_rlt0 ?mulr_gt0 ?ltr0n //.
    by rewrite -opprB mulNr oppr_lt0 mulr_gt0 ?subr_gt0.
  rewrite rootE hornerZ mulf_eq0 sgr_cp0 (rootPf qb0) orFb => rc0.
  by exists c => //; rewrite !hornerM !mulf_eq0 rc0.
move=> lab pab; wlog pb0 : p pab / p.[b] = 0 => [hwlog|].
  case: (hwlog (p - p.[b]%:P)); rewrite ?hornerE ?pab ?subrr //.
  by move=> c acb; rewrite !derivE subr0 => hc; exists c.
move: pab; rewrite pb0=> pa0.
have: (forall rs : seq R, {subset rs <= `]a, b[} ->
    (size p <= size rs)%N -> uniq rs -> all (root p) rs -> p = 0).
  by move=> rs hrs; apply: poly_ltsp_roots.
elim: (size p) a b lab pa0 pb0=> [|n ihn] a b lab pa0 pb0 max_roots.
  rewrite (@max_roots [::]) //=.
  by exists (mid a b); rewrite ?mid_in_itv // derivE horner0.
case: (@rolle_weak a b p); rewrite // ?pa0 ?pb0 //=.
move=> c hc; case: (altP (_ =P 0))=> //= p'c0 pc0; first by exists c.
suff: { d : R | d \in `]a, c[ & (p^`()).[d] = 0 }.
  case=> [d hd] p'd0; exists d=> //.
  by apply: subitvPr hd; rewrite bnd_simp (itvP hc).
  apply: ihn => //; [by rewrite (itvP hc)|exact/eqP|].
move=> rs hrs srs urs rrs; apply: (max_roots (c :: rs))=> //=; last exact/andP.
  move=> x; rewrite in_cons; case/predU1P=> hx; first by rewrite hx.
  have: x \in `]a, c[ by apply: hrs.
  by apply: subitvPr; rewrite bnd_simp (itvP hc).
by rewrite urs andbT; apply/negP => /hrs; rewrite bound_in_itv.
Qed.

Theorem poly_mvt a b p : a < b ->
  {c | c \in `]a, b[ & p.[b] - p.[a] = p^`().[c] * (b - a)}.
Proof.
pose q := (p.[b] - p.[a])%:P * ('X - a%:P) - (b - a)%:P * (p - p.[a]%:P).
move=> lt_ab; have [//||c le_acb q'x0] := @poly_rolle a b q.
  by rewrite /q !hornerE !(subrr,mulr0) mulrC subrr.
exists c=> //; move: q'x0; rewrite /q !derivE !(mul0r,add0r,subr0,mulr1).
by move/eqP; rewrite !hornerE mulrC subr_eq0; move/eqP.
Qed.

Lemma poly_lipshitz p a b :
  { k | k >= 1 & {in `[a, b] &, forall x y, `|p.[y] - p.[x]| <= k * `|y - x| }}.
Proof.
have [ub p_le] := @poly_itv_bound _ p^`() a b; exists (1 + `|ub|).
  by rewrite lerDl.
move=> x y xi yi; wlog lt_xy : x y xi yi / x < y => [hw|].
  set d := `|y - _|; have [/hw->//|xy|xy//] := ltrgtP x y; last first.
    by rewrite /d xy !subrr normr0 mulr0.
  by rewrite /d (distrC y) (distrC p.[y]) hw.
have [c ci ->] := poly_mvt p lt_xy; rewrite normrM ler_pM2r ?p_le //.
  by rewrite ?normr_gt0 ?subr_eq0 gt_eqF.
rewrite ler_wpDl // (le_trans _ (ler_norm _)) // p_le //.
by have: c \in `[a, b] by apply: subitvP ci; rewrite sub_oo_itv.
Qed.

Lemma poly_cont x p e : e > 0 ->
  exists2 d, d > 0 & forall y, `|y - x| < d -> `|p.[y] - p.[x]| < e.
Proof.
move=> e_gt0; have [k k_ge1 kP] := poly_lipshitz p (x - e) (x + e).
have k_gt0 : k > 0 by rewrite (lt_le_trans ltr01).
exists (e / k) => [|y]; first by rewrite mulr_gt0 ?invr_gt0.
have [y_small|y_big] := lerP `|y - x| e.
  rewrite ltr_pdivlMr // mulrC; apply/le_lt_trans/kP => //;
  by rewrite -![_ \in _]ler_distl ?subrr ?normr0 // ?ltW.
by move=> /(lt_trans y_big); rewrite ltr_pMr // invf_gt1 // le_gtF.
Qed.

Lemma ler_hornerW a b p : (forall x, x \in `]a, b[ -> p^`().[x] >= 0) ->
  {in `[a, b] &, {homo horner p : x y / x <= y}}.
Proof.
move=> der_nneg x y axb ayb; rewrite le_eqVlt => /orP[/eqP->//|ltxy].
have [c xcy /(canRL (@subrK _ _))->]:= poly_mvt p ltxy.
rewrite lerDr mulr_ge0 ?subr_ge0 ?(ltW ltxy) ?der_nneg //.
by apply: subitvP xcy; rewrite /(_ <= _)%O/= !bnd_simp ?(itvP axb) ?(itvP ayb).
Qed.

End Prelim.

Lemma le_itv (a a' b b' : itv_bound R) :
  (Interval a b <= Interval a' b')%O = (a' <= a)%O && (b <= b')%O.
Proof. by []. Qed.

Section MonotonictyAndRoots.

Section DerPos.

Variable (p : {poly R}).

Variables (a b : R).

Hypothesis der_gt0 : forall x, x \in `]a, b[ -> (p^`()).[x] > 0.

Lemma ltr_hornerW : {in `[a, b] &, {homo horner p : x y / x < y}}.
Proof.
move=> x y axb ayb ltxy; have [c xcy /(canRL (@subrK _ _))->]:= poly_mvt p ltxy.
rewrite ltrDr mulr_gt0 ?subr_gt0 ?der_gt0 //.
apply: subitvP xcy; rewrite le_itv !bnd_simp.
by rewrite /= (itvP axb) (itvP ayb).
Qed.

Lemma ler_horner : {in `[a, b] &, {mono horner p : x y / x <= y}}.
Proof. exact/le_mono_in/ltr_hornerW. Qed.

Lemma ltr_horner : {in `[a, b] &, {mono horner p : x y / x < y}}.
Proof. exact/leW_mono_in/ler_horner. Qed.

Lemma derp_inj : {in `[a, b] &, injective (horner p)}.
Proof. exact/inc_inj_in/ler_horner. Qed.

Lemma derpr x : x \in `]a, b] -> p.[x] > p.[a].
Proof.
by move=> axb; rewrite ltr_horner ?(itvP axb) // subset_itv_oc_cc.
Qed.

Lemma derpl x : x \in `[a, b[ -> p.[x] < p.[b].
Proof.
by move=> axb; rewrite ltr_horner ?(itvP axb) // subset_itv_co_cc.
Qed.

Lemma derprW x : x \in `[a, b] -> p.[x] >= p.[a].
Proof. by move=> axb; rewrite ler_horner ?(itvP axb). Qed.

Lemma derplW x : x \in `[a, b] -> p.[x] <= p.[b].
Proof. by move=> axb; rewrite ler_horner ?(itvP axb). Qed.
End DerPos.

Section NoRoot_sg.

Variable (p : {poly R}).

Variables (a b c : R).

Hypothesis lt_ab : a < b.
Hypothesis derp_neq0 : {in `]a, b[, noroot p^`()}.
Let mid_in : mid a b \in `]a, b[. Proof. exact: mid_in_itv. Qed.
Hint Resolve mid_in : core.

Local Notation s := (p^`().[mid a b] < 0).
Local Notation sp' := ((- 1) ^+ s).
Let q := (sp' *: p).

Lemma sgr_sign : sgr ((-1) ^+ s) = (-1) ^+ s :> R.
Proof. by case: s; rewrite ?(sgr1, sgrN1). Qed.

Fact signpE : p = (sp' *: q).
Proof. by rewrite scalerA [_ ^+ _ * _]sqrr_sign scale1r. Qed.

Fact sgp x : sgr p.[x] = sp' * sgr q.[x].
Proof. by rewrite {1}signpE hornerZ sgrM sgr_sign. Qed.

Fact derq_gt0 x : x \in `]a, b[ -> (q^`()).[x] > 0.
Proof.
move=> hx; rewrite derivZ hornerZ -sgr_cp0 neqr0_sign ?(derp_neq0 _) //.
rewrite sgrM sgr_id mulr_sg_eq1 ?derp_neq0 //=.
by apply/eqP; apply: (@polyrN0_itv `]a, b[).
Qed.
Hint Resolve derq_gt0 : core.

Lemma lgtr_horner : {in `[a, b] &, forall x y,
  (p.[x] < p.[y]) = (sp' * x < sp' * y)}.
Proof.
move=> x y axb ayb; rewrite /= [in LHS]signpE ![(_ *: q).[_]]hornerZ.
by case: s; rewrite ?mul1r ?mulN1r ?ltrN2 (ltr_horner derq_gt0).
Qed.

Lemma lger_horner : {in `[a, b] &, forall x y,
  (p.[x] <= p.[y]) = (sp' * x <= sp' * y)}.
Proof.
move=> x y axb ayb; rewrite /= [in LHS]signpE ![(_ *: q).[_]]hornerZ.
by case: s; rewrite ?mul1r ?mulN1r ?lerN2 (ler_horner derq_gt0).
Qed.

Lemma horner_inj : {in `[a, b] &, injective (horner p)}.
Proof.
move=> x y xab yab; rewrite signpE ![(_ *: q).[_]]hornerE.
by move=> /mulfI /(derp_inj derq_gt0)-> //; rewrite signr_eq0.
Qed.

Lemma uniq_root : {in `[a, b] &, forall x y, root p x -> root p y -> x = y}.
Proof. by move=> x y ?? /eqP? /eqP rpy; apply: horner_inj; rewrite //rpy. Qed.

Lemma sgrB (x y : R) : sgr (x - y) = (- 1) ^+ (x < y)%R *+ (x != y).
Proof.
case: ltrgtP => //= [xy|xy|->]; last by rewrite subrr sgr0.
  by rewrite ltr0_sg ?subr_lt0.
by rewrite gtr0_sg ?subr_gt0.
Qed.

Lemma root_sgp : {in `[a, b] &, forall x y, root p x ->
  sgr p.[y] = (- 1) ^+ s * sgr (y - x)}.
Proof.
move=> x y xab yab rpx; rewrite {1}signpE hornerZ sgrM sgr_sign; congr (_ * _).
have rqx : root q x by rewrite /root hornerZ mulf_eq0 [p.[_] == _]rpx orbT.
rewrite sgrB; have [xy|xy|<-]/= := ltrgtP x y; last first.
- by rewrite hornerZ sgrM (eqP rpx) sgr0 mulr0.
- by apply/eqP; rewrite sgr_cp0 -(eqP rqx) (ltr_horner derq_gt0).
- by apply/eqP; rewrite sgr_cp0 -(eqP rqx) (ltr_horner derq_gt0).
Qed.


Lemma root_has_ivt r : r \in `[a, b] -> root p r ->
  {in `[a, r] & `[r, b], forall x y, p.[x] * p.[y] <= 0}.
Proof.
move=> rab rpr x y xar yrb; rewrite -sgr_le0 sgrM.
have xab : x \in `[a, b]
  by apply: subitvP xar; rewrite /= le_itv !bnd_simp ?(itvP rab).
have yab : y \in `[a, b]
  by apply: subitvP yrb; rewrite /= le_itv !bnd_simp ?(itvP rab).
rewrite ?(root_sgp _ _ rpr)// mulrACA [_ ^+ _ * _]sqrr_sign mul1r -sgrM sgr_le0.
by rewrite mulr_le0_ge0 ?subr_ge0 ?subr_le0 ?(itvP xar) ?(itvP yrb).
Qed.

Lemma noroot_noivt : {in `[a, b], forall r, ~~ root p r} ->
  {in `[a, b] &, forall x y, p.[x] * p.[y] > 0}.
Proof.
move=> rpr x y xar yrb; wlog lt_xy : x y xar yrb / x <= y => [hw|].
  by have /orP[/hw->//|/hw] := le_total x y; rewrite mulrC; apply.
rewrite ltNge; case: has_itv_rootP => // r _ r_in.
rewrite (negPf (rpr _ _)) //; apply: subitvP r_in;
by rewrite le_itv !bnd_simp /= ?(itvP xar) ?(itvP yrb).
Qed.

Fact gtr0_sgp x : 0 < q.[x] -> sgr p.[x] = sp'.
Proof. by move=> qx_gt0; rewrite sgp gtr0_sg ?mulr1. Qed.

Fact ltr0_sgpN x : q.[x] < 0 -> sgr p.[x] = - sp'.
Proof. by move=> qx_gt0; rewrite sgp ltr0_sg ?mulrN1. Qed.

Lemma root_dersr : p.[a] = 0 -> {in `]a, b], forall x, sgr p.[x] = sp'}.
Proof.
move=> pa0 x xab; have qa0 : q.[a] = 0 by rewrite hornerE pa0 mulr0.
by rewrite gtr0_sgp// -qa0 (derpr derq_gt0).
Qed.

Lemma derspr : sgr p.[a] = sp' -> {in `[a, b], forall x, sgr p.[x] = sp'}.
Proof.
move=> pa_sp' x xab; rewrite gtr0_sgp// (lt_le_trans _ (derprW derq_gt0 _))//.
by rewrite hornerE -sgr_cp0 sgrM sgr_sign pa_sp' [_ * _]sqrr_sign.
Qed.

Lemma root_dersl : p.[b] = 0 -> {in `[a, b[, forall x, sgr p.[x] = - sp'}.
Proof.
move=> pb0 x xab; have qb0 : q.[b] = 0 by rewrite hornerE pb0 mulr0.
by rewrite ltr0_sgpN// -qb0 (derpl derq_gt0).
Qed.

Lemma derspl : sgr p.[b] = - sp' -> forall x, x \in `[a, b] -> sgr p.[x] = - sp'.
Proof.
move=> pbNsp' x xab; rewrite ltr0_sgpN// (le_lt_trans (derplW derq_gt0 _))//.
by rewrite hornerE -sgr_cp0 sgrM sgr_sign pbNsp' mulrN [_ * _]sqrr_sign.
Qed.

End NoRoot_sg.

Section DerNeg.

Variable (p : {poly R}).

Variables (a b : R).

Hypothesis der_neg : forall x, x \in `]a, b[ -> (p^`()).[x] < 0.
Let dern_gt0 x : x \in `]a, b[ -> ((- p)^`()).[x] > 0.
Proof. by move=> axb; rewrite derivN hornerN oppr_gt0 der_neg. Qed.

Lemma gtr_hornerW : {in `[a, b] &, {homo horner p : x y /~ x < y}}.
Proof.
by move=> x y axb ayb yx; rewrite -ltrN2 -!hornerN (ltr_hornerW dern_gt0).
Qed.

Lemma ger_horner : {in `[a, b] &, {mono horner p : x y /~ x <= y}}.
Proof. exact/le_nmono_in/gtr_hornerW. Qed.

Lemma gtr_horner : {in `[a, b] &, {mono horner p : x y /~ x < y}}.
Proof. exact/leW_nmono_in/ger_horner. Qed.

Lemma dernr x : x \in `]a, b] -> p.[x] < p.[a].
Proof.
by move=> axb; rewrite gtr_horner ?(itvP axb) //; apply: subset_itv_oc_cc.
Qed.

Lemma dernl x : x \in `[a, b[ -> p.[x] > p.[b].
Proof.
by move=> axb; rewrite gtr_horner ?(itvP axb) //; apply: subset_itv_co_cc.
Qed.

Lemma dernrW x : x \in `[a, b] -> p.[x] <= p.[a].
Proof. by move=> axb; rewrite ger_horner ?(itvP axb). Qed.

Lemma dernlW x : x \in `[a, b] -> p.[x] >= p.[b].
Proof. by move=> axb; rewrite ger_horner ?(itvP axb). Qed.

End DerNeg.


Variable (p : {poly R}) (a b : R).

Section der_root.

Hypothesis der_pos : forall x, x \in `]a, b[ ->  (p^`()).[x] > 0.

Lemma derp_root : a <= b -> p.[a] * p.[b] < 0 ->
  { r : R |
    [/\ forall x, x \in `[a, r[ -> p.[x] < 0,
      p.[r] = 0,
      r \in `]a, b[ &
      forall x, x \in `]r, b] -> p.[x] > 0] }.
Proof.
move=> leab hpab; have [r arb pr0] := poly_ivtoo leab hpab.
exists r; split => //; last 2 first.
- by move/eqP: pr0.
- move=> x rxb; have hd : forall t, t \in `]r, b[ ->  0 < (p^`()).[t].
    by move=> t ht; rewrite der_pos // ?(subitvPl _ ht) /<=%O //= ?(itvP arb).
  by rewrite (le_lt_trans _ (derpr hd _)) ?(eqP pr0).
- move=> x rxb; have hd : forall t, t \in `]a, r[ ->  0 < (p^`()).[t].
    by move=> t ht; rewrite der_pos // ?(subitvPr _ ht) /<=%O //= ?(itvP arb).
  by rewrite (lt_le_trans (derpl hd _)) ?(eqP pr0).
Qed.

End der_root.

End MonotonictyAndRoots.

Section RootsOn.

Variable T : predType R.

Definition roots_on (p : {poly R}) (i : T) (s : seq R) :=
  forall x, (x \in i) && (root p x) = (x \in s).

Lemma roots_onP p i s : roots_on p i s -> {in i, root p =1 mem s}.
Proof. by move=> hp x hx; move: (hp x); rewrite hx. Qed.

Lemma roots_on_in p i s :
  roots_on p i s -> forall x, x \in s -> x \in i.
Proof. by move=> hp x; rewrite -hp; case/andP. Qed.

Lemma roots_on_root p i s :
  roots_on p i s -> forall x, x \in s -> root p x.
Proof. by move=> hp x; rewrite -hp; case/andP. Qed.

Lemma root_roots_on p i s :
  roots_on p i s -> forall x, x \in i -> root p x -> x \in s.
Proof. by move=> hp x; rewrite -hp=> ->. Qed.

Lemma roots_on_opp p i s : roots_on (- p) i s -> roots_on p i s.
Proof. by move=> hp x; rewrite -hp rootN. Qed.

Lemma roots_on_nil p i : roots_on p i [::] -> {in i, noroot p}.
Proof. by move=> hp x hx; move: (hp x); rewrite in_nil hx /=; move->. Qed.

Lemma roots_on_same s' p i s : s =i s' -> (roots_on p i s <-> roots_on p i s').
Proof. by move=> hss'; split=> hs x; rewrite (hss', (I, hss')). Qed.

End RootsOn.


(* (* Symmetry of center a *) *)
(* Definition symr (a x : R) := a - x. *)

(* Lemma symr_inv : forall a, involutive (symr a). *)
(* Proof. by move=> a y; rewrite /symr opprD addrA subrr opprK add0r. Qed. *)

(* Lemma symr_inj : forall a, injective (symr a). *)
(* Proof. by move=> a; apply: inv_inj; apply: symr_inv. Qed. *)

(* Lemma ltr_sym : forall a x y, (symr a x < symr a y) = (y < x). *)
(* Proof. by move=> a x y; rewrite lterD2rr lterNr opprK. Qed. *)

(* Lemma symr_add_itv : forall a b x,  *)
(*   (a < symr (a + b) x < b) = (a < x < b). *)
(* Proof.  *)
(* move=> a b x; rewrite andbC.    *)
(* by rewrite lter_subrA lterD2rr -lter_addlA lterD2rl. *)
(* Qed. *)

Lemma roots_on_comp p a b s :
  roots_on (p \Po (-'X)) `](-b), (-a)[ (map (-%R) s) <-> roots_on p `]a, b[ s.
Proof.
split=> /= hs x; rewrite ?root_comp ?hornerE.
  move: (hs (- x)); rewrite (mem_map oppr_inj).
  by rewrite root_comp ?hornerE oppr_itv !opprK.
by rewrite -[x]opprK oppr_itv /= (mem_map oppr_inj) -(hs (- x)) !opprK.
Qed.

Lemma min_roots_on p a b x s :
    all (> x) s -> roots_on p `]a, b[ (x :: s) ->
  [/\ x \in `]a, b[, roots_on p `]a, x[ [::], root p x & roots_on p `]x, b[ s].
Proof.
move=> lxs hxs.
have hx: x \in `]a, b[ by rewrite (roots_on_in hxs) ?mem_head.
rewrite hx (roots_on_root hxs) ?mem_head //.
split=> // y; move: (hxs y); rewrite ?in_nil ?in_cons /=.
  case hy: (y \in `]a, x[)=> //=.
  rewrite (subitvPr _ hy) /<=%O /= ?lt_eqF ?(itvP hx) ?(itvP hy) //= => ->.
  by apply/negP; move/allP: lxs=> lxs /lxs; rewrite ?(itvP hy).
case: eqVneq => [-> _|eyx].
  by rewrite boundl_in_itv; apply/esym/negP; move/(allP lxs); rewrite ltxx.
case: root; rewrite !(andbT, andbF) // !in_itv /=.
case: (boolP (y \in s)) (allP lxs y) => [_ /(_ isT) -> /andP [] // | ys _].
by apply/contraFF => /andP [xy ->]; rewrite (lt_trans _ xy) ?(itvP hx).
Qed.

Lemma max_roots_on p a b x s :
    all (< x) s -> roots_on p `]a, b[ (x :: s) ->
  [/\ x \in `]a, b[, roots_on p `]x, b[ [::], root p x & roots_on p `]a, x[ s].
Proof.
move/allP=> lsx /roots_on_comp/=/min_roots_on[].
  apply/allP=> y; rewrite -[y]opprK (mem_map oppr_inj).
  by move/lsx; rewrite ltrN2.
rewrite oppr_itv root_comp !hornerE !opprK=> -> rxb -> rax.
by split=> //; apply/roots_on_comp.
Qed.

Lemma roots_on_cons p a b r s :
  sorted <%R (r :: s) -> roots_on p `]a, b[ (r :: s) -> roots_on p `]r, b[ s.
Proof.
move=> /= hrs hr.
have allrs := order_path_min lt_trans hrs.
by case: (min_roots_on allrs hr).
Qed.
(* move=> p a b r s hp hr x; apply/andP/idP. *)
(*   have:= (order_path_min (@ltr_trans _) hp) => /=; case/andP=> ar1 _. *)
(*   case; move/ooitvP=> rxb rpx; move: (hr x); rewrite in_cons rpx andbT. *)
(*   by rewrite rxb andbT (ltr_trans ar1) 1?eq_sym ?ltr_eqF  ?rxb. *)
(* move=> spx. *)
(* have xrsp: x \in r :: s by rewrite in_cons spx orbT. *)
(* rewrite (roots_on_root hr) //. *)
(* rewrite (roots_on_in hr xrsp); move: hp => /=; case/andP=> _. *)
(* by move/(order_path_min (@ltr_trans _)); move/allP; move/(_ _ spx)->. *)
(* Qed. *)

Lemma roots_on_rcons : forall p a b r s,
  sorted <%R (rcons s r) -> roots_on p `]a, b[ (rcons s r)
  -> roots_on p `]a, r[ s.
Proof.
move=> p a b r s; rewrite -{1}[s]revK -!rev_cons rev_sorted /=.
move=> hrs /(@roots_on_same _ _ _ _ (r::s)) hr.
have allrrs := order_path_min (rev_trans lt_trans) hrs.
have allrs: all (< r) s.
  by apply/allP => x hx; apply: (allP allrrs); rewrite mem_rev.
by case: (max_roots_on allrs (hr _))=> // x; rewrite mem_rcons.
Qed.


(* move=> p a b r s; rewrite -{1}[s]revK -!rev_cons rev_sorted. *)
(* rewrite  [r :: _]lock /=; unlock; move=> hp hr x; apply/andP/idP. *)
(*   have:= (order_path_min (rev_trans (@ltr_trans _)) hp) => /=. *)
(*   case/andP=> ar1 _; case; move/ooitvP=> axr rpx. *)
(*   move: (hr x); rewrite mem_rcons in_cons rpx andbT axr andTb. *)
(*   by rewrite ((rev_trans (@ltr_trans _) ar1)) ?ltr_eqF ?axr. *)
(* move=> spx. *)
(* have xrsp: x \in rcons s r by rewrite mem_rcons in_cons spx orbT. *)
(* rewrite (roots_on_root hr) //. *)
(* rewrite (roots_on_in hr xrsp); move: hp => /=; case/andP=> _. *)
(* move/(order_path_min (rev_trans (@ltr_trans _))); move/allP.  *)
(* by move/(_ x)=> -> //; rewrite mem_rev. *)
(* Qed. *)

Lemma no_roots_on (p : {poly R}) a b :
  {in `]a, b[, noroot p} -> roots_on p `]a, b[ [::].
Proof. by move=> hr x; case: (boolP (x \in _)) => //= /hr /negPf. Qed.

Lemma monotonic_rootN (p : {poly R}) (a b : R) :
    {in `]a, b[,  noroot p^`()} ->
  ((roots_on p `]a, b[ [::]) + ({r : R | roots_on p `]a, b[ [:: r]}))%type.
Proof.
(move=> hp'; case: (ltrP a b); last first) => leab.
  by left => x; rewrite in_nil itv_ge // -leNgt.
wlog {hp'} hp'sg: p / forall x, x \in `]a, b[ -> sgr (p^`()).[x] = 1.
  move=> hwlog; move: (mid_in_itvoo leab) (polyrN0_itv hp') => hm /(_ _ _ hm).
  case: (sgrP _.[mid a b])=> hpm.
  - by move: (hp' _ hm); rewrite rootE hpm eqxx.
  - by move/(hwlog p).
  - move=> hp'N; case: (hwlog (-p))=> [x|h|[r hr]].
    * by rewrite derivE hornerN sgrN=> /hp'N->; rewrite opprK.
    * by left; apply: roots_on_opp.
    * by right; exists r; apply: roots_on_opp.
have hp'pos x : x \in `]a, b[ -> (p^`()).[x] > 0.
  by move=> /hp'sg /eqP; rewrite sgr_cp0.
case: (lerP 0 p.[a]) => ha.
  left; apply: no_roots_on => x axb; rewrite rootE gt_eqF //.
  by rewrite (le_lt_trans _ (derpr hp'pos _))// (subitvPr _ axb) /<=%O /=.
case: (lerP p.[b] 0) => hb.
  left => x; case: (boolP (x \in _)) => //= axb; rewrite rootE lt_eqF //.
  by rewrite (lt_le_trans (derpl hp'pos _)) // (subitvPl _ axb) /<=%O /=.
case: (derp_root hp'pos (ltW leab) _) => [|r [h1 h2 h3] h4];
  first by rewrite pmulr_llt0.
right; exists r => x; rewrite in_cons in_nil (itv_splitUeq h3).
have [->|exr] := eqVneq; rewrite ?orbT ?orbF /=; first by apply/eqP.
case: rootP => px0; rewrite (andbT, andbF) //; apply/negP; case/orP=> hx.
  by move: (h1 x); rewrite (subitvPl _ hx) /<=%O //= px0 ltxx; move/implyP.
by move: (h4 x); rewrite (subitvPr _ hx) /<=%O //= px0 ltxx; move/implyP.
Qed.

(* Inductive polN0 : Type := PolN0 : forall p : {poly R}, p != 0 -> polN0. *)

(* Coercion pol_of_polN0 i := let: PolN0 p _ := i in p. *)

(* Canonical Structure polN0_subType := [subType for pol_of_polN0]. *)
(* Definition polN0_eqMixin := Eval hnf in [eqMixin of polN0 by <:]. *)
(* Canonical Structure polN0_eqType := *)
(*   Eval hnf in EqType polN0 polN0_eqMixin. *)
(* Definition polN0_choiceMixin := [choiceMixin of polN0 by <:]. *)
(* Canonical Structure polN0_choiceType := *)
(*   Eval hnf in ChoiceType polN0 polN0_choiceMixin. *)

(* Todo : Lemmas about operations of intervall :
   itversection, restriction and splitting *)
Lemma cat_roots_on (p : {poly R}) a b x :
    x \in `]a, b[ -> ~~ (root p x) ->
    forall s s', sorted <%R s -> sorted <%R s' ->
    roots_on p `]a, x[ s -> roots_on p `]x, b[ s' ->
  roots_on p `]a, b[ (s ++ s').
Proof.
move=> hx /= npx0 s; elim: s a hx => [|y s ihs] a hx s' //= ss ss'.
  move/roots_on_nil=> hax hs' y; rewrite -hs' (itv_splitUeq hx).
  case: eqP => [->|_]; rewrite ?(negPf npx0) ?andbF //=.
  by case: (boolP (y \in `]a, x[)) => [/hax/negPf ->|]; rewrite ?andbF.
move/min_roots_on; rewrite (order_path_min lt_trans) //.
case=> // hy hay py0 hs hs' z.
rewrite in_cons (@itv_splitUeq _ _ y).
  by rewrite (subitvPr _ hy) /<=%O //= (itvP hx).
have [->|ezy] := eqVneq; rewrite ?orbT //= -(ihs y) //.
- by rewrite in_itv /= (itvP hx) (itvP hy).
- exact: path_sorted ss.
- by case: (z \in `]y, b[); rewrite ?orbF ?orbT //= (hay z).
Qed.

Variant roots_spec (p : {poly R}) (i : pred R) (s : seq R) :
  {poly R} -> bool -> seq R -> Type :=
| Roots0 of p = 0 :> {poly R} & s = [::] : roots_spec p i s 0 true [::]
| Roots of p != 0 & roots_on p i s
  & sorted <%R s : roots_spec p i s p false s.

(* still much too long *)
Lemma itv_roots (p :{poly R}) (a b : R) :
  {s : seq R & roots_spec p (topred `]a, b[) s p (p == 0) s}.
Proof.
elim: (size p) {-2}p (leqnn (size p)) a b => {p} [|n ihn] p sp a b.
  by move/size_poly_leq0P: sp => ->; rewrite eqxx; exists [::]; constructor.
case: eqVneq => [->|p0]; first by exists [::]; constructor.
case: (boolP (p^`() == 0)) => [|p'0].
  rewrite -derivn1 -derivnPpoly0 => /size1_polyC pC; exists [::].
  by constructor=> // x; rewrite pC rootC -polyC_eq0 -pC (negPf p0) andbF.
have {}/ihn /(_ a b) [sp'] : (size p^`() <= n)%N.
  rewrite -ltnS; apply: leq_trans sp; rewrite size_deriv prednK // lt0n.
  by rewrite size_poly_eq0 p0.
elim: sp' a => [|r1 sp' hsp'] a hp'.
  case: hp' p'0 => //= p'0 /roots_on_nil /monotonic_rootN [h| [r rh]] _ _.
    by exists [::]; constructor.
  by exists [:: r]; constructor; rewrite //= andbT.
case: hp' p'0 => //= p'0 hroots' hpath' _.
case: (min_roots_on _ hroots') => [|hr1 har1 p'r10 hr1b].
  by rewrite order_path_min //; apply: lt_trans.
case: (hsp' r1) p0 => [|s].
  by rewrite (negPf p'0); constructor; rewrite // (path_sorted hpath').
case; rewrite ?eqxx // => p0 hroot hsort _.
move/monotonic_rootN: (roots_on_nil har1).
case pr1 : (root p r1); case => hrootsl; last 2 first.
- exists s; constructor=> //.
  by rewrite -[s]cat0s; apply: (cat_roots_on hr1); rewrite // pr1.
- case: hrootsl=> r hr; exists (r::s); constructor=> //=.
    by rewrite -cat1s; apply: (cat_roots_on hr1); rewrite // pr1.
  rewrite path_min_sorted //; apply/allP=> y; rewrite -hroot; case/andP=> hy _.
  rewrite (lt_trans (_ : _ < r1)) ?(itvP hy) //.
  by rewrite (itvP (roots_on_in hr (mem_head _ _))).
- exists (r1::s); constructor=> //=; last first.
    rewrite path_min_sorted //; apply/allP => y; rewrite -hroot.
    by case/andP => /itvP->.
  move=> x; rewrite in_cons; have [->|exr1] /= := eqVneq; first by rewrite hr1.
  rewrite -hroot (itv_splitUeq hr1) (negPf exr1) /=.
  by case: (_ \in `]r1, _[); rewrite (orbT, orbF).
- case: hrootsl => r0 /min_roots_on [] // hr0 har0 pr0 hr0r1.
  exists [:: r0, r1 & s]; constructor=> //=; last first.
    rewrite (itvP hr0) /= path_min_sorted //; apply/allP=> y.
    by rewrite -hroot; case/andP => /itvP ->.
  move=> y; rewrite !in_cons (itv_splitUeq hr1) (itv_splitUeq hr0).
  have [->|eyr0] := eqVneq y r0; rewrite ?orbT ?pr0 //=.
  have [->|eyr1] := eqVneq y r1; rewrite ?orbT ?pr1 //=.
  move: (hr0r1 y) (har0 y); rewrite -!hroot.
  case: (_ \in `]r0, r1[) => /= [->|_]; rewrite ?andbF ?orbF //.
  by case: (_ \in `]a, r0[) => /= [->|_]; rewrite ?andbF.
Qed.

Definition roots (p : {poly R}) a b := projT1 (itv_roots p a b).

Lemma rootsP p a b :
  roots_spec p (topred `]a, b[) (roots p a b) p (p == 0) (roots p a b).
Proof. by rewrite /roots; case: itv_roots. Qed.

Lemma roots0 a b : roots 0 a b = [::].
Proof. by case: rootsP=> //=; rewrite eqxx. Qed.

Lemma roots_on_roots : forall p a b, p != 0 ->
  roots_on p `]a, b[ (roots p a b).
Proof. by move=> a b p; case: rootsP. Qed.
Hint Resolve roots_on_roots : core.

Lemma sorted_roots a b p : sorted <%R (roots p a b).
Proof. by case: rootsP. Qed.
Hint Resolve sorted_roots : core.

Lemma path_roots p a b : path <%R a (roots p a b).
Proof.
case: rootsP=> //= p0 hp sp; rewrite path_min_sorted //.
by apply/allP=> y; rewrite -hp; case/andP => /itvP ->.
Qed.
Hint Resolve path_roots : core.

Lemma root_is_roots (p : {poly R}) (a b : R) :
   p != 0 -> forall x, x \in `]a, b[ -> root p x = (x \in roots p a b).
Proof. by case: rootsP=> // p0 hs ps _ y hy /=; rewrite -hs hy. Qed.

Lemma root_in_roots (p : {poly R}) a b :
  p != 0 -> forall x, x \in `]a, b[ -> root p x -> x \in (roots p a b).
Proof. by move=> p0 x axb rpx; rewrite -root_is_roots. Qed.

Lemma root_roots p a b x : x \in roots p a b -> root p x.
Proof. by case: rootsP=> // p0 <- _ /andP []. Qed.

Lemma roots_nil p a b : p != 0 ->
  roots p a b = [::] -> {in `]a, b[, noroot p}.
Proof.
case: rootsP => // p0 hs ps _ s0 x axb.
by move: (hs x); rewrite s0 in_nil !axb /= => ->.
Qed.

Lemma roots_in p a b x : x \in roots p a b -> x \in `]a, b[.
Proof. by case: rootsP=> //= np0 ron_p *; apply: (roots_on_in ron_p). Qed.

Lemma rootsEba p a b : b <= a -> roots p a b = [::].
Proof.
case: rootsP=> // p0; case: (roots _ _ _) => [|x s] hs ps ba //;
by move: (hs x); rewrite itv_ge -?leNgt //= mem_head.
Qed.

Lemma roots_on_uniq p a b s1 s2 :
    sorted <%R s1 -> sorted <%R s2 ->
  roots_on p `]a, b[ s1 -> roots_on p `]a, b[ s2 -> s1 = s2.
Proof.
wlog: s1 s2 / (size s1 <= size s2)%N => [hwlog ? ? ? ?|].
  by case: (leqP (size s1) (size s2)) => [|/ltnW] /hwlog ->.
elim: s1 p a b s2 => [| r1 s1 ih] p a b [| r2 s2] les12 ps1 ps2 rs1 rs2 //=.
  have rpr2 : root p r2 by apply: (roots_on_root rs2); rewrite mem_head.
  have abr2 : r2 \in `]a, b[ by apply: (roots_on_in rs2); rewrite mem_head.
  by have:= (rs1 r2); rewrite rpr2 !abr2 in_nil.
have er1r2 : r1 = r2.
  move: (rs1 r2) (rs2 r1); rewrite rs2 rs1 !mem_head !in_cons //=.
  move=> /esym /predU1P [-> //|hr2] /esym /predU1P [-> //|hr1].
  move/(order_path_min lt_trans)/allP/(_ r2 hr2): ps1 => h1.
  move/(order_path_min lt_trans)/allP/(_ r1 hr1)/(lt_trans h1): ps2.
  by rewrite ltxx.
congr (_ :: _) => //; rewrite er1r2 in ps1 rs1.
move: (roots_on_cons ps1 rs1) (roots_on_cons ps2 rs2).
exact: ih (path_sorted ps1) (path_sorted ps2).
Qed.

Lemma roots_eq (p q : {poly R}) (a b : R) :
    p != 0 -> q != 0 ->
  ({in `]a, b[, root p =1 root q} <-> roots p a b = roots q a b).
Proof.
move=> p0 q0; split=> hpq; last first.
  by move=> x hx; rewrite !(root_is_roots _ hx) // hpq.
apply: (@roots_on_uniq p a b); rewrite ?path_roots //.
  exact: roots_on_roots.
move=> x; case hx: (_ \in _).
  by rewrite -hx hpq //; apply: roots_on_roots.
by rewrite /= -(andFb (q.[x] == 0)) -hx; apply: roots_on_roots.
Qed.

Lemma roots_opp p : roots (- p) =2 roots p.
Proof.
move=> a b; have [->|p0] := eqVneq p 0; first by rewrite oppr0.
by apply/roots_eq=> [||x]; rewrite ?oppr_eq0 ?p0 ?rootN.
Qed.

Lemma no_root_roots (p : {poly R}) a b :
  {in `]a, b[ , noroot p} -> roots p a b = [::].
Proof.
move=> hr; case: rootsP => // p0 hs ps.
apply: (@roots_on_uniq p a b)=> // x; rewrite in_nil.
by apply/negP; case/andP => /hr/negPf->.
Qed.

Lemma head_roots_on_ge p a b s :
  a < b -> roots_on p `]a, b[ s -> a < head b s.
Proof.
case: s => [|x s] ab // /(_ x).
by rewrite in_cons eqxx; case/andP; case/andP.
Qed.

Lemma head_roots_ge : forall p a b, a < b -> a < head b (roots p a b).
Proof.
by move=> p a b; case: rootsP=> // *; apply: head_roots_on_ge.
Qed.

Lemma last_roots_on_le p a b s :
  a < b -> roots_on p `]a, b[ s -> last a s < b.
Proof.
case: s => [|x s] ab rs //.
by rewrite (itvP (roots_on_in rs _)) //= mem_last.
Qed.

Lemma last_roots_le p a b : a < b -> last a (roots p a b) < b.
Proof. by case: rootsP=> // *; apply: last_roots_on_le. Qed.

Lemma roots_uniq p a b s :
  p != 0 -> roots_on p `]a, b[ s -> sorted <%R s -> s = roots p a b.
Proof.
case: rootsP=> // p0 hs' ps' _ hs ss.
exact: (@roots_on_uniq p a b)=> //.
Qed.

Lemma roots_cons p a b x s :
  (roots p a b == x :: s)
    = [&& p != 0, x \in `]a, b[,
          roots p a x == [::], root p x & roots p x b == s].
Proof.
case: rootsP => //= p0 hs' ps'.
apply/idP/idP.
  move/eqP=> es'; move: ps' hs'; rewrite es' /= => sxs.
  case/min_roots_on; first by apply: order_path_min=> //; apply: lt_trans.
  move=> -> rax px0 rxb.
  rewrite px0 (@roots_uniq p a x [::]) // (@roots_uniq p x b s) ?eqxx //=.
  by move/path_sorted:sxs.
case: rootsP p0=> // p0 rax sax _.
case/and3P=> hx hax; rewrite (eqP hax) in rax sax.
case: rootsP p0=> // p0 rxb sxb _.
case/andP=> px0 hxb; rewrite (eqP hxb) in rxb sxb.
rewrite [_ :: _](@roots_uniq p a b) //; last first.
  rewrite /= path_min_sorted //; apply/allP => y.
  by rewrite -(eqP hxb); move/roots_in/itvP->.
move=> y; rewrite (itv_splitUeq hx) !andb_orl in_cons.
have [->|_] := eqVneq y x; first by rewrite px0 orbT.
by rewrite andFb orFb rax rxb in_nil.
Qed.

Lemma roots_rcons p a b x s :
  (roots p a b == rcons s x) =
    [&& p != 0, x \in `]a , b[,
        roots p x b == [::], root p x & roots p a x == s].
Proof.
case: rootsP; first by case: s.
move=> // p0 hs' ps' /=.
apply/idP/idP.
  move/eqP=> es'; move: ps' hs'; rewrite es' /= => sxs.
  have hsx: rcons s x =i x :: rev s.
    by move=> y; rewrite mem_rcons !in_cons mem_rev.
  move/(roots_on_same _ _ hsx).
  case/max_roots_on.
    move: sxs; rewrite -[rcons _ _]revK rev_sorted rev_rcons.
    by apply: order_path_min=> u v w /= /(lt_trans _); apply.
  move=> -> rax px0 /(@roots_on_same _ s); move/(_ (mem_rev _)) => rxb.
  rewrite px0 (@roots_uniq p x b [::]) // (@roots_uniq p a x s) ?eqxx //=.
  move: sxs; rewrite -[rcons _ _]revK rev_sorted rev_rcons.
  by move/path_sorted; rewrite -rev_sorted revK.
case: rootsP p0=> // p0 rax sax _.
case/and3P=> hx hax; rewrite (eqP hax) in rax sax.
case: rootsP p0=> // p0 rxb sxb _.
case/andP=> px0 hxb; rewrite (eqP hxb) in rxb sxb.
rewrite [rcons _ _](@roots_uniq p a b) //; last first.
  rewrite -[rcons _ _]revK rev_sorted rev_rcons /= path_min_sorted; last first.
    by rewrite -rev_sorted revK.
  apply/allP=> y; rewrite mem_rev; rewrite -(eqP hxb).
  by move/roots_in/itvP->.
move=> y; rewrite (itv_splitUeq hx) mem_rcons in_cons !andb_orl.
have [->|_] := eqVneq y x; first by rewrite px0 orbT.
by rewrite rxb rax in_nil !orbF.
Qed.

Section NeighborHood.

Implicit Types a b : R.

Implicit Types p : {poly R}.

Definition next_root (p : {poly R}) x b :=
  if p == 0 then x else head (maxr b x) (roots p x b).

Lemma next_root0 a b : next_root 0 a b = a.
Proof. by rewrite /next_root eqxx. Qed.

Variant next_root_spec (p : {poly R}) x b : bool -> R -> Type :=
| NextRootSpec0 of p = 0 : next_root_spec p x b true x
| NextRootSpecRoot y of p != 0 & p.[y] = 0 & y \in `]x, b[
  & {in `]x, y[, forall z, ~~(root p z)} : next_root_spec p x b true y
| NextRootSpecNoRoot c of p != 0 & c = maxr b x
  & {in `]x, b[, forall z, ~~(root p z)} : next_root_spec p x b (p.[c] == 0) c.

Lemma next_rootP (p : {poly R}) a b :
  next_root_spec p a b (p.[next_root p a b] == 0) (next_root p a b).
Proof.
rewrite /next_root /=; case hs: roots => [|x s] /=.
  case: (eqVneq p 0) hs => [->|p0] hs.
    by rewrite hornerC eqxx; constructor.
  by constructor=> // y hy; apply: (roots_nil p0 hs).
move/eqP: hs; rewrite roots_cons; case/and5P=> p0 hx /eqP rap rpx rx.
rewrite (negPf p0) (rootPt rpx); constructor=> //; first by apply/eqP.
by move=> y hy; apply: (roots_nil p0 rap).
Qed.

Lemma next_root_in p a b : next_root p a b \in `[a, maxr b a].
Proof.
case: next_rootP => [p0|y np0 py0 hy _|c np0 hc _].
* by rewrite bound_in_itv /<=%O /= le_max lexx orbT.
* by apply: subitvP hy; rewrite /<=%O /= /<=%O /= le_max !lexx.
* by rewrite hc bound_in_itv /<=%O /= le_max lexx orbT.
Qed.

Lemma next_root_gt p a b : a < b -> p != 0 -> next_root p a b > a.
Proof.
move=> ab np0; case: next_rootP=> [p0|y _ py0 hy _|c _ -> _].
* by rewrite p0 eqxx in np0.
* by rewrite (itvP hy).
* by rewrite lt_max ab.
Qed.

Lemma next_noroot p a b : {in `]a, (next_root p a b)[, noroot p}.
Proof.
move=> z; case: next_rootP; first by rewrite itv_xx.
  by move=> y np0 py0 hy hp hz; rewrite (negPf (hp _ _)).
move=> c p0 -> hp hz; rewrite (negPf (hp _ _)) //.
by case: leP hz; first rewrite itv_xx.
Qed.

Lemma is_next_root p a b x :
  next_root_spec p a b (root p x) x -> x = next_root p a b.
Proof.
case; first by move->; rewrite /next_root eqxx.
  move=> y; case: next_rootP; first by move->; rewrite eqxx.
  move=> y' np0 py'0 hy' hp' _ py0 hy hp.
    wlog: y y' hy' hy hp' hp py0 py'0 / y <= y'.
      by case/orP: (le_total y y')=> lyy' hw; [|symmetry]; apply: hw.
    case: ltrgtP=> // hyy' _; move: (hp' y).
    by rewrite in_itv /= (itvP hy) hyy' rootE py0 eqxx; move/(_ isT).
  move=> c p0 ->; case: leP => hba; first by rewrite itv_ge // -leNgt.
  by move=> hpz _ py0 /hpz; rewrite rootE py0 eqxx.
case: next_rootP; first by move->; rewrite eqxx.
  by move=> y np0 py0 hy _ c _ _ /(_ _ hy); rewrite rootE py0 eqxx.
by move=> c _ -> _ c' _ ->.
Qed.

Definition prev_root (p : {poly R}) a x :=
  if p == 0 then x else last (minr a x) (roots p a x).

Lemma prev_root0 a b : prev_root 0 a b = b.
Proof. by rewrite /prev_root eqxx. Qed.

Variant prev_root_spec (p : {poly R}) a x : bool -> R -> Type :=
| PrevRootSpec0 of p = 0 : prev_root_spec p a x true x
| PrevRootSpecRoot y of p != 0 & p.[y] = 0 & y \in`]a, x[
  & {in `]y, x[, forall z, ~~(root p z)} : prev_root_spec p a x true y
| PrevRootSpecNoRoot c of p != 0 & c = minr a x
 & {in `]a, x[, forall z, ~~(root p z)} : prev_root_spec p a x (p.[c] == 0) c.

Lemma prev_rootP (p : {poly R}) a b :
  prev_root_spec p a b (p.[prev_root p a b] == 0) (prev_root p a b).
Proof.
rewrite /prev_root /=; move hs: (roots _ _ _)=> s.
case: (lastP s) hs=> {s} [|s x] hs /=.
  case: (eqVneq p 0) hs => [->|p0] hs.
    by rewrite hornerC eqxx; constructor.
  by constructor=> // y hy; apply: (roots_nil p0 hs).
move/eqP: hs; rewrite last_rcons roots_rcons.
case/and5P=> p0 hx /eqP rap rpx rx.
rewrite (negPf p0) (rootPt rpx); constructor=> //; first by apply/eqP.
by move=> y hy /=; move/(roots_nil p0): (rap); apply.
Qed.

Lemma prev_root_in p a b : prev_root p a b \in `[minr a b, b].
Proof.
case: prev_rootP => [p0|y np0 py0 hy _|c np0 hc _].
* by rewrite bound_in_itv /<=%O /= ge_min lexx orbT.
* by apply: subitvP hy; rewrite /<=%O /= /<=%O /= ge_min !lexx.
* by rewrite hc bound_in_itv /<=%O /= ge_min lexx orbT.
Qed.

Lemma prev_noroot p a b : {in `](prev_root p a b), b[, noroot p}.
Proof.
move=> z; case: prev_rootP; first by rewrite itv_xx.
  by move=> y np0 py0 hy hp hz; rewrite (negPf (hp _ _)).
move=> c np0 ->; case: leP=> hab; last by rewrite itv_xx.
by move=> hp hz; rewrite (negPf (hp _ _)).
Qed.

Lemma prev_root_lt p a b : a < b -> p != 0 -> prev_root p a b < b.
Proof.
move=> ab np0; case: prev_rootP=> [p0|y _ py0 hy _|c _ -> _].
* by rewrite p0 eqxx in np0.
* by rewrite (itvP hy).
* by rewrite gt_min ab.
Qed.

Lemma is_prev_root p a b x :
  prev_root_spec p a b (root p x) x -> x = prev_root p a b.
Proof.
case; first by move->; rewrite /prev_root eqxx.
  move=> y; case: prev_rootP; first by move->; rewrite eqxx.
  move=> y' np0 py'0 hy' hp' _ py0 hy hp.
    wlog: y y' hy' hy hp' hp py0 py'0 / y <= y'.
      by case/orP: (le_total y y')=> lyy' hw; [|symmetry]; apply: hw.
    case: ltrgtP=> // hyy' _; move/implyP: (hp y').
    by rewrite rootE py'0 eqxx in_itv /= (itvP hy') hyy'.
  by move=> c _ _ hpz _ py0 /hpz; rewrite rootE py0 eqxx.
case: prev_rootP=> //; first by move->; rewrite eqxx.
  move=> y ? py0 hy _ c _ ->.
  case: ltP hy=> hab; last by rewrite itv_ge // -leNgt.
  by move=> hy /(_ _ hy); rewrite rootE py0 eqxx.
by move=> c  _ -> _ c' _ ->.
Qed.

Definition neighpr p a b := `]a, (next_root p a b)[.

Definition neighpl p a b := `](prev_root p a b), b[.

Lemma neighpl_root p a x : {in neighpl p a x, noroot p}.
Proof. exact: prev_noroot. Qed.

Lemma sgr_neighplN p a x :
  ~~ root p x -> {in neighpl p a x, forall y, (sgr p.[y] = sgr p.[x])}.
Proof.
rewrite /neighpl=> nrpx /= y hy.
apply: (@polyrN0_itv `[y, x]); do ?by rewrite bound_in_itv /<=%O /= (itvP hy).
move=> z; rewrite (@itv_splitU _ _ (BLeft x)) ?itv_xx /=.
(* Todo : Lemma itv_splitP *)
  by rewrite bound_lexx /<=%O /= (itvP hy).
rewrite orbC => /predU1P[-> // | hz].
rewrite (@prev_noroot _ a x) //.
by apply: subitvPl hz; rewrite /<=%O /= (itvP hy).
Qed.

Lemma sgr_neighpl_same p a x :
  {in neighpl p a x &, forall y z, (sgr p.[y] = sgr p.[z])}.
Proof.
by rewrite /neighpl=> y z *; apply: (polyrN0_itv (@prev_noroot p a x)).
Qed.

Lemma neighpr_root p x b : {in neighpr p x b, noroot p}.
Proof. exact: next_noroot. Qed.

Lemma sgr_neighprN p x b :
  p.[x] != 0 -> {in neighpr p x b, forall y, (sgr p.[y] = sgr p.[x])}.
Proof.
rewrite /neighpr=> nrpx /= y hy; symmetry.
apply: (@polyrN0_itv `[x, y]); do ?by rewrite bound_in_itv /<=%O /= (itvP hy).
move=> z; rewrite (@itv_splitU _ _ (BRight x)) ?itv_xx /=.
(* Todo : Lemma itv_splitP *)
  by rewrite bound_lexx /<=%O /= (itvP hy).
case/predU1P => [-> //|hz]; rewrite (@next_noroot _ x b) //.
by apply: subitvPr hz; rewrite /<=%O /= (itvP hy).
Qed.

Lemma sgr_neighpr_same p x b :
  {in neighpr p x b &, forall y z, (sgr p.[y] = sgr p.[z])}.
Proof.
by rewrite /neighpl=> y z *; apply: (polyrN0_itv (@next_noroot p x b)).
Qed.

Lemma uniq_roots a b p : uniq (roots p a b).
Proof.
have [->|p0] := eqVneq p 0; first by rewrite roots0.
by apply: (@sorted_uniq _ <%R); [apply: lt_trans | apply: ltxx|].
Qed.

Hint Resolve uniq_roots : core.

Lemma in_roots p (a b x : R) :
  (x \in roots p a b) = [&& root p x, x \in `]a, b[ & p != 0].
Proof.
case: rootsP=> //=; first by rewrite in_nil !andbF.
by move=> p0 hr sr; rewrite andbT -hr andbC.
Qed.

(* Todo : move to polyorder => need char 0 *)
Lemma gdcop_eq0 p q : (gdcop p q == 0) = (q == 0) && (p != 0).
Proof.
have [->|q0] := eqVneq q.
  by rewrite gdcop0 /=; case: (p == 0); rewrite ?eqxx ?oner_eq0.
rewrite /gdcop; move: {-1}(size q) (leqnn (size q))=> k hk; apply: negPf.
elim: k q q0 hk => [|k ihk] /= q q0 hk.
  by move: hk q0; rewrite leqn0 size_poly_eq0; move->.
case: ifP=> cpq; first by rewrite (negPf q0).
apply: ihk.
  rewrite divpN0; first by rewrite gcdp_eq0 negb_and q0.
  by rewrite dvdp_leq // dvdp_gcdl.
rewrite -ltnS; apply: leq_trans hk; move: (dvdp_gcdl q p); rewrite dvdp_eq.
move/eqP=> eqq; move/(f_equal (fun x : {poly R} => size x)): (eqq).
rewrite size_scale; first exact: lc_expn_scalp_neq0.
have gcdn0 : gcdp q p != 0 by rewrite gcdp_eq0 negb_and q0.
have qqn0 : q %/ gcdp q p != 0.
  apply: contraNneq q0 => e.
  move: (scaler_eq0 (lead_coef (gcdp q p) ^+ scalp q (gcdp q p)) q).
  by rewrite (negPf (lc_expn_scalp_neq0 _ _)) /= eqq e mul0r eqxx.
move->; rewrite size_mul //; case sgcd: (size (gcdp q p)) => [|n].
  by move/eqP: sgcd gcdn0; rewrite size_poly_eq0; move->.
case: n sgcd => [|n]; first by move/eqP; rewrite size_poly_eq1 gcdp_eqp1 cpq.
by rewrite addnS /= -{1}[size (_ %/ _)]addn0 ltn_add2l.
Qed.

Lemma roots_mul a b : a < b -> forall p q,
  p != 0 -> q != 0 -> perm_eq (roots (p*q) a b)
  (roots p a b ++ roots ((gdcop p q)) a b).
Proof.
move=> hab p q np0 nq0.
apply: uniq_perm; first exact: uniq_roots.
  rewrite cat_uniq ?uniq_roots andbT /=; apply/hasPn=> x /=.
  move/root_roots; rewrite root_gdco //; case/andP=> _.
  by rewrite in_roots !negb_and=> ->.
move=> x; rewrite mem_cat !in_roots root_gdco //.
rewrite rootM mulf_eq0 gdcop_eq0 negb_and.
case: (x \in `]_, _[); last by rewrite !andbF.
by rewrite negb_or !np0 !nq0 !andbT /=; do 2?case: root=> //=.
Qed.

Lemma roots_mul_coprime a b :
  a < b ->
  forall p q, p != 0 -> q != 0 -> coprimep p q ->
  perm_eq (roots (p * q) a b)
  (roots p a b ++ roots q a b).
Proof.
move=> hab p q np0 nq0 cpq.
rewrite (perm_trans (roots_mul hab np0 nq0)) //.
suff ->: roots (gdcop p q) a b = roots q a b by apply: perm_refl.
case: gdcopP=> r rq hrp /(_ q (dvdpp _)).
rewrite coprimep_sym; move/(_ cpq)=> qr.
have erq : r %= q by rewrite /eqp rq qr.
(* Todo : relate eqp with roots *)
apply/roots_eq=> // [|x hx]; last exact: eqp_root.
by rewrite -size_poly_eq0 (eqp_size erq) size_poly_eq0.
Qed.


Lemma next_rootM a b (p q : {poly R}) :
  next_root (p * q) a b = minr (next_root p a b) (next_root q a b).
Proof.
apply/esym/is_next_root.
wlog: p q / next_root p a b <= next_root q a b.
  case: leP=> hpq; first by move/(_ _ _ hpq); case: leP hpq.
  by move/(_ _ _ (ltW hpq)); rewrite mulrC; case: ltP hpq.
case: leP => //; case: next_rootP=> [|y np0 py0 hy|c np0 ->] hp hpq _.
* by rewrite hp mul0r root0; constructor.
* rewrite rootM; move/rootP:(py0)->; constructor=> //.
  - by rewrite mulf_neq0 //; case: next_rootP hpq; rewrite // (itvP hy).
  - by rewrite hornerM py0 mul0r.
  - move=> z hz /=; rewrite rootM negb_or ?hp //.
    by rewrite (@next_noroot _ a b) //; apply: subitvPr hz.
* case: (eqVneq q 0) hpq => [->|q0 hpq].
    rewrite mulr0 root0 next_root0 ge_max lexx andbT.
    by move/max_r->; constructor.
  constructor=> //; first by rewrite mulf_neq0.
  move=> z hz /=; rewrite rootM negb_or ?hp // (@next_noroot _ a b) //.
  by apply: subitvPr hz=> /=; move: hpq; rewrite ge_max; case/andP.
Qed.

Lemma neighpr_mul a b p q :
  (neighpr (p * q) a b) =i [predI (neighpr p a b) & (neighpr q a b)].
Proof.
move=> x; rewrite !inE /<=%O /= /<=%O /= next_rootM.
by case: (a < x); rewrite // lt_min.
Qed.

Lemma prev_rootM a b (p q : {poly R}) :
  prev_root (p * q) a b = maxr (prev_root p a b) (prev_root q a b).
Proof.
apply/esym/is_prev_root.
wlog: p q / prev_root p a b >= prev_root q a b.
  case: leP=> hpq; last by move/(_ _ _ (ltW hpq)); case: leP hpq.
  by move/(_ _ _ hpq); case: ltP hpq; rewrite mulrC.
case: ltP => //; case: (@prev_rootP p)=> [|y np0 py0 hy|c np0 ->] hp hpq _.
* by rewrite hp mul0r root0; constructor.
* rewrite rootM; move/rootP:(py0)->; constructor=> //.
  - by rewrite mulf_neq0 //; case: prev_rootP hpq; rewrite // (itvP hy).
  - by rewrite hornerM py0 mul0r.
  - move=> z hz /=; rewrite rootM negb_or ?hp //.
    by rewrite (@prev_noroot _ a b) //; apply: subitvPl hz.
* case: (eqVneq q 0) hpq => [->|q0 hpq].
    rewrite mulr0 root0 prev_root0 le_min lexx andbT.
    by move/min_r->; constructor.
  constructor=> //; first by rewrite mulf_neq0.
  move=> z hz /=; rewrite rootM negb_or ?hp // (@prev_noroot _ a b) //.
  by apply: subitvPl hz=> /=; move: hpq; rewrite le_min; case/andP.
Qed.

Lemma neighpl_mul a b p q :
  (neighpl (p * q) a b) =i [predI (neighpl p a b) & (neighpl q a b)].
Proof.
move=> x; rewrite !inE /<=%O /= /<=%O /= prev_rootM.
by case: (x < b); rewrite // gt_max !(andbT, andbF).
Qed.

Lemma neighpr_wit p x b : x < b -> p != 0 -> {y | y \in neighpr p x b}.
Proof.
move=> xb; exists (mid x (next_root p x b)).
by rewrite mid_in_itv //= next_root_gt.
Qed.

Lemma neighpl_wit p a x : a < x -> p != 0 -> {y | y \in neighpl p a x}.
Proof.
move=> xb; exists (mid (prev_root p a x) x).
by rewrite mid_in_itv //= prev_root_lt.
Qed.

End NeighborHood.

Section SignRight.

Definition sgp_right (p : {poly R}) x :=
  let fix aux (p : {poly R}) n :=
  if n is n'.+1
    then if ~~ root p x
      then sgr p.[x]
      else aux p^`() n'
    else 0
      in aux p (size p).

Lemma sgp_right0 x : sgp_right 0 x = 0.
Proof. by rewrite /sgp_right size_poly0. Qed.

Lemma sgr_neighpr b p x :
  {in neighpr p x b, forall y, (sgr p.[y] = sgp_right p x)}.
Proof.
have [n] := ubnP (size p); elim: n => // -[_|n ihn] in p *; rewrite ltnS.
  by move=> /size_poly_leq0P-> y; rewrite /neighpr next_root0 itv_xx.
rewrite leq_eqVlt ltnS; case/orP; last exact: ihn.
move/eqP=> sp; rewrite /sgp_right sp /=.
have pN0 : p != 0 by apply: contra_eq_neq sp => ->; rewrite size_poly0.
case px0: root=> /=; last first.
  move=> y; rewrite /neighpr => hy /=; symmetry.
  apply: (@polyrN0_itv `[x, y]); do ?by rewrite bound_in_itv ?bnd_simp /= (itvP hy).
  move=> z; rewrite (@itv_splitU _ _ (BRight x))
     ?bound_in_itv /= ?bnd_simp ?(itvP hy) //.
  rewrite itv_xx /=; case/predU1P=> hz; first by rewrite hz px0.
  rewrite (@next_noroot p x b) //.
  by apply: subitvPr hz=> /=; rewrite !bnd_simp (itvP hy).
have <-: size p^`() = n by rewrite size_deriv sp.
rewrite -/(sgp_right p^`() x).
move=> y; rewrite /neighpr=> hy /=.
case: (@neighpr_wit (p * p^`()) x b)=> [||m hm].
* case: next_rootP hy; first by rewrite itv_xx.
    by move=> ? ? ?; move/itvP->.
  by move=> c p0 -> _; case: lerP => _; rewrite ?itv_xx //; move/itvP->.
* rewrite mulf_neq0 //.
  move: (size_deriv p); rewrite sp /=; move/eqP; apply: contraTneq=> ->.
  rewrite size_poly0; apply: contraTneq px0=> hn; rewrite -hn in sp.
  by move/eqP: sp; case/size_poly1P=> c nc0 ->; rewrite rootC.
* move: hm; rewrite neighpr_mul /neighpr inE /=; case/andP=> hmp hmp'.
  have lt_xm : x < m by rewrite (itvP hmp).
  rewrite (polyrN0_itv _ hmp) //; first exact: next_noroot.
  have midxmxb : mid x m \in neighpr p^`() x b.
    rewrite (subitvP _ (@mid_in_itv _ false true _ _ _)) //=.
    by rewrite ?lerr le_itv !bnd_simp (itvP hmp').
  rewrite (@root_dersr p x m) ?(eqP px0) ?mid_in_itv ?bound_in_itv //;
    rewrite ?bnd_simp /= ?(itvP hmp) //.
    move=> u hu /=; rewrite (@next_noroot _ x b) //.
    by apply: subitvPr hu; rewrite /= ?bnd_simp (itvP hmp').
  rewrite neqr0_sign// ?(@next_noroot _ x b)//.
  by rewrite ihn ?size_deriv ?sp /neighpr.
Qed.

Lemma sgr_neighpl a p x :
  {in neighpl p a x, forall y,
    (sgr p.[y] = (-1) ^+ (odd (\mu_x p)) * sgp_right p x)
  }.
Proof.
have [n] := ubnP (size p); elim: n => // -[_|n ihn] in p *; rewrite ltnS.
  by move=> /size_poly_leq0P-> y; rewrite /neighpl prev_root0 itv_xx.
rewrite leq_eqVlt ltnS; case/orP; last exact: ihn.
move/eqP=> sp; rewrite /sgp_right sp /=.
have pN0 : p != 0 by apply: contra_eq_neq sp => ->; rewrite size_poly0.
case px0: root=> /=; last first.
  move=> y; rewrite /neighpl => hy /=; symmetry.
  move: (negbT px0); rewrite -mup_gt0.
    by apply: contraFN px0; move/eqP->; rewrite rootC.
  rewrite -leqNgt leqn0; move/eqP=> -> /=; rewrite expr0 mul1r.
  symmetry; apply: (@polyrN0_itv `[y, x]);
    do ?by rewrite bound_in_itv  ?bnd_simp /= (itvP hy).
  move=> z; rewrite (@itv_splitU _ _ (BLeft x)) ?bound_in_itv ?bnd_simp /= ?(itvP hy) //.
  rewrite itv_xx /= orbC; case/predU1P=> hz; first by rewrite hz px0.
  rewrite (@prev_noroot p a x) //.
  by apply: subitvPl hz=> /=; rewrite bnd_simp (itvP hy).
have <-: size p^`() = n by rewrite size_deriv sp.
rewrite -/(sgp_right p^`() x).
move=> y; rewrite /neighpl=> hy /=.
case: (@neighpl_wit (p * p^`()) a x)=> [||m hm].
* case: prev_rootP hy; first by rewrite itv_xx.
    by move=> ? ? ?; move/itvP->.
  by move=> c p0 -> _; case: lerP => _; rewrite ?itv_xx //; move/itvP->.
* rewrite mulf_neq0 //.
  move: (size_deriv p); rewrite sp /=; move/eqP; apply: contraTneq=> ->.
  rewrite size_poly0; apply: contraTneq px0=> hn; rewrite -hn in sp.
  by move/eqP: sp; case/size_poly1P=> c nc0 ->; rewrite rootC.
* move: hm; rewrite neighpl_mul /neighpl inE /=; case/andP=> hmp hmp'.
  have lt_xm : m < x by rewrite (itvP hmp).
  have midxmxb : mid m x \in neighpl p^`() a x.
    rewrite (subitvP _ (@mid_in_itv _ false true _ _ _)) //=
       ?le_itv ?bnd_simp (itvP hmp')//.
  rewrite (polyrN0_itv _ hmp) //; first exact: prev_noroot.
  rewrite (@root_dersl p m x) ?(eqP px0) ?mid_in_itv ?bound_in_itv //;
    rewrite /= ?bnd_simp ?(itvP hmp) //.
    move=> u hu /=; rewrite (@prev_noroot _ a x) //.
    by apply: subitvPl hu; rewrite /= ?bnd_simp (itvP hmp').
  rewrite neqr0_sign ?(@prev_noroot _ a x)// ihn// ?size_deriv ?sp//.
  have pc0 : has_pchar0 R by exact: pchar_num.
  by rewrite mup_deriv// oddB ?mup_gt0//= signr_addb mulrN1 mulNr opprK.
Qed.

Lemma sgp_right_deriv (p : {poly R}) x :
  root p x -> sgp_right p x = sgp_right (p^`()) x.
Proof.
elim: (size p) {-2}p (erefl (size p)) x => {p} [p|sp hp p hsp x].
  by move/eqP; rewrite size_poly_eq0; move/eqP=> -> x _; rewrite derivC.
by rewrite /sgp_right size_deriv hsp /= => ->.
Qed.

Lemma sgp_rightNroot (p : {poly R}) x :
  ~~ root p x -> sgp_right p x = sgr p.[x].
Proof.
move=> nrpx; rewrite /sgp_right; case hsp: (size _)=> [|sp].
  by move/eqP:hsp; rewrite size_poly_eq0; move/eqP->; rewrite hornerC sgr0.
by rewrite nrpx.
Qed.

Lemma sgp_right_mul p q x : sgp_right (p * q) x = sgp_right p x * sgp_right q x.
Proof.
have [->|q0] := eqVneq q 0; first by rewrite /sgp_right !(size_poly0,mulr0).
have [->|p0] := eqVneq p 0; first by rewrite /sgp_right !(size_poly0,mul0r).
case: (@neighpr_wit (p * q) x (1 + x))=> [||m hpq]; do ?by rewrite mulf_neq0.
  by rewrite ltr_pwDl ?ltr01.
rewrite -(@sgr_neighpr (1 + x) _ _ m) //; move: hpq; rewrite neighpr_mul.
by case/andP=> /= hp hq; rewrite hornerM sgrM !(@sgr_neighpr (1 + x) _ x).
Qed.

Lemma sgp_right_scale c p x : sgp_right (c *: p) x = sgr c * sgp_right p x.
Proof.
have [->|c0] := eqVneq c 0; first by rewrite scale0r sgr0 mul0r sgp_right0.
by rewrite -mul_polyC sgp_right_mul sgp_rightNroot ?hornerC ?rootC ?c0.
Qed.

Lemma sgp_right_square p x : p != 0 -> sgp_right p x * sgp_right p x = 1.
Proof.
move=> np0; case: (@neighpr_wit p x (1 + x))=> [||m hpq] //.
  by rewrite ltr_pwDl ?ltr01.
rewrite -(@sgr_neighpr (1 + x) _ _ m) //.
by rewrite -expr2 sqr_sg (@next_noroot _ x (1 + x)).
Qed.

Lemma sgp_right_rec p x :
  sgp_right p x =
   (if p == 0 then 0 else if ~~ root p x then sgr p.[x] else sgp_right p^`() x).
Proof.
rewrite /sgp_right; case hs: size => [|s]; rewrite -size_poly_eq0 hs //=.
by rewrite size_deriv hs.
Qed.

Lemma sgp_right_addp0 (p q : {poly R}) x :
  q != 0 -> (\mu_x p > \mu_x q)%N -> sgp_right (p + q) x = sgp_right q x.
Proof.
move=> nq0; move hm: (\mu_x q)=> m.
elim: m p q nq0 hm => [|mq ihmq] p q nq0 hmq; case hmp: (\mu_x p)=> // [mp];
  do[rewrite ltnS=> hm; rewrite sgp_right_rec {1}addrC addr_eq0].
  case: (eqVneq q (- p)) nq0 hmq => [-> np0 hmq|hqp nq0 hmq].
    rewrite sgp_right_rec (negPf np0) -mup_gt0 // hmq ltnn /=; apply/esym/eqP.
    by rewrite hornerN sgrN oppr_eq0 sgr_eq0 -[_ == _]mup_gt0 ?hmp // -oppr_eq0.
  rewrite rootE hornerD.
  have ->: p.[x] = 0.
    apply/eqP; rewrite -[_ == _]mup_gt0 ?hmp //.
    by apply: contra_eq_neq hmp => ->; rewrite mup0.
  by rewrite [RHS]sgp_right_rec (negPf nq0) add0r -/(root _ _) -mup_gt0 // hmq.
case: eqVneq => hqp.
  by move: hm; rewrite -ltnS -hmq -hmp hqp mupN ltnn.
have px0: p.[x] = 0.
  apply/rootP; rewrite -mup_gt0 ?hmp //.
  by apply: contra_eq_neq hmp => ->; rewrite mup0.
have qx0: q.[x] = 0 by apply/rootP; rewrite -mup_gt0 ?hmq //.
have pc0 : has_pchar0 R by exact: pchar_num.
rewrite rootE hornerD px0 qx0 add0r eqxx /=; symmetry.
rewrite sgp_right_rec rootE (negPf nq0) qx0 eqxx /=.
rewrite derivD ihmq // ?mup_deriv ?rootE ?px0 ?qx0 ?hmp ?hmq ?subn1 //.
apply: contra nq0; rewrite -size_poly_eq0 size_deriv.
case hsq: size=> [|sq] /=.
  by move/eqP: hsq; rewrite size_poly_eq0.
move/eqP=> sq0; move/eqP: hsq qx0; rewrite sq0; case/size_poly1P=> c c0 ->.
by rewrite hornerC; move/eqP; rewrite (negPf c0).
Qed.

End SignRight.

(* redistribute some of what follows with in the file *)
Section PolyRCFPdiv.
Import Pdiv.Ring Pdiv.ComRing.

Lemma sgp_rightc (x c : R) : sgp_right c%:P x = sgr c.
Proof.
rewrite /sgp_right size_polyC.
by have [->|cn0] /= := eqVneq; rewrite ?sgr0 // rootC hornerC cn0.
Qed.

Lemma sgp_right_eq0 (x : R) p : (sgp_right p x == 0) = (p == 0).
Proof.
have [->|p0] := eqVneq p; first by rewrite sgp_rightc sgr0 eqxx.
rewrite /sgp_right.
elim: (size p) {-2}p (erefl (size p)) p0=> {p} [|sp ihsp] p esp p0.
  by move/eqP: esp; rewrite size_poly_eq0 (negPf p0).
rewrite esp /=; case px0: root=> //=; rewrite ?sgr_cp0 ?px0//.
have hsp: sp = size p^`() by rewrite size_deriv esp.
rewrite hsp ihsp // -size_poly_eq0 -hsp.
move: px0; rewrite root_factor_theorem => /rdvdp_leq /(_ p0).
by rewrite size_XsubC esp ltnS; case: posnP.
Qed.

(* :TODO: backport to polydiv *)
Lemma lc_expn_rscalp_neq0 (p q : {poly R}): lead_coef q ^+ rscalp p q != 0.
Proof.
have [->|nzq] := eqVneq q 0; last by rewrite expf_neq0 ?lead_coef_eq0.
by rewrite /rscalp unlock /= eqxx /= expr0 oner_neq0.
Qed.
Notation lcn_neq0 := lc_expn_rscalp_neq0.

Lemma sgp_right_mod p q x : (\mu_x p < \mu_x q)%N ->
  sgp_right (rmodp p q) x = (sgr (lead_coef q)) ^+ (rscalp p q) * sgp_right p x.
Proof.
case: (eqVneq p 0) => [-> _|p0 mupq]; first by rewrite rmod0p !sgp_right0 mulr0.
have qn0 : q != 0 by apply: contraTneq mupq => ->; rewrite -leqNgt mup0.
move/(canLR (addKr _)): (rdivp_eq q p) => <-.
have [->|qpq0] := eqVneq (rdivp p q) 0.
  by rewrite mul0r oppr0 add0r sgp_right_scale // sgrX.
rewrite sgp_right_addp0 ?sgp_right_scale ?sgrX //.
  by rewrite scaler_eq0 negb_or p0 lcn_neq0.
by rewrite mup_scale ?lcn_neq0 // mupN mupM // ltn_addl.
Qed.

Lemma rootsC (a b c : R) : roots c%:P a b = [::].
Proof.
have [->|hc] := eqVneq c 0; first by rewrite roots0.
by apply: no_root_roots=> x hx; rewrite rootC.
Qed.

Lemma rootsZ a b c p : c != 0 -> roots (c *: p) a b = roots p a b.
Proof.
case: (eqVneq p 0) => [->|p_neq0 c_neq0]; first by rewrite scaler0.
by apply/roots_eq => [||x axb]; rewrite ?scaler_eq0 ?(negPf c_neq0) ?rootZ.
Qed.

Lemma root_bigrgcd (x : R) (ps : seq {poly R}) :
  root (\big[(@rgcdp _)/0]_(p <- ps) p) x = all (root^~ x) ps.
Proof.
elim: ps; first by rewrite big_nil root0.
move=> p ps ihp; rewrite big_cons /=.
by rewrite (eqp_root (eqp_rgcd_gcd _ _)) root_gcd ihp.
Qed.

Definition rootsR p := roots p (- cauchy_bound p) (cauchy_bound p).

Lemma roots_on_rootsR p : p != 0 -> roots_on p `]-oo, +oo[ (rootsR p).
Proof.
rewrite /rootsR => p_neq0 x /=; rewrite -roots_on_roots // andbC.
by have [/(cauchy_boundP p_neq0) /=|//] := rootP; rewrite ltr_norml.
Qed.

Lemma rootsR0 : rootsR 0 = [::]. Proof. exact: roots0. Qed.

Lemma rootsRC c : rootsR c%:P = [::]. Proof. exact: rootsC. Qed.

Lemma rootsRP p a b :
    {in `]-oo, a], noroot p} -> {in `[b , +oo[, noroot p} ->
  roots p a b = rootsR p.
Proof.
move=> rpa rpb.
have [->|p_neq0] := eqVneq p 0; first by rewrite rootsR0 roots0.
apply: (irr_sorted_eq lt_trans); rewrite ?sorted_roots // => x.
rewrite -roots_on_rootsR -?roots_on_roots //=.
case: (boolP (root _ _)); rewrite ?(andbT, andbF) //.
apply: contraLR; rewrite in_itv negb_and -!leNgt.
by move=> /orP[/rpa //|xb]; rewrite rpb // in_itv andbT.
Qed.

Lemma sgp_pinftyP x (p : {poly R}) :
    {in `[x , +oo[, noroot p} ->
  {in `[x, +oo[, forall y, sgr p.[y] = sgp_pinfty p}.
Proof.
rewrite /sgp_pinfty; wlog lp_gt0 : x p / lead_coef p > 0 => [hwlog|rpx y Hy].
  have [|/(hwlog x p) //|/eqP] := ltrgtP (lead_coef p) 0; last first.
    by rewrite lead_coef_eq0 => /eqP -> ? ? ?; rewrite lead_coef0 horner0.
  rewrite -[p]opprK lead_coefN oppr_cp0 => /(hwlog x _) Hp HNp y Hy.
  by rewrite hornerN !sgrN Hp => // z /HNp; rewrite rootN.
have [z Hz] := poly_pinfty_gt_lc lp_gt0.
have {}Hz u : u \in `[z, +oo[ -> Num.sg p.[u] = 1.
  rewrite in_itv andbT => /Hz pu_ge1.
  by rewrite gtr0_sg // (lt_le_trans lp_gt0).
rewrite (@polyrN0_itv _ _ rpx (maxr y z)) ?in_itv /= ?le_max ?(itvP Hy) //.
by rewrite Hz ?gtr0_sg // in_itv /= le_max lexx orbT.
Qed.

Lemma sgp_minftyP x (p : {poly R}) :
    {in `]-oo, x], noroot p} ->
  {in `]-oo, x], forall y, sgr p.[y] = sgp_minfty p}.
Proof.
move=> rpx y Hy; rewrite -sgp_pinfty_sym.
have ->: p.[y] = (p \Po -'X).[-y] by rewrite horner_comp !hornerE opprK.
apply: (@sgp_pinftyP (- x)) => /= [z Hz|].
  by rewrite root_comp !hornerE rpx // in_itv /= lerNl (itvP Hz).
by rewrite in_itv /= lerN2 (itvP Hy).
Qed.

Lemma odd_poly_root (p : {poly R}) : ~~ odd (size p) -> {x | root p x}.
Proof.
move=> size_p_even.
have [->|p_neq0] := eqVneq p 0; first by exists 0; rewrite root0.
pose b := cauchy_bound p.
have [] := @poly_ivtoo p (-b) b; last by move=> x _; exists x.
  by rewrite ge0_cp // ?cauchy_bound_ge0.
rewrite -sgr_cp0 sgrM.
rewrite (sgp_minftyP (le_cauchy_bound p_neq0)) ?bound_in_itv //.
rewrite (sgp_pinftyP (ge_cauchy_bound p_neq0)) ?bound_in_itv //.
move: size_p_even; rewrite polySpred //= negbK /sgp_minfty -signr_odd => ->.
by rewrite expr1 mulN1r sgrN mulNr -expr2 sqr_sg lead_coef_eq0 p_neq0.
Qed.
End PolyRCFPdiv.

End PolyRCF.

#[deprecated(since="mathcomp-real-closed 2.1.0", use=poly_rolle)]
Notation rolle := poly_rolle.
#[deprecated(since="mathcomp-real-closed 2.1.0", use=poly_mvt)]
Notation mvt := poly_mvt.
#[deprecated(since="mathcomp-real-closed 1.1.0", use=poly_ivtoo)]
Notation ivt_sign := ivt_sign_deprecated.

(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import boot order orderedzmod near sets.
From mathcomp Require Import algebraic_hierarchy numeric_hierarchy archimedean.
From mathcomp Require Import rat poly polyXY polydiv mxpoly cauchyreals.
From mathcomp Require Import separable.

(*************************************************************************)
(* This files constructs the real closure of an archimedean field in the *)
(* way described in Cyril Cohen. Construction of real algebraic numbers  *)
(* in Coq. In Lennart Beringer and Amy Felty, editors, ITP - 3rd         *)
(* International Conference on Interactive Theorem Proving - 2012,       *)
(* Princeton, United States, August 2012. Springer                       *)
(*                                                                       *)
(* The only definition one may want to use in this file is the operator  *)
(* {realclosure R} which constructs the real closure of an archimedean   *)
(* field R (e.g. rat).                                                   *)
(*************************************************************************)

Import Order.TTheory GRing.Theory Num.Theory.
Require Setoid.

(* remove the line when requiring MathComp >= 2.6 *)
Unset SsrOldRewriteGoalsOrder.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "{ 'realclosure' T }"
  (at level 0, format "{ 'realclosure'  T }").
Reserved Notation "{ 'alg' T }" (at level 0, format "{ 'alg'  T }").

Section extras.

Local Open Scope ring_scope.
Local Notation "p ^ f" := (map_poly f p) : ring_scope.

Lemma map_comp_poly (aR : fieldType) (rR : idomainType)
  (f : {rmorphism aR -> rR})
  (p q : {poly aR}) : (p \Po q) ^ f = (p ^ f) \Po (q ^ f).
Proof.
rewrite !comp_polyE size_map_poly; apply: (big_ind2 (fun x y => x ^ f = y)).
- by rewrite rmorph0.
- by move=> u u' v v' /=; rewrite rmorphD /= => -> ->.
move=> /= i _; rewrite -mul_polyC rmorphM /= map_polyC mul_polyC.
by rewrite coef_map rmorphXn.
Qed.

End extras.

Module RealAlg.

Local Open Scope ring_scope.
Local Notation eval := horner_eval.
Local Open Scope near_scope.

Section RealAlg.

Variable F : archiRealFieldType.
Local Notation m0 := (fun _ => 0%N). 

(*********************************************************************)
(* Construction of algebraic Cauchy reals : Cauchy real + polynomial *)
(*********************************************************************)

Record algcreal := AlgCReal {
  creal_of_alg :> creal F;
  annul_creal : {poly F};
  _ : annul_creal \is monic;
  _ : (annul_creal.[creal_of_alg] == 0)%CR
}.

Lemma monic_annul_creal x : annul_creal x \is monic.
Proof. by case: x. Qed.
Hint Resolve monic_annul_creal : core.

Lemma annul_creal_eq0 x : (annul_creal x == 0) = false.
Proof. by rewrite (negPf (monic_neq0 _)). Qed.

Lemma root_annul_creal x : ((annul_creal x).[x] == 0)%CR.
Proof. by case: x. Qed.
Hint Resolve root_annul_creal : core.

Definition cst_algcreal (x : F) :=
  AlgCReal (monicXsubC _) (@root_cst_creal _ x).

Local Notation zero_algcreal := (cst_algcreal 0).
Local Notation one_algcreal := (cst_algcreal 1).

Lemma size_annul_creal_gt1 (x : algcreal) :
  (1 < size (annul_creal x))%N.
Proof.
apply: (@has_root_creal_size_gt1 _ x).
  by rewrite monic_neq0 // monic_annul_creal.
exact: root_annul_creal.
Qed.

Lemma is_root_annul_creal (x : algcreal) (y : creal F) :
  (x == y)%CR -> ((annul_creal x).[y] == 0)%CR.
Proof. by move <-. Qed.

Definition AlgCRealOf (p : {poly F}) (x : creal F)
  (p_neq0 : p != 0) (px_eq0 : (p.[x] == 0)%CR) :=
  AlgCReal (neq0_scale_monic p_neq0) (root_monic_from_neq0 px_eq0).

Lemma sub_annihilant_algcreal_neq0 (x y : algcreal) :
  sub_annihilant (annul_creal x) (annul_creal y) != 0.
Proof. by rewrite sub_annihilant_neq0 ?monic_neq0. Qed.

Lemma root_sub_algcreal (x y : algcreal) :
  ((sub_annihilant (annul_creal x) (annul_creal y)).[x - y] == 0)%CR.
Proof. by rewrite root_sub_annihilant_creal ?root_annul_creal ?monic_neq0. Qed.

Definition sub_algcreal (x y : algcreal) : algcreal :=
  AlgCRealOf (sub_annihilant_algcreal_neq0 x y) (@root_sub_algcreal x y).

Lemma root_opp_algcreal (x : algcreal) :
  ((annul_creal (sub_algcreal (cst_algcreal 0) x)).[- x] == 0)%CR.
Proof. by apply: is_root_annul_creal; rewrite /= add_0creal. Qed.

Definition opp_algcreal (x : algcreal) : algcreal :=
  AlgCReal (@monic_annul_creal _) (@root_opp_algcreal x).

Lemma root_add_algcreal (x y : algcreal) :
  ((annul_creal (sub_algcreal x (opp_algcreal y))).[x + y] == 0)%CR.
Proof.
apply: is_root_annul_creal; apply: eq_crealP => e e0; near=> i.
by rewrite /= opprK subrr normr0.
Unshelve. all: by end_near. Qed.

Definition add_algcreal (x y : algcreal) : algcreal :=
  AlgCReal (@monic_annul_creal _) (@root_add_algcreal x y).

Lemma div_annihilant_algcreal_neq0 (x y : algcreal) :
   (annul_creal y).[0] != 0 ->
   div_annihilant (annul_creal x) (annul_creal y) != 0.
Proof. by move=> ?; rewrite div_annihilant_neq0 ?monic_neq0. Qed.

Hint Resolve eq_creal_refl le_creal_refl : core.

Lemma simplify_algcreal (x : algcreal) (x_neq0 : (x != 0)%CR) :
  {y | ((annul_creal y).[0] != 0) & ((y != 0)%CR * (x == y)%CR)%type}.
Proof.
elim: size {-3}x x_neq0 (leqnn (size (annul_creal x))) =>
  {x} [|n ihn] x x_neq0 hx.
  by move: hx; rewrite leqn0 size_poly_eq0 annul_creal_eq0.
have [dvdX|ndvdX] := boolP ('X %| annul_creal x); last first.
  by exists x=> //; rewrite -rootE -dvdp_XsubCl subr0.
have monic_p: @annul_creal x %/ 'X \is monic.
  by rewrite -(monicMr _ (@monicX _)) divpK //.
have root_p: ((@annul_creal x %/ 'X).[x] == 0)%CR.
  have := @eq_creal_refl _ ((annul_creal x).[x])%CR.
  rewrite -{1}(divpK dvdX) horner_crealM // root_annul_creal.
  by case/poly_mul_creal_eq0=> //; rewrite horner_crealX.
have [//|/=|y *] := ihn (AlgCReal monic_p root_p); last by exists y.
by rewrite size_divp ?size_polyX ?polyX_eq0 ?leq_subLR ?add1n.
Qed.

(* Decidability of equality to 0 *)
Lemma algcreal_eq0_dec (x : algcreal) : {(x == 0)%CR} + {(x != 0)%CR}.
Proof.
pose p := annul_creal x; move: {2}(size p) (leqnn (size p)) => n.
elim: n x @p => [x p|n ihn x p].
  by rewrite leqn0 size_poly_eq0 /p annul_creal_eq0.
rewrite leq_eqVlt.
have [/=|//|eq_sp_Sn _] := ltngtP.
  by rewrite ltnS => /ihn ihnp _; apply: ihnp.
have px0 : (p.[x] == 0)%CR by exact: root_annul_creal.
have [cpX|ncpX] := boolP (coprimep p 'X).
  by right; move: cpX => /coprimep_root /(_ px0); rewrite horner_crealX.
have [eq_pX|neq_pX] := altP (p =P 'X).
  by left; move: px0; rewrite eq_pX horner_crealX.
have monic_p : p \is monic by rewrite /p monic_annul_creal.
have Xdvd_p : 'X %| p.
  by move: ncpX; rewrite coprimepX negbK -dvdp_XsubCl subr0.
have ndiv_pX : ~~ (p %| 'X).
  apply/negP => pdvdX.
  have eqp_pX : p %= 'X by rewrite /eqp pdvdX Xdvd_p.
  have eq_pX : p == 'X.
    by move: eqp_pX; rewrite (eqp_monic monic_p (monicX _)).
  by move: neq_pX; rewrite eq_pX.
have [r] := smaller_factor monic_p px0 ndiv_pX ncpX.
rewrite eq_sp_Sn ltnS => /andP[le_r_n monic_r] rx_eq0.
exact: (ihn (AlgCReal monic_r rx_eq0)).
Qed.

Lemma eq_algcreal_dec (x y : algcreal) : {(x == y)%CR} + {(x != y)%CR}.
Proof.
have /= [d_eq0 | d_neq0] := algcreal_eq0_dec (sub_algcreal x y); [left | right].
- apply: eq_crealP => e e0.
  by apply: filterS (asympt_eq d_eq0 e0) => i /=; rewrite subr0.
- case: d_neq0 => d d0 hd.
  by exists d => //; apply: filterS hd => i /=; rewrite subr0.
Qed.

Definition eq_algcreal : rel algcreal := eq_algcreal_dec.

Lemma eq_algcrealP (x y : algcreal) : reflect (x == y)%CR (eq_algcreal x y).
Proof. by rewrite /eq_algcreal; case: eq_algcreal_dec=> /=; constructor. Qed.
Arguments eq_algcrealP {x y}.

Lemma neq_algcrealP (x y : algcreal) : reflect (x != y)%CR (~~ eq_algcreal x y).
Proof. by rewrite /eq_algcreal; case: eq_algcreal_dec=> /=; constructor. Qed.
Arguments neq_algcrealP {x y}.
Prenex Implicits eq_algcrealP neq_algcrealP.

Fact eq_algcreal_is_equiv : equiv_class_of eq_algcreal.
Proof.
split=> [x|x y|y x z]; first by apply/eq_algcrealP.
  by apply/eq_algcrealP/eq_algcrealP; symmetry.
by move=> /eq_algcrealP /eq_creal_trans h /eq_algcrealP /h /eq_algcrealP.
Qed.

Canonical eq_algcreal_rel := EquivRelPack eq_algcreal_is_equiv.

Lemma root_div_algcreal (x y : algcreal) (y_neq0 : (y != 0)%CR) :
  (annul_creal y).[0] != 0 ->
  ((div_annihilant (annul_creal x) (annul_creal y)).[x / y_neq0] == 0)%CR.
Proof. by move=> hx; rewrite root_div_annihilant_creal ?monic_neq0. Qed.

Definition div_algcreal (x y : algcreal) :=
  match eq_algcreal_dec y (cst_algcreal 0) with
    | left y_eq0 => cst_algcreal 0
    | right y_neq0 =>
      let: exist2 y' py'0_neq0 (y'_neq0, _) := simplify_algcreal y_neq0 in
      AlgCRealOf (div_annihilant_algcreal_neq0 x py'0_neq0)
                 (@root_div_algcreal x y' y'_neq0 py'0_neq0)
  end.

Lemma root_inv_algcreal (x : algcreal) (x_neq0 : (x != 0)%CR) :
  ((annul_creal (div_algcreal (cst_algcreal 1) x)).[x_neq0^-1] == 0)%CR.
Proof.
rewrite /div_algcreal; case: eq_algcreal_dec =>
    [/(_ x_neq0)|x_neq0'] //=.
case: simplify_algcreal => x' px'0_neq0 [x'_neq0 eq_xx'].
apply: is_root_annul_creal.
rewrite /= -(@eq_creal_inv _ _ _ x_neq0)//.
by apply: eq_crealP => e e0; near=> i; rewrite /= div1r subrr normr0.
Unshelve. all: by end_near. Qed.

Definition inv_algcreal (x : algcreal) :=
  match eq_algcreal_dec x (cst_algcreal 0) with
    | left x_eq0 => cst_algcreal 0
    | right x_neq0 =>
      AlgCReal (@monic_annul_creal _) (@root_inv_algcreal _ x_neq0)
  end.

Lemma div_creal_creal (y : creal F) (y_neq0 : (y != 0)%CR) :
  (y / y_neq0 == 1%:CR)%CR.
Proof.
apply: eq_crealP => e e0; near=> i.
have yi_neq0 : (y i != 0)%B.
  by near: i; exact: creal_neq0_always y_neq0.
by rewrite /= divff ?subrr ?normr0.
Unshelve. all: by end_near. Qed.

Lemma root_mul_algcreal (x y : algcreal) :
  ((annul_creal (div_algcreal x (inv_algcreal y))).[x * y] == 0)%CR.
Proof.
rewrite /div_algcreal /inv_algcreal.
case: (eq_algcreal_dec y) => [->|y_neq0]; apply: is_root_annul_creal.
- rewrite mul_creal0.
  case: eq_algcreal_dec => // neq_00.
  by move: (eq_creal_refl neq_00).
- case: eq_algcreal_dec => /= [yV_eq0|yV_neq0].
  + have : (y * y_neq0^-1 == 0)%CR by rewrite yV_eq0 mul_creal0.
    by rewrite div_creal_creal => /eq_creal_cst; rewrite oner_eq0.
  + case: simplify_algcreal => y' py'0_neq0 [y'_neq0 /= eq_yy'].
    rewrite -(@eq_creal_inv _ _ _ yV_neq0) //.
    by apply: eq_crealP => e e0; near=> i; rewrite /= invrK subrr normr0.
Unshelve. all: by end_near. Qed.

Definition mul_algcreal (x y : algcreal) :=
  AlgCReal (@monic_annul_creal _) (@root_mul_algcreal x y).

Lemma le_creal_neqVlt (x y : algcreal) : (x <= y)%CR -> {(x == y)%CR} + {(x < y)%CR}.
Proof.
move=> le_xy; case: (eq_algcreal_dec x y) => [eq_xy | neq_xy].
- by left.
- right.
  have [lt_xy | lt_yx] := neq_creal_ltVgt neq_xy.
  + exact: lt_xy.
  + by case: le_xy.
Qed.

Lemma neq_creal_ltVgt_dec (x y : creal F) :
  (x != y)%CR -> {(x < y)%CR} + {(y < x)%CR}.
Proof.
move=> neq_xy.
have sub_neq0 : ((x - y)%CR != 0)%CR.
  case: neq_xy => d d0 hd.
  by exists d => //; near do rewrite subr0.
have [[d N] hsep] := inv_crealP_subdef sub_neq0.
have /and3P[d0 hNd hsepN] := hsep.
pose i := maxn N (maxn (cauchymod x (d / 5)) (cauchymod y (d / 5))).
have hNi : (N <= i)%N by exact: leq_maxl.
have hxi : (cauchymod x (d / 5) <= i)%N.
  exact: leq_trans (leq_maxl _ _) (leq_maxr _ _).
have hyi : (cauchymod y (d / 5) <= i)%N.
  exact: leq_trans (leq_maxr _ _) (leq_maxr _ _).
have hdist : d <= `|x i - y i| by exact: creal_2separatedW hsep hNi.
have hx_near : \forall k \near \oo, `|x i - x k| < d / 5.
  by near do rewrite cauchymodP ?divr_gt0//.
have hy_near : \forall k \near \oo, `|y i - y k| < d / 5.
  by near do rewrite cauchymodP ?divr_gt0//.
have [le_xy | lt_yx] := lerP (x i) (y i).
- left; apply: (@lt_crealP _ d i i d0 x y) => //.
  rewrite -lerBrDl.
  by move: hdist; rewrite distrC ger0_norm // subr_ge0.
- right; apply: (@lt_crealP _ d i i d0 y x) => //.
  rewrite -lerBrDl.
  by move: hdist; rewrite gtr0_norm ?subr_gt0.
Unshelve. all: by end_near. Qed.

Lemma ltVge_algcreal_dec (x y : algcreal) : {(x < y)%CR} + {(y <= x)%CR}.
Proof.
have [eq_xy|neq_xy] := eq_algcreal_dec x y.
- by right; rewrite eq_xy.
- have [|lt_yx] := neq_creal_ltVgt_dec neq_xy.
  + exact: left.
  + exact: right (lt_crealW lt_yx).
Qed.

Definition lt_algcreal : rel algcreal := ltVge_algcreal_dec.
Definition le_algcreal : rel algcreal := fun x y => ~~ ltVge_algcreal_dec y x.

Lemma lt_algcrealP (x y : algcreal) : reflect (x < y)%CR (lt_algcreal x y).
Proof. by rewrite /lt_algcreal; case: ltVge_algcreal_dec; constructor. Qed.
Arguments lt_algcrealP {x y}.

Lemma le_algcrealP (x y : algcreal) : reflect (x <= y)%CR (le_algcreal x y).
Proof. by rewrite /le_algcreal; case: ltVge_algcreal_dec; constructor. Qed.
Arguments le_algcrealP {x y}.
Prenex Implicits lt_algcrealP le_algcrealP.

Definition exp_algcreal x n := iterop n mul_algcreal x one_algcreal.

Lemma exp_algcrealE x n : (exp_algcreal x n == x ^+ n)%CR.
Proof.
case: n=> // n; rewrite /exp_algcreal /exp_creal !iteropS.
by elim: n=> //= n ->.
Qed.

Definition horner_algcreal (p : {poly F}) x : algcreal :=
  \big[add_algcreal/zero_algcreal]_(i < size p)
   mul_algcreal (cst_algcreal p`_i) (exp_algcreal x i).

Lemma horner_algcrealE p x : (horner_algcreal p x == p.[x])%CR.
Proof.
rewrite horner_coef_creal.
apply: (big_ind2 (fun (u : algcreal) v => u == v)%CR)=> //.
  by move=> u u' v v' /= -> ->.
by move=> i _ /=; rewrite exp_algcrealE.
Qed.

Definition norm_algcreal (x : algcreal) :=
  if le_algcreal zero_algcreal x then x else opp_algcreal x.

Lemma norm_algcrealE (x : algcreal) : (norm_algcreal x == `|x|)%CR.
Proof.
rewrite /norm_algcreal /le_algcreal.
case: ltVge_algcreal_dec => /=[x_lt0|].
- apply: eq_crealP => e e0; near=> i.
  have hxi : x i < 0 by near: i; exact: creal_lt_always x_lt0.
  by rewrite /= [`|x i|]ler0_norm ?ltW // subrr normr0.
- move=> /(@le_creal_neqVlt zero_algcreal) /= [<-|x_gt0].
  + apply: eq_crealP => e e0; near=> i.
    by rewrite /= normr0 subrr normr0.
  + apply: eq_crealP => e e0; near=> i.
    have hxi : 0 < x i by near: i; exact: creal_gt0_always x_gt0.
    by rewrite /= [`|x i|]ger0_norm ?ltW // subrr normr0.
Unshelve. all: by end_near. Qed.

(**********************************************************************)
(* Theory of the "domain" of algebraic numbers: polynomial + interval *)
(**********************************************************************)
Record algdom := AlgDom {
  annul_algdom : {poly F};
  center_alg : F;
  radius_alg : F;
  _ : annul_algdom \is monic;
  _ : radius_alg >= 0;
  _ : annul_algdom.[center_alg - radius_alg]
      * annul_algdom.[center_alg + radius_alg] <= 0
}.

Lemma radius_alg_ge0 x : 0 <= radius_alg x. Proof. by case: x. Qed.

Lemma monic_annul_algdom x : annul_algdom x \is monic. Proof. by case: x. Qed.
Hint Resolve monic_annul_algdom : core.

Lemma annul_algdom_eq0 x : (annul_algdom x == 0) = false.
Proof. by rewrite (negPf (monic_neq0 _)). Qed.

Lemma algdomP x : (annul_algdom x).[center_alg x - radius_alg x]
  * (annul_algdom x).[center_alg x + radius_alg x] <= 0.
Proof. by case: x. Qed.

Definition algdom' := seq F.

Definition encode_algdom (x : algdom) : algdom' :=
  [:: center_alg x, radius_alg x & (annul_algdom x)].

Definition decode_algdom  (x : algdom') : option algdom :=
  if x is [::c, r & p']
  then let p := Poly p' in
    if ((p \is monic) =P true, (r >= 0) =P true,
       (p.[c - r] * p.[c + r] <= 0) =P true)
    is (ReflectT monic_p, ReflectT r_gt0, ReflectT hp)
      then Some (AlgDom monic_p r_gt0 hp)
      else None
  else None.

Lemma encode_algdomK : pcancel encode_algdom decode_algdom.
Proof.
case=> p c r monic_p r_ge0 hp /=; rewrite polyseqK.
do 3?[case: eqP; rewrite ?monic_p ?r_ge0 ?monic_p //] => monic_p' r_ge0' hp'.
by congr (Some (AlgDom _ _ _)); apply: bool_irrelevance.
Qed.

HB.instance Definition _ := Choice.copy algdom (pcan_type encode_algdomK).

Fixpoint to_algcreal_of (p : {poly F}) (c r : F) (i : nat) : F :=
  match i with
    | 0 => c
    | i.+1 =>
      let c' := to_algcreal_of p c r i in
        if p.[c' - r / 2 ^+ i] * p.[c'] <= 0
          then c' - r / 2 ^+ i.+1
          else c' + r / 2 ^+ i.+1
  end.

Lemma to_algcreal_of_recP p c r i : 0 <= r ->
  `|to_algcreal_of p c r i.+1 - to_algcreal_of p c r i| <= r * 2 ^- i.+1.
Proof.
move=> r_ge0 /=; case: ifP=> _; rewrite addrAC subrr add0r ?normrN ger0_norm //;
by rewrite mulr_ge0 ?invr_ge0 ?exprn_ge0 ?ler0n.
Qed.

Lemma to_algcreal_ofP p c r i j : 0 <= r -> (i <= j)%N ->
  `|to_algcreal_of p c r j - to_algcreal_of p c r i| <= r * 2 ^- i.
Proof.
move=> r_ge0 leij; pose r' := r * 2 ^- j * (2 ^+ (j - i) - 1).
apply: le_trans (_ : r' <= _); last first.
  rewrite /r' -mulrA ler_wpM2l // ler_pdivrMl ?exprn_gt0 ?ltr0n //.
  rewrite -{2}(subnK leij) exprD mulfK ?gt_eqF ?exprn_gt0 ?ltr0n //.
  by rewrite gerDl lerN10.
rewrite /r' subrX1 addrK mul1r -{1 2}(subnK leij); set f := _  c r.
elim: (_ - _)%N=> [|k ihk]; first by rewrite subrr normr0 big_ord0 mulr0 lexx.
rewrite addSn big_ord_recl /= mulrDr.
rewrite (le_trans (ler_distD (f (k + i)%N) _ _)) //.
rewrite lerD ?expr0 ?mulr1 ?to_algcreal_of_recP // (le_trans ihk) //.
rewrite exprSr invfM -!mulrA !ler_wpM2l ?invr_ge0 ?exprn_ge0 ?ler0n //.
by rewrite mulr_sumr ler_sum // => l _ /=; rewrite exprS mulKf ?pnatr_eq0.
Qed.

Lemma alg_to_crealP (x : algdom) :
  creal_axiom_sig (to_algcreal_of (annul_algdom x) (center_alg x) (radius_alg x)).
Proof.
exists (fun e => Num.bound (e^-1 * radius_alg x)) => /= e i j e_gt0 hi hj.
wlog leij : i j {hi} hj / (j <= i)%N.
  move=> hwlog; case/orP: (leq_total i j) => /hwlog; last exact.
  by rewrite distrC; exact.
rewrite (le_lt_trans (to_algcreal_ofP _ _ _ _)) ?radius_alg_ge0 //.
by rewrite ltr_pdivrMr ?gtr0E // -ltr_pdivrMl// upper_nthrootP.
Qed.

Definition alg_to_creal x := CReal (alg_to_crealP x).

Lemma exp2k_crealP : creal_axiom_sig (fun i => 2 ^- i : F).
Proof.
exists (fun e => Num.bound e^-1) => e i j e0 ei ej.
wlog leij : i j {ej} ei / (i <= j)%N.
  move=> hwlog.
  case/orP: (leq_total i j) => /hwlog; first exact.
  by rewrite distrC; exact.
rewrite ger0_norm ?subr_ge0.
  by rewrite ?lef_pV2 -?topredE /= ?gtr0E // ler_eXn2l ?ltr1n.
rewrite -(@ltr_pM2l _ (2 ^+ i)) ?gtr0E//.
rewrite mulrBr mulfV ?gt_eqF ?gtr0E//.
rewrite (@le_lt_trans _ _ 1)// ?gerDl ?oppr_le0 ?mulr_ge0 ?ger0E//.
by rewrite -ltr_pdivrMr // mul1r upper_nthrootP.
Qed.

Definition exp2k_creal := CReal exp2k_crealP.

Lemma exp2k_creal_eq0 : (exp2k_creal == 0)%CR.
Proof.
move=> [d d0 hd].
near \oo => i.
have [+ hlt] : d <= `|exp2k_creal i| /\ `|exp2k_creal i| < d.
  split.
  - near: i.
    by apply: filterS hd => j /=; rewrite subr0.
  - rewrite /= gtr0_norm ?gtr0E // -ltf_pV2 -?topredE /= ?gtr0E ?d0//.
    rewrite invrK upper_nthrootP//.
    by near: i.
by rewrite leNgt hlt.
Unshelve. all: by end_near. Qed.

Lemma to_algcrealP (x : algdom) : ((annul_algdom x).[alg_to_creal x] == 0)%CR.
Proof.
set u := alg_to_creal _.
set p := annul_algdom _.
pose r := radius_alg x.
pose cr := cst_creal r.
have : (p.[u - cr * exp2k_creal] * p.[u + cr * exp2k_creal] <= 0)%CR.
  apply: (@le_crealP _ 0%N) => i _ /=.
  rewrite -/p -/r.
  set c := center_alg _.
  elim: i => /= [|i].
  - by rewrite !expr0 divr1 algdomP.
  - set c' := to_algcreal_of _ _ _ => ihi.
    have [] := lerP (_ * p.[c' i]).
    + rewrite addrNK -addrA -opprD -mulr2n -[_ / _ *+ _]mulr_natr.
      by rewrite -mulrA exprSr invfM mulfVK ?pnatr_eq0.
    + rewrite addrK -addrA -mulr2n -[_ / _ *+ _]mulr_natr.
      rewrite -mulrA exprSr invfM mulfVK ?pnatr_eq0 //.
      move=> /ler_pM2l <-.
      rewrite mulr0 mulrCA !mulrA [X in X * _]mulrAC -mulrA.
      by rewrite mulr_ge0_le0 // -expr2 exprn_even_ge0.
rewrite exp2k_creal_eq0 mul_creal0 opp_creal0 add_creal0 => + pu0.
apply.
case: pu0 => /= d d0 hd.
exists (d ^+ 2).
- by rewrite exprn_gt0.
- near=> i.
  have hdi : d <= `|p.[u i]|.
    near: i.
    by apply: filterS hd => j /=; rewrite subr0.
  rewrite add0r [u]lock /= -!expr2 -lock.
  rewrite -[p.[u i] ^+ 2]ger0_norm ?exprn_even_ge0 // normrX.
  by rewrite ler_pXn2r -?topredE /= ?(ltW d0) ?normr_ge0.
Unshelve. all: by end_near. Qed.

Definition to_algcreal_rec (x : algdom) :=
  AlgCReal (monic_annul_algdom x) (@to_algcrealP x).
(* "Encoding" function from algdom to algcreal *)
Definition to_algcreal := locked to_algcreal_rec.

(* "Decoding" function, constructed interactively *)

Let deriv_gt0_mono (p : {poly F}) (x : creal F) (d : F) (i0 : nat) :
  0 < d ->
  (cauchymod (p^`().[x])%CR (d / 2) <= i0)%N ->
  d <= p^`().[x i0] ->
  {r : F & 0 < r & {i & (cauchymod x r <= i)%N & strong_mono p (x i) r}}.
Proof.
move=> d0 hi0 hdi0.
have [b b0 hb] := ubound_subproof_sig x.
pose delta := d / 2.
have delta0 : 0 < delta by rewrite /delta divr_gt0.
pose b1 := poly_accr_bound p^`() 0 (1 + b).
pose b2 := poly_accr_bound2 p 0 (1 + b).
pose r : F := Num.min 1 (Num.min (delta / 4 / b1) (delta / 4 / b2 / 2)).
have r0 : 0 < r.
  rewrite /r !lt_min ltr01/= !divr_gt0 ?poly_accr_bound2_gt0//.
  exact: poly_accr_bound_gt0.
pose i := maxn (cauchymod x r) (maxn i0 (cauchymod (p^`().[x])%CR delta)).
have hxi : (cauchymod x r <= i)%N by rewrite /i leq_maxl.
have hi0i : (i0 <= i)%N by exact: leq_trans (leq_maxl _ _) (leq_maxr _ _).
have hp'i : (cauchymod (p^`().[x])%CR delta <= i)%N.
  exact: leq_trans (leq_maxr _ _) (leq_maxr _ _).
have hp'dist : `|p^`().[x i0] - p^`().[x i]| < delta.
  exact: cauchymodP delta0 hi0 hp'i.
have hdelta : delta <= p^`().[x i].
  have hlow : p^`().[x i0] - delta < p^`().[x i].
    by move: hp'dist; rewrite distrC ltr_distl => /andP[].
  rewrite ltW// (le_lt_trans _ hlow)// lerBrDr.
  by move: hdi0; rewrite -(splitr d).
exists r => //; exists i => //; left; split => /=.
  exists (delta / 4); first by rewrite divr_gt0.
  move=> y z yz yxir zxir.
  have y1b : `|y| <= 1 + b.
    rewrite (@le_trans _ _ (r + `|x i|)) ?lerD ?ge_min ?lexx//.
    by rewrite -lerBlDr (le_trans (lerB_dist _ _)).
  have z1b : `|z| <= 1 + b.
    rewrite (@le_trans _ _ (r + `|x i|)) ?lerD ?ge_min ?lexx//.
    by rewrite -lerBlDr (le_trans (lerB_dist _ _)).
  have xi1b : `|x i| <= 1 + b by rewrite (le_trans (hb i)) // lerDr.
  have := @poly_accr_bound2P _ p 0 (1 + b) z y.
  rewrite eq_sym !subr0 => /(_ yz z1b y1b).
  rewrite ler_distl => /andP[+ _]; apply: lt_le_trans.
  rewrite -ltrBlDr opprK.
  have := @poly_accr_bound1P _ p^`() 0 (1 + b) (x i) z.
  rewrite !subr0 => /(_ xi1b z1b).
  rewrite ler_distl => /andP[+ _]; apply: lt_le_trans.
  rewrite -ltrBlDr opprK (lt_le_trans _ hdelta)//.
  rewrite [ltRHS](splitf 4) /= -!addrA ltrD2l ltr_pwDl ?divr_gt0//.
  rewrite -/b1 -/b2 lerD//.
  - rewrite -ler_pdivlMr ?poly_accr_bound2_gt0 //.
    rewrite (le_trans (ler_distD (x i) _ _))//.
    rewrite (@le_trans _ _ (r * 2))//.
      by rewrite mulrDr mulr1 lerD // distrC.
    by rewrite -ler_pdivlMr ?ltr0n // /r !ge_min lexx !orbT.
  - rewrite -ler_pdivlMr ?poly_accr_bound_gt0//.
    by rewrite (le_trans zxir)// /r 2!ge_min lexx orbT.
move=> y yxi1.
have y1b : `|y| <= 1 + b.
  rewrite (@le_trans _ _ (r + `|x i|)) ?lerD ?ge_min ?lexx//.
  by rewrite -lerBlDr (le_trans (lerB_dist _ _)).
have xi1b : `|x i| <= 1 + b by rewrite (le_trans (hb i)) // lerDr.
have := @poly_accr_bound1P _ p^`() 0 (1 + b) (x i) y.
rewrite !subr0 => /(_ xi1b y1b).
rewrite ler_distl => /andP[+ _]; apply: lt_le_trans.
rewrite subr_gt0 -/b1.
apply: lt_le_trans hdelta.
rewrite (@le_lt_trans _ _ (r * b1))//.
  by rewrite ler_wpM2r ?poly_accr_bound_ge0.
rewrite -ltr_pdivlMr ?poly_accr_bound_gt0//.
rewrite /r 2!gt_min ltr_pM2r ?invr_gt0//; first by rewrite poly_accr_bound_gt0.
by rewrite gtr_pMr// invf_lt1// ltr1n/= orbT.
Qed.

Let neq0_creal_sign (x : creal F) : (x != 0)%CR ->
  ({d : F & {i & [/\ 0 < d, (cauchymod x (d / 2) <= i)%N & d <= x i]}} +
   {d : F & {i & [/\ 0 < d, (cauchymod x (d / 2) <= i)%N & x i <= - d]}})%type.
Proof.
move=> /inv_crealP_subdef[[d N] sepxdN].
have /and3P[d0 _ _] := sepxdN.
pose d' := d / 2.
have d'0 : 0 < d' by rewrite /d' divr_gt0.
pose i := maxn N (cauchymod x (d' / 2)).
have Ni : (N <= i)%N by rewrite /i leq_maxl.
have modd' : (cauchymod x (d' / 2) <= i)%N by rewrite /i leq_maxr.
have d'xi : d' <= `|x i|.
  have : d <= `|x i| by exact: creal_2separatedW sepxdN Ni.
  by apply: le_trans; rewrite ger_pMr// invf_le1// ler1n.
have [xi_ge0 | xi_lt0] := lerP 0 (x i).
- left; exists d', i; split => //.
  by move: d'xi; rewrite ger0_norm.
- right; exists d', i; split => //.
  by move: d'xi; rewrite ltr0_norm// lerNr.
Qed.

Lemma deriv_neq0_mono (p : {poly F}) (x : creal F) :
  (p^`().[x] != 0)%CR ->
  {r : F & 0 < r & {i & (cauchymod x r <= i)%N & strong_mono p (x i) r}}.
Proof.
move=> hp.
have [[d [i [d0 hdi hpos]]]|[d [i [d0 hdi hneg]]]] := neq0_creal_sign hp.
  exact: (deriv_gt0_mono d0 hdi hpos).
pose d' := d / 2.
have d'0 : 0 < d' by rewrite /d' divr_gt0.
pose j := maxn i (cauchymod ((- p)^`().[x])%CR (d' / 2)).
have ij : (i <= j)%N by rewrite /j leq_maxl.
have modNp' : (cauchymod ((- p)^`().[x])%CR (d' / 2) <= j)%N.
  by rewrite /j leq_maxr.
have hpdist : `|p^`().[x i] - p^`().[x j]| < d / 2.
  by rewrite (@cauchymodP _ (p^`().[x])%CR (d / 2) i j)// (leq_trans hdi).
have p'd' : p^`().[x j] < - d'.
  have /lt_le_trans ->// : p^`().[x j] < p^`().[x i] + d'.
    by move: hpdist; rewrite distrC ltr_distl => /andP[].
  have <- : - d + d' = - d' by rewrite (splitr d) opprD subrK.
  by rewrite lerD2r.
have d'p' : d' <= (- p)^`().[x j] by rewrite /= derivN hornerN lerNr ltW.
have [r r0 [k xrk sm]] := @deriv_gt0_mono (- p) x d' j d'0 modNp' d'p'.
exists r => //; exists k => //.
by rewrite -[p]opprK; exact: strong_monoN.
Qed.

Lemma to_algdom_exists (x : algcreal) :
  { y : algdom | (to_algcreal y == x)%CR }.
Proof.
pose p := annul_creal x.
move: {2}(size p) (leqnn (size p)) => n.
elim: n x @p => [x p|n ihn x p le_sp_Sn].
  by rewrite leqn0 size_poly_eq0 /p annul_creal_eq0.
move: le_sp_Sn; rewrite leq_eqVlt.
have [|//|eq_sp_Sn _] := ltngtP.
  by rewrite ltnS => /ihn ihnp _; exact: ihnp.
have px0 := @root_annul_creal x; rewrite -/p -/root in px0.
have [|ncop] := boolP (coprimep p p^`()).
  move/coprimep_root => /(_ _ px0) /deriv_neq0_mono [r r_gt0 [i ir sm]].
  have p_chg_sign : p.[x i - r] * p.[x i + r] <= 0.
    have [/accr_pos_incr hp|/accr_neg_decr hp] := sm.
      have hpxj j : (i <= j)%N ->
          (p.[x i - r] <= p.[x j]) * (p.[x j] <= p.[x i + r]).
        move=> hj.
        suff:  p.[x i - r] <= p.[x j] <= p.[x i + r] by case/andP=> -> ->.
        rewrite !hp 1?addrAC ?subrr ?add0r ?normrN;
        rewrite ?(gtr0_norm r_gt0)//;
          [by rewrite ltW ?cauchymodP ?(leq_trans _ hj)..|].
        by rewrite -ler_distl ltW ?cauchymodP ?(leq_trans _ hj).
      rewrite mulr_le0_ge0 //; apply/le_creal_cst; rewrite -px0;
      by apply: (@le_crealP _ i)=> h hj /=; rewrite hpxj.
    have hpxj j : (i <= j)%N ->
        (p.[x i + r] <= p.[x j]) * (p.[x j] <= p.[x i - r]).
      move=> hj.
      suff:  p.[x i + r] <= p.[x j] <= p.[x i - r] by case/andP => -> ->.
      rewrite !hp 1?addrAC ?subrr ?add0r ?normrN;
      rewrite ?(gtr0_norm r_gt0) //;
        [by rewrite ltW ?cauchymodP ?(leq_trans _ hj)..|].
      by rewrite andbC -ler_distl ltW ?cauchymodP ?(leq_trans _ hj).
    rewrite mulr_ge0_le0 //; apply/le_creal_cst; rewrite -px0;
    by apply: (@le_crealP _ i)=> h hj /=; rewrite hpxj.
  pose y := AlgDom (monic_annul_creal x) (ltW r_gt0) p_chg_sign.
  have eq_py_px: (p.[to_algcreal y] == p.[x])%CR.
    rewrite /to_algcreal -lock.
    by have := @to_algcrealP y; rewrite /= -/p=> ->; apply: eq_creal_sym.
  exists y.
  have [k k_gt0 hk] := strong_mono_bound sm.
  apply: eq_crealP => e e_gt0.
  have ek_gt0 : 0 < e / k by rewrite divr_gt0.
  near=> j.
  have [hij hpj] : (i <= j)%N /\ `|p.[to_algcreal y j] - p.[x j]| < e / k.
    split.
    - by near: j.
    - by near: j; exact: (asympt_eq eq_py_px).
have hdist : `|to_algcreal y j - x j| <= k * `|p.[to_algcreal y j] - p.[x j]|.
  apply: hk.
  - rewrite /to_algcreal -lock.
    rewrite (le_trans (to_algcreal_ofP _ _ _ (leq0n _))) ?(ltW r_gt0)//.
    by rewrite expr0 divr1.
  - by rewrite ltW // distrC (cauchymodP r_gt0 ir)// (leq_trans ir).
  by rewrite (le_lt_trans hdist)// -ltr_pdivlMl// mulrC.
case: (@smaller_factor _ p p^`() x); rewrite ?monic_annul_creal //.
- rewrite gtNdvdp // -?size_poly_eq0 size_deriv eq_sp_Sn //=.
  apply: contra ncop => /eqP n_eq0.
  move: eq_sp_Sn; rewrite n_eq0.
  by move=> /eqP /size_poly1P [c c_neq0 ->]; rewrite derivC coprimep0 polyC_eqp1.
- move=> r /andP[hsr monic_r] rx_eq0.
  apply: (ihn (AlgCReal monic_r rx_eq0)) => /=.
  by rewrite -ltnS -eq_sp_Sn.
Unshelve. all: by end_near. Qed.

Definition to_algdom x := projT1 (to_algdom_exists x).

Lemma to_algdomK x : (to_algcreal (to_algdom x) == x)%CR.
Proof. by rewrite /to_algdom; case: to_algdom_exists. Qed.

Lemma eq_algcreal_to_algdom x : eq_algcreal (to_algcreal (to_algdom x)) x.
Proof. by apply/eq_algcrealP; apply: to_algdomK. Qed.

(* Explicit encoding to a choice type *)
Canonical eq_algcreal_encModRel := EncModRel eq_algcreal eq_algcreal_to_algdom.

Local Open Scope quotient_scope.
Local Notation "\pi ( x )" := (\pi x) : quotient_scope.

(***************************************************************************)
(* Algebraic numbers are the quotient of algcreal by their setoid equality *)
(***************************************************************************)
Definition alg := {eq_quot eq_algcreal}.

HB.instance Definition _ := Choice.on alg.
HB.instance Definition _ := EqQuotient.on alg.

Definition to_alg_def (phF : phant F) : F -> alg :=
  lift_embed alg cst_algcreal.
Notation to_alg := (@to_alg_def (Phant F)).
Notation "x %:RA" := (to_alg x)
  (at level 1, left associativity, format "x %:RA").
Local Notation "p ^ f" := (map_poly f p) : ring_scope.

Canonical to_alg_pi_morph := PiEmbed to_alg.

Local Notation zero_alg := 0%:RA.
Local Notation one_alg := 1%:RA.

Lemma equiv_alg (x y : algcreal) : (x == y)%CR <-> (x = y %[mod alg]).
Proof.
split; first by move=> /eq_algcrealP /eqquotP ->.
by move=> /eqquotP /eq_algcrealP.
Qed.

Lemma nequiv_alg (x y : algcreal) : reflect (x != y)%CR (x != y %[mod alg]).
Proof. by rewrite eqquotE; apply: neq_algcrealP. Qed.
Arguments nequiv_alg {x y}.
Prenex Implicits nequiv_alg.

Lemma pi_algK (x : algcreal) : (repr (\pi_alg x) == x)%CR.
Proof. by apply/equiv_alg; rewrite reprK. Qed.

Definition add_alg := lift_op2 alg add_algcreal.

Lemma pi_add : {morph \pi_alg : x y / add_algcreal x y >-> add_alg x y}.
Proof. by unlock add_alg=> x y; rewrite -equiv_alg /= !pi_algK. Qed.

Canonical add_pi_morph := PiMorph2 pi_add.

Definition opp_alg := lift_op1 alg opp_algcreal.

Lemma pi_opp : {morph \pi_alg : x / opp_algcreal x >-> opp_alg x}.
Proof. by unlock opp_alg=> x; rewrite -equiv_alg /= !pi_algK. Qed.

Canonical opp_pi_morph := PiMorph1 pi_opp.

Definition mul_alg := lift_op2 alg mul_algcreal.

Lemma pi_mul : {morph \pi_alg : x y / mul_algcreal x y >-> mul_alg x y}.
Proof. by unlock mul_alg=> x y; rewrite -equiv_alg /= !pi_algK. Qed.

Canonical mul_pi_morph := PiMorph2 pi_mul.

Definition inv_alg := lift_op1 alg inv_algcreal.

Lemma pi_inv : {morph \pi_alg : x / inv_algcreal x >-> inv_alg x}.
Proof.
unlock inv_alg=> x; symmetry; rewrite -equiv_alg /= /inv_algcreal.
case: eq_algcreal_dec=> /= [|x'_neq0].
  by rewrite pi_algK; case: eq_algcreal_dec.
move: x'_neq0 (x'_neq0); rewrite {1}pi_algK.
case: eq_algcreal_dec=> // x'_neq0' x_neq0 x'_neq0 /=.
by apply: eq_creal_inv; rewrite pi_algK.
Qed.

Canonical inv_pi_morph := PiMorph1 pi_inv.

Lemma add_algA : associative add_alg.
Proof.
elim/quotW => x; elim/quotW => y; elim/quotW => z.
rewrite !piE -equiv_alg.
by apply: eq_crealP => e e0; near=> i; rewrite /= addrA subrr normr0.
Unshelve. all: by end_near. Qed.

Lemma add_algC : commutative add_alg.
Proof.
elim/quotW => x; elim/quotW => y; rewrite !piE -equiv_alg /=.
apply: eq_crealP => e e0; near=> i.
by rewrite /= [X in _ - X]addrC subrr normr0.
Unshelve. all: by end_near. Qed.

Lemma add_0alg : left_id zero_alg add_alg.
Proof. by elim/quotW=> x; rewrite !piE -equiv_alg /= add_0creal. Qed.

Lemma add_Nalg : left_inverse zero_alg opp_alg add_alg.
Proof.
elim/quotW => x; rewrite !piE -equiv_alg /=.
by apply: eq_crealP => e e0; near=> i; rewrite /= addNr subr0 normr0.
Unshelve. all: by end_near. Qed.

HB.instance Definition _ := GRing.isZmodule.Build alg
  add_algA add_algC add_0alg add_Nalg.

Lemma add_pi x y : \pi_alg x + \pi_alg y
  = \pi_alg (add_algcreal x y).
Proof. by rewrite [_ + _]piE. Qed.

Lemma opp_pi x : - \pi_alg x  = \pi_alg (opp_algcreal x).
Proof. by rewrite [- _]piE. Qed.

Lemma zeroE : 0 = \pi_alg zero_algcreal.
Proof. by rewrite [0]piE. Qed.

Lemma sub_pi x y : \pi_alg x - \pi_alg y
  = \pi_alg (add_algcreal x (opp_algcreal y)).
Proof. by rewrite [_ - _]piE. Qed.

Lemma mul_algC : commutative mul_alg.
Proof.
elim/quotW => x; elim/quotW => y; rewrite !piE -equiv_alg /=.
by apply: eq_crealP => e e0; near=> i; rewrite /= mulrC subrr normr0.
Unshelve. all: by end_near. Qed.

Lemma mul_algA : associative mul_alg.
Proof.
elim/quotW => x; elim/quotW => y; elim/quotW => z.
rewrite !piE -equiv_alg /=.
by apply: eq_crealP => e e0; near=> i; rewrite /= mulrA subrr normr0.
Unshelve. all: by end_near. Qed.

Lemma mul_1alg : left_id one_alg mul_alg.
Proof. by elim/quotW=> x; rewrite piE -equiv_alg /= mul_1creal. Qed.

Lemma mul_alg_addl : left_distributive mul_alg add_alg.
Proof.
elim/quotW => x; elim/quotW => y; elim/quotW => z.
rewrite !piE -equiv_alg /=.
by apply: eq_crealP => e e0; near=> i; rewrite /= mulrDl subrr normr0.
Unshelve. all: by end_near. Qed.

Arguments neq_creal_cst {F x y}.
Prenex Implicits neq_creal_cst.

Lemma nonzero1_alg : one_alg != zero_alg.
Proof. by rewrite piE -(rwP neq_algcrealP) (rwP neq_creal_cst) oner_eq0. Qed.

HB.instance Definition _ := GRing.Zmodule_isComNzRing.Build alg
  mul_algA mul_algC mul_1alg mul_alg_addl nonzero1_alg.

Lemma mul_pi x y : \pi_alg x * \pi_alg y
  = \pi_alg (mul_algcreal x y).
Proof. by rewrite [_ * _]piE. Qed.

Lemma oneE : 1 = \pi_alg one_algcreal.
Proof. by rewrite [1]piE. Qed.

Lemma mul_Valg (x : alg) :
  x != zero_alg -> mul_alg (inv_alg x) x = one_alg.
Proof.
elim/quotW: x => x.
rewrite piE -(rwP neq_algcrealP) /= => x_neq0.
apply/eqP; rewrite piE.
apply/eq_algcrealP.
rewrite /= /inv_algcreal.
case: eq_algcreal_dec => [/(_ x_neq0) //|/= x_neq0'].
apply: eq_crealP => e e0; near=> i.
have xi_neq0 : (x i != 0)%B.
  by near: i; exact: creal_neq0_always x_neq0'.
by rewrite /= mulVf ?subrr ?normr0.
Unshelve. all: by end_near. Qed.

Lemma inv_alg0 : inv_alg zero_alg = zero_alg.
Proof.
rewrite !piE -equiv_alg /= /inv_algcreal.
by case: eq_algcreal_dec=> //= zero_neq0; move: (eq_creal_refl zero_neq0).
Qed.

Lemma to_alg_zmod_morphism : zmod_morphism to_alg.
Proof.
move=> x y /=; rewrite !piE /= -equiv_alg /=.
by apply: eq_crealP => e e0; near=> i; rewrite /= subrr normr0.
Unshelve. all: by end_near. Qed.

HB.instance Definition _ :=
  Algebra.isZmodMorphism.Build F alg to_alg to_alg_zmod_morphism.

Lemma to_alg_monoid_morphism : monoid_morphism to_alg.
Proof.
split => [|x y] //.
rewrite !piE -equiv_alg.
by apply: eq_crealP => e e0; near=> i; rewrite /= subrr normr0.
Unshelve. all: by end_near. Qed.

HB.instance Definition _ :=
  GRing.isMonoidMorphism.Build F alg to_alg to_alg_monoid_morphism.

Lemma expn_pi (x : algcreal) (n : nat) :
  (\pi_alg x) ^+ n = \pi_alg (exp_algcreal x n).
Proof.
rewrite /exp_algcreal; case: n=> [|n]; first by rewrite expr0 oneE.
rewrite exprS iteropS; elim: n=> /= [|n ihn]; rewrite ?expr0 ?mulr1 //.
by rewrite exprS ihn mul_pi.
Qed.

Lemma horner_pi (p : {poly F}) (x : algcreal) :
  (p ^ to_alg).[\pi_alg x] = \pi_alg (horner_algcreal p x).
Proof.
rewrite horner_coef /horner_algcreal size_map_poly.
apply: (big_ind2 (fun x y => x = \pi_alg y)).
+ by rewrite zeroE.
+ by move=> u u' v v' -> ->; rewrite [_ + _]piE.
by move=> i /= _; rewrite expn_pi coef_map /= [_ * _]piE.
Qed.

(* Defining annihilating polynomials for algebraics *)
Definition annul_alg : alg -> {poly F} := locked (annul_creal \o repr).

Lemma root_annul_algcreal (x : algcreal) : ((annul_alg (\pi x)).[x] == 0)%CR.
Proof. by unlock annul_alg; rewrite /= -pi_algK root_annul_creal. Qed.

Lemma root_annul_alg (x : alg) : root ((annul_alg x) ^ to_alg) x.
Proof.
apply/rootP; rewrite -[x]reprK horner_pi /= zeroE -equiv_alg.
by rewrite horner_algcrealE root_annul_algcreal.
Qed.

Lemma monic_annul_alg (x : alg) : annul_alg x \is monic.
Proof. by unlock annul_alg; rewrite monic_annul_creal. Qed.

Lemma annul_alg_neq0 (x : alg) : annul_alg x != 0.
Proof. by rewrite monic_neq0 ?monic_annul_alg. Qed.

HB.instance Definition _ := GRing.ComNzRing_isField.Build alg mul_Valg inv_alg0.

Lemma inv_pi x : (\pi_alg x)^-1  = \pi_alg (inv_algcreal x).
Proof. by rewrite [_^-1]piE. Qed.

Lemma div_pi x y : \pi_alg x / \pi_alg y
  = \pi_alg (mul_algcreal x (inv_algcreal y)).
Proof. by rewrite [_ / _]piE. Qed.

Definition lt_alg := lift_fun2 alg lt_algcreal.
Definition le_alg := lift_fun2 alg le_algcreal.

Lemma lt_alg_pi : {mono \pi_alg : x y / lt_algcreal x y >-> lt_alg x y}.
Proof.
move=> x y; unlock lt_alg; rewrite /lt_algcreal.
by do 2!case: ltVge_algcreal_dec=> //=; rewrite !pi_algK.
Qed.

Canonical lt_alg_pi_mono := PiMono2 lt_alg_pi.

Lemma le_alg_pi : {mono \pi_alg : x y / le_algcreal x y >-> le_alg x y}.
Proof.
move=> x y; unlock le_alg; rewrite /le_algcreal.
by do 2!case: ltVge_algcreal_dec=> //=; rewrite !pi_algK.
Qed.

Canonical le_alg_pi_mono := PiMono2 le_alg_pi.

Definition norm_alg := lift_op1 alg norm_algcreal.

Lemma norm_alg_pi : {morph \pi_alg : x / norm_algcreal x >-> norm_alg x}.
Proof.
move=> x; unlock norm_alg; rewrite /norm_algcreal /le_algcreal.
by do 2!case: ltVge_algcreal_dec=> //=; rewrite !(pi_opp, pi_algK, reprK).
Qed.

Canonical norm_alg_pi_morph := PiMorph1 norm_alg_pi.

Lemma add_alg_gt0 x y :
  lt_alg zero_alg x -> lt_alg zero_alg y ->
  lt_alg zero_alg (x + y).
Proof.
rewrite -[x]reprK -[y]reprK !piE -!(rwP lt_algcrealP).
move=> [dx dx0 hdx] [dy dy0 hdy].
exists (dx + dy); first by rewrite addr_gt0.
near=> i.
have [hxi hyi] : dx <= repr x i /\ dy <= repr y i.
  split.
  - near: i.
    apply: filterS hdx => j /=.
    by rewrite add0r.
  - near: i.
    apply: filterS hdy => j /=.
    by rewrite add0r.
by rewrite /= add0r lerD.
Unshelve. all: by end_near. Qed.

Lemma mul_alg_gt0 x y :
  lt_alg zero_alg x -> lt_alg zero_alg y ->
  lt_alg zero_alg (x * y).
Proof.
rewrite -[x]reprK -[y]reprK !piE -!(rwP lt_algcrealP).
move=> [dx dx0 hdx] [dy dy0 hdy].
exists (dx * dy); first by rewrite pmulr_rgt0.
near=> i.
have [hxi hyi] : dx <= repr x i /\ dy <= repr y i.
  split.
  - near: i; apply: filterS hdx => j /=.
    by rewrite add0r.
  - near: i; apply: filterS hdy => j /=.
    by rewrite add0r.
by rewrite /= add0r ler_pM// ltW.
Unshelve. all: by end_near. Qed.

Lemma gt0_alg_nlt0 x : lt_alg zero_alg x -> ~~ lt_alg x zero_alg.
Proof.
rewrite -[x]reprK !piE -!(rwP lt_algcrealP, rwP le_algcrealP).
exact: lt_crealW.
Qed.

Lemma sub_alg_gt0 x y : lt_alg zero_alg (y - x) = lt_alg x y.
Proof.
rewrite -[x]reprK -[y]reprK !piE.
apply/lt_algcrealP/lt_algcrealP => /=.
- move=> [d d0 hd].
  exists d => //; apply: filterS hd => i /=.
  by rewrite add0r -lerBlDr opprK addrC.
- move=> [d d0 hd].
  exists d => //; apply: filterS hd => i /=.
  by rewrite add0r -lerBlDr opprK addrC.
Qed.

Lemma lt0_alg_total (x : alg) : x != zero_alg ->
  lt_alg zero_alg x || lt_alg x zero_alg.
Proof.
rewrite -[x]reprK !piE => /neq_algcrealP /= x_neq0.
apply/orP.
rewrite -!(rwP lt_algcrealP).
case: (neq_creal_ltVgt x_neq0) => [lt_x0 | lt_0x].
- by right.
- by left.
Qed.

Lemma norm_algN x : norm_alg (- x) = norm_alg x.
Proof.
rewrite -[x]reprK !piE /= -equiv_alg !norm_algcrealE.
by apply: eq_crealP => e e0; near=> i; rewrite /= normrN subrr normr0.
Unshelve. all: by end_near. Qed.

Lemma ge0_norm_alg x : le_alg 0 x -> norm_alg x = x.
Proof. by rewrite -[x]reprK !piE /= /norm_algcreal => ->. Qed.

Lemma lt_alg0N (x : alg) : lt_alg 0 (- x) = lt_alg x 0.
Proof. by rewrite -sub0r sub_alg_gt0. Qed.

Lemma lt_alg00 : lt_alg zero_alg zero_alg = false.
Proof. by have /implyP := @gt0_alg_nlt0 0; case: lt_alg. Qed.

Lemma le_alg_def x y : le_alg x y = (x == y) || lt_alg x y.
Proof.
rewrite -[x]reprK -[y]reprK piE [lt_alg _ _]piE; apply/le_algcrealP/orP.
  move=> /le_creal_neqVlt [/eq_algcrealP/eqquotP/eqP-> //|lt_xy]; first by left.
  by right; apply/lt_algcrealP.
by move=> [/eqP/eqquotP/eq_algcrealP-> //| /lt_algcrealP /lt_crealW].
Qed.

HB.instance Definition _ := Num.IntegralDomain_isLtReal.Build alg
  add_alg_gt0 mul_alg_gt0 gt0_alg_nlt0 sub_alg_gt0 lt0_alg_total norm_algN
  ge0_norm_alg le_alg_def.

Lemma lt_pi x y : (\pi_alg x < \pi y) = lt_algcreal x y.
Proof. by rewrite [_ < _]lt_alg_pi. Qed.

Lemma le_pi x y : (\pi_alg x <= \pi y) = le_algcreal x y.
Proof. by rewrite [_ <= _]le_alg_pi. Qed.

Lemma norm_pi (x : algcreal) : `|\pi_alg x| = \pi (norm_algcreal x).
Proof. by rewrite [`|_|]piE. Qed.

Lemma lt_algP (x y : algcreal) : reflect (x < y)%CR (\pi_alg x < \pi y).
Proof. by rewrite lt_pi; apply: lt_algcrealP. Qed.
Arguments lt_algP {x y}.

Lemma le_algP (x y : algcreal) : reflect (x <= y)%CR (\pi_alg x <= \pi y).
Proof. by rewrite le_pi; apply: le_algcrealP. Qed.
Arguments le_algP {x y}.
Prenex Implicits lt_algP le_algP.

Lemma ler_to_alg : {mono to_alg : x y / x <= y}.
Proof.
apply: le_mono=> x y lt_xy; rewrite !piE -(rwP lt_algP).
by apply/lt_creal_cst; rewrite lt_xy.
Qed.

Lemma ltr_to_alg : {mono to_alg : x y / x < y}.
Proof. by apply: leW_mono; apply: ler_to_alg. Qed.

Lemma normr_to_alg : { morph to_alg : x / `|x| }.
Proof.
move=> x /=; have [] := ger0P; have [] := ger0P x%:RA;
  rewrite ?rmorph0 ?rmorphN ?oppr0 //=.
  by rewrite ltr_to_alg leNgt => ->.
by rewrite ler_to_alg ltNge => ->.
Qed.

Lemma inf_alg_proof x : {d | 0 < d & 0 < x -> (d%:RA < x)}.
Proof.
have [|] := lerP; first by exists 1.
elim/quotW: x => x; rewrite zeroE => /lt_algP /= x_gt0.
have x_neq0 : (x != 0)%CR by exact: gt_creal_neq.
have [[d [i [d0 hdi hpos]]] |[d [i [d0 hdi hneg]]]] := neq0_creal_sign x_neq0.
- exists (d / 4); first by rewrite divr_gt0.
  rewrite piE -(rwP lt_algP) /= => _.
  exists (d / 4); first by rewrite divr_gt0.
  near=> j.
  have hij : (i <= j)%N by near: j.
  have hdj : (cauchymod x (d / 2) <= j)%N by exact: leq_trans hdi hij.
  have hdist : `|x i - x j| < d / 2 by rewrite cauchymodP// divr_gt0.
  have hxj : d / 2 < x j.
    have : x i - d / 2 < x j.
      by move: hdist; rewrite distrC ltr_distl => /andP[].
    apply: le_lt_trans.
    rewrite lerBrDr.
    by move: hpos; rewrite -(splitr d).
  apply: ltW.
  move: hxj.
  rewrite (splitr (d / 2)) /=.
  rewrite (_ : d / 2 / 2 = d / 4)//.
  rewrite -mulrA.
  by rewrite -invrM ?unitfE -?natrM// pnatr_eq0.
- suff : False by [].
  case: x_gt0 => a a0 ha.
  near \oo => j.
  have [haj hij] : a <= x j /\ (i <= j)%N.
    split.
    + by rewrite -(add0r a); near: j.
    + by near: j; exact: nbhs_infty_ge.
  have hdj : (cauchymod x (d / 2) <= j)%N.
    exact: leq_trans hdi hij.
  have hdist : `|x i - x j| < d / 2 by rewrite cauchymodP// divr_gt0.
  have hupper : x j < x i + d / 2.
    move: hdist.
    by rewrite distrC ltr_distl => /andP[].
  have hhalf : - d + d / 2 = - (d / 2).
    by rewrite {1}(splitr d) opprD subrK.
  have hxj_half : x j < - (d / 2).
    by rewrite (lt_le_trans hupper)// -hhalf lerD2r.
  have hxj0 : x j < 0.
    by rewrite (lt_trans hxj_half)// oppr_lt0 divr_gt0.
  have : (0 < 0 :> F).
    exact: lt_trans (lt_le_trans a0 haj) hxj0.
  by rewrite ltxx.
Unshelve. all: by end_near. Qed.

Definition inf_alg (x : alg) : F :=
  let: exist2 d _ _ := inf_alg_proof x in d.

Lemma inf_alg_gt0 x : 0 < inf_alg x.
Proof. by rewrite /inf_alg; case: inf_alg_proof. Qed.

Lemma inf_lt_alg x : 0 < x -> (inf_alg x)%:RA < x.
Proof. by rewrite /inf_alg=> x_gt0; case: inf_alg_proof=> d _ /(_ x_gt0). Qed.

Lemma approx_proof x e : {y | 0 < e -> `|x - y%:RA| < e}.
Proof.
elim/quotW: x => x.
pose i := cauchymod x (inf_alg e / 2).
exists (x i) => e_gt0.
rewrite (lt_trans _ (inf_lt_alg _)) //.
rewrite !piE norm_pi -(rwP lt_algP) /= norm_algcrealE /=.
exists (inf_alg e / 2); first by rewrite divr_gt0 ?inf_alg_gt0.
near=> j.
rewrite /= {2}[inf_alg e](splitf 2) /= lerD2r ltW// cauchymodP//.
- by rewrite divr_gt0 ?inf_alg_gt0.
- by near: j.
Unshelve. all: by end_near. Qed.

Definition approx := locked
  (fun (x : alg) (e : alg) => projT1 (approx_proof x e) : F).

Lemma approxP (x e e': alg) : 0 < e -> e <= e' -> `|x - (approx x e)%:RA| < e'.
Proof.
by unlock approx; case: approx_proof=> /= y hy /hy /lt_le_trans hy' /hy'.
Qed.

Lemma alg_archi : Num.archimedean_axiom alg.
Proof.
move=> x; move: {x}`|x| (normr_ge0 x) => x x_ge0.
pose a := approx x 1%:RA; exists (Num.bound (a + 1)).
have := @archi_boundP _ (a + 1); rewrite -ltr_to_alg rmorph_nat.
have := @approxP x _ _ ltr01 (lexx _); rewrite ltr_distl -/a => /andP [_ hxa].
rewrite -ler_to_alg rmorphD /= (le_trans _ (ltW hxa)) //.
by move=> /(_ isT) /(lt_trans _)->.
Qed.

HB.instance Definition _ := Num.NumDomain_bounded_isArchimedean.Build alg alg_archi.

(**************************************************************************)
(* At this stage, algebraics form an archimedian field.  We now build the *)
(* material to prove the intermediate value theorem.  We first prove a    *)
(* "weak version", which expresses that the extension {alg F} indeed      *)
(* contains solutions of the intermediate value probelem in F             *)
(**************************************************************************)

Notation "'Y" := 'X%:P.

Lemma weak_ivt (p : {poly F}) (a b : F) : a <= b -> p.[a] <= 0 <= p.[b] ->
  { x : alg | a%:RA <= x <= b%:RA & root (p ^ to_alg) x }.
Proof.
move=> le_ab; have [->  _|p_neq0] := eqVneq p 0.
  by exists a%:RA; rewrite ?lexx ?ler_to_alg // rmorph0 root0.
move=> /andP[pa_le0 pb_ge0]; apply/sig2W.
have hpab: p.[a] * p.[b] <= 0 by rewrite mulr_le0_ge0.
move=> {pa_le0 pb_ge0}; wlog monic_p : p hpab p_neq0 / p \is monic.
  set q := (lead_coef p) ^-1 *: p => /(_ q).
  rewrite !hornerZ mulrCA !mulrA -mulrA mulr_ge0_le0 //.
    by rewrite (@exprn_even_ge0 _ 2).
  have mq: q \is monic by rewrite monicE lead_coefZ mulVf ?lead_coef_eq0.
  rewrite monic_neq0 ?mq=> // [] [] // x hx hqx; exists x=> //.
  move: hqx; rewrite /q -mul_polyC rmorphM /= rootM map_polyC rootC.
  by rewrite fmorph_eq0 invr_eq0 lead_coef_eq0 (negPf p_neq0).
pose c := (a + b) / 2; pose r := (b - a) / 2.
have r_ge0 : 0 <= r by rewrite mulr_ge0 ?ger0E // subr_ge0.
have hab: ((c - r = a)%R * (c + r = b)%R)%type.
  rewrite -mulrDl -mulrBl opprD addrA addrK opprK.
  rewrite addrAC addrA [a + _ + _]addrAC subrr add0r.
  by rewrite !mulrDl -![_ + _](splitf 2).
have hp: p.[c - r] * p.[c + r] <= 0 by rewrite !hab.
pose x := AlgDom monic_p r_ge0 hp; exists (\pi_alg (to_algcreal x)).
  rewrite !piE; apply/andP; rewrite -!(rwP le_algP) /=.
  split;
  by do [ unlock to_algcreal=> /=; apply: (@le_crealP _ 0%N)=> /= j _;
          have := @to_algcreal_ofP p c r 0%N j r_ge0 isT;
          rewrite ler_distl /= expr0 divr1 !hab=> /andP []].
apply/rootP; rewrite horner_pi zeroE -equiv_alg horner_algcrealE /=.
by rewrite -(@to_algcrealP x); unlock to_algcreal.
Qed.

(* any sequence of algebraic can be expressed as a sequence of
polynomials in a unique algebraic *)
Lemma pet_alg_proof (s : seq alg) :
  { ap : alg * seq {poly F} |
    [forall i : 'I_(size s), (ap.2`_i ^ to_alg).[ap.1] == s`_i]
    &  size ap.2 = size s }.
Proof.
apply: sig2_eqW; elim: s; first by exists (0,[::])=> //; apply/forallP=> [] [].
move=> x s [[a sp] /forallP /= hs hsize].
have := pchar0_PET _ (root_annul_alg a) _ (root_annul_alg x).
rewrite !annul_alg_neq0 => /(_ isT isT (pchar_num _)) /= [n [[p hp] [q hq]]].
exists (x *+ n - a, q :: [seq r \Po p | r <- sp]); last first.
  by rewrite /= size_map hsize.
apply/forallP=> /=; rewrite -add1n=> i; apply/eqP.
have [k->|l->] := splitP i; first by rewrite !ord1.
rewrite add1n /= (nth_map 0) ?hsize // map_comp_poly /=.
by rewrite horner_comp hp; apply/eqP.
Qed.

(****************************************************************************)
(* Given a sequence s of algebraics (seq {alg F})                           *)
(*        pet_alg == primitive algebraic                                    *)
(*   pet_alg_poly == sequence of polynomials such that when instanciated in *)
(*                   pet_alg gives back the sequence s (cf. pet_algK)       *)
(*                                                                          *)
(* Given a polynomial p on algebraic {poly {alg F}}                         *)
(*     pet_ground == bivariate polynomial such that when the inner          *)
(*                   variable ('Y) is instanciated in pet_alg gives back    *)
(*                   the polynomial p.                                      *)
(****************************************************************************)

Definition pet_alg s : alg :=
  let: exist2 (a, _) _ _ := pet_alg_proof s in a.
Definition pet_alg_poly s : seq {poly F}:=
  let: exist2 (_, sp) _ _ := pet_alg_proof s in sp.

Lemma size_pet_alg_poly s : size (pet_alg_poly s) = size s.
Proof. by unlock pet_alg_poly; case: pet_alg_proof. Qed.

Lemma pet_algK s i :
   ((pet_alg_poly s)`_i ^ to_alg).[pet_alg s] = s`_i.
Proof.
rewrite /pet_alg /pet_alg_poly; case: pet_alg_proof.
move=> [a sp] /= /forallP hs hsize; have [lt_is|le_si] := ltnP i (size s).
  by rewrite -[i]/(val (Ordinal lt_is)); apply/eqP; apply: hs.
by rewrite !nth_default ?hsize // rmorph0 horner0.
Qed.

Definition poly_ground := locked (fun (p : {poly alg}) =>
  swapXY (Poly (pet_alg_poly p)) : {poly {poly F}}).

Lemma sizeY_poly_ground p : sizeY (poly_ground p) = size p.
Proof.
unlock poly_ground; rewrite sizeYE swapXYK; have [->|p_neq0] := eqVneq p 0.
  apply/eqP; rewrite size_poly0 eqn_leq leq0n (leq_trans (size_Poly _)) //.
  by rewrite size_pet_alg_poly size_poly0.
rewrite (@PolyK _ 0) -?nth_last ?size_pet_alg_poly //.
have /eqP := (pet_algK p (size p).-1); apply: contraL=> /eqP->.
by rewrite rmorph0 horner0 -lead_coefE eq_sym lead_coef_eq0.
Qed.

Lemma poly_ground_eq0 p : (poly_ground p == 0) = (p == 0).
Proof. by rewrite -sizeY_eq0 sizeY_poly_ground size_poly_eq0. Qed.

Lemma poly_ground0 : poly_ground 0 = 0.
Proof. by apply/eqP; rewrite poly_ground_eq0. Qed.

Lemma poly_groundK p :
  ((poly_ground p) ^ (map_poly to_alg)).[(pet_alg p)%:P] = p.
Proof.
have [->|p_neq0] := eqVneq p 0; first by rewrite poly_ground0 rmorph0 horner0.
unlock poly_ground; rewrite horner_polyC /eval /= swapXY_map swapXYK.
apply/polyP=> i /=; rewrite coef_map_id0 ?horner0 // coef_map /=.
by rewrite coef_Poly pet_algK.
Qed.

Lemma annul_from_alg_proof (p : {poly alg}) (q : {poly F}) :
  p != 0 -> q != 0 -> root (q ^ to_alg) (pet_alg p)
  -> {r | resultant (poly_ground p) (r ^ polyC) != 0
        & (r != 0) && (root (r ^ to_alg) (pet_alg p))}.
Proof.
move=> p_neq0; elim: (size q) {-2}q (leqnn (size q))=> {q} [|n ihn] q.
  by rewrite size_poly_leq0=> ->.
move=> size_q q_neq0 hq; apply/sig2_eqW.
have [|apq_neq0] :=
  eqVneq (resultant (poly_ground p) (q ^ polyC)) 0; last first.
  by exists q=> //; rewrite q_neq0.
move/eqP; rewrite resultant_eq0 ltn_neqAle eq_sym -coprimep_def.
move=> /andP[] /(Bezout_coprimepPn _ _) [].
+ by rewrite poly_ground_eq0.
+ by rewrite map_polyC_eq0.
move=> [u v] /and3P [] /andP [u_neq0 ltn_uq] v_neq0 ltn_vp hpq.
rewrite ?size_map_polyC in ltn_uq ltn_vp.
rewrite ?size_poly_gt0 in u_neq0 v_neq0.
pose a := pet_alg p.
have := erefl (size ((u * poly_ground p) ^ (map_poly to_alg)).[a%:P]).
rewrite {2}hpq !{1}rmorphM /= !{1}hornerM poly_groundK -map_poly_comp /=.
have /eq_map_poly-> : (map_poly to_alg) \o polyC =1 polyC \o to_alg.
  by move=> r /=; rewrite map_polyC.
rewrite map_poly_comp horner_map (rootP hq) mulr0 size_poly0.
move/eqP; rewrite size_poly_eq0 mulf_eq0 (negPf p_neq0) orbF.
pose u' : {poly F} := lead_coef (swapXY u).
have [/rootP u'a_eq0|u'a_neq0] := eqVneq (u' ^ to_alg).[a] 0; last first.
  rewrite horner_polyC -lead_coef_eq0 lead_coef_map_eq /=.
    by rewrite swapXY_map /= lead_coef_map_eq /= ?map_poly_eq0 ?lead_coef_eq0
      ?swapXY_eq0.
  by rewrite swapXY_map /= lead_coef_map_eq /= ?map_poly_eq0 ?lead_coef_eq0
    ?swapXY_eq0 ?(negPf u'a_neq0).
have u'_neq0 : u' != 0 by rewrite lead_coef_eq0 swapXY_eq0.
have size_u' : (size u' < size q)%N.
  by rewrite /u' (leq_ltn_trans (max_size_lead_coefXY _)) // sizeYE swapXYK.
move: u'a_eq0=> /ihn [] //; first by rewrite -ltnS (leq_trans size_u').
by move=> r; exists r.
Qed.

Definition annul_pet_alg (p : {poly alg}) : {poly F} :=
    if (p != 0) =P true is ReflectT p_neq0 then
      let: exist2 r _ _ :=
        annul_from_alg_proof p_neq0 (annul_alg_neq0 _) (root_annul_alg _) in r
      else 0.

Lemma root_annul_pet_alg p : root (annul_pet_alg p ^ to_alg) (pet_alg p).
Proof.
rewrite /annul_pet_alg; case: eqP=> /=; last by rewrite ?rmorph0 ?root0.
by move=> p_neq0; case: annul_from_alg_proof=> ? ? /andP[].
Qed.

Definition annul_from_alg p :=
  if (size (poly_ground p) == 1)%N then lead_coef (poly_ground p)
    else resultant (poly_ground p) (annul_pet_alg p ^ polyC).

Lemma annul_from_alg_neq0 p : p != 0 -> annul_from_alg p != 0.
Proof.
move=> p_neq0; rewrite /annul_from_alg.
case: ifP; first by rewrite lead_coef_eq0 poly_ground_eq0.
rewrite /annul_pet_alg; case: eqP p_neq0=> //= p_neq0 _.
by case: annul_from_alg_proof.
Qed.

Lemma annul_pet_alg_neq0 p : p != 0 -> annul_pet_alg p != 0.
Proof.
rewrite /annul_pet_alg; case: eqP=> /=; last by rewrite ?rmorph0 ?root0.
by move=> p_neq0; case: annul_from_alg_proof=> ? ? /andP[].
Qed.

End RealAlg.

Notation to_alg F := (@to_alg_def _ (Phant F)).
Notation "x %:RA" := (to_alg _ x)
  (at level 1, left associativity, format "x %:RA").

Lemma upper_nthrootVP (F : archiRealFieldType) (x : F) (i : nat) :
   0 < x -> (Num.bound (x ^-1) <= i)%N -> 2 ^- i < x.
Proof.
move=> x_gt0 hx; rewrite -ltf_pV2 -?topredE //= ?gtr0E //.
by rewrite invrK upper_nthrootP.
Qed.

Notation "{ 'alg'  F }" := (alg F).

Section AlgAlg.

Variable F : archiRealFieldType.

Local Open Scope ring_scope.

Local Notation "p ^ f" := (map_poly f p) : ring_scope.
Local Notation "'Y" := 'X%:P.
Local Notation m0 := (fun _ => 0%N).

Definition approx2 (x : {alg {alg F}}) i :=
  approx (approx x (2 ^- i)) (2 ^- i).

Lemma asympt_approx2 x :
  {asympt e : i / `|(approx2 x i)%:RA%:RA - x| < e}.
Proof.
move=> e e_gt0; near=> i.
rewrite distrC /approx2 (@split_dist_add _ (approx x (2 ^- i))%:RA) //.
- rewrite approxP ?gtr0E // ltW //.
  rewrite upper_nthrootVP ?divrn_gt0 ?ltr_to_alg//.
  by near: i.
- rewrite (lt_trans _ (inf_lt_alg _)) ?divrn_gt0 //.
  rewrite -rmorphB -normr_to_alg ltr_to_alg approxP ?gtr0E // ltW //.
  rewrite upper_nthrootVP ?divrn_gt0 ?inf_alg_gt0 ?ltr_to_alg //.
  by near: i.
Unshelve. all: by end_near. Qed.

Lemma asympt_approx2_sig x : {m : {alg {alg F}} -> nat |
  forall e i, 0 < e -> (m e <= i)%N -> `|(approx2 x i)%:RA%:RA - x| < e}.
Proof.
exists (fun e => maxn (Num.bound (e / 2)^-1) (Num.bound (inf_alg (e / 2))^-1)).
move=> e i e_gt0.
rewrite geq_max => /andP[hi1 hi2].
rewrite distrC /approx2.
rewrite (@split_dist_add _ (approx x (2 ^- i))%:RA)//.
- rewrite approxP ?gtr0E// ltW//.
  by rewrite upper_nthrootVP ?divrn_gt0 ?ltr_to_alg.
- rewrite (lt_trans _ (inf_lt_alg _)) ?divrn_gt0 //.
  rewrite -rmorphB -normr_to_alg ltr_to_alg approxP ?gtr0E // ltW //.
  by rewrite upper_nthrootVP ?divrn_gt0 ?inf_alg_gt0 ?ltr_to_alg.
Qed.

Lemma from_alg_crealP (x : {alg {alg F}}) : creal_axiom_sig (approx2 x).
Proof.
have [m hm] := asympt_approx2_sig x.
exists (fun e => m (e%:RA%:RA / 2)).
move=> e i j e_gt0 hi hj.
rewrite -2!ltr_to_alg !normr_to_alg !rmorphB /=.
rewrite (@split_dist_add _ x) // ?[`|_ - _%:RA|]distrC.
- by rewrite hm// divr_gt0// !ltr_to_alg.
- by rewrite hm// divr_gt0// !ltr_to_alg.
Qed.

Definition from_alg_creal := locked (fun x => CReal (from_alg_crealP x)).

Lemma to_alg_crealP (x : creal F) : creal_axiom_sig (fun i => to_alg F (x i)).
Proof.
exists (fun e => cauchymod x (inf_alg e)).
move=> e i j e_gt0 hi hj.
rewrite -rmorphB -normr_to_alg (lt_trans _ (inf_lt_alg _)) //.
by rewrite ltr_to_alg cauchymodP ?inf_alg_gt0.
Qed.
Definition to_alg_creal x := CReal (to_alg_crealP x).

Lemma horner_to_alg_creal p x :
  ((p ^ to_alg F).[to_alg_creal x] == to_alg_creal p.[x])%CR.
Proof.
by apply: eq_crealP => e e0; near=> i; rewrite /= horner_map subrr normr0.
Unshelve. all: by end_near. Qed.

Lemma neq_to_alg_creal x y :
  (to_alg_creal x != to_alg_creal y)%CR <-> (x != y)%CR.
Proof.
split=> [[/= d d0 hd]|[d d0 hd]].
- exists (inf_alg d); first by rewrite inf_alg_gt0.
  apply: filterS hd => i /=.
  rewrite -rmorphB -normr_to_alg => hdi.
  by rewrite -ler_to_alg (le_trans _ hdi)// ltW// inf_lt_alg.
- exists d%:RA; first by rewrite ltr_to_alg.
  apply: filterS hd => i /= hdi.
  by rewrite -rmorphB -normr_to_alg ler_to_alg.
Qed.

Lemma eq_to_alg_creal x y :
  (to_alg_creal x == to_alg_creal y)%CR -> (x == y)%CR.
Proof. by move=> hxy /neq_to_alg_creal. Qed.

Lemma to_alg_creal0 : (to_alg_creal 0 == 0)%CR.
Proof.
by apply: eq_crealP => e e0; near=> i; rewrite /= subrr normr0.
Unshelve. all: by end_near. Qed.

Local Notation "R ==> R'" := (Morphisms.respectful R R')
  (right associativity, at level 55) : signature_scope.

Add Morphism to_alg_creal
 with signature (@eq_creal _) ==> (@eq_creal _) as to_alg_creal_morph.
Proof. by move=> x y hxy /neq_to_alg_creal. Qed.
Global Existing Instance to_alg_creal_morph_Proper.

Lemma to_alg_creal_repr (x : {alg F}) :
  (to_alg_creal (repr x) == x%:CR)%CR.
Proof.
apply: eq_crealP => e e_gt0; near=> i.
have hi : (cauchymod (repr x) (inf_alg e) <= i)%N by near: i.
rewrite (le_lt_trans _ (inf_lt_alg _)) //.
rewrite -{2}[x]reprK !piE norm_pi.
rewrite -(rwP (le_algP _ _)) norm_algcrealE /=.
apply: (@le_crealP _ (cauchymod (repr x) (inf_alg e))) => k hk /=.
by rewrite ltW// cauchymodP// inf_alg_gt0.
Unshelve. all: by end_near. Qed.

Local Open Scope quotient_scope.

Lemma cst_pi (x : algcreal F) : ((\pi_{alg F} x)%:CR == to_alg_creal x)%CR.
Proof.
apply: eq_crealP => e e_gt0; near=> i.
rewrite (lt_trans _ (inf_lt_alg _))//.
rewrite !piE norm_pi /= -(rwP (lt_algP _ _)) norm_algcrealE /=.
exists (inf_alg e / 2); first by rewrite divrn_gt0 ?inf_alg_gt0.
near=> j.
rewrite /= [leRHS]splitr lerD2r ltW// distrC// cauchymodP//.
- by rewrite divrn_gt0 ?inf_alg_gt0.
- by near: i.
- by near: j.
Unshelve. all: by end_near. Qed.

End AlgAlg.

Section AlgAlgAlg.

Variable F : archiRealFieldType.

Local Open Scope ring_scope.

Local Notation "p ^ f" := (map_poly f p) : ring_scope.
Local Notation "'Y" := 'X%:P.

Lemma from_alg_crealK (x : {alg {alg F}}) :
  (to_alg_creal (to_alg_creal (from_alg_creal x)) == x%:CR)%CR.
Proof.
apply: eq_crealP.
unlock from_alg_creal => /=.
exact: asympt_approx2.
Qed.

Lemma root_annul_from_alg_creal (x : {alg {alg F}}) :
  ((annul_from_alg (annul_alg x)).[from_alg_creal x] == 0)%CR.
Proof.
do 2!apply: eq_to_alg_creal.
rewrite -!horner_to_alg_creal from_alg_crealK !to_alg_creal0.
rewrite horner_creal_cst; apply/eq_creal_cst; rewrite -rootE.
rewrite /annul_from_alg; have [/size_poly1P [c c_neq0 hc]|sp_neq1] := boolP (_ == _).
  set p := _ ^ _; suff ->: p = (annul_alg x) ^ to_alg _ by apply: root_annul_alg.
  congr (_ ^ _); rewrite -{2}[annul_alg x]poly_groundK /=.
  by rewrite !hc lead_coefC map_polyC /= hornerC.
have [||[u v] /= [hu hv] hpq] := @resultant_in_ideal _
  (poly_ground (annul_alg x)) (annul_pet_alg (annul_alg x) ^ polyC).
+ rewrite ltn_neqAle eq_sym sp_neq1 //= lt0n size_poly_eq0.
  by rewrite poly_ground_eq0 annul_alg_neq0.
+ rewrite size_map_polyC -(size_map_poly (to_alg _)) /=.
  rewrite (root_size_gt1 _ (root_annul_pet_alg _)) //.
  by rewrite map_poly_eq0 annul_pet_alg_neq0 ?annul_alg_neq0.
move: hpq=> /(f_equal (map_poly (map_poly (to_alg _)))).
rewrite map_polyC /= => /(f_equal (eval (pet_alg (annul_alg x))%:P)).
rewrite {1}/eval hornerC !rmorphD !{1}rmorphM /= /eval /= => ->.
rewrite -map_poly_comp /=.
have /eq_map_poly->: (map_poly (@to_alg F)) \o polyC =1 polyC \o (@to_alg F).
  by move=> r /=; rewrite map_polyC.
rewrite map_poly_comp horner_map /= (rootP (root_annul_pet_alg _)) mulr0 addr0.
by rewrite rmorphM /= rootM orbC poly_groundK root_annul_alg.
Qed.

Lemma annul_alg_from_alg_creal_neq0 (x : {alg {alg F}}) :
  annul_from_alg (annul_alg x) != 0.
Proof. by rewrite annul_from_alg_neq0 ?annul_alg_neq0. Qed.

Definition from_alg_algcreal x :=
  AlgCRealOf (@annul_alg_from_alg_creal_neq0 x) (@root_annul_from_alg_creal x).

Definition from_alg : {alg {alg F}} -> {alg F} :=
  locked (\pi%qT \o from_alg_algcreal).

Lemma from_algK : cancel from_alg (to_alg _).
Proof.
move=> x; unlock from_alg; rewrite -{2}[x]reprK piE -equiv_alg /= cst_pi.
by apply: eq_to_alg_creal; rewrite from_alg_crealK to_alg_creal_repr.
Qed.

Lemma ivt (p : {poly (alg F)}) (a b : alg F) : a <= b ->
  p.[a] <= 0 <= p.[b] -> exists2 x : alg F, a <= x <= b & root p x.
Proof.
move=> le_ab hp; have [x /andP [hax hxb]] := @weak_ivt _ _ _ _ le_ab hp.
rewrite -[x]from_algK fmorph_root=> rpx; exists (from_alg x)=> //.
by rewrite -ler_to_alg from_algK hax -ler_to_alg from_algK.
Qed.

HB.instance Definition _ := Num.RealField_isClosed.Build (alg F) ivt.

End AlgAlgAlg.
End RealAlg.
HB.export RealAlg.

Notation "{ 'realclosure'  F }" := (RealAlg.alg F).

Notation annul_realalg := RealAlg.annul_alg.
Notation realalg_of F := (@RealAlg.to_alg_def _ (Phant F)).
Notation "x %:RA" := (realalg_of x)
  (at level 1, left associativity, format "x %:RA").

Section RealClosureTheory.

Variable F : archiRealFieldType.
Notation R := {realclosure F}.

Local Notation "p ^ f" := (map_poly f p) : ring_scope.

Lemma root_annul_realalg (x : R) : root ((annul_realalg x) ^ realalg_of _) x.
Proof. exact: RealAlg.root_annul_alg. Qed.
Hint Resolve root_annul_realalg : core.

Lemma monic_annul_realalg (x : R) : annul_realalg x \is monic.
Proof. exact: RealAlg.monic_annul_alg. Qed.
Hint Resolve monic_annul_realalg : core.

Lemma annul_realalg_neq0 (x : R) : annul_realalg x != 0%R.
Proof. exact: RealAlg.annul_alg_neq0. Qed.
Hint Resolve annul_realalg_neq0 : core.

Lemma realalg_algebraic : integralRange (realalg_of F).
Proof. by move=> x; exists (annul_realalg x). Qed.

End RealClosureTheory.

Definition realalg := {realclosure rat}.
HB.instance Definition _ := Num.RealClosedField.on realalg.

Module RatRealAlg.
HB.instance Definition _ := Countable.copy (RealAlg.algdom rat)
  (pcan_type (@RealAlg.encode_algdomK rat)).
#[export] HB.instance Definition _ := Countable.on realalg.
End RatRealAlg.
HB.export RatRealAlg.

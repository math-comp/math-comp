(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype.
From mathcomp
Require Import bigop ssralg ssrnum ssrint rat poly polydiv polyorder.
From mathcomp
Require Import perm matrix mxpoly polyXY binomial generic_quotient.
From mathcomp
Require Import cauchyreals separable zmodp bigenough.

(*************************************************************************)
(* This files constructs the real closure of an archimedian field in the *)
(* way described in Cyril Cohen. Construction of real algebraic numbers  *)
(* in Coq. In Lennart Beringer and Amy Felty, editors, ITP - 3rd         *)
(* International Conference on Interactive Theorem Proving - 2012,       *)
(* Princeton, United States, August 2012. Springer                       *)
(*                                                                       *)
(* The only definition one may want to use in this file is the operator  *)
(* {realclosure R} which constructs the real closure of the archimedian  *)
(* field R (for which rat is a prefect candidate)                        *)
(*************************************************************************)

Import GRing.Theory Num.Theory BigEnough.

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
+ by rewrite rmorph0.
+ by move=> u u' v v' /=; rewrite rmorphD /= => -> ->.
move=> /= i _; rewrite -mul_polyC rmorphM /= map_polyC mul_polyC.
by rewrite coef_map rmorphX.
Qed.

End extras.

Module RealAlg.

Local Open Scope ring_scope.
Local Notation eval := horner_eval.

Section RealAlg.

Variable F : archiFieldType.
Local Notation m0 := (fun _ => 0%N).

(*********************************************************************)
(* Construction of algebraic Cauchy reals : Cauchy real + polynomial *)
(*********************************************************************)

CoInductive algcreal := AlgCReal {
  creal_of_alg :> creal F;
  annul_creal : {poly F};
  _ : annul_creal \is monic;
  _ : (annul_creal.[creal_of_alg] == 0)%CR
}.

Lemma monic_annul_creal x : annul_creal x \is monic.
Proof. by case: x. Qed.
Hint Resolve monic_annul_creal.

Lemma annul_creal_eq0 x : (annul_creal x == 0) = false.
Proof. by rewrite (negPf (monic_neq0 _)). Qed.

Lemma root_annul_creal x : ((annul_creal x).[x] == 0)%CR.
Proof. by case: x. Qed.
Hint Resolve root_annul_creal.

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
  AlgCReal (monic_monic_from_neq0 p_neq0) (root_monic_from_neq0 px_eq0).

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
apply: is_root_annul_creal; apply: eq_crealP.
by exists m0=> * /=; rewrite opprK subrr normr0.
Qed.

Definition add_algcreal (x y : algcreal) : algcreal :=
  AlgCReal (@monic_annul_creal _) (@root_add_algcreal x y).

Lemma div_annihilant_algcreal_neq0 (x y : algcreal) :
   (annul_creal y).[0] != 0 ->
   div_annihilant (annul_creal x) (annul_creal y) != 0.
Proof. by move=> ?; rewrite div_annihilant_neq0 ?monic_neq0. Qed.

Hint Resolve eq_creal_refl.
Hint Resolve le_creal_refl.

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
pose p := annul_creal x; move: {2}(size _)%N (leqnn (size p))=> n.
elim: n x @p => [x p|n ihn x p le_sp_Sn].
  by rewrite leqn0 size_poly_eq0 /p  annul_creal_eq0.
move: le_sp_Sn; rewrite leq_eqVlt; have [|//|eq_sp_Sn _] := ltngtP.
  by rewrite ltnS=> /ihn ihnp _; apply: ihnp.
have px0 : (p.[x] == 0)%CR by apply: root_annul_creal.
have [cpX|ncpX] := boolP (coprimep p 'X).
  by right; move: (cpX)=> /coprimep_root /(_ px0); rewrite horner_crealX.
have [eq_pX|] := altP (p =P 'X).
  by left; move: px0; rewrite eq_pX horner_crealX.
rewrite -eqp_monic /p ?monicX // negb_and orbC.
have:= ncpX; rewrite coprimepX -dvdp_XsubCl subr0 => /negPf-> /= ndiv_pX.
have [r] := smaller_factor (monic_annul_creal _) px0 ndiv_pX ncpX.
rewrite eq_sp_Sn ltnS => /andP[le_r_n monic_r] rx_eq0.
exact: (ihn (AlgCReal monic_r rx_eq0)).
Qed.

Lemma eq_algcreal_dec (x y : algcreal) : {(x == y)%CR} + {(x != y)%CR}.
Proof.
have /= [d_eq0|d_neq0] := algcreal_eq0_dec (sub_algcreal x y); [left|right].
  apply: eq_crealP; exists_big_modulus m F.
    by move=> e i e_gt0 hi; rewrite (@eq0_modP _ _ d_eq0).
  by close.
pose_big_enough i.
  apply: (@neq_crealP _ (lbound d_neq0) i i); do ?by rewrite ?lbound_gt0.
  by rewrite (@lbound0P _ _ d_neq0).
by close.
Qed.

Definition eq_algcreal : rel algcreal := eq_algcreal_dec.

Lemma eq_algcrealP (x y : algcreal) : reflect (x == y)%CR (eq_algcreal x y).
Proof. by rewrite /eq_algcreal; case: eq_algcreal_dec=> /=; constructor. Qed.
Arguments eq_algcrealP [x y].

Lemma neq_algcrealP (x y : algcreal) : reflect (x != y)%CR (~~ eq_algcreal x y).
Proof. by rewrite /eq_algcreal; case: eq_algcreal_dec=> /=; constructor. Qed.
Arguments neq_algcrealP [x y].
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
rewrite /div_algcreal; case: eq_algcreal_dec=> [/(_ x_neq0)|x_neq0'] //=.
case: simplify_algcreal=> x' px'0_neq0 [x'_neq0 eq_xx'].
apply: is_root_annul_creal; rewrite /= -(@eq_creal_inv _ _ _ x_neq0) //.
by apply: eq_crealP; exists m0=> * /=; rewrite div1r subrr normr0.
Qed.

Definition inv_algcreal (x : algcreal) :=
  match eq_algcreal_dec x (cst_algcreal 0) with
    | left x_eq0 => cst_algcreal 0
    | right x_neq0 =>
      AlgCReal (@monic_annul_creal _) (@root_inv_algcreal _ x_neq0)
  end.

Lemma div_creal_creal (y : creal F) (y_neq0 : (y != 0)%CR) :
  (y / y_neq0 == 1%:CR)%CR.
Proof.
apply: eq_crealP; exists_big_modulus m F.
  move=> e i e_gt0 hi; rewrite /= divff ?subrr ?normr0 //.
  by rewrite (@creal_neq_always _ _ 0%CR).
by close.
Qed.

Lemma root_mul_algcreal (x y : algcreal) :
  ((annul_creal (div_algcreal x (inv_algcreal y))).[x * y] == 0)%CR.
Proof.
rewrite /div_algcreal /inv_algcreal.
case: (eq_algcreal_dec y)=> [->|y_neq0]; apply: is_root_annul_creal.
  rewrite mul_creal0; case: eq_algcreal_dec=> // neq_00.
  by move: (eq_creal_refl neq_00).
case: eq_algcreal_dec=> /= [yV_eq0|yV_neq0].
  have: (y * y_neq0^-1 == 0)%CR by rewrite yV_eq0 mul_creal0.
  by rewrite div_creal_creal=> /eq_creal_cst; rewrite oner_eq0.
case: simplify_algcreal=> y' py'0_neq0 [y'_neq0 /= eq_yy'].
rewrite -(@eq_creal_inv _ _ _ yV_neq0) //.
by apply: eq_crealP; exists m0=> * /=; rewrite invrK subrr normr0.
Qed.

Definition mul_algcreal (x y : algcreal) :=
  AlgCReal (@monic_annul_creal _) (@root_mul_algcreal x y).

Lemma le_creal_neqVlt (x y : algcreal) : (x <= y)%CR -> {(x == y)%CR} + {(x < y)%CR}.
Proof.
case: (eq_algcreal_dec x y); first by left.
by move=> /neq_creal_ltVgt [|h /(_ h) //]; right.
Qed.

Lemma ltVge_algcreal_dec (x y : algcreal) : {(x < y)%CR} + {(y <= x)%CR}.
Proof.
have [eq_xy|/neq_creal_ltVgt [lt_xy|lt_yx]] := eq_algcreal_dec x y;
by [right; rewrite eq_xy | left | right; apply: lt_crealW].
Qed.

Definition lt_algcreal : rel algcreal := ltVge_algcreal_dec.
Definition le_algcreal : rel algcreal := fun x y => ~~ ltVge_algcreal_dec y x.

Lemma lt_algcrealP (x y : algcreal) : reflect (x < y)%CR (lt_algcreal x y).
Proof. by rewrite /lt_algcreal; case: ltVge_algcreal_dec; constructor. Qed.
Arguments lt_algcrealP [x y].

Lemma le_algcrealP (x y : algcreal) : reflect (x <= y)%CR (le_algcreal x y).
Proof. by rewrite /le_algcreal; case: ltVge_algcreal_dec; constructor. Qed.
Arguments le_algcrealP [x y].
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

Lemma norm_algcrealE (x : algcreal) : (norm_algcreal x == `| x |)%CR.
Proof.
rewrite /norm_algcreal /le_algcreal; case: ltVge_algcreal_dec => /=.
  move=> x_lt0; apply: eq_crealP; exists_big_modulus m F.
    move=> e i e_gt0 hi /=; rewrite [`|x i|]ler0_norm ?subrr ?normr0 //.
    by rewrite ltrW // [_ < 0%CR i]creal_lt_always.
  by close.
move=> /(@le_creal_neqVlt zero_algcreal) /= [].
  by move<-; apply: eq_crealP; exists m0=> * /=; rewrite !(normr0, subrr).
move=> x_gt0; apply: eq_crealP; exists_big_modulus m F.
  move=> e i e_gt0 hi /=; rewrite [`|x i|]ger0_norm ?subrr ?normr0 //.
  by rewrite ltrW // creal_gt0_always.
by close.
Qed.

(**********************************************************************)
(* Theory of the "domain" of algebraic numbers: polynomial + interval *)
(**********************************************************************)
CoInductive algdom := AlgDom {
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
Hint Resolve monic_annul_algdom.

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

Definition algdom_EqMixin := PcanEqMixin encode_algdomK.
Canonical algdom_eqType := EqType algdom algdom_EqMixin.

Definition algdom_ChoiceMixin := PcanChoiceMixin encode_algdomK.
Canonical algdom_choiceType := ChoiceType algdom algdom_ChoiceMixin.

Fixpoint to_algcreal_of (p : {poly F}) (c r : F) (i : nat) : F :=
  match i with
    | 0 => c
    | i.+1 =>
      let c' := to_algcreal_of p c r i in
        if p.[c' - r / 2%:R ^+ i] * p.[c'] <= 0
          then c' - r / 2%:R ^+ i.+1
          else c' + r / 2%:R ^+ i.+1
  end.


Lemma to_algcreal_of_recP p c r i : 0 <= r ->
  `|to_algcreal_of p c r i.+1 - to_algcreal_of p c r i| <= r * 2%:R ^- i.+1.
Proof.
move=> r_ge0 /=; case: ifP=> _; rewrite addrAC subrr add0r ?normrN ger0_norm //;
by rewrite mulr_ge0 ?invr_ge0 ?exprn_ge0 ?ler0n.
Qed.

Lemma to_algcreal_ofP p c r i j : 0 <= r -> (i <= j)%N ->
  `|to_algcreal_of p c r j - to_algcreal_of p c r i| <= r * 2%:R ^- i.
Proof.
move=> r_ge0 leij; pose r' := r * 2%:R ^- j * (2%:R ^+ (j - i) - 1).
rewrite (@ler_trans _ r') //; last first.
  rewrite /r' -mulrA ler_wpmul2l // ler_pdivr_mull ?exprn_gt0 ?ltr0n //.
  rewrite -{2}(subnK leij) exprD mulfK ?gtr_eqF ?exprn_gt0 ?ltr0n //.
  by rewrite ger_addl lerN10.
rewrite /r' subrX1 addrK mul1r -{1 2}(subnK leij); set f := _  c r.
elim: (_ - _)%N=> [|k ihk]; first by rewrite subrr normr0 big_ord0 mulr0 lerr.
rewrite addSn big_ord_recl /= mulrDr.
rewrite (ler_trans (ler_dist_add (f (k + i)%N) _ _)) //.
rewrite ler_add ?expr0 ?mulr1 ?to_algcreal_of_recP // (ler_trans ihk) //.
rewrite exprSr invfM -!mulrA !ler_wpmul2l ?invr_ge0 ?exprn_ge0 ?ler0n //.
by rewrite mulr_sumr ler_sum // => l _ /=; rewrite exprS mulKf ?pnatr_eq0.
Qed.

Lemma alg_to_crealP (x : algdom) :
  creal_axiom (to_algcreal_of (annul_algdom x) (center_alg x) (radius_alg x)).
Proof.
pose_big_modulus m F.
  exists m=> e i j e_gt0 hi hj.
  wlog leij : i j {hi} hj / (j <= i)%N.
    move=> hwlog; case/orP: (leq_total i j)=> /hwlog; last exact.
    by rewrite distrC; apply.
  rewrite (ler_lt_trans (to_algcreal_ofP _ _ _ _)) ?radius_alg_ge0 //.
  rewrite ltr_pdivr_mulr ?gtr0E // -ltr_pdivr_mull //.
  by rewrite upper_nthrootP.
by close.
Qed.

Definition alg_to_creal x := CReal (alg_to_crealP x).

Lemma exp2k_crealP : @creal_axiom F (fun i => 2%:R ^- i).
Proof.
pose_big_modulus m F.
  exists m=> e i j e_gt0 hi hj.
  wlog leij : i j {hj} hi / (i <= j)%N.
    move=> hwlog; case/orP: (leq_total i j)=> /hwlog; first exact.
    by rewrite distrC; apply.
  rewrite ger0_norm ?subr_ge0; last first.
    by rewrite ?lef_pinv -?topredE /= ?gtr0E // ler_eexpn2l ?ltr1n.
  rewrite -(@ltr_pmul2l _ (2%:R ^+ i )) ?gtr0E //.
  rewrite mulrBr mulfV ?gtr_eqF ?gtr0E //.
  rewrite (@ler_lt_trans _ 1) // ?ger_addl ?oppr_le0 ?mulr_ge0 ?ger0E //.
  by rewrite -ltr_pdivr_mulr // mul1r upper_nthrootP.
by close.
Qed.
Definition exp2k_creal := CReal exp2k_crealP.

Lemma exp2k_creal_eq0 : (exp2k_creal == 0)%CR.
Proof.
apply: eq_crealP; exists_big_modulus m F.
  move=> e i e_gt0 hi /=.
  rewrite subr0 gtr0_norm ?gtr0E // -ltf_pinv -?topredE /= ?gtr0E //.
  by rewrite invrK upper_nthrootP.
by close.
Qed.

Notation lbound0_of p := (@lbound0P _ _ p _ _ _).

Lemma to_algcrealP (x : algdom) : ((annul_algdom x).[alg_to_creal x] == 0)%CR.
Proof.
set u := alg_to_creal _; set p := annul_algdom _.
pose r := radius_alg x; pose cr := cst_creal r.
have: ((p).[u - cr * exp2k_creal] *  (p).[u + cr * exp2k_creal] <= 0)%CR.
  apply: (@le_crealP _ 0%N)=> i _ /=.
  rewrite -/p -/r; set c := center_alg _.
  elim: i=> /= [|i].
    by rewrite !expr0 divr1 algdomP.
  set c' := to_algcreal_of _ _ _=> ihi.
  have [] := lerP (_ * p.[c' i]).
    rewrite addrNK -addrA -opprD -mulr2n -[_ / _ *+ _]mulr_natr.
    by rewrite -mulrA exprSr invfM mulfVK ?pnatr_eq0.
  rewrite addrK -addrA -mulr2n -[_ / _ *+ _]mulr_natr.
  rewrite -mulrA exprSr invfM mulfVK ?pnatr_eq0 // => /ler_pmul2l<-.
  rewrite mulr0 mulrCA !mulrA [X in X * _]mulrAC -mulrA.
  by rewrite mulr_ge0_le0 // -expr2 exprn_even_ge0.
rewrite exp2k_creal_eq0 mul_creal0 opp_creal0 add_creal0.
move=> hu pu0; apply: hu; pose e := (lbound pu0).
pose_big_enough i.
  apply: (@lt_crealP _ (e * e) i i) => //.
    by rewrite !pmulr_rgt0 ?invr_gt0 ?ltr0n ?lbound_gt0.
  rewrite add0r [u]lock /= -!expr2.
  rewrite -[_.[_] ^+ _]ger0_norm ?exprn_even_ge0 // normrX.
  rewrite ler_pexpn2r -?topredE /= ?lbound_ge0 ?normr_ge0 //.
  by rewrite -lock (ler_trans _ (lbound0_of pu0)).
by close.
Qed.

Definition to_algcreal_rec (x : algdom) :=
  AlgCReal (monic_annul_algdom x) (@to_algcrealP x).
(* "Encoding" function from algdom to algcreal *)
Definition to_algcreal := locked to_algcreal_rec.

(* "Decoding" function, constructed interactively *)
Lemma to_algdom_exists (x : algcreal) :
  { y : algdom | (to_algcreal y == x)%CR }.
Proof.
pose p := annul_creal x.
move: {2}(size p) (leqnn (size p))=> n.
elim: n x @p=> [x p|n ihn x p le_sp_Sn].
  by rewrite leqn0 size_poly_eq0 /p annul_creal_eq0.
move: le_sp_Sn; rewrite leq_eqVlt.
have [|//|eq_sp_Sn _] := ltngtP.
  by rewrite ltnS=> /ihn ihnp _; apply: ihnp.
have px0 := @root_annul_creal x; rewrite -/p -/root in px0.
have [|ncop] := boolP (coprimep p p^`()).
  move/coprimep_root => /(_ _ px0) /deriv_neq0_mono [r r_gt0 [i ir sm]].
  have p_chg_sign : p.[x i - r] * p.[x i + r] <= 0.
    have [/accr_pos_incr hp|/accr_neg_decr hp] := sm.
      have hpxj : forall j, (i <= j)%N ->
        (p.[x i - r] <= p.[x j]) * (p.[x j] <= p.[x i + r]).
        move=> j hj.
          suff:  p.[x i - r] <= p.[x j] <= p.[x i + r] by case/andP=> -> ->.
        rewrite !hp 1?addrAC ?subrr ?add0r ?normrN;
        rewrite ?(gtr0_norm r_gt0) //;
          do ?by rewrite ltrW ?cauchymodP ?(leq_trans _ hj).
        by rewrite -ler_distl ltrW ?cauchymodP ?(leq_trans _ hj).
      rewrite mulr_le0_ge0 //; apply/le_creal_cst; rewrite -px0;
      by apply: (@le_crealP _ i)=> h hj /=; rewrite hpxj.
    have hpxj : forall j, (i <= j)%N ->
      (p.[x i + r] <= p.[x j]) * (p.[x j] <= p.[x i - r]).
      move=> j hj.
        suff:  p.[x i + r] <= p.[x j] <= p.[x i - r] by case/andP=> -> ->.
      rewrite !hp 1?addrAC ?subrr ?add0r ?normrN;
      rewrite ?(gtr0_norm r_gt0) //;
        do ?by rewrite ltrW ?cauchymodP ?(leq_trans _ hj).
      by rewrite andbC -ler_distl ltrW ?cauchymodP ?(leq_trans _ hj).
    rewrite mulr_ge0_le0 //; apply/le_creal_cst; rewrite -px0;
    by apply: (@le_crealP _ i)=> h hj /=; rewrite hpxj.
  pose y := (AlgDom (monic_annul_creal x) (ltrW r_gt0) p_chg_sign).
  have eq_py_px: (p.[to_algcreal y] == p.[x])%CR.
    rewrite /to_algcreal -lock.
    by have := @to_algcrealP y; rewrite /= -/p=> ->; apply: eq_creal_sym.
  exists y.
  move: sm=> /strong_mono_bound [k k_gt0 hk].
  rewrite -/p; apply: eq_crealP.
  exists_big_modulus m F.
    move=> e j e_gt0 hj; rewrite (ler_lt_trans (hk _ _ _ _)) //.
    + rewrite /to_algcreal -lock.
      rewrite (ler_trans (to_algcreal_ofP _ _ _ (leq0n _))) ?(ltrW r_gt0) //.
      by rewrite expr0 divr1.
    + by rewrite ltrW // cauchymodP.
    rewrite -ltr_pdivl_mull //.
    by rewrite (@eq_modP _ _ _ eq_py_px) // ?pmulr_rgt0 ?invr_gt0.
  by close.
case: (@smaller_factor _ p p^`() x); rewrite ?monic_annul_creal //.
  rewrite gtNdvdp // -?size_poly_eq0 size_deriv eq_sp_Sn //=.
  apply: contra ncop=> /eqP n_eq0; move: eq_sp_Sn; rewrite n_eq0.
  by move=> /eqP /size_poly1P [c c_neq0 ->]; rewrite derivC coprimep0 polyC_eqp1.
move=> r /andP [hsr monic_r rx_eq0].
apply: (ihn (AlgCReal monic_r rx_eq0))=> /=.
by rewrite -ltnS -eq_sp_Sn.
Qed.

Definition to_algdom x := projT1 (to_algdom_exists x).

Lemma to_algdomK x : (to_algcreal (to_algdom x) == x)%CR.
Proof. by rewrite /to_algdom; case: to_algdom_exists. Qed.

Lemma eq_algcreal_to_algdom x : eq_algcreal (to_algcreal (to_algdom x)) x.
Proof. by apply/eq_algcrealP; apply: to_algdomK. Qed.

(* Explicit encoding to a choice type *)
Canonical eq_algcreal_encModRel := EncModRel eq_algcreal eq_algcreal_to_algdom.

Local Open Scope quotient_scope.

(***************************************************************************)
(* Algebraic numbers are the quotient of algcreal by their setoid equality *)
(***************************************************************************)
Definition alg := {eq_quot eq_algcreal}.

Definition alg_of of (phant F) := alg.
Identity Coercion type_alg_of : alg_of >-> alg.

Notation "{ 'alg'  F }" := (alg_of (Phant F)).

(* A lot of structure is inherited *)
Canonical alg_eqType := [eqType of alg].
Canonical alg_choiceType := [choiceType of alg].
Canonical alg_quotType := [quotType of alg].
Canonical alg_eqQuotType := [eqQuotType eq_algcreal of alg].
Canonical alg_of_eqType := [eqType of {alg F}].
Canonical alg_of_choiceType := [choiceType of {alg F}].
Canonical alg_of_quotType := [quotType of {alg F}].
Canonical alg_of_eqQuotType := [eqQuotType eq_algcreal of {alg F}].

Definition to_alg_def (phF : phant F) : F -> {alg F} :=
  lift_embed {alg F} cst_algcreal.
Notation to_alg := (@to_alg_def (Phant F)).
Notation "x %:RA" := (to_alg x)
  (at level 2, left associativity, format "x %:RA").
Local Notation "p ^ f" := (map_poly f p) : ring_scope.

Canonical to_alg_pi_morph := PiEmbed to_alg.

Local Notation zero_alg := 0%:RA.
Local Notation one_alg := 1%:RA.

Lemma equiv_alg (x y : algcreal) : (x == y)%CR <-> (x = y %[mod {alg F}]).
Proof.
split; first by move=> /eq_algcrealP /eqquotP ->.
by move=> /eqquotP /eq_algcrealP.
Qed.

Lemma nequiv_alg (x y : algcreal) : reflect (x != y)%CR (x != y %[mod {alg F}]).
Proof. by rewrite eqquotE; apply: neq_algcrealP. Qed.
Arguments nequiv_alg [x y].
Prenex Implicits nequiv_alg.

Lemma pi_algK (x : algcreal) : (repr (\pi_{alg F} x) == x)%CR.
Proof. by apply/equiv_alg; rewrite reprK. Qed.

Definition add_alg := lift_op2 {alg F} add_algcreal.

Lemma pi_add : {morph \pi_{alg F} : x y / add_algcreal x y >-> add_alg x y}.
Proof. by unlock add_alg=> x y; rewrite -equiv_alg /= !pi_algK. Qed.

Canonical add_pi_morph := PiMorph2 pi_add.

Definition opp_alg := lift_op1 {alg F} opp_algcreal.

Lemma pi_opp : {morph \pi_{alg F} : x / opp_algcreal x >-> opp_alg x}.
Proof. by unlock opp_alg=> x; rewrite -equiv_alg /= !pi_algK. Qed.

Canonical opp_pi_morph := PiMorph1 pi_opp.

Definition mul_alg := lift_op2 {alg F} mul_algcreal.

Lemma pi_mul : {morph \pi_{alg F} : x y / mul_algcreal x y >-> mul_alg x y}.
Proof. by unlock mul_alg=> x y; rewrite -equiv_alg /= !pi_algK. Qed.

Canonical mul_pi_morph := PiMorph2 pi_mul.

Definition inv_alg := lift_op1 {alg F} inv_algcreal.

Lemma pi_inv : {morph \pi_{alg F} : x / inv_algcreal x >-> inv_alg x}.
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
elim/quotW=> x; elim/quotW=> y; elim/quotW=> z; rewrite !piE -equiv_alg.
by apply: eq_crealP; exists m0=> * /=; rewrite addrA subrr normr0.
Qed.

Lemma add_algC : commutative add_alg.
Proof.
elim/quotW=> x; elim/quotW=> y; rewrite !piE -equiv_alg /=.
by apply: eq_crealP; exists m0=> * /=; rewrite [X in _ - X]addrC subrr normr0.
Qed.

Lemma add_0alg : left_id zero_alg add_alg.
Proof. by elim/quotW=> x; rewrite !piE -equiv_alg /= add_0creal. Qed.

Lemma add_Nalg : left_inverse zero_alg opp_alg add_alg.
Proof.
elim/quotW=> x; rewrite !piE -equiv_alg /=.
by apply: eq_crealP; exists m0=> *; rewrite /= addNr subr0 normr0.
Qed.

Definition alg_zmodMixin :=  ZmodMixin add_algA add_algC add_0alg add_Nalg.
Canonical alg_zmodType := Eval hnf in ZmodType alg alg_zmodMixin.
Canonical alg_of_zmodType := Eval hnf in ZmodType {alg F} alg_zmodMixin.


Lemma add_pi x y : \pi_{alg F} x + \pi_{alg F} y
  = \pi_{alg F} (add_algcreal x y).
Proof. by rewrite [_ + _]piE. Qed.

Lemma opp_pi x : - \pi_{alg F} x  = \pi_{alg F} (opp_algcreal x).
Proof. by rewrite [- _]piE. Qed.

Lemma zeroE : 0 = \pi_{alg F} zero_algcreal.
Proof. by rewrite [0]piE. Qed.

Lemma sub_pi x y : \pi_{alg F} x - \pi_{alg F} y
  = \pi_{alg F} (add_algcreal x (opp_algcreal y)).
Proof. by rewrite [_ - _]piE. Qed.

Lemma mul_algC : commutative mul_alg.
Proof.
elim/quotW=> x; elim/quotW=> y; rewrite !piE -equiv_alg /=.
by apply: eq_crealP; exists m0=> * /=; rewrite mulrC subrr normr0.
Qed.

Lemma mul_algA : associative mul_alg.
Proof.
elim/quotW=> x; elim/quotW=> y; elim/quotW=> z; rewrite !piE -equiv_alg /=.
by apply: eq_crealP; exists m0=> * /=; rewrite mulrA subrr normr0.
Qed.

Lemma mul_1alg : left_id one_alg mul_alg.
Proof. by elim/quotW=> x; rewrite piE -equiv_alg /= mul_1creal. Qed.

Lemma mul_alg_addl : left_distributive mul_alg add_alg.
Proof.
elim/quotW=> x; elim/quotW=> y; elim/quotW=> z; rewrite !piE -equiv_alg /=.
by apply: eq_crealP; exists m0=> * /=; rewrite mulrDl subrr normr0.
Qed.

Arguments neq_creal_cst [F x y].
Prenex Implicits neq_creal_cst.

Lemma nonzero1_alg : one_alg != zero_alg.
Proof. by rewrite piE -(rwP neq_algcrealP) (rwP neq_creal_cst) oner_eq0. Qed.

Definition alg_comRingMixin :=
  ComRingMixin mul_algA mul_algC mul_1alg mul_alg_addl nonzero1_alg.
Canonical alg_Ring := Eval hnf in RingType alg alg_comRingMixin.
Canonical alg_comRing := Eval hnf in ComRingType alg mul_algC.
Canonical alg_of_Ring := Eval hnf in RingType {alg F} alg_comRingMixin.
Canonical alg_of_comRing := Eval hnf in ComRingType {alg F} mul_algC.

Lemma mul_pi x y : \pi_{alg F} x * \pi_{alg F} y
  = \pi_{alg F} (mul_algcreal x y).
Proof. by rewrite [_ * _]piE. Qed.

Lemma oneE : 1 = \pi_{alg F} one_algcreal.
Proof. by rewrite [1]piE. Qed.

Lemma mul_Valg (x : alg) : x != zero_alg -> mul_alg (inv_alg x) x = one_alg.
Proof.
elim/quotW: x=> x; rewrite piE -(rwP neq_algcrealP) /= => x_neq0.
apply/eqP; rewrite piE; apply/eq_algcrealP; rewrite /= /inv_algcreal.
case: eq_algcreal_dec=> [/(_ x_neq0) //|/= x_neq0'].
apply: eq_crealP; exists_big_modulus m F.
  by move=> * /=; rewrite mulVf ?subrr ?normr0 ?creal_neq0_always.
by close.
Qed.

Lemma inv_alg0 : inv_alg zero_alg = zero_alg.
Proof.
rewrite !piE -equiv_alg /= /inv_algcreal.
by case: eq_algcreal_dec=> //= zero_neq0; move: (eq_creal_refl zero_neq0).
Qed.

Lemma to_alg_additive : additive to_alg.
Proof.
move=> x y /=; rewrite !piE sub_pi -equiv_alg /=.
by apply: eq_crealP; exists m0=> * /=; rewrite subrr normr0.
Qed.

Canonical to_alg_is_additive := Additive to_alg_additive.

Lemma to_alg_multiplicative : multiplicative to_alg.
Proof.
split=> [x y |] //; rewrite !piE mul_pi -equiv_alg.
by apply: eq_crealP; exists m0=> * /=; rewrite subrr normr0.
Qed.

Canonical to_alg_is_rmorphism := AddRMorphism to_alg_multiplicative.

Lemma expn_pi (x : algcreal) (n : nat) :
  (\pi_{alg F} x) ^+ n = \pi (exp_algcreal x n).
Proof.
rewrite /exp_algcreal; case: n=> [|n]; first by rewrite expr0 oneE.
rewrite exprS iteropS; elim: n=> /= [|n ihn]; rewrite ?expr0 ?mulr1 //.
by rewrite exprS ihn mul_pi.
Qed.

Lemma horner_pi (p : {poly F}) (x : algcreal) :
  (p ^ to_alg).[\pi_alg x] = \pi (horner_algcreal p x).
Proof.
rewrite horner_coef /horner_algcreal size_map_poly.
apply: (big_ind2 (fun x y => x = \pi_alg y)).
+ by rewrite zeroE.
+ by move=> u u' v v' -> ->; rewrite [_ + _]piE.
by move=> i /= _; rewrite expn_pi coef_map /= [_ * _]piE.
Qed.

(* Defining annihilating polynomials for algebraics *)
Definition annul_alg : {alg F} -> {poly F} := locked (annul_creal \o repr).

Lemma root_annul_algcreal (x : algcreal) : ((annul_alg (\pi x)).[x] == 0)%CR.
Proof. by unlock annul_alg; rewrite /= -pi_algK root_annul_creal. Qed.

Lemma root_annul_alg (x : {alg F}) : root ((annul_alg x) ^ to_alg) x.
Proof.
apply/rootP; rewrite -[x]reprK horner_pi /= zeroE -equiv_alg.
by rewrite horner_algcrealE root_annul_algcreal.
Qed.

Lemma monic_annul_alg (x : {alg F}) : annul_alg x \is monic.
Proof. by unlock annul_alg; rewrite monic_annul_creal. Qed.

Lemma annul_alg_neq0 (x : {alg F}) : annul_alg x != 0.
Proof. by rewrite monic_neq0 ?monic_annul_alg. Qed.

Definition AlgFieldUnitMixin := FieldUnitMixin mul_Valg inv_alg0.
Canonical alg_unitRing :=
  Eval hnf in UnitRingType alg AlgFieldUnitMixin.
Canonical alg_comUnitRing := Eval hnf in [comUnitRingType of alg].
Canonical alg_of_unitRing :=
  Eval hnf in UnitRingType {alg F} AlgFieldUnitMixin.
Canonical alg_of_comUnitRing := Eval hnf in [comUnitRingType of {alg F}].

Lemma field_axiom : GRing.Field.mixin_of alg_unitRing. Proof. exact. Qed.

Definition AlgFieldIdomainMixin := (FieldIdomainMixin field_axiom).
Canonical alg_iDomain :=
  Eval hnf in IdomainType alg (FieldIdomainMixin field_axiom).
Canonical alg_fieldType := FieldType alg field_axiom.
Canonical alg_of_iDomain :=
  Eval hnf in IdomainType {alg F} (FieldIdomainMixin field_axiom).
Canonical alg_of_fieldType := FieldType {alg F} field_axiom.

Lemma inv_pi x : (\pi_{alg F} x)^-1  = \pi_{alg F} (inv_algcreal x).
Proof. by rewrite [_^-1]piE. Qed.

Lemma div_pi x y : \pi_{alg F} x / \pi_{alg F} y
  = \pi_{alg F} (mul_algcreal x (inv_algcreal y)).
Proof. by rewrite [_ / _]piE. Qed.

Definition lt_alg := lift_fun2 {alg F} lt_algcreal.
Definition le_alg := lift_fun2 {alg F} le_algcreal.

Lemma lt_alg_pi : {mono \pi_{alg F} : x y / lt_algcreal x y >-> lt_alg x y}.
Proof.
move=> x y; unlock lt_alg; rewrite /lt_algcreal.
by do 2!case: ltVge_algcreal_dec=> //=; rewrite !pi_algK.
Qed.

Canonical lt_alg_pi_mono := PiMono2 lt_alg_pi.

Lemma le_alg_pi : {mono \pi_{alg F} : x y / le_algcreal x y >-> le_alg x y}.
Proof.
move=> x y; unlock le_alg; rewrite /le_algcreal.
by do 2!case: ltVge_algcreal_dec=> //=; rewrite !pi_algK.
Qed.

Canonical le_alg_pi_mono := PiMono2 le_alg_pi.

Definition norm_alg := lift_op1 {alg F} norm_algcreal.

Lemma norm_alg_pi : {morph \pi_{alg F} : x / norm_algcreal x >-> norm_alg x}.
Proof.
move=> x; unlock norm_alg; rewrite /norm_algcreal /le_algcreal.
by do 2!case: ltVge_algcreal_dec=> //=; rewrite !(pi_opp, pi_algK, reprK).
Qed.

Canonical norm_alg_pi_morph := PiMorph1 norm_alg_pi.

(* begin hide *)
(* Lemma norm_pi (x : algcreal) : `|\pi_{alg F} x| = \pi (norm_algcreal x). *)
(* Proof. by rewrite /norm_algcreal -lt_pi -zeroE -lerNgt fun_if -opp_pi. Qed. *)
(* end hide *)

Lemma add_alg_gt0 x y : lt_alg zero_alg x -> lt_alg zero_alg y ->
  lt_alg zero_alg (x + y).
Proof.
rewrite -[x]reprK -[y]reprK !piE -!(rwP lt_algcrealP).
move=> x_gt0 y_gt0; pose_big_enough i.
  apply: (@lt_crealP _ (diff x_gt0 + diff y_gt0) i i) => //.
    by rewrite addr_gt0 ?diff_gt0.
  by rewrite /= add0r ler_add // ?diff0P.
by close.
Qed.

Lemma mul_alg_gt0 x y : lt_alg zero_alg x -> lt_alg zero_alg y ->
  lt_alg zero_alg (x * y).
Proof.
rewrite -[x]reprK -[y]reprK !piE -!(rwP lt_algcrealP).
move=> x_gt0 y_gt0; pose_big_enough i.
  apply: (@lt_crealP _ (diff x_gt0 * diff y_gt0) i i) => //.
    by rewrite pmulr_rgt0 ?diff_gt0.
  rewrite /= add0r (@ler_trans _ (diff x_gt0 * (repr y) i)) //.
    by rewrite ler_wpmul2l ?(ltrW (diff_gt0 _)) // diff0P.
  by rewrite ler_wpmul2r ?diff0P ?ltrW ?creal_gt0_always.
by close.
Qed.

Lemma gt0_alg_nlt0 x : lt_alg zero_alg x -> ~~ lt_alg x zero_alg.
Proof.
rewrite -[x]reprK !piE -!(rwP lt_algcrealP, rwP le_algcrealP).
move=> hx; pose_big_enough i.
  apply: (@le_crealP _ i)=> j /= hj.
  by rewrite ltrW // creal_gt0_always.
by close.
Qed.

Lemma sub_alg_gt0 x y : lt_alg zero_alg (y - x) = lt_alg x y.
Proof.
rewrite -[x]reprK -[y]reprK !piE; apply/lt_algcrealP/lt_algcrealP=> /= hxy.
  pose_big_enough i.
    apply: (@lt_crealP _ (diff hxy) i i); rewrite ?diff_gt0 //.
    by rewrite (monoLR (addNKr _) (ler_add2l _)) addrC diff0P.
  by close.
pose_big_enough i.
  apply: (@lt_crealP _ (diff hxy) i i); rewrite ?diff_gt0 //.
  by rewrite (monoRL (addrK _) (ler_add2r _)) add0r addrC diffP.
by close.
Qed.

Lemma lt0_alg_total (x : alg) : x != zero_alg ->
  lt_alg zero_alg x || lt_alg x zero_alg.
Proof.
rewrite -[x]reprK !piE => /neq_algcrealP /= x_neq0.
apply/orP; rewrite -!(rwP lt_algcrealP).
case/neq_creal_ltVgt: x_neq0=> /= [lt_x0|lt_0x]; [right|by left].
pose_big_enough i.
  by apply: (@lt_crealP _ (diff lt_x0) i i); rewrite ?diff_gt0 ?diffP.
by close.
Qed.

Lemma norm_algN x :  norm_alg (- x) = norm_alg x.
Proof.
rewrite -[x]reprK !piE /= -equiv_alg !norm_algcrealE; apply: eq_crealP.
exists_big_modulus m F=> [e i e_gt0 hi /=|].
  by rewrite normrN subrr normr0.
by close.
Qed.

Lemma ge0_norm_alg x : le_alg 0 x -> norm_alg x = x.
Proof. by rewrite -[x]reprK !piE /= /norm_algcreal => ->. Qed.

Lemma lt_alg0N (x : alg) : lt_alg 0 (- x) = lt_alg x 0.
Proof. by rewrite -sub0r sub_alg_gt0. Qed.

Lemma lt_alg00 : lt_alg zero_alg zero_alg = false.
Proof. by have /implyP := @gt0_alg_nlt0 0; case: lt_alg. Qed.

Lemma le_alg_def x y : le_alg x y = (y == x) || lt_alg x y.
Proof.
rewrite -[x]reprK -[y]reprK eq_sym piE [lt_alg _ _]piE; apply/le_algcrealP/orP.
  move=> /le_creal_neqVlt [/eq_algcrealP/eqquotP/eqP-> //|lt_xy]; first by left.
  by right; apply/lt_algcrealP.
by move=> [/eqP/eqquotP/eq_algcrealP-> //| /lt_algcrealP /lt_crealW].
Qed.

Definition AlgNumFieldMixin := RealLtMixin add_alg_gt0 mul_alg_gt0
  gt0_alg_nlt0 sub_alg_gt0 lt0_alg_total norm_algN ge0_norm_alg le_alg_def.
Canonical alg_numDomainType := NumDomainType alg AlgNumFieldMixin.
Canonical alg_numFieldType := [numFieldType of alg].
Canonical alg_of_numDomainType := [numDomainType of {alg F}].
Canonical alg_of_numFieldType := [numFieldType of {alg F}].

Definition AlgRealFieldMixin := RealLeAxiom alg.
Canonical alg_realDomainType := RealDomainType alg AlgRealFieldMixin.
Canonical alg_realFieldType := [realFieldType of alg].
Canonical alg_of_realDomainType := [realDomainType of {alg F}].
Canonical alg_of_realFieldType := [realFieldType of {alg F}].

Lemma lt_pi x y : \pi_{alg F} x < \pi y = lt_algcreal x y.
Proof. by rewrite [_ < _]lt_alg_pi. Qed.

Lemma le_pi x y : \pi_{alg F} x <= \pi y = le_algcreal x y.
Proof. by rewrite [_ <= _]le_alg_pi. Qed.

Lemma norm_pi (x : algcreal) : `|\pi_{alg F} x| = \pi (norm_algcreal x).
Proof. by rewrite [`|_|]piE. Qed.

Lemma lt_algP (x y : algcreal) : reflect (x < y)%CR (\pi_{alg F} x < \pi y).
Proof. by rewrite lt_pi; apply: lt_algcrealP. Qed.
Arguments lt_algP [x y].

Lemma le_algP (x y : algcreal) : reflect (x <= y)%CR (\pi_{alg F} x <= \pi y).
Proof. by rewrite le_pi; apply: le_algcrealP. Qed.
Arguments le_algP [x y].
Prenex Implicits lt_algP le_algP.

Lemma ler_to_alg : {mono to_alg : x y / x <= y}.
Proof.
apply: homo_mono=> x y lt_xy; rewrite !piE -(rwP lt_algP).
by apply/lt_creal_cst; rewrite lt_xy.
Qed.

Lemma ltr_to_alg : {mono to_alg : x y / x < y}.
Proof. by apply: lerW_mono; apply: ler_to_alg. Qed.

Lemma normr_to_alg : { morph to_alg : x / `|x| }.
Proof.
move=> x /=; have [] := ger0P; have [] := ger0P x%:RA;
  rewrite ?rmorph0 ?rmorphN ?oppr0 //=.
  by rewrite ltr_to_alg lerNgt => ->.
by rewrite ler_to_alg ltrNge => ->.
Qed.

Lemma inf_alg_proof x : {d | 0 < d & 0 < x -> (d%:RA < x)}.
Proof.
have [|] := lerP; first by exists 1.
elim/quotW: x=> x; rewrite zeroE=> /lt_algP /= x_gt0.
exists (diff x_gt0 / 2%:R); first by rewrite pmulr_rgt0 ?gtr0E ?diff_gt0.
rewrite piE -(rwP lt_algP) /= => _; pose_big_enough i.
  apply: (@lt_crealP _ (diff x_gt0 / 2%:R) i i) => //.
    by rewrite pmulr_rgt0 ?gtr0E ?diff_gt0.
  by rewrite -[_ + _](splitf 2) diff0P.
by close.
Qed.

Definition inf_alg (x : {alg F}) : F :=
  let: exist2 d _ _ := inf_alg_proof x in d.

Lemma inf_alg_gt0 x : 0 < inf_alg x.
Proof. by rewrite /inf_alg; case: inf_alg_proof. Qed.

Lemma inf_lt_alg x : 0 < x -> (inf_alg x)%:RA < x.
Proof. by rewrite /inf_alg=> x_gt0; case: inf_alg_proof=> d _ /(_ x_gt0). Qed.

Lemma approx_proof x e : {y | 0 < e -> `|x - y%:RA| < e}.
Proof.
elim/quotW:x => x; pose_big_enough i.
  exists (x i)=> e_gt0; rewrite (ltr_trans _ (inf_lt_alg _)) //.
  rewrite !piE sub_pi norm_pi -(rwP lt_algP) /= norm_algcrealE /=.
  pose_big_enough j.
    apply: (@lt_crealP  _ (inf_alg e / 2%:R) j j) => //.
      by rewrite pmulr_rgt0 ?gtr0E ?inf_alg_gt0.
    rewrite /= {2}[inf_alg e](splitf 2) /= ler_add2r.
    by rewrite ltrW // cauchymodP ?pmulr_rgt0 ?gtr0E ?inf_alg_gt0.
  by close.
by close.
Qed.

Definition approx := locked
  (fun (x : alg) (e : alg) => projT1 (approx_proof x e) : F).

Lemma approxP (x e e': alg) : 0 < e -> e <= e' -> `|x - (approx x e)%:RA| < e'.
Proof.
by unlock approx; case: approx_proof=> /= y hy /hy /ltr_le_trans hy' /hy'.
Qed.

Lemma alg_archi : Num.archimedean_axiom alg_of_numDomainType.
Proof.
move=> x; move: {x}`|x| (normr_ge0 x) => x x_ge0.
pose a := approx x 1%:RA; exists (Num.bound (a + 1)).
have := @archi_boundP _ (a + 1); rewrite -ltr_to_alg rmorph_nat.
have := @approxP x _ _ ltr01 (lerr _); rewrite ltr_distl -/a => /andP [_ hxa].
rewrite -ler_to_alg rmorphD /= (ler_trans _ (ltrW hxa)) //.
by move=> /(_ isT) /(ltr_trans _)->.
Qed.

Canonical alg_archiFieldType := ArchiFieldType alg alg_archi.
Canonical alg_of_archiFieldType := [archiFieldType of {alg F}].

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
  by exists a%:RA; rewrite ?lerr ?ler_to_alg // rmorph0 root0.
move=> /andP[pa_le0 pb_ge0]; apply/sig2W.
have hpab: p.[a] * p.[b] <= 0 by rewrite mulr_le0_ge0.
move=> {pa_le0 pb_ge0}; wlog monic_p : p hpab p_neq0 / p \is monic.
  set q := (lead_coef p) ^-1 *: p => /(_ q).
  rewrite !hornerZ mulrCA !mulrA -mulrA mulr_ge0_le0 //; last first.
    by rewrite (@exprn_even_ge0 _ 2).
  have mq: q \is monic by rewrite monicE lead_coefZ mulVf ?lead_coef_eq0.
  rewrite monic_neq0 ?mq=> // [] [] // x hx hqx; exists x=> //.
  move: hqx; rewrite /q -mul_polyC rmorphM /= rootM map_polyC rootC.
  by rewrite fmorph_eq0 invr_eq0 lead_coef_eq0 (negPf p_neq0).
pose c := (a + b) / 2%:R; pose r := (b - a) / 2%:R.
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
  { ap : {alg F} * seq {poly F} |
    [forall i : 'I_(size s), (ap.2`_i ^ to_alg).[ap.1] == s`_i]
    &  size ap.2 = size s }.
Proof.
apply: sig2_eqW; elim: s; first by exists (0,[::])=> //; apply/forallP=> [] [].
move=> x s [[a sp] /forallP /= hs hsize].
have:= char0_PET _ (root_annul_alg a) _ (root_annul_alg x).
rewrite !annul_alg_neq0 => /(_ isT isT (char_num _)) /= [n [[p hp] [q hq]]].
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

Definition pet_alg s : {alg F} :=
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

Definition poly_ground := locked (fun (p : {poly {alg F}}) =>
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
  rewrite horner_polyC -lead_coef_eq0 lead_coef_map_eq /=;
  by do ?rewrite swapXY_map /= lead_coef_map_eq /=
        ?map_poly_eq0 ?lead_coef_eq0 ?swapXY_eq0 ?(negPf u'a_neq0).
have u'_neq0 : u' != 0 by rewrite lead_coef_eq0 swapXY_eq0.
have size_u' : (size u' < size q)%N.
  by rewrite /u' (leq_ltn_trans (max_size_lead_coefXY _)) // sizeYE swapXYK.
move: u'a_eq0=> /ihn [] //; first by rewrite -ltnS (leq_trans size_u').
by move=> r; exists r.
Qed.

Definition annul_pet_alg (p : {poly {alg F}}) : {poly F} :=
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
  (at level 2, left associativity, format "x %:RA").

Lemma upper_nthrootVP (F : archiFieldType) (x : F) (i : nat) :
   0 < x -> (Num.bound (x ^-1) <= i)%N -> 2%:R ^- i < x.
Proof.
move=> x_gt0 hx; rewrite -ltf_pinv -?topredE //= ?gtr0E //.
by rewrite invrK upper_nthrootP.
Qed.

Notation "{ 'alg'  F }" := (alg_of (Phant F)).

Section AlgAlg.

Variable F : archiFieldType.

Local Open Scope ring_scope.

Local Notation "p ^ f" := (map_poly f p) : ring_scope.
Local Notation "'Y" := 'X%:P.
Local Notation m0 := (fun _ => 0%N).

Definition approx2 (x : {alg {alg F}}) i :=
  approx (approx x (2%:R ^- i)) (2%:R ^- i).

Lemma asympt_approx2 x : { asympt e : i / `|(approx2 x i)%:RA%:RA - x| < e }.
Proof.
exists_big_modulus m {alg {alg F}}.
  move=> e i e_gt0 hi; rewrite distrC /approx2.
  rewrite (@split_dist_add _ (approx x (2%:R ^- i))%:RA) //.
    rewrite approxP ?gtr0E // ltrW //.
    by rewrite upper_nthrootVP ?divrn_gt0 ?ltr_to_alg.
  rewrite (ltr_trans _ (inf_lt_alg _)) ?divrn_gt0 //.
  rewrite -rmorphB -normr_to_alg ltr_to_alg approxP ?gtr0E // ltrW //.
  by rewrite upper_nthrootVP ?divrn_gt0 ?inf_alg_gt0 ?ltr_to_alg.
by close.
Qed.

Lemma from_alg_crealP (x : {alg {alg F}}) : creal_axiom (approx2 x).
Proof.
exists_big_modulus m F.
  move=> e i j e_gt0 hi hj; rewrite -2!ltr_to_alg !normr_to_alg !rmorphB /=.
  rewrite (@split_dist_add _ x) // ?[`|_ - _%:RA|]distrC;
  by rewrite (@asympt1modP _ _ (asympt_approx2 x)) ?divrn_gt0 ?ltr_to_alg.
by close.
Qed.

Definition from_alg_creal := locked (fun x => CReal (from_alg_crealP x)).

Lemma to_alg_crealP (x : creal F) :  creal_axiom (fun i => to_alg F (x i)).
Proof.
exists_big_modulus m (alg F).
  move=> e i j e_gt0 hi hj.
  rewrite -rmorphB -normr_to_alg (ltr_trans _ (inf_lt_alg _)) //.
  by rewrite ltr_to_alg cauchymodP ?inf_alg_gt0.
by close.
Qed.
Definition to_alg_creal x := CReal (to_alg_crealP x).

Lemma horner_to_alg_creal p x :
  ((p ^ to_alg F).[to_alg_creal x] == to_alg_creal p.[x])%CR.
Proof.
by apply: eq_crealP; exists m0=> * /=; rewrite horner_map subrr normr0.
Qed.

Lemma neq_to_alg_creal x y :
  (to_alg_creal x != to_alg_creal y)%CR <-> (x != y)%CR.
Proof.
split=> neq_xy.
  pose_big_enough i.
    apply: (@neq_crealP _ (inf_alg (lbound neq_xy)) i i) => //.
      by rewrite inf_alg_gt0.
    rewrite -ler_to_alg normr_to_alg rmorphB /= ltrW //.
    by rewrite (ltr_le_trans (inf_lt_alg _)) ?lbound_gt0 ?lboundP.
  by close.
pose_big_enough i.
  apply: (@neq_crealP _ (lbound neq_xy)%:RA i i) => //.
    by rewrite ltr_to_alg lbound_gt0.
  by rewrite -rmorphB -normr_to_alg ler_to_alg lboundP.
by close.
Qed.

Lemma eq_to_alg_creal x y :
  (to_alg_creal x == to_alg_creal y)%CR -> (x == y)%CR.
Proof. by move=> hxy /neq_to_alg_creal. Qed.

Lemma to_alg_creal0 : (to_alg_creal 0 == 0)%CR.
Proof. by apply: eq_crealP; exists m0=> * /=; rewrite subrr normr0. Qed.

Import Setoid.

Add Morphism to_alg_creal
 with signature (@eq_creal _) ==> (@eq_creal _) as to_alg_creal_morph.
Proof. by move=> x y hxy /neq_to_alg_creal. Qed.
Global Existing Instance to_alg_creal_morph_Proper.

Lemma to_alg_creal_repr (x : {alg F}) : (to_alg_creal (repr x) == x%:CR)%CR.
Proof.
apply: eq_crealP; exists_big_modulus m {alg F}.
  move=> e i e_gt0 hi /=; rewrite (ler_lt_trans _ (inf_lt_alg _)) //.
  rewrite -{2}[x]reprK !piE sub_pi norm_pi.
  rewrite -(rwP (le_algP _ _)) norm_algcrealE /=; pose_big_enough j.
    apply: (@le_crealP _ j)=> k hk /=.
    by rewrite ltrW // cauchymodP ?inf_alg_gt0.
  by close.
by close.
Qed.

Local Open Scope quotient_scope.

Lemma cst_pi (x : algcreal F) : ((\pi_{alg F} x)%:CR == to_alg_creal x)%CR.
Proof.
apply: eq_crealP; exists_big_modulus m {alg F}.
  move=> e i e_gt0 hi /=; rewrite (ltr_trans _ (inf_lt_alg _)) //.
  rewrite !piE sub_pi norm_pi /= -(rwP (lt_algP _ _)) norm_algcrealE /=.
  pose_big_enough j.
    apply: (@lt_crealP _ (inf_alg e / 2%:R) j j) => //.
      by rewrite ?divrn_gt0 ?inf_alg_gt0.
    rewrite /= {2}[inf_alg _](splitf 2) ler_add2r ltrW // distrC.
    by rewrite cauchymodP ?divrn_gt0 ?inf_alg_gt0.
  by close.
by close.
Qed.

End AlgAlg.

Section AlgAlgAlg.

Variable F : archiFieldType.

Local Open Scope ring_scope.

Local Notation "p ^ f" := (map_poly f p) : ring_scope.
Local Notation "'Y" := 'X%:P.

Lemma from_alg_crealK (x : {alg {alg F}}) :
  (to_alg_creal (to_alg_creal (from_alg_creal x)) == x%:CR)%CR.
Proof.
apply: eq_crealP; exists_big_modulus m {alg {alg F}}.
  move=> e i e_gt0 hi; unlock from_alg_creal=> /=.
  by rewrite (@asympt1modP _ _ (asympt_approx2 x)).
by close.
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
+ rewrite size_map_polyC -(size_map_poly [rmorphism of to_alg _]) /=.
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

Canonical alg_rcfType := RcfType (alg F) ivt.
Canonical alg_of_rcfType := [rcfType of {alg F}].

End AlgAlgAlg.
End RealAlg.

Notation "{ 'realclosure'  F }" := (RealAlg.alg_of (Phant F)).

Notation annul_realalg := RealAlg.annul_alg.
Notation realalg_of F := (@RealAlg.to_alg_def _ (Phant F)).
Notation "x %:RA" := (realalg_of x)
  (at level 2, left associativity, format "x %:RA").

Canonical RealAlg.alg_eqType.
Canonical RealAlg.alg_choiceType.
Canonical RealAlg.alg_zmodType.
Canonical RealAlg.alg_Ring.
Canonical RealAlg.alg_comRing.
Canonical RealAlg.alg_unitRing.
Canonical RealAlg.alg_comUnitRing.
Canonical RealAlg.alg_iDomain.
Canonical RealAlg.alg_fieldType.
Canonical RealAlg.alg_numDomainType.
Canonical RealAlg.alg_numFieldType.
Canonical RealAlg.alg_realDomainType.
Canonical RealAlg.alg_realFieldType.
Canonical RealAlg.alg_archiFieldType.
Canonical RealAlg.alg_rcfType.

Canonical RealAlg.alg_of_eqType.
Canonical RealAlg.alg_of_choiceType.
Canonical RealAlg.alg_of_zmodType.
Canonical RealAlg.alg_of_Ring.
Canonical RealAlg.alg_of_comRing.
Canonical RealAlg.alg_of_unitRing.
Canonical RealAlg.alg_of_comUnitRing.
Canonical RealAlg.alg_of_iDomain.
Canonical RealAlg.alg_of_fieldType.
Canonical RealAlg.alg_of_numDomainType.
Canonical RealAlg.alg_of_numFieldType.
Canonical RealAlg.alg_of_realDomainType.
Canonical RealAlg.alg_of_realFieldType.
Canonical RealAlg.alg_of_archiFieldType.
Canonical RealAlg.alg_of_rcfType.

Canonical RealAlg.to_alg_is_rmorphism.
Canonical RealAlg.to_alg_is_additive.

Section RealClosureTheory.

Variable F : archiFieldType.
Notation R := {realclosure F}.

Local Notation "p ^ f" := (map_poly f p) : ring_scope.

Lemma root_annul_realalg (x : R) : root ((annul_realalg x) ^ realalg_of _) x.
Proof. exact: RealAlg.root_annul_alg. Qed.
Hint Resolve root_annul_realalg.

Lemma monic_annul_realalg (x : R) : annul_realalg x \is monic.
Proof. exact: RealAlg.monic_annul_alg. Qed.
Hint Resolve monic_annul_realalg.

Lemma annul_realalg_neq0 (x : R) : annul_realalg x != 0%R.
Proof. exact: RealAlg.annul_alg_neq0. Qed.
Hint Resolve annul_realalg_neq0.

Lemma realalg_algebraic : integralRange (realalg_of F).
Proof. by move=> x; exists (annul_realalg x). Qed.

End RealClosureTheory.

Definition realalg := {realclosure rat}.
Canonical realalg_eqType := [eqType of realalg].
Canonical realalg_choiceType := [choiceType of realalg].
Canonical realalg_zmodType := [zmodType of realalg].
Canonical realalg_ringType := [ringType of realalg].
Canonical realalg_comRingType := [comRingType of realalg].
Canonical realalg_unitRingType := [unitRingType of realalg].
Canonical realalg_comUnitRingType := [comUnitRingType of realalg].
Canonical realalg_idomainType := [idomainType of realalg].
Canonical realalg_fieldTypeType := [fieldType of realalg].
Canonical realalg_numDomainType := [numDomainType of realalg].
Canonical realalg_numFieldType := [numFieldType of realalg].
Canonical realalg_realDomainType := [realDomainType of realalg].
Canonical realalg_realFieldType := [realFieldType of realalg].
Canonical realalg_archiFieldType := [archiFieldType of realalg].
Canonical realalg_rcfType := [rcfType of realalg].

Module RatRealAlg.
Canonical RealAlg.algdom_choiceType.
Definition realalgdom_CountMixin :=
   PcanCountMixin (@RealAlg.encode_algdomK [archiFieldType of rat]).
Canonical realalgdom_countType :=
   CountType (RealAlg.algdom [archiFieldType of rat]) realalgdom_CountMixin.
Definition realalg_countType := [countType of realalg].
End RatRealAlg.

Canonical RatRealAlg.realalg_countType.

(* From mathcomp
Require Import countalg. *)
(* Canonical realalg_countZmodType := [countZmodType of realalg]. *)
(* Canonical realalg_countRingType := [countRingType of realalg]. *)
(* Canonical realalg_countComRingType := [countComRingType of realalg]. *)
(* Canonical realalg_countUnitRingType := [countUnitRingType of realalg]. *)
(* Canonical realalg_countComUnitRingType := [countComUnitRingType of realalg]. *)
(* Canonical realalg_countIdomainType := [countIdomainType of realalg]. *)
(* Canonical realalg_countFieldTypeType := [countFieldType of realalg]. *)

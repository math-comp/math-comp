(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype bigop order ssralg countalg div ssrnum.
From mathcomp Require Import ssrint prime archimedean.

(******************************************************************************)
(* This file defines a datatype for rational numbers and equips it with a     *)
(* structure of archimedean, real field, with int and nat declared as closed  *)
(* subrings.                                                                  *)
(*          rat == the type of rational number, with single constructor Rat   *)
(*     <number> == <number> as a rat with <number> a decimal constant.        *)
(*                 This notation is in rat_scope (delimited with %Q).         *)
(*         n%:Q == explicit cast from int to rat, ie. the specialization to   *)
(*                 rationals of the generic ring morphism n%:~R               *)
(*       numq r == numerator of (r : rat)                                     *)
(*       denq r == denominator of (r : rat)                                   *)
(*       ratr r == generic embedding of (r : rat) into an arbitrary unit ring.*)
(* [rat x // y] == smart constructor for rationals, definitionally equal      *)
(*                 to x / y for concrete values, intended for printing only   *)
(*                 of normal forms. The parsable notation is for debugging.   *)
(******************************************************************************)

Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "[ 'rat' x // y ]" (format "[ 'rat'  x  //  y ]", at level 0).
Reserved Notation "n %:Q" (at level 2, left associativity, format "n %:Q").

Local Open Scope ring_scope.
Local Notation sgr := Num.sg.

Record rat : Set := Rat {
  valq : (int * int);
  _ : (0 < valq.2) && coprime `|valq.1| `|valq.2|
}.

Bind Scope ring_scope with rat.
Delimit Scope rat_scope with Q.

Definition ratz (n : int) := @Rat (n, 1) (coprimen1 _).
(* Coercion ratz (n : int) := @Rat (n, 1) (coprimen1 _). *)

Definition rat_isSub := Eval hnf in [isSub for valq].
HB.instance Definition _ := rat_isSub.
#[hnf] HB.instance Definition _ := [Equality of rat by <:].
HB.instance Definition _ := [Countable of rat by <:].

Definition numq x := (valq x).1.
Definition denq x := (valq x).2.
Arguments numq : simpl never.
Arguments denq : simpl never.

Lemma denq_gt0 x : 0 < denq x.
Proof. by rewrite /denq; case: x=> [[a b] /= /andP []]. Qed.
#[global] Hint Resolve denq_gt0 : core.

Definition denq_ge0 x := ltW (denq_gt0 x).

Lemma denq_lt0 x : (denq x < 0) = false. Proof. by rewrite lt_gtF. Qed.

Lemma denq_neq0 x : denq x != 0.
Proof. by rewrite /denq gt_eqF ?denq_gt0. Qed.
#[global] Hint Resolve denq_neq0 : core.

Lemma denq_eq0 x : (denq x == 0) = false.
Proof. exact: negPf (denq_neq0 _). Qed.

Lemma coprime_num_den x : coprime `|numq x| `|denq x|.
Proof. by rewrite /numq /denq; case: x=> [[a b] /= /andP []]. Qed.

Fact RatK x P : @Rat (numq x, denq x) P = x.
Proof. by move: x P => [[a b] P'] P; apply: val_inj. Qed.

Definition fracq_subdef x :=
  if x.2 != 0 then  let g := gcdn `|x.1| `|x.2| in
    ((-1) ^ ((x.2 < 0) (+) (x.1 < 0)) * (`|x.1| %/ g)%:Z, (`|x.2| %/ g)%:Z)
 else (0, 1).
Arguments fracq_subdef /.

Definition fracq_opt_subdef (x : int * int) :=
  if (0 < x.2) && coprime `|x.1| `|x.2| then x else fracq_subdef x.

Lemma fracq_opt_subdefE x : fracq_opt_subdef x = fracq_subdef x.
Proof.
rewrite /fracq_opt_subdef; case: ifP => //; case: x => n d /= /andP[d_gt0 cnd].
rewrite /fracq_subdef gt_eqF//= lt_gtF//= (eqP cnd) !divn1 abszEsg gtz0_abs//.
rewrite mulrA sgz_def mulrnAr -signr_addb addbb expr0.
by have [->|] := eqVneq n 0; rewrite (mulr0, mul1r).
Qed.

Fact fracq_subproof x (y := fracq_opt_subdef x) :
  (0 < y.2) && (coprime `|y.1| `|y.2|).
Proof.
rewrite {}/y fracq_opt_subdefE /=; have [] //= := eqVneq x.2 0.
case: x => [/= n d]; rewrite -absz_gt0 => dN0.
have ggt0 : (0 < gcdn `|n| `|d|)%N by rewrite gcdn_gt0 dN0 orbT.
rewrite ltz_nat divn_gt0// dvdn_leq ?dvdn_gcdr//=.
rewrite abszM abszX abszN1 exp1n mul1n absz_nat.
rewrite /coprime -(@eqn_pmul2r (gcdn `|n| `|d|))// mul1n.
by rewrite muln_gcdl !divnK ?(dvdn_gcdl, dvdn_gcdr).
Qed.

Lemma fracq_opt_subdef_id x :
  fracq_opt_subdef (fracq_opt_subdef x) = fracq_subdef x.
Proof.
rewrite [fracq_opt_subdef (_ x)]/fracq_opt_subdef.
by rewrite fracq_subproof fracq_opt_subdefE.
Qed.

(* We use a match expression in order to "lock" the definition of fracq.   *)
(* Indeed, the kernel will try to reduce a fracq only when applied to      *)
(* a term which has "enough" constructors: i.e. it reduces to a pair of    *)
(* a Posz or Negz on the first component, and a Posz of 0 or S, or a Negz  *)
(* on the second component. See issue #698.                                *)
(* Additionally, we use fracq_opt_subdef to precompute the normal form     *)
(* before we use fracq_subproof in order to make sure the proof will be    *)
(* independent from the input of fracq. This ensure reflexivity of any     *)
(* computation involving rationals as long as all operators use fracq.     *)
(* As a consequence val (fracq x) = fracq_opt_subdef (fracq_opt_subdef x)) *)
Definition fracq '((n', d')) : rat :=
  match d', n' with
  | Posz 0 as d, _ as n => Rat (fracq_subproof (1, 0))
  | _ as d, Posz _ as n | _ as d, _ as n =>
     Rat (fracq_subproof (fracq_opt_subdef (n, d)))
  end.
Arguments fracq : simpl never.

(* Define a Number Notation for rat in rat_scope *)
(* Since rat values obtained from fracq contain fracq_subdef, which is not *)
(* an inductive constructor, we need to go through an intermediate         *)
(* inductive type.                                                         *)
Variant Irat_prf := Ifracq_subproof : (int * int) -> Irat_prf.
Variant Irat := IRat : (int * int) -> Irat_prf -> Irat.

Definition parse (x : Number.number) : option Irat :=
  let parse_pos i f :=
    let nf := Decimal.nb_digits f in
    let d := (10 ^ nf)%nat in
    let n := (Nat.of_uint i * d + Nat.of_uint f)%nat in
    valq (fracq (Posz n, Posz d)) in
  let parse i f :=
    match i with
    | Decimal.Pos i => parse_pos i f
    | Decimal.Neg i => let (n, d) := parse_pos i f in ((- n)%R, d)
    end in
  match x with
  | Number.Decimal (Decimal.Decimal i f) =>
      let nd := parse i f in
      Some (IRat nd (Ifracq_subproof nd))
  | Number.Decimal (Decimal.DecimalExp _ _ _) => None
  | Number.Hexadecimal _ => None
  end.

Definition print (r : Irat) : option Number.number :=
  let print_pos n d :=
    if d == 1%nat then Some (Nat.to_uint n, Decimal.Nil) else
      let d2d5 :=
        match prime_decomp d with
        | [:: (2, d2); (5, d5)] => Some (d2, d5)
        | [:: (2, d2)] => Some (d2, O)
        | [:: (5, d5)] => Some (O, d5)
        | _ => None
        end in
      match d2d5 with
      | Some (d2, d5) =>
          let f := (2 ^ (d5 - d2) * 5 ^ (d2 - d5))%nat in
          let (i, f) := edivn (n * f) (d * f) in
          Some (Nat.to_uint i, Nat.to_uint f)
      | None => None
      end in
  let print_IRat nd :=
    match nd with
    | (Posz n, Posz d) =>
        match print_pos n d with
        | Some (i, f) => Some (Decimal.Pos i, f)
        | None => None
        end
    | (Negz n, Posz d) =>
        match print_pos n.+1 d with
        | Some (i, f) => Some (Decimal.Neg i, f)
        | None => None
        end
    | (_, Negz _) => None
    end in
  match r with
  | IRat nd _ =>
      match print_IRat nd with
      | Some (i, f) => Some (Number.Decimal (Decimal.Decimal i f))
      | None => None
      end
  end.

Number Notation rat parse print (via Irat
  mapping [Rat => IRat, fracq_subproof => Ifracq_subproof])
  : rat_scope.

(* Now, the following should parse as rat (and print unchanged) *)
(* Check 12%Q. *)
(* Check 3.14%Q. *)
(* Check (-3.14)%Q. *)
(* Check 0.5%Q. *)
(* Check 0.2%Q. *)

Lemma val_fracq x : val (fracq x) = fracq_subdef x.
Proof. by case: x => [[n|n] [[|[|d]]|d]]//=; rewrite !fracq_opt_subdef_id. Qed.

Lemma num_fracq x : numq (fracq x) = if x.2 != 0 then
  (-1) ^ ((x.2 < 0) (+) (x.1 < 0)) * (`|x.1| %/ gcdn `|x.1| `|x.2|)%:Z else 0.
Proof. by rewrite /numq val_fracq/=; case: ifP. Qed.

Lemma den_fracq x : denq (fracq x) =
  if x.2 != 0 then (`|x.2| %/ gcdn `|x.1| `|x.2|)%:Z else 1.
Proof. by rewrite /denq val_fracq/=; case: ifP. Qed.

Fact ratz_frac n : ratz n = fracq (n, 1).
Proof.
by apply: val_inj; rewrite val_fracq/= gcdn1 !divn1 abszE mulr_sign_norm.
Qed.

Fact valqK x : fracq (valq x) = x.
Proof.
move: x => [[n d] /= Pnd]; apply: val_inj; rewrite ?val_fracq/=.
move: Pnd; rewrite /coprime /fracq /= => /andP[] hd -/eqP hnd.
by rewrite lt_gtF ?gt_eqF //= hnd !divn1 mulz_sign_abs abszE gtr0_norm.
Qed.

Definition scalq '(n, d) := sgr d * (gcdn `|n| `|d|)%:Z.
Lemma scalq_def x : scalq x = sgr x.2 * (gcdn `|x.1| `|x.2|)%:Z.
Proof. by case: x. Qed.

Fact scalq_eq0 x : (scalq x == 0) = (x.2 == 0).
Proof.
case: x => n d; rewrite scalq_def /= mulf_eq0 sgr_eq0 /= eqz_nat.
rewrite -[gcdn _ _ == 0]negbK -lt0n gcdn_gt0 ?absz_gt0 [X in ~~ X]orbC.
by case: sgrP.
Qed.

Lemma sgr_scalq x : sgr (scalq x) = sgr x.2.
Proof.
rewrite scalq_def sgrM sgr_id -[(gcdn _ _)%:Z]intz sgr_nat.
by rewrite -lt0n gcdn_gt0 ?absz_gt0 orbC; case: sgrP; rewrite // mul0r.
Qed.

Lemma signr_scalq x : (scalq x < 0) = (x.2 < 0).
Proof. by rewrite -!sgr_cp0 sgr_scalq. Qed.

Lemma scalqE x :
  x.2 != 0 -> scalq x = (-1) ^+ (x.2 < 0)%R * (gcdn `|x.1| `|x.2|)%:Z.
Proof. by rewrite scalq_def; case: sgrP. Qed.

Fact valq_frac x :
  x.2 != 0 -> x = (scalq x * numq (fracq x), scalq x * denq (fracq x)).
Proof.
move=> x2_neq0; rewrite scalqE//; move: x2_neq0.
case: x => [n d] /= d_neq0; rewrite num_fracq den_fracq/= ?d_neq0.
rewrite mulr_signM -mulrA -!PoszM addKb.
do 2!rewrite muln_divCA ?(dvdn_gcdl, dvdn_gcdr) // divnn.
by rewrite gcdn_gt0 !absz_gt0 d_neq0 orbT !muln1 !mulz_sign_abs.
Qed.

Definition zeroq := 0%Q.
Definition oneq := 1%Q.

Fact frac0q x : fracq (0, x) = zeroq.
Proof.
apply: val_inj; rewrite //= val_fracq/= div0n !gcd0n !mulr0 !divnn.
by have [//|x_neq0] := eqVneq; rewrite absz_gt0 x_neq0.
Qed.

Fact fracq0  x : fracq (x, 0) = zeroq. Proof. exact/eqP. Qed.

Variant fracq_spec (x : int * int) : int * int -> rat -> Type :=
  | FracqSpecN of x.2 = 0 : fracq_spec x (x.1, 0) zeroq
  | FracqSpecP k fx of k != 0 : fracq_spec x (k * numq fx, k * denq fx) fx.

Fact fracqP x : fracq_spec x x (fracq x).
Proof.
case: x => n d /=; have [d_eq0 | d_neq0] := eqVneq d 0.
  by rewrite d_eq0 fracq0; constructor.
by rewrite {2}[(_, _)]valq_frac //; constructor; rewrite scalq_eq0.
Qed.

Lemma rat_eqE x y : (x == y) = (numq x == numq y) && (denq x == denq y).
Proof.
rewrite -val_eqE [val x]surjective_pairing [val y]surjective_pairing /=.
by rewrite xpair_eqE.
Qed.

Lemma sgr_denq x : sgr (denq x) = 1. Proof. by apply/eqP; rewrite sgr_cp0. Qed.

Lemma normr_denq x : `|denq x| = denq x. Proof. by rewrite gtr0_norm. Qed.

Lemma absz_denq x : `|denq x|%N = denq x :> int.
Proof. by rewrite abszE normr_denq. Qed.

Lemma rat_eq x y : (x == y) = (numq x * denq y == numq y * denq x).
Proof.
symmetry; rewrite rat_eqE andbC.
have [->|] /= := eqVneq (denq _); first by rewrite (inj_eq (mulIf _)).
apply: contraNF => /eqP hxy; rewrite -absz_denq -[eqbRHS]absz_denq.
rewrite eqz_nat /= eqn_dvd.
rewrite -(@Gauss_dvdr _ `|numq x|) 1?coprime_sym ?coprime_num_den // andbC.
rewrite -(@Gauss_dvdr _ `|numq y|) 1?coprime_sym ?coprime_num_den //.
by rewrite -!abszM hxy -{1}hxy !abszM !dvdn_mull ?dvdnn.
Qed.

Fact fracq_eq x y : x.2 != 0 -> y.2 != 0 ->
  (fracq x == fracq y) = (x.1 * y.2 == y.1 * x.2).
Proof.
case: fracqP=> //= u fx u_neq0 _; case: fracqP=> //= v fy v_neq0 _; symmetry.
rewrite [eqbRHS]mulrC mulrACA [eqbRHS]mulrACA.
by rewrite [denq _ * _]mulrC (inj_eq (mulfI _)) ?mulf_neq0 // rat_eq.
Qed.

Fact fracq_eq0 x : (fracq x == zeroq) = (x.1 == 0) || (x.2 == 0).
Proof.
move: x=> [n d] /=; have [->|d0] := eqVneq d 0.
  by rewrite fracq0 eqxx orbT.
by rewrite -[zeroq]valqK orbF fracq_eq ?d0 //= mulr1 mul0r.
Qed.

Fact fracqMM x n d : x != 0 -> fracq (x * n, x * d) = fracq (n, d).
Proof.
move=> x_neq0; apply/eqP.
have [->|d_neq0] := eqVneq d 0; first by rewrite mulr0 !fracq0.
by rewrite fracq_eq ?mulf_neq0 //= mulrCA mulrA.
Qed.

(* We "lock" the definition of addq, oppq, mulq and invq, using a match on    *)
(* the constructor Rat for both arguments, so that it may only be reduced     *)
(* when applied to explicit rationals. Since fracq is also "locked" in a      *)
(* similar way, fracq will not reduce to a Rat x xP unless it is also applied *)
(* to "enough" constructors. This preserves the reduction on gound elements   *)
(* while it suspends it when applied to at least one variable at the leaf of  *)
(* the arithmetic operation.                                                  *)
(* Moreover we optimize addition when one or both arguments are integers,     *)
(* in which case we presimplify the output, this shortens the size of the hnf *)
(* of terms of the form N%:Q when N is a concrete natural number.             *)
Definition addq_subdef (x y : int * int) :=
  let: (x1, x2) := x in
  let: (y1, y2) := y in
  match x2, y2 with
    | Posz 1, Posz 1   =>
        match x1, y1 with
        | Posz 0, _ => (y1, 1)
        | _, Posz 0 => (x1, 1)
        | Posz n, Posz 1 => (Posz n.+1, 1)
        | Posz 1, Posz n => (Posz n.+1, 1)
        | _, _ => (x1 + y1, 1)
        end
    | Posz 1, _  => (x1 * y2 + y1, y2)
    | _, Posz 1  => (x1 + y1 * x2, x2)
    | _, _       => (x1 * y2 + y1 * x2, x2 * y2)
  end.
Definition addq '(Rat x xP) '(Rat y yP) := fracq (addq_subdef x y).
Lemma addq_def x y : addq x y = fracq (addq_subdef (valq x) (valq y)).
Proof. by case: x; case: y. Qed.

Lemma addq_subdefE x y : addq_subdef x y = (x.1 * y.2 + y.1 * x.2, x.2 * y.2).
Proof.
case: x y => [x1 [[|[|x2]]|x2]] [y1 [[|[|y2]]|y2]]/=; rewrite ?Monoid.simpm//.
by case: x1 y1 => [[|[|m]]|m] [[|[|n]]|n]; rewrite ?Monoid.simpm// -PoszD addn1.
Qed.

Definition oppq_subdef (x : int * int) := (- x.1, x.2).
Definition oppq '(Rat x xP) := fracq (oppq_subdef x).
Definition oppq_def x : oppq x = fracq (oppq_subdef (valq x)).
Proof. by case: x. Qed.

Fact addq_subdefC : commutative addq_subdef.
Proof. by move=> x y; rewrite !addq_subdefE addrC [x.2 * _]mulrC. Qed.

Fact addq_subdefA : associative addq_subdef.
Proof.
move=> x y z; rewrite !addq_subdefE.
by rewrite !mulrA !mulrDl addrA ![_ * x.2]mulrC !mulrA.
Qed.

Fact addq_frac x y : x.2 != 0 -> y.2 != 0 ->
  (addq (fracq x) (fracq y)) = fracq (addq_subdef x y).
Proof.
case: fracqP => // u fx u_neq0 _; case: fracqP => // v fy v_neq0 _.
rewrite addq_def !addq_subdefE /=.
rewrite ![(_ * numq _) * _]mulrACA [(_ * denq _) * _]mulrACA.
by rewrite [v * _]mulrC -mulrDr fracqMM ?mulf_neq0.
Qed.

Fact ratzD : {morph ratz : x y / x + y >-> addq x y}.
Proof. by move=> x y; rewrite !ratz_frac addq_frac// addq_subdefE/= !mulr1. Qed.

Fact oppq_frac x : oppq (fracq x) = fracq (oppq_subdef x).
Proof.
rewrite /oppq_subdef; case: fracqP => /= [|u fx u_neq0].
  by rewrite fracq0.
by rewrite oppq_def -mulrN fracqMM.
Qed.

Fact ratzN : {morph ratz : x / - x >-> oppq x}.
Proof. by move=> x /=; rewrite !ratz_frac // /add /= !mulr1. Qed.

Fact addqC : commutative addq.
Proof. by move=> x y; rewrite !addq_def /= addq_subdefC. Qed.

Fact addqA : associative addq.
Proof.
move=> x y z; rewrite -[x]valqK -[y]valqK -[z]valqK.
by rewrite ?addq_frac ?addq_subdefA// ?addq_subdefE ?mulf_neq0 ?denq_neq0.
Qed.

Fact add0q : left_id zeroq addq.
Proof.
move=> x; rewrite -[x]valqK -[zeroq]valqK addq_frac ?denq_neq0 // !addq_subdefE.
by rewrite mul0r add0r mulr1 mul1r -surjective_pairing.
Qed.

Fact addNq : left_inverse (fracq (0, 1)) oppq addq.
Proof.
move=> x; rewrite -[x]valqK !(addq_frac, oppq_frac) ?denq_neq0 //.
rewrite !addq_subdefE /oppq_subdef //= mulNr addNr; apply/eqP.
by rewrite fracq_eq ?mulf_neq0 ?denq_neq0 //= !mul0r.
Qed.

HB.instance Definition _ := GRing.isZmodule.Build rat addqA addqC add0q addNq.

Definition mulq_subdef (x y : int * int) :=
  let: (x1, x2) := x in
  let: (y1, y2) := y in
  match x2, y2 with
    | Posz 1, Posz 1 => (x1 * y1, 1)
    | Posz 1, _      => (x1 * y1, y2)
    | _, Posz 1      => (x1 * y1, x2)
    | _, _           => (x1 * y1, x2 * y2)
  end.
Definition mulq '(Rat x xP) '(Rat y yP) := fracq (mulq_subdef x y).
Lemma mulq_def x y : mulq x y = fracq (mulq_subdef (valq x) (valq y)).
Proof. by case: x; case: y. Qed.

Lemma mulq_subdefE x y : mulq_subdef x y = (x.1 * y.1, x.2 * y.2).
Proof.
by case: x y => [x1 [[|[|x2]]|x2]] [y1 [[|[|y2]]|y2]]/=; rewrite ?Monoid.simpm.
Qed.

Fact mulq_subdefC : commutative mulq_subdef.
Proof. by move=> x y; rewrite !mulq_subdefE mulrC [_ * x.2]mulrC. Qed.

Fact mul_subdefA : associative mulq_subdef.
Proof. by move=> x y z; rewrite !mulq_subdefE !mulrA. Qed.

Definition invq_subdef (x : int * int) := (x.2, x.1).
Definition invq '(Rat x xP) := fracq (invq_subdef x).
Lemma invq_def x : invq x = fracq (invq_subdef (valq x)).
Proof. by case: x. Qed.

Fact mulq_frac x y : (mulq (fracq x) (fracq y)) = fracq (mulq_subdef x y).
Proof.
rewrite mulq_def !mulq_subdefE; case: (fracqP x) => /= [|u fx u_neq0].
  by rewrite !mul0r !mul1r fracq0 frac0q.
case: (fracqP y) => /= [|v fy v_neq0].
  by rewrite !mulr0 !mulr1 fracq0 frac0q.
by rewrite ![_ * (v * _)]mulrACA fracqMM ?mulf_neq0.
Qed.

Fact ratzM : {morph ratz : x y / x * y >-> mulq x y}.
Proof. by move=> x y /=; rewrite !ratz_frac //= !mulr1. Qed.

Fact invq_frac x :
  x.1 != 0 -> x.2 != 0 -> invq (fracq x) = fracq (invq_subdef x).
Proof. by rewrite invq_def; case: (fracqP x) => // k ? k0; rewrite fracqMM. Qed.

Fact mulqC : commutative mulq.
Proof. by move=> x y; rewrite !mulq_def mulq_subdefC. Qed.

Fact mulqA : associative mulq.
Proof.
by move=> x y z; rewrite -[x]valqK -[y]valqK -[z]valqK !mulq_frac mul_subdefA.
Qed.

Fact mul1q : left_id oneq mulq.
Proof.
move=> x; rewrite -[x]valqK -[oneq]valqK; rewrite mulq_frac !mulq_subdefE.
by rewrite !mul1r -surjective_pairing.
Qed.

Fact mulq_addl : left_distributive mulq addq.
Proof.
move=> x y z; rewrite -[x]valqK -[y]valqK -[z]valqK /=.
rewrite !(mulq_frac, addq_frac, mulq_subdefE, addq_subdefE) ?mulf_neq0 ?denq_neq0 //=.
apply/eqP; rewrite fracq_eq ?mulf_neq0 ?denq_neq0 //= !mulrDl; apply/eqP.
by rewrite !mulrA ![_ * (valq z).1]mulrC !mulrA ![_ * (valq x).2]mulrC !mulrA.
Qed.

Fact nonzero1q : oneq != zeroq. Proof. by []. Qed.

HB.instance Definition _ :=
  GRing.Zmodule_isComNzRing.Build rat mulqA mulqC mul1q mulq_addl nonzero1q.

Fact mulVq x : x != 0 -> mulq (invq x) x = 1.
Proof.
rewrite -[x]valqK -[0]valqK fracq_eq ?denq_neq0 //= mulr1 mul0r=> nx0.
rewrite !(mulq_frac, invq_frac, mulq_subdefE) ?denq_neq0 // -[1]valqK.
by apply/eqP; rewrite fracq_eq ?mulf_neq0 ?denq_neq0 //= mulr1 mul1r mulrC.
Qed.

Fact invq0 : invq 0 = 0. Proof. exact/eqP. Qed.

HB.instance Definition _ := GRing.ComNzRing_isField.Build rat mulVq invq0.

Lemma numq_eq0 x : (numq x == 0) = (x == 0).
Proof.
rewrite -[x]valqK fracq_eq0; case: fracqP=> /= [|k {}x k0].
  by rewrite eqxx orbT.
by rewrite !mulf_eq0 (negPf k0) /= denq_eq0 orbF.
Qed.

Notation "n %:Q" := ((n : int)%:~R : rat) : ring_scope.

#[global] Hint Resolve denq_neq0 denq_gt0 denq_ge0 : core.

Definition subq (x y : rat) : rat := (addq x (oppq y)).
Definition divq (x y : rat) : rat := (mulq x (invq y)).

Infix "+" := addq : rat_scope.
Notation "- x" := (oppq x) : rat_scope.
Infix "*" := mulq : rat_scope.
Notation "x ^-1" := (invq x) : rat_scope.
Infix "-" := subq : rat_scope.
Infix "/" := divq : rat_scope.

(* ratz should not be used, %:Q should be used instead *)
Lemma ratzE n : ratz n = n%:Q.
Proof.
elim: n=> [|n ihn|n ihn]; first by rewrite mulr0z ratz_frac.
  by rewrite intS mulrzDr ratzD ihn.
by rewrite intS opprD mulrzDr ratzD ihn.
Qed.

Lemma numq_int n : numq n%:Q = n. Proof. by rewrite -ratzE. Qed.
Lemma denq_int n : denq n%:Q = 1. Proof. by rewrite -ratzE. Qed.

Lemma rat0 : 0%:Q = 0. Proof. by []. Qed.
Lemma rat1 : 1%:Q = 1. Proof. by []. Qed.

Lemma numqN x : numq (- x) = - numq x.
Proof.
rewrite [- _]oppq_def/= num_fracq.
case: x => -[a b]; rewrite /numq/= => /andP[b_gt0].
rewrite /coprime => /eqP cab.
by rewrite lt_gtF ?gt_eqF // {2}abszN cab divn1 mulz_sign_abs.
Qed.

Lemma denqN x : denq (- x) = denq x.
Proof.
rewrite [- _]oppq_def den_fracq.
case: x => -[a b]; rewrite /denq/= => /andP[b_gt0].
by rewrite /coprime=> /eqP cab; rewrite gt_eqF // abszN cab divn1 gtz0_abs.
Qed.

(* Will be subsumed by pnatr_eq0 *)
Fact intq_eq0 n : (n%:~R == 0 :> rat) = (n == 0)%N.
Proof. by rewrite -ratzE /ratz rat_eqE/= /numq /denq/= eqxx andbT. Qed.

(* fracq should never appear, its canonical form is _%:Q / _%:Q *)
Lemma fracqE x : fracq x = x.1%:Q / x.2%:Q.
Proof.
move: x => [m n] /=; apply/val_inj; rewrite val_fracq/=.
case: eqVneq => //= [->|n_neq0]; first by rewrite rat0 invr0 mulr0.
rewrite -[m%:Q]valqK -[n%:Q]valqK.
rewrite [_^-1]invq_frac ?denq_neq0 ?numq_eq0 ?intq_eq0//=.
rewrite [X in valq X]mulq_frac val_fracq /invq_subdef !mulq_subdefE/=.
by rewrite -!/(numq _) -!/(denq _) !numq_int !denq_int mul1r mulr1 n_neq0.
Qed.

Lemma divq_num_den x : (numq x)%:Q / (denq x)%:Q = x.
Proof. by rewrite -{3}[x]valqK [valq _]surjective_pairing /= fracqE. Qed.

Variant divq_spec (n d : int) : int -> int -> rat -> Type :=
| DivqSpecN of d = 0 : divq_spec n d n 0 0
| DivqSpecP k x of k != 0 : divq_spec n d (k * numq x) (k * denq x) x.

(* replaces fracqP *)
Lemma divqP n d : divq_spec n d n d (n%:Q / d%:Q).
Proof.
set x := (n, d); rewrite -[n]/x.1 -[d]/x.2 -fracqE.
by case: fracqP => [_|k fx k_neq0] /=; constructor.
Qed.

Variant rat_spec (* (x : rat) *) : rat -> int -> int -> Type :=
  Rat_spec (n : int) (d : nat)  & coprime `|n| d.+1
  : rat_spec (* x  *) (n%:Q / d.+1%:Q) n d.+1.

Lemma ratP x : rat_spec x (numq x) (denq x).
Proof.
rewrite -{1}[x](divq_num_den); case hd: denq => [p|n].
  have: 0 < p%:Z by rewrite -hd denq_gt0.
  case: p hd=> //= n hd; constructor; rewrite -?hd ?divq_num_den //.
  by rewrite -[n.+1]/`|n.+1|%N -hd coprime_num_den.
by move: (denq_gt0 x); rewrite hd.
Qed.

Lemma coprimeq_num n d : coprime `|n| `|d| -> numq (n%:~R / d%:~R) = sgr d * n.
Proof.
move=> cnd /=; have <- := fracqE (n, d).
rewrite num_fracq/= (eqP (cnd : _ == 1)) divn1.
have [|d_gt0|d_lt0] := sgrP d;
by rewrite (mul0r, mul1r, mulN1r) //= ?[_ ^ _]signrN ?mulNr mulz_sign_abs.
Qed.

Lemma coprimeq_den n d :
  coprime `|n| `|d| -> denq (n%:~R / d%:~R) = (if d == 0 then 1 else `|d|).
Proof.
move=> cnd; have <- := fracqE (n, d).
by rewrite den_fracq/= (eqP (cnd : _ == 1)) divn1; case: d {cnd}; case.
Qed.

Lemma denqVz (i : int) : i != 0 -> denq (i%:~R^-1) = `|i|.
Proof.
move=> h; rewrite -div1r -[1]/(1%:~R).
by rewrite coprimeq_den /= ?coprime1n // (negPf h).
Qed.

Lemma numqE x : (numq x)%:~R = x * (denq x)%:~R.
Proof. by rewrite -{2}[x]divq_num_den divfK // intq_eq0 denq_eq0. Qed.

Lemma denqP x : {d | denq x = d.+1}.
Proof. by rewrite /denq; case: x => [[_ [[|d]|]] //= _]; exists d. Qed.

Definition normq '(Rat x _) : rat := `|x.1|%:~R / (x.2)%:~R.
Definition le_rat '(Rat x _) '(Rat y _) := x.1 * y.2 <= y.1 * x.2.
Definition lt_rat '(Rat x _) '(Rat y _) := x.1 * y.2 < y.1 * x.2.

Lemma normqE x : normq x = `|numq x|%:~R / (denq x)%:~R.
Proof. by case: x. Qed.

Lemma le_ratE x y : le_rat x y = (numq x * denq y <= numq y * denq x).
Proof. by case: x; case: y. Qed.

Lemma lt_ratE x y : lt_rat x y = (numq x * denq y < numq y * denq x).
Proof. by case: x; case: y. Qed.

Lemma gt_rat0 x : lt_rat 0 x = (0 < numq x).
Proof. by rewrite lt_ratE mul0r mulr1. Qed.

Lemma lt_rat0 x : lt_rat x 0 = (numq x < 0).
Proof. by rewrite lt_ratE mul0r mulr1. Qed.

Lemma ge_rat0 x : le_rat 0 x = (0 <= numq x).
Proof. by rewrite le_ratE mul0r mulr1. Qed.

Lemma le_rat0 x : le_rat x 0 = (numq x <= 0).
Proof. by rewrite le_ratE mul0r mulr1. Qed.

Fact le_rat0D x y : le_rat 0 x -> le_rat 0 y -> le_rat 0 (x + y).
Proof.
rewrite !ge_rat0 => hnx hny.
have hxy: (0 <= numq x * denq y + numq y * denq x).
  by rewrite addr_ge0 ?mulr_ge0.
rewrite [_ + _]addq_def /numq /= -!/(denq _) ?mulf_eq0 ?denq_eq0.
rewrite val_fracq/=; case: ifP => //=.
by rewrite ?addq_subdefE !mulr_ge0// !le_gtF ?mulr_ge0 ?denq_ge0//=.
Qed.

Fact le_rat0M x y : le_rat 0 x -> le_rat 0 y -> le_rat 0 (x * y).
Proof.
rewrite !ge_rat0 => hnx hny.
have hxy: (0 <= numq x * denq y + numq y * denq x).
  by rewrite addr_ge0 ?mulr_ge0.
rewrite [_ * _]mulq_def /numq /= -!/(denq _) ?mulf_eq0 ?denq_eq0.
rewrite val_fracq/=; case: ifP => //=.
by rewrite ?mulq_subdefE !mulr_ge0// !le_gtF ?mulr_ge0 ?denq_ge0//=.
Qed.

Fact le_rat0_anti x : le_rat 0 x -> le_rat x 0 -> x = 0.
Proof.
by move=> hx hy; apply/eqP; rewrite -numq_eq0 eq_le -ge_rat0 -le_rat0 hx hy.
Qed.

Lemma sgr_numq_div (n d : int) : sgr (numq (n%:Q / d%:Q)) = sgr n * sgr d.
Proof.
set x := (n, d); rewrite -[n]/x.1 -[d]/x.2 -fracqE.
case: fracqP => [|k fx k_neq0] /=; first by rewrite mulr0.
by rewrite !sgrM  mulrACA -expr2 sqr_sg k_neq0 sgr_denq mulr1 mul1r.
Qed.

Fact subq_ge0 x y : le_rat 0 (y - x) = le_rat x y.
Proof.
symmetry; rewrite ge_rat0 !le_ratE -subr_ge0.
case: ratP => nx dx cndx; case: ratP => ny dy cndy.
rewrite -!mulNr addf_div ?intq_eq0 // !mulNr -!rmorphM -rmorphB /=.
symmetry; rewrite !leNgt -sgr_cp0 sgr_numq_div mulrC gtr0_sg //.
by rewrite mul1r sgr_cp0.
Qed.

Fact le_rat_total : total le_rat.
Proof. by move=> x y; rewrite !le_ratE; apply: le_total. Qed.

Fact numq_sign_mul (b : bool) x : numq ((-1) ^+ b * x) = (-1) ^+ b * numq x.
Proof. by case: b; rewrite ?(mul1r, mulN1r) // numqN. Qed.

Fact numq_div_lt0 n d : n != 0 -> d != 0 ->
  (numq (n%:~R / d%:~R) < 0)%R = (n < 0)%R (+) (d < 0)%R.
Proof.
move=> n0 d0; rewrite -sgr_cp0 sgr_numq_div !sgr_def n0 d0.
by rewrite !mulr1n -signr_addb; case: (_ (+) _).
Qed.

Lemma normr_num_div n d : `|numq (n%:~R / d%:~R)| = numq (`|n|%:~R / `|d|%:~R).
Proof.
rewrite (normrEsg n) (normrEsg d) !rmorphM /= invfM mulrACA !sgr_def.
have [->|n_neq0] := eqVneq; first by rewrite mul0r mulr0.
have [->|d_neq0] := eqVneq; first by rewrite invr0 !mulr0.
rewrite !intr_sign invr_sign -signr_addb numq_sign_mul -numq_div_lt0 //.
by apply: (canRL (signrMK _)); rewrite mulz_sign_abs.
Qed.

Fact norm_ratN x : normq (- x) = normq x.
Proof. by rewrite !normqE numqN denqN normrN. Qed.

Fact ge_rat0_norm x : le_rat 0 x -> normq x = x.
Proof.
rewrite ge_rat0; case: ratP=> [] // n d cnd n_ge0.
by rewrite normqE /= normr_num_div ?ger0_norm // divq_num_den.
Qed.

Fact lt_rat_def x y : (lt_rat x y) = (y != x) && (le_rat x y).
Proof. by rewrite lt_ratE le_ratE lt_def rat_eq. Qed.

HB.instance Definition _ :=
   Num.IntegralDomain_isLeReal.Build rat le_rat0D le_rat0M le_rat0_anti
     subq_ge0 (@le_rat_total 0) norm_ratN ge_rat0_norm lt_rat_def.

Lemma numq_ge0 x : (0 <= numq x) = (0 <= x).
Proof.
by case: ratP => n d cnd; rewrite ?pmulr_lge0 ?invr_gt0 (ler0z, ltr0z).
Qed.

Lemma numq_le0 x : (numq x <= 0) = (x <= 0).
Proof. by rewrite -oppr_ge0 -numqN numq_ge0 oppr_ge0. Qed.

Lemma numq_gt0 x : (0 < numq x) = (0 < x).
Proof. by rewrite !ltNge numq_le0. Qed.

Lemma numq_lt0 x : (numq x < 0) = (x < 0).
Proof. by rewrite !ltNge numq_ge0. Qed.

Lemma sgr_numq x : sgz (numq x) = sgz x.
Proof.
apply/eqP; case: (sgzP x); rewrite sgz_cp0 ?(numq_gt0, numq_lt0) //.
by move->.
Qed.

Lemma denq_mulr_sign (b : bool) x : denq ((-1) ^+ b * x) = denq x.
Proof. by case: b; rewrite ?(mul1r, mulN1r) // denqN. Qed.

Lemma denq_norm x : denq `|x| = denq x.
Proof. by rewrite normrEsign denq_mulr_sign. Qed.

Module ratArchimedean.
Section ratArchimedean.

Implicit Types x : rat.

Let trunc x : nat := if 0 <= x then (`|numq x| %/ `|denq x|)%N else 0%N.

Lemma truncP x :
  if 0 <= x then (trunc x)%:R <= x < (trunc x).+1%:R else trunc x == 0%N.
Proof.
rewrite /trunc -numq_ge0; case: (ratP x) => -[] //= n d _.
rewrite ler_pdivlMr ?ltr_pdivrMr ?ltr0z // -!natrM ler_nat ltr_nat.
by rewrite leq_trunc_div ltn_ceil.
Qed.

Let is_nat x := (0 <= x) && (denq x == 1).

Lemma is_natE x : is_nat x = ((trunc x)%:R == x).
Proof.
rewrite /is_nat /trunc -numq_ge0 !rat_eq; case: (ratP x) => -[] //= n d pnd.
rewrite pmulrn numq_int denq_int mulr1 -PoszM !eqz_nat -dvdn_eq.
apply/eqP/idP => [->|/dvdnP[k nE]] //.
by move/eqP: pnd; rewrite nE gcdnC gcdnMl.
Qed.

Lemma is_intE x : (denq x == 1) = is_nat x || is_nat (- x).
Proof. by rewrite /is_nat denqN oppr_ge0 -andb_orl le_total. Qed.

End ratArchimedean.
End ratArchimedean.

HB.instance Definition _ := Num.NumDomain_isArchimedean.Build rat
  ratArchimedean.truncP ratArchimedean.is_natE ratArchimedean.is_intE.

Lemma Qint_def (x : rat) : (x \is a Num.int) = (denq x == 1). Proof. by []. Qed.

Lemma numqK : {in Num.int, cancel (fun x => numq x) intr}.
Proof. by move=> _ /intrP [x ->]; rewrite numq_int. Qed.

Lemma natq_div m n : n %| m -> (m %/ n)%:R = m%:R / n%:R :> rat.
Proof. exact/pchar0_natf_div/pchar_num. Qed.

Section InRing.

Variable R : unitRingType.

Definition ratr x : R := (numq x)%:~R / (denq x)%:~R.

Lemma ratr_int z : ratr z%:~R = z%:~R.
Proof. by rewrite /ratr numq_int denq_int divr1. Qed.

Lemma ratr_nat n : ratr n%:R = n%:R.
Proof. exact: ratr_int n. Qed.

Lemma rpred_rat (S : divringClosed R) a : ratr a \in S.
Proof. by rewrite rpred_div ?rpred_int. Qed.

End InRing.

Section Fmorph.

Implicit Type rR : unitRingType.

Lemma fmorph_rat (aR : fieldType) rR (f : {rmorphism aR -> rR}) a :
  f (ratr _ a) = ratr _ a.
Proof. by rewrite fmorph_div !rmorph_int. Qed.

Lemma fmorph_eq_rat rR (f : {rmorphism rat -> rR}) : f =1 ratr _.
Proof. by move=> a; rewrite -{1}[a]divq_num_den fmorph_div !rmorph_int. Qed.

End Fmorph.

Section Linear.

Implicit Types (U V : lmodType rat) (A B : lalgType rat).

Lemma rat_linear U V (f : U -> V) : additive f -> scalable f.
Proof.
move=> fB a u.
pose aM := GRing.isAdditive.Build U V f fB.
pose phi : {additive U -> V} := HB.pack f aM.
rewrite -[f]/(phi : _ -> _) -{2}[a]divq_num_den mulrC -scalerA.
apply: canRL (scalerK _) _; first by rewrite intr_eq0 denq_neq0.
rewrite 2!scaler_int -3!raddfMz /=.
by rewrite -scalerMzr scalerMzl -mulrzr -numqE scaler_int.
Qed.

End Linear.

Section InPrealField.

Variable F : numFieldType.

Fact ratr_is_additive : additive (@ratr F).
Proof.
have injZtoQ: @injective rat int intr by apply: intr_inj.
have nz_den x: (denq x)%:~R != 0 :> F by rewrite intr_eq0 denq_eq0.
move=> x y.
apply: (canLR (mulfK (nz_den _))); apply: (mulIf (nz_den x)).
rewrite mulrAC mulrBl divfK ?nz_den // mulrAC -!rmorphM.
apply: (mulIf (nz_den y)); rewrite mulrAC mulrBl divfK ?nz_den //.
rewrite -!(rmorphM, rmorphB); congr _%:~R; apply: injZtoQ.
rewrite !(rmorphM, rmorphB) /= [_ - _]lock /= -lock !numqE.
by rewrite (mulrAC y) -!mulrBl -mulrA mulrAC !mulrA.
Qed.

Fact ratr_is_multiplicative : multiplicative (@ratr F).
Proof.
have injZtoQ: @injective rat int intr by apply: intr_inj.
have nz_den x: (denq x)%:~R != 0 :> F by rewrite intr_eq0 denq_eq0.
split=> [x y|]; last by rewrite /ratr divr1.
rewrite /ratr mulrC mulrAC; apply: canLR (mulKf (nz_den _)) _; rewrite !mulrA.
do 2!apply: canRL (mulfK (nz_den _)) _; rewrite -!rmorphM; congr _%:~R.
apply: injZtoQ; rewrite !rmorphM [x * y]lock /= !numqE -lock.
by rewrite -!mulrA mulrA mulrCA -!mulrA (mulrCA y).
Qed.

HB.instance Definition _ := GRing.isAdditive.Build rat F (@ratr F)
  ratr_is_additive.
HB.instance Definition _ := GRing.isMultiplicative.Build rat F (@ratr F)
  ratr_is_multiplicative.

Lemma ler_rat : {mono (@ratr F) : x y / x <= y}.
Proof.
move=> x y /=; case: (ratP x) => nx dx cndx; case: (ratP y) => ny dy cndy.
rewrite !fmorph_div /= !ratr_int !ler_pdivlMr ?ltr0z //.
by rewrite ![_ / _ * _]mulrAC !ler_pdivrMr ?ltr0z // -!rmorphM /= !ler_int.
Qed.

Lemma ltr_rat : {mono (@ratr F) : x y / x < y}.
Proof. exact: leW_mono ler_rat. Qed.

Lemma ler0q x : (0 <= ratr F x) = (0 <= x).
Proof. by rewrite (_ : 0 = ratr F 0) ?ler_rat ?rmorph0. Qed.

Lemma lerq0 x : (ratr F x <= 0) = (x <= 0).
Proof. by rewrite (_ : 0 = ratr F 0) ?ler_rat ?rmorph0. Qed.

Lemma ltr0q x : (0 < ratr F x) = (0 < x).
Proof. by rewrite (_ : 0 = ratr F 0) ?ltr_rat ?rmorph0. Qed.

Lemma ltrq0 x : (ratr F x < 0) = (x < 0).
Proof. by rewrite (_ : 0 = ratr F 0) ?ltr_rat ?rmorph0. Qed.

Lemma ratr_sg x : ratr F (sgr x) = sgr (ratr F x).
Proof. by rewrite !sgr_def fmorph_eq0 ltrq0 rmorphMn /= rmorph_sign. Qed.

Lemma ratr_norm x : ratr F `|x| = `|ratr F x|.
Proof.
by rewrite {2}[x]numEsign rmorphMsign normrMsign [`|ratr F _|]ger0_norm ?ler0q.
Qed.

Lemma minr_rat : {morph ratr F : x y / Num.min x y}.
Proof. by move=> x y; rewrite !minEle ler_rat; case: leP. Qed.

Lemma maxr_rat : {morph ratr F : x y / Num.max x y}.
Proof. by move=> x y; rewrite !maxEle ler_rat; case: leP. Qed.

End InPrealField.

Section InParchiField.

Variable F : archiNumFieldType.

Lemma floor_rat : {mono (@ratr F) : x / Num.floor x}.
Proof.
move=> x; apply: floor_def; apply/andP; split.
- by rewrite -ratr_int ler_rat ge_floor.
- by rewrite -ratr_int ltr_rat lt_succ_floor.
Qed.

Lemma ceil_rat : {mono (@ratr F) : x / Num.ceil x}.
Proof. by move=> x; rewrite /Num.ceil -rmorphN floor_rat. Qed.

End InParchiField.

Arguments ratr {R}.

(* Connecting rationals to the ring and field tactics *)

Ltac rat_to_ring :=
  rewrite -?[0%Q]/(0 : rat)%R -?[1%Q]/(1 : rat)%R
          -?[(_ - _)%Q]/(_ - _ : rat)%R -?[(_ / _)%Q]/(_ / _ : rat)%R
          -?[(_ + _)%Q]/(_ + _ : rat)%R -?[(_ * _)%Q]/(_ * _ : rat)%R
          -?[(- _)%Q]/(- _ : rat)%R -?[(_ ^-1)%Q]/(_ ^-1 : rat)%R /=.

Ltac ring_to_rat :=
  rewrite -?[0%R]/0%Q -?[1%R]/1%Q
          -?[(_ - _)%R]/(_ - _)%Q -?[(_ / _)%R]/(_ / _)%Q
          -?[(_ + _)%R]/(_ + _)%Q -?[(_ * _)%R]/(_ * _)%Q
          -?[(- _)%R]/(- _)%Q -?[(_ ^-1)%R]/(_ ^-1)%Q /=.

(* Pretty printing or normal element of rat. *)
Notation "[ 'rat' x // y ]" := (@Rat (x, y) _) (only printing) : ring_scope.

(* For debugging purposes we provide the parsable version *)
Notation "[ 'rat' x // y ]" :=
  (@Rat (x : int, y : int) (fracq_subproof (x : int, y : int))) : ring_scope.

(* A specialization of vm_compute rewrite rule for pattern _%:Q *)
Lemma rat_vm_compute n (x : rat) : vm_compute_eq n%:Q x -> n%:Q = x.
Proof. exact. Qed.

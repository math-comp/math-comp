(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice.
From mathcomp Require Import order interval ssralg.
From mathcomp Require Import orderedzmod numdomain numfield ssrint.

(**md**************************************************************************)
(* # Numbers within an interval                                               *)
(*                                                                            *)
(* This file develops tools to make the manipulation of numbers within        *)
(* a known interval easier, thanks to canonical structures. This adds types   *)
(* like {itv R & `[a, b]}, a notation e%:itv that infers an enclosing         *)
(* interval for expression e according to existing canonical instances and    *)
(* %:num to cast back from type {itv R & i} to R.                             *)
(* For instance, for x : {i01 R}, we have (1 - x%:num)%:itv : {i01 R}         *)
(* automatically inferred.                                                    *)
(*                                                                            *)
(* ## types for values within known interval                                  *)
(*                                                                            *)
(* ```                                                                        *)
(*   {itv R & i} == generic type of values in interval i : interval int       *)
(*                  See interval.v for notations that can be used for i.      *)
(*                  R must have a numDomainType structure. This type is shown *)
(*                  to be a porderType.                                       *)
(*       {i01 R} := {itv R & `[0, 1]}                                         *)
(*                  Allows to solve automatically goals of the form x >= 0    *)
(*                  and x <= 1 when x is canonically a {i01 R}.               *)
(*                  {i01 R} is canonically stable by common operations.       *)
(*    {posnum R} := {itv R & `]0, +oo[)                                       *)
(*    {nonneg R} := {itv R & `[0, +oo[)                                       *)
(* ```                                                                        *)
(*                                                                            *)
(* ## casts from/to values within known interval                              *)
(*                                                                            *)
(* Explicit casts of x to some {itv R & i} according to existing canonical    *)
(* instances:                                                                 *)
(* ```                                                                        *)
(*        x%:itv == cast to the most precisely known {itv R & i}              *)
(*        x%:i01 == cast to {i01 R}, or fail                                  *)
(*        x%:pos == cast to {posnum R}, or fail                               *)
(*        x%:nng == cast to {nonneg R}, or fail                               *)
(* ```                                                                        *)
(*                                                                            *)
(* Explicit casts of x from some {itv R & i} to R:                            *)
(* ```                                                                        *)
(*        x%:num == cast from {itv R & i}                                     *)
(*     x%:posnum == cast from {posnum R}                                      *)
(*     x%:nngnum == cast from {nonneg R}                                      *)
(* ```                                                                        *)
(*                                                                            *)
(* ## sign proofs                                                             *)
(*                                                                            *)
(* ```                                                                        *)
(*    [itv of x] == proof that x is in the interval inferred by x%:itv        *)
(*    [gt0 of x] == proof that x > 0                                          *)
(*    [lt0 of x] == proof that x < 0                                          *)
(*    [ge0 of x] == proof that x >= 0                                         *)
(*    [le0 of x] == proof that x <= 0                                         *)
(*   [cmp0 of x] == proof that 0 >=< x                                        *)
(*   [neq0 of x] == proof that x != 0                                         *)
(* ```                                                                        *)
(*                                                                            *)
(* ## constructors                                                            *)
(*                                                                            *)
(* ```                                                                        *)
(* ItvNum xr lx xu == builds a {itv R & i} from proofs xr : x \in Num.real,   *)
(*                    lx : map_itv_bound (Itv.num_sem R) l <= BLeft x         *)
(*                    xu : BRight x <= map_itv_bound (Itv.num_sem R) u        *)
(*                    where x : R with R : numDomainType                      *)
(*                    and l u : itv_bound int                                 *)
(*   ItvReal lx xu == builds a {itv R & i} from proofs                        *)
(*                    lx : map_itv_bound (Itv.num_sem R) l <= BLeft x         *)
(*                    xu : BRight x <= map_itv_bound (Itv.num_sem R) u        *)
(*                    where x : R with R : realDomainType                     *)
(*                    and l u : itv_bound int                                 *)
(*     Itv01 x0 x1 == builds a {i01 R} from proofs x0 : 0 <= x and x1 : x <= 1*)
(*                    where x : R with R : numDomainType                      *)
(*       PosNum x0 == builds a {posnum R} from a proof x0 : x > 0 where x : R *)
(*       NngNum x0 == builds a {posnum R} from a proof x0 : x >= 0 where x : R*)
(* ```                                                                        *)
(*                                                                            *)
(* A number of canonical instances are provided for common operations, if     *)
(* your favorite operator is missing, look below for examples on how to add   *)
(* the appropriate Canonical.                                                 *)
(* Also note that all provided instances aren't necessarily optimal,          *)
(* improvements welcome!                                                      *)
(* Canonical instances are also provided according to types, as a             *)
(* fallback when no known operator appears in the expression. Look to top_typ *)
(* below for an example on how to add your favorite type.                     *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "{ 'itv' R & i }"
  (R at level 200, i at level 200, format "{ 'itv'  R  &  i }").
Reserved Notation "{ 'i01' R }"
  (R at level 200, format "{ 'i01'  R }").
Reserved Notation "{ 'posnum' R }" (format "{ 'posnum'  R }").
Reserved Notation "{ 'nonneg' R }" (format "{ 'nonneg'  R }").

Reserved Notation "x %:itv" (format "x %:itv").
Reserved Notation "x %:i01" (format "x %:i01").
Reserved Notation "x %:pos" (format "x %:pos").
Reserved Notation "x %:nng" (format "x %:nng").
Reserved Notation "x %:inum" (format "x %:inum").
Reserved Notation "x %:num" (format "x %:num").
Reserved Notation "x %:posnum" (format "x %:posnum").
Reserved Notation "x %:nngnum" (format "x %:nngnum").

Reserved Notation "[ 'itv' 'of' x ]" (format "[ 'itv' 'of'  x ]").
Reserved Notation "[ 'gt0' 'of' x ]" (format "[ 'gt0' 'of'  x ]").
Reserved Notation "[ 'lt0' 'of' x ]" (format "[ 'lt0' 'of'  x ]").
Reserved Notation "[ 'ge0' 'of' x ]" (format "[ 'ge0' 'of'  x ]").
Reserved Notation "[ 'le0' 'of' x ]" (format "[ 'le0' 'of'  x ]").
Reserved Notation "[ 'cmp0' 'of' x ]" (format "[ 'cmp0' 'of'  x ]").
Reserved Notation "[ 'neq0' 'of' x ]" (format "[ 'neq0' 'of'  x ]").

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory Order.Syntax.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope order_scope.

Definition map_itv_bound S T (f : S -> T) (b : itv_bound S) : itv_bound T :=
  match b with
  | BSide b x => BSide b (f x)
  | BInfty b => BInfty _ b
  end.

Lemma map_itv_bound_comp S T U (f : T -> S) (g : U -> T) (b : itv_bound U) :
  map_itv_bound (f \o g) b = map_itv_bound f (map_itv_bound g b).
Proof. by case: b. Qed.

Definition map_itv S T (f : S -> T) (i : interval S) : interval T :=
  let 'Interval l u := i in Interval (map_itv_bound f l) (map_itv_bound f u).

Lemma map_itv_comp S T U (f : T -> S) (g : U -> T) (i : interval U) :
  map_itv (f \o g) i = map_itv f (map_itv g i).
Proof. by case: i => l u /=; rewrite -!map_itv_bound_comp. Qed.

(* First, the interval arithmetic operations we will later use *)
Module IntItv.
Implicit Types (b : itv_bound int) (i j : interval int).

Definition opp_bound b :=
  match b with
  | BSide b x => BSide (~~ b) (intZmod.oppz x)
  | BInfty b => BInfty _ (~~ b)
  end.

Lemma opp_bound_ge0 b : (BLeft 0%R <= opp_bound b)%O = (b <= BRight 0%R)%O.
Proof. by case: b => [[] b | []//]; rewrite /= !bnd_simp oppr_ge0. Qed.

Lemma opp_bound_gt0 b : (BRight 0%R <= opp_bound b)%O = (b <= BLeft 0%R)%O.
Proof.
by case: b => [[] b | []//]; rewrite /= !bnd_simp ?oppr_ge0 ?oppr_gt0.
Qed.

Definition opp i :=
  let: Interval l u := i in Interval (opp_bound u) (opp_bound l).
Arguments opp /.

Definition add_boundl b1 b2 :=
  match b1, b2 with
  | BSide b1 x1, BSide b2 x2 => BSide (b1 && b2) (intZmod.addz x1 x2)
  | _, _ => BInfty _ true
  end.

Definition add_boundr b1 b2 :=
  match b1, b2 with
  | BSide b1 x1, BSide b2 x2 => BSide (b1 || b2) (intZmod.addz x1 x2)
  | _, _ => BInfty _ false
  end.

Definition add i1 i2 :=
  let: Interval l1 u1 := i1 in let: Interval l2 u2 := i2 in
  Interval (add_boundl l1 l2) (add_boundr u1 u2).
Arguments add /.

Variant signb := EqZero | NonNeg | NonPos.

Definition sign_boundl b :=
  let: b0 := BLeft 0%Z in
  if b == b0 then EqZero else if (b <= b0)%O then NonPos else NonNeg.

Definition sign_boundr b :=
  let: b0 := BRight 0%Z in
  if b == b0 then EqZero else if (b <= b0)%O then NonPos else NonNeg.

Variant signi := Known of signb | Unknown | Empty.

Definition sign i : signi :=
  let: Interval l u := i in
  match sign_boundl l, sign_boundr u with
  | EqZero, NonPos
  | NonNeg, EqZero
  | NonNeg, NonPos => Empty
  | EqZero, EqZero => Known EqZero
  | NonPos, EqZero
  | NonPos, NonPos => Known NonPos
  | EqZero, NonNeg
  | NonNeg, NonNeg => Known NonNeg
  | NonPos, NonNeg => Unknown
  end.

Definition mul_boundl b1 b2 :=
  match b1, b2 with
  | BInfty _, _
  | _, BInfty _
  | BLeft 0%Z, _
  | _, BLeft 0%Z => BLeft 0%Z
  | BSide b1 x1, BSide b2 x2 => BSide (b1 && b2) (intRing.mulz x1 x2)
  end.

Definition mul_boundr b1 b2 :=
  match b1, b2 with
  | BLeft 0%Z, _
  | _, BLeft 0%Z => BLeft 0%Z
  | BRight 0%Z, _
  | _, BRight 0%Z => BRight 0%Z
  | BSide b1 x1, BSide b2 x2 => BSide (b1 || b2) (intRing.mulz x1 x2)
  | _, BInfty _
  | BInfty _, _ => +oo%O
  end.

Lemma mul_boundrC b1 b2 : mul_boundr b1 b2 = mul_boundr b2 b1.
Proof.
by move: b1 b2 => [[] [[|?]|?] | []] [[] [[|?]|?] | []] //=; rewrite mulnC.
Qed.

Lemma mul_boundr_gt0 b1 b2 :
  (BRight 0%Z <= b1 -> BRight 0%Z <= b2 -> BRight 0%Z <= mul_boundr b1 b2)%O.
Proof.
case: b1 b2 => [b1b b1 | []] [b2b b2 | []]//=.
- by case: b1b b2b => -[]; case: b1 b2 => [[|b1] | b1] [[|b2] | b2].
- by case: b1b b1 => -[[] |].
- by case: b2b b2 => -[[] |].
Qed.

Definition mul i1 i2 :=
  let: Interval l1 u1 := i1 in let: Interval l2 u2 := i2 in
  let: opp := opp_bound in
  let: mull := mul_boundl in let: mulr := mul_boundr in
  match sign i1, sign i2 with
  | Empty, _ | _, Empty => `[1, 0]
  | Known EqZero, _ | _, Known EqZero => `[0, 0]
  | Known NonNeg, Known NonNeg =>
      Interval (mull l1 l2) (mulr u1 u2)
  | Known NonPos, Known NonPos =>
      Interval (mull (opp u1) (opp u2)) (mulr (opp l1) (opp l2))
  | Known NonNeg, Known NonPos =>
      Interval (opp (mulr u1 (opp l2))) (opp (mull l1 (opp u2)))
  | Known NonPos, Known NonNeg =>
      Interval (opp (mulr (opp l1) u2)) (opp (mull (opp u1) l2))
  | Known NonNeg, Unknown =>
      Interval (opp (mulr u1 (opp l2))) (mulr u1 u2)
  | Known NonPos, Unknown =>
      Interval (opp (mulr (opp l1) u2)) (mulr (opp l1) (opp l2))
  | Unknown, Known NonNeg =>
      Interval (opp (mulr (opp l1) u2)) (mulr u1 u2)
  | Unknown, Known NonPos =>
      Interval (opp (mulr u1 (opp l2))) (mulr (opp l1) (opp l2))
  | Unknown, Unknown =>
      Interval
        (Order.min (opp (mulr (opp l1) u2)) (opp (mulr u1 (opp l2))))
        (Order.max (mulr (opp l1) (opp l2)) (mulr u1 u2))
  end.
Arguments mul /.

Definition min i j :=
  let: Interval li ui := i in let: Interval lj uj := j in
  Interval (Order.min li lj) (Order.min ui uj).
Arguments min /.

Definition max i j :=
  let: Interval li ui := i in let: Interval lj uj := j in
  Interval (Order.max li lj) (Order.max ui uj).
Arguments max /.

Definition keep_nonneg_bound b :=
  match b with
  | BSide _ (Posz _) => BLeft 0%Z
  | BSide _ (Negz _) => -oo%O
  | BInfty _ => -oo%O
  end.
Arguments keep_nonneg_bound /.

Definition keep_pos_bound b :=
  match b with
  | BSide b 0%Z => BSide b 0%Z
  | BSide _ (Posz (S _)) => BRight 0%Z
  | BSide _ (Negz _) => -oo
  | BInfty _ => -oo
  end.
Arguments keep_pos_bound /.

Definition keep_nonpos_bound b :=
  match b with
  | BSide _ (Negz _) | BSide _ (Posz 0) => BRight 0%Z
  | BSide _ (Posz (S _)) => +oo%O
  | BInfty _ => +oo%O
  end.
Arguments keep_nonpos_bound /.

Definition keep_neg_bound b :=
  match b with
  | BSide b 0%Z => BSide b 0%Z
  | BSide _ (Negz _) => BLeft 0%Z
  | BSide _ (Posz _) => +oo
  | BInfty _ => +oo
  end.
Arguments keep_neg_bound /.

Definition inv i :=
  let: Interval l u := i in
  Interval (keep_pos_bound l) (keep_neg_bound u).
Arguments inv /.

Definition exprn_le1_bound b1 b2 :=
  if b2 isn't BSide _ 1%Z then +oo
  else if (BLeft (-1)%Z <= b1)%O then BRight 1%Z else +oo.
Arguments exprn_le1_bound /.

Definition exprn i :=
  let: Interval l u := i in
  Interval (keep_pos_bound l) (exprn_le1_bound l u).
Arguments exprn /.

Definition exprz i1 i2 :=
  let: Interval l2 _ := i2 in
  if l2 is BSide _ (Posz _) then exprn i1 else
    let: Interval l u := i1 in
    Interval (keep_pos_bound l) +oo.
Arguments exprz /.

Definition keep_sign i :=
  let: Interval l u := i in
  Interval (keep_nonneg_bound l) (keep_nonpos_bound u).

(* used in ereal.v *)
Definition keep_nonpos i :=
  let 'Interval l u := i in
  Interval -oo%O (keep_nonpos_bound u).
Arguments keep_nonpos /.

(* used in ereal.v *)
Definition keep_nonneg i :=
  let 'Interval l u := i in
  Interval (keep_nonneg_bound l) +oo%O.
Arguments keep_nonneg /.

End IntItv.

Module Itv.

Variant t := Top | Real of interval int.

Definition sub (x y : t) :=
  match x, y with
  | _, Top => true
  | Top, Real _ => false
  | Real xi, Real yi => subitv xi yi
  end.

Section Itv.
Context T (sem : interval int -> T -> bool).

Definition spec (i : t) (x : T) := if i is Real i then sem i x else true.

Record def (i : t) := Def {
  r : T;
  #[canonical=no]
  P : spec i r
}.

End Itv.

Record typ i := Typ {
  sort : Type;
  #[canonical=no]
  sort_sem : interval int -> sort -> bool;
  #[canonical=no]
  allP : forall x : sort, spec sort_sem i x
}.

Definition mk {T f} i x P : @def T f i := @Def T f i x P.

Definition from {T f i} {x : @def T f i} (phx : phantom T (r x)) := x.

Definition fromP {T f i} {x : @def T f i} (phx : phantom T (r x)) := P x.

Definition num_sem (R : numDomainType) (i : interval int) (x : R) : bool :=
  (x \in Num.real) && (x \in map_itv intr i).

Definition nat_sem (i : interval int) (x : nat) : bool := Posz x \in i.

Definition posnum (R : numDomainType) of phant R :=
  def (@num_sem R) (Real `]0, +oo[).

Definition nonneg (R : numDomainType) of phant R :=
  def (@num_sem R) (Real `[0, +oo[).

(* a few lifting helper functions *)
Definition real1 (op1 : interval int -> interval int) (x : Itv.t) : Itv.t :=
  match x with Itv.Top => Itv.Top | Itv.Real x => Itv.Real (op1 x) end.

Definition real2 (op2 : interval int -> interval int -> interval int)
    (x y : Itv.t) : Itv.t :=
  match x, y with
  | Itv.Top, _ | _, Itv.Top => Itv.Top
  | Itv.Real x, Itv.Real y => Itv.Real (op2 x y)
  end.

Lemma spec_real1 T f (op1 : T -> T) (op1i : interval int -> interval int) :
    forall (x : T), (forall xi, f xi x = true -> f (op1i xi) (op1 x) = true) ->
  forall xi, spec f xi x -> spec f (real1 op1i xi) (op1 x).
Proof. by move=> x + [//| xi]; apply. Qed.

Lemma spec_real2 T f (op2 : T -> T -> T)
    (op2i : interval int -> interval int -> interval int) (x y : T) :
    (forall xi yi, f xi x = true -> f yi y = true ->
     f (op2i xi yi) (op2 x y) = true) ->
  forall xi yi, spec f xi x -> spec f yi y ->
    spec f (real2 op2i xi yi) (op2 x y).
Proof. by move=> + [//| xi] [//| yi]; apply. Qed.

Module Exports.
Arguments r {T sem i}.
Notation "{ 'itv' R & i }" := (def (@num_sem R) (Itv.Real i%Z)) : type_scope.
Notation "{ 'i01' R }" := {itv R & `[0, 1]} : type_scope.
Notation "{ 'posnum' R }" := (@posnum _ (Phant R))  : ring_scope.
Notation "{ 'nonneg' R }" := (@nonneg _ (Phant R))  : ring_scope.
Notation "x %:itv" := (from (Phantom _ x)) : ring_scope.
Notation "[ 'itv' 'of' x ]" := (fromP (Phantom _ x)) : ring_scope.
Notation num := r.
Notation "x %:inum" := (r x) (only parsing) : ring_scope.
Notation "x %:num" := (r x) : ring_scope.
Notation "x %:posnum" := (@r _ _ (Real `]0%Z, +oo[) x) : ring_scope.
Notation "x %:nngnum" := (@r _ _ (Real `[0%Z, +oo[) x) : ring_scope.
End Exports.
End Itv.
Export Itv.Exports.

Local Notation num_spec := (Itv.spec (@Itv.num_sem _)).
Local Notation num_def R := (Itv.def (@Itv.num_sem R)).
Local Notation num_itv_bound R := (@map_itv_bound _ R intr).

Local Notation nat_spec := (Itv.spec Itv.nat_sem).
Local Notation nat_def := (Itv.def Itv.nat_sem).

Section POrder.
Context d (T : porderType d) (f : interval int -> T -> bool) (i : Itv.t).
Local Notation itv := (Itv.def f i).
HB.instance Definition _ := [isSub for @Itv.r T f i].
HB.instance Definition _ : Order.POrder d itv := [POrder of itv by <:].
End POrder.

Section Order.
Variables (R : numDomainType) (i : interval int).
Local Notation nR := (num_def R (Itv.Real i)).

Lemma itv_le_total_subproof : total (<=%O : rel nR).
Proof.
move=> x y; apply: real_comparable.
- by case: x => [x /=/andP[]].
- by case: y => [y /=/andP[]].
Qed.

HB.instance Definition _ := Order.POrder_isTotal.Build ring_display nR
  itv_le_total_subproof.

End Order.

Module TypInstances.

Lemma top_typ_spec T f (x : T) : Itv.spec f Itv.Top x.
Proof. by []. Qed.

Canonical top_typ T f := Itv.Typ (@top_typ_spec T f).

Lemma real_domain_typ_spec (R : realDomainType) (x : R) :
  num_spec (Itv.Real `]-oo, +oo[) x.
Proof. by rewrite /Itv.num_sem/= num_real. Qed.

Canonical real_domain_typ (R : realDomainType) :=
  Itv.Typ (@real_domain_typ_spec R).

Lemma real_field_typ_spec (R : realFieldType) (x : R) :
  num_spec (Itv.Real `]-oo, +oo[) x.
Proof. exact: real_domain_typ_spec. Qed.

Canonical real_field_typ (R : realFieldType) :=
  Itv.Typ (@real_field_typ_spec R).

Lemma nat_typ_spec (x : nat) : nat_spec (Itv.Real `[0, +oo[) x.
Proof. by []. Qed.

Canonical nat_typ := Itv.Typ nat_typ_spec.

Lemma typ_inum_spec (i : Itv.t) (xt : Itv.typ i) (x : Itv.sort xt) :
  Itv.spec (@Itv.sort_sem _ xt) i x.
Proof. by move: xt x => []. Qed.

(* This adds _ <- Itv.r ( typ_inum )
   to canonical projections (c.f., Print Canonical Projections
   Itv.r) meaning that if no other canonical instance (with a
   registered head symbol) is found, a canonical instance of
   Itv.typ, like the ones above, will be looked for. *)
Canonical typ_inum (i : Itv.t) (xt : Itv.typ i) (x : Itv.sort xt) :=
  Itv.mk (typ_inum_spec x).

End TypInstances.
Export (canonicals) TypInstances.

Class unify {T} f (x y : T) := Unify : f x y = true.
#[export] Hint Mode unify + + + + : typeclass_instances.
Class unify' {T} f (x y : T) := Unify' : f x y = true.
#[export] Instance unify'P {T} f (x y : T) : unify' f x y -> unify f x y := id.
#[export]
Hint Extern 0 (unify' _ _ _) => vm_compute; reflexivity : typeclass_instances.

Notation unify_itv ix iy := (unify Itv.sub ix iy).

#[export] Instance top_wider_anything i : unify_itv i Itv.Top.
Proof. by case: i. Qed.

#[export] Instance real_wider_anyreal i :
  unify_itv (Itv.Real i) (Itv.Real `]-oo, +oo[).
Proof. by case: i => [l u]; apply/andP; rewrite !bnd_simp. Qed.

Section NumDomainTheory.
Context {R : numDomainType} {i : Itv.t}.
Implicit Type x : num_def R i.

Lemma le_num_itv_bound (x y : itv_bound int) :
  (num_itv_bound R x <= num_itv_bound R y)%O = (x <= y)%O.
Proof.
by case: x y => [[] x | x] [[] y | y]//=; rewrite !bnd_simp ?ler_int ?ltr_int.
Qed.

Lemma num_itv_bound_le_BLeft (x : itv_bound int) (y : int) :
  (num_itv_bound R x <= BLeft (y%:~R : R))%O = (x <= BLeft y)%O.
Proof.
rewrite -[BLeft y%:~R]/(map_itv_bound intr (BLeft y)).
by rewrite le_num_itv_bound.
Qed.

Lemma BRight_le_num_itv_bound (x : int) (y : itv_bound int) :
  (BRight (x%:~R : R) <= num_itv_bound R y)%O = (BRight x <= y)%O.
Proof.
rewrite -[BRight x%:~R]/(map_itv_bound intr (BRight x)).
by rewrite le_num_itv_bound.
Qed.

Lemma num_spec_sub (x y : Itv.t) : Itv.sub x y ->
  forall z : R, num_spec x z -> num_spec y z.
Proof.
case: x y => [| x] [| y] //= x_sub_y z /andP[rz]; rewrite /Itv.num_sem rz/=.
move: x y x_sub_y => [lx ux] [ly uy] /andP[lel leu] /=.
move=> /andP[lxz zux]; apply/andP; split.
- by apply: le_trans lxz; rewrite le_num_itv_bound.
- by apply: le_trans zux _; rewrite le_num_itv_bound.
Qed.

Definition empty_itv := Itv.Real `[1, 0]%Z.

Lemma bottom x : ~ unify_itv i empty_itv.
Proof.
case: x => x /= /[swap] /num_spec_sub /[apply] /andP[_] /=.
by rewrite in_itv/= => /andP[] /le_trans /[apply]; rewrite ler10.
Qed.

Lemma gt0 x : unify_itv i (Itv.Real `]0%Z, +oo[) -> 0 < x%:num :> R.
Proof.
case: x => x /= /[swap] /num_spec_sub /[apply] /andP[_].
by rewrite /= in_itv/= andbT.
Qed.

Lemma le0F x : unify_itv i (Itv.Real `]0%Z, +oo[) -> (x%:num <= 0 :> R) = false.
Proof.
case: x => x /= /[swap] /num_spec_sub /[apply] /andP[_] /=.
by rewrite in_itv/= andbT => /lt_geF.
Qed.

Lemma lt0 x : unify_itv i (Itv.Real `]-oo, 0%Z[) -> x%:num < 0 :> R.
Proof.
by case: x => x /= /[swap] /num_spec_sub /[apply] /andP[_] /=; rewrite in_itv.
Qed.

Lemma ge0F x : unify_itv i (Itv.Real `]-oo, 0%Z[) -> (0 <= x%:num :> R) = false.
Proof.
case: x => x /= /[swap] /num_spec_sub /[apply] /andP[_] /=.
by rewrite in_itv/= => /lt_geF.
Qed.

Lemma ge0 x : unify_itv i (Itv.Real `[0%Z, +oo[) -> 0 <= x%:num :> R.
Proof.
case: x => x /= /[swap] /num_spec_sub /[apply] /andP[_] /=.
by rewrite in_itv/= andbT.
Qed.

Lemma lt0F x : unify_itv i (Itv.Real `[0%Z, +oo[) -> (x%:num < 0 :> R) = false.
Proof.
case: x => x /= /[swap] /num_spec_sub /[apply] /andP[_] /=.
by rewrite in_itv/= andbT => /le_gtF.
Qed.

Lemma le0 x : unify_itv i (Itv.Real `]-oo, 0%Z]) -> x%:num <= 0 :> R.
Proof.
by case: x => x /= /[swap] /num_spec_sub /[apply] /andP[_] /=; rewrite in_itv.
Qed.

Lemma gt0F x : unify_itv i (Itv.Real `]-oo, 0%Z]) -> (0 < x%:num :> R) = false.
Proof.
case: x => x /= /[swap] /num_spec_sub /[apply] /andP[_] /=.
by rewrite in_itv/= => /le_gtF.
Qed.

Lemma cmp0 x : unify_itv i (Itv.Real `]-oo, +oo[) -> 0 >=< x%:num.
Proof. by case: i x => [//| i' [x /=/andP[]]]. Qed.

Lemma neq0 x :
  unify (fun ix iy => ~~ Itv.sub ix iy) (Itv.Real `[0%Z, 0%Z]) i ->
  x%:num != 0 :> R.
Proof.
case: i x => [//| [l u] [x /= Px]]; apply: contra => /eqP x0 /=.
move: Px; rewrite x0 => /and3P[_ /= l0 u0]; apply/andP; split.
- by case: l l0 => [[] l /= |//]; rewrite !bnd_simp ?lerz0 ?ltrz0.
- by case: u u0 => [[] u /= |//]; rewrite !bnd_simp ?ler0z ?ltr0z.
Qed.

Lemma eq0F x :
  unify (fun ix iy => ~~ Itv.sub ix iy) (Itv.Real `[0%Z, 0%Z]) i ->
  (x%:num == 0 :> R) = false.
Proof. by move=> u; apply/negbTE/neq0. Qed.

Lemma lt1 x : unify_itv i (Itv.Real `]-oo, 1%Z[) -> x%:num < 1 :> R.
Proof.
by case: x => x /= /[swap] /num_spec_sub /[apply] /andP[_] /=; rewrite in_itv.
Qed.

Lemma ge1F x : unify_itv i (Itv.Real `]-oo, 1%Z[) -> (1 <= x%:num :> R) = false.
Proof.
case: x => x /= /[swap] /num_spec_sub /[apply] /andP[_] /=.
by rewrite in_itv/= => /lt_geF.
Qed.

Lemma le1 x : unify_itv i (Itv.Real `]-oo, 1%Z]) -> x%:num <= 1 :> R.
Proof.
by case: x => x /= /[swap] /num_spec_sub /[apply] /andP[_] /=; rewrite in_itv.
Qed.

Lemma gt1F x : unify_itv i (Itv.Real `]-oo, 1%Z]) -> (1 < x%:num :> R) = false.
Proof.
case: x => x /= /[swap] /num_spec_sub /[apply] /andP[_] /=.
by rewrite in_itv/= => /le_gtF.
Qed.

Lemma widen_itv_subproof x i' : Itv.sub i i' -> num_spec i' x%:num.
Proof. by case: x => x /= /[swap] /num_spec_sub; apply. Qed.

Definition widen_itv x i' (uni : unify_itv i i') :=
  Itv.mk (widen_itv_subproof x uni).

Lemma widen_itvE x (uni : unify_itv i i) : @widen_itv x i uni = x.
Proof. exact/val_inj. Qed.

Lemma posE x (uni : unify_itv i (Itv.Real `]0%Z, +oo[)) :
  (widen_itv x%:num%:itv uni)%:num = x%:num.
Proof. by []. Qed.

Lemma nngE x (uni : unify_itv i (Itv.Real `[0%Z, +oo[)) :
  (widen_itv x%:num%:itv uni)%:num = x%:num.
Proof. by []. Qed.

End NumDomainTheory.

Arguments bottom {R i} _ {_}.
Arguments gt0 {R i} _ {_}.
Arguments le0F {R i} _ {_}.
Arguments lt0 {R i} _ {_}.
Arguments ge0F {R i} _ {_}.
Arguments ge0 {R i} _ {_}.
Arguments lt0F {R i} _ {_}.
Arguments le0 {R i} _ {_}.
Arguments gt0F {R i} _ {_}.
Arguments cmp0 {R i} _ {_}.
Arguments neq0 {R i} _ {_}.
Arguments eq0F {R i} _ {_}.
Arguments lt1 {R i} _ {_}.
Arguments ge1F {R i} _ {_}.
Arguments le1 {R i} _ {_}.
Arguments gt1F {R i} _ {_}.
Arguments widen_itv {R i} _ {_ _}.
Arguments widen_itvE {R i} _ {_}.
Arguments posE {R i} _ {_}.
Arguments nngE {R i} _ {_}.

Notation "[ 'gt0' 'of' x ]" := (ltac:(refine (gt0 x%:itv))) (only parsing).
Notation "[ 'lt0' 'of' x ]" := (ltac:(refine (lt0 x%:itv))) (only parsing).
Notation "[ 'ge0' 'of' x ]" := (ltac:(refine (ge0 x%:itv))) (only parsing).
Notation "[ 'le0' 'of' x ]" := (ltac:(refine (le0 x%:itv))) (only parsing).
Notation "[ 'cmp0' 'of' x ]" := (ltac:(refine (cmp0 x%:itv))) (only parsing).
Notation "[ 'neq0' 'of' x ]" := (ltac:(refine (neq0 x%:itv))) (only parsing).

#[export] Hint Extern 0 (is_true (0%R < _)%R) => solve [apply: gt0] : core.
#[export] Hint Extern 0 (is_true (_ < 0%R)%R) => solve [apply: lt0] : core.
#[export] Hint Extern 0 (is_true (0%R <= _)%R) => solve [apply: ge0] : core.
#[export] Hint Extern 0 (is_true (_ <= 0%R)%R) => solve [apply: le0] : core.
#[export] Hint Extern 0 (is_true (_ \is Num.real)) => solve [apply: cmp0]
  : core.
#[export] Hint Extern 0 (is_true (0%R >=< _)%R) => solve [apply: cmp0] : core.
#[export] Hint Extern 0 (is_true (_ != 0%R)) => solve [apply: neq0] : core.
#[export] Hint Extern 0 (is_true (_ < 1%R)%R) => solve [apply: lt1] : core.
#[export] Hint Extern 0 (is_true (_ <= 1%R)%R) => solve [apply: le1] : core.

Notation "x %:i01" := (widen_itv x%:itv : {i01 _}) (only parsing) : ring_scope.
Notation "x %:i01" := (@widen_itv _ _
    (@Itv.from _ _ _ (Phantom _ x)) (Itv.Real `[0, 1]%Z) _)
  (only printing) : ring_scope.
Notation "x %:pos" := (widen_itv x%:itv : {posnum _}) (only parsing)
  : ring_scope.
Notation "x %:pos" := (@widen_itv _ _
    (@Itv.from _ _ _ (Phantom _ x)) (Itv.Real `]0%Z, +oo[) _)
  (only printing) : ring_scope.
Notation "x %:nng" := (widen_itv x%:itv : {nonneg _}) (only parsing)
  : ring_scope.
Notation "x %:nng" := (@widen_itv _ _
    (@Itv.from _ _ _ (Phantom _ x)) (Itv.Real `[0%Z, +oo[) _)
  (only printing) : ring_scope.

Local Open Scope ring_scope.

Module Instances.

Import IntItv.

Section NumDomainInstances.
Context {R : numDomainType}.

Lemma num_spec_zero : num_spec (Itv.Real `[0, 0]) (0 : R).
Proof. by apply/andP; split; [exact: real0 | rewrite /= in_itv/= lexx]. Qed.

Canonical zero_inum := Itv.mk num_spec_zero.

Lemma num_spec_one : num_spec (Itv.Real `[1, 1]) (1 : R).
Proof. by apply/andP; split; [exact: real1 | rewrite /= in_itv/= lexx]. Qed.

Canonical one_inum := Itv.mk num_spec_one.

Lemma opp_boundr (x : R) b :
  (BRight (- x)%R <= num_itv_bound R (opp_bound b))%O
  = (num_itv_bound R b <= BLeft x)%O.
Proof.
by case: b => [[] b | []//]; rewrite /= !bnd_simp mulrNz ?lerN2 // ltrN2.
Qed.

Lemma opp_boundl (x : R) b :
  (num_itv_bound R (opp_bound b) <= BLeft (- x)%R)%O
  = (BRight x <= num_itv_bound R b)%O.
Proof.
by case: b => [[] b | []//]; rewrite /= !bnd_simp mulrNz ?lerN2 // ltrN2.
Qed.

Lemma num_spec_opp (i : Itv.t) (x : num_def R i) (r := Itv.real1 opp i) :
  num_spec r (- x%:num).
Proof.
apply: Itv.spec_real1 (Itv.P x).
case: x => x /= _ [l u] /and3P[xr lx xu].
rewrite /Itv.num_sem/= realN xr/=; apply/andP.
by rewrite opp_boundl opp_boundr.
Qed.

Canonical opp_inum (i : Itv.t) (x : num_def R i) := Itv.mk (num_spec_opp x).

Lemma num_itv_add_boundl (x1 x2 : R) b1 b2 :
  (num_itv_bound R b1 <= BLeft x1)%O -> (num_itv_bound R b2 <= BLeft x2)%O ->
  (num_itv_bound R (add_boundl b1 b2) <= BLeft (x1 + x2)%R)%O.
Proof.
case: b1 b2 => [bb1 b1 |//] [bb2 b2 |//].
case: bb1; case: bb2; rewrite /= !bnd_simp mulrzDr.
- exact: lerD.
- exact: ler_ltD.
- exact: ltr_leD.
- exact: ltrD.
Qed.

Lemma num_itv_add_boundr (x1 x2 : R) b1 b2 :
  (BRight x1 <= num_itv_bound R b1)%O -> (BRight x2 <= num_itv_bound R b2)%O ->
  (BRight (x1 + x2)%R <= num_itv_bound R (add_boundr b1 b2))%O.
Proof.
case: b1 b2 => [bb1 b1 |//] [bb2 b2 |//].
case: bb1; case: bb2; rewrite /= !bnd_simp mulrzDr.
- exact: ltrD.
- exact: ltr_leD.
- exact: ler_ltD.
- exact: lerD.
Qed.

Lemma num_spec_add (xi yi : Itv.t) (x : num_def R xi) (y : num_def R yi)
    (r := Itv.real2 add xi yi) :
  num_spec r (x%:num + y%:num).
Proof.
apply: Itv.spec_real2 (Itv.P x) (Itv.P y).
case: x y => [x /= _] [y /= _] => {xi yi r} -[lx ux] [ly uy]/=.
move=> /andP[xr /=/andP[lxx xux]] /andP[yr /=/andP[lyy yuy]].
rewrite /Itv.num_sem realD//=; apply/andP.
by rewrite num_itv_add_boundl ?num_itv_add_boundr.
Qed.

Canonical add_inum (xi yi : Itv.t) (x : num_def R xi) (y : num_def R yi) :=
  Itv.mk (num_spec_add x y).

Variant sign_spec (l u : itv_bound int) (x : R) : signi -> Set :=
  | ISignEqZero : l = BLeft 0 -> u = BRight 0 -> x = 0 ->
                  sign_spec l u x (Known EqZero)
  | ISignNonNeg : (BLeft 0%:Z <= l)%O -> (BRight 0%:Z < u)%O -> 0 <= x ->
                  sign_spec l u x (Known NonNeg)
  | ISignNonPos : (l < BLeft 0%:Z)%O -> (u <= BRight 0%:Z)%O -> x <= 0 ->
                  sign_spec l u x (Known NonPos)
  | ISignBoth : (l < BLeft 0%:Z)%O -> (BRight 0%:Z < u)%O -> x \in Num.real ->
                sign_spec l u x Unknown.

Lemma signP (l u : itv_bound int) (x : R) :
    (num_itv_bound R l <= BLeft x)%O -> (BRight x <= num_itv_bound R u)%O ->
    x \in Num.real ->
  sign_spec l u x (sign (Interval l u)).
Proof.
move=> + + xr; rewrite /sign/sign_boundl/sign_boundr.
have [lneg|lpos|->] := ltgtP l; have [uneg|upos|->] := ltgtP u => lx xu.
- apply: ISignNonPos => //; first exact: ltW.
  have:= le_trans xu (eqbRL (le_num_itv_bound _ _) (ltW uneg)).
  by rewrite bnd_simp.
- exact: ISignBoth.
- exact: ISignNonPos.
- have:= @ltxx _ _ (num_itv_bound R l).
  rewrite (le_lt_trans lx) -?leBRight_ltBLeft ?(le_trans xu)//.
  by rewrite le_num_itv_bound (le_trans (ltW uneg)).
- apply: ISignNonNeg => //; first exact: ltW.
  have:= le_trans (eqbRL (le_num_itv_bound _ _) (ltW lpos)) lx.
  by rewrite bnd_simp.
- have:= @ltxx _ _ (num_itv_bound R l).
  rewrite (le_lt_trans lx) -?leBRight_ltBLeft ?(le_trans xu)//.
  by rewrite le_num_itv_bound ?leBRight_ltBLeft.
- have:= @ltxx _ _ (num_itv_bound R (BLeft 0%Z)).
  rewrite (le_lt_trans lx) -?leBRight_ltBLeft ?(le_trans xu)//.
  by rewrite le_num_itv_bound -?ltBRight_leBLeft.
- exact: ISignNonNeg.
- apply: ISignEqZero => //.
  by apply/le_anti/andP; move: lx xu; rewrite !bnd_simp.
Qed.

Lemma num_itv_mul_boundl b1 b2 (x1 x2 : R) :
  (BLeft 0%:Z <= b1 -> BLeft 0%:Z <= b2 ->
   num_itv_bound R b1 <= BLeft x1 ->
   num_itv_bound R b2 <= BLeft x2 ->
   num_itv_bound R (mul_boundl b1 b2) <= BLeft (x1 * x2))%O.
Proof.
move: b1 b2 => [[] b1 | []//] [[] b2 | []//] /=; rewrite 4!bnd_simp.
- set bl := match b1 with 0%Z => _ | _ => _ end.
  have -> : bl = BLeft (b1 * b2).
    rewrite {}/bl; move: b1 b2 => [[|p1]|p1] [[|p2]|p2]; congr BLeft.
    by rewrite mulr0.
  by rewrite bnd_simp intrM -2!(ler0z R); apply: ler_pM.
- case: b1 => [[|b1] | b1]; rewrite !bnd_simp// => b1p b2p sx1 sx2.
  + by rewrite mulr_ge0 ?(le_trans _ (ltW sx2)) ?ler0z.
  + rewrite intrM (@lt_le_trans _ _ (b1.+1%:~R * x2)) ?ltr_pM2l//.
    by rewrite ler_pM2r// (le_lt_trans _ sx2) ?ler0z.
- case: b2 => [[|b2] | b2]; rewrite !bnd_simp// => b1p b2p sx1 sx2.
  + by rewrite mulr_ge0 ?(le_trans _ (ltW sx1)) ?ler0z.
  + rewrite intrM (@le_lt_trans _ _ (b1%:~R * x2)) ?ler_wpM2l ?ler0z//.
    by rewrite ltr_pM2r ?(lt_le_trans _ sx2).
- by rewrite -2!(ler0z R) bnd_simp intrM; apply: ltr_pM.
Qed.

Lemma num_itv_mul_boundr b1 b2 (x1 x2 : R) :
  (0 <= x1 -> 0 <= x2 ->
   BRight x1 <= num_itv_bound R b1 ->
   BRight x2 <= num_itv_bound R b2 ->
   BRight (x1 * x2) <= num_itv_bound R (mul_boundr b1 b2))%O.
Proof.
case: b1 b2 => [b1b b1 | []] [b2b b2 | []] //= x1p x2p; last first.
- case: b2b b2 => -[[|//] | //] _ x20.
  + have:= @ltxx _ (itv_bound R) (BLeft 0%:~R).
    by rewrite (lt_le_trans _ x20).
  + have -> : x2 = 0 by apply/le_anti/andP.
    by rewrite mulr0.
- case: b1b b1 => -[[|//] |//] x10 _.
  + have:= @ltxx _ (itv_bound R) (BLeft 0%Z%:~R).
    by rewrite (lt_le_trans _ x10).
  + by have -> : x1 = 0; [apply/le_anti/andP | rewrite mul0r].
case: b1b b2b => -[]; rewrite -[intRing.mulz]/GRing.mul.
- case: b1 => [[|b1] | b1]; rewrite !bnd_simp => x1b x2b.
  + by have:= @ltxx _ R 0; rewrite (le_lt_trans x1p x1b).
  + case: b2 x2b => [[| b2] | b2] => x2b; rewrite bnd_simp.
    * by have:= @ltxx _ R 0; rewrite (le_lt_trans x2p x2b).
    * by rewrite intrM ltr_pM.
    * have:= @ltxx _ R 0; rewrite (le_lt_trans x2p)//.
      by rewrite (lt_le_trans x2b) ?lerz0.
  + have:= @ltxx _ R 0; rewrite (le_lt_trans x1p)//.
    by rewrite (lt_le_trans x1b) ?lerz0.
- case: b1 => [[|b1] | b1]; rewrite !bnd_simp => x1b x2b.
  + by have:= @ltxx _ R 0; rewrite (le_lt_trans x1p x1b).
  + case: b2 x2b => [[| b2] | b2] x2b; rewrite bnd_simp.
    * exact: mulr_ge0_le0.
    * by rewrite intrM (le_lt_trans (ler_wpM2l x1p x2b)) ?ltr_pM2r.
    * have:= @ltxx _ _ x2.
      by rewrite (le_lt_trans x2b) ?(lt_le_trans _ x2p) ?ltrz0.
  + have:= @ltxx _ _ x1.
    by rewrite (lt_le_trans x1b) ?(le_trans _ x1p) ?lerz0.
- case: b1 => [[|b1] | b1]; rewrite !bnd_simp => x1b x2b.
  + case: b2 x2b => [[|b2] | b2] x2b; rewrite bnd_simp.
    * by have:= @ltxx _ _ x2; rewrite (lt_le_trans x2b).
    * by have -> : x1 = 0; [apply/le_anti/andP | rewrite mul0r].
    * have:= @ltxx _ _ x2.
      by rewrite (lt_le_trans x2b) ?(le_trans _ x2p) ?lerz0.
  + case: b2 x2b => [[|b2] | b2] x2b; rewrite bnd_simp.
    * by have:= @ltxx _ _ x2; rewrite (lt_le_trans x2b).
    * by rewrite intrM (le_lt_trans (ler_wpM2r x2p x1b)) ?ltr_pM2l.
    * have:= @ltxx _ _ x2.
      by rewrite (lt_le_trans x2b) ?(le_trans _ x2p) ?lerz0.
  + have:= @ltxx _ _ x1.
    by rewrite (le_lt_trans x1b) ?(lt_le_trans _ x1p) ?ltrz0.
- case: b1 => [[|b1] | b1]; rewrite !bnd_simp => x1b x2b.
  + by have -> : x1 = 0; [apply/le_anti/andP | rewrite mul0r].
  + case: b2 x2b => [[| b2] | b2] x2b; rewrite bnd_simp.
    * by have -> : x2 = 0; [apply/le_anti/andP | rewrite mulr0].
    * by rewrite intrM ler_pM.
    * have:= @ltxx _ _ x2.
      by rewrite (le_lt_trans x2b) ?(lt_le_trans _ x2p) ?ltrz0.
  + have:= @ltxx _ _ x1.
    by rewrite (le_lt_trans x1b) ?(lt_le_trans _ x1p) ?ltrz0.
Qed.

Lemma BRight_le_mul_boundr b1 b2 (x1 x2 : R) :
  (0 <= x1 -> x2 \in Num.real -> BRight 0%Z <= b2 ->
   BRight x1 <= num_itv_bound R b1 ->
   BRight x2 <= num_itv_bound R b2 ->
   BRight (x1 * x2) <= num_itv_bound R (mul_boundr b1 b2))%O.
Proof.
move=> x1ge0 x2r b2ge0 lex1b1 lex2b2.
have /orP[x2ge0 | x2le0] := x2r; first exact: num_itv_mul_boundr.
have lem0 : (BRight (x1 * x2) <= BRight 0%R)%O.
  by rewrite bnd_simp mulr_ge0_le0 // ltW.
apply: le_trans lem0 _.
rewrite -(mulr0z 1) BRight_le_num_itv_bound.
apply: mul_boundr_gt0 => //.
by rewrite -(@BRight_le_num_itv_bound R) (le_trans _ lex1b1).
Qed.

Lemma comparable_num_itv_bound (x y : itv_bound int) :
  (num_itv_bound R x >=< num_itv_bound R y)%O.
Proof.
by case: x y => [[] x | []] [[] y | []]//; apply/orP;
  rewrite !bnd_simp ?ler_int ?ltr_int;
  case: leP => xy; apply/orP => //; rewrite ltW ?orbT.
Qed.

Lemma num_itv_bound_min (x y : itv_bound int) :
  num_itv_bound R (Order.min x y)
  = Order.min (num_itv_bound R x) (num_itv_bound R y).
Proof.
have [lexy | ltyx] := leP x y; [by rewrite !minEle le_num_itv_bound lexy|].
rewrite minElt -if_neg -comparable_leNgt ?le_num_itv_bound ?ltW//.
exact: comparable_num_itv_bound.
Qed.

Lemma num_itv_bound_max (x y : itv_bound int) :
  num_itv_bound R (Order.max x y)
  = Order.max (num_itv_bound R x) (num_itv_bound R y).
Proof.
have [lexy | ltyx] := leP x y; [by rewrite !maxEle le_num_itv_bound lexy|].
rewrite maxElt -if_neg -comparable_leNgt ?le_num_itv_bound ?ltW//.
exact: comparable_num_itv_bound.
Qed.

Lemma num_spec_mul (xi yi : Itv.t) (x : num_def R xi) (y : num_def R yi)
    (r := Itv.real2 mul xi yi) :
  num_spec r (x%:num * y%:num).
Proof.
rewrite {}/r; case: xi yi x y => [//| [xl xu]] [//| [yl yu]].
case=> [x /=/and3P[xr /= xlx xxu]] [y /=/and3P[yr /= yly yyu]].
rewrite -/(sign (Interval xl xu)) -/(sign (Interval yl yu)).
have ns000 : @Itv.num_sem R `[0, 0] 0 by apply/and3P.
have xyr : x * y \in Num.real by exact: realM.
case: (signP xlx xxu xr) => xlb xub xs.
- by rewrite xs mul0r; case: (signP yly yyu yr).
- case: (signP yly yyu yr) => ylb yub ys.
  + by rewrite ys mulr0.
  + apply/and3P; split=> //=.
    * exact: num_itv_mul_boundl xlx yly.
    * exact: num_itv_mul_boundr xxu yyu.
  + apply/and3P; split=> //=; rewrite -[x * y]opprK -mulrN.
    * by rewrite opp_boundl num_itv_mul_boundr ?oppr_ge0// opp_boundr.
    * by rewrite opp_boundr num_itv_mul_boundl ?opp_boundl// opp_bound_ge0.
  + apply/and3P; split=> //=.
    * rewrite  -[x * y]opprK -mulrN opp_boundl.
      by rewrite BRight_le_mul_boundr ?realN ?opp_boundr// opp_bound_gt0 ltW.
    * by rewrite BRight_le_mul_boundr// ltW.
- case: (signP yly yyu yr) => ylb yub ys.
  + by rewrite ys mulr0.
  + apply/and3P; split=> //=; rewrite -[x * y]opprK -mulNr.
    * rewrite opp_boundl.
      by rewrite num_itv_mul_boundr ?oppr_ge0 ?opp_boundr.
    * by rewrite opp_boundr num_itv_mul_boundl ?opp_boundl// opp_bound_ge0.
  + apply/and3P; split=> //=; rewrite -mulrNN.
    * by rewrite num_itv_mul_boundl ?opp_bound_ge0 ?opp_boundl.
    * by rewrite num_itv_mul_boundr ?oppr_ge0 ?opp_boundr.
  + apply/and3P; split=> //=; rewrite -[x * y]opprK.
    * rewrite -mulNr opp_boundl BRight_le_mul_boundr ?oppr_ge0 ?opp_boundr//.
      exact: ltW.
    * rewrite opprK -mulrNN.
      by rewrite BRight_le_mul_boundr ?opp_boundr
              ?oppr_ge0 ?realN ?opp_bound_gt0// ltW.
- case: (signP yly yyu yr) => ylb yub ys.
  + by rewrite ys mulr0.
  + apply/and3P; split=> //=; rewrite mulrC mul_boundrC.
    * rewrite -[y * x]opprK -mulrN opp_boundl.
      rewrite BRight_le_mul_boundr ?oppr_ge0 ?realN ?opp_boundr//.
      by rewrite opp_bound_gt0 ltW.
    * by rewrite BRight_le_mul_boundr// ltW.
  + apply/and3P; split=> //=; rewrite mulrC mul_boundrC.
    * rewrite -[y * x]opprK -mulNr opp_boundl.
      by rewrite BRight_le_mul_boundr ?oppr_ge0 ?opp_boundr// ltW.
    * rewrite -mulrNN BRight_le_mul_boundr ?oppr_ge0 ?realN ?opp_boundr//.
      by rewrite opp_bound_gt0 ltW.
apply/and3P; rewrite xyr/= num_itv_bound_min num_itv_bound_max.
rewrite (comparable_ge_min _ (comparable_num_itv_bound _ _)).
rewrite (comparable_le_max _ (comparable_num_itv_bound _ _)).
case: (comparable_leP xr) => [x0 | /ltW x0]; split=> //.
- apply/orP; right; rewrite -[x * y]opprK -mulrN opp_boundl.
  by rewrite BRight_le_mul_boundr ?realN ?opp_boundr// opp_bound_gt0 ltW.
- by apply/orP; right; rewrite BRight_le_mul_boundr// ltW.
- apply/orP; left; rewrite -[x * y]opprK -mulNr opp_boundl.
  by rewrite BRight_le_mul_boundr ?oppr_ge0 ?opp_boundr// ltW.
- apply/orP; left; rewrite -mulrNN.
  rewrite BRight_le_mul_boundr ?oppr_ge0 ?realN ?opp_boundr//.
  by rewrite opp_bound_gt0 ltW.
Qed.

Canonical mul_inum (xi yi : Itv.t) (x : num_def R xi) (y : num_def R yi) :=
  Itv.mk (num_spec_mul x y).

Lemma num_spec_min (xi yi : Itv.t) (x : num_def R xi) (y : num_def R yi)
    (r := Itv.real2 min xi yi) :
  num_spec r (Order.min x%:num y%:num).
Proof.
apply: Itv.spec_real2 (Itv.P x) (Itv.P y).
case: x y => [x /= _] [y /= _] => {xi yi r} -[lx ux] [ly uy]/=.
move=> /andP[xr /=/andP[lxx xux]] /andP[yr /=/andP[lyy yuy]].
apply/and3P; split; rewrite ?min_real//= num_itv_bound_min real_BSide_min//.
- apply: (comparable_le_min2 (comparable_num_itv_bound _ _)) => //.
  exact: real_comparable.
- apply: (comparable_le_min2 _ (comparable_num_itv_bound _ _)) => //.
  exact: real_comparable.
Qed.

Lemma num_spec_max (xi yi : Itv.t) (x : num_def R xi) (y : num_def R yi)
    (r := Itv.real2 max xi yi) :
  num_spec r (Order.max x%:num y%:num).
Proof.
apply: Itv.spec_real2 (Itv.P x) (Itv.P y).
case: x y => [x /= _] [y /= _] => {xi yi r} -[lx ux] [ly uy]/=.
move=> /andP[xr /=/andP[lxx xux]] /andP[yr /=/andP[lyy yuy]].
apply/and3P; split; rewrite ?max_real//= num_itv_bound_max real_BSide_max//.
- apply: (comparable_le_max2 (comparable_num_itv_bound _ _)) => //.
  exact: real_comparable.
- apply: (comparable_le_max2 _ (comparable_num_itv_bound _ _)) => //.
  exact: real_comparable.
Qed.

(* We can't directly put an instance on Order.min for R : numDomainType
   since we may want instances for other porderType
   (typically \bar R or even nat). So we resort on this additional
   canonical structure. *)
Record min_max_typ d := MinMaxTyp {
  min_max_sort : porderType d;
  #[canonical=no]
  min_max_sem : interval int -> min_max_sort -> bool;
  #[canonical=no]
  min_max_minP : forall (xi yi : Itv.t) (x : Itv.def min_max_sem xi)
    (y : Itv.def min_max_sem yi),
    let: r := Itv.real2 min xi yi in
    Itv.spec min_max_sem r (Order.min x%:num y%:num);
  #[canonical=no]
  min_max_maxP : forall (xi yi : Itv.t) (x : Itv.def min_max_sem xi)
    (y : Itv.def min_max_sem yi),
    let: r := Itv.real2 max xi yi in
    Itv.spec min_max_sem r (Order.max x%:num y%:num);
}.

(* The default instances on porderType, for min... *)
Canonical min_typ_inum d (t : min_max_typ d) (xi yi : Itv.t)
    (x : Itv.def (@min_max_sem d t) xi) (y : Itv.def (@min_max_sem d t) yi)
    (r := Itv.real2 min xi yi) :=
  Itv.mk (min_max_minP x y).

(* ...and for max *)
Canonical max_typ_inum d (t : min_max_typ d) (xi yi : Itv.t)
    (x : Itv.def (@min_max_sem d t) xi) (y : Itv.def (@min_max_sem d t) yi)
    (r := Itv.real2 min xi yi) :=
  Itv.mk (min_max_maxP x y).

(* Instance of the above structure for numDomainType *)
Canonical num_min_max_typ := MinMaxTyp num_spec_min num_spec_max.

Lemma nat_num_spec (i : Itv.t) (n : nat) : nat_spec i n = num_spec i (n%:R : R).
Proof.
case: i => [//| [l u]]; rewrite /= /Itv.num_sem realn/=; congr (_ && _).
- by case: l => [[] l |//]; rewrite !bnd_simp ?pmulrn ?ler_int ?ltr_int.
- by case: u => [[] u |//]; rewrite !bnd_simp ?pmulrn ?ler_int ?ltr_int.
Qed.

Definition natmul_itv (i1 i2 : Itv.t) : Itv.t :=
  match i1, i2 with
  | Itv.Top, _ => Itv.Top
  | _, Itv.Top => Itv.Real `]-oo, +oo[
  | Itv.Real i1, Itv.Real i2 => Itv.Real (mul i1 i2)
  end.
Arguments natmul_itv /.

Lemma num_spec_natmul (xi ni : Itv.t) (x : num_def R xi) (n : nat_def ni)
    (r := natmul_itv xi ni) :
  num_spec r (x%:num *+ n%:num).
Proof.
rewrite {}/r; case: xi x ni n => [//| xi] x [| ni] n.
  by apply/and3P; case: n%:num => [|?]; rewrite ?mulr0n ?realrMn.
have Pn : num_spec (Itv.Real ni) (n%:num%:R : R).
  by case: n => /= n; rewrite [Itv.nat_sem ni n](nat_num_spec (Itv.Real ni)).
rewrite -mulr_natr -[n%:num%:R]/((Itv.Def Pn)%:num).
by rewrite (@num_spec_mul (Itv.Real xi) (Itv.Real ni)).
Qed.

Canonical natmul_inum (xi ni : Itv.t) (x : num_def R xi) (n : nat_def ni) :=
  Itv.mk (num_spec_natmul x n).

Lemma num_spec_int (i : Itv.t) (n : int) :
  num_spec i n = num_spec i (n%:~R : R).
Proof.
case: i => [//| [l u]]; rewrite /= /Itv.num_sem num_real realz/=.
congr (andb _ _).
- by case: l => [[] l |//]; rewrite !bnd_simp intz ?ler_int ?ltr_int.
- by case: u => [[] u |//]; rewrite !bnd_simp intz ?ler_int ?ltr_int.
Qed.

Lemma num_spec_intmul (xi ii : Itv.t) (x : num_def R xi) (i : num_def int ii)
    (r := natmul_itv xi ii) :
  num_spec r (x%:num *~ i%:num).
Proof.
rewrite {}/r; case: xi x ii i => [//| xi] x [| ii] i.
  by apply/and3P; case: i%:inum => [[|n] | n]; rewrite ?mulr0z ?realN ?realrMn.
have Pi : num_spec (Itv.Real ii) (i%:num%:~R : R).
  by case: i => /= i; rewrite [Itv.num_sem ii i](num_spec_int (Itv.Real ii)).
rewrite -mulrzr -[i%:num%:~R]/((Itv.Def Pi)%:num).
by rewrite (@num_spec_mul (Itv.Real xi) (Itv.Real ii)).
Qed.

Canonical intmul_inum (xi ni : Itv.t) (x : num_def R xi) (n : num_def int ni) :=
  Itv.mk (num_spec_intmul x n).

Lemma num_itv_bound_keep_pos (op : R -> R) (x : R) b :
  {homo op : x / 0 <= x} -> {homo op : x / 0 < x} ->
  (num_itv_bound R b <= BLeft x)%O ->
  (num_itv_bound R (keep_pos_bound b) <= BLeft (op x))%O.
Proof.
case: b => [[] [] [| b] // | []//] hle hlt; rewrite !bnd_simp.
- exact: hle.
- by move=> blex; apply: le_lt_trans (hlt _ _) => //; apply: lt_le_trans blex.
- exact: hlt.
- by move=> bltx; apply: le_lt_trans (hlt _ _) => //; apply: le_lt_trans bltx.
Qed.

Lemma num_itv_bound_keep_neg (op : R -> R) (x : R) b :
  {homo op : x / x <= 0} -> {homo op : x / x < 0} ->
  (BRight x <= num_itv_bound R b)%O ->
  (BRight (op x) <= num_itv_bound R (keep_neg_bound b))%O.
Proof.
case: b => [[] [[|//] | b] | []//] hge hgt; rewrite !bnd_simp.
- exact: hgt.
- by move=> xltb; apply: hgt; apply: lt_le_trans xltb _; rewrite lerz0.
- exact: hge.
- by move=> xleb; apply: hgt; apply: le_lt_trans xleb _; rewrite ltrz0.
Qed.

Lemma num_spec_inv (i : Itv.t) (x : num_def R i) (r := Itv.real1 inv i) :
  num_spec r (x%:num^-1).
Proof.
apply: Itv.spec_real1 (Itv.P x).
case: x => x /= _ [l u] /and3P[xr /= lx xu].
rewrite /Itv.num_sem/= realV xr/=; apply/andP; split.
- apply: num_itv_bound_keep_pos lx.
  + by move=> ?; rewrite invr_ge0.
  + by move=> ?; rewrite invr_gt0.
- apply: num_itv_bound_keep_neg xu.
  + by move=> ?; rewrite invr_le0.
  + by move=> ?; rewrite invr_lt0.
Qed.

Canonical inv_inum (i : Itv.t) (x : num_def R i) := Itv.mk (num_spec_inv x).

Lemma num_itv_bound_exprn_le1 (x : R) n l u :
  (num_itv_bound R l <= BLeft x)%O ->
  (BRight x <= num_itv_bound R u)%O ->
  (BRight (x ^+ n) <= num_itv_bound R (exprn_le1_bound l u))%O.
Proof.
case: u => [bu [[//|[|//]] |//] | []//].
rewrite /exprn_le1_bound; case: (leP _ l) => [lge1 /= |//] lx xu.
rewrite bnd_simp; case: n => [| n]; rewrite ?powr0n//.
have xN1 : -1 <= x.
  case: l lge1 lx => [[] l | []//]; rewrite !bnd_simp -(@ler_int R).
  - exact: le_trans.
  - by move=> + /ltW; apply: le_trans.
have x1 : x <= 1 by case: bu xu; rewrite bnd_simp// => /ltW.
have xr : x \is Num.real by exact: ler1_real.
case: (real_ge0P xr) => x0; first by rewrite expr_le1.
rewrite -[x]opprK exprNn; apply: le_trans (ler_piMl _ _) _.
- by rewrite exprn_ge0 ?oppr_ge0 1?ltW.
- suff: -1 <= (-1) ^+ n.+1 :> R /\ (-1) ^+ n.+1 <= 1 :> R => [[]//|].
  elim: n => [|n [IHn1 IHn2]]; rewrite ?powr1n// ![_ ^+ n.+2]powrS !mulN1r.
  by rewrite lerNl opprK lerNl.
- by rewrite expr_le1 ?oppr_ge0 1?lerNl// ltW.
Qed.

Lemma num_spec_exprn (i : Itv.t) (x : num_def R i) n (r := Itv.real1 exprn i) :
  num_spec r (x%:num ^+ n).
Proof.
apply: (@Itv.spec_real1 _ _ (fun x => x^+n) _ _ _ _ (Itv.P x)).
case: x => x /= _ [l u] /and3P[xr /= lx xu].
rewrite /Itv.num_sem realX//=; apply/andP; split.
- apply: (@num_itv_bound_keep_pos (fun x => x^+n)) lx.
  + exact: exprn_ge0.
  + exact: exprn_gt0.
- exact: num_itv_bound_exprn_le1 lx xu.
Qed.

Canonical exprn_inum (i : Itv.t) (x : num_def R i) n :=
  Itv.mk (num_spec_exprn x n).

Lemma num_spec_exprz (xi ki : Itv.t) (x : num_def R xi) (k : num_def int ki)
    (r := Itv.real2 exprz xi ki) :
  num_spec r (x%:num ^ k%:num).
Proof.
rewrite {}/r; case: ki k => [|[lk uk]] k; first by case: xi x.
case: xi x => [//|xi x]; rewrite /Itv.real2.
have P : Itv.num_sem
    (let 'Interval l _ := xi in Interval (keep_pos_bound l) +oo)
    (x%:num ^ k%:num).
  case: xi x => lx ux x; apply/and3P; split=> [||//].
    have xr : x%:num \is Num.real by case: x => x /=/andP[].
    by case: k%:num => n; rewrite ?realV realX.
  apply: (@num_itv_bound_keep_pos (fun x => x ^ k%:num));
    [exact: exprz_ge0 | exact: exprz_gt0 |].
  by case: x => x /=/and3P[].
case: lk k P => [slk [lk | lk] | slk] k P; [|exact: P..].
case: k P => -[k | k] /= => [_ _|]; rewrite -/(exprn xi); last first.
  by move=> /and3P[_ /=]; case: slk; rewrite bnd_simp -pmulrn natz.
exact: (@num_spec_exprn (Itv.Real xi)).
Qed.

Canonical exprz_inum (xi ki : Itv.t) (x : num_def R xi) (k : num_def int ki) :=
  Itv.mk (num_spec_exprz x k).

Lemma num_spec_norm {V : normedZmodType R} (x : V) :
  num_spec (Itv.Real `[0, +oo[) `|x|.
Proof. by apply/and3P; split; rewrite //= ?normr_real ?bnd_simp ?normr_ge0. Qed.

Canonical norm_inum {V : normedZmodType R} (x : V) := Itv.mk (num_spec_norm x).

End NumDomainInstances.

Section RcfInstances.
Context {R : rcfType}.

Definition sqrt_itv (i : Itv.t) : Itv.t :=
  match i with
  | Itv.Top => Itv.Real `[0%Z, +oo[
  | Itv.Real (Interval l u) =>
    match l with
    | BSide b 0%Z => Itv.Real (Interval (BSide b 0%Z) +oo)
    | BSide b (Posz (S _)) => Itv.Real `]0%Z, +oo[
    | _ => Itv.Real `[0, +oo[
    end
  end.
Arguments sqrt_itv /.

Lemma num_spec_sqrt (i : Itv.t) (x : num_def R i) (r := sqrt_itv i) :
  num_spec r (Num.sqrt x%:num).
Proof.
have: Itv.num_sem `[0%Z, +oo[ (Num.sqrt x%:num).
  by apply/and3P; rewrite /= num_real !bnd_simp sqrtr_ge0.
rewrite {}/r; case: i x => [//| [[bl [l |//] |//] u]] [x /= +] _.
case: bl l => -[| l] /and3P[xr /= bx _]; apply/and3P; split=> //=;
  move: bx; rewrite !bnd_simp ?sqrtr_ge0// sqrtr_gt0;
  [exact: lt_le_trans | exact: le_lt_trans..].
Qed.

Canonical sqrt_inum (i : Itv.t) (x : num_def R i) := Itv.mk (num_spec_sqrt x).

End RcfInstances.

Section NumClosedFieldInstances.
Context {R : numClosedFieldType}.

Definition sqrtC_itv (i : Itv.t) : Itv.t :=
  match i with
  | Itv.Top => Itv.Top
  | Itv.Real (Interval l u) =>
    match l with
    | BSide b (Posz _) => Itv.Real (Interval (BSide b 0%Z) +oo)
    | _ => Itv.Top
    end
  end.
Arguments sqrtC_itv /.

Lemma num_spec_sqrtC (i : Itv.t) (x : num_def R i) (r := sqrtC_itv i) :
  num_spec r (sqrtC x%:num).
Proof.
rewrite {}/r; case: i x => [//| [l u] [x /=/and3P[xr /= lx xu]]].
case: l lx => [bl [l |//] |[]//] lx; apply/and3P; split=> //=.
  by apply: sqrtC_real; case: bl lx => /[!bnd_simp] [|/ltW]; apply: le_trans.
case: bl lx => /[!bnd_simp] lx.
- by rewrite sqrtC_ge0; apply: le_trans lx.
- by rewrite sqrtC_gt0; apply: le_lt_trans lx.
Qed.

Canonical sqrtC_inum (i : Itv.t) (x : num_def R i) := Itv.mk (num_spec_sqrtC x).

End NumClosedFieldInstances.

Section NatInstances.
Local Open Scope nat_scope.
Implicit Type (n : nat).

Lemma nat_spec_zero : nat_spec (Itv.Real `[0, 0]%Z) 0. Proof. by []. Qed.

Canonical zeron_inum := Itv.mk nat_spec_zero.

Lemma nat_spec_add (xi yi : Itv.t) (x : nat_def xi) (y : nat_def yi)
    (r := Itv.real2 add xi yi) :
  nat_spec r (x%:num + y%:num).
Proof.
have Px : num_spec xi (x%:num%:R : int).
  by case: x => /= x; rewrite (@nat_num_spec int).
have Py : num_spec yi (y%:num%:R : int).
  by case: y => /= y; rewrite (@nat_num_spec int).
rewrite (@nat_num_spec int) natrD.
rewrite -[x%:num%:R]/((Itv.Def Px)%:num) -[y%:num%:R]/((Itv.Def Py)%:num).
exact: num_spec_add.
Qed.

Canonical addn_inum (xi yi : Itv.t) (x : nat_def xi) (y : nat_def yi) :=
  Itv.mk (nat_spec_add x y).

Lemma nat_spec_succ (i : Itv.t) (n : nat_def i)
    (r := Itv.real2 add i (Itv.Real `[1, 1]%Z)) :
  nat_spec r (S n%:num).
Proof.
pose i1 := Itv.Real `[1, 1]%Z; have P1 : nat_spec i1 1 by [].
by rewrite -addn1 -[1%N]/((Itv.Def P1)%:num); apply: nat_spec_add.
Qed.

Canonical succn_inum (i : Itv.t) (n : nat_def i) := Itv.mk (nat_spec_succ n).

Lemma nat_spec_double (i : Itv.t) (n : nat_def i) (r := Itv.real2 add i i) :
  nat_spec r (n%:num.*2).
Proof. by rewrite -addnn nat_spec_add. Qed.

Canonical double_inum (i : Itv.t) (x : nat_def i) := Itv.mk (nat_spec_double x).

Lemma nat_spec_mul (xi yi : Itv.t) (x : nat_def xi) (y : nat_def yi)
    (r := Itv.real2 mul xi yi) :
  nat_spec r (x%:num * y%:num).
Proof.
have Px : num_spec xi (x%:num%:R : int).
  by case: x => /= x; rewrite (@nat_num_spec int).
have Py : num_spec yi (y%:num%:R : int).
  by case: y => /= y; rewrite (@nat_num_spec int).
rewrite (@nat_num_spec int) natrM.
rewrite -[x%:num%:R]/((Itv.Def Px)%:num) -[y%:num%:R]/((Itv.Def Py)%:num).
exact: num_spec_mul.
Qed.

Canonical muln_inum (xi yi : Itv.t) (x : nat_def xi) (y : nat_def yi) :=
  Itv.mk (nat_spec_mul x y).

Lemma nat_spec_exp (i : Itv.t) (x : nat_def i) n (r := Itv.real1 exprn i) :
  nat_spec r (x%:num ^ n).
Proof.
have Px : num_spec i (x%:num%:R : int).
  by case: x => /= x; rewrite (@nat_num_spec int).
rewrite (@nat_num_spec int) natrX -[x%:num%:R]/((Itv.Def Px)%:num).
exact: num_spec_exprn.
Qed.

Canonical expn_inum (i : Itv.t) (x : nat_def i) n := Itv.mk (nat_spec_exp x n).

Lemma nat_spec_min (xi yi : Itv.t) (x : nat_def xi) (y : nat_def yi)
    (r := Itv.real2 min xi yi) :
  nat_spec r (minn x%:num y%:num).
Proof.
have Px : num_spec xi (x%:num%:R : int).
  by case: x => /= x; rewrite (@nat_num_spec int).
have Py : num_spec yi (y%:num%:R : int).
  by case: y => /= y; rewrite (@nat_num_spec int).
rewrite (@nat_num_spec int) -minEnat natr_min.
rewrite -[x%:num%:R]/((Itv.Def Px)%:num) -[y%:num%:R]/((Itv.Def Py)%:num).
exact: num_spec_min.
Qed.

Canonical minn_inum (xi yi : Itv.t) (x : nat_def xi) (y : nat_def yi) :=
  Itv.mk (nat_spec_min x y).

Lemma nat_spec_max (xi yi : Itv.t) (x : nat_def xi) (y : nat_def yi)
    (r := Itv.real2 max xi yi) :
  nat_spec r (maxn x%:num y%:num).
Proof.
have Px : num_spec xi (x%:num%:R : int).
  by case: x => /= x; rewrite (@nat_num_spec int).
have Py : num_spec yi (y%:num%:R : int).
  by case: y => /= y; rewrite (@nat_num_spec int).
rewrite (@nat_num_spec int) -maxEnat natr_max.
rewrite -[x%:num%:R]/((Itv.Def Px)%:num) -[y%:num%:R]/((Itv.Def Py)%:num).
exact: num_spec_max.
Qed.

Canonical maxn_inum (xi yi : Itv.t) (x : nat_def xi) (y : nat_def yi) :=
  Itv.mk (nat_spec_max x y).

Canonical nat_min_max_typ := MinMaxTyp nat_spec_min nat_spec_max.

Lemma nat_spec_factorial (n : nat) : nat_spec (Itv.Real `[1%Z, +oo[) n`!.
Proof. by apply/andP; rewrite bnd_simp lez_nat fact_gt0. Qed.

Canonical factorial_inum n := Itv.mk (nat_spec_factorial n).

End NatInstances.

Section IntInstances.

Lemma num_spec_Posz n : num_spec (Itv.Real `[0, +oo[) (Posz n).
Proof. by apply/and3P; rewrite /= num_real !bnd_simp. Qed.

Canonical Posz_inum n := Itv.mk (num_spec_Posz n).

Lemma num_spec_Negz n : num_spec (Itv.Real `]-oo, (-1)]) (Negz n).
Proof. by apply/and3P; rewrite /= num_real !bnd_simp. Qed.

Canonical Negz_inum n := Itv.mk (num_spec_Negz n).

End IntInstances.

End Instances.
Export (canonicals) Instances.

Section Morph.
Context {R : numDomainType} {i : Itv.t}.
Local Notation nR := (num_def R i).
Implicit Types x y : nR.
Local Notation num := (@num R (@Itv.num_sem R) i).

Lemma num_eq : {mono num : x y / x == y}. Proof. by []. Qed.
Lemma num_le : {mono num : x y / (x <= y)%O}. Proof. by []. Qed.
Lemma num_lt : {mono num : x y / (x < y)%O}. Proof. by []. Qed.
Lemma num_min : {morph num : x y / Order.min x y}.
Proof. by move=> x y; rewrite !minEle num_le -fun_if. Qed.
Lemma num_max : {morph num : x y / Order.max x y}.
Proof. by move=> x y; rewrite !maxEle num_le -fun_if. Qed.

End Morph.

Section MorphNum.
Context {R : numDomainType}.

Lemma num_abs_eq0 (a : R) : (`|a|%:nng == 0%:nng) = (a == 0).
Proof. by rewrite -normr_eq0. Qed.

End MorphNum.

Section MorphReal.
Context {R : numDomainType} {i : interval int}.
Local Notation nR := (num_def R (Itv.Real i)).
Implicit Type x y : nR.
Local Notation num := (@num R (@Itv.num_sem R) i).

Lemma num_le_max a x y :
  (a <= Num.max x%:num y%:num) = (a <= x%:num) || (a <= y%:num).
Proof. by rewrite -comparable_le_max// real_comparable. Qed.

Lemma num_ge_max a x y :
  (Num.max x%:num y%:num <= a) = (x%:num <= a) && (y%:num <= a).
Proof. by rewrite -comparable_ge_max// real_comparable. Qed.

Lemma num_le_min a x y :
  (a <= Num.min x%:num y%:num) = (a <= x%:num) && (a <= y%:num).
Proof. by rewrite -comparable_le_min// real_comparable. Qed.

Lemma num_ge_min a x y :
  (Num.min x%:num y%:num <= a) = (x%:num <= a) || (y%:num <= a).
Proof. by rewrite -comparable_ge_min// real_comparable. Qed.

Lemma num_lt_max a x y :
  (a < Num.max x%:num y%:num) = (a < x%:num) || (a < y%:num).
Proof. by rewrite -comparable_lt_max// real_comparable. Qed.

Lemma num_gt_max a x y :
  (Num.max x%:num  y%:num < a) = (x%:num < a) && (y%:num < a).
Proof. by rewrite -comparable_gt_max// real_comparable. Qed.

Lemma num_lt_min a x y :
  (a < Num.min x%:num y%:num) = (a < x%:num) && (a < y%:num).
Proof. by rewrite -comparable_lt_min// real_comparable. Qed.

Lemma num_gt_min a x y :
  (Num.min x%:num y%:num < a) = (x%:num < a) || (y%:num < a).
Proof. by rewrite -comparable_gt_min// real_comparable. Qed.

End MorphReal.

Section MorphGe0.
Context {R : numDomainType}.
Local Notation nR := (num_def R (Itv.Real `[0%Z, +oo[)).
Implicit Type x y : nR.
Local Notation num := (@num R (@Itv.num_sem R) (Itv.Real `[0%Z, +oo[)).

Lemma num_abs_le a x : 0 <= a -> (`|a|%:nng <= x) = (a <= x%:num).
Proof. by move=> a0; rewrite -num_le//= ger0_norm. Qed.

Lemma num_abs_lt a x : 0 <= a -> (`|a|%:nng < x) = (a < x%:num).
Proof. by move=> a0; rewrite -num_lt/= ger0_norm. Qed.
End MorphGe0.

Section ItvNum.
Context (R : numDomainType).
Context (x : R) (l u : itv_bound int).
Context (x_real : x \in Num.real).
Context (l_le_x : (num_itv_bound R l <= BLeft x)%O).
Context (x_le_u : (BRight x <= num_itv_bound R u)%O).
Lemma itvnum_subdef : num_spec (Itv.Real (Interval l u)) x.
Proof. by apply/and3P. Qed.
Definition ItvNum : num_def R (Itv.Real (Interval l u)) := Itv.mk itvnum_subdef.
End ItvNum.

Section ItvReal.
Context (R : realDomainType).
Context (x : R) (l u : itv_bound int).
Context (l_le_x : (num_itv_bound R l <= BLeft x)%O).
Context (x_le_u : (BRight x <= num_itv_bound R u)%O).
Lemma itvreal_subdef : num_spec (Itv.Real (Interval l u)) x.
Proof. by apply/and3P; split; first exact: num_real. Qed.
Definition ItvReal : num_def R (Itv.Real (Interval l u)) :=
  Itv.mk itvreal_subdef.
End ItvReal.

Section Itv01.
Context (R : numDomainType).
Context (x : R) (x_ge0 : 0 <= x) (x_le1 : x <= 1).
Lemma itv01_subdef : num_spec (Itv.Real `[0%Z, 1%Z]) x.
Proof. by apply/and3P; split; rewrite ?bnd_simp// ger0_real. Qed.
Definition Itv01 : num_def R (Itv.Real `[0%Z, 1%Z]) := Itv.mk itv01_subdef.
End Itv01.

Section Posnum.
Context (R : numDomainType) (x : R) (x_gt0 : 0 < x).
Lemma posnum_subdef : num_spec (Itv.Real `]0, +oo[) x.
Proof. by apply/and3P; rewrite /= gtr0_real. Qed.
Definition PosNum : {posnum R} := Itv.mk posnum_subdef.
End Posnum.

Section Nngnum.
Context (R : numDomainType) (x : R) (x_ge0 : 0 <= x).
Lemma nngnum_subdef : num_spec (Itv.Real `[0, +oo[) x.
Proof. by apply/and3P; rewrite /= ger0_real. Qed.
Definition NngNum : {nonneg R} := Itv.mk nngnum_subdef.
End Nngnum.

Variant posnum_spec (R : numDomainType) (x : R) :
  R -> bool -> bool -> bool -> Type :=
| IsPosnum (p : {posnum R}) : posnum_spec x (p%:num) false true true.

Lemma posnumP (R : numDomainType) (x : R) : 0 < x ->
  posnum_spec x x (x == 0) (0 <= x) (0 < x).
Proof.
move=> x_gt0; case: real_ltgt0P (x_gt0) => []; rewrite ?gtr0_real // => _ _.
by rewrite -[x]/(PosNum x_gt0)%:num; constructor.
Qed.

Variant nonneg_spec (R : numDomainType) (x : R) : R -> bool -> Type :=
| IsNonneg (p : {nonneg R}) : nonneg_spec x (p%:num) true.

Lemma nonnegP (R : numDomainType) (x : R) : 0 <= x -> nonneg_spec x x (0 <= x).
Proof. by move=> xge0; rewrite xge0 -[x]/(NngNum xge0)%:num; constructor. Qed.

Section Test1.

Variable R : numDomainType.
Variable x : {i01 R}.

Goal 0%:i01 = 1%:i01 :> {i01 R}.
Proof.
Abort.

Goal (- x%:num)%:itv = (- x%:num)%:itv :> {itv R & `[-1, 0]}.
Proof.
Abort.

Goal (1 - x%:num)%:i01 = x.
Proof.
Abort.

End Test1.

Section Test2.

Variable R : realDomainType.
Variable x y : {i01 R}.

Goal (x%:num * y%:num)%:i01 = x%:num%:i01.
Proof.
Abort.

End Test2.

Module Test3.
Section Test3.
Variable R : realDomainType.

Definition s_of_pq (p q : {i01 R}) : {i01 R} :=
  (1 - ((1 - p%:num)%:i01%:num * (1 - q%:num)%:i01%:num))%:i01.

Lemma s_of_p0 (p : {i01 R}) : s_of_pq p 0%:i01 = p.
Proof. by apply/val_inj; rewrite /= subr0 mulr1 subKr. Qed.

End Test3.
End Test3.

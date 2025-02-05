(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import ssrnat eqtype choice order ssralg.
From mathcomp Require Import orderedzmod numdomain numfield ssrint interval.

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
(* ```                                                                        *)
(*       {i01 R} == interface type for elements in R that live in `[0, 1];    *)
(*                  R must have a numDomainType structure.                    *)
(*                  Allows to solve automatically goals of the form x >= 0    *)
(*                  and x <= 1 if x is canonically a {i01 R}. {i01 R} is      *)
(*                  canonically stable by common operations.                  *)
(*   {itv R & i} == more generic type of values in interval i : interval int  *)
(*                  (see interval.v for notations that can be sused for i).   *)
(*                  R must have a numDomainType structure. This type is shown *)
(*                  to be a porderType.                                       *)
(*    {posnum R} := {itv R & `]0, +oo[)                                       *)
(*    {nonneg R} := {itv R & `[0, +oo[)                                       *)
(* ```                                                                        *)
(*                                                                            *)
(* ## casts from/to values within known interval                              *)
(* ```                                                                        *)
(*        x%:itv == explicitly casts x to the most precise known {itv R & i}  *)
(*                  according to existing canonical instances.                *)
(*        x%:i01 == explicitly casts x to {i01 R} according to existing       *)
(*                  canonical instances.                                      *)
(*        x%:pos == explicitly casts x to {posnum R} according to existing    *)
(*                  canonical instances.                                      *)
(*        x%:nng == explicitly casts x to {nonneg R} according to existing    *)
(*                  canonical instances.                                      *)
(*        x%:num == explicit cast from {itv R & i} to R.                      *)
(*     x%:posnum == explicit cast from {posnum R} to R.                       *)
(*     x%:nngnum == explicit cast from {nonneg R} to R.                       *)
(* ```                                                                        *)
(*                                                                            *)
(* ## sign proofs                                                             *)
(* ```                                                                        *)
(*    [itv of x] == proof that x is in interval inferred by x%:itv            *)
(*    [gt0 of x] == proof that x > 0                                          *)
(*    [lt0 of x] == proof that x < 0                                          *)
(*    [ge0 of x] == proof that x >= 0                                         *)
(*    [le0 of x] == proof that x <= 0                                         *)
(*   [cmp0 of x] == proof that 0 >=< x                                        *)
(*   [neq0 of x] == proof that x != 0                                         *)
(* ```                                                                        *)
(*                                                                            *)
(* ## constructors                                                            *)
(* ```                                                                        *)
(* ItvNum xr lx xu == builds a {itv R & i} from proofs xr : x \in Num.real,   *)
(*                    lx : Itv.map_itv_bound (Itv.num_sem R) l <= BLeft x     *)
(*                    xu : BRight x <= Itv.map_itv_bound (Itv.num_sem R) u    *)
(*                    where x : R with R : numDomainType                      *)
(*                    and l u : itv_bound int                                 *)
(*   ItvReal lx xu == builds a {itv R & i} from proofs                        *)
(*                    lx : Itv.map_itv_bound (Itv.num_sem R) l <= BLeft x     *)
(*                    xu : BRight x <= Itv.map_itv_bound (Itv.num_sem R) u    *)
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
(******************************************************************************)

Reserved Notation "{ 'itv' R & i }"
  (at level 0, R at level 200, i at level 200, format "{ 'itv'  R  &  i }").
Reserved Notation "{ 'i01' R }"
  (at level 0, R at level 200, format "{ 'i01'  R }").
Reserved Notation "{ 'posnum' R }" (at level 0, format "{ 'posnum'  R }").
Reserved Notation "{ 'nonneg' R }" (at level 0, format "{ 'nonneg'  R }").

Reserved Notation "x %:itv" (at level 2, format "x %:itv").
Reserved Notation "x %:i01" (at level 2, format "x %:i01").
Reserved Notation "x %:pos" (at level 2, format "x %:pos").
Reserved Notation "x %:nng" (at level 2, format "x %:nng").
Reserved Notation "x %:inum" (at level 2, format "x %:inum").
Reserved Notation "x %:num" (at level 2, format "x %:num").
Reserved Notation "x %:posnum" (at level 2, format "x %:posnum").
Reserved Notation "x %:nngnum" (at level 2, format "x %:nngnum").

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
Import GRing.Theory.
Import orderedzmod.Num.Theory numdomain.Num.Theory numfield.Num.Theory.

Local Open Scope ring_scope.
Local Open Scope order_scope.

Module Itv.

Variant t := Top | Real of interval int.

Definition sub (x y : t) :=
  match x, y with
  | _, Top => true
  | Top, Real _ => false
  | Real xi, Real yi => subitv xi yi
  end.

Definition map_itv_bound S T (f : S -> T) (b : itv_bound S) : itv_bound T :=
  match b with
  | BSide b x => BSide b (f x)
  | BInfty b => BInfty _ b
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
  (x \in Num.real)
  && let: Interval l u := i in
     x \in Interval (map_itv_bound intr l) (map_itv_bound intr u).

Definition nat_sem (i : interval int) (x : nat) : bool := Posz x \in i.

Definition posnum (R : numDomainType) of phant R :=
  def (@num_sem R) (Real `]0, +oo[).

Definition nonneg (R : numDomainType) of phant R :=
  def (@num_sem R) (Real `[0, +oo[).

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
Notation "x %:posnum" := (@r _ _ (Itv.Real `]0%Z, +oo[) x) : ring_scope.
Notation "x %:nngnum" := (@r _ _ (Itv.Real `[0%Z, +oo[) x) : ring_scope.
End Exports.
End Itv.
Export Itv.Exports.

Local Notation num_spec := (Itv.spec (@Itv.num_sem _)).
Local Notation num_def R := (Itv.def (@Itv.num_sem R)).
Local Notation num_itv_bound R := (@Itv.map_itv_bound _ R intr).

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

Lemma top_typ_subproof T f (x : T) : Itv.spec f Itv.Top x.
Proof. by []. Qed.

Canonical top_typ T f := Itv.Typ (@top_typ_subproof T f).

Lemma real_domain_typ_subproof (R : realDomainType) (x : R) :
  num_spec (Itv.Real `]-oo, +oo[) x.
Proof. by rewrite /Itv.num_sem/= num_real. Qed.

Canonical real_domain_typ (R : realDomainType) :=
  Itv.Typ (@real_domain_typ_subproof R).

Lemma real_field_typ_subproof (R : realFieldType) (x : R) :
  num_spec (Itv.Real `]-oo, +oo[) x.
Proof. exact: real_domain_typ_subproof. Qed.

Canonical real_field_typ (R : realFieldType) :=
  Itv.Typ (@real_field_typ_subproof R).

Lemma nat_typ_subproof (x : nat) : nat_spec (Itv.Real `[0, +oo[) x.
Proof. by []. Qed.

Canonical nat_typ := Itv.Typ nat_typ_subproof.

Lemma typ_inum_subproof (i : Itv.t) (xt : Itv.typ i) (x : Itv.sort xt) :
  Itv.spec (@Itv.sort_sem _ xt) i x.
Proof. by move: xt x => []. Qed.

(* This adds _ <- Itv.r ( typ_inum )
   to canonical projections (c.f., Print Canonical Projections
   Itv.r) meaning that if no other canonical instance (with a
   registered head symbol) is found, a canonical instance of
   Itv.typ, like the ones above, will be looked for. *)
Canonical typ_inum (i : Itv.t) (xt : Itv.typ i) (x : Itv.sort xt) :=
  Itv.mk (typ_inum_subproof x).

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

Definition itv_real1_subdef (op1 : interval int -> interval int)
    (x : Itv.t) : Itv.t :=
  match x with Itv.Top => Itv.Top | Itv.Real x => Itv.Real (op1 x) end.

Definition itv_real2_subdef (op2 : interval int -> interval int -> interval int)
    (x y : Itv.t) : Itv.t :=
  match x, y with
  | Itv.Top, _ | _, Itv.Top => Itv.Top
  | Itv.Real x, Itv.Real y => Itv.Real (op2 x y)
  end.

Lemma itv_real1_subproof T f (op1 : T -> T)
    (op1i : interval int -> interval int) (x : T) :
    (forall xi, f xi x = true -> f (op1i xi) (op1 x) = true) ->
  forall xi, Itv.spec f xi x ->
    Itv.spec f (itv_real1_subdef op1i xi) (op1 x).
Proof. by move=> + [//| xi]; apply. Qed.

Lemma itv_real2_subproof T f (op2 : T -> T -> T)
    (op2i : interval int -> interval int -> interval int) (x y : T) :
    (forall xi yi, f xi x = true -> f yi y = true ->
     f (op2i xi yi) (op2 x y) = true) ->
  forall xi yi, Itv.spec f xi x -> Itv.spec f yi y ->
    Itv.spec f (itv_real2_subdef op2i xi yi) (op2 x y).
Proof. by move=> + [//| xi] [//| yi]; apply. Qed.

Lemma map_itv_bound_comp S T U (f : T -> S) (g : U -> T) (b : itv_bound U) :
  Itv.map_itv_bound (f \o g) b = Itv.map_itv_bound f (Itv.map_itv_bound g b).
Proof. by case: b. Qed.

Section NumDomainTheory.
Context {R : numDomainType} {i : Itv.t}.
Implicit Type x : num_def R i.

Lemma intr_le_map_itv_bound (x y : itv_bound int) :
  (num_itv_bound R x <= num_itv_bound R y)%O = (x <= y)%O.
Proof.
by case: x y => [[] x | x] [[] y | y]//=; rewrite !bnd_simp ?ler_int ?ltr_int.
Qed.

Lemma intr_BLeft_le_map_itv_bound (x : itv_bound int) (y : int) :
  (num_itv_bound R x <= BLeft (y%:~R : R))%O = (x <= BLeft y)%O.
Proof.
rewrite -[BLeft y%:~R]/(Itv.map_itv_bound intr (BLeft y)).
by rewrite intr_le_map_itv_bound.
Qed.

Lemma BRight_intr_le_map_itv_bound (x : int) (y : itv_bound int) :
  (BRight (x%:~R : R) <= num_itv_bound R y)%O = (BRight x <= y)%O.
Proof.
rewrite -[BRight x%:~R]/(Itv.map_itv_bound intr (BRight x)).
by rewrite intr_le_map_itv_bound.
Qed.

Lemma subitv_map_itv (x y : Itv.t) : Itv.sub x y ->
  forall z : R, num_spec x z -> num_spec y z.
Proof.
case: x y => [| x] [| y] //= x_sub_y z /andP[rz]; rewrite /Itv.num_sem rz/=.
move: x y x_sub_y => [lx ux] [ly uy] /andP[lel leu] /=.
move=> /andP[lxz zux]; apply/andP; split.
- by apply: le_trans lxz; rewrite intr_le_map_itv_bound ?map_itv_bound_num.
- by apply: le_trans zux _; rewrite intr_le_map_itv_bound ?map_itv_bound_num.
Qed.

Definition empty_itv := Itv.Real `[Posz 1, Posz 0].

Lemma bottom x : unify_itv i empty_itv -> False.
Proof.
case: x => x /= /[swap] /subitv_map_itv /[apply] /andP[_] /=.
by rewrite in_itv/= => /andP[] /le_trans /[apply]; rewrite ler10.
Qed.

Lemma gt0 x : unify_itv i (Itv.Real `]Posz 0, +oo[) -> 0%R < x%:num :> R.
Proof.
case: x => x /= /[swap] /subitv_map_itv /[apply] /andP[_].
by rewrite /= in_itv/= andbT.
Qed.

Lemma le0F x : unify_itv i (Itv.Real `]Posz 0, +oo[) ->
  x%:num <= 0%R :> R = false.
Proof.
case: x => x /= /[swap] /subitv_map_itv /[apply] /andP[_] /=.
by rewrite in_itv/= andbT => /lt_geF.
Qed.

Lemma lt0 x : unify_itv i (Itv.Real `]-oo, Posz 0[) -> x%:num < 0%R :> R.
Proof.
by case: x => x /= /[swap] /subitv_map_itv /[apply] /andP[_] /=; rewrite in_itv.
Qed.

Lemma ge0F x : unify_itv i (Itv.Real `]-oo, Posz 0[) ->
  0%R <= x%:num :> R = false.
Proof.
case: x => x /= /[swap] /subitv_map_itv /[apply] /andP[_] /=.
by rewrite in_itv/= => /lt_geF.
Qed.

Lemma ge0 x : unify_itv i (Itv.Real `[Posz 0, +oo[) -> 0%R <= x%:num :> R.
Proof.
case: x => x /= /[swap] /subitv_map_itv /[apply] /andP[_] /=.
by rewrite in_itv/= andbT.
Qed.

Lemma lt0F x : unify_itv i (Itv.Real `[Posz 0, +oo[) ->
  x%:num < 0%R :> R = false.
Proof.
case: x => x /= /[swap] /subitv_map_itv /[apply] /andP[_] /=.
by rewrite in_itv/= andbT => /le_gtF.
Qed.

Lemma le0 x : unify_itv i (Itv.Real `]-oo, Posz 0]) -> x%:num <= 0%R :> R.
Proof.
by case: x => x /= /[swap] /subitv_map_itv /[apply] /andP[_] /=; rewrite in_itv.
Qed.

Lemma gt0F x : unify_itv i (Itv.Real `]-oo, Posz 0]) ->
  0%R < x%:num :> R = false.
Proof.
case: x => x /= /[swap] /subitv_map_itv /[apply] /andP[_] /=.
by rewrite in_itv/= => /le_gtF.
Qed.

Lemma cmp0 x : unify_itv i (Itv.Real `]-oo, +oo[) -> (0 >=< x%:num).
Proof. by case: i x => [//| i' [x /=/andP[]]]. Qed.

Lemma neq0 x :
  unify (fun ix iy => negb (Itv.sub ix iy)) (Itv.Real `[0%Z, 0%Z]) i ->
  x%:num != 0 :> R.
Proof.
case: i x => [//| [l u] [x /= Px]]; apply: contra => /eqP x0 /=.
move: Px; rewrite x0 => /and3P[_ /= l0 u0]; apply/andP; split.
- by case: l l0 => [[] l /= |//]; rewrite !bnd_simp ?lerz0 ?ltrz0.
- by case: u u0 => [[] u /= |//]; rewrite !bnd_simp ?ler0z ?ltr0z.
Qed.

Lemma eq0F x :
  unify (fun ix iy => negb (Itv.sub ix iy)) (Itv.Real `[0%Z, 0%Z]) i ->
  x%:num == 0 :> R = false.
Proof. by move=> u; apply/negbTE/neq0. Qed.

Lemma lt1 x : unify_itv i (Itv.Real `]-oo, Posz 1[) -> x%:num < 1%R :> R.
Proof.
by case: x => x /= /[swap] /subitv_map_itv /[apply] /andP[_] /=; rewrite in_itv.
Qed.

Lemma ge1F x : unify_itv i (Itv.Real `]-oo, Posz 1[) ->
  1%R <= x%:num :> R = false.
Proof.
case: x => x /= /[swap] /subitv_map_itv /[apply] /andP[_] /=.
by rewrite in_itv/= => /lt_geF.
Qed.

Lemma le1 x : unify_itv i (Itv.Real `]-oo, Posz 1]) -> x%:num <= 1%R :> R.
Proof.
by case: x => x /= /[swap] /subitv_map_itv /[apply] /andP[_] /=; rewrite in_itv.
Qed.

Lemma gt1F x : unify_itv i (Itv.Real `]-oo, Posz 1]) ->
  1%R < x%:num :> R = false.
Proof.
case: x => x /= /[swap] /subitv_map_itv /[apply] /andP[_] /=.
by rewrite in_itv/= => /le_gtF.
Qed.

Lemma widen_itv_subproof x i' : Itv.sub i i' -> num_spec i' x%:num.
Proof. by case: x => x /= /[swap] /subitv_map_itv; apply. Qed.

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

Notation "[ 'gt0' 'of' x ]" := (ltac:(refine (gt0 x%:itv))).
Notation "[ 'lt0' 'of' x ]" := (ltac:(refine (lt0 x%:itv))).
Notation "[ 'ge0' 'of' x ]" := (ltac:(refine (ge0 x%:itv))).
Notation "[ 'le0' 'of' x ]" := (ltac:(refine (le0 x%:itv))).
Notation "[ 'cmp0' 'of' x ]" := (ltac:(refine (cmp0 x%:itv))).
Notation "[ 'neq0' 'of' x ]" := (ltac:(refine (neq0 x%:itv))).

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
    (@Itv.from _ _ _ (Phantom _ x)) (Itv.Real `[Posz 0, Posz 1]) _)
  (only printing) : ring_scope.
Notation "x %:pos" := (widen_itv x%:itv : {posnum _}) (only parsing)
  : ring_scope.
Notation "x %:pos" := (@widen_itv _ _
    (@Itv.from _ _ _ (Phantom _ x)) (Itv.Real `]Posz 0, +oo[) _)
  (only printing) : ring_scope.
Notation "x %:nng" := (widen_itv x%:itv : {nonneg _}) (only parsing)
  : ring_scope.
Notation "x %:nng" := (@widen_itv _ _
    (@Itv.from _ _ _ (Phantom _ x)) (Itv.Real `[Posz 0, +oo[) _)
  (only printing) : ring_scope.

Local Open Scope ring_scope.

Section NumDomainInstances.
Context {R : numDomainType}.

Lemma zero_inum_subproof : num_spec (Itv.Real `[0, 0]) (0 : R).
Proof. by apply/andP; split; [exact: real0 | rewrite /= in_itv/= lexx]. Qed.

Canonical zero_inum := Itv.mk zero_inum_subproof.

Lemma one_inum_subproof : num_spec (Itv.Real `[1, 1]) (1 : R).
Proof. by apply/andP; split; [exact: real1 | rewrite /= in_itv/= lexx]. Qed.

Canonical one_inum := Itv.mk one_inum_subproof.

Definition opp_itv_bound_subdef (b : itv_bound int) : itv_bound int :=
  match b with
  | BSide b x => BSide (~~ b) (intZmod.oppz x)
  | BInfty b => BInfty _ (~~ b)
  end.

Lemma opp_itv_ge0_subproof b :
  (BLeft 0%R <= opp_itv_bound_subdef b)%O = (b <= BRight 0%R)%O.
Proof. by case: b => [[] b | []//]; rewrite /= !bnd_simp oppr_ge0. Qed.

Lemma opp_itv_gt0_subproof b :
  (BRight 0%R <= opp_itv_bound_subdef b)%O = (b <= BLeft 0%R)%O.
Proof.
by case: b => [[] b | []//]; rewrite /= !bnd_simp ?oppr_ge0 ?oppr_gt0.
Qed.

Lemma opp_itv_boundr_subproof (x : R) b :
  (BRight (- x)%R <= num_itv_bound R (opp_itv_bound_subdef b))%O
  = (num_itv_bound R b <= BLeft x)%O.
Proof.
by case: b => [[] b | []//]; rewrite /= !bnd_simp mulrNz ?lerN2 // ltrN2.
Qed.

Lemma opp_itv_boundl_subproof (x : R) b :
  (num_itv_bound R (opp_itv_bound_subdef b) <= BLeft (- x)%R)%O
  = (BRight x <= num_itv_bound R b)%O.
Proof.
by case: b => [[] b | []//]; rewrite /= !bnd_simp mulrNz ?lerN2 // ltrN2.
Qed.

Definition opp_itv_subdef (i : interval int) : interval int :=
  let: Interval l u := i in
  Interval (opp_itv_bound_subdef u) (opp_itv_bound_subdef l).
Arguments opp_itv_subdef /.

Lemma opp_inum_subproof (i : Itv.t) (x : num_def R i)
    (r := itv_real1_subdef opp_itv_subdef i) :
  num_spec r (- x%:num).
Proof.
apply: itv_real1_subproof (Itv.P x).
case: x => x /= _ [l u] /and3P[xr lx xu].
rewrite /Itv.num_sem/= realN xr/=; apply/andP.
by rewrite opp_itv_boundl_subproof opp_itv_boundr_subproof.
Qed.

Canonical opp_inum (i : Itv.t) (x : num_def R i) :=
  Itv.mk (opp_inum_subproof x).

Definition add_itv_boundl_subdef (b1 b2 : itv_bound int) : itv_bound int :=
  match b1, b2 with
  | BSide b1 x1, BSide b2 x2 => BSide (b1 && b2) (intZmod.addz x1 x2)
  | _, _ => BInfty _ true
  end.

Lemma add_itv_boundl_subproof (x1 x2 : R) b1 b2 :
  (num_itv_bound R b1 <= BLeft x1)%O -> (num_itv_bound R b2 <= BLeft x2)%O ->
  (num_itv_bound R (add_itv_boundl_subdef b1 b2) <= BLeft (x1 + x2)%R)%O.
Proof.
case: b1 b2 => [bb1 b1 |//] [bb2 b2 |//].
case: bb1; case: bb2; rewrite /= !bnd_simp mulrzDr_tmp.
- exact: lerD.
- exact: ler_ltD.
- exact: ltr_leD.
- exact: ltrD.
Qed.

Definition add_itv_boundr_subdef (b1 b2 : itv_bound int) : itv_bound int :=
  match b1, b2 with
  | BSide b1 x1, BSide b2 x2 => BSide (b1 || b2) (intZmod.addz x1 x2)
  | _, _ => BInfty _ false
  end.

Lemma add_itv_boundr_subproof (x1 x2 : R) b1 b2 :
  (BRight x1 <= num_itv_bound R b1)%O -> (BRight x2 <= num_itv_bound R b2)%O ->
  (BRight (x1 + x2)%R <= num_itv_bound R (add_itv_boundr_subdef b1 b2))%O.
Proof.
case: b1 b2 => [bb1 b1 |//] [bb2 b2 |//].
case: bb1; case: bb2; rewrite /= !bnd_simp mulrzDr_tmp.
- exact: ltrD.
- exact: ltr_leD.
- exact: ler_ltD.
- exact: lerD.
Qed.

Definition add_itv_subdef (i1 i2 : interval int) : interval int :=
  let: Interval l1 u1 := i1 in
  let: Interval l2 u2 := i2 in
  Interval (add_itv_boundl_subdef l1 l2) (add_itv_boundr_subdef u1 u2).
Arguments add_itv_subdef /.

Lemma add_inum_subproof (xi yi : Itv.t) (x : num_def R xi) (y : num_def R yi)
    (r := itv_real2_subdef add_itv_subdef xi yi) :
  num_spec r (x%:num + y%:num).
Proof.
apply: itv_real2_subproof (Itv.P x) (Itv.P y).
case: x y => [x /= _] [y /= _] => {xi yi r} -[lx ux] [ly uy]/=.
move=> /andP[xr /=/andP[lxx xux]] /andP[yr /=/andP[lyy yuy]].
rewrite /Itv.num_sem realD//=; apply/andP.
by rewrite add_itv_boundl_subproof ?add_itv_boundr_subproof.
Qed.

Canonical add_inum (xi yi : Itv.t) (x : num_def R xi) (y : num_def R yi) :=
  Itv.mk (add_inum_subproof x y).

Variant signb := EqZero | NonNeg | NonPos.

Definition itv_bound_signl (b : itv_bound int) : signb :=
  let: b0 := BLeft 0%Z in
  if b == b0 then EqZero else if (b <= b0)%O then NonPos else NonNeg.

Definition itv_bound_signr (b : itv_bound int) : signb :=
  let: b0 := BRight 0%Z in
  if b == b0 then EqZero else if (b <= b0)%O then NonPos else NonNeg.

Variant signi := Known of signb | Unknown | Empty.

Definition interval_sign (i : interval int) : signi :=
  let: Interval l u := i in
  match itv_bound_signl l, itv_bound_signr u with
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

Variant interval_sign_spec (l u : itv_bound int) (x : R) : signi -> Set :=
  | ISignEqZero : l = BLeft 0 -> u = BRight 0 -> x = 0 ->
                  interval_sign_spec l u x (Known EqZero)
  | ISignNonNeg : (BLeft 0%:Z <= l)%O -> (BRight 0%:Z < u)%O -> 0 <= x ->
                  interval_sign_spec l u x (Known NonNeg)
  | ISignNonPos : (l < BLeft 0%:Z)%O -> (u <= BRight 0%:Z)%O -> x <= 0 ->
                  interval_sign_spec l u x (Known NonPos)
  | ISignBoth : (l < BLeft 0%:Z)%O -> (BRight 0%:Z < u)%O -> x \in Num.real ->
                interval_sign_spec l u x Unknown.

Lemma interval_signP (l u : itv_bound int) (x : R) :
    (num_itv_bound R l <= BLeft x)%O -> (BRight x <= num_itv_bound R u)%O ->
    x \in Num.real ->
  interval_sign_spec l u x (interval_sign (Interval l u)).
Proof.
move=> + + xr; rewrite /interval_sign/itv_bound_signl/itv_bound_signr.
have [lneg|lpos|->] := ltgtP l; have [uneg|upos|->] := ltgtP u => lx xu.
- apply: ISignNonPos => //; first exact: ltW.
  have:= le_trans xu (eqbRL (intr_le_map_itv_bound _ _) (ltW uneg)).
  by rewrite bnd_simp.
- exact: ISignBoth.
- exact: ISignNonPos.
- have:= (@ltxx _ _ (num_itv_bound R l)).
  rewrite (le_lt_trans lx) -?leBRight_ltBLeft ?(le_trans xu)//.
  by rewrite intr_le_map_itv_bound (le_trans (ltW uneg)).
- apply: ISignNonNeg => //; first exact: ltW.
  have:= (le_trans (eqbRL (intr_le_map_itv_bound _ _) (ltW lpos)) lx).
  by rewrite bnd_simp.
- have:= (@ltxx _ _ (num_itv_bound R l)).
  rewrite (le_lt_trans lx) -?leBRight_ltBLeft ?(le_trans xu)//.
  by rewrite intr_le_map_itv_bound ?leBRight_ltBLeft.
- have:= (@ltxx _ _ (num_itv_bound R (BLeft 0%Z))).
  rewrite (le_lt_trans lx) -?leBRight_ltBLeft ?(le_trans xu)//.
  by rewrite intr_le_map_itv_bound -?ltBRight_leBLeft.
- exact: ISignNonNeg.
- apply: ISignEqZero => //.
  by apply/le_anti/andP; move: lx xu; rewrite !bnd_simp.
Qed.

Definition mul_itv_boundl_subdef (b1 b2 : itv_bound int) : itv_bound int :=
  match b1, b2 with
  | BInfty _, _
  | _, BInfty _
  | BLeft 0%Z, _
  | _, BLeft 0%Z => BLeft 0%Z
  | BSide b1 x1, BSide b2 x2 => BSide (b1 && b2) (intRing.mulz x1 x2)
  end.

Definition mul_itv_boundr_subdef (b1 b2 : itv_bound int) : itv_bound int :=
  match b1, b2 with
  | BLeft 0%Z, _
  | _, BLeft 0%Z => BLeft 0%Z
  | BRight 0%Z, _
  | _, BRight 0%Z => BRight 0%Z
  | BSide b1 x1, BSide b2 x2 => BSide (b1 || b2) (intRing.mulz x1 x2)
  | _, BInfty _
  | BInfty _, _ => +oo%O
  end.

Lemma mul_itv_boundl_subproof b1 b2 (x1 x2 : R) :
  (BLeft 0%:Z <= b1 -> BLeft 0%:Z <= b2 ->
   num_itv_bound R b1 <= BLeft x1 ->
   num_itv_bound R b2 <= BLeft x2 ->
   num_itv_bound R (mul_itv_boundl_subdef b1 b2) <= BLeft (x1 * x2))%O.
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

Lemma mul_itv_boundrC_subproof b1 b2 :
  mul_itv_boundr_subdef b1 b2 = mul_itv_boundr_subdef b2 b1.
Proof.
by move: b1 b2 => [[] [[|?]|?] | []] [[] [[|?]|?] | []] //=; rewrite mulnC.
Qed.

Lemma mul_itv_boundr_subproof b1 b2 (x1 x2 : R) :
  (0 <= x1 -> 0 <= x2 ->
   BRight x1 <= num_itv_bound R b1 ->
   BRight x2 <= num_itv_bound R b2 ->
   BRight (x1 * x2) <= num_itv_bound R (mul_itv_boundr_subdef b1 b2))%O.
Proof.
case: b1 b2 => [b1b b1 | []] [b2b b2 | []] //= x1p x2p; last first.
- case: b2b b2 => -[[|//] | //] _ x20.
  + have:= (@ltxx _ (itv_bound R) (BLeft 0%:~R)).
    by rewrite (lt_le_trans _ x20).
  + have -> : x2 = 0 by apply/le_anti/andP.
    by rewrite mulr0.
- case: b1b b1 => -[[|//] |//] x10 _.
  + have:= (@ltxx _ (itv_bound R) (BLeft 0%Z%:~R)).
    by rewrite (lt_le_trans _ x10).
  + by have -> : x1 = 0; [apply/le_anti/andP | rewrite mul0r].
case: b1b b2b => -[]; rewrite -[intRing.mulz]/GRing.mul.
- case: b1 => [[|b1] | b1]; rewrite !bnd_simp => x1b x2b.
  + by have:= (@ltxx _ R 0); rewrite (le_lt_trans x1p x1b).
  + case: b2 x2b => [[| b2] | b2] => x2b; rewrite bnd_simp.
    * by have:= (@ltxx _ R 0); rewrite (le_lt_trans x2p x2b).
    * by rewrite intrM ltr_pM.
    * have:= (@ltxx _ R 0); rewrite (le_lt_trans x2p)//.
      by rewrite (lt_le_trans x2b) ?lerz0.
  + have:= (@ltxx _ R 0); rewrite (le_lt_trans x1p)//.
    by rewrite (lt_le_trans x1b) ?lerz0.
- case: b1 => [[|b1] | b1]; rewrite !bnd_simp => x1b x2b.
  + by have:= (@ltxx _ R 0); rewrite (le_lt_trans x1p x1b).
  + case: b2 x2b => [[| b2] | b2] x2b; rewrite bnd_simp.
    * exact: mulr_ge0_le0.
    * by rewrite intrM (le_lt_trans (ler_wpM2l x1p x2b)) ?ltr_pM2r.
    * have:= (@ltxx _ _ x2).
      by rewrite (le_lt_trans x2b) ?(lt_le_trans _ x2p) ?ltrz0.
  + have:= (@ltxx _ _ x1).
    by rewrite (lt_le_trans x1b) ?(le_trans _ x1p) ?lerz0.
- case: b1 => [[|b1] | b1]; rewrite !bnd_simp => x1b x2b.
  + case: b2 x2b => [[|b2] | b2] x2b; rewrite bnd_simp.
    * by have:= (@ltxx _ _ x2); rewrite (lt_le_trans x2b).
    * by have -> : x1 = 0; [apply/le_anti/andP | rewrite mul0r].
    * have:= (@ltxx _ _ x2).
      by rewrite (lt_le_trans x2b) ?(le_trans _ x2p) ?lerz0.
  + case: b2 x2b => [[|b2] | b2] x2b; rewrite bnd_simp.
    * by have:= (@ltxx _ _ x2); rewrite (lt_le_trans x2b).
    * by rewrite intrM (le_lt_trans (ler_wpM2r x2p x1b)) ?ltr_pM2l.
    * have:= (@ltxx _ _ x2).
      by rewrite (lt_le_trans x2b) ?(le_trans _ x2p) ?lerz0.
  + have:= (@ltxx _ _ x1).
    by rewrite (le_lt_trans x1b) ?(lt_le_trans _ x1p) ?ltrz0.
- case: b1 => [[|b1] | b1]; rewrite !bnd_simp => x1b x2b.
  + by have -> : x1 = 0; [apply/le_anti/andP | rewrite mul0r].
  + case: b2 x2b => [[| b2] | b2] x2b; rewrite bnd_simp.
    * by have -> : x2 = 0; [apply/le_anti/andP | rewrite mulr0].
    * by rewrite intrM ler_pM.
    * have:= (@ltxx _ _ x2).
      by rewrite (le_lt_trans x2b) ?(lt_le_trans _ x2p) ?ltrz0.
  + have:= (@ltxx _ _ x1).
    by rewrite (le_lt_trans x1b) ?(lt_le_trans _ x1p) ?ltrz0.
Qed.

Lemma mul_itv_boundr_BRight_subproof b1 b2 :
  (BRight 0%Z <= b1 -> BRight 0%Z <= b2 ->
   BRight 0%Z <= mul_itv_boundr_subdef b1 b2)%O.
Proof.
case: b1 b2 => [b1b b1 | []] [b2b b2 | []]//=.
- by case: b1b b2b => -[]; case: b1 b2 => [[|b1] | b1] [[|b2] | b2].
- by case: b1b b1 => -[[] |].
- by case: b2b b2 => -[[] |].
Qed.

Lemma mul_itv_boundr'_subproof b1 b2 (x1 x2 : R) :
  (0 <= x1 -> x2 \in Num.real -> BRight 0%Z <= b2 ->
   BRight x1 <= num_itv_bound R b1 ->
   BRight x2 <= num_itv_bound R b2 ->
   BRight (x1 * x2) <= num_itv_bound R (mul_itv_boundr_subdef b1 b2))%O.
Proof.
move=> x1ge0 x2r b2ge0 lex1b1 lex2b2.
have /orP[x2ge0 | x2le0] := x2r; first exact: mul_itv_boundr_subproof.
have lem0 : (BRight (x1 * x2) <= BRight 0%R)%O.
  by rewrite bnd_simp mulr_ge0_le0 // ltW.
apply: le_trans lem0 _.
rewrite -(mulr0z 1) BRight_intr_le_map_itv_bound.
apply: mul_itv_boundr_BRight_subproof => //.
by rewrite -(@BRight_intr_le_map_itv_bound R) (le_trans _ lex1b1).
Qed.

Definition mul_itv_subdef (i1 i2 : interval int) : interval int :=
  let: Interval l1 u1 := i1 in
  let: Interval l2 u2 := i2 in
  let: opp := opp_itv_bound_subdef in
  let: mull := mul_itv_boundl_subdef in
  let: mulr := mul_itv_boundr_subdef in
  match interval_sign i1, interval_sign i2 with
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
Arguments mul_itv_subdef /.

Lemma comparable_num_itv_bound_subproof (x y : itv_bound int) :
  (num_itv_bound R x >=< num_itv_bound R y)%O.
Proof.
by case: x y => [[] x | []] [[] y | []]//; apply/orP;
  rewrite !bnd_simp ?ler_int ?ltr_int;
  case: leP => xy; apply/orP => //; rewrite ltW ?orbT.
Qed.

Lemma map_itv_bound_min (x y : itv_bound int) :
  num_itv_bound R (Order.min x y)
  = Order.min (num_itv_bound R x) (num_itv_bound R y).
Proof.
have [lexy | ltyx] := leP x y; [by rewrite !minEle intr_le_map_itv_bound lexy|].
rewrite minElt -if_neg -comparable_leNgt ?intr_le_map_itv_bound ?ltW//.
exact: comparable_num_itv_bound_subproof.
Qed.

Lemma map_itv_bound_max (x y : itv_bound int) :
  num_itv_bound R (Order.max x y)
  = Order.max (num_itv_bound R x) (num_itv_bound R y).
Proof.
have [lexy | ltyx] := leP x y; [by rewrite !maxEle intr_le_map_itv_bound lexy|].
rewrite maxElt -if_neg -comparable_leNgt ?intr_le_map_itv_bound ?ltW//.
exact: comparable_num_itv_bound_subproof.
Qed.

Lemma mul_inum_subproof (xi yi : Itv.t) (x : num_def R xi) (y : num_def R yi)
    (r := itv_real2_subdef mul_itv_subdef xi yi) :
  num_spec r (x%:num * y%:num).
Proof.
rewrite {}/r; case: xi yi x y => [//| [xl xu]] [//| [yl yu]].
case=> [x /=/and3P[xr /= xlx xxu]] [y /=/and3P[yr /= yly yyu]].
rewrite -/(interval_sign (Interval xl xu)) -/(interval_sign (Interval yl yu)).
have ns000 : @Itv.num_sem R `[0, 0] 0 by apply/and3P.
have xyr : x * y \in Num.real by exact: realM.
case: (interval_signP xlx xxu xr) => xlb xub xs.
- by rewrite xs mul0r; case: (interval_signP yly yyu yr).
- case: (interval_signP yly yyu yr) => ylb yub ys.
  + by rewrite ys mulr0.
  + apply/and3P; split=> //=.
    * exact: mul_itv_boundl_subproof xlx yly.
    * exact: mul_itv_boundr_subproof xxu yyu.
  + apply/and3P; split=> //=; rewrite -[x * y]opprK -mulrN.
    * rewrite opp_itv_boundl_subproof.
      by rewrite mul_itv_boundr_subproof ?oppr_ge0// opp_itv_boundr_subproof.
    * rewrite opp_itv_boundr_subproof.
      rewrite mul_itv_boundl_subproof ?opp_itv_boundl_subproof//.
      by rewrite opp_itv_ge0_subproof.
  + apply/and3P; split=> //=.
    * rewrite  -[x * y]opprK -mulrN opp_itv_boundl_subproof.
      rewrite mul_itv_boundr'_subproof ?realN ?opp_itv_boundr_subproof//.
      by rewrite opp_itv_gt0_subproof ltW.
    * by rewrite mul_itv_boundr'_subproof// ltW.
- case: (interval_signP yly yyu yr) => ylb yub ys.
  + by rewrite ys mulr0.
  + apply/and3P; split=> //=; rewrite -[x * y]opprK -mulNr.
    * rewrite opp_itv_boundl_subproof.
      by rewrite mul_itv_boundr_subproof ?oppr_ge0 ?opp_itv_boundr_subproof.
    * rewrite opp_itv_boundr_subproof.
      rewrite mul_itv_boundl_subproof ?opp_itv_boundl_subproof//.
      by rewrite opp_itv_ge0_subproof.
  + apply/and3P; split=> //=; rewrite -mulrNN.
    * by rewrite mul_itv_boundl_subproof
        ?opp_itv_ge0_subproof ?opp_itv_boundl_subproof.
    * by rewrite mul_itv_boundr_subproof ?oppr_ge0 ?opp_itv_boundr_subproof.
  + apply/and3P; split=> //=; rewrite -[x * y]opprK.
    * rewrite -mulNr opp_itv_boundl_subproof.
      rewrite mul_itv_boundr'_subproof ?oppr_ge0 ?opp_itv_boundr_subproof//.
      exact: ltW.
    * rewrite opprK -mulrNN.
      by rewrite mul_itv_boundr'_subproof ?opp_itv_boundr_subproof
              ?oppr_ge0 ?realN ?opp_itv_gt0_subproof// ltW.
- case: (interval_signP yly yyu yr) => ylb yub ys.
  + by rewrite ys mulr0.
  + apply/and3P; split=> //=; rewrite mulrC mul_itv_boundrC_subproof.
    * rewrite -[y * x]opprK -mulrN opp_itv_boundl_subproof.
      rewrite mul_itv_boundr'_subproof ?oppr_ge0 ?realN
              ?opp_itv_boundr_subproof//.
      by rewrite opp_itv_gt0_subproof ltW.
    * by rewrite mul_itv_boundr'_subproof// ltW.
  + apply/and3P; split=> //=; rewrite mulrC mul_itv_boundrC_subproof.
    * rewrite -[y * x]opprK -mulNr opp_itv_boundl_subproof.
      rewrite mul_itv_boundr'_subproof ?oppr_ge0 ?opp_itv_boundr_subproof//.
      exact: ltW.
    * rewrite -mulrNN mul_itv_boundr'_subproof ?oppr_ge0 ?realN
              ?opp_itv_boundr_subproof//.
      by rewrite opp_itv_gt0_subproof ltW.
apply/and3P; rewrite xyr/= map_itv_bound_min map_itv_bound_max.
rewrite (comparable_ge_min _ (comparable_num_itv_bound_subproof _ _)).
rewrite (comparable_le_max _ (comparable_num_itv_bound_subproof _ _)).
case: (comparable_leP xr) => [x0 | /ltW x0]; split=> //.
- apply/orP; right; rewrite -[x * y]opprK -mulrN opp_itv_boundl_subproof.
  rewrite mul_itv_boundr'_subproof ?realN ?opp_itv_boundr_subproof//.
  by rewrite opp_itv_gt0_subproof ltW.
- by apply/orP; right; rewrite mul_itv_boundr'_subproof// ltW.
- apply/orP; left; rewrite -[x * y]opprK -mulNr opp_itv_boundl_subproof.
  by rewrite mul_itv_boundr'_subproof ?oppr_ge0 ?opp_itv_boundr_subproof// ltW.
- apply/orP; left; rewrite -mulrNN.
  rewrite mul_itv_boundr'_subproof ?oppr_ge0 ?realN ?opp_itv_boundr_subproof//.
  by rewrite opp_itv_gt0_subproof ltW.
Qed.

Canonical mul_inum (xi yi : Itv.t) (x : num_def R xi) (y : num_def R yi) :=
  Itv.mk (mul_inum_subproof x y).

Definition min_itv_subdef (x y : interval int) : interval int :=
  let: Interval lx ux := x in
  let: Interval ly uy := y in
  Interval (Order.min lx ly) (Order.min ux uy).
Arguments min_itv_subdef /.

(* To backport to interval *)
Lemma comparable_BSide_min d (T : porderType d) b (x y : T) : (x >=< y)%O ->
  BSide b (Order.min x y) = Order.min (BSide b x) (BSide b y).
Proof. by rewrite !minEle bnd_simp => /comparable_leP[]. Qed.

(* To backport to interval *)
Lemma comparable_BSide_max d (T : porderType d) b (x y : T) : (x >=< y)%O ->
  BSide b (Order.max x y) = Order.max (BSide b x) (BSide b y).
Proof. by rewrite !maxEle bnd_simp => /comparable_leP[]. Qed.

(* To backport to interval *)
Lemma BSide_min d (T : orderType d) b (x y : T) : (x >=< y)%O ->
  BSide b (Order.min x y) = Order.min (BSide b x) (BSide b y).
Proof. exact: comparable_BSide_min. Qed.

(* To backport to interval *)
Lemma BSide_max d (T : orderType d) b (x y : T) : (x >=< y)%O ->
  BSide b (Order.max x y) = Order.max (BSide b x) (BSide b y).
Proof. exact: comparable_BSide_max. Qed.

(* To backport to interval *)
Lemma real_BSide_min b (x y : R) : x \in Num.real -> y \in Num.real ->
  BSide b (Order.min x y) = Order.min (BSide b x) (BSide b y).
Proof. by move=> xr yr; apply/comparable_BSide_min/real_comparable. Qed.

(* To backport to interval *)
Lemma real_BSide_max b (x y : R) : x \in Num.real -> y \in Num.real ->
  BSide b (Order.max x y) = Order.max (BSide b x) (BSide b y).
Proof. by move=> xr yr; apply/comparable_BSide_max/real_comparable. Qed.

(* To backport to order.v *)
Lemma comparable_min_le_min d (T : porderType d) (x y z t : T) :
    (x >=< y)%O -> (z >=< t)%O ->
  (x <= z)%O -> (y <= t)%O -> (Order.min x y <= Order.min z t)%O.
Proof.
move=> + + xz yt => /comparable_leP[] xy /comparable_leP[] zt //.
- exact: le_trans xy yt.
- exact: le_trans (ltW xy) xz.
Qed.

(* To backport to order.v *)
Lemma comparable_max_le_max d (T : porderType d) (x y z t : T) :
    (x >=< y)%O -> (z >=< t)%O ->
  (x <= z)%O -> (y <= t)%O -> (Order.max x y <= Order.max z t)%O.
Proof.
move=> + + xz yt => /comparable_leP[] xy /comparable_leP[] zt //.
- exact: le_trans yt (ltW zt).
- exact: le_trans xz zt.
Qed.

Lemma num_min_inum_subproof (xi yi : Itv.t) (x : num_def R xi) (y : num_def R yi)
    (r := itv_real2_subdef min_itv_subdef xi yi) :
  num_spec r (Order.min x%:num y%:num).
Proof.
apply: itv_real2_subproof (Itv.P x) (Itv.P y).
case: x y => [x /= _] [y /= _] => {xi yi r} -[lx ux] [ly uy]/=.
move=> /andP[xr /=/andP[lxx xux]] /andP[yr /=/andP[lyy yuy]].
apply/and3P; split; rewrite ?min_real//= map_itv_bound_min real_BSide_min//.
- apply: (comparable_min_le_min (comparable_num_itv_bound_subproof _ _)) => //.
  exact: real_comparable.
- apply: (comparable_min_le_min _ (comparable_num_itv_bound_subproof _ _)) => //.
  exact: real_comparable.
Qed.

Definition max_itv_subdef (x y : interval int) : interval int :=
  let: Interval lx ux := x in
  let: Interval ly uy := y in
  Interval (Order.max lx ly) (Order.max ux uy).
Arguments max_itv_subdef /.

Lemma num_max_inum_subproof (xi yi : Itv.t) (x : num_def R xi) (y : num_def R yi)
    (r := itv_real2_subdef max_itv_subdef xi yi) :
  num_spec r (Order.max x%:num y%:num).
Proof.
apply: itv_real2_subproof (Itv.P x) (Itv.P y).
case: x y => [x /= _] [y /= _] => {xi yi r} -[lx ux] [ly uy]/=.
move=> /andP[xr /=/andP[lxx xux]] /andP[yr /=/andP[lyy yuy]].
apply/and3P; split; rewrite ?max_real//= map_itv_bound_max real_BSide_max//.
- apply: (comparable_max_le_max (comparable_num_itv_bound_subproof _ _)) => //.
  exact: real_comparable.
- apply: (comparable_max_le_max _ (comparable_num_itv_bound_subproof _ _)) => //.
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
    let: r := itv_real2_subdef min_itv_subdef xi yi in
    Itv.spec min_max_sem r (Order.min x%:num y%:num);
  #[canonical=no]
  min_max_maxP : forall (xi yi : Itv.t) (x : Itv.def min_max_sem xi)
    (y : Itv.def min_max_sem yi),
    let: r := itv_real2_subdef max_itv_subdef xi yi in
    Itv.spec min_max_sem r (Order.max x%:num y%:num);
}.

(* The default instances on porderType, for min... *)
Canonical min_typ_inum d (t : min_max_typ d) (xi yi : Itv.t)
    (x : Itv.def (@min_max_sem d t) xi) (y : Itv.def (@min_max_sem d t) yi)
    (r := itv_real2_subdef min_itv_subdef xi yi) :=
  Itv.mk (min_max_minP x y).

(* ...and for max *)
Canonical max_typ_inum d (t : min_max_typ d) (xi yi : Itv.t)
    (x : Itv.def (@min_max_sem d t) xi) (y : Itv.def (@min_max_sem d t) yi)
    (r := itv_real2_subdef min_itv_subdef xi yi) :=
  Itv.mk (min_max_maxP x y).

(* Instance of the above structure for numDomainType *)
Canonical num_min_max_typ (R : numDomainType) :=
  MinMaxTyp num_min_inum_subproof num_max_inum_subproof.

Lemma nat_num_spec (i : Itv.t) (n : nat) : nat_spec i n = num_spec i (n%:R : R).
Proof.
case: i => [//| [l u]]; rewrite /= /Itv.num_sem realn/=; congr (_ && _).
- by case: l => [[] l |//]; rewrite !bnd_simp ?pmulrn ?ler_int ?ltr_int.
- by case: u => [[] u |//]; rewrite !bnd_simp ?pmulrn ?ler_int ?ltr_int.
Qed.

Lemma natmul_inum_subproof (xi ni : Itv.t) (x : num_def R xi) (n : nat_def ni)
    (r := itv_real2_subdef mul_itv_subdef xi ni) :
  num_spec r (x%:num *+ n%:num).
Proof.
have Pn : num_spec ni (n%:num%:R : R) by case: n => /= n; rewrite nat_num_spec.
by rewrite -mulr_natr -[n%:num%:R]/((Itv.Def Pn)%:num) mul_inum_subproof.
Qed.

Canonical natmul_inum (xi ni : Itv.t) (x : num_def R xi) (n : nat_def ni) :=
  Itv.mk (natmul_inum_subproof x n).

Lemma int_num_spec (i : Itv.t) (n : int) :
  num_spec i n = num_spec i (n%:~R : R).
Proof.
case: i => [//| [l u]]; rewrite /= /Itv.num_sem num_real realz/=.
congr (andb _ _).
- by case: l => [[] l |//]; rewrite !bnd_simp intz ?ler_int ?ltr_int.
- by case: u => [[] u |//]; rewrite !bnd_simp intz ?ler_int ?ltr_int.
Qed.

Lemma intmul_inum_subproof (xi ii : Itv.t)
    (x : num_def R xi) (i : num_def int ii)
    (r := itv_real2_subdef mul_itv_subdef xi ii) :
  num_spec r (x%:num *~ i%:num).
Proof.
have Pi : num_spec ii (i%:num%:~R : R) by case: i => /= i; rewrite int_num_spec.
by rewrite -mulrzr -[i%:num%:~R]/((Itv.Def Pi)%:num) mul_inum_subproof.
Qed.

Canonical intmul_inum (xi ni : Itv.t) (x : num_def R xi) (n : num_def int ni) :=
  Itv.mk (intmul_inum_subproof x n).

Definition keep_pos_itv_bound_subdef (b : itv_bound int) : itv_bound int :=
  match b with
  | BSide b (Posz 0) => BSide b 0
  | BSide _ (Posz (S _)) => BRight 0
  | BSide _ (Negz _) => -oo
  | BInfty _ => -oo
  end.
Arguments keep_pos_itv_bound_subdef /.

Lemma keep_pos_itv_bound_subproof (op : R -> R) (x : R) b :
  {homo op : x / 0 <= x} -> {homo op : x / 0 < x} ->
  (num_itv_bound R b <= BLeft x)%O ->
  (num_itv_bound R (keep_pos_itv_bound_subdef b) <= BLeft (op x))%O.
Proof.
case: b => [[] [] [| b] // | []//] hle hlt; rewrite !bnd_simp.
- exact: hle.
- by move=> blex; apply: le_lt_trans (hlt _ _) => //; apply: lt_le_trans blex.
- exact: hlt.
- by move=> bltx; apply: le_lt_trans (hlt _ _) => //; apply: le_lt_trans bltx.
Qed.

Definition keep_neg_itv_bound_subdef (b : itv_bound int) : itv_bound int :=
  match b with
  | BSide b (Posz 0) => BSide b 0
  | BSide _ (Negz _) => BLeft 0
  | BSide _ (Posz _) => +oo
  | BInfty _ => +oo
  end.
Arguments keep_neg_itv_bound_subdef /.

Lemma keep_neg_itv_bound_subproof (op : R -> R) (x : R) b :
  {homo op : x / x <= 0} -> {homo op : x / x < 0} ->
  (BRight x <= num_itv_bound R b)%O ->
  (BRight (op x) <= num_itv_bound R (keep_neg_itv_bound_subdef b))%O.
Proof.
case: b => [[] [[|//] | b] | []//] hge hgt; rewrite !bnd_simp.
- exact: hgt.
- by move=> xltb; apply: hgt; apply: lt_le_trans xltb _; rewrite lerz0.
- exact: hge.
- by move=> xleb; apply: hgt; apply: le_lt_trans xleb _; rewrite ltrz0.
Qed.

Definition inv_itv_subdef (i : interval int) : interval int :=
  let: Interval l u := i in
  Interval (keep_pos_itv_bound_subdef l) (keep_neg_itv_bound_subdef u).
Arguments inv_itv_subdef /.

Lemma inv_inum_subproof (i : Itv.t) (x : num_def R i)
    (r := itv_real1_subdef inv_itv_subdef i) :
  num_spec r (x%:num^-1).
Proof.
apply: itv_real1_subproof (Itv.P x).
case: x => x /= _ [l u] /and3P[xr /= lx xu].
rewrite /Itv.num_sem/= realV xr/=; apply/andP; split.
- apply: keep_pos_itv_bound_subproof lx.
  + by move=> ?; rewrite invr_ge0.
  + by move=> ?; rewrite invr_gt0.
- apply: keep_neg_itv_bound_subproof xu.
  + by move=> ?; rewrite invr_le0.
  + by move=> ?; rewrite invr_lt0.
Qed.

Canonical inv_inum (i : Itv.t) (x : num_def R i) :=
  Itv.mk (inv_inum_subproof x).

Definition exprn_le1_itv_bound_subdef (l u : itv_bound int) : itv_bound int :=
  if u isn't BSide _ (Posz 1) then +oo
  else if (BLeft 0%Z <= l)%O then BRight 1%Z else +oo.
Arguments exprn_le1_itv_bound_subdef /.

Lemma exprn_le1_itv_bound_subproof (x : R) n l u :
  (num_itv_bound R l <= BLeft x)%O ->
  (BRight x <= num_itv_bound R u)%O ->
  (BRight (x ^+ n) <= num_itv_bound R (exprn_le1_itv_bound_subdef l u))%O.
Proof.
case: u => [bu [[//|[|//]] |//] | []//].
rewrite /exprn_le1_itv_bound_subdef; case: (leP _ l) => [lge1 /= |//] lx xu.
rewrite bnd_simp; case: n => [| n]; rewrite ?expr0// expr_le1//.
  by case: bu xu; rewrite bnd_simp//; apply: ltW.
case: l lge1 lx => [[] l | []//]; rewrite !bnd_simp -(@ler_int R).
- exact: le_trans.
- by move=> + /ltW; apply: le_trans.
Qed.

Definition exprn_itv_subdef (i : interval int) : interval int :=
  let: Interval l u := i in
  Interval (keep_pos_itv_bound_subdef l) (exprn_le1_itv_bound_subdef l u).
Arguments exprn_itv_subdef /.

Lemma exprn_inum_subproof (i : Itv.t) (x : num_def R i) n
    (r := itv_real1_subdef exprn_itv_subdef i) :
  num_spec r (x%:num ^+ n).
Proof.
apply: (@itv_real1_subproof _ _ (fun x => x^+n) _ _ _ _ (Itv.P x)).
case: x => x /= _ [l u] /and3P[xr /= lx xu].
rewrite /Itv.num_sem realX//=; apply/andP; split.
- apply: (@keep_pos_itv_bound_subproof (fun x => x^+n)) lx.
  + exact: exprn_ge0.
  + exact: exprn_gt0.
- exact: exprn_le1_itv_bound_subproof lx xu.
Qed.

Canonical exprn_inum (i : Itv.t) (x : num_def R i) n :=
  Itv.mk (exprn_inum_subproof x n).

Lemma norm_inum_subproof {V : normedZmodType R} (x : V) :
  num_spec (Itv.Real `[0, +oo[) `|x|.
Proof. by apply/and3P; split; rewrite //= ?normr_real ?bnd_simp ?normr_ge0. Qed.

Canonical norm_inum {V : normedZmodType R} (x : V) :=
  Itv.mk (norm_inum_subproof x).

End NumDomainInstances.

Section RcfInstances.
Context {R : rcfType}.

Definition sqrt_itv_subdef (i : Itv.t) : Itv.t :=
  match i with
  | Itv.Top => Itv.Real `[0%Z, +oo[
  | Itv.Real (Interval l u) =>
    match l with
    | BSide b (Posz 0) => Itv.Real (Interval (BSide b 0%Z) +oo)
    | BSide b (Posz (S _)) => Itv.Real `]0%Z, +oo[
    | _ => Itv.Real `[0, +oo[
    end
  end.
Arguments sqrt_itv_subdef /.

Lemma sqrt_inum_subproof (i : Itv.t) (x : num_def R i)
    (r := sqrt_itv_subdef i) :
  num_spec r (Num.sqrt x%:num).
Proof.
have: Itv.num_sem `[0%Z, +oo[ (Num.sqrt x%:num).
  by apply/and3P; rewrite /= num_real !bnd_simp sqrtr_ge0.
rewrite {}/r; case: i x => [//| [[bl [l |//] |//] u]] [x /= +] _.
case: bl l => -[| l] /and3P[xr /= bx _]; apply/and3P; split=> //=;
  move: bx; rewrite !bnd_simp ?sqrtr_ge0// sqrtr_gt0;
  [exact: lt_le_trans | exact: le_lt_trans..].
Qed.

Canonical sqrt_inum (i : Itv.t) (x : num_def R i) :=
  Itv.mk (sqrt_inum_subproof x).

End RcfInstances.

(* To backport to ssrnum.v *)
Lemma real_sqrtC {R : numClosedFieldType} (x : R) : 0 <= x ->
  sqrtC x \in Num.real.
Proof. by rewrite -sqrtC_ge0; apply: ger0_real. Qed.


Section NumClosedFieldInstances.
Context {R : numClosedFieldType}.

Definition sqrtC_itv_subdef (i : Itv.t) : Itv.t :=
  match i with
  | Itv.Top => Itv.Top
  | Itv.Real (Interval l u) =>
    match l with
    | BSide b (Posz _) => Itv.Real (Interval (BSide b 0%Z) +oo)
    | _ => Itv.Top
    end
  end.
Arguments sqrtC_itv_subdef /.

Lemma sqrtC_inum_subproof (i : Itv.t) (x : num_def R i)
    (r := sqrtC_itv_subdef i) :
  num_spec r (sqrtC x%:num).
Proof.
rewrite {}/r; case: i x => [//| [l u] [x /=/and3P[xr /= lx xu]]].
case: l lx => [bl [l |//] |[]//] lx; apply/and3P; split=> //=.
  by apply: real_sqrtC; case: bl lx => /[!bnd_simp] [|/ltW]; apply: le_trans.
case: bl lx => /[!bnd_simp] lx.
- by rewrite sqrtC_ge0; apply: le_trans lx.
- by rewrite sqrtC_gt0; apply: le_lt_trans lx.
Qed.

Canonical sqrtC_inum (i : Itv.t) (x : num_def R i) :=
  Itv.mk (sqrtC_inum_subproof x).

End NumClosedFieldInstances.

Section NumDomainType.

Variable (R : numDomainType).


(* To backport to ssralg.v *)
Lemma natr_min (m n : nat) : (Order.min m n)%:R = Order.min m%:R n%:R :> R.
Proof. by rewrite !minElt ltr_nat /Order.lt/= -fun_if. Qed.

(* To backport to ssralg.v *)
Lemma natr_max (m n : nat) : (Order.max m n)%:R = Order.max m%:R n%:R :> R.
Proof. by rewrite !maxElt ltr_nat /Order.lt/= -fun_if. Qed.

End NumDomainType.

Section NatInstances.
Local Open Scope nat_scope.
Implicit Type (n : nat).

Lemma zeron_inum_subproof : nat_spec (Itv.Real `[0, 0]%Z) 0.
Proof. by []. Qed.

Canonical zeron_inum := Itv.mk zeron_inum_subproof.

Lemma succn_inum_subproof n : nat_spec (Itv.Real `[1, +oo[%Z) n.+1.
Proof. by []. Qed.

Canonical succn_inum n := Itv.mk (succn_inum_subproof n).

Lemma addn_inum_subproof (xi yi : Itv.t) (x : nat_def xi) (y : nat_def yi)
    (r := itv_real2_subdef add_itv_subdef xi yi) :
  nat_spec r (x%:num + y%:num).
Proof.
have Px : num_spec xi (x%:num%:R : int).
  by case: x => /= x; rewrite (@nat_num_spec int).
have Py : num_spec yi (y%:num%:R : int).
  by case: y => /= y; rewrite (@nat_num_spec int).
rewrite (@nat_num_spec int) natrD.
rewrite -[x%:num%:R]/((Itv.Def Px)%:num) -[y%:num%:R]/((Itv.Def Py)%:num).
exact: add_inum_subproof.
Qed.

Canonical addn_inum (xi yi : Itv.t) (x : nat_def xi) (y : nat_def yi) :=
  Itv.mk (addn_inum_subproof x y).

Lemma double_inum_subproof (i : Itv.t) (n : nat_def i)
    (r := itv_real2_subdef add_itv_subdef i i) :
  nat_spec r (n%:num.*2).
Proof. by rewrite -addnn addn_inum_subproof. Qed.

Canonical double_inum (i : Itv.t) (x : nat_def i) :=
  Itv.mk (double_inum_subproof x).

Lemma muln_inum_subproof (xi yi : Itv.t) (x : nat_def xi) (y : nat_def yi)
    (r := itv_real2_subdef mul_itv_subdef xi yi) :
  nat_spec r (x%:num * y%:num).
Proof.
have Px : num_spec xi (x%:num%:R : int).
  by case: x => /= x; rewrite (@nat_num_spec int).
have Py : num_spec yi (y%:num%:R : int).
  by case: y => /= y; rewrite (@nat_num_spec int).
rewrite (@nat_num_spec int) natrM.
rewrite -[x%:num%:R]/((Itv.Def Px)%:num) -[y%:num%:R]/((Itv.Def Py)%:num).
exact: mul_inum_subproof.
Qed.

Canonical muln_inum (xi yi : Itv.t) (x : nat_def xi) (y : nat_def yi) :=
  Itv.mk (muln_inum_subproof x y).

Lemma expn_inum_subproof (i : Itv.t) (x : nat_def i) n
    (r := itv_real1_subdef exprn_itv_subdef i) :
  nat_spec r (x%:num ^ n).
Proof.
have Px : num_spec i (x%:num%:R : int).
  by case: x => /= x; rewrite (@nat_num_spec int).
rewrite (@nat_num_spec int) natrX -[x%:num%:R]/((Itv.Def Px)%:num).
exact: exprn_inum_subproof.
Qed.

Canonical expn_inum (i : Itv.t) (x : nat_def i) n :=
  Itv.mk (expn_inum_subproof x n).


Lemma minn_inum_subproof (xi yi : Itv.t) (x : nat_def xi) (y : nat_def yi)
    (r := itv_real2_subdef min_itv_subdef xi yi) :
  nat_spec r (minn x%:num y%:num).
Proof.
have Px : num_spec xi (x%:num%:R : int).
  by case: x => /= x; rewrite (@nat_num_spec int).
have Py : num_spec yi (y%:num%:R : int).
  by case: y => /= y; rewrite (@nat_num_spec int).
rewrite (@nat_num_spec int) -minEnat natr_min.
rewrite -[x%:num%:R]/((Itv.Def Px)%:num) -[y%:num%:R]/((Itv.Def Py)%:num).
exact: num_min_inum_subproof.
Qed.

Canonical minn_inum (xi yi : Itv.t) (x : nat_def xi) (y : nat_def yi) :=
  Itv.mk (minn_inum_subproof x y).

Lemma maxn_inum_subproof (xi yi : Itv.t) (x : nat_def xi) (y : nat_def yi)
    (r := itv_real2_subdef max_itv_subdef xi yi) :
  nat_spec r (maxn x%:num y%:num).
Proof.
have Px : num_spec xi (x%:num%:R : int).
  by case: x => /= x; rewrite (@nat_num_spec int).
have Py : num_spec yi (y%:num%:R : int).
  by case: y => /= y; rewrite (@nat_num_spec int).
rewrite (@nat_num_spec int) -maxEnat natr_max.
rewrite -[x%:num%:R]/((Itv.Def Px)%:num) -[y%:num%:R]/((Itv.Def Py)%:num).
exact: num_max_inum_subproof.
Qed.

Canonical maxn_inum (xi yi : Itv.t) (x : nat_def xi) (y : nat_def yi) :=
  Itv.mk (maxn_inum_subproof x y).

Canonical nat_min_max_typ :=
  MinMaxTyp minn_inum_subproof maxn_inum_subproof.

End NatInstances.

Section IntInstances.

Lemma Posz_inum_subproof n : num_spec (Itv.Real `[0, +oo[) (Posz n).
Proof. by apply/and3P; rewrite /= num_real !bnd_simp. Qed.

Canonical Posz_inum n := Itv.mk (Posz_inum_subproof n).

Lemma Negz_inum_subproof n : num_spec (Itv.Real `]-oo, -1]) (Negz n).
Proof. by apply/and3P; rewrite /= num_real !bnd_simp. Qed.

Canonical Negz_inum n := Itv.mk (Negz_inum_subproof n).

End IntInstances.

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
  a <= Num.max x%:num y%:num = (a <= x%:num) || (a <= y%:num).
Proof. by rewrite -comparable_le_max// real_comparable. Qed.

Lemma num_ge_max a x y :
  Num.max x%:num y%:num <= a = (x%:num <= a) && (y%:num <= a).
Proof. by rewrite -comparable_ge_max// real_comparable. Qed.

Lemma num_le_min a x y :
  a <= Num.min x%:num y%:num = (a <= x%:num) && (a <= y%:num).
Proof. by rewrite -comparable_le_min// real_comparable. Qed.

Lemma num_ge_min a x y :
  Num.min x%:num y%:num <= a = (x%:num <= a) || (y%:num <= a).
Proof. by rewrite -comparable_ge_min// real_comparable. Qed.

Lemma num_lt_max a x y :
  a < Num.max x%:num y%:num = (a < x%:num) || (a < y%:num).
Proof. by rewrite -comparable_lt_max// real_comparable. Qed.

Lemma num_gt_max a x y :
  Num.max x%:num  y%:num < a = (x%:num < a) && (y%:num < a).
Proof. by rewrite -comparable_gt_max// real_comparable. Qed.

Lemma num_lt_min a x y :
  a < Num.min x%:num y%:num = (a < x%:num) && (a < y%:num).
Proof. by rewrite -comparable_lt_min// real_comparable. Qed.

Lemma num_gt_min a x y :
  Num.min x%:num y%:num < a = (x%:num < a) || (y%:num < a).
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

Reserved Notation "`1- x" (format "`1- x", at level 2).

Section onem.
Variable R : numDomainType.
Implicit Types r : R.

Definition onem r := 1 - r.
Local Notation "`1- r" := (onem r).

Lemma onem0 : `1-0 = 1. Proof. by rewrite /onem subr0. Qed.

Lemma onem1 : `1-1 = 0. Proof. by rewrite /onem subrr. Qed.

Lemma onemK r : `1-(`1-r) = r. Proof. exact: subKr. Qed.

Lemma add_onemK r : r + `1- r = 1.
Proof. by rewrite /onem addrC subrK. Qed.

Lemma onem_gt0 r : r < 1 -> 0 < `1-r. Proof. by rewrite subr_gt0. Qed.

Lemma onem_ge0 r : r <= 1 -> 0 <= `1-r.
Proof. by rewrite le_eqVlt => /predU1P[->|/onem_gt0/ltW]; rewrite ?onem1. Qed.

Lemma onem_le1 r : 0 <= r -> `1-r <= 1.
Proof. by rewrite lerBlDr lerDl. Qed.

Lemma onem_lt1 r : 0 < r -> `1-r < 1.
Proof. by rewrite ltrBlDr ltrDl. Qed.

Lemma onemX_ge0 r n : 0 <= r -> r <= 1 -> 0 <= `1-(r ^+ n).
Proof. by move=> ? ?; rewrite subr_ge0 exprn_ile1. Qed.

Lemma onemX_lt1 r n : 0 < r -> `1-(r ^+ n) < 1.
Proof. by move=> ?; rewrite onem_lt1// exprn_gt0. Qed.

Lemma onemD r s : `1-(r + s) = `1-r - s.
Proof. by rewrite /onem addrAC opprD addrA addrAC. Qed.

Lemma onemMr r s : s * `1-r = s - s * r.
Proof. by rewrite /onem mulrBr mulr1. Qed.

Lemma onemM r s : `1-(r * s) = `1-r + `1-s - `1-r * `1-s.
Proof.
rewrite /onem mulrBr mulr1 mulrBl mul1r opprB -addrA.
by rewrite (addrC (1 - r)) !addrA subrK opprB addrA subrK addrK.
Qed.

End onem.
Notation "`1- r" := (onem r) : ring_scope.

Lemma onemV (F : numFieldType) (x : F) : x != 0 -> `1-(x^-1) = (x - 1) / x.
Proof. by move=> ?; rewrite mulrDl divff// mulN1r. Qed.

Module Test3.
Section Test3.
Variable R : realDomainType.

Definition s_of_pq (p q : {i01 R}) : {i01 R} :=
  (1 - ((1 - p%:num)%:i01%:num * (1 - q%:num)%:i01%:num))%:i01.

Lemma s_of_p0 (p : {i01 R}) : s_of_pq p 0%:i01 = p.
Proof. by apply/val_inj; rewrite /= subr0 mulr1 subKr. Qed.

Canonical onem_itv01 (p : {i01 R}) : {i01 R} :=
  @Itv.mk _ _ _ (onem p%:num) [itv of 1 - p%:num].

Definition s_of_pq' (p q : {i01 R}) : {i01 R} :=
  (`1- (`1-(p%:num) * `1-(q%:num)))%:i01.

End Test3.
End Test3.

(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import ssrAC div fintype path bigop order finset fingroup.
From mathcomp Require Import ssralg poly.

(******************************************************************************)
(*                            Number structures                               *)
(*                                                                            *)
(* NB: See CONTRIBUTING.md for an introduction to HB concepts and commands.   *)
(*                                                                            *)
(* This file defines some classes to manipulate number structures, i.e,       *)
(* structures with an order and a norm. To use this file, insert              *)
(* "Import Num.Theory." before your scripts. You can also "Import Num.Def."   *)
(* to enjoy shorter notations (e.g., minr instead of Num.min, lerif instead   *)
(* of Num.leif, etc.).                                                        *)
(*                                                                            *)
(* This file defines the following number structures:                         *)
(*                                                                            *)
(*  porderZmodType == join of Order.POrder and GRing.Zmodule                  *)
(*                    The HB class is called POrderedZmodule.                 *)
(*  normedZmodType == Zmodule with a norm                                     *)
(*                    The HB class is called NormedZmodule.                   *)
(*   numDomainType == Integral domain with an order and a norm                *)
(*                    The HB class is called NumDomain.                       *)
(*    numFieldType == Field with an order and a norm                          *)
(*                    The HB class is called NumField.                        *)
(* numClosedFieldType == Partially ordered Closed Field with conjugation      *)
(*                    The HB class is called ClosedField.                     *)
(*  realDomainType == Num domain where all elements are positive or negative  *)
(*                    The HB class is called RealDomain.                      *)
(*   realFieldType == Num Field where all elements are positive or negative   *)
(*                    The HB class is called RealField.                       *)
(*         rcfType == A Real Field with the real closed axiom                 *)
(*                    The HB class is called RealClosedField.                 *)
(*                                                                            *)
(* The ordering symbols and notations (<, <=, >, >=, _ <= _ ?= iff _,         *)
(* _ < _ ?<= if _, >=<, and ><) and lattice operations (meet and join)        *)
(* defined in order.v are redefined for the ring_display in the ring_scope    *)
(* (%R). 0-ary ordering symbols for the ring_display have the suffix "%R",    *)
(* e.g., <%R. All the other ordering notations are the same as order.v.       *)
(*                                                                            *)
(* Over these structures, we have the following operations:                   *)
(*             `|x| == norm of x                                              *)
(*         Num.sg x == sign of x: equal to 0 iff x = 0, to 1 iff x > 0, and   *)
(*                     to -1 in all other cases (including x < 0)             *)
(*  x \is a Num.pos <=> x is positive (:= x > 0)                              *)
(*  x \is a Num.neg <=> x is negative (:= x < 0)                              *)
(* x \is a Num.nneg <=> x is positive or 0 (:= x >= 0)                        *)
(* x \is a Num.npos <=> x is negative or 0 (:= x <= 0)                        *)
(* x \is a Num.real <=> x is real (:= x >= 0 or x < 0)                        *)
(*       Num.sqrt x == in a real-closed field, a positive square root of x if *)
(*                     x >= 0, or 0 otherwise                                 *)
(* For numeric algebraically closed fields we provide the generic definitions *)
(*         'i == the imaginary number (:= sqrtC (-1))                         *)
(*      'Re z == the real component of z                                      *)
(*      'Im z == the imaginary component of z                                 *)
(*        z^* == the complex conjugate of z (:= conjC z)                      *)
(*    sqrtC z == a nonnegative square root of z, i.e., 0 <= sqrt x if 0 <= x  *)
(*  n.-root z == more generally, for n > 0, an nth root of z, chosen with a   *)
(*               minimal non-negative argument for n > 1 (i.e., with a        *)
(*               maximal real part subject to a nonnegative imaginary part)   *)
(*               Note that n.-root (-1) is a primitive 2nth root of unity,    *)
(*               an thus not equal to -1 for n odd > 1 (this will be shown in *)
(*               file cyclotomic.v).                                          *)
(*                                                                            *)
(* - list of prefixes :                                                       *)
(*   p : positive                                                             *)
(*   n : negative                                                             *)
(*   sp : strictly positive                                                   *)
(*   sn : strictly negative                                                   *)
(*   i : interior = in [0, 1] or ]0, 1[                                       *)
(*   e : exterior = in [1, +oo[ or ]1; +oo[                                   *)
(*   w : non strict (weak) monotony                                           *)
(*                                                                            *)
(* Pdeg2.NumClosed : theory of the degree 2 polynomials on NumClosedField.    *)
(* Pdeg2.NumClosedMonic : theory of Pdeg2.NumClosed specialized to monic      *)
(*   polynomials.                                                             *)
(* Pdeg2.Real : theory of the degree 2 polynomials on RealField and rcfType.  *)
(* Pdeg2.RealMonic : theory of Pdeg2.Real specialized to monic polynomials.   *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "n .-root" (at level 2, format "n .-root").
Reserved Notation "'i" (at level 0).
Reserved Notation "'Re z" (at level 10, z at level 8).
Reserved Notation "'Im z" (at level 10, z at level 8).

Local Open Scope order_scope.
Local Open Scope group_scope.
Local Open Scope ring_scope.
Import Order.TTheory GRing.Theory.

Fact ring_display : Order.disp_t. Proof. exact. Qed.

Module Num.

#[short(type="porderZmodType")]
HB.structure Definition POrderedZmodule :=
  { R of Order.isPOrder ring_display R & GRing.Zmodule R }.

HB.mixin Record Zmodule_isNormed (R : POrderedZmodule.type) M
         of GRing.Zmodule M := {
  norm : M -> R;
  ler_normD : forall x y, norm (x + y) <= norm x + norm y;
  normr0_eq0 : forall x, norm x = 0 -> x = 0;
  normrMn : forall x n, norm (x *+ n) = norm x *+ n;
  normrN : forall x, norm (- x) = norm x;
}.

#[short(type="normedZmodType")]
HB.structure Definition NormedZmodule (R : porderZmodType) :=
  { M of Zmodule_isNormed R M & GRing.Zmodule M }.
Arguments norm {R M} x : rename.

Module NormedZmoduleExports.
Bind Scope ring_scope with NormedZmodule.sort.
(* Notation "[ 'normedZmodType' R 'of' T 'for' cT ]" :=
  (@clone _ (Phant R) T cT _ idfun)
  (at level 0, format "[ 'normedZmodType'  R  'of'  T  'for'  cT ]") :
  form_scope.
Notation "[ 'normedZmodType' R 'of' T ]" := (@clone _ (Phant R) T _ _ id)
  (at level 0, format "[ 'normedZmodType'  R  'of'  T ]") : form_scope. *)
End NormedZmoduleExports.
HB.export NormedZmoduleExports.

HB.mixin Record isNumRing R of GRing.NzRing R & POrderedZmodule R
  & NormedZmodule (POrderedZmodule.clone R _) R := {
 addr_gt0 : forall x y : R, 0 < x -> 0 < y -> 0 < (x + y);
 ger_leVge : forall x y : R, 0 <= x -> 0 <= y -> (x <= y) || (y <= x);
 normrM : {morph (norm : R -> R) : x y / x * y};
 ler_def : forall x y : R, (x <= y) = (norm (y - x) == (y - x));
}.

#[short(type="numDomainType")]
HB.structure Definition NumDomain := { R of
     GRing.IntegralDomain R &
     POrderedZmodule R &
     NormedZmodule (POrderedZmodule.clone R _) R &
     isNumRing R
  }.
Arguments addr_gt0 {_} [x y] : rename.
Arguments ger_leVge {_} [x y] : rename.

(* TODO: make isNumDomain depend on intermediate structures *)
(* TODO: make isNumDomain.sort canonically a NumDomain *)

Module NumDomainExports.
Bind Scope ring_scope with NumDomain.sort.
End NumDomainExports.
HB.export NumDomainExports.

Module Import Def.

Notation normr := norm.
Notation "`| x |" := (norm x) : ring_scope.

Notation ler := (@Order.le ring_display _) (only parsing).
Notation "@ 'ler' R" := (@Order.le ring_display R)
  (at level 10, R at level 8, only parsing) : function_scope.
Notation ltr := (@Order.lt ring_display _) (only parsing).
Notation "@ 'ltr' R" := (@Order.lt ring_display R)
  (at level 10, R at level 8, only parsing) : function_scope.
Notation ger := (@Order.ge ring_display _) (only parsing).
Notation "@ 'ger' R" := (@Order.ge ring_display R)
  (at level 10, R at level 8, only parsing) : function_scope.
Notation gtr := (@Order.gt ring_display _) (only parsing).
Notation "@ 'gtr' R" := (@Order.gt ring_display R)
  (at level 10, R at level 8, only parsing) : function_scope.
Notation lerif := (@Order.leif ring_display _) (only parsing).
Notation "@ 'lerif' R" := (@Order.leif ring_display R)
  (at level 10, R at level 8, only parsing) : function_scope.
Notation lterif := (@Order.lteif ring_display _) (only parsing).
Notation "@ 'lteif' R" := (@Order.lteif ring_display R)
  (at level 10, R at level 8, only parsing) : function_scope.
Notation comparabler := (@Order.comparable ring_display _) (only parsing).
Notation "@ 'comparabler' R" := (@Order.comparable ring_display R)
  (at level 10, R at level 8, only parsing) : function_scope.
Notation maxr := (@Order.max ring_display _).
Notation "@ 'maxr' R" := (@Order.max ring_display R)
    (at level 10, R at level 8, only parsing) : function_scope.
Notation minr := (@Order.min ring_display _).
Notation "@ 'minr' R" := (@Order.min ring_display R)
  (at level 10, R at level 8, only parsing) : function_scope.

Section NumDomainDef.
Context {R : numDomainType}.

Definition sgr (x : R) : R := if x == 0 then 0 else if x < 0 then -1 else 1.
Definition Rpos_pred := fun x : R => 0 < x.
Definition Rpos : qualifier 0 R := [qualify x | Rpos_pred x].
Definition Rneg_pred := fun x : R => x < 0.
Definition Rneg : qualifier 0 R := [qualify x : R | Rneg_pred x].
Definition Rnneg_pred := fun x : R => 0 <= x.
Definition Rnneg : qualifier 0 R := [qualify x : R | Rnneg_pred x].
Definition Rnpos_pred := fun x : R => x <= 0.
Definition Rnpos : qualifier 0 R := [qualify x : R | Rnpos_pred x].
Definition Rreal_pred := fun x : R => (0 <= x) || (x <= 0).
Definition Rreal : qualifier 0 R := [qualify x : R | Rreal_pred x].

End NumDomainDef.

End Def.

Arguments Rpos_pred _ _ /.
Arguments Rneg_pred _ _ /.
Arguments Rnneg_pred _ _ /.
Arguments Rreal_pred _ _ /.

(* Shorter qualified names, when Num.Def is not imported. *)
Notation le := ler (only parsing).
Notation lt := ltr (only parsing).
Notation ge := ger (only parsing).
Notation gt := gtr (only parsing).
Notation leif := lerif (only parsing).
Notation lteif := lterif (only parsing).
Notation comparable := comparabler (only parsing).
Notation sg := sgr.
Notation max := maxr.
Notation min := minr.
Notation pos := Rpos.
Notation neg := Rneg.
Notation nneg := Rnneg.
Notation npos := Rnpos.
Notation real := Rreal.

(* (Exported) symbolic syntax. *)
Module Import Syntax.
Import Def.

Notation "`| x |" := (norm x) : ring_scope.

Notation "<=%R" := le : function_scope.
Notation ">=%R" := ge : function_scope.
Notation "<%R" := lt : function_scope.
Notation ">%R" := gt : function_scope.
Notation "<?=%R" := leif : function_scope.
Notation "<?<=%R" := lteif : function_scope.
Notation ">=<%R" := comparable : function_scope.
Notation "><%R" := (fun x y => ~~ (comparable x y)) : function_scope.

Notation "<= y" := (ge y) : ring_scope.
Notation "<= y :> T" := (<= (y : T)) (only parsing) : ring_scope.
Notation ">= y"  := (le y) : ring_scope.
Notation ">= y :> T" := (>= (y : T)) (only parsing) : ring_scope.

Notation "< y" := (gt y) : ring_scope.
Notation "< y :> T" := (< (y : T)) (only parsing) : ring_scope.
Notation "> y" := (lt y) : ring_scope.
Notation "> y :> T" := (> (y : T)) (only parsing) : ring_scope.

Notation "x <= y" := (le x y) : ring_scope.
Notation "x <= y :> T" := ((x : T) <= (y : T)) (only parsing) : ring_scope.
Notation "x >= y" := (y <= x) (only parsing) : ring_scope.
Notation "x >= y :> T" := ((x : T) >= (y : T)) (only parsing) : ring_scope.

Notation "x < y"  := (lt x y) : ring_scope.
Notation "x < y :> T" := ((x : T) < (y : T)) (only parsing) : ring_scope.
Notation "x > y"  := (y < x) (only parsing) : ring_scope.
Notation "x > y :> T" := ((x : T) > (y : T)) (only parsing) : ring_scope.

Notation "x <= y <= z" := ((x <= y) && (y <= z)) : ring_scope.
Notation "x < y <= z" := ((x < y) && (y <= z)) : ring_scope.
Notation "x <= y < z" := ((x <= y) && (y < z)) : ring_scope.
Notation "x < y < z" := ((x < y) && (y < z)) : ring_scope.

Notation "x <= y ?= 'iff' C" := (lerif x y C) : ring_scope.
Notation "x <= y ?= 'iff' C :> R" := ((x : R) <= (y : R) ?= iff C)
  (only parsing) : ring_scope.

Notation "x < y ?<= 'if' C" := (lterif x y C) : ring_scope.
Notation "x < y ?<= 'if' C :> R" := ((x : R) < (y : R) ?<= if C)
  (only parsing) : ring_scope.

Notation ">=< y" := [pred x | comparable x y] : ring_scope.
Notation ">=< y :> T" := (>=< (y : T)) (only parsing) : ring_scope.
Notation "x >=< y" := (comparable x y) : ring_scope.

Notation ">< y" := [pred x | ~~ comparable x y] : ring_scope.
Notation ">< y :> T" := (>< (y : T)) (only parsing) : ring_scope.
Notation "x >< y" := (~~ (comparable x y)) : ring_scope.

Export Order.POCoercions.

End Syntax.

Section ExtensionAxioms.

Variable R : numDomainType.

Definition real_axiom : Prop := forall x : R, x \is real.

Definition archimedean_axiom : Prop := forall x : R, exists ub, `|x| < ub%:R.

Definition real_closed_axiom : Prop :=
  forall (p : {poly R}) (a b : R),
    a <= b -> p.[a] <= 0 <= p.[b] -> exists2 x, a <= x <= b & root p x.

End ExtensionAxioms.

(* The rest of the numbers interface hierarchy. *)

#[short(type="numFieldType")]
HB.structure Definition NumField := { R of GRing.UnitRing_isField R &
     GRing.IntegralDomain R &
     POrderedZmodule R &
     NormedZmodule (POrderedZmodule.clone R _) R &
     isNumRing R }.

Module NumFieldExports.
Bind Scope ring_scope with NumField.sort.
End NumFieldExports.
HB.export NumFieldExports.

HB.mixin Record NumField_isImaginary R of NumField R := {
  imaginary : R;
  conj_op : {rmorphism R -> R};
  sqrCi : imaginary ^+ 2 = - 1;
  normCK : forall x, `|x| ^+ 2 = x * conj_op x;
}.

#[short(type="numClosedFieldType")]
HB.structure Definition ClosedField :=
  { R of NumField_isImaginary R & GRing.ClosedField R & NumField R }.

Module ClosedFieldExports.
Bind Scope ring_scope with ClosedField.sort.
End ClosedFieldExports.
HB.export ClosedFieldExports.

#[short(type="realDomainType")]
HB.structure Definition RealDomain :=
  { R of Order.Total ring_display R & NumDomain R }.

Module RealDomainExports.
Bind Scope ring_scope with RealDomain.sort.
End RealDomainExports.
HB.export RealDomainExports.

#[short(type="realFieldType")]
HB.structure Definition RealField :=
  { R of Order.Total ring_display R & NumField R }.

Module RealFieldExports.
Bind Scope ring_scope with RealField.sort.
End RealFieldExports.
HB.export RealFieldExports.

HB.mixin Record RealField_isClosed R of RealField R := {
  poly_ivt_subproof : real_closed_axiom R
}.

#[short(type="rcfType")]
HB.structure Definition RealClosedField :=
  { R of RealField_isClosed R & RealField R }.

Module RealClosedFieldExports.
Bind Scope ring_scope with RealClosedField.sort.
End RealClosedFieldExports.
HB.export RealClosedFieldExports.

(* The elementary theory needed to support the definition of the derived      *)
(* operations for the extensions described above.                             *)
Module Import Internals.

Section NumDomain.
Variable R : numDomainType.
Implicit Types x y : R.

(* Basic consequences (just enough to get predicate closure properties). *)

Lemma ger0_def x : (0 <= x) = (`|x| == x).
Proof. by rewrite ler_def subr0. Qed.

Lemma subr_ge0 x y : (0 <= x - y) = (y <= x).
Proof. by rewrite ger0_def -ler_def. Qed.

Lemma oppr_ge0 x : (0 <= - x) = (x <= 0).
Proof. by rewrite -sub0r subr_ge0. Qed.

Lemma ler01 : 0 <= 1 :> R.
Proof.
have n1_nz: `|1 : R| != 0 by apply: contraNneq (@oner_neq0 R) => /normr0_eq0->.
by rewrite ger0_def -(inj_eq (mulfI n1_nz)) -normrM !mulr1.
Qed.

Lemma ltr01 : 0 < 1 :> R. Proof. by rewrite lt_def oner_neq0 ler01. Qed.

Lemma le0r x : (0 <= x) = (x == 0) || (0 < x).
Proof. by rewrite le_eqVlt eq_sym. Qed.

Lemma addr_ge0 x y : 0 <= x -> 0 <= y -> 0 <= x + y.
Proof.
rewrite le0r; case/predU1P=> [-> | x_pos]; rewrite ?add0r // le0r.
by case/predU1P=> [-> | y_pos]; rewrite ltW ?addr0 ?addr_gt0.
Qed.

Lemma pmulr_rgt0 x y : 0 < x -> (0 < x * y) = (0 < y).
Proof.
rewrite !lt_def !ger0_def normrM mulf_eq0 negb_or => /andP[x_neq0 /eqP->].
by rewrite x_neq0 (inj_eq (mulfI x_neq0)).
Qed.

(* Closure properties of the real predicates. *)

Lemma posrE x : (x \is pos) = (0 < x). Proof. by []. Qed.
Lemma nnegrE x : (x \is nneg) = (0 <= x). Proof. by []. Qed.
Lemma realE x : (x \is real) = (0 <= x) || (x <= 0). Proof. by []. Qed.

Fact pos_divr_closed : divr_closed (@pos R).
Proof.
split=> [|x y x_gt0 y_gt0]; rewrite posrE ?ltr01 //.
have [Uy|/invr_out->] := boolP (y \is a GRing.unit); last by rewrite pmulr_rgt0.
by rewrite -(pmulr_rgt0 _ y_gt0) mulrC divrK.
Qed.
#[export]
HB.instance Definition _ := GRing.isDivClosed.Build R Rpos_pred
  pos_divr_closed.

Fact nneg_divr_closed : divr_closed (@nneg R).
Proof.
split=> [|x y]; rewrite !nnegrE ?ler01 ?le0r // -!posrE.
case/predU1P=> [-> _ | x_gt0]; first by rewrite mul0r eqxx.
by case/predU1P=> [-> | y_gt0]; rewrite ?invr0 ?mulr0 ?eqxx // orbC rpred_div.
Qed.
#[export]
HB.instance Definition _ := GRing.isDivClosed.Build R Rnneg_pred
  nneg_divr_closed.

Fact nneg_addr_closed : addr_closed (@nneg R).
Proof. by split; [apply: lexx | apply: addr_ge0]. Qed.
#[export]
HB.instance Definition _ := GRing.isAddClosed.Build R Rnneg_pred
  nneg_addr_closed.

Fact real_oppr_closed : oppr_closed (@real R).
Proof. by move=> x; rewrite /= !realE oppr_ge0 orbC -!oppr_ge0 opprK. Qed.
#[export]
HB.instance Definition _ := GRing.isOppClosed.Build R Rreal_pred
  real_oppr_closed.

Fact real_addr_closed : addr_closed (@real R).
Proof.
split=> [|x y Rx Ry]; first by rewrite realE lexx.
without loss{Rx} x_ge0: x y Ry / 0 <= x.
  case/orP: Rx => [? | x_le0]; first exact.
  by rewrite -rpredN opprD; apply; rewrite ?rpredN ?oppr_ge0.
case/orP: Ry => [y_ge0 | y_le0]; first by rewrite realE -nnegrE rpredD.
by rewrite realE -[y]opprK orbC -oppr_ge0 opprB !subr_ge0 ger_leVge ?oppr_ge0.
Qed.
#[export]
HB.instance Definition _ := GRing.isAddClosed.Build R Rreal_pred
  real_addr_closed.

Fact real_divr_closed : divr_closed (@real R).
Proof.
split=> [|x y Rx Ry]; first by rewrite realE ler01.
without loss{Rx} x_ge0: x / 0 <= x.
  case/orP: Rx => [? | x_le0]; first exact.
  by rewrite -rpredN -mulNr; apply; rewrite ?oppr_ge0.
without loss{Ry} y_ge0: y / 0 <= y; last by rewrite realE -nnegrE rpred_div.
case/orP: Ry => [? | y_le0]; first exact.
by rewrite -rpredN -mulrN -invrN; apply; rewrite ?oppr_ge0.
Qed.
#[export]
HB.instance Definition _ := GRing.isDivClosed.Build R Rreal_pred
  real_divr_closed.

End NumDomain.

Lemma num_real (R : realDomainType) (x : R) : x \is real.
Proof. exact: le_total. Qed.

Section RealClosed.
Variable R : rcfType.

Lemma poly_ivt : real_closed_axiom R. Proof. exact: poly_ivt_subproof. Qed.

Fact sqrtr_subproof (x : R) :
  exists2 y, 0 <= y & (if 0 <= x then y ^+ 2 == x else y == 0) : bool.
Proof.
case x_ge0: (0 <= x); last by exists 0.
have le0x1: 0 <= x + 1 by rewrite -nnegrE rpredD ?rpred1.
have [|y /andP[y_ge0 _]] := @poly_ivt ('X^2 - x%:P) _ _ le0x1.
  rewrite !hornerE -subr_ge0 add0r expr0n sub0r opprK x_ge0 sqrrD mulr1.
  by rewrite addrAC !addrA addrK -nnegrE !rpredD ?rpredX ?rpred1.
by rewrite rootE !hornerE subr_eq0; exists y.
Qed.

End RealClosed.

Module Exports. HB.reexport. End Exports.

End Internals.

Module PredInstances.

Export Internals.Exports.

End PredInstances.

Module Import ExtraDef.

Definition sqrtr {R} x := s2val (sig2W (@sqrtr_subproof R x)).

End ExtraDef.

Notation sqrt := sqrtr.

Module Import Theory.

Section NumIntegralDomainTheory.

Variable R : numDomainType.
Implicit Types (V : normedZmodType R) (x y z t : R).

(* Lemmas from the signature (reexported). *)

Definition ler_normD V (x y : V) : `|x + y| <= `|x| + `|y| :=
  ler_normD x y.
Definition addr_gt0 x y : 0 < x -> 0 < y -> 0 < x + y := @addr_gt0 R x y.
Definition normr0_eq0 V (x : V) : `|x| = 0 -> x = 0 :=
  @normr0_eq0 R V x.
Definition ger_leVge x y : 0 <= x -> 0 <= y -> (x <= y) || (y <= x) :=
  @ger_leVge R x y.
Definition normrM : {morph norm : x y / (x : R) * y} := @normrM R.
Definition ler_def x y : (x <= y) = (`|y - x| == y - x) := ler_def x y.
Definition normrMn V (x : V) n : `|x *+ n| = `|x| *+ n := normrMn x n.
Definition normrN V (x : V) : `|- x| = `|x| := normrN x.

(* Predicate definitions. *)

Lemma posrE x : (x \is pos) = (0 < x). Proof. by []. Qed.
Lemma negrE x : (x \is neg) = (x < 0). Proof. by []. Qed.
Lemma nnegrE x : (x \is nneg) = (0 <= x). Proof. by []. Qed.
Lemma nposrE x : (x \is npos) = (x <= 0). Proof. by []. Qed.
Lemma realE x : (x \is real) = (0 <= x) || (x <= 0). Proof. by []. Qed.

(* General properties of <= and < *)

Lemma lt0r x : (0 < x) = (x != 0) && (0 <= x). Proof. exact: lt_def. Qed.
Lemma le0r x : (0 <= x) = (x == 0) || (0 < x). Proof. exact: le0r. Qed.

Lemma lt0r_neq0 (x : R) : 0 < x -> x != 0. Proof. by move=> /gt_eqF ->. Qed.
Lemma ltr0_neq0 (x : R) : x < 0 -> x != 0. Proof. by move=> /lt_eqF ->. Qed.

Lemma pmulr_rgt0 x y : 0 < x -> (0 < x * y) = (0 < y).
Proof. exact: pmulr_rgt0. Qed.

Lemma pmulr_rge0 x y : 0 < x -> (0 <= x * y) = (0 <= y).
Proof. by move=> x_gt0; rewrite !le0r mulf_eq0 pmulr_rgt0 // gt_eqF. Qed.

(* Integer comparisons and characteristic 0. *)
Lemma ler01 : 0 <= 1 :> R. Proof. exact: ler01. Qed.
Lemma ltr01 : 0 < 1 :> R. Proof. exact: ltr01. Qed.
Lemma ler0n n : 0 <= n%:R :> R. Proof. by rewrite -nnegrE rpred_nat. Qed.
Hint Extern 0 (is_true (@Order.le ring_display _ _ _)) =>
  (apply: ler01) : core.
Hint Extern 0 (is_true (@Order.lt ring_display _ _ _)) =>
  (apply: ltr01) : core.
Hint Extern 0 (is_true (@Order.le ring_display _ _ _)) =>
  (apply: ler0n) : core.
Lemma ltr0Sn n : 0 < n.+1%:R :> R.
Proof. by elim: n => // n; apply: addr_gt0. Qed.
Lemma ltr0n n : (0 < n%:R :> R) = (0 < n)%N.
Proof. by case: n => //= n; apply: ltr0Sn. Qed.
Hint Extern 0 (is_true (@Order.lt ring_display _ _ _)) =>
  (apply: ltr0Sn) : core.

Lemma pnatr_eq0 n : (n%:R == 0 :> R) = (n == 0)%N.
Proof. by case: n => [|n]; rewrite ?mulr0n ?eqxx // gt_eqF. Qed.

Lemma char_num : [char R] =i pred0.
Proof. by case=> // p /=; rewrite !inE pnatr_eq0 andbF. Qed.

(* Properties of the norm. *)

Lemma ger0_def x : (0 <= x) = (`|x| == x). Proof. exact: ger0_def. Qed.
Lemma normr_idP {x} : reflect (`|x| = x) (0 <= x).
Proof. by rewrite ger0_def; apply: eqP. Qed.
Lemma ger0_norm x : 0 <= x -> `|x| = x. Proof. exact: normr_idP. Qed.
Lemma normr1 : `|1 : R| = 1. Proof. exact: ger0_norm. Qed.
Lemma normr_nat n : `|n%:R : R| = n%:R. Proof. exact: ger0_norm. Qed.

Lemma normr_prod I r (P : pred I) (F : I -> R) :
  `|\prod_(i <- r | P i) F i| = \prod_(i <- r | P i) `|F i|.
Proof. exact: (big_morph norm normrM normr1). Qed.

Lemma normrX n x : `|x ^+ n| = `|x| ^+ n.
Proof. by rewrite -(card_ord n) -!prodr_const normr_prod. Qed.

Lemma normr_unit : {homo (@norm _ (* R *) R) : x / x \is a GRing.unit}.
Proof.
move=> x /= /unitrP [y [yx xy]]; apply/unitrP; exists `|y|.
by rewrite -!normrM xy yx normr1.
Qed.

Lemma normrV : {in GRing.unit, {morph (@norm _ (* R *) R) : x / x ^-1}}.
Proof.
move=> x ux; apply: (mulrI (normr_unit ux)).
by rewrite -normrM !divrr ?normr1 ?normr_unit.
Qed.

Lemma normrN1 : `|-1 : R| = 1.
Proof.
have: `|-1 : R| ^+ 2 == 1 by rewrite -normrX -signr_odd normr1.
rewrite sqrf_eq1 => /orP[/eqP //|]; rewrite -ger0_def le0r oppr_eq0 oner_eq0.
by move/(addr_gt0 ltr01); rewrite subrr ltxx.
Qed.

Lemma big_real x0 op I (P : pred I) F (s : seq I) :
  {in real &, forall x y, op x y \is real} -> x0 \is real ->
  {in P, forall i, F i \is real} -> \big[op/x0]_(i <- s | P i) F i \is real.
Proof. exact: comparable_bigr. Qed.

Lemma sum_real I (P : pred I) (F : I -> R) (s : seq I) :
  {in P, forall i, F i \is real} -> \sum_(i <- s | P i) F i \is real.
Proof. by apply/big_real; [apply: rpredD | apply: rpred0]. Qed.

Lemma prod_real I (P : pred I) (F : I -> R) (s : seq I) :
  {in P, forall i, F i \is real} -> \prod_(i <- s | P i) F i \is real.
Proof. by apply/big_real; [apply: rpredM | apply: rpred1]. Qed.

Section NormedZmoduleTheory.

Variable V : normedZmodType R.
Implicit Types (v w : V).

Lemma normr0 : `|0 : V| = 0.
Proof. by rewrite -(mulr0n 0) normrMn mulr0n. Qed.

Lemma normr0P v : reflect (`|v| = 0) (v == 0).
Proof. by apply: (iffP eqP)=> [->|/normr0_eq0 //]; apply: normr0. Qed.

Definition normr_eq0 v := sameP (`|v| =P 0) (normr0P v).

Lemma distrC v w : `|v - w| = `|w - v|.
Proof. by rewrite -opprB normrN. Qed.

Lemma normr_id v : `| `|v| | = `|v|.
Proof.
have nz2: 2 != 0 :> R by rewrite pnatr_eq0.
apply: (mulfI nz2); rewrite -{1}normr_nat -normrM mulr_natl mulr2n ger0_norm //.
by rewrite -{2}normrN -normr0 -(subrr v) ler_normD.
Qed.

Lemma normr_ge0 v : 0 <= `|v|. Proof. by rewrite ger0_def normr_id. Qed.

Lemma normr_le0 v : `|v| <= 0 = (v == 0).
Proof. by rewrite -normr_eq0 eq_le normr_ge0 andbT. Qed.

Lemma normr_lt0 v : `|v| < 0 = false.
Proof. by rewrite lt_neqAle normr_le0 normr_eq0 andNb. Qed.

Lemma normr_gt0 v : `|v| > 0 = (v != 0).
Proof. by rewrite lt_def normr_eq0 normr_ge0 andbT. Qed.

Definition normrE := (normr_id, normr0, normr1, normrN1, normr_ge0, normr_eq0,
  normr_lt0, normr_le0, normr_gt0, normrN).

End NormedZmoduleTheory.

Lemma ler0_def x : (x <= 0) = (`|x| == - x).
Proof. by rewrite ler_def sub0r normrN. Qed.

Lemma ler0_norm x : x <= 0 -> `|x| = - x.
Proof. by move=> x_le0; rewrite -[r in _ = r]ger0_norm ?normrN ?oppr_ge0. Qed.

Definition gtr0_norm x (hx : 0 < x) := ger0_norm (ltW hx).
Definition ltr0_norm x (hx : x < 0) := ler0_norm (ltW hx).

Lemma ger0_le_norm :
  {in nneg &, {mono (@normr _ R) : x y / x <= y}}.
Proof. by move=> x y; rewrite !nnegrE => x0 y0; rewrite !ger0_norm. Qed.

Lemma gtr0_le_norm :
  {in pos &, {mono (@normr _ R) : x y / x <= y}}.
Proof. by move=> x y; rewrite !posrE => /ltW x0 /ltW y0; exact: ger0_le_norm. Qed.

Lemma ler0_ge_norm :
  {in npos &, {mono (@normr _ R) : x y / x <= y >-> x >= y}}.
Proof.
move=> x y; rewrite !nposrE => x0 y0.
by rewrite !ler0_norm// -subr_ge0 opprK addrC subr_ge0.
Qed.

Lemma ltr0_ge_norm :
  {in neg &, {mono (@normr _ R) : x y / x <= y >-> x >= y}}.
Proof. by move=> x y; rewrite !negrE => /ltW x0 /ltW y0; exact: ler0_ge_norm. Qed.

(* Comparison to 0 of a difference *)

Lemma subr_ge0 x y : (0 <= y - x) = (x <= y). Proof. exact: subr_ge0. Qed.
Lemma subr_gt0 x y : (0 < y - x) = (x < y).
Proof. by rewrite !lt_def subr_eq0 subr_ge0. Qed.
Lemma subr_le0  x y : (y - x <= 0) = (y <= x).
Proof. by rewrite -[LHS]subr_ge0 opprB add0r subr_ge0. Qed.  (* FIXME: rewrite pattern *)
Lemma subr_lt0  x y : (y - x < 0) = (y < x).
Proof. by rewrite -[LHS]subr_gt0 opprB add0r subr_gt0. Qed.  (* FIXME: rewrite pattern *)

Definition subr_lte0 := (subr_le0, subr_lt0).
Definition subr_gte0 := (subr_ge0, subr_gt0).
Definition subr_cp0 := (subr_lte0, subr_gte0).

(* Comparability in a numDomain *)

Lemma comparable0r x : (0 >=< x)%R = (x \is Num.real). Proof. by []. Qed.

Lemma comparabler0 x : (x >=< 0)%R = (x \is Num.real).
Proof. by rewrite comparable_sym. Qed.

Lemma subr_comparable0 x y : (x - y >=< 0)%R = (x >=< y)%R.
Proof. by rewrite /comparable subr_ge0 subr_le0. Qed.

Lemma comparablerE x y : (x >=< y)%R = (x - y \is Num.real).
Proof. by rewrite -comparabler0 subr_comparable0. Qed.

Lemma  comparabler_trans : transitive (comparable : rel R).
Proof.
move=> y x z; rewrite !comparablerE => xBy_real yBz_real.
by have := rpredD xBy_real yBz_real; rewrite addrA addrNK.
Qed.

(* Ordered ring properties. *)

Definition lter01 := (ler01, ltr01).

Lemma addr_ge0 x y : 0 <= x -> 0 <= y -> 0 <= x + y.
Proof. exact: addr_ge0. Qed.

End NumIntegralDomainTheory.

Arguments ler01 {R}.
Arguments ltr01 {R}.
Arguments normr_idP {R x}.
Arguments normr0P {R V v}.
#[global] Hint Extern 0 (is_true (@Order.le ring_display _ _ _)) =>
  (apply: ler01) : core.
#[global] Hint Extern 0 (is_true (@Order.lt ring_display _ _ _)) =>
  (apply: ltr01) : core.
#[global] Hint Extern 0 (is_true (@Order.le ring_display _ _ _)) =>
  (apply: ler0n) : core.
#[global] Hint Extern 0 (is_true (@Order.lt ring_display _ _ _)) =>
  (apply: ltr0Sn) : core.
#[global] Hint Extern 0 (is_true (0 <= norm _)) => apply: normr_ge0 : core.

Lemma normr_nneg (R : numDomainType) (x : R) : `|x| \is Num.nneg.
Proof. by rewrite qualifE /=. Qed.
#[global] Hint Resolve normr_nneg : core.

Section NumDomainOperationTheory.

Variable R : numDomainType.
Implicit Types x y z t : R.

(* Comparison and opposite. *)

Lemma lerN2 : {mono -%R : x y /~ x <= y :> R}.
Proof. by move=> x y /=; rewrite -subr_ge0 opprK addrC subr_ge0. Qed.
Hint Resolve lerN2 : core.
Lemma ltrN2 : {mono -%R : x y /~ x < y :> R}.
Proof. by move=> x y /=; rewrite leW_nmono. Qed.
Hint Resolve ltrN2 : core.
Definition lterN2 := (lerN2, ltrN2).

Lemma lerNr x y : (x <= - y) = (y <= - x).
Proof. by rewrite (monoRL opprK lerN2). Qed.

Lemma ltrNr x y : (x < - y) = (y < - x).
Proof. by rewrite (monoRL opprK (leW_nmono _)). Qed.

Definition lterNr := (lerNr, ltrNr).

Lemma lerNl x y : (- x <= y) = (- y <= x).
Proof. by rewrite (monoLR opprK lerN2). Qed.

Lemma ltrNl x y : (- x < y) = (- y < x).
Proof. by rewrite (monoLR opprK (leW_nmono _)). Qed.

Definition lterNl := (lerNl, ltrNl).

Lemma oppr_ge0 x : (0 <= - x) = (x <= 0). Proof. by rewrite lerNr oppr0. Qed.

Lemma oppr_gt0 x : (0 < - x) = (x < 0). Proof. by rewrite ltrNr oppr0. Qed.

Definition oppr_gte0 := (oppr_ge0, oppr_gt0).

Lemma oppr_le0 x : (- x <= 0) = (0 <= x). Proof. by rewrite lerNl oppr0. Qed.

Lemma oppr_lt0 x : (- x < 0) = (0 < x). Proof. by rewrite ltrNl oppr0. Qed.

Lemma gtrN x : 0 < x -> - x < x.
Proof. by move=> n0; rewrite -subr_lt0 -opprD oppr_lt0 addr_gt0. Qed.

Definition oppr_lte0 := (oppr_le0, oppr_lt0).
Definition oppr_cp0 := (oppr_gte0, oppr_lte0).
Definition lterNE := (oppr_cp0, lterN2).

Lemma ge0_cp x : 0 <= x -> (- x <= 0) * (- x <= x).
Proof. by move=> hx; rewrite oppr_cp0 hx (@le_trans _ _ 0) ?oppr_cp0. Qed.

Lemma gt0_cp x : 0 < x ->
  (0 <= x) * (- x <= 0) * (- x <= x) * (- x < 0) * (- x < x).
Proof.
move=> hx; move: (ltW hx) => hx'; rewrite !ge0_cp hx' //.
by rewrite oppr_cp0 hx // (@lt_trans _ _ 0) ?oppr_cp0.
Qed.

Lemma le0_cp x : x <= 0 -> (0 <= - x) * (x <= - x).
Proof. by move=> hx; rewrite oppr_cp0 hx (@le_trans _ _ 0) ?oppr_cp0. Qed.

Lemma lt0_cp x :
  x < 0 -> (x <= 0) * (0 <= - x) * (x <= - x) * (0 < - x) * (x < - x).
Proof.
move=> hx; move: (ltW hx) => hx'; rewrite !le0_cp // hx'.
by rewrite oppr_cp0 hx // (@lt_trans _ _ 0) ?oppr_cp0.
Qed.

(* Properties of the real subset. *)

Lemma ger0_real x : 0 <= x -> x \is real.
Proof. by rewrite realE => ->. Qed.

Lemma ler0_real x : x <= 0 -> x \is real.
Proof. by rewrite realE orbC => ->. Qed.

Lemma gtr0_real x : 0 < x -> x \is real. Proof. by move=> /ltW/ger0_real. Qed.

Lemma ltr0_real x : x < 0 -> x \is real. Proof. by move=> /ltW/ler0_real. Qed.

Lemma real0 : 0 \is @real R. Proof. exact: rpred0. Qed.
Lemma real1 : 1 \is @real R. Proof. exact: rpred1. Qed.
Lemma realn n : n%:R \is @real R. Proof. exact: rpred_nat. Qed.
#[local] Hint Resolve real0 real1 : core.

Lemma ler_leVge x y : x <= 0 -> y <= 0 -> (x <= y) || (y <= x).
Proof. by rewrite -!oppr_ge0 => /(ger_leVge _) /[apply]; rewrite !lerN2. Qed.

Lemma real_leVge x y : x \is real -> y \is real -> (x <= y) || (y <= x).
Proof. by rewrite -comparabler0 -comparable0r => /comparabler_trans P/P. Qed.

Lemma real_comparable x y : x \is real -> y \is real -> x >=< y.
Proof. exact: real_leVge. Qed.

Lemma realB : {in real &, forall x y, x - y \is real}.
Proof. exact: rpredB. Qed.

Lemma realN : {mono (@GRing.opp R) : x / x \is real}.
Proof. exact: rpredN. Qed.

Lemma realBC x y : (x - y \is real) = (y - x \is real).
Proof. exact: rpredBC. Qed.

Lemma realD : {in real &, forall x y, x + y \is real}.
Proof. exact: rpredD. Qed.

(* dichotomy and trichotomy *)

Variant ler_xor_gt (x y : R) : R -> R -> R -> R -> R -> R ->
    bool -> bool -> Set :=
  | LerNotGt of x <= y : ler_xor_gt x y x x y y (y - x) (y - x) true false
  | GtrNotLe of y < x  : ler_xor_gt x y y y x x (x - y) (x - y) false true.

Variant ltr_xor_ge (x y : R) : R -> R -> R -> R -> R -> R ->
    bool -> bool -> Set :=
  | LtrNotGe of x < y  : ltr_xor_ge x y x x y y (y - x) (y - x) false true
  | GerNotLt of y <= x : ltr_xor_ge x y y y x x (x - y) (x - y) true false.

Variant comparer x y : R -> R -> R -> R -> R -> R ->
    bool -> bool -> bool -> bool -> bool -> bool -> Set :=
  | ComparerLt of x < y : comparer x y x x y y (y - x) (y - x)
    false false false true false true
  | ComparerGt of x > y : comparer x y y y x x (x - y) (x - y)
    false false true false true false
  | ComparerEq of x = y : comparer x y x x x x 0 0
    true true true true false false.

Lemma real_leP x y : x \is real -> y \is real ->
  ler_xor_gt x y (min y x) (min x y) (max y x) (max x y)
                 `|x - y| `|y - x| (x <= y) (y < x).
Proof.
move=> xR yR; case: (comparable_leP (real_leVge xR yR)) => xy.
- by rewrite [`|x - y|]distrC !ger0_norm ?subr_cp0 //; constructor.
- by rewrite [`|y - x|]distrC !gtr0_norm ?subr_cp0 //; constructor.
Qed.

Lemma real_ltP x y : x \is real -> y \is real ->
  ltr_xor_ge x y (min y x) (min x y) (max y x) (max x y)
             `|x - y| `|y - x| (y <= x) (x < y).
Proof. by move=> xR yR; case: real_leP=> //; constructor. Qed.

Lemma real_ltNge : {in real &, forall x y, (x < y) = ~~ (y <= x)}.
Proof. by move=> x y xR yR /=; case: real_leP. Qed.

Lemma real_leNgt : {in real &, forall x y, (x <= y) = ~~ (y < x)}.
Proof. by move=> x y xR yR /=; case: real_leP. Qed.

Lemma real_ltgtP x y : x \is real -> y \is real ->
  comparer x y (min y x) (min x y) (max y x) (max x y) `|x - y| `|y - x|
               (y == x) (x == y) (x >= y) (x <= y) (x > y) (x < y).
Proof.
move=> xR yR; case: (comparable_ltgtP (real_leVge yR xR)) => [?|?|->].
- by rewrite [`|y - x|]distrC !gtr0_norm ?subr_gt0//; constructor.
- by rewrite [`|x - y|]distrC !gtr0_norm ?subr_gt0//; constructor.
- by rewrite subrr normr0; constructor.
Qed.

Variant ger0_xor_lt0 (x : R) : R -> R -> R -> R -> R ->
    bool -> bool -> Set :=
  | Ger0NotLt0 of 0 <= x : ger0_xor_lt0 x 0 0 x x x false true
  | Ltr0NotGe0 of x < 0  : ger0_xor_lt0 x x x 0 0 (- x) true false.

Variant ler0_xor_gt0 (x : R) : R -> R -> R -> R -> R ->
   bool -> bool -> Set :=
  | Ler0NotLe0 of x <= 0 : ler0_xor_gt0 x x x 0 0 (- x) false true
  | Gtr0NotGt0 of 0 < x  : ler0_xor_gt0 x 0 0 x x x true false.

Variant comparer0 x : R -> R -> R -> R -> R ->
    bool -> bool -> bool -> bool -> bool -> bool -> Set :=
  | ComparerGt0 of 0 < x : comparer0 x 0 0 x x x false false false true false true
  | ComparerLt0 of x < 0 : comparer0 x x x 0 0 (- x) false false true false true false
  | ComparerEq0 of x = 0 : comparer0 x 0 0 0 0 0 true true true true false false.

Lemma real_ge0P x : x \is real -> ger0_xor_lt0 x
   (min 0 x) (min x 0) (max 0 x) (max x 0)
  `|x| (x < 0) (0 <= x).
Proof.
move=> hx; rewrite -[X in `|X|]subr0; case: real_leP;
by rewrite ?subr0 ?sub0r //; constructor.
Qed.

Lemma real_le0P x : x \is real -> ler0_xor_gt0 x
  (min 0 x) (min x 0) (max 0 x) (max x 0)
  `|x| (0 < x) (x <= 0).
Proof.
move=> hx; rewrite -[X in `|X|]subr0; case: real_ltP;
by rewrite ?subr0 ?sub0r //; constructor.
Qed.

Lemma real_ltgt0P x : x \is real ->
  comparer0 x (min 0 x) (min x 0) (max 0 x) (max x 0)
            `|x| (0 == x) (x == 0) (x <= 0) (0 <= x) (x < 0) (x > 0).
Proof.
move=> hx; rewrite -[X in `|X|]subr0; case: (@real_ltgtP 0 x);
by rewrite ?subr0 ?sub0r //; constructor.
Qed.

Lemma max_real : {in real &, forall x y, max x y \is real}.
Proof. exact: comparable_maxr. Qed.

Lemma min_real : {in real &, forall x y, min x y \is real}.
Proof. exact: comparable_minr. Qed.

Lemma bigmax_real I x0 (r : seq I) (P : pred I) (f : I -> R):
  x0 \is real -> {in P, forall i : I, f i \is real} ->
  \big[max/x0]_(i <- r | P i) f i \is real.
Proof. exact/big_real/max_real. Qed.

Lemma bigmin_real I x0 (r : seq I) (P : pred I) (f : I -> R):
  x0 \is real -> {in P, forall i : I, f i \is real} ->
  \big[min/x0]_(i <- r | P i) f i \is real.
Proof. exact/big_real/min_real. Qed.

Lemma real_neqr_lt : {in real &, forall x y, (x != y) = (x < y) || (y < x)}.
Proof. by move=> * /=; case: real_ltgtP. Qed.

Lemma lerB_real x y : x <= y -> y - x \is real.
Proof. by move=> le_xy; rewrite ger0_real // subr_ge0. Qed.

Lemma gerB_real x y : x <= y -> x - y \is real.
Proof. by move=> le_xy; rewrite ler0_real // subr_le0. Qed.

Lemma ler_real y x : x <= y -> (x \is real) = (y \is real).
Proof. by move=> le_xy; rewrite -(addrNK x y) rpredDl ?lerB_real. Qed.

Lemma ger_real x y : y <= x -> (x \is real) = (y \is real).
Proof. by move=> le_yx; rewrite -(ler_real le_yx). Qed.

Lemma ger1_real x : 1 <= x -> x \is real. Proof. by move=> /ger_real->. Qed.
Lemma ler1_real x : x <= 1 -> x \is real. Proof. by move=> /ler_real->. Qed.

Lemma Nreal_leF x y : y \is real -> x \notin real -> (x <= y) = false.
Proof. by move=> yR; apply: contraNF=> /ler_real->. Qed.

Lemma Nreal_geF x y : y \is real -> x \notin real -> (y <= x) = false.
Proof. by move=> yR; apply: contraNF=> /ger_real->. Qed.

Lemma Nreal_ltF x y : y \is real -> x \notin real -> (x < y) = false.
Proof. by move=> yR xNR; rewrite lt_def Nreal_leF ?andbF. Qed.

Lemma Nreal_gtF x y : y \is real -> x \notin real -> (y < x) = false.
Proof. by move=> yR xNR; rewrite lt_def Nreal_geF ?andbF. Qed.

(* real wlog *)

Lemma real_wlog_ler P :
    (forall a b, P b a -> P a b) -> (forall a b, a <= b -> P a b) ->
  forall a b : R, a \is real -> b \is real -> P a b.
Proof.
move=> sP hP a b ha hb; wlog: a b ha hb / a <= b => [hwlog|]; last exact: hP.
by case: (real_leP ha hb)=> [/hP //|/ltW hba]; apply/sP/hP.
Qed.

Lemma real_wlog_ltr P :
    (forall a, P a a) -> (forall a b, (P b a -> P a b)) ->
    (forall a b, a < b -> P a b) ->
  forall a b : R, a \is real -> b \is real -> P a b.
Proof.
move=> rP sP hP; apply: real_wlog_ler=> // a b.
by rewrite le_eqVlt; case: eqVneq => [->|] //= _ /hP.
Qed.

(* Monotony of addition *)
Lemma lerD2l x : {mono +%R x : y z / y <= z}.
Proof. by move=> y z; rewrite -subr_ge0 opprD addrAC addNKr addrC subr_ge0. Qed.

Lemma lerD2r x : {mono +%R^~ x : y z / y <= z}.
Proof. by move=> y z; rewrite ![_ + x]addrC lerD2l. Qed.

Lemma ltrD2l x : {mono +%R x : y z / y < z}.
Proof. by move=> y z; rewrite (leW_mono (lerD2l _)). Qed.

Lemma ltrD2r x : {mono +%R^~ x : y z / y < z}.
Proof. by move=> y z /=; rewrite (leW_mono (lerD2r _)). Qed.

Definition lerD2 := (lerD2l, lerD2r).
Definition ltrD2 := (ltrD2l, ltrD2r).
Definition lterD2 := (lerD2, ltrD2).

(* Addition, subtraction and transitivity *)
Lemma lerD x y z t : x <= y -> z <= t -> x + z <= y + t.
Proof. by move=> lxy lzt; rewrite (@le_trans _ _ (y + z)) ?lterD2. Qed.

Lemma ler_ltD x y z t : x <= y -> z < t -> x + z < y + t.
Proof. by move=> lxy lzt; rewrite (@le_lt_trans _ _ (y + z)) ?lterD2. Qed.

Lemma ltr_leD x y z t : x < y -> z <= t -> x + z < y + t.
Proof. by move=> lxy lzt; rewrite (@lt_le_trans _ _ (y + z)) ?lterD2. Qed.

Lemma ltrD x y z t : x < y -> z < t -> x + z < y + t.
Proof. by move=> lxy lzt; rewrite ltr_leD // ltW. Qed.

Lemma lerB x y z t : x <= y -> t <= z -> x - z <= y - t.
Proof. by move=> lxy ltz; rewrite lerD // lterN2. Qed.

Lemma ler_ltB x y z t : x <= y -> t < z -> x - z < y - t.
Proof. by move=> lxy lzt; rewrite ler_ltD // lterN2. Qed.

Lemma ltr_leB x y z t : x < y -> t <= z -> x - z < y - t.
Proof. by move=> lxy lzt; rewrite ltr_leD // lterN2. Qed.

Lemma ltrB x y z t : x < y -> t < z -> x - z < y - t.
Proof. by move=> lxy lzt; rewrite ltrD // lterN2. Qed.

Lemma lerBlDr x y z : (x - y <= z) = (x <= z + y).
Proof. by rewrite (monoLR (addrK _) (lerD2r _)). Qed.

Lemma ltrBlDr x y z : (x - y < z) = (x < z + y).
Proof. by rewrite (monoLR (addrK _) (ltrD2r _)). Qed.

Lemma lerBrDr x y z : (x <= y - z) = (x + z <= y).
Proof. by rewrite (monoLR (addrNK _) (lerD2r _)). Qed.

Lemma ltrBrDr x y z : (x < y - z) = (x + z < y).
Proof. by rewrite (monoLR (addrNK _) (ltrD2r _)). Qed.

Definition lerBDr := (lerBlDr, lerBrDr).
Definition ltrBDr := (ltrBlDr, ltrBrDr).
Definition lterBDr := (lerBDr, ltrBDr).

Lemma lerBlDl x y z : (x - y <= z) = (x <= y + z).
Proof. by rewrite lterBDr addrC. Qed.

Lemma ltrBlDl x y z : (x - y < z) = (x < y + z).
Proof. by rewrite lterBDr addrC. Qed.

Lemma lerBrDl x y z : (x <= y - z) = (z + x <= y).
Proof. by rewrite lerBrDr addrC. Qed.

Lemma ltrBrDl x y z : (x < y - z) = (z + x < y).
Proof. by rewrite lterBDr addrC. Qed.

Definition lerBDl := (lerBlDl, lerBrDl).
Definition ltrBDl := (ltrBlDl, ltrBrDl).
Definition lterBDl := (lerBDl, ltrBDl).

Lemma lerDl x y : (x <= x + y) = (0 <= y).
Proof. by rewrite -{1}[x]addr0 lterD2. Qed.

Lemma ltrDl x y : (x < x + y) = (0 < y).
Proof. by rewrite -{1}[x]addr0 lterD2. Qed.

Lemma lerDr x y : (x <= y + x) = (0 <= y).
Proof. by rewrite -{1}[x]add0r lterD2. Qed.

Lemma ltrDr x y : (x < y + x) = (0 < y).
Proof. by rewrite -{1}[x]add0r lterD2. Qed.

Lemma gerDl x y : (x + y <= x) = (y <= 0).
Proof. by rewrite -{2}[x]addr0 lterD2. Qed.

Lemma gerBl x y : (x - y <= x) = (0 <= y).
Proof. by rewrite lerBlDl lerDr. Qed.

Lemma gtrDl x y : (x + y < x) = (y < 0).
Proof. by rewrite -{2}[x]addr0 lterD2. Qed.

Lemma gtrBl x y : (x - y < x) = (0 < y).
Proof. by rewrite ltrBlDl ltrDr. Qed.

Lemma gerDr x y : (y + x <= x) = (y <= 0).
Proof. by rewrite -{2}[x]add0r lterD2. Qed.

Lemma gtrDr x y : (y + x < x) = (y < 0).
Proof. by rewrite -{2}[x]add0r lterD2. Qed.

Definition cprD := (lerDl, lerDr, gerDl, gerDl,
                    ltrDl, ltrDr, gtrDl, gtrDl).

(* Addition with left member known to be positive/negative *)
Lemma ler_wpDl y x z : 0 <= x -> y <= z -> y <= x + z.
Proof. by move=> *; rewrite -[y]add0r lerD. Qed.

Lemma ltr_wpDl y x z : 0 <= x -> y < z -> y < x + z.
Proof. by move=> *; rewrite -[y]add0r ler_ltD. Qed.

Lemma ltr_pwDl y x z : 0 < x -> y <= z -> y < x + z.
Proof. by move=> *; rewrite -[y]add0r ltr_leD. Qed.

Lemma ltr_pDl y x z : 0 < x -> y < z -> y < x + z.
Proof. by move=> *; rewrite -[y]add0r ltrD. Qed.

Lemma ler_wnDl y x z : x <= 0 -> y <= z -> x + y <= z.
Proof. by move=> *; rewrite -[z]add0r lerD. Qed.

Lemma ltr_wnDl y x z : x <= 0 -> y < z -> x + y < z.
Proof. by move=> *; rewrite -[z]add0r ler_ltD. Qed.

Lemma ltr_nwDl y x z : x < 0 -> y <= z -> x + y < z.
Proof. by move=> *; rewrite -[z]add0r ltr_leD. Qed.

Lemma ltr_nDl y x z : x < 0 -> y < z -> x + y < z.
Proof. by move=> *; rewrite -[z]add0r ltrD. Qed.

(* Addition with right member we know positive/negative *)
Lemma ler_wpDr y x z : 0 <= x -> y <= z -> y <= z + x.
Proof. by move=> *; rewrite addrC ler_wpDl. Qed.

Lemma ltr_wpDr y x z : 0 <= x -> y < z -> y < z + x.
Proof. by move=> *; rewrite addrC ltr_wpDl. Qed.

Lemma ltr_pwDr y x z : 0 < x -> y <= z -> y < z + x.
Proof. by move=> *; rewrite addrC ltr_pwDl. Qed.

Lemma ltr_pDr y x z : 0 < x -> y < z -> y < z + x.
Proof. by move=> *; rewrite addrC ltr_pDl. Qed.

Lemma ler_wnDr y x z : x <= 0 -> y <= z -> y + x <= z.
Proof. by move=> *; rewrite addrC ler_wnDl. Qed.

Lemma ltr_wnDr y x z : x <= 0 -> y < z -> y + x < z.
Proof. by move=> *; rewrite addrC ltr_wnDl. Qed.

Lemma ltr_nwDr y x z : x < 0 -> y <= z -> y + x < z.
Proof. by move=> *; rewrite addrC ltr_nwDl. Qed.

Lemma ltr_nDr y x z : x < 0 -> y < z -> y + x < z.
Proof. by move=> *; rewrite addrC ltr_nDl. Qed.

(* x and y have the same sign and their sum is null *)
Lemma paddr_eq0 (x y : R) :
  0 <= x -> 0 <= y -> (x + y == 0) = (x == 0) && (y == 0).
Proof.
rewrite le0r; case/orP=> [/eqP->|hx]; first by rewrite add0r eqxx.
by rewrite (gt_eqF hx) /= => hy; rewrite gt_eqF // ltr_pwDl.
Qed.

Lemma naddr_eq0 (x y : R) :
  x <= 0 -> y <= 0 -> (x + y == 0) = (x == 0) && (y == 0).
Proof.
by move=> lex0 ley0; rewrite -oppr_eq0 opprD paddr_eq0 ?oppr_cp0 // !oppr_eq0.
Qed.

Lemma addr_ss_eq0 (x y : R) :
    (0 <= x) && (0 <= y) || (x <= 0) && (y <= 0) ->
  (x + y == 0) = (x == 0) && (y == 0).
Proof. by case/orP=> /andP []; [apply: paddr_eq0 | apply: naddr_eq0]. Qed.

(* big sum and ler *)
Lemma sumr_ge0 I (r : seq I) (P : pred I) (F : I -> R) :
  (forall i, P i -> (0 <= F i)) -> 0 <= \sum_(i <- r | P i) (F i).
Proof. exact: (big_ind _ _ (@ler_wpDl 0)). Qed.

Lemma ler_sum I (r : seq I) (P : pred I) (F G : I -> R) :
    (forall i, P i -> F i <= G i) ->
  \sum_(i <- r | P i) F i <= \sum_(i <- r | P i) G i.
Proof. exact: (big_ind2 _ (lexx _) lerD). Qed.

Lemma ler_sum_nat (m n : nat) (F G : nat -> R) :
  (forall i, (m <= i < n)%N -> F i <= G i) ->
  \sum_(m <= i < n) F i <= \sum_(m <= i < n) G i.
Proof. by move=> le_FG; rewrite !big_nat ler_sum. Qed.

Lemma psumr_eq0 (I : eqType) (r : seq I) (P : pred I) (F : I -> R) :
    (forall i, P i -> 0 <= F i) ->
  (\sum_(i <- r | P i) (F i) == 0) = (all (fun i => (P i) ==> (F i == 0)) r).
Proof.
elim: r=> [|a r ihr hr] /=; rewrite (big_nil, big_cons); first by rewrite eqxx.
by case: ifP=> pa /=; rewrite ?paddr_eq0 ?ihr ?hr // sumr_ge0.
Qed.

(* :TODO: Cyril : See which form to keep *)
Lemma psumr_eq0P (I : finType) (P : pred I) (F : I -> R) :
     (forall i, P i -> 0 <= F i) -> \sum_(i | P i) F i = 0 ->
  (forall i, P i -> F i = 0).
Proof.
move=> F_ge0 /eqP; rewrite psumr_eq0 // -big_all big_andE => /forallP hF i Pi.
by move: (hF i); rewrite implyTb Pi /= => /eqP.
Qed.

Lemma psumr_neq0 (I : eqType) (r : seq I) (P : pred I) (F : I -> R) :
    (forall i, P i -> 0 <= F i) ->
  (\sum_(i <- r | P i) (F i) != 0) = (has (fun i => P i && (0 < F i)) r).
Proof.
move=> F_ge0; rewrite psumr_eq0// -has_predC; apply: eq_has => x /=.
by case Px: (P x); rewrite //= lt_def F_ge0 ?andbT.
Qed.

Lemma psumr_neq0P (I : finType) (P : pred I) (F : I -> R) :
     (forall i, P i -> 0 <= F i) -> \sum_(i | P i) F i <> 0 ->
  (exists i, P i && (0 < F i)).
Proof. by move=> ? /eqP; rewrite psumr_neq0// => /hasP[x _ ?]; exists x. Qed.

(* mulr and ler/ltr *)

Lemma ler_pM2l x : 0 < x -> {mono *%R x : x y / x <= y}.
Proof.
by move=> x_gt0 y z /=; rewrite -subr_ge0 -mulrBr pmulr_rge0 // subr_ge0.
Qed.

Lemma ltr_pM2l x : 0 < x -> {mono *%R x : x y / x < y}.
Proof. by move=> x_gt0; apply: leW_mono (ler_pM2l _). Qed.

Definition lter_pM2l := (ler_pM2l, ltr_pM2l).

Lemma ler_pM2r x : 0 < x -> {mono *%R^~ x : x y / x <= y}.
Proof. by move=> x_gt0 y z /=; rewrite ![_ * x]mulrC ler_pM2l. Qed.

Lemma ltr_pM2r x : 0 < x -> {mono *%R^~ x : x y / x < y}.
Proof. by move=> x_gt0; apply: leW_mono (ler_pM2r _). Qed.

Definition lter_pM2r := (ler_pM2r, ltr_pM2r).

Lemma ler_nM2l x : x < 0 -> {mono *%R x : x y /~ x <= y}.
Proof. by move=> x_lt0 y z /=; rewrite -lerN2 -!mulNr ler_pM2l ?oppr_gt0. Qed.

Lemma ltr_nM2l x : x < 0 -> {mono *%R x : x y /~ x < y}.
Proof. by move=> x_lt0; apply: leW_nmono (ler_nM2l _). Qed.

Definition lter_nM2l := (ler_nM2l, ltr_nM2l).

Lemma ler_nM2r x : x < 0 -> {mono *%R^~ x : x y /~ x <= y}.
Proof. by move=> x_lt0 y z /=; rewrite ![_ * x]mulrC ler_nM2l. Qed.

Lemma ltr_nM2r x : x < 0 -> {mono *%R^~ x : x y /~ x < y}.
Proof. by move=> x_lt0; apply: leW_nmono (ler_nM2r _). Qed.

Definition lter_nM2r := (ler_nM2r, ltr_nM2r).

Lemma ler_wpM2l x : 0 <= x -> {homo *%R x : y z / y <= z}.
Proof.
by rewrite le0r => /orP[/eqP-> y z | /ler_pM2l/mono2W//]; rewrite !mul0r.
Qed.

Lemma ler_wpM2r x : 0 <= x -> {homo *%R^~ x : y z / y <= z}.
Proof. by move=> x_ge0 y z leyz; rewrite ![_ * x]mulrC ler_wpM2l. Qed.

Lemma ler_wnM2l x : x <= 0 -> {homo *%R x : y z /~ y <= z}.
 by move=> x_le0 y z leyz; rewrite -![x * _]mulrNN ler_wpM2l ?lterNE. Qed.

Lemma ler_wnM2r x : x <= 0 -> {homo *%R^~ x : y z /~ y <= z}.
Proof. by move=> x_le0 y z leyz; rewrite -![_ * x]mulrNN ler_wpM2r ?lterNE. Qed.

(* Binary forms, for backchaining. *)

Lemma ler_pM x1 y1 x2 y2 :
  0 <= x1 -> 0 <= x2 -> x1 <= y1 -> x2 <= y2 -> x1 * x2 <= y1 * y2.
Proof.
move=> x1ge0 x2ge0 le_xy1 le_xy2; have y1ge0 := le_trans x1ge0 le_xy1.
exact: le_trans (ler_wpM2r x2ge0 le_xy1) (ler_wpM2l y1ge0 le_xy2).
Qed.

Lemma ltr_pM x1 y1 x2 y2 :
  0 <= x1 -> 0 <= x2 -> x1 < y1 -> x2 < y2 -> x1 * x2 < y1 * y2.
Proof.
move=> x1ge0 x2ge0 lt_xy1 lt_xy2; have y1gt0 := le_lt_trans x1ge0 lt_xy1.
by rewrite (le_lt_trans (ler_wpM2r x2ge0 (ltW lt_xy1))) ?ltr_pM2l.
Qed.

(* complement for x *+ n and <= or < *)

Lemma ler_pMn2r n : (0 < n)%N -> {mono (@GRing.natmul R)^~ n : x y / x <= y}.
Proof.
by case: n => // n _ x y /=; rewrite -mulr_natl -[y *+ _]mulr_natl ler_pM2l.
Qed.

Lemma ltr_pMn2r n : (0 < n)%N -> {mono (@GRing.natmul R)^~ n : x y / x < y}.
Proof. by move/ler_pMn2r/leW_mono. Qed.

Lemma pmulrnI n : (0 < n)%N -> injective ((@GRing.natmul R)^~ n).
Proof. by move/ler_pMn2r/inc_inj. Qed.

Lemma eqr_pMn2r n : (0 < n)%N -> {mono (@GRing.natmul R)^~ n : x y / x == y}.
Proof. by move/pmulrnI/inj_eq. Qed.

Lemma pmulrn_lgt0 x n : (0 < n)%N -> (0 < x *+ n) = (0 < x).
Proof. by move=> n_gt0; rewrite -(mul0rn _ n) ltr_pMn2r // mul0rn. Qed.

Lemma pmulrn_llt0 x n : (0 < n)%N -> (x *+ n < 0) = (x < 0).
Proof. by move=> n_gt0; rewrite -(mul0rn _ n) ltr_pMn2r // mul0rn. Qed.

Lemma pmulrn_lge0 x n : (0 < n)%N -> (0 <= x *+ n) = (0 <= x).
Proof. by move=> n_gt0; rewrite -(mul0rn _ n) ler_pMn2r // mul0rn. Qed.

Lemma pmulrn_lle0 x n : (0 < n)%N -> (x *+ n <= 0) = (x <= 0).
Proof. by move=> n_gt0; rewrite -(mul0rn _ n) ler_pMn2r // mul0rn. Qed.

Lemma ltr_wMn2r x y n : x < y -> (x *+ n < y *+ n) = (0 < n)%N.
Proof. by move=> ltxy; case: n=> // n; rewrite ltr_pMn2r. Qed.

Lemma ltr_wpMn2r n : (0 < n)%N -> {homo (@GRing.natmul R)^~ n : x y / x < y}.
Proof. by move=> n_gt0 x y /= / ltr_wMn2r ->. Qed.

Lemma ler_wMn2r n : {homo (@GRing.natmul R)^~ n : x y / x <= y}.
Proof. by move=> x y hxy /=; case: n=> // n; rewrite ler_pMn2r. Qed.

Lemma mulrn_wge0 x n : 0 <= x -> 0 <= x *+ n.
Proof. by move=> /(ler_wMn2r n); rewrite mul0rn. Qed.

Lemma mulrn_wle0 x n : x <= 0 -> x *+ n <= 0.
Proof. by move=> /(ler_wMn2r n); rewrite mul0rn. Qed.

Lemma lerMn2r n x y : (x *+ n <= y *+ n) = ((n == 0) || (x <= y)).
Proof. by case: n => [|n]; rewrite ?lexx ?eqxx // ler_pMn2r. Qed.

Lemma ltrMn2r n x y : (x *+ n < y *+ n) = ((0 < n)%N && (x < y)).
Proof. by case: n => [|n]; rewrite ?lexx ?eqxx // ltr_pMn2r. Qed.

Lemma eqrMn2r n x y : (x *+ n == y *+ n) = (n == 0)%N || (x == y).
Proof. by rewrite !(@eq_le _ R) !lerMn2r -orb_andr. Qed.

(* More characteristic zero properties. *)

Lemma mulrn_eq0 x n : (x *+ n == 0) = ((n == 0)%N || (x == 0)).
Proof. by rewrite -mulr_natl mulf_eq0 pnatr_eq0. Qed.

Lemma eqNr x : (- x == x) = (x == 0).
Proof. by rewrite eq_sym -addr_eq0 -mulr2n mulrn_eq0. Qed.

Lemma mulrIn x : x != 0 -> injective (GRing.natmul x).
Proof.
move=> x_neq0 m n; without loss /subnK <-: m n / (n <= m)%N.
  by move=> IH eq_xmn; case/orP: (leq_total m n) => /IH->.
by move/eqP; rewrite mulrnDr -subr_eq0 addrK mulrn_eq0 => /predU1P[-> | /idPn].
Qed.

Lemma ler_wpMn2l x :
  0 <= x -> {homo (@GRing.natmul R x) : m n / (m <= n)%N >-> m <= n}.
Proof. by move=> xge0 m n /subnK <-; rewrite mulrnDr ler_wpDl ?mulrn_wge0. Qed.

Lemma ler_wnMn2l x :
  x <= 0 -> {homo (@GRing.natmul R x) : m n / (n <= m)%N >-> m <= n}.
Proof.
by move=> xle0 m n hmn /=; rewrite -lerN2 -!mulNrn ler_wpMn2l // oppr_cp0.
Qed.

Lemma mulrn_wgt0 x n : 0 < x -> 0 < x *+ n = (0 < n)%N.
Proof. by case: n => // n hx; rewrite pmulrn_lgt0. Qed.

Lemma mulrn_wlt0 x n : x < 0 -> x *+ n < 0 = (0 < n)%N.
Proof. by case: n => // n hx; rewrite pmulrn_llt0. Qed.

Lemma ler_pMn2l x :
  0 < x -> {mono (@GRing.natmul R x) : m n / (m <= n)%N >-> m <= n}.
Proof.
move=> x_gt0 m n /=; case: leqP => hmn; first by rewrite ler_wpMn2l // ltW.
by rewrite -(subnK (ltnW hmn)) mulrnDr gerDr lt_geF // mulrn_wgt0 // subn_gt0.
Qed.

Lemma ltr_pMn2l x :
  0 < x -> {mono (@GRing.natmul R x) : m n / (m < n)%N >-> m < n}.
Proof. by move=> x_gt0; apply: leW_mono (ler_pMn2l _). Qed.

Lemma ler_nMn2l x :
  x < 0 -> {mono (@GRing.natmul R x) : m n / (n <= m)%N >-> m <= n}.
Proof. by move=> xlt0 m n /=; rewrite -lerN2 -!mulNrn ler_pMn2l// oppr_gt0. Qed.

Lemma ltr_nMn2l x :
  x < 0 -> {mono (@GRing.natmul R x) : m n / (n < m)%N >-> m < n}.
Proof. by move=> x_lt0; apply: leW_nmono (ler_nMn2l _). Qed.

Lemma ler_nat m n : (m%:R <= n%:R :> R) = (m <= n)%N.
Proof. by rewrite ler_pMn2l. Qed.

Lemma ltr_nat m n : (m%:R < n%:R :> R) = (m < n)%N.
Proof. by rewrite ltr_pMn2l. Qed.

Lemma eqr_nat m n : (m%:R == n%:R :> R) = (m == n)%N.
Proof. by rewrite (inj_eq (mulrIn _)) ?oner_eq0. Qed.

Lemma pnatr_eq1 n : (n%:R == 1 :> R) = (n == 1)%N.
Proof. exact: eqr_nat 1. Qed.

Lemma lern0 n : (n%:R <= 0 :> R) = (n == 0).
Proof. by rewrite -[0]/0%:R ler_nat leqn0. Qed.

Lemma ltrn0 n : (n%:R < 0 :> R) = false.
Proof. by rewrite -[0]/0%:R ltr_nat ltn0. Qed.

Lemma ler1n n : 1 <= n%:R :> R = (1 <= n)%N. Proof. by rewrite -ler_nat. Qed.
Lemma ltr1n n : 1 < n%:R :> R = (1 < n)%N. Proof. by rewrite -ltr_nat. Qed.
Lemma lern1 n : n%:R <= 1 :> R = (n <= 1)%N. Proof. by rewrite -ler_nat. Qed.
Lemma ltrn1 n : n%:R < 1 :> R = (n < 1)%N. Proof. by rewrite -ltr_nat. Qed.

Lemma ltrN10 : -1 < 0 :> R. Proof. by rewrite oppr_lt0. Qed.
Lemma lerN10 : -1 <= 0 :> R. Proof. by rewrite oppr_le0. Qed.
Lemma ltr10 : 1 < 0 :> R = false. Proof. by rewrite le_gtF. Qed.
Lemma ler10 : 1 <= 0 :> R = false. Proof. by rewrite lt_geF. Qed.
Lemma ltr0N1 : 0 < -1 :> R = false. Proof. by rewrite le_gtF // lerN10. Qed.
Lemma ler0N1 : 0 <= -1 :> R = false. Proof. by rewrite lt_geF // ltrN10. Qed.

#[deprecated(since="mathcomp 2.4.0", note="use `mulrn_wgt0` instead")]
Lemma pmulrn_rgt0 x n : 0 < x -> 0 < x *+ n = (0 < n)%N.
Proof. exact: mulrn_wgt0. Qed.

Lemma pmulrn_rlt0 x n : 0 < x -> x *+ n < 0 = false.
Proof. by move=> x_gt0; rewrite -(mulr0n x) ltr_pMn2l. Qed.

Lemma pmulrn_rge0 x n : 0 < x -> 0 <= x *+ n.
Proof. by move=> x_gt0; rewrite -(mulr0n x) ler_pMn2l. Qed.

Lemma pmulrn_rle0 x n : 0 < x -> x *+ n <= 0 = (n == 0)%N.
Proof. by move=> x_gt0; rewrite -(mulr0n x) ler_pMn2l ?leqn0. Qed.

Lemma nmulrn_rgt0 x n : x < 0 -> 0 < x *+ n = false.
Proof. by move=> x_lt0; rewrite -(mulr0n x) ltr_nMn2l. Qed.

Lemma nmulrn_rge0 x n : x < 0 -> 0 <= x *+ n = (n == 0)%N.
Proof. by move=> x_lt0; rewrite -(mulr0n x) ler_nMn2l ?leqn0. Qed.

Lemma nmulrn_rle0 x n : x < 0 -> x *+ n <= 0.
Proof. by move=> x_lt0; rewrite -(mulr0n x) ler_nMn2l. Qed.

(* (x * y) compared to 0 *)
(* Remark : pmulr_rgt0 and pmulr_rge0 are defined above *)

(* x positive and y right *)
Lemma pmulr_rlt0 x y : 0 < x -> (x * y < 0) = (y < 0).
Proof.
by move=> x_gt0; rewrite -[LHS]oppr_gt0 -mulrN pmulr_rgt0 // oppr_gt0.
Qed.

Lemma pmulr_rle0 x y : 0 < x -> (x * y <= 0) = (y <= 0).
Proof.
by move=> x_gt0; rewrite -[LHS]oppr_ge0 -mulrN pmulr_rge0 // oppr_ge0.
Qed.

(* x positive and y left *)
Lemma pmulr_lgt0 x y : 0 < x -> (0 < y * x) = (0 < y).
Proof. by move=> x_gt0; rewrite mulrC pmulr_rgt0. Qed.

Lemma pmulr_lge0 x y : 0 < x -> (0 <= y * x) = (0 <= y).
Proof. by move=> x_gt0; rewrite mulrC pmulr_rge0. Qed.

Lemma pmulr_llt0 x y : 0 < x -> (y * x < 0) = (y < 0).
Proof. by move=> x_gt0; rewrite mulrC pmulr_rlt0. Qed.

Lemma pmulr_lle0 x y : 0 < x -> (y * x <= 0) = (y <= 0).
Proof. by move=> x_gt0; rewrite mulrC pmulr_rle0. Qed.

(* x negative and y right *)
Lemma nmulr_rgt0 x y : x < 0 -> (0 < x * y) = (y < 0).
Proof. by move=> x_lt0; rewrite -mulrNN pmulr_rgt0 lterNE. Qed.

Lemma nmulr_rge0 x y : x < 0 -> (0 <= x * y) = (y <= 0).
Proof. by move=> x_lt0; rewrite -mulrNN pmulr_rge0 lterNE. Qed.

Lemma nmulr_rlt0 x y : x < 0 -> (x * y < 0) = (0 < y).
Proof. by move=> x_lt0; rewrite -mulrNN pmulr_rlt0 lterNE. Qed.

Lemma nmulr_rle0 x y : x < 0 -> (x * y <= 0) = (0 <= y).
Proof. by move=> x_lt0; rewrite -mulrNN pmulr_rle0 lterNE. Qed.

(* x negative and y left *)
Lemma nmulr_lgt0 x y : x < 0 -> (0 < y * x) = (y < 0).
Proof. by move=> x_lt0; rewrite mulrC nmulr_rgt0. Qed.

Lemma nmulr_lge0 x y : x < 0 -> (0 <= y * x) = (y <= 0).
Proof. by move=> x_lt0; rewrite mulrC nmulr_rge0. Qed.

Lemma nmulr_llt0 x y : x < 0 -> (y * x < 0) = (0 < y).
Proof. by move=> x_lt0; rewrite mulrC nmulr_rlt0. Qed.

Lemma nmulr_lle0 x y : x < 0 -> (y * x <= 0) = (0 <= y).
Proof. by move=> x_lt0; rewrite mulrC nmulr_rle0. Qed.

(* weak and symmetric lemmas *)
Lemma mulr_ge0 x y : 0 <= x -> 0 <= y -> 0 <= x * y.
Proof. by move=> x_ge0 y_ge0; rewrite -(mulr0 x) ler_wpM2l. Qed.

Lemma mulr_le0 x y : x <= 0 -> y <= 0 -> 0 <= x * y.
Proof. by move=> x_le0 y_le0; rewrite -(mulr0 x) ler_wnM2l. Qed.

Lemma mulr_ge0_le0 x y : 0 <= x -> y <= 0 -> x * y <= 0.
Proof. by move=> x_le0 y_le0; rewrite -(mulr0 x) ler_wpM2l. Qed.

Lemma mulr_le0_ge0 x y : x <= 0 -> 0 <= y -> x * y <= 0.
Proof. by move=> x_le0 y_le0; rewrite -(mulr0 x) ler_wnM2l. Qed.

(* mulr_gt0 with only one case *)

Lemma mulr_gt0 x y : 0 < x -> 0 < y -> 0 < x * y.
Proof. by move=> x_gt0 y_gt0; rewrite pmulr_rgt0. Qed.

(* and reverse direction *)

Lemma mulr_ge0_gt0 x y : 0 <= x -> 0 <= y -> (0 < x * y) = (0 < x) && (0 < y).
Proof.
rewrite le_eqVlt => /predU1P[<-|x0]; first by rewrite mul0r ltxx.
rewrite le_eqVlt => /predU1P[<-|y0]; first by rewrite mulr0 ltxx andbC.
by apply/idP/andP=> [|_]; rewrite pmulr_rgt0.
Qed.

(* Iterated products *)

Lemma prodr_ge0 I r (P : pred I) (E : I -> R) :
  (forall i, P i -> 0 <= E i) -> 0 <= \prod_(i <- r | P i) E i.
Proof. by move=> Ege0; rewrite -nnegrE rpred_prod. Qed.

Lemma prodr_gt0 I r (P : pred I) (E : I -> R) :
  (forall i, P i -> 0 < E i) -> 0 < \prod_(i <- r | P i) E i.
Proof. by move=> Ege0; rewrite -posrE rpred_prod. Qed.

Lemma ler_prod I r (P : pred I) (E1 E2 : I -> R) :
    (forall i, P i -> 0 <= E1 i <= E2 i) ->
  \prod_(i <- r | P i) E1 i <= \prod_(i <- r | P i) E2 i.
Proof.
move=> leE12; elim/(big_load (fun x => 0 <= x)): _.
elim/big_rec2: _ => // i x2 x1 /leE12/andP[le0Ei leEi12] [x1ge0 le_x12].
by rewrite mulr_ge0 // ler_pM.
Qed.

Lemma ltr_prod I r (P : pred I) (E1 E2 : I -> R) :
    has P r -> (forall i, P i -> 0 <= E1 i < E2 i) ->
  \prod_(i <- r | P i) E1 i < \prod_(i <- r | P i) E2 i.
Proof.
elim: r => //= i r IHr; rewrite !big_cons; case: ifP => {IHr}// Pi _ ltE12.
have /andP[le0E1i ltE12i] := ltE12 i Pi; set E2r := \prod_(j <- r | P j) E2 j.
apply: le_lt_trans (_ : E1 i * E2r < E2 i * E2r).
  by rewrite ler_wpM2l ?ler_prod // => j /ltE12/andP[-> /ltW].
by rewrite ltr_pM2r ?prodr_gt0 // => j /ltE12/andP[le0E1j /le_lt_trans->].
Qed.

Lemma ltr_prod_nat (E1 E2 : nat -> R) (n m : nat) :
   (m < n)%N -> (forall i, (m <= i < n)%N -> 0 <= E1 i < E2 i) ->
  \prod_(m <= i < n) E1 i < \prod_(m <= i < n) E2 i.
Proof.
move=> lt_mn ltE12; rewrite !big_nat ltr_prod {ltE12}//.
by apply/hasP; exists m; rewrite ?mem_index_iota leqnn.
Qed.

(* real of mul *)

Lemma realMr x y : x != 0 -> x \is real -> (x * y \is real) = (y \is real).
Proof.
move=> x_neq0 xR; case: real_ltgtP x_neq0 => // hx _; rewrite !realE.
  by rewrite nmulr_rge0 // nmulr_rle0 // orbC.
by rewrite pmulr_rge0 // pmulr_rle0 // orbC.
Qed.

Lemma realrM x y : y != 0 -> y \is real -> (x * y \is real) = (x \is real).
Proof. by move=> y_neq0 yR; rewrite mulrC realMr. Qed.

Lemma realM : {in real &, forall x y, x * y \is real}.
Proof. exact: rpredM. Qed.

Lemma realrMn x n : (n != 0)%N -> (x *+ n \is real) = (x \is real).
Proof. by move=> n_neq0; rewrite -mulr_natl realMr ?realn ?pnatr_eq0. Qed.

(* ler/ltr and multiplication between a positive/negative *)

Lemma ger_pMl x y : 0 < y -> (x * y <= y) = (x <= 1).
Proof. by move=> hy; rewrite -{2}[y]mul1r ler_pM2r. Qed.

Lemma gtr_pMl x y : 0 < y -> (x * y < y) = (x < 1).
Proof. by move=> hy; rewrite -{2}[y]mul1r ltr_pM2r. Qed.

Lemma ger_pMr x y : 0 < y -> (y * x <= y) = (x <= 1).
Proof. by move=> hy; rewrite -{2}[y]mulr1 ler_pM2l. Qed.

Lemma gtr_pMr x y : 0 < y -> (y * x < y) = (x < 1).
Proof. by move=> hy; rewrite -{2}[y]mulr1 ltr_pM2l. Qed.

Lemma ler_pMl x y : 0 < y -> (y <= x * y) = (1 <= x).
Proof. by move=> hy; rewrite -{1}[y]mul1r ler_pM2r. Qed.

Lemma ltr_pMl x y : 0 < y -> (y < x * y) = (1 < x).
Proof. by move=> hy; rewrite -{1}[y]mul1r ltr_pM2r. Qed.

Lemma ler_pMr x y : 0 < y -> (y <= y * x) = (1 <= x).
Proof. by move=> hy; rewrite -{1}[y]mulr1 ler_pM2l. Qed.

Lemma ltr_pMr x y : 0 < y -> (y < y * x) = (1 < x).
Proof. by move=> hy; rewrite -{1}[y]mulr1 ltr_pM2l. Qed.

Lemma ger_nMl x y : y < 0 -> (x * y <= y) = (1 <= x).
Proof. by move=> hy; rewrite -{2}[y]mul1r ler_nM2r. Qed.

Lemma gtr_nMl x y : y < 0 -> (x * y < y) = (1 < x).
Proof. by move=> hy; rewrite -{2}[y]mul1r ltr_nM2r. Qed.

Lemma ger_nMr x y : y < 0 -> (y * x <= y) = (1 <= x).
Proof. by move=> hy; rewrite -{2}[y]mulr1 ler_nM2l. Qed.

Lemma gtr_nMr x y : y < 0 -> (y * x < y) = (1 < x).
Proof. by move=> hy; rewrite -{2}[y]mulr1 ltr_nM2l. Qed.

Lemma ler_nMl x y : y < 0 -> (y <= x * y) = (x <= 1).
Proof. by move=> hy; rewrite -{1}[y]mul1r ler_nM2r. Qed.

Lemma ltr_nMl x y : y < 0 -> (y < x * y) = (x < 1).
Proof. by move=> hy; rewrite -{1}[y]mul1r ltr_nM2r. Qed.

Lemma ler_nMr x y : y < 0 -> (y <= y * x) = (x <= 1).
Proof. by move=> hy; rewrite -{1}[y]mulr1 ler_nM2l. Qed.

Lemma ltr_nMr x y : y < 0 -> (y < y * x) = (x < 1).
Proof. by move=> hy; rewrite -{1}[y]mulr1 ltr_nM2l. Qed.

(* ler/ltr and multiplication between a positive/negative
   and a exterior (1 <= _) or interior (0 <= _ <= 1) *)

Lemma ler_peMl x y : 0 <= y -> 1 <= x -> y <= x * y.
Proof. by move=> hy hx; rewrite -{1}[y]mul1r ler_wpM2r. Qed.

Lemma ler_neMl x y : y <= 0 -> 1 <= x -> x * y <= y.
Proof. by move=> hy hx; rewrite -{2}[y]mul1r ler_wnM2r. Qed.

Lemma ler_peMr x y : 0 <= y -> 1 <= x -> y <= y * x.
Proof. by move=> hy hx; rewrite -{1}[y]mulr1 ler_wpM2l. Qed.

Lemma ler_neMr x y : y <= 0 -> 1 <= x -> y * x <= y.
Proof. by move=> hy hx; rewrite -{2}[y]mulr1 ler_wnM2l. Qed.

Lemma ler_piMl x y : 0 <= y -> x <= 1 -> x * y <= y.
Proof. by move=> hy hx; rewrite -{2}[y]mul1r ler_wpM2r. Qed.

Lemma ler_niMl x y : y <= 0 -> x <= 1 -> y <= x * y.
Proof. by move=> hy hx; rewrite -{1}[y]mul1r ler_wnM2r. Qed.

Lemma ler_piMr x y : 0 <= y -> x <= 1 -> y * x <= y.
Proof. by move=> hy hx; rewrite -{2}[y]mulr1 ler_wpM2l. Qed.

Lemma ler_niMr x y : y <= 0 -> x <= 1 -> y <= y * x.
Proof. by move=> hx hy; rewrite -{1}[y]mulr1 ler_wnM2l. Qed.

Lemma mulr_ile1 x y : 0 <= x -> 0 <= y -> x <= 1 -> y <= 1 -> x * y <= 1.
Proof. by move=> *; rewrite (@le_trans _ _ y) ?ler_piMl. Qed.

Lemma mulr_ilt1 x y : 0 <= x -> 0 <= y -> x < 1 -> y < 1 -> x * y < 1.
Proof. by move=> *; rewrite (@le_lt_trans _ _ y) ?ler_piMl // ltW. Qed.

Definition mulr_ilte1 := (mulr_ile1, mulr_ilt1).

Lemma mulr_ege1 x y : 1 <= x -> 1 <= y -> 1 <= x * y.
Proof.
by move=> le1x le1y; rewrite (@le_trans _ _ y) ?ler_peMl // (le_trans ler01).
Qed.

Lemma mulr_egt1 x y : 1 < x -> 1 < y -> 1 < x * y.
Proof.
by move=> le1x lt1y; rewrite (@lt_trans _ _ y) // ltr_pMl // (lt_trans ltr01).
Qed.
Definition mulr_egte1 := (mulr_ege1, mulr_egt1).
Definition mulr_cp1 := (mulr_ilte1, mulr_egte1).

(* ler and ^-1 *)

Lemma invr_gt0 x : (0 < x^-1) = (0 < x).
Proof.
have [ux | nux] := boolP (x \is a GRing.unit); last by rewrite invr_out.
by apply/idP/idP=> /ltr_pM2r <-; rewrite mul0r (mulrV, mulVr) ?ltr01.
Qed.

Lemma invr_ge0 x : (0 <= x^-1) = (0 <= x).
Proof. by rewrite !le0r invr_gt0 invr_eq0. Qed.

Lemma invr_lt0 x : (x^-1 < 0) = (x < 0).
Proof. by rewrite -oppr_cp0 -invrN invr_gt0 oppr_cp0. Qed.

Lemma invr_le0 x : (x^-1 <= 0) = (x <= 0).
Proof. by rewrite -oppr_cp0 -invrN invr_ge0 oppr_cp0. Qed.

Definition invr_gte0 := (invr_ge0, invr_gt0).
Definition invr_lte0 := (invr_le0, invr_lt0).

Lemma divr_ge0 x y : 0 <= x -> 0 <= y -> 0 <= x / y.
Proof. by move=> x_ge0 y_ge0; rewrite mulr_ge0 ?invr_ge0. Qed.

Lemma divr_gt0 x y : 0 < x -> 0 < y -> 0 < x / y.
Proof. by move=> x_gt0 y_gt0; rewrite pmulr_rgt0 ?invr_gt0. Qed.

Lemma realV : {mono (@GRing.inv R) : x / x \is real}.
Proof. exact: rpredV. Qed.

(* ler and exprn *)
Lemma exprn_ge0 n x : 0 <= x -> 0 <= x ^+ n.
Proof. by move=> xge0; rewrite -nnegrE rpredX. Qed.

Lemma realX n : {in real, forall x, x ^+ n \is real}.
Proof. exact: rpredX. Qed.

Lemma exprn_gt0 n x : 0 < x -> 0 < x ^+ n.
Proof.
by rewrite !lt0r expf_eq0 => /andP[/negPf-> /exprn_ge0->]; rewrite andbF.
Qed.

Definition exprn_gte0 := (exprn_ge0, exprn_gt0).

Lemma exprn_ile1 n x : 0 <= x -> x <= 1 -> x ^+ n <= 1.
Proof.
move=> xge0 xle1; elim: n=> [|*]; rewrite ?expr0 // exprS.
by rewrite mulr_ile1 ?exprn_ge0.
Qed.

Lemma exprn_ilt1 n x : 0 <= x -> x < 1 -> x ^+ n < 1 = (n != 0).
Proof.
move=> xge0 xlt1.
case: n; [by rewrite eqxx ltxx | elim=> [|n ihn]; first by rewrite expr1].
by rewrite exprS mulr_ilt1 // exprn_ge0.
Qed.

Definition exprn_ilte1 := (exprn_ile1, exprn_ilt1).

Lemma exprn_ege1 n x : 1 <= x -> 1 <= x ^+ n.
Proof.
by move=> x_ge1; elim: n=> [|n ihn]; rewrite ?expr0 // exprS mulr_ege1.
Qed.

Lemma exprn_egt1 n x : 1 < x -> 1 < x ^+ n = (n != 0).
Proof.
move=> xgt1; case: n; first by rewrite eqxx ltxx.
by elim=> [|n ihn]; rewrite ?expr1// exprS mulr_egt1 // exprn_ge0.
Qed.

Definition exprn_egte1 := (exprn_ege1, exprn_egt1).
Definition exprn_cp1 := (exprn_ilte1, exprn_egte1).

Lemma ler_iXnr x n : (0 < n)%N -> 0 <= x -> x <= 1 -> x ^+ n <= x.
Proof. by case: n => n // *; rewrite exprS ler_piMr // exprn_ile1. Qed.

Lemma ltr_iXnr x n : 0 < x -> x < 1 -> (x ^+ n < x) = (1 < n)%N.
Proof.
case: n=> [|[|n]] //; first by rewrite expr0 => _ /lt_gtF ->.
by move=> x0 x1; rewrite exprS gtr_pMr // ?exprn_ilt1 // ltW.
Qed.

Definition lter_iXnr := (ler_iXnr, ltr_iXnr).

Lemma ler_eXnr x n : (0 < n)%N -> 1 <= x -> x <= x ^+ n.
Proof.
case: n => // n _ x_ge1.
by rewrite exprS ler_peMr ?(le_trans _ x_ge1) // exprn_ege1.
Qed.

Lemma ltr_eXnr x n : 1 < x -> (x < x ^+ n) = (1 < n)%N.
Proof.
move=> x_ge1; case: n=> [|[|n]] //; first by rewrite expr0 lt_gtF.
by rewrite exprS ltr_pMr ?(lt_trans _ x_ge1) ?exprn_egt1.
Qed.

Definition lter_eXnr := (ler_eXnr, ltr_eXnr).
Definition lter_Xnr := (lter_iXnr, lter_eXnr).

Lemma ler_wiXn2l x :
  0 <= x -> x <= 1 -> {homo GRing.exp x : m n / (n <= m)%N >-> m <= n}.
Proof.
move=> xge0 xle1 m n /= hmn.
by rewrite -(subnK hmn) exprD ler_piMl ?(exprn_ge0, exprn_ile1).
Qed.

Lemma ler_weXn2l x : 1 <= x -> {homo GRing.exp x : m n / (m <= n)%N >-> m <= n}.
Proof.
move=> xge1 m n /= hmn; rewrite -(subnK hmn) exprD.
by rewrite ler_peMl ?(exprn_ge0, exprn_ege1) // (le_trans _ xge1) ?ler01.
Qed.

Lemma ieexprn_weq1 x n : 0 <= x -> (x ^+ n == 1) = ((n == 0) || (x == 1)).
Proof.
move=> xle0; case: n => [|n]; first by rewrite expr0 eqxx.
case: (@real_ltgtP x 1); do ?by rewrite ?ger0_real.
+ by move=> x_lt1; rewrite 1?lt_eqF // exprn_ilt1.
+ by move=> x_lt1; rewrite 1?gt_eqF // exprn_egt1.
by move->; rewrite expr1n eqxx.
Qed.

Lemma ieexprIn x : 0 < x -> x != 1 -> injective (GRing.exp x).
Proof.
move=> x_gt0 x_neq1 m n; without loss /subnK <-: m n / (n <= m)%N.
  by move=> IH eq_xmn; case/orP: (leq_total m n) => /IH->.
case: {m}(m - n)%N => // m /eqP/idPn[]; rewrite -[x ^+ n]mul1r exprD.
by rewrite (inj_eq (mulIf _)) ?ieexprn_weq1 ?ltW // expf_neq0 ?gt_eqF.
Qed.

Lemma ler_iXn2l x :
  0 < x -> x < 1 -> {mono GRing.exp x : m n / (n <= m)%N >-> m <= n}.
Proof.
move=> xgt0 xlt1; apply: (le_nmono (inj_nhomo_lt _ _)); last first.
  by apply/ler_wiXn2l; exact/ltW.
by apply: ieexprIn; rewrite ?lt_eqF ?ltr_cpable.
Qed.

Lemma ltr_iXn2l x :
  0 < x -> x < 1 -> {mono GRing.exp x : m n / (n < m)%N >-> m < n}.
Proof. by move=> xgt0 xlt1; apply: (leW_nmono (ler_iXn2l _ _)). Qed.

Definition lter_iXn2l := (ler_iXn2l, ltr_iXn2l).

Lemma ler_eXn2l x :
  1 < x -> {mono GRing.exp x : m n / (m <= n)%N >-> m <= n}.
Proof.
move=> xgt1; apply: (le_mono (inj_homo_lt _ _)); last first.
  by apply: ler_weXn2l; rewrite ltW.
by apply: ieexprIn; rewrite ?gt_eqF ?gtr_cpable //; apply: lt_trans xgt1.
Qed.

Lemma ltr_eXn2l x :
  1 < x -> {mono (GRing.exp x) : m n / (m < n)%N >-> m < n}.
Proof. by move=> xgt1; apply: (leW_mono (ler_eXn2l _)). Qed.

Definition lter_eXn2l := (ler_eXn2l, ltr_eXn2l).

Lemma ltrXn2r n x y : 0 <= x -> x < y -> x ^+ n < y ^+ n = (n != 0).
Proof.
move=> xge0 xlty; case: n; first by rewrite ltxx.
elim=> [|n IHn]; rewrite ?[_ ^+ _.+2]exprS //.
rewrite (@le_lt_trans _ _ (x * y ^+ n.+1)) ?ler_wpM2l ?ltr_pM2r ?IHn //.
  by rewrite ltW.
by rewrite exprn_gt0 // (le_lt_trans xge0).
Qed.

Lemma lerXn2r n : {in nneg & , {homo (@GRing.exp R)^~ n : x y / x <= y}}.
Proof.
move=> x y /= x0 y0 xy; elim: n => [|n IHn]; rewrite !(expr0, exprS) //.
by rewrite (@le_trans _ _ (x * y ^+ n)) ?ler_wpM2l ?ler_wpM2r ?exprn_ge0.
Qed.

Definition lterXn2r := (lerXn2r, ltrXn2r).

Lemma ltr_wpXn2r n :
  (0 < n)%N -> {in nneg & , {homo (@GRing.exp R)^~ n : x y / x < y}}.
Proof. by move=> ngt0 x y /= x0 y0 hxy; rewrite ltrXn2r // -lt0n. Qed.

Lemma ler_pXn2r n :
  (0 < n)%N -> {in nneg & , {mono (@GRing.exp R)^~ n : x y / x <= y}}.
Proof.
case: n => // n _ x y; rewrite !qualifE /= =>  x_ge0 y_ge0.
have [-> | nzx] := eqVneq x 0; first by rewrite exprS mul0r exprn_ge0.
rewrite -subr_ge0 subrXX pmulr_lge0 ?subr_ge0 //= big_ord_recr /=.
rewrite subnn expr0 mul1r /= ltr_pwDr // ?exprn_gt0 ?lt0r ?nzx //.
by rewrite sumr_ge0 // => i _; rewrite mulr_ge0 ?exprn_ge0.
Qed.

Lemma ltr_pXn2r n :
  (0 < n)%N -> {in nneg & , {mono (@GRing.exp R)^~ n : x y / x < y}}.
Proof.
by move=> n_gt0 x y x_ge0 y_ge0; rewrite !lt_neqAle !eq_le !ler_pXn2r.
Qed.

Definition lter_pXn2r := (ler_pXn2r, ltr_pXn2r).

Lemma pexpIrn n : (0 < n)%N -> {in nneg &, injective ((@GRing.exp R)^~ n)}.
Proof. by move=> n_gt0; apply: inc_inj_in (ler_pXn2r _). Qed.

(* expr and ler/ltr *)
Lemma expr_le1 n x : (0 < n)%N -> 0 <= x -> (x ^+ n <= 1) = (x <= 1).
Proof.
by move=> ngt0 xge0; rewrite -{1}[1](expr1n _ n) ler_pXn2r // [_ \in _]ler01.
Qed.

Lemma expr_lt1 n x : (0 < n)%N -> 0 <= x -> (x ^+ n < 1) = (x < 1).
Proof.
by move=> ngt0 xge0; rewrite -{1}[1](expr1n _ n) ltr_pXn2r // [_ \in _]ler01.
Qed.

Definition expr_lte1 := (expr_le1, expr_lt1).

Lemma expr_ge1 n x : (0 < n)%N -> 0 <= x -> (1 <= x ^+ n) = (1 <= x).
Proof.
by move=> ngt0 xge0; rewrite -{1}[1](expr1n _ n) ler_pXn2r // [_ \in _]ler01.
Qed.

Lemma expr_gt1 n x : (0 < n)%N -> 0 <= x -> (1 < x ^+ n) = (1 < x).
Proof.
by move=> ngt0 xge0; rewrite -{1}[1](expr1n _ n) ltr_pXn2r // [_ \in _]ler01.
Qed.

Definition expr_gte1 := (expr_ge1, expr_gt1).

Lemma pexpr_eq1 x n : (0 < n)%N -> 0 <= x -> (x ^+ n == 1) = (x == 1).
Proof. by move=> ngt0 xge0; rewrite !eq_le expr_le1 // expr_ge1. Qed.

Lemma pexprn_eq1 x n : 0 <= x -> (x ^+ n == 1) = (n == 0) || (x == 1).
Proof. by case: n => [|n] xge0; rewrite ?eqxx // pexpr_eq1 ?gtn_eqF. Qed.

Lemma eqrXn2 n x y :
  (0 < n)%N -> 0 <= x -> 0 <= y -> (x ^+ n == y ^+ n) = (x == y).
Proof. by move=> ngt0 xge0 yge0; rewrite (inj_in_eq (pexpIrn _)). Qed.

Lemma sqrp_eq1 x : 0 <= x -> (x ^+ 2 == 1) = (x == 1).
Proof. by move/pexpr_eq1->. Qed.

Lemma sqrn_eq1 x : x <= 0 -> (x ^+ 2 == 1) = (x == -1).
Proof. by rewrite -sqrrN -oppr_ge0 -eqr_oppLR => /sqrp_eq1. Qed.

Lemma ler_sqr : {in nneg &, {mono (fun x => x ^+ 2) : x y / x <= y}}.
Proof. exact: ler_pXn2r. Qed.

Lemma ltr_sqr : {in nneg &, {mono (fun x => x ^+ 2) : x y / x < y}}.
Proof. exact: ltr_pXn2r. Qed.

Lemma ler_pV2 :
  {in [pred x in GRing.unit | 0 < x] &, {mono (@GRing.inv R) : x y /~ x <= y}}.
Proof.
move=> x y /andP [ux hx] /andP [uy hy] /=.
by rewrite -(ler_pM2l hx) -(ler_pM2r hy) !(divrr, mulrVK) ?unitf_gt0 // mul1r.
Qed.

Lemma ler_nV2 :
  {in [pred x in GRing.unit | x < 0] &, {mono (@GRing.inv R) : x y /~ x <= y}}.
Proof.
move=> x y /andP [ux hx] /andP [uy hy] /=.
by rewrite -(ler_nM2l hx) -(ler_nM2r hy) !(divrr, mulrVK) ?unitf_lt0 // mul1r.
Qed.

Lemma ltr_pV2 :
  {in [pred x in GRing.unit | 0 < x] &, {mono (@GRing.inv R) : x y /~ x < y}}.
Proof. exact: leW_nmono_in ler_pV2. Qed.

Lemma ltr_nV2 :
  {in [pred x in GRing.unit | x < 0] &, {mono (@GRing.inv R) : x y /~ x < y}}.
Proof. exact: leW_nmono_in ler_nV2. Qed.

Lemma invr_gt1 x : x \is a GRing.unit -> 0 < x -> (1 < x^-1) = (x < 1).
Proof.
by move=> Ux xgt0; rewrite -{1}[1]invr1 ltr_pV2 ?inE ?unitr1 ?ltr01 ?Ux.
Qed.

Lemma invr_ge1 x : x \is a GRing.unit -> 0 < x -> (1 <= x^-1) = (x <= 1).
Proof.
by move=> Ux xgt0; rewrite -{1}[1]invr1 ler_pV2 ?inE ?unitr1 ?ltr01 // Ux.
Qed.

Definition invr_gte1 := (invr_ge1, invr_gt1).

Lemma invr_le1 x (ux : x \is a GRing.unit) (hx : 0 < x) :
  (x^-1 <= 1) = (1 <= x).
Proof. by rewrite -invr_ge1 ?invr_gt0 ?unitrV // invrK. Qed.

Lemma invr_lt1 x (ux : x \is a GRing.unit) (hx : 0 < x) : (x^-1 < 1) = (1 < x).
Proof. by rewrite -invr_gt1 ?invr_gt0 ?unitrV // invrK. Qed.

Definition invr_lte1 := (invr_le1, invr_lt1).
Definition invr_cp1 := (invr_gte1, invr_lte1).

(* max and min *)

Lemma addr_min_max x y : min x y + max x y = x + y.
Proof. by rewrite /min /max; case: ifP => //; rewrite addrC. Qed.

Lemma addr_max_min x y : max x y + min x y = x + y.
Proof. by rewrite addrC addr_min_max. Qed.

Lemma minr_to_max x y : min x y = x + y - max x y.
Proof. by rewrite -[x + y]addr_min_max addrK. Qed.

Lemma maxr_to_min x y : max x y = x + y - min x y.
Proof. by rewrite -[x + y]addr_max_min addrK. Qed.

Lemma real_oppr_max : {in real &, {morph -%R : x y / max x y >-> min x y : R}}.
Proof.
by move=> x y xr yr; rewrite !(fun_if, if_arg) ltrN2; case: real_ltgtP => // ->.
Qed.

Lemma real_oppr_min : {in real &, {morph -%R : x y / min x y >-> max x y : R}}.
Proof.
by move=> x y xr yr; rewrite -[RHS]opprK real_oppr_max ?realN// !opprK.
Qed.

Lemma real_addr_minl : {in real & real & real, @left_distributive R R +%R min}.
Proof.
by move=> x y z xr yr zr; case: (@real_leP (_ + _)); rewrite ?realD//;
   rewrite lterD2; case: real_leP.
Qed.

Lemma real_addr_minr : {in real & real & real, @right_distributive R R +%R min}.
Proof. by move=> x y z xr yr zr; rewrite !(addrC x) real_addr_minl. Qed.

Lemma real_addr_maxl : {in real & real & real, @left_distributive R R +%R max}.
Proof.
by move=> x y z xr yr zr; case: (@real_leP (_ + _)); rewrite ?realD//;
   rewrite lterD2; case: real_leP.
Qed.

Lemma real_addr_maxr : {in real & real & real, @right_distributive R R +%R max}.
Proof. by move=> x y z xr yr zr; rewrite !(addrC x) real_addr_maxl. Qed.

Lemma minr_pMr x y z : 0 <= x -> x * min y z = min (x * y) (x * z).
Proof.
have [|x_gt0||->]// := comparableP x; last by rewrite !mul0r minxx.
by rewrite !(fun_if, if_arg) lter_pM2l//; case: (y < z).
Qed.

Lemma maxr_pMr x y z : 0 <= x -> x * max y z = max (x * y) (x * z).
Proof.
have [|x_gt0||->]// := comparableP x; last by rewrite !mul0r maxxx.
by rewrite !(fun_if, if_arg) lter_pM2l//; case: (y < z).
Qed.

Lemma real_maxr_nMr x y z : x <= 0 -> y \is real -> z \is real ->
  x * max y z = min (x * y) (x * z).
Proof.
move=> x0 yr zr; rewrite -[_ * _]opprK -mulrN real_oppr_max// -mulNr.
by rewrite minr_pMr ?oppr_ge0// !(mulNr, mulrN, opprK).
Qed.

Lemma real_minr_nMr x y z :  x <= 0 -> y \is real -> z \is real ->
  x * min y z = max (x * y) (x * z).
Proof.
move=> x0 yr zr; rewrite -[_ * _]opprK -mulrN real_oppr_min// -mulNr.
by rewrite maxr_pMr ?oppr_ge0// !(mulNr, mulrN, opprK).
Qed.

Lemma minr_pMl x y z : 0 <= x -> min y z * x = min (y * x) (z * x).
Proof. by move=> *; rewrite mulrC minr_pMr // ![_ * x]mulrC. Qed.

Lemma maxr_pMl x y z : 0 <= x -> max y z * x = max (y * x) (z * x).
Proof. by move=> *; rewrite mulrC maxr_pMr // ![_ * x]mulrC. Qed.

Lemma real_minr_nMl x y z : x <= 0 -> y \is real -> z \is real ->
  min y z * x = max (y * x) (z * x).
Proof. by move=> *; rewrite mulrC real_minr_nMr // ![_ * x]mulrC. Qed.

Lemma real_maxr_nMl x y z : x <= 0 -> y \is real -> z \is real ->
  max y z * x = min (y * x) (z * x).
Proof. by move=> *; rewrite mulrC real_maxr_nMr // ![_ * x]mulrC. Qed.

Lemma real_maxrN x : x \is real -> max x (- x) = `|x|.
Proof.
move=> x_real; rewrite /max.
by case: real_ge0P => // [/ge0_cp [] | /lt0_cp []];
   case: (@real_leP (- x) x); rewrite ?realN.
Qed.

Lemma real_maxNr x : x \is real -> max (- x) x = `|x|.
Proof.
by move=> x_real; rewrite comparable_maxC ?real_maxrN ?real_comparable ?realN.
Qed.

Lemma real_minrN x : x \is real -> min x (- x) = - `|x|.
Proof.
by move=> x_real; rewrite -[LHS]opprK real_oppr_min ?opprK ?real_maxNr ?realN.
Qed.

Lemma real_minNr x : x \is real ->  min (- x) x = - `|x|.
Proof.
by move=> x_real; rewrite -[LHS]opprK real_oppr_min ?opprK ?real_maxrN ?realN.
Qed.

Section RealDomainArgExtremum.

Context {I : finType} (i0 : I).
Context (P : pred I) (F : I -> R) (Pi0 : P i0).
Hypothesis F_real : {in P, forall i, F i \is real}.

Lemma real_arg_minP : extremum_spec <=%R P F [arg min_(i < i0 | P i) F i].
Proof.
by apply: comparable_arg_minP => // i j iP jP; rewrite real_comparable ?F_real.
Qed.

Lemma real_arg_maxP : extremum_spec >=%R P F [arg max_(i > i0 | P i) F i].
Proof.
by apply: comparable_arg_maxP => // i j iP jP; rewrite real_comparable ?F_real.
Qed.

End RealDomainArgExtremum.

(* norm *)

Lemma real_ler_norm x : x \is real -> x <= `|x|.
Proof.
by case/real_ge0P=> hx //; rewrite (le_trans (ltW hx)) // oppr_ge0 ltW.
Qed.

(* norm + add *)

Section NormedZmoduleTheory.

Variable V : normedZmodType R.
Implicit Types (u v w : V).

Lemma normr_real v : `|v| \is real. Proof. by apply/ger0_real. Qed.
Hint Resolve normr_real : core.

Lemma ler_norm_sum I r (G : I -> V) (P : pred I):
  `|\sum_(i <- r | P i) G i| <= \sum_(i <- r | P i) `|G i|.
Proof.
elim/big_rec2: _ => [|i y x _]; first by rewrite normr0.
by rewrite -(lerD2l `|G i|); apply: le_trans; apply: ler_normD.
Qed.

Lemma ler_normB v w : `|v - w| <= `|v| + `|w|.
Proof. by rewrite (le_trans (ler_normD _ _)) ?normrN. Qed.

Lemma ler_distD u v w : `|v - w| <= `|v - u| + `|u - w|.
Proof. by rewrite (le_trans _ (ler_normD _ _)) // addrA addrNK. Qed.

Lemma lerB_normD v w : `|v| - `|w| <= `|v + w|.
Proof.
by rewrite -{1}[v](addrK w) lterBDl (le_trans (ler_normD _ _))// addrC normrN.
Qed.

Lemma lerB_dist v w : `|v| - `|w| <= `|v - w|.
Proof. by rewrite -[`|w|]normrN lerB_normD. Qed.

Lemma ler_dist_dist v w : `| `|v| - `|w| | <= `|v - w|.
Proof.
have [||_|_] // := @real_leP `|v| `|w|; last by rewrite lerB_dist.
by rewrite distrC lerB_dist.
Qed.

Lemma ler_dist_normD v w : `| `|v| - `|w| | <= `|v + w|.
Proof. by rewrite -[w]opprK normrN ler_dist_dist. Qed.

Lemma ler_nnorml v x : x < 0 -> `|v| <= x = false.
Proof. by move=> h; rewrite lt_geF //; apply/(lt_le_trans h). Qed.

Lemma ltr_nnorml v x : x <= 0 -> `|v| < x = false.
Proof. by move=> h; rewrite le_gtF //; apply/(le_trans h). Qed.

Definition lter_nnormr := (ler_nnorml, ltr_nnorml).

End NormedZmoduleTheory.

Hint Extern 0 (is_true (norm _ \is real)) => apply: normr_real : core.

Lemma real_ler_norml x y : x \is real -> (`|x| <= y) = (- y <= x <= y).
Proof.
move=> xR; wlog x_ge0 : x xR / 0 <= x => [hwlog|].
  move: (xR) => /(@real_leVge 0) /orP [|/hwlog->|hx] //.
  by rewrite -[x]opprK normrN lerN2 andbC lerNl hwlog ?realN ?oppr_ge0.
rewrite ger0_norm //; have [le_xy|] := boolP (x <= y); last by rewrite andbF.
by rewrite (le_trans _ x_ge0) // oppr_le0 (le_trans x_ge0).
Qed.

Lemma real_ler_normlP x y :
  x \is real -> reflect ((-x <= y) * (x <= y)) (`|x| <= y).
Proof.
by move=> Rx; rewrite real_ler_norml // lerNl; apply: (iffP andP) => [] [].
Qed.
Arguments real_ler_normlP {x y}.

Lemma real_eqr_norml x y :
  x \is real -> (`|x| == y) = ((x == y) || (x == -y)) && (0 <= y).
Proof.
move=> Rx.
apply/idP/idP=> [|/andP[/pred2P[]-> /ger0_norm/eqP]]; rewrite ?normrE //.
case: real_le0P => // hx; rewrite 1?eqr_oppLR => /eqP exy.
  by move: hx; rewrite exy ?oppr_le0 eqxx orbT //.
by move: hx=> /ltW; rewrite exy eqxx.
Qed.

Lemma real_eqr_norm2 x y :
  x \is real -> y \is real -> (`|x| == `|y|) = (x == y) || (x == -y).
Proof.
move=> Rx Ry; rewrite real_eqr_norml // normrE andbT.
by case: real_le0P; rewrite // opprK orbC.
Qed.

Lemma real_ltr_norml x y : x \is real -> (`|x| < y) = (- y < x < y).
Proof.
move=> Rx; wlog x_ge0 : x Rx / 0 <= x => [hwlog|].
  move: (Rx) => /(@real_leVge 0) /orP [|/hwlog->|hx] //.
  by rewrite -[x]opprK normrN ltrN2 andbC ltrNl hwlog ?realN ?oppr_ge0.
rewrite ger0_norm //; have [le_xy|] := boolP (x < y); last by rewrite andbF.
by rewrite (lt_le_trans _ x_ge0) // oppr_lt0 (le_lt_trans x_ge0).
Qed.

Definition real_lter_norml := (real_ler_norml, real_ltr_norml).

Lemma real_ltr_normlP x y :
  x \is real -> reflect ((-x < y) * (x < y)) (`|x| < y).
Proof.
by move=> Rx; rewrite real_ltr_norml // ltrNl; apply: (iffP (@andP _ _)); case.
Qed.
Arguments real_ltr_normlP {x y}.

Lemma real_ler_normr x y : y \is real -> (x <= `|y|) = (x <= y) || (x <= - y).
Proof.
move=> Ry.
have [xR|xNR] := boolP (x \is real); last by rewrite ?Nreal_leF ?realN.
rewrite real_leNgt ?real_ltr_norml // negb_and -?real_leNgt ?realN //.
by rewrite orbC lerNr.
Qed.

Lemma real_ltr_normr x y : y \is real -> (x < `|y|) = (x < y) || (x < - y).
Proof.
move=> Ry.
have [xR|xNR] := boolP (x \is real); last by rewrite ?Nreal_ltF ?realN.
rewrite real_ltNge ?real_ler_norml // negb_and -?real_ltNge ?realN //.
by rewrite orbC ltrNr.
Qed.

Definition real_lter_normr := (real_ler_normr, real_ltr_normr).

Lemma real_ltr_normlW x y : x \is real -> `|x| < y -> x < y.
Proof. by move=> ?; case/real_ltr_normlP. Qed.

Lemma real_ltrNnormlW x y : x \is real -> `|x| < y -> - y < x.
Proof. by move=> ?; case/real_ltr_normlP => //; rewrite ltrNl. Qed.

Lemma real_ler_normlW x y : x \is real -> `|x| <= y -> x <= y.
Proof. by move=> ?; case/real_ler_normlP. Qed.

Lemma real_lerNnormlW x y : x \is real -> `|x| <= y -> - y <= x.
Proof. by move=> ?; case/real_ler_normlP => //; rewrite lerNl. Qed.

Lemma real_ler_distl x y e :
  x - y \is real -> (`|x - y| <= e) = (y - e <= x <= y + e).
Proof. by move=> Rxy; rewrite real_lter_norml // !lterBDl. Qed.

Lemma real_ltr_distl x y e :
  x - y \is real -> (`|x - y| < e) = (y - e < x < y + e).
Proof. by move=> Rxy; rewrite real_lter_norml // !lterBDl. Qed.

Definition real_lter_distl := (real_ler_distl, real_ltr_distl).

Lemma real_ltr_distlDr x y e : x - y \is real -> `|x - y| < e -> x < y + e.
Proof. by move=> ?; rewrite real_ltr_distl // => /andP[]. Qed.

Lemma real_ler_distlDr x y e : x - y \is real -> `|x - y| <= e -> x <= y + e.
Proof. by move=> ?; rewrite real_ler_distl // => /andP[]. Qed.

Lemma real_ltr_distlCDr x y e : x - y \is real -> `|x - y| < e -> y < x + e.
Proof. by rewrite realBC (distrC x) => ? /real_ltr_distlDr; apply. Qed.

Lemma real_ler_distlCDr x y e : x - y \is real -> `|x - y| <= e -> y <= x + e.
Proof. by rewrite realBC distrC => ? /real_ler_distlDr; apply. Qed.

Lemma real_ltr_distlBl x y e : x - y \is real -> `|x - y| < e -> x - e < y.
Proof. by move/real_ltr_distlDr; rewrite ltrBlDr; apply. Qed.

Lemma real_ler_distlBl x y e : x - y \is real -> `|x - y| <= e -> x - e <= y.
Proof. by move/real_ler_distlDr; rewrite lerBlDr; apply. Qed.

Lemma real_ltr_distlCBl x y e : x - y \is real -> `|x - y| < e -> y - e < x.
Proof. by rewrite realBC distrC => ? /real_ltr_distlBl; apply. Qed.

Lemma real_ler_distlCBl x y e : x - y \is real -> `|x - y| <= e -> y - e <= x.
Proof. by rewrite realBC distrC => ? /real_ler_distlBl; apply. Qed.

#[deprecated(since="mathcomp 2.3.0", note="use `ger0_def` instead")]
Lemma eqr_norm_id x : (`|x| == x) = (0 <= x). Proof. by rewrite ger0_def. Qed.

#[deprecated(since="mathcomp 2.3.0", note="use `ler0_def` instead")]
Lemma eqr_normN x : (`|x| == - x) = (x <= 0). Proof. by rewrite ler0_def. Qed.

Definition eqr_norm_idVN := =^~ (ger0_def, ler0_def).

Lemma real_exprn_even_ge0 n x : x \is real -> ~~ odd n -> 0 <= x ^+ n.
Proof.
move=> xR even_n; have [/exprn_ge0 -> //|x_lt0] := real_ge0P xR.
rewrite -[x]opprK -mulN1r exprMn -signr_odd (negPf even_n) expr0 mul1r.
by rewrite exprn_ge0 ?oppr_ge0 ?ltW.
Qed.

Lemma real_exprn_even_gt0 n x :
  x \is real -> ~~ odd n -> (0 < x ^+ n) = (n == 0)%N || (x != 0).
Proof.
move=> xR n_even; rewrite lt0r real_exprn_even_ge0 ?expf_eq0 //.
by rewrite andbT negb_and lt0n negbK.
Qed.

Lemma real_exprn_even_le0 n x :
  x \is real -> ~~ odd n -> (x ^+ n <= 0) = (n != 0) && (x == 0).
Proof.
move=> xR n_even; rewrite !real_leNgt ?rpred0 ?rpredX //.
by rewrite real_exprn_even_gt0 // negb_or negbK.
Qed.

Lemma real_exprn_even_lt0 n x :
  x \is real -> ~~ odd n -> (x ^+ n < 0) = false.
Proof. by move=> xR n_even; rewrite le_gtF // real_exprn_even_ge0. Qed.

Lemma real_exprn_odd_ge0 n x :
  x \is real -> odd n -> (0 <= x ^+ n) = (0 <= x).
Proof.
case/real_ge0P => [x_ge0|x_lt0] n_odd; first by rewrite exprn_ge0.
apply: negbTE; rewrite lt_geF //.
case: n n_odd => // n /= n_even; rewrite exprS pmulr_llt0 //.
by rewrite real_exprn_even_gt0 ?ler0_real ?ltW // (lt_eqF x_lt0) ?orbT.
Qed.

Lemma real_exprn_odd_gt0 n x : x \is real -> odd n -> (0 < x ^+ n) = (0 < x).
Proof.
by move=> xR n_odd; rewrite !lt0r expf_eq0 real_exprn_odd_ge0; case: n n_odd.
Qed.

Lemma real_exprn_odd_le0 n x : x \is real -> odd n -> (x ^+ n <= 0) = (x <= 0).
Proof.
by move=> xR n_odd; rewrite !real_leNgt ?rpred0 ?rpredX // real_exprn_odd_gt0.
Qed.

Lemma real_exprn_odd_lt0 n x : x \is real -> odd n -> (x ^+ n < 0) = (x < 0).
Proof.
by move=> xR n_odd; rewrite !real_ltNge ?rpred0 ?rpredX // real_exprn_odd_ge0.
Qed.

(* GG: Could this be a better definition of "real" ? *)
Lemma realEsqr x : (x \is real) = (0 <= x ^+ 2).
Proof. by rewrite ger0_def normrX eqf_sqr -ger0_def -ler0_def. Qed.

Lemma real_normK x : x \is real -> `|x| ^+ 2 = x ^+ 2.
Proof. by move=> Rx; rewrite -normrX ger0_norm -?realEsqr. Qed.

(* Binary sign ((-1) ^+ s). *)

Lemma normr_sign s : `|(-1) ^+ s : R| = 1.
Proof. by rewrite normrX normrN1 expr1n. Qed.

Lemma normrMsign s x : `|(-1) ^+ s * x| = `|x|.
Proof. by rewrite normrM normr_sign mul1r. Qed.

Lemma signr_gt0 (b : bool) : (0 < (-1) ^+ b :> R) = ~~ b.
Proof. by case: b; rewrite (ltr01, ltr0N1). Qed.

Lemma signr_lt0 (b : bool) : ((-1) ^+ b < 0 :> R) = b.
Proof. by case: b; rewrite // ?(ltrN10, ltr10). Qed.

Lemma signr_ge0 (b : bool) : (0 <= (-1) ^+ b :> R) = ~~ b.
Proof. by rewrite le0r signr_eq0 signr_gt0. Qed.

Lemma signr_le0 (b : bool) : ((-1) ^+ b <= 0 :> R) = b.
Proof. by rewrite le_eqVlt signr_eq0 signr_lt0. Qed.

(* This actually holds for char R != 2. *)
Lemma signr_inj : injective (fun b : bool => (-1) ^+ b : R).
Proof. exact: can_inj (fun x => 0 >= x) signr_le0. Qed.

(* Ternary sign (sg). *)

Lemma sgr_def x : sg x = (-1) ^+ (x < 0)%R *+ (x != 0).
Proof. by rewrite /sg; do 2!case: ifP => //. Qed.

Lemma neqr0_sign x : x != 0 -> (-1) ^+ (x < 0)%R = sgr x.
Proof. by rewrite sgr_def  => ->. Qed.

Lemma gtr0_sg x : 0 < x -> sg x = 1.
Proof. by move=> x_gt0; rewrite /sg gt_eqF // lt_gtF. Qed.

Lemma ltr0_sg x : x < 0 -> sg x = -1.
Proof. by move=> x_lt0; rewrite /sg x_lt0 lt_eqF. Qed.

Lemma sgr0 : sg 0 = 0 :> R. Proof. by rewrite /sgr eqxx. Qed.
Lemma sgr1 : sg 1 = 1 :> R. Proof. by rewrite gtr0_sg // ltr01. Qed.
Lemma sgrN1 : sg (-1) = -1 :> R. Proof. by rewrite ltr0_sg // ltrN10. Qed.
Definition sgrE := (sgr0, sgr1, sgrN1).

Lemma sqr_sg x : sg x ^+ 2 = (x != 0)%:R.
Proof. by rewrite sgr_def exprMn_n sqrr_sign -mulnn mulnb andbb. Qed.

Lemma mulr_sg_eq1 x y : (sg x * y == 1) = (x != 0) && (sg x == y).
Proof.
rewrite /sg eq_sym; case: ifP => _; first by rewrite mul0r oner_eq0.
by case: ifP => _; rewrite ?mul1r // mulN1r eqr_oppLR.
Qed.

Lemma mulr_sg_eqN1 x y : (sg x * sg y == -1) = (x != 0) && (sg x == - sg y).
Proof.
move/sg: y => y; rewrite /sg eq_sym eqr_oppLR.
case: ifP => _; first by rewrite mul0r oppr0 oner_eq0.
by case: ifP => _; rewrite ?mul1r // mulN1r eqr_oppLR.
Qed.

Lemma sgr_eq0 x : (sg x == 0) = (x == 0).
Proof. by rewrite -sqrf_eq0 sqr_sg pnatr_eq0; case: (x == 0). Qed.

Lemma sgr_odd n x : x != 0 -> (sg x) ^+ n = (sg x) ^+ (odd n).
Proof. by rewrite /sg; do 2!case: ifP => // _; rewrite ?expr1n ?signr_odd. Qed.

Lemma sgrMn x n : sg (x *+ n) = (n != 0)%:R * sg x.
Proof.
case: n => [|n]; first by rewrite mulr0n sgr0 mul0r.
by rewrite !sgr_def mulrn_eq0 mul1r pmulrn_llt0.
Qed.

Lemma sgr_nat n : sg n%:R = (n != 0)%:R :> R.
Proof. by rewrite sgrMn sgr1 mulr1. Qed.

Lemma sgr_id x : sg (sg x) = sg x.
Proof. by rewrite !(fun_if sg) !sgrE. Qed.

Lemma sgr_lt0 x : (sg x < 0) = (x < 0).
Proof.
rewrite /sg; case: eqP => [-> // | _].
by case: ifP => _; rewrite ?ltrN10 // lt_gtF.
Qed.

Lemma sgr_le0 x : (sgr x <= 0) = (x <= 0).
Proof. by rewrite !le_eqVlt sgr_eq0 sgr_lt0. Qed.

(* sign and norm *)

Lemma realEsign x : x \is real -> x = (-1) ^+ (x < 0)%R * `|x|.
Proof. by case/real_ge0P; rewrite (mul1r, mulN1r) ?opprK. Qed.

Lemma realNEsign x : x \is real -> - x = (-1) ^+ (0 < x)%R * `|x|.
Proof. by move=> Rx; rewrite -normrN -oppr_lt0 -realEsign ?rpredN. Qed.

Lemma real_normrEsign (x : R) (xR : x \is real) : `|x| = (-1) ^+ (x < 0)%R * x.
Proof. by rewrite {3}[x]realEsign // signrMK. Qed.

#[deprecated(since="mathcomp 2.3.0", note="use `realEsign` instead")]
Lemma real_mulr_sign_norm x : x \is real -> (-1) ^+ (x < 0)%R * `|x| = x.
Proof. by move/realEsign. Qed.

Lemma real_mulr_Nsign_norm x : x \is real -> (-1) ^+ (0 < x)%R * `|x| = - x.
Proof. by move/realNEsign. Qed.

Lemma realEsg x : x \is real -> x = sgr x * `|x|.
Proof.
move=> xR; have [-> | ] := eqVneq x 0; first by rewrite normr0 mulr0.
by move=> /neqr0_sign <-; rewrite -realEsign.
Qed.

Lemma normr_sg x : `|sg x| = (x != 0)%:R.
Proof. by rewrite sgr_def -mulr_natr normrMsign normr_nat. Qed.

Lemma sgr_norm x : sg `|x| = (x != 0)%:R.
Proof. by rewrite /sg le_gtF // normr_eq0 mulrb if_neg. Qed.

(* leif *)

Lemma leif_nat_r m n C : (m%:R <= n%:R ?= iff C :> R) = (m <= n ?= iff C)%N.
Proof. by rewrite /leif !ler_nat eqr_nat. Qed.

Lemma leifBLR x y z C : (x - y <= z ?= iff C) = (x <= z + y ?= iff C).
Proof. by rewrite /leif !eq_le lerBlDr lerBrDr. Qed.

Lemma leifBRL x y z C : (x <= y - z ?= iff C) = (x + z <= y ?= iff C).
Proof. by rewrite -leifBLR opprK. Qed.

Lemma leifD x1 y1 C1 x2 y2 C2 :
    x1 <= y1 ?= iff C1 -> x2 <= y2 ?= iff C2 ->
  x1 + x2 <= y1 + y2 ?= iff C1 && C2.
Proof.
rewrite -(mono_leif (C := C1) (lerD2r x2)).
rewrite -(mono_leif (C := C2) (lerD2l y1)).
exact: leif_trans.
Qed.

Lemma leif_sum (I : finType) (P C : pred I) (E1 E2 : I -> R) :
    (forall i, P i -> E1 i <= E2 i ?= iff C i) ->
  \sum_(i | P i) E1 i <= \sum_(i | P i) E2 i ?= iff [forall (i | P i), C i].
Proof.
move=> leE12; rewrite -big_andE.
elim/big_rec3: _ => [|i Ci m2 m1 /leE12]; first by rewrite /leif lexx eqxx.
exact: leifD.
Qed.

Lemma leif_0_sum (I : finType) (P C : pred I) (E : I -> R) :
    (forall i, P i -> 0 <= E i ?= iff C i) ->
  0 <= \sum_(i | P i) E i ?= iff [forall (i | P i), C i].
Proof. by move/leif_sum; rewrite big1_eq. Qed.

Lemma real_leif_norm x : x \is real -> x <= `|x| ?= iff (0 <= x).
Proof.
by move=> xR; rewrite ger0_def eq_sym; apply: leif_eq; rewrite real_ler_norm.
Qed.

Lemma leif_pM x1 x2 y1 y2 C1 C2 :
    0 <= x1 -> 0 <= x2 -> x1 <= y1 ?= iff C1 -> x2 <= y2 ?= iff C2 ->
  x1 * x2 <= y1 * y2 ?= iff (y1 * y2 == 0) || C1 && C2.
Proof.
move=> x1_ge0 x2_ge0 le_xy1 le_xy2; have [y_0 | ] := eqVneq _ 0.
  apply/leifP; rewrite y_0 /= mulf_eq0 !eq_le x1_ge0 x2_ge0 !andbT.
  move/eqP: y_0; rewrite mulf_eq0.
  by case/pred2P=> <-; rewrite (le_xy1, le_xy2) ?orbT.
rewrite /= mulf_eq0 => /norP[y1nz y2nz].
have y1_gt0: 0 < y1 by rewrite lt_def y1nz (le_trans _ le_xy1).
have [x2_0 | x2nz] := eqVneq x2 0.
  apply/leifP; rewrite -le_xy2 x2_0 eq_sym (negPf y2nz) andbF mulr0.
  by rewrite mulr_gt0 // lt_def y2nz -x2_0 le_xy2.
have:= le_xy2; rewrite -[X in X -> _](mono_leif (ler_pM2l y1_gt0)).
by apply: leif_trans; rewrite (mono_leif (ler_pM2r _)) // lt_def x2nz.
Qed.

Lemma leif_nM x1 x2 y1 y2 C1 C2 :
    y1 <= 0 -> y2 <= 0 -> x1 <= y1 ?= iff C1 -> x2 <= y2 ?= iff C2 ->
  y1 * y2 <= x1 * x2 ?= iff (x1 * x2 == 0) || C1 && C2.
Proof.
rewrite -!oppr_ge0 -mulrNN -[x1 * x2]mulrNN => y1le0 y2le0 le_xy1 le_xy2.
by apply: leif_pM => //; rewrite (nmono_leif lerN2).
Qed.

Lemma leif_pprod (I : finType) (P C : pred I) (E1 E2 : I -> R) :
    (forall i, P i -> 0 <= E1 i) ->
    (forall i, P i -> E1 i <= E2 i ?= iff C i) ->
  let pi E := \prod_(i | P i) E i in
  pi E1 <= pi E2 ?= iff (pi E2 == 0) || [forall (i | P i), C i].
Proof.
move=> E1_ge0 leE12 /=; rewrite -big_andE; elim/(big_load (fun x => 0 <= x)): _.
elim/big_rec3: _ => [|i Ci m2 m1 Pi [m1ge0 le_m12]].
  by split=> //; apply/leifP; rewrite orbT.
have Ei_ge0 := E1_ge0 i Pi; split; first by rewrite mulr_ge0.
congr (leif _ _ _): (leif_pM Ei_ge0 m1ge0 (leE12 i Pi) le_m12).
by rewrite mulf_eq0 -!orbA; congr (_ || _); rewrite !orb_andr orbA orbb.
Qed.

(* lteif *)

Lemma subr_lteifr0 C x y : (y - x < 0 ?<= if C) = (y < x ?<= if C).
Proof. by case: C => /=; rewrite subr_lte0. Qed.

Lemma subr_lteif0r C x y : (0 < y - x ?<= if C) = (x < y ?<= if C).
Proof. by case: C => /=; rewrite subr_gte0. Qed.

Definition subr_lteif0 := (subr_lteifr0, subr_lteif0r).

Lemma lteif01 C : 0 < 1 ?<= if C :> R.
Proof. by case: C; rewrite /= lter01. Qed.

Lemma lteifNl C x y : - x < y ?<= if C = (- y < x ?<= if C).
Proof. by case: C; rewrite /= lterNl. Qed.

Lemma lteifNr C x y : x < - y ?<= if C = (y < - x ?<= if C).
Proof. by case: C; rewrite /= lterNr. Qed.

Lemma lteif0Nr C x : 0 < - x ?<= if C = (x < 0 ?<= if C).
Proof. by case: C; rewrite /= (oppr_ge0, oppr_gt0). Qed.

Lemma lteifNr0 C x : - x < 0 ?<= if C = (0 < x ?<= if C).
Proof. by case: C; rewrite /= (oppr_le0, oppr_lt0). Qed.

Lemma lteifN2 C : {mono -%R : x y /~ x < y ?<= if C :> R}.
Proof. by case: C => ? ?; rewrite /= lterN2. Qed.

Definition lteif_oppE := (lteif0Nr, lteifNr0, lteifN2).

Lemma lteifD2l C x : {mono +%R x : y z / y < z ?<= if C}.
Proof. by case: C => ? ?; rewrite /= lterD2. Qed.

Lemma lteifD2r C x : {mono +%R^~ x : y z / y < z ?<= if C}.
Proof. by case: C => ? ?; rewrite /= lterD2. Qed.

Definition lteifD2 := (lteifD2l, lteifD2r).

Lemma lteifBlDr C x y z : (x - y < z ?<= if C) = (x < z + y ?<= if C).
Proof. by case: C; rewrite /= lterBDr. Qed.

Lemma lteifBrDr C x y z : (x < y - z ?<= if C) = (x + z < y ?<= if C).
Proof. by case: C; rewrite /= lterBDr. Qed.

Definition lteifBDr := (lteifBlDr, lteifBrDr).

Lemma lteifBlDl C x y z : (x - y < z ?<= if C) = (x < y + z ?<= if C).
Proof. by case: C; rewrite /= lterBDl. Qed.

Lemma lteifBrDl C x y z : (x < y - z ?<= if C) = (z + x < y ?<= if C).
Proof. by case: C; rewrite /= lterBDl. Qed.

Definition lteifBDl := (lteifBlDl, lteifBrDl).

Lemma lteif_pM2l C x : 0 < x -> {mono *%R x : y z / y < z ?<= if C}.
Proof. by case: C => ? ? ?; rewrite /= lter_pM2l. Qed.

Lemma lteif_pM2r C x : 0 < x -> {mono *%R^~ x : y z / y < z ?<= if C}.
Proof. by case: C => ? ? ?; rewrite /= lter_pM2r. Qed.

Lemma lteif_nM2l C x : x < 0 -> {mono *%R x : y z /~ y < z ?<= if C}.
Proof. by case: C => ? ? ?; rewrite /= lter_nM2l. Qed.

Lemma lteif_nM2r C x : x < 0 -> {mono *%R^~ x : y z /~ y < z ?<= if C}.
Proof. by case: C => ? ? ?; rewrite /= lter_nM2r. Qed.

Lemma lteif_nnormr C x y : y < 0 ?<= if ~~ C -> (`|x| < y ?<= if C) = false.
Proof. by case: C => ?; rewrite /= lter_nnormr. Qed.

Lemma real_lteifNE x y C : x \is Num.real -> y \is Num.real ->
  x < y ?<= if ~~ C = ~~ (y < x ?<= if C).
Proof. by move=> ? ?; rewrite comparable_lteifNE ?real_comparable. Qed.

Lemma real_lteif_norml C x y :
  x \is Num.real ->
  (`|x| < y ?<= if C) = ((- y < x ?<= if C) && (x < y ?<= if C)).
Proof. by case: C => ?; rewrite /= real_lter_norml. Qed.

Lemma real_lteif_normr C x y :
  y \is Num.real ->
  (x < `|y| ?<= if C) = ((x < y ?<= if C) || (x < - y ?<= if C)).
Proof. by case: C => ?; rewrite /= real_lter_normr. Qed.

Lemma real_lteif_distl C x y e :
  x - y \is real ->
  (`|x - y| < e ?<= if C) = (y - e < x ?<= if C) && (x < y + e ?<= if C).
Proof. by case: C => /= ?; rewrite real_lter_distl. Qed.

(* Mean inequalities. *)

Lemma real_leif_mean_square_scaled x y :
  x \is real -> y \is real -> x * y *+ 2 <= x ^+ 2 + y ^+ 2 ?= iff (x == y).
Proof.
move=> Rx Ry; rewrite -[_ *+ 2]add0r -leifBRL addrAC -sqrrB -subr_eq0.
by rewrite -sqrf_eq0 eq_sym; apply: leif_eq; rewrite -realEsqr rpredB.
Qed.

Lemma real_leif_AGM2_scaled x y :
  x \is real -> y \is real -> x * y *+ 4 <= (x + y) ^+ 2 ?= iff (x == y).
Proof.
move=> Rx Ry; rewrite sqrrD addrAC (mulrnDr _ 2) -leifBLR addrK.
exact: real_leif_mean_square_scaled.
Qed.

Lemma leif_AGM_scaled (I : finType) (A : {pred I}) (E : I -> R) (n := #|A|) :
    {in A, forall i, 0 <= E i *+ n} ->
  \prod_(i in A) (E i *+ n) <= (\sum_(i in A) E i) ^+ n
                            ?= iff [forall i in A, forall j in A, E i == E j].
Proof.
have [m leAm] := ubnP #|A|; elim: m => // m IHm in A leAm E n * => Ege0.
apply/leifP; case: ifPn => [/forall_inP-Econstant | Enonconstant].
  have [i /= Ai | A0] := pickP [in A]; last by rewrite [n]eq_card0 ?big_pred0.
  have /eqfun_inP-E_i := Econstant i Ai; rewrite -(eq_bigr _ E_i) sumr_const.
  by rewrite exprMn_n prodrMn_const -(eq_bigr _ E_i) prodr_const.
set mu := \sum_(i in A) E i; pose En i := E i *+ n.
pose cmp_mu s := [pred i | s * mu < s * En i].
have{Enonconstant} has_cmp_mu e (s := (-1) ^+ e): {i | i \in A & cmp_mu s i}.
  apply/sig2W/exists_inP; apply: contraR Enonconstant => /exists_inPn-mu_s_A.
  have n_gt0 i: i \in A -> (0 < n)%N by rewrite [n](cardD1 i) => ->.
  have{} mu_s_A i: i \in A -> s * En i <= s * mu.
    move=> Ai; rewrite real_leNgt ?mu_s_A ?rpredMsign ?ger0_real ?Ege0 //.
    by rewrite -(pmulrn_lge0 _ (n_gt0 i Ai)) -sumrMnl sumr_ge0.
  have [_ /esym/eqfun_inP] := leif_sum (fun i Ai => leif_eq (mu_s_A i Ai)).
  rewrite sumr_const -/n -mulr_sumr sumrMnl -/mu mulrnAr eqxx => A_mu.
  apply/forall_inP=> i Ai; apply/eqfun_inP=> j Aj.
  by apply: (pmulrnI (n_gt0 i Ai)); apply: (can_inj (signrMK e)); rewrite !A_mu.
have [[i Ai Ei_lt_mu] [j Aj Ej_gt_mu]] := (has_cmp_mu 1, has_cmp_mu 0)%N.
rewrite {cmp_mu has_cmp_mu}/= !mul1r !mulN1r ltrN2 in Ei_lt_mu Ej_gt_mu.
pose A' := [predD1 A & i]; pose n' := #|A'|.
have [Dn n_gt0]: n = n'.+1 /\ (n > 0)%N  by rewrite [n](cardD1 i) Ai.
have i'j: j != i by apply: contraTneq Ej_gt_mu => ->; rewrite lt_gtF.
have{i'j} A'j: j \in A' by rewrite !inE Aj i'j.
have mu_gt0: 0 < mu := le_lt_trans (Ege0 i Ai) Ei_lt_mu.
rewrite (bigD1 i) // big_andbC (bigD1 j) //= mulrA; set pi := \prod_(k | _) _.
have [-> | nz_pi] := eqVneq pi 0; first by rewrite !mulr0 exprn_gt0.
have{nz_pi} pi_gt0: 0 < pi.
  by rewrite lt_def nz_pi prodr_ge0 // => k /andP[/andP[_ /Ege0]].
rewrite -/(En i) -/(En j); pose E' := [eta En with j |-> En i + En j - mu].
have E'ge0 k: k \in A' -> E' k *+ n' >= 0.
  case/andP=> /= _ Ak; apply: mulrn_wge0; case: ifP => _; last exact: Ege0.
  by rewrite subr_ge0 ler_wpDl ?Ege0 // ltW.
rewrite -/n Dn in leAm; have{leAm IHm E'ge0}: _ <= _ := IHm _ leAm _ E'ge0.
have ->: \sum_(k in A') E' k = mu *+ n'.
  apply: (addrI mu); rewrite -mulrS -Dn -sumrMnl (bigD1 i Ai) big_andbC /=.
  rewrite !(bigD1 j A'j) /= addrCA eqxx !addrA subrK; congr (_ + _).
  by apply: eq_bigr => k /andP[_ /negPf->].
rewrite prodrMn_const exprMn_n -/n' ler_pMn2r ?expn_gt0; last by case: (n').
have ->: \prod_(k in A') E' k = E' j * pi.
  by rewrite (bigD1 j) //=; congr *%R; apply: eq_bigr => k /andP[_ /negPf->].
rewrite -(ler_pM2l mu_gt0) -exprS -Dn mulrA; apply: lt_le_trans.
rewrite ltr_pM2r //= eqxx -addrA mulrDr mulrC -ltrBlDl -mulrBl.
by rewrite mulrC ltr_pM2r ?subr_gt0.
Qed.

(* Polynomial bound. *)

Implicit Type p : {poly R}.

Lemma poly_disk_bound p b : {ub | forall x, `|x| <= b -> `|p.[x]| <= ub}.
Proof.
exists (\sum_(j < size p) `|p`_j| * b ^+ j) => x le_x_b.
rewrite horner_coef (le_trans (ler_norm_sum _ _ _)) ?ler_sum // => j _.
rewrite normrM normrX ler_wpM2l ?lerXn2r ?unfold_in //=.
exact: le_trans (normr_ge0 x) le_x_b.
Qed.

End NumDomainOperationTheory.

#[global] Hint Resolve lerN2 ltrN2 normr_real : core.
#[global] Hint Extern 0 (is_true (_%:R \is real)) => apply: realn : core.
#[global] Hint Extern 0 (is_true (0 \is real)) => apply: real0 : core.
#[global] Hint Extern 0 (is_true (1 \is real)) => apply: real1 : core.

Arguments ler_sqr {R} [x y].
Arguments ltr_sqr {R} [x y].
Arguments signr_inj {R} [x1 x2].
Arguments real_ler_normlP {R x y}.
Arguments real_ltr_normlP {R x y}.

Section NumDomainMonotonyTheoryForReals.
Local Open Scope order_scope.

Variables (R R' : numDomainType) (D : pred R) (f : R -> R') (f' : R -> nat).
Implicit Types (m n p : nat) (x y z : R) (u v w : R').

Lemma real_mono :
  {homo f : x y / x < y} -> {in real &, {mono f : x y / x <= y}}.
Proof.
move=> mf x y xR yR /=; have [lt_xy | le_yx] := real_leP xR yR.
  by rewrite ltW_homo.
by rewrite lt_geF ?mf.
Qed.

Lemma real_nmono :
  {homo f : x y /~ x < y} -> {in real &, {mono f : x y /~ x <= y}}.
Proof.
move=> mf x y xR yR /=; have [lt_xy|le_yx] := real_ltP xR yR.
  by rewrite lt_geF ?mf.
by rewrite ltW_nhomo.
Qed.

Lemma real_mono_in :
    {in D &, {homo f : x y / x < y}} ->
  {in [pred x in D | x \is real] &, {mono f : x y / x <= y}}.
Proof.
move=> Dmf x y /andP[hx xR] /andP[hy yR] /=.
have [lt_xy|le_yx] := real_leP xR yR; first by rewrite (ltW_homo_in Dmf).
by rewrite lt_geF ?Dmf.
Qed.

Lemma real_nmono_in :
    {in D &, {homo f : x y /~ x < y}} ->
  {in [pred x in D | x \is real] &, {mono f : x y /~ x <= y}}.
Proof.
move=> Dmf x y /andP[hx xR] /andP[hy yR] /=.
have [lt_xy|le_yx] := real_ltP xR yR; last by rewrite (ltW_nhomo_in Dmf).
by rewrite lt_geF ?Dmf.
Qed.

Lemma realn_mono : {homo f' : x y / x < y >-> (x < y)} ->
  {in real &, {mono f' : x y / x <= y >-> (x <= y)}}.
Proof.
move=> mf x y xR yR /=; have [lt_xy | le_yx] := real_leP xR yR.
  by rewrite ltW_homo.
by rewrite lt_geF ?mf.
Qed.

Lemma realn_nmono : {homo f' : x y / y < x >-> (x < y)} ->
  {in real &, {mono f' : x y / y <= x >-> (x <= y)}}.
Proof.
move=> mf x y xR yR /=; have [lt_xy|le_yx] := real_ltP xR yR.
  by rewrite lt_geF ?mf.
by rewrite ltW_nhomo.
Qed.

Lemma realn_mono_in : {in D &, {homo f' : x y / x < y >-> (x < y)}} ->
  {in [pred x in D | x \is real] &, {mono f' : x y / x <= y >-> (x <= y)}}.
Proof.
move=> Dmf x y /andP[hx xR] /andP[hy yR] /=.
have [lt_xy|le_yx] := real_leP xR yR; first by rewrite (ltW_homo_in Dmf).
by rewrite lt_geF ?Dmf.
Qed.

Lemma realn_nmono_in : {in D &, {homo f' : x y / y < x >-> (x < y)}} ->
  {in [pred x in D | x \is real] &, {mono f' : x y / y <= x >-> (x <= y)}}.
Proof.
move=> Dmf x y /andP[hx xR] /andP[hy yR] /=.
have [lt_xy|le_yx] := real_ltP xR yR; last by rewrite (ltW_nhomo_in Dmf).
by rewrite lt_geF ?Dmf.
Qed.

End NumDomainMonotonyTheoryForReals.

Section FinGroup.

Variables (R : numDomainType) (gT : finGroupType).
Implicit Types G : {group gT}.

Lemma natrG_gt0 G : #|G|%:R > 0 :> R.
Proof. by rewrite ltr0n cardG_gt0. Qed.

Lemma natrG_neq0 G : #|G|%:R != 0 :> R.
Proof. by rewrite gt_eqF // natrG_gt0. Qed.

Lemma natr_indexg_gt0 G B : #|G : B|%:R > 0 :> R.
Proof. by rewrite ltr0n indexg_gt0. Qed.

Lemma natr_indexg_neq0 G B : #|G : B|%:R != 0 :> R.
Proof. by rewrite gt_eqF // natr_indexg_gt0. Qed.

End FinGroup.

Section NumFieldTheory.

Variable F : numFieldType.
Implicit Types x y z t : F.

Lemma unitf_gt0 x : 0 < x -> x \is a GRing.unit.
Proof. by move=> hx; rewrite unitfE eq_sym lt_eqF. Qed.

Lemma unitf_lt0 x : x < 0 -> x \is a GRing.unit.
Proof. by move=> hx; rewrite unitfE lt_eqF. Qed.

Lemma lef_pV2 : {in pos &, {mono (@GRing.inv F) : x y /~ x <= y}}.
Proof. by move=> x y hx hy /=; rewrite ler_pV2 ?inE ?unitf_gt0. Qed.

Lemma lef_nV2 : {in neg &, {mono (@GRing.inv F) : x y /~ x <= y}}.
Proof. by move=> x y hx hy /=; rewrite ler_nV2 ?inE ?unitf_lt0. Qed.

Lemma ltf_pV2 : {in pos &, {mono (@GRing.inv F) : x y /~ x < y}}.
Proof. exact: leW_nmono_in lef_pV2. Qed.

Lemma ltf_nV2 : {in neg &, {mono (@GRing.inv F) : x y /~ x < y}}.
Proof. exact: leW_nmono_in lef_nV2. Qed.

Definition ltef_pV2 := (lef_pV2, ltf_pV2).
Definition ltef_nV2 := (lef_nV2, ltf_nV2).

Lemma invf_pgt : {in pos &, forall x y, (x < y^-1) = (y < x^-1)}.
Proof. by move=> x y *; rewrite -[x in LHS]invrK ltf_pV2// posrE invr_gt0. Qed.

Lemma invf_pge : {in pos &, forall x y, (x <= y^-1) = (y <= x^-1)}.
Proof. by move=> x y *; rewrite -[x in LHS]invrK lef_pV2// posrE invr_gt0. Qed.

Lemma invf_ngt : {in neg &, forall x y, (x < y^-1) = (y < x^-1)}.
Proof. by move=> x y *; rewrite -[x in LHS]invrK ltf_nV2// negrE invr_lt0. Qed.

Lemma invf_nge : {in neg &, forall x y, (x <= y^-1) = (y <= x^-1)}.
Proof. by move=> x y *; rewrite -[x in LHS]invrK lef_nV2// negrE invr_lt0. Qed.

Lemma invf_gt1 x : 0 < x -> (1 < x^-1) = (x < 1).
Proof. by move=> x0; rewrite invf_pgt ?invr1 ?posrE. Qed.

Lemma invf_ge1 x : 0 < x -> (1 <= x^-1) = (x <= 1).
Proof. by move=> x0; rewrite invf_pge ?invr1 ?posrE. Qed.

Definition invf_gte1 := (invf_ge1, invf_gt1).

Lemma invf_plt : {in pos &, forall x y, (x^-1 < y) = (y^-1 < x)}.
Proof. by move=> x y *; rewrite -[y in LHS]invrK ltf_pV2// posrE invr_gt0. Qed.

Lemma invf_ple : {in pos &, forall x y, (x^-1 <= y) = (y^-1 <= x)}.
Proof. by move=> x y *; rewrite -[y in LHS]invrK lef_pV2// posrE invr_gt0. Qed.

Lemma invf_nlt : {in neg &, forall x y, (x^-1 < y) = (y^-1 < x)}.
Proof. by move=> x y *; rewrite -[y in LHS]invrK ltf_nV2// negrE invr_lt0. Qed.

Lemma invf_nle : {in neg &, forall x y, (x^-1 <= y) = (y^-1 <= x)}.
Proof. by move=> x y *; rewrite -[y in LHS]invrK lef_nV2// negrE invr_lt0. Qed.

Lemma invf_le1 x : 0 < x -> (x^-1 <= 1) = (1 <= x).
Proof. by move=> x0; rewrite -invf_ple ?invr1 ?posrE. Qed.

Lemma invf_lt1 x : 0 < x -> (x^-1 < 1) = (1 < x).
Proof. by move=> x0; rewrite invf_plt ?invr1 ?posrE. Qed.

Definition invf_lte1 := (invf_le1, invf_lt1).
Definition invf_cp1 := (invf_gte1, invf_lte1).

(* These lemma are all combinations of mono(LR|RL) with ler_[pn]mul2[rl]. *)
Lemma ler_pdivlMr z x y : 0 < z -> (x <= y / z) = (x * z <= y).
Proof. by move=> z_gt0; rewrite -(@ler_pM2r _ z _ x) ?mulfVK ?gt_eqF. Qed.

Lemma ltr_pdivlMr z x y : 0 < z -> (x < y / z) = (x * z < y).
Proof. by move=> z_gt0; rewrite -(@ltr_pM2r _ z _ x) ?mulfVK ?gt_eqF. Qed.

Definition lter_pdivlMr := (ler_pdivlMr, ltr_pdivlMr).

Lemma ler_pdivrMr z x y : 0 < z -> (y / z <= x) = (y <= x * z).
Proof. by move=> z_gt0; rewrite -(@ler_pM2r _ z) ?mulfVK ?gt_eqF. Qed.

Lemma ltr_pdivrMr z x y : 0 < z -> (y / z < x) = (y < x * z).
Proof. by move=> z_gt0; rewrite -(@ltr_pM2r _ z) ?mulfVK ?gt_eqF. Qed.

Definition lter_pdivrMr := (ler_pdivrMr, ltr_pdivrMr).

Lemma ler_pdivlMl z x y : 0 < z -> (x <= z^-1 * y) = (z * x <= y).
Proof. by move=> z_gt0; rewrite mulrC ler_pdivlMr ?[z * _]mulrC. Qed.

Lemma ltr_pdivlMl z x y : 0 < z -> (x < z^-1 * y) = (z * x < y).
Proof. by move=> z_gt0; rewrite mulrC ltr_pdivlMr ?[z * _]mulrC. Qed.

Definition lter_pdivlMl := (ler_pdivlMl, ltr_pdivlMl).

Lemma ler_pdivrMl z x y : 0 < z -> (z^-1 * y <= x) = (y <= z * x).
Proof. by move=> z_gt0; rewrite mulrC ler_pdivrMr ?[z * _]mulrC. Qed.

Lemma ltr_pdivrMl z x y : 0 < z -> (z^-1 * y < x) = (y < z * x).
Proof. by move=> z_gt0; rewrite mulrC ltr_pdivrMr ?[z * _]mulrC. Qed.

Definition lter_pdivrMl := (ler_pdivrMl, ltr_pdivrMl).

Lemma ler_ndivlMr z x y : z < 0 -> (x <= y / z) = (y <= x * z).
Proof. by move=> z_lt0; rewrite -(@ler_nM2r _ z) ?mulfVK  ?lt_eqF. Qed.

Lemma ltr_ndivlMr z x y : z < 0 -> (x < y / z) = (y < x * z).
Proof. by move=> z_lt0; rewrite -(@ltr_nM2r _ z) ?mulfVK ?lt_eqF. Qed.

Definition lter_ndivlMr := (ler_ndivlMr, ltr_ndivlMr).

Lemma ler_ndivrMr z x y : z < 0 -> (y / z <= x) = (x * z <= y).
Proof. by move=> z_lt0; rewrite -(@ler_nM2r _ z) ?mulfVK ?lt_eqF. Qed.

Lemma ltr_ndivrMr z x y : z < 0 -> (y / z < x) = (x * z < y).
Proof. by move=> z_lt0; rewrite -(@ltr_nM2r _ z) ?mulfVK ?lt_eqF. Qed.

Definition lter_ndivrMr := (ler_ndivrMr, ltr_ndivrMr).

Lemma ler_ndivlMl z x y : z < 0 -> (x <= z^-1 * y) = (y <= z * x).
Proof. by move=> z_lt0; rewrite mulrC ler_ndivlMr ?[z * _]mulrC. Qed.

Lemma ltr_ndivlMl z x y : z < 0 -> (x < z^-1 * y) = (y < z * x).
Proof. by move=> z_lt0; rewrite mulrC ltr_ndivlMr ?[z * _]mulrC. Qed.

Definition lter_ndivlMl := (ler_ndivlMl, ltr_ndivlMl).

Lemma ler_ndivrMl z x y : z < 0 -> (z^-1 * y <= x) = (z * x <= y).
Proof. by move=> z_lt0; rewrite mulrC ler_ndivrMr ?[z * _]mulrC. Qed.

Lemma ltr_ndivrMl z x y : z < 0 -> (z^-1 * y < x) = (z * x < y).
Proof. by move=> z_lt0; rewrite mulrC ltr_ndivrMr ?[z * _]mulrC. Qed.

Definition lter_ndivrMl := (ler_ndivrMl, ltr_ndivrMl).

Lemma natf_div m d : (d %| m)%N -> (m %/ d)%:R = m%:R / d%:R :> F.
Proof. by apply: char0_natf_div; apply: (@char_num F). Qed.

Lemma normfV : {morph (norm : F -> F) : x / x ^-1}.
Proof.
move=> x /=; have [/normrV //|Nux] := boolP (x \is a GRing.unit).
by rewrite !invr_out // unitfE normr_eq0 -unitfE.
Qed.

Lemma normf_div : {morph (norm : F -> F) : x y / x / y}.
Proof. by move=> x y /=; rewrite normrM normfV. Qed.

Lemma invr_sg x : (sg x)^-1 = sgr x.
Proof. by rewrite !(fun_if GRing.inv) !(invr0, invrN, invr1). Qed.

Lemma sgrV x : sgr x^-1 = sgr x.
Proof. by rewrite /sgr invr_eq0 invr_lt0. Qed.

Lemma splitr x : x = x / 2%:R + x / 2%:R.
Proof. by rewrite -mulr2n -[RHS]mulr_natr mulfVK //= pnatr_eq0. Qed.

(* lteif *)

Lemma lteif_pdivlMr C z x y :
  0 < z -> x < y / z ?<= if C = (x * z < y ?<= if C).
Proof. by case: C => ? /=; rewrite lter_pdivlMr. Qed.

Lemma lteif_pdivrMr C z x y :
  0 < z -> y / z < x ?<= if C = (y < x * z ?<= if C).
Proof. by case: C => ? /=; rewrite lter_pdivrMr. Qed.

Lemma lteif_pdivlMl C z x y :
  0 < z -> x < z^-1 * y ?<= if C = (z * x < y ?<= if C).
Proof. by case: C => ? /=; rewrite lter_pdivlMl. Qed.

Lemma lteif_pdivrMl C z x y :
  0 < z -> z^-1 * y < x ?<= if C = (y < z * x ?<= if C).
Proof. by case: C => ? /=; rewrite lter_pdivrMl. Qed.

Lemma lteif_ndivlMr C z x y :
  z < 0 -> x < y / z ?<= if C = (y < x * z ?<= if C).
Proof. by case: C => ? /=; rewrite lter_ndivlMr. Qed.

Lemma lteif_ndivrMr C z x y :
  z < 0 -> y / z < x ?<= if C = (x * z < y ?<= if C).
Proof. by case: C => ? /=; rewrite lter_ndivrMr. Qed.

Lemma lteif_ndivlMl C z x y :
  z < 0 -> x < z^-1 * y ?<= if C = (y < z * x ?<= if C).
Proof. by case: C => ? /=; rewrite lter_ndivlMl. Qed.

Lemma lteif_ndivrMl C z x y :
  z < 0 -> z^-1 * y < x ?<= if C = (z * x < y ?<= if C).
Proof. by case: C => ? /=; rewrite lter_ndivrMl. Qed.

(* Interval midpoint. *)

Local Notation mid x y := ((x + y) / 2).

Lemma midf_le x y : x <= y -> (x <= mid x y) * (mid x y <= y).
Proof.
move=> lexy; rewrite ler_pdivlMr ?ler_pdivrMr ?ltr0Sn //.
by rewrite !mulrDr !mulr1 !lerD2.
Qed.

Lemma midf_lt x y : x < y -> (x < mid x y) * (mid x y < y).
Proof.
move=> ltxy; rewrite ltr_pdivlMr ?ltr_pdivrMr ?ltr0Sn //.
by rewrite !mulrDr !mulr1 !ltrD2.
Qed.

Definition midf_lte := (midf_le, midf_lt).

Lemma ler_addgt0Pr x y : reflect (forall e, e > 0 -> x <= y + e) (x <= y).
Proof.
apply/(iffP idP)=> [lexy e e_gt0 | lexye]; first by rewrite ler_wpDr// ltW.
have [||ltyx]// := comparable_leP.
  rewrite (@comparabler_trans _ (y + 1))// /Order.comparable ?lexye ?ltr01//.
  by rewrite lerDl ler01 orbT.
have /midf_lt [_] := ltyx; rewrite le_gtF//.
rewrite -(@addrK _ y y) (addrAC _ _ x) -addrA 2!mulrDl -splitr lexye//.
by rewrite divr_gt0// ?ltr0n// subr_gt0.
Qed.

Lemma ler_addgt0Pl x y : reflect (forall e, e > 0 -> x <= e + y) (x <= y).
Proof.
by apply/(equivP (ler_addgt0Pr x y)); split=> lexy e /lexy; rewrite addrC.
Qed.

Lemma lt_le a b : (forall x, x < a -> x < b) -> a <= b.
Proof.
move=> ab; apply/ler_addgt0Pr => e e_gt0; rewrite -lerBDr ltW//.
by rewrite ab// ltrBlDr ltrDl.
Qed.

Lemma gt_ge a b : (forall x, b < x -> a < x) -> a <= b.
Proof.
by move=> ab; apply/ler_addgt0Pr => e e_gt0; rewrite ltW// ab// ltrDl.
Qed.

(* The AGM, unscaled but without the nth root. *)

Lemma real_leif_mean_square x y :
  x \is real -> y \is real -> x * y <= mid (x ^+ 2) (y ^+ 2) ?= iff (x == y).
Proof.
move=> Rx Ry; rewrite -(mono_leif (ler_pM2r (ltr_nat F 0 2))).
by rewrite divfK ?pnatr_eq0 // mulr_natr; apply: real_leif_mean_square_scaled.
Qed.

Lemma real_leif_AGM2 x y :
  x \is real -> y \is real -> x * y <= mid x y ^+ 2 ?= iff (x == y).
Proof.
move=> Rx Ry; rewrite -(mono_leif (ler_pM2r (ltr_nat F 0 4))).
rewrite mulr_natr (natrX F 2 2) -exprMn divfK ?pnatr_eq0 //.
exact: real_leif_AGM2_scaled.
Qed.

Lemma leif_AGM (I : finType) (A : {pred I}) (E : I -> F) :
    let n := #|A| in let mu := (\sum_(i in A) E i) / n%:R in
    {in A, forall i, 0 <= E i} ->
  \prod_(i in A) E i <= mu ^+ n
                     ?= iff [forall i in A, forall j in A, E i == E j].
Proof.
move=> n mu Ege0; have [n0 | n_gt0] := posnP n.
  by rewrite n0 -big_andE !(big_pred0 _ _ _ _ (card0_eq n0)); apply/leifP.
pose E' i := E i / n%:R.
have defE' i: E' i *+ n = E i by rewrite -mulr_natr divfK ?pnatr_eq0 -?lt0n.
have /leif_AGM_scaled (i): i \in A -> 0 <= E' i *+ n by rewrite defE' => /Ege0.
rewrite -/n -mulr_suml (eq_bigr _ (in1W defE')); congr (_ <= _ ?= iff _).
by do 2![apply: eq_forallb_in => ? _]; rewrite -(eqr_pMn2r n_gt0) !defE'.
Qed.

Implicit Type p : {poly F}.
Lemma Cauchy_root_bound p : p != 0 -> {b | forall x, root p x -> `|x| <= b}.
Proof.
move=> nz_p; set a := lead_coef p; set n := (size p).-1.
have [q Dp]: {q | forall x, x != 0 -> p.[x] = (a - q.[x^-1] / x) * x ^+ n}.
  exists (- \poly_(i < n) p`_(n - i.+1)) => x nz_x.
  rewrite hornerN mulNr opprK horner_poly mulrDl !mulr_suml addrC.
  rewrite horner_coef polySpred // big_ord_recr (reindex_inj rev_ord_inj) /=.
  rewrite -/n -lead_coefE; congr (_ + _); apply: eq_bigr=> i _.
  by rewrite exprB ?unitfE // -exprVn mulrA mulrAC exprSr mulrA.
have [b ub_q] := poly_disk_bound q 1; exists (b / `|a| + 1) => x px0.
have b_ge0: 0 <= b by rewrite (le_trans (normr_ge0 q.[1])) ?ub_q ?normr1.
have{b_ge0} ba_ge0: 0 <= b / `|a| by rewrite divr_ge0.
rewrite real_leNgt ?rpredD ?rpred1 ?ger0_real //.
apply: contraL px0 => lb_x; rewrite rootE.
have x_ge1: 1 <= `|x| by rewrite (le_trans _ (ltW lb_x)) // ler_wpDl.
have nz_x: x != 0 by rewrite -normr_gt0 (lt_le_trans ltr01).
rewrite {}Dp // mulf_neq0 ?expf_neq0 // subr_eq0 eq_sym.
have: (b / `|a|) < `|x| by rewrite (lt_trans _ lb_x) // ltr_pwDr ?ltr01.
apply: contraTneq => /(canRL (divfK nz_x))Dax.
rewrite ltr_pdivrMr ?normr_gt0 ?lead_coef_eq0 // mulrC -normrM -{}Dax.
by rewrite le_gtF // ub_q // normfV invf_le1 ?normr_gt0.
Qed.

Import GroupScope.

Lemma natf_indexg (gT : finGroupType) (G H : {group gT}) :
  H \subset G -> #|G : H|%:R = (#|G|%:R / #|H|%:R)%R :> F.
Proof. by move=> sHG; rewrite -divgS // natf_div ?cardSg. Qed.

End NumFieldTheory.

Section RealDomainTheory.

Variable R : realDomainType.
Implicit Types x y z t : R.

Lemma num_real x : x \is real. Proof. exact: num_real. Qed.
Hint Resolve num_real : core.

Lemma lerP x y : ler_xor_gt x y (min y x) (min x y) (max y x) (max x y)
                                `|x - y| `|y - x| (x <= y) (y < x).
Proof. exact: real_leP. Qed.

Lemma ltrP x y : ltr_xor_ge x y (min y x) (min x y) (max y x) (max x y)
                                `|x - y| `|y - x| (y <= x) (x < y).
Proof. exact: real_ltP. Qed.

Lemma ltrgtP x y :
   comparer x y  (min y x) (min x y) (max y x) (max x y)
                 `|x - y| `|y - x| (y == x) (x == y)
                 (x >= y) (x <= y) (x > y) (x < y) .
Proof. exact: real_ltgtP. Qed.

Lemma ger0P x : ger0_xor_lt0 x (min 0 x) (min x 0) (max 0 x) (max x 0)
                                `|x| (x < 0) (0 <= x).
Proof. exact: real_ge0P. Qed.

Lemma ler0P x : ler0_xor_gt0 x (min 0 x) (min x 0) (max 0 x) (max x 0)
                                `|x| (0 < x) (x <= 0).
Proof. exact: real_le0P. Qed.

Lemma ltrgt0P x : comparer0 x (min 0 x) (min x 0) (max 0 x) (max x 0)
  `|x| (0 == x) (x == 0) (x <= 0) (0 <= x) (x < 0) (x > 0).
Proof. exact: real_ltgt0P. Qed.

(* sign *)

Lemma mulr_lt0 x y :
  (x * y < 0) = [&& x != 0, y != 0 & (x < 0) (+) (y < 0)].
Proof.
have [x_gt0|x_lt0|->] /= := ltrgt0P x; last by rewrite mul0r.
  by rewrite pmulr_rlt0 //; case: ltrgt0P.
by rewrite nmulr_rlt0 //; case: ltrgt0P.
Qed.

Lemma neq0_mulr_lt0 x y :
  x != 0 -> y != 0 -> (x * y < 0) = (x < 0) (+) (y < 0).
Proof. by move=> x_neq0 y_neq0; rewrite mulr_lt0 x_neq0 y_neq0. Qed.

Lemma mulr_sign_lt0 (b : bool) x :
  ((-1) ^+ b * x < 0) = (x != 0) && (b (+) (x < 0)%R).
Proof. by rewrite mulr_lt0 signr_lt0 signr_eq0. Qed.

(* sign & norm *)

Lemma mulr_sign_norm x : (-1) ^+ (x < 0)%R * `|x| = x.
Proof. by rewrite -realEsign. Qed.

Lemma mulr_Nsign_norm x : (-1) ^+ (0 < x)%R * `|x| = - x.
Proof. by rewrite real_mulr_Nsign_norm. Qed.

Lemma numEsign x : x = (-1) ^+ (x < 0)%R * `|x|.
Proof. by rewrite -realEsign. Qed.

Lemma numNEsign x : -x = (-1) ^+ (0 < x)%R * `|x|.
Proof. by rewrite -realNEsign. Qed.

Lemma normrEsign x : `|x| = (-1) ^+ (x < 0)%R * x.
Proof. by rewrite -real_normrEsign. Qed.

End RealDomainTheory.

#[global] Hint Resolve num_real : core.

Section RealDomainOperations.

Notation "[ 'arg' 'min_' ( i < i0 | P ) F ]" :=
    (Order.arg_min (disp := ring_display) i0 (fun i => P%B) (fun i => F)) :
   ring_scope.

Notation "[ 'arg' 'min_' ( i < i0 'in' A ) F ]" :=
  [arg min_(i < i0 | i \in A) F] : ring_scope.

Notation "[ 'arg' 'min_' ( i < i0 ) F ]" := [arg min_(i < i0 | true) F] :
  ring_scope.

Notation "[ 'arg' 'max_' ( i > i0 | P ) F ]" :=
   (Order.arg_max (disp := ring_display) i0 (fun i => P%B) (fun i => F)) :
  ring_scope.

Notation "[ 'arg' 'max_' ( i > i0 'in' A ) F ]" :=
    [arg max_(i > i0 | i \in A) F] : ring_scope.

Notation "[ 'arg' 'max_' ( i > i0 ) F ]" := [arg max_(i > i0 | true) F] :
  ring_scope.

(* sgr section *)

Variable R : realDomainType.
Implicit Types x y z t : R.
Let numR_real := @num_real R.
Hint Resolve numR_real : core.

Lemma sgr_cp0 x :
  ((sg x == 1) = (0 < x)) *
  ((sg x == -1) = (x < 0)) *
  ((sg x == 0) = (x == 0)).
Proof.
rewrite -[1]/((-1) ^+ false) -signrN lt0r leNgt sgr_def.
case: (x =P 0) => [-> | _]; first by rewrite !(eq_sym 0) !signr_eq0 ltxx eqxx.
by rewrite !(inj_eq signr_inj) eqb_id eqbF_neg signr_eq0 //.
Qed.

Variant sgr_val x : R -> bool -> bool -> bool -> bool -> bool -> bool
  -> bool -> bool -> bool -> bool -> bool -> bool -> R -> Set :=
  | SgrNull of x = 0 : sgr_val x 0 true true true true false false
    true false false true false false 0
  | SgrPos of x > 0 : sgr_val x x false false true false false true
    false false true false false true 1
  | SgrNeg of x < 0 : sgr_val x (- x) false true false false true false
    false true false false true false (-1).

Lemma sgrP x :
  sgr_val x `|x| (0 == x) (x <= 0) (0 <= x) (x == 0) (x < 0) (0 < x)
                 (0 == sg x) (-1 == sg x) (1 == sg x)
                 (sg x == 0)  (sg x == -1) (sg x == 1) (sg x).
Proof.
by rewrite ![_ == sg _]eq_sym !sgr_cp0 /sg; case: ltrgt0P; constructor.
Qed.

Lemma normrEsg x : `|x| = sg x * x.
Proof. by case: sgrP; rewrite ?(mul0r, mul1r, mulN1r). Qed.

Lemma numEsg x : x = sg x * `|x|.
Proof. by case: sgrP; rewrite !(mul1r, mul0r, mulrNN). Qed.

#[deprecated(since="mathcomp 2.3.0", note="use `numEsg` instead")]
Lemma mulr_sg_norm x : sg x * `|x| = x. Proof. by rewrite -numEsg. Qed.

Lemma sgrM x y : sg (x * y) = sg x * sg y.
Proof.
rewrite !sgr_def mulr_lt0 andbA mulrnAr mulrnAl -mulrnA mulnb -negb_or mulf_eq0.
by case: (~~ _) => //; rewrite signr_addb.
Qed.

Lemma sgrN x : sg (- x) = - sg x.
Proof. by rewrite -mulrN1 sgrM sgrN1 mulrN1. Qed.

Lemma sgrX n x : sg (x ^+ n) = (sg x) ^+ n.
Proof. by elim: n => [|n IHn]; rewrite ?sgr1 // !exprS sgrM IHn. Qed.

Lemma sgr_smul x y : sg (sg x * y) = sg x * sg y.
Proof. by rewrite sgrM sgr_id. Qed.

Lemma sgr_gt0 x : (sg x > 0) = (x > 0).
Proof. by rewrite -[LHS]sgr_cp0 sgr_id sgr_cp0. Qed.

Lemma sgr_ge0 x : (sgr x >= 0) = (x >= 0).
Proof. by rewrite !leNgt sgr_lt0. Qed.

(* norm section *)

Lemma ler_norm x : (x <= `|x|).
Proof. exact: real_ler_norm. Qed.

Lemma ler_norml x y : (`|x| <= y) = (- y <= x <= y).
Proof. exact: real_ler_norml. Qed.

Lemma ler_normlP x y : reflect ((- x <= y) * (x <= y)) (`|x| <= y).
Proof. exact: real_ler_normlP. Qed.
Arguments ler_normlP {x y}.

Lemma eqr_norml x y : (`|x| == y) = ((x == y) || (x == -y)) && (0 <= y).
Proof. exact: real_eqr_norml. Qed.

Lemma eqr_norm2 x y : (`|x| == `|y|) = (x == y) || (x == -y).
Proof. exact: real_eqr_norm2. Qed.

Lemma ltr_norml x y : (`|x| < y) = (- y < x < y).
Proof. exact: real_ltr_norml. Qed.

Definition lter_norml := (ler_norml, ltr_norml).

Lemma ltr_normlP x y : reflect ((-x < y) * (x < y)) (`|x| < y).
Proof. exact: real_ltr_normlP. Qed.
Arguments ltr_normlP {x y}.

Lemma ltr_normlW x y : `|x| < y -> x < y. Proof. exact: real_ltr_normlW. Qed.

Lemma ltrNnormlW x y : `|x| < y -> - y < x. Proof. exact: real_ltrNnormlW. Qed.

Lemma ler_normlW x y : `|x| <= y -> x <= y. Proof. exact: real_ler_normlW. Qed.

Lemma lerNnormlW x y : `|x| <= y -> - y <= x. Proof. exact: real_lerNnormlW. Qed.

Lemma ler_normr x y : (x <= `|y|) = (x <= y) || (x <= - y).
Proof. exact: real_ler_normr. Qed.

Lemma ltr_normr x y : (x < `|y|) = (x < y) || (x < - y).
Proof. exact: real_ltr_normr. Qed.

Definition lter_normr := (ler_normr, ltr_normr).

Lemma ler_distl x y e : (`|x - y| <= e) = (y - e <= x <= y + e).
Proof. exact: real_ler_distl. Qed.

Lemma ltr_distl x y e : (`|x - y| < e) = (y - e < x < y + e).
Proof. exact: real_ltr_distl. Qed.

Definition lter_distl := (ler_distl, ltr_distl).

Lemma ltr_distlC x y e : (`|x - y| < e) = (x - e < y < x + e).
Proof. by rewrite distrC ltr_distl. Qed.

Lemma ler_distlC x y e : (`|x - y| <= e) = (x - e <= y <= x + e).
Proof. by rewrite distrC ler_distl. Qed.

Definition lter_distlC := (ler_distlC, ltr_distlC).

Lemma ltr_distlDr x y e : `|x - y| < e -> x < y + e.
Proof. exact: real_ltr_distlDr. Qed.

Lemma ler_distlDr x y e : `|x - y| <= e -> x <= y + e.
Proof. exact: real_ler_distlDr. Qed.

Lemma ltr_distlCDr x y e : `|x - y| < e -> y < x + e.
Proof. exact: real_ltr_distlCDr. Qed.

Lemma ler_distlCDr x y e : `|x - y| <= e -> y <= x + e.
Proof. exact: real_ler_distlCDr. Qed.

Lemma ltr_distlBl x y e : `|x - y| < e -> x - e < y.
Proof. exact: real_ltr_distlBl. Qed.

Lemma ler_distlBl x y e : `|x - y| <= e -> x - e <= y.
Proof. exact: real_ler_distlBl. Qed.

Lemma ltr_distlCBl x y e : `|x - y| < e -> y - e < x.
Proof. exact: real_ltr_distlCBl. Qed.

Lemma ler_distlCBl x y e : `|x - y| <= e -> y - e <= x.
Proof. exact: real_ler_distlCBl. Qed.

Lemma exprn_even_ge0 n x : ~~ odd n -> 0 <= x ^+ n.
Proof. by move=> even_n; rewrite real_exprn_even_ge0 ?num_real. Qed.

Lemma exprn_even_gt0 n x : ~~ odd n -> (0 < x ^+ n) = (n == 0)%N || (x != 0).
Proof. by move=> even_n; rewrite real_exprn_even_gt0 ?num_real. Qed.

Lemma exprn_even_le0 n x : ~~ odd n -> (x ^+ n <= 0) = (n != 0) && (x == 0).
Proof. by move=> even_n; rewrite real_exprn_even_le0 ?num_real. Qed.

Lemma exprn_even_lt0 n x : ~~ odd n -> (x ^+ n < 0) = false.
Proof. by move=> even_n; rewrite real_exprn_even_lt0 ?num_real. Qed.

Lemma exprn_odd_ge0 n x : odd n -> (0 <= x ^+ n) = (0 <= x).
Proof. by move=> even_n; rewrite real_exprn_odd_ge0 ?num_real. Qed.

Lemma exprn_odd_gt0 n x : odd n -> (0 < x ^+ n) = (0 < x).
Proof. by move=> even_n; rewrite real_exprn_odd_gt0 ?num_real. Qed.

Lemma exprn_odd_le0 n x : odd n -> (x ^+ n <= 0) = (x <= 0).
Proof. by move=> even_n; rewrite real_exprn_odd_le0 ?num_real. Qed.

Lemma exprn_odd_lt0 n x : odd n -> (x ^+ n < 0) = (x < 0).
Proof. by move=> even_n; rewrite real_exprn_odd_lt0 ?num_real. Qed.

(* lteif *)

Lemma lteif_norml C x y :
  (`|x| < y ?<= if C) = (- y < x ?<= if C) && (x < y ?<= if C).
Proof. by case: C; rewrite /= lter_norml. Qed.

Lemma lteif_normr C x y :
  (x < `|y| ?<= if C) = (x < y ?<= if C) || (x < - y ?<= if C).
Proof. by case: C; rewrite /= lter_normr. Qed.

Lemma lteif_distl C x y e :
  (`|x - y| < e ?<= if C) = (y - e < x ?<= if C) && (x < y + e ?<= if C).
Proof. by case: C; rewrite /= lter_distl. Qed.

(* Special lemmas for squares. *)

Lemma sqr_ge0 x : 0 <= x ^+ 2. Proof. by rewrite exprn_even_ge0. Qed.

Lemma sqr_norm_eq1 x : (x ^+ 2 == 1) = (`|x| == 1).
Proof. by rewrite sqrf_eq1 eqr_norml ler01 andbT. Qed.

Lemma leif_mean_square_scaled x y :
  x * y *+ 2 <= x ^+ 2 + y ^+ 2 ?= iff (x == y).
Proof. exact: real_leif_mean_square_scaled. Qed.

Lemma leif_AGM2_scaled x y : x * y *+ 4 <= (x + y) ^+ 2 ?= iff (x == y).
Proof. exact: real_leif_AGM2_scaled. Qed.

Section MinMax.

Lemma oppr_max : {morph -%R : x y / max x y >-> min x y : R}.
Proof. by move=> x y; apply: real_oppr_max. Qed.

Lemma oppr_min : {morph -%R : x y / min x y >-> max x y : R}.
Proof. by move=> x y; apply: real_oppr_min. Qed.

Lemma addr_minl : @left_distributive R R +%R min.
Proof. by move=> x y z; apply: real_addr_minl. Qed.

Lemma addr_minr : @right_distributive R R +%R min.
Proof. by move=> x y z; apply: real_addr_minr. Qed.

Lemma addr_maxl : @left_distributive R R +%R max.
Proof. by move=> x y z; apply: real_addr_maxl. Qed.

Lemma addr_maxr : @right_distributive R R +%R max.
Proof. by move=> x y z; apply: real_addr_maxr. Qed.

Lemma minr_nMr x y z : x <= 0 -> x * min y z = max (x * y) (x * z).
Proof. by move=> x_le0; apply: real_minr_nMr. Qed.

Lemma maxr_nMr x y z : x <= 0 -> x * max y z = min (x * y) (x * z).
Proof. by move=> x_le0; apply: real_maxr_nMr. Qed.

Lemma minr_nMl x y z : x <= 0 -> min y z * x = max (y * x) (z * x).
Proof. by move=> x_le0; apply: real_minr_nMl. Qed.

Lemma maxr_nMl x y z : x <= 0 -> max y z * x = min (y * x) (z * x).
Proof. by move=> x_le0; apply: real_maxr_nMl. Qed.

Lemma maxrN x : max x (- x) = `|x|.   Proof. exact: real_maxrN. Qed.
Lemma maxNr x : max (- x) x = `|x|.   Proof. exact: real_maxNr. Qed.
Lemma minrN x : min x (- x) = - `|x|. Proof. exact: real_minrN. Qed.
Lemma minNr x : min (- x) x = - `|x|. Proof. exact: real_minNr. Qed.

End MinMax.

Section PolyBounds.

Variable p : {poly R}.

Lemma poly_itv_bound a b : {ub | forall x, a <= x <= b -> `|p.[x]| <= ub}.
Proof.
have [ub le_p_ub] := poly_disk_bound p (Num.max `|a| `|b|).
exists ub => x /andP[le_a_x le_x_b]; rewrite le_p_ub // le_max !ler_normr.
by have [_|_] := ler0P x; rewrite ?lerN2 ?le_a_x ?le_x_b orbT.
Qed.

Lemma monic_Cauchy_bound : p \is monic -> {b | forall x, x >= b -> p.[x] > 0}.
Proof.
move/monicP=> mon_p; pose n := (size p - 2)%N.
have [p_le1 | p_gt1] := leqP (size p) 1.
  exists 0 => x _; rewrite (size1_polyC p_le1) hornerC.
  by rewrite -[p`_0]lead_coefC -size1_polyC // mon_p ltr01.
pose lb := \sum_(j < n.+1) `|p`_j|; exists (lb + 1) => x le_ub_x.
have x_ge1: 1 <= x; last have x_gt0 := lt_le_trans ltr01 x_ge1.
  by rewrite -(lerD2l lb) ler_wpDl ?sumr_ge0 // => j _.
rewrite horner_coef -(subnK p_gt1) -/n addnS big_ord_recr /= addn1.
rewrite [in p`__]subnSK // subn1 -lead_coefE mon_p mul1r -ltrBlDl sub0r.
apply: le_lt_trans (_ : lb * x ^+ n < _); last first.
  by rewrite exprS ltr_pM2r ?exprn_gt0// -(ltrD2r 1) ltr_pwDr.
rewrite -sumrN mulr_suml ler_sum // => j _; apply: le_trans (ler_norm _) _.
rewrite normrN normrM ler_wpM2l // normrX.
by rewrite ger0_norm ?(ltW x_gt0) // ler_weXn2l ?leq_ord.
Qed.

End PolyBounds.

End RealDomainOperations.

Section RealField.

Variables (F : realFieldType) (x y : F).

Lemma leif_mean_square : x * y <= (x ^+ 2 + y ^+ 2) / 2 ?= iff (x == y).
Proof. by apply: real_leif_mean_square; apply: num_real. Qed.

Lemma leif_AGM2 : x * y <= ((x + y) / 2)^+ 2 ?= iff (x == y).
Proof. by apply: real_leif_AGM2; apply: num_real. Qed.

End RealField.

Section RealClosedFieldTheory.

Variable R : rcfType.
Implicit Types a x y : R.

Lemma poly_ivt : real_closed_axiom R. Proof. exact: poly_ivt. Qed.

(* Square Root theory *)

Lemma sqrtr_ge0 a : 0 <= sqrt a.
Proof. by rewrite /sqrt; case: (sig2W _). Qed.
Hint Resolve sqrtr_ge0 : core.

Lemma sqr_sqrtr a : 0 <= a -> sqrt a ^+ 2 = a.
Proof.
by rewrite /sqrt => a_ge0; case: (sig2W _) => /= x _; rewrite a_ge0 => /eqP.
Qed.

Lemma ler0_sqrtr a : a <= 0 -> sqrt a = 0.
Proof.
rewrite /sqrtr; case: (sig2W _) => x /= _.
by have [//|_ /eqP//|->] := ltrgt0P a; rewrite mulf_eq0 orbb => /eqP.
Qed.

Lemma ltr0_sqrtr a : a < 0 -> sqrt a = 0.
Proof. by move=> /ltW; apply: ler0_sqrtr. Qed.

Variant sqrtr_spec a : R -> bool -> bool -> R -> Type :=
| IsNoSqrtr of a < 0 : sqrtr_spec a a false true 0
| IsSqrtr b of 0 <= b : sqrtr_spec a (b ^+ 2) true false b.

Lemma sqrtrP a : sqrtr_spec a a (0 <= a) (a < 0) (sqrt a).
Proof.
have [a_ge0|a_lt0] := ger0P a.
  by rewrite -{1 2}[a]sqr_sqrtr //; constructor.
by rewrite ltr0_sqrtr //; constructor.
Qed.

Lemma sqrtr_sqr a : sqrt (a ^+ 2) = `|a|.
Proof.
have /eqP : sqrt (a ^+ 2) ^+ 2 = `|a| ^+ 2.
  by rewrite -normrX ger0_norm ?sqr_sqrtr ?sqr_ge0.
rewrite eqf_sqr => /predU1P[-> //|ha].
have := sqrtr_ge0 (a ^+ 2); rewrite (eqP ha) oppr_ge0 normr_le0 => /eqP ->.
by rewrite normr0 oppr0.
Qed.

Lemma sqrtrM a b : 0 <= a -> sqrt (a * b) = sqrt a * sqrt b.
Proof.
case: (sqrtrP a) => // {}a a_ge0 _; case: (sqrtrP b) => [b_lt0 | {}b b_ge0].
  by rewrite mulr0 ler0_sqrtr // nmulr_lle0 ?mulr_ge0.
by rewrite mulrACA sqrtr_sqr ger0_norm ?mulr_ge0.
Qed.

Lemma sqrtr0 : sqrt 0 = 0 :> R.
Proof. by move: (sqrtr_sqr 0); rewrite exprS mul0r => ->; rewrite normr0. Qed.

Lemma sqrtr1 : sqrt 1 = 1 :> R.
Proof. by move: (sqrtr_sqr 1); rewrite expr1n => ->; rewrite normr1. Qed.

Lemma sqrtr_eq0 a : (sqrt a == 0) = (a <= 0).
Proof.
case: sqrtrP => [/ltW ->|b]; first by rewrite eqxx.
case: ltrgt0P => [b_gt0|//|->]; last by rewrite exprS mul0r lexx.
by rewrite lt_geF ?pmulr_rgt0.
Qed.

Lemma sqrtr_gt0 a : (0 < sqrt a) = (0 < a).
Proof. by rewrite lt0r sqrtr_ge0 sqrtr_eq0 -ltNge andbT. Qed.

Lemma eqr_sqrt a b : 0 <= a -> 0 <= b -> (sqrt a == sqrt b) = (a == b).
Proof.
move=> a_ge0 b_ge0; apply/eqP/eqP=> [HS|->] //.
by move: (sqr_sqrtr a_ge0); rewrite HS (sqr_sqrtr b_ge0).
Qed.

Lemma ler_wsqrtr : {homo @sqrt R : a b / a <= b}.
Proof.
move=> a b /= le_ab; case: (boolP (0 <= a))=> [pa|]; last first.
  by rewrite -ltNge; move/ltW; rewrite -sqrtr_eq0; move/eqP->.
rewrite -(@ler_pXn2r R 2) ?nnegrE ?sqrtr_ge0 //.
by rewrite !sqr_sqrtr // (le_trans pa).
Qed.

Lemma ler_psqrt : {in @nneg R &, {mono sqrt : a b / a <= b}}.
Proof.
apply: le_mono_in => x y x_gt0 y_gt0.
rewrite !lt_neqAle => /andP[neq_xy le_xy].
by rewrite ler_wsqrtr // eqr_sqrt // neq_xy.
Qed.

Lemma ler_sqrt a b : 0 <= b -> (sqrt a <= sqrt b) = (a <= b).
Proof.
move=> b_ge0; have [a_le0|a_gt0] := ler0P a; last first.
  by rewrite ler_psqrt // nnegrE ltW.
by rewrite ler0_sqrtr // sqrtr_ge0 (le_trans a_le0).
Qed.

Lemma ltr_sqrt a b : 0 < b -> (sqrt a < sqrt b) = (a < b).
Proof.
move=> b_gt0; have [a_le0|a_gt0] := ler0P a; last first.
  by rewrite (leW_mono_in ler_psqrt)//; apply: ltW.
by rewrite ler0_sqrtr // sqrtr_gt0 b_gt0 (le_lt_trans a_le0).
Qed.

Lemma sqrtrV x : 0 <= x -> sqrt (x^-1) = (sqrt x)^-1.
Proof.
case: ltrgt0P => // [x_gt0 _|->]; last by rewrite !(invr0, sqrtr0).
have sx_neq0 : sqrt x != 0 by rewrite sqrtr_eq0 -ltNge.
apply: (mulfI sx_neq0).
by rewrite -sqrtrM !(divff, ltW, sqrtr1) // lt0r_neq0.
Qed.

End RealClosedFieldTheory.

Notation "z ^*" := (conj_op z) (at level 2, format "z ^*") : ring_scope.
Notation "'i" := imaginary (at level 0) : ring_scope.

Section ClosedFieldTheory.

Variable C : numClosedFieldType.
Implicit Types a x y z : C.

Definition normCK : forall x, `|x| ^+ 2 = x * x^* := normCK.

Definition sqrCi : 'i ^+ 2 = -1 :> C := sqrCi.

Lemma mulCii : 'i * 'i = -1 :> C. Proof. exact: sqrCi. Qed.

Lemma conjCK : involutive (@conj_op C).
Proof.
have JE x : x^* = `|x|^+2 / x.
  have [->|x_neq0] := eqVneq x 0; first by rewrite rmorph0 invr0 mulr0.
  by apply: (canRL (mulfK _)) => //; rewrite mulrC -normCK.
move=> x; have [->|x_neq0] := eqVneq x 0; first by rewrite !rmorph0.
rewrite !JE normrM normfV exprMn normrX normr_id.
rewrite invfM exprVn (AC (2*2) (1*(2*3)*4))/= -invfM -exprMn.
by rewrite divff ?mul1r ?invrK // !expf_eq0 normr_eq0 //.
Qed.

Let Re2 z := z + z^*.
Definition nnegIm z := (0 <= 'i * (z^* - z)).
Definition argCle y z := nnegIm z ==> nnegIm y && (Re2 z <= Re2 y).

Variant rootC_spec n (x : C) : Type :=
  RootCspec (y : C) of if (n > 0)%N then y ^+ n = x else y = 0
                        & forall z, (n > 0)%N -> z ^+ n = x -> argCle y z.

Fact rootC_subproof n x : rootC_spec n x.
Proof.
have realRe2 u : Re2 u \is Num.real by
  rewrite realEsqr expr2 {2}/Re2 -{2}[u]conjCK addrC -rmorphD -normCK exprn_ge0.
have argCle_total : total argCle.
  move=> u v; rewrite /total /argCle.
  by do 2!case: (nnegIm _) => //; rewrite ?orbT //= real_leVge.
have argCle_trans : transitive argCle.
  move=> u v w /implyP geZuv /implyP geZvw; apply/implyP.
  by case/geZvw/andP=> /geZuv/andP[-> geRuv] /le_trans->.
pose p := 'X^n - (x *+ (n > 0))%:P; have [r0 Dp] := closed_field_poly_normal p.
have sz_p : size p = n.+1.
  rewrite size_polyDl ?size_polyXn // ltnS size_polyN size_polyC mulrn_eq0.
  by case: posnP => //; case: negP.
pose r := sort argCle r0; have r_arg: sorted argCle r by apply: sort_sorted.
have{} Dp: p = \prod_(z <- r) ('X - z%:P).
  rewrite Dp lead_coefE sz_p coefB coefXn coefC -mulrb -mulrnA mulnb lt0n andNb.
  by rewrite subr0 eqxx scale1r; apply/esym/perm_big; rewrite perm_sort.
have mem_rP z: (n > 0)%N -> reflect (z ^+ n = x) (z \in r).
  move=> n_gt0; rewrite -root_prod_XsubC -Dp rootE !hornerE n_gt0.
  by rewrite subr_eq0; apply: eqP.
exists r`_0 => [|z n_gt0 /(mem_rP z n_gt0) r_z].
  have sz_r: size r = n by apply: succn_inj; rewrite -sz_p Dp size_prod_XsubC.
  case: posnP => [n0 | n_gt0]; first by rewrite nth_default // sz_r n0.
  by apply/mem_rP=> //; rewrite mem_nth ?sz_r.
case: {Dp mem_rP}r r_z r_arg => // y r1 /[1!inE] /predU1P[-> _|r1z].
  by apply/implyP=> ->; rewrite lexx.
by move/(order_path_min argCle_trans)/allP->.
Qed.

Definition nthroot n x := let: RootCspec y _ _ := rootC_subproof n x in y.
Notation "n .-root" := (nthroot n) : ring_scope.
Notation sqrtC := 2.-root.

Fact Re_lock : unit. Proof. exact: tt. Qed.
Fact Im_lock : unit. Proof. exact: tt. Qed.
Definition Re z := locked_with Re_lock ((z + z^*) / 2%:R).
Definition Im z := locked_with Im_lock ('i * (z^* - z) / 2%:R).
Notation "'Re z" := (Re z) : ring_scope.
Notation "'Im z" := (Im z) : ring_scope.

Lemma ReE z : 'Re z = (z + z^*) / 2%:R. Proof. by rewrite ['Re _]unlock. Qed.
Lemma ImE z : 'Im z = 'i * (z^* - z) / 2%:R.
Proof. by rewrite ['Im _]unlock. Qed.

Let nz2 : 2 != 0 :> C. Proof. by rewrite pnatr_eq0. Qed.

Lemma normCKC x : `|x| ^+ 2 = x^* * x. Proof. by rewrite normCK mulrC. Qed.

Lemma mul_conjC_ge0 x : 0 <= x * x^*.
Proof. by rewrite -normCK exprn_ge0. Qed.

Lemma mul_conjC_gt0 x : (0 < x * x^* ) = (x != 0).
Proof.
have [->|x_neq0] := eqVneq; first by rewrite rmorph0 mulr0.
by rewrite -normCK exprn_gt0 ?normr_gt0.
Qed.

Lemma mul_conjC_eq0 x : (x * x^* == 0) = (x == 0).
Proof. by rewrite -normCK expf_eq0 normr_eq0. Qed.

Lemma conjC_ge0 x : (0 <= x^* ) = (0 <= x).
Proof.
wlog suffices: x / 0 <= x -> 0 <= x^*.
  by move=> IH; apply/idP/idP=> /IH; rewrite ?conjCK.
rewrite [in X in X -> _]le0r => /predU1P[-> | x_gt0]; first by rewrite rmorph0.
by rewrite -(pmulr_rge0 _ x_gt0) mul_conjC_ge0.
Qed.

Lemma conjC_nat n : (n%:R)^* = n%:R :> C. Proof. exact: rmorph_nat. Qed.
Lemma conjC0 : 0^* = 0 :> C. Proof. exact: rmorph0. Qed.
Lemma conjC1 : 1^* = 1 :> C. Proof. exact: rmorph1. Qed.
Lemma conjCN1 : (- 1)^* = - 1 :> C. Proof. exact: rmorphN1. Qed.
Lemma conjC_eq0 x : (x^* == 0) = (x == 0). Proof. exact: fmorph_eq0. Qed.

Lemma invC_norm x : x^-1 = `|x| ^- 2 * x^*.
Proof.
have [-> | nx_x] := eqVneq x 0; first by rewrite conjC0 mulr0 invr0.
by rewrite normCK invfM divfK ?conjC_eq0.
Qed.

(* Real number subset. *)

Lemma CrealE x : (x \is real) = (x^* == x).
Proof.
rewrite realEsqr ger0_def normrX normCK.
by have [-> | /mulfI/inj_eq-> //] := eqVneq x 0; rewrite rmorph0 !eqxx.
Qed.

Lemma CrealP {x} : reflect (x^* = x) (x \is real).
Proof. by rewrite CrealE; apply: eqP. Qed.

Lemma conj_Creal x : x \is real -> x^* = x.
Proof. by move/CrealP. Qed.

Lemma conj_normC z : `|z|^* = `|z|.
Proof. by rewrite conj_Creal ?normr_real. Qed.

Lemma CrealJ : {mono (@conj_op C) : x / x \is Num.real}.
Proof. by apply: (homo_mono1 conjCK) => x xreal; rewrite conj_Creal. Qed.

Lemma geC0_conj x : 0 <= x -> x^* = x.
Proof. by move=> /ger0_real/CrealP. Qed.

Lemma geC0_unit_exp x n : 0 <= x -> (x ^+ n.+1 == 1) = (x == 1).
Proof. by move=> x_ge0; rewrite pexpr_eq1. Qed.

(* Elementary properties of roots. *)

Ltac case_rootC := rewrite /nthroot; case: (rootC_subproof _ _).

Lemma root0C x : 0.-root x = 0. Proof. by case_rootC. Qed.

Lemma rootCK n : (n > 0)%N -> cancel n.-root (fun x => x ^+ n).
Proof. by case: n => //= n _ x; case_rootC. Qed.

Lemma root1C x : 1.-root x = x. Proof. exact: (@rootCK 1). Qed.

Lemma rootC0 n : n.-root 0 = 0.
Proof.
have [-> | n_gt0] := posnP n; first by rewrite root0C.
by have /eqP := rootCK n_gt0 0; rewrite expf_eq0 n_gt0 /= => /eqP.
Qed.

Lemma rootC_inj n : (n > 0)%N -> injective n.-root.
Proof. by move/rootCK/can_inj. Qed.

Lemma eqr_rootC n : (n > 0)%N -> {mono n.-root : x y / x == y}.
Proof. by move/rootC_inj/inj_eq. Qed.

Lemma rootC_eq0 n x : (n > 0)%N -> (n.-root x == 0) = (x == 0).
Proof. by move=> n_gt0; rewrite -{1}(rootC0 n) eqr_rootC. Qed.

(* Rectangular coordinates. *)

Lemma nonRealCi : ('i : C) \isn't real.
Proof. by rewrite realEsqr sqrCi oppr_ge0 lt_geF ?ltr01. Qed.

Lemma neq0Ci : 'i != 0 :> C. Proof. by apply: contraNneq nonRealCi => ->. Qed.

Lemma normCi : `|'i| = 1 :> C.
Proof. by apply/eqP; rewrite -(@pexpr_eq1 _ _ 2) // -normrX sqrCi normrN1. Qed.

Lemma invCi : 'i^-1 = - 'i :> C.
Proof. by rewrite -div1r -[1]opprK -sqrCi mulNr mulfK ?neq0Ci. Qed.

Lemma conjCi : 'i^* = - 'i :> C.
Proof. by rewrite -invCi invC_norm normCi expr1n invr1 mul1r. Qed.

Lemma Crect x : x = 'Re x + 'i * 'Im x.
Proof.
rewrite !(ReE, ImE) 2!mulrA mulCii mulN1r opprB -mulrDl.
by rewrite addrACA subrr addr0 mulrDl -splitr.
Qed.

Lemma eqCP x y : x = y <-> ('Re x = 'Re y) /\ ('Im x = 'Im y).
Proof. by split=> [->//|[eqRe eqIm]]; rewrite [x]Crect [y]Crect eqRe eqIm. Qed.

Lemma eqC x y : (x == y) = ('Re x == 'Re y) && ('Im x == 'Im y).
Proof. by apply/eqP/(andPP eqP eqP) => /eqCP. Qed.

Lemma Creal_Re x : 'Re x \is real.
Proof. by rewrite ReE CrealE fmorph_div rmorph_nat rmorphD /= conjCK addrC. Qed.

Lemma Creal_Im x : 'Im x \is real.
Proof.
rewrite ImE CrealE fmorph_div rmorph_nat rmorphM /= rmorphB conjCK.
by rewrite conjCi -opprB mulrNN.
Qed.
Hint Resolve Creal_Re Creal_Im : core.

Fact Re_is_additive : additive Re.
Proof. by move=> x y; rewrite !ReE rmorphB addrACA -opprD mulrBl. Qed.
#[export]
HB.instance Definition _ := GRing.isAdditive.Build C C Re Re_is_additive.

Fact Im_is_additive : additive Im.
Proof.
by move=> x y; rewrite !ImE rmorphB opprD addrACA -opprD mulrBr mulrBl.
Qed.
#[export]
HB.instance Definition _ := GRing.isAdditive.Build C C Im Im_is_additive.

Lemma Creal_ImP z : reflect ('Im z = 0) (z \is real).
Proof.
rewrite ImE CrealE -subr_eq0 -(can_eq (mulKf neq0Ci)) mulr0.
by rewrite -(can_eq (divfK nz2)) mul0r; apply: eqP.
Qed.

Lemma Creal_ReP z : reflect ('Re z = z) (z \in real).
Proof.
rewrite (sameP (Creal_ImP z) eqP) -(can_eq (mulKf neq0Ci)) mulr0.
by rewrite -(inj_eq (addrI ('Re z))) addr0 -Crect eq_sym; apply: eqP.
Qed.

Lemma ReMl : {in real, forall x, {morph Re : z / x * z}}.
Proof.
by move=> x Rx z /=; rewrite !ReE rmorphM /= (conj_Creal Rx) -mulrDr -mulrA.
Qed.

Lemma ReMr : {in real, forall x, {morph Re : z / z * x}}.
Proof. by move=> x Rx z /=; rewrite mulrC ReMl // mulrC. Qed.

Lemma ImMl : {in real, forall x, {morph Im : z / x * z}}.
Proof.
by move=> x Rx z; rewrite !ImE rmorphM /= (conj_Creal Rx) -mulrBr mulrCA !mulrA.
Qed.

Lemma ImMr : {in real, forall x, {morph Im : z / z * x}}.
Proof. by move=> x Rx z /=; rewrite mulrC ImMl // mulrC. Qed.

Lemma Re_i : 'Re 'i = 0. Proof. by rewrite ReE conjCi subrr mul0r. Qed.

Lemma Im_i : 'Im 'i = 1.
Proof.
rewrite ImE conjCi -opprD mulrN -mulr2n mulrnAr mulCii.
by rewrite mulNrn opprK divff.
Qed.

Lemma Re_conj z : 'Re z^* = 'Re z.
Proof. by rewrite !ReE addrC conjCK. Qed.

Lemma Im_conj z : 'Im z^* = - 'Im z.
Proof. by rewrite !ImE -mulNr -mulrN opprB conjCK. Qed.

Lemma Re_rect : {in real &, forall x y, 'Re (x + 'i * y) = x}.
Proof.
move=> x y Rx Ry; rewrite /= raddfD /= (Creal_ReP x Rx).
by rewrite ReMr // Re_i mul0r addr0.
Qed.

Lemma Im_rect : {in real &, forall x y, 'Im (x + 'i * y) = y}.
Proof.
move=> x y Rx Ry; rewrite /= raddfD /= (Creal_ImP x Rx) add0r.
by rewrite ImMr // Im_i mul1r.
Qed.

Lemma conjC_rect : {in real &, forall x y, (x + 'i * y)^* = x - 'i * y}.
Proof.
by move=> x y Rx Ry; rewrite /= rmorphD rmorphM /= conjCi mulNr !conj_Creal.
Qed.

Lemma addC_rect x1 y1 x2 y2 :
  (x1 + 'i * y1) + (x2 + 'i * y2) = x1 + x2 + 'i * (y1 + y2).
Proof. by rewrite addrACA -mulrDr. Qed.

Lemma oppC_rect x y : - (x + 'i * y)  = - x + 'i * (- y).
Proof. by rewrite mulrN -opprD. Qed.

Lemma subC_rect x1 y1 x2 y2 :
  (x1 + 'i * y1) - (x2 + 'i * y2) = x1 - x2 + 'i * (y1 - y2).
Proof. by rewrite oppC_rect addC_rect. Qed.

Lemma mulC_rect x1 y1 x2 y2 : (x1 + 'i * y1) * (x2 + 'i * y2) =
                              x1 * x2 - y1 * y2 + 'i * (x1 * y2 + x2 * y1).
Proof.
rewrite mulrDl !mulrDr (AC (2*2) (1*4*(2*3)))/= mulrACA.
by rewrite -expr2 sqrCi mulN1r -!mulrA [_ * ('i * _)]mulrCA [_ * y1]mulrC.
Qed.

Lemma ImM x y : 'Im (x * y) = 'Re x * 'Im y + 'Re y * 'Im x.
Proof.
rewrite [x in LHS]Crect [y in LHS]Crect mulC_rect.
by rewrite !(Im_rect, rpredB, rpredD, rpredM).
Qed.

Lemma ImMil x : 'Im ('i * x) = 'Re x.
Proof. by rewrite ImM Re_i Im_i mul0r mulr1 add0r. Qed.

Lemma ReMil x : 'Re ('i * x) = - 'Im x.
Proof. by rewrite -ImMil mulrA mulCii mulN1r raddfN. Qed.

Lemma ReMir x : 'Re (x * 'i) = - 'Im x. Proof. by rewrite mulrC ReMil. Qed.

Lemma ImMir x : 'Im (x * 'i) = 'Re x. Proof. by rewrite mulrC ImMil. Qed.

Lemma ReM x y : 'Re (x * y) = 'Re x * 'Re y - 'Im x * 'Im y.
Proof. by rewrite -ImMil mulrCA ImM ImMil ReMil mulNr ['Im _ * _]mulrC. Qed.

Lemma normC2_rect :
  {in real &, forall x y, `|x + 'i * y| ^+ 2 = x ^+ 2 + y ^+ 2}.
Proof.
move=> x y Rx Ry; rewrite /= normCK rmorphD rmorphM /= conjCi !conj_Creal //.
by rewrite mulrC mulNr -subr_sqr exprMn sqrCi mulN1r opprK.
Qed.

Lemma normC2_Re_Im z : `|z| ^+ 2 = 'Re z ^+ 2 + 'Im z ^+ 2.
Proof. by rewrite -normC2_rect -?Crect. Qed.

Lemma invC_Crect x y : (x + 'i * y)^-1  = (x^* - 'i * y^*) / `|x + 'i * y| ^+ 2.
Proof. by rewrite /= invC_norm mulrC !rmorphE rmorphM /= conjCi mulNr. Qed.

Lemma invC_rect :
  {in real &, forall x y, (x + 'i * y)^-1  = (x - 'i * y) / (x ^+ 2 + y ^+ 2)}.
Proof. by move=> x y Rx Ry; rewrite invC_Crect normC2_rect ?conj_Creal. Qed.

Lemma ImV x : 'Im x^-1 = - 'Im x / `|x| ^+ 2.
Proof.
rewrite [x in LHS]Crect invC_rect// ImMr ?(rpredV, rpredD, rpredX)//.
by rewrite -mulrN Im_rect ?rpredN// -normC2_rect// -Crect.
Qed.

Lemma ReV x : 'Re x^-1 = 'Re x / `|x| ^+ 2.
Proof.
rewrite [x in LHS]Crect invC_rect// ReMr ?(rpredV, rpredD, rpredX)//.
by rewrite -mulrN Re_rect ?rpredN// -normC2_rect// -Crect.
Qed.

Lemma rectC_mulr x y z : (x + 'i * y) * z = x * z + 'i * (y * z).
Proof. by rewrite mulrDl mulrA. Qed.

Lemma rectC_mull x y z : z * (x + 'i * y) = z * x + 'i * (z * y).
Proof. by rewrite mulrDr mulrCA. Qed.

Lemma divC_Crect x1 y1 x2 y2 :
  (x1 + 'i * y1) / (x2 + 'i * y2) =
  (x1 * x2^* + y1 * y2^* + 'i * (x2^* * y1 - x1 * y2^*)) /
    `|x2 + 'i * y2| ^+ 2.
Proof.
rewrite invC_Crect// -mulrN [_ / _]rectC_mulr mulC_rect !mulrA -mulrBl.
rewrite [_ * _ * y1]mulrAC -mulrDl mulrA -mulrDl !(mulrN, mulNr) opprK.
by rewrite [- _ + _]addrC.
Qed.

Lemma divC_rect x1 y1 x2 y2 :
     x1 \is real -> y1 \is real -> x2 \is real -> y2 \is real ->
  (x1 + 'i * y1) / (x2 + 'i * y2) =
  (x1 * x2 + y1 * y2 + 'i * (x2 * y1 - x1 * y2)) /
    (x2 ^+ 2 + y2 ^+ 2).
Proof. by move=> *; rewrite divC_Crect normC2_rect ?conj_Creal. Qed.

Lemma Im_div x y : 'Im (x / y) = ('Re y * 'Im x - 'Re x * 'Im y) / `|y| ^+ 2.
Proof. by rewrite ImM ImV ReV mulrA [X in _ + X]mulrAC -mulrDl mulrN addrC. Qed.

Lemma Re_div x y : 'Re (x / y) = ('Re x * 'Re y + 'Im x * 'Im y) / `|y| ^+ 2.
Proof. by rewrite ReM ImV ReV !mulrA -mulrBl mulrN opprK. Qed.

Lemma leif_normC_Re_Creal z : `|'Re z| <= `|z| ?= iff (z \is real).
Proof.
rewrite -(mono_in_leif ler_sqr); try by rewrite qualifE /=.
rewrite [`|'Re _| ^+ 2]normCK conj_Creal // normC2_Re_Im -expr2.
rewrite addrC -leifBLR subrr (sameP (Creal_ImP _) eqP) -sqrf_eq0 eq_sym.
by apply: leif_eq; rewrite -realEsqr.
Qed.

Lemma leif_Re_Creal z : 'Re z <= `|z| ?= iff (0 <= z).
Proof.
have ubRe: 'Re z <= `|'Re z| ?= iff (0 <= 'Re z).
  by rewrite ger0_def eq_sym; apply/leif_eq/real_ler_norm.
congr (_ <= _ ?= iff _): (leif_trans ubRe (leif_normC_Re_Creal z)).
apply/andP/idP=> [[zRge0 /Creal_ReP <- //] | z_ge0].
by have Rz := ger0_real z_ge0; rewrite (Creal_ReP _ _).
Qed.

(* Equality from polar coordinates, for the upper plane. *)
Lemma eqC_semipolar x y :
  `|x| = `|y| -> 'Re x = 'Re y -> 0 <= 'Im x * 'Im y -> x = y.
Proof.
move=> eq_norm eq_Re sign_Im.
rewrite [x]Crect [y]Crect eq_Re; congr (_ + 'i * _).
have /eqP := congr1 (fun z => z ^+ 2) eq_norm.
rewrite !normC2_Re_Im eq_Re (can_eq (addKr _)) eqf_sqr => /pred2P[] // eq_Im.
rewrite eq_Im mulNr -expr2 oppr_ge0 real_exprn_even_le0 //= in sign_Im.
by rewrite eq_Im (eqP sign_Im) oppr0.
Qed.

(* Nth roots. *)

Let argCleP y z :
  reflect (0 <= 'Im z -> 0 <= 'Im y /\ 'Re z <= 'Re y) (argCle y z).
Proof.
suffices dIm x: nnegIm x = (0 <= 'Im x).
  rewrite /argCle !dIm !(ImE, ReE) ler_pM2r ?invr_gt0 ?ltr0n //.
  by apply: (iffP implyP) => geZyz /geZyz/andP.
by rewrite (ImE x) pmulr_lge0 ?invr_gt0 ?ltr0n //; congr (0 <= _ * _).
Qed.

Lemma rootC_Re_max n x y :
  (n > 0)%N -> y ^+ n = x -> 0 <= 'Im y -> 'Re y <= 'Re (n.-root x).
Proof.
by move=> n_gt0 yn_x leI0y; case_rootC=> z /= _ /(_ y n_gt0 yn_x)/argCleP[].
Qed.

Let neg_unity_root n : (n > 1)%N -> exists2 w : C, w ^+ n = 1 & 'Re w < 0.
Proof.
move=> n_gt1; have [|w /eqP pw_0] := closed_rootP (\poly_(i < n) (1 : C)) _.
  by rewrite size_poly_eq ?oner_eq0 // -(subnKC n_gt1).
rewrite horner_poly (eq_bigr _ (fun _ _ => mul1r _)) in pw_0.
have wn1: w ^+ n = 1 by apply/eqP; rewrite -subr_eq0 subrX1 pw_0 mulr0.
suffices /existsP[i ltRwi0]: [exists i : 'I_n, 'Re (w ^+ i) < 0].
  by exists (w ^+ i) => //; rewrite exprAC wn1 expr1n.
apply: contra_eqT (congr1 Re pw_0) => /existsPn geRw0.
rewrite raddf_sum raddf0 /= (bigD1 (Ordinal (ltnW n_gt1))) //=.
rewrite (Creal_ReP _ _) ?rpred1 // gt_eqF ?ltr_wpDr ?ltr01 //=.
by apply: sumr_ge0 => i _; rewrite real_leNgt ?rpred0.
Qed.

Lemma Im_rootC_ge0 n x : (n > 1)%N -> 0 <= 'Im (n.-root x).
Proof.
set y := n.-root x => n_gt1; have n_gt0 := ltnW n_gt1.
apply: wlog_neg; rewrite -real_ltNge ?rpred0 // => ltIy0.
suffices [z zn_x leI0z]: exists2 z, z ^+ n = x & 'Im z >= 0.
  by rewrite /y; case_rootC => /= y1 _ /(_ z n_gt0 zn_x)/argCleP[].
have [w wn1 ltRw0] := neg_unity_root n_gt1.
wlog leRI0yw: w wn1 ltRw0 / 0 <= 'Re y * 'Im w.
  move=> IHw; have: 'Re y * 'Im w \is real by rewrite rpredM.
  case/real_ge0P=> [|/ltW leRIyw0]; first exact: IHw.
  apply: (IHw w^* ); rewrite ?Re_conj ?Im_conj ?mulrN ?oppr_ge0 //.
  by rewrite -rmorphXn wn1 rmorph1.
exists (w * y); first by rewrite exprMn wn1 mul1r rootCK.
rewrite [w]Crect [y]Crect mulC_rect.
by rewrite Im_rect ?rpredD ?rpredN 1?rpredM // addr_ge0 // ltW ?nmulr_rgt0.
Qed.

Lemma rootC_lt0 n x : (1 < n)%N -> (n.-root x < 0) = false.
Proof.
set y := n.-root x => n_gt1; have n_gt0 := ltnW n_gt1.
apply: negbTE; apply: wlog_neg => /negbNE lt0y; rewrite le_gtF //.
have Rx: x \is real by rewrite -[x](rootCK n_gt0) rpredX // ltr0_real.
have Re_y: 'Re y = y by apply/Creal_ReP; rewrite ltr0_real.
have [z zn_x leR0z]: exists2 z, z ^+ n = x & 'Re z >= 0.
  have [w wn1 ltRw0] := neg_unity_root n_gt1.
  exists (w * y); first by rewrite exprMn wn1 mul1r rootCK.
  by rewrite ReMr ?ltr0_real // ltW // nmulr_lgt0.
without loss leI0z: z zn_x leR0z / 'Im z >= 0.
  move=> IHz; have: 'Im z \is real by [].
  case/real_ge0P=> [|/ltW leIz0]; first exact: IHz.
  apply: (IHz z^* ); rewrite ?Re_conj ?Im_conj ?oppr_ge0 //.
  by rewrite -rmorphXn /= zn_x conj_Creal.
by apply: le_trans leR0z _; rewrite -Re_y ?rootC_Re_max ?ltr0_real.
Qed.

Lemma rootC_ge0 n x : (n > 0)%N -> (0 <= n.-root x) = (0 <= x).
Proof.
set y := n.-root x => n_gt0.
apply/idP/idP=> [/(exprn_ge0 n) | x_ge0]; first by rewrite rootCK.
rewrite -(ge_leif (leif_Re_Creal y)).
have Ray: `|y| \is real by apply: normr_real.
rewrite -(Creal_ReP _ Ray) rootC_Re_max ?(Creal_ImP _ Ray) //.
by rewrite -normrX rootCK // ger0_norm.
Qed.

Lemma rootC_gt0 n x : (n > 0)%N -> (n.-root x > 0) = (x > 0).
Proof. by move=> n_gt0; rewrite !lt0r rootC_ge0 ?rootC_eq0. Qed.

Lemma rootC_le0 n x : (1 < n)%N -> (n.-root x <= 0) = (x == 0).
Proof.
by move=> n_gt1; rewrite le_eqVlt rootC_lt0 // orbF rootC_eq0 1?ltnW.
Qed.

Lemma ler_rootCl n : (n > 0)%N -> {in Num.nneg, {mono n.-root : x y / x <= y}}.
Proof.
move=> n_gt0 x x_ge0 y; have [y_ge0 | not_y_ge0] := boolP (0 <= y).
  by rewrite -(ler_pXn2r n_gt0) ?qualifE /= ?rootC_ge0 ?rootCK.
rewrite (contraNF (@le_trans _ _ _ 0 _ _)) ?rootC_ge0 //.
by rewrite (contraNF (le_trans x_ge0)).
Qed.

Lemma ler_rootC n : (n > 0)%N -> {in Num.nneg &, {mono n.-root : x y / x <= y}}.
Proof. by move=> n_gt0 x y x_ge0 _; apply: ler_rootCl. Qed.

Lemma ltr_rootCl n : (n > 0)%N -> {in Num.nneg, {mono n.-root : x y / x < y}}.
Proof. by move=> n_gt0 x x_ge0 y; rewrite !lt_def ler_rootCl ?eqr_rootC. Qed.

Lemma ltr_rootC n : (n > 0)%N -> {in Num.nneg &, {mono n.-root : x y / x < y}}.
Proof. by move/ler_rootC/leW_mono_in. Qed.

Lemma exprCK n x : (0 < n)%N -> 0 <= x -> n.-root (x ^+ n) = x.
Proof.
move=> n_gt0 x_ge0; apply/eqP.
by rewrite -(eqrXn2 n_gt0) ?rootC_ge0 ?exprn_ge0 ?rootCK.
Qed.

Lemma norm_rootC n x : `|n.-root x| = n.-root `|x|.
Proof.
have [-> | n_gt0] := posnP n; first by rewrite !root0C normr0.
by apply/eqP; rewrite -(eqrXn2 n_gt0) ?rootC_ge0 // -normrX !rootCK.
Qed.

Lemma rootCX n x k : (n > 0)%N -> 0 <= x -> n.-root (x ^+ k) = n.-root x ^+ k.
Proof.
move=> n_gt0 x_ge0; apply/eqP.
by rewrite -(eqrXn2 n_gt0) ?(exprn_ge0, rootC_ge0) // 1?exprAC !rootCK.
Qed.

Lemma rootC1 n : (n > 0)%N -> n.-root 1 = 1.
Proof. by move/(rootCX 0)/(_ ler01). Qed.

Lemma rootCpX n x k : (k > 0)%N -> 0 <= x -> n.-root (x ^+ k) = n.-root x ^+ k.
Proof.
by case: n => [|n] k_gt0; [rewrite !root0C expr0n gtn_eqF | apply: rootCX].
Qed.

Lemma rootCV n x : 0 <= x -> n.-root x^-1 = (n.-root x)^-1.
Proof.
move=> x_ge0; have [->|n_gt0] := posnP n; first by rewrite !root0C invr0.
apply/eqP.
by rewrite -(eqrXn2 n_gt0) ?(invr_ge0, rootC_ge0) // !exprVn !rootCK.
Qed.

Lemma rootC_eq1 n x : (n > 0)%N -> (n.-root x == 1) = (x == 1).
Proof. by move=> n_gt0; rewrite -{1}(rootC1 n_gt0) eqr_rootC. Qed.

Lemma rootC_ge1 n x : (n > 0)%N -> (n.-root x >= 1) = (x >= 1).
Proof.
by move=> n_gt0; rewrite -{1}(rootC1 n_gt0) ler_rootCl // qualifE /= ler01.
Qed.

Lemma rootC_gt1 n x : (n > 0)%N -> (n.-root x > 1) = (x > 1).
Proof. by move=> n_gt0; rewrite !lt_def rootC_eq1 ?rootC_ge1. Qed.

Lemma rootC_le1 n x : (n > 0)%N -> 0 <= x -> (n.-root x <= 1) = (x <= 1).
Proof. by move=> n_gt0 x_ge0; rewrite -{1}(rootC1 n_gt0) ler_rootCl. Qed.

Lemma rootC_lt1 n x : (n > 0)%N -> 0 <= x -> (n.-root x < 1) = (x < 1).
Proof. by move=> n_gt0 x_ge0; rewrite !lt_neqAle rootC_eq1 ?rootC_le1. Qed.

Lemma rootCMl n x z : 0 <= x -> n.-root (x * z) = n.-root x * n.-root z.
Proof.
rewrite le0r => /predU1P[-> | x_gt0]; first by rewrite !(mul0r, rootC0).
have [| n_gt1 | ->] := ltngtP n 1; last by rewrite !root1C.
  by case: n => //; rewrite !root0C mul0r.
have [x_ge0 n_gt0] := (ltW x_gt0, ltnW n_gt1).
have nx_gt0: 0 < n.-root x by rewrite rootC_gt0.
have Rnx: n.-root x \is real by rewrite ger0_real ?ltW.
apply: eqC_semipolar; last 1 first; try apply/eqP.
- by rewrite ImMl // !(Im_rootC_ge0, mulr_ge0, rootC_ge0).
- by rewrite -(eqrXn2 n_gt0) // -!normrX exprMn !rootCK.
rewrite eq_le; apply/andP; split; last first.
  rewrite rootC_Re_max ?exprMn ?rootCK ?ImMl //.
  by rewrite mulr_ge0 ?Im_rootC_ge0 ?ltW.
rewrite -[n.-root _](mulVKf (negbT (gt_eqF nx_gt0))) !(ReMl Rnx) //.
rewrite ler_pM2l // rootC_Re_max ?exprMn ?exprVn ?rootCK ?mulKf ?gt_eqF //.
by rewrite ImMl ?rpredV // mulr_ge0 ?invr_ge0 ?Im_rootC_ge0 ?ltW.
Qed.

Lemma rootCMr n x z : 0 <= x -> n.-root (z * x) = n.-root z * n.-root x.
Proof. by move=> x_ge0; rewrite mulrC rootCMl // mulrC. Qed.

Lemma imaginaryCE : 'i = sqrtC (-1).
Proof.
have : sqrtC (-1) ^+ 2 - 'i ^+ 2 == 0 by rewrite sqrCi rootCK // subrr.
rewrite subr_sqr mulf_eq0 subr_eq0 addr_eq0; have [//|_/= /eqP sCN1E] := eqP.
by have := @Im_rootC_ge0 2 (-1) isT; rewrite sCN1E raddfN /= Im_i ler0N1.
Qed.

(* More properties of n.-root will be established in cyclotomic.v. *)

(* The proper form of the Arithmetic - Geometric Mean inequality. *)

Lemma leif_rootC_AGM (I : finType) (A : {pred I}) (n := #|A|) E :
    {in A, forall i, 0 <= E i} ->
  n.-root (\prod_(i in A) E i) <= (\sum_(i in A) E i) / n%:R
                             ?= iff [forall i in A, forall j in A, E i == E j].
Proof.
move=> Ege0; have [n0 | n_gt0] := posnP n.
  rewrite n0 root0C invr0 mulr0; apply/leif_refl/forall_inP=> i.
  by rewrite (card0_eq n0).
rewrite -(mono_in_leif (ler_pXn2r n_gt0)) ?rootCK //=; first 1 last.
- by rewrite qualifE /= rootC_ge0 // prodr_ge0.
- by rewrite rpred_div ?rpred_nat ?rpred_sum.
exact: leif_AGM.
Qed.

(* Square root. *)

Lemma sqrtC0 : sqrtC 0 = 0. Proof. exact: rootC0. Qed.
Lemma sqrtC1 : sqrtC 1 = 1. Proof. exact: rootC1. Qed.
Lemma sqrtCK x : sqrtC x ^+ 2 = x. Proof. exact: rootCK. Qed.
Lemma sqrCK x : 0 <= x -> sqrtC (x ^+ 2) = x. Proof. exact: exprCK. Qed.

Lemma sqrtC_ge0 x : (0 <= sqrtC x) = (0 <= x). Proof. exact: rootC_ge0. Qed.
Lemma sqrtC_eq0 x : (sqrtC x == 0) = (x == 0). Proof. exact: rootC_eq0. Qed.
Lemma sqrtC_gt0 x : (sqrtC x > 0) = (x > 0). Proof. exact: rootC_gt0. Qed.
Lemma sqrtC_lt0 x : (sqrtC x < 0) = false. Proof. exact: rootC_lt0. Qed.
Lemma sqrtC_le0 x : (sqrtC x <= 0) = (x == 0). Proof. exact: rootC_le0. Qed.

Lemma ler_sqrtC : {in Num.nneg &, {mono sqrtC : x y / x <= y}}.
Proof. exact: ler_rootC. Qed.
Lemma ltr_sqrtC : {in Num.nneg &, {mono sqrtC : x y / x < y}}.
Proof. exact: ltr_rootC. Qed.
Lemma eqr_sqrtC : {mono sqrtC : x y / x == y}.
Proof. exact: eqr_rootC. Qed.
Lemma sqrtC_inj : injective sqrtC.
Proof. exact: rootC_inj. Qed.
Lemma sqrtCM : {in Num.nneg &, {morph sqrtC : x y / x * y}}.
Proof. by move=> x y _; apply: rootCMr. Qed.

Lemma sqrCK_P x : reflect (sqrtC (x ^+ 2) = x) ((0 <= 'Im x) && ~~ (x < 0)).
Proof.
apply: (iffP andP) => [[leI0x not_gt0x] | <-]; last first.
  by rewrite sqrtC_lt0 Im_rootC_ge0.
have /eqP := sqrtCK (x ^+ 2); rewrite eqf_sqr => /pred2P[] // defNx.
apply: sqrCK; rewrite -real_leNgt ?rpred0 // in not_gt0x;
apply/Creal_ImP/le_anti;
by rewrite leI0x -oppr_ge0 -raddfN -defNx Im_rootC_ge0.
Qed.

Lemma normC_def x : `|x| = sqrtC (x * x^* ).
Proof. by rewrite -normCK sqrCK. Qed.

Lemma norm_conjC x : `|x^*| = `|x|.
Proof. by rewrite !normC_def conjCK mulrC. Qed.

Lemma normC_rect :
  {in real &, forall x y, `|x + 'i * y| = sqrtC (x ^+ 2 + y ^+ 2)}.
Proof. by move=> x y Rx Ry; rewrite /= normC_def -normCK normC2_rect. Qed.

Lemma normC_Re_Im z : `|z| = sqrtC ('Re z ^+ 2 + 'Im z ^+ 2).
Proof. by rewrite normC_def -normCK normC2_Re_Im. Qed.

(* Norm sum (in)equalities. *)

Lemma normCDeq x y :
    `|x + y| = `|x| + `|y| ->
  {t : C | `|t| == 1 & (x, y) = (`|x| * t, `|y| * t)}.
Proof.
move=> lin_xy; apply: sig2_eqW; pose u z := if z == 0 then 1 else z / `|z|.
have uE z: (`|u z| = 1) * (`|z| * u z = z).
  rewrite /u; have [->|nz_z] := eqVneq; first by rewrite normr0 normr1 mul0r.
  by rewrite normf_div normr_id mulrCA divff ?mulr1 ?normr_eq0.
have [->|nz_x] := eqVneq x 0; first by exists (u y); rewrite uE ?normr0 ?mul0r.
exists (u x); rewrite uE // /u (negPf nz_x); congr (_ , _).
have{lin_xy} def2xy: `|x| * `|y| *+ 2 = x * y ^* + y * x ^*.
  apply/(addrI (x * x^* ))/(addIr (y * y^* )); rewrite -2!{1}normCK -sqrrD.
  by rewrite addrA -[RHS]addrA -!mulrDr -mulrDl -rmorphD -normCK lin_xy.
have def_xy: x * y^* = y * x^*.
  apply/eqP; rewrite -subr_eq0 -[_ == 0](@expf_eq0 _ _ 2).
  rewrite (canRL (subrK _) (subr_sqrDB _ _)) opprK -def2xy exprMn_n exprMn.
  by rewrite mulrN (@GRing.mul C).[AC (2*2) (1*4*(3*2))] -!normCK mulNrn addNr.
have{def_xy def2xy} def_yx: `|y * x| = y * x^*.
  by apply: (mulIf nz2); rewrite !mulr_natr mulrC normrM def2xy def_xy.
rewrite -{1}(divfK nz_x y) invC_norm mulrCA -{}def_yx !normrM invfM.
by rewrite mulrCA divfK ?normr_eq0 // mulrAC mulrA.
Qed.

Lemma normC_sum_eq (I : finType) (P : pred I) (F : I -> C) :
     `|\sum_(i | P i) F i| = \sum_(i | P i) `|F i| ->
   {t : C | `|t| == 1 & forall i, P i -> F i = `|F i| * t}.
Proof.
have [i /andP[Pi nzFi] | F0] := pickP [pred i | P i & F i != 0]; last first.
  exists 1 => [|i Pi]; first by rewrite normr1.
  by case/nandP: (F0 i) => [/negP[]// | /negbNE/eqP->]; rewrite normr0 mul0r.
rewrite !(bigD1 i Pi) /= => norm_sumF; pose Q j := P j && (j != i).
rewrite -normr_eq0 in nzFi; set c := F i / `|F i|; exists c => [|j Pj].
  by rewrite normrM normfV normr_id divff.
have [Qj | /nandP[/negP[]// | /negbNE/eqP->]] := boolP (Q j); last first.
  by rewrite mulrC divfK.
have: `|F i + F j| = `|F i| + `|F j|.
  do [rewrite !(bigD1 j Qj) /=; set z := \sum_(k | _) `|_|] in norm_sumF.
  apply/eqP; rewrite eq_le ler_normD -(lerD2r z) -addrA -norm_sumF addrA.
  by rewrite (le_trans (ler_normD _ _)) // lerD2l ler_norm_sum.
by case/normCDeq=> k _ [/(canLR (mulKf nzFi)) <-]; rewrite -(mulrC (F i)).
Qed.

Lemma normC_sum_eq1 (I : finType) (P : pred I) (F : I -> C) :
    `|\sum_(i | P i) F i| = (\sum_(i | P i) `|F i|) ->
     (forall i, P i -> `|F i| = 1) ->
   {t : C | `|t| == 1 & forall i, P i -> F i = t}.
Proof.
case/normC_sum_eq=> t t1 defF normF.
by exists t => // i Pi; rewrite defF // normF // mul1r.
Qed.

Lemma normC_sum_upper (I : finType) (P : pred I) (F G : I -> C) :
     (forall i, P i -> `|F i| <= G i) ->
     \sum_(i | P i) F i = \sum_(i | P i) G i ->
   forall i, P i -> F i = G i.
Proof.
set sumF := \sum_(i | _) _; set sumG := \sum_(i | _) _ => leFG eq_sumFG.
have posG i: P i -> 0 <= G i by move/leFG; apply: le_trans.
have norm_sumG: `|sumG| = sumG by rewrite ger0_norm ?sumr_ge0.
have norm_sumF: `|sumF| = \sum_(i | P i) `|F i|.
  apply/eqP; rewrite eq_le ler_norm_sum eq_sumFG norm_sumG -subr_ge0 -sumrB.
  by rewrite sumr_ge0 // => i Pi; rewrite subr_ge0 ?leFG.
have [t _ defF] := normC_sum_eq norm_sumF.
have [/(psumr_eq0P posG) G0 i Pi | nz_sumG] := eqVneq sumG 0.
  by apply/eqP; rewrite G0 // -normr_eq0 eq_le normr_ge0 -(G0 i Pi) leFG.
have t1: t = 1.
  apply: (mulfI nz_sumG); rewrite mulr1 -{1}norm_sumG -eq_sumFG norm_sumF.
  by rewrite mulr_suml -(eq_bigr _ defF).
have /psumr_eq0P eqFG i: P i -> 0 <= G i - F i.
  by move=> Pi; rewrite subr_ge0 defF // t1 mulr1 leFG.
move=> i /eqFG/(canRL (subrK _))->; rewrite ?add0r //.
by rewrite sumrB -/sumF eq_sumFG subrr.
Qed.

Lemma normCBeq x y :
  `|x - y| = `|x| - `|y| -> {t | `|t| == 1 & (x, y) = (`|x| * t, `|y| * t)}.
Proof.
set z := x - y; rewrite -(subrK y x) -/z => /(canLR (subrK _))/esym-Dx.
have [t t_1 [Dz Dy]] := normCDeq Dx.
by exists t; rewrite // Dx mulrDl -Dz -Dy.
Qed.

End ClosedFieldTheory.

Notation "n .-root" := (@nthroot _ n).
Notation sqrtC := 2.-root.
Notation "'i" := imaginary : ring_scope.
Notation "'Re z" := (Re z) : ring_scope.
Notation "'Im z" := (Im z) : ring_scope.

Arguments conjCK {C} x.
Arguments sqrCK {C} [x] le0x.
Arguments sqrCK_P {C x}.

#[global] Hint Extern 0 (is_true (in_mem ('Re _) _)) =>
  solve [apply: Creal_Re] : core.
#[global] Hint Extern 0 (is_true (in_mem ('Im _) _)) =>
  solve [apply: Creal_Im] : core.

Module Export Pdeg2.

Module NumClosed.

Section Pdeg2NumClosed.

Variables (F : numClosedFieldType) (p : {poly F}).

Hypothesis degp : size p = 3.

Let a := p`_2.
Let b := p`_1.
Let c := p`_0.

Let delta := b ^+ 2 - 4 * a * c.

Let r1 := (- b - sqrtC delta) / (2 * a).
Let r2 := (- b + sqrtC delta) / (2 * a).

Lemma deg2_poly_factor : p = a *: ('X - r1%:P) * ('X - r2%:P).
Proof. by apply: deg2_poly_factor; rewrite ?pnatr_eq0// sqrtCK. Qed.

Lemma deg2_poly_root1 : root p r1.
Proof. by apply: deg2_poly_root1; rewrite ?pnatr_eq0// sqrtCK. Qed.

Lemma deg2_poly_root2 : root p r2.
Proof. by apply: deg2_poly_root2; rewrite ?pnatr_eq0// sqrtCK. Qed.

End Pdeg2NumClosed.

End NumClosed.

Module NumClosedMonic.

Export FieldMonic.

Section Pdeg2NumClosedMonic.

Variables (F : numClosedFieldType) (p : {poly F}).

Hypothesis degp : size p = 3.
Hypothesis monicp : p \is monic.

Let a := p`_2.
Let b := p`_1.
Let c := p`_0.

Let delta := b ^+ 2 - 4 * c.

Let r1 := (- b - sqrtC delta) / 2.
Let r2 := (- b + sqrtC delta) / 2.

Lemma deg2_poly_factor : p = ('X - r1%:P) * ('X - r2%:P).
Proof. by apply: deg2_poly_factor; rewrite ?pnatr_eq0// sqrtCK. Qed.

Lemma deg2_poly_root1 : root p r1.
Proof. by apply: deg2_poly_root1; rewrite ?pnatr_eq0// sqrtCK. Qed.

Lemma deg2_poly_root2 : root p r2.
Proof. by apply: deg2_poly_root2; rewrite ?pnatr_eq0// sqrtCK. Qed.

End Pdeg2NumClosedMonic.
End NumClosedMonic.

Module Real.

Section Pdeg2Real.

Variable F : realFieldType.

Section Pdeg2RealConvex.

Variable p : {poly F}.
Hypothesis degp : size p = 3.

Let a := p`_2.
Let b := p`_1.
Let c := p`_0.

Hypothesis age0 : 0 <= a.

Let delta := b ^+ 2 - 4 * a * c.

Let pneq0 : p != 0. Proof. by rewrite -size_poly_gt0 degp. Qed.
Let aneq0 : a != 0.
Proof. by move: pneq0; rewrite -lead_coef_eq0 lead_coefE degp. Qed.
Let agt0 : 0 < a. Proof. by rewrite lt_def aneq0. Qed.
Let a4gt0 : 0 < 4 * a. Proof. by rewrite mulr_gt0 ?ltr0n. Qed.

Lemma deg2_poly_min x : p.[- b / (2 * a)] <= p.[x].
Proof.
rewrite [p]deg2_poly_canonical ?pnatr_eq0// -/a -/b -/c /delta !hornerE/=.
by rewrite ler_pM2l// lerD2r addrC mulNr subrr expr0n sqr_ge0.
Qed.

Lemma deg2_poly_minE : p.[- b / (2 * a)] = - delta / (4 * a).
Proof.
rewrite [p]deg2_poly_canonical ?pnatr_eq0// -/a -/b -/c -/delta !hornerE/=.
rewrite [X in X^+2]addrC [in LHS]mulNr subrr expr0n add0r mulNr.
by rewrite mulrC mulNr invfM mulrA mulfVK.
Qed.

Lemma deg2_poly_gt0 : reflect (forall x, 0 < p.[x]) (delta < 0).
Proof.
apply/(iffP idP) => [dlt0 x | /(_ (- b / (2 * a)))]; last first.
  by rewrite deg2_poly_minE ltr_pdivlMr// mul0r oppr_gt0.
apply: lt_le_trans (deg2_poly_min _).
by rewrite deg2_poly_minE ltr_pdivlMr// mul0r oppr_gt0.
Qed.

Lemma deg2_poly_ge0 : reflect (forall x, 0 <= p.[x]) (delta <= 0).
Proof.
apply/(iffP idP) => [dlt0 x | /(_ (- b / (2 * a)))]; last first.
  by rewrite deg2_poly_minE ler_pdivlMr// mul0r oppr_ge0.
apply: le_trans (deg2_poly_min _).
by rewrite deg2_poly_minE ler_pdivlMr// mul0r oppr_ge0.
Qed.

End Pdeg2RealConvex.

Section Pdeg2RealConcave.

Variable p : {poly F}.
Hypothesis degp : size p = 3.

Let a := p`_2.
Let b := p`_1.
Let c := p`_0.

Hypothesis ale0 : a <= 0.

Let delta := b ^+ 2 - 4 * a * c.

Let degpN : size (- p) = 3. Proof. by rewrite size_polyN. Qed.
Let b2a : - (- p)`_1 / (2 * (- p)`_2) = - b / (2 * a).
Proof. by rewrite !coefN mulrN divrNN. Qed.
Let deltaN : (- p)`_1 ^+ 2 - 4 * (- p)`_2 * (- p)`_0 = delta.
Proof. by rewrite !coefN sqrrN -mulrN opprK mulrN mulNr. Qed.

Lemma deg2_poly_max x : p.[x] <= p.[- b / (2 * a)].
Proof. by rewrite -lerN2 -!hornerN -b2a deg2_poly_min// coefN oppr_ge0. Qed.

Lemma deg2_poly_maxE : p.[- b / (2 * a)] = - delta / (4 * a).
Proof.
apply/eqP; rewrite [eqbRHS]mulNr -eqr_oppLR -hornerN -b2a.
by rewrite deg2_poly_minE// deltaN coefN mulrN divrNN.
Qed.

Lemma deg2_poly_lt0 : reflect (forall x, p.[x] < 0) (delta < 0).
Proof.
rewrite -deltaN; apply/(iffP (deg2_poly_gt0 _ _)); rewrite ?coefN ?oppr_ge0//.
- by move=> gt0 x; rewrite -oppr_gt0 -hornerN gt0.
- by move=> lt0 x; rewrite hornerN oppr_gt0 lt0.
Qed.

Lemma deg2_poly_le0 : reflect (forall x, p.[x] <= 0) (delta <= 0).
Proof.
rewrite -deltaN; apply/(iffP (deg2_poly_ge0 _ _)); rewrite ?coefN ?oppr_ge0//.
- by move=> ge0 x; rewrite -oppr_ge0 -hornerN ge0.
- by move=> le0 x; rewrite hornerN oppr_ge0 le0.
Qed.

End Pdeg2RealConcave.
End Pdeg2Real.

Section Pdeg2RealClosed.

Variable F : rcfType.

Section Pdeg2RealClosedConvex.

Variable p : {poly F}.
Hypothesis degp : size p = 3.

Let a := p`_2.
Let b := p`_1.
Let c := p`_0.

Let pneq0 : p != 0. Proof. by rewrite -size_poly_gt0 degp. Qed.
Let aneq0 : a != 0.
Proof. by move: pneq0; rewrite -lead_coef_eq0 lead_coefE degp. Qed.
Let sqa2 : 4 * a ^+ 2 = (2 * a) ^+ 2. Proof. by rewrite exprMn -natrX. Qed.
Let nz2 : 2 != 0 :> F. Proof. by rewrite pnatr_eq0. Qed.

Let delta := b ^+ 2 - 4 * a * c.

Let r1 := (- b - sqrt delta) / (2 * a).
Let r2 := (- b + sqrt delta) / (2 * a).

Lemma deg2_poly_factor : 0 <= delta -> p = a *: ('X - r1%:P) * ('X - r2%:P).
Proof. by move=> dge0; apply: deg2_poly_factor; rewrite ?sqr_sqrtr. Qed.

Lemma deg2_poly_root1 : 0 <= delta -> root p r1.
Proof. by move=> dge0; apply: deg2_poly_root1; rewrite ?sqr_sqrtr. Qed.

Lemma deg2_poly_root2 : 0 <= delta -> root p r2.
Proof. by move=> dge0; apply: deg2_poly_root2; rewrite ?sqr_sqrtr. Qed.

Lemma deg2_poly_noroot : reflect (forall x, ~~ root p x) (delta < 0).
Proof.
apply/(iffP idP) => [dlt0 x | /(_ r1)].
  case: ltgtP aneq0 => [agt0 _|alt0 _|//]; rewrite rootE; last first.
    exact/lt0r_neq0/(deg2_poly_gt0 degp (ltW alt0)).
  rewrite -oppr_eq0 -hornerN.
  apply/lt0r_neq0/deg2_poly_gt0; rewrite ?size_polyN ?coefN ?oppr_ge0 ?ltW//.
  by rewrite sqrrN -mulrA mulrNN mulrA.
by rewrite ltNge; apply: contraNN => ?; apply: deg2_poly_root1.
Qed.

Hypothesis age0 : 0 <= a.

Let agt0 : 0 < a. Proof. by rewrite lt_def aneq0. Qed.
Let a2gt0 : 0 < 2 * a. Proof. by rewrite mulr_gt0 ?ltr0n. Qed.
Let a4gt0 : 0 < 4 * a. Proof. by rewrite mulr_gt0 ?ltr0n. Qed.
Let aa4gt0 : 0 < 4 * a * a. Proof. by rewrite mulr_gt0 ?ltr0n. Qed.

Let xb4 x : (x + b / (2 * a)) ^+ 2 * (4 * a * a) = (x * (2 * a) + b) ^+ 2.
Proof.
have -> : 4 * a * a = (2 * a) ^+ 2 by rewrite expr2 mulrACA -natrM mulrA.
by rewrite -exprMn mulrDl mulfVK ?mulf_neq0 ?pnatr_eq0.
Qed.

Lemma deg2_poly_gt0l x : x < r1 -> 0 < p.[x].
Proof.
move=> xltr1; have [? | dge0] := ltP delta 0; first exact: deg2_poly_gt0.
have {}xltr1 : sqrt delta < - (x * (2 * a) + b).
  by rewrite ltrNr -ltrBrDr addrC -ltr_pdivlMr.
rewrite [p]deg2_poly_canonical// -/a -/b -/c -/delta !hornerE/=.
rewrite mulr_gt0// subr_gt0 ltr_pdivrMr// xb4 -sqrrN.
rewrite -ltr_sqrt ?sqrtr_sqr ?(lt_le_trans xltr1) ?ler_norm//.
by rewrite exprn_gt0 ?(le_lt_trans _ xltr1) ?sqrtr_ge0.
Qed.

Lemma deg2_poly_gt0r x : r2 < x -> 0 < p.[x].
Proof.
move=> xgtr2; have [? | dge0] := ltP delta 0; first exact: deg2_poly_gt0.
have {}xgtr2 : sqrt delta < x * (2 * a) + b.
  by rewrite -ltrBlDr addrC -ltr_pdivrMr.
rewrite [p]deg2_poly_canonical// -/a -/b -/c -/delta !hornerE/=.
rewrite mulr_gt0// subr_gt0 ltr_pdivrMr// xb4.
rewrite -ltr_sqrt ?sqrtr_sqr ?(lt_le_trans xgtr2) ?ler_norm//.
by rewrite exprn_gt0 ?(le_lt_trans _ xgtr2) ?sqrtr_ge0.
Qed.

Lemma deg2_poly_lt0m x : r1 < x < r2 -> p.[x] < 0.
Proof.
move=> /andP[r1ltx xltr2].
have [dle0 | dgt0] := leP delta 0.
  by move: (lt_trans r1ltx xltr2); rewrite /r1 /r2 ler0_sqrtr// oppr0 ltxx.
rewrite [p]deg2_poly_canonical// !hornerE/= -/a -/b -/c -/delta.
rewrite pmulr_rlt0// subr_lt0 ltr_pdivlMr// xb4 -ltr_sqrt// sqrtr_sqr ltr_norml.
by rewrite -ltrBlDr addrC -ltr_pdivrMr// r1ltx -ltrBrDr addrC -ltr_pdivlMr.
Qed.

Lemma deg2_poly_ge0l x : x <= r1 -> 0 <= p.[x].
Proof.
rewrite le_eqVlt => /orP[/eqP->|xltr1]; last exact/ltW/deg2_poly_gt0l.
have [dge0|dlt0] := leP 0 delta; last by apply: deg2_poly_ge0 => //; apply: ltW.
by rewrite le_eqVlt (rootP (deg2_poly_root1 dge0)) eqxx.
Qed.

Lemma deg2_poly_ge0r x : r2 <= x -> 0 <= p.[x].
Proof.
rewrite le_eqVlt => /orP[/eqP<-|xgtr2]; last exact/ltW/deg2_poly_gt0r.
have [dge0|dlt0] := leP 0 delta; last by apply: deg2_poly_ge0 => //; apply: ltW.
by rewrite le_eqVlt (rootP (deg2_poly_root2 dge0)) eqxx.
Qed.

Lemma deg2_poly_le0m x : 0 <= delta -> r1 <= x <= r2 -> p.[x] <= 0.
Proof.
move=> dge0; rewrite le_eqVlt andb_orl => /orP[/andP[/eqP<- _]|].
  by rewrite le_eqVlt (rootP (deg2_poly_root1 dge0)) eqxx.
rewrite le_eqVlt andb_orr => /orP[/andP[_ /eqP->]|].
  by rewrite le_eqVlt (rootP (deg2_poly_root2 dge0)) eqxx.
by move=> ?; apply/ltW/deg2_poly_lt0m.
Qed.

End Pdeg2RealClosedConvex.

Section Pdeg2RealClosedConcave.

Variable p : {poly F}.
Hypothesis degp : size p = 3.

Let a := p`_2.
Let b := p`_1.
Let c := p`_0.

Let delta := b ^+ 2 - 4 * a * c.

Let r1 := (- b + sqrt delta) / (2 * a).
Let r2 := (- b - sqrt delta) / (2 * a).

Hypothesis ale0 : a <= 0.

Let degpN : size (- p) = 3. Proof. by rewrite size_polyN. Qed.
Let aNge0 : 0 <= (- p)`_2. Proof. by rewrite coefN oppr_ge0. Qed.
Let deltaN : (- p)`_1 ^+ 2 - 4 * (- p)`_2 * (- p)`_0 = delta.
Proof. by rewrite !coefN sqrrN -mulrN opprK mulrN mulNr. Qed.
Let r1N : (- (- p)`_1 - sqrt delta) / (2 * (- p)`_2) = r1.
Proof. by rewrite !coefN -opprD mulrN divrNN. Qed.
Let r2N : (- (- p)`_1 + sqrt delta) / (2 * (- p)`_2) = r2.
Proof. by rewrite !coefN mulrN divrN -mulNr opprK opprD. Qed.

Lemma deg2_poly_lt0l x : x < r1 -> p.[x] < 0.
Proof. by move=> ?; rewrite -oppr_gt0 -hornerN deg2_poly_gt0l// deltaN r1N. Qed.

Lemma deg2_poly_lt0r x : r2 < x -> p.[x] < 0.
Proof. by move=> ?; rewrite -oppr_gt0 -hornerN deg2_poly_gt0r// deltaN r2N. Qed.

Lemma deg2_poly_gt0m x : r1 < x < r2 -> 0 < p.[x].
Proof.
by move=> ?; rewrite -oppr_lt0 -hornerN deg2_poly_lt0m// deltaN r1N r2N.
Qed.

Lemma deg2_poly_le0l x : x <= r1 -> p.[x] <= 0.
Proof. by move=> ?; rewrite -oppr_ge0 -hornerN deg2_poly_ge0l// deltaN r1N. Qed.

Lemma deg2_poly_le0r x : r2 <= x -> p.[x] <= 0.
Proof. by move=> ?; rewrite -oppr_ge0 -hornerN deg2_poly_ge0r// deltaN r2N. Qed.

Lemma deg2_poly_ge0m x : 0 <= delta -> r1 <= x <= r2 -> 0 <= p.[x].
Proof.
by move=> ? ?; rewrite -oppr_le0 -hornerN deg2_poly_le0m ?deltaN// r1N r2N.
Qed.

End Pdeg2RealClosedConcave.
End Pdeg2RealClosed.
End Real.

Module RealMonic.

Import Real.
Export FieldMonic.

Section Pdeg2RealMonic.

Variable F : realFieldType.

Variable p : {poly F}.
Hypothesis degp : size p = 3.
Hypothesis monicp : p \is monic.

Let a := p`_2.
Let b := p`_1.
Let c := p`_0.

Let delta := b ^+ 2 - 4 * c.

Let a1 : a = 1. Proof. by move: (monicP monicp); rewrite lead_coefE degp. Qed.
Let a2 : 2 * a = 2. Proof. by rewrite a1 mulr1. Qed.
Let a4 : 4 * a = 4. Proof. by rewrite a1 mulr1. Qed.

Lemma deg2_poly_min x : p.[- b / 2] <= p.[x].
Proof. by rewrite -a2 deg2_poly_min -/a ?a1 ?ler01. Qed.

Let deltam : delta = b ^+ 2 - 4 * a * c. Proof. by rewrite a1 mulr1. Qed.

Lemma deg2_poly_minE : p.[- b / 2] = - delta / 4.
Proof. by rewrite -a2 -a4 deltam deg2_poly_minE. Qed.

Lemma deg2_poly_gt0 : reflect (forall x, 0 < p.[x]) (delta < 0).
Proof. by rewrite deltam; apply: deg2_poly_gt0; rewrite // -/a a1 ler01. Qed.

Lemma deg2_poly_ge0 : reflect (forall x, 0 <= p.[x]) (delta <= 0).
Proof. by rewrite deltam; apply: deg2_poly_ge0; rewrite // -/a a1 ler01. Qed.

End Pdeg2RealMonic.

Section Pdeg2RealClosedMonic.

Variables (F : rcfType) (p : {poly F}).
Hypothesis degp : size p = 3.
Hypothesis monicp : p \is monic.

Let a := p`_2.
Let b := p`_1.
Let c := p`_0.

Let a1 : a = 1. Proof. by move: (monicP monicp); rewrite lead_coefE degp. Qed.

Let delta := b ^+ 2 - 4 * c.

Let deltam : delta = b ^+ 2 - 4 * a * c. Proof. by rewrite a1 mulr1. Qed.

Let r1 := (- b - sqrt delta) / 2.
Let r2 := (- b + sqrt delta) / 2.

Let nz2 : 2 != 0 :> F. Proof. by rewrite pnatr_eq0. Qed.

Lemma deg2_poly_factor : 0 <= delta -> p = ('X - r1%:P) * ('X - r2%:P).
Proof. by move=> dge0; apply: deg2_poly_factor; rewrite ?sqr_sqrtr. Qed.

Lemma deg2_poly_root1 : 0 <= delta -> root p r1.
Proof. by move=> dge0; apply: deg2_poly_root1; rewrite ?sqr_sqrtr. Qed.

Lemma deg2_poly_root2 : 0 <= delta -> root p r2.
Proof. by move=> dge0; apply: deg2_poly_root2; rewrite ?sqr_sqrtr. Qed.

Lemma deg2_poly_noroot : reflect (forall x, ~~ root p x) (delta < 0).
Proof. by rewrite deltam; apply: deg2_poly_noroot. Qed.

Lemma deg2_poly_gt0l x : x < r1 -> 0 < p.[x].
Proof.
by move=> ?; apply: deg2_poly_gt0l; rewrite // -/a ?a1 ?ler01 ?mulr1.
Qed.

Lemma deg2_poly_gt0r x : r2 < x -> 0 < p.[x].
Proof.
by move=> ?; apply: deg2_poly_gt0r; rewrite // -/a ?a1 ?ler01 ?mulr1.
Qed.

Lemma deg2_poly_lt0m x : r1 < x < r2 -> p.[x] < 0.
Proof.
by move=> ?; apply: deg2_poly_lt0m; rewrite // -/a ?a1 ?ler01 ?mulr1.
Qed.

Lemma deg2_poly_ge0l x : x <= r1 -> 0 <= p.[x].
Proof.
by move=> ?; apply: deg2_poly_ge0l; rewrite // -/a ?a1 ?ler01 ?mulr1.
Qed.

Lemma deg2_poly_ge0r x : r2 <= x -> 0 <= p.[x].
Proof.
by move=> ?; apply: deg2_poly_ge0r; rewrite // -/a ?a1 ?ler01 ?mulr1.
Qed.

Lemma deg2_poly_le0m x : 0 <= delta -> r1 <= x <= r2 -> p.[x] <= 0.
move=> dge0 xm.
by apply: deg2_poly_le0m; rewrite -/a -/b -/c ?a1 ?mulr1 -/delta ?ler01.
Qed.

End Pdeg2RealClosedMonic.
End RealMonic.
End Pdeg2.

Section Degle2PolyRealConvex.

Variable (F : realFieldType) (p : {poly F}).
Hypothesis degp : (size p <= 3)%N.

Let a := p`_2.
Let b := p`_1.
Let c := p`_0.

Let delta := b ^+ 2 - 4 * a * c.

Lemma deg_le2_poly_delta_ge0 : 0 <= a -> (forall x, 0 <= p.[x]) -> delta <= 0.
Proof.
move=> age0 pge0; move: degp; rewrite leq_eqVlt => /orP[/eqP|] degp'.
  exact/(Real.deg2_poly_ge0 degp' age0).
have a0 : a = 0 by rewrite /a nth_default.
rewrite /delta a0 mulr0 mul0r subr0 exprn_even_le0//=.
have [//|/eqP nzb] := eqP; move: (pge0 ((- 1 - c) / b)).
have -> : p = b *: 'X + c%:P.
  apply/polyP => + /[!coefE] => -[|[|i]] /=; rewrite !Monoid.simpm//.
  by rewrite nth_default// -ltnS (leq_trans degp').
by rewrite !hornerE/= mulrAC mulfV// mul1r subrK ler0N1.
Qed.

End Degle2PolyRealConvex.

Section Degle2PolyRealConcave.

Variable (F : realFieldType) (p : {poly F}).
Hypothesis degp : (size p <= 3)%N.

Let a := p`_2.
Let b := p`_1.
Let c := p`_0.

Let delta := b ^+ 2 - 4 * a * c.

Lemma deg_le2_poly_delta_le0 : a <= 0 -> (forall x, p.[x] <= 0) -> delta <= 0.
Proof.
move=> ale0 ple0; rewrite /delta -sqrrN -[c]opprK mulrN -mulNr -[-(4 * a)]mulrN.
rewrite -!coefN deg_le2_poly_delta_ge0 ?size_polyN ?coefN ?oppr_ge0// => x.
by rewrite hornerN oppr_ge0.
Qed.

End Degle2PolyRealConcave.

Section Degle2PolyRealClosedConvex.

Variable (F : rcfType) (p : {poly F}).
Hypothesis degp : (size p <= 3)%N.

Let a := p`_2.
Let b := p`_1.
Let c := p`_0.

Let delta := b ^+ 2 - 4 * a * c.

Lemma deg_le2_poly_ge0 : (forall x, 0 <= p.[x]) -> delta <= 0.
Proof.
have [age0|alt0] := leP 0 a; first exact: deg_le2_poly_delta_ge0.
move=> pge0; move: degp; rewrite leq_eqVlt => /orP[/eqP|] degp'; last first.
  by move: alt0; rewrite /a nth_default ?ltxx.
have [//|dge0] := leP delta 0.
pose r1 := (- b - sqrt delta) / (2 * a).
pose r2 := (- b + sqrt delta) / (2 * a).
pose x0 := Num.max (r1 + 1) (r2 + 1).
move: (pge0 x0); rewrite (Real.deg2_poly_factor degp' (ltW dge0)).
rewrite !hornerE/= -mulrA nmulr_rge0// leNgt => /negbTE<-.
by apply: mulr_gt0; rewrite subr_gt0 lt_max ltrDl ltr01 ?orbT.
Qed.

End Degle2PolyRealClosedConvex.

Section Degle2PolyRealClosedConcave.

Variable (F : rcfType) (p : {poly F}).
Hypothesis degp : (size p <= 3)%N.

Let a := p`_2.
Let b := p`_1.
Let c := p`_0.

Let delta := b ^+ 2 - 4 * a * c.

Lemma deg_le2_poly_le0 : (forall x, p.[x] <= 0) -> delta <= 0.
Proof.
move=> ple0; rewrite /delta -sqrrN -[c]opprK mulrN -mulNr -[-(4 * a)]mulrN.
by rewrite -!coefN deg_le2_poly_ge0 ?size_polyN// => x; rewrite hornerN oppr_ge0.
Qed.

End Degle2PolyRealClosedConcave.

End Theory.

HB.factory Record IntegralDomain_isNumRing R of GRing.IntegralDomain R := {
  Rle : rel R;
  Rlt : rel R;
  norm : R -> R;
  normD     : forall x y, Rle (norm (x + y)) (norm x + norm y);
  addr_gt0  : forall x y, Rlt 0 x -> Rlt 0 y -> Rlt 0 (x + y);
  norm_eq0  : forall x, norm x = 0 -> x = 0;
  ger_total : forall x y, Rle 0 x -> Rle 0 y -> Rle x y || Rle y x;
  normM     : {morph norm : x y / x * y};
  le_def    : forall x y, (Rle x y) = (norm (y - x) == y - x);
  lt_def    : forall x y, (Rlt x y) = (y != x) && (Rle x y)
}.

HB.builders Context R of IntegralDomain_isNumRing R.
  Local Notation "x <= y" := (Rle x y) : ring_scope.
  Local Notation "x < y" := (Rlt x y) : ring_scope.
  Local Notation "`| x |" := (norm x) : ring_scope.

  Lemma ltrr x : x < x = false. Proof. by rewrite lt_def eqxx. Qed.

  Lemma ge0_def x : (0 <= x) = (`|x| == x).
  Proof. by rewrite le_def subr0. Qed.

  Lemma subr_ge0 x y : (0 <= x - y) = (y <= x).
  Proof. by rewrite ge0_def -le_def. Qed.

  Lemma subr_gt0 x y : (0 < y - x) = (x < y).
  Proof. by rewrite !lt_def subr_eq0 subr_ge0. Qed.

  Lemma lt_trans : transitive Rlt.
  Proof.
  move=> y x z le_xy le_yz.
  by rewrite -subr_gt0 -(subrK y z) -addrA addr_gt0 // subr_gt0.
  Qed.

  Lemma le01 : 0 <= 1.
  Proof.
  have n1_nz: `|1| != 0 :> R by apply: contraNneq (@oner_neq0 R) => /norm_eq0->.
  by rewrite ge0_def -(inj_eq (mulfI n1_nz)) -normM !mulr1.
  Qed.

  Lemma lt01 : 0 < 1.
  Proof. by rewrite lt_def oner_neq0 le01. Qed.

  Lemma ltW x y : x < y -> x <= y. Proof. by rewrite lt_def => /andP[]. Qed.

  Lemma lerr x : x <= x.
  Proof.
  have n2: `|2| == 2 :> R by rewrite -ge0_def ltW ?addr_gt0 ?lt01.
  rewrite le_def subrr -(inj_eq (addrI `|0|)) addr0 -mulr2n -mulr_natr.
  by rewrite -(eqP n2) -normM mul0r.
  Qed.

  Lemma le_def' x y : (x <= y) = (x == y) || (x < y).
  Proof. by rewrite lt_def; case: eqVneq => //= ->; rewrite lerr. Qed.

  Lemma le_trans : transitive Rle.
  by move=> y x z; rewrite !le_def' => /predU1P [->|hxy] // /predU1P [<-|hyz];
    rewrite ?hxy ?(lt_trans hxy hyz) orbT.
  Qed.

  Lemma normrMn x n : `|x *+ n| = `|x| *+ n.
  Proof.
  rewrite -mulr_natr -[RHS]mulr_natr normM.
  congr (_ * _); apply/eqP; rewrite -ge0_def.
  elim: n => [|n ih]; [exact: lerr | apply: (le_trans ih)].
  by rewrite le_def -natrB // subSnn -[_%:R]subr0 -le_def mulr1n le01.
  Qed.

  Lemma normrN1 : `|-1| = 1 :> R.
  Proof.
  have: `|-1| ^+ 2 == 1 :> R
    by rewrite expr2 /= -normM mulrNN mul1r -[1]subr0 -le_def le01.
  rewrite sqrf_eq1 => /predU1P [] //; rewrite -[-1]subr0 -le_def.
  have ->: 0 <= -1 = (-1 == 0 :> R) || (0 < -1)
    by rewrite lt_def; case: eqP => // ->; rewrite lerr.
  by rewrite oppr_eq0 oner_eq0 => /(addr_gt0 lt01); rewrite subrr ltrr.
  Qed.

  Lemma normrN x : `|- x| = `|x|.
  Proof. by rewrite -mulN1r normM -[RHS]mul1r normrN1. Qed.

  HB.instance Definition _ :=
    Order.LtLe_isPOrder.Build ring_display R le_def' ltrr lt_trans.

  HB.instance Definition _ :=
    Zmodule_isNormed.Build _ R normD norm_eq0 normrMn normrN.

  HB.instance Definition _ :=
    isNumRing.Build R addr_gt0 ger_total normM le_def.
HB.end.

HB.factory Record NumDomain_isReal R of NumDomain R := {
  real : real_axiom R
}.

HB.builders Context R of NumDomain_isReal R.
  Lemma le_total : Order.POrder_isTotal ring_display R.
  Proof.
  constructor=> x y; move: (real (x - y)).
  by rewrite unfold_in /= !ler_def subr0 add0r opprB orbC.
  Qed.

  HB.instance Definition _ := le_total.
HB.end.

HB.factory Record IntegralDomain_isLeReal R of GRing.IntegralDomain R := {
  Rle : rel R;
  Rlt : rel R;
  norm : R -> R;
  le0_add   : forall x y, Rle 0 x -> Rle 0 y -> Rle 0 (x + y);
  le0_mul   : forall x y, Rle 0 x -> Rle 0 y -> Rle 0 (x * y);
  le0_anti  : forall x, Rle 0 x -> Rle x 0 -> x = 0;
  sub_ge0   : forall x y, Rle 0 (y - x) = Rle x y;
  le0_total : forall x, Rle 0 x || Rle x 0;
  normN     : forall x, norm (- x) = norm x;
  ge0_norm  : forall x, Rle 0 x -> norm x = x;
  lt_def    : forall x y, Rlt x y = (y != x) && Rle x y;
}.

HB.builders Context R of IntegralDomain_isLeReal R.
  Local Notation le := Rle.
  Local Notation lt := Rlt.

  Local Notation "x <= y" := (le x y) : ring_scope.
  Local Notation "x < y" := (lt x y) : ring_scope.
  Local Notation "`| x |" := (norm x) : ring_scope.

  Let le0N x : (0 <= - x) = (x <= 0). Proof. by rewrite -sub0r sub_ge0. Qed.
  Let leN_total x : 0 <= x \/ 0 <= - x.
  Proof. by apply/orP; rewrite le0N le0_total. Qed.

  Let le00 : 0 <= 0. Proof. by have:= le0_total 0; rewrite orbb. Qed.

  Fact lt0_add x y : 0 < x -> 0 < y -> 0 < x + y.
  Proof.
  rewrite !lt_def => /andP [x_neq0 l0x] /andP [y_neq0 l0y]; rewrite le0_add //.
  rewrite andbT addr_eq0; apply: contraNneq x_neq0 => hxy.
  by rewrite [x](@le0_anti) // hxy -le0N opprK.
  Qed.

  Fact eq0_norm x : `|x| = 0 -> x = 0.
  Proof.
  case: (leN_total x) => /ge0_norm => [-> // | Dnx nx0].
  by rewrite -[x]opprK -Dnx normN nx0 oppr0.
  Qed.

  Fact le_def x y : (x <= y) = (`|y - x| == y - x).
  Proof.
  wlog ->: x y / x = 0 by move/(_ 0 (y - x)); rewrite subr0 sub_ge0 => ->.
  rewrite {x}subr0; apply/idP/eqP=> [/ge0_norm// | Dy].
  by have [//| ny_ge0] := leN_total y; rewrite -Dy -normN ge0_norm.
  Qed.

  Fact normM : {morph norm : x y / x * y}.
  Proof.
  move=> x y /=; wlog x_ge0 : x / 0 <= x.
    by move=> IHx; case: (leN_total x) => /IHx//; rewrite mulNr !normN.
  wlog y_ge0 : y / 0 <= y; last by rewrite ?ge0_norm ?le0_mul.
  by move=> IHy; case: (leN_total y) => /IHy//; rewrite mulrN !normN.
  Qed.

  Fact le_normD x y : `|x + y| <= `|x| + `|y|.
  Proof.
  wlog x_ge0 : x y / 0 <= x.
    by move=> IH; case: (leN_total x) => /IH// /(_ (- y)); rewrite -opprD !normN.
  rewrite -sub_ge0 ge0_norm //; have [y_ge0 | ny_ge0] := leN_total y.
    by rewrite !ge0_norm ?subrr ?le0_add.
  rewrite -normN ge0_norm //; have [hxy|hxy] := leN_total (x + y).
    by rewrite ge0_norm // opprD addrCA -addrA addKr le0_add.
  by rewrite -normN ge0_norm // opprK addrCA addrNK le0_add.
  Qed.

  Fact le_total : total le.
  Proof. by move=> x y; rewrite -sub_ge0 -opprB le0N orbC -sub_ge0 le0_total. Qed.

  HB.instance Definition _ := IntegralDomain_isNumRing.Build R
    le_normD lt0_add eq0_norm (in2W le_total) normM le_def lt_def.

  HB.instance Definition _ := Order.POrder_isTotal.Build ring_display R
    le_total.
HB.end.

HB.factory Record IntegralDomain_isLtReal R of GRing.IntegralDomain R := {
  Rlt : rel R;
  Rle : rel R;
  norm : R -> R;
  lt0_add   : forall x y, Rlt 0 x -> Rlt 0 y -> Rlt 0 (x + y);
  lt0_mul   : forall x y, Rlt 0 x -> Rlt 0 y -> Rlt 0 (x * y);
  lt0_ngt0  : forall x,  Rlt 0 x -> ~~ (Rlt x 0);
  sub_gt0   : forall x y, Rlt 0 (y - x) = Rlt x y;
  lt0_total : forall x, x != 0 -> Rlt 0 x || Rlt x 0;
  normN     : forall x, norm (- x) = norm x;
  ge0_norm  : forall x, Rle 0 x -> norm x = x;
  le_def    : forall x y, Rle x y = (x == y) || Rlt x y;
}.

HB.builders Context R of IntegralDomain_isLtReal R.
  Local Notation le := Rle.
  Local Notation lt := Rlt.

  Local Notation "x < y" := (lt x y) : ring_scope.
  Local Notation "x <= y" := (le x y) : ring_scope.
  Local Notation "`| x |" := (norm x) : ring_scope.

  Fact lt0N x : (- x < 0) = (0 < x).
  Proof. by rewrite -sub_gt0 add0r opprK. Qed.
  Let leN_total x : 0 <= x \/ 0 <= - x.
  Proof.
  rewrite !le_def [_ == - x]eq_sym oppr_eq0 -[0 < - x]lt0N opprK.
  apply/orP; case: (eqVneq x) => //=; exact: lt0_total.
  Qed.

  Let le00 : (0 <= 0). Proof. by rewrite le_def eqxx. Qed.

  Fact sub_ge0 x y : (0 <= y - x) = (x <= y).
  Proof. by rewrite !le_def eq_sym subr_eq0 eq_sym sub_gt0. Qed.

  Fact le0_add x y : 0 <= x -> 0 <= y -> 0 <= x + y.
  Proof.
  rewrite !le_def => /predU1P [<-|x_gt0]; first by rewrite add0r.
  by case/predU1P=> [<-|y_gt0]; rewrite ?addr0 ?x_gt0 ?lt0_add // orbT.
  Qed.

  Fact le0_mul x y : 0 <= x -> 0 <= y -> 0 <= x * y.
  Proof.
  rewrite !le_def => /predU1P [<-|x_gt0]; first by rewrite mul0r eqxx.
  by case/predU1P=> [<-|y_gt0]; rewrite ?mulr0 ?eqxx ?lt0_mul // orbT.
  Qed.

  Fact normM : {morph norm : x y / x * y}.
  Proof.
  move=> x y /=; wlog x_ge0 : x / 0 <= x.
    by move=> IHx; case: (leN_total x) => /IHx//; rewrite mulNr !normN.
  wlog y_ge0 : y / 0 <= y; last by rewrite ?ge0_norm ?le0_mul.
  by move=> IHy; case: (leN_total y) => /IHy//; rewrite mulrN !normN.
  Qed.

  Fact le_normD x y : `|x + y| <= `|x| + `|y|.
  Proof.
  wlog x_ge0 : x y / 0 <= x.
    by move=> IH; case: (leN_total x) => /IH// /(_ (- y)); rewrite -opprD !normN.
  rewrite -sub_ge0 ge0_norm //; have [y_ge0 | ny_ge0] := leN_total y.
    by rewrite !ge0_norm ?subrr ?le0_add.
  rewrite -normN ge0_norm //; have [hxy|hxy] := leN_total (x + y).
    by rewrite ge0_norm // opprD addrCA -addrA addKr le0_add.
  by rewrite -normN ge0_norm // opprK addrCA addrNK le0_add.
  Qed.

  Fact eq0_norm x : `|x| = 0 -> x = 0.
  Proof.
  case: (leN_total x) => /ge0_norm => [-> // | Dnx nx0].
  by rewrite -[x]opprK -Dnx normN nx0 oppr0.
  Qed.

  Fact le_def' x y : (x <= y) = (`|y - x| == y - x).
  Proof.
  wlog ->: x y / x = 0 by move/(_ 0 (y - x)); rewrite subr0 sub_ge0 => ->.
  rewrite {x}subr0; apply/idP/eqP=> [/ge0_norm// | Dy].
  by have [//| ny_ge0] := leN_total y; rewrite -Dy -normN ge0_norm.
  Qed.

  Fact lt_def x y : (x < y) = (y != x) && (x <= y).
  Proof.
  rewrite le_def; case: eqVneq => //= ->; rewrite -sub_gt0 subrr.
  by apply/idP=> lt00; case/negP: (lt0_ngt0 lt00).
  Qed.

  Fact le_total : total le.
  Proof.
  move=> x y; rewrite !le_def; have [->|] //= := eqVneq; rewrite -subr_eq0.
  by move/lt0_total; rewrite -(sub_gt0 (x - y)) sub0r opprB !sub_gt0 orbC.
  Qed.

  HB.instance Definition _ := IntegralDomain_isNumRing.Build R
    le_normD lt0_add eq0_norm (in2W le_total) normM le_def' lt_def.

  HB.instance Definition _ := Order.POrder_isTotal.Build ring_display R
    le_total.
HB.end.

Module Exports. HB.reexport. End Exports.

End Num.
Export Num.Exports.

Export Num.Syntax Num.PredInstances.

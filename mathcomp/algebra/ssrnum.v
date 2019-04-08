(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrfun ssrbool eqtype ssrnat seq div choice fintype path.
From mathcomp
Require Import bigop ssralg finset fingroup zmodp poly.

(******************************************************************************)
(*                                                                            *)
(* This file defines some classes to manipulate number structures, i.e        *)
(*   structures with an order and a norm                                      *)
(*                                                                            *)
(*   * NumDomain  (Integral domain with an order and a norm)                  *)
(*         NumMixin == the mixin that provides an order and a norm over       *)
(*                     a ring and their characteristic properties.            *)
(*    numDomainType == interface for a num integral domain.                   *)
(*    NumDomainType T m                                                       *)
(*                  == packs the num mixin into a numberDomainType. The       *)
(*                     carrier T must have a integral domain structure.       *)
(*  [numDomainType of T for S ]                                               *)
(*                  == T-clone of the numDomainType structure  S.             *)
(*  [numDomainType of T]                                                      *)
(*                 == clone of a canonical numDomainType structure on T.      *)
(*                                                                            *)
(*   * NumField (Field with an order and a norm)                              *)
(*    numFieldType == interface for a num field.                              *)
(*  [numFieldType of T]                                                       *)
(*                  == clone of a canonical numFieldType structure on T       *)
(*                                                                            *)
(*   * NumClosedField (Closed Field with an order and a norm)                 *)
(*    numClosedFieldType                                                      *)
(*                  == interface for a num closed field.                      *)
(*  [numClosedFieldType of T]                                                 *)
(*                  == clone of a canonical numClosedFieldType structure on T *)
(*                                                                            *)
(*   * RealDomain  (Num domain where all elements are positive or negative)   *)
(*   realDomainType == interface for a real integral domain.                  *)
(*   RealDomainType T r                                                       *)
(*                  == packs the  real axiom r into a realDomainType. The     *)
(*                     carrier T must have a num domain structure.            *)
(*  [realDomainType of T for S ]                                              *)
(*                  == T-clone of the realDomainType structure  S.            *)
(*  [realDomainType of T]                                                     *)
(*                  == clone of a canonical realDomainType structure on T.    *)
(*                                                                            *)
(*   * RealField (Num Field where all elements are positive or negative)      *)
(*    realFieldType == interface for a real field.                            *)
(*  [realFieldType of T]                                                      *)
(*                  == clone of a canonical realFieldType structure on T      *)
(*                                                                            *)
(*   * ArchiField (A Real Field with the archimedean axiom)                   *)
(*  archiFieldType  == interface for an archimedean field.                    *)
(*   ArchiFieldType T r                                                       *)
(*                  == packs the archimeadean axiom r into an archiFieldType. *)
(*                     The  carrier T must have a real field type structure.  *)
(*  [archiFieldType of T for S ]                                              *)
(*                  == T-clone of the archiFieldType structure  S.            *)
(*  [archiFieldType of T]                                                     *)
(*                  == clone of a canonical archiFieldType structure on T     *)
(*                                                                            *)
(*   * RealClosedField (Real Field with the real closed axiom)                *)
(*    rcfType       == interface for a real closed field.                     *)
(*   RcfType T r    == packs the real closed axiom r into a                   *)
(*                     rcfType. The  carrier T must have a real               *)
(*                     field type structure.                                  *)
(*  [rcfType of T]  == clone of a canonical realClosedFieldType structure on  *)
(*                     T.                                                     *)
(*  [rcfType of T for S ]                                                     *)
(*                  == T-clone of the realClosedFieldType structure  S.       *)
(*                                                                            *)
(*   * NumClosedField (Partially ordered Closed Field with conjugation)       *)
(*    numClosedFieldType       == interface for a closed field with conj.     *)
(*  NumClosedFieldType T r    == packs the real closed axiom r into a         *)
(*                     numClosedFieldType. The  carrier T must have a closed  *)
(*                     field type structure.                                  *)
(*  [numClosedFieldType of T]  == clone of a canonical numClosedFieldType     *)
(*                               structure on  T                              *)
(*  [numClosedFieldType of T for S ]                                          *)
(*                  == T-clone of the realClosedFieldType structure  S.       *)
(*                                                                            *)
(* Over these structures, we have the following operations                    *)
(*            `|x| == norm of x.                                              *)
(*          x <= y <=> x is less than or equal to y (:= '|y - x| == y - x).   *)
(*           x < y <=> x is less than y (:= (x <= y) && (x != y)).            *)
(* x <= y ?= iff C <-> x is less than y, or equal iff C is true.              *)
(*        Num.sg x == sign of x: equal to 0 iff x = 0, to 1 iff x > 0, and    *)
(*                    to -1 in all other cases (including x < 0).             *)
(*  x \is a Num.pos <=> x is positive (:= x > 0).                             *)
(*  x \is a Num.neg <=> x is negative (:= x < 0).                             *)
(* x \is a Num.nneg <=> x is positive or 0 (:= x >= 0).                       *)
(* x \is a Num.real <=> x is real (:= x >= 0 or x < 0).                       *)
(*      Num.min x y == minimum of x y                                         *)
(*      Num.max x y == maximum of x y                                         *)
(*      Num.bound x == in archimedean fields, and upper bound for x, i.e.,    *)
(*                     and n such that `|x| < n%:R.                           *)
(*       Num.sqrt x == in a real-closed field, a positive square root of x if *)
(*                     x >= 0, or 0 otherwise.                                *)
(* For numeric algebraically closed fields we provide the generic definitions *)
(*         'i == the imaginary number (:= sqrtC (-1)).                        *)
(*      'Re z == the real component of z.                                     *)
(*      'Im z == the imaginary component of z.                                *)
(*        z^* == the complex conjugate of z (:= conjC z).                     *)
(*    sqrtC z == a nonnegative square root of z, i.e., 0 <= sqrt x if 0 <= x. *)
(*  n.-root z == more generally, for n > 0, an nth root of z, chosen with a   *)
(*               minimal non-negative argument for n > 1 (i.e., with a        *)
(*               maximal real part subject to a nonnegative imaginary part).  *)
(*               Note that n.-root (-1) is a primitive 2nth root of unity,    *)
(*               an thus not equal to -1 for n odd > 1 (this will be shown in *)
(*               file cyclotomic.v).                                          *)
(*                                                                            *)
(*  There are now three distinct uses of the symbols <, <=, > and >=:         *)
(*    0-ary, unary (prefix) and binary (infix).                               *)
(*  0. <%R, <=%R, >%R, >=%R stand respectively for lt, le, gt and ge.         *)
(*  1. (< x),  (<= x), (> x),  (>= x) stand respectively for                  *)
(*     (gt x), (ge x), (lt x), (le x).                                        *)
(*     So (< x) is a predicate characterizing elements smaller than x.        *)
(*  2. (x < y), (x <= y), ... mean what they are expected to.                 *)
(*  These convention are compatible with haskell's,                           *)
(*   where ((< y) x) = (x < y) = ((<) x y),                                   *)
(*   except that we write <%R instead of (<).                                 *)
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
(* [arg minr_(i < i0 | P) M] == a value i : T minimizing M : R, subject       *)
(*                   to the condition P (i may appear in P and M), and        *)
(*                   provided P holds for i0.                                 *)
(* [arg maxr_(i > i0 | P) M] == a value i maximizing M subject to P and       *)
(*                   provided P holds for i0.                                 *)
(* [arg minr_(i < i0 in A) M] == an i \in A minimizing M if i0 \in A.         *)
(* [arg maxr_(i > i0 in A) M] == an i \in A maximizing M if i0 \in A.         *)
(* [arg minr_(i < i0) M] == an i : T minimizing M, given i0 : T.              *)
(* [arg maxr_(i > i0) M] == an i : T maximizing M, given i0 : T.              *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory.

Reserved Notation "<= y" (at level 35).
Reserved Notation ">= y" (at level 35).
Reserved Notation "< y" (at level 35).
Reserved Notation "> y" (at level 35).
Reserved Notation "<= y :> T" (at level 35, y at next level).
Reserved Notation ">= y :> T" (at level 35, y at next level).
Reserved Notation "< y :> T" (at level 35, y at next level).
Reserved Notation "> y :> T" (at level 35, y at next level).

Module Num.

(* Principal mixin; further classes add axioms rather than operations. *)
Record mixin_of (R : ringType) := Mixin {
  norm_op : R -> R;
  le_op : rel R;
  lt_op : rel R;
  _ : forall x y, le_op (norm_op (x + y)) (norm_op x + norm_op y);
  _ : forall x y, lt_op 0 x -> lt_op 0 y -> lt_op 0 (x + y);
  _ : forall x, norm_op x = 0 -> x = 0;
  _ : forall x y, le_op 0 x -> le_op 0 y -> le_op x y || le_op y x;
  _ : {morph norm_op : x y / x * y};
  _ : forall x y, (le_op x y) = (norm_op (y - x) == y - x);
  _ : forall x y, (lt_op x y) = (y != x) && (le_op x y)
}.

Local Notation ring_for T b := (@GRing.Ring.Pack T b).

(* Base interface. *)
Module NumDomain.

Section ClassDef.

Record class_of T := Class {
  base : GRing.IntegralDomain.class_of T;
  mixin : mixin_of (ring_for T base)
}.
Local Coercion base : class_of >-> GRing.IntegralDomain.class_of.
Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c  as cT' := cT return class_of cT' in c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition clone c of phant_id class c := @Pack T c.
Definition pack b0 (m0 : mixin_of (ring_for T b0)) :=
  fun bT b & phant_id (GRing.IntegralDomain.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m).

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition zmodType := @GRing.Zmodule.Pack cT xclass.
Definition ringType := @GRing.Ring.Pack cT xclass.
Definition comRingType := @GRing.ComRing.Pack cT xclass.
Definition unitRingType := @GRing.UnitRing.Pack cT xclass.
Definition comUnitRingType := @GRing.ComUnitRing.Pack cT xclass.
Definition idomainType := @GRing.IntegralDomain.Pack cT xclass.

End ClassDef.

Module Exports.
Coercion base : class_of >-> GRing.IntegralDomain.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical comRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical unitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical comUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical idomainType.
Notation numDomainType := type.
Notation NumMixin := Mixin.
Notation NumDomainType T m := (@pack T _ m _ _ id _ id).
Notation "[ 'numDomainType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'numDomainType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'numDomainType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'numDomainType'  'of'  T ]") : form_scope.
End Exports.

End NumDomain.
Import NumDomain.Exports.

Module Import Def. Section Def.
Import NumDomain.
Context {R : type}.
Implicit Types (x y : R) (C : bool).

Definition normr : R -> R := norm_op (class R).
Definition ler : rel R := le_op (class R).
Definition ltr : rel R := lt_op (class R).
Local Notation "x <= y" := (ler x y) : ring_scope.
Local Notation "x < y" := (ltr x y) : ring_scope.

Definition ger : simpl_rel R := [rel x y | y <= x].
Definition gtr : simpl_rel R := [rel x y | y < x].
Definition lerif x y C : Prop := ((x <= y) * ((x == y) = C))%type.
Definition sgr x : R := if x == 0 then 0 else if x < 0 then -1 else 1.
Definition minr x y : R := if x <= y then x else y.
Definition maxr x y : R := if y <= x then x else y.

Definition Rpos : qualifier 0 R := [qualify x : R | 0 < x].
Definition Rneg : qualifier 0 R := [qualify x : R | x < 0].
Definition Rnneg : qualifier 0 R := [qualify x : R | 0 <= x].
Definition Rreal : qualifier 0 R := [qualify x : R | (0 <= x) || (x <= 0)].
End Def. End Def.

(* Shorter qualified names, when Num.Def is not imported. *)
Notation norm := normr.
Notation le := ler.
Notation lt := ltr.
Notation ge := ger.
Notation gt := gtr.
Notation sg := sgr.
Notation max := maxr.
Notation min := minr.
Notation pos := Rpos.
Notation neg := Rneg.
Notation nneg := Rnneg.
Notation real := Rreal.

Module Keys. Section Keys.
Variable R : numDomainType.
Fact Rpos_key : pred_key (@pos R). Proof. by []. Qed.
Definition Rpos_keyed := KeyedQualifier Rpos_key.
Fact Rneg_key : pred_key (@real R). Proof. by []. Qed.
Definition Rneg_keyed := KeyedQualifier Rneg_key.
Fact Rnneg_key : pred_key (@nneg R). Proof. by []. Qed.
Definition Rnneg_keyed := KeyedQualifier Rnneg_key.
Fact Rreal_key : pred_key (@real R). Proof. by []. Qed.
Definition Rreal_keyed := KeyedQualifier Rreal_key.
Definition ler_of_leif x y C (le_xy : @lerif R x y C) := le_xy.1 : le x y.
End Keys. End Keys.

(* (Exported) symbolic syntax. *)
Module Import Syntax.
Import Def Keys.

Notation "`| x |" := (norm x) : ring_scope.

Notation "<%R" := lt : ring_scope.
Notation ">%R" := gt : ring_scope.
Notation "<=%R" := le : ring_scope.
Notation ">=%R" := ge : ring_scope.
Notation "<?=%R" := lerif : ring_scope.

Notation "< y" := (gt y) : ring_scope.
Notation "< y :> T" := (< (y : T)) : ring_scope.
Notation "> y" := (lt y) : ring_scope.
Notation "> y :> T" := (> (y : T)) : ring_scope.

Notation "<= y" := (ge y) : ring_scope.
Notation "<= y :> T" := (<= (y : T)) : ring_scope.
Notation ">= y"  := (le y) : ring_scope.
Notation ">= y :> T" := (>= (y : T)) : ring_scope.

Notation "x < y"  := (lt x y) : ring_scope.
Notation "x < y :> T" := ((x : T) < (y : T)) : ring_scope.
Notation "x > y"  := (y < x) (only parsing) : ring_scope.
Notation "x > y :> T" := ((x : T) > (y : T)) (only parsing) : ring_scope.

Notation "x <= y" := (le x y) : ring_scope.
Notation "x <= y :> T" := ((x : T) <= (y : T)) : ring_scope.
Notation "x >= y" := (y <= x) (only parsing) : ring_scope.
Notation "x >= y :> T" := ((x : T) >= (y : T)) (only parsing) : ring_scope.

Notation "x <= y <= z" := ((x <= y) && (y <= z)) : ring_scope.
Notation "x < y <= z" := ((x < y) && (y <= z)) : ring_scope.
Notation "x <= y < z" := ((x <= y) && (y < z)) : ring_scope.
Notation "x < y < z" := ((x < y) && (y < z)) : ring_scope.

Notation "x <= y ?= 'iff' C" := (lerif x y C) : ring_scope.
Notation "x <= y ?= 'iff' C :> R" := ((x : R) <= (y : R) ?= iff C)
  (only parsing) : ring_scope.

Coercion ler_of_leif : lerif >-> is_true.

Canonical Rpos_keyed.
Canonical Rneg_keyed.
Canonical Rnneg_keyed.
Canonical Rreal_keyed.

End Syntax.

Section ExtensionAxioms.

Variable R : numDomainType.

Definition real_axiom : Prop := forall x : R, x \is real.

Definition archimedean_axiom : Prop := forall x : R, exists ub, `|x| < ub%:R.

Definition real_closed_axiom : Prop :=
  forall (p : {poly R}) (a b : R),
    a <= b -> p.[a] <= 0 <= p.[b] -> exists2 x, a <= x <= b & root p x.

End ExtensionAxioms.

Local Notation num_for T b := (@NumDomain.Pack T b).

(* The rest of the numbers interface hierarchy. *)
Module NumField.

Section ClassDef.

Record class_of R :=
  Class { base : GRing.Field.class_of R; mixin : mixin_of (ring_for R base) }.
Definition base2 R (c : class_of R) := NumDomain.Class (mixin c).
Local Coercion base : class_of >-> GRing.Field.class_of.
Local Coercion base2 : class_of >-> NumDomain.class_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack :=
  fun bT b & phant_id (GRing.Field.class bT) (b : GRing.Field.class_of T) =>
  fun mT m & phant_id (NumDomain.class mT) (@NumDomain.Class T b m) =>
  Pack (@Class T b m).

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition zmodType := @GRing.Zmodule.Pack cT xclass.
Definition ringType := @GRing.Ring.Pack cT xclass.
Definition comRingType := @GRing.ComRing.Pack cT xclass.
Definition unitRingType := @GRing.UnitRing.Pack cT xclass.
Definition comUnitRingType := @GRing.ComUnitRing.Pack cT xclass.
Definition idomainType := @GRing.IntegralDomain.Pack cT xclass.
Definition numDomainType := @NumDomain.Pack cT xclass.
Definition fieldType := @GRing.Field.Pack cT xclass.
Definition join_numDomainType := @NumDomain.Pack fieldType xclass.

End ClassDef.

Module Exports.
Coercion base : class_of >-> GRing.Field.class_of.
Coercion base2 : class_of >-> NumDomain.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical comRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical unitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical comUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical idomainType.
Coercion numDomainType : type >-> NumDomain.type.
Canonical numDomainType.
Coercion fieldType : type >-> GRing.Field.type.
Canonical fieldType.
Notation numFieldType := type.
Notation "[ 'numFieldType' 'of' T ]" := (@pack T _ _ id _ _ id)
  (at level 0, format "[ 'numFieldType'  'of'  T ]") : form_scope.
End Exports.

End NumField.
Import NumField.Exports.

Module ClosedField.

Section ClassDef.

Record imaginary_mixin_of (R : numDomainType) := ImaginaryMixin {
  imaginary : R;
  conj_op : {rmorphism R -> R};
  _ : imaginary ^+ 2 = - 1;
  _ : forall x, x * conj_op x = `|x| ^+ 2;
}.

Record class_of R := Class {
  base : GRing.ClosedField.class_of R;
  mixin : mixin_of (ring_for R base);
  conj_mixin : imaginary_mixin_of (num_for R (NumDomain.Class mixin))
}.
Definition base2 R (c : class_of R) := NumField.Class (mixin c).
Local Coercion base : class_of >-> GRing.ClosedField.class_of.
Local Coercion base2 : class_of >-> NumField.class_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack :=
  fun bT b & phant_id (GRing.ClosedField.class bT)
                      (b : GRing.ClosedField.class_of T) =>
  fun mT m & phant_id (NumField.class mT) (@NumField.Class T b m) =>
  fun mc => Pack (@Class T b m mc).
Definition clone := fun b & phant_id class (b : class_of T) => Pack b.

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition zmodType := @GRing.Zmodule.Pack cT xclass.
Definition ringType := @GRing.Ring.Pack cT xclass.
Definition comRingType := @GRing.ComRing.Pack cT xclass.
Definition unitRingType := @GRing.UnitRing.Pack cT xclass.
Definition comUnitRingType := @GRing.ComUnitRing.Pack cT xclass.
Definition idomainType := @GRing.IntegralDomain.Pack cT xclass.
Definition numDomainType := @NumDomain.Pack cT xclass.
Definition fieldType := @GRing.Field.Pack cT xclass.
Definition numFieldType := @NumField.Pack cT xclass.
Definition decFieldType := @GRing.DecidableField.Pack cT xclass.
Definition closedFieldType := @GRing.ClosedField.Pack cT xclass.
Definition join_dec_numDomainType := @NumDomain.Pack decFieldType xclass.
Definition join_dec_numFieldType := @NumField.Pack decFieldType xclass.
Definition join_numDomainType := @NumDomain.Pack closedFieldType xclass.
Definition join_numFieldType := @NumField.Pack closedFieldType xclass.

End ClassDef.

Module Exports.
Coercion base : class_of >-> GRing.ClosedField.class_of.
Coercion base2 : class_of >-> NumField.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical comRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical unitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical comUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical idomainType.
Coercion numDomainType : type >-> NumDomain.type.
Canonical numDomainType.
Coercion fieldType : type >-> GRing.Field.type.
Canonical fieldType.
Coercion decFieldType : type >-> GRing.DecidableField.type.
Canonical decFieldType.
Coercion numFieldType : type >-> NumField.type.
Canonical numFieldType.
Coercion closedFieldType : type >-> GRing.ClosedField.type.
Canonical closedFieldType.
Canonical join_dec_numDomainType.
Canonical join_dec_numFieldType.
Canonical join_numDomainType.
Canonical join_numFieldType.
Notation numClosedFieldType := type.
Notation NumClosedFieldType T m := (@pack T _ _ id _ _ id m).
Notation "[ 'numClosedFieldType' 'of' T 'for' cT ]" := (@clone T cT _ id)
  (at level 0, format "[ 'numClosedFieldType'  'of'  T  'for' cT ]") :
                                                         form_scope.
Notation "[ 'numClosedFieldType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'numClosedFieldType'  'of'  T ]") : form_scope.
End Exports.

End ClosedField.
Import ClosedField.Exports.

Module RealDomain.

Section ClassDef.

Record class_of R :=
  Class {base : NumDomain.class_of R; _ : @real_axiom (num_for R base)}.
Local Coercion base : class_of >-> NumDomain.class_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition clone c of phant_id class c := @Pack T c.
Definition pack b0 (m0 : real_axiom (num_for T b0)) :=
  fun bT b & phant_id (NumDomain.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m).

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition zmodType := @GRing.Zmodule.Pack cT xclass.
Definition ringType := @GRing.Ring.Pack cT xclass.
Definition comRingType := @GRing.ComRing.Pack cT xclass.
Definition unitRingType := @GRing.UnitRing.Pack cT xclass.
Definition comUnitRingType := @GRing.ComUnitRing.Pack cT xclass.
Definition idomainType := @GRing.IntegralDomain.Pack cT xclass.
Definition numDomainType := @NumDomain.Pack cT xclass.

End ClassDef.

Module Exports.
Coercion base : class_of >-> NumDomain.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical comRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical unitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical comUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical idomainType.
Coercion numDomainType : type >-> NumDomain.type.
Canonical numDomainType.
Notation realDomainType := type.
Notation RealDomainType T m := (@pack T _ m _ _ id _ id).
Notation "[ 'realDomainType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'realDomainType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'realDomainType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'realDomainType'  'of'  T ]") : form_scope.
End Exports.

End RealDomain.
Import RealDomain.Exports.

Module RealField.

Section ClassDef.

Record class_of R :=
  Class { base : NumField.class_of R; mixin : real_axiom (num_for R base) }.
Definition base2 R (c : class_of R) := RealDomain.Class (@mixin R c).
Local Coercion base : class_of >-> NumField.class_of.
Local Coercion base2 : class_of >-> RealDomain.class_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack :=
  fun bT b & phant_id (NumField.class bT) (b : NumField.class_of T) =>
  fun mT m & phant_id (RealDomain.class mT) (@RealDomain.Class T b m) =>
  Pack (@Class T b m).

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition zmodType := @GRing.Zmodule.Pack cT xclass.
Definition ringType := @GRing.Ring.Pack cT xclass.
Definition comRingType := @GRing.ComRing.Pack cT xclass.
Definition unitRingType := @GRing.UnitRing.Pack cT xclass.
Definition comUnitRingType := @GRing.ComUnitRing.Pack cT xclass.
Definition idomainType := @GRing.IntegralDomain.Pack cT xclass.
Definition numDomainType := @NumDomain.Pack cT xclass.
Definition realDomainType := @RealDomain.Pack cT xclass.
Definition fieldType := @GRing.Field.Pack cT xclass.
Definition numFieldType := @NumField.Pack cT xclass.
Definition join_realDomainType := @RealDomain.Pack numFieldType xclass.

End ClassDef.

Module Exports.
Coercion base : class_of >-> NumField.class_of.
Coercion base2 : class_of >-> RealDomain.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical comRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical unitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical comUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical idomainType.
Coercion numDomainType : type >-> NumDomain.type.
Canonical numDomainType.
Coercion realDomainType : type >-> RealDomain.type.
Canonical realDomainType.
Coercion fieldType : type >-> GRing.Field.type.
Canonical fieldType.
Coercion numFieldType : type >-> NumField.type.
Canonical numFieldType.
Canonical join_realDomainType.
Notation realFieldType := type.
Notation "[ 'realFieldType' 'of' T ]" := (@pack T _ _ id _ _ id)
  (at level 0, format "[ 'realFieldType'  'of'  T ]") : form_scope.
End Exports.

End RealField.
Import RealField.Exports.

Module ArchimedeanField.

Section ClassDef.

Record class_of R :=
  Class { base : RealField.class_of R; _ : archimedean_axiom (num_for R base) }.
Local Coercion base : class_of >-> RealField.class_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition clone c of phant_id class c := @Pack T c.
Definition pack b0 (m0 : archimedean_axiom (num_for T b0)) :=
  fun bT b & phant_id (RealField.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m).

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition zmodType := @GRing.Zmodule.Pack cT xclass.
Definition ringType := @GRing.Ring.Pack cT xclass.
Definition comRingType := @GRing.ComRing.Pack cT xclass.
Definition unitRingType := @GRing.UnitRing.Pack cT xclass.
Definition comUnitRingType := @GRing.ComUnitRing.Pack cT xclass.
Definition idomainType := @GRing.IntegralDomain.Pack cT xclass.
Definition numDomainType := @NumDomain.Pack cT xclass.
Definition realDomainType := @RealDomain.Pack cT xclass.
Definition fieldType := @GRing.Field.Pack cT xclass.
Definition numFieldType := @NumField.Pack cT xclass.
Definition realFieldType := @RealField.Pack cT xclass.

End ClassDef.

Module Exports.
Coercion base : class_of >-> RealField.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical comRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical unitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical comUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical idomainType.
Coercion numDomainType : type >-> NumDomain.type.
Canonical numDomainType.
Coercion realDomainType : type >-> RealDomain.type.
Canonical realDomainType.
Coercion fieldType : type >-> GRing.Field.type.
Canonical fieldType.
Coercion numFieldType : type >-> NumField.type.
Canonical numFieldType.
Coercion realFieldType : type >-> RealField.type.
Canonical realFieldType.
Notation archiFieldType := type.
Notation ArchiFieldType T m := (@pack T _ m _ _ id _ id).
Notation "[ 'archiFieldType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'archiFieldType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'archiFieldType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'archiFieldType'  'of'  T ]") : form_scope.
End Exports.

End ArchimedeanField.
Import ArchimedeanField.Exports.

Module RealClosedField.

Section ClassDef.

Record class_of R :=
  Class { base : RealField.class_of R; _ : real_closed_axiom (num_for R base) }.
Local Coercion base : class_of >-> RealField.class_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition clone c of phant_id class c := @Pack T c.
Definition pack b0 (m0 : real_closed_axiom (num_for T b0)) :=
  fun bT b & phant_id (RealField.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m).

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition zmodType := @GRing.Zmodule.Pack cT xclass.
Definition ringType := @GRing.Ring.Pack cT xclass.
Definition comRingType := @GRing.ComRing.Pack cT xclass.
Definition unitRingType := @GRing.UnitRing.Pack cT xclass.
Definition comUnitRingType := @GRing.ComUnitRing.Pack cT xclass.
Definition idomainType := @GRing.IntegralDomain.Pack cT xclass.
Definition numDomainType := @NumDomain.Pack cT xclass.
Definition realDomainType := @RealDomain.Pack cT xclass.
Definition fieldType := @GRing.Field.Pack cT xclass.
Definition numFieldType := @NumField.Pack cT xclass.
Definition realFieldType := @RealField.Pack cT xclass.

End ClassDef.

Module Exports.
Coercion base : class_of >-> RealField.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical comRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical unitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical comUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical idomainType.
Coercion numDomainType : type >-> NumDomain.type.
Canonical numDomainType.
Coercion realDomainType : type >-> RealDomain.type.
Canonical realDomainType.
Coercion fieldType : type >-> GRing.Field.type.
Canonical fieldType.
Coercion numFieldType : type >-> NumField.type.
Canonical numFieldType.
Coercion realFieldType : type >-> RealField.type.
Canonical realFieldType.
Notation rcfType := Num.RealClosedField.type.
Notation RcfType T m := (@pack T _ m _ _ id _ id).
Notation "[ 'rcfType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'rcfType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'rcfType' 'of' T ]" :=  (@clone T _ _ id)
  (at level 0, format "[ 'rcfType'  'of'  T ]") : form_scope.
End Exports.

End RealClosedField.
Import RealClosedField.Exports.

(* The elementary theory needed to support the definition of the derived      *)
(* operations for the extensions described above.                             *)
Module Import Internals.

Section Domain.
Variable R : numDomainType.
Implicit Types x y : R.

(* Lemmas from the signature *)

Lemma normr0_eq0 x : `|x| = 0 -> x = 0.
Proof. by case: R x => ? [? []]. Qed.

Lemma ler_norm_add x y : `|x + y| <= `|x| + `|y|.
Proof. by case: R x y => ? [? []]. Qed.

Lemma addr_gt0 x y : 0 < x -> 0 < y -> 0 < x + y.
Proof. by case: R x y => ? [? []]. Qed.

Lemma ger_leVge x y : 0 <= x -> 0 <= y -> (x <= y) || (y <= x).
Proof. by case: R x y => ? [? []]. Qed.

Lemma normrM : {morph norm : x y / x * y : R}.
Proof. by case: R => ? [? []]. Qed.

Lemma ler_def x y : (x <= y) = (`|y - x| == y - x).
Proof. by case: R x y => ? [? []]. Qed.

Lemma ltr_def x y : (x < y) = (y != x) && (x <= y).
Proof. by case: R x y => ? [? []]. Qed.

(* Basic consequences (just enough to get predicate closure properties). *)

Lemma ger0_def x : (0 <= x) = (`|x| == x).
Proof. by rewrite ler_def subr0. Qed.

Lemma subr_ge0 x y : (0 <= x - y) = (y <= x).
Proof. by rewrite ger0_def -ler_def. Qed.

Lemma oppr_ge0 x : (0 <= - x) = (x <= 0).
Proof. by rewrite -sub0r subr_ge0. Qed.

Lemma ler01 : 0 <= 1 :> R.
Proof.
have n1_nz: `|1| != 0 :> R by apply: contraNneq (@oner_neq0 R) => /normr0_eq0->.
by rewrite ger0_def -(inj_eq (mulfI n1_nz)) -normrM !mulr1.
Qed.

Lemma ltr01 : 0 < 1 :> R. Proof. by rewrite ltr_def oner_neq0 ler01. Qed.

Lemma ltrW x y : x < y -> x <= y. Proof. by rewrite ltr_def => /andP[]. Qed.

Lemma lerr x : x <= x.
Proof.
have n2: `|2%:R| == 2%:R :> R by rewrite -ger0_def ltrW ?addr_gt0 ?ltr01.
rewrite ler_def subrr -(inj_eq (addrI `|0|)) addr0 -mulr2n -mulr_natr.
by rewrite -(eqP n2) -normrM mul0r.
Qed.

Lemma le0r x : (0 <= x) = (x == 0) || (0 < x).
Proof. by rewrite ltr_def; case: eqP => // ->; rewrite lerr. Qed.

Lemma addr_ge0 x y : 0 <= x -> 0 <= y -> 0 <= x + y.
Proof.
rewrite le0r; case/predU1P=> [-> | x_pos]; rewrite ?add0r // le0r.
by case/predU1P=> [-> | y_pos]; rewrite ltrW ?addr0 ?addr_gt0.
Qed.

Lemma pmulr_rgt0 x y : 0 < x -> (0 < x * y) = (0 < y).
Proof.
rewrite !ltr_def !ger0_def normrM mulf_eq0 negb_or => /andP[x_neq0 /eqP->].
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
Canonical pos_mulrPred := MulrPred pos_divr_closed.
Canonical pos_divrPred := DivrPred pos_divr_closed.

Fact nneg_divr_closed : divr_closed (@nneg R).
Proof.
split=> [|x y]; rewrite !nnegrE ?ler01 ?le0r // -!posrE.
case/predU1P=> [-> _ | x_gt0]; first by rewrite mul0r eqxx.
by case/predU1P=> [-> | y_gt0]; rewrite ?invr0 ?mulr0 ?eqxx // orbC rpred_div.
Qed.
Canonical nneg_mulrPred := MulrPred nneg_divr_closed.
Canonical nneg_divrPred := DivrPred nneg_divr_closed.

Fact nneg_addr_closed : addr_closed (@nneg R).
Proof. by split; [apply: lerr | apply: addr_ge0]. Qed.
Canonical nneg_addrPred := AddrPred nneg_addr_closed.
Canonical nneg_semiringPred := SemiringPred nneg_divr_closed.

Fact real_oppr_closed : oppr_closed (@real R).
Proof. by move=> x; rewrite /= !realE oppr_ge0 orbC -!oppr_ge0 opprK. Qed.
Canonical real_opprPred := OpprPred real_oppr_closed.

Fact real_addr_closed : addr_closed (@real R).
Proof.
split=> [|x y Rx Ry]; first by rewrite realE lerr.
without loss{Rx} x_ge0: x y Ry / 0 <= x.
  case/orP: Rx => [? | x_le0]; first exact.
  by rewrite -rpredN opprD; apply; rewrite ?rpredN ?oppr_ge0.
case/orP: Ry => [y_ge0 | y_le0]; first by rewrite realE -nnegrE rpredD.
by rewrite realE -[y]opprK orbC -oppr_ge0 opprB !subr_ge0 ger_leVge ?oppr_ge0.
Qed.
Canonical real_addrPred := AddrPred real_addr_closed.
Canonical real_zmodPred := ZmodPred real_oppr_closed.

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
Canonical real_mulrPred := MulrPred real_divr_closed.
Canonical real_smulrPred := SmulrPred real_divr_closed.
Canonical real_divrPred := DivrPred real_divr_closed.
Canonical real_sdivrPred := SdivrPred real_divr_closed.
Canonical real_semiringPred := SemiringPred real_divr_closed.
Canonical real_subringPred := SubringPred real_divr_closed.
Canonical real_divringPred := DivringPred real_divr_closed.

End Domain.

Lemma num_real (R : realDomainType) (x : R) : x \is real.
Proof. by case: R x => T []. Qed.

Fact archi_bound_subproof (R : archiFieldType) : archimedean_axiom R.
Proof. by case: R => ? []. Qed.

Section RealClosed.
Variable R : rcfType.

Lemma poly_ivt : real_closed_axiom R. Proof. by case: R => ? []. Qed.

Fact sqrtr_subproof (x : R) :
  exists2 y,  0 <= y & if 0 <= x return bool then y ^+ 2 == x else y == 0.
Proof.
case x_ge0: (0 <= x); last by exists 0; rewrite ?lerr.
have le0x1: 0 <= x + 1 by rewrite -nnegrE rpredD ?rpred1.
have [|y /andP[y_ge0 _]] := @poly_ivt ('X^2 - x%:P) _ _ le0x1.
  rewrite !hornerE -subr_ge0 add0r opprK x_ge0 -expr2 sqrrD mulr1.
  by rewrite addrAC !addrA addrK -nnegrE !rpredD ?rpredX ?rpred1.
by rewrite rootE !hornerE subr_eq0; exists y.
Qed.

End RealClosed.

End Internals.

Module PredInstances.

Canonical pos_mulrPred.
Canonical pos_divrPred.

Canonical nneg_addrPred.
Canonical nneg_mulrPred.
Canonical nneg_divrPred.
Canonical nneg_semiringPred.

Canonical real_addrPred.
Canonical real_opprPred.
Canonical real_zmodPred.
Canonical real_mulrPred.
Canonical real_smulrPred.
Canonical real_divrPred.
Canonical real_sdivrPred.
Canonical real_semiringPred.
Canonical real_subringPred.
Canonical real_divringPred.

End PredInstances.

Module Import ExtraDef.

Definition archi_bound {R} x := sval (sigW (@archi_bound_subproof R x)).

Definition sqrtr {R} x := s2val (sig2W (@sqrtr_subproof R x)).

End ExtraDef.

Notation bound := archi_bound.
Notation sqrt := sqrtr.

Module Theory.

Section NumIntegralDomainTheory.

Variable R : numDomainType.
Implicit Types x y z t : R.

(* Lemmas from the signature (reexported from internals). *)

Definition ler_norm_add x y : `|x + y| <= `|x| + `|y| := ler_norm_add x y.
Definition addr_gt0 x y : 0 < x -> 0 < y -> 0 < x + y := @addr_gt0 R x y.
Definition normr0_eq0 x : `|x| = 0 -> x = 0 := @normr0_eq0 R x.
Definition ger_leVge x y : 0 <= x -> 0 <= y -> (x <= y) || (y <= x) :=
  @ger_leVge R x y.
Definition normrM : {morph normr : x y / x * y : R} := @normrM R.
Definition ler_def x y : (x <= y) = (`|y - x| == y - x) := @ler_def R x y.
Definition ltr_def x y : (x < y) = (y != x) && (x <= y) := @ltr_def R x y.

(* Predicate and relation definitions. *)

Lemma gerE x y : ge x y = (y <= x). Proof. by []. Qed.
Lemma gtrE x y : gt x y = (y < x). Proof. by []. Qed.
Lemma posrE x : (x \is pos) = (0 < x). Proof. by []. Qed.
Lemma negrE x : (x \is neg) = (x < 0). Proof. by []. Qed.
Lemma nnegrE x : (x \is nneg) = (0 <= x). Proof. by []. Qed.
Lemma realE x : (x \is real) = (0 <= x) || (x <= 0). Proof. by []. Qed.

(* General properties of <= and < *)

Lemma lerr x : x <= x. Proof. exact: lerr. Qed.
Lemma ltrr x : x < x = false. Proof. by rewrite ltr_def eqxx. Qed.
Lemma ltrW x y : x < y -> x <= y. Proof. exact: ltrW. Qed.
Hint Resolve lerr ltrr ltrW : core.

Lemma ltr_neqAle x y : (x < y) = (x != y) && (x <= y).
Proof. by rewrite ltr_def eq_sym. Qed.

Lemma ler_eqVlt x y : (x <= y) = (x == y) || (x < y).
Proof. by rewrite ltr_neqAle; case: eqP => // ->; rewrite lerr. Qed.

Lemma lt0r x : (0 < x) = (x != 0) && (0 <= x). Proof. by rewrite ltr_def. Qed.
Lemma le0r x : (0 <= x) = (x == 0) || (0 < x). Proof. exact: le0r. Qed.

Lemma lt0r_neq0 (x : R) : 0 < x  -> x != 0.
Proof. by rewrite lt0r; case/andP. Qed.

Lemma ltr0_neq0 (x : R) : x < 0  -> x != 0.
Proof. by rewrite ltr_neqAle; case/andP. Qed.

Lemma gtr_eqF x y : y < x -> x == y = false.
Proof. by rewrite ltr_def; case/andP; move/negPf=> ->. Qed.

Lemma ltr_eqF x y : x < y -> x == y = false.
Proof. by move=> hyx; rewrite eq_sym gtr_eqF. Qed.

Lemma pmulr_rgt0 x y : 0 < x -> (0 < x * y) = (0 < y).
Proof. exact: pmulr_rgt0. Qed.

Lemma pmulr_rge0 x y : 0 < x -> (0 <= x * y) = (0 <= y).
Proof.
by rewrite !le0r mulf_eq0; case: eqP => // [-> /negPf[] | _ /pmulr_rgt0->].
Qed.

(* Integer comparisons and characteristic 0. *)
Lemma ler01 : 0 <= 1 :> R. Proof. exact: ler01. Qed.
Lemma ltr01 : 0 < 1 :> R. Proof. exact: ltr01. Qed.
Lemma ler0n n : 0 <= n%:R :> R. Proof. by rewrite -nnegrE rpred_nat. Qed.
Hint Resolve ler01 ltr01 ler0n : core.
Lemma ltr0Sn n : 0 < n.+1%:R :> R.
Proof. by elim: n => // n; apply: addr_gt0. Qed.
Lemma ltr0n n : (0 < n%:R :> R) = (0 < n)%N.
Proof. by case: n => //= n; apply: ltr0Sn. Qed.
Hint Resolve ltr0Sn : core.

Lemma pnatr_eq0 n : (n%:R == 0 :> R) = (n == 0)%N.
Proof. by case: n => [|n]; rewrite ?mulr0n ?eqxx // gtr_eqF. Qed.

Lemma char_num : [char R] =i pred0.
Proof. by case=> // p /=; rewrite !inE pnatr_eq0 andbF. Qed.

(* Properties of the norm. *)

Lemma ger0_def x : (0 <= x) = (`|x| == x). Proof. exact: ger0_def. Qed.
Lemma normr_idP {x} : reflect (`|x| = x) (0 <= x).
Proof. by rewrite ger0_def; apply: eqP. Qed.
Lemma ger0_norm x : 0 <= x -> `|x| = x. Proof. exact: normr_idP. Qed.

Lemma normr0 : `|0| = 0 :> R. Proof. exact: ger0_norm. Qed.
Lemma normr1 : `|1| = 1 :> R. Proof. exact: ger0_norm. Qed.
Lemma normr_nat n : `|n%:R| = n%:R :> R. Proof. exact: ger0_norm. Qed.
Lemma normrMn x n : `|x *+ n| = `|x| *+ n.
Proof. by rewrite -mulr_natl normrM normr_nat mulr_natl. Qed.

Lemma normr_prod I r (P : pred I) (F : I -> R) :
  `|\prod_(i <- r | P i) F i| = \prod_(i <- r | P i) `|F i|.
Proof. exact: (big_morph norm normrM normr1). Qed.

Lemma normrX n x : `|x ^+ n| = `|x| ^+ n.
Proof. by rewrite -(card_ord n) -!prodr_const normr_prod. Qed.

Lemma normr_unit : {homo (@norm R) : x / x \is a GRing.unit}.
Proof.
move=> x /= /unitrP [y [yx xy]]; apply/unitrP; exists `|y|.
by rewrite -!normrM xy yx normr1.
Qed.

Lemma normrV : {in GRing.unit, {morph (@normr R) : x / x ^-1}}.
Proof.
move=> x ux; apply: (mulrI (normr_unit ux)).
by rewrite -normrM !divrr ?normr1 ?normr_unit.
Qed.

Lemma normr0P {x} : reflect (`|x| = 0) (x == 0).
Proof. by apply: (iffP eqP)=> [->|/normr0_eq0 //]; apply: normr0. Qed.

Definition normr_eq0 x := sameP (`|x| =P 0) normr0P.

Lemma normrN1 : `|-1| = 1 :> R.
Proof.
have: `|-1| ^+ 2 == 1 :> R by rewrite -normrX -signr_odd normr1.
rewrite sqrf_eq1 => /orP[/eqP //|]; rewrite -ger0_def le0r oppr_eq0 oner_eq0.
by move/(addr_gt0 ltr01); rewrite subrr ltrr.
Qed.

Lemma normrN x : `|- x| = `|x|.
Proof. by rewrite -mulN1r normrM normrN1 mul1r. Qed.

Lemma distrC x y : `|x - y| = `|y - x|.
Proof. by rewrite -opprB normrN. Qed.

Lemma ler0_def x : (x <= 0) = (`|x| == - x).
Proof. by rewrite ler_def sub0r normrN. Qed.

Lemma normr_id x : `|`|x| | = `|x|.
Proof.
have nz2: 2%:R != 0 :> R by rewrite pnatr_eq0.
apply: (mulfI nz2); rewrite -{1}normr_nat -normrM mulr_natl mulr2n ger0_norm //.
by rewrite -{2}normrN -normr0 -(subrr x) ler_norm_add.
Qed.

Lemma normr_ge0 x : 0 <= `|x|. Proof. by rewrite ger0_def normr_id. Qed.
Hint Resolve normr_ge0 : core.

Lemma ler0_norm x : x <= 0 -> `|x| = - x.
Proof. by move=> x_le0; rewrite -[r in _ = r]ger0_norm ?normrN ?oppr_ge0. Qed.

Definition gtr0_norm x (hx : 0 < x) := ger0_norm (ltrW hx).
Definition ltr0_norm x (hx : x < 0) := ler0_norm (ltrW hx).

(* Comparision to 0 of a difference *)

Lemma subr_ge0 x y : (0 <= y - x) = (x <= y). Proof. exact: subr_ge0. Qed.
Lemma subr_gt0 x y : (0 < y - x) = (x < y).
Proof. by rewrite !ltr_def subr_eq0 subr_ge0. Qed.
Lemma subr_le0  x y : (y - x <= 0) = (y <= x).
Proof. by rewrite -subr_ge0 opprB add0r subr_ge0. Qed.
Lemma subr_lt0  x y : (y - x < 0) = (y < x).
Proof. by rewrite -subr_gt0 opprB add0r subr_gt0. Qed.

Definition subr_lte0 := (subr_le0, subr_lt0).
Definition subr_gte0 := (subr_ge0, subr_gt0).
Definition subr_cp0 := (subr_lte0, subr_gte0).

(* Ordered ring properties. *)

Lemma ler_asym : antisymmetric (<=%R : rel R).
Proof.
move=> x y; rewrite !ler_def distrC -opprB -addr_eq0 => /andP[/eqP->].
by rewrite -mulr2n -mulr_natl mulf_eq0 subr_eq0 pnatr_eq0 => /eqP.
Qed.

Lemma eqr_le x y : (x == y) = (x <= y <= x).
Proof. by apply/eqP/idP=> [->|/ler_asym]; rewrite ?lerr. Qed.

Lemma ltr_trans : transitive (@ltr R).
Proof.
move=> y x z le_xy le_yz.
by rewrite -subr_gt0 -(subrK y z) -addrA addr_gt0 ?subr_gt0.
Qed.

Lemma ler_lt_trans y x z : x <= y -> y < z -> x < z.
Proof. by rewrite !ler_eqVlt => /orP[/eqP -> //|/ltr_trans]; apply. Qed.

Lemma ltr_le_trans y x z : x < y -> y <= z -> x < z.
Proof. by rewrite !ler_eqVlt => lxy /orP[/eqP <- //|/(ltr_trans lxy)]. Qed.

Lemma ler_trans : transitive (@ler R).
Proof.
move=> y x z; rewrite !ler_eqVlt => /orP [/eqP -> //|lxy].
by move=> /orP [/eqP <-|/(ltr_trans lxy) ->]; rewrite ?lxy orbT.
Qed.

Definition lter01 := (ler01, ltr01).
Definition lterr := (lerr, ltrr).

Lemma addr_ge0 x y : 0 <= x -> 0 <= y -> 0 <= x + y.
Proof. exact: addr_ge0. Qed.

Lemma lerifP x y C : reflect (x <= y ?= iff C) (if C then x == y else x < y).
Proof.
rewrite /lerif ler_eqVlt; apply: (iffP idP)=> [|[]].
  by case: C => [/eqP->|lxy]; rewrite ?eqxx // lxy ltr_eqF.
by move=> /orP[/eqP->|lxy] <-; rewrite ?eqxx // ltr_eqF.
Qed.

Lemma ltr_asym x y : x < y < x = false.
Proof. by apply/negP=> /andP [/ltr_trans hyx /hyx]; rewrite ltrr. Qed.

Lemma ler_anti : antisymmetric (@ler R).
Proof. by move=> x y; rewrite -eqr_le=> /eqP. Qed.

Lemma ltr_le_asym x y : x < y <= x = false.
Proof. by rewrite ltr_neqAle -andbA -eqr_le eq_sym; case: (_ == _). Qed.

Lemma ler_lt_asym x y : x <= y < x = false.
Proof. by rewrite andbC ltr_le_asym. Qed.

Definition lter_anti := (=^~ eqr_le, ltr_asym, ltr_le_asym, ler_lt_asym).

Lemma ltr_geF x y : x < y -> (y <= x = false).
Proof.
by move=> xy; apply: contraTF isT=> /(ltr_le_trans xy); rewrite ltrr.
Qed.

Lemma ler_gtF x y : x <= y -> (y < x = false).
Proof. by apply: contraTF=> /ltr_geF->. Qed.

Definition ltr_gtF x y hxy := ler_gtF (@ltrW x y hxy).

(* Norm and order properties. *)

Lemma normr_le0 x : (`|x| <= 0) = (x == 0).
Proof. by rewrite -normr_eq0 eqr_le normr_ge0 andbT. Qed.

Lemma normr_lt0 x : `|x| < 0 = false.
Proof. by rewrite ltr_neqAle normr_le0 normr_eq0 andNb. Qed.

Lemma normr_gt0 x : (`|x| > 0) = (x != 0).
Proof. by rewrite ltr_def normr_eq0 normr_ge0 andbT. Qed.

Definition normrE x := (normr_id, normr0, normr1, normrN1, normr_ge0, normr_eq0,
  normr_lt0, normr_le0, normr_gt0, normrN).

End NumIntegralDomainTheory.

Arguments ler01 {R}.
Arguments ltr01 {R}.
Arguments normr_idP {R x}.
Arguments normr0P {R x}.
Arguments lerifP {R x y C}.
Hint Resolve @ler01 @ltr01 lerr ltrr ltrW ltr_eqF ltr0Sn ler0n normr_ge0 : core.

Section NumIntegralDomainMonotonyTheory.

Variables R R' : numDomainType.
Implicit Types m n p : nat.
Implicit Types x y z : R.
Implicit Types u v w : R'.

(****************************************************************************)
(* This listing of "Let"s factor out the required premices for the          *)
(* subsequent lemmas, putting them in the context so that "done" solves the *)
(* goals quickly                                                            *)
(****************************************************************************)

Let leqnn := leqnn.
Let ltnE := ltn_neqAle.
Let ltrE := @ltr_neqAle R.
Let ltr'E := @ltr_neqAle R'.
Let gtnE (m n : nat) : (m > n)%N = (m != n) && (m >= n)%N.
Proof. by rewrite ltn_neqAle eq_sym. Qed.
Let gtrE (x y : R) : (x > y) = (x != y) && (x >= y).
Proof. by rewrite ltr_neqAle eq_sym. Qed.
Let gtr'E (x y : R') : (x > y) = (x != y) && (x >= y).
Proof. by rewrite ltr_neqAle eq_sym. Qed.
Let leq_anti : antisymmetric leq.
Proof. by move=> m n; rewrite -eqn_leq => /eqP. Qed.
Let geq_anti : antisymmetric geq.
Proof. by move=> m n; rewrite -eqn_leq => /eqP. Qed.
Let ler_antiR := @ler_anti R.
Let ler_antiR' := @ler_anti R'.
Let ger_antiR : antisymmetric (>=%R : rel R).
Proof. by move=> ??; rewrite andbC; apply: ler_anti. Qed.
Let ger_antiR' : antisymmetric (>=%R : rel R').
Proof. by move=> ??; rewrite andbC; apply: ler_anti. Qed.
Let leq_total := leq_total.
Let geq_total : total geq.
Proof. by move=> m n; apply: leq_total. Qed.

Section AcrossTypes.

Variable D D' : pred R.
Variable (f : R -> R').

Lemma ltrW_homo : {homo f : x y / x < y} -> {homo f : x y / x <= y}.
Proof. exact: homoW. Qed.

Lemma ltrW_nhomo : {homo f : x y /~ x < y} -> {homo f : x y /~ x <= y}.
Proof. exact: homoW. Qed.

Lemma inj_homo_ltr :
  injective f -> {homo f : x y / x <= y} -> {homo f : x y / x < y}.
Proof. exact: inj_homo. Qed.

Lemma inj_nhomo_ltr :
  injective f -> {homo f : x y /~ x <= y} -> {homo f : x y /~ x < y}.
Proof. exact: inj_homo. Qed.

Lemma incr_inj : {mono f : x y / x <= y} -> injective f.
Proof. exact: mono_inj. Qed.

Lemma decr_inj : {mono f : x y /~ x <= y} -> injective f.
Proof. exact: mono_inj. Qed.

Lemma lerW_mono : {mono f : x y / x <= y} -> {mono f : x y / x < y}.
Proof. exact: anti_mono. Qed.

Lemma lerW_nmono : {mono f : x y /~ x <= y} -> {mono f : x y /~ x < y}.
Proof. exact: anti_mono. Qed.

(* Monotony in D D' *)
Lemma ltrW_homo_in :
  {in D & D', {homo f : x y / x < y}} -> {in D & D', {homo f : x y / x <= y}}.
Proof. exact: homoW_in. Qed.

Lemma ltrW_nhomo_in :
  {in D & D', {homo f : x y /~ x < y}} -> {in D & D', {homo f : x y /~ x <= y}}.
Proof. exact: homoW_in. Qed.

Lemma inj_homo_ltr_in :
    {in D & D', injective f} ->  {in D & D', {homo f : x y / x <= y}} ->
  {in D & D', {homo f : x y / x < y}}.
Proof. exact: inj_homo_in. Qed.

Lemma inj_nhomo_ltr_in :
    {in D & D', injective f} -> {in D & D', {homo f : x y /~ x <= y}} ->
  {in D & D', {homo f : x y /~ x < y}}.
Proof. exact: inj_homo_in. Qed.

Lemma incr_inj_in : {in D &, {mono f : x y / x <= y}} ->
   {in D &, injective f}.
Proof. exact: mono_inj_in. Qed.

Lemma decr_inj_in :
  {in D &, {mono f : x y /~ x <= y}} -> {in D &, injective f}.
Proof. exact: mono_inj_in. Qed.

Lemma lerW_mono_in :
  {in D &, {mono f : x y / x <= y}} -> {in D &, {mono f : x y / x < y}}.
Proof. exact: anti_mono_in. Qed.

Lemma lerW_nmono_in :
  {in D &, {mono f : x y /~ x <= y}} -> {in D &, {mono f : x y /~ x < y}}.
Proof. exact: anti_mono_in. Qed.

End AcrossTypes.

Section NatToR.

Variable D D' : pred nat.
Variable (f : nat -> R).

Lemma ltnrW_homo : {homo f : m n / (m < n)%N >-> m < n} ->
  {homo f : m n / (m <= n)%N >-> m <= n}.
Proof. exact: homoW. Qed.

Lemma ltnrW_nhomo : {homo f : m n / (n < m)%N >-> m < n} ->
  {homo f : m n / (n <= m)%N >-> m <= n}.
Proof. exact: homoW. Qed.

Lemma inj_homo_ltnr : injective f ->
  {homo f : m n / (m <= n)%N >-> m <= n} ->
  {homo f : m n / (m < n)%N >-> m < n}.
Proof. exact: inj_homo. Qed.

Lemma inj_nhomo_ltnr : injective f ->
  {homo f : m n / (n <= m)%N >-> m <= n} ->
  {homo f : m n / (n < m)%N >-> m < n}.
Proof. exact: inj_homo. Qed.

Lemma incnr_inj : {mono f : m n / (m <= n)%N >-> m <= n} -> injective f.
Proof. exact: mono_inj. Qed.

Lemma decnr_inj_inj : {mono f : m n / (n <= m)%N >-> m <= n} -> injective f.
Proof. exact: mono_inj. Qed.

Lemma lenrW_mono : {mono f : m n / (m <= n)%N >-> m <= n} ->
  {mono f : m n / (m < n)%N >-> m < n}.
Proof. exact: anti_mono. Qed.

Lemma lenrW_nmono : {mono f : m n / (n <= m)%N >-> m <= n} ->
  {mono f : m n / (n < m)%N >-> m < n}.
Proof. exact: anti_mono. Qed.

Lemma lenr_mono : {homo f : m n / (m < n)%N >-> m < n} ->
   {mono f : m n / (m <= n)%N >-> m <= n}.
Proof. exact: total_homo_mono. Qed.

Lemma lenr_nmono : {homo f : m n / (n < m)%N >-> m < n} ->
  {mono f : m n / (n <= m)%N >-> m <= n}.
Proof. exact: total_homo_mono. Qed.

Lemma ltnrW_homo_in : {in D & D', {homo f : m n / (m < n)%N >-> m < n}} ->
  {in D & D', {homo f : m n / (m <= n)%N >-> m <= n}}.
Proof. exact: homoW_in. Qed.

Lemma ltnrW_nhomo_in : {in D & D', {homo f : m n / (n < m)%N >-> m < n}} ->
  {in D & D', {homo f : m n / (n <= m)%N >-> m <= n}}.
Proof. exact: homoW_in. Qed.

Lemma inj_homo_ltnr_in : {in D & D', injective f} ->
  {in D & D', {homo f : m n / (m <= n)%N >-> m <= n}} ->
  {in D & D', {homo f : m n / (m < n)%N >-> m < n}}.
Proof. exact: inj_homo_in. Qed.

Lemma inj_nhomo_ltnr_in : {in D & D', injective f} ->
  {in D & D', {homo f : m n / (n <= m)%N >-> m <= n}} ->
  {in D & D', {homo f : m n / (n < m)%N >-> m < n}}.
Proof. exact: inj_homo_in. Qed.

Lemma incnr_inj_in : {in D &, {mono f : m n / (m <= n)%N >-> m <= n}} ->
  {in D &, injective f}.
Proof. exact: mono_inj_in. Qed.

Lemma decnr_inj_inj_in : {in D &, {mono f : m n / (n <= m)%N >-> m <= n}} ->
  {in D &, injective f}.
Proof. exact: mono_inj_in. Qed.

Lemma lenrW_mono_in : {in D &, {mono f : m n / (m <= n)%N >-> m <= n}} ->
  {in D &, {mono f : m n / (m < n)%N >-> m < n}}.
Proof. exact: anti_mono_in. Qed.

Lemma lenrW_nmono_in : {in D &, {mono f : m n / (n <= m)%N >-> m <= n}} ->
  {in D &, {mono f : m n / (n < m)%N >-> m < n}}.
Proof. exact: anti_mono_in. Qed.

Lemma lenr_mono_in : {in D &, {homo f : m n / (m < n)%N >-> m < n}} ->
   {in D &, {mono f : m n / (m <= n)%N >-> m <= n}}.
Proof. exact: total_homo_mono_in. Qed.

Lemma lenr_nmono_in : {in D &, {homo f : m n / (n < m)%N >-> m < n}} ->
  {in D &, {mono f : m n / (n <= m)%N >-> m <= n}}.
Proof. exact: total_homo_mono_in. Qed.

End NatToR.

Section RToNat.

Variable D D' : pred R.
Variable (f : R -> nat).

Lemma ltrnW_homo : {homo f : m n / m < n >-> (m < n)%N} ->
  {homo f : m n / m <= n >-> (m <= n)%N}.
Proof. exact: homoW. Qed.

Lemma ltrnW_nhomo : {homo f : m n / n < m >-> (m < n)%N} ->
  {homo f : m n / n <= m >-> (m <= n)%N}.
Proof. exact: homoW. Qed.

Lemma inj_homo_ltrn : injective f ->
  {homo f : m n / m <= n >-> (m <= n)%N} ->
  {homo f : m n / m < n >-> (m < n)%N}.
Proof. exact: inj_homo. Qed.

Lemma inj_nhomo_ltrn : injective f ->
  {homo f : m n / n <= m >-> (m <= n)%N} ->
  {homo f : m n / n < m >-> (m < n)%N}.
Proof. exact: inj_homo. Qed.

Lemma incrn_inj : {mono f : m n / m <= n >-> (m <= n)%N} -> injective f.
Proof. exact: mono_inj. Qed.

Lemma decrn_inj : {mono f : m n / n <= m >-> (m <= n)%N} -> injective f.
Proof. exact: mono_inj. Qed.

Lemma lernW_mono : {mono f : m n / m <= n >-> (m <= n)%N} ->
  {mono f : m n / m < n >-> (m < n)%N}.
Proof. exact: anti_mono. Qed.

Lemma lernW_nmono : {mono f : m n / n <= m >-> (m <= n)%N} ->
  {mono f : m n / n < m >-> (m < n)%N}.
Proof. exact: anti_mono. Qed.

Lemma ltrnW_homo_in : {in D & D', {homo f : m n / m < n >-> (m < n)%N}} ->
  {in D & D', {homo f : m n / m <= n >-> (m <= n)%N}}.
Proof. exact: homoW_in. Qed.

Lemma ltrnW_nhomo_in : {in D & D', {homo f : m n / n < m >-> (m < n)%N}} ->
  {in D & D', {homo f : m n / n <= m >-> (m <= n)%N}}.
Proof. exact: homoW_in. Qed.

Lemma inj_homo_ltrn_in : {in D & D', injective f} ->
  {in D & D', {homo f : m n / m <= n >-> (m <= n)%N}} ->
  {in D & D', {homo f : m n / m < n >-> (m < n)%N}}.
Proof. exact: inj_homo_in. Qed.

Lemma inj_nhomo_ltrn_in : {in D & D', injective f} ->
  {in D & D', {homo f : m n / n <= m >-> (m <= n)%N}} ->
  {in D & D', {homo f : m n / n < m >-> (m < n)%N}}.
Proof. exact: inj_homo_in. Qed.

Lemma incrn_inj_in : {in D &, {mono f : m n / m <= n >-> (m <= n)%N}} ->
  {in D &, injective f}.
Proof. exact: mono_inj_in. Qed.

Lemma decrn_inj_in : {in D &, {mono f : m n / n <= m >-> (m <= n)%N}} ->
  {in D &, injective f}.
Proof. exact: mono_inj_in. Qed.

Lemma lernW_mono_in : {in D &, {mono f : m n / m <= n >-> (m <= n)%N}} ->
  {in D &, {mono f : m n / m < n >-> (m < n)%N}}.
Proof. exact: anti_mono_in. Qed.

Lemma lernW_nmono_in : {in D &, {mono f : m n / n <= m >-> (m <= n)%N}} ->
  {in D &, {mono f : m n / n < m >-> (m < n)%N}}.
Proof. exact: anti_mono_in. Qed.

End RToNat.

End NumIntegralDomainMonotonyTheory.

Section NumDomainOperationTheory.

Variable R : numDomainType.
Implicit Types x y z t : R.

(* Comparision and opposite. *)

Lemma ler_opp2 : {mono -%R : x y /~ x <= y :> R}.
Proof. by move=> x y /=; rewrite -subr_ge0 opprK addrC subr_ge0. Qed.
Hint Resolve ler_opp2 : core.
Lemma ltr_opp2 : {mono -%R : x y /~ x < y :> R}.
Proof. by move=> x y /=; rewrite lerW_nmono. Qed.
Hint Resolve ltr_opp2 : core.
Definition lter_opp2 := (ler_opp2, ltr_opp2).

Lemma ler_oppr x y : (x <= - y) = (y <= - x).
Proof. by rewrite (monoRL opprK ler_opp2). Qed.

Lemma ltr_oppr x y : (x < - y) = (y < - x).
Proof. by rewrite (monoRL opprK (lerW_nmono _)). Qed.

Definition lter_oppr := (ler_oppr, ltr_oppr).

Lemma ler_oppl x y : (- x <= y) = (- y <= x).
Proof. by rewrite (monoLR opprK ler_opp2). Qed.

Lemma ltr_oppl x y : (- x < y) = (- y < x).
Proof. by rewrite (monoLR opprK (lerW_nmono _)). Qed.

Definition lter_oppl := (ler_oppl, ltr_oppl).

Lemma oppr_ge0 x : (0 <= - x) = (x <= 0).
Proof. by rewrite lter_oppr oppr0. Qed.

Lemma oppr_gt0 x : (0 < - x) = (x < 0).
Proof. by rewrite lter_oppr oppr0. Qed.

Definition oppr_gte0 := (oppr_ge0, oppr_gt0).

Lemma oppr_le0 x : (- x <= 0) = (0 <= x).
Proof. by rewrite lter_oppl oppr0. Qed.

Lemma oppr_lt0 x : (- x < 0) = (0 < x).
Proof. by rewrite lter_oppl oppr0. Qed.

Definition oppr_lte0 := (oppr_le0, oppr_lt0).
Definition oppr_cp0 := (oppr_gte0, oppr_lte0).
Definition lter_oppE := (oppr_cp0, lter_opp2).

Lemma ge0_cp x : 0 <= x -> (- x <= 0) * (- x <= x).
Proof. by move=> hx; rewrite oppr_cp0 hx (@ler_trans _ 0) ?oppr_cp0. Qed.

Lemma gt0_cp x : 0 < x ->
  (0 <= x) * (- x <= 0) * (- x <= x) * (- x < 0) * (- x < x).
Proof.
move=> hx; move: (ltrW hx) => hx'; rewrite !ge0_cp hx' //.
by rewrite oppr_cp0 hx // (@ltr_trans _ 0) ?oppr_cp0.
Qed.

Lemma le0_cp x : x <= 0 -> (0 <= - x) * (x <= - x).
Proof. by move=> hx; rewrite oppr_cp0 hx (@ler_trans _ 0) ?oppr_cp0. Qed.

Lemma lt0_cp x :
  x < 0 -> (x <= 0) * (0 <= - x) * (x <= - x) * (0 < - x) * (x < - x).
Proof.
move=> hx; move: (ltrW hx) => hx'; rewrite !le0_cp // hx'.
by rewrite oppr_cp0 hx // (@ltr_trans _ 0) ?oppr_cp0.
Qed.

(* Properties of the real subset. *)

Lemma ger0_real x : 0 <= x -> x \is real.
Proof. by rewrite realE => ->. Qed.

Lemma ler0_real x : x <= 0 -> x \is real.
Proof. by rewrite realE orbC => ->. Qed.

Lemma gtr0_real x : 0 < x -> x \is real.
Proof. by move=> /ltrW/ger0_real. Qed.

Lemma ltr0_real x : x < 0 -> x \is real.
Proof. by move=> /ltrW/ler0_real. Qed.

Lemma real0 : 0 \is @real R. Proof. by rewrite ger0_real. Qed.
Hint Resolve real0 : core.

Lemma real1 : 1 \is @real R. Proof. by rewrite ger0_real. Qed.
Hint Resolve real1 : core.

Lemma realn n : n%:R \is @real R. Proof. by rewrite ger0_real. Qed.

Lemma ler_leVge x y : x <= 0 -> y <= 0 -> (x <= y) || (y <= x).
Proof. by rewrite -!oppr_ge0 => /(ger_leVge _) h /h; rewrite !ler_opp2. Qed.

Lemma real_leVge x y : x \is real -> y \is real -> (x <= y) || (y <= x).
Proof.
rewrite !realE; have [x_ge0 _|x_nge0 /= x_le0] := boolP (_ <= _); last first.
  by have [/(ler_trans x_le0)->|_ /(ler_leVge x_le0) //] := boolP (0 <= _).
by have [/(ger_leVge x_ge0)|_ /ler_trans->] := boolP (0 <= _); rewrite ?orbT.
Qed.

Lemma realB : {in real &, forall x y, x - y \is real}.
Proof. exact: rpredB. Qed.

Lemma realN : {mono (@GRing.opp R) : x /  x \is real}.
Proof. exact: rpredN. Qed.

(* :TODO: add a rpredBC in ssralg *)
Lemma realBC x y : (x - y \is real) = (y - x \is real).
Proof. by rewrite -realN opprB. Qed.

Lemma realD : {in real &, forall x y, x + y \is real}.
Proof. exact: rpredD. Qed.

(* dichotomy and trichotomy *)

Variant ler_xor_gt (x y : R) : R -> R -> bool -> bool -> Set :=
  | LerNotGt of x <= y : ler_xor_gt x y (y - x) (y - x) true false
  | GtrNotLe of y < x  : ler_xor_gt x y (x - y) (x - y) false true.

Variant ltr_xor_ge (x y : R) : R -> R -> bool -> bool -> Set :=
  | LtrNotGe of x < y  : ltr_xor_ge x y (y - x) (y - x) false true
  | GerNotLt of y <= x : ltr_xor_ge x y (x - y) (x - y) true false.

Variant comparer x y : R -> R ->
  bool -> bool -> bool -> bool -> bool -> bool -> Set :=
  | ComparerLt of x < y : comparer x y (y - x) (y - x)
    false false true false true false
  | ComparerGt of x > y : comparer x y (x - y) (x - y)
    false false false true false true
  | ComparerEq of x = y : comparer x y 0 0
    true true true true false false.

Lemma real_lerP x y :
    x \is real -> y \is real ->
  ler_xor_gt x y `|x - y| `|y - x| (x <= y) (y < x).
Proof.
move=> xR /(real_leVge xR); have [le_xy _|Nle_xy /= le_yx] := boolP (_ <= _).
  have [/(ler_lt_trans le_xy)|] := boolP (_ < _); first by rewrite ltrr.
  by rewrite ler0_norm ?ger0_norm ?subr_cp0 ?opprB //; constructor.
have [lt_yx|] := boolP (_ < _).
  by rewrite ger0_norm ?ler0_norm ?subr_cp0 ?opprB //; constructor.
by rewrite ltr_def le_yx andbT negbK=> /eqP exy; rewrite exy lerr in Nle_xy.
Qed.

Lemma real_ltrP x y :
    x \is real -> y \is real ->
  ltr_xor_ge x y `|x - y| `|y - x| (y <= x) (x < y).
Proof. by move=> xR yR; case: real_lerP=> //; constructor. Qed.

Lemma real_ltrNge : {in real &, forall x y, (x < y) = ~~ (y <= x)}.
Proof. by move=> x y xR yR /=; case: real_lerP. Qed.

Lemma real_lerNgt : {in real &, forall x y, (x <= y) = ~~ (y < x)}.
Proof. by move=> x y xR yR /=; case: real_lerP. Qed.

Lemma real_ltrgtP x y :
    x \is real -> y \is real ->
  comparer x y `|x - y| `|y - x|
                (y == x) (x == y) (x <= y) (y <= x) (x < y) (x > y).
Proof.
move=> xR yR; case: real_lerP => // [le_yx|lt_xy]; last first.
  by rewrite gtr_eqF // ltr_eqF // ler_gtF ?ltrW //; constructor.
case: real_lerP => // [le_xy|lt_yx]; last first.
  by rewrite ltr_eqF // gtr_eqF //; constructor.
have /eqP ->: x == y by rewrite eqr_le le_yx le_xy.
by rewrite subrr eqxx; constructor.
Qed.

Variant ger0_xor_lt0 (x : R) : R -> bool -> bool -> Set :=
  | Ger0NotLt0 of 0 <= x : ger0_xor_lt0 x x false true
  | Ltr0NotGe0 of x < 0  : ger0_xor_lt0 x (- x) true false.

Variant ler0_xor_gt0 (x : R) : R -> bool -> bool -> Set :=
  | Ler0NotLe0 of x <= 0 : ler0_xor_gt0 x (- x) false true
  | Gtr0NotGt0 of 0 < x  : ler0_xor_gt0 x x true false.

Variant comparer0 x :
               R -> bool -> bool -> bool -> bool -> bool -> bool -> Set :=
  | ComparerGt0 of 0 < x : comparer0 x x false false false true false true
  | ComparerLt0 of x < 0 : comparer0 x (- x) false false true false true false
  | ComparerEq0 of x = 0 : comparer0 x 0 true true true true false false.

Lemma real_ger0P x : x \is real -> ger0_xor_lt0 x `|x| (x < 0) (0 <= x).
Proof.
move=> hx; rewrite -{2}[x]subr0; case: real_ltrP;
by rewrite ?subr0 ?sub0r //; constructor.
Qed.

Lemma real_ler0P x : x \is real -> ler0_xor_gt0 x `|x| (0 < x) (x <= 0).
Proof.
move=> hx; rewrite -{2}[x]subr0; case: real_ltrP;
by rewrite ?subr0 ?sub0r //; constructor.
Qed.

Lemma real_ltrgt0P x :
     x \is real ->
  comparer0 x `|x| (0 == x) (x == 0) (x <= 0) (0 <= x) (x < 0) (x > 0).
Proof.
move=> hx; rewrite -{2}[x]subr0; case: real_ltrgtP;
by rewrite ?subr0 ?sub0r //; constructor.
Qed.

Lemma real_neqr_lt : {in real &, forall x y, (x != y) = (x < y) || (y < x)}.
Proof. by move=> * /=; case: real_ltrgtP. Qed.

Lemma ler_sub_real x y : x <= y -> y - x \is real.
Proof. by move=> le_xy; rewrite ger0_real // subr_ge0. Qed.

Lemma ger_sub_real x y : x <= y -> x - y \is real.
Proof. by move=> le_xy; rewrite ler0_real // subr_le0. Qed.

Lemma ler_real y x : x <= y -> (x \is real) = (y \is real).
Proof. by move=> le_xy; rewrite -(addrNK x y) rpredDl ?ler_sub_real. Qed.

Lemma ger_real x y : y <= x -> (x \is real) = (y \is real).
Proof. by move=> le_yx; rewrite -(ler_real le_yx). Qed.

Lemma ger1_real x : 1 <= x -> x \is real. Proof. by move=> /ger_real->. Qed.
Lemma ler1_real x : x <= 1 -> x \is real. Proof. by move=> /ler_real->. Qed.

Lemma Nreal_leF x y : y \is real -> x \notin real -> (x <= y) = false.
Proof. by move=> yR; apply: contraNF=> /ler_real->. Qed.

Lemma Nreal_geF x y : y \is real -> x \notin real -> (y <= x) = false.
Proof. by move=> yR; apply: contraNF=> /ger_real->. Qed.

Lemma Nreal_ltF x y : y \is real -> x \notin real -> (x < y) = false.
Proof. by move=> yR xNR; rewrite ltr_def Nreal_leF ?andbF. Qed.

Lemma Nreal_gtF x y : y \is real -> x \notin real -> (y < x) = false.
Proof. by move=> yR xNR; rewrite ltr_def Nreal_geF ?andbF. Qed.

(* real wlog *)

Lemma real_wlog_ler P :
    (forall a b, P b a -> P a b) -> (forall a b, a <= b -> P a b) ->
  forall a b : R, a \is real -> b \is real -> P a b.
Proof.
move=> sP hP a b ha hb; wlog: a b ha hb / a <= b => [hwlog|]; last exact: hP.
by case: (real_lerP ha hb)=> [/hP //|/ltrW hba]; apply: sP; apply: hP.
Qed.

Lemma real_wlog_ltr P :
    (forall a, P a a) -> (forall a b, (P b a -> P a b)) ->
    (forall a b, a < b -> P a b) ->
  forall a b : R, a \is real -> b \is real -> P a b.
Proof.
move=> rP sP hP; apply: real_wlog_ler=> // a b.
by rewrite ler_eqVlt; case: (altP (_ =P _))=> [->|] //= _ lab; apply: hP.
Qed.

(* Monotony of addition *)
Lemma ler_add2l x : {mono +%R x : y z / y <= z}.
Proof.
by move=> y z /=; rewrite -subr_ge0 opprD addrAC addNKr addrC subr_ge0.
Qed.

Lemma ler_add2r x : {mono +%R^~ x : y z / y <= z}.
Proof. by move=> y z /=; rewrite ![_ + x]addrC ler_add2l. Qed.

Lemma ltr_add2l x : {mono +%R x : y z / y < z}.
Proof. by move=> y z /=; rewrite (lerW_mono (ler_add2l _)). Qed.

Lemma ltr_add2r x : {mono +%R^~ x : y z / y < z}.
Proof. by move=> y z /=; rewrite (lerW_mono (ler_add2r _)). Qed.

Definition ler_add2 := (ler_add2l, ler_add2r).
Definition ltr_add2 := (ltr_add2l, ltr_add2r).
Definition lter_add2 := (ler_add2, ltr_add2).

(* Addition, subtraction and transitivity *)
Lemma ler_add x y z t : x <= y -> z <= t -> x + z <= y + t.
Proof. by move=> lxy lzt; rewrite (@ler_trans _ (y + z)) ?lter_add2. Qed.

Lemma ler_lt_add x y z t : x <= y -> z < t -> x + z < y + t.
Proof. by move=> lxy lzt; rewrite (@ler_lt_trans _ (y + z)) ?lter_add2. Qed.

Lemma ltr_le_add x y z t : x < y -> z <= t -> x + z < y + t.
Proof. by move=> lxy lzt; rewrite (@ltr_le_trans _ (y + z)) ?lter_add2. Qed.

Lemma ltr_add x y z t : x < y -> z < t -> x + z < y + t.
Proof. by move=> lxy lzt; rewrite ltr_le_add // ltrW. Qed.

Lemma ler_sub x y z t : x <= y -> t <= z -> x - z <= y - t.
Proof. by move=> lxy ltz; rewrite ler_add // lter_opp2. Qed.

Lemma ler_lt_sub x y z t : x <= y -> t < z -> x - z < y - t.
Proof. by move=> lxy lzt; rewrite ler_lt_add // lter_opp2. Qed.

Lemma ltr_le_sub x y z t : x < y -> t <= z -> x - z < y - t.
Proof. by move=> lxy lzt; rewrite ltr_le_add // lter_opp2. Qed.

Lemma ltr_sub x y z t : x < y -> t < z -> x - z < y - t.
Proof. by move=> lxy lzt; rewrite ltr_add // lter_opp2. Qed.

Lemma ler_subl_addr x y z : (x - y <= z) = (x <= z + y).
Proof. by rewrite (monoLR (addrK _) (ler_add2r _)). Qed.

Lemma ltr_subl_addr x y z : (x - y < z) = (x < z + y).
Proof. by rewrite (monoLR (addrK _) (ltr_add2r _)). Qed.

Lemma ler_subr_addr x y z : (x <= y - z) = (x + z <= y).
Proof. by rewrite (monoLR (addrNK _) (ler_add2r _)). Qed.

Lemma ltr_subr_addr x y z : (x < y - z) = (x + z < y).
Proof. by rewrite (monoLR (addrNK _) (ltr_add2r _)). Qed.

Definition ler_sub_addr := (ler_subl_addr, ler_subr_addr).
Definition ltr_sub_addr := (ltr_subl_addr, ltr_subr_addr).
Definition lter_sub_addr := (ler_sub_addr, ltr_sub_addr).

Lemma ler_subl_addl x y z : (x - y <= z) = (x <= y + z).
Proof. by rewrite lter_sub_addr addrC. Qed.

Lemma ltr_subl_addl x y z : (x - y < z) = (x < y + z).
Proof. by rewrite lter_sub_addr addrC. Qed.

Lemma ler_subr_addl x y z : (x <= y - z) = (z + x <= y).
Proof. by rewrite lter_sub_addr addrC. Qed.

Lemma ltr_subr_addl x y z : (x < y - z) = (z + x < y).
Proof. by rewrite lter_sub_addr addrC. Qed.

Definition ler_sub_addl := (ler_subl_addl, ler_subr_addl).
Definition ltr_sub_addl := (ltr_subl_addl, ltr_subr_addl).
Definition lter_sub_addl := (ler_sub_addl, ltr_sub_addl).

Lemma ler_addl x y : (x <= x + y) = (0 <= y).
Proof. by rewrite -{1}[x]addr0 lter_add2. Qed.

Lemma ltr_addl x y : (x < x + y) = (0 < y).
Proof. by rewrite -{1}[x]addr0 lter_add2. Qed.

Lemma ler_addr x y : (x <= y + x) = (0 <= y).
Proof. by rewrite -{1}[x]add0r lter_add2. Qed.

Lemma ltr_addr x y : (x < y + x) = (0 < y).
Proof. by rewrite -{1}[x]add0r lter_add2. Qed.

Lemma ger_addl x y : (x + y <= x) = (y <= 0).
Proof. by rewrite -{2}[x]addr0 lter_add2. Qed.

Lemma gtr_addl x y : (x + y < x) = (y < 0).
Proof. by rewrite -{2}[x]addr0 lter_add2. Qed.

Lemma ger_addr x y : (y + x <= x) = (y <= 0).
Proof. by rewrite -{2}[x]add0r lter_add2. Qed.

Lemma gtr_addr x y : (y + x < x) = (y < 0).
Proof. by rewrite -{2}[x]add0r lter_add2. Qed.

Definition cpr_add := (ler_addl, ler_addr, ger_addl, ger_addl,
                       ltr_addl, ltr_addr, gtr_addl, gtr_addl).

(* Addition with left member knwon to be positive/negative *)
Lemma ler_paddl y x z : 0 <= x -> y <= z -> y <= x + z.
Proof. by move=> *; rewrite -[y]add0r ler_add. Qed.

Lemma ltr_paddl y x z : 0 <= x -> y < z -> y < x + z.
Proof. by move=> *; rewrite -[y]add0r ler_lt_add. Qed.

Lemma ltr_spaddl y x z : 0 < x -> y <= z -> y < x + z.
Proof. by move=> *; rewrite -[y]add0r ltr_le_add. Qed.

Lemma ltr_spsaddl y x z : 0 < x -> y < z -> y < x + z.
Proof. by move=> *; rewrite -[y]add0r ltr_add. Qed.

Lemma ler_naddl y x z : x <= 0 -> y <= z -> x + y <= z.
Proof. by move=> *; rewrite -[z]add0r ler_add. Qed.

Lemma ltr_naddl y x z : x <= 0 -> y < z -> x + y < z.
Proof. by move=> *; rewrite -[z]add0r ler_lt_add. Qed.

Lemma ltr_snaddl y x z : x < 0 -> y <= z -> x + y < z.
Proof. by move=> *; rewrite -[z]add0r ltr_le_add. Qed.

Lemma ltr_snsaddl y x z : x < 0 -> y < z -> x + y < z.
Proof. by move=> *; rewrite -[z]add0r ltr_add. Qed.

(* Addition with right member we know positive/negative *)
Lemma ler_paddr y x z : 0 <= x -> y <= z -> y <= z + x.
Proof. by move=> *; rewrite [_ + x]addrC ler_paddl. Qed.

Lemma ltr_paddr y x z : 0 <= x -> y < z -> y < z + x.
Proof. by move=> *; rewrite [_ + x]addrC ltr_paddl. Qed.

Lemma ltr_spaddr y x z : 0 < x -> y <= z -> y < z + x.
Proof. by move=> *; rewrite [_ + x]addrC ltr_spaddl. Qed.

Lemma ltr_spsaddr y x z : 0 < x -> y < z -> y < z + x.
Proof. by move=> *; rewrite [_ + x]addrC ltr_spsaddl. Qed.

Lemma ler_naddr y x z : x <= 0 -> y <= z -> y + x <= z.
Proof. by move=> *; rewrite [_ + x]addrC ler_naddl. Qed.

Lemma ltr_naddr y x z : x <= 0 -> y < z -> y + x < z.
Proof. by move=> *; rewrite [_ + x]addrC ltr_naddl. Qed.

Lemma ltr_snaddr y x z : x < 0 -> y <= z -> y + x < z.
Proof. by move=> *; rewrite [_ + x]addrC ltr_snaddl. Qed.

Lemma ltr_snsaddr y x z : x < 0 -> y < z -> y + x < z.
Proof. by move=> *; rewrite [_ + x]addrC ltr_snsaddl. Qed.

(* x and y have the same sign and their sum is null *)
Lemma paddr_eq0 (x y : R) :
  0 <= x -> 0 <= y -> (x + y == 0) = (x == 0) && (y == 0).
Proof.
rewrite le0r; case/orP=> [/eqP->|hx]; first by rewrite add0r eqxx.
by rewrite (gtr_eqF hx) /= => hy; rewrite gtr_eqF // ltr_spaddl.
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
Proof. exact: (big_ind _ _ (@ler_paddl 0)). Qed.

Lemma ler_sum I (r : seq I) (P : pred I) (F G : I -> R) :
    (forall i, P i -> F i <= G i) ->
  \sum_(i <- r | P i) F i <= \sum_(i <- r | P i) G i.
Proof. exact: (big_ind2 _ (lerr _) ler_add). Qed.

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

(* mulr and ler/ltr *)

Lemma ler_pmul2l x : 0 < x -> {mono *%R x : x y / x <= y}.
Proof.
by move=> x_gt0 y z /=; rewrite -subr_ge0 -mulrBr pmulr_rge0 // subr_ge0.
Qed.

Lemma ltr_pmul2l x : 0 < x -> {mono *%R x : x y / x < y}.
Proof. by move=> x_gt0; apply: lerW_mono (ler_pmul2l _). Qed.

Definition lter_pmul2l := (ler_pmul2l, ltr_pmul2l).

Lemma ler_pmul2r x : 0 < x -> {mono *%R^~ x : x y / x <= y}.
Proof. by move=> x_gt0 y z /=; rewrite ![_ * x]mulrC ler_pmul2l. Qed.

Lemma ltr_pmul2r x : 0 < x -> {mono *%R^~ x : x y / x < y}.
Proof. by move=> x_gt0; apply: lerW_mono (ler_pmul2r _). Qed.

Definition lter_pmul2r := (ler_pmul2r, ltr_pmul2r).

Lemma ler_nmul2l x : x < 0 -> {mono *%R x : x y /~ x <= y}.
Proof.
by move=> x_lt0 y z /=; rewrite -ler_opp2 -!mulNr ler_pmul2l ?oppr_gt0.
Qed.

Lemma ltr_nmul2l x : x < 0 -> {mono *%R x : x y /~ x < y}.
Proof. by move=> x_lt0; apply: lerW_nmono (ler_nmul2l _). Qed.

Definition lter_nmul2l := (ler_nmul2l, ltr_nmul2l).

Lemma ler_nmul2r x : x < 0 -> {mono *%R^~ x : x y /~ x <= y}.
Proof. by move=> x_lt0 y z /=; rewrite ![_ * x]mulrC ler_nmul2l. Qed.

Lemma ltr_nmul2r x : x < 0 -> {mono *%R^~ x : x y /~ x < y}.
Proof. by move=> x_lt0; apply: lerW_nmono (ler_nmul2r _). Qed.

Definition lter_nmul2r := (ler_nmul2r, ltr_nmul2r).

Lemma ler_wpmul2l x : 0 <= x -> {homo *%R x : y z / y <= z}.
Proof.
by rewrite le0r => /orP[/eqP-> y z | /ler_pmul2l/mono2W//]; rewrite !mul0r.
Qed.

Lemma ler_wpmul2r x : 0 <= x -> {homo *%R^~ x : y z / y <= z}.
Proof. by move=> x_ge0 y z leyz; rewrite ![_ * x]mulrC ler_wpmul2l. Qed.

Lemma ler_wnmul2l x : x <= 0 -> {homo *%R x : y z /~ y <= z}.
Proof.
by move=> x_le0 y z leyz; rewrite -![x * _]mulrNN ler_wpmul2l ?lter_oppE.
Qed.

Lemma ler_wnmul2r x : x <= 0 -> {homo *%R^~ x : y z /~ y <= z}.
Proof.
by move=> x_le0 y z leyz; rewrite -![_ * x]mulrNN ler_wpmul2r ?lter_oppE.
Qed.

(* Binary forms, for backchaining. *)

Lemma ler_pmul x1 y1 x2 y2 :
  0 <= x1 -> 0 <= x2 -> x1 <= y1 -> x2 <= y2 -> x1 * x2 <= y1 * y2.
Proof.
move=> x1ge0 x2ge0 le_xy1 le_xy2; have y1ge0 := ler_trans x1ge0 le_xy1.
exact: ler_trans (ler_wpmul2r x2ge0 le_xy1) (ler_wpmul2l y1ge0 le_xy2).
Qed.

Lemma ltr_pmul x1 y1 x2 y2 :
  0 <= x1 -> 0 <= x2 -> x1 < y1 -> x2 < y2 -> x1 * x2 < y1 * y2.
Proof.
move=> x1ge0 x2ge0 lt_xy1 lt_xy2; have y1gt0 := ler_lt_trans x1ge0 lt_xy1.
by rewrite (ler_lt_trans (ler_wpmul2r x2ge0 (ltrW lt_xy1))) ?ltr_pmul2l.
Qed.

(* complement for x *+ n and <= or < *)

Lemma ler_pmuln2r n : (0 < n)%N -> {mono (@GRing.natmul R)^~ n : x y / x <= y}.
Proof.
by case: n => // n _ x y /=; rewrite -mulr_natl -[y *+ _]mulr_natl ler_pmul2l.
Qed.

Lemma ltr_pmuln2r n : (0 < n)%N -> {mono (@GRing.natmul R)^~ n : x y / x < y}.
Proof. by move/ler_pmuln2r/lerW_mono. Qed.

Lemma pmulrnI n : (0 < n)%N -> injective ((@GRing.natmul R)^~ n).
Proof. by move/ler_pmuln2r/incr_inj. Qed.

Lemma eqr_pmuln2r n : (0 < n)%N -> {mono (@GRing.natmul R)^~ n : x y / x == y}.
Proof. by move/pmulrnI/inj_eq. Qed.

Lemma pmulrn_lgt0 x n : (0 < n)%N -> (0 < x *+ n) = (0 < x).
Proof. by move=> n_gt0; rewrite -(mul0rn _ n) ltr_pmuln2r // mul0rn. Qed.

Lemma pmulrn_llt0 x n : (0 < n)%N -> (x *+ n < 0) = (x < 0).
Proof. by move=> n_gt0; rewrite -(mul0rn _ n) ltr_pmuln2r // mul0rn. Qed.

Lemma pmulrn_lge0 x n : (0 < n)%N -> (0 <= x *+ n) = (0 <= x).
Proof. by move=> n_gt0; rewrite -(mul0rn _ n) ler_pmuln2r // mul0rn. Qed.

Lemma pmulrn_lle0 x n : (0 < n)%N -> (x *+ n <= 0) = (x <= 0).
Proof. by move=> n_gt0; rewrite -(mul0rn _ n) ler_pmuln2r // mul0rn. Qed.

Lemma ltr_wmuln2r x y n : x < y -> (x *+ n < y *+ n) = (0 < n)%N.
Proof. by move=> ltxy; case: n=> // n; rewrite ltr_pmuln2r. Qed.

Lemma ltr_wpmuln2r n : (0 < n)%N -> {homo (@GRing.natmul R)^~ n : x y / x < y}.
Proof. by move=> n_gt0 x y /= / ltr_wmuln2r ->. Qed.

Lemma ler_wmuln2r n : {homo (@GRing.natmul R)^~ n : x y / x <= y}.
Proof. by move=> x y hxy /=; case: n=> // n; rewrite ler_pmuln2r. Qed.

Lemma mulrn_wge0 x n : 0 <= x -> 0 <= x *+ n.
Proof. by move=> /(ler_wmuln2r n); rewrite mul0rn. Qed.

Lemma mulrn_wle0 x n : x <= 0 -> x *+ n <= 0.
Proof. by move=> /(ler_wmuln2r n); rewrite mul0rn. Qed.

Lemma ler_muln2r n x y : (x *+ n <= y *+ n) = ((n == 0%N) || (x <= y)).
Proof. by case: n => [|n]; rewrite ?lerr ?eqxx // ler_pmuln2r. Qed.

Lemma ltr_muln2r n x y : (x *+ n < y *+ n) = ((0 < n)%N && (x < y)).
Proof. by case: n => [|n]; rewrite ?lerr ?eqxx // ltr_pmuln2r. Qed.

Lemma eqr_muln2r n x y : (x *+ n == y *+ n) = (n == 0)%N || (x == y).
Proof. by rewrite !eqr_le !ler_muln2r -orb_andr. Qed.

(* More characteristic zero properties. *)

Lemma mulrn_eq0 x n : (x *+ n == 0) = ((n == 0)%N || (x == 0)).
Proof. by rewrite -mulr_natl mulf_eq0 pnatr_eq0. Qed.

Lemma mulrIn x : x != 0 -> injective (GRing.natmul x).
Proof.
move=> x_neq0 m n; without loss /subnK <-: m n / (n <= m)%N.
  by move=> IH eq_xmn; case/orP: (leq_total m n) => /IH->.
by move/eqP; rewrite mulrnDr -subr_eq0 addrK mulrn_eq0 => /predU1P[-> | /idPn].
Qed.

Lemma ler_wpmuln2l x :
  0 <= x -> {homo (@GRing.natmul R x) : m n / (m <= n)%N >-> m <= n}.
Proof. by move=> xge0 m n /subnK <-; rewrite mulrnDr ler_paddl ?mulrn_wge0. Qed.

Lemma ler_wnmuln2l x :
  x <= 0 -> {homo (@GRing.natmul R x) : m n / (n <= m)%N >-> m <= n}.
Proof.
by move=> xle0 m n hmn /=; rewrite -ler_opp2 -!mulNrn ler_wpmuln2l // oppr_cp0.
Qed.

Lemma mulrn_wgt0 x n : 0 < x -> 0 < x *+ n = (0 < n)%N.
Proof. by case: n => // n hx; rewrite pmulrn_lgt0. Qed.

Lemma mulrn_wlt0 x n : x < 0 -> x *+ n < 0 = (0 < n)%N.
Proof. by case: n => // n hx; rewrite pmulrn_llt0. Qed.

Lemma ler_pmuln2l x :
  0 < x -> {mono (@GRing.natmul R x) : m n / (m <= n)%N >-> m <= n}.
Proof.
move=> x_gt0 m n /=; case: leqP => hmn; first by rewrite ler_wpmuln2l // ltrW.
rewrite -(subnK (ltnW hmn)) mulrnDr ger_addr ltr_geF //.
by rewrite mulrn_wgt0 // subn_gt0.
Qed.

Lemma ltr_pmuln2l x :
  0 < x -> {mono (@GRing.natmul R x) : m n / (m < n)%N >-> m < n}.
Proof. by move=> x_gt0; apply: lenrW_mono (ler_pmuln2l _). Qed.

Lemma ler_nmuln2l x :
  x < 0 -> {mono (@GRing.natmul R x) : m n / (n <= m)%N >-> m <= n}.
Proof.
by move=> x_lt0 m n /=; rewrite -ler_opp2 -!mulNrn ler_pmuln2l // oppr_gt0.
Qed.

Lemma ltr_nmuln2l x :
  x < 0 -> {mono (@GRing.natmul R x) : m n / (n < m)%N >-> m < n}.
Proof. by move=> x_lt0; apply: lenrW_nmono (ler_nmuln2l _). Qed.

Lemma ler_nat m n : (m%:R <= n%:R :> R) = (m <= n)%N.
Proof. by rewrite ler_pmuln2l. Qed.

Lemma ltr_nat m n : (m%:R < n%:R :> R) = (m < n)%N.
Proof. by rewrite ltr_pmuln2l. Qed.

Lemma eqr_nat m n : (m%:R == n%:R :> R) = (m == n)%N.
Proof. by rewrite (inj_eq (mulrIn _)) ?oner_eq0. Qed.

Lemma pnatr_eq1 n : (n%:R == 1 :> R) = (n == 1)%N.
Proof. exact: eqr_nat 1%N. Qed.

Lemma lern0 n : (n%:R <= 0 :> R) = (n == 0%N).
Proof. by rewrite -[0]/0%:R ler_nat leqn0. Qed.

Lemma ltrn0 n : (n%:R < 0 :> R) = false.
Proof. by rewrite -[0]/0%:R ltr_nat ltn0. Qed.

Lemma ler1n n : 1 <= n%:R :> R = (1 <= n)%N. Proof. by rewrite -ler_nat. Qed.
Lemma ltr1n n : 1 < n%:R :> R = (1 < n)%N. Proof. by rewrite -ltr_nat. Qed.
Lemma lern1 n : n%:R <= 1 :> R = (n <= 1)%N. Proof. by rewrite -ler_nat. Qed.
Lemma ltrn1 n : n%:R < 1 :> R = (n < 1)%N. Proof. by rewrite -ltr_nat. Qed.

Lemma ltrN10 : -1 < 0 :> R. Proof. by rewrite oppr_lt0. Qed.
Lemma lerN10 : -1 <= 0 :> R. Proof. by rewrite oppr_le0. Qed.
Lemma ltr10 : 1 < 0 :> R = false. Proof. by rewrite ler_gtF. Qed.
Lemma ler10 : 1 <= 0 :> R = false. Proof. by rewrite ltr_geF. Qed.
Lemma ltr0N1 : 0 < -1 :> R = false. Proof. by rewrite ler_gtF // lerN10. Qed.
Lemma ler0N1 : 0 <= -1 :> R = false. Proof. by rewrite ltr_geF // ltrN10. Qed.

Lemma pmulrn_rgt0 x n : 0 < x -> 0 < x *+ n = (0 < n)%N.
Proof. by move=> x_gt0; rewrite -(mulr0n x) ltr_pmuln2l. Qed.

Lemma pmulrn_rlt0 x n : 0 < x -> x *+ n < 0 = false.
Proof. by move=> x_gt0; rewrite -(mulr0n x) ltr_pmuln2l. Qed.

Lemma pmulrn_rge0 x n : 0 < x -> 0 <= x *+ n.
Proof. by move=> x_gt0; rewrite -(mulr0n x) ler_pmuln2l. Qed.

Lemma pmulrn_rle0 x n : 0 < x -> x *+ n <= 0 = (n == 0)%N.
Proof. by move=> x_gt0; rewrite -(mulr0n x) ler_pmuln2l ?leqn0. Qed.

Lemma nmulrn_rgt0 x n : x < 0 -> 0 < x *+ n = false.
Proof. by move=> x_lt0; rewrite -(mulr0n x) ltr_nmuln2l. Qed.

Lemma nmulrn_rge0 x n : x < 0 -> 0 <= x *+ n = (n == 0)%N.
Proof. by move=> x_lt0; rewrite -(mulr0n x) ler_nmuln2l ?leqn0. Qed.

Lemma nmulrn_rle0 x n : x < 0 -> x *+ n <= 0.
Proof. by move=> x_lt0; rewrite -(mulr0n x) ler_nmuln2l. Qed.

(* (x * y) compared to 0 *)
(* Remark : pmulr_rgt0 and pmulr_rge0 are defined above *)

(* x positive and y right *)
Lemma pmulr_rlt0 x y : 0 < x -> (x * y < 0) = (y < 0).
Proof. by move=> x_gt0; rewrite -oppr_gt0 -mulrN pmulr_rgt0 // oppr_gt0. Qed.

Lemma pmulr_rle0 x y : 0 < x -> (x * y <= 0) = (y <= 0).
Proof. by move=> x_gt0; rewrite -oppr_ge0 -mulrN pmulr_rge0 // oppr_ge0. Qed.

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
Proof. by move=> x_lt0; rewrite -mulrNN pmulr_rgt0 lter_oppE. Qed.

Lemma nmulr_rge0 x y : x < 0 -> (0 <= x * y) = (y <= 0).
Proof. by move=> x_lt0; rewrite -mulrNN pmulr_rge0 lter_oppE. Qed.

Lemma nmulr_rlt0 x y : x < 0 -> (x * y < 0) = (0 < y).
Proof. by move=> x_lt0; rewrite -mulrNN pmulr_rlt0 lter_oppE. Qed.

Lemma nmulr_rle0 x y : x < 0 -> (x * y <= 0) = (0 <= y).
Proof. by move=> x_lt0; rewrite -mulrNN pmulr_rle0 lter_oppE. Qed.

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
Proof. by move=> x_ge0 y_ge0; rewrite -(mulr0 x) ler_wpmul2l. Qed.

Lemma mulr_le0 x y : x <= 0 -> y <= 0 -> 0 <= x * y.
Proof. by move=> x_le0 y_le0; rewrite -(mulr0 x) ler_wnmul2l. Qed.

Lemma mulr_ge0_le0 x y : 0 <= x -> y <= 0 -> x * y <= 0.
Proof. by move=> x_le0 y_le0; rewrite -(mulr0 x) ler_wpmul2l. Qed.

Lemma mulr_le0_ge0 x y : x <= 0 -> 0 <= y -> x * y <= 0.
Proof. by move=> x_le0 y_le0; rewrite -(mulr0 x) ler_wnmul2l. Qed.

(* mulr_gt0 with only one case *)

Lemma mulr_gt0 x y : 0 < x -> 0 < y -> 0 < x * y.
Proof. by move=> x_gt0 y_gt0; rewrite pmulr_rgt0. Qed.

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
by rewrite mulr_ge0 // ler_pmul.
Qed.

Lemma ltr_prod I r (P : pred I) (E1 E2 : I -> R) :
    has P r -> (forall i, P i -> 0 <= E1 i < E2 i) ->
  \prod_(i <- r | P i) E1 i < \prod_(i <- r | P i) E2 i.
Proof.
elim: r => //= i r IHr; rewrite !big_cons; case: ifP => {IHr}// Pi _ ltE12.
have /andP[le0E1i ltE12i] := ltE12 i Pi; set E2r := \prod_(j <- r | P j) E2 j.
apply: ler_lt_trans (_ : E1 i * E2r < E2 i * E2r).
  by rewrite ler_wpmul2l ?ler_prod // => j /ltE12/andP[-> /ltrW].
by rewrite ltr_pmul2r ?prodr_gt0 // => j /ltE12/andP[le0E1j /ler_lt_trans->].
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
move=> x_neq0 xR; case: real_ltrgtP x_neq0 => // hx _; rewrite !realE.
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

Lemma ger_pmull x y : 0 < y -> (x * y <= y) = (x <= 1).
Proof. by move=> hy; rewrite -{2}[y]mul1r ler_pmul2r. Qed.

Lemma gtr_pmull x y : 0 < y -> (x * y < y) = (x < 1).
Proof. by move=> hy; rewrite -{2}[y]mul1r ltr_pmul2r. Qed.

Lemma ger_pmulr x y : 0 < y -> (y * x <= y) = (x <= 1).
Proof. by move=> hy; rewrite -{2}[y]mulr1 ler_pmul2l. Qed.

Lemma gtr_pmulr x y : 0 < y -> (y * x < y) = (x < 1).
Proof. by move=> hy; rewrite -{2}[y]mulr1 ltr_pmul2l. Qed.

Lemma ler_pmull x y : 0 < y -> (y <= x * y) = (1 <= x).
Proof. by move=> hy; rewrite -{1}[y]mul1r ler_pmul2r. Qed.

Lemma ltr_pmull x y : 0 < y -> (y < x * y) = (1 < x).
Proof. by move=> hy; rewrite -{1}[y]mul1r ltr_pmul2r. Qed.

Lemma ler_pmulr x y : 0 < y -> (y <= y * x) = (1 <= x).
Proof. by move=> hy; rewrite -{1}[y]mulr1 ler_pmul2l. Qed.

Lemma ltr_pmulr x y : 0 < y -> (y < y * x) = (1 < x).
Proof. by move=> hy; rewrite -{1}[y]mulr1 ltr_pmul2l. Qed.

Lemma ger_nmull x y : y < 0 -> (x * y <= y) = (1 <= x).
Proof. by move=> hy; rewrite -{2}[y]mul1r ler_nmul2r. Qed.

Lemma gtr_nmull x y : y < 0 -> (x * y < y) = (1 < x).
Proof. by move=> hy; rewrite -{2}[y]mul1r ltr_nmul2r. Qed.

Lemma ger_nmulr x y : y < 0 -> (y * x <= y) = (1 <= x).
Proof. by move=> hy; rewrite -{2}[y]mulr1 ler_nmul2l. Qed.

Lemma gtr_nmulr x y : y < 0 -> (y * x < y) = (1 < x).
Proof. by move=> hy; rewrite -{2}[y]mulr1 ltr_nmul2l. Qed.

Lemma ler_nmull x y : y < 0 -> (y <= x * y) = (x <= 1).
Proof. by move=> hy; rewrite -{1}[y]mul1r ler_nmul2r. Qed.

Lemma ltr_nmull x y : y < 0 -> (y < x * y) = (x < 1).
Proof. by move=> hy; rewrite -{1}[y]mul1r ltr_nmul2r. Qed.

Lemma ler_nmulr x y : y < 0 -> (y <= y * x) = (x <= 1).
Proof. by move=> hy; rewrite -{1}[y]mulr1 ler_nmul2l. Qed.

Lemma ltr_nmulr x y : y < 0 -> (y < y * x) = (x < 1).
Proof. by move=> hy; rewrite -{1}[y]mulr1 ltr_nmul2l. Qed.

(* ler/ltr and multiplication between a positive/negative
   and a exterior (1 <= _) or interior (0 <= _ <= 1) *)

Lemma ler_pemull x y : 0 <= y -> 1 <= x -> y <= x * y.
Proof. by move=> hy hx; rewrite -{1}[y]mul1r ler_wpmul2r. Qed.

Lemma ler_nemull x y : y <= 0 -> 1 <= x -> x * y <= y.
Proof. by move=> hy hx; rewrite -{2}[y]mul1r ler_wnmul2r. Qed.

Lemma ler_pemulr x y : 0 <= y -> 1 <= x -> y <= y * x.
Proof. by move=> hy hx; rewrite -{1}[y]mulr1 ler_wpmul2l. Qed.

Lemma ler_nemulr x y : y <= 0 -> 1 <= x -> y * x <= y.
Proof. by move=> hy hx; rewrite -{2}[y]mulr1 ler_wnmul2l. Qed.

Lemma ler_pimull x y : 0 <= y -> x <= 1 -> x * y <= y.
Proof. by move=> hy hx; rewrite -{2}[y]mul1r ler_wpmul2r. Qed.

Lemma ler_nimull x y : y <= 0 -> x <= 1 -> y <= x * y.
Proof. by move=> hy hx; rewrite -{1}[y]mul1r ler_wnmul2r. Qed.

Lemma ler_pimulr x y : 0 <= y -> x <= 1 -> y * x <= y.
Proof. by move=> hy hx; rewrite -{2}[y]mulr1 ler_wpmul2l. Qed.

Lemma ler_nimulr x y : y <= 0 -> x <= 1 -> y <= y * x.
Proof. by move=> hx hy; rewrite -{1}[y]mulr1 ler_wnmul2l. Qed.

Lemma mulr_ile1 x y : 0 <= x -> 0 <= y -> x <= 1 -> y <= 1 -> x * y <= 1.
Proof. by move=> *; rewrite (@ler_trans _ y) ?ler_pimull. Qed.

Lemma mulr_ilt1 x y : 0 <= x -> 0 <= y -> x < 1 -> y < 1 -> x * y < 1.
Proof. by move=> *; rewrite (@ler_lt_trans _ y) ?ler_pimull // ltrW. Qed.

Definition mulr_ilte1 := (mulr_ile1, mulr_ilt1).

Lemma mulr_ege1 x y : 1 <= x -> 1 <= y -> 1 <= x * y.
Proof.
by move=> le1x le1y; rewrite (@ler_trans _ y) ?ler_pemull // (ler_trans ler01).
Qed.

Lemma mulr_egt1 x y : 1 < x -> 1 < y -> 1 < x * y.
Proof.
by move=> le1x lt1y; rewrite (@ltr_trans _ y) // ltr_pmull // (ltr_trans ltr01).
Qed.
Definition mulr_egte1 := (mulr_ege1, mulr_egt1).
Definition mulr_cp1 := (mulr_ilte1, mulr_egte1).

(* ler and ^-1 *)

Lemma invr_gt0 x : (0 < x^-1) = (0 < x).
Proof.
have [ux | nux] := boolP (x \is a GRing.unit); last by rewrite invr_out.
by apply/idP/idP=> /ltr_pmul2r<-; rewrite mul0r (mulrV, mulVr) ?ltr01.
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

Lemma exprn_ilt1 n x : 0 <= x -> x < 1 -> x ^+ n < 1 = (n != 0%N).
Proof.
move=> xge0 xlt1.
case: n; [by rewrite eqxx ltrr | elim=> [|n ihn]; first by rewrite expr1].
by rewrite exprS mulr_ilt1 // exprn_ge0.
Qed.

Definition exprn_ilte1 := (exprn_ile1, exprn_ilt1).

Lemma exprn_ege1 n x : 1 <= x -> 1 <= x ^+ n.
Proof.
by move=> x_ge1; elim: n=> [|n ihn]; rewrite ?expr0 // exprS mulr_ege1.
Qed.

Lemma exprn_egt1 n x : 1 < x -> 1 < x ^+ n = (n != 0%N).
Proof.
move=> xgt1; case: n; first by rewrite eqxx ltrr.
elim=> [|n ihn]; first by rewrite expr1.
by rewrite exprS mulr_egt1 // exprn_ge0.
Qed.

Definition exprn_egte1 := (exprn_ege1, exprn_egt1).
Definition exprn_cp1 := (exprn_ilte1, exprn_egte1).

Lemma ler_iexpr x n : (0 < n)%N -> 0 <= x -> x <= 1 -> x ^+ n <= x.
Proof. by case: n => n // *; rewrite exprS ler_pimulr // exprn_ile1. Qed.

Lemma ltr_iexpr x n : 0 < x -> x < 1 -> (x ^+ n < x) = (1 < n)%N.
Proof.
case: n=> [|[|n]] //; first by rewrite expr0 => _ /ltr_gtF ->.
by move=> x0 x1; rewrite exprS gtr_pmulr // ?exprn_ilt1 // ltrW.
Qed.

Definition lter_iexpr := (ler_iexpr, ltr_iexpr).

Lemma ler_eexpr x n : (0 < n)%N -> 1 <= x -> x <= x ^+ n.
Proof.
case: n => // n _ x_ge1.
by rewrite exprS ler_pemulr ?(ler_trans _ x_ge1) // exprn_ege1.
Qed.

Lemma ltr_eexpr x n : 1 < x -> (x < x ^+ n) = (1 < n)%N.
Proof.
move=> x_ge1; case: n=> [|[|n]] //; first by rewrite expr0 ltr_gtF.
by rewrite exprS ltr_pmulr ?(ltr_trans _ x_ge1) ?exprn_egt1.
Qed.

Definition lter_eexpr := (ler_eexpr, ltr_eexpr).
Definition lter_expr := (lter_iexpr, lter_eexpr).

Lemma ler_wiexpn2l x :
  0 <= x -> x <= 1 -> {homo (GRing.exp x) : m n / (n <= m)%N >-> m <= n}.
Proof.
move=> xge0 xle1 m n /= hmn.
by rewrite -(subnK hmn) exprD ler_pimull ?(exprn_ge0, exprn_ile1).
Qed.

Lemma ler_weexpn2l x :
  1 <= x -> {homo (GRing.exp x) : m n / (m <= n)%N >-> m <= n}.
Proof.
move=> xge1 m n /= hmn; rewrite -(subnK hmn) exprD.
by rewrite ler_pemull ?(exprn_ge0, exprn_ege1) // (ler_trans _ xge1) ?ler01.
Qed.

Lemma ieexprn_weq1 x n : 0 <= x -> (x ^+ n == 1) = ((n == 0%N) || (x == 1)).
Proof.
move=> xle0; case: n => [|n]; first by rewrite expr0 eqxx.
case: (@real_ltrgtP x 1); do ?by rewrite ?ger0_real.
+ by move=> x_lt1; rewrite ?ltr_eqF // exprn_ilt1.
+ by move=> x_lt1; rewrite ?gtr_eqF // exprn_egt1.
by move->; rewrite expr1n eqxx.
Qed.

Lemma ieexprIn x : 0 < x -> x != 1 -> injective (GRing.exp x).
Proof.
move=> x_gt0 x_neq1 m n; without loss /subnK <-: m n / (n <= m)%N.
  by move=> IH eq_xmn; case/orP: (leq_total m n) => /IH->.
case: {m}(m - n)%N => // m /eqP/idPn[]; rewrite -[x ^+ n]mul1r exprD.
by rewrite (inj_eq (mulIf _)) ?ieexprn_weq1 ?ltrW // expf_neq0 ?gtr_eqF.
Qed.

Lemma ler_iexpn2l x :
  0 < x -> x < 1 -> {mono (GRing.exp x) : m n / (n <= m)%N >-> m <= n}.
Proof.
move=> xgt0 xlt1; apply: (lenr_nmono (inj_nhomo_ltnr _ _)); last first.
  by apply: ler_wiexpn2l; rewrite ltrW.
by apply: ieexprIn; rewrite ?ltr_eqF ?ltr_cpable.
Qed.

Lemma ltr_iexpn2l x :
  0 < x -> x < 1 -> {mono (GRing.exp x) : m n / (n < m)%N >-> m < n}.
Proof. by move=> xgt0 xlt1; apply: (lenrW_nmono (ler_iexpn2l _ _)). Qed.

Definition lter_iexpn2l := (ler_iexpn2l, ltr_iexpn2l).

Lemma ler_eexpn2l x :
  1 < x -> {mono (GRing.exp x) : m n / (m <= n)%N >-> m <= n}.
Proof.
move=> xgt1; apply: (lenr_mono (inj_homo_ltnr _ _)); last first.
  by apply: ler_weexpn2l; rewrite ltrW.
by apply: ieexprIn; rewrite ?gtr_eqF ?gtr_cpable //; apply: ltr_trans xgt1.
Qed.

Lemma ltr_eexpn2l x :
  1 < x -> {mono (GRing.exp x) : m n / (m < n)%N >-> m < n}.
Proof. by move=> xgt1; apply: (lenrW_mono (ler_eexpn2l _)). Qed.

Definition lter_eexpn2l := (ler_eexpn2l, ltr_eexpn2l).

Lemma ltr_expn2r n x y : 0 <= x -> x < y ->  x ^+ n < y ^+ n = (n != 0%N).
Proof.
move=> xge0 xlty; case: n; first by rewrite ltrr.
elim=> [|n IHn]; rewrite ?[_ ^+ _.+2]exprS //.
rewrite (@ler_lt_trans _ (x * y ^+ n.+1)) ?ler_wpmul2l ?ltr_pmul2r ?IHn //.
  by rewrite ltrW // ihn.
by rewrite exprn_gt0 // (ler_lt_trans xge0).
Qed.

Lemma ler_expn2r n : {in nneg & , {homo ((@GRing.exp R)^~ n) : x y / x <= y}}.
Proof.
move=> x y /= x0 y0 xy; elim: n => [|n IHn]; rewrite !(expr0, exprS) //.
by rewrite (@ler_trans _ (x * y ^+ n)) ?ler_wpmul2l ?ler_wpmul2r ?exprn_ge0.
Qed.

Definition lter_expn2r := (ler_expn2r, ltr_expn2r).

Lemma ltr_wpexpn2r n :
  (0 < n)%N -> {in nneg & , {homo ((@GRing.exp R)^~ n) : x y / x < y}}.
Proof. by move=> ngt0 x y /= x0 y0 hxy; rewrite ltr_expn2r // -lt0n. Qed.

Lemma ler_pexpn2r n :
  (0 < n)%N -> {in nneg & , {mono ((@GRing.exp R)^~ n) : x y / x <= y}}.
Proof.
case: n => // n _ x y; rewrite !qualifE /= =>  x_ge0 y_ge0.
have [-> | nzx] := eqVneq x 0; first by rewrite exprS mul0r exprn_ge0.
rewrite -subr_ge0 subrXX pmulr_lge0 ?subr_ge0 //= big_ord_recr /=.
rewrite subnn expr0 mul1r /= ltr_spaddr // ?exprn_gt0 ?lt0r ?nzx //.
by rewrite sumr_ge0 // => i _; rewrite mulr_ge0 ?exprn_ge0.
Qed.

Lemma ltr_pexpn2r n :
  (0 < n)%N -> {in nneg & , {mono ((@GRing.exp R)^~ n) : x y / x < y}}.
Proof.
by move=> n_gt0 x y x_ge0 y_ge0; rewrite !ltr_neqAle !eqr_le !ler_pexpn2r.
Qed.

Definition lter_pexpn2r := (ler_pexpn2r, ltr_pexpn2r).

Lemma pexpIrn n : (0 < n)%N -> {in nneg &, injective ((@GRing.exp R)^~ n)}.
Proof. by move=> n_gt0; apply: incr_inj_in (ler_pexpn2r _). Qed.

(* expr and ler/ltr *)
Lemma expr_le1 n x : (0 < n)%N -> 0 <= x -> (x ^+ n <= 1) = (x <= 1).
Proof.
by move=> ngt0 xge0; rewrite -{1}[1](expr1n _ n) ler_pexpn2r // [_ \in _]ler01.
Qed.

Lemma expr_lt1 n x : (0 < n)%N -> 0 <= x -> (x ^+ n < 1) = (x < 1).
Proof.
by move=> ngt0 xge0; rewrite -{1}[1](expr1n _ n) ltr_pexpn2r // [_ \in _]ler01.
Qed.

Definition expr_lte1 := (expr_le1, expr_lt1).

Lemma expr_ge1 n x : (0 < n)%N -> 0 <= x -> (1 <= x ^+ n) = (1 <= x).
Proof.
by move=> ngt0 xge0; rewrite -{1}[1](expr1n _ n) ler_pexpn2r // [_ \in _]ler01.
Qed.

Lemma expr_gt1 n x : (0 < n)%N -> 0 <= x -> (1 < x ^+ n) = (1 < x).
Proof.
by move=> ngt0 xge0; rewrite -{1}[1](expr1n _ n) ltr_pexpn2r // [_ \in _]ler01.
Qed.

Definition expr_gte1 := (expr_ge1, expr_gt1).

Lemma pexpr_eq1 x n : (0 < n)%N -> 0 <= x -> (x ^+ n == 1) = (x == 1).
Proof. by move=> ngt0 xge0; rewrite !eqr_le expr_le1 // expr_ge1. Qed.

Lemma pexprn_eq1 x n : 0 <= x -> (x ^+ n == 1) = (n == 0%N) || (x == 1).
Proof. by case: n => [|n] xge0; rewrite ?eqxx // pexpr_eq1 ?gtn_eqF. Qed.

Lemma eqr_expn2 n x y :
  (0 < n)%N -> 0 <= x -> 0 <= y -> (x ^+ n == y ^+ n) = (x == y).
Proof. by move=> ngt0 xge0 yge0; rewrite (inj_in_eq (pexpIrn _)). Qed.

Lemma sqrp_eq1 x : 0 <= x -> (x ^+ 2 == 1) = (x == 1).
Proof. by move/pexpr_eq1->. Qed.

Lemma sqrn_eq1 x : x <= 0 -> (x ^+ 2 == 1) = (x == -1).
Proof. by rewrite -sqrrN -oppr_ge0 -eqr_oppLR => /sqrp_eq1. Qed.

Lemma ler_sqr : {in nneg &, {mono (fun x => x ^+ 2) : x y / x <= y}}.
Proof. exact: ler_pexpn2r. Qed.

Lemma ltr_sqr : {in nneg &, {mono (fun x => x ^+ 2) : x y / x < y}}.
Proof. exact: ltr_pexpn2r. Qed.

Lemma ler_pinv :
  {in [pred x in GRing.unit | 0 < x] &, {mono (@GRing.inv R) : x y /~ x <= y}}.
Proof.
move=> x y /andP [ux hx] /andP [uy hy] /=.
rewrite -(ler_pmul2l hx) -(ler_pmul2r hy).
by rewrite !(divrr, mulrVK) ?unitf_gt0 // mul1r.
Qed.

Lemma ler_ninv :
  {in [pred x in GRing.unit | x < 0] &, {mono (@GRing.inv R) : x y /~ x <= y}}.
Proof.
move=> x y /andP [ux hx] /andP [uy hy] /=.
rewrite -(ler_nmul2l hx) -(ler_nmul2r hy).
by rewrite !(divrr, mulrVK) ?unitf_lt0 // mul1r.
Qed.

Lemma ltr_pinv :
  {in [pred x in GRing.unit | 0 < x] &, {mono (@GRing.inv R) : x y /~ x < y}}.
Proof. exact: lerW_nmono_in ler_pinv. Qed.

Lemma ltr_ninv :
  {in [pred x in GRing.unit | x < 0] &, {mono (@GRing.inv R) : x y /~ x < y}}.
Proof. exact: lerW_nmono_in ler_ninv. Qed.

Lemma invr_gt1 x : x \is a GRing.unit -> 0 < x -> (1 < x^-1) = (x < 1).
Proof.
by move=> Ux xgt0; rewrite -{1}[1]invr1 ltr_pinv ?inE ?unitr1 ?ltr01 ?Ux.
Qed.

Lemma invr_ge1 x : x \is a GRing.unit -> 0 < x -> (1 <= x^-1) = (x <= 1).
Proof.
by move=> Ux xgt0; rewrite -{1}[1]invr1 ler_pinv ?inE ?unitr1 ?ltr01 // Ux.
Qed.

Definition invr_gte1 := (invr_ge1, invr_gt1).

Lemma invr_le1 x (ux : x \is a GRing.unit) (hx : 0 < x) :
  (x^-1 <= 1) = (1 <= x).
Proof. by rewrite -invr_ge1 ?invr_gt0 ?unitrV // invrK. Qed.

Lemma invr_lt1 x (ux : x \is a GRing.unit) (hx : 0 < x) : (x^-1 < 1) = (1 < x).
Proof. by rewrite -invr_gt1 ?invr_gt0 ?unitrV // invrK. Qed.

Definition invr_lte1 := (invr_le1, invr_lt1).
Definition invr_cp1 := (invr_gte1, invr_lte1).

(* norm *)

Lemma real_ler_norm x : x \is real -> x <= `|x|.
Proof.
by case/real_ger0P=> hx //; rewrite (ler_trans (ltrW hx)) // oppr_ge0 ltrW.
Qed.

(* norm + add *)

Lemma normr_real x : `|x| \is real. Proof. by rewrite ger0_real. Qed.
Hint Resolve normr_real : core.

Lemma ler_norm_sum I r (G : I -> R) (P : pred I):
  `|\sum_(i <- r | P i) G i| <= \sum_(i <- r | P i) `|G i|.
Proof.
elim/big_rec2: _ => [|i y x _]; first by rewrite normr0.
by rewrite -(ler_add2l `|G i|); apply: ler_trans; apply: ler_norm_add.
Qed.

Lemma ler_norm_sub x y : `|x - y| <= `|x| + `|y|.
Proof. by rewrite (ler_trans (ler_norm_add _ _)) ?normrN. Qed.

Lemma ler_dist_add z x y : `|x - y| <= `|x - z| + `|z - y|.
Proof. by rewrite (ler_trans _ (ler_norm_add _ _)) // addrA addrNK. Qed.

Lemma ler_sub_norm_add x y : `|x| - `|y| <= `|x + y|.
Proof.
rewrite -{1}[x](addrK y) lter_sub_addl.
by rewrite (ler_trans (ler_norm_add _ _)) // addrC normrN.
Qed.

Lemma ler_sub_dist x y : `|x| - `|y| <= `|x - y|.
Proof. by rewrite -[`|y|]normrN ler_sub_norm_add. Qed.

Lemma ler_dist_dist x y : `|`|x| - `|y| | <= `|x - y|.
Proof.
have [||_|_] // := @real_lerP `|x| `|y|; last by rewrite ler_sub_dist.
by rewrite distrC ler_sub_dist.
Qed.

Lemma ler_dist_norm_add x y : `| `|x| - `|y| | <= `| x + y |.
Proof. by rewrite -[y]opprK normrN ler_dist_dist. Qed.

Lemma real_ler_norml x y : x \is real -> (`|x| <= y) = (- y <= x <= y).
Proof.
move=> xR; wlog x_ge0 : x xR / 0 <= x => [hwlog|].
  move: (xR) => /(@real_leVge 0) /orP [|/hwlog->|hx] //.
  by rewrite -[x]opprK normrN ler_opp2 andbC ler_oppl hwlog ?realN ?oppr_ge0.
rewrite ger0_norm //; have [le_xy|] := boolP (x <= y); last by rewrite andbF.
by rewrite (ler_trans _ x_ge0) // oppr_le0 (ler_trans x_ge0).
Qed.

Lemma real_ler_normlP x y :
  x \is real -> reflect ((-x <= y) * (x <= y)) (`|x| <= y).
Proof.
by move=> Rx; rewrite real_ler_norml // ler_oppl; apply: (iffP andP) => [] [].
Qed.
Arguments real_ler_normlP {x y}.

Lemma real_eqr_norml x y :
  x \is real -> (`|x| == y) = ((x == y) || (x == -y)) && (0 <= y).
Proof.
move=> Rx.
apply/idP/idP=> [|/andP[/pred2P[]-> /ger0_norm/eqP]]; rewrite ?normrE //.
case: real_ler0P => // hx; rewrite 1?eqr_oppLR => /eqP exy.
  by move: hx; rewrite exy ?oppr_le0 eqxx orbT //.
by move: hx=> /ltrW; rewrite exy eqxx.
Qed.

Lemma real_eqr_norm2 x y :
  x \is real -> y \is real -> (`|x| == `|y|) = (x == y) || (x == -y).
Proof.
move=> Rx Ry; rewrite real_eqr_norml // normrE andbT.
by case: real_ler0P; rewrite // opprK orbC.
Qed.

Lemma real_ltr_norml x y : x \is real -> (`|x| < y) = (- y < x < y).
Proof.
move=> Rx; wlog x_ge0 : x Rx / 0 <= x => [hwlog|].
  move: (Rx) => /(@real_leVge 0) /orP [|/hwlog->|hx] //.
  by rewrite -[x]opprK normrN ltr_opp2 andbC ltr_oppl hwlog ?realN ?oppr_ge0.
rewrite ger0_norm //; have [le_xy|] := boolP (x < y); last by rewrite andbF.
by rewrite (ltr_le_trans _ x_ge0) // oppr_lt0 (ler_lt_trans x_ge0).
Qed.

Definition real_lter_norml := (real_ler_norml, real_ltr_norml).

Lemma real_ltr_normlP x y :
  x \is real -> reflect ((-x < y) * (x < y)) (`|x| < y).
Proof.
move=> Rx; rewrite real_ltr_norml // ltr_oppl.
by apply: (iffP (@andP _ _)); case.
Qed.
Arguments real_ltr_normlP {x y}.

Lemma real_ler_normr x y : y \is real -> (x <= `|y|) = (x <= y) || (x <= - y).
Proof.
move=> Ry.
have [xR|xNR] := boolP (x \is real); last by rewrite ?Nreal_leF ?realN.
rewrite real_lerNgt ?real_ltr_norml // negb_and -?real_lerNgt ?realN //.
by rewrite orbC ler_oppr.
Qed.

Lemma real_ltr_normr x y : y \is real -> (x < `|y|) = (x < y) || (x < - y).
Proof.
move=> Ry.
have [xR|xNR] := boolP (x \is real); last by rewrite ?Nreal_ltF ?realN.
rewrite real_ltrNge ?real_ler_norml // negb_and -?real_ltrNge ?realN //.
by rewrite orbC ltr_oppr.
Qed.

Definition real_lter_normr :=  (real_ler_normr, real_ltr_normr).

Lemma ler_nnorml x y : y < 0 -> `|x| <= y = false.
Proof. by move=> y_lt0; rewrite ltr_geF // (ltr_le_trans y_lt0). Qed.

Lemma ltr_nnorml x y : y <= 0 -> `|x| < y = false.
Proof. by move=> y_le0; rewrite ler_gtF // (ler_trans y_le0). Qed.

Definition lter_nnormr := (ler_nnorml, ltr_nnorml).

Lemma real_ler_distl x y e :
  x - y \is real -> (`|x - y| <= e) = (y - e <= x <= y + e).
Proof. by move=> Rxy; rewrite real_lter_norml // !lter_sub_addl. Qed.

Lemma real_ltr_distl x y e :
  x - y \is real -> (`|x - y| < e) = (y - e < x < y + e).
Proof. by move=> Rxy; rewrite real_lter_norml // !lter_sub_addl. Qed.

Definition real_lter_distl := (real_ler_distl, real_ltr_distl).

(* GG: pointless duplication }-( *)
Lemma eqr_norm_id x : (`|x| == x) = (0 <= x). Proof. by rewrite ger0_def. Qed.
Lemma eqr_normN x : (`|x| == - x) = (x <= 0). Proof. by rewrite ler0_def. Qed.
Definition eqr_norm_idVN := =^~ (ger0_def, ler0_def).

Lemma real_exprn_even_ge0 n x : x \is real -> ~~ odd n -> 0 <= x ^+ n.
Proof.
move=> xR even_n; have [/exprn_ge0 -> //|x_lt0] := real_ger0P xR.
rewrite -[x]opprK -mulN1r exprMn -signr_odd (negPf even_n) expr0 mul1r.
by rewrite exprn_ge0 ?oppr_ge0 ?ltrW.
Qed.

Lemma real_exprn_even_gt0 n x :
  x \is real -> ~~ odd n -> (0 < x ^+ n) = (n == 0)%N || (x != 0).
Proof.
move=> xR n_even; rewrite lt0r real_exprn_even_ge0 ?expf_eq0 //.
by rewrite andbT negb_and lt0n negbK.
Qed.

Lemma real_exprn_even_le0 n x :
  x \is real -> ~~ odd n -> (x ^+ n <= 0) = (n != 0%N) && (x == 0).
Proof.
move=> xR n_even; rewrite !real_lerNgt ?rpred0 ?rpredX //.
by rewrite real_exprn_even_gt0 // negb_or negbK.
Qed.

Lemma real_exprn_even_lt0 n x :
  x \is real -> ~~ odd n -> (x ^+ n < 0) = false.
Proof. by move=> xR n_even; rewrite ler_gtF // real_exprn_even_ge0. Qed.

Lemma real_exprn_odd_ge0 n x :
  x \is real -> odd n -> (0 <= x ^+ n) = (0 <= x).
Proof.
case/real_ger0P => [x_ge0|x_lt0] n_odd; first by rewrite exprn_ge0.
apply: negbTE; rewrite ltr_geF //.
case: n n_odd => // n /= n_even; rewrite exprS pmulr_llt0 //.
by rewrite real_exprn_even_gt0 ?ler0_real ?ltrW // ltr_eqF ?orbT.
Qed.

Lemma real_exprn_odd_gt0 n x : x \is real -> odd n -> (0 < x ^+ n) = (0 < x).
Proof.
by move=> xR n_odd; rewrite !lt0r expf_eq0 real_exprn_odd_ge0; case: n n_odd.
Qed.

Lemma real_exprn_odd_le0 n x : x \is real -> odd n -> (x ^+ n <= 0) = (x <= 0).
Proof.
by move=> xR n_odd; rewrite !real_lerNgt ?rpred0 ?rpredX // real_exprn_odd_gt0.
Qed.

Lemma real_exprn_odd_lt0 n x : x \is real -> odd n -> (x ^+ n < 0) = (x < 0).
Proof.
by move=> xR n_odd; rewrite !real_ltrNge ?rpred0 ?rpredX // real_exprn_odd_ge0.
Qed.

(* GG: Could this be a better definition of "real" ? *)
Lemma realEsqr x : (x \is real) = (0 <= x ^+ 2).
Proof. by rewrite ger0_def normrX eqf_sqr -ger0_def -ler0_def. Qed.

Lemma real_normK x : x \is real -> `|x| ^+ 2 = x ^+ 2.
Proof. by move=> Rx; rewrite -normrX ger0_norm -?realEsqr. Qed.

(* Binary sign ((-1) ^+ s). *)

Lemma normr_sign s : `|(-1) ^+ s| = 1 :> R.
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
Proof. by rewrite ler_eqVlt signr_eq0 signr_lt0. Qed.

(* This actually holds for char R != 2. *)
Lemma signr_inj : injective (fun b : bool => (-1) ^+ b : R).
Proof. exact: can_inj (fun x => 0 >= x) signr_le0. Qed.

(* Ternary sign (sg). *)

Lemma sgr_def x : sg x = (-1) ^+ (x < 0)%R *+ (x != 0).
Proof. by rewrite /sg; do 2!case: ifP => //. Qed.

Lemma neqr0_sign x : x != 0 -> (-1) ^+ (x < 0)%R = sgr x.
Proof. by rewrite sgr_def  => ->. Qed.

Lemma gtr0_sg x : 0 < x -> sg x = 1.
Proof. by move=> x_gt0; rewrite /sg gtr_eqF // ltr_gtF. Qed.

Lemma ltr0_sg x : x < 0 -> sg x = -1.
Proof. by move=> x_lt0; rewrite /sg x_lt0 ltr_eqF. Qed.

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

Lemma sgrMn x n : sg (x *+ n) = (n != 0%N)%:R * sg x.
Proof.
case: n => [|n]; first by rewrite mulr0n sgr0 mul0r.
by rewrite !sgr_def mulrn_eq0 mul1r pmulrn_llt0.
Qed.

Lemma sgr_nat n : sg n%:R = (n != 0%N)%:R :> R.
Proof. by rewrite sgrMn sgr1 mulr1. Qed.

Lemma sgr_id x : sg (sg x) = sg x.
Proof. by rewrite !(fun_if sg) !sgrE. Qed.

Lemma sgr_lt0 x : (sg x < 0) = (x < 0).
Proof.
rewrite /sg; case: eqP => [-> // | _].
by case: ifP => _; rewrite ?ltrN10 // ltr_gtF.
Qed.

Lemma sgr_le0 x : (sgr x <= 0) = (x <= 0).
Proof. by rewrite !ler_eqVlt sgr_eq0 sgr_lt0. Qed.

(* sign and norm *)

Lemma realEsign x : x \is real -> x = (-1) ^+ (x < 0)%R * `|x|.
Proof. by case/real_ger0P; rewrite (mul1r, mulN1r) ?opprK. Qed.

Lemma realNEsign x : x \is real -> - x = (-1) ^+ (0 < x)%R * `|x|.
Proof. by move=> Rx; rewrite -normrN -oppr_lt0 -realEsign ?rpredN. Qed.

Lemma real_normrEsign (x : R) (xR : x \is real) : `|x| = (-1) ^+ (x < 0)%R * x.
Proof. by rewrite {3}[x]realEsign // signrMK. Qed.

(* GG: pointless duplication... *)
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
Proof. by rewrite /sg ler_gtF ?normr_ge0 // normr_eq0 mulrb if_neg. Qed.

(* lerif *)

Lemma lerif_refl x C : reflect (x <= x ?= iff C) C.
Proof. by apply: (iffP idP) => [-> | <-] //; split; rewrite ?eqxx. Qed.

Lemma lerif_trans x1 x2 x3 C12 C23 :
  x1 <= x2 ?= iff C12 -> x2 <= x3 ?= iff C23 -> x1 <= x3 ?= iff C12 && C23.
Proof.
move=> ltx12 ltx23; apply/lerifP; rewrite -ltx12.
case eqx12: (x1 == x2).
  by rewrite (eqP eqx12) ltr_neqAle !ltx23 andbT; case C23.
by rewrite (@ltr_le_trans _ x2) ?ltx23 // ltr_neqAle eqx12 ltx12.
Qed.

Lemma lerif_le x y : x <= y -> x <= y ?= iff (x >= y).
Proof. by move=> lexy; split=> //; rewrite eqr_le lexy. Qed.

Lemma lerif_eq x y : x <= y -> x <= y ?= iff (x == y).
Proof. by []. Qed.

Lemma ger_lerif x y C : x <= y ?= iff C -> (y <= x) = C.
Proof. by case=> le_xy; rewrite eqr_le le_xy. Qed.

Lemma ltr_lerif x y C : x <= y ?= iff C -> (x < y) = ~~ C.
Proof. by move=> le_xy; rewrite ltr_neqAle !le_xy andbT. Qed.

Lemma lerif_nat m n C : (m%:R <= n%:R ?= iff C :> R) = (m <= n ?= iff C)%N.
Proof. by rewrite /lerif !ler_nat eqr_nat. Qed.

Lemma mono_in_lerif (A : pred R) (f : R -> R) C :
   {in A &, {mono f : x y / x <= y}} ->
  {in A &, forall x y, (f x <= f y ?= iff C) = (x <= y ?= iff C)}.
Proof.
by move=> mf x y Ax Ay; rewrite /lerif mf ?(inj_in_eq (incr_inj_in mf)).
Qed.

Lemma mono_lerif (f : R -> R) C :
    {mono f : x y / x <= y} ->
  forall x y, (f x <= f y ?= iff C) = (x <= y ?= iff C).
Proof. by move=> mf x y; rewrite /lerif mf (inj_eq (incr_inj _)). Qed.

Lemma nmono_in_lerif (A : pred R) (f : R -> R) C :
    {in A &, {mono f : x y /~ x <= y}} ->
  {in A &, forall x y, (f x <= f y ?= iff C) = (y <= x ?= iff C)}.
Proof.
move=> mf x y Ax Ay; rewrite /lerif eq_sym mf //.
by rewrite ?(inj_in_eq (decr_inj_in mf)).
Qed.

Lemma nmono_lerif (f : R -> R) C :
    {mono f : x y /~ x <= y} ->
  forall x y, (f x <= f y ?= iff C) = (y <= x ?= iff C).
Proof. by move=> mf x y; rewrite /lerif eq_sym mf ?(inj_eq (decr_inj mf)). Qed.

Lemma lerif_subLR x y z C : (x - y <= z ?= iff C) = (x <= z + y ?= iff C).
Proof. by rewrite /lerif !eqr_le ler_subr_addr ler_subl_addr. Qed.

Lemma lerif_subRL x y z C : (x <= y - z ?= iff C) = (x + z <= y ?= iff C).
Proof. by rewrite -lerif_subLR opprK. Qed.

Lemma lerif_add x1 y1 C1 x2 y2 C2 :
    x1 <= y1 ?= iff C1 -> x2 <= y2 ?= iff C2 ->
  x1 + x2 <= y1 + y2 ?= iff C1 && C2.
Proof.
rewrite -(mono_lerif _ (ler_add2r x2)) -(mono_lerif C2 (ler_add2l y1)).
exact: lerif_trans.
Qed.

Lemma lerif_sum (I : finType) (P C : pred I) (E1 E2 : I -> R) :
    (forall i, P i -> E1 i <= E2 i ?= iff C i) ->
  \sum_(i | P i) E1 i <= \sum_(i | P i) E2 i ?= iff [forall (i | P i), C i].
Proof.
move=> leE12; rewrite -big_andE.
elim/big_rec3: _ => [|i Ci m2 m1 /leE12]; first by rewrite /lerif lerr eqxx.
exact: lerif_add.
Qed.

Lemma lerif_0_sum (I : finType) (P C : pred I) (E : I -> R) :
    (forall i, P i -> 0 <= E i ?= iff C i) ->
  0 <= \sum_(i | P i) E i ?= iff [forall (i | P i), C i].
Proof. by move/lerif_sum; rewrite big1_eq. Qed.

Lemma real_lerif_norm x : x \is real -> x <= `|x| ?= iff (0 <= x).
Proof.
by move=> xR; rewrite ger0_def eq_sym; apply: lerif_eq; rewrite real_ler_norm.
Qed.

Lemma lerif_pmul x1 x2 y1 y2 C1 C2 :
    0 <= x1 -> 0 <= x2 -> x1 <= y1 ?= iff C1 -> x2 <= y2 ?= iff C2 ->
  x1 * x2 <= y1 * y2 ?= iff (y1 * y2 == 0) || C1 && C2.
Proof.
move=> x1_ge0 x2_ge0 le_xy1 le_xy2; have [y_0 | ] := altP (_ =P 0).
  apply/lerifP; rewrite y_0 /= mulf_eq0 !eqr_le x1_ge0 x2_ge0 !andbT.
  move/eqP: y_0; rewrite mulf_eq0.
  by case/pred2P=> <-; rewrite (le_xy1, le_xy2) ?orbT.
rewrite /= mulf_eq0 => /norP[y1nz y2nz].
have y1_gt0: 0 < y1 by rewrite ltr_def y1nz (ler_trans _ le_xy1).
have [x2_0 | x2nz] := eqVneq x2 0.
  apply/lerifP; rewrite -le_xy2 x2_0 eq_sym (negPf y2nz) andbF mulr0.
  by rewrite mulr_gt0 // ltr_def y2nz -x2_0 le_xy2.
have:= le_xy2; rewrite -(mono_lerif _ (ler_pmul2l y1_gt0)).
by apply: lerif_trans; rewrite (mono_lerif _ (ler_pmul2r _)) // ltr_def x2nz.
Qed.

Lemma lerif_nmul x1 x2 y1 y2 C1 C2 :
    y1 <= 0 -> y2 <= 0 -> x1 <= y1 ?= iff C1 -> x2 <= y2 ?= iff C2 ->
  y1 * y2 <= x1 * x2 ?= iff (x1 * x2 == 0) || C1 && C2.
Proof.
rewrite -!oppr_ge0 -mulrNN -[x1 * x2]mulrNN => y1le0 y2le0 le_xy1 le_xy2.
by apply: lerif_pmul => //; rewrite (nmono_lerif _ ler_opp2).
Qed.

Lemma lerif_pprod (I : finType) (P C : pred I) (E1 E2 : I -> R) :
    (forall i, P i -> 0 <= E1 i) ->
    (forall i, P i -> E1 i <= E2 i ?= iff C i) ->
  let pi E := \prod_(i | P i) E i in
  pi E1 <= pi E2 ?= iff (pi E2 == 0) || [forall (i | P i), C i].
Proof.
move=> E1_ge0 leE12 /=; rewrite -big_andE; elim/(big_load (fun x => 0 <= x)): _.
elim/big_rec3: _ => [|i Ci m2 m1 Pi [m1ge0 le_m12]].
  by split=> //; apply/lerifP; rewrite orbT.
have Ei_ge0 := E1_ge0 i Pi; split; first by rewrite mulr_ge0.
congr (lerif _ _ _): (lerif_pmul Ei_ge0 m1ge0 (leE12 i Pi) le_m12).
by rewrite mulf_eq0 -!orbA; congr (_ || _); rewrite !orb_andr orbA orbb.
Qed.

(* Mean inequalities. *)

Lemma real_lerif_mean_square_scaled x y :
  x \is real -> y \is real -> x * y *+ 2 <= x ^+ 2 + y ^+ 2 ?= iff (x == y).
Proof.
move=> Rx Ry; rewrite -[_ *+ 2]add0r -lerif_subRL addrAC -sqrrB -subr_eq0.
by rewrite -sqrf_eq0 eq_sym; apply: lerif_eq; rewrite -realEsqr rpredB.
Qed.

Lemma real_lerif_AGM2_scaled x y :
  x \is real -> y \is real -> x * y *+ 4 <= (x + y) ^+ 2 ?= iff (x == y).
Proof.
move=> Rx Ry; rewrite sqrrD addrAC (mulrnDr _ 2) -lerif_subLR addrK.
exact: real_lerif_mean_square_scaled.
Qed.

Lemma lerif_AGM_scaled (I : finType) (A : pred I) (E : I -> R) (n := #|A|) :
    {in A, forall i, 0 <= E i *+ n} ->
  \prod_(i in A) (E i *+ n) <= (\sum_(i in A) E i) ^+ n
                            ?= iff [forall i in A, forall j in A, E i == E j].
Proof.
elim: {A}_.+1 {-2}A (ltnSn #|A|) => // m IHm A leAm in E n * => Ege0.
apply/lerifP; case: ifPn => [/forall_inP-Econstant | Enonconstant].
  have [i /= Ai | A0] := pickP (mem A); last by rewrite [n]eq_card0 ?big_pred0.
  have /eqfun_inP-E_i := Econstant i Ai; rewrite -(eq_bigr _ E_i) sumr_const.
  by rewrite exprMn_n prodrMn -(eq_bigr _ E_i) prodr_const.
set mu := \sum_(i in A) E i; pose En i := E i *+ n.
pose cmp_mu s := [pred i | s * mu < s * En i].
have{Enonconstant} has_cmp_mu e (s := (-1) ^+ e): {i | i \in A & cmp_mu s i}.
  apply/sig2W/exists_inP; apply: contraR Enonconstant.
  rewrite negb_exists_in => /forall_inP-mu_s_A.
  have n_gt0 i: i \in A -> (0 < n)%N by rewrite [n](cardD1 i) => ->.
  have{mu_s_A} mu_s_A i: i \in A -> s * En i <= s * mu.
    move=> Ai; rewrite real_lerNgt ?mu_s_A ?rpredMsign ?ger0_real ?Ege0 //.
    by rewrite -(pmulrn_lge0 _ (n_gt0 i Ai)) -sumrMnl sumr_ge0.
  have [_ /esym/eqfun_inP] := lerif_sum (fun i Ai => lerif_eq (mu_s_A i Ai)).
  rewrite sumr_const -/n -mulr_sumr sumrMnl -/mu mulrnAr eqxx => A_mu.
  apply/forall_inP=> i Ai; apply/eqfun_inP=> j Aj.
  by apply: (pmulrnI (n_gt0 i Ai)); apply: (can_inj (signrMK e)); rewrite !A_mu.
have [[i Ai Ei_lt_mu] [j Aj Ej_gt_mu]] := (has_cmp_mu 1, has_cmp_mu 0)%N.
rewrite {cmp_mu has_cmp_mu}/= !mul1r !mulN1r ltr_opp2 in Ei_lt_mu Ej_gt_mu.
pose A' := [predD1 A & i]; pose n' := #|A'|.
have [Dn n_gt0]: n = n'.+1 /\ (n > 0)%N  by rewrite [n](cardD1 i) Ai.
have i'j: j != i by apply: contraTneq Ej_gt_mu => ->; rewrite ltr_gtF.
have{i'j} A'j: j \in A' by rewrite !inE Aj i'j.
have mu_gt0: 0 < mu := ler_lt_trans (Ege0 i Ai) Ei_lt_mu.
rewrite (bigD1 i) // big_andbC (bigD1 j) //= mulrA; set pi := \prod_(k | _) _.
have [-> | nz_pi] := eqVneq pi 0; first by rewrite !mulr0 exprn_gt0.
have{nz_pi} pi_gt0: 0 < pi.
  by rewrite ltr_def nz_pi prodr_ge0 // => k /andP[/andP[_ /Ege0]].
rewrite -/(En i) -/(En j); pose E' := [eta En with j |-> En i + En j - mu].
have E'ge0 k: k \in A' -> E' k *+ n' >= 0.
  case/andP=> /= _ Ak; apply: mulrn_wge0; case: ifP => _; last exact: Ege0.
  by rewrite subr_ge0 ler_paddl ?Ege0 // ltrW.
rewrite -/n Dn in leAm; have{leAm IHm E'ge0}: _ <= _ := IHm _ leAm _ E'ge0.
have ->: \sum_(k in A') E' k = mu *+ n'.
  apply: (addrI mu); rewrite -mulrS -Dn -sumrMnl (bigD1 i Ai) big_andbC /=.
  rewrite !(bigD1 j A'j) /= addrCA eqxx !addrA subrK; congr (_ + _).
  by apply: eq_bigr => k /andP[_ /negPf->].
rewrite prodrMn exprMn_n -/n' ler_pmuln2r ?expn_gt0; last by case: (n').
have ->: \prod_(k in A') E' k = E' j * pi.
  by rewrite (bigD1 j) //=; congr *%R; apply: eq_bigr => k /andP[_ /negPf->].
rewrite -(ler_pmul2l mu_gt0) -exprS -Dn mulrA; apply: ltr_le_trans.
rewrite ltr_pmul2r //= eqxx -addrA mulrDr mulrC -ltr_subl_addl -mulrBl.
by rewrite mulrC ltr_pmul2r ?subr_gt0.
Qed.

(* Polynomial bound. *)

Implicit Type p : {poly R}.

Lemma poly_disk_bound p b : {ub | forall x, `|x| <= b -> `|p.[x]| <= ub}.
Proof.
exists (\sum_(j < size p) `|p`_j| * b ^+ j) => x le_x_b.
rewrite horner_coef (ler_trans (ler_norm_sum _ _ _)) ?ler_sum // => j _.
rewrite normrM normrX ler_wpmul2l ?ler_expn2r ?unfold_in ?normr_ge0 //.
exact: ler_trans (normr_ge0 x) le_x_b.
Qed.

End NumDomainOperationTheory.

Hint Resolve ler_opp2 ltr_opp2 real0 real1 normr_real : core.
Arguments ler_sqr {R} [x y].
Arguments ltr_sqr {R} [x y].
Arguments signr_inj {R} [x1 x2].
Arguments real_ler_normlP {R x y}.
Arguments real_ltr_normlP {R x y}.
Arguments lerif_refl {R x C}.
Arguments mono_in_lerif [R A f C].
Arguments nmono_in_lerif [R A f C].
Arguments mono_lerif [R f C].
Arguments nmono_lerif [R f C].

Section NumDomainMonotonyTheoryForReals.

Variables (R R' : numDomainType) (D : pred R) (f : R -> R') (f' : R -> nat).
Implicit Types (m n p : nat) (x y z : R) (u v w : R').

Lemma real_mono :
  {homo f : x y / x < y} -> {in real &, {mono f : x y / x <= y}}.
Proof.
move=> mf x y xR yR /=; have [lt_xy | le_yx] := real_lerP xR yR.
  by rewrite ltrW_homo.
by rewrite ltr_geF ?mf.
Qed.

Lemma real_nmono :
  {homo f : x y /~ x < y} -> {in real &, {mono f : x y /~ x <= y}}.
Proof.
move=> mf x y xR yR /=; have [lt_xy|le_yx] := real_ltrP xR yR.
  by rewrite ltr_geF ?mf.
by rewrite ltrW_nhomo.
Qed.

Lemma real_mono_in :
    {in D &, {homo f : x y / x < y}} ->
  {in [pred x in D | x \is real] &, {mono f : x y / x <= y}}.
Proof.
move=> Dmf x y /andP[hx xR] /andP[hy yR] /=.
have [lt_xy|le_yx] := real_lerP xR yR; first by rewrite (ltrW_homo_in Dmf).
by rewrite ltr_geF ?Dmf.
Qed.

Lemma real_nmono_in :
    {in D &, {homo f : x y /~ x < y}} ->
  {in [pred x in D | x \is real] &, {mono f : x y /~ x <= y}}.
Proof.
move=> Dmf x y /andP[hx xR] /andP[hy yR] /=.
have [lt_xy|le_yx] := real_ltrP xR yR; last by rewrite (ltrW_nhomo_in Dmf).
by rewrite ltr_geF ?Dmf.
Qed.

Lemma realn_mono : {homo f' : x y / x < y >-> (x < y)%N} ->
  {in real &, {mono f' : x y / x <= y >-> (x <= y)%N}}.
Proof.
move=> mf x y xR yR /=; have [lt_xy | le_yx] := real_lerP xR yR.
  by rewrite ltrnW_homo.
by rewrite ltn_geF ?mf.
Qed.

Lemma realn_nmono : {homo f' : x y / y < x >-> (x < y)%N} ->
  {in real &, {mono f' : x y / y <= x >-> (x <= y)%N}}.
Proof.
move=> mf x y xR yR /=; have [lt_xy|le_yx] := real_ltrP xR yR.
  by rewrite ltn_geF ?mf.
by rewrite ltrnW_nhomo.
Qed.

Lemma realn_mono_in : {in D &, {homo f' : x y / x < y >-> (x < y)%N}} ->
  {in [pred x in D | x \is real] &, {mono f' : x y / x <= y >-> (x <= y)%N}}.
Proof.
move=> Dmf x y /andP[hx xR] /andP[hy yR] /=.
have [lt_xy|le_yx] := real_lerP xR yR; first by rewrite (ltrnW_homo_in Dmf).
by rewrite ltn_geF ?Dmf.
Qed.

Lemma realn_nmono_in : {in D &, {homo f' : x y / y < x >-> (x < y)%N}} ->
  {in [pred x in D | x \is real] &, {mono f' : x y / y <= x >-> (x <= y)%N}}.
Proof.
move=> Dmf x y /andP[hx xR] /andP[hy yR] /=.
have [lt_xy|le_yx] := real_ltrP xR yR; last by rewrite (ltrnW_nhomo_in Dmf).
by rewrite ltn_geF ?Dmf.
Qed.

End NumDomainMonotonyTheoryForReals.

Section FinGroup.

Import GroupScope.

Variables (R : numDomainType) (gT : finGroupType).
Implicit Types G : {group gT}.

Lemma natrG_gt0 G : #|G|%:R > 0 :> R.
Proof. by rewrite ltr0n cardG_gt0. Qed.

Lemma natrG_neq0 G : #|G|%:R != 0 :> R.
Proof. by rewrite gtr_eqF // natrG_gt0. Qed.

Lemma natr_indexg_gt0 G B : #|G : B|%:R > 0 :> R.
Proof. by rewrite ltr0n indexg_gt0. Qed.

Lemma natr_indexg_neq0 G B : #|G : B|%:R != 0 :> R.
Proof. by rewrite gtr_eqF // natr_indexg_gt0. Qed.

End FinGroup.

Section NumFieldTheory.

Variable F : numFieldType.
Implicit Types x y z t : F.

Lemma unitf_gt0 x : 0 < x -> x \is a GRing.unit.
Proof. by move=> hx; rewrite unitfE eq_sym ltr_eqF. Qed.

Lemma unitf_lt0 x : x < 0 -> x \is a GRing.unit.
Proof. by move=> hx; rewrite unitfE ltr_eqF. Qed.

Lemma lef_pinv : {in pos &, {mono (@GRing.inv F) : x y /~ x <= y}}.
Proof. by move=> x y hx hy /=; rewrite ler_pinv ?inE ?unitf_gt0. Qed.

Lemma lef_ninv : {in neg &, {mono (@GRing.inv F) : x y /~ x <= y}}.
Proof. by move=> x y hx hy /=; rewrite ler_ninv ?inE ?unitf_lt0. Qed.

Lemma ltf_pinv : {in pos &, {mono (@GRing.inv F) : x y /~ x < y}}.
Proof. exact: lerW_nmono_in lef_pinv. Qed.

Lemma ltf_ninv: {in neg &, {mono (@GRing.inv F) : x y /~ x < y}}.
Proof. exact: lerW_nmono_in lef_ninv. Qed.

Definition ltef_pinv := (lef_pinv, ltf_pinv).
Definition ltef_ninv := (lef_ninv, ltf_ninv).

Lemma invf_gt1 x : 0 < x -> (1 < x^-1) = (x < 1).
Proof. by move=> x_gt0; rewrite -{1}[1]invr1 ltf_pinv ?posrE ?ltr01. Qed.

Lemma invf_ge1 x : 0 < x -> (1 <= x^-1) = (x <= 1).
Proof. by move=> x_lt0; rewrite -{1}[1]invr1 lef_pinv ?posrE ?ltr01. Qed.

Definition invf_gte1 := (invf_ge1, invf_gt1).

Lemma invf_le1 x : 0 < x -> (x^-1 <= 1) = (1 <= x).
Proof. by move=> x_gt0; rewrite -invf_ge1 ?invr_gt0 // invrK. Qed.

Lemma invf_lt1 x : 0 < x -> (x^-1 < 1) = (1 < x).
Proof. by move=> x_lt0; rewrite -invf_gt1 ?invr_gt0 // invrK. Qed.

Definition invf_lte1 := (invf_le1, invf_lt1).
Definition invf_cp1 := (invf_gte1, invf_lte1).

(* These lemma are all combinations of mono(LR|RL) with ler_[pn]mul2[rl]. *)
Lemma ler_pdivl_mulr z x y : 0 < z -> (x <= y / z) = (x * z <= y).
Proof. by move=> z_gt0; rewrite -(@ler_pmul2r _ z) ?mulfVK ?gtr_eqF. Qed.

Lemma ltr_pdivl_mulr z x y : 0 < z -> (x < y / z) = (x * z < y).
Proof. by move=> z_gt0; rewrite -(@ltr_pmul2r _ z) ?mulfVK ?gtr_eqF. Qed.

Definition lter_pdivl_mulr := (ler_pdivl_mulr, ltr_pdivl_mulr).

Lemma ler_pdivr_mulr z x y : 0 < z -> (y / z <= x) = (y <= x * z).
Proof. by move=> z_gt0; rewrite -(@ler_pmul2r _ z) ?mulfVK ?gtr_eqF. Qed.

Lemma ltr_pdivr_mulr z x y : 0 < z -> (y / z < x) = (y < x * z).
Proof. by move=> z_gt0; rewrite -(@ltr_pmul2r _ z) ?mulfVK ?gtr_eqF. Qed.

Definition lter_pdivr_mulr := (ler_pdivr_mulr, ltr_pdivr_mulr).

Lemma ler_pdivl_mull z x y : 0 < z -> (x <= z^-1 * y) = (z * x <= y).
Proof. by move=> z_gt0; rewrite mulrC ler_pdivl_mulr ?[z * _]mulrC. Qed.

Lemma ltr_pdivl_mull z x y : 0 < z -> (x < z^-1 * y) = (z * x < y).
Proof. by move=> z_gt0; rewrite mulrC ltr_pdivl_mulr ?[z * _]mulrC. Qed.

Definition lter_pdivl_mull := (ler_pdivl_mull, ltr_pdivl_mull).

Lemma ler_pdivr_mull z x y : 0 < z -> (z^-1 * y <= x) = (y <= z * x).
Proof. by move=> z_gt0; rewrite mulrC ler_pdivr_mulr ?[z * _]mulrC. Qed.

Lemma ltr_pdivr_mull z x y : 0 < z -> (z^-1 * y < x) = (y < z * x).
Proof. by move=> z_gt0; rewrite mulrC ltr_pdivr_mulr ?[z * _]mulrC. Qed.

Definition lter_pdivr_mull := (ler_pdivr_mull, ltr_pdivr_mull).

Lemma ler_ndivl_mulr z x y : z < 0 -> (x <= y / z) = (y <= x * z).
Proof. by move=> z_lt0; rewrite -(@ler_nmul2r _ z) ?mulfVK  ?ltr_eqF. Qed.

Lemma ltr_ndivl_mulr z x y : z < 0 -> (x < y / z) = (y < x * z).
Proof. by move=> z_lt0; rewrite -(@ltr_nmul2r _ z) ?mulfVK ?ltr_eqF. Qed.

Definition lter_ndivl_mulr := (ler_ndivl_mulr, ltr_ndivl_mulr).

Lemma ler_ndivr_mulr z x y : z < 0 -> (y / z <= x) = (x * z <= y).
Proof. by move=> z_lt0; rewrite -(@ler_nmul2r _ z) ?mulfVK ?ltr_eqF. Qed.

Lemma ltr_ndivr_mulr z x y : z < 0 -> (y / z < x) = (x * z < y).
Proof. by move=> z_lt0; rewrite -(@ltr_nmul2r _ z) ?mulfVK ?ltr_eqF. Qed.

Definition lter_ndivr_mulr := (ler_ndivr_mulr, ltr_ndivr_mulr).

Lemma ler_ndivl_mull z x y : z < 0 -> (x <= z^-1 * y) = (y <= z * x).
Proof. by move=> z_lt0; rewrite mulrC ler_ndivl_mulr ?[z * _]mulrC. Qed.

Lemma ltr_ndivl_mull z x y : z < 0 -> (x < z^-1 * y) = (y < z * x).
Proof. by move=> z_lt0; rewrite mulrC ltr_ndivl_mulr ?[z * _]mulrC. Qed.

Definition lter_ndivl_mull := (ler_ndivl_mull, ltr_ndivl_mull).

Lemma ler_ndivr_mull z x y : z < 0 -> (z^-1 * y <= x) = (z * x <= y).
Proof. by move=> z_lt0; rewrite mulrC ler_ndivr_mulr ?[z * _]mulrC. Qed.

Lemma ltr_ndivr_mull z x y : z < 0 -> (z^-1 * y < x) = (z * x < y).
Proof. by move=> z_lt0; rewrite mulrC ltr_ndivr_mulr ?[z * _]mulrC. Qed.

Definition lter_ndivr_mull := (ler_ndivr_mull, ltr_ndivr_mull).

Lemma natf_div m d : (d %| m)%N -> (m %/ d)%:R = m%:R / d%:R :> F.
Proof. by apply: char0_natf_div; apply: (@char_num F). Qed.

Lemma normfV : {morph (@norm F) : x / x ^-1}.
Proof.
move=> x /=; have [/normrV //|Nux] := boolP (x \is a GRing.unit).
by rewrite !invr_out // unitfE normr_eq0 -unitfE.
Qed.

Lemma normf_div : {morph (@norm F) : x y / x / y}.
Proof. by move=> x y /=; rewrite normrM normfV. Qed.

Lemma invr_sg x : (sg x)^-1 = sgr x.
Proof. by rewrite !(fun_if GRing.inv) !(invr0, invrN, invr1). Qed.

Lemma sgrV x : sgr x^-1 = sgr x.
Proof. by rewrite /sgr invr_eq0 invr_lt0. Qed.

(* Interval midpoint. *)

Local Notation mid x y := ((x + y) / 2%:R).

Lemma midf_le x y : x <= y -> (x <= mid x y) * (mid x y  <= y).
Proof.
move=> lexy; rewrite ler_pdivl_mulr ?ler_pdivr_mulr ?ltr0Sn //.
by rewrite !mulrDr !mulr1 ler_add2r ler_add2l.
Qed.

Lemma midf_lt x y : x < y -> (x < mid x y) * (mid x y  < y).
Proof.
move=> ltxy; rewrite ltr_pdivl_mulr ?ltr_pdivr_mulr ?ltr0Sn //.
by rewrite !mulrDr !mulr1 ltr_add2r ltr_add2l.
Qed.

Definition midf_lte := (midf_le, midf_lt).

(* The AGM, unscaled but without the nth root. *)

Lemma real_lerif_mean_square x y :
  x \is real -> y \is real -> x * y <= mid (x ^+ 2) (y ^+ 2) ?= iff (x == y).
Proof.
move=> Rx Ry; rewrite -(mono_lerif (ler_pmul2r (ltr_nat F 0 2))).
by rewrite divfK ?pnatr_eq0 // mulr_natr; apply: real_lerif_mean_square_scaled.
Qed.

Lemma real_lerif_AGM2 x y :
  x \is real -> y \is real -> x * y <= mid x y ^+ 2 ?= iff (x == y).
Proof.
move=> Rx Ry; rewrite -(mono_lerif (ler_pmul2r (ltr_nat F 0 4))).
rewrite mulr_natr (natrX F 2 2) -exprMn divfK ?pnatr_eq0 //.
exact: real_lerif_AGM2_scaled.
Qed.

Lemma lerif_AGM (I : finType) (A : pred I) (E : I -> F) :
    let n := #|A| in let mu := (\sum_(i in A) E i) / n%:R in
    {in A, forall i, 0 <= E i} ->
  \prod_(i in A) E i <= mu ^+ n
                     ?= iff [forall i in A, forall j in A, E i == E j].
Proof.
move=> n mu Ege0; have [n0 | n_gt0] := posnP n.
  by rewrite n0 -big_andE !(big_pred0 _ _ _ _ (card0_eq n0)); apply/lerifP.
pose E' i := E i / n%:R.
have defE' i: E' i *+ n = E i by rewrite -mulr_natr divfK ?pnatr_eq0 -?lt0n.
have /lerif_AGM_scaled (i): i \in A -> 0 <= E' i *+ n by rewrite defE' => /Ege0.
rewrite -/n -mulr_suml (eq_bigr _ (in1W defE')); congr (_ <= _ ?= iff _).
by do 2![apply: eq_forallb_in => ? _]; rewrite -(eqr_pmuln2r n_gt0) !defE'.
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
have b_ge0: 0 <= b by rewrite (ler_trans (normr_ge0 q.[1])) ?ub_q ?normr1.
have{b_ge0} ba_ge0: 0 <= b / `|a| by rewrite divr_ge0 ?normr_ge0.
rewrite real_lerNgt ?rpredD ?rpred1 ?ger0_real ?normr_ge0 //.
apply: contraL px0 => lb_x; rewrite rootE.
have x_ge1: 1 <= `|x| by rewrite (ler_trans _ (ltrW lb_x)) // ler_paddl.
have nz_x: x != 0 by rewrite -normr_gt0 (ltr_le_trans ltr01).
rewrite {}Dp // mulf_neq0 ?expf_neq0 // subr_eq0 eq_sym.
have: (b / `|a|) < `|x| by rewrite (ltr_trans _ lb_x) // ltr_spaddr ?ltr01.
apply: contraTneq => /(canRL (divfK nz_x))Dax.
rewrite ltr_pdivr_mulr ?normr_gt0 ?lead_coef_eq0 // mulrC -normrM -{}Dax.
by rewrite ler_gtF // ub_q // normfV invf_le1 ?normr_gt0.
Qed.

Import GroupScope.

Lemma natf_indexg (gT : finGroupType) (G H : {group gT}) :
  H \subset G -> #|G : H|%:R = (#|G|%:R / #|H|%:R)%R :> F.
Proof. by move=> sHG; rewrite -divgS // natf_div ?cardSg. Qed.

End NumFieldTheory.

Section RealDomainTheory.

Hint Resolve lerr : core.

Variable R : realDomainType.
Implicit Types x y z t : R.

Lemma num_real x : x \is real. Proof. exact: num_real. Qed.
Hint Resolve num_real : core.

Lemma ler_total : total (@le R). Proof. by move=> x y; apply: real_leVge. Qed.

Lemma ltr_total x y : x != y -> (x < y) || (y < x).
Proof. by rewrite !ltr_def [_ == y]eq_sym => ->; apply: ler_total. Qed.

Lemma wlog_ler P :
     (forall a b, P b a -> P a b) -> (forall a b, a <= b -> P a b) ->
   forall a b : R, P a b.
Proof. by move=> sP hP a b; apply: real_wlog_ler. Qed.

Lemma wlog_ltr P :
    (forall a, P a a) ->
    (forall a b, (P b a -> P a b)) -> (forall a b, a < b -> P a b) ->
  forall a b : R, P a b.
Proof. by move=> rP sP hP a b; apply: real_wlog_ltr. Qed.

Lemma ltrNge x y : (x < y) = ~~ (y <= x). Proof. exact: real_ltrNge. Qed.

Lemma lerNgt x y : (x <= y) = ~~ (y < x). Proof. exact: real_lerNgt. Qed.

Lemma lerP x y : ler_xor_gt x y `|x - y| `|y - x| (x <= y) (y < x).
Proof. exact: real_lerP. Qed.

Lemma ltrP x y : ltr_xor_ge x y `|x - y| `|y - x| (y <= x) (x < y).
Proof. exact: real_ltrP. Qed.

Lemma ltrgtP x y :
   comparer x y `|x - y| `|y - x| (y == x) (x == y)
                 (x <= y) (y <= x) (x < y) (x > y) .
Proof. exact: real_ltrgtP. Qed.

Lemma ger0P x : ger0_xor_lt0 x `|x| (x < 0) (0 <= x).
Proof. exact: real_ger0P. Qed.

Lemma ler0P x : ler0_xor_gt0 x `|x| (0 < x) (x <= 0).
Proof. exact: real_ler0P. Qed.

Lemma ltrgt0P x :
  comparer0 x `|x| (0 == x) (x == 0) (x <= 0) (0 <= x) (x < 0) (x > 0).
Proof. exact: real_ltrgt0P. Qed.

Lemma neqr_lt x y : (x != y) = (x < y) || (y < x).
Proof. exact: real_neqr_lt. Qed.

Lemma eqr_leLR x y z t :
  (x <= y -> z <= t) -> (y < x -> t < z) -> (x <= y) = (z <= t).
Proof. by move=> *; apply/idP/idP; rewrite // !lerNgt; apply: contra. Qed.

Lemma eqr_leRL x y z t :
  (x <= y -> z <= t) -> (y < x -> t < z) -> (z <= t) = (x <= y).
Proof. by move=> *; symmetry; apply: eqr_leLR. Qed.

Lemma eqr_ltLR x y z t :
  (x < y -> z < t) -> (y <= x -> t <= z) -> (x < y) = (z < t).
Proof. by move=> *; rewrite !ltrNge; congr negb; apply: eqr_leLR. Qed.

Lemma eqr_ltRL x y z t :
  (x < y -> z < t) -> (y <= x -> t <= z) -> (z < t) = (x < y).
Proof. by move=> *; symmetry; apply: eqr_ltLR. Qed.

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

(* sign & norm*)

Lemma mulr_sign_norm x : (-1) ^+ (x < 0)%R * `|x| = x.
Proof. by rewrite real_mulr_sign_norm. Qed.

Lemma mulr_Nsign_norm x : (-1) ^+ (0 < x)%R * `|x| = - x.
Proof. by rewrite real_mulr_Nsign_norm. Qed.

Lemma numEsign x : x = (-1) ^+ (x < 0)%R * `|x|.
Proof. by rewrite -realEsign. Qed.

Lemma numNEsign x : -x = (-1) ^+ (0 < x)%R * `|x|.
Proof. by rewrite -realNEsign. Qed.

Lemma normrEsign x : `|x| = (-1) ^+ (x < 0)%R * x.
Proof. by rewrite -real_normrEsign. Qed.

End RealDomainTheory.

Hint Resolve num_real : core.

Section RealDomainMonotony.

Variables (R : realDomainType) (R' : numDomainType) (D : pred R).
Variables (f : R -> R') (f' : R -> nat).
Implicit Types (m n p : nat) (x y z : R) (u v w : R').

Hint Resolve (@num_real R) : core.

Lemma ler_mono : {homo f : x y / x < y} -> {mono f : x y / x <= y}.
Proof. by move=> mf x y; apply: real_mono. Qed.

Lemma ler_nmono : {homo f : x y /~ x < y} -> {mono f : x y /~ x <= y}.
Proof. by move=> mf x y; apply: real_nmono. Qed.

Lemma ler_mono_in :
  {in D &, {homo f : x y / x < y}} -> {in D &, {mono f : x y / x <= y}}.
Proof.
by move=> mf x y Dx Dy; apply: (real_mono_in mf); rewrite ?inE ?Dx ?Dy /=.
Qed.

Lemma ler_nmono_in :
  {in D &, {homo f : x y /~ x < y}} -> {in D &, {mono f : x y /~ x <= y}}.
Proof.
by move=> mf x y Dx Dy; apply: (real_nmono_in mf); rewrite ?inE ?Dx ?Dy /=.
Qed.

Lemma lern_mono : {homo f' : m n / m < n >-> (m < n)%N} ->
   {mono f' : m n / m <= n >-> (m <= n)%N}.
Proof. by move=> mf x y; apply: realn_mono. Qed.

Lemma lern_nmono : {homo f' : m n / n < m >-> (m < n)%N} ->
  {mono f' : m n / n <= m >-> (m <= n)%N}.
Proof. by move=> mf x y; apply: realn_nmono. Qed.

Lemma lern_mono_in : {in D &, {homo f' : m n / m < n >-> (m < n)%N}} ->
   {in D &, {mono f' : m n / m <= n >-> (m <= n)%N}}.
Proof.
by move=> mf x y Dx Dy; apply: (realn_mono_in mf); rewrite ?inE ?Dx ?Dy /=.
Qed.

Lemma lern_nmono_in : {in D &, {homo f' : m n / n < m >-> (m < n)%N}} ->
  {in D &, {mono f' : m n / n <= m >-> (m <= n)%N}}.
Proof.
by move=> mf x y Dx Dy; apply: (realn_nmono_in mf); rewrite ?inE ?Dx ?Dy /=.
Qed.

End RealDomainMonotony.

Section RealDomainArgExtremum.

Context {R : realDomainType} {I : finType} (i0 : I).
Context (P : pred I) (F : I -> R) (Pi0 : P i0).

Definition arg_minr := extremum <=%R i0 P F.
Definition arg_maxr := extremum >=%R i0 P F.

Lemma arg_minrP: extremum_spec <=%R P F arg_minr.
Proof. by apply: extremumP => //; [apply: ler_trans|apply: ler_total]. Qed.

Lemma arg_maxrP: extremum_spec >=%R P F arg_maxr.
Proof.
apply: extremumP => //; first exact: lerr.
  by move=> ??? /(ler_trans _) le /le.
by move=> ??; apply: ler_total.
Qed.

End RealDomainArgExtremum.

Notation "[ 'arg' 'minr_' ( i < i0 | P ) F ]" :=
    (arg_minr i0 (fun i => P%B) (fun i => F))
  (at level 0, i, i0 at level 10,
   format "[ 'arg'  'minr_' ( i  <  i0  |  P )  F ]") : form_scope.

Notation "[ 'arg' 'minr_' ( i < i0 'in' A ) F ]" :=
    [arg minr_(i < i0 | i \in A) F]
  (at level 0, i, i0 at level 10,
   format "[ 'arg'  'minr_' ( i  <  i0  'in'  A )  F ]") : form_scope.

Notation "[ 'arg' 'minr_' ( i < i0 ) F ]" := [arg minr_(i < i0 | true) F]
  (at level 0, i, i0 at level 10,
   format "[ 'arg'  'minr_' ( i  <  i0 )  F ]") : form_scope.

Notation "[ 'arg' 'maxr_' ( i > i0 | P ) F ]" :=
     (arg_maxr i0 (fun i => P%B) (fun i => F))
  (at level 0, i, i0 at level 10,
   format "[ 'arg'  'maxr_' ( i  >  i0  |  P )  F ]") : form_scope.

Notation "[ 'arg' 'maxr_' ( i > i0 'in' A ) F ]" :=
    [arg maxr_(i > i0 | i \in A) F]
  (at level 0, i, i0 at level 10,
   format "[ 'arg'  'maxr_' ( i  >  i0  'in'  A )  F ]") : form_scope.

Notation "[ 'arg' 'maxr_' ( i > i0 ) F ]" := [arg maxr_(i > i0 | true) F]
  (at level 0, i, i0 at level 10,
   format "[ 'arg'  'maxr_' ( i  >  i0 ) F ]") : form_scope.

Section RealDomainOperations.

(* sgr section *)

Variable R : realDomainType.
Implicit Types x y z t : R.
Hint Resolve (@num_real R) : core.

Lemma sgr_cp0 x :
  ((sg x == 1) = (0 < x)) *
  ((sg x == -1) = (x < 0)) *
  ((sg x == 0) = (x == 0)).
Proof.
rewrite -[1]/((-1) ^+ false) -signrN lt0r lerNgt sgr_def.
case: (x =P 0) => [-> | _]; first by rewrite !(eq_sym 0) !signr_eq0 ltrr eqxx.
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

(* GG: duplicate! *)
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
Proof. by rewrite -sgr_cp0 sgr_id sgr_cp0. Qed.

Lemma sgr_ge0 x : (sgr x >= 0) = (x >= 0).
Proof. by rewrite !lerNgt sgr_lt0. Qed.

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

Lemma ler_normr x y : (x <= `|y|) = (x <= y) || (x <= - y).
Proof. by rewrite lerNgt ltr_norml negb_and -!lerNgt orbC ler_oppr. Qed.

Lemma ltr_normr x y : (x < `|y|) = (x < y) || (x < - y).
Proof. by rewrite ltrNge ler_norml negb_and -!ltrNge orbC ltr_oppr. Qed.

Definition lter_normr := (ler_normr, ltr_normr).

Lemma ler_distl x y e : (`|x - y| <= e) = (y - e <= x <= y + e).
Proof. by rewrite lter_norml !lter_sub_addl. Qed.

Lemma ltr_distl x y e : (`|x - y| < e) = (y - e < x < y + e).
Proof. by rewrite lter_norml !lter_sub_addl. Qed.

Definition lter_distl := (ler_distl, ltr_distl).

Lemma exprn_even_ge0 n x : ~~ odd n -> 0 <= x ^+ n.
Proof. by move=> even_n; rewrite real_exprn_even_ge0 ?num_real. Qed.

Lemma exprn_even_gt0 n x : ~~ odd n -> (0 < x ^+ n) = (n == 0)%N || (x != 0).
Proof. by move=> even_n; rewrite real_exprn_even_gt0 ?num_real. Qed.

Lemma exprn_even_le0 n x : ~~ odd n -> (x ^+ n <= 0) = (n != 0%N) && (x == 0).
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

(* Special lemmas for squares. *)

Lemma sqr_ge0 x : 0 <= x ^+ 2. Proof. by rewrite exprn_even_ge0. Qed.

Lemma sqr_norm_eq1 x : (x ^+ 2 == 1) = (`|x| == 1).
Proof. by rewrite sqrf_eq1 eqr_norml ler01 andbT. Qed.

Lemma lerif_mean_square_scaled x y :
  x * y *+ 2 <= x ^+ 2 + y ^+ 2 ?= iff (x == y).
Proof. exact: real_lerif_mean_square_scaled. Qed.

Lemma lerif_AGM2_scaled x y : x * y *+ 4 <= (x + y) ^+ 2 ?= iff (x == y).
Proof. exact: real_lerif_AGM2_scaled. Qed.

Section MinMax.

(* GG: Many of the first lemmas hold unconditionally, and others hold for    *)
(* the real subset of a general domain.                                      *)
Lemma minrC : @commutative R R min.
Proof. by move=> x y; rewrite /min; case: ltrgtP. Qed.

Lemma minrr : @idempotent R min.
Proof. by move=> x; rewrite /min if_same. Qed.

Lemma minr_l x y : x <= y -> min x y = x.
Proof. by rewrite /minr => ->. Qed.

Lemma minr_r x y : y <= x -> min x y = y.
Proof. by move/minr_l; rewrite minrC. Qed.

Lemma maxrC : @commutative R R max.
Proof. by move=> x y; rewrite /maxr; case: ltrgtP. Qed.

Lemma maxrr : @idempotent R max.
Proof. by move=> x; rewrite /max if_same. Qed.

Lemma maxr_l x y : y <= x -> max x y = x.
Proof. by move=> hxy; rewrite /max hxy. Qed.

Lemma maxr_r x y : x <= y -> max x y = y.
Proof. by move=> hxy; rewrite maxrC maxr_l. Qed.

Lemma addr_min_max x y : min x y + max x y = x + y.
Proof.
case: (lerP x y)=> hxy; first by rewrite maxr_r ?minr_l.
by rewrite maxr_l ?minr_r ?ltrW // addrC.
Qed.

Lemma addr_max_min x y : max x y + min x y = x + y.
Proof. by rewrite addrC addr_min_max. Qed.

Lemma minr_to_max x y : min x y = x + y - max x y.
Proof. by rewrite -[x + y]addr_min_max addrK. Qed.

Lemma maxr_to_min x y : max x y = x + y - min x y.
Proof. by rewrite -[x + y]addr_max_min addrK. Qed.

Lemma minrA x y z : min x (min y z) = min (min x y) z.
Proof.
rewrite /min; case: (lerP y z) => [hyz | /ltrW hyz].
  by case: lerP => hxy; rewrite ?hyz // (@ler_trans _ y).
case: lerP=> hxz; first by rewrite !(ler_trans hxz).
case: (lerP x y)=> hxy; first by rewrite lerNgt hxz.
by case: ltrgtP hyz.
Qed.

Lemma minrCA : @left_commutative R R min.
Proof. by move=> x y z; rewrite !minrA [minr x y]minrC. Qed.

Lemma minrAC : @right_commutative R R min.
Proof. by move=> x y z; rewrite -!minrA [minr y z]minrC. Qed.

Variant minr_spec x y : bool -> bool -> R -> Type :=
| Minr_r of x <= y : minr_spec x y true false x
| Minr_l of y < x : minr_spec x y false true y.

Lemma minrP x y : minr_spec x y (x <= y) (y < x) (min x y).
Proof.
case: lerP=> hxy; first by rewrite minr_l //; constructor.
by rewrite minr_r 1?ltrW //; constructor.
Qed.

Lemma oppr_max x y : - max x y = min (- x) (- y).
Proof.
case: minrP; rewrite lter_opp2 => hxy; first by rewrite maxr_l.
by rewrite maxr_r // ltrW.
Qed.

Lemma oppr_min x y : - min x y = max (- x) (- y).
Proof. by rewrite -[maxr _ _]opprK oppr_max !opprK. Qed.

Lemma maxrA x y z : max x (max y z) = max (max x y) z.
Proof. by apply/eqP; rewrite -eqr_opp !oppr_max minrA. Qed.

Lemma maxrCA : @left_commutative R R max.
Proof. by move=> x y z; rewrite !maxrA [maxr x y]maxrC. Qed.

Lemma maxrAC : @right_commutative R R max.
Proof. by move=> x y z; rewrite -!maxrA [maxr y z]maxrC. Qed.

Variant maxr_spec x y : bool -> bool -> R -> Type :=
| Maxr_r of y <= x : maxr_spec x y true false x
| Maxr_l of x < y : maxr_spec x y false true y.

Lemma maxrP x y : maxr_spec x y (y <= x) (x < y) (maxr x y).
Proof.
case: lerP => hxy; first by rewrite maxr_l //; constructor.
by rewrite maxr_r 1?ltrW //; constructor.
Qed.

Lemma eqr_minl x y : (min x y == x) = (x <= y).
Proof. by case: minrP=> hxy; rewrite ?eqxx // ltr_eqF. Qed.

Lemma eqr_minr x y : (min x y == y) = (y <= x).
Proof. by rewrite minrC eqr_minl. Qed.

Lemma eqr_maxl x y : (max x y == x) = (y <= x).
Proof. by case: maxrP=> hxy; rewrite ?eqxx // eq_sym ltr_eqF. Qed.

Lemma eqr_maxr x y : (max x y == y) = (x <= y).
Proof. by rewrite maxrC eqr_maxl. Qed.

Lemma ler_minr x y z : (x <= min y z) = (x <= y) && (x <= z).
Proof.
case: minrP=> hyz.
  by case: lerP=> hxy //; rewrite (ler_trans _ hyz).
by case: lerP=> hxz; rewrite andbC // (ler_trans hxz) // ltrW.
Qed.

Lemma ler_minl x y z : (min y z <= x) = (y <= x) || (z <= x).
Proof.
case: minrP => hyz.
  case: lerP => hyx //=; symmetry; apply: negbTE.
  by rewrite -ltrNge (@ltr_le_trans _ y).
case: lerP => hzx; rewrite orbC //=; symmetry; apply: negbTE.
by rewrite -ltrNge (@ltr_trans _ z).
Qed.

Lemma ler_maxr x y z : (x <= max y z) = (x <= y) || (x <= z).
Proof. by rewrite -lter_opp2 oppr_max ler_minl !ler_opp2. Qed.

Lemma ler_maxl x y z : (max y z <= x) = (y <= x) && (z <= x).
Proof. by rewrite -lter_opp2 oppr_max ler_minr !ler_opp2. Qed.

Lemma ltr_minr x y z : (x < min y z) = (x < y) && (x < z).
Proof. by rewrite !ltrNge ler_minl negb_or. Qed.

Lemma ltr_minl x y z : (min y z < x) = (y < x) || (z < x).
Proof. by rewrite !ltrNge ler_minr negb_and. Qed.

Lemma ltr_maxr x y z : (x < max y z) = (x < y) || (x < z).
Proof. by rewrite !ltrNge ler_maxl negb_and. Qed.

Lemma ltr_maxl x y z : (max y z < x) = (y < x) && (z < x).
Proof. by rewrite !ltrNge ler_maxr negb_or. Qed.

Definition lter_minr := (ler_minr, ltr_minr).
Definition lter_minl := (ler_minl, ltr_minl).
Definition lter_maxr := (ler_maxr, ltr_maxr).
Definition lter_maxl := (ler_maxl, ltr_maxl).

Lemma addr_minl : @left_distributive R R +%R min.
Proof.
move=> x y z; case: minrP=> hxy; first by rewrite minr_l // ler_add2r.
by rewrite minr_r // ltrW // ltr_add2r.
Qed.

Lemma addr_minr : @right_distributive R R +%R min.
Proof.
move=> x y z; case: minrP=> hxy; first by rewrite minr_l // ler_add2l.
by rewrite minr_r // ltrW // ltr_add2l.
Qed.

Lemma addr_maxl : @left_distributive R R +%R max.
Proof.
move=> x y z; rewrite -[_ + _]opprK opprD oppr_max.
by rewrite addr_minl -!opprD oppr_min !opprK.
Qed.

Lemma addr_maxr : @right_distributive R R +%R max.
Proof.
move=> x y z; rewrite -[_ + _]opprK opprD oppr_max.
by rewrite addr_minr -!opprD oppr_min !opprK.
Qed.

Lemma minrK x y : max (min x y) x = x.
Proof. by case: minrP => hxy; rewrite ?maxrr ?maxr_r // ltrW. Qed.

Lemma minKr x y : min y (max x y) = y.
Proof. by case: maxrP => hxy; rewrite ?minrr ?minr_l. Qed.

Lemma maxr_minl : @left_distributive R R max min.
Proof.
move=> x y z; case: minrP => hxy.
  by case: maxrP => hm; rewrite minr_l // ler_maxr (hxy, lerr) ?orbT.
by case: maxrP => hyz; rewrite minr_r // ler_maxr (ltrW hxy, lerr) ?orbT.
Qed.

Lemma maxr_minr : @right_distributive R R max min.
Proof. by move=> x y z; rewrite maxrC maxr_minl ![_ _ x]maxrC. Qed.

Lemma minr_maxl : @left_distributive R R min max.
Proof.
move=> x y z; rewrite -[min _ _]opprK !oppr_min [- max x y]oppr_max.
by rewrite maxr_minl !(oppr_max, oppr_min, opprK).
Qed.

Lemma minr_maxr : @right_distributive R R min max.
Proof. by move=> x y z; rewrite minrC minr_maxl ![_ _ x]minrC. Qed.

Lemma minr_pmulr x y z : 0 <= x -> x * min y z = min (x * y) (x * z).
Proof.
case: sgrP=> // hx _; first by rewrite hx !mul0r minrr.
case: minrP=> hyz; first by rewrite minr_l // ler_pmul2l.
by rewrite minr_r // ltrW // ltr_pmul2l.
Qed.

Lemma minr_nmulr x y z : x <= 0 -> x * min y z = max (x * y) (x * z).
Proof.
move=> hx; rewrite -[_ * _]opprK -mulNr minr_pmulr ?oppr_cp0 //.
by rewrite oppr_min !mulNr !opprK.
Qed.

Lemma maxr_pmulr x y z : 0 <= x -> x * max y z = max (x * y) (x * z).
Proof.
move=> hx; rewrite -[_ * _]opprK -mulrN oppr_max minr_pmulr //.
by rewrite oppr_min !mulrN !opprK.
Qed.

Lemma maxr_nmulr x y z : x <= 0 -> x * max y z = min (x * y) (x * z).
Proof.
move=> hx; rewrite -[_ * _]opprK -mulrN oppr_max minr_nmulr //.
by rewrite oppr_max !mulrN !opprK.
Qed.

Lemma minr_pmull x y z : 0 <= x -> min y z * x = min (y * x) (z * x).
Proof. by move=> *; rewrite mulrC minr_pmulr // ![_ * x]mulrC. Qed.

Lemma minr_nmull x y z : x <= 0 -> min y z * x = max (y * x) (z * x).
Proof. by move=> *; rewrite mulrC minr_nmulr // ![_ * x]mulrC. Qed.

Lemma maxr_pmull x y z : 0 <= x -> max y z * x = max (y * x) (z * x).
Proof. by move=> *; rewrite mulrC maxr_pmulr // ![_ * x]mulrC. Qed.

Lemma maxr_nmull x y z : x <= 0 -> max y z * x = min (y * x) (z * x).
Proof. by move=> *; rewrite mulrC maxr_nmulr // ![_ * x]mulrC. Qed.

Lemma maxrN x : max x (- x) = `|x|.
Proof.
case: ger0P=> hx; first by rewrite maxr_l // ge0_cp //.
by rewrite maxr_r // le0_cp // ltrW.
Qed.

Lemma maxNr x : max (- x) x = `|x|.
Proof. by rewrite maxrC maxrN. Qed.

Lemma minrN x : min x (- x) = - `|x|.
Proof. by rewrite -[minr _ _]opprK oppr_min opprK maxNr. Qed.

Lemma minNr x : min (- x) x = - `|x|.
Proof. by rewrite -[minr _ _]opprK oppr_min opprK maxrN. Qed.

End MinMax.

Section PolyBounds.

Variable p : {poly R}.

Lemma poly_itv_bound a b : {ub | forall x, a <= x <= b -> `|p.[x]| <= ub}.
Proof.
have [ub le_p_ub] := poly_disk_bound p (Num.max `|a| `|b|).
exists ub => x /andP[le_a_x le_x_b]; rewrite le_p_ub // ler_maxr !ler_normr.
by have [_|_] := ler0P x; rewrite ?ler_opp2 ?le_a_x ?le_x_b orbT.
Qed.

Lemma monic_Cauchy_bound : p \is monic -> {b | forall x, x >= b -> p.[x] > 0}.
Proof.
move/monicP=> mon_p; pose n := (size p - 2)%N.
have [p_le1 | p_gt1] := leqP (size p) 1.
  exists 0 => x _; rewrite (size1_polyC p_le1) hornerC.
  by rewrite -[p`_0]lead_coefC -size1_polyC // mon_p ltr01.
pose lb := \sum_(j < n.+1) `|p`_j|; exists (lb + 1) => x le_ub_x.
have x_ge1: 1 <= x; last have x_gt0 := ltr_le_trans ltr01 x_ge1.
  by rewrite -(ler_add2l lb) ler_paddl ?sumr_ge0 // => j _; apply: normr_ge0.
rewrite horner_coef -(subnK p_gt1) -/n addnS big_ord_recr /= addn1.
rewrite [in p`__]subnSK // subn1 -lead_coefE mon_p mul1r -ltr_subl_addl sub0r.
apply: ler_lt_trans (_ : lb * x ^+ n < _); last first.
  rewrite exprS ltr_pmul2r ?exprn_gt0 ?(ltr_le_trans ltr01) //.
  by rewrite -(ltr_add2r 1) ltr_spaddr ?ltr01.
rewrite -sumrN mulr_suml ler_sum // => j _; apply: ler_trans (ler_norm _) _.
rewrite normrN normrM ler_wpmul2l ?normr_ge0 // normrX.
by rewrite ger0_norm ?(ltrW x_gt0) // ler_weexpn2l ?leq_ord.
Qed.

End PolyBounds.

End RealDomainOperations.

Section RealField.

Variables (F : realFieldType) (x y : F).

Lemma lerif_mean_square : x * y <= (x ^+ 2 + y ^+ 2) / 2%:R ?= iff (x == y).
Proof. by apply: real_lerif_mean_square; apply: num_real. Qed.

Lemma lerif_AGM2 : x * y <= ((x + y) / 2%:R)^+ 2 ?= iff (x == y).
Proof. by apply: real_lerif_AGM2; apply: num_real. Qed.

End RealField.

Section ArchimedeanFieldTheory.

Variables (F : archiFieldType) (x : F).

Lemma archi_boundP : 0 <= x -> x < (bound x)%:R.
Proof. by move/ger0_norm=> {1}<-; rewrite /bound; case: (sigW _). Qed.

Lemma upper_nthrootP i : (bound x <= i)%N -> x < 2%:R ^+ i.
Proof.
rewrite /bound; case: (sigW _) => /= b le_x_b le_b_i.
apply: ler_lt_trans (ler_norm x) (ltr_trans le_x_b _ ).
by rewrite -natrX ltr_nat (leq_ltn_trans le_b_i) // ltn_expl.
Qed.

End ArchimedeanFieldTheory.

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
Proof. by move=> /ltrW; apply: ler0_sqrtr. Qed.

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
case: (sqrtrP a) => // {a} a a_ge0 _; case: (sqrtrP b) => [b_lt0 | {b} b b_ge0].
  by rewrite mulr0 ler0_sqrtr // nmulr_lle0 ?mulr_ge0.
by rewrite mulrACA sqrtr_sqr ger0_norm ?mulr_ge0.
Qed.

Lemma sqrtr0 : sqrt 0 = 0 :> R.
Proof. by move: (sqrtr_sqr 0); rewrite exprS mul0r => ->; rewrite normr0. Qed.

Lemma sqrtr1 : sqrt 1 = 1 :> R.
Proof. by move: (sqrtr_sqr 1); rewrite expr1n => ->; rewrite normr1. Qed.

Lemma sqrtr_eq0 a : (sqrt a == 0) = (a <= 0).
Proof.
case: sqrtrP => [/ltrW ->|b]; first by rewrite eqxx.
case: ltrgt0P => [b_gt0|//|->]; last by rewrite exprS mul0r lerr.
by rewrite ltr_geF ?pmulr_rgt0.
Qed.

Lemma sqrtr_gt0 a : (0 < sqrt a) = (0 < a).
Proof. by rewrite lt0r sqrtr_ge0 sqrtr_eq0 -ltrNge andbT. Qed.

Lemma eqr_sqrt a b : 0 <= a -> 0 <= b -> (sqrt a == sqrt b) = (a == b).
Proof.
move=> a_ge0 b_ge0; apply/eqP/eqP=> [HS|->] //.
by move: (sqr_sqrtr a_ge0); rewrite HS (sqr_sqrtr b_ge0).
Qed.

Lemma ler_wsqrtr : {homo @sqrt R : a b / a <= b}.
Proof.
move=> a b /= le_ab; case: (boolP (0 <= a))=> [pa|]; last first.
  by rewrite -ltrNge; move/ltrW; rewrite -sqrtr_eq0; move/eqP->.
rewrite -(@ler_pexpn2r R 2) ?nnegrE ?sqrtr_ge0 //.
by rewrite !sqr_sqrtr // (ler_trans pa).
Qed.

Lemma ler_psqrt : {in @pos R &, {mono sqrt : a b / a <= b}}.
Proof.
apply: ler_mono_in => x y x_gt0 y_gt0.
rewrite !ltr_neqAle => /andP[neq_xy le_xy].
by rewrite ler_wsqrtr // eqr_sqrt ?ltrW // neq_xy.
Qed.

Lemma ler_sqrt a b : 0 < b -> (sqrt a <= sqrt b) = (a <= b).
Proof.
move=> b_gt0; have [a_le0|a_gt0] := ler0P a; last by rewrite ler_psqrt.
by rewrite ler0_sqrtr // sqrtr_ge0 (ler_trans a_le0) ?ltrW.
Qed.

Lemma ltr_sqrt a b : 0 < b -> (sqrt a < sqrt b) = (a < b).
Proof.
move=> b_gt0; have [a_le0|a_gt0] := ler0P a; last first.
  by rewrite (lerW_mono_in ler_psqrt).
by rewrite ler0_sqrtr // sqrtr_gt0 b_gt0 (ler_lt_trans a_le0).
Qed.

End RealClosedFieldTheory.

Definition conjC {C : numClosedFieldType} : {rmorphism C -> C} :=
 ClosedField.conj_op (ClosedField.conj_mixin (ClosedField.class C)).
Notation "z ^*" := (@conjC _ z) (at level 2, format "z ^*") : ring_scope.

Definition imaginaryC {C : numClosedFieldType} : C :=
 ClosedField.imaginary (ClosedField.conj_mixin (ClosedField.class C)).
Notation "'i" := (@imaginaryC _) (at level 0) : ring_scope.

Section ClosedFieldTheory.

Variable C : numClosedFieldType.
Implicit Types a x y z : C.

Definition normCK x : `|x| ^+ 2 = x * x^*.
Proof. by case: C x => ? [? ? []]. Qed.

Lemma sqrCi : 'i ^+ 2 = -1 :> C.
Proof. by case: C => ? [? ? []]. Qed.

Lemma conjCK : involutive (@conjC C).
Proof.
have JE x : x^* = `|x|^+2 / x.
  have [->|x_neq0] := eqVneq x 0; first by rewrite rmorph0 invr0 mulr0.
  by apply: (canRL (mulfK _)) => //; rewrite mulrC -normCK.
move=> x; have [->|x_neq0] := eqVneq x 0; first by rewrite !rmorph0.
rewrite !JE normrM normfV exprMn normrX normr_id.
rewrite invfM exprVn mulrA -[X in X * _]mulrA -invfM -exprMn.
by rewrite divff ?mul1r ?invrK // !expf_eq0 normr_eq0 //.
Qed.

Let Re2 z := z + z^*.
Definition nnegIm z := (0 <= imaginaryC * (z^* - z)).
Definition argCle y z := nnegIm z ==> nnegIm y && (Re2 z <= Re2 y).

Variant rootC_spec n (x : C) : Type :=
  RootCspec (y : C) of if (n > 0)%N then y ^+ n = x else y = 0
                        & forall z, (n > 0)%N -> z ^+ n = x -> argCle y z.

Fact rootC_subproof n x : rootC_spec n x.
Proof.
have realRe2 u : Re2 u \is Num.real.
  rewrite realEsqr expr2 {2}/Re2 -{2}[u]conjCK addrC -rmorphD -normCK.
  by rewrite exprn_ge0 ?normr_ge0.
have argCle_total : total argCle.
  move=> u v; rewrite /total /argCle.
  by do 2!case: (nnegIm _) => //; rewrite ?orbT //= real_leVge.
have argCle_trans : transitive argCle.
  move=> u v w /implyP geZuv /implyP geZvw; apply/implyP.
  by case/geZvw/andP=> /geZuv/andP[-> geRuv] /ler_trans->.
pose p := 'X^n - (x *+ (n > 0))%:P; have [r0 Dp] := closed_field_poly_normal p.
have sz_p: size p = n.+1.
  rewrite size_addl ?size_polyXn // ltnS size_opp size_polyC mulrn_eq0.
  by case: posnP => //; case: negP.
pose r := sort argCle r0; have r_arg: sorted argCle r by apply: sort_sorted.
have{Dp} Dp: p = \prod_(z <- r) ('X - z%:P).
  rewrite Dp lead_coefE sz_p coefB coefXn coefC -mulrb -mulrnA mulnb lt0n andNb.
  rewrite subr0 eqxx scale1r; apply: eq_big_perm.
  by rewrite perm_eq_sym perm_sort.
have mem_rP z: (n > 0)%N -> reflect (z ^+ n = x) (z \in r).
  move=> n_gt0; rewrite -root_prod_XsubC -Dp rootE !hornerE hornerXn n_gt0.
  by rewrite subr_eq0; apply: eqP.
exists r`_0 => [|z n_gt0 /(mem_rP z n_gt0) r_z].
  have sz_r: size r = n by apply: succn_inj; rewrite -sz_p Dp size_prod_XsubC.
  case: posnP => [n0 | n_gt0]; first by rewrite nth_default // sz_r n0.
  by apply/mem_rP=> //; rewrite mem_nth ?sz_r.
case: {Dp mem_rP}r r_z r_arg => // y r1; rewrite inE => /predU1P[-> _|r1z].
  by apply/implyP=> ->; rewrite lerr.
by move/(order_path_min argCle_trans)/allP->.
Qed.

Definition nthroot n x := let: RootCspec y _ _ := rootC_subproof n x in y.
Notation "n .-root" := (nthroot n) (at level 2, format "n .-root") : ring_core_scope.
Notation "n .-root" := (nthroot n) (only parsing) : ring_scope.
Notation sqrtC := 2.-root.

Definition Re x := (x + x^*) / 2%:R.
Definition Im x := 'i * (x^* - x) / 2%:R.
Notation "'Re z" := (Re z) (at level 10, z at level 8) : ring_scope.
Notation "'Im z" := (Im z) (at level 10, z at level 8) : ring_scope.

Let nz2 : 2%:R != 0 :> C. Proof. by rewrite pnatr_eq0. Qed.

Lemma normCKC x : `|x| ^+ 2 = x^* * x. Proof. by rewrite normCK mulrC. Qed.

Lemma mul_conjC_ge0 x : 0 <= x * x^*.
Proof. by rewrite -normCK exprn_ge0 ?normr_ge0. Qed.

Lemma mul_conjC_gt0 x : (0 < x * x^*) = (x != 0).
Proof.
have [->|x_neq0] := altP eqP; first by rewrite rmorph0 mulr0.
by rewrite -normCK exprn_gt0 ?normr_gt0.
Qed.

Lemma mul_conjC_eq0 x : (x * x^* == 0) = (x == 0).
Proof. by rewrite -normCK expf_eq0 normr_eq0. Qed.

Lemma conjC_ge0 x : (0 <= x^*) = (0 <= x).
Proof.
wlog suffices: x / 0 <= x -> 0 <= x^*.
  by move=> IH; apply/idP/idP=> /IH; rewrite ?conjCK.
rewrite le0r => /predU1P[-> | x_gt0]; first by rewrite rmorph0.
by rewrite -(pmulr_rge0 _ x_gt0) mul_conjC_ge0.
Qed.

Lemma conjC_nat n : (n%:R)^* = n%:R :> C. Proof. exact: rmorph_nat. Qed.
Lemma conjC0 : 0^* = 0 :> C. Proof. exact: rmorph0. Qed.
Lemma conjC1 : 1^* = 1 :> C. Proof. exact: rmorph1. Qed.
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
Proof. by rewrite realEsqr sqrCi oppr_ge0 ltr_geF ?ltr01. Qed.

Lemma neq0Ci : 'i != 0 :> C.
Proof. by apply: contraNneq nonRealCi => ->; apply: real0. Qed.

Lemma normCi : `|'i| = 1 :> C.
Proof.
apply/eqP; rewrite -(@pexpr_eq1 _ _ 2) ?normr_ge0 //.
by rewrite -normrX sqrCi normrN1.
Qed.

Lemma invCi : 'i^-1 = - 'i :> C.
Proof. by rewrite -div1r -[1]opprK -sqrCi mulNr mulfK ?neq0Ci. Qed.

Lemma conjCi : 'i^* = - 'i :> C.
Proof. by rewrite -invCi invC_norm normCi expr1n invr1 mul1r. Qed.

Lemma Crect x : x = 'Re x + 'i * 'Im x.
Proof.
rewrite 2!mulrA -expr2 sqrCi mulN1r opprB -mulrDl addrACA subrr addr0.
by rewrite -mulr2n -mulr_natr mulfK.
Qed.

Lemma Creal_Re x : 'Re x \is real.
Proof. by rewrite CrealE fmorph_div rmorph_nat rmorphD conjCK addrC. Qed.

Lemma Creal_Im x : 'Im x \is real.
Proof.
rewrite CrealE fmorph_div rmorph_nat rmorphM rmorphB conjCK.
by rewrite conjCi -opprB mulrNN.
Qed.
Hint Resolve Creal_Re Creal_Im : core.

Fact Re_is_additive : additive Re.
Proof. by move=> x y; rewrite /Re rmorphB addrACA -opprD mulrBl. Qed.
Canonical Re_additive := Additive Re_is_additive.

Fact Im_is_additive : additive Im.
Proof.
by move=> x y; rewrite /Im rmorphB opprD addrACA -opprD mulrBr mulrBl.
Qed.
Canonical Im_additive := Additive Im_is_additive.

Lemma Creal_ImP z : reflect ('Im z = 0) (z \is real).
Proof.
rewrite CrealE -subr_eq0 -(can_eq (mulKf neq0Ci)) mulr0.
by rewrite -(can_eq (divfK nz2)) mul0r; apply: eqP.
Qed.

Lemma Creal_ReP z : reflect ('Re z = z) (z \in real).
Proof.
rewrite (sameP (Creal_ImP z) eqP) -(can_eq (mulKf neq0Ci)) mulr0.
by rewrite -(inj_eq (addrI ('Re z))) addr0 -Crect eq_sym; apply: eqP.
Qed.

Lemma ReMl : {in real, forall x, {morph Re : z / x * z}}.
Proof.
by move=> x Rx z /=; rewrite /Re rmorphM (conj_Creal Rx) -mulrDr -mulrA.
Qed.

Lemma ReMr : {in real, forall x, {morph Re : z / z * x}}.
Proof. by move=> x Rx z /=; rewrite mulrC ReMl // mulrC. Qed.

Lemma ImMl : {in real, forall x, {morph Im : z / x * z}}.
Proof.
by move=> x Rx z; rewrite /Im rmorphM (conj_Creal Rx) -mulrBr mulrCA !mulrA.
Qed.

Lemma ImMr : {in real, forall x, {morph Im : z / z * x}}.
Proof. by move=> x Rx z /=; rewrite mulrC ImMl // mulrC. Qed.

Lemma Re_i : 'Re 'i = 0. Proof. by rewrite /Re conjCi subrr mul0r. Qed.

Lemma Im_i : 'Im 'i = 1.
Proof.
rewrite /Im conjCi -opprD mulrN -mulr2n mulrnAr ['i * _]sqrCi.
by rewrite mulNrn opprK divff.
Qed.

Lemma Re_conj z : 'Re z^* = 'Re z.
Proof. by rewrite /Re addrC conjCK. Qed.

Lemma Im_conj z : 'Im z^* = - 'Im z.
Proof. by rewrite /Im -mulNr -mulrN opprB conjCK. Qed.

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
by move=> x y Rx Ry; rewrite /= rmorphD rmorphM conjCi mulNr !conj_Creal.
Qed.

Lemma addC_rect x1 y1 x2 y2 :
  (x1 + 'i * y1) + (x2 + 'i * y2) = x1 + x2 + 'i * (y1 + y2).
Proof. by rewrite addrACA -mulrDr. Qed.

Lemma oppC_rect x y : - (x + 'i * y)  = - x + 'i * (- y).
Proof. by rewrite mulrN -opprD. Qed.

Lemma subC_rect x1 y1 x2 y2 :
  (x1 + 'i * y1) - (x2 + 'i * y2) = x1 - x2 + 'i * (y1 - y2).
Proof. by rewrite oppC_rect addC_rect. Qed.

Lemma mulC_rect x1 y1 x2 y2 :
  (x1 + 'i * y1) * (x2 + 'i * y2)
      = x1 * x2 - y1 * y2 + 'i * (x1 * y2 + x2 * y1).
Proof.
rewrite mulrDl !mulrDr mulrCA -!addrA mulrAC -mulrA; congr (_ + _).
by rewrite mulrACA -expr2 sqrCi mulN1r addrA addrC.
Qed.

Lemma normC2_rect :
  {in real &, forall x y, `|x + 'i * y| ^+ 2 = x ^+ 2 + y ^+ 2}.
Proof.
move=> x y Rx Ry; rewrite /= normCK rmorphD rmorphM conjCi !conj_Creal //.
by rewrite mulrC mulNr -subr_sqr exprMn sqrCi mulN1r opprK.
Qed.

Lemma normC2_Re_Im z : `|z| ^+ 2 = 'Re z ^+ 2 + 'Im z ^+ 2.
Proof. by rewrite -normC2_rect -?Crect. Qed.

Lemma invC_rect :
  {in real &, forall x y, (x + 'i * y)^-1  = (x - 'i * y) / (x ^+ 2 + y ^+ 2)}.
Proof.
by move=> x y Rx Ry; rewrite /= invC_norm conjC_rect // mulrC normC2_rect.
Qed.

Lemma lerif_normC_Re_Creal z : `|'Re z| <= `|z| ?= iff (z \is real).
Proof.
rewrite -(mono_in_lerif ler_sqr); try by rewrite qualifE normr_ge0.
rewrite normCK conj_Creal // normC2_Re_Im -expr2.
rewrite addrC -lerif_subLR subrr (sameP (Creal_ImP _) eqP) -sqrf_eq0 eq_sym.
by apply: lerif_eq; rewrite -realEsqr.
Qed.

Lemma lerif_Re_Creal z : 'Re z <= `|z| ?= iff (0 <= z).
Proof.
have ubRe: 'Re z <= `|'Re z| ?= iff (0 <= 'Re z).
  by rewrite ger0_def eq_sym; apply/lerif_eq/real_ler_norm.
congr (_ <= _ ?= iff _): (lerif_trans ubRe (lerif_normC_Re_Creal z)).
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
  rewrite /argCle !dIm ler_pmul2r ?invr_gt0 ?ltr0n //.
  by apply: (iffP implyP) => geZyz /geZyz/andP.
by rewrite /('Im x) pmulr_lge0 ?invr_gt0 ?ltr0n //; congr (0 <= _ * _).
Qed.
(* case Du: sqrCi => [u u2N1] /=. *)
(* have/eqP := u2N1; rewrite -sqrCi eqf_sqr => /pred2P[] //. *)
(* have:= conjCi; rewrite /'i; case_rootC => /= v v2n1 min_v conj_v Duv. *)
(* have{min_v} /idPn[] := min_v u isT u2N1; rewrite negb_imply /nnegIm Du /= Duv. *)
(* rewrite rmorphN conj_v opprK -opprD mulrNN mulNr -mulr2n mulrnAr -expr2 v2n1. *)
(* by rewrite mulNrn opprK ler0n oppr_ge0 (ler_nat _ 2 0). *)


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
apply: contra_eqT (congr1 Re pw_0); rewrite negb_exists => /forallP geRw0.
rewrite raddf_sum raddf0 /= (bigD1 (Ordinal (ltnW n_gt1))) //=.
rewrite (Creal_ReP _ _) ?rpred1 // gtr_eqF ?ltr_paddr ?ltr01 //=.
by apply: sumr_ge0 => i _; rewrite real_lerNgt ?rpred0.
Qed.

Lemma Im_rootC_ge0 n x : (n > 1)%N -> 0 <= 'Im (n.-root x).
Proof.
set y := n.-root x => n_gt1; have n_gt0 := ltnW n_gt1.
apply: wlog_neg; rewrite -real_ltrNge ?rpred0 // => ltIy0.
suffices [z zn_x leI0z]: exists2 z, z ^+ n = x & 'Im z >= 0.
  by rewrite /y; case_rootC => /= y1 _ /(_ z n_gt0 zn_x)/argCleP[].
have [w wn1 ltRw0] := neg_unity_root n_gt1.
wlog leRI0yw: w wn1 ltRw0 / 0 <= 'Re y * 'Im w.
  move=> IHw; have: 'Re y * 'Im w \is real by rewrite rpredM.
  case/real_ger0P=> [|/ltrW leRIyw0]; first exact: IHw.
  apply: (IHw w^*); rewrite ?Re_conj ?Im_conj ?mulrN ?oppr_ge0 //.
  by rewrite -rmorphX wn1 rmorph1.
exists (w * y); first by rewrite exprMn wn1 mul1r rootCK.
rewrite [w]Crect [y]Crect mulC_rect.
by rewrite Im_rect ?rpredD ?rpredN 1?rpredM // addr_ge0 // ltrW ?nmulr_rgt0.
Qed.

Lemma rootC_lt0 n x : (1 < n)%N -> (n.-root x < 0) = false.
Proof.
set y := n.-root x => n_gt1; have n_gt0 := ltnW n_gt1.
apply: negbTE; apply: wlog_neg => /negbNE lt0y; rewrite ler_gtF //.
have Rx: x \is real by rewrite -[x](rootCK n_gt0) rpredX // ltr0_real.
have Re_y: 'Re y = y by apply/Creal_ReP; rewrite ltr0_real.
have [z zn_x leR0z]: exists2 z, z ^+ n = x & 'Re z >= 0.
  have [w wn1 ltRw0] := neg_unity_root n_gt1.
  exists (w * y); first by rewrite exprMn wn1 mul1r rootCK.
  by rewrite ReMr ?ltr0_real // ltrW // nmulr_lgt0.
without loss leI0z: z zn_x leR0z / 'Im z >= 0.
  move=> IHz; have: 'Im z \is real by [].
  case/real_ger0P=> [|/ltrW leIz0]; first exact: IHz.
  apply: (IHz z^*); rewrite ?Re_conj ?Im_conj ?oppr_ge0 //.
  by rewrite -rmorphX zn_x conj_Creal.
by apply: ler_trans leR0z _; rewrite -Re_y ?rootC_Re_max ?ltr0_real.
Qed.

Lemma rootC_ge0 n x : (n > 0)%N -> (0 <= n.-root x) = (0 <= x).
Proof.
set y := n.-root x => n_gt0.
apply/idP/idP=> [/(exprn_ge0 n) | x_ge0]; first by rewrite rootCK.
rewrite -(ger_lerif (lerif_Re_Creal y)).
have Ray: `|y| \is real by apply: normr_real.
rewrite -(Creal_ReP _ Ray) rootC_Re_max ?(Creal_ImP _ Ray) //.
by rewrite -normrX rootCK // ger0_norm.
Qed.

Lemma rootC_gt0 n x : (n > 0)%N -> (n.-root x > 0) = (x > 0).
Proof. by move=> n_gt0; rewrite !lt0r rootC_ge0 ?rootC_eq0. Qed.

Lemma rootC_le0 n x : (1 < n)%N -> (n.-root x <= 0) = (x == 0).
Proof.
by move=> n_gt1; rewrite ler_eqVlt rootC_lt0 // orbF rootC_eq0 1?ltnW.
Qed.

Lemma ler_rootCl n : (n > 0)%N -> {in Num.nneg, {mono n.-root : x y / x <= y}}.
Proof.
move=> n_gt0 x x_ge0 y; have [y_ge0 | not_y_ge0] := boolP (0 <= y).
  by rewrite -(ler_pexpn2r n_gt0) ?qualifE ?rootC_ge0 ?rootCK.
rewrite (contraNF (@ler_trans _ _ 0 _ _)) ?rootC_ge0 //.
by rewrite (contraNF (ler_trans x_ge0)).
Qed.

Lemma ler_rootC n : (n > 0)%N -> {in Num.nneg &, {mono n.-root : x y / x <= y}}.
Proof. by move=> n_gt0 x y x_ge0 _; apply: ler_rootCl. Qed.

Lemma ltr_rootCl n : (n > 0)%N -> {in Num.nneg, {mono n.-root : x y / x < y}}.
Proof. by move=> n_gt0 x x_ge0 y; rewrite !ltr_def ler_rootCl ?eqr_rootC. Qed.

Lemma ltr_rootC n : (n > 0)%N -> {in Num.nneg &, {mono n.-root : x y / x < y}}.
Proof. by move/ler_rootC/lerW_mono_in. Qed.

Lemma exprCK n x : (0 < n)%N -> 0 <= x -> n.-root (x ^+ n) = x.
Proof.
move=> n_gt0 x_ge0; apply/eqP.
by rewrite -(eqr_expn2 n_gt0) ?rootC_ge0 ?exprn_ge0 ?rootCK.
Qed.

Lemma norm_rootC n x : `|n.-root x| = n.-root `|x|.
Proof.
have [-> | n_gt0] := posnP n; first by rewrite !root0C normr0.
apply/eqP; rewrite -(eqr_expn2 n_gt0) ?rootC_ge0 ?normr_ge0 //.
by rewrite -normrX !rootCK.
Qed.

Lemma rootCX n x k : (n > 0)%N -> 0 <= x -> n.-root (x ^+ k) = n.-root x ^+ k.
Proof.
move=> n_gt0 x_ge0; apply/eqP.
by rewrite -(eqr_expn2 n_gt0) ?(exprn_ge0, rootC_ge0) // 1?exprAC !rootCK.
Qed.

Lemma rootC1 n : (n > 0)%N -> n.-root 1 = 1.
Proof. by move/(rootCX 0)/(_ ler01). Qed.

Lemma rootCpX n x k : (k > 0)%N -> 0 <= x -> n.-root (x ^+ k) = n.-root x ^+ k.
Proof.
by case: n => [|n] k_gt0; [rewrite !root0C expr0n gtn_eqF | apply: rootCX].
Qed.

Lemma rootCV n x : (n > 0)%N -> 0 <= x -> n.-root x^-1 = (n.-root x)^-1.
Proof.
move=> n_gt0 x_ge0; apply/eqP.
by rewrite -(eqr_expn2 n_gt0) ?(invr_ge0, rootC_ge0) // !exprVn !rootCK.
Qed.

Lemma rootC_eq1 n x : (n > 0)%N -> (n.-root x == 1) = (x == 1).
Proof. by move=> n_gt0; rewrite -{1}(rootC1 n_gt0) eqr_rootC. Qed.

Lemma rootC_ge1 n x : (n > 0)%N -> (n.-root x >= 1) = (x >= 1).
Proof.
by move=> n_gt0; rewrite -{1}(rootC1 n_gt0) ler_rootCl // qualifE ler01.
Qed.

Lemma rootC_gt1 n x : (n > 0)%N -> (n.-root x > 1) = (x > 1).
Proof. by move=> n_gt0; rewrite !ltr_def rootC_eq1 ?rootC_ge1. Qed.

Lemma rootC_le1 n x : (n > 0)%N -> 0 <= x -> (n.-root x <= 1) = (x <= 1).
Proof. by move=> n_gt0 x_ge0; rewrite -{1}(rootC1 n_gt0) ler_rootCl. Qed.

Lemma rootC_lt1 n x : (n > 0)%N -> 0 <= x -> (n.-root x < 1) = (x < 1).
Proof. by move=> n_gt0 x_ge0; rewrite !ltr_neqAle rootC_eq1 ?rootC_le1. Qed.

Lemma rootCMl n x z : 0 <= x -> n.-root (x * z) = n.-root x * n.-root z.
Proof.
rewrite le0r => /predU1P[-> | x_gt0]; first by rewrite !(mul0r, rootC0).
have [| n_gt1 | ->] := ltngtP n 1; last by rewrite !root1C.
  by case: n => //; rewrite !root0C mul0r.
have [x_ge0 n_gt0] := (ltrW x_gt0, ltnW n_gt1).
have nx_gt0: 0 < n.-root x by rewrite rootC_gt0.
have Rnx: n.-root x \is real by rewrite ger0_real ?ltrW.
apply: eqC_semipolar; last 1 first; try apply/eqP.
- by rewrite ImMl // !(Im_rootC_ge0, mulr_ge0, rootC_ge0).
- by rewrite -(eqr_expn2 n_gt0) ?normr_ge0 // -!normrX exprMn !rootCK.
rewrite eqr_le; apply/andP; split; last first.
  rewrite rootC_Re_max ?exprMn ?rootCK ?ImMl //.
  by rewrite mulr_ge0 ?Im_rootC_ge0 ?ltrW.
rewrite -[n.-root _](mulVKf (negbT (gtr_eqF nx_gt0))) !(ReMl Rnx) //.
rewrite ler_pmul2l // rootC_Re_max ?exprMn ?exprVn ?rootCK ?mulKf ?gtr_eqF //.
by rewrite ImMl ?rpredV // mulr_ge0 ?invr_ge0 ?Im_rootC_ge0 ?ltrW.
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

Lemma lerif_rootC_AGM (I : finType) (A : pred I) (n := #|A|) E :
    {in A, forall i, 0 <= E i} ->
  n.-root (\prod_(i in A) E i) <= (\sum_(i in A) E i) / n%:R
                             ?= iff [forall i in A, forall j in A, E i == E j].
Proof.
move=> Ege0; have [n0 | n_gt0] := posnP n.
  rewrite n0 root0C invr0 mulr0; apply/lerif_refl/forall_inP=> i.
  by rewrite (card0_eq n0).
rewrite -(mono_in_lerif (ler_pexpn2r n_gt0)) ?rootCK //=; first 1 last.
- by rewrite qualifE rootC_ge0 // prodr_ge0.
- by rewrite rpred_div ?rpred_nat ?rpred_sum.
exact: lerif_AGM.
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
apply: sqrCK; rewrite -real_lerNgt ?rpred0 // in not_gt0x;
apply/Creal_ImP/ler_anti;
by rewrite leI0x -oppr_ge0 -raddfN -defNx Im_rootC_ge0.
Qed.

Lemma normC_def x : `|x| = sqrtC (x * x^*).
Proof. by rewrite -normCK sqrCK ?normr_ge0. Qed.

Lemma norm_conjC x : `|x^*| = `|x|.
Proof. by rewrite !normC_def conjCK mulrC. Qed.

Lemma normC_rect :
  {in real &, forall x y, `|x + 'i * y| = sqrtC (x ^+ 2 + y ^+ 2)}.
Proof. by move=> x y Rx Ry; rewrite /= normC_def -normCK normC2_rect. Qed.

Lemma normC_Re_Im z : `|z| = sqrtC ('Re z ^+ 2 + 'Im z ^+ 2).
Proof. by rewrite normC_def -normCK normC2_Re_Im. Qed.

(* Norm sum (in)equalities. *)

Lemma normC_add_eq x y :
    `|x + y| = `|x| + `|y| ->
  {t : C | `|t| == 1 & (x, y) = (`|x| * t, `|y| * t)}.
Proof.
move=> lin_xy; apply: sig2_eqW; pose u z := if z == 0 then 1 else z / `|z|.
have uE z: (`|u z| = 1) * (`|z| * u z = z).
  rewrite /u; have [->|nz_z] := altP eqP; first by rewrite normr0 normr1 mul0r.
  by rewrite normf_div normr_id mulrCA divff ?mulr1 ?normr_eq0.
have [->|nz_x] := eqVneq x 0; first by exists (u y); rewrite uE ?normr0 ?mul0r.
exists (u x); rewrite uE // /u (negPf nz_x); congr (_ , _).
have{lin_xy} def2xy: `|x| * `|y| *+ 2 = x * y ^* + y * x ^*.
  apply/(addrI (x * x^*))/(addIr (y * y^*)); rewrite -2!{1}normCK -sqrrD.
  by rewrite addrA -addrA -!mulrDr -mulrDl -rmorphD -normCK lin_xy.
have def_xy: x * y^* = y * x^*.
  apply/eqP; rewrite -subr_eq0 -[_ == 0](@expf_eq0 _ _ 2).
  rewrite (canRL (subrK _) (subr_sqrDB _ _)) opprK -def2xy exprMn_n exprMn.
  by rewrite mulrN mulrAC mulrA -mulrA mulrACA -!normCK mulNrn addNr.
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
  apply/eqP; rewrite eqr_le ler_norm_add -(ler_add2r z) -addrA -norm_sumF addrA.
  by rewrite (ler_trans (ler_norm_add _ _)) // ler_add2l ler_norm_sum.
by case/normC_add_eq=> k _ [/(canLR (mulKf nzFi)) <-]; rewrite -(mulrC (F i)).
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
have posG i: P i -> 0 <= G i by move/leFG; apply: ler_trans; apply: normr_ge0.
have norm_sumG: `|sumG| = sumG by rewrite ger0_norm ?sumr_ge0.
have norm_sumF: `|sumF| = \sum_(i | P i) `|F i|.
  apply/eqP; rewrite eqr_le ler_norm_sum eq_sumFG norm_sumG -subr_ge0 -sumrB.
  by rewrite sumr_ge0 // => i Pi; rewrite subr_ge0 ?leFG.
have [t _ defF] := normC_sum_eq norm_sumF.
have [/(psumr_eq0P posG) G0 i Pi | nz_sumG] := eqVneq sumG 0.
  by apply/eqP; rewrite G0 // -normr_eq0 eqr_le normr_ge0 -(G0 i Pi) leFG.
have t1: t = 1.
  apply: (mulfI nz_sumG); rewrite mulr1 -{1}norm_sumG -eq_sumFG norm_sumF.
  by rewrite mulr_suml -(eq_bigr _ defF).
have /psumr_eq0P eqFG i: P i -> 0 <= G i - F i.
  by move=> Pi; rewrite subr_ge0 defF // t1 mulr1 leFG.
move=> i /eqFG/(canRL (subrK _))->; rewrite ?add0r //.
by rewrite sumrB -/sumF eq_sumFG subrr.
Qed.

Lemma normC_sub_eq x y :
  `|x - y| = `|x| - `|y| -> {t | `|t| == 1 & (x, y) = (`|x| * t, `|y| * t)}.
Proof.
rewrite -{-1}(subrK y x) => /(canLR (subrK _))/esym-Dx; rewrite Dx.
by have [t ? [Dxy Dy]] := normC_add_eq Dx; exists t; rewrite // mulrDl -Dxy -Dy.
Qed.

End ClosedFieldTheory.

Notation "n .-root" := (@nthroot _ n)
  (at level 2, format "n .-root") : ring_scope.
Notation sqrtC := 2.-root.
Notation "'i" := (@imaginaryC _) (at level 0) : ring_scope.
Notation "'Re z" := (Re z) (at level 10, z at level 8) : ring_scope.
Notation "'Im z" := (Im z) (at level 10, z at level 8) : ring_scope.

Arguments conjCK {C} x.
Arguments sqrCK {C} [x] le0x.
Arguments sqrCK_P {C x}.

End Theory.

Module RealMixin.

Section RealMixins.

Variables (R : idomainType) (le : rel R) (lt : rel R) (norm : R -> R).
Local Infix "<=" := le.
Local Infix "<" := lt.
Local Notation "`| x |" := (norm x) : ring_scope.

Section LeMixin.

Hypothesis le0_add : forall x y, 0 <= x -> 0 <= y -> 0 <= x + y.
Hypothesis le0_mul : forall x y, 0 <= x -> 0 <= y -> 0 <= x * y.
Hypothesis le0_anti : forall x, 0 <= x -> x <= 0 -> x = 0.
Hypothesis sub_ge0  : forall x y, (0 <= y - x) = (x <= y).
Hypothesis le0_total : forall x, (0 <= x) || (x <= 0).
Hypothesis normN: forall x, `|- x| = `|x|.
Hypothesis ge0_norm : forall x, 0 <= x -> `|x| = x.
Hypothesis lt_def : forall x y, (x < y) = (y != x) && (x <= y).

Let le0N x : (0 <= - x) = (x <= 0). Proof. by rewrite -sub0r sub_ge0. Qed.
Let leN_total x : 0 <= x \/ 0 <= - x.
Proof. by apply/orP; rewrite le0N le0_total. Qed.

Let le00 : (0 <= 0). Proof. by have:= le0_total 0; rewrite orbb. Qed.
Let le01 : (0 <= 1).
Proof.
by case/orP: (le0_total 1)=> // ?; rewrite -[1]mul1r -mulrNN le0_mul ?le0N.
Qed.

Fact lt0_add x y : 0 < x -> 0 < y -> 0 < x + y.
Proof.
rewrite !lt_def => /andP[x_neq0 l0x] /andP[y_neq0 l0y]; rewrite le0_add //.
rewrite andbT addr_eq0; apply: contraNneq x_neq0 => hxy.
by rewrite [x]le0_anti // hxy -le0N opprK.
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

Lemma le_total x y : (x <= y) || (y <= x).
Proof. by rewrite -sub_ge0 -opprB le0N orbC -sub_ge0 le0_total. Qed.

Definition Le :=
  Mixin le_normD lt0_add eq0_norm (in2W le_total) normM le_def lt_def.

Lemma Real (R' : numDomainType) & phant R' :
  R' = NumDomainType R Le -> real_axiom R'.
Proof. by move->. Qed.

End LeMixin.

Section LtMixin.

Hypothesis lt0_add : forall x y, 0 < x -> 0 < y -> 0 < x + y.
Hypothesis lt0_mul : forall x y, 0 < x -> 0 < y -> 0 < x * y.
Hypothesis lt0_ngt0  : forall x,  0 < x -> ~~ (x < 0).
Hypothesis sub_gt0  : forall x y, (0 < y - x) = (x < y).
Hypothesis lt0_total : forall x, x != 0 -> (0 < x) || (x < 0).
Hypothesis normN : forall x, `|- x| = `|x|.
Hypothesis ge0_norm : forall x, 0 <= x -> `|x| = x.
Hypothesis le_def : forall x y, (x <= y) = (y == x) || (x < y).

Fact le0_add x y : 0 <= x -> 0 <= y -> 0 <= x + y.
Proof.
rewrite !le_def => /predU1P[->|x_gt0]; first by rewrite add0r.
by case/predU1P=> [->|y_gt0]; rewrite ?addr0 ?x_gt0 ?lt0_add // orbT.
Qed.

Fact le0_mul x y : 0 <= x -> 0 <= y -> 0 <= x * y.
Proof.
rewrite !le_def => /predU1P[->|x_gt0]; first by rewrite mul0r eqxx.
by case/predU1P=> [->|y_gt0]; rewrite ?mulr0 ?eqxx // orbC lt0_mul.
Qed.

Fact le0_anti x : 0 <= x -> x <= 0 -> x = 0.
Proof. by rewrite !le_def => /predU1P[] // /lt0_ngt0/negPf-> /predU1P[]. Qed.

Fact sub_ge0  x y : (0 <= y - x) = (x <= y).
Proof. by rewrite !le_def subr_eq0 sub_gt0. Qed.

Fact lt_def x y : (x < y) = (y != x) && (x <= y).
Proof.
rewrite le_def; case: eqP => //= ->; rewrite -sub_gt0 subrr.
by apply/idP=> lt00; case/negP: (lt0_ngt0 lt00).
Qed.

Fact le0_total x : (0 <= x) || (x <= 0).
Proof. by rewrite !le_def [0 == _]eq_sym; have [|/lt0_total] := altP eqP. Qed.

Definition Lt :=
  Le le0_add le0_mul le0_anti sub_ge0 le0_total normN ge0_norm lt_def.

End LtMixin.

End RealMixins.

End RealMixin.

End Num.

Export Num.NumDomain.Exports Num.NumField.Exports Num.ClosedField.Exports.
Export Num.RealDomain.Exports Num.RealField.Exports.
Export Num.ArchimedeanField.Exports Num.RealClosedField.Exports.
Export Num.Syntax Num.PredInstances.

Notation RealLeMixin := Num.RealMixin.Le.
Notation RealLtMixin := Num.RealMixin.Lt.
Notation RealLeAxiom R := (Num.RealMixin.Real (Phant R) (erefl _)).
Notation ImaginaryMixin := Num.ClosedField.ImaginaryMixin.

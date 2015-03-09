(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
Require Import bigop ssralg finalg zmodp matrix mxalgebra.
Require Import poly polydiv mxpoly generic_quotient ring_quotient closed_field.
Require Import ssrint rat.

(*****************************************************************************)
(* This file clones part of ssralg hierachy for countable types; it does not *)
(* cover the left module / algebra interfaces, providing only                *)
(*          countZmodType == countable zmodType interface.                   *)
(*          countRingType == countable ringType interface.                   *)
(*       countComRingType == countable comRingType interface.                *)
(*      countUnitRingType == countable unitRingType interface.               *)
(*   countComUnitRingType == countable comUnitRingType interface.            *)
(*       countIdomainType == countable idomainType interface.                *)
(*         countFieldType == countable fieldType interface.                  *)
(*      countDecFieldType == countable decFieldType interface.               *)
(*   countClosedFieldType == countable closedFieldType interface.            *)
(* The interface cloning syntax is extended to these structures              *)
(*   [countZmodType of M] == countZmodType structure for an M that has both  *)
(*                           zmodType and countType structures.              *)
(*                    ... etc                                                *)
(* This file provides constructions for both simple extension and algebraic  *)
(* closure of countable fields.                                              *) 
(*****************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory CodeSeq.

Module CountRing.

Local Notation mixin_of T := (Countable.mixin_of T).

Section Generic.

(* Implicits *)
Variables (type base_type : Type) (class_of base_of : Type -> Type).
Variable base_sort : base_type -> Type.

(* Explicits *)
Variable Pack : forall T, class_of T -> Type -> type.
Variable Class : forall T, base_of T -> mixin_of T -> class_of T.
Variable base_class : forall bT, base_of (base_sort bT).

Definition gen_pack T :=
  fun bT b & phant_id (base_class bT) b =>
  fun fT c m & phant_id (Countable.class fT) (Countable.Class c m) =>
  Pack (@Class T b m) T.

End Generic.

Implicit Arguments gen_pack [type base_type class_of base_of base_sort].
Local Notation cnt_ c := (@Countable.Class _ c c).
Local Notation do_pack pack T := (pack T _ _ id _ _ _ id).
Import GRing.Theory.

Module Zmodule.

Section ClassDef.

Record class_of M :=
  Class { base : GRing.Zmodule.class_of M; mixin : mixin_of M }.
Local Coercion base : class_of >-> GRing.Zmodule.class_of.
Local Coercion mixin : class_of >-> mixin_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Definition pack := gen_pack Pack Class GRing.Zmodule.class.
Variable cT : type.
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition countType := @Countable.Pack cT (cnt_ xclass) xT.
Definition zmodType := @GRing.Zmodule.Pack cT xclass xT.

Definition join_countType := @Countable.Pack zmodType (cnt_ xclass) xT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> GRing.Zmodule.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion countType : type >-> Countable.type.
Canonical countType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Canonical join_countType.
Notation countZmodType := type.
Notation "[ 'countZmodType' 'of' T ]" := (do_pack pack T)
  (at level 0, format "[ 'countZmodType'  'of'  T ]") : form_scope.
End Exports.

End Zmodule.
Import Zmodule.Exports.

Module Ring.

Section ClassDef.

Record class_of R := Class { base : GRing.Ring.class_of R; mixin : mixin_of R }.
Definition base2 R (c : class_of R) := Zmodule.Class (base c) (mixin c).
Local Coercion base : class_of >-> GRing.Ring.class_of.
Local Coercion base2 : class_of >-> Zmodule.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Definition pack := gen_pack Pack Class GRing.Ring.class.
Variable cT : type.
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition countType := @Countable.Pack cT (cnt_ xclass) xT.
Definition zmodType := @GRing.Zmodule.Pack cT xclass cT.
Definition countZmodType := @Zmodule.Pack cT xclass xT.
Definition ringType := @GRing.Ring.Pack cT xclass xT.
Definition join_countType := @Countable.Pack ringType (cnt_ xclass) xT.
Definition join_countZmodType := @Zmodule.Pack ringType xclass xT.

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> GRing.Ring.class_of.
Coercion base2 : class_of >-> Zmodule.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion countType : type >-> Countable.type.
Canonical countType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion countZmodType : type >-> Zmodule.type.
Canonical countZmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Canonical join_countType.
Canonical join_countZmodType.
Notation countRingType := type.
Notation "[ 'countRingType' 'of' T ]" := (do_pack pack T)
  (at level 0, format "[ 'countRingType'  'of'  T ]") : form_scope.
End Exports.

End Ring.
Import Ring.Exports.

Module ComRing.

Section ClassDef.

Record class_of R :=
  Class { base : GRing.ComRing.class_of R; mixin : mixin_of R }.
Definition base2 R (c : class_of R) := Ring.Class (base c) (mixin c).
Local Coercion base : class_of >-> GRing.ComRing.class_of.
Local Coercion base2 : class_of >-> Ring.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Definition pack := gen_pack Pack Class GRing.ComRing.class.
Variable cT : type.
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition countType := @Countable.Pack cT (cnt_ xclass) xT.
Definition zmodType := @GRing.Zmodule.Pack cT xclass xT.
Definition countZmodType := @Zmodule.Pack cT xclass xT.
Definition ringType := @GRing.Ring.Pack cT xclass xT.
Definition countRingType := @Ring.Pack cT xclass xT.
Definition comRingType := @GRing.ComRing.Pack cT xclass xT.
Definition join_countType := @Countable.Pack comRingType (cnt_ xclass) xT.
Definition join_countZmodType := @Zmodule.Pack comRingType xclass xT.
Definition join_countRingType := @Ring.Pack comRingType xclass xT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> GRing.ComRing.class_of.
Coercion base2 : class_of >-> Ring.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion countType : type >-> Countable.type.
Canonical countType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion countZmodType : type >-> Zmodule.type.
Canonical countZmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion countRingType : type >-> Ring.type.
Canonical countRingType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical comRingType.
Canonical join_countType.
Canonical join_countZmodType.
Canonical join_countRingType.
Notation countComRingType := CountRing.ComRing.type.
Notation "[ 'countComRingType' 'of' T ]" := (do_pack pack T)
  (at level 0, format "[ 'countComRingType'  'of'  T ]") : form_scope.
End Exports.

End ComRing.
Import ComRing.Exports.

Module UnitRing.

Section ClassDef.

Record class_of R :=
  Class { base : GRing.UnitRing.class_of R; mixin : mixin_of R }.
Definition base2 R (c : class_of R) := Ring.Class (base c) (mixin c).
Local Coercion base : class_of >-> GRing.UnitRing.class_of.
Local Coercion base2 : class_of >-> Ring.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Definition pack := gen_pack Pack Class GRing.UnitRing.class.
Variable cT : type.
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition countType := @Countable.Pack cT (cnt_ xclass) xT.
Definition zmodType := @GRing.Zmodule.Pack cT xclass xT.
Definition countZmodType := @Zmodule.Pack cT xclass xT.
Definition ringType := @GRing.Ring.Pack cT xclass xT.
Definition countRingType := @Ring.Pack cT xclass xT.
Definition unitRingType := @GRing.UnitRing.Pack cT xclass xT.

Definition join_countType := @Countable.Pack unitRingType (cnt_ xclass) xT.
Definition join_countZmodType := @Zmodule.Pack unitRingType xclass xT.
Definition join_countRingType := @Ring.Pack unitRingType xclass xT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> GRing.UnitRing.class_of.
Coercion base2 : class_of >-> Ring.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion countType : type >-> Countable.type.
Canonical countType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion countZmodType : type >-> Zmodule.type.
Canonical countZmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion countRingType : type >-> Ring.type.
Canonical countRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical unitRingType.
Canonical join_countType.
Canonical join_countZmodType.
Canonical join_countRingType.
Notation countUnitRingType := CountRing.UnitRing.type.
Notation "[ 'countUnitRingType' 'of' T ]" := (do_pack pack T)
  (at level 0, format "[ 'countUnitRingType'  'of'  T ]") : form_scope.
End Exports.

End UnitRing.
Import UnitRing.Exports.

Module ComUnitRing.

Section ClassDef.

Record class_of R :=
  Class { base : GRing.ComUnitRing.class_of R; mixin : mixin_of R }.
Definition base2 R (c : class_of R) := ComRing.Class (base c) (mixin c).
Definition base3 R (c : class_of R) := @UnitRing.Class R (base c) (mixin c).
Local Coercion base : class_of >-> GRing.ComUnitRing.class_of.
Local Coercion base2 : class_of >-> ComRing.class_of.
Local Coercion base3 : class_of >-> UnitRing.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Definition pack := gen_pack Pack Class GRing.ComUnitRing.class.
Variable cT : type.
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition countType := @Countable.Pack cT (cnt_ xclass) xT.
Definition zmodType := @GRing.Zmodule.Pack cT xclass xT.
Definition countZmodType := @Zmodule.Pack cT xclass xT.
Definition ringType := @GRing.Ring.Pack cT xclass xT.
Definition countRingType := @Ring.Pack cT xclass xT.
Definition comRingType := @GRing.ComRing.Pack cT xclass xT.
Definition countComRingType := @ComRing.Pack cT xclass xT.
Definition unitRingType := @GRing.UnitRing.Pack cT xclass xT.
Definition countUnitRingType := @UnitRing.Pack cT xclass xT.
Definition comUnitRingType := @GRing.ComUnitRing.Pack cT xclass xT.

Definition join_countType := @Countable.Pack comUnitRingType (cnt_ xclass) xT.
Definition join_countZmodType := @Zmodule.Pack comUnitRingType xclass xT.
Definition join_countRingType := @Ring.Pack comUnitRingType xclass xT.
Definition join_countComRingType := @ComRing.Pack comUnitRingType xclass xT.
Definition join_countUnitRingType := @UnitRing.Pack comUnitRingType xclass xT.
Definition ujoin_countComRingType := @ComRing.Pack unitRingType xclass xT.
Definition cjoin_countUnitRingType := @UnitRing.Pack comRingType xclass xT.
Definition ccjoin_countUnitRingType :=
  @UnitRing.Pack countComRingType xclass xT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> GRing.ComUnitRing.class_of.
Coercion base2 : class_of >-> ComRing.class_of.
Coercion base3 : class_of >-> UnitRing.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion countType : type >-> Countable.type.
Canonical countType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion countZmodType : type >-> Zmodule.type.
Canonical countZmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion countRingType : type >-> Ring.type.
Canonical countRingType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical comRingType.
Coercion countComRingType : type >-> ComRing.type.
Canonical countComRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical unitRingType.
Coercion countUnitRingType : type >-> UnitRing.type.
Canonical countUnitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical comUnitRingType.
Canonical join_countType.
Canonical join_countZmodType.
Canonical join_countRingType.
Canonical join_countComRingType.
Canonical join_countUnitRingType.
Canonical ujoin_countComRingType.
Canonical cjoin_countUnitRingType.
Canonical ccjoin_countUnitRingType.
Notation countComUnitRingType := CountRing.ComUnitRing.type.
Notation "[ 'countComUnitRingType' 'of' T ]" := (do_pack pack T)
  (at level 0, format "[ 'countComUnitRingType'  'of'  T ]") : form_scope.
End Exports.

End ComUnitRing.
Import ComUnitRing.Exports.

Module IntegralDomain.

Section ClassDef.

Record class_of R :=
  Class { base : GRing.IntegralDomain.class_of R; mixin : mixin_of R }.
Definition base2 R (c : class_of R) := ComUnitRing.Class (base c) (mixin c).
Local Coercion base : class_of >-> GRing.IntegralDomain.class_of.
Local Coercion base2 : class_of >-> ComUnitRing.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Definition pack := gen_pack Pack Class GRing.IntegralDomain.class.
Variable cT : type.
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition countType := @Countable.Pack cT (cnt_ xclass) xT.
Definition zmodType := @GRing.Zmodule.Pack cT xclass xT.
Definition countZmodType := @Zmodule.Pack cT xclass xT.
Definition ringType := @GRing.Ring.Pack cT xclass xT.
Definition countRingType := @Ring.Pack cT xclass xT.
Definition comRingType := @GRing.ComRing.Pack cT xclass xT.
Definition countComRingType := @ComRing.Pack cT xclass xT.
Definition unitRingType := @GRing.UnitRing.Pack cT xclass xT.
Definition countUnitRingType := @UnitRing.Pack cT xclass xT.
Definition comUnitRingType := @GRing.ComUnitRing.Pack cT xclass xT.
Definition countComUnitRingType := @ComUnitRing.Pack cT xclass xT.
Definition idomainType := @GRing.IntegralDomain.Pack cT xclass xT.

Definition join_countType := @Countable.Pack idomainType (cnt_ xclass) xT.
Definition join_countZmodType := @Zmodule.Pack idomainType xclass xT.
Definition join_countRingType := @Ring.Pack idomainType xclass xT.
Definition join_countUnitRingType := @UnitRing.Pack idomainType xclass xT.
Definition join_countComRingType := @ComRing.Pack idomainType xclass xT.
Definition join_countComUnitRingType := @ComUnitRing.Pack idomainType xclass xT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> GRing.IntegralDomain.class_of.
Coercion base2 : class_of >-> ComUnitRing.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion countType : type >-> Countable.type.
Canonical countType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion countZmodType : type >-> Zmodule.type.
Canonical countZmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion countRingType : type >-> Ring.type.
Canonical countRingType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical comRingType.
Coercion countComRingType : type >-> ComRing.type.
Canonical countComRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical unitRingType.
Coercion countUnitRingType : type >-> UnitRing.type.
Canonical countUnitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical comUnitRingType.
Coercion countComUnitRingType : type >-> ComUnitRing.type.
Canonical countComUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical idomainType.
Canonical join_countType.
Canonical join_countZmodType.
Canonical join_countRingType.
Canonical join_countComRingType.
Canonical join_countUnitRingType.
Canonical join_countComUnitRingType.
Notation countIdomainType := CountRing.IntegralDomain.type.
Notation "[ 'countIdomainType' 'of' T ]" := (do_pack pack T)
  (at level 0, format "[ 'countIdomainType'  'of'  T ]") : form_scope.
End Exports.

End IntegralDomain.
Import IntegralDomain.Exports.

Module Field.

Section ClassDef.

Record class_of R :=
  Class { base : GRing.Field.class_of R; mixin : mixin_of R }.
Definition base2 R (c : class_of R) := IntegralDomain.Class (base c) (mixin c).
Local Coercion base : class_of >-> GRing.Field.class_of.
Local Coercion base2 : class_of >-> IntegralDomain.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Definition pack := gen_pack Pack Class GRing.Field.class.
Variable cT : type.
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition countType := @Countable.Pack cT (cnt_ xclass) xT.
Definition zmodType := @GRing.Zmodule.Pack cT xclass xT.
Definition countZmodType := @Zmodule.Pack cT xclass xT.
Definition ringType := @GRing.Ring.Pack cT xclass xT.
Definition countRingType := @Ring.Pack cT xclass xT.
Definition comRingType := @GRing.ComRing.Pack cT xclass xT.
Definition countComRingType := @ComRing.Pack cT xclass xT.
Definition unitRingType := @GRing.UnitRing.Pack cT xclass xT.
Definition countUnitRingType := @UnitRing.Pack cT xclass xT.
Definition comUnitRingType := @GRing.ComUnitRing.Pack cT xclass xT.
Definition countComUnitRingType := @ComUnitRing.Pack cT xclass xT.
Definition idomainType := @GRing.IntegralDomain.Pack cT xclass xT.
Definition countIdomainType := @IntegralDomain.Pack cT xclass xT.
Definition fieldType := @GRing.Field.Pack cT xclass xT.

Definition join_countType := @Countable.Pack fieldType (cnt_ xclass) xT.
Definition join_countZmodType := @Zmodule.Pack fieldType xclass xT.
Definition join_countRingType := @Ring.Pack fieldType xclass xT.
Definition join_countUnitRingType := @UnitRing.Pack fieldType xclass xT.
Definition join_countComRingType := @ComRing.Pack fieldType xclass xT.
Definition join_countComUnitRingType := @ComUnitRing.Pack fieldType xclass xT.
Definition join_countIdomainType := @IntegralDomain.Pack fieldType xclass xT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> GRing.Field.class_of.
Coercion base2 : class_of >-> IntegralDomain.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion countType : type >-> Countable.type.
Canonical countType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion countZmodType : type >-> Zmodule.type.
Canonical countZmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion countRingType : type >-> Ring.type.
Canonical countRingType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical comRingType.
Coercion countComRingType : type >-> ComRing.type.
Canonical countComRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical unitRingType.
Coercion countUnitRingType : type >-> UnitRing.type.
Canonical countUnitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical comUnitRingType.
Coercion countComUnitRingType : type >-> ComUnitRing.type.
Canonical countComUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical idomainType.
Coercion countIdomainType : type >-> IntegralDomain.type.
Canonical countIdomainType.
Coercion fieldType : type >-> GRing.Field.type.
Canonical fieldType.
Canonical join_countType.
Canonical join_countZmodType.
Canonical join_countRingType.
Canonical join_countComRingType.
Canonical join_countUnitRingType.
Canonical join_countComUnitRingType.
Canonical join_countIdomainType.
Notation countFieldType := CountRing.Field.type.
Notation "[ 'countFieldType' 'of' T ]" := (do_pack pack T)
  (at level 0, format "[ 'countFieldType'  'of'  T ]") : form_scope.
End Exports.

End Field.
Import Field.Exports.

Module DecidableField.

Section ClassDef.

Record class_of R :=
  Class { base : GRing.DecidableField.class_of R; mixin : mixin_of R }.
Definition base2 R (c : class_of R) := Field.Class (base c) (mixin c).
Local Coercion base : class_of >-> GRing.DecidableField.class_of.
Local Coercion base2 : class_of >-> Field.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Definition pack := gen_pack Pack Class GRing.DecidableField.class.
Variable cT : type.
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition countType := @Countable.Pack cT (cnt_ xclass) xT.
Definition zmodType := @GRing.Zmodule.Pack cT xclass xT.
Definition countZmodType := @Zmodule.Pack cT xclass xT.
Definition ringType := @GRing.Ring.Pack cT xclass xT.
Definition countRingType := @Ring.Pack cT xclass xT.
Definition comRingType := @GRing.ComRing.Pack cT xclass xT.
Definition countComRingType := @ComRing.Pack cT xclass xT.
Definition unitRingType := @GRing.UnitRing.Pack cT xclass xT.
Definition countUnitRingType := @UnitRing.Pack cT xclass xT.
Definition comUnitRingType := @GRing.ComUnitRing.Pack cT xclass xT.
Definition countComUnitRingType := @ComUnitRing.Pack cT xclass xT.
Definition idomainType := @GRing.IntegralDomain.Pack cT xclass xT.
Definition countIdomainType := @IntegralDomain.Pack cT xclass xT.
Definition fieldType := @GRing.Field.Pack cT xclass xT.
Definition countFieldType := @Field.Pack cT xclass xT.
Definition decFieldType := @GRing.DecidableField.Pack cT xclass xT.

Definition join_countType := @Countable.Pack decFieldType (cnt_ xclass) xT.
Definition join_countZmodType := @Zmodule.Pack decFieldType xclass xT.
Definition join_countRingType := @Ring.Pack decFieldType xclass xT.
Definition join_countUnitRingType := @UnitRing.Pack decFieldType xclass xT.
Definition join_countComRingType := @ComRing.Pack decFieldType xclass xT.
Definition join_countComUnitRingType :=
  @ComUnitRing.Pack decFieldType xclass xT.
Definition join_countIdomainType := @IntegralDomain.Pack decFieldType xclass xT.
Definition join_countFieldType := @Field.Pack decFieldType xclass xT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> GRing.DecidableField.class_of.
Coercion base2 : class_of >-> Field.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion countType : type >-> Countable.type.
Canonical countType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion countZmodType : type >-> Zmodule.type.
Canonical countZmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion countRingType : type >-> Ring.type.
Canonical countRingType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical comRingType.
Coercion countComRingType : type >-> ComRing.type.
Canonical countComRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical unitRingType.
Coercion countUnitRingType : type >-> UnitRing.type.
Canonical countUnitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical comUnitRingType.
Coercion countComUnitRingType : type >-> ComUnitRing.type.
Canonical countComUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical idomainType.
Coercion countIdomainType : type >-> IntegralDomain.type.
Canonical countIdomainType.
Coercion fieldType : type >-> GRing.Field.type.
Canonical fieldType.
Coercion countFieldType : type >-> Field.type.
Canonical countFieldType.
Coercion decFieldType : type >-> GRing.DecidableField.type.
Canonical decFieldType.
Canonical join_countType.
Canonical join_countZmodType.
Canonical join_countRingType.
Canonical join_countComRingType.
Canonical join_countUnitRingType.
Canonical join_countComUnitRingType.
Canonical join_countIdomainType.
Canonical join_countFieldType.
Notation countDecFieldType := CountRing.DecidableField.type.
Notation "[ 'countDecFieldType' 'of' T ]" := (do_pack pack T)
  (at level 0, format "[ 'countDecFieldType'  'of'  T ]") : form_scope.
End Exports.

End DecidableField.
Import DecidableField.Exports.

Module ClosedField.

Section ClassDef.

Record class_of R :=
  Class { base : GRing.ClosedField.class_of R; mixin : mixin_of R }.
Definition base2 R (c : class_of R) := DecidableField.Class (base c) (mixin c).
Local Coercion base : class_of >-> GRing.ClosedField.class_of.
Local Coercion base2 : class_of >-> DecidableField.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Definition pack := gen_pack Pack Class GRing.ClosedField.class.
Variable cT : type.
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition countType := @Countable.Pack cT (cnt_ xclass) xT.
Definition zmodType := @GRing.Zmodule.Pack cT xclass xT.
Definition countZmodType := @Zmodule.Pack cT xclass xT.
Definition ringType := @GRing.Ring.Pack cT xclass xT.
Definition countRingType := @Ring.Pack cT xclass xT.
Definition comRingType := @GRing.ComRing.Pack cT xclass xT.
Definition countComRingType := @ComRing.Pack cT xclass xT.
Definition unitRingType := @GRing.UnitRing.Pack cT xclass xT.
Definition countUnitRingType := @UnitRing.Pack cT xclass xT.
Definition comUnitRingType := @GRing.ComUnitRing.Pack cT xclass xT.
Definition countComUnitRingType := @ComUnitRing.Pack cT xclass xT.
Definition idomainType := @GRing.IntegralDomain.Pack cT xclass xT.
Definition countIdomainType := @IntegralDomain.Pack cT xclass xT.
Definition fieldType := @GRing.Field.Pack cT xclass xT.
Definition countFieldType := @Field.Pack cT xclass xT.
Definition decFieldType := @GRing.DecidableField.Pack cT xclass xT.
Definition countDecFieldType := @DecidableField.Pack cT xclass xT.
Definition closedFieldType := @GRing.ClosedField.Pack cT xclass xT.

Definition join_countType := @Countable.Pack closedFieldType (cnt_ xclass) xT.
Definition join_countZmodType := @Zmodule.Pack closedFieldType xclass xT.
Definition join_countRingType := @Ring.Pack closedFieldType xclass xT.
Definition join_countUnitRingType := @UnitRing.Pack closedFieldType xclass xT.
Definition join_countComRingType := @ComRing.Pack closedFieldType xclass xT.
Definition join_countComUnitRingType :=
  @ComUnitRing.Pack closedFieldType xclass xT.
Definition join_countIdomainType :=
  @IntegralDomain.Pack closedFieldType xclass xT.
Definition join_countFieldType := @Field.Pack closedFieldType xclass xT.
Definition join_countDecFieldType :=
  @DecidableField.Pack closedFieldType xclass xT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> GRing.ClosedField.class_of.
Coercion base2 : class_of >-> DecidableField.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion countType : type >-> Countable.type.
Canonical countType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion countZmodType : type >-> Zmodule.type.
Canonical countZmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion countRingType : type >-> Ring.type.
Canonical countRingType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical comRingType.
Coercion countComRingType : type >-> ComRing.type.
Canonical countComRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical unitRingType.
Coercion countUnitRingType : type >-> UnitRing.type.
Canonical countUnitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical comUnitRingType.
Coercion countComUnitRingType : type >-> ComUnitRing.type.
Canonical countComUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical idomainType.
Coercion fieldType : type >-> GRing.Field.type.
Canonical fieldType.
Coercion countFieldType : type >-> Field.type.
Canonical countFieldType.
Coercion decFieldType : type >-> GRing.DecidableField.type.
Canonical decFieldType.
Coercion countDecFieldType : type >-> DecidableField.type.
Canonical countDecFieldType.
Coercion closedFieldType : type >-> GRing.ClosedField.type.
Canonical closedFieldType.
Canonical join_countType.
Canonical join_countZmodType.
Canonical join_countRingType.
Canonical join_countComRingType.
Canonical join_countUnitRingType.
Canonical join_countComUnitRingType.
Canonical join_countIdomainType.
Canonical join_countFieldType.
Canonical join_countDecFieldType.
Notation countClosedFieldType := CountRing.ClosedField.type.
Notation "[ 'countClosedFieldType' 'of' T ]" := (do_pack pack T)
  (at level 0, format "[ 'countClosedFieldType'  'of'  T ]") : form_scope.
End Exports.

End ClosedField.
Import ClosedField.Exports.

End CountRing.

Import CountRing.
Export Zmodule.Exports Ring.Exports ComRing.Exports UnitRing.Exports.
Export ComUnitRing.Exports IntegralDomain.Exports.
Export Field.Exports DecidableField.Exports ClosedField.Exports.

Require Import poly polydiv generic_quotient ring_quotient.
Require Import mxpoly polyXY.
Import GRing.Theory.
Require Import closed_field.

Canonical Zp_countZmodType m := [countZmodType of 'I_m.+1].
Canonical Zp_countRingType m := [countRingType of 'I_m.+2].
Canonical Zp_countComRingType m := [countComRingType of 'I_m.+2].
Canonical Zp_countUnitRingType m := [countUnitRingType of 'I_m.+2].
Canonical Zp_countComUnitRingType m := [countComUnitRingType of 'I_m.+2].
Canonical Fp_countIdomainType p := [countIdomainType of 'F_p].
Canonical Fp_countFieldType p := [countFieldType of 'F_p].
Canonical Fp_countDecFieldType p := [countDecFieldType of 'F_p].

Canonical matrix_countZmodType (M : countZmodType) m n :=
  [countZmodType of 'M[M]_(m, n)].
Canonical matrix_countRingType (R : countRingType) n :=
  [countRingType of 'M[R]_n.+1].
Canonical matrix_countUnitRingType (R : countComUnitRingType) n :=
  [countUnitRingType of 'M[R]_n.+1].

Definition poly_countMixin (R : countRingType) :=
  [countMixin of polynomial R by <:].
Canonical polynomial_countType R := CountType _ (poly_countMixin R).
Canonical poly_countType (R : countRingType) := [countType of {poly R}].
Canonical polynomial_countZmodType (R : countRingType) :=
  [countZmodType of polynomial R].
Canonical poly_countZmodType (R : countRingType) := [countZmodType of {poly R}].
Canonical polynomial_countRingType (R : countRingType) :=
  [countRingType of polynomial R].
Canonical poly_countRingType (R : countRingType) := [countRingType of {poly R}].
Canonical polynomial_countComRingType (R : countComRingType) :=
  [countComRingType of polynomial R].
Canonical poly_countComRingType (R : countComRingType) :=
  [countComRingType of {poly R}].
Canonical polynomial_countUnitRingType (R : countIdomainType) :=
  [countUnitRingType of polynomial R].
Canonical poly_countUnitRingType (R : countIdomainType) :=
  [countUnitRingType of {poly R}].
Canonical polynomial_countComUnitRingType (R : countIdomainType) :=
  [countComUnitRingType of polynomial R].
Canonical poly_countComUnitRingType (R : countIdomainType) :=
  [countComUnitRingType of {poly R}].
Canonical polynomial_countIdomainType (R : countIdomainType) :=
  [countIdomainType of polynomial R].
Canonical poly_countIdomainType (R : countIdomainType) :=
  [countIdomainType of {poly R}].

Canonical int_countZmodType := [countZmodType of int].
Canonical int_countRingType := [countRingType of int].
Canonical int_countComRingType := [countComRingType of int].
Canonical int_countUnitRingType := [countUnitRingType of int].
Canonical int_countComUnitRingType := [countComUnitRingType of int].
Canonical int_countIdomainType := [countIdomainType of int].

Canonical rat_countZmodType := [countZmodType of rat].
Canonical rat_countRingType := [countRingType of rat].
Canonical rat_countComRingType := [countComRingType of rat].
Canonical rat_countUnitRingType := [countUnitRingType of rat].
Canonical rat_countComUnitRingType := [countComUnitRingType of rat].
Canonical rat_countIdomainType := [countIdomainType of rat].
Canonical rat_countFieldType := [countFieldType of rat].

Lemma countable_field_extension (F : countFieldType) (p : {poly F}) :
    size p > 1 ->
  {E : countFieldType & {FtoE : {rmorphism F -> E} &
  {w : E | root (map_poly FtoE p) w
         & forall u : E, exists q, u = (map_poly FtoE q).[w]}}}.
Proof.
pose fix d i :=
  if i is i1.+1 then
    let d1 := oapp (gcdp (d i1)) 0 (unpickle i1) in
    if size d1 > 1 then d1 else d i1
  else p.
move=> p_gt1; have sz_d i: size (d i) > 1 by elim: i => //= i IHi; case: ifP.
have dv_d i j: i <= j -> d j %| d i.
  move/subnK <-; elim: {j}(j - i)%N => //= j IHj; case: ifP => //=.
  case: (unpickle _) => /= [q _|]; last by rewrite size_poly0.
  exact: dvdp_trans (dvdp_gcdl _ _) IHj.
pose I : pred {poly F} := [pred q | d (pickle q).+1 %| q].
have I'co q i: q \notin I -> i > pickle q -> coprimep q (d i).
  rewrite inE => I'q /dv_d/coprimep_dvdl-> //; apply: contraR I'q.
  rewrite coprimep_sym /coprimep /= pickleK /= neq_ltn.
  case: ifP => [_ _| ->]; first exact: dvdp_gcdr.
  rewrite orbF ltnS leqn0 size_poly_eq0 gcdp_eq0 -size_poly_eq0.
  by rewrite -leqn0 leqNgt ltnW //.
have memI q: reflect (exists i, d i %| q) (q \in I).
  apply: (iffP idP) => [|[i dv_di_q]]; first by exists (pickle q).+1.
  have [le_i_q | /I'co i_co_q] := leqP i (pickle q).
    rewrite inE /= pickleK /=; case: ifP => _; first exact: dvdp_gcdr.
    exact: dvdp_trans (dv_d _ _ le_i_q) dv_di_q.
  apply: contraR i_co_q _.
  by rewrite /coprimep (eqp_size (dvdp_gcd_idr dv_di_q)) neq_ltn sz_d orbT.
have I_ideal : idealr_closed I.
  split=> [||a q1 q2 Iq1 Iq2]; first exact: dvdp0.
    by apply/memI=> [[i /idPn[]]]; rewrite dvdp1 neq_ltn sz_d orbT.
  apply/memI; exists (maxn (pickle q1).+1 (pickle q2).+1); apply: dvdp_add.
    by apply: dvdp_mull; apply: dvdp_trans Iq1; apply/dv_d/leq_maxl.
  by apply: dvdp_trans Iq2; apply/dv_d/leq_maxr.
pose Iaddkey := GRing.Pred.Add (DefaultPredKey I) I_ideal.
pose Iidkey := MkIdeal (GRing.Pred.Zmod Iaddkey I_ideal) I_ideal.
pose E := ComRingType _ (@Quotient.mulqC _ _ _ (KeyedPred Iidkey)).
pose PtoE : {rmorphism {poly F} -> E} := [rmorphism of \pi_E%qT : {poly F} -> E].
have PtoEd i: PtoE (d i) = 0.
  by apply/eqP; rewrite piE Quotient.equivE subr0; apply/memI; exists i.
pose Einv (z : E) (q := repr z) (dq := d (pickle q).+1) :=
  let q_unitP := Bezout_eq1_coprimepP q dq in
  if q_unitP is ReflectT ex_uv then PtoE (sval (sig_eqW ex_uv)).1 else 0.
have Einv0: Einv 0 = 0.
  rewrite /Einv; case: Bezout_eq1_coprimepP => // ex_uv.
  case/negP: (oner_neq0 E); rewrite piE -[_ 1]/(PtoE 1); have [uv <-] := ex_uv.
  by rewrite rmorphD !rmorphM PtoEd /= reprK !mulr0 addr0.
have EmulV: GRing.Field.axiom Einv.
  rewrite /Einv=> z nz_z; case: Bezout_eq1_coprimepP => [ex_uv |]; last first.
    move/Bezout_eq1_coprimepP; rewrite I'co //.
    by rewrite piE -{1}[z]reprK -Quotient.idealrBE subr0 in nz_z.
  apply/eqP; case: sig_eqW => {ex_uv} [uv uv1]; set i := _.+1 in uv1 *.
  rewrite piE /= -[z]reprK -(rmorphM PtoE) -Quotient.idealrBE.
  by rewrite -uv1 opprD addNKr -mulNr; apply/memI; exists i; exact: dvdp_mull.
pose EringU := [comUnitRingType of UnitRingType _ (FieldUnitMixin EmulV Einv0)].
have Eunitf := @FieldMixin _ _ EmulV Einv0.
pose Efield := FieldType (IdomainType EringU (FieldIdomainMixin Eunitf)) Eunitf.
pose Ecount := CountType Efield (CanCountMixin (@reprK _ _)).
pose FtoE := [rmorphism of PtoE \o polyC]; pose w : E := PtoE 'X.
have defPtoE q: (map_poly FtoE q).[w] = PtoE q.
  by rewrite map_poly_comp horner_map [_.['X]]comp_polyXr.
exists [countFieldType of Ecount], FtoE, w => [|u].
  by rewrite /root defPtoE (PtoEd 0%N).
by exists (repr u); rewrite defPtoE /= reprK.
Qed.

Lemma countable_algebraic_closure (F : countFieldType) :
  {K : countClosedFieldType & {FtoK : {rmorphism F -> K} | integralRange FtoK}}.
Proof.
pose minXp (R : ringType) (p : {poly R}) := if size p > 1 then p else 'X.
have minXp_gt1 R p: size (minXp R p) > 1.
  by rewrite /minXp; case: ifP => // _; rewrite size_polyX.
have minXpE (R : ringType) (p : {poly R}) : size p > 1 -> minXp R p = p.
  by rewrite /minXp => ->.
have ext1 p := countable_field_extension (minXp_gt1 _ p).
pose ext1fT E p := tag (ext1 E p).
pose ext1to E p : {rmorphism _ -> ext1fT E p} := tag (tagged (ext1 E p)).
pose ext1w E p : ext1fT E p := s2val (tagged (tagged (ext1 E p))).
have ext1root E p: root (map_poly (ext1to E p) (minXp E p)) (ext1w E p).
  by rewrite /ext1w; case: (tagged (tagged (ext1 E p))).
have ext1gen E p u: {q | u = (map_poly (ext1to E p) q).[ext1w E p]}.
  by apply: sig_eqW; rewrite /ext1w; case: (tagged (tagged (ext1 E p))) u.
pose pExtEnum (E : countFieldType) := nat -> {poly E}.
pose Ext := {E : countFieldType & pExtEnum E}; pose MkExt : Ext := Tagged _ _.
pose EtoInc (E : Ext) i := ext1to (tag E) (tagged E i).
pose incEp E i j :=
  let v := map_poly (EtoInc E i) (tagged E j) in
  if decode j is [:: i1; k] then
    if i1 == i then odflt v (unpickle k) else v
  else v. 
pose fix E_ i := if i is i1.+1 then MkExt _ (incEp (E_ i1) i1) else MkExt F \0.
pose E i := tag (E_ i); pose Krep := {i : nat & E i}.
pose fix toEadd i k : {rmorphism E i -> E (k + i)%N} :=
  if k is k1.+1 then [rmorphism of EtoInc _ (k1 + i)%N \o toEadd _ _]
  else [rmorphism of idfun].
pose toE i j (le_ij : i <= j) :=
  ecast j {rmorphism E i -> E j} (subnK le_ij) (toEadd i (j - i)%N).
have toEeq i le_ii: toE i i le_ii =1 id.
  by rewrite /toE; move: (subnK _); rewrite subnn => ?; rewrite eq_axiomK.
have toEleS i j leij leiSj z: toE i j.+1 leiSj z = EtoInc _ _ (toE i j leij z).
  rewrite /toE; move: (j - i)%N {leij leiSj}(subnK _) (subnK _) => k.
  by case: j /; rewrite (addnK i k.+1) => eq_kk; rewrite [eq_kk]eq_axiomK.
have toEirr := congr1 ((toE _ _)^~ _) (bool_irrelevance _ _).
have toEtrans j i k leij lejk leik z:
  toE i k leik z = toE j k lejk (toE i j leij z).
- elim: k leik lejk => [|k IHk] leiSk lejSk.
    by case: j => // in leij lejSk *; rewrite toEeq.
  have:= lejSk; rewrite {1}leq_eqVlt ltnS => /predU1P[Dk | lejk].
    by rewrite -Dk in leiSk lejSk *; rewrite toEeq.
  by have leik := leq_trans leij lejk; rewrite !toEleS -IHk.
have [leMl leMr] := (leq_maxl, leq_maxr); pose le_max := (leq_max, leqnn, orbT).
pose pairK (x y : Krep) (m := maxn _ _) :=
  (toE _ m (leMl _ _) (tagged x), toE _ m (leMr _ _) (tagged y)).
pose eqKrep x y := prod_curry (@eq_op _) (pairK x y).
have eqKrefl : reflexive eqKrep by move=> z; apply/eqP; apply: toEirr.
have eqKsym : symmetric eqKrep.
  move=> z1 z2; rewrite {1}/eqKrep /= eq_sym; move: (leMl _ _) (leMr _ _).
  by rewrite maxnC => lez1m lez2m; congr (_ == _); apply: toEirr.
have eqKtrans : transitive eqKrep.
  rewrite /eqKrep /= => z2 z1 z3 /eqP eq_z12 /eqP eq_z23.
  rewrite -(inj_eq (fmorph_inj (toE _ _ (leMr (tag z2) _)))).
  rewrite -!toEtrans ?le_max // maxnCA maxnA => lez3m lez1m.
  rewrite {lez1m}(toEtrans (maxn (tag z1) (tag z2))) // {}eq_z12.
  do [rewrite -toEtrans ?le_max // -maxnA => lez2m] in lez3m *.
  by rewrite (toEtrans (maxn (tag z2) (tag z3))) // eq_z23 -toEtrans.
pose K := {eq_quot (EquivRel _  eqKrefl eqKsym eqKtrans)}%qT.
have cntK : Countable.mixin_of K := CanCountMixin (@reprK _ _).
pose EtoKrep i (x : E i) : K := \pi%qT (Tagged E x).
have [EtoK piEtoK]: {EtoK | forall i, EtoKrep i =1 EtoK i} by exists EtoKrep.
pose FtoK := EtoK 0%N; rewrite {}/EtoKrep in piEtoK.
have eqEtoK i j x y:
  toE i _ (leMl i j) x = toE j _ (leMr i j) y -> EtoK i x = EtoK j y.
- by move/eqP=> eq_xy; rewrite -!piEtoK; apply/eqmodP.
have toEtoK j i leij x : EtoK j (toE i j leij x) = EtoK i x.
  by apply: eqEtoK; rewrite -toEtrans.
have EtoK_0 i: EtoK i 0 = FtoK 0 by apply: eqEtoK; rewrite !rmorph0.
have EtoK_1 i: EtoK i 1 = FtoK 1 by apply: eqEtoK; rewrite !rmorph1.
have EtoKeq0 i x: (EtoK i x == FtoK 0) = (x == 0).
  by rewrite /FtoK -!piEtoK eqmodE /= /eqKrep /= rmorph0 fmorph_eq0.
have toErepr m i leim x lerm:
  toE _ m lerm (tagged (repr (EtoK i x))) = toE i m leim x.
- have: (Tagged E x == repr (EtoK i x) %[mod K])%qT by rewrite reprK piEtoK.
  rewrite eqmodE /= /eqKrep; case: (repr _) => j y /= in lerm * => /eqP /=.
  have leijm: maxn i j <= m by rewrite geq_max leim.
  by move/(congr1 (toE _ _ leijm)); rewrite -!toEtrans.
pose Kadd (x y : K) := EtoK _ (prod_curry +%R (pairK (repr x) (repr y))).
pose Kopp (x : K) := EtoK _ (- tagged (repr x)).
pose Kmul (x y : K) := EtoK _ (prod_curry *%R (pairK (repr x) (repr y))).
pose Kinv (x : K) := EtoK _ (tagged (repr x))^-1.
have EtoK_D i: {morph EtoK i : x y / x + y >-> Kadd x y}.
  move=> x y; apply: eqEtoK; set j := maxn (tag _) _; rewrite !rmorphD.
  by rewrite -!toEtrans ?le_max  // => lexm leym; rewrite !toErepr.
have EtoK_N i: {morph EtoK i : x / - x >-> Kopp x}.
  by move=> x; apply: eqEtoK; set j := tag _; rewrite !rmorphN toErepr.
have EtoK_M i: {morph EtoK i : x y / x * y >-> Kmul x y}.
  move=> x y; apply: eqEtoK; set j := maxn (tag _) _; rewrite !rmorphM.
  by rewrite -!toEtrans ?le_max  // => lexm leym; rewrite !toErepr.
have EtoK_V i: {morph EtoK i : x / x^-1 >-> Kinv x}.
  by move=> x; apply: eqEtoK; set j := tag _; rewrite !fmorphV toErepr.
case: {toErepr}I in (Kadd) (Kopp) (Kmul) (Kinv) EtoK_D EtoK_N EtoK_M EtoK_V.
pose inEi i z := {x : E i | z = EtoK i x}; have KtoE z: {i : nat & inEi i z}.
  by elim/quotW: z => [[i x] /=]; exists i, x; rewrite piEtoK.
have inEle i j z: i <= j -> inEi i z -> inEi j z.
  by move=> leij [x ->]; exists (toE i j leij x); rewrite toEtoK.
have KtoE2 z1 z2: {i : nat & inEi i z1 & inEi i z2}.
  have [[i1 Ez1] [i2 Ez2]] := (KtoE z1, KtoE z2).
  by exists (maxn i1 i2); [apply: inEle Ez1 | apply: inEle Ez2].
have KtoE3 z1 z2 z3: {i : nat & inEi i z1 & inEi i z2 * inEi i z3}%type.
  have [[i1 Ez1] [i2 Ez2 Ez3]] := (KtoE z1, KtoE2 z2 z3).
  by exists (maxn i1 i2); [apply: inEle Ez1 | split; apply: inEle (leMr _ _) _].
have KaddC: commutative Kadd.
  by move=> u v; have [i [x ->] [y ->]] := KtoE2 u v; rewrite -!EtoK_D addrC.
have KaddA: associative Kadd.
  move=> u v w; have [i [x ->] [[y ->] [z ->]]] := KtoE3 u v w.
  by rewrite -!EtoK_D addrA.
have Kadd0: left_id (FtoK 0) Kadd.
  by move=> u; have [i [x ->]] := KtoE u; rewrite -(EtoK_0 i) -EtoK_D add0r.
have KaddN: left_inverse (FtoK 0) Kopp Kadd.
  by move=> u; have [i [x ->]] := KtoE u; rewrite -EtoK_N -EtoK_D addNr EtoK_0.
pose Kzmod := ZmodType K (ZmodMixin KaddA KaddC Kadd0 KaddN).
have KmulC: commutative Kmul.
  by move=> u v; have [i [x ->] [y ->]] := KtoE2 u v; rewrite -!EtoK_M mulrC.
have KmulA: @associative Kzmod Kmul.
  move=> u v w; have [i [x ->] [[y ->] [z ->]]] := KtoE3 u v w.
  by rewrite -!EtoK_M mulrA.
have Kmul1: left_id (FtoK 1) Kmul.
  by move=> u; have [i [x ->]] := KtoE u; rewrite -(EtoK_1 i) -EtoK_M mul1r.
have KmulD: left_distributive Kmul Kadd.
  move=> u v w; have [i [x ->] [[y ->] [z ->]]] := KtoE3 u v w.
  by rewrite -!(EtoK_M, EtoK_D) mulrDl.
have Kone_nz: FtoK 1 != FtoK 0 by rewrite EtoKeq0 oner_neq0.
pose KringMixin := ComRingMixin KmulA KmulC Kmul1 KmulD Kone_nz.
pose Kring := ComRingType (RingType Kzmod KringMixin) KmulC.
have KmulV: @GRing.Field.axiom Kring Kinv.
  move=> u; have [i [x ->]] := KtoE u; rewrite EtoKeq0 => nz_x.
  by rewrite -EtoK_V -[_ * _]EtoK_M mulVf ?EtoK_1.
have Kinv0: Kinv (FtoK 0) = FtoK 0 by rewrite -EtoK_V invr0.
pose Kuring := [comUnitRingType of UnitRingType _ (FieldUnitMixin KmulV Kinv0)].
pose KfieldMixin := @FieldMixin _ _ KmulV Kinv0.
pose Kidomain := IdomainType Kuring (FieldIdomainMixin KfieldMixin).
pose Kfield := FieldType Kidomain KfieldMixin.
have EtoKrmorphism i: rmorphism (EtoK i : E i -> Kfield).
  by do 2?split=> [x y|]; rewrite ?EtoK_D ?EtoK_N ?EtoK_M ?EtoK_1.
pose EtoKM := RMorphism (EtoKrmorphism _); have EtoK_E: EtoK _ = EtoKM _ by [].
have toEtoKp := @eq_map_poly _ Kring _ _(toEtoK _ _ _).
have Kclosed: GRing.ClosedField.axiom Kfield.
  move=> n pK n_gt0; pose m0 := \max_(i < n) tag (KtoE (pK i)); pose m := m0.+1.
  have /fin_all_exists[pE DpE] (i : 'I_n): exists y, EtoK m y = pK i.
    pose u := KtoE (pK i); have leum0: tag u <= m0 by rewrite (bigmax_sup i).
    by have [y ->] := tagged u; exists (toE _ _ (leqW leum0) y); rewrite toEtoK.
  pose p := 'X^n - rVpoly (\row_i pE i); pose j := code [:: m0; pickle p].
  pose pj := tagged (E_ j) j; pose w : E j.+1 := ext1w (E j) pj.
  have lemj: m <= j by rewrite (allP (ltn_code _)) ?mem_head.
  exists (EtoKM j.+1 w); apply/eqP; rewrite -subr_eq0; apply/eqP.
  transitivity (EtoKM j.+1 (map_poly (toE m j.+1 (leqW lemj)) p).[w]).
    rewrite -horner_map -map_poly_comp toEtoKp EtoK_E; move/EtoKM: w => w.
    rewrite rmorphB [_ 'X^n]map_polyXn !hornerE hornerXn; congr (_ - _ : Kring).
    rewrite (@horner_coef_wide _ n) ?size_map_poly ?size_poly //.
    by apply: eq_bigr => i _; rewrite coef_map coef_rVpoly valK mxE /= DpE.
  suffices Dpj: map_poly (toE m j lemj) p = pj.
    apply/eqP; rewrite EtoKeq0 (eq_map_poly (toEleS _ _ _ _)) map_poly_comp Dpj.
    rewrite -rootE -[pj]minXpE ?ext1root // -Dpj size_map_poly.
    by rewrite size_addl ?size_polyXn ltnS ?size_opp ?size_poly.
  rewrite {w}/pj; elim: {-9}j lemj => // k IHk lemSk.
  move: lemSk (lemSk); rewrite {1}leq_eqVlt ltnS => /predU1P[<- | lemk] lemSk.
    rewrite {k IHk lemSk}(eq_map_poly (toEeq m _)) map_poly_id //= /incEp.
    by rewrite codeK eqxx pickleK.
  rewrite (eq_map_poly (toEleS _ _ _ _)) map_poly_comp {}IHk //= /incEp codeK.
  by rewrite -if_neg neq_ltn lemk.
suffices{Kclosed} algF_K: {FtoK : {rmorphism F -> Kfield} | integralRange FtoK}.
  pose Kdec := DecFieldType Kfield (closed_fields_QEMixin Kclosed).
  pose KclosedField := ClosedFieldType Kdec Kclosed.
  by exists [countClosedFieldType of CountType KclosedField cntK].
exists (EtoKM 0%N) => /= z; have [i [{z}z ->]] := KtoE z.
suffices{z} /(_ z)[p mon_p]: integralRange (toE 0%N i isT).
  by rewrite -(fmorph_root (EtoKM i)) -map_poly_comp toEtoKp; exists p.
rewrite /toE /E; clear - minXp_gt1 ext1root ext1gen.
move: (i - 0)%N (subnK _) => n; case: i /.
elim: n => [|n IHn] /= z; first exact: integral_id.
have{z} [q ->] := ext1gen _ _ z; set pn := tagged (E_ _) _.
apply: integral_horner.
  by apply/integral_poly=> i; rewrite coef_map; apply: integral_rmorph.
apply: integral_root (ext1root _ _) _.
  by rewrite map_poly_eq0 -size_poly_gt0 ltnW.
by apply/integral_poly=> i; rewrite coef_map; apply: integral_rmorph.
Qed.

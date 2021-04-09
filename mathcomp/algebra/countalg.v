(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype bigop ssralg.
(* From mathcomp Require Import generic_quotient ring_quotient. *)

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

(*Section Generic.

(* Implicits *)
Variables (type base_type : Type) (class_of base_of : Type -> Type).
Variable base_sort : base_type -> Type.

(* Explicits *)
Variable Pack : forall T, class_of T -> type.
Variable Class : forall T, base_of T -> mixin_of T -> class_of T.
Variable base_class : forall bT, base_of (base_sort bT).

Definition gen_pack T :=
  fun bT b & phant_id (base_class bT) b =>
  fun fT c m & phant_id (Countable.class fT) (Countable.Class c m) =>
  Pack (@Class T b m).

End Generic.

Arguments gen_pack [type base_type class_of base_of base_sort].*)
Local Notation cnt_ c := (@Countable.Class _ c c).
Local Notation do_pack pack T := (pack T _ _ id _ _ _ id).
Import GRing.Theory.

#[mathcomp]
HB.structure Definition Zmodule := {M of GRing.Zmodule M & Countable M}.
Module ZmoduleExports.
Notation countZmodType := Zmodule.type.
Notation "[ 'countZmodType' 'of' T ]" := (Zmodule.clone T _)
  (* NB: was (do_pack pack T)*)
  (at level 0, format "[ 'countZmodType'  'of'  T ]") : form_scope.
End ZmoduleExports.
HB.export ZmoduleExports.

#[mathcomp]
HB.structure Definition Ring := {R of GRing.Ring R & Countable R}.

Module RingExports.
Notation countRingType := Ring.type.
Notation "[ 'countRingType' 'of' T ]" :=
  (Ring.clone T _) (* NB: was (do_pack pack T) *)
      (at level 0, format "[ 'countRingType'  'of'  T ]") : form_scope.
End RingExports.
HB.export RingExports.

#[mathcomp]
HB.structure Definition ComRing := {R of GRing.ComRing R & Countable R}.

Module ComRingExports.
Notation countComRingType := ComRing.type.
Notation "[ 'countComRingType' 'of' T ]" := (ComRing.clone T _)
  (at level 0, format "[ 'countComRingType'  'of'  T ]") : form_scope.
End ComRingExports.
HB.export ComRingExports.

#[mathcomp]
HB.structure Definition UnitRing := {R of GRing.UnitRing R & Countable R}.

Module UnitRingExports.
Notation countUnitRingType := UnitRing.type.
Notation "[ 'countUnitRingType' 'of' T ]" := (UnitRing.clone T _) 
  (*NB: was (do_pack pack T)*)
  (at level 0, format "[ 'countUnitRingType'  'of'  T ]") : form_scope.
End UnitRingExports.
HB.export UnitRingExports.

#[mathcomp]
HB.structure Definition ComUnitRing := {R of GRing.ComUnitRing R & Countable R}.

Module ComUnitRingExports.
Notation countComUnitRingType := ComUnitRing.type.
Notation "[ 'countComUnitRingType' 'of' T ]" := (ComUnitRing.clone T _)
  (*NB: was (do_pack pack T)*)
  (at level 0, format "[ 'countComUnitRingType'  'of'  T ]") : form_scope.
End ComUnitRingExports.
HB.export ComUnitRingExports.

#[mathcomp]
HB.structure Definition IntegralDomain :=
  {R of GRing.IntegralDomain R & Countable R}.

Module IntegralDomainExports.
Notation countIdomainType := IntegralDomain.type.
Notation "[ 'countIdomainType' 'of' T ]" := (IntegralDomain.clone T _) 
  (*NB: was (do_pack pack T)*)
  (at level 0, format "[ 'countIdomainType'  'of'  T ]") : form_scope.
End IntegralDomainExports.
HB.export IntegralDomainExports.

#[mathcomp]
HB.structure Definition Field := {R of GRing.Field R & Countable R}.

Module FieldExports.
Notation countFieldType := Field.type.
Notation "[ 'countFieldType' 'of' T ]" := (Field.clone T _) (*(do_pack pack T)*)
  (at level 0, format "[ 'countFieldType'  'of'  T ]") : form_scope.
End FieldExports.
HB.export FieldExports.

#[mathcomp]
HB.structure Definition DecidableField := 
  {R of GRing.DecidableField R & Countable R}.

Module DecidableFieldExports.
Notation countDecFieldType := DecidableField.type.
Notation "[ 'countDecFieldType' 'of' T ]" := (DecidableField.clone T _) 
  (*NB: was (do_pack pack T)*)
  (at level 0, format "[ 'countDecFieldType'  'of'  T ]") : form_scope.
End DecidableFieldExports.
HB.export DecidableFieldExports.

#[mathcomp]
HB.structure Definition ClosedField := {R of GRing.ClosedField R & Countable R}.

Module ClosedFieldExports.
Notation countClosedFieldType := ClosedField.type.
Notation "[ 'countClosedFieldType' 'of' T ]" := (ClosedField.clone T _) 
  (*NB: was (do_pack pack T)*)
  (at level 0, format "[ 'countClosedFieldType'  'of'  T ]") : form_scope.
End ClosedFieldExports.
HB.export ClosedFieldExports.

#[export]
HB.instance Definition _ (R : countZmodType) := Zmodule.on R^o.
#[export]
HB.instance Definition _ (R : countRingType) := Ring.on R^o.

End CountRing.

Import CountRing.
HB.reexport.

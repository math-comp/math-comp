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

Import GRing.Theory.

#[short(type="countZmodType")]
HB.structure Definition Zmodule := {M of GRing.Zmodule M & Countable M}.
Module ZmoduleExports.
Notation "[ 'countZmodType' 'of' T ]" := (Zmodule.clone T _)
  (at level 0, format "[ 'countZmodType'  'of'  T ]") : form_scope.
End ZmoduleExports.
HB.export ZmoduleExports.

#[short(type="countRingType")]
HB.structure Definition Ring := {R of GRing.Ring R & Countable R}.

Module RingExports.
Notation "[ 'countRingType' 'of' T ]" :=
  (Ring.clone T _) (* NB: was (do_pack pack T) *)
      (at level 0, format "[ 'countRingType'  'of'  T ]") : form_scope.
End RingExports.
HB.export RingExports.

#[short(type="countComRingType")]
HB.structure Definition ComRing := {R of GRing.ComRing R & Countable R}.

Module ComRingExports.
Notation "[ 'countComRingType' 'of' T ]" := (ComRing.clone T _)
  (at level 0, format "[ 'countComRingType'  'of'  T ]") : form_scope.
End ComRingExports.
HB.export ComRingExports.

#[short(type="countUnitRingType")]
HB.structure Definition UnitRing := {R of GRing.UnitRing R & Countable R}.

Module UnitRingExports.
Notation countUnitRingType := UnitRing.type.
Notation "[ 'countUnitRingType' 'of' T ]" := (UnitRing.clone T _) 
  (at level 0, format "[ 'countUnitRingType'  'of'  T ]") : form_scope.
End UnitRingExports.
HB.export UnitRingExports.

#[short(type="countComUnitRingType")]
HB.structure Definition ComUnitRing := {R of GRing.ComUnitRing R & Countable R}.

Module ComUnitRingExports.
Notation "[ 'countComUnitRingType' 'of' T ]" := (ComUnitRing.clone T _)
  (at level 0, format "[ 'countComUnitRingType'  'of'  T ]") : form_scope.
End ComUnitRingExports.
HB.export ComUnitRingExports.

#[short(type="countIdomainType")]
HB.structure Definition IntegralDomain :=
  {R of GRing.IntegralDomain R & Countable R}.

Module IntegralDomainExports.
Notation "[ 'countIdomainType' 'of' T ]" := (IntegralDomain.clone T _) 
  (at level 0, format "[ 'countIdomainType'  'of'  T ]") : form_scope.
End IntegralDomainExports.
HB.export IntegralDomainExports.

#[short(type="countFieldType")]
HB.structure Definition Field := {R of GRing.Field R & Countable R}.

Module FieldExports.
Notation "[ 'countFieldType' 'of' T ]" := (Field.clone T _) (*(do_pack pack T)*)
  (at level 0, format "[ 'countFieldType'  'of'  T ]") : form_scope.
End FieldExports.
HB.export FieldExports.

#[short(type="countDecFieldType")]
HB.structure Definition DecidableField := 
  {R of GRing.DecidableField R & Countable R}.

Module DecidableFieldExports.
Notation "[ 'countDecFieldType' 'of' T ]" := (DecidableField.clone T _) 
  (at level 0, format "[ 'countDecFieldType'  'of'  T ]") : form_scope.
End DecidableFieldExports.
HB.export DecidableFieldExports.

#[short(type="countClosedFieldType")]
HB.structure Definition ClosedField := {R of GRing.ClosedField R & Countable R}.

Module ClosedFieldExports.
Notation "[ 'countClosedFieldType' 'of' T ]" := (ClosedField.clone T _) 
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

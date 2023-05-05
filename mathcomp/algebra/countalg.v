(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype bigop ssralg.

(*****************************************************************************)
(*     The algebraic part of the algebraic hierarchy for countable types     *)
(*                                                                           *)
(* This file clones part of ssralg hierarchy for countable types; it does    *)
(* not cover the left module / algebra interfaces, providing only            *)
(*          countNmodType == countable nmodType interface                    *)
(*          countZmodType == countable zmodType interface                    *)
(*      countSemiRingType == countable semiRingType interface                *)
(*          countRingType == countable ringType interface                    *)
(*   countComSemiRingType == countable comSemiRingType interface             *)
(*       countComRingType == countable comRingType interface                 *)
(*      countUnitRingType == countable unitRingType interface                *)
(*   countComUnitRingType == countable comUnitRingType interface             *)
(*       countIdomainType == countable idomainType interface                 *)
(*         countFieldType == countable fieldType interface                   *)
(*      countDecFieldType == countable decFieldType interface                *)
(*   countClosedFieldType == countable closedFieldType interface             *)
(*                                                                           *)
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

#[short(type="countNmodType")]
HB.structure Definition Nmodule := {M of GRing.Nmodule M & Countable M}.
Module NmoduleExports.
#[deprecated(since="mathcomp 2.0.0",
  note="Use CountRing.Nmodule.clone instead.")]
Notation "[ 'countNmodType' 'of' T ]" := (Nmodule.clone T _)
  (at level 0, format "[ 'countNmodType'  'of'  T ]") : form_scope.
End NmoduleExports.
HB.export NmoduleExports.

#[short(type="countZmodType")]
HB.structure Definition Zmodule := {M of GRing.Zmodule M & Countable M}.
Module ZmoduleExports.
#[deprecated(since="mathcomp 2.0.0",
  note="Use CountRing.Zmodule.clone instead.")]
Notation "[ 'countZmodType' 'of' T ]" := (Zmodule.clone T%type _)
  (at level 0, format "[ 'countZmodType'  'of'  T ]") : form_scope.
End ZmoduleExports.
HB.export ZmoduleExports.

#[short(type="countSemiRingType")]
HB.structure Definition SemiRing := {R of GRing.SemiRing R & Countable R}.

Module SemiRingExports.
#[deprecated(since="mathcomp 2.0.0",
  note="Use CountRing.SemiRing.clone instead.")]
Notation "[ 'countSemiRingType' 'of' T ]" :=
  (SemiRing.clone T _) (* NB: was (do_pack pack T) *)
      (at level 0, format "[ 'countSemiRingType'  'of'  T ]") : form_scope.
End SemiRingExports.
HB.export SemiRingExports.

#[short(type="countRingType")]
HB.structure Definition Ring := {R of GRing.Ring R & Countable R}.

Module RingExports.
#[deprecated(since="mathcomp 2.0.0", note="Use CountRing.Ring.clone instead.")]
Notation "[ 'countRingType' 'of' T ]" :=
  (Ring.clone T%type _) (* NB: was (do_pack pack T) *)
      (at level 0, format "[ 'countRingType'  'of'  T ]") : form_scope.
End RingExports.
HB.export RingExports.

#[short(type="countComSemiRingType")]
HB.structure Definition ComSemiRing := {R of GRing.ComSemiRing R & Countable R}.

Module ComSemiRingExports.
#[deprecated(since="mathcomp 2.0.0",
  note="Use CountRing.ComSemiRing.clone instead.")]
Notation "[ 'countComSemiRingType' 'of' T ]" := (ComSemiRing.clone T _)
  (at level 0, format "[ 'countComSemiRingType'  'of'  T ]") : form_scope.
End ComSemiRingExports.
HB.export ComSemiRingExports.

#[short(type="countComRingType")]
HB.structure Definition ComRing := {R of GRing.ComRing R & Countable R}.

Module ComRingExports.
#[deprecated(since="mathcomp 2.0.0",
  note="Use CountRing.ComRing.clone instead.")]
Notation "[ 'countComRingType' 'of' T ]" := (ComRing.clone T%type _)
  (at level 0, format "[ 'countComRingType'  'of'  T ]") : form_scope.
End ComRingExports.
HB.export ComRingExports.

#[short(type="countUnitRingType")]
HB.structure Definition UnitRing := {R of GRing.UnitRing R & Countable R}.

Module UnitRingExports.
#[deprecated(since="mathcomp 2.0.0",
  note="Use CountRing.UnitRing.clone instead.")]
Notation "[ 'countUnitRingType' 'of' T ]" := (UnitRing.clone T%type _)
  (at level 0, format "[ 'countUnitRingType'  'of'  T ]") : form_scope.
End UnitRingExports.
HB.export UnitRingExports.

#[short(type="countComUnitRingType")]
HB.structure Definition ComUnitRing := {R of GRing.ComUnitRing R & Countable R}.

Module ComUnitRingExports.
#[deprecated(since="mathcomp 2.0.0",
  note="Use CountRing.ComUnitRing.clone instead.")]
Notation "[ 'countComUnitRingType' 'of' T ]" := (ComUnitRing.clone T%type _)
  (at level 0, format "[ 'countComUnitRingType'  'of'  T ]") : form_scope.
End ComUnitRingExports.
HB.export ComUnitRingExports.

#[short(type="countIdomainType")]
HB.structure Definition IntegralDomain :=
  {R of GRing.IntegralDomain R & Countable R}.

Module IntegralDomainExports.
#[deprecated(since="mathcomp 2.0.0",
  note="Use CountRing.IntegralDomain.clone instead.")]
Notation "[ 'countIdomainType' 'of' T ]" := (IntegralDomain.clone T%type _)
  (at level 0, format "[ 'countIdomainType'  'of'  T ]") : form_scope.
End IntegralDomainExports.
HB.export IntegralDomainExports.

#[short(type="countFieldType")]
HB.structure Definition Field := {R of GRing.Field R & Countable R}.

Module FieldExports.
#[deprecated(since="mathcomp 2.0.0", note="Use CountRing.Field.clone instead.")]
Notation "[ 'countFieldType' 'of' T ]" := (Field.clone T%type _)
  (at level 0, format "[ 'countFieldType'  'of'  T ]") : form_scope.
End FieldExports.
HB.export FieldExports.

#[short(type="countDecFieldType")]
HB.structure Definition DecidableField :=
  {R of GRing.DecidableField R & Countable R}.

Module DecidableFieldExports.
#[deprecated(since="mathcomp 2.0.0",
  note="Use CountRing.DecidableField.clone instead.")]
Notation "[ 'countDecFieldType' 'of' T ]" := (DecidableField.clone T%type _)
  (at level 0, format "[ 'countDecFieldType'  'of'  T ]") : form_scope.
End DecidableFieldExports.
HB.export DecidableFieldExports.

#[short(type="countClosedFieldType")]
HB.structure Definition ClosedField := {R of GRing.ClosedField R & Countable R}.

Module ClosedFieldExports.
#[deprecated(since="mathcomp 2.0.0",
  note="Use CountRing.ClosedField.clone instead.")]
Notation "[ 'countClosedFieldType' 'of' T ]" := (ClosedField.clone T%type _)
  (at level 0, format "[ 'countClosedFieldType'  'of'  T ]") : form_scope.
End ClosedFieldExports.
HB.export ClosedFieldExports.

#[export]
HB.instance Definition _ (R : countNmodType) := Nmodule.on R^o.
#[export]
HB.instance Definition _ (R : countZmodType) := Zmodule.on R^o.
#[export]
HB.instance Definition _ (R : countSemiRingType) := SemiRing.on R^o.
#[export]
HB.instance Definition _ (R : countRingType) := Ring.on R^o.

End CountRing.

Import CountRing.
HB.reexport.

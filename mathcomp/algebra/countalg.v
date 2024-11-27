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
(*    countNzSemiRingType == countable nzSemiRingType interface              *)
(*        countNzRingType == countable nzRingType interface                  *)
(* countComNzSemiRingType == countable comNzSemiRingType interface           *)
(*     countComNzRingType == countable comNzRingType interface               *)
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

#[short(type="countZmodType")]
HB.structure Definition Zmodule := {M of GRing.Zmodule M & Countable M}.

#[short(type="countNzSemiRingType")]
HB.structure Definition NzSemiRing := {R of GRing.NzSemiRing R & Countable R}.

#[short(type="countNzRingType")]
HB.structure Definition NzRing := {R of GRing.NzRing R & Countable R}.

#[short(type="countComNzSemiRingType")]
HB.structure Definition ComNzSemiRing := {R of GRing.ComNzSemiRing R & Countable R}.

#[short(type="countComNzRingType")]
HB.structure Definition ComNzRing := {R of GRing.ComNzRing R & Countable R}.

#[short(type="countUnitRingType")]
HB.structure Definition UnitRing := {R of GRing.UnitRing R & Countable R}.

#[short(type="countComUnitRingType")]
HB.structure Definition ComUnitRing := {R of GRing.ComUnitRing R & Countable R}.

#[short(type="countIdomainType")]
HB.structure Definition IntegralDomain :=
  {R of GRing.IntegralDomain R & Countable R}.

#[short(type="countFieldType")]
HB.structure Definition Field := {R of GRing.Field R & Countable R}.

#[short(type="countDecFieldType")]
HB.structure Definition DecidableField :=
  {R of GRing.DecidableField R & Countable R}.

#[short(type="countClosedFieldType")]
HB.structure Definition ClosedField := {R of GRing.ClosedField R & Countable R}.

#[export]
HB.instance Definition _ (R : countNmodType) := Nmodule.on R^o.
#[export]
HB.instance Definition _ (R : countZmodType) := Zmodule.on R^o.
#[export]
HB.instance Definition _ (R : countNzSemiRingType) := NzSemiRing.on R^o.
#[export]
HB.instance Definition _ (R : countNzRingType) := NzRing.on R^o.

End CountRing.

Import CountRing.
HB.reexport.

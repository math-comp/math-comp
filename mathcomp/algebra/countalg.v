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

#[short(type="countZmodType")]
HB.structure Definition Zmodule := {M of GRing.Zmodule M & Countable M}.

#[short(type="countSemiRingType")]
HB.structure Definition SemiRing := {R of GRing.SemiRing R & Countable R}.

#[short(type="countRingType")]
HB.structure Definition Ring := {R of GRing.Ring R & Countable R}.

#[short(type="countComSemiRingType")]
HB.structure Definition ComSemiRing := {R of GRing.ComSemiRing R & Countable R}.

#[short(type="countComRingType")]
HB.structure Definition ComRing := {R of GRing.ComRing R & Countable R}.

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
HB.instance Definition _ (R : countSemiRingType) := SemiRing.on R^o.
#[export]
HB.instance Definition _ (R : countRingType) := Ring.on R^o.

End CountRing.

Import CountRing.
HB.reexport.

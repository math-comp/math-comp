(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import bigop ssralg.

(*****************************************************************************)
(*     The algebraic part of the algebraic hierarchy for countable types     *)
(*                                                                           *)
(* This file clones part of ssralg hierarchy for countable types; it does    *)
(* not cover the left module / algebra interfaces, providing only            *)
(*          countNmodType == countable nmodType interface                    *)
(*          countZmodType == countable zmodType interface                    *)
(*    countPzSemiRingType == countable pzSemiRingType interface              *)
(*    countNzSemiRingType == countable nzSemiRingType interface              *)
(*        countPzRingType == countable pzRingType interface                  *)
(*        countNzRingType == countable nzRingType interface                  *)
(* countComPzSemiRingType == countable comPzSemiRingType interface           *)
(* countComNzSemiRingType == countable comNzSemiRingType interface           *)
(*     countComPzRingType == countable comPzRingType interface               *)
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

#[short(type="countPzSemiRingType")]
HB.structure Definition PzSemiRing := {R of GRing.PzSemiRing R & Countable R}.

#[short(type="countNzSemiRingType")]
HB.structure Definition NzSemiRing := {R of GRing.NzSemiRing R & Countable R}.

#[deprecated(since="mathcomp 2.4.0", use=CountRing.NzSemiRing)]
Notation SemiRing R := (NzSemiRing R) (only parsing).

Module SemiRing.
#[deprecated(since="mathcomp 2.4.0", use=CountRing.NzSemiRing.sort)]
Notation sort := (NzSemiRing.sort) (only parsing).
#[deprecated(since="mathcomp 2.4.0", use=CountRing.NzSemiRing.on)]
Notation on R := (NzSemiRing.on R) (only parsing).
#[deprecated(since="mathcomp 2.4.0", use=CountRing.NzSemiRing.copy)]
Notation copy T U := (NzSemiRing.copy T U) (only parsing).
End SemiRing.

#[short(type="countPzRingType")]
HB.structure Definition PzRing := {R of GRing.PzRing R & Countable R}.

#[short(type="countNzRingType")]
HB.structure Definition NzRing := {R of GRing.NzRing R & Countable R}.

#[deprecated(since="mathcomp 2.4.0", use=CountRing.NzRing)]
Notation Ring R := (NzRing R) (only parsing).

Module Ring.
#[deprecated(since="mathcomp 2.4.0", use=CountRing.NzRing.sort)]
Notation sort := (NzRing.sort) (only parsing).
#[deprecated(since="mathcomp 2.4.0", use=CountRing.NzRing.on)]
Notation on R := (NzRing.on R) (only parsing).
#[deprecated(since="mathcomp 2.4.0", use=CountRing.NzRing.copy)]
Notation copy T U := (NzRing.copy T U) (only parsing).
End Ring.

#[short(type="countComPzSemiRingType")]
HB.structure Definition ComPzSemiRing :=
  {R of GRing.ComPzSemiRing R & Countable R}.

#[short(type="countComNzSemiRingType")]
HB.structure Definition ComNzSemiRing :=
  {R of GRing.ComNzSemiRing R & Countable R}.

#[deprecated(since="mathcomp 2.4.0", use=CountRing.ComNzSemiRing)]
Notation ComSemiRing R := (ComNzSemiRing R) (only parsing).

Module ComSemiRing.
#[deprecated(since="mathcomp 2.4.0", use=CountRing.ComNzSemiRing.sort)]
Notation sort := (ComNzSemiRing.sort) (only parsing).
#[deprecated(since="mathcomp 2.4.0", use=CountRing.ComNzSemiRing.on)]
Notation on R := (ComNzSemiRing.on R) (only parsing).
#[deprecated(since="mathcomp 2.4.0", use=CountRing.ComNzSemiRing.copy)]
Notation copy T U := (ComNzSemiRing.copy T U) (only parsing).
End ComSemiRing.

#[short(type="countComPzRingType")]
HB.structure Definition ComPzRing := {R of GRing.ComPzRing R & Countable R}.

#[short(type="countComNzRingType")]
HB.structure Definition ComNzRing := {R of GRing.ComNzRing R & Countable R}.

#[deprecated(since="mathcomp 2.4.0", use=CountRing.ComNzRing)]
Notation ComRing R := (ComNzRing R) (only parsing).

Module ComRing.
#[deprecated(since="mathcomp 2.4.0", use=CountRing.ComNzRing.sort)]
Notation sort := (ComNzRing.sort) (only parsing).
#[deprecated(since="mathcomp 2.4.0", use=CountRing.ComNzRing.on)]
Notation on R := (ComNzRing.on R) (only parsing).
#[deprecated(since="mathcomp 2.4.0", use=CountRing.ComNzRing.copy)]
Notation copy T U := (ComNzRing.copy T U) (only parsing).
End ComRing.

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

Module ReguralExports.
HB.instance Definition _ (R : countType) := Countable.on R^o.
HB.instance Definition _ (R : countNmodType) := Nmodule.on R^o.
HB.instance Definition _ (R : countZmodType) := Zmodule.on R^o.
HB.instance Definition _ (R : countPzSemiRingType) := PzSemiRing.on R^o.
HB.instance Definition _ (R : countNzSemiRingType) := NzSemiRing.on R^o.
HB.instance Definition _ (R : countPzRingType) := PzRing.on R^o.
HB.instance Definition _ (R : countNzRingType) := NzRing.on R^o.
HB.instance Definition _ (R : countComPzSemiRingType) := ComPzSemiRing.on R^o.
HB.instance Definition _ (R : countComNzSemiRingType) := ComNzSemiRing.on R^o.
HB.instance Definition _ (R : countComPzRingType) := ComPzRing.on R^o.
HB.instance Definition _ (R : countComNzRingType) := ComNzRing.on R^o.
HB.instance Definition _ (R : countUnitRingType) := UnitRing.on R^o.
HB.instance Definition _ (R : countComUnitRingType) := ComUnitRing.on R^o.
HB.instance Definition _ (R : countIdomainType) := IntegralDomain.on R^o.
HB.instance Definition _ (R : countFieldType) := Field.on R^o.
HB.instance Definition _ (R : countDecFieldType) := DecidableField.on R^o.
HB.instance Definition _ (R : countClosedFieldType) := ClosedField.on R^o.
End ReguralExports.
HB.export ReguralExports.

End CountRing.

Import CountRing.
HB.reexport.

#[deprecated(since="mathcomp 2.4.0", use=countNzSemiRingType)]
Notation countSemiRingType := (countNzSemiRingType) (only parsing).
#[deprecated(since="mathcomp 2.4.0", use=countNzRingType)]
Notation countRingType := (countNzRingType) (only parsing).
#[deprecated(since="mathcomp 2.4.0", use=countComNzSemiRingType)]
Notation countComSemiRingType := (countComNzSemiRingType) (only parsing).
#[deprecated(since="mathcomp 2.4.0", use=countComNzRingType)]
Notation countComRingType := (countComNzRingType) (only parsing).

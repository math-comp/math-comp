(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import bigop nmodule rings_modules_and_algebras divalg.
From mathcomp Require Import decfield.

(*****************************************************************************)
(*     The algebraic part of the algebraic hierarchy for countable types     *)
(*                                                                           *)
(* This file clones part of ssralg hierarchy for countable types; it does    *)
(* not cover the left module / algebra interfaces, providing only            *)
(*          countNmodType == countable nmodType interface                    *)
(*          countZmodType == countable zmodType interface                    *)
(*      countSemiRingType == countable semiRingType interface                *)
(*    countNzSemiRingType == countable nzSemiRingType interface              *)
(*          countRingType == countable ringType interface                    *)
(*        countNzRingType == countable nzRingType interface                  *)
(*   countComSemiRingType == countable comSemiRingType interface             *)
(* countComNzSemiRingType == countable comNzSemiRingType interface           *)
(*       countComRingType == countable comRingType interface                 *)
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

#[short(type="countSemiRingType")]
HB.structure Definition SemiRing := {R of GRing.SemiRing R & Countable R}.

#[deprecated(since="mathcomp 2.7.0", use=CountRing.SemiRing)]
Notation PzSemiRing R := (SemiRing R) (only parsing).
Module PzSemiRing.
#[deprecated(since="mathcomp 2.7.0", use=CountRing.SemiRing.sort)]
Notation sort := (SemiRing.sort) (only parsing).
#[deprecated(since="mathcomp 2.7.0", use=CountRing.SemiRing.on)]
Notation on R := (SemiRing.on R) (only parsing).
#[deprecated(since="mathcomp 2.7.0", use=CountRing.SemiRing.copy)]
Notation copy T U := (SemiRing.copy T U) (only parsing).
End PzSemiRing.

#[short(type="countNzSemiRingType")]
HB.structure Definition NzSemiRing := {R of GRing.NzSemiRing R & Countable R}.

#[short(type="countRingType")]
HB.structure Definition Ring := {R of GRing.Ring R & Countable R}.

#[deprecated(since="mathcomp 2.7.0", use=CountRing.Ring)]
Notation PzRing R := (Ring R) (only parsing).
Module PzRing.
#[deprecated(since="mathcomp 2.7.0", use=CountRing.Ring.sort)]
Notation sort := (Ring.sort) (only parsing).
#[deprecated(since="mathcomp 2.7.0", use=CountRing.Ring.on)]
Notation on R := (Ring.on R) (only parsing).
#[deprecated(since="mathcomp 2.7.0", use=CountRing.Ring.copy)]
Notation copy T U := (Ring.copy T U) (only parsing).
End PzRing.

#[short(type="countNzRingType")]
HB.structure Definition NzRing := {R of GRing.NzRing R & Countable R}.

#[short(type="countComSemiRingType")]
HB.structure Definition ComSemiRing := {R of GRing.ComSemiRing R & Countable R}.

#[deprecated(since="mathcomp 2.7.0", use=CountRing.ComSemiRing)]
Notation ComPzSemiRing R := (ComSemiRing R) (only parsing).
Module ComPzSemiRing.
#[deprecated(since="mathcomp 2.7.0", use=CountRing.ComSemiRing.sort)]
Notation sort := (ComSemiRing.sort) (only parsing).
#[deprecated(since="mathcomp 2.7.0", use=CountRing.ComSemiRing.on)]
Notation on R := (ComSemiRing.on R) (only parsing).
#[deprecated(since="mathcomp 2.7.0", use=CountRing.ComSemiRing.copy)]
Notation copy T U := (ComSemiRing.copy T U) (only parsing).
End ComPzSemiRing.

#[short(type="countComNzSemiRingType")]
HB.structure Definition ComNzSemiRing :=
  {R of GRing.ComNzSemiRing R & Countable R}.

#[short(type="countComRingType")]
HB.structure Definition ComRing := {R of GRing.ComRing R & Countable R}.

#[deprecated(since="mathcomp 2.7.0", use=CountRing.ComRing)]
Notation ComPzRing R := (ComRing R) (only parsing).
Module ComPzRing.
#[deprecated(since="mathcomp 2.7.0", use=CountRing.ComRing.sort)]
Notation sort := (ComRing.sort) (only parsing).
#[deprecated(since="mathcomp 2.7.0", use=CountRing.ComRing.on)]
Notation on R := (ComRing.on R) (only parsing).
#[deprecated(since="mathcomp 2.7.0", use=CountRing.ComRing.copy)]
Notation copy T U := (ComRing.copy T U) (only parsing).
End ComPzRing.

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

Module ReguralExports.
HB.instance Definition _ (R : countType) := Countable.on R^o.
HB.instance Definition _ (R : countNmodType) := Nmodule.on R^o.
HB.instance Definition _ (R : countZmodType) := Zmodule.on R^o.
HB.instance Definition _ (R : countSemiRingType) := SemiRing.on R^o.
HB.instance Definition _ (R : countNzSemiRingType) := NzSemiRing.on R^o.
HB.instance Definition _ (R : countRingType) := Ring.on R^o.
HB.instance Definition _ (R : countNzRingType) := NzRing.on R^o.
HB.instance Definition _ (R : countComSemiRingType) := ComSemiRing.on R^o.
HB.instance Definition _ (R : countComNzSemiRingType) := ComNzSemiRing.on R^o.
HB.instance Definition _ (R : countComRingType) := ComRing.on R^o.
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

#[deprecated(since="mathcomp 2.7.0", use=countSemiRingType)]
Notation countPzSemiRingType := (countSemiRingType) (only parsing).
#[deprecated(since="mathcomp 2.7.0", use=countRingType)]
Notation countPzRingType := (countRingType) (only parsing).
#[deprecated(since="mathcomp 2.7.0", use=countComSemiRingType)]
Notation countComPzSemiRingType := (countComSemiRingType) (only parsing).
#[deprecated(since="mathcomp 2.7.0", use=countComRingType)]
Notation countComPzRingType := (countComRingType) (only parsing).

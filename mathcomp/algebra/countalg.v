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

(* Initial C letter of CZmodule is needed because of name clashes in short
  names.  see coq-elpi issue ### *)
#[mathcomp]
HB.structure Definition CZmodule := {M of GRing.Zmodule M & Countable M}.
Module CZmoduleExports.
Notation countZmodType := CZmodule.type.
Notation "[ 'countZmodType' 'of' T ]" := (CZmodule.clone T _)
  (* NB: was (do_pack pack T)*)
  (at level 0, format "[ 'countZmodType'  'of'  T ]") : form_scope.
End CZmoduleExports.
HB.export CZmoduleExports.

#[mathcomp]
HB.structure Definition CRing := {R of GRing.Ring R & Countable R}.

Module CRingExports.
Notation countRingType := CRing.type.
Notation "[ 'countRingType' 'of' T ]" :=
  (CRing.clone T _) (* NB: was (do_pack pack T) *)
      (at level 0, format "[ 'countRingType'  'of'  T ]") : form_scope.
End CRingExports.
HB.export CRingExports.

#[mathcomp]
HB.structure Definition CComRing := {R of GRing.ComRing R & Countable R}.

Module CComRingExports.
Notation countComRingType := CComRing.type.
Notation "[ 'countComRingType' 'of' T ]" := (CComRing.clone T _)
  (at level 0, format "[ 'countComRingType'  'of'  T ]") : form_scope.
End CComRingExports.
HB.export CComRingExports.

#[mathcomp]
HB.structure Definition CUnitRing := {R of GRing.UnitRing R & Countable R}.

Module CUnitRingExports.
Notation countUnitRingType := CUnitRing.type.
Notation "[ 'countUnitRingType' 'of' T ]" := (CUnitRing.clone T _) (*NB: was (do_pack pack T)*)
  (at level 0, format "[ 'countUnitRingType'  'of'  T ]") : form_scope.
End CUnitRingExports.
HB.export CUnitRingExports.

#[mathcomp]
HB.structure Definition CComUnitRing := {R of GRing.ComUnitRing R & Countable R}.

Module CComUnitRingExports.
Notation countComUnitRingType := CComUnitRing.type.
Notation "[ 'countComUnitRingType' 'of' T ]" := (CComUnitRing.clone T _) (*NB: was (do_pack pack T)*)
  (at level 0, format "[ 'countComUnitRingType'  'of'  T ]") : form_scope.
End CComUnitRingExports.
HB.export CComUnitRingExports.

#[mathcomp]
HB.structure Definition CIntegralDomain := {R of GRing.IntegralDomain R & Countable R}.

Module CIntegralDomainExports.
Notation countIdomainType := CIntegralDomain.type.
Notation "[ 'countIdomainType' 'of' T ]" := (CIntegralDomain.clone T _) (*NB: was (do_pack pack T)*)
  (at level 0, format "[ 'countIdomainType'  'of'  T ]") : form_scope.
End CIntegralDomainExports.
HB.export CIntegralDomainExports.

#[mathcomp]
HB.structure Definition CField := {R of GRing.Field R & Countable R}.

Module CFieldExports.
Notation countFieldType := CField.type.
Notation "[ 'countFieldType' 'of' T ]" := (CField.clone T _) (*(do_pack pack T)*)
  (at level 0, format "[ 'countFieldType'  'of'  T ]") : form_scope.
End CFieldExports.
HB.export CFieldExports.

#[mathcomp]
HB.structure Definition CDecidableField := {R of GRing.DecidableField R & Countable R}.

Module CDecidableFieldExports.
Notation countDecFieldType := CDecidableField.type.
Notation "[ 'countDecFieldType' 'of' T ]" := (CDecidableField.clone T _) (*NB: was (do_pack pack T)*)
  (at level 0, format "[ 'countDecFieldType'  'of'  T ]") : form_scope.
End CDecidableFieldExports.
HB.export CDecidableFieldExports.

#[mathcomp]
HB.structure Definition CClosedField := {R of GRing.ClosedField R & Countable R}.

Module CClosedFieldExports.
Notation countClosedFieldType := CClosedField.type.
Notation "[ 'countClosedFieldType' 'of' T ]" := (CClosedField.clone T _) (*NB: was (do_pack pack T)*)
  (at level 0, format "[ 'countClosedFieldType'  'of'  T ]") : form_scope.
End CClosedFieldExports.
HB.export CClosedFieldExports.

End CountRing.

HB.reexport.
(*
Import CountRing.
Export Zmodule.Exports Ring.Exports ComRing.Exports UnitRing.Exports.
Export ComUnitRing.Exports IntegralDomain.Exports.
Export Field.Exports DecidableField.Exports ClosedField.Exports.
*)

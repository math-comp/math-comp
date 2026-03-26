(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
From mathcomp Require Import choice fintype finfun bigop prime binomial.
From mathcomp Require Export nmodule algebra divalg decfield.

(******************************************************************************)
(*                            Ring-like structures                            *)
(*                                                                            *)
(* This file re-exports the contents of algebra.v, divalg.v, and decfield.v:  *)
(* (semi)rings, (semi)modules, (semi)algebras with or without commutativity,  *)
(* multiplicative inverse, etc., decidable fields, algebraically closed       *)
(* fields, and their morphisms.                                               *)
(*                                                                            *)
(* Reference: Francois Garillot, Georges Gonthier, Assia Mahboubi, Laurence   *)
(* Rideau, Packaging mathematical structures, TPHOLs 2009                     *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Module Import GRing.

Export GRing.

(* Structures *)

#[deprecated(since="mathcomp 2.4.0", use=NzSemiRing)]
Notation SemiRing R := (NzSemiRing R) (only parsing).

Module SemiRing.
#[deprecated(since="mathcomp 2.4.0", use=NzSemiRing.sort)]
Notation sort := (NzSemiRing.sort) (only parsing).
#[deprecated(since="mathcomp 2.4.0", use=NzSemiRing.on)]
Notation on R := (NzSemiRing.on R) (only parsing).
#[deprecated(since="mathcomp 2.4.0", use=NzSemiRing.copy)]
Notation copy T U := (NzSemiRing.copy T U) (only parsing).
End SemiRing.

#[deprecated(since="mathcomp 2.4.0", use=NzRing)]
Notation Ring R := (NzRing R) (only parsing).

Module Ring.
#[deprecated(since="mathcomp 2.4.0", use=NzRing.sort)]
Notation sort := (NzRing.sort) (only parsing).
#[deprecated(since="mathcomp 2.4.0", use=NzRing.on)]
Notation on R := (NzRing.on R) (only parsing).
#[deprecated(since="mathcomp 2.4.0", use=NzRing.copy)]
Notation copy T U := (NzRing.copy T U) (only parsing).
End Ring.

#[deprecated(since="mathcomp 2.6.0", use=NzLSemiAlgebra)]
Notation LSemiAlgebra R := (NzLSemiAlgebra R) (only parsing).

Module LSemiAlgebra.
#[deprecated(since="mathcomp 2.6.0", use=NzLSemiAlgebra.sort)]
Notation sort := (NzLSemiAlgebra.sort) (only parsing).
#[deprecated(since="mathcomp 2.6.0", use=NzLSemiAlgebra.on)]
Notation on R := (NzLSemiAlgebra.on R) (only parsing).
#[deprecated(since="mathcomp 2.6.0", use=NzLSemiAlgebra.copy)]
Notation copy T U := (NzLSemiAlgebra.copy T U) (only parsing).
End LSemiAlgebra.

#[deprecated(since="mathcomp 2.6.0", use=NzLalgebra)]
Notation Lalgebra R := (NzLalgebra R) (only parsing).

Module Lalgebra.
#[deprecated(since="mathcomp 2.6.0", use=NzLalgebra.sort)]
Notation sort := (NzLalgebra.sort) (only parsing).
#[deprecated(since="mathcomp 2.6.0", use=NzLalgebra.on)]
Notation on R := (NzLalgebra.on R) (only parsing).
#[deprecated(since="mathcomp 2.6.0", use=NzLalgebra.copy)]
Notation copy T U := (NzLalgebra.copy T U) (only parsing).
End Lalgebra.

#[deprecated(since="mathcomp 2.4.0", use=ComNzSemiRing)]
Notation ComSemiRing R := (ComNzSemiRing R) (only parsing).

Module ComSemiRing.
#[deprecated(since="mathcomp 2.4.0", use=ComNzSemiRing.sort)]
Notation sort := (ComNzSemiRing.sort) (only parsing).
#[deprecated(since="mathcomp 2.4.0", use=ComNzSemiRing.on)]
Notation on R := (ComNzSemiRing.on R) (only parsing).
#[deprecated(since="mathcomp 2.4.0", use=ComNzSemiRing.copy)]
Notation copy T U := (ComNzSemiRing.copy T U) (only parsing).
End ComSemiRing.

#[deprecated(since="mathcomp 2.4.0", use=ComNzRing)]
Notation ComRing R := (ComNzRing R) (only parsing).

Module ComRing.
#[deprecated(since="mathcomp 2.4.0", use=ComNzRing.sort)]
Notation sort := (ComNzRing.sort) (only parsing).
#[deprecated(since="mathcomp 2.4.0", use=ComNzRing.on)]
Notation on R := (ComNzRing.on R) (only parsing).
#[deprecated(since="mathcomp 2.4.0", use=ComNzRing.copy)]
Notation copy T U := (ComNzRing.copy T U) (only parsing).
End ComRing.

#[deprecated(since="mathcomp 2.6.0", use=NzSemiAlgebra)]
Notation SemiAlgebra R := (NzSemiAlgebra R) (only parsing).

Module SemiAlgebra.
#[deprecated(since="mathcomp 2.6.0", use=NzSemiAlgebra.sort)]
Notation sort := (NzSemiAlgebra.sort) (only parsing).
#[deprecated(since="mathcomp 2.6.0", use=NzSemiAlgebra.on)]
Notation on R := (NzSemiAlgebra.on R) (only parsing).
#[deprecated(since="mathcomp 2.6.0", use=NzSemiAlgebra.copy)]
Notation copy T U := (NzSemiAlgebra.copy T U) (only parsing).
End SemiAlgebra.

#[deprecated(since="mathcomp 2.6.0", use=NzAlgebra)]
Notation Algebra R := (NzAlgebra R) (only parsing).

Module Algebra.
#[deprecated(since="mathcomp 2.6.0", use=NzAlgebra.sort)]
Notation sort := (NzAlgebra.sort) (only parsing).
#[deprecated(since="mathcomp 2.6.0", use=NzAlgebra.on)]
Notation on R := (NzAlgebra.on R) (only parsing).
#[deprecated(since="mathcomp 2.6.0", use=NzAlgebra.copy)]
Notation copy T U := (NzAlgebra.copy T U) (only parsing).
End Algebra.

#[deprecated(since="mathcomp 2.6.0", use=ComNzSemiAlgebra)]
Notation ComSemiAlgebra R := (ComNzSemiAlgebra R) (only parsing).

Module ComSemiAlgebra.
#[deprecated(since="mathcomp 2.6.0", use=ComNzSemiAlgebra.sort)]
Notation sort := (ComNzSemiAlgebra.sort) (only parsing).
#[deprecated(since="mathcomp 2.6.0", use=ComNzSemiAlgebra.on)]
Notation on R := (ComNzSemiAlgebra.on R) (only parsing).
#[deprecated(since="mathcomp 2.6.0", use=ComNzSemiAlgebra.copy)]
Notation copy T U := (ComNzSemiAlgebra.copy T U) (only parsing).
End ComSemiAlgebra.

#[deprecated(since="mathcomp 2.6.0", use=ComNzAlgebra)]
Notation ComAlgebra R := (ComNzAlgebra R) (only parsing).

Module ComAlgebra.
#[deprecated(since="mathcomp 2.6.0", use=ComNzAlgebra.sort)]
Notation sort := (ComNzAlgebra.sort) (only parsing).
#[deprecated(since="mathcomp 2.6.0", use=ComNzAlgebra.on)]
Notation on R := (ComNzAlgebra.on R) (only parsing).
#[deprecated(since="mathcomp 2.6.0", use=ComNzAlgebra.copy)]
Notation copy T U := (ComNzAlgebra.copy T U) (only parsing).
End ComAlgebra.

#[deprecated(since="mathcomp 2.4.0", use=SubNzSemiRing)]
Notation SubSemiRing R := (SubNzSemiRing R) (only parsing).

Module SubSemiRing.
#[deprecated(since="mathcomp 2.4.0", use=SubNzSemiRing.sort)]
Notation sort := (SubNzSemiRing.sort) (only parsing).
#[deprecated(since="mathcomp 2.4.0", use=SubNzSemiRing.on)]
Notation on R := (SubNzSemiRing.on R) (only parsing).
#[deprecated(since="mathcomp 2.4.0", use=SubNzSemiRing.copy)]
Notation copy T U := (SubNzSemiRing.copy T U) (only parsing).
End SubSemiRing.

#[deprecated(since="mathcomp 2.4.0", use=SubComNzSemiRing)]
Notation SubComSemiRing R := (SubComNzSemiRing R) (only parsing).

Module SubComSemiRing.
#[deprecated(since="mathcomp 2.4.0", use=SubComNzSemiRing.sort)]
Notation sort  := (SubComNzSemiRing.sort) (only parsing).
#[deprecated(since="mathcomp 2.4.0", use=SubComNzSemiRing.on)]
Notation on R := (SubComNzSemiRing.on R) (only parsing).
#[deprecated(since="mathcomp 2.4.0", use=SubComNzSemiRing.copy)]
Notation copy T U := (SubComNzSemiRing.copy T U) (only parsing).
End SubComSemiRing.

#[deprecated(since="mathcomp 2.4.0", use=SubNzRing)]
Notation SubRing R := (SubNzRing R) (only parsing).

Module SubRing.
#[deprecated(since="mathcomp 2.4.0", use=SubNzRing.sort)]
Notation sort := (SubNzRing.sort) (only parsing).
#[deprecated(since="mathcomp 2.4.0", use=SubNzRing.on)]
Notation on R := (SubNzRing.on R) (only parsing).
#[deprecated(since="mathcomp 2.4.0", use=SubNzRing.copy)]
Notation copy T U := (SubNzRing.copy T U) (only parsing).
End SubRing.

#[deprecated(since="mathcomp 2.4.0", use=SubComNzRing)]
Notation SubComRing R := (SubComNzRing R) (only parsing).

Module SubComRing.
#[deprecated(since="mathcomp 2.4.0", use=SubComNzRing.sort)]
Notation sort := (SubComNzRing.sort) (only parsing).
#[deprecated(since="mathcomp 2.4.0", use=SubComNzRing.on)]
Notation on R := (SubComNzRing.on R) (only parsing).
#[deprecated(since="mathcomp 2.4.0", use=SubComNzRing.copy)]
Notation copy T U := (SubComNzRing.copy T U) (only parsing).
End SubComRing.

#[deprecated(since="mathcomp 2.6.0", use=SubNzLSemiAlgebra)]
Notation SubLSemiAlgebra R := (SubNzLSemiAlgebra R) (only parsing).

Module SubLSemiAlgebra.
#[deprecated(since="mathcomp 2.6.0", use=SubNzLSemiAlgebra.sort)]
Notation sort := (SubNzLSemiAlgebra.sort) (only parsing).
#[deprecated(since="mathcomp 2.6.0", use=SubNzLSemiAlgebra.on)]
Notation on R := (SubNzLSemiAlgebra.on R) (only parsing).
#[deprecated(since="mathcomp 2.6.0", use=SubNzLSemiAlgebra.copy)]
Notation copy T U := (SubNzLSemiAlgebra.copy T U) (only parsing).
End SubLSemiAlgebra.

#[deprecated(since="mathcomp 2.6.0", use=SubNzLalgebra)]
Notation SubLalgebra R := (SubNzLalgebra R) (only parsing).

Module SubLalgebra.
#[deprecated(since="mathcomp 2.6.0", use=SubNzLalgebra.sort)]
Notation sort := (SubNzLalgebra.sort) (only parsing).
#[deprecated(since="mathcomp 2.6.0", use=SubNzLalgebra.on)]
Notation on R := (SubNzLalgebra.on R) (only parsing).
#[deprecated(since="mathcomp 2.6.0", use=SubNzLalgebra.copy)]
Notation copy T U := (SubNzLalgebra.copy T U) (only parsing).
End SubLalgebra.

#[deprecated(since="mathcomp 2.6.0", use=SubNzSemiAlgebra)]
Notation SubSemiAlgebra R := (SubNzSemiAlgebra R) (only parsing).

Module SubSemiAlgebra.
#[deprecated(since="mathcomp 2.6.0", use=SubNzSemiAlgebra.sort)]
Notation sort := (SubNzSemiAlgebra.sort) (only parsing).
#[deprecated(since="mathcomp 2.6.0", use=SubNzSemiAlgebra.on)]
Notation on R := (SubNzSemiAlgebra.on R) (only parsing).
#[deprecated(since="mathcomp 2.6.0", use=SubNzSemiAlgebra.copy)]
Notation copy T U := (SubNzSemiAlgebra.copy T U) (only parsing).
End SubSemiAlgebra.

#[deprecated(since="mathcomp 2.6.0", use=SubNzAlgebra)]
Notation SubAlgebra R := (SubNzAlgebra R) (only parsing).

Module SubAlgebra.
#[deprecated(since="mathcomp 2.6.0", use=SubNzAlgebra.sort)]
Notation sort := (SubNzAlgebra.sort) (only parsing).
#[deprecated(since="mathcomp 2.6.0", use=SubNzAlgebra.on)]
Notation on R := (SubNzAlgebra.on R) (only parsing).
#[deprecated(since="mathcomp 2.6.0", use=SubNzAlgebra.copy)]
Notation copy T U := (SubNzAlgebra.copy T U) (only parsing).
End SubAlgebra.

(* Mixins and factories *)

Module Nmodule_isSemiRing.
#[deprecated(since="mathcomp 2.4.0", use=Nmodule_isNzSemiRing.Build)]
Notation Build R := (Nmodule_isNzSemiRing.Build R) (only parsing).
End Nmodule_isSemiRing.

Module isSemiRing.
#[deprecated(since="mathcomp 2.4.0", use=isNzSemiRing.Build)]
Notation Build R := (isNzSemiRing.Build R) (only parsing).
End isSemiRing.

#[deprecated(since="mathcomp 2.4.0", use=isNzSemiRing)]
Notation isSemiRing R := (isNzSemiRing R) (only parsing).

Module Zmodule_isRing.
#[deprecated(since="mathcomp 2.4.0", use=Zmodule_isNzRing.Build)]
Notation Build R := (Zmodule_isNzRing.Build R) (only parsing).
End Zmodule_isRing.

#[deprecated(since="mathcomp 2.4.0", use=Zmodule_isNzRing)]
Notation Zmodule_isRing R := (Zmodule_isNzRing R) (only parsing).

Module isRing.
#[deprecated(since="mathcomp 2.4.0", use=isNzRing.Build)]
Notation Build R := (isNzRing.Build R) (only parsing).
End isRing.

#[deprecated(since="mathcomp 2.4.0", use=isNzRing)]
Notation isRing R := (isNzRing R) (only parsing).

Module Lmodule_isLalgebra.
#[deprecated(since="mathcomp 2.6.0", use=LSemiModule_isLSemiAlgebra.Build)]
Notation Build R V := (LSemiModule_isLSemiAlgebra.Build R V) (only parsing).
End Lmodule_isLalgebra.

#[deprecated(since="mathcomp 2.6.0", use=LSemiModule_isLSemiAlgebra)]
Notation Lmodule_isLalgebra R V :=
  (LSemiModule_isLSemiAlgebra R V) (only parsing).

Module PzSemiRing_hasCommutativeMul.
#[deprecated(since="mathcomp 2.6.0", use=SemiRing_hasCommutativeMul.Build)]
Notation Build R := (SemiRing_hasCommutativeMul.Build R) (only parsing).
End PzSemiRing_hasCommutativeMul.

#[deprecated(since="mathcomp 2.6.0", use=SemiRing_hasCommutativeMul)]
Notation PzSemiRing_hasCommutativeMul R :=
  (SemiRing_hasCommutativeMul R) (only parsing).

Module Ring_hasCommutativeMul.
#[deprecated(since="mathcomp 2.4.0", use=SemiRing_hasCommutativeMul.Build)]
Notation Build R := (SemiRing_hasCommutativeMul.Build R) (only parsing).
End Ring_hasCommutativeMul.

#[deprecated(since="mathcomp 2.4.0", use=SemiRing_hasCommutativeMul)]
Notation Ring_hasCommutativeMul R :=
  (SemiRing_hasCommutativeMul R) (only parsing).

Module PzRing_hasCommutativeMul.
#[deprecated(since="mathcomp 2.6.0", use=SemiRing_hasCommutativeMul.Build)]
Notation Build R := (SemiRing_hasCommutativeMul.Build R) (only parsing).
End PzRing_hasCommutativeMul.

#[deprecated(since="mathcomp 2.6.0", use=SemiRing_hasCommutativeMul)]
Notation PzRing_hasCommutativeMul R :=
  (SemiRing_hasCommutativeMul R) (only parsing).

Module Nmodule_isComSemiRing.
#[deprecated(since="mathcomp 2.4.0", use=Nmodule_isComNzSemiRing.Build)]
Notation Build R := (Nmodule_isComNzSemiRing.Build R) (only parsing).
End Nmodule_isComSemiRing.

#[deprecated(since="mathcomp 2.4.0", use=Nmodule_isComNzSemiRing)]
Notation Nmodule_isComSemiRing R := (Nmodule_isComNzSemiRing R) (only parsing).

Module Zmodule_isComRing.
#[deprecated(since="mathcomp 2.4.0", use=Zmodule_isComNzRing.Build)]
Notation Build R := (Zmodule_isComNzRing.Build R) (only parsing).
End Zmodule_isComRing.

#[deprecated(since="mathcomp 2.4.0", use=Zmodule_isComNzRing)]
Notation Zmodule_isComRing R := (Zmodule_isComNzRing R) (only parsing).

Module Lalgebra_isAlgebra.
#[deprecated(since="mathcomp 2.6.0", use=LSemiAlgebra_isSemiAlgebra.Build)]
Notation Build R V := (LSemiAlgebra_isSemiAlgebra.Build R V) (only parsing).
End Lalgebra_isAlgebra.

#[deprecated(since="mathcomp 2.6.0", use=LSemiAlgebra_isSemiAlgebra)]
Notation Lalgebra_isAlgebra R V :=
  (LSemiAlgebra_isSemiAlgebra R V) (only parsing).

Module Lalgebra_isComAlgebra.
#[deprecated(since="mathcomp 2.6.0", use=LSemiAlgebra_isComSemiAlgebra.Build)]
Notation Build R V := (LSemiAlgebra_isComSemiAlgebra.Build R V) (only parsing).
End Lalgebra_isComAlgebra.

#[deprecated(since="mathcomp 2.6.0", use=LSemiAlgebra_isComSemiAlgebra)]
Notation Lalgebra_isComAlgebra R V :=
  (LSemiAlgebra_isComSemiAlgebra R V) (only parsing).

Module isSubSemiRing.
#[deprecated(since="mathcomp 2.4.0", use=isSubPzSemiRing.Build)]
Notation Build R S U := (isSubPzSemiRing.Build R S U) (only parsing).
End isSubSemiRing.

#[deprecated(since="mathcomp 2.4.0", use=isSubPzSemiRing)]
Notation isSubSemiRing R S U := (isSubPzSemiRing R S U) (only parsing).

Module SubNmodule_isSubSemiRing.
#[deprecated(since="mathcomp 2.4.0", use=SubNmodule_isSubNzSemiRing.Build)]
Notation Build R S U := (SubNmodule_isSubNzSemiRing.Build R S U) (only parsing).
End SubNmodule_isSubSemiRing.

#[deprecated(since="mathcomp 2.4.0", use=SubNmodule_isSubNzSemiRing)]
Notation SubNmodule_isSubSemiRing R S U :=
  (SubNmodule_isSubNzSemiRing R S U) (only parsing).

Module SubZmodule_isSubRing.
#[deprecated(since="mathcomp 2.4.0", use=SubZmodule_isSubNzRing.Build)]
Notation Build R S U := (SubZmodule_isSubNzRing.Build R S U) (only parsing).
End SubZmodule_isSubRing.

#[deprecated(since="mathcomp 2.4.0", use=SubZmodule_isSubNzRing)]
Notation SubZmodule_isSubRing R S U :=
  (SubZmodule_isSubNzRing R S U) (only parsing).

Module SubChoice_isSubSemiRing.
#[deprecated(since="mathcomp 2.4.0", use=SubChoice_isSubNzSemiRing.Build)]
Notation Build R S U := (SubChoice_isSubNzSemiRing.Build R S U) (only parsing).
End SubChoice_isSubSemiRing.

#[deprecated(since="mathcomp 2.4.0", use=SubChoice_isSubNzSemiRing)]
Notation SubChoice_isSubSemiRing R S U :=
  (SubChoice_isSubNzSemiRing R S U) (only parsing).

Module SubChoice_isSubComSemiRing.
#[deprecated(since="mathcomp 2.4.0", use=SubChoice_isSubComNzSemiRing.Build)]
Notation Build R S U :=
  (SubChoice_isSubComNzSemiRing.Build R S U) (only parsing).
End SubChoice_isSubComSemiRing.

#[deprecated(since="mathcomp 2.4.0", use=SubChoice_isSubComNzSemiRing)]
Notation SubChoice_isSubComSemiRing R S U :=
  (SubChoice_isSubComNzSemiRing R S U) (only parsing).

Module SubChoice_isSubRing.
#[deprecated(since="mathcomp 2.4.0", use=SubChoice_isSubNzRing.Build)]
Notation Build R S U := (SubChoice_isSubNzRing.Build R S U) (only parsing).
End SubChoice_isSubRing.

#[deprecated(since="mathcomp 2.4.0", use=SubChoice_isSubNzRing)]
Notation SubChoice_isSubRing R S U :=
  (SubChoice_isSubNzRing R S U) (only parsing).

Module SubChoice_isSubComRing.
#[deprecated(since="mathcomp 2.4.0", use=SubChoice_isSubComNzRing.Build)]
Notation Build R S U := (SubChoice_isSubComNzRing.Build R S U) (only parsing).
End SubChoice_isSubComRing.

#[deprecated(since="mathcomp 2.4.0", use=SubChoice_isSubComNzRing)]
Notation SubChoice_isSubComRing R S U :=
  (SubChoice_isSubComNzRing R S U) (only parsing).

Module Ring_hasMulInverse.
#[deprecated(since="mathcomp 2.4.0", use=NzRing_hasMulInverse.Build)]
Notation Build R := (NzRing_hasMulInverse.Build R) (only parsing).
End Ring_hasMulInverse.

#[deprecated(since="mathcomp 2.4.0", use=NzRing_hasMulInverse)]
Notation Ring_hasMulInverse R := (NzRing_hasMulInverse R) (only parsing).

Module ComRing_hasMulInverse.
#[deprecated(since="mathcomp 2.4.0", use=ComNzRing_hasMulInverse.Build)]
Notation Build R := (ComNzRing_hasMulInverse.Build R) (only parsing).
End ComRing_hasMulInverse.

#[deprecated(since="mathcomp 2.4.0", use=ComNzRing_hasMulInverse)]
Notation ComRing_hasMulInverse R := (ComNzRing_hasMulInverse R) (only parsing).

Module ComRing_isField.
#[deprecated(since="mathcomp 2.4.0", use=ComNzRing_isField.Build)]
Notation Build R := (ComNzRing_isField.Build R) (only parsing).
End ComRing_isField.

#[deprecated(since="mathcomp 2.4.0", use=ComNzRing_isField)]
Notation ComRing_isField R := (ComNzRing_isField R) (only parsing).

Module SubExports.

#[deprecated(since="mathcomp 2.4.0",
             note="Use [ SubNmodule_isSubNzSemiRing of U by <: ] instead.")]
Notation "[ 'SubNmodule_isSubSemiRing' 'of' U 'by' <: ]" :=
  (SubNmodule_isSubNzSemiRing.Build _ _ U (@rpred1M _ _))
  (format "[ 'SubNmodule_isSubSemiRing'  'of'  U  'by'  <: ]")
  : form_scope.
#[deprecated(since="mathcomp 2.4.0",
             note="Use [ SubChoice_isSubNzSemiRing of U by <: ] instead.")]
Notation "[ 'SubChoice_isSubSemiRing' 'of' U 'by' <: ]" :=
  (SubChoice_isSubNzSemiRing.Build _ _ U (semiringClosedP _))
  (format "[ 'SubChoice_isSubSemiRing'  'of'  U  'by'  <: ]")
  : form_scope.
#[deprecated(since="mathcomp 2.6.0",
        note="Use [ SubSemiRing_isSubComSemiRing of U by <: ] instead.")]
Notation "[ 'SubPzSemiRing_isSubComPzSemiRing' 'of' U 'by' <: ]" :=
  (SubSemiRing_isSubComSemiRing.Build _ _ U)
  (format "[ 'SubPzSemiRing_isSubComPzSemiRing'  'of'  U  'by'  <: ]")
  : form_scope.
#[deprecated(since="mathcomp 2.6.0",
        note="Use [ SubSemiRing_isSubComSemiRing of U by <: ] instead.")]
Notation "[ 'SubNzSemiRing_isSubComNzSemiRing' 'of' U 'by' <: ]" :=
  (SubSemiRing_isSubComSemiRing.Build _ _ U)
  (format "[ 'SubNzSemiRing_isSubComNzSemiRing'  'of'  U  'by'  <: ]")
  : form_scope.
#[deprecated(since="mathcomp 2.4.0",
             note="Use [ SubSemiRing_isSubComSemiRing of U by <: ] instead.")]
Notation "[ 'SubRing_isSubComRing' 'of' U 'by' <: ]" :=
  (SubSemiRing_isSubComSemiRing.Build _ _ U)
  (format "[ 'SubRing_isSubComRing'  'of'  U  'by'  <: ]")
  : form_scope.
#[deprecated(since="mathcomp 2.6.0",
             note="Use [ SubSemiRing_isSubComSemiRing of U by <: ] instead.")]
Notation "[ 'SubPzRing_isSubComPzRing' 'of' U 'by' <: ]" :=
  (SubSemiRing_isSubComSemiRing.Build _ _ U)
  (format "[ 'SubPzRing_isSubComPzRing'  'of'  U  'by'  <: ]")
  : form_scope.
#[deprecated(since="mathcomp 2.6.0",
             note="Use [ SubSemiRing_isSubComSemiRing of U by <: ] instead.")]
Notation "[ 'SubNzRing_isSubComNzRing' 'of' U 'by' <: ]" :=
  (SubSemiRing_isSubComSemiRing.Build _ _ U)
  (format "[ 'SubNzRing_isSubComNzRing'  'of'  U  'by'  <: ]")
  : form_scope.
#[deprecated(since="mathcomp 2.4.0",
             note="Use [ SubChoice_isSubComNzSemiRing of U by <: ] instead.")]
Notation "[ 'SubChoice_isSubComSemiRing' 'of' U 'by' <: ]" :=
  (SubChoice_isSubComNzSemiRing.Build _ _ U (semiringClosedP _))
  (format "[ 'SubChoice_isSubComSemiRing'  'of'  U  'by'  <: ]")
  : form_scope.
#[deprecated(since="mathcomp 2.4.0",
             note="Use [ SubZmodule_isSubNzRing of U by <: ] instead.")]
Notation "[ 'SubZmodule_isSubRing' 'of' U 'by' <: ]" :=
  (SubZmodule_isSubNzRing.Build _ _ U (subringClosedP _))
  (format "[ 'SubZmodule_isSubRing'  'of'  U  'by'  <: ]")
  : form_scope.
#[deprecated(since="mathcomp 2.4.0",
             note="Use [ SubChoice_isSubNzRing of U by <: ] instead.")]
Notation "[ 'SubChoice_isSubRing' 'of' U 'by' <: ]" :=
  (SubChoice_isSubNzRing.Build _ _ U (subringClosedP _))
  (format "[ 'SubChoice_isSubRing'  'of'  U  'by'  <: ]")
  : form_scope.
#[deprecated(since="mathcomp 2.4.0",
             note="Use [ SubChoice_isSubComNzRing of U by <: ] instead.")]
Notation "[ 'SubChoice_isSubComRing' 'of' U 'by' <: ]" :=
  (SubChoice_isSubComNzRing.Build _ _ U (subringClosedP _))
  (format "[ 'SubChoice_isSubComRing'  'of'  U  'by'  <: ]")
  : form_scope.
#[deprecated(since="mathcomp 2.6.0",
        note="Use [ SubNmodule_isSubLSemiModule of U by <: ] instead.")]
Notation "[ 'SubZmodule_isSubLmodule' 'of' U 'by' <: ]" :=
  (SubNmodule_isSubLSemiModule.Build _ _ _ U (subsemimodClosedP _))
  (format "[ 'SubZmodule_isSubLmodule'  'of'  U  'by'  <: ]")
  : form_scope.
#[deprecated(since="mathcomp 2.6.0",
      note="Use [ SubSemiRing_SubLSemiModule_isSubLSemiAlgebra of U by <: ] instead.")]
Notation "[ 'SubNzSemiRing_SubLSemiModule_isSubLSemiAlgebra' 'of' U 'by' <: ]" :=
  (SubSemiRing_SubLSemiModule_isSubLSemiAlgebra.Build _ _ _ U)
  (format "[ 'SubNzSemiRing_SubLSemiModule_isSubLSemiAlgebra'  'of'  U  'by'  <: ]")
  : form_scope.
#[deprecated(since="mathcomp 2.6.0",
      note="Use [ SubRing_SubLmodule_isSubLalgebra of U by <: ] instead.")]
Notation "[ 'SubNzRing_SubLmodule_isSubLalgebra' 'of' U 'by' <: ]" :=
  (SubRing_SubLmodule_isSubLalgebra.Build _ _ _ U)
  (format "[ 'SubNzRing_SubLmodule_isSubLalgebra'  'of'  U  'by'  <: ]")
  : form_scope.
#[deprecated(since="mathcomp 2.6.0",
        note="Use [ SubLSemiAlgebra_isSubSemiAlgebra of U by <: ] instead.")]
Notation "[ 'SubLalgebra_isSubAlgebra' 'of' U 'by' <: ]" :=
  (SubLSemiAlgebra_isSubSemiAlgebra.Build _ _ _ U)
  (format "[ 'SubLalgebra_isSubAlgebra'  'of'  U  'by'  <: ]")
  : form_scope.
#[deprecated(since="mathcomp 2.6.0",
      note="Use [ SubChoice_isSubNzLSemiAlgebra of U by <: ] instead.")]
Notation "[ 'SubChoice_isSubLSemiAlgebra' 'of' U 'by' <: ]" :=
  (SubChoice_isSubNzLSemiAlgebra.Build _ _ _ U (subsemialgClosedP _))
  (format "[ 'SubChoice_isSubLSemiAlgebra'  'of'  U  'by'  <: ]")
  : form_scope.
#[deprecated(since="mathcomp 2.6.0",
      note="Use [ SubChoice_isSubNzLalgebra of U by <: ] instead.")]
Notation "[ 'SubChoice_isSubLalgebra' 'of' U 'by' <: ]" :=
  (SubChoice_isSubNzLalgebra.Build _ _ _ U (subsemialgClosedP _))
  (format "[ 'SubChoice_isSubLalgebra'  'of'  U  'by'  <: ]")
  : form_scope.
#[deprecated(since="mathcomp 2.6.0",
             note="Use [ SubChoice_isSubNzSemiAlgebra of U by <: ] instead.")]
Notation "[ 'SubChoice_isSubSemiAlgebra' 'of' U 'by' <: ]" :=
  (SubChoice_isSubNzSemiAlgebra.Build _ _ _ U (subsemialgClosedP _))
  (format "[ 'SubChoice_isSubSemiAlgebra'  'of'  U  'by'  <: ]")
  : form_scope.
#[deprecated(since="mathcomp 2.6.0",
             note="Use [ SubChoice_isSubNzAlgebra of U by <: ] instead.")]
Notation "[ 'SubChoice_isSubAlgebra' 'of' U 'by' <: ]" :=
  (SubChoice_isSubNzAlgebra.Build _ _ _ U (subalgClosedP _))
  (format "[ 'SubChoice_isSubAlgebra'  'of'  U  'by'  <: ]")
 : form_scope.
#[deprecated(since="mathcomp 2.4.0",
             note="Use [ SubNzRing_isSubUnitRing of U by <: ] instead.")]
Notation "[ 'SubRing_isSubUnitRing' 'of' U 'by' <: ]" :=
  (SubNzRing_isSubUnitRing.Build _ _ U (divringClosedP _))
  (format "[ 'SubRing_isSubUnitRing'  'of'  U  'by'  <: ]")
  : form_scope.

End SubExports.
HB.export SubExports.

(* Definitions and lemmas *)

#[deprecated(since="mathcomp 2.4.0", use=Nmodule_isNzSemiRing)]
Notation Nmodule_isSemiRing R := (Nmodule_isNzSemiRing R) (only parsing).

#[deprecated(since="mathcomp 2.4.0", use=Algebra.nmod_closed)]
Definition addr_closed := nmod_closed.

#[deprecated(since="mathcomp 2.6.0", use=Algebra.zmod_closed0D)]
Definition zmod_closedD := zmod_closed0D.

#[deprecated(since="mathcomp 2.6.0", use=Algebra.subr_closed)]
Definition subr_2closed := subr_closed.

#[deprecated(since="mathcomp 2.4.0", use=pchar)]
Notation char := pchar (only parsing).

#[deprecated(since="mathcomp 2.4.0", use=has_pchar0)]
Notation has_char0 L := (has_pchar0 L) (only parsing).

#[deprecated(since="mathcomp 2.4.0", use=pFrobenius_aut)]
Notation Frobenius_aut := pFrobenius_aut (only parsing).
#[deprecated(since="mathcomp 2.4.0", use=pcharf0)]
Notation charf0 := pcharf0 (only parsing).
#[deprecated(since="mathcomp 2.4.0", use=pcharf_prime)]
Notation charf_prime := pcharf_prime (only parsing).
#[deprecated(since="mathcomp 2.4.0", use=mulrn_pchar)]
Notation mulrn_char := mulrn_pchar (only parsing).
#[deprecated(since="mathcomp 2.4.0", use=natr_mod_pchar)]
Notation natr_mod_char := natr_mod_pchar (only parsing).
#[deprecated(since="mathcomp 2.4.0", use=dvdn_pcharf)]
Notation dvdn_charf := dvdn_pcharf (only parsing).
#[deprecated(since="mathcomp 2.4.0", use=pcharf_eq)]
Notation charf_eq := pcharf_eq (only parsing).
#[deprecated(since="mathcomp 2.4.0", use=bin_lt_pcharf_0)]
Notation bin_lt_charf_0 := bin_lt_pcharf_0 (only parsing).
#[deprecated(since="mathcomp 2.4.0", use=pFrobenius_autE)]
Notation Frobenius_autE := pFrobenius_autE (only parsing).
#[deprecated(since="mathcomp 2.4.0", use=pFrobenius_aut0)]
Notation Frobenius_aut0 := pFrobenius_aut0 (only parsing).
#[deprecated(since="mathcomp 2.4.0", use=pFrobenius_aut1)]
Notation Frobenius_aut1 := pFrobenius_aut1 (only parsing).
#[deprecated(since="mathcomp 2.4.0", use=pFrobenius_autD_comm)]
Notation Frobenius_autD_comm := pFrobenius_autD_comm (only parsing).
#[deprecated(since="mathcomp 2.4.0", use=pFrobenius_autMn)]
Notation Frobenius_autMn := pFrobenius_autMn (only parsing).
#[deprecated(since="mathcomp 2.4.0", use=pFrobenius_aut_nat)]
Notation Frobenius_aut_nat := pFrobenius_aut_nat (only parsing).
#[deprecated(since="mathcomp 2.4.0", use=pFrobenius_autM_comm)]
Notation Frobenius_autM_comm := pFrobenius_autM_comm (only parsing).
#[deprecated(since="mathcomp 2.4.0", use=pFrobenius_autX)]
Notation Frobenius_autX := pFrobenius_autX (only parsing).
#[deprecated(since="mathcomp 2.4.0", use=addrr_pchar2)]
Notation addrr_char2 := addrr_pchar2 (only parsing).

#[deprecated(since="mathcomp 2.4.0", use=pFrobenius_autN)]
Notation Frobenius_autN := pFrobenius_autN (only parsing).
#[deprecated(since="mathcomp 2.4.0", use=pFrobenius_autB_comm)]
Notation Frobenius_autB_comm := pFrobenius_autB_comm (only parsing).
#[deprecated(since="mathcomp 2.4.0", use=exprNn_pchar)]
Notation exprNn_char := exprNn_pchar (only parsing).
#[deprecated(since="mathcomp 2.4.0", use=oppr_pchar2)]
Notation oppr_char2 := oppr_pchar2 (only parsing).
#[deprecated(since="mathcomp 2.4.0", use=subr_pchar2)]
Notation subr_char2 := subr_pchar2 (only parsing).
#[deprecated(since="mathcomp 2.4.0", use=addrK_pchar2)]
Notation addrK_char2 := addrK_pchar2 (only parsing).
#[deprecated(since="mathcomp 2.4.0", use=addKr_pchar2)]
Notation addKr_char2 := addKr_pchar2 (only parsing).

#[deprecated(since="mathcomp 2.5.0", use=monoid_morphism)]
Definition multiplicative (R S : pzSemiRingType) (f : R -> S) : Prop :=
  {morph f : x y / x * y}%R * (f 1 = 1).

#[warning="-deprecated-since-mathcomp-2.5.0"]
HB.factory Record isMultiplicative (R S : pzSemiRingType) (f : R -> S) := {
      rmorphism_subproof : multiplicative f
}.
HB.builders Context R S f & isMultiplicative R S f.

#[warning="-HB.no-new-instance"]
HB.instance Definition _ := isMonoidMorphism.Build R S f
                              (rmorphism_subproof.2, rmorphism_subproof.1).

HB.end.

#[warning="-deprecated-reference-since-mathcomp-2.5.0",
  deprecated(since="mathcomp 2.5.0", use=rmorphism_monoidP)]
Definition rmorphismMP (R S : pzSemiRingType) (f : {rmorphism R -> S}) :
  multiplicative f := (fun p => (p.2, p.1)) (rmorphism_monoidP f).

#[deprecated(since="mathcomp 2.4.0", use=rmorph_pchar)]
Notation rmorph_char := rmorph_pchar (only parsing).

#[deprecated(since="mathcomp 2.5.0", use=zmod_morphism_linear)]
Definition additive_linear := zmod_morphism_linear.

#[deprecated(since="mathcomp 2.5.0", use=pFrobenius_aut_is_monoid_morphism)]
Notation pFrobenius_aut_is_multiplicative :=
  (fun p => (p.2, p.1) \o pFrobenius_aut_is_monoid_morphism) (only parsing).
#[deprecated(since="mathcomp 2.4.0", use=exprDn_pchar)]
Notation exprDn_char := exprDn_pchar (only parsing).

#[deprecated(since="mathcomp 2.4.0", use=natf_neq0_pchar)]
Notation natf_neq0 := natf_neq0_pchar (only parsing).
#[deprecated(since="mathcomp 2.4.0", use=natf0_pchar)]
Notation natf0_char := natf0_pchar (only parsing).
#[deprecated(since="mathcomp 2.4.0", use=pcharf'_nat)]
Notation charf'_nat := pcharf'_nat (only parsing).
#[deprecated(since="mathcomp 2.4.0", use=pcharf0P)]
Notation charf0P := pcharf0P (only parsing).

#[deprecated(since="mathcomp 2.4.0", use=pchar0_natf_div)]
Notation char0_natf_div := pchar0_natf_div (only parsing).
#[deprecated(since="mathcomp 2.4.0", use=fmorph_pchar)]
Notation fmorph_char := fmorph_pchar (only parsing).
#[deprecated(since="mathcomp 2.4.0", use=pchar_lalg)]
Notation char_lalg := pchar_lalg (only parsing).

#[deprecated(since="mathcomp 2.6.0",
      note="Use [ SubSemiRing_SubLSemiModule_isSubLSemiAlgebra of U by <: ] instead.")]
Lemma lalgMixin
  (R : pzRingType) (A : pzLalgType R) (B : lmodType R) (f : B -> A) :
  phant B -> injective f -> scalable f ->
  forall mulB, {morph f : x y / mulB x y >-> x * y} ->
  forall a u v, a *: (mulB u v) = mulB (a *: u) v.
Proof.
by move=> _ injf fZ mulB fM a x y; apply: injf; rewrite !(fZ, fM) scalerAl.
Qed.

#[deprecated(since="mathcomp 2.6.0",
      note="Use [ SubSemiRing_isSubComSemiRing of U by <: ] instead.")]
Lemma comRingMixin (R : comPzRingType) (T : pzRingType) (f : T -> R) :
  phant T -> injective f -> {morph f : x y / x * y} -> commutative (@mul T).
Proof. by move=> _ inj_f fM x y; apply: inj_f; rewrite !fM mulrC. Qed.

#[deprecated(since="mathcomp 2.6.0",
      note="Use [ SubLSemiAlgebra_isSubSemiAlgebra of U by <: ] instead.")]
Lemma algMixin
  (R : pzRingType) (A : pzAlgType R) (B : pzLalgType R) (f : B -> A) :
  phant B -> injective f -> {morph f : x y / x * y} -> scalable f ->
  forall k (x y : B), k *: (x * y) = x * (k *: y).
Proof.
by move=> _ inj_f fM fZ a x y; apply: inj_f; rewrite !(fM, fZ) scalerAr.
Qed.

Module Theory.
Export GRing.Theory.
#[deprecated(since="mathcomp 2.4.0", use=pcharf0)]
Definition charf0 := pcharf0.
#[deprecated(since="mathcomp 2.4.0", use=pcharf_prime)]
Definition charf_prime := pcharf_prime.
#[deprecated(since="mathcomp 2.4.0", use=mulrn_pchar)]
Definition mulrn_char := mulrn_pchar.
#[deprecated(since="mathcomp 2.4.0", use=dvdn_pcharf)]
Definition dvdn_charf := dvdn_pcharf.
#[deprecated(since="mathcomp 2.4.0", use=pcharf_eq)]
Definition charf_eq := pcharf_eq.
#[deprecated(since="mathcomp 2.4.0", use=bin_lt_pcharf_0)]
Definition bin_lt_charf_0 := bin_lt_pcharf_0.
#[deprecated(since="mathcomp 2.4.0", use=pFrobenius_autE)]
Definition Frobenius_autE := pFrobenius_autE.
#[deprecated(since="mathcomp 2.4.0", use=pFrobenius_aut0)]
Definition Frobenius_aut0 := pFrobenius_aut0.
#[deprecated(since="mathcomp 2.4.0", use=pFrobenius_aut1)]
Definition Frobenius_aut1 := pFrobenius_aut1.
#[deprecated(since="mathcomp 2.4.0", use=pFrobenius_autD_comm)]
Definition Frobenius_autD_comm := pFrobenius_autD_comm.
#[deprecated(since="mathcomp 2.4.0", use=pFrobenius_autMn)]
Definition Frobenius_autMn := pFrobenius_autMn.
#[deprecated(since="mathcomp 2.4.0", use=pFrobenius_aut_nat)]
Definition Frobenius_aut_nat := pFrobenius_aut_nat.
#[deprecated(since="mathcomp 2.4.0", use=pFrobenius_autM_comm)]
Definition Frobenius_autM_comm := pFrobenius_autM_comm.
#[deprecated(since="mathcomp 2.4.0", use=pFrobenius_autX)]
Definition Frobenius_autX := pFrobenius_autX.
#[deprecated(since="mathcomp 2.4.0", use=pFrobenius_autN)]
Definition Frobenius_autN := pFrobenius_autN.
#[deprecated(since="mathcomp 2.4.0", use=pFrobenius_autB_comm)]
Definition Frobenius_autB_comm := pFrobenius_autB_comm.
#[deprecated(since="mathcomp 2.4.0", use=exprNn_pchar)]
Definition exprNn_char := exprNn_pchar.
#[deprecated(since="mathcomp 2.4.0", use=addrr_pchar2)]
Definition addrr_char2 := addrr_pchar2.
#[deprecated(since="mathcomp 2.4.0", use=oppr_pchar2)]
Definition oppr_char2 := oppr_pchar2.
#[deprecated(since="mathcomp 2.4.0", use=addrK_pchar2)]
Definition addrK_char2 := addrK_pchar2.
#[deprecated(since="mathcomp 2.4.0", use=addKr_pchar2)]
Definition addKr_char2 := addKr_pchar2.
#[deprecated(since="mathcomp 2.4.0", use=exprDn_pchar)]
Definition exprDn_char := exprDn_pchar.
#[warning="-deprecated-since-mathcomp-2.5.0",
  deprecated(since="mathcomp 2.5.0", use=nmod_morphism)]
Definition semi_additive := semi_additive.
#[warning="-deprecated-since-mathcomp-2.5.0",
  deprecated(since="mathcomp 2.5.0", use=zmod_morphism)]
Definition additive := additive.
#[warning="-deprecated-since-mathcomp-2.5.0",
  deprecated(since="mathcomp 2.5.0", use=can2_nmod_morphism)]
Definition can2_semi_additive := can2_semi_additive.
#[warning="-deprecated-since-mathcomp-2.5.0",
  deprecated(since="mathcomp 2.5.0", use=can2_zmod_morphism)]
Definition can2_additive := can2_additive.
#[warning="-deprecated-since-mathcomp-2.5.0",
  deprecated(since="mathcomp 2.5.0", use=monoid_morphism)]
Definition multiplicative := multiplicative.
#[warning="-deprecated-since-mathcomp-2.5.0",
  deprecated(since="mathcomp 2.5.0", use=rmorphism_monoidP)]
Definition rmorphismMP := rmorphismMP.
#[deprecated(since="mathcomp 2.4.0", use=rmorph_pchar)]
Definition rmorph_char := rmorph_pchar.
#[warning="-deprecated-since-mathcomp-2.5.0",
  deprecated(since="mathcomp 2.5.0", use=can2_monoid_morphism)]
Definition can2_rmorphism := can2_rmorphism.
#[warning="-deprecated-since-mathcomp-2.5.0",
  deprecated(since="mathcomp 2.5.0", use=nmod_morphism_semilinear)]
Definition additive_semilinear := additive_semilinear.
#[warning="-deprecated-since-mathcomp-2.5.0",
  deprecated(since="mathcomp 2.5.0", use=zmod_morphism_linear)]
Definition additive_linear := additive_linear.
#[deprecated(since="mathcomp 2.4.0", use=pchar_lalg)]
Definition char_lalg := pchar_lalg.
#[deprecated(since="mathcomp 2.4.0", use=natf_neq0_pchar)]
Definition natf_neq0 := natf_neq0_pchar.
#[deprecated(since="mathcomp 2.4.0", use=natf0_pchar)]
Definition natf0_char := natf0_pchar.
#[deprecated(since="mathcomp 2.4.0", use=pcharf'_nat)]
Definition charf'_nat := pcharf'_nat.
#[deprecated(since="mathcomp 2.4.0", use=pcharf0P)]
Definition charf0P := pcharf0P.
#[deprecated(since="mathcomp 2.4.0", use=pchar0_natf_div)]
Definition char0_natf_div := pchar0_natf_div.
#[deprecated(since="mathcomp 2.4.0", use=fmorph_pchar)]
Definition fmorph_char := fmorph_pchar.
End Theory.

Module AllExports. HB.reexport. End AllExports.

End GRing.

Export AllExports.

#[deprecated(since="mathcomp 2.4.0",
             note="Try pzSemiRingType (the potentially-zero counterpart) first, or use nzSemiRingType instead.")]
Notation semiRingType := (nzSemiRingType) (only parsing).
#[deprecated(since="mathcomp 2.4.0",
             note="Try pzRingType (the potentially-zero counterpart) first, or use nzRingType instead.")]
Notation ringType := (nzRingType) (only parsing).
#[deprecated(since="mathcomp 2.4.0",
             note="Try comPzSemiRingType (the potentially-zero counterpart) first, or use comNzSemiRingType instead.")]
Notation comSemiRingType := (comNzSemiRingType) (only parsing).
#[deprecated(since="mathcomp 2.4.0",
             note="Try comPzRingType (the potentially-zero counterpart) first, or use comNzRingType instead.")]
Notation comRingType := (comNzRingType) (only parsing).
#[deprecated(since="mathcomp 2.4.0",
             note="Try subPzSemiRingType (the potentially-zero counterpart) first, or use subNzSemiRingType instead.")]
Notation subSemiRingType := (subNzSemiRingType) (only parsing).
#[deprecated(since="mathcomp 2.4.0",
             note="Try subComPzSemiRingType (the potentially-zero counterpart) first, or use subComNzSemiRingType instead.")]
Notation subComSemiRingType := (subComNzSemiRingType) (only parsing).
#[deprecated(since="mathcomp 2.4.0",
             note="Try subPzRingType (the potentially-zero counterpart) first, or use subNzRingType instead.")]
Notation subRingType := (subNzRingType) (only parsing).
#[deprecated(since="mathcomp 2.4.0",
             note="Try subComPzRingType (the potentially-zero counterpart) first, or use subComNzRingType instead.")]
Notation subComRingType := (subComNzRingType) (only parsing).
#[deprecated(since="mathcomp 2.6.0",
             note="Try pzLSemiAlgType (the potentially-zero counterpart) first, or use nzLSemiAlgType instead.")]
Notation lSemiAlgType := (nzLSemiAlgType) (only parsing).
#[deprecated(since="mathcomp 2.6.0",
             note="Try pzLalgType (the potentially-zero counterpart) first, or use nzLalgType instead.")]
Notation lalgType := (nzLalgType) (only parsing).
#[deprecated(since="mathcomp 2.6.0",
             note="Try pzSemiAlgType (the potentially-zero counterpart) first, or use nzSemiAlgType instead.")]
Notation semiAlgType := (nzSemiAlgType) (only parsing).
#[deprecated(since="mathcomp 2.6.0",
             note="Try pzAlgType (the potentially-zero counterpart) first, or use nzAlgType instead.")]
Notation algType := (nzAlgType) (only parsing).
#[deprecated(since="mathcomp 2.6.0",
             note="Try comPzSemiAlgType (the potentially-zero counterpart) first, or use comNzSemiAlgType instead.")]
Notation comSemiAlgType := (comNzSemiAlgType) (only parsing).
#[deprecated(since="mathcomp 2.6.0",
             note="Try comPzAlgType (the potentially-zero counterpart) first, or use comNzAlgType instead.")]
Notation comAlgType := (comNzAlgType) (only parsing).
#[deprecated(since="mathcomp 2.6.0",
             note="Try subPzLSemiAlgType (the potentially-zero counterpart) first, or use subNzLSemiAlgType instead.")]
Notation subLSemiAlgType := (subNzLSemiAlgType) (only parsing).
#[deprecated(since="mathcomp 2.6.0",
             note="Try subPzLalgType (the potentially-zero counterpart) first, or use subNzLalgType instead.")]
Notation subLalgType := (subNzLalgType) (only parsing).
#[deprecated(since="mathcomp 2.6.0",
             note="Try subPzSemiAlgType (the potentially-zero counterpart) first, or use subNzSemiAlgType instead.")]
Notation subSemiAlgType := (subNzSemiAlgType) (only parsing).
#[deprecated(since="mathcomp 2.6.0",
             note="Try subPzAlgType (the potentially-zero counterpart) first, or use subNzAlgType instead.")]
Notation subAlgType := (subNzAlgType) (only parsing).

#[deprecated(since="mathcomp 2.4.0", note="Use [pchar R] instead.")]
Notation "[ 'char' R ]" := (GRing.pchar R) : ring_scope.
#[deprecated(since="mathcomp 2.4.0", use=has_pchar0)]
Notation has_char0 R := (GRing.pchar R =i pred0).
#[deprecated(since="mathcomp 2.4.0", use=pFrobenius_aut)]
Notation Frobenius_aut chRp := (pFrobenius_aut chRp).

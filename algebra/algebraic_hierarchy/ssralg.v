(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
From mathcomp Require Import choice fintype finfun bigop prime binomial.
From mathcomp Require Export nmodule rings_modules_and_algebras divalg decfield.

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

(* Mixins and factories *)

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

Module SubZmodule_isSubPzRing.
#[deprecated(since="mathcomp 2.6.0", use=SubNmodule_isSubSemiRing.Build)]
Notation Build R S U := (SubNmodule_isSubSemiRing.Build R S U) (only parsing).
End SubZmodule_isSubPzRing.

#[deprecated(since="mathcomp 2.6.0", use=SubNmodule_isSubSemiRing)]
Notation SubZmodule_isSubPzRing R S U :=
  (SubNmodule_isSubSemiRing R S U) (only parsing).

Module SubZmodule_isSubNzRing.
#[deprecated(since="mathcomp 2.6.0", use=SubNmodule_isSubNzSemiRing.Build)]
Notation Build R S U := (SubNmodule_isSubNzSemiRing.Build R S U) (only parsing).
End SubZmodule_isSubNzRing.

#[deprecated(since="mathcomp 2.6.0", use=SubNmodule_isSubNzSemiRing)]
Notation SubZmodule_isSubNzRing R S U :=
  (SubNmodule_isSubNzSemiRing R S U) (only parsing).

Module SubZmodule_isSubRing.
#[deprecated(since="mathcomp 2.4.0", use=SubNmodule_isSubNzSemiRing.Build)]
Notation Build R S U := (SubNmodule_isSubNzSemiRing.Build R S U) (only parsing).
End SubZmodule_isSubRing.

#[deprecated(since="mathcomp 2.4.0", use=SubNmodule_isSubNzSemiRing)]
Notation SubZmodule_isSubRing R S U :=
  (SubNmodule_isSubNzSemiRing R S U) (only parsing).

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
#[deprecated(since="mathcomp 2.6.0",
             note="Use [ SubNmodule_isSubNzSemiRing of U by <: ] instead.")]
Notation "[ 'SubZmodule_isSubNzRing' 'of' U 'by' <: ]" :=
  (SubNmodule_isSubNzSemiRing.Build _ _ U (subringClosedP _))
  (format "[ 'SubZmodule_isSubNzRing'  'of'  U  'by'  <: ]")
  : form_scope.
#[deprecated(since="mathcomp 2.4.0",
             note="Use [ SubZmodule_isSubNzRing of U by <: ] instead.")]
Notation "[ 'SubZmodule_isSubRing' 'of' U 'by' <: ]" :=
  (SubNmodule_isSubNzSemiRing.Build _ _ U (subringClosedP _))
  (format "[ 'SubZmodule_isSubRing'  'of'  U  'by'  <: ]")
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
#[deprecated(since="mathcomp 2.4.0",
             note="Use [ SubNzRing_isSubUnitRing of U by <: ] instead.")]
Notation "[ 'SubRing_isSubUnitRing' 'of' U 'by' <: ]" :=
  (SubNzRing_isSubUnitRing.Build _ _ U (divringClosedP _))
  (format "[ 'SubRing_isSubUnitRing'  'of'  U  'by'  <: ]")
  : form_scope.

End SubExports.
HB.export SubExports.

(* Definitions and lemmas *)

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
Definition multiplicative (R S : semiRingType) (f : R -> S) : Prop :=
  {morph f : x y / x * y}%R * (f 1 = 1).

#[warning="-deprecated-since-mathcomp-2.5.0"]
HB.factory Record isMultiplicative (R S : semiRingType) (f : R -> S) := {
      rmorphism_subproof : multiplicative f
}.
HB.builders Context R S f & isMultiplicative R S f.

#[warning="-HB.no-new-instance"]
HB.instance Definition _ := isMonoidMorphism.Build R S f
                              (rmorphism_subproof.2, rmorphism_subproof.1).

HB.end.

(* It will be possible to remove this factory after the release of MathComp 2.7.0 *)
HB.factory Record SubPzRing_isSubComPzRing (R : comRingType) S U
    & SubRing R S U := {}.

HB.builders Context R S U & SubPzRing_isSubComPzRing R S U.
HB.instance Definition _ := SubSemiRing_isSubComSemiRing.Build R S U.
HB.end.

#[warning="-deprecated-reference-since-mathcomp-2.5.0",
  deprecated(since="mathcomp 2.5.0", use=rmorphism_monoidP)]
Definition rmorphismMP (R S : semiRingType) (f : {rmorphism R -> S}) :
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
  (R : ringType) (A : lalgType R) (B : lmodType R) (f : B -> A) :
  phant B -> injective f -> scalable f ->
  forall mulB, {morph f : x y / mulB x y >-> x * y} ->
  forall a u v, a *: (mulB u v) = mulB (a *: u) v.
Proof.
by move=> _ injf fZ mulB fM a x y; apply: injf; rewrite !(fZ, fM) scalerAl.
Qed.

#[deprecated(since="mathcomp 2.6.0",
      note="Use [ SubSemiRing_isSubComSemiRing of U by <: ] instead.")]
Lemma comRingMixin (R : comRingType) (T : ringType) (f : T -> R) :
  phant T -> injective f -> {morph f : x y / x * y} -> commutative (@mul T).
Proof. by move=> _ inj_f fM x y; apply: inj_f; rewrite !fM mulrC. Qed.

#[deprecated(since="mathcomp 2.6.0",
      note="Use [ SubLSemiAlgebra_isSubSemiAlgebra of U by <: ] instead.")]
Lemma algMixin
  (R : ringType) (A : algType R) (B : lalgType R) (f : B -> A) :
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

Module AllExports.
#[deprecated(since="mathcomp 2.6.0", use=nmod_closed)]
Notation addr_closed := nmod_closed.
HB.reexport.
End AllExports.

End GRing.

Export AllExports.

#[deprecated(since="mathcomp 2.4.0", note="Use [pchar R] instead.")]
Notation "[ 'char' R ]" := (GRing.pchar R) : ring_scope.
#[deprecated(since="mathcomp 2.4.0", use=has_pchar0)]
Notation has_char0 R := (GRing.pchar R =i pred0).
#[deprecated(since="mathcomp 2.4.0", use=pFrobenius_aut)]
Notation Frobenius_aut chRp := (pFrobenius_aut chRp).

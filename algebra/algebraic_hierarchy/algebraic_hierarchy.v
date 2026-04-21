From mathcomp Require Import ssreflect ssrfun.
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

#[deprecated(since="mathcomp 2.5.0", use=GRing.monoid_morphism)]
Definition multiplicative (R S : pzSemiRingType) (f : R -> S) : Prop :=
  {morph f : x y / x * y}%R * (f 1 = 1)%R.

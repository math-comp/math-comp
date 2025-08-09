(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* TODO: remove this file when requiring Rocq >= 9.2
   and use the identical file in Corelib instead *)

From Corelib Require Import BinNums.
From mathcomp Require Import RatDef.

Set Implicit Arguments.

(** Definition of multivariable polynomials with coefficients in C :
   Type [Pol] represents [X1 ... Xn].
   The representation is Horner's where a [n] variable polynomial
   (C[X1..Xn]) is seen as a polynomial on [X1] whose coefficients
   are polynomials with [n-1] variables (C[X2..Xn]).
   There are several optimisations to make the repr more compact:
   - [Pc c] is the constant polynomial of value c
      == c*X1^0*..*Xn^0
   - [Pinj j Q] is a polynomial constant w.r.t the [j] first variables.
       variable indices are shifted of j in Q.
      == X1^0 *..* Xj^0 * Q{X1 <- Xj+1;..; Xn-j <- Xn}
   - [PX P i Q] is an optimised Horner form of P*X^i + Q
       with P not the null polynomial
      == P * X1^i + Q{X1 <- X2; ..; Xn-1 <- Xn}
   In addition:
   - polynomials of the form (PX (PX P i (Pc 0)) j Q) are forbidden
     since they can be represented by the simpler form (PX P (i+j) Q)
   - (Pinj i (Pinj j P)) is (Pinj (i+j) P)
   - (Pinj i (Pc c)) is (Pc c) *)
#[universes(template)]
Inductive Pol {C} : Type :=
| Pc : C -> Pol
| Pinj : positive -> Pol -> Pol
| PX : Pol -> positive -> Pol -> Pol.
Arguments Pol : clear implicits.

Register Pc as micromega.Pol.Pc.
Register Pinj as micromega.Pol.Pinj.
Register PX as micromega.Pol.PX.

Section Micromega.
Variable C : Type.

Inductive Psatz : Type :=
| PsatzLet: Psatz -> Psatz -> Psatz
| PsatzIn : nat -> Psatz
| PsatzSquare : Pol C -> Psatz
| PsatzMulC : Pol C -> Psatz -> Psatz
| PsatzMulE : Psatz -> Psatz -> Psatz
| PsatzAdd : Psatz -> Psatz -> Psatz
| PsatzC : C -> Psatz
| PsatzZ : Psatz.
End Micromega.

Register PsatzLet as micromega.Psatz.PsatzLet.
Register PsatzIn as micromega.Psatz.PsatzIn.
Register PsatzSquare as micromega.Psatz.PsatzSquare.
Register PsatzMulC as micromega.Psatz.PsatzMulC.
Register PsatzMulE as micromega.Psatz.PsatzMulE.
Register PsatzAdd as micromega.Psatz.PsatzAdd.
Register PsatzC as micromega.Psatz.PsatzC.
Register PsatzZ as micromega.Psatz.PsatzZ.

Definition QWitness := Psatz Q.

Register QWitness as micromega.QWitness.type.

Definition ZWitness := Psatz Z.

Inductive ZArithProof :=
| DoneProof
| RatProof : ZWitness -> ZArithProof -> ZArithProof
| CutProof : ZWitness -> ZArithProof -> ZArithProof
| SplitProof : Pol Z -> ZArithProof -> ZArithProof -> ZArithProof
| EnumProof : ZWitness -> ZWitness -> list ZArithProof -> ZArithProof
| ExProof : positive -> ZArithProof -> ZArithProof
(*ExProof x : exists z t, x = z - t /\ z >= 0 /\ t >= 0 *)
.

Register ZArithProof as micromega.ZArithProof.type.
Register DoneProof as micromega.ZArithProof.DoneProof.
Register RatProof as micromega.ZArithProof.RatProof.
Register CutProof as micromega.ZArithProof.CutProof.
Register SplitProof as micromega.ZArithProof.SplitProof.
Register EnumProof as micromega.ZArithProof.EnumProof.
Register ExProof as micromega.ZArithProof.ExProof.

From Corelib Require Import PosDef.
From mathcomp Require Import RatDef.
From mathcomp Require Import ssreflect ssrfun ssrbool seq ssralg ssrnum lra.
From mathcomp Require Import micromega_formula micromega_witness.
From mathcomp Require Import micromega_tactics.

Local Open Scope ring_scope.

Goal forall (R : realFieldType) (x y : R),
  x + 2 * y <= 3 -> 2 * x + y <= 3 -> x + y <= 2.
Proof.
move=> R x y.
(* the formula as it would be obtained from reification *)
pose (ff :=
  IMPL
    (A isProp
       {|
         Flhs := PEadd (PEX xH) (PEmul (PEc ((Qmake (Zpos (xO xH)) xH))) (PEX (xO xH)));
         Fop := OpLe;
         Frhs := PEc (Qmake (Zpos (xI xH)) xH)
       |} tt) None
    (IMPL
       (A isProp
          {|
            Flhs := PEadd (PEmul (PEc (Qmake (Zpos (xO xH)) xH)) (PEX xH)) (PEX (xO xH));
            Fop := OpLe;
            Frhs := PEc (Qmake (Zpos (xI xH)) xH)
          |} tt) None
       (A isProp
          {| Flhs := PEadd (PEX xH) (PEX (xO xH)); Fop := OpLe; Frhs := PEc (Qmake (Zpos (xO xH)) xH) |} tt))
  : BFormula (Formula Q) isProp).
(* getting the witness *)
let ff' := eval unfold ff in ff in wlra_Q wit ff'.
(* just a check (for the test, wouldn't be there in actual impleme) *)
Check erefl : wit = (PsatzAdd (PsatzIn Q 2)
  (PsatzAdd (PsatzIn Q 1) (PsatzMulE (PsatzC (Qmake (Zpos (xI xH)) xH)) (PsatzIn Q 0))) :: nil).
(* calling the tactic and evaluating the checker with vm_compute *)
by apply: (@lra.Internals.QTautoCheckerT _ [:: x; y] ff wit); vm_compute.
Qed.

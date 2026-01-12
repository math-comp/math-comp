(* This file is largely based on the ring_error.v file from                  *)
(* https://github.com/math-comp/algebra-tactics                              *)
From mathcomp Require Import ssreflect ssralg ring.

(* A failure to test the error message *)

Goal forall (R : comRingType) (a : R), (a + a = a)%R.
Proof.
move=> R a.
Fail ring. (* prints Not a valid ring equation. *)
ring || idtac "elpi-tactic failure caught by ltac".
Abort.

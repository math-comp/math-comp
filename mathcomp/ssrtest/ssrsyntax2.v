(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssrsyntax1.
Require Import Arith.

Goal (forall a b, a + b = b + a).
intros.
rewrite plus_comm, plus_comm.
split.
Qed.


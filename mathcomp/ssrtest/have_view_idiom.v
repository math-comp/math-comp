(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrbool.

Lemma test (a b : bool) (pab : a && b) : b.
have {pab} /= /andP [pa -> //] /= : true && (a && b) := pab.
Qed.

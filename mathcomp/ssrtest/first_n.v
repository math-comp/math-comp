(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrbool.

Lemma test : False -> (bool -> False -> True -> True) -> True.
move=> F; let w := constr:(2) in apply; last w first.
- by apply: F.
- by apply: I.
by apply: true.
Qed.
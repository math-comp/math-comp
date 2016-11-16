(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.

Ltac mycut x :=
  let tx := type of x in
  cut tx.

Lemma test : True.
Proof.
by mycut I=> [ x | ]; [ exact x | exact I ].
Qed.
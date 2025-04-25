(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From Corelib Require Export ssreflect.
Global Set SsrOldRewriteGoalsOrder.
Global Set Asymmetric Patterns.
Global Set Bullet Behavior "None".

#[deprecated(since="mathcomp 2.3.0", note="Use `Arguments def : simpl never` instead (should work fine since Coq 8.18).")]
Notation nosimpl t := (nosimpl t).

(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require mathcomp.ssreflect.ssreflect.
Require Import Arith.

Goal (forall a b, a + b = b + a).
intros.
rewrite plus_comm, plus_comm.
split.
Abort.

Module Foo.
Import ssreflect.

Goal (forall a b, a + b = b + a).
intros.
rewrite 2![_ + _]plus_comm.
split.
Abort.
End Foo.

Goal (forall a b, a + b = b + a).
intros.
rewrite plus_comm, plus_comm.
split.
Abort.
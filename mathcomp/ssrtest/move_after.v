(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.


Goal True -> True -> True.
move=> H1 H2.
move H1 after H2.
Admitted.

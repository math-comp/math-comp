Require Import ssreflect.

Definition x := 3.
Opaque x.

Goal x = 3.
Fail rewrite /x.
Admitted.
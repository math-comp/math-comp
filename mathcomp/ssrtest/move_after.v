Require Import ssreflect.

Goal True -> True -> True.
move=> H1 H2.
move H1 after H2.
Admitted.

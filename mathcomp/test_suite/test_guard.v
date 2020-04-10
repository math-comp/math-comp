From mathcomp Require Import all_ssreflect.

Inductive tree := Node { children : seq tree }.

Fixpoint eq_tree (x y : tree) {struct x} : bool :=
  all2 eq_tree (children x) (children y).

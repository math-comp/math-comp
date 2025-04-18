From mathcomp Require Import all_boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive tree := Node { children : seq tree }.

Inductive ptree (T : Type) := singleton of T | branch of list (ptree T).

(* has *)
Fixpoint tree_has (T : Type) (p : pred T) (t : ptree T) : bool :=
  match t with
    | singleton x => p x
    | branch ts => has (tree_has p) ts
  end.

(* all *)
Fixpoint tree_all (T : Type) (p : pred T) (t : ptree T) : bool :=
  match t with
    | singleton x => p x
    | branch ts => all (tree_all p) ts
  end.

(* map *)
Fixpoint traverse_id (t : tree) : tree :=
  Node (map traverse_id (children t)).

(* foldr *)
Fixpoint tree_foldr (T R : Type) (f : T -> R -> R) (z : R) (t : ptree T) : R :=
  match t with
    | singleton x => f x z
    | branch ts => foldr (fun t z' => tree_foldr f z' t) z ts
  end.

(* foldl *)
Fixpoint tree_foldl (T R : Type) (f : R -> T -> R) (z : R) (t : ptree T) : R :=
  match t with
    | singleton x => f z x
    | branch ts => foldl (tree_foldl f) z ts
  end.

(* all2 *)
Fixpoint eq_tree (x y : tree) {struct x} : bool :=
  all2 eq_tree (children x) (children y).

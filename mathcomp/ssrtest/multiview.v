(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrnat.

Goal forall m n p, n <= p -> m <= n -> m <= p.
by move=> m n p le_n_p /leq_trans; apply.
Undo 1.
by move=> m n p le_n_p /leq_trans /(_ le_n_p) le_m_p; exact: le_m_p.
Undo 1.
by move=> m n p le_n_p /leq_trans ->.
Qed.

Goal forall P Q X : Prop, Q -> (True -> X -> Q = P) -> X -> P.
by move=> P Q X q V /V <-.
Qed.

Lemma test0: forall a b, a && a && b -> b.
by move=> a b; repeat move=> /andP []; move=> *.
Qed.

Lemma test1 : forall a b, a && b -> b.
by move=> a b /andP /andP /andP [] //.
Qed.

Lemma test2 : forall a b, a && b -> b.
by move=> a b /andP /andP /(@andP a) [] //.
Qed.

Lemma test3 : forall a b, a && (b && b) -> b.
by move=> a b /andP [_ /andP [_ //]].
Qed.

Lemma test4:  forall a b, a && b = b && a.
by move=> a b; apply/andP/andP=> ?; apply/andP/andP/andP; rewrite andbC; apply/andP.
Qed.

Lemma test5:  forall C I A O, (True -> O) -> (O -> A) -> (True -> A -> I) -> (I -> C) -> C.
by move=> c i a o O A I C; apply/C/I/A/O.
Qed.

Lemma test6:  forall A B, (A -> B) -> A -> B.
move=> A B A_to_B a; move/A_to_B in a; exact: a.
Qed.

Lemma test7:  forall A B, (A -> B) -> A -> B.
move=> A B A_to_B a; apply A_to_B in a; exact: a.
Qed.

Require Import ssrfun eqtype ssrnat div seq choice fintype finfun finset.

Lemma test8 (T : finType) (A B : {set T}) x (Ax : x \in A) (_ : B = A) : x \in B.
apply/subsetP: x Ax.
by rewrite H subxx.
Qed.




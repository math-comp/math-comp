Require Import ssreflect ssrfun ssrbool eqtype.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Lemma test0 (a b : unit) f : a = f b.
Proof. by rewrite !unitE.  Qed.

Lemma phE T : all_equal_to (Phant T). Proof. by case. Qed.

Lemma test1 (a b : phant nat) f : a = f b.
Proof.  by rewrite !phE.  Qed.

Lemma eq_phE (T : eqType) : all_equal_to (Phant T). Proof. by case. Qed.

Lemma test2 (a b : phant bool) f : a = locked (f b).
Proof. by rewrite !eq_phE. Qed.

Require Import ssreflect.

Definition unopt (x : option bool) := 
  if x isn't Some x then false else x.

Lemma test1 : unopt None = false /\ 
              unopt (Some false) = false /\
              unopt (Some true) = true.
Proof. by auto. Qed.


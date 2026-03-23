From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice.
From mathcomp Require Import order interval ssralg.
From mathcomp Require Import orderedzmod numdomain numfield ssrint.
From mathcomp Require Import interval_inference.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory Order.Syntax.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope order_scope.


Section Test1.

Variable R : numDomainType.
Variable x : {i01 R}.

Goal 0%:i01 = 1%:i01 :> {i01 R}.
Proof.
Abort.

Goal (- x%:num)%:itv = (- x%:num)%:itv :> {itv R & `[-1, 0]}.
Proof.
Abort.

Goal (1 - x%:num)%:i01 = x.
Proof.
Abort.

End Test1.

Section Test2.

Variable R : realDomainType.
Variable x y : {i01 R}.

Goal (x%:num * y%:num)%:i01 = x%:num%:i01.
Proof.
Abort.

End Test2.

Module Test3.
Section Test3.
Variable R : realDomainType.

Definition s_of_pq (p q : {i01 R}) : {i01 R} :=
  (1 - ((1 - p%:num)%:i01%:num * (1 - q%:num)%:i01%:num))%:i01.

Lemma s_of_p0 (p : {i01 R}) : s_of_pq p 0%:i01 = p.
Proof. by apply/val_inj; rewrite /= subr0 mulr1 subKr. Qed.

End Test3.
End Test3.

Module Test4.
Section Test4.

Type 0%:n01 : {i01 nat}.
Type 1%:n01 : {i01 nat}.
Fail Type 2%:n01 : {i01 nat}.

Type 1%:posnat : {posnum nat}.
Type 2%:posnat : {posnum nat}.
Fail Type 0%:posnat : {posnum nat}.

End Test4.
End Test4.

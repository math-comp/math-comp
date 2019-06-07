From mathcomp
Require Import ssreflect ssrfun ssrbool ssrnat eqtype bigop.
Require Import dioid.

(******************************************************************************)
(*  This file contains description of kleene operator, residuation operator   *)
(* and some lemmas around them. These operators are an extention of complete  *)
(* dioid theory. (see dioid.v)                                                *)
(*                                                                            *)
(*   * Kleene Star                                                            *)
(*         a ^i == the power i of a                                           *)
(*         a ^* == the kleene star operator (infinite sum of a ^i, i >= 0)    *)
(*         a ^+ == the 'plus' operator (infinite sum of a ^i, i > 0)          *)
(* Interesting lemmas:                                                        *)
(* * forall a and b in a complete dioid, a^* * b is the least solution of     *)
(*   x = a * x + b                                                            *)
(* * forall a and b in a complete commutative dioid, (a + b)^* = a^* * b ^*   *)
(*                                                                            *)
(*   * Residuation                                                            *)
(*        a / b == the residuation operator: forall x, a and b elements       *)
(*                 of a complete dioid then x * a <= b <-> x <= b / a         *)
(******************************************************************************)

Reserved Notation "x ^+" (at level 20, format "x ^+").
Reserved Notation "x ^*" (at level 20, format "x ^*").

Import GDioid.

Open Scope dioid_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section operatorsDefinitions.

Variable (D : completeDioidType).

Definition exp D x n := iterop n (mul D) x (e D).
Definition op_kleene D a := @set_add D (fun y => exists i, y = exp a i).
Definition op_plus D a := @set_add D (fun y => exists i : nat, (0 < i)%nat /\ y = exp a i).
Definition div (b a : D) : D := set_add (fun x => x * a <= b ).

End operatorsDefinitions.

Notation "a ^ i" := (@exp _ a i) : dioid_scope.
Notation "a ^*" := (@op_kleene _ a) (at level 20) : dioid_scope.
Notation "a ^+" := (@op_plus _ a) (at level 20) : dioid_scope.
Notation "a / b" := (div a b) : dioid_scope.

Section KleeneStar.
Variable (D : completeDioidType).

Lemma exp0 (a : D) : a ^ 0 = 1.
Proof. by rewrite /=. Qed.

Lemma expS i (a : D) : a ^ (i.+1) = a * (a ^ i).
Proof. by case i => //; rewrite exp0 muld1. Qed.

Lemma expSr i (a : D) : a ^ (i.+1) = (a ^ i) * a.
Proof.
elim: i => [|i Hi].
{ by rewrite exp0 mul1d. }
by rewrite expS {1}Hi expS muldA.
Qed.

Lemma kleeneSr (a : D) : a^* = 1 + a^+.
Proof.
rewrite -(exp0 a) -set_add_rem /op_kleene.
apply set_add_eq => x; split.
{ by move=> [] [?|i ?]; [left|right; exists i.+1].
}
by move=> [?|[i [_ ?]]]; [exists 0%nat|exists i].
Qed.

Lemma plusSr (a : D) : a ^+ = a * a ^*.
Proof.
rewrite /op_kleene set_addDl /op_plus. apply set_add_eq => d.
split.
{ move=> [[|i] [Hi Hi']]; [by case Hi|].
  exists (exp a i).
  by split; [exists i| rewrite Hi' expS].
}
move => [x [[i Hi] H]].
exists i.+1.
split => //.
by rewrite H expS Hi.
Qed.

Lemma plus_le_kleene (a : D) : a^+ <= a^*.
Proof. by apply /eqP; rewrite kleeneSr adddA adddC adddA adddd adddC. Qed.

Lemma le_plus (a : D) : a <= a ^+.
Proof. by apply /eqP; rewrite plusSr kleeneSr muldDr muld1 adddA adddd. Qed.

Lemma le_kleene (a : D) : a <= a^*.
Proof. apply (led_trans (le_plus a)), plus_le_kleene. Qed.

Lemma kleene_mul_expl (a : D) n : a ^ n * a ^* <= a^*.
Proof.
elim: n => [|n IHn]; [by rewrite mul1d; apply led_reflexive|].
rewrite expSr -muldA.
move: IHn; apply led_trans, led_mul2l.
rewrite -plusSr; apply plus_le_kleene.
Qed.

Lemma kleene_le (a b: D) : a <= b -> a ^* <= b ^*.
Proof.
move => Ha.
rewrite /op_kleene.
apply set_add_led_set => k.
have Hyp : forall i, a ^ i <= b ^i.
{ move=> i; elim: i => [| i Hni].
  { rewrite !exp0 /le; apply/eqP; apply adddd. }
  rewrite !expS.
  by apply led_mul.
}
elim: k => [|k IHk].
{ by rewrite !set_add_0 /led /= adddd. }
by rewrite !set_add_S; apply led_add.
Qed.

Lemma kleene_1r (a : D) : (a + 1) ^* = a ^*.
Proof.
rewrite /op_kleene /=.
have Hyp : forall i, (a + (e D)) ^i
                     = set_add (fun x => exists j, (j <= i)%nat /\ x = a ^j).
{ move=> i;elim: i => [ |i iHk].
  { by rewrite set_add_0 /=. }
  rewrite expS muldDl mul1d !iHk /= set_addDl.
  rewrite (set_add_eq _ (B':= fun y => y = a^i.+1 \/
                                (exists j, (1<=j<=i)%nat /\ y = a ^j) ));last first.
  {  move => x; split.
    { move=> [x0 [[j [Hj ->]]]] ->.
      move:Hj.
      rewrite leq_eqVlt => /orP [/eqP ->|Hi]; [by left; rewrite expS|].
      right; exists j.+1.
      by split; [| rewrite expS].
    }
    move => [-> | [j [Hj ->]] ].
    { by exists (a^i) ; split; [exists i| rewrite expS]. }
    move: Hj; case: j => [//| j Hj].
    exists (a^j) ; split ; [exists j| by rewrite expS]; split => //.
    move: Hj; apply leqW.
  }
  rewrite set_add_rem.
  set s := a ^ _ + _.
  rewrite (set_add_eq _ (B':= fun y => y = a^0 \/
                                       (exists j, (1<= j <= i)%nat /\ y = a^j)));
  last first; [|rewrite {}/s].
  { move=> x; split.
    { move => [[|j] [Hj ->]]; [by left|].
      by right; exists j.+1.
    }
    by move=>[-> | [j [Hj ->]]]; [exists O | exists j; move:Hj => /andP []].
  }
  rewrite set_add_rem.
  rewrite (adddC (a^0)) adddA -(adddA (a ^i.+1)) adddd adddC -!set_add_rem.
  apply set_add_eq => x.
  split.
  { move => [-> | [-> | [j [Hj ->]]]].
    { by exists O. }
    { by exists i.+1. }
    by exists j; move:Hj => /andP [] _ /leqW.
  }
  move=> [j [Hj ->]].
  move: j Hj => [|j] Hj.
  { by left. }
  right; move:Hj.
  rewrite leq_eqVlt => /orP [/eqP ->|Hj] ; [by left|].
    by right; exists j.+1.
}
apply set_add_eq_set => k.
elim: k => [|k IHk].
{ by rewrite !set_add_0 exp0. }
by rewrite set_add_S Hyp IHk set_add_S adddA adddd.
Qed.

Lemma kleene_sqr (a : D) : a^* * a^* = a^*.
Proof.
rewrite {1}/op_kleene set_addDr.
rewrite (set_add_eq _ (B':= fun y => y = a^* \/
                                     exists i, y = a^i.+1 * a^*)); last first.
{ move=>x; split.
  { by move=> [y [[[|i] ->] ->]]; [left; rewrite mul1d |right; exists i]. }
  move=> [-> |[i ->] ].
  { exists (e D).
    by split; [exists O| rewrite mul1d].
    }
  exists (a ^i.+1).
  by split; [exists i.+1| ].
}
rewrite set_add_rem.
rewrite adddC.
apply /eqP.
apply set_add_lim_nat => k.
elim: k => [|k ].
{ rewrite set_add_0 /= -plusSr.
  apply /eqP.
  by rewrite  kleeneSr adddC -adddA adddd.
}
rewrite set_add_S.
move /eqP => IHk; apply /eqP.
rewrite -adddA (adddC (_ * _)) adddA {}IHk.
rewrite adddC; apply /eqP /kleene_mul_expl.
Qed.

Lemma kleene_exp (a : D) i : (1<=i)%nat -> ( a^* )^i = a^*.
Proof.
case: i => [//|] i _; elim: i => [//|i IHi].
by rewrite expS IHi kleene_sqr.
Qed.

Lemma kleene_kleene (a : D) : (a^*)^* = a^*.
Proof.
rewrite kleeneSr.
rewrite /op_plus.
rewrite (set_add_eq _ (B':= fun y => y = a ^* \/ False)); last first.
{ move=> x; split.
  { move=> [i [Hi ->]].
    by left; apply kleene_exp. }
    by move=> [-> | //]; exists 1%N.
}
by rewrite set_add_rem set_add_empty addd0 kleeneSr adddA adddd.
Qed.

Theorem kleene_star (a b : D): (a^* * b = a * (a^* * b) + b) /\
                               (forall x, (x = a*x + b) -> a^* * b <= x).                 
Proof.
split.
{ by rewrite muldA -plusSr -{3}(mul1d b) -muldDl kleeneSr adddC. }
move=> x Hx.
rewrite /op_kleene set_addDr.
rewrite (set_add_eq _ (B':= fun y => exists i, y = (a ^ i) * b)); last first.
{ move=> y'; split.
  { by move=> [y [[i ->] ->]]; exists i. }
  by move=> [i ->]; exists (a^i); split; [exists i| ].
}
apply set_add_lim_nat => k.
elim: k => [ |k IHk].
{ by apply /eqP; rewrite set_add_0 mul1d Hx adddA adddC adddA adddd adddC. }
rewrite set_add_S led_add_eqv.
split; [apply IHk|].
move:k.+1=>i; elim: i => [|i IHi].
{ rewrite mul1d Hx.
   apply led_addl.
}
rewrite expS.
have Ha : a * x <= x; [by rewrite {2}Hx; apply led_addr|].
apply: (led_trans _ Ha); rewrite -muldA.
by apply led_mul2l.
Qed.

End KleeneStar.

Section ResiduationTheory.

Variable D : completeDioidType.

Lemma div_mul_le (x a : D) : (x / a) * a <= x.
Proof. by rewrite /div set_addDr; apply set_add_lim => y [z [Hz -> ]]. Qed.

Lemma mul_div_le (x a : D): x <= (x * a) / a.
Proof. by rewrite /div; apply led_set_add, led_reflexive. Qed.

Lemma mul_div_equiv (a b x : D) : x * a <= b <-> x <= b / a.
Proof.
split.
{ by move=> H; rewrite /div; apply led_set_add. }
move=>H.
move:(div_mul_le b a); apply led_trans.
by apply led_mul2r.
Qed.

Lemma div_top x : top D / x = top D.
Proof.
apply /led_antisym /andP; split; [|rewrite -mul_div_equiv]; apply led_top.
Qed.

Lemma led_divl (a b c : D) : a <= b -> a / c <= b / c.
Proof. rewrite -mul_div_equiv; apply /led_trans /div_mul_le. Qed.

Lemma led_divr (a b c : D) : a <= b -> c / b <= c / a.
Proof.
move=> Hab; rewrite -mul_div_equiv.
apply /(led_trans (led_mul2l  _ Hab)) /div_mul_le.
Qed.

Lemma addd_div_le (a b c : D) : a / c + b / c <= (a + b) / c.
Proof.
rewrite led_add_eqv.
by split; apply led_divl; [apply led_addr|apply led_addl].
Qed.

Lemma div_mul (a b c : D) : a / (b * c) = a / c / b.
Proof.
apply /led_antisym /andP; split.
{ by rewrite -!mul_div_equiv -muldA; apply div_mul_le. }
by rewrite -mul_div_equiv muldA !mul_div_equiv; apply led_reflexive.
Qed.

Lemma mul_divA (a b c : D ) : a * (b / c) <= (a * b) / c.
Proof. rewrite -mul_div_equiv -muldA; apply /led_mul2l /div_mul_le. Qed.

Lemma kleene_div_equiv (a: D) : a = a^* <-> a = div a a.
Proof.
split.
{ move=> ->.
  apply /led_antisym /andP; split.
  { apply set_add_lim => _ [i ->].
    rewrite -mul_div_equiv.
    apply kleene_mul_expl. }
  apply set_add_lim => x.
  rewrite {1}kleeneSr muldDr muld1.
  by rewrite led_add_eqv; move=> [? _].
}
move=>Ha; apply /led_antisym /andP.
split; [apply le_kleene|].
apply set_add_lim => _ [i ->].
elim:i => [|i IHi]; [by rewrite exp0 Ha -mul_div_equiv mul1d led_reflexive|].
by rewrite expSr mul_div_equiv -Ha.
Qed.

Lemma mul_kleene (a b : D) : a * b^* = (a * b^*) / b^*.
Proof.
apply /led_antisym /andP.
split.
{ by rewrite -mul_div_equiv -muldA kleene_sqr led_reflexive. }
apply set_add_lim => x.
apply led_trans.
by rewrite kleeneSr muldDr muld1 led_addr.
Qed.

Lemma div_kleene (a b : D) : a / b^* = (a / b^*) * b^*.
Proof.
apply /led_antisym /andP.
split.
{ apply set_add_lim => x.
  rewrite mul_div_equiv => Hx.
  apply (led_trans Hx).
  by rewrite kleeneSr muldDr muld1 led_addr.
}
by rewrite -mul_div_equiv -muldA kleene_sqr div_mul_le.
Qed.

End ResiduationTheory.

Section ComResiduationTheory.

Variable C : comCompleteDioidType.

Lemma divAC : right_commutative (@div C).
Proof.
move=> a b c. apply /led_antisym /andP. split.
{ by rewrite -!mul_div_equiv -muldA (muldC b) muldA !mul_div_equiv led_reflexive. }
by rewrite -!mul_div_equiv -muldA (muldC c) muldA !mul_div_equiv led_reflexive.
Qed.

Lemma kleene_add_mul (a b : C) : (a + b)^* = a^* * b ^*.
Proof.
apply /led_antisym /andP; split.
{ apply set_add_lim => _ [i ->].
  elim: i => [|i IHi].
  { rewrite exp0 -(muld1 1).
    apply led_mul.
    { rewrite kleeneSr -{1}(addd0 1).
      by apply led_add2l; apply /eqP; rewrite add0d.
    }
    rewrite kleeneSr -{1}(addd0 1).
    by apply led_add2l; apply /eqP; rewrite add0d.
  }
  rewrite expS.
  apply (led_trans (led_mul2l _ IHi)).
  rewrite muldDl muldA -plusSr (muldC b) -muldA -(muldC b) -plusSr.
  rewrite !kleeneSr !muldDl !muldDr !muld1 !mul1d.
  rewrite !adddA (adddC (a^+)) adddC !adddA adddd.
  rewrite [X in _ <= X]adddC -!adddA (adddC 1) (adddC (a^+)) !adddA.
  apply led_addr.
}
rewrite {2}/op_kleene /set_add set_addDl.
apply set_add_is_lub => _ [_ [[i -> ->]]].
rewrite {1}/op_kleene /set_add set_addDr.
apply set_add_is_lub => _ [_ [[j -> ->]]].
elim : i => [|i HIi].
{ rewrite exp0 muld1.
  elim : j => [|j HIj].
  { by rewrite exp0 kleeneSr led_addr . }
  rewrite expS kleeneSr plusSr -(add0d (_ *_)).
  apply led_add; [apply led_0_1|].
  apply led_mul => //.
  apply led_addr.
}
rewrite expS (muldC b) muldA.
apply (led_trans (led_mul2r _ HIi)).
rewrite muldC {2}kleeneSr plusSr -(add0d (_*_)).
apply led_add; [by apply led_0_1|].
apply led_mul2r, led_addl.
Qed.

End ComResiduationTheory.

(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrfun ssrbool eqtype ssrnat seq div choice fintype.
From mathcomp
Require Import bigop ssralg finset fingroup zmodp.
From mathcomp
Require Import poly ssrnum.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.

Reserved Notation "p <% q" (at level 70, no associativity).
Reserved Notation "p <=% q" (at level 70, no associativity).

(* Set Printing Width 30. *)

Module ord.

Section Formulas.

Variable T : Type.

Inductive formula : Type :=
| Bool of bool
| Equal of (term T) & (term T)
| Lt of (term T) & (term T)
| Le of (term T) & (term T)
| Unit of (term T)
| And of formula & formula
| Or of formula & formula
| Implies of formula & formula
| Not of formula
| Exists of nat & formula
| Forall of nat & formula.

End Formulas.

Fixpoint term_eq (T : eqType)(t1 t2 : term T) :=
  match t1, t2 with
    | Var n1, Var n2 => n1 == n2
    | Const r1, Const r2 => r1 == r2
    | NatConst n1, NatConst n2 => n1 == n2
    | Add r1 s1, Add r2 s2 => (term_eq r1 r2) && (term_eq s1 s2)
    | Opp r1, Opp r2 => term_eq r1 r2
    | NatMul r1 n1, NatMul r2 n2 => (term_eq r1 r2) && (n1 == n2)
    | Mul r1 s1, Mul r2 s2 => (term_eq r1 r2) && (term_eq s1 s2)
    | Inv r1, Inv r2 => term_eq r1 r2
    | Exp r1 n1, Exp r2 n2 => (term_eq r1 r2) && (n1 == n2)
    |_, _ => false
  end.

Lemma term_eqP (T : eqType) : Equality.axiom (@term_eq T).
Proof.
move=> t1 t2; apply: (iffP idP) => [|<-]; last first.
  by elim: t1 {t2} => //= t -> // n; rewrite eqxx.
elim: t1 t2.
- by move=> n1 /= [] // n2 /eqP ->.
- by move=> r1 /= [] // r2 /eqP ->.
- by move=> n1 /= [] // n2 /eqP ->.
- by move=> r1 hr1 r2 hr2 [] //= s1 s2 /andP [] /hr1 -> /hr2 ->.
- by move=> r1 hr1 [] //= s1 /hr1 ->.
- by move=> s1 hs1 n1 [] //= s2 n2 /andP [] /hs1 -> /eqP ->.
- by move=> r1 hr1 r2 hr2 [] //= s1 s2 /andP [] /hr1 -> /hr2 ->.
- by move=> r1 hr1 [] //= s1 /hr1 ->.
- by move=> s1 hs1 n1 [] //= s2 n2 /andP [] /hs1 -> /eqP ->.
Qed.

Canonical term_eqMixin (T : eqType) := EqMixin (@term_eqP T).
Canonical term_eqType (T : eqType) :=
   Eval hnf in EqType (term T) (@term_eqMixin T).

Arguments term_eqP T [x y].
Prenex Implicits term_eq.


Bind Scope oterm_scope with term.
Bind Scope oterm_scope with formula.
Delimit Scope oterm_scope with oT.
Arguments Add _ _%oT _%oT.
Arguments Opp _ _%oT.
Arguments NatMul _ _%oT _%N.
Arguments Mul _ _%oT _%oT.
Arguments Mul _ _%oT _%oT.
Arguments Inv _ _%oT.
Arguments Exp _ _%oT _%N.
Arguments Equal _ _%oT _%oT.
Arguments Unit _ _%oT.
Arguments And _ _%oT _%oT.
Arguments Or _ _%oT _%oT.
Arguments Implies _ _%oT _%oT.
Arguments Not _ _%oT.
Arguments Exists _ _%N _%oT.
Arguments Forall _ _%N _%oT.

Arguments Bool [T].
Prenex Implicits Const Add Opp NatMul Mul Exp Bool Unit And Or Implies Not.
Prenex Implicits Exists Forall Lt.

Notation True := (Bool true).
Notation False := (Bool false).

Notation "''X_' i" := (Var _ i) : oterm_scope.
Notation "n %:R" := (NatConst _ n) : oterm_scope.
Notation "x %:T" := (Const x) : oterm_scope.
Notation "0" := 0%:R%oT : oterm_scope.
Notation "1" := 1%:R%oT : oterm_scope.
Infix "+" := Add : oterm_scope.
Notation "- t" := (Opp t) : oterm_scope.
Notation "t - u" := (Add t (- u)) : oterm_scope.
Infix "*" := Mul : oterm_scope.
Infix "*+" := NatMul : oterm_scope.
Notation "t ^-1" := (Inv t) : oterm_scope.
Notation "t / u" := (Mul t u^-1) : oterm_scope.
Infix "^+" := Exp : oterm_scope.
Notation "t ^- n" := (t^-1 ^+ n)%oT : oterm_scope.
Infix "==" := Equal : oterm_scope.
Infix "<%" := Lt : oterm_scope.
Infix "<=%" := Le : oterm_scope.
Infix "/\" := And : oterm_scope.
Infix "\/" := Or : oterm_scope.
Infix "==>" := Implies : oterm_scope.
Notation "~ f" := (Not f) : oterm_scope.
Notation "x != y" := (Not (x == y)) : oterm_scope.
Notation "''exists' ''X_' i , f" := (Exists i f) : oterm_scope.
Notation "''forall' ''X_' i , f" := (Forall i f) : oterm_scope.

Section Substitution.

Variable T : Type.


Fixpoint fsubst (f : formula T) (s : nat * term T) :=
  match f with
  | Bool _ => f
  | (t1 == t2) => (tsubst t1 s == tsubst t2 s)
  | (t1 <% t2) => (tsubst t1 s <% tsubst t2 s)
  | (t1 <=% t2) => (tsubst t1 s <=% tsubst t2 s)
  | (Unit t1) => Unit (tsubst t1 s)
  | (f1 /\ f2) => (fsubst f1 s /\ fsubst f2 s)
  | (f1 \/ f2) => (fsubst f1 s \/ fsubst f2 s)
  | (f1 ==> f2) => (fsubst f1 s ==> fsubst f2 s)
  | (~ f1) => (~ fsubst f1 s)
  | ('exists 'X_i, f1) => ('exists 'X_i, if i == s.1 then f1 else fsubst f1 s)
  | ('forall 'X_i, f1) => ('forall 'X_i, if i == s.1 then f1 else fsubst f1 s)
  end%oT.

End Substitution.

Section OrderedClause.

Inductive oclause (R : Type) : Type :=
  Oclause : seq (term R) -> seq (term R) -> seq (term R) -> seq (term R) -> oclause R.

Definition eq_of_oclause (R : Type)(x : oclause R) :=
  let: Oclause y _ _ _  := x in y.
Definition neq_of_oclause (R : Type)(x : oclause R) :=
  let: Oclause _ y _ _  := x in y.
Definition lt_of_oclause (R : Type) (x : oclause R) :=
  let: Oclause  _ _ y _  := x in y.
Definition le_of_oclause (R : Type) (x : oclause R) :=
  let: Oclause  _ _ _ y := x in y.

End OrderedClause.

Delimit Scope oclause_scope with OCLAUSE.
Open Scope oclause_scope.

Notation "p .1" := (@eq_of_oclause _ p)
  (at level 2, left associativity, format "p .1") : oclause_scope.
Notation "p .2" := (@neq_of_oclause _ p)
  (at level 2, left associativity, format "p .2") : oclause_scope.

Notation "p .3" := (@lt_of_oclause _ p)
  (at level 2, left associativity, format "p .3") : oclause_scope.
Notation "p .4" := (@le_of_oclause _ p)
  (at level 2, left associativity, format "p .4") : oclause_scope.

Definition oclause_eq (T : eqType)(t1 t2 : oclause T) :=
  let: Oclause eq_l1 neq_l1 lt_l1 leq_l1 := t1 in
  let: Oclause eq_l2 neq_l2 lt_l2 leq_l2 := t2 in
    [&& eq_l1 == eq_l2, neq_l1 == neq_l2, lt_l1 == lt_l2 & leq_l1 == leq_l2].

Lemma oclause_eqP (T : eqType) : Equality.axiom (@oclause_eq T).
Proof.
move=> t1 t2; apply: (iffP idP) => [|<-] /=; last first.
  by rewrite /oclause_eq; case: t1=> l1 l2 l3 l4; rewrite !eqxx.
case: t1 => [l1 l2 l3 l4]; case: t2 => m1 m2 m3 m4 /=; case/and4P.
by move/eqP=> -> /eqP -> /eqP -> /eqP ->.
Qed.

Canonical oclause_eqMixin (T : eqType) := EqMixin (@oclause_eqP T).
Canonical oclause_eqType (T : eqType) :=
   Eval hnf in EqType (oclause T) (@oclause_eqMixin T).

Arguments oclause_eqP T [x y].
Prenex Implicits oclause_eq.

Section EvalTerm.

Variable R : realDomainType.

(* Evaluation of a reified formula *)

Fixpoint holds (e : seq R) (f : ord.formula R) {struct f} : Prop :=
  match f with
  | Bool b => b
  | (t1 == t2)%oT => eval e t1 = eval e t2
  | (t1 <% t2)%oT => eval e t1 < eval e t2
  | (t1 <=% t2)%oT => eval e t1 <= eval e t2
  | Unit t1 => eval e t1 \in unit
  | (f1 /\ f2)%oT => holds e f1 /\ holds e f2
  | (f1 \/ f2)%oT => holds e f1 \/ holds e f2
  | (f1 ==> f2)%oT => holds e f1 -> holds e f2
  | (~ f1)%oT => ~ holds e f1
  | ('exists 'X_i, f1)%oT => exists x, holds (set_nth 0 e i x) f1
  | ('forall 'X_i, f1)%oT => forall x, holds (set_nth 0 e i x) f1
  end.


(* Extensionality of formula evaluation *)
Lemma eq_holds e e' f : same_env e e' -> holds e f -> holds e' f.
Proof.
pose sv := set_nth (0 : R).
have eq_i i v e1 e2: same_env e1 e2 -> same_env (sv e1 i v) (sv e2 i v).
  by move=> eq_e j; rewrite !nth_set_nth /= eq_e.
elim: f e e' => //=.
- by move=> t1 t2 e e' eq_e; rewrite !(eq_eval _ eq_e).
- by move=> t1 t2 e e' eq_e; rewrite !(eq_eval _ eq_e).
- by move=> t1 t2 e e' eq_e; rewrite !(eq_eval _ eq_e).
- by move=> t e e' eq_e; rewrite (eq_eval _ eq_e).
- by move=> f1 IH1 f2 IH2 e e' eq_e; move/IH2: (eq_e); move/IH1: eq_e; tauto.
- by move=> f1 IH1 f2 IH2 e e' eq_e; move/IH2: (eq_e); move/IH1: eq_e; tauto.
- by move=> f1 IH1 f2 IH2 e e' eq_e f12; move/IH1: (same_env_sym eq_e); eauto.
- by move=> f1 IH1 e e'; move/same_env_sym; move/IH1; tauto.
- by move=> i f1 IH1 e e'; move/(eq_i i)=> eq_e [x f_ex]; exists x; eauto.
by move=> i f1 IH1 e e'; move/(eq_i i); eauto.
Qed.

(* Evaluation and substitution by a constant *)
Lemma holds_fsubst e f i v :
  holds e (fsubst f (i, v%:T)%T) <-> holds (set_nth 0 e i v) f.
Proof.
elim: f e => //=; do [
  by move=> *; rewrite !eval_tsubst
| move=> f1 IHf1 f2 IHf2 e; move: (IHf1 e) (IHf2 e); tauto
| move=> f IHf e; move: (IHf e); tauto
| move=> j f IHf e].
- case eq_ji: (j == i); first rewrite (eqP eq_ji).
    by split=> [] [x f_x]; exists x; rewrite set_set_nth eqxx in f_x *.
  split=> [] [x f_x]; exists x; move: f_x; rewrite set_set_nth eq_sym eq_ji;
     have:= IHf (set_nth 0 e j x); tauto.
case eq_ji: (j == i); first rewrite (eqP eq_ji).
  by split=> [] f_ x; move: (f_ x); rewrite set_set_nth eqxx.
split=> [] f_ x; move: (IHf (set_nth 0 e j x)) (f_ x);
  by rewrite set_set_nth eq_sym eq_ji; tauto.
Qed.

(* Boolean test selecting formulas in the theory of rings *)
Fixpoint rformula (f : formula R) :=
  match f with
  | Bool _ => true
  | t1 == t2 => rterm t1 && rterm t2
  | t1 <% t2 => rterm t1 && rterm t2
  | t1 <=% t2 => rterm t1 && rterm t2
  | Unit t1 => false
  | (f1 /\ f2) | (f1 \/ f2) | (f1 ==> f2) => rformula f1 && rformula f2
  | (~ f1) | ('exists 'X__, f1) | ('forall 'X__, f1) => rformula f1
  end%oT.

(* An oformula stating that t1 is equal to 0 in the ring theory. *)
Definition eq0_rform t1 :=
  let m := @ub_var R t1 in
  let: (t1', r1) := to_rterm t1 [::] m in
  let fix loop r i := match r with
  | [::] => t1' == 0
  | t :: r' =>
    let f := ('X_i * t == 1 /\ t * 'X_i == 1) in
     'forall 'X_i, (f \/ 'X_i == t /\ ~ ('exists 'X_i,  f)) ==> loop r' i.+1
  end%oT
  in loop r1 m.

(* An oformula stating that t1 is less than 0 in the equational ring theory.
Definition leq0_rform t1 :=
  let m := @ub_var R t1 in
  let: (t1', r1) := to_rterm t1 [::] m in
  let fix loop r i := match r with
  | [::] => 'exists 'X_m.+1, t1' == 'X_m.+1 * 'X_m.+1
  | t :: r' =>
    let f := ('X_i * t == 1 /\ t * 'X_i == 1) in
     'forall 'X_i, (f \/ 'X_i == t /\ ~ ('exists 'X_i,  f)) ==> loop r' i.+1
  end%oT
  in loop r1 m.
*)
Definition leq0_rform t1 :=
  let m := @ub_var R t1 in
  let: (t1', r1) := to_rterm t1 [::] m in
  let fix loop r i := match r with
  | [::] => t1' <=% 0
  | t :: r' =>
    let f := ('X_i * t == 1 /\ t * 'X_i == 1) in
     'forall 'X_i, (f \/ 'X_i == t /\ ~ ('exists 'X_i,  f)) ==> loop r' i.+1
  end%oT
  in loop r1 m.


(* Definition lt0_rform t1 := *)
(*   let m := @ub_var R t1 in *)
(*   let: (t1', r1) := to_rterm t1 [::] m in *)
(*   let fix loop r i := match r with *)
(*   | [::] => 'exists 'X_m.+1, (t1' == 'X_m.+1 * 'X_m.+1 /\ ~ ('X_m.+1 == 0)) *)
(*   | t :: r' => *)
(*     let f := ('X_i * t == 1 /\ t * 'X_i == 1) in *)
(*      'forall 'X_i, (f \/ 'X_i == t /\ ~ ('exists 'X_i,  f)) ==> loop r' i.+1 *)
(*   end%oT *)
(*   in loop r1 m. *)

Definition lt0_rform t1 :=
  let m := @ub_var R t1 in
  let: (t1', r1) := to_rterm t1 [::] m in
  let fix loop r i := match r with
  | [::] => t1' <% 0
  | t :: r' =>
    let f := ('X_i * t == 1 /\ t * 'X_i == 1) in
     'forall 'X_i, (f \/ 'X_i == t /\ ~ ('exists 'X_i,  f)) ==> loop r' i.+1
  end%oT
  in loop r1 m.

(* Transformation of a formula in the theory of rings with units into an *)

(* equivalent formula in the sub-theory of rings.                        *)
Fixpoint to_rform f :=
  match f with
  | Bool b => f
  | t1 == t2 => eq0_rform (t1 - t2)
  | t1 <% t2 => lt0_rform (t1 - t2)
  | t1 <=% t2 => leq0_rform (t1 - t2)
  | Unit t1 => eq0_rform (t1 * t1^-1 - 1)
  | f1 /\ f2 => to_rform f1 /\ to_rform f2
  | f1 \/ f2 =>  to_rform f1 \/ to_rform f2
  | f1 ==> f2 => to_rform f1 ==> to_rform f2
  | ~ f1 => ~ to_rform f1
  | ('exists 'X_i, f1) => 'exists 'X_i, to_rform f1
  | ('forall 'X_i, f1) => 'forall 'X_i, to_rform f1
  end%oT.

(* The transformation gives a ring formula. *)
(* the last part of the proof consists in 3 cases that are exactly the same.
   how to factorize ? *)
Lemma to_rform_rformula f : rformula (to_rform f).
Proof.
suffices [h1 h2 h3]:
  [/\ forall t1, rformula (eq0_rform t1),
      forall t1, rformula (lt0_rform t1) &
      forall t1, rformula (leq0_rform t1)].
  by elim: f => //= => f1 ->.
split=> t1.
- rewrite /eq0_rform; move: (ub_var t1) => m.
  set tr := _ m.
  suffices: all (@rterm R) (tr.1 :: tr.2)%PAIR.
    case: tr => {t1} t1 r /= /andP[t1_r].
    by elim: r m => [|t r IHr] m; rewrite /= ?andbT // => /andP[->]; apply: IHr.
  have: all (@rterm R) [::] by [].
  rewrite {}/tr; elim: t1 [::] => //=.
  + move=> t1 IHt1 t2 IHt2 r.
  move/IHt1; case: to_rterm => {t1 r IHt1} t1 r /= /andP[t1_r].
  move/IHt2; case: to_rterm => {t2 r IHt2} t2 r /= /andP[t2_r].
  by rewrite t1_r t2_r.
  + by move=> t1 IHt1 r /IHt1; case: to_rterm.
  + by move=> t1 IHt1 n r /IHt1; case: to_rterm.
  + move=> t1 IHt1 t2 IHt2 r.
  move/IHt1; case: to_rterm => {t1 r IHt1} t1 r /= /andP[t1_r].
  move/IHt2; case: to_rterm => {t2 r IHt2} t2 r /= /andP[t2_r].
  by rewrite t1_r t2_r.
  + move=> t1 IHt1 r.
  by move/IHt1; case: to_rterm => {t1 r IHt1} t1 r /=; rewrite all_rcons.
  + by move=> t1 IHt1 n r /IHt1; case: to_rterm.
- rewrite /lt0_rform; move: (ub_var t1) => m; set tr := _ m.
  suffices: all (@rterm R) (tr.1 :: tr.2)%PAIR.
    case: tr => {t1} t1 r /= /andP[t1_r].
    by elim: r m => [|t r IHr] m; rewrite /= ?andbT // => /andP[->]; apply: IHr.
  have: all (@rterm R) [::] by [].
  rewrite {}/tr; elim: t1 [::] => //=.
  + move=> t1 IHt1 t2 IHt2 r.
  move/IHt1; case: to_rterm => {t1 r IHt1} t1 r /= /andP[t1_r].
  move/IHt2; case: to_rterm => {t2 r IHt2} t2 r /= /andP[t2_r].
  by rewrite t1_r t2_r.
  + by move=> t1 IHt1 r /IHt1; case: to_rterm.
  + by move=> t1 IHt1 n r /IHt1; case: to_rterm.
  + move=> t1 IHt1 t2 IHt2 r.
  move/IHt1; case: to_rterm => {t1 r IHt1} t1 r /= /andP[t1_r].
  move/IHt2; case: to_rterm => {t2 r IHt2} t2 r /= /andP[t2_r].
  by rewrite t1_r t2_r.
  + move=> t1 IHt1 r.
  by move/IHt1; case: to_rterm => {t1 r IHt1} t1 r /=; rewrite all_rcons.
  + by move=> t1 IHt1 n r /IHt1; case: to_rterm.
- rewrite /leq0_rform; move: (ub_var t1) => m; set tr := _ m.
  suffices: all (@rterm R) (tr.1 :: tr.2)%PAIR.
    case: tr => {t1} t1 r /= /andP[t1_r].
    by elim: r m => [|t r IHr] m; rewrite /= ?andbT // => /andP[->]; apply: IHr.
  have: all (@rterm R) [::] by [].
  rewrite {}/tr; elim: t1 [::] => //=.
  + move=> t1 IHt1 t2 IHt2 r.
  move/IHt1; case: to_rterm => {t1 r IHt1} t1 r /= /andP[t1_r].
  move/IHt2; case: to_rterm => {t2 r IHt2} t2 r /= /andP[t2_r].
  by rewrite t1_r t2_r.
  + by move=> t1 IHt1 r /IHt1; case: to_rterm.
  + by move=> t1 IHt1 n r /IHt1; case: to_rterm.
  + move=> t1 IHt1 t2 IHt2 r.
  move/IHt1; case: to_rterm => {t1 r IHt1} t1 r /= /andP[t1_r].
  move/IHt2; case: to_rterm => {t2 r IHt2} t2 r /= /andP[t2_r].
  by rewrite t1_r t2_r.
  + move=> t1 IHt1 r.
  by move/IHt1; case: to_rterm => {t1 r IHt1} t1 r /=; rewrite all_rcons.
  + by move=> t1 IHt1 n r /IHt1; case: to_rterm.
Qed.

Import Num.Theory.

(* Correctness of the transformation. *)
Lemma to_rformP e f : holds e (to_rform f) <-> holds e f.
Proof.
suffices{e f} [equal0_equiv lt0_equiv le0_equiv]:
  [/\ forall e t1 t2, holds e (eq0_rform (t1 - t2)) <-> (eval e t1 == eval e t2),
    forall e t1 t2, holds e (lt0_rform (t1 - t2)) <-> (eval e t1 < eval e t2) &
      forall e t1 t2, holds e (leq0_rform (t1 - t2)) <-> (eval e t1 <= eval e t2)].
- elim: f e => /=; try tauto.
  + move=> t1 t2 e.
    by split; [move/equal0_equiv/eqP | move/eqP/equal0_equiv].
  + by move=> t1 t2 e; split; move/lt0_equiv.
  + by move=> t1 t2 e; split; move/le0_equiv.
  + by move=> t1 e; rewrite unitrE; apply: equal0_equiv.
  + by move=> f1 IHf1 f2 IHf2 e; move: (IHf1 e) (IHf2 e); tauto.
  + by move=> f1 IHf1 f2 IHf2 e; move: (IHf1 e) (IHf2 e); tauto.
  + by move=> f1 IHf1 f2 IHf2 e; move: (IHf1 e) (IHf2 e); tauto.
  + by move=> f1 IHf1 e; move: (IHf1 e); tauto.
  + by move=> n f1 IHf1 e; split=> [] [x] /IHf1; exists x.
  + by move=> n f1 IHf1 e; split=> Hx x; apply/IHf1.
suffices h e t1 t2 :
  [/\ holds e (eq0_rform (t1 - t2)) <-> (eval e t1 == eval e t2),
    holds e (lt0_rform (t1 - t2)) <-> (eval e t1 < eval e t2) &
    holds e (leq0_rform (t1 - t2)) <-> (eval e t1 <= eval e t2)].
  by split => e t1 t2; case: (h e t1 t2).
rewrite -{1}(add0r (eval e t2)) -(can2_eq (subrK _) (addrK _)).
rewrite -subr_lt0 -subr_le0 -/(eval e (t1 - t2)); move: {t1 t2}(t1 - t2)%T => t.
have sub_var_tsubst s t0: (s.1%PAIR >= ub_var t0)%N -> tsubst t0 s = t0.
  elim: t0 {t} => //=.
  - by move=> n; case: ltngtP.
  - by move=> t1 IHt1 t2 IHt2; rewrite geq_max => /andP[/IHt1-> /IHt2->].
  - by move=> t1 IHt1 /IHt1->.
  - by move=> t1 IHt1 n /IHt1->.
  - by move=> t1 IHt1 t2 IHt2; rewrite geq_max => /andP[/IHt1-> /IHt2->].
  - by move=> t1 IHt1 /IHt1->.
  - by move=> t1 IHt1 n /IHt1->.
pose fix rsub t' m r : term R :=
  if r is u :: r' then tsubst (rsub t' m.+1 r') (m, u^-1)%T else t'.
pose fix ub_sub m r : Prop :=
  if r is u :: r' then (ub_var u <= m)%N /\ ub_sub m.+1 r' else true.
suffices{t} rsub_to_r t r0 m: (m >= ub_var t)%N -> ub_sub _ m r0 ->
  let: (t', r) := to_rterm t r0 m in
  [/\ take (size r0) r = r0,
      ub_var t' <= m + size r, ub_sub _ m r & rsub t' m r = t]%N.
- have:= rsub_to_r t [::] _ (leqnn _); rewrite /eq0_rform /lt0_rform /leq0_rform.
  case: (to_rterm _ _ _) => [t1' r1] /= [//| _ _ ub_r1 def_t].
  rewrite -{2 4 6}def_t {def_t}.
  elim: r1 (ub_var t) e ub_r1 => [|u r1 IHr1] m e /= => [_|[ub_u ub_r1]].
    by split => //; split=> /eqP.
  rewrite eval_tsubst /=; set y := eval e u; split; split => //= t_h0.
  + case: (IHr1 m.+1 (set_nth 0 e m y^-1) ub_r1) => h _ _; apply/h.
    apply: t_h0.
    rewrite nth_set_nth /= eqxx -(eval_tsubst e u (m, Const _)).
    rewrite sub_var_tsubst //= -/y.
    case Uy: (y \in unit); [left | right]; first by rewrite mulVr ?divrr.
    split=> [|[z]]; first by rewrite invr_out ?Uy.
    rewrite nth_set_nth /= eqxx.
    rewrite -!(eval_tsubst _ _ (m, Const _)) !sub_var_tsubst // -/y => yz1.
    by case/unitrP: Uy; exists z.
  + move=> x def_x.
    case: (IHr1 m.+1 (set_nth 0 e m x) ub_r1) => h _ _. apply/h.
    suff ->: x = y^-1 by []; move: def_x.
    rewrite nth_set_nth /= eqxx -(eval_tsubst e u (m, Const _)).
    rewrite sub_var_tsubst //= -/y; case=> [[xy1 yx1] | [xy nUy]].
      by rewrite -[y^-1]mul1r -[1]xy1 mulrK //; apply/unitrP; exists x.
    rewrite invr_out //; apply/unitrP=> [[z yz1]]; case: nUy; exists z.
    rewrite nth_set_nth /= eqxx -!(eval_tsubst _ _ (m, _%:T)%T).
    by rewrite !sub_var_tsubst.
  + case: (IHr1 m.+1 (set_nth 0 e m y^-1) ub_r1) =>  _ h _. apply/h.
    apply: t_h0.
    rewrite nth_set_nth /= eqxx -(eval_tsubst e u (m, Const _)).
    rewrite sub_var_tsubst //= -/y.
    case Uy: (y \in unit); [left | right]; first by rewrite mulVr ?divrr.
    split=> [|[z]]; first by rewrite invr_out ?Uy.
    rewrite nth_set_nth /= eqxx.
    rewrite -!(eval_tsubst _ _ (m, Const _)) !sub_var_tsubst // -/y => yz1.
    by case/unitrP: Uy; exists z.
  + move=> x def_x.
    case: (IHr1 m.+1 (set_nth 0 e m x) ub_r1) => _ h _. apply/h.
    suff ->: x = y^-1 by []; move: def_x.
    rewrite nth_set_nth /= eqxx -(eval_tsubst e u (m, Const _)).
    rewrite sub_var_tsubst //= -/y; case=> [[xy1 yx1] | [xy nUy]].
      by rewrite -[y^-1]mul1r -[1]xy1 mulrK //; apply/unitrP; exists x.
    rewrite invr_out //; apply/unitrP=> [[z yz1]]; case: nUy; exists z.
    rewrite nth_set_nth /= eqxx -!(eval_tsubst _ _ (m, _%:T)%T).
    by rewrite !sub_var_tsubst.
  + case: (IHr1 m.+1 (set_nth 0 e m y^-1) ub_r1) =>  _ _ h. apply/h.
    apply: t_h0.
    rewrite nth_set_nth /= eqxx -(eval_tsubst e u (m, Const _)).
    rewrite sub_var_tsubst //= -/y.
    case Uy: (y \in unit); [left | right]; first by rewrite mulVr ?divrr.
    split=> [|[z]]; first by rewrite invr_out ?Uy.
    rewrite nth_set_nth /= eqxx.
    rewrite -!(eval_tsubst _ _ (m, Const _)) !sub_var_tsubst // -/y => yz1.
    by case/unitrP: Uy; exists z.
  + move=> x def_x.
    case: (IHr1 m.+1 (set_nth 0 e m x) ub_r1) => _ _ h. apply/h.
    suff ->: x = y^-1 by []; move: def_x.
    rewrite nth_set_nth /= eqxx -(eval_tsubst e u (m, Const _)).
    rewrite sub_var_tsubst //= -/y; case=> [[xy1 yx1] | [xy nUy]].
      by rewrite -[y^-1]mul1r -[1]xy1 mulrK //; apply/unitrP; exists x.
    rewrite invr_out //; apply/unitrP=> [[z yz1]]; case: nUy; exists z.
    rewrite nth_set_nth /= eqxx -!(eval_tsubst _ _ (m, _%:T)%T).
    by rewrite !sub_var_tsubst.
have rsub_id r t0 n: (ub_var t0 <= n)%N -> rsub t0 n r = t0.
  by elim: r n => //= t1 r IHr n let0n; rewrite IHr ?sub_var_tsubst ?leqW.
have rsub_acc r s t1 m1:
  (ub_var t1 <= m1 + size r)%N -> rsub t1 m1 (r ++ s) = rsub t1 m1 r.
  elim: r t1 m1 => [|t1 r IHr] t2 m1 /=; first by rewrite addn0; apply: rsub_id.
  by move=> letmr; rewrite IHr ?addSnnS.
elim: t r0 m => /=; try do [
  by move=> n r m hlt hub; rewrite take_size (ltn_addr _ hlt) rsub_id
| by move=> n r m hlt hub; rewrite leq0n take_size rsub_id
| move=> t1 IHt1 t2 IHt2 r m; rewrite geq_max; case/andP=> hub1 hub2 hmr;
  case: to_rterm {IHt1 hub1 hmr}(IHt1 r m hub1 hmr) => t1' r1;
  case=> htake1 hub1' hsub1 <-;
  case: to_rterm {IHt2 hub2 hsub1}(IHt2 r1 m hub2 hsub1) => t2' r2 /=;
  rewrite geq_max; case=> htake2 -> hsub2 /= <-;
  rewrite -{1 2}(cat_take_drop (size r1) r2) htake2; set r3 := drop _ _;
  rewrite size_cat addnA (leq_trans _ (leq_addr _ _)) //;
  split=> {hsub2}//;
   first by [rewrite takel_cat // -htake1 size_take geq_minr];
  rewrite -(rsub_acc r1 r3 t1') {hub1'}// -{htake1}htake2 {r3}cat_take_drop;
  by elim: r2 m => //= u r2 IHr2 m; rewrite IHr2
| do [ move=> t1 IHt1 r m; do 2!move/IHt1=> {IHt1}IHt1
     | move=> t1 IHt1 n r m; do 2!move/IHt1=> {IHt1}IHt1];
  case: to_rterm IHt1 => t1' r1 [-> -> hsub1 <-]; split=> {hsub1}//;
  by elim: r1 m => //= u r1 IHr1 m; rewrite IHr1].
move=> t1 IH r m letm /IH {IH} /(_ letm) {letm}.
case: to_rterm => t1' r1 /= [def_r ub_t1' ub_r1 <-].
rewrite size_rcons addnS leqnn -{1}cats1 takel_cat ?def_r; last first.
  by rewrite -def_r size_take geq_minr.
elim: r1 m ub_r1 ub_t1' {def_r} => /= [|u r1 IHr1] m => [_|[->]].
  by rewrite addn0 eqxx.
by rewrite -addSnnS => /IHr1 IH /IH[_ _ ub_r1 ->].
Qed.

(* The above proof is ugly but is in fact copypaste *)

(* Boolean test selecting formulas which describe a constructible set, *)
(* i.e. formulas without quantifiers.                                  *)

(* The quantifier elimination check. *)
Fixpoint qf_form (f : formula R) :=
  match f with
  | Bool _ | _ == _ | Unit _ | Lt _ _ | Le _ _ => true
  | f1 /\ f2 | f1 \/ f2 | f1 ==> f2 => qf_form f1 && qf_form f2
  | ~ f1 => qf_form f1
  | _ => false
  end%oT.

(* Boolean holds predicate for quantifier free formulas *)
Definition qf_eval e := fix loop (f : formula R) : bool :=
  match f with
  | Bool b => b
  | t1 == t2 => (eval e t1 == eval e t2)%bool
  | t1 <% t2 => (eval e t1 < eval e t2)%bool
  | t1 <=% t2 => (eval e t1 <= eval e t2)%bool
  | Unit t1 => eval e t1 \in unit
  | f1 /\ f2 => loop f1 && loop f2
  | f1 \/ f2 => loop f1 || loop f2
  | f1 ==> f2 => (loop f1 ==> loop f2)%bool
  | ~ f1 => ~~ loop f1
  |_ => false
  end%oT.

(* qf_eval is equivalent to holds *)
Lemma qf_evalP e f : qf_form f -> reflect (holds e f) (qf_eval e f).
Proof.
elim: f => //=; try by move=> *; apply: idP.
- by move=> t1 t2 _; apply: eqP.
- move=> f1 IHf1 f2 IHf2 /= /andP[/IHf1[] f1T]; last by right; case.
  by case/IHf2; [left | right; case].
- move=> f1 IHf1 f2 IHf2 /= /andP[/IHf1[] f1F]; first by do 2 left.
  by case/IHf2; [left; right | right; case].
- move=> f1 IHf1 f2 IHf2 /= /andP[/IHf1[] f1T]; last by left.
  by case/IHf2; [left | right; move/(_ f1T)].
by move=> f1 IHf1 /IHf1[]; [right | left].
Qed.

(* Quantifier-free formula are normalized into DNF. A DNF is *)
(* represented by the type seq (seq (term R) * seq (term R)), where we *)
(* separate positive and negative literals *)


(* DNF preserving conjunction *)

Definition and_odnf (bcs1 bcs2 : seq (oclause R)) :=
  \big[cat/nil]_(bc1 <- bcs1)
     map (fun bc2 : oclause R =>
       (Oclause (bc1.1 ++ bc2.1) (bc1.2 ++ bc2.2) (bc1.3 ++ bc2.3) (bc1.4 ++ bc2.4)))%OCLAUSE bcs2.

(* Computes a DNF from a qf ring formula *)
Fixpoint qf_to_odnf (f : formula R) (neg : bool) {struct f} : seq (oclause R) :=
  match f with
  | Bool b => if b (+) neg then [:: (Oclause [::] [::] [::] [::])] else [::]
  | t1 == t2 =>
    [:: if neg then (Oclause [::] [:: t1 - t2] [::] [::]) else (Oclause [:: t1 - t2] [::] [::] [::])]
  | t1 <% t2 =>
    [:: if neg then (Oclause [::] [::] [::] [:: t1 - t2]) else (Oclause [::] [::] [:: t2 - t1] [::])]
  | t1 <=% t2 =>
    [:: if neg then (Oclause [::] [::] [:: t1 - t2] [::]) else (Oclause [::] [::] [::] [:: t2 - t1])]
  | f1 /\ f2 => (if neg then cat else and_odnf) [rec f1, neg] [rec f2, neg]
  | f1 \/ f2 => (if neg then and_odnf else cat) [rec f1, neg] [rec f2, neg]
  | f1 ==> f2 => (if neg then and_odnf else cat) [rec f1, ~~ neg] [rec f2, neg]
  | ~ f1 => [rec f1, ~~ neg]
  | _ =>  if neg then  [:: (Oclause [::] [::] [::] [::])] else [::]
  end%oT where "[ 'rec' f , neg ]" := (qf_to_odnf f neg).

(* Conversely, transforms a DNF into a formula *)
Definition odnf_to_oform :=
  let pos_lit t := And (t == 0)%oT in let neg_lit t := And (t != 0)%oT in
  let lt_lit t :=  And (0 <% t)%oT in let le_lit t := And (0 <=% t)%oT in
  let ocls (bc : oclause R) :=
    Or
    (foldr pos_lit True bc.1 /\ foldr neg_lit True bc.2 /\
     foldr lt_lit True bc.3 /\ foldr le_lit True bc.4) in
  foldr ocls False.

(* Catenation of dnf is the Or of formulas *)
Lemma cat_dnfP e bcs1 bcs2 :
  qf_eval e (odnf_to_oform (bcs1 ++ bcs2))
    = qf_eval e (odnf_to_oform bcs1 \/ odnf_to_oform bcs2).
Proof.
by elim: bcs1 => //= bc1 bcs1 IH1; rewrite -orbA; congr orb; rewrite IH1.
Qed.



(* and_dnf is the And of formulas *)
Lemma and_odnfP e bcs1 bcs2 :
  qf_eval e (odnf_to_oform (and_odnf bcs1 bcs2))
   = qf_eval e (odnf_to_oform bcs1 /\ odnf_to_oform bcs2).
Proof.
elim: bcs1 => [|bc1 bcs1 IH1] /=; first by rewrite /and_odnf big_nil.
rewrite /and_odnf big_cons -/(and_odnf bcs1 bcs2) cat_dnfP  /=.
rewrite {}IH1 /= andb_orl; congr orb.
elim: bcs2 bc1 {bcs1} => [|bc2 bcs2 IH] bc1 /=; first by rewrite andbF.
rewrite {}IH /= andb_orr; congr orb => {bcs2}.
suffices aux (l1 l2 : seq (term R)) g : let redg := foldr (And \o g) True in
  qf_eval e (redg (l1 ++ l2)) = qf_eval e (redg l1 /\ redg l2)%oT.
+ rewrite !aux /= !andbA; congr (_ && _); rewrite -!andbA; congr (_ && _).
  rewrite -andbCA; congr (_ && _); bool_congr; rewrite andbCA; bool_congr.
  by rewrite andbA andbC !andbA.
by elim: l1 => [| t1 l1 IHl1] //=; rewrite -andbA IHl1.
Qed.

Lemma qf_to_dnfP e :
  let qev f b := qf_eval e (odnf_to_oform (qf_to_odnf f b)) in
  forall f, qf_form f && rformula f -> qev f false = qf_eval e f.
Proof.
move=> qev; have qevT f: qev f true = ~~ qev f false.
  rewrite {}/qev; elim: f => //=; do [by case | move=> f1 IH1 f2 IH2 | ].
  - by move=> t1 t2; rewrite !andbT !orbF.
  - by move=> t1 t2; rewrite !andbT !orbF; rewrite !subr_gte0 -lerNgt.
  - by move=> t1 t2; rewrite !andbT !orbF; rewrite !subr_gte0 -ltrNge.
  - by rewrite and_odnfP cat_dnfP negb_and -IH1 -IH2.
  - by rewrite and_odnfP cat_dnfP negb_or -IH1 -IH2.
  - by rewrite and_odnfP cat_dnfP /= negb_or IH1 -IH2 negbK.
  by move=> t1 ->; rewrite negbK.
rewrite /qev; elim=> //=; first by case.
- by move=> t1 t2 _; rewrite subr_eq0 !andbT orbF.
- by move=> t1 t2 _; rewrite orbF !andbT subr_gte0.
- by move=> t1 t2 _; rewrite orbF !andbT subr_gte0.
- move=> f1 IH1 f2 IH2; rewrite andbCA -andbA andbCA andbA; case/andP.
  by rewrite and_odnfP /= => /IH1-> /IH2->.
- move=> f1 IH1 f2 IH2; rewrite andbCA -andbA andbCA andbA; case/andP.
  by rewrite cat_dnfP /= => /IH1-> => /IH2->.
- move=> f1 IH1 f2 IH2; rewrite andbCA -andbA andbCA andbA; case/andP.
  by rewrite cat_dnfP /= [qf_eval _ _]qevT -implybE => /IH1 <- /IH2->.
by move=> f1 IH1 /IH1 <-; rewrite -qevT.
Qed.

Lemma dnf_to_form_qf bcs : qf_form (odnf_to_oform bcs).
Proof.
elim: bcs => //= [[clT clF] clLt clLe ? ->] /=; elim: clT => //=.
by rewrite andbT; elim: clF; elim: clLt => //; elim: clLe.
Qed.

Definition dnf_rterm (cl : oclause R) :=
  [&& all (@rterm R) cl.1, all (@rterm R) cl.2,
  all (@rterm R) cl.3 & all (@rterm R) cl.4].

Lemma qf_to_dnf_rterm f b : rformula f -> all dnf_rterm (qf_to_odnf f b).
Proof.
set ok := all dnf_rterm.
have cat_ok bcs1 bcs2: ok bcs1 -> ok bcs2 -> ok (bcs1 ++ bcs2).
  by move=> ok1 ok2; rewrite [ok _]all_cat; apply/andP.
have and_ok bcs1 bcs2: ok bcs1 -> ok bcs2 -> ok (and_odnf bcs1 bcs2).
  rewrite /and_odnf unlock; elim: bcs1 => //= cl1 bcs1 IH1; rewrite -andbA.
  case/and3P=> ok11 ok12 ok1 ok2; rewrite cat_ok ?{}IH1 {bcs1 ok1}//.
  elim: bcs2 ok2 => //= cl2 bcs2 IH2 /andP[ok2 /IH2->].
  by rewrite /dnf_rterm /= !all_cat andbT ok11; case/and3P: ok12=> -> -> ->.
elim: f b => //=; try by [move=> _ ? ? [] | move=> ? ? ? ? [] /= /andP[]; auto].
- by do 2!case.
- by rewrite /dnf_rterm => ? ? [] /= ->.
- by rewrite /dnf_rterm => ? ? [] /=; rewrite andbC !andbT.
- by rewrite /dnf_rterm => ? ? [] /=; rewrite andbC !andbT.
by auto.
Qed.

Lemma dnf_to_rform bcs : rformula (odnf_to_oform bcs) = all dnf_rterm bcs.
Proof.
elim: bcs => //= [[cl1 cl2 cl3 cl4] bcs ->]; rewrite {2}/dnf_rterm /=; congr (_ && _).
congr andb; first by elim: cl1 => //= t cl ->; rewrite andbT.
congr andb; first by elim: cl2 => //= t cl ->; rewrite andbT.
congr andb; first by elim: cl3 => //= t cl ->.
by elim: cl4 => //= t cl ->.
Qed.

Implicit Type f : formula R.

Fixpoint leq_elim_aux (eq_l lt_l le_l : seq (term R)) :=
  match le_l with
    [::] => [:: (eq_l, lt_l)]
    |le1 :: le_l' =>
  let res := leq_elim_aux eq_l lt_l le_l' in
  let as_eq := map (fun x => (le1 :: x.1%PAIR, x.2%PAIR)) res in
  let as_lt := map (fun x => (x.1%PAIR, le1 :: x.2%PAIR)) res in
    as_eq ++ as_lt
  end.

Definition oclause_leq_elim oc : seq (oclause R) :=
  let: Oclause eq_l neq_l lt_l le_l := oc in
    map (fun x => Oclause x.1%PAIR neq_l x.2%PAIR [::])
    (leq_elim_aux eq_l lt_l le_l).

Definition terms_of_oclause (oc : oclause R) :=
  let: Oclause eq_l neq_l lt_l le_l := oc in
    eq_l ++ neq_l ++ lt_l ++ le_l.

Lemma terms_of_leq_elim oc1 oc2:
  oc2 \in (oclause_leq_elim oc1) ->
  (terms_of_oclause oc2) =i (terms_of_oclause oc1).
case: oc1 => eq1 neq1 lt1 leq1 /=.
elim: leq1 eq1 lt1 oc2 => [|t1 leq1 ih] eq1 lt1 [eq2 neq2 lt2 leq2] /=.
  by rewrite inE; case/eqP=> -> -> -> -> ?.
rewrite map_cat /= mem_cat -!map_comp; set f := fun _ => _.
rewrite -/f in ih; case/orP.
  case/mapP=> [[y1 y2]] yin ye.
  move: (ih eq1 lt1 (f (y1, y2))); rewrite mem_map //; last first.
    by move=> [u1 u2] [v1 v2]; rewrite /f /=; case=> -> ->.
  move/(_ yin); move: ye; rewrite /f /=; case=> -> -> -> -> /= h.
  move=> u; rewrite in_cons (h u) !mem_cat in_cons.
  by rewrite orbC !orbA; set x := _ || (u \in lt1); rewrite orbAC.
case/mapP=> [[y1 y2]] yin ye.
move: (ih eq1 lt1 (f (y1, y2))); rewrite mem_map //; last first.
  by move=> [u1 u2] [v1 v2]; rewrite /f /=; case=> -> ->.
move/(_ yin); move: ye; rewrite /f /=; case=> -> -> -> -> /= h u.
rewrite !mem_cat !in_cons orbA orbCA -!orbA; move: (h u); rewrite !mem_cat=> ->.
by rewrite orbC !orbA; set x := _ || (u \in lt1); rewrite orbAC.
Qed.

Lemma odnf_to_oform_cat e c d : holds e (odnf_to_oform (c ++ d))
              <-> holds e ((odnf_to_oform c) \/ (odnf_to_oform d))%oT.
Proof.
elim: c d => [| tc c ihc] d /=; first by split => // hd; [right | case: hd].
rewrite ihc /=; split.
  case; first by case=> ?; case=> ?; case=> ? ?; left; left.
  case; first by move=> ?; left; right.
  by move=> ?; right.
case; last by move=> ?; right; right.
case; last by move=> ?; right; left.
by do 3!case=> ?; move=> ?; left.
Qed.

Lemma oclause_leq_elimP oc e :
  holds e (odnf_to_oform [:: oc])  <->
  holds e (odnf_to_oform (oclause_leq_elim oc)).
Proof.
case: oc => eq_l neq_l lt_l le_l; rewrite /oclause_leq_elim.
elim: le_l eq_l neq_l lt_l => [|t le_l ih] eq_l neq_l lt_l //=.
move: (ih eq_l neq_l lt_l) => /= {ih}.
set x1 := foldr _ _ _; set x2 := foldr _ _ _; set x3 := foldr _ _ _.
set x4 := foldr _ _ _ => h.
have -> : (holds e x1 /\ holds e x2 /\ holds e x3 /\ 0%:R <= eval e t /\
            holds e x4 \/ false) <->
          (0%:R <= eval e t) /\ (holds e x1 /\ holds e x2 /\ holds e x3 /\
            holds e x4 \/ false).
  split; first by case=> //; do 4!(case=> ?); move=> ?; split => //; left.
  by case=> ?; case=> //; do 3!(case=> ?); move=> ?; left.
rewrite h {h} /= !map_cat /= -!map_comp.
set s1 := [seq _ | _ <- _]; set s2 := [seq _ | _ <- _].
set s3 := [seq _ | _ <- _]. rewrite odnf_to_oform_cat.
suff {x1 x2 x3 x4} /= -> :
  holds e (odnf_to_oform s2) <-> eval e t == 0%:R /\ holds e (odnf_to_oform s1).
  suff /= -> :
    holds e (odnf_to_oform s3) <-> 0%:R < eval e t /\ holds e (odnf_to_oform s1).
    rewrite ler_eqVlt eq_sym; split; first by case; case/orP=> -> ?; [left|right].
    by case; [case=> -> ? /= |case=> ->; rewrite orbT].
  rewrite /s1 /s3.
  elim: (leq_elim_aux eq_l lt_l le_l) => /= [| t1 l ih]; first by split=> // [[]].
  rewrite /= ih; split.
    case; last by case=> -> ?; split=> //; right.
    by do 2!case=> ?; case; case=> -> ? _; split => //; auto.
  by case=> ->; case; [do 3!case=> ?; move=> _; left | right].
rewrite /s2 /s1.
elim: (leq_elim_aux eq_l lt_l le_l) => /= [| t1 l ih]; first by split=> // [[]].
rewrite /= ih; split.
  case; last by case=> -> ?; split=> //; right.
  by case; case=> /eqP ? ?; do 2!case=> ?; move=> _; split=> //; left.
case=> /eqP ?; case; first by do 3!case=> ?; move=> _; left.
by right; split=> //; apply/eqP.
Qed.

Fixpoint neq_elim_aux (lt_l neq_l : seq (term R)) :=
  match neq_l with
    [::] => [:: lt_l]
    |neq1 :: neq_l' =>
  let res := neq_elim_aux lt_l neq_l' in
  let as_pos := map (fun x => neq1 :: x) res in
  let as_neg := map (fun x => Opp neq1 :: x) res in
    as_pos ++ as_neg
  end.

Definition oclause_neq_elim oc : seq (oclause R) :=
  let: Oclause eq_l neq_l lt_l le_l := oc in
    map (fun x => Oclause eq_l [::] x le_l) (neq_elim_aux lt_l neq_l).

Lemma terms_of_neq_elim oc1 oc2:
  oc2 \in (oclause_neq_elim oc1) ->
  {subset (terms_of_oclause oc2) <= (terms_of_oclause oc1) ++ (map Opp oc1.2)}.
Proof.
case: oc1 => eq1 neq1 lt1 leq1 /=.
elim: neq1 lt1 oc2 => [|t1 neq1 ih] lt1 [eq2 neq2 lt2 leq2] /=.
  by rewrite inE; case/eqP=> -> -> -> ->; rewrite !cats0 !cat0s.
rewrite map_cat /= mem_cat -!map_comp; set f := fun _ => _.
rewrite -/f in ih; case/orP.
  case/mapP=> y yin ye.
  move: (ih lt1 (f y)); rewrite mem_map //; last first.
    by move=> u v; rewrite /f /=; case.
  move/(_ yin); move: ye; rewrite /f /=; case=> -> -> -> -> /= h.
  move=> u. rewrite !mem_cat !in_cons orbAC orbC mem_cat -!orbA.
  case/orP; first by move->; rewrite !orbT.
  rewrite !orbA [_ || (_ \in eq1)]orbC; move: (h u); rewrite !mem_cat=> hu.
  by move/hu; do 2!(case/orP; last by move->; rewrite !orbT); move->.
case/mapP=> y yin ye.
move: (ih lt1 (f y)); rewrite mem_map //; last first.
  by move=> u v; rewrite /f /=; case.
move/(_ yin); move: ye; rewrite /f /=; case=> -> -> -> -> /= h.
move=> u; rewrite !mem_cat !in_cons orbAC orbC mem_cat -!orbA.
case/orP; first by move->; rewrite !orbT.
rewrite !orbA [_ || (_ \in eq1)]orbC; move: (h u); rewrite !mem_cat=> hu.
by move/hu; do 2!(case/orP; last by move->; rewrite !orbT); move->.
Qed.


Lemma oclause_neq_elimP oc e :
  holds e (odnf_to_oform [:: oc])  <->
  holds e (odnf_to_oform (oclause_neq_elim oc)).
Proof.
case: oc => eq_l neq_l lt_l le_l; rewrite /oclause_neq_elim.
elim: neq_l lt_l => [|t neq_l ih] lt_l //=.
move: (ih lt_l) => /= {ih}.
set x1 := foldr _ _ _; set x2 := foldr _ _ _; set x3 := foldr _ _ _.
set x4 := foldr _ _ _ => h /=.
have -> : holds e x1 /\
   (eval e t <> 0%:R /\
    holds e x2) /\
   holds e x3 /\ holds e x4 \/
   false <->
          (eval e t <> 0%:R) /\ (holds e x1 /\ holds e x2 /\ holds e x3 /\
            holds e x4 \/ false).
  split; case=> //.
  - by case=> ?; case; case=> ? ? [] ? ?; split=> //; left.
  - by move=> ?; case=> //; do 3!case=> ?; move=> ?; left.
rewrite h {h} /= !map_cat /= -!map_comp.
set s1 := [seq _ | _ <- _]; set s2 := [seq _ | _ <- _].
set s3 := [seq _ | _ <- _]; rewrite odnf_to_oform_cat.
suff {x1 x2 x3 x4} /= -> :
  holds e (odnf_to_oform s2) <-> 0%:R < eval e t/\ holds e (odnf_to_oform s1).
  suff /= -> :
    holds e (odnf_to_oform s3) <-> 0%:R < - eval e t /\ holds e (odnf_to_oform s1).
    rewrite oppr_gt0; split.
      by case; move/eqP; rewrite neqr_lt; case/orP=> -> h1; [right | left].
    by case; case=> h ?; split=> //; apply/eqP; rewrite neqr_lt h ?orbT.
  rewrite /s1 /s3.
  elim: (neq_elim_aux lt_l neq_l) => /= [| t1 l ih] /=; first by split => //; case.
  set y1 := foldr _ _ _; set y2 := foldr _ _ _; set y3 := foldr _ _ _.
  rewrite ih; split.
    case; first by case=> ?; case=> _; case; case=> -> ? ?; split=> //; left.
    by case=> ? ?; split=> //; right.
  by case=> ->; case; [case=> ?; case=> _; case=> ? ?; left| move=> ?; right].
rewrite /s1 /s2.
elim: (neq_elim_aux lt_l neq_l) => /= [| t1 l ih] /=; first by split => //; case.
set y1 := foldr _ _ _; set y2 := foldr _ _ _; set y3 := foldr _ _ _.
rewrite ih; split.
  case; first by case=> ? [] _ [] [] ? ? ?; split=> //; left.
  by case=> ? ?; split=> //; right.
case=> ? []; last by right.
by case=> ? [] _ [] ? ?; left.
Qed.

Definition oclause_neq_leq_elim oc :=
  flatten (map oclause_neq_elim (oclause_leq_elim oc)).

Lemma terms_of_neq_leq_elim oc1 oc2:
  oc2 \in (oclause_neq_leq_elim oc1) ->
  {subset (terms_of_oclause oc2) <= (terms_of_oclause oc1) ++ map Opp oc1.2}.
Proof.
rewrite /oclause_neq_leq_elim/flatten; rewrite foldr_map.
suff : forall oc3,
  oc3 \in (oclause_leq_elim oc1) ->
  (terms_of_oclause oc3 =i terms_of_oclause oc1) /\ oc3.2 = oc1.2.
  elim: (oclause_leq_elim oc1) => [| t l ih] //= h1.
  rewrite mem_cat; case/orP.
  - move/terms_of_neq_elim=> h u; move/(h u); rewrite !mem_cat.
    by case: (h1 t (mem_head _ _)); move/(_ u)=> -> ->.
  - by move=> h; apply: (ih _ h) => ? loc3; apply: h1; rewrite in_cons loc3 orbT.
move=> {oc2} oc3 hoc3; split; first exact: terms_of_leq_elim.
case: oc3 hoc3=> eq2 neq2 lt2 leq2 /=; case: oc1=> eq1 neq1 lt1 leq1 /=.
elim: leq1 => [| t1 le1 ih] //=; first by rewrite inE; case/eqP=> _ ->.
rewrite map_cat mem_cat; move: ih.
elim: (leq_elim_aux eq1 lt1 le1) => [| t2 l2 ih2] //=; rewrite !in_cons.
move=> h1; case/orP=> /=.
  case/orP; first by case/eqP.
  by move=> h2; apply: ih2; rewrite ?h2 // => - h3; apply: h1; rewrite h3 orbT.
case/orP; first by case/eqP.
move=> h3; apply: ih2; last by rewrite h3 orbT.
by move=> h2; apply: h1; rewrite h2 orbT.
Qed.

Lemma oclause_neq_leq_elimP oc e :
  holds e (odnf_to_oform [:: oc])  <->
  holds e (odnf_to_oform (oclause_neq_leq_elim oc)).
Proof.
rewrite /oclause_neq_leq_elim.
rewrite oclause_leq_elimP; elim: (oclause_leq_elim oc) => [| t l ih] //=.
rewrite odnf_to_oform_cat /= ih -oclause_neq_elimP /=.
suff -> : forall A, A \/ false <-> A by [].
by intuition.
Qed.

Definition oclause_to_w oc :=
  let s := oclause_neq_leq_elim oc in
    map (fun x => let: Oclause eq_l neq_l lt_l leq_l := x in (eq_l, lt_l)) s.

Definition w_to_oclause (t : seq (term R) * seq (term R)) :=
  Oclause t.1%PAIR [::] t.2%PAIR [::].

Lemma oclause_leq_elim4 bc oc : oc \in (oclause_leq_elim bc) -> oc.4 == [::].
Proof.
case: bc => bc1 bc2 bc3 bc4; elim: bc4 bc1 bc3 oc => [|t bc4 ih] bc1 bc3 /= oc.
  by rewrite inE; move/eqP; case: oc => ? ? ? oc4 /=; case=> _ _ _ /eqP.
rewrite map_cat; move: (ih bc1 bc3 oc) => /= {ih}.
elim: (leq_elim_aux bc1 bc3 bc4) => [| t2 l2 ih2] //= ih1.
rewrite in_cons; case/orP.
  by move/eqP; case: oc {ih1 ih2} => ? ? ? ? [] /= _ _ _ /eqP.
rewrite mem_cat; case/orP=> [hoc1|].
  apply: ih2; first by move=> hoc2; apply: ih1; rewrite in_cons hoc2 orbT.
  by rewrite mem_cat hoc1.
rewrite in_cons; case/orP=> [| hoc1].
  by move/eqP; case: {ih1 ih2} oc=> ? ? ? ?  [] /= _ _ _ /eqP.
apply: ih2; first by move=> hoc2; apply: ih1; rewrite in_cons hoc2 orbT.
by rewrite mem_cat hoc1 orbT.
Qed.

Lemma oclause_neq_elim2 bc oc :
  oc \in (oclause_neq_elim bc) -> (oc.2 == [::]) && (oc.4 == bc.4).
Proof.
case: bc => bc1 bc2 bc3 bc4; elim: bc2 bc4 oc => [|t bc2 /= ih] bc4 /= oc.
  by rewrite inE; move/eqP; case: oc => ? ? ? oc4 /=; case=> _ /eqP -> _ /eqP.
rewrite map_cat; move: (ih bc4 oc) => /= {ih}.
elim: (neq_elim_aux bc3 bc2) => [| t2 l2 ih2] //= ih1.
rewrite in_cons; case/orP.
  by move/eqP; case: oc {ih1 ih2} => ? ? ? ? [] /= _ -> _ ->; rewrite !eqxx.
rewrite mem_cat; case/orP=> [hoc1|].
  apply: ih2; first by move=> hoc2; apply: ih1; rewrite in_cons hoc2 orbT.
  by rewrite mem_cat hoc1.
rewrite in_cons; case/orP=> [| hoc1].
  by move/eqP; case: {ih1 ih2} oc=> ? ? ? ?  [] /= _ ->  _ ->; rewrite !eqxx.
apply: ih2; first by move=> hoc2; apply: ih1; rewrite in_cons hoc2 orbT.
by rewrite mem_cat hoc1 orbT.
Qed.

Lemma oclause_to_wP e bc :
  holds e (odnf_to_oform (oclause_neq_leq_elim bc)) <->
  holds e (odnf_to_oform (map w_to_oclause (oclause_to_w bc))).
Proof.
rewrite /oclause_to_w /oclause_neq_leq_elim.
move: (@oclause_leq_elim4 bc).
elim: (oclause_leq_elim bc) => [| t1 l1 ih1] //= h4.
rewrite !map_cat !odnf_to_oform_cat.
rewrite -[holds e (_ \/ _)]/(holds e _ \/ holds e _).
suff <- : (oclause_neq_elim t1) = map w_to_oclause
           [seq (let: Oclause eq_l _  lt_l _ := x in (eq_l, lt_l))
              | x <- oclause_neq_elim t1].
  by rewrite ih1 // => - oc hoc; apply: h4; rewrite in_cons hoc orbT.
have : forall oc, oc \in (oclause_neq_elim t1) -> oc.2 = [::] /\ oc.4 = [::].
  move=> oc hoc; move/oclause_neq_elim2: (hoc); case/andP=> /eqP -> /eqP ->.
  by move/eqP: (h4 _ (mem_head _ _))->.
elim: (oclause_neq_elim t1) => [| [teq1 tneq1 tleq1 tlt1] l2 ih2] h24 //=.
rewrite /w_to_oclause /=; move: (h24 _ (mem_head _ _ ))=> /= [] -> ->.
by congr (_ :: _); apply: ih2 => oc hoc; apply: h24; rewrite in_cons hoc orbT.
Qed.

Variable wproj : nat -> (seq (term R) * seq (term R)) -> formula R.

Definition proj (n : nat)(oc : oclause R) :=
  foldr Or False (map (wproj n) (oclause_to_w oc)).

Hypothesis wf_QE_wproj : forall i bc (bc_i := wproj i bc),
  dnf_rterm (w_to_oclause bc) -> qf_form bc_i && rformula bc_i.

Lemma dnf_rterm_subproof bc : dnf_rterm bc ->
  all (dnf_rterm \o w_to_oclause) (oclause_to_w bc).
Proof.
case: bc => leq lneql llt lle; rewrite /dnf_rterm /=; case/and4P=> req rneq rlt rle.
rewrite /oclause_to_w /= !all_map.
apply/allP => [] [oc_eq oc_neq oc_le oc_lt] hoc; rewrite /dnf_rterm /= andbT.
rewrite -all_cat; apply/allP=> u hu; move/terms_of_neq_leq_elim: hoc => /=.
move/(_ u); rewrite !mem_cat.
have {hu} hu : [|| u \in oc_eq, u \in oc_neq, u \in oc_le | u \in oc_lt].
  by move: hu; rewrite mem_cat; case/orP=> ->; rewrite ?orbT.
move/(_ hu); case/orP; last first.
  move: rneq.
  have <- : (all (@rterm R) (map Opp lneql)) = all (@rterm R) lneql.
    by elim: lneql => [| t l] //= ->.
  by move/allP; apply.
case/orP; first by apply: (allP req).
case/orP; first by apply: (allP rneq).
case/orP; first by apply: (allP rlt).
exact: (allP rle).
Qed.


Lemma wf_QE_proj i : forall bc (bc_i := proj i bc),
  dnf_rterm bc -> qf_form bc_i && rformula bc_i.
Proof.
case=> leq lneql llt lle /= hdnf; move: (hdnf).
rewrite /dnf_rterm /=; case/and4P=> req rneq rlt rle; rewrite /proj; apply/andP.
move: (dnf_rterm_subproof hdnf).
elim: (oclause_to_w _ ) => //= [a t] ih /andP [h1 h2].
by case: (ih h2)=> -> ->; case/andP: (wf_QE_wproj i h1) => -> ->.
Qed.

Hypothesis valid_QE_wproj :
  forall i bc (bc' := w_to_oclause bc)
    (ex_i_bc := ('exists 'X_i, odnf_to_oform [:: bc'])%oT) e,
  dnf_rterm bc' ->
  reflect (holds e ex_i_bc) (qf_eval e (wproj i bc)).

Lemma valid_QE_proj e i : forall bc (bc_i := proj i bc)
  (ex_i_bc := ('exists 'X_i, odnf_to_oform [:: bc])%oT),
  dnf_rterm bc -> reflect (holds e ex_i_bc) (qf_eval e (proj i bc)).
Proof.
move=> bc; rewrite /dnf_rterm => hdnf; rewrite /proj; apply: (equivP idP).
have -> : holds e ('exists 'X_i, odnf_to_oform [:: bc]) <->
          (exists x : R, holds (set_nth 0 e i x)
            (odnf_to_oform (oclause_neq_leq_elim bc))).
  split; case=> x h; exists x; first by rewrite -oclause_neq_leq_elimP.
  by rewrite oclause_neq_leq_elimP.
have -> :
  (exists x : R,
    holds (set_nth 0 e i x) (odnf_to_oform (oclause_neq_leq_elim bc))) <->
  (exists x : R,
    holds (set_nth 0 e i x) (odnf_to_oform (map w_to_oclause (oclause_to_w bc)))).
  by split; case=> x; move/oclause_to_wP=> h; exists x.
move: (dnf_rterm_subproof hdnf).
rewrite /oclause_to_w; elim: (oclause_neq_leq_elim bc) => /= [|a l ih].
  by split=> //; case.
case/andP=> h1 h2; have {ih h2} ih := (ih h2); split.
- case/orP.
    move/(valid_QE_wproj i e h1)=> /= [x /=] [] // [] h2 [] _ [] h3 _; exists x.
    by left.
  by case/ih => x h; exists x; right.
- case=> x [] /=.
  + case=> h2 [] _ h3; apply/orP; left; apply/valid_QE_wproj => //=.
    by exists x; left.
  + by move=> hx; apply/orP; right; apply/ih; exists x.
Qed.

Let elim_aux f n := foldr Or False (map (proj n) (qf_to_odnf f false)).

Fixpoint quantifier_elim f :=
  match f with
  | f1 /\ f2 => (quantifier_elim f1) /\ (quantifier_elim f2)
  | f1 \/ f2 => (quantifier_elim f1) \/ (quantifier_elim f2)
  | f1 ==> f2 => (~ quantifier_elim f1) \/ (quantifier_elim f2)
  | ~ f => ~ quantifier_elim f
  | ('exists 'X_n, f) => elim_aux (quantifier_elim f) n
  | ('forall 'X_n, f) => ~ elim_aux (~ quantifier_elim f) n
  | _ => f
  end%oT.

Lemma quantifier_elim_wf f :
  let qf := quantifier_elim f in rformula f -> qf_form qf && rformula qf.
Proof.
suffices aux_wf f0 n : let qf := elim_aux f0 n in
  rformula f0 -> qf_form qf && rformula qf.
- by elim: f => //=; do ?[  move=> f1 IH1 f2 IH2;
                     case/andP=> rf1 rf2;
                     case/andP:(IH1 rf1)=> -> ->;
                     case/andP:(IH2 rf2)=> -> -> //
                  |  move=> n f1 IH rf1;
                     case/andP: (IH rf1)=> qff rf;
                     rewrite aux_wf ].
rewrite /elim_aux => rf.
suffices or_wf fs : let ofs := foldr Or False fs in
  all qf_form fs && all rformula fs -> qf_form ofs && rformula ofs.
- apply: or_wf.
  suffices map_proj_wf bcs: let mbcs := map (proj n) bcs in
    all dnf_rterm bcs -> all qf_form mbcs && all rformula mbcs.
    by apply: map_proj_wf; apply: qf_to_dnf_rterm.
  elim: bcs => [|bc bcs ihb] bcsr //= /andP[rbc rbcs].
  by rewrite andbAC andbA wf_QE_proj //= andbC ihb.
elim: fs => //= g gs ihg; rewrite -andbA => /and4P[-> qgs -> rgs] /=.
by apply: ihg; rewrite qgs rgs.
Qed.

Lemma quantifier_elim_rformP e f :
  rformula f -> reflect (holds e f) (qf_eval e (quantifier_elim f)).
Proof.
pose rc e n f := exists x, qf_eval (set_nth 0 e n x) f.
have auxP f0 e0 n0: qf_form f0 && rformula f0 ->
  reflect (rc e0 n0 f0) (qf_eval e0 (elim_aux f0 n0)).
+ rewrite /elim_aux => cf; set bcs := qf_to_odnf f0 false.
  apply: (@iffP (rc e0 n0 (odnf_to_oform bcs))); last first.
  - by case=> x; rewrite -qf_to_dnfP //; exists x.
  - by case=> x; rewrite qf_to_dnfP //; exists x.
  have: all dnf_rterm bcs by case/andP: cf => _; apply: qf_to_dnf_rterm.
  elim: {f0 cf}bcs => [|bc bcs IHbcs] /=; first by right; case.
  case/andP=> r_bc /IHbcs {IHbcs}bcsP.
  have f_qf := dnf_to_form_qf [:: bc].
  case: valid_QE_proj => //= [ex_x|no_x].
    left; case: ex_x => x /(qf_evalP _ f_qf); rewrite /= orbF => bc_x.
    by exists x; rewrite /= bc_x.
  apply: (iffP bcsP) => [[x bcs_x] | [x]] /=.
    by exists x; rewrite /= bcs_x orbT.
  case/orP => [bc_x|]; last by exists x.
  by case: no_x; exists x; apply/(qf_evalP _ f_qf); rewrite /= bc_x.
elim: f e => //.
- by move=> b e _; apply: idP.
- by move=> t1 t2 e _; apply: eqP.
- by move=> t1 t2 e _; apply: idP.
- by move=> t1 t2 e _; apply: idP.
- move=> f1 IH1 f2 IH2 e /= /andP[/IH1[] f1e]; last by right; case.
  by case/IH2; [left | right; case].
- move=> f1 IH1 f2 IH2 e /= /andP[/IH1[] f1e]; first by do 2!left.
  by case/IH2; [left; right | right; case].
- move=> f1 IH1 f2 IH2 e /= /andP[/IH1[] f1e]; last by left.
  by case/IH2; [left | right; move/(_ f1e)].
- by move=> f IHf e /= /IHf[]; [right | left].
- move=> n f IHf e /= rf; have rqf := quantifier_elim_wf rf.
  by apply: (iffP (auxP _ _ _ rqf)) => [] [x]; exists x; apply/IHf.
move=> n f IHf e /= rf; have rqf := quantifier_elim_wf rf.
case: auxP => // [f_x|no_x]; first by right=> no_x; case: f_x => x /IHf[].
by left=> x; apply/IHf=> //; apply/idPn=> f_x; case: no_x; exists x.
Qed.

Definition proj_sat e f := qf_eval e (quantifier_elim (to_rform f)).

Lemma proj_satP :   forall e f, reflect (holds e f) (proj_sat e f).
Proof.
move=> e f; have fP := quantifier_elim_rformP e (to_rform_rformula f).
by apply: (iffP fP); move/to_rformP.
Qed.

End EvalTerm.

End ord.
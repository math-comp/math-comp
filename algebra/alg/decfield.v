(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype finfun bigop nmodule algebra divalg.

(******************************************************************************)
(*                  Decidable and algebraically closed fields                 *)
(*                                                                            *)
(* NB: See CONTRIBUTING.md for an introduction to HB concepts and commands.   *)
(*                                                                            *)
(* Reference: Francois Garillot, Georges Gonthier, Assia Mahboubi, Laurence   *)
(* Rideau, Packaging mathematical structures, TPHOLs 2009                     *)
(*                                                                            *)
(* This file defines the following algebraic structures:                      *)
(*                                                                            *)
(*    decFieldType == fields with a decidable first order theory              *)
(*                    The HB class is called DecidableField.                  *)
(* closedFieldType == algebraically closed fields                             *)
(*                    The HB class is called ClosedField.                     *)
(*                                                                            *)
(* Canonical properties of the algebraic structures:                          *)
(*                                                                            *)
(*  * DecidableField (fields with a decidable first order theory):            *)
(*           GRing.term R == the type of formal expressions in a unit ring R  *)
(*                           with formal variables 'X_k, k : nat, and         *)
(*                           manifest constants x%:T, x : R                   *)
(*                           The notation of all the ring operations is       *)
(*                           redefined for terms, in scope %T.                *)
(*        GRing.formula R == the type of first order formulas over R; the %T  *)
(*                           scope binds the logical connectives /\, \/, ~,   *)
(*                           ==>, ==, and != to formulae; GRing.True/False    *)
(*                           and GRing.Bool b denote constant formulae, and   *)
(*                           quantifiers are written 'forall/'exists 'X_k, f  *)
(*                             GRing.Unit x tests for ring units              *)
(*                             GRing.If p_f t_f e_f emulates if-then-else     *)
(*                             GRing.Pick p_f t_f e_f emulates fintype.pick   *)
(*                             foldr GRing.Exists/Forall q_f xs can be used   *)
(*                               to write iterated quantifiers                *)
(*         GRing.eval e t == the value of term t with valuation e : seq R     *)
(*                           (e maps 'X_i to e`_i)                            *)
(*  GRing.same_env e1 e2 <-> environments e1 and e2 are extensionally equal   *)
(*        GRing.qf_form f == f is quantifier-free                             *)
(*        GRing.holds e f == the intuitionistic CiC interpretation of the     *)
(*                           formula f holds with valuation e                 *)
(*      GRing.qf_eval e f == the value (in bool) of a quantifier-free f       *)
(*          GRing.sat e f == valuation e satisfies f (only in a decField)     *)
(*          GRing.sol n f == a sequence e of size n such that e satisfies f,  *)
(*                           if one exists, or [::] if there is no such e     *)
(*        'exists 'X_i, u1 == 0 /\ ... /\ u_m == 0 /\ v1 != 0 ... /\ v_n != 0 *)
(*                                                                            *)
(* See algebra.v for general remarks about the module layout, the notation    *)
(* scopes, and the naming convention for lemmas. In addition, the notations   *)
(* for term and formula are defined in term_scope (delimiter %T).             *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope term_scope.
Delimit Scope term_scope with T.

Local Open Scope ring_scope.

Module Import GRing.

(* FIXME: Since we should not import GRing, we should be able to remove this: *)
Export GRing.

(* Reification of the theory of rings with units, in named style  *)
Section TermDef.

Variable R : Type.

Inductive term : Type :=
| Var of nat
| Const of R
| NatConst of nat
| Add of term & term
| Opp of term
| NatMul of term & nat
| Mul of term & term
| Inv of term
| Exp of term & nat.

Inductive formula : Type :=
| Bool of bool
| Equal of term & term
| Unit of term
| And of formula & formula
| Or of formula & formula
| Implies of formula & formula
| Not of formula
| Exists of nat & formula
| Forall of nat & formula.

End TermDef.

Bind Scope term_scope with term.
Bind Scope term_scope with formula.
Arguments Add {R} t1%_T t2%_T.
Arguments Opp {R} t1%_T.
Arguments NatMul {R} t1%_T n%_N.
Arguments Mul {R} t1%_T t2%_T.
Arguments Inv {R} t1%_T.
Arguments Exp {R} t1%_T n%_N.
Arguments Equal {R} t1%_T t2%_T.
Arguments Unit {R} t1%_T.
Arguments And {R} f1%_T f2%_T.
Arguments Or {R} f1%_T f2%_T.
Arguments Implies {R} f1%_T f2%_T.
Arguments Not {R} f1%_T.
Arguments Exists {R} i%_N f1%_T.
Arguments Forall {R} i%_N f1%_T.

Arguments Bool {R} b.
Arguments Const {R} x.

Notation True := (Bool true).
Notation False := (Bool false).

Local Notation "''X_' i" := (Var _ i) : term_scope.
Local Notation "n %:R" := (NatConst _ n) : term_scope.
Local Notation "x %:T" := (Const x) : term_scope.
Local Notation "0" := 0%:R%T : term_scope.
Local Notation "1" := 1%:R%T : term_scope.
Local Infix "+" := Add : term_scope.
Local Notation "- t" := (Opp t) : term_scope.
Local Notation "t - u" := (Add t (- u)) : term_scope.
Local Infix "*" := Mul : term_scope.
Local Infix "*+" := NatMul : term_scope.
Local Notation "t ^-1" := (Inv t) : term_scope.
Local Notation "t / u" := (Mul t u^-1) : term_scope.
Local Infix "^+" := Exp : term_scope.
Local Infix "==" := Equal : term_scope.
Local Infix "/\" := And : term_scope.
Local Infix "\/" := Or : term_scope.
Local Infix "==>" := Implies : term_scope.
Local Notation "~ f" := (Not f) : term_scope.
Local Notation "x != y" := (Not (x == y)) : term_scope.
Local Notation "''exists' ''X_' i , f" := (Exists i f) : term_scope.
Local Notation "''forall' ''X_' i , f" := (Forall i f) : term_scope.

Section Substitution.

Variable R : Type.

Fixpoint tsubst (t : term R) (s : nat * term R) :=
  match t with
  | 'X_i => if i == s.1 then s.2 else t
  | _%:T | _%:R => t
  | t1 + t2 => tsubst t1 s + tsubst t2 s
  | - t1 => - tsubst t1 s
  | t1 *+ n => tsubst t1 s *+ n
  | t1 * t2 => tsubst t1 s * tsubst t2 s
  | t1^-1 => (tsubst t1 s)^-1
  | t1 ^+ n => tsubst t1 s ^+ n
  end%T.

Fixpoint fsubst (f : formula R) (s : nat * term R) :=
  match f with
  | Bool _ => f
  | t1 == t2 => tsubst t1 s == tsubst t2 s
  | Unit t1 => Unit (tsubst t1 s)
  | f1 /\ f2 => fsubst f1 s /\ fsubst f2 s
  | f1 \/ f2 => fsubst f1 s \/ fsubst f2 s
  | f1 ==> f2 => fsubst f1 s ==> fsubst f2 s
  | ~ f1 => ~ fsubst f1 s
  | ('exists 'X_i, f1) => 'exists 'X_i, if i == s.1 then f1 else fsubst f1 s
  | ('forall 'X_i, f1) => 'forall 'X_i, if i == s.1 then f1 else fsubst f1 s
  end%T.

End Substitution.

Section EvalTerm.

Variable R : unitRingType.

(* Evaluation of a reified term into R a ring with units *)
Fixpoint eval (e : seq R) (t : term R) {struct t} : R :=
  match t with
  | ('X_i)%T => e`_i
  | (x%:T)%T => x
  | (n%:R)%T => n%:R
  | (t1 + t2)%T => eval e t1 + eval e t2
  | (- t1)%T => - eval e t1
  | (t1 *+ n)%T => eval e t1 *+ n
  | (t1 * t2)%T => eval e t1 * eval e t2
  | t1^-1%T => (eval e t1)^-1
  | (t1 ^+ n)%T => eval e t1 ^+ n
  end.

Definition same_env (e e' : seq R) := nth 0 e =1 nth 0 e'.

Lemma eq_eval e e' t : same_env e e' -> eval e t = eval e' t.
Proof. by move=> eq_e; elim: t => //= t1 -> // t2 ->. Qed.

Lemma eval_tsubst e t s :
  eval e (tsubst t s) = eval (set_nth 0 e s.1 (eval e s.2)) t.
Proof.
case: s => i u; elim: t => //=; do 2?[move=> ? -> //] => j.
by rewrite nth_set_nth /=; case: (_ == _).
Qed.

(* Evaluation of a reified formula *)
Fixpoint holds (e : seq R) (f : formula R) {struct f} : Prop :=
  match f with
  | Bool b => b
  | (t1 == t2)%T => eval e t1 = eval e t2
  | Unit t1 => eval e t1 \in unit
  | (f1 /\ f2)%T => holds e f1 /\ holds e f2
  | (f1 \/ f2)%T => holds e f1 \/ holds e f2
  | (f1 ==> f2)%T => holds e f1 -> holds e f2
  | (~ f1)%T => ~ holds e f1
  | ('exists 'X_i, f1)%T => exists x, holds (set_nth 0 e i x) f1
  | ('forall 'X_i, f1)%T => forall x, holds (set_nth 0 e i x) f1
  end.

Lemma same_env_sym e e' : same_env e e' -> same_env e' e.
Proof. exact: fsym. Qed.

(* Extensionality of formula evaluation *)
Lemma eq_holds e e' f : same_env e e' -> holds e f -> holds e' f.
Proof.
pose sv := set_nth (0 : R).
have eq_i i v e1 e2: same_env e1 e2 -> same_env (sv e1 i v) (sv e2 i v).
  by move=> eq_e j; rewrite !nth_set_nth /= eq_e.
elim: f e e' => //=.
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
  by rewrite set_set_nth 1?[i == j]eq_sym eq_ji; tauto.
Qed.

(* Boolean test selecting terms in the language of rings *)
Fixpoint rterm (t : term R) :=
  match t with
  | _^-1 => false
  | t1 + t2 | t1 * t2 => rterm t1 && rterm t2
  | - t1 | t1 *+ _ | t1 ^+ _ => rterm t1
  | _ => true
  end%T.

(* Boolean test selecting formulas in the theory of rings *)
Fixpoint rformula (f : formula R) :=
  match f with
  | Bool _ => true
  | t1 == t2 => rterm t1 && rterm t2
  | Unit t1 => false
  | f1 /\ f2 | f1 \/ f2 | f1 ==> f2 => rformula f1 && rformula f2
  | ~ f1 | ('exists 'X__, f1) | ('forall 'X__, f1) => rformula f1
  end%T.

(* Upper bound of the names used in a term *)
Fixpoint ub_var (t : term R) :=
  match t with
  | 'X_i => i.+1
  | t1 + t2 | t1 * t2 => maxn (ub_var t1) (ub_var t2)
  | - t1 | t1 *+ _ | t1 ^+ _ | t1^-1 => ub_var t1
  | _ => 0%N
  end%T.

(* Replaces inverses in the term t by fresh variables, accumulating the *)
(* substitution. *)
Fixpoint to_rterm (t : term R) (r : seq (term R)) (n : nat) {struct t} :=
  match t with
  | t1^-1 =>
    let: (t1', r1) := to_rterm t1 r n in
      ('X_(n + size r1), rcons r1 t1')
  | t1 + t2 =>
    let: (t1', r1) := to_rterm t1 r n in
    let: (t2', r2) := to_rterm t2 r1 n in
      (t1' + t2', r2)
  | - t1 =>
   let: (t1', r1) := to_rterm t1 r n in
     (- t1', r1)
  | t1 *+ m =>
   let: (t1', r1) := to_rterm t1 r n in
     (t1' *+ m, r1)
  | t1 * t2 =>
    let: (t1', r1) := to_rterm t1 r n in
    let: (t2', r2) := to_rterm t2 r1 n in
      (Mul t1' t2', r2)
  | t1 ^+ m =>
       let: (t1', r1) := to_rterm t1 r n in
     (t1' ^+ m, r1)
  | _ => (t, r)
  end%T.

Lemma to_rterm_id t r n : rterm t -> to_rterm t r n = (t, r).
Proof.
elim: t r n => //.
- by move=> t1 IHt1 t2 IHt2 r n /= /andP[rt1 rt2]; rewrite {}IHt1 // IHt2.
- by move=> t IHt r n /= rt; rewrite {}IHt.
- by move=> t IHt r n m /= rt; rewrite {}IHt.
- by move=> t1 IHt1 t2 IHt2 r n /= /andP[rt1 rt2]; rewrite {}IHt1 // IHt2.
- by move=> t IHt r n m /= rt; rewrite {}IHt.
Qed.

(* A ring formula stating that t1 is equal to 0 in the ring theory. *)
(* Also applies to non commutative rings.                           *)
Definition eq0_rform t1 :=
  let m := ub_var t1 in
  let: (t1', r1) := to_rterm t1 [::] m in
  let fix loop r i := match r with
  | [::] => t1' == 0
  | t :: r' =>
    let f := 'X_i * t == 1 /\ t * 'X_i == 1 in
     'forall 'X_i, (f \/ 'X_i == t /\ ~ ('exists 'X_i,  f)) ==> loop r' i.+1
  end%T
  in loop r1 m.

(* Transformation of a formula in the theory of rings with units into an *)
(* equivalent formula in the sub-theory of rings.                        *)
Fixpoint to_rform f :=
  match f with
  | Bool b => f
  | t1 == t2 => eq0_rform (t1 - t2)
  | Unit t1 => eq0_rform (t1 * t1^-1 - 1)
  | f1 /\ f2 => to_rform f1 /\ to_rform f2
  | f1 \/ f2 =>  to_rform f1 \/ to_rform f2
  | f1 ==> f2 => to_rform f1 ==> to_rform f2
  | ~ f1 => ~ to_rform f1
  | ('exists 'X_i, f1) => 'exists 'X_i, to_rform f1
  | ('forall 'X_i, f1) => 'forall 'X_i, to_rform f1
  end%T.

(* The transformation gives a ring formula. *)
Lemma to_rform_rformula f : rformula (to_rform f).
Proof.
suffices eq0_ring t1: rformula (eq0_rform t1) by elim: f => //= => f1 ->.
rewrite /eq0_rform; move: (ub_var t1) => m; set tr := _ m.
suffices: all rterm (tr.1 :: tr.2).
  case: tr => {}t1 r /= /andP[t1_r].
  by elim: r m => [|t r IHr] m; rewrite /= ?andbT // => /andP[->]; apply: IHr.
have: all rterm [::] by [].
rewrite {}/tr; elim: t1 [::] => //=.
- move=> t1 IHt1 t2 IHt2 r.
  move/IHt1; case: to_rterm => {r IHt1}t1 r /= /andP[t1_r].
  move/IHt2; case: to_rterm => {r IHt2}t2 r /= /andP[t2_r].
  by rewrite t1_r t2_r.
- by move=> t1 IHt1 r /IHt1; case: to_rterm.
- by move=> t1 IHt1 n r /IHt1; case: to_rterm.
- move=> t1 IHt1 t2 IHt2 r.
  move/IHt1; case: to_rterm => {r IHt1}t1 r /= /andP[t1_r].
  move/IHt2; case: to_rterm => {r IHt2}t2 r /= /andP[t2_r].
  by rewrite t1_r t2_r.
- move=> t1 IHt1 r.
  by move/IHt1; case: to_rterm => {r IHt1}t1 r /=; rewrite all_rcons.
- by move=> t1 IHt1 n r /IHt1; case: to_rterm.
Qed.

(* Correctness of the transformation. *)
Lemma to_rformP e f : holds e (to_rform f) <-> holds e f.
Proof.
suffices{e f} equal0_equiv e t1 t2:
  holds e (eq0_rform (t1 - t2)) <-> (eval e t1 == eval e t2).
- elim: f e => /=; try tauto.
  + move=> t1 t2 e.
    by split; [move/equal0_equiv/eqP | move/eqP/equal0_equiv].
  + by move=> t1 e; rewrite unitrE; apply: equal0_equiv.
  + by move=> f1 IHf1 f2 IHf2 e; move: (IHf1 e) (IHf2 e); tauto.
  + by move=> f1 IHf1 f2 IHf2 e; move: (IHf1 e) (IHf2 e); tauto.
  + by move=> f1 IHf1 f2 IHf2 e; move: (IHf1 e) (IHf2 e); tauto.
  + by move=> f1 IHf1 e; move: (IHf1 e); tauto.
  + by move=> n f1 IHf1 e; split=> [] [x] /IHf1; exists x.
  + by move=> n f1 IHf1 e; split=> Hx x; apply/IHf1.
rewrite -(add0r (eval e t2)) -(can2_eq (subrK _) (addrK _)).
rewrite -/(eval e (t1 - t2)); move: (t1 - t2)%T => {t1 t2} t.
have sub_var_tsubst s t0: s.1 >= ub_var t0 -> tsubst t0 s = t0.
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
  if r is u :: r' then ub_var u <= m /\ ub_sub m.+1 r' else true.
suffices{t} rsub_to_r t r0 m: m >= ub_var t -> ub_sub m r0 ->
  let: (t', r) := to_rterm t r0 m in
  [/\ take (size r0) r = r0,
      ub_var t' <= m + size r, ub_sub m r & rsub t' m r = t].
- have:= rsub_to_r t [::] _ (leqnn _); rewrite /eq0_rform.
  case: (to_rterm _ _ _) => [t1' r1] [//|_ _ ub_r1 def_t].
  rewrite -{2}def_t {def_t}.
  elim: r1 (ub_var t) e ub_r1 => [|u r1 IHr1] m e /= => [_|[ub_u ub_r1]].
    by split=> /eqP.
  rewrite eval_tsubst /=; set y := eval e u; split=> t_eq0.
    apply/IHr1=> //; apply: t_eq0.
    rewrite nth_set_nth /= eqxx -(eval_tsubst e u (m, Const _)).
    rewrite sub_var_tsubst //= -/y.
    case Uy: (y \in unit); [left | right]; first by rewrite mulVr ?divrr.
    split=> [|[z]]; first by rewrite invr_out ?Uy.
    rewrite nth_set_nth /= eqxx.
    rewrite -!(eval_tsubst _ _ (m, Const _)) !sub_var_tsubst // -/y => yz1.
    by case/unitrP: Uy; exists z.
  move=> x def_x; apply/IHr1=> //; suff ->: x = y^-1 by []; move: def_x.
  rewrite nth_set_nth /= eqxx -(eval_tsubst e u (m, Const _)).
  rewrite sub_var_tsubst //= -/y; case=> [[xy1 yx1] | [xy nUy]].
    by rewrite -[y^-1]mul1r -[1]xy1 mulrK //; apply/unitrP; exists x.
  rewrite invr_out //; apply/unitrP=> [[z yz1]]; case: nUy; exists z.
  rewrite nth_set_nth /= eqxx -!(eval_tsubst _ _ (m, _%:T)%T).
  by rewrite !sub_var_tsubst.
have rsub_id r t0 n: ub_var t0 <= n -> rsub t0 n r = t0.
  by elim: r n => //= t1 r IHr n let0n; rewrite IHr ?sub_var_tsubst ?leqW.
have rsub_acc r s t1 m1:
  ub_var t1 <= m1 + size r -> rsub t1 m1 (r ++ s) = rsub t1 m1 r.
  elim: r t1 m1 => [|t1 r IHr] t2 m1 /=; first by rewrite addn0; apply: rsub_id.
  by move=> letmr; rewrite IHr ?addSnnS.
elim: t r0 m => /=; try do [
  by move=> n r m hlt hub; rewrite take_size (ltn_addr _ hlt) rsub_id
| by move=> n r m hlt hub; rewrite leq0n take_size rsub_id
| move=> t1 IHt1 t2 IHt2 r m; rewrite geq_max; case/andP=> hub1 hub2 hmr;
  case: to_rterm {hub1 hmr}(IHt1 r m hub1 hmr) => t1' r1;
  case=> htake1 hub1' hsub1 <-;
  case: to_rterm {IHt2 hub2 hsub1}(IHt2 r1 m hub2 hsub1) => t2' r2 /=;
  rewrite geq_max; case=> htake2 -> hsub2 /= <-;
  rewrite -{1 2}(cat_take_drop (size r1) r2) htake2; set r3 := drop _ _;
  rewrite size_cat addnA (leq_trans _ (leq_addr _ _)) //;
  split=> {hsub2}//;
   first by [rewrite takel_cat // -htake1 size_take geq_min leqnn orbT];
  rewrite -(rsub_acc r1 r3 t1') {hub1'}// -{htake1}htake2 {r3}cat_take_drop;
  by elim: r2 m => //= u r2 IHr2 m; rewrite IHr2
| do [ move=> t1 IHt1 r m; do 2!move=> /IHt1{}IHt1
     | move=> t1 IHt1 n r m; do 2!move=> /IHt1{}IHt1];
  case: to_rterm IHt1 => t1' r1 [-> -> hsub1 <-]; split=> {hsub1}//;
  by elim: r1 m => //= u r1 IHr1 m; rewrite IHr1].
move=> t1 IH r m letm /IH {IH} /(_ letm) {letm}.
case: to_rterm => t1' r1 /= [def_r ub_t1' ub_r1 <-].
rewrite size_rcons addnS leqnn -{1}cats1 takel_cat ?def_r; last first.
  by rewrite -def_r size_take geq_min leqnn orbT.
elim: r1 m ub_r1 ub_t1' {def_r} => /= [|u r1 IHr1] m => [_|[->]].
  by rewrite addn0 eqxx.
by rewrite -addSnnS => /IHr1 IH /IH[_ _ ub_r1 ->].
Qed.

(* Boolean test selecting formulas which describe a constructible set, *)
(* i.e. formulas without quantifiers.                                  *)

(* The quantifier elimination check. *)
Fixpoint qf_form (f : formula R) :=
  match f with
  | Bool _ | _ == _ | Unit _ => true
  | f1 /\ f2 | f1 \/ f2 | f1 ==> f2 => qf_form f1 && qf_form f2
  | ~ f1 => qf_form f1
  | _ => false
  end%T.

(* Boolean holds predicate for quantifier free formulas *)
Definition qf_eval e := fix loop (f : formula R) : bool :=
  match f with
  | Bool b => b
  | t1 == t2 => (eval e t1 == eval e t2)%bool
  | Unit t1 => eval e t1 \in unit
  | f1 /\ f2 => loop f1 && loop f2
  | f1 \/ f2 => loop f1 || loop f2
  | f1 ==> f2 => (loop f1 ==> loop f2)%bool
  | ~ f1 => ~~ loop f1
  |_ => false
  end%T.

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

Implicit Type bc : seq (term R) * seq (term R).

(* Quantifier-free formula are normalized into DNF. A DNF is *)
(* represented by the type seq (seq (term R) * seq (term R)), where we *)
(* separate positive and negative literals *)

(* DNF preserving conjunction *)
Definition and_dnf bcs1 bcs2 :=
  \big[cat/nil]_(bc1 <- bcs1)
     map (fun bc2 => (bc1.1 ++ bc2.1, bc1.2 ++ bc2.2)) bcs2.

(* Computes a DNF from a qf ring formula *)
Fixpoint qf_to_dnf (f : formula R) (neg : bool) {struct f} :=
  match f with
  | Bool b => if b (+) neg then [:: ([::], [::])] else [::]
  | t1 == t2 => [:: if neg then ([::], [:: t1 - t2]) else ([:: t1 - t2], [::])]
  | f1 /\ f2 => (if neg then cat else and_dnf) [rec f1, neg] [rec f2, neg]
  | f1 \/ f2 => (if neg then and_dnf else cat) [rec f1, neg] [rec f2, neg]
  | f1 ==> f2 => (if neg then and_dnf else cat) [rec f1, ~~ neg] [rec f2, neg]
  | ~ f1 => [rec f1, ~~ neg]
  | _ =>  if neg then [:: ([::], [::])] else [::]
  end%T where "[ 'rec' f , neg ]" := (qf_to_dnf f neg).

(* Conversely, transforms a DNF into a formula *)
Definition dnf_to_form :=
  let pos_lit t := And (t == 0) in let neg_lit t := And (t != 0) in
  let cls bc := Or (foldr pos_lit True bc.1 /\ foldr neg_lit True bc.2) in
  foldr cls False.

(* Catenation of dnf is the Or of formulas *)
Lemma cat_dnfP e bcs1 bcs2 :
  qf_eval e (dnf_to_form (bcs1 ++ bcs2))
    = qf_eval e (dnf_to_form bcs1 \/ dnf_to_form bcs2).
Proof.
by elim: bcs1 => //= bc1 bcs1 IH1; rewrite -orbA; congr orb; rewrite IH1.
Qed.

(* and_dnf is the And of formulas *)
Lemma and_dnfP e bcs1 bcs2 :
  qf_eval e (dnf_to_form (and_dnf bcs1 bcs2))
   = qf_eval e (dnf_to_form bcs1 /\ dnf_to_form bcs2).
Proof.
elim: bcs1 => [|bc1 bcs1 IH1] /=; first by rewrite /and_dnf big_nil.
rewrite /and_dnf big_cons -/(and_dnf bcs1 bcs2) cat_dnfP  /=.
rewrite {}IH1 /= andb_orl; congr orb.
elim: bcs2 bc1 {bcs1} => [|bc2 bcs2 IH] bc1 /=; first by rewrite andbF.
rewrite {}IH /= andb_orr; congr orb => {bcs2}.
suffices aux (l1 l2 : seq (term R)) g : let redg := foldr (And \o g) True in
  qf_eval e (redg (l1 ++ l2)) = qf_eval e (redg l1 /\ redg l2)%T.
+ by rewrite 2!aux /= 2!andbA -andbA -andbCA andbA andbCA andbA.
by elim: l1 => [| t1 l1 IHl1] //=; rewrite -andbA IHl1.
Qed.

Lemma qf_to_dnfP e :
  let qev f b := qf_eval e (dnf_to_form (qf_to_dnf f b)) in
  forall f, qf_form f && rformula f -> qev f false = qf_eval e f.
Proof.
move=> qev; have qevT f: qev f true = ~~ qev f false.
  rewrite {}/qev; elim: f => //=; do [by case | move=> f1 IH1 f2 IH2 | ].
  - by move=> t1 t2; rewrite !andbT !orbF.
  - by rewrite and_dnfP cat_dnfP negb_and -IH1 -IH2.
  - by rewrite and_dnfP cat_dnfP negb_or -IH1 -IH2.
  - by rewrite and_dnfP cat_dnfP /= negb_or IH1 -IH2 negbK.
  by move=> t1 ->; rewrite negbK.
rewrite /qev; elim=> //=; first by case.
- by move=> t1 t2 _; rewrite subr_eq0 !andbT orbF.
- move=> f1 IH1 f2 IH2; rewrite andbCA -andbA andbCA andbA; case/andP.
  by rewrite and_dnfP /= => /IH1-> /IH2->.
- move=> f1 IH1 f2 IH2; rewrite andbCA -andbA andbCA andbA; case/andP.
  by rewrite cat_dnfP /= => /IH1-> => /IH2->.
- move=> f1 IH1 f2 IH2; rewrite andbCA -andbA andbCA andbA; case/andP.
  by rewrite cat_dnfP /= [qf_eval _ _]qevT -implybE => /IH1 <- /IH2->.
by move=> f1 IH1 /IH1 <-; rewrite -qevT.
Qed.

Lemma dnf_to_form_qf bcs : qf_form (dnf_to_form bcs).
Proof.
by elim: bcs => //= [[clT clF] _ ->] /=; elim: clT => //=; elim: clF.
Qed.

Definition dnf_rterm cl := all rterm cl.1 && all rterm cl.2.

Lemma qf_to_dnf_rterm f b : rformula f -> all dnf_rterm (qf_to_dnf f b).
Proof.
set ok := all dnf_rterm.
have cat_ok bcs1 bcs2: ok bcs1 -> ok bcs2 -> ok (bcs1 ++ bcs2).
  by move=> ok1 ok2; rewrite [ok _]all_cat; apply/andP.
have and_ok bcs1 bcs2: ok bcs1 -> ok bcs2 -> ok (and_dnf bcs1 bcs2).
  rewrite /and_dnf unlock; elim: bcs1 => //= cl1 bcs1 IH1; rewrite -andbA.
  case/and3P=> ok11 ok12 ok1 ok2; rewrite cat_ok ?{}IH1 {bcs1 ok1}//.
  elim: bcs2 ok2 => //= cl2 bcs2 IH2 /andP[ok2 /IH2->].
  by rewrite /dnf_rterm !all_cat ok11 ok12 /= !andbT.
elim: f b => //=; [ by do 2!case | | | | | by auto | | ];
  try by repeat case/andP || intro; case: ifP; auto.
by rewrite /dnf_rterm => ?? [] /= ->.
Qed.

Lemma dnf_to_rform bcs : rformula (dnf_to_form bcs) = all dnf_rterm bcs.
Proof.
elim: bcs => //= [[cl1 cl2] bcs ->]; rewrite {2}/dnf_rterm /=; congr (_ && _).
by (congr andb; [elim: cl1 | elim: cl2]) => //= t cl ->; rewrite andbT.
Qed.

Section If.

Variables (pred_f then_f else_f : formula R).

Definition If := (pred_f /\ then_f \/ ~ pred_f /\ else_f)%T.

Lemma If_form_qf :
  qf_form pred_f -> qf_form then_f -> qf_form else_f -> qf_form If.
Proof. by move=> /= -> -> ->. Qed.

Lemma If_form_rf :
  rformula pred_f -> rformula then_f -> rformula else_f -> rformula If.
Proof. by move=> /= -> -> ->. Qed.

Lemma eval_If e :
  let ev := qf_eval e in ev If = (if ev pred_f then ev then_f else ev else_f).
Proof. by rewrite /=; case: ifP => _; rewrite ?orbF. Qed.

End If.

Section Pick.

Variables (I : finType) (pred_f then_f : I -> formula R) (else_f : formula R).

Definition Pick :=
  \big[Or/False]_(p : {ffun pred I})
    ((\big[And/True]_i (if p i then pred_f i else ~ pred_f i))
    /\ (if pick p is Some i then then_f i else else_f))%T.

Lemma Pick_form_qf :
   (forall i, qf_form (pred_f i)) ->
   (forall i, qf_form (then_f i)) ->
    qf_form else_f ->
  qf_form Pick.
Proof.
move=> qfp qft qfe; have mA := (big_morph qf_form) true andb.
rewrite mA // big1 //= => p _.
rewrite mA // big1 => [|i _]; first by case: pick.
by rewrite fun_if if_same /= qfp.
Qed.

Lemma eval_Pick e (qev := qf_eval e) :
  let P i := qev (pred_f i) in
  qev Pick = (if pick P is Some i then qev (then_f i) else qev else_f).
Proof.
move=> P; rewrite ((big_morph qev) false orb) //= big_orE /=.
apply/existsP/idP=> [[p] | true_at_P].
  rewrite ((big_morph qev) true andb) //= big_andE /=.
  case/andP=> /forallP-eq_p_P.
  rewrite (@eq_pick _ _ P) => [|i]; first by case: pick.
  by move/(_ i): eq_p_P => /=; case: (p i) => //= /negPf.
exists [ffun i => P i] => /=; apply/andP; split.
  rewrite ((big_morph qev) true andb) //= big_andE /=.
  by apply/forallP=> i; rewrite /= ffunE; case Pi: (P i) => //=; apply: negbT.
rewrite (@eq_pick _ _ P) => [|i]; first by case: pick true_at_P.
by rewrite ffunE.
Qed.

End Pick.

Section MultiQuant.

Variable f : formula R.
Implicit Types (I : seq nat) (e : seq R).

Lemma foldExistsP I e :
  (exists2 e', {in [predC I], same_env e e'} & holds e' f)
    <-> holds e (foldr Exists f I).
Proof.
elim: I e => /= [|i I IHi] e.
  by split=> [[e' eq_e] |]; [apply: eq_holds => i; rewrite eq_e | exists e].
split=> [[e' eq_e f_e'] | [x]]; last set e_x := set_nth 0 e i x.
  exists e'`_i; apply/IHi; exists e' => // j.
  by have:= eq_e j; rewrite nth_set_nth /= !inE; case: eqP => // ->.
case/IHi=> e' eq_e f_e'; exists e' => // j.
by have:= eq_e j; rewrite nth_set_nth /= !inE; case: eqP.
Qed.

Lemma foldForallP I e :
  (forall e', {in [predC I], same_env e e'} -> holds e' f)
    <-> holds e (foldr Forall f I).
Proof.
elim: I e => /= [|i I IHi] e.
  by split=> [|f_e e' eq_e]; [apply | apply: eq_holds f_e => i; rewrite eq_e].
split=> [f_e' x | f_e e' eq_e]; first set e_x := set_nth 0 e i x.
  apply/IHi=> e' eq_e; apply: f_e' => j.
  by have:= eq_e j; rewrite nth_set_nth /= !inE; case: eqP.
move/IHi: (f_e e'`_i); apply=> j.
by have:= eq_e j; rewrite nth_set_nth /= !inE; case: eqP => // ->.
Qed.

End MultiQuant.

End EvalTerm.

Prenex Implicits dnf_rterm.

Definition decidable_field_axiom (R : unitRingType)
    (s : seq R -> pred (formula R)) :=
  forall e f, reflect (holds e f) (s e f).

HB.mixin Record Field_isDecField R & UnitRing R := {
  sat : seq R -> pred (formula R);
  satP : decidable_field_axiom sat;
}.

#[mathcomp(axiom="decidable_field_axiom"), short(type="decFieldType")]
HB.structure Definition DecidableField := { F of Field F & Field_isDecField F }.

Module DecFieldExports.
Bind Scope ring_scope with DecidableField.sort.
End DecFieldExports.
HB.export DecFieldExports.

#[export] HB.instance Definition _ (F : decFieldType) := DecidableField.on F^o.

Section DecidableFieldTheory.

Variable F : decFieldType.
Implicit Type f : formula F.

Fact sol_subproof n f :
  reflect (exists s, (size s == n) && sat s f)
          (sat [::] (foldr Exists f (iota 0 n))).
Proof.
apply: (iffP (satP _ _)) => [|[s]]; last first.
  case/andP=> /eqP sz_s /satP f_s; apply/foldExistsP.
  exists s => // i; rewrite !inE mem_iota -leqNgt add0n => le_n_i.
  by rewrite !nth_default ?sz_s.
case/foldExistsP=> e e0 f_e; set s := take n (set_nth 0 e n 0).
have sz_s: size s = n by rewrite size_take size_set_nth leq_max leqnn.
exists s; rewrite sz_s eqxx; apply/satP; apply: eq_holds f_e => i.
case: (leqP n i) => [le_n_i | lt_i_n].
  by rewrite -e0 ?nth_default ?sz_s // !inE mem_iota -leqNgt.
by rewrite nth_take // nth_set_nth /= eq_sym eqn_leq leqNgt lt_i_n.
Qed.

Definition sol n f :=
  if sol_subproof n f is ReflectT sP then xchoose sP else nseq n 0.

Lemma size_sol n f : size (sol n f) = n.
Proof.
rewrite /sol; case: sol_subproof => [sP | _]; last exact: size_nseq.
by case/andP: (xchooseP sP) => /eqP.
Qed.

Lemma solP n f : reflect (exists2 s, size s = n & holds s f) (sat (sol n f) f).
Proof.
rewrite /sol; case: sol_subproof => [sP | sPn].
  case/andP: (xchooseP sP) => _ ->; left.
  by case: sP => s; case/andP; move/eqP=> <-; move/satP; exists s.
apply: (iffP (satP _ _)); first by exists (nseq n 0); rewrite ?size_nseq.
by case=> s sz_s; move/satP=> f_s; case: sPn; exists s; rewrite sz_s eqxx.
Qed.

Lemma eq_sat f1 f2 :
  (forall e, holds e f1 <-> holds e f2) -> sat^~ f1 =1 sat^~ f2.
Proof. by move=> eqf12 e; apply/satP/satP; case: (eqf12 e). Qed.

Lemma eq_sol f1 f2 :
  (forall e, holds e f1 <-> holds e f2) -> sol^~ f1 =1 sol^~ f2.
Proof.
rewrite /sol => /eq_sat eqf12 n.
do 2![case: sol_subproof] => //= [f1s f2s | ns1 [s f2s] | [s f1s] []].
- by apply: eq_xchoose => s; rewrite eqf12.
- by case: ns1; exists s; rewrite -eqf12.
by exists s; rewrite eqf12.
Qed.

End DecidableFieldTheory.

Arguments satP {F e f} : rename.
Arguments solP {F n f} : rename.

Section QE_Mixin.

Variable F : Field.type.
Implicit Type f : formula F.

Variable proj : nat -> seq (term F) * seq (term F) -> formula F.
(* proj is the elimination of a single existential quantifier *)

(* The elimination projector is well_formed. *)
Definition wf_QE_proj :=
  forall i bc (bc_i := proj i bc),
  dnf_rterm bc -> qf_form bc_i && rformula bc_i.

(* The elimination projector is valid *)
Definition valid_QE_proj :=
  forall i bc (ex_i_bc := ('exists 'X_i, dnf_to_form [:: bc])%T) e,
  dnf_rterm bc -> reflect (holds e ex_i_bc) (qf_eval e (proj i bc)).

Hypotheses (wf_proj : wf_QE_proj) (ok_proj : valid_QE_proj).

Let elim_aux f n := foldr Or False (map (proj n) (qf_to_dnf f false)).

Fixpoint quantifier_elim f :=
  match f with
  | f1 /\ f2 => (quantifier_elim f1) /\ (quantifier_elim f2)
  | f1 \/ f2 => (quantifier_elim f1) \/ (quantifier_elim f2)
  | f1 ==> f2 => (~ quantifier_elim f1) \/ (quantifier_elim f2)
  | ~ f => ~ quantifier_elim f
  | ('exists 'X_n, f) => elim_aux (quantifier_elim f) n
  | ('forall 'X_n, f) => ~ elim_aux (~ quantifier_elim f) n
  | _ => f
  end%T.

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
  all (@qf_form F) fs && all (@rformula F) fs -> qf_form ofs && rformula ofs.
- apply: or_wf.
  suffices map_proj_wf bcs: let mbcs := map (proj n) bcs in
    all dnf_rterm bcs -> all (@qf_form _) mbcs && all (@rformula _) mbcs.
    by apply/map_proj_wf/qf_to_dnf_rterm.
  elim: bcs => [|bc bcs ihb] bcsr //= /andP[rbc rbcs].
  by rewrite andbAC andbA wf_proj //= andbC ihb.
elim: fs => //= g gs ihg; rewrite -andbA => /and4P[-> qgs -> rgs] /=.
by apply: ihg; rewrite qgs rgs.
Qed.

Lemma quantifier_elim_rformP e f :
  rformula f -> reflect (holds e f) (qf_eval e (quantifier_elim f)).
Proof.
pose rc e n f := exists x, qf_eval (set_nth 0 e n x) f.
have auxP f0 e0 n0: qf_form f0 && rformula f0 ->
  reflect (rc e0 n0 f0) (qf_eval e0 (elim_aux f0 n0)).
+ rewrite /elim_aux => cf; set bcs := qf_to_dnf f0 false.
  apply: (@iffP (rc e0 n0 (dnf_to_form bcs))); last first.
  - by case=> x; rewrite -qf_to_dnfP //; exists x.
  - by case=> x; rewrite qf_to_dnfP //; exists x.
  have: all dnf_rterm bcs by case/andP: cf => _; apply: qf_to_dnf_rterm.
  elim: {f0 cf}bcs => [|bc bcs IHbcs] /=; first by right; case.
  case/andP=> r_bc /IHbcs {IHbcs}bcsP.
  have f_qf := dnf_to_form_qf [:: bc].
  case: ok_proj => //= [ex_x|no_x].
    left; case: ex_x => x /(qf_evalP _ f_qf); rewrite /= orbF => bc_x.
    by exists x; rewrite /= bc_x.
  apply: (iffP bcsP) => [[x bcs_x] | [x]] /=.
    by exists x; rewrite /= bcs_x orbT.
  case/orP => [bc_x|]; last by exists x.
  by case: no_x; exists x; apply/(qf_evalP _ f_qf); rewrite /= bc_x.
elim: f e => //.
- by move=> b e _; apply: idP.
- by move=> t1 t2 e _; apply: eqP.
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

Lemma proj_satP : DecidableField.axiom proj_sat.
Proof.
move=> e f; have fP := quantifier_elim_rformP e (to_rform_rformula f).
by apply: (iffP fP); move/to_rformP.
Qed.

End QE_Mixin.

HB.factory Record Field_QE_isDecField F & Field F := {
  proj : nat -> seq (term F) * seq (term F) -> formula F;
  wf_proj : wf_QE_proj proj;
  ok_proj : valid_QE_proj proj;
}.
HB.builders Context F & Field_QE_isDecField F.

HB.instance Definition qe_is_def_field : Field_isDecField F :=
  Field_isDecField.Build F (proj_satP wf_proj ok_proj).
HB.end.

(* Axiom == all non-constant monic polynomials have a root *)
Definition closed_field_axiom (R : pzRingType) :=
  forall n (P : nat -> R), n > 0 ->
   exists x : R, x ^+ n = \sum_(i < n) P i * (x ^+ i).

HB.mixin Record DecField_isAlgClosed F & DecidableField F := {
  solve_monicpoly : closed_field_axiom F;
}.

#[mathcomp(axiom="closed_field_axiom"), short(type="closedFieldType")]
HB.structure Definition ClosedField :=
  { F of DecidableField F & DecField_isAlgClosed F }.

Module ClosedFieldExports.
Bind Scope ring_scope with ClosedField.sort.
End ClosedFieldExports.
HB.export ClosedFieldExports.

#[export] HB.instance Definition _ (F : closedFieldType) := ClosedField.on F^o.

Section ClosedFieldTheory.

Variable F : closedFieldType.

Lemma imaginary_exists : {i : F | i ^+ 2 = -1}.
Proof.
have /sig_eqW[i Di2] := @solve_monicpoly F 2 (nth 0 [:: -1]) isT.
by exists i; rewrite Di2 !big_ord_recl big_ord0 mul0r mulr1 !addr0.
Qed.

End ClosedFieldTheory.

Module Theory.

Export GRing.Theory.

Definition eq_eval := eq_eval.
Definition eval_tsubst := eval_tsubst.
Definition eq_holds := eq_holds.
Definition holds_fsubst := holds_fsubst.
Definition satP {F e f} := @satP F e f.
Definition eq_sat := eq_sat.
Definition solP {F n f} := @solP F n f.
Definition eq_sol := eq_sol.
Definition size_sol := size_sol.
Definition solve_monicpoly := @solve_monicpoly.
Definition imaginary_exists := imaginary_exists.

End Theory.

Module AllExports. HB.reexport. End AllExports.

End GRing.

Export AllExports.

Bind Scope term_scope with term.
Bind Scope term_scope with formula.

Notation "''X_' i" := (Var _ i) : term_scope.
Notation "n %:R" := (NatConst _ n) : term_scope.
Notation "0" := 0%:R%T : term_scope.
Notation "1" := 1%:R%T : term_scope.
Notation "x %:T" := (Const x) : term_scope.
Infix "+" := Add : term_scope.
Notation "- t" := (Opp t) : term_scope.
Notation "t - u" := (Add t (- u)) : term_scope.
Infix "*" := Mul : term_scope.
Infix "*+" := NatMul : term_scope.
Notation "t ^-1" := (Inv t) : term_scope.
Notation "t / u" := (Mul t u^-1) : term_scope.
Infix "^+" := Exp : term_scope.
Infix "==" := Equal : term_scope.
Notation "x != y" := (GRing.Not (x == y)) : term_scope.
Infix "/\" := And : term_scope.
Infix "\/" := Or : term_scope.
Infix "==>" := Implies : term_scope.
Notation "~ f" := (Not f) : term_scope.
Notation "''exists' ''X_' i , f" := (Exists i f) : term_scope.
Notation "''forall' ''X_' i , f" := (Forall i f) : term_scope.

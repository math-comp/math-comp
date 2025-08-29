(* Distributed under the terms of CeCILL-B.                                  *)
From elpi Require Import derive.std param2.
From Corelib Require Import BinNums.
From mathcomp Require Import PosDef NatDef.
From Corelib Require Import IntDef.
From mathcomp Require Import RatDef.
From mathcomp Require Import micromega_formula micromega_witness.
From mathcomp Require Import micromega_tactics micromega_checker micromega_eval.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From mathcomp Require Import seq order ssralg ssrnum ssrint rat binnums ring.
From mathcomp.algebra Extra Dependency "ring.elpi" as ring.
From mathcomp.algebra Extra Dependency "lra.elpi" as lra.

(******************************************************************************)
(* This file provides the lra, nra, psatz and psatz <n> tactics.              *)
(*                                                                            *)
(* These tactics, based on the micromega plugin distributed with Rocq provide:*)
(*          lra == a decision procedure for Linear Real Arithmetic            *)
(*          nra == a *semi* decision procedure for Nonlinear Real Arithmetic  *)
(*    psatz [n] == a *semi* decision procedure for nonlinear real arithmetic  *)
(*                 using the PositivstellenSATZ                               *)
(*                 This can use the external CSDP numerical solver.           *)
(*                 Higher integer n may find more proofs, at an higher cost.  *)
(* These tactics work on any realDomainType (with integer coefficients)       *)
(* or realFieldType (with rational coefficients) and handle additive morphisms*)
(* {additive _ -> _} and ring morphisms {rmorphism _ -> _}.                   *)
(*                                                                            *)
(* See file test-suite/test_lra.v for examples of use.                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
#[local] Set Uniform Inductive Parameters.

Import Order.Theory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

Module Import Internals.
Export Internals.

Section PevalSemiRing.
Variable C : pzSemiRingType.
Variable R : comPzSemiRingType.
Variable R_of_C : {rmorphism C -> R}.

Implicit Type l : seq R.

#[local] Notation env_nth := (env_nth 0).
#[local] Notation Peval := (Peval
  +%R *%R N.to_nat (@GRing.exp R) R_of_C (@env_jump R) env_nth).
#[local] Notation Psquare := (Psquare 0 1 +%R *%R eq_op).

Lemma Peval_square l P : Peval l (Psquare P) = Peval l P ^+ 2.
Proof.
elim: P l => [c | j Q IH | P IHP i Q IHQ] l; rewrite /= ?rmorphM ?expr2 ?IH//.
rewrite Peval_mkPX PevalD Peval_mkPX PevalM Peval_mkPinj PevalMC IHP.
rewrite IHQ /= rmorph0 addr0 [in LHS]mulrDl -mulrA mulrACA.
set p := Peval l P * env_nth 1 l ^+ Pos.to_nat i; set q := Peval _ Q.
rewrite rmorphD rmorph1 [X in _ + X + _]mulrAC -/p -[1 + 1]/2.
by rewrite -!expr2 mulrA mulr_natr -sqrrD.
Qed.

End PevalSemiRing.

Section CNF.
Variable Term : Type.
Variable Annot : Type.

Variable eval : Term -> bool.

Variable is_tauto : Term -> Term -> bool.
Hypothesis is_tautoT : forall t t', is_tauto t t' -> eval t || eval t'.

#[local] Notation clause := (clause Term Annot).
#[local] Notation cnf := (cnf Term Annot).
#[local] Notation cnf_tt := (cnf_tt Term Annot).
#[local] Notation cnf_ff := (cnf_ff Term Annot).
#[local] Notation add_term := (add_term is_tauto).
#[local] Notation or_clause := (or_clause is_tauto).
#[local] Notation or_clause_cnf := (or_clause_cnf is_tauto).
#[local] Notation or_cnf_aux := (or_cnf_aux is_tauto).
#[local] Notation or_cnf := (or_cnf is_tauto).

Definition eval_clause : clause -> bool := has (fun t => eval t.1).

Definition eval_cnf : cnf -> bool := all eval_clause.

Lemma eval_cnf_tt : eval_cnf cnf_tt. Proof. by []. Qed.

Lemma eval_cnf_ff : eval_cnf cnf_ff = false. Proof. by []. Qed.

Lemma is_cnf_ttT f : is_cnf_tt f -> f = cnf_tt. Proof. by case: f. Qed.

Lemma is_cnf_ffT f : is_cnf_ff f -> f = cnf_ff.
Proof. by case: f => [//| [|//] []]. Qed.

Lemma add_termP t cl :
  match add_term t cl with
  | None => eval t.1 || eval_clause cl
  | Some cl' => eval_clause cl' = eval t.1 || eval_clause cl
  end.
Proof.
elim: cl t => [| t' cl IH] t /=.
  by case: ifP => [/is_tautoT/[!orbb]->//|_].
case: ifP => [|_]; first by rewrite orbA => /is_tautoT->.
by case: add_term (IH t) => [?|] {}IH; rewrite /= orbCA IH ?orbT.
Qed.

Lemma or_clauseP cl1 cl2 :
  match or_clause cl1 cl2 with
  | None => eval_clause cl1 || eval_clause cl2
  | Some cl' => eval_clause cl' = eval_clause cl1 || eval_clause cl2
  end.
Proof.
elim: cl1 cl2 => [//| t cl IH] cl2 /=.
case: add_term (add_termP t cl2) => [cl'|]; last by rewrite orbAC => ->.
rewrite [eval t.1 || eval_clause cl]orbC -orbA.
by case: or_clause (IH cl') => [_->->|/[swap]->].
Qed.

Lemma eval_or_clause_cnf cl f :
  eval_cnf (or_clause_cnf cl f) = eval_clause cl || eval_cnf f.
Proof.
case: cl => [//| t cl].
rewrite /or_clause_cnf; move: (t :: cl) => {t}cl; set orcl := fun acc cl => _.
have orclP acc cl' : eval_cnf (orcl acc cl')
    = (eval_clause cl || eval_clause cl') && eval_cnf acc.
  rewrite /orcl; case: or_clause (or_clauseP cl cl') => [cl''/=->//|].
  by move=> /orP[]->//=; rewrite orbT.
rewrite -[RHS]andbT -[true]/(eval_cnf [::]).
have: eval_cnf [::] = eval_clause cl || eval_cnf [::] by rewrite orbT.
elim: f [::] => [|cl' f IH] acc clacc /=; first by rewrite orbT.
rewrite IH; last by rewrite orclP clacc -!orb_andr orbA orbb.
by rewrite orclP clacc -!orb_andr andbCA andbA.
Qed.

Lemma eval_rev_append f1 f2 :
  eval_cnf (ListDef.rev_append f1 f2) = eval_cnf f1 && eval_cnf f2.
Proof. by elim: f1 f2 => [//|cl f1 IH] f2 /=; rewrite IH andbCA andbA. Qed.

Lemma eval_or_cnf_aux f1 f2 :
  eval_cnf (or_cnf_aux f1 f2) = eval_cnf f1 || eval_cnf f2.
Proof.
elim: f1 => [//|cl f1 IH] /=.
by rewrite eval_rev_append IH eval_or_clause_cnf -orb_andl andbC.
Qed.

Lemma eval_or_cnf f1 f2 : eval_cnf (or_cnf f1 f2) = eval_cnf f1 || eval_cnf f2.
Proof.
rewrite /or_cnf.
case: ifP => [/orP[]/is_cnf_ttT->|_]; rewrite ?eval_cnf_tt ?orbT//.
by case: ifP => [/is_cnf_ffT->|_]; rewrite ?eval_cnf_ff ?orbF ?eval_or_cnf_aux.
Qed.

Lemma eval_and_cnf f1 f2 :
  eval_cnf (and_cnf f1 f2) = eval_cnf f1 && eval_cnf f2.
Proof.
rewrite /and_cnf.
case: ifP => [/orP[]/is_cnf_ffT->|_]; rewrite ?eval_cnf_ff ?andbF//.
by case: ifP => [/is_cnf_ttT->|_]; rewrite ?eval_cnf_tt ?andbT ?eval_rev_append.
Qed.

End CNF.

Section FormulaNormalisation.
Variables (R C : realDomainType) (R_of_C : {rmorphism C -> R}).
Hypothesis R_of_C_ge0 : {mono R_of_C : x / 0 <= x}.

Implicit Type pe : PExpr C.
Implicit Type l : seq R.

#[local] Notation Peval := (Peval
  +%R *%R N.to_nat (@GRing.exp R) R_of_C (@env_jump R) (env_nth 0)).
#[local] Notation PEeval := (PEeval +%R *%R (fun x y : R => x - y) -%R
  N.to_nat (@GRing.exp R) R_of_C (env_nth 0)).
#[local] Notation Feval := (Feval +%R *%R (fun x y : R => x - y) -%R N.to_nat
  (@GRing.exp R) isBool eq_op (cneqb eq_op) <=%R <%R R_of_C (env_nth 0)).
#[local] Notation Pol_of_PExpr := (Pol_of_PExpr
  0 1 +%R *%R (fun x y : C => x - y) -%R eq_op).
#[local] Notation normalise := (normalise
  0 1 +%R *%R (fun x y : C => x - y) -%R eq_op).
#[local] Notation check_inconsistent := (check_inconsistent 0%R eq_op <=%R).
#[local] Notation normalise_aux := (normalise_aux -%R).
#[local] Notation negate_aux := (negate_aux -%R).
#[local] Notation cnf_of_list := (cnf_of_list 0 eq_op <=%R).
#[local] Notation cnf_normalise := (cnf_normalise
  0 1 +%R *%R (fun x y : C => x - y) -%R eq_op <=%R).
#[local] Notation cnf_negate := (cnf_negate
  0 1 +%R *%R (fun x y : C => x - y) -%R eq_op <=%R).

Lemma Peval_Pol_of_PExpr l pe : Peval l (Pol_of_PExpr pe) = PEeval l pe.
Proof.
elim: pe l => [//|i|e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2|e IH|e IH k] l /=.
- exact: Peval_mkX.
- by move: e1 IH1 => [c|i|e1' e2'|e1' e2'|e1' e2'|e|e k] IH1;
    move: e2 IH2 => [c'|i'|e1'' e2''|e1'' e2''|e1'' e2''|e'|e' k'] IH2;
    rewrite ?PevalD ?IH1 ?IH2// PevalB ?IH1 -PevalN IH2// addrC -IH1.
- by rewrite PevalB IH1 IH2.
- by rewrite PevalM IH1 IH2.
- by rewrite PevalN IH.
- by rewrite Peval_pow_N IH.
Qed.

Definition eval_op1 (o : Op1) (x : R) : bool :=
  match o with
  | Equal => x == 0
  | NonEqual => x != 0
  | Strict => 0 < x
  | NonStrict => 0 <= x
  end.

Definition NFeval (env : seq R) (f : NFormula C) : bool :=
  let: (p, op) := f in eval_op1 op (Peval env p).

Lemma NFeval_normalise l f : NFeval l (normalise f) = Feval l f.
Proof.
by case: f => lhs [|||||] rhs /=;
  rewrite PevalB !Peval_Pol_of_PExpr ?subr_eq0 ?subr_ge0 ?subr_gt0.
Qed.

Lemma check_inconsistentT l f : check_inconsistent f -> NFeval l f = false.
Proof.
case: f => -[] // c [] /= + /ltac:(apply: negbTE).
- by apply: contraNN; rewrite !eq_le -oppr_ge0 -rmorphN !R_of_C_ge0 oppr_ge0.
- by move=> /eqP->; rewrite rmorph0 negbK.
- by rewrite -leNgt -!oppr_ge0 -rmorphN R_of_C_ge0.
- by rewrite /cltb andbC -lt_neqAle ltNge R_of_C_ge0.
Qed.

Lemma eval_normalise_aux T (tg : T) l f :
  eval_cnf (fun f => ~~ NFeval l f) [seq [:: (nf, tg)] | nf <- normalise_aux f]
  = NFeval l f.
Proof.
case: f => e [] /=; rewrite andbT !orbF// PevalN.
- by rewrite oppr_gt0 -!leNgt eq_le.
- by rewrite oppr_ge0 -ltNge.
- by rewrite oppr_gt0 -leNgt.
Qed.

Lemma eval_negate_aux T (tg : T) l f :
  eval_cnf (fun f => ~~ NFeval l f) [seq [:: (nf, tg)] | nf <- negate_aux f]
  = ~~ NFeval l f.
Proof.
by case: f => e[]; rewrite /= andbT !orbF// PevalN oppr_gt0 -!leNgt negbK eq_le.
Qed.

Lemma eval_cnf_of_list T (tg : T) l lf :
  eval_cnf (fun f => ~~ NFeval l f) (cnf_of_list lf tg)
  = eval_cnf (fun f => ~~ NFeval l f) [seq [:: (f, tg)] | f <- lf].
Proof.
elim: lf => [//|f lf /= <-]; rewrite orbF.
case: (boolP (check_inconsistent f)) => [/check_inconsistentT->//|_/=].
by rewrite orbF.
Qed.

Lemma eval_cnf_normalise T (tg : T) l f :
  eval_cnf (fun f => ~~ NFeval l f) (cnf_normalise f tg) = Feval l f.
Proof.
rewrite /cnf_normalise/= -NFeval_normalise; set nf := normalise f.
case: (boolP (check_inconsistent nf)) => [/check_inconsistentT->//|_].
by rewrite eval_cnf_of_list eval_normalise_aux.
Qed.

Lemma eval_cnf_negate T (tg : T) l f :
  eval_cnf (fun f => ~~ NFeval l f) (cnf_negate f tg) = ~~ Feval l f.
Proof.
rewrite /cnf_negate/= -NFeval_normalise; set nf := normalise f.
case: (boolP (check_inconsistent nf)) => [/check_inconsistentT->//|_].
by rewrite eval_cnf_of_list eval_negate_aux.
Qed.

End FormulaNormalisation.

Section BFKFeval.
Variables (R : Type) (rO : R) (radd rmul : R -> R -> R) (ropp : R -> R).
Variable (rpow : R -> N -> R).
Variable req rneq rle rlt : R -> R -> bool.
Variable (C : Type) (R_of_C : C -> R).

Definition KFeval k : seq R -> Formula C -> eKind k :=
  let ev k eq neq le lt := Feval radd rmul (fun x y => radd x (ropp y)) ropp
    id rpow k eq neq le lt R_of_C (env_nth rO) in
  if k is isBool then ev isBool req rneq rle rlt else
    ev isProp eq (fun x y => x <> y) (fun x y => rle x y) (fun x y => rlt x y).

Definition BFKFeval (l : seq R) : forall k, BFormula (Formula C) k -> eKind k :=
  BFeval eqb (fun k f => KFeval k l f).

End BFKFeval.

Definition RFeval (R : numDomainType) C (R_of_C : C -> R) := KFeval 0 +%R *%R
  -%R (fun x n => x ^+ N.to_nat n) eq_op (cneqb eq_op) <=%R <%R R_of_C.

Definition RBFeval (R : numDomainType) C (R_of_C : C -> R) := BFKFeval 0 +%R *%R
  -%R (fun x n => x ^+ N.to_nat n) eq_op (cneqb eq_op) <=%R <%R R_of_C.

Lemma RFevalP (R : numDomainType) C (R_of_C : C -> R) l f :
  reflect (RFeval R_of_C isProp l f) (RFeval R_of_C isBool l f).
Proof.
case: f => lhs [] rhs; try exact/idP; first exact/(iffP eqP) => [/eqP|/=->].
by apply/(iffP idP) => [/eqP//|]; apply: contra_notN => /eqP.
Qed.

Section GFormulaNormalisation.
Variables (R C : realDomainType) (R_of_C : {rmorphism C -> R}).
Hypothesis R_of_C_ge0 : {mono R_of_C : x / 0 <= x}.

Implicit Type l : seq R.

#[local] Notation is_tauto := (is_tauto 0 +%R eq_op <=%R).

#[local] Notation cnf_tt := (cnf_tt (NFormula C) unit).
#[local] Notation cnf_ff := (cnf_ff (NFormula C) unit).
#[local] Notation or_cnf := (or_cnf is_tauto).
#[local] Notation and_cnf := (@and_cnf (NFormula C) unit).

#[local] Notation normalise := (cnf_normalise
  0 1 +%R *%R (fun x y : C => x - y) -%R eq_op <=%R).
#[local] Notation negate := (cnf_negate
  0 1 +%R *%R (fun x y : C => x - y) -%R eq_op <=%R).

#[local] Notation cnf_of_GFormula := (@cnf_of_GFormula
  _ _ _ cnf_tt cnf_ff or_cnf and_cnf normalise negate).

Hypothesis is_tautoT : forall l (f g : NFormula C),
  is_tauto f g -> ~~ NFeval R_of_C l f || ~~ NFeval R_of_C l g.

#[local] Notation eval_or_cnf := (eval_or_cnf (is_tautoT _)).

Definition hold pol k : eKind k -> Prop :=
  if k is isProp then if pol then id else not else fun x => x = pol.

Variant is_bool_spec T k (f : BFormula T k) :
      GFormula k -> option bool -> Type :=
  | IsBoolT : is_bool_spec (TT k) (Some true)
  | IsBoolF : is_bool_spec (FF k) (Some false)
  | IsBoolNone : is_bool_spec f None.

Lemma is_boolP T k (f : BFormula T k) : is_bool_spec f f (is_bool f).
Proof.
case: f => {}k => [||x|f u|f g|f g|f|f u g|f g|f] /=; try exact: IsBoolNone.
- exact: IsBoolT.
- exact: IsBoolF.
Qed.

Lemma eval_cnf_of_GFormula l pol k (f : GFormula k) :
    eval_cnf (fun f => ~~ NFeval R_of_C l f) (cnf_of_GFormula pol f) ->
  hold pol (RBFeval R_of_C l f).
Proof.
elim: f pol => {}k /=.
- by move: k => -[] [].
- by move: k => -[] [] //= _.
- by move=> x [] /=.
- move=> f u [].
  + by rewrite eval_cnf_normalise//; case: k => [/RFevalP|//].
  + by rewrite eval_cnf_negate//; case: k => [/RFevalP|/negbTE].
- case: k => /= f IHf g IHg [].
  + by rewrite eval_and_cnf => /andP[/IHf+ /IHg].
  + by rewrite eval_or_cnf => /orP[/IHf|/IHg] ? [].
  + by rewrite eval_and_cnf => /andP[/IHf-> /IHg->].
  + by rewrite eval_or_cnf => /orP[/IHf->//|/IHg->]; rewrite andbF.
- case: k => /= f IHf g IHg [].
  + by rewrite eval_or_cnf => /orP[/IHf|/IHg] ?; [left|right].
  + by rewrite eval_and_cnf => /andP[/IHf nf /IHg ng] [].
  + by rewrite eval_or_cnf => /orP[/IHf->//|/IHg->]; rewrite orbT.
  + by rewrite eval_and_cnf => /andP[/IHf-> /IHg->].
- by case: k => /= f IH [] /IH => [//|?|->//|->//]; apply.
- case: k => /= f IHf u g IHg [].
  + by rewrite eval_or_cnf => /orP[/IHf|/IHg].
  + by rewrite eval_and_cnf => /andP[/IHf ff /IHg]; apply: contra_not; apply.
  + by rewrite eval_or_cnf => /orP[/IHf->|/IHg->]; apply/implyP.
  + by rewrite eval_and_cnf => /andP[/IHf-> /IHg->].
- case: k => /= f IHf g IHg [].
  + case: is_boolP => [/IHf//|/IHf//|]; rewrite eval_or_cnf !eval_and_cnf.
    by move=> /orP[/andP[/IHf+ /IHg]|/andP[/IHf+ /IHg]].
  + case: is_boolP => [/IHf|/IHf|]/=; last rewrite eval_or_cnf !eval_and_cnf.
    * by move=> ef ei; apply/ef/ei.2.
    * by move=> ef ei; apply: ei.1.
    move => /orP[/andP[/IHf+ /IHg]|/andP[/IHf+ /IHg]].
    * by move=> ef eg ei; apply/eg/ei.1.
    * by move=> ef eg ei; apply/ef/ei.2.
  + case: is_boolP => [/IHf->//|/IHf->//|]/=; rewrite eval_or_cnf !eval_and_cnf.
    by move=> /orP[/andP[/IHf-> /IHg->]|/andP[/IHf-> /IHg->]].
  + case: is_boolP => [/IHf->//|/IHf->//|]/=; rewrite eval_or_cnf !eval_and_cnf.
    by move=> /orP[/andP[/IHf-> /IHg->]|/andP[/IHf-> /IHg->]].
- move: k => f IHf g IHg [].
  + case: is_boolP => [/IHf//|/IHf//|]; rewrite eval_or_cnf !eval_and_cnf.
    by move=> /orP[/andP[/IHf-> /IHg->]|/andP[/IHf-> /IHg->]].
  + case: is_boolP => [/IHf->//|/IHf->//|]/=; rewrite eval_or_cnf !eval_and_cnf.
    by move=> /orP[/andP[/IHf-> /IHg->]|/andP[/IHf-> /IHg->]].
Qed.

End GFormulaNormalisation.

Section FormulaChecker.
Variables (R C : realDomainType) (R_of_C : {rmorphism C -> R}).
Hypothesis R_of_C_ge0 : {mono R_of_C : x / 0 <= x}.

Implicit Type l : seq R.

#[local] Notation NFeval := (NFeval R_of_C).

#[local] Notation pexpr_times_nformula := (pexpr_times_nformula
  0 1 +%R *%R eq_op).
#[local] Notation nformula_times_nformula := (nformula_times_nformula
  0 1 +%R *%R eq_op).
#[local] Notation nformula_plus_nformula := (nformula_plus_nformula
  0 +%R eq_op).
#[local] Notation eval_Psatz := (eval_Psatz 0 1 +%R *%R eq_op <=%R).
#[local] Notation deduce := nformula_plus_nformula.
#[local] Notation unsat := (check_inconsistent 0 eq_op <=%R).
#[local] Notation check_normalised_formulas := (check_normalised_formulas
  0 1 +%R *%R eq_op <=%R).

Lemma eval_OpMult o o' (x x' : R) : eval_op1 o x -> eval_op1 o' x' ->
  forall o'', OpMult o o' = Some o'' -> eval_op1 o'' (x * x').
Proof.
case: o => /=[/eqP->| ro | ro | ro].
- by rewrite mul0r; case: o' => /= + + [<-]/=.
- by case: o' => //= /eqP-> + [<-]/=; rewrite mulr0.
- case: o' => /=[/eqP->|//| ro' | ro'] o'' [<-]/=.
  + by rewrite mulr0.
  + exact: mulr_gt0.
  + by rewrite mulr_ge0// ltW.
- case: o' => /=[/eqP->|//| ro' | ro'] o'' [<-]/=.
  + by rewrite mulr0.
  + by rewrite mulr_ge0// ltW.
  + exact: mulr_ge0.
Qed.

Lemma eval_OpAdd o o' (x x' : R) : eval_op1 o x -> eval_op1 o' x' ->
  forall o'', OpAdd o o' = Some o'' -> eval_op1 o'' (x + x').
Proof.
case: o => /=[/eqP->| ro | ro | ro].
- by rewrite add0r => + + [<-].
- by case: o' => //= /eqP-> + [<-]; rewrite addr0.
- case: o' => /=[/eqP->|//| ro' | ro'] o'' [<-]/=.
  + by rewrite addr0.
  + exact: addr_gt0.
  + exact: ltr_wpDr.
- case: o' => /=[/eqP->|//| ro' | ro'] o'' [<-]/=.
  + by rewrite addr0.
  + exact: ltr_wpDl.
  + exact: addr_ge0.
Qed.

Lemma eval_pexpr_times_nformula l e f f' :
  NFeval l f -> pexpr_times_nformula e f = Some f' -> NFeval l f'.
Proof. by case: f => e' []//= /eqP ee' [<-]/=; rewrite PevalM ee' mulr0. Qed.

Lemma eval_nformula_times_nformula l f f' f'' : NFeval l f -> NFeval l f' ->
  nformula_times_nformula f f' = Some f'' -> NFeval l f''.
Proof.
case: f f' => [e o] [e' o'] /= ee ee'.
case: OpMult (eval_OpMult ee ee') => [o'' /(_ _ erefl) + [<-]/=|//].
by rewrite PevalM.
Qed.

Lemma eval_nformula_plus_nformula l f f' f'' : NFeval l f -> NFeval l f' ->
  nformula_plus_nformula f f' = Some f'' -> NFeval l f''.
Proof.
case: f f' => [e o] [e' o'] /= ee ee'.
case: OpAdd (eval_OpAdd ee ee') => [o'' /(_ _ erefl) + [<-]/=|//].
by rewrite PevalD.
Qed.

Lemma is_tautoT l f g :
    match deduce f g with None => false | Some u => unsat u end ->
  ~~ NFeval l f || ~~ NFeval l g.
Proof.
case: nformula_plus_nformula (@eval_nformula_plus_nformula l f g) => [f'|//].
move=> /(_ f') + if'.
rewrite -negb_and; apply: contraPN => /andP[-> ->] /(_ erefl erefl erefl).
by rewrite (check_inconsistentT _ _ if').
Qed.

Lemma nth_nth T n s (x0 : T) : ListDef.nth n s x0 = nth x0 s n.
Proof. by elim: s n => [| e s IH] /= [| n]. Qed.

Lemma eval_eval_Psatz l lf (w : Psatz C) : all (NFeval l) lf ->
  forall f : NFormula C, eval_Psatz lf w = Some f -> NFeval l f.
Proof.
elim: w lf.
- move=> p1 IHp1 p2 IHp2 lf elf f /=.
  case: eval_Psatz (IHp1 lf elf) => [f' /(_ _ erefl) ef'|//].
  by apply: IHp2; rewrite /= ef'.
- move=> n lf /all_nthP elf f /=[<-].
  case: (ltnP n (size lf)) => nslf; first by rewrite nth_nth elf.
  by rewrite nth_nth nth_default/= ?rmorph0.
- by move=> e lf elf f /=[<-]/=; rewrite Peval_square sqr_ge0.
- move=> re e IH lf elf f /=.
  case: eval_Psatz (IH _ elf) => [f' /(_ _ erefl) ef' /=|//].
  exact/(eval_pexpr_times_nformula ef').
- move=> f1 IHf1 f2 IHf2 lf elf f /=.
  case: eval_Psatz (IHf1 _ elf) => [f1' /(_ _ erefl) ef1'|]; last first.
    by case: eval_Psatz.
  case: eval_Psatz (IHf2 _ elf) => [f2' /(_ _ erefl) ef2' /= |//].
  exact/(eval_nformula_times_nformula ef1' ef2').
- move=> f1 IHf1 f2 IHf2 lf elf f /=.
  case: eval_Psatz (IHf1 _ elf) => [f1' /(_ _ erefl) ef1'|]; last first.
    by case: eval_Psatz.
  case: eval_Psatz (IHf2 _ elf) => [f2' /(_ _ erefl) ef2' /= |//].
  exact/(eval_nformula_plus_nformula ef1' ef2').
- move=> c lf elf f /=; rewrite /cltb andbC -lt_neqAle.
  case: ltP => [c0 |//] [<-]/=.
  by rewrite ltNge -oppr_ge0 -rmorphN R_of_C_ge0 oppr_ge0 -ltNge.
- by move=> lf elf f [<-]/=; rewrite rmorph0.
Qed.

Lemma check_normalised_formulasT l (lf : seq (NFormula C)) (w : Psatz C) :
  check_normalised_formulas lf w -> has (fun f => ~~ NFeval l f) lf.
Proof.
rewrite has_predC; apply: contraL => /(@eval_eval_Psatz _ _ w).
rewrite /check_normalised_formulas; case: eval_Psatz => [f /(_ _ erefl)|//].
by apply: contraL => /check_inconsistentT->.
Qed.

End FormulaChecker.

Section TautoChecker.
Variables (R C : realDomainType) (R_of_C : {rmorphism C -> R}).
Hypothesis R_of_C_ge0 : {mono R_of_C : x / 0 <= x}.

Implicit Type l : seq R.

#[local] Notation check_normalised_formulas := (check_normalised_formulas
  0 1 +%R *%R eq_op <=%R).
#[local] Notation tauto_checker := (tauto_checker
  (fun c : seq (NFormula C * unit) => check_normalised_formulas (map fst c))).
#[local] Notation check_normalised_formulasT := (check_normalised_formulasT
  R_of_C_ge0).

Lemma tauto_checkerT l (f : cnf (NFormula C) unit) (w : seq (Psatz C)) :
  tauto_checker f w -> eval_cnf (fun f => ~~ NFeval R_of_C l f) f.
Proof.
elim: f w => [//| f lf IH] [//| w lw] /=/andP[/(check_normalised_formulasT l)].
by rewrite has_map /eval_clause => -> /IH.
Qed.

End TautoChecker.

Arguments option_R {_ _}.

Elpi derive.param2 True.
Elpi derive.param2 False.
Elpi derive.param2 and.
Elpi derive.param2 or.
Elpi derive.param2 not.
Elpi derive.param2 eq.
Elpi derive.param2 iff.
Elpi derive.param2 Datatypes.is_true.

Elpi derive.param2 orb.
Elpi derive.param2 andb.
Elpi derive.param2 negb.
Elpi derive.param2 addb.
Elpi derive.param2 eqb.
Elpi derive.param2 implb.

Elpi derive.param2 fst.
Elpi derive.param2 predn.
Elpi derive.param2 Nat.add.

Elpi derive.param2 ListDef.nth.
Elpi derive.param2 ListDef.map.
Elpi derive.param2 ListDef.rev_append.
Elpi derive.param2 ListDef.fold_left.
Elpi derive.param2 ListDef.fold_right.

#[warning="-elpi.renamed"]
Elpi derive.param2 nth.

Elpi derive.param2 apply_option.
Elpi derive.param2 bind_option.
Elpi derive.param2 map_option.
Elpi derive.param2 bind_option2.

Elpi derive.param2 Pos.iter_op.
Elpi derive.param2 Pos.to_nat.

Elpi derive.param2 Op2.
Elpi derive.param2 Formula.
Elpi derive.param2 kind.
Elpi derive.param2 GFormula.
Elpi derive.param2 eKind.
Elpi derive.param2 BFormula.
Elpi derive.param2 Psatz.

Elpi derive.param2 Psquare.

Elpi derive.param2 clause.
Elpi derive.param2 cnf.
Elpi derive.param2 cnf_tt.
Elpi derive.param2 cnf_ff.
Elpi derive.param2 is_cnf_tt.
Elpi derive.param2 is_cnf_ff.
Elpi derive.param2 add_term.
Elpi derive.param2 or_clause.
Elpi derive.param2 or_clause_cnf.
Elpi derive.param2 or_cnf_aux.
Elpi derive.param2 or_cnf.
Elpi derive.param2 and_cnf.

Elpi derive.param2 cneqb.
Elpi derive.param2 cltb.
Elpi derive.param2 Op1.
Elpi derive.param2 NFormula.
Elpi derive.param2 Pol_of_PExpr.
Elpi derive.param2 normalise.
Elpi derive.param2 check_inconsistent.
Elpi derive.param2 normalise_aux.
Elpi derive.param2 negate_aux.
Elpi derive.param2 cnf_of_list.
Elpi derive.param2 cnf_normalise.
Elpi derive.param2 cnf_negate.

Elpi derive.param2 mk_and.
Elpi derive.param2 mk_or.
Elpi derive.param2 mk_impl.
Elpi derive.param2 mk_iff.
Elpi derive.param2 is_bool.
Elpi derive.param2 cnf_of_GFormula.

Elpi derive.param2 OpMult.
Elpi derive.param2 OpAdd.
Elpi derive.param2 pexpr_times_nformula.
Elpi derive.param2 nformula_times_nformula.
Elpi derive.param2 nformula_plus_nformula.
Elpi derive.param2 is_tauto.
Elpi derive.param2 eval_Psatz.
Elpi derive.param2 check_normalised_formulas.

Elpi derive.param2 cnf_checker.
Elpi derive.param2 tauto_checker.

Elpi derive.param2 CWeakChecker.
Elpi derive.param2 Cnormalise.
Elpi derive.param2 Cnegate.
Elpi derive.param2 Cis_tauto.
Elpi derive.param2 Ccnf_of_GFormula.
Elpi derive.param2 CTautoChecker.

Elpi derive.param2 PEeval.
Elpi derive.param2 eval_op2.
Elpi derive.param2 Feval.
Elpi derive.param2 eTT.
Elpi derive.param2 eFF.
Elpi derive.param2 eAND.
Elpi derive.param2 eOR.
Elpi derive.param2 eNOT.
Elpi derive.param2 eIMPL.
Elpi derive.param2 eIFF.
Elpi derive.param2 GFeval.

Elpi derive.param2 env_nth.
Elpi derive.param2 KFeval.
Elpi derive.param2 BFeval.
Elpi derive.param2 BFKFeval.

(* a bunch of helper lemmas *)

Lemma unit_Rxx u : unit_R u u. Proof. by case: u; apply: tt_R. Qed.
Lemma option_Rxx A (RA : A -> A -> Type) (_ : forall x, RA x x) s :
  option_R RA s s.
Proof. by case: s => [x |]; constructor. Qed.
Lemma list_Rxx A (RA : A -> A -> Type) (_ : forall x, RA x x) s : list_R RA s s.
Proof. by elim: s => [| x s IH]; constructor. Qed.
Lemma eKind_Rxx k (rk : kind_R k k) (t : eKind k) : eKind_R rk t t.
Proof.
case: k rk t => rk t.
- by refine
    (match rk in kind_R k1 k2
           return
           eKind_R rk
             (match k1 with isProp => t | isBool => true end)
             (match k2 with isProp => t | isBool => true end)
     with
     | isProp_R => fun _ _ => True
     | isBool_R => true_R
     end).
- by refine
    (match rk in kind_R k1 k2
           return
           eKind_R rk
             (match k1 with isProp => True | isBool => t end)
             (match k2 with isProp => True | isBool => t end)
     with
     | isProp_R => fun _ _ => True
     | isBool_R => bool_Rxx t
     end).
Qed.

Lemma positive_R_eq p p' : positive_R p p' -> p = p'.
Proof. by elim/positive_R_ind => [? ? ? ->|? ? ? ->|]. Qed.
Lemma N_R_eq n n' : N_R n n' -> n = n'.
Proof. by elim/N_R_ind => [//| ? _ /positive_R_eq<-]. Qed.
Lemma list_R_eq T (s s' : seq T) : list_R eq s s' -> s = s'.
Proof. by elim/list_R_ind => [//| x _ <- {}s _ _ <-]. Qed.

Lemma erefl1 {A B} {f : A -> B} : forall a1 a2 (ra : a1 = a2), f a1 = f a2.
Proof. by move=> ? ? ->. Qed.
Lemma erefl2 {A B C} {f : A -> B -> C} :
  forall a1 a2 (ra : a1 = a2) b1 b2 (rb : b1 = b2), f a1 b1 = f a2 b2.
Proof. by move=> ? ? -> ? ? ->. Qed.
Lemma erefl2b {A B} {f : A -> B -> bool} :
  forall a1 a2 (ra : a1 = a2) b1 b2 (rb : b1 = b2), bool_R (f a1 b1) (f a2 b2).
Proof. by move=> ? ? -> ? ? ->; apply: bool_Rxx. Qed.
Lemma erefl2n {A B} {f : A -> N -> B} :
  forall a1 a2 (ra : a1 = a2) b1 b2 (rb : N_R b1 b2), f a1 b1 = f a2 b2.
Proof. by move=> _ ? -> _ ? /N_R_eq->. Qed.

Lemma Formula_R_map A B (RAB : A -> B -> Type) (f : A -> B) :
    (forall a, RAB a (f a)) ->
  forall g : Formula A, Formula_R RAB g (Fmap f g).
Proof.
move=> rf [lhs o rhs]; apply: Build_Formula_R.
- exact: PExpr_R_map.
- by case: o; constructor.
- exact: PExpr_R_map.
Qed.

Lemma BFormula_R_map A B (RAB : A -> B -> Type) (f : A -> B) :
    (forall a, RAB a (f a)) ->
  forall k (rk : kind_R k k) (g : BFormula (Formula A) k),
    BFormula_R (Formula_R RAB) rk g (GFmap (Fmap f) g).
Proof.
move=> rf k rk g; elim: g rk.
- by move=> {}k rk; apply: TT_R.
- by move=> {}k rk; apply: FF_R.
- by move=> {}k t rk; apply/X_R/eKind_Rxx.
- by move=> {}k g u rk; apply: A_R; [apply: Formula_R_map | apply: unit_Rxx].
- by move=> {}k f1 IH1 f2 IH2 rk; apply: AND_R; [apply: IH1 | apply: IH2].
- by move=> {}k f1 IH1 f2 IH2 rk; apply: OR_R; [apply: IH1 | apply: IH2].
- by move=> {}k g IH rk; apply/NOT_R/IH.
- move=> {}k f1 IH1 u f2 IH2 rk.
  by apply: IMPL_R; [exact: IH1 | exact/option_Rxx/unit_Rxx | exact: IH2].
- by move=> {}k f1 IH1 f2 IH2 rk; apply: IFF_R; [apply: IH1 | apply: IH2].
- move=> f1 IH1 f2 IH2 rk {k}.
  refine
    (match rk in kind_R k1 k2
           return
           BFormula_R (Formula_R RAB) rk
             (match k1 with isProp => EQ f1 f2 | isBool => TT isBool end)
             (match k2 with
              | isProp => EQ (GFmap (Fmap f) f1) (GFmap (Fmap f) f2)
              | isBool => TT isBool
              end)
     with
     | isProp_R => _
     | isBool_R => TT_R _ _ _ _ isBool_R
     end).
  by apply: EQ_R; [apply: IH1 | apply: IH2].
Qed.

Lemma Pol_R_map A B (RAB : A -> B -> Type) (f : A -> B) :
  (forall a, RAB a (f a)) -> forall w : Pol A, Pol_R RAB w (Pmap f w).
Proof.
by move=> rf; elim=> [c | j P IH | P IHP i Q IHQ];
  constructor=> //; apply: positive_Rxx.
Qed.

Lemma Psatz_R_map A B (RAB : A -> B -> Type) (f : A -> B) :
  (forall a, RAB a (f a)) -> forall w : Psatz A, Psatz_R RAB w (Psatz_map f w).
Proof.
move=> rf; elim=> [p1 IH1 p2 IH2|n|p|re e IH|f1 IH1 f2 IH2|f1 IH1 f2 IH2|c|].
- by apply: PsatzLet_R; [apply: IH1 | apply: IH2].
- exact/PsatzIn_R/nat_Rxx.
- exact/PsatzSquare_R/Pol_R_map.
- by apply: PsatzMulC_R; [apply: Pol_R_map | apply: IH].
- by apply: PsatzMulE_R; [apply: IH1 | apply: IH2].
- by apply: PsatzAdd_R; [apply: IH1 | apply: IH2].
- exact: PsatzC_R.
- exact: PsatzZ_R.
Qed.

(* Refinement of C to an actually computable type, for the reflexive tactic. *)
Section CTautoChecker.
Variables (R AC : realDomainType) (R_of_AC : {rmorphism AC -> R}).
Hypothesis R_of_AC_eq0 : {mono R_of_AC : x / x == 0}.
Hypothesis R_of_AC_ge0 : {mono R_of_AC : x / 0 <= x}.
Variable (C : Type) (cO cI : C) (cadd cmul csub : C -> C -> C) (copp : C -> C).
Variables (ceqb cleb : C -> C -> bool) (R_of_C : C -> R) (AC_of_C : C -> AC).
Variable (CAC : C -> AC -> Prop) (CAC0 : CAC cO 0) (CAC1 : CAC cI 1).
Hypothesis CACD : forall c ac (_ : CAC c ac) c' ac' (_ : CAC c' ac'),
  CAC (cadd c c') (ac + ac').
Hypothesis CACM : forall c ac (_ : CAC c ac) c' ac' (_ : CAC c' ac'),
  CAC (cmul c c') (ac * ac').
Hypothesis CACB : forall c ac (_ : CAC c ac) c' ac' (_ : CAC c' ac'),
  CAC (csub c c') (ac - ac').
Hypothesis CACN : forall c ac, CAC c ac -> CAC (copp c) (- ac).
Hypothesis CACeq : forall c ac (_ : CAC c ac) c' ac' (_ : CAC c' ac'),
  ceqb c c' = (ac == ac').
Hypothesis CACle : forall c ac (_ : CAC c ac) c' ac' (_ : CAC c' ac'),
  cleb c c' = (ac <= ac').
Hypothesis R_of_C_R_of_AC : forall c ac, CAC c ac -> R_of_C c = R_of_AC ac.
Hypothesis CAC_AC_of_C : forall c, CAC c (AC_of_C c).

Implicit Type l : seq R.

Lemma CTautoChecker_map_AC_of_C f w :
  @CTautoChecker C cO cI cadd cmul csub copp ceqb cleb f w
  = @CTautoChecker AC 0 1 +%R  *%R (fun x y : AC => x - y) -%R eq_op <=%R
    (GFmap (Fmap AC_of_C) f) [seq Psatz_map AC_of_C ps | ps <- w].
Proof.
have rf : BFormula_R (Formula_R CAC) isProp_R f (GFmap (Fmap AC_of_C) f).
  exact: BFormula_R_map.
have rw : list_R (Psatz_R CAC) w [seq Psatz_map AC_of_C ps | ps <- w].
  by apply: list_R_map => w'; apply: Psatz_R_map.
by apply: bool_R_eq; apply: CTautoChecker_R rw => //; apply: eq_bool_R2.
Qed.

(* Unfortunately, we can only use derive.param2 for bool, not Prop *)
Lemma RBFeval_map_AC_of_C_bool l (f : BFormula (Formula C) isBool) :
  RBFeval R_of_AC l (GFmap (Fmap AC_of_C) f) = RBFeval R_of_C l f.
Proof.
have rl : list_R eq l l by apply: list_Rxx.
have rf : BFormula_R (Formula_R CAC) isBool_R f (GFmap (Fmap AC_of_C) f).
  exact: BFormula_R_map.
by rewrite /RBFeval (bool_R_eq (BFKFeval_R erefl erefl2 erefl2 erefl1 erefl2n
  erefl2b erefl2b erefl2b erefl2b R_of_C_R_of_AC rl rf)).
Qed.

(* So we have to do the Prop case by hand (but we can still use Feval_R there
   and it isn't much work in the end). *)
Lemma RBFeval_map_AC_of_C l k (f : BFormula (Formula C) k) :
  hold true
    (eIFF eqb k (RBFeval R_of_AC l (GFmap (Fmap AC_of_C) f))
       (RBFeval R_of_C l f)).
Proof.
elim: f.
- by case.
- by case.
- by case=> f => [//|/=]; rewrite -/(f == f) eqxx.
- case=> f u; last by apply/eqP; rewrite -RBFeval_map_AC_of_C_bool.
  have rN n n' : N_R n n' -> n = n' by move=> /N_R_eq->.
  have renv_nth : forall i i' (ii' : positive_R i i')
      (s s' : seq R) (ss' : list_R eq s s'), env_nth 0 i s = env_nth 0 i' s'.
    by move=> i _ /positive_R_eq<- s _ /list_R_eq<-.
  have rl : list_R eq l l by apply: list_Rxx.
  have rf : Formula_R CAC f (Fmap AC_of_C f) by apply: Formula_R_map.
  pose Feval_R := bool_R_eq (Feval_R erefl2 erefl2 erefl2 erefl1 rN erefl2
    (k_R:=isBool_R) erefl2b erefl2b erefl2b erefl2b R_of_C_R_of_AC renv_nth
    rl rf).
  by split=> /RFevalP/=; [rewrite -Feval_R | rewrite Feval_R]; move=> /RFevalP.
- case=> f IHf g IHg; last by apply/eqP; rewrite -RBFeval_map_AC_of_C_bool.
  by split=> -[/IHf+ /IHg].
- case=> f IHf g IHg; last by apply/eqP; rewrite -RBFeval_map_AC_of_C_bool.
  by split=> /=; (move=> [/IHf|/IHg]; [left|right]).
- case=> f IH; last by apply/eqP; rewrite -RBFeval_map_AC_of_C_bool.
  by split=> /IH.
- case=> f IHf u g IHg; last by apply/eqP; rewrite -RBFeval_map_AC_of_C_bool.
  by split=> efg ef; apply/IHg/efg/IHf.
- case=> f IHf g IHg; last by apply/eqP; rewrite -RBFeval_map_AC_of_C_bool.
  by split=> -[efg egf]; split=> [/IHf/efg/IHg|/IHg/egf/IHf].
- by move=> /= f /eqP-> g /eqP->.
Qed.

Lemma CTautoCheckerT l f w :
    @CTautoChecker C cO cI cadd cmul csub copp ceqb cleb f w ->
  RBFeval R_of_C l f.
Proof.
rewrite CTautoChecker_map_AC_of_C => checkfw.
apply: (RBFeval_map_AC_of_C l f).1.
rewrite -/(hold true (RBFeval R_of_AC l (GFmap (Fmap AC_of_C) f))).
apply: eval_cnf_of_GFormula => //; first exact: is_tautoT.
exact: tauto_checkerT checkfw.
Qed.

End CTautoChecker.

(* Refinement from rat to Q, for actual computation in the reflexive tactic. *)
Definition R_of_Q (R : unitRingType) (q : Q) : R :=
  let: Qmake n d := q in
  if d is xH then (int_of_Z n)%:~R
  else if n is Zpos xH then (Pos.to_nat d)%:R ^-1
  else (int_of_Z n)%:~R / (Pos.to_nat d)%:R.

Lemma R_of_Q_ratr (R : numFieldType) q r : Qrat q r -> R_of_Q R q = ratr r.
Proof.
suff -> : R_of_Q R q = (int_of_Z (Qnum q))%:~R / (Pos.to_nat (Qden q))%:R.
  by move/eqP => <-; rewrite fmorph_div/= ratr_int ratr_nat.
by case: q => n [d | d |]/=; [| |by rewrite Pos_to_nat1 divr1];
  case: n => [//| [//|//|/=] |//]; rewrite Pos_to_nat1 div1r.
Qed.

Lemma QTautoCheckerT (R : realFieldType) (l : seq R) f w :
  QTautoChecker f w -> RBFeval (R_of_Q R) l f.
Proof.
exact: (CTautoCheckerT (ler0q R) Qrat0 Qrat1 QratD QratM QratB QratN
  Qrat_eq Qrat_le (R_of_Q_ratr R) Qrat_rat_of_Q).
Qed.

(* Refinement from int to Z, for actual computation in the reflexive tactic. *)
Definition ZTautoChecker := @CTautoChecker Z
  Z0 (Zpos xH) Z.add Z.mul Z.sub Z.opp Z.eqb Z.leb.

Lemma ZTautoCheckerT (R : realDomainType) (l : seq R) f w :
  ZTautoChecker f w -> RBFeval (R_of_Z R intr) l f.
Proof.
exact: (CTautoCheckerT (ler0z R) (CAC:=Zint) Zint0 _ ZintD ZintM ZintB ZintN
  Zint_eq Zint_le (R_of_Z_intr R) Zint_int_of_Z).
Qed.

(* Everything below is essentially imported form algebra-tactics *)

Implicit Types (V : nmodType) (R : pzSemiRingType) (F : fieldType).

Record RFormula R := { Rlhs : RExpr R; Rop : Op2; Rrhs : RExpr R }.

Section Rnorm_formula.
Variables (R : field_or_ring).
Variables (R_not_semiring : (if R is SemiRing _ then false else true) = true).
Variables (R_of_N : bool -> N -> R).
Variables (R_of_NE : R_of_N =2 fun b n => invi b (N.to_nat n)%:R).
Variables (add : R -> R -> R) (addE : add = +%R).
Variables (mul : R -> R -> R) (mulE : mul = *%R).
Variables (opp_intr : option ((R -> R) * (int -> R))).
Variables (opp_intrE : opp_intr = ring_opp_intr R).
Variables (exp : R -> N -> R) (expE : exp = (fun x n => x ^+ N.to_nat n)).
Variables (inv : option (R -> R)) (invE : inv = field_inv R).
Variables (beq bneq le lt : R -> R -> bool).

#[local] Notation Rnorm_expr := (Rnorm
  R_of_N (R_of_N false N0) add opp_intr (R_of_N false (Npos 1)) mul exp inv
  true false).

Definition Reval_op2 k : Op2 -> R -> R -> eKind k :=
  if k is isBool then eval_op2 isBool beq bneq le lt
  else eval_op2 isProp eq (fun x y => ~ x = y) le lt.

Definition Reval_formula k (ff : RFormula R) : eKind k :=
  let: Build_RFormula lhs o rhs := ff in Reval_op2 k o (Reval lhs) (Reval rhs).

Definition Rnorm_formula k (ff : RFormula R) :=
  let: Build_RFormula lhs o rhs := ff in
  Reval_op2 k o (Rnorm_expr id lhs) (Rnorm_expr id rhs).

Lemma Rnorm_formula_correct k (ff : RFormula R) :
  Reval_formula k ff = Rnorm_formula k ff.
Proof.
case: ff => lhs o rhs /=.
have e : true = (if R is SemiRing _ then false else true) && true.
  by case: R R_not_semiring.
rewrite !(@Rnorm_correct R true _ e) !R_of_NE addE opp_intrE mulE expE invE.
by congr Reval_op2; apply: Rnorm_eq_F_of_N.
Qed.

Lemma Rnorm_bf_correct k (ff : BFormula (RFormula R) k) :
  BFeval eqb Reval_formula ff = BFeval eqb Rnorm_formula ff.
Proof.
elim: ff => // {k}.
- by move=> k ff ?; exact: Rnorm_formula_correct.
- by move=> k ff1 IH1 ff2 IH2; congr eAND.
- by move=> k ff1 IH1 ff2 IH2; congr eOR.
- by move=> k ff IH; congr eNOT.
- by move=> k ff1 IH1 o ff2 IH2; congr eIMPL.
- by move=> k ff1 IH1 ff2 IH2; congr eIFF.
- by move=> ff1 IH1 ff2 IH2; congr eq.
Qed.

End Rnorm_formula.

Lemma FTautoChecker_sound (F : realFieldType)
    (ff : BFormula (RFormula F) isProp)
    (f : BFormula (Formula Q) isProp) (env : seq F) (w : seq (Psatz Q)) :
    (forall F_of_Q add mul opp exp beq bneq le lt,
       let norm_ff :=
         let F_of_N b n :=
           if b then F_of_Q (Qinv (Qmake (Z.of_N n) 1))
           else F_of_Q (Qmake (Z.of_N n) 1) in
         let opp_intr := Some (opp, intr : int -> Field F) in
         let inv : option (Field F -> Field F) := Some (@GRing.inv F) in
         Rnorm_formula F_of_N add mul opp_intr exp inv beq bneq le lt in
       let eval_f :=
         (KFeval 0 add mul opp exp beq bneq le lt F_of_Q)^~ env in
       BFeval eqb norm_ff ff = BFeval eqb eval_f f) ->
    QTautoChecker f w ->
  BFeval eqb (@Reval_formula (Field F) eq_op (cneqb eq_op) <=%R <%R) ff.
Proof.
pose F_of_N b n : Field F :=
  if b then R_of_Q F (Qinv (Qmake (Z.of_N n) 1))
  else R_of_Q F (Qmake (Z.of_N n) 1).
have F_of_NE : F_of_N =2 fun b n => @invi (Field F) b (N.to_nat n)%:R.
  by move=> [] [|[]]; rewrite //= /inv_id/= ?invr0 ?invr1.
rewrite (Rnorm_bf_correct _ F_of_NE erefl erefl erefl erefl erefl)//.
by move/(_ (R_of_Q F)) => -> /(QTautoCheckerT env).
Qed.

Lemma RTautoChecker_sound (R : realDomainType)
    (ff : BFormula (RFormula R) isProp)
    (f : BFormula (Formula Z) isProp) (env : seq R) (w : seq (Psatz Z)) :
    (forall R_of_Z add mul opp exp beq bneq le lt,
       let norm_ff :=
         let R_of_N _ n := R_of_Z (Z.of_N n) in
         let opp_intr := Some (opp, intr : int -> Ring R) in
         let inv : option (Ring R -> Ring R) := None in
         Rnorm_formula R_of_N add mul opp_intr exp inv beq bneq le lt in
       let eval_f :=
         (KFeval 0 add mul opp exp beq bneq le lt R_of_Z)^~ env in
       BFeval eqb norm_ff ff = BFeval eqb eval_f f) ->
    ZTautoChecker f w ->
  BFeval eqb (@Reval_formula (Ring R) eq_op (cneqb eq_op) <=%R <%R) ff.
Proof.
pose R_of_N (b : bool) n : Ring R := R_of_Z R intr (Z.of_N n).
have R_of_NE : R_of_N =2 fun b n => @invi (Ring R) b (N.to_nat n)%:R.
  by case=> [] [].
rewrite (Rnorm_bf_correct _ R_of_NE erefl erefl erefl erefl erefl)//.
by move/(_ (R_of_Z R intr)) => -> /(ZTautoCheckerT env).
Qed.

(* Translating formulas and witnesses from Q to Z for the realDomainType case *)

Fixpoint PExpr_Q2Z (e : PExpr Q) : option (PExpr Z) := match e with
  | PEc (Qmake z 1) => Some (PEc z) | PEc _ => None
  | PEX n => Some (PEX n)
  | PEadd e1 e2 => map_option2 PEadd (PExpr_Q2Z e1) (PExpr_Q2Z e2)
  | PEsub e1 e2 => map_option2 PEsub (PExpr_Q2Z e1) (PExpr_Q2Z e2)
  | PEmul e1 e2 => map_option2 PEmul (PExpr_Q2Z e1) (PExpr_Q2Z e2)
  | PEopp e1 => map_option PEopp (PExpr_Q2Z e1)
  | PEpow e1 n => map_option (PEpow ^~ n) (PExpr_Q2Z e1) end.

Definition Formula_Q2Z (ff : Formula Q) : option (Formula Z) :=
  map_option2
    (fun l r => Build_Formula l (Fop ff) r)
    (PExpr_Q2Z (Flhs ff)) (PExpr_Q2Z (Frhs ff)).

Fixpoint BFormula_Q2Z [k] (ff : BFormula (Formula Q) k) :
    option (BFormula (Formula Z) k) := match ff with
  | TT k => Some (TT k)
  | FF k => Some (FF k)
  | X k P => Some (X k P)
  | A k a aa => map_option (A k ^~ aa) (Formula_Q2Z a)
  | AND _ f1 f2 =>
      map_option2 (fun f => AND f) (BFormula_Q2Z f1) (BFormula_Q2Z f2)
  | OR _ f1 f2 =>
      map_option2 (fun f => OR f) (BFormula_Q2Z f1) (BFormula_Q2Z f2)
  | NOT _ f1 => map_option (fun f => NOT f) (BFormula_Q2Z f1)
  | IMPL _ f1 o f2 =>
      map_option2 (fun f => IMPL f o) (BFormula_Q2Z f1) (BFormula_Q2Z f2)
  | IFF _ f1 f2 =>
      map_option2 (fun f => IFF f) (BFormula_Q2Z f1) (BFormula_Q2Z f2)
  | EQ f1 f2 => map_option2 EQ (BFormula_Q2Z f1) (BFormula_Q2Z f2) end.

Fixpoint Pol_Q2Z (p : Pol Q) : Pol Z * positive := match p with
  | Pc (Qmake n d) => (Pc n, d)
  | Pinj j p => let (p, n) := Pol_Q2Z p in (Pinj j p, n)
  | PX p1 i p2 =>
      let (p1, n1) := Pol_Q2Z p1 in
      let (p2, n2) := Pol_Q2Z p2 in
      let mulc c p := PmulC Z0 (Zpos 1) Z.mul Z.eqb p (Zpos c) in
      (PX (mulc n2 p1) i (mulc n1 p2), Pos.mul n1 n2)
  end.

Fixpoint Psatz_Q2Z (l : seq positive) (p : Psatz Q) : Psatz Z * positive :=
  match p with
  | PsatzC (Qmake n d) => (PsatzC n, d)
  | PsatzLet p1 p2 =>
      let (p1, n1) := Psatz_Q2Z l p1 in
      let (p2, n2) := Psatz_Q2Z (n1 :: l) p2 in
      (PsatzLet p1 p2, n2)
  | PsatzIn n => (PsatzIn _ n, nth 1%positive l n)
  | PsatzSquare p => let (p, n) := Pol_Q2Z p in (PsatzSquare p, Pos.mul n n)
  | PsatzMulC p1 p2 =>
      let (p1, n1) := Pol_Q2Z p1 in
      let (p2, n2) := Psatz_Q2Z l p2 in
      (PsatzMulC p1 p2, Pos.mul n1 n2)
  | PsatzMulE p1 p2 =>
      let (p1, n1) := Psatz_Q2Z l p1 in
      let (p2, n2) := Psatz_Q2Z l p2 in
      (PsatzMulE p1 p2, Pos.mul n1 n2)
  | PsatzAdd p1 p2 =>
      let (p1, n1) := Psatz_Q2Z l p1 in
      let (p2, n2) := Psatz_Q2Z l p2 in
      let mulc c p := PsatzMulE (PsatzC (Zpos c)) p in
      (PsatzAdd (mulc n2 p1) (mulc n1 p2), Pos.mul n1 n2)
  | PsatzZ => (PsatzZ _, 1%positive)
  end.

Definition seq_Psatz_Q2Z : seq (Psatz Q) -> seq (Psatz Z) :=
  map (fun p => fst (Psatz_Q2Z [::] p)).

(* Main tactics, called from the elpi parser (c.f., lra.elpi) *)

Ltac mclra_witness n f := let w := fresh "__wit" in wlra_Q w f.
Ltac mcnra_witness n f := let w := fresh "__wit" in wnra_Q w f.
Ltac mcpsatz_witness n f :=
  let w := fresh "__wit" in wsos_Q w f || wpsatz_Q n w f.

Ltac mctacF F hyps ff f varmap wit :=
  let nff := fresh "__ff" in
  let nf := fresh "__f" in
  let nvarmap := fresh "__varmap" in
  pose (nff := ff);
  pose (nf := f);
  pose (nvarmap := varmap);
  refine (hyps (@FTautoChecker_sound F nff nf nvarmap wit
                  (fun _ _ _ _ _ _ _ _ _ => erefl) _));
  [ vm_compute; reflexivity ].

Ltac mctacR R hyps ff f varmap wit :=
  let nff := fresh "__ff" in
  let nf := fresh "__f" in
  let nvarmap := fresh "__varmap" in
  lazymatch eval vm_compute in (BFormula_Q2Z f) with
  | Some ?f =>
      pose (nff := ff);
      pose (nf := f);
      pose (nvarmap := varmap);
      refine (hyps (@RTautoChecker_sound R nff f nvarmap (seq_Psatz_Q2Z wit)
                      (fun _ _ _ _ _ _ _ _ _ => erefl) _));
      [ vm_compute; reflexivity ]
  | _ => fail  (* should never happen, the parser only parses int constants *)
  end.

End Internals.

Strategy expand [Reval_op2 Reval_formula Rnorm_formula].

Elpi Tactic mclra.
Elpi Accumulate Db mc.canonicals.db.
#[warning="-elpi.flex-clause"]
Elpi Accumulate File ring lra.

Tactic Notation "lra" := elpi mclra "mclra_witness" "mctacF" "mctacR" 0.
Tactic Notation "nra" := elpi mclra "mcnra_witness" "mctacF" "mctacR" 0.
Tactic Notation "psatz" integer(n) :=
  elpi mclra "mcpsatz_witness" "mctacF" "mctacR" ltac_int:(n).
Tactic Notation "psatz" := elpi mclra "mcpsatz_witness" "mctacF" "mctacR" (-1).

Elpi Query lp:{{ canonical-init library "mc.canonicals.db" }}.
Elpi Query lp:{{ coercion-init library "mc.canonicals.db" }}.

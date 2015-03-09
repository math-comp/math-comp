(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Structure tProp := TProp {tProp_statement :> Prop; _ : tProp_statement}.
Lemma claim : forall tP : tProp, tP. Proof. by case. Qed.
Hint Resolve claim.

Canonical Structure True_tProp := TProp Logic.I.
Canonical Structure eq_tProp T (x : T) := TProp (erefl x).
Canonical Structure true_tProp := @TProp true (erefl _).
Canonical Structure and_tProp (P Q : tProp) :=
  TProp (conj (claim P) (claim Q)).

Structure postProp (P : Prop) := PostProp {postProp_statement :> tProp; _ : P}.
Canonical Structure tProp_postProp P claimP pP :=
  PostProp (@TProp P claimP) (claim pP).

Delimit Scope n_ary_op_scope with QOP.
Delimit Scope quote_scope with QT.

Fixpoint n_ary n T := if n is n'.+1 then T -> n_ary n' T else T.
Notation "n .-ary" := (n_ary n) (at level 2, format "n .-ary") : type_scope.

Module Quotation.

CoInductive n_ary_op T := NaryOp n of n.-ary T.
Notation "f / n" := (@NaryOp _ n f) : n_ary_op_scope.
Definition bind_op T R (op : n_ary_op T) ifun : R :=
  let: NaryOp n f := op in ifun n f.
Definition arity T op := @bind_op T nat op (fun n _ => n).

Structure type := Pack {sort :> Type; sym; _ : sym -> n_ary_op sort}.
Notation QuoteType sf := (Pack sf%QOP).
Definition symop T := let: Pack _ _ ops := T return sym T -> n_ary_op T in ops.

Inductive term S := Var of nat | App of S & seq (term S).

Lemma term_ind' : forall S (P : term S -> Type),
  (forall i, P (Var S i)) ->
  (forall s a, foldr prod True (map P a) -> P (App s a)) ->
  (forall t, P t).
Proof.
move=> S P P_V P_A; pose fix sz (t : term S) :=
  if t is App _ a then (foldr maxn 0 (map sz a)).+1 else 0.
move=> t; elim: {t}(sz t) {-2}t (leqnn (sz t)) => [|n IHn] [i | s a] //=.
rewrite ltnS => sz_a; apply: P_A; elim: a sz_a => //= t a IHa.
by rewrite geq_max; case/andP; move/IHn=> Pt; move/IHa.
Qed.

Bind Scope quote_scope with term.
Notation "''K_' i" := (Var _ i)
  (at level 8, i at level 2, format "''K_' i") : quote_scope.
Notation "''[' s x1 .. xn ]" := (App s (x1%QT :: .. [:: xn%QT] ..))
  (at level 0, s at level 2, x1, xn at level 8,
   format "''[' '[hv' s  x1  ..  xn ']' ]") : quote_scope.
Notation "''[' s ]" := (App s [::])
  (at level 0, s at level 2, format "''[' s ]") : quote_scope.

Section OneType.

Variable T : type.
Implicit Type P : Prop.
Implicit Type tP : tProp.

Definition Env := @id (seq T).

Fixpoint lookup i e : option T :=
  if i is i'.+1 then lookup i' (behead e) else ohead e.

Definition interp_app (iarg : term (sym T) -> option T) :=
  fix loop a n {struct a} : n.-ary T -> option T :=
  if n is n'.+1 return n.-ary T -> option T
  then fun f => if a is t :: a' then obind (loop a' n' \o f) (iarg t) else None
  else fun x => if a is [::] then Some x else None.

Fixpoint interp e t := match t with
 | Var i => lookup i e
 | App s a => bind_op (symop s) (interp_app (interp e) a)
 end.

Fixpoint wf (t : term (sym T)) :=
  match t with
  | App s a => let: NaryOp n _ := symop s in (n == size a) && all wf a
  | Var _ => true
  end.

Fixpoint eval x0 e t :=
  match t with
  | Var i => nth x0 e i
  | App s a =>
    odflt x0 (bind_op (symop s) (interp_app (fun x => Some (eval x0 e x)) a))
  end.

Lemma interp_wf_eval : forall y0 e t y,
  interp e t = Some y -> wf t /\ eval y0 e t = y.
Proof.
move=> y0 e t; elim/term_ind': t => [i|s a IHa] y /=.
  by elim: i e => [|i IHi] [|z e] //=; [case | elim: i {IHi} | exact: IHi].
case: symop => /= n x1.
elim: n x1 a IHa => [|n IHn] x1 [|f a] //=; first by move=> _  [].
case: (interp e f) => //= x []; case/(_ x)=> // -> ->; exact: IHn.
Qed.

Definition var_val := @id T.
Definition op_val := var_val.

Structure form e t P := Form {fval; _ : P -> interp e t = Some fval}.
Lemma formP : forall e t tP f, interp e t = Some (@fval e t tP f).
Proof. by move=> e t tP [x <-]. Qed.

Structure store i x P := Store {stval; _ : P -> lookup i stval = Some x}.
Canonical Structure head_store x e :=
  @Store 0 x True (Env (x :: Env e)) (fun _ => erefl _).
Lemma tail_store_subproof : forall i x y e tP s,
  e = @stval i x tP s -> lookup i.+1 (y :: e) = Some x.
Proof. by move=> i x y _ tP [e /= <- //] ->. Qed.
Canonical Structure tail_store i x y e tP s :=
  Store (@tail_store_subproof i x y e tP s).

Lemma var_form_subproof : forall i x P (s : store i x P),
  P -> interp (stval s) 'K_i = Some (var_val x).
Proof. by move=> i x P []. Qed.
Canonical Structure var_form i x P s := Form (@var_form_subproof i x P s).

Lemma op_form_subproof : forall e t tP (f : form e t tP) x,
  x = @fval e t tP f -> interp e t = Some (op_val x).
Proof. by move=> e t tP f _ ->; exact: formP. Qed.

Canonical Structure op_form e t tP f x :=
  Form (@op_form_subproof e t tP f x).

Section OpForm.

Variables (s : sym T) (e : seq T).

Fixpoint OpForm_type a xa fa n :=
  if n is n'.+1 then
    forall x t tP f, OpForm_type (t :: a) (x :: xa) (@fval e t tP f :: fa) n'
  else form e (App s (rev a)) (map op_val (rev xa) = rev fa).

Definition OpForm_rechyp a (xa fa : seq T) n (x : n.-ary T) :=
  forall a', map op_val (rev xa) = rev fa ->
  interp e (App s (catrev a' a)) = interp_app (interp e) a' x.

Definition OpForm_rectype a xa fa n (x : n.-ary T) :=
  OpForm_rechyp a xa fa x -> OpForm_type a xa fa n.

Definition OpForm_basetype P x a :=
  (P -> interp e (App s a) = Some x) -> form e (App s a) P.

Lemma OpForm_recproof : forall a xa fa n (x1 : n.+1.-ary T),
  forall x t tP f, OpForm_rechyp a xa fa x1 ->
  OpForm_rechyp (t :: a) (x :: xa) (@fval e t tP f :: fa) (x1 x).
Proof.
move=> a xa fa n x1 x t tP f IHx a'; move/(_ (t :: a')): IHx => /=.
rewrite !map_id (formP f) /= => IHx; case/(can_inj (@revK _)) => -> eq_xa.
by rewrite {}IHx ?eq_xa.
Qed.

Fixpoint OpForm_rec a xa fa n : forall x, @OpForm_rectype a xa fa n x :=
  if n is _.+1 return forall x, @OpForm_rectype a xa fa n x then
  fun _ IHx _ _ _ _ => OpForm_rec (OpForm_recproof IHx) else
  fun x IHx =>
    (if rev a is (t :: a') as rev_a return OpForm_basetype _ _ rev_a then
     fun IHx => Form IHx else fun IHx => Form IHx) (IHx [::]).

Lemma OpForm_subproof : bind_op (symop s) (OpForm_rechyp [::] [::] [::]).
Proof. by case def_s: (symop s) => [n x] a _; rewrite /= def_s. Qed.

Definition OpForm :=
  (let: (op/n)%QOP as op_n := symop s
   return (bind_op op_n _ : Prop) -> @OpForm_type _ _ _ (arity op_n) in
   @OpForm_rec _ _ _ n op)
   OpForm_subproof.

End OpForm.

Section GenSimp.

Variable simp : seq T -> term (sym T) -> option T.

Definition simp_axiom := forall e t x y,
  interp e t = Some x -> simp e t = Some y -> x = y.

Hypothesis simpP : simp_axiom.

Structure closed := Closed {closed_val :> seq T}.
Canonical Structure head_closed := Closed (Env [::]).
Canonical Structure tail_closed x (ce : closed) := Closed (x :: ce).
Inductive close : seq T -> Prop := Close (ce : closed) : close ce.
Canonical Structure close_tProp ce := TProp (Close ce).

Lemma simp_form : forall e t y ptP,
  forall f : form (Env e) t
      (@postProp_statement (close (Env e) /\ simp e t = Some y) ptP),
  fval f = y.
Proof.
move=> e t y [tP [_ def_y]] [x /= def_x]; apply: simpP def_y; exact: def_x.
Qed.

End GenSimp.

Definition Econs := Cons.
Definition Etag of nat := @idfun.
Definition Enil := Nil.

Fixpoint simp_env {T'} e i :=
  if e is x :: e' then omap (Econs (Etag i x)) (simp_env e' i.+1)
  else Some (Enil T').

Notation "' 'K_' i := x" := (Etag i x)
  (at level 200, format "' 'K_' i  :=  x") : quote_tag_scope.
Arguments Scope Econs [type_scope quote_tag_scope _].

Notation "[ 'env' d1 ; .. ; d_n ]" := (Econs d1 .. (Econs d_n (Enil _)) ..)
  (at level 0, format "[ 'env' '['  d1 ; '/'  .. ; '/'  d_n ] ']'")
   : quote_scope.

Notation "[ 'env' ]" := (Enil _)
  (at level 0, format "[ 'env' ]") : quote_scope.

Lemma unquote_default : false -> T. Proof. by []. Qed.
Definition unquote e t :=
  if interp e t is Some x as ox return ox -> T then fun _ => x else
  unquote_default.

Arguments Scope unquote [quote_scope quote_scope _].

Lemma end_unquote : true. Proof. by []. Qed.
Definition simp_quote e t :=
  obind (fun e' =>
   (if interp e' t as b return (b -> _) -> _ then
      fun wf_t' => Some (unquote (wf_t' end_unquote))
   else fun _ => None) id)
  (simp_env e 0).

Lemma simp_quoteP : simp_axiom simp_quote.
Proof.
rewrite /simp_quote => e t x y def_x.
suff ->: simp_env e 0 = Some e by rewrite /unquote /= def_x; case.
by elim: e {def_x} 0 => //= z e IHe i; rewrite IHe.
Qed.

Definition quote := simp_form simp_quoteP.

End OneType.

End Quotation.

Canonical Structure Quotation.head_store.
Canonical Structure Quotation.tail_store.
Canonical Structure Quotation.var_form.
Canonical Structure Quotation.op_form.
Canonical Structure Quotation.head_closed.
Canonical Structure Quotation.tail_closed.
Canonical Structure Quotation.close_tProp.

Notation QuoteType sf := (Quotation.Pack sf%QOP).
Notation "f / n" := (@Quotation.NaryOp _ n f) : n_ary_op_scope.

Notation OpForm := Quotation.OpForm.

Notation "''K_' i" := (Quotation.Var _ i)
  (at level 8, i at level 2, format "''K_' i") : quote_scope.
Notation "''[' s x1 .. xn ]" :=
  (Quotation.App s (x1%QT :: .. [:: xn%QT] ..))
  (at level 0, s at level 2, x1, xn at level 8,
   format "''[' s '[hv'  x1 '/'  .. '/'  xn ']' ]") : quote_scope.
Notation "''[' s ]" := (Quotation.App s [::])
  (at level 0, s at level 2, format "''[' s ]") : quote_scope.
Notation "' 'K_' i := x" := (Quotation.Etag i x)
  (at level 200, format "' 'K_' i  :=  x") : quote_tag_scope.
Arguments Scope Quotation.Econs [type_scope quote_tag_scope _].
Notation "[ 'env' d1 ; .. ; d_n ]" :=
  (Quotation.Econs d1 .. (Quotation.Econs d_n (Quotation.Enil _)) ..)
  (at level 0, format "[ 'env' '['  d1 ; '/'  .. ; '/'  d_n ] ']'")
   : quote_scope.
Notation "[ 'env' ]" := (Quotation.Enil _)
  (at level 0, format "[ 'env' ]") : quote_scope.

Arguments Scope Quotation.unquote [_ quote_scope quote_scope _].
Notation unquote e t := (@Quotation.unquote _ e t%QT _).

CoInductive bool_sym := bTrue | bAnd.
Canonical Structure bool_quoteType :=
  QuoteType (fun s => match s with bTrue => true/0 | bAnd => andb/2 end).
Canonical Structure and_form := Eval hnf in OpForm bAnd.
Canonical Structure true_form := Eval hnf in OpForm bTrue.

Lemma try_bquote : forall b1 b2 b3,
  false && b1 && (b2 && true && b3) && (b2 && b1 && b2) = false && b2.
Proof.
move=> b1 b2 b3.
Time rewrite Quotation.quote.
Time rewrite !Quotation.quote.
by [].
Qed.

Fixpoint bstore s bt := match bt with
| 'K_i => set_nth false s i true
| '[bAnd t1 t2] => bstore (bstore s t1) t2
| _ => s
end%QT.

Fixpoint bread ot i s := match s with
| [::] => odflt '[bTrue] ot
| true :: s' => bread (Some (oapp (fun t => '[bAnd t 'K_i]) 'K_i ot)) i.+1 s'
| false :: s' => bread ot i.+1 s'
end%QT.

Fixpoint bnormed t i := match t with
| '[bAnd t' 'K_j] => bnormed t' 1
| 'K_j => i > 0
| '[bTrue] => i == 0
| _ => false
end%QT.

Definition bsimp_fn e t :=
  if bnormed t 0 then None else
  Quotation.interp e (bread None 0 (bstore [::] t)).

Lemma bsimpP : Quotation.simp_axiom bsimp_fn.
Proof.
pose oand ob1 ob2 := obind (fun b1 => omap (andb b1) ob2) ob1.
have [oaC oaA oaI]: [/\ commutative oand, associative oand & idempotent oand].
  by split; do 6?case=> //.
have oa1: left_id (Some true) oand by case=> [[]|].
rewrite /bsimp_fn => e t b b'; case: bnormed => //=.
set ie := Quotation.interp e; set s := [::] => def_b.
pose ir j s := ie (bread None j s).
suff{b'} storeP: ir 0 (bstore s t) = oand (ir 0 s) (Some b).
  by rewrite [ie _]storeP => [[]].
elim/Quotation.term_ind': t s => [i | op a IHa] /= s in b def_b *; last first.
  case: op def_b; first by case: a {IHa} => //= <-; rewrite oaC oa1.
  case: a IHa => //= t1; rewrite /ie /= -/ie; case: (ie _) => //= b1 [] //= t2.
  case: (ie t2) => //= b2 [] //= [IHb1 [IHb2 _]] [<-].
  by rewrite (IHb2 _ b2) // (IHb1 _ b1) // -oaA.
have irT: forall s' j, ir j (true :: s') = oand (ie 'K_j)%QT (ir j.+1 s').
  rewrite /ir /= => s' j; move: s' j ('K_j)%QT.
  by elim=> [|[|] s' IHs] j u; first 1 [rewrite oaC oa1] || rewrite !IHs -?oaA.
rewrite -{}def_b -{2}[i]addn0; elim: i 0 s => [|i IHi] j.
  case=> [|bj s]; first by rewrite oa1.
  by case: bj; rewrite !irT oaC // -oaA oaI.
rewrite addSnnS; case=> [|[|] s]; last exact: IHi.
  by rewrite /= -set_nth_nil [ir _ _]IHi.
by rewrite !irT IHi oaA.
Qed.

Definition bsimp := Quotation.simp_form bsimpP.

Lemma try_bsimp : forall b1 b2 b3,
  true && b1 && (b2 && b3) && (b2 && b1 && b2) = b1 && b2 && true && b3.
Proof.
move=> b1 b2 b3.
Time rewrite bsimp.
Time rewrite !bsimp.
by [].
Qed.
Print try_bsimp.



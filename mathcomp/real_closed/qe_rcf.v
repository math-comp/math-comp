(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype.
From mathcomp
Require Import finfun path matrix.
From mathcomp
Require Import bigop ssralg poly polydiv ssrnum zmodp div ssrint.
From mathcomp
Require Import polyorder polyrcf interval polyXY.
From mathcomp
Require Import qe_rcf_th ordered_qelim mxtens.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.

Local Open Scope nat_scope.
Local Open Scope ring_scope.

Definition grab (X Y : Type) (pattern : Y -> Prop) (P : Prop -> Prop) 
           (y : X) (f : X -> Y) :
           (let F := f in P (forall x, y = x -> pattern (F x)))
           -> P (forall x : X, y = x -> pattern (f x)) := id.

Definition grab_eq X Y u := @grab X Y (fun v => u = v :> Y).

Tactic Notation "grab_eq" ident(f) open_constr(PAT1) :=
  let Edef := fresh "Edef" in
  let E := fresh "E" in
  move Edef: PAT1 => E;
  move: E Edef;
  elim/grab_eq: _ => f _ <-.

Import ord.

Section QF.

Variable R : Type.

Inductive term : Type :=
| Var of nat
| Const of R
| NatConst of nat
| Add of term & term
| Opp of term
| NatMul of term & nat
| Mul of term & term
| Exp of term & nat.

Inductive formula : Type :=
| Bool of bool
| Equal of term & term
| Lt of term & term
| Le of term & term
| And of formula & formula
| Or of formula & formula
| Implies of formula & formula
| Not of formula.

Coercion rterm_to_term := fix loop (t : term) : GRing.term R :=
  match t with
    | Var x => GRing.Var _ x
    | Const x => GRing.Const x
    | NatConst n => GRing.NatConst _ n
    | Add u v => GRing.Add (loop u) (loop v)
    | Opp u => GRing.Opp (loop u)
    | NatMul u n  => GRing.NatMul (loop u) n
    | Mul u v => GRing.Mul (loop u) (loop v)
    | Exp u n => GRing.Exp (loop u) n
  end.

Coercion qfr_to_formula := fix loop (f : formula) : ord.formula R :=
  match f with
    | Bool b => ord.Bool b
    | Equal x y => ord.Equal x y
    | Lt x y => ord.Lt x y
    | Le x y => ord.Le x y
    | And f g => ord.And (loop f) (loop g)
    | Or f g => ord.Or (loop f) (loop g)
    | Implies f g => ord.Implies (loop f) (loop g)
    | Not f => ord.Not (loop f)
  end.

Definition to_rterm := fix loop (t : GRing.term R) : term :=
  match t with
    | GRing.Var x => Var x
    | GRing.Const x => Const x
    | GRing.NatConst n => NatConst n
    | GRing.Add u v => Add (loop u) (loop v)
    | GRing.Opp u => Opp (loop u)
    | GRing.NatMul u n  => NatMul (loop u) n
    | GRing.Mul u v => Mul (loop u) (loop v)
    | GRing.Exp u n => Exp (loop u) n
    | _ => NatConst 0
  end.

End QF.

Bind Scope qf_scope with term.
Bind Scope qf_scope with formula.
Delimit Scope qf_scope with qfT.
Arguments Add _ _%qfT _%qfT.
Arguments Opp _ _%qfT.
Arguments NatMul _ _%qfT _%N.
Arguments Mul _ _%qfT _%qfT.
Arguments Mul _ _%qfT _%qfT.
Arguments Exp _ _%qfT _%N.
Arguments Equal _ _%qfT _%qfT.
Arguments And _ _%qfT _%qfT.
Arguments Or _ _%qfT _%qfT.
Arguments Implies _ _%qfT _%qfT.
Arguments Not _ _%qfT.

Arguments Bool [R].
Prenex Implicits Const Add Opp NatMul Mul Exp Bool Unit And Or Implies Not Lt.
Prenex Implicits to_rterm.

Notation True := (Bool true).
Notation False := (Bool false).

Notation "''X_' i" := (Var _ i) : qf_scope.
Notation "n %:R" := (NatConst _ n) : qf_scope.
Notation "x %:T" := (Const x) : qf_scope.
Notation "0" := 0%:R%qfT : qf_scope.
Notation "1" := 1%:R%qfT : qf_scope.
Infix "+" := Add : qf_scope.
Notation "- t" := (Opp t) : qf_scope.
Notation "t - u" := (Add t (- u)) : qf_scope.
Infix "*" := Mul : qf_scope.
Infix "*+" := NatMul : qf_scope.
Infix "^+" := Exp : qf_scope.
Notation "t ^- n" := (t^-1 ^+ n)%qfT : qf_scope.
Infix "==" := Equal : qf_scope.
Infix "<%" := Lt : qf_scope.
Infix "<=%" := Le : qf_scope.
Infix "/\" := And : qf_scope.
Infix "\/" := Or : qf_scope.
Infix "==>" := Implies : qf_scope.
Notation "~ f" := (Not f) : qf_scope.
Notation "x != y" := (Not (x == y)) : qf_scope.

Section evaluation.

Variable R : realDomainType.

Fixpoint eval (e : seq R) (t : term R) {struct t} : R :=
  match t with
  | ('X_i)%qfT => e`_i
  | (x%:T)%qfT => x
  | (n%:R)%qfT => n%:R
  | (t1 + t2)%qfT => eval e t1 + eval e t2
  | (- t1)%qfT => - eval e t1
  | (t1 *+ n)%qfT => eval e t1 *+ n
  | (t1 * t2)%qfT => eval e t1 * eval e t2
  | (t1 ^+ n)%qfT => eval e t1 ^+ n
  end.

Lemma evalE (e : seq R) (t : term R) : eval e t = GRing.eval e t.
Proof. by elim: t=> /=; do ?[move->|move=> ?]. Qed.

Definition qf_eval e := fix loop (f : formula R) : bool :=
  match f with
  | Bool b => b
  | t1 == t2 => (eval e t1 == eval e t2)%bool
  | t1 <% t2 => (eval e t1 < eval e t2)%bool
  | t1 <=% t2 => (eval e t1 <= eval e t2)%bool
  | f1 /\ f2 => loop f1 && loop f2
  | f1 \/ f2 => loop f1 || loop f2
  | f1 ==> f2 => (loop f1 ==> loop f2)%bool
  | ~ f1 => ~~ loop f1
  end%qfT.

Lemma qf_evalE (e : seq R) (f : formula R) : qf_eval e f = ord.qf_eval e f.
Proof. by elim: f=> /=; do ?[rewrite evalE|move->|move=> ?]. Qed.

Lemma to_rtermE (t : GRing.term R) :
  GRing.rterm t -> to_rterm t = t :> GRing.term _.
Proof.
elim: t=> //=; do ?
  [ by move=> u hu v hv /andP[ru rv]; rewrite hu ?hv
  | by move=> u hu *; rewrite hu].
Qed.

End evaluation.

Import Pdiv.Ring.

Definition bind_def T1 T2 T3 (f : (T1 -> T2) -> T3) (k : T1 -> T2)  := f k.
Notation "'bind' x <- y ; z" :=
  (bind_def y (fun x => z)) (at level 99, x at level 0, y at level 0,
    format "'[hv' 'bind'  x  <-  y ;  '/' z ']'").

Section ProjDef.

Variable F : realFieldType.

Notation fF := (formula  F).
Notation tF := (term  F).
Definition polyF := seq tF.

Lemma qf_formF (f : fF) : qf_form f.
Proof. by elim: f=> // *; apply/andP; split. Qed.

Lemma rtermF (t : tF) : GRing.rterm t.
Proof. by elim: t=> //=; do ?[move->|move=> ?]. Qed.

Lemma rformulaF (f : fF) : rformula f.
Proof. by elim: f=> /=; do ?[rewrite rtermF|move->|move=> ?]. Qed.

Section If.

Implicit Types (pf tf ef : formula F).

Definition If pf tf ef := (pf /\ tf \/ ~ pf /\ ef)%qfT.

End If.

Notation "'If' c1 'Then' c2 'Else' c3" := (If c1 c2 c3)
  (at level 200, right associativity, format
"'[hv   ' 'If'  c1  '/' '[' 'Then'  c2  ']' '/' '[' 'Else'  c3 ']' ']'").

Notation cps T := ((T -> fF) -> fF).

Section Pick.

Variables (I : finType) (pred_f then_f : I -> fF) (else_f : fF).

Definition Pick :=
  \big[Or/False]_(p : {ffun pred I})
    ((\big[And/True]_i (if p i then pred_f i else ~ pred_f i))
    /\ (if pick p is Some i then then_f i else else_f))%qfT.

Lemma eval_Pick e (qev := qf_eval e) :
  let P i := qev (pred_f i) in
  qev Pick = (if pick P is Some i then qev (then_f i) else qev else_f).
Proof.
move=> P; rewrite ((big_morph qev) false orb) //= big_orE /=.
apply/existsP/idP=> [[p] | true_at_P].
  rewrite ((big_morph qev) true andb) //= big_andE /=.
  case/andP=> /forallP eq_p_P.
  rewrite (@eq_pick _ _ P) => [|i]; first by case: pick.
  by move/(_ i): eq_p_P => /=; case: (p i) => //=; move/negbTE.
exists [ffun i => P i] => /=; apply/andP; split.
  rewrite ((big_morph qev) true andb) //= big_andE /=.
  by apply/forallP=> i; rewrite /= ffunE; case Pi: (P i) => //=; apply: negbT.
rewrite (@eq_pick _ _ P) => [|i]; first by case: pick true_at_P.
by rewrite ffunE.
Qed.

End Pick.

Fixpoint eval_poly (e : seq F) pf :=
  if pf is c :: qf then (eval_poly e qf) * 'X + (eval e c)%:P else 0.

Lemma eval_polyP e p : eval_poly e p = Poly (map (eval e) p).
Proof. by elim: p=> // a p /= ->; rewrite cons_poly_def. Qed.

Fixpoint Size (p : polyF) : cps nat := fun k =>
  if p is c :: q then
    bind n <- Size q;
    if n is m.+1 then k m.+2
      else If c == 0 Then k 0%N Else k 1%N
    else k 0%N.

Definition Isnull (p : polyF) : cps bool := fun k =>
  bind n <- Size p; k (n == 0%N).

Definition LtSize (p q : polyF) : cps bool := fun k =>
  bind n <- Size p; bind m <- Size q; k (n < m)%N.

Fixpoint LeadCoef p : cps tF := fun k =>
  if p is c :: q then
    bind l <- LeadCoef q; If l == 0 Then k c Else k l
    else k (Const 0).

Fixpoint AmulXn (a : tF) (n : nat) : polyF:=
  if n is n'.+1 then (Const 0) :: (AmulXn a n') else [::a].

Fixpoint AddPoly (p q : polyF) :=
  if p is a::p' then
    if q is b::q' then (a + b)%qfT :: (AddPoly p' q')
      else p
    else q.
Local Infix "++" := AddPoly : qf_scope.

Definition ScalPoly (c : tF) (p : polyF) : polyF := map (Mul c) p.
Local Infix "*:" := ScalPoly : qf_scope.

Fixpoint MulPoly (p q : polyF) := if p is a :: p'
    then (a *: q ++ (0 :: (MulPoly p' q)))%qfT else [::].
Local Infix "**" := MulPoly (at level 40) : qf_scope.

Lemma map_poly0 (R R' : ringType) (f : R -> R') : map_poly f 0 = 0.
Proof. by rewrite map_polyE polyseq0. Qed.

Definition ExpPoly p n := iterop n MulPoly p [::1%qfT].
Local Infix "^^+" := ExpPoly (at level 29) : qf_scope.

Definition OppPoly := ScalPoly (@Const F (-1)).
Local Notation "-- p" := (OppPoly p) (at level 35) : qf_scope.
Local Notation "p -- q" := (p ++ (-- q))%qfT (at level 50) : qf_scope.

Definition NatMulPoly n := ScalPoly (NatConst F n).
Local Infix "+**" := NatMulPoly (at level 40) : qf_scope.

Fixpoint Horner (p : polyF) (x : tF) : tF :=
  if p is a :: p then (Horner p x * x + a)%qfT else 0%qfT.

Fixpoint Deriv (p : polyF) : polyF :=
  if p is a :: q then (q ++ (0 :: Deriv q))%qfT else [::].

Fixpoint Rediv_rec_loop (q : polyF) sq cq
  (c : nat) (qq r : polyF) (n : nat) {struct n} :
  cps (nat * polyF * polyF) := fun k =>
  bind sr <- Size r;
  if (sr < sq)%N then k (c, qq, r) else
    bind lr <- LeadCoef r;
    let m := AmulXn lr (sr - sq) in
    let qq1 := (qq ** [::cq] ++ m)%qfT in
    let r1 := (r ** [::cq] -- m ** q)%qfT in
    if n is n1.+1 then Rediv_rec_loop q sq cq c.+1 qq1 r1 n1 k
    else k (c.+1, qq1, r1).

 Definition Rediv (p : polyF) (q : polyF) : cps (nat * polyF * polyF) :=
  fun k =>
  bind b <- Isnull q;
  if b then k (0%N, [::Const 0], p)
    else bind sq <- Size q;
      bind sp <- Size p;
      bind lq <- LeadCoef q;
      Rediv_rec_loop q sq lq 0 [::Const 0] p sp k.

Definition Rmod (p : polyF) (q : polyF) (k : polyF -> fF) : fF :=
  Rediv p q (fun d => k d.2)%PAIR.
Definition Rdiv (p : polyF) (q : polyF) (k : polyF -> fF) : fF :=
  Rediv p q (fun d => k d.1.2)%PAIR.
Definition Rscal (p : polyF) (q : polyF) (k : nat -> fF) : fF :=
  Rediv p q (fun d => k d.1.1)%PAIR.
Definition Rdvd (p : polyF) (q : polyF) (k : bool -> fF) : fF :=
  bind r <- Rmod p q; bind r_null <- Isnull r; k r_null.

Fixpoint rgcdp_loop n (pp qq : {poly F}) {struct n} :=
  if rmodp pp qq == 0 then qq
    else if n is n1.+1 then rgcdp_loop n1 qq (rmodp pp qq)
        else rmodp pp qq.

Fixpoint Rgcd_loop n pp qq k {struct n} :=
  bind r <- Rmod pp qq; bind b <- Isnull r;
  if b then (k qq)
    else if n is n1.+1 then Rgcd_loop n1 qq r k else k r.

Definition Rgcd (p : polyF) (q : polyF) : cps polyF := fun k =>
  let aux p1 q1 k := (bind b <- Isnull p1;
    if b then k q1 else bind n <- Size p1; Rgcd_loop n p1 q1 k) in
  bind b <- LtSize p q;
  if b then aux q p k else aux p q k.

Fixpoint BigRgcd (ps : seq polyF) : cps (seq tF) := fun k =>
  if ps is p :: pr then bind r <- BigRgcd pr; Rgcd p r k else k [::Const 0].

Fixpoint Changes (s : seq tF) : cps nat := fun k =>
  if s is a :: q then
    bind v <- Changes q;
    If (Lt (a * head 0 q) 0)%qfT Then k (1 + v)%N Else k v
    else k 0%N.

Fixpoint SeqPInfty (ps : seq polyF) : cps (seq tF) := fun k =>
  if ps is p :: ps then
    bind lp <- LeadCoef p;
    bind lps <- SeqPInfty ps;
    k (lp :: lps)
  else k [::].

Fixpoint SeqMInfty (ps : seq polyF) : cps (seq tF) := fun k =>
  if ps is p :: ps then
    bind lp <- LeadCoef p;
    bind sp <- Size p;
    bind lps <- SeqMInfty ps;
    k ((-1)%:T ^+ (~~ odd sp) * lp :: lps)%qfT
  else k [::].

Definition ChangesPoly ps : cps int := fun k =>
  bind mps <- SeqMInfty ps;
  bind pps <- SeqPInfty ps;
  bind vm <- Changes mps; bind vp <- Changes pps; k (vm%:Z - vp%:Z).

Definition NextMod (p q : polyF) : cps polyF := fun k =>
  bind lq <- LeadCoef q;
  bind spq <- Rscal p q;
  bind rpq <- Rmod p q; k (- lq ^+ spq *: rpq)%qfT.

Fixpoint ModsAux (p q : polyF) n : cps (seq polyF) := fun k =>
    if n is m.+1
      then
        bind p_eq0 <- Isnull p;
        if p_eq0 then k [::]
        else
          bind npq <- NextMod p q;
          bind ps <- ModsAux q npq m;
          k (p :: ps)
      else k [::].

Definition Mods (p q : polyF) : cps (seq polyF) := fun k =>
  bind sp <- Size p; bind sq <- Size q;
  ModsAux p q (maxn sp sq.+1) k.

Definition PolyComb (sq : seq polyF) (sc : seq int) :=
  reducebig [::1%qfT] (iota 0 (size sq))
  (fun i => BigBody i MulPoly true (nth [::] sq i ^^+ comb_exp sc`_i)%qfT).

Definition Pcq sq i := (nth [::] (map (PolyComb sq) (sg_tab (size sq))) i).

Definition TaqR (p : polyF) (q : polyF) : cps int := fun k =>
  bind r <- Mods p (Deriv p ** q)%qfT; ChangesPoly r k.

Definition TaqsR (p : polyF) (sq : seq polyF) (i : nat) : cps tF :=
  fun k => bind n <- TaqR p (Pcq sq i); k ((n%:~R) %:T)%qfT.

Fixpoint ProdPoly T (s : seq T) (f : T -> cps polyF) : cps polyF := fun k =>
  if s is a :: s then
    bind fa <- f a;
    bind fs <- ProdPoly s f;
    k (fa ** fs)%qfT
  else k [::1%qfT].

Definition BoundingPoly (sq : seq polyF) : polyF :=
  Deriv (reducebig [::1%qfT] sq (fun i => BigBody i MulPoly true i)).

Definition Coefs (n i : nat) : tF :=
  Const (match n with
    | 0 => (i == 0%N)%:R
    | 1 => [:: 2%:R^-1; 2%:R^-1; 0]`_i
    | n => coefs _ n i
  end).

Definition CcountWeak (p : polyF) (sq : seq polyF) : cps tF := fun k =>
  let fix aux s (i : nat) k := if i is i'.+1
    then bind x <- TaqsR p sq i';
      aux (x * (Coefs (size sq) i') + s)%qfT i' k
    else k s in
   aux 0%qfT (3 ^ size sq)%N k.

Definition CcountGt0 (sp sq : seq polyF) : fF :=
  bind p <- BigRgcd sp; bind p0 <- Isnull p;
  if ~~ p0 then
    bind c <- CcountWeak p sq;
    Lt 0%qfT c
  else
    let bq := BoundingPoly sq in
      bind cw <- CcountWeak bq sq;
      ((reducebig True sq (fun q =>
          BigBody q And true (LeadCoef q (fun lq => Lt 0 lq))))
        \/ ((reducebig True sq (fun q =>
         BigBody q And true
          (bind sq <- Size q;
          bind lq <- LeadCoef q;
          Lt 0 ((Opp 1) ^+ (sq).-1 * lq)
        ))) \/ Lt 0 cw))%qfT.


Fixpoint abstrX (i : nat) (t : tF) : polyF :=
  (match t with
    | 'X_n => if n == i then [::0; 1] else [::t]
    | - x => -- abstrX i x
    | x + y => abstrX i x ++ abstrX i y
    | x * y => abstrX i x ** abstrX i y
    | x *+ n => n +** abstrX i x
    | x ^+ n => abstrX i x ^^+ n
    | _ => [::t]
  end)%qfT.

Definition wproj (n : nat) (s : seq (GRing.term F) * seq (GRing.term F)) :
  formula F :=
  let sp := map (abstrX n \o to_rterm) s.1%PAIR in
  let sq := map (abstrX n \o to_rterm) s.2%PAIR in
    CcountGt0 sp sq.

Definition rcf_sat := proj_sat wproj.

End ProjDef.

Section ProjCorrect.

Variable F : rcfType.
Implicit Types (e : seq F).

Notation fF := (formula  F).
Notation tF := (term  F).
Notation polyF := (polyF F).

Notation "'If' c1 'Then' c2 'Else' c3" := (If c1 c2 c3)
  (at level 200, right associativity, format
"'[hv   ' 'If'  c1  '/' '[' 'Then'  c2  ']' '/' '[' 'Else'  c3 ']' ']'").

Notation cps T := ((T -> fF) -> fF).

Local Infix "**" := MulPoly (at level 40) : qf_scope.
Local Infix "+**" := NatMulPoly (at level 40) : qf_scope.
Local Notation "-- p" := (OppPoly p) (at level 35) : qf_scope.
Local Notation "p -- q" := (p ++ (-- q))%qfT (at level 50) : qf_scope.
Local Infix "^^+" := ExpPoly (at level 29) : qf_scope.
Local Infix "**" := MulPoly (at level 40) : qf_scope.
Local Infix "*:" := ScalPoly : qf_scope.
Local Infix "++" := AddPoly : qf_scope.

Lemma eval_If e pf tf ef (ev := qf_eval e) :
  ev (If pf Then tf Else ef) = (if ev pf then ev tf else ev ef).
Proof. by unlock (If _ Then _ Else _)=> /=; case: ifP => _; rewrite ?orbF. Qed.

Lemma eval_Size k p e :
  qf_eval e (Size p k) = qf_eval e (k (size (eval_poly e p))).
Proof.
elim: p e k=> [|c p ihp] e k; first by rewrite size_poly0.
rewrite ihp /= size_MXaddC -size_poly_eq0; case: size=> //.
by rewrite eval_If /=; case: (_ == _).
Qed.

Lemma eval_Isnull k p e : qf_eval e (Isnull p k)
  = qf_eval e (k (eval_poly e p == 0)).
Proof. by rewrite eval_Size size_poly_eq0. Qed.

Lemma eval_LeadCoef e p k k' :
  (forall x, qf_eval e (k x) = (k' (eval e x))) ->
  qf_eval e (LeadCoef p k) = k' (lead_coef (eval_poly e p)).
Proof.
move=> Pk; elim: p k k' Pk=> [|a p ihp] k k' Pk //=.
  by rewrite lead_coef0 Pk.
rewrite (ihp _ (fun l => if l == 0 then qf_eval e (k a) else (k' l))); last first.
  by move=> x; rewrite eval_If /= !Pk.
rewrite lead_coef_eq0; have [->|p_neq0] := altP (_ =P 0).
  by rewrite mul0r add0r lead_coefC.
rewrite lead_coefDl ?lead_coefMX ?size_mulX // ltnS size_polyC.
by rewrite (leq_trans (leq_b1 _)) // size_poly_gt0.
Qed.

Arguments eval_LeadCoef [e p k].
Prenex Implicits eval_LeadCoef.

Lemma eval_AmulXn a n e : eval_poly e (AmulXn a n) = (eval e a)%:P * 'X^n.
Proof.
elim: n=> [|n] /=; first by rewrite expr0 mulr1 mul0r add0r.
by move->; rewrite addr0 -mulrA -exprSr.
Qed.

Lemma eval_AddPoly p q e :
  eval_poly e (p ++ q)%qfT = (eval_poly e p) + (eval_poly e q).
Proof.
elim: p q => [|a p Hp] q /=; first by rewrite add0r.
case: q => [|b q] /=; first by rewrite addr0.
by rewrite Hp mulrDl rmorphD /= !addrA [X in _ = X + _]addrAC.
Qed.

Lemma eval_ScalPoly e t p :
  eval_poly e (ScalPoly t p) = (eval e t) *: (eval_poly e p).
Proof.
elim: p=> [|a p ihp] /=; first by rewrite scaler0.
by rewrite ihp scalerDr scalerAl -!mul_polyC rmorphM.
Qed.

Lemma eval_MulPoly e p q :
  eval_poly e (p ** q)%qfT = (eval_poly e p) * (eval_poly e q).
Proof.
elim: p q=> [|a p Hp] q /=; first by rewrite mul0r.
rewrite eval_AddPoly /= eval_ScalPoly Hp.
by rewrite addr0 mulrDl addrC mulrAC mul_polyC.
Qed.

Lemma eval_ExpPoly e p n : eval_poly e (p ^^+ n)%qfT = (eval_poly e p) ^+ n.
Proof.
case: n=> [|n]; first by rewrite /= expr0 mul0r add0r.
rewrite /ExpPoly iteropS exprSr; elim: n=> [|n ihn] //=.
  by rewrite expr0 mul1r.
by rewrite eval_MulPoly ihn exprS mulrA.
Qed.

Lemma eval_NatMulPoly p n e :
  eval_poly e (n +** p)%qfT = (eval_poly e p) *+ n.
Proof.
elim: p; rewrite //= ?mul0rn // => c p ->.
rewrite mulrnDl mulr_natl polyC_muln; congr (_+_).
by rewrite -mulr_natl mulrAC -mulrA mulr_natl mulrC.
Qed.

Lemma eval_OppPoly p e : eval_poly e (-- p)%qfT = - eval_poly e p.
Proof.
elim: p; rewrite //= ?oppr0 // => t ts ->.
by rewrite !mulNr !opprD polyC_opp mul1r.
Qed.

Lemma eval_Horner e p x : eval e (Horner p x) = (eval_poly e p).[eval e x].
Proof. by elim: p => /= [|a p ihp]; rewrite !(horner0, hornerE) // ihp. Qed.

Lemma eval_ConstPoly e c : eval_poly e [::c] = (eval e c)%:P.
Proof. by rewrite /= mul0r add0r. Qed.

Lemma eval_Deriv e p : eval_poly e (Deriv p) = (eval_poly e p)^`().
Proof.
elim: p=> [|a p ihp] /=; first by rewrite deriv0.
by rewrite eval_AddPoly /= addr0 ihp !derivE.
Qed.

Definition eval_OpPoly :=
  (eval_MulPoly, eval_AmulXn, eval_AddPoly, eval_OppPoly, eval_NatMulPoly,
  eval_ConstPoly, eval_Horner, eval_ExpPoly, eval_Deriv, eval_ScalPoly).

Lemma eval_Changes e s k : qf_eval e (Changes s k)
  = qf_eval e (k (changes (map (eval e) s))).
Proof.
elim: s k=> //= a q ihq k; rewrite ihq eval_If /= -nth0.
by case: q {ihq}=> /= [|b q]; [rewrite /= mulr0 ltrr add0n | case: ltrP].
Qed.

Lemma eval_SeqPInfty e ps k k' :
  (forall xs, qf_eval e (k xs) = k' (map (eval e) xs)) ->
 qf_eval e (SeqPInfty ps k)
  = k' (map lead_coef (map (eval_poly e) ps)).
Proof.
elim: ps k k' => [|p ps ihps] k k' Pk /=; first by rewrite Pk.
set X := lead_coef _; grab_eq k'' X; apply: (eval_LeadCoef k'') => lp {X}.
rewrite (ihps _ (fun ps => k' (eval e lp :: ps))) => //= lps.
by rewrite Pk.
Qed.

Arguments eval_SeqPInfty [e ps k].
Prenex Implicits eval_SeqPInfty.

Lemma eval_SeqMInfty e ps k k' :
  (forall xs, qf_eval e (k xs) = k' (map (eval e) xs)) ->
 qf_eval e (SeqMInfty ps k)
  = k' (map (fun p : {poly F} => (-1) ^+ (~~ odd (size p)) * lead_coef p)
            (map (eval_poly e) ps)).
Proof.
elim: ps k k' => [|p ps ihps] k k' Pk /=; first by rewrite Pk.
set X := lead_coef _; grab_eq k'' X; apply: eval_LeadCoef => lp {X}.
rewrite eval_Size /= /k'' {k''}.
by set X := map _ _; grab_eq k'' X; apply: ihps => {X} lps; rewrite Pk.
Qed.

Arguments eval_SeqMInfty [e ps k].
Prenex Implicits eval_SeqMInfty.

Lemma eval_ChangesPoly e ps k : qf_eval e (ChangesPoly ps k) =
  qf_eval e (k (changes_poly (map (eval_poly e) ps))).
Proof.
rewrite (eval_SeqMInfty (fun mps =>
  qf_eval e (k ((changes mps)%:Z -
     (changes_pinfty  [seq eval_poly e i | i <- ps])%:Z)))) => // mps.
rewrite (eval_SeqPInfty (fun pps =>
  qf_eval e (k ((changes (map (eval e) mps))%:Z - (changes pps)%:Z)))) => // pps.
by rewrite !eval_Changes.
Qed.

Fixpoint redivp_rec_loop (q : {poly F}) sq cq
   (k : nat) (qq r : {poly F})(n : nat) {struct n} :=
    if (size r < sq)%N then (k, qq, r) else
    let m := (lead_coef r) *: 'X^(size r - sq) in
    let qq1 := qq * cq%:P + m in
    let r1 := r * cq%:P - m * q in
    if n is n1.+1 then redivp_rec_loop q sq cq k.+1 qq1 r1 n1 else (k.+1, qq1, r1).

Lemma redivp_rec_loopP q c qq r n : redivp_rec q c qq r n
    = redivp_rec_loop q (size q) (lead_coef q) c qq r n.
Proof. by elim: n c qq r => [| n Pn] c qq r //=; rewrite Pn. Qed.

Lemma eval_Rediv_rec_loop e q sq cq c qq r n k k'
  (d := redivp_rec_loop (eval_poly e q) sq (eval e cq)
    c (eval_poly e qq) (eval_poly e r) n) :
  (forall c qq r, qf_eval e (k (c, qq, r))
    = k' (c, eval_poly e qq, eval_poly e r)) ->
  qf_eval e (Rediv_rec_loop q sq cq c qq r n k) = k' d.
Proof.
move=> Pk; elim: n c qq r k Pk @d=> [|n ihn] c qq r k Pk /=.
  rewrite eval_Size /=; have [//=|gtq] := ltnP.
  set X := lead_coef _; grab_eq k'' X; apply: eval_LeadCoef => {X}.
  by move=> x /=; rewrite Pk /= !eval_OpPoly /= !mul_polyC.
rewrite eval_Size /=; have [//=|gtq] := ltnP.
set X := lead_coef _; grab_eq k'' X; apply: eval_LeadCoef => {X}.
by move=> x; rewrite ihn // !eval_OpPoly /= !mul_polyC.
Qed.

Arguments eval_Rediv_rec_loop [e q sq cq c qq r n k].
Prenex Implicits eval_Rediv_rec_loop.

Lemma eval_Rediv e p q k k' (d := (redivp (eval_poly e p) (eval_poly e q))) :
  (forall c qq r,  qf_eval e (k (c, qq, r)) = k' (c, eval_poly e qq, eval_poly e r)) ->
  qf_eval e (Rediv p q k) = k' d.
Proof.
move=> Pk; rewrite eval_Isnull /d unlock.
have [_|p_neq0] /= := boolP (_ == _); first by rewrite Pk /= mul0r add0r.
rewrite !eval_Size; set p' := eval_poly e p; set q' := eval_poly e q.
rewrite (eval_LeadCoef (fun lq =>
  k' (redivp_rec_loop q' (size q') lq 0 0 p' (size p')))) /=; last first.
  by move=> x; rewrite (eval_Rediv_rec_loop k') //= mul0r add0r.
by rewrite redivp_rec_loopP.
Qed.

Arguments eval_Rediv [e p q k].
Prenex Implicits eval_Rediv.

Lemma eval_NextMod e p q k k' :
  (forall p, qf_eval e (k p) = k' (eval_poly e p)) ->
  qf_eval e (NextMod p q k) =
  k' (next_mod (eval_poly e p) (eval_poly e q)).
Proof.
move=> Pk; set p' := eval_poly e p; set q' := eval_poly e q.
rewrite (eval_LeadCoef (fun lq =>
  k' (- lq ^+ rscalp p' q' *: rmodp p' q'))) => // lq.
rewrite (eval_Rediv (fun spq =>
  k' (- eval e lq ^+ spq.1.1%PAIR *: rmodp p' q'))) => //= spq _ _.
rewrite (eval_Rediv (fun mpq =>
  k' (- eval e lq ^+ spq *:  mpq.2%PAIR))) => //= _ _ mpq.
by rewrite Pk !eval_OpPoly.
Qed.

Arguments eval_NextMod [e p q k].
Prenex Implicits eval_NextMod.

Lemma eval_Rgcd_loop e n p q k k' :
  (forall p, qf_eval e (k p) = k' (eval_poly e p))
  -> qf_eval e (Rgcd_loop n p q k) =
    k' (rgcdp_loop n (eval_poly e p) (eval_poly e q)).
Proof.
elim: n p q k k'=> [|n ihn] p q k k' Pk /=.
  rewrite (eval_Rediv (fun r =>
    if r.2%PAIR == 0 then k' (eval_poly e q) else k' r.2%PAIR)) /=.
    by case: eqP.
  by move=> _ _ r; rewrite eval_Isnull; case: eqP.
pose q' := eval_poly e q.
rewrite (eval_Rediv (fun r =>
  if r.2%PAIR == 0 then k' q' else k' (rgcdp_loop n q' r.2%PAIR))) /=.
  by case: eqP.
move=> _ _ r; rewrite eval_Isnull; case: eqP; first by rewrite Pk.
by rewrite (ihn _ _ _ k').
Qed.

Lemma eval_Rgcd e p q k k' :
  (forall p, qf_eval e (k p) = k' (eval_poly e p)) ->
  qf_eval e (Rgcd p q k) =
  k' (rgcdp (eval_poly e p) (eval_poly e q)).
Proof.
move=> Pk; rewrite /Rgcd /LtSize !eval_Size /rgcdp.
case: ltnP=> _; rewrite !eval_Isnull; case: eqP=> // _;
by rewrite eval_Size; apply: eval_Rgcd_loop.
Qed.


Lemma eval_BigRgcd e ps k k' :
  (forall p, qf_eval e (k p) = k' (eval_poly e p)) ->
  qf_eval e (BigRgcd ps k) =
  k' (\big[@rgcdp _/0%:P]_(i <- ps) (eval_poly e i)).
Proof.
elim: ps k k'=> [|p sp ihsp] k k' Pk /=.
  by rewrite big_nil Pk /= mul0r add0r.
rewrite big_cons (ihsp _ (fun r => k' (rgcdp (eval_poly e p) r))) //.
by move=> r; apply: eval_Rgcd.
Qed.

Arguments eval_Rgcd [e p q k].
Prenex Implicits eval_Rgcd.


Fixpoint mods_aux (p q : {poly F}) (n : nat) : seq {poly F} :=
    if n is m.+1
      then if p == 0 then [::]
           else p :: (mods_aux q (next_mod p q) m)
      else [::].

Lemma eval_ModsAux e p q n k k' :
  (forall sp, qf_eval e (k sp) = k' (map (eval_poly e) sp)) ->
  qf_eval e (ModsAux p q n k) =
  k' (mods_aux (eval_poly e p) (eval_poly e q) n).
Proof.
elim: n p q k k'=> [|n ihn] p q k k' Pk; first by rewrite /= Pk.
rewrite /= eval_Isnull; have [|ep_neq0] := altP (_ =P _); first by rewrite Pk.
set q' := eval_poly e q; set p' := eval_poly e p.
rewrite (eval_NextMod (fun npq => k' (p' :: mods_aux q' npq n))) => // npq.
by rewrite (ihn _ _ _ (fun ps => k' (p' :: ps))) => // ps; rewrite Pk.
Qed.

Arguments eval_ModsAux [e p q n k].
Prenex Implicits eval_ModsAux.

Lemma eval_Mods e p q k k' :
  (forall sp, qf_eval e (k sp) = k' (map (eval_poly e) sp)) ->
  qf_eval e (Mods p q k) = k' (mods (eval_poly e p) (eval_poly e q)).
Proof. by move=> Pk; rewrite !eval_Size; apply: eval_ModsAux. Qed.

Arguments eval_Mods [e p q k].
Prenex Implicits eval_Mods.

Lemma eval_TaqR e p q k :
  qf_eval e (TaqR p q k) =
  qf_eval e (k (taqR (eval_poly e p) (eval_poly e q))).
Proof.
rewrite (eval_Mods (fun r => qf_eval e (k (changes_poly r)))).
  by rewrite !eval_OpPoly.
by move=> sp; rewrite !eval_ChangesPoly.
Qed.

Lemma eval_PolyComb e sq sc :
  eval_poly e (PolyComb sq sc) = poly_comb (map (eval_poly e) sq) sc.
Proof.
rewrite /PolyComb /poly_comb size_map.
rewrite -BigOp.bigopE -val_enum_ord -filter_index_enum !big_map.
apply: (big_ind2 (fun u v => eval_poly e u = v)).
+ by rewrite /= mul0r add0r.
+ by move=> x x' y y'; rewrite eval_MulPoly=> -> ->.
by move=> i _; rewrite eval_ExpPoly /= (nth_map [::]).
Qed.

Definition pcq (sq : seq {poly F}) i :=
  (map (poly_comb sq) (sg_tab (size sq)))`_i.

Lemma eval_Pcq e sq i :
  eval_poly e (Pcq sq i) = pcq (map (eval_poly e) sq) i.
Proof.
rewrite /Pcq /pcq size_map; move: (sg_tab _)=> s.
have [ge_is|lt_is] := leqP (size s) i.
  by rewrite !nth_default ?size_map // /=.
rewrite -(nth_map _ 0) ?size_map //; congr _`_i; rewrite -map_comp.
by apply: eq_map=> x /=; rewrite eval_PolyComb.
Qed.

Lemma eval_TaqsR e p sq i k k' :
  (forall x, qf_eval e (k x) = k' (eval e x)) ->
  qf_eval e (TaqsR p sq i k) =
  k' (taqsR (eval_poly e p) (map (eval_poly e) sq) i).
Proof. by move=> Pk; rewrite /TaqsR /taqsR eval_TaqR Pk /= eval_Pcq. Qed.

Arguments eval_TaqsR [e p sq i k].
Prenex Implicits eval_TaqsR.

Fact invmx_ctmat1 : invmx (map_mx (intr : int -> F) ctmat1) =
  \matrix_(i, j)
  (nth [::] [:: [::  2%:R^-1; - 2%:R^-1;  0];
                [::  2%:R^-1;   2%:R^-1; -1];
                [::        0;         0;  1]] i)`_j :> 'M[F]_3.
Proof.
rewrite -[lhs in lhs = _]mul1r; apply: (canLR (mulrK _)).
  exact: ctmat1_unit.
symmetry; rewrite /ctmat1.
apply/matrixP => i j; rewrite !(big_ord_recl, big_ord0, mxE) /=.
have halfP (K : numFieldType) : 2%:R^-1 + 2%:R^-1 = 1 :> K.
  by rewrite -mulr2n -[_ *+ 2]mulr_natl mulfV // pnatr_eq0.
move: i; do ?[case=> //=]; move: j; do ?[case=> //=] => _ _;
rewrite !(mulr1, mul1r, mulrN1, mulN1r, mulr0, mul0r, opprK);
by rewrite !(addr0, add0r, oppr0, subrr, addrA, halfP).
Qed.

Lemma eval_Coefs e n i : eval e (Coefs F n i) = coefs F n i.
Proof.
case: n => [|[|n]] //=; rewrite /coefs /=.
  case: i => [|i]; last first.
    by rewrite nth_default // size_map size_enum_ord expn0.
  rewrite (nth_map 0) ?size_enum_ord //.
  set O := _`_0; rewrite (_ : O = ord0).
    by rewrite ?castmxE ?cast_ord_id map_mx1 invmx1 mxE.
  by apply: val_inj => /=; rewrite nth_enum_ord.
have [lt_i3|le_3i] := ltnP i 3; last first.
  by rewrite !nth_default // size_map size_enum_ord.
rewrite /ctmat /= ?ntensmx1 invmx_ctmat1 /=.
rewrite (nth_map 0) ?size_enum_ord // castmxE /=.
rewrite !mxE !cast_ord_id //= nth_enum_ord //=.
by move: i lt_i3; do 3?case.
Qed.

Lemma eval_CcountWeak e p sq k k' :
  (forall x, qf_eval e (k x) = k' (eval e x)) ->
  qf_eval e (CcountWeak p sq k) =
  k' (ccount_weak (eval_poly e p) (map (eval_poly e) sq)).
Proof.
move=> Pk; rewrite /CcountWeak /ccount_weak.
set Aux := (fix Aux s i k := match i with 0 => _ | _ => _ end).
set aux := (fix aux s i := match i with 0 => _ | _ => _ end).
rewrite size_map -[0]/(eval e 0%qfT); move: 0%qfT=> x.
elim: (_ ^ _)%N k k' Pk x=> /= [|n ihn] k k' Pk x.
  by rewrite Pk.
rewrite (eval_TaqsR
  (fun y => k' (aux (y * (coefs F (size sq) n) + eval e x) n))).
  by rewrite size_map.
by move=> y; rewrite (ihn _ k') // -(eval_Coefs e).
Qed.

Arguments eval_CcountWeak [e p sq k].
Prenex Implicits eval_CcountWeak.

Lemma eval_ProdPoly e T s f k f' k' :
  (forall x k k', (forall p, (qf_eval e (k p) = k' (eval_poly e p))) ->
  qf_eval e (f x k) = k' (f' x)) ->
  (forall p, qf_eval e (k p) = k' (eval_poly e p)) ->
  qf_eval e (@ProdPoly _ T s f k) = k' (\prod_(x <- s) f' x).
Proof.
move=> Pf; elim: s k k'=> [|a s ihs] k k' Pk /=.
  by rewrite big_nil Pk /= !(mul0r, add0r).
rewrite (Pf _ _ (fun fa => k' (fa * \prod_(x <- s) f' x))).
  by rewrite big_cons.
move=> fa; rewrite (ihs _ (fun fs => k' (eval_poly e fa * fs))) //.
by move=> fs; rewrite Pk eval_OpPoly.
Qed.

Arguments eval_ProdPoly [e T s f k].
Prenex Implicits eval_ProdPoly.

Lemma eval_BoundingPoly e sq :
  eval_poly e (BoundingPoly sq) = bounding_poly (map (eval_poly e) sq).
Proof.
rewrite eval_Deriv -BigOp.bigopE; congr _^`(); rewrite big_map.
by apply: big_morph => [p q | ]/=; rewrite ?eval_MulPoly // mul0r add0r.
Qed.

Lemma eval_CcountGt0 e sp sq : qf_eval e (CcountGt0 sp sq) =
  ccount_gt0 (map (eval_poly e) sp) (map (eval_poly e) sq).
Proof.
pose sq' := map (eval_poly e) sq; rewrite /ccount_gt0.
rewrite (@eval_BigRgcd _ _ _ (fun p => if p != 0
  then 0 < ccount_weak p sq'
  else let bq := bounding_poly sq' in
    [|| \big[andb/true]_(q <- sq') (0 < lead_coef q),
     \big[andb/true]_(q <- sq') (0 < (-1) ^+ (size q).-1 * lead_coef q)
    | 0 < ccount_weak bq sq'])).
  by rewrite !big_map.
move=> p; rewrite eval_Isnull; case: eqP=> _ /=; last first.
  by rewrite (eval_CcountWeak (> 0)).
rewrite (eval_CcountWeak (fun n =>
   [|| \big[andb/true]_(q <- sq') (0 < lead_coef q),
    \big[andb/true]_(q <- sq') (0 < (-1) ^+ (size q).-1 * lead_coef q)
   | 0 < n ])).
  by rewrite eval_BoundingPoly.
move=> n /=; rewrite -!BigOp.bigopE !big_map; congr [|| _, _| _].
  apply: (big_ind2 (fun u v => qf_eval e u = v))=> //=.
    by move=> u v u' v' -> ->.
  by move=> i _; rewrite (eval_LeadCoef (> 0)).
apply: (big_ind2 (fun u v => qf_eval e u = v))=> //=.
  by move=> u v u' v' -> ->.
by move=> i _; rewrite eval_Size (eval_LeadCoef (fun lq =>
  (0 < (-1) ^+ (size (eval_poly e i)).-1 * lq))).
Qed.

Lemma abstrXP e i t x :
  (eval_poly e (abstrX i t)).[x] = eval (set_nth 0 e i x) t.
Proof.
elim: t.
- move=> n /=; case ni: (_ == _);
    rewrite //= ?(mul0r,add0r,addr0,polyC1,mul1r,hornerX,hornerC);
    by rewrite // nth_set_nth /= ni.
- by move=> r; rewrite /= mul0r add0r hornerC.
- by move=> r; rewrite /= mul0r add0r hornerC.
- by move=> t tP s sP; rewrite /= eval_AddPoly hornerD tP ?sP.
- by move=> t tP; rewrite /= eval_OppPoly hornerN tP.
- by move=> t tP n; rewrite /= eval_NatMulPoly hornerMn tP.
- by move=> t tP s sP; rewrite /= eval_MulPoly hornerM tP ?sP.
- by move=> t tP n; rewrite /= eval_ExpPoly horner_exp tP.
Qed.

Lemma wf_QE_wproj i bc (bc_i := @wproj F i bc) :
  dnf_rterm (w_to_oclause bc) -> qf_form bc_i && rformula bc_i.
Proof.
case: bc @bc_i=> sp sq /=; rewrite /dnf_rterm /= /wproj andbT=> /andP[rsp rsq].
by rewrite qf_formF rformulaF.
Qed.

Lemma valid_QE_wproj i bc (bc' := w_to_oclause bc)
    (ex_i_bc := ('exists 'X_i, odnf_to_oform [:: bc'])%oT) e :
  dnf_rterm bc' -> reflect (holds e ex_i_bc) (ord.qf_eval e (wproj i bc)).
Proof.
case: bc @bc' @ex_i_bc=> sp sq /=; rewrite /dnf_rterm /wproj /= andbT.
move=> /andP[rsp rsq]; rewrite -qf_evalE.
rewrite eval_CcountGt0 /=; apply: (equivP (ccount_gt0P _ _)).
set P1 := (fun x => _); set P2 := (fun x => _).
suff: forall x, P1 x <-> P2 x.
  by move=> hP; split=> [] [x Px]; exists x; rewrite (hP, =^~ hP).
move=> x; rewrite /P1 /P2 {P1 P2} !big_map !(big_seq_cond xpredT) /=.
rewrite (eq_bigr (fun t => GRing.eval (set_nth 0 e i x) t == 0)); last first.
  by move=> t /andP[t_in_sp _]; rewrite abstrXP evalE to_rtermE ?(allP rsp).
rewrite [X in _ && X](eq_bigr (fun t => 0 < GRing.eval (set_nth 0 e i x) t));
  last by move=> t /andP[tsq _]; rewrite abstrXP evalE to_rtermE ?(allP rsq).
rewrite -!big_seq_cond !(rwP (qf_evalP _ _)); first last.
+ elim: sp rsp => //= p sp ihsp /andP[rp rsp]; first by rewrite ihsp.
+ elim: sq rsq => //= q sq ihsq /andP[rq rsq]; first by rewrite ihsq.
rewrite !(rwP andP) (rwP orP) orbF !andbT /=.
have unfoldr P s : foldr (fun t => ord.And (P t)) ord.True s =
  \big[ord.And/ord.True]_(t <- s) P t by rewrite unlock /reducebig.
rewrite !unfoldr; set e' := set_nth _ _ _ _.
by rewrite !(@big_morph _ _ (ord.qf_eval _) true andb).
Qed.

Lemma rcf_satP e f : reflect (holds e f) (rcf_sat e f).
Proof. exact: (proj_satP wf_QE_wproj valid_QE_wproj). Qed.

End ProjCorrect.

(* Section Example. *)
(* no chances it computes *)

(* From mathcomp
Require Import rat. *)

(* Eval vm_compute in (54%:R / 289%:R + 2%:R^-1 :rat). *)

(* Local Open Scope qf_scope. *)

(* Notation polyF := (polyF [realFieldType of rat]). *)
(* Definition p : polyF := [::'X_2; 'X_1; 'X_0]. *)
(* Definition q : polyF := [:: 0; 1]. *)
(* Definition sq := [::q]. *)

(* Eval vm_compute in MulPoly p q. *)

(* Eval vm_compute in Rediv ([:: 1] : polyF) [::1]. *)

(* Definition fpq := Eval vm_compute in (CcountWeak p [::q]). *)

(* End Example. *)

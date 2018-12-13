(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrfun ssrbool eqtype choice ssrnat seq fintype generic_quotient.
From mathcomp
Require Import bigop ssralg poly polydiv matrix mxpoly countalg ring_quotient.

(******************************************************************************)
(* This files contains two main contributions:                                *)
(* 1. Theorem "closed_field_QEMixin"                                          *)
(*    A proof that algebraically closed field enjoy quantifier elimination,   *)
(*    as described in                                                         *)
(*    ``A formal quantifier elimination for algebraically closed fields'',    *)
(*     proceedings of Calculemus 2010, by Cyril Cohen and Assia Mahboubi      *)
(*                                                                            *)
(* We constructs an instance of quantifier elimination mixin,                 *)
(* (see the ssralg library) from the theory of polynomials with coefficients  *)
(* is an algebraically closed field (see the polydiv library).                *)
(* The algebraic operations operating on fomulae are implemented in CPS style *)
(* We provide one CPS counterpart for each operation involved in the proof    *)
(* of quantifier elimination. See the paper  for more details.                *)
(*                                                                            *)
(* 2. Theorems "countable_field_extension" and "countable_algebraic_closure"  *)
(*    constructions for both simple extension and algebraic closure of        *)
(*    countable fields, by Georges Gonthier.                                  *)
(*    Note that the construction of the algebraic closure relies on the       *)
(*    above mentionned quantifier elimination.                                *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Import Pdiv.Ring.
Import PreClosedField.

Module ClosedFieldQE.
Section ClosedFieldQE.

Variables (F : fieldType) (F_closed : GRing.ClosedField.axiom F).

Notation fF := (@GRing.formula F).
Notation tF := (@GRing.term F).
Notation qf f := (GRing.qf_form f && GRing.rformula f).
Definition polyF := seq tF.

Lemma qf_simpl (f : fF) :
  (qf f -> GRing.qf_form f) * (qf f -> GRing.rformula f).
Proof. by split=> /andP[]. Qed.

Notation cps T := ((T -> fF) -> fF).
Definition ret T1 : T1 -> cps T1 := fun x k => k x.
Arguments ret {T1} x k /.

Definition bind T1 T2 (x : cps T1) (f : T1 -> cps T2) : cps T2 :=
  fun k => x (fun x => f x k).
Arguments bind {T1 T2} x f k /.
Notation "''let' x <- y ; z" :=
  (bind y (fun x => z)) (at level 99, x at level 0, y at level 0,
    format "'[hv' ''let'  x  <-  y ;  '/' z ']'").

Definition cpsif T (c : fF) (t : T) (e : T) : cps T :=
  fun k => GRing.If c (k t) (k e).
Arguments cpsif {T} c t e k /.
Notation "''if' c1 'then' c2 'else' c3" := (cpsif c1%T c2%T c3%T)
  (at level 200, right associativity, format
"'[hv   ' ''if'  c1  '/' '[' 'then'  c2  ']' '/' '[' 'else'  c3 ']' ']'").

Notation eval := GRing.eval.
Notation rterm := GRing.rterm.
Notation qf_eval := GRing.qf_eval.

Fixpoint eval_poly (e : seq F) pf :=
  if pf is c :: q then eval_poly e q * 'X + (eval e c)%:P else 0.

Definition rpoly (p : polyF) := all (@rterm F) p.

Definition sizeT : polyF -> cps nat := (fix loop p :=
  if p isn't c :: q then ret 0%N
  else 'let n <- loop q;
       if n is m.+1 then ret m.+2 else
       'if (c == 0) then 0%N else 1%N).

Definition qf_red_cps T (x : cps T) (y : _ -> T) :=
   forall e k, qf_eval e (x k) = qf_eval e (k (y e)).
Notation "x ->_ e y" := (qf_red_cps x (fun e => y))
  (e ident, at level 90, format "x  ->_ e  y").

Definition qf_cps T D (x : cps T) :=
  forall k, (forall y, D y -> qf (k y)) -> qf (x k).

Lemma qf_cps_ret T D (x : T) : D x -> qf_cps D (ret x).
Proof. move=> ??; exact. Qed.
Hint Resolve qf_cps_ret : core.

Lemma qf_cps_bind T1 D1 T2 D2 (x : cps T1) (f : T1 -> cps T2) :
  qf_cps D1 x -> (forall x, D1 x -> qf_cps D2 (f x)) -> qf_cps D2 (bind x f).
Proof. by move=> xP fP k kP /=; apply: xP => y ?; apply: fP. Qed.

Lemma qf_cps_if T D (c : fF) (t : T) (e : T) : qf c -> D t -> D e ->
  qf_cps D ('if c then t else e).
Proof.
move=> qfc Dt De k kP /=; have [qft qfe] := (kP _ Dt, kP _ De).
by do !rewrite qf_simpl //.
Qed.

Lemma sizeTP (pf : polyF) : sizeT pf ->_e size (eval_poly e pf).
Proof.
elim: pf=> [|c qf qfP /=]; first by rewrite /= size_poly0.
move=> e k; rewrite size_MXaddC qfP -(size_poly_eq0 (eval_poly _ _)).
by case: (size (eval_poly e qf))=> //=; case: eqP; rewrite // orbF.
Qed.

Lemma sizeT_qf (p : polyF) : rpoly p -> qf_cps xpredT (sizeT p).
Proof.
elim: p => /= [_|c p ihp /andP[rc rq]]; first exact: qf_cps_ret.
apply: qf_cps_bind; first exact: ihp.
move=> [|n] //= _; last exact: qf_cps_ret.
by apply: qf_cps_if; rewrite //= rc.
Qed.

Definition isnull (p : polyF) : cps bool :=
  'let n <- sizeT p; ret (n == 0%N).

Lemma isnullP (p : polyF) : isnull p ->_e (eval_poly e p == 0).
Proof. by move=> e k; rewrite sizeTP size_poly_eq0. Qed.

Lemma isnull_qf (p : polyF) : rpoly p -> qf_cps xpredT (isnull p).
Proof.
move=> rp; apply: qf_cps_bind; first exact: sizeT_qf.
by move=> ? _; apply: qf_cps_ret.
Qed.

Definition lt_sizeT (p q : polyF) : cps bool :=
  'let n <- sizeT p; 'let m <- sizeT q; ret (n < m).

Definition lift (p : {poly F}) := map GRing.Const p.

Lemma eval_lift (e : seq F) (p : {poly F}) : eval_poly e (lift p) = p.
Proof.
elim/poly_ind: p => [|p c]; first by rewrite /lift polyseq0.
rewrite -cons_poly_def /lift polyseq_cons /nilp.
case pn0: (_ == _) => /=; last by move->; rewrite -cons_poly_def.
move=> _; rewrite polyseqC.
case c0: (_==_)=> /=.
  move: pn0; rewrite (eqP c0) size_poly_eq0; move/eqP->.
  by apply: val_inj=> /=; rewrite polyseq_cons // polyseq0.
by rewrite mul0r add0r; apply: val_inj=> /=; rewrite polyseq_cons // /nilp pn0.
Qed.

Fixpoint lead_coefT p : cps tF :=
  if p is c :: q then
    'let l <- lead_coefT q; 'if (l == 0) then c else l
  else ret 0%T.

Lemma lead_coefTP (k : tF -> fF) :
 (forall x e, qf_eval e (k x) = qf_eval e (k (eval e x)%:T%T)) ->
  forall (p : polyF) (e : seq F),
  qf_eval e (lead_coefT p k) = qf_eval e (k (lead_coef (eval_poly e p))%:T%T).
Proof.
move=> kP p e; elim: p => [|a p IHp]/= in k kP e *.
  by rewrite lead_coef0 kP.
rewrite IHp; last by move=> *; rewrite //= -kP.
rewrite GRing.eval_If /= lead_coef_eq0.
case p'0: (_ == _); first by rewrite (eqP p'0) mul0r add0r lead_coefC -kP.
rewrite lead_coefDl ?lead_coefMX // polyseqC size_mul ?p'0 //; last first.
  by rewrite -size_poly_eq0 size_polyX.
rewrite size_polyX addnC /=; case: (_ == _)=> //=.
by rewrite ltnS lt0n size_poly_eq0 p'0.
Qed.

Lemma lead_coefT_qf (p : polyF) : rpoly p -> qf_cps (@rterm _) (lead_coefT p).
Proof.
elim: p => [_|c q ihp //= /andP[rc rq]]; first by apply: qf_cps_ret.
apply: qf_cps_bind => [|y ty]; first exact: ihp.
by apply: qf_cps_if; rewrite //= ty.
Qed.

Fixpoint amulXnT (a : tF) (n : nat) : polyF :=
  if n is n'.+1 then 0%T :: (amulXnT a n') else [:: a].

Lemma eval_amulXnT  (a : tF) (n : nat) (e : seq F) :
  eval_poly e (amulXnT a n) = (eval e a)%:P * 'X^n.
Proof.
elim: n=> [|n] /=; first by rewrite expr0 mulr1 mul0r add0r.
by move->; rewrite addr0 -mulrA -exprSr.
Qed.

Lemma ramulXnT: forall a n, rterm a -> rpoly (amulXnT a n).
Proof. by move=> a n; elim: n a=> [a /= -> //|n ihn a ra]; apply: ihn. Qed.

Fixpoint sumpT (p q : polyF) :=
  match p, q with a :: p, b :: q => (a + b)%T :: sumpT p q
                | [::], q => q | p, [::] => p end.

Lemma eval_sumpT (p q : polyF) (e : seq F) :
  eval_poly e (sumpT p q) = (eval_poly e p) + (eval_poly e q).
Proof.
elim: p q => [|a p Hp] q /=; first by rewrite add0r.
case: q => [|b q] /=; first by rewrite addr0.
rewrite Hp mulrDl -!addrA; congr (_ + _); rewrite polyC_add addrC -addrA.
by congr (_ + _); rewrite addrC.
Qed.

Lemma rsumpT (p q : polyF) : rpoly p -> rpoly q -> rpoly (sumpT p q).
Proof.
elim: p q=> [|a p ihp] q rp rq //; move: rp; case/andP=> ra rp.
case: q rq => [|b q]; rewrite /= ?ra ?rp //=.
by case/andP=> -> rq //=; apply: ihp.
Qed.

Fixpoint mulpT (p q : polyF) :=
  if p isn't a :: p then [::]
  else sumpT [seq (a * x)%T | x <- q] (0%T :: mulpT p q).

Lemma eval_mulpT (p q : polyF) (e : seq F) :
  eval_poly e (mulpT p q) = (eval_poly e p) * (eval_poly e q).
Proof.
elim: p q=> [|a p Hp] q /=; first by rewrite mul0r.
rewrite eval_sumpT /= Hp addr0 mulrDl addrC mulrAC; congr (_ + _).
elim: q=> [|b q Hq] /=; first by rewrite mulr0.
by rewrite Hq polyC_mul mulrDr mulrA.
Qed.

Lemma rpoly_map_mul (t : tF) (p : polyF) (rt : rterm t) :
  rpoly [seq (t * x)%T | x <- p] = rpoly p.
Proof.
by rewrite /rpoly all_map /= (@eq_all _ _ (@rterm _)) // => x; rewrite /= rt.
Qed.

Lemma rmulpT (p q : polyF) : rpoly p -> rpoly q -> rpoly (mulpT p q).
Proof.
elim: p q=> [|a p ihp] q rp rq //=; move: rp; case/andP=> ra rp /=.
apply: rsumpT; last exact: ihp.
by rewrite rpoly_map_mul.
Qed.

Definition opppT : polyF -> polyF := map (GRing.Mul (- 1%T)%T).

Lemma eval_opppT (p : polyF) (e : seq F) :
  eval_poly e (opppT p) = - eval_poly e p.
Proof.
by elim: p; rewrite /= ?oppr0 // => ? ? ->; rewrite !mulNr opprD polyC_opp mul1r.
Qed.

Definition natmulpT n : polyF -> polyF := map (GRing.Mul n%:R%T).

Lemma eval_natmulpT  (p : polyF) (n : nat) (e : seq F) :
  eval_poly e (natmulpT n p) = (eval_poly e p) *+ n.
Proof.
elim: p; rewrite //= ?mul0rn // => c p ->.
rewrite mulrnDl mulr_natl polyC_muln; congr (_ + _).
by rewrite -mulr_natl mulrAC -mulrA mulr_natl mulrC.
Qed.

Fixpoint redivp_rec_loopT (q : polyF) sq cq (c : nat) (qq r : polyF)
  (n : nat) {struct n} : cps (nat * polyF * polyF) :=
  'let sr <- sizeT r;
  if sr < sq then ret (c, qq, r) else
  'let lr <- lead_coefT r;
  let m := amulXnT lr (sr - sq) in
  let qq1 := sumpT (mulpT qq [::cq]) m in
  let r1 := sumpT (mulpT r ([::cq])) (opppT (mulpT m q)) in
  if n is n1.+1 then redivp_rec_loopT q sq cq c.+1 qq1 r1 n1
  else ret (c.+1, qq1, r1).

Fixpoint redivp_rec_loop (q : {poly F}) sq cq
   (k : nat) (qq r : {poly F}) (n : nat) {struct n} :=
    if size r < sq then (k, qq, r) else
      let m := (lead_coef r) *: 'X^(size r - sq) in
      let qq1 := qq * cq%:P + m in
      let r1 := r * cq%:P - m * q in
      if n is n1.+1 then redivp_rec_loop q sq cq k.+1 qq1 r1 n1 else
        (k.+1, qq1, r1).

Lemma redivp_rec_loopTP (k : nat * polyF * polyF -> fF) :
  (forall c qq r e,  qf_eval e (k (c,qq,r))
    = qf_eval e (k (c, lift (eval_poly e qq), lift (eval_poly e r))))
  -> forall q sq cq c qq r n e
    (d := redivp_rec_loop (eval_poly e q) sq (eval e cq)
      c (eval_poly e qq) (eval_poly e r) n),
    qf_eval e (redivp_rec_loopT q sq cq c qq r n k)
    = qf_eval e (k (d.1.1, lift d.1.2, lift d.2)).
Proof.
move=> Pk q sq cq c qq r n e /=.
elim: n c qq r k Pk e => [|n Pn] c qq r k Pk e; rewrite sizeTP.
  case ltrq : (_ < _); first by rewrite /= ltrq /= -Pk.
  rewrite lead_coefTP => [|a p]; rewrite Pk.
    rewrite ?(eval_mulpT,eval_amulXnT,eval_sumpT,eval_opppT) //=.
    by rewrite ltrq //= mul_polyC ?(mul0r,add0r).
  by symmetry; rewrite Pk ?(eval_mulpT,eval_amulXnT,eval_sumpT, eval_opppT).
case ltrq : (_<_); first by rewrite /= ltrq Pk.
rewrite lead_coefTP.
  rewrite Pn ?(eval_mulpT,eval_amulXnT,eval_sumpT,eval_opppT) //=.
  by rewrite ltrq //= mul_polyC ?(mul0r,add0r).
rewrite -/redivp_rec_loopT => x e'.
rewrite Pn; last by move=> *; rewrite Pk.
symmetry; rewrite Pn; last by move=> *; rewrite Pk.
rewrite Pk ?(eval_lift,eval_mulpT,eval_amulXnT,eval_sumpT,eval_opppT).
by rewrite mul_polyC ?(mul0r,add0r).
Qed.

Lemma redivp_rec_loopT_qf (q : polyF) (sq : nat) (cq : tF)
  (c : nat) (qq r : polyF) (n : nat) :
  rpoly q -> rterm cq -> rpoly qq -> rpoly r ->
  qf_cps (fun x => [&& rpoly x.1.2 & rpoly x.2])
         (redivp_rec_loopT q sq cq c qq r n).
Proof.
do ![move=>x/(pair x){x}] => rw; elim: n => [|n IHn]//= in q sq cq c qq r rw *;
apply: qf_cps_bind; do ?[by apply: sizeT_qf; rewrite !rw] => sr _;
case: ifPn => // _; do ?[by apply: qf_cps_ret; rewrite //= ?rw];
apply: qf_cps_bind; do ?[by apply: lead_coefT_qf; rewrite !rw] => lr /= rlr;
[apply: qf_cps_ret|apply: IHn];
by do !rewrite ?(rsumpT,rmulpT,ramulXnT,rpoly_map_mul,rlr,rw) //=.
Qed.

Definition redivpT (p : polyF) (q : polyF) : cps (nat * polyF * polyF) :=
  'let b <- isnull q;
  if b then ret (0%N, [::0%T], p) else
  'let sq <- sizeT q; 'let sp <- sizeT p;
  'let lq <- lead_coefT q;
  redivp_rec_loopT q sq lq 0 [::0%T] p sp.

Lemma redivp_rec_loopP  (q : {poly F}) (c : nat) (qq r : {poly F}) (n : nat) :
  redivp_rec q c qq r n = redivp_rec_loop q (size q) (lead_coef q) c qq r n.
Proof. by elim: n c qq r => [| n Pn] c qq r //=; rewrite Pn. Qed.

Lemma redivpTP (k : nat * polyF * polyF -> fF) :
  (forall c qq r e,
     qf_eval e (k (c,qq,r)) =
     qf_eval e (k (c, lift (eval_poly e qq), lift (eval_poly e r)))) ->
  forall p q e (d := redivp (eval_poly e p) (eval_poly e q)),
    qf_eval e (redivpT p q k) = qf_eval e (k (d.1.1, lift d.1.2, lift d.2)).
Proof.
move=> Pk p q e /=; rewrite isnullP unlock /=.
case q0 : (eval_poly e q == 0) => /=; first by rewrite Pk /= mul0r add0r polyC0.
rewrite !sizeTP lead_coefTP /=; last by move=> *; rewrite !redivp_rec_loopTP.
rewrite redivp_rec_loopTP /=; last by move=> *; rewrite Pk.
by rewrite mul0r add0r polyC0 redivp_rec_loopP.
Qed.

Lemma redivpT_qf (p : polyF) (q : polyF) : rpoly p -> rpoly q ->
  qf_cps (fun x => [&& rpoly x.1.2 & rpoly x.2]) (redivpT p q).
Proof.
move=> rp rq; apply: qf_cps_bind => [|[] _]; first exact: isnull_qf.
  by apply: qf_cps_ret.
apply: qf_cps_bind => [|sp _]; first exact: sizeT_qf.
apply: qf_cps_bind => [|sq _]; first exact: sizeT_qf.
apply: qf_cps_bind => [|lq rlq]; first exact: lead_coefT_qf.
by apply: redivp_rec_loopT_qf => //=.
Qed.

Definition rmodpT (p : polyF) (q : polyF) : cps polyF :=
  'let d <- redivpT p q; ret d.2.
Definition rdivpT (p : polyF) (q : polyF) : cps polyF :=
  'let d <- redivpT p q; ret d.1.2.
Definition rscalpT (p : polyF) (q : polyF) : cps nat :=
  'let d <- redivpT p q; ret d.1.1.
Definition rdvdpT (p : polyF) (q : polyF) : cps bool :=
  'let d <- rmodpT p q; isnull d.

Fixpoint rgcdp_loop n (pp qq : {poly F}) {struct n} :=
  let rr := rmodp pp qq in if rr == 0 then qq
    else if n is n1.+1 then rgcdp_loop n1 qq rr else rr.

Fixpoint rgcdp_loopT n (pp : polyF) (qq : polyF) : cps polyF :=
  'let rr <- rmodpT pp qq; 'let nrr <- isnull rr; if nrr then ret qq
    else if n is n1.+1 then rgcdp_loopT n1 qq rr else ret rr.

Lemma rgcdp_loopP (k : polyF -> fF) :
  (forall p e, qf_eval e (k p) = qf_eval e (k (lift (eval_poly e p)))) ->
  forall n p q e,
    qf_eval e (rgcdp_loopT n p q k) =
    qf_eval e (k (lift (rgcdp_loop n (eval_poly e p) (eval_poly e q)))).
Proof.
move=> Pk n p q e; elim: n => /= [| m IHm] in p q e *;
rewrite redivpTP /==> *; rewrite ?isnullP ?eval_lift -/(rmodp _ _);
by case: (_ == _); do ?by rewrite -?Pk ?IHm ?eval_lift.
Qed.

Lemma rgcdp_loopT_qf (n : nat) (p : polyF) (q : polyF) :
  rpoly p -> rpoly q -> qf_cps rpoly (rgcdp_loopT n p q).
Proof.
elim: n => [|n IHn] in p q * => rp rq /=;
(apply: qf_cps_bind=> [|rr rrr]; [
  apply: qf_cps_bind => [|[[a u] v]]; do ?exact: redivpT_qf;
  by move=> /andP[/= ??]; apply: (@qf_cps_ret _ rpoly)|
apply: qf_cps_bind => [|[] _];
by [apply: isnull_qf|apply: qf_cps_ret|apply: IHn]]).
Qed.

Definition rgcdpT (p : polyF) (q : polyF) : cps polyF :=
  let aux p1 q1 : cps polyF :=
    'let b <- isnull p1; if b then ret q1
    else 'let n <- sizeT p1; rgcdp_loopT n p1 q1 in
  'let b <- lt_sizeT p q; if b then aux q p else aux p q.

Lemma rgcdpTP (k : polyF -> fF) :
  (forall p e, qf_eval e (k p) = qf_eval e (k (lift (eval_poly e p)))) ->
   forall p q e, qf_eval e (rgcdpT p q k) =
                 qf_eval e (k (lift (rgcdp (eval_poly e p) (eval_poly e q)))).
Proof.
move=> Pk p q e; rewrite /rgcdpT /rgcdp !sizeTP /=.
case: (_ < _); rewrite !isnullP /=; case: (_ == _); rewrite -?Pk ?sizeTP;
by rewrite ?rgcdp_loopP.
Qed.

Lemma rgcdpT_qf (p : polyF) (q : polyF) :
   rpoly p -> rpoly q -> qf_cps rpoly (rgcdpT p q).
Proof.
move=> rp rq k kP; rewrite /rgcdpT /=; do ![rewrite sizeT_qf => // ? _].
case: (_ < _); rewrite ?isnull_qf // => -[]; rewrite ?kP // => _;
by rewrite sizeT_qf => // ? _; rewrite rgcdp_loopT_qf.
Qed.

Fixpoint rgcdpTs (ps : seq polyF) : cps polyF :=
  if ps is p :: pr then 'let pr <- rgcdpTs pr; rgcdpT p pr else ret [::0%T].

Lemma rgcdpTsP (k : polyF -> fF) :
  (forall p e, qf_eval e (k p) = qf_eval e (k (lift (eval_poly e p)))) ->
  forall ps e,
    qf_eval e (rgcdpTs ps k) =
    qf_eval e (k (lift (\big[@rgcdp _/0%:P]_(i <- ps)(eval_poly e i)))).
Proof.
move=> Pk ps e; elim: ps k Pk => [|p ps Pps] /= k Pk.
  by rewrite /= big_nil Pk /= mul0r add0r.
by rewrite big_cons Pps => *; rewrite !rgcdpTP // !eval_lift -?Pk.
Qed.

Lemma rgcdpTs_qf (ps : seq polyF) :
   all rpoly ps -> qf_cps rpoly (rgcdpTs ps).
Proof.
elim: ps => [_|c p ihp /andP[rc rp]] //=; first exact: qf_cps_ret.
by apply: qf_cps_bind => [|r rr]; [apply: ihp|apply: rgcdpT_qf].
Qed.

Fixpoint rgdcop_recT n (q : polyF) (p : polyF) :=
  if n is m.+1 then
    'let g <- rgcdpT p q; 'let sg <- sizeT g;
    if sg == 1%N then ret p
    else 'let r <- rdivpT p g;
          rgdcop_recT m q r
  else 'let b <- isnull q; ret [::b%:R%T].


Lemma rgdcop_recTP (k : polyF -> fF) :
  (forall p e, qf_eval e (k p) = qf_eval e (k (lift (eval_poly e p))))
  -> forall p q n e, qf_eval e (rgdcop_recT n p q k)
    = qf_eval e (k (lift (rgdcop_rec (eval_poly e p) (eval_poly e q) n))).
Proof.
move=> Pk p q n e; elim: n => [|n Pn] /= in k Pk p q e *.
  rewrite isnullP /=.
  by case: (_ == _); rewrite Pk /= mul0r add0r ?(polyC0, polyC1).
rewrite /rcoprimep rgcdpTP ?sizeTP ?eval_lift => * /=.
  case: (_ == _);
  by do ?[rewrite /= ?(=^~Pk, redivpTP, rgcdpTP, sizeTP, Pn, eval_lift) //==> *].
do ?[rewrite /= ?(=^~Pk, redivpTP, rgcdpTP, sizeTP, Pn, eval_lift) //==> *].
case: (_ == _);
by do ?[rewrite /= ?(=^~Pk, redivpTP, rgcdpTP, sizeTP, Pn, eval_lift) //==> *].
Qed.

Lemma rgdcop_recT_qf (n : nat) (p : polyF) (q : polyF) :
  rpoly p -> rpoly q -> qf_cps rpoly (rgdcop_recT n p q).
Proof.
elim: n => [|n ihn] in p q * => k kP rp rq /=.
  by rewrite isnull_qf => //*; rewrite rq.
rewrite rgcdpT_qf=> //*; rewrite sizeT_qf=> //*.
case: (_ == _); rewrite ?kP ?rq //= redivpT_qf=> //= ? /andP[??].
by rewrite ihn.
Qed.

Definition rgdcopT q p := 'let sp <- sizeT p; rgdcop_recT sp q p.

Lemma rgdcopTP (k : polyF -> fF) :
  (forall p e, qf_eval e (k p) = qf_eval e (k (lift (eval_poly e p)))) ->
  forall p q e, qf_eval e (rgdcopT p q k) =
                qf_eval e (k (lift (rgdcop (eval_poly e p) (eval_poly e q)))).
Proof. by move=> *; rewrite sizeTP rgdcop_recTP 1?Pk. Qed.

Lemma rgdcopT_qf (p : polyF) (q : polyF) :
  rpoly p -> rpoly q -> qf_cps rpoly (rgdcopT p q).
Proof.
by move=> rp rq k kP; rewrite sizeT_qf => //*; rewrite rgdcop_recT_qf.
Qed.

Definition ex_elim_seq (ps : seq polyF) (q : polyF) : fF :=
  ('let g <- rgcdpTs ps; 'let d <- rgdcopT q g;
  'let n <- sizeT d; ret (n != 1%N)) GRing.Bool.

Lemma ex_elim_seqP (ps : seq polyF) (q : polyF) (e : seq F) :
  let gp := (\big[@rgcdp _/0%:P]_(p <- ps)(eval_poly e p)) in
  qf_eval e (ex_elim_seq ps q) = (size (rgdcop (eval_poly e q) gp) != 1%N).
Proof.
by do ![rewrite (rgcdpTsP,rgdcopTP,sizeTP,eval_lift) //= | move=> * //=].
Qed.

Lemma ex_elim_seq_qf  (ps : seq polyF) (q : polyF) :
  all rpoly ps -> rpoly q -> qf (ex_elim_seq ps q).
Proof.
move=> rps rq; apply: rgcdpTs_qf=> // g rg; apply: rgdcopT_qf=> // d rd.
exact : sizeT_qf.
Qed.

Fixpoint abstrX (i : nat) (t : tF) :=
  match t with
    | 'X_n => if n == i then [::0; 1] else [::t]
    | - x => opppT (abstrX i x)
    | x + y => sumpT (abstrX i x) (abstrX i y)
    | x * y => mulpT (abstrX i x) (abstrX i y)
    | x *+ n => natmulpT n (abstrX i x)
    | x ^+ n => let ax := (abstrX i x) in iter n (mulpT ax) [::1]
    | _ => [::t]
  end%T.

Lemma abstrXP  (i : nat) (t : tF) (e : seq F) (x : F) :
  rterm t -> (eval_poly e (abstrX i t)).[x] = eval (set_nth 0 e i x) t.
Proof.
elim: t => [n | r | n | t tP s sP | t tP | t tP n | t tP s sP | t tP | t tP n] h.
- move=> /=; case ni: (_ == _);
    rewrite //= ?(mul0r,add0r,addr0,polyC1,mul1r,hornerX,hornerC);
    by rewrite // nth_set_nth /= ni.
- by rewrite /= mul0r add0r hornerC.
- by rewrite /= mul0r add0r hornerC.
- by case/andP: h => *; rewrite /= eval_sumpT hornerD tP ?sP.
- by rewrite /= eval_opppT hornerN tP.
- by rewrite /= eval_natmulpT hornerMn tP.
- by case/andP: h => *; rewrite /= eval_mulpT hornerM tP ?sP.
- by [].
- elim: n h => [|n ihn] rt; first by rewrite /= expr0 mul0r add0r hornerC.
  by rewrite /= eval_mulpT exprSr hornerM ihn // mulrC tP.
Qed.

Lemma rabstrX (i : nat) (t : tF) : rterm t -> rpoly (abstrX i t).
Proof.
elim: t; do ?[ by move=> * //=; do ?case: (_ == _)].
- move=> t irt s irs /=; case/andP=> rt rs.
  by apply: rsumpT; rewrite ?irt ?irs //.
- by move=> t irt /= rt; rewrite rpoly_map_mul ?irt //.
- by move=> t irt /= n rt; rewrite rpoly_map_mul ?irt //.
- move=> t irt s irs /=; case/andP=> rt rs.
  by apply: rmulpT; rewrite ?irt ?irs //.
- move=> t irt /= n rt; move: (irt rt)=> {rt} rt; elim: n => [|n ihn] //=.
  exact: rmulpT.
Qed.

Implicit Types tx ty : tF.

Lemma abstrX_mulM (i : nat) : {morph abstrX i : x y / x * y >-> mulpT x y}%T.
Proof. by []. Qed.

Lemma abstrX1 (i : nat) : abstrX i 1%T = [::1%T].
Proof. done. Qed.

Lemma eval_poly_mulM e : {morph eval_poly e : x y / mulpT x y >-> x * y}.
Proof. by move=> x y; rewrite eval_mulpT. Qed.

Lemma eval_poly1 e : eval_poly e [::1%T] = 1.
Proof. by rewrite /= mul0r add0r. Qed.

Notation abstrX_bigmul := (big_morph _ (abstrX_mulM _) (abstrX1 _)).
Notation eval_bigmul := (big_morph _ (eval_poly_mulM _) (eval_poly1 _)).
Notation bigmap_id := (big_map _ (fun _ => true) id).

Lemma rseq_poly_map (x : nat) (ts : seq tF) :
  all (@rterm _) ts ->  all rpoly (map (abstrX x) ts).
Proof.
by elim: ts => //= t ts iht; case/andP=> rt rts; rewrite rabstrX // iht.
Qed.

Definition ex_elim (x : nat) (pqs : seq tF * seq tF) :=
  ex_elim_seq (map (abstrX x) pqs.1)
  (abstrX x (\big[GRing.Mul/1%T]_(q <- pqs.2) q)).

Lemma ex_elim_qf (x : nat) (pqs : seq tF * seq tF) :
  GRing.dnf_rterm pqs -> qf (ex_elim x pqs).
case: pqs => ps qs; case/andP=> /= rps rqs.
apply: ex_elim_seq_qf; first exact: rseq_poly_map.
apply: rabstrX=> /=.
elim: qs rqs=> [|t ts iht] //=; first by rewrite big_nil.
by case/andP=> rt rts; rewrite big_cons /= rt /= iht.
Qed.

Lemma holds_conj : forall e i x ps, all (@rterm _) ps ->
  (GRing.holds (set_nth 0 e i x)
               (foldr (fun t : tF => GRing.And (t == 0)) GRing.True%T ps)
  <-> all ((@root _)^~ x) (map (eval_poly e \o abstrX i) ps)).
Proof.
move=> e i x; elim=> [|p ps ihps] //=.
case/andP=> rp rps; rewrite rootE abstrXP //.
constructor; first by case=> -> hps; rewrite eqxx /=; apply/ihps.
by case/andP; move/eqP=> -> psr; split=> //; apply/ihps.
Qed.

Lemma holds_conjn (e : seq F) (i : nat) (x : F) (ps : seq tF) :
  all (@rterm _) ps ->
  (GRing.holds (set_nth 0 e i x)
               (foldr (fun t : tF => GRing.And (t != 0)) GRing.True ps) <->
  all (fun p => ~~root p x) (map (eval_poly e \o abstrX i) ps)).
Proof.
elim: ps => [|p ps ihps] //=.
case/andP=> rp rps; rewrite rootE abstrXP //.
constructor; first by case=> /eqP-> hps /=; apply/ihps.
by case/andP=> pr psr; split; first apply/eqP=> //; apply/ihps.
Qed.

Lemma holds_ex_elim: GRing.valid_QE_proj ex_elim.
Proof.
move=> i [ps qs] /= e; case/andP=> /= rps rqs.
rewrite ex_elim_seqP big_map.
have -> : \big[@rgcdp _/0%:P]_(j <- ps) eval_poly e (abstrX i j) =
          \big[@rgcdp _/0%:P]_(j <- (map (eval_poly e) (map (abstrX i) (ps)))) j.
  by rewrite !big_map.
rewrite -!map_comp.
  have aux I (l : seq I) (P : I -> {poly F}) :
    \big[(@gcdp F)/0]_(j <- l) P j %= \big[(@rgcdp F)/0]_(j <- l) P j.
    elim: l => [| u l ihl] /=; first by rewrite !big_nil eqpxx.
    rewrite !big_cons; move: ihl; move/(eqp_gcdr (P u)) => h.
    by apply: eqp_trans h _; rewrite eqp_sym; apply: eqp_rgcd_gcd.
case g0: (\big[(@rgcdp F)/0%:P]_(j <- map (eval_poly e \o abstrX i) ps) j == 0).
  rewrite (eqP g0) rgdcop0.
  case m0 : (_ == 0)=> //=; rewrite ?(size_poly1,size_poly0) //=.
    rewrite abstrX_bigmul eval_bigmul -bigmap_id in m0.
    constructor=> [[x] // []] //.
    case=> _; move/holds_conjn=> hc; move/hc:rqs.
    by rewrite -root_bigmul //= (eqP m0) root0.
  constructor; move/negP:m0; move/negP=>m0.
  case: (closed_nonrootP F_closed _ m0) => x {m0}.
  rewrite abstrX_bigmul eval_bigmul -bigmap_id root_bigmul=> m0.
  exists x; do 2?constructor=> //; last by apply/holds_conjn.
  apply/holds_conj; rewrite //= -root_biggcd.
  by rewrite (eqp_root (aux _ _ _ )) (eqP g0) root0.
apply: (iffP (closed_rootP F_closed _)) => -[x Px]; exists x; move: Px => //=.
  rewrite (eqp_root (eqp_rgdco_gdco _ _)) root_gdco ?g0 //.
  rewrite -(eqp_root (aux _ _ _ )) root_biggcd  abstrX_bigmul eval_bigmul.
  rewrite -bigmap_id root_bigmul; case/andP=> psr qsr.
  do 2?constructor; first by apply/holds_conj.
  by apply/holds_conjn.
rewrite (eqp_root (eqp_rgdco_gdco _ _)) root_gdco ?g0 // -(eqp_root (aux _ _ _)).
rewrite root_biggcd abstrX_bigmul eval_bigmul -bigmap_id.
rewrite root_bigmul=> [[] // [hps hqs]]; apply/andP.
constructor; first by apply/holds_conj.
by apply/holds_conjn.
Qed.

Lemma wf_ex_elim : GRing.wf_QE_proj ex_elim.
Proof. by move=> i bc /= rbc; apply: ex_elim_qf. Qed.

Definition Mixin := QEdecFieldMixin wf_ex_elim holds_ex_elim.

End ClosedFieldQE.
End ClosedFieldQE.
Notation closed_field_QEMixin := ClosedFieldQE.Mixin.

Import CodeSeq.

Lemma countable_field_extension (F : countFieldType) (p : {poly F}) :
    size p > 1 ->
  {E : countFieldType & {FtoE : {rmorphism F -> E} &
  {w : E | root (map_poly FtoE p) w
         & forall u : E, exists q, u = (map_poly FtoE q).[w]}}}.
Proof.
pose fix d i :=
  if i is i1.+1 then
    let d1 := oapp (gcdp (d i1)) 0 (unpickle i1) in
    if size d1 > 1 then d1 else d i1
  else p.
move=> p_gt1; have sz_d i: size (d i) > 1 by elim: i => //= i IHi; case: ifP.
have dv_d i j: i <= j -> d j %| d i.
  move/subnK <-; elim: {j}(j - i)%N => //= j IHj; case: ifP => //=.
  case: (unpickle _) => /= [q _|]; last by rewrite size_poly0.
  exact: dvdp_trans (dvdp_gcdl _ _) IHj.
pose I : pred {poly F} := [pred q | d (pickle q).+1 %| q].
have I'co q i: q \notin I -> i > pickle q -> coprimep q (d i).
  rewrite inE => I'q /dv_d/coprimep_dvdl-> //; apply: contraR I'q.
  rewrite coprimep_sym /coprimep /= pickleK /= neq_ltn.
  case: ifP => [_ _| ->]; first exact: dvdp_gcdr.
  rewrite orbF ltnS leqn0 size_poly_eq0 gcdp_eq0 -size_poly_eq0.
  by rewrite -leqn0 leqNgt ltnW //.
have memI q: reflect (exists i, d i %| q) (q \in I).
  apply: (iffP idP) => [|[i dv_di_q]]; first by exists (pickle q).+1.
  have [le_i_q | /I'co i_co_q] := leqP i (pickle q).
    rewrite inE /= pickleK /=; case: ifP => _; first exact: dvdp_gcdr.
    exact: dvdp_trans (dv_d _ _ le_i_q) dv_di_q.
  apply: contraR i_co_q _.
  by rewrite /coprimep (eqp_size (dvdp_gcd_idr dv_di_q)) neq_ltn sz_d orbT.
have I_ideal : idealr_closed I.
  split=> [||a q1 q2 Iq1 Iq2]; first exact: dvdp0.
    by apply/memI=> [[i /idPn[]]]; rewrite dvdp1 neq_ltn sz_d orbT.
  apply/memI; exists (maxn (pickle q1).+1 (pickle q2).+1); apply: dvdp_add.
    by apply: dvdp_mull; apply: dvdp_trans Iq1; apply/dv_d/leq_maxl.
  by apply: dvdp_trans Iq2; apply/dv_d/leq_maxr.
pose Iaddkey := GRing.Pred.Add (DefaultPredKey I) I_ideal.
pose Iidkey := MkIdeal (GRing.Pred.Zmod Iaddkey I_ideal) I_ideal.
pose E := ComRingType _ (@Quotient.mulqC _ _ _ (KeyedPred Iidkey)).
pose PtoE : {rmorphism {poly F} -> E} := [rmorphism of \pi_E%qT : {poly F} -> E].
have PtoEd i: PtoE (d i) = 0.
  by apply/eqP; rewrite piE Quotient.equivE subr0; apply/memI; exists i.
pose Einv (z : E) (q := repr z) (dq := d (pickle q).+1) :=
  let q_unitP := Bezout_eq1_coprimepP q dq in
  if q_unitP is ReflectT ex_uv then PtoE (sval (sig_eqW ex_uv)).1 else 0.
have Einv0: Einv 0 = 0.
  rewrite /Einv; case: Bezout_eq1_coprimepP => // ex_uv.
  case/negP: (oner_neq0 E); rewrite piE -[_ 1]/(PtoE 1); have [uv <-] := ex_uv.
  by rewrite rmorphD !rmorphM PtoEd /= reprK !mulr0 addr0.
have EmulV: GRing.Field.axiom Einv.
  rewrite /Einv=> z nz_z; case: Bezout_eq1_coprimepP => [ex_uv |]; last first.
    move/Bezout_eq1_coprimepP; rewrite I'co //.
    by rewrite piE -{1}[z]reprK -Quotient.idealrBE subr0 in nz_z.
  apply/eqP; case: sig_eqW => {ex_uv} [uv uv1]; set i := _.+1 in uv1 *.
  rewrite piE /= -[z]reprK -(rmorphM PtoE) -Quotient.idealrBE.
  by rewrite -uv1 opprD addNKr -mulNr; apply/memI; exists i; apply: dvdp_mull.
pose Efield := FieldType _ (FieldMixin EmulV Einv0).
pose Ecount := CountType Efield (CanCountMixin reprK).
pose FtoE := [rmorphism of PtoE \o polyC]; pose w : E := PtoE 'X.
have defPtoE q: (map_poly FtoE q).[w] = PtoE q.
  by rewrite map_poly_comp horner_map [_.['X]]comp_polyXr.
exists [countFieldType of Ecount], FtoE, w => [|u].
  by rewrite /root defPtoE (PtoEd 0%N).
by exists (repr u); rewrite defPtoE /= reprK.
Qed.

Lemma countable_algebraic_closure (F : countFieldType) :
  {K : countClosedFieldType & {FtoK : {rmorphism F -> K} | integralRange FtoK}}.
Proof.
pose minXp (R : ringType) (p : {poly R}) := if size p > 1 then p else 'X.
have minXp_gt1 R p: size (minXp R p) > 1.
  by rewrite /minXp; case: ifP => // _; rewrite size_polyX.
have minXpE (R : ringType) (p : {poly R}) : size p > 1 -> minXp R p = p.
  by rewrite /minXp => ->.
have ext1 p := countable_field_extension (minXp_gt1 _ p).
pose ext1fT E p := tag (ext1 E p).
pose ext1to E p : {rmorphism _ -> ext1fT E p} := tag (tagged (ext1 E p)).
pose ext1w E p : ext1fT E p := s2val (tagged (tagged (ext1 E p))).
have ext1root E p: root (map_poly (ext1to E p) (minXp E p)) (ext1w E p).
  by rewrite /ext1w; case: (tagged (tagged (ext1 E p))).
have ext1gen E p u: {q | u = (map_poly (ext1to E p) q).[ext1w E p]}.
  by apply: sig_eqW; rewrite /ext1w; case: (tagged (tagged (ext1 E p))) u.
pose pExtEnum (E : countFieldType) := nat -> {poly E}.
pose Ext := {E : countFieldType & pExtEnum E}; pose MkExt : Ext := Tagged _ _.
pose EtoInc (E : Ext) i := ext1to (tag E) (tagged E i).
pose incEp E i j :=
  let v := map_poly (EtoInc E i) (tagged E j) in
  if decode j is [:: i1; k] then
    if i1 == i then odflt v (unpickle k) else v
  else v.
pose fix E_ i := if i is i1.+1 then MkExt _ (incEp (E_ i1) i1) else MkExt F \0.
pose E i := tag (E_ i); pose Krep := {i : nat & E i}.
pose fix toEadd i k : {rmorphism E i -> E (k + i)%N} :=
  if k is k1.+1 then [rmorphism of EtoInc _ (k1 + i)%N \o toEadd _ _]
  else [rmorphism of idfun].
pose toE i j (le_ij : i <= j) :=
  ecast j {rmorphism E i -> E j} (subnK le_ij) (toEadd i (j - i)%N).
have toEeq i le_ii: toE i i le_ii =1 id.
  by rewrite /toE; move: (subnK _); rewrite subnn => ?; rewrite eq_axiomK.
have toEleS i j leij leiSj z: toE i j.+1 leiSj z = EtoInc _ _ (toE i j leij z).
  rewrite /toE; move: (j - i)%N {leij leiSj}(subnK _) (subnK _) => k.
  by case: j /; rewrite (addnK i k.+1) => eq_kk; rewrite [eq_kk]eq_axiomK.
have toEirr := congr1 ((toE _ _)^~ _) (bool_irrelevance _ _).
have toEtrans j i k leij lejk leik z:
  toE i k leik z = toE j k lejk (toE i j leij z).
- elim: k leik lejk => [|k IHk] leiSk lejSk.
    by case: j => // in leij lejSk *; rewrite toEeq.
  have:= lejSk; rewrite {1}leq_eqVlt ltnS => /predU1P[Dk | lejk].
    by rewrite -Dk in leiSk lejSk *; rewrite toEeq.
  by have leik := leq_trans leij lejk; rewrite !toEleS -IHk.
have [leMl leMr] := (leq_maxl, leq_maxr); pose le_max := (leq_max, leqnn, orbT).
pose pairK (x y : Krep) (m := maxn _ _) :=
  (toE _ m (leMl _ _) (tagged x), toE _ m (leMr _ _) (tagged y)).
pose eqKrep x y := prod_curry (@eq_op _) (pairK x y).
have eqKrefl : reflexive eqKrep by move=> z; apply/eqP; apply: toEirr.
have eqKsym : symmetric eqKrep.
  move=> z1 z2; rewrite {1}/eqKrep /= eq_sym; move: (leMl _ _) (leMr _ _).
  by rewrite maxnC => lez1m lez2m; congr (_ == _); apply: toEirr.
have eqKtrans : transitive eqKrep.
  rewrite /eqKrep /= => z2 z1 z3 /eqP eq_z12 /eqP eq_z23.
  rewrite -(inj_eq (fmorph_inj (toE _ _ (leMr (tag z2) _)))).
  rewrite -!toEtrans ?le_max // maxnCA maxnA => lez3m lez1m.
  rewrite {lez1m}(toEtrans (maxn (tag z1) (tag z2))) // {}eq_z12.
  do [rewrite -toEtrans ?le_max // -maxnA => lez2m] in lez3m *.
  by rewrite (toEtrans (maxn (tag z2) (tag z3))) // eq_z23 -toEtrans.
pose K := {eq_quot (EquivRel _  eqKrefl eqKsym eqKtrans)}%qT.
have cntK : Countable.mixin_of K := CanCountMixin reprK.
pose EtoKrep i (x : E i) : K := \pi%qT (Tagged E x).
have [EtoK piEtoK]: {EtoK | forall i, EtoKrep i =1 EtoK i} by exists EtoKrep.
pose FtoK := EtoK 0%N; rewrite {}/EtoKrep in piEtoK.
have eqEtoK i j x y:
  toE i _ (leMl i j) x = toE j _ (leMr i j) y -> EtoK i x = EtoK j y.
- by move/eqP=> eq_xy; rewrite -!piEtoK; apply/eqmodP.
have toEtoK j i leij x : EtoK j (toE i j leij x) = EtoK i x.
  by apply: eqEtoK; rewrite -toEtrans.
have EtoK_0 i: EtoK i 0 = FtoK 0 by apply: eqEtoK; rewrite !rmorph0.
have EtoK_1 i: EtoK i 1 = FtoK 1 by apply: eqEtoK; rewrite !rmorph1.
have EtoKeq0 i x: (EtoK i x == FtoK 0) = (x == 0).
  by rewrite /FtoK -!piEtoK eqmodE /= /eqKrep /= rmorph0 fmorph_eq0.
have toErepr m i leim x lerm:
  toE _ m lerm (tagged (repr (EtoK i x))) = toE i m leim x.
- have: (Tagged E x == repr (EtoK i x) %[mod K])%qT by rewrite reprK piEtoK.
  rewrite eqmodE /= /eqKrep; case: (repr _) => j y /= in lerm * => /eqP /=.
  have leijm: maxn i j <= m by rewrite geq_max leim.
  by move/(congr1 (toE _ _ leijm)); rewrite -!toEtrans.
pose Kadd (x y : K) := EtoK _ (prod_curry +%R (pairK (repr x) (repr y))).
pose Kopp (x : K) := EtoK _ (- tagged (repr x)).
pose Kmul (x y : K) := EtoK _ (prod_curry *%R (pairK (repr x) (repr y))).
pose Kinv (x : K) := EtoK _ (tagged (repr x))^-1.
have EtoK_D i: {morph EtoK i : x y / x + y >-> Kadd x y}.
  move=> x y; apply: eqEtoK; set j := maxn (tag _) _; rewrite !rmorphD.
  by rewrite -!toEtrans ?le_max  // => lexm leym; rewrite !toErepr.
have EtoK_N i: {morph EtoK i : x / - x >-> Kopp x}.
  by move=> x; apply: eqEtoK; set j := tag _; rewrite !rmorphN toErepr.
have EtoK_M i: {morph EtoK i : x y / x * y >-> Kmul x y}.
  move=> x y; apply: eqEtoK; set j := maxn (tag _) _; rewrite !rmorphM.
  by rewrite -!toEtrans ?le_max  // => lexm leym; rewrite !toErepr.
have EtoK_V i: {morph EtoK i : x / x^-1 >-> Kinv x}.
  by move=> x; apply: eqEtoK; set j := tag _; rewrite !fmorphV toErepr.
case: {toErepr}I in (Kadd) (Kopp) (Kmul) (Kinv) EtoK_D EtoK_N EtoK_M EtoK_V.
pose inEi i z := {x : E i | z = EtoK i x}; have KtoE z: {i : nat & inEi i z}.
  by elim/quotW: z => [[i x] /=]; exists i, x; rewrite piEtoK.
have inEle i j z: i <= j -> inEi i z -> inEi j z.
  by move=> leij [x ->]; exists (toE i j leij x); rewrite toEtoK.
have KtoE2 z1 z2: {i : nat & inEi i z1 & inEi i z2}.
  have [[i1 Ez1] [i2 Ez2]] := (KtoE z1, KtoE z2).
  by exists (maxn i1 i2); [apply: inEle Ez1 | apply: inEle Ez2].
have KtoE3 z1 z2 z3: {i : nat & inEi i z1 & inEi i z2 * inEi i z3}%type.
  have [[i1 Ez1] [i2 Ez2 Ez3]] := (KtoE z1, KtoE2 z2 z3).
  by exists (maxn i1 i2); [apply: inEle Ez1 | split; apply: inEle (leMr _ _) _].
have KaddC: commutative Kadd.
  by move=> u v; have [i [x ->] [y ->]] := KtoE2 u v; rewrite -!EtoK_D addrC.
have KaddA: associative Kadd.
  move=> u v w; have [i [x ->] [[y ->] [z ->]]] := KtoE3 u v w.
  by rewrite -!EtoK_D addrA.
have Kadd0: left_id (FtoK 0) Kadd.
  by move=> u; have [i [x ->]] := KtoE u; rewrite -(EtoK_0 i) -EtoK_D add0r.
have KaddN: left_inverse (FtoK 0) Kopp Kadd.
  by move=> u; have [i [x ->]] := KtoE u; rewrite -EtoK_N -EtoK_D addNr EtoK_0.
pose Kzmod := ZmodType K (ZmodMixin KaddA KaddC Kadd0 KaddN).
have KmulC: commutative Kmul.
  by move=> u v; have [i [x ->] [y ->]] := KtoE2 u v; rewrite -!EtoK_M mulrC.
have KmulA: @associative Kzmod Kmul.
  move=> u v w; have [i [x ->] [[y ->] [z ->]]] := KtoE3 u v w.
  by rewrite -!EtoK_M mulrA.
have Kmul1: left_id (FtoK 1) Kmul.
  by move=> u; have [i [x ->]] := KtoE u; rewrite -(EtoK_1 i) -EtoK_M mul1r.
have KmulD: left_distributive Kmul Kadd.
  move=> u v w; have [i [x ->] [[y ->] [z ->]]] := KtoE3 u v w.
  by rewrite -!(EtoK_M, EtoK_D) mulrDl.
have Kone_nz: FtoK 1 != FtoK 0 by rewrite EtoKeq0 oner_neq0.
pose KringMixin := ComRingMixin KmulA KmulC Kmul1 KmulD Kone_nz.
pose Kring := ComRingType (RingType Kzmod KringMixin) KmulC.
have KmulV: @GRing.Field.axiom Kring Kinv.
  move=> u; have [i [x ->]] := KtoE u; rewrite EtoKeq0 => nz_x.
  by rewrite -EtoK_V -[_ * _]EtoK_M mulVf ?EtoK_1.
have Kinv0: Kinv (FtoK 0) = FtoK 0 by rewrite -EtoK_V invr0.
pose Kuring := [comUnitRingType of UnitRingType _ (FieldUnitMixin KmulV Kinv0)].
pose KfieldMixin := @FieldMixin _ _ KmulV Kinv0.
pose Kidomain := IdomainType Kuring (FieldIdomainMixin KfieldMixin).
pose Kfield := FieldType Kidomain KfieldMixin.
have EtoKrmorphism i: rmorphism (EtoK i : E i -> Kfield).
  by do 2?split=> [x y|]; rewrite ?EtoK_D ?EtoK_N ?EtoK_M ?EtoK_1.
pose EtoKM := RMorphism (EtoKrmorphism _); have EtoK_E: EtoK _ = EtoKM _ by [].
have toEtoKp := @eq_map_poly _ Kring _ _(toEtoK _ _ _).
have Kclosed: GRing.ClosedField.axiom Kfield.
  move=> n pK n_gt0; pose m0 := \max_(i < n) tag (KtoE (pK i)); pose m := m0.+1.
  have /fin_all_exists[pE DpE] (i : 'I_n): exists y, EtoK m y = pK i.
    pose u := KtoE (pK i); have leum0: tag u <= m0 by rewrite (bigmax_sup i).
    by have [y ->] := tagged u; exists (toE _ _ (leqW leum0) y); rewrite toEtoK.
  pose p := 'X^n - rVpoly (\row_i pE i); pose j := code [:: m0; pickle p].
  pose pj := tagged (E_ j) j; pose w : E j.+1 := ext1w (E j) pj.
  have lemj: m <= j by rewrite (allP (ltn_code _)) ?mem_head.
  exists (EtoKM j.+1 w); apply/eqP; rewrite -subr_eq0; apply/eqP.
  transitivity (EtoKM j.+1 (map_poly (toE m j.+1 (leqW lemj)) p).[w]).
    rewrite -horner_map -map_poly_comp toEtoKp EtoK_E; move/EtoKM: w => w.
    rewrite rmorphB [_ 'X^n]map_polyXn !hornerE hornerXn; congr (_ - _ : Kring).
    rewrite (@horner_coef_wide _ n) ?size_map_poly ?size_poly //.
    by apply: eq_bigr => i _; rewrite coef_map coef_rVpoly valK mxE /= DpE.
  suffices Dpj: map_poly (toE m j lemj) p = pj.
    apply/eqP; rewrite EtoKeq0 (eq_map_poly (toEleS _ _ _ _)) map_poly_comp Dpj.
    rewrite -rootE -[pj]minXpE ?ext1root // -Dpj size_map_poly.
    by rewrite size_addl ?size_polyXn ltnS ?size_opp ?size_poly.
  rewrite {w}/pj; elim: {-9}j lemj => // k IHk lemSk.
  move: lemSk (lemSk); rewrite {1}leq_eqVlt ltnS => /predU1P[<- | lemk] lemSk.
    rewrite {k IHk lemSk}(eq_map_poly (toEeq m _)) map_poly_id //= /incEp.
    by rewrite codeK eqxx pickleK.
  rewrite (eq_map_poly (toEleS _ _ _ _)) map_poly_comp {}IHk //= /incEp codeK.
  by rewrite -if_neg neq_ltn lemk.
suffices{Kclosed} algF_K: {FtoK : {rmorphism F -> Kfield} | integralRange FtoK}.
  pose Kdec := DecFieldType Kfield (closed_field_QEMixin Kclosed).
  pose KclosedField := ClosedFieldType Kdec Kclosed.
  by exists [countClosedFieldType of CountType KclosedField cntK].
exists (EtoKM 0%N) => /= z; have [i [{z}z ->]] := KtoE z.
suffices{z} /(_ z)[p mon_p]: integralRange (toE 0%N i isT).
  by rewrite -(fmorph_root (EtoKM i)) -map_poly_comp toEtoKp; exists p.
rewrite /toE /E; clear - minXp_gt1 ext1root ext1gen.
move: (i - 0)%N (subnK _) => n; case: i /.
elim: n => [|n IHn] /= z; first exact: integral_id.
have{z} [q ->] := ext1gen _ _ z; set pn := tagged (E_ _) _.
apply: integral_horner.
  by apply/integral_poly=> i; rewrite coef_map; apply: integral_rmorph.
apply: integral_root (ext1root _ _) _.
  by rewrite map_poly_eq0 -size_poly_gt0 ltnW.
by apply/integral_poly=> i; rewrite coef_map; apply: integral_rmorph.
Qed.

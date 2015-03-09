(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import bigop ssralg poly polydiv.

(******************************************************************************)
(*   A proof that algebraically closed field enjoy quantifier elimination,    *)
(*   as described in                                                          *)
(*   ``A formal quantifier elimination for algebraically closed fields'',     *)
(*    proceedings of Calculemus 2010, by Cyril Cohen and Assia Mahboubi       *)
(*                                                                            *)
(* This file constructs an instance of quantifier elimination mixin,          *)
(* (see the ssralg library) from the theory of polynomials with coefficients  *)
(* is an algebraically closed field (see the polydiv library).                *)
(*                                                                            *)
(* This file hence deals with the transformation of formulae part, which we   *)
(* address by implementing one CPS style formula transformer per effective    *)
(* operation involved in the proof of quantifier elimination. See the paper   *)
(* for more details.                                                          *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.
Local Open Scope ring_scope.

Import Pdiv.Ring.
Import PreClosedField.

Section ClosedFieldQE.

Variable F : Field.type.

Variable axiom : ClosedField.axiom F.

Notation fF := (formula F).
Notation qf f := (qf_form f && rformula f).

Definition polyF := seq (term F).

Fixpoint eval_poly (e : seq F) pf := 
  if pf is c::q then (eval_poly e q)*'X + (eval e c)%:P else 0.

Definition rpoly (p : polyF) := all (@rterm F) p.

Fixpoint sizeT (k : nat -> fF) (p : polyF) :=
  if p is c::q then 
    sizeT (fun n => 
      if n is m.+1 then k m.+2 else 
        GRing.If (c == 0) (k 0%N) (k 1%N)) q 
   else k O%N.


Lemma sizeTP (k : nat -> formula F) (pf : polyF) (e : seq F) : 
  qf_eval e (sizeT k pf) = qf_eval e (k (size (eval_poly e pf))).
Proof.
elim: pf e k; first by move=> *; rewrite size_poly0.
move=> c qf Pqf e k; rewrite Pqf.
rewrite size_MXaddC -(size_poly_eq0 (eval_poly _ _)).
by case: (size (eval_poly e qf))=> //=; case: eqP; rewrite // orbF.
Qed.

Lemma sizeT_qf (k : nat -> formula F) (p : polyF) : 
  (forall n, qf (k n)) -> rpoly p -> qf (sizeT k p).
Proof.
elim: p k => /= [|c q ihp] k kP rp; first exact: kP.
case/andP: rp=> rc rq.
apply: ihp; rewrite ?rq //; case=> [|n]; last exact: kP.
have [/andP[qf0 rf0] /andP[qf1 rf1]] := (kP 0, kP 1)%N.
by rewrite If_form_qf ?If_form_rf //= andbT.
Qed.

Definition isnull (k : bool -> fF) (p : polyF) :=
  sizeT (fun n => k (n == 0%N)) p.

Lemma isnullP (k : bool -> formula F) (p : polyF) (e : seq F) :
  qf_eval e (isnull k p) = qf_eval e (k (eval_poly e p == 0)).
Proof. by rewrite sizeTP size_poly_eq0. Qed.

Lemma isnull_qf (k : bool -> formula F) (p : polyF) :
  (forall b, qf (k b)) -> rpoly p -> qf (isnull k p).
Proof. by move=> *; apply: sizeT_qf. Qed.

Definition lt_sizeT (k : bool -> fF) (p q : polyF) : fF :=
  sizeT (fun n => sizeT (fun m => k (n<m)) q) p.

Definition lift (p : {poly F}) := let: q := p in map Const q.

Lemma eval_lift (e : seq F) (p : {poly F}) : eval_poly e (lift p) = p.
Proof.
elim/poly_ind: p => [|p c]; first by rewrite /lift polyseq0.
rewrite -cons_poly_def /lift polyseq_cons /nilp.
case pn0: (_ == _) => /=; last by move->; rewrite -cons_poly_def.
move=> _; rewrite polyseqC.
case c0: (_==_)=> /=.
  move: pn0; rewrite (eqP c0) size_poly_eq0; move/eqP->. 
  by apply:val_inj=> /=; rewrite polyseq_cons // polyseq0.
by rewrite mul0r add0r; apply:val_inj=> /=; rewrite polyseq_cons // /nilp pn0.
Qed.

Fixpoint lead_coefT (k : term F -> fF) p :=  
  if p is c::q then 
    lead_coefT (fun l => GRing.If (l == 0) (k c) (k l)) q 
  else k (Const 0).

Lemma lead_coefTP (k : term F -> formula F) :
 (forall x e, qf_eval e (k x) = qf_eval e (k (Const (eval e x)))) ->
  forall (p : polyF) (e : seq F),
  qf_eval e (lead_coefT k p) = qf_eval e (k (Const (lead_coef (eval_poly e p)))).
Proof.
move=> Pk p e; elim: p k Pk => /= [*|a p' Pp' k Pk]; first by rewrite lead_coef0.
rewrite Pp'; last by move=> *; rewrite //= -Pk.
rewrite GRing.eval_If /= lead_coef_eq0.
case p'0: (_ == _); first by rewrite (eqP p'0) mul0r add0r lead_coefC -Pk.
rewrite lead_coefDl ?lead_coefMX // polyseqC size_mul ?p'0 //; last first.
  by rewrite -size_poly_eq0 size_polyX.
rewrite size_polyX addnC /=; case: (_ == _)=> //=.
by rewrite ltnS lt0n size_poly_eq0 p'0.
Qed.

Lemma lead_coefT_qf (k : term F -> formula F) (p : polyF) :
 (forall c, rterm c -> qf (k c)) -> rpoly p -> qf (lead_coefT k p).
Proof.
elim: p k => /= [|c q ihp] k kP rp; first exact: kP.
move: rp; case/andP=> rc rq; apply: ihp; rewrite ?rq // => l rl.
have [/andP[qfc rfc] /andP[qfl rfl]] := (kP c rc, kP l rl).
by rewrite If_form_qf ?If_form_rf //= andbT.
Qed.

Fixpoint amulXnT (a : term F) (n : nat) : polyF :=
  if n is n'.+1 then (Const 0) :: (amulXnT a n') else [::a].

Lemma eval_amulXnT  (a : term F) (n : nat) (e : seq F) :
  eval_poly e (amulXnT a n) = (eval e a)%:P * 'X^n.
Proof.
elim: n=> [|n] /=; first by rewrite expr0 mulr1 mul0r add0r.
by move->; rewrite addr0 -mulrA -exprSr.
Qed.

Lemma ramulXnT: forall a n, rterm a -> rpoly (amulXnT a n).
Proof. by move=> a n; elim: n a=> [a /= -> //|n ihn a ra]; apply: ihn. Qed.

Fixpoint sumpT (p q : polyF) :=
  if p is a::p' then
    if q is b::q' then (Add a b)::(sumpT p' q')
      else p
    else q.

Lemma eval_sumpT (p q : polyF) (e : seq F) :
  eval_poly e (sumpT p q) = (eval_poly e p) + (eval_poly e q).
Proof.
elim: p q => [|a p Hp] q /=; first by rewrite add0r.
case: q => [|b q] /=; first by rewrite addr0.
rewrite Hp mulrDl -!addrA; congr (_+_); rewrite polyC_add addrC -addrA.
by congr (_+_); rewrite addrC.
Qed.

Lemma rsumpT (p q : polyF) : rpoly p -> rpoly q -> rpoly (sumpT p q).
Proof.
elim: p q=> [|a p ihp] q rp rq //; move: rp; case/andP=> ra rp.
case: q rq => [|b q]; rewrite /= ?ra ?rp //=.
by case/andP=> -> rq //=; apply: ihp.
Qed.

Fixpoint mulpT (p q : polyF) :=
  if p is a :: p' then sumpT (map (Mul a) q) (Const 0::(mulpT p' q)) else [::].

Lemma eval_mulpT (p q : polyF) (e : seq F) :
  eval_poly e (mulpT p q) = (eval_poly e p) * (eval_poly e q).
Proof.
elim: p q=> [|a p Hp] q /=; first by rewrite mul0r.
rewrite eval_sumpT /= Hp addr0 mulrDl addrC mulrAC; congr (_+_).
elim: q=> [|b q Hq] /=; first by rewrite mulr0.
by rewrite Hq polyC_mul mulrDr mulrA.
Qed.

Lemma rpoly_map_mul (t : term F) (p : polyF) (rt : rterm t) : 
  rpoly (map (Mul t) p) = rpoly p.
Proof. 
by rewrite /rpoly all_map /= (@eq_all _ _ (@rterm _)) // => x; rewrite /= rt.
Qed.

Lemma rmulpT (p q : polyF) : rpoly p -> rpoly q -> rpoly (mulpT p q). 
Proof.
elim: p q=> [|a p ihp] q rp rq //=; move: rp; case/andP=> ra rp /=.
apply: rsumpT; last exact: ihp.
by rewrite rpoly_map_mul.
Qed.

Definition opppT := map (Mul (@Const F (-1))).

Lemma eval_opppT (p : polyF) (e : seq F) : 
 eval_poly e (opppT p) = - eval_poly e p.
Proof.
by elim: p; rewrite /= ?oppr0 // => ? ? ->; rewrite !mulNr opprD polyC_opp mul1r.
Qed.

Definition natmulpT n := map (Mul (@NatConst F n)).

Lemma eval_natmulpT  (p : polyF) (n : nat) (e : seq F) :
  eval_poly e (natmulpT n p) = (eval_poly e p) *+ n.
Proof.
elim: p; rewrite //= ?mul0rn // => c p ->.
rewrite mulrnDl mulr_natl polyC_muln; congr (_+_). 
by rewrite -mulr_natl mulrAC -mulrA mulr_natl mulrC.
Qed.

Fixpoint redivp_rec_loopT (q : polyF) sq cq (k : nat * polyF * polyF -> fF)
  (c : nat) (qq r : polyF) (n : nat) {struct n}:=
  sizeT (fun sr => 
    if sr < sq then k (c, qq, r) else 
      lead_coefT (fun lr =>
        let m := amulXnT lr (sr - sq) in
        let qq1 := sumpT (mulpT qq [::cq]) m in
        let r1 := sumpT (mulpT r ([::cq])) (opppT (mulpT m q)) in
        if n is n1.+1 then redivp_rec_loopT q sq cq k c.+1 qq1 r1 n1
        else k (c.+1, qq1, r1)
      ) r
  ) r.
  
Fixpoint redivp_rec_loop (q : {poly F}) sq cq 
   (k : nat) (qq r : {poly F})(n : nat) {struct n} :=
    if size r < sq then (k, qq, r) else
      let m := (lead_coef r) *: 'X^(size r - sq) in
      let qq1 := qq * cq%:P + m in
      let r1 := r * cq%:P - m * q in
      if n is n1.+1 then redivp_rec_loop q sq cq k.+1 qq1 r1 n1 else
        (k.+1, qq1, r1).

Lemma redivp_rec_loopTP (k : nat * polyF * polyF -> formula F) : 
  (forall c qq r e,  qf_eval e (k (c,qq,r)) 
    = qf_eval e (k (c, lift (eval_poly e qq), lift (eval_poly e r))))
  -> forall q sq cq c qq r n e 
    (d := redivp_rec_loop (eval_poly e q) sq (eval e cq)
      c (eval_poly e qq) (eval_poly e r) n),
    qf_eval e (redivp_rec_loopT q sq cq k c qq r n) 
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
rewrite Pn; last by move=>*; rewrite Pk. 
symmetry; rewrite Pn; last by move=>*; rewrite Pk.
rewrite Pk ?(eval_lift,eval_mulpT,eval_amulXnT,eval_sumpT,eval_opppT).
by rewrite mul_polyC ?(mul0r,add0r).
Qed.

Lemma redivp_rec_loopT_qf (q : polyF) (sq : nat) (cq : term F)
 (k : nat * polyF * polyF -> formula F) (c : nat) (qq r : polyF) (n : nat) :
  (forall r, [&& rpoly r.1.2 & rpoly r.2] -> qf (k r)) ->
  rpoly q -> rterm cq -> rpoly qq -> rpoly r ->
    qf (redivp_rec_loopT q sq cq k c qq r n).
Proof.
elim: n q sq cq k c qq r => [|n ihn] q sq cq k c qq r kP rq rcq rqq rr.
  apply: sizeT_qf=> // n; case: (_ < _); first by apply: kP; rewrite // rqq rr.
  apply: lead_coefT_qf=> // l rl; apply: kP. 
  by rewrite /= ?(rsumpT,rmulpT,ramulXnT,rpoly_map_mul) //= rcq.
apply: sizeT_qf=> // m; case: (_ < _); first by apply: kP => //=; rewrite rqq rr.
apply: lead_coefT_qf=> // l rl; apply: ihn; rewrite //= ?rcq //.
  by rewrite ?(rsumpT,rmulpT,ramulXnT,rpoly_map_mul) //= rcq.
by rewrite ?(rsumpT,rmulpT,ramulXnT,rpoly_map_mul) //= rcq.
Qed.

Definition redivpT (p : polyF) (k : nat * polyF * polyF -> fF) 
                   (q : polyF) : fF :=
  isnull (fun b =>
    if b then k (0%N, [::Const 0], p) else
      sizeT (fun sq =>
        sizeT (fun sp =>
          lead_coefT (fun lq =>
            redivp_rec_loopT q sq lq k 0 [::Const 0] p sp
          ) q
        ) p
      ) q
  ) q.

Lemma redivp_rec_loopP  (q : {poly F}) (c : nat) (qq r : {poly F}) (n : nat) :
  redivp_rec q c qq r n = redivp_rec_loop q (size q) (lead_coef q) c qq r n.
Proof. by elim: n c qq r => [| n Pn] c qq r //=; rewrite Pn. Qed. 

Lemma redivpTP (k : nat * polyF * polyF -> formula F) :
  (forall c qq r e,  
     qf_eval e (k (c,qq,r)) = 
     qf_eval e (k (c, lift (eval_poly e qq), lift (eval_poly e r)))) ->
  forall p q e (d := redivp (eval_poly e p) (eval_poly e q)),
    qf_eval e (redivpT p k q) = qf_eval e (k (d.1.1, lift d.1.2, lift d.2)).
Proof.
move=> Pk p q e /=; rewrite isnullP unlock.
case q0 : (_ == _); first by rewrite Pk /= mul0r add0r polyC0.
rewrite !sizeTP lead_coefTP /=; last by move=> *; rewrite !redivp_rec_loopTP.
rewrite redivp_rec_loopTP /=; last by move=> *; rewrite Pk.
by rewrite mul0r add0r polyC0 redivp_rec_loopP.
Qed.

Lemma redivpT_qf (p : polyF) (k : nat * polyF * polyF -> formula F) (q : polyF) :
  (forall r, [&& rpoly r.1.2 & rpoly r.2] -> qf (k r)) ->
   rpoly p -> rpoly q -> qf (redivpT p k q).
Proof.
move=> kP rp rq; rewrite /redivpT; apply: isnull_qf=> // [[]]; first exact: kP.
apply: sizeT_qf => // sq; apply: sizeT_qf=> // sp.
apply: lead_coefT_qf=> // lq rlq; exact: redivp_rec_loopT_qf.
Qed.

Definition rmodpT (p : polyF) (k : polyF -> fF) (q : polyF) : fF :=
  redivpT p (fun d => k d.2) q.
Definition rdivpT (p : polyF) (k:polyF -> fF) (q : polyF) : fF :=
  redivpT p (fun d => k d.1.2) q.
Definition rscalpT (p : polyF) (k: nat -> fF) (q : polyF) : fF :=
  redivpT p (fun d => k d.1.1) q.
Definition rdvdpT (p : polyF) (k:bool -> fF) (q : polyF) : fF :=
  rmodpT p (isnull k) q.

Fixpoint rgcdp_loop n (pp qq : {poly F}) {struct n} :=
  if rmodp pp qq == 0 then qq 
    else if n is n1.+1 then rgcdp_loop n1 qq (rmodp pp qq)
         else rmodp pp qq.

Fixpoint rgcdp_loopT (pp : polyF) (k : polyF -> formula F) n (qq : polyF) :=
  rmodpT pp (isnull 
    (fun b => if b then (k qq) 
              else (if n is n1.+1 
                    then rmodpT pp (rgcdp_loopT qq k n1) qq 
                    else rmodpT pp k qq)
    )
            ) qq.

Lemma rgcdp_loopP (k : polyF -> formula F) :
  (forall p e, qf_eval e (k p) = qf_eval e (k (lift (eval_poly e p)))) ->
  forall n p q e, 
    qf_eval e (rgcdp_loopT p k n q) = 
    qf_eval e (k (lift (rgcdp_loop n (eval_poly e p) (eval_poly e q)))).
Proof.
move=> Pk n p q e.
elim: n p q e => /= [| m Pm] p q e.
  rewrite redivpTP; last by move=>*; rewrite !isnullP eval_lift.
  rewrite isnullP eval_lift; case: (_ == 0); first by rewrite Pk.
  by rewrite redivpTP; last by move=>*; rewrite Pk.
rewrite redivpTP; last by move=>*; rewrite !isnullP eval_lift.
rewrite isnullP eval_lift; case: (_ == 0); first by rewrite Pk.
by rewrite redivpTP; move=>*; rewrite ?Pm !eval_lift.
Qed.

Lemma rgcdp_loopT_qf (p : polyF) (k : polyF -> formula F) (q : polyF) (n : nat) :
  (forall r, rpoly r -> qf (k r)) -> 
  rpoly p -> rpoly q -> qf (rgcdp_loopT p k n q).
elim: n p k q => [|n ihn] p k q kP rp rq.
  apply: redivpT_qf=> // r; case/andP=> _ rr.
  apply: isnull_qf=> // [[]]; first exact: kP.
  by apply: redivpT_qf=> // r'; case/andP=> _ rr'; apply: kP.
apply: redivpT_qf=> // r; case/andP=> _ rr.
apply: isnull_qf=> // [[]]; first exact: kP.
by apply: redivpT_qf=> // r'; case/andP=> _ rr'; apply: ihn.
Qed.
   
Definition rgcdpT (p : polyF) k (q : polyF) : fF :=
  let aux p1 k q1 := isnull 
    (fun b => if b 
      then (k q1) 
      else (sizeT (fun n => (rgcdp_loopT p1 k n q1)) p1)) p1
    in (lt_sizeT (fun b => if b then (aux q k p) else (aux p k q)) p q). 

Lemma rgcdpTP (k : seq (term F) -> formula F) :
  (forall p e, qf_eval e (k p) = qf_eval e (k (lift (eval_poly e p)))) ->
   forall p q e, qf_eval e (rgcdpT p k q) = 
                 qf_eval e (k (lift (rgcdp (eval_poly e p) (eval_poly e q)))).
Proof.
move=> Pk p q e; rewrite /rgcdpT !sizeTP; case lqp: (_ < _).  
  rewrite isnullP; case q0: (_ == _); first by rewrite Pk (eqP q0) rgcdp0.
  rewrite sizeTP rgcdp_loopP => [|e' p']; last by rewrite Pk. 
  by rewrite /rgcdp lqp q0.
rewrite isnullP; case p0: (_ == _); first by rewrite Pk (eqP p0) rgcd0p.
rewrite sizeTP rgcdp_loopP => [|e' p']; last by rewrite Pk.
by rewrite /rgcdp lqp p0.
Qed.

Lemma rgcdpT_qf  (p : polyF) (k : polyF -> formula F) (q : polyF) :
  (forall r, rpoly r -> qf (k r)) -> rpoly p -> rpoly q -> qf (rgcdpT p k q).
Proof.
move=> kP rp rq; apply: sizeT_qf=> // n; apply: sizeT_qf=> // m.
by case:(_ < _); 
   apply: isnull_qf=> //; case; do ?apply: kP=> //;
   apply: sizeT_qf=> // n'; apply: rgcdp_loopT_qf.
Qed.

Fixpoint rgcdpTs k (ps : seq polyF) : fF :=
  if ps is p::pr then rgcdpTs (rgcdpT p k) pr else k [::Const 0].

Lemma rgcdpTsP (k : polyF -> formula F) : 
  (forall p e, qf_eval e (k p) = qf_eval e (k (lift (eval_poly e p)))) ->
  forall ps e, 
    qf_eval e (rgcdpTs k ps) = 
    qf_eval e (k (lift (\big[@rgcdp _/0%:P]_(i <- ps)(eval_poly e i)))).
Proof.
move=> Pk ps e.
elim: ps k Pk; first by move=> p Pk; rewrite /= big_nil Pk /= mul0r add0r.
move=> p ps Pps /= k Pk /=; rewrite big_cons Pps => [|p' e'].
  by rewrite rgcdpTP // eval_lift.
by rewrite !rgcdpTP // Pk !eval_lift .
Qed.

Definition rseq_poly ps := all rpoly ps.

Lemma rgcdpTs_qf (k : polyF -> formula F) (ps : seq polyF) :
  (forall r, rpoly r -> qf (k r)) -> rseq_poly ps -> qf (rgcdpTs k ps).
Proof.
elim: ps k=> [|c p ihp] k kP rps=> /=; first exact: kP.
by move: rps; case/andP=> rc rp; apply: ihp=> // r rr; apply: rgcdpT_qf.
Qed.

Fixpoint rgdcop_recT (q : polyF) k  (p : polyF) n :=
  if n is m.+1 then
    rgcdpT p (sizeT (fun sd =>
      if sd == 1%N then k p
      else rgcdpT p (rdivpT p (fun r => rgdcop_recT q k r m)) q
    )) q
  else isnull (fun b => k [::Const b%:R]) q.


Lemma rgdcop_recTP (k : polyF -> formula F) : 
  (forall p e, qf_eval e (k p) = qf_eval e (k (lift (eval_poly e p))))
  -> forall p q n e, qf_eval e (rgdcop_recT p k q n) 
    = qf_eval e (k (lift (rgdcop_rec (eval_poly e p) (eval_poly e q) n))).
Proof.
move=> Pk p q n e.
elim: n k Pk p q e => [|n Pn] k Pk p q e /=.
  rewrite isnullP /=.
  by case: (_ == _); rewrite Pk /= mul0r add0r ?(polyC0, polyC1).
rewrite rgcdpTP ?sizeTP ?eval_lift //.
  rewrite /rcoprimep; case se : (_==_); rewrite Pk //.
  do ?[rewrite (rgcdpTP,Pn,eval_lift,redivpTP) | move=> * //=].
by do ?[rewrite (sizeTP,eval_lift) | move=> * //=].
Qed.

Lemma rgdcop_recT_qf (p : polyF) (k : polyF -> formula F) (q : polyF) (n : nat) :
 (forall r, rpoly r -> qf (k r)) -> 
 rpoly p -> rpoly q -> qf (rgdcop_recT p k q n).
Proof.
elim: n p k q => [|n ihn] p k q kP rp rq /=.
apply: isnull_qf=> //; first by case; rewrite kP.
apply: rgcdpT_qf=> // g rg; apply: sizeT_qf=> // n'.
case: (_ == _); first exact: kP.
apply: rgcdpT_qf=> // g' rg'; apply: redivpT_qf=> // r; case/andP=> rr _.
exact: ihn.
Qed.

Definition rgdcopT q k p := sizeT (rgdcop_recT q k p) p.

Lemma rgdcopTP (k : polyF -> formula F) : 
  (forall p e, qf_eval e (k p) = qf_eval e (k (lift (eval_poly e p)))) ->
  forall p q e, qf_eval e (rgdcopT p k q) =
                qf_eval e (k (lift (rgdcop (eval_poly e p) (eval_poly e q)))).
Proof. by move=> *; rewrite sizeTP rgdcop_recTP 1?Pk. Qed.

Lemma rgdcopT_qf (p : polyF) (k : polyF -> formula F) (q : polyF) :
  (forall r, rpoly r -> qf (k r)) -> rpoly p -> rpoly q -> qf (rgdcopT p k q).
Proof. 
by move=> kP rp rq; apply: sizeT_qf => // n; apply: rgdcop_recT_qf.
Qed.


Definition ex_elim_seq (ps : seq polyF) (q : polyF) :=
  (rgcdpTs (rgdcopT q (sizeT (fun n => Bool (n != 1%N)))) ps).

Lemma ex_elim_seqP (ps : seq polyF) (q : polyF) (e : seq F) :
  let gp := (\big[@rgcdp _/0%:P]_(p <- ps)(eval_poly e p)) in
  qf_eval e (ex_elim_seq ps q) = (size (rgdcop (eval_poly e q) gp) != 1%N).
Proof.
by do ![rewrite (rgcdpTsP,rgdcopTP,sizeTP,eval_lift) //= | move=> * //=].
Qed.

Lemma ex_elim_seq_qf  (ps : seq polyF) (q : polyF) :
  rseq_poly ps -> rpoly q -> qf (ex_elim_seq ps q).
Proof.
move=> rps rq; apply: rgcdpTs_qf=> // g rg; apply: rgdcopT_qf=> // d rd.
exact : sizeT_qf.
Qed.

Fixpoint abstrX (i : nat) (t : term F) :=
  match t with
    | (Var n) => if n == i then [::Const 0; Const 1] else [::t]
    | (Opp x) => opppT (abstrX i x)
    | (Add x y) => sumpT (abstrX i x) (abstrX i y)
    | (Mul x y) => mulpT (abstrX i x) (abstrX i y)
    | (NatMul x n) => natmulpT n (abstrX i x)
    | (Exp x n) => let ax := (abstrX i x) in
      iter n (mulpT ax) [::Const 1]
    | _ => [::t]
  end.

Lemma abstrXP  (i : nat) (t : term F) (e : seq F) (x : F) :
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

Lemma rabstrX (i : nat) (t : term F) : rterm t -> rpoly (abstrX i t).
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

Implicit Types tx ty : term F.

Lemma abstrX_mulM (i : nat) : {morph abstrX i : x y / Mul x y >-> mulpT x y}.
Proof. done. Qed.

Lemma abstrX1 (i : nat) : abstrX i (Const 1) = [::Const 1].
Proof. done. Qed.

Lemma eval_poly_mulM e : {morph eval_poly e : x y / mulpT x y >-> mul x y}.
Proof. by move=> x y; rewrite eval_mulpT. Qed.

Lemma eval_poly1 e : eval_poly e [::Const 1] = 1.
Proof. by rewrite /= mul0r add0r. Qed.

Notation abstrX_bigmul := (big_morph _ (abstrX_mulM _) (abstrX1 _)).
Notation eval_bigmul := (big_morph _ (eval_poly_mulM _) (eval_poly1 _)).
Notation bigmap_id := (big_map _ (fun _ => true) id).

Lemma rseq_poly_map (x : nat) (ts : seq (term F)) :
  all (@rterm _) ts ->  rseq_poly (map (abstrX x) ts).
Proof.
by elim: ts => //= t ts iht; case/andP=> rt rts; rewrite rabstrX // iht.
Qed.

Definition ex_elim (x : nat) (pqs : seq (term F) * seq (term F)) :=
  ex_elim_seq (map (abstrX x) pqs.1) 
  (abstrX x (\big[Mul/Const 1]_(q <- pqs.2) q)).
 
Lemma ex_elim_qf (x : nat) (pqs : seq (term F) * seq (term F)) : 
  dnf_rterm pqs -> qf (ex_elim x pqs).
case: pqs => ps qs; case/andP=> /= rps rqs.
apply: ex_elim_seq_qf; first exact: rseq_poly_map.
apply: rabstrX=> /=.
elim: qs rqs=> [|t ts iht] //=; first by rewrite big_nil.
by case/andP=> rt rts; rewrite big_cons /= rt /= iht.
Qed.

Lemma holds_conj : forall e i x ps, all (@rterm _) ps ->
  (holds (set_nth 0 e i x) (foldr (fun t : term F => And (t == 0)) True ps)
  <-> all ((@root _)^~ x) (map (eval_poly e \o abstrX i) ps)).
Proof.
move=> e i x; elim=> [|p ps ihps] //=.
case/andP=> rp rps; rewrite rootE abstrXP //.
constructor; first by case=> -> hps; rewrite eqxx /=; apply/ihps.
by case/andP; move/eqP=> -> psr; split=> //; apply/ihps. 
Qed.

Lemma holds_conjn (e : seq F) (i : nat) (x : F) (ps : seq (term F)) :
  all (@rterm _) ps ->
  (holds (set_nth 0 e i x) (foldr (fun t : term F => And (t != 0)) True ps) <-> 
  all (fun p => ~~root p x) (map (eval_poly e \o abstrX i) ps)).
Proof.
elim: ps => [|p ps ihps] //=.
case/andP=> rp rps; rewrite rootE abstrXP //.
constructor; first by case=> /eqP-> hps /=; apply/ihps.
by case/andP=> pr psr; split; first apply/eqP=> //; apply/ihps. 
Qed.

Lemma holds_ex_elim : GRing.valid_QE_proj ex_elim.
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
    apply: eqp_trans h _; rewrite eqp_sym; exact: eqp_rgcd_gcd.
case g0: (\big[(@rgcdp F)/0%:P]_(j <- map (eval_poly e \o abstrX i) ps) j == 0).
  rewrite (eqP g0) rgdcop0.
  case m0 : (_ == 0)=> //=; rewrite ?(size_poly1,size_poly0) //=.
    rewrite abstrX_bigmul eval_bigmul -bigmap_id in m0.
    constructor=> [[x] // []] //.
    case=> _; move/holds_conjn=> hc; move/hc:rqs.
    by rewrite -root_bigmul //= (eqP m0) root0.
  constructor; move/negP:m0; move/negP=>m0.
  case: (closed_nonrootP axiom _ m0) => x {m0}.
  rewrite abstrX_bigmul eval_bigmul -bigmap_id root_bigmul=> m0.
  exists x; do 2?constructor=> //; last by apply/holds_conjn.
  apply/holds_conj; rewrite //= -root_biggcd.
  by rewrite (eqp_root (aux _ _ _ )) (eqP g0) root0.
apply:(iffP (closed_rootP axiom _)); case=> x Px; exists x; move:Px => //=.
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

Definition closed_fields_QEMixin := 
  QEdecFieldMixin wf_ex_elim holds_ex_elim.

End ClosedFieldQE.

(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
Require Import bigop div prime finfun tuple ssralg zmodp matrix binomial.

(*****************************************************************************)
(* This files contains the definitions of:                                   *)
(*     fib n == n.+1 th fibonacci number                                     *)
(*                                                                           *)
(*   lucas n == n.+1 lucas number                                            *)
(*                                                                           *)
(*  and some of their standard properties                                    *)
(*****************************************************************************)

Fixpoint  fib_rec (n : nat) {struct n} : nat :=
  if n is n1.+1 then
    if n1 is n2.+1 then fib_rec n1 + fib_rec n2
    else 1
  else 0.

Definition fib := nosimpl fib_rec.

Lemma fibE : fib = fib_rec.
Proof. by []. Qed.

Lemma fib0 : fib 0 = 0.
Proof. by []. Qed.

Lemma fib1 : fib 1 = 1.
Proof. by []. Qed.

Lemma fibSS : forall n, fib n.+2 = fib n.+1 + fib n.
Proof. by []. Qed.

Fixpoint lin_fib_rec (a b n : nat) {struct n} : nat :=
  if n is n1.+1 then
    if n1 is n2.+1
      then lin_fib_rec b (b + a) n1
      else b
    else a.

Definition lin_fib := nosimpl lin_fib_rec.

Lemma lin_fibE : lin_fib = lin_fib_rec.
Proof. by []. Qed.

Lemma lin_fib0 : forall a b, lin_fib a b 0 = a.
Proof. by []. Qed.

Lemma lin_fib1 : forall a b, lin_fib a b 1 = b.
Proof. by []. Qed.

Lemma lin_fibSS : forall a b n, lin_fib a b n.+2 = lin_fib b (b + a) n.+1.
Proof. by []. Qed.

Lemma lin_fib_alt : forall n a b,
  lin_fib a b n.+2 = lin_fib a b n.+1 + lin_fib a b n.
Proof.
case=>//; elim => [//|n IHn] a b.
by rewrite lin_fibSS (IHn b (b + a)) lin_fibE.
Qed.

Lemma fib_is_linear : fib =1 lin_fib 0 1.
Proof.
move=>n; elim: n {-2}n (leqnn n)=> [n|n IHn].
  by rewrite leqn0; move/eqP=>->.
case=>//; case=>// n0; rewrite ltnS=> ltn0n; rewrite fibSS lin_fib_alt.
by rewrite (IHn _ ltn0n) (IHn _ (ltnW ltn0n)).
Qed.

Lemma fib_add : forall m n,
 m != 0 ->  fib (m + n) = fib m.-1 * fib n + fib m * fib n.+1.
Proof.
move=> m; elim: m {-2}m (leqnn m)=> [[] // _ |m IH].
move=> m1; rewrite leq_eqVlt; case/orP=> [|Hm]; last first.
  by apply: IH; rewrite -ltnS.
move/eqP->; case: m IH=> [|[|m]] IH n _.
- by case: n=> [|n] //; rewrite fibSS mul1n.
- by rewrite add2n fibSS addnC !mul1n.
rewrite 2!addSn fibSS -addSn !IH // addnA [fib _ * _ + _ + _]addnAC.
by rewrite -addnA -!mulnDl -!fibSS.
Qed.

Theorem dvdn_fib: forall m n, m %| n -> fib m %| fib n.
Proof.
move=> m n; case/dvdnP=> n1 ->.
elim: {n}n1 m=> [|m IH] // [|n]; first by rewrite muln0.
by rewrite mulSn fib_add // dvdn_add //; [apply dvdn_mull | apply dvdn_mulr].
Qed.

Lemma fib_gt0 : forall m, 0 < m -> 0 < fib m.
Proof.
by elim=> [|[|m] IH _] //; rewrite fibSS addn_gt0 IH.
Qed.

Lemma fib_smonotone : forall m n, 1 < m < n -> fib m < fib n.
Proof.
move=> m n; elim: n=> [|[|n] IH]; first  by rewrite andbF.
  by rewrite ltnNge leq_eqVlt orbC andbC; case: leq.
rewrite fibSS andbC; case/andP; rewrite leq_eqVlt; case/orP.
  by rewrite eqSS; move/eqP=> -> H1m; rewrite -addn1 leq_add // fib_gt0.
by move=> H1m H2m; apply: ltn_addr; apply: IH; rewrite // H2m.
Qed.

Lemma fib_monotone : forall m n, m <= n -> fib m <= fib n.
Proof.
move=> m n; elim: n=> [|[|n] IH]; first by case: m.
  by case: m{IH}=> [|[]].
rewrite fibSS leq_eqVlt; case/orP=>[|Hm]; first by move/eqP->.
by apply: (leq_trans (IH _)) => //; exact: leq_addr.
Qed.

Lemma fib_eq1 : forall n, (fib n == 1) = ((n == 1) || (n == 2)).
Proof.
case=> [|[|[|n]]] //; case: eqP=> // Hm; have: 1 < 2 < n.+3 by [].
by move/fib_smonotone; rewrite Hm.
Qed.

Lemma fib_eq : forall m n,
  (fib m == fib n) = [|| m == n, (m == 1) && (n == 2) | (m == 2) && (n == 1)].
Proof.
move=> m n; wlog: m n/ m <= n=> [HH|].
  case/orP: (leq_total m n)=> Hm; first by exact: HH.
  by rewrite eq_sym HH // eq_sym ![(_ == 1) && _]andbC [(_ && _) || _] orbC.
rewrite leq_eqVlt; case/orP=>[|]; first by move/eqP->; rewrite !eqxx.
case: m=> [|[|m]] Hm.
- by move: (fib_gt0 _ Hm); rewrite orbF [0 == _]eq_sym !eqn0Ngt Hm;
     case: (fib n).
- by rewrite eq_sym fib_eq1 orbF [1==_]eq_sym; case: eqP.
have: 1 < m.+2 < n by [].
move/fib_smonotone; rewrite ltn_neqAle; case/andP; move/negPf=> -> _.
case: n Hm=> [|[|n]] //;rewrite ltn_neqAle; case/andP; move/negPf=> ->.
by rewrite andbF.
Qed.

Lemma fib_prime : forall p, p != 4 -> prime (fib p) -> prime p.
Proof.
move=> p Dp4 Pp.
apply/primeP; split; first by case: (p) Pp  => [|[]].
move=> d; case/dvdnP=> k Hp.
have F: forall u, (fib u == 1) = ((u == 1) || (u == 2)).
  case=> [|[|[|n]]] //; case: eqP=> // Hm; have: 1 < 2 < n.+3 by [].
  by move/fib_smonotone; rewrite Hm.
case/primeP: (Pp); rewrite Hp => _ Hf.
case/orP: (Hf _ (dvdn_fib _ _ (dvdn_mulr d (dvdnn k)))).
  rewrite fib_eq1; case/orP; first by move/eqP->; rewrite mul1n eqxx orbT.
  move/eqP=> Hk.
  case/orP: (Hf _ (dvdn_fib _ _ (dvdn_mull k (dvdnn d)))).
    rewrite fib_eq1; case/orP; first by move->.
    by move/eqP=>Hd; case/negP: Dp4; rewrite Hp Hd Hk.
  rewrite fib_eq; case/or3P; first by move/eqP<-; rewrite eqxx orbT.
    by case/andP=>->.
  by rewrite Hk; case: (d)=> [|[|[|]]].
rewrite fib_eq; case/or3P; last by case/andP;move/eqP->; case: (d)=> [|[|]].
  rewrite -{1}[k]muln1; rewrite eqn_mul2l; case/orP; move/eqP=> HH.
    by move: Pp; rewrite Hp HH.
  by rewrite -HH eqxx.
by case/andP; move/eqP->; rewrite mul1n eqxx orbT.
Qed.

Lemma fib_sub : forall m n, n <= m ->
   fib (m - n) = if odd n then fib m.+1 * fib n - fib m * fib n.+1
                 else fib m * fib n.+1 - fib m.+1 * fib n.
Proof.
elim=> [|m IH]; first by case=> /=.
case=> [|n Hn]; first by rewrite muln0 muln1 !subn0.
by rewrite -{2}[n.+1]add1n odd_add (addTb (odd n)) subSS IH //; case: odd;
   rewrite !fibSS !mulnDr !mulnDl !subnDA !addKn.
Qed.

Lemma gcdn_fib: forall m n, gcdn (fib m) (fib n) = fib (gcdn m n).
Proof.
move=> m n; apply: gcdn_def.
- by apply: dvdn_fib; exact: dvdn_gcdl.
- by apply: dvdn_fib; exact: dvdn_gcdr.
move=> d' Hdm Hdn.
case: m Hdm=> [|m Hdm]; first by rewrite gcdnE eqxx.
have F: 0 < m.+1 by [].
case: (egcdnP n F)=> km kn Hg Hl.
have->: gcdn m.+1 n = km * m.+1 - kn * n by rewrite Hg addKn.
rewrite fib_sub; last by rewrite Hg leq_addr.
by case: odd; apply: dvdn_sub;
   try (by apply: (dvdn_trans Hdn); apply: dvdn_mull;
        apply: dvdn_fib; apply: dvdn_mull);
   apply: (dvdn_trans Hdm); apply: dvdn_mulr;
   apply: dvdn_fib; apply: dvdn_mull.
Qed.

Lemma coprimeSn_fib: forall n, coprime (fib n.+1) (fib n).
Proof.
by move=> n; move: (coprimeSn n); rewrite /coprime gcdn_fib; move/eqP->.
Qed.

Fixpoint lucas_rec (n : nat) {struct n} : nat :=
  if n is n1.+1 then
    if n1 is n2.+1 then lucas_rec n1 + lucas_rec n2
    else 1
  else 2.

Definition lucas := nosimpl lucas_rec.

Lemma lucasE : lucas = lucas_rec.
Proof. by []. Qed.

Lemma lucas0 : lucas 0 = 2.
Proof. by []. Qed.

Lemma lucas1 : lucas 1 = 1.
Proof. by []. Qed.

Lemma lucasSS : forall n, lucas n.+2 = lucas n.+1 + lucas n.
Proof. by []. Qed.

Lemma lucas_is_linear : lucas =1 lin_fib 2 1.
Proof.
move=>n; elim: n {-2}n (leqnn n)=> [n|n IHn].
  by rewrite leqn0; move/eqP=>->.
case=>//; case=>// n0; rewrite ltnS=> ltn0n; rewrite lucasSS lin_fib_alt.
by rewrite (IHn _ ltn0n) (IHn _ (ltnW ltn0n)).
Qed.

Lemma lucas_fib: forall n, n != 0 -> lucas n = fib n.+1 + fib n.-1.
Proof.
move=> n; elim: n {-2}n (leqnn n)=> [[] // _ |n IH].
move=> n1; rewrite leq_eqVlt; case/orP=> [|Hn1]; last first.
  by apply: IH; rewrite -ltnS.
move/eqP->; case: n IH=> [|[|n] IH _] //.
by rewrite lucasSS !IH // addnCA -addnA -fibSS addnC.
Qed.

Lemma lucas_gt0 : forall m, 0 < lucas m.
Proof.
by elim=> [|[|m] IH] //; rewrite lucasSS addn_gt0 IH.
Qed.

Lemma double_lucas: forall n, 3 <= n -> (lucas n).*2 = fib (n.+3) + fib (n-3).
Proof.
case=> [|[|[|n]]] // _; rewrite !subSS subn0.
apply/eqP; rewrite -(eqn_add2l (lucas n.+4)) {2}lucasSS addnC -addnn.
rewrite -2![lucas _ + _ + _]addnA eqn_add2l addnC -lucasSS.
rewrite !lucas_fib // [_ + (_ + _)]addnC -[fib _ + _ + _]addnA eqn_add2l.
by rewrite [_ + (_ + _)]addnC -addnA -fibSS.
Qed.

Lemma fib_double_lucas : forall n, fib (n.*2) = fib n * lucas n.
Proof.
case=> [|n]; rewrite // -addnn fib_add // lucas_fib // mulnDr addnC.
by apply/eqP; rewrite eqn_add2l mulnC.
Qed.

Lemma fib_doubleS: forall n, fib (n.*2.+1) = fib n.+1 ^ 2 + fib n ^ 2.
Proof.
by move=> n; rewrite -addnn -addSn fib_add // addnC.
Qed.

Lemma fib_square: forall n, (fib n)^2 = if odd n then (fib n.+1 * fib n.-1).+1
                                        else (fib n.+1 * fib n.-1).-1.
Proof.
case=> [|n] //; move: (fib_sub (n.+1) n (leqnSn _)).
rewrite subSn // subnn fib1 -{8}[n.+1]add1n odd_add addTb.
case: odd=> H1; last first.
  by rewrite -[(_ * _).+1]addn1 {2}H1 addnC subnK // ltnW // -subn_gt0 -H1.
by apply/eqP; rewrite -subn1 {2}H1 subKn // ltnW // -subn_gt0 -H1.
Qed.

Lemma fib_sum : forall n, \sum_(i < n) fib i = (fib n.+1).-1.
Proof.
elim=> [|n IH]; first by rewrite big_ord0.
by rewrite big_ord_recr /= IH fibSS; case: fib (fib_gt0 _ (ltn0Sn n)).
Qed.

Lemma fib_sum_even : forall n, \sum_(i < n) fib i.*2 = (fib n.*2.-1).-1.
Proof.
elim=> [|n IH]; first by rewrite big_ord0.
rewrite big_ord_recr IH; case: (n)=> [|n1] //.
rewrite (fibSS (n1.*2.+1)) addnC -[(n1.+1).*2.-1]/n1.*2.+1.
by case: fib (fib_gt0 _ (ltn0Sn ((n1.*2)))).
Qed.

Lemma fib_sum_odd: forall n, \sum_(i < n) fib i.*2.+1 = fib n.*2.
Proof.
elim=> [|n IH]; first by rewrite big_ord0.
by rewrite big_ord_recr IH /= addnC -fibSS.
Qed.

Lemma fib_sum_square: forall n, \sum_(i < n) (fib i)^2 = fib n * fib n.-1.
Proof.
elim=> [|n IH]; first by rewrite big_ord0.
rewrite big_ord_recr /= IH.
by rewrite -mulnDr addnC; case: (n)=> // n1; rewrite -fibSS mulnC.
Qed.

Lemma bin_sum_diag: forall n, \sum_(i < n) 'C(n.-1-i,i) = fib n.
Proof.
move=> n; elim: n {-2}n (leqnn n)=> [[] // _ |n IH]; first by rewrite big_ord0.
move=> n1; rewrite leq_eqVlt; case/orP=> [|Hn]; last first.
  by apply: IH; rewrite -ltnS.
move/eqP->; case: n IH=> [|[|n]] IH.
- by rewrite big_ord_recr big_ord0.
- by rewrite !big_ord_recr big_ord0.
rewrite fibSS -!IH // big_ord_recl bin0 big_ord_recr /= subnn bin0n addn0.
set ss := \sum_(i < _) _.
rewrite big_ord_recl bin0 -addnA -big_split; congr (_ + _).
by apply eq_bigr=> i _ /=; rewrite -binS subSn //; case: i.
Qed.


(* The matrix                                                                *)

Section Matrix.

Open Local Scope ring_scope.
Import GRing.Theory.

Variable R: ringType.

(*  Equivalence                                  ^ n.+1                      *)
(*                fib n.+2   fib n.+1      1   1                             *)
(*                                     =                                     *)
(*                fib n.+1   fib n         1   0                             *)

Definition seq2matrix m n (l: seq (seq R)) :=
  \matrix_(i<m,j<n) nth 1 (nth [::] l i) j.

Local Notation "''M{' l } " := (seq2matrix _ _ l).

Lemma matrix_fib : forall n,
  'M{[:: [::(fib n.+2)%:R; (fib n.+1)%:R];
         [::(fib n.+1)%:R;    (fib n)%:R]]} =  
 ('M{[:: [:: 1; 1];
         [:: 1; 0]]})^+n.+1 :> 'M[R]_(2,2).
Proof.
elim=> [|n IH].
  by apply/matrixP=> [[[|[|]] // _] [[|[|]] // _]]; rewrite !mxE.
rewrite exprS -IH; apply/matrixP=> i j.
by rewrite !mxE !big_ord_recl big_ord0 !mxE;
   case: i=> [[|[|]]] //= _; case: j=> [[|[|]]] //= _;
   rewrite !mul1r ?mul0r !addr0  // fibSS natrD.
Qed.

End Matrix.

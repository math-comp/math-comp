(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect mini_ssrfun mini_ssrbool mini_eqtype.
From mathcomp Require Import mini_ssrnat mini_seq mini_path mini_div.

(******************************************************************************)
(* This file contains the definitions of:                                     *)
(*        prime p <=> p is a prime.                                           *)
(*       primes m == the sorted list of prime divisors of m > 1, else [::].   *)
(*    pfactor p e == the value p ^ e of a prime factor (p, e).                *)
(* prime_decomp m == the list of prime factors of m > 1, sorted by primes.    *)
(*       logn p m == the e such that (p ^ e) \in prime_decomp n, else 0.      *)
(*  trunc_log p m == the largest e such that p ^ e <= m, or 0 if p or m is 0. *)
(*         pdiv n == the smallest prime divisor of n > 1, else 1.             *)
(*     max_pdiv n == the largest prime divisor of n > 1, else 1.              *)
(*     divisors m == the sorted list of divisors of m > 0, else [::].         *)
(*      totient n == the Euler totient (#|{i < n | i and n coprime}|).        *)
(*       nat_pred == the type of explicit collective nat predicates.          *)
(*                := simpl_pred nat.                                          *)
(*    -> We allow the coercion nat >-> nat_pred, interpreting p as pred1 p.   *)
(*    -> We define a predType for nat_pred, enabling the notation p \in pi.   *)
(*    -> We don't have nat_pred >-> pred, which would imply nat >-> Funclass. *)
(*           pi^' == the complement of pi : nat_pred, i.e., the nat_pred such *)
(*                   that (p \in pi^') = (p \notin pi).                       *)
(*         \pi(n) == the set of prime divisors of n, i.e., the nat_pred such  *)
(*                   that (p \in \pi(n)) = (p \in primes n).                  *)
(*         \pi(A) == the set of primes of #|A|, with A a collective predicate *)
(*                   over a finite Type.                                      *)
(*    -> The notation \pi(A) is implemented with a collapsible Coercion. The  *)
(*       type of A must coerce to finpred_sort (e.g., by coercing to {set T}) *)
(*       and not merely implement the predType interface (as seq T does).     *)
(*    -> The expression #|A| will only appear in \pi(A) after simplification  *)
(*       collapses the coercion, so it is advisable to do so early on.        *)
(*     pi.-nat n <=> n > 0 and all prime divisors of n are in pi.             *)
(*          n`_pi == the pi-part of n -- the largest pi.-nat divisor of n.    *)
(*               := \prod_(0 <= p < n.+1 | p \in pi) p ^ logn p n.            *)
(*    -> The nat >-> nat_pred coercion lets us write p.-nat n and n`_p.       *)
(* In addition to the lemmas relevant to these definitions, this file also    *)
(* contains the dvdn_sum lemma, so that bigop.v doesn't depend on div.v.      *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* The complexity of any arithmetic operation with the Peano representation *)
(* is pretty dreadful, so using algorithms for "harder" problems such as    *)
(* factoring, that are geared for efficient artihmetic leads to dismal      *)
(* performance -- it takes a significant time, for instance, to compute the *)
(* divisors of just a two-digit number. On the other hand, for Peano        *)
(* integers, prime factoring (and testing) is linear-time with a small      *)
(* constant factor -- indeed, the same as converting in and out of a binary *)
(* representation. This is implemented by the code below, which is then     *)
(* used to give the "standard" definitions of prime, primes, and divisors,  *)
(* which can then be used casually in proofs with moderately-sized numeric  *)
(* values (indeed, the code here performs well for up to 6-digit numbers).  *)

Module Import PrimeDecompAux.

(* We start with faster mod-2 and 2-valuation functions. *)

Fixpoint edivn2 q r := if r is r'.+2 then edivn2 q.+1 r' else (q, r).

Lemma edivn2P n : edivn_spec n 2 (edivn2 0 n).
Proof.
rewrite -[n]odd_double_half addnC -{1}[n./2]addn0 -{1}mul2n mulnC.
elim: n./2 {1 4}0 => [|r IHr] q; first by case (odd n) => /=.
by rewrite addSnnS; apply: IHr.
Qed.

Fixpoint elogn2 e q r {struct q} :=
  match q, r with
  | 0, _ | _, 0 => (e, q)
  | q'.+1, 1 => elogn2 e.+1 q' q'
  | q'.+1, r'.+2 => elogn2 e q' r'
  end.

Variant elogn2_spec n : nat * nat -> Type :=
  Elogn2Spec e m of n = 2 ^ e * m.*2.+1 : elogn2_spec n (e, m).

Lemma elogn2P n : elogn2_spec n.+1 (elogn2 0 n n).
Proof.
rewrite -{1}[n.+1]mul1n -[1]/(2 ^ 0) -{1}(addKn n n) addnn.
elim: n {1 4 6}n {2 3}0 (leqnn n) => [|q IHq] [|[|r]] e //=; last first.
  by move/ltnW; apply: IHq.
clear 1; rewrite subn1 -[_.-1.+1]doubleS -mul2n mulnA -expnSr.
by rewrite -{1}(addKn q q) addnn; apply: IHq.
Qed.

Definition ifnz T n (x y : T) := if n is 0 then y else x.

Variant ifnz_spec T n (x y : T) : T -> Type :=
  | IfnzPos of n > 0 : ifnz_spec n x y x
  | IfnzZero of n = 0 : ifnz_spec n x y y.

Lemma ifnzP T n (x y : T) : ifnz_spec n x y (ifnz n x y).
Proof. by case: n => [|n]; [right | left]. Qed.

(* The list of divisors and the Euler function are computed directly from    *)
(* the decomposition, using a merge_sort variant sort of the divisor list.   *)

Definition add_divisors f divs :=
  let: (p, e) := f in
  let add1 divs' := merge leq (map (muln p) divs') divs in
  iter e add1 divs.

Definition add_totient_factor f m := let: (p, e) := f in p.-1 * p ^ e.-1 * m.

Definition cons_pfactor (p e : nat) pd := ifnz e ((p, e) :: pd) pd.

Notation "p ^? e :: pd" := (cons_pfactor p e pd)
  (at level 30, e at level 30, pd at level 60) : nat_scope.

End PrimeDecompAux.

Definition pfactor p e := p ^ e.

Section prime_decomp.

Local Fixpoint prime_decomp_rec m k a b c e :=
  let p := k.*2.+1 in
  if a is a'.+1 then
    if b - (ifnz e 1 k - c) is b'.+1 then
      [rec m, k, a', b', ifnz c c.-1 (ifnz e p.-2 1), e] else
    if (b == 0) && (c == 0) then
      let b' := k + a' in [rec b'.*2.+3, k, a', b', k.-1, e.+1] else
    let bc' := ifnz e (ifnz b (k, 0) (edivn2 0 c)) (b, c) in
    p ^? e :: ifnz a' [rec m, k.+1, a'.-1, bc'.1 + a', bc'.2, 0] [:: (m, 1)]
  else if (b == 0) && (c == 0) then [:: (p, e.+2)] else p ^? e :: [:: (m, 1)]
where "[ 'rec' m , k , a , b , c , e ]" := (prime_decomp_rec m k a b c e).

Definition prime_decomp n :=
  let: (e2, m2) := elogn2 0 n.-1 n.-1 in
  if m2 < 2 then 2 ^? e2 :: 3 ^? m2 :: [::] else
  let: (a, bc) := edivn m2.-2 3 in
  let: (b, c) := edivn (2 - bc) 2 in
  2 ^? e2 :: [rec m2.*2.+1, 1, a, b, c, 0].

End prime_decomp.

Definition primes n := unzip1 (prime_decomp n).

Definition prime p := if prime_decomp p is [:: (_ , 1)] then true else false.

Definition nat_pred := simpl_pred nat.

Definition pdiv n := head 1 (primes n).

Definition max_pdiv n := last 1 (primes n).

Definition divisors n := foldr add_divisors [:: 1] (prime_decomp n).

Definition totient n := foldr add_totient_factor (n > 0) (prime_decomp n).

(* Correctness of the decomposition algorithm. *)

Definition index_iota m n := iota m (n - m).

Lemma mem_index_iota m n i : i \in index_iota m n = (m <= i < n).
Proof.
rewrite mem_iota; case le_m_i: (m <= i) => //=.
by rewrite -leq_subLR subSn // -subn_gt0 -subnDA subnKC // subn_gt0.
Qed.

Lemma prime_decomp_correct :
  let pd_val pd := foldr (fun f => muln (pfactor f.1 f.2)) 1 pd in
  let lb_dvd q m := ~~ has [pred d | d %| m] (index_iota 2 q) in
  let pf_ok f := lb_dvd f.1 f.1 && (0 < f.2) in
  let pd_ord q pd := path ltn q (unzip1 pd) in
  let pd_ok q n pd := [/\ n = pd_val pd, all pf_ok pd & pd_ord q pd] in
  forall n, n > 0 -> pd_ok 1 n (prime_decomp n).
Proof.
move=> pd_val lb_dvd pf_ok pd_ord pd_ok.
have leq_pd_ok m p q pd: q <= p -> pd_ok p m pd -> pd_ok q m pd.
  rewrite /pd_ok /pd_ord; case: pd => [|[r _] pd] //= leqp [<- ->].
  by case/andP=> /(leq_trans _)->.
have apd_ok m e q p pd: lb_dvd p p || (e == 0) -> q < p ->
     pd_ok p m pd -> pd_ok q (p ^ e * m) (p ^? e :: pd).
- case: e => [|e]; rewrite orbC /= => pr_p ltqp.
    by rewrite mul1n; apply: leq_pd_ok; apply: ltnW.
  by rewrite /pd_ok /pd_ord /pf_ok /= pr_p ltqp => [[<- -> ->]].
case=> // n _; rewrite /prime_decomp.
case: elogn2P => e2 m2 -> {n}; case: m2 => [|[|abc]]/=; try exact: apd_ok.
case: edivnP => a bc ->{abc}.
case: edivnP => b c def_bc /= ltc2 ltbc3; apply: (apd_ok) => //.
move def_m: _.*2.+1 => m; set k := {2}1; rewrite -[2]/k.*2; set e := 0.
pose p := k.*2.+1; rewrite -{1}[m]mul1n -[1]/(p ^ e)%N.
have{def_m bc def_bc ltc2 ltbc3}:
   let kb := (ifnz e k 1).*2 in
   [&& k > 0, p < m, lb_dvd p m, c < kb & lb_dvd p p || (e == 0)]
    /\ m + (b * kb + c).*2 = p ^ 2 + (a * p).*2.
- rewrite -def_m [in lb_dvd _ _]def_m; split=> //=; last first.
    by rewrite -def_bc addSn -doubleD 2!addSn -addnA subnKC // addnC.
  rewrite ltc2 /lb_dvd /= dvdn2 -def_m.
  by rewrite [_.+2]lock /= odd_double.
have [n] := ubnP a.
elim: n => // n IHn in a (k) p m b c (e) * => /ltnSE-le_a_n [].
set kb := _.*2; set d := _ + c => /and5P[lt0k ltpm leppm ltc pr_p def_m].
have def_k1: k.-1.+1 = k := ltn_predK lt0k.
have def_kb1: kb.-1.+1 = kb by rewrite /kb -def_k1; case e.
have eq_bc_0: (b == 0) && (c == 0) = (d == 0).
  by rewrite addn_eq0 muln_eq0 orbC -def_kb1.
have lt1p: 1 < p by rewrite ltnS double_gt0.
have co_p_2: coprime p 2 by rewrite /coprime gcdnC gcdnE modn2 /= odd_double.
have if_d0: d = 0 -> [/\ m = (p + a.*2) * p, lb_dvd p p & lb_dvd p (p + a.*2)].
  move=> d0; have{d0 def_m} def_m: m = (p + a.*2) * p.
    by rewrite d0 addn0 -mulnn -!mul2n mulnA -mulnDl in def_m *.
  split=> //; apply/hasPn=> r /(hasPn leppm); apply: contra => /= dv_r.
    by rewrite def_m dvdn_mull.
  by rewrite def_m dvdn_mulr.
case def_a: a => [|a'] /= in le_a_n *; rewrite -/p {}eq_bc_0.
  case: d if_d0 def_m => [[//| def_m {pr_p}pr_p pr_m'] _ | d _ def_m] /=.
    rewrite def_m def_a addn0 mulnA -2!expnSr.
    by split; rewrite /pd_ord /pf_ok /= ?muln1 ?pr_p ?leqnn.
  apply: apd_ok; rewrite // /pd_ok /= /pfactor expn1 muln1 /pd_ord /= ltpm.
  rewrite /pf_ok !andbT /=; split=> //; apply: contra leppm.
  case/hasP=> r /=; rewrite mem_index_iota => /andP[lt1r ltrm] dvrm; apply/hasP.
  have [ltrp | lepr] := ltnP r p.
    by exists r; rewrite // mem_index_iota lt1r.
  case/dvdnP: dvrm => q def_q; exists q; last by rewrite def_q /= dvdn_mulr.
  rewrite mem_index_iota -(ltn_pmul2r (ltnW lt1r)) -def_q mul1n ltrm.
  move: def_m; rewrite def_a addn0 -(@ltn_pmul2r p) // mulnn => <-.
  apply: (@leq_ltn_trans m); first by rewrite def_q leq_mul.
  by rewrite -addn1 leq_add2l.
have def_k2: k.*2 = ifnz e 1 k * kb.
  by rewrite /kb; case: (e) => [|e']; rewrite (mul1n, muln2).
case def_b': (b - _) => [|b']; last first.
  have ->: ifnz e k.*2.-1 1 = kb.-1 by rewrite /kb; case e.
  apply: IHn => {n le_a_n}//; rewrite -/p -/kb; split=> //.
    rewrite lt0k ltpm leppm pr_p andbT /=.
    by case: ifnzP; [move/ltn_predK->; apply: ltnW | rewrite def_kb1].
  apply: (@addIn p.*2).
  rewrite -2!addnA -!doubleD -addnA -mulSnr -def_a -def_m /d.
  have ->: b * kb = b' * kb + (k.*2 - c * kb + kb).
    rewrite addnCA addnC -mulSnr -def_b' def_k2 -mulnBl -mulnDl subnK //.
    by rewrite ltnW // -subn_gt0 def_b'.
  rewrite -addnA; congr (_ + (_ + _).*2).
  case: (c) ltc; first by rewrite -addSnnS def_kb1 subn0 addn0 addnC.
  rewrite /kb; case e => [[] // _ | e' c' _] /=; last first.
    by rewrite subnDA subnn addnC addSnnS.
  by rewrite mul1n -doubleB -doubleD subn1 !addn1 def_k1.
have ltdp: d < p.
  move/eqP: def_b'; rewrite subn_eq0 -(@leq_pmul2r kb); last first.
    by rewrite -def_kb1.
  rewrite mulnBl -def_k2 ltnS -(leq_add2r c); move/leq_trans; apply.
  have{ltc} ltc: c < k.*2.
    by apply: (leq_trans ltc); rewrite leq_double /kb; case e.
  rewrite -{2}(subnK (ltnW ltc)) leq_add2r leq_sub2l //.
  by rewrite -def_kb1 mulnS leq_addr.
case def_d: d if_d0 => [|d'] => [[//|{def_m ltdp pr_p} def_m pr_p pr_m'] | _].
  rewrite eqxx -doubleS -addnS -def_a doubleD -addSn -/p def_m.
  rewrite mulnCA mulnC -expnSr.
  apply: IHn => {n le_a_n}//; rewrite -/p -/kb; split.
    rewrite lt0k -addn1 leq_add2l {1}def_a pr_m' pr_p /= def_k1 -addnn.
    by rewrite leq_addr.
  rewrite -addnA -doubleD addnCA def_a addSnnS def_k1 -(addnC k) -mulnSr.
  rewrite -[_.*2.+1]/p mulnDl doubleD addnA -mul2n mulnA mul2n -mulSn.
  by rewrite -/p mulnn.
have next_pm: lb_dvd p.+2 m.
  rewrite /lb_dvd /index_iota 2!subSS subn0 -(subnK lt1p) iota_add.
  rewrite has_cat; apply/norP; split=> //=; rewrite orbF subnKC // orbC.
  apply/norP; split; apply/dvdnP=> [[q def_q]].
     case/hasP: leppm; exists 2; first by rewrite /p -(subnKC lt0k).
    by rewrite /= def_q dvdn_mull // dvdn2 /= odd_double.
  move/(congr1 (dvdn p)): def_m; rewrite -mulnn -!mul2n mulnA -mulnDl.
  rewrite dvdn_mull // dvdn_addr; last by rewrite def_q dvdn_mull.
  case/dvdnP=> r; rewrite mul2n => def_r; move: ltdp (congr1 odd def_r).
  rewrite odd_double -ltn_double {1}def_r -mul2n ltn_pmul2r //.
  by case: r def_r => [|[|[]]] //; rewrite def_d // mul1n /= odd_double.
apply: apd_ok => //; case: a' def_a le_a_n => [|a'] def_a => [_ | lta] /=.
  rewrite /pd_ok /= /pfactor expn1 muln1 /pd_ord /= ltpm /pf_ok !andbT /=.
  split=> //; apply: contra next_pm.
  case/hasP=> q; rewrite mem_index_iota => /andP[lt1q ltqm] dvqm; apply/hasP.
  have [ltqp | lepq] := ltnP q p.+2.
    by exists q; rewrite // mem_index_iota lt1q.
  case/dvdnP: dvqm => r def_r; exists r; last by rewrite def_r /= dvdn_mulr.
  rewrite mem_index_iota -(ltn_pmul2r (ltnW lt1q)) -def_r mul1n ltqm /=.
  rewrite -(@ltn_pmul2l p.+2) //; apply: (@leq_ltn_trans m).
    by rewrite def_r mulnC leq_mul.
  rewrite -addn2 mulnn sqrnD mul2n muln2 -addnn addnCA -addnA addnCA addnA.
  by rewrite def_a mul1n in def_m; rewrite -def_m addnS -addnA ltnS leq_addr.
set bc := ifnz _ _ _; apply: leq_pd_ok (leqnSn _) _.
rewrite -doubleS -{1}[m]mul1n -[1]/(k.+1.*2.+1 ^ 0)%N.
apply: IHn; first exact: ltnW.
rewrite doubleS -/p [ifnz 0 _ _]/=; do 2?split => //.
  rewrite orbT next_pm /= -(leq_add2r d.*2) def_m 2!addSnnS -doubleS leq_add.
  - move: ltc; rewrite /kb {}/bc andbT; case e => //= e' _; case: ifnzP => //.
    by case: edivn2P.
  - by rewrite -{1}[p]muln1 -mulnn ltn_pmul2l.
  by rewrite leq_double def_a mulSn (leq_trans ltdp) ?leq_addr.
rewrite mulnDl !muln2 -addnA addnCA doubleD addnCA.
rewrite (_ : _ + bc.2 = d); last first.
  rewrite /d {}/bc /kb -muln2.
  case: (e) (b) def_b' => //= _ []; first by case: edivn2P.
  by case c; do 2?case; rewrite // mul1n /= muln2.
rewrite def_m 3!doubleS addnC -(addn2 p) sqrnD mul2n muln2 -3!addnA.
congr (_ + _); rewrite 4!addnS -!doubleD; congr _.*2.+2.+2.
by rewrite def_a -add2n mulnDl -addnA -muln2 -mulnDr mul2n.
Qed.

Lemma primePn n :
  reflect (n < 2 \/ exists2 d, 1 < d < n & d %| n) (~~ prime n).
Proof.
rewrite /prime; case: n => [|[|p2]]; try by do 2!left.
case: (@prime_decomp_correct p2.+2) => //.
case: prime_decomp => [|[q [|[|e]]] pd] //=; last first; last by rewrite andbF.
  rewrite {1}/pfactor 2!expnS -!mulnA /=.
  case: (_ ^ _ * _) => [|u -> _ /andP[lt1q _]]; first by rewrite !muln0.
  left; right; exists q; last by rewrite dvdn_mulr.
  have lt0q := ltnW lt1q; rewrite lt1q -{1}[q]muln1 ltn_pmul2l //.
  by rewrite -[2]muln1 leq_mul.
rewrite {1}/pfactor expn1; case: pd => [|[r e] pd] /=; last first.
  case: e => [|e] /=; first by rewrite !andbF.
  rewrite {1}/pfactor expnS -mulnA.
  case: (_ ^ _ * _) => [|u -> _ /and3P[lt1q ltqr _]]; first by rewrite !muln0.
  left; right; exists q; last by rewrite dvdn_mulr.
  by rewrite lt1q -{1}[q]mul1n ltn_mul // -[q.+1]muln1 leq_mul.
rewrite muln1 !andbT => def_q pr_q lt1q; right=> [[]] // [d].
by rewrite def_q -mem_index_iota => in_d_2q dv_d_q; case/hasP: pr_q; exists d.
Qed.

Lemma primeP p :
  reflect (p > 1 /\ forall d, d %| p -> xpred2 1 p d) (prime p).
Proof.
rewrite -[prime p]negbK; have [npr_p | pr_p] := primePn p.
  right=> [[lt1p pr_p]]; case: npr_p => [|[d n1pd]].
    by rewrite ltnNge lt1p.
  by move/pr_p=> /orP[] /eqP def_d; rewrite def_d ltnn ?andbF in n1pd.
have [lep1 | lt1p] := leqP; first by case: pr_p; left.
left; split=> // d dv_d_p; apply/norP=> [[nd1 ndp]]; case: pr_p; right.
exists d; rewrite // andbC 2!ltn_neqAle ndp eq_sym nd1.
by have lt0p := ltnW lt1p; rewrite dvdn_leq // (dvdn_gt0 lt0p).
Qed.

Lemma prime_nt_dvdP d p : prime p -> d != 1 -> reflect (d = p) (d %| p).
Proof.
case/primeP=> _ min_p d_neq1; apply: (iffP idP) => [/min_p|-> //].
by rewrite (negPf d_neq1) /= => /eqP.
Qed.

Arguments primeP {p}.
Arguments primePn {n}.

Lemma prime_gt1 p : prime p -> 1 < p.
Proof. by case/primeP. Qed.

Lemma prime_gt0 p : prime p -> 0 < p.
Proof. by move/prime_gt1; apply: ltnW. Qed.

Hint Resolve prime_gt1 prime_gt0 : core.

Lemma prod_prime_decomp n :
  n > 0 -> n = foldr (fun f => muln (pfactor f.1 f.2)) 1 (prime_decomp n).
Proof. by case/prime_decomp_correct. Qed.

Lemma even_prime p : prime p -> p = 2 \/ odd p.
Proof.
move=> pr_p; case odd_p: (odd p); [by right | left].
have: 2 %| p by rewrite dvdn2 odd_p.
by case/primeP: pr_p => _ dv_p /dv_p/(2 =P p).
Qed.

Lemma prime_oddPn p : prime p -> reflect (p = 2) (~~ odd p).
Proof.
by move=> p_pr; apply: (iffP idP) => [|-> //]; case/even_prime: p_pr => ->.
Qed.

Lemma odd_prime_gt2 p : odd p -> prime p -> p > 2.
Proof. by move=> odd_p /prime_gt1; apply: odd_gt2. Qed.

Lemma mem_prime_decomp n p e :
  (p, e) \in prime_decomp n -> [/\ prime p, e > 0 & p ^ e %| n].
Proof.
case: (posnP n) => [-> //| /prime_decomp_correct[def_n mem_pd ord_pd pd_pe]].
have /andP[pr_p ->] := allP mem_pd _ pd_pe; split=> //; last first.
  case/splitPr: pd_pe def_n => pd1 pd2 ->; rewrite foldr_cat/=.
  set f := (fun f => muln _); set k := pfactor _ _ * _.
  have: p ^ e %| k by rewrite dvdn_mulr.
  by elim: pd1 => //= x l pedvd /pedvd /dvdn_trans->; rewrite // dvdn_mull.
have lt1p: 1 < p.
  apply: (allP (order_path_min ltn_trans ord_pd)).
  by apply/mapP; exists (p, e).
apply/primeP; split=> // d dv_d_p; apply/norP=> [[nd1 ndp]].
case/hasP: pr_p; exists d => //.
rewrite mem_index_iota andbC 2!ltn_neqAle ndp eq_sym nd1.
by have lt0p := ltnW lt1p; rewrite dvdn_leq // (dvdn_gt0 lt0p).
Qed.

Lemma prime_coprime p m : prime p -> coprime p m = ~~ (p %| m).
Proof.
case/primeP=> p_gt1 p_pr; apply/eqP/negP=> [d1 | ndv_pm].
  case/dvdnP=> k def_m; rewrite -(addn0 m) def_m gcdnMDl gcdn0 in d1.
  by rewrite d1 in p_gt1.
by apply: gcdn_def => // d /p_pr /orP[] /eqP->.
Qed.

Lemma dvdn_prime2 p q : prime p -> prime q -> (p %| q) = (p == q).
Proof.
move=> pr_p pr_q; apply: negb_inj.
by rewrite eqn_dvd negb_and -!prime_coprime // coprime_sym orbb.
Qed.

Lemma Euclid_dvd1 p : prime p -> (p %| 1) = false.
Proof. by rewrite dvdn1; case: eqP => // ->. Qed.

Lemma Euclid_dvdM m n p : prime p -> (p %| m * n) = (p %| m) || (p %| n).
Proof.
move=> pr_p; case dv_pm: (p %| m); first exact: dvdn_mulr.
by rewrite Gauss_dvdr // prime_coprime // dv_pm.
Qed.

Lemma Euclid_dvd_prod (I : Type) (r : seq I) (P : pred I) (f : I -> nat) p :
  prime p ->
  p %| foldr (fun i => muln (f i)) 1 [seq i <- r | P i] =
  has (fun i => p %| f i) [seq i <- r | P i].
Proof.
move=> pP; elim: r => [|n r IHr]/=; first by rewrite Euclid_dvd1.
by case: (P n) => //=; rewrite Euclid_dvdM //= IHr.
Qed.

Lemma Euclid_dvdX m n p : prime p -> (p %| m ^ n) = (p %| m) && (n > 0).
Proof.
case: n => [|n] pr_p; first by rewrite andbF Euclid_dvd1.
by apply: (inv_inj negbK); rewrite !andbT -!prime_coprime // coprime_pexpr.
Qed.

Lemma mem_primes p n : (p \in primes n) = [&& prime p, n > 0 & p %| n].
Proof.
rewrite andbCA; case: posnP => [-> // | /= n_gt0].
apply/mapP/andP=> [[[q e]]|[pr_p]] /=.
  case/mem_prime_decomp=> pr_q e_gt0; case/dvdnP=> u -> -> {p}.
  by rewrite -(prednK e_gt0) expnS mulnCA dvdn_mulr.
rewrite {1}(prod_prime_decomp n_gt0).
elim: (prime_decomp n) (@mem_prime_decomp n) => [|[/= q e] r IHr] mem_pd.
   by rewrite Euclid_dvd1.
rewrite Euclid_dvdM //= => /orP[].
  have := mem_pd q e; rewrite mem_head => - []// q_prime e_gt0 dv_qe_n.
  rewrite Euclid_dvdX // dvdn_prime2 // => /andP[/eqP-> _].
  by exists (q, e); rewrite /= ?mem_head.
move=> /IHr[k f kfr|]; first by apply: mem_pd; rewrite in_cons kfr orbT.
by move=> x xr ->; exists x; rewrite // ?in_cons xr orbT.
Qed.

Lemma sorted_primes n : sorted ltn (primes n).
Proof.
by case: (posnP n) => [-> // | /prime_decomp_correct[_ _]]; apply: path_sorted.
Qed.

Lemma eq_primes m n : (primes m =i primes n) <-> (primes m = primes n).
Proof.
split=> [eqpr| -> //].
by apply: (eq_sorted_irr ltn_trans ltnn); rewrite ?sorted_primes.
Qed.

Lemma primes_uniq n : uniq (primes n).
Proof. exact: (sorted_uniq ltn_trans ltnn (sorted_primes n)). Qed.

(* The smallest prime divisor *)



Lemma primes_mul m n p : m > 0 -> n > 0 ->
  (p \in primes (m * n)) = (p \in primes m) || (p \in primes n).
Proof.
move=> m_gt0 n_gt0; rewrite !mem_primes muln_gt0 m_gt0 n_gt0.
by case pr_p: (prime p); rewrite // Euclid_dvdM.
Qed.

Lemma primes_exp m n : n > 0 -> primes (m ^ n) = primes m.
Proof.
case: n => // n _; rewrite expnS; case: (posnP m) => [-> //| m_gt0].
apply/eq_primes => /= p; elim: n => [|n IHn]; first by rewrite muln1.
by rewrite primes_mul ?(expn_gt0, expnS, IHn, orbb, m_gt0).
Qed.

Lemma primes_prime p : prime p -> primes p = [::p].
Proof.
move=> pr_p; apply: (eq_sorted_irr ltn_trans ltnn) => // [|q].
  exact: sorted_primes.
rewrite mem_seq1 mem_primes prime_gt0 //=.
by apply/andP/idP=> [[pr_q q_p] | /eqP-> //]; rewrite -dvdn_prime2.
Qed.


Lemma pdiv_id p : prime p -> pdiv p = p.
Proof. by move=> p_pr; rewrite /pdiv primes_prime. Qed.

Lemma pdiv_pfactor p k : prime p -> pdiv (p ^ k.+1) = p.
Proof. by move=> p_pr; rewrite /pdiv primes_exp ?primes_prime. Qed.


(* "prime" logarithms and p-parts. *)

Fixpoint logn_rec d m r :=
  match r, edivn m d with
  | r'.+1, (_.+1 as m', 0) => (logn_rec d m' r').+1
  | _, _ => 0
  end.

Definition logn p m := if prime p then logn_rec p m m else 0.

Lemma lognE p m :
  logn p m = if [&& prime p, 0 < m & p %| m] then (logn p (m %/ p)).+1 else 0.
Proof.
rewrite /logn /dvdn; case p_pr: (prime p) => //.
case def_m: m => // [m']; rewrite !andTb [LHS]/= -def_m /divn modn_def.
case: edivnP def_m => [[|q] [|r] -> _] // def_m; congr _.+1; rewrite [_.1]/=.
have{m def_m}: q < m'.
  by rewrite -ltnS -def_m addn0 mulnC -{1}[q.+1]mul1n ltn_pmul2r // prime_gt1.
elim/ltn_ind: m' {q}q.+1 (ltn0Sn q) => -[_ []|r IHr m] //= m_gt0 le_mr.
rewrite -[m in logn_rec _ _ m]prednK //=.
case: edivnP => [[|q] [|_] def_q _] //; rewrite addn0 in def_q.
have{def_q} lt_qm1: q < m.-1.
  by rewrite -[q.+1]muln1 -ltnS prednK // def_q ltn_pmul2l // prime_gt1.
have{le_mr} le_m1r: m.-1 <= r by rewrite -ltnS prednK.
by rewrite (IHr r) ?(IHr m.-1) // (leq_trans lt_qm1).
Qed.

Lemma logn_gt0 p n : (0 < logn p n) = (p \in primes n).
Proof. by rewrite lognE -mem_primes; case: {+}(p \in _). Qed.

Lemma ltn_log0 p n : n < p -> logn p n = 0.
Proof. by case: n => [|n] ltnp; rewrite lognE ?andbF // gtnNdvd ?andbF. Qed.

Lemma logn0 p : logn p 0 = 0.
Proof. by rewrite /logn if_same. Qed.

Lemma logn1 p : logn p 1 = 0.
Proof. by rewrite lognE dvdn1 /= andbC; case: eqP => // ->. Qed.

Lemma pfactor_gt0 p n : 0 < p ^ logn p n.
Proof. by rewrite expn_gt0 lognE; case: (posnP p) => // ->. Qed.
Hint Resolve pfactor_gt0 : core.

Lemma pfactor_dvdn p n m : prime p -> m > 0 -> (p ^ n %| m) = (n <= logn p m).
Proof.
move=> p_pr; elim: n m => [|n IHn] m m_gt0; first exact: dvd1n.
rewrite lognE p_pr m_gt0 /=; case dv_pm: (p %| m); last first.
  apply/dvdnP=> [] [/= q def_m].
  by rewrite def_m expnS mulnCA dvdn_mulr in dv_pm.
case/dvdnP: dv_pm m_gt0 => q ->{m}; rewrite muln_gt0 => /andP[p_gt0 q_gt0].
by rewrite expnSr dvdn_pmul2r // mulnK // IHn.
Qed.

Lemma pfactor_dvdnn p n : p ^ logn p n %| n.
Proof.
case: n => // n; case pr_p: (prime p); first by rewrite pfactor_dvdn.
by rewrite lognE pr_p dvd1n.
Qed.

Lemma logn_prime p q : prime q -> logn p q = (p == q).
Proof.
move=> pr_q; have q_gt0 := prime_gt0 pr_q; rewrite lognE q_gt0 /=.
case pr_p: (prime p); last by case: eqP pr_p pr_q => // -> ->.
by rewrite dvdn_prime2 //; case: eqP => // ->; rewrite divnn q_gt0 logn1.
Qed.

Lemma pfactor_coprime p n :
  prime p -> n > 0 -> {m | coprime p m & n = m * p ^ logn p n}.
Proof.
move=> p_pr n_gt0; set k := logn p n.
have dv_pk_n: p ^ k %| n by rewrite pfactor_dvdn.
exists (n %/ p ^ k); last by rewrite divnK.
rewrite prime_coprime // -(@dvdn_pmul2r (p ^ k)) ?expn_gt0 ?prime_gt0 //.
by rewrite -expnS divnK // pfactor_dvdn // ltnn.
Qed.

Lemma pfactorK p n : prime p -> logn p (p ^ n) = n.
Proof.
move=> p_pr; have pn_gt0: p ^ n > 0 by rewrite expn_gt0 prime_gt0.
apply/eqP; rewrite eqn_leq -pfactor_dvdn // dvdnn andbT.
by rewrite -(leq_exp2l _ _ (prime_gt1 p_pr)) dvdn_leq // pfactor_dvdn.
Qed.

Lemma pfactorKpdiv p n : prime p -> logn (pdiv (p ^ n)) (p ^ n) = n.
Proof. by case: n => // n p_pr; rewrite pdiv_pfactor ?pfactorK. Qed.

Lemma dvdn_leq_log p m n : 0 < n -> m %| n -> logn p m <= logn p n.
Proof.
move=> n_gt0 dv_m_n; have m_gt0 := dvdn_gt0 n_gt0 dv_m_n.
case p_pr: (prime p); last by do 2!rewrite lognE p_pr /=.
by rewrite -pfactor_dvdn //; apply: dvdn_trans dv_m_n; rewrite pfactor_dvdn.
Qed.

Lemma ltn_logl p n : 0 < n -> logn p n < n.
Proof.
move=> n_gt0; have [p_gt1 | p_le1] := boolP (1 < p).
  by rewrite (leq_trans (ltn_expl _ p_gt1)) // dvdn_leq ?pfactor_dvdnn.
by rewrite lognE (contraNF (@prime_gt1 _)).
Qed.

Lemma logn_Gauss p m n : coprime p m -> logn p (m * n) = logn p n.
Proof.
move=> co_pm; case p_pr: (prime p); last by rewrite /logn p_pr.
have [-> | n_gt0] := posnP n; first by rewrite muln0.
have [m0 | m_gt0] := posnP m; first by rewrite m0 prime_coprime ?dvdn0 in co_pm.
have mn_gt0: m * n > 0 by rewrite muln_gt0 m_gt0.
apply/eqP; rewrite eqn_leq andbC dvdn_leq_log ?dvdn_mull //.
set k := logn p _; have: p ^ k %| m * n by rewrite pfactor_dvdn.
by rewrite Gauss_dvdr ?coprime_expl // -pfactor_dvdn.
Qed.

Lemma lognM p m n : 0 < m -> 0 < n -> logn p (m * n) = logn p m + logn p n.
Proof.
case p_pr: (prime p); last by rewrite /logn p_pr.
have xlp := pfactor_coprime p_pr.
case/xlp=> m' co_m' def_m /xlp[n' co_n' def_n] {xlp}.
by rewrite {1}def_m {1}def_n mulnCA -mulnA -expnD !logn_Gauss // pfactorK.
Qed.

Lemma lognX p m n : logn p (m ^ n) = n * logn p m.
Proof.
case p_pr: (prime p); last by rewrite /logn p_pr muln0.
elim: n => [|n IHn]; first by rewrite logn1.
have [->|m_gt0] := posnP m; first by rewrite exp0n // lognE andbF muln0.
by rewrite expnS lognM ?IHn // expn_gt0 m_gt0.
Qed.

Lemma logn_div p m n : m %| n -> logn p (n %/ m) = logn p n - logn p m.
Proof.
rewrite dvdn_eq => /eqP def_n.
case: (posnP n) => [-> |]; first by rewrite div0n logn0.
by rewrite -{1 3}def_n muln_gt0 => /andP[q_gt0 m_gt0]; rewrite lognM ?addnK.
Qed.

Lemma dvdn_pfactor p d n : prime p ->
  reflect (exists2 m, m <= n & d = p ^ m) (d %| p ^ n).
Proof.
move=> p_pr; have pn_gt0: p ^ n > 0 by rewrite expn_gt0 prime_gt0.
apply: (iffP idP) => [dv_d_pn|[m le_m_n ->]]; last first.
  by rewrite -(subnK le_m_n) expnD dvdn_mull.
exists (logn p d); first by rewrite -(pfactorK n p_pr) dvdn_leq_log.
have d_gt0: d > 0 by apply: dvdn_gt0 dv_d_pn.
case: (pfactor_coprime p_pr d_gt0) => q co_p_q def_d.
rewrite {1}def_d ((q =P 1) _) ?mul1n // -dvdn1.
suff: q %| p ^ n * 1 by rewrite Gauss_dvdr // coprime_sym coprime_expl.
by rewrite muln1 (dvdn_trans _ dv_d_pn) // def_d dvdn_mulr.
Qed.

(* Truncated real log. *)

Definition trunc_log p n :=
  let fix loop n k :=
    if k is k'.+1 then if p <= n then (loop (n %/ p) k').+1 else 0 else 0
  in loop n n.

Lemma trunc_log_bounds p n :
  1 < p -> 0 < n -> let k := trunc_log p n in p ^ k <= n < p ^ k.+1.
Proof.
rewrite {+}/trunc_log => p_gt1; have p_gt0 := ltnW p_gt1.
set loop := (loop in loop n n); set m := n; rewrite [in n in loop m n]/m.
have: m <= n by []; elim: n m => [|n IHn] [|m] //= /ltnSE-le_m_n _.
have [le_p_n | // ] := leqP p _; rewrite 2!expnSr -leq_divRL -?ltn_divLR //.
by apply: IHn; rewrite ?divn_gt0 // -ltnS (leq_trans (ltn_Pdiv _ _)).
Qed.

Lemma trunc_log_ltn p n : 1 < p -> n < p ^ (trunc_log p n).+1.
Proof.
have [-> | n_gt0] := posnP n; first by move=> /ltnW; rewrite expn_gt0.
by case/trunc_log_bounds/(_ n_gt0)/andP.
Qed.

Lemma trunc_logP p n : 1 < p -> 0 < n -> p ^ trunc_log p n <= n.
Proof. by move=> p_gt1 /(trunc_log_bounds p_gt1)/andP[]. Qed.

Lemma trunc_log_max p k j : 1 < p -> p ^ j <= k -> j <= trunc_log p k.
Proof.
move=> p_gt1 le_pj_k; rewrite -ltnS -(@ltn_exp2l p) //.
exact: leq_ltn_trans (trunc_log_ltn _ _).
Qed.

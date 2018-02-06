(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype.
From mathcomp
Require Import ssralg poly ssrnum zmodp polydiv interval.

Import GRing.Theory.
Import Num.Theory.

Import Pdiv.Idomain.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Section Multiplicity.

Variable R : idomainType.
Implicit Types x y c : R.
Implicit Types p q r d : {poly R}.

(* Definition multiplicity (x : R) (p : {poly R}) : nat :=  *)
(*   (odflt ord0 (pick (fun i : 'I_(size p).+1 =>  ((('X - x%:P) ^+ i %| p))  *)
(*                                  && (~~ (('X - x%:P) ^+ i.+1 %| p))))). *)

(* Notation "'\mu_' x" := (multiplicity x) *)
(*   (at level 8, format "'\mu_' x") : ring_scope. *)

(* Lemma mu0 : forall x, \mu_x 0 = 0%N. *)
(* Proof. *)
(* by move=> x; rewrite /multiplicity; case: pickP=> //= i; rewrite !dvdp0. *)
(* Qed. *)

(* Lemma muP : forall p x, p != 0 -> *)
(*   (('X - x%:P) ^+ (\mu_x p) %| p) && ~~(('X - x%:P) ^+ (\mu_x p).+1 %| p). *)
(* Proof. *)
(* move=> p x np0; rewrite /multiplicity; case: pickP=> //= hp. *)
(* have {hp} hip: forall i, i <= size p  *)
(*     -> (('X - x%:P) ^+ i %| p) -> (('X - x%:P) ^+ i.+1 %| p). *)
(*   move=> i; rewrite -ltnS=> hi; move/negbT: (hp (Ordinal hi)).  *)
(*   by rewrite -negb_imply negbK=> /implyP. *)
(* suff: forall i, i <= size p -> ('X - x%:P) ^+ i %| p. *)
(*   move=> /(_ _ (leqnn _)) /(size_dvdp np0). *)
(*   rewrite -[size _]prednK; first by rewrite size_exp size_XsubC mul1n ltnn. *)
(*   by rewrite lt0n size_poly_eq0 expf_eq0 polyXsubC_eq0 lt0n size_poly_eq0 np0. *)
(* elim=> [|i ihi /ltnW hsp]; first by rewrite expr0 dvd1p. *)
(* by rewrite hip // ihi. *)
(* Qed. *)

(* Lemma cofactor_XsubC : forall p a, p != 0 ->  *)
(*   exists2 q : {poly R}, (~~ root q a) & p = q * ('X - a%:P) ^+ (\mu_a p). *)
(* Proof. *)
(* move=> p a np0. *)

Definition multiplicity (x : R) (p : {poly R}) :=
  if p == 0 then 0%N else sval (multiplicity_XsubC p x).

Notation "'\mu_' x" := (multiplicity x)
  (at level 8, format "'\mu_' x") : ring_scope.

Lemma mu_spec p a : p != 0 ->
  { q : {poly R} & (~~ root q a)
    & ( p = q * ('X - a%:P) ^+ (\mu_a p)) }.
Proof.
move=> nz_p; rewrite /multiplicity -if_neg.
by case: (_ p a) => m /=/sig2_eqW[q]; rewrite nz_p; exists q.
Qed.

Lemma mu0 x : \mu_x 0 = 0%N.
Proof. by rewrite /multiplicity {1}eqxx. Qed.

Lemma root_mu p x : ('X - x%:P) ^+ (\mu_x p) %| p.
Proof.
case p0: (p == 0); first by rewrite (eqP p0) mu0 expr0 dvd1p.
case: (@mu_spec p x); first by rewrite p0.
by move=> q qn0 hp //=; rewrite {2}hp dvdp_mulIr.
Qed.

(* Lemma size_exp_XsubC : forall x n, size (('X - x%:P) ^+ n) = n.+1. *)
(* Proof. *)
(* move=> x n; rewrite -[size _]prednK ?size_exp ?size_XsubC ?mul1n //. *)
(* by rewrite ltnNge leqn0 size_poly_eq0 expf_neq0 // polyXsubC_eq0. *)
(* Qed. *)

Lemma root_muN p x : p != 0 ->
  (('X - x%:P)^+(\mu_x p).+1 %| p) = false.
Proof.
move=> pn0; case: (mu_spec x pn0)=> q qn0 hp /=.
rewrite {2}hp exprS dvdp_mul2r; last first.
  by rewrite expf_neq0 // polyXsubC_eq0.
apply: negbTE; rewrite -eqp_div_XsubC; apply: contra qn0.
by move/eqP->; rewrite rootM root_XsubC eqxx orbT.
Qed.

Lemma root_le_mu p x n : p != 0 -> ('X - x%:P)^+n %| p = (n <= \mu_x p)%N.
Proof.
move=> pn0; case: leqP=> hn; last apply/negP=> hp.
  apply: (@dvdp_trans _ (('X - x%:P) ^+ (\mu_x p))); last by rewrite root_mu.
  by rewrite dvdp_Pexp2l // size_XsubC.
suff : ('X - x%:P) ^+ (\mu_x p).+1 %| p by rewrite root_muN.
by apply: dvdp_trans hp; rewrite dvdp_Pexp2l // size_XsubC.
Qed.

Lemma muP p x n : p != 0 ->
  (('X - x%:P)^+n %| p) && ~~(('X - x%:P)^+n.+1 %| p) = (n == \mu_x p).
Proof.
by move=> hp0; rewrite !root_le_mu//; case: (ltngtP n (\mu_x p)).
Qed.

Lemma mu_gt0 p x : p != 0 -> (0 < \mu_x p)%N = root p x.
Proof. by move=> pn0; rewrite -root_le_mu// expr1 root_factor_theorem. Qed.

Lemma muNroot p x : ~~ root p x -> \mu_x p = 0%N.
Proof.
case p0: (p == 0); first by rewrite (eqP p0) rootC eqxx.
by move=> pnx0; apply/eqP; rewrite -leqn0 leqNgt mu_gt0 ?p0.
Qed.

Lemma mu_polyC c x : \mu_x (c%:P) = 0%N.
Proof.
case c0: (c == 0); first by rewrite (eqP c0) mu0.
by apply: muNroot; rewrite rootC c0.
Qed.

Lemma cofactor_XsubC_mu  x p n :
  ~~ root p x -> \mu_x (p * ('X - x%:P) ^+ n) = n.
Proof.
move=> p0; apply/eqP; rewrite eq_sym -muP//; last first.
  apply: contra p0; rewrite mulf_eq0 expf_eq0 polyXsubC_eq0 andbF orbF.
  by move/eqP->; rewrite root0.
rewrite dvdp_mulIr /= exprS dvdp_mul2r -?root_factor_theorem //.
by rewrite expf_eq0 polyXsubC_eq0 andbF //.
Qed.

Lemma mu_mul p q x : p * q != 0 ->
  \mu_x (p * q) = (\mu_x p + \mu_x q)%N.
Proof.
move=> hpqn0; apply/eqP; rewrite eq_sym -muP//.
rewrite exprD dvdp_mul ?root_mu//=.
move: hpqn0; rewrite mulf_eq0 negb_or; case/andP=> hp0 hq0.
move: (mu_spec x hp0)=> [qp qp0 hp].
move: (mu_spec x hq0)=> [qq qq0 hq].
rewrite {2}hp {2}hq exprS exprD !mulrA [qp * _ * _]mulrAC.
rewrite !dvdp_mul2r ?expf_neq0 ?polyXsubC_eq0 // -eqp_div_XsubC.
move: (mulf_neq0 qp0 qq0); rewrite -hornerM; apply: contra; move/eqP->.
by rewrite hornerM hornerXsubC subrr mulr0.
Qed.

Lemma mu_XsubC x : \mu_x ('X - x%:P) = 1%N.
Proof.
apply/eqP; rewrite eq_sym -muP; last by rewrite polyXsubC_eq0.
by rewrite expr1 dvdpp/= -{2}[_ - _]expr1 dvdp_Pexp2l // size_XsubC.
Qed.

Lemma mu_mulC c p x : c != 0 -> \mu_x (c *: p) = \mu_x p.
Proof.
move=> cn0; case p0: (p == 0); first by rewrite (eqP p0) scaler0.
by rewrite -mul_polyC mu_mul ?mu_polyC// mulf_neq0 ?p0 ?polyC_eq0.
Qed.

Lemma mu_opp p x : \mu_x (-p) = \mu_x p.
Proof.
rewrite -mulN1r -polyC1 -polyC_opp mul_polyC mu_mulC //.
by rewrite -oppr0 (inj_eq (inv_inj (@opprK _))) oner_eq0.
Qed.

Lemma mu_exp p x n : \mu_x (p ^+ n) = (\mu_x p * n)%N.
Proof.
elim: n p => [|n ihn] p; first by rewrite expr0 mu_polyC muln0.
case p0: (p == 0); first by rewrite (eqP p0) exprS mul0r mu0 mul0n.
by rewrite exprS mu_mul ?ihn ?mulnS// mulf_eq0 expf_eq0 p0 andbF.
Qed.

Lemma mu_addr p q x : p != 0 -> (\mu_x p < \mu_x q)%N ->
  \mu_x (p + q) = \mu_x p.
Proof.
move=> pn0 mupq.
have pqn0 : p + q != 0.
  move: mupq; rewrite ltnNge; apply: contra.
  by rewrite -[q]opprK subr_eq0; move/eqP->; rewrite opprK mu_opp leqnn.
have qn0: q != 0 by move: mupq; apply: contraL; move/eqP->; rewrite mu0 ltn0.
case: (mu_spec x pn0)=> [qqp qqp0] hp.
case: (mu_spec x qn0)=> [qqq qqq0] hq.
rewrite hp hq -(subnK (ltnW mupq)).
rewrite mu_mul ?mulf_eq0; last first.
  rewrite expf_eq0 polyXsubC_eq0 andbF orbF.
  by apply: contra qqp0; move/eqP->; rewrite root0.
rewrite mu_exp mu_XsubC mul1n [\mu_x qqp]muNroot // add0n.
rewrite exprD mulrA -mulrDl mu_mul; last first.
  by rewrite mulrDl -mulrA -exprD subnK 1?ltnW // -hp -hq.
rewrite muNroot ?add0n ?mu_exp ?mu_XsubC ?mul1n //.
rewrite rootE !hornerE horner_exp hornerXsubC subrr.
by rewrite -subnSK // subnS exprS mul0r mulr0 addr0.
Qed.

Lemma mu_addl p q x : q != 0 -> (\mu_x p > \mu_x q)%N ->
  \mu_x (p + q) = \mu_x q.
Proof. by move=> q0 hmu; rewrite addrC mu_addr. Qed.

Lemma mu_div p x n : (n <= \mu_x p)%N ->
  \mu_x (p %/ ('X - x%:P) ^+ n) = (\mu_x p - n)%N.
Proof.
move=> hn.
case p0: (p == 0); first by rewrite (eqP p0) div0p mu0 sub0n.
case: (@mu_spec p x); rewrite ?p0 // => q hq hp.
rewrite {1}hp -{1}(subnK hn) exprD mulrA.
rewrite Pdiv.IdomainMonic.mulpK; last by apply: monic_exp; apply: monicXsubC.
rewrite mu_mul ?mulf_eq0 ?expf_eq0 ?polyXsubC_eq0 ?andbF ?orbF; last first.
  by apply: contra hq; move/eqP->; rewrite root0.
by rewrite mu_exp muNroot // add0n mu_XsubC mul1n.
Qed.

End Multiplicity.

Notation "'\mu_' x" := (multiplicity x)
  (at level 8, format "'\mu_' x") : ring_scope.


Section PolyrealIdomain.

 (*************************************************************************)
 (* This should be replaced by a 0-characteristic condition + integrality *)
 (* and merged into poly and polydiv                                      *)
 (*************************************************************************)

Variable R : realDomainType.

Lemma size_deriv (p : {poly R}) : size p^`() = (size p).-1.
Proof.
have [lep1|lt1p] := leqP (size p) 1.
  by rewrite {1}[p]size1_polyC // derivC size_poly0 -subn1 (eqnP lep1).
rewrite size_poly_eq // mulrn_eq0 -subn2 -subSn // subn2.
by rewrite lead_coef_eq0 -size_poly_eq0 -(subnKC lt1p).
Qed.

Lemma derivn_poly0 : forall (p : {poly R}) n, (size p <= n)%N = (p^`(n) == 0).
Proof.
move=> p n; apply/idP/idP.
   move=> Hpn; apply/eqP; apply/polyP=>i; rewrite coef_derivn.
   rewrite nth_default; first by rewrite mul0rn coef0.
   by apply: leq_trans Hpn _; apply leq_addr.
elim: n {-2}n p (leqnn n) => [m | n ihn [| m]] p.
- by rewrite leqn0; move/eqP->; rewrite derivn0 leqn0 -size_poly_eq0.
- by move=> _; apply: ihn; rewrite leq0n.
- rewrite derivSn => hmn hder; case e: (size p) => [|sp] //.
  rewrite -(prednK (ltn0Sn sp)) [(_.-1)%N]lock -e -lock -size_deriv ltnS.
  exact: ihn.
Qed.

Lemma mu_deriv : forall x (p : {poly R}), root p x ->
  \mu_x (p^`()) = (\mu_x p - 1)%N.
Proof.
move=> x p px0; have [-> | nz_p] := eqVneq p 0; first by rewrite derivC mu0.
have [q nz_qx Dp] := mu_spec x nz_p.
case Dm: (\mu_x p) => [|m]; first by rewrite Dp Dm mulr1 (negPf nz_qx) in px0.
rewrite subn1 Dp Dm !derivCE exprS mul1r mulrnAr -mulrnAl mulrA -mulrDl.
rewrite cofactor_XsubC_mu // rootE !(hornerE, hornerMn) subrr mulr0 add0r.
by rewrite mulrn_eq0.
Qed.

Lemma mu_deriv_root : forall x (p : {poly R}), p != 0 -> root p x ->
  \mu_x p  = (\mu_x (p^`()) + 1)%N.
Proof.
by move=> x p p0 rpx; rewrite mu_deriv // subn1 addn1 prednK // mu_gt0.
Qed.

End PolyrealIdomain.




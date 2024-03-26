(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path.
From mathcomp Require Import div choice fintype tuple finfun bigop prime order.
From mathcomp Require Import ssralg poly ssrnum ssrint archimedean rat matrix.
From mathcomp Require Import polydiv perm zmodp mxalgebra vector.

(******************************************************************************)
(* This file provides various results on divisibility of integers.            *)
(* It defines, for m, n, d : int,                                             *)
(*   (m %% d)%Z == the remainder of the Euclidean division of m by d; this is *)
(*                 the least non-negative element of the coset m + dZ when    *)
(*                 d != 0, and m if d = 0.                                    *)
(*   (m %/ d)%Z == the quotient of the Euclidean division of m by d, such     *)
(*                 that m = (m %/ d)%Z * d + (m %% d)%Z. Since for d != 0 the *)
(*                 remainder is non-negative, (m %/ d)%Z is non-zero for      *)
(*                 negative m.                                                *)
(*   (d %| m)%Z <=> m is divisible by d; dvdz d is the (collective) predicate *)
(*                 for integers divisible by d, and (d %| m)%Z is actually    *)
(*                 (transposing) notation for m \in dvdz d.                   *)
(* (m = n %[mod d])%Z, (m == n %[mod d])%Z, (m != n %[mod d])%Z               *)
(*                 m and n are (resp. compare, don't compare) equal mod d.    *)
(*     gcdz m n == the (non-negative) greatest common divisor of m and n,     *)
(*                 with gcdz 0 0 = 0.                                         *)
(*     lcmz m n == the (non-negative) least common multiple of m and n.       *)
(* coprimez m n <=> m and n are coprime.                                      *)
(*    egcdz m n == the Bezout coefficients of the gcd of m and n: a pair      *)
(*                 (u, v) of coprime integers such that u*m + v*n = gcdz m n. *)
(*                 Alternatively, a Bezoutz lemma states such u and v exist.  *)
(* zchinese m1 m2 n1 n2 == for coprime m1 and m2, a solution to the Chinese   *)
(*                 remainder problem for n1 and n2, i.e., and integer n such  *)
(*                 that n = n1 %[mod m1] and n = n2 %[mod m2].                *)
(*  zcontents p == the contents of p : {poly int}, that is, the gcd of the    *)
(*                 coefficients of p, with the same sign as the lead          *)
(*                 coefficient of p.                                          *)
(* zprimitive p == the primitive part of p : {poly int}, i.e., p divided by   *)
(*                 its contents.                                              *)
(* inIntSpan X v <-> v is an integral linear combination of elements of       *)
(*                 X : seq V, where V is a zmodType. We prove that this is a  *)
(*                 decidable property for Q-vector spaces.                    *)
(* int_Smith_normal_form :: a theorem asserting the existence of the Smith    *)
(*                 normal form for integer matrices.                          *)
(* Note that many of the concepts and results in this file could and perhaps  *)
(* should be generalized to the more general setting of integral, unique      *)
(* factorization, principal ideal, or Euclidean domains.                      *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Definition divz (m d : int) : int :=
  let: (K, n) := match m with Posz n => (Posz, n) | Negz n => (Negz, n) end in
  sgz d * K (n %/ `|d|)%N.

Definition modz (m d : int) : int := m - divz m d * d.

Definition dvdz d m := (`|d| %| `|m|)%N.

Definition gcdz m n := (gcdn `|m| `|n|)%:Z.

Definition lcmz m n := (lcmn `|m| `|n|)%:Z.

Definition egcdz m n : int * int :=
  if m == 0 then (0, (-1) ^+ (n < 0)%R) else
  let: (u, v) := egcdn `|m| `|n| in (sgz m * u, - (-1) ^+ (n < 0)%R * v%:Z).

Definition coprimez m n := (gcdz m n == 1).

Infix "%/" := divz : int_scope.
Infix "%%" := modz : int_scope.
Notation "d %| m" := (m \in dvdz d) : int_scope.
Notation "m = n %[mod d ]" := (modz m d = modz n d) : int_scope.
Notation "m == n %[mod d ]" := (modz m d == modz n d) : int_scope.
Notation "m <> n %[mod d ]" := (modz m d <> modz n d) : int_scope.
Notation "m != n %[mod d ]" := (modz m d != modz n d) : int_scope.

Lemma divz_nat (n d : nat) : (n %/ d)%Z = (n %/ d)%N.
Proof. by case: d => // d; rewrite /divz /= mul1r. Qed.

Lemma divzN m d : (m %/ - d)%Z = - (m %/ d)%Z.
Proof. by case: m => n; rewrite /divz /= sgzN abszN mulNr. Qed.

Lemma divz_abs (m d : int) : (m %/ `|d|)%Z = (-1) ^+ (d < 0)%R * (m %/ d)%Z.
Proof.
by rewrite {3}[d]intEsign !mulr_sign; case: ifP => -> //; rewrite divzN opprK.
Qed.

Lemma div0z d : (0 %/ d)%Z = 0.
Proof.
by rewrite -(canLR (signrMK _) (divz_abs _ _)) (divz_nat 0) div0n mulr0.
Qed.

Lemma divNz_nat m d : (d > 0)%N -> (Negz m %/ d)%Z = - (m %/ d).+1%:Z.
Proof. by case: d => // d _; apply: mul1r. Qed.

Lemma divz_eq m d : m = (m %/ d)%Z * d + (m %% d)%Z.
Proof. by rewrite addrC subrK. Qed.

Lemma modzN m d : (m %% - d)%Z = (m %% d)%Z.
Proof. by rewrite /modz divzN mulrNN. Qed.

Lemma modz_abs m d : (m %% `|d|%N)%Z = (m %% d)%Z.
Proof. by rewrite {2}[d]intEsign mulr_sign; case: ifP; rewrite ?modzN. Qed.

Lemma modz_nat (m d : nat) : (m %% d)%Z = (m %% d)%N.
Proof.
by apply: (canLR (addrK _)); rewrite addrC divz_nat {1}(divn_eq m d).
Qed.

Lemma modNz_nat m d : (d > 0)%N -> (Negz m %% d)%Z = d%:Z - 1 - (m %% d)%:Z.
Proof.
rewrite /modz => /divNz_nat->; apply: (canLR (addrK _)).
rewrite -!addrA -!opprD -!PoszD -opprB mulnSr !addnA PoszD addrK.
by rewrite addnAC -addnA mulnC -divn_eq.
Qed.

Lemma modz_ge0 m d : d != 0 -> 0 <= (m %% d)%Z.
Proof.
rewrite -absz_gt0 -modz_abs => d_gt0.
case: m => n; rewrite ?modNz_nat ?modz_nat // -addrA -opprD subr_ge0.
by rewrite lez_nat ltn_mod.
Qed.

Lemma divz0 m : (m %/ 0)%Z = 0. Proof. by case: m. Qed.
Lemma mod0z d : (0 %% d)%Z = 0. Proof. by rewrite /modz div0z mul0r subrr. Qed.
Lemma modz0 m : (m %% 0)%Z = m. Proof. by rewrite /modz mulr0 subr0. Qed.

Lemma divz_small m d : 0 <= m < `|d|%:Z -> (m %/ d)%Z = 0.
Proof.
rewrite -(canLR (signrMK _) (divz_abs _ _)); case: m => // n /divn_small.
by rewrite divz_nat => ->; rewrite mulr0.
Qed.

Lemma divzMDl q m d : d != 0 -> ((q * d + m) %/ d)%Z = q + (m %/ d)%Z.
Proof.
rewrite neq_lt -oppr_gt0 => nz_d.
wlog{nz_d} d_gt0: q d / d > 0; last case: d => // d in d_gt0 *.
  move=> IH; case/orP: nz_d => /IH// /(_  (- q)).
  by rewrite mulrNN !divzN -opprD => /oppr_inj.
wlog q_gt0: q m / q >= 0; last case: q q_gt0 => // q _.
  move=> IH; case: q => n; first exact: IH; rewrite NegzE mulNr.
  by apply: canRL (addKr _) _; rewrite -IH ?addNKr.
case: m => n; first by rewrite !divz_nat divnMDl.
have [le_qd_n | lt_qd_n] := leqP (q * d) n.
  rewrite divNz_nat // NegzE -(subnKC le_qd_n) divnMDl //.
  by rewrite -!addnS !PoszD !opprD !addNKr divNz_nat.
rewrite divNz_nat // NegzE -PoszM subzn // divz_nat.
apply: canRL (addrK _) _; congr _%:Z; rewrite addnC -divnMDl // mulSnr.
rewrite -{3}(subnKC (ltn_pmod n d_gt0)) addnA addnS -divn_eq addnAC.
by rewrite subnKC // divnMDl // divn_small ?addn0 // subnSK ?ltn_mod ?leq_subr.
Qed.

Lemma mulzK m d : d != 0 -> (m * d %/ d)%Z = m.
Proof. by move=> d_nz; rewrite -[m * d]addr0 divzMDl // div0z addr0. Qed.

Lemma mulKz m d : d != 0 -> (d * m %/ d)%Z = m.
Proof. by move=> d_nz; rewrite mulrC mulzK. Qed.

Lemma expzB p m n : p != 0 -> (m >= n)%N -> p ^+ (m - n) = (p ^+ m %/ p ^+ n)%Z.
Proof. by move=> p_nz /subnK{2}<-; rewrite exprD mulzK // expf_neq0. Qed.

Lemma modz1 m : (m %% 1)%Z = 0.
Proof. by case: m => n; rewrite (modNz_nat, modz_nat) ?modn1. Qed.

Lemma divz1 m : (m %/ 1)%Z = m. Proof. by rewrite -{1}[m]mulr1 mulzK. Qed.

Lemma divzz d : (d %/ d)%Z = (d != 0).
Proof. by have [-> // | d_nz] := eqVneq; rewrite -{1}[d]mul1r mulzK. Qed.

Lemma ltz_pmod m d : d > 0 -> (m %% d)%Z < d.
Proof.
case: m d => n [] // d d_gt0; first by rewrite modz_nat ltz_nat ltn_pmod.
by rewrite modNz_nat // -lezD1 addrAC subrK gerDl oppr_le0.
Qed.

Lemma ltz_mod m d : d != 0 -> (m %% d)%Z < `|d|.
Proof. by rewrite -absz_gt0 -modz_abs => d_gt0; apply: ltz_pmod. Qed.

Lemma divzMpl p m d : p > 0 -> (p * m %/ (p * d) = m %/ d)%Z.
Proof.
case: p => // p p_gt0; wlog d_gt0: d / d > 0; last case: d => // d in d_gt0 *.
  by move=> IH; case/intP: d => [|d|d]; rewrite ?mulr0 ?divz0 ?mulrN ?divzN ?IH.
rewrite {1}(divz_eq m d) mulrDr mulrCA divzMDl ?mulf_neq0 ?gt_eqF // addrC.
rewrite divz_small ?add0r // PoszM pmulr_rge0 ?modz_ge0 ?gt_eqF //=.
by rewrite ltr_pM2l ?ltz_pmod.
Qed.
Arguments divzMpl [p m d].

Lemma divzMpr p m d : p > 0 -> (m * p %/ (d * p) = m %/ d)%Z.
Proof. by move=> p_gt0; rewrite -!(mulrC p) divzMpl. Qed.
Arguments divzMpr [p m d].

Lemma lez_floor m d : d != 0 -> (m %/ d)%Z * d <= m.
Proof. by rewrite -subr_ge0; apply: modz_ge0. Qed.

(* leq_mod does not extend to negative m. *)
Lemma lez_div m d : (`|(m %/ d)%Z| <= `|m|)%N.
Proof.
wlog d_gt0: d / d > 0; last case: d d_gt0 => // d d_gt0.
  by move=> IH; case/intP: d => [|n|n]; rewrite ?divz0 ?divzN ?abszN // IH.
case: m => n; first by rewrite divz_nat leq_div.
by rewrite divNz_nat // NegzE !abszN ltnS leq_div.
Qed.

Lemma ltz_ceil m d : d > 0 -> m < ((m %/ d)%Z + 1) * d.
Proof.
by case: d => // d d_gt0; rewrite mulrDl mul1r -ltrBlDl ltz_mod ?gt_eqF.
Qed.

Lemma ltz_divLR m n d : d > 0 -> ((m %/ d)%Z < n) = (m < n * d).
Proof.
move=> d_gt0; apply/idP/idP.
  by rewrite -[_ < n]lezD1 -(ler_pM2r d_gt0); exact/lt_le_trans/ltz_ceil.
by rewrite -(ltr_pM2r d_gt0 _ n); apply/le_lt_trans/lez_floor; rewrite gt_eqF.
Qed.

Lemma lez_divRL m n d : d > 0 -> (m <= (n %/ d)%Z) = (m * d <= n).
Proof. by move=> d_gt0; rewrite !leNgt ltz_divLR. Qed.

Lemma lez_pdiv2r d : 0 <= d -> {homo divz^~ d : m n / m <= n}.
Proof.
by case: d => [[|d]|]// _ [] m [] n //; rewrite /divz !mul1r; apply: leq_div2r.
Qed.

Lemma divz_ge0 m d : d > 0 -> ((m %/ d)%Z >= 0) = (m >= 0).
Proof. by case: d m => // d [] n d_gt0; rewrite (divz_nat, divNz_nat). Qed.

Lemma divzMA_ge0 m n p : n >= 0 -> (m %/ (n * p) = (m %/ n)%Z %/ p)%Z.
Proof.
case: n => // [[|n]] _; first by rewrite mul0r !divz0 div0z.
wlog p_gt0: p / p > 0; last case: p => // p in p_gt0 *.
  by case/intP: p => [|p|p] IH; rewrite ?mulr0 ?divz0 ?mulrN ?divzN // IH.
rewrite {2}(divz_eq m (n.+1%:Z * p)) mulrA mulrAC !divzMDl // ?gt_eqF //.
rewrite [rhs in _ + rhs]divz_small ?addr0 // ltz_divLR // divz_ge0 //.
by rewrite mulrC ltz_pmod ?modz_ge0 ?gt_eqF ?pmulr_lgt0.
Qed.

Lemma modz_small m d : 0 <= m < d -> (m %% d)%Z = m.
Proof. by case: m d => //= m [] // d; rewrite modz_nat => /modn_small->. Qed.

Lemma modz_mod m d : ((m %% d)%Z = m %[mod d])%Z.
Proof.
rewrite -!(modz_abs _ d); case: {d}`|d|%N => [|d]; first by rewrite !modz0.
by rewrite modz_small ?modz_ge0 ?ltz_mod.
Qed.

Lemma modzMDl p m d : (p * d + m = m %[mod d])%Z.
Proof.
have [-> | d_nz] := eqVneq d 0; first by rewrite mulr0 add0r.
by rewrite /modz divzMDl // mulrDl opprD addrACA subrr add0r.
Qed.

Lemma mulz_modr {p m d} : 0 < p -> p * (m %% d)%Z = ((p * m) %% (p * d))%Z.
Proof.
case: p => // p p_gt0; rewrite mulrBr; apply: canLR (addrK _) _.
by rewrite mulrCA -(divzMpl p_gt0) subrK.
Qed.

Lemma mulz_modl {p m d} : 0 < p -> (m %% d)%Z * p = ((m * p) %% (d * p))%Z.
Proof. by rewrite -!(mulrC p); apply: mulz_modr. Qed.

Lemma modzDl m d : (d + m = m %[mod d])%Z.
Proof. by rewrite -{1}[d]mul1r modzMDl. Qed.

Lemma modzDr m d : (m + d = m %[mod d])%Z.
Proof. by rewrite addrC modzDl. Qed.

Lemma modzz d : (d %% d)%Z = 0.
Proof. by rewrite -{1}[d]addr0 modzDl mod0z. Qed.

Lemma modzMl p d : (p * d %% d)%Z = 0.
Proof. by rewrite -[p * d]addr0 modzMDl mod0z. Qed.

Lemma modzMr p d : (d * p %% d)%Z = 0.
Proof. by rewrite mulrC modzMl. Qed.

Lemma modzDml m n d : ((m %% d)%Z + n = m + n %[mod d])%Z.
Proof. by rewrite {2}(divz_eq m d) -[_ * d + _ + n]addrA modzMDl. Qed.

Lemma modzDmr m n d : (m + (n %% d)%Z = m + n %[mod d])%Z.
Proof. by rewrite !(addrC m) modzDml. Qed.

Lemma modzDm m n d : ((m %% d)%Z + (n %% d)%Z = m + n %[mod d])%Z.
Proof. by rewrite modzDml modzDmr. Qed.

Lemma eqz_modDl p m n d : (p + m == p + n %[mod d])%Z = (m == n %[mod d])%Z.
Proof.
have [-> | d_nz] := eqVneq d 0; first by rewrite !modz0 (inj_eq (addrI p)).
apply/eqP/eqP=> eq_mn; last by rewrite -modzDmr eq_mn modzDmr.
by rewrite -(addKr p m) -modzDmr eq_mn modzDmr addKr.
Qed.

Lemma eqz_modDr p m n d : (m + p == n + p %[mod d])%Z = (m == n %[mod d])%Z.
Proof. by rewrite -!(addrC p) eqz_modDl. Qed.

Lemma modzMml m n d : ((m %% d)%Z * n = m * n %[mod d])%Z.
Proof. by rewrite {2}(divz_eq m d) [in RHS]mulrDl mulrAC modzMDl. Qed.  (* FIXME: rewrite pattern *)

Lemma modzMmr m n d : (m * (n %% d)%Z = m * n %[mod d])%Z.
Proof. by rewrite !(mulrC m) modzMml. Qed.

Lemma modzMm m n d : ((m %% d)%Z * (n %% d)%Z = m * n %[mod d])%Z.
Proof. by rewrite modzMml modzMmr. Qed.

Lemma modzXm k m d : ((m %% d)%Z ^+ k = m ^+ k %[mod d])%Z.
Proof. by elim: k => // k IHk; rewrite !exprS -modzMmr IHk modzMm. Qed.

Lemma modzNm m d : (- (m %% d)%Z = - m %[mod d])%Z.
Proof. by rewrite -mulN1r modzMmr mulN1r. Qed.

Lemma modz_absm m d : ((-1) ^+ (m < 0)%R * (m %% d)%Z = `|m|%:Z %[mod d])%Z.
Proof. by rewrite modzMmr -abszEsign. Qed.

(** Divisibility **)

Lemma dvdzE d m : (d %| m)%Z = (`|d| %| `|m|)%N. Proof. by []. Qed.
Lemma dvdz0 d : (d %| 0)%Z. Proof. exact: dvdn0. Qed.
Lemma dvd0z n : (0 %| n)%Z = (n == 0). Proof. by rewrite -absz_eq0 -dvd0n. Qed.
Lemma dvdz1 d : (d %| 1)%Z = (`|d|%N == 1). Proof. exact: dvdn1. Qed.
Lemma dvd1z m : (1 %| m)%Z. Proof. exact: dvd1n. Qed.
Lemma dvdzz m : (m %| m)%Z. Proof. exact: dvdnn. Qed.

Lemma dvdz_mull d m n : (d %| n)%Z -> (d %| m * n)%Z.
Proof. by rewrite !dvdzE abszM; apply: dvdn_mull. Qed.

Lemma dvdz_mulr d m n : (d %| m)%Z -> (d %| m * n)%Z.
Proof. by move=> d_m; rewrite mulrC dvdz_mull. Qed.
#[global] Hint Resolve dvdz0 dvd1z dvdzz dvdz_mull dvdz_mulr : core.

Lemma dvdz_mul d1 d2 m1 m2 : (d1 %| m1 -> d2 %| m2 -> d1 * d2 %| m1 * m2)%Z.
Proof. by rewrite !dvdzE !abszM; apply: dvdn_mul. Qed.

Lemma dvdz_trans n d m : (d %| n -> n %| m -> d %| m)%Z.
Proof. by rewrite !dvdzE; apply: dvdn_trans. Qed.

Lemma dvdzP d m : reflect (exists q, m = q * d) (d %| m)%Z.
Proof.
apply: (iffP dvdnP) => [] [q Dm]; last by exists `|q|%N; rewrite Dm abszM.
exists ((-1) ^+ (m < 0)%R * q%:Z * (-1) ^+ (d < 0)%R).
by rewrite -!mulrA -abszEsign -PoszM -Dm -intEsign.
Qed.
Arguments dvdzP {d m}.

Lemma dvdz_mod0P d m : reflect (m %% d = 0)%Z (d %| m)%Z.
Proof.
apply: (iffP dvdzP) => [[q ->] | md0]; first by rewrite modzMl.
by rewrite (divz_eq m d) md0 addr0; exists (m %/ d)%Z.
Qed.
Arguments dvdz_mod0P {d m}.

Lemma dvdz_eq d m : (d %| m)%Z = ((m %/ d)%Z * d == m).
Proof. by rewrite (sameP dvdz_mod0P eqP) subr_eq0 eq_sym. Qed.

Lemma divzK d m : (d %| m)%Z -> (m %/ d)%Z * d = m.
Proof. by rewrite dvdz_eq => /eqP. Qed.

Lemma lez_divLR d m n : 0 < d -> (d %| m)%Z -> ((m %/ d)%Z <= n) = (m <= n * d).
Proof. by move=> /ler_pM2r <- /divzK->. Qed.

Lemma ltz_divRL d m n : 0 < d -> (d %| m)%Z -> (n < m %/ d)%Z = (n * d < m).
Proof. by move=> /ltr_pM2r/(_ n)<- /divzK->. Qed.

Lemma eqz_div d m n : d != 0 -> (d %| m)%Z -> (n == m %/ d)%Z = (n * d == m).
Proof. by move=> /mulIf/inj_eq <- /divzK->. Qed.

Lemma eqz_mul d m n : d != 0 -> (d %| m)%Z -> (m == n * d) = (m %/ d == n)%Z.
Proof. by move=> d_gt0 dv_d_m; rewrite eq_sym -eqz_div // eq_sym. Qed.

Lemma divz_mulAC d m n : (d %| m)%Z -> (m %/ d)%Z * n = (m * n %/ d)%Z.
Proof.
have [-> | d_nz] := eqVneq d 0; first by rewrite !divz0 mul0r.
by move/divzK=> {2} <-; rewrite mulrAC mulzK.
Qed.

Lemma mulz_divA d m n : (d %| n)%Z -> m * (n %/ d)%Z = (m * n %/ d)%Z.
Proof. by move=> dv_d_m; rewrite !(mulrC m) divz_mulAC. Qed.

Lemma mulz_divCA d m n :
  (d %| m)%Z -> (d %| n)%Z -> m * (n %/ d)%Z = n * (m %/ d)%Z.
Proof. by move=> dv_d_m dv_d_n; rewrite mulrC divz_mulAC ?mulz_divA. Qed.

Lemma divzA m n p : (p %| n -> n %| m * p -> m %/ (n %/ p)%Z = m * p %/ n)%Z.
Proof.
move/divzK=> p_dv_n; have [->|] := eqVneq n 0; first by rewrite div0z !divz0.
rewrite -{1 2}p_dv_n mulf_eq0 => /norP[pn_nz p_nz] /divzK; rewrite mulrA p_dv_n.
by move/mulIf=> {1} <- //; rewrite mulzK.
Qed.

Lemma divzMA m n p : (n * p %| m -> m %/ (n * p) = (m %/ n)%Z %/ p)%Z.
Proof.
have [-> | nz_p] := eqVneq p 0; first by rewrite mulr0 !divz0.
have [-> | nz_n] := eqVneq n 0; first by rewrite mul0r !divz0 div0z.
by move/divzK=> {2} <-; rewrite mulrA mulrAC !mulzK.
Qed.

Lemma divzAC m n p : (n * p %| m -> (m %/ n)%Z %/ p =  (m %/ p)%Z %/ n)%Z.
Proof. by move=> np_dv_mn; rewrite -!divzMA // mulrC. Qed.

Lemma divzMl p m d : p != 0 -> (d %| m -> p * m %/ (p * d) = m %/ d)%Z.
Proof.
have [-> | nz_d nz_p] := eqVneq d 0; first by rewrite mulr0 !divz0.
by move/divzK=> {1}<-; rewrite mulrCA mulzK ?mulf_neq0.
Qed.

Lemma divzMr p m d : p != 0 -> (d %| m -> m * p %/ (d * p) = m %/ d)%Z.
Proof. by rewrite -!(mulrC p); apply: divzMl. Qed.

Lemma dvdz_mul2l p d m : p != 0 -> (p * d %| p * m)%Z = (d %| m)%Z.
Proof. by rewrite !dvdzE -absz_gt0 !abszM; apply: dvdn_pmul2l. Qed.
Arguments dvdz_mul2l [p d m].

Lemma dvdz_mul2r p d m : p != 0 -> (d * p %| m * p)%Z = (d %| m)%Z.
Proof. by rewrite !dvdzE -absz_gt0 !abszM; apply: dvdn_pmul2r. Qed.
Arguments dvdz_mul2r [p d m].

Lemma dvdz_exp2l p m n : (m <= n)%N -> (p ^+ m %| p ^+ n)%Z.
Proof. by rewrite dvdzE !abszX; apply: dvdn_exp2l. Qed.

Lemma dvdz_Pexp2l p m n : `|p| > 1 -> (p ^+ m %| p ^+ n)%Z = (m <= n)%N.
Proof. by rewrite dvdzE !abszX ltz_nat; apply: dvdn_Pexp2l. Qed.

Lemma dvdz_exp2r m n k : (m %| n -> m ^+ k %| n ^+ k)%Z.
Proof. by rewrite !dvdzE !abszX; apply: dvdn_exp2r. Qed.

Fact dvdz_zmod_closed d : zmod_closed (dvdz d).
Proof.
split=> [|_ _ /dvdzP[p ->] /dvdzP[q ->]]; first exact: dvdz0.
by rewrite -mulrBl dvdz_mull.
Qed.
HB.instance Definition _ d := GRing.isZmodClosed.Build int (dvdz d)
  (dvdz_zmod_closed d).

Lemma dvdz_exp k d m : (0 < k)%N -> (d %| m -> d %| m ^+ k)%Z.
Proof. by case: k => // k _ d_dv_m; rewrite exprS dvdz_mulr. Qed.

Lemma eqz_mod_dvd d m n : (m == n %[mod d])%Z = (d %| m - n)%Z.
Proof.
apply/eqP/dvdz_mod0P=> eq_mn.
  by rewrite -modzDml eq_mn modzDml subrr mod0z.
by rewrite -(subrK n m) -modzDml eq_mn add0r.
Qed.

Lemma divzDl m n d :
  (d %| m)%Z -> ((m + n) %/ d)%Z = (m %/ d)%Z + (n %/ d)%Z.
Proof.
have [-> | d_nz] := eqVneq d 0; first by rewrite !divz0.
by move/divzK=> {1}<-; rewrite divzMDl.
Qed.

Lemma divzDr m n d :
  (d %| n)%Z -> ((m + n) %/ d)%Z = (m %/ d)%Z + (n %/ d)%Z.
Proof. by move=> dv_n; rewrite addrC divzDl // addrC. Qed.

Lemma Qint_dvdz (m d : int) : (d %| m)%Z -> (m%:~R / d%:~R : rat) \is a Num.int.
Proof.
case/dvdzP=> z ->; rewrite rmorphM /=; have [->|dn0] := eqVneq d 0.
  by rewrite mulr0 mul0r.
by rewrite mulfK ?intr_eq0.
Qed.

Lemma Qnat_dvd (m d : nat) : (d %| m)%N -> (m%:R / d%:R : rat) \is a Num.nat.
Proof. by move=> h; rewrite natrEint divr_ge0 ?ler0n // !pmulrn Qint_dvdz. Qed.

(* Greatest common divisor *)

Lemma gcdzz m : gcdz m m = `|m|%:Z. Proof. by rewrite /gcdz gcdnn. Qed.
Lemma gcdzC : commutative gcdz. Proof. by move=> m n; rewrite /gcdz gcdnC. Qed.
Lemma gcd0z m : gcdz 0 m = `|m|%:Z. Proof. by rewrite /gcdz gcd0n. Qed.
Lemma gcdz0 m : gcdz m 0 = `|m|%:Z. Proof. by rewrite /gcdz gcdn0. Qed.
Lemma gcd1z : left_zero 1 gcdz. Proof. by move=> m; rewrite /gcdz gcd1n. Qed.
Lemma gcdz1 : right_zero 1 gcdz. Proof. by move=> m; rewrite /gcdz gcdn1. Qed.
Lemma dvdz_gcdr m n : (gcdz m n %| n)%Z. Proof. exact: dvdn_gcdr. Qed.
Lemma dvdz_gcdl m n : (gcdz m n %| m)%Z. Proof. exact: dvdn_gcdl. Qed.
Lemma gcdz_eq0 m n : (gcdz m n == 0) = (m == 0) && (n == 0).
Proof. by rewrite -absz_eq0 eqn0Ngt gcdn_gt0 !negb_or -!eqn0Ngt !absz_eq0. Qed.
Lemma gcdNz m n : gcdz (- m) n = gcdz m n. Proof. by rewrite /gcdz abszN. Qed.
Lemma gcdzN m n : gcdz m (- n) = gcdz m n. Proof. by rewrite /gcdz abszN. Qed.

Lemma gcdz_modr m n : gcdz m (n %% m)%Z = gcdz m n.
Proof.
rewrite -modz_abs /gcdz; move/absz: m => m.
have [-> | m_gt0] := posnP m; first by rewrite modz0.
case: n => n; first by rewrite modz_nat gcdn_modr.
rewrite modNz_nat // NegzE abszN {2}(divn_eq n m) -addnS gcdnMDl.
rewrite -addrA -opprD -intS /=; set m1 := _.+1.
have le_m1m: (m1 <= m)%N by apply: ltn_pmod.
by rewrite subzn // !(gcdnC m) -{2 3}(subnK le_m1m) gcdnDl gcdnDr gcdnC.
Qed.

Lemma gcdz_modl m n : gcdz (m %% n)%Z n = gcdz m n.
Proof. by rewrite -!(gcdzC n) gcdz_modr. Qed.

Lemma gcdzMDl q m n : gcdz m (q * m + n) = gcdz m n.
Proof. by rewrite -gcdz_modr modzMDl gcdz_modr. Qed.
 
Lemma gcdzDl m n : gcdz m (m + n) = gcdz m n.
Proof. by rewrite -{2}(mul1r m) gcdzMDl. Qed.

Lemma gcdzDr m n : gcdz m (n + m) = gcdz m n.
Proof. by rewrite addrC gcdzDl. Qed.

Lemma gcdzMl n m : gcdz n (m * n) = `|n|%:Z.
Proof. by rewrite -[m * n]addr0 gcdzMDl gcdz0. Qed.

Lemma gcdzMr n m : gcdz n (n * m) = `|n|%:Z.
Proof. by rewrite mulrC gcdzMl. Qed.

Lemma gcdz_idPl {m n} : reflect (gcdz m n = `|m|%:Z) (m %| n)%Z.
Proof. by apply: (iffP gcdn_idPl) => [<- | []]. Qed.

Lemma gcdz_idPr {m n} : reflect (gcdz m n = `|n|%:Z) (n %| m)%Z.
Proof. by rewrite gcdzC; apply: gcdz_idPl. Qed.

Lemma expz_min e m n : e >= 0 -> e ^+ minn m n = gcdz (e ^+ m) (e ^+ n).
Proof.
by case: e => // e _; rewrite /gcdz !abszX -expn_min -natz -natrX !natz.
Qed.

Lemma dvdz_gcd p m n : (p %| gcdz m n)%Z = (p %| m)%Z && (p %| n)%Z.
Proof. exact: dvdn_gcd. Qed.

Lemma gcdzAC : right_commutative gcdz.
Proof. by move=> m n p; rewrite /gcdz gcdnAC. Qed.

Lemma gcdzA : associative gcdz.
Proof. by move=> m n p; rewrite /gcdz gcdnA. Qed.

Lemma gcdzCA : left_commutative gcdz.
Proof. by move=> m n p; rewrite /gcdz gcdnCA. Qed.

Lemma gcdzACA : interchange gcdz gcdz.
Proof. by move=> m n p q; rewrite /gcdz gcdnACA. Qed.

Lemma mulz_gcdr m n p : `|m|%:Z * gcdz n p = gcdz (m * n) (m * p).
Proof. by rewrite -PoszM muln_gcdr -!abszM. Qed.

Lemma mulz_gcdl m n p : gcdz m n * `|p|%:Z = gcdz (m * p) (n * p).
Proof. by rewrite -PoszM muln_gcdl -!abszM. Qed.

Lemma mulz_divCA_gcd n m : n * (m %/ gcdz n m)%Z  = m * (n %/ gcdz n m)%Z.
Proof. by rewrite mulz_divCA ?dvdz_gcdl ?dvdz_gcdr. Qed.

(* Least common multiple *)

Lemma dvdz_lcmr m n : (n %| lcmz m n)%Z.
Proof. exact: dvdn_lcmr. Qed.

Lemma dvdz_lcml m n : (m %| lcmz m n)%Z.
Proof. exact: dvdn_lcml. Qed.

Lemma dvdz_lcm d1 d2 m : ((lcmn d1 d2 %| m) = (d1 %| m) && (d2 %| m))%Z.
Proof. exact: dvdn_lcm. Qed.

Lemma lcmzC : commutative lcmz.
Proof. by move=> m n; rewrite /lcmz lcmnC. Qed.

Lemma lcm0z : left_zero 0 lcmz.
Proof. by move=> x; rewrite /lcmz absz0 lcm0n. Qed.

Lemma lcmz0 : right_zero 0 lcmz.
Proof. by move=> x; rewrite /lcmz absz0 lcmn0. Qed.

Lemma lcmz_ge0 m n : 0 <= lcmz m n.
Proof. by []. Qed.

Lemma lcmz_neq0 m n : (lcmz m n != 0) = (m != 0) && (n != 0).
Proof.
have [->|m_neq0] := eqVneq m 0; first by rewrite lcm0z.
have [->|n_neq0] := eqVneq n 0; first by rewrite lcmz0.
by rewrite gt_eqF// [0 < _]lcmn_gt0 !absz_gt0 m_neq0 n_neq0.
Qed.

(* Coprime factors *)

Lemma coprimezE m n : coprimez m n = coprime `|m| `|n|. Proof. by []. Qed.

Lemma coprimez_sym : symmetric coprimez.
Proof. by move=> m n; apply: coprime_sym. Qed.

Lemma coprimeNz m n : coprimez (- m) n = coprimez m n.
Proof. by rewrite coprimezE abszN. Qed.

Lemma coprimezN m n : coprimez m (- n) = coprimez m n.
Proof. by rewrite coprimezE abszN. Qed.

Variant egcdz_spec m n : int * int -> Type :=
  EgcdzSpec u v of u * m + v * n = gcdz m n & coprimez u v
     : egcdz_spec m n (u, v).

Lemma egcdzP m n : egcdz_spec m n (egcdz m n).
Proof.
rewrite /egcdz; have [-> | m_nz] := eqVneq.
  by split; [rewrite -abszEsign gcd0z | rewrite coprimezE absz_sign].
have m_gt0 : (`|m| > 0)%N by rewrite absz_gt0.
case: egcdnP (coprime_egcdn `|n| m_gt0) => //= u v Duv _ co_uv; split.
  rewrite !mulNr -!mulrA mulrCA -abszEsg mulrCA -abszEsign.
  by rewrite -!PoszM Duv addnC PoszD addrK.
by rewrite coprimezE abszM absz_sg m_nz mul1n mulNr abszN abszMsign.
Qed.

Lemma Bezoutz m n : {u : int & {v : int | u * m + v * n = gcdz m n}}.
Proof. by exists (egcdz m n).1, (egcdz m n).2; case: egcdzP. Qed.

Lemma coprimezP m n :
  reflect (exists uv, uv.1 * m + uv.2 * n = 1) (coprimez m n).
Proof.
apply: (iffP eqP) => [<-| [[u v] /= Duv]].
  by exists (egcdz m n); case: egcdzP.
congr _%:Z; apply: gcdn_def; rewrite ?dvd1n // => d dv_d_n dv_d_m.
by rewrite -(dvdzE d 1) -Duv [m]intEsg [n]intEsg rpredD ?dvdz_mull.
Qed.

Lemma Gauss_dvdz m n p :
  coprimez m n -> (m * n %| p)%Z = (m %| p)%Z && (n %| p)%Z.
Proof. by move/Gauss_dvd <-; rewrite -abszM. Qed.

Lemma Gauss_dvdzr m n p : coprimez m n -> (m %| n * p)%Z = (m %| p)%Z.
Proof. by rewrite dvdzE abszM => /Gauss_dvdr->. Qed.

Lemma Gauss_dvdzl m n p : coprimez m p -> (m %| n * p)%Z = (m %| n)%Z.
Proof. by rewrite mulrC; apply: Gauss_dvdzr. Qed.

Lemma Gauss_gcdzr p m n : coprimez p m -> gcdz p (m * n) = gcdz p n.
Proof. by rewrite /gcdz abszM => /Gauss_gcdr->. Qed.

Lemma Gauss_gcdzl p m n : coprimez p n -> gcdz p (m * n) = gcdz p m.
Proof. by move=> co_pn; rewrite mulrC Gauss_gcdzr. Qed.

Lemma coprimezMr p m n : coprimez p (m * n) = coprimez p m && coprimez p n.
Proof. by rewrite -coprimeMr -abszM. Qed.

Lemma coprimezMl p m n : coprimez (m * n) p = coprimez m p && coprimez n p.
Proof. by rewrite -coprimeMl -abszM. Qed.

Lemma coprimez_pexpl k m n : (0 < k)%N -> coprimez (m ^+ k) n = coprimez m n.
Proof. by rewrite /coprimez /gcdz abszX; apply: coprime_pexpl. Qed.

Lemma coprimez_pexpr k m n : (0 < k)%N -> coprimez m (n ^+ k) = coprimez m n.
Proof. by move=> k_gt0; rewrite !(coprimez_sym m) coprimez_pexpl. Qed.

Lemma coprimezXl k m n : coprimez m n -> coprimez (m ^+ k) n.
Proof. by rewrite /coprimez /gcdz abszX; apply: coprimeXl. Qed.

Lemma coprimezXr k m n : coprimez m n -> coprimez m (n ^+ k).
Proof. by rewrite !(coprimez_sym m); apply: coprimezXl. Qed.

Lemma coprimez_dvdl m n p : (m %| n)%N -> coprimez n p -> coprimez m p.
Proof. exact: coprime_dvdl. Qed.

Lemma coprimez_dvdr m n p : (m %| n)%N -> coprimez p n -> coprimez p m.
Proof. exact: coprime_dvdr. Qed.

Lemma dvdz_pexp2r m n k : (k > 0)%N -> (m ^+ k %| n ^+ k)%Z = (m %| n)%Z.
Proof. by rewrite dvdzE !abszX; apply: dvdn_pexp2r. Qed.

Section Chinese.

(***********************************************************************)
(*   The chinese remainder theorem                                     *)
(***********************************************************************)

Variables m1 m2 : int.
Hypothesis co_m12 : coprimez m1 m2.

Lemma zchinese_remainder x y :
  (x == y %[mod m1 * m2])%Z = (x == y %[mod m1])%Z && (x == y %[mod m2])%Z.
Proof. by rewrite !eqz_mod_dvd Gauss_dvdz. Qed.

(***********************************************************************)
(*   A function that solves the chinese remainder problem              *)
(***********************************************************************)

Definition zchinese r1 r2 :=
  r1 * m2 * (egcdz m1 m2).2 + r2 * m1 * (egcdz m1 m2).1.

Lemma zchinese_modl r1 r2 : (zchinese r1 r2 = r1 %[mod m1])%Z.
Proof.
rewrite /zchinese; have [u v /= Duv _] := egcdzP m1 m2.
rewrite -{2}[r1]mulr1 -((gcdz _ _ =P 1) co_m12) -Duv.
by rewrite mulrDr mulrAC addrC (mulrAC r2) !mulrA !modzMDl.
Qed.

Lemma zchinese_modr r1 r2 : (zchinese r1 r2 = r2 %[mod m2])%Z.
Proof.
rewrite /zchinese; have [u v /= Duv _] := egcdzP m1 m2.
rewrite -{2}[r2]mulr1 -((gcdz _ _ =P 1) co_m12) -Duv.
by rewrite mulrAC modzMDl mulrAC addrC mulrDr !mulrA modzMDl.
Qed.

Lemma zchinese_mod x : (x = zchinese (x %% m1)%Z (x %% m2)%Z %[mod m1 * m2])%Z.
Proof.
apply/eqP; rewrite zchinese_remainder //.
by rewrite zchinese_modl zchinese_modr !modz_mod !eqxx.
Qed.

End Chinese.

Section ZpolyScale.

Definition zcontents (p : {poly int}) : int :=
  sgz (lead_coef p) * \big[gcdn/0]_(i < size p) `|(p`_i)%R|%N.

Lemma sgz_contents p : sgz (zcontents p) = sgz (lead_coef p).
Proof.
rewrite /zcontents mulrC sgzM sgz_id; set d := _%:Z.
have [-> | nz_p] := eqVneq p 0; first by rewrite lead_coef0 mulr0.
rewrite gtr0_sgz ?mul1r // ltz_nat polySpred ?big_ord_recr //= -lead_coefE.
by rewrite gcdn_gt0 orbC absz_gt0 lead_coef_eq0 nz_p.
Qed.

Lemma zcontents_eq0 p : (zcontents p == 0) = (p == 0).
Proof. by rewrite -sgz_eq0 sgz_contents sgz_eq0 lead_coef_eq0. Qed.

Lemma zcontents0 : zcontents 0 = 0.
Proof. by apply/eqP; rewrite zcontents_eq0. Qed.

Lemma zcontentsZ a p : zcontents (a *: p) = a * zcontents p.
Proof.
have [-> | nz_a] := eqVneq a 0; first by rewrite scale0r mul0r zcontents0.
rewrite {2}[a]intEsg mulrCA -mulrA -PoszM big_distrr /= mulrCA mulrA -sgzM.
rewrite -lead_coefZ; congr (_ * _%:Z); rewrite size_scale //.
by apply: eq_bigr => i _; rewrite coefZ abszM.
Qed.

Lemma zcontents_monic p : p \is monic -> zcontents p = 1.
Proof.
move=> mon_p; rewrite /zcontents polySpred ?monic_neq0 //.
by rewrite big_ord_recr /= -lead_coefE (monicP mon_p) gcdn1.
Qed.

Lemma dvdz_contents a p : (a %| zcontents p)%Z = (p \is a polyOver (dvdz a)).
Proof.
rewrite dvdzE abszM absz_sg lead_coef_eq0.
have [-> | nz_p] := eqVneq; first by rewrite mul0n dvdn0 rpred0.
rewrite mul1n; apply/dvdn_biggcdP/(all_nthP 0)=> a_dv_p i ltip /=.
  exact: (a_dv_p (Ordinal ltip)).
exact: a_dv_p.
Qed.

Lemma map_poly_divzK {a} p :
  p \is a polyOver (dvdz a) -> a *: map_poly (divz^~ a) p = p.
Proof.
move/polyOverP=> a_dv_p; apply/polyP=> i.
by rewrite coefZ coef_map_id0 ?div0z // mulrC divzK.
Qed.

Lemma polyOver_dvdzP a p :
  reflect (exists q, p = a *: q) (p \is a polyOver (dvdz a)).
Proof.
apply: (iffP idP) => [/map_poly_divzK | [q ->]].
  by exists (map_poly (divz^~ a) p).
by apply/polyOverP=> i; rewrite coefZ dvdz_mulr.
Qed.

Definition zprimitive p := map_poly (divz^~ (zcontents p)) p.

Lemma zpolyEprim p : p = zcontents p *: zprimitive p.
Proof. by rewrite map_poly_divzK // -dvdz_contents. Qed.

Lemma zprimitive0 : zprimitive 0 = 0.
Proof.
by apply/polyP=> i; rewrite coef0 coef_map_id0 ?div0z // zcontents0 divz0.
Qed.

Lemma zprimitive_eq0 p : (zprimitive p == 0) = (p == 0).
Proof.
apply/idP/idP=> /eqP p0; first by rewrite [p]zpolyEprim p0 scaler0.
by rewrite p0 zprimitive0.
Qed.

Lemma size_zprimitive p : size (zprimitive p) = size p.
Proof.
have [-> | ] := eqVneq p 0; first by rewrite zprimitive0.
by rewrite {1 3}[p]zpolyEprim scale_poly_eq0 => /norP[/size_scale-> _].
Qed.

Lemma sgz_lead_primitive p : sgz (lead_coef (zprimitive p)) = (p != 0).
Proof.
have [-> | nz_p] := eqVneq; first by rewrite zprimitive0 lead_coef0.
apply: (@mulfI _ (sgz (zcontents p))); first by rewrite sgz_eq0 zcontents_eq0.
by rewrite -sgzM mulr1 -lead_coefZ -zpolyEprim sgz_contents.
Qed.

Lemma zcontents_primitive p : zcontents (zprimitive p) = (p != 0).
Proof.
have [-> | nz_p] := eqVneq; first by rewrite zprimitive0 zcontents0.
apply: (@mulfI _ (zcontents p)); first by rewrite zcontents_eq0.
by rewrite mulr1 -zcontentsZ -zpolyEprim.
Qed.

Lemma zprimitive_id p : zprimitive (zprimitive p) = zprimitive p.
Proof.
have [-> | nz_p] := eqVneq p 0; first by rewrite !zprimitive0.
by rewrite {2}[zprimitive p]zpolyEprim zcontents_primitive nz_p scale1r.
Qed.

Lemma zprimitive_monic p : p \in monic -> zprimitive p = p.
Proof. by move=> mon_p; rewrite {2}[p]zpolyEprim zcontents_monic ?scale1r. Qed.

Lemma zprimitiveZ a p : a != 0 -> zprimitive (a *: p) = zprimitive p.
Proof.
have [-> | nz_p nz_a] := eqVneq p 0; first by rewrite scaler0.
apply: (@mulfI _ (a * zcontents p)%:P).
  by rewrite polyC_eq0 mulf_neq0 ?zcontents_eq0.
by rewrite -{1}zcontentsZ !mul_polyC -zpolyEprim -scalerA -zpolyEprim.
Qed.

Lemma zprimitive_min p a q :
    p != 0 -> p = a *: q ->
  {b | sgz b = sgz (lead_coef q) & q = b *: zprimitive p}.
Proof.
move=> nz_p Dp; have /dvdzP/sig_eqW[b Db]: (a %| zcontents p)%Z.
  by rewrite dvdz_contents; apply/polyOver_dvdzP; exists q.
suffices ->: q = b *: zprimitive p.
  by rewrite lead_coefZ sgzM sgz_lead_primitive nz_p mulr1; exists b.
apply: (@mulfI _ a%:P).
  by apply: contraNneq nz_p; rewrite Dp -mul_polyC => ->; rewrite mul0r.
by rewrite !mul_polyC -Dp scalerA mulrC -Db -zpolyEprim.
Qed.

Lemma zprimitive_irr p a q :
  p != 0 -> zprimitive p = a *: q -> a = sgz (lead_coef q).
Proof.
move=> nz_p Dp; have: p = (a * zcontents p) *: q.
  by rewrite mulrC -scalerA -Dp -zpolyEprim.
case/zprimitive_min=> // b <- /eqP.
rewrite Dp -{1}[q]scale1r scalerA -subr_eq0 -scalerBl scale_poly_eq0 subr_eq0.
have{Dp} /negPf->: q != 0.
  by apply: contraNneq nz_p; rewrite -zprimitive_eq0 Dp => ->; rewrite scaler0.
by case: b a => [[|[|b]] | [|b]] [[|[|a]] | [|a]] //; rewrite mulr0.
Qed.

Lemma zcontentsM p q : zcontents (p * q) = zcontents p * zcontents q.
Proof.
have [-> | nz_p] := eqVneq p 0; first by rewrite !(mul0r, zcontents0).
have [-> | nz_q] := eqVneq q 0; first by rewrite !(mulr0, zcontents0).
rewrite -[zcontents q]mulr1 {1}[p]zpolyEprim {1}[q]zpolyEprim.
rewrite -scalerAl -scalerAr !zcontentsZ; congr (_ * (_ * _)).
rewrite [zcontents _]intEsg sgz_contents lead_coefM sgzM !sgz_lead_primitive.
apply/eqP; rewrite nz_p nz_q !mul1r [_ == _]eqn_leq absz_gt0 zcontents_eq0.
rewrite mulf_neq0 ?zprimitive_eq0 // andbT leqNgt.
apply/negP=> /pdivP[r r_pr r_dv_d]; pose to_r : int -> 'F_r := intr.
have nz_prim_r q1: q1 != 0 -> map_poly to_r (zprimitive q1) != 0.
  move=> nz_q1; apply: contraTneq (prime_gt1 r_pr) => r_dv_q1.
  rewrite -leqNgt dvdn_leq // -(dvdzE r true) -nz_q1 -zcontents_primitive.
  rewrite dvdz_contents; apply/polyOverP=> i /=; rewrite dvdzE /=.
  have /polyP/(_ i)/eqP := r_dv_q1; rewrite coef_map coef0 /=.
  rewrite {1}[_`_i]intEsign rmorphM /= rmorph_sign /= mulf_eq0 signr_eq0 /=.
  by rewrite -val_eqE /= val_Fp_nat.
suffices{nz_prim_r} /idPn[]: map_poly to_r (zprimitive p * zprimitive q) == 0.
  by rewrite rmorphM mulf_neq0 ?nz_prim_r.
rewrite [_ * _]zpolyEprim [zcontents _]intEsign mulrC -scalerA map_polyZ /=.
by rewrite scale_poly_eq0 -val_eqE /= val_Fp_nat ?(eqnP r_dv_d).
Qed.


Lemma zprimitiveM p q : zprimitive (p * q) = zprimitive p * zprimitive q.
Proof.
have [pq_0|] := eqVneq (p * q) 0.
  rewrite pq_0; move/eqP: pq_0; rewrite mulf_eq0.
  by case/pred2P=> ->; rewrite !zprimitive0 (mul0r, mulr0).
rewrite -zcontents_eq0 -polyC_eq0 => /mulfI; apply; rewrite !mul_polyC.
by rewrite -zpolyEprim zcontentsM -scalerA scalerAr scalerAl -!zpolyEprim.
Qed.

Lemma dvdpP_int p q : p %| q -> {r | q = zprimitive p * r}.
Proof.
case/Pdiv.Idomain.dvdpP/sig2_eqW=> [[c r] /= nz_c Dpr].
exists (zcontents q *: zprimitive r); rewrite -scalerAr.
by rewrite -zprimitiveM mulrC -Dpr zprimitiveZ // -zpolyEprim.
Qed.

Local Notation pZtoQ := (map_poly (intr : int -> rat)).

Lemma size_rat_int_poly p : size (pZtoQ p) = size p.
Proof. by apply: size_map_inj_poly; first apply: intr_inj. Qed.

Lemma rat_poly_scale (p : {poly rat}) :
  {q : {poly int} & {a | a != 0 & p = a%:~R^-1 *: pZtoQ q}}.
Proof.
pose a := \prod_(i < size p) denq p`_i.
have nz_a: a != 0 by apply/prodf_neq0=> i _; apply: denq_neq0.
exists (map_poly numq (a%:~R *: p)), a => //.
apply: canRL (scalerK _) _; rewrite ?intr_eq0 //.
apply/polyP=> i; rewrite !(coefZ, coef_map_id0) // numqK // Qint_def mulrC.
have [ltip | /(nth_default 0)->] := ltnP i (size p); last by rewrite mul0r.
by rewrite [a](bigD1 (Ordinal ltip)) // rmorphM mulrA -numqE -rmorphM denq_int.
Qed.

Lemma dvdp_rat_int p q : (pZtoQ p %| pZtoQ q) = (p %| q).
Proof.
apply/dvdpP/Pdiv.Idomain.dvdpP=> [[/= r1 Dq] | [[/= a r] nz_a Dq]]; last first.
  exists (a%:~R^-1 *: pZtoQ r); rewrite -scalerAl -rmorphM -Dq /=.
  by rewrite -{2}[a]intz scaler_int rmorphMz -scaler_int scalerK ?intr_eq0.
have [r [a nz_a Dr1]] := rat_poly_scale r1; exists (a, r) => //=.
apply: (map_inj_poly _ _ : injective pZtoQ) => //; first exact: intr_inj.
rewrite -[a]intz scaler_int rmorphMz -scaler_int /= Dq Dr1.
by rewrite -scalerAl -rmorphM scalerKV ?intr_eq0.
Qed.

Lemma dvdpP_rat_int p q :
    p %| pZtoQ q ->
  {p1 : {poly int} & {a | a != 0 & p = a *: pZtoQ p1} & {r | q = p1 * r}}.
Proof.
have{p} [p [a nz_a ->]] := rat_poly_scale p.
rewrite dvdpZl ?invr_eq0 ?intr_eq0 // dvdp_rat_int => dv_p_q.
exists (zprimitive p); last exact: dvdpP_int.
have [-> | nz_p] := eqVneq p 0.
  by exists 1; rewrite ?oner_eq0 // zprimitive0 map_poly0 !scaler0.
exists ((zcontents p)%:~R / a%:~R).
  by rewrite mulf_neq0 ?invr_eq0 ?intr_eq0 ?zcontents_eq0.
by rewrite mulrC -scalerA -map_polyZ -zpolyEprim.
Qed.

End ZpolyScale.

(* Integral spans. *)

Lemma int_Smith_normal_form m n (M : 'M[int]_(m, n)) :
  {L : 'M[int]_m & L \in unitmx &
  {R : 'M[int]_n & R \in unitmx &
  {d : seq int | sorted dvdz d &
   M = L *m (\matrix_(i, j) (d`_i *+ (i == j :> nat))) *m R}}}.
Proof.
move: {2}_.+1 (ltnSn (m + n)) => mn.
elim: mn => // mn IHmn in m n M *; rewrite ltnS => le_mn.
have [[i j] nzMij | no_ij] := pickP (fun k => M k.1 k.2 != 0); last first.
  do 2![exists 1%:M; first exact: unitmx1]; exists nil => //=.
  apply/matrixP=> i j; apply/eqP; rewrite mulmx1 mul1mx mxE nth_nil mul0rn.
  exact: negbFE (no_ij (i, j)).
do [case: m i => [[]//|m] i; case: n j => [[]//|n] j /=] in M nzMij le_mn *.
wlog Dj: j M nzMij / j = 0; last rewrite {j}Dj in nzMij.
  case/(_ 0 (xcol j 0 M)); rewrite ?mxE ?tpermR // => L uL [R uR [d dvD dM]].
  exists L => //; exists (xcol j 0 R); last exists d => //=.
     by rewrite xcolE unitmx_mul uR unitmx_perm.
  by rewrite xcolE !mulmxA -dM xcolE -mulmxA -perm_mxM tperm2 perm_mx1 mulmx1.
move Da: (M i 0) nzMij => a nz_a.
have [A leA] := ubnP `|a|; elim: A => // A IHa in a leA m n M i Da nz_a le_mn *.
wlog [j a'Mij]: m n M i Da le_mn / {j | ~~ (a %| M i j)%Z}; last first.
  have nz_j: j != 0 by apply: contraNneq a'Mij => ->; rewrite Da.
  case: n => [[[]//]|n] in j le_mn nz_j M a'Mij Da *.
  wlog{nz_j} Dj: j M a'Mij Da / j = 1; last rewrite {j}Dj in a'Mij.
    case/(_ 1 (xcol j 1 M)); rewrite ?mxE ?tpermR ?tpermD //.
    move=> L uL [R uR [d dvD dM]]; exists L => //.
    exists (xcol j 1 R); first by rewrite xcolE unitmx_mul uR unitmx_perm.
    exists d; rewrite //= xcolE !mulmxA -dM xcolE -mulmxA -perm_mxM tperm2.
    by rewrite perm_mx1 mulmx1.
  have [u [v]] := Bezoutz a (M i 1); set b := gcdz _ _ => Db.
  have{leA} ltA: (`|b| < A)%N.
    rewrite -ltnS (leq_trans _ leA) // ltnS ltn_neqAle andbC.
    rewrite dvdn_leq ?absz_gt0 ? dvdn_gcdl //=.
    by rewrite (contraNneq _ a'Mij) ?dvdzE // => <-; apply: dvdn_gcdr.
  pose t2 := [fun j : 'I_2 => [tuple _; _]`_j : int]; pose a1 := M i 1.
  pose Uul := \matrix_(k, j) t2 (t2 u (- (a1 %/ b)%Z) j) (t2 v (a %/ b)%Z j) k.
  pose U : 'M_(2 + n) := block_mx Uul 0 0 1%:M; pose M1 := M *m U.
  have{nz_a} nz_b: b != 0 by rewrite gcdz_eq0 (negPf nz_a).
  have uU: U \in unitmx.
    rewrite unitmxE det_ublock det1 (expand_det_col _ 0) big_ord_recl big_ord1.
    do 2!rewrite /cofactor [row' _ _]mx11_scalar !mxE det_scalar1 /=.
    rewrite mulr1 mul1r mulN1r opprK -[_ + _](mulzK _ nz_b) mulrDl.
    by rewrite -!mulrA !divzK ?dvdz_gcdl ?dvdz_gcdr // Db divzz nz_b unitr1.
  have{} Db: M1 i 0 = b.
    rewrite /M1 -(lshift0 n 1) [U]block_mxEh mul_mx_row row_mxEl.
    rewrite -[M](@hsubmxK _ _ 2) (@mul_row_col _ _ 2) mulmx0 addr0 !mxE /=.
    rewrite big_ord_recl big_ord1 !mxE /= [lshift _ _]((_ =P 0) _) // Da.
    by rewrite [lshift _ _]((_ =P 1) _) // mulrC -(mulrC v).
  have [L uL [R uR [d dvD dM1]]] := IHa b ltA _ _ M1 i Db nz_b le_mn.
  exists L => //; exists (R *m invmx U); last exists d => //.
    by rewrite unitmx_mul uR unitmx_inv.
  by rewrite mulmxA -dM1 mulmxK.
move=> {A leA}IHa; wlog Di: i M Da / i = 0; last rewrite {i}Di in Da.
  case/(_ 0 (xrow i 0 M)); rewrite ?mxE ?tpermR // => L uL [R uR [d dvD dM]].
  exists (xrow i 0 L); first by rewrite xrowE unitmx_mul unitmx_perm.
  exists R => //; exists d; rewrite //= xrowE -!mulmxA (mulmxA L) -dM xrowE.
  by rewrite mulmxA -perm_mxM tperm2 perm_mx1 mul1mx.
without loss /forallP a_dvM0: / [forall j, a %| M 0%R j]%Z.
  case: (altP forallP) => [_ IH|/forallPn/sigW/IHa IH _]; exact: IH.
without loss{Da a_dvM0} Da: M / forall j, M 0 j = a.
  pose Uur := col' 0 (\row_j (1 - (M 0%R j %/ a)%Z)).
  pose U : 'M_(1 + n) := block_mx 1 Uur 0 1%:M; pose M1 := M *m U.
  have uU: U \in unitmx by rewrite unitmxE det_ublock !det1 mulr1.
  case/(_ (M *m U)) => [j | L uL [R uR [d dvD dM]]].
    rewrite -(lshift0 m 0) -[M](@submxK _ 1 _ 1) (@mulmx_block _ 1 m 1).
    rewrite (@col_mxEu _ 1) !mulmx1 mulmx0 addr0 [ulsubmx _]mx11_scalar.
    rewrite mul_scalar_mx !mxE !lshift0 Da.
    case: splitP => [j0 _ | j1 Dj]; rewrite ?ord1 !mxE // lshift0 rshift1.
    by rewrite mulrBr mulr1 mulrC divzK ?subrK.
  exists L => //; exists (R * U^-1); first by rewrite unitmx_mul uR unitmx_inv.
  by exists d; rewrite //= mulmxA -dM mulmxK.
without loss{IHa} /forallP/(_ (_, _))/= a_dvM: / [forall k, a %| M k.1 k.2]%Z.
  case: (altP forallP) => [_|/forallPn/sigW [[i j] /= a'Mij] _]; first exact.
  have [|||L uL [R uR [d dvD dM]]] := IHa _ _ M^T j; rewrite ?mxE 1?addnC //.
    by exists i; rewrite mxE.
  exists R^T; last exists L^T; rewrite ?unitmx_tr //; exists d => //.
  rewrite -[M]trmxK dM !trmx_mul mulmxA; congr (_ *m _ *m _).
  by apply/matrixP=> i1 j1 /[!mxE]; case: eqVneq => // ->.
without loss{nz_a a_dvM} a1: M a Da / a = 1.
  pose M1 := map_mx (divz^~ a) M; case/(_ M1 1)=> // [k|L uL [R uR [d dvD dM]]].
    by rewrite !mxE Da divzz nz_a.
  exists L => //; exists R => //; exists [seq a * x | x <- d].
    case: d dvD {dM} => //= x d; elim: d x => //= y d IHd x /andP[dv_xy /IHd].
    by rewrite [dvdz _ _]dvdz_mul2l ?[_ \in _]dv_xy.
  have ->: M = a *: M1 by apply/matrixP=> i j; rewrite !mxE mulrC divzK ?a_dvM.
  rewrite dM scalemxAl scalemxAr; congr (_ *m _ *m _).
  apply/matrixP=> i j; rewrite !mxE mulrnAr; congr (_ *+ _).
  have [lt_i_d | le_d_i] := ltnP i (size d); first by rewrite (nth_map 0).
  by rewrite !nth_default ?size_map ?mulr0.
rewrite {a}a1 -[m.+1]/(1 + m)%N -[n.+1]/(1 + n)%N in M Da *.
pose Mu := ursubmx M; pose Ml := dlsubmx M.
have{} Da: ulsubmx M = 1 by rewrite [_ M]mx11_scalar !mxE !lshift0 Da.
pose M1 := - (Ml *m Mu) + drsubmx M.
have [|L uL [R uR [d dvD dM1]]] := IHmn m n M1; first by rewrite -addnS ltnW.
exists (block_mx 1 0 Ml L).
  by rewrite unitmxE det_lblock det_scalar1 mul1r.
exists (block_mx 1 Mu 0 R).
  by rewrite unitmxE det_ublock det_scalar1 mul1r.
exists (1 :: d); set D1 := \matrix_(i, j) _ in dM1.
  by rewrite /= path_min_sorted //; apply/allP => g _; apply: dvd1n.
rewrite [D in _ *m D *m _](_ : _ = block_mx 1 0 0 D1); last first.
  by apply/matrixP=> i j; do 3?[rewrite ?mxE ?ord1 //=; case: splitP => ? ->].
rewrite !mulmx_block !(mul0mx, mulmx0, addr0) !mulmx1 add0r mul1mx -Da -dM1.
by rewrite addNKr submxK.
Qed.

Definition inIntSpan (V : zmodType) m (s : m.-tuple V) v :=
  exists a : int ^ m, v = \sum_(i < m) s`_i *~ a i.

Lemma solve_Qint_span (vT : vectType rat) m (s : m.-tuple vT) v :
  {b : int ^ m &
  {p : seq (int ^ m) &
  forall a : int ^ m,
  v = \sum_(i < m) s`_i *~ a i <->
  exists c : seq int, a = b + \sum_(i < size p) p`_i *~ c`_i}} +
  (~ inIntSpan s v).
Proof.
have s_s (i : 'I_m): s`_i \in <<s>>%VS by rewrite memv_span ?memt_nth.
have s_Zs a: \sum_(i < m) s`_i *~ a i \in <<s>>%VS.
  by rewrite memv_suml // => i _; rewrite -scaler_int memvZ.
case s_v: (v \in <<s>>%VS); last by right=> [[a Dv]]; rewrite Dv s_Zs in s_v.
pose S := \matrix_(i < m, j < _) coord (vbasis <<s>>) j s`_i.
pose r := \rank S; pose k := (m - r)%N; pose Em := erefl m; pose Ek := erefl k.
have Dm: (m = k + r)%N by rewrite subnK ?rank_leq_row.
have [K kerK]: {K : 'M_(k, m) | map_mx intr K == kermx S}%MS.
  pose B := row_base (kermx S); pose d := \prod_ij denq (B ij.1 ij.2).
  exists (castmx (mxrank_ker S, Em) (map_mx numq (intr d *: B))).
  rewrite /k; case: _ / (mxrank_ker S); set B1 := map_mx _ _.
  have ->: B1 = (intr d *: B).
    apply/matrixP=> i j; rewrite 3!mxE mulrC [d](bigD1 (i, j)) // rmorphM mulrA.
    by rewrite -numqE -rmorphM numq_int.
  suffices nz_d: d%:Q != 0 by rewrite !eqmx_scale // !eq_row_base andbb.
  by rewrite intr_eq0; apply/prodf_neq0 => i _; apply: denq_neq0.
have [L _ [G uG [D _ defK]]] := int_Smith_normal_form K.
pose Gud := castmx (Dm, Em) G; pose G'lr := castmx (Em, Dm) (invmx G).
have{K L D defK kerK} [kerGu kerS_sub_Gu]: map_mx intr (usubmx Gud) *m S = 0 /\
    (kermx S <= map_mx intr (usubmx Gud))%MS.
  pose Kl : 'M[rat]_k:= map_mx intr (lsubmx (castmx (Ek, Dm) (K *m invmx G))).
  have{} defK: map_mx intr K = row_mx Kl 0 *m map_mx intr Gud.
    rewrite -[K](mulmxKV uG) -{2}[G](castmxK Dm Em) -/Gud.
    rewrite -[K *m _](castmxK Ek Dm) map_mxM map_castmx.
    rewrite -(hsubmxK (castmx _ _)) map_row_mx -/Kl map_castmx /Em.
    set Kr := map_mx _ _; case: _ / (esym Dm) (map_mx _ _) => /= GudQ.
    congr (row_mx _ _ *m _); apply/matrixP=> i j; rewrite !mxE defK mulmxK //=.
    rewrite castmxE mxE big1 //= => j1 _; rewrite mxE /= eqn_leq andbC.
    by rewrite leqNgt (leq_trans (valP j1)) ?mulr0 ?leq_addr.
  split; last first.
    rewrite -(eqmxP kerK); apply/submxP; exists Kl.
    by rewrite defK -{1}[Gud]vsubmxK map_col_mx mul_row_col mul0mx addr0.
  have /row_full_inj: row_full Kl; last apply.
    rewrite /row_full eqn_leq rank_leq_row /= -{1}[k](mxrank_ker S).
    rewrite -(eqmxP kerK) defK map_castmx mxrankMfree; last first.
      case: _ / (Dm); apply/row_freeP; exists (map_mx intr (invmx G)).
      by rewrite -map_mxM mulmxV ?map_mx1.
    by rewrite -mxrank_tr tr_row_mx trmx0 -addsmxE addsmx0 mxrank_tr.
  rewrite mulmx0 mulmxA (sub_kermxP _) // -(eqmxP kerK) defK.
  by rewrite -{2}[Gud]vsubmxK map_col_mx mul_row_col mul0mx addr0.
pose T := map_mx intr (dsubmx Gud) *m S.
have defS: map_mx intr (rsubmx G'lr) *m T = S.
  have: G'lr *m Gud = 1%:M by rewrite /G'lr /Gud; case: _ / (Dm); apply: mulVmx.
  rewrite -{1}[G'lr]hsubmxK -[Gud]vsubmxK mulmxA mul_row_col -map_mxM.
  move/(canRL (addKr _))->; rewrite -mulNmx raddfD /= map_mx1 map_mxM /=.
  by rewrite mulmxDl -mulmxA kerGu mulmx0 add0r mul1mx.
pose vv := \row_j coord (vbasis <<s>>) j v.
have uS: row_full S.
  apply/row_fullP; exists (\matrix_(i, j) coord s j (vbasis <<s>>)`_i).
  apply/matrixP=> j1 j2; rewrite !mxE.
  rewrite -(coord_free _ _ (basis_free (vbasisP _))).
  rewrite -!tnth_nth (coord_span (vbasis_mem (mem_tnth j1 _))) linear_sum.
  by apply: eq_bigr => i _; rewrite !mxE (tnth_nth 0) !linearZ.
have eqST: (S :=: T)%MS by apply/eqmxP; rewrite -{1}defS !submxMl.
case Zv: (map_mx denq (vv *m pinvmx T) == const_mx 1).
  pose b := map_mx numq (vv *m pinvmx T) *m dsubmx Gud.
  left; exists [ffun j => b 0 j], [seq [ffun j => (usubmx Gud) i j] | i : 'I_k].
  rewrite size_image card_ord => a; rewrite -[a](addNKr [ffun j => b 0 j]).
  move: (_ + a) => h; under eq_bigr => i _ do rewrite !ffunE mulrzDr_tmp.
  rewrite big_split /=.
  have <-: v = \sum_(i < m) s`_i *~ b 0 i.
    transitivity (\sum_j (map_mx intr b *m S) 0 j *: (vbasis <<s>>)`_j).
      rewrite {1}(coord_vbasis s_v); apply: eq_bigr => j _; congr (_ *: _).
      have ->: map_mx intr b = vv *m pinvmx T *m map_mx intr (dsubmx Gud).
        rewrite map_mxM /=; congr (_ *m _); apply/rowP=> i; rewrite 2!mxE numqE.
        by have /eqP/rowP/(_ i)/[!mxE]-> := Zv; rewrite mulr1.
      by rewrite -(mulmxA _ _ S) mulmxKpV ?mxE // -eqST submx_full.
    rewrite (coord_vbasis (s_Zs _)); apply: eq_bigr => j _; congr (_ *: _).
    rewrite linear_sum mxE; apply: eq_bigr => i _.
    by rewrite -scaler_int linearZ [b]lock !mxE.
  split.
    rewrite -[LHS]addr0 => /addrI hP; pose c := \row_i h i *m lsubmx G'lr.
    exists [seq c 0 i | i : 'I_k]; congr (_ + _).
    have/sub_kermxP: map_mx intr (\row_i h i) *m S = 0.
      transitivity (\row_j coord (vbasis <<s>>) j (\sum_(i < m) s`_i *~ h i)).
        apply/rowP=> j; rewrite !mxE linear_sum; apply: eq_bigr => i _.
        by rewrite !mxE -scaler_int linearZ.
      by apply/rowP=> j; rewrite !mxE -hP linear0.
    case/submx_trans/(_ kerS_sub_Gu)/submxP=> c' /[dup].
    move/(congr1 (mulmx^~ (map_mx intr (lsubmx G'lr)))).
    rewrite -mulmxA -!map_mxM [in RHS]mulmx_lsub mul_usub_mx -/c /=.
    have ->: Gud *m G'lr = 1%:M
      by rewrite /G'lr /Gud; case: _ / (Dm); apply: mulmxV.
    rewrite scalar_mx_block -/(ulsubmx _) block_mxKul map_scalar_mx mulmx1.
    move=> {c'}<-; rewrite -map_mxM /= => defh; apply/ffunP=> j.
    move/rowP/(_ j): defh; rewrite sum_ffunE !mxE; move/intr_inj->.
    apply: eq_bigr => i _; rewrite ffunMzE mulrzz mulrC.
    rewrite (nth_map i) ?size_enum_ord // nth_ord_enum ffunE.
    by rewrite (nth_map i) ?size_enum_ord // nth_ord_enum.
  case=> c {h}/addrI->; rewrite -[LHS]addr0; congr (_ + _).
  pose h := \row_(j < k) c`_j *m usubmx Gud.
  transitivity (\sum_j (map_mx intr h *m S) 0 j *: (vbasis <<s>>)`_j).
    by rewrite map_mxM -mulmxA kerGu mulmx0 big1 // => j _; rewrite mxE scale0r.
  rewrite (coord_vbasis (s_Zs _)); apply: eq_bigr => i _; congr (_ *: _).
  rewrite linear_sum mxE; apply: eq_bigr => j _.
  rewrite -scaler_int linearZ !mxE sum_ffunE; congr (_%:~R * _).
  apply: {i} eq_bigr => i _; rewrite mxE ffunMzE mulrzz mulrC.
  by rewrite (nth_map i) ?size_enum_ord // ffunE nth_ord_enum.
right=> [[a Dv]]; case/eqP: Zv; apply/rowP.
have ->: vv = map_mx intr (\row_i a i) *m S.
  apply/rowP=> j; rewrite !mxE Dv linear_sum.
  by apply: eq_bigr => i _; rewrite -scaler_int linearZ !mxE.
rewrite -defS -2!mulmxA; have ->: T *m pinvmx T = 1%:M.
  have uT: row_free T by rewrite /row_free -eqST.
  by apply: (row_free_inj uT); rewrite mul1mx mulmxKpV.
by move=> i; rewrite mulmx1 -map_mxM 2!mxE denq_int mxE.
Qed.

Lemma dec_Qint_span (vT : vectType rat) m (s : m.-tuple vT) v :
  decidable (inIntSpan s v).
Proof.
have [[b [p aP]]|] := solve_Qint_span s v; last by right.
left; exists b; apply/(aP b); exists [::]; rewrite big1 ?addr0 // => i _.
by rewrite nth_nil mulr0z.
Qed.

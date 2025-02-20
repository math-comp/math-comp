(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
(* -------------------------------------------------------------------- *)
(* Copyright (c) - 2015--2016 - IMDEA Software Institute                *)
(* Copyright (c) - 2015--2018 - Inria                                   *)
(* Copyright (c) - 2016--2018 - Polytechnique                           *)
(* -------------------------------------------------------------------- *)

(* TODO: merge this with table.v in real-closed
   (c.f. https://github.com/math-comp/real-closed/pull/29 ) and
   incorporate it into mathcomp proper where it could then be used for
   bounds of intervals*)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg.
From mathcomp Require Import orderedzmod zmodext numdomain numfield itv.

(**md**************************************************************************)
(* # Extended real numbers $\overline{R}$                                     *)
(*                                                                            *)
(* Given a type R for numbers, \bar R is the type R extended with symbols     *)
(* -oo and +oo (notation scope: %E), suitable to represent extended real      *)
(* numbers. When R is a numDomainType, \bar R is equipped with a canonical    *)
(* porderType and operations for addition/opposite. When R is a               *)
(* realDomainType, \bar R is equipped with a Canonical orderType.             *)
(*                                                                            *)
(* Naming convention: in definition/lemma identifiers, "e" stands for an      *)
(* extended number and "y" and "Ny" for +oo ad -oo respectively.              *)
(* ```                                                                        *)
(*                     *%E == multiplication for extended reals               *)
(*                   sqrte == square root for extended reals                  *)
(*                `| x |%E == the absolute value of x                         *)
(*                  x ^+ n == iterated multiplication                         *)
(*                  x *+ n == iterated addition                               *)
(*             (x *+ n)%dE == dual iterated addition for                      *)
(*                            extended reals (-oo + +oo = +oo instead of -oo) *)
(*                            Import DualAddTheory for related lemmas         *)
(*                  x *? y == the multiplication of the extended real numbers *)
(*                            x and y is not of the form 0 * +oo or 0 * -oo   *)
(*  (\prod_(i in A) f i)%E == bigop-like notation in scope %E                 *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Order.Theory.
Import orderedzmod.Num.Theory numdomain.Num.Theory numfield.Num.Theory.
Local Open Scope ring_scope.
Local Open Scope order_scope.
Local Open Scope ereal_scope.

Section ERealOrder_numDomainType.
Context {R : numDomainType}.
Implicit Types (x y : \bar R) (r : R).

Lemma lee01 : 0 <= 1 :> \bar R. Proof. by rewrite lee_fin. Qed.

Lemma lte01 : 0 < 1 :> \bar R. Proof. by rewrite lte_fin. Qed.

Lemma fine1 : fine 1 = 1%R :> R. Proof. by []. Qed.

End ERealOrder_numDomainType.

#[global] Hint Resolve lee01 lte01 : core.

Section ERealOrder_realDomainType.
Context {R : realDomainType}.
Implicit Types (x y : \bar R) (r : R).

Lemma ltry r : r%:E < +oo. Proof. exact: num_real. Qed.

Lemma ltey x : (x < +oo) = (x != +oo).
Proof. by case: x => // r; rewrite ltry. Qed.

Lemma ltNyr r : -oo < r%:E. Proof. exact: num_real. Qed.

Lemma ltNye x : (-oo < x) = (x != -oo).
Proof. by case: x => // r; rewrite ltNyr. Qed.

Lemma leey x : x <= +oo. Proof. by case: x => //= r; exact: num_real. Qed.

Lemma leNye x : -oo <= x. Proof. by case: x => //= r; exact: num_real. Qed.

Definition lteey := (ltey, leey).

Definition lteNye := (ltNye, leNye).

Lemma le_er_map (f : R -> R) : {homo f : x y / (x <= y)%R} ->
  {homo er_map f : x y / x <= y}.
Proof.
move=> ndf.
by move=> [r| |] [l| |]//=; rewrite ?leey ?leNye// !lee_fin; exact: ndf.
Qed.

Lemma le_total_ereal : total (Order.le : rel (\bar R)).
Proof.
by move=> [?||][?||]//=; rewrite (ltEereal, leEereal)/= ?num_real ?le_total.
Qed.

HB.instance Definition _ := Order.POrder_isTotal.Build ereal_display (\bar R)
  le_total_ereal.

HB.instance Definition _ := Order.hasBottom.Build ereal_display (\bar R) leNye.
HB.instance Definition _ := Order.hasTop.Build ereal_display (\bar R) leey.

End ERealOrder_realDomainType.

Section ERealZmodule.
Context {R : zmodType}.
Implicit Types x y z : \bar R.

Definition oppe x :=
  match x with
  | r%:E  => (- r)%:E
  | -oo => +oo
  | +oo => -oo
  end.

End ERealZmodule.

Section ERealArith.
Context {R : numDomainType}.
Implicit Types x y z : \bar R.

Definition mule x y :=
  match x, y with
  | x%:E , y%:E => (x * y)%:E
  | -oo, y | y, -oo => if y == 0 then 0 else if 0 < y then -oo else +oo
  | +oo, y | y, +oo => if y == 0 then 0 else if 0 < y then +oo else -oo
  end.
Arguments mule : simpl never.

Definition abse x : \bar R := if x is r%:E then `|r|%:E else +oo.

Definition expe x n := iterop n mule x 1.

End ERealArith.
Arguments mule : simpl never.

Notation "+%dE"  := (@GRing.add (\bar^d _)).
Notation "+%E"   := (@GRing.add (\bar _)).
Notation "-%E"   := oppe.
Notation "x + y" := (GRing.add (x%dE : \bar^d _) y%dE) : ereal_dual_scope.
Notation "x + y" := (GRing.add x%E y%E) : ereal_scope.
Notation "x - y" := ((x%dE : \bar^d _) + oppe y%dE) : ereal_dual_scope.
Notation "x - y" := (x%E + (oppe y%E)) : ereal_scope.
Notation "- x"   := (oppe x%dE : \bar^d _) : ereal_dual_scope.
Notation "- x"   := (oppe x%E) : ereal_scope.
Notation "*%E"   := mule.
Notation "x * y" := (mule x%dE y%dE : \bar^d _) : ereal_dual_scope.
Notation "x * y" := (mule x%E y%E) : ereal_scope.
Notation "`| x |" := (abse x%dE : \bar^d _) : ereal_dual_scope.
Notation "`| x |" := (abse x%E) : ereal_scope.
Arguments abse {R}.
Notation "x ^+ n" := (expe x%dE n : \bar^d _) : ereal_dual_scope.
Notation "x ^+ n" := (expe x%E n) : ereal_scope.
Notation "x *+ n" := (ednatmul x%dE n) : ereal_dual_scope.
Notation "x *+ n" := (enatmul x%E n) : ereal_scope.

Notation "\- f" := (fun x => - f x)%dE : ereal_dual_scope.
Notation "\- f" := (fun x => - f x)%E : ereal_scope.
Notation "f \+ g" := (fun x => f x + g x)%dE : ereal_dual_scope.
Notation "f \+ g" := (fun x => f x + g x)%E : ereal_scope.
Notation "f \* g" := (fun x => f x * g x)%dE : ereal_dual_scope.
Notation "f \* g" := (fun x => f x * g x)%E : ereal_scope.
Notation "f \- g" := (fun x => f x - g x)%dE : ereal_dual_scope.
Notation "f \- g" := (fun x => f x - g x)%E : ereal_scope.

Notation "\sum_ ( i <- r | P ) F" :=
  (\big[+%dE/0%dE]_(i <- r | P%B) F%dE) : ereal_dual_scope.
Notation "\sum_ ( i <- r | P ) F" :=
  (\big[+%E/0%E]_(i <- r | P%B) F%E) : ereal_scope.
Notation "\sum_ ( i <- r ) F" :=
  (\big[+%dE/0%dE]_(i <- r) F%dE) : ereal_dual_scope.
Notation "\sum_ ( i <- r ) F" :=
  (\big[+%E/0%E]_(i <- r) F%E) : ereal_scope.
Notation "\sum_ ( m <= i < n | P ) F" :=
  (\big[+%dE/0%dE]_(m <= i < n | P%B) F%dE) : ereal_dual_scope.
Notation "\sum_ ( m <= i < n | P ) F" :=
  (\big[+%E/0%E]_(m <= i < n | P%B) F%E) : ereal_scope.
Notation "\sum_ ( m <= i < n ) F" :=
  (\big[+%dE/0%dE]_(m <= i < n) F%dE) : ereal_dual_scope.
Notation "\sum_ ( m <= i < n ) F" :=
  (\big[+%E/0%E]_(m <= i < n) F%E) : ereal_scope.
Notation "\sum_ ( i | P ) F" :=
  (\big[+%dE/0%dE]_(i | P%B) F%dE) : ereal_dual_scope.
Notation "\sum_ ( i | P ) F" :=
  (\big[+%E/0%E]_(i | P%B) F%E) : ereal_scope.
Notation "\sum_ i F" :=
  (\big[+%dE/0%dE]_i F%dE) : ereal_dual_scope.
Notation "\sum_ i F" :=
  (\big[+%E/0%E]_i F%E) : ereal_scope.
Notation "\sum_ ( i : t | P ) F" :=
  (\big[+%dE/0%dE]_(i : t | P%B) F%dE) (only parsing) : ereal_dual_scope.
Notation "\sum_ ( i : t | P ) F" :=
  (\big[+%E/0%E]_(i : t | P%B) F%E) (only parsing) : ereal_scope.
Notation "\sum_ ( i : t ) F" :=
  (\big[+%dE/0%dE]_(i : t) F%dE) (only parsing) : ereal_dual_scope.
Notation "\sum_ ( i : t ) F" :=
  (\big[+%E/0%E]_(i : t) F%E) (only parsing) : ereal_scope.
Notation "\sum_ ( i < n | P ) F" :=
  (\big[+%dE/0%dE]_(i < n | P%B) F%dE) : ereal_dual_scope.
Notation "\sum_ ( i < n | P ) F" :=
  (\big[+%E/0%E]_(i < n | P%B) F%E) : ereal_scope.
Notation "\sum_ ( i < n ) F" :=
  (\big[+%dE/0%dE]_(i < n) F%dE) : ereal_dual_scope.
Notation "\sum_ ( i < n ) F" :=
  (\big[+%E/0%E]_(i < n) F%E) : ereal_scope.
Notation "\sum_ ( i 'in' A | P ) F" :=
  (\big[+%dE/0%dE]_(i in A | P%B) F%dE) : ereal_dual_scope.
Notation "\sum_ ( i 'in' A | P ) F" :=
  (\big[+%E/0%E]_(i in A | P%B) F%E) : ereal_scope.
Notation "\sum_ ( i 'in' A ) F" :=
  (\big[+%dE/0%dE]_(i in A) F%dE) : ereal_dual_scope.
Notation "\sum_ ( i 'in' A ) F" :=
  (\big[+%E/0%E]_(i in A) F%E) : ereal_scope.

Notation "\prod_ ( i <- r | P ) F" :=
  (\big[*%E/1%:E]_(i <- r | P%B) F%E) : ereal_scope.
Notation "\prod_ ( i <- r ) F" :=
  (\big[*%E/1%:E]_(i <- r) F%E) : ereal_scope.
Notation "\prod_ ( m <= i < n | P ) F" :=
  (\big[*%E/1%:E]_(m <= i < n | P%B) F%E) : ereal_scope.
Notation "\prod_ ( m <= i < n ) F" :=
  (\big[*%E/1%:E]_(m <= i < n) F%E) : ereal_scope.
Notation "\prod_ ( i | P ) F" :=
  (\big[*%E/1%:E]_(i | P%B) F%E) : ereal_scope.
Notation "\prod_ i F" :=
  (\big[*%E/1%:E]_i F%E) : ereal_scope.
Notation "\prod_ ( i : t | P ) F" :=
  (\big[*%E/1%:E]_(i : t | P%B) F%E) (only parsing) : ereal_scope.
Notation "\prod_ ( i : t ) F" :=
  (\big[*%E/1%:E]_(i : t) F%E) (only parsing) : ereal_scope.
Notation "\prod_ ( i < n | P ) F" :=
  (\big[*%E/1%:E]_(i < n | P%B) F%E) : ereal_scope.
Notation "\prod_ ( i < n ) F" :=
  (\big[*%E/1%:E]_(i < n) F%E) : ereal_scope.
Notation "\prod_ ( i 'in' A | P ) F" :=
  (\big[*%E/1%:E]_(i in A | P%B) F%E) : ereal_scope.
Notation "\prod_ ( i 'in' A ) F" :=
  (\big[*%E/1%:E]_(i in A) F%E) : ereal_scope.

Section ERealOrderTheory.
Context {R : numDomainType}.
Implicit Types x y z : \bar R.

Local Tactic Notation "elift" constr(lm) ":" ident(x) :=
  by case: x => [||?]; first by rewrite ?eqe; apply: lm.

Local Tactic Notation "elift" constr(lm) ":" ident(x) ident(y) :=
  by case: x y => [?||] [?||]; first by rewrite ?eqe; apply: lm.

Local Tactic Notation "elift" constr(lm) ":" ident(x) ident(y) ident(z) :=
  by case: x y z => [?||] [?||] [?||]; first by rewrite ?eqe; apply: lm.

Lemma lee0N1 : 0 <= (-1)%:E :> \bar R = false.
Proof. by rewrite lee_fin ler0N1. Qed.

Lemma lte0N1 : 0 < (-1)%:E :> \bar R = false.
Proof. by rewrite lte_fin ltr0N1. Qed.

Lemma lteN10 : - 1%E < 0 :> \bar R.
Proof. by rewrite lte_fin ltrN10. Qed.

Lemma leeN10 : - 1%E <= 0 :> \bar R.
Proof. by rewrite lee_fin lerN10. Qed.

Lemma lte0n n : (0 < n%:R%:E :> \bar R) = (0 < n)%N.
Proof. by rewrite lte_fin ltr0n. Qed.

Lemma lee0n n : (0 <= n%:R%:E :> \bar R) = (0 <= n)%N.
Proof. by rewrite lee_fin ler0n. Qed.

Lemma lte1n n : (1 < n%:R%:E :> \bar R) = (1 < n)%N.
Proof. by rewrite lte_fin ltr1n. Qed.

Lemma lee1n n : (1 <= n%:R%:E :> \bar R) = (1 <= n)%N.
Proof. by rewrite lee_fin ler1n. Qed.

Lemma fine_ge0 x : 0 <= x -> (0 <= fine x)%R.
Proof. by case: x. Qed.

Lemma fine_gt0 x : 0 < x < +oo -> (0 < fine x)%R.
Proof. by move: x => [x| |] //=; rewrite ?ltxx ?andbF// lte_fin => /andP[]. Qed.

Lemma fine_lt0 x : -oo < x < 0 -> (fine x < 0)%R.
Proof. by move: x => [x| |] //= /andP[_]; rewrite lte_fin. Qed.

Lemma fine_le0 x : x <= 0 -> (fine x <= 0)%R.
Proof. by case: x. Qed.

Lemma lee_tofin (r0 r1 : R) : (r0 <= r1)%R -> r0%:E <= r1%:E.
Proof. by []. Qed.

Lemma lte_tofin (r0 r1 : R) : (r0 < r1)%R -> r0%:E < r1%:E.
Proof. by []. Qed.

Lemma enatmul_pinfty n : +oo *+ n.+1 = +oo :> \bar R.
Proof. by elim: n => //= n ->. Qed.

Lemma enatmul_ninfty n : -oo *+ n.+1 = -oo :> \bar R.
Proof. by elim: n => //= n ->. Qed.

Lemma EFin_natmul (r : R) n : (r *+ n.+1)%:E = r%:E *+ n.+1.
Proof. by elim: n => //= n <-. Qed.

Lemma mule2n x : x *+ 2 = x + x. Proof. by []. Qed.

Lemma expe2 x : x ^+ 2 = x * x. Proof. by []. Qed.

Lemma leeN2 : {mono @oppe R : x y /~ x <= y}.
Proof.
move=> x y; case: x y => [?||] [?||] //; first by rewrite !lee_fin !lerN2.
  by rewrite /Order.le/= realN.
by rewrite /Order.le/= realN.
Qed.

Lemma lteN2 : {mono @oppe R : x y /~ x < y}.
Proof.
move=> x y; case: x y => [?||] [?||] //; first by rewrite !lte_fin !ltrN2.
  by rewrite /Order.lt/= realN.
by rewrite /Order.lt/= realN.
Qed.

End ERealOrderTheory.
#[global] Hint Resolve leeN10 lteN10 : core.

Section finNumPred.
Context {R : numDomainType}.
Implicit Type (x : \bar R).

Definition fin_num := [qualify a x : \bar R | (x != -oo) && (x != +oo)].
Fact fin_num_key : pred_key fin_num. Proof. by []. Qed.
(*Canonical fin_num_keyd := KeyedQualifier fin_num_key.*)

Lemma fin_numE x : (x \is a fin_num) = (x != -oo) && (x != +oo).
Proof. by []. Qed.

Lemma fin_numP x : reflect ((x != -oo) /\ (x != +oo)) (x \is a fin_num).
Proof. by apply/(iffP idP) => [/andP//|/andP]. Qed.

Lemma fin_numEn x : (x \isn't a fin_num) = (x == -oo) || (x == +oo).
Proof. by rewrite fin_numE negb_and ?negbK. Qed.

Lemma fin_numPn x : reflect (x = -oo \/ x = +oo) (x \isn't a fin_num).
Proof. by rewrite fin_numEn; apply: (iffP orP) => -[]/eqP; by [left|right]. Qed.

Lemma fin_real x : -oo < x < +oo -> x \is a fin_num.
Proof. by move=> /andP[oox xoo]; rewrite fin_numE gt_eqF ?lt_eqF. Qed.

Lemma fin_num_abs x : (x \is a fin_num) = (`| x | < +oo)%E.
Proof. by rewrite fin_numE; case: x => // r; rewrite real_ltry normr_real. Qed.

End finNumPred.

Section ERealArithTh_numDomainType.
Context {R : numDomainType}.
Implicit Types (x y z : \bar R) (r : R).

Lemma fine_le : {in fin_num &, {homo @fine R : x y / x <= y >-> (x <= y)%R}}.
Proof. by move=> [? [?| |]| |]. Qed.

Lemma fine_lt : {in fin_num &, {homo @fine R : x y / x < y >-> (x < y)%R}}.
Proof. by move=> [? [?| |]| |]. Qed.

Lemma fine_abse : {in fin_num, {morph @fine R : x / `|x| >-> `|x|%R}}.
Proof. by case. Qed.

Lemma abse_fin_num x : (`|x| \is a fin_num) = (x \is a fin_num).
Proof. by case: x. Qed.

Lemma fine_eq0 x : x \is a fin_num -> (fine x == 0%R) = (x == 0).
Proof. by move: x => [//| |] /=; rewrite fin_numE. Qed.

Lemma EFinN r : (- r)%:E = (- r%:E). Proof. by []. Qed.

Lemma fineN x : fine (- x) = (- fine x)%R.
Proof. by case: x => //=; rewrite oppr0. Qed.

Lemma EFinD r r' : (r + r')%:E = r%:E + r'%:E. Proof. by []. Qed.

Lemma EFin_semi_additive : @semi_additive _ (\bar R) EFin. Proof. by split. Qed.
HB.instance Definition _ := GRing.isSemiAdditive.Build R (\bar R) EFin
  EFin_semi_additive.

Lemma EFinB r r' : (r - r')%:E = r%:E - r'%:E. Proof. by []. Qed.

Lemma EFinM r r' : (r * r')%:E = r%:E * r'%:E. Proof. by []. Qed.

Lemma sumEFin I s P (F : I -> R) :
  \sum_(i <- s | P i) (F i)%:E = (\sum_(i <- s | P i) F i)%:E.
Proof. by rewrite (big_morph _ EFinD erefl). Qed.

Lemma EFin_min : {morph (@EFin R) : r s / Num.min r s >-> Order.min r s}.
Proof. by move=> x y; rewrite !minElt lte_fin -fun_if. Qed.

Lemma EFin_max : {morph (@EFin R) : r s / Num.max r s >-> Order.max r s}.
Proof. by move=> x y; rewrite !maxElt lte_fin -fun_if. Qed.

Definition adde_def x y :=
  ~~ ((x == +oo) && (y == -oo)) && ~~ ((x == -oo) && (y == +oo)).

Local Notation "x +? y" := (adde_def x y).

Lemma adde_defC x y : x +? y = y +? x.
Proof. by rewrite /adde_def andbC (andbC (x == -oo)) (andbC (x == +oo)). Qed.

Lemma fin_num_adde_defr x y : x \is a fin_num -> x +? y.
Proof. by move: x y => [x| |] [y | |]. Qed.

Lemma fin_num_adde_defl x y : y \is a fin_num -> x +? y.
Proof. by rewrite adde_defC; exact: fin_num_adde_defr. Qed.

Lemma adde_defN x y : x +? - y = - x +? y.
Proof. by move: x y => [x| |] [y| |]. Qed.

Lemma adde_defDr x y z : x +? y -> x +? z -> x +? (y + z).
Proof. by move: x y z => [x||] [y||] [z||]. Qed.

Lemma adde_defEninfty x : (x +? -oo) = (x != +oo).
Proof. by case: x. Qed.

Lemma ge0_adde_def : {in [pred x | x >= 0] &, forall x y, x +? y}.
Proof. by move=> [x| |] [y| |]. Qed.

Lemma addeC : commutative (S := \bar R) +%E. Proof. exact: addrC. Qed.

Lemma adde0 : right_id (0 : \bar R) +%E. Proof. exact: addr0. Qed.

Lemma add0e : left_id (0 : \bar R) +%E. Proof. exact: add0r. Qed.

Lemma addeA : associative (S := \bar R) +%E. Proof. exact: addrA. Qed.

Lemma adde_def_sum I h t (P : pred I) (f : I -> \bar R) :
    {in P, forall i : I, f h +? f i} ->
  f h +? \sum_(j <- t | P j) f j.
Proof.
move=> fhi; elim/big_rec : _; first by rewrite fin_num_adde_defl.
by move=> i x Pi fhx; rewrite adde_defDr// fhi.
Qed.

Lemma addeAC : @right_commutative (\bar R) _ +%E.
Proof. exact: Monoid.mulmAC. Qed.

Lemma addeCA : @left_commutative (\bar R) _ +%E.
Proof. exact: Monoid.mulmCA. Qed.

Lemma addeACA : @interchange (\bar R) +%E +%E.
Proof. exact: Monoid.mulmACA. Qed.

Lemma adde_gt0 x y : 0 < x -> 0 < y -> 0 < x + y.
Proof.
by move: x y => [x| |] [y| |] //; rewrite !lte_fin; exact: addr_gt0.
Qed.

Lemma padde_eq0 x y : 0 <= x -> 0 <= y -> (x + y == 0) = (x == 0) && (y == 0).
Proof.
move: x y => [x| |] [y| |]//; rewrite !lee_fin; first exact: paddr_eq0.
by move=> x0 _ /=; rewrite andbF.
Qed.

Lemma nadde_eq0 x y : x <= 0 -> y <= 0 -> (x + y == 0) = (x == 0) && (y == 0).
Proof.
move: x y => [x| |] [y| |]//; rewrite !lee_fin; first exact: naddr_eq0.
by move=> x0 _ /=; rewrite andbF.
Qed.

Lemma realDe x y : (0%E >=< x)%O -> (0%E >=< y)%O -> (0%E >=< x + y)%O.
Proof. case: x y => [x||] [y||] //; exact: realD. Qed.

Lemma oppe0 : - 0 = 0 :> \bar R.
Proof. by rewrite /= oppr0. Qed.

Lemma oppeK : involutive (A := \bar R) -%E.
Proof. by case=> [x||] //=; rewrite opprK. Qed.

Lemma oppe_inj : @injective (\bar R) _ -%E.
Proof. exact: inv_inj oppeK. Qed.

Lemma adde_defNN x y : - x +? - y = x +? y.
Proof. by rewrite adde_defN oppeK. Qed.

Lemma oppe_eq0 x : (- x == 0)%E = (x == 0)%E.
Proof. by rewrite -(can_eq oppeK) oppe0. Qed.

Lemma oppeD x y : x +? y -> - (x + y) = - x - y.
Proof. by move: x y => [x| |] [y| |] //= _; rewrite opprD. Qed.

Lemma fin_num_oppeD x y : y \is a fin_num -> - (x + y) = - x - y.
Proof. by move=> finy; rewrite oppeD// fin_num_adde_defl. Qed.

Lemma sube0 x : x - 0 = x.
Proof. by move: x => [x| |] //; rewrite -EFinB subr0. Qed.

Lemma sub0e x : 0 - x = - x.
Proof. by move: x => [x| |] //; rewrite -EFinB sub0r. Qed.

Lemma muleC x y : x * y = y * x.
Proof. by move: x y => [r||] [s||]//=; rewrite -EFinM mulrC. Qed.

Lemma onee_neq0 : 1 != 0 :> \bar R. Proof. exact: oner_neq0. Qed.
Lemma onee_eq0 : 1 == 0 :> \bar R = false. Proof. exact: oner_eq0. Qed.

Lemma mule1 x : x * 1 = x.
Proof.
by move: x=> [r||]/=; rewrite /mule/= ?mulr1 ?(negbTE onee_neq0) ?lte_tofin.
Qed.

Lemma mul1e x : 1 * x = x.
Proof. by rewrite muleC mule1. Qed.

Lemma mule0 x : x * 0 = 0.
Proof. by move: x => [r| |] //=; rewrite /mule/= ?mulr0// eqxx. Qed.

Lemma mul0e x : 0 * x = 0.
Proof. by move: x => [r| |]/=; rewrite /mule/= ?mul0r// eqxx. Qed.

HB.instance Definition _ := Monoid.isMulLaw.Build (\bar R) 0 mule mul0e mule0.

Lemma expeS x n : x ^+ n.+1 = x * x ^+ n.
Proof. by case: n => //=; rewrite mule1. Qed.

Lemma EFin_expe r n : (r ^+ n)%:E = r%:E ^+ n.
Proof. by elim: n => [//|n IHn]; rewrite exprS EFinM IHn expeS. Qed.

Definition mule_def x y :=
  ~~ (((x == 0) && (`| y | == +oo)) || ((y == 0) && (`| x | == +oo))).

Local Notation "x *? y" := (mule_def x y).

Lemma mule_defC x y : x *? y = y *? x.
Proof. by rewrite [in LHS]/mule_def orbC. Qed.

Lemma mule_def_fin x y : x \is a fin_num -> y \is a fin_num -> x *? y.
Proof.
move: x y => [x| |] [y| |] finx finy//.
by rewrite /mule_def negb_or 2!negb_and/= 2!orbT.
Qed.

Lemma mule_def_neq0_infty x y : x != 0 -> y \isn't a fin_num -> x *? y.
Proof. by move: x y => [x| |] [y| |]// x0 _; rewrite /mule_def (negbTE x0). Qed.

Lemma mule_def_infty_neq0 x y : x \isn't a fin_num -> y!= 0 -> x *? y.
Proof. by move: x y => [x| |] [y| |]// _ y0; rewrite /mule_def (negbTE y0). Qed.

Lemma neq0_mule_def x y :  x * y != 0 -> x *? y.
Proof.
move: x y => [x| |] [y| |] //; first by rewrite mule_def_fin.
- by have [->|?] := eqVneq x 0%R; rewrite ?mul0e ?eqxx// mule_def_neq0_infty.
- by have [->|?] := eqVneq x 0%R; rewrite ?mul0e ?eqxx// mule_def_neq0_infty.
- by have [->|?] := eqVneq y 0%R; rewrite ?mule0 ?eqxx// mule_def_infty_neq0.
- by have [->|?] := eqVneq y 0%R; rewrite ?mule0 ?eqxx// mule_def_infty_neq0.
Qed.

Lemma ltpinfty_adde_def : {in [pred x | x < +oo] &, forall x y, x +? y}.
Proof. by move=> [x| |] [y| |]. Qed.

Lemma ltninfty_adde_def : {in [pred x | -oo < x] &, forall x y, x +? y}.
Proof. by move=> [x| |] [y| |]. Qed.

Lemma abse_eq0 x : (`|x| == 0) = (x == 0).
Proof. by move: x => [| |] //= r; rewrite !eqe normr_eq0. Qed.

Lemma abse0 : `|0| = 0 :> \bar R. Proof. by rewrite /abse/= normr0. Qed.

Lemma abse1 : `|1| = 1 :> \bar R. Proof. by rewrite /abse normr1. Qed.

Lemma abseN x : `|- x| = `|x|.
Proof. by case: x => [r||]; rewrite //= normrN. Qed.

Lemma eqe_opp x y : (- x == - y) = (x == y).
Proof.
move: x y => [r| |] [r'| |] //=; apply/idP/idP => [|/eqP[->]//].
by move/eqP => -[] /eqP; rewrite eqr_opp => /eqP ->.
Qed.

Lemma eqe_oppP x y : (- x = - y) <-> (x = y).
Proof. by split=> [/eqP | -> //]; rewrite eqe_opp => /eqP. Qed.

Lemma eqe_oppLR x y : (- x == y) = (x == - y).
Proof. by move: x y => [r0| |] [r1| |] //=; rewrite !eqe eqr_oppLR. Qed.

Lemma eqe_oppLRP x y : (- x = y) <-> (x = - y).
Proof.
split=> /eqP; first by rewrite eqe_oppLR => /eqP.
by rewrite -eqe_oppLR => /eqP.
Qed.

Lemma fin_numN x : (- x \is a fin_num) = (x \is a fin_num).
Proof. by rewrite !fin_num_abs abseN. Qed.

Lemma oppeB x y : x +? - y -> - (x - y) = - x + y.
Proof. by move=> xy; rewrite oppeD// oppeK. Qed.

Lemma fin_num_oppeB x y : y \is a fin_num -> - (x - y) = - x + y.
Proof. by move=> ?; rewrite oppeB// adde_defN fin_num_adde_defl. Qed.

Lemma fin_numD x y :
  (x + y \is a fin_num) = (x \is a fin_num) && (y \is a fin_num).
Proof. by move: x y => [x| |] [y| |]. Qed.

Lemma sum_fin_num (T : Type) (s : seq T) (P : pred T) (f : T -> \bar R) :
  \sum_(i <- s | P i) f i \is a fin_num =
  all [pred x | x \is a fin_num] [seq f i | i <- s & P i].
Proof.
by rewrite -big_all big_map big_filter; exact: (big_morph _ fin_numD).
Qed.

Lemma sum_fin_numP (T : eqType) (s : seq T) (P : pred T) (f : T -> \bar R) :
  reflect (forall i, i \in s -> P i -> f i \is a fin_num)
          (\sum_(i <- s | P i) f i \is a fin_num).
Proof.
rewrite sum_fin_num; apply: (iffP allP) => /=.
  by move=> + x xs Px; apply; rewrite map_f// mem_filter Px.
by move=> + _ /mapP[x /[!mem_filter]/andP[Px xs] ->]; apply.
Qed.

Lemma fin_numB x y :
  (x - y \is a fin_num) = (x \is a fin_num) && (y \is a fin_num).
Proof. by move: x y => [x| |] [y| |]. Qed.

Lemma fin_numM x y : x \is a fin_num -> y \is a fin_num ->
  x * y \is a fin_num.
Proof. by move: x y => [x| |] [y| |]. Qed.

Lemma prode_fin_num (I : Type) (s : seq I) (P : pred I) (f : I -> \bar R) :
  (forall i, P i -> f i \is a fin_num) ->
  \prod_(i <- s | P i) f i \is a fin_num.
Proof. by move=> ffin; elim/big_ind : _ => // x y x0 y0; rewrite fin_numM. Qed.

Lemma fin_numX x n : x \is a fin_num -> x ^+ n \is a fin_num.
Proof. by elim: n x => // n ih x finx; rewrite expeS fin_numM// ih. Qed.

Lemma fineD : {in @fin_num R &, {morph fine : x y / x + y >-> (x + y)%R}}.
Proof. by move=> [r| |] [s| |]. Qed.

Lemma fineB : {in @fin_num R &, {morph fine : x y / x - y >-> (x - y)%R}}.
Proof. by move=> [r| |] [s| |]. Qed.

Lemma fineM : {in @fin_num R &, {morph fine : x y / x * y >-> (x * y)%R}}.
Proof. by move=> [x| |] [y| |]. Qed.

Lemma fineK x : x \is a fin_num -> (fine x)%:E = x.
Proof. by case: x. Qed.

Lemma EFin_sum_fine (I : Type) s (P : pred I) (f : I -> \bar R) :
    (forall i, P i -> f i \is a fin_num) ->
  (\sum_(i <- s | P i) fine (f i))%:E = \sum_(i <- s | P i) f i.
Proof.
by move=> h; rewrite -sumEFin; apply: eq_bigr => i Pi; rewrite fineK// h.
Qed.

Lemma sum_fine (I : Type) s (P : pred I) (F : I -> \bar R) :
    (forall i, P i -> F i \is a fin_num) ->
  (\sum_(i <- s | P i) fine (F i) = fine (\sum_(i <- s | P i) F i))%R.
Proof. by move=> h; rewrite -EFin_sum_fine. Qed.

Lemma sumeN I s (P : pred I) (f : I -> \bar R) :
    {in P &, forall i j, f i +? f j} ->
  \sum_(i <- s | P i) - f i = - \sum_(i <- s | P i) f i.
Proof.
elim: s => [|a b ih h]; first by rewrite !big_nil oppe0.
rewrite !big_cons; case: ifPn => Pa; last by rewrite ih.
by rewrite oppeD ?ih// adde_def_sum// => i Pi; rewrite h.
Qed.

Lemma fin_num_sumeN I s (P : pred I) (f : I -> \bar R) :
    (forall i, P i -> f i \is a fin_num) ->
  \sum_(i <- s | P i) - f i = - \sum_(i <- s | P i) f i.
Proof.
by move=> h; rewrite sumeN// => i j Pi Pj; rewrite fin_num_adde_defl// h.
Qed.

Lemma telescope_sume n m (f : nat -> \bar R) :
  (forall i, (n <= i <= m)%N -> f i \is a fin_num) -> (n <= m)%N ->
  \sum_(n <= k < m) (f k.+1 - f k) = f m - f n.
Proof.
move=> nmf nm; under eq_big_nat => i /andP[ni im] do
  rewrite -[f i.+1]fineK -1?[f i]fineK ?(nmf, ni, im) 1?ltnW//= -EFinD.
by rewrite sumEFin telescope_sumr// EFinB !fineK ?nmf ?nm ?leqnn.
Qed.

Lemma addeK x y : x \is a fin_num -> y + x - x = y.
Proof. by move: x y => [x| |] [y| |] //; rewrite -EFinD -EFinB addrK. Qed.

Lemma subeK x y : y \is a fin_num -> x - y + y = x.
Proof. by move: x y => [x| |] [y| |] //; rewrite -EFinD subrK. Qed.

Lemma subee x : x \is a fin_num -> x - x = 0.
Proof. by move: x => [r _| |] //; rewrite -EFinB subrr. Qed.

Lemma sube_eq x y z : x \is a fin_num -> (y +? z) ->
  (x - z == y) = (x == y + z).
Proof.
by move: x y z => [x| |] [y| |] [z| |] // _ _; rewrite !eqe subr_eq.
Qed.

Lemma adde_eq_ninfty x y : (x + y == -oo) = ((x == -oo) || (y == -oo)).
Proof. by move: x y => [?| |] [?| |]. Qed.

Lemma addye x : x != -oo -> +oo + x = +oo. Proof. by case: x. Qed.

Lemma addey x : x != -oo -> x + +oo = +oo. Proof. by case: x. Qed.

Lemma addNye x : -oo + x = -oo. Proof. by []. Qed.

Lemma addeNy x : x + -oo = -oo. Proof. by case: x. Qed.

Lemma adde_Neq_pinfty x y : x != -oo -> y != -oo ->
  (x + y != +oo) = (x != +oo) && (y != +oo).
Proof. by move: x y => [x| |] [y| |]. Qed.

Lemma adde_Neq_ninfty x y : x != +oo -> y != +oo ->
  (x + y != -oo) = (x != -oo) && (y != -oo).
Proof. by move: x y => [x| |] [y| |]. Qed.

Lemma adde_ss_eq0 x y : (0 <= x) && (0 <= y) || (x <= 0) && (y <= 0) ->
  x + y == 0 = (x == 0) && (y == 0).
Proof. by move=> /orP[|] /andP[]; [exact: padde_eq0|exact: nadde_eq0]. Qed.

Lemma esum_eqNyP (T : eqType) (s : seq T) (P : pred T) (f : T -> \bar R) :
  \sum_(i <- s | P i) f i = -oo <-> exists i, [/\ i \in s, P i & f i = -oo].
Proof.
split=> [|[i [si Pi fi]]].
  rewrite big_seq_cond; elim/big_ind: _ => // [[?| |] [?| |]//|].
  by move=> i /andP[si Pi] fioo; exists i; rewrite si Pi fioo.
rewrite big_mkcond (bigID (xpred1 i))/= (eq_bigr (fun _ => -oo)); last first.
  by move=> j /eqP ->; rewrite Pi.
rewrite big_const_seq/= [X in X + _](_ : _ = -oo)//.
elim: s i Pi fi si => // h t ih i Pi fi.
rewrite inE => /predU1P[<-/=|it]; first by rewrite eqxx.
by rewrite /= iterD ih//=; case: (_ == _).
Qed.

Lemma esum_eqNy (I : finType) (f : I -> \bar R) (P : {pred I}) :
  (\sum_(i | P i) f i == -oo) = [exists i in P, f i == -oo].
Proof.
apply/idP/idP => [/eqP/esum_eqNyP|/existsP[i /andP[Pi /eqP fi]]].
  by move=> -[i [_ Pi fi]]; apply/existsP; exists i; rewrite fi eqxx andbT.
by apply/eqP/esum_eqNyP; exists i.
Qed.

Lemma esum_eqyP (T : eqType) (s : seq T) (P : pred T) (f : T -> \bar R) :
  (forall i, P i -> f i != -oo) ->
  \sum_(i <- s | P i) f i = +oo <-> exists i, [/\ i \in s, P i & f i = +oo].
Proof.
move=> finoo; split=> [|[i [si Pi fi]]].
  rewrite big_seq_cond; elim/big_ind: _ => // [[?| |] [?| |]//|].
  by move=> i /andP[si Pi] fioo; exists i; rewrite si Pi fioo.
elim: s i Pi fi si => // h t ih i Pi fi.
rewrite inE => /predU1P[<-/=|it].
  rewrite big_cons Pi fi addye//.
  by apply/eqP => /esum_eqNyP[j [jt /finoo/negbTE/eqP]].
by rewrite big_cons; case: ifPn => Ph; rewrite (ih i)// addey// finoo.
Qed.

Lemma esum_eqy (I : finType) (P : {pred I}) (f : I -> \bar R) :
  (forall i, P i -> f i != -oo) ->
  (\sum_(i | P i) f i == +oo) = [exists i in P, f i == +oo].
Proof.
move=> fio; apply/idP/existsP => [/eqP /=|[/= i /andP[Pi /eqP fi]]].
  have {}fio : (forall i, P i -> f i != -oo) by move=> i Pi; exact: fio.
  by move=> /(esum_eqyP _ fio)[i [_ Pi fi]]; exists i; rewrite fi eqxx andbT.
by apply/eqP/esum_eqyP => //; exists i.
Qed.

#[deprecated(since="mathcomp-analysis 0.6.0", note="renamed `esum_eqNyP`")]
Notation esum_ninftyP := esum_eqNyP (only parsing).
#[deprecated(since="mathcomp-analysis 0.6.0", note="renamed `esum_eqNy`")]
Notation esum_ninfty := esum_eqNy (only parsing).
#[deprecated(since="mathcomp-analysis 0.6.0", note="renamed `esum_eqyP`")]
Notation esum_pinftyP := esum_eqyP (only parsing).
#[deprecated(since="mathcomp-analysis 0.6.0", note="renamed `esum_eqy`")]
Notation esum_pinfty := esum_eqy (only parsing).

Lemma adde_ge0 x y : 0 <= x -> 0 <= y -> 0 <= x + y.
Proof. by move: x y => [r0| |] [r1| |] // ? ?; rewrite !lee_fin addr_ge0. Qed.

Lemma adde_le0 x y : x <= 0 -> y <= 0 -> x + y <= 0.
Proof.
move: x y => [r0||] [r1||]// ? ?; rewrite !lee_fin -(addr0 0%R); exact: lerD.
Qed.

Lemma oppe_gt0 x : (0 < - x) = (x < 0).
Proof. move: x => [x||] //; exact: oppr_gt0. Qed.

Lemma oppe_lt0 x : (- x < 0) = (0 < x).
Proof. move: x => [x||] //; exact: oppr_lt0. Qed.

Lemma oppe_ge0 x : (0 <= - x) = (x <= 0).
Proof. move: x => [x||] //; exact: oppr_ge0. Qed.

Lemma oppe_le0 x : (- x <= 0) = (0 <= x).
Proof. move: x => [x||] //; exact: oppr_le0. Qed.

Lemma oppe_cmp0 x : (0 >=< - x)%O = (0 >=< x)%O.
Proof. by rewrite /Order.comparable oppe_ge0 oppe_le0 orbC. Qed.

Lemma sume_ge0 T (f : T -> \bar R) (P : pred T) :
  (forall t, P t -> 0 <= f t) -> forall l, 0 <= \sum_(i <- l | P i) f i.
Proof. by move=> f0 l; elim/big_rec : _ => // t x Pt; apply/adde_ge0/f0. Qed.

Lemma sume_le0 T (f : T -> \bar R) (P : pred T) :
  (forall t, P t -> f t <= 0) -> forall l, \sum_(i <- l | P i) f i <= 0.
Proof. by move=> f0 l; elim/big_rec : _ => // t x Pt; apply/adde_le0/f0. Qed.

Lemma mulNyy : -oo * +oo = -oo :> \bar R. Proof. by rewrite /mule /= lt0y. Qed.

Lemma mulyNy : +oo * -oo = -oo :> \bar R. Proof. by rewrite muleC mulNyy. Qed.

Lemma mulyy : +oo * +oo = +oo :> \bar R. Proof. by rewrite /mule /= lt0y. Qed.

Lemma mulNyNy : -oo * -oo = +oo :> \bar R. Proof. by []. Qed.

Lemma real_mulry r : r \is Num.real -> r%:E * +oo = (Num.sg r)%:E * +oo.
Proof.
move=> rreal; rewrite /mule/= !eqe sgr_eq0; case: ifP => [//|rn0].
move: rreal => /orP[|]; rewrite le_eqVlt.
  by rewrite eq_sym rn0/= => rgt0; rewrite lte_fin rgt0 gtr0_sg// lte01.
by rewrite rn0/= => rlt0; rewrite lt_def lt_geF// andbF ltr0_sg// lte0N1.
Qed.

Lemma real_mulyr r : r \is Num.real -> +oo * r%:E = (Num.sg r)%:E * +oo.
Proof. by move=> rreal; rewrite muleC real_mulry. Qed.

Lemma real_mulrNy r : r \is Num.real -> r%:E * -oo = (Num.sg r)%:E * -oo.
Proof.
move=> rreal; rewrite /mule/= !eqe sgr_eq0; case: ifP => [//|rn0].
move: rreal => /orP[|]; rewrite le_eqVlt.
  by rewrite eq_sym rn0/= => rgt0; rewrite lte_fin rgt0 gtr0_sg// lte01.
by rewrite rn0/= => rlt0; rewrite lt_def lt_geF// andbF ltr0_sg// lte0N1.
Qed.

Lemma real_mulNyr r : r \is Num.real -> -oo * r%:E = (Num.sg r)%:E * -oo.
Proof. by move=> rreal; rewrite muleC real_mulrNy. Qed.

Definition real_mulr_infty := (real_mulry, real_mulyr, real_mulrNy, real_mulNyr).

Lemma mulN1e x : - 1%E * x = - x.
Proof.
rewrite -EFinN /mule/=; case: x => [x||];
  do ?[by rewrite mulN1r|by rewrite eqe oppr_eq0 oner_eq0 lte_fin ltr0N1].
Qed.

Lemma muleN1 x : x * - 1%E = - x. Proof. by rewrite muleC mulN1e. Qed.

Lemma mule_neq0 x y : x != 0 -> y != 0 -> x * y != 0.
Proof.
move: x y => [x||] [y||] x0 y0 //; rewrite /mule/= ?(lt0y,mulf_neq0)//;
  try by (rewrite (negbTE x0); case: ifPn) ||
      by (rewrite (negbTE y0); case: ifPn).
Qed.

Lemma mule_eq0 x y : (x * y == 0) = (x == 0) || (y == 0).
Proof.
apply/idP/idP => [|/orP[] /eqP->]; rewrite ?(mule0, mul0e)//.
by apply: contraTT => /norP[]; apply: mule_neq0.
Qed.

Lemma mule_ge0 x y : 0 <= x -> 0 <= y -> 0 <= x * y.
Proof.
move: x y => [x||] [y||]//=; rewrite /mule/= ?(lee_fin, eqe, lte_fin, lt0y)//.
- exact: mulr_ge0.
- rewrite le_eqVlt => /predU1P[<- _|x0 _]; first by rewrite eqxx.
  by rewrite gt_eqF // x0 le0y.
- move=> _; rewrite le_eqVlt => /predU1P[<-|y0]; first by rewrite eqxx.
  by rewrite gt_eqF // y0 le0y.
Qed.

Lemma prode_ge0 (I : Type) (s : seq I) (P : pred I) (f : I -> \bar R) :
  (forall i, P i -> 0 <= f i) -> 0 <= \prod_(i <- s | P i) f i.
Proof. by move=> f0; elim/big_ind : _ => // x y x0 y0; rewrite mule_ge0. Qed.

Lemma mule_gt0 x y : 0 < x -> 0 < y -> 0 < x * y.
Proof.
by rewrite !lt_def => /andP[? ?] /andP[? ?]; rewrite mule_neq0 ?mule_ge0.
Qed.

Lemma mule_le0 x y : x <= 0 -> y <= 0 -> 0 <= x * y.
Proof.
move: x y => [x||] [y||]//=; rewrite /mule/= ?(lee_fin, eqe, lte_fin)//.
- exact: mulr_le0.
- by rewrite lt_leAnge => -> _; case: ifP => _ //; rewrite andbF le0y.
- by rewrite lt_leAnge => _ ->; case: ifP => _ //; rewrite andbF le0y.
Qed.

Lemma mule_le0_ge0 x y : x <= 0 -> 0 <= y -> x * y <= 0.
Proof.
move: x y => [x| |] [y| |] //; rewrite /mule/= ?(lee_fin, lte_fin).
- exact: mulr_le0_ge0.
- by move=> x0 _; case: ifP => _ //; rewrite lt_leAnge /= x0 andbF leNy0.
- move=> _; rewrite le_eqVlt => /predU1P[<-|->]; first by rewrite eqxx.
  by case: ifP => _ //; rewrite leNy0.
- by rewrite lt0y leNy0.
Qed.

Lemma mule_ge0_le0 x y : 0 <= x -> y <= 0 -> x * y <= 0.
Proof. by move=> x0 y0; rewrite muleC mule_le0_ge0. Qed.

Lemma mule_lt0_lt0 x y : x < 0 -> y < 0 -> 0 < x * y.
Proof.
by rewrite !lt_neqAle => /andP[? ?]/andP[*]; rewrite eq_sym mule_neq0 ?mule_le0.
Qed.

Lemma mule_gt0_lt0 x y : 0 < x -> y < 0 -> x * y < 0.
Proof.
rewrite lt_def !lt_neqAle => /andP[? ?]/andP[? ?].
by rewrite mule_neq0 ?mule_ge0_le0.
Qed.

Lemma mule_lt0_gt0 x y : x < 0 -> 0 < y -> x * y < 0.
Proof. by move=> x0 y0; rewrite muleC mule_gt0_lt0. Qed.

Lemma gteN x : 0 < x -> - x < x.
Proof. by case: x => //= r; rewrite !lte_fin; apply: gtrN. Qed.

Lemma realMe x y : (0%E >=< x)%O -> (0%E >=< y)%O -> (0%E >=< x * y)%O.
Proof.
case: x y => [x||] [y||]// rx ry;
  do ?[exact: realM
      |by rewrite /mule/= lt0y
      |by rewrite real_mulr_infty ?realE -?lee_fin// /Num.sg;
          case: ifP; [|case: ifP]; rewrite ?mul0e /Order.comparable ?lexx;
          rewrite ?mulN1e ?leNy0 ?mul1e ?le0y
      |by rewrite mulNyNy /Order.comparable le0y].
Qed.

Lemma real_fine (x : \bar R) : (0 >=< x)%O = (fine x \in Num.real).
Proof. by case: x => [x //||//]; rewrite /= real0 /Order.comparable le0y. Qed.

Lemma real_muleN (x y : \bar R) : (0 >=< x)%O -> (0 >=< y)%O ->
  x * - y = - (x * y).
Proof.
rewrite !real_fine; case: x y => [x||] [y||] /= xr yr; rewrite /mule/=.
- by rewrite mulrN.
- by case: ifP; rewrite ?oppe0//; case: ifP.
- by case: ifP; rewrite ?oppe0//; case: ifP.
- rewrite EFinN oppe_eq0; case: ifP; rewrite ?oppe0// oppe_gt0 !lte_fin.
  by case: (real_ltgtP xr yr) => // <-; rewrite eqxx.
- by case: ifP.
- by case: ifP.
- rewrite EFinN oppe_eq0; case: ifP; rewrite ?oppe0// oppe_gt0 !lte_fin.
  by case: (real_ltgtP xr yr) => // <-; rewrite eqxx.
- by rewrite lt0y.
- by rewrite lt0y.
Qed.

Lemma real_mulNe (x y : \bar R) : (0 >=< x)%O -> (0 >=< y)%O ->
  - x * y = - (x * y).
Proof. by move=> rx ry; rewrite muleC real_muleN 1?muleC. Qed.

Lemma real_muleNN (x y : \bar R) : (0 >=< x)%O -> (0 >=< y)%O ->
  - x * - y = x * y.
Proof. by move=> rx ry; rewrite real_muleN ?real_mulNe ?oppeK ?oppe_cmp0. Qed.

Lemma sqreD x y : x + y \is a fin_num ->
  (x + y) ^+ 2 = x ^+ 2 + x * y *+ 2 + y ^+ 2.
Proof.
case: x y => [x||] [y||] // _.
by rewrite -EFinM -EFin_natmul -!EFin_expe -!EFinD sqrrD.
Qed.

Lemma abse_ge0 x : 0 <= `|x|.
Proof. by move: x => [x| |] /=; rewrite ?le0y ?lee_fin. Qed.

Lemma gee0_abs x : 0 <= x -> `|x| = x.
Proof.
by move: x => [x| |]//; rewrite lee_fin => x0; apply/eqP; rewrite eqe ger0_norm.
Qed.

Lemma gte0_abs x : 0 < x -> `|x| = x. Proof. by move=> /ltW/gee0_abs. Qed.

Lemma lee0_abs x : x <= 0 -> `|x| = - x.
Proof.
by move: x => [x| |]//; rewrite lee_fin => x0; apply/eqP; rewrite eqe ler0_norm.
Qed.

Lemma lte0_abs x : x < 0 -> `|x| = - x.
Proof. by move=> /ltW/lee0_abs. Qed.

End ERealArithTh_numDomainType.
Notation "x +? y" := (adde_def x%dE y%dE) : ereal_dual_scope.
Notation "x +? y" := (adde_def x y) : ereal_scope.
Notation "x *? y" := (mule_def x%dE y%dE) : ereal_dual_scope.
Notation "x *? y" := (mule_def x y) : ereal_scope.

Notation maxe := (@Order.max ereal_display _).
Notation "@ 'maxe' R" := (@Order.max ereal_display R)
  (at level 10, R at level 8, only parsing) : function_scope.

Notation mine := (@Order.min ereal_display _).
Notation "@ 'mine' R" := (@Order.min ereal_display R)
  (at level 10, R at level 8, only parsing) : function_scope.

Module DualAddTheoryNumDomain.

Section DualERealArithTh_numDomainType.

Local Open Scope ereal_dual_scope.

Context {R : numDomainType}.

Implicit Types x y z : \bar^d R.

Lemma dual_addeE x y : (x + y)%dE = - ((- x) + (- y))%E.
Proof. by case: x => [x| |]; case: y => [y| |] //=; rewrite opprD !opprK. Qed.

Lemma dual_sumeE I (r : seq I) (P : pred I) (F : I -> \bar^d R) :
  (\sum_(i <- r | P i) F i)%dE = - (\sum_(i <- r | P i) (- F i)%E)%E.
Proof.
apply: (big_ind2 (fun x y => x = - y)%E) => [|_ x _ y -> ->|i _].
- by rewrite oppe0.
- by rewrite dual_addeE !oppeK.
- by rewrite oppeK.
Qed.

Lemma dual_addeE_def x y : x +? y -> (x + y)%dE = (x + y)%E.
Proof. by case: x => [x| |]; case: y. Qed.

Lemma dEFinD (r r' : R) : (r + r')%R%:E = r%:E + r'%:E.
Proof. by []. Qed.

Lemma dEFinE (r : R) : dEFin r = r%:E. Proof. by []. Qed.

Lemma dEFin_semi_additive : @semi_additive _ (\bar^d R) dEFin.
Proof. by split. Qed.
#[export]
HB.instance Definition _ := GRing.isSemiAdditive.Build R (\bar^d R) dEFin
  dEFin_semi_additive.

Lemma dEFinB (r r' : R) : (r - r')%R%:E = r%:E - r'%:E.
Proof. by []. Qed.

Lemma dsumEFin I r P (F : I -> R) :
  \sum_(i <- r | P i) (F i)%:E = (\sum_(i <- r | P i) F i)%R%:E.
Proof. by rewrite dual_sumeE fin_num_sumeN// oppeK sumEFin. Qed.

Lemma daddeC : commutative (S := \bar^d R) +%dE. Proof. exact: addrC. Qed.

Lemma dadde0 : right_id (0 : \bar^d R) +%dE. Proof. exact: addr0. Qed.

Lemma dadd0e : left_id (0 : \bar^d R) +%dE. Proof. exact: add0r. Qed.

Lemma daddeA : associative (S := \bar^d R) +%dE. Proof. exact: addrA. Qed.

Lemma daddeAC : right_commutative (S := \bar^d R) +%dE.
Proof. exact: Monoid.mulmAC. Qed.

Lemma daddeCA : left_commutative (S := \bar^d R) +%dE.
Proof. exact: Monoid.mulmCA. Qed.

Lemma daddeACA : @interchange (\bar^d R) +%dE +%dE.
Proof. exact: Monoid.mulmACA. Qed.

Lemma realDed x y : (0%dE >=< x)%O -> (0%dE >=< y)%O -> (0%dE >=< x + y)%O.
Proof. case: x y => [x||] [y||] //; exact: realD. Qed.

Lemma doppeD x y : x +? y -> - (x + y) = - x - y.
Proof. by move: x y => [x| |] [y| |] //= _; rewrite opprD. Qed.

Lemma fin_num_doppeD x y : y \is a fin_num -> - (x + y) = - x - y.
Proof. by move=> finy; rewrite doppeD// fin_num_adde_defl. Qed.

Lemma dsube0 x : x - 0 = x.
Proof. by move: x => [x| |] //; rewrite -dEFinB subr0. Qed.

Lemma dsub0e x : 0 - x = - x.
Proof. by move: x => [x| |] //; rewrite -dEFinB sub0r. Qed.

Lemma doppeB x y : x +? - y -> - (x - y) = - x + y.
Proof. by move=> xy; rewrite doppeD// oppeK. Qed.

Lemma fin_num_doppeB x y : y \is a fin_num -> - (x - y) = - x + y.
Proof. by move=> ?; rewrite doppeB// fin_num_adde_defl// fin_numN. Qed.

Lemma dfin_numD x y :
  (x + y \is a fin_num) = (x \is a fin_num) && (y \is a fin_num).
Proof. by move: x y => [x| |] [y| |]. Qed.

Lemma dfineD :
  {in (@fin_num R) &, {morph fine : x y / x + y >-> (x + y)%R}}.
Proof. by move=> [r| |] [s| |]. Qed.

Lemma dfineB : {in @fin_num R &, {morph fine : x y / x - y >-> (x - y)%R}}.
Proof. by move=> [r| |] [s| |]. Qed.

Lemma daddeK x y : x \is a fin_num -> y + x - x = y.
Proof. by move=> fx; rewrite !dual_addeE oppeK addeK ?oppeK; case: x fx. Qed.

Lemma dsubeK x y : y \is a fin_num -> x - y + y = x.
Proof. by move=> fy; rewrite !dual_addeE oppeK subeK ?oppeK; case: y fy. Qed.

Lemma dsubee x : x \is a fin_num -> x - x = 0.
Proof. by move=> fx; rewrite dual_addeE subee ?oppe0; case: x fx. Qed.

Lemma dsube_eq x y z : x \is a fin_num -> (y +? z) ->
  (x - z == y) = (x == y + z).
Proof.
by move: x y z => [x| |] [y| |] [z| |] // _ _; rewrite !eqe subr_eq.
Qed.

Lemma dadde_eq_pinfty x y : (x + y == +oo) = ((x == +oo) || (y == +oo)).
Proof. by move: x y => [?| |] [?| |]. Qed.

Lemma daddye x : +oo + x = +oo. Proof. by []. Qed.

Lemma daddey x : x + +oo = +oo. Proof. by case: x. Qed.

Lemma daddNye x : x != +oo -> -oo + x = -oo. Proof. by case: x. Qed.

Lemma daddeNy x : x != +oo -> x + -oo = -oo. Proof. by case: x. Qed.

Lemma dadde_Neq_pinfty x y : x != -oo -> y != -oo ->
  (x + y != +oo) = (x != +oo) && (y != +oo).
Proof. by move: x y => [x| |] [y| |]. Qed.

Lemma dadde_Neq_ninfty x y : x != +oo -> y != +oo ->
  (x + y != -oo) = (x != -oo) && (y != -oo).
Proof. by move: x y => [x| |] [y| |]. Qed.

Lemma ndadde_eq0 x y : x <= 0 -> y <= 0 -> x + y == 0 = (x == 0) && (y == 0).
Proof.
move: x y => [x||] [y||] //.
- by rewrite !lee_fin -dEFinD !eqe; exact: naddr_eq0.
- by rewrite /adde/= (_ : -oo == 0 = false)// andbF.
Qed.

Lemma pdadde_eq0 x y : 0 <= x -> 0 <= y -> x + y == 0 = (x == 0) && (y == 0).
Proof.
move: x y => [x||] [y||] //.
- by rewrite !lee_fin -dEFinD !eqe; exact: paddr_eq0.
- by rewrite /adde/= (_ : +oo == 0 = false)// andbF.
Qed.

Lemma dadde_ss_eq0 x y : (0 <= x) && (0 <= y) || (x <= 0) && (y <= 0) ->
  x + y == 0 = (x == 0) && (y == 0).
Proof. move=> /orP[|] /andP[]; [exact: pdadde_eq0|exact: ndadde_eq0]. Qed.

Lemma desum_eqyP (T : eqType) (s : seq T) (P : pred T) (f : T -> \bar^d R) :
  \sum_(i <- s | P i) f i = +oo <-> exists i, [/\ i \in s, P i & f i = +oo].
Proof.
rewrite dual_sumeE eqe_oppLRP /= esum_eqNyP.
by split=> -[i + /ltac:(exists i)] => [|] []; [|split]; rewrite // eqe_oppLRP.
Qed.

Lemma desum_eqy (I : finType) (f : I -> \bar R) (P : {pred I}) :
  (\sum_(i | P i) f i == +oo) = [exists i in P, f i == +oo].
Proof.
rewrite dual_sumeE eqe_oppLR esum_eqNy.
by under eq_existsb => i do rewrite eqe_oppLR.
Qed.

Lemma desum_eqNyP
    (T : eqType) (s : seq T) (P : pred T) (f : T -> \bar^d R) :
  (forall i, P i -> f i != +oo) ->
  \sum_(i <- s | P i) f i = -oo <-> exists i, [/\ i \in s, P i & f i = -oo].
Proof.
move=> fioo.
rewrite dual_sumeE eqe_oppLRP /= esum_eqyP => [|i Pi]; last first.
  by rewrite eqe_oppLR fioo.
by split=> -[i + /ltac:(exists i)] => [|] []; [|split]; rewrite // eqe_oppLRP.
Qed.

Lemma desum_eqNy (I : finType) (f : I -> \bar^d R) (P : {pred I}) :
  (forall i, f i != +oo) ->
  (\sum_(i | P i) f i == -oo) = [exists i in P, f i == -oo].
Proof.
move=> finoo.
rewrite dual_sumeE eqe_oppLR /= esum_eqy => [|i]; rewrite ?eqe_oppLR //.
by under eq_existsb => i do rewrite eqe_oppLR.
Qed.

Lemma dadde_ge0 x y : 0 <= x -> 0 <= y -> 0 <= x + y.
Proof. rewrite dual_addeE oppe_ge0 -!oppe_le0; exact: adde_le0. Qed.

Lemma dadde_le0 x y : x <= 0 -> y <= 0 -> x + y <= 0.
Proof. rewrite dual_addeE oppe_le0 -!oppe_ge0; exact: adde_ge0. Qed.

Lemma dsume_ge0 T (f : T -> \bar^d R) (P : pred T) :
  (forall n, P n -> 0 <= f n) -> forall l, 0 <= \sum_(i <- l | P i) f i.
Proof.
move=> u0 l; rewrite dual_sumeE oppe_ge0 sume_le0 // => t Pt.
rewrite oppe_le0; exact: u0.
Qed.

Lemma dsume_le0 T (f : T -> \bar^d R) (P : pred T) :
  (forall n, P n -> f n <= 0) -> forall l, \sum_(i <- l | P i) f i <= 0.
Proof.
move=> u0 l; rewrite dual_sumeE oppe_le0 sume_ge0 // => t Pt.
rewrite oppe_ge0; exact: u0.
Qed.

Lemma gte_dN (r : \bar^d R) : (0 < r)%E -> (- r < r)%E.
Proof. by case: r => //= r; rewrite !lte_fin; apply: gtrN. Qed.

Lemma ednatmul_pinfty n : +oo *+ n.+1 = +oo :> \bar^d R.
Proof. by elim: n => //= n ->. Qed.

Lemma ednatmul_ninfty n : -oo *+ n.+1 = -oo :> \bar^d R.
Proof. by elim: n => //= n ->. Qed.

Lemma EFin_dnatmul (r : R) n : (r *+ n.+1)%:E = r%:E *+ n.+1.
Proof. by elim: n => //= n <-. Qed.

Lemma ednatmulE x n : x *+ n = (x *+ n)%E.
Proof.
case: x => [x| |]; case: n => [//|n].
- by rewrite -EFin_natmul -EFin_dnatmul.
- by rewrite enatmul_pinfty ednatmul_pinfty.
- by rewrite enatmul_ninfty ednatmul_ninfty.
Qed.

Lemma dmule2n x : x *+ 2 = x + x. Proof. by []. Qed.

Lemma sqredD x y : x + y \is a fin_num ->
  (x + y) ^+ 2 = x ^+ 2 + x * y *+ 2 + y ^+ 2.
Proof.
case: x y => [x||] [y||] // _.
by rewrite -EFinM -EFin_dnatmul -!EFin_expe -!dEFinD sqrrD.
Qed.

End DualERealArithTh_numDomainType.

#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed `gte_dN`")]
Notation gte_dopp := gte_dN (only parsing).

End DualAddTheoryNumDomain.

Section ERealArithTh_realDomainType.
Context {R : realDomainType}.
Implicit Types (x y z u a b : \bar R) (r : R).

Lemma fin_numElt x : (x \is a fin_num) = (-oo < x < +oo).
Proof. by rewrite fin_numE -leye_eq -leeNy_eq -2!ltNge. Qed.

Lemma fin_numPlt x : reflect (-oo < x < +oo) (x \is a fin_num).
Proof. by rewrite fin_numElt; exact: idP. Qed.

Lemma ltey_eq x : (x < +oo) = (x \is a fin_num) || (x == -oo).
Proof. by case: x => // x //=; exact: ltry. Qed.

Lemma ltNye_eq x : (-oo < x) = (x \is a fin_num) || (x == +oo).
Proof. by case: x => // x //=; exact: ltNyr. Qed.

Lemma ge0_fin_numE x : 0 <= x -> (x \is a fin_num) = (x < +oo).
Proof. by move: x => [x| |] => // x0; rewrite fin_numElt ltNyr. Qed.

Lemma gt0_fin_numE x : 0 < x -> (x \is a fin_num) = (x < +oo).
Proof. by move/ltW; exact: ge0_fin_numE. Qed.

Lemma le0_fin_numE x : x <= 0 -> (x \is a fin_num) = (-oo < x).
Proof. by move: x => [x| |]//=; rewrite lee_fin => x0; rewrite ltNyr. Qed.

Lemma lt0_fin_numE x : x < 0 -> (x \is a fin_num) = (-oo < x).
Proof. by move/ltW; exact: le0_fin_numE. Qed.

Lemma eqyP x : x = +oo <-> (forall A, (0 < A)%R -> A%:E <= x).
Proof.
split=> [-> // A A0|Ax]; first by rewrite leey.
apply/eqP; rewrite eq_le leey /= leNgt; apply/negP.
case: x Ax => [x Ax _|//|/(_ _ ltr01)//].
suff: ~ x%:E < (Order.max 0 x + 1)%:E.
  by apply; rewrite lte_fin ltr_pwDr// le_max lexx orbT.
by apply/negP; rewrite -leNgt; apply/Ax/ltr_pwDr; rewrite // le_max lexx.
Qed.

Lemma seq_psume_eq0 (I : choiceType) (r : seq I)
    (P : pred I) (F : I -> \bar R) : (forall i, P i -> 0 <= F i)%E ->
  (\sum_(i <- r | P i) F i == 0)%E = all (fun i => P i ==> (F i == 0%E)) r.
Proof.
move=> F0; apply/eqP/allP => PF0; last first.
  rewrite big_seq_cond big1// => i /andP[ir Pi].
  by have := PF0 _ ir; rewrite Pi implyTb => /eqP.
move=> i ir; apply/implyP => Pi; apply/eqP.
have rPF : {in r, forall i, P i ==> (F i \is a fin_num)}.
  move=> j jr; apply/implyP => Pj; rewrite fin_numElt; apply/andP; split.
    by rewrite (lt_le_trans _ (F0 _ Pj))// ltNyr.
  rewrite ltNge; apply/eqP; rewrite leye_eq; apply/eqP/negP => /eqP Fjoo.
  have PFninfty k : P k -> F k != -oo%E.
    by move=> Pk; rewrite gt_eqF// (lt_le_trans _ (F0 _ Pk))// ltNyr.
  have /esum_eqyP : exists i, [/\ i \in r, P i & F i = +oo%E] by exists j.
  by move=> /(_ PFninfty); rewrite PF0.
have ? : (\sum_(i <- r | P i) (fine \o F) i == 0)%R.
  apply/eqP/EFin_inj; rewrite big_seq_cond -sumEFin.
  rewrite (eq_bigr (fun i0 => F i0)); last first.
    move=> j /andP[jr Pj] /=; rewrite fineK//.
    by have := rPF _ jr; rewrite Pj implyTb.
  by rewrite -big_seq_cond PF0.
have /allP/(_ _ ir) : all (fun i => P i ==> ((fine \o F) i == 0))%R r.
  by rewrite -psumr_eq0// => j Pj/=; apply/fine_ge0/F0.
rewrite Pi implyTb => /= => /eqP Fi0.
rewrite -(@fineK _ (F i))//; last by have := rPF _ ir; rewrite Pi implyTb.
by rewrite Fi0.
Qed.

Lemma lte_add_pinfty x y : x < +oo -> y < +oo -> x + y < +oo.
Proof. by move: x y => -[r [r'| |]| |] // ? ?; rewrite -EFinD ltry. Qed.

Lemma lte_sum_pinfty I (s : seq I) (P : pred I) (f : I -> \bar R) :
  (forall i, P i -> f i < +oo) -> \sum_(i <- s | P i) f i < +oo.
Proof.
elim/big_ind : _ => [_|x y xoo yoo foo|i ?]; [exact: ltry| |exact].
by apply: lte_add_pinfty; [exact: xoo| exact: yoo].
Qed.

Lemma sube_gt0 x y : (0 < y - x) = (x < y).
Proof.
by move: x y => [r | |] [r'| |] //=; rewrite ?(ltry, ltNyr)// !lte_fin subr_gt0.
Qed.

Lemma sube_le0 x y : (y - x <= 0) = (y <= x).
Proof. by rewrite !leNgt sube_gt0. Qed.

Lemma suber_ge0 y x : y \is a fin_num -> (0 <= x - y) = (y <= x).
Proof.
by move: x y => [x| |] [y| |] //= _; rewrite ?(leey, lee_fin, subr_ge0).
Qed.

Lemma subre_ge0 x y : y \is a fin_num -> (0 <= y - x) = (x <= y).
Proof.
by move: x y => [x| |] [y| |] //=; rewrite ?(leey, leNye, lee_fin) //= subr_ge0.
Qed.

Lemma sube_ge0 x y : (x \is a fin_num) || (y \is a fin_num) ->
  (0 <= y - x) = (x <= y).
Proof. by move=> /orP[?|?]; [rewrite suber_ge0|rewrite subre_ge0]. Qed.

Lemma lteNl x y : (- x < y) = (- y < x).
Proof.
by move: x y => [r| |] [r'| |] //=; rewrite ?(ltry, ltNyr)// !lte_fin ltrNl.
Qed.

Lemma lteNr x y : (x < - y) = (y < - x).
Proof.
by move: x y => [r| |] [r'| |] //=; rewrite ?(ltry, ltNyr)// !lte_fin ltrNr.
Qed.

Lemma leeNr x y : (x <= - y) = (y <= - x).
Proof.
by move: x y => [r0| |] [r1| |] //=; rewrite ?(leey, leNye)// !lee_fin lerNr.
Qed.

Lemma leeNl x y : (- x <= y) = (- y <= x).
Proof.
by move: x y => [r0| |] [r1| |] //=; rewrite ?(leey, leNye)// !lee_fin lerNl.
Qed.

Lemma muleN x y : x * - y = - (x * y).
Proof. by rewrite real_muleN ?real_fine ?num_real. Qed.

Lemma mulNe x y : - x * y = - (x * y). Proof. by rewrite muleC muleN muleC. Qed.

Lemma muleNN x y : - x * - y = x * y. Proof. by rewrite mulNe muleN oppeK. Qed.

Lemma mulry r : r%:E * +oo%E = (Num.sg r)%:E * +oo%E.
Proof. by rewrite [LHS]real_mulry// num_real. Qed.

Lemma mulyr r : +oo%E * r%:E = (Num.sg r)%:E * +oo%E.
Proof. by rewrite muleC mulry. Qed.

Lemma mulrNy r : r%:E * -oo%E = (Num.sg r)%:E * -oo%E.
Proof. by rewrite [LHS]real_mulrNy// num_real. Qed.

Lemma mulNyr r : -oo%E * r%:E = (Num.sg r)%:E * -oo%E.
Proof. by rewrite muleC mulrNy. Qed.

Definition mulr_infty := (mulry, mulyr, mulrNy, mulNyr).

Lemma lte_mul_pinfty x y : 0 <= x -> x \is a fin_num -> y < +oo -> x * y < +oo.
Proof.
move: x y => [x| |] [y| |] // x0 xfin _; first by rewrite -EFinM ltry.
rewrite mulr_infty; move: x0; rewrite lee_fin le_eqVlt => /predU1P[<-|x0].
- by rewrite sgr0 mul0e ltry.
- by rewrite gtr0_sg // mul1e.
Qed.

Lemma mule_ge0_gt0 x y : 0 <= x -> 0 <= y -> (0 < x * y) = (0 < x) && (0 < y).
Proof.
move: x y => [x| |] [y| |] //; rewrite ?lee_fin.
- by move=> x0 y0; rewrite !lte_fin; exact: mulr_ge0_gt0.
- rewrite le_eqVlt => /predU1P[<-|x0] _; first by rewrite mul0e ltxx.
  by rewrite ltry andbT mulr_infty gtr0_sg// mul1e lte_fin x0 ltry.
- move=> _; rewrite le_eqVlt => /predU1P[<-|x0].
    by rewrite mule0 ltxx andbC.
  by rewrite ltry/= mulr_infty gtr0_sg// mul1e lte_fin x0 ltry.
- by move=> _ _; rewrite mulyy ltry.
Qed.

Lemma gt0_mulye x : (0 < x -> +oo * x = +oo)%E.
Proof.
move: x => [x|_|//]; last by rewrite mulyy.
by rewrite lte_fin => x0; rewrite muleC mulr_infty gtr0_sg// mul1e.
Qed.

Lemma lt0_mulye x : (x < 0 -> +oo * x = -oo)%E.
Proof.
move: x => [x|//|_]; last by rewrite mulyNy.
by rewrite lte_fin => x0; rewrite muleC mulr_infty ltr0_sg// mulN1e.
Qed.

Lemma gt0_mulNye x : (0 < x -> -oo * x = -oo)%E.
Proof.
move: x => [x|_|//]; last by rewrite mulNyy.
by rewrite lte_fin => x0; rewrite muleC mulr_infty gtr0_sg// mul1e.
Qed.

Lemma lt0_mulNye x : (x < 0 -> -oo * x = +oo)%E.
Proof.
move: x => [x|//|_]; last by rewrite mulNyNy.
by rewrite lte_fin => x0; rewrite muleC mulr_infty ltr0_sg// mulN1e.
Qed.

Lemma gt0_muley x : (0 < x -> x * +oo = +oo)%E.
Proof. by move=> /gt0_mulye; rewrite muleC; apply. Qed.

Lemma lt0_muley x : (x < 0 -> x * +oo = -oo)%E.
Proof. by move=> /lt0_mulye; rewrite muleC; apply. Qed.

Lemma gt0_muleNy x : (0 < x -> x * -oo = -oo)%E.
Proof. by move=> /gt0_mulNye; rewrite muleC; apply. Qed.

Lemma lt0_muleNy x : (x < 0 -> x * -oo = +oo)%E.
Proof. by move=> /lt0_mulNye; rewrite muleC; apply. Qed.

Lemma mule_eq_pinfty x y : (x * y == +oo) =
  [|| (x > 0) && (y == +oo), (x < 0) && (y == -oo),
     (x == +oo) && (y > 0) | (x == -oo) && (y < 0)].
Proof.
move: x y => [x| |] [y| |]; rewrite ?(lte_fin,andbF,andbT,orbF,eqxx,andbT)//=.
- by rewrite mulr_infty; have [/ltr0_sg|/gtr0_sg|] := ltgtP x 0%R;
    move=> ->; rewrite ?(mulN1e,mul1e,sgr0,mul0e).
- by rewrite mulr_infty; have [/ltr0_sg|/gtr0_sg|] := ltgtP x 0%R;
    move=> ->; rewrite ?(mulN1e,mul1e,sgr0,mul0e).
- by rewrite mulr_infty; have [/ltr0_sg|/gtr0_sg|] := ltgtP y 0%R;
    move=> ->; rewrite ?(mulN1e,mul1e,sgr0,mul0e).
- by rewrite mulyy ltry.
- by rewrite mulyNy.
- by rewrite mulr_infty; have [/ltr0_sg|/gtr0_sg|] := ltgtP y 0%R;
    move=> ->; rewrite ?(mulN1e,mul1e,sgr0,mul0e).
- by rewrite mulNyy.
- by rewrite ltNyr.
Qed.

Lemma mule_eq_ninfty x y : (x * y == -oo) =
  [|| (x > 0) && (y == -oo), (x < 0) && (y == +oo),
     (x == -oo) && (y > 0) | (x == +oo) && (y < 0)].
Proof.
have := mule_eq_pinfty x (- y); rewrite muleN eqe_oppLR => ->.
by rewrite !eqe_oppLR lteNr lteNl oppe0 (orbC _ ((x == -oo) && _)).
Qed.

Lemma lteD a b x y : a < b -> x < y -> a + x < b + y.
Proof.
move: a b x y=> [a| |] [b| |] [x| |] [y| |]; rewrite ?(ltry,ltNyr)//.
by rewrite !lte_fin; exact: ltrD.
Qed.

Lemma leeDl x y : 0 <= y -> x <= x + y.
Proof.
move: x y => -[ x [y| |]//= | [| |]// | [| | ]//];
  by [rewrite !lee_fin lerDl | move=> _; exact: leey].
Qed.

Lemma leeDr x y : 0 <= y -> x <= y + x.
Proof. by rewrite addeC; exact: leeDl. Qed.

Lemma geeDl x y : y <= 0 -> x + y <= x.
Proof.
move: x y => -[ x [y| |]//= | [| |]// | [| | ]//];
  by [rewrite !lee_fin gerDl | move=> _; exact: leNye].
Qed.

Lemma geeDr x y : y <= 0 -> y + x <= x. Proof. rewrite addeC; exact: geeDl. Qed.

Lemma lteDl y x : y \is a fin_num -> (y < y + x) = (0 < x).
Proof.
by move: x y => [x| |] [y| |] _ //; rewrite ?ltry ?ltNyr // !lte_fin ltrDl.
Qed.

Lemma lteDr y x : y \is a fin_num -> (y < x + y) = (0 < x).
Proof. rewrite addeC; exact: lteDl. Qed.

Lemma gte_subl y x : y \is a fin_num -> (y - x < y) = (0 < x).
Proof.
move: y x => [x| |] [y| |] _ //; rewrite addeC /= ?ltNyr ?ltry//.
by rewrite !lte_fin gtrDr ltrNl oppr0.
Qed.

Lemma gte_subr y x : y \is a fin_num -> (- x + y < y) = (0 < x).
Proof. by rewrite addeC; exact: gte_subl. Qed.

Lemma gteDl x y : x \is a fin_num -> (x + y < x) = (y < 0).
Proof.
by move: x y => [r| |] [s| |]// _; [rewrite !lte_fin gtrDl|rewrite !ltNyr].
Qed.

Lemma gteDr x y : x \is a fin_num -> (y + x < x) = (y < 0).
Proof. by rewrite addeC; exact: gteDl. Qed.

Lemma lteD2lE x a b : x \is a fin_num -> (x + a < x + b) = (a < b).
Proof.
move: a b x => [a| |] [b| |] [x| |] _ //; rewrite ?(ltry, ltNyr)//.
by rewrite !lte_fin ltrD2l.
Qed.

Lemma lteD2rE x a b : x \is a fin_num -> (a + x < b + x) = (a < b).
Proof. by rewrite -!(addeC x); exact: lteD2lE. Qed.

Lemma leeD2l x a b : a <= b -> x + a <= x + b.
Proof.
move: a b x => -[a [b [x /=|//|//] | []// |//] | []// | ].
- by rewrite !lee_fin lerD2l.
- by move=> r _; exact: leey.
- by move=> -[b [|  |]// | []// | //] r oob; exact: leNye.
Qed.

Lemma leeD2lE x a b : x \is a fin_num -> (x + a <= x + b) = (a <= b).
Proof.
move: a b x => [a| |] [b| |] [x| |] _ //; rewrite ?(leey, leNye)//.
by rewrite !lee_fin lerD2l.
Qed.

Lemma leeD2rE x a b : x \is a fin_num -> (a + x <= b + x) = (a <= b).
Proof. by rewrite -!(addeC x); exact: leeD2lE. Qed.

Lemma leeD2r x a b : a <= b -> a + x <= b + x.
Proof. rewrite addeC (addeC b); exact: leeD2l. Qed.

Lemma leeD a b x y : a <= b -> x <= y -> a + x <= b + y.
Proof.
move: a b x y => [a| |] [b| |] [x| |] [y| |]; rewrite ?(leey, leNye)//.
by rewrite !lee_fin; exact: lerD.
Qed.

Lemma lte_leD a b x y : b \is a fin_num -> a < x -> b <= y -> a + b < x + y.
Proof.
move: x y a b => [x| |] [y| |] [a| |] [b| |] _ //=; rewrite ?(ltry, ltNyr)//.
by rewrite !lte_fin; exact: ltr_leD.
Qed.

Lemma lee_ltD a b x y : a \is a fin_num -> a <= x -> b < y -> a + b < x + y.
Proof. by move=> afin xa yb; rewrite (addeC a) (addeC x) lte_leD. Qed.

Lemma leeB x y z u : x <= y -> u <= z -> x - z <= y - u.
Proof.
move: x y z u => -[x| |] -[y| |] -[z| |] -[u| |] //=; rewrite ?(leey,leNye)//.
by rewrite !lee_fin; exact: lerB.
Qed.

Lemma lte_leB z u x y : u \is a fin_num ->
  x < z -> u <= y -> x - y < z - u.
Proof.
move: z u x y => [z| |] [u| |] [x| |] [y| |] _ //=; rewrite ?(ltry, ltNyr)//.
by rewrite !lte_fin => xltr tley; apply: ltr_leD; rewrite // lerNl opprK.
Qed.

Lemma lte_pmul2r z : z \is a fin_num -> 0 < z -> {mono *%E^~ z : x y / x < y}.
Proof.
move: z => [z| |] _ // z0 [x| |] [y| |] //.
- by rewrite !lte_fin ltr_pM2r.
- by rewrite mulr_infty gtr0_sg// mul1e 2!ltry.
- by rewrite mulr_infty gtr0_sg// mul1e ltNge leNye ltNge leNye.
- by rewrite mulr_infty gtr0_sg// mul1e ltNge leey ltNge leey.
- by rewrite mulr_infty gtr0_sg// mul1e mulr_infty gtr0_sg// mul1e.
- by rewrite mulr_infty gtr0_sg// mul1e 2!ltNyr.
- by rewrite mulr_infty gtr0_sg// mul1e mulr_infty gtr0_sg// mul1e.
Qed.

Lemma lte_pmul2l z : z \is a fin_num -> 0 < z -> {mono *%E z : x y / x < y}.
Proof. by move=> zfin z0 x y; rewrite 2!(muleC z) lte_pmul2r. Qed.

Lemma lte_nmul2l z : z \is a fin_num -> z < 0 -> {mono *%E z : x y /~ x < y}.
Proof.
rewrite -oppe0 lteNr => zfin z0 x y.
by rewrite -(oppeK z) !mulNe lteNl oppeK -2!mulNe lte_pmul2l ?fin_numN.
Qed.

Lemma lte_nmul2r z : z \is a fin_num -> z < 0 -> {mono *%E^~ z : x y /~ x < y}.
Proof. by move=> zfin z0 x y; rewrite -!(muleC z) lte_nmul2l. Qed.

Lemma lte_pmulr x y : y \is a fin_num -> 0 < y -> (y < y * x) = (1 < x).
Proof. by move=> yfin y0; rewrite -[X in X < _ = _]mule1 lte_pmul2l. Qed.

Lemma lte_pmull x y : y \is a fin_num -> 0 < y -> (y < x * y) = (1 < x).
Proof. by move=> yfin y0; rewrite muleC lte_pmulr. Qed.

Lemma lte_nmulr x y : y \is a fin_num -> y < 0 -> (y < y * x) = (x < 1).
Proof. by move=> yfin y0; rewrite -[X in X < _ = _]mule1 lte_nmul2l. Qed.

Lemma lte_nmull x y : y \is a fin_num -> y < 0 -> (y < x * y) = (x < 1).
Proof. by move=> yfin y0; rewrite muleC lte_nmulr. Qed.

Lemma lee_sum I (f g : I -> \bar R) s (P : pred I) :
  (forall i, P i -> f i <= g i) ->
  \sum_(i <- s | P i) f i <= \sum_(i <- s | P i) g i.
Proof. by move=> Pfg; elim/big_ind2 : _ => // *; exact: leeD. Qed.

Lemma lee_sum_nneg_subset I (s : seq I) (P Q : {pred I}) (f : I -> \bar R) :
  {subset Q <= P} -> {in [predD P & Q], forall i, 0 <= f i} ->
  \sum_(i <- s | Q i) f i <= \sum_(i <- s | P i) f i.
Proof.
move=> QP PQf; rewrite big_mkcond [leRHS]big_mkcond lee_sum// => i.
by move/implyP: (QP i); move: (PQf i); rewrite !inE -!topredE/=; do !case: ifP.
Qed.

Lemma lee_sum_npos_subset I (s : seq I) (P Q : {pred I}) (f : I -> \bar R) :
  {subset Q <= P} -> {in [predD P & Q], forall i, f i <= 0} ->
  \sum_(i <- s | P i) f i <= \sum_(i <- s | Q i) f i.
Proof.
move=> QP PQf; rewrite big_mkcond [leRHS]big_mkcond lee_sum// => i.
by move/implyP: (QP i); move: (PQf i); rewrite !inE -!topredE/=; do !case: ifP.
Qed.

Lemma lee_sum_nneg (I : eqType) (s : seq I) (P Q : pred I)
  (f : I -> \bar R) : (forall i, P i -> ~~ Q i -> 0 <= f i) ->
  \sum_(i <- s | P i && Q i) f i <= \sum_(i <- s | P i) f i.
Proof.
move=> PQf; rewrite [leRHS](bigID Q) /= -[leLHS]adde0 leeD //.
by rewrite sume_ge0// => i /andP[]; exact: PQf.
Qed.

Lemma lee_sum_npos (I : eqType) (s : seq I) (P Q : pred I)
  (f : I -> \bar R) : (forall i, P i -> ~~ Q i -> f i <= 0) ->
  \sum_(i <- s | P i) f i <= \sum_(i <- s | P i && Q i) f i.
Proof.
move=> PQf; rewrite [leLHS](bigID Q) /= -[leRHS]adde0 leeD //.
by rewrite sume_le0// => i /andP[]; exact: PQf.
Qed.

Lemma lee_sum_nneg_ord (f : nat -> \bar R) (P : pred nat) :
  (forall n, P n -> 0 <= f n) ->
  {homo (fun n => \sum_(i < n | P i) (f i)) : i j / (i <= j)%N >-> i <= j}.
Proof.
move=> f0 i j le_ij; rewrite (big_ord_widen_cond j) // big_mkcondr /=.
by rewrite lee_sum // => k ?; case: ifP => // _; exact: f0.
Qed.

Lemma lee_sum_npos_ord (f : nat -> \bar R) (P : pred nat) :
  (forall n, P n -> f n <= 0) ->
  {homo (fun n => \sum_(i < n | P i) (f i)) : i j / (i <= j)%N >-> j <= i}.
Proof.
move=> f0 m n ?; rewrite [leRHS](big_ord_widen_cond n) // big_mkcondr /=.
by rewrite lee_sum // => i ?; case: ifP => // _; exact: f0.
Qed.

Lemma lee_sum_nneg_natr (f : nat -> \bar R) (P : pred nat) m :
  (forall n, (m <= n)%N -> P n -> 0 <= f n) ->
  {homo (fun n => \sum_(m <= i < n | P i) (f i)) : i j / (i <= j)%N >-> i <= j}.
Proof.
move=> f0 i j le_ij; rewrite -[m]add0n !big_addn !big_mkord.
apply: (@lee_sum_nneg_ord (fun k => f (k + m)%N) (fun k => P (k + m)%N));
  by [move=> n /f0; apply; rewrite leq_addl | rewrite leq_sub2r].
Qed.

Lemma lee_sum_npos_natr (f : nat -> \bar R) (P : pred nat) m :
  (forall n, (m <= n)%N -> P n -> f n <= 0) ->
  {homo (fun n => \sum_(m <= i < n | P i) (f i)) : i j / (i <= j)%N >-> j <= i}.
Proof.
move=> f0 i j le_ij; rewrite -[m]add0n !big_addn !big_mkord.
apply: (@lee_sum_npos_ord (fun k => f (k + m)%N) (fun k => P (k + m)%N));
  by [move=> n /f0; apply; rewrite leq_addl | rewrite leq_sub2r].
Qed.

Lemma lee_sum_nneg_natl (f : nat -> \bar R) (P : pred nat) n :
  (forall m, (m < n)%N -> P m -> 0 <= f m) ->
  {homo (fun m => \sum_(m <= i < n | P i) (f i)) : i j / (i <= j)%N >-> j <= i}.
Proof.
move=> f0 i j le_ij; rewrite !big_geq_mkord/=.
rewrite lee_sum_nneg_subset// => [k | k /and3P[_ /f0->//]].
by rewrite ?inE -!topredE/= => /andP[-> /(leq_trans le_ij)->].
Qed.

Lemma lee_sum_npos_natl (f : nat -> \bar R) (P : pred nat) n :
  (forall m, (m < n)%N -> P m -> f m <= 0) ->
  {homo (fun m => \sum_(m <= i < n | P i) (f i)) : i j / (i <= j)%N >-> i <= j}.
Proof.
move=> f0 i j le_ij; rewrite !big_geq_mkord/=.
rewrite lee_sum_npos_subset// => [k | k /and3P[_ /f0->//]].
by rewrite ?inE -!topredE/= => /andP[-> /(leq_trans le_ij)->].
Qed.

Lemma lteBlDr x y z : y \is a fin_num -> (x - y < z) = (x < z + y).
Proof.
move: x y z => [x| |] [y| |] [z| |] _ //=; rewrite ?ltry ?ltNyr //.
by rewrite !lte_fin ltrBlDr.
Qed.

Lemma lteBlDl x y z : y \is a fin_num -> (x - y < z) = (x < y + z).
Proof. by move=> ?; rewrite lteBlDr// addeC. Qed.

Lemma lteBrDr x y z : z \is a fin_num -> (x < y - z) = (x + z < y).
Proof.
move: x y z => [x| |] [y| |] [z| |] _ //=; rewrite ?ltNyr ?ltry //.
by rewrite !lte_fin ltrBrDr.
Qed.

Lemma lteBrDl x y z : z \is a fin_num -> (x < y - z) = (z + x < y).
Proof. by move=> ?; rewrite lteBrDr// addeC. Qed.

Lemma lte_subel_addr x y z : x \is a fin_num -> (x - y < z) = (x < z + y).
Proof.
move: x y z => [x| |] [y| |] [z| |] _ //=; rewrite ?ltNyr ?ltry //.
by rewrite !lte_fin ltrBlDr.
Qed.

Lemma lte_subel_addl x y z : x \is a fin_num -> (x - y < z) = (x < y + z).
Proof. by move=> ?; rewrite lte_subel_addr// addeC. Qed.

Lemma lte_suber_addr x y z : x \is a fin_num -> (x < y - z) = (x + z < y).
Proof.
move: x y z => [x| |] [y| |] [z| |] _ //=; rewrite ?ltNyr ?ltry //.
by rewrite !lte_fin ltrBrDr.
Qed.

Lemma lte_suber_addl x y z : x \is a fin_num -> (x < y - z) = (z + x < y).
Proof. by move=> ?; rewrite lte_suber_addr// addeC. Qed.

Lemma leeBlDr x y z : y \is a fin_num -> (x - y <= z) = (x <= z + y).
Proof.
move: x y z => [x| |] [y| |] [z| |] _ //=; rewrite ?leey ?leNye //.
by rewrite !lee_fin lerBlDr.
Qed.

Lemma leeBlDl x y z : y \is a fin_num -> (x - y <= z) = (x <= y + z).
Proof. by move=> ?; rewrite leeBlDr// addeC. Qed.

Lemma leeBrDr x y z : z \is a fin_num -> (x <= y - z) = (x + z <= y).
Proof.
move: y x z => [y| |] [x| |] [z| |] _ //=; rewrite ?leNye ?leey //.
by rewrite !lee_fin lerBrDr.
Qed.

Lemma leeBrDl x y z : z \is a fin_num -> (x <= y - z) = (z + x <= y).
Proof. by move=> ?; rewrite leeBrDr// addeC. Qed.

Lemma lee_subel_addr x y z : z \is a fin_num -> (x - y <= z) = (x <= z + y).
Proof.
move: x y z => [x| |] [y| |] [z| |] _ //=; rewrite ?leey ?leNye //.
by rewrite !lee_fin lerBlDr.
Qed.

Lemma lee_subel_addl x y z : z \is a fin_num -> (x - y <= z) = (x <= y + z).
Proof. by move=> ?; rewrite lee_subel_addr// addeC. Qed.

Lemma lee_suber_addr x y z : y \is a fin_num -> (x <= y - z) = (x + z <= y).
Proof.
move: y x z => [y| |] [x| |] [z| |] _ //=; rewrite ?leNye ?leey //.
by rewrite !lee_fin lerBrDr.
Qed.

Lemma lee_suber_addl x y z : y \is a fin_num -> (x <= y - z) = (z + x <= y).
Proof. by move=> ?; rewrite lee_suber_addr// addeC. Qed.

Lemma subre_lt0 x y : x \is a fin_num -> (x - y < 0) = (x < y).
Proof. by move=> ?; rewrite lte_subel_addr// add0e. Qed.

Lemma suber_lt0 x y : y \is a fin_num -> (x - y < 0) = (x < y).
Proof. by move=> ?; rewrite lteBlDl// adde0. Qed.

Lemma sube_lt0 x y : (x \is a fin_num) || (y \is a fin_num) ->
  (x - y < 0) = (x < y).
Proof. by move=> /orP[?|?]; [rewrite subre_lt0|rewrite suber_lt0]. Qed.

Lemma pmule_rge0 x y : 0 < x -> (x * y >= 0) = (y >= 0).
Proof.
move=> x_gt0; apply/idP/idP; last exact/mule_ge0/ltW.
by apply: contra_le; apply: mule_gt0_lt0.
Qed.

Lemma pmule_lge0 x y : 0 < x -> (y * x >= 0) = (y >= 0).
Proof. by rewrite muleC; apply: pmule_rge0. Qed.

Lemma pmule_rlt0 x y : 0 < x -> (x * y < 0) = (y < 0).
Proof. by move=> /pmule_rge0; rewrite !ltNge => ->. Qed.

Lemma pmule_llt0 x y : 0 < x -> (y * x < 0) = (y < 0).
Proof. by rewrite muleC; apply: pmule_rlt0. Qed.

Lemma pmule_rle0 x y : 0 < x -> (x * y <= 0) = (y <= 0).
Proof. by move=> xgt0; rewrite -oppe_ge0 -muleN pmule_rge0 ?oppe_ge0. Qed.

Lemma pmule_lle0 x y : 0 < x -> (y * x <= 0) = (y <= 0).
Proof. by rewrite muleC; apply: pmule_rle0. Qed.

Lemma pmule_rgt0 x y : 0 < x -> (x * y > 0) = (y > 0).
Proof. by move=> xgt0; rewrite -oppe_lt0 -muleN pmule_rlt0 ?oppe_lt0. Qed.

Lemma pmule_lgt0 x y : 0 < x -> (y * x > 0) = (y > 0).
Proof. by rewrite muleC; apply: pmule_rgt0. Qed.

Lemma nmule_rge0 x y : x < 0 -> (x * y >= 0) = (y <= 0).
Proof. by rewrite -oppe_gt0 => /pmule_rle0<-; rewrite mulNe oppe_le0. Qed.

Lemma nmule_lge0 x y : x < 0 -> (y * x >= 0) = (y <= 0).
Proof. by rewrite muleC; apply: nmule_rge0. Qed.

Lemma nmule_rle0 x y : x < 0 -> (x * y <= 0) = (y >= 0).
Proof. by rewrite -oppe_gt0 => /pmule_rge0<-; rewrite mulNe oppe_ge0. Qed.

Lemma nmule_lle0 x y : x < 0 -> (y * x <= 0) = (y >= 0).
Proof. by rewrite muleC; apply: nmule_rle0. Qed.

Lemma nmule_rgt0 x y : x < 0 -> (x * y > 0) = (y < 0).
Proof. by rewrite -oppe_gt0 => /pmule_rlt0<-; rewrite mulNe oppe_lt0. Qed.

Lemma nmule_lgt0 x y : x < 0 -> (y * x > 0) = (y < 0).
Proof. by rewrite muleC; apply: nmule_rgt0. Qed.

Lemma nmule_rlt0 x y : x < 0 -> (x * y < 0) = (y > 0).
Proof.
by rewrite -[x < 0]oppe_gt0 => /pmule_rgt0<-; rewrite mulNe oppe_gt0.
Qed.

Lemma nmule_llt0 x y : x < 0 -> (y * x < 0) = (y > 0).
Proof. by rewrite muleC; apply: nmule_rlt0. Qed.

Lemma mule_lt0 x y : (x * y < 0) = [&& x != 0, y != 0 & (x < 0) (+) (y < 0)].
Proof.
have [xlt0|xgt0|->] := ltgtP x 0; last by rewrite mul0e.
  by rewrite nmule_rlt0//= -leNgt lt_def.
by rewrite pmule_rlt0//= !lt_neqAle andbA andbb.
Qed.

Lemma muleA : associative ( *%E : \bar R -> \bar R -> \bar R ).
Proof.
move=> x y z.
wlog x0 : x y z / 0 < x => [hwlog|].
  have [x0| |->] := ltgtP x 0; [ |exact: hwlog|by rewrite !mul0e].
  by apply: oppe_inj; rewrite -!mulNe hwlog ?oppe_gt0.
wlog y0 : x y z x0 / 0 < y => [hwlog|].
  have [y0| |->] := ltgtP y 0; [ |exact: hwlog|by rewrite !(mul0e, mule0)].
  by apply: oppe_inj; rewrite -muleN -2!mulNe -muleN hwlog ?oppe_gt0.
wlog z0 : x y z x0 y0 / 0 < z => [hwlog|].
  have [z0| |->] := ltgtP z 0; [ |exact: hwlog|by rewrite !mule0].
  by apply: oppe_inj; rewrite -!muleN hwlog ?oppe_gt0.
case: x x0 => [x x0| |//]; last by rewrite !gt0_mulye ?mule_gt0.
case: y y0 => [y y0| |//]; last by rewrite gt0_mulye // muleC !gt0_mulye.
case: z z0 => [z z0| |//]; last by rewrite !gt0_muley ?mule_gt0.
by rewrite /mule/= mulrA.
Qed.

Local Open Scope ereal_scope.

HB.instance Definition _ := Monoid.isComLaw.Build (\bar R) 1%E mule
  muleA muleC mul1e.

Lemma muleCA : left_commutative ( *%E : \bar R -> \bar R -> \bar R ).
Proof. exact: Monoid.mulmCA. Qed.

Lemma muleAC : right_commutative ( *%E : \bar R -> \bar R -> \bar R ).
Proof. exact: Monoid.mulmAC. Qed.

Lemma muleACA : interchange (@mule R) (@mule R).
Proof. exact: Monoid.mulmACA. Qed.

Lemma muleDr x y z : x \is a fin_num -> y +? z -> x * (y + z) = x * y + x * z.
Proof.
rewrite /mule/=; move: x y z => [x| |] [y| |] [z| |] //= _; try
  (by case: ltgtP => // -[] <-; rewrite ?(mul0r,add0r,adde0))
  || (by case: ltgtP => //; rewrite adde0).
by rewrite mulrDr.
Qed.

Lemma muleDl x y z : x \is a fin_num -> y +? z -> (y + z) * x = y * x + z * x.
Proof. by move=> ? ?; rewrite -!(muleC x) muleDr. Qed.

Lemma muleBr x y z : x \is a fin_num -> y +? - z -> x * (y - z) = x * y - x * z.
Proof. by move=> ? yz; rewrite muleDr ?muleN. Qed.

Lemma muleBl x y z : x \is a fin_num -> y +? - z -> (y - z) * x = y * x - z * x.
Proof. by move=> ? yz; rewrite muleDl// mulNe. Qed.

Lemma ge0_muleDl x y z : 0 <= y -> 0 <= z -> (y + z) * x = y * x + z * x.
Proof.
rewrite /mule/=; move: x y z => [r| |] [s| |] [t| |] //= s0 t0.
- by rewrite mulrDl.
- by case: ltgtP => // -[] <-; rewrite mulr0 adde0.
- by case: ltgtP => // -[] <-; rewrite mulr0 adde0.
- by case: ltgtP => //; rewrite adde0.
- rewrite !eqe paddr_eq0 //; move: s0; rewrite lee_fin.
  case: (ltgtP s) => //= [s0|->{s}] _; rewrite ?add0e.
  + rewrite lte_fin -[in LHS](addr0 0%R) ltr_leD // lte_fin s0.
    by case: ltgtP t0 => // [t0|[<-{t}]] _; [rewrite gt_eqF|rewrite eqxx].
  + by move: t0; rewrite lee_fin; case: (ltgtP t).
- by rewrite ltry; case: ltgtP s0.
- by rewrite ltry; case: ltgtP t0.
- by rewrite ltry.
- rewrite !eqe paddr_eq0 //; move: s0; rewrite lee_fin.
  case: (ltgtP s) => //= [s0|->{s}] _; rewrite ?add0e.
  + rewrite lte_fin -[in LHS](addr0 0%R) ltr_leD // lte_fin s0.
    by case: ltgtP t0 => // [t0|[<-{t}]].
  + by move: t0; rewrite lee_fin; case: (ltgtP t).
- by rewrite ltry; case: ltgtP s0.
- by rewrite ltry; case: ltgtP s0.
- by rewrite ltry; case: ltgtP s0.
Qed.

Lemma ge0_muleDr x y z : 0 <= y -> 0 <= z -> x * (y + z) = x * y + x * z.
Proof. by move=> y0 z0; rewrite !(muleC x) ge0_muleDl. Qed.

Lemma le0_muleDl x y z : y <= 0 -> z <= 0 -> (y + z) * x = y * x + z * x.
Proof.
rewrite /mule/=; move: x y z => [r| |] [s| |] [t| |] //= s0 t0.
- by rewrite mulrDl.
- by case: ltgtP => // -[] <-; rewrite mulr0 adde0.
- by case: ltgtP => // -[] <-; rewrite mulr0 adde0.
- by case: ltgtP => //; rewrite adde0.
- rewrite !eqe naddr_eq0 //; move: s0; rewrite lee_fin.
  case: (ltgtP s) => //= [s0|->{s}] _; rewrite ?add0e.
  + rewrite !lte_fin -[in LHS](addr0 0%R) ltNge lerD // ?ltW //=.
    by rewrite !ltNge ltW //.
  + by case: (ltgtP t).
- by rewrite ltry; case: ltgtP s0.
- by rewrite ltry; case: ltgtP t0.
- by rewrite ltry.
- rewrite !eqe naddr_eq0 //; move: s0; rewrite lee_fin.
  case: (ltgtP s) => //= [s0|->{s}] _; rewrite ?add0e.
  + rewrite !lte_fin -[in LHS](addr0 0%R) ltNge lerD // ?ltW //=.
    by rewrite !ltNge ltW // -lee_fin t0; case: eqP.
  + by case: (ltgtP t).
- by rewrite ltNge s0 /=; case: eqP.
- by rewrite ltNge t0 /=; case: eqP.
Qed.

Lemma le0_muleDr x y z : y <= 0 -> z <= 0 -> x * (y + z) = x * y + x * z.
Proof. by move=> y0 z0; rewrite !(muleC x) le0_muleDl. Qed.

Lemma gee_pMl y x : y \is a fin_num -> 0 <= x -> y <= 1 -> y * x <= x.
Proof.
move=> yfin; rewrite le_eqVlt => /predU1P[<-|]; first by rewrite mule0.
move: x y yfin => [x| |] [y| |] //= _.
- by rewrite lte_fin => x0 y1; rewrite lee_fin ger_pMl.
- by move=> _; rewrite /mule/= eqe => r1; rewrite leey.
Qed.

Lemma lee_wpmul2r x : 0 <= x -> {homo *%E^~ x : y z / y <= z}.
Proof.
move: x => [x|_|//].
  rewrite lee_fin le_eqVlt => /predU1P[<- y z|x0]; first by rewrite 2!mule0.
  move=> [y| |] [z| |]//; first by rewrite !lee_fin// ler_pM2r.
  - by move=> _; rewrite mulr_infty gtr0_sg// mul1e leey.
  - by move=> _; rewrite mulr_infty gtr0_sg// mul1e leNye.
  - by move=> _; rewrite 2!mulr_infty gtr0_sg// 2!mul1e.
move=> [y| |] [z| |]//.
- rewrite lee_fin => yz.
  have [z0|z0|] := ltgtP 0%R z.
  + by rewrite [leRHS]mulr_infty gtr0_sg// mul1e leey.
  + by rewrite mulr_infty ltr0_sg// ?(le_lt_trans yz)// [leRHS]mulr_infty ltr0_sg.
  + move=> z0; move: yz; rewrite -z0 mul0e le_eqVlt => /predU1P[->|y0].
      by rewrite mul0e.
    by rewrite mulr_infty ltr0_sg// mulN1e leNye.
  + by move=> _; rewrite mulyy leey.
  + by move=> _; rewrite mulNyy leNye.
  + by move=> _; rewrite mulNyy leNye.
Qed.

Lemma lee_wpmul2l x : 0 <= x -> {homo *%E x : y z / y <= z}.
Proof. by move=> x0 y z yz; rewrite !(muleC x) lee_wpmul2r. Qed.

Lemma ge0_sume_distrl (I : Type) (s : seq I) x (P : pred I) (F : I -> \bar R) :
  (forall i, P i -> 0 <= F i) ->
  (\sum_(i <- s | P i) F i) * x = \sum_(i <- s | P i) (F i * x).
Proof.
elim: s x P F => [x P F F0|h t ih x P F F0]; first by rewrite 2!big_nil mul0e.
rewrite big_cons; case: ifPn => Ph; last by rewrite big_cons (negbTE Ph) ih.
by rewrite ge0_muleDl ?sume_ge0// ?F0// ih// big_cons Ph.
Qed.

Lemma ge0_sume_distrr (I : Type) (s : seq I) x (P : pred I) (F : I -> \bar R) :
  (forall i, P i -> 0 <= F i) ->
  x * (\sum_(i <- s | P i) F i) = \sum_(i <- s | P i) (x * F i).
Proof.
by move=> F0; rewrite muleC ge0_sume_distrl//; under eq_bigr do rewrite muleC.
Qed.

Lemma le0_sume_distrl (I : Type) (s : seq I) x (P : pred I) (F : I -> \bar R) :
  (forall i, P i -> F i <= 0) ->
  (\sum_(i <- s | P i) F i) * x = \sum_(i <- s | P i) (F i * x).
Proof.
elim: s x P F => [x P F F0|h t ih x P F F0]; first by rewrite 2!big_nil mul0e.
rewrite big_cons; case: ifPn => Ph; last by rewrite big_cons (negbTE Ph) ih.
by rewrite le0_muleDl ?sume_le0// ?F0// ih// big_cons Ph.
Qed.

Lemma le0_sume_distrr (I : Type) (s : seq I) x (P : pred I) (F : I -> \bar R) :
  (forall i, P i -> F i <= 0) ->
  x * (\sum_(i <- s | P i) F i) = \sum_(i <- s | P i) (x * F i).
Proof.
by move=> F0; rewrite muleC le0_sume_distrl//; under eq_bigr do rewrite muleC.
Qed.

Lemma fin_num_sume_distrr (I : Type) (s : seq I) x (P : pred I)
    (F : I -> \bar R) :
  x \is a fin_num -> {in P &, forall i j, F i +? F j} ->
    x * (\sum_(i <- s | P i) F i) = \sum_(i <- s | P i) x * F i.
Proof.
move=> xfin PF; elim: s => [|h t ih]; first by rewrite !big_nil mule0.
rewrite !big_cons; case: ifPn => Ph //.
by rewrite muleDr// ?ih// adde_def_sum// => i Pi; rewrite PF.
Qed.

Lemma eq_infty x : (forall r, r%:E <= x) -> x = +oo.
Proof.
case: x => [x /(_ (x + 1)%R)|//|/(_ 0%R)//].
by rewrite EFinD addeC -leeBrDr// subee// lee_fin ler10.
Qed.

Lemma eq_ninfty x : (forall r, x <= r%:E) -> x = -oo.
Proof.
move=> *; apply: (can_inj oppeK); apply: eq_infty => r.
by rewrite leeNr -EFinN.
Qed.

Lemma lee_abs x : x <= `|x|.
Proof. by move: x => [x| |]//=; rewrite lee_fin ler_norm. Qed.

Lemma abse_id x : `| `|x| | = `|x|.
Proof. by move: x => [x| |] //=; rewrite normr_id. Qed.

Lemma lte_absl (x y : \bar R) : (`|x| < y)%E = (- y < x < y)%E.
Proof.
by move: x y => [x| |] [y| |] //=; rewrite ?lte_fin ?ltry ?ltNyr// ltr_norml.
Qed.

Lemma eqe_absl x y : (`|x| == y) = ((x == y) || (x == - y)) && (0 <= y).
Proof.
by move: x y => [x| |] [y| |] //=; rewrite? leey// !eqe eqr_norml lee_fin.
Qed.

Lemma lee_abs_add x y : `|x + y| <= `|x| + `|y|.
Proof.
by move: x y => [x| |] [y| |] //; rewrite /abse -EFinD lee_fin ler_normD.
Qed.

Lemma lee_abs_sum (I : Type) (s : seq I) (F : I -> \bar R) (P : pred I) :
  `|\sum_(i <- s | P i) F i| <= \sum_(i <- s | P i) `|F i|.
Proof.
elim/big_ind2 : _ => //; first by rewrite abse0.
by move=> *; exact/(le_trans (lee_abs_add _ _) (leeD _ _)).
Qed.

Lemma lee_abs_sub x y : `|x - y| <= `|x| + `|y|.
Proof.
by move: x y => [x| |] [y| |] //; rewrite /abse -EFinD lee_fin ler_normB.
Qed.

Lemma abseM : {morph @abse R : x y / x * y}.
Proof.
have xoo r : `|r%:E * +oo| = `|r|%:E * +oo.
  have [r0|r0] := leP 0%R r.
    by rewrite (ger0_norm r0)// gee0_abs// mule_ge0// leey.
  rewrite (ltr0_norm r0)// lte0_abs// ?EFinN ?mulNe//.
  by rewrite mule_lt0 /= eqe lt_eqF//= lte_fin r0.
move=> [x| |] [y| |] //=; first by rewrite normrM.
- by rewrite -abseN -muleNN abseN -EFinN xoo normrN.
- by rewrite muleC xoo muleC.
- by rewrite mulyy.
- by rewrite mulyy mulyNy.
- by rewrite -abseN -muleNN abseN -EFinN xoo normrN.
- by rewrite mulyy mulNyy.
- by rewrite mulyy.
Qed.

Lemma fine_max :
  {in fin_num &, {mono @fine R : x y / maxe x y >-> (Num.max x y)%:E}}.
Proof.
by move=> [x| |] [y| |]//= _ _; apply/esym; have [ab|ba] := leP x y;
  [apply/max_idPr; rewrite lee_fin|apply/max_idPl; rewrite lee_fin ltW].
Qed.

Lemma fine_min :
  {in fin_num &, {mono @fine R : x y / mine x y >-> (Num.min x y)%:E}}.
Proof.
by move=> [x| |] [y| |]//= _ _; apply/esym; have [ab|ba] := leP x y;
  [apply/min_idPl; rewrite lee_fin|apply/min_idPr; rewrite lee_fin ltW].
Qed.

Lemma adde_maxl : left_distributive (@GRing.add (\bar R)) maxe.
Proof.
move=> x y z; have [xy|yx] := leP x y.
  by apply/esym/max_idPr; rewrite leeD2r.
by apply/esym/max_idPl; rewrite leeD2r// ltW.
Qed.

Lemma adde_maxr : right_distributive (@GRing.add (\bar R)) maxe.
Proof.
move=> x y z; have [yz|zy] := leP y z.
  by apply/esym/max_idPr; rewrite leeD2l.
by apply/esym/max_idPl; rewrite leeD2l// ltW.
Qed.

Lemma maxey : right_zero (+oo : \bar R) maxe.
Proof. by move=> x; rewrite maxC maxye. Qed.

Lemma maxNye : left_id (-oo : \bar R) maxe.
Proof. by move=> x; have [//|] := leP -oo x; rewrite ltNge leNye. Qed.

HB.instance Definition _ :=
  Monoid.isLaw.Build (\bar R) -oo maxe maxA maxNye maxeNy.

Lemma minNye : left_zero (-oo : \bar R) mine.
Proof. by move=> x; have [|//] := leP x -oo; rewrite leeNy_eq => /eqP. Qed.

Lemma miney : right_id (+oo : \bar R) mine.
Proof. by move=> x; rewrite minC minye. Qed.

Lemma oppe_max : {morph -%E : x y / maxe x y >-> mine x y : \bar R}.
Proof.
move=> [x| |] [y| |] //=.
- by rewrite -fine_max//= -fine_min//= oppr_max.
- by rewrite maxey mineNy.
- by rewrite miney.
- by rewrite minNye.
- by rewrite maxNye minye.
Qed.

Lemma oppe_min : {morph -%E : x y / mine x y >-> maxe x y : \bar R}.
Proof. by move=> x y; rewrite -[RHS]oppeK oppe_max !oppeK. Qed.

Lemma maxe_pMr z x y : z \is a fin_num -> 0 <= z ->
  z * maxe x y = maxe (z * x) (z * y).
Proof.
move=> /[swap]; rewrite le_eqVlt => /predU1P[<- _|z0].
  by rewrite !mul0e maxxx.
have [xy|yx|->] := ltgtP x y; last by rewrite maxxx.
- by move=> zfin; rewrite /maxe lte_pmul2l // xy.
- by move=> zfin; rewrite maxC /maxe lte_pmul2l// yx.
Qed.

Lemma maxe_pMl z x y : z \is a fin_num -> 0 <= z ->
  maxe x y * z = maxe (x * z) (y * z).
Proof. by move=> zfin z0; rewrite muleC maxe_pMr// !(muleC z). Qed.

Lemma mine_pMr z x y : z \is a fin_num -> 0 <= z ->
  z * mine x y = mine (z * x) (z * y).
Proof.
move=> fz zge0.
by rewrite -eqe_oppP -muleN [in LHS]oppe_min maxe_pMr// !muleN -oppe_min.
Qed.

Lemma mine_pMl z x y : z \is a fin_num -> 0 <= z ->
  mine x y * z = mine (x * z) (y * z).
Proof. by move=> zfin z0; rewrite muleC mine_pMr// !(muleC z). Qed.

Lemma bigmaxe_fin_num (s : seq R) r : r \in s ->
  \big[maxe/-oo%E]_(i <- s) i%:E \is a fin_num.
Proof.
move=> rs; have {rs} : s != [::].
  by rewrite -size_eq0 -lt0n -has_predT; apply/hasP; exists r.
elim: s => [//|a l]; have [-> _ _|_ /(_ isT) ih _] := eqVneq l [::].
  by rewrite big_seq1.
by rewrite big_cons {1}/maxe;  case: (_ < _)%E.
Qed.

Lemma lee_pemull x y : 0 <= y -> 1 <= x -> y <= x * y.
Proof.
move: x y => [x| |] [y| |] //; last by rewrite mulyy.
- by rewrite -EFinM 3!lee_fin; exact: ler_peMl.
- move=> _; rewrite lee_fin => x1.
  by rewrite mulr_infty gtr0_sg ?mul1e// (lt_le_trans _ x1).
- rewrite lee_fin le_eqVlt => /predU1P[<- _|y0 _]; first by rewrite mule0.
  by rewrite mulr_infty gtr0_sg// mul1e leey.
Qed.

Lemma lee_nemull x y : y <= 0 -> 1 <= x -> x * y <= y.
Proof.
move: x y => [x| |] [y| |] //; last by rewrite mulyNy.
- by rewrite -EFinM 3!lee_fin; exact: ler_neMl.
- move=> _; rewrite lee_fin => x1.
  by rewrite mulr_infty gtr0_sg ?mul1e// (lt_le_trans _ x1).
- rewrite lee_fin le_eqVlt => /predU1P[-> _|y0 _]; first by rewrite mule0.
  by rewrite mulr_infty ltr0_sg// mulN1e leNye.
Qed.

Lemma lee_pemulr x y : 0 <= y -> 1 <= x -> y <= y * x.
Proof. by move=> y0 x1; rewrite muleC lee_pemull. Qed.

Lemma lee_nemulr x y : y <= 0 -> 1 <= x -> y * x <= y.
Proof. by move=> y0 x1; rewrite muleC lee_nemull. Qed.

Lemma mule_natl x n : n%:R%:E * x = x *+ n.
Proof.
elim: n => [|n]; first by rewrite mul0e.
move: x => [x| |] ih.
- by rewrite -EFinM mulr_natl EFin_natmul.
- by rewrite mulry gtr0_sg// mul1e enatmul_pinfty.
- by rewrite mulrNy gtr0_sg// mul1e enatmul_ninfty.
Qed.

Lemma lte_pmul x1 y1 x2 y2 :
  0 <= x1 -> 0 <= x2 -> x1 < y1 -> x2 < y2 -> x1 * x2 < y1 * y2.
Proof.
move: x1 y1 x2 y2 => [x1| |] [y1| |] [x2| |] [y2| |] //;
    rewrite !(lte_fin,lee_fin).
- by move=> *; rewrite ltr_pM.
- move=> x10 x20 xy1 xy2.
  by rewrite mulry gtr0_sg ?mul1e -?EFinM ?ltry// (le_lt_trans _ xy1).
- move=> x10 x20 xy1 xy2.
  by rewrite mulyr gtr0_sg ?mul1e -?EFinM ?ltry// (le_lt_trans _ xy2).
- by move=> *; rewrite mulyy -EFinM ltry.
Qed.

Lemma lee_pmul x1 y1 x2 y2 : 0 <= x1 -> 0 <= x2 -> x1 <= y1 -> x2 <= y2 ->
  x1 * x2 <= y1 * y2.
Proof.
move: x1 y1 x2 y2 => [x1| |] [y1| |] [x2| |] [y2| |] //; rewrite !lee_fin.
- exact: ler_pM.
- rewrite le_eqVlt => /predU1P[<- x20 y10 _|x10 x20 xy1 _].
    by rewrite mul0e mule_ge0// leey.
  by rewrite mulr_infty gtr0_sg// ?mul1e ?leey// (lt_le_trans x10).
- rewrite le_eqVlt => /predU1P[<- _ y10 _|x10 _ xy1 _].
    by rewrite mul0e mule_ge0// leey.
  rewrite mulr_infty gtr0_sg// mul1e mulr_infty gtr0_sg// ?mul1e//.
  exact: (lt_le_trans x10).
- move=> x10; rewrite le_eqVlt => /predU1P[<- _ y20|x20 _ xy2].
    by rewrite mule0 mulr_infty mule_ge0// ?leey// lee_fin sgr_ge0.
  by rewrite mulr_infty gtr0_sg ?mul1e ?leey// (lt_le_trans x20).
- by move=> x10 x20 _ _; rewrite mulyy leey.
- rewrite le_eqVlt => /predU1P[<- _ _ _|x10 _ _ _].
    by rewrite mulyy mul0e leey.
  by rewrite mulyy mulr_infty gtr0_sg// mul1e.
- move=> _; rewrite le_eqVlt => /predU1P[<- _ y20|x20 _ xy2].
    by rewrite mule0 mulr_infty mule_ge0// ?leey// lee_fin sgr_ge0.
  rewrite mulr_infty gtr0_sg// mul1e mulr_infty gtr0_sg ?mul1e//.
  exact: (lt_le_trans x20).
- move=> _; rewrite le_eqVlt => /predU1P[<- _ _|x20 _ _].
    by rewrite mule0 mulyy leey.
  by rewrite mulr_infty gtr0_sg// mul1e// mulyy.
Qed.

Lemma lee_pmul2l x : x \is a fin_num -> 0 < x -> {mono *%E x : x y / x <= y}.
Proof.
move: x => [x _|//|//] /[!(@lte_fin R)] x0 [y| |] [z| |].
- by rewrite -2!EFinM 2!lee_fin ler_pM2l.
- by rewrite mulry gtr0_sg// mul1e 2!leey.
- by rewrite mulrNy gtr0_sg// mul1e 2!leeNy_eq.
- by rewrite mulry gtr0_sg// mul1e 2!leye_eq.
- by rewrite mulry gtr0_sg// mul1e.
- by rewrite mulry mulrNy gtr0_sg// mul1e mul1e.
- by rewrite mulrNy gtr0_sg// mul1e 2!leNye.
- by rewrite mulrNy mulry gtr0_sg// 2!mul1e.
- by rewrite mulrNy gtr0_sg// mul1e.
Qed.

Lemma lee_pmul2r x : x \is a fin_num -> 0 < x -> {mono *%E^~ x : x y / x <= y}.
Proof. by move=> xfin x0 y z; rewrite -2!(muleC x) lee_pmul2l. Qed.

Lemma lee_sqr x y : 0 <= x -> 0 <= y -> (x ^+ 2 <= y ^+ 2) = (x <= y).
Proof.
move=> xge0 yge0; apply/idP/idP; rewrite !expe2.
  by apply: contra_le => yltx; apply: lte_pmul.
by move=> xley; apply: lee_pmul.
Qed.

Lemma lte_sqr x y : 0 <= x -> 0 <= y -> (x ^+ 2 < y ^+ 2) = (x < y).
Proof.
move=> xge0 yge0; apply/idP/idP; rewrite !expe2.
  by apply: contra_lt => yltx; apply: lee_pmul.
by move=> xley; apply: lte_pmul.
Qed.

Lemma lee_sqrE x y : 0 <= y -> x ^+ 2 <= y ^+ 2 -> x <= y.
Proof.
move=> yge0; have [xge0|xlt0 x2ley2] := leP 0 x; first by rewrite lee_sqr.
exact: le_trans (ltW xlt0) _.
Qed.

Lemma lte_sqrE x y : 0 <= y -> x ^+ 2 < y ^+ 2 -> x < y.
Proof.
move=> yge0; have [xge0|xlt0 x2ley2] := leP 0 x; first by rewrite lte_sqr.
exact: lt_le_trans xlt0 _.
Qed.

Lemma sqre_ge0 x : 0 <= x ^+ 2.
Proof.
by case: x => [x||]; rewrite /= ?mulyy ?mulNyNy ?le0y//; apply: sqr_ge0.
Qed.

Lemma lee_paddl y x z : 0 <= x -> y <= z -> y <= x + z.
Proof. by move=> *; rewrite -[y]add0e leeD. Qed.

Lemma lte_paddl y x z : 0 <= x -> y < z -> y < x + z.
Proof. by move=> x0 /lt_le_trans; apply; rewrite lee_paddl. Qed.

Lemma lee_paddr y x z : 0 <= x -> y <= z -> y <= z + x.
Proof. by move=> *; rewrite addeC lee_paddl. Qed.

Lemma lte_paddr y x z : 0 <= x -> y < z -> y < z + x.
Proof. by move=> *; rewrite addeC lte_paddl. Qed.

Lemma lte_spaddre z x y : z \is a fin_num -> 0 < y -> z <= x -> z < x + y.
Proof.
move: z y x => [z| |] [y| |] [x| |] _ //=; rewrite ?(lte_fin,ltry)//.
exact: ltr_pwDr.
Qed.

Lemma lte_spadder z x y : x \is a fin_num -> 0 < y -> z <= x -> z < x + y.
Proof.
move: z y x => [z| |] [y| |] [x| |] _ //=; rewrite ?(lte_fin,ltry,ltNyr)//.
exact: ltr_pwDr.
Qed.

End ERealArithTh_realDomainType.
Arguments lee_sum_nneg_ord {R}.
Arguments lee_sum_npos_ord {R}.
Arguments lee_sum_nneg_natr {R}.
Arguments lee_sum_npos_natr {R}.
Arguments lee_sum_nneg_natl {R}.
Arguments lee_sum_npos_natl {R}.
#[global] Hint Extern 0 (is_true (0 <= `| _ |)%E) => solve [apply: abse_ge0] : core.

#[deprecated(since="mathcomp-analysis 1.1.0", note="Use leeDl instead.")]
Notation lee_addl := leeDl (only parsing).
#[deprecated(since="mathcomp-analysis 1.1.0", note="Use leeDr instead.")]
Notation lee_addr := leeDr (only parsing).
#[deprecated(since="mathcomp-analysis 1.1.0", note="Use leeD2l instead.")]
Notation lee_add2l := leeD2l (only parsing).
#[deprecated(since="mathcomp-analysis 1.1.0", note="Use leeD2r instead.")]
Notation lee_add2r := leeD2r (only parsing).
#[deprecated(since="mathcomp-analysis 1.1.0", note="Use leeD instead.")]
Notation lee_add := leeD (only parsing).
#[deprecated(since="mathcomp-analysis 1.1.0", note="Use leeB instead.")]
Notation lee_sub := leeB (only parsing).
#[deprecated(since="mathcomp-analysis 1.1.0", note="Use leeD2lE instead.")]
Notation lee_add2lE := leeD2lE (only parsing).
#[deprecated(since="mathcomp-analysis 1.1.0", note="Use leeNl instead.")]
Notation lee_oppl := leeNl (only parsing).
#[deprecated(since="mathcomp-analysis 1.1.0", note="Use leeNr instead.")]
Notation lee_oppr := leeNr (only parsing).
#[deprecated(since="mathcomp-analysis 1.1.0", note="Use lteNl instead.")]
Notation lte_oppl := lteNl (only parsing).
#[deprecated(since="mathcomp-analysis 1.1.0", note="Use lteNr instead.")]
Notation lte_oppr := lteNr (only parsing).
#[deprecated(since="mathcomp-analysis 1.1.0", note="Use lteD instead.")]
Notation lte_add := lteD (only parsing).
#[deprecated(since="mathcomp-analysis 1.1.0", note="Use lteD2lE instead.")]
Notation lte_add2lE := lteD2lE (only parsing).
#[deprecated(since="mathcomp-analysis 1.1.0", note="Use lteDl instead.")]
Notation lte_addl := lteDl (only parsing).
#[deprecated(since="mathcomp-analysis 1.1.0", note="Use lteDr instead.")]
Notation lte_addr := lteDr (only parsing).
#[deprecated(since="mathcomp-analysis 1.2.0", note="Use gee_pMl instead.")]
Notation gee_pmull := gee_pMl (only parsing).
#[deprecated(since="mathcomp-analysis 1.2.0", note="Use geeDl instead.")]
Notation gee_addl := geeDl (only parsing).
#[deprecated(since="mathcomp-analysis 1.2.0", note="Use geeDr instead.")]
Notation gee_addr := geeDr (only parsing).
#[deprecated(since="mathcomp-analysis 1.2.0", note="Use gteDr instead.")]
Notation gte_addr := gteDr (only parsing).
#[deprecated(since="mathcomp-analysis 1.2.0", note="Use gteDl instead.")]
Notation gte_addl := gteDl (only parsing).
#[deprecated(since="mathcomp-analysis 1.2.0", note="Use lteBlDr instead.")]
Notation lte_subl_addr := lteBlDr (only parsing).
#[deprecated(since="mathcomp-analysis 1.2.0", note="Use lteBlDl instead.")]
Notation lte_subl_addl := lteBlDl (only parsing).
#[deprecated(since="mathcomp-analysis 1.2.0", note="Use lteBrDr instead.")]
Notation lte_subr_addr := lteBrDr (only parsing).
#[deprecated(since="mathcomp-analysis 1.2.0", note="Use lteBrDl instead.")]
Notation lte_subr_addl := lteBrDl (only parsing).
#[deprecated(since="mathcomp-analysis 1.2.0", note="Use leeBlDr instead.")]
Notation lee_subl_addr := leeBlDr (only parsing).
#[deprecated(since="mathcomp-analysis 1.2.0", note="Use leeBlDl instead.")]
Notation lee_subl_addl := leeBlDl (only parsing).
#[deprecated(since="mathcomp-analysis 1.2.0", note="Use leeBrDr instead.")]
Notation lee_subr_addr := leeBrDr (only parsing).
#[deprecated(since="mathcomp-analysis 1.2.0", note="Use leeBrDl instead.")]
Notation lee_subr_addl := leeBrDl (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="Use `lte_leD` instead.")]
Notation lte_le_add := lte_leD (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="Use `lee_ltD` instead.")]
Notation lee_lt_add := lee_ltD (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="Use `lte_leB` instead.")]
Notation lte_le_sub := lte_leB (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="Use leeN2 instead.")]
Notation lee_opp2 := leeN2 (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="Use lteN2 instead.")]
Notation lte_opp2 := lteN2 (only parsing).
#[deprecated(since="mathcomp-analysis 1.8.0", note="renamed to maxe_pMr")]
Notation maxeMr := maxe_pMr (only parsing).
#[deprecated(since="mathcomp-analysis 1.8.0", note="renamed to maxe_pMl")]
Notation maxeMl := maxe_pMl (only parsing).
#[deprecated(since="mathcomp-analysis 1.8.0", note="renamed to mine_pMr")]
Notation mineMr := mine_pMr (only parsing).
#[deprecated(since="mathcomp-analysis 1.8.0", note="renamed to mine_pMl")]
Notation mineMl := mine_pMl (only parsing).

Module DualAddTheoryRealDomain.

Section DualERealArithTh_realDomainType.

Import DualAddTheoryNumDomain.

Local Open Scope ereal_dual_scope.

Context {R : realDomainType}.
Implicit Types x y z a b : \bar^d R.

Lemma dsube_lt0 x y : (x - y < 0) = (x < y).
Proof. by rewrite dual_addeE oppe_lt0 sube_gt0 lteN2. Qed.

Lemma dsube_ge0 x y : (0 <= y - x) = (x <= y).
Proof. by rewrite dual_addeE oppe_ge0 sube_le0 leeN2. Qed.

Lemma dsuber_le0 x y : y \is a fin_num -> (x - y <= 0) = (x <= y).
Proof.
by move=> ?; rewrite dual_addeE oppe_le0 suber_ge0 ?fin_numN// leeN2.
Qed.

Lemma dsubre_le0 y x : y \is a fin_num -> (y - x <= 0) = (y <= x).
Proof.
by move=> ?; rewrite dual_addeE oppe_le0 subre_ge0 ?fin_numN// leeN2.
Qed.

Lemma dsube_le0 x y : (x \is a fin_num) || (y \is a fin_num) ->
  (y - x <= 0) = (y <= x).
Proof. by move=> /orP[?|?]; [rewrite dsuber_le0|rewrite dsubre_le0]. Qed.

Lemma lte_dD a b x y : a < b -> x < y -> a + x < b + y.
Proof. by rewrite !dual_addeE lteN2 -(lteN2 b) -(lteN2 y); exact: lteD. Qed.

Lemma lee_dDl x y : 0 <= y -> x <= x + y.
Proof. rewrite dual_addeE leeNr -oppe_le0; exact: geeDl. Qed.

Lemma lee_dDr x y : 0 <= y -> x <= y + x.
Proof. rewrite dual_addeE leeNr -oppe_le0; exact: geeDr. Qed.

Lemma gee_dDl x y : y <= 0 -> x + y <= x.
Proof. rewrite dual_addeE leeNl -oppe_ge0; exact: leeDl. Qed.

Lemma gee_dDr x y : y <= 0 -> y + x <= x.
Proof. rewrite dual_addeE leeNl -oppe_ge0; exact: leeDr. Qed.

Lemma lte_dDl y x : y \is a fin_num -> (y < y + x) = (0 < x).
Proof. by rewrite -fin_numN dual_addeE lteNr; exact: gte_subl. Qed.

Lemma lte_dDr y x : y \is a fin_num -> (y < x + y) = (0 < x).
Proof. by rewrite -fin_numN dual_addeE lteNr addeC; exact: gte_subl. Qed.

Lemma gte_dBl y x : y \is a fin_num -> (y - x < y) = (0 < x).
Proof. by rewrite -fin_numN dual_addeE lteNl oppeK; exact: lteDl. Qed.

Lemma gte_dBr y x : y \is a fin_num -> (- x + y < y) = (0 < x).
Proof. by rewrite -fin_numN dual_addeE lteNl oppeK; exact: lteDr. Qed.

Lemma gte_dDl x y : x \is a fin_num -> (x + y < x) = (y < 0).
Proof.
by rewrite -fin_numN dual_addeE lteNl -[0]oppe0 lteNr; exact: lteDl.
Qed.

Lemma gte_dDr x y : x \is a fin_num -> (y + x < x) = (y < 0).
Proof. by rewrite daddeC; exact: gte_dDl. Qed.

Lemma lte_dD2lE x a b : x \is a fin_num -> (x + a < x + b) = (a < b).
Proof. by move=> ?; rewrite !dual_addeE lteN2 lteD2lE ?fin_numN// lteN2. Qed.

Lemma lte_dD2rE x a b : x \is a fin_num -> (a + x < b + x) = (a < b).
Proof.
move=> ?; rewrite !dual_addeE lteN2 -[RHS]lteN2.
by rewrite -[RHS](@lteD2rE _ (- x))// fin_numN.
Qed.

Lemma lee_dD2rE x a b : x \is a fin_num -> (a + x <= b + x) = (a <= b).
Proof.
move=> ?; rewrite !dual_addeE leeN2 -[RHS]leeN2.
by rewrite -[RHS](@leeD2rE _ (- x))// fin_numN.
Qed.

Lemma lee_dD2l x a b : a <= b -> x + a <= x + b.
Proof. rewrite !dual_addeE leeN2 -(leeN2 b); exact: leeD2l. Qed.

Lemma lee_dD2lE x a b : x \is a fin_num -> (x + a <= x + b) = (a <= b).
Proof. by move=> ?; rewrite !dual_addeE leeN2 leeD2lE ?fin_numN// leeN2. Qed.

Lemma lee_dD2r x a b : a <= b -> a + x <= b + x.
Proof. rewrite !dual_addeE leeN2 -(leeN2 b); exact: leeD2r. Qed.

Lemma lee_dD a b x y : a <= b -> x <= y -> a + x <= b + y.
Proof. rewrite !dual_addeE leeN2 -(leeN2 b) -(leeN2 y); exact: leeD. Qed.

Lemma lte_le_dD a b x y : b \is a fin_num -> a < x -> b <= y -> a + b < x + y.
Proof. by rewrite !dual_addeE lteN2 -(lteN2 x); exact: lte_leB. Qed.

Lemma lee_lt_dD a b x y : a \is a fin_num -> a <= x -> b < y -> a + b < x + y.
Proof. by move=> afin xa yb; rewrite (daddeC a) (daddeC x) lte_le_dD. Qed.

Lemma lee_dB x y z t : x <= y -> t <= z -> x - z <= y - t.
Proof. rewrite !dual_addeE leeNl oppeK -leeN2 !oppeK; exact: leeD. Qed.

Lemma lte_le_dB z u x y : u \is a fin_num -> x < z -> u <= y -> x - y < z - u.
Proof. by rewrite !dual_addeE lteN2 !oppeK -(lteN2 z); exact: lte_leD. Qed.

Lemma lee_dsum I (f g : I -> \bar^d R) s (P : pred I) :
  (forall i, P i -> f i <= g i) ->
  \sum_(i <- s | P i) f i <= \sum_(i <- s | P i) g i.
Proof.
move=> Pfg; rewrite !dual_sumeE leeN2.
apply: lee_sum => i Pi; rewrite leeN2; exact: Pfg.
Qed.

Lemma lee_dsum_nneg_subset I (s : seq I) (P Q : {pred I}) (f : I -> \bar^d R) :
  {subset Q <= P} -> {in [predD P & Q], forall i, 0 <= f i} ->
  \sum_(i <- s | Q i) f i <= \sum_(i <- s | P i) f i.
Proof.
move=> QP PQf; rewrite !dual_sumeE leeN2.
apply: lee_sum_npos_subset => [//|i iPQ]; rewrite oppe_le0; exact: PQf.
Qed.

Lemma lee_dsum_npos_subset I (s : seq I) (P Q : {pred I}) (f : I -> \bar^d R) :
  {subset Q <= P} -> {in [predD P & Q], forall i, f i <= 0} ->
  \sum_(i <- s | P i) f i <= \sum_(i <- s | Q i) f i.
Proof.
move=> QP PQf; rewrite !dual_sumeE leeN2.
apply: lee_sum_nneg_subset => [//|i iPQ]; rewrite oppe_ge0; exact: PQf.
Qed.

Lemma lee_dsum_nneg (I : eqType) (s : seq I) (P Q : pred I)
  (f : I -> \bar^d R) : (forall i, P i -> ~~ Q i -> 0 <= f i) ->
  \sum_(i <- s | P i && Q i) f i <= \sum_(i <- s | P i) f i.
Proof.
move=> PQf; rewrite !dual_sumeE leeN2.
apply: lee_sum_npos => i Pi nQi; rewrite oppe_le0; exact: PQf.
Qed.

Lemma lee_dsum_npos (I : eqType) (s : seq I) (P Q : pred I)
  (f : I -> \bar^d R) : (forall i, P i -> ~~ Q i -> f i <= 0) ->
  \sum_(i <- s | P i) f i <= \sum_(i <- s | P i && Q i) f i.
Proof.
move=> PQf; rewrite !dual_sumeE leeN2.
apply: lee_sum_nneg => i Pi nQi; rewrite oppe_ge0; exact: PQf.
Qed.

Lemma lee_dsum_nneg_ord (f : nat -> \bar^d R) (P : pred nat) :
  (forall n, P n -> 0 <= f n)%E ->
  {homo (fun n => \sum_(i < n | P i) (f i)) : i j / (i <= j)%N >-> i <= j}.
Proof.
move=> f0 m n mlen; rewrite !dual_sumeE leeN2.
apply: (lee_sum_npos_ord (fun i => - f i)%E) => [i Pi|//].
rewrite oppe_le0; exact: f0.
Qed.

Lemma lee_dsum_npos_ord (f : nat -> \bar^d R) (P : pred nat) :
  (forall n, P n -> f n <= 0)%E ->
  {homo (fun n => \sum_(i < n | P i) (f i)) : i j / (i <= j)%N >-> j <= i}.
Proof.
move=> f0 m n mlen; rewrite !dual_sumeE leeN2.
apply: (lee_sum_nneg_ord (fun i => - f i)%E) => [i Pi|//].
rewrite oppe_ge0; exact: f0.
Qed.

Lemma lee_dsum_nneg_natr (f : nat -> \bar^d R) (P : pred nat) m :
  (forall n, (m <= n)%N -> P n -> 0 <= f n) ->
  {homo (fun n => \sum_(m <= i < n | P i) (f i)) : i j / (i <= j)%N >-> i <= j}.
Proof.
move=> f0 i j le_ij; rewrite !dual_sumeE leeN2.
apply: lee_sum_npos_natr => [n ? ?|//]; rewrite oppe_le0; exact: f0.
Qed.

Lemma lee_dsum_npos_natr (f : nat -> \bar^d R) (P : pred nat) m :
  (forall n, (m <= n)%N -> P n -> f n <= 0) ->
  {homo (fun n => \sum_(m <= i < n | P i) (f i)) : i j / (i <= j)%N >-> j <= i}.
Proof.
move=> f0 i j le_ij; rewrite !dual_sumeE leeN2.
apply: lee_sum_nneg_natr => [n ? ?|//]; rewrite oppe_ge0; exact: f0.
Qed.

Lemma lee_dsum_nneg_natl (f : nat -> \bar^d R) (P : pred nat) n :
  (forall m, (m < n)%N -> P m -> 0 <= f m) ->
  {homo (fun m => \sum_(m <= i < n | P i) (f i)) : i j / (i <= j)%N >-> j <= i}.
Proof.
move=> f0 i j le_ij; rewrite !dual_sumeE leeN2.
apply: lee_sum_npos_natl => [m ? ?|//]; rewrite oppe_le0; exact: f0.
Qed.

Lemma lee_dsum_npos_natl (f : nat -> \bar^d R) (P : pred nat) n :
  (forall m, (m < n)%N -> P m -> f m <= 0) ->
  {homo (fun m => \sum_(m <= i < n | P i) (f i)) : i j / (i <= j)%N >-> i <= j}.
Proof.
move=> f0 i j le_ij; rewrite !dual_sumeE leeN2.
apply: lee_sum_nneg_natl => [m ? ?|//]; rewrite oppe_ge0; exact: f0.
Qed.

Lemma lte_dBlDr x y z : y \is a fin_num -> (x - y < z) = (x < z + y).
Proof. by move=> ?; rewrite !dual_addeE lteNl lteNr oppeK lteBlDr. Qed.

Lemma lte_dBlDl x y z : y \is a fin_num -> (x - y < z) = (x < y + z).
Proof. by move=> ?; rewrite !dual_addeE lteNl lteNr lteBrDl ?fin_numN. Qed.

Lemma lte_dBrDr x y z : z \is a fin_num -> (x < y - z) = (x + z < y).
Proof. by move=> ?; rewrite !dual_addeE lteNl lteNr lteBlDr ?fin_numN. Qed.

Lemma lte_dBrDl x y z : z \is a fin_num -> (x < y - z) = (z + x < y).
Proof. by move=> ?; rewrite !dual_addeE lteNl lteNr lteBlDl ?fin_numN. Qed.

Lemma lte_dsuber_addr x y z : y \is a fin_num -> (x < y - z) = (x + z < y).
Proof.
by move=> ?; rewrite !dual_addeE lteNl lteNr lte_subel_addr ?fin_numN.
Qed.

Lemma lte_dsuber_addl x y z : y \is a fin_num -> (x < y - z) = (z + x < y).
Proof.
by move=> ?; rewrite !dual_addeE lteNl lteNr lte_subel_addl ?fin_numN.
Qed.

Lemma lte_dsubel_addr x y z : z \is a fin_num -> (x - y < z) = (x < z + y).
Proof.
by move=> ?; rewrite !dual_addeE lteNl lteNr lte_suber_addr ?fin_numN.
Qed.

Lemma lte_dsubel_addl x y z : z \is a fin_num -> (x - y < z) = (x < y + z).
Proof.
by move=> ?; rewrite !dual_addeE lteNl lteNr lte_suber_addl ?fin_numN.
Qed.

Lemma lee_dsubl_addr x y z : y \is a fin_num -> (x - y <= z) = (x <= z + y).
Proof. by move=> ?; rewrite !dual_addeE leeNl leeNr leeBrDr ?fin_numN. Qed.

Lemma lee_dsubl_addl x y z : y \is a fin_num -> (x - y <= z) = (x <= y + z).
Proof. by move=> ?; rewrite !dual_addeE leeNl leeNr leeBrDl ?fin_numN. Qed.

Lemma lee_dsubr_addr x y z : z \is a fin_num -> (x <= y - z) = (x + z <= y).
Proof. by move=> ?; rewrite !dual_addeE leeNl leeNr leeBlDr ?fin_numN. Qed.

Lemma lee_dsubr_addl x y z : z \is a fin_num -> (x <= y - z) = (z + x <= y).
Proof. by move=> ?; rewrite !dual_addeE leeNl leeNr leeBlDl ?fin_numN. Qed.

Lemma lee_dsubel_addr x y z : x \is a fin_num -> (x - y <= z) = (x <= z + y).
Proof.
by move=> ?; rewrite !dual_addeE leeNl leeNr lee_suber_addr ?fin_numN.
Qed.

Lemma lee_dsubel_addl x y z : x \is a fin_num -> (x - y <= z) = (x <= y + z).
Proof.
by move=> ?; rewrite !dual_addeE leeNl leeNr lee_suber_addl ?fin_numN.
Qed.

Lemma lee_dsuber_addr x y z : x \is a fin_num -> (x <= y - z) = (x + z <= y).
Proof.
by move=> ?; rewrite !dual_addeE leeNl leeNr lee_subel_addr ?fin_numN.
Qed.

Lemma lee_dsuber_addl x y z : x \is a fin_num -> (x <= y - z) = (z + x <= y).
Proof.
by move=> ?; rewrite !dual_addeE leeNl leeNr lee_subel_addl ?fin_numN.
Qed.

Lemma dsuber_gt0 x y : x \is a fin_num -> (0 < y - x) = (x < y).
Proof. by move=> ?; rewrite lte_dBrDl// dadde0. Qed.

Lemma dsubre_gt0 x y : y \is a fin_num -> (0 < y - x) = (x < y).
Proof. by move=> ?; rewrite lte_dsuber_addl// dadde0. Qed.

Lemma dsube_gt0 x y : (x \is a fin_num) || (y \is a fin_num) ->
  (0 < y - x) = (x < y).
Proof. by move=> /orP[?|?]; [rewrite dsuber_gt0|rewrite dsubre_gt0]. Qed.

Lemma dmuleDr x y z : x \is a fin_num -> y +? z -> x * (y + z) = x * y + x * z.
Proof.
by move=> *; rewrite !dual_addeE/= muleN muleDr ?adde_defNN// !muleN.
Qed.

Lemma dmuleDl x y z : x \is a fin_num -> y +? z -> (y + z) * x = y * x + z * x.
Proof. by move=> *; rewrite -!(muleC x) dmuleDr. Qed.

Lemma dge0_muleDl x y z : 0 <= y -> 0 <= z -> (y + z) * x = y * x + z * x.
Proof. by move=> *; rewrite !dual_addeE mulNe le0_muleDl ?oppe_le0 ?mulNe. Qed.

Lemma dge0_muleDr x y z : 0 <= y -> 0 <= z -> x * (y + z) = x * y + x * z.
Proof. by move=> *; rewrite !dual_addeE muleN le0_muleDr ?oppe_le0 ?muleN. Qed.

Lemma dle0_muleDl x y z : y <= 0 -> z <= 0 -> (y + z) * x = y * x + z * x.
Proof. by move=> *; rewrite !dual_addeE mulNe ge0_muleDl ?oppe_ge0 ?mulNe. Qed.

Lemma dle0_muleDr x y z : y <= 0 -> z <= 0 -> x * (y + z) = x * y + x * z.
Proof. by move=> *; rewrite !dual_addeE muleN ge0_muleDr ?oppe_ge0 ?muleN. Qed.

Lemma ge0_dsume_distrl (I : Type) (s : seq I) x (P : pred I)
    (F : I -> \bar^d R) :
  (forall i, P i -> 0 <= F i) ->
  (\sum_(i <- s | P i) F i) * x = \sum_(i <- s | P i) (F i * x).
Proof.
move=> F0; rewrite !dual_sumeE !mulNe le0_sume_distrl => [|i Pi].
- by under eq_bigr => i _ do rewrite mulNe.
- by rewrite oppe_le0 F0.
Qed.

Lemma ge0_dsume_distrr (I : Type) (s : seq I) x (P : pred I)
    (F : I -> \bar^d R) :
  (forall i, P i -> 0 <= F i) ->
  x * (\sum_(i <- s | P i) F i) = \sum_(i <- s | P i) (x * F i).
Proof.
by move=> F0; rewrite muleC ge0_dsume_distrl//; under eq_bigr do rewrite muleC.
Qed.

Lemma le0_dsume_distrl (I : Type) (s : seq I) x (P : pred I)
    (F : I -> \bar^d R) :
  (forall i, P i -> F i <= 0) ->
  (\sum_(i <- s | P i) F i) * x = \sum_(i <- s | P i) (F i * x).
Proof.
move=> F0; rewrite !dual_sumeE mulNe ge0_sume_distrl => [|i Pi].
- by under eq_bigr => i _ do rewrite mulNe.
- by rewrite oppe_ge0 F0.
Qed.

Lemma le0_dsume_distrr (I : Type) (s : seq I) x (P : pred I)
    (F : I -> \bar^d R) :
  (forall i, P i -> F i <= 0) ->
  x * (\sum_(i <- s | P i) F i) = \sum_(i <- s | P i) (x * F i).
Proof.
by move=> F0; rewrite muleC le0_dsume_distrl//; under eq_bigr do rewrite muleC.
Qed.

Lemma lee_abs_dadd x y : `|x + y| <= `|x| + `|y|.
Proof.
by move: x y => [x| |] [y| |] //; rewrite /abse -dEFinD lee_fin ler_normD.
Qed.

Lemma lee_abs_dsum (I : Type) (s : seq I) (F : I -> \bar^d R) (P : pred I) :
  `|\sum_(i <- s | P i) F i| <= \sum_(i <- s | P i) `|F i|.
Proof.
elim/big_ind2 : _ => //; first by rewrite abse0.
by move=> *; exact/(le_trans (lee_abs_dadd _ _) (lee_dD _ _)).
Qed.

Lemma lee_abs_dsub x y : `|x - y| <= `|x| + `|y|.
Proof.
by move: x y => [x| |] [y| |] //; rewrite /abse -dEFinD lee_fin ler_normB.
Qed.

Lemma dadde_minl : left_distributive (@GRing.add (\bar^d R)) mine.
Proof. by move=> x y z; rewrite !dual_addeE oppe_min adde_maxl oppe_max. Qed.

Lemma dadde_minr : right_distributive (@GRing.add (\bar^d R)) mine.
Proof. by move=> x y z; rewrite !dual_addeE oppe_min adde_maxr oppe_max. Qed.

Lemma dmule_natl x n : n%:R%:E * x = x *+ n.
Proof. by rewrite mule_natl ednatmulE. Qed.

Lemma lee_pdaddl y x z : 0 <= x -> y <= z -> y <= x + z.
Proof. by move=> *; rewrite -[y]dadd0e lee_dD. Qed.

Lemma lte_pdaddl y x z : 0 <= x -> y < z -> y < x + z.
Proof. by move=> x0 /lt_le_trans; apply; rewrite lee_pdaddl. Qed.

Lemma lee_pdaddr y x z : 0 <= x -> y <= z -> y <= z + x.
Proof. by move=> *; rewrite daddeC lee_pdaddl. Qed.

Lemma lte_pdaddr y x z : 0 <= x -> y < z -> y < z + x.
Proof. by move=> *; rewrite daddeC lte_pdaddl. Qed.

Lemma lte_spdaddre z x y : z \is a fin_num -> 0 < y -> z <= x -> z < x + y.
Proof.
move: z y x => [z| |] [y| |] [x| |] _ //=; rewrite ?(lte_fin,ltry,ltNyr)//.
exact: ltr_pwDr.
Qed.

Lemma lte_spdadder z x y : x \is a fin_num -> 0 < y -> z <= x -> z < x + y.
Proof.
move: z y x => [z| |] [y| |] [x| |] _ //=; rewrite ?(lte_fin,ltry,ltNyr)//.
exact: ltr_pwDr.
Qed.

End DualERealArithTh_realDomainType.
Arguments lee_dsum_nneg_ord {R}.
Arguments lee_dsum_npos_ord {R}.
Arguments lee_dsum_nneg_natr {R}.
Arguments lee_dsum_npos_natr {R}.
Arguments lee_dsum_nneg_natl {R}.
Arguments lee_dsum_npos_natl {R}.

#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed `lte_dD`")]
Notation lte_dadd := lte_dD (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed `lee_dDl`")]
Notation lee_daddl := lee_dDl (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed `lee_dDr`")]
Notation lee_daddr := lee_dDr (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed `gee_dDl`")]
Notation gee_daddl := gee_dDl (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed `gee_dDr`")]
Notation gee_daddr := gee_dDr (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed `lte_dDl`")]
Notation lte_daddl := lte_dDl (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed `lte_dDr`")]
Notation lte_daddr := lte_dDr (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed `gte_dBl`")]
Notation gte_dsubl := gte_dBl (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed `gte_dBr`")]
Notation gte_dsubr := gte_dBr (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed `gte_dDl`")]
Notation gte_daddl := gte_dDl (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed `gte_dDr`")]
Notation gte_daddr := gte_dDr (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed `lte_dD2lE`")]
Notation lte_dadd2lE := lte_dD2lE (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed `lee_dD2rE`")]
Notation lee_dadd2rE := lee_dD2rE (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed `lee_dD2l`")]
Notation lee_dadd2l := lee_dD2l (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed `lee_dD2r`")]
Notation lee_dadd2r := lee_dD2r (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed `lee_dD`")]
Notation lee_dadd := lee_dD (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed `lee_dB`")]
Notation lee_dsub := lee_dB (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed `lte_dBlDr`")]
Notation lte_dsubl_addr := lte_dBlDr (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed `lte_dBlDl`")]
Notation lte_dsubl_addl := lte_dBlDl (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed `lte_dBrDr`")]
Notation lte_dsubr_addr := lte_dBrDr (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed `lte_dBrDl`")]
Notation lte_dsubr_addl := lte_dBrDl (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed `lte_le_dD`")]
Notation lte_le_dadd := lte_le_dD (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed `lee_lt_dD`")]
Notation lee_lt_dadd := lee_lt_dD (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed `lte_le_dB`")]
Notation lte_le_dsub := lte_le_dD (only parsing).

End DualAddTheoryRealDomain.

Section realFieldType_lemmas.
Variable R : realFieldType.
Implicit Types x y : \bar R.
Implicit Types r : R.

Lemma lee_addgt0Pr x y :
  reflect (forall e, (0 < e)%R -> x <= y + e%:E) (x <= y).
Proof.
apply/(iffP idP) => [|].
- move: x y => [x| |] [y| |]//.
  + by rewrite lee_fin => xy e e0; rewrite -EFinD lee_fin ler_wpDr// ltW.
  + by move=> _ e e0; rewrite leNye.
- move: x y => [x| |] [y| |]// xy; rewrite ?leey ?leNye//;
    [|by move: xy => /(_ _ lte01)..].
  by rewrite lee_fin; apply/ler_addgt0Pr => e e0; rewrite -lee_fin EFinD xy.
Qed.

Lemma lee_subgt0Pr x y :
  reflect (forall e, (0 < e)%R -> x - e%:E <= y) (x <= y).
Proof.
apply/(iffP idP) => [xy e|xy].
  by rewrite leeBlDr//; move: e; exact/lee_addgt0Pr.
by apply/lee_addgt0Pr => e e0; rewrite -leeBlDr// xy.
Qed.

Lemma lee_mul01Pr x y : 0 <= x ->
  reflect (forall r, (0 < r < 1)%R -> r%:E * x <= y) (x <= y).
Proof.
move=> x0; apply/(iffP idP) => [xy r /andP[r0 r1]|h].
  move: x0 xy; rewrite le_eqVlt => /predU1P[<-|x0 xy]; first by rewrite mule0.
  by rewrite (le_trans _ xy)// gee_pMl// ltW.
have h01 : (0 < (2^-1 : R) < 1)%R by rewrite invr_gt0 ?invf_lt1 ?ltr0n ?ltr1n.
move: x y => [x||] [y||] // in x0 h *.
- move: (x0); rewrite lee_fin le_eqVlt => /predU1P[<-|{}x0].
    by rewrite (le_trans _ (h _ h01))// mule_ge0// lee_fin.
  have y0 : (0 < y)%R.
    by rewrite -lte_fin (lt_le_trans _ (h _ h01))// mule_gt0// lte_fin.
  rewrite lee_fin leNgt; apply/negP => yx.
  have /h : (0 < (y + x) / (2 * x) < 1)%R.
    apply/andP; split; first by rewrite divr_gt0 // ?addr_gt0// ?mulr_gt0.
    by rewrite ltr_pdivrMr ?mulr_gt0// mul1r mulr_natl mulr2n ltrD2r.
  rewrite -(EFinM _ x) lee_fin invrM ?unitfE// ?gt_eqF// -mulrA mulrAC.
  by rewrite mulVr ?unitfE ?gt_eqF// mul1r; apply/negP; rewrite -ltNge midf_lt.
- by rewrite leey.
- by have := h _ h01.
- by have := h _ h01; rewrite mulr_infty sgrV gtr0_sg // mul1e.
- by have := h _ h01; rewrite mulr_infty sgrV gtr0_sg // mul1e.
Qed.

Lemma lte_pdivrMl r x y : (0 < r)%R -> (r^-1%:E * y < x) = (y < r%:E * x).
Proof.
move=> r0; move: x y => [x| |] [y| |] //=.
- by rewrite 2!lte_fin ltr_pdivrMl.
- by rewrite mulr_infty sgrV gtr0_sg// mul1e 2!ltNge 2!leey.
- by rewrite mulr_infty sgrV gtr0_sg// mul1e -EFinM 2!ltNyr.
- by rewrite mulr_infty gtr0_sg// mul1e 2!ltry.
- by rewrite mulr_infty [in RHS]mulr_infty sgrV gtr0_sg// mul1e ltxx.
- by rewrite mulr_infty [in RHS]mulr_infty sgrV gtr0_sg// 2!mul1e.
- by rewrite mulr_infty gtr0_sg// mul1e.
- by rewrite mulr_infty [in RHS]mulr_infty sgrV gtr0_sg// 2!mul1e.
- by rewrite mulr_infty [in RHS]mulr_infty sgrV gtr0_sg// mul1e.
Qed.

Lemma lte_pdivrMr r x y : (0 < r)%R -> (y * r^-1%:E < x) = (y < x * r%:E).
Proof. by move=> r0; rewrite muleC lte_pdivrMl// muleC. Qed.

Lemma lte_pdivlMl r y x : (0 < r)%R -> (x < r^-1%:E * y) = (r%:E * x < y).
Proof.
move=> r0; move: x y => [x| |] [y| |] //=.
- by rewrite 2!lte_fin ltr_pdivlMl.
- by rewrite mulr_infty sgrV gtr0_sg// mul1e 2!ltry.
- by rewrite mulr_infty sgrV gtr0_sg// mul1e.
- by rewrite mulr_infty gtr0_sg// mul1e.
- by rewrite mulr_infty [in RHS]mulr_infty sgrV gtr0_sg// mul1e.
- by rewrite mulr_infty [in RHS]mulr_infty sgrV gtr0_sg// 2!mul1e.
- by rewrite mulr_infty gtr0_sg// mul1e 2!ltNyr.
- by rewrite mulr_infty [in RHS]mulr_infty sgrV gtr0_sg// 2!mul1e.
- by rewrite mulr_infty [in RHS]mulr_infty sgrV gtr0_sg// mul1e.
Qed.

Lemma lte_pdivlMr r x y : (0 < r)%R -> (x < y * r^-1%:E) = (x * r%:E < y).
Proof. by move=> r0; rewrite muleC lte_pdivlMl// muleC. Qed.

Lemma lte_ndivlMr r x y : (r < 0)%R -> (x < y * r^-1%:E) = (y < x * r%:E).
Proof.
rewrite -oppr0 ltrNr => r0; rewrite -{1}(opprK r) invrN.
by rewrite EFinN muleN lteNr lte_pdivrMr// EFinN muleNN.
Qed.

Lemma lte_ndivlMl r x y : (r < 0)%R -> (x < r^-1%:E * y) = (y < r%:E * x).
Proof. by move=> r0; rewrite muleC lte_ndivlMr// muleC. Qed.

Lemma lte_ndivrMl r x y : (r < 0)%R -> (r^-1%:E * y < x) = (r%:E * x < y).
Proof.
rewrite -oppr0 ltrNr => r0; rewrite -{1}(opprK r) invrN.
by rewrite EFinN mulNe lteNl lte_pdivlMl// EFinN muleNN.
Qed.

Lemma lte_ndivrMr r x y : (r < 0)%R -> (y * r^-1%:E < x) = (x * r%:E < y).
Proof. by move=> r0; rewrite muleC lte_ndivrMl// muleC. Qed.

Lemma lee_pdivrMl r x y : (0 < r)%R -> (r^-1%:E * y <= x) = (y <= r%:E * x).
Proof.
move=> r0; apply/idP/idP.
- rewrite le_eqVlt => /predU1P[<-|]; last by rewrite lte_pdivrMl// => /ltW.
  by rewrite muleA -EFinM divrr ?mul1e// unitfE gt_eqF.
- rewrite le_eqVlt => /predU1P[->|]; last by rewrite -lte_pdivrMl// => /ltW.
  by rewrite muleA -EFinM mulVr ?mul1e// unitfE gt_eqF.
Qed.

Lemma lee_pdivrMr r x y : (0 < r)%R -> (y * r^-1%:E <= x) = (y <= x * r%:E).
Proof. by move=> r0; rewrite muleC lee_pdivrMl// muleC. Qed.

Lemma lee_pdivlMl r y x : (0 < r)%R -> (x <= r^-1%:E * y) = (r%:E * x <= y).
Proof.
move=> r0; apply/idP/idP.
- rewrite le_eqVlt => /predU1P[->|]; last by rewrite lte_pdivlMl// => /ltW.
  by rewrite muleA -EFinM divrr ?mul1e// unitfE gt_eqF.
- rewrite le_eqVlt => /predU1P[<-|]; last by rewrite -lte_pdivlMl// => /ltW.
  by rewrite muleA -EFinM mulVr ?mul1e// unitfE gt_eqF.
Qed.

Lemma lee_pdivlMr r x y : (0 < r)%R -> (x <= y * r^-1%:E) = (x * r%:E <= y).
Proof. by move=> r0; rewrite muleC lee_pdivlMl// muleC. Qed.

Lemma lee_ndivlMr r x y : (r < 0)%R -> (x <= y * r^-1%:E) = (y <= x * r%:E).
Proof.
rewrite -oppr0 ltrNr => r0; rewrite -{1}(opprK r) invrN.
by rewrite EFinN muleN leeNr lee_pdivrMr// EFinN muleNN.
Qed.

Lemma lee_ndivlMl r x y : (r < 0)%R -> (x <= r^-1%:E * y) = (y <= r%:E * x).
Proof. by move=> r0; rewrite muleC lee_ndivlMr// muleC. Qed.

Lemma lee_ndivrMl r x y : (r < 0)%R -> (r^-1%:E * y <= x) = (r%:E * x <= y).
Proof.
rewrite -oppr0 ltrNr => r0; rewrite -{1}(opprK r) invrN.
by rewrite EFinN mulNe leeNl lee_pdivlMl// EFinN muleNN.
Qed.

Lemma lee_ndivrMr r x y : (r < 0)%R -> (y * r^-1%:E <= x) = (x * r%:E <= y).
Proof. by move=> r0; rewrite muleC lee_ndivrMl// muleC. Qed.

Lemma eqe_pdivrMl r x y : (r != 0)%R ->
  ((r^-1)%:E * y == x) = (y == r%:E * x).
Proof.
rewrite neq_lt => /orP[|] r0.
- by rewrite eq_le lee_ndivrMl// lee_ndivlMl// -eq_le.
- by rewrite eq_le lee_pdivrMl// lee_pdivlMl// -eq_le.
Qed.

End realFieldType_lemmas.
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed `lte_pdivrMl`")]
Notation lte_pdivr_mull := lte_pdivrMl (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed `lte_pdivrMr`")]
Notation lte_pdivr_mulr := lte_pdivrMr (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed `lte_pdivlMl`")]
Notation lte_pdivl_mull := lte_pdivlMl (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed `lte_pdivlMr`")]
Notation lte_pdivl_mulr := lte_pdivlMr (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed `lee_pdivrMl`")]
Notation lee_pdivr_mull := lee_pdivrMl (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed `lee_pdivrMr`")]
Notation lee_pdivr_mulr := lee_pdivrMr (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed `lee_pdivlMl`")]
Notation lee_pdivl_mull := lee_pdivlMl (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed `lee_pdivlMr`")]
Notation lee_pdivl_mulr := lee_pdivlMr (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed `lte_ndivrMl`")]
Notation lte_ndivr_mull := lte_ndivrMl (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed `lte_ndivrMr`")]
Notation lte_ndivr_mulr := lte_ndivrMr (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed `lte_ndivlMl`")]
Notation lte_ndivl_mull := lte_ndivlMl (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed `lte_ndivlMr`")]
Notation lte_ndivl_mulr := lte_ndivlMr (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed `lee_ndivrMl`")]
Notation lee_ndivr_mull := lee_ndivrMl (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed `lee_ndivrMr`")]
Notation lee_ndivr_mulr := lee_ndivrMr (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed `lee_ndivlMl`")]
Notation lee_ndivl_mull := lee_ndivlMl (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed `lee_ndivlMr`")]
Notation lee_ndivl_mulr := lee_ndivlMr (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed `eqe_pdivrMl`")]
Notation eqe_pdivr_mull := eqe_pdivrMl (only parsing).

Module DualAddTheoryRealField.

Import DualAddTheoryNumDomain DualAddTheoryRealDomain.

Section DualRealFieldType_lemmas.
Local Open Scope ereal_dual_scope.
Variable R : realFieldType.
Implicit Types x y : \bar^d R.

Lemma lee_daddgt0Pr x y :
  reflect (forall e, (0 < e)%R -> x <= y + e%:E) (x <= y).
Proof. exact: lee_addgt0Pr. Qed.

End DualRealFieldType_lemmas.

End DualAddTheoryRealField.

Section sqrte.
Variable R : rcfType.
Implicit Types x y : \bar R.

Definition sqrte x :=
  if x is +oo then +oo else if x is r%:E then (Num.sqrt r)%:E else 0.

Lemma sqrte0 : sqrte 0 = 0 :> \bar R.
Proof. by rewrite /= sqrtr0. Qed.

Lemma sqrte_ge0 x : 0 <= sqrte x.
Proof. by case: x => [x|//|]; rewrite /= ?leey// lee_fin sqrtr_ge0. Qed.

Lemma lee_sqrt x y : 0 <= y -> (sqrte x <= sqrte y) = (x <= y).
Proof.
case: x y => [x||] [y||] yge0 //=.
- exact: ler_sqrt.
- by rewrite !leey.
- by rewrite leNye lee_fin sqrtr_ge0.
Qed.

Lemma sqrteM x y : 0 <= x -> sqrte (x * y) = sqrte x * sqrte y.
Proof.
case: x y => [x||] [y||] //= age0.
- by rewrite sqrtrM ?EFinM.
- move: age0; rewrite le_eqVlt eqe => /predU1P[<-|x0].
    by rewrite mul0e sqrte0 sqrtr0 mul0e.
  by rewrite mulry gtr0_sg ?mul1e// mulry gtr0_sg ?mul1e// sqrtr_gt0.
- move: age0; rewrite mule0 mulrNy lee_fin -sgr_ge0.
  by case: sgrP; rewrite ?mul0e ?sqrte0// ?mul1e// ler0N1.
- rewrite !mulyr; case: (sgrP y) => [->||].
  + by rewrite sqrtr0 sgr0 mul0e sqrte0.
  + by rewrite mul1e/= -sqrtr_gt0 -sgr_gt0 -lte_fin => /gt0_muley->.
  + by move=> y0; rewrite EFinN mulN1e/= ltr0_sqrtr// sgr0 mul0e.
- by rewrite mulyy.
- by rewrite mulyNy mule0.
Qed.

Lemma sqr_sqrte x : 0 <= x -> sqrte x ^+ 2 = x.
Proof.
case: x => [x||] xge0; rewrite expe2 ?mulyy//.
by rewrite -sqrteM// -EFinM/= sqrtr_sqr ger0_norm.
Qed.

Lemma sqrte_sqr x : sqrte (x ^+ 2) = `|x|%E.
Proof. by case: x => [x||//]; rewrite /expe/= ?sqrtr_sqr// mulyy. Qed.

Lemma sqrte_fin_num x : 0 <= x -> (sqrte x \is a fin_num) = (x \is a fin_num).
Proof. by case: x => [x|//|//]; rewrite !qualifE/=. Qed.

End sqrte.

Module DualAddTheory.
Export DualAddTheoryNumDomain.
Export DualAddTheoryRealDomain.
Export DualAddTheoryRealField.
End DualAddTheory.

Module ConstructiveDualAddTheory.
Export DualAddTheory.
End ConstructiveDualAddTheory.

(* TODO: bump up *)
From mathcomp Require Import interval ssrint.

Section Itv.
Context {R : numDomainType}.

Definition ext_num_sem (i : interval int) (x : \bar R) :=
  (0 >=< x)%O
  && let: Interval l u := i in
     x \in Interval (Itv.map_itv_bound (EFin \o intr) l)
             (Itv.map_itv_bound (EFin \o intr) u).

Local Notation num_spec := (Itv.spec (@Itv.num_sem _)).
Local Notation num_def R := (Itv.def (@Itv.num_sem R)).
Local Notation num_itv_bound R := (@Itv.map_itv_bound _ R intr).

Local Notation ext_num_spec := (Itv.spec ext_num_sem).
Local Notation ext_num_def := (Itv.def ext_num_sem).
Local Notation ext_num_itv_bound :=
  (@Itv.map_itv_bound _ (\bar R) (EFin \o intr)).

Lemma ext_num_num_sem_subproof i (x : R) :
  Itv.ext_num_sem i x%:E = Itv.num_sem i x.
Proof. by case: i => [l u]; do 2![congr (_ && _)]; [case: l | case: u]. Qed.

Lemma ext_num_num_spec_subproof i (x : R) :
  ext_num_spec i x%:E = num_spec i x.
Proof. by case: i => [//| i]; apply: ext_num_num_sem_subproof. Qed.

Lemma EFin_le_map_itv_bound (x y : itv_bound R) :
  (Itv.map_itv_bound EFin x <= Itv.map_itv_bound EFin y)%O = (x <= y)%O.
Proof. by case: x y => [xb x | x] [yb y | y]. Qed.

Lemma EFin_BLeft_le_map_itv_bound (x : itv_bound R) (y : R) :
  (Itv.map_itv_bound EFin x <= BLeft y%:E)%O = (x <= BLeft y)%O.
Proof.
rewrite -[BLeft y%:E]/(Itv.map_itv_bound EFin (BLeft y)).
by rewrite EFin_le_map_itv_bound.
Qed.

Lemma BRight_EFin_le_map_itv_bound (x : R) (y : itv_bound R) :
  (BRight x%:E <= Itv.map_itv_bound EFin y)%O = (BRight x <= y)%O.
Proof.
rewrite -[BRight x%:E]/(Itv.map_itv_bound EFin (BRight x)).
by rewrite EFin_le_map_itv_bound.
Qed.

Lemma ext_le_map_itv_bound (x y : itv_bound int) :
  (ext_num_itv_bound x <= ext_num_itv_bound y)%O = (x <= y)%O.
Proof.
rewrite !(map_itv_bound_comp EFin intr)/=.
by rewrite EFin_le_map_itv_bound intr_le_map_itv_bound.
Qed.

Lemma subitv_map_itv (x y : Itv.t) : Itv.sub x y ->
  forall z : \bar R, ext_num_spec x z -> ext_num_spec y z.
Proof.
case: x y => [| x] [| y] //= x_sub_y z /andP[rz]; rewrite /Itv.ext_num_sem rz/=.
move: x y x_sub_y => [lx ux] [ly uy] /andP[lel leu] /=.
move=> /andP[lxz zux]; apply/andP; split.
- by apply: le_trans lxz; rewrite ext_le_map_itv_bound.
- by apply: le_trans zux _; rewrite ext_le_map_itv_bound.
Qed.

Section ItvTheory.
Context {i : Itv.t}.
Implicit Type x : ext_num_def i.

Lemma ext_widen_itv_subproof x i' : Itv.sub i i' ->
  ext_num_spec i' x%:inum.
Proof. by case: x => x /= /[swap] /subitv_map_itv; apply. Qed.

Definition ext_widen_itv x i' (uni : unify_itv i i') :=
  Itv.mk (ext_widen_itv_subproof x uni).

Lemma gt0e x : unify_itv i (Itv.Real `]Posz 0, +oo[) -> 0%E < x%:inum :> \bar R.
Proof.
case: x => x /= /[swap] /subitv_map_itv /[apply] /andP[_].
by rewrite /= in_itv/= andbT.
Qed.

Lemma lte0 x : unify_itv i (Itv.Real `]-oo, Posz 0[) -> x%:inum < 0%E :> \bar R.
Proof.
by case: x => x /= /[swap] /subitv_map_itv /[apply] /andP[_] /=; rewrite in_itv.
Qed.

Lemma ge0e x : unify_itv i (Itv.Real `[Posz 0, +oo[) -> 0%E <= x%:inum :> \bar R.
Proof.
case: x => x /= /[swap] /subitv_map_itv /[apply] /andP[_] /=.
by rewrite in_itv/= andbT.
Qed.

Lemma lee0 x : unify_itv i (Itv.Real `]-oo, Posz 0]) -> x%:inum <= 0%E :> \bar R.
Proof.
by case: x => x /= /[swap] /subitv_map_itv /[apply] /andP[_] /=; rewrite in_itv.
Qed.

Lemma cmp0e x : unify_itv i (Itv.Real `]-oo, +oo[) -> (0%E >=< x%:inum)%O.
Proof. by case: i x => [//| [l u] [[x||//] /=/andP[/= xr _]]]. Qed.

Lemma neqe0 x :
  unify (fun ix iy => negb (Itv.sub ix iy)) (Itv.Real `[0%Z, 0%Z]) i ->
  x%:inum != 0 :> \bar R.
Proof.
case: i x => [//| [l u] [x /= Px]]; apply: contra => /eqP x0 /=.
move: Px; rewrite x0 => /and3P[_ /= l0 u0]; apply/andP; split.
- by case: l l0 => [[] l |]; rewrite ?bnd_simp ?lee_fin ?lte_fin ?lerz0 ?ltrz0.
- by case: u u0 => [[] u |]; rewrite ?bnd_simp ?lee_fin ?lte_fin ?ler0z ?ltr0z.
Qed.

End ItvTheory.

Lemma pinfty_inum_subproof : ext_num_spec (Itv.Real `]1%Z, +oo[) (+oo : \bar R).
Proof. by apply/and3P; rewrite /= cmp0y !bnd_simp real_ltry. Qed.

Canonical pinfty_inum := Itv.mk (pinfty_inum_subproof).

Lemma ninfty_inum_subproof :
  ext_num_spec (Itv.Real `]-oo, (-1)%Z[) (-oo : \bar R).
Proof. by apply/and3P; rewrite /= cmp0Ny !bnd_simp real_ltNyr. Qed.

Canonical ninfty_snum := Itv.mk (ninfty_inum_subproof).

Lemma EFin_inum_subproof i (x : num_def R i) : ext_num_spec i x%:num%:E.
Proof.
case: i x => [//| [l u] [x /=/and3P[xr /= lx xu]]].
by apply/and3P; split=> [//||]; [case: l lx | case: u xu].
Qed.

Canonical EFin_inum i (x : num_def R i) := Itv.mk (EFin_inum_subproof x).

Definition keep_nonneg_itv_bound_subdef b :=
  match b with
  | BSide _ (Posz _) => BLeft 0%Z
  | BSide _ (Negz _) => -oo%O
  | BInfty _ => -oo%O
  end.
Arguments keep_nonneg_itv_bound_subdef /.

Definition keep_nonpos_itv_bound_subdef b :=
  match b with
  | BSide _ (Negz _) | BSide _ (Posz 0) => BRight 0%Z
  | BSide _ (Posz (S _)) => +oo%O
  | BInfty _ => +oo%O
  end.
Arguments keep_nonpos_itv_bound_subdef /.

Definition fine_itv_subdef i :=
  let: Interval l u := i in
  Interval (keep_nonneg_itv_bound_subdef l) (keep_nonpos_itv_bound_subdef u).

Lemma fine_inum_subproof i (x : ext_num_def i)
    (r := itv_real1_subdef fine_itv_subdef i) :
  num_spec r (fine x%:num).
Proof.
rewrite {}/r; case: i x => [//| [l u] [x /=/and3P[xr /= lx xu]]].
apply/and3P; split; rewrite -?real_fine//.
- case: x lx {xu xr} => [x||]/=; [|by case: l => [? []|]..].
  by case: l => [[] [l |//] |//] /[!bnd_simp] => [|/ltW]/=; rewrite lee_fin;
     apply: le_trans.
- case: x xu {lx xr} => [x||]/=; [|by case: u => [? [[]|] |]..].
  by case: u => [bu [[|//] | u] |//]; case: bu => /[!bnd_simp] [/ltW|]/=;
     rewrite lee_fin// => xu; apply: le_trans xu _; rewrite lerz0.
Qed.

Canonical fine_inum i (x : ext_num_def i) := Itv.mk (fine_inum_subproof x).

Lemma ext_num_sem_y l u :
  ext_num_sem (Interval l u) +oo = ((l != +oo%O) && (u == +oo%O)).
Proof.
apply/and3P/andP => [[_ ly uy] | [ly uy]]; split.
- by case: l ly => -[].
- by case: u uy => -[].
- exact: cmp0y.
- case: l ly => [|[]//].
  by case=> l _ /=; rewrite bnd_simp ?real_leey ?real_ltry /= realz.
- by case: u uy => -[].
Qed.

Lemma ext_num_sem_Ny l u :
  ext_num_sem (Interval l u) -oo = ((l == -oo%O) && (u != -oo%O)).
Proof.
apply/and3P/andP => [[_ ly uy] | [ly uy]]; split.
- by case: l ly => -[].
- by case: u uy => -[].
- exact: real0.
- by case: l ly => -[].
- case: u uy => [|[]//].
  by case=> u _ /=; rewrite bnd_simp ?real_leNye ?real_ltNyr /= realz.
Qed.

Lemma oppe_itv_boundr_subproof (x : \bar R) b :
  (BRight (- x) <= ext_num_itv_bound (opp_itv_bound_subdef b))%O
  = (ext_num_itv_bound b <= BLeft x)%O.
Proof.
by case: b => [[] b | []//]; rewrite /= !bnd_simp mulrNz EFinN ?leeN2 // lteN2.
Qed.

Lemma oppe_itv_boundl_subproof (x : \bar R) b :
  (ext_num_itv_bound (opp_itv_bound_subdef b) <= BLeft (- x))%O
  = (BRight x <= ext_num_itv_bound b)%O.
Proof.
by case: b => [[] b | []//]; rewrite /= !bnd_simp mulrNz EFinN ?leeN2 // lteN2.
Qed.

Lemma oppe_inum_subproof i (x : ext_num_def i)
    (r := itv_real1_subdef opp_itv_subdef i) :
  ext_num_spec r (- x%:inum).
Proof.
rewrite {}/r; case: x => -[x||]/=;
  [|by case: i => [//| [l u]]; rewrite /= ext_num_sem_y ext_num_sem_Ny;
       case: l u => [[] ?|[]] [[] ?|[]]..].
rewrite !ext_num_num_spec_subproof => Px.
by rewrite -[x]/(Itv.mk Px)%:inum opp_inum_subproof.
Qed.

Canonical oppe_inum i (x : ext_num_def i) := Itv.mk (oppe_inum_subproof x).

Lemma adde_inum_subproof xi yi (x : ext_num_def xi) (y : ext_num_def yi)
    (r := itv_real2_subdef add_itv_subdef xi yi) :
  ext_num_spec r (adde x%:inum y%:inum).
Proof.
rewrite {}/r; case: x y => -[x||] + [[y||]]/=;
  [|by case: xi yi => [//| [xl xu]] [//| [yl yu]];
       rewrite /adde/= ?ext_num_sem_y ?ext_num_sem_Ny;
       case: xl xu yl yu => [[] ?|[]] [[] ?|[]] [[] ?|[]] [[] ?|[]]..].
rewrite !ext_num_num_spec_subproof => Px Py.
by rewrite -[x]/(Itv.mk Px)%:inum -[y]/(Itv.mk Py)%:inum add_inum_subproof.
Qed.

Canonical adde_inum xi yi (x : ext_num_def xi) (y : ext_num_def yi) :=
  Itv.mk (adde_inum_subproof x y).

Import DualAddTheory.

Lemma dEFin_inum_subproof i (x : num_def R i) : ext_num_spec i (dEFin x%:num).
Proof.
case: i x => [//| [l u] [x /=/and3P[xr /= lx xu]]].
by apply/and3P; split=> [//||]; [case: l lx | case: u xu].
Qed.

Canonical dEFin_inum i (x : num_def R i) := Itv.mk (dEFin_inum_subproof x).

Lemma dadde_inum_subproof xi yi (x : ext_num_def xi) (y : ext_num_def yi)
    (r := itv_real2_subdef add_itv_subdef xi yi) :
  ext_num_spec r (dual_adde x%:inum y%:inum).
Proof.
rewrite {}/r; case: x y => -[x||] + [[y||]]/=;
  [|by case: xi yi => [//| [xl xu]] [//| [yl yu]];
       rewrite /dual_adde/= ?ext_num_sem_y ?ext_num_sem_Ny;
       case: xl xu yl yu => [[] ?|[]] [[] ?|[]] [[] ?|[]] [[] ?|[]]..].
rewrite !ext_num_num_spec_subproof => Px Py.
by rewrite -[x]/(Itv.mk Px)%:inum -[y]/(Itv.mk Py)%:inum add_inum_subproof.
Qed.

Canonical dadde_inum xi yi (x : ext_num_def xi) (y : ext_num_def yi) :=
  Itv.mk (dadde_inum_subproof x y).

Variant ext_interval_sign_spec (l u : itv_bound int) (x : \bar R) :
      signi -> Set :=
  | ISignEqZero : l = BLeft 0%Z -> u = BRight 0%Z -> x = 0 ->
                  ext_interval_sign_spec l u x (Known EqZero)
  | ISignNonNeg : (BLeft 0%:Z <= l)%O -> (BRight 0%:Z < u)%O -> 0 <= x ->
                  ext_interval_sign_spec l u x (Known NonNeg)
  | ISignNonPos : (l < BLeft 0%:Z)%O -> (u <= BRight 0%:Z)%O -> x <= 0 ->
                  ext_interval_sign_spec l u x (Known NonPos)
  | ISignBoth : (l < BLeft 0%:Z)%O -> (BRight 0%:Z < u)%O ->
                (0 >=< x)%O -> ext_interval_sign_spec l u x Unknown.

Lemma ext_interval_signP (l u : itv_bound int) (x : \bar R) :
    (ext_num_itv_bound l <= BLeft x)%O -> (BRight x <= ext_num_itv_bound u)%O ->
    (0 >=< x)%O ->
  ext_interval_sign_spec l u x (interval_sign (Interval l u)).
Proof.
case: x => [x||] xl xu xs.
- case: (@interval_signP R l u x _ _ xs).
  + by case: l xl => -[].
  + by case: u xu => -[].
  + by move=> l0 u0 x0; apply: ISignEqZero => //; rewrite x0.
  + by move=> l0 u0 x0; apply: ISignNonNeg.
  + by move=> l0 u0 x0; apply: ISignNonPos.
  + by move=> l0 u0 x0; apply: ISignBoth.
- have uy : u = +oo%O by case: u xu => -[].
  have u0 : (BRight 0%:Z < u)%O by rewrite uy.
  case: (leP (BLeft 0%Z) l) => l0.
  + suff -> : interval_sign (Interval l u) = Known NonNeg.
      by apply: ISignNonNeg => //; apply: le0y.
    rewrite /=/itv_bound_signl /itv_bound_signr uy/=.
    by case: eqP => [//| /eqP lneq0]; case: ltgtP l0 lneq0.
  + suff -> : interval_sign (Interval l u) = Unknown by exact: ISignBoth.
    rewrite /=/itv_bound_signl /itv_bound_signr uy/=.
    by case: eqP l0 => [->//| /eqP leq0] /ltW->.
- have ly : l = -oo%O by case: l xl => -[].
  have l0 : (l < BLeft 0%:Z)%O by rewrite ly.
  case: (leP u (BRight 0%Z)) => u0.
  + suff -> : interval_sign (Interval l u) = Known NonPos by exact: ISignNonPos.
    rewrite /=/itv_bound_signl /itv_bound_signr ly/=.
    by case: eqP => [//| /eqP uneq0]; case: ltgtP u0 uneq0.
  + suff -> : interval_sign (Interval l u) = Unknown by exact: ISignBoth.
    rewrite /=/itv_bound_signl /itv_bound_signr ly/=.
    by case: eqP u0 => [->//| /eqP ueq0]; rewrite ltNge => /negbTE->.
Qed.

Lemma ext_mul_itv_boundl_subproof b1 b2 (x1 x2 : \bar R) :
  (BLeft 0%:Z <= b1 -> BLeft 0%:Z <= b2 ->
   ext_num_itv_bound b1 <= BLeft x1 ->
   ext_num_itv_bound b2 <= BLeft x2 ->
   ext_num_itv_bound (mul_itv_boundl_subdef b1 b2) <= BLeft (x1 * x2))%O.
Proof.
move=> b10 b20 b1x1 b2x2.
have x10 : 0 <= x1.
  by case: x1 b1x1 (le_trans (eqbRL (ext_le_map_itv_bound _ _) b10) b1x1).
have x20 : 0 <= x2.
  by case: x2 b2x2 (le_trans (eqbRL (ext_le_map_itv_bound _ _) b20) b2x2).
have x1r : (0 >=< x1)%O by rewrite real_fine; exact/ger0_real/fine_ge0.
have x2r : (0 >=< x2)%O by rewrite real_fine; exact/ger0_real/fine_ge0.
have ley b1' b2' :
    (Itv.map_itv_bound EFin (num_itv_bound R (mul_itv_boundl_subdef b1' b2'))
     <= BLeft +oo%E)%O.
  by case: b1' b2' => [[] [[| ?] | ?] | []] [[] [[| ?] | ?] | []]//=;
     rewrite bnd_simp ?real_leey ?real_ltry/= ?realz.
case: x1 x2 x10 x20 x1r x2r b1x1 b2x2 => [x1||] [x2||] //= x10 x20 x1r x2r.
- rewrite !(map_itv_bound_comp, EFin_BLeft_le_map_itv_bound)/=.
  exact: mul_itv_boundl_subproof.
- rewrite !(map_itv_bound_comp EFin intr) real_mulry//= => b1x1 _.
  case: (comparable_ltgtP x1r) x10 => [x10 |//| [x10]] _.
    by rewrite gtr0_sg ?mul1e ?bnd_simp.
  rewrite -x10 sgr0 mul0e/= EFin_BLeft_le_map_itv_bound.
  suff -> : b1 = BLeft 0%Z by case: b2 {b20}.
  apply/le_anti; rewrite b10 andbT.
  move: b1x1; rewrite EFin_BLeft_le_map_itv_bound.
  by rewrite -x10 -(mulr0z 1) intr_BLeft_le_map_itv_bound.
- rewrite !(map_itv_bound_comp EFin intr) real_mulyr//= => _ b2x2.
  case: (comparable_ltgtP x2r) x20 => [x20 |//| [x20]] _.
    by rewrite gtr0_sg ?mul1e ?bnd_simp.
  rewrite -x20 sgr0 mul0e/= EFin_BLeft_le_map_itv_bound.
  suff -> : b2 = BLeft 0%Z by case: b1 {b10} => [[] [] []|].
  apply/le_anti; rewrite b20 andbT.
  move: b2x2; rewrite EFin_BLeft_le_map_itv_bound.
  by rewrite -x20 -(mulr0z 1) intr_BLeft_le_map_itv_bound.
- by rewrite mulyy/= 3!map_itv_bound_comp.
Qed.

Lemma ext_mul_itv_boundr_subproof b1 b2 (x1 x2 : \bar R) :
  (0 <= x1 -> 0 <= x2 ->
   BRight x1 <= ext_num_itv_bound b1 ->
   BRight x2 <= ext_num_itv_bound b2 ->
   BRight (x1 * x2) <= ext_num_itv_bound (mul_itv_boundr_subdef b1 b2))%O.
Proof.
move=> x10 x20 b1x1 b2x2.
have x1r : (0 >=< x1)%O by rewrite real_fine; exact/ger0_real/fine_ge0.
have x2r : (0 >=< x2)%O by rewrite real_fine; exact/ger0_real/fine_ge0.
case: x1 x2 x10 x20 x1r x2r b1x1 b2x2 => [x1||] [x2||] //= x10 x20 x1r x2r.
- rewrite !(map_itv_bound_comp, BRight_EFin_le_map_itv_bound)/=.
  exact: mul_itv_boundr_subproof.
- rewrite real_mulry// => b1x1 b2x2.
  have -> : b2 = +oo%O by case: b2 b2x2 => -[].
  rewrite mul_itv_boundrC_subproof/= map_itv_bound_comp.
  case: (comparable_ltgtP x1r) x10 => [x10 |//| [x10]] _.
  + rewrite gtr0_sg ?mul1e ?bnd_simp//.
    suff: (BRight 0%Z < b1)%O by case: b1 b1x1 => [[] [] [] |].
    move: b1x1; rewrite map_itv_bound_comp BRight_EFin_le_map_itv_bound.
    case: b1 => [[] b1 |//]; rewrite !bnd_simp -(@ltr0z R).
    * exact/le_lt_trans/ltW.
    * exact/lt_le_trans.
  + rewrite -x10 sgr0 mul0e/= BRight_EFin_le_map_itv_bound.
    suff: (BRight 0%Z <= b1)%O by case: b1 b1x1 => [[] [] [] |].
    move: b1x1; rewrite map_itv_bound_comp BRight_EFin_le_map_itv_bound.
    by rewrite -x10 -(@mulr0z R 1) BRight_intr_le_map_itv_bound.
- rewrite real_mulyr// => b1x1 b2x2.
  have -> : b1 = +oo%O by case: b1 b1x1 => -[].
  rewrite /= map_itv_bound_comp.
  case: (comparable_ltgtP x2r) x20 => [x20 |//| [x20]] _.
  + rewrite gtr0_sg ?mul1e ?bnd_simp//.
    suff: (BRight 0%Z < b2)%O by case: b2 b2x2 => [[] [] [] |].
    move: b2x2; rewrite map_itv_bound_comp BRight_EFin_le_map_itv_bound.
    case: b2 => [[] b2 |//]; rewrite !bnd_simp -(@ltr0z R).
    * exact/le_lt_trans/ltW.
    * exact/lt_le_trans.
  + rewrite -x20 sgr0 mul0e/= BRight_EFin_le_map_itv_bound.
    suff: (BRight 0%Z <= b2)%O by case: b2 b2x2 => [[] [] [] |].
    move: b2x2; rewrite map_itv_bound_comp BRight_EFin_le_map_itv_bound.
    by rewrite -x20 -(@mulr0z R 1) BRight_intr_le_map_itv_bound.
- rewrite mulyy/= => b1x1 b2x2.
  have -> : b1 = +oo%O by case: b1 b1x1 => -[].
  by have -> : b2 = +oo%O by case: b2 b2x2 => -[].
Qed.

Lemma ext_mul_itv_boundr'_subproof b1 b2 (x1 x2 : \bar R) :
  (0 <= x1 -> (0 >=< x2)%O -> BRight 0%Z <= b2 ->
   BRight x1 <= ext_num_itv_bound b1 ->
   BRight x2 <= ext_num_itv_bound b2 ->
   BRight (x1 * x2) <= ext_num_itv_bound (mul_itv_boundr_subdef b1 b2))%O.
Proof.
move=> x1ge0 x2r b2ge0 lex1b1 lex2b2.
have /orP[x2ge0 | x2le0] : (0 <= x2) || (x2 <= 0).
- by case: x2 x2r {lex2b2} => [x2 /=|_|_]; rewrite ?lee_fin ?le0y ?leNy0.
- exact: ext_mul_itv_boundr_subproof.
have lem0 : (BRight (x1 * x2) <= BRight 0%R)%O.
  by have:= mule_ge0_le0 x1ge0 x2le0; case: mule.
apply: le_trans lem0 _.
rewrite map_itv_bound_comp BRight_EFin_le_map_itv_bound/=.
rewrite -(@mulr0z R 1) BRight_intr_le_map_itv_bound.
apply: mul_itv_boundr_BRight_subproof => //.
case: x1 x1ge0 lex1b1 => [x1||//]/= x1ge0; last by case: b1 => -[].
rewrite map_itv_bound_comp BRight_EFin_le_map_itv_bound.
rewrite -(@BRight_intr_le_map_itv_bound R)/=.
by apply: le_trans; rewrite bnd_simp -lee_fin.
Qed.

Lemma comparable_ext_num_itv_bound_subproof (x y : itv_bound int) :
  (ext_num_itv_bound x >=< ext_num_itv_bound y)%O.
Proof.
apply/orP; rewrite !(map_itv_bound_comp EFin intr)/= !EFin_le_map_itv_bound.
exact/orP/comparable_num_itv_bound_subproof.
Qed.

Lemma ext_map_itv_bound_min (x y : itv_bound int) :
  ext_num_itv_bound (Order.min x y)
  = Order.min (ext_num_itv_bound x) (ext_num_itv_bound y).
Proof.
have [lexy | ltyx] := leP x y; [by rewrite !minEle ext_le_map_itv_bound lexy|].
rewrite minElt -if_neg -comparable_leNgt ?ext_le_map_itv_bound ?ltW//.
exact: comparable_ext_num_itv_bound_subproof.
Qed.

Lemma ext_map_itv_bound_max (x y : itv_bound int) :
  ext_num_itv_bound (Order.max x y)
  = Order.max (ext_num_itv_bound x) (ext_num_itv_bound y).
Proof.
have [lexy | ltyx] := leP x y; [by rewrite !maxEle ext_le_map_itv_bound lexy|].
rewrite maxElt -if_neg -comparable_leNgt ?ext_le_map_itv_bound ?ltW//.
exact: comparable_ext_num_itv_bound_subproof.
Qed.

Lemma mule_inum_subproof xi yi (x : ext_num_def xi) (y : ext_num_def yi)
    (r := itv_real2_subdef mul_itv_subdef xi yi) :
  ext_num_spec r (x%:inum * y%:inum).
Proof.
rewrite {}/r; case: xi yi x y => [//| [xl xu]] [//| [yl yu]].
case=> [x /=/and3P[xr /= xlx xxu]] [y /=/and3P[yr /= yly yyu]].
rewrite -/(interval_sign (Interval xl xu)) -/(interval_sign (Interval yl yu)).
have ns000 : ext_num_sem `[0%Z, 0%Z] 0 by apply/and3P; rewrite ?comparablexx.
have xyr : (0 >=< (x * y)%E)%O by exact: realMe.
case: (ext_interval_signP xlx xxu xr) => xlb xub xs.
- by rewrite xs mul0e; case: (ext_interval_signP yly yyu yr).
- case: (ext_interval_signP yly yyu yr) => ylb yub ys.
  + by rewrite ys mule0.
  + apply/and3P; split=> //=.
    * exact: ext_mul_itv_boundl_subproof.
    * exact: ext_mul_itv_boundr_subproof.
  + apply/and3P; split=> //=; rewrite -[x * y]oppeK -real_muleN//.
    * rewrite oppe_itv_boundl_subproof.
      by rewrite ext_mul_itv_boundr_subproof ?oppe_ge0 ?oppe_itv_boundr_subproof.
    * rewrite oppe_itv_boundr_subproof.
      rewrite ext_mul_itv_boundl_subproof ?oppe_itv_boundl_subproof//.
      by rewrite opp_itv_ge0_subproof.
  + apply/and3P; split=> //=.
    * rewrite  -[x * y]oppeK -real_muleN// oppe_itv_boundl_subproof.
      rewrite ext_mul_itv_boundr'_subproof -?real_fine ?oppe_cmp0
              ?oppe_itv_boundr_subproof//.
      by rewrite opp_itv_gt0_subproof ltW.
    * by rewrite ext_mul_itv_boundr'_subproof// ltW.
- case: (ext_interval_signP yly yyu yr) => ylb yub ys.
  + by rewrite ys mule0.
  + apply/and3P; split=> //=; rewrite -[x * y]oppeK -real_mulNe//.
    * rewrite oppe_itv_boundl_subproof.
      by rewrite ext_mul_itv_boundr_subproof ?oppe_ge0 ?oppe_itv_boundr_subproof.
    * rewrite oppe_itv_boundr_subproof.
      rewrite ext_mul_itv_boundl_subproof ?oppe_itv_boundl_subproof//.
      by rewrite opp_itv_ge0_subproof.
  + apply/and3P; split=> //=; rewrite -real_muleNN//.
    * by rewrite ext_mul_itv_boundl_subproof
        ?opp_itv_ge0_subproof ?oppe_itv_boundl_subproof.
    * by rewrite ext_mul_itv_boundr_subproof ?oppe_ge0 ?oppe_itv_boundr_subproof.
  + apply/and3P; split=> //=; rewrite -[x * y]oppeK.
    * rewrite -real_mulNe// oppe_itv_boundl_subproof.
      rewrite ext_mul_itv_boundr'_subproof ?oppe_ge0 ?oppe_itv_boundr_subproof//.
      exact: ltW.
    * rewrite oppeK -real_muleNN//.
      by rewrite ext_mul_itv_boundr'_subproof ?oppe_itv_boundr_subproof
                 ?oppe_ge0 ?oppe_cmp0 ?opp_itv_gt0_subproof// ltW.
- case: (ext_interval_signP yly yyu yr) => ylb yub ys.
  + by rewrite ys mule0.
  + apply/and3P; split=> //=; rewrite muleC mul_itv_boundrC_subproof.
    * rewrite -[y * x]oppeK -real_muleN// oppe_itv_boundl_subproof.
      rewrite ext_mul_itv_boundr'_subproof ?oppe_ge0 ?oppe_cmp0
              ?oppe_itv_boundr_subproof//.
      by rewrite opp_itv_gt0_subproof ltW.
    * by rewrite ext_mul_itv_boundr'_subproof// ltW.
  + apply/and3P; split=> //=; rewrite muleC mul_itv_boundrC_subproof.
    * rewrite -[y * x]oppeK -real_mulNe// oppe_itv_boundl_subproof.
      rewrite ext_mul_itv_boundr'_subproof ?oppe_ge0 ?oppe_itv_boundr_subproof//.
      exact: ltW.
    * rewrite -real_muleNN// ext_mul_itv_boundr'_subproof ?oppe_ge0
              ?oppe_cmp0 ?oppe_itv_boundr_subproof//.
      by rewrite opp_itv_gt0_subproof ltW.
apply/and3P; rewrite xyr/= ext_map_itv_bound_min ext_map_itv_bound_max.
rewrite (comparable_ge_min _ (comparable_ext_num_itv_bound_subproof _ _)).
rewrite (comparable_le_max _ (comparable_ext_num_itv_bound_subproof _ _)).
have [x0 | /ltW x0] : 0 <= x \/ x < 0; [|split=> //..].
  case: x xr {xlx xxu xyr xs} => [x||] /= xr.
  - by case: (comparable_leP xr) => x0; [left | right].
  - by left; rewrite le0y.
  - by right; rewrite ltNy0.
- apply/orP; right; rewrite -[x * y]oppeK -real_muleN// oppe_itv_boundl_subproof.
  rewrite ext_mul_itv_boundr'_subproof ?oppe_cmp0 ?oppe_itv_boundr_subproof//.
  by rewrite opp_itv_gt0_subproof ltW.
- by apply/orP; right; rewrite ext_mul_itv_boundr'_subproof// ltW.
- apply/orP; left; rewrite -[x * y]oppeK -real_mulNe// oppe_itv_boundl_subproof.
  rewrite ext_mul_itv_boundr'_subproof ?oppe_ge0 ?oppe_itv_boundr_subproof//.
  exact: ltW.
- apply/orP; left; rewrite -real_muleNN//.
  rewrite ext_mul_itv_boundr'_subproof ?oppe_ge0 ?oppe_cmp0
          ?oppe_itv_boundr_subproof//.
  by rewrite opp_itv_gt0_subproof ltW.
Qed.

Canonical mule_inum xi yi (x : ext_num_def xi) (y : ext_num_def yi) :=
  Itv.mk (mule_inum_subproof x y).

Definition abse_itv_subdef (i : Itv.t) : Itv.t :=
  match i with
  | Itv.Top => Itv.Real `[0%Z, +oo[
  | Itv.Real (Interval l u) =>
    match l with
    | BRight (Posz _) | BLeft (Posz (S _)) => Itv.Real `]0%Z, +oo[
    | _ => Itv.Real `[0%Z, +oo[
    end
  end.
Arguments abse_itv_subdef /.

Lemma abse_inum_subproof i (x : ext_num_def i)
    (r := abse_itv_subdef i) :
  ext_num_spec r `|x%:inum|.
Proof.
have: ext_num_sem `[0%Z, +oo[ `|x%:inum|.
  apply/and3P; split; rewrite ?bnd_simp ?abse_ge0//.
  by case: x%:inum => [x'||]; rewrite ?cmp0y// le_comparable ?abse_ge0.
have: 0 < x%:inum -> ext_num_sem `]0%Z, +oo[ `|x%:inum|.
  move=> xgt0; apply/and3P; split; rewrite ?bnd_simp//.
  - by case: x%:num => [x'||]; rewrite ?cmp0y// le_comparable ?abse_ge0.
  - case: x%:inum xgt0 => [x'|//|//]/=.
    by rewrite !lte_fin normr_gt0; apply: lt0r_neq0.
rewrite {}/r; case: i x => [//| [[[] [[//| l] | //] | //] u]] [x /=] + + _;
    move/and3P => [xr /= /[!bnd_simp]lx _]; apply.
- by apply: lt_le_trans lx; rewrite lte_fin ltr0z.
- by apply: le_lt_trans lx; rewrite lee_fin ler0z.
- by apply: lt_trans lx; rewrite lte_fin ltr0z.
Qed.

Canonical abse_inum i (x : ext_num_def i) := Itv.mk (abse_inum_subproof x).

Lemma ext_min_itv_boundl_subproof x1 x2 b1 b2 :
  (ext_num_itv_bound b1 <= BLeft x1)%O ->
  (ext_num_itv_bound b2 <= BLeft x2)%O ->
  (ext_num_itv_bound (Order.min b1 b2) <= BLeft (Order.min x1 x2))%O.
Proof.
case: (leP b1 b2) => [b1_le_b2 | /ltW b2_le_b1].
- have sb1_le_sb2 := eqbRL (ext_le_map_itv_bound _ _) b1_le_b2.
  by rewrite minElt; case: (x1 < x2)%O => [//|_]; apply: le_trans.
- have sb2_le_sb1 := eqbRL (ext_le_map_itv_bound _ _) b2_le_b1.
  by rewrite minElt; case: (x1 < x2)%O => [+ _|//]; apply: le_trans.
Qed.

Lemma ext_min_itv_boundr_subproof x1 x2 b1 b2 : (x1 >=< x2)%O ->
  (BRight x1 <= ext_num_itv_bound b1)%O ->
  (BRight x2 <= ext_num_itv_bound b2)%O ->
  (BRight (Order.min x1 x2) <= ext_num_itv_bound (Order.min b1 b2))%O.
Proof.
move=> x1_cmp_x2; case: (leP b1 b2) => [b1_le_b2 | /ltW b2_le_b1].
- have sb1_le_sb2 := eqbRL (ext_le_map_itv_bound _ _) b1_le_b2.
  by case: (comparable_leP x1_cmp_x2) => [//| /ltW ? + _]; apply: le_trans.
- have sb2_le_sb1 := eqbRL (ext_le_map_itv_bound _ _) b2_le_b1.
  by case: (comparable_leP x1_cmp_x2) => [? _ |//]; apply: le_trans.
Qed.

Lemma ext_min_inum_subproof (xi yi : Itv.t)
    (x : ext_num_def xi) (y : ext_num_def yi)
    (r := itv_real2_subdef min_itv_subdef xi yi) :
  ext_num_spec r (Order.min x%:inum y%:inum).
Proof.
apply: itv_real2_subproof (Itv.P x) (Itv.P y).
case: x y => [x /= _] [y /= _] => {xi yi r} -[lx ux] [ly uy]/=.
move=> /andP[xr /=/andP[lxx xux]] /andP[yr /=/andP[lyy yuy]].
apply/and3P; split.
- case: x y xr yr {lxx xux lyy yuy} => [x||] [y||]//=.
  + by move=> ? ?; apply: comparable_minr.
  + by move=> ? ?; rewrite real_miney.
  + by move=> ? ?; rewrite real_minNye.
- exact: ext_min_itv_boundl_subproof.
- by apply: ext_min_itv_boundr_subproof => //; apply: ereal_comparable.
Qed.

Lemma ext_max_itv_boundl_subproof x1 x2 b1 b2 : (x1 >=< x2)%O ->
  (ext_num_itv_bound b1 <= BLeft x1)%O ->
  (ext_num_itv_bound b2 <= BLeft x2)%O ->
  (ext_num_itv_bound (Order.max b1 b2) <= BLeft (Order.max x1 x2))%O.
Proof.
move=> x1_cmp_x2.
case: (leP b1 b2) => [b1_le_b2 | /ltW b2_le_b1].
- case: (comparable_leP x1_cmp_x2) => [//| /ltW ? _ sb2_x2].
  exact: le_trans sb2_x2 _.
- case: (comparable_leP x1_cmp_x2) => [? sb1_x1 _ |//].
  exact: le_trans sb1_x1 _.
Qed.

Lemma ext_max_itv_boundr_subproof x1 x2 b1 b2 :
  (BRight x1 <= ext_num_itv_bound b1)%O ->
  (BRight x2 <= ext_num_itv_bound b2)%O ->
  (BRight (Order.max x1 x2) <= ext_num_itv_bound (Order.max b1 b2))%O.
Proof.
case: (leP b1 b2) => [b1_le_b2 | /ltW b2_le_b1].
- have sb1_le_sb2 := eqbRL (ext_le_map_itv_bound _ _) b1_le_b2.
  by rewrite maxElt; case: ifP => [//|_ ? _]; apply: le_trans sb1_le_sb2.
- have sb2_le_sb1 := eqbRL (ext_le_map_itv_bound _ _) b2_le_b1.
  by rewrite maxElt; case: ifP => [_ _ ?|//]; apply: le_trans sb2_le_sb1.
Qed.

Lemma ext_max_inum_subproof (xi yi : Itv.t)
    (x : ext_num_def xi) (y : ext_num_def yi)
    (r := itv_real2_subdef max_itv_subdef xi yi) :
  ext_num_spec r (Order.max x%:inum y%:inum).
Proof.
apply: itv_real2_subproof (Itv.P x) (Itv.P y).
case: x y => [x /= _] [y /= _] => {xi yi r} -[lx ux] [ly uy]/=.
move=> /andP[xr /=/andP[lxx xux]] /andP[yr /=/andP[lyy yuy]].
apply/and3P; split.
- case: x y xr yr {lxx xux lyy yuy} => [x||] [y||]//=.
  + by move=> ? ?; apply: comparable_maxr.
  + by move=> ? ?; rewrite real_maxey.
  + by move=> ? ?; rewrite real_maxNye.
- by apply: ext_max_itv_boundl_subproof => //; apply: ereal_comparable.
- exact: ext_max_itv_boundr_subproof.
Qed.

Canonical ext_min_max_typ (R : numDomainType) :=
  MinMaxTyp ext_min_inum_subproof ext_max_inum_subproof.

End Itv.

Arguments gt0e {R i} _ {_}.
Arguments lte0 {R i} _ {_}.
Arguments ge0e {R i} _ {_}.
Arguments lee0 {R i} _ {_}.
Arguments cmp0e {R i} _ {_}.
Arguments neqe0 {R i} _ {_}.
Arguments ext_widen_itv {R i} _ {_ _}.

Definition posnume (R : numDomainType) of phant R :=
  Itv.def (@ext_num_sem R) (Itv.Real `]0%Z, +oo[).
Notation "{ 'posnum' '\bar' R }" := (@posnume _ (Phant R)) : type_scope.
Definition nonnege (R : numDomainType) of phant R :=
  Itv.def (@ext_num_sem R) (Itv.Real `[0%Z, +oo[).
Notation "{ 'nonneg' '\bar' R }" := (@nonnege _ (Phant R)) : type_scope.
Notation "x %:pos" := (ext_widen_itv x%:itv : {posnum \bar _}) (only parsing)
  : ereal_dual_scope.
Notation "x %:pos" := (ext_widen_itv x%:itv : {posnum \bar _}) (only parsing)
  : ereal_scope.
Notation "x %:pos" := (@ext_widen_itv _ _
    (@Itv.from _ _ _ (Phantom _ x)) (Itv.Real `]Posz 0, +oo[) _)
  (only printing) : ereal_dual_scope.
Notation "x %:pos" := (@ext_widen_itv _ _
    (@Itv.from _ _ _ (Phantom _ x)) (Itv.Real `]Posz 0, +oo[) _)
  (only printing) : ereal_scope.
Notation "x %:nng" := (ext_widen_itv x%:itv : {nonneg \bar _}) (only parsing)
  : ereal_dual_scope.
Notation "x %:nng" := (ext_widen_itv x%:itv : {nonneg \bar _}) (only parsing)
  : ereal_scope.
Notation "x %:nng" := (@ext_widen_itv _ _
    (@Itv.from _ _ _ (Phantom _ x)) (Itv.Real `[Posz 0, +oo[) _)
  (only printing) : ereal_dual_scope.
Notation "x %:nng" := (@ext_widen_itv _ _
    (@Itv.from _ _ _ (Phantom _ x)) (Itv.Real `[Posz 0, +oo[) _)
  (only printing) : ereal_scope.

#[export] Hint Extern 0 (is_true (0%R < _)%E) => solve [apply: gt0e] : core.
#[export] Hint Extern 0 (is_true (_ < 0%R)%E) => solve [apply: lte0] : core.
#[export] Hint Extern 0 (is_true (0%R <= _)%E) => solve [apply: ge0e] : core.
#[export] Hint Extern 0 (is_true (_ <= 0%R)%E) => solve [apply: lee0] : core.
#[export] Hint Extern 0 (is_true (0%R >=< _)%O) => solve [apply: cmp0e] : core.
#[export] Hint Extern 0 (is_true (_ != 0%R)%O) => solve [apply: neqe0] : core.

Section MorphNum.
Context {R : numDomainType} {i : Itv.t}.
Local Notation nR := (Itv.def (@ext_num_sem R) i).
Implicit Types (a : \bar R).

Lemma num_abse_eq0 a : (`|a|%:nng == 0%:E%:nng) = (a == 0).
Proof. by rewrite -abse_eq0. Qed.

End MorphNum.

Section MorphReal.
Context {R : numDomainType} {xi yi : interval int}.
Implicit Type x : (Itv.def (@ext_num_sem R) (Itv.Real xi)).
Implicit Type y : (Itv.def (@ext_num_sem R) (Itv.Real yi)).

Lemma num_lee_max a x y :
  a <= maxe x%:num y%:num = (a <= x%:num) || (a <= y%:num).
Proof. by rewrite -comparable_le_max// ereal_comparable. Qed.

Lemma num_gee_max a x y :
  maxe x%:num  y%:num <= a = (x%:num <= a) && (y%:num <= a).
Proof. by rewrite -comparable_ge_max// ereal_comparable. Qed.

Lemma num_lee_min a x y :
  a <= mine x%:num y%:num = (a <= x%:num) && (a <= y%:num).
Proof. by rewrite -comparable_le_min// ereal_comparable. Qed.

Lemma num_gee_min a x y :
  mine x%:num y%:num <= a = (x%:num <= a) || (y%:num <= a).
Proof. by rewrite -comparable_ge_min// ereal_comparable. Qed.

Lemma num_lte_max a x y :
  a < maxe x%:num y%:num = (a < x%:num) || (a < y%:num).
Proof. by rewrite -comparable_lt_max// ereal_comparable. Qed.

Lemma num_gte_max a x y :
  maxe x%:num  y%:num < a = (x%:num < a) && (y%:num < a).
Proof. by rewrite -comparable_gt_max// ereal_comparable. Qed.

Lemma num_lte_min a x y :
  a < mine x%:num y%:num = (a < x%:num) && (a < y%:num).
Proof. by rewrite -comparable_lt_min// ereal_comparable. Qed.

Lemma num_gte_min a x y :
  mine x%:num y%:num < a = (x%:num < a) || (y%:num < a).
Proof. by rewrite -comparable_gt_min// ereal_comparable. Qed.

End MorphReal.

Variant posnume_spec (R : numDomainType) (x : \bar R) :
  \bar R -> bool -> bool -> bool -> Type :=
| IsPinftyPosnume :
  posnume_spec x +oo false true true
| IsRealPosnume (p : {posnum R}) :
  posnume_spec x (p%:num%:E) false true true.

Lemma posnumeP (R : numDomainType) (x : \bar R) : 0 < x ->
  posnume_spec x x (x == 0) (0 <= x) (0 < x).
Proof.
case: x => [x|_|//]; last by rewrite le0y lt0y; exact: IsPinftyPosnume.
rewrite lte_fin lee_fin eqe => x_gt0.
rewrite x_gt0 (ltW x_gt0) (negbTE (lt0r_neq0 x_gt0)).
exact: IsRealPosnume (PosNum x_gt0).
Qed.

Variant nonnege_spec (R : numDomainType) (x : \bar R) :
  \bar R -> bool -> Type :=
| IsPinftyNonnege : nonnege_spec x +oo true
| IsRealNonnege (p : {nonneg R}) : nonnege_spec x (p%:num%:E) true.

Lemma nonnegeP (R : numDomainType) (x : \bar R) : 0 <= x ->
  nonnege_spec x x (0 <= x).
Proof.
case: x => [x|_|//]; last by rewrite le0y; exact: IsPinftyNonnege.
by rewrite lee_fin => /[dup] x_ge0 ->; exact: IsRealNonnege (NngNum x_ge0).
Qed.

Section contract_expand.
Variable R : realFieldType.
Implicit Types (x : \bar R) (r : R).
Local Open Scope ereal_scope.

Definition contract x : R :=
  match x with
  | r%:E => r / (1 + `|r|) | +oo => 1 | -oo => -1
  end.

Lemma contract_lt1 r : (`|contract r%:E| < 1)%R.
Proof.
rewrite normrM normrV ?unitfE //.
rewrite ltr_pdivrMr // ?mul1r//; last by rewrite gtr0_norm.
by rewrite [ltRHS]gtr0_norm ?ltrDr// ltr_pwDl.
Qed.

Lemma contract_le1 x : (`|contract x| <= 1)%R.
Proof.
by case: x => [r| |] /=; rewrite ?normrN1 ?normr1 // (ltW (contract_lt1 _)).
Qed.

Lemma contract0 : contract 0 = 0%R.
Proof. by rewrite /contract/= mul0r. Qed.

Lemma contractN x : contract (- x) = (- contract x)%R.
Proof. by case: x => //= [r|]; [ rewrite normrN mulNr | rewrite opprK]. Qed.

(* TODO: not exploited yet: expand is nondecreasing everywhere so it should be
   possible to use some of the homoRL/homoLR lemma where monoRL/monoLR do not
   apply *)
Definition expand r : \bar R :=
  if (r >= 1)%R then +oo else if (r <= -1)%R then -oo else (r / (1 - `|r|))%:E.

Lemma expand1 r : (1 <= r)%R -> expand r = +oo.
Proof. by move=> r1; rewrite /expand r1. Qed.

Lemma expandN r : expand (- r)%R = - expand r.
Proof.
rewrite /expand; case: ifPn => [r1|].
  rewrite ifF; [by rewrite ifT // -lerNr|apply/negbTE].
  by rewrite -ltNge -(opprK r) -ltrNl (lt_le_trans _ r1) // -subr_gt0 opprK.
rewrite -ltNge => r1; case: ifPn; rewrite lerNl opprK; [by move=> ->|].
by rewrite -ltNge leNgt => ->; rewrite leNgt -ltrNl r1 /= mulNr normrN.
Qed.

Lemma expandN1 r : (r <= -1)%R -> expand r = -oo.
Proof.
by rewrite lerNr => /expand1/eqP; rewrite expandN eqe_oppLR => /eqP.
Qed.

Lemma expand0 : expand 0%R = 0.
Proof. by rewrite /expand leNgt ltr01 /= oppr_ge0 leNgt ltr01 /= mul0r. Qed.

Lemma expandK : {in [pred r | `|r| <= 1]%R, cancel expand contract}.
Proof.
move=> r; rewrite inE le_eqVlt => /orP[|r1].
  rewrite eqr_norml => /andP[/orP[]/eqP->{r}] _;
    by [rewrite expand1|rewrite expandN1].
rewrite /expand 2!leNgt ltrNl; case/ltr_normlP : (r1) => -> -> /=.
have r_pneq0 : (1 + r / (1 - r) != 0)%R.
  rewrite -[X in (X + _)%R](@divrr _ (1 - r)%R) -?mulrDl; last first.
    by rewrite unitfE subr_eq0 eq_sym lt_eqF // ltr_normlW.
  by rewrite subrK mulf_neq0 // invr_eq0 subr_eq0 eq_sym lt_eqF // ltr_normlW.
have r_nneq0 : (1 - r / (1 + r) != 0)%R.
  rewrite -[X in (X + _)%R](@divrr _ (1 + r)%R) -?mulrBl; last first.
    by rewrite unitfE addrC addr_eq0 gt_eqF // ltrNnormlW.
  rewrite addrK mulf_neq0 // invr_eq0 addr_eq0 -eqr_oppLR eq_sym gt_eqF //.
  exact: ltrNnormlW.
wlog : r r1 r_pneq0 r_nneq0 / (0 <= r)%R => wlog_r0.
  have [r0|r0] := lerP 0 r; first by rewrite wlog_r0.
  move: (wlog_r0 (- r)%R).
  rewrite !(normrN, opprK, mulNr) oppr_ge0 => /(_ r1 r_nneq0 r_pneq0 (ltW r0)).
  by move/eqP; rewrite eqr_opp => /eqP.
rewrite /contract !ger0_norm //; last first.
  by rewrite divr_ge0 // subr_ge0 (le_trans _ (ltW r1)) // ler_norm.
apply: (@mulIr _ (1 + r / (1 - r))%R); first by rewrite unitfE.
rewrite -(mulrA (r / _)) mulVr ?unitfE // mulr1.
rewrite -[X in (X + _ / _)%R](@divrr _ (1 - r)%R) -?mulrDl ?subrK ?div1r //.
by rewrite unitfE subr_eq0 eq_sym lt_eqF // ltr_normlW.
Qed.

Lemma le_contract : {mono contract : x y / (x <= y)%O}.
Proof.
apply: le_mono; move=> -[r0 | | ] [r1 | _ | _] //=.
- rewrite lte_fin => r0r1; rewrite ltr_pdivrMr ?ltr_wpDr//.
  rewrite mulrAC ltr_pdivlMr ?ltr_wpDr// 2?mulrDr 2?mulr1.
  have [r10|?] := ler0P r1; last first.
    rewrite ltr_leD // mulrC; have [r00|//] := ler0P r0.
    by rewrite (@le_trans _ _ 0%R) // ?pmulr_rle0// mulr_ge0// ?oppr_ge0// ltW.
  have [?|r00] := ler0P r0; first by rewrite ltr_leD // 2!mulrN mulrC.
  by move: (le_lt_trans r10 (lt_trans r00 r0r1)); rewrite ltxx.
- by rewrite ltr_pdivrMr ?ltr_wpDr// mul1r ltr_pwDl // ler_norm.
- rewrite ltr_pdivlMr ?mulN1r ?ltr_wpDr// => _.
  by rewrite ltrNl ltr_pwDl // ler_normr lexx orbT.
Qed.

Definition lt_contract := leW_mono le_contract.
Definition contract_inj := mono_inj lexx le_anti le_contract.

Lemma le_expand_in : {in [pred r | `|r| <= 1]%R &,
  {mono expand : x y / (x <= y)%O}}.
Proof. exact: can_mono_in (onW_can_in predT expandK) _ (in2W le_contract). Qed.

Definition lt_expand := leW_mono_in le_expand_in.
Definition expand_inj := mono_inj_in lexx le_anti le_expand_in.

Lemma fine_expand r : (`|r| < 1)%R ->
  (fine (expand r))%:E = expand r.
Proof.
by move=> r1; rewrite /expand 2!leNgt ltrNl; case/ltr_normlP : r1 => -> ->.
Qed.

Lemma le_expand : {homo expand : x y / (x <= y)%O}.
Proof.
move=> x y xy; have [x1|] := lerP `|x| 1.
  have [y_le1|/ltW /expand1->] := leP y 1%R; last by rewrite leey.
  rewrite le_expand_in ?inE// ler_norml y_le1 (le_trans _ xy)//.
  by rewrite lerNl (ler_normlP _ _ _).
rewrite ltr_normr => /orP[|] x1; last first.
  by rewrite expandN1 // ?leNye // lerNr ltW.
by rewrite expand1; [rewrite expand1 // (le_trans _ xy) // ltW | exact: ltW].
Qed.

Lemma expand_eqoo r : (expand r == +oo) = (1 <= r)%R.
Proof. by rewrite /expand; case: ifP => //; case: ifP. Qed.

Lemma expand_eqNoo r : (expand r == -oo) = (r <= -1)%R.
Proof.
rewrite /expand; case: ifP => /= r1; last by case: ifP.
by apply/esym/negbTE; rewrite -ltNge (lt_le_trans _ r1) // -subr_gt0 opprK.
Qed.

End contract_expand.

Section ereal_PseudoMetric.
Context {R : realFieldType}.
Implicit Types (x y : \bar R) (r : R).

Definition ereal_ball x r y := (`|contract x - contract y| < r)%R.

Lemma ereal_ball_center x r : (0 < r)%R -> ereal_ball x r x.
Proof. by move=> e0; rewrite /ereal_ball subrr normr0. Qed.

Lemma ereal_ball_sym x y r : ereal_ball x r y -> ereal_ball y r x.
Proof. by rewrite /ereal_ball distrC. Qed.

Lemma ereal_ball_triangle x y z r1 r2 :
  ereal_ball x r1 y -> ereal_ball y r2 z -> ereal_ball x (r1 + r2) z.
Proof.
rewrite /ereal_ball => h1 h2; rewrite -[X in (X - _)%R](subrK (contract y)).
by rewrite -addrA (le_lt_trans (ler_normD _ _)) // ltrD.
Qed.

Lemma ereal_ballN x y (e : {posnum R}) :
  ereal_ball (- x) e%:num (- y) -> ereal_ball x e%:num y.
Proof. by rewrite /ereal_ball 2!contractN opprK -opprB normrN addrC. Qed.

Lemma ereal_ball_ninfty_oversize (e : {posnum R}) x :
  (2 < e%:num)%R -> ereal_ball -oo e%:num x.
Proof.
move=> e2; rewrite /ereal_ball /= (le_lt_trans _ e2) // -opprB normrN opprK.
rewrite (le_trans (ler_normD _ _)) // normr1 -lerBrDr.
by rewrite (le_trans (contract_le1 _)) // (_ : 2 = 1 + 1)%R // addrK.
Qed.

Lemma contract_ereal_ball_pinfty r (e : {posnum R}) :
  (1 < contract r%:E + e%:num)%R -> ereal_ball r%:E e%:num +oo.
Proof.
move=> re1; rewrite /ereal_ball; rewrite [contract +oo]/= ler0_norm; last first.
  by rewrite subr_le0; case/ler_normlP: (contract_le1 r%:E).
by rewrite opprB ltrBlDl.
Qed.

End ereal_PseudoMetric.

(* TODO: generalize to numFieldType? *)
Lemma lt_ereal_nbhs (R : realFieldType) (a b : \bar R) (r : R) :
  a < r%:E -> r%:E < b ->
  exists delta : {posnum R},
    forall y, (`|y - r| < delta%:num)%R -> (a < y%:E) && (y%:E < b).
Proof.
move=> [:wlog]; case: a b => [a||] [b||] //= ltax ltxb.
- move: a b ltax ltxb; abstract: wlog. (*BUG*)
  move=> {}a {}b ltxa ltxb.
  have m_gt0 : (Num.min ((r - a) / 2) ((b - r) / 2) > 0)%R.
    by rewrite lt_min !divr_gt0 // ?subr_gt0.
  exists (PosNum m_gt0) => y //=; rewrite lt_min !ltr_distl.
  move=> /andP[/andP[ay _] /andP[_ yb]].
  rewrite 2!lte_fin (lt_trans _ ay) ?(lt_trans yb) //=.
    rewrite -subr_gt0 opprD addrA {1}[(b - r)%R]splitr addrK.
    by rewrite divr_gt0 ?subr_gt0.
  by rewrite -subr_gt0 addrAC {1}[(r - a)%R]splitr addrK divr_gt0 ?subr_gt0.
- have [//||d dP] := wlog a (r + 1)%R; rewrite ?lte_fin ?ltrDl //.
  by exists d => y /dP /andP[->] /= /lt_le_trans; apply; rewrite leey.
- have [//||d dP] := wlog (r - 1)%R b; rewrite ?lte_fin ?gtrDl ?ltrN10 //.
  by exists d => y /dP /andP[_ ->] /=; rewrite ltNyr.
- by exists 1%:pos%R => ? ?; rewrite ltNyr ltry.
Qed.

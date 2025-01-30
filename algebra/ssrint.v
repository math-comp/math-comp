(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice seq.
From mathcomp Require Import fintype finfun bigop order ssralg countalg.
From mathcomp Require Import orderedzmod numdomain numfield poly.

(******************************************************************************)
(* This file develops a basic theory of signed integers, defining:            *)
(*         int == the type of signed integers, with two constructors Posz for *)
(*                non-negative integers and Negz for negative integers. It    *)
(*                supports the realDomainType interface (and its parents).    *)
(*        n%:Z == explicit cast from nat to int (:= Posz n); displayed as n.  *)
(*                However (Posz m = Posz n) is displayed as (m = n :> int)    *)
(*                (and so are ==, != and <>)                                  *)
(*                Lemma NegzE : turns (Negz n) into - n.+1%:Z.                *)
(*    <number> == <number> as an int, with <number> an optional minus sign    *)
(*                followed by a sequence of digits. This notation is in       *)
(*                int_scope (delimited with %Z).                              *)
(*      x *~ m == m times x, with m : int;                                    *)
(*                convertible to x *+ n if m is Posz n                        *)
(*                convertible to x *- n.+1 if m is Negz n.                    *)
(*       m%:~R == the image of m : int in a generic ring (:= 1 *~ m).         *)
(*       x ^ m == x to the m, with m : int;                                   *)
(*                convertible to x ^+ n if m is Posz n                        *)
(*                convertible to x ^- n.+1 if m is Negz n.                    *)
(*       sgz x == sign of x : R,                                              *)
(*                equals (0 : int) if and only x == 0,                        *)
(*                equals (1 : int) if x is positive                           *)
(*                and (-1 : int) otherwise.                                   *)
(*      `|m|%N == the n : nat such that `|m|%R = n%:Z, for m : int.           *)
(*  `|m - n|%N == the distance between m and n; the '-' is specialized to     *)
(*                the int type, so m and n can be either of type nat or int   *)
(*                thanks to the Posz coercion; m and n are however parsed in  *)
(*                the %N scope. The IntDist submodule provides this notation  *)
(*                and the corresponding theory independently of the rest of   *)
(*                of the int and ssralg libraries (and notations).            *)
(* Warning: due to the declaration of Posz as a coercion, two terms might be  *)
(* displayed the same while not being convertible, for instance:              *)
(* (Posz (x - y)) and (Posz x) - (Posz y) for x, y : nat.                     *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope int_scope.
Declare Scope distn_scope.
Declare Scope rat_scope.

Reserved Notation "n %:Z" (at level 2, left associativity, format "n %:Z").
Reserved Notation "n = m :> 'int'"
  (at level 70, m at next level, format "n  =  m  :>  'int'").
Reserved Notation "n == m :> 'int'"
  (at level 70, m at next level, format "n  ==  m  :>  'int'").
Reserved Notation "n != m :> 'int'"
  (at level 70, m at next level, format "n  !=  m  :>  'int'").
Reserved Notation "n <> m :> 'int'"
  (at level 70, m at next level, format "n  <>  m  :>  'int'").

Import Order.TTheory GRing.Theory.
Import orderedzmod.Num.Theory numdomain.Num.Theory numfield.Num.Theory.
Delimit Scope int_scope with Z.
Local Open Scope int_scope.

(* Defining int *)
Variant int : Set := Posz of nat | Negz of nat.
(* This must be deferred to module DistInt to work around the design flaws of *)
(* the Coq module system.                                                     *)
(* Coercion Posz : nat >-> int. *)

Notation "n %:Z" := (Posz n) (only parsing) : int_scope.
Notation "n %:Z" := (Posz n) (only parsing) : ring_scope.

Notation "n = m :> 'int'"  := (@eq int n%Z m%Z) (only parsing)  : ring_scope.
Notation "n = m :> 'int'"  := (Posz n = Posz m) (only printing)  : ring_scope.
Notation "n == m :> 'int'" := ((n%Z : int) == (m%Z : int)) (only parsing)
  : ring_scope.
Notation "n == m :> 'int'" := (Posz n == Posz m) (only printing) : ring_scope.
Notation "n != m :> 'int'" := ((n%Z : int) != (m%Z : int)) (only parsing)
  : ring_scope.
Notation "n != m :> 'int'" := (Posz n != Posz m) (only printing) : ring_scope.
Notation "n <> m :> 'int'" := (not (@eq int n%Z m%Z)) (only parsing)
  : ring_scope.
Notation "n <> m :> 'int'" := (Posz n <> Posz m) (only printing) : ring_scope.

Definition parse_int (x : Number.int) : int :=
  match x with
  | Number.IntDecimal (Decimal.Pos u) => Posz (Nat.of_uint u)
  | Number.IntDecimal (Decimal.Neg u) => Negz (Nat.of_uint u).-1
  | Number.IntHexadecimal (Hexadecimal.Pos u) => Posz (Nat.of_hex_uint u)
  | Number.IntHexadecimal (Hexadecimal.Neg u) => Negz (Nat.of_hex_uint u).-1
  end.

Definition print_int (x : int) : Number.int :=
  match x with
  | Posz n => Number.IntDecimal (Decimal.Pos (Nat.to_uint n))
  | Negz n => Number.IntDecimal (Decimal.Neg (Nat.to_uint n.+1))
  end.

Number Notation int parse_int print_int : int_scope.

Definition natsum_of_int (m : int) : nat + nat :=
  match m with Posz p => inl _ p | Negz n => inr _ n end.

Definition int_of_natsum (m : nat + nat) :=
  match m with inl p => Posz p | inr n => Negz n end.

Lemma natsum_of_intK : cancel natsum_of_int int_of_natsum.
Proof. by case. Qed.

HB.instance Definition _ := Countable.copy int (can_type natsum_of_intK).

Lemma eqz_nat (m n : nat) : (m%:Z == n%:Z) = (m == n). Proof. by []. Qed.

Module intZmod.
Section intZmod.

Definition addz (m n : int) :=
  match m, n with
    | Posz m', Posz n' => Posz (m' + n')
    | Negz m', Negz n' => Negz (m' + n').+1
    | Posz m', Negz n' => if n' < m' then Posz (m' - n'.+1) else Negz (n' - m')
    | Negz n', Posz m' => if n' < m' then Posz (m' - n'.+1) else Negz (n' - m')
  end.

Definition oppz m :=
  match m with
    | Posz n => if n is (n'.+1)%N then Negz n' else Posz 0
    | Negz n => Posz (n.+1)%N
  end.
Arguments oppz : simpl never.

Local Notation "-%Z" := (@oppz) : int_scope.
Local Notation "- x" := (oppz x) : int_scope.
Local Notation "+%Z" := (@addz) : int_scope.
Local Notation "x + y" := (addz x y) : int_scope.
Local Notation "x - y" := (x + - y) : int_scope.

Lemma PoszD : {morph Posz : m n / (m + n)%N >-> m + n}. Proof. by []. Qed.

Local Coercion Posz : nat >-> int.

Lemma NegzE (n : nat) : Negz n = - n.+1. Proof. by []. Qed.

Lemma int_rect (P : int -> Type) :
  P 0 -> (forall n : nat, P n -> P (n.+1))
  -> (forall n : nat, P (- n) -> P (- (n.+1)))
  -> forall n : int, P n.
Proof.
by move=> P0 hPp hPn []; elim=> [|n ihn]//; do ?[apply: hPn | apply: hPp].
Qed.

Definition int_rec := int_rect.
Definition int_ind := int_rect.

Variant int_spec (x : int) : int -> Type :=
| ZintNull of x = 0 : int_spec x 0
| ZintPos n of x = n.+1 : int_spec x n.+1
| ZintNeg n of x = - (n.+1)%:Z : int_spec x (- n.+1).

Lemma intP x : int_spec x x. Proof. by move: x=> [] []; constructor. Qed.

Lemma addzC : commutative addz.
Proof. by move=> [] m [] n //=; rewrite addnC. Qed.

Lemma add0z : left_id 0 addz. Proof. by do 2?case. Qed.

Lemma oppzK : involutive oppz. Proof. by do 2?case. Qed.

Lemma oppzD : {morph oppz : m n / m + n}.
Proof.
by move=> [[|n]|n] [[|m]|m] /=; rewrite ?addn0 ?subn0 ?addnS //;
  rewrite !NegzE !ltnS !subSS; case: ltngtP => [?|?|->];
  rewrite ?subnn // ?oppzK ?subnS ?prednK // subn_gt0.
Qed.

Lemma add1Pz (n : int) : 1 + (n - 1) = n.
Proof. by case: (intP n)=> // n' /= _; rewrite ?(subn1, addn0). Qed.

Lemma subSz1 (n : int) : 1 + n - 1 = n.
Proof.
by apply: (inv_inj oppzK); rewrite addzC !oppzD oppzK [_ - n]addzC add1Pz.
Qed.

Lemma addSnz (m : nat) (n : int) : m.+1%N + n = 1 + (m + n).
Proof.
move: m n=> [|m] [] [|n] //=; rewrite ?add1n ?subn1 // !(ltnS, subSS).
case: ltngtP=> hnm /=; rewrite ?hnm ?subnn //.
  by rewrite subnS add1n prednK ?subn_gt0.
by rewrite ltnS leqn0 subn_eq0 leqNgt hnm /= subnS subn1.
Qed.

Lemma addSz (m n : int) : (1 + m) + n = 1 + (m + n).
Proof.
case: m => [] m; first by rewrite -PoszD add1n addSnz.
rewrite !NegzE; apply: (inv_inj oppzK).
rewrite !oppzD !oppzK addSnz [-1%:Z + _]addzC addSnz add1Pz.
by rewrite [-1%:Z + _]addzC subSz1.
Qed.

Lemma addPz (m n : int) : (m - 1) + n = (m + n) - 1.
Proof.
by apply: (inv_inj oppzK); rewrite !oppzD oppzK [_ + 1]addzC addSz addzC.
Qed.

Lemma addzA : associative addz.
Proof.
elim=> [|m ihm|m ihm] n p; first by rewrite !add0z.
  by rewrite -add1n PoszD !addSz ihm.
by rewrite -add1n addnC PoszD oppzD !addPz ihm.
Qed.

Lemma addNz : left_inverse (0:int) oppz addz. Proof. by do 3?elim. Qed.

Lemma predn_int (n : nat) : 0 < n -> n.-1%:Z = n - 1.
Proof. by case: n => //= n _; rewrite subn1. Qed.

Definition Mixin := GRing.isZmodule.Build int addzA addzC add0z addNz.

End intZmod.
Arguments oppz : simpl never.
End intZmod.

HB.instance Definition _ := intZmod.Mixin.

HB.instance Definition _ := GRing.isSemiAdditive.Build nat int Posz
  (erefl, intZmod.PoszD).

Local Open Scope ring_scope.

Section intZmoduleTheory.

Local Coercion Posz : nat >-> int.

Lemma PoszD : {morph Posz : n m / (n + m)%N >-> n + m}. Proof. by []. Qed.

Lemma NegzE (n : nat) : Negz n = -(n.+1)%:Z. Proof. by []. Qed.

Lemma int_rect (P : int -> Type) :
  P 0 -> (forall n : nat, P n -> P (n.+1)%N)
  -> (forall n : nat, P (- (n%:Z)) -> P (- (n.+1%N%:Z)))
  -> forall n : int, P n.
Proof.
by move=> P0 hPp hPn []; elim=> [|n ihn]//; do ?[apply: hPn | apply: hPp].
Qed.

Definition int_rec := int_rect.
Definition int_ind := int_rect.

Variant int_spec (x : int) : int -> Type :=
| ZintNull : int_spec x 0
| ZintPos n : int_spec x n.+1
| ZintNeg n : int_spec x (- (n.+1)%:Z).

Lemma intP x : int_spec x x.
Proof. by move: x=> [] [] *; rewrite ?NegzE; constructor. Qed.

Definition oppzD := @opprD int.

Lemma subzn (m n : nat) : (n <= m)%N -> m%:Z - n%:Z = (m - n)%N.
Proof.
elim: n=> //= [|n ihn] hmn; first by rewrite subr0 subn0.
rewrite subnS -addn1 !PoszD opprD addrA ihn 1?ltnW //.
by rewrite intZmod.predn_int // subn_gt0.
Qed.

Lemma subzSS (m n : nat) : m.+1%:Z - n.+1%:Z = m%:Z - n%:Z.
Proof. by elim: n m=> [|n ihn] m //; rewrite !subzn. Qed.

End intZmoduleTheory.

Module intRing.
Section intRing.

Local Coercion Posz : nat >-> int.

Definition mulz (m n : int) :=
  match m, n with
    | Posz m', Posz n' => (m' * n')%N%:Z
    | Negz m', Negz n' => (m'.+1%N * n'.+1%N)%N%:Z
    | Posz m', Negz n' => - (m' * (n'.+1%N))%N%:Z
    | Negz n', Posz m' => - (m' * (n'.+1%N))%N%:Z
  end.

Local Notation "*%Z" := (@mulz) : int_scope.
Local Notation "x * y" := (mulz x y) : int_scope.

Lemma mul0z : left_zero 0 *%Z.
Proof. by case=> [n|[|n]] //=; rewrite muln0. Qed.

Lemma mulzC : commutative mulz.
Proof. by move=> [] m [] n //=; rewrite mulnC. Qed.

Lemma mulz0 : right_zero 0 *%Z.
Proof. by move=> x; rewrite mulzC mul0z. Qed.

Lemma mulzN (m n : int) : (m * (- n))%Z = - (m * n)%Z.
Proof.
by case: (intP m)=> {m} [|m|m]; rewrite ?mul0z //;
case: (intP n)=> {n} [|n|n]; rewrite ?mulz0 //= mulnC.
Qed.

Lemma mulNz (m n : int) : ((- m) * n)%Z = - (m * n)%Z.
Proof. by rewrite mulzC mulzN mulzC. Qed.

Lemma mulzA : associative mulz.
Proof.
by move=> [] m [] n [] p; rewrite ?NegzE ?(mulnA,mulNz,mulzN,opprK) //= ?mulnA.
Qed.

Lemma mul1z : left_id 1%Z mulz.
Proof. by case=> [[|n]|n] //=; rewrite ?mul1n// plusE addn0. Qed.

Lemma mulzS (x : int) (n : nat) : (x * n.+1%:Z)%Z = x + (x * n)%Z.
Proof.
by case: (intP x)=> [|m'|m'] //=; [rewrite mulnS|rewrite mulSn -opprD].
Qed.

Lemma mulz_addl : left_distributive mulz (+%R).
Proof.
move=> x y z; elim: z=> [|n|n]; first by rewrite !(mul0z,mulzC).
  by rewrite !mulzS=> ->; rewrite !addrA [X in X + _]addrAC.
rewrite !mulzN !mulzS -!opprD=> /oppr_inj->.
by rewrite !addrA [X in X + _]addrAC.
Qed.

Lemma nonzero1z : 1%Z != 0. Proof. by []. Qed.

Definition comMixin := GRing.Zmodule_isComNzRing.Build int
  mulzA mulzC mul1z mulz_addl nonzero1z.

End intRing.
End intRing.

HB.instance Definition _ := intRing.comMixin.

Section intRingTheory.

Implicit Types m n : int.
Local Coercion Posz : nat >-> int.

Lemma PoszM : {morph Posz : n m / (n * m)%N >-> n * m}. Proof. by []. Qed.

Lemma intS (n : nat) : n.+1%:Z = 1 + n%:Z. Proof. by rewrite -PoszD. Qed.

Lemma predn_int (n : nat) : (0 < n)%N -> n.-1%:Z = n%:Z - 1.
Proof. exact: intZmod.predn_int. Qed.

End intRingTheory.

HB.instance Definition _ := GRing.isMultiplicative.Build nat int Posz
  (PoszM, erefl).

Module intUnitRing.
Section intUnitRing.
Implicit Types m n : int.
Local Coercion Posz : nat >-> int.

Definition unitz := [qualify a n : int | (n == 1) || (n == -1)].
Definition invz n : int := n.

Lemma mulVz : {in unitz, left_inverse 1%R invz *%R}.
Proof. by move=> n /pred2P[] ->. Qed.

Lemma mulzn_eq1 m (n : nat) : (m * n == 1) = (m == 1) && (n == 1).
Proof. by case: m => m /=; [rewrite -PoszM [_==_]muln_eq1 | case: n]. Qed.

Lemma unitzPl m n : n * m = 1 -> m \is a unitz.
Proof.
rewrite qualifE => /eqP.
by case: m => m; rewrite ?NegzE ?mulrN -?mulNr mulzn_eq1 => /andP[_ /eqP->].
Qed.

Lemma invz_out : {in [predC unitz], invz =1 id}.
Proof. exact. Qed.

Lemma idomain_axiomz m n : m * n = 0 -> (m == 0) || (n == 0).
Proof. by case: m n => [[|m]|m] [[|n]|n]. Qed.

Definition comMixin := GRing.ComNzRing_hasMulInverse.Build int
  mulVz unitzPl invz_out.

End intUnitRing.
End intUnitRing.

HB.instance Definition _ := intUnitRing.comMixin.
HB.instance Definition _ := GRing.ComUnitRing_isIntegral.Build int
  intUnitRing.idomain_axiomz.

Definition absz m := match m with Posz p => p | Negz n => n.+1 end.
Notation "m - n" := (@GRing.add int m%N (@GRing.opp int n%N)) : distn_scope.
Arguments absz m%distn_scope.
Local Notation "`| m |" := (absz m) : nat_scope.

Module intOrdered.
Section intOrdered.
Implicit Types m n p : int.
Local Coercion Posz : nat >-> int.

Local Notation normz m := (absz m)%:Z.

Definition lez m n :=
  match m, n with
    | Posz m', Posz n' => (m' <= n')%N
    | Posz m', Negz n' => false
    | Negz m', Posz n' => true
    | Negz m', Negz n' => (n' <= m')%N
  end.

Definition ltz m n :=
  match m, n with
    | Posz m', Posz n' => (m' < n')%N
    | Posz m', Negz n' => false
    | Negz m', Posz n' => true
    | Negz m', Negz n' => (n' < m')%N
  end.

Fact lez_add m n : lez 0 m -> lez 0 n -> lez 0 (m + n).
Proof. by case: m n => [] m [] n. Qed.

Fact lez_mul m n : lez 0 m -> lez 0 n -> lez 0 (m * n).
Proof. by case: m n => [] m [] n. Qed.

Fact lez_anti m : lez 0 m -> lez m 0 -> m = 0.
Proof. by case: m; first case. Qed.

Lemma subz_ge0 m n : lez 0 (n - m) = lez m n.
Proof.
case: (intP m); case: (intP n)=> // {}m {}n /=;
rewrite ?ltnS -?opprD ?opprB ?subzSS; case: leqP=> // hmn;
by [ rewrite subzn //
   | rewrite -opprB subzn ?(ltnW hmn) //;
      move: hmn; rewrite -subn_gt0; case: (_ - _)%N].
Qed.

Fact lez_total m n : lez m n || lez n m.
Proof. by move: m n => [] m [] n //=; apply: leq_total. Qed.

Fact normzN m : normz (- m) = normz m.
Proof. by case: m => // -[]. Qed.

Fact gez0_norm m : lez 0 m -> normz m = m.
Proof. by case: m. Qed.

Fact ltz_def m n : (ltz m n) = (n != m) && (lez m n).
Proof.
by move: m n => [] m [] n //=; rewrite (ltn_neqAle, leq_eqVlt) // eq_sym.
Qed.

Definition Mixin := Num.IntegralDomain_isLeReal.Build int
  lez_add lez_mul lez_anti subz_ge0 (lez_total 0) normzN gez0_norm ltz_def.

End intOrdered.
End intOrdered.

HB.instance Definition _ := intOrdered.Mixin.

Section intOrderedTheory.

Local Coercion Posz : nat >-> int.
Implicit Types m n p : nat.
Implicit Types x y z : int.

Lemma lez_nat m n : (m <= n :> int) = (m <= n)%N. Proof. by []. Qed.

Lemma ltz_nat  m n : (m < n :> int) = (m < n)%N.
Proof. by rewrite ltnNge ltNge lez_nat. Qed.

Definition ltez_nat := (lez_nat, ltz_nat).

Lemma leNz_nat m n : (- m%:Z <= n). Proof. by case: m. Qed.

Lemma ltNz_nat m n : (- m%:Z < n) = (m != 0) || (n != 0).
Proof. by move: m n=> [|?] []. Qed.

Definition lteNz_nat := (leNz_nat, ltNz_nat).

Lemma lezN_nat m n : (m%:Z <= - n%:Z) = (m == 0) && (n == 0).
Proof. by move: m n=> [|?] []. Qed.

Lemma ltzN_nat m n : (m%:Z < - n%:Z) = false.
Proof. by move: m n=> [|?] []. Qed.

Lemma le0z_nat n : 0 <= n :> int. Proof. by []. Qed.

Lemma lez0_nat n : n <= 0 :> int = (n == 0 :> nat). Proof. by elim: n. Qed.

Definition ltezN_nat := (lezN_nat, ltzN_nat).
Definition ltez_natE := (ltez_nat, lteNz_nat, ltezN_nat, le0z_nat, lez0_nat).

Lemma gtz0_ge1 x : (0 < x) = (1 <= x). Proof. by case: (intP x). Qed.

Lemma lez1D x y : (1 + x <= y) = (x < y).
Proof. by rewrite -subr_gt0 gtz0_ge1 lterBDr. Qed.

Lemma lezD1 x y : (x + 1 <= y) = (x < y).
Proof. by rewrite addrC lez1D. Qed.

Lemma ltz1D x y : (x < 1 + y) = (x <= y).
Proof. by rewrite -lez1D lerD2l. Qed.

Lemma ltzD1 x y : (x < y + 1) = (x <= y).
Proof. by rewrite -lezD1 lerD2r. Qed.

End intOrderedTheory.

Bind Scope ring_scope with int.

(* definition of intmul *)
Definition intmul (R : zmodType) (x : R) (n : int) :=
  match n with
    | Posz n => (x *+ n)%R
    | Negz n => (x *- (n.+1))%R
  end.
Arguments intmul : simpl never.

Notation "*~%R" := (@intmul _) (at level 0, format " *~%R") : function_scope.
Notation "x *~ n" := (intmul x n)
  (at level 40, left associativity, format "x  *~  n") : ring_scope.
Notation intr := ( *~%R 1).
Notation "n %:~R" := (1 *~ n)%R
  (at level 2, left associativity, format "n %:~R")  : ring_scope.

Lemma pmulrn (R : zmodType) (x : R) (n : nat) : x *+ n = x *~ n%:Z.
Proof. by []. Qed.

Lemma nmulrn (R : zmodType) (x : R) (n : nat) : x *- n = x *~ - n%:Z.
Proof. by case: n; rewrite // oppr0. Qed.

Section ZintLmod.

Definition zmodule (M : Type) : Type := M.
Local Notation "M ^z" := (zmodule M) (at level 2, format "M ^z") : type_scope.
Local Coercion Posz : nat >-> int.

Variable M : zmodType.

Implicit Types m n : int.
Implicit Types x y z : M.

Fact mulrzA_C m n x : (x *~ n) *~ m = x *~ (m * n).
Proof.
elim: m=> [|m _|m _]; elim: n=> [|n _|n _]; rewrite /intmul //=;
rewrite ?(muln0, mulr0n, mul0rn, oppr0, mulNrn, opprK) //;
 do ?by rewrite mulnC mulrnA.
* by rewrite -mulrnA mulnC.
* by rewrite -mulrnA.
Qed.

Fact mulrzAC m n x : (x *~ n) *~ m = (x *~ m) *~ n.
Proof. by rewrite !mulrzA_C mulrC. Qed.

Fact mulr1z (x : M) : x *~ 1 = x. Proof. by []. Qed.

Fact mulrzDl m : {morph ( *~%R^~ m : M -> M) : x y / x + y}.
Proof. by case: m => m x y; rewrite /intmul mulrnDl // opprD. Qed.

Lemma mulrzBl_nat (m n : nat) x : x *~ (m%:Z - n%:Z) = x *~ m - x *~ n.
Proof.
wlog/subnK <-: m n / (n <= m)%N; last by rewrite -!pmulrn PoszD mulrnDr !addrK.
have [hmn|/ltnW hmn] := leqP n m; first exact.
by rewrite -[in LHS]opprB -[RHS]opprB subzn // -nmulrn pmulrn -subzn // => ->.
Qed.

Fact mulrzDr x : {morph *~%R x : m n / m + n}.
Proof.
by case=> []m []n; rewrite ?NegzE /intmul /= -/(intmul _ _) -?opprD;
  rewrite -?[- _ + _]addrC ?mulrzBl_nat // -mulrnDr // addnS.
Qed.

HB.instance Definition _ := GRing.Zmodule.on M^z.  (* FIXME, the error message below "nomsg" when we forget this line is not very helpful *)
HB.instance Definition _ := @GRing.Zmodule_isLmodule.Build _ M^z
  (fun n x => x *~ n) mulrzA_C mulr1z mulrzDl mulrzDr.

Lemma scalezrE n x : n *: (x : M^z) = x *~ n. Proof. by []. Qed.

Lemma mulrzA x m n :  x *~ (m * n) = x *~ m *~ n.
Proof. by rewrite -!scalezrE scalerA mulrC. Qed.

Lemma mulr0z x : x *~ 0 = 0. Proof. by []. Qed.

Lemma mul0rz n : 0 *~ n = 0 :> M.
Proof. by rewrite -scalezrE scaler0. Qed.

Lemma mulrNz x n : x *~ (- n) = - (x *~ n).
Proof. by rewrite -scalezrE scaleNr. Qed.

Lemma mulrN1z x : x *~ (- 1) = - x. Proof. by rewrite -scalezrE scaleN1r. Qed.

Lemma mulNrz x n : (- x) *~ n = - (x *~ n).
Proof. by rewrite -scalezrE scalerN. Qed.

Lemma mulrzBr x m n : x *~ (m - n) = x *~ m - x *~ n.
Proof. by rewrite -scalezrE scalerBl. Qed.

Lemma mulrzBl x y n : (x - y) *~ n = x *~ n - y *~ n.
Proof. by rewrite -scalezrE scalerBr. Qed.

Lemma mulrz_nat (n : nat) x : x *~ n%:R = x *+ n.
Proof. by rewrite -scalezrE scaler_nat. Qed.

Lemma mulrz_sumr : forall x I r (P : pred I) F,
  x *~ (\sum_(i <- r | P i) F i) = \sum_(i <- r | P i) x *~ F i.
Proof. by rewrite -/M^z; apply: scaler_suml. Qed.

Lemma mulrz_suml : forall n I r (P : pred I) (F : I -> M),
  (\sum_(i <- r | P i) F i) *~ n= \sum_(i <- r | P i) F i *~ n.
Proof. by rewrite -/M^z; apply: scaler_sumr. Qed.

HB.instance Definition _ (x : M) := GRing.isAdditive.Build int M ( *~%R x)
  (@mulrzBr x).

End ZintLmod.

#[deprecated(since="mathcomp 2.3.0", note="Use mulrzDl instead.")]
Notation mulrzDl_tmp := mulrzDl.
#[deprecated(since="mathcomp 2.3.0", note="Use mulrzDr instead.")]
Notation mulrzDr_tmp := mulrzDr.

Lemma ffunMzE (I : finType) (M : zmodType) (f : {ffun I -> M}) z x :
  (f *~ z) x = f x *~ z.
Proof. by case: z => n; rewrite ?ffunE ffunMnE. Qed.

Lemma intz (n : int) : n%:~R = n.
Proof. by case: n => n; rewrite ?NegzE /intmul/= -(rmorphMn Posz)/= natn. Qed.

Lemma natz (n : nat) : n%:R = n%:Z :> int.
Proof. by rewrite pmulrn intz. Qed.

Section RintMod.

Local Coercion Posz : nat >-> int.
Variable R : pzRingType.

Implicit Types m n : int.
Implicit Types x y z : R.

Lemma mulrzAl n x y : (x *~ n) * y = (x * y) *~ n.
Proof. by case: n => n; rewrite ?mulNr mulrnAl. Qed.

Lemma mulrzAr n x y : x * (y *~ n) = (x * y) *~ n.
Proof. by case: n => n; rewrite ?mulrN mulrnAr. Qed.

Lemma mulrzl x n : n%:~R * x = x *~ n. Proof. by rewrite mulrzAl mul1r. Qed.

Lemma mulrzr x n : x * n%:~R = x *~ n. Proof. by rewrite mulrzAr mulr1. Qed.

Lemma mulNrNz n x : (- x) *~ (- n) = x *~ n.
Proof. by rewrite mulNrz mulrNz opprK. Qed.

Lemma mulrbz x (b : bool) : x *~ b = (if b then x else 0).
Proof. by case: b. Qed.

Lemma intrN n : (- n)%:~R = - n%:~R :> R. Proof. exact: mulrNz. Qed.

Lemma intrD m n : (m + n)%:~R = m%:~R + n%:~R :> R. Proof. exact: mulrzDr. Qed.

Lemma intrB m n : (m - n)%:~R = m%:~R - n%:~R :> R. Proof. exact: mulrzBr. Qed.

Lemma intrM m n : (m * n)%:~R = m%:~R * n%:~R :> R.
Proof. by rewrite mulrzA -mulrzr. Qed.

Lemma intmul1_is_multiplicative : multiplicative ( *~%R (1 : R)).
Proof. by split; move=> // x y /=; rewrite ?intrD ?mulrNz ?intrM. Qed.
HB.instance Definition _ := GRing.isMultiplicative.Build int R ( *~%R 1)
  intmul1_is_multiplicative.

Lemma mulr2z n : n *~ 2 = n + n. Proof. exact: mulr2n. Qed.

End RintMod.

Lemma mulrzz m n : m *~ n = m * n. Proof. by rewrite -mulrzr intz. Qed.

Lemma mulz2 n : n * 2%:Z = n + n. Proof. by rewrite -mulrzz. Qed.

Lemma mul2z n : 2%:Z * n = n + n. Proof. by rewrite mulrC -mulrzz. Qed.

Section LMod.

Variable R : pzRingType.
Variable V : (lmodType R).
Local Coercion Posz : nat >-> int.

Implicit Types m n : int.
Implicit Types x y z : R.
Implicit Types u v w : V.

Lemma scaler_int n v : n%:~R *: v = v *~ n.
Proof. by case: n => n; rewrite /intmul ?scaleNr scaler_nat. Qed.

Lemma scalerMzl a v n : (a *: v) *~ n = (a *~ n) *: v.
Proof. by rewrite -mulrzl -scaler_int scalerA. Qed.

Lemma scalerMzr a v n : (a *: v) *~ n = a *: (v *~ n).
Proof. by rewrite -!scaler_int !scalerA mulrzr mulrzl. Qed.

End LMod.

Lemma mulrz_int (M : zmodType) (n : int) (x : M) : x *~ n%:~R = x *~ n.
Proof. by rewrite -scalezrE scaler_int. Qed.

Section MorphTheory.
Local Coercion Posz : nat >-> int.
Section Additive.
Variables (U V : zmodType) (f : {additive U -> V}).

Lemma raddfMz n : {morph f : x / x *~ n}.
Proof. by case: n=> n x; rewrite 1?raddfN raddfMn. Qed.

End Additive.

Section Multiplicative.

Variables (R S : pzRingType) (f : {rmorphism R -> S}).

Lemma rmorphMz : forall n, {morph f : x / x *~ n}. Proof. exact: raddfMz. Qed.

Lemma rmorph_int : forall n, f n%:~R = n%:~R.
Proof. by move=> n; rewrite rmorphMz rmorph1. Qed.

End Multiplicative.

Section Linear.

Variable R : pzRingType.
Variables (U V : lmodType R) (f : {linear U -> V}).

Lemma linearMn : forall n, {morph f : x / x *~ n}. Proof. exact: raddfMz. Qed.

End Linear.

Lemma raddf_int_scalable (aV rV : lmodType int) (f : {additive aV -> rV}) :
  scalable f.
Proof. by move=> z u; rewrite -[z]intz !scaler_int raddfMz. Qed.

Section Zintmul1rMorph.

Variable R : pzRingType.

Lemma commrMz (x y : R) n : GRing.comm x y -> GRing.comm x (y *~ n).
Proof. by rewrite /GRing.comm=> com_xy; rewrite mulrzAr mulrzAl com_xy. Qed.

Lemma commr_int (x : R) n : GRing.comm x n%:~R.
Proof. exact/commrMz/commr1. Qed.

End Zintmul1rMorph.

Section ZintBigMorphism.

Variable R : pzRingType.

Lemma sumMz : forall I r (P : pred I) F,
 (\sum_(i <- r | P i) F i)%N%:~R = \sum_(i <- r | P i) ((F i)%:~R) :> R.
Proof. exact: rmorph_sum. Qed.

Lemma prodMz : forall I r (P : pred I) F,
 (\prod_(i <- r | P i) F i)%N%:~R = \prod_(i <- r | P i) ((F i)%:~R) :> R.
Proof. exact: rmorph_prod. Qed.

End ZintBigMorphism.

Section Frobenius.

Variable R : nzRingType.
Implicit Types x y : R.

Variable p : nat.
Hypothesis charFp : p \in [char R].

Local Notation "x ^f" := (Frobenius_aut charFp x).

Lemma Frobenius_autMz x n : (x *~ n)^f = x^f *~ n.
Proof.
case: n=> n /=; first exact: Frobenius_autMn.
by rewrite !NegzE !mulrNz Frobenius_autN Frobenius_autMn.
Qed.

Lemma Frobenius_aut_int n : (n%:~R)^f = n%:~R.
Proof. by rewrite Frobenius_autMz Frobenius_aut1. Qed.

End Frobenius.

Section NumMorphism.

Section PO.

Variables (R : numDomainType).

Implicit Types n m : int.
Implicit Types x y : R.

Lemma rmorphzP (f : {rmorphism int -> R}) : f =1 ( *~%R 1).
Proof. by move=> n; rewrite -[n in LHS]intz rmorph_int. Qed.

(* intmul and ler/ltr *)
Lemma ler_pMz2r n (hn : 0 < n) : {mono *~%R^~ n :x y / x <= y :> R}.
Proof. by move=> x y; case: n hn=> [[]|] // n _; rewrite ler_pMn2r. Qed.

Lemma ltr_pMz2r n (hn : 0 < n) : {mono *~%R^~ n : x y / x < y :> R}.
Proof. exact: leW_mono (ler_pMz2r _). Qed.

Lemma ler_nMz2r n (hn : n < 0) : {mono *~%R^~ n : x y /~ x <= y :> R}.
Proof.
by move=> x y /=; rewrite -![_ *~ n]mulNrNz ler_pMz2r (oppr_cp0, lerN2).
Qed.

Lemma ltr_nMz2r n (hn : n < 0) : {mono *~%R^~ n : x y /~ x < y :> R}.
Proof. exact: leW_nmono (ler_nMz2r _). Qed.

Lemma ler_wpMz2r n (hn : 0 <= n) : {homo *~%R^~ n : x y / x <= y :> R}.
Proof. by move=> x y xy; case: n hn=> [] // n _; rewrite ler_wMn2r. Qed.

Lemma ler_wnMz2r n (hn : n <= 0) : {homo *~%R^~ n : x y /~ x <= y :> R}.
Proof. by move=> x y xy /=; rewrite -lerN2 -!mulrNz ler_wpMz2r // oppr_ge0. Qed.

Lemma mulrz_ge0 x n (x0 : 0 <= x) (n0 : 0 <= n) : 0 <= x *~ n.
Proof. by rewrite -(mul0rz _ n) ler_wpMz2r. Qed.

Lemma mulrz_le0 x n (x0 : x <= 0) (n0 : n <= 0) : 0 <= x *~ n.
Proof. by rewrite -(mul0rz _ n) ler_wnMz2r. Qed.

Lemma mulrz_ge0_le0 x n (x0 : 0 <= x) (n0 : n <= 0) : x *~ n <= 0.
Proof. by rewrite -(mul0rz _ n) ler_wnMz2r. Qed.

Lemma mulrz_le0_ge0 x n (x0 : x <= 0) (n0 : 0 <= n) : x *~ n <= 0.
Proof. by rewrite -(mul0rz _ n) ler_wpMz2r. Qed.

Lemma pmulrz_lgt0 x n (n0 : 0 < n) : 0 < x *~ n = (0 < x).
Proof. by rewrite -(mul0rz _ n) ltr_pMz2r // mul0rz. Qed.

Lemma nmulrz_lgt0 x n (n0 : n < 0) : 0 < x *~ n = (x < 0).
Proof. by rewrite -(mul0rz _ n) ltr_nMz2r // mul0rz. Qed.

Lemma pmulrz_llt0 x n (n0 : 0 < n) : x *~ n < 0 = (x < 0).
Proof. by rewrite -(mul0rz _ n) ltr_pMz2r // mul0rz. Qed.

Lemma nmulrz_llt0 x n (n0 : n < 0) : x *~ n < 0 = (0 < x).
Proof. by rewrite -(mul0rz _ n) ltr_nMz2r // mul0rz. Qed.

Lemma pmulrz_lge0 x n (n0 : 0 < n) : 0 <= x *~ n = (0 <= x).
Proof. by rewrite -(mul0rz _ n) ler_pMz2r // mul0rz. Qed.

Lemma nmulrz_lge0 x n (n0 : n < 0) : 0 <= x *~ n = (x <= 0).
Proof. by rewrite -(mul0rz _ n) ler_nMz2r // mul0rz. Qed.

Lemma pmulrz_lle0 x n (n0 : 0 < n) : x *~ n <= 0 = (x <= 0).
Proof. by rewrite -(mul0rz _ n) ler_pMz2r // mul0rz. Qed.

Lemma nmulrz_lle0 x n (n0 : n < 0) : x *~ n <= 0 = (0 <= x).
Proof. by rewrite -(mul0rz _ n) ler_nMz2r // mul0rz. Qed.

Lemma ler_wpMz2l x (hx : 0 <= x) : {homo *~%R x : x y / x <= y}.
Proof.
by move=> m n /= hmn; rewrite -subr_ge0 -mulrzBr mulrz_ge0 // subr_ge0.
Qed.

Lemma ler_wnMz2l x (hx : x <= 0) : {homo *~%R x : x y /~ x <= y}.
Proof.
by move=> m n /= hmn; rewrite -subr_ge0 -mulrzBr mulrz_le0 // subr_le0.
Qed.

Lemma ler_pMz2l x (hx : 0 < x) : {mono *~%R x : x y / x <= y}.
Proof.
move=> m n /=; rewrite real_mono ?num_real // => {m n}.
by move=> m n /= hmn; rewrite -subr_gt0 -mulrzBr pmulrz_lgt0 // subr_gt0.
Qed.

Lemma ler_nMz2l x (hx : x < 0) : {mono *~%R x : x y /~ x <= y}.
Proof.
move=> m n /=; rewrite real_nmono ?num_real // => {m n}.
by move=> m n /= hmn; rewrite -subr_gt0 -mulrzBr nmulrz_lgt0 // subr_lt0.
Qed.

Lemma ltr_pMz2l x (hx : 0 < x) : {mono *~%R x : x y / x < y}.
Proof. exact: leW_mono (ler_pMz2l _). Qed.

Lemma ltr_nMz2l x (hx : x < 0) : {mono *~%R x : x y /~ x < y}.
Proof. exact: leW_nmono (ler_nMz2l _). Qed.

Lemma pmulrz_rgt0 x n (x0 : 0 < x) : 0 < x *~ n = (0 < n).
Proof. by rewrite -(mulr0z x) ltr_pMz2l. Qed.

Lemma nmulrz_rgt0 x n (x0 : x < 0) : 0 < x *~ n = (n < 0).
Proof. by rewrite -(mulr0z x) ltr_nMz2l. Qed.

Lemma pmulrz_rlt0 x n (x0 : 0 < x) : x *~ n < 0 = (n < 0).
Proof. by rewrite -(mulr0z x) ltr_pMz2l. Qed.

Lemma nmulrz_rlt0 x n (x0 : x < 0) : x *~ n < 0 = (0 < n).
Proof. by rewrite -(mulr0z x) ltr_nMz2l. Qed.

Lemma pmulrz_rge0 x n (x0 : 0 < x) : 0 <= x *~ n = (0 <= n).
Proof. by rewrite -(mulr0z x) ler_pMz2l. Qed.

Lemma nmulrz_rge0 x n (x0 : x < 0) : 0 <= x *~ n = (n <= 0).
Proof. by rewrite -(mulr0z x) ler_nMz2l. Qed.

Lemma pmulrz_rle0 x n (x0 : 0 < x) : x *~ n <= 0 = (n <= 0).
Proof. by rewrite -(mulr0z x) ler_pMz2l. Qed.

Lemma nmulrz_rle0 x n (x0 : x < 0) : x *~ n <= 0 = (0 <= n).
Proof. by rewrite -(mulr0z x) ler_nMz2l. Qed.

Lemma mulrIz x (hx : x != 0) : injective ( *~%R x).
Proof.
move=> y z; rewrite -![x *~ _]mulrzr => /(mulfI hx).
by apply: inc_inj y z; exact: ler_pMz2l.
Qed.

Lemma ler_int m n : (m%:~R <= n%:~R :> R) = (m <= n).
Proof. by rewrite ler_pMz2l. Qed.

Lemma ltr_int m n : (m%:~R < n%:~R :> R) = (m < n).
Proof. by rewrite ltr_pMz2l. Qed.

Lemma eqr_int m n : (m%:~R == n%:~R :> R) = (m == n).
Proof. by rewrite (inj_eq (mulrIz _)) ?oner_eq0. Qed.

Lemma ler0z n : (0 <= n%:~R :> R) = (0 <= n).
Proof. by rewrite pmulrz_rge0. Qed.

Lemma ltr0z n : (0 < n%:~R :> R) = (0 < n).
Proof. by rewrite pmulrz_rgt0. Qed.

Lemma lerz0 n : (n%:~R <= 0 :> R) = (n <= 0).
Proof. by rewrite pmulrz_rle0. Qed.

Lemma ltrz0 n : (n%:~R < 0 :> R) = (n < 0).
Proof. by rewrite pmulrz_rlt0. Qed.

Lemma ler1z (n : int) : (1 <= n%:~R :> R) = (1 <= n).
Proof. by rewrite -[1]/(1%:~R) ler_int. Qed.

Lemma ltr1z (n : int) : (1 < n%:~R :> R) = (1 < n).
Proof. by rewrite -[1]/(1%:~R) ltr_int. Qed.

Lemma lerz1 n : (n%:~R <= 1 :> R) = (n <= 1).
Proof. by rewrite -[1]/(1%:~R) ler_int. Qed.

Lemma ltrz1 n : (n%:~R < 1 :> R) = (n < 1).
Proof. by rewrite -[1]/(1%:~R) ltr_int. Qed.

Lemma intr_eq0 n : (n%:~R == 0 :> R) = (n == 0).
Proof. by rewrite -(mulr0z 1) (inj_eq (mulrIz _)) // oner_eq0. Qed.

Lemma mulrz_eq0 x n : (x *~ n == 0) = ((n == 0) || (x == 0)).
Proof. by rewrite -mulrzl mulf_eq0 intr_eq0. Qed.

Lemma mulrz_neq0 x n : x *~ n != 0 = ((n != 0) && (x != 0)).
Proof. by rewrite mulrz_eq0 negb_or. Qed.

Lemma realz n : (n%:~R : R) \in Num.real.
Proof. by rewrite -topredE /Num.real /= ler0z lerz0 le_total. Qed.
Hint Resolve realz : core.

Definition intr_inj := @mulrIz 1 (oner_neq0 R).

End PO.

End NumMorphism.

End MorphTheory.

Arguments intr_inj {R} [x1 x2].

Definition exprz (R : unitRingType) (x : R) (n : int) :=
  match n with
    | Posz n => x ^+ n
    | Negz n => x ^- (n.+1)
  end.
Arguments exprz : simpl never.

Notation "x ^ n" := (exprz x n) : ring_scope.

Section ExprzUnitRing.

Variable R : unitRingType.
Implicit Types x y : R.
Implicit Types m n : int.
Local Coercion Posz : nat >-> int.

Lemma exprnP x (n : nat) : x ^+ n = x ^ n. Proof. by []. Qed.

Lemma exprnN x (n : nat) : x ^- n = x ^ -n%:Z.
Proof. by case: n=> //; rewrite oppr0 expr0 invr1. Qed.

Lemma expr0z x : x ^ 0 = 1. Proof. by []. Qed.

Lemma expr1z x : x ^ 1 = x. Proof. by []. Qed.

Lemma exprN1 x : x ^ (-1) = x^-1. Proof. by []. Qed.

Lemma invr_expz x n : (x ^ n)^-1 = x ^ (- n).
Proof. by case: (intP n)=> // [|m]; rewrite ?opprK ?expr0z ?invr1 // invrK. Qed.

Lemma exprz_inv x n : (x^-1) ^ n = x ^ (- n).
Proof. by case: (intP n)=> // m; rewrite -[_ ^ (- _)]exprVn ?opprK ?invrK. Qed.

Lemma exp1rz n : 1 ^ n = 1 :> R.
Proof. by case: (intP n)=> // m; rewrite -?exprz_inv ?invr1; apply: expr1n. Qed.

Lemma exprSz x (n : nat) : x ^ n.+1 = x * x ^ n. Proof. exact: exprS. Qed.

Lemma exprSzr x (n : nat) : x ^ n.+1 = x ^ n * x. Proof. exact: exprSr. Qed.

Fact exprzD_nat x (m n : nat) : x ^ (m%:Z + n) = x ^ m * x ^ n.
Proof. exact: exprD. Qed.

Fact exprzD_Nnat x (m n : nat) : x ^ (-m%:Z + -n%:Z) = x ^ (-m%:Z) * x ^ (-n%:Z).
Proof. by rewrite -opprD -!exprz_inv exprzD_nat. Qed.

Lemma exprzD_ss x m n : (0 <= m) && (0 <= n) || (m <= 0) && (n <= 0)
  ->  x ^ (m + n) = x ^ m * x ^ n.
Proof.
case: (intP m)=> {m} [|m|m]; case: (intP n)=> {n} [|n|n] //= _;
by rewrite ?expr0z ?mul1r ?exprzD_nat ?exprzD_Nnat ?sub0r ?addr0 ?mulr1.
Qed.

Lemma exp0rz n : 0 ^ n = (n == 0)%:~R :> R.
Proof. by case: (intP n)=> // m; rewrite -?exprz_inv ?invr0 exprSz mul0r. Qed.

Lemma commrXz x y n : GRing.comm x y -> GRing.comm x (y ^ n).
Proof.
rewrite /GRing.comm; elim: n x y=> [|n ihn|n ihn] x y com_xy //=.
* by rewrite expr0z mul1r mulr1.
* by rewrite -exprnP commrX //.
rewrite -exprz_inv -exprnP commrX //.
case: (boolP (y \is a GRing.unit))=> uy; last by rewrite invr_out.
by apply/eqP; rewrite (can2_eq (mulrVK _) (mulrK _)) // -mulrA com_xy mulKr.
Qed.

Lemma exprMz_comm x y n : x \is a GRing.unit -> y \is a GRing.unit ->
  GRing.comm x y -> (x * y) ^ n = x ^ n * y ^ n.
Proof.
move=> ux uy com_xy; elim: n => [|n _|n _]; first by rewrite expr0z mulr1.
  by rewrite -!exprnP exprMn_comm.
rewrite -!exprnN -!exprVn com_xy -exprMn_comm ?invrM//.
exact/commrV/commr_sym/commrV.
Qed.

Lemma commrXz_wmulls x y n :
  0 <= n -> GRing.comm x y -> (x * y) ^ n = x ^ n * y ^ n.
Proof.
move=> n0 com_xy; elim: n n0 => [|n _|n _] //; first by rewrite expr0z mulr1.
by rewrite -!exprnP exprMn_comm.
Qed.

Lemma unitrXz x n (ux : x \is a GRing.unit) : x ^ n \is a GRing.unit.
Proof.
case: (intP n)=> {n} [|n|n]; rewrite ?expr0z ?unitr1 ?unitrX //.
by rewrite -invr_expz unitrV unitrX.
Qed.

Lemma exprzDr x (ux : x \is a GRing.unit) m n : x ^ (m + n) = x ^ m * x ^ n.
Proof.
move: n m; apply: wlog_le=> n m hnm.
  by rewrite addrC hnm commrXz //; exact/commr_sym/commrXz.
case: (intP m) hnm=> {m} [|m|m]; rewrite ?mul1r ?add0r //;
 case: (intP n)=> {n} [|n|n _]; rewrite ?mulr1 ?addr0 //;
   do ?by rewrite exprzD_ss.
rewrite -invr_expz subzSS !exprSzr invrM ?unitrX // -mulrA mulVKr //.
case: (leqP n m)=> [|/ltnW] hmn; rewrite -{2}(subnK hmn) exprzD_nat -subzn //.
  by rewrite mulrK ?unitrX.
by rewrite invrM ?unitrXz // mulVKr ?unitrXz // -opprB -invr_expz.
Qed.

Lemma exprz_exp x m n : (x ^ m) ^ n = (x ^ (m * n)).
Proof.
wlog: n / 0 <= n.
  by case: n=> [n -> //|n]; rewrite ?NegzE mulrN -?invr_expz=> -> /=.
elim: n x m=> [|n ihn|n ihn] x m // _; first by rewrite mulr0 !expr0z.
rewrite exprSz ihn // intS mulrDr mulr1 exprzD_ss //.
by case: (intP m)=> // m'; rewrite ?oppr_le0 //.
Qed.

Lemma exprzAC x m n : (x ^ m) ^ n = (x ^ n) ^ m.
Proof. by rewrite !exprz_exp mulrC. Qed.

Lemma exprz_out x n (nux : x \isn't a GRing.unit) (hn : 0 <= n) :
  x ^ (- n) = x ^ n.
Proof. by case: (intP n) hn=> //= m; rewrite -exprnN -exprVn invr_out. Qed.

End ExprzUnitRing.

Section Exprz_Zint_UnitRing.

Variable R : unitRingType.
Implicit Types x y : R.
Implicit Types m n : int.
Local Coercion Posz : nat >-> int.

Lemma exprz_pMzl x m n : 0 <= n -> (x *~ m) ^ n = x ^ n *~ (m ^ n).
Proof.
by elim: n=> [|n ihn|n _] // _; rewrite !exprSz ihn // mulrzAr mulrzAl -mulrzA.
Qed.

Lemma exprz_pintl m n (hn : 0 <= n) : m%:~R ^ n = (m ^ n)%:~R :> R.
Proof. by rewrite exprz_pMzl // exp1rz. Qed.

Lemma exprzMzl x m n (ux : x \is a GRing.unit) (um : m%:~R \is a @GRing.unit R):
   (x *~ m) ^ n = (m%:~R ^ n) * x ^ n :> R.
Proof. rewrite -[x *~ _]mulrzl exprMz_comm //; exact/commr_sym/commr_int. Qed.

Lemma expNrz x n : (- x) ^ n = (-1) ^ n * x ^ n :> R.
Proof.
case: n=> [] n; rewrite ?NegzE; first exact: exprNn.
by rewrite -!exprz_inv !invrN invr1; apply: exprNn.
Qed.

Lemma unitr_n0expz x n :
  n != 0 -> (x ^ n \is a GRing.unit) = (x \is a GRing.unit).
Proof.
by case: n => *; rewrite ?NegzE -?exprz_inv ?unitrX_pos ?unitrV ?lt0n.
Qed.

Lemma intrV (n : int) :
  n \in [:: 0; 1; -1] -> n%:~R ^-1 = n%:~R :> R.
Proof.
by case: (intP n)=> // [|[]|[]] //; rewrite ?rmorphN ?invrN (invr0, invr1).
Qed.

Lemma rmorphXz (R' : unitRingType) (f : {rmorphism R -> R'}) n :
  {in GRing.unit, {morph f : x / x ^ n}}.
Proof. by case: n => n x Ux; rewrite ?rmorphV ?rpredX ?rmorphXn. Qed.

End Exprz_Zint_UnitRing.

Section ExprzIdomain.

Variable R : idomainType.
Implicit Types x y : R.
Implicit Types m n : int.
Local Coercion Posz : nat >-> int.

Lemma expfz_eq0 x n : (x ^ n == 0) = (n != 0) && (x == 0).
Proof.
by case: n=> n; rewrite ?NegzE -?exprz_inv ?expf_eq0 ?lt0n ?invr_eq0.
Qed.

Lemma expfz_neq0 x n : x != 0 -> x ^ n != 0.
Proof. by move=> x_nz; rewrite expfz_eq0; apply/nandP; right. Qed.

Lemma exprzMl x y n (ux : x \is a GRing.unit) (uy : y \is a GRing.unit) :
  (x * y) ^ n = x ^ n * y ^ n.
Proof. by rewrite exprMz_comm //; apply: mulrC. Qed.

Lemma expfV (x : R) (i : int) : (x ^ i) ^-1 = (x ^-1) ^ i.
Proof. by rewrite invr_expz exprz_inv. Qed.

End ExprzIdomain.

Section ExprzField.

Variable F : fieldType.
Implicit Types x y : F.
Implicit Types m n : int.
Local Coercion Posz : nat >-> int.

Lemma expfzDr x m n : x != 0 -> x ^ (m + n) = x ^ m * x ^ n.
Proof. by move=> hx; rewrite exprzDr ?unitfE. Qed.

Lemma expfz_n0addr x m n : m + n != 0 -> x ^ (m + n) = x ^ m * x ^ n.
Proof.
have [-> hmn|nx0 _] := eqVneq x 0; last exact: expfzDr.
rewrite !exp0rz (negPf hmn).
case: (eqVneq m 0) hmn => [->|]; rewrite (mul0r, mul1r) //.
by rewrite add0r=> /negPf->.
Qed.

Lemma expfzMl x y n : (x * y) ^ n = x ^ n * y ^ n.
Proof.
have [->|/negPf n0] := eqVneq n 0; first by rewrite !expr0z mulr1.
case: (boolP ((x * y) == 0)); rewrite ?mulf_eq0.
  by case/pred2P=> ->; rewrite ?(mul0r, mulr0, exp0rz, n0).
by case/norP=> x0 y0; rewrite exprzMl ?unitfE.
Qed.

Lemma fmorphXz (R : unitRingType) (f : {rmorphism F -> R}) n :
  {morph f : x / x ^ n}.
Proof. by case: n => n x; rewrite ?fmorphV rmorphXn. Qed.

End ExprzField.

Section ExprzOrder.

Variable R : realFieldType.
Implicit Types x y : R.
Implicit Types m n : int.
Local Coercion Posz : nat >-> int.

(* ler and exprz *)
Lemma exprz_ge0 n x (hx : 0 <= x) : (0 <= x ^ n).
Proof. by case: n=> n; rewrite ?NegzE -?invr_expz ?invr_ge0 ?exprn_ge0. Qed.

Lemma exprz_gt0 n x (hx : 0 < x) : (0 < x ^ n).
Proof. by case: n=> n; rewrite ?NegzE -?invr_expz ?invr_gt0 ?exprn_gt0. Qed.

Definition exprz_gte0 := (exprz_ge0, exprz_gt0).

Lemma ler_wpiXz2l x (x0 : 0 <= x) (x1 : x <= 1) :
  {in >= 0 &, {homo exprz x : x y /~ x <= y}}.
Proof.
move=> [] m [] n; rewrite -!topredE /= ?oppr_cp0 ?ltz_nat // => _ _.
by rewrite lez_nat -?exprnP => /ler_wiXn2l; apply.
Qed.

Lemma ler_wniXz2l x (x0 : 0 <= x) (x1 : x <= 1) :
  {in < 0 &, {homo exprz x : x y /~ x <= y}}.
Proof.
move=> [] m [] n; rewrite ?NegzE -!topredE /= ?oppr_cp0 ?ltz_nat // => _ _.
rewrite lerN2 lez_nat -?invr_expz=> hmn; have := x0.
rewrite le0r=> /predU1P [->|lx0]; first by rewrite !exp0rz invr0.
by rewrite lef_pV2 -?topredE /= ?exprz_gt0 // ler_wiXn2l.
Qed.

Fact ler_wpeXz2l x (x1 : 1 <= x) : {in >= 0 &, {homo exprz x : x y / x <= y}}.
Proof.
move=> [] m [] n; rewrite -!topredE /= ?oppr_cp0 ?ltz_nat // => _ _.
by rewrite lez_nat -?exprnP=> /ler_weXn2l; apply.
Qed.

Fact ler_wneXz2l x (x1 : 1 <= x) : {in <= 0 &, {homo exprz x : x y / x <= y}}.
Proof.
move=> m n hm hn /= hmn.
rewrite -lef_pV2 -?topredE /= ?exprz_gt0 ?(lt_le_trans ltr01) //.
by rewrite !invr_expz ler_wpeXz2l ?lerN2 -?topredE //= oppr_cp0.
Qed.

Lemma ler_weXz2l x (x1 : 1 <= x) : {homo exprz x : x y / x <= y}.
Proof.
move=> m n /= hmn; case: (lerP 0 m)=> [|/ltW] hm.
  by rewrite ler_wpeXz2l // [_ \in _](le_trans hm).
case: (lerP n 0)=> [|/ltW] hn.
  by rewrite ler_wneXz2l // [_ \in _](le_trans hmn).
apply: (@le_trans _ _ (x ^ 0)); first by rewrite ler_wneXz2l.
by rewrite ler_wpeXz2l.
Qed.

Lemma pexprz_eq1 x n (x0 : 0 <= x) : (x ^ n == 1) = ((n == 0) || (x == 1)).
Proof.
case: n=> n; rewrite ?NegzE -?exprz_inv ?oppr_eq0 pexprn_eq1 // ?invr_eq1 //.
by rewrite invr_ge0.
Qed.

Lemma ieexprIz x (x0 : 0 < x) (nx1 : x != 1) : injective (exprz x).
Proof.
apply: wlog_lt=> // m n hmn; first by move=> hmn'; rewrite hmn.
move=> /(f_equal ( *%R^~ (x ^ (- n)))).
rewrite -!expfzDr ?gt_eqF // subrr expr0z=> /eqP.
by rewrite pexprz_eq1 ?(ltW x0) // (negPf nx1) subr_eq0 orbF=> /eqP.
Qed.

Lemma ler_piXz2l x (x0 : 0 < x) (x1 : x < 1) :
  {in >= 0 &, {mono exprz x : x y /~ x <= y}}.
Proof.
apply: (le_nmono_in (inj_nhomo_lt_in _ _)).
  by move=> n m hn hm /=; apply: ieexprIz; rewrite // lt_eqF.
by apply: ler_wpiXz2l; rewrite ?ltW.
Qed.

Lemma ltr_piXz2l x (x0 : 0 < x) (x1 : x < 1) :
  {in >= 0 &, {mono exprz x : x y /~ x < y}}.
Proof. exact: (leW_nmono_in (ler_piXz2l _ _)). Qed.

Lemma ler_niXz2l x (x0 : 0 < x) (x1 : x < 1) :
  {in < 0 &, {mono exprz x : x y /~ x <= y}}.
Proof.
apply: (le_nmono_in (inj_nhomo_lt_in _ _)).
  by move=> n m hn hm /=; apply: ieexprIz; rewrite // lt_eqF.
by apply: ler_wniXz2l; rewrite ?ltW.
Qed.

Lemma ltr_niXz2l x (x0 : 0 < x) (x1 : x < 1) :
  {in < 0 &, {mono (exprz x) : x y /~ x < y}}.
Proof. exact: (leW_nmono_in (ler_niXz2l _ _)). Qed.

Lemma ler_eXz2l x (x1 : 1 < x) : {mono exprz x : x y / x <= y}.
Proof.
apply: (le_mono (inj_homo_lt _ _)).
  by apply: ieexprIz; rewrite ?(lt_trans ltr01) // gt_eqF.
by apply: ler_weXz2l; rewrite ?ltW.
Qed.

Lemma ltr_eXz2l x (x1 : 1 < x) : {mono exprz x : x y / x < y}.
Proof. exact: (leW_mono (ler_eXz2l _)). Qed.

Lemma ler_wpXz2r n (hn : 0 <= n) :
  {in >= 0 & , {homo (@exprz R)^~ n : x y / x <= y}}.
Proof. by case: n hn=> // n _; exact: lerXn2r. Qed.

Lemma ler_wnXz2r n (hn : n <= 0) :
  {in > 0 & , {homo (@exprz R)^~ n : x y /~ x <= y}}.
Proof.
move=> x y /= hx hy hxy; rewrite -lef_pV2 ?[_ \in _]exprz_gt0 //.
by rewrite !invr_expz ler_wpXz2r ?[_ \in _]ltW // oppr_cp0.
Qed.

Lemma pexpIrz n (n0 : n != 0) : {in >= 0 &, injective ((@exprz R)^~ n)}.
Proof.
move=> x y; rewrite ![_ \in _]le0r=> /predU1P [-> _ /eqP|hx].
  by rewrite exp0rz ?(negPf n0) eq_sym expfz_eq0=> /andP [_ /eqP->].
case/predU1P=> [-> /eqP|hy].
  by rewrite exp0rz ?(negPf n0) expfz_eq0=> /andP [_ /eqP].
move=> /(f_equal ( *%R^~ (y ^ (- n)))) /eqP.
rewrite -expfzDr ?(gt_eqF hy) // subrr expr0z -exprz_inv -expfzMl.
rewrite pexprz_eq1 ?(negPf n0) /= ?mulr_ge0 ?invr_ge0 ?ltW //.
by rewrite (can2_eq (mulrVK _) (mulrK _)) ?unitfE ?(gt_eqF hy) // mul1r=> /eqP.
Qed.

Lemma nexpIrz n (n0 : n != 0) : {in <= 0 &, injective ((@exprz R)^~ n)}.
Proof.
move=> x y; rewrite ![_ \in _]le_eqVlt => /predU1P [-> _ /eqP|hx].
  by rewrite exp0rz ?(negPf n0) eq_sym expfz_eq0=> /andP [_ /eqP->].
case/predU1P=> [-> /eqP|hy].
  by rewrite exp0rz ?(negPf n0) expfz_eq0=> /andP [_ /eqP].
move=> /(f_equal ( *%R^~ (y ^ (- n)))) /eqP.
rewrite -expfzDr ?(lt_eqF hy) // subrr expr0z -exprz_inv -expfzMl.
rewrite pexprz_eq1 ?(negPf n0) /= ?mulr_le0 ?invr_le0 ?ltW //.
by rewrite (can2_eq (mulrVK _) (mulrK _)) ?unitfE ?(lt_eqF hy) // mul1r=> /eqP.
Qed.

Lemma ler_pXz2r n (hn : 0 < n) :
  {in >= 0 & , {mono ((@exprz R)^~ n) : x y / x <= y}}.
Proof.
apply: le_mono_in (inj_homo_lt_in _ _).
  by move=> x y hx hy /=; apply: pexpIrz; rewrite // gt_eqF.
by apply: ler_wpXz2r; rewrite ltW.
Qed.

Lemma ltr_pXz2r n (hn : 0 < n) :
  {in >= 0 & , {mono ((@exprz R)^~ n) : x y / x < y}}.
Proof. exact: leW_mono_in (ler_pXz2r _). Qed.

Lemma ler_nXz2r n (hn : n < 0) :
  {in > 0 & , {mono ((@exprz R)^~ n) : x y /~ x <= y}}.
Proof.
apply: le_nmono_in (inj_nhomo_lt_in _ _); last first.
  by apply: ler_wnXz2r; rewrite ltW.
by move=> x y hx hy /=; apply: pexpIrz; rewrite ?[_ \in _]ltW ?lt_eqF.
Qed.

Lemma ltr_nXz2r n (hn : n < 0) :
  {in > 0 & , {mono ((@exprz R)^~ n) : x y /~ x < y}}.
Proof. exact: leW_nmono_in (ler_nXz2r _). Qed.

Lemma eqrXz2 n x y : n != 0 -> 0 <= x -> 0 <= y -> (x ^ n == y ^ n) = (x == y).
Proof. by  move=> *; rewrite (inj_in_eq (pexpIrz _)). Qed.

End ExprzOrder.

Local Notation sgr := Num.sg.

Section Sgz.

Variable R : numDomainType.
Implicit Types x y z : R.
Implicit Types m n p : int.
Local Coercion Posz : nat >-> int.

Definition sgz x : int := if x == 0 then 0 else if x < 0 then -1 else 1.

Lemma sgz_def x : sgz x = (-1) ^+ (x < 0)%R *+ (x != 0).
Proof. by rewrite /sgz; case: (_ == _); case: (_ < _). Qed.

Lemma sgrEz x : sgr x = (sgz x)%:~R. Proof. by rewrite !(fun_if intr). Qed.

Lemma gtr0_sgz x : 0 < x -> sgz x = 1.
Proof. by move=> x_gt0; rewrite /sgz lt_neqAle andbC eq_le lt_geF. Qed.

Lemma ltr0_sgz x : x < 0 -> sgz x = -1.
Proof. by move=> x_lt0; rewrite /sgz eq_sym eq_le x_lt0 lt_geF. Qed.

Lemma sgz0 : sgz (0 : R) = 0. Proof. by rewrite /sgz eqxx. Qed.
Lemma sgz1 : sgz (1 : R) = 1. Proof. by rewrite gtr0_sgz // ltr01. Qed.
Lemma sgzN1 : sgz (-1 : R) = -1. Proof. by rewrite ltr0_sgz // ltrN10. Qed.

Definition sgzE := (sgz0, sgz1, sgzN1).

Lemma sgz_sgr x : sgz (sgr x) = sgz x.
Proof. by rewrite !(fun_if sgz) !sgzE. Qed.

Lemma normr_sgz x : `|sgz x| = (x != 0).
Proof. by rewrite sgz_def -mulr_natr normrMsign normr_nat natz. Qed.

Lemma normr_sg x : `|sgr x| = (x != 0)%:~R.
Proof. by rewrite sgr_def -mulr_natr normrMsign normr_nat. Qed.

End Sgz.

Section MoreSgz.

Variable R : numDomainType.

Lemma sgz_int m : sgz (m%:~R : R) = sgz m.
Proof. by rewrite /sgz intr_eq0 ltrz0. Qed.

Lemma sgrz (n : int) : sgr n = sgz n. Proof. by rewrite sgrEz intz. Qed.

Lemma intr_sg m : (sgr m)%:~R = sgr (m%:~R) :> R.
Proof. by rewrite sgrz -sgz_int -sgrEz. Qed.

Lemma sgz_id (x : R) : sgz (sgz x) = sgz x.
Proof. by rewrite !(fun_if (@sgz _)). Qed.

End MoreSgz.

Section SgzReal.

Variable R : realDomainType.
Implicit Types x y z : R.
Implicit Types m n p : int.
Local Coercion Posz : nat >-> int.

Lemma sgz_cp0 x :
  ((sgz x == 1) = (0 < x)) *
  ((sgz x == -1) = (x < 0)) *
  ((sgz x == 0) = (x == 0)).
Proof. by rewrite /sgz; case: ltrgtP. Qed.

Variant sgz_val x : bool -> bool -> bool -> bool -> bool -> bool
  -> bool -> bool -> bool -> bool -> bool -> bool
  -> bool -> bool -> bool -> bool -> bool -> bool
  -> R -> R -> int -> Set :=
  | SgzNull of x = 0 : sgz_val x true true true true false false
    true false false true false false true false false true false false 0 0 0
  | SgzPos of x > 0 : sgz_val x false false true false false true
    false false true false false true false false true false false true x 1 1
  | SgzNeg of x < 0 : sgz_val x false true false false true false
    false true false false true false false true false false true false (-x) (-1) (-1).

Lemma sgzP x :
  sgz_val x (0 == x) (x <= 0) (0 <= x) (x == 0) (x < 0) (0 < x)
  (0 == sgr x) (-1 == sgr x) (1 == sgr x)
  (sgr x == 0)  (sgr x == -1) (sgr x == 1)
  (0 == sgz x) (-1 == sgz x) (1 == sgz x)
  (sgz x == 0)  (sgz x == -1) (sgz x == 1) `|x| (sgr x) (sgz x).
Proof.
rewrite ![_ == sgz _]eq_sym ![_ == sgr _]eq_sym !sgr_cp0 !sgz_cp0.
by rewrite /sgz; case: sgrP; constructor.
Qed.

Lemma sgzN x : sgz (- x) = - sgz x.
Proof. by rewrite /sgz oppr_eq0 oppr_lt0; case: ltrgtP. Qed.

Lemma mulz_sg x : sgz x * sgz x = (x != 0)%:~R.
Proof. by case: sgzP; rewrite ?(mulr0, mulr1, mulrNN). Qed.

Lemma mulz_sg_eq1 x y : (sgz x * sgz y == 1) = (x != 0) && (sgz x == sgz y).
Proof.
do 2?case: sgzP=> _; rewrite ?(mulr0, mulr1, mulrN1, opprK, oppr0, eqxx);
  by rewrite ?[0 == 1]eq_sym ?oner_eq0 //= eqr_oppLR oppr0 oner_eq0.
Qed.

Lemma mulz_sg_eqN1 x y : (sgz x * sgz y == -1) = (x != 0) && (sgz x == - sgz y).
Proof. by rewrite -eqr_oppLR -mulrN -sgzN mulz_sg_eq1. Qed.

(* Lemma muls_eqA x y z : sgr x != 0 -> *)
(*   (sgr y * sgr z == sgr x) = ((sgr y * sgr x == sgr z) && (sgr z != 0)). *)
(* Proof. by do 3!case: sgrP=> _. Qed. *)

Lemma sgzM x y : sgz (x * y) = sgz x * sgz y.
Proof.
rewrite -sgz_sgr -(sgz_sgr x) -(sgz_sgr y) sgrM.
by case: sgrP; case: sgrP; rewrite /sgz ?(mulNr, mul0r, mul1r);
  rewrite ?(oppr_eq0, oppr_cp0, eqxx, ltxx, ltr01, ltr10, oner_eq0).
Qed.

Lemma sgzX (n : nat) x : sgz (x ^+ n) = (sgz x) ^+ n.
Proof. by elim: n => [|n IHn]; rewrite ?sgz1 // !exprS sgzM IHn. Qed.

Lemma sgz_eq0 x : (sgz x == 0) = (x == 0).
Proof. by rewrite sgz_cp0. Qed.

Lemma sgz_odd (n : nat) x : x != 0 -> (sgz x) ^+ n = (sgz x) ^+ (odd n).
Proof. by case: sgzP => //=; rewrite ?expr1n // signr_odd. Qed.

Lemma sgz_gt0 x : (sgz x > 0) = (x > 0).
Proof. by case: sgzP. Qed.

Lemma sgz_lt0 x : (sgz x < 0) = (x < 0).
Proof. by case: sgzP. Qed.

Lemma sgz_ge0 x : (sgz x >= 0) = (x >= 0).
Proof. by case: sgzP. Qed.

Lemma sgz_le0 x : (sgz x <= 0) = (x <= 0).
Proof. by case: sgzP. Qed.

Lemma sgz_smul x y : sgz (y *~ (sgz x)) = (sgz x) * (sgz y).
Proof. by rewrite -mulrzl sgzM -sgrEz sgz_sgr. Qed.

Lemma sgrMz m x : sgr (x *~ m) = sgr x *~ sgr m.
Proof. by rewrite -mulrzr sgrM -intr_sg mulrzr. Qed.

End SgzReal.

Lemma sgz_eq (R R' : realDomainType) (x : R) (y : R') :
  (sgz x == sgz y) = ((x == 0) == (y == 0)) && ((0 < x) == (0 < y)).
Proof. by do 2!case: sgzP. Qed.

Lemma intr_sign (R : pzRingType) s : ((-1) ^+ s)%:~R = (-1) ^+ s :> R.
Proof. exact: rmorph_sign. Qed.

Section Absz.

Implicit Types m n p : int.
Open Scope nat_scope.
Local Coercion Posz : nat >-> int.

Lemma absz_nat (n : nat) : `|n| = n. Proof. by []. Qed.

Lemma abszE (m : int) : `|m| = `|m|%R :> int. Proof. by []. Qed.

Lemma absz0 : `|0%R| = 0. Proof. by []. Qed.

Lemma abszN m : `|- m| = `|m|. Proof. by case: (normrN m). Qed.

Lemma absz_eq0 m : (`|m| == 0) = (m == 0%R). Proof. by case: (intP m). Qed.

Lemma absz_gt0 m : (`|m| > 0) = (m != 0%R). Proof. by case: (intP m). Qed.

Lemma absz1 : `|1%R| = 1. Proof. by []. Qed.

Lemma abszN1 : `|-1%R| = 1. Proof. by []. Qed.

Lemma absz_id m : `|(`|m|)| = `|m|. Proof. by []. Qed.

Lemma abszM m1 m2 : `|(m1 * m2)%R| = `|m1| * `|m2|.
Proof. by case: m1 m2 => [[|m1]|m1] [[|m2]|m2] //=; rewrite ?mulnS mulnC. Qed.

Lemma abszX (n : nat) m : `|m ^+ n| = `|m| ^ n.
Proof. by elim: n => // n ihn; rewrite exprS expnS abszM ihn. Qed.

Lemma absz_sg m : `|sgr m| = (m != 0%R). Proof. by case: (intP m). Qed.

Lemma gez0_abs m : (0 <= m)%R -> `|m| = m :> int.
Proof. by case: (intP m). Qed.

Lemma gtz0_abs m : (0 < m)%R -> `|m| = m :> int.
Proof. by case: (intP m). Qed.

Lemma lez0_abs m : (m <= 0)%R -> `|m| = - m :> int.
Proof. by case: (intP m). Qed.

Lemma ltz0_abs m : (m < 0)%R -> `|m| = - m :> int.
Proof. by case: (intP m). Qed.

Lemma lez_abs m : m <= `|m|%N :> int.
Proof. by case: (intP m). Qed.

Lemma absz_sign s : `|(-1) ^+ s| = 1.
Proof. by rewrite abszX exp1n. Qed.

Lemma abszMsign s m : `|((-1) ^+ s * m)%R| = `|m|.
Proof. by rewrite abszM absz_sign mul1n. Qed.

Lemma mulz_sign_abs m : ((-1) ^+ (m < 0)%R * `|m|%:Z)%R = m.
Proof. by rewrite abszE mulr_sign_norm. Qed.

Lemma mulz_Nsign_abs m : ((-1) ^+ (0 < m)%R * `|m|%:Z)%R = - m.
Proof. by rewrite abszE mulr_Nsign_norm. Qed.

Lemma intEsign  m : m = ((-1) ^+ (m < 0)%R * `|m|%:Z)%R.
Proof. exact: numEsign. Qed.

Lemma abszEsign m : `|m|%:Z = ((-1) ^+ (m < 0)%R * m)%R.
Proof. exact: normrEsign. Qed.

Lemma intEsg m : m = (sgz m * `|m|%:Z)%R.
Proof. by rewrite -sgrz -numEsg. Qed.

Lemma abszEsg m : (`|m|%:Z = sgz m * m)%R.
Proof. by rewrite -sgrz -normrEsg. Qed.

End Absz.

Section MoreAbsz.
Variable R : numDomainType.
Implicit Type i : int.

Lemma mulr_absz (x : R) i : x *+ `|i| = x *~ `|i|.
Proof. by rewrite -abszE. Qed.

Lemma natr_absz i : `|i|%:R = `|i|%:~R :> R.
Proof. by rewrite -abszE. Qed.

End MoreAbsz.

Module Export IntDist.

(* This notation is supposed to work even if the ssrint library is not Imported.
   Since we can't rely on the CS database to contain the zmodule instance on
   int we put the instance by hand in the notation. *)
Local Definition int_nmodType : nmodType := int.
Local Definition int_zmodType : zmodType := int.
Notation "m - n" :=
  (@GRing.add int_nmodType (m%N : int)
    (@GRing.opp int_zmodType (n%N : int))) : distn_scope.
Arguments absz m%distn_scope.
Notation "`| m |" := (absz m) : nat_scope.
Coercion Posz : nat >-> int.

Section Distn.

Open Scope nat_scope.
Implicit Type m : int.
Implicit Types n d : nat.

Lemma distnC m1 m2 : `|m1 - m2| = `|m2 - m1|.
Proof. by rewrite -opprB abszN. Qed.

Lemma distnDl d n1 n2 : `|d + n1 - (d + n2)| = `|n1 - n2|.
Proof. by rewrite !PoszD opprD addrCA -addrA addKr. Qed.

Lemma distnDr d n1 n2 : `|n1 + d - (n2 + d)| = `|n1 - n2|.
Proof. by rewrite -!(addnC d) distnDl. Qed.

Lemma distnEr n1 n2 : n1 <= n2 -> `|n1 - n2| = n2 - n1.
Proof. by move/subnK=> {1}<-; rewrite distnC PoszD addrK absz_nat. Qed.

Lemma distnEl n1 n2 : n2 <= n1 -> `|n1 - n2| = n1 - n2.
Proof. by move/distnEr <-; rewrite distnC. Qed.

Lemma distn0 n : `|n - 0| = n.
Proof. by rewrite subr0 absz_nat. Qed.

Lemma dist0n n : `|0 - n| = n.
Proof. by rewrite distnC distn0. Qed.

Lemma distnn m : `|m - m| = 0.
Proof. by rewrite subrr. Qed.

Lemma distn_eq0 n1 n2 : (`|n1 - n2| == 0) = (n1 == n2).
Proof. by rewrite absz_eq0 subr_eq0. Qed.

Lemma distnS n : `|n - n.+1| = 1.
Proof. exact: distnDr n 0 1. Qed.

Lemma distSn n : `|n.+1 - n| = 1.
Proof. exact: distnDr n 1 0. Qed.

Lemma distn_eq1 n1 n2 :
  (`|n1 - n2| == 1) = (if n1 < n2 then n1.+1 == n2 else n1 == n2.+1).
Proof.
case: ltnP => [lt_n12 | le_n21].
  by rewrite eq_sym -(eqn_add2r n1) distnEr ?subnK // ltnW.
by rewrite -(eqn_add2r n2) distnEl ?subnK.
Qed.

Lemma leqD_dist  m1 m2 m3 : `|m1 - m3| <= `|m1 - m2| + `|m2 - m3|.
Proof. by rewrite -lez_nat PoszD !abszE ler_distD. Qed.

(* Most of this proof generalizes to all real-ordered rings. *)
Lemma leqifD_distz m1 m2 m3 :
  `|m1 - m3| <= `|m1 - m2| + `|m2 - m3|
             ?= iff (m1 <= m2 <= m3)%R || (m3 <= m2 <= m1)%R.
Proof.
apply/leqifP; rewrite -ltz_nat -eqz_nat PoszD !abszE; apply/leifP.
wlog le_m31 : m1 m3 / (m3 <= m1)%R.
  move=> IH; case/orP: (le_total m1 m3) => /IH //.
  by rewrite (addrC `|_|)%R orbC !(distrC m1) !(distrC m3).
rewrite ger0_norm ?subr_ge0 // orb_idl => [|/andP[le_m12 le_m23]]; last first.
  by have /eqP->: m2 == m3; rewrite ?lexx // eq_le le_m23 (le_trans le_m31).
rewrite -{1}(subrK m2 m1) -(addrA _ m2) -subr_ge0 andbC -[X in X && _]subr_ge0.
by apply: leifD; apply/real_leif_norm/num_real.
Qed.

Lemma leqifD_dist n1 n2 n3 :
  `|n1 - n3| <= `|n1 - n2| + `|n2 - n3|
             ?= iff (n1 <= n2 <= n3) || (n3 <= n2 <= n1).
Proof. exact: leqifD_distz. Qed.

Lemma sqrn_dist n1 n2 : `|n1 - n2| ^ 2 + 2 * (n1 * n2) = n1 ^ 2 + n2 ^ 2.
Proof.
wlog le_n21: n1 n2 / n2 <= n1.
  move=> IH; case/orP: (leq_total n2 n1) => /IH //.
  by rewrite (addnC (n2 ^ 2)) (mulnC n2) distnC.
by rewrite distnEl ?sqrnB ?subnK ?nat_Cauchy.
Qed.

End Distn.

End IntDist.

Section NormInt.

Variable R : numDomainType.

Lemma intr_norm m : `|m|%:~R = `|m%:~R : R|.
Proof. by rewrite {2}[m]intEsign rmorphMsign normrMsign abszE normr_nat. Qed.

Lemma normrMz m (x : R) : `|x *~ m| = `|x| *~ `|m|.
Proof. by rewrite -mulrzl normrM -intr_norm mulrzl. Qed.

Lemma expN1r (i : int) : (-1 : R) ^ i = (-1) ^+ `|i|.
Proof.
case: i => n; first by rewrite exprnP absz_nat.
by rewrite NegzE abszN  absz_nat -invr_expz expfV invrN1.
Qed.

End NormInt.

Section PolyZintRing.

Variable R : nzRingType.
Implicit Types x y z: R.
Implicit Types m n : int.
Implicit Types i j k : nat.
Implicit Types p q r : {poly R}.

Lemma coefMrz p n i : (p *~ n)`_i = (p`_i *~ n).
Proof. by case: n => n; rewrite ?NegzE (coefMNn, coefMn). Qed.

Lemma polyCMz n : {morph (@polyC R) : c / c *~ n}.
Proof. by case: (intP n) => // n' c; rewrite ?mulrNz ?polyCN polyCMn. Qed.

Lemma hornerMz n p x : (p *~ n).[x] = p.[x] *~ n.
Proof. by case: n => n; rewrite ?NegzE ?mulNzr ?(hornerN, hornerMn). Qed.

Lemma horner_int n x : (n%:~R : {poly R}).[x] = n%:~R.
Proof. by rewrite hornerMz hornerC. Qed.

Lemma derivMz n p : (p *~ n)^`() = p^`() *~ n.
Proof. by case: n => n; rewrite ?NegzE -?pmulrn (derivMn, derivMNn). Qed.

Lemma mulpz p n : p *~ n = n%:~R *: p.
Proof. by rewrite -mul_polyC polyCMz polyC1 mulrzl. Qed.

End PolyZintRing.

Section rpred.

Lemma rpredMz (M : zmodType) (S : zmodClosed M) m :
  {in S, forall u, u *~ m \in S}.
Proof. by case: m => n u Su; rewrite ?rpredN ?rpredMn. Qed.

Lemma rpred_int (R : pzRingType) (S : subringClosed R) m : m%:~R \in S.
Proof. by rewrite rpredMz ?rpred1. Qed.

Lemma rpredZint (R : pzRingType) (M : lmodType R) (S : zmodClosed M) m :
  {in S, forall u, m%:~R *: u \in S}.
Proof. by move=> u Su; rewrite /= scaler_int rpredMz. Qed.

Lemma rpredXz (R : unitRingType) (S : divClosed R) m :
  {in S, forall x, x ^ m \in S}.
Proof. by case: m => n x Sx; rewrite ?rpredV rpredX. Qed.

Lemma rpredXsign (R : unitRingType) (S : divClosed R) n x :
  (x ^ ((-1) ^+ n) \in S) = (x \in S).
Proof. by rewrite -signr_odd; case: (odd n); rewrite ?rpredV. Qed.

End rpred.

(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool choice eqtype ssrnat seq div.
From mathcomp Require Import fintype bigop finset prime fingroup.
From mathcomp Require Import ssralg finalg countalg.

(******************************************************************************)
(*  Definition of the additive group and ring Zp, represented as 'I_p         *)
(******************************************************************************)
(* Definitions:                                                               *)
(* From fintype.v:                                                            *)
(*     'I_p == the subtype of integers less than p, taken here as the type of *)
(*             the integers mod p.                                            *)
(* This file:                                                                 *)
(*     inZp == the natural projection from nat into the integers mod p,       *)
(*             represented as 'I_p. Here p is implicit, but MUST be of the    *)
(*             form n.+1.                                                     *)
(* The operations:                                                            *)
(*      Zp0 == the identity element for addition                              *)
(*      Zp1 == the identity element for multiplication, and a generator of    *)
(*             additive group                                                 *)
(*   Zp_opp == inverse function for addition                                  *)
(*   Zp_add == addition                                                       *)
(*   Zp_mul == multiplication                                                 *)
(*   Zp_inv == inverse function for multiplication                            *)
(* Note that while 'I_n.+1 has canonical finZmodType and finGroupType         *)
(* structures, only 'I_n.+2 has a canonical ring structure (it has, in fact,  *)
(* a canonical finComUnitRing structure), and hence an associated             *)
(* multiplicative unit finGroupType. To mitigate the issues caused by the     *)
(* trivial "ring" (which is, indeed is NOT a ring in the ssralg/finalg        *)
(* formalization), we define additional notation:                             *)
(*       'Z_p == the type of integers mod (max p 2); this is always a proper  *)
(*               ring, by constructions. Note that 'Z_p is provably equal to  *)
(*               'I_p if p > 1, and convertible to 'I_p if p is of the form   *)
(*               n.+2.                                                        *)
(*       Zp p == the subgroup of integers mod (max p 1) in 'Z_p; this is thus *)
(*               all of 'Z_p if p > 1, and else the trivial group.            *)
(* units_Zp p == the group of all units of 'Z_p -- i.e., the group of         *)
(*               (multiplicative) automorphisms of Zp p.                      *)
(* We show that Zp and units_Zp are abelian, and compute their orders.        *)
(* We use a similar technique to represent the prime fields:                  *)
(*        'F_p == the finite field of integers mod the first prime divisor of *)
(*                maxn p 2. This is provably equal to 'Z_p and 'I_p if p is   *)
(*                provably prime, and indeed convertible to the above if p is *)
(*                a concrete prime such as 2, 5 or 23.                        *)
(* Note finally that due to the canonical structures it is possible to use    *)
(* 0%R instead of Zp0, and 1%R instead of Zp1 (for the latter, p must be of   *)
(* the form n.+2, and 1%R : nat will simplify to 1%N).                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Section ZpDef.

(***********************************************************************)
(*                                                                     *)
(*  Mod p arithmetic on the finite set {0, 1, 2, ..., p - 1}           *)
(*                                                                     *)
(***********************************************************************)

Variable p' : nat.
Local Notation p := p'.+1.

Implicit Types x y z : 'I_p.

(* Standard injection; val (inZp i) = i %% p *)
Definition inZp i := Ordinal (ltn_pmod i (ltn0Sn p')).
Lemma modZp x : x %% p = x.
Proof. by rewrite modn_small ?ltn_ord. Qed.
Lemma valZpK x : inZp x = x.
Proof. by apply: val_inj; rewrite /= modZp. Qed.

(* Operations *)
Definition Zp0 : 'I_p := ord0.
Definition Zp1 := inZp 1.
Definition Zp_opp x := inZp (p - x).
Definition Zp_add x y := inZp (x + y).
Definition Zp_mul x y := inZp (x * y).
Definition Zp_inv x := if coprime p x then inZp (egcdn x p).1 else x.

(* Additive group structure. *)

Lemma Zp_add0z : left_id Zp0 Zp_add.
Proof. exact: valZpK. Qed.

Lemma Zp_addNz : left_inverse Zp0 Zp_opp Zp_add.
Proof.
by move=> x; apply: val_inj; rewrite /= modnDml subnK ?modnn // ltnW.
Qed.

Lemma Zp_addA : associative Zp_add.
Proof.
by move=> x y z; apply: val_inj; rewrite /= modnDml modnDmr addnA.
Qed.

Lemma Zp_addC : commutative Zp_add.
Proof. by move=> x y; apply: val_inj; rewrite /= addnC. Qed.

HB.instance Definition _ :=
  GRing.isZmodule.Build 'I_p Zp_addA Zp_addC Zp_add0z Zp_addNz.

HB.instance Definition _ := [finGroupMixin of 'I_p for +%R].

(* Ring operations *)

Lemma Zp_mul1z : left_id Zp1 Zp_mul.
Proof. by move=> x; apply: val_inj; rewrite /= modnMml mul1n modZp. Qed.

Lemma Zp_mulC : commutative Zp_mul.
Proof. by move=> x y; apply: val_inj; rewrite /= mulnC. Qed.

Lemma Zp_mulz1 : right_id Zp1 Zp_mul.
Proof. by move=> x; rewrite Zp_mulC Zp_mul1z. Qed.

Lemma Zp_mulA : associative Zp_mul.
Proof.
by move=> x y z; apply: val_inj; rewrite /= modnMml modnMmr mulnA.
Qed.

Lemma Zp_mul_addr : right_distributive Zp_mul Zp_add.
Proof.
by move=> x y z; apply: val_inj; rewrite /= modnMmr modnDm mulnDr.
Qed.

Lemma Zp_mul_addl : left_distributive Zp_mul Zp_add.
Proof. by move=> x y z; rewrite -!(Zp_mulC z) Zp_mul_addr. Qed.

Lemma Zp_mulVz x : coprime p x -> Zp_mul (Zp_inv x) x = Zp1.
Proof.
move=> co_p_x; apply: val_inj; rewrite /Zp_inv co_p_x /= modnMml.
by rewrite -(chinese_modl co_p_x 1 0) /chinese addn0 mul1n mulnC.
Qed.

Lemma Zp_mulzV x : coprime p x -> Zp_mul x (Zp_inv x) = Zp1.
Proof. by move=> Ux; rewrite /= Zp_mulC Zp_mulVz. Qed.

Lemma Zp_intro_unit x y : Zp_mul y x = Zp1 -> coprime p x.
Proof.
case=> yx1; have:= coprimen1 p.
by rewrite -coprime_modr -yx1 coprime_modr coprimeMr; case/andP.
Qed.

Lemma Zp_inv_out x : ~~ coprime p x -> Zp_inv x = x.
Proof. by rewrite /Zp_inv => /negPf->. Qed.

Lemma Zp_mulrn x n : x *+ n = inZp (x * n).
Proof.
apply: val_inj => /=; elim: n => [|n IHn]; first by rewrite muln0 modn_small.
by rewrite !GRing.mulrS /= IHn modnDmr mulnS.
Qed.

Import GroupScope.

Lemma Zp_mulgC : @commutative 'I_p _ mulg.
Proof. exact: Zp_addC. Qed.

Lemma Zp_abelian : abelian [set: 'I_p].
Proof. exact: FinRing.zmod_abelian. Qed.

Lemma Zp_expg x n : x ^+ n = inZp (x * n).
Proof. exact: Zp_mulrn. Qed.

Lemma Zp1_expgz x : Zp1 ^+ x = x.
Proof. by rewrite Zp_expg; apply: Zp_mul1z. Qed.

Lemma Zp_cycle : setT = <[Zp1]>.
Proof. by apply/setP=> x; rewrite -[x]Zp1_expgz inE groupX ?mem_gen ?set11. Qed.

Lemma order_Zp1 : #[Zp1] = p.
Proof. by rewrite orderE -Zp_cycle cardsT card_ord. Qed.

End ZpDef.

Arguments Zp0 {p'}.
Arguments Zp1 {p'}.
Arguments inZp {p'} i.
Arguments valZpK {p'} x.

(* We redefine fintype.ord1 to specialize it with 0 instead of ord0 *)
(* since 'I_n is now canonically a zmodType  *)
Lemma ord1 : all_equal_to (0 : 'I_1).
Proof. exact: ord1. Qed.

Lemma lshift0 m n : lshift m (0 : 'I_n.+1) = (0 : 'I_(n + m).+1).
Proof. exact: val_inj. Qed.

Lemma rshift1 n : @rshift 1 n =1 lift (0 : 'I_n.+1).
Proof. by move=> i; apply: val_inj. Qed.

Lemma split1 n i :
  split (i : 'I_(1 + n)) = oapp (@inr _ _) (inl _ 0) (unlift 0 i).
Proof.
case: unliftP => [i'|] -> /=.
  by rewrite -rshift1 (unsplitK (inr _ _)).
by rewrite -(lshift0 n 0) (unsplitK (inl _ _)).
Qed.

Section ZpRing.

Variable p' : nat.
Local Notation p := p'.+2.

Lemma Zp_nontrivial : Zp1 != 0 :> 'I_p. Proof. by []. Qed.

HB.instance Definition _ :=
  GRing.Zmodule_isComRing.Build 'I_p
    (@Zp_mulA _) (@Zp_mulC _) (@Zp_mul1z _) (@Zp_mul_addl _) Zp_nontrivial.
HB.instance Definition _ :=
  GRing.ComRing_hasMulInverse.Build 'I_p
    (@Zp_mulVz _) (@Zp_intro_unit _) (@Zp_inv_out _).

Lemma Zp_nat n : n%:R = inZp n :> 'I_p.
Proof. by apply: val_inj; rewrite [n%:R]Zp_mulrn /= modnMml mul1n. Qed.

Lemma natr_Zp (x : 'I_p) : x%:R = x.
Proof. by rewrite Zp_nat valZpK. Qed.

Lemma natr_negZp (x : 'I_p) : (- x)%:R = - x.
Proof. by apply: val_inj; rewrite /= Zp_nat /= modn_mod. Qed.

Import GroupScope.

Lemma unit_Zp_mulgC : @commutative {unit 'I_p} _ mulg.
Proof. by move=> u v; apply: val_inj; rewrite /= GRing.mulrC. Qed.

Lemma unit_Zp_expg (u : {unit 'I_p}) n :
  val (u ^+ n) = inZp (val u ^ n) :> 'I_p.
Proof.
apply: val_inj => /=; elim: n => [|n IHn] //.
by rewrite expgS /= IHn expnS modnMmr.
Qed.

End ZpRing.

Definition Zp_trunc p := p.-2.

Notation "''Z_' p" := 'I_(Zp_trunc p).+2
  (at level 8, p at level 2, format "''Z_' p") : type_scope.
Notation "''F_' p" := 'Z_(pdiv p)
  (at level 8, p at level 2, format "''F_' p") : type_scope.

Arguments natr_Zp {p'} x.

Section ZpRing.

Import GRing.Theory.

Lemma add_1_Zp p (x : 'Z_p) : 1 + x = ordS x.
Proof. by case: p => [|[|p]] in x *; apply/val_inj. Qed.

Lemma add_Zp_1 p (x : 'Z_p) : x + 1 = ordS x.
Proof. by rewrite addrC add_1_Zp. Qed.

Lemma sub_Zp_1 p (x : 'Z_p) : x - 1 = ord_pred x.
Proof. by apply: (addIr 1); rewrite addrNK add_Zp_1 ord_predK. Qed.

Lemma add_N1_Zp p (x : 'Z_p) : -1 + x = ord_pred x.
Proof. by rewrite addrC sub_Zp_1. Qed.

End ZpRing.

Section Groups.

Variable p : nat.

Definition Zp := if p > 1 then [set: 'Z_p] else 1%g.
Definition units_Zp := [set: {unit 'Z_p}].

Lemma Zp_cast : p > 1 -> (Zp_trunc p).+2 = p.
Proof. by case: p => [|[]]. Qed.

Lemma val_Zp_nat (p_gt1 : p > 1) n : (n%:R : 'Z_p) = (n %% p)%N :> nat.
Proof. by rewrite Zp_nat /= Zp_cast. Qed.

Lemma Zp_nat_mod (p_gt1 : p > 1)m : (m %% p)%:R = m%:R :> 'Z_p.
Proof. by apply: ord_inj; rewrite !val_Zp_nat // modn_mod. Qed.

Lemma char_Zp : p > 1 -> p%:R = 0 :> 'Z_p.
Proof. by move=> p_gt1; rewrite -Zp_nat_mod ?modnn. Qed.

Lemma unitZpE x : p > 1 -> ((x%:R : 'Z_p) \is a GRing.unit) = coprime p x.
Proof.
move=> p_gt1; rewrite qualifE /=.
by rewrite val_Zp_nat ?Zp_cast ?coprime_modr.
Qed.

Lemma Zp_group_set : group_set Zp.
Proof. by rewrite /Zp; case: (p > 1); apply: groupP. Qed.
(* FIX ME : is this ok something similar is done in fingroup *)
Canonical Zp_group := Group Zp_group_set.

Lemma card_Zp : p > 0 -> #|Zp| = p.
Proof.
rewrite /Zp; case: p => [|[|p']] //= _; first by rewrite cards1.
by rewrite cardsT card_ord.
Qed.

Lemma mem_Zp x : p > 1 -> x \in Zp. Proof. by rewrite /Zp => ->. Qed.

Canonical units_Zp_group := [group of units_Zp].

Lemma card_units_Zp : p > 0 -> #|units_Zp| = totient p.
Proof.
move=> p_gt0; transitivity (totient p.-2.+2); last by case: p p_gt0 => [|[|p']].
rewrite cardsT card_sub -sum1_card big_mkcond /=.
by rewrite totient_count_coprime big_mkord.
Qed.

Lemma units_Zp_abelian : abelian units_Zp.
Proof. by apply/centsP=> u _ v _; apply: unit_Zp_mulgC. Qed.

End Groups.

(* Field structure for primes. *)

Section PrimeField.

Open Scope ring_scope.

Variable p : nat.

Section F_prime.

Hypothesis p_pr : prime p.

Lemma Fp_Zcast : Zp_trunc (pdiv p) = Zp_trunc p.
Proof. by rewrite /pdiv primes_prime. Qed.

Lemma Fp_cast : (Zp_trunc (pdiv p)).+2 = p.
Proof. by rewrite Fp_Zcast ?Zp_cast ?prime_gt1. Qed.

Lemma card_Fp : #|'F_p| = p.
Proof. by rewrite card_ord Fp_cast. Qed.

Lemma val_Fp_nat n : (n%:R : 'F_p) = (n %% p)%N :> nat.
Proof. by rewrite Zp_nat /= Fp_cast. Qed.

Lemma Fp_nat_mod m : (m %% p)%:R = m%:R :> 'F_p.
Proof. by apply: ord_inj; rewrite !val_Fp_nat // modn_mod. Qed.

Lemma char_Fp : p \in [char 'F_p].
Proof. by rewrite !inE -Fp_nat_mod p_pr ?modnn. Qed.

Lemma char_Fp_0 : p%:R = 0 :> 'F_p.
Proof. exact: GRing.charf0 char_Fp. Qed.

Lemma unitFpE x : ((x%:R : 'F_p) \is a GRing.unit) = coprime p x.
Proof. by rewrite pdiv_id // unitZpE // prime_gt1. Qed.

End F_prime.

Lemma Fp_fieldMixin : GRing.ComUnitRing_isField 'F_p.
Proof.
constructor => x nzx.
rewrite qualifE /= prime_coprime ?gtnNdvd ?lt0n //.
case: (ltnP 1 p) => [lt1p | ]; last by case: p => [|[|p']].
by rewrite Zp_cast ?prime_gt1 ?pdiv_prime.
Qed.

HB.instance Definition _ := Fp_fieldMixin.
HB.instance Definition _ := FinRing.isField.Build 'F_p.

End PrimeField.

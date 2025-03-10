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
From mathcomp Require Import orderedzmod.
 
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
(*                  \bar R == coproduct of R and {+oo, -oo};                  *)
(*                            notation for extended (R:Type)                  *)
(*                    r%:E == injects real numbers into \bar R                *)
(*                +%E, -%E == addition/opposite for extended  reals           *)
(*    er_map (f : T -> T') == the \bar T -> \bar T' lifting of f              *)
(*                    +%dE == dual addition/dual iterated addition for        *)
(*                            extended reals (-oo + +oo = +oo instead of -oo) *)
(*                            Import DualAddTheory for related lemmas         *)
(*                  x +? y == the addition of the extended real numbers x and *)
(*                            and y is defined, i.e., it is neither +oo - oo  *)
(*                            nor -oo + oo                                    *)
(*  (_ <= _)%E, (_ < _)%E, == comparison relations for extended reals         *)
(*  (_ >= _)%E, (_ > _)%E                                                     *)
(*   (\sum_(i in A) f i)%E == bigop-like notation in scope %E                 *)
(*      maxe x y, mine x y == notation for the maximum/minimum of two         *)
(*                            extended real numbers                           *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "x %:E" (at level 2, format "x %:E").
Reserved Notation "x %:dE" (at level 2, format "x %:dE").
Reserved Notation "x +? y" (at level 50, format "x  +?  y").
Reserved Notation "x *? y" (at level 50, format "x  *?  y").
Reserved Notation "'\bar' x" (at level 2, format "'\bar'  x").
Reserved Notation "'\bar' '^d' x" (at level 2, format "'\bar' '^d'  x").
Reserved Notation "{ 'posnum' '\bar' R }" (at level 0,
  format "{ 'posnum'  '\bar'  R }").
Reserved Notation "{ 'nonneg' '\bar' R }" (at level 0,
  format "{ 'nonneg'  '\bar'  R }").

Declare Scope ereal_dual_scope.
Declare Scope ereal_scope.

Import GRing.Theory Order.TTheory orderedzmod.Num.Theory.
Local Open Scope order_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Variant extended (R : Type) := EFin of R | EPInf | ENInf.
Arguments EFin {R}.

Lemma EFin_inj T : injective (@EFin T).
Proof. by move=> a b; case. Qed.

Definition dual_extended := extended.

Definition dEFin : forall {R}, R -> dual_extended R := @EFin.

(* Notations in ereal_dual_scope should be kept *before* the
   corresponding notation in ereal_scope, otherwise when none of the
   scope is open (lte x y) would be displayed as (x < y)%dE, instead
   of (x < y)%E, for instance. *)
Notation "+oo" := (@EPInf _ : dual_extended _) : ereal_dual_scope.
Notation "+oo" := (@EPInf _) : ereal_scope.
Notation "-oo" := (@ENInf _ : dual_extended _) : ereal_dual_scope.
Notation "-oo" := (@ENInf _) : ereal_scope.
Notation "r %:dE" := (@EFin _ r%R : dual_extended _) : ereal_dual_scope.
Notation "r %:E" := (@EFin _ r%R : dual_extended _) : ereal_dual_scope.
Notation "r %:E" := (@EFin _ r%R).
Notation "'\bar' R" := (extended R) : type_scope.
Notation "'\bar' '^d' R" := (dual_extended R) : type_scope.
Notation "0" := (@GRing.zero (\bar^d _)) : ereal_dual_scope.
Notation "0" := (@GRing.zero (\bar _)) : ereal_scope.
Notation "1" := (1%R%:E : dual_extended _) : ereal_dual_scope.
Notation "1" := (1%R%:E) : ereal_scope.

Bind    Scope ereal_dual_scope with dual_extended.
Bind    Scope ereal_scope with extended.
Delimit Scope ereal_dual_scope with dE.
Delimit Scope ereal_scope with E.

Section ereal_theory.
Local Open Scope ereal_scope.

Definition er_map T T' (f : T -> T') (x : \bar T) : \bar T' :=
  match x with
  | r%:E => (f r)%:E
  | +oo => +oo
  | -oo => -oo
  end.

Lemma er_map_idfun T (x : \bar T) : er_map idfun x = x.
Proof. by case: x. Qed.

Definition fine {R : zmodType} x : R := if x is EFin v then v else 0.

Section EqEReal.
Variable (R : eqType).

Definition eq_ereal (x y : \bar R) :=
  match x, y with
    | x%:E, y%:E => x == y
    | +oo, +oo => true
    | -oo, -oo => true
    | _, _ => false
  end.

Lemma ereal_eqP : Equality.axiom eq_ereal.
Proof. by case=> [?||][?||]; apply: (iffP idP) => //= [/eqP|[]] ->. Qed.

HB.instance Definition _ := hasDecEq.Build (\bar R) ereal_eqP.

Lemma eqe (r1 r2 : R) : (r1%:E == r2%:E) = (r1 == r2). Proof. by []. Qed.

End EqEReal.

Section ERealChoice.
Variable (R : choiceType).

Definition code (x : \bar R) :=
  match x with
  | r%:E => GenTree.Node 0 [:: GenTree.Leaf r]
  | +oo => GenTree.Node 1 [::]
  | -oo => GenTree.Node 2 [::]
  end.

Definition decode (x : GenTree.tree R) : option (\bar R) :=
  match x with
  | GenTree.Node 0 [:: GenTree.Leaf r] => Some r%:E
  | GenTree.Node 1 [::] => Some +oo
  | GenTree.Node 2 [::] => Some -oo
  | _ => None
  end.

Lemma codeK : pcancel code decode. Proof. by case. Qed.

HB.instance Definition _ := Choice.copy (\bar R) (pcan_type codeK).

End ERealChoice.

Section ERealCount.
Variable (R : countType).

HB.instance Definition _ := PCanIsCountable (@codeK R).

End ERealCount.

Section ERealOrder.
Context {R : porderNmodType}.

Implicit Types x y : \bar R.

Definition le_ereal x1 x2 :=
  match x1, x2 with
  | -oo, r%:E | r%:E, +oo => r \is Num.real
  | r1%:E, r2%:E => r1 <= r2
  | -oo, _    | _, +oo => true
  | +oo, _    | _, -oo => false
  end.

Definition lt_ereal x1 x2 :=
  match x1, x2 with
  | -oo, r%:E | r%:E, +oo => r \is Num.real
  | r1%:E, r2%:E => r1 < r2
  | -oo, -oo  | +oo, +oo => false
  | +oo, _    | _  , -oo => false
  | -oo, _  => true
  end.

Lemma lt_def_ereal x y : lt_ereal x y = (y != x) && le_ereal x y.
Proof. by case: x y => [?||][?||] //=; rewrite lt_def eqe. Qed.

Lemma le_refl_ereal : reflexive le_ereal.
Proof. by case => /=. Qed.

Lemma le_anti_ereal : ssrbool.antisymmetric le_ereal.
Proof. by case=> [?||][?||]/=; rewrite ?andbF => // /le_anti ->. Qed.

End ERealOrder.

Section ERealComparable.
Context {R : numZmodType}.

Implicit Types x y : \bar R.

Lemma le_trans_ereal : ssrbool.transitive (@le_ereal R).
Proof.
case=> [?||][?||][?||] //=; rewrite -?comparabler0; first exact: le_trans.
  by move=> /le_comparable cmp /(comparabler_trans cmp).
by move=> cmp /ge_comparable /comparabler_trans; apply.
Qed.

Fact ereal_display : Order.disp_t. Proof. by []. Qed.

HB.instance Definition _ := Order.isPOrder.Build ereal_display (\bar R)
  lt_def_ereal le_refl_ereal le_anti_ereal le_trans_ereal.

Lemma leEereal x y : (x <= y)%O = le_ereal x y. Proof. by []. Qed.
Lemma ltEereal x y : (x < y)%O = lt_ereal x y. Proof. by []. Qed.

End ERealComparable.


Notation lee := (@Order.le ereal_display _) (only parsing).
Notation "@ 'lee' R" :=
  (@Order.le ereal_display R) (at level 10, R at level 8, only parsing).
Notation lte := (@Order.lt ereal_display _) (only parsing).
Notation "@ 'lte' R" :=
  (@Order.lt ereal_display R) (at level 10, R at level 8, only parsing).
Notation gee := (@Order.ge ereal_display _) (only parsing).
Notation "@ 'gee' R" :=
  (@Order.ge ereal_display R) (at level 10, R at level 8, only parsing).
Notation gte := (@Order.gt ereal_display _) (only parsing).
Notation "@ 'gte' R" :=
  (@Order.gt ereal_display R) (at level 10, R at level 8, only parsing).

Notation "x <= y" := (lee x y) (only printing) : ereal_dual_scope.
Notation "x <= y" := (lee x y) (only printing) : ereal_scope.
Notation "x < y"  := (lte x y) (only printing) : ereal_dual_scope.
Notation "x < y"  := (lte x y) (only printing) : ereal_scope.

Notation "x <= y <= z" := ((lee x y) && (lee y z)) (only printing) : ereal_dual_scope.
Notation "x <= y <= z" := ((lee x y) && (lee y z)) (only printing) : ereal_scope.
Notation "x < y <= z"  := ((lte x y) && (lee y z)) (only printing) : ereal_dual_scope.
Notation "x < y <= z"  := ((lte x y) && (lee y z)) (only printing) : ereal_scope.
Notation "x <= y < z"  := ((lee x y) && (lte y z)) (only printing) : ereal_dual_scope.
Notation "x <= y < z"  := ((lee x y) && (lte y z)) (only printing) : ereal_scope.
Notation "x < y < z"   := ((lte x y) && (lte y z)) (only printing) : ereal_dual_scope.
Notation "x < y < z"   := ((lte x y) && (lte y z)) (only printing) : ereal_scope.

Notation "x <= y" := (lee (x%dE : dual_extended _) (y%dE : dual_extended _)) : ereal_dual_scope.
Notation "x <= y" := (lee (x : extended _) (y : extended _)) : ereal_scope.
Notation "x < y"  := (lte (x%dE : dual_extended _) (y%dE : dual_extended _)) : ereal_dual_scope.
Notation "x < y"  := (lte (x : extended _) (y : extended _)) : ereal_scope.
Notation "x >= y" := (y <= x) (only parsing) : ereal_dual_scope.
Notation "x >= y" := (y <= x) (only parsing) : ereal_scope.
Notation "x > y"  := (y < x) (only parsing) : ereal_dual_scope.
Notation "x > y"  := (y < x) (only parsing) : ereal_scope.

Notation "x <= y <= z" := ((x <= y) && (y <= z)) : ereal_dual_scope.
Notation "x <= y <= z" := ((x <= y) && (y <= z)) : ereal_scope.
Notation "x < y <= z"  := ((x < y) && (y <= z)) : ereal_dual_scope.
Notation "x < y <= z"  := ((x < y) && (y <= z)) : ereal_scope.
Notation "x <= y < z"  := ((x <= y) && (y < z)) : ereal_dual_scope.
Notation "x <= y < z"  := ((x <= y) && (y < z)) : ereal_scope.
Notation "x < y < z"   := ((x < y) && (y < z)) : ereal_dual_scope.
Notation "x < y < z"   := ((x < y) && (y < z)) : ereal_scope.

Notation "x <= y :> T" := ((x : T) <= (y : T)) (only parsing) : ereal_scope.
Notation "x < y :> T" := ((x : T) < (y : T)) (only parsing) : ereal_scope.

Section ERealZsemimodule.
Context {R : nmodType}.
Implicit Types x y z : \bar R.

Definition adde x y :=
  match x, y with
  | x%:E , y%:E  => (x + y)%:E
  | -oo, _     => -oo
  | _    , -oo => -oo
  | +oo, _     => +oo
  | _    , +oo => +oo
  end.
Arguments adde : simpl never.

Definition dual_adde x y :=
  match x, y with
  | x%:E , y%:E  => (x + y)%R%:E
  | +oo, _     => +oo
  | _    , +oo => +oo
  | -oo, _     => -oo
  | _    , -oo => -oo
  end.
Arguments dual_adde : simpl never.

Lemma addeA_subproof : associative (S := \bar R) adde.
Proof. by case=> [x||] [y||] [z||] //; rewrite /adde /= addrA. Qed.

Lemma addeC_subproof : commutative (S := \bar R) adde.
Proof. by case=> [x||] [y||] //; rewrite /adde /= addrC. Qed.

Lemma add0e_subproof : left_id (0%:E : \bar R) adde.
Proof. by case=> // r; rewrite /adde /= add0r. Qed.

HB.instance Definition _ := GRing.isNmodule.Build (\bar R)
  addeA_subproof addeC_subproof add0e_subproof.

Lemma daddeA_subproof : associative (S := \bar^d R) dual_adde.
Proof. by case=> [x||] [y||] [z||] //; rewrite /dual_adde /= addrA. Qed.

Lemma daddeC_subproof : commutative (S := \bar^d R) dual_adde.
Proof. by case=> [x||] [y||] //; rewrite /dual_adde /= addrC. Qed.

Lemma dadd0e_subproof : left_id (0%:dE%dE : \bar^d R) dual_adde.
Proof. by case=> // r; rewrite /dual_adde /= add0r. Qed.

HB.instance Definition _ := Choice.on (\bar^d R).
HB.instance Definition _ := GRing.isNmodule.Build (\bar^d R)
  daddeA_subproof daddeC_subproof dadd0e_subproof.

Definition enatmul x n : \bar R := iterop n +%R x 0.

Definition ednatmul (x : \bar^d R) n : \bar^d R := iterop n +%R x 0.

End ERealZsemimodule.
Arguments adde : simpl never.
Arguments dual_adde : simpl never.

Section ERealOrder_numZmodType.
Context {R : numZmodType}.
Implicit Types (x y : \bar R) (r : R).

Lemma lee_fin (r s : R) : (r%:E <= s%:E) = (r <= s)%R. Proof. by []. Qed.

Lemma lte_fin (r s : R) : (r%:E < s%:E) = (r < s)%R. Proof. by []. Qed.

Lemma leeNy_eq x : (x <= -oo) = (x == -oo). Proof. by case: x. Qed.

Lemma leye_eq x : (+oo <= x) = (x == +oo). Proof. by case: x. Qed.

Lemma lt0y : (0 : \bar R) < +oo. Proof. exact: real0. Qed.

Lemma ltNy0 : -oo < (0 : \bar R). Proof. exact: real0. Qed.

Lemma le0y : (0 : \bar R) <= +oo. Proof. exact: real0. Qed.

Lemma leNy0 : -oo <= (0 : \bar R). Proof. exact: real0. Qed.

Lemma cmp0y : ((0 : \bar R) >=< +oo%E)%O.
Proof. by rewrite /Order.comparable le0y. Qed.

Lemma cmp0Ny : ((0 : \bar R) >=< -oo%E)%O.
Proof. by rewrite /Order.comparable leNy0 orbT. Qed.

Lemma lt0e x : (0 < x) = (x != 0) && (0 <= x).
Proof. by case: x => [r| |]//; rewrite lte_fin lee_fin lt0r. Qed.

Lemma ereal_comparable x y : (0%E >=< x)%O -> (0%E >=< y)%O -> (x >=< y)%O.
Proof.
move: x y => [x||] [y||] //; rewrite /Order.comparable !lee_fin -!realE.
- exact: real_comparable.
- by rewrite /lee/= => ->.
- by rewrite /lee/= => _ ->.
Qed.

Lemma real_ltry r : r%:E < +oo = (r \is Num.real). Proof. by []. Qed.
Lemma real_ltNyr r : -oo < r%:E = (r \is Num.real). Proof. by []. Qed.

Lemma real_leey x : (x <= +oo) = (fine x \is Num.real).
Proof. by case: x => //=; rewrite real0. Qed.

Lemma real_leNye x : (-oo <= x) = (fine x \is Num.real).
Proof. by case: x => //=; rewrite real0. Qed.

Lemma minye : left_id (+oo : \bar R) Order.min.
Proof. by case. Qed.

Lemma real_miney (x : \bar R) : (0 >=< x)%O -> Order.min x +oo = x.
Proof.
by case: x => [x |//|//] rx; rewrite minEle real_leey [_ \in Num.real]rx.
Qed.

Lemma real_minNye (x : \bar R) : (0 >=< x)%O -> Order.min -oo%E x = -oo%E.
Proof.
by case: x => [x |//|//] rx; rewrite minEle real_leNye [_ \in Num.real]rx.
Qed.

Lemma mineNy : right_zero (-oo : \bar R) Order.min.
Proof. by case=> [x |//|//]; rewrite minElt. Qed.

Lemma maxye : left_zero (+oo : \bar R) Order.max.
Proof. by case. Qed.

Lemma real_maxey (x : \bar R) : (0 >=< x)%O -> Order.max x +oo = +oo.
Proof.
by case: x => [x |//|//] rx; rewrite maxEle real_leey [_ \in Num.real]rx.
Qed.

Lemma real_maxNye (x : \bar R) : (0 >=< x)%O -> Order.max -oo%E x = x.
Proof.
by case: x => [x |//|//] rx; rewrite maxEle real_leNye [_ \in Num.real]rx.
Qed.

Lemma maxeNy : right_id (-oo : \bar R) Order.max.
Proof. by case=> [x |//|//]; rewrite maxElt. Qed.

Lemma gee0P x : 0 <= x <-> x = +oo \/ exists2 r, (r >= 0)%R & x = r%:E.
Proof.
split=> [|[->|[r r0 ->//]]]; last by rewrite real_leey/= real0.
by case: x => [r r0 | _ |//]; [right; exists r|left].
Qed.

Lemma fine0 : fine 0 = 0%R :> R. Proof. by []. Qed.

End ERealOrder_numZmodType.

End ereal_theory.

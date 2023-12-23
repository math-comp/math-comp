From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype choice ssrnat seq.
From mathcomp Require Import fintype finfun.

(******************************************************************************)
(*                          Group-like structures                             *) 
(*                                                                            *)
(* NB: See CONTRIBUTING.md for an introduction to HB concepts and commands.   *)
(*                                                                            *)
(* This file defines the following algebraic structures:                      *)
(*                                                                            *)
(*        nmodType == additive abelian monoid                                 *)
(*                    The HB class is called Nmodule.                         *)
(*        zmodType == additive abelian group (Nmodule with an opposite)       *)
(*                    The HB class is called Zmodule.                         *)
(*                                                                            *)
(* and their joins with subType:                                              *)
(*                                                                            *)
(*         subNmodType V P == join of nmodType and subType (P : pred V) such  *)
(*                            that val is semi_additive                       *)
(*                            The HB class is called SubNmodule.              *)
(*         subZmodType V P == join of zmodType and subType (P : pred V)       *)
(*                            such that val is additive                       *)
(*                            The HB class is called SubZmodule.              *)
(*                                                                            *)
(* Morphisms between the above structures:                                    *)
(*                                                                            *)
(*     Additive.type U V == semi additive (resp. additive) functions between  *)
(*                          nmodType (resp. zmodType) instances U and V       *)
(*                                                                            *)
(* Closedness predicates for the algebraic structures:                        *)
(*                                                                            *)
(*  oppgClosed V == predicate closed under opposite on V : zmodType           *)
(*                  The HB class is called OppClosed.                         *)
(*  addgClosed V == predicate closed under addition on V : nmodType           *)
(*                  The HB class is called AddClosed.                         *)
(*  zmodClosed V == predicate closed under opposite and addition on V         *)
(*                  The HB class is called ZmodClosed.                        *)
(*                                                                            *)
(* Canonical properties of the algebraic structures:                          *)
(*  * nmodType (additive abelian monoids):                                    *)
(*                     0 == the zero (additive identity) of a Nmodule         *)
(*                 x + y == the sum of x and y (in a Nmodule)                 *)
(*                x *+ n == n times x, with n in nat (non-negative), i.e.,    *)
(*                          x + (x + .. (x + x)..) (n terms); x *+ 1 is thus  *)
(*                          convertible to x, and x *+ 2 to x + x             *)
(*        \sum_<range> e == iterated sum for a Zmodule (cf bigop.v)           *)
(*                  e`_i == nth 0 e i, when e : seq M and M has a zmodType    *)
(*                          structure                                         *)
(*             support f == 0.-support f, i.e., [pred x | f x != 0]           *)
(*         addg_closed S <-> collective predicate S is closed under finite    *)
(*                           sums (0 and x + y in S, for x, y in S)           *)
(* [SubChoice_isSubNmodule of U by <:] == nmodType mixin for a subType whose  *)
(*                          base type is a nmodType and whose predicate's is  *)
(*                          a addgClosed                                       *)
(*                                                                            *)
(*  * zmodType (additive abelian groups):                                     *)
(*                   - x == the opposite (additive inverse) of x              *)
(*                 x - y == the difference of x and y; this is only notation  *)
(*                          for x + (- y)                                     *)
(*                x *- n == notation for - (x *+ n), the opposite of x *+ n   *)
(*         oppr_closed S <-> collective predicate S is closed under opposite  *)
(*         zmod_closed S <-> collective predicate S is closed under zmodType  *)
(*                          operations (0 and x - y in S, for x, y in S)      *)
(*                          This property coerces to oppr_pred and addr_pred. *)
(* [SubChoice_isSubZmodule of U by <:] == zmodType mixin for a subType whose  *)
(*                          base type is a zmodType and whose predicate's     *)
(*                          is a zmodClosed                                   *)
(*                                                                            *)
(*   In addition to this structure hierarchy, we also develop a separate,     *)
(* parallel hierarchy for morphisms linking these structures:                 *)
(*                                                                            *)
(* * Additive (semi additive or additive functions):                          *)
(*        semi_additive f <-> f of type U -> V is semi additive, i.e., f maps *)
(*                           the Nmodule structure of U to that of V, 0 to 0  *)
(*                           and + to +                                       *)
(*                        := (f 0 = 0) * {morph f : x y / x + y}              *)
(*             additive f <-> f of type U -> V is additive, i.e., f maps the  *)
(*                           Zmodule structure of U to that of V, 0 to 0,     *)
(*                           - to - and + to + (equivalently, binary - to -)  *)
(*                        := {morph f : u v / u - v}                          *)
(*      {additive U -> V} == the interface type for a Structure (keyed on     *)
(*                           a function f : U -> V) that encapsulates the     *)
(*                           semi_additive property; both U and V must have   *)
(*                           canonical nmodType instances                     *)
(*                           When both U and V have zmodType instances, it is *)
(*                           an additive function.                            *)
(*                                                                            *)
(*   TODO: correct this.                                                      *)
(*   Notations are defined in scope ring_scope (delimiter %R), except term    *)
(* and formula notations, which are in term_scope (delimiter %T).             *)
(*   This library also extends the conventional suffixes described in library *)
(* ssrbool.v with the following:                                              *)
(*   0 -- ring 0, as in addr0 : x + 0 = x                                     *)
(*   1 -- ring 1, as in mulr1 : x * 1 = x                                     *)
(*   D -- ring addition, as in linearD : f (u + v) = f u + f v                *)
(*   B -- ring subtraction, as in opprB : - (x - y) = y - x                   *)
(*   M -- ring multiplication, as in invfM : (x * y)^-1 = x^-1 * y^-1         *)
(*  Mn -- ring by nat multiplication, as in raddfMn : f (x *+ n) = f x *+ n   *)
(*   N -- ring opposite, as in mulNr : (- x) * y = - (x * y)                  *)
(*   V -- ring inverse, as in mulVr : x^-1 * x = 1                            *)
(*   X -- ring exponentiation, as in rmorphXn : f (x ^+ n) = f x ^+ n         *)
(*   Z -- (left) module scaling, as in linearZ : f (a *: v)  = s *: f v       *)
(* The operator suffixes D, B, M and X are also used for the corresponding    *)
(* operations on nat, as in natrX : (m ^ n)%:R = m%:R ^+ n. For the binary    *)
(* power operator, a trailing "n" suffix is used to indicate the operator     *)
(* suffix applies to the left-hand ring argument, as in                       *)
(*   expr1n : 1 ^+ n = 1 vs. expr1 : x ^+ 1 = x.                              *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "*%G" (at level 0).
Reserved Notation "/%G" (at level 0).
Reserved Notation "+%G" (at level 0).
Reserved Notation "-%G" (at level 0).
Reserved Notation "\1" (at level 0).
Reserved Notation "f \* g" (at level 40, left associativity).
(* TOTHINK: Which notation should we use? *)
Reserved Notation "f \\/ g" (at level 40, left associativity).
Reserved Notation "f \^-1" (at level 35).
Reserved Notation "\0" (at level 0).
Reserved Notation "f \+ g" (at level 50, left associativity).
Reserved Notation "f \- g" (at level 50, left associativity).
Reserved Notation "\- f" (at level 35, f at level 35).

Reserved Notation "'{' 'additive' U '->' V '}'"
  (at level 0, U at level 98, V at level 99,
   format "{ 'additive'  U  ->  V }").
Reserved Notation "'{' 'multiplicative' U '->' V '}'"
  (at level 0, U at level 98, V at level 99,
   format "{ 'multiplicative'  U  ->  V }").

Declare Scope group_scope.
Delimit Scope group_scope with G.
Local Open Scope group_scope.

HB.mixin Record isMagma V := {
  mul : V -> V -> V
}.

#[short(type="magmaType")]
HB.structure Definition Magma := {V of isMagma V & Choice V}.

Local Notation "*%G" := (@mul _) : function_scope.
Local Notation "x * y" := (mul x y) : group_scope.

Section MagmaTheory.

Variable V : magmaType.
Implicit Types x y : V.

Definition commute x y := x * y = y * x.

Lemma commute_refl x : commute x x.
Proof. by []. Qed.

Lemma commute_sym x y : commute x y -> commute y x.
Proof. by []. Qed.

Section ClosedPredicates.

Variable S : {pred V}.

Definition mulg_closed := {in S &, forall u v, u * v \in S}.

End ClosedPredicates.

End MagmaTheory.

HB.mixin Record Magma_isSemigroup V of Magma V := {
  mulgA : associative (@mul V)
}.

#[short(type="semigroupType")]
HB.structure Definition Semigroup := {V of Magma_isSemigroup V & Magma V}.

HB.factory Record isSemigroup V of Choice V := {
  mul : V -> V -> V;
  mulgA : associative mul
}.

HB.builders Context V of isSemigroup V.

HB.instance Definition _ := isMagma.Build V mul.
HB.instance Definition _ := Magma_isSemigroup.Build V mulgA.

HB.end.

Section SemigroupTheory.
Variable V : semigroupType.
Implicit Types x y : V.

Lemma commuteM x y z : commute x y ->  commute x z ->  commute x (y * z).
Proof. by move=> cxy cxz; rewrite /commute -mulgA -cxz !mulgA cxy. Qed.

End SemigroupTheory.

HB.mixin Record Magma_isUmagma V of Magma V := {
  one : V;
  mul1g : left_id one mul;
  mulg1 : right_id one mul
}.

#[short(type="umagmaType")]
HB.structure Definition Umagma := {V of Magma_isUmagma V & Magma V}.

Local Notation "1" := (@one _) : group_scope.
Local Notation "s `_ i" := (nth 1 s i) : group_scope.

Definition natexp (V : umagmaType) (x : V) n := @iterop _ n (mul : V -> V -> V) x (@one V).
Arguments natexp : simpl never.

Local Notation "x ^+ n" := (natexp x n) : group_scope.

Section UmagmaTheory.

Variable V : umagmaType.
Implicit Types x y : V.

Lemma expg0n x : x ^+ 0 = 1. Proof. by []. Qed.
Lemma expg1n x : x ^+ 1 = x. Proof. by []. Qed.
Lemma expg2n x : x ^+ 2 = x * x. Proof. by []. Qed.

Lemma expgS x n : x ^+ n.+1 = x * x ^+ n.
Proof. by case: n => //=; rewrite mulg1. Qed.

Lemma expgb x (b : bool) : x ^+ b = (if b then x else 1).
Proof. by case: b. Qed.

Lemma exp1gn n : 1 ^+ n = 1 :> V.
Proof. by elim: n => // n IHn; rewrite expgS mul1g. Qed.

Lemma commute1 x : commute x 1.
Proof. by rewrite /commute mulg1 mul1g. Qed.

Section ClosedPredicates.

Variable S : {pred V}.

Definition umagma_closed := 1 \in S /\ mulg_closed S.

End ClosedPredicates.

End UmagmaTheory.

#[short(type="monoidType")]
HB.structure Definition Monoid := {V of Magma_isUmagma V & Magma_isSemigroup V & Magma V}.

HB.factory Record Semigroup_isMonoid V of Semigroup V := {
  one : V;
  mul1g : left_id one mul;
  mulg1 : right_id one mul
}.

HB.builders Context V of Semigroup_isMonoid V.

HB.instance Definition _ := Magma_isUmagma.Build V mul1g mulg1.

HB.end.

HB.factory Record Umagma_isMonoid V of Umagma V := {
  mulgA : associative (@mul V)
}.

HB.builders Context V of Umagma_isMonoid V.

HB.instance Definition _ := Magma_isSemigroup.Build V mulgA.

HB.end.

HB.factory Record isMonoid V of Choice V := {
  mul : V -> V -> V;
  one : V;
  mulgA : associative mul;
  mul1g : left_id one mul;
  mulg1 : right_id one mul
}.

HB.builders Context V of isMonoid V.

HB.instance Definition _ := isMagma.Build V mul.
HB.instance Definition _ := Magma_isSemigroup.Build V mulgA.
HB.instance Definition _ := Magma_isUmagma.Build V mul1g mulg1.

HB.end.

Section MonoidTheory.

Variable V : monoidType.
Implicit Types x y : V.

Lemma expgSr x n : x ^+ n.+1 = x ^+ n * x.
Proof.
elim: n => [|n IHn]; first by rewrite mul1g.
by rewrite expgS {1}IHn expgS mulgA.
Qed.

Lemma expgnDr x m n : x ^+ (m + n) = x ^+ m * x ^+ n.
Proof.
elim: m => [|m IHm]; first by rewrite mul1g.
by rewrite 2!expgS IHm mulgA.
Qed.

Lemma expgnA x m n : x ^+ (m * n) = x ^+ m ^+ n.
Proof.
by rewrite mulnC; elim: n => //= n IHn; rewrite expgS expgnDr IHn.
Qed.

Lemma expgnAC x m n : x ^+ m ^+ n = x ^+ n ^+ m.
Proof. by rewrite -2!expgnA mulnC. Qed.

Lemma iter_mulg n x y : iter n ( *%G x) y = x ^+ n * y.
Proof. by elim: n => [|n IHn]; rewrite ?mul1g //= IHn expgS mulgA. Qed.

Lemma iter_mulg_1 n x : iter n ( *%G x) 1 = x ^+ n.
Proof. by rewrite iter_mulg mulg1. Qed.

Lemma commuteX x y n : commute x y ->  commute x (y ^+ n).
Proof.
by move=> cxy; case: n; [apply: commute1 | elim=> // n; apply: commuteM].
Qed.

Lemma commuteX2 x y m n : commute x y -> commute (x ^+ m) (y ^+ n).
Proof. by move=> cxy; apply/commuteX/commute_sym/commuteX. Qed.

Lemma expgMn x y n : commute x y -> (x * y) ^+ n  = x ^+ n * y ^+ n.
Proof.
move=> cxy; elim: n => [|n IHn]; first by rewrite mulg1.
by rewrite !expgS IHn -mulgA (mulgA y) (commuteX _ (commute_sym cxy)) !mulgA.
Qed.

Section ClosedPredicates.

Definition monoid_closed := @umagma_closed V.

End ClosedPredicates.

End MonoidTheory.

HB.mixin Record Monoid_isNmodule V of Monoid V := {
  mulgC : commutative (@mul V)
}.

#[short(type="nmodType")]
HB.structure Definition Nmodule := {V of Monoid_isNmodule V & Monoid V}.

HB.factory Record isNmodule V of Choice V := {
  zero : V;
  add : V -> V -> V;
  addgA : associative add;
  addgC : commutative add;
  add0g : left_id zero add
}.

HB.builders Context V of isNmodule V.

HB.instance Definition _ := isMagma.Build V add.
HB.instance Definition _ := Magma_isSemigroup.Build V addgA.

Lemma addg0 : right_id zero add.
Proof. by move=> x; rewrite addgC add0g. Qed.

HB.instance Definition _ := Magma_isUmagma.Build V add0g addg0.
HB.instance Definition _ := Monoid_isNmodule.Build V addgC.

HB.end.

Module NmodExports.
Bind Scope group_scope with Nmodule.sort.
#[deprecated(since="mathcomp 2.0.0",
  note="Use GRing.Nmodule.clone instead.")]
Notation "[ 'nmodType' 'of' T 'for' cT ]" := (Nmodule.clone T cT)
  (at level 0, format "[ 'nmodType'  'of'  T  'for'  cT ]") : form_scope.
#[deprecated(since="mathcomp 2.0.0",
  note="Use GRing.Nmodule.clone instead.")]
Notation "[ 'nmodType' 'of' T ]" :=  (Nmodule.clone T _)
  (at level 0, format "[ 'nmodType'  'of'  T ]") : form_scope.
End NmodExports.
HB.export NmodExports.

Definition zero {V : nmodType} := @one V.
Definition add {V : nmodType} := @mul V.

Local Notation "0" := (@zero _) : group_scope.
Local Notation "+%G" := (@add _) : function_scope.
Local Notation "x + y" := (add x y) : group_scope.

Definition natmul (V : nmodType) (x : V) n := @iterop _ n (add : V -> V -> V) x (@zero V).
Arguments natmul : simpl never.

Local Notation "x *+ n" := (natmul x n) : group_scope.

Section NmoduleTheory.

Variable V : nmodType.
Implicit Types x y : V.

Lemma addgA : associative (@add V).
Proof. exact: mulgA. Qed.

Lemma addgC : commutative (@add V).
Proof. exact: mulgC. Qed.

Lemma add0g : left_id (@zero V) add.
Proof. exact: mul1g. Qed.

Lemma addg0 : right_id (@zero V) add.
Proof. exact: mulg1. Qed.

Lemma addgCA : @left_commutative V V +%G.
Proof. by move=> x y z; rewrite !addgA [x + _]addgC. Qed.

Lemma addgAC : @right_commutative V V +%G.
Proof. by move=> x y z; rewrite -!addgA [y + _]addgC. Qed.

Lemma addgACA : @interchange V +%G +%G.
Proof. by move=> x y z t; rewrite -!addgA [y + _]addgCA. Qed.

Lemma mulg0n x : x *+ 0 = 0. Proof. by []. Qed.
Lemma mulg1n x : x *+ 1 = x. Proof. by []. Qed.
Lemma mulg2n x : x *+ 2 = x * x. Proof. by []. Qed.

Lemma mulgS x n : x *+ n.+1 = x + (x *+ n).
Proof. exact: expgS. Qed.

Lemma mulgSr x n : x *+ n.+1 = x *+ n + x.
Proof. by rewrite addgC mulgS. Qed.

Lemma mulgb x (b : bool) : x *+ b = (if b then x else 0).
Proof. exact: expgb. Qed.

Lemma mul0gn n : 0 *+ n = 0 :> V.
Proof. exact: exp1gn. Qed.

Lemma commuteT x y : commute x y.
Proof. exact/mulgC. Qed.

Lemma mulgnDl n : {morph (fun x => x *+ n) : x y / x + y}.
Proof. by move=> x y; apply/expgMn/commuteT. Qed.

Lemma mulgnDr x m n : x *+ (m + n) = x *+ m + x *+ n.
Proof. exact: expgnDr. Qed.

Lemma mulgnA x m n : x *+ (m * n) = x *+ m *+ n.
Proof. exact: expgnA. Qed.

Lemma mulgnAC x m n : x *+ m *+ n = x *+ n *+ m.
Proof. exact: expgnAC. Qed.

Lemma iter_addg n x y : iter n (+%G x) y = x *+ n + y.
Proof. exact: iter_mulg. Qed.

Lemma iter_addg_0 n x : iter n (+%G x) 0 = x *+ n.
Proof. exact: iter_mulg_1. Qed.

Section ClosedPredicates.

Variable S : {pred V}.

Definition addg_closed := {in S &, forall u v, u + v \in S}.
Definition nmod_closed := 0 \in S /\ addg_closed.

End ClosedPredicates.

End NmoduleTheory.

HB.mixin Record Monoid_isGroup V of Monoid V := {
  inv : V -> V;
  mulVg : left_inverse one inv mul;
  mulgV : right_inverse one inv mul
}.

#[short(type="groupType")]
HB.structure Definition Group := {V of Monoid_isGroup V & Monoid V}.

HB.factory Record isGroup V of Choice V := {
  one : V;
  inv : V -> V;
  mul : V -> V -> V;
  mulgA : associative mul;
  mul1g : left_id one mul;
  mulg1 : right_id one mul;
  mulVg : left_inverse one inv mul;
  mulgV : right_inverse one inv mul
}.

HB.builders Context V of isGroup V.

HB.instance Definition _ := isMagma.Build V mul.
HB.instance Definition _ := Magma_isSemigroup.Build V mulgA.
HB.instance Definition _ := Magma_isUmagma.Build V mul1g mulg1.
HB.instance Definition _ := Monoid_isGroup.Build V mulVg mulgV.

HB.end.

Local Notation "/%G" := (@inv _) : group_scope.
Local Notation "x ^-1" := (inv x) : group_scope.
Local Notation "x / y" := (x * y^-1) : group_scope.
Local Notation "x ^- n" := ((x ^+ n)^-1) : group_scope.

Definition conjg (V : groupType) (x y : V) := y^-1 * (x * y).
Local Notation "x ^ y" := (conjg x y) : group_scope.

Definition commg (V : groupType) (x y : V) := x^-1 * (conjg x y).
Local Notation "[~ x , y ]" := (commg x y) : group_scope.

Section GroupTheory.
Variable V : groupType.
Implicit Types x y : V.

Definition divgg := @mulgV V.

Lemma mulKg : @left_loop V V /%G *%G.
Proof. by move=> x y; rewrite mulgA mulVg mul1g. Qed.

Lemma mulVKg : @rev_left_loop V V /%G *%G.
Proof. by move=> x y ; rewrite mulgA mulgV mul1g. Qed.

Lemma mulgK : @right_loop V V /%G *%G.
Proof. by move=> x y; rewrite -mulgA mulgV mulg1. Qed.

Lemma mulgVK : @rev_right_loop V V /%G *%G.
Proof. by move=> x y ; rewrite -mulgA mulVg mulg1. Qed.
Definition divgK := mulgVK.

Lemma mulgI : @right_injective V V V *%G.
Proof. by move=> x; apply: can_inj (mulKg x). Qed.

Lemma mulIg : @left_injective V V V *%G.
Proof. by move=> x; apply: can_inj (mulgK x). Qed.

Lemma invgK : @involutive V /%G.
Proof. by move=> x; rewrite -[LHS]mulg1 -(mulVg x) mulgA mulVg mul1g. Qed.

Lemma invg_inj : @injective V V /%G.
Proof. exact: inv_inj invgK. Qed.

Lemma divgI : @right_injective V V V (fun x y => x / y).
Proof. by move=> x y z /mulgI/invg_inj. Qed.

Lemma divIg : @left_injective V V V (fun x y => x / y).
Proof. by move=> x y z /mulIg. Qed.

Lemma invg1 : 1 ^-1 = 1 :> V.
Proof. by rewrite -[LHS]mul1g divgg. Qed.

Lemma invg_eq1 x : (x ^-1 == 1) = (x == 1).
Proof. by rewrite (inv_eq invgK) invg1. Qed.

Lemma divg1 x : x / 1 = x. Proof. by rewrite invg1 mulg1. Qed.

Lemma div1g x : 1 / x = x^-1. Proof. by rewrite mul1g. Qed.

Lemma invgF x y : (x / y)^-1 = y / x.
Proof. by apply/(canRL (mulgK x))/(@divIg y); rewrite -mulgA mulVg divgg. Qed.

Lemma invgM : {morph /%G: x y / x * y >-> y * x : V}.
Proof. by move=> x y; rewrite -[y in LHS] invgK invgF. Qed.

(* TOTHINK : This does not have the same form as addrKA in ssralg.v *)
Lemma mulgKA z x y : (x * z) / (y * z) = x / y.
Proof. by rewrite invgM mulgA -[_ / z]mulgA divgg mulg1. Qed.

Lemma divgKA z x y : (x / z) * (z * y) = x * y.
Proof. by rewrite mulgA -[_ * z]mulgA mulVg mulg1. Qed.

Lemma mulg1_eq x y : x * y = 1 -> x^-1 = y.
Proof. by rewrite -[x^-1]mulg1 => <-; rewrite mulKg. Qed.

Lemma divg1_eq x y : x / y = 1 -> x = y.
Proof. by move/mulg1_eq/invg_inj. Qed.

Lemma divg_eq x y z : (x / z == y) = (x == y * z).
Proof. exact: can2_eq (divgK z) (mulgK z) x y. Qed.

Lemma divg_eq1 x y : (x / y == 1) = (x == y).
Proof. by rewrite divg_eq mul1g. Qed.

Lemma mulg_eq1 x y : (x * y == 1) = (x == y^-1).
Proof. by rewrite -[y in LHS]invgK divg_eq1. Qed.

Lemma eqg_inv x y : (x^-1 == y^-1) = (x == y).
Proof. exact: can_eq invgK x y. Qed.

Lemma eqg_invLR x y : (x^-1 == y) = (x == y^-1).
Proof. exact: inv_eq invgK x y. Qed.

Lemma expVgn x n : (x^-1) ^+ n = x ^- n.
Proof.
apply: (@mulgI (x ^+ n)); rewrite divgg.
elim: n => [|n IHn]; first exact: mulg1.
by rewrite expgSr expgS mulgA mulgK.
Qed.

Lemma expgnBr x m n : n <= m -> x ^+ (m - n) = x ^+ m / x ^+ n.
Proof.
elim: m n => [|m IHm] [|n nm]; rewrite ?divg1 // {}IHm //.
by rewrite expgSr expgSr invgM mulgA mulgK.
Qed.

Lemma commuteV x y : commute x y -> commute x y^-1.
Proof. by move=> cxy; apply: (@mulIg y); rewrite mulgVK -mulgA cxy mulKg. Qed.

Lemma conjgE x y : x ^ y = y^-1 * (x * y). Proof. by []. Qed.

Lemma conjgC x y : x * y = y * x ^ y.
Proof. by rewrite mulVKg. Qed.

Lemma conjgCV x y : x * y = y ^ x^-1 * x.
Proof. by rewrite -mulgA mulgVK invgK. Qed.

Lemma conjg1 x : x ^ 1 = x.
Proof. by rewrite conjgE commute1 mulKg. Qed.

Lemma conj1g x : 1 ^ x = 1.
Proof. by rewrite conjgE mul1g mulVg. Qed.

Lemma conjMg x y z : (x * y) ^ z = x ^ z * y ^ z.
Proof. by rewrite !conjgE !mulgA mulgK. Qed.

Lemma conjgM x y z : x ^ (y * z) = (x ^ y) ^ z.
Proof. by rewrite !conjgE invgM !mulgA. Qed.

Lemma conjVg x y : x^-1 ^ y = (x ^ y)^-1.
Proof. by rewrite !conjgE !invgM invgK mulgA. Qed.

Lemma conjJg x y z : (x ^ y) ^ z = (x ^ z) ^ y ^ z.
Proof. by rewrite 2!conjMg conjVg. Qed.

Lemma conjXg x y n : (x ^+ n) ^ y = (x ^ y) ^+ n.
Proof. by elim: n => [|n IHn]; rewrite ?conj1g // !expgS conjMg IHn. Qed.

Lemma conjgK : @right_loop V V /%G (@conjg V).
Proof. by move=> y x; rewrite -conjgM mulgV conjg1. Qed.

Lemma conjgKV : @rev_right_loop V V /%G (@conjg V).
Proof. by move=> y x; rewrite -conjgM mulVg conjg1. Qed.

Lemma conjg_inj : @left_injective V V V (@conjg V).
Proof. by move=> y; apply: can_inj (conjgK y). Qed.

Lemma conjg_eq1 x y : (x ^ y == 1) = (x == 1).
Proof. by rewrite (can2_eq (conjgK _) (conjgKV _)) conj1g. Qed.

Lemma commgEl x y : [~ x, y] = x^-1 * x ^ y. Proof. by []. Qed.

Lemma commgEr x y : [~ x, y] = y^-1 ^ x * y.
Proof. by rewrite -!mulgA. Qed.

Lemma commgC x y : x * y = y * x * [~ x, y].
Proof. by rewrite -mulgA !mulVKg. Qed.

Lemma commgCV x y : x * y = [~ x^-1, y^-1] * (y * x).
Proof. by rewrite commgEl !mulgA !invgK !mulgVK. Qed.

Lemma conjRg x y z : [~ x, y] ^ z = [~ x ^ z, y ^ z].
Proof. by rewrite !conjMg !conjVg. Qed.

Lemma invg_comm x y : [~ x, y]^-1 = [~ y, x].
Proof. by rewrite commgEr conjVg invgM invgK. Qed.

Lemma commgP x y : reflect (commute x y) ([~ x, y] == 1).
Proof. rewrite [[~ x, y]]mulgA -invgM mulg_eq1 eqg_inv eq_sym; apply: eqP. Qed.

(* TOTHINK: why use `reflect` here and equalities elsewhere? *)
Lemma conjg_fixP x y : reflect (x ^ y = x) ([~ x, y] == 1).
Proof. by rewrite mulg_eq1 eqg_inv eq_sym; apply: eqP. Qed.

Lemma commg1_sym x y : ([~ x, y] == 1) = ([~ y, x] == 1).
Proof. by rewrite -invg_comm (inv_eq invgK) invg1. Qed.

Lemma commg1 x : [~ x, 1] = 1.
Proof. exact/eqP/commgP/commute1. Qed.

Lemma comm1g x : [~ 1, x] = 1.
Proof. by rewrite -invg_comm commg1 invg1. Qed.

Lemma commgg x : [~ x, x] = 1.
Proof. exact/eqP/commgP. Qed.

Lemma commgXg x n : [~ x, x ^+ n] = 1.
Proof. exact/eqP/commgP/commuteX. Qed.

Lemma commgVg x : [~ x, x^-1] = 1.
Proof. exact/eqP/commgP/commuteV. Qed.

Lemma commgXVg x n : [~ x, x ^- n] = 1.
Proof. exact/eqP/commgP/commuteV/commuteX. Qed.

Section ClosedPredicates.

Variable S : {pred V}.

Definition invg_closed := {in S, forall u, u^-1 \in S}.
Definition divg_2closed := {in S &, forall u v, u / v \in S}.
Definition group_closed := 1 \in S /\ divg_2closed.

Lemma group_closedV : group_closed -> invg_closed.
Proof. by move=> [S1 SB] x /(SB 1)-/(_ S1); rewrite div1g. Qed.

Lemma group_closedM : group_closed -> mulg_closed S.
Proof.
move=> /[dup]-[S1 SB] /group_closedV SV x y xS /SV yS.
rewrite -[y]invgK; exact: SB.
Qed.

End ClosedPredicates.

End GroupTheory.

#[short(type="zmodType")]
HB.structure Definition Zmodule := {V of Monoid_isNmodule V & Group V}.

HB.factory Record Group_isZmodule V of Group V := {
  mulgC : commutative (@mul V)
}.

HB.builders Context V of Group_isZmodule V.

HB.instance Definition _ := Monoid_isNmodule.Build V mulgC.

HB.end.

HB.factory Record Nmodule_isZmodule V of Nmodule V := {
  opp : V -> V;
  addNg : left_inverse zero opp add
}.

HB.builders Context V of Nmodule_isZmodule V.

Lemma addgN : right_inverse zero opp add.
Proof. by move=> x; rewrite addgC addNg. Qed.

HB.instance Definition _ := Monoid_isGroup.Build V addNg addgN.

HB.end.

HB.factory Record isZmodule V of Choice V := {
  zero : V;
  opp : V -> V;
  add : V -> V -> V;
  addgA : associative add;
  addgC : commutative add;
  add0g : left_id zero add;
  addNg : left_inverse zero opp add
}.

HB.builders Context V of isZmodule V.

HB.instance Definition _ := isNmodule.Build V addgA addgC add0g.
HB.instance Definition _ := Nmodule_isZmodule.Build V addNg.

HB.end.

Module ZmodExports.
Bind Scope group_scope with Zmodule.sort.
#[deprecated(since="mathcomp 2.0.0", note="use GRing.isZmodule.Build instead")]
Notation ZmodMixin V := (isZmodule.Build V).
#[deprecated(since="mathcomp 2.0.0", note="Use GRing.Zmodule.clone instead.")]
Notation "[ 'zmodType' 'of' T 'for' cT ]" := (Zmodule.clone T cT)
  (at level 0, format "[ 'zmodType'  'of'  T  'for'  cT ]") : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use GRing.Zmodule.clone instead.")]
Notation "[ 'zmodType' 'of' T ]" :=  (Zmodule.clone T _)
  (at level 0, format "[ 'zmodType'  'of'  T ]") : form_scope.
End ZmodExports.
HB.export ZmodExports.

Definition opp (V : zmodType) := @inv V.

Local Notation "-%G" := (@opp _) : group_scope.
Local Notation "- x" := (opp x) : group_scope.
Local Notation "x - y" := (x + - y) : group_scope.
Local Notation "x *- n" := (- (x *+ n)) : group_scope.

Section ZmoduleTheory.

Variable V : zmodType.
Implicit Types x y : V.

Lemma addNg : @left_inverse V V V 0 -%G +%G.
Proof. exact: mulVg. Qed.
Lemma addgN : @right_inverse V V V 0 -%G +%G.
Proof. exact: mulgV. Qed.
Definition subrr := addgN.

#[non_forgetful_inheritance]
HB.instance Definition _ := Monoid_isGroup.Build V addNg addgN.

Lemma addKg : @left_loop V V -%G +%G.
Proof. exact: mulKg. Qed.
Lemma addNKg : @rev_left_loop V V -%G +%G.
Proof. exact: mulVKg. Qed.
Lemma addgK : @right_loop V V -%G +%G.
Proof. exact: mulgK. Qed.
Lemma addgNK : @rev_right_loop V V -%G +%G.
Proof. exact: mulgVK. Qed.
Definition subgK := addgNK.
Lemma subKg x : involutive (fun y => x - y).
Proof. by move=> y; apply: (canLR (addgK _)); rewrite addgC subgK. Qed.
Lemma addgI : @right_injective V V V +%G.
Proof. exact: mulgI. Qed.
Lemma addIg : @left_injective V V V +%G.
Proof. exact: mulIg. Qed.
Lemma subgI : right_injective (fun x y => x - y).
Proof. exact: divgI. Qed.
Lemma subIg : left_injective (fun x y => x - y).
Proof. exact: divIg. Qed.
Lemma oppgK : @involutive V -%G.
Proof. exact: invgK. Qed.
Lemma oppg_inj : @injective V V -%G.
Proof. exact: invg_inj. Qed.
Lemma oppg0 : -0 = 0 :> V.
Proof. exact: invg1. Qed.
Lemma oppg_eq0 x : (- x == 0) = (x == 0).
Proof. exact: invg_eq1. Qed.

Lemma subg0 x : x - 0 = x. Proof. exact: divg1. Qed.
Lemma sub0g x : 0 - x = - x. Proof. exact: div1g. Qed.

Lemma oppgB x y : - (x - y) = y - x.
Proof. exact: invgF. Qed.

Lemma oppgD : {morph -%G: x y / x + y : V}.
Proof. by move=> x y; rewrite -[y in LHS]oppgK oppgB addgC. Qed.

Lemma addgKA z x y : (x + z) - (z + y) = x - y.
Proof. by rewrite oppgD addgA addgK. Qed.

Lemma subgKA z x y : (x - z) + (z + y) = x + y.
Proof. exact: divgKA. Qed.

Lemma addg0_eq x y : x + y = 0 -> - x = y.
Proof. exact: mulg1_eq. Qed.

Lemma subg0_eq x y : x - y = 0 -> x = y. Proof. exact: divg1_eq. Qed.

Lemma subg_eq x y z : (x - z == y) = (x == y + z).
Proof. exact: divg_eq. Qed.

Lemma subg_eq0 x y : (x - y == 0) = (x == y).
Proof. exact: divg_eq1. Qed.

Lemma addg_eq0 x y : (x + y == 0) = (x == - y).
Proof. exact: mulg_eq1. Qed.

Lemma eqg_opp x y : (- x == - y) = (x == y).
Proof. exact: eqg_inv. Qed.

Lemma eqg_oppLR x y : (- x == y) = (x == - y).
Proof. exact: eqg_invLR. Qed.

Lemma mulNgn x n : (- x) *+ n = x *- n.
Proof. exact: expVgn. Qed.

Lemma mulgnBl n : {morph (fun x => x *+ n) : x y / x - y}.
Proof.
move=> x y; elim: n => [|n IHn]; rewrite ?subg0 // !mulgS -!addgA; congr(_ + _).
by rewrite addgC IHn -!addgA oppgD [_ - y]addgC.
Qed.

Lemma mulgnBr x m n : n <= m -> x *+ (m - n) = x *+ m - x *+ n.
Proof. exact: expgnBr. Qed.

Section ClosedPredicates.

Variable S : {pred V}.

Definition oppg_closed := {in S, forall u, - u \in S}.
Definition subg_2closed := {in S &, forall u v, u - v \in S}.
Definition zmod_closed := 0 \in S /\ subg_2closed.

Lemma zmod_closedN : zmod_closed -> oppg_closed.
Proof. exact: group_closedV. Qed.

Lemma zmod_closedD : zmod_closed -> addg_closed S.
Proof. exact: group_closedM. Qed.

Lemma zmod_closed0D : zmod_closed -> nmod_closed S.
Proof. by move=> z; split; [case: z|apply: zmod_closedD]. Qed.

End ClosedPredicates.

End ZmoduleTheory.

Arguments addgI {V} y [x1 x2].
Arguments addIg {V} x [x1 x2].
Arguments oppgK {V}.
Arguments oppg_inj {V} [x1 x2].

(* Morphism hierarchy. *)

HB.mixin Record isMultiplicative (U V : magmaType) (apply : U -> V) := {
  gmulfM : {morph apply : x y / x * y}
}.

HB.structure Definition Multiplicative (U V : magmaType) :=
  {f of isMultiplicative U V f}.

(* TODO: define pointedTypes and generalize this to pointedTypes. *)
HB.mixin Record isUmagmaMorphism (U V : umagmaType) (f : U -> V) := {
  gmulf1 : f 1 = 1
}.

HB.structure Definition UmagmaMorphism (U V : umagmaType) := {f of isUmagmaMorphism U V f & isMultiplicative U V f}.

HB.factory Record isGroupMorphism (U V : groupType) (f : U -> V) := {
  gmulfB : {morph f : x y / x / y}
}.

HB.builders Context U V apply of isGroupMorphism U V apply.

Local Lemma gmulf1 : apply 1 = 1.
Proof. by rewrite -[1]divg1 gmulfB divgg. Qed.

Local Lemma gmulfM : {morph apply : x y / x * y}.
Proof.
move=> x y; rewrite -[y in LHS] invgK -[y^-1]mul1g.
by rewrite !gmulfB gmulf1 div1g invgK.
Qed.

HB.instance Definition _ := isMultiplicative.Build U V apply gmulfM.
HB.instance Definition _ := isUmagmaMorphism.Build U V apply gmulf1.

HB.end.

Definition semi_additive (U V : nmodType) (f : U -> V) : Prop :=
  (f 0 = 0) * {morph f : x y / x + y}.

HB.mixin Record isSemiAdditive (U V : nmodType) (apply : U -> V) := {
  semi_additive_subproof : semi_additive apply;
}.

HB.builders Context U V apply of isSemiAdditive U V apply.

Fact gmorphM : {morph apply : x y / x + y}.
Proof. by case: semi_additive_subproof. Qed.
Fact gmorph1 : apply 1 = 1.
Proof. by case: semi_additive_subproof. Qed.

HB.instance Definition _ := isMultiplicative.Build U V apply gmorphM.
HB.instance Definition _ := isUmagmaMorphism.Build U V apply gmorph1.

HB.end.

#[mathcomp(axiom="semi_additive")]
HB.structure Definition Additive (U V : nmodType) :=
  {f of isSemiAdditive U V f}.

Definition additive (U V : zmodType) (f : U -> V) := {morph f : x y / x - y}.

HB.factory Record isAdditive (U V : zmodType) (apply : U -> V) := {
  additive_subproof : additive apply;
}.

HB.builders Context U V apply of isAdditive U V apply.
Local Lemma gaddf0 : apply 0 = 0.
Proof. by rewrite -[0]subg0 additive_subproof subrr. Qed.

Local Lemma gaddfD : {morph apply : x y / x + y}.
Proof.
move=> x y; rewrite -[y in LHS]oppgK -[- y]add0g.
by rewrite !additive_subproof gaddf0 sub0g oppgK.
Qed.

HB.instance Definition _ := isSemiAdditive.Build U V apply (conj gaddf0 gaddfD).

HB.end.

Module AdditiveExports.
Module Additive.
Definition apply_deprecated (U V : nmodType) (phUV : phant (U -> V)) :=
  @Additive.sort U V.
#[deprecated(since="mathcomp 2.0", note="Use Additive.sort instead.")]
Notation apply := apply_deprecated.
End Additive.
Notation "{ 'additive' U -> V }" := (Additive.type U%type V%type) : type_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use GRing.Additive.clone instead.")]
Notation "[ 'additive' 'of' f 'as' g ]" := (Additive.clone _ _ f%function g)
  (at level 0, format "[ 'additive'  'of'  f  'as'  g ]") : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use GRing.Additive.clone instead.")]
Notation "[ 'additive' 'of' f ]" := (Additive.clone _ _ f%function _)
  (at level 0, format "[ 'additive'  'of'  f ]") : form_scope.
End AdditiveExports.
HB.export AdditiveExports.

(*
HB.factory Record isAdditive (U V : nmodType) (f : U -> V) := {
  gaddfD : {morph f : x y / x + y}
}.

HB.builders Context U V apply of isAdditive U V apply.

HB.instance Definition _ := isMultiplicative.Build U V apply gaddfD.

HB.end.

HB.factory Record isNmodMorphism (U V : nmodType) (f : U -> V) := {
  gaddfD : {morph f : x y / x + y};
  gaddf0 : f 0 = 0
}.

Notation "NmodMorphism.type" := (UmagmaMorphism.type).

HB.builders Context U V apply of isNmodMorphism U V apply.

HB.instance Definition _ := isMultiplicative.Build U V apply gaddfD.
HB.instance Definition _ := isUmagmaMorphism.Build U V apply gaddf0.

HB.end.

HB.factory Record isZmodMorphism (U V : zmodType) (f : U -> V) := {
  gaddfB : {morph f : x y / x - y}
}.

HB.builders Context U V apply of isZmodMorphism U V apply.

HB.instance Definition _ := isGroupMorphism.Build U V apply gaddfB.

   HB.end.*)

(* Lifted operations *)
Section LiftedMagma.
Variables (U : Type) (V : magmaType).
Definition mul_fun (f g : U -> V) x := f x * g x.
End LiftedMagma.
Section LiftedUmagma.
Variables (U : Type) (V : umagmaType).
Definition one_fun of U : V := 1.
End LiftedUmagma.
Section LiftedGroup.
Variables (U : Type) (V : groupType).
Definition div_fun (f g : U -> V) x := f x / g x.
Definition inv_fun (f : U -> V) x := (f x)^-1.
End LiftedGroup.
Section LiftedNmod.
Variables (U : Type) (V : nmodType).
Definition null_fun of U : V := 0.
Definition add_fun (f g : U -> V) x := f x + g x.
End LiftedNmod.
Section LiftedZmod.
Variables (U : Type) (V : zmodType).
Definition sub_fun (f g : U -> V) x := f x - g x.
Definition opp_fun (f : U -> V) x := - f x.
End LiftedZmod.

Local Notation "\1" := (one_fun _) : group_scope.
Local Notation "f \* g" := (mul_fun f g) : group_scope.
Local Notation "f \\/ g" := (div_fun f g) : group_scope.
Local Notation "f \^-1" := (inv_fun f) : group_scope.
Local Notation "\0" := (null_fun _) : group_scope.
Local Notation "f \+ g" := (add_fun f g) : group_scope.
Local Notation "f \- g" := (sub_fun f g) : group_scope.
Local Notation "\- f" := (opp_fun f) : group_scope.

Arguments one_fun {_} V _ /.
Arguments mul_fun {_ _} f g _ /.
Arguments div_fun {_ _} f g _ /.
Arguments inv_fun {_ _} f _ /.
Arguments null_fun {_} V _ /.
Arguments add_fun {_ _} f g _ /.
Arguments sub_fun {_ _} f g _ /.
Arguments opp_fun {_ _} f _ /.

Section MorphismTheory.

Section Magma.
Variables (U V : magmaType) (f : Multiplicative.type U V).

Lemma can2_gmulfM f' : cancel f f' -> cancel f' f -> {morph f' : x y / x * y}.
Proof. by move=> fK f'K x y; apply: (canLR fK); rewrite gmulfM !f'K. Qed.

Lemma gmulf_commute x y : commute x y -> commute (f x) (f y).
Proof. by move=> xy; rewrite /commute -!gmulfM xy. Qed.

End Magma.

Section Umagma.
Variables (U V : umagmaType) (f : UmagmaMorphism.type U V).

Lemma gmulf_eq1 x : injective f -> (f x == 1) = (x == 1).
Proof. by move=> /inj_eq <-; rewrite gmulf1. Qed.

Lemma gmulfXn n : {morph f : x / x ^+ n}.
Proof.
(* TOTHINK: The simplification after gmulfM should not be necessary. *)
by elim: n => [|n IHn] x /=; rewrite ?gmulf1 // !expgS gmulfM/= IHn.
Qed.

Lemma can2_gmulf1 f' : cancel f f' -> cancel f' f -> f' 1 = 1.
Proof. by move=> fK f'K; apply: (canLR fK); rewrite gmulf1. Qed.
End Umagma.

Section Group.
Variables (U V : groupType) (f : UmagmaMorphism.type U V).

Lemma gmulfV : {morph f : x / x^-1}.
Proof.
move=> x; apply/eqP.
by rewrite -mulg_eq1 -gmulfM mulVg/= gmulf1.
Qed.

Lemma gmulfB : {morph f : x y / x / y}.
Proof. by move=> x y; rewrite gmulfM -gmulfV. Qed.

Lemma gmulf_inj : (forall x, f x = 1 -> x = 1) -> injective f.
Proof. by move=> fI x y xy; apply/divg1_eq/fI; rewrite gmulfB xy divgg. Qed.

Lemma gmulfXVn n : {morph f : x / x ^- n}.
Proof. by move=> x /=; rewrite gmulfV gmulfXn. Qed.

Lemma gmulf_conj : {morph f : x y / x ^ y}.
Proof. by move=> x y; rewrite !gmulfM/= gmulfV. Qed.

Lemma gmulf_comm : {morph f : x y / [~ x, y]}.
Proof. by move=> x y; rewrite !gmulfM/= !gmulfV. Qed.
End Group.

Section Nmod.
Variables (U V : nmodType) (f : {additive U -> V}).

Lemma gaddf0 : f 0 = 0.
Proof. exact: gmulf1. Qed.

Lemma gaddf_eq0 x : injective f -> (f x == 0) = (x == 0).
Proof. exact: (@gmulf_eq1 U V f). Qed.

Lemma gaddfD : {morph f : x y / x + y}.
Proof. exact: gmulfM. Qed.

Lemma gaddfMn n : {morph f : x / x *+ n}.
Proof. exact: (@gmulfXn U V f). Qed.

Lemma can2_semi_additive f' : cancel f f' -> cancel f' f -> semi_additive f'.
Proof. by split; [apply: (@can2_gmulf1 U V f)|apply/can2_gmulfM]. Qed.
End Nmod.

Section Zmod.
Variables (U V : zmodType) (f : {additive U -> V}).

Lemma gaddfN : {morph f : x / - x}.
Proof. exact: (@gmulfV U V f). Qed.

Lemma gaddfB : {morph f : x y / x - y}.
Proof. exact: (@gmulfB U V f). Qed.

Lemma gaddf_inj : (forall x, f x = 0 -> x = 0) -> injective f.
Proof. exact: (@gmulf_inj U V f). Qed.

Lemma gaddfMNn n : {morph f : x / x *- n}.
Proof. exact: (@gmulfXVn U V f). Qed.

Lemma can2_additive f' : cancel f f' -> cancel f' f -> additive f'.
Proof. by move=> fK f'K x y /=; apply: (canLR fK); rewrite gaddfB !f'K. Qed.
End Zmod.

Section MulFun.
Variables (U V W : magmaType).
Variables (f g : Multiplicative.type V W) (h : Multiplicative.type U V).

Fact idfun_gmulfM : {morph @idfun U : x y / x * y}.
Proof. by []. Qed.
#[export]
HB.instance Definition _ := isMultiplicative.Build U U idfun idfun_gmulfM.

Fact comp_gmulfM : {morph f \o h : x y / x * y}.
Proof. by move=> x y /=; rewrite !gmulfM. Qed.
#[export]
HB.instance Definition _ := isMultiplicative.Build U W (f \o h) comp_gmulfM.
End MulFun.

Section Mul1Fun.
Variables (U : magmaType) (V : umagmaType).

Fact idfun_gmulf1 : idfun 1 = 1 :> V.
Proof. by []. Qed.
HB.instance Definition _ := isUmagmaMorphism.Build V V idfun idfun_gmulf1.

Fact one_fun_gmulfM : {morph @one_fun U V : x y / x * y}.
Proof. by move=> x y; rewrite mulg1. Qed.
HB.instance Definition _ := isMultiplicative.Build U V (@one_fun U V) one_fun_gmulfM.
End Mul1Fun.

Section Mul11Fun.
Variables (U V W : umagmaType).
Variables (f g : UmagmaMorphism.type V W) (h : UmagmaMorphism.type U V).

Fact comp_gmulf1 : (f \o h) 1 = 1.
Proof. by rewrite /= !gmulf1. Qed.
HB.instance Definition _ := isUmagmaMorphism.Build U W (f \o h) comp_gmulf1.

Fact one_fun_gmulf1 : @one_fun U V 1 = 1.
Proof. by []. Qed.
HB.instance Definition _ := isUmagmaMorphism.Build U V (@one_fun U V) one_fun_gmulf1.

Fact mul_fun_gmulf1 : (f \* g) 1 = 1.
Proof. by rewrite /mul_fun /= !gmulf1 mulg1. Qed.
HB.instance Definition _ := isUmagmaMorphism.Build V W (f \* g) mul_fun_gmulf1.
End Mul11Fun.

Section MulCFun.
Variables (U : magmaType) (V : nmodType).
Variables (f g : Multiplicative.type U V).

Fact mul_fun_gmulfM : {morph f \* g : x y / x * y}.
Proof. by move=> x y; rewrite /mul_fun !gmulfM [LHS]addgACA. Qed.
HB.instance Definition _ := isMultiplicative.Build U V (f \* g) mul_fun_gmulfM.
End MulCFun.

Section AddFun.

Variables (U V W : nmodType).
Variables (f g : {additive V -> W}) (h : {additive U -> V}).

Fact idfun_is_semi_additive : semi_additive (@idfun U).
Proof. by []. Qed.
#[export]
HB.instance Definition _ := isSemiAdditive.Build U U idfun
  idfun_is_semi_additive.

Fact comp_is_semi_additive : semi_additive (f \o h).
Proof. by split=> [|x y]; rewrite /= ?gaddf0// !gaddfD. Qed.
#[export]
HB.instance Definition _ := isSemiAdditive.Build U W (f \o h)
  comp_is_semi_additive.

Fact null_fun_is_semi_additive : semi_additive (\0 : U -> V).
Proof. by split=> // x y /=; rewrite addg0. Qed.
#[export]
HB.instance Definition _ := isSemiAdditive.Build U V \0
  null_fun_is_semi_additive.

Fact add_fun_is_semi_additive : semi_additive (f \+ g).
Proof.
by split=> [|x y]; rewrite /= ?gaddf0 ?addg0// !gaddfD addgCA -!addgA addgCA.
Qed.
#[export]
HB.instance Definition _ := isSemiAdditive.Build V W (f \+ g)
  add_fun_is_semi_additive.

End AddFun.

Section AddVFun.
Variables (U V W : zmodType).
Variables (f g : {additive V -> W}) (h : {additive U -> V}).

Fact opp_is_semi_additive : semi_additive (@opp U).
Proof. by split; [apply/oppg0|apply/oppgD]. Qed.
HB.instance Definition _ :=
  isSemiAdditive.Build U U (@opp U) opp_is_semi_additive.

Fact sub_fun_is_additive : additive (f \- g).
Proof.
by move=> x y /=; rewrite !gaddfB addgAC -!addgA -!oppgD addgAC addgA.
Qed.
HB.instance Definition _ :=
  isAdditive.Build V W (f \- g) sub_fun_is_additive.

Fact opp_fun_is_additive : additive (\- g).
Proof. by move=> x y /=; rewrite !gaddfB oppgB addgC oppgK. Qed.
#[export]
HB.instance Definition _ := isAdditive.Build V W (\- g) opp_fun_is_additive.

End AddVFun.
End MorphismTheory.

(* Mixins for stability properties *)

HB.mixin Record isMulClosed (V : magmaType) (S : {pred V}) := {
  gpredM : mulg_closed S
}.

HB.mixin Record isMul1Closed (V : umagmaType) (S : {pred V}) := {
  gpred1 : 1 \in S
}.

HB.mixin Record isInvClosed (V : groupType) (S : {pred V}) := {
  gpredVr : invg_closed S
}.

HB.mixin Record isAddClosed (V : nmodType) (S : {pred V}) := {
  gpred0D : nmod_closed S
}.

HB.builders Context V S of isAddClosed V S.
HB.instance Definition _ := isMulClosed.Build V S (snd gpred0D).
HB.instance Definition _ := isMul1Closed.Build V S (fst gpred0D).
HB.end.

HB.mixin Record isOppClosed (V : zmodType) (S : {pred V}) := {
  gpredNr : oppg_closed S
}.

HB.builders Context V S of isOppClosed V S.
HB.instance Definition _ := isInvClosed.Build V S gpredNr.
HB.end.

(* Structures for stability properties *)

#[short(type="mulgClosed")]
HB.structure Definition MulClosed V := {S of isMulClosed V S}.

#[short(type="umagmaClosed")]
HB.structure Definition UmagmaClosed V := {S of isMul1Closed V S & isMulClosed V S}.

#[short(type="invgClosed")]
HB.structure Definition InvClosed V := {S of isInvClosed V S}.

#[short(type="groupClosed")]
HB.structure Definition GroupClosed V := {S of isInvClosed V S & isMul1Closed V S & isMulClosed V S}.

#[short(type="addgClosed")]
HB.structure Definition AddClosed V := {S of isAddClosed V S}.

#[short(type="oppgClosed")]
HB.structure Definition OppClosed V := {S of isOppClosed V S}.

#[short(type="zmodClosed")]
HB.structure Definition ZmodClosed V := {S of OppClosed V S & AddClosed V S & isAddClosed V S}.

(* Factories for stability properties *)

HB.factory Record isZmodClosed (V : zmodType) (S : V -> bool) := {
  zmod_closed_subproof : zmod_closed S
}.

HB.builders Context V S of isZmodClosed V S.
HB.instance Definition _ := isOppClosed.Build V S
  (zmod_closedN zmod_closed_subproof).
HB.instance Definition _ := isAddClosed.Build V S
  (zmod_closed0D zmod_closed_subproof).
HB.end.

Section UmagmaPred.
Variables (V : umagmaType).

Section Umagma.
Variables S : umagmaClosed V.

Lemma gpredXn n : {in S, forall u, u ^+ n \in S}.
Proof. by move=> x xS; elim: n => [|n IHn]; rewrite ?gpred1 // expgS gpredM. Qed.

End Umagma.
End UmagmaPred.

Section GroupPred.
Variables (V : groupType).

Section Group.
Variables S : groupClosed V.

Lemma gpredV : {mono /%G: u / u \in S}.
Proof. by move=> u; apply/idP/idP=> /gpredVr; rewrite ?invgK; apply. Qed.

Lemma gpredF : {in S &, forall u v, u / v \in S}.
Proof. by move=> x y xS yS; rewrite gpredM// gpredV. Qed.

Lemma gpredFC u v : u / v \in S = (v / u \in S).
Proof. by rewrite -gpredV invgF. Qed.

Lemma gpredXNn n: {in S, forall u, u ^- n \in S}.
Proof. by move=> x xS; apply/gpredVr/gpredXn. Qed.

Lemma gpredMr x y : x \in S -> (y * x \in S) = (y \in S).
Proof.
move=> Sx; apply/idP/idP => [Sxy|/gpredM-> //].
by rewrite -(mulgK x y) gpredF.
Qed.

Lemma gpredMl x y : x \in S -> (x * y \in S) = (y \in S).
Proof.
move=> Sx; apply/idP/idP => [Sxy|/(gpredM x y Sx)//].
by rewrite -[y]mul1g -(mulVg x) -mulgA gpredM// gpredV.
Qed.

Lemma gpredFr x y : x \in S -> (y / x \in S) = (y \in S).
Proof. by rewrite -gpredV; apply: gpredMr. Qed.

Lemma gpredFl x y : x \in S -> (x / y \in S) = (y \in S).
Proof. by rewrite -(gpredV y); apply: gpredMl. Qed.

Lemma gpred_conj x y : x \in S -> y \in S -> x ^ y \in S.
Proof. by move=> xS yS; apply/gpredM; [apply/gpredVr|apply/gpredM]. Qed.

Lemma gpred_comm x y : x \in S -> y \in S -> [~ x, y] \in S.
Proof. by move=> xS yS; apply/gpredM; [apply/gpredVr|apply/gpred_conj]. Qed.

End Group.
End GroupPred. 

Section NmodPred.
Variables (V : nmodType).

Section Nmod.
Variables S : addgClosed V.

Lemma gpred0 : 0 \in S.
Proof. by case: (@gpred0D V S). Qed.
Lemma gpredD : {in S &, forall u v, u + v \in S}.
Proof. by case: (@gpred0D V S). Qed.

Lemma gpredMn n : {in S, forall u, u *+ n \in S}.
Proof. by move=> x xS; elim: n => [|n IHn]; rewrite /= ?gpred0 // mulgS gpredD. Qed.

End Nmod.
End NmodPred.

Section ZmodPred.
Variables (V : zmodType).

Section Opp.

Variable S : oppgClosed V.

Lemma gpredN : {mono -%G: u / u \in S}.
Proof. by move=> u; apply/idP/idP=> /gpredNr; rewrite ?oppgK; apply. Qed.

End Opp.

Section Zmod.
Variables S : zmodClosed V.

Lemma gpredB : {in S &, forall u v, u - v \in S}.
Proof. by move=> x y xS yS; rewrite gpredD// gpredN. Qed.

Lemma gpredBC u v : u - v \in S = (v - u \in S).
Proof. by rewrite -gpredN oppgB. Qed.

Lemma gpredMNn n: {in S, forall u, u *- n \in S}.
Proof. by move=> x xS; apply/gpredNr/gpredMn. Qed.

Lemma gpredDr x y : x \in S -> (y + x \in S) = (y \in S).
Proof.
move=> Sx; apply/idP/idP => [Sxy|/gpredD-> //].
by rewrite -(addgK x y) gpredB.
Qed.

Lemma gpredDl x y : x \in S -> (x + y \in S) = (y \in S).
Proof.
move=> Sx; apply/idP/idP => [Sxy|/(gpredD Sx)//].
by rewrite -[y]add0g -(addNg x) -addgA gpredD// gpredN.
Qed.

Lemma gpredBr x y : x \in S -> (y - x \in S) = (y \in S).
Proof. by rewrite -gpredN; apply: gpredDr. Qed.

Lemma gpredBl x y : x \in S -> (x - y \in S) = (y \in S).
Proof. by rewrite -[x \in S]gpredN -[LHS]gpredN oppgB; apply: gpredDr. Qed.

End Zmod.
End ZmodPred. 

HB.mixin Record isSubMagma (V : magmaType) (S : pred V) U
    of SubType V S U & Magma U := {
  valM_subproof : {morph (val : U -> V) : x y / x * y}
}.

#[short(type="subMagmaType")]
HB.structure Definition SubMagma (V : magmaType) S :=
  { U of SubChoice V S U & Magma U & isSubMagma V S U }.

Section subMagma.
Context (V : magmaType) (S : pred V) (U : subMagmaType S).
Notation val := (val : U -> V).
#[export]
HB.instance Definition _ := isMultiplicative.Build U V val valM_subproof.
Lemma valM : {morph val : x y / x * y}. Proof. exact: gmulfM. Qed.
End subMagma.

HB.factory Record SubChoice_isSubMagma (V : magmaType) S U
    of SubChoice V S U := {
  mulg_closed_subproof : mulg_closed S
}.

HB.builders Context V S U of SubChoice_isSubMagma V S U.

HB.instance Definition _ := isMulClosed.Build V S mulg_closed_subproof.

Let inU v Sv : U := Sub v Sv.
Let mulU (u1 u2 : U) := inU (gpredM _ _ (valP u1) (valP u2)).

HB.instance Definition _ := isMagma.Build U mulU.

Lemma valM : {morph (val : U -> V) : x y / x * y}.
Proof. by move=> x y; rewrite SubK. Qed.

HB.instance Definition _ := isSubMagma.Build V S U valM.

HB.end.

#[short(type="subUmagmaType")]
HB.structure Definition SubSemigroup (V : semigroupType) S :=
  { U of SubMagma V S U & Semigroup U}.

HB.factory Record SubChoice_isSubSemigroup (V : semigroupType) S U
    of SubChoice V S U := {
  mulg_closed_subproof : mulg_closed S
}.

HB.builders Context V S U of SubChoice_isSubSemigroup V S U.

HB.instance Definition _ := SubChoice_isSubMagma.Build V S U mulg_closed_subproof.

Lemma mulgA : associative (@mul U).
Proof. by move=> x y z; apply/val_inj; rewrite !valM mulgA. Qed.

HB.instance Definition _ := isSemigroup.Build U mulgA.

HB.end.

HB.mixin Record isSubUmagma (V : umagmaType) (S : pred V) U
    of SubMagma V S U & Umagma U := {
  val1_subproof : (val : U -> V) 1 = 1
}.

#[short(type="subUmagmaType")]
HB.structure Definition SubUmagma (V : umagmaType) S :=
  { U of SubMagma V S U & Umagma U & isSubUmagma V S U}.

Section subUmagma.
Context (V : umagmaType) (S : pred V) (U : subUmagmaType S).
Notation val := (val : U -> V).
#[export]
HB.instance Definition _ := isUmagmaMorphism.Build U V val val1_subproof.
Lemma val1 : val 1 = 1. Proof. exact: gmulf1. Qed.
End subUmagma.

HB.factory Record SubChoice_isSubUmagma (V : umagmaType) S U
    of SubChoice V S U := {
  umagma_closed_subproof : umagma_closed S
}.

HB.builders Context V S U of SubChoice_isSubUmagma V S U.

HB.instance Definition _ := SubChoice_isSubMagma.Build V S U (snd umagma_closed_subproof).

Let inU v Sv : U := Sub v Sv.
Let oneU := inU (fst umagma_closed_subproof).

Lemma mul1g : left_id oneU *%G.
Proof. by move=> x; apply/val_inj; rewrite valM SubK mul1g. Qed.
Lemma mulg1 : right_id oneU *%G.
Proof. by move=> x; apply/val_inj; rewrite valM SubK mulg1. Qed.

HB.instance Definition _ := Magma_isUmagma.Build U mul1g mulg1.

Lemma val1 : (val : U -> V) 1 = 1. 
Proof. exact/SubK. Qed.

HB.instance Definition _ := isSubUmagma.Build V S U val1.

HB.end.

#[short(type="subMonoidType")]
HB.structure Definition SubMonoid (V : monoidType) S :=
  { U of SubUmagma V S U & Monoid U}.

HB.factory Record SubChoice_isSubMonoid (V : monoidType) S U
    of SubChoice V S U := {
  monoid_closed_subproof : monoid_closed S
}.

HB.builders Context V S U of SubChoice_isSubMonoid V S U.

HB.instance Definition _ := SubChoice_isSubUmagma.Build V S U monoid_closed_subproof.
HB.instance Definition _ := SubChoice_isSubSemigroup.Build V S U (snd monoid_closed_subproof).

HB.end.

#[short(type="subNmodType")]
HB.structure Definition SubNmodule (V : nmodType) S :=
  { U of SubMonoid V S U & Nmodule U}.

Section subNmodule.
Context (V : nmodType) (S : pred V) (U : subNmodType S).
Notation val := (val : U -> V).
Fact val_is_semi_additive : semi_additive val.
Proof. by split; [apply/val1|apply/valM]. Qed.
#[export]
HB.instance Definition _ := isSemiAdditive.Build U V val val_is_semi_additive.
Lemma valD : {morph (val : U -> V) : x y / x + y}.
Proof. exact: valM. Qed.
Lemma val0 : val 0 = 0. Proof. exact: val1. Qed.
End subNmodule.

HB.factory Record SubChoice_isSubNmodule (V : nmodType) S U
    of SubChoice V S U := {
  nmod_closed_subproof : nmod_closed S
}.

HB.builders Context V S U of SubChoice_isSubNmodule V S U.

HB.instance Definition _ := isAddClosed.Build V S nmod_closed_subproof.

HB.instance Definition _ := SubChoice_isSubUmagma.Build V S U nmod_closed_subproof.
HB.instance Definition _ := SubChoice_isSubSemigroup.Build V S U (snd nmod_closed_subproof).

Lemma mulgC : commutative (@mul U).
Proof. by move=> x y; apply/val_inj; rewrite !valM mulgC. Qed.

HB.instance Definition _ := Monoid_isNmodule.Build U mulgC.

HB.end.

#[short(type="subUmagmaType")]
HB.structure Definition SubGroup (V : groupType) S :=
  { U of SubUmagma V S U & Group U}.

HB.factory Record SubChoice_isSubGroup (V : groupType) S U
    of SubChoice V S U := {
  group_closed_subproof : group_closed S
}.

HB.builders Context V S U of SubChoice_isSubGroup V S U.

Lemma umagma_closed : umagma_closed S.
Proof.
by split; [apply/(fst group_closed_subproof)|apply/group_closedM/group_closed_subproof].
Qed.
HB.instance Definition _ := SubChoice_isSubMonoid.Build V S U umagma_closed.
HB.instance Definition _ := isInvClosed.Build V S (group_closedV group_closed_subproof).

Let inU v Sv : U := Sub v Sv.
Let invU (u : U) := inU (gpredVr _ (valP u)).

Lemma mulVg : left_inverse 1%G invU *%G.
Proof. by move=> x; apply/val_inj; rewrite valM SubK mulVg val1. Qed. 
Lemma mulgV : right_inverse 1%G invU *%G.
Proof. by move=> x; apply/val_inj; rewrite valM SubK mulgV val1. Qed. 

HB.instance Definition _ := Monoid_isGroup.Build U mulVg mulgV.

HB.end.

#[short(type="subZmodType")]
HB.structure Definition SubZmodule (V : zmodType) S :=
  { U of SubMonoid V S U & Zmodule U}.

Section additive.
Context (V : zmodType) (S : pred V) (U : SubZmodule.type S).
Notation val := (val : U -> V).
Lemma valB : {morph val : x y / x - y}. Proof. exact: gaddfB. Qed.
Lemma valN : {morph val : x / - x}. Proof. exact: gaddfN. Qed.
End additive.

HB.factory Record SubChoice_isSubZmodule (V : zmodType) S U
    of SubChoice V S U := {
  zmod_closed_subproof : zmod_closed S
}.

HB.builders Context V S U of SubChoice_isSubZmodule V S U.

HB.instance Definition _ :=
  SubChoice_isSubGroup.Build V S U zmod_closed_subproof.

Lemma mulgC : commutative (@mul U).
Proof. by move=> x y; apply/val_inj; rewrite !valM mulgC. Qed.

HB.instance Definition _ := Monoid_isNmodule.Build U mulgC.

HB.end.

(* Lifting Structure from the codomain of finfuns. *)
Section FinFunMagma.
Variable (aT : finType) (rT : magmaType).
Implicit Types f g : {ffun aT -> rT}.

Definition ffun_mul f g := [ffun a => f a * g a].

HB.instance Definition _ := isMagma.Build {ffun aT -> rT} ffun_mul.

End FinFunMagma.

Section FinFunUmagma.
Variable (aT : finType) (rT : umagmaType).
Implicit Types f g : {ffun aT -> rT}.

Definition ffun_one := [ffun a : aT => (1 : rT)].

Fact ffun_mul1g : left_id ffun_one *%G.
Proof. by move=> f; apply/ffunP => a; rewrite !ffunE mul1g. Qed.
Fact ffun_mulg1 : right_id ffun_one *%G.
Proof. by move=> f; apply/ffunP => a; rewrite !ffunE mulg1. Qed.

HB.instance Definition _ :=
  Magma_isUmagma.Build {ffun aT -> rT} ffun_mul1g ffun_mulg1.

End FinFunUmagma.

Section FinFunSemigroup.
Variable (aT : finType) (rT : semigroupType).
Implicit Types f g : {ffun aT -> rT}.

Fact ffun_mulgA : associative (@ffun_mul aT rT).
Proof. by move=> f1 f2 f3; apply/ffunP=> a; rewrite !ffunE mulgA. Qed.

HB.instance Definition _ := isSemigroup.Build {ffun aT -> rT} ffun_mulgA.

End FinFunSemigroup.

HB.instance Definition _ (aT : finType) (rT : monoidType) :=
  Umagma_isMonoid.Build {ffun aT -> rT} (@ffun_mulgA aT rT).

Section FinFunNmod.

Variable (aT : finType) (rT : nmodType).
Implicit Types f g : {ffun aT -> rT}.

(* TODO: find a way to make the following instance use these definitions. *)
Definition ffun_add f g := [ffun a => f a + g a].
Definition ffun_zero := [ffun a : aT => (0 : rT)].

Fact ffun_addgC : commutative ffun_add.
Proof. by move=> f1 f2; apply/ffunP=> a; rewrite !ffunE; rewrite addgC. Qed.

#[export]
HB.instance Definition _ := Monoid_isNmodule.Build {ffun aT -> rT} ffun_addgC.

Lemma ffunMnE f n x : (f *+ n) x = f x *+ n.
Proof.
(* TODO: the `rewrite ffunE` produces a `1` where I would like a `0` (which comes from `ffun_one`). *)
elim: n => [|n IHn]; first by rewrite ffunE.
by rewrite !mulgS ffunE IHn.
Qed.

End FinFunNmod.

Section FinFunGroup.

Variable (aT : finType) (rT : groupType).
Implicit Types f g : {ffun aT -> rT}.

Definition ffun_inv f := [ffun a => (f a)^-1].

Fact ffun_addNg : left_inverse (@ffun_one _ _) ffun_inv (@ffun_mul _ _).
Proof. by move=> f; apply/ffunP=> a; rewrite !ffunE mulVg. Qed.
Fact ffun_addgN : right_inverse (@ffun_one _ _) ffun_inv (@ffun_mul _ _).
Proof. by move=> f; apply/ffunP=> a; rewrite !ffunE mulgV. Qed.

#[export]
HB.instance Definition _ := Monoid_isGroup.Build {ffun aT -> rT}
  ffun_addNg ffun_addgN.

End FinFunGroup.

(* TODO: HB.saturate *)
#[export]
HB.instance Definition _ (aT : finType) (rT : zmodType) := Group_isZmodule.Build {ffun aT -> rT} (@ffun_addgC aT rT).

(* External direct product *)
Section PairMagma.
Variables U V : magmaType.

Definition mul_pair (x y : U * V) := (x.1 * y.1, x.2 * y.2).

#[export]
HB.instance Definition _ := isMagma.Build (U * V)%type mul_pair.

Fact fst_is_multiplicative : {morph fst : x y / x * y}. Proof. by []. Qed.
#[export]
HB.instance Definition _ := isMultiplicative.Build _ _ _ fst_is_multiplicative.

Fact snd_is_multiplicative : {morph snd : x y / x * y}. Proof. by []. Qed.
#[export]
HB.instance Definition _ := isMultiplicative.Build _ _ _ snd_is_multiplicative.

End PairMagma.

Section PairSemigroup.
Variables U V : semigroupType.

Lemma pair_mulgA : associative (@mul (U * V)%type).
Proof. by move=> x y z; congr (_, _); apply/mulgA. Qed.

HB.instance Definition _ := Magma_isSemigroup.Build (U * V)%type pair_mulgA.

End PairSemigroup.

Section PairUmagma.
Variables U V : umagmaType.

Definition one_pair  := (1 : U, 1 : V).

Lemma pair_mul1g : left_id one_pair *%G.
Proof. by move=> [x y]; congr (_, _); rewrite mul1g. Qed.
Lemma pair_mulg1 : right_id one_pair *%G.
Proof. by move=> [x y]; congr (_, _); rewrite mulg1. Qed.

#[export]
HB.instance Definition _ := Magma_isUmagma.Build (U * V)%type pair_mul1g pair_mulg1.

Fact fst_is_umagma_morphism : fst (1 : (U * V)%type) = 1. Proof. by []. Qed.
#[export]
HB.instance Definition _ := isUmagmaMorphism.Build _ _ _ fst_is_umagma_morphism.

Fact snd_is_umagma_morphism : snd (1 : (U * V)%type) = 1. Proof. by []. Qed.
#[export]
HB.instance Definition _ := isUmagmaMorphism.Build _ _ _ snd_is_umagma_morphism.

End PairUmagma.

(* TOTHINK: Should not this be done automatically by HB? *)
HB.instance Definition _ (U V : monoidType) := Umagma_isMonoid.Build (U * V)%type (@pair_mulgA U V).

Section PairNmodule.
Variables U V : nmodType.

Lemma pair_mulgC : commutative (@mul (U * V)%type).
Proof. by move=> x y; congr (_, _); apply/mulgC. Qed.

HB.instance Definition _ := Monoid_isNmodule.Build (U * V)%type pair_mulgC.

HB.instance Definition _ := isSemiAdditive.Build (U * V)%type U (@fst U V) (@fst_is_umagma_morphism U V, @fst_is_multiplicative U V)%PAIR.
HB.instance Definition _ := isSemiAdditive.Build (U * V)%type V (@snd U V) (@snd_is_umagma_morphism U V, @snd_is_multiplicative U V)%PAIR.

End PairNmodule.

Section PairGroup.
Variables U V : groupType.

Definition inv_pair (u : U * V) := (u.1 ^-1, u.2 ^-1).

Lemma pair_mulVg : left_inverse one inv_pair mul.
Proof. by move=> x; congr (_, _); apply/mulVg. Qed.
Lemma pair_mulgV : right_inverse one inv_pair mul.
Proof. by move=> x; congr (_, _); apply/mulgV. Qed.

HB.instance Definition _ := Monoid_isGroup.Build (U * V)%type pair_mulVg pair_mulgV.

End PairGroup.

(* TODO: HB.saturate *)
HB.instance Definition _ (U V : zmodType) := Group_isZmodule.Build (U * V)%type (@pair_mulgC U V).


(* zmodType structure on bool *)
HB.instance Definition _ := isZmodule.Build bool addbA addbC addFb addbb.

(* nmodType structure on nat *)
HB.instance Definition _ := isNmodule.Build nat addnA addnC add0n.

HB.instance Definition _ (V : nmodType) (x : V) :=
  isSemiAdditive.Build nat V (natmul x) (mulg0n x, mulgnDr x).

Lemma natg0E : 0 = 0%N. Proof. by []. Qed.
Lemma natgDE n m : n + m = (n + m)%N. Proof. by []. Qed.
Definition natgE := (natg0E, natgDE).

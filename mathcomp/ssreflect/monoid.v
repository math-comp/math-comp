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
(*                          a addgClosed                                      *)
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

Reserved Notation "*%g" (at level 0).
Reserved Notation "\1" (at level 0).
Reserved Notation "f \* g" (at level 40, left associativity).

Reserved Notation "'{' 'multiplicative' G '->' H '}'"
  (at level 0, G at level 98, H at level 99,
   format "{ 'multiplicative'  G  ->  H }").

Declare Scope group_scope.
Delimit Scope group_scope with g.
Local Open Scope group_scope.

HB.mixin Record isMagma G := {
  mul : G -> G -> G
}.

#[short(type="magmaType")]
HB.structure Definition Magma := {G of isMagma G & Choice G}.

Local Notation "*%g" := (@mul _) : function_scope.
Local Notation "x * y" := (mul x y) : group_scope.

Section MagmaTheory.

Variable G : magmaType.
Implicit Types x y : G.

Definition commute x y := x * y = y * x.

Lemma commute_refl x : commute x x.
Proof. by []. Qed.

Lemma commute_sym x y : commute x y -> commute y x.
Proof. by []. Qed.

Section ClosedPredicates.

Variable S : {pred G}.

Definition mulg_closed := {in S &, forall u v, u * v \in S}.

End ClosedPredicates.

End MagmaTheory.

HB.mixin Record Magma_isSemigroup G of Magma G := {
  mulgA : associative (@mul G)
}.

#[short(type="semigroupType")]
HB.structure Definition Semigroup := {G of Magma_isSemigroup G & Magma G}.

HB.factory Record isSemigroup G of Choice G := {
  mul : G -> G -> G;
  mulgA : associative mul
}.

HB.builders Context G of isSemigroup G.

HB.instance Definition _ := isMagma.Build G mul.
HB.instance Definition _ := Magma_isSemigroup.Build G mulgA.

HB.end.

Section SemigroupTheory.
Variable G : semigroupType.
Implicit Types x y : G.

Lemma commuteM x y z : commute x y -> commute x z -> commute x (y * z).
Proof. by move=> cxy cxz; rewrite /commute -mulgA -cxz !mulgA cxy. Qed.

End SemigroupTheory.

HB.mixin Record Magma_isBaseUMagma G of Magma G := {
  one : G
}.

#[short(type="baseUMagmaType")]
HB.structure Definition BaseUMagma := {G of Magma_isBaseUMagma G & Magma G}.

Local Notation "1" := (@one _) : group_scope.
Local Notation "s `_ i" := (nth 1 s i) : group_scope.

Definition natexp (G : baseUMagmaType) (x : G) n : G := iterop n *%g x 1.
Arguments natexp : simpl never.

Local Notation "x ^+ n" := (natexp x n) : group_scope.

Section baseUMagmaTheory.

Variable G : baseUMagmaType.
Implicit Types x : G.
Lemma expg0n x : x ^+ 0 = 1. Proof. by []. Qed.
Lemma expg1n x : x ^+ 1 = x. Proof. by []. Qed.
Lemma expg2n x : x ^+ 2 = x * x. Proof. by []. Qed.

Lemma expgSS x n : x ^+ n.+2 = x * x ^+ n.+1.
Proof. by []. Qed.

Lemma expgb x (b : bool) : x ^+ b = (if b then x else 1).
Proof. by case: b. Qed.

Section ClosedPredicates.

Variable S : {pred G}.

Definition umagma_closed := 1 \in S /\ mulg_closed S.

End ClosedPredicates.

End baseUMagmaTheory.

HB.mixin Record BaseUMagma_isUMagma G of BaseUMagma G := {
  mul1g : left_id one (@mul G);
  mulg1 : right_id one (@mul G)
}.

HB.factory Record Magma_isUMagma G of Magma G := {
  one : G;
  mul1g : left_id one (@mul G);
  mulg1 : right_id one (@mul G)
}.

HB.builders Context G of Magma_isUMagma G.
HB.instance Definition _ := Magma_isBaseUMagma.Build G one.
HB.instance Definition _ := BaseUMagma_isUMagma.Build G mul1g mulg1.
HB.end.

#[short(type="umagmaType")]
HB.structure Definition UMagma := {G of Magma_isUMagma G & Magma G}.

Section UMagmaTheory.

Variable G : umagmaType.
Implicit Types x y : G.

Lemma expgS x n : x ^+ n.+1 = x * x ^+ n.
Proof. by case: n => //=; rewrite mulg1. Qed.

Lemma exp1gn n : 1 ^+ n = 1 :> G.
Proof. by elim: n => // n IHn; rewrite expgS mul1g. Qed.

Lemma commute1 x : commute x 1.
Proof. by rewrite /commute mulg1 mul1g. Qed.

End UMagmaTheory.

#[short(type="monoidType")]
HB.structure Definition Monoid :=
  {G of Magma_isUMagma G & Semigroup G}.

HB.factory Record Semigroup_isMonoid G of Semigroup G := {
  one : G;
  mul1g : left_id one mul;
  mulg1 : right_id one mul
}.

HB.builders Context G of Semigroup_isMonoid G.

HB.instance Definition _ := Magma_isUMagma.Build G mul1g mulg1.

HB.end.

HB.factory Record UMagma_isMonoid G of UMagma G := {
  mulgA : associative (@mul G)
}.

HB.builders Context G of UMagma_isMonoid G.

HB.instance Definition _ := Magma_isSemigroup.Build G mulgA.

HB.end.

HB.factory Record isMonoid G of Choice G := {
  mul : G -> G -> G;
  one : G;
  mulgA : associative mul;
  mul1g : left_id one mul;
  mulg1 : right_id one mul
}.

HB.builders Context G of isMonoid G.

HB.instance Definition _ := isMagma.Build G mul.
HB.instance Definition _ := Magma_isSemigroup.Build G mulgA.
HB.instance Definition _ := Magma_isUMagma.Build G mul1g mulg1.

HB.end.

Section MonoidTheory.

Variable G : monoidType.
Implicit Types x y : G.

Lemma expgSr x n : x ^+ n.+1 = x ^+ n * x.
Proof.
elim: n => [|n IHn]; first by rewrite mul1g.
by rewrite expgS [in LHS]IHn expgS mulgA.
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

Lemma iter_mulg n x y : iter n ( *%g x) y = x ^+ n * y.
Proof. by elim: n => [|n IHn]; rewrite ?mul1g //= IHn expgS mulgA. Qed.

Lemma iter_mulg_1 n x : iter n ( *%g x) 1 = x ^+ n.
Proof. by rewrite iter_mulg mulg1. Qed.

Lemma commuteX x y n : commute x y -> commute x (y ^+ n).
Proof.
by move=> cxy; case: n; [apply: commute1 | elim=> // n; apply: commuteM].
Qed.

Lemma commuteX2 x y m n : commute x y -> commute (x ^+ m) (y ^+ n).
Proof. by move=> cxy; apply/commuteX/commute_sym/commuteX. Qed.

Lemma expgMn x y n : commute x y -> (x * y) ^+ n = x ^+ n * y ^+ n.
Proof.
move=> cxy; elim: n => [|n IHn]; first by rewrite mulg1.
by rewrite !expgS IHn -mulgA (mulgA y) (commuteX _ (commute_sym cxy)) !mulgA.
Qed.

End MonoidTheory.

Notation monoid_closed := umagma_closed.

HB.mixin Record Monoid_isGroup G of Monoid G := {
  inv : G -> G;
  mulVg : left_inverse one inv mul;
  mulgV : right_inverse one inv mul
}.

#[short(type="groupType")]
HB.structure Definition Group := {G of Monoid_isGroup G & Monoid G}.

HB.factory Record isGroup G of Choice G := {
  one : G;
  inv : G -> G;
  mul : G -> G -> G;
  mulgA : associative mul;
  mul1g : left_id one mul;
  mulg1 : right_id one mul;
  mulVg : left_inverse one inv mul;
  mulgV : right_inverse one inv mul
}.

HB.builders Context G of isGroup G.

HB.instance Definition _ := isMagma.Build G mul.
HB.instance Definition _ := Magma_isSemigroup.Build G mulgA.
HB.instance Definition _ := Magma_isUMagma.Build G mul1g mulg1.
HB.instance Definition _ := Monoid_isGroup.Build G mulVg mulgV.

HB.end.

Local Notation "x ^-1" := (inv x) : group_scope.
Local Notation "x / y" := (x * y^-1) : group_scope.
Local Notation "x ^- n" := ((x ^+ n)^-1) : group_scope.

Definition conjg (G : groupType) (x y : G) := y^-1 * (x * y).
Local Notation "x ^ y" := (conjg x y) : group_scope.

Definition commg (G : groupType) (x y : G) := x^-1 * (conjg x y).
Local Notation "[~ x , y ]" := (commg x y) : group_scope.

Section GroupTheory.
Variable G : groupType.
Implicit Types x y : G.

Definition divgg := @mulgV G.

Lemma mulKg : @left_loop G G (@inv G) *%g.
Proof. by move=> x y; rewrite mulgA mulVg mul1g. Qed.

Lemma mulVKg : @rev_left_loop G G (@inv G) *%g.
Proof. by move=> x y ; rewrite mulgA mulgV mul1g. Qed.

Lemma mulgK : @right_loop G G (@inv G) *%g.
Proof. by move=> x y; rewrite -mulgA mulgV mulg1. Qed.

Lemma mulgVK : @rev_right_loop G G (@inv G) *%g.
Proof. by move=> x y ; rewrite -mulgA mulVg mulg1. Qed.
Definition divgK := mulgVK.

Lemma mulgI : @right_injective G G G *%g.
Proof. by move=> x; apply: can_inj (mulKg x). Qed.

Lemma mulIg : @left_injective G G G *%g.
Proof. by move=> x; apply: can_inj (mulgK x). Qed.

Lemma invgK : @involutive G (@inv G).
Proof. by move=> x; rewrite -[LHS]mulg1 -(mulVg x) mulgA mulVg mul1g. Qed.

Lemma invg_inj : @injective G G (@inv G).
Proof. exact: inv_inj invgK. Qed.

Lemma divgI : @right_injective G G G (fun x y => x / y).
Proof. by move=> x y z /mulgI/invg_inj. Qed.

Lemma divIg : @left_injective G G G (fun x y => x / y).
Proof. by move=> x y z /mulIg. Qed.

Lemma invg1 : 1 ^-1 = 1 :> G.
Proof. by rewrite -[LHS]mul1g divgg. Qed.

Lemma invg_eq1 x : (x ^-1 == 1) = (x == 1).
Proof. by rewrite (inv_eq invgK) invg1. Qed.

Lemma divg1 x : x / 1 = x. Proof. by rewrite invg1 mulg1. Qed.

Lemma div1g x : 1 / x = x^-1. Proof. by rewrite mul1g. Qed.

Lemma invgF x y : (x / y)^-1 = y / x.
Proof. by apply/(canRL (mulgK x))/(@divIg y); rewrite -mulgA mulVg divgg. Qed.

Lemma invgM : {morph (@inv G): x y / x * y >-> y * x : G}.
Proof. by move=> x y; rewrite -[y in LHS] invgK invgF. Qed.

Lemma divKg x y : commute x y -> x / (x / y) = y.
Proof. by move=> xyC; rewrite invgM invgK mulgA xyC -mulgA divgg mulg1. Qed.

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
elim: n => [|n IHn]; first by rewrite !expg0n invg1.
by rewrite expgS IHn -invgM -expgSr.
Qed.

Lemma expgnBr x m n : n <= m -> x ^+ (m - n) = x ^+ m / x ^+ n.
Proof.
elim: m n => [|m IHm] [|n]; rewrite ?divg1 => // /IHm ->.
by rewrite 2!expgSr mulgKA.
Qed.

Lemma commuteV x y : commute x y -> commute x y^-1.
Proof. by move=> cxy; apply: (@mulIg y); rewrite mulgVK -mulgA cxy mulKg. Qed.

Lemma expgnBl x y n : commute x y -> (x / y) ^+ n = x ^+ n / y ^+ n.
Proof.
move=> xyC.
elim: n => [|n IHn]; first by rewrite divg1.
rewrite !expgS IHn -!mulgA; congr (x * _).
rewrite invgM [RHS]mulgA.
apply/commuteM.
  exact/commuteX/commute_sym/commuteV.
by rewrite -expVgn; apply/commuteX.
Qed.

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

Lemma conjgK : @right_loop G G (@inv G) (@conjg G).
Proof. by move=> y x; rewrite -conjgM mulgV conjg1. Qed.

Lemma conjgKV : @rev_right_loop G G (@inv G) (@conjg G).
Proof. by move=> y x; rewrite -conjgM mulVg conjg1. Qed.

Lemma conjg_inj : @left_injective G G G (@conjg G).
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

Lemma conjg_fix x y : x ^ y == x = ([~ x, y] == 1).
Proof. by rewrite mulg_eq1 eqg_inv. Qed.

Lemma conjg_fixP x y : reflect (x ^ y = x) ([~ x, y] == 1).
Proof. by rewrite -conjg_fix; apply: eqP. Qed.

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

Variable S : {pred G}.

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

(* Morphism hierarchy. *)

HB.mixin Record isMultiplicative (G H : magmaType) (apply : G -> H) := {
  gmulfM : {morph apply : x y / x * y}
}.

HB.structure Definition Multiplicative (G H : magmaType) :=
  {f of isMultiplicative G H f}.

(* TODO: define pointedTypes and generalize this to pointedTypes. *)
HB.mixin Record isUMagmaMorphism (G H : baseUMagmaType) (f : G -> H) := {
  gmulf1 : f 1 = 1
}.

HB.structure Definition UMagmaMorphism (G H : baseUMagmaType) :=
  {f of isUMagmaMorphism G H f & isMultiplicative G H f}.

HB.factory Record isGroupMorphism (G H : groupType) (f : G -> H) := {
  gmulfB : {morph f : x y / x / y}
}.

HB.builders Context G H apply of isGroupMorphism G H apply.

Local Lemma gmulf1 : apply 1 = 1.
Proof. by rewrite -[1]divg1 gmulfB divgg. Qed.

Local Lemma gmulfM : {morph apply : x y / x * y}.
Proof.
move=> x y; rewrite -[y in LHS] invgK -[y^-1]mul1g.
by rewrite !gmulfB gmulf1 div1g invgK.
Qed.

HB.instance Definition _ := isMultiplicative.Build G H apply gmulfM.
HB.instance Definition _ := isUMagmaMorphism.Build G H apply gmulf1.

HB.end.

Module MultiplicativeExports.
Notation "{ 'multiplicative' U -> V }" :=
  (Multiplicative.type U%type V%type) : type_scope.
End MultiplicativeExports.
HB.export MultiplicativeExports.


(* Lifted operations *)
(* TODO: declare `forall x : T, G x` as a magma for `T : Type`
   and `G : magmaType` when HB allows it.
   Idem for umagmas and (base) groups (to be defined). *)
Section LiftedMagma.
Variables (T : Type) (G : magmaType).
Definition mul_fun (f g : T -> G) x := f x * g x.
End LiftedMagma.
Section LiftedBaseUMagma.
Variables (T : Type) (G : baseUMagmaType).
Definition one_fun of T : G := 1.
End LiftedBaseUMagma.

Local Notation "\1" := (one_fun _) : group_scope.
Local Notation "f \* g" := (mul_fun f g) : group_scope.

Arguments one_fun {_} G _ /.
Arguments mul_fun {_ _} f g _ /.

Section MorphismTheory.

Section Magma.
Variables (G H : magmaType) (f : {multiplicative G -> H}).

Lemma can2_gmulfM f' : cancel f f' -> cancel f' f -> {morph f' : x y / x * y}.
Proof. by move=> fK f'K x y; apply: (canLR fK); rewrite gmulfM !f'K. Qed.

Lemma gmulf_commute x y : commute x y -> commute (f x) (f y).
Proof. by move=> xy; rewrite /commute -!gmulfM xy. Qed.

End Magma.

Section UMagma.
Variables (G H : baseUMagmaType) (f : UMagmaMorphism.type G H).

Lemma gmulf_eq1 x : injective f -> (f x == 1) = (x == 1).
Proof. by move=> /inj_eq <-; rewrite gmulf1. Qed.

Lemma can2_gmulf1 f' : cancel f f' -> cancel f' f -> f' 1 = 1.
Proof. by move=> fK f'K; apply: (canLR fK); rewrite gmulf1. Qed.

Lemma gmulfXn n : {morph f : x / x ^+ n}.
Proof.
elim: n => [|n IHn] x /=; first exact: gmulf1.
case: n IHn => [//|n] IHn.
by rewrite gmulfM [X in _ * X]IHn.
Qed.

End UMagma.

Section Group.
Variables (G H : groupType) (f : UMagmaMorphism.type G H).

Lemma gmulfV : {morph f : x / x^-1}.
Proof.
Proof. by move=> x; apply/divg1_eq; rewrite invgK -gmulfM mulVg/= gmulf1. Qed.

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

Section MulFun.
Variables (G H K : magmaType).
Variables (f g : {multiplicative H -> K}) (h : {multiplicative G -> H}).

Fact idfun_gmulfM : {morph @idfun G : x y / x * y}.
Proof. by []. Qed.
#[export]
HB.instance Definition _ := isMultiplicative.Build G G idfun idfun_gmulfM.

Fact comp_gmulfM : {morph f \o h : x y / x * y}.
Proof. by move=> x y /=; rewrite !gmulfM. Qed.
#[export]
HB.instance Definition _ := isMultiplicative.Build G K (f \o h) comp_gmulfM.
End MulFun.

Section Mul1Fun.
Variables (G : magmaType) (H : umagmaType).

Fact idfun_gmulf1 : idfun 1 = 1 :> H.
Proof. by []. Qed.
HB.instance Definition _ := isUMagmaMorphism.Build H H idfun idfun_gmulf1.

Fact one_fun_gmulfM : {morph @one_fun G H : x y / x * y}.
Proof. by move=> x y; rewrite mulg1. Qed.
HB.instance Definition _ :=
  isMultiplicative.Build G H (@one_fun G H) one_fun_gmulfM.
End Mul1Fun.

Section Mul11Fun.
Variables (G H K : umagmaType).
Variables (f g : UMagmaMorphism.type H K) (h : UMagmaMorphism.type G H).

Fact comp_gmulf1 : (f \o h) 1 = 1.
Proof. by rewrite /= !gmulf1. Qed.
HB.instance Definition _ := isUMagmaMorphism.Build G K (f \o h) comp_gmulf1.

Fact one_fun_gmulf1 : @one_fun G H 1 = 1.
Proof. by []. Qed.
HB.instance Definition _ :=
  isUMagmaMorphism.Build G H (@one_fun G H) one_fun_gmulf1.

Fact mul_fun_gmulf1 : (f \* g) 1 = 1.
Proof. by rewrite /mul_fun /= !gmulf1 mulg1. Qed.
HB.instance Definition _ := isUMagmaMorphism.Build H K (f \* g) mul_fun_gmulf1.
End Mul11Fun.
End MorphismTheory.

(* Mixins for stability properties *)

HB.mixin Record isMulClosed (G : magmaType) (S : {pred G}) := {
  gpredM : mulg_closed S
}.

HB.mixin Record isMul1Closed (G : baseUMagmaType) (S : {pred G}) := {
  gpred1 : 1 \in S
}.

HB.mixin Record isInvClosed (G : groupType) (S : {pred G}) := {
  gpredVr : invg_closed S
}.

(* Structures for stability properties *)

#[short(type="mulgClosed")]
HB.structure Definition MulClosed G := {S of isMulClosed G S}.

#[short(type="umagmaClosed")]
HB.structure Definition UMagmaClosed G :=
  {S of isMul1Closed G S & isMulClosed G S}.

#[short(type="invgClosed")]
HB.structure Definition InvClosed G := {S of isInvClosed G S}.

#[short(type="groupClosed")]
HB.structure Definition GroupClosed G :=
  {S of isInvClosed G S & isMul1Closed G S & isMulClosed G S}.

Section UMagmaPred.
Variables (G : baseUMagmaType).

Section UMagma.
Variables S : umagmaClosed G.

Lemma gpredXn n : {in S, forall u, u ^+ n \in S}.
Proof.
move=> x xS; elim: n => [|n IHn]; first exact: gpred1.
by case: n IHn => [//|n] IHn; apply/gpredM.
Qed.

End UMagma.
End UMagmaPred.

Section GroupPred.
Variables (G : groupType).

Section Group.
Variables S : groupClosed G.

Lemma gpredV : {mono (@inv G): u / u \in S}.
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

HB.mixin Record isSubMagma (G : magmaType) (S : pred G) H
    of SubType G S H & Magma H := {
  valM_subproof : {morph (val : H -> G) : x y / x * y}
}.

#[short(type="subMagmaType")]
HB.structure Definition SubMagma (G : magmaType) S :=
  { H of SubChoice G S H & Magma H & isSubMagma G S H }.

Section subMagma.
Context (G : magmaType) (S : pred G) (H : subMagmaType S).
Notation val := (val : H -> G).
#[export]
HB.instance Definition _ := isMultiplicative.Build H G val valM_subproof.
Lemma valM : {morph val : x y / x * y}. Proof. exact: gmulfM. Qed.
End subMagma.

HB.factory Record SubChoice_isSubMagma (G : magmaType) S H
    of SubChoice G S H := {
  mulg_closed_subproof : mulg_closed S
}.

HB.builders Context G S H of SubChoice_isSubMagma G S H.

HB.instance Definition _ := isMulClosed.Build G S mulg_closed_subproof.

Let inH v Sv : H := Sub v Sv.
Let mulH (u1 u2 : H) := inH (gpredM _ _ (valP u1) (valP u2)).

HB.instance Definition _ := isMagma.Build H mulH.

Lemma valM : {morph (val : H -> G) : x y / x * y}.
Proof. by move=> x y; rewrite SubK. Qed.

HB.instance Definition _ := isSubMagma.Build G S H valM.

HB.end.

#[short(type="subUMagmaType")]
HB.structure Definition SubSemigroup (G : semigroupType) S :=
  { H of SubMagma G S H & Semigroup H}.

HB.factory Record SubChoice_isSubSemigroup (G : semigroupType) S H
    of SubChoice G S H := {
  mulg_closed_subproof : mulg_closed S
}.

HB.builders Context G S H of SubChoice_isSubSemigroup G S H.

HB.instance Definition _ :=
  SubChoice_isSubMagma.Build G S H mulg_closed_subproof.

Lemma mulgA : associative (@mul H).
Proof. by move=> x y z; apply/val_inj; rewrite !valM mulgA. Qed.

HB.instance Definition _ := isSemigroup.Build H mulgA.

HB.end.

HB.mixin Record isSubBaseUMagma (G : baseUMagmaType) (S : pred G) H
    of SubMagma G S H & BaseUMagma H := {
  val1_subproof : (val : H -> G) 1 = 1
}.

#[short(type="subBaseUMagmaType")]
HB.structure Definition SubBaseUMagma (G : umagmaType) S :=
  { H of SubMagma G S H & BaseUMagma H & isSubBaseUMagma G S H}.

#[short(type="subUMagmaType")]
HB.structure Definition SubUMagma (G : umagmaType) S :=
  { H of SubMagma G S H & UMagma H & isSubBaseUMagma G S H}.

Section subUMagma.
Context (G : umagmaType) (S : pred G) (H : subUMagmaType S).
Notation val := (val : H -> G).
#[export]
HB.instance Definition _ := isUMagmaMorphism.Build H G val val1_subproof.
Lemma val1 : val 1 = 1. Proof. exact: gmulf1. Qed.
End subUMagma.

HB.factory Record SubChoice_isSubUMagma (G : umagmaType) S H
    of SubChoice G S H := {
  umagma_closed_subproof : umagma_closed S
}.

HB.builders Context G S H of SubChoice_isSubUMagma G S H.

HB.instance Definition _ :=
  SubChoice_isSubMagma.Build G S H (snd umagma_closed_subproof).

Let inH v Sv : H := Sub v Sv.
Let oneH := inH (fst umagma_closed_subproof).

HB.instance Definition _ := Magma_isBaseUMagma.Build H oneH.

Lemma val1 : (val : H -> G) 1 = 1. 
Proof. exact/SubK. Qed.

HB.instance Definition _ := isSubBaseUMagma.Build G S H val1.

Lemma mul1g : left_id 1 (@mul H).
Proof. by move=> x; apply/val_inj; rewrite valM val1 mul1g. Qed.
Lemma mulg1 : right_id 1 (@mul H).
Proof. by move=> x; apply/val_inj; rewrite valM val1 mulg1. Qed.

HB.instance Definition _ := BaseUMagma_isUMagma.Build H mul1g mulg1.

HB.end.

#[short(type="subMonoidType")]
HB.structure Definition SubMonoid (G : monoidType) S :=
  { H of SubUMagma G S H & Monoid H}.

HB.factory Record SubChoice_isSubMonoid (G : monoidType) S H
    of SubChoice G S H := {
  monoid_closed_subproof : monoid_closed S
}.

HB.builders Context G S H of SubChoice_isSubMonoid G S H.

HB.instance Definition _ :=
  SubChoice_isSubUMagma.Build G S H monoid_closed_subproof.
HB.instance Definition _ :=
  SubChoice_isSubSemigroup.Build G S H (snd monoid_closed_subproof).

HB.end.

#[short(type="subGroupType")]
HB.structure Definition SubGroup (G : groupType) S :=
  { H of SubUMagma G S H & Group H}.

HB.factory Record SubChoice_isSubGroup (G : groupType) S H
    of SubChoice G S H := {
  group_closed_subproof : group_closed S
}.

HB.builders Context G S H of SubChoice_isSubGroup G S H.

Lemma umagma_closed : umagma_closed S.
Proof.
by split;
  [apply/(fst group_closed_subproof)|apply/group_closedM/group_closed_subproof].
Qed.
HB.instance Definition _ := SubChoice_isSubMonoid.Build G S H umagma_closed.
HB.instance Definition _ :=
  isInvClosed.Build G S (group_closedV group_closed_subproof).

Let inH v Sv : H := Sub v Sv.
Let invH (u : H) := inH (gpredVr _ (valP u)).

Lemma mulVg : left_inverse 1%g invH *%g.
Proof. by move=> x; apply/val_inj; rewrite valM SubK mulVg val1. Qed.
Lemma mulgV : right_inverse 1%g invH *%g.
Proof. by move=> x; apply/val_inj; rewrite valM SubK mulgV val1. Qed. 

HB.instance Definition _ := Monoid_isGroup.Build H mulVg mulgV.

HB.end.

(* Lifting Structure from the codomain of finfuns. *)
Section FinFunMagma.
Variable (aT : finType) (rT : magmaType).
Implicit Types f g : {ffun aT -> rT}.

Definition ffun_mul f g := [ffun a => f a * g a].

HB.instance Definition _ := isMagma.Build {ffun aT -> rT} ffun_mul.

End FinFunMagma.

Section FinFunSemigroup.
Variable (aT : finType) (rT : semigroupType).
Implicit Types f g : {ffun aT -> rT}.

Fact ffun_mulgA : associative (@ffun_mul aT rT).
Proof. by move=> f1 f2 f3; apply/ffunP=> a; rewrite !ffunE mulgA. Qed.

HB.instance Definition _ := isSemigroup.Build {ffun aT -> rT} ffun_mulgA.

End FinFunSemigroup.

Section FinFunBaseUMagma.
Variable (aT : finType) (rT : baseUMagmaType).
Implicit Types f g : {ffun aT -> rT}.

Definition ffun_one := [ffun a : aT => (1 : rT)].

HB.instance Definition _ :=
  Magma_isBaseUMagma.Build {ffun aT -> rT} ffun_one.

End FinFunBaseUMagma.

Section FinFunUMagma.
Variable (aT : finType) (rT : umagmaType).
Implicit Types f g : {ffun aT -> rT}.

Fact ffun_mul1g : left_id (@ffun_one aT rT) *%g.
Proof. by move=> f; apply/ffunP => a; rewrite !ffunE mul1g. Qed.
Fact ffun_mulg1 : right_id (@ffun_one aT rT) *%g.
Proof. by move=> f; apply/ffunP => a; rewrite !ffunE mulg1. Qed.

HB.instance Definition _ :=
  Magma_isUMagma.Build {ffun aT -> rT} ffun_mul1g ffun_mulg1.

End FinFunUMagma.

HB.instance Definition _ (aT : finType) (rT : monoidType) :=
  UMagma_isMonoid.Build {ffun aT -> rT} (@ffun_mulgA aT rT).

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

(* External direct product *)
Section PairMagma.
Variables G H : magmaType.

Definition mul_pair (x y : G * H) := (x.1 * y.1, x.2 * y.2).

#[export]
HB.instance Definition _ := isMagma.Build (G * H)%type mul_pair.

Fact fst_is_multiplicative : {morph fst : x y / x * y}. Proof. by []. Qed.
#[export]
HB.instance Definition _ := isMultiplicative.Build _ _ _ fst_is_multiplicative.

Fact snd_is_multiplicative : {morph snd : x y / x * y}. Proof. by []. Qed.
#[export]
HB.instance Definition _ := isMultiplicative.Build _ _ _ snd_is_multiplicative.

End PairMagma.

Section PairSemigroup.
Variables G H : semigroupType.

Lemma pair_mulgA : associative (@mul (G * H)%type).
Proof. by move=> x y z; congr (_, _); apply/mulgA. Qed.

HB.instance Definition _ := Magma_isSemigroup.Build (G * H)%type pair_mulgA.

End PairSemigroup.

Section PairBaseUMagma.
Variables G H : baseUMagmaType.

Definition one_pair : G * H := (1, 1).

#[export]
HB.instance Definition _ := Magma_isBaseUMagma.Build (G * H)%type one_pair.

Fact fst_is_umagma_morphism : fst (1 : (G * H)%type) = 1. Proof. by []. Qed.
#[export]
HB.instance Definition _ := isUMagmaMorphism.Build _ _ _ fst_is_umagma_morphism.

Fact snd_is_umagma_morphism : snd (1 : (G * H)%type) = 1. Proof. by []. Qed.
#[export]
HB.instance Definition _ := isUMagmaMorphism.Build _ _ _ snd_is_umagma_morphism.

End PairBaseUMagma.

Section PairUMagma.
Variables G H : umagmaType.

Lemma pair_mul1g : left_id (@one_pair G H) *%g.
Proof. by move=> [x y]; congr (_, _); rewrite mul1g. Qed.
Lemma pair_mulg1 : right_id (@one_pair G H) *%g.
Proof. by move=> [x y]; congr (_, _); rewrite mulg1. Qed.

#[export]
HB.instance Definition _ :=
  BaseUMagma_isUMagma.Build (G * H)%type pair_mul1g pair_mulg1.

End PairUMagma.

HB.instance Definition _ (U V : monoidType) := Semigroup.on (U * V)%type.

Section PairGroup.
Variables G H : groupType.

Definition inv_pair (u : G * H) := (u.1 ^-1, u.2 ^-1).

Lemma pair_mulVg : left_inverse one inv_pair mul.
Proof. by move=> x; congr (_, _); apply/mulVg. Qed.
Lemma pair_mulgV : right_inverse one inv_pair mul.
Proof. by move=> x; congr (_, _); apply/mulgV. Qed.

HB.instance Definition _ :=
  Monoid_isGroup.Build (G * H)%type pair_mulVg pair_mulgV.

End PairGroup.

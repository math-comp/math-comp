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
(*             magmaType == magma                                             *)
(*                          The HB class is called Magma.                     *)
(*      ChoiceMagma.type == join of magmaType and choiceType                  *)
(*                          The HB class is called ChoiceMagma.               *)
(*         semigroupType == associative magma                                 *)
(*                          The HB class is called Semigroup.                 *)
(*        baseUMagmaType == pointed magma                                     *)
(*                          The HB class is called BaseUMagma.                *)
(* ChoiceBaseUMagma.type == join of baseUMagmaType and choiceType             *)
(*                          The HB class is called ChoiceBaseUMagma.          *)
(*            umagmaType == unitary magma                                     *)
(*                          The HB class is called UMagma.                    *)
(*            monoidType == monoid                                            *)
(*                          The HB class is called Monoid.                    *)
(*         baseGroupType == pointed magma with an inversion operator          *)
(*                          The HB class is called BaseGroup.                 *)
(*             groupType == group                                             *)
(*                          The HB class is called Group.                     *)
(*                                                                            *)
(* and their joins with subType:                                              *)
(*                                                                            *)
(*        subMagmaType V P == join of magmaType and subType (P : pred V) such *)
(*                            that val is multiplicative                      *)
(*                            The HB class is called SubMagma.                *)
(*    subSemigroupType V P == join of semigroupType and subType (P : pred V)  *)
(*                            such that val is multiplicative                 *)
(*                            The HB class is called SubSemigroup.            *)
(*   subBaseUMagmaType V P == join of baseUMagmaType and subType (P : pred V) *)
(*                            such that val is multiplicative and preserves 1 *)
(*                            The HB class is called SubBaseUMagma.           *)
(*      subUMagmaType V P == join of UMagmaType and subType (P : pred V)      *)
(*                            such that val is multiplicative and preserves 1 *)
(*                            The HB class is called SubUMagma.               *)
(*      subMonoidType V P == join of monoidType and subType (P : pred V)      *)
(*                            such that val is multiplicative and preserves 1 *)
(*                            The HB class is called SubMonoid.               *)
(*       subGroupType V P == join of groupType and subType (P : pred V)       *)
(*                            such that val is multiplicative and preserves 1 *)
(*                            The HB class is called SubGroup.                *)
(*                                                                            *)
(* Morphisms between the above structures:                                    *)
(*                                                                            *)
(*  Multiplicative.type G H == multiplicative functions between magmaType     *)
(*                             instances G and H                              *)
(*  UMagmaMorphism.type G H == multiplicative functions preserving 1 between  *)
(*                             baseUMagmaType instances G and H               *)
(*                                                                            *)
(* Closedness predicates for the algebraic structures:                        *)
(*                                                                            *)
(*    mulgClosed V == predicate closed under multiplication on G : magmaType  *)
(*                    The HB class is called MulClosed.                       *)
(*  umagmaClosed V == predicate closed under multiplication and containing 1  *)
(*                    on G : baseUMagmaType                                   *)
(*                    The HB class is called UMagmaClosed.                    *)
(*    invgClosed V == predicate closed under inversion on G : baseGroupType   *)
(*                    The HB class is called InvClosed.                       *)
(*   groupClosed V == predicate closed under multiplication and inversion and *)
(*                    containing 1 on G : baseGroupType                       *)
(*                    The HB class is called InvClosed.                       *)
(*                                                                            *)
(* Canonical properties of the algebraic structures:                          *)
(*  * magmaType (magmas):                                                     *)
(*                 x * y == the product of x and y                            *)
(*           commute x y <-> x and y commute (i.e. x * y = y * x)             *)
(*         mulg_closed S <-> collective predicate S is closed under           *)
(*                          multiplication                                    *)
(*                                                                            *)
(*  * baseUMagmaType (pointed magmas):                                        *)
(*                     1 == the unit of a unitary magma                       *)
(*                x ^+ n == x to the power n, with n in nat (non-negative),   *)
(*                          i.e. x * (x * .. (x * x)..) (n terms); x ^+ 1 is  *)
(*                          thus convertible to x, and x ^+ 2 to x * x        *)
(*       umagma_closed S <-> collective predicate S is closed under           *)
(*                          multiplication and contains 1                     *)
(*                                                                            *)
(*  * monoidType (monoids):                                                   *)
(*       monoid_closed S := umagma_closed S                                   *)
(*                                                                            *)
(*  * baseGroupType (pointed magmas with an inversion operator):              *)
(*                 x ^-1 == the inverse of x                                  *)
(*                 x / y == x * (y ^- 1)                                      *)
(*                x ^- n == (x ^+ n)^-1                                       *)
(*                 x ^ y := y^-1 * (x * y)                                    *)
(*                       == the conjugate of x by y                           *)
(*              [~ x, y] := x^-1 * (y^-1 * (x * y)                            *)
(*                       == the commutator of x and y                         *)
(*         invg_closed S <-> collective predicate S is closed under inversion *)
(*         divg_closed S <-> collective predicate S is closed under division  *)
(*        group_closed S <-> collective predicate S is closed under division  *)
(*                           and contains 1                                   *)
(*                                                                            *)
(*                                                                            *)
(*   Notations are defined in scope group_scope (delimiter %g)                *)
(*   This library also extends the conventional suffixes described in library *)
(* ssrbool.v with the following:                                              *)
(*   1 -- unitary magma 1, as in mulg1 : x * 1 = x                            *)
(*   M -- magma multiplication, as in conjgM : x ^ (y * z) = (x ^ y) ^ z      *)
(*  Mn -- ring by nat multiplication, as in expgMn :                          *)
(*        (x * y) ^+ n = x ^+ n * y ^+ n                                      *)
(*   V -- group inverse, as in expVgn : (x^-1) ^+ n = x ^- n                  *)
(*   F -- group division, as in expgnFr : x ^+ (m - n) = x ^+ m / x ^+ n      *)
(*   X -- unitary magma exponentiation, as in conjXg :                        *)
(*        (x ^+ n) ^ y = (x ^ y) ^+ n                                         *)
(*   J -- group conjugation, as in conjJg : (x ^ y) ^ z = (x ^ z) ^ y ^ z     *)
(*   R -- group commutator, as in conjRg : [~ x, y] ^ z = [~ x ^ z, y ^ z]    *)
(* The operator suffixes D, B, M and X are also used for the corresponding    *)
(* operations on nat, as in expgnDr : x ^+ (m + n) = x ^+ m * x ^+ n. For the *)
(* binary power operator, a trailing "n" suffix is used to indicate the       *)
(* operator suffix applies to the left-hand group argument, as in             *)
(*   expg1n : 1 ^+ n = 1 vs. expg1 : x ^+ 1 = x.                              *)
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

HB.mixin Record hasMul G := {
  mul : G -> G -> G
}.

#[short(type="magmaType")]
HB.structure Definition Magma := {G of hasMul G}.

Bind Scope group_scope with Magma.sort.

HB.structure Definition ChoiceMagma := {G of Magma G & Choice G}.

Bind Scope group_scope with ChoiceMagma.sort.

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
HB.structure Definition Semigroup := {G of Magma_isSemigroup G & Magma G & Choice G}.

HB.factory Record isSemigroup G of Choice G := {
  mul : G -> G -> G;
  mulgA : associative mul
}.

HB.builders Context G of isSemigroup G.

HB.instance Definition _ := hasMul.Build G mul.
HB.instance Definition _ := Magma_isSemigroup.Build G mulgA.

HB.end.

Bind Scope group_scope with Semigroup.sort.

Section SemigroupTheory.
Variable G : semigroupType.
Implicit Types x y : G.

Lemma commuteM x y z : commute x y -> commute x z -> commute x (y * z).
Proof. by move=> cxy cxz; rewrite /commute -mulgA -cxz !mulgA cxy. Qed.

End SemigroupTheory.

HB.mixin Record hasOne G := {
  one : G
}.

#[short(type="baseUMagmaType")]
HB.structure Definition BaseUMagma := {G of hasOne G & Magma G}.

Bind Scope group_scope with BaseUMagma.sort.

HB.structure Definition ChoiceBaseUMagma := {G of BaseUMagma G & Choice G}.

Bind Scope group_scope with ChoiceBaseUMagma.sort.

Local Notation "1" := (@one _) : group_scope.
Local Notation "s `_ i" := (nth 1 s i) : group_scope.

Definition natexp (G : baseUMagmaType) (x : G) n : G := iterop n *%g x 1.
Arguments natexp : simpl never.

Local Notation "x ^+ n" := (natexp x n) : group_scope.

Section baseUMagmaTheory.

Variable G : baseUMagmaType.
Implicit Types x : G.
Lemma expg0 x : x ^+ 0 = 1. Proof. by []. Qed.
Lemma expg1 x : x ^+ 1 = x. Proof. by []. Qed.
Lemma expg2 x : x ^+ 2 = x * x. Proof. by []. Qed.

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
HB.instance Definition _ := hasOne.Build G one.
#[warning="-HB.no-new-instance"]
HB.instance Definition _ := BaseUMagma_isUMagma.Build G mul1g mulg1.
HB.end.

#[short(type="umagmaType")]
HB.structure Definition UMagma := {G of Magma_isUMagma G & Magma G & Choice G}.

Bind Scope group_scope with UMagma.sort.

Section UMagmaTheory.

Variable G : umagmaType.
Implicit Types x y : G.

Lemma expgS x n : x ^+ n.+1 = x * x ^+ n.
Proof. by case: n => //=; rewrite mulg1. Qed.

Lemma expg1n n : 1 ^+ n = 1 :> G.
Proof. by elim: n => // n IHn; rewrite expgS mul1g. Qed.

Lemma commute1 x : commute x 1.
Proof. by rewrite /commute mulg1 mul1g. Qed.

End UMagmaTheory.

#[short(type="monoidType")]
HB.structure Definition Monoid := {G of Magma_isUMagma G & Semigroup G}.

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

HB.instance Definition _ := hasMul.Build G mul.
HB.instance Definition _ := Magma_isSemigroup.Build G mulgA.
HB.instance Definition _ := Magma_isUMagma.Build G mul1g mulg1.

HB.end.

Bind Scope group_scope with Monoid.sort.

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
Proof. by rewrite mulnC; elim: n => //= n IHn; rewrite expgS expgnDr IHn. Qed.

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

HB.mixin Record hasInv G := {
  inv : G -> G
}.

#[short(type="baseGroupType")]
HB.structure Definition BaseGroup := {G of hasInv G & BaseUMagma G}.

Bind Scope group_scope with BaseGroup.sort.

HB.mixin Record Monoid_isGroup G of BaseGroup G := {
  mulVg : left_inverse one inv (@mul G);
  mulgV : right_inverse one inv (@mul G)
}.

#[short(type="groupType")]
HB.structure Definition Group := {G of Monoid_isGroup G & BaseGroup G & Monoid G}.

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

HB.instance Definition _ := hasMul.Build G mul.
HB.instance Definition _ := Magma_isSemigroup.Build G mulgA.
HB.instance Definition _ := Magma_isUMagma.Build G mul1g mulg1.
HB.instance Definition _ := hasInv.Build G inv.
HB.instance Definition _ := Monoid_isGroup.Build G mulVg mulgV.

HB.end.

Bind Scope group_scope with Group.sort.

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
Proof. by move=> x; rewrite -[LHS](mulVKg x) divgg mulg1. Qed.

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
Proof. by move=> x y; rewrite -[y in LHS]invgK invgF. Qed.

Lemma divKg x y : commute x y -> x / (x / y) = y.
Proof. by move=> xyC; rewrite invgF mulgA xyC mulgK. Qed.

(* TOTHINK : This does not have the same form as addrKA in ssralg.v *)
Lemma mulgKA z x y : (x * z) / (y * z) = x / y.
Proof. by rewrite invgM mulgA mulgK. Qed.

Lemma divgKA z x y : (x / z) * (z * y) = x * y.
Proof. by rewrite mulgA mulgVK. Qed.

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

Lemma commuteV x y : commute x y -> commute x y^-1.
Proof. by move=> cxy; apply: (@mulIg y); rewrite mulgVK -mulgA cxy mulKg. Qed.

Lemma expVgn x n : (x^-1) ^+ n = x ^- n.
Proof.
apply/esym/mulg1_eq; rewrite -expgMn; first by rewrite divgg expg1n.
exact/commuteV.
Qed.

Lemma expgnFr x m n : n <= m -> x ^+ (m - n) = x ^+ m / x ^+ n.
Proof. by move=> lenm; rewrite -[in RHS](subnK lenm) expgnDr mulgK. Qed.

Lemma expgnFl x y n : commute x y -> (x / y) ^+ n = x ^+ n / y ^+ n.
Proof. by move=> xyC; rewrite expgMn 1?expVgn; last exact/commuteV. Qed.

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

Lemma invgR x y : [~ x, y]^-1 = [~ y, x].
Proof. by rewrite commgEr conjVg invgM invgK. Qed.

Lemma commgP x y : reflect (commute x y) ([~ x, y] == 1).
Proof. rewrite [[~ x, y]]mulgA -invgM mulg_eq1 eqg_inv eq_sym; apply: eqP. Qed.

Lemma conjg_fix x y : x ^ y == x = ([~ x, y] == 1).
Proof. by rewrite mulg_eq1 eqg_inv. Qed.

Lemma conjg_fixP x y : reflect (x ^ y = x) ([~ x, y] == 1).
Proof. by rewrite -conjg_fix; apply: eqP. Qed.

Lemma commg1_sym x y : ([~ x, y] == 1) = ([~ y, x] == 1).
Proof. by rewrite -invgR (inv_eq invgK) invg1. Qed.

Lemma commg1 x : [~ x, 1] = 1.
Proof. exact/eqP/commgP/commute1. Qed.

Lemma comm1g x : [~ 1, x] = 1.
Proof. by rewrite -invgR commg1 invg1. Qed.

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
Definition divg_closed := {in S &, forall u v, u / v \in S}.
Definition group_closed := 1 \in S /\ divg_closed.

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
  gmulfF : {morph f : x y / x / y}
}.

HB.builders Context G H apply of isGroupMorphism G H apply.

Local Lemma gmulf1 : apply 1 = 1.
Proof. by rewrite -[1]divg1 gmulfF divgg. Qed.

Local Lemma gmulfM : {morph apply : x y / x * y}.
Proof.
move=> x y; rewrite -[y in LHS] invgK -[y^-1]mul1g.
by rewrite !gmulfF gmulf1 div1g invgK.
Qed.

HB.instance Definition _ := isMultiplicative.Build G H apply gmulfM.
HB.instance Definition _ := isUMagmaMorphism.Build G H apply gmulf1.

HB.end.

Module MultiplicativeExports.
Notation "{ 'multiplicative' U -> V }" :=
  (Multiplicative.type U%type V%type) : type_scope.
End MultiplicativeExports.
HB.export MultiplicativeExports.

(* FIXME: HB should do this automatically. *)
#[non_forgetful_inheritance]
HB.instance Definition _ G H (f : UMagmaMorphism.type G H) :=
  UMagmaMorphism.on (Multiplicative.sort f).

Section LiftedMagma.
Variables (T : Type) (G : magmaType).
Definition mul_fun (f g : T -> G) x := f x * g x.

End LiftedMagma.
Section LiftedBaseUMagma.
Variables (T : Type) (G : baseUMagmaType).
Definition one_fun : T -> G := fun=> 1.

End LiftedBaseUMagma.

Local Notation "\1" := (one_fun _) : function_scope.
Local Notation "f \* g" := (mul_fun f g) : function_scope.
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
Variables (G H : umagmaType) (f : UMagmaMorphism.type G H).

Lemma gmulf_eq1 x : injective f -> (f x == 1) = (x == 1).
Proof. by move=> /inj_eq <-; rewrite gmulf1. Qed.

Lemma can2_gmulf1 f' : cancel f f' -> cancel f' f -> f' 1 = 1.
Proof. by move=> fK f'K; apply: (canLR fK); rewrite gmulf1. Qed.

Lemma gmulfXn n : {morph f : x / x ^+ n}.
Proof. by elim: n => [|[|n] IHn] x /=; rewrite ?(gmulf1, gmulfM) // IHn. Qed.

End UMagma.

Section Group.
Variables (G H : groupType) (f : UMagmaMorphism.type G H).

Lemma gmulfV : {morph f : x / x^-1}.
Proof. by move=> x; apply/divg1_eq; rewrite invgK -gmulfM mulVg gmulf1. Qed.

Lemma gmulfF : {morph f : x y / x / y}.
Proof. by move=> x y; rewrite gmulfM gmulfV. Qed.

Lemma gmulf_inj : (forall x, f x = 1 -> x = 1) -> injective f.
Proof. by move=> fI x y xy; apply/divg1_eq/fI; rewrite gmulfF xy divgg. Qed.

Lemma gmulfXVn n : {morph f : x / x ^- n}.
Proof. by move=> x /=; rewrite gmulfV gmulfXn. Qed.

Lemma gmulfJ : {morph f : x y / x ^ y}.
Proof. by move=> x y; rewrite !gmulfM/= gmulfV. Qed.

Lemma gmulfR : {morph f : x y / [~ x, y]}.
Proof. by move=> x y; rewrite !gmulfM/= !gmulfV. Qed.
End Group.

Section MulFun.
Variables (G H K : magmaType).
Variables (f g : {multiplicative H -> K}) (h : {multiplicative G -> H}).

Fact idfun_gmulfM : {morph @idfun G : x y / x * y}.
Proof. by []. Qed.
HB.instance Definition _ := isMultiplicative.Build G G idfun idfun_gmulfM.

Fact comp_gmulfM : {morph f \o h : x y / x * y}.
Proof. by move=> x y /=; rewrite !gmulfM. Qed.
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
#[warning="-HB.no-new-instance"]
HB.instance Definition _ := isUMagmaMorphism.Build G K (f \o h) comp_gmulf1.

Fact one_fun_gmulf1 : @one_fun G H 1 = 1.
Proof. by []. Qed.
HB.instance Definition _ :=
  isUMagmaMorphism.Build G H (@one_fun G H) one_fun_gmulf1.

Fact mul_fun_gmulf1 : (f \* g) 1 = 1.
Proof. by rewrite /= !gmulf1 mulg1. Qed.

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
by move=> x xS; elim: n => [|[//|n] IHn]; [exact: gpred1 | exact: gpredM].
Qed.

End UMagma.
End UMagmaPred.

Section GroupPred.
Variables (G : groupType).

Lemma gpredV (S : invgClosed G) : {mono (@inv G): u / u \in S}.
Proof. by move=> u; apply/idP/idP=> /gpredVr; rewrite ?invgK; apply. Qed.

Section Group.
Variables S : groupClosed G.

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
by rewrite -(mulKg x y) gpredM// gpredV.
Qed.

Lemma gpredFr x y : x \in S -> (y / x \in S) = (y \in S).
Proof. by rewrite -gpredV; apply: gpredMr. Qed.

Lemma gpredFl x y : x \in S -> (x / y \in S) = (y \in S).
Proof. by rewrite -(gpredV S y); apply: gpredMl. Qed.

Lemma gpredJ x y : x \in S -> y \in S -> x ^ y \in S.
Proof. by move=> xS yS; apply/gpredM; [apply/gpredVr|apply/gpredM]. Qed.

Lemma gpredR x y : x \in S -> y \in S -> [~ x, y] \in S.
Proof. by move=> xS yS; apply/gpredM; [apply/gpredVr|apply/gpredJ]. Qed.

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

HB.instance Definition _ := hasMul.Build H mulH.

Lemma valM : {morph (val : H -> G) : x y / x * y}.
Proof. by move=> x y; rewrite SubK. Qed.

HB.instance Definition _ := isSubMagma.Build G S H valM.

HB.end.

#[short(type="subSemigroupType")]
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

HB.instance Definition _ := hasOne.Build H oneH.

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
split; first exact/(fst group_closed_subproof).
exact/group_closedM/group_closed_subproof.
Qed.
HB.instance Definition _ := SubChoice_isSubMonoid.Build G S H umagma_closed.
HB.instance Definition _ :=
  isInvClosed.Build G S (group_closedV group_closed_subproof).

Let inH v Sv : H := Sub v Sv.
Let invH (u : H) := inH (gpredVr _ (valP u)).

HB.instance Definition _ := hasInv.Build H invH.

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

HB.instance Definition _ := hasMul.Build {ffun aT -> rT} ffun_mul.

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
  hasOne.Build {ffun aT -> rT} ffun_one.

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
  UMagma.on {ffun aT -> rT}.

Section FinFunBaseGroup.

Variable (aT : finType) (rT : baseGroupType).
Implicit Types f g : {ffun aT -> rT}.

Definition ffun_inv f := [ffun a => (f a)^-1].

HB.instance Definition _ := hasInv.Build {ffun aT -> rT} ffun_inv.

End FinFunBaseGroup.

Section FinFunGroup.

Variable (aT : finType) (rT : groupType).
Implicit Types f g : {ffun aT -> rT}.

Fact ffun_mulVg :
  left_inverse (@ffun_one aT rT) (@ffun_inv _ _) (@ffun_mul _ _).
Proof. by move=> f; apply/ffunP=> a; rewrite !ffunE mulVg. Qed.
Fact ffun_mulgV :
  right_inverse (@ffun_one aT rT) (@ffun_inv _ _) (@ffun_mul _ _).
Proof. by move=> f; apply/ffunP=> a; rewrite !ffunE mulgV. Qed.

HB.instance Definition _ := Monoid_isGroup.Build {ffun aT -> rT}
  ffun_mulVg ffun_mulgV.

End FinFunGroup.

(* External direct product *)
Section PairMagma.
Variables G H : magmaType.

Definition mul_pair (x y : G * H) := (x.1 * y.1, x.2 * y.2).

HB.instance Definition _ := hasMul.Build (G * H)%type mul_pair.

Fact fst_is_multiplicative : {morph fst : x y / x * y}. Proof. by []. Qed.
HB.instance Definition _ :=
  isMultiplicative.Build _ _ fst fst_is_multiplicative.

Fact snd_is_multiplicative : {morph snd : x y / x * y}. Proof. by []. Qed.
HB.instance Definition _ :=
  isMultiplicative.Build _ _ snd snd_is_multiplicative.

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

HB.instance Definition _ := hasOne.Build (G * H)%type one_pair.

Fact fst_is_umagma_morphism : fst (1 : G * H) = 1. Proof. by []. Qed.
HB.instance Definition _ :=
  isUMagmaMorphism.Build _ _ fst fst_is_umagma_morphism.

Fact snd_is_umagma_morphism : snd (1 : G * H) = 1. Proof. by []. Qed.
HB.instance Definition _ :=
  isUMagmaMorphism.Build _ _ snd snd_is_umagma_morphism.

End PairBaseUMagma.

Section PairUMagma.
Variables G H : umagmaType.

Lemma pair_mul1g : left_id (@one_pair G H) *%g.
Proof. by move=> [x y]; congr (_, _); rewrite mul1g. Qed.
Lemma pair_mulg1 : right_id (@one_pair G H) *%g.
Proof. by move=> [x y]; congr (_, _); rewrite mulg1. Qed.

HB.instance Definition _ :=
  BaseUMagma_isUMagma.Build (G * H)%type pair_mul1g pair_mulg1.

End PairUMagma.

HB.instance Definition _ (G H : monoidType) := Semigroup.on (G * H)%type.

Section PairBaseGroup.
Variables G H : baseGroupType.

Definition inv_pair (u : G * H) := (u.1 ^-1, u.2 ^-1).

HB.instance Definition _ := hasInv.Build (G * H)%type inv_pair.

End PairBaseGroup.

Section PairGroup.
Variables G H : groupType.

Lemma pair_mulVg : left_inverse one (@inv_pair G H) mul.
Proof. by move=> x; congr (_, _); apply/mulVg. Qed.
Lemma pair_mulgV : right_inverse one (@inv_pair G H) mul.
Proof. by move=> x; congr (_, _); apply/mulgV. Qed.

HB.instance Definition _ :=
  Monoid_isGroup.Build (G * H)%type pair_mulVg pair_mulgV.

End PairGroup.

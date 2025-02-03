From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype choice ssrnat seq.
From mathcomp Require Import bigop fintype finfun monoid.

(******************************************************************************)
(*                       Additive group-like structures                       *)
(*                                                                            *)
(* NB: See CONTRIBUTING.md for an introduction to HB concepts and commands.   *)
(*                                                                            *)
(* This file defines the following algebraic structures:                      *)
(*                                                                            *)
(*         baseAddMagmaType == type with an addition operator                 *)
(*                             The HB class is called BaseAddMagma.           *)
(*  ChoiceBaseAddMagma.type == join of baseAddMagmaType and choiceType        *)
(*                             The HB class is called ChoiceBaseAddMagma.     *)
(*             addMagmaType == additive magma                                 *)
(*                             The HB class is called AddMagma.               *)
(*         addSemigroupType == additive semigroup                             *)
(*                             The HB class is called AddSemigroup.           *)
(*        baseAddUMagmaType == pointed additive magma                         *)
(*                             The HB class is called BaseAddUMagma.          *)
(* ChoiceBaseAddUMagma.type == join of baseAddUMagmaType and choiceType       *)
(*                             The HB class is called ChoiceBaseUMagma.       *)
(*            addUmagmaType == additive unitary magma                         *)
(*                             The HB class is called AddUMagma.              *)
(*                 nmodType == additive monoid                                *)
(*                             The HB class is called Nmodule.                *)
(*             baseZmodType == pointed additive magma with an opposite        *)
(*                             operator                                       *)
(*                             The HB class is called BaseZmodule.            *)
(*                 zmodType == abelian group                                  *)
(*                             The HB class is called Group.                  *)
(*                                                                            *)
(* and their joins with subType:                                              *)
(*                                                                            *)
(*  subBaseAddUMagmaType V P == join of baseAddUMagmaType and subType         *)
(*                              (P : pred V) such that val is additive        *)
(*                              The HB class is called SubBaseAddUMagma.      *)
(*      subAddUMagmaType V P == join of addUMagmaType and subType (P : pred V)*)
(*                              such that val is additive                     *)
(*                              The HB class is called SubAddUMagma.          *)
(*           subNmodType V P == join of nmodType and subType (P : pred V)     *)
(*                              such that val is additive                     *)
(*                              The HB class is called SubNmodule.            *)
(*           subZmodType V P == join of zmodType and subType (P : pred V)     *)
(*                              such that val is additive                     *)
(*                              The HB class is called SubZmodule.            *)
(*                                                                            *)
(* Morphisms between the above structures (see below for details):            *)
(*                                                                            *)
(*       {additive U -> V} == semi additive (resp. additive) functions between*)
(*                            nmodType (resp. zmodType) instances U and V.    *)
(*                            The HB class is called Additive.                *)
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
(*  * addMagmaType (additive magmas):                                         *)
(*                 x + y == the addition of x and y                           *)
(*         addg_closed S <-> collective predicate S is closed under addition  *)
(*                                                                            *)
(*  * baseAddUMagmaType (pointed additive magmas):                            *)
(*                     0 == the zero of a unitary additive magma              *)
(*                x *+ n == n times x, with n in nat (non-negative),          *)
(*                          i.e. x + (x + .. (x + x)..) (n terms); x *+ 1 is  *)
(*                          thus convertible to x, and x *+ 2 to x + x        *)
(*    addumagma_closed S <-> collective predicate S is closed under           *)
(*                          addition and contains 0                           *)
(*                                                                            *)
(*  * nmodType (abelian monoids):                                             *)
(*         nmod_closed S := addumagma_closed S                                *)
(*                                                                            *)
(*  * baseZmodType (pointed additive magmas with an opposite operator):       *)
(*                   - x == the opposite of x                                 *)
(*                 x - y == x + (- y)                                         *)
(*                x *- n == - (x *+ n)                                        *)
(*         oppg_closed S <-> collective predicate S is closed under opposite  *)
(*         subg_closed S <-> collective predicate S is closed under           *)
(*                           subtraction                                      *)
(*         zmod_closed S <-> collective predicate S is closed under           *)
(*                           subtraction and contains 1                       *)
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
(*                           canonical baseAddUMagmaType instances            *)
(*                           When both U and V have zmodType instances, it is *)
(*                           an additive function.                            *)
(*                        := GRing.Additive.type U V                          *)
(*                                                                            *)
(*   Notations are defined in scope ring_scope (delimiter %R)                 *)
(*   This library also extends the conventional suffixes described in library *)
(* ssrbool.v with the following:                                              *)
(*   0 -- unitary additive magma 0, as in addr0 : x + 0 = x                   *)
(*   D -- additive magma addition, as in mulrnDr :                            *)
(*        x *+ (m + n) = x *+ m + x *+ n                                      *)
(*   B -- z-module subtraction, as in opprB : - (x - y) = y - x               *)
(*  Mn -- ring by nat multiplication, as in raddfMn : f (x *+ n) = f x *+ n   *)
(*   N -- z-module opposite, as in mulNr : (- x) * y = - (x * y)              *)
(* The operator suffixes D, B are also used for the corresponding operations  *)
(* on nat, as in mulrDr : x *+ (m + n) = x *+ m + x *+ n.                     *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope ring_scope.
Delimit Scope ring_scope with R.
Local Open Scope ring_scope.

Reserved Notation "+%R" (at level 0).
Reserved Notation "-%R" (at level 0).
Reserved Notation "n %:R" (at level 2, left associativity, format "n %:R").
Reserved Notation "\0" (at level 0).
Reserved Notation "f \+ g" (at level 50, left associativity).
Reserved Notation "f \- g" (at level 50, left associativity).
Reserved Notation "\- f" (at level 35, f at level 35).

Reserved Notation "'{' 'additive' U '->' V '}'"
  (at level 0, U at level 98, V at level 99,
   format "{ 'additive'  U  ->  V }").

Module Import GRing.

HB.mixin Record hasAdd V := {
  add : V -> V -> V
}.

#[short(type="baseAddMagmaType")]
HB.structure Definition BaseAddMagma := {V of hasAdd V}.

Module BaseAddMagmaExports.
Bind Scope ring_scope with BaseAddMagma.sort.
End BaseAddMagmaExports.
HB.export BaseAddMagmaExports. 

HB.structure Definition ChoiceBaseAddMagma := {V of BaseAddMagma V & Choice V}.

Module ChoiceBaseAddMagmaExports.
Bind Scope ring_scope with ChoiceBaseAddMagma.sort.
End ChoiceBaseAddMagmaExports.
HB.export ChoiceBaseAddMagmaExports. 

Local Notation "+%R" := (@add _) : function_scope.
Local Notation "x + y" := (add x y) : ring_scope.

Definition to_multiplicative := @id Type.

#[export]
HB.instance Definition _ (V : choiceType) := Choice.on (to_multiplicative V).
#[export]
HB.instance Definition _ (V : baseAddMagmaType) :=
  hasMul.Build (to_multiplicative V) (@add V).

Section BaseAddMagmaTheory.
Variables V : baseAddMagmaType.

Section ClosedPredicates.

Variable S : {pred V}.

Definition addr_closed := {in S &, forall u v, u + v \in S}.

End ClosedPredicates.
End BaseAddMagmaTheory.

HB.mixin Record BaseAddMagma_isAddMagma V of BaseAddMagma V := {
  addrC : commutative (@add V)
}.

#[short(type="addMagmaType")]
HB.structure Definition AddMagma :=
  {V of BaseAddMagma_isAddMagma V & BaseAddMagma V & Choice V}.

HB.factory Record isAddMagma V of Choice V := {
  add : V -> V -> V;
  addrC : commutative add
}.

HB.builders Context V of isAddMagma V.
HB.instance Definition _ := hasAdd.Build V add.
HB.instance Definition _ := BaseAddMagma_isAddMagma.Build V addrC.
HB.end.

Module AddMagmaExports.
Bind Scope ring_scope with AddMagma.sort.
End AddMagmaExports.
HB.export AddMagmaExports.

Section AddMagmaTheory.
Variables V : addMagmaType.

Lemma commuteT x y : @commute (to_multiplicative V) x y.
Proof. exact/addrC. Qed.

End AddMagmaTheory.

HB.mixin Record AddMagma_isAddSemigroup V of AddMagma V := {
  addrA : associative (@add V)
}.

#[short(type="addSemigroupType")]
HB.structure Definition AddSemigroup :=
  {V of AddMagma_isAddSemigroup V & AddMagma V}.

HB.factory Record isAddSemigroup V of Choice V := {
  add : V -> V -> V;
  addrC : commutative add;
  addrA : associative add
}.

HB.builders Context V of isAddSemigroup V.
HB.instance Definition _ := isAddMagma.Build V addrC.
HB.instance Definition _ := AddMagma_isAddSemigroup.Build V addrA.
HB.end.

Module AddSemigroupExports.
Bind Scope ring_scope with AddSemigroup.sort.
End AddSemigroupExports.
HB.export AddSemigroupExports.

#[export]
HB.instance Definition _ (V : addSemigroupType) :=
  Magma_isSemigroup.Build (to_multiplicative V) addrA.

Section AddSemigroupTheory.
Variables V : addSemigroupType.

Lemma addrCA : @left_commutative V V +%R.
Proof. by move=> x y z; rewrite !addrA [x + _]addrC. Qed.

Lemma addrAC : @right_commutative V V +%R.
Proof. by move=> x y z; rewrite -!addrA [y + _]addrC. Qed.

Lemma addrACA : @interchange V +%R +%R.
Proof. by move=> x y z t; rewrite -!addrA [y + (z + t)]addrCA. Qed.

End AddSemigroupTheory.

HB.mixin Record hasZero V := {
  zero : V
}.

#[short(type="baseAddUMagmaType")]
HB.structure Definition BaseAddUMagma :=
  {V of hasZero V & BaseAddMagma V}.

Module BaseAddUMagmaExports.
Bind Scope ring_scope with BaseAddUMagma.sort.
End BaseAddUMagmaExports.
HB.export BaseAddUMagmaExports.

HB.structure Definition ChoiceBaseAddUMagma :=
  {V of BaseAddUMagma V & Choice V}.

Module ChoiceBaseAddUMagmaExports.
Bind Scope ring_scope with ChoiceBaseAddUMagma.sort.
End ChoiceBaseAddUMagmaExports.
HB.export ChoiceBaseAddUMagmaExports.

Local Notation "0" := (@zero _) : ring_scope.

Definition natmul (V : baseAddUMagmaType) (x : V) n : V := iterop n +%R x 0.
Arguments natmul : simpl never.

Local Notation "x *+ n" := (natmul x n) : ring_scope.

#[export]
HB.instance Definition _ (V : baseAddUMagmaType) :=
  hasOne.Build (to_multiplicative V) (@zero V).

Section BaseAddUMagmaTheory.
Variable V : baseAddUMagmaType.
Implicit Types x : V.

Lemma mulr0n x : x *+ 0 = 0. Proof. by []. Qed.
Lemma mulr1n x : x *+ 1 = x. Proof. by []. Qed.
Lemma mulr2n x : x *+ 2 = x + x. Proof. by []. Qed.
Lemma mulrb x (b : bool) : x *+ b = (if b then x else 0).
Proof. exact: (@expgb (to_multiplicative V)). Qed.
Lemma mulrSS x n : x *+ n.+2 = x + x *+ n.+1. Proof. by []. Qed.

Section ClosedPredicates.

Variable S : {pred V}.

Definition addumagma_closed := 0 \in S /\ addr_closed S.

End ClosedPredicates.

End BaseAddUMagmaTheory.

HB.mixin Record BaseAddUMagma_isAddUMagma V of BaseAddUMagma V := {
  add0r : left_id zero (@add V)
}.

HB.factory Record isAddUMagma V of Choice V := {
  add : V -> V -> V;
  zero : V;
  addrC : commutative add;
  add0r : left_id zero add
}.

HB.builders Context V of isAddUMagma V.
HB.instance Definition _ := isAddMagma.Build V addrC.
HB.instance Definition _ := hasZero.Build V zero.
#[warning="-HB.no-new-instance"]
HB.instance Definition _ := BaseAddUMagma_isAddUMagma.Build V add0r.
HB.end.

#[short(type="addUMagmaType")]
HB.structure Definition AddUMagma := {V of isAddUMagma V & Choice V}.

Lemma addr0 (V : addUMagmaType) : right_id (@zero V) add.
Proof. by move=> x; rewrite addrC add0r. Qed.

Local Notation "\sum_ ( i <- r | P ) F" := (\big[+%R/0]_(i <- r | P) F).
Local Notation "\sum_ ( m <= i < n ) F" := (\big[+%R/0]_(m <= i < n) F).
Local Notation "\sum_ ( i < n ) F" := (\big[+%R/0]_(i < n) F).
Local Notation "\sum_ ( i 'in' A ) F" := (\big[+%R/0]_(i in A) F).

Import Monoid.Theory.

#[export]
HB.instance Definition _ (V : addUMagmaType) :=
  Magma_isUMagma.Build (to_multiplicative V) add0r (@addr0 V).

HB.factory Record isNmodule V of Choice V := {
  zero : V;
  add : V -> V -> V;
  addrA : associative add;
  addrC : commutative add;
  add0r : left_id zero add
}.

HB.builders Context V of isNmodule V.
HB.instance Definition _ := isAddUMagma.Build V addrC add0r.
HB.instance Definition _ := AddMagma_isAddSemigroup.Build V addrA.
HB.end.

Module AddUMagmaExports.
Bind Scope ring_scope with AddUMagma.sort.
End AddUMagmaExports.
HB.export AddUMagmaExports.

#[short(type="nmodType")]
HB.structure Definition Nmodule := {V of isNmodule V & Choice V}.

Module NmoduleExports.
Bind Scope ring_scope with Nmodule.sort.
End NmoduleExports.
HB.export NmoduleExports.

#[export]
HB.instance Definition _ (V : nmodType) :=
  UMagma_isMonoid.Build (to_multiplicative V) addrA.

#[export]
HB.instance Definition _ (V : nmodType) :=
  Monoid.isComLaw.Build V 0%R +%R addrA addrC add0r.

Section NmoduleTheory.

Variable V : nmodType.
Implicit Types x y : V.

Let G := to_multiplicative V.

(* addrA, addrC and add0r in the structure *)
(* addr0 proved above *)

Lemma mulrS x n : x *+ n.+1 = x + (x *+ n).
Proof. exact: (@expgS G). Qed.

Lemma mulrSr x n : x *+ n.+1 = x *+ n + x.
Proof. exact: (@expgSr G). Qed.

Lemma mul0rn n : 0 *+ n = 0 :> V.
Proof. exact: (@expg1n G). Qed.

Lemma mulrnDl n : {morph (fun x => x *+ n) : x y / x + y}.
Proof. by move=> x y; apply/(@expgMn G)/commuteT. Qed.

Lemma mulrnDr x m n : x *+ (m + n) = x *+ m + x *+ n.
Proof. exact: (@expgnDr G). Qed.

Lemma mulrnA x m n : x *+ (m * n) = x *+ m *+ n.
Proof. exact: (@expgnA G). Qed.

Lemma mulrnAC x m n : x *+ m *+ n = x *+ n *+ m.
Proof. exact: (@expgnAC G). Qed.

Lemma iter_addr n x y : iter n (+%R x) y = x *+ n + y.
Proof. exact: (@iter_mulg G). Qed.

Lemma iter_addr_0 n x : iter n (+%R x) 0 = x *+ n.
Proof. exact: (@iter_mulg_1 G). Qed.

Lemma sumrMnl I r P (F : I -> V) n :
  \sum_(i <- r | P i) F i *+ n = (\sum_(i <- r | P i) F i) *+ n.
Proof. by rewrite (big_morph _ (mulrnDl n) (mul0rn _)). Qed.

Lemma sumrMnr x I r P (F : I -> nat) :
  \sum_(i <- r | P i) x *+ F i = x *+ (\sum_(i <- r | P i) F i).
Proof. by rewrite (big_morph _ (mulrnDr x) (erefl _)). Qed.

Lemma sumr_const (I : finType) (A : pred I) x : \sum_(i in A) x = x *+ #|A|.
Proof. by rewrite big_const -iteropE. Qed.

Lemma sumr_const_nat m n x : \sum_(n <= i < m) x = x *+ (m - n).
Proof. by rewrite big_const_nat iter_addr_0. Qed.

Section ClosedPredicates.

Variable S : {pred V}.

Definition nmod_closed := addumagma_closed S.

End ClosedPredicates.

End NmoduleTheory.

HB.mixin Record hasOpp V := {
  opp : V -> V
}.

#[short(type="baseZmodType")]
HB.structure Definition BaseZmodule := {V of hasOpp V & BaseAddUMagma V}.

Module BaseZmodExports.
Bind Scope ring_scope with BaseZmodule.sort.
End BaseZmodExports.
HB.export BaseZmodExports.

Local Notation "-%R" := (@opp _) : ring_scope.
Local Notation "- x" := (opp x) : ring_scope.
Local Notation "x - y" := (x + - y) : ring_scope.
Local Notation "x *- n" := (- (x *+ n)) : ring_scope.

Section ClosedPredicates.

Variable (U : baseZmodType) (S : {pred U}).

Definition oppr_closed := {in S, forall u, - u \in S}.
Definition subr_closed := {in S &, forall u v, u - v \in S}.
Definition zmod_closed := 0 \in S /\ subr_closed.

End ClosedPredicates.

HB.mixin Record BaseZmoduleNmodule_isZmodule V of BaseZmodule V := {
  addNr : left_inverse zero opp (@add V)
}.

#[short(type="zmodType")]
HB.structure Definition Zmodule :=
  {V of BaseZmoduleNmodule_isZmodule V & BaseZmodule V & Nmodule V}.

HB.factory Record Nmodule_isZmodule V of Nmodule V := {
  opp : V -> V;
  addNr : left_inverse zero opp add
}.

HB.builders Context V of Nmodule_isZmodule V.
HB.instance Definition _ := hasOpp.Build V opp.
HB.instance Definition _ := BaseZmoduleNmodule_isZmodule.Build V addNr.
HB.end.

HB.factory Record isZmodule V of Choice V := {
  zero : V;
  opp : V -> V;
  add : V -> V -> V;
  addrA : associative add;
  addrC : commutative add;
  add0r : left_id zero add;
  addNr : left_inverse zero opp add
}.

HB.builders Context V of isZmodule V.

HB.instance Definition _ := isNmodule.Build V addrA addrC add0r.
HB.instance Definition _ := Nmodule_isZmodule.Build V addNr.

HB.end.

HB.factory Record Group_isZmodule V of Group V := {
  mulgC : commutative (@mul V)
}.

HB.builders Context V of Group_isZmodule V.

HB.instance Definition _ := isZmodule.Build V mulgA mulgC mul1g mulVg.

HB.end.

Module ZmoduleExports.
Bind Scope ring_scope with Zmodule.sort.
End ZmoduleExports.
HB.export ZmoduleExports.

Lemma addrN (V : zmodType) : @right_inverse V V V 0 -%R +%R.
Proof. by move=> x; rewrite addrC addNr. Qed.

#[export]
HB.instance Definition _ (V : baseZmodType) :=
  hasInv.Build (to_multiplicative V) (@opp V).
#[export]
HB.instance Definition _ (V : zmodType) :=
  Monoid_isGroup.Build (to_multiplicative V) addNr (@addrN V).

Section ZmoduleTheory.

Variable V : zmodType.
Implicit Types x y : V.

Let G := to_multiplicative V.

Definition subrr := addrN.

Lemma addKr : @left_loop V V -%R +%R.
Proof. exact: (@mulKg G). Qed.
Lemma addNKr : @rev_left_loop V V -%R +%R.
Proof. exact: (@mulVKg G). Qed.
Lemma addrK : @right_loop V V -%R +%R.
Proof. exact: (@mulgK G). Qed.
Lemma addrNK : @rev_right_loop V V -%R +%R.
Proof. exact: (@mulgVK G). Qed.
Definition subrK := addrNK.
Lemma subKr x : involutive (fun y => x - y).
Proof. by move=> y; exact/(@divKg G)/commuteT. Qed.
Lemma addrI : @right_injective V V V +%R.
Proof. exact: (@mulgI G). Qed.
Lemma addIr : @left_injective V V V +%R.
Proof. exact: (@mulIg G). Qed.
Lemma subrI : right_injective (fun x y => x - y).
Proof. exact: (@divgI G). Qed.
Lemma subIr : left_injective (fun x y => x - y).
Proof. exact: (@divIg G). Qed.
Lemma opprK : @involutive V -%R.
Proof. exact: (@invgK G). Qed.
Lemma oppr_inj : @injective V V -%R.
Proof. exact: (@invg_inj G). Qed.
Lemma oppr0 : -0 = 0 :> V.
Proof. exact: (@invg1 G). Qed.
Lemma oppr_eq0 x : (- x == 0) = (x == 0).
Proof. exact: (@invg_eq1 G). Qed.

Lemma subr0 x : x - 0 = x. Proof. exact: (@divg1 G). Qed.
Lemma sub0r x : 0 - x = - x. Proof. exact: (@div1g G). Qed.

Lemma opprB x y : - (x - y) = y - x.
Proof. exact: (@invgF G). Qed.

Lemma opprD : {morph -%R: x y / x + y : V}.
Proof. by move=> x y; rewrite -[y in LHS]opprK opprB addrC. Qed.

Lemma addrKA z x y : (x + z) - (z + y) = x - y.
Proof. by rewrite opprD addrA addrK. Qed.

Lemma subrKA z x y : (x - z) + (z + y) = x + y.
Proof. exact: (@divgKA G). Qed.

Lemma addr0_eq x y : x + y = 0 -> - x = y.
Proof. exact: (@mulg1_eq G). Qed.

Lemma subr0_eq x y : x - y = 0 -> x = y.
Proof. exact: (@divg1_eq G). Qed.

Lemma subr_eq x y z : (x - z == y) = (x == y + z).
Proof. exact: (@divg_eq G). Qed.

Lemma subr_eq0 x y : (x - y == 0) = (x == y).
Proof. exact: (@divg_eq1 G). Qed.

Lemma addr_eq0 x y : (x + y == 0) = (x == - y).
Proof. exact: (@mulg_eq1 G). Qed.

Lemma eqr_opp x y : (- x == - y) = (x == y).
Proof. exact: (@eqg_inv G). Qed.

Lemma eqr_oppLR x y : (- x == y) = (x == - y).
Proof. exact: (@eqg_invLR G). Qed.

Lemma mulNrn x n : (- x) *+ n = x *- n.
Proof. exact: (@expVgn G). Qed.

Lemma mulrnBl n : {morph (fun x => x *+ n) : x y / x - y}.
Proof. by move=> x y; exact/(@expgnFl G)/commuteT. Qed.

Lemma mulrnBr x m n : n <= m -> x *+ (m - n) = x *+ m - x *+ n.
Proof. exact: (@expgnFr G). Qed.

Lemma sumrN I r P (F : I -> V) :
  (\sum_(i <- r | P i) - F i = - (\sum_(i <- r | P i) F i)).
Proof. by rewrite (big_morph _ opprD oppr0). Qed.

Lemma sumrB I r (P : pred I) (F1 F2 : I -> V) :
  \sum_(i <- r | P i) (F1 i - F2 i)
     = \sum_(i <- r | P i) F1 i - \sum_(i <- r | P i) F2 i.
Proof. by rewrite -sumrN -big_split /=. Qed.

Lemma telescope_sumr n m (f : nat -> V) : n <= m ->
  \sum_(n <= k < m) (f k.+1 - f k) = f m - f n.
Proof.
move=> nm; rewrite (telescope_big (fun i j => f j - f i)).
  by case: ltngtP nm => // ->; rewrite subrr.
by move=> k /andP[nk km]/=; rewrite addrC subrKA.
Qed.

Lemma telescope_sumr_eq n m (f u : nat -> V) : n <= m ->
    (forall k, (n <= k < m)%N -> u k = f k.+1 - f k) ->
  \sum_(n <= k < m) u k = f m - f n.
Proof.
by move=> ? uE; under eq_big_nat do rewrite uE //=; exact: telescope_sumr.
Qed.

Section ClosedPredicates.

Variable (S : {pred V}).

Lemma zmod_closedN : zmod_closed S -> oppr_closed S.
Proof. exact: (@group_closedV G). Qed.

Lemma zmod_closedD : zmod_closed S -> addr_closed S.
Proof. exact: (@group_closedM G). Qed.

Lemma zmod_closed0D : zmod_closed S -> nmod_closed S.
Proof. by move=> z; split; [case: z|apply: zmod_closedD]. Qed.

End ClosedPredicates.

End ZmoduleTheory.

Arguments addrI {V} y [x1 x2].
Arguments addIr {V} x [x1 x2].
Arguments opprK {V}.
Arguments oppr_inj {V} [x1 x2].

Definition semi_additive (U V : baseAddUMagmaType) (f : U -> V) : Prop :=
  (f 0 = 0) * {morph f : x y / x + y}.

HB.mixin Record isSemiAdditive (U V : baseAddUMagmaType) (apply : U -> V) := {
  semi_additive_subproof : semi_additive apply;
}.

#[mathcomp(axiom="semi_additive")]
HB.structure Definition Additive (U V : baseAddUMagmaType) :=
  {f of isSemiAdditive U V f}.

Definition additive (U V : zmodType) (f : U -> V) := {morph f : x y / x - y}.

HB.factory Record isAdditive (U V : zmodType) (apply : U -> V) := {
  additive_subproof : additive apply;
}.

HB.builders Context U V apply of isAdditive U V apply.
Local Lemma raddf0 : apply 0 = 0.
Proof. by rewrite -[0]subr0 additive_subproof subrr. Qed.

Local Lemma raddfD : {morph apply : x y / x + y}.
Proof.
move=> x y; rewrite -[y in LHS]opprK -[- y]add0r.
by rewrite !additive_subproof raddf0 sub0r opprK.
Qed.

HB.instance Definition _ := isSemiAdditive.Build U V apply (conj raddf0 raddfD).

HB.end.

Module AdditiveExports.
Notation "{ 'additive' U -> V }" := (Additive.type U%type V%type) : type_scope.
End AdditiveExports.
HB.export AdditiveExports.

Section AdditiveTheory.
Variables (U V : baseAddUMagmaType) (f : {additive U -> V}).

Lemma raddf0 : f 0 = 0.
Proof. by case: (@semi_additive_subproof _ _ f). Qed.

Lemma raddfD :
  {morph f : x y / x + y}.
Proof. by case: (@semi_additive_subproof _ _ f). Qed.

Lemma raddf_sum I r (P : pred I) E :
  f (\sum_(i <- r | P i) E i) = \sum_(i <- r | P i) f (E i).
Proof. exact: (big_morph f raddfD raddf0). Qed.

End AdditiveTheory.

Definition to_fmultiplicative U V := @id (to_multiplicative U -> to_multiplicative V).

#[export]
HB.instance Definition _ U V (f : {additive U -> V}) :=
  isMultiplicative.Build (to_multiplicative U) (to_multiplicative V)
    (to_fmultiplicative f) (@raddfD _ _ f).
#[export]
HB.instance Definition _ (U V : baseAddUMagmaType) (f : {additive U -> V}) :=
  isUMagmaMorphism.Build (to_multiplicative U) (to_multiplicative V)
    (to_fmultiplicative f) (@raddf0 _ _ f).

Section LiftedAddMagma.
Variables (U : Type) (V : baseAddMagmaType).
Definition add_fun (f g : U -> V) x := f x + g x.
End LiftedAddMagma.
Section LiftedNmod.
Variables (U : Type) (V : baseAddUMagmaType).
Definition null_fun of U : V := 0.
End LiftedNmod.
Section LiftedZmod.
Variables (U : Type) (V : baseZmodType).
Definition opp_fun (f : U -> V) x := - f x.
Definition sub_fun (f g : U -> V) x := f x - g x.
End LiftedZmod.

Arguments null_fun {_} V _ /.
Arguments add_fun {_ _} f g _ /.
Arguments opp_fun {_ _} f _ /.
Arguments sub_fun {_ _} f g _ /.

Local Notation "\0" := (null_fun _) : function_scope.
Local Notation "f \+ g" := (add_fun f g) : function_scope.
Local Notation "\- f" := (opp_fun f) : function_scope.
Local Notation "f \- g" := (sub_fun f g) : function_scope.

Section Nmod.
Variables (U V : addUMagmaType) (f : {additive U -> V}).
Let g := to_fmultiplicative f.

Lemma raddf_eq0 x : injective f -> (f x == 0) = (x == 0).
Proof.
move=> fK; apply/eqP/eqP => [|->]; last by rewrite raddf0.
by rewrite -[RHS](raddf0 f) => /fK.
Qed.

Lemma raddfMn n : {morph f : x / x *+ n}.
Proof. exact: (@gmulfXn _ _ g). Qed.

Lemma can2_semi_additive f' : cancel f f' -> cancel f' f -> semi_additive f'.
Proof.
split; first exact/(@can2_gmulf1 _ _ g).
exact/(@can2_gmulfM _ _ g).
Qed.

End Nmod.

Section Zmod.
Variables (U V : zmodType) (f : {additive U -> V}).
Let g := to_fmultiplicative f.

Lemma raddfN : {morph f : x / - x}.
Proof. exact: (@gmulfV _ _ g). Qed.

Lemma raddfB : {morph f : x y / x - y}.
Proof. exact: (@gmulfF _ _ g). Qed.

Lemma raddf_inj : (forall x, f x = 0 -> x = 0) -> injective f.
Proof. exact: (@gmulf_inj _ _ g). Qed.

Lemma raddfMNn n : {morph f : x / x *- n}.
Proof. exact: (@gmulfXVn _ _ g). Qed.

Lemma can2_additive f' : cancel f f' -> cancel f' f -> additive f'.
Proof. by move=> fK f'K x y /=; apply: (canLR fK); rewrite raddfB !f'K. Qed.
End Zmod.

Section AdditiveTheory.
Section AddCFun.
Variables (U : baseAddUMagmaType) (V : nmodType).
Implicit Types (f g : {additive U -> V}).

Fact add_fun_semi_additive f g : semi_additive (add_fun f g).
Proof.
split; first by rewrite /= !raddf0 addr0.
by move=> x y; rewrite /= !raddfD [LHS]addrACA.
Qed.
#[export]
HB.instance Definition _ f g :=
  isSemiAdditive.Build U V (add_fun f g) (add_fun_semi_additive f g).



End AddCFun.

Section AddFun.
Variables (U V W : baseAddUMagmaType).
Variables (f : {additive V -> W}) (g : {additive U -> V}).

Fact idfun_is_semi_additive : semi_additive (@idfun U).
Proof. by []. Qed.
#[export]
HB.instance Definition _ := isSemiAdditive.Build U U idfun
  idfun_is_semi_additive.

Fact comp_is_semi_additive : semi_additive (f \o g).
Proof. by split=> [|x y]; rewrite /= ?raddf0// !raddfD. Qed.
#[export]
HB.instance Definition _ := isSemiAdditive.Build U W (f \o g)
  comp_is_semi_additive.

End AddFun.
Section AddFun.
Variables (U : baseAddUMagmaType) (V : addUMagmaType).

Fact null_fun_is_semi_additive : semi_additive (\0 : U -> V).
Proof. by split=> // x y /=; rewrite addr0. Qed.
#[export]
HB.instance Definition _ :=
  isSemiAdditive.Build U V (\0 : U -> V)
    null_fun_is_semi_additive.

End AddFun.

Section AddVFun.

Fact opp_is_semi_additive (U : zmodType) : semi_additive (@opp U).
Proof. by split; [apply/oppr0|apply/opprD]. Qed.
#[export]
HB.instance Definition _ (U : zmodType) :=
  isSemiAdditive.Build U U (@opp U) (opp_is_semi_additive U).

Fact opp_fun_is_additive (U : baseAddUMagmaType) (V : zmodType)
    (f : {additive U -> V}) :
  semi_additive (\- f).
Proof.
split=> [|x y]; first by rewrite -[LHS]/(- (f 0)) raddf0 oppr0.
by rewrite -[LHS]/(- (f (x + y))) !raddfD/=.
Qed.
#[export]
HB.instance Definition _ (U : baseAddUMagmaType) (V : zmodType)
    (f : {additive U -> V}) :=
  isSemiAdditive.Build U V (opp_fun f) (opp_fun_is_additive f).

Fact sub_fun_is_additive (U : baseAddUMagmaType) (V : zmodType)
    (f g : {additive U -> V}) :
  semi_additive (f \- g).
Proof.
split=> [|x y]/=; first by rewrite !raddf0 addr0.
by rewrite !raddfD/= addrACA.
Qed.
#[export]
HB.instance Definition _ (U : baseAddUMagmaType) (V : zmodType)
    (f g : {additive U -> V}) :=
  isSemiAdditive.Build U V (f \- g) (sub_fun_is_additive f g).


End AddVFun.
End AdditiveTheory.

(* Mixins for stability properties *)

HB.mixin Record isAddClosed (V : baseAddUMagmaType) (S : {pred V}) := {
  nmod_closed_subproof : addumagma_closed S
}.

HB.mixin Record isOppClosed (V : zmodType) (S : {pred V}) := {
  oppr_closed_subproof : oppr_closed S
}.

(* Structures for stability properties *)

#[short(type="addrClosed")]
HB.structure Definition AddClosed V := {S of isAddClosed V S}.

#[short(type="opprClosed")]
HB.structure Definition OppClosed V := {S of isOppClosed V S}.

#[short(type="zmodClosed")]
HB.structure Definition ZmodClosed V := {S of OppClosed V S & AddClosed V S}.

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

Definition to_pmultiplicative (T : Type) := @id {pred to_multiplicative T}.

#[export]
HB.instance Definition _ (U : baseAddUMagmaType) (S : addrClosed U) :=
  isMulClosed.Build (to_multiplicative U) (to_pmultiplicative S)
    (snd nmod_closed_subproof).
#[export]
HB.instance Definition _ (U : baseAddUMagmaType) (S : addrClosed U) :=
  isMul1Closed.Build (to_multiplicative U) (to_pmultiplicative S)
    (fst nmod_closed_subproof).
#[export]
HB.instance Definition _ (U : zmodType) (S : opprClosed U) :=
  isInvClosed.Build (to_multiplicative U) (to_pmultiplicative S) oppr_closed_subproof.

(* FIXME: HB.saturate *)
#[export]
HB.instance Definition _ (U : zmodType) (S : zmodClosed U) :=
  InvClosed.on (to_pmultiplicative S).

Section BaseAddUMagmaPred.
Variables (V : baseAddUMagmaType).

Section BaseAddUMagmaPred.
Variables S : addrClosed V.

Lemma rpred0 : 0 \in S.
Proof. by case: (@nmod_closed_subproof V S). Qed.
Lemma rpredD : {in S &, forall u v, u + v \in S}.
Proof. by case: (@nmod_closed_subproof V S). Qed.

Lemma rpred0D : addumagma_closed S.
Proof. exact: nmod_closed_subproof. Qed.

Lemma rpredMn n : {in S, forall u, u *+ n \in S}.
Proof. exact: (@gpredXn _ (to_pmultiplicative S)). Qed.

Lemma rpred_sum I r (P : pred I) F :
  (forall i, P i -> F i \in S) -> \sum_(i <- r | P i) F i \in S.
Proof. by move=> IH; elim/big_ind: _; [apply: rpred0 | apply: rpredD |]. Qed.

End BaseAddUMagmaPred.
End BaseAddUMagmaPred.

Section ZmodPred.
Variables (V : zmodType).

Section Opp.

Variable S : opprClosed V.

Lemma rpredNr : {in S, forall u, - u \in S}.
Proof. exact: oppr_closed_subproof. Qed.

Lemma rpredN : {mono -%R: u / u \in S}.
Proof. exact: (gpredV (to_pmultiplicative S)). Qed.

End Opp.

Section Zmod.
Variables S : zmodClosed V.
Let T := to_pmultiplicative S.

Lemma rpredB : {in S &, forall u v, u - v \in S}.
Proof. exact: (@gpredF _ T). Qed.

Lemma rpredBC u v : u - v \in S = (v - u \in S).
Proof. exact: (@gpredFC _ T). Qed.

Lemma rpredMNn n: {in S, forall u, u *- n \in S}.
Proof. exact: (@gpredXNn _ T). Qed.

Lemma rpredDr x y : x \in S -> (y + x \in S) = (y \in S).
Proof. exact: (@gpredMr _ T). Qed.

Lemma rpredDl x y : x \in S -> (x + y \in S) = (y \in S).
Proof. exact: (@gpredMl _ T). Qed.

Lemma rpredBr x y : x \in S -> (y - x \in S) = (y \in S).
Proof. exact: (@gpredFr _ T). Qed.

Lemma rpredBl x y : x \in S -> (x - y \in S) = (y \in S).
Proof. exact: (@gpredFl _ T). Qed.

Lemma zmodClosedP : zmod_closed S.
Proof. split; [ exact: (@rpred0D V S).1 | exact: rpredB ]. Qed.
End Zmod.
End ZmodPred. 

HB.mixin Record isSubBaseAddUMagma (V : baseAddUMagmaType) (S : pred V) U
    of SubType V S U & BaseAddUMagma U := {
  valD0_subproof : semi_additive (val : U -> V)
}.

#[short(type="subBaseAddUMagma")]
HB.structure Definition SubBaseAddUMagma (V : baseAddUMagmaType) S :=
  { U of SubChoice V S U & BaseAddUMagma U & isSubBaseAddUMagma V S U }.

#[short(type="subAddUMagma")]
HB.structure Definition SubAddUMagma (V : addUMagmaType) S :=
  { U of SubChoice V S U & AddUMagma U & isSubBaseAddUMagma V S U }.

#[short(type="subNmodType")]
HB.structure Definition SubNmodule (V : nmodType) S :=
  { U of SubChoice V S U & Nmodule U & isSubBaseAddUMagma V S U}.

Section subBaseAddUMagma.
Context (V : baseAddUMagmaType) (S : pred V) (U : subBaseAddUMagma S).
Notation val := (val : U -> V).
#[export]
HB.instance Definition _ := isSemiAdditive.Build U V val valD0_subproof.
Lemma valD : {morph val : x y / x + y}. Proof. exact: raddfD. Qed.
Lemma val0 : val 0 = 0. Proof. exact: raddf0. Qed.
End subBaseAddUMagma.

HB.factory Record SubChoice_isSubAddUMagma (V : addUMagmaType) S U
    of SubChoice V S U := {
  addumagma_closed_subproof : addumagma_closed S
}.

HB.builders Context V S U of SubChoice_isSubAddUMagma V S U.

HB.instance Definition _ := isAddClosed.Build V S addumagma_closed_subproof.

Let inU v Sv : U := Sub v Sv.
Let addU (u1 u2 : U) := inU (rpredD (valP u1) (valP u2)).
Let oneU := inU (fst addumagma_closed_subproof).

Lemma addrC : commutative addU.
Proof. by move=> x y; apply/val_inj; rewrite !SubK addrC. Qed.

Lemma add0r : left_id oneU addU.
Proof. by move=> x; apply/val_inj; rewrite !SubK add0r. Qed.

HB.instance Definition _ := isAddUMagma.Build U addrC add0r.

Lemma valD0 : semi_additive (val : U -> V).
Proof. by split=> [|x y]; rewrite !SubK. Qed.

HB.instance Definition _ := isSubBaseAddUMagma.Build V S U valD0.

HB.end.

HB.factory Record SubChoice_isSubNmodule (V : nmodType) S U
    of SubChoice V S U := {
  nmod_closed_subproof : nmod_closed S
}.

HB.builders Context V S U of SubChoice_isSubNmodule V S U.

HB.instance Definition _ :=
  SubChoice_isSubAddUMagma.Build V S U nmod_closed_subproof.

Lemma addrA : associative (@add U).
Proof. by move=> x y z; apply/val_inj; rewrite !SubK addrA. Qed.

HB.instance Definition _ := AddMagma_isAddSemigroup.Build U addrA.

HB.end.

#[short(type="subZmodType")]
HB.structure Definition SubZmodule (V : zmodType) S :=
  { U of SubChoice V S U & Zmodule U & isSubBaseAddUMagma V S U}.

Section additive.
Context (V : zmodType) (S : pred V) (U : SubZmodule.type S).
Notation val := (val : U -> V).
Lemma valB : {morph val : x y / x - y}. Proof. exact: raddfB. Qed.
Lemma valN : {morph val : x / - x}. Proof. exact: raddfN. Qed.
End additive.

HB.factory Record isSubZmodule (V : zmodType) S U
    of SubChoice V S U & Zmodule U := {
  valB_subproof : additive (val : U -> V)
}.

HB.builders Context V S U of isSubZmodule V S U.

Fact valD0 : semi_additive (val : U -> V).
Proof.
have val0: (val : U -> V) 0 = 0.
  by rewrite -[X in val X](subr0 0) valB_subproof subrr.
split=> // x y; apply/(@subIr _ (val y)).
by rewrite -valB_subproof -!addrA !subrr !addr0.
Qed.

HB.instance Definition _ := isSubBaseAddUMagma.Build V S U valD0.

HB.end.

HB.factory Record SubChoice_isSubZmodule (V : zmodType) S U
    of SubChoice V S U := {
  zmod_closed_subproof : zmod_closed S
}.

HB.builders Context V S U of SubChoice_isSubZmodule V S U.

HB.instance Definition _ := isZmodClosed.Build V S zmod_closed_subproof.
HB.instance Definition _ :=
  SubChoice_isSubNmodule.Build V S U nmod_closed_subproof.

Let inU v Sv : U := Sub v Sv.
Let oppU (u : U) := inU (rpredNr (valP u)).

HB.instance Definition _ := hasOpp.Build U oppU.

Lemma addNr : left_inverse 0 oppU (@add U).
Proof. by move=> x; apply/val_inj; rewrite !SubK addNr. Qed.

HB.instance Definition _ := Nmodule_isZmodule.Build U addNr.

HB.end.

Module SubExports.

Notation "[ 'SubChoice_isSubNmodule' 'of' U 'by' <: ]" :=
  (SubChoice_isSubNmodule.Build _ _ U rpred0D)
  (at level 0, format "[ 'SubChoice_isSubNmodule'  'of'  U  'by'  <: ]")
  : form_scope.
Notation "[ 'SubChoice_isSubZmodule' 'of' U 'by' <: ]" :=
  (SubChoice_isSubZmodule.Build _ _ U (zmodClosedP _))
  (at level 0, format "[ 'SubChoice_isSubZmodule'  'of'  U  'by'  <: ]")
  : form_scope.

End SubExports.
HB.export SubExports.

Module AllExports. HB.reexport. End AllExports.

End GRing.

Export AllExports.

Notation "0" := (@zero _) : ring_scope.
Notation "-%R" := (@opp _) : ring_scope.
Notation "- x" := (opp x) : ring_scope.
Notation "+%R" := (@add _) : function_scope.
Notation "x + y" := (add x y) : ring_scope.
Notation "x - y" := (add x (- y)) : ring_scope.
Arguments natmul : simpl never.
Notation "x *+ n" := (natmul x n) : ring_scope.
Notation "x *- n" := (opp (x *+ n)) : ring_scope.
Notation "s `_ i" := (seq.nth 0%R s%R i) : ring_scope.
Notation support := 0.-support.

Notation "1" := (@one _) : ring_scope.
Notation "- 1" := (opp 1) : ring_scope.

Notation "n %:R" := (natmul 1 n) : ring_scope.

Notation "\sum_ ( i <- r | P ) F" :=
  (\big[+%R/0%R]_(i <- r | P%B) F%R) : ring_scope.
Notation "\sum_ ( i <- r ) F" :=
  (\big[+%R/0%R]_(i <- r) F%R) : ring_scope.
Notation "\sum_ ( m <= i < n | P ) F" :=
  (\big[+%R/0%R]_(m <= i < n | P%B) F%R) : ring_scope.
Notation "\sum_ ( m <= i < n ) F" :=
  (\big[+%R/0%R]_(m <= i < n) F%R) : ring_scope.
Notation "\sum_ ( i | P ) F" :=
  (\big[+%R/0%R]_(i | P%B) F%R) : ring_scope.
Notation "\sum_ i F" :=
  (\big[+%R/0%R]_i F%R) : ring_scope.
Notation "\sum_ ( i : t | P ) F" :=
  (\big[+%R/0%R]_(i : t | P%B) F%R) (only parsing) : ring_scope.
Notation "\sum_ ( i : t ) F" :=
  (\big[+%R/0%R]_(i : t) F%R) (only parsing) : ring_scope.
Notation "\sum_ ( i < n | P ) F" :=
  (\big[+%R/0%R]_(i < n | P%B) F%R) : ring_scope.
Notation "\sum_ ( i < n ) F" :=
  (\big[+%R/0%R]_(i < n) F%R) : ring_scope.
Notation "\sum_ ( i 'in' A | P ) F" :=
  (\big[+%R/0%R]_(i in A | P%B) F%R) : ring_scope.
Notation "\sum_ ( i 'in' A ) F" :=
  (\big[+%R/0%R]_(i in A) F%R) : ring_scope.

Section FinFunBaseAddMagma.
Variable (aT : finType) (rT : baseAddMagmaType).
Implicit Types f g : {ffun aT -> rT}.

Definition ffun_add f g := [ffun a => f a + g a].

HB.instance Definition _ := hasAdd.Build {ffun aT -> rT} ffun_add.

End FinFunBaseAddMagma.

Section FinFunAddMagma.
Variable (aT : finType) (rT : addMagmaType).
Implicit Types f g : {ffun aT -> rT}.

Fact ffun_addrC : commutative (@ffun_add aT rT).
Proof. by move=> f1 f2; apply/ffunP => a; rewrite !ffunE addrC. Qed.

HB.instance Definition _ :=
  BaseAddMagma_isAddMagma.Build {ffun aT -> rT} ffun_addrC.

End FinFunAddMagma.

Section FinFunAddSemigroup.
Variable (aT : finType) (rT : addSemigroupType).
Implicit Types f g : {ffun aT -> rT}.

Fact ffun_addrA : associative (@ffun_add aT rT).
Proof. by move=> f g h; apply/ffunP => a; rewrite !ffunE addrA. Qed.

HB.instance Definition _ :=
  AddMagma_isAddSemigroup.Build {ffun aT -> rT} ffun_addrA.

End FinFunAddSemigroup.

Section FinFunBaseAddUMagma.
Variable (aT : finType) (rT : baseAddUMagmaType).
Implicit Types f g : {ffun aT -> rT}.

Definition ffun_zero := [ffun a : aT => (0 : rT)].

HB.instance Definition _ := hasZero.Build {ffun aT -> rT} ffun_zero.

End FinFunBaseAddUMagma.

Section FinFunAddUMagma.
Variable (aT : finType) (rT : addUMagmaType).
Implicit Types f g : {ffun aT -> rT}.

Fact ffun_add0r : left_id (@ffun_zero aT rT) (@ffun_add aT rT).
Proof. by move=> f; apply/ffunP => a; rewrite !ffunE add0r. Qed.

HB.instance Definition _ :=
  BaseAddUMagma_isAddUMagma.Build {ffun aT -> rT} ffun_add0r.

End FinFunAddUMagma.

(* FIXME: HB.saturate *)
HB.instance Definition _ (aT : finType) (rT : ChoiceBaseAddMagma.type) :=
  BaseAddMagma.on {ffun aT -> rT}.
HB.instance Definition _ (aT : finType) (rT : ChoiceBaseAddUMagma.type) :=
  BaseAddMagma.on {ffun aT -> rT}.

Section FinFunNmod.
Variable (aT : finType) (rT : nmodType).
Implicit Types f g : {ffun aT -> rT}.

(* FIXME: HB.saturate *)
HB.instance Definition _ := AddSemigroup.on {ffun aT -> rT}.

Lemma ffunMnE f n x : (f *+ n) x = f x *+ n.
Proof.
elim: n => [|n IHn]; first by rewrite ffunE.
by rewrite !mulrS ffunE IHn.
Qed.

Section Sum.

Variables (I : Type) (r : seq I) (P : pred I) (F : I -> {ffun aT -> rT}).

Lemma sum_ffunE x : (\sum_(i <- r | P i) F i) x = \sum_(i <- r | P i) F i x.
Proof. by elim/big_rec2: _ => // [|i _ y _ <-]; rewrite !ffunE. Qed.

Lemma sum_ffun :
  \sum_(i <- r | P i) F i = [ffun x => \sum_(i <- r | P i) F i x].
Proof. by apply/ffunP=> i; rewrite sum_ffunE ffunE. Qed.

End Sum.

End FinFunNmod.

Section FinFunZmod.

Variable (aT : finType) (rT : zmodType).
Implicit Types f g : {ffun aT -> rT}.

Definition ffun_opp f := [ffun a => - f a].

HB.instance Definition _ := hasOpp.Build {ffun aT -> rT} ffun_opp.

Fact ffun_addNr : left_inverse 0 ffun_opp +%R.
Proof. by move=> f; apply/ffunP => a; rewrite !ffunE addNr. Qed.

HB.instance Definition _ := Nmodule_isZmodule.Build {ffun aT -> rT} ffun_addNr.

End FinFunZmod.

Section PairBaseAddMagma.
Variables U V : baseAddMagmaType.

Definition pair_add (a b : U * V) := (a.1 + b.1, a.2 + b.2).

HB.instance Definition _ := hasAdd.Build (U * V)%type pair_add.

End PairBaseAddMagma.

Section PairAddMagma.
Variables U V : addMagmaType.

Fact pair_addrC : commutative (@pair_add U V).
Proof. by move=> a b; congr pair; exact: addrC. Qed.

HB.instance Definition _ :=
  BaseAddMagma_isAddMagma.Build (U * V)%type pair_addrC.

End PairAddMagma.

Section PairAddSemigroup.
Variables U V : addSemigroupType.

Fact pair_addrA : associative (@pair_add U V).
Proof. by move=> [] al ar [] bl br [] cl cr; rewrite /pair_add !addrA. Qed.

HB.instance Definition _ :=
  AddMagma_isAddSemigroup.Build (U * V)%type pair_addrA.

End PairAddSemigroup.

Section PairBaseAddUMagma.
Variables U V : baseAddUMagmaType.

Definition pair_zero : U * V := (0, 0).

HB.instance Definition _ := hasZero.Build (U * V)%type pair_zero.

Fact fst_is_additive : semi_additive (@fst U V). Proof. by []. Qed.
Fact snd_is_additive : semi_additive (@snd U V). Proof. by []. Qed.

HB.instance Definition _ := isSemiAdditive.Build _ _ (@fst U V) fst_is_additive.
HB.instance Definition _ := isSemiAdditive.Build _ _ (@snd U V) snd_is_additive.

End PairBaseAddUMagma.

Section PairAddUMagma.
Variables U V : addUMagmaType.

Fact pair_add0r : left_id (@pair_zero U V) (@pair_add U V).
Proof. by move=> [] al ar; rewrite /pair_add !add0r. Qed.

HB.instance Definition _ :=
  BaseAddUMagma_isAddUMagma.Build (U * V)%type pair_add0r.

End PairAddUMagma.

HB.instance Definition _ (U V : ChoiceBaseAddMagma.type) :=
  BaseAddMagma.on (U * V)%type.
HB.instance Definition _ (U V : ChoiceBaseAddUMagma.type) :=
  BaseAddMagma.on (U * V)%type.

Section PairNmodule.
Variables U V : nmodType.

HB.instance Definition _ := AddSemigroup.on (U * V)%type.

End PairNmodule.

Section PairZmodule.
Variables U V : zmodType.

Definition pair_opp (a : U * V) := (- a.1, - a.2).

HB.instance Definition _ := hasOpp.Build (U * V)%type pair_opp.

Fact pair_addNr : left_inverse 0 pair_opp +%R.
Proof. by move=> [] al ar; rewrite /pair_opp; congr pair; apply/addNr. Qed.

HB.instance Definition _ := Nmodule_isZmodule.Build (U * V)%type pair_addNr.

End PairZmodule.

(* zmodType structure on bool *)
HB.instance Definition _ := isZmodule.Build bool addbA addbC addFb addbb.

(* nmodType structure on nat *)
HB.instance Definition _ := isNmodule.Build nat addnA addnC add0n.

HB.instance Definition _ (V : nmodType) (x : V) :=
  isSemiAdditive.Build nat V (natmul x) (mulr0n x, mulrnDr x).

Lemma natr0E : 0 = 0%N. Proof. by []. Qed.
Lemma natrDE n m : n + m = (n + m)%N. Proof. by []. Qed.
Definition natrE := (natr0E, natrDE).

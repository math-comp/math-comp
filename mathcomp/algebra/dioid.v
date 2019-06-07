From mathcomp
Require Import ssreflect ssrfun ssrbool eqtype choice ssrnat bigop.

(******************************************************************************)
(*  The algebraic structures of semi-rings and dioids, as described in :      *)
(*    Michel Minoux, Michel Gondran.                                          *)
(*    'Graphs, Dioids and Semirings. New Models and Algorithms.'              *)
(*    Springer, 2008                                                          *)
(*                                                                            *)
(* This file defines for each structures (SemiRing, Dioid, etc ...) its type, *)
(* its packers and its cannonical properties:                                 *)
(*                                                                            *)
(*   * SemiRing (non commutative semi-rings):                                 *)
(*          semiRingType == interface type for semi-ring structure            *)
(* SemiRingMixin muldDl muldDr muld0 mul0d == builds the mixin for a SemiRing *)
(*                          from the algebraic properties of its operations.  *)
(*                          The underlying additive operator must have        *)
(*                          a commutative monoid structure while the          *)
(*                          multiplicative operator must have                 *)
(*                          a monoid structure (see bigop.v).                 *)
(*      SemiRingType T m == packs the mixin m to build a SemiRing of type     *)
(*                          semiRingType. The carrier type T must have a      *)
(*                          choiceType cannonical structures.                 *)
(* [semiRingType of T for cT] == T-clone of the semiRingType structure cT: a  *)
(*                          copy of cT where the sort carrier has been        *)
(*                          replaced by cT, and which is therefore            *)
(*                          a semiRingType structure on cT. The sort carrier  *)
(*                          for T must be convertible to cT.                  *)
(*       [semiRing of T] == clone of a canonical semiRing structure on T.     *)
(*                          Similar to the above, except cT is inferred,      *)
(*                          possibly with a syntactically different carrier.  *)
(*                     0 == the zero element (aditive identity)               *)
(*                     1 == the unit element (multiplicative identity)        *)
(*                 x + y == the addition of x and y in a semiRing             *)
(*                 x * y == the multiplication of x and y in a semiRing       *)
(*         addd_closed S <-> collective predicate S is closed under           *)
(*                          finite sums (0 and x + y in S, for x, y in S)     *)
(*         muld_closed S <-> collective predicate S is closed under finite    *)
(*                          multiplication (0 and x + y in S, for x, y in S)  *)
(*     semiring_closed S <-> collective predicate S is closed under finite    *)
(*                          addition and multiplication. This property        *)
(*                          coerces to addd_closed and muld_closed.           *)
(*          AddPred addS == packs addS : addd_closed S into an addPred S      *)
(*                          interface structure associating this property to  *)
(*                          the cannonical pred_key S, i.e the k for wich S   *)
(*                          has a Cannonical keyed_pred k structure.          *)
(*                          (see file ssrbool.v)                              *)
(*          MulPred addS == packs mulS : muld_closed S into an semiRingPred S *)
(*                          interface structure associating this property to  *)
(*                          the cannonical pred_key S                         *)
(*     SemiRingPred mulS == packs mulS : muld_closed S into an semiringPred S *)
(*                          interface structure associating the               *)
(*                          semiring_closed property to the canonical         *)
(*                          pred_key S (see above), wich must already be an   *)
(*                          AddPred.                                          *)
(* [semiringMixin of U by <:] == semiRingType mixin for a subType whose base  *)
(*                          type is a semiRingType and whose predicate's      *)
(*                          cannonical pred_key is a semiRingPred.            *)
(* --> Coq can be made to behave as if all predicate had canonical            *)
(*     semiRingPred key by executing Import DefaultKeying GDioid.DefaultPred  *)
(*     The required addd_closed and muld_closed assumptions will be either    *)
(*     abstracted, resolved or issued as separate proof obligations by the    *)
(*     ssreflect plugin abstraction and Prop-irrelevance functions.           *)
(*                                                                            *)
(*   * Dioid (idempotent semi-ring):                                          *)
(*             dioidType == interface type for dioid structure.               *)
(*     DioidType R addxx == packs addxx into a dioidType; the carrier type R  *)
(*                          must have a semiRingType canonical structure.     *)
(* [dioidType of T for cT] == T-clone of the dioidType structure cT           *)
(*      [dioidType of T] == clone of a canonical semiRing structure on T.     *)
(*                x <= y == the order relation, derived from the addition     *)
(*                          (x <= y when x + y == y)                          *)
(* [dioidMixin of R by <:] == idempotent mixin axiom for R when it is a       *)
(*                          subType of a dioid.                               *)
(*                                                                            *)
(*   * ComSemiRing (multiplication is commutative):                           *)
(*       comSemiRingType == interface type for commutative semi ring          *)
(*                          structure                                         *)
(* ComSemiRingType R mulC == packs mulC into a comSemiRingType; the carrier   *)
(*                          type R must have a semiRingType canonical         *)
(*                          structure.                                        *)
(* ComSemiRingMixin addA add0l addC mulA mul1d mulC muld0 mulDl == builds the *)
(*                          mixin for a SemiRing (i.e non commutative)        *)
(*                          using the commutativity to reduce the number      *)
(*                          of proof obligations.                             *)
(* [comSemiRingType of R for S] == R-clone of the comSemiRingType structure S *)
(* [comSemiRingType of R] == clone of the canonical comSemiRing structure     *)
(*                          on R.                                             *)
(* [comSemiRingMixin of R by <:] == commutativity mixin axiom for R when it   *)
(*                          is a subType of a commutative semi-ring.          *)
(*                                                                            *)
(*  * ComDioid:                                                               *)
(*          comDioidType == interface type for commutative dioid structure    *)
(*   ComDioidType D mulC == packs mulC into a ComDioidType; the carrier type  *)
(*                          D must have a dioidType canonical structure.      *)
(* [comDioidType of T for cT] == T-clone of the comDioid structure cT.        *)
(* [comSemiRingType of T] == clone of the canonical dioid structure on T.     *)
(* [comDioidMixin of R by <:] == commutativity mixin axiom for R when it is a *)
(*                          subType of a commutative dioid.                   *)
(*                                                                            *)
(*   * CompleteDioid (dioid with infinte distributivity):                     *)
(*                   (From GONDRAN-MINOUX définition 6.1.8)                   *)
(*     completeDioidType == interface type for complete Dioid structure       *)
(*              sup{ B } == the infinite operator for dioidtype on set B      *)
(*                          (a function from the carrier type D to Prop).     *)
(*                   top == the greatest element of a complete dioid.         *)
(* completeDioidMixin setAdd_is_lub setAddDl setAddDr == builds a             *)
(*                          completeDioid mixin.                              *)
(* CompleteDioidType T m == packs the mixin m to build a complete dioid       *)
(*                          of type CompleteDioidType. The carrier type T     *)
(*                          must have a dioidType cannonical structure.       *)
(* [completeDioidType of T for cT] == T-clone of the semiRingType structure   *)
(*                          cT.                                               *)
(* [completeDioidType of T] == clone of a canonical semiRing structure on T.  *)
(*      set_add_closed S <-> collective predicate S is closed under infinite  *)
(*                          sums.                                             *)
(*    SetAddPred setAddS == packs set_addS : set_addd_closed S into a         *)
(*                          SetaddPred S interface structure associating      *)
(*                          this property to the cannonical pred_key S.       *)
(* CompleteDioidPred setAddS == packs set_addS : set_addd_closed S into a     *)
(*                          completeDioidPred S interface structure           *)
(*                          associating this property to the cannonical       *)
(*                          SemiRingPred S.                                   *)
(* [completeDioidMixin of U by <:] == completeDioidType mixin for a subType   *)
(*                          whose base type is a dioidType                    *)
(*                                                                            *)
(*   * ComCompleteDioid:                                                      *)
(*  comCompleteDioidType == interface type for complete commutative dioid     *)
(*                          structure                                         *)
(* ComComplteDioidType C mulC == packs mulC into a comCompleteDioidType;      *)
(*                          the carrier type C must have a completeDioidType  *)
(*                          canonical structure.                              *)
(* [comCompleteDioidType of T for cT] == T-clone of the comCompleteDioid      *)
(*                          structure cT.                                     *)
(* [comCompleteDioidType of T] == clone of the canonical comCompleteDioid     *)
(*                          structure on T.                                   *)
(* [comCompleteDioidMixin of U by <:] == comCompleteDioidType mixin for a     *)
(*                          subType whose base type is a comCompleteDioidType *)
(*                                                                            *)
(* The Lemmas about these structures are contained in both the GDioid module  *)
(* and in the submodule GDioid.Theory, which can be imported when unqualified *)
(* access to the theory is needed. The main GDioid module should NOT be       *)
(* imported.                                                                  *)
(*   Notations are defined in scope dioid_scope (delimiter %D).               *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope dioid_scope with D.

Module Import GDioid.

Reserved Notation "+%D" (at level 0).
Reserved Notation "*%D" (at level 0).
Reserved Notation "<=%D" (at level 0).
Reserved Notation "sup%D" (at level 0).

Import Monoid.Theory.

Module SemiRing.

Record mixin_of (D : Type) : Type := Mixin {
  eps : D;
  add : Monoid.com_law eps;
  e : D;
  mul : Monoid.law e;
  _ : left_distributive mul add;
  _ : right_distributive mul add;
  _ : left_zero eps mul;
  _ : right_zero eps mul
}.

Section ClassDef.

Record class_of T := Class { base : Choice.class_of T; mixin : mixin_of T }.
Local Coercion base : class_of >-> Choice.class_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack m :=
  fun bT b & phant_id (Choice.class bT) b => Pack (@Class T b m).

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Choice.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Bind Scope dioid_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Notation semiRingType := type.
Notation SemiRingType T m := (@pack T m _ _ id).
Notation SemiRingMixin := Mixin.
Notation "[ 'semiRingType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'semiRingType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'semiRingType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'semiRingType'  'of'  T ]") : form_scope.

End Exports.

End SemiRing.

Import SemiRing.Exports.

Variable SR : semiRingType.

Definition eps D := SemiRing.eps (SemiRing.class D).
Definition add D := SemiRing.add (SemiRing.class D).

Definition e D := SemiRing.e (SemiRing.class D).
Definition mul D := SemiRing.mul (SemiRing.class D).

Local Notation "0" := (eps _) : dioid_scope.
Local Notation "1" := (@e _) : dioid_scope.
Local Notation "+%D" := (@add _) : dioid_scope.
Local Notation "*%D" := (@mul _) : dioid_scope.
Local Notation "x + y" := (@add _ x y) : dioid_scope.
Local Notation "x * y" := (@mul _ x y) : dioid_scope.

Section SemiRingTheory.

Local Open Scope dioid_scope.
Variable V : semiRingType.

Lemma muldDl : @left_distributive V V *%D +%D.
Proof. by case V => [? [c] []]. Qed.

Lemma muldDr : @right_distributive V V *%D +%D.
Proof. by case V => [? [c] []]. Qed.

Lemma mul0d : left_zero (eps V) *%D.
Proof. by case V => [? [c] []]. Qed.

Lemma muld0 : right_zero (eps V) *%D.
Proof. by case V => [? [c] []]. Qed.

Lemma muldA : @associative V *%D.
Proof. by case V => [ T [c] []] eps ADD e []. Qed.

Lemma adddA : @associative V +%D.
Proof. by case V => [ T [c] []] eps [[]]. Qed.

Lemma adddC : @commutative V V +%D.
Proof. by case V => [ T [c] []] eps [[]]. Qed.

Lemma add0d : @left_id V V 0%D +%D.
Proof. by case V => [ T [c] []] eps [[]]. Qed.

Lemma addd0 : @right_id V V 0 +%D.
Proof. by case V => [ T [c] []] eps [[]]. Qed.

Lemma mul1d : @left_id V V 1 *%D.
Proof. by case V => [ T [c] []] eps ADD e []. Qed.

Lemma muld1 : @right_id V V 1 *%D.
Proof. by case V => [ T [c] []] eps ADD e []. Qed.

Section ClosedPredicates.

Variable S : predPredType V.
 
Definition addd_closed := 0 \in S /\ {in S &, forall u v, u + v \in S}.
Definition muld_closed := 1 \in S /\ {in S &, forall u v, u * v \in S}.
Definition semiring_closed := addd_closed /\ muld_closed.

Lemma semiring_closedA : semiring_closed -> addd_closed.
Proof. case=> [Sa _]; apply Sa. Qed.
Lemma semiring_closedM : semiring_closed -> muld_closed.
Proof. case=> [_ Sm]; apply Sm. Qed.

End ClosedPredicates.

End SemiRingTheory.

Module ComSemiRing.

Definition SemiRingMixin
           D eps (add : D -> D -> D) addA add0l (addC : commutative add)
           e (mul : D -> D -> D) mulA mul1l (mulC : commutative mul)
           mul0d (addDl : left_distributive mul add) :=
  let addL :=
    @Monoid.ComLaw _ _
      (Monoid.Law addA add0l (Monoid.mulC_id addC add0l)) addC in
  let mulL :=
    @Monoid.ComLaw _ _
      (Monoid.Law mulA mul1l (Monoid.mulC_id mulC mul1l)) mulC in
  let mul0r := Monoid.mulC_zero mulC mul0d in
  let addDr := Monoid.mulC_dist mulC addDl in
  @SemiRing.Mixin D eps addL e mulL addDl addDr mul0d mul0r.

Section ClassDef.

Record class_of D :=
  Class {base : SemiRing.class_of D; mixin : commutative (SemiRing.mul base)}.
Local Coercion base : class_of >-> SemiRing.class_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variable (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack mul0 (m0 : @commutative T T mul0) :=
  fun bT b & phant_id (SemiRing.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m).

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition semiRingType := @SemiRing.Pack cT xclass.

End ClassDef.

Module Exports.
Coercion base : class_of >-> SemiRing.class_of.
Arguments mixin [D].
Coercion mixin : class_of >-> commutative.
Coercion sort : type >-> Sortclass.
Bind Scope semiring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion semiRingType : type >-> SemiRing.type.
Canonical semiRingType.
Notation comSemiRingType := type.
Notation ComSemiRingType T m := (@pack T _ m _ _ id _ id).
Notation ComSemiRingMixin := SemiRingMixin.
Notation "[ 'comSemiRingType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'comSemiRingType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'comSemiRingType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'comSemiRingType'  'of'  T ]") : form_scope.
End Exports.

End ComSemiRing.
Import ComSemiRing.Exports.

Section ComSemiRingTheory.

Variable V : comSemiRingType.

Lemma muldC : commutative (@mul V).
Proof. by case V => T []. Qed.

Lemma muldCA : left_commutative (@mul V).
Proof. by move=> x y z; rewrite muldC -muldA (muldC z). Qed.

Lemma muldAC : right_commutative (@mul V).
Proof. by move=> x y z; rewrite -muldA (muldC y) -muldA. Qed.

Lemma muldACA : interchange (@mul V) (mul V).
Proof. by move => a b c d; rewrite -muldAC muldA (muldC b d) muldA. Qed.

End ComSemiRingTheory.

Module Dioid.

Section ClassDef.

Record class_of (SR : Type) : Type :=
  Class {base : SemiRing.class_of SR;
         mixin : idempotent (SemiRing.add base)}.
Local Coercion base : class_of >-> SemiRing.class_of.
Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variable (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack add0 (a0 : @idempotent T add0) :=
  fun bT b & phant_id (SemiRing.class bT) b =>
  fun    a & phant_id a0 a => Pack (@Class T b a).

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition semiRingType := @SemiRing.Pack cT xclass.

End ClassDef.

Module Exports.
Coercion base : class_of >-> SemiRing.class_of.
Arguments mixin [SR].
Coercion mixin : class_of >-> idempotent.
Coercion sort : type >-> Sortclass.
Bind Scope semiRing_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion semiRingType : type >-> SemiRing.type.
Canonical semiRingType.
Notation dioidType := type.
Notation DioidType T a := (@pack T _ a _ _ id _ id).
Notation "[ 'dioidType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'dioidType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'dioidType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'dioidType'  'of'  T ]") : form_scope.
End Exports.

End Dioid.

Import Dioid.Exports.

Definition led (D : dioidType)(a b : D) := @add D a b == b.

Local Notation "x <= y" := (@led _ x y) : dioid_scope.
Local Notation "<=%D" := (@led _ ) : dioid_scope.

Local Open Scope dioid_scope.

Section DioidTheory.

Variable (D : dioidType).

Lemma adddd : @idempotent D (add D).
Proof. by case D => [c [T]]. Qed.

Lemma led_0_1 : @led D 0 1.
Proof. by apply /eqP; rewrite add0d. Qed.

Lemma led_reflexive : @reflexive D <=%D.
Proof. by move=> a; rewrite /led; rewrite adddd. Qed.

Lemma led_trans : @transitive D <=%D.
Proof.
move=> a b c. rewrite /led => /eqP A /eqP <-. rewrite -{2}A.
apply /eqP /adddA.
Qed.

Lemma led_antisym : @antisymmetric D <=%D.
Proof.
by move=> a b /andP []; rewrite /le => /eqP ? /eqP; rewrite adddC => <-.
Qed.

Lemma led_add2r (c : D) : {homo +%D^~ c : a b / a <= b }.
Proof.
move => a b /eqP H; apply /eqP.
by rewrite (adddC b) adddA -(adddA a) adddd -adddA (adddC c) adddA H.
Qed.

Lemma led_add2l (c : D) : {homo +%D c : a b / a <= b }.
Proof. move=> a b. rewrite !(adddC c); apply led_add2r. Qed.

Lemma led_add (a b c d : D) : a <= c -> b <= d -> (a + b) <= (c + d).
Proof. by move => Hac Hbd; apply (led_trans (led_add2r _ Hac)), led_add2l. Qed.

Lemma led_mul2l (c : D): {homo *%D c : a b / a <= b }.
Proof. by move => a b /eqP Hb; rewrite /led -muldDr Hb. Qed.

Lemma led_mul2r (c : D): {homo *%D^~ c : a b / a <= b }.
Proof. by move=> a b /eqP Hb; rewrite /led -muldDl Hb. Qed.

Lemma led_mul (a b c d : D) : a <= c -> b <= d -> (a * b) <= (c * d).
Proof. by move => Hac Hbd; apply (led_trans (led_mul2r _ Hac)), led_mul2l. Qed.

Lemma led_addl (a b : D) : a <= b + a.
Proof. by apply /eqP; rewrite adddC -adddA adddd. Qed.

Lemma led_addr (a b : D) : a <= a + b.
Proof. by apply /eqP; rewrite adddA adddd. Qed.

Lemma led_add_eqv (a b c : D) :  b + c <= a <-> (b <= a /\ c <= a).
Proof.
split.
{ move=>Ha.
  split; [by apply: (led_trans _ Ha); apply /eqP; rewrite adddA adddd|].
  by apply: (led_trans _ Ha); apply /eqP ; rewrite -adddC -(adddA b) adddd.
}
move=>[/eqP Hb /eqP Hc].
rewrite -Hb -Hc; apply /eqP.
by rewrite (adddC b) adddA -(adddA c) adddd (adddC c) adddA -(adddA b) adddd adddA.
Qed.

End DioidTheory.

Module ComDioid.

Section ClassDef.

Record class_of D :=
  Class {base : Dioid.class_of D; mixin : commutative (SemiRing.mul base)}.
Local Coercion base : class_of >-> Dioid.class_of.
Definition base2 D m := ComSemiRing.Class (@mixin D m).
Local Coercion base2 : class_of >-> ComSemiRing.class_of.
Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variable (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack mul0 (m0 : @commutative T T mul0) :=
  fun bT b & phant_id (Dioid.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m).

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition semiRingType := @SemiRing.Pack cT xclass.
Definition dioidType := @Dioid.Pack cT xclass.
Definition comSemiRingType := @ComSemiRing.Pack cT xclass.
Definition com_dioidType := @ComSemiRing.Pack dioidType xclass.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Dioid.class_of.
Arguments mixin [D].
Coercion mixin : class_of >-> commutative.
Coercion base2 : class_of >-> ComSemiRing.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope dioid_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion semiRingType : type >-> SemiRing.type.
Canonical semiRingType.
Coercion dioidType : type >-> Dioid.type.
Canonical dioidType.
Coercion comSemiRingType : type >-> ComSemiRing.type.
Canonical comSemiRingType.
Canonical com_dioidType.
Notation comDioidType := type.
Notation ComDioidType T m := (@pack T _ m _ _ id _ id).
Notation "[ 'comDioidType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'comDioidType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'comDioidType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'comDioidType'  'of'  T ]") : form_scope.
End Exports.

End ComDioid.
Import ComDioid.Exports.

Definition is_upper_bound (D : dioidType) B l := forall x : D, B x -> x <= l.
Definition is_lub (D : dioidType)(B : D -> Prop) l :=
  is_upper_bound B l /\ forall y, is_upper_bound B y -> l <= y.

Module CompleteDioid.

Record mixin_of (D : dioidType): Type := Mixin {
  set_add : (D -> Prop) -> D;
  _ : forall B, is_lub B (set_add B);
  _ : forall a B, a * (set_add B) = set_add (fun y => exists x, B x /\ y = a * x);
  _ : forall a B, (set_add B) * a = set_add (fun y => exists x, B x /\ y = x * a)
}.

Section ClassDef.

Record class_of D :=
  Class {base : Dioid.class_of D;
         mixin : mixin_of (Dioid.Pack base)}.

Local Coercion base : class_of >-> Dioid.class_of.
Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variable (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack b0 (m0 : mixin_of (@Dioid.Pack T b0)) :=
  fun bT b & phant_id (Dioid.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m).

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition semiRingType := @SemiRing.Pack cT xclass.
Definition dioidType := @Dioid.Pack cT xclass.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Dioid.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Bind Scope completeDioid_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion semiRingType : type >-> SemiRing.type.
Canonical semiRingType.
Coercion dioidType : type >-> Dioid.type.
Canonical dioidType.
Notation completeDioidType := type.
Notation CompleteDioidType T m := (@pack T _ m _ _ id _ id).
Notation CompleteDioidMixin := Mixin.
Notation "[ 'completeDioidType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'completeDioidType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'completeDioidType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'completeDioidType'  'of'  T ]") : form_scope.
End Exports.

End CompleteDioid.

Import CompleteDioid.Exports.

Section CompleteDioidTheory.

Definition set_add C := CompleteDioid.set_add (CompleteDioid.class C).

Local Notation "sup{ B }" := (set_add B) : dioid_scope.

Variables (C : completeDioidType).

Lemma set_add_is_lub : forall B, @is_lub C B sup{B}.
Proof. by case C => [? [? []]]. Qed.

Lemma set_add_unique lub' B : @is_lub C B (lub' B) -> lub' B = sup{B}.
Proof.
move=> Hlub'; apply /led_antisym /andP; split.
{ by apply Hlub' => ? ?; apply set_add_is_lub. }
by apply set_add_is_lub => ? ?; apply Hlub'.
Qed.

Lemma set_add_empty : sup{fun=> False} = (eps C).
Proof.
by apply /led_antisym /andP; split; [apply set_add_is_lub|apply /eqP /add0d].
Qed.

Lemma set_add_rem a (B : C -> Prop) : sup{fun x => x = a \/ B x} = a + sup{B}.
Proof.
apply /led_antisym /andP; split.
{ apply set_add_is_lub => x [->|Hx]; [by apply led_addr|].
  by refine (led_trans _ (led_addl _ _)); apply set_add_is_lub. }
rewrite led_add_eqv; split; [by apply set_add_is_lub; left|].
by apply (proj2 (set_add_is_lub B)) => ? ?; apply set_add_is_lub; right.
Qed.

Lemma set_add_eq (B B' : C -> Prop) :
  (forall x, B x <-> B' x) -> set_add B = set_add B'.
Proof.
by move=> H; apply /led_antisym /andP; split;
apply (proj2 (set_add_is_lub _)) => x Hx; apply set_add_is_lub, H.
Qed.

Lemma set_add_singleton (a : C) : sup{fun x => x = a} = a.
Proof.
rewrite (set_add_eq (B':=fun x => x = a \/ False)).
{ by rewrite set_add_rem set_add_empty addd0. }
by move=> x; split=> [->|[]]; [left| |].
Qed.

Lemma set_addDl (a : C) (B : C -> Prop) :
  a * sup{B} = sup{fun y => exists x, B x /\ y = a * x}.
Proof. by move : B a; case C => [? [? []]]. Qed.

Lemma set_addDr (a : C) (B : C -> Prop) :
  sup{B} * a = sup{fun y => exists x, B x /\ y = x * a}.
Proof. by move : B a; case C => [? [?[]]]. Qed.

Lemma set_add_0 (F : nat -> C) :
  sup{fun y=> exists i : nat, (i <= 0)%N /\ y = F i} = F 0%N.
Proof.
rewrite -(addd0 (F 0%N)) /=.
rewrite -set_add_empty => //=.
rewrite -set_add_rem; apply set_add_eq => x; split.
{ move=> [i [Hi Hi']].
  by left; move : Hi Hi'; case i.
}
move=> [Hx | Fa]; by exists 0%N.
Qed.

Lemma set_add_S (F : nat -> C) k :
    sup{fun y => exists i, (i <= k.+1)%N /\ y = F i} =
    sup{fun y => exists i, (i <= k)%N /\ y = F i} + F k.+1.
Proof.
rewrite adddC -set_add_rem.
apply set_add_eq => x. split.
{ move=> [i [Hi ->]]; move: Hi.
  by rewrite leq_eqVlt => /orP [/eqP ->|Hi]; [left|right; exists i].
}
move=> [Hx | [i [Hi Hi']]]; [by exists k.+1| exists i].
split => //=.
by apply leqW.
Qed.

Lemma led_set_add (B : C -> Prop) x : B x -> x <= sup{B}.
Proof.
move=> Bx; apply /eqP; rewrite -set_add_rem.
by apply set_add_eq => y; split; [move=>[->|]| move=>By; right].
Qed.

Lemma set_add_led (F : nat -> C) k :
  sup{fun y => exists i, (i<=k)%N /\ y = F i}<=
  sup{fun y => exists i, y = F i}.
Proof.
elim: k => /= [| k /eqP Ihk].
{ rewrite set_add_0 /led -set_add_rem.
  apply /eqP /set_add_eq => x; split .
  { by move=> [-> | //]; exists 0%N. }
  by move => ?; right.
}
rewrite set_add_S /le ; apply /eqP.
rewrite (adddC _ (F k.+1)) -adddA Ihk -set_add_rem.
apply set_add_eq => x; split; [by move=> [-> | //]; exists k.+1|].
by move => ?; right.
Qed.

Lemma set_add_lim_nat (F : nat -> C) l:
  (forall k, sup{fun y => exists i, (i <= k)%N /\ y = F i} <= l) ->
  sup{fun y => exists i, y = F i} <= l.
Proof.
move=> H. apply set_add_is_lub => _ [i ->].
move: (H i).
apply led_trans.
rewrite (set_add_eq _ (B':= fun y => y= F i \/ (exists j, (j<=i)%N /\ y = F j)));
  [by rewrite set_add_rem; apply led_addr|].
move=> x; split.
{ by move=>[j [Hj ->]]; right; exists j. }
by move=> [->|//]; exists i.
Qed.

Lemma set_add_led_set (F F' : nat -> C):
  (forall k, sup{fun x => exists i, (i<= k)%N /\ x = F i} <=
             sup{ fun x => exists i, (i<= k)%N /\ x = F' i}) ->
  sup{fun x => exists i, x = F i} <=
  sup{fun x => exists i, x = F' i}.
Proof.
move=> Hyp; apply set_add_lim_nat => k.
apply (led_trans (Hyp k)), set_add_led.
Qed.

Lemma set_add_eq_set (F F' : nat -> C):
  (forall k, sup{fun x => exists i, (i<= k)%N /\ x = F i}
             = sup{fun x => exists i, (i<= k)%N /\ x = F' i}) ->
  sup{fun x => exists i, x = F i} = sup{fun x => exists i, x = F' i}.
Proof.
move=> Hyp; apply /led_antisym /andP; split;
apply set_add_led_set => k; rewrite Hyp; apply led_reflexive.
Qed.

Definition set_add_lim B := proj2 (set_add_is_lub B).

Definition top : C := sup{ fun _ : C => True }.

Lemma add_dtop : right_zero top (add C).
Proof.
by move=> x; rewrite -set_add_rem; apply set_add_eq => y; split=> _; [|right].
Qed.

Lemma add_topd : left_zero top (add C).
Proof. by move=> x; rewrite adddC add_dtop. Qed.

Lemma led_top x : x <= top.
Proof. by rewrite /led add_dtop. Qed.

Section ClosedPredicates.

Variable S : predPredType C.

Definition set_addd_closed :=
  forall (B : C -> Prop), (forall x, B x -> x \in S) -> sup{ B } \in S.
Definition completedioid_closed := semiring_closed S /\ set_addd_closed.

Lemma completedioid_closedA : completedioid_closed -> addd_closed S.
Proof. case=> [Sa _]; apply Sa. Qed.
Lemma completedioid_closedM : completedioid_closed -> muld_closed S.
Proof. case=> [Sm _]; apply Sm. Qed.
Lemma completedioid_closedS : completedioid_closed -> set_addd_closed.
Proof. case=> [_ SS]; apply SS. Qed.

End ClosedPredicates.

End CompleteDioidTheory.

Module ComCompleteDioid.

Section ClassDef.

Record class_of D :=
  Class {base : CompleteDioid.class_of D; mixin : commutative (SemiRing.mul base)}.
Local Coercion base : class_of >-> CompleteDioid.class_of.
Definition base2 D m := ComDioid.Class (@mixin D m).
Local Coercion base2 : class_of >-> ComDioid.class_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variable (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack mul0 (m0 : @commutative T T mul0) :=
  fun bT b & phant_id (CompleteDioid.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m).

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition semiRingType := @SemiRing.Pack cT xclass.
Definition dioidType := @Dioid.Pack cT xclass.
Definition comSemiRingType := @ComSemiRing.Pack cT xclass.
Definition comDioidType := @ComDioid.Pack cT xclass.
Definition completeDioidType := @CompleteDioid.Pack cT xclass.
Definition com_complete_dioidType := @ComDioid.Pack completeDioidType xclass.
Definition com_semi_ring_complete_dioidType := @ComSemiRing.Pack completeDioidType xclass.

End ClassDef.

Module Exports.
Coercion base : class_of >-> CompleteDioid.class_of.
Arguments mixin [D].
Coercion mixin : class_of >-> commutative.
Coercion base2 : class_of >-> ComDioid.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope dioid_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion semiRingType : type >-> SemiRing.type.
Canonical semiRingType.
Coercion dioidType : type >-> Dioid.type.
Canonical dioidType.
Coercion comSemiRingType : type >-> ComSemiRing.type.
Canonical comSemiRingType.
Coercion comDioidType : type >-> ComDioid.type.
Canonical comDioidType.
Coercion completeDioidType : type >-> CompleteDioid.type.
Canonical completeDioidType.
Canonical com_complete_dioidType.
Canonical com_semi_ring_complete_dioidType.
Notation comCompleteDioidType := type.
Notation ComCompleteDioidType T m := (@pack T _ m _ _ id _ id).
Notation "[ 'comCompleteDioidType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'comCompleteDioidType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'comCompleteDioidType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'comCompleteDioidType'  'of'  T ]") : form_scope.
End Exports.

End ComCompleteDioid.
Import ComCompleteDioid.Exports.

(* Interface structures for algebraically closed predicates. *)
Module Pred.

Structure add V S := Add {add_key : pred_key S; _ : @addd_closed V S}.
Structure mul R S := Mul {mul_key : pred_key S; _ : @muld_closed R S}.
Structure set_add C S := SetAdd {set_add_key : pred_key S; _ : @set_addd_closed C S}.
Structure semiring R S := SemiRing { semiring_add : add S; _ : @muld_closed R S }.
Structure completedioid C S :=
  CompleteDioid { completedioid_semiring : semiring S; _ : @set_addd_closed C S }.

Section Subtyping.

Ltac done := case=> *; assumption.
Fact semiring_mulr R S : @semiring R S -> muld_closed S. Proof. by []. Qed.
Fact completedioid_set_addd_closed R S : @completedioid R S -> set_addd_closed S.
Proof. by []. Qed.

Definition semiring_mul R S (ringS : @semiring R S) :=
  Mul (add_key (semiring_add ringS)) (semiring_mulr ringS).

Definition completedioid_set_add C S (dioidS : @completedioid C S) :=
  SetAdd (add_key (semiring_add (completedioid_semiring dioidS)))
         (completedioid_set_addd_closed dioidS).

End Subtyping.

Section Extensionality.
(* This could be avoided by exploiting the Coq 8.4 eta-convertibility.        *)

Lemma add_ext (U : semiRingType) S k (kS : @keyed_pred U S k) :
  addd_closed kS -> addd_closed S.
Proof.
by case=> S0 addS; split=> [|x y]; rewrite -!(keyed_predE kS) //; apply: addS.
Qed.

Lemma mul_ext (R : semiRingType) S k (kS : @keyed_pred R S k) :
  muld_closed kS -> muld_closed S.
Proof.
by case=> S1 mulS; split=> [|x y]; rewrite -!(keyed_predE kS) //; apply: mulS.
Qed.

Lemma set_add_ext (R : completeDioidType) S k (kS : @keyed_pred R S k) :
  set_addd_closed kS -> set_addd_closed S.
Proof.
move=> set_addS ? HB; rewrite -!(keyed_predE kS).
by apply set_addS => ? ?; rewrite keyed_predE; apply HB.
Qed.

End Extensionality.

Module Default.

Definition add V S addS := @Add V S (DefaultPredKey S) addS.
Definition mul V S mulS := @Mul V S (DefaultPredKey S) mulS.
Definition set_add V S set_addS := @SetAdd V S (DefaultPredKey S) set_addS.
Definition semiring R S addS mulS := @SemiRing R S (add addS) mulS.
Definition completedioid C S addS mulS set_addS :=
  @CompleteDioid C S (semiring addS mulS) set_addS.

End Default.

Module Exports.

Notation addd_closed := addd_closed.
Notation muld_closed := muld_closed.
Notation semiring_closed := semiring_closed.
Notation completedioid_closed := completedioid_closed.

Coercion semiring_closedA : semiring_closed >-> addd_closed.
Coercion semiring_closedM : semiring_closed >-> muld_closed.
Coercion completedioid_closedA : completedioid_closed >-> addd_closed.
Coercion completedioid_closedM : completedioid_closed >-> muld_closed.
Coercion completedioid_closedS : completedioid_closed >-> set_addd_closed.
Coercion add_key : add >-> pred_key.
Coercion mul_key : mul >-> pred_key.
Coercion set_add_key : set_add >-> pred_key.
Coercion semiring_add : semiring >-> add.
Coercion semiring_mul : semiring >-> mul.
Canonical semiring_mul.
Coercion completedioid_semiring : completedioid >-> semiring.
Coercion completedioid_set_add : completedioid >-> set_add.
Canonical completedioid_set_add.

Notation addPred := add.
Notation mulPred := mul.
Notation semiringPred := semiring.
Notation set_addPred := set_add.
Notation completedioidPred := completedioid.

Definition AddPred U S k kS DkS := Add k (@add_ext U S k kS DkS).
Definition MulPred R S k kS MkS := Mul k (@mul_ext R S k kS MkS).
Definition SemiRingPred R S k kS MkS := SemiRing k (@mul_ext R S k kS MkS).
Definition SetAddPred C S k kS SkS := SetAdd k (@set_add_ext C S k kS SkS).
Definition CompleteDioidPred C S k kS SkS :=
  CompleteDioid k (@set_add_ext C S k kS SkS).

End Exports.

End Pred.
Import Pred.Exports.

Module DefaultPred.

Canonical Pred.Default.add.
Canonical Pred.Default.mul.
Canonical Pred.Default.semiring.
Canonical Pred.Default.set_add.
Canonical Pred.Default.completedioid.

End DefaultPred.

Section SemiRingPred.

Variables (V : semiRingType) (S : predPredType V).

Section Add.

Variables (addS : addPred S) (kS : keyed_pred addS).

Lemma rpred0D : addd_closed kS.
Proof. split=> [|x y]; rewrite !keyed_predE; case: addS=> _ [_]//; apply. Qed.

Lemma rpred0 : (eps V) \in kS.
Proof. by case: rpred0D. Qed.

Lemma rpredD : {in kS &, forall u v, (@add V u v) \in kS}.
Proof. by case: rpred0D. Qed.

End Add.

Section Mul.

Variables (mulS : mulPred S) (kS : keyed_pred mulS).

Lemma rpred1M : muld_closed kS.
Proof.
by split=> [|x y]; rewrite !keyed_predE; case: mulS => _ [_] //; apply.
Qed.

Lemma rpred1 : (e V) \in kS.
Proof. by case: rpred1M. Qed.

Lemma rpredM : {in kS &, forall u v, u * v \in kS}.
Proof. by case: rpred1M. Qed.

End Mul.

End SemiRingPred.

Section CompleteDioidPred.

Variables (C : completeDioidType) (S : predPredType C).

Section SetAdd.

Variables (set_addS : set_addPred S) (kS : keyed_pred set_addS).

Lemma rpredS :
  forall (B : C -> Prop), (forall x, B x -> x \in kS) -> @set_add C B \in kS.
Proof.
move=> B HB; rewrite !keyed_predE.
move: set_addS kS => [k S' kS']; apply (S' B) => x Hx.
by move: (HB x); rewrite !keyed_predE; apply.
Qed.

End SetAdd.

End CompleteDioidPred.

Module SubType.

Section SemiRing.

Variables (V : semiRingType) (S : predPredType V).
Variables (subS : semiringPred S) (kS : keyed_pred subS).
Variable U : subType (mem kS).

Let inU v Sv : U := Sub v Sv.
Let zeroU := inU (rpred0 kS).
Let oneU := inU (rpred1 kS).
Let addU (u1 u2 : U) := inU (rpredD (valP u1) (valP u2)).
Let mulU (u1 u2 : U) := inU (rpredM (valP u1) (valP u2)).

Fact adddA : associative addU.
Proof. by move=> a b c; apply val_inj; rewrite !SubK adddA. Qed.

Fact add0d : left_id zeroU addU.
Proof. by move=> a; apply val_inj; rewrite !SubK add0d. Qed.

Fact addd0 : right_id zeroU addU.
Proof. by move=> a; apply val_inj; rewrite !SubK addd0. Qed.

Fact adddC : commutative addU.
Proof. by move=> a b; apply val_inj; rewrite !SubK adddC. Qed.

Fact muldA : associative mulU.
Proof. by move=> a b c; apply val_inj; rewrite !SubK muldA. Qed.

Fact mul1d : left_id oneU mulU.
Proof. by move=> a; apply val_inj; rewrite !SubK mul1d. Qed.

Fact muld1 : right_id oneU mulU.
Proof. by move=> a; apply val_inj; rewrite !SubK muld1. Qed.

Fact muldDl : @left_distributive U U mulU addU.
Proof. by move=> a b c; apply val_inj; rewrite !SubK muldDl. Qed.

Fact muldDr : right_distributive mulU addU.
Proof. by move=> a b c; apply val_inj; rewrite !SubK muldDr. Qed.

Lemma mul0d : left_zero zeroU mulU.
Proof. by move=> a; apply val_inj; rewrite !SubK mul0d. Qed.

Lemma muld0 : right_zero zeroU mulU.
Proof. by move=> a; apply val_inj; rewrite !SubK muld0. Qed.

Definition semiRingMixin of phant U :=
  let addLaw := @Monoid.ComLaw U zeroU (Monoid.Law adddA add0d addd0) adddC in
  let mulLaw := Monoid.Law muldA mul1d muld1 in
  @SemiRing.Mixin _ zeroU addLaw oneU mulLaw muldDl muldDr mul0d muld0.

End SemiRing.

Lemma comSemiRingMixin (R : comSemiRingType) (T : semiRingType) (f : T -> R) :
phant T -> injective f -> {morph f : x y / x * y} -> commutative (@mul T).
Proof. by move=> _ inj_f fM x y; apply: inj_f; rewrite !fM muldC. Qed.

Lemma dioidMixin (R : dioidType) (T : semiRingType) (f : T -> R) :
phant T -> injective f -> {morph f : x y / x + y} -> idempotent (@add T).
Proof. by move=> _ inj_f fM x; apply: inj_f; rewrite !fM adddd. Qed.

Lemma comDioidMixin (R : comDioidType) (T : dioidType) (f : T -> R) :
phant T -> injective f -> {morph f : x y / x * y} -> commutative (@mul T).
Proof. by move=> _ inj_f fM x y; apply: inj_f; rewrite !fM muldC. Qed.

Section CompleteDioid.

Definition cast_dioidType (D : dioidType) U (DeqU : D = U :> Type) :=
  let cast rD := let: erefl in _ = U := DeqU return Dioid.class_of U in rD in
  Dioid.Pack (cast (Dioid.class D)).

Variables (C : completeDioidType) (S : predPredType C).
Variables (subS : completedioidPred S) (kS : keyed_pred subS).

Variables (U : subType (mem kS)) (D : dioidType) (DeqU : D = U :> Type).

Let U' := cast_dioidType DeqU.
Let inU' v Sv : U' := Sub v Sv.
Let set_addU' (B : U' -> Prop) :=
  inU' (rpredS (B:=fun x : C => x \in kS /\ B (insubd (eps U') x))
               (fun x Hx => proj1 Hx)).

Hypothesis val0 : val (eps U') = eps C.
Hypothesis valA : {morph (val : U' -> C) : x y / x + y}.
Hypothesis valM : {morph (val : U' -> C) : x y / x * y}.

Fact set_add_empty : set_addU' (fun=> False) = eps U'.
Proof.
apply val_inj; rewrite !SubK.
rewrite (set_add_eq (B':=fun=>False)) ?set_add_empty ?val0 // => x.
by split=> [[]|].
Qed.

Fact set_add_rem (a : U') B : set_addU' (fun x => x = a \/ B x) = a + (set_addU' B).
Proof.
apply val_inj; rewrite !SubK valA SubK -set_add_rem.
apply set_add_eq => x; split.
{ by move=> [Hx [<-|H]]; [left; rewrite insubdK|right]. }
by move=> [->|[H H']]; split; [apply valP|left; rewrite valKd| |right].
Qed.

Fact set_add_eq B B' : (forall x, B x <-> B' x) -> set_addU' B = set_addU' B'.
Proof.
move => H.
apply val_inj; rewrite !SubK.
apply set_add_eq => x.
by split; move=> [H' H'']; split=> [//|]; [rewrite -H| rewrite H].
Qed.

Fact set_add_lim (B : U' -> Prop) (l : U') :
  (forall x, B x -> x <= l) -> (set_addU' B) <= l.
Proof.
move=> H; apply /eqP /val_inj; rewrite valA !SubK.
apply /eqP /set_add_lim => x [H' H'']; apply /eqP.
rewrite -(SubK U H') -valA; apply /f_equal /eqP /H.
by move: H''; rewrite /insubd insubT.
Qed.

Fact set_addDl (a : U') B :
  a * (set_addU' B) = set_addU' (fun y => exists x, B x /\ y = a * x).
Proof.
apply val_inj; rewrite valM !SubK set_addDl.
apply GDioid.set_add_eq => x; split.
{ move=> [y [[Hy Hy'] ->]].
  split; [by rewrite -(SubK U Hy) -valM; apply valP|].
  exists (insubd (eps U') y); split=> [//|].
  apply val_inj; rewrite valM insubdK ?insubdK //.
  by rewrite -(SubK U Hy) -valM; apply valP. }
move=> [Hx [y [Hy Hy']]].
exists (val y); split; [split|]; [by apply valP|by rewrite valKd|].
by move: Hy'; rewrite -(SubK U Hx) valKd => ->; rewrite valM.
Qed.

Fact set_addDr a B :
  (set_addU' B) * a = set_addU' (fun y => exists x, B x /\ y = x * a).
Proof.
apply val_inj; rewrite valM !SubK set_addDr.
apply GDioid.set_add_eq => x; split.
{ move=> [y [[Hy Hy'] ->]].
  split; [by rewrite -(SubK U Hy) -valM; apply valP|].
  exists (insubd (eps U') y); split=> [//|].
  apply val_inj; rewrite valM insubdK ?insubdK //.
  by rewrite -(SubK U Hy) -valM; apply valP. }
move=> [Hx [y [Hy Hy']]].
exists (val y); split; [split|]; [by apply valP|by rewrite valKd|].
by move: Hy'; rewrite -(SubK U Hx) valKd => ->; rewrite valM.
Qed.

Fact is_lubU : forall B : U' -> Prop, is_lub B (set_addU' B).
Proof.
move=> B; split.
{ move=> x Hx. apply /eqP.
  rewrite -set_add_rem. apply set_add_eq => y.
  by split; [move=> [-> | H]| move=> hB; right].
}
move=> y. rewrite /is_upper_bound => Hy. 
by apply set_add_lim.
Qed.

Definition completeDioidMixin of phant U' :=
  @CompleteDioid.Mixin U' set_addU' is_lubU set_addDl set_addDr.

End CompleteDioid.

Lemma comCompleteDioidMixin (R : comCompleteDioidType) (T : completeDioidType)
      (f : T -> R) :
phant T -> injective f -> {morph f : x y / x * y} -> commutative (@mul T).
Proof. by move=> _ inj_f fM x y; apply: inj_f; rewrite !fM muldC. Qed.

Module Exports.

Notation "[ 'semiRingMixin' 'of' U 'by' <: ]" := (semiRingMixin (Phant U))
  (at level 0, format "[ 'semiRingMixin' 'of' U 'by' <: ]") : form_scope.

Notation "[ 'comSemiRingMixin' 'of' R 'by' <: ]" :=
  (comSemiRingMixin (Phant R) val_inj (rrefl _))
  (at level 0, format "[ 'comSemiRingMixin' 'of' R 'by' <: ]") : form_scope.

Notation "[ 'dioidMixin' 'of' R 'by' <: ]" :=
  (dioidMixin (Phant R) val_inj (rrefl _))
  (at level 0, format "[ 'dioidMixin' 'of' R 'by' <: ]") : form_scope.

Notation "[ 'comDioidMixin' 'of' R 'by' <: ]" :=
  (comDioidMixin (Phant R) val_inj (rrefl _))
  (at level 0, format "[ 'comDioidMixin' 'of' R 'by' <: ]") : form_scope.

Notation "[ 'completeDioidMixin' 'of' R 'by' <: ]" :=
  (@completeDioidMixin _ _ _ _ _ _ (@erefl Type R%type) (rrefl _) (rrefl _) (Phant R))
(at level 0, format "[ 'completeDioidMixin' 'of' R 'by' <: ]") : form_scope.

Notation "[ 'comCompleteDioidMixin' 'of' R 'by' <: ]" :=
  (comCompleteDioidMixin (Phant R) val_inj (rrefl _))
  (at level 0, format "[ 'comCompleteDioidMixin' 'of' R 'by' <: ]") : form_scope.

End Exports.

End SubType.

Module Theory.

Definition muldDl := muldDl.
Definition muldDr := muldDr.
Definition mul0d := mul0d.
Definition muld0 := muld0.
Definition muldA := muldA.
Definition adddA := adddA.
Definition adddC := adddC.
Definition add0d := add0d.
Definition addd0 := addd0.
Definition mul1d := mul1d.
Definition muld1 := muld1.
Definition muldC := muldC.
Definition muldCA := muldCA.
Definition muldAC := muldAC.
Definition muldACA := muldACA.
Definition adddd := adddd.
Definition led_reflexive :=  led_reflexive.
Definition led_trans := led_trans.
Definition led_antisym := led_antisym.
Definition led_add2r := led_add2r.
Definition led_add2l := led_add2l.
Definition led_add := led_add.
Definition led_mul2l := led_mul2l.
Definition led_mul2r := led_mul2r.
Definition led_mul := led_mul.
Definition led_addl := led_addl.
Definition led_addr := led_addr.
Definition led_add_eqv := led_add_eqv.
Definition led:= led.
Definition e := e.
Definition set_add_empty := set_add_empty.
Definition set_add_rem := set_add_rem.
Definition set_add_eq := set_add_eq.
Definition add_dtop := add_dtop.
Definition add_topd := add_topd.
Definition led_top := led_top.
Definition set_add_lim := set_add_lim.
Definition set_addDl := set_addDl.
Definition set_addDr := set_addDr.
Definition set_add_is_lub := set_add_is_lub.
Definition set_add_unique := set_add_unique.
Definition set_add_singleton := set_add_singleton.
Definition led_set_add := led_set_add.
Definition set_add_led := set_add_led.
Definition set_add_led_set := set_add_led_set.
Definition set_add_eq_set := set_add_eq_set.
Definition set_add_lim_nat := set_add_lim_nat.
Definition set_add_0 := set_add_0.
End Theory.

End GDioid.

Export Monoid.Exports SemiRing.Exports ComSemiRing.Exports.
Export Dioid.Exports ComDioid.Exports.
Export CompleteDioid.Exports ComCompleteDioid.Exports.
Export Pred.Exports SubType.Exports.

Notation "0" := (@eps _) : dioid_scope.
Notation "1" := (@e _) : dioid_scope.
Notation "+%D" := (@add _) : dioid_scope.
Notation "*%D" := (@mul _) : dioid_scope.
Notation "x + y" := (@add _ x y) : dioid_scope.
Notation "x * y" := (@mul _ x y) : dioid_scope.
Notation "<=%D" := (@led _) : dioid_scope.
Notation "x <= y" := (@led _ x y) : dioid_scope.
Notation "sup{ B }" := (set_add B) : dioid_scope.

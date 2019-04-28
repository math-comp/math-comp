(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype finset fingroup morphism perm action.
From mathcomp Require Import ssralg countalg.

(*****************************************************************************)
(* This file clones the entire ssralg hierachy for finite types; this allows *)
(* type inference to function properly on expressions that mix combinatorial *)
(* and algebraic operators (e.g., [set x + y | x in A, y in A]).             *)
(*   finZmodType, finRingType, finComRingType, finUnitRingType,              *)
(*   finComUnitRingType, finIdomType, finFieldType finLmodType,              *)
(*   finLalgType finAlgType finUnitAlgType                                   *)
(*      == the finite counterparts of zmodType, etc.                         *)
(* Note that a finFieldType is canonically decidable. All these structures   *)
(* can be derived using [xxxType of T] forms, e.g., if R has both canonical  *)
(* finType and ringType structures, then                                     *)
(*     Canonical R_finRingType := Eval hnf in [finRingType of R].            *)
(* declares the derived finRingType structure for R. As the implementation   *)
(* of the derivation is somewhat involved, the Eval hnf normalization is     *)
(* strongly recommended.                                                     *)
(*   This file also provides direct tie-ins with finite group theory:        *)
(*  [baseFinGroupType of R for +%R] == the (canonical) additive group        *)
(*      [finGroupType of R for +%R]    structures for R                      *)
(*                         {unit R} == the type of units of R, which has a   *)
(*                                     canonical group structure.            *)
(*                FinRing.unit R Ux == the element of {unit R} corresponding *)
(*                                     to x, where Ux : x \in GRing.unit.    *)
(*                           'U%act == the action by right multiplication of *)
(*                                     {unit R} on R, via FinRing.unit_act.  *)
(*                                     (This is also a group action.)        *)
(*****************************************************************************)

Local Open Scope ring_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module FinRing.

Local Notation mixin_of T b := (Finite.mixin_of (EqType T b)).

Section Generic.

(* Implicits *)
Variables (type base_type : Type) (class_of base_of : Type -> Type).
Variable to_choice : forall T, base_of T -> Choice.class_of T.
Variable base_sort : base_type -> Type.

(* Explicits *)
Variable Pack : forall T, class_of T -> type.
Variable Class : forall T b, mixin_of T (to_choice b) -> class_of T.
Variable base_class : forall bT, base_of (base_sort bT).

Definition gen_pack T :=
  fun bT b & phant_id (base_class bT) b =>
  fun fT m & phant_id (Finite.class fT) (Finite.Class m) =>
  Pack (@Class T b m).

End Generic.

Arguments gen_pack [type base_type class_of base_of to_choice base_sort].
Local Notation fin_ c := (@Finite.Class _ c c).
Local Notation do_pack pack T := (pack T _ _ id _ _ id).
Import GRing.Theory.

Definition groupMixin V := FinGroup.Mixin (@addrA V) (@add0r V) (@addNr V).
Local Notation base_group T vT fT :=
  (@FinGroup.PackBase T (groupMixin vT) (Finite.class fT)).
Local Notation fin_group B V := (@FinGroup.Pack B (@addNr V)).

Module Zmodule.

Section ClassDef.

Record class_of M :=
  Class { base : GRing.Zmodule.class_of M; mixin : mixin_of M base }.
Local Coercion base : class_of >-> GRing.Zmodule.class_of.
Local Coercion base2 R (c : class_of R) : CountRing.Zmodule.class_of R :=
  CountRing.Zmodule.Class c (mixin c).
Local Coercion mixin : class_of >-> mixin_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Definition pack := gen_pack Pack Class GRing.Zmodule.class.
Variable cT : type.
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition countType := @Countable.Pack cT (fin_ xclass).
Definition finType := @Finite.Pack cT (fin_ xclass).
Definition zmodType := @GRing.Zmodule.Pack cT xclass.
Definition countZmodType := @CountRing.Zmodule.Pack cT xclass.
Definition baseFinGroupType := base_group cT zmodType finType.
Definition finGroupType := fin_group baseFinGroupType zmodType.

Definition zmod_finType := @Finite.Pack zmodType (fin_ xclass).
Definition zmod_baseFinGroupType := base_group zmodType zmodType finType.
Definition zmod_finGroupType := fin_group zmod_baseFinGroupType zmodType.
Definition countZmod_finType := @Finite.Pack countZmodType (fin_ xclass).
Definition countZmod_baseFinGroupType :=
  base_group countZmodType zmodType finType.
Definition countZmod_finGroupType :=
  fin_group countZmod_baseFinGroupType zmodType.

End ClassDef.

Module Exports.
Coercion base : class_of >-> GRing.Zmodule.class_of.
Coercion base2 : class_of >-> CountRing.Zmodule.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion countType : type >-> Countable.type.
Canonical countType.
Coercion finType : type >-> Finite.type.
Canonical finType.
Coercion baseFinGroupType : type >-> FinGroup.base_type.
Canonical baseFinGroupType.
Coercion finGroupType : type >-> FinGroup.type.
Canonical finGroupType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion countZmodType : type >-> CountRing.Zmodule.type.
Canonical countZmodType.
Canonical zmod_finType.
Canonical zmod_baseFinGroupType.
Canonical zmod_finGroupType.
Canonical countZmod_finType.
Canonical countZmod_baseFinGroupType.
Canonical countZmod_finGroupType.
Notation finZmodType := type.
Notation "[ 'finZmodType' 'of' T ]" := (do_pack pack T)
  (at level 0, format "[ 'finZmodType'  'of'  T ]") : form_scope.
Notation "[ 'baseFinGroupType' 'of' R 'for' +%R ]" :=
    (BaseFinGroupType R (groupMixin _))
  (at level 0, format "[ 'baseFinGroupType'  'of'  R  'for'  +%R ]")
    : form_scope.
Notation "[ 'finGroupType' 'of' R 'for' +%R ]" :=
    (@FinGroup.clone R _ (finGroupType _) id _ id)
  (at level 0, format "[ 'finGroupType'  'of'  R  'for'  +%R ]") : form_scope.
End Exports.

End Zmodule.
Import Zmodule.Exports.

Section AdditiveGroup.

Variable U : finZmodType.
Implicit Types x y : U.

Lemma zmod1gE : 1%g = 0 :> U.            Proof. by []. Qed.
Lemma zmodVgE x : x^-1%g = - x.          Proof. by []. Qed.
Lemma zmodMgE x y : (x * y)%g = x + y.   Proof. by []. Qed.
Lemma zmodXgE n x : (x ^+ n)%g = x *+ n. Proof. by []. Qed.
Lemma zmod_mulgC x y : commute x y.      Proof. exact: GRing.addrC. Qed.
Lemma zmod_abelian (A : {set U}) : abelian A.
Proof. by apply/centsP=> x _ y _; apply: zmod_mulgC. Qed.

End AdditiveGroup.

Module Ring.

Section ClassDef.

Record class_of R :=
  Class { base : GRing.Ring.class_of R; mixin : mixin_of R base }.
Local Coercion base : class_of >-> GRing.Ring.class_of.
Local Coercion base2 R (c : class_of R) : CountRing.Ring.class_of R :=
  CountRing.Ring.Class c (mixin c).
Local Coercion base3 R (c : class_of R) : Zmodule.class_of R :=
  Zmodule.Class (mixin c).

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Definition pack := gen_pack Pack Class GRing.Ring.class.
Variable cT : type.
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition countType := @Countable.Pack cT (fin_ xclass).
Definition finType := @Finite.Pack cT (fin_ xclass).
Definition zmodType := @GRing.Zmodule.Pack cT xclass.
Definition countZmodType := @CountRing.Zmodule.Pack cT xclass.
Definition finZmodType := @Zmodule.Pack cT xclass.
Definition ringType := @GRing.Ring.Pack cT xclass.
Definition countRingType := @CountRing.Ring.Pack cT xclass.
Definition baseFinGroupType := base_group cT zmodType finType.
Definition finGroupType := fin_group baseFinGroupType zmodType.

Definition ring_finType := @Finite.Pack ringType (fin_ xclass).
Definition ring_baseFinGroupType := base_group ringType zmodType finType.
Definition ring_finGroupType := fin_group ring_baseFinGroupType zmodType.
Definition ring_finZmodType := @Zmodule.Pack ringType xclass.
Definition countRing_finType := @Finite.Pack countRingType (fin_ xclass).
Definition countRing_baseFinGroupType :=
  base_group countRingType zmodType finType.
Definition countRing_finGroupType :=
  fin_group countRing_baseFinGroupType zmodType.
Definition countRing_finZmodType := @Zmodule.Pack countRingType xclass.

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> GRing.Ring.class_of.
Coercion base2 : class_of >-> CountRing.Ring.class_of.
Coercion base3 : class_of >-> Zmodule.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion countType : type >-> Countable.type.
Canonical countType.
Coercion finType : type >-> Finite.type.
Canonical finType.
Coercion baseFinGroupType : type >-> FinGroup.base_type.
Canonical baseFinGroupType.
Coercion finGroupType : type >-> FinGroup.type.
Canonical finGroupType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion countZmodType : type >-> CountRing.Zmodule.type.
Canonical countZmodType.
Coercion finZmodType : type >-> Zmodule.type.
Canonical finZmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion countRingType : type >-> CountRing.Ring.type.
Canonical countRingType.
Canonical ring_finType.
Canonical ring_baseFinGroupType.
Canonical ring_finGroupType.
Canonical ring_finZmodType.
Canonical countRing_finType.
Canonical countRing_baseFinGroupType.
Canonical countRing_finGroupType.
Canonical countRing_finZmodType.
Notation finRingType := type.
Notation "[ 'finRingType' 'of' T ]" := (do_pack pack T)
  (at level 0, format "[ 'finRingType'  'of'  T ]") : form_scope.
End Exports.

Section Unit.

Variable R : finRingType.

Definition is_inv (x y : R) := (x * y == 1) && (y * x == 1).
Definition unit := [qualify a x : R | [exists y, is_inv x y]].
Definition inv x := odflt x (pick (is_inv x)).

Lemma mulVr : {in unit, left_inverse 1 inv *%R}.
Proof.
rewrite /inv => x Ux; case: pickP => [y | no_y]; last by case/pred0P: Ux.
by case/andP=> _; move/eqP.
Qed.

Lemma mulrV : {in unit, right_inverse 1 inv *%R}.
Proof.
rewrite /inv => x Ux; case: pickP => [y | no_y]; last by case/pred0P: Ux.
by case/andP; move/eqP.
Qed.

Lemma intro_unit x y : y * x = 1 /\ x * y = 1 -> x \is a unit.
Proof.
by case=> yx1 xy1; apply/existsP; exists y; rewrite /is_inv xy1 yx1 !eqxx.
Qed.

Lemma invr_out : {in [predC unit], inv =1 id}.
Proof.
rewrite /inv => x nUx; case: pickP => // y invxy.
by case/existsP: nUx; exists y.
Qed.

Definition UnitMixin := GRing.UnitRing.Mixin mulVr mulrV intro_unit invr_out.

End Unit.

End Ring.
Import Ring.Exports.

Module ComRing.

Section ClassDef.

Record class_of R :=
  Class { base : GRing.ComRing.class_of R; mixin : mixin_of R base }.
Local Coercion base : class_of >-> GRing.ComRing.class_of.
Local Coercion base2 R (c : class_of R) : CountRing.ComRing.class_of R :=
  CountRing.ComRing.Class c (mixin c).
Local Coercion base3 R (c : class_of R) : Ring.class_of R :=
  Ring.Class (mixin c).

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Definition pack := gen_pack Pack Class GRing.ComRing.class.
Variable cT : type.
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition countType := @Countable.Pack cT (fin_ xclass).
Definition finType := @Finite.Pack cT (fin_ xclass).
Definition zmodType := @GRing.Zmodule.Pack cT xclass.
Definition countZmodType := @CountRing.Zmodule.Pack cT xclass.
Definition finZmodType := @Zmodule.Pack cT xclass.
Definition ringType := @GRing.Ring.Pack cT xclass.
Definition countRingType := @CountRing.Ring.Pack cT xclass.
Definition finRingType := @Ring.Pack cT xclass.
Definition comRingType := @GRing.ComRing.Pack cT xclass.
Definition countComRingType := @CountRing.ComRing.Pack cT xclass.
Definition baseFinGroupType := base_group cT zmodType finType.
Definition finGroupType := fin_group baseFinGroupType zmodType.

Definition comRing_finType := @Finite.Pack comRingType (fin_ xclass).
Definition comRing_baseFinGroupType := base_group comRingType zmodType finType.
Definition comRing_finGroupType := fin_group comRing_baseFinGroupType zmodType.
Definition comRing_finZmodType := @Zmodule.Pack comRingType xclass.
Definition comRing_finRingType := @Ring.Pack comRingType xclass.
Definition countComRing_finType := @Finite.Pack countComRingType (fin_ xclass).
Definition countComRing_baseFinGroupType :=
  base_group countComRingType zmodType finType.
Definition countComRing_finGroupType :=
  fin_group countComRing_baseFinGroupType zmodType.
Definition countComRing_finZmodType := @Zmodule.Pack countComRingType xclass.
Definition countComRing_finRingType := @Ring.Pack countComRingType xclass.

End ClassDef.

Module Exports.
Coercion base : class_of >-> GRing.ComRing.class_of.
Coercion base2 : class_of >-> CountRing.ComRing.class_of.
Coercion base3 : class_of >-> Ring.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion countType : type >-> Countable.type.
Canonical countType.
Coercion finType : type >-> Finite.type.
Canonical finType.
Coercion baseFinGroupType : type >-> FinGroup.base_type.
Canonical baseFinGroupType.
Coercion finGroupType : type >-> FinGroup.type.
Canonical finGroupType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion countZmodType : type >-> CountRing.Zmodule.type.
Canonical countZmodType.
Coercion finZmodType : type >-> Zmodule.type.
Canonical finZmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion countRingType : type >-> CountRing.Ring.type.
Canonical countRingType.
Coercion finRingType : type >-> Ring.type.
Canonical finRingType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical comRingType.
Coercion countComRingType : type >-> CountRing.ComRing.type.
Canonical countComRingType.
Canonical comRing_finType.
Canonical comRing_baseFinGroupType.
Canonical comRing_finGroupType.
Canonical comRing_finZmodType.
Canonical comRing_finRingType.
Canonical countComRing_finType.
Canonical countComRing_baseFinGroupType.
Canonical countComRing_finGroupType.
Canonical countComRing_finZmodType.
Canonical countComRing_finRingType.
Notation finComRingType := FinRing.ComRing.type.
Notation "[ 'finComRingType' 'of' T ]" := (do_pack pack T)
  (at level 0, format "[ 'finComRingType'  'of'  T ]") : form_scope.
End Exports.

End ComRing.
Import ComRing.Exports.

Module UnitRing.

Section ClassDef.

Record class_of R :=
  Class { base : GRing.UnitRing.class_of R; mixin : mixin_of R base }.
Local Coercion base : class_of >-> GRing.UnitRing.class_of.
Local Coercion base2 R (c : class_of R) : CountRing.UnitRing.class_of R :=
  CountRing.UnitRing.Class c (mixin c).
Local Coercion base3 R (c : class_of R) : Ring.class_of R :=
  Ring.Class (mixin c).

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Definition pack := gen_pack Pack Class GRing.UnitRing.class.
Variable cT : type.
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition countType := @Countable.Pack cT (fin_ xclass).
Definition finType := @Finite.Pack cT (fin_ xclass).
Definition zmodType := @GRing.Zmodule.Pack cT xclass.
Definition countZmodType := @CountRing.Zmodule.Pack cT xclass.
Definition finZmodType := @Zmodule.Pack cT xclass.
Definition ringType := @GRing.Ring.Pack cT xclass.
Definition countRingType := @CountRing.Ring.Pack cT xclass.
Definition finRingType := @Ring.Pack cT xclass.
Definition unitRingType := @GRing.UnitRing.Pack cT xclass.
Definition countUnitRingType := @CountRing.UnitRing.Pack cT xclass.
Definition baseFinGroupType := base_group cT zmodType finType.
Definition finGroupType := fin_group baseFinGroupType zmodType.

Definition unitRing_finType := @Finite.Pack unitRingType (fin_ xclass).
Definition unitRing_baseFinGroupType :=
  base_group unitRingType zmodType finType.
Definition unitRing_finGroupType :=
  fin_group unitRing_baseFinGroupType zmodType.
Definition unitRing_finZmodType := @Zmodule.Pack unitRingType xclass.
Definition unitRing_finRingType := @Ring.Pack unitRingType xclass.
Definition countUnitRing_finType :=
  @Finite.Pack countUnitRingType (fin_ xclass).
Definition countUnitRing_baseFinGroupType :=
  base_group countUnitRingType zmodType finType.
Definition countUnitRing_finGroupType :=
  fin_group countUnitRing_baseFinGroupType zmodType.
Definition countUnitRing_finZmodType := @Zmodule.Pack countUnitRingType xclass.
Definition countUnitRing_finRingType := @Ring.Pack countUnitRingType xclass.

End ClassDef.

Module Exports.
Coercion base : class_of >-> GRing.UnitRing.class_of.
Coercion base2 : class_of >-> CountRing.UnitRing.class_of.
Coercion base3 : class_of >-> Ring.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion countType : type >-> Countable.type.
Canonical countType.
Coercion finType : type >-> Finite.type.
Canonical finType.
Coercion baseFinGroupType : type >-> FinGroup.base_type.
Canonical baseFinGroupType.
Coercion finGroupType : type >-> FinGroup.type.
Canonical finGroupType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion countZmodType : type >-> CountRing.Zmodule.type.
Canonical countZmodType.
Coercion finZmodType : type >-> Zmodule.type.
Canonical finZmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion countRingType : type >-> CountRing.Ring.type.
Canonical countRingType.
Coercion finRingType : type >-> Ring.type.
Canonical finRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical unitRingType.
Coercion countUnitRingType : type >-> CountRing.UnitRing.type.
Canonical countUnitRingType.
Canonical unitRing_finType.
Canonical unitRing_baseFinGroupType.
Canonical unitRing_finGroupType.
Canonical unitRing_finZmodType.
Canonical unitRing_finRingType.
Canonical countUnitRing_finType.
Canonical countUnitRing_baseFinGroupType.
Canonical countUnitRing_finGroupType.
Canonical countUnitRing_finZmodType.
Canonical countUnitRing_finRingType.
Notation finUnitRingType := FinRing.UnitRing.type.
Notation "[ 'finUnitRingType' 'of' T ]" := (do_pack pack T)
  (at level 0, format "[ 'finUnitRingType'  'of'  T ]") : form_scope.
End Exports.

End UnitRing.
Import UnitRing.Exports.

Section UnitsGroup.

Variable R : finUnitRingType.

Inductive unit_of (phR : phant R) := Unit (x : R) of x \is a GRing.unit.
Bind Scope group_scope with unit_of.

Let phR := Phant R.
Local Notation uT := (unit_of phR).
Implicit Types u v : uT.
Definition uval u := let: Unit x _ := u in x.

Canonical unit_subType := [subType for uval].
Definition unit_eqMixin := Eval hnf in [eqMixin of uT by <:].
Canonical unit_eqType := Eval hnf in EqType uT unit_eqMixin.
Definition unit_choiceMixin := [choiceMixin of uT by <:].
Canonical unit_choiceType := Eval hnf in ChoiceType uT unit_choiceMixin.
Definition unit_countMixin := [countMixin of uT by <:].
Canonical unit_countType := Eval hnf in CountType uT unit_countMixin.
Canonical unit_subCountType := Eval hnf in [subCountType of uT].
Definition unit_finMixin := [finMixin of uT by <:].
Canonical unit_finType := Eval hnf in FinType uT unit_finMixin.
Canonical unit_subFinType := Eval hnf in [subFinType of uT].

Definition unit1 := Unit phR (@GRing.unitr1 _).
Lemma unit_inv_proof u : (val u)^-1 \is a GRing.unit.
Proof. by rewrite GRing.unitrV ?(valP u). Qed.
Definition unit_inv u := Unit phR (unit_inv_proof u).
Lemma unit_mul_proof u v : val u * val v \is a GRing.unit.
Proof. by rewrite (GRing.unitrMr _ (valP u)) ?(valP v). Qed.
Definition unit_mul u v := Unit phR (unit_mul_proof u v).
Lemma unit_muluA : associative unit_mul.
Proof. by move=> u v w; apply: val_inj; apply: GRing.mulrA. Qed.
Lemma unit_mul1u : left_id unit1 unit_mul.
Proof. by move=> u; apply: val_inj; apply: GRing.mul1r. Qed.
Lemma unit_mulVu : left_inverse unit1 unit_inv unit_mul.
Proof. by move=> u; apply: val_inj; apply: GRing.mulVr (valP u). Qed.

Definition unit_GroupMixin := FinGroup.Mixin unit_muluA unit_mul1u unit_mulVu.
Canonical unit_baseFinGroupType :=
  Eval hnf in BaseFinGroupType uT unit_GroupMixin.
Canonical unit_finGroupType := Eval hnf in FinGroupType unit_mulVu.

Lemma val_unit1 : val (1%g : uT) = 1. Proof. by []. Qed.
Lemma val_unitM x y : val (x * y : uT)%g = val x * val y. Proof. by []. Qed.
Lemma val_unitV x : val (x^-1 : uT)%g = (val x)^-1. Proof. by []. Qed.
Lemma val_unitX n x : val (x ^+ n : uT)%g = val x ^+ n.
Proof. by case: n; last by elim=> //= n ->. Qed.

Definition unit_act x u := x * val u.
Lemma unit_actE x u : unit_act x u = x * val u. Proof. by []. Qed.

Canonical unit_action :=
  @TotalAction _ _ unit_act (@GRing.mulr1 _) (fun _ _ _ => GRing.mulrA _ _ _).
Lemma unit_is_groupAction : @is_groupAction _ R setT setT unit_action.
Proof.
move=> u _ /=; rewrite inE; apply/andP; split.
  by apply/subsetP=> x _; rewrite inE.
by apply/morphicP=> x y _ _; rewrite !actpermE /= [_ u]GRing.mulrDl.
Qed.
Canonical unit_groupAction := GroupAction unit_is_groupAction.

End UnitsGroup.

Module Import UnitsGroupExports.
Bind Scope group_scope with unit_of.
Canonical unit_subType.
Canonical unit_eqType.
Canonical unit_choiceType.
Canonical unit_countType.
Canonical unit_subCountType.
Canonical unit_finType.
Canonical unit_subFinType.
Canonical unit_baseFinGroupType.
Canonical unit_finGroupType.
Canonical unit_action.
Canonical unit_groupAction.
End UnitsGroupExports.

Notation unit R Ux := (Unit (Phant R) Ux).

Module ComUnitRing.

Section ClassDef.

Record class_of R :=
  Class { base : GRing.ComUnitRing.class_of R; mixin : mixin_of R base }.
Local Coercion base : class_of >-> GRing.ComUnitRing.class_of.
Local Coercion base2 R (c : class_of R) : CountRing.ComUnitRing.class_of R :=
  CountRing.ComUnitRing.Class c (mixin c).
Local Coercion base3 R (c : class_of R) : ComRing.class_of R :=
  ComRing.Class (mixin c).
Local Coercion base4 R (c : class_of R) : UnitRing.class_of R :=
  @UnitRing.Class R (base c) (mixin c).

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Definition pack := gen_pack Pack Class GRing.ComUnitRing.class.
Variable cT : type.
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition countType := @Countable.Pack cT (fin_ xclass).
Definition finType := @Finite.Pack cT (fin_ xclass).
Definition zmodType := @GRing.Zmodule.Pack cT xclass.
Definition countZmodType := @CountRing.Zmodule.Pack cT xclass.
Definition finZmodType := @Zmodule.Pack cT xclass.
Definition ringType := @GRing.Ring.Pack cT xclass.
Definition countRingType := @CountRing.Ring.Pack cT xclass.
Definition finRingType := @Ring.Pack cT xclass.
Definition comRingType := @GRing.ComRing.Pack cT xclass.
Definition countComRingType := @CountRing.ComRing.Pack cT xclass.
Definition finComRingType := @ComRing.Pack cT xclass.
Definition unitRingType := @GRing.UnitRing.Pack cT xclass.
Definition countUnitRingType := @CountRing.UnitRing.Pack cT xclass.
Definition finUnitRingType := @UnitRing.Pack cT xclass.
Definition comUnitRingType := @GRing.ComUnitRing.Pack cT xclass.
Definition countComUnitRingType := @CountRing.ComUnitRing.Pack cT xclass.
Definition baseFinGroupType := base_group cT zmodType finType.
Definition finGroupType := fin_group baseFinGroupType zmodType.

Definition comUnitRing_finType := @Finite.Pack comUnitRingType (fin_ xclass).
Definition comUnitRing_baseFinGroupType :=
  base_group comUnitRingType zmodType finType.
Definition comUnitRing_finGroupType :=
  fin_group comUnitRing_baseFinGroupType zmodType.
Definition comUnitRing_finZmodType := @Zmodule.Pack comUnitRingType xclass.
Definition comUnitRing_finRingType := @Ring.Pack comUnitRingType xclass.
Definition comUnitRing_finComRingType := @ComRing.Pack comUnitRingType xclass.
Definition comUnitRing_finUnitRingType := @UnitRing.Pack comUnitRingType xclass.
Definition countComUnitRing_finType :=
  @Finite.Pack countComUnitRingType (fin_ xclass).
Definition countComUnitRing_baseFinGroupType :=
  base_group countComUnitRingType zmodType finType.
Definition countComUnitRing_finGroupType :=
  fin_group countComUnitRing_baseFinGroupType zmodType.
Definition countComUnitRing_finZmodType :=
  @Zmodule.Pack countComUnitRingType xclass.
Definition countComUnitRing_finRingType :=
  @Ring.Pack countComUnitRingType xclass.
Definition countComUnitRing_finComRingType :=
  @ComRing.Pack countComUnitRingType xclass.
Definition countComUnitRing_finUnitRingType :=
  @UnitRing.Pack countComUnitRingType xclass.
Definition unitRing_finComRingType := @ComRing.Pack unitRingType xclass.
Definition countUnitRing_finComRingType :=
  @ComRing.Pack countUnitRingType xclass.
Definition comRing_finUnitRingType := @UnitRing.Pack comRingType xclass.
Definition countComRing_finUnitRingType :=
  @UnitRing.Pack countComRingType xclass.
Definition finComRing_finUnitRingType := @UnitRing.Pack finComRingType xclass.

End ClassDef.

Module Exports.
Coercion base : class_of >-> GRing.ComUnitRing.class_of.
Coercion base2 : class_of >-> CountRing.ComUnitRing.class_of.
Coercion base3 : class_of >-> ComRing.class_of.
Coercion base4 : class_of >-> UnitRing.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion countType : type >-> Countable.type.
Canonical countType.
Coercion finType : type >-> Finite.type.
Canonical finType.
Coercion baseFinGroupType : type >-> FinGroup.base_type.
Canonical baseFinGroupType.
Coercion finGroupType : type >-> FinGroup.type.
Canonical finGroupType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion countZmodType : type >-> CountRing.Zmodule.type.
Canonical countZmodType.
Coercion finZmodType : type >-> Zmodule.type.
Canonical finZmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion countRingType : type >-> CountRing.Ring.type.
Canonical countRingType.
Coercion finRingType : type >-> Ring.type.
Canonical finRingType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical comRingType.
Coercion countComRingType : type >-> CountRing.ComRing.type.
Canonical countComRingType.
Coercion finComRingType : type >-> ComRing.type.
Canonical finComRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical unitRingType.
Coercion countUnitRingType : type >-> CountRing.UnitRing.type.
Canonical countUnitRingType.
Coercion finUnitRingType : type >-> UnitRing.type.
Canonical finUnitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical comUnitRingType.
Coercion countComUnitRingType : type >-> CountRing.ComUnitRing.type.
Canonical countComUnitRingType.
Canonical comUnitRing_finType.
Canonical comUnitRing_baseFinGroupType.
Canonical comUnitRing_finGroupType.
Canonical comUnitRing_finZmodType.
Canonical comUnitRing_finRingType.
Canonical comUnitRing_finComRingType.
Canonical comUnitRing_finUnitRingType.
Canonical countComUnitRing_finType.
Canonical countComUnitRing_baseFinGroupType.
Canonical countComUnitRing_finGroupType.
Canonical countComUnitRing_finZmodType.
Canonical countComUnitRing_finRingType.
Canonical countComUnitRing_finComRingType.
Canonical countComUnitRing_finUnitRingType.
Canonical unitRing_finComRingType.
Canonical countUnitRing_finComRingType.
Canonical comRing_finUnitRingType.
Canonical countComRing_finUnitRingType.
Canonical finComRing_finUnitRingType.
Notation finComUnitRingType := FinRing.ComUnitRing.type.
Notation "[ 'finComUnitRingType' 'of' T ]" := (do_pack pack T)
  (at level 0, format "[ 'finComUnitRingType'  'of'  T ]") : form_scope.
End Exports.

End ComUnitRing.
Import ComUnitRing.Exports.

Module IntegralDomain.

Section ClassDef.

Record class_of R :=
  Class { base : GRing.IntegralDomain.class_of R; mixin : mixin_of R base }.
Local Coercion base : class_of >-> GRing.IntegralDomain.class_of.
Local Coercion base2 R (c : class_of R) : CountRing.IntegralDomain.class_of R :=
  CountRing.IntegralDomain.Class c (mixin c).
Local Coercion base3 R (c : class_of R) : ComUnitRing.class_of R :=
  ComUnitRing.Class (mixin c).

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Definition pack := gen_pack Pack Class GRing.IntegralDomain.class.
Variable cT : type.
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition countType := @Countable.Pack cT (fin_ xclass).
Definition finType := @Finite.Pack cT (fin_ xclass).
Definition zmodType := @GRing.Zmodule.Pack cT xclass.
Definition countZmodType := @CountRing.Zmodule.Pack cT xclass.
Definition finZmodType := @Zmodule.Pack cT xclass.
Definition ringType := @GRing.Ring.Pack cT xclass.
Definition countRingType := @CountRing.Ring.Pack cT xclass.
Definition finRingType := @Ring.Pack cT xclass.
Definition comRingType := @GRing.ComRing.Pack cT xclass.
Definition countComRingType := @CountRing.ComRing.Pack cT xclass.
Definition finComRingType := @ComRing.Pack cT xclass.
Definition unitRingType := @GRing.UnitRing.Pack cT xclass.
Definition countUnitRingType := @CountRing.UnitRing.Pack cT xclass.
Definition finUnitRingType := @UnitRing.Pack cT xclass.
Definition comUnitRingType := @GRing.ComUnitRing.Pack cT xclass.
Definition countComUnitRingType := @CountRing.ComUnitRing.Pack cT xclass.
Definition finComUnitRingType := @ComUnitRing.Pack cT xclass.
Definition idomainType := @GRing.IntegralDomain.Pack cT xclass.
Definition countIdomainType := @CountRing.IntegralDomain.Pack cT xclass.
Definition baseFinGroupType := base_group cT zmodType finType.
Definition finGroupType := fin_group baseFinGroupType zmodType.

Definition idomain_finType := @Finite.Pack idomainType (fin_ xclass).
Definition idomain_baseFinGroupType := base_group idomainType zmodType finType.
Definition idomain_finGroupType := fin_group idomain_baseFinGroupType zmodType.
Definition idomain_finZmodType := @Zmodule.Pack idomainType xclass.
Definition idomain_finRingType := @Ring.Pack idomainType xclass.
Definition idomain_finUnitRingType := @UnitRing.Pack idomainType xclass.
Definition idomain_finComRingType := @ComRing.Pack idomainType xclass.
Definition idomain_finComUnitRingType := @ComUnitRing.Pack idomainType xclass.
Definition countIdomain_finType := @Finite.Pack countIdomainType (fin_ xclass).
Definition countIdomain_baseFinGroupType :=
  base_group countIdomainType zmodType finType.
Definition countIdomain_finGroupType :=
  fin_group countIdomain_baseFinGroupType zmodType.
Definition countIdomain_finZmodType := @Zmodule.Pack countIdomainType xclass.
Definition countIdomain_finRingType := @Ring.Pack countIdomainType xclass.
Definition countIdomain_finUnitRingType :=
  @UnitRing.Pack countIdomainType xclass.
Definition countIdomain_finComRingType := @ComRing.Pack countIdomainType xclass.
Definition countIdomain_finComUnitRingType :=
  @ComUnitRing.Pack countIdomainType xclass.

End ClassDef.

Module Exports.
Coercion base : class_of >-> GRing.IntegralDomain.class_of.
Coercion base2 : class_of >-> CountRing.IntegralDomain.class_of.
Coercion base3 : class_of >-> ComUnitRing.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion countType : type >-> Countable.type.
Canonical countType.
Coercion finType : type >-> Finite.type.
Canonical finType.
Coercion baseFinGroupType : type >-> FinGroup.base_type.
Canonical baseFinGroupType.
Coercion finGroupType : type >-> FinGroup.type.
Canonical finGroupType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion countZmodType : type >-> CountRing.Zmodule.type.
Canonical countZmodType.
Coercion finZmodType : type >-> Zmodule.type.
Canonical finZmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion countRingType : type >-> CountRing.Ring.type.
Canonical countRingType.
Coercion finRingType : type >-> Ring.type.
Canonical finRingType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical comRingType.
Coercion countComRingType : type >-> CountRing.ComRing.type.
Canonical countComRingType.
Coercion finComRingType : type >-> ComRing.type.
Canonical finComRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical unitRingType.
Coercion countUnitRingType : type >-> CountRing.UnitRing.type.
Canonical countUnitRingType.
Coercion finUnitRingType : type >-> UnitRing.type.
Canonical finUnitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical comUnitRingType.
Coercion countComUnitRingType : type >-> CountRing.ComUnitRing.type.
Canonical countComUnitRingType.
Coercion finComUnitRingType : type >-> ComUnitRing.type.
Canonical finComUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical idomainType.
Coercion countIdomainType : type >-> CountRing.IntegralDomain.type.
Canonical countIdomainType.
Canonical idomain_finType.
Canonical idomain_baseFinGroupType.
Canonical idomain_finGroupType.
Canonical idomain_finZmodType.
Canonical idomain_finRingType.
Canonical idomain_finUnitRingType.
Canonical idomain_finComRingType.
Canonical idomain_finComUnitRingType.
Canonical countIdomain_finType.
Canonical countIdomain_baseFinGroupType.
Canonical countIdomain_finGroupType.
Canonical countIdomain_finZmodType.
Canonical countIdomain_finRingType.
Canonical countIdomain_finUnitRingType.
Canonical countIdomain_finComRingType.
Canonical countIdomain_finComUnitRingType.
Notation finIdomainType := FinRing.IntegralDomain.type.
Notation "[ 'finIdomainType' 'of' T ]" := (do_pack pack T)
  (at level 0, format "[ 'finIdomainType'  'of'  T ]") : form_scope.
End Exports.

End IntegralDomain.
Import IntegralDomain.Exports.

Module Field.

Section ClassDef.

Record class_of R :=
  Class { base : GRing.Field.class_of R; mixin : mixin_of R base }.
Local Coercion base : class_of >-> GRing.Field.class_of.
Local Coercion base2 R (c : class_of R) : CountRing.Field.class_of R :=
  CountRing.Field.Class c (mixin c).
Local Coercion base3 R (c : class_of R) : IntegralDomain.class_of R :=
  IntegralDomain.Class (mixin c).

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Definition pack := gen_pack Pack Class GRing.Field.class.
Variable cT : type.
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition countType := @Countable.Pack cT (fin_ xclass).
Definition finType := @Finite.Pack cT (fin_ xclass).
Definition zmodType := @GRing.Zmodule.Pack cT xclass.
Definition countZmodType := @CountRing.Zmodule.Pack cT xclass.
Definition finZmodType := @Zmodule.Pack cT xclass.
Definition ringType := @GRing.Ring.Pack cT xclass.
Definition countRingType := @CountRing.Ring.Pack cT xclass.
Definition finRingType := @Ring.Pack cT xclass.
Definition comRingType := @GRing.ComRing.Pack cT xclass.
Definition countComRingType := @CountRing.ComRing.Pack cT xclass.
Definition finComRingType := @ComRing.Pack cT xclass.
Definition unitRingType := @GRing.UnitRing.Pack cT xclass.
Definition countUnitRingType := @CountRing.UnitRing.Pack cT xclass.
Definition finUnitRingType := @UnitRing.Pack cT xclass.
Definition comUnitRingType := @GRing.ComUnitRing.Pack cT xclass.
Definition countComUnitRingType := @CountRing.ComUnitRing.Pack cT xclass.
Definition finComUnitRingType := @ComUnitRing.Pack cT xclass.
Definition idomainType := @GRing.IntegralDomain.Pack cT xclass.
Definition countIdomainType := @CountRing.IntegralDomain.Pack cT xclass.
Definition finIdomainType := @IntegralDomain.Pack cT xclass.
Definition fieldType := @GRing.Field.Pack cT xclass.
Definition countFieldType := @CountRing.Field.Pack cT xclass.
Definition baseFinGroupType := base_group cT zmodType finType.
Definition finGroupType := fin_group baseFinGroupType zmodType.

Definition field_finType := @Finite.Pack fieldType (fin_ xclass).
Definition field_baseFinGroupType := base_group fieldType zmodType finType.
Definition field_finGroupType := fin_group field_baseFinGroupType zmodType.
Definition field_finZmodType := @Zmodule.Pack fieldType xclass.
Definition field_finRingType := @Ring.Pack fieldType xclass.
Definition field_finUnitRingType := @UnitRing.Pack fieldType xclass.
Definition field_finComRingType := @ComRing.Pack fieldType xclass.
Definition field_finComUnitRingType := @ComUnitRing.Pack fieldType xclass.
Definition field_finIdomainType := @IntegralDomain.Pack fieldType xclass.
Definition countField_finType := @Finite.Pack countFieldType (fin_ xclass).
Definition countField_baseFinGroupType :=
  base_group countFieldType zmodType finType.
Definition countField_finGroupType :=
  fin_group countField_baseFinGroupType zmodType.
Definition countField_finZmodType := @Zmodule.Pack countFieldType xclass.
Definition countField_finRingType := @Ring.Pack countFieldType xclass.
Definition countField_finUnitRingType := @UnitRing.Pack countFieldType xclass.
Definition countField_finComRingType := @ComRing.Pack countFieldType xclass.
Definition countField_finComUnitRingType :=
  @ComUnitRing.Pack countFieldType xclass.
Definition countField_finIdomainType :=
  @IntegralDomain.Pack countFieldType xclass.

End ClassDef.

Module Exports.
Coercion base : class_of >-> GRing.Field.class_of.
Coercion base2 : class_of >-> CountRing.Field.class_of.
Coercion base3 : class_of >-> IntegralDomain.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion countType : type >-> Countable.type.
Canonical countType.
Coercion finType : type >-> Finite.type.
Canonical finType.
Coercion baseFinGroupType : type >-> FinGroup.base_type.
Canonical baseFinGroupType.
Coercion finGroupType : type >-> FinGroup.type.
Canonical finGroupType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion countZmodType : type >-> CountRing.Zmodule.type.
Canonical countZmodType.
Coercion finZmodType : type >-> Zmodule.type.
Canonical finZmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion countRingType : type >-> CountRing.Ring.type.
Canonical countRingType.
Coercion finRingType : type >-> Ring.type.
Canonical finRingType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical comRingType.
Coercion countComRingType : type >-> CountRing.ComRing.type.
Canonical countComRingType.
Coercion finComRingType : type >-> ComRing.type.
Canonical finComRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical unitRingType.
Coercion countUnitRingType : type >-> CountRing.UnitRing.type.
Canonical countUnitRingType.
Coercion finUnitRingType : type >-> UnitRing.type.
Canonical finUnitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical comUnitRingType.
Coercion countComUnitRingType : type >-> CountRing.ComUnitRing.type.
Canonical countComUnitRingType.
Coercion finComUnitRingType : type >-> ComUnitRing.type.
Canonical finComUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical idomainType.
Coercion countIdomainType : type >-> CountRing.IntegralDomain.type.
Canonical countIdomainType.
Coercion finIdomainType : type >-> IntegralDomain.type.
Canonical finIdomainType.
Coercion fieldType : type >-> GRing.Field.type.
Canonical fieldType.
Coercion countFieldType : type >-> CountRing.Field.type.
Canonical countFieldType.
Canonical field_finType.
Canonical field_baseFinGroupType.
Canonical field_finGroupType.
Canonical field_finZmodType.
Canonical field_finRingType.
Canonical field_finUnitRingType.
Canonical field_finComRingType.
Canonical field_finComUnitRingType.
Canonical field_finIdomainType.
Canonical countField_finType.
Canonical countField_baseFinGroupType.
Canonical countField_finGroupType.
Canonical countField_finZmodType.
Canonical countField_finRingType.
Canonical countField_finUnitRingType.
Canonical countField_finComRingType.
Canonical countField_finComUnitRingType.
Canonical countField_finIdomainType.
Notation finFieldType := FinRing.Field.type.
Notation "[ 'finFieldType' 'of' T ]" := (do_pack pack T)
  (at level 0, format "[ 'finFieldType'  'of'  T ]") : form_scope.
End Exports.

End Field.
Import Field.Exports.

Section DecideField.

Variable F : Field.type.

Fixpoint sat e f :=
  match f with
  | GRing.Bool b => b
  | t1 == t2 => (GRing.eval e t1 == GRing.eval e t2)%bool
  | GRing.Unit t => GRing.eval e t \is a GRing.unit
  | f1 /\ f2 => sat e f1 && sat e f2
  | f1 \/ f2 => sat e f1 || sat e f2
  | f1 ==> f2 => (sat e f1 ==> sat e f2)%bool
  | ~ f1 => ~~ sat e f1
  | ('exists 'X_k, f1) => [exists x : F, sat (set_nth 0%R e k x) f1]
  | ('forall 'X_k, f1) => [forall x : F, sat (set_nth 0%R e k x) f1]
  end%T.

Lemma decidable : GRing.DecidableField.axiom sat.
Proof.
move=> e f; elim: f e;
  try by move=> f1 IH1 f2 IH2 e /=; case IH1; case IH2; constructor; tauto.
- by move=> b e; apply: idP.
- by move=> t1 t2 e; apply: eqP.
- by move=> t e; apply: idP.
- by move=> f IH e /=; case: IH; constructor.
- by move=> i f IH e; apply: (iffP existsP) => [] [x fx]; exists x; apply/IH.
by move=> i f IH e; apply: (iffP forallP) => f_ x; apply/IH.
Qed.

Definition DecidableFieldMixin := DecFieldMixin decidable.

End DecideField.

Module DecField.

Section Joins.

Variable cT : Field.type.
Let xT := let: Field.Pack T _ := cT in T. 
Let xclass : Field.class_of xT := Field.class cT.

Definition type := Eval hnf in DecFieldType cT (DecidableFieldMixin cT).
Definition finType := @Finite.Pack type (fin_ xclass).
Definition finZmodType := @Zmodule.Pack type xclass.
Definition finRingType := @Ring.Pack type xclass.
Definition finUnitRingType := @UnitRing.Pack type xclass.
Definition finComRingType := @ComRing.Pack type xclass.
Definition finComUnitRingType := @ComUnitRing.Pack type xclass.
Definition finIdomainType := @IntegralDomain.Pack type xclass.
Definition baseFinGroupType := base_group type finZmodType finZmodType.
Definition finGroupType := fin_group baseFinGroupType cT.

End Joins.

Module Exports.
Coercion type : Field.type >-> GRing.DecidableField.type.
Canonical type.
Canonical finType.
Canonical finZmodType.
Canonical finRingType.
Canonical finUnitRingType.
Canonical finComRingType.
Canonical finComUnitRingType.
Canonical finIdomainType.
Canonical baseFinGroupType.
Canonical finGroupType.

End Exports.

End DecField.

Module Lmodule.

Section ClassDef.

Variable R : ringType.

Record class_of M :=
  Class { base : GRing.Lmodule.class_of R M; mixin : mixin_of M base }.
Local Coercion base : class_of >-> GRing.Lmodule.class_of.
Local Coercion base2 R (c : class_of R) : Zmodule.class_of R :=
  Zmodule.Class (mixin c).

Structure type (phR : phant R) := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (phR : phant R) (cT : type phR).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition pack := gen_pack (Pack phR) Class (@GRing.Lmodule.class R phR).
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition countType := @Countable.Pack cT (fin_ xclass).
Definition finType := @Finite.Pack cT (fin_ xclass).
Definition zmodType := @GRing.Zmodule.Pack cT xclass.
Definition countZmodType := @CountRing.Zmodule.Pack cT xclass.
Definition finZmodType := @Zmodule.Pack cT xclass.
Definition lmodType := @GRing.Lmodule.Pack R phR cT xclass.
Definition baseFinGroupType := base_group cT zmodType finType.
Definition finGroupType := fin_group baseFinGroupType zmodType.

Definition lmod_countType := @Countable.Pack lmodType (fin_ xclass).
Definition lmod_finType := @Finite.Pack lmodType (fin_ xclass).
Definition lmod_baseFinGroupType := base_group lmodType zmodType finType.
Definition lmod_finGroupType := fin_group lmod_baseFinGroupType zmodType.
Definition lmod_countZmodType := @CountRing.Zmodule.Pack lmodType xclass.
Definition lmod_finZmodType := @Zmodule.Pack lmodType xclass.

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> GRing.Lmodule.class_of.
Coercion base2 : class_of >-> Zmodule.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion countType : type >-> Countable.type.
Canonical countType.
Coercion finType : type >-> Finite.type.
Canonical finType.
Coercion baseFinGroupType : type >-> FinGroup.base_type.
Canonical baseFinGroupType.
Coercion finGroupType : type >-> FinGroup.type.
Canonical finGroupType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion countZmodType : type >-> CountRing.Zmodule.type.
Canonical countZmodType.
Coercion finZmodType : type >-> Zmodule.type.
Canonical finZmodType.
Coercion lmodType : type >-> GRing.Lmodule.type.
Canonical lmodType.
Canonical lmod_countType.
Canonical lmod_finType.
Canonical lmod_baseFinGroupType.
Canonical lmod_finGroupType.
Canonical lmod_countZmodType.
Canonical lmod_finZmodType.
Notation finLmodType R := (FinRing.Lmodule.type (Phant R)).
Notation "[ 'finLmodType' R 'of' T ]" := (do_pack (@pack _ (Phant R)) T)
  (at level 0, format "[ 'finLmodType'  R  'of'  T ]") : form_scope.
End Exports.

End Lmodule.
Import Lmodule.Exports.

Module Lalgebra.

Section ClassDef.

Variable R : ringType.

Record class_of M :=
  Class { base : GRing.Lalgebra.class_of R M; mixin : mixin_of M base }.
Definition base2 M (c : class_of M) := Ring.Class (mixin c).
Definition base3 M (c : class_of M) := @Lmodule.Class _ _ (base c) (mixin c).
Local Coercion base : class_of >-> GRing.Lalgebra.class_of.
Local Coercion base2 : class_of >-> Ring.class_of.
Local Coercion base3 : class_of >-> Lmodule.class_of.

Structure type (phR : phant R) := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (phR : phant R) (cT : type phR).
Definition pack := gen_pack (Pack phR) Class (@GRing.Lalgebra.class R phR).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition countType := @Countable.Pack cT (fin_ xclass).
Definition finType := @Finite.Pack cT (fin_ xclass).
Definition zmodType := @GRing.Zmodule.Pack cT xclass.
Definition countZmodType := @CountRing.Zmodule.Pack cT xclass.
Definition finZmodType := @Zmodule.Pack cT xclass.
Definition ringType := @GRing.Ring.Pack cT xclass.
Definition countRingType := @CountRing.Ring.Pack cT xclass.
Definition finRingType := @Ring.Pack cT xclass.
Definition lmodType := @GRing.Lmodule.Pack R phR cT xclass.
Definition finLmodType := @Lmodule.Pack R phR cT xclass.
Definition lalgType := @GRing.Lalgebra.Pack R phR cT xclass.
Definition baseFinGroupType := base_group cT zmodType finType.
Definition finGroupType := fin_group baseFinGroupType zmodType.

Definition lalg_countType := @Countable.Pack lalgType (fin_ xclass).
Definition lalg_finType := @Finite.Pack lalgType (fin_ xclass).
Definition lalg_baseFinGroupType := base_group lalgType zmodType finType.
Definition lalg_finGroupType := fin_group lalg_baseFinGroupType zmodType.
Definition lalg_countZmodType := @CountRing.Zmodule.Pack lalgType xclass.
Definition lalg_finZmodType := @Zmodule.Pack lalgType xclass.
Definition lalg_finLmodType := @Lmodule.Pack R phR lalgType xclass.
Definition lalg_countRingType := @CountRing.Ring.Pack lalgType xclass.
Definition lalg_finRingType := @Ring.Pack lalgType xclass.
Definition lmod_countRingType := @CountRing.Ring.Pack lmodType xclass.
Definition lmod_finRingType := @Ring.Pack lmodType xclass.
Definition finLmod_ringType := @GRing.Ring.Pack finLmodType xclass.
Definition finLmod_countRingType := @CountRing.Ring.Pack finLmodType xclass.
Definition finLmod_finRingType := @Ring.Pack finLmodType xclass.

End ClassDef.

Module Exports.
Coercion base : class_of >-> GRing.Lalgebra.class_of.
Coercion base2 : class_of >-> Ring.class_of.
Coercion base3 : class_of >-> Lmodule.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion countType : type >-> Countable.type.
Canonical countType.
Coercion finType : type >-> Finite.type.
Canonical finType.
Coercion baseFinGroupType : type >-> FinGroup.base_type.
Canonical baseFinGroupType.
Coercion finGroupType : type >-> FinGroup.type.
Canonical finGroupType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion countZmodType : type >-> CountRing.Zmodule.type.
Canonical countZmodType.
Coercion finZmodType : type >-> Zmodule.type.
Canonical finZmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion countRingType : type >-> CountRing.Ring.type.
Canonical countRingType.
Coercion finRingType : type >-> Ring.type.
Canonical finRingType.
Coercion lmodType : type >-> GRing.Lmodule.type.
Canonical lmodType.
Coercion finLmodType : type >-> Lmodule.type.
Canonical finLmodType.
Coercion lalgType : type >-> GRing.Lalgebra.type.
Canonical lalgType.
Canonical lalg_countType.
Canonical lalg_finType.
Canonical lalg_baseFinGroupType.
Canonical lalg_finGroupType.
Canonical lalg_countZmodType.
Canonical lalg_finZmodType.
Canonical lalg_finLmodType.
Canonical lalg_countRingType.
Canonical lalg_finRingType.
Canonical lmod_countRingType.
Canonical lmod_finRingType.
Canonical finLmod_ringType.
Canonical finLmod_countRingType.
Canonical finLmod_finRingType.
Notation finLalgType R := (FinRing.Lalgebra.type (Phant R)).
Notation "[ 'finLalgType' R 'of' T ]" := (do_pack (@pack _ (Phant R)) T)
  (at level 0, format "[ 'finLalgType'  R  'of'  T ]") : form_scope.
End Exports.

End Lalgebra.
Import Lalgebra.Exports.

Module Algebra.

Section ClassDef.

Variable R : ringType.

Record class_of M :=
  Class { base : GRing.Algebra.class_of R M; mixin : mixin_of M base }.
Definition base2 M (c : class_of M) := Lalgebra.Class (mixin c).
Local Coercion base : class_of >-> GRing.Algebra.class_of.
Local Coercion base2 : class_of >->Lalgebra.class_of.

Structure type (phR : phant R) := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (phR : phant R) (cT : type phR).
Definition pack := gen_pack (Pack phR) Class (@GRing.Algebra.class R phR).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition countType := @Countable.Pack cT (fin_ xclass).
Definition finType := @Finite.Pack cT (fin_ xclass).
Definition zmodType := @GRing.Zmodule.Pack cT xclass.
Definition countZmodType := @CountRing.Zmodule.Pack cT xclass.
Definition finZmodType := @Zmodule.Pack cT xclass.
Definition ringType := @GRing.Ring.Pack cT xclass.
Definition countRingType := @CountRing.Ring.Pack cT xclass.
Definition finRingType := @Ring.Pack cT xclass.
Definition lmodType := @GRing.Lmodule.Pack R phR cT xclass.
Definition finLmodType := @Lmodule.Pack R phR cT xclass.
Definition lalgType := @GRing.Lalgebra.Pack R phR cT xclass.
Definition finLalgType := @Lalgebra.Pack R phR cT xclass.
Definition algType := @GRing.Algebra.Pack R phR cT xclass.
Definition baseFinGroupType := base_group cT zmodType finType.
Definition finGroupType := fin_group baseFinGroupType zmodType.

Definition alg_countType := @Countable.Pack algType (fin_ xclass).
Definition alg_finType := @Finite.Pack algType (fin_ xclass).
Definition alg_baseFinGroupType := base_group algType zmodType finType.
Definition alg_finGroupType := fin_group alg_baseFinGroupType zmodType.
Definition alg_countZmodType := @CountRing.Zmodule.Pack algType xclass.
Definition alg_finZmodType := @Zmodule.Pack algType xclass.
Definition alg_countRingType := @CountRing.Ring.Pack algType xclass.
Definition alg_finRingType := @Ring.Pack algType xclass.
Definition alg_finLmodType := @Lmodule.Pack R phR algType xclass.
Definition alg_finLalgType := @Lalgebra.Pack R phR algType xclass.

End ClassDef.

Module Exports.
Coercion base : class_of >-> GRing.Algebra.class_of.
Coercion base2 : class_of >-> Lalgebra.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion countType : type >-> Countable.type.
Canonical countType.
Coercion finType : type >-> Finite.type.
Canonical finType.
Coercion baseFinGroupType : type >-> FinGroup.base_type.
Canonical baseFinGroupType.
Coercion finGroupType : type >-> FinGroup.type.
Canonical finGroupType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion countZmodType : type >-> CountRing.Zmodule.type.
Canonical countZmodType.
Coercion finZmodType : type >-> Zmodule.type.
Canonical finZmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion countRingType : type >-> CountRing.Ring.type.
Canonical countRingType.
Coercion finRingType : type >-> Ring.type.
Canonical finRingType.
Coercion lmodType : type >-> GRing.Lmodule.type.
Canonical lmodType.
Coercion finLmodType : type >-> Lmodule.type.
Canonical finLmodType.
Coercion lalgType : type >-> GRing.Lalgebra.type.
Canonical lalgType.
Coercion finLalgType : type >-> Lalgebra.type.
Canonical finLalgType.
Coercion algType : type >-> GRing.Algebra.type.
Canonical algType.
Canonical alg_countType.
Canonical alg_finType.
Canonical alg_baseFinGroupType.
Canonical alg_finGroupType.
Canonical alg_countZmodType.
Canonical alg_finZmodType.
Canonical alg_countRingType.
Canonical alg_finRingType.
Canonical alg_finLmodType.
Canonical alg_finLalgType.
Notation finAlgType R := (type (Phant R)).
Notation "[ 'finAlgType' R 'of' T ]" := (do_pack (@pack _ (Phant R)) T)
  (at level 0, format "[ 'finAlgType'  R  'of'  T ]") : form_scope.
End Exports.

End Algebra.
Import Algebra.Exports.

Module UnitAlgebra.

Section ClassDef.

Variable R : unitRingType.

Record class_of M :=
  Class { base : GRing.UnitAlgebra.class_of R M; mixin : mixin_of M base }.
Definition base2 M (c : class_of M) := Algebra.Class (mixin c).
Definition base3 M (c : class_of M) := @UnitRing.Class _ (base c) (mixin c).

Local Coercion base : class_of >-> GRing.UnitAlgebra.class_of.
Local Coercion base2 : class_of >-> Algebra.class_of.
Local Coercion base3 : class_of >-> UnitRing.class_of.

Structure type (phR : phant R) := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (phR : phant R) (cT : type phR).
Definition pack := gen_pack (Pack phR) Class (@GRing.UnitAlgebra.class R phR).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition countType := @Countable.Pack cT (fin_ xclass).
Definition finType := @Finite.Pack cT (fin_ xclass).
Definition zmodType := @GRing.Zmodule.Pack cT xclass.
Definition countZmodType := @CountRing.Zmodule.Pack cT xclass.
Definition finZmodType := @Zmodule.Pack cT xclass.
Definition ringType := @GRing.Ring.Pack cT xclass.
Definition countRingType := @CountRing.Ring.Pack cT xclass.
Definition finRingType := @Ring.Pack cT xclass.
Definition unitRingType := @GRing.UnitRing.Pack cT xclass.
Definition countUnitRingType := @CountRing.UnitRing.Pack cT xclass.
Definition finUnitRingType := @UnitRing.Pack cT xclass.
Definition lmodType := @GRing.Lmodule.Pack R phR cT xclass.
Definition finLmodType := @Lmodule.Pack R phR cT xclass.
Definition lalgType := @GRing.Lalgebra.Pack R phR cT xclass.
Definition finLalgType := @Lalgebra.Pack R phR cT xclass.
Definition algType := @GRing.Algebra.Pack R phR cT xclass.
Definition finAlgType := @Algebra.Pack R phR cT xclass.
Definition unitAlgType := @GRing.UnitAlgebra.Pack R phR cT xclass.
Definition baseFinGroupType := base_group cT zmodType finType.
Definition finGroupType := fin_group baseFinGroupType zmodType.

Definition unitAlg_countType := @Countable.Pack unitAlgType (fin_ xclass).
Definition unitAlg_finType := @Finite.Pack unitAlgType (fin_ xclass).
Definition unitAlg_baseFinGroupType := base_group unitAlgType zmodType finType.
Definition unitAlg_finGroupType := fin_group unitAlg_baseFinGroupType zmodType.
Definition unitAlg_countZmodType := @CountRing.Zmodule.Pack unitAlgType xclass.
Definition unitAlg_finZmodType := @Zmodule.Pack unitAlgType xclass.
Definition unitAlg_countRingType := @CountRing.Ring.Pack unitAlgType xclass.
Definition unitAlg_finRingType := @Ring.Pack unitAlgType xclass.
Definition unitAlg_countUnitRingType :=
  @CountRing.UnitRing.Pack unitAlgType xclass.
Definition unitAlg_finUnitRingType := @UnitRing.Pack unitAlgType xclass.
Definition unitAlg_finLmodType := @Lmodule.Pack R phR unitAlgType xclass.
Definition unitAlg_finLalgType := @Lalgebra.Pack R phR unitAlgType xclass.
Definition unitAlg_finAlgType := @Algebra.Pack R phR unitAlgType xclass.
Definition unitRing_finLmodType := @Lmodule.Pack R phR unitRingType xclass.
Definition unitRing_finLalgType := @Lalgebra.Pack R phR unitRingType xclass.
Definition unitRing_finAlgType := @Algebra.Pack R phR unitRingType xclass.
Definition countUnitRing_lmodType :=
  @GRing.Lmodule.Pack R phR countUnitRingType xclass.
Definition countUnitRing_finLmodType :=
  @Lmodule.Pack R phR countUnitRingType xclass.
Definition countUnitRing_lalgType :=
  @GRing.Lalgebra.Pack R phR countUnitRingType xclass.
Definition countUnitRing_finLalgType :=
  @Lalgebra.Pack R phR countUnitRingType xclass.
Definition countUnitRing_algType :=
  @GRing.Algebra.Pack R phR countUnitRingType xclass.
Definition countUnitRing_finAlgType :=
  @Algebra.Pack R phR countUnitRingType xclass.
Definition finUnitRing_lmodType :=
  @GRing.Lmodule.Pack R phR finUnitRingType xclass.
Definition finUnitRing_finLmodType :=
  @Lmodule.Pack R phR finUnitRingType xclass.
Definition finUnitRing_lalgType :=
  @GRing.Lalgebra.Pack R phR finUnitRingType xclass.
Definition finUnitRing_finLalgType :=
  @Lalgebra.Pack R phR finUnitRingType xclass.
Definition finUnitRing_algType :=
  @GRing.Algebra.Pack R phR finUnitRingType xclass.
Definition finUnitRing_finAlgType :=
  @Algebra.Pack R phR finUnitRingType xclass.

End ClassDef.

Module Exports.
Coercion base : class_of >-> GRing.UnitAlgebra.class_of.
Coercion base2 : class_of >-> Algebra.class_of.
Coercion base3 : class_of >-> UnitRing.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion countType : type >-> Countable.type.
Canonical countType.
Coercion finType : type >-> Finite.type.
Canonical finType.
Coercion baseFinGroupType : type >-> FinGroup.base_type.
Canonical baseFinGroupType.
Coercion finGroupType : type >-> FinGroup.type.
Canonical finGroupType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion countZmodType : type >-> CountRing.Zmodule.type.
Canonical countZmodType.
Coercion finZmodType : type >-> Zmodule.type.
Canonical finZmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion countRingType : type >-> CountRing.Ring.type.
Canonical countRingType.
Coercion finRingType : type >-> Ring.type.
Canonical finRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical unitRingType.
Coercion countUnitRingType : type >-> CountRing.UnitRing.type.
Canonical countUnitRingType.
Coercion finUnitRingType : type >-> UnitRing.type.
Canonical finUnitRingType.
Coercion lmodType : type >-> GRing.Lmodule.type.
Canonical lmodType.
Coercion finLmodType : type >-> Lmodule.type.
Canonical finLmodType.
Coercion lalgType : type >-> GRing.Lalgebra.type.
Canonical lalgType.
Coercion finLalgType : type >-> Lalgebra.type.
Canonical finLalgType.
Coercion algType : type >-> GRing.Algebra.type.
Canonical algType.
Coercion finAlgType : type >-> Algebra.type.
Canonical finAlgType.
Coercion unitAlgType : type >-> GRing.UnitAlgebra.type.
Canonical unitAlgType.
Canonical unitAlg_countType.
Canonical unitAlg_finType.
Canonical unitAlg_baseFinGroupType.
Canonical unitAlg_finGroupType.
Canonical unitAlg_countZmodType.
Canonical unitAlg_finZmodType.
Canonical unitAlg_countRingType.
Canonical unitAlg_finRingType.
Canonical unitAlg_countUnitRingType.
Canonical unitAlg_finUnitRingType.
Canonical unitAlg_finLmodType.
Canonical unitAlg_finLalgType.
Canonical unitAlg_finAlgType.
Canonical unitRing_finLmodType.
Canonical unitRing_finLalgType.
Canonical unitRing_finAlgType.
Canonical countUnitRing_lmodType.
Canonical countUnitRing_finLmodType.
Canonical countUnitRing_lalgType.
Canonical countUnitRing_finLalgType.
Canonical countUnitRing_algType.
Canonical countUnitRing_finAlgType.
Canonical finUnitRing_lmodType.
Canonical finUnitRing_finLmodType.
Canonical finUnitRing_lalgType.
Canonical finUnitRing_finLalgType.
Canonical finUnitRing_algType.
Canonical finUnitRing_finAlgType.
Notation finUnitAlgType R := (type (Phant R)).
Notation "[ 'finUnitAlgType' R 'of' T ]" := (do_pack (@pack _ (Phant R)) T)
  (at level 0, format "[ 'finUnitAlgType'  R  'of'  T ]") : form_scope.
End Exports.

End UnitAlgebra.
Import UnitAlgebra.Exports.

Module Theory.

Definition zmod1gE := zmod1gE.
Definition zmodVgE := zmodVgE.
Definition zmodMgE := zmodMgE.
Definition zmodXgE := zmodXgE.
Definition zmod_mulgC := zmod_mulgC.
Definition zmod_abelian := zmod_abelian.
Definition val_unit1 := val_unit1.
Definition val_unitM := val_unitM.
Definition val_unitX := val_unitX.
Definition val_unitV := val_unitV.
Definition unit_actE := unit_actE.

End Theory.

End FinRing.

Import FinRing.
Export Zmodule.Exports Ring.Exports ComRing.Exports.
Export UnitRing.Exports UnitsGroupExports ComUnitRing.Exports.
Export IntegralDomain.Exports Field.Exports DecField.Exports.
Export Lmodule.Exports Lalgebra.Exports Algebra.Exports UnitAlgebra.Exports.

Notation "{ 'unit' R }" := (unit_of (Phant R))
  (at level 0, format "{ 'unit'  R }") : type_scope.
Prenex Implicits FinRing.uval.
Notation "''U'" := (unit_action _) (at level 8) : action_scope.
Notation "''U'" := (unit_groupAction _) (at level 8) : groupAction_scope.

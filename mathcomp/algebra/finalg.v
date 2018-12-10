(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype.
From mathcomp
Require Import ssralg finset fingroup morphism perm action countalg.

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

Definition join_finType := @Finite.Pack zmodType (fin_ xclass).

Definition baseFinGroupType := base_group cT zmodType finType.
Definition finGroupType := fin_group baseFinGroupType zmodType.
Definition join_baseFinGroupType := base_group zmodType zmodType finType.
Definition join_finGroupType := fin_group join_baseFinGroupType zmodType.

End ClassDef.

Module Exports.
Coercion base : class_of >-> GRing.Zmodule.class_of.
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
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Canonical join_finType.
Notation finZmodType := type.
Notation "[ 'finZmodType' 'of' T ]" := (do_pack pack T)
  (at level 0, format "[ 'finZmodType'  'of'  T ]") : form_scope.
Coercion baseFinGroupType : type >-> FinGroup.base_type.
Canonical baseFinGroupType.
Coercion finGroupType : type >-> FinGroup.type.
Canonical finGroupType.
Canonical join_baseFinGroupType.
Canonical join_finGroupType.
Notation "[ 'baseFinGroupType' 'of' R 'for' +%R ]" :=
    (BaseFinGroupType R (groupMixin _))
  (at level 0, format "[ 'baseFinGroupType'  'of'  R  'for'  +%R ]")
    : form_scope.
Notation "[ 'finGroupType' 'of' R 'for' +%R ]" :=
    (@FinGroup.clone R _ (finGroupType _) id _ id)
  (at level 0, format "[ 'finGroupType'  'of'  R  'for'  +%R ]") : form_scope.
Canonical countZmodType (T : type) := [countZmodType of T].
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
Definition base2 R (c : class_of R) := Zmodule.Class (mixin c).
Local Coercion base : class_of >-> GRing.Ring.class_of.
Local Coercion base2 : class_of >-> Zmodule.class_of.

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
Definition finZmodType := @Zmodule.Pack cT xclass.
Definition ringType := @GRing.Ring.Pack cT xclass.
Definition join_finType := @Finite.Pack ringType (fin_ xclass).
Definition join_finZmodType := @Zmodule.Pack ringType xclass.

Definition baseFinGroupType := base_group cT zmodType finType.
Definition finGroupType := fin_group baseFinGroupType zmodType.
Definition join_baseFinGroupType := base_group ringType zmodType finType.
Definition join_finGroupType := fin_group join_baseFinGroupType zmodType.

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> GRing.Ring.class_of.
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
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion finZmodType : type >-> Zmodule.type.
Canonical finZmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Canonical join_finType.
Canonical join_finZmodType.
Notation finRingType := type.
Notation "[ 'finRingType' 'of' T ]" := (do_pack pack T)
  (at level 0, format "[ 'finRingType'  'of'  T ]") : form_scope.
Canonical baseFinGroupType.
Canonical finGroupType.
Canonical join_baseFinGroupType.
Canonical join_finGroupType.
Canonical countZmodType (T : type) := [countZmodType of T].
Canonical countRingType (T : type) := [countRingType of T].
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
Definition base2 R (c : class_of R) := Ring.Class (mixin c).
Local Coercion base : class_of >-> GRing.ComRing.class_of.
Local Coercion base2 : class_of >-> Ring.class_of.

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
Definition finZmodType := @Zmodule.Pack cT xclass.
Definition ringType := @GRing.Ring.Pack cT xclass.
Definition finRingType := @Ring.Pack cT xclass.
Definition comRingType := @GRing.ComRing.Pack cT xclass.
Definition join_finType := @Finite.Pack comRingType (fin_ xclass).
Definition join_finZmodType := @Zmodule.Pack comRingType xclass.
Definition join_finRingType := @Ring.Pack comRingType xclass.

Definition baseFinGroupType := base_group cT zmodType finType.
Definition finGroupType := fin_group baseFinGroupType zmodType.
Definition join_baseFinGroupType := base_group comRingType zmodType finType.
Definition join_finGroupType := fin_group join_baseFinGroupType zmodType.

End ClassDef.

Module Exports.
Coercion base : class_of >-> GRing.ComRing.class_of.
Coercion base2 : class_of >-> Ring.class_of.
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
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion finZmodType : type >-> Zmodule.type.
Canonical finZmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion finRingType : type >-> Ring.type.
Canonical finRingType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical comRingType.
Canonical join_finType.
Canonical join_finZmodType.
Canonical join_finRingType.
Notation finComRingType := FinRing.ComRing.type.
Notation "[ 'finComRingType' 'of' T ]" := (do_pack pack T)
  (at level 0, format "[ 'finComRingType'  'of'  T ]") : form_scope.
Canonical baseFinGroupType.
Canonical finGroupType.
Canonical join_baseFinGroupType.
Canonical join_finGroupType.
Canonical countZmodType (T : type) := [countZmodType of T].
Canonical countRingType (T : type) := [countRingType of T].
Canonical countComRingType (T : type) := [countComRingType of T].
End Exports.

End ComRing.
Import ComRing.Exports.

Module UnitRing.

Section ClassDef.

Record class_of R :=
  Class { base : GRing.UnitRing.class_of R; mixin : mixin_of R base }.
Definition base2 R (c : class_of R) := Ring.Class (mixin c).
Local Coercion base : class_of >-> GRing.UnitRing.class_of.
Local Coercion base2 : class_of >-> Ring.class_of.

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
Definition finZmodType := @Zmodule.Pack cT xclass.
Definition ringType := @GRing.Ring.Pack cT xclass.
Definition finRingType := @Ring.Pack cT xclass.
Definition unitRingType := @GRing.UnitRing.Pack cT xclass.

Definition join_finType := @Finite.Pack unitRingType (fin_ xclass).
Definition join_finZmodType := @Zmodule.Pack unitRingType xclass.
Definition join_finRingType := @Ring.Pack unitRingType xclass.

Definition baseFinGroupType := base_group cT zmodType finType.
Definition finGroupType := fin_group baseFinGroupType zmodType.
Definition join_baseFinGroupType := base_group unitRingType zmodType finType.
Definition join_finGroupType := fin_group join_baseFinGroupType zmodType.

End ClassDef.

Module Exports.
Coercion base : class_of >-> GRing.UnitRing.class_of.
Coercion base2 : class_of >-> Ring.class_of.
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
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion finZmodType : type >-> Zmodule.type.
Canonical finZmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion finRingType : type >-> Ring.type.
Canonical finRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical unitRingType.
Canonical join_finType.
Canonical join_finZmodType.
Canonical join_finRingType.
Notation finUnitRingType := FinRing.UnitRing.type.
Notation "[ 'finUnitRingType' 'of' T ]" := (do_pack pack T)
  (at level 0, format "[ 'finUnitRingType'  'of'  T ]") : form_scope.
Canonical baseFinGroupType.
Canonical finGroupType.
Canonical join_baseFinGroupType.
Canonical join_finGroupType.
Canonical countZmodType (T : type) := [countZmodType of T].
Canonical countRingType (T : type) := [countRingType of T].
Canonical countUnitRingType (T : type) := [countUnitRingType of T].
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
Definition base2 R (c : class_of R) := ComRing.Class (mixin c).
Definition base3 R (c : class_of R) := @UnitRing.Class R (base c) (mixin c).
Local Coercion base : class_of >-> GRing.ComUnitRing.class_of.
Local Coercion base2 : class_of >-> ComRing.class_of.
Local Coercion base3 : class_of >-> UnitRing.class_of.

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
Definition finZmodType := @Zmodule.Pack cT xclass.
Definition ringType := @GRing.Ring.Pack cT xclass.
Definition finRingType := @Ring.Pack cT xclass.
Definition comRingType := @GRing.ComRing.Pack cT xclass.
Definition finComRingType := @ComRing.Pack cT xclass.
Definition unitRingType := @GRing.UnitRing.Pack cT xclass.
Definition finUnitRingType := @UnitRing.Pack cT xclass.
Definition comUnitRingType := @GRing.ComUnitRing.Pack cT xclass.

Definition join_finType := @Finite.Pack comUnitRingType (fin_ xclass).
Definition join_finZmodType := @Zmodule.Pack comUnitRingType xclass.
Definition join_finRingType := @Ring.Pack comUnitRingType xclass.
Definition join_finComRingType := @ComRing.Pack comUnitRingType xclass.
Definition join_finUnitRingType := @UnitRing.Pack comUnitRingType xclass.
Definition ujoin_finComRingType := @ComRing.Pack unitRingType xclass.
Definition cjoin_finUnitRingType := @UnitRing.Pack comRingType xclass.
Definition fcjoin_finUnitRingType := @UnitRing.Pack finComRingType xclass.

Definition baseFinGroupType := base_group cT zmodType finType.
Definition finGroupType := fin_group baseFinGroupType zmodType.
Definition join_baseFinGroupType := base_group comUnitRingType zmodType finType.
Definition join_finGroupType := fin_group join_baseFinGroupType zmodType.

End ClassDef.

Module Exports.
Coercion base : class_of >-> GRing.ComUnitRing.class_of.
Coercion base2 : class_of >-> ComRing.class_of.
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
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion finZmodType : type >-> Zmodule.type.
Canonical finZmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion finRingType : type >-> Ring.type.
Canonical finRingType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical comRingType.
Coercion finComRingType : type >-> ComRing.type.
Canonical finComRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical unitRingType.
Coercion finUnitRingType : type >-> UnitRing.type.
Canonical finUnitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical comUnitRingType.
Canonical join_finType.
Canonical join_finZmodType.
Canonical join_finRingType.
Canonical join_finComRingType.
Canonical join_finUnitRingType.
Canonical ujoin_finComRingType.
Canonical cjoin_finUnitRingType.
Canonical fcjoin_finUnitRingType.
Notation finComUnitRingType := FinRing.ComUnitRing.type.
Notation "[ 'finComUnitRingType' 'of' T ]" := (do_pack pack T)
  (at level 0, format "[ 'finComUnitRingType'  'of'  T ]") : form_scope.
Canonical baseFinGroupType.
Canonical finGroupType.
Canonical join_baseFinGroupType.
Canonical join_finGroupType.
Canonical countZmodType (T : type) := [countZmodType of T].
Canonical countRingType (T : type) := [countRingType of T].
Canonical countUnitRingType (T : type) := [countUnitRingType of T].
Canonical countComRingType (T : type) := [countComRingType of T].
Canonical countComUnitRingType (T : type) := [countComUnitRingType of T].
End Exports.

End ComUnitRing.
Import ComUnitRing.Exports.

Module IntegralDomain.

Section ClassDef.

Record class_of R :=
  Class { base : GRing.IntegralDomain.class_of R; mixin : mixin_of R base }.
Definition base2 R (c : class_of R) := ComUnitRing.Class (mixin c).
Local Coercion base : class_of >-> GRing.IntegralDomain.class_of.
Local Coercion base2 : class_of >-> ComUnitRing.class_of.

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
Definition finZmodType := @Zmodule.Pack cT xclass.
Definition ringType := @GRing.Ring.Pack cT xclass.
Definition finRingType := @Ring.Pack cT xclass.
Definition comRingType := @GRing.ComRing.Pack cT xclass.
Definition finComRingType := @ComRing.Pack cT xclass.
Definition unitRingType := @GRing.UnitRing.Pack cT xclass.
Definition finUnitRingType := @UnitRing.Pack cT xclass.
Definition comUnitRingType := @GRing.ComUnitRing.Pack cT xclass.
Definition finComUnitRingType := @ComUnitRing.Pack cT xclass.
Definition idomainType := @GRing.IntegralDomain.Pack cT xclass.

Definition join_finType := @Finite.Pack idomainType (fin_ xclass).
Definition join_finZmodType := @Zmodule.Pack idomainType xclass.
Definition join_finRingType := @Ring.Pack idomainType xclass.
Definition join_finUnitRingType := @UnitRing.Pack idomainType xclass.
Definition join_finComRingType := @ComRing.Pack idomainType xclass.
Definition join_finComUnitRingType := @ComUnitRing.Pack idomainType xclass.

Definition baseFinGroupType := base_group cT zmodType finType.
Definition finGroupType := fin_group baseFinGroupType zmodType.
Definition join_baseFinGroupType := base_group idomainType zmodType finType.
Definition join_finGroupType := fin_group join_baseFinGroupType zmodType.

End ClassDef.

Module Exports.
Coercion base : class_of >-> GRing.IntegralDomain.class_of.
Coercion base2 : class_of >-> ComUnitRing.class_of.
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
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion finZmodType : type >-> Zmodule.type.
Canonical finZmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion finRingType : type >-> Ring.type.
Canonical finRingType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical comRingType.
Coercion finComRingType : type >-> ComRing.type.
Canonical finComRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical unitRingType.
Coercion finUnitRingType : type >-> UnitRing.type.
Canonical finUnitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical comUnitRingType.
Coercion finComUnitRingType : type >-> ComUnitRing.type.
Canonical finComUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical idomainType.
Canonical join_finType.
Canonical join_finZmodType.
Canonical join_finRingType.
Canonical join_finComRingType.
Canonical join_finUnitRingType.
Canonical join_finComUnitRingType.
Notation finIdomainType := FinRing.IntegralDomain.type.
Notation "[ 'finIdomainType' 'of' T ]" := (do_pack pack T)
  (at level 0, format "[ 'finIdomainType'  'of'  T ]") : form_scope.
Canonical baseFinGroupType.
Canonical finGroupType.
Canonical join_baseFinGroupType.
Canonical join_finGroupType.
Canonical countZmodType (T : type) := [countZmodType of T].
Canonical countRingType (T : type) := [countRingType of T].
Canonical countUnitRingType (T : type) := [countUnitRingType of T].
Canonical countComRingType (T : type) := [countComRingType of T].
Canonical countComUnitRingType (T : type) := [countComUnitRingType of T].
Canonical countIdomainType (T : type) := [countIdomainType of T].
End Exports.

End IntegralDomain.
Import IntegralDomain.Exports.

Module Field.

Section ClassDef.

Record class_of R :=
  Class { base : GRing.Field.class_of R; mixin : mixin_of R base }.
Definition base2 R (c : class_of R) := IntegralDomain.Class (mixin c).
Local Coercion base : class_of >-> GRing.Field.class_of.
Local Coercion base2 : class_of >-> IntegralDomain.class_of.

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
Definition finZmodType := @Zmodule.Pack cT xclass.
Definition ringType := @GRing.Ring.Pack cT xclass.
Definition finRingType := @Ring.Pack cT xclass.
Definition comRingType := @GRing.ComRing.Pack cT xclass.
Definition finComRingType := @ComRing.Pack cT xclass.
Definition unitRingType := @GRing.UnitRing.Pack cT xclass.
Definition finUnitRingType := @UnitRing.Pack cT xclass.
Definition comUnitRingType := @GRing.ComUnitRing.Pack cT xclass.
Definition finComUnitRingType := @ComUnitRing.Pack cT xclass.
Definition idomainType := @GRing.IntegralDomain.Pack cT xclass.
Definition finIdomainType := @IntegralDomain.Pack cT xclass.
Definition fieldType := @GRing.Field.Pack cT xclass.

Definition join_finType := @Finite.Pack fieldType (fin_ xclass).
Definition join_finZmodType := @Zmodule.Pack fieldType xclass.
Definition join_finRingType := @Ring.Pack fieldType xclass.
Definition join_finUnitRingType := @UnitRing.Pack fieldType xclass.
Definition join_finComRingType := @ComRing.Pack fieldType xclass.
Definition join_finComUnitRingType := @ComUnitRing.Pack fieldType xclass.
Definition join_finIdomainType := @IntegralDomain.Pack fieldType xclass.

Definition baseFinGroupType := base_group cT zmodType finType.
Definition finGroupType := fin_group baseFinGroupType zmodType.
Definition join_baseFinGroupType := base_group fieldType zmodType finType.
Definition join_finGroupType := fin_group join_baseFinGroupType zmodType.

End ClassDef.

Module Exports.
Coercion base : class_of >-> GRing.Field.class_of.
Coercion base2 : class_of >-> IntegralDomain.class_of.
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
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion finZmodType : type >-> Zmodule.type.
Canonical finZmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion finRingType : type >-> Ring.type.
Canonical finRingType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical comRingType.
Coercion finComRingType : type >-> ComRing.type.
Canonical finComRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical unitRingType.
Coercion finUnitRingType : type >-> UnitRing.type.
Canonical finUnitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical comUnitRingType.
Coercion finComUnitRingType : type >-> ComUnitRing.type.
Canonical finComUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical idomainType.
Coercion finIdomainType : type >-> IntegralDomain.type.
Canonical finIdomainType.
Coercion fieldType : type >-> GRing.Field.type.
Canonical fieldType.
Canonical join_finType.
Canonical join_finZmodType.
Canonical join_finRingType.
Canonical join_finComRingType.
Canonical join_finUnitRingType.
Canonical join_finComUnitRingType.
Canonical join_finIdomainType.
Notation finFieldType := FinRing.Field.type.
Notation "[ 'finFieldType' 'of' T ]" := (do_pack pack T)
  (at level 0, format "[ 'finFieldType'  'of'  T ]") : form_scope.
Canonical baseFinGroupType.
Canonical finGroupType.
Canonical join_baseFinGroupType.
Canonical join_finGroupType.
Canonical countZmodType (T : type) := [countZmodType of T].
Canonical countRingType (T : type) := [countRingType of T].
Canonical countUnitRingType (T : type) := [countUnitRingType of T].
Canonical countComRingType (T : type) := [countComRingType of T].
Canonical countComUnitRingType (T : type) := [countComUnitRingType of T].
Canonical countIdomainType (T : type) := [countIdomainType of T].
Canonical countFieldType (T : type) := [countFieldType of T].
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
Definition base2 R (c : class_of R) := Zmodule.Class (mixin c).
Local Coercion base : class_of >-> GRing.Lmodule.class_of.
Local Coercion base2 : class_of >-> Zmodule.class_of.

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
Definition finZmodType := @Zmodule.Pack cT xclass.
Definition lmodType := @GRing.Lmodule.Pack R phR cT xclass.
Definition join_finType := @Finite.Pack lmodType (fin_ xclass).
Definition join_finZmodType := @Zmodule.Pack lmodType xclass.

Definition baseFinGroupType := base_group cT zmodType finType.
Definition finGroupType := fin_group baseFinGroupType zmodType.
Definition join_baseFinGroupType := base_group lmodType zmodType finType.
Definition join_finGroupType := fin_group join_baseFinGroupType zmodType.

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
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion finZmodType : type >-> Zmodule.type.
Canonical finZmodType.
Coercion lmodType : type >-> GRing.Lmodule.type.
Canonical lmodType.
Canonical join_finType.
Canonical join_finZmodType.
Notation finLmodType R := (FinRing.Lmodule.type (Phant R)).
Notation "[ 'finLmodType' R 'of' T ]" := (do_pack (@pack _ (Phant R)) T)
  (at level 0, format "[ 'finLmodType'  R  'of'  T ]") : form_scope.
Canonical baseFinGroupType.
Canonical finGroupType.
Canonical join_baseFinGroupType.
Canonical join_finGroupType.
Section counttype.
Variables (R : ringType) (phR : phant R) (T : type phR).
Canonical countZmodType := [countZmodType of T].
End counttype.
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
Definition finZmodType := @Zmodule.Pack cT xclass.
Definition ringType := @GRing.Ring.Pack cT xclass.
Definition finRingType := @Ring.Pack cT xclass.
Definition lmodType := @GRing.Lmodule.Pack R phR cT xclass.
Definition finLmodType := @Lmodule.Pack R phR cT xclass.
Definition lalgType := @GRing.Lalgebra.Pack R phR cT xclass.

Definition join_finType := @Finite.Pack lalgType (fin_ xclass).
Definition join_finZmodType := @Zmodule.Pack lalgType xclass.
Definition join_finLmodType := @Lmodule.Pack R phR lalgType xclass.
Definition join_finRingType := @Ring.Pack lalgType xclass.
Definition rjoin_finLmodType := @Lmodule.Pack R phR ringType xclass.
Definition ljoin_finRingType := @Ring.Pack lmodType xclass.
Definition fljoin_finRingType := @Ring.Pack finLmodType xclass.

Definition baseFinGroupType := base_group cT zmodType finType.
Definition finGroupType := fin_group baseFinGroupType zmodType.
Definition join_baseFinGroupType := base_group lalgType zmodType finType.
Definition join_finGroupType := fin_group join_baseFinGroupType zmodType.

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
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion finZmodType : type >-> Zmodule.type.
Canonical finZmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion finRingType : type >-> Ring.type.
Canonical finRingType.
Coercion lmodType : type >-> GRing.Lmodule.type.
Canonical lmodType.
Coercion finLmodType : type >-> Lmodule.type.
Canonical finLmodType.
Coercion lalgType : type >-> GRing.Lalgebra.type.
Canonical lalgType.
Canonical join_finType.
Canonical join_finZmodType.
Canonical join_finLmodType.
Canonical join_finRingType.
Canonical rjoin_finLmodType.
Canonical ljoin_finRingType.
Canonical fljoin_finRingType.
Notation finLalgType R := (FinRing.Lalgebra.type (Phant R)).
Notation "[ 'finLalgType' R 'of' T ]" := (do_pack (@pack _ (Phant R)) T)
  (at level 0, format "[ 'finLalgType'  R  'of'  T ]") : form_scope.
Canonical baseFinGroupType.
Canonical finGroupType.
Canonical join_baseFinGroupType.
Canonical join_finGroupType.
Section counttype.
Variables (R : GRing.Ring.type) (phR : phant R) (T : type phR).
Canonical countZmodType := [countZmodType of T].
Canonical countRingType := [countRingType of T].
End counttype.
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
Definition finZmodType := @Zmodule.Pack cT xclass.
Definition ringType := @GRing.Ring.Pack cT xclass.
Definition finRingType := @Ring.Pack cT xclass.
Definition lmodType := @GRing.Lmodule.Pack R phR cT xclass.
Definition finLmodType := @Lmodule.Pack R phR cT xclass.
Definition lalgType := @GRing.Lalgebra.Pack R phR cT xclass.
Definition finLalgType := @Lalgebra.Pack R phR cT xclass.
Definition algType := @GRing.Algebra.Pack R phR cT xclass.

Definition join_finType := @Finite.Pack algType (fin_ xclass).
Definition join_finZmodType := @Zmodule.Pack algType xclass.
Definition join_finRingType := @Ring.Pack algType xclass.
Definition join_finLmodType := @Lmodule.Pack R phR algType xclass.
Definition join_finLalgType := @Lalgebra.Pack R phR algType xclass.

Definition baseFinGroupType := base_group cT zmodType finType.
Definition finGroupType := fin_group baseFinGroupType zmodType.
Definition join_baseFinGroupType := base_group algType zmodType finType.
Definition join_finGroupType := fin_group join_baseFinGroupType zmodType.

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
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion finZmodType : type >-> Zmodule.type.
Canonical finZmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
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
Canonical join_finType.
Canonical join_finZmodType.
Canonical join_finLmodType.
Canonical join_finRingType.
Canonical join_finLalgType.
Notation finAlgType R := (type (Phant R)).
Notation "[ 'finAlgType' R 'of' T ]" := (do_pack (@pack _ (Phant R)) T)
  (at level 0, format "[ 'finAlgType'  R  'of'  T ]") : form_scope.
Canonical baseFinGroupType.
Canonical finGroupType.
Canonical join_baseFinGroupType.
Canonical join_finGroupType.
Section counttype.
Variables (R : GRing.Ring.type) (phR : phant R) (T : type phR).
Canonical countZmodType := [countZmodType of T].
Canonical countRingType := [countRingType of T].
End counttype.
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
Definition finZmodType := @Zmodule.Pack cT xclass.
Definition ringType := @GRing.Ring.Pack cT xclass.
Definition finRingType := @Ring.Pack cT xclass.
Definition unitRingType := @GRing.UnitRing.Pack cT xclass.
Definition finUnitRingType := @UnitRing.Pack cT xclass.
Definition lmodType := @GRing.Lmodule.Pack R phR cT xclass.
Definition finLmodType := @Lmodule.Pack R phR cT xclass.
Definition lalgType := @GRing.Lalgebra.Pack R phR cT xclass.
Definition finLalgType := @Lalgebra.Pack R phR cT xclass.
Definition algType := @GRing.Algebra.Pack R phR cT xclass.
Definition finAlgType := @Algebra.Pack R phR cT xclass.
Definition unitAlgType := @GRing.UnitAlgebra.Pack R phR cT xclass.

Definition join_finType := @Finite.Pack unitAlgType (fin_ xclass).
Definition join_finZmodType := @Zmodule.Pack unitAlgType xclass.
Definition join_finRingType := @Ring.Pack unitAlgType xclass.
Definition join_finUnitRingType := @UnitRing.Pack unitAlgType xclass.
Definition join_finLmodType := @Lmodule.Pack R phR unitAlgType xclass.
Definition join_finLalgType := @Lalgebra.Pack R phR unitAlgType xclass.
Definition join_finAlgType := @Algebra.Pack R phR unitAlgType xclass.
Definition  ljoin_finUnitRingType := @UnitRing.Pack lmodType xclass.
Definition fljoin_finUnitRingType := @UnitRing.Pack finLmodType xclass.
Definition  njoin_finUnitRingType := @UnitRing.Pack lalgType xclass.
Definition fnjoin_finUnitRingType := @UnitRing.Pack finLalgType xclass.
Definition  ajoin_finUnitRingType := @UnitRing.Pack algType xclass.
Definition fajoin_finUnitRingType := @UnitRing.Pack finAlgType xclass.
Definition ujoin_finLmodType := @Lmodule.Pack R phR unitRingType xclass.
Definition ujoin_finLalgType := @Lalgebra.Pack R phR unitRingType xclass.
Definition ujoin_finAlgType := @Algebra.Pack R phR unitRingType xclass.

Definition baseFinGroupType := base_group cT zmodType finType.
Definition finGroupType := fin_group baseFinGroupType zmodType.
Definition join_baseFinGroupType := base_group unitAlgType zmodType finType.
Definition join_finGroupType := fin_group join_baseFinGroupType zmodType.

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
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion finZmodType : type >-> Zmodule.type.
Canonical finZmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion finRingType : type >-> Ring.type.
Canonical finRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical unitRingType.
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
Canonical join_finType.
Canonical join_finZmodType.
Canonical join_finLmodType.
Canonical join_finRingType.
Canonical join_finLalgType.
Canonical join_finAlgType.
Canonical ljoin_finUnitRingType.
Canonical fljoin_finUnitRingType.
Canonical njoin_finUnitRingType.
Canonical fnjoin_finUnitRingType.
Canonical ajoin_finUnitRingType.
Canonical fajoin_finUnitRingType.
Canonical ujoin_finLmodType.
Canonical ujoin_finLalgType.
Canonical ujoin_finAlgType.
Notation finUnitAlgType R := (type (Phant R)).
Notation "[ 'finUnitAlgType' R 'of' T ]" := (do_pack (@pack _ (Phant R)) T)
  (at level 0, format "[ 'finUnitAlgType'  R  'of'  T ]") : form_scope.
Canonical baseFinGroupType.
Canonical finGroupType.
Canonical join_baseFinGroupType.
Canonical join_finGroupType.
Section counttype.
Variables (R : GRing.UnitRing.type) (phR : phant R) (T : type phR).
Canonical countZmodType := [countZmodType of T].
Canonical countRingType := [countRingType of T].
Canonical countUnitRingType := [countUnitRingType of T].
End counttype.
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

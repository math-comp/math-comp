(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
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

(* Local Notation mixin_of T b := (Finite.mixin_of (EqType T b)). *)

(* Section Generic. *)

(* (* Implicits *) *)
(* Variables (type base_type : Type) (class_of base_of : Type -> Type). *)
(* Variable to_choice : forall T, base_of T -> Choice.class_of T. *)
(* Variable base_sort : base_type -> Type. *)

(* (* Explicits *) *)
(* Variable Pack : forall T, class_of T -> type. *)
(* Variable Class : forall T b, mixin_of T (to_choice b) -> class_of T. *)
(* Variable base_class : forall bT, base_of (base_sort bT). *)

(* Definition gen_pack T := *)
(*   fun bT b & phant_id (base_class bT) b => *)
(*   fun fT m & phant_id (Finite.class fT) (Finite.Class m) => *)
(*   Pack (@Class T b m). *)

(* End Generic. *)

(* Arguments gen_pack [type base_type class_of base_of to_choice base_sort]. *)
(* Local Notation fin_ c := (@Finite.Class _ c c). *)
(* Local Notation do_pack pack T := (pack T _ _ id _ _ id). *)
Import GRing.Theory.

(* Definition groupMixin V := FinGroup.Mixin (@addrA V) (@add0r V) (@addNr V). *)
(* Local Notation base_group T vT fT := *)
(*   (@FinGroup.PackBase T (groupMixin vT) (Finite.class fT)). *)
(* Local Notation fin_group B V := (@FinGroup.Pack B (@addNr V)). *)

#[mathcomp]
HB.structure Definition Zmodule := {M of GRing.Zmodule M & Finite M}.

HB.instance Definition _ (R : Zmodule.type) :=
  IsMulGroup.Build R (@addrA R) (@add0r R) (@addNr R).
Coercion Zmodule_to_baseFinGroup (R : Zmodule.type) := BaseFinGroup.clone R _.
Coercion Zmodule_to_finGroup (R : Zmodule.type) := FinGroup.clone R _.
(* FIXME (c.f. branch hierarchy-builder-finalg) *)

Module ZmoduleExports.
Notation finZmodType := Zmodule.type.
Notation "[ 'finZmodType' 'of' T ]" := (Zmodule.clone T _)
  (at level 0, format "[ 'finZmodType'  'of'  T ]") : form_scope.
Notation "[ 'finGroupMixin' 'of' R 'for' +%R ]" :=
    (IsMulGroup.Build R (@addrA R) (@add0r R) (@addNr R))
  (at level 0, format "[ 'finGroupMixin'  'of'  R  'for'  +%R ]") : form_scope.
End ZmoduleExports.
HB.export ZmoduleExports.

Section AdditiveGroup.

Variable U : finZmodType.
Implicit Types x y : U.

Lemma zmod1gE : 1%g = 0 :> U.            Proof. by []. Qed.
Lemma zmodVgE x : x^-1%g = - x.          Proof. by []. Qed.
Lemma zmodMgE x y : (x * y)%g = x + y.   Proof. by []. Qed.
Lemma zmodXgE n x : (x ^+ n)%g = x *+ n. Proof. by []. Qed.
Lemma zmod_mulgC x y : commute x y.      Proof. exact: addrC. Qed.
Lemma zmod_abelian (A : {set U}) : abelian A.
Proof. by apply/centsP=> x _ y _; apply: zmod_mulgC. Qed.

End AdditiveGroup.

#[mathcomp]
HB.structure Definition Ring := {R of GRing.Ring R & Finite R}.

HB.instance Definition _ (R : Ring.type) :=
  IsMulGroup.Build R (@addrA R) (@add0r R) (@addNr R).
Coercion Ring_to_baseFinGroup (R : Ring.type) := BaseFinGroup.clone R _.
Coercion Ring_to_finGroup (R : Ring.type) := FinGroup.clone R _.

Module RingExports.
Notation finRingType := Ring.type.
Notation "[ 'finRingType' 'of' T ]" := (Ring.clone T _)
  (at level 0, format "[ 'finRingType'  'of'  T ]") : form_scope.
End RingExports.
HB.export RingExports.

HB.factory Record IsRing R of Ring R := {}.

HB.builders Context R of IsRing R.
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

  HB.instance Definition _ :=
    GRing.Ring_HasMulInverse.Build R mulVr mulrV intro_unit invr_out.
HB.end.

#[mathcomp]
HB.structure Definition ComRing := {R of GRing.ComRing R & Finite R}.

HB.instance Definition _ (R : ComRing.type) :=
  IsMulGroup.Build R (@addrA R) (@add0r R) (@addNr R).
Coercion ComRing_to_baseFinGroup (R : ComRing.type) := BaseFinGroup.clone R _.
Coercion ComRing_to_finGroup (R : ComRing.type) := FinGroup.clone R _.

Module ComRingExports.
Notation finComRingType := ComRing.type.
Notation "[ 'finComRingType' 'of' T ]" := (ComRing.clone T _)
  (at level 0, format "[ 'finComRingType'  'of'  T ]") : form_scope.
End ComRingExports.
HB.export ComRingExports.

#[mathcomp]
HB.structure Definition UnitRing := {R of GRing.UnitRing R & Finite R}.

HB.instance Definition _ (R : UnitRing.type) :=
  IsMulGroup.Build R (@addrA R) (@add0r R) (@addNr R).
Coercion UnitRing_to_baseFinGroup (R : UnitRing.type) := BaseFinGroup.clone R _.
Coercion UnitRing_to_finGroup (R : UnitRing.type) := FinGroup.clone R _.

Module UnitRingExports.
Notation finUnitRingType := UnitRing.type.
Notation "[ 'finUnitRingType' 'of' T ]" := (UnitRing.clone T _)
  (at level 0, format "[ 'finUnitRingType'  'of'  T ]") : form_scope.
End UnitRingExports.
HB.export UnitRingExports.

Section UnitsGroup.

Variable R : finUnitRingType.

Inductive unit_of (phR : phant R) := Unit (x : R) of x \is a GRing.unit.
Bind Scope group_scope with unit_of.

Let phR := Phant R.
Local Notation uT := (unit_of phR).
Implicit Types u v : uT.
Definition uval u := let: Unit x _ := u in x.

#[export]
HB.instance Definition _ := [subMixin for uval].
#[export]
HB.instance Definition _ := [Finite of uT by <:].

Definition unit1 := Unit phR (@GRing.unitr1 _).
Lemma unit_inv_proof u : (val u)^-1 \is a GRing.unit.
Proof. by rewrite unitrV ?(valP u). Qed.
Definition unit_inv u := Unit phR (unit_inv_proof u).
Lemma unit_mul_proof u v : val u * val v \is a GRing.unit.
Proof. by rewrite (unitrMr _ (valP u)) ?(valP v). Qed.
Definition unit_mul u v := Unit phR (unit_mul_proof u v).
Lemma unit_muluA : associative unit_mul.
Proof. by move=> u v w; apply/val_inj/mulrA. Qed.
Lemma unit_mul1u : left_id unit1 unit_mul.
Proof. by move=> u; apply/val_inj/mul1r. Qed.
Lemma unit_mulVu : left_inverse unit1 unit_inv unit_mul.
Proof. by move=> u; apply/val_inj/(mulVr (valP u)). Qed.

#[export]
HB.instance Definition _ :=
  IsMulGroup.Build uT unit_muluA unit_mul1u unit_mulVu.

Lemma val_unit1 : val (1%g : uT) = 1. Proof. by []. Qed.
Lemma val_unitM x y : val (x * y : uT)%g = val x * val y. Proof. by []. Qed.
Lemma val_unitV x : val (x^-1 : uT)%g = (val x)^-1. Proof. by []. Qed.
Lemma val_unitX n x : val (x ^+ n : uT)%g = val x ^+ n.
Proof. by case: n; last by elim=> //= n ->. Qed.

Definition unit_act x u := x * val u.
Lemma unit_actE x u : unit_act x u = x * val u. Proof. by []. Qed.

Canonical unit_action :=
  @TotalAction _ _ unit_act (@mulr1 _) (fun _ _ _ => mulrA _ _ _).

Lemma unit_is_groupAction : @is_groupAction _ R setT setT unit_action.
Proof.
move=> u _ /=; rewrite inE; apply/andP; split.
  by apply/subsetP=> x _; rewrite inE.
by apply/morphicP=> x y _ _; rewrite !actpermE /= [_ u]mulrDl.
Qed.
Canonical unit_groupAction := GroupAction unit_is_groupAction.

End UnitsGroup.

Module Import UnitsGroupExports.
Bind Scope group_scope with unit_of.
Canonical unit_action.
Canonical unit_groupAction.
End UnitsGroupExports.

Notation unit R Ux := (Unit (Phant R) Ux).

#[mathcomp]
HB.structure Definition ComUnitRing := {R of GRing.ComUnitRing R & Finite R}.

HB.instance Definition _ (R : ComUnitRing.type) :=
  IsMulGroup.Build R (@addrA R) (@add0r R) (@addNr R).
Coercion ComUnitRing_to_baseFinGroup (R : ComUnitRing.type) :=
  BaseFinGroup.clone R _.
Coercion ComUnitRing_to_finGroup (R : ComUnitRing.type) :=
  FinGroup.clone R _.

Module ComUnitRingExports.
Notation finComUnitRingType := ComUnitRing.type.
Notation "[ 'finComUnitRingType' 'of' T ]" := (ComUnitRing.clone T _)
  (at level 0, format "[ 'finComUnitRingType'  'of'  T ]") : form_scope.
End ComUnitRingExports.
HB.export ComUnitRingExports.

#[mathcomp]
HB.structure Definition IntegralDomain :=
  {R of GRing.IntegralDomain R & Finite R}.

HB.instance Definition _ (R : IntegralDomain.type) :=
  IsMulGroup.Build R (@addrA R) (@add0r R) (@addNr R).
Coercion IntegralDomain_to_baseFinGroup (R : IntegralDomain.type) :=
  BaseFinGroup.clone R _.
Coercion IntegralDomain_to_finGroup (R : IntegralDomain.type) :=
  FinGroup.clone R _.

Module IntegralDomainExports.
Notation finIntegralDomainType := IntegralDomain.type.
Notation "[ 'finIntegralDomainType' 'of' T ]" := (IntegralDomain.clone T _)
  (at level 0, format "[ 'finIntegralDomainType'  'of'  T ]") : form_scope.
End IntegralDomainExports.
HB.export IntegralDomainExports.

#[mathcomp]
HB.structure Definition Field := {R of GRing.Field R & Finite R}.

HB.instance Definition _ (R : Field.type) :=
  IsMulGroup.Build R (@addrA R) (@add0r R) (@addNr R).
Coercion Field_to_baseFinGroup (R : Field.type) := BaseFinGroup.clone R _.
Coercion Field_to_finGroup (R : Field.type) := FinGroup.clone R _.

Module FieldExports.
Notation finFieldType := Field.type.
Notation "[ 'finFieldType' 'of' T ]" := (Field.clone T _)
  (at level 0, format "[ 'finFieldType'  'of'  T ]") : form_scope.
End FieldExports.
HB.export FieldExports.

HB.factory Record IsField F of Field F := {}.

HB.builders Context F of IsField F.
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

  (* FIXME : we would have expected GRing.DecidableField.axiom *)
  Lemma decidable : GRing.decidable_field_axiom sat.
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

  HB.instance Definition _ := GRing.UnitRing_IsDec.Build F decidable.
HB.end.

(* STOP

#[mathcomp, infer(R)]
HB.structure Definition Lmodule (R : ringType) :=
  {M of GRing.Lmodule R M & Finite M}.

Check   IsMulGroup.Build M (@addrA M) (@add0r M) (@addNr M).


HB.instance Definition _ (R : ringType) (M : Lmodule.type R) :=
  IsMulGroup.Build (Lmodule.sort M) (@addrA M) (@add0r M) (@addNr M).
(* FIXME doesn't work with M instead of (Finite.sort M) *)
Set Printing All.
Coercion Lmodule_to_baseFinGroup (R : ringType) (M : Lmodule.type R) :=
  BaseFinGroup.clone M _.
Coercion Lmodule_to_finGroup (R : Lmodule.type) := FinGroup.clone R _.

Module FieldExports.
Notation finFieldType := Field.type.
Notation "[ 'finFieldType' 'of' T ]" := (Field.clone T _)
  (at level 0, format "[ 'finFieldType'  'of'  T ]") : form_scope.
End FieldExports.
HB.export FieldExports.





Module Lmodule.

Section ClassDef.

Variable R : ringType.

Set Primitive Projections.
Record class_of M :=
  Class { base : GRing.Lmodule.class_of R M; mixin : mixin_of M base }.
Unset Primitive Projections.
Local Coercion base : class_of >-> GRing.Lmodule.class_of.
Local Coercion base2 R (c : class_of R) : Zmodule.class_of R :=
  Zmodule.Class (mixin c).

Structure type (phR : phant R) := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (phR : phant R) (cT : type phR).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition pack := gen_pack (Pack phR) Class (@GRing.Lmodule.class R phR).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
(* Definition countType := @Countable.Pack cT (fin_ class). *)
Definition finType := @Finite.Pack cT (fin_ class).
Definition zmodType := @GRing.Zmodule.Pack cT class.
(* Definition countZmodType := @CountRing.Zmodule.Pack cT class. *)
Definition finZmodType := @Zmodule.Pack cT class.
Definition lmodType := @GRing.Lmodule.Pack R phR cT class.
Definition baseFinGroupType := base_group cT zmodType finType.
Definition finGroupType := fin_group baseFinGroupType zmodType.

(* Definition lmod_countType := @Countable.Pack lmodType (fin_ class). *)
Definition lmod_finType := @Finite.Pack lmodType (fin_ class).
Definition lmod_baseFinGroupType := base_group lmodType zmodType finType.
Definition lmod_finGroupType := fin_group lmod_baseFinGroupType zmodType.
(* Definition lmod_countZmodType := @CountRing.Zmodule.Pack lmodType class. *)
Definition lmod_finZmodType := @Zmodule.Pack lmodType class.

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
(* Coercion countType : type >-> Countable.type. *)
(* Canonical countType. *)
Coercion finType : type >-> Finite.type.
Canonical finType.
Coercion baseFinGroupType : type >-> FinGroup.base_type.
Canonical baseFinGroupType.
Coercion finGroupType : type >-> FinGroup.type.
Canonical finGroupType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
(* Coercion countZmodType : type >-> CountRing.Zmodule.type. *)
(* Canonical countZmodType. *)
Coercion finZmodType : type >-> Zmodule.type.
Canonical finZmodType.
Coercion lmodType : type >-> GRing.Lmodule.type.
Canonical lmodType.
(* Canonical lmod_countType. *)
Canonical lmod_finType.
Canonical lmod_baseFinGroupType.
Canonical lmod_finGroupType.
(* Canonical lmod_countZmodType. *)
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

Set Primitive Projections.
Record class_of M :=
  Class { base : GRing.Lalgebra.class_of R M; mixin : mixin_of M base }.
Unset Primitive Projections.
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

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
(* Definition countType := @Countable.Pack cT (fin_ class). *)
Definition finType := @Finite.Pack cT (fin_ class).
Definition zmodType := @GRing.Zmodule.Pack cT class.
(* Definition countZmodType := @CountRing.Zmodule.Pack cT class. *)
Definition finZmodType := @Zmodule.Pack cT class.
Definition ringType := @GRing.Ring.Pack cT class.
(* Definition countRingType := @CountRing.Ring.Pack cT class. *)
Definition finRingType := @Ring.Pack cT class.
Definition lmodType := @GRing.Lmodule.Pack R phR cT class.
Definition finLmodType := @Lmodule.Pack R phR cT class.
Definition lalgType := @GRing.Lalgebra.Pack R phR cT class.
Definition baseFinGroupType := base_group cT zmodType finType.
Definition finGroupType := fin_group baseFinGroupType zmodType.

(* Definition lalg_countType := @Countable.Pack lalgType (fin_ class). *)
Definition lalg_finType := @Finite.Pack lalgType (fin_ class).
Definition lalg_baseFinGroupType := base_group lalgType zmodType finType.
Definition lalg_finGroupType := fin_group lalg_baseFinGroupType zmodType.
(* Definition lalg_countZmodType := @CountRing.Zmodule.Pack lalgType class. *)
Definition lalg_finZmodType := @Zmodule.Pack lalgType class.
Definition lalg_finLmodType := @Lmodule.Pack R phR lalgType class.
(* Definition lalg_countRingType := @CountRing.Ring.Pack lalgType class. *)
Definition lalg_finRingType := @Ring.Pack lalgType class.
(* Definition lmod_countRingType := @CountRing.Ring.Pack lmodType class. *)
Definition lmod_finRingType := @Ring.Pack lmodType class.
Definition finLmod_ringType := @GRing.Ring.Pack finLmodType class.
(* Definition finLmod_countRingType := @CountRing.Ring.Pack finLmodType class. *)
Definition finLmod_finRingType := @Ring.Pack finLmodType class.

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
(* Coercion countType : type >-> Countable.type. *)
(* Canonical countType. *)
Coercion finType : type >-> Finite.type.
Canonical finType.
Coercion baseFinGroupType : type >-> FinGroup.base_type.
Canonical baseFinGroupType.
Coercion finGroupType : type >-> FinGroup.type.
Canonical finGroupType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
(* Coercion countZmodType : type >-> CountRing.Zmodule.type. *)
(* Canonical countZmodType. *)
Coercion finZmodType : type >-> Zmodule.type.
Canonical finZmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
(* Coercion countRingType : type >-> CountRing.Ring.type. *)
(* Canonical countRingType. *)
Coercion finRingType : type >-> Ring.type.
Canonical finRingType.
Coercion lmodType : type >-> GRing.Lmodule.type.
Canonical lmodType.
Coercion finLmodType : type >-> Lmodule.type.
Canonical finLmodType.
Coercion lalgType : type >-> GRing.Lalgebra.type.
Canonical lalgType.
(* Canonical lalg_countType. *)
Canonical lalg_finType.
Canonical lalg_baseFinGroupType.
Canonical lalg_finGroupType.
(* Canonical lalg_countZmodType. *)
Canonical lalg_finZmodType.
Canonical lalg_finLmodType.
(* Canonical lalg_countRingType. *)
Canonical lalg_finRingType.
(* Canonical lmod_countRingType. *)
Canonical lmod_finRingType.
Canonical finLmod_ringType.
(* Canonical finLmod_countRingType. *)
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

Set Primitive Projections.
Record class_of M :=
  Class { base : GRing.Algebra.class_of R M; mixin : mixin_of M base }.
Unset Primitive Projections.
Definition base2 M (c : class_of M) := Lalgebra.Class (mixin c).
Local Coercion base : class_of >-> GRing.Algebra.class_of.
Local Coercion base2 : class_of >->Lalgebra.class_of.

Structure type (phR : phant R) := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (phR : phant R) (cT : type phR).
Definition pack := gen_pack (Pack phR) Class (@GRing.Algebra.class R phR).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
(* Definition countType := @Countable.Pack cT (fin_ class). *)
Definition finType := @Finite.Pack cT (fin_ class).
Definition zmodType := @GRing.Zmodule.Pack cT class.
(* Definition countZmodType := @CountRing.Zmodule.Pack cT class. *)
Definition finZmodType := @Zmodule.Pack cT class.
Definition ringType := @GRing.Ring.Pack cT class.
(* Definition countRingType := @CountRing.Ring.Pack cT class. *)
Definition finRingType := @Ring.Pack cT class.
Definition lmodType := @GRing.Lmodule.Pack R phR cT class.
Definition finLmodType := @Lmodule.Pack R phR cT class.
Definition lalgType := @GRing.Lalgebra.Pack R phR cT class.
Definition finLalgType := @Lalgebra.Pack R phR cT class.
Definition algType := @GRing.Algebra.Pack R phR cT class.
Definition baseFinGroupType := base_group cT zmodType finType.
Definition finGroupType := fin_group baseFinGroupType zmodType.

(* Definition alg_countType := @Countable.Pack algType (fin_ class). *)
Definition alg_finType := @Finite.Pack algType (fin_ class).
Definition alg_baseFinGroupType := base_group algType zmodType finType.
Definition alg_finGroupType := fin_group alg_baseFinGroupType zmodType.
(* Definition alg_countZmodType := @CountRing.Zmodule.Pack algType class. *)
Definition alg_finZmodType := @Zmodule.Pack algType class.
(* Definition alg_countRingType := @CountRing.Ring.Pack algType class. *)
Definition alg_finRingType := @Ring.Pack algType class.
Definition alg_finLmodType := @Lmodule.Pack R phR algType class.
Definition alg_finLalgType := @Lalgebra.Pack R phR algType class.

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
(* Coercion countType : type >-> Countable.type. *)
(* Canonical countType. *)
Coercion finType : type >-> Finite.type.
Canonical finType.
Coercion baseFinGroupType : type >-> FinGroup.base_type.
Canonical baseFinGroupType.
Coercion finGroupType : type >-> FinGroup.type.
Canonical finGroupType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
(* Coercion countZmodType : type >-> CountRing.Zmodule.type. *)
(* Canonical countZmodType. *)
Coercion finZmodType : type >-> Zmodule.type.
Canonical finZmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
(* Coercion countRingType : type >-> CountRing.Ring.type. *)
(* Canonical countRingType. *)
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
(* Canonical alg_countType. *)
Canonical alg_finType.
Canonical alg_baseFinGroupType.
Canonical alg_finGroupType.
(* Canonical alg_countZmodType. *)
Canonical alg_finZmodType.
(* Canonical alg_countRingType. *)
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

Set Primitive Projections.
Record class_of M :=
  Class { base : GRing.UnitAlgebra.class_of R M; mixin : mixin_of M base }.
Unset Primitive Projections.
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

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
(* Definition countType := @Countable.Pack cT (fin_ class). *)
Definition finType := @Finite.Pack cT (fin_ class).
Definition zmodType := @GRing.Zmodule.Pack cT class.
(* Definition countZmodType := @CountRing.Zmodule.Pack cT class. *)
Definition finZmodType := @Zmodule.Pack cT class.
Definition ringType := @GRing.Ring.Pack cT class.
(* Definition countRingType := @CountRing.Ring.Pack cT class. *)
Definition finRingType := @Ring.Pack cT class.
Definition unitRingType := @GRing.UnitRing.Pack cT class.
(* Definition countUnitRingType := @CountRing.UnitRing.Pack cT class. *)
Definition finUnitRingType := @UnitRing.Pack cT class.
Definition lmodType := @GRing.Lmodule.Pack R phR cT class.
Definition finLmodType := @Lmodule.Pack R phR cT class.
Definition lalgType := @GRing.Lalgebra.Pack R phR cT class.
Definition finLalgType := @Lalgebra.Pack R phR cT class.
Definition algType := @GRing.Algebra.Pack R phR cT class.
Definition finAlgType := @Algebra.Pack R phR cT class.
Definition unitAlgType := @GRing.UnitAlgebra.Pack R phR cT class.
Definition baseFinGroupType := base_group cT zmodType finType.
Definition finGroupType := fin_group baseFinGroupType zmodType.

(* Definition unitAlg_countType := @Countable.Pack unitAlgType (fin_ class). *)
Definition unitAlg_finType := @Finite.Pack unitAlgType (fin_ class).
Definition unitAlg_baseFinGroupType := base_group unitAlgType zmodType finType.
Definition unitAlg_finGroupType := fin_group unitAlg_baseFinGroupType zmodType.
(* Definition unitAlg_countZmodType := @CountRing.Zmodule.Pack unitAlgType class. *)
Definition unitAlg_finZmodType := @Zmodule.Pack unitAlgType class.
(* Definition unitAlg_countRingType := @CountRing.Ring.Pack unitAlgType class. *)
Definition unitAlg_finRingType := @Ring.Pack unitAlgType class.
(* Definition unitAlg_countUnitRingType := *)
  (* @CountRing.UnitRing.Pack unitAlgType class. *)
Definition unitAlg_finUnitRingType := @UnitRing.Pack unitAlgType class.
Definition unitAlg_finLmodType := @Lmodule.Pack R phR unitAlgType class.
Definition unitAlg_finLalgType := @Lalgebra.Pack R phR unitAlgType class.
Definition unitAlg_finAlgType := @Algebra.Pack R phR unitAlgType class.
Definition unitRing_finLmodType := @Lmodule.Pack R phR unitRingType class.
Definition unitRing_finLalgType := @Lalgebra.Pack R phR unitRingType class.
Definition unitRing_finAlgType := @Algebra.Pack R phR unitRingType class.
(* Definition countUnitRing_lmodType := *)
  (* @GRing.Lmodule.Pack R phR countUnitRingType class. *)
(* Definition countUnitRing_finLmodType := *)
  (* @Lmodule.Pack R phR countUnitRingType class. *)
(* Definition countUnitRing_lalgType := *)
  (* @GRing.Lalgebra.Pack R phR countUnitRingType class. *)
(* Definition countUnitRing_finLalgType := *)
  (* @Lalgebra.Pack R phR countUnitRingType class. *)
(* Definition countUnitRing_algType := *)
  (* @GRing.Algebra.Pack R phR countUnitRingType class. *)
(* Definition countUnitRing_finAlgType := *)
  (* @Algebra.Pack R phR countUnitRingType class. *)
Definition finUnitRing_lmodType :=
  @GRing.Lmodule.Pack R phR finUnitRingType class.
Definition finUnitRing_finLmodType :=
  @Lmodule.Pack R phR finUnitRingType class.
Definition finUnitRing_lalgType :=
  @GRing.Lalgebra.Pack R phR finUnitRingType class.
Definition finUnitRing_finLalgType :=
  @Lalgebra.Pack R phR finUnitRingType class.
Definition finUnitRing_algType :=
  @GRing.Algebra.Pack R phR finUnitRingType class.
Definition finUnitRing_finAlgType :=
  @Algebra.Pack R phR finUnitRingType class.

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
(* Coercion countType : type >-> Countable.type. *)
(* Canonical countType. *)
Coercion finType : type >-> Finite.type.
Canonical finType.
Coercion baseFinGroupType : type >-> FinGroup.base_type.
Canonical baseFinGroupType.
Coercion finGroupType : type >-> FinGroup.type.
Canonical finGroupType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
(* Coercion countZmodType : type >-> CountRing.Zmodule.type. *)
(* Canonical countZmodType. *)
Coercion finZmodType : type >-> Zmodule.type.
Canonical finZmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
(* Coercion countRingType : type >-> CountRing.Ring.type. *)
(* Canonical countRingType. *)
Coercion finRingType : type >-> Ring.type.
Canonical finRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical unitRingType.
(* Coercion countUnitRingType : type >-> CountRing.UnitRing.type. *)
(* Canonical countUnitRingType. *)
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
(* Canonical unitAlg_countType. *)
Canonical unitAlg_finType.
Canonical unitAlg_baseFinGroupType.
Canonical unitAlg_finGroupType.
(* Canonical unitAlg_countZmodType. *)
Canonical unitAlg_finZmodType.
(* Canonical unitAlg_countRingType. *)
Canonical unitAlg_finRingType.
(* Canonical unitAlg_countUnitRingType. *)
Canonical unitAlg_finUnitRingType.
Canonical unitAlg_finLmodType.
Canonical unitAlg_finLalgType.
Canonical unitAlg_finAlgType.
Canonical unitRing_finLmodType.
Canonical unitRing_finLalgType.
Canonical unitRing_finAlgType.
(* Canonical countUnitRing_lmodType. *)
(* Canonical countUnitRing_finLmodType. *)
(* Canonical countUnitRing_lalgType. *)
(* Canonical countUnitRing_finLalgType. *)
(* Canonical countUnitRing_algType. *)
(* Canonical countUnitRing_finAlgType. *)
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

 *)

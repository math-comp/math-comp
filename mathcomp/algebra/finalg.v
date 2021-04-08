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
HB.export UnitsGroupExports.

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

  HB.instance Definition _ := GRing.Field_IsDec.Build F decidable.
HB.end.

#[mathcomp, infer(R)]
HB.structure Definition Lmodule (R : ringType) :=
  {M of GRing.Lmodule R M & Finite M}.

(* FIXME
HB.instance Definition _ (R : ringType) (M : Lmodule.type R) :=
  IsMulGroup.Build M (@addrA M) (@add0r M) (@addNr M).
Coercion Lmodule_to_baseFinGroup (R : ringType) (M : Lmodule.type R) :=
  BaseFinGroup.clone M _.
Coercion Lmodule_to_finGroup (R : ringType) (M : Lmodule.type R) :=
  FinGroup.clone M _.
*)

Module LmoduleExports.
Notation finLmodType R := (Lmodule.type R).
Notation "[ 'finLmodType' 'of' T ]" := (Lmodule.clone _ T _)
  (at level 0, format "[ 'finLmodType'  'of'  T ]") : form_scope.
End LmoduleExports.
HB.export LmoduleExports.

#[mathcomp, infer(R)]
HB.structure Definition Lalgebra (R : ringType) :=
  {M of GRing.Lalgebra R M & Finite M}.

(* FIXME
HB.instance Definition _ (R : ringType) (M : Lalgebra.type R) :=
  IsMulGroup.Build M (@addrA M) (@add0r M) (@addNr M).
Coercion Lalgebra_to_baseFinGroup (R : ringType) (M : Lalgebra.type R) :=
  BaseFinGroup.clone M _.
Coercion Lalgebra_to_finGroup (R : ringType) (M : Lalgebra.type R) :=
  FinGroup.clone M _.
*)

Module LalgebraExports.
Notation finLalgType R := (Lalgebra.type R).
Notation "[ 'finLalgType' 'of' T ]" := (Lalgebra.clone _ T _)
  (at level 0, format "[ 'finLalgType'  'of'  T ]") : form_scope.
End LalgebraExports.
HB.export LalgebraExports.

#[mathcomp, infer(R)]
HB.structure Definition Algebra (R : ringType) :=
  {M of GRing.Algebra R M & Finite M}.

(* FIXME
HB.instance Definition _ (R : ringType) (M : Algebra.type R) :=
  IsMulGroup.Build M (@addrA M) (@add0r M) (@addNr M).
Coercion Lalgebra_to_baseFinGroup (R : ringType) (M : Algebra.type R) :=
  BaseFinGroup.clone M _.
Coercion Lalgebra_to_finGroup (R : ringType) (M : Algebra.type R) :=
  FinGroup.clone M _.
*)

Module AlgebraExports.
Notation finAlgType R := (Algebra.type R).
Notation "[ 'finAlgType' 'of' T ]" := (Algebra.clone _ T _)
  (at level 0, format "[ 'finAlgType'  'of'  T ]") : form_scope.
End AlgebraExports.
HB.export AlgebraExports.

#[mathcomp, infer(R)]
HB.structure Definition UnitAlgebra (R : unitRingType) :=
  {M of GRing.UnitAlgebra R M & Finite M}.

(* FIXME
HB.instance Definition _ (R : unitRingType) (M : UnitAlgebra.type R) :=
  IsMulGroup.Build M (@addrA M) (@add0r M) (@addNr M).
Coercion Lalgebra_to_baseFinGroup (R : unitRingType) (M : UnitAlgebra.type R) :=
  BaseFinGroup.clone M _.
Coercion Lalgebra_to_finGroup (R : unitRingType) (M : UnitAlgebra.type R) :=
  FinGroup.clone M _.
*)

Module UnitAlgebraExports.
Notation finUnitAlgType R := (UnitAlgebra.type R).
Notation "[ 'finUnitAlgType' 'of' T ]" := (UnitAlgebra.clone _ T _)
  (at level 0, format "[ 'finUnitAlgType'  'of'  T ]") : form_scope.
End UnitAlgebraExports.
HB.export UnitAlgebraExports.

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
HB.reexport.

Notation "{ 'unit' R }" := (unit_of (Phant R))
  (at level 0, format "{ 'unit'  R }") : type_scope.
Prenex Implicits FinRing.uval.
Notation "''U'" := (unit_action _) (at level 8) : action_scope.
Notation "''U'" := (unit_groupAction _) (at level 8) : groupAction_scope.

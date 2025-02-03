(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype finset fingroup morphism perm action.
From mathcomp Require Import monoid ssralg countalg.

(*****************************************************************************)
(*      The algebraic part of the algebraic hierarchy for finite types       *)
(*                                                                           *)
(* This file clones the entire ssralg hierarchy for finite types; this       *)
(* allows type inference to function properly on expressions that mix        *)
(* combinatorial and algebraic operators, e.g., [set x + y | x in A, y in A].*)
(*                                                                           *)
(*   finNmodType, finZmodType, finNzSemiRingType, finNzRingType,             *)
(*   finComNzRingType, finComNzSemiRingType, finUnitRingType,                *)
(*   finComUnitRingType, finIdomType, finFieldType, finLmodType,             *)
(*   finLalgType, finAlgType, finUnitAlgType                                 *)
(*      == the finite counterparts of nmodType, etc                          *)
(* Note that a finFieldType is canonically decidable.                        *)
(*   This file also provides direct tie-ins with finite group theory:        *)
(*     [finGroupMixin of R for +%R] == structures for R                      *)
(*                         {unit R} == the type of units of R, which has a   *)
(*                                     canonical group structure             *)
(*                FinRing.unit R Ux == the element of {unit R}               *)
(*                                     corresponding to x,                   *)
(*                                     where Ux : x \in GRing.unit           *)
(*                           'U%act == the action by right multiplication of *)
(*                                     {unit R} on R, via FinRing.unit_act   *)
(*                                     (This is also a group action.)        *)
(*****************************************************************************)

Local Open Scope ring_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module FinRing.

Import GRing.Theory.

#[short(type="finNmodType")]
HB.structure Definition Nmodule := {M of GRing.Nmodule M & Finite M}.

#[short(type="finZmodType")]
HB.structure Definition Zmodule := {M of GRing.Zmodule M & Finite M}.

Module ZmoduleExports.
Notation "[ 'finGroupMixin' 'of' R 'for' +%R ]" :=
    (isMulGroup.Build R (@addrA _) (@add0r _) (@addNr _))
  (at level 0, format "[ 'finGroupMixin'  'of'  R  'for'  +%R ]") : form_scope.
End ZmoduleExports.
HB.export ZmoduleExports.

#[short(type="finNzSemiRingType")]
HB.structure Definition NzSemiRing := {R of GRing.NzSemiRing R & Finite R}.

#[deprecated(since="mathcomp 2.4.0",
             note="Use FinNzSemiRing instead.")]
Notation SemiRing R := (NzSemiRing R) (only parsing).

Module SemiRing.
#[deprecated(since="mathcomp 2.4.0",
             note="Use NzSemiRing.sort instead.")]
Notation sort := (NzSemiRing.sort) (only parsing).
#[deprecated(since="mathcomp 2.4.0",
             note="Use NzSemiRing.on instead.")]
Notation on R := (NzSemiRing.on R) (only parsing).
#[deprecated(since="mathcomp 2.4.0",
             note="Use NzSemiRing.copy instead.")]
Notation copy T U := (NzSemiRing.copy T U) (only parsing).
End SemiRing.

#[short(type="finNzRingType")]
HB.structure Definition NzRing := {R of GRing.NzRing R & Finite R}.

#[deprecated(since="mathcomp 2.4.0",
             note="Use FinNzRing instead.")]
Notation Ring R := (NzRing R) (only parsing).

Module Ring.
#[deprecated(since="mathcomp 2.4.0",
             note="Use NzRing.sort instead.")]
Notation sort := (NzRing.sort) (only parsing).
#[deprecated(since="mathcomp 2.4.0",
             note="Use NzRing.on instead.")]
Notation on R := (NzRing.on R) (only parsing).
#[deprecated(since="mathcomp 2.4.0",
             note="Use NzRing.copy instead.")]
Notation copy T U := (NzRing.copy T U) (only parsing).
End Ring.

#[short(type="finComNzSemiRingType")]
HB.structure Definition ComNzSemiRing :=
  {R of GRing.ComNzSemiRing R & Finite R}.

#[deprecated(since="mathcomp 2.4.0",
             note="Use FinComNzSemiRing instead.")]
Notation ComSemiRing R := (ComNzSemiRing R) (only parsing).

Module ComSemiRing.
#[deprecated(since="mathcomp 2.4.0",
             note="Use ComNzSemiRing.sort instead.")]
Notation sort := (ComNzSemiRing.sort) (only parsing).
#[deprecated(since="mathcomp 2.4.0",
             note="Use ComNzSemiRing.on instead.")]
Notation on R := (ComNzSemiRing.on R) (only parsing).
#[deprecated(since="mathcomp 2.4.0",
             note="Use ComNzSemiRing.copy instead.")]
Notation copy T U := (ComNzSemiRing.copy T U) (only parsing).
End ComSemiRing.

#[short(type="finComNzRingType")]
HB.structure Definition ComNzRing := {R of GRing.ComNzRing R & Finite R}.

#[deprecated(since="mathcomp 2.4.0",
             note="Use FinComNzRing instead.")]
Notation ComRing R := (ComNzRing R) (only parsing).

Module ComRing.
#[deprecated(since="mathcomp 2.4.0",
             note="Use ComNzRing.sort instead.")]
Notation sort := (ComNzRing.sort) (only parsing).
#[deprecated(since="mathcomp 2.4.0",
             note="Use ComNzRing.on instead.")]
Notation on R := (ComNzRing.on R) (only parsing).
#[deprecated(since="mathcomp 2.4.0",
             note="Use ComNzRing.copy instead.")]
Notation copy T U := (ComNzRing.copy T U) (only parsing).
End ComRing.

#[short(type="finUnitRingType")]
HB.structure Definition UnitRing := {R of GRing.UnitRing R & Finite R}.

#[short(type="finComUnitRingType")]
HB.structure Definition ComUnitRing := {R of GRing.ComUnitRing R & Finite R}.

#[short(type="finIdomainType")]
HB.structure Definition IntegralDomain :=
  {R of GRing.IntegralDomain R & Finite R}.

#[short(type="finFieldType")]
HB.structure Definition Field := {R of GRing.Field R & Finite R}.

#[short(type="finLmodType")]
HB.structure Definition Lmodule (R : nzRingType) :=
  {M of GRing.Lmodule R M & Finite M}.

#[short(type="finLalgType")]
HB.structure Definition Lalgebra (R : nzRingType) :=
  {M of GRing.Lalgebra R M & Finite M}.

#[short(type="finAlgType")]
HB.structure Definition Algebra (R : nzRingType) :=
  {M of GRing.Algebra R M & Finite M}.

#[short(type="finUnitAlgType")]
HB.structure Definition UnitAlgebra (R : unitRingType) :=
  {M of GRing.UnitAlgebra R M & Finite M}.

(* Group structures *)

#[export, non_forgetful_inheritance]
HB.instance Definition _ (R : Zmodule.type) := [finGroupMixin of R for +%R].
Coercion Zmodule_to_baseFinGroup (R : Zmodule.type) := BaseFinGroup.clone R _.
Coercion Zmodule_to_finGroup (R : Zmodule.type) := FinGroup.clone R _.

Section AdditiveGroup.

Variable U : finZmodType.
Implicit Types x y : U.

Lemma zmod1gE : 1%g = 0 :> U.            Proof. by []. Qed.
Lemma zmodVgE x : x^-1%g = - x.          Proof. by []. Qed.
Lemma zmodMgE x y : (x * y)%g = x + y.   Proof. by []. Qed.
Lemma zmodXgE n x : (x ^+ n)%g = x *+ n. Proof. by []. Qed.
Lemma zmod_mulgC x y : @commute (comoid.GRing.to_multiplicative U) x y.
Proof. exact: addrC. Qed.
Lemma zmod_abelian (A : {set U}) : abelian A.
Proof. by apply/centsP=> x _ y _; apply: zmod_mulgC. Qed.

End AdditiveGroup.

#[export, non_forgetful_inheritance]
HB.instance Definition _ (R : NzRing.type) := [finGroupMixin of R for +%R].
Coercion NzRing_to_baseFinGroup (R : NzRing.type) := BaseFinGroup.clone R _.
Coercion NzRing_to_finGroup (R : NzRing.type) := FinGroup.clone R _.

HB.factory Record isNzRing R of NzRing R := {}.

Module isRing.
#[deprecated(since="mathcomp 2.4.0",
             note="Use isNzRing.Build instead.")]
Notation Build R := (isNzRing.Build R) (only parsing).
End isRing.

#[deprecated(since="mathcomp 2.4.0",
             note="Use isNzRing instead.")]
Notation isRing R := (isNzRing R) (only parsing).

HB.builders Context R of isNzRing R.
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
    GRing.NzRing_hasMulInverse.Build R mulVr mulrV intro_unit invr_out.
HB.end.

#[export, non_forgetful_inheritance]
HB.instance Definition _ (R : ComNzRing.type) := [finGroupMixin of R for +%R].
Coercion ComNzRing_to_baseFinGroup (R : ComNzRing.type) :=
  BaseFinGroup.clone R _.
Coercion ComNzRing_to_finGroup (R : ComNzRing.type) := FinGroup.clone R _.


#[export, non_forgetful_inheritance]
HB.instance Definition _ (R : UnitRing.type) := [finGroupMixin of R for +%R].
Coercion UnitRing_to_baseFinGroup (R : UnitRing.type) := BaseFinGroup.clone R _.
Coercion UnitRing_to_finGroup (R : UnitRing.type) := FinGroup.clone R _.

Section UnitsGroup.

Variable R : finUnitRingType.

Inductive unit_of := Unit (x : R) of x \is a GRing.unit.
Bind Scope group_scope with unit_of.

Implicit Types u v : unit_of.
Definition uval u := let: Unit x _ := u in x.

#[export] HB.instance Definition _ := [isSub for uval].
#[export] HB.instance Definition _ := [Finite of unit_of by <:].

Definition unit1 := Unit (@GRing.unitr1 _).
Lemma unit_inv_proof u : (val u)^-1 \is a GRing.unit.
Proof. by rewrite unitrV ?(valP u). Qed.
Definition unit_inv u := Unit (unit_inv_proof u).
Lemma unit_mul_proof u v : val u * val v \is a GRing.unit.
Proof. by rewrite (unitrMr _ (valP u)) ?(valP v). Qed.
Definition unit_mul u v := Unit (unit_mul_proof u v).
Lemma unit_muluA : associative unit_mul.
Proof. by move=> u v w; apply/val_inj/mulrA. Qed.
Lemma unit_mul1u : left_id unit1 unit_mul.
Proof. by move=> u; apply/val_inj/mul1r. Qed.
Lemma unit_mulVu : left_inverse unit1 unit_inv unit_mul.
Proof. by move=> u; apply/val_inj/(mulVr (valP u)). Qed.

#[export] HB.instance Definition _ := isMulGroup.Build unit_of
  unit_muluA unit_mul1u unit_mulVu.

Lemma val_unit1 : val (1%g : unit_of) = 1. Proof. by []. Qed.
Lemma val_unitM x y : val (x * y : unit_of)%g = val x * val y.
Proof. by []. Qed.
Lemma val_unitV x : val (x^-1 : unit_of)%g = (val x)^-1. Proof. by []. Qed.
Lemma val_unitX n x : val (x ^+ n : unit_of)%g = val x ^+ n.
Proof. by case: n; last by elim=> //= n ->. Qed.

Definition unit_act x u := x * val u.
Lemma unit_actE x u : unit_act x u = x * val u. Proof. by []. Qed.

Canonical unit_action :=
  @TotalAction _ _ unit_act (@mulr1 _) (fun _ _ _ => mulrA _ _ _).

Lemma unit_is_groupAction : @is_groupAction _ R setT setT unit_action.
Proof.
move=> u _ /[1!inE]; apply/andP; split; first by apply/subsetP=> x /[1!inE].
by apply/morphicP=> x y _ _; rewrite !actpermE /= [_ u]mulrDl.
Qed.
Canonical unit_groupAction := GroupAction unit_is_groupAction.

End UnitsGroup.

Module Import UnitsGroupExports.
Bind Scope group_scope with unit_of.
Arguments unit_of R%type.
Canonical unit_action.
Canonical unit_groupAction.
End UnitsGroupExports.
HB.export UnitsGroupExports.

Notation unit R Ux := (@Unit R%type _ Ux).

#[export, non_forgetful_inheritance]
HB.instance Definition _ (R : ComUnitRing.type) := [finGroupMixin of R for +%R].
Coercion ComUnitRing_to_baseFinGroup (R : ComUnitRing.type) :=
  BaseFinGroup.clone R _.
Coercion ComUnitRing_to_finGroup (R : ComUnitRing.type) :=
  FinGroup.clone R _.

#[export, non_forgetful_inheritance]
HB.instance Definition _ (R : IntegralDomain.type) :=
  [finGroupMixin of R for +%R].
Coercion IntegralDomain_to_baseFinGroup (R : IntegralDomain.type) :=
  BaseFinGroup.clone R _.
Coercion IntegralDomain_to_finGroup (R : IntegralDomain.type) :=
  FinGroup.clone R _.

#[export, non_forgetful_inheritance]
HB.instance Definition _ (R : Field.type) := [finGroupMixin of R for +%R].
Coercion Field_to_baseFinGroup (R : Field.type) := BaseFinGroup.clone R _.
Coercion Field_to_finGroup (R : Field.type) := FinGroup.clone R _.

HB.factory Record isField F of Field F := {}.

HB.builders Context F of isField F.
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

  HB.instance Definition _ := GRing.Field_isDecField.Build F decidable.
HB.end.

#[export, non_forgetful_inheritance]
HB.instance Definition _ (R : nzRingType) (M : Lmodule.type R) :=
  [finGroupMixin of M for +%R].

Coercion Lmodule_to_baseFinGroup (R : nzRingType) (M : Lmodule.type R) :=
  BaseFinGroup.clone M _.
Coercion Lmodule_to_finGroup (R : nzRingType) (M : Lmodule.type R)
    : finGroupType :=
  FinGroup.clone (M : Type) _.

#[export, non_forgetful_inheritance]
HB.instance Definition _ (R : nzRingType) (M : Lalgebra.type R) :=
  [finGroupMixin of M for +%R].
Coercion Lalgebra_to_baseFinGroup (R : nzRingType) (M : Lalgebra.type R) :=
  BaseFinGroup.clone M _.
Coercion Lalgebra_to_finGroup (R : nzRingType) (M : Lalgebra.type R) :=
  FinGroup.clone M _.

#[export, non_forgetful_inheritance]
HB.instance Definition _ (R : nzRingType) (M : Algebra.type R) :=
  [finGroupMixin of M for +%R].
Coercion Algebra_to_baseFinGroup (R : nzRingType) (M : Algebra.type R) :=
  BaseFinGroup.clone M _.
Coercion Algebra_to_finGroup (R : nzRingType) (M : Algebra.type R) :=
  FinGroup.clone M _.

#[export, non_forgetful_inheritance]
HB.instance Definition _ (R : unitRingType) (M : UnitAlgebra.type R) :=
  [finGroupMixin of M for +%R].
Coercion UnitAlgebra_to_baseFinGroup
  (R : unitRingType) (M : UnitAlgebra.type R) := BaseFinGroup.clone M _.
Coercion UnitAlgebra_to_finGroup (R : unitRingType) (M : UnitAlgebra.type R) :=
  FinGroup.clone M _.

Module RegularExports.
HB.instance Definition _ (R : finZmodType) := Zmodule.on R^o.
HB.instance Definition _ (R : finNzRingType) := NzRing.on R^o.
HB.instance Definition _ (R : finComNzRingType) := NzRing.on R^o.
HB.instance Definition _ (R : finUnitRingType) := NzRing.on R^o.
HB.instance Definition _ (R : finComUnitRingType) := NzRing.on R^o.
HB.instance Definition _ (R : finIdomainType) := NzRing.on R^o.
HB.instance Definition _ (R : finFieldType) := NzRing.on R^o.
End RegularExports.
HB.export RegularExports.

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

#[deprecated(since="mathcomp 2.4.0",
             note="Use finNzSemiRingType instead.")]
Notation finSemiRingType := (finNzSemiRingType) (only parsing).
#[deprecated(since="mathcomp 2.4.0",
             note="Use finNzRingType instead.")]
Notation finRingType := (finNzRingType) (only parsing).
#[deprecated(since="mathcomp 2.4.0",
             note="Use finComNzSemiRingType instead.")]
Notation finComSemiRingType := (finComNzSemiRingType) (only parsing).
#[deprecated(since="mathcomp 2.4.0",
             note="Use finComNzRingType instead.")]
Notation finComRingType := (finComNzRingType) (only parsing).

Lemma card_finNzRing_gt1 (R : finNzRingType) : 1 < #|R|.
Proof. by rewrite (cardD1 0) (cardD1 1) !inE GRing.oner_neq0. Qed.

#[deprecated(since="mathcomp 2.4.0",
             note="Use card_finNzRing_gt1 instead.")]
Notation card_finRing_gt1 := (card_finNzRing_gt1) (only parsing).

Notation "{ 'unit' R }" := (unit_of R)
  (at level 0, format "{ 'unit'  R }") : type_scope.
Prenex Implicits FinRing.uval.
Notation "''U'" := (unit_action _) (at level 8) : action_scope.
Notation "''U'" := (unit_groupAction _) (at level 8) : groupAction_scope.

Lemma card_finField_unit (F : finFieldType) : #|[set: {unit F}]| = #|F|.-1.
Proof.
rewrite -(cardC1 0) cardsT card_sub; apply: eq_card => x.
by rewrite GRing.unitfE.
Qed.

(* Finite Algebraic structure for bool *)

#[hnf] HB.instance Definition _ := GRing.NzRing.on bool.
#[hnf] HB.instance Definition _ := isField.Build bool.

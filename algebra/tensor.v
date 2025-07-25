From HB Require Import structures.
From mathcomp Require Import ssrnat ssrint ssreflect finfun fintype seq ssrbool.
From mathcomp Require Import eqtype ssralg zmodp ssrfun choice tuple order.

Open Scope ring_scope.
Open Scope seq_scope.
Open Scope bool_scope.

(******************************************************************************)
(* This file defines tensors.                                                 *)
(* For tensors we define:                                                     *)
(*            'T[R]_ds == the type of tensors with elements of type R and     *)
(*            'T_ds       dimensions ds, e.g. 'T[nat]_[:: 1; 3]. The [R] is   *)
(*                        optional and can usually be ommited.                *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Reserved Notation "''T_' ds" (at level 0, ds at level 2, format "''T_' ds").
Reserved Notation "''T[' R ]_ ds" (at level 0, ds at level 2). (* only parsing*)

(*****************************************************************************)
(****************************Type Definition**********************************)
(*****************************************************************************)

Section TensorDef.

Context (ds : seq nat) (T : Type).

Definition internal_type := foldr (fun d t => t ^ d)%type T ds.

Variant tensor : predArgType := Tensor of internal_type.

Definition tensor_val A := let: Tensor g := A in g.

Definition tensor_valK : cancel tensor_val Tensor.
Proof. by case. Qed.

End TensorDef.


Bind Scope ring_scope with tensor.

Notation "''T[' R ]_ ds" := (tensor ds R) (only parsing) : type_scope.
Notation "''T_' ds" := 'T[_]_ds : type_scope.


Section NonEmptyTensor.

Context (d : nat) (ds : seq nat) (R : Type).
Implicit Type t : 'T[R]_(d :: ds).

Definition nth t (i : 'I_d) := Tensor ((tensor_val t) i).

End NonEmptyTensor.


Section TensorOperations.

Context (R : Type).

Definition stack {d} {ds : seq nat} (f : {ffun 'I_d -> 'T_ds}) := 
  @Tensor (d :: ds) R [ffun i => tensor_val (f i)].

Fixpoint const {ds : seq nat} : R -> 'T_ds := match ds with
  | [::] => fun v => @Tensor [::] R v
  | d :: ds' => fun v => stack [ffun=> @const ds' v]
  end.

End TensorOperations.


Section TensorEquality.

Context (R : eqType).

Fixpoint tensor_eq_op {ds} : rel ('T[R]_ds) := match ds with
  | [::] => fun t1 t2 => eq_op (tensor_val t1) (tensor_val t2)
  | d :: ds' => fun t1 t2 => [forall i, tensor_eq_op (nth t1 i) (nth t2 i)]
  end.

Definition tensor_eqP {ds} : Equality.axiom (@tensor_eq_op ds).
Proof.
elim: ds=> [|d ds' Hind] [x] [y] /=.
  case (x =P y) => [->|x_neq_y]; first by left.
    by right; case; exact x_neq_y.
case forallP => forall_tensor_eq_op_nth.
- left; apply f_equal; apply ffunP => i.
  have: forall a b, Tensor a = Tensor b -> a = b => [ds T0 a b|tensor_eq_ab].
    by case.
  apply tensor_eq_ab; apply/Hind.
  by rewrite /nth; apply forall_tensor_eq_op_nth.
- right=> x_eq_y. 
  have: forall x1, tensor_eq_op (nth (Tensor x) x1) (nth (Tensor y) x1) => [x1|].
    by apply/Hind; rewrite x_eq_y.
  by apply forall_tensor_eq_op_nth.
Qed.

HB.instance Definition _ {ds} := hasDecEq.Build ('T_ds) tensor_eqP.

End TensorEquality.


Section MapTensor.

Context {X Y Z : Type}.

Fixpoint map_tensor {ds} (f : X -> Y) : 'T[X]_ds -> 'T[Y]_ds :=
  match ds with
  | [::] => fun t => @Tensor [::] Y (f (tensor_val t))
  | d :: ds' => fun t => stack [ffun i => map_tensor f (nth t i)]
  end.

Fixpoint map2_tensor {ds} (f : X -> Y -> Z) : 'T[X]_ds -> 'T[Y]_ds -> 'T[Z]_ds :=
  match ds with
  | [::] => fun u v => @Tensor [::] Z (f (tensor_val u) (tensor_val v))
  | d :: ds' => fun u v => stack [ffun i => map2_tensor f (nth u i) (nth v i)]
  end.

End MapTensor.


Section TensorChoice.

Import Choice.InternalTheory.

Context {R : choiceType}.

Fixpoint tensor_find {ds} : pred 'T[R]_ds -> nat -> option 'T[R]_ds := match ds with
  | [::] => fun P n => omap (@Tensor [::] _) (find (fun t => P (@Tensor [::] _ t)) n)
  | d :: ds' => fun P n => None
  end.

(* Definition tensor_hasChoice {ds} : hasChoice ('T[R]_ds).
Proof.
exists tensor_find.
- elim: ds => [|d ds' Hind] P n t.
  + rewrite /tensor_find. case: t => /= i H.
    (* have: P (@Tensor [::] _ i) = (P \o @Tensor [::] _) i => [//|-> H]. *)
    
    move: H. case: (find _ n) => //= j.
    by case => ->.
  + admit.
- elim: ds => [|d ds' Hind] P [[i]].
  + rewrite /tensor_find.
    have: P (@Tensor [::] _ i) = (P \o @Tensor [::] _) i => [//|-> H].
    rewrite /isSome.
    admit.
  + admit.
- elim: ds => [|d ds' Hind] P Q P_eq1_Q. 
  + rewrite /tensor_find /eqfun => n.
Admitted. *)

Definition tensor_hasChoice {ds} : hasChoice ('T[R]_ds).
Admitted.

HB.instance Definition _ {ds} := @tensor_hasChoice ds.

End TensorChoice.


Section TensorNModule.

Context {R : nmodType}.

Definition addT {ds} := @map2_tensor R R R ds +%R.

Definition tensor0 {ds} := @const R ds 0.

Lemma addTA {ds} : associative (@addT ds).
Proof.
elim ds=> [t u v|d ds' Hind t u v]; first by rewrite /addT/= addrA.
rewrite /addT/=; apply f_equal; apply eq_dffun=> x0. 
rewrite -/addT {2 5}/nth/= !ffunE 2!tensor_valK.
by apply Hind.
Qed.

Lemma addTC {ds} : commutative (@addT ds).
Proof.
elim: ds => [t u|d ds' Hind t u]; first by rewrite /addT/= addrC.
rewrite /addT/= /stack.
apply f_equal; apply eq_dffun=> x0; apply f_equal.
rewrite !ffunE.
by apply Hind.
Qed.

Lemma add0T {ds} : left_id tensor0 (@addT ds).
Proof.
elim: ds => [t|d ds' Hind]; first by rewrite /addT/= add0r tensor_valK.
rewrite /addT/= -/addT /stack => [[i]].
apply f_equal; apply ffunP => x.
by rewrite 2!ffunE /tensor0 /nth/= 2!ffunE tensor_valK Hind.
Qed.

HB.instance Definition _ {ds} := GRing.isNmodule.Build ('T_ds) addTA addTC add0T.

End TensorNModule.


Section TensorZModule.

Context {R : zmodType}.

Definition oppT {ds} := @map_tensor R R ds -%R.

Lemma addNT {ds} : left_inverse 0 (@oppT ds) +%R.
Proof.
elim: ds => [|d ds' Hind]; case => i.
  by rewrite /oppT /GRing.add/= /addT/= addNr.
rewrite /oppT/= -/oppT /GRing.add/= /addT /stack/= /GRing.zero/= /tensor0/=.
apply f_equal; apply eq_dffun => x.
rewrite /nth/= 2!ffunE tensor_valK -/addT.
rewrite (_ : forall a b, addT a b = a + b); last by rewrite /GRing.add/=.
by rewrite Hind.
Qed.

HB.instance Definition _ {ds} := GRing.Nmodule_isZmodule.Build ('T_ds) addNT.

End TensorZModule.


Section TensorPzSemiRing.

Context {R : pzSemiRingType}.

Definition tensor1 {ds} := @const R ds 1. 

Definition mulT {ds} := @map2_tensor R R R ds *%R.

Lemma mulTA {ds} : associative (@mulT ds).
Proof.
elim: ds => [t u v|d ds' Hind t u v]; first by rewrite /mulT/= mulrA.
rewrite /mulT/= -/mulT.
apply f_equal; apply eq_dffun => x.
by rewrite {2 5}/nth/= !ffunE 2!tensor_valK Hind.
Qed.

Lemma mul1T {ds} : left_id tensor1 (@mulT ds).
Proof.
elim: ds => [t|d ds' Hind]; first by rewrite /mulT/= mul1r tensor_valK.
rewrite /mulT/= -/mulT /stack => [[i]].
apply f_equal; apply ffunP => x.
by rewrite 2!ffunE /tensor1 /nth/= 2!ffunE tensor_valK Hind.
Qed.

Lemma mulT1 {ds} : right_id tensor1 (@mulT ds).
Proof.
elim: ds => [t|d ds' Hind]; first by rewrite /mulT/= mulr1 tensor_valK.
rewrite /mulT/= -/mulT /stack => [[i]].
apply f_equal; apply ffunP => x.
by rewrite 2!ffunE /tensor1 /nth/= 2!ffunE tensor_valK Hind.
Qed.

Lemma mulTDl {ds} : left_distributive (@mulT ds) +%R.
Proof.
elim: ds => [t u v|d ds' Hind t u v].
  by rewrite /mulT/= mulrDl {2}/GRing.add/= /addT.
rewrite /mulT/= -/mulT /GRing.add/= /addT /nth/=.
apply f_equal; apply eq_dffun => x.
rewrite 2!ffunE tensor_valK -/addT.
have: forall a b, addT a b = a + b => addT_add; first by rewrite /GRing.add/=.
by rewrite 2!addT_add Hind /nth /stack 4!ffunE 2!tensor_valK.
Qed.

Lemma mulTDr {ds} : right_distributive (@mulT ds) +%R.
Proof.
elim: ds => [t u v|d ds' Hind t u v].
  by rewrite /mulT/= mulrDr {2}/GRing.add/= /addT.
rewrite /mulT/= -/mulT /GRing.add/= /addT /nth/=.
apply f_equal; apply eq_dffun => x.
rewrite 2!ffunE tensor_valK -/addT.
have: forall a b, addT a b = a + b => addT_add; first by rewrite /GRing.add/=.
by rewrite 2!addT_add Hind /nth /stack 4!ffunE 2!tensor_valK.
Qed.

Lemma mul0T {ds} : left_zero 0 (@mulT ds).
Proof.
elim: ds => [t|d ds' Hind t]; first by rewrite /mulT/= mul0r.
rewrite /mulT/= -/mulT /GRing.zero/= /tensor0/=.
apply f_equal; apply eq_dffun => x.
by rewrite /nth /stack 2!ffunE tensor_valK Hind.
Qed.

Lemma mulT0 {ds} : right_zero 0 (@mulT ds).
Proof.
elim: ds => [t|d ds' Hind t]; first by rewrite /mulT/= mulr0.
rewrite /mulT/= -/mulT /GRing.zero/= /tensor0/=.
apply f_equal; apply eq_dffun => x.
by rewrite /nth /stack 2!ffunE tensor_valK Hind.
Qed.

HB.instance Definition _ {ds} := GRing.Nmodule_isPzSemiRing.Build ('T_ds)
    mulTA mul1T mulT1 mulTDl mulTDr mul0T mulT0.

End TensorPzSemiRing.


Section TensorNzSemiRing.

Context {R : nzSemiRingType}.

Lemma oneT_neq0 {ds} : all [eta leq 1] ds -> @GRing.one ('T[R]_ds) != 0.
Proof.
elim: ds => [|d ds' Hind]; first by rewrite oner_neq0.
rewrite /eq_op/=.
Admitted.

HB.instance Definition _ {ds} {ds_gt_0} := GRing.PzSemiRing_isNonZero.Build ('T_ds) (oneT_neq0 ds_gt_0).

End TensorNzSemiRing.


Section TensorOrder.

Import Order.LTheory.

Context (o : Order.disp_t) (R : porderType o).

Fixpoint leT {ds} : rel ('T[R]_ds) := match ds with
  | [::] => fun t u => Order.le (tensor_val t) (tensor_val u)
  | d :: ds' => fun t u => [forall i, leT (nth t i) (nth u i)]
  end.

Definition ltT {ds} : rel ('T[R]_ds) := fun t u => (u != t) && leT t u.

Lemma ltT_def {ds} : forall x y : 'T[R]_ds, ltT x y = (y != x) && leT x y.
Proof. by rewrite /ltT. Qed.

Lemma leT_refl {ds} : reflexive (@leT ds).
Proof.
elim: ds => [t|d ds' Hind t].
  by rewrite /leT le_refl.
rewrite /leT -/leT.
by apply/forallP => x.
Qed.

Lemma leT_anti {ds} : antisymmetric (@leT ds).
Proof.
elim: ds => [t u|d ds' Hind t u].
  rewrite /leT => le_tut.
  have: tensor_val t = tensor_val u -> t = u => [|->//].
    by case t; case u => i0 i1 /= i1_eq_i0; rewrite i1_eq_i0.
  by apply le_anti.
rewrite /leT -/leT => /andP [/forallP le_tu /forallP le_ut].
have: (forall i, nth t i = nth u i) -> t = u => [nth_tu|->// i].
  apply/eqP; rewrite /eq_op/=; apply/forallP => i; rewrite nth_tu.
  by apply/tensor_eqP.
by apply/Hind/andP.
Qed.

Lemma leT_trans {ds} : transitive (@leT ds).
Proof.
elim: ds => [t u v|d ds' Hind t u v].
  by rewrite /leT; apply le_trans.
rewrite /leT -/leT => /forallP le_ut /forallP le_tv.
apply/forallP => i.
by apply /Hind.
Qed.

HB.instance Definition _ {ds} := Order.isPOrder.Build
  o ('T_ds) ltT_def leT_refl leT_anti leT_trans.

End TensorOrder.

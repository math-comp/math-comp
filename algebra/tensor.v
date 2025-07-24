From HB Require Import structures.
From mathcomp Require Import ssrnat ssrint ssreflect finfun fintype seq ssrbool eqtype ssralg zmodp ssrfun choice tuple.
Open Scope ring_scope.
Open Scope seq_scope.
Open Scope bool_scope.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(******************************************************************************)
(* This file defines tensors.                                                 *)
(* For tensors we define:                                                     *)
(*        ds.-tensor T == the type of tensors with elements of type T and     *)
(*                        dimensions ds, e.g. [:: 1; 3].-tensor nat.          *)
(*             const v ==                                                     *)
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
(*                                                                            *)
(******************************************************************************)

Section TensorDef.

Context (ds : seq nat) (T : Type).

Definition internal_type := foldr (fun d t => t ^ d)%type T ds.

Variant tensor_of : predArgType := Tensor of internal_type.

Definition tensor_val A := let: Tensor g := A in g.

Definition tensor_valK : cancel tensor_val Tensor.
Proof. by case. Qed.

End TensorDef.


Notation "ds '.-tensor'" := (tensor_of ds)
    (at level 2, format "ds '.-tensor'") : type_scope.


Section NilTensor.

Context (T : Type).
Implicit Type t : [::].-tensor T.

End NilTensor.


Section NonEmptyTensor.

Context (d : nat) (ds : seq nat) (T : Type).
Implicit Type t : (d :: ds).-tensor T.

Definition nth t (i : 'I_d) := Tensor ((tensor_val t) i).

End NonEmptyTensor.


Section TensorOperations.

Context (T : Type).

Definition stack {d} {ds : seq nat} (f : {ffun 'I_d -> ds.-tensor T}) := 
  @Tensor (d :: ds) T [ffun i => tensor_val (f i)].

Fixpoint const {ds : seq nat} : T -> ds.-tensor T := match ds with
  | [::] => fun v => @Tensor [::] T v
  | d :: ds' => fun v => stack [ffun=> @const ds' v]
  end.

End TensorOperations.


Section TensorEquality.

Context (T : eqType).

Fixpoint tensor_eq_op {ds} : rel (ds.-tensor T) := match ds with
  | [::] => fun t1 t2 => eq_op (tensor_val t1) (tensor_val t2)
  | d :: ds' => fun t1 t2 => [forall i, tensor_eq_op (nth t1 i) (nth t2 i)]
  end.

Definition tensor_eqP {ds} : Equality.axiom (@tensor_eq_op ds).
Proof.
elim: ds=> [[x] [y]|d ds' Hind [x/=] [y/=]]/=. 
  case (x =P y) => H_xy.
  - by rewrite H_xy; left.
  - by right=> [[]]; exact H_xy.
case forallP => H_forall.
- left. apply f_equal. apply ffunP => i.
  have: forall a b, Tensor a = Tensor b -> a = b => [ds T0 a b|H_tensor_ab]; first by case.
  apply H_tensor_ab; apply/Hind.
  by move: H_forall; rewrite /nth; apply.
- right. case. 


elim: d Hind x y H_forall => [Hind x y H_forall|n H1 H2 x y H3].
  - have: forall x0 : 'I_0, tensor_eq_op (nth (Tensor x) x0) (nth (Tensor y) x0).
    move=> x0. case: x0 => m i//. by [].
Admitted.

HB.instance Definition _ {ds} := hasDecEq.Build (ds.-tensor T) tensor_eqP.

End TensorEquality.


Section MapTensor.

Context {T R S : Type}.

Fixpoint map_tensor {ds} (f : T -> R) : ds.-tensor T -> ds.-tensor R :=
  match ds with
  | [::] => fun t => @Tensor [::] R (f (tensor_val t))
  | d :: ds' => fun t => stack [ffun i => map_tensor f (nth t i)]
  end.

Fixpoint map2_tensor {ds} (f : T -> R -> S) : ds.-tensor T -> ds.-tensor R -> ds.-tensor S :=
    match ds with
    | [::] => fun u v => @Tensor [::] S (f (tensor_val u) (tensor_val v))
    | d :: ds' => fun u v => stack [ffun i => map2_tensor f (nth u i) (nth v i)]
    end.

End MapTensor.


Section TensorChoice.

Context (ds : seq nat) (T : choiceType).

Definition tensor_hasChoice : hasChoice (ds.-tensor T).
Proof. Admitted.

HB.instance Definition _ := tensor_hasChoice.

End TensorChoice.


Section TensorNModule.

Context {T : nmodType}.

Definition addT {ds} := @map2_tensor T T T ds +%R.

Definition tensor0 {ds} := @const T ds 0.

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
    rewrite /addT/= /stack; apply f_equal; apply eq_dffun=> x0; apply f_equal; rewrite !ffunE.
    by apply Hind.
Qed.

Lemma add0T {ds} : left_id tensor0 (@addT ds).
Proof.
    elim: ds => [t|d ds' Hind]; first by rewrite /addT/= add0r tensor_valK.
    rewrite /addT/= -/addT /stack.
    case => i.
    apply f_equal; apply ffunP => x.
    by rewrite 2!ffunE /tensor0 /nth/= 2!ffunE tensor_valK Hind.
Qed.

HB.instance Definition _ {ds} := GRing.isNmodule.Build (ds.-tensor T) addTA addTC add0T.

End TensorNModule.


Section TensorZModule.

Context {T : zmodType}.

Definition oppT {ds} := @map_tensor T T ds -%R.

Lemma addNT {ds} : left_inverse 0 (@oppT ds) +%R.
Proof.
    elim: ds => [|d ds' Hind]; case => i; first by rewrite /oppT /GRing.add/= /addT/= addNr.
    rewrite /oppT/= -/oppT /GRing.add/= /addT /stack/= /GRing.zero/= /tensor0/=.
    apply f_equal; apply eq_dffun => x.
    rewrite /nth/= 2!ffunE tensor_valK -/addT.
    rewrite (_ : forall a b, addT a b = a + b); last by rewrite /GRing.add/=.
    by rewrite Hind.
Qed.

HB.instance Definition _ {ds} := GRing.Nmodule_isZmodule.Build (ds.-tensor T) addNT.

End TensorZModule.


Section TensorPzSemiRing.

Context (T : pzSemiRingType).

Definition tensor1 {ds} := @const T ds 1. 

Definition mulT {ds} := @map2_tensor T T T ds *%R.

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
    rewrite /mulT/= -/mulT /stack.
    case => i.
    apply f_equal; apply ffunP => x.
    by rewrite 2!ffunE /tensor1 /nth/= 2!ffunE tensor_valK Hind.
Qed.

Lemma mulT1 {ds} : right_id tensor1 (@mulT ds).
Proof.
    elim: ds => [t|d ds' Hind]; first by rewrite /mulT/= mulr1 tensor_valK.
    rewrite /mulT/= -/mulT /stack.
    case => i.
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

HB.instance Definition _ {ds} := GRing.Nmodule_isPzSemiRing.Build (ds.-tensor T)
    mulTA mul1T mulT1 mulTDl mulTDr mul0T mulT0.

End TensorPzSemiRing.


Section TensorNzSemiRing.

Context (T : nzSemiRingType).

Lemma oneT_neq0 {ds} : @GRing.one (ds.-tensor T) != 0.
Proof.
    elim: ds => [|d ds' Hind]; first by rewrite oner_neq0.
    rewrite /eq_op/=. apply/forallP. 
Admitted.

HB.instance Definition _ {ds} := GRing.PzSemiRing_isNonZero.Build (ds.-tensor T) oneT_neq0.

End TensorNzSemiRing.


Section Test.

HB.about tensor_of.

Context (ds : seq nat) (T : pzSemiRingType) (t u v : ds.-tensor T).

Lemma dist : (t + u) * v = t * v + u * v.
Proof.
    by rewrite mulrDl.
Qed.

End Test.

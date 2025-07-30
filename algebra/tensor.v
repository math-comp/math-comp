From HB Require Import structures.
From mathcomp Require Import ssreflect seq matrix bigop ssrbool eqtype choice.
From mathcomp Require Import fintype ssralg ssrnat ssrfun order.


(******************************************************************************)
(* This file defines tensors.                                                 *)
(* For tensors we define:                                                     *)
(*       'T[R]_(us, ds) == the type of tensors with elements of type R,       *)
(*       'T_(us, ds)       contravariant dimensions us, and covariant         *)
(*                         dimensions ds, e.g. 'T[nat]_([:: 1; 3], [::]).     *)
(*                         The [R] is optional and can usually be ommited.    *)
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

Reserved Notation "''T_' ( us , ds )"
  (at level 0, us at level 2, ds at level 2, format "''T_' ( us ,  ds )").
Reserved Notation "''T[' R ]_ ( us , ds )"
  (at level 0, us at level 2, ds at level 2, format "''T[' R ]_ ( us ,  ds )").
  (* only parsing*)


Section TensorDef.

Context (us ds : seq nat) (K : Type).

Variant tensor : predArgType := Tensor of 'M[K]_(\prod_(u <- us) u, \prod_(d <- ds) d).

Definition T_val T := let: Tensor g := T in g.

HB.instance Definition _ := [isNew for T_val].

End TensorDef.

Notation "''T[' R ]_ ( us , ds )" := (tensor us ds R) (only parsing).
Notation "''T_' ( us , ds )" := 'T[_]_(us, ds).

Section SubtypeInstances.

Context (us ds : seq nat).

HB.instance Definition _ (R : eqType) := [Equality of 'T[R]_(us, ds) by <:].
HB.instance Definition _ (R : choiceType) := [Choice of 'T[R]_(us, ds) by <:].
HB.instance Definition _ (R : countType) := [Countable of 'T[R]_(us, ds) by <:].
HB.instance Definition _ (R : finType) := [Finite of 'T[R]_(us, ds) by <:].

End SubtypeInstances.

Section IndexTensor.

Context (us ds : seq nat) (R : Type).

Definition indexT (t : 'T[R]_(us, ds)) (ui : _) (di : _) : R := T_val t ui di.

End IndexTensor.

Section ContravariantTensor.

Context (u' : nat) (us ds : seq nat) (R : Type).
Local Notation u := u'.+1 (only parsing).



Lemma ord_i_j (i : 'I_u) (j : 'I_\prod_(e <- us) e) : j * u + i < \prod_(e <- u :: us) e.
Proof.
  case: i => i i_ord /=.
  case: j => j j_ord /=.
  rewrite big_cons. 
  set e := \prod_(e <- us) e in j_ord *.
  set u := u'.+1 in i_ord *.
  by rewrite -ltn_subRL mulnC -mulnBl (ltn_leq_trans i_ord)// leq_pmull// subn_gt0.
Qed.

Definition upper_index (t : 'T[R]_(u :: us, ds)) (i : 'I_u) : 'T[R]_(us, ds) :=
  Tensor (rowsub (fun j => Ordinal (ord_i_j i j)) (T_val t)).

End ContravariantTensor.

Section CovariantTensor.

Context (d : nat) (us ds : seq nat) (R : Type).

Definition lower_index (t : 'T[R]_(us, d :: ds)) (i : 'I_d) : 'T[R]_(us, ds).
Admitted.


End CovariantTensor.

Section Test.

Context (t v : 'T[bool]_([:: 2; 3], [:: 2])) (u : 'T[unit]_([::], [::])).

Check t == v.

End Test.
(* (c) Copyright 2006-2019 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype tuple preorder porder lattice total_order.
From mathcomp Require Import complemented_lattice.

From mathcomp Require Export lattice_instances.
From mathcomp Require Export total_order_instances.
From mathcomp Require Export complemented_lattice_instances.

(******************************************************************************)
(*                       Instances of order structures                        *)
(*                                                                            *)
(* NB: See the header of order.v for general remarks about the preorder and   *)
(*     order structures in MathComp, and the files in this directory.         *)
(*                                                                            *)
(* This file provides finite total order and finite complemented lattice      *)
(* instances for bool, and re-exports the contents of lattice_instances.v,    *)
(* total_order_instances.v, and complemented_lattice_instances.v.             *)
(* Use `HB.about type` to discover the instances on type.                     *)
(*                                                                            *)
(* Acknowledgments: The files in this directory are based on prior work by    *)
(* D. Dreyer, G. Gonthier, A. Nanevski, P-Y Strub, B. Ziliani                 *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope order_scope.

Module Order.

Export total_order.Order complemented_lattice.Order.

Module ProdLexiTheory.

Lemma sub_prod_lexi (d1 d2 d3 d4 : disp_t)
  (T1 : preorderType d1) (T2 : preorderType d2) :
  subrel (<=%O : rel (T1 *prod[d3] T2)) (<=%O : rel (T1 *lexi[d4] T2)).
Proof.
case=> [x1 x2] [y1 y2]; rewrite leEprod leEprodlexi /= => /andP[] -> ->.
exact: implybT.
Qed.

Lemma sub_seqprod_lexi (d1 d2 d3 : disp_t) (T : preorderType d1) :
   subrel (<=%O : rel (seqprod_with d2 T)) (<=%O : rel (seqlexi_with d3 T)).
Proof.
elim=> [|x1 s1 ihs1] [|x2 s2]//=; rewrite le_cons lexi_cons /=.
by move=> /andP[-> /ihs1->]; rewrite implybT.
Qed.

Lemma sub_tprod_lexi (d1 d2 d3 : disp_t) n (T : preorderType d1) :
   subrel (<=%O : rel (n.-tupleprod[d2] T)) (<=%O : rel (n.-tuplelexi[d3] T)).
Proof. exact: sub_seqprod_lexi. Qed.

End ProdLexiTheory.
HB.export ProdLexiTheory.

(*********************)
(* Instances on bool *)
(*********************)

Module BoolOrder.
Section BoolOrder.
Implicit Types (x y : bool).

Fact bool_display : disp_t. Proof. exact. Qed.

Fact ltb_def x y : (x < y)%N = (y != x) && (x <= y)%N.
Proof. by case: x y => [] []. Qed.

Fact leb_refl : reflexive (leq : rel bool).
Proof. by case. Qed.

Fact leb_anti : antisymmetric (leq : rel bool).
Proof. by case=> [] []. Qed.

Fact leb_trans : transitive (leq : rel bool).
Proof. exact: leq_trans. Qed.

Fact leb_andb x y z : (x <= y && z)%N = (x <= y)%N && (x <= z)%N.
Proof. by case: x y z => [] [] []. Qed.

Fact le_orb_b x y z : (x || y <= z)%N = (x <= z)%N && (y <= z)%N.
Proof. by case: x y z => [] [] []. Qed.

#[export] HB.instance Definition _ :=
  isPOrder.Build bool_display bool ltb_def leb_refl leb_anti leb_trans.
#[export] HB.instance Definition _ := @hasBottom.Build _ bool false leq0n.
#[export] HB.instance Definition _ := @hasTop.Build _ bool true leq_b1.
#[export] HB.instance Definition _ :=
  @POrder_MeetJoin_isLattice.Build _ bool andb orb leb_andb le_orb_b.
#[export] HB.instance Definition _ := Lattice_isTotal.Build _ bool leq_total.
#[export] HB.instance Definition _ :=
  TBDistrLattice_hasComplement.Build _ bool orbN andbN.

Lemma leEbool : le = (leq : rel bool). Proof. by []. Qed.
Lemma ltEbool x y : (x < y) = (x < y)%N. Proof. by []. Qed.
Lemma andEbool : meet = andb. Proof. by []. Qed.
Lemma orEbool : meet = andb. Proof. by []. Qed.
Lemma subEbool x y : x `\` y = x && ~~ y. Proof. by []. Qed.
Lemma complEbool : compl = negb. Proof. by []. Qed.

End BoolOrder.
Module Exports.
HB.reexport BoolOrder.
Definition leEbool := leEbool.
Definition ltEbool := ltEbool.
Definition andEbool := andEbool.
Definition orEbool := orEbool.
Definition subEbool := subEbool.
Definition complEbool := complEbool.
End Exports.
End BoolOrder.
HB.export BoolOrder.Exports.

Module Exports.
HB.reexport.
End Exports.

End Order.

Export Order.Exports.

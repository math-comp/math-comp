(* (c) Copyright 2006-2019 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype choice.
From mathcomp Require Export preorder porder lattice total_order.
From mathcomp Require Export complemented_lattice order_instances.

(******************************************************************************)
(*              Types equipped with preorder and order relations              *)
(*                                                                            *)
(* NB: See CONTRIBUTING.md for an introduction to HB concepts and commands.   *)
(*                                                                            *)
(* The files in this directory define structures for types equipped with      *)
(* order relations.                                                           *)
(*                                                                            *)
(* * How to use orders in MathComp?                                           *)
(* Use one of the following modules implementing different theories (all      *)
(* located in the module Order):                                              *)
(*   Order.LTheory: partially ordered types and lattices excluding complement *)
(*                  and totality related theorems                             *)
(*   Order.CTheory: complemented lattices including Order.LTheory             *)
(*   Order.TTheory: totally ordered types including Order.LTheory             *)
(*    Order.Theory: ordered types including all of the above theory modules   *)
(* To access the definitions, notations, and the theory from, say,            *)
(* "Order.Xyz", insert "Import Order.Xyz." at the top of your scripts. You can*)
(* also "Import Order.Def." to enjoy shorter notations (e.g., min instead of  *)
(* Order.min, nondecreasing instead of Order.nondecreasing, etc.).            *)
(*                                                                            *)
(* In order to reason about abstract orders, notations are accessible by      *)
(* opening the scope "order_scope" bound to the delimiting key "O"; however,  *)
(* when dealing with another notation scope providing order notations for     *)
(* a concrete instance (e.g., "ring_scope"), it is not recommended to open    *)
(* "order_scope" at the same time.                                            *)
(*                                                                            *)
(* * Control of inference (parsing) and printing                              *)
(* One characteristic of ordered types is that one carrier type may have      *)
(* several orders. For example, natural numbers can be totally or partially   *)
(* ordered by the less than or equal relation, the divisibility relation, and *)
(* their dual relations. Therefore, we need a way to control inference of     *)
(* ordered type instances and printing of generic relations and operations on *)
(* ordered types. As a rule of thumb, we use the carrier type or its "alias"  *)
(* (named copy) to control inference (using canonical structures), and use a  *)
(* "display" to control the printing of notations.                            *)
(*                                                                            *)
(* Each generic interface and operation for ordered types has, as its first   *)
(* argument, a "display" of type Order.disp_t. For example, the less than or  *)
(* equal relation has type:                                                   *)
(*   Order.le : forall {d : Order.disp_t} {T : porderType d}, rel T,          *)
(* where porderType d is the structure of partially ordered types with        *)
(* display d. (@Order.le dvd_display _ m n) is printed as m %| n because      *)
(* ordered type instances associated to the display dvd_display is intended   *)
(* to represent natural numbers partially ordered by the divisibility         *)
(* relation.                                                                  *)
(*                                                                            *)
(* We stress that order structure inference can be triggered only from the    *)
(* carrier type (or its alias), but not the display. For example, writing     *)
(* m %| n for m and n of type nat does not trigger an inference of the        *)
(* divisibility relation on natural numbers, which is associated to an alias  *)
(* natdvd for nat; such an inference should be triggered through the use of   *)
(* the corresponding alias, i.e., (m : natdvd) %| n. In other words, displays *)
(* are merely used to inform the user and the notation mechanism of what the  *)
(* inference did; they are not additional input for the inference.            *)
(*                                                                            *)
(* See below for various aliases and their associated displays.               *)
(*                                                                            *)
(* NB: algebra/ssrnum.v provides the display ring_display to change the       *)
(* scope of the usual notations to ring_scope.                                *)
(*                                                                            *)
(* Instantiating d with Disp tt tt or an unknown display will lead to a       *)
(* default display for notations.                                             *)
(*                                                                            *)
(* Alternative notation displays can be defined by:                           *)
(* 1. declaring a new opaque definition of type Order.disp_t. Using the idiom *)
(*    `Fact my_display : Order.disp_t. Proof. exact: Disp tt tt. Qed.`        *)
(* 2. using this symbol to tag canonical porderType structures using          *)
(*    `HB.instance Definition _ := isPOrder.Build my_display my_type ...`,    *)
(* 3. declaring notations for the main operations of this library, by         *)
(*    setting the first argument of the definition to the display, e.g.       *)
(*    `Notation my_syndef_le x y := @Order.le my_display _ x y.` or           *)
(*    `Notation "x <=< y" := @Order.lt my_display _ x y (at level ...).`      *)
(*    Non overloaded notations will default to the default display.           *)
(* We suggest the user to refer to the example of natdvd below as a guideline *)
(* example to add their own displays.                                         *)
(*                                                                            *)
(* * Useful lemmas:                                                           *)
(* On orderType, leP, ltP, and ltgtP are the three main lemmas for case       *)
(* analysis.                                                                  *)
(* On porderType, one may use comparableP, comparable_leP, comparable_ltP,    *)
(* and comparable_ltgtP, which are the four main lemmas for case analysis.    *)
(*                                                                            *)
(* We also provide specialized versions of some theorems from path.v.         *)
(*                                                                            *)
(* The following notations are provided to build substructures:               *)
(*   [POrder of U by <:] == porderType mixin for a subType whose base type is *)
(*                          a porderType                                      *)
(*    [Order of U by <:] == orderType mixin for a subType whose base type is  *)
(*                          an orderType                                      *)
(*                                                                            *)
(* Acknowledgments: The files in this directory are based on prior work by    *)
(* D. Dreyer, G. Gonthier, A. Nanevski, P-Y Strub, B. Ziliani                 *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope order_scope.

Module Order.

Import total_order.Order.
Import total_order.Order.Theory.

Module DeprecatedSubOrder.

Section Total.
Context {disp : disp_t} {T : orderType disp} (P : {pred T}) (sT : subType P).

#[export]
HB.instance Definition _ :=
  SubPOrder_isSubOrder.Build disp T P disp (sub_type sT).

End Total.

Module Exports.
HB.reexport DeprecatedSubOrder.
Notation "[ 'POrder' 'of' T 'by' <: ]" :=
  (POrder.copy T%type (sub_type T%type))
  (format "[ 'POrder'  'of'  T  'by'  <: ]") : form_scope.
Notation "[ 'Order' 'of' T 'by' <: ]" :=
  (Total.copy T%type (sub_type T%type))
  (only parsing) : form_scope.
End Exports.
End DeprecatedSubOrder.
HB.export DeprecatedSubOrder.Exports.

Module Theory.
Export total_order.Order.Theory.
Export complemented_lattice.Order.Theory.
End Theory.

(* LTheory, TTheory, and CTheory below are considered deprecated *)
Module LTheory := lattice.Order.Theory.
Module TTheory := total_order.Order.Theory.
Module CTheory := complemented_lattice.Order.Theory.

Module Exports.
HB.reexport.
End Exports.
End Order.

Export Order.Exports.

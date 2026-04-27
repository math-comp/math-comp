(* (c) Copyright 2006-2019 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype choice.
From mathcomp Require Export preorder porder lattice lattice_instances.
From mathcomp Require Export total_order total_order_instances.
From mathcomp Require Export complemented_lattice.
From mathcomp Require Export complemented_lattice_instances order_instances.

(******************************************************************************)
(*              Types equipped with preorder and order relations              *)
(*                                                                            *)
(* NB: See CONTRIBUTING.md for an introduction to HB concepts and commands.   *)
(*                                                                            *)
(* The order package (this directory) provides the definitions of structures  *)
(* for types equipped with preorder and order relations, their theory, and    *)
(* instances. It consists of the following files:                             *)
(*              preorder.v: preorder structures and their theory              *)
(*                porder.v: partial order structures and their theory         *)
(*               lattice.v: semilattice and lattice structures, and their     *)
(*                          theory                                            *)
(*     lattice_instances.v: instances of the lattice structures, e.g., the    *)
(*                          product order on lists, and natural numbers (nat) *)
(*                          partially ordered by the divisibility relation    *)
(*           total_order.v: total order structures and their theory           *)
(* total_order_instances.v: instances of the total order structures, e.g.,    *)
(*                          the lexicographic orders on the product type and  *)
(*                          lists                                             *)
(*  complemented_lattice.v: complemented lattice structures and their theory  *)
(* complemented_lattice_instances.v: instances of the complemented lattice    *)
(*                          structures, e.g., the product order on the        *)
(*                          product type and tuples                           *)
(*       order_instances.v: re-exportation of all the order instances above   *)
(*     order.v (this file): re-exportation of all the files above             *)
(*                                                                            *)
(* As a rule of thumb, <library>_instances.v depend only on <library>.v and   *)
(* its dependencies, and instance declarations on the same carrier type       *)
(* belong to the same file (for the maintenance reasons); for example,        *)
(* lattice instances, that are also complemented under certain conditions,    *)
(* are declared in complemented_lattice_instances.v, not lattice_instances.v. *)
(* These files must be imported in the dependency order. Note that neither    *)
(* total_order(_instances).v nor complemented_lattice(_instances).v depends   *)
(* on the other. If you use the theory of both totally-ordered types and      *)
(* complemented lattices, it is recommended to import order.v; otherwise,     *)
(* importing Order.Theory or Order.Def (see below) may not give you access to *)
(* the lemmas or shorthands you need.                                         *)
(*                                                                            *)
(* * Order relations and operations                                           *)
(*                                                                            *)
(* In general, an overloaded relation or operation on ordered types takes the *)
(* following arguments:                                                       *)
(* 1. a display d of type Order.disp_t,                                       *)
(* 2. an instance T of the minimal structure it operates on, and              *)
(* 3. operands.                                                               *)
(* As detailed below, the purpose of displays is to control the printing of   *)
(* order relations and operations. See the theory files for the complete list *)
(* of operations. You can also import Order.Def to enjoy the abbreviations    *)
(* (e.g., min instead of Order.min, nondecreasing instead of                  *)
(* Order.nondecreasing, etc.).                                                *)
(*                                                                            *)
(* * Displays, order notations, and control of inference (parsing) and        *)
(*   printing                                                                 *)
(*                                                                            *)
(* One characteristic of ordered types is that one carrier type may have      *)
(* several orders. For example, natural numbers can be totally or partially   *)
(* ordered by the less than or equal relation, the divisibility relation, and *)
(* their dual relations (see below). Therefore, we need a way to control      *)
(* inference of ordered type instances and printing of generic relations and  *)
(* operations on ordered types. As a rule of thumb, we use the carrier type   *)
(* or its "alias" (named copy) to control inference (using canonical          *)
(* structures), and use a "display" to control the printing of notations.     *)
(*                                                                            *)
(* Each generic interface and operation for ordered types has, as its first   *)
(* argument, a "display" of type Order.disp_t. For example, the less than or  *)
(* equal relation (defined in preorder.v) has type:                           *)
(*   Order.le : forall {d : Order.disp_t} {T : porderType d}, rel T,          *)
(* where porderType d is the structure of partially ordered types with        *)
(* display d. For example, (@Order.le dvd_display _ m n) is printed as m %| n *)
(* because ordered type instances associated to dvd_display is intended to    *)
(* represent natural numbers partially ordered by the divisibility relation   *)
(* (defined in lattice_instances.v).                                          *)
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
(* The "default" notations for the order relations and operations are defined *)
(* in the scope "order_scope" bound to the delimiting key "O". Printing falls *)
(* back to the default ones when the notation specific to the given display   *)
(* is not defined, e.g., when the display is abstract or Order.Disp tt tt.    *)
(* Opening order_scope is not recommended when dealing with order notations   *)
(* defined in another notation scope, e.g., "ring_scope" defined in           *)
(* "numeric_hierarchy/".                                                      *)
(*                                                                            *)
(* See the instance files for various aliases and their associated displays.  *)
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
(* We suggest the user to refer to the example of natdvd in                   *)
(* lattice_instances.v as a guideline example to add their own displays.      *)
(*                                                                            *)
(* * Dual orders                                                              *)
(*                                                                            *)
(* For any order relation <=, its dual relation <=^d (x <=^d y := y <= x)     *)
(* is an order. To allow the inference of dual orders, preorder.v provides    *)
(* the following definition:                                                  *)
(*                                                                            *)
(*              T^d := dual T,                                                *)
(*                     where dual is a new definition for (fun T : Type => T) *)
(*                  == an alias for T, such that if T is canonically          *)
(*                     ordered, then T^d is canonically ordered with the      *)
(*                     dual order                                             *)
(*   dual_display d == the display of the dual order T^d when the display of  *)
(*                     T is d                                                 *)
(*                                                                            *)
(* For any order structure ordType, its dual structure dual_ordType exists;   *)
(* for example, meetSemilatticeType is the dual of joinSemilatticeType        *)
(* (defined in lattice.v), and porderType is the dual of itself (defined in   *)
(* porder.v). For any type T that is canonically an ordType d, T^d is         *)
(* canonically a dual_ordType (dual_display d). Thanks to dual_display, the   *)
(* order relations and operations on a dual instance are printed with an      *)
(* extra ^d in the notations, i.e., <=^d, <^d, >=<^d, ><^d, `&`^d, `|`^d are  *)
(* used and displayed instead of <=, <, >=<, ><, `&`, `|`.                    *)
(*                                                                            *)
(* Duality plays a central role in the order package. Most notably, the dual  *)
(* instances are definitionally involutive; that is, for any T : ordType, the *)
(* canonical ordType instance on T^d^d is definitionally equal to the         *)
(* record-eta expansion of T.                                                 *)
(*                                                                            *)
(* * Order theory                                                             *)
(*                                                                            *)
(* Importing Order.Theory gives you access to the theory of the order         *)
(* structures.                                                                *)
(*                                                                            *)
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

Export total_order.Order complemented_lattice.Order.

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

(* Syntax, LTheory, TTheory, and CTheory below are considered deprecated *)
Module Syntax. End Syntax.
Module LTheory := lattice.Order.Theory.
Module TTheory := total_order.Order.Theory.
Module CTheory := complemented_lattice.Order.Theory.

Module Exports.
HB.reexport.
End Exports.
End Order.

Export Order.Exports.

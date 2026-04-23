(* (c) Copyright 2006-2019 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype choice.
From mathcomp Require Export preorder porder lattice total_order.
From mathcomp Require Export complemented_lattice order_instances.

(******************************************************************************)
(*                   Types equipped with order relations                      *)
(*                                                                            *)
(* NB: See CONTRIBUTING.md for an introduction to HB concepts and commands.   *)
(*                                                                            *)
(* NB: See the header of all_order.v for general remarks about the preorder   *)
(*     and order structures in MathComp, and the files in this directory.     *)
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

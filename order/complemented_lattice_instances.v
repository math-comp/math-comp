(* (c) Copyright 2006-2019 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype tuple bigop finset preorder porder lattice.
From mathcomp Require Import lattice_instances complemented_lattice.

(******************************************************************************)
(*               Instances of (complemented) lattice structures               *)
(*                                                                            *)
(* NB: See the header of order.v for general remarks about the preorder and   *)
(*     order structures in MathComp, and the files in this directory.         *)
(*                                                                            *)
(* We provide aliases for various types and their displays:                   *)
(*     T *prod[d] T' := T * T'                                                *)
(*                   == an alias for the cartesian product such that,         *)
(*                      if T and T' are canonically ordered,                  *)
(*                      then T *prod[d] T' is canonically ordered in product  *)
(*                      order, i.e.,                                          *)
(*                      (x1, x2) <= (y1, y2) = (x1 <= y1) && (x2 <= y2),      *)
(*                      and displayed in display d                            *)
(*           T *p T' := T *prod[prod_display d d'] T'                         *)
(*                      where d and d' are the displays of T and T',          *)
(*                      respectively, and prod_display adds an extra ^p to    *)
(*                      all notations                                         *)
(* n.-tupleprod[d] T := n.-tuple T                                            *)
(*                   == an alias for tuple, such that if T is canonically     *)
(*                      ordered, then n.-tupleprod[d] T is canonically        *)
(*                      ordered in product order, i.e.,                       *)
(*                      [:: x1, .., xn] <= [y1, .., yn] =                     *)
(*                        (x1 <= y1) && ... && (xn <= yn)                     *)
(*                      and displayed in display d                            *)
(*    n.-tupleprod T := n.-tupleprod[seqprod_display d] T                     *)
(*                      where d is the display of T                           *)
(*     {subset[d] T} := {set T}                                               *)
(*                   == an alias for set which is canonically ordered by the  *)
(*                      subset order and displayed in display d               *)
(*        {subset T} := {subset[subset_display] T}                            *)
(*                                                                            *)
(* We provide expected instances of ordered types for T *prod[disp] T',       *)
(* n.-tupleprod[disp] (using product order), {subset[disp] T} (using subset   *)
(* order) and all possible finite type instances.                             *)
(* (Use `HB.about type` to discover the instances on type.)                   *)
(*                                                                            *)
(* In order to get a canonical product order on prod, tuple, and set, one may *)
(* import modules DefaultProdOrder, DefaultTupleProdOrder, and                *)
(* DefaultSetSubsetOrder.                                                     *)
(*                                                                            *)
(* Acknowledgments: The files in this directory are based on prior work by    *)
(* D. Dreyer, G. Gonthier, A. Nanevski, P-Y Strub, B. Ziliani                 *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope order_scope.

(* Reserved notations for product ordering of prod *)
Reserved Notation "x <=^p y" (at level 70, y at next level).
Reserved Notation "x >=^p y" (at level 70, y at next level).
Reserved Notation "x <^p y" (at level 70, y at next level).
Reserved Notation "x >^p y" (at level 70, y at next level).
Reserved Notation "x <=^p y :> T" (at level 70, y at next level).
Reserved Notation "x >=^p y :> T" (at level 70, y at next level).
Reserved Notation "x <^p y :> T" (at level 70, y at next level).
Reserved Notation "x >^p y :> T" (at level 70, y at next level).
Reserved Notation "<=^p y" (at level 35).
Reserved Notation ">=^p y" (at level 35).
Reserved Notation "<^p y" (at level 35).
Reserved Notation ">^p y" (at level 35).
Reserved Notation "<=^p y :> T" (at level 35, y at next level).
Reserved Notation ">=^p y :> T" (at level 35, y at next level).
Reserved Notation "<^p y :> T" (at level 35, y at next level).
Reserved Notation ">^p y :> T" (at level 35, y at next level).
Reserved Notation "x >=<^p y" (at level 70, no associativity).
Reserved Notation ">=<^p x" (at level 35).
Reserved Notation ">=<^p y :> T" (at level 35, y at next level).
Reserved Notation "x ><^p y" (at level 70, no associativity).
Reserved Notation "><^p x" (at level 35).
Reserved Notation "><^p y :> T" (at level 35, y at next level).

Reserved Notation "x <=^p y <=^p z" (at level 70, y, z at next level).
Reserved Notation "x <^p y <=^p z" (at level 70, y, z at next level).
Reserved Notation "x <=^p y <^p z" (at level 70, y, z at next level).
Reserved Notation "x <^p y <^p z" (at level 70, y, z at next level).
Reserved Notation "x <=^p y ?= 'iff' c" (at level 70, y, c at next level,
  format "x '[hv'  <=^p  y '/'  ?=  'iff'  c ']'").
Reserved Notation "x <=^p y ?= 'iff' c :> T" (at level 70, y, c at next level,
  format "x '[hv'  <=^p  y '/'  ?=  'iff'  c  :> T ']'").

Reserved Notation "\bot^p".
Reserved Notation "\top^p".

Reserved Notation "A `&^p` B"  (at level 48, left associativity).
Reserved Notation "A `|^p` B" (at level 52, left associativity).
Reserved Notation "A `\^p` B" (at level 50, left associativity).
Reserved Notation "~^p` A" (at level 35, right associativity).

Reserved Notation "\meet^p_ i F"
  (at level 34, F at level 41, i at level 0,
           format "'[' \meet^p_ i '/  '  F ']'").
Reserved Notation "\meet^p_ ( i <- r | P ) F"
  (at level 34, F at level 41, i, r at level 60,
           format "'[' \meet^p_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\meet^p_ ( i <- r ) F"
  (F at level 41,
           format "'[' \meet^p_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\meet^p_ ( m <= i < n | P ) F"
  (F at level 41, i, n at level 60,
           format "'[' \meet^p_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\meet^p_ ( m <= i < n ) F"
  (F at level 41,
           format "'[' \meet^p_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\meet^p_ ( i | P ) F"
  (F at level 41,
           format "'[' \meet^p_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\meet^p_ ( i : t | P ) F" (F at level 41).
Reserved Notation "\meet^p_ ( i : t ) F" (F at level 41).
Reserved Notation "\meet^p_ ( i < n | P ) F"
  (F at level 41, n at level 60,
           format "'[' \meet^p_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\meet^p_ ( i < n ) F"
  (F at level 41,
           format "'[' \meet^p_ ( i  <  n )  F ']'").
Reserved Notation "\meet^p_ ( i 'in' A | P ) F"
  (F at level 41, A at level 60,
           format "'[' \meet^p_ ( i  'in'  A  |  P ) '/  '  F ']'").
Reserved Notation "\meet^p_ ( i 'in' A ) F"
  (F at level 41,
           format "'[' \meet^p_ ( i  'in'  A ) '/  '  F ']'").

Reserved Notation "\join^p_ i F"
  (at level 34, F at level 41, i at level 0,
           format "'[' \join^p_ i '/  '  F ']'").
Reserved Notation "\join^p_ ( i <- r | P ) F"
  (at level 34, F at level 41, i, r at level 60,
           format "'[' \join^p_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\join^p_ ( i <- r ) F"
  (F at level 41,
           format "'[' \join^p_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\join^p_ ( m <= i < n | P ) F"
  (F at level 41, i, n at level 60,
           format "'[' \join^p_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\join^p_ ( m <= i < n ) F"
  (F at level 41,
           format "'[' \join^p_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\join^p_ ( i | P ) F"
  (F at level 41,
           format "'[' \join^p_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\join^p_ ( i : t | P ) F" (F at level 41).
Reserved Notation "\join^p_ ( i : t ) F" (F at level 41).
Reserved Notation "\join^p_ ( i < n | P ) F"
  (F at level 41, n at level 60,
           format "'[' \join^p_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\join^p_ ( i < n ) F"
  (F at level 41,
           format "'[' \join^p_ ( i  <  n )  F ']'").
Reserved Notation "\join^p_ ( i 'in' A | P ) F"
  (F at level 41, A at level 60,
           format "'[' \join^p_ ( i  'in'  A  |  P ) '/  '  F ']'").
Reserved Notation "\join^p_ ( i 'in' A ) F"
  (F at level 41,
           format "'[' \join^p_ ( i  'in'  A ) '/  '  F ']'").

Reserved Notation "\min^p_ i F"
  (at level 34, F at level 41, i at level 0,
           format "'[' \min^p_ i '/  '  F ']'").
Reserved Notation "\min^p_ ( i <- r | P ) F"
  (at level 34, F at level 41, i, r at level 60,
           format "'[' \min^p_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\min^p_ ( i <- r ) F"
  (F at level 41,
           format "'[' \min^p_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\min^p_ ( m <= i < n | P ) F"
  (F at level 41, i, n at level 60,
           format "'[' \min^p_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\min^p_ ( m <= i < n ) F"
  (F at level 41,
           format "'[' \min^p_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\min^p_ ( i | P ) F"
  (F at level 41,
           format "'[' \min^p_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\min^p_ ( i : t | P ) F" (F at level 41).
Reserved Notation "\min^p_ ( i : t ) F" (F at level 41).
Reserved Notation "\min^p_ ( i < n | P ) F"
  (F at level 41, n at level 60,
           format "'[' \min^p_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\min^p_ ( i < n ) F"
  (F at level 41,
           format "'[' \min^p_ ( i  <  n )  F ']'").
Reserved Notation "\min^p_ ( i 'in' A | P ) F"
  (F at level 41, A at level 60,
           format "'[' \min^p_ ( i  'in'  A  |  P ) '/  '  F ']'").
Reserved Notation "\min^p_ ( i 'in' A ) F"
  (F at level 41,
           format "'[' \min^p_ ( i  'in'  A ) '/  '  F ']'").

Reserved Notation "\max^p_ i F"
  (at level 34, F at level 41, i at level 0,
           format "'[' \max^p_ i '/  '  F ']'").
Reserved Notation "\max^p_ ( i <- r | P ) F"
  (at level 34, F at level 41, i, r at level 60,
           format "'[' \max^p_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\max^p_ ( i <- r ) F"
  (F at level 41,
           format "'[' \max^p_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\max^p_ ( m <= i < n | P ) F"
  (F at level 41, i, n at level 60,
           format "'[' \max^p_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\max^p_ ( m <= i < n ) F"
  (F at level 41,
           format "'[' \max^p_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\max^p_ ( i | P ) F"
  (F at level 41,
           format "'[' \max^p_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\max^p_ ( i : t | P ) F" (F at level 41).
Reserved Notation "\max^p_ ( i : t ) F" (F at level 41).
Reserved Notation "\max^p_ ( i < n | P ) F"
  (F at level 41, n at level 60,
           format "'[' \max^p_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\max^p_ ( i < n ) F"
  (F at level 41,
           format "'[' \max^p_ ( i  <  n )  F ']'").
Reserved Notation "\max^p_ ( i 'in' A | P ) F"
  (F at level 41, A at level 60,
           format "'[' \max^p_ ( i  'in'  A  |  P ) '/  '  F ']'").
Reserved Notation "\max^p_ ( i 'in' A ) F"
  (F at level 41,
           format "'[' \max^p_ ( i  'in'  A ) '/  '  F ']'").

Module Order.

Import Order Order.Theory.

(******************************)
(* Definition of prod_display *)
(******************************)

Fact prod_display_unit (_ _ : unit) : unit. Proof. exact: tt. Qed.

Definition prod_display (displ dispr : disp_t) : disp_t :=
  Disp (prod_display_unit (d1 displ) (d1 dispr))
       (prod_display_unit (d2 displ) (d2 dispr)).

Module Import ProdSyntax.

Notation "<=^p%O" := (@le (prod_display _ _) _) : function_scope.
Notation ">=^p%O" := (@ge (prod_display _ _) _)  : function_scope.
Notation ">=^p%O" := (@ge (prod_display _ _) _)  : function_scope.
Notation "<^p%O" := (@lt (prod_display _ _) _) : function_scope.
Notation ">^p%O" := (@gt (prod_display _ _) _) : function_scope.
Notation "<?=^p%O" := (@leif (prod_display _ _) _) : function_scope.
Notation ">=<^p%O" := (@comparable (prod_display _ _) _) : function_scope.
Notation "><^p%O" := (fun x y => ~~ (@comparable (prod_display _ _) _ x y)) :
  function_scope.

Notation "<=^p y" := (>=^p%O y) : order_scope.
Notation "<=^p y :> T" := (<=^p (y : T)) (only parsing) : order_scope.
Notation ">=^p y"  := (<=^p%O y) : order_scope.
Notation ">=^p y :> T" := (>=^p (y : T)) (only parsing) : order_scope.

Notation "<^p y" := (>^p%O y) : order_scope.
Notation "<^p y :> T" := (<^p (y : T)) (only parsing) : order_scope.
Notation ">^p y" := (<^p%O y) : order_scope.
Notation ">^p y :> T" := (>^p (y : T)) (only parsing) : order_scope.

Notation "x <=^p y" := (<=^p%O x y) : order_scope.
Notation "x <=^p y :> T" := ((x : T) <=^p (y : T)) (only parsing) : order_scope.
Notation "x >=^p y" := (y <=^p x) (only parsing) : order_scope.
Notation "x >=^p y :> T" := ((x : T) >=^p (y : T)) (only parsing) : order_scope.

Notation "x <^p y"  := (<^p%O x y) : order_scope.
Notation "x <^p y :> T" := ((x : T) <^p (y : T)) (only parsing) : order_scope.
Notation "x >^p y"  := (y <^p x) (only parsing) : order_scope.
Notation "x >^p y :> T" := ((x : T) >^p (y : T)) (only parsing) : order_scope.

Notation "x <=^p y <=^p z" := ((x <=^p y) && (y <=^p z)) : order_scope.
Notation "x <^p y <=^p z" := ((x <^p y) && (y <=^p z)) : order_scope.
Notation "x <=^p y <^p z" := ((x <=^p y) && (y <^p z)) : order_scope.
Notation "x <^p y <^p z" := ((x <^p y) && (y <^p z)) : order_scope.

Notation "x <=^p y ?= 'iff' C" := (<?=^p%O x y C) : order_scope.
Notation "x <=^p y ?= 'iff' C :> T" := ((x : T) <=^p (y : T) ?= iff C)
  (only parsing) : order_scope.

Notation ">=<^p y" := [pred x | >=<^p%O x y] : order_scope.
Notation ">=<^p y :> T" := (>=<^p (y : T)) (only parsing) : order_scope.
Notation "x >=<^p y" := (>=<^p%O x y) : order_scope.

Notation "><^p y" := [pred x | ~~ (>=<^p%O x y)] : order_scope.
Notation "><^p y :> T" := (><^p (y : T)) (only parsing) : order_scope.
Notation "x ><^p y" := (~~ (><^p%O x y)) : order_scope.

(* The following Local Notations are here to define the \join^p_ and \meet^p_ *)
(* notations later. Do not remove them.                                       *)
Local Notation "\bot" := (@bottom (prod_display _ _) _).
Local Notation "\top" := (@top (prod_display _ _) _).
Local Notation meet := (@meet (prod_display _ _) _).
Local Notation join := (@join (prod_display _ _) _).
Local Notation min := (@min (prod_display _ _) _).
Local Notation max := (@max (prod_display _ _) _).

Notation "x `&^p` y" :=  (meet x y) : order_scope.
Notation "x `|^p` y" := (join x y) : order_scope.

Notation "\join^p_ ( i <- r | P ) F" :=
  (\big[join / \bot]_(i <- r | P%B) F%O) : order_scope.
Notation "\join^p_ ( i <- r ) F" :=
  (\big[join / \bot]_(i <- r) F%O) : order_scope.
Notation "\join^p_ ( i | P ) F" :=
  (\big[join / \bot]_(i | P%B) F%O) : order_scope.
Notation "\join^p_ i F" :=
  (\big[join / \bot]_i F%O) : order_scope.
Notation "\join^p_ ( i : I | P ) F" :=
  (\big[join / \bot]_(i : I | P%B) F%O) (only parsing) : order_scope.
Notation "\join^p_ ( i : I ) F" :=
  (\big[join / \bot]_(i : I) F%O) (only parsing) : order_scope.
Notation "\join^p_ ( m <= i < n | P ) F" :=
 (\big[join / \bot]_(m <= i < n | P%B) F%O) : order_scope.
Notation "\join^p_ ( m <= i < n ) F" :=
 (\big[join / \bot]_(m <= i < n) F%O) : order_scope.
Notation "\join^p_ ( i < n | P ) F" :=
 (\big[join / \bot]_(i < n | P%B) F%O) : order_scope.
Notation "\join^p_ ( i < n ) F" :=
 (\big[join / \bot]_(i < n) F%O) : order_scope.
Notation "\join^p_ ( i 'in' A | P ) F" :=
 (\big[join / \bot]_(i in A | P%B) F%O) : order_scope.
Notation "\join^p_ ( i 'in' A ) F" :=
 (\big[join / \bot]_(i in A) F%O) : order_scope.

Notation "\meet^p_ ( i <- r | P ) F" :=
  (\big[meet / \top]_(i <- r | P%B) F%O) : order_scope.
Notation "\meet^p_ ( i <- r ) F" :=
  (\big[meet / \top]_(i <- r) F%O) : order_scope.
Notation "\meet^p_ ( i | P ) F" :=
  (\big[meet / \top]_(i | P%B) F%O) : order_scope.
Notation "\meet^p_ i F" :=
  (\big[meet / \top]_i F%O) : order_scope.
Notation "\meet^p_ ( i : I | P ) F" :=
  (\big[meet / \top]_(i : I | P%B) F%O) (only parsing) : order_scope.
Notation "\meet^p_ ( i : I ) F" :=
  (\big[meet / \top]_(i : I) F%O) (only parsing) : order_scope.
Notation "\meet^p_ ( m <= i < n | P ) F" :=
 (\big[meet / \top]_(m <= i < n | P%B) F%O) : order_scope.
Notation "\meet^p_ ( m <= i < n ) F" :=
 (\big[meet / \top]_(m <= i < n) F%O) : order_scope.
Notation "\meet^p_ ( i < n | P ) F" :=
 (\big[meet / \top]_(i < n | P%B) F%O) : order_scope.
Notation "\meet^p_ ( i < n ) F" :=
 (\big[meet / \top]_(i < n) F%O) : order_scope.
Notation "\meet^p_ ( i 'in' A | P ) F" :=
 (\big[meet / \top]_(i in A | P%B) F%O) : order_scope.
Notation "\meet^p_ ( i 'in' A ) F" :=
 (\big[meet / \top]_(i in A) F%O) : order_scope.

Notation "\min^p_ i F" :=
  (\big[min/top]_i F) : order_scope.
Notation "\min^p_ ( i <- r | P ) F" :=
  (\big[min/top]_(i <- r | P%B) F%O) : order_scope.
Notation "\min^p_ ( i < r ) F" :=
  (\big[min/top]_(i <- r) F%O) : order_scope.
Notation "\min^p_ ( m <= i < n | P ) F" :=
  (\big[min/top]_(m <= i < n | P%B) F%O) : order_scope.
Notation "\min^p_ ( m <= i < n ) F" :=
  (\big[min/top]_(m <= i < n) F%O) : order_scope.
Notation "\min^p_ ( i | P ) F" :=
  (\big[min/top]_(i | P%B) F%O) : order_scope.
Notation "\min^p_ ( i : t | P ) F" :=
  (\big[min/top]_(i : t | P%B) F%O) (only parsing) : order_scope.
Notation "\min^p_ ( i : t ) F" :=
  (\big[min/top]_(i : t) F%O) (only parsing) : order_scope.
Notation "\min^p_ ( i < n | P ) F" :=
  (\big[min/top]_(i < n | P%B) F%O) : order_scope.
Notation "\min^p_ ( i < n ) F" :=
  (\big[min/top]_(i < n) F%O) : order_scope.
Notation "\min^p_ ( i 'in' A | P ) F" :=
  (\big[min/top]_(i in A | P%B) F%O) : order_scope.
Notation "\min^p_ ( i 'in' A ) F" :=
  (\big[min/top]_(i in A) F%O) : order_scope.

Notation "\max^p_ i F" :=
  (\big[max/bottom]_i F%O) : order_scope.
Notation "\max^p_ ( i <- r | P ) F" :=
  (\big[max/bottom]_(i <- r | P%B) F%O) : order_scope.
Notation "\max^p_ ( i < r ) F" :=
  (\big[max/bottom]_(i <- r) F%O) : order_scope.
Notation "\max^p_ ( m <= i < n | P ) F" :=
  (\big[max/bottom]_(m <= i < n | P%B) F%O) : order_scope.
Notation "\max^p_ ( m <= i < n ) F" :=
  (\big[max/bottom]_(m <= i < n) F%O) : order_scope.
Notation "\max^p_ ( i | P ) F" :=
  (\big[max/bottom]_(i | P%B) F%O) : order_scope.
Notation "\max^p_ ( i : t | P ) F" :=
  (\big[max/bottom]_(i : t | P%B) F%O) (only parsing) : order_scope.
Notation "\max^p_ ( i : t ) F" :=
  (\big[max/bottom]_(i : t) F%O) (only parsing) : order_scope.
Notation "\max^p_ ( i < n | P ) F" :=
  (\big[max/bottom]_(i < n | P%B) F%O) : order_scope.
Notation "\max^p_ ( i < n ) F" :=
  (\big[max/bottom]_(i < n) F%O) : order_scope.
Notation "\max^p_ ( i 'in' A | P ) F" :=
  (\big[max/bottom]_(i in A | P%B) F%O) : order_scope.
Notation "\max^p_ ( i 'in' A ) F" :=
  (\big[max/bottom]_(i in A) F%O) : order_scope.

End ProdSyntax.

(************************************************)
(* We declare an alias of the cartesian product *)
(* which has canonical product order.           *)
(************************************************)

Module ProdOrder.

Local Open Scope type_scope. (* FIXME *)

Definition type (disp : disp_t) (T T' : Type) := T * T'.
Definition type_
  (disp1 disp2 : disp_t) (T : preorderType disp1) (T' : preorderType disp2) :=
  type (prod_display disp1 disp2) T T'.

Section Basis.
Context {disp : disp_t}.

Local Notation "T * T'" := (type disp T T') : type_scope.

#[export] HB.instance Definition _ (T T' : eqType) := Equality.on (T * T').
#[export] HB.instance Definition _ (T T' : choiceType) := Choice.on (T * T').
#[export] HB.instance Definition _ (T T' : countType) := Countable.on (T * T').
#[export] HB.instance Definition _ (T T' : finType) := Finite.on (T * T').

End Basis.

Section Preorder.
Context (disp1 disp2 : disp_t).
Context (T1 : preorderType disp1) (T2 : preorderType disp2).
Implicit Types (x y : T1 * T2).

Let le x y := (x.1 <= y.1) && (x.2 <= y.2).

Let lt x y := (x.1 < y.1) && (x.2 <= y.2) || (x.1 <= y.1) && (x.2 < y.2).

Fact lt_def x y : lt x y = le x y && ~~ le y x.
Proof.
rewrite /lt /le !lt_leAnge -andbA -andb_orr.
by rewrite [~~ _ && _]andbC -andb_orr andbA negb_and.
Qed.

Fact refl : reflexive le. Proof. by move=> ?; rewrite /le !lexx. Qed.

Fact trans : transitive le.
Proof.
rewrite /le => y x z /andP [] hxy ? /andP [] /(le_trans hxy) ->.
by apply: le_trans.
Qed.

End Preorder.

Section Preorder.
Context (disp1 disp2 disp3 : disp_t).
Context (T1 : preorderType disp1) (T2 : preorderType disp2).
Local Notation "T1 * T2" := (type disp3 T1 T2) : type_scope.
Implicit Types (x y : T1 * T2).

Let T1' : Type := T1.
HB.instance Definition _ := Preorder.on T1'.
Let T2' : Type := T2.
HB.instance Definition _ := Preorder.on T2'.

Definition le x y := (x.1 <= y.1) && (x.2 <= y.2).

Definition lt x y := (x.1 < y.1) && (x.2 <= y.2) || (x.1 <= y.1) && (x.2 < y.2).

#[export] HB.instance Definition _ :=
  @isDuallyPreorder.Build disp3 (T1 * T2) le lt
    (@lt_def _ _ T1' T2') (@lt_def _ _ T1^d T2^d)
    (@refl _ _ T1' T2') (@refl _ _ T1^d T2^d)
    (@trans _ _ T1' T2') (@trans _ _ T1^d T2^d).

Lemma leEprod x y : (x <= y) = (x.1 <= y.1) && (x.2 <= y.2). Proof. by []. Qed.

Lemma ltEprod x y :
  (x < y) = (x.1 < y.1) && (x.2 <= y.2) || (x.1 <= y.1) && (x.2 < y.2).
Proof.
rewrite lt_leAnge !leEprod negb_and andb_orr andbAC -lt_leAnge -andbA.
by rewrite -lt_leAnge.
Qed.

Lemma le_pair (x1 y1 : T1) (x2 y2 : T2) :
  ((x1, x2) <= (y1, y2) :> T1 * T2) = (x1 <= y1) && (x2 <= y2).
Proof. by []. Qed.

Lemma lt_pair (x1 y1 : T1) (x2 y2 : T2) :
  ((x1, x2) < (y1, y2) :> T1 * T2)
  = (x1 < y1) && (x2 <= y2) || (x1 <= y1) && (x2 < y2).
Proof. exact/ltEprod. Qed.

End Preorder.

Section BPreorder.
Context (disp1 disp2 : disp_t).
Context (T1 : bPreorderType disp1) (T2 : bPreorderType disp2).
Local Notation "T1 * T2" := (type (Disp tt tt) T1 T2) : type_scope.
Implicit Types (x : T1 * T2).

Fact le0x x : (\bot, \bot) <= x :> T1 * T2.
Proof. by rewrite leEprod !le0x. Qed.

End BPreorder.

Section BPreorder.
Context (disp1 disp2 disp3 : disp_t).
Context (T1 : bPreorderType disp1) (T2 : bPreorderType disp2).
Local Notation "T1 * T2" := (type disp3 T1 T2) : type_scope.

Let T1' : Type := T1.
HB.instance Definition _ := BPreorder.on T1'.
Let T2' : Type := T2.
HB.instance Definition _ := BPreorder.on T2'.

#[export] HB.instance Definition _ :=
  @hasBottom.Build disp3 (T1 * T2) (\bot, \bot) (@le0x _ _ T1' T2').

Lemma botEprod : \bot = (\bot, \bot) :> T1 * T2. Proof. by []. Qed.

End BPreorder.

Section TPreorder.
Context (disp1 disp2 disp3 : disp_t).
Context (T1 : tPreorderType disp1) (T2 : tPreorderType disp2).
Local Notation "T1 * T2" := (type disp3 T1 T2) : type_scope.

#[export] HB.instance Definition _ :=
  @hasTop.Build disp3 (T1 * T2) (\top, \top) (@le0x _ _ T1^d T2^d).

Lemma topEprod : \top = (\top, \top) :> T1 * T2. Proof. by []. Qed.

End TPreorder.

Section POrder.
Context (disp1 disp2 disp3 : disp_t).
Context (T1 : porderType disp1) (T2 : porderType disp2).

Fact anti : antisymmetric (@le disp1 disp2 disp2 T1 T2).
Proof.
case=> [? ?] [? ?].
by rewrite andbAC andbA andbAC -andbA => /= /andP [] /le_anti -> /le_anti ->.
Qed.

End POrder.

Section POrder.
Context (disp1 disp2 disp3 : disp_t).
Context (T1 : porderType disp1) (T2 : porderType disp2).
Local Notation "T1 * T2" := (type disp3 T1 T2) : type_scope.
Implicit Types (x y : T1 * T2).

Let T1' : Type := T1.
HB.instance Definition _ := POrder.on T1'.
Let T2' : Type := T2.
HB.instance Definition _ := POrder.on T2'.

#[export] HB.instance Definition _ :=
  Preorder_isDuallyPOrder.Build disp3 (T1 * T2)
    (@anti _ _ T1' T2') (@anti _ _ T1^d T2^d).

(* FIXME: name collision with ltEprod and lt_pair above *)
Lemma ltEprod' x y : (x < y) = [&& x != y, x.1 <= y.1 & x.2 <= y.2].
Proof. by rewrite lt_neqAle. Qed.

Lemma lt_pair' (x1 y1 : T1) (x2 y2 : T2) : ((x1, x2) < (y1, y2) :> T1 * T2) =
  [&& (x1 != y1) || (x2 != y2), x1 <= y1 & x2 <= y2].
Proof. by rewrite ltEprod' negb_and. Qed.

End POrder.

Section MeetSemilattice.
Context (disp1 disp2 : disp_t).
Context (T1 : meetSemilatticeType disp1) (T2 : meetSemilatticeType disp2).
Local Notation "T1 * T2" := (type (Disp tt tt) T1 T2) : type_scope.
Implicit Types (x y : T1 * T2).

Let meet x y := (x.1 `&` y.1, x.2 `&` y.2).

Fact lexI x y z : (x <= meet y z) = (x <= y) && (x <= z).
Proof. by rewrite leEprod !lexI andbACA. Qed.

End MeetSemilattice.

Section MeetSemilattice.
Context (disp1 disp2 disp3 : disp_t).
Context (T1 : meetSemilatticeType disp1) (T2 : meetSemilatticeType disp2).
Local Notation "T1 * T2" := (type disp3 T1 T2) : type_scope.
Implicit Types (x y : T1 * T2).

Let T1' : Type := T1.
HB.instance Definition _ := MeetSemilattice.on T1'.
Let T2' : Type := T2.
HB.instance Definition _ := MeetSemilattice.on T2'.

Definition meet x y := (x.1 `&` y.1, x.2 `&` y.2).

#[export] HB.instance Definition _ :=
  @POrder_isMeetSemilattice.Build disp3 (T1 * T2) meet (@lexI _ _ T1' T2').

Lemma meetEprod x y : x `&` y = (x.1 `&` y.1, x.2 `&` y.2). Proof. by []. Qed.

End MeetSemilattice.

Section JoinSemilattice.
Context (disp1 disp2 disp3 : disp_t).
Context (T1 : joinSemilatticeType disp1) (T2 : joinSemilatticeType disp2).
Local Notation "T1 * T2" := (type disp3 T1 T2) : type_scope.
Implicit Types (x y : T1 * T2).

Definition join x y := (x.1 `|` y.1, x.2 `|` y.2).

#[export] HB.instance Definition _ :=
  @POrder_isJoinSemilattice.Build disp3 (T1 * T2) join
    (fun x y z => @lexI _ _ T1^d T2^d z x y).

Lemma joinEprod x y : x `|` y = (x.1 `|` y.1, x.2 `|` y.2). Proof. by []. Qed.

End JoinSemilattice.

(* FIXME: use HB.saturate *)
Section TBOrder.
Context (disp1 disp2 disp3 : disp_t).

#[export] HB.instance Definition _
  (T1 : tbPreorderType disp1) (T2 : tbPreorderType disp2) :=
  Preorder.on (type disp3 T1 T2).

#[export] HB.instance Definition _
  (T1 : bPOrderType disp1) (T2 : bPOrderType disp2) :=
    POrder.on (type disp3 T1 T2).
#[export] HB.instance Definition _
  (T1 : tPOrderType disp1) (T2 : tPOrderType disp2) :=
    POrder.on (type disp3 T1 T2).
#[export] HB.instance Definition _
  (T1 : tbPOrderType disp1) (T2 : tbPOrderType disp2) :=
    POrder.on (type disp3 T1 T2).

#[export] HB.instance Definition _
  (T1 : bMeetSemilatticeType disp1) (T2 : bMeetSemilatticeType disp2) :=
  POrder.on (type disp3 T1 T2).
#[export] HB.instance Definition _
  (T1 : tMeetSemilatticeType disp1) (T2 : tMeetSemilatticeType disp2) :=
  POrder.on (type disp3 T1 T2).
#[export] HB.instance Definition _
  (T1 : tbMeetSemilatticeType disp1) (T2 : tbMeetSemilatticeType disp2) :=
  POrder.on (type disp3 T1 T2).

#[export] HB.instance Definition _
  (T1 : bJoinSemilatticeType disp1) (T2 : bJoinSemilatticeType disp2) :=
  POrder.on (type disp3 T1 T2).
#[export] HB.instance Definition _
  (T1 : tJoinSemilatticeType disp1) (T2 : tJoinSemilatticeType disp2) :=
  POrder.on (type disp3 T1 T2).
#[export] HB.instance Definition _
  (T1 : tbJoinSemilatticeType disp1) (T2 : tbJoinSemilatticeType disp2) :=
  POrder.on (type disp3 T1 T2).

#[export] HB.instance Definition _
  (T1 : latticeType disp1) (T2 : latticeType disp2) :=
    POrder.on (type disp3 T1 T2).
#[export] HB.instance Definition _
  (T1 : bLatticeType disp1) (T2 : bLatticeType disp2) :=
    POrder.on (type disp3 T1 T2).
#[export] HB.instance Definition _
  (T1 : tLatticeType disp1) (T2 : tLatticeType disp2) :=
    POrder.on (type disp3 T1 T2).
#[export] HB.instance Definition _
  (T1 : tbLatticeType disp1) (T2 : tbLatticeType disp2) :=
    POrder.on (type disp3 T1 T2).

End TBOrder.
(* /FIXME *)

Section DistrLattice.
Context (disp1 disp2 : disp_t).
Context (T1 : distrLatticeType disp1) (T2 : distrLatticeType disp2).
Local Notation "T1 * T2" := (type (Disp tt tt) T1 T2) : type_scope.

Fact meetUl : @left_distributive (T1 * T2) _ Order.meet Order.join.
Proof. by move=> ? ? ?; rewrite meetEprod !meetUl. Qed.

End DistrLattice.

Section DistrLattice.
Context (disp1 disp2 disp3 : disp_t).
Context (T1 : distrLatticeType disp1) (T2 : distrLatticeType disp2).
Local Notation "T1 * T2" := (type disp3 T1 T2) : type_scope.

Let T1' : Type := T1.
HB.instance Definition _ := DistrLattice.on T1'.
Let T2' : Type := T2.
HB.instance Definition _ := DistrLattice.on T2'.

#[export]
HB.instance Definition _ := Lattice_isDistributive.Build disp3 (T1 * T2)
  (@meetUl _ _ T1' T2') (@meetUl _ _ T1^d T2^d).

End DistrLattice.

(* FIXME: use HB.saturate *)
#[export] HB.instance Definition _ (disp1 disp2 disp3 : disp_t)
  (T1 : bDistrLatticeType disp1) (T2 : bDistrLatticeType disp2) :=
  POrder.on (type disp3 T1 T2).
#[export] HB.instance Definition _ (disp1 disp2 disp3 : disp_t)
  (T1 : tDistrLatticeType disp1) (T2 : tDistrLatticeType disp2) :=
  POrder.on (type disp3 T1 T2).
#[export] HB.instance Definition _ (disp1 disp2 disp3 : disp_t)
  (T1 : tbDistrLatticeType disp1) (T2 : tbDistrLatticeType disp2) :=
  POrder.on (type disp3 T1 T2).
(* /FIXME *)

Section CDistrLattice.
Context (disp1 disp2 : disp_t).
Context (T1 : cDistrLatticeType disp1) (T2 : cDistrLatticeType disp2).
Local Notation "T1 * T2" := (type (Disp tt tt) T1 T2) : type_scope.
Implicit Types (x y z : T1 * T2).

Let rcompl x y z := (rcompl x.1 y.1 z.1, rcompl x.2 y.2 z.2).

Fact rcomplPmeet x y z : ((x `&` y) `|` z) `&` rcompl x y z = x `&` y.
Proof. by rewrite !(meetEprod, joinEprod) !rcomplPmeet. Qed.

End CDistrLattice.

Section CDistrLattice.
Context (disp1 disp2 disp3 : disp_t).
Context (T1 : cDistrLatticeType disp1) (T2 : cDistrLatticeType disp2).
Local Notation "T1 * T2" := (type disp3 T1 T2) : type_scope.
Implicit Types (x y z : T1 * T2).

Let T1' : Type := T1.
HB.instance Definition _ := CDistrLattice.on T1'.
Let T2' : Type := T2.
HB.instance Definition _ := CDistrLattice.on T2'.

Definition rcompl x y z := (rcompl x.1 y.1 z.1, rcompl x.2 y.2 z.2).

#[export] HB.instance Definition _ :=
  @DistrLattice_hasRelativeComplement.Build disp3 (T1 * T2)
    rcompl (@rcomplPmeet _ _ T1' T2')
    (fun x y => @rcomplPmeet _ _ T1^d T2^d y x).

Lemma rcomplEprod x y z :
  rcompl x y z = (Order.rcompl x.1 y.1 z.1, Order.rcompl x.2 y.2 z.2).
Proof. by []. Qed.

End CDistrLattice.

Section CBDistrLattice.
Context (disp1 disp2 : disp_t).
Context (T1 : cbDistrLatticeType disp1) (T2 : cbDistrLatticeType disp2).
Local Notation "T1 * T2" := (type (Disp tt tt) T1 T2) : type_scope.
Implicit Types (x y : T1 * T2).

Let diff x y := (diff x.1 y.1, diff x.2 y.2).

Fact diffErcompl x y : diff x y = rcompl \bot x y.
Proof. by rewrite /diff !diffErcompl. Qed.

End CBDistrLattice.

Section CBDistrLattice.
Context (disp1 disp2 disp3 : disp_t).
Context (T1 : cbDistrLatticeType disp1) (T2 : cbDistrLatticeType disp2).
Local Notation "T1 * T2" := (type disp3 T1 T2) : type_scope.
Implicit Types (x y : T1 * T2).

Let T1' : Type := T1.
HB.instance Definition _ := CBDistrLattice.on T1'.
Let T2' : Type := T2.
HB.instance Definition _ := CBDistrLattice.on T2'.

Definition diff x y := (diff x.1 y.1, diff x.2 y.2).

#[export] HB.instance Definition _ :=
  @CDistrLattice_hasSectionalComplement.Build disp3 (T1 * T2)
    diff (@diffErcompl _ _ T1' T2').

Lemma diffEprod x y : x `\` y = (x.1 `\` y.1, x.2 `\` y.2). Proof. by []. Qed.

End CBDistrLattice.

Section CTDistrLattice.
Context (disp1 disp2 disp3 : disp_t).
Context (T1 : ctDistrLatticeType disp1) (T2 : ctDistrLatticeType disp2).
Local Notation "T1 * T2" := (type disp3 T1 T2) : type_scope.
Implicit Types (x y : T1 * T2).

Definition codiff x y := (codiff x.1 y.1, codiff x.2 y.2).

#[export] HB.instance Definition _ :=
  @CDistrLattice_hasDualSectionalComplement.Build disp3 (T1 * T2)
    codiff (@diffErcompl _ _ T1^d T2^d).

Lemma codiffEprod x y :
  codiff x y = (Order.codiff x.1 y.1, Order.codiff x.2 y.2).
Proof. by []. Qed.

End CTDistrLattice.

Section CTBDistrLattice.
Context (disp1 disp2 : disp_t).
Context (T1 : ctbDistrLatticeType disp1) (T2 : ctbDistrLatticeType disp2).
Local Notation "T1 * T2" := (type (Disp tt tt) T1 T2) : type_scope.
Implicit Types (x : T1 * T2).

Let compl x := (~` x.1, ~` x.2).

Fact complEdiff x : compl x = (\top : T1 * T2) `\` x.
Proof. by rewrite /compl !complEdiff. Qed.

End CTBDistrLattice.

Section CTBDistrLattice.
Context (disp1 disp2 disp3 : disp_t).
Context (T1 : ctbDistrLatticeType disp1) (T2 : ctbDistrLatticeType disp2).
Local Notation "T1 * T2" := (type disp3 T1 T2) : type_scope.
Implicit Types (x : T1 * T2).

Let T1' : Type := T1.
HB.instance Definition _ := CTBDistrLattice.on T1'.
Let T2' : Type := T2.
HB.instance Definition _ := CTBDistrLattice.on T2'.

Definition compl x := (~` x.1, ~` x.2).

#[export] HB.instance Definition _ :=
  @CDistrLattice_hasComplement.Build _ (T1 * T2) compl
    (@complEdiff _ _ T1' T2') (@complEdiff _ _ T1^d T2^d).

Lemma complEprod x : ~` x = (~` x.1, ~` x.2). Proof. by []. Qed.

End CTBDistrLattice.

(* FIXME: use HB.saturate *)
Section FinOrder.
Context (disp1 disp2 disp3 : disp_t).

#[export] HB.instance Definition _
  (T1 : finPreorderType disp1) (T2 : finPreorderType disp2) :=
    Preorder.on (type disp3 T1 T2).
#[export] HB.instance Definition _
  (T1 : finBPreorderType disp1) (T2 : finBPreorderType disp2) :=
    Preorder.on (type disp3 T1 T2).
#[export] HB.instance Definition _
  (T1 : finTPreorderType disp1) (T2 : finTPreorderType disp2) :=
    Preorder.on (type disp3 T1 T2).
#[export] HB.instance Definition _
  (T1 : finTBPreorderType disp1) (T2 : finTBPreorderType disp2) :=
    Preorder.on (type disp3 T1 T2).

#[export] HB.instance Definition _
  (T1 : finPOrderType disp1) (T2 : finPOrderType disp2) :=
    POrder.on (type disp3 T1 T2).
#[export] HB.instance Definition _
  (T1 : finBPOrderType disp1) (T2 : finBPOrderType disp2) :=
    POrder.on (type disp3 T1 T2).
#[export] HB.instance Definition _
  (T1 : finTPOrderType disp1) (T2 : finTPOrderType disp2) :=
    POrder.on (type disp3 T1 T2).
#[export] HB.instance Definition _
  (T1 : finTBPOrderType disp1) (T2 : finTBPOrderType disp2) :=
    POrder.on (type disp3 T1 T2).

#[export] HB.instance Definition _
  (T1 : finMeetSemilatticeType disp1) (T2 : finMeetSemilatticeType disp2) :=
    POrder.on (type disp3 T1 T2).
#[export] HB.instance Definition _
  (T1 : finBMeetSemilatticeType disp1) (T2 : finBMeetSemilatticeType disp2) :=
    POrder.on (type disp3 T1 T2).

#[export] HB.instance Definition _
  (T1 : finJoinSemilatticeType disp1) (T2 : finJoinSemilatticeType disp2) :=
    POrder.on (type disp3 T1 T2).
#[export] HB.instance Definition _
  (T1 : finTJoinSemilatticeType disp1) (T2 : finTJoinSemilatticeType disp2) :=
    POrder.on (type disp3 T1 T2).

#[export] HB.instance Definition _
  (T1 : finLatticeType disp1) (T2 : finLatticeType disp2) :=
    POrder.on (type disp3 T1 T2).
#[export] HB.instance Definition _
  (T1 : finTBLatticeType disp1) (T2 : finTBLatticeType disp2) :=
    POrder.on (type disp3 T1 T2).

#[export] HB.instance Definition _
  (T1 : finDistrLatticeType disp1) (T2 : finDistrLatticeType disp2) :=
    POrder.on (type disp3 T1 T2).
#[export] HB.instance Definition _
  (T1 : finTBDistrLatticeType disp1) (T2 : finTBDistrLatticeType disp2) :=
    POrder.on (type disp3 T1 T2).

#[export] HB.instance Definition _
  (T1 : finCDistrLatticeType disp1) (T2 : finCDistrLatticeType disp2) :=
    POrder.on (type disp3 T1 T2).
#[export] HB.instance Definition _
  (T1 : finCTBDistrLatticeType disp1) (T2 : finCTBDistrLatticeType disp2) :=
    POrder.on (type disp3 T1 T2).

End FinOrder.
(* /FIXME *)

Module Exports.
HB.reexport ProdOrder.
Notation "T *prod[ d ] T'" := (type d T T')
  (at level 70, d at next level, format "T  *prod[ d ]  T'") : type_scope.
Notation "T *p T'" := (type_ T T')
  (at level 70, format "T  *p  T'") : type_scope.
Definition leEprod := @leEprod.
Definition ltEprod := @ltEprod.
Definition le_pair := @le_pair.
Definition lt_pair := @lt_pair.
Definition botEprod := @botEprod.
Definition topEprod := @topEprod.
Definition ltEprod' := @ltEprod'. (* FIXME *)
Definition lt_pair' := @lt_pair'. (* FIXME *)
Definition meetEprod := @meetEprod.
Definition joinEprod := @joinEprod.
Definition rcomplEprod := @rcomplEprod.
Definition diffEprod := @diffEprod.
Definition codiffEprod := @codiffEprod.
Definition complEprod := @complEprod.
End Exports.
End ProdOrder.
HB.export ProdOrder.Exports.

Module DefaultProdOrder.
Section DefaultProdOrder.
Context {disp1 disp2 : disp_t}.

Let prod T1 T2 := T1 *prod[prod_display disp1 disp2] T2.

(* FIXME: Scopes of arguments are broken in several places.                   *)
(* FIXME: Declaring a bunch of copies is still a bit painful.                 *)
HB.instance Definition _ (T : preorderType disp1) (T' : preorderType disp2) :=
  Preorder.copy (T * T')%type (T *p T').
HB.instance Definition _ (T1 : bPreorderType disp1) (T2 : bPreorderType disp2) :=
  BPreorder.copy (T1 * T2)%type (prod T1 T2).
HB.instance Definition _ (T1 : tPreorderType disp1) (T2 : tPreorderType disp2) :=
  TPreorder.copy (T1 * T2)%type (prod T1 T2).
HB.instance Definition _ (T1 : tbPreorderType disp1) (T2 : tbPreorderType disp2) :=
  TBPreorder.copy (T1 * T2)%type (prod T1 T2).
HB.instance Definition _ (T1 : porderType disp1) (T2 : porderType disp2) :=
  POrder.copy (T1 * T2)%type (prod T1 T2).
HB.instance Definition _ (T1 : bPOrderType disp1) (T2 : bPOrderType disp2) :=
  BPOrder.copy (T1 * T2)%type (prod T1 T2).
HB.instance Definition _ (T1 : tPOrderType disp1) (T2 : tPOrderType disp2) :=
  TPOrder.copy (T1 * T2)%type (prod T1 T2).
HB.instance Definition _ (T1 : tbPOrderType disp1) (T2 : tbPOrderType disp2) :=
  TBPOrder.copy (T1 * T2)%type (prod T1 T2).
HB.instance Definition _
  (T1 : meetSemilatticeType disp1) (T2 : meetSemilatticeType disp2) :=
  MeetSemilattice.copy (T1 * T2)%type (prod T1 T2).
HB.instance Definition _
  (T1 : bMeetSemilatticeType disp1) (T2 : bMeetSemilatticeType disp2) :=
  BMeetSemilattice.copy (T1 * T2)%type (prod T1 T2).
HB.instance Definition _
  (T1 : tMeetSemilatticeType disp1) (T2 : tMeetSemilatticeType disp2) :=
  TMeetSemilattice.copy (T1 * T2)%type (prod T1 T2).
HB.instance Definition _
  (T1 : tbMeetSemilatticeType disp1) (T2 : tbMeetSemilatticeType disp2) :=
  TBMeetSemilattice.copy (T1 * T2)%type (prod T1 T2).
HB.instance Definition _
  (T1 : joinSemilatticeType disp1) (T2 : joinSemilatticeType disp2) :=
  JoinSemilattice.copy (T1 * T2)%type (prod T1 T2).
HB.instance Definition _
  (T1 : bJoinSemilatticeType disp1) (T2 : bJoinSemilatticeType disp2) :=
  BJoinSemilattice.copy (T1 * T2)%type (prod T1 T2).
HB.instance Definition _
  (T1 : tJoinSemilatticeType disp1) (T2 : tJoinSemilatticeType disp2) :=
  TJoinSemilattice.copy (T1 * T2)%type (prod T1 T2).
HB.instance Definition _
  (T1 : tbJoinSemilatticeType disp1) (T2 : tbJoinSemilatticeType disp2) :=
  TBJoinSemilattice.copy (T1 * T2)%type (prod T1 T2).
HB.instance Definition _ (T1 : latticeType disp1) (T2 : latticeType disp2) :=
  Lattice.copy (T1 * T2)%type (prod T1 T2).
HB.instance Definition _ (T1 : bLatticeType disp1) (T2 : bLatticeType disp2) :=
  BLattice.copy (T1 * T2)%type (prod T1 T2).
HB.instance Definition _ (T1 : tLatticeType disp1) (T2 : tLatticeType disp2) :=
  TLattice.copy (T1 * T2)%type (prod T1 T2).
HB.instance Definition _
  (T1 : tbLatticeType disp1) (T2 : tbLatticeType disp2) :=
  TBLattice.copy (T1 * T2)%type (prod T1 T2).
HB.instance Definition _
  (T1 : distrLatticeType disp1) (T2 : distrLatticeType disp2) :=
  DistrLattice.copy (T1 * T2)%type (prod T1 T2).
HB.instance Definition _
  (T1 : bDistrLatticeType disp1) (T2 : bDistrLatticeType disp2) :=
  BDistrLattice.copy (T1 * T2)%type (prod T1 T2).
HB.instance Definition _
  (T1 : tDistrLatticeType disp1) (T2 : tDistrLatticeType disp2) :=
  TDistrLattice.copy (T1 * T2)%type (prod T1 T2).
HB.instance Definition _
  (T1 : tbDistrLatticeType disp1) (T2 : tbDistrLatticeType disp2) :=
  TBDistrLattice.copy (T1 * T2)%type (prod T1 T2).
HB.instance Definition _
  (T1 : cDistrLatticeType disp1) (T2 : cDistrLatticeType disp2) :=
  CDistrLattice.copy (T1 * T2)%type (prod T1 T2).
HB.instance Definition _
  (T1 : cbDistrLatticeType disp1) (T2 : cbDistrLatticeType disp2) :=
  CBDistrLattice.copy (T1 * T2)%type (prod T1 T2).
HB.instance Definition _
  (T1 : ctDistrLatticeType disp1) (T2 : ctDistrLatticeType disp2) :=
  CTDistrLattice.copy (T1 * T2)%type (prod T1 T2).
HB.instance Definition _
  (T1 : ctbDistrLatticeType disp1) (T2 : ctbDistrLatticeType disp2) :=
  CTBDistrLattice.copy (T1 * T2)%type (prod T1 T2).
HB.instance Definition _
  (T1 : finPreorderType disp1) (T2 : finPreorderType disp2) :=
  FinPreorder.copy (T1 * T2)%type (prod T1 T2).
HB.instance Definition _
  (T1 : finBPreorderType disp1) (T2 : finBPreorderType disp2) :=
  FinBPreorder.copy (T1 * T2)%type (prod T1 T2).
HB.instance Definition _
  (T1 : finTPreorderType disp1) (T2 : finTPreorderType disp2) :=
  FinTPreorder.copy (T1 * T2)%type (prod T1 T2).
HB.instance Definition _
  (T1 : finTBPreorderType disp1) (T2 : finTBPreorderType disp2) :=
  FinTBPreorder.copy (T1 * T2)%type (prod T1 T2).
HB.instance Definition _
  (T1 : finPOrderType disp1) (T2 : finPOrderType disp2) :=
  FinPOrder.copy (T1 * T2)%type (prod T1 T2).
HB.instance Definition _
  (T1 : finBPOrderType disp1) (T2 : finBPOrderType disp2) :=
  FinBPOrder.copy (T1 * T2)%type (prod T1 T2).
HB.instance Definition _
  (T1 : finTPOrderType disp1) (T2 : finTPOrderType disp2) :=
  FinTPOrder.copy (T1 * T2)%type (prod T1 T2).
HB.instance Definition _
  (T1 : finTBPOrderType disp1) (T2 : finTBPOrderType disp2) :=
  FinTBPOrder.copy (T1 * T2)%type (prod T1 T2).
HB.instance Definition _
  (T1 : finMeetSemilatticeType disp1) (T2 : finMeetSemilatticeType disp2) :=
  FinMeetSemilattice.copy (T1 * T2)%type (prod T1 T2).
HB.instance Definition _
  (T1 : finBMeetSemilatticeType disp1) (T2 : finBMeetSemilatticeType disp2) :=
  FinBMeetSemilattice.copy (T1 * T2)%type (prod T1 T2).
HB.instance Definition _
  (T1 : finJoinSemilatticeType disp1) (T2 : finJoinSemilatticeType disp2) :=
  FinJoinSemilattice.copy (T1 * T2)%type (prod T1 T2).
HB.instance Definition _
  (T1 : finTJoinSemilatticeType disp1) (T2 : finTJoinSemilatticeType disp2) :=
  FinTJoinSemilattice.copy (T1 * T2)%type (prod T1 T2).
HB.instance Definition _
  (T1 : finLatticeType disp1) (T2 : finLatticeType disp2) :=
  FinLattice.copy (T1 * T2)%type (prod T1 T2).
HB.instance Definition _
  (T1 : finTBLatticeType disp1) (T2 : finTBLatticeType disp2) :=
  FinTBLattice.copy (T1 * T2)%type (prod T1 T2).
HB.instance Definition _
  (T1 : finDistrLatticeType disp1) (T2 : finDistrLatticeType disp2) :=
  FinDistrLattice.copy (T1 * T2)%type (prod T1 T2).
HB.instance Definition _
  (T1 : finTBDistrLatticeType disp1) (T2 : finTBDistrLatticeType disp2) :=
  FinTBDistrLattice.copy (T1 * T2)%type (prod T1 T2).
HB.instance Definition _
  (T1 : finCDistrLatticeType disp1) (T2 : finCDistrLatticeType disp2) :=
  FinCDistrLattice.copy (T1 * T2)%type (prod T1 T2).
HB.instance Definition _
  (T1 : finCTBDistrLatticeType disp1) (T2 : finCTBDistrLatticeType disp2) :=
  FinCTBDistrLattice.copy (T1 * T2)%type (prod T1 T2).
(* /FIXME *)

End DefaultProdOrder.
End DefaultProdOrder.

(***************************************)
(* We declare an alias of the tuples,  *)
(* which has canonical product order.  *)
(***************************************)

Module TupleProdOrder.
Import DefaultSeqProdOrder.

Section TupleProdOrder.

Definition type (disp : disp_t) n T := n.-tuple T.
Definition type_ (disp : disp_t) n (T : preorderType disp) :=
  type (Order.seqprod_display disp) n T.

Context {disp disp' : disp_t}.
Local Notation "n .-tuple" := (type disp' n) : type_scope.

Section Basics.
Context (n : nat).
#[export] HB.instance Definition _ (T : eqType) := Equality.on (n.-tuple T).
#[export] HB.instance Definition _ (T : eqType) := SubEquality.on (n.-tuple T).
#[export] HB.instance Definition _ (T : choiceType) :=
  SubChoice.on (n.-tuple T).
#[export] HB.instance Definition _ (T : countType) :=
  SubCountable.on (n.-tuple T).
#[export] HB.instance Definition _ (T : finType) := SubFinite.on (n.-tuple T).
End Basics.

Section Preorder.
Implicit Types (n : nat) (T : preorderType disp).

(* FIXME: this instance should be dualizable, but then we should not depend   *)
(* on the subtype mechanism, because the pointwise order on seq cannot be the *)
(* dual of itself.                                                            *)
#[export] HB.instance Definition _ n T :=
  [SubChoice_isSubPreorder of n.-tuple T by <: with disp'].

Lemma leEtprod n T (t1 t2 : n.-tuple T) :
  (t1 <= t2) = [forall i, tnth t1 i <= tnth t2 i].
Proof.
elim: n => [|n IHn] in t1 t2 *.
  by rewrite tuple0 [t2]tuple0/= lexx; symmetry; apply/forallP => [].
case: (tupleP t1) (tupleP t2) => [x1 {}t1] [x2 {}t2].
rewrite [_ <= _]le_cons [t1 <= t2 :> seq _]IHn.
apply/idP/forallP => [/andP[lex12 /forallP/= let12 i]|lext12].
  by case: (unliftP ord0 i) => [j ->|->]//; rewrite !tnthS.
rewrite (lext12 ord0)/=; apply/forallP=> i.
by have := lext12 (lift ord0 i); rewrite !tnthS.
Qed.

Lemma ltEtprod n T (t1 t2 : n.-tuple T) :
  (t1 < t2) = [exists i, tnth t1 i < tnth t2 i] &&
              [forall i, tnth t1 i <= tnth t2 i].
Proof.
rewrite lt_leAnge !leEtprod negb_forall andbC.
apply/andP/andP => -[] /existsP[x] xlt le; split=> //; apply/existsP; exists x.
  rewrite lt_leAnge xlt.
  by move: le => /forallP ->.
by move: xlt; rewrite lt_leAnge => /andP[].
Qed.

End Preorder.

Section BPreorder.
Context (n : nat) (T : bPreorderType disp).
Implicit Types (t : n.-tuple T).

Fact le0x t : [tuple \bot | _ < n] <= t :> n.-tuple T.
Proof. by rewrite leEtprod; apply/forallP => i; rewrite tnth_mktuple le0x. Qed.

#[export] HB.instance Definition _ := hasBottom.Build _ (n.-tuple T) le0x.

Lemma botEtprod : \bot = [tuple \bot | _ < n] :> n.-tuple T.
Proof. by []. Qed.

End BPreorder.

Section TPreorder.
Context (n : nat) (T : tPreorderType disp).
Implicit Types (t : n.-tuple T).

Fact lex1 t : t <= [tuple \top | _ < n] :> n.-tuple T.
Proof. by rewrite leEtprod; apply/forallP => i; rewrite tnth_mktuple lex1. Qed.

#[export] HB.instance Definition _ := hasTop.Build _ (n.-tuple T) lex1.

Lemma topEtprod : \top = [tuple \top | _ < n] :> n.-tuple T.
Proof. by []. Qed.

End TPreorder.

#[export] HB.instance Definition _ n (T : porderType disp) :=
  [SubChoice_isSubPOrder of n.-tuple T by <: with disp'].

Section MeetSemilattice.
Context (n : nat) (T : meetSemilatticeType disp).
Implicit Types (t : n.-tuple T).

Definition meet t1 t2 : n.-tuple T := [tuple tnth t1 i `&` tnth t2 i | i < n].

Fact lexI t1 t2 t3 : (t1 <= meet t2 t3) = (t1 <= t2) && (t1 <= t3).
Proof.
rewrite !leEtprod; apply/forallP/andP => [H|[Ht12 Ht13] i]; last first.
  by rewrite tnth_mktuple lexI (forallP Ht12) (forallP Ht13).
by split; apply/forallP => i; move: (H i); rewrite tnth_mktuple lexI => /andP[].
Qed.

#[export] HB.instance Definition _ :=
  @POrder_isMeetSemilattice.Build _ (n.-tuple T) meet lexI.

Lemma tnth_meet t1 t2 i : tnth (t1 `&` t2) i = tnth t1 i `&` tnth t2 i.
Proof. exact: tnth_mktuple. Qed.

Lemma meetEtprod t1 t2 : t1 `&` t2 = [tuple tnth t1 i `&` tnth t2 i | i < n].
Proof. by []. Qed.

End MeetSemilattice.

Section JoinSemilattice.
Context (n : nat) (T : joinSemilatticeType disp).
Implicit Types (t : n.-tuple T).

Definition join t1 t2 : n.-tuple T := [tuple tnth t1 i `|` tnth t2 i | i < n].

Fact leUx t1 t2 t3 : (join t1 t2 <= t3) = (t1 <= t3) && (t2 <= t3).
Proof.
rewrite !leEtprod; apply/forallP/andP => [H|[Ht13 Ht23] i]; last first.
  by rewrite tnth_mktuple leUx (forallP Ht13) (forallP Ht23).
by split; apply/forallP => i; move: (H i); rewrite tnth_mktuple leUx => /andP[].
Qed.

#[export] HB.instance Definition _ :=
  @POrder_isJoinSemilattice.Build _ (n.-tuple T) join leUx.

Lemma tnth_join t1 t2 i : tnth (t1 `|` t2) i = tnth t1 i `|` tnth t2 i.
Proof. exact: tnth_mktuple. Qed.

Lemma joinEtprod t1 t2 : t1 `|` t2 = [tuple tnth t1 i `|` tnth t2 i | i < n].
Proof. by []. Qed.

End JoinSemilattice.

(* FIXME: use HB.saturate *)
#[export] HB.instance Definition _ (n : nat) (T : tbPreorderType disp) :=
  Preorder.on (n.-tuple T).
#[export] HB.instance Definition _ (n : nat) (T : bPOrderType disp) :=
  POrder.on (n.-tuple T).
#[export] HB.instance Definition _ (n : nat) (T : tPOrderType disp) :=
  POrder.on (n.-tuple T).
#[export] HB.instance Definition _ (n : nat) (T : tbPOrderType disp) :=
  POrder.on (n.-tuple T).
#[export] HB.instance Definition _ (n : nat) (T : bMeetSemilatticeType disp) :=
  POrder.on (n.-tuple T).
#[export] HB.instance Definition _ (n : nat) (T : tMeetSemilatticeType disp) :=
  POrder.on (n.-tuple T).
#[export] HB.instance Definition _ (n : nat) (T : tbMeetSemilatticeType disp) :=
  POrder.on (n.-tuple T).
#[export] HB.instance Definition _ (n : nat) (T : bJoinSemilatticeType disp) :=
  POrder.on (n.-tuple T).
#[export] HB.instance Definition _ (n : nat) (T : tJoinSemilatticeType disp) :=
  POrder.on (n.-tuple T).
#[export] HB.instance Definition _ (n : nat) (T : tbJoinSemilatticeType disp) :=
  POrder.on (n.-tuple T).
#[export] HB.instance Definition _ (n : nat) (T : latticeType disp) :=
  POrder.on (n.-tuple T).
#[export] HB.instance Definition _ (n : nat) (T : bLatticeType disp) :=
  POrder.on (n.-tuple T).
#[export] HB.instance Definition _ (n : nat) (T : tLatticeType disp) :=
  POrder.on (n.-tuple T).
#[export] HB.instance Definition _ (n : nat) (T : tbLatticeType disp) :=
  POrder.on (n.-tuple T).
(* /FIXME *)

Section DistrLattice.
Context (n : nat) (T : distrLatticeType disp).
Implicit Types (t : n.-tuple T).

Fact meetUl : left_distributive (@meet n T) (@join n T).
Proof.
by move=> t1 t2 t3; apply: eq_from_tnth => i; rewrite !tnth_mktuple meetUl.
Qed.

#[export] HB.instance Definition _ :=
  Lattice_Meet_isDistrLattice.Build _ (n.-tuple T) meetUl.

End DistrLattice.

(* FIXME: use HB.saturate *)
#[export] HB.instance Definition _ (n : nat) (T : bDistrLatticeType disp) :=
  DistrLattice.on (n.-tuple T).
#[export] HB.instance Definition _ (n : nat) (T : tDistrLatticeType disp) :=
  DistrLattice.on (n.-tuple T).
#[export] HB.instance Definition _ (n : nat) (T : tbDistrLatticeType disp) :=
  DistrLattice.on (n.-tuple T).
(* /FIXME *)

Section CDistrLattice.
Context (n : nat) (T : cDistrLatticeType disp).
Implicit Types (t : n.-tuple T).

Definition rcompl t1 t2 t3 :=
  [tuple rcompl (tnth t1 i) (tnth t2 i) (tnth t3 i) | i < n].

Fact rcomplPmeet x y z : ((x `&` y) `|` z) `&` rcompl x y z = x `&` y.
Proof. by apply: eq_from_tnth => i; rewrite !tnth_mktuple rcomplPmeet. Qed.

Fact rcomplPjoin x y z : ((y `|` x) `&` z) `|` rcompl x y z = y `|` x.
Proof. by apply: eq_from_tnth => i; rewrite !tnth_mktuple rcomplPjoin. Qed.

#[export] HB.instance Definition _ :=
  @DistrLattice_hasRelativeComplement.Build _ (n.-tuple T)
    rcompl rcomplPmeet rcomplPjoin.

Lemma tnth_rcompl t1 t2 t3 i :
  tnth (Order.rcompl t1 t2 t3) i =
    Order.rcompl (tnth t1 i) (tnth t2 i) (tnth t3 i).
Proof. exact: tnth_mktuple. Qed.

Lemma rcomplEtprod t1 t2 t3 :
  Order.rcompl t1 t2 t3 =
    [tuple Order.rcompl (tnth t1 i) (tnth t2 i) (tnth t3 i) | i < n].
Proof. by []. Qed.

End CDistrLattice.

Section CBDistrLattice.
Context (n : nat) (T : cbDistrLatticeType disp).
Implicit Types (t : n.-tuple T).

Definition diff t1 t2 : n.-tuple T := [tuple tnth t1 i `\` tnth t2 i | i < n].

Fact diffErcompl t1 t2 : diff t1 t2 = rcompl \bot t1 t2.
Proof. by apply: eq_from_tnth => i; rewrite !tnth_mktuple diffErcompl. Qed.

#[export] HB.instance Definition _ :=
  @CDistrLattice_hasSectionalComplement.Build _ (n.-tuple T) diff diffErcompl.

Lemma tnth_diff t1 t2 i : tnth (diff t1 t2) i = tnth t1 i `\` tnth t2 i.
Proof. exact: tnth_mktuple. Qed.

Lemma diffEtprod t1 t2 : t1 `\` t2 = [tuple tnth t1 i `\` tnth t2 i | i < n].
Proof. by []. Qed.

End CBDistrLattice.

Section CTDistrLattice.
Context (n : nat) (T : ctDistrLatticeType disp).
Implicit Types (t : n.-tuple T).

Definition codiff t1 t2 : n.-tuple T :=
  [tuple Order.codiff (tnth t1 i) (tnth t2 i) | i < n].

Fact codiffErcompl t1 t2 : codiff t1 t2 = rcompl t1 \top t2.
Proof. by apply: eq_from_tnth => i; rewrite !tnth_mktuple codiffErcompl. Qed.

#[export] HB.instance Definition _ :=
  @CDistrLattice_hasDualSectionalComplement.Build _ (n.-tuple T)
    codiff codiffErcompl.

Lemma tnth_codiff t1 t2 i :
  tnth (Order.codiff t1 t2) i = Order.codiff (tnth t1 i) (tnth t2 i).
Proof. exact: tnth_mktuple. Qed.

Lemma codiffEtprod t1 t2 :
  Order.codiff t1 t2 = [tuple Order.codiff (tnth t1 i) (tnth t2 i) | i < n].
Proof. by []. Qed.

End CTDistrLattice.

Section CTBDistrLattice.
Context (n : nat) (T : ctbDistrLatticeType disp).
Implicit Types (t : n.-tuple T).

Definition compl t : n.-tuple T := map_tuple compl t.

Fact complEdiff t : compl t = (\top : n.-tuple T) `\` t.
Proof.
by apply: eq_from_tnth => i; rewrite tnth_map !tnth_mktuple complEdiff.
Qed.

Fact complEcodiff t : compl t = codiff (\bot : n.-tuple T) t.
Proof.
by apply: eq_from_tnth => i; rewrite tnth_map !tnth_mktuple complEcodiff.
Qed.

#[export] HB.instance Definition _ :=
  @CDistrLattice_hasComplement.Build _ (n.-tuple T)
    compl complEdiff complEcodiff.

Lemma tnth_compl t i : tnth (~` t) i = ~` tnth t i.
Proof. by rewrite tnth_map. Qed.

Lemma complEtprod t : ~` t = map_tuple Order.compl t.
Proof. by []. Qed.

End CTBDistrLattice.

(* FIXME: use HB.saturate *)
#[export] HB.instance Definition _ (n : nat) (T : finPreorderType disp) :=
  Preorder.on (n.-tuple T).
#[export] HB.instance Definition _ (n : nat) (T : finBPreorderType disp) :=
  Preorder.on (n.-tuple T).
#[export] HB.instance Definition _ (n : nat) (T : finTPreorderType disp) :=
  Preorder.on (n.-tuple T).
#[export] HB.instance Definition _ (n : nat) (T : finTBPreorderType disp) :=
  Preorder.on (n.-tuple T).
#[export] HB.instance Definition _ (n : nat) (T : finPOrderType disp) :=
  POrder.on (n.-tuple T).
#[export] HB.instance Definition _ (n : nat) (T : finBPOrderType disp) :=
  POrder.on (n.-tuple T).
#[export] HB.instance Definition _ (n : nat) (T : finTPOrderType disp) :=
  POrder.on (n.-tuple T).
#[export] HB.instance Definition _ (n : nat) (T : finTBPOrderType disp) :=
  POrder.on (n.-tuple T).
#[export] HB.instance Definition _
  (n : nat) (T : finMeetSemilatticeType disp) := POrder.on (n.-tuple T).
#[export] HB.instance Definition _
  (n : nat) (T : finBMeetSemilatticeType disp) := POrder.on (n.-tuple T).
#[export] HB.instance Definition _
  (n : nat) (T : finJoinSemilatticeType disp) := POrder.on (n.-tuple T).
#[export] HB.instance Definition _
  (n : nat) (T : finTJoinSemilatticeType disp) := POrder.on (n.-tuple T).
#[export] HB.instance Definition _
  (n : nat) (T : finLatticeType disp) := POrder.on (n.-tuple T).
#[export] HB.instance Definition _
  (n : nat) (T : finTBLatticeType disp) := POrder.on (n.-tuple T).
#[export] HB.instance Definition _
  (n : nat) (T : finDistrLatticeType disp) := POrder.on (n.-tuple T).
#[export] HB.instance Definition _
  (n : nat) (T : finTBDistrLatticeType disp) := POrder.on (n.-tuple T).
#[export] HB.instance Definition _
  (n : nat) (T : finCDistrLatticeType disp) := POrder.on (n.-tuple T).
#[export] HB.instance Definition _
  (n : nat) (T : finCTBDistrLatticeType disp) := POrder.on (n.-tuple T).
(* /FIXME *)

End TupleProdOrder.

Module Exports.

HB.reexport TupleProdOrder.

Notation "n .-tupleprod[ disp ]" := (type disp n)
  (format "n .-tupleprod[ disp ]") : type_scope.
Notation "n .-tupleprod" := (type_ n)
  (format "n .-tupleprod") : type_scope.

Definition leEtprod := @leEtprod.
Definition ltEtprod := @ltEtprod.
Definition botEtprod := @botEtprod.
Definition topEtprod := @topEtprod.

Definition tnth_meet := @tnth_meet.
Definition meetEtprod := @meetEtprod.
Definition tnth_join := @tnth_join.
Definition joinEtprod := @joinEtprod.
Definition tnth_rcompl := @tnth_rcompl.
Definition rcomplEtprod := @rcomplEtprod.
Definition tnth_diff := @tnth_diff.
Definition diffEtprod := @diffEtprod.
Definition tnth_codiff := @tnth_codiff.
Definition codiffEtprod := @codiffEtprod.
Definition tnth_compl := @tnth_compl.
Definition complEtprod := @complEtprod.

End Exports.
End TupleProdOrder.
HB.export TupleProdOrder.Exports.

Module DefaultTupleProdOrder.
Section DefaultTupleProdOrder.
Context {disp : disp_t}.

Notation "n .-tupleprod" := n.-tupleprod[Order.seqprod_display disp].

HB.instance Definition _ n (T : preorderType disp) :=
  Preorder.copy (n.-tuple T) (n.-tupleprod T).
HB.instance Definition _ n (T : bPreorderType disp) :=
  BPreorder.copy (n.-tuple T) (n.-tupleprod T).
HB.instance Definition _ n (T : tPreorderType disp) :=
  TPreorder.copy (n.-tuple T) (n.-tupleprod T).
HB.instance Definition _ n (T : tbPreorderType disp) :=
  TBPreorder.copy (n.-tuple T) (n.-tupleprod T).
HB.instance Definition _ n (T : porderType disp) :=
  POrder.copy (n.-tuple T) (n.-tupleprod T).
HB.instance Definition _ n (T : bPOrderType disp) :=
  BPOrder.copy (n.-tuple T) (n.-tupleprod T).
HB.instance Definition _ n (T : tPOrderType disp) :=
  TPOrder.copy (n.-tuple T) (n.-tupleprod T).
HB.instance Definition _ n (T : tbPOrderType disp) :=
  TBPOrder.copy (n.-tuple T) (n.-tupleprod T).
HB.instance Definition _ n (T : meetSemilatticeType disp) :=
  MeetSemilattice.copy (n.-tuple T) (n.-tupleprod T).
HB.instance Definition _ n (T : bMeetSemilatticeType disp) :=
  BMeetSemilattice.copy (n.-tuple T) (n.-tupleprod T).
HB.instance Definition _ n (T : tMeetSemilatticeType disp) :=
  TMeetSemilattice.copy (n.-tuple T) (n.-tupleprod T).
HB.instance Definition _ n (T : tbMeetSemilatticeType disp) :=
  TBMeetSemilattice.copy (n.-tuple T) (n.-tupleprod T).
HB.instance Definition _ n (T : joinSemilatticeType disp) :=
  JoinSemilattice.copy (n.-tuple T) (n.-tupleprod T).
HB.instance Definition _ n (T : bJoinSemilatticeType disp) :=
  BJoinSemilattice.copy (n.-tuple T) (n.-tupleprod T).
HB.instance Definition _ n (T : tJoinSemilatticeType disp) :=
  TJoinSemilattice.copy (n.-tuple T) (n.-tupleprod T).
HB.instance Definition _ n (T : tbJoinSemilatticeType disp) :=
  TBJoinSemilattice.copy (n.-tuple T) (n.-tupleprod T).
HB.instance Definition _ n (T : latticeType disp) :=
  Lattice.copy (n.-tuple T) (n.-tupleprod T).
HB.instance Definition _ n (T : bLatticeType disp) :=
  BLattice.copy (n.-tuple T) (n.-tupleprod T).
HB.instance Definition _ n (T : tLatticeType disp) :=
  TLattice.copy (n.-tuple T) (n.-tupleprod T).
HB.instance Definition _ n (T : tbLatticeType disp) :=
  TBLattice.copy (n.-tuple T) (n.-tupleprod T).
HB.instance Definition _ n (T : distrLatticeType disp) :=
  DistrLattice.copy (n.-tuple T) (n.-tupleprod T).
HB.instance Definition _ n (T : bDistrLatticeType disp) :=
  BDistrLattice.copy (n.-tuple T) (n.-tupleprod T).
HB.instance Definition _ n (T : tDistrLatticeType disp) :=
  TDistrLattice.copy (n.-tuple T) (n.-tupleprod T).
HB.instance Definition _ n (T : tbDistrLatticeType disp) :=
  TBDistrLattice.copy (n.-tuple T) (n.-tupleprod T).
HB.instance Definition _ n (T : cDistrLatticeType disp) :=
  CDistrLattice.copy (n.-tuple T) (n.-tupleprod T).
HB.instance Definition _ n (T : cbDistrLatticeType disp) :=
  CBDistrLattice.copy (n.-tuple T) (n.-tupleprod T).
HB.instance Definition _ n (T : ctDistrLatticeType disp) :=
  CTDistrLattice.copy (n.-tuple T) (n.-tupleprod T).
HB.instance Definition _ n (T : ctbDistrLatticeType disp) :=
  CTBDistrLattice.copy (n.-tuple T) (n.-tupleprod T).
HB.instance Definition _ n (T : finPreorderType disp) :=
  FinPreorder.copy (n.-tuple T) (n.-tupleprod T).
HB.instance Definition _ n (T : finBPreorderType disp) :=
  FinBPreorder.copy (n.-tuple T) (n.-tupleprod T).
HB.instance Definition _ n (T : finTPreorderType disp) :=
  FinTPreorder.copy (n.-tuple T) (n.-tupleprod T).
HB.instance Definition _ n (T : finTBPreorderType disp) :=
  FinTBPreorder.copy (n.-tuple T) (n.-tupleprod T).
HB.instance Definition _ n (T : finPOrderType disp) :=
  FinPOrder.copy (n.-tuple T) (n.-tupleprod T).
HB.instance Definition _ n (T : finBPOrderType disp) :=
  FinBPOrder.copy (n.-tuple T) (n.-tupleprod T).
HB.instance Definition _ n (T : finTPOrderType disp) :=
  FinTPOrder.copy (n.-tuple T) (n.-tupleprod T).
HB.instance Definition _ n (T : finTBPOrderType disp) :=
  FinTBPOrder.copy (n.-tuple T) (n.-tupleprod T).
HB.instance Definition _ n (T : finMeetSemilatticeType disp) :=
  FinMeetSemilattice.copy (n.-tuple T) (n.-tupleprod T).
HB.instance Definition _ n (T : finBMeetSemilatticeType disp) :=
  FinBMeetSemilattice.copy (n.-tuple T) (n.-tupleprod T).
HB.instance Definition _ n (T : finJoinSemilatticeType disp) :=
  FinJoinSemilattice.copy (n.-tuple T) (n.-tupleprod T).
HB.instance Definition _ n (T : finTJoinSemilatticeType disp) :=
  FinTJoinSemilattice.copy (n.-tuple T) (n.-tupleprod T).
HB.instance Definition _ n (T : finLatticeType disp) :=
  FinLattice.copy (n.-tuple T) (n.-tupleprod T).
HB.instance Definition _ n (T : finTBLatticeType disp) :=
  FinTBLattice.copy (n.-tuple T) (n.-tupleprod T).
HB.instance Definition _ n (T : finDistrLatticeType disp) :=
  FinDistrLattice.copy (n.-tuple T) (n.-tupleprod T).
HB.instance Definition _ n (T : finTBDistrLatticeType disp) :=
  FinTBDistrLattice.copy (n.-tuple T) (n.-tupleprod T).
HB.instance Definition _ n (T : finCDistrLatticeType disp) :=
  FinCDistrLattice.copy (n.-tuple T) (n.-tupleprod T).
HB.instance Definition _ n (T : finCTBDistrLatticeType disp) :=
  FinCTBDistrLattice.copy (n.-tuple T) (n.-tupleprod T).

End DefaultTupleProdOrder.
End DefaultTupleProdOrder.

(*********************************************)
(* We declare an alias of the sets,          *)
(* which is canonically ordered by inclusion *)
(*********************************************)
Module SetSubsetOrder.
Section SetSubsetOrder.

Fact subset_display : disp_t. Proof. exact. Qed.

Definition type (disp : disp_t) (T : finType) := {set T}.

Context {disp : disp_t} {T : finType}.
Local Notation "{ 'subset' T }" := (type disp T).
Implicit Type (A B C : {subset T}).

#[export] HB.instance Definition _ := Choice.on {subset T}.

Fact le_anti : antisymmetric (fun A B => A \subset B).
Proof. by move=> A B ABA; apply/eqP; rewrite eqEsubset. Qed.

#[export] HB.instance Definition _ := Le_isPOrder.Build disp {subset T}
    (@subxx _ _) le_anti (fun A B => @subset_trans _ B A).

Lemma leEsubset A B : (A <= B) = (A \subset B).
Proof. by []. Qed.

#[export] HB.instance Definition _ :=
  hasBottom.Build disp {subset T} (@sub0set _).

#[export] HB.instance Definition _ :=
  hasTop.Build disp {subset T} (@subsetT _).

#[export] HB.instance Definition _ :=
  @POrder_MeetJoin_isLattice.Build disp {subset T}
    (@setI _) (@setU _) (@subsetI _) (fun x y z => @subUset _ z x y).

#[export] HB.instance Definition _ :=
  Lattice_Meet_isDistrLattice.Build disp {subset T} (@setIUl _).

Lemma setIDv A B : B :&: (A :\: B) = set0.
Proof.
apply/eqP; rewrite -subset0; apply/subsetP => x.
by rewrite !inE => /and3P[->].
Qed.

#[export]
HB.instance Definition _ :=
  @BDistrLattice_hasSectionalComplement.Build disp {subset T}
    (@setD _) setIDv (@setID _).

Lemma setTDsym A : ~: A = setT :\: A.
Proof. by rewrite setTD. Qed.

#[export]
HB.instance Definition _ :=
  CBDistrLattice_hasComplement.Build disp {subset T} setTDsym.

Lemma meetEsubset A B : A `&` B = A :&: B.
Proof. by []. Qed.
Lemma joinEsubset A B : A `|` B = A :|: B.
Proof. by []. Qed.
Lemma botEsubset : \bot = set0 :> {subset T}.
Proof. by []. Qed.
Lemma topEsubset : \top = setT :> {subset T}.
Proof. by []. Qed.
Lemma subEsubset A B : A `\` B = A :\: B.
Proof. by []. Qed.
Lemma complEsubset A : ~` A = ~: A.
Proof. by []. Qed.

End SetSubsetOrder.

Module Exports.
Arguments type disp T%_type.
Notation "{ 'subset' [ d ] T }" := (type d T)
  (format "{ 'subset' [ d ]  T }") : type_scope.
Notation "{ 'subset' T }" := {subset[subset_display] T}
  (format "{ 'subset' T }") : type_scope.

HB.reexport.

Definition leEsubset := @leEsubset.
Definition meetEsubset := @meetEsubset.
Definition joinEsubset := @joinEsubset.
Definition botEsubset := @botEsubset.
Definition topEsubset := @topEsubset.
Definition subEsubset := @subEsubset.
Definition complEsubset := @complEsubset.

End Exports.
End SetSubsetOrder.
Export SetSubsetOrder.Exports.

Module DefaultSetSubsetOrder.

HB.instance Definition _ (T : finType) :=
  CTBDistrLattice.copy {set T} {subset T}.

End DefaultSetSubsetOrder.

Module Exports.
HB.reexport.
End Exports.

End Order.

Export Order.Exports.

Module DefaultProdOrder := Order.DefaultProdOrder.
Module DefaultTupleProdOrder := Order.DefaultTupleProdOrder.

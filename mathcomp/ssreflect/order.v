(* (c) Copyright 2006-2019 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrbool eqtype ssrfun ssrnat choice seq.
From mathcomp Require Import fintype tuple bigop path finset.

(******************************************************************************)
(* This files defines a ordered and decidable relations on a type as          *)
(* canonical structure.  One need to import some of the following modules to  *)
(* get the definitions, notations, and theory of such relations.              *)
(*       Order.Def: definitions of basic operations.                          *)
(*    Order.Syntax: fancy notations for ordering declared in the order_scope  *)
(*                  (%O).                                                     *)
(*   Order.LTheory: theory of partially ordered types and lattices excluding  *)
(*                  complement and totality related theorems.                 *)
(*   Order.CTheory: theory of complemented lattices including Order.LTheory.  *)
(*   Order.TTheory: theory of totally ordered types including Order.LTheory.  *)
(*    Order.Theory: theory of ordered types including all of the above        *)
(*                  theory modules.                                           *)
(*                                                                            *)
(* We provide the following structures of ordered types                       *)
(*        porderType == the type of partially ordered types                   *)
(*         orderType == the type of totally ordered types                     *)
(*       latticeType == the type of distributive lattices                     *)
(*      blatticeType == ... with a bottom elemnt                              *)
(*     tblatticeType == ... with both a top and a bottom                      *)
(*     cblatticeType == the type of sectionally complemented lattices         *)
(*                      (lattices with a complement to, and bottom)           *)
(*    ctblatticeType == the type of complemented lattices                     *)
(*                      (lattices with a top, bottom, and general complement) *)
(*    finPOerderType == the type of partially ordered finite types            *)
(*    finLatticeType == the type of nonempty finite lattices                  *)
(*   finClatticeType == the type of nonempty finite complemented lattices     *)
(*      finOrderType == the type of nonempty totally ordered finite types     *)
(*                                                                            *)
(* Each of these structure take a first argument named display, of type unit  *)
(* instanciating it with tt or an unknown key will lead to a default display. *)
(* Optionally, one can configure the display by setting one owns notation on  *)
(* operators instanciated for their particular display.                       *)
(* One example of this is the converse display ^c, every notation with the    *)
(* suffix ^c (e.g. x <=^c y) is about the converse order, in order not to     *)
(* confuse the normal order with its converse.                                *)
(*                                                                            *)
(* PorderType pord_mixin == builds a porderType from a partial order mixin    *)
(*                          containing le, lt and refl, antisym, trans of le  *)
(* LatticeType lat_mixin == builds a distributive lattice from a porderType   *)
(*                          meet and join and axioms                          *)
(*    OrderType le_total == builds an order type from a latticeType and from  *)
(*                          a proof of totality                               *)
(*                  ...                                                       *)
(*                                                                            *)
(* Over these structures, we have the following operations                    *)
(*            x <= y <-> x is less than or equal to y.                        *)
(*             x < y <-> x is less than y (:= (y != x) && (x <= y)).          *)
(*            x >= y <-> x is greater than or equal to y (:= y <= x).         *)
(*             x > y <-> x is greater than y (:= y < x).                      *)
(*   x <= y ?= iff C <-> x is less than y, or equal iff C is true.            *)
(*           x >=< y <-> x and y are comparable (:= (x <= y) || (y <= x)).    *)
(*            x >< y <-> x and y are incomparable.                            *)
(* For lattices we provide the following operations                           *)
(*           x `&` y == the meet of x and y.                                  *)
(*           x `|` y == the join of x and y.                                  *)
(*                 0 == the bottom element.                                   *)
(*                 1 == the top element.                                      *)
(*           x `\` y == the (sectional) complement of y in [0, x].            *)
(*              ~` x == the complement of x in [0, 1].                        *)
(*   \meet_<range> e == iterated meet of a lattice with a top.                *)
(*   \join_<range> e == iterated join of a lattice with a bottom.             *)
(* For orderType we provide the following operations                          *)
(*   [arg minr_(i < i0 | P) M] == a value i : T minimizing M : R, subject to  *)
(*                      the condition P (i may appear in P and M), and        *)
(*                      provided P holds for i0.                              *)
(*   [arg maxr_(i > i0 | P) M] == a value i maximizing M subject to P and     *)
(*                      provided P holds for i0.                              *)
(*   [arg min_(i < i0 in A) M] == an i \in A minimizing M if i0 \in A.        *)
(*   [arg max_(i > i0 in A) M] == an i \in A maximizing M if i0 \in A.        *)
(*   [arg min_(i < i0) M] == an i : T minimizing M, given i0 : T.             *)
(*   [arg max_(i > i0) M] == an i : T maximizing M, given i0 : T.             *)
(*                                                                            *)
(* There are three distinct uses of the symbols                               *)
(* <, <=, >, >=, _ <= _ ?= iff _, >=<, and ><:                                *)
(*    0-ary, unary (prefix), and binary (infix).                              *)
(* 0. <%O, <=%O, >%O, >=%O, <?=%O, >=<%O, and ><%O stand respectively for     *)
(*    lt, le, gt, ge, leif (_ <= _ ?= iff _), comparable, and incomparable.   *)
(* 1. (< x),  (<= x), (> x), (>= x), (>=< x), and (>< x) stand respectively   *)
(*    for (>%O x), (>=%O x), (<%O x), (<=%O x), (>=<%O x), and (><%O x).      *)
(*    So (< x) is a predicate characterizing elements smaller than x.         *)
(* 2. (x < y), (x <= y), ... mean what they are expected to.                  *)
(*  These convention are compatible with Haskell's,                           *)
(*   where ((< y) x) = (x < y) = ((<) x y),                                   *)
(*   except that we write <%O instead of (<).                                 *)
(*                                                                            *)
(* We provide the following canonical instances of ordered types              *)
(* - porderType, latticeType, orderType, blatticeType of nat                  *)
(* - porderType of seq (lexicographic ordering)                               *)
(*                                                                            *)
(* leP ltP ltgtP are the three main lemmas for case analysis.                 *)
(*                                                                            *)
(* We also provide specialized version of some theorems from path.v.          *)
(*                                                                            *)
(* This file is based on prior works by                                       *)
(* D. Dreyer, G. Gonthier, A. Nanevski, P-Y Strub, B. Ziliani                 *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope order_scope with O.
Local Open Scope order_scope.

Reserved Notation "<= y" (at level 35).
Reserved Notation ">= y" (at level 35).
Reserved Notation "< y" (at level 35).
Reserved Notation "> y" (at level 35).
Reserved Notation "<= y :> T" (at level 35, y at next level).
Reserved Notation ">= y :> T" (at level 35, y at next level).
Reserved Notation "< y :> T" (at level 35, y at next level).
Reserved Notation "> y :> T" (at level 35, y at next level).
Reserved Notation "x >=< y" (at level 70, no associativity).
Reserved Notation ">=< x" (at level 35).
Reserved Notation ">=< y :> T" (at level 35, y at next level).
Reserved Notation "x >< y" (at level 70, no associativity).
Reserved Notation ">< x" (at level 35).
Reserved Notation ">< y :> T" (at level 35, y at next level).

Reserved Notation "x <=^c y" (at level 70, y at next level).
Reserved Notation "x >=^c y" (at level 70, y at next level, only parsing).
Reserved Notation "x <^c y" (at level 70, y at next level).
Reserved Notation "x >^c y" (at level 70, y at next level, only parsing).
Reserved Notation "x <=^c y :> T" (at level 70, y at next level).
Reserved Notation "x >=^c y :> T" (at level 70, y at next level, only parsing).
Reserved Notation "x <^c y :> T" (at level 70, y at next level).
Reserved Notation "x >^c y :> T" (at level 70, y at next level, only parsing).
Reserved Notation "<=^c y" (at level 35).
Reserved Notation ">=^c y" (at level 35).
Reserved Notation "<^c y" (at level 35).
Reserved Notation ">^c y" (at level 35).
Reserved Notation "<=^c y :> T" (at level 35, y at next level).
Reserved Notation ">=^c y :> T" (at level 35, y at next level).
Reserved Notation "<^c y :> T" (at level 35, y at next level).
Reserved Notation ">^c y :> T" (at level 35, y at next level).
Reserved Notation "x >=<^c y" (at level 70, no associativity).
Reserved Notation ">=<^c x" (at level 35).
Reserved Notation ">=<^c y :> T" (at level 35, y at next level).
Reserved Notation "x ><^c y" (at level 70, no associativity).
Reserved Notation "><^c x" (at level 35).
Reserved Notation "><^c y :> T" (at level 35, y at next level).

Reserved Notation "x <=^c y <=^c z" (at level 70, y, z at next level).
Reserved Notation "x <^c y <=^c z" (at level 70, y, z at next level).
Reserved Notation "x <=^c y <^c z" (at level 70, y, z at next level).
Reserved Notation "x <^c y <^c z" (at level 70, y, z at next level).
Reserved Notation "x <=^c y ?= 'iff' c" (at level 70, y, c at next level,
  format "x '[hv'  <=^c  y '/'  ?=  'iff'  c ']'").
Reserved Notation "x <=^c y ?= 'iff' c :> T" (at level 70, y, c at next level,
  format "x '[hv'  <=^c  y '/'  ?=  'iff'  c  :> T ']'").

(* Reserved notation for lattice operations. *)
Reserved Notation "A `&` B"  (at level 48, left associativity).
Reserved Notation "A `|` B" (at level 52, left associativity).
Reserved Notation "A `\` B" (at level 50, left associativity).
Reserved Notation "~` A" (at level 35, right associativity).

(* Reserved notation for converse lattice operations. *)
Reserved Notation "A `&^c` B"  (at level 48, left associativity).
Reserved Notation "A `|^c` B" (at level 52, left associativity).
Reserved Notation "A `\^c` B" (at level 50, left associativity).
Reserved Notation "~^c` A" (at level 35, right associativity).

Reserved Notation "\meet_ i F"
  (at level 41, F at level 41, i at level 0,
           format "'[' \meet_ i '/  '  F ']'").
Reserved Notation "\meet_ ( i <- r | P ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \meet_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\meet_ ( i <- r ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \meet_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\meet_ ( m <= i < n | P ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \meet_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\meet_ ( m <= i < n ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \meet_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\meet_ ( i | P ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \meet_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\meet_ ( i : t | P ) F"
  (at level 41, F at level 41, i at level 50,
           only parsing).
Reserved Notation "\meet_ ( i : t ) F"
  (at level 41, F at level 41, i at level 50,
           only parsing).
Reserved Notation "\meet_ ( i < n | P ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \meet_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\meet_ ( i < n ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \meet_ ( i  <  n )  F ']'").
Reserved Notation "\meet_ ( i 'in' A | P ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \meet_ ( i  'in'  A  |  P ) '/  '  F ']'").
Reserved Notation "\meet_ ( i 'in' A ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \meet_ ( i  'in'  A ) '/  '  F ']'").

Reserved Notation "\join_ i F"
  (at level 41, F at level 41, i at level 0,
           format "'[' \join_ i '/  '  F ']'").
Reserved Notation "\join_ ( i <- r | P ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \join_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\join_ ( i <- r ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \join_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\join_ ( m <= i < n | P ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \join_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\join_ ( m <= i < n ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \join_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\join_ ( i | P ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \join_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\join_ ( i : t | P ) F"
  (at level 41, F at level 41, i at level 50,
           only parsing).
Reserved Notation "\join_ ( i : t ) F"
  (at level 41, F at level 41, i at level 50,
           only parsing).
Reserved Notation "\join_ ( i < n | P ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \join_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\join_ ( i < n ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \join_ ( i  <  n )  F ']'").
Reserved Notation "\join_ ( i 'in' A | P ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \join_ ( i  'in'  A  |  P ) '/  '  F ']'").
Reserved Notation "\join_ ( i 'in' A ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \join_ ( i  'in'  A ) '/  '  F ']'").

Reserved Notation "\meet^c_ i F"
  (at level 41, F at level 41, i at level 0,
           format "'[' \meet^c_ i '/  '  F ']'").
Reserved Notation "\meet^c_ ( i <- r | P ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \meet^c_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\meet^c_ ( i <- r ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \meet^c_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\meet^c_ ( m <= i < n | P ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \meet^c_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\meet^c_ ( m <= i < n ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \meet^c_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\meet^c_ ( i | P ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \meet^c_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\meet^c_ ( i : t | P ) F"
  (at level 41, F at level 41, i at level 50,
           only parsing).
Reserved Notation "\meet^c_ ( i : t ) F"
  (at level 41, F at level 41, i at level 50,
           only parsing).
Reserved Notation "\meet^c_ ( i < n | P ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \meet^c_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\meet^c_ ( i < n ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \meet^c_ ( i  <  n )  F ']'").
Reserved Notation "\meet^c_ ( i 'in' A | P ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \meet^c_ ( i  'in'  A  |  P ) '/  '  F ']'").
Reserved Notation "\meet^c_ ( i 'in' A ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \meet^c_ ( i  'in'  A ) '/  '  F ']'").

Reserved Notation "\join^c_ i F"
  (at level 41, F at level 41, i at level 0,
           format "'[' \join^c_ i '/  '  F ']'").
Reserved Notation "\join^c_ ( i <- r | P ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \join^c_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\join^c_ ( i <- r ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \join^c_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\join^c_ ( m <= i < n | P ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \join^c_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\join^c_ ( m <= i < n ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \join^c_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\join^c_ ( i | P ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \join^c_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\join^c_ ( i : t | P ) F"
  (at level 41, F at level 41, i at level 50,
           only parsing).
Reserved Notation "\join^c_ ( i : t ) F"
  (at level 41, F at level 41, i at level 50,
           only parsing).
Reserved Notation "\join^c_ ( i < n | P ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \join^c_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\join^c_ ( i < n ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \join^c_ ( i  <  n )  F ']'").
Reserved Notation "\join^c_ ( i 'in' A | P ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \join^c_ ( i  'in'  A  |  P ) '/  '  F ']'").
Reserved Notation "\join^c_ ( i 'in' A ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \join^c_ ( i  'in'  A ) '/  '  F ']'").

Module Order.

(**************)
(* STRUCTURES *)
(**************)

Module POrder.
Section ClassDef.
Record mixin_of (T : eqType) := Mixin {
  le : rel T;
  lt : rel T;
  _  : forall x y, lt x y = (y != x) && (le x y);
  _  : reflexive     le;
  _  : antisymmetric le;
  _  : transitive    le
}.

Record class_of T := Class {
  base  : Choice.class_of T;
  mixin : mixin_of (EqType T base)
}.

Local Coercion base : class_of >-> Choice.class_of.

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack disp T c.
Definition clone_with disp' c of phant_id class c := @Pack disp' T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack :=
  fun bT b & phant_id (Choice.class bT) b =>
  fun m => Pack disp (@Class T b m).

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
End ClassDef.

Module Exports.
Coercion base : class_of >-> Choice.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Canonical eqType.
Canonical choiceType.
Notation porderType := type.
Notation porderMixin := mixin_of.
Notation POrderMixin := Mixin.
Notation POrderType disp T m := (@pack T disp _ _ id m).
Notation "[ 'porderType' 'of' T 'for' cT ]" := (@clone T _ cT _ id)
  (at level 0, format "[ 'porderType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'porderType' 'of' T 'for' cT 'with' disp ]" :=
  (@clone_with T _ cT disp _ id)
  (at level 0, format "[ 'porderType'  'of'  T  'for'  cT  'with'  disp ]") :
  form_scope.
Notation "[ 'porderType' 'of' T ]" := [porderType of T for _]
  (at level 0, format "[ 'porderType'  'of'  T ]") : form_scope.
Notation "[ 'porderType' 'of' T 'with' disp ]" :=
  [porderType of T for _ with disp]
  (at level 0, format "[ 'porderType'  'of'  T  'with' disp ]") : form_scope.
End Exports.

End POrder.
Import POrder.Exports.
Bind Scope cpo_sort with POrder.sort.

Module Import POrderDef.
Section Def.

Variable (disp : unit).
Local Notation porderType := (porderType disp).
Variable (T : porderType).

Definition le (R : porderType) : rel R := POrder.le (POrder.class R).
Local Notation "x <= y" := (le x y) : order_scope.

Definition lt (R : porderType) : rel R := POrder.lt (POrder.class R).
Local Notation "x < y" := (lt x y) : order_scope.

Definition comparable (R : porderType) : rel R :=
  fun (x y : R) => (x <= y) || (y <= x).
Local Notation "x >=< y" := (comparable x y) : order_scope.
Local Notation "x >< y" := (~~ (x >=< y)) : order_scope.

Definition ge : simpl_rel T := [rel x y | y <= x].
Definition gt : simpl_rel T := [rel x y | y < x].
Definition leif (x y : T) C : Prop := ((x <= y) * ((x == y) = C))%type.

Definition le_of_leif x y C (le_xy : @leif x y C) := le_xy.1 : le x y.

Variant le_xor_gt (x y : T) : bool -> bool -> Set :=
  | LerNotGt of x <= y : le_xor_gt x y true false
  | GtrNotLe of y < x  : le_xor_gt x y false true.

Variant lt_xor_ge (x y : T) : bool -> bool -> Set :=
  | LtrNotGe of x < y  : lt_xor_ge x y false true
  | GerNotLt of y <= x : lt_xor_ge x y true false.

Variant comparer (x y : T) :
  bool -> bool -> bool -> bool -> bool -> bool -> Set :=
  | ComparerEq of x = y : comparer x y
    true true true true false false
  | ComparerLt of x < y : comparer x y
    false false true false true false
  | ComparerGt of y < x : comparer x y
    false false false true false true.

Variant incomparer (x y : T) :
  bool -> bool -> bool -> bool -> bool -> bool -> bool -> bool -> Set :=
  | InComparerEq of x = y : incomparer x y
    true true true true false false true true
  | InComparerLt of x < y : incomparer x y
    false false true false true false true true
  | InComparerGt of y < x : incomparer x y
    false false false true false true true true
  | InComparer of x >< y : incomparer x y
    false false false false false false false false.

End Def.
End POrderDef.

Prenex Implicits lt le leif.
Arguments ge {_ _}.
Arguments gt {_ _}.

Module Import POSyntax.

Notation "<=%O" := le : order_scope.
Notation ">=%O" := ge : order_scope.
Notation "<%O" := lt : order_scope.
Notation ">%O" := gt : order_scope.
Notation "<?=%O" := leif : order_scope.
Notation ">=<%O" := comparable : order_scope.
Notation "><%O" := (fun x y => ~~ (comparable x y)) : order_scope.

Notation "<= y" := (ge y) : order_scope.
Notation "<= y :> T" := (<= (y : T)) : order_scope.
Notation ">= y"  := (le y) : order_scope.
Notation ">= y :> T" := (>= (y : T)) : order_scope.

Notation "< y" := (gt y) : order_scope.
Notation "< y :> T" := (< (y : T)) : order_scope.
Notation "> y" := (lt y) : order_scope.
Notation "> y :> T" := (> (y : T)) : order_scope.

Notation ">=< y" := (comparable y) : order_scope.
Notation ">=< y :> T" := (>=< (y : T)) : order_scope.

Notation "x <= y" := (le x y) : order_scope.
Notation "x <= y :> T" := ((x : T) <= (y : T)) : order_scope.
Notation "x >= y" := (y <= x) (only parsing) : order_scope.
Notation "x >= y :> T" := ((x : T) >= (y : T)) (only parsing) : order_scope.

Notation "x < y"  := (lt x y) : order_scope.
Notation "x < y :> T" := ((x : T) < (y : T)) : order_scope.
Notation "x > y"  := (y < x) (only parsing) : order_scope.
Notation "x > y :> T" := ((x : T) > (y : T)) (only parsing) : order_scope.

Notation "x <= y <= z" := ((x <= y) && (y <= z)) : order_scope.
Notation "x < y <= z" := ((x < y) && (y <= z)) : order_scope.
Notation "x <= y < z" := ((x <= y) && (y < z)) : order_scope.
Notation "x < y < z" := ((x < y) && (y < z)) : order_scope.

Notation "x <= y ?= 'iff' C" := (leif x y C) : order_scope.
Notation "x <= y ?= 'iff' C :> T" := ((x : T) <= (y : T) ?= iff C)
  (only parsing) : order_scope.

Notation ">=< x" := (comparable x) : order_scope.
Notation ">=< x :> T" := (>=< (x : T)) (only parsing) : order_scope.
Notation "x >=< y" := (comparable x y) : order_scope.

Notation ">< x" := (fun y => ~~ (comparable x y)) : order_scope.
Notation ">< x :> T" := (>< (x : T)) (only parsing) : order_scope.
Notation "x >< y" := (~~ (comparable x y)) : order_scope.

End POSyntax.

Module POCoercions.
Coercion le_of_leif : leif >-> is_true.
End POCoercions.

Module Lattice.
Section ClassDef.

Record mixin_of d (T : porderType d) := Mixin {
  meet : T -> T -> T;
  join : T -> T -> T;
  _ : commutative meet;
  _ : commutative join;
  _ : associative meet;
  _ : associative join;
  _ : forall y x, meet x (join x y) = x;
  _ : forall y x, join x (meet x y) = x;
  _ : forall x y, (x <= y) = (meet x y == x);
  _ : left_distributive meet join;
}.

Record class_of (T : Type) := Class {
  base  : POrder.class_of T;
  mixin_disp : unit;
  mixin : mixin_of (POrder.Pack mixin_disp base)
}.

Local Coercion base : class_of >-> POrder.class_of.

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack disp T c.
Definition clone_with disp' c of phant_id class c := @Pack disp' T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack b0 (m0 : mixin_of (@POrder.Pack disp T b0)) :=
  fun bT b & phant_id (@POrder.class disp bT) b =>
  fun disp' m & phant_id m0 m => Pack disp (@Class T b disp' m).

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition porderType := @POrder.Pack disp cT xclass.
End ClassDef.

Module Exports.
Coercion base : class_of >-> POrder.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion porderType : type >-> POrder.type.
Canonical eqType.
Canonical choiceType.
Canonical porderType.
Notation latticeType  := type.
Notation latticeMixin := mixin_of.
Notation LatticeMixin := Mixin.
Notation LatticeType T m := (@pack T _ _ m _ _ id _ _ id).
Notation "[ 'latticeType' 'of' T 'for' cT ]" := (@clone T _ cT _ id)
  (at level 0, format "[ 'latticeType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'latticeType' 'of' T 'for' cT 'with' disp ]" :=
  (@clone_with T _ cT disp _ id)
  (at level 0, format "[ 'latticeType'  'of'  T  'for'  cT  'with'  disp ]") :
  form_scope.
Notation "[ 'latticeType' 'of' T ]" := [latticeType of T for _]
  (at level 0, format "[ 'latticeType'  'of'  T ]") : form_scope.
Notation "[ 'latticeType' 'of' T 'with' disp ]" :=
  [latticeType of T for _ with disp]
  (at level 0, format "[ 'latticeType'  'of'  T  'with' disp ]") : form_scope.
End Exports.

End Lattice.
Export Lattice.Exports.

Module Import LatticeDef.
Section LatticeDef.
Context {disp : unit}.
Local Notation latticeType := (latticeType disp).
Context {T : latticeType}.
Definition meet : T -> T -> T := Lattice.meet (Lattice.class T).
Definition join : T -> T -> T := Lattice.join (Lattice.class T).

Variant le_xor_gt (x y : T) : bool -> bool -> T -> T -> T -> T -> Set :=
  | LerNotGt of x <= y : le_xor_gt x y true false x x y y
  | GtrNotLe of y < x  : le_xor_gt x y false true y y x x.

Variant lt_xor_ge (x y : T) : bool -> bool -> T -> T -> T -> T -> Set :=
  | LtrNotGe of x < y  : lt_xor_ge x y false true x x y y
  | GerNotLt of y <= x : lt_xor_ge x y true false y y x x.

Variant comparer (x y : T) :
  bool -> bool -> bool -> bool -> bool -> bool -> T -> T -> T -> T -> Set :=
  | ComparerEq of x = y : comparer x y
    true true true true false false x x x x
  | ComparerLt of x < y : comparer x y
    false false true false true false x x y y
  | ComparerGt of y < x : comparer x y
    false false false true false true y y x x.

Variant incomparer (x y : T) :
  bool -> bool -> bool -> bool -> bool -> bool -> bool -> bool ->
  T -> T -> T -> T -> Set :=
  | InComparerEq of x = y : incomparer x y
    true true true true false false true true x x x x
  | InComparerLt of x < y : incomparer x y
    false false true false true false true true x x y y
  | InComparerGt of y < x : incomparer x y
    false false false true false true true true y y x x
  | InComparer of x >< y  : incomparer x y
    false false false false false false false false
    (meet x y) (meet x y) (join x y) (join x y).

End LatticeDef.
End LatticeDef.

Module Import LatticeSyntax.

Notation "x `&` y" :=  (meet x y).
Notation "x `|` y" := (join x y).

End LatticeSyntax.

Module Total.
Definition mixin_of d (T : latticeType d) := (total (<=%O : rel T)).
Section ClassDef.

Record class_of (T : Type) := Class {
  base  : Lattice.class_of T;
  mixin_disp : unit;
  mixin : mixin_of (Lattice.Pack mixin_disp base)
}.

Local Coercion base : class_of >-> Lattice.class_of.

Structure type (d : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone disp' c & phant_id class c := @Pack disp' T c.
Definition clone_with disp' c & phant_id class c := @Pack disp' T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack b0 (m0 : mixin_of (@Lattice.Pack disp T b0)) :=
  fun bT b & phant_id (@Lattice.class disp bT) b =>
  fun disp' m & phant_id m0 m => Pack disp (@Class T b disp' m).

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition porderType := @POrder.Pack disp cT xclass.
Definition latticeType := @Lattice.Pack disp cT xclass.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Lattice.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion porderType : type >-> POrder.type.
Coercion latticeType : type >-> Lattice.type.
Canonical eqType.
Canonical choiceType.
Canonical porderType.
Canonical latticeType.
Notation orderType  := type.
Notation OrderType T m := (@pack T _ _ m _ _ id _ _ id).
Notation "[ 'orderType' 'of' T 'for' cT ]" := (@clone T _ cT _ _ id)
  (at level 0, format "[ 'orderType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'orderType' 'of' T 'for' cT 'with' disp ]" :=
  (@clone_with T _ cT disp _ id)
  (at level 0, format "[ 'orderType'  'of'  T  'for'  cT  'with'  disp ]") :
  form_scope.
Notation "[ 'orderType' 'of' T ]" := [orderType of T for _]
  (at level 0, format "[ 'orderType'  'of'  T ]") : form_scope.
Notation "[ 'orderType' 'of' T 'with' disp ]" :=
  [orderType of T for _ with disp]
  (at level 0, format "[ 'orderType'  'of'  T  'with' disp ]") : form_scope.
End Exports.

End Total.
Import Total.Exports.

Module Import TotalDef.
Section TotalDef.
Context {disp : unit} {T : orderType disp} {I : finType}.
Definition arg_min := @extremum T I <=%O.
Definition arg_max := @extremum T I >=%O.
End TotalDef.
End TotalDef.

Module Import TotalSyntax.

Fact total_display : unit. Proof. exact: tt. Qed.

Notation max := (@join total_display _).
Notation "@ 'max' R" :=
  (@join total_display R) (at level 10, R at level 8, only parsing).
Notation min := (@meet total_display _).
Notation "@ 'min' R" :=
  (@meet total_display R) (at level 10, R at level 8, only parsing).

Notation "\max_ ( i <- r | P ) F" :=
  (\big[@join total_display _/0%O]_(i <- r | P%B) F%O) : order_scope.
Notation "\max_ ( i <- r ) F" :=
  (\big[@join total_display _/0%O]_(i <- r) F%O) : order_scope.
Notation "\max_ ( i | P ) F" :=
  (\big[@join total_display _/0%O]_(i | P%B) F%O) : order_scope.
Notation "\max_ i F" :=
  (\big[@join total_display _/0%O]_i F%O) : order_scope.
Notation "\max_ ( i : I | P ) F" :=
  (\big[@join total_display _/0%O]_(i : I | P%B) F%O) (only parsing) :
  order_scope.
Notation "\max_ ( i : I ) F" :=
  (\big[@join total_display _/0%O]_(i : I) F%O) (only parsing) : order_scope.
Notation "\max_ ( m <= i < n | P ) F" :=
  (\big[@join total_display _/0%O]_(m <= i < n | P%B) F%O) : order_scope.
Notation "\max_ ( m <= i < n ) F" :=
  (\big[@join total_display _/0%O]_(m <= i < n) F%O) : order_scope.
Notation "\max_ ( i < n | P ) F" :=
  (\big[@join total_display _/0%O]_(i < n | P%B) F%O) : order_scope.
Notation "\max_ ( i < n ) F" :=
  (\big[@join total_display _/0%O]_(i < n) F%O) : order_scope.
Notation "\max_ ( i 'in' A | P ) F" :=
  (\big[@join total_display _/0%O]_(i in A | P%B) F%O) : order_scope.
Notation "\max_ ( i 'in' A ) F" :=
  (\big[@join total_display _/0%O]_(i in A) F%O) : order_scope.

Notation "[ 'arg' 'min_' ( i < i0 | P ) F ]" :=
    (arg_min i0 (fun i => P%B) (fun i => F))
  (at level 0, i, i0 at level 10,
   format "[ 'arg'  'min_' ( i  <  i0  |  P )  F ]") : order_scope.

Notation "[ 'arg' 'min_' ( i < i0 'in' A ) F ]" :=
    [arg min_(i < i0 | i \in A) F]
  (at level 0, i, i0 at level 10,
   format "[ 'arg'  'min_' ( i  <  i0  'in'  A )  F ]") : order_scope.

Notation "[ 'arg' 'min_' ( i < i0 ) F ]" := [arg min_(i < i0 | true) F]
  (at level 0, i, i0 at level 10,
   format "[ 'arg'  'min_' ( i  <  i0 )  F ]") : order_scope.

Notation "[ 'arg' 'max_' ( i > i0 | P ) F ]" :=
     (arg_max i0 (fun i => P%B) (fun i => F))
  (at level 0, i, i0 at level 10,
   format "[ 'arg'  'max_' ( i  >  i0  |  P )  F ]") : order_scope.

Notation "[ 'arg' 'max_' ( i > i0 'in' A ) F ]" :=
    [arg max_(i > i0 | i \in A) F]
  (at level 0, i, i0 at level 10,
   format "[ 'arg'  'max_' ( i  >  i0  'in'  A )  F ]") : order_scope.

Notation "[ 'arg' 'max_' ( i > i0 ) F ]" := [arg max_(i > i0 | true) F]
  (at level 0, i, i0 at level 10,
   format "[ 'arg'  'max_' ( i  >  i0 ) F ]") : order_scope.

End TotalSyntax.

Module BLattice.
Section ClassDef.
Record mixin_of d (T : porderType d) := Mixin {
  bottom : T;
  _ : forall x, bottom <= x;
}.

Record class_of (T : Type) := Class {
  base  : Lattice.class_of T;
  mixin_disp : unit;
  mixin : mixin_of (POrder.Pack mixin_disp base)
}.

Local Coercion base : class_of >-> Lattice.class_of.

Structure type (d : unit) := Pack { sort; _ : class_of sort}.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack disp T c.
Definition clone_with disp' c of phant_id class c := @Pack disp' T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack b0 (m0 : mixin_of (@Lattice.Pack disp T b0)) :=
  fun bT b & phant_id (@Lattice.class disp bT) b =>
  fun disp' m & phant_id m0 m => Pack disp (@Class T b disp' m).

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition porderType := @POrder.Pack disp cT xclass.
Definition latticeType := @Lattice.Pack disp cT xclass.
End ClassDef.

Module Exports.
Coercion base : class_of >-> Lattice.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion porderType : type >-> POrder.type.
Coercion latticeType : type >-> Lattice.type.
Canonical eqType.
Canonical choiceType.
Canonical porderType.
Canonical latticeType.
Notation blatticeType  := type.
Notation blatticeMixin := mixin_of.
Notation BLatticeMixin := Mixin.
Notation BLatticeType T m := (@pack T _ _ m _ _ id _ _ id).
Notation "[ 'blatticeType' 'of' T 'for' cT ]" := (@clone T _ cT _ id)
  (at level 0, format "[ 'blatticeType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'blatticeType' 'of' T 'for' cT 'with' disp ]" :=
  (@clone_with T _ cT disp _ id)
  (at level 0, format "[ 'blatticeType'  'of'  T  'for'  cT  'with'  disp ]") :
  form_scope.
Notation "[ 'blatticeType' 'of' T ]" := [blatticeType of T for _]
  (at level 0, format "[ 'blatticeType'  'of'  T ]") : form_scope.
Notation "[ 'blatticeType' 'of' T 'with' disp ]" :=
  [blatticeType of T for _ with disp]
  (at level 0, format "[ 'blatticeType'  'of'  T  'with' disp ]") : form_scope.
End Exports.

End BLattice.
Export BLattice.Exports.

Module Import BLatticeDef.
Definition bottom {disp : unit} {T : blatticeType disp} : T :=
  BLattice.bottom (BLattice.class T).
End BLatticeDef.

Module Import BLatticeSyntax.
Notation "0" := bottom : order_scope.

Notation "\join_ ( i <- r | P ) F" :=
  (\big[@join _ _/0%O]_(i <- r | P%B) F%O) : order_scope.
Notation "\join_ ( i <- r ) F" :=
  (\big[@join _ _/0%O]_(i <- r) F%O) : order_scope.
Notation "\join_ ( i | P ) F" :=
  (\big[@join _ _/0%O]_(i | P%B) F%O) : order_scope.
Notation "\join_ i F" :=
  (\big[@join _ _/0%O]_i F%O) : order_scope.
Notation "\join_ ( i : I | P ) F" :=
  (\big[@join _ _/0%O]_(i : I | P%B) F%O) (only parsing) : order_scope.
Notation "\join_ ( i : I ) F" :=
  (\big[@join _ _/0%O]_(i : I) F%O) (only parsing) : order_scope.
Notation "\join_ ( m <= i < n | P ) F" :=
  (\big[@join _ _/0%O]_(m <= i < n | P%B) F%O) : order_scope.
Notation "\join_ ( m <= i < n ) F" :=
  (\big[@join _ _/0%O]_(m <= i < n) F%O) : order_scope.
Notation "\join_ ( i < n | P ) F" :=
  (\big[@join _ _/0%O]_(i < n | P%B) F%O) : order_scope.
Notation "\join_ ( i < n ) F" :=
  (\big[@join _ _/0%O]_(i < n) F%O) : order_scope.
Notation "\join_ ( i 'in' A | P ) F" :=
  (\big[@join _ _/0%O]_(i in A | P%B) F%O) : order_scope.
Notation "\join_ ( i 'in' A ) F" :=
  (\big[@join _ _/0%O]_(i in A) F%O) : order_scope.

End BLatticeSyntax.

Module TBLattice.
Section ClassDef.
Record mixin_of d (T : porderType d) := Mixin {
  top : T;
  _ : forall x, x <= top;
}.

Record class_of (T : Type) := Class {
  base  : BLattice.class_of T;
  mixin_disp : unit;
  mixin : mixin_of (POrder.Pack mixin_disp base)
}.

Local Coercion base : class_of >-> BLattice.class_of.

Structure type (d : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack disp T c.
Definition clone_with disp' c of phant_id class c := @Pack disp' T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack b0 (m0 : mixin_of (@BLattice.Pack disp T b0)) :=
  fun bT b & phant_id (@BLattice.class disp bT) b =>
  fun disp' m & phant_id m0 m => Pack disp (@Class T b disp' m).

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition porderType := @POrder.Pack disp cT xclass.
Definition latticeType := @Lattice.Pack disp cT xclass.
Definition blatticeType := @BLattice.Pack disp cT xclass.
End ClassDef.

Module Exports.
Coercion base : class_of >-> BLattice.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion porderType : type >-> POrder.type.
Coercion latticeType : type >-> Lattice.type.
Coercion blatticeType : type >-> BLattice.type.
Canonical eqType.
Canonical choiceType.
Canonical porderType.
Canonical latticeType.
Canonical blatticeType.
Notation tblatticeType  := type.
Notation tblatticeMixin := mixin_of.
Notation TBLatticeMixin := Mixin.
Notation TBLatticeType T m := (@pack T _ _ m _ _ id _ _ id).
Notation "[ 'tblatticeType' 'of' T 'for' cT ]" := (@clone T _ cT _ id)
  (at level 0, format "[ 'tblatticeType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'tblatticeType' 'of' T 'for' cT 'with' disp ]" :=
  (@clone_with T _ cT disp _ id)
  (at level 0, format "[ 'tblatticeType'  'of'  T  'for'  cT  'with'  disp ]") :
  form_scope.
Notation "[ 'tblatticeType' 'of' T ]" := [tblatticeType of T for _]
  (at level 0, format "[ 'tblatticeType'  'of'  T ]") : form_scope.
Notation "[ 'tblatticeType' 'of' T 'with' disp ]" :=
  [tblatticeType of T for _ with disp]
  (at level 0, format "[ 'tblatticeType'  'of'  T  'with' disp ]") : form_scope.
End Exports.

End TBLattice.
Export TBLattice.Exports.

Module Import TBLatticeDef.
Definition top disp  {T : tblatticeType disp} : T :=
  TBLattice.top (TBLattice.class T).
End TBLatticeDef.

Module Import TBLatticeSyntax.

Notation "1" := top : order_scope.

Notation "\meet_ ( i <- r | P ) F" :=
  (\big[meet/1]_(i <- r | P%B) F%O) : order_scope.
Notation "\meet_ ( i <- r ) F" :=
  (\big[meet/1]_(i <- r) F%O) : order_scope.
Notation "\meet_ ( i | P ) F" :=
  (\big[meet/1]_(i | P%B) F%O) : order_scope.
Notation "\meet_ i F" :=
  (\big[meet/1]_i F%O) : order_scope.
Notation "\meet_ ( i : I | P ) F" :=
  (\big[meet/1]_(i : I | P%B) F%O) (only parsing) : order_scope.
Notation "\meet_ ( i : I ) F" :=
  (\big[meet/1]_(i : I) F%O) (only parsing) : order_scope.
Notation "\meet_ ( m <= i < n | P ) F" :=
 (\big[meet/1]_(m <= i < n | P%B) F%O) : order_scope.
Notation "\meet_ ( m <= i < n ) F" :=
 (\big[meet/1]_(m <= i < n) F%O) : order_scope.
Notation "\meet_ ( i < n | P ) F" :=
 (\big[meet/1]_(i < n | P%B) F%O) : order_scope.
Notation "\meet_ ( i < n ) F" :=
 (\big[meet/1]_(i < n) F%O) : order_scope.
Notation "\meet_ ( i 'in' A | P ) F" :=
 (\big[meet/1]_(i in A | P%B) F%O) : order_scope.
Notation "\meet_ ( i 'in' A ) F" :=
 (\big[meet/1]_(i in A) F%O) : order_scope.

End TBLatticeSyntax.

Module CBLattice.
Section ClassDef.
Record mixin_of d (T : blatticeType d) := Mixin {
  sub : T -> T -> T;
  _ : forall x y, y `&` sub x y = bottom;
  _ : forall x y, (x `&` y) `|` sub x y = x
}.

Record class_of (T : Type) := Class {
  base  : BLattice.class_of T;
  mixin_disp : unit;
  mixin : mixin_of (BLattice.Pack mixin_disp base)
}.

Local Coercion base : class_of >-> BLattice.class_of.

Structure type (d : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack disp T c.
Definition clone_with disp' c of phant_id class c := @Pack disp' T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack b0 (m0 : mixin_of (@BLattice.Pack disp T b0)) :=
  fun bT b & phant_id (@BLattice.class disp bT) b =>
  fun disp' m & phant_id m0 m => Pack disp (@Class T b disp' m).

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition porderType := @POrder.Pack disp cT xclass.
Definition latticeType := @Lattice.Pack disp cT xclass.
Definition blatticeType := @BLattice.Pack disp cT xclass.
End ClassDef.

Module Exports.
Coercion base : class_of >-> BLattice.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion porderType : type >-> POrder.type.
Coercion latticeType : type >-> Lattice.type.
Coercion blatticeType : type >-> BLattice.type.
Canonical eqType.
Canonical choiceType.
Canonical porderType.
Canonical latticeType.
Canonical blatticeType.
Notation cblatticeType  := type.
Notation cblatticeMixin := mixin_of.
Notation CBLatticeMixin := Mixin.
Notation CBLatticeType T m := (@pack T _ _ m _ _ id _ _ id).
Notation "[ 'cblatticeType' 'of' T 'for' cT ]" := (@clone T _ cT _ id)
  (at level 0, format "[ 'cblatticeType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'cblatticeType' 'of' T 'for' cT 'with' disp ]" :=
  (@clone_with T _ cT disp _ id)
  (at level 0, format "[ 'cblatticeType'  'of'  T  'for'  cT  'with'  disp ]") :
  form_scope.
Notation "[ 'cblatticeType' 'of' T ]" := [cblatticeType of T for _]
  (at level 0, format "[ 'cblatticeType'  'of'  T ]") : form_scope.
Notation "[ 'cblatticeType' 'of' T 'with' disp ]" :=
  [cblatticeType of T for _ with disp]
  (at level 0, format "[ 'cblatticeType'  'of'  T  'with' disp ]") : form_scope.
End Exports.

End CBLattice.
Export CBLattice.Exports.

Module Import CBLatticeDef.
Definition sub {disp : unit} {T : cblatticeType disp} : T -> T -> T :=
  CBLattice.sub (CBLattice.class T).
End CBLatticeDef.

Module Import CBLatticeSyntax.
Notation "x `\` y" := (sub x y).
End CBLatticeSyntax.

Module CTBLattice.
Section ClassDef.
Record mixin_of d (T : tblatticeType d) (sub : T -> T -> T) := Mixin {
   compl : T -> T;
   _ : forall x, compl x = sub top x
}.

Record class_of (T : Type) := Class {
  base  : TBLattice.class_of T;
  mixin1_disp : unit;
  mixin1 : CBLattice.mixin_of (BLattice.Pack mixin1_disp base);
  mixin2_disp : unit;
  mixin2 : @mixin_of _ (TBLattice.Pack mixin2_disp base) (CBLattice.sub mixin1)
}.

Local Coercion base : class_of >-> TBLattice.class_of.
Local Coercion base2 T (c : class_of T) : CBLattice.class_of T :=
  CBLattice.Class (mixin1 c).

Structure type (d : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack disp T c.
Definition clone_with disp' c of phant_id class c := @Pack disp' T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack :=
  fun bT  b  & phant_id (@TBLattice.class disp bT) b =>
  fun disp1 m1T m1 & phant_id (@CBLattice.class disp1 m1T)
                              (@CBLattice.Class _ _ _ m1) =>
  fun disp2 m2 => Pack disp (@Class T b disp1 m1 disp2 m2).

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition porderType := @POrder.Pack disp cT xclass.
Definition latticeType := @Lattice.Pack disp cT xclass.
Definition blatticeType := @BLattice.Pack disp cT xclass.
Definition tblatticeType := @TBLattice.Pack disp cT xclass.
Definition cblatticeType := @CBLattice.Pack disp cT xclass.
Definition tbd_cblatticeType :=
  @CBLattice.Pack disp tblatticeType xclass.
End ClassDef.

Module Exports.
Coercion base : class_of >-> TBLattice.class_of.
Coercion base2 : class_of >-> CBLattice.class_of.
Coercion mixin1 : class_of >-> CBLattice.mixin_of.
Coercion mixin2 : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion porderType : type >-> POrder.type.
Coercion latticeType : type >-> Lattice.type.
Coercion blatticeType : type >-> BLattice.type.
Coercion tblatticeType : type >-> TBLattice.type.
Coercion cblatticeType : type >-> CBLattice.type.
Canonical eqType.
Canonical choiceType.
Canonical porderType.
Canonical latticeType.
Canonical blatticeType.
Canonical tblatticeType.
Canonical cblatticeType.
Canonical tbd_cblatticeType.
Notation ctblatticeType  := type.
Notation ctblatticeMixin := mixin_of.
Notation CTBLatticeMixin := Mixin.
Notation CTBLatticeType T m := (@pack T _ _ _ id _ _ _ id _ m).
Notation "[ 'ctblatticeType' 'of' T 'for' cT ]" := (@clone T _ cT _ id)
  (at level 0, format "[ 'ctblatticeType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'ctblatticeType' 'of' T 'for' cT 'with' disp ]" :=
  (@clone_with T _ cT disp _ id)
  (at level 0, format "[ 'ctblatticeType'  'of'  T  'for'  cT  'with'  disp ]")
  : form_scope.
Notation "[ 'ctblatticeType' 'of' T ]" := [ctblatticeType of T for _]
  (at level 0, format "[ 'ctblatticeType'  'of'  T ]") : form_scope.
Notation "[ 'ctblatticeType' 'of' T 'with' disp ]" :=
  [ctblatticeType of T for _ with disp]
  (at level 0, format "[ 'ctblatticeType'  'of'  T  'with' disp ]") :
  form_scope.
Notation "[ 'default_ctblatticeType' 'of' T ]" :=
  (@pack T _ _ _ id _ _ id (Mixin (fun=> erefl)))
  (at level 0, format "[ 'default_ctblatticeType'  'of'  T ]") : form_scope.
End Exports.

End CTBLattice.
Export CTBLattice.Exports.

Module Import CTBLatticeDef.
Definition compl {d : unit} {T : ctblatticeType d} : T -> T :=
  CTBLattice.compl (CTBLattice.class T).
End CTBLatticeDef.

Module Import CTBLatticeSyntax.
Notation "~` A" := (compl A).
End CTBLatticeSyntax.

(**********)
(* FINITE *)
(**********)

Module FinPOrder.
Section ClassDef.

Record class_of T := Class {
  base  : POrder.class_of T;
  mixin : Finite.mixin_of (Equality.Pack base)
}.

Local Coercion base : class_of >-> POrder.class_of.
Local Coercion base2 T (c : class_of T) : Finite.class_of T :=
  Finite.Class (mixin c).

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack :=
  fun bT b & phant_id (@POrder.class disp bT) b =>
  fun mT m & phant_id (@Finite.class mT) (@Finite.Class _ _ m) =>
  Pack disp (@Class T b m).

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition countType := @Countable.Pack cT xclass.
Definition finType := @Finite.Pack cT xclass.
Definition porderType := @POrder.Pack disp cT xclass.
Definition count_porderType := @POrder.Pack disp countType xclass.
Definition fin_porderType := @POrder.Pack disp finType xclass.
End ClassDef.

Module Exports.
Coercion base : class_of >-> POrder.class_of.
Coercion base2 : class_of >-> Finite.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion countType : type >-> Countable.type.
Coercion finType : type >-> Finite.type.
Coercion porderType : type >-> POrder.type.
Canonical eqType.
Canonical choiceType.
Canonical countType.
Canonical finType.
Canonical porderType.
Canonical count_porderType.
Canonical fin_porderType.
Notation finPOrderType := type.
Notation "[ 'finPOrderType' 'of' T ]" := (@pack T _ _ _ id _ _ id)
  (at level 0, format "[ 'finPOrderType'  'of'  T ]") : form_scope.
End Exports.

End FinPOrder.
Import FinPOrder.Exports.
Bind Scope cpo_sort with FinPOrder.sort.

Module FinLattice.
Section ClassDef.

Record class_of (T : Type) := Class {
  base : TBLattice.class_of T;
  mixin : Finite.mixin_of (Equality.Pack base);
}.

Local Coercion base : class_of >-> TBLattice.class_of.
Local Coercion base2 T (c : class_of T) : Finite.class_of T :=
  Finite.Class (mixin c).
Local Coercion base3 T (c : class_of T) : FinPOrder.class_of T :=
  @FinPOrder.Class T c c.

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack :=
  fun bT b & phant_id (@TBLattice.class disp bT) b =>
  fun mT m & phant_id (@Finite.class mT) (@Finite.Class _ _ m) =>
  Pack disp (@Class T b m).

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition countType := @Countable.Pack cT xclass.
Definition finType := @Finite.Pack cT xclass.
Definition porderType := @POrder.Pack disp cT xclass.
Definition finPOrderType := @FinPOrder.Pack disp cT xclass.
Definition latticeType := @Lattice.Pack disp cT xclass.
Definition blatticeType := @BLattice.Pack disp cT xclass.
Definition tblatticeType := @TBLattice.Pack disp cT xclass.
Definition count_latticeType := @Lattice.Pack disp countType xclass.
Definition count_blatticeType := @BLattice.Pack disp countType xclass.
Definition count_tblatticeType := @TBLattice.Pack disp countType xclass.
Definition fin_latticeType := @Lattice.Pack disp finType xclass.
Definition fin_blatticeType := @BLattice.Pack disp finType xclass.
Definition fin_tblatticeType := @TBLattice.Pack disp finType xclass.
Definition finPOrder_latticeType := @Lattice.Pack disp finPOrderType xclass.
Definition finPOrder_blatticeType := @BLattice.Pack disp finPOrderType xclass.
Definition finPOrder_tblatticeType := @TBLattice.Pack disp finPOrderType xclass.

End ClassDef.

Module Exports.
Coercion base : class_of >-> TBLattice.class_of.
Coercion base2 : class_of >-> Finite.class_of.
Coercion base3 : class_of >-> FinPOrder.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion countType : type >-> Countable.type.
Coercion finType : type >-> Finite.type.
Coercion porderType : type >-> POrder.type.
Coercion finPOrderType : type >-> FinPOrder.type.
Coercion latticeType : type >-> Lattice.type.
Coercion blatticeType : type >-> BLattice.type.
Coercion tblatticeType : type >-> TBLattice.type.
Canonical eqType.
Canonical choiceType.
Canonical countType.
Canonical finType.
Canonical porderType.
Canonical finPOrderType.
Canonical latticeType.
Canonical blatticeType.
Canonical tblatticeType.
Canonical count_latticeType.
Canonical count_blatticeType.
Canonical count_tblatticeType.
Canonical fin_latticeType.
Canonical fin_blatticeType.
Canonical fin_tblatticeType.
Canonical finPOrder_latticeType.
Canonical finPOrder_blatticeType.
Canonical finPOrder_tblatticeType.
Notation finLatticeType  := type.
Notation "[ 'finLatticeType' 'of' T ]" := (@pack T _ _ _ id _ _ id)
  (at level 0, format "[ 'finLatticeType'  'of'  T ]") : form_scope.
End Exports.

End FinLattice.
Export FinLattice.Exports.

Module FinCLattice.
Section ClassDef.

Record class_of (T : Type) := Class {
  base  : CTBLattice.class_of T;
  mixin : Finite.mixin_of (Equality.Pack base);
}.

Local Coercion base : class_of >-> CTBLattice.class_of.
Local Coercion base2 T (c : class_of T) : Finite.class_of T :=
  Finite.Class (mixin c).
Local Coercion base3 T (c : class_of T) : FinLattice.class_of T :=
  @FinLattice.Class T c c.

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack :=
  fun bT b & phant_id (@CTBLattice.class disp bT) b =>
  fun mT m & phant_id (@Finite.class mT) (@Finite.Class _ _ m) =>
  Pack disp (@Class T b m).

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition countType := @Countable.Pack cT xclass.
Definition finType := @Finite.Pack cT xclass.
Definition porderType := @POrder.Pack disp cT xclass.
Definition finPOrderType := @FinPOrder.Pack disp cT xclass.
Definition latticeType := @Lattice.Pack disp cT xclass.
Definition blatticeType := @BLattice.Pack disp cT xclass.
Definition tblatticeType := @TBLattice.Pack disp cT xclass.
Definition finLatticeType := @FinLattice.Pack disp cT xclass.
Definition cblatticeType := @CBLattice.Pack disp cT xclass.
Definition ctblatticeType := @CTBLattice.Pack disp cT xclass.
Definition count_cblatticeType := @CBLattice.Pack disp countType xclass.
Definition count_ctblatticeType := @CTBLattice.Pack disp countType xclass.
Definition fin_cblatticeType := @CBLattice.Pack disp finType xclass.
Definition fin_ctblatticeType := @CTBLattice.Pack disp finType xclass.
Definition finPOrder_cblatticeType := @CBLattice.Pack disp finPOrderType xclass.
Definition finPOrder_ctblatticeType :=
  @CTBLattice.Pack disp finPOrderType xclass.
Definition finLattice_cblatticeType :=
  @CBLattice.Pack disp finLatticeType xclass.
Definition finLattice_ctblatticeType :=
  @CTBLattice.Pack disp finLatticeType xclass.

End ClassDef.

Module Exports.
Coercion base : class_of >-> CTBLattice.class_of.
Coercion base2 : class_of >-> Finite.class_of.
Coercion base3 : class_of >-> FinLattice.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion countType : type >-> Countable.type.
Coercion finType : type >-> Finite.type.
Coercion porderType : type >-> POrder.type.
Coercion finPOrderType : type >-> FinPOrder.type.
Coercion latticeType : type >-> Lattice.type.
Coercion blatticeType : type >-> BLattice.type.
Coercion tblatticeType : type >-> TBLattice.type.
Coercion finLatticeType : type >-> FinLattice.type.
Coercion cblatticeType : type >-> CBLattice.type.
Coercion ctblatticeType : type >-> CTBLattice.type.
Canonical eqType.
Canonical choiceType.
Canonical countType.
Canonical finType.
Canonical porderType.
Canonical finPOrderType.
Canonical latticeType.
Canonical blatticeType.
Canonical tblatticeType.
Canonical finLatticeType.
Canonical cblatticeType.
Canonical ctblatticeType.
Canonical count_cblatticeType.
Canonical count_ctblatticeType.
Canonical fin_cblatticeType.
Canonical fin_ctblatticeType.
Canonical finPOrder_cblatticeType.
Canonical finPOrder_ctblatticeType.
Canonical finLattice_cblatticeType.
Canonical finLattice_ctblatticeType.
Notation finCLatticeType  := type.
Notation "[ 'finCLatticeType' 'of' T ]" := (@pack T _ _ _ id _ _ id)
  (at level 0, format "[ 'finCLatticeType'  'of'  T ]") : form_scope.
End Exports.

End FinCLattice.
Export FinCLattice.Exports.

Module FinTotal.
Section ClassDef.

Record class_of (T : Type) := Class {
  base  : FinLattice.class_of T;
  mixin_disp : unit;
  mixin : Total.mixin_of (Lattice.Pack mixin_disp base)
}.

Local Coercion base : class_of >-> FinLattice.class_of.
Local Coercion base2 T (c : class_of T) : Total.class_of T :=
  @Total.Class _ c _ (mixin (c := c)).

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack :=
  fun bT b & phant_id (@FinLattice.class disp bT) b =>
  fun disp' mT m & phant_id (@Total.class disp mT) (@Total.Class _ _ _ m) =>
  Pack disp (@Class T b disp' m).

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition countType := @Countable.Pack cT xclass.
Definition finType := @Finite.Pack cT xclass.
Definition porderType := @POrder.Pack disp cT xclass.
Definition finPOrderType := @FinPOrder.Pack disp cT xclass.
Definition latticeType := @Lattice.Pack disp cT xclass.
Definition blatticeType := @BLattice.Pack disp cT xclass.
Definition tblatticeType := @TBLattice.Pack disp cT xclass.
Definition finLatticeType := @FinLattice.Pack disp cT xclass.
Definition orderType := @Total.Pack disp cT xclass.
Definition order_countType := @Countable.Pack orderType xclass.
Definition order_finType := @Finite.Pack orderType xclass.
Definition order_finPOrderType := @FinPOrder.Pack disp orderType xclass.
Definition order_blatticeType := @BLattice.Pack disp orderType xclass.
Definition order_tblatticeType := @TBLattice.Pack disp orderType xclass.
Definition order_finLatticeType := @FinLattice.Pack disp orderType xclass.

End ClassDef.

Module Exports.
Coercion base : class_of >-> FinLattice.class_of.
Coercion base2 : class_of >-> Total.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion countType : type >-> Countable.type.
Coercion finType : type >-> Finite.type.
Coercion porderType : type >-> POrder.type.
Coercion finPOrderType : type >-> FinPOrder.type.
Coercion latticeType : type >-> Lattice.type.
Coercion blatticeType : type >-> BLattice.type.
Coercion tblatticeType : type >-> TBLattice.type.
Coercion finLatticeType : type >-> FinLattice.type.
Coercion orderType : type >-> Total.type.
Canonical eqType.
Canonical choiceType.
Canonical countType.
Canonical finType.
Canonical porderType.
Canonical finPOrderType.
Canonical latticeType.
Canonical blatticeType.
Canonical tblatticeType.
Canonical finLatticeType.
Canonical orderType.
Canonical order_countType.
Canonical order_finType.
Canonical order_finPOrderType.
Canonical order_blatticeType.
Canonical order_tblatticeType.
Canonical order_finLatticeType.
Notation finOrderType := type.
Notation "[ 'finOrderType' 'of' T ]" := (@pack T _ _ _ id _ _ _ id)
  (at level 0, format "[ 'finOrderType'  'of'  T ]") : form_scope.
End Exports.

End FinTotal.
Export Total.Exports.

(************)
(* CONVERSE *)
(************)

Definition converse T : Type := T.
Definition converse_display : unit -> unit. Proof. exact. Qed.
Local Notation "T ^c" := (converse T) (at level 2, format "T ^c") : type_scope.

Module Import ConverseSyntax.

Notation "<=^c%O" := (@le (converse_display _) _) : order_scope.
Notation ">=^c%O" := (@ge (converse_display _) _)  : order_scope.
Notation ">=^c%O" := (@ge (converse_display _) _)  : order_scope.
Notation "<^c%O" := (@lt (converse_display _) _) : order_scope.
Notation ">^c%O" := (@gt (converse_display _) _) : order_scope.
Notation "<?=^c%O" := (@leif (converse_display _) _) : order_scope.
Notation ">=<^c%O" := (@comparable (converse_display _) _) : order_scope.
Notation "><^c%O" := (fun x y => ~~ (@comparable (converse_display _) _ x y)) :
  order_scope.

Notation "<=^c y" := (>=^c%O y) : order_scope.
Notation "<=^c y :> T" := (<=^c (y : T)) : order_scope.
Notation ">=^c y"  := (<=^c%O y) : order_scope.
Notation ">=^c y :> T" := (>=^c (y : T)) : order_scope.

Notation "<^c y" := (>^c%O y) : order_scope.
Notation "<^c y :> T" := (<^c (y : T)) : order_scope.
Notation ">^c y" := (<^c%O y) : order_scope.
Notation ">^c y :> T" := (>^c (y : T)) : order_scope.

Notation ">=<^c y" := (>=<^c%O y) : order_scope.
Notation ">=<^c y :> T" := (>=<^c (y : T)) : order_scope.

Notation "x <=^c y" := (<=^c%O x y) : order_scope.
Notation "x <=^c y :> T" := ((x : T) <=^c (y : T)) : order_scope.
Notation "x >=^c y" := (y <=^c x) (only parsing) : order_scope.
Notation "x >=^c y :> T" := ((x : T) >=^c (y : T)) (only parsing) : order_scope.

Notation "x <^c y"  := (<^c%O x y) : order_scope.
Notation "x <^c y :> T" := ((x : T) <^c (y : T)) : order_scope.
Notation "x >^c y"  := (y <^c x) (only parsing) : order_scope.
Notation "x >^c y :> T" := ((x : T) >^c (y : T)) (only parsing) : order_scope.

Notation "x <=^c y <=^c z" := ((x <=^c y) && (y <=^c z)) : order_scope.
Notation "x <^c y <=^c z" := ((x <^c y) && (y <=^c z)) : order_scope.
Notation "x <=^c y <^c z" := ((x <=^c y) && (y <^c z)) : order_scope.
Notation "x <^c y <^c z" := ((x <^c y) && (y <^c z)) : order_scope.

Notation "x <=^c y ?= 'iff' C" := (<?=^c%O x y C) : order_scope.
Notation "x <=^c y ?= 'iff' C :> R" := ((x : R) <=^c (y : R) ?= iff C)
  (only parsing) : order_scope.

Notation ">=<^c x" := (>=<^c%O x) : order_scope.
Notation ">=<^c x :> T" := (>=<^c (x : T)) (only parsing) : order_scope.
Notation "x >=<^c y" := (>=<^c%O x y) : order_scope.

Notation "><^c x" := (fun y => ~~ (>=<^c%O x y)) : order_scope.
Notation "><^c x :> T" := (><^c (x : T)) (only parsing) : order_scope.
Notation "x ><^c y" := (~~ (><^c%O x y)) : order_scope.

Notation "x `&^c` y" :=  (@meet (converse_display _) _ x y).
Notation "x `|^c` y" := (@join (converse_display _) _ x y).

End ConverseSyntax.

(**********)
(* THEORY *)
(**********)

Module Import POrderTheory.
Section POrderTheory.
Import POrderDef.

Context {disp : unit}.
Local Notation porderType := (porderType disp).
Context {T : porderType}.

Implicit Types x y : T.

Lemma geE x y : ge x y = (y <= x). Proof. by []. Qed.
Lemma gtE x y : gt x y = (y < x). Proof. by []. Qed.

Lemma lexx (x : T) : x <= x.
Proof. by case: T x => ? [? []]. Qed.
Hint Resolve lexx : core.

Definition le_refl : reflexive le := lexx.
Definition ge_refl : reflexive ge := lexx.
Hint Resolve le_refl : core.

Lemma le_anti: antisymmetric (<=%O : rel T).
Proof. by case: T => ? [? []]. Qed.

Lemma ge_anti: antisymmetric (>=%O : rel T).
Proof. by move=> x y /le_anti. Qed.

Lemma le_trans: transitive (<=%O : rel T).
Proof. by case: T => ? [? []]. Qed.

Lemma ge_trans: transitive (>=%O : rel T).
Proof. by move=> ? ? ? ? /le_trans; apply. Qed.

Lemma lt_def x y: (x < y) = (y != x) && (x <= y).
Proof. by case: T x y => ? [? []]. Qed.

Lemma lt_neqAle x y: (x < y) = (x != y) && (x <= y).
Proof. by rewrite lt_def eq_sym. Qed.

Lemma ltxx x: x < x = false.
Proof. by rewrite lt_def eqxx. Qed.

Definition lt_irreflexive : irreflexive lt := ltxx.
Hint Resolve lt_irreflexive : core.

Definition ltexx := (lexx, ltxx).

Lemma le_eqVlt x y: (x <= y) = (x == y) || (x < y).
Proof. by rewrite lt_neqAle; case: eqP => //= ->; rewrite lexx. Qed.

Lemma lt_eqF x y: x < y -> x == y = false.
Proof. by rewrite lt_neqAle => /andP [/negbTE->]. Qed.

Lemma gt_eqF x y : y < x -> x == y = false.
Proof. by apply: contraTF => /eqP ->; rewrite ltxx. Qed.

Lemma eq_le x y: (x == y) = (x <= y <= x).
Proof. by apply/eqP/idP => [->|/le_anti]; rewrite ?lexx. Qed.

Lemma ltW x y: x < y -> x <= y.
Proof. by rewrite le_eqVlt orbC => ->. Qed.

Lemma lt_le_trans y x z: x < y -> y <= z -> x < z.
Proof.
rewrite !lt_neqAle => /andP [nexy lexy leyz]; rewrite (le_trans lexy) // andbT.
by apply: contraNneq nexy => eqxz; rewrite eqxz eq_le leyz andbT in lexy *.
Qed.

Lemma lt_trans: transitive (<%O : rel T).
Proof. by move=> y x z le1 /ltW le2; apply/(@lt_le_trans y). Qed.

Lemma le_lt_trans y x z: x <= y -> y < z -> x < z.
Proof. by rewrite le_eqVlt => /orP [/eqP ->|/lt_trans t /t]. Qed.

Lemma lt_nsym x y : x < y -> y < x -> False.
Proof. by move=> xy /(lt_trans xy); rewrite ltxx. Qed.

Lemma lt_asym x y : x < y < x = false.
Proof. by apply/negP => /andP []; apply: lt_nsym. Qed.

Lemma le_gtF x y: x <= y -> y < x = false.
Proof.
by move=> le_xy; apply/negP => /lt_le_trans /(_ le_xy); rewrite ltxx.
Qed.

Lemma lt_geF x y : (x < y) -> y <= x = false.
Proof.
by move=> le_xy; apply/negP => /le_lt_trans /(_ le_xy); rewrite ltxx.
Qed.

Definition lt_gtF x y hxy := le_gtF (@ltW x y hxy).

Lemma lt_leAnge x y : (x < y) = (x <= y) && ~~ (y <= x).
Proof.
apply/idP/idP => [ltxy|/andP[lexy Nleyx]]; first by rewrite ltW // lt_geF.
by rewrite lt_neqAle lexy andbT; apply: contraNneq Nleyx => ->.
Qed.

Lemma lt_le_asym x y : x < y <= x = false.
Proof. by rewrite lt_neqAle -andbA -eq_le eq_sym andNb. Qed.

Lemma le_lt_asym x y : x <= y < x = false.
Proof. by rewrite andbC lt_le_asym. Qed.

Definition lte_anti := (=^~ eq_le, lt_asym, lt_le_asym, le_lt_asym).

Lemma lt_sorted_uniq_le (s : seq T) :
   sorted lt s = uniq s && sorted le s.
Proof.
case: s => //= n s; elim: s n => //= m s IHs n.
rewrite inE lt_neqAle negb_or IHs -!andbA.
case sn: (n \in s); last do !bool_congr.
rewrite andbF; apply/and5P=> [[ne_nm lenm _ _ le_ms]]; case/negP: ne_nm.
by rewrite eq_le lenm /=; apply: (allP (order_path_min le_trans le_ms)).
Qed.

Lemma eq_sorted_lt (s1 s2 : seq T) :
  sorted lt s1 -> sorted lt s2 -> s1 =i s2 -> s1 = s2.
Proof. by apply: eq_sorted_irr => //; apply: lt_trans. Qed.

Lemma eq_sorted_le (s1 s2 : seq T) :
   sorted le s1 -> sorted le s2 -> perm_eq s1 s2 -> s1 = s2.
Proof. by apply: eq_sorted; [apply: le_trans|apply: le_anti]. Qed.

Lemma comparable_leNgt x y : x >=< y -> (x <= y) = ~~ (y < x).
Proof.
move=> c_xy; apply/idP/idP => [/le_gtF/negP/negP//|]; rewrite lt_neqAle.
by move: c_xy => /orP [] -> //; rewrite andbT negbK => /eqP ->.
Qed.

Lemma comparable_ltNge x y : x >=< y -> (x < y) = ~~ (y <= x).
Proof.
move=> c_xy; apply/idP/idP => [/lt_geF/negP/negP//|].
by rewrite lt_neqAle eq_le; move: c_xy => /orP [] -> //; rewrite andbT.
Qed.

Lemma comparable_ltgtP x y : x >=< y ->
  comparer x y (y == x) (x == y) (x <= y) (y <= x) (x < y) (x > y).
Proof.
rewrite />=<%O !le_eqVlt [y == x]eq_sym.
have := (altP (x =P y), (boolP (x < y), boolP (y < x))).
move=> [[->//|neq_xy /=] [[] xy [] //=]] ; do ?by rewrite ?ltxx; constructor.
  by rewrite ltxx in xy.
by rewrite le_gtF // ltW.
Qed.

Lemma comparable_leP x y : x >=< y -> le_xor_gt x y (x <= y) (y < x).
Proof.
by move=> /comparable_ltgtP [->|xy|xy]; constructor => //; rewrite ltW.
Qed.

Lemma comparable_ltP x y : x >=< y -> lt_xor_ge x y (y <= x) (x < y).
Proof.
by move=> /comparable_ltgtP [->|xy|xy]; constructor => //; rewrite ltW.
Qed.

Lemma comparable_sym x y : (y >=< x) = (x >=< y).
Proof. by rewrite /comparable orbC. Qed.

Lemma comparablexx x : x >=< x.
Proof. by rewrite /comparable lexx. Qed.

Lemma incomparable_eqF x y : (x >< y) -> (x == y) = false.
Proof. by apply: contraNF => /eqP ->; rewrite comparablexx. Qed.

Lemma incomparable_leF x y : (x >< y) -> (x <= y) = false.
Proof. by apply: contraNF; rewrite /comparable => ->. Qed.

Lemma incomparable_ltF x y : (x >< y) -> (x < y) = false.
Proof. by rewrite lt_neqAle => /incomparable_leF ->; rewrite andbF. Qed.

Lemma comparableP x y : incomparer x y
  (y == x) (x == y) (x <= y) (y <= x) (x < y) (x > y)
  (y >=< x) (x >=< y).
Proof.
rewrite ![y >=< _]comparable_sym; have [c_xy|i_xy] := boolP (x >=< y).
  by case: (comparable_ltgtP c_xy) => ?; constructor.
by rewrite ?incomparable_eqF ?incomparable_leF ?incomparable_ltF //
           1?comparable_sym //; constructor.
Qed.

Lemma le_comparable (x y : T) : x <= y -> x >=< y.
Proof. by case: comparableP. Qed.

Lemma lt_comparable (x y : T) : x < y -> x >=< y.
Proof. by case: comparableP. Qed.

Lemma ge_comparable (x y : T) : y <= x -> x >=< y.
Proof. by case: comparableP. Qed.

Lemma gt_comparable (x y : T) : y < x -> x >=< y.
Proof. by case: comparableP. Qed.

Lemma leifP x y C : reflect (x <= y ?= iff C) (if C then x == y else x < y).
Proof.
rewrite /leif le_eqVlt; apply: (iffP idP)=> [|[]].
  by case: C => [/eqP->|lxy]; rewrite ?eqxx // lxy lt_eqF.
by move=> /orP[/eqP->|lxy] <-; rewrite ?eqxx // lt_eqF.
Qed.

Lemma leif_refl x C : reflect (x <= x ?= iff C) C.
Proof. by apply: (iffP idP) => [-> | <-] //; split; rewrite ?eqxx. Qed.

Lemma leif_trans x1 x2 x3 C12 C23 :
  x1 <= x2 ?= iff C12 -> x2 <= x3 ?= iff C23 -> x1 <= x3 ?= iff C12 && C23.
Proof.
move=> ltx12 ltx23; apply/leifP; rewrite -ltx12.
case eqx12: (x1 == x2).
  by rewrite (eqP eqx12) lt_neqAle !ltx23 andbT; case C23.
by rewrite (@lt_le_trans x2) ?ltx23 // lt_neqAle eqx12 ltx12.
Qed.

Lemma leif_le x y : x <= y -> x <= y ?= iff (x >= y).
Proof. by move=> lexy; split=> //; rewrite eq_le lexy. Qed.

Lemma leif_eq x y : x <= y -> x <= y ?= iff (x == y).
Proof. by []. Qed.

Lemma ge_leif x y C : x <= y ?= iff C -> (y <= x) = C.
Proof. by case=> le_xy; rewrite eq_le le_xy. Qed.

Lemma lt_leif x y C : x <= y ?= iff C -> (x < y) = ~~ C.
Proof. by move=> le_xy; rewrite lt_neqAle !le_xy andbT. Qed.

Lemma mono_in_leif (A : {pred T}) (f : T -> T) C :
   {in A &, {mono f : x y / x <= y}} ->
  {in A &, forall x y, (f x <= f y ?= iff C) = (x <= y ?= iff C)}.
Proof. by move=> mf x y Ax Ay; rewrite /leif !eq_le !mf. Qed.

Lemma mono_leif (f : T -> T) C :
    {mono f : x y / x <= y} ->
  forall x y, (f x <= f y ?= iff C) = (x <= y ?= iff C).
Proof. by move=> mf x y; rewrite /leif !eq_le !mf. Qed.

Lemma nmono_in_leif (A : {pred T}) (f : T -> T) C :
    {in A &, {mono f : x y /~ x <= y}} ->
  {in A &, forall x y, (f x <= f y ?= iff C) = (y <= x ?= iff C)}.
Proof. by move=> mf x y Ax Ay; rewrite /leif !eq_le !mf. Qed.

Lemma nmono_leif (f : T -> T) C :
    {mono f : x y /~ x <= y} ->
  forall x y, (f x <= f y ?= iff C) = (y <= x ?= iff C).
Proof. by move=> mf x y; rewrite /leif !eq_le !mf. Qed.

End POrderTheory.
Section POrderMonotonyTheory.

Context {disp disp' : unit}.
Context {T : porderType disp} {T' : porderType disp'}.
Implicit Types (m n p : nat) (x y z : T) (u v w : T').
Variables (D D' : {pred T}) (f : T -> T').

Hint Resolve lexx lt_neqAle (@le_anti _ T) (@le_anti _ T') lt_def : core.

Let ge_antiT : antisymmetric (>=%O : rel T).
Proof. by move=> ? ? /le_anti. Qed.

Lemma ltW_homo : {homo f : x y / x < y} -> {homo f : x y / x <= y}.
Proof. exact: homoW. Qed.

Lemma ltW_nhomo : {homo f : x y /~ x < y} -> {homo f : x y /~ x <= y}.
Proof. exact: homoW. Qed.

Lemma inj_homo_lt :
  injective f -> {homo f : x y / x <= y} -> {homo f : x y / x < y}.
Proof. exact: inj_homo. Qed.

Lemma inj_nhomo_lt :
  injective f -> {homo f : x y /~ x <= y} -> {homo f : x y /~ x < y}.
Proof. exact: inj_homo. Qed.

Lemma inc_inj : {mono f : x y / x <= y} -> injective f.
Proof. exact: mono_inj. Qed.

Lemma dec_inj : {mono f : x y /~ x <= y} -> injective f.
Proof. exact: mono_inj. Qed.

Lemma leW_mono : {mono f : x y / x <= y} -> {mono f : x y / x < y}.
Proof. exact: anti_mono. Qed.

Lemma leW_nmono : {mono f : x y /~ x <= y} -> {mono f : x y /~ x < y}.
Proof. exact: anti_mono. Qed.

(* Monotony in D D' *)
Lemma ltW_homo_in :
  {in D & D', {homo f : x y / x < y}} -> {in D & D', {homo f : x y / x <= y}}.
Proof. exact: homoW_in. Qed.

Lemma ltW_nhomo_in :
  {in D & D', {homo f : x y /~ x < y}} -> {in D & D', {homo f : x y /~ x <= y}}.
Proof. exact: homoW_in. Qed.

Lemma inj_homo_lt_in :
    {in D & D', injective f} ->  {in D & D', {homo f : x y / x <= y}} ->
  {in D & D', {homo f : x y / x < y}}.
Proof. exact: inj_homo_in. Qed.

Lemma inj_nhomo_lt_in :
    {in D & D', injective f} -> {in D & D', {homo f : x y /~ x <= y}} ->
  {in D & D', {homo f : x y /~ x < y}}.
Proof. exact: inj_homo_in. Qed.

Lemma inc_inj_in : {in D &, {mono f : x y / x <= y}} ->
   {in D &, injective f}.
Proof. exact: mono_inj_in. Qed.

Lemma dec_inj_in :
  {in D &, {mono f : x y /~ x <= y}} -> {in D &, injective f}.
Proof. exact: mono_inj_in. Qed.

Lemma leW_mono_in :
  {in D &, {mono f : x y / x <= y}} -> {in D &, {mono f : x y / x < y}}.
Proof. exact: anti_mono_in. Qed.

Lemma leW_nmono_in :
  {in D &, {mono f : x y /~ x <= y}} -> {in D &, {mono f : x y /~ x < y}}.
Proof. exact: anti_mono_in. Qed.

End POrderMonotonyTheory.

End POrderTheory.

Hint Resolve lexx le_refl ltxx lt_irreflexive ltW lt_eqF : core.

Arguments leifP {disp T x y C}.
Arguments leif_refl {disp T x C}.
Arguments mono_in_leif [disp T A f C].
Arguments nmono_in_leif [disp T A f C].
Arguments mono_leif [disp T f C].
Arguments nmono_leif [disp T f C].

Module Import ConversePOrder.
Section ConversePOrder.
Canonical converse_eqType (T : eqType) := EqType T [eqMixin of T^c].
Canonical converse_choiceType (T : choiceType) := [choiceType of T^c].

Context {disp : unit}.
Local Notation porderType := (porderType disp).
Variable T : porderType.

Definition converse_le (x y : T) := (y <= x).
Definition converse_lt (x y : T) := (y < x).

Lemma converse_lt_def (x y : T) :
  converse_lt x y = (y != x) && (converse_le x y).
Proof. by apply: lt_neqAle. Qed.

Fact converse_le_anti : antisymmetric converse_le.
Proof. by move=> x y /andP [xy yx]; apply/le_anti/andP; split. Qed.

Definition converse_porderMixin :=
  POrderMixin converse_lt_def (lexx : reflexive converse_le) converse_le_anti
             (fun y z x zy yx => @le_trans _ _ y x z yx zy).
Canonical converse_porderType :=
  POrderType (converse_display disp) (T^c) converse_porderMixin.

End ConversePOrder.
End ConversePOrder.

Module Import ConverseLattice.
Section ConverseLattice.
Context {disp : unit}.
Local Notation latticeType := (latticeType disp).

Variable L : latticeType.
Implicit Types (x y : L).

Lemma meetC : commutative (@meet _ L). Proof. by case: L => [?[? ?[]]]. Qed.
Lemma joinC : commutative (@join _ L). Proof. by case: L => [?[? ?[]]]. Qed.

Lemma meetA : associative (@meet _ L). Proof. by case: L => [?[? ?[]]]. Qed.
Lemma joinA : associative (@join _ L). Proof. by case: L => [?[? ?[]]]. Qed.

Lemma joinKI y x : x `&` (x `|` y) = x.
Proof. by case: L x y => [?[? ?[]]]. Qed.
Lemma meetKU y x : x `|` (x `&` y) = x.
Proof. by case: L x y => [?[? ?[]]]. Qed.

Lemma joinKIC y x : x `&` (y `|` x) = x. Proof. by rewrite joinC joinKI. Qed.
Lemma meetKUC y x : x `|` (y `&` x) = x. Proof. by rewrite meetC meetKU. Qed.

Lemma meetUK x y : (x `&` y) `|` y = y.
Proof. by rewrite joinC meetC meetKU. Qed.
Lemma joinIK x y : (x `|` y) `&` y = y.
Proof. by rewrite joinC meetC joinKI. Qed.

Lemma meetUKC x y : (y `&` x) `|` y = y. Proof. by rewrite meetC meetUK. Qed.
Lemma joinIKC x y : (y `|` x) `&` y = y. Proof. by rewrite joinC joinIK. Qed.

Lemma leEmeet x y : (x <= y) = (x `&` y == x).
Proof. by case: L x y => [?[? ?[]]]. Qed.

Lemma leEjoin x y : (x <= y) = (x `|` y == y).
Proof. by rewrite leEmeet; apply/eqP/eqP => <-; rewrite (joinKI, meetUK). Qed.

Lemma meetUl : left_distributive (@meet _ L) (@join _ L).
Proof. by case: L => [?[? ?[]]]. Qed.

Lemma meetUr : right_distributive (@meet _ L) (@join _ L).
Proof. by move=> x y z; rewrite meetC meetUl ![_ `&` x]meetC. Qed.

Lemma joinIl : left_distributive (@join _ L) (@meet _ L).
Proof. by move=> x y z; rewrite meetUr joinIK meetUl -joinA meetUKC. Qed.

Fact converse_leEmeet (x y : L^c) : (x <= y) = (x `|` y == x).
Proof. by rewrite [LHS]leEjoin joinC. Qed.

Definition converse_latticeMixin :=
   @LatticeMixin _ [porderType of L^c] _ _ joinC meetC
  joinA meetA meetKU joinKI converse_leEmeet joinIl.
Canonical converse_latticeType := LatticeType L^c converse_latticeMixin.
End ConverseLattice.
End ConverseLattice.

Module Import LatticeTheoryMeet.
Section LatticeTheoryMeet.
Context {disp : unit}.
Local Notation latticeType := (latticeType disp).
Context {L : latticeType}.
Implicit Types (x y : L).

(* lattice theory *)
Lemma meetAC : right_commutative (@meet _ L).
Proof. by move=> x y z; rewrite -!meetA [X in _ `&` X]meetC. Qed.
Lemma meetCA : left_commutative (@meet _ L).
Proof. by move=> x y z; rewrite !meetA [X in X `&` _]meetC. Qed.
Lemma meetACA : interchange (@meet _ L) (@meet _ L).
Proof. by move=> x y z t; rewrite !meetA [X in X `&` _]meetAC. Qed.

Lemma meetxx x : x `&` x = x.
Proof. by rewrite -[X in _ `&` X](meetKU x) joinKI. Qed.

Lemma meetKI y x : x `&` (x `&` y) = x `&` y.
Proof. by rewrite meetA meetxx. Qed.
Lemma meetIK y x : (x `&` y) `&` y = x `&` y.
Proof. by rewrite -meetA meetxx. Qed.
Lemma meetKIC y x : x `&` (y `&` x) = x `&` y.
Proof. by rewrite meetC meetIK meetC. Qed.
Lemma meetIKC y x : y `&` x `&` y = x `&` y.
Proof. by rewrite meetAC meetC meetxx. Qed.

(* interaction with order *)

Lemma lexI x y z : (x <= y `&` z) = (x <= y) && (x <= z).
Proof.
rewrite !leEmeet; apply/idP/idP => [/eqP<-|/andP[/eqP<- /eqP<-]].
  by rewrite meetA meetIK eqxx -meetA meetACA meetxx meetAC eqxx.
by rewrite -[X in X `&` _]meetA meetIK meetA.
Qed.

Lemma leIxl x y z : y <= x -> y `&` z <= x.
Proof. by rewrite !leEmeet meetAC => /eqP ->. Qed.

Lemma leIxr x y z : z <= x -> y `&` z <= x.
Proof. by rewrite !leEmeet -meetA => /eqP ->. Qed.

Lemma leIx2 x y z : (y <= x) || (z <= x) -> y `&` z <= x.
Proof. by case/orP => [/leIxl|/leIxr]. Qed.

Lemma leIr x y : y `&` x <= x.
Proof. by rewrite leIx2 ?lexx ?orbT. Qed.

Lemma leIl x y : x `&` y <= x.
Proof. by rewrite leIx2 ?lexx ?orbT. Qed.

Lemma meet_idPl {x y} : reflect (x `&` y = x) (x <= y).
Proof. by rewrite leEmeet; apply/eqP. Qed.
Lemma meet_idPr {x y} : reflect (y `&` x = x) (x <= y).
Proof. by rewrite meetC; apply/meet_idPl. Qed.

Lemma leIidl x y : (x <= x `&` y) = (x <= y).
Proof. by rewrite !leEmeet meetKI. Qed.
Lemma leIidr x y : (x <= y `&` x) = (x <= y).
Proof. by rewrite !leEmeet meetKIC. Qed.

Lemma eq_meetl x y : (x `&` y == x) = (x <= y).
Proof. by apply/esym/leEmeet. Qed.

Lemma eq_meetr x y : (x `&` y == y) = (y <= x).
Proof. by rewrite meetC eq_meetl. Qed.

Lemma leI2 x y z t : x <= z -> y <= t -> x `&` y <= z `&` t.
Proof. by move=> xz yt; rewrite lexI !leIx2 ?xz ?yt ?orbT //. Qed.

End LatticeTheoryMeet.
End LatticeTheoryMeet.

Module Import LatticeTheoryJoin.
Section LatticeTheoryJoin.
Import LatticeDef.
Context {disp : unit}.
Local Notation latticeType := (latticeType disp).
Context {L : latticeType}.
Implicit Types (x y : L).

(* lattice theory *)
Lemma joinAC : right_commutative (@join _ L).
Proof. exact: (@meetAC _ [latticeType of L^c]). Qed.
Lemma joinCA : left_commutative (@join _ L).
Proof. exact: (@meetCA _ [latticeType of L^c]). Qed.
Lemma joinACA : interchange (@join _ L) (@join _ L).
Proof. exact: (@meetACA _ [latticeType of L^c]). Qed.

Lemma joinxx x : x `|` x = x.
Proof. exact: (@meetxx _ [latticeType of L^c]). Qed.

Lemma joinKU y x : x `|` (x `|` y) = x `|` y.
Proof. exact: (@meetKI _ [latticeType of L^c]). Qed.
Lemma joinUK y x : (x `|` y) `|` y = x `|` y.
Proof. exact: (@meetIK _ [latticeType of L^c]). Qed.
Lemma joinKUC y x : x `|` (y `|` x) = x `|` y.
Proof. exact: (@meetKIC _ [latticeType of L^c]). Qed.
Lemma joinUKC y x : y `|` x `|` y = x `|` y.
Proof. exact: (@meetIKC _ [latticeType of L^c]). Qed.

(* interaction with order *)
Lemma leUx x y z : (x `|` y <= z) = (x <= z) && (y <= z).
Proof. exact: (@lexI _ [latticeType of L^c]). Qed.
Lemma lexUl x y z : x <= y -> x <= y `|` z.
Proof. exact: (@leIxl _ [latticeType of L^c]). Qed.
Lemma lexUr x y z : x <= z -> x <= y `|` z.
Proof. exact: (@leIxr _ [latticeType of L^c]). Qed.
Lemma lexU2 x y z : (x <= y) || (x <= z) -> x <= y `|` z.
Proof. exact: (@leIx2 _ [latticeType of L^c]). Qed.

Lemma leUr x y : x <= y `|` x.
Proof. exact: (@leIr _ [latticeType of L^c]). Qed.
Lemma leUl x y : x <= x `|` y.
Proof. exact: (@leIl _ [latticeType of L^c]). Qed.

Lemma join_idPl {x y} : reflect (x `|` y = y) (x <= y).
Proof. exact: (@meet_idPr _ [latticeType of L^c]). Qed.
Lemma join_idPr {x y} : reflect (y `|` x = y) (x <= y).
Proof. exact: (@meet_idPl _ [latticeType of L^c]). Qed.

Lemma leUidl x y : (x `|` y <= y) = (x <= y).
Proof. exact: (@leIidr _ [latticeType of L^c]). Qed.
Lemma leUidr x y : (y `|` x <= y) = (x <= y).
Proof. exact: (@leIidl _ [latticeType of L^c]). Qed.

Lemma eq_joinl x y : (x `|` y == x) = (y <= x).
Proof. exact: (@eq_meetl _ [latticeType of L^c]). Qed.
Lemma eq_joinr x y : (x `|` y == y) = (x <= y).
Proof. exact: (@eq_meetr _ [latticeType of L^c]). Qed.

Lemma leU2 x y z t : x <= z -> y <= t -> x `|` y <= z `|` t.
Proof. exact: (@leI2 _ [latticeType of L^c]). Qed.

(* Distributive lattice theory *)
Lemma joinIr : right_distributive (@join _ L) (@meet _ L).
Proof. exact: (@meetUr _ [latticeType of L^c]). Qed.

Lemma lcomparableP x y : incomparer x y
  (y == x) (x == y) (x <= y) (y <= x) (x < y) (x > y)
  (y >=< x) (x >=< y) (y `&` x) (x `&` y) (y `|` x) (x `|` y).
Proof.
by case: (comparableP x) => [-> | hxy | hxy | hxy]; do 1?have hxy' := ltW hxy;
  rewrite ?(meetxx, joinxx, meetC y, joinC y)
          ?(meet_idPl hxy', meet_idPr hxy', join_idPl hxy', join_idPr hxy');
  constructor.
Qed.

Lemma lcomparable_ltgtP x y : x >=< y ->
  comparer x y (y == x) (x == y) (x <= y) (y <= x) (x < y) (x > y)
           (y `&` x) (x `&` y) (y `|` x) (x `|` y).
Proof. by case: (lcomparableP x) => // *; constructor. Qed.

Lemma lcomparable_leP x y : x >=< y ->
  le_xor_gt x y (x <= y) (y < x) (y `&` x) (x `&` y) (y `|` x) (x `|` y).
Proof. by move/lcomparable_ltgtP => [->|/ltW xy|xy]; constructor => //. Qed.

Lemma lcomparable_ltP x y : x >=< y ->
  lt_xor_ge x y (y <= x) (x < y) (y `&` x) (x `&` y) (y `|` x) (x `|` y).
Proof. by move=> /lcomparable_ltgtP [->|xy|/ltW xy]; constructor => //. Qed.

End LatticeTheoryJoin.
End LatticeTheoryJoin.

Module Import TotalTheory.
Section TotalTheory.
Context {disp : unit}.
Local Notation orderType := (orderType disp).
Context {T : orderType}.
Implicit Types (x y z t : T).

Lemma le_total : total (<=%O : rel T). Proof. by case: T => [? [?]]. Qed.
Hint Resolve le_total : core.

Lemma ge_total : total (>=%O : rel T).
Proof. by move=> ? ?; apply: le_total. Qed.
Hint Resolve ge_total : core.

Lemma comparableT x y : x >=< y. Proof. exact: le_total. Qed.
Hint Resolve comparableT : core.

Lemma sort_le_sorted (s : seq T) : sorted <=%O (sort <=%O s).
Proof. exact: sort_sorted. Qed.

Lemma sort_lt_sorted (s : seq T) : sorted lt (sort le s) = uniq s.
Proof. by rewrite lt_sorted_uniq_le sort_uniq sort_le_sorted andbT. Qed.

Lemma sort_le_id (s : seq T) : sorted le s -> sort le s = s.
Proof.
by move=> ss; apply: eq_sorted_le; rewrite ?sort_le_sorted // perm_sort.
Qed.

Lemma leNgt x y : (x <= y) = ~~ (y < x). Proof. exact: comparable_leNgt. Qed.

Lemma ltNge x y : (x < y) = ~~ (y <= x). Proof. exact: comparable_ltNge. Qed.

Lemma wlog_le P :
     (forall x y, P y x -> P x y) -> (forall x y, x <= y -> P x y) ->
   forall x y, P x y.
Proof.
move=> sP hP x y; case hxy: (x <= y); last apply/sP; apply/hP => //.
by move/negbT: hxy; rewrite -ltNge; apply/ltW.
Qed.

Lemma wlog_lt P :
    (forall x, P x x) ->
    (forall x y, (P y x -> P x y)) -> (forall x y, x < y -> P x y) ->
  forall x y, P x y.
Proof.
move=> rP sP hP x y; case hxy: (x < y); first by apply/hP.
case hxy': (x == y); first by move/eqP: hxy' => <-; apply: rP.
by apply/sP/hP; rewrite lt_def leNgt hxy hxy'.
Qed.

Definition ltgtP x y := LatticeTheoryJoin.lcomparable_ltgtP (comparableT x y).
Definition leP x y := LatticeTheoryJoin.lcomparable_leP (comparableT x y).
Definition ltP x y := LatticeTheoryJoin.lcomparable_ltP (comparableT x y).

Lemma neq_lt x y : (x != y) = (x < y) || (y < x). Proof. by case: ltgtP. Qed.

Lemma lt_total x y : x != y -> (x < y) || (y < x). Proof. by case: ltgtP. Qed.

Lemma eq_leLR x y z t :
  (x <= y -> z <= t) -> (y < x -> t < z) -> (x <= y) = (z <= t).
Proof. by move=> *; apply/idP/idP; rewrite // !leNgt; apply: contra. Qed.

Lemma eq_leRL x y z t :
  (x <= y -> z <= t) -> (y < x -> t < z) -> (z <= t) = (x <= y).
Proof. by move=> *; symmetry; apply: eq_leLR. Qed.

Lemma eq_ltLR x y z t :
  (x < y -> z < t) -> (y <= x -> t <= z) -> (x < y) = (z < t).
Proof. by move=> *; rewrite !ltNge; congr negb; apply: eq_leLR. Qed.

Lemma eq_ltRL x y z t :
  (x < y -> z < t) -> (y <= x -> t <= z) -> (z < t) = (x < y).
Proof. by move=> *; symmetry; apply: eq_ltLR. Qed.

(* interaction with lattice operations *)

Lemma leIx x y z : (meet y z <= x) = (y <= x) || (z <= x).
Proof.
by case: (leP y z) => hyz; case: leP => ?;
  rewrite ?(orbT, orbF) //=; apply/esym/negbTE;
  rewrite -ltNge ?(lt_le_trans _ hyz) ?(lt_trans _ hyz).
Qed.

Lemma lexU x y z : (x <= join y z) = (x <= y) || (x <= z).
Proof.
by case: (leP y z) => hyz; case: leP => ?;
  rewrite ?(orbT, orbF) //=; apply/esym/negbTE;
  rewrite -ltNge ?(le_lt_trans hyz) ?(lt_trans hyz).
Qed.

Lemma ltxI x y z : (x < meet y z) = (x < y) && (x < z).
Proof. by rewrite !ltNge leIx negb_or. Qed.

Lemma ltIx x y z : (meet y z < x) = (y < x) || (z < x).
Proof. by rewrite !ltNge lexI negb_and. Qed.

Lemma ltxU x y z : (x < join y z) = (x < y) || (x < z).
Proof. by rewrite !ltNge leUx negb_and. Qed.

Lemma ltUx x y z : (join y z < x) = (y < x) && (z < x).
Proof. by rewrite !ltNge lexU negb_or. Qed.

Definition ltexI := (@lexI _ T, ltxI).
Definition lteIx := (leIx, ltIx).
Definition ltexU := (lexU, ltxU).
Definition lteUx := (@leUx _ T, ltUx).

Section ArgExtremum.

Context (I : finType) (i0 : I) (P : {pred I}) (F : I -> T) (Pi0 : P i0).

Lemma arg_minP: extremum_spec <=%O P F (arg_min i0 P F).
Proof. by apply: extremumP => //; apply: le_trans. Qed.

Lemma arg_maxP: extremum_spec >=%O P F (arg_max i0 P F).
Proof. by apply: extremumP => //; [apply: ge_refl | apply: ge_trans]. Qed.

End ArgExtremum.

End TotalTheory.
Section TotalMonotonyTheory.

Context {disp : unit} {disp' : unit}.
Context {T : orderType disp} {T' : porderType disp'}.
Variables (D : {pred T}) (f : T -> T').
Implicit Types (x y z : T) (u v w : T').

Lemma le_mono : {homo f : x y / x < y} -> {mono f : x y / x <= y}.
Proof.
move=> mf x y; case: ltgtP; first (by move=> ->; apply/lexx); move/mf => fxy.
- by rewrite comparable_leNgt /comparable 1?(le_eqVlt (f y)) fxy ?orbT.
- by apply/ltW.
Qed.

Lemma le_nmono : {homo f : x y /~ x < y} -> {mono f : x y /~ x <= y}.
Proof.
move=> mf x y; case: ltgtP; first (by move=> ->; apply/lexx); move/mf => fxy.
- by rewrite comparable_leNgt /comparable 1?(le_eqVlt (f y)) fxy ?orbT.
- by apply/ltW.
Qed.

Lemma le_mono_in :
  {in D &, {homo f : x y / x < y}} -> {in D &, {mono f : x y / x <= y}}.
Proof.
move=> mf x y Dx Dy; case: ltgtP;
  first (by move=> ->; apply/lexx); move/mf => fxy.
- by rewrite comparable_leNgt /comparable 1?(le_eqVlt (f y)) fxy ?orbT.
- by apply/ltW/fxy.
Qed.

Lemma le_nmono_in :
  {in D &, {homo f : x y /~ x < y}} -> {in D &, {mono f : x y /~ x <= y}}.
Proof.
move=> mf x y Dx Dy; case: ltgtP;
  first (by move=> ->; apply/lexx); move/mf => fxy.
- by rewrite comparable_leNgt /comparable 1?(le_eqVlt (f y)) fxy ?orbT.
- by apply/ltW/fxy.
Qed.

End TotalMonotonyTheory.
End TotalTheory.

Module Import BLatticeTheory.
Section BLatticeTheory.
Context {disp : unit}.
Local Notation blatticeType := (blatticeType disp).
Context {L : blatticeType}.
Implicit Types (x y z : L).
Local Notation "0" := bottom.

(* Distributive lattice theory with 0 & 1*)
Lemma le0x x : 0 <= x. Proof. by case: L x => [?[? ?[]]]. Qed.
Hint Resolve le0x : core.

Lemma lex0 x : (x <= 0) = (x == 0).
Proof. by rewrite le_eqVlt (le_gtF (le0x _)) orbF. Qed.

Lemma ltx0 x : (x < 0) = false.
Proof. by rewrite lt_neqAle lex0 andNb. Qed.

Lemma lt0x x : (0 < x) = (x != 0).
Proof. by rewrite lt_neqAle le0x andbT eq_sym. Qed.

Lemma meet0x : left_zero 0 (@meet _ L).
Proof. by move=> x; apply/eqP; rewrite -leEmeet. Qed.

Lemma meetx0 : right_zero 0 (@meet _ L).
Proof. by move=> x; rewrite meetC meet0x. Qed.

Lemma join0x : left_id 0 (@join _ L).
Proof. by move=> x; apply/eqP; rewrite -leEjoin. Qed.

Lemma joinx0 : right_id 0 (@join _ L).
Proof. by move=> x; rewrite joinC join0x. Qed.

Lemma leU2l_le y t x z : x `&` t = 0 -> x `|` y <= z `|` t -> x <= z.
Proof.
by move=> xIt0 /(leI2 (lexx x)); rewrite joinKI meetUr xIt0 joinx0 leIidl.
Qed.

Lemma leU2r_le y t x z : x `&` t = 0 -> y `|` x <= t `|` z -> x <= z.
Proof. by rewrite joinC [_ `|` z]joinC => /leU2l_le H /H. Qed.

Lemma lexUl z x y : x `&` z = 0 -> (x <= y `|` z) = (x <= y).
Proof.
move=> xz0; apply/idP/idP=> xy; last by rewrite lexU2 ?xy.
by apply: (@leU2l_le x z); rewrite ?joinxx.
Qed.

Lemma lexUr z x y : x `&` z = 0 -> (x <= z `|` y) = (x <= y).
Proof. by move=> xz0; rewrite joinC; rewrite lexUl. Qed.

Lemma leU2E x y z t : x `&` t = 0 -> y `&` z = 0 ->
  (x `|` y <= z `|` t) = (x <= z) && (y <= t).
Proof.
move=> dxt dyz; apply/idP/andP; last by case=> ? ?; exact: leU2.
by move=> lexyzt; rewrite (leU2l_le _ lexyzt) // (leU2r_le _ lexyzt).
Qed.

Lemma join_eq0 x y : (x `|` y == 0) = (x == 0) && (y == 0).
Proof.
apply/idP/idP; last by move=> /andP [/eqP-> /eqP->]; rewrite joinx0.
by move=> /eqP xUy0; rewrite -!lex0 -!xUy0 ?leUl ?leUr.
Qed.

Variant eq0_xor_gt0 x : bool -> bool -> Set :=
    Eq0NotPOs : x = 0 -> eq0_xor_gt0 x true false
  | POsNotEq0 : 0 < x -> eq0_xor_gt0 x false true.

Lemma posxP x : eq0_xor_gt0 x (x == 0) (0 < x).
Proof. by rewrite lt0x; have [] := altP eqP; constructor; rewrite ?lt0x. Qed.

Canonical join_monoid := Monoid.Law (@joinA _ _) join0x joinx0.
Canonical join_comoid := Monoid.ComLaw (@joinC _ _).

Lemma join_sup (I : finType) (j : I) (P : {pred I}) (F : I -> L) :
   P j -> F j <= \join_(i | P i) F i.
Proof. by move=> Pj; rewrite (bigD1 j) //= lexU2 ?lexx. Qed.

Lemma join_min (I : finType) (j : I) (l : L) (P : {pred I}) (F : I -> L) :
   P j -> l <= F j -> l <= \join_(i | P i) F i.
Proof. by move=> Pj /le_trans -> //; rewrite join_sup. Qed.

Lemma joinsP (I : finType) (u : L) (P : {pred I}) (F : I -> L) :
   reflect (forall i : I, P i -> F i <= u) (\join_(i | P i) F i <= u).
Proof.
have -> : \join_(i | P i) F i <= u = (\big[andb/true]_(i | P i) (F i <= u)).
  by elim/big_rec2: _ => [|i y b Pi <-]; rewrite ?le0x ?leUx.
rewrite big_all_cond; apply: (iffP allP) => /= H i;
have := H i _; rewrite mem_index_enum; last by move/implyP->.
by move=> /(_ isT) /implyP.
Qed.

Lemma le_joins (I : finType) (A B : {set I}) (F : I -> L) :
   A \subset B -> \join_(i in A) F i <= \join_(i in B) F i.
Proof.
move=> AsubB; rewrite -(setID B A).
rewrite [X in _ <= X](eq_bigl [predU B :&: A & B :\: A]); last first.
  by move=> i; rewrite !inE.
rewrite bigU //=; last by rewrite -setI_eq0 setDE setIACA setICr setI0.
by rewrite lexU2 // (setIidPr _) // lexx.
Qed.

Lemma joins_setU (I : finType) (A B : {set I}) (F : I -> L) :
   \join_(i in (A :|: B)) F i = \join_(i in A) F i `|` \join_(i in B) F i.
Proof.
apply/eqP; rewrite eq_le leUx !le_joins ?subsetUl ?subsetUr ?andbT //.
apply/joinsP => i; rewrite inE; move=> /orP.
by case=> ?; rewrite lexU2 //; [rewrite join_sup|rewrite orbC join_sup].
Qed.

Lemma join_seq (I : finType) (r : seq I) (F : I -> L) :
   \join_(i <- r) F i = \join_(i in r) F i.
Proof.
rewrite [RHS](eq_bigl (mem [set i | i \in r])); last by move=> i; rewrite !inE.
elim: r => [|i r ihr]; first by rewrite big_nil big1 // => i; rewrite ?inE.
rewrite big_cons {}ihr; apply/eqP; rewrite eq_le set_cons.
rewrite leUx join_sup ?inE ?eqxx // le_joins //= ?subsetUr //.
apply/joinsP => j; rewrite !inE => /predU1P [->|jr]; rewrite ?lexU2 ?lexx //.
by rewrite join_sup ?orbT ?inE.
Qed.

Lemma joins_disjoint (I : finType) (d : L) (P : {pred I}) (F : I -> L) :
   (forall i : I, P i -> d `&` F i = 0) -> d `&` \join_(i | P i) F i = 0.
Proof.
move=> d_Fi_disj; have : \big[andb/true]_(i | P i) (d `&` F i == 0).
  rewrite big_all_cond; apply/allP => i _ /=.
  by apply/implyP => /d_Fi_disj ->.
elim/big_rec2: _ => [|i y]; first by rewrite meetx0.
case; rewrite (andbF, andbT) // => Pi /(_ isT) dy /eqP dFi.
by rewrite meetUr dy dFi joinxx.
Qed.

End BLatticeTheory.
End BLatticeTheory.

Module Import ConverseTBLattice.
Section ConverseTBLattice.
Context {disp : unit}.
Local Notation tblatticeType := (tblatticeType disp).
Context {L : tblatticeType}.

Lemma lex1 (x : L) : x <= top. Proof. by case: L x => [?[? ?[]]]. Qed.

Definition converse_blatticeMixin :=
  @BLatticeMixin _ [latticeType of L^c] top lex1.
Canonical converse_blatticeType := BLatticeType L^c converse_blatticeMixin.

Definition converse_tblatticeMixin :=
   @TBLatticeMixin _ [latticeType of L^c] (bottom : L) (@le0x _ L).
Canonical converse_tblatticeType := TBLatticeType L^c converse_tblatticeMixin.

End ConverseTBLattice.
End ConverseTBLattice.

Module Import ConverseTBLatticeSyntax.
Section ConverseTBLatticeSyntax.
Local Notation "0" := bottom.
Local Notation "1" := top.
Local Notation join := (@join (converse_display _) _).
Local Notation meet := (@meet (converse_display _) _).

Notation "\join^c_ ( i <- r | P ) F" :=
  (\big[join/0]_(i <- r | P%B) F%O) : order_scope.
Notation "\join^c_ ( i <- r ) F" :=
  (\big[join/0]_(i <- r) F%O) : order_scope.
Notation "\join^c_ ( i | P ) F" :=
  (\big[join/0]_(i | P%B) F%O) : order_scope.
Notation "\join^c_ i F" :=
  (\big[join/0]_i F%O) : order_scope.
Notation "\join^c_ ( i : I | P ) F" :=
  (\big[join/0]_(i : I | P%B) F%O) (only parsing) : order_scope.
Notation "\join^c_ ( i : I ) F" :=
  (\big[join/0]_(i : I) F%O) (only parsing) : order_scope.
Notation "\join^c_ ( m <= i < n | P ) F" :=
 (\big[join/0]_(m <= i < n | P%B) F%O) : order_scope.
Notation "\join^c_ ( m <= i < n ) F" :=
 (\big[join/0]_(m <= i < n) F%O) : order_scope.
Notation "\join^c_ ( i < n | P ) F" :=
 (\big[join/0]_(i < n | P%B) F%O) : order_scope.
Notation "\join^c_ ( i < n ) F" :=
 (\big[join/0]_(i < n) F%O) : order_scope.
Notation "\join^c_ ( i 'in' A | P ) F" :=
 (\big[join/0]_(i in A | P%B) F%O) : order_scope.
Notation "\join^c_ ( i 'in' A ) F" :=
 (\big[join/0]_(i in A) F%O) : order_scope.

Notation "\meet^c_ ( i <- r | P ) F" :=
  (\big[meet/1]_(i <- r | P%B) F%O) : order_scope.
Notation "\meet^c_ ( i <- r ) F" :=
  (\big[meet/1]_(i <- r) F%O) : order_scope.
Notation "\meet^c_ ( i | P ) F" :=
  (\big[meet/1]_(i | P%B) F%O) : order_scope.
Notation "\meet^c_ i F" :=
  (\big[meet/1]_i F%O) : order_scope.
Notation "\meet^c_ ( i : I | P ) F" :=
  (\big[meet/1]_(i : I | P%B) F%O) (only parsing) : order_scope.
Notation "\meet^c_ ( i : I ) F" :=
  (\big[meet/1]_(i : I) F%O) (only parsing) : order_scope.
Notation "\meet^c_ ( m <= i < n | P ) F" :=
 (\big[meet/1]_(m <= i < n | P%B) F%O) : order_scope.
Notation "\meet^c_ ( m <= i < n ) F" :=
 (\big[meet/1]_(m <= i < n) F%O) : order_scope.
Notation "\meet^c_ ( i < n | P ) F" :=
 (\big[meet/1]_(i < n | P%B) F%O) : order_scope.
Notation "\meet^c_ ( i < n ) F" :=
 (\big[meet/1]_(i < n) F%O) : order_scope.
Notation "\meet^c_ ( i 'in' A | P ) F" :=
 (\big[meet/1]_(i in A | P%B) F%O) : order_scope.
Notation "\meet^c_ ( i 'in' A ) F" :=
 (\big[meet/1]_(i in A) F%O) : order_scope.

End ConverseTBLatticeSyntax.
End ConverseTBLatticeSyntax.

Module Import TBLatticeTheory.
Section TBLatticeTheory.
Context {disp : unit}.
Local Notation tblatticeType := (tblatticeType disp).
Context {L : tblatticeType}.
Implicit Types (x y : L).

Local Notation "1" := top.

Hint Resolve le0x lex1 : core.

Lemma meetx1 : right_id 1 (@meet _ L).
Proof. exact: (@joinx0 _ [tblatticeType of L^c]). Qed.

Lemma meet1x : left_id 1 (@meet _ L).
Proof. exact: (@join0x _ [tblatticeType of L^c]). Qed.

Lemma joinx1 : right_zero 1 (@join _ L).
Proof. exact: (@meetx0 _ [tblatticeType of L^c]). Qed.

Lemma join1x : left_zero 1 (@join _ L).
Proof. exact: (@meet0x _ [tblatticeType of L^c]). Qed.

Lemma le1x x : (1 <= x) = (x == 1).
Proof. exact: (@lex0 _ [tblatticeType of L^c]). Qed.

Lemma leI2l_le y t x z : y `|` z = 1 -> x `&` y <= z `&` t -> x <= z.
Proof. rewrite joinC; exact: (@leU2l_le _ [tblatticeType of L^c]). Qed.

Lemma leI2r_le y t x z : y `|` z = 1 -> y `&` x <= t `&` z -> x <= z.
Proof. rewrite joinC; exact: (@leU2r_le _ [tblatticeType of L^c]). Qed.

Lemma lexIl z x y : z `|` y = 1 -> (x `&` z <= y) = (x <= y).
Proof. rewrite joinC; exact: (@lexUl _ [tblatticeType of L^c]). Qed.

Lemma lexIr z x y : z `|` y = 1 -> (z `&` x <= y) = (x <= y).
Proof. rewrite joinC; exact: (@lexUr _ [tblatticeType of L^c]). Qed.

Lemma leI2E x y z t : x `|` t = 1 -> y `|` z = 1 ->
  (x `&` y <= z `&` t) = (x <= z) && (y <= t).
Proof.
by move=> ? ?; apply: (@leU2E _ [tblatticeType of L^c]); rewrite meetC.
Qed.

Lemma meet_eq1 x y : (x `&` y == 1) = (x == 1) && (y == 1).
Proof. exact: (@join_eq0 _ [tblatticeType of L^c]). Qed.

Canonical meet_monoid := Monoid.Law (@meetA _ _) meet1x meetx1.
Canonical meet_comoid := Monoid.ComLaw (@meetC _ _).

Canonical meet_muloid := Monoid.MulLaw (@meet0x _ L) (@meetx0 _ _).
Canonical join_muloid := Monoid.MulLaw join1x joinx1.
Canonical join_addoid := Monoid.AddLaw (@meetUl _ L) (@meetUr _ _).
Canonical meet_addoid := Monoid.AddLaw (@joinIl _ L) (@joinIr _ _).

Lemma meets_inf (I : finType) (j : I) (P : {pred I}) (F : I -> L) :
   P j -> \meet_(i | P i) F i <= F j.
Proof. exact: (@join_sup _ [tblatticeType of L^c]). Qed.

Lemma meets_max (I : finType) (j : I) (u : L) (P : {pred I}) (F : I -> L) :
   P j -> F j <= u -> \meet_(i | P i) F i <= u.
Proof. exact: (@join_min _ [tblatticeType of L^c]). Qed.

Lemma meetsP (I : finType) (l : L) (P : {pred I}) (F : I -> L) :
   reflect (forall i : I, P i -> l <= F i) (l <= \meet_(i | P i) F i).
Proof. exact: (@joinsP _ [tblatticeType of L^c]). Qed.

Lemma le_meets (I : finType) (A B : {set I}) (F : I -> L) :
   A \subset B -> \meet_(i in B) F i <= \meet_(i in A) F i.
Proof. exact: (@le_joins _ [tblatticeType of L^c]). Qed.

Lemma meets_setU (I : finType) (A B : {set I}) (F : I -> L) :
   \meet_(i in (A :|: B)) F i = \meet_(i in A) F i `&` \meet_(i in B) F i.
Proof. exact: (@joins_setU _ [tblatticeType of L^c]). Qed.

Lemma meet_seq (I : finType) (r : seq I) (F : I -> L) :
   \meet_(i <- r) F i = \meet_(i in r) F i.
Proof. exact: (@join_seq _ [tblatticeType of L^c]). Qed.

Lemma meets_total (I : finType) (d : L) (P : {pred I}) (F : I -> L) :
   (forall i : I, P i -> d `|` F i = 1) -> d `|` \meet_(i | P i) F i = 1.
Proof. exact: (@joins_disjoint _ [tblatticeType of L^c]). Qed.

End TBLatticeTheory.
End TBLatticeTheory.

Module Import CBLatticeTheory.
Section CBLatticeTheory.
Context {disp : unit}.
Local Notation cblatticeType := (cblatticeType disp).
Context {L : cblatticeType}.
Implicit Types (x y z : L).
Local Notation "0" := bottom.

Lemma subKI x y : y `&` (x `\` y) = 0.
Proof. by case: L x y => ? [? ?[]]. Qed.

Lemma subIK x y : (x `\` y) `&` y = 0.
Proof. by rewrite meetC subKI. Qed.

Lemma meetIB z x y : (z `&` y) `&` (x `\` y) = 0.
Proof. by rewrite -meetA subKI meetx0. Qed.

Lemma meetBI z x y : (x `\` y) `&` (z `&` y) = 0.
Proof. by rewrite meetC meetIB. Qed.

Lemma joinIB y x : (x `&` y) `|` (x `\` y) = x.
Proof. by case: L x y => ? [? ?[]]. Qed.

Lemma joinBI y x : (x `\` y) `|` (x `&` y) = x.
Proof. by rewrite joinC joinIB. Qed.

Lemma joinIBC y x : (y `&` x) `|` (x `\` y) = x.
Proof. by rewrite meetC joinIB. Qed.

Lemma joinBIC y x : (x `\` y) `|` (y `&` x) = x.
Proof. by rewrite meetC joinBI. Qed.

Lemma leBx x y : x `\` y <= x.
Proof. by rewrite -{2}[x](joinIB y) lexU2 // lexx orbT. Qed.
Hint Resolve leBx : core.

Lemma subxx x : x `\` x = 0.
Proof. by have := subKI x x; rewrite (meet_idPr _). Qed.

Lemma leBl z x y : x <= y -> x `\` z <= y `\` z.
Proof.
rewrite -{1}[x](joinIB z) -{1}[y](joinIB z).
by rewrite leU2E ?meetIB ?meetBI // => /andP [].
Qed.

Lemma subKU y x : y `|` (x `\` y) = y `|` x.
Proof.
apply/eqP; rewrite eq_le leU2 //= leUx leUl.
by apply/meet_idPl; have := joinIB y x; rewrite joinIl (join_idPr _).
Qed.

Lemma subUK y x : (x `\` y) `|` y = x `|` y.
Proof. by rewrite joinC subKU joinC. Qed.

Lemma leBKU y x : y <= x -> y `|` (x `\` y) = x.
Proof. by move=> /join_idPl {2}<-; rewrite subKU. Qed.

Lemma leBUK y x : y <= x -> (x `\` y) `|` y = x.
Proof. by move=> leyx; rewrite joinC leBKU. Qed.

Lemma leBLR x y z : (x `\` y <= z) = (x <= y `|` z).
Proof.
apply/idP/idP; first by move=> /join_idPl <-; rewrite joinA subKU joinAC leUr.
by rewrite -{1}[x](joinIB y) => /(leU2r_le (subIK _ _)).
Qed.

Lemma subUx x y z : (x `|` y) `\` z = (x `\` z) `|` (y `\` z).
Proof.
apply/eqP; rewrite eq_le leUx !leBl ?leUr ?leUl ?andbT //.
by rewrite leBLR joinA subKU joinAC subKU joinAC -joinA leUr.
Qed.

Lemma sub_eq0 x y : (x `\` y == 0) = (x <= y).
Proof. by rewrite -lex0 leBLR joinx0. Qed.

Lemma joinxB x y z : x `|` (y `\` z) = ((x `|` y) `\` z) `|` (x `&` z).
Proof. by rewrite subUx joinAC joinBI. Qed.

Lemma joinBx x y z : (y `\` z) `|` x = ((y `|` x) `\` z) `|` (z `&` x).
Proof. by rewrite ![_ `|` x]joinC ![_ `&` x]meetC joinxB. Qed.

Lemma leBr z x y : x <= y -> z `\` y <= z `\` x.
Proof.
by move=> lexy; rewrite leBLR joinxB (meet_idPr _) ?leBUK ?leUr ?lexU2 ?lexy.
Qed.

Lemma leB2 x y z t : x <= z -> t <= y -> x `\` y <= z `\` t.
Proof. by move=> /(@leBl t) ? /(@leBr x) /le_trans ->. Qed.

Lemma meet_eq0E_sub z x y : x <= z -> (x `&` y == 0) = (x <= z `\` y).
Proof.
move=> xz; apply/idP/idP; last by move=> /meet_idPr <-; rewrite -meetA meetBI.
by move=> /eqP xIy_eq0; rewrite -[x](joinIB y) xIy_eq0 join0x leBl.
Qed.

Lemma leBRL x y z : (x <= z `\` y) = (x <= z) && (x `&` y == 0).
Proof.
apply/idP/idP => [xyz|]; first by rewrite (@meet_eq0E_sub z) // (le_trans xyz).
by move=> /andP [?]; rewrite -meet_eq0E_sub.
Qed.

Lemma eq_sub x y z : (x `\` y == z) = (z <= x <= y `|` z) && (z `&` y == 0).
Proof. by rewrite eq_le leBLR leBRL andbCA andbA. Qed.

Lemma subxU x y z : z `\` (x `|` y) = (z `\` x) `&` (z `\` y).
Proof.
apply/eqP; rewrite eq_le lexI !leBr ?leUl ?leUr //=.
rewrite leBRL leIx2 ?leBx //= meetUr meetAC subIK -meetA subIK.
by rewrite meet0x meetx0 joinx0.
Qed.

Lemma subx0 x : x `\` 0 = x.
Proof. by apply/eqP; rewrite eq_sub join0x meetx0 lexx eqxx. Qed.

Lemma sub0x x : 0 `\` x = 0.
Proof. by apply/eqP; rewrite eq_sub joinx0 meet0x lexx eqxx le0x. Qed.

Lemma subIx x y z : (x `&` y) `\` z = (x `\` z) `&` (y `\` z).
Proof.
apply/eqP; rewrite eq_sub joinIr ?leI2 ?subKU ?leUr ?leBx //=.
by rewrite -meetA subIK meetx0.
Qed.

Lemma meetxB x y z : x `&` (y `\` z) = (x `&` y) `\` z.
Proof. by rewrite subIx -{1}[x](joinBI z) meetUl meetIB joinx0. Qed.

Lemma meetBx x y z : (x `\` y) `&` z = (x `&` z) `\` y.
Proof. by rewrite ![_ `&` z]meetC meetxB. Qed.

Lemma subxI x y z : x `\` (y `&` z) = (x `\` y) `|` (x `\` z).
Proof.
apply/eqP; rewrite eq_sub leUx !leBx //= joinIl joinA joinCA !subKU.
rewrite joinCA -joinA [_ `|` x]joinC ![x `|` _](join_idPr _) //.
by rewrite -joinIl leUr /= meetUl {1}[_ `&` z]meetC ?meetBI joinx0.
Qed.

Lemma subBx x y z : (x `\` y) `\` z = x `\` (y `|` z).
Proof.
apply/eqP; rewrite eq_sub leBr ?leUl //=.
rewrite subxU joinIr subKU -joinIr (meet_idPl _) ?leUr //=.
by rewrite -meetA subIK meetx0.
Qed.

Lemma subxB x y z : x `\` (y `\` z) = (x `\` y) `|` (x `&` z).
Proof.
rewrite -[y in RHS](joinIB z) subxU joinIl subxI -joinA.
rewrite joinBI (join_idPl _) // joinBx [x `|` _](join_idPr _) ?leIl //.
by rewrite meetA meetAC subIK meet0x joinx0 (meet_idPr _).
Qed.

Lemma joinBK x y : (y `|` x) `\` x = (y `\` x).
Proof. by rewrite subUx subxx joinx0. Qed.

Lemma joinBKC x y : (x `|` y) `\` x = (y `\` x).
Proof. by rewrite subUx subxx join0x. Qed.

Lemma disj_le x y : x `&` y == 0 -> x <= y = (x == 0).
Proof.
have [->|x_neq0] := altP (x =P 0); first by rewrite le0x.
by apply: contraTF => lexy; rewrite (meet_idPl _).
Qed.

Lemma disj_leC x y : y `&` x == 0 -> x <= y = (x == 0).
Proof. by rewrite meetC => /disj_le. Qed.

Lemma disj_subl x y : x `&` y == 0 -> x `\` y = x.
Proof. by move=> dxy; apply/eqP; rewrite eq_sub dxy lexx leUr. Qed.

Lemma disj_subr x y : x `&` y == 0 -> y `\` x = y.
Proof. by rewrite meetC => /disj_subl. Qed.

Lemma lt0B x y : x < y -> 0 < y `\` x.
Proof.
by move=> ?; rewrite lt_leAnge leBRL leBLR le0x meet0x eqxx joinx0 /= lt_geF.
Qed.

End CBLatticeTheory.
End CBLatticeTheory.

Module Import CTBLatticeTheory.
Section CTBLatticeTheory.
Context {disp : unit}.
Local Notation ctblatticeType := (ctblatticeType disp).
Context {L : ctblatticeType}.
Implicit Types (x y z : L).
Local Notation "0" := bottom.
Local Notation "1" := top.

Lemma complE x : ~` x = 1 `\` x.
Proof. by case: L x => [?[? ? ? ?[]]]. Qed.

Lemma sub1x x : 1 `\` x = ~` x.
Proof. by rewrite complE. Qed.

Lemma subE x y : x `\` y = x `&` ~` y.
Proof. by rewrite complE meetxB meetx1. Qed.

Lemma complK : involutive (@compl _ L).
Proof. by move=> x; rewrite !complE subxB subxx meet1x join0x. Qed.

Lemma compl_inj : injective (@compl _ L).
Proof. exact/inv_inj/complK. Qed.

Lemma disj_leC x y : (x `&` y == 0) = (x <= ~` y).
Proof. by rewrite -sub_eq0 subE complK. Qed.

Lemma leC x y : (~` x <= ~` y) = (y <= x).
Proof.
gen have leC : x y / y <= x -> ~` x <= ~` y; last first.
  by apply/idP/idP=> /leC; rewrite ?complK.
by move=> leyx; rewrite !complE leBr.
Qed.

Lemma complU x y : ~` (x `|` y) = ~` x `&` ~` y.
Proof. by rewrite !complE subxU. Qed.

Lemma complI  x y : ~` (x `&` y) = ~` x `|` ~` y.
Proof. by rewrite !complE subxI. Qed.

Lemma joinxC  x :  x `|` ~` x = 1.
Proof. by rewrite complE subKU joinx1. Qed.

Lemma joinCx  x : ~` x `|` x = 1.
Proof. by rewrite joinC joinxC. Qed.

Lemma meetxC  x :  x `&` ~` x = 0.
Proof. by rewrite complE subKI. Qed.

Lemma meetCx  x : ~` x `&` x = 0.
Proof. by rewrite meetC meetxC. Qed.

Lemma compl1 : ~` 1 = 0 :> L.
Proof. by rewrite complE subxx. Qed.

Lemma compl0 : ~` 0 = 1 :> L.
Proof. by rewrite complE subx0. Qed.

Lemma complB x y : ~` (x `\` y) = ~` x `|` y.
Proof. by rewrite !complE subxB meet1x. Qed.

Lemma leBC x y : x `\` y <= ~` y.
Proof. by rewrite leBLR joinxC lex1. Qed.

Lemma leCx x y : (~` x <= y) = (~` y <= x).
Proof. by rewrite !complE !leBLR joinC. Qed.

Lemma lexC x y : (x <= ~` y) = (y <= ~` x).
Proof. by rewrite !complE !leBRL !lex1 meetC. Qed.

Lemma compl_joins (J : Type) (r : seq J) (P : {pred J}) (F : J -> L) :
   ~` (\join_(j <- r | P j) F j) = \meet_(j <- r | P j) ~` F j.
Proof. by elim/big_rec2: _=> [|i x y ? <-]; rewrite ?compl0 ?complU. Qed.

Lemma compl_meets (J : Type) (r : seq J) (P : {pred J}) (F : J -> L) :
   ~` (\meet_(j <- r | P j) F j) = \join_(j <- r | P j) ~` F j.
Proof. by elim/big_rec2: _=> [|i x y ? <-]; rewrite ?compl1 ?complI. Qed.

End CTBLatticeTheory.
End CTBLatticeTheory.

(*************)
(* FACTORIES *)
(*************)

Module TotalLatticeMixin.
Section TotalLatticeMixin.
Import POrderDef.
Variable (disp : unit) (T : porderType disp).
Definition of_ := total (<=%O : rel T).
Variable (m : of_).
Implicit Types (x y z : T).

Let comparableT x y : x >=< y := m x y.

Fact ltgtP x y :
  comparer x y (y == x) (x == y) (x <= y) (y <= x) (x < y) (x > y).
Proof. exact: comparable_ltgtP. Qed.

Fact leP x y : le_xor_gt x y (x <= y) (y < x).
Proof. exact: comparable_leP. Qed.

Fact ltP x y : lt_xor_ge x y (y <= x) (x < y).
Proof. exact: comparable_ltP. Qed.

Definition meet x y := if x <= y then x else y.
Definition join x y := if y <= x then x else y.

Fact meetC : commutative meet.
Proof. by move=> x y; rewrite /meet; have [] := ltgtP. Qed.

Fact joinC : commutative join.
Proof. by move=> x y; rewrite /join; have [] := ltgtP. Qed.

Fact meetA : associative meet.
Proof.
move=> x y z; rewrite /meet; case: (leP y z) => yz; case: (leP x y) => xy //=.
- by rewrite (le_trans xy).
- by rewrite yz.
by rewrite !lt_geF // (lt_trans yz).
Qed.

Fact joinA : associative join.
Proof.
move=> x y z; rewrite /join; case: (leP z y) => yz; case: (leP y x) => xy //=.
- by rewrite (le_trans yz).
- by rewrite yz.
by rewrite !lt_geF // (lt_trans xy).
Qed.

Fact joinKI y x : meet x (join x y) = x.
Proof. by rewrite /meet /join; case: (leP y x) => yx; rewrite ?lexx ?ltW. Qed.

Fact meetKU y x : join x (meet x y) = x.
Proof. by rewrite /meet /join; case: (leP x y) => yx; rewrite ?lexx ?ltW. Qed.

Fact leEmeet x y : (x <= y) = (meet x y == x).
Proof. by rewrite /meet; case: leP => ?; rewrite ?eqxx ?lt_eqF. Qed.

Fact meetUl : left_distributive meet join.
Proof.
move=> x y z; rewrite /meet /join.
case: (leP y z) => yz; case: (leP y x) => xy //=; first 1 last.
- by rewrite yz [x <= z](le_trans _ yz) ?[x <= y]ltW // lt_geF.
- by rewrite lt_geF ?lexx // (lt_le_trans yz).
- by rewrite lt_geF //; have [->|/lt_geF->|] := (ltgtP x z); rewrite ?lexx.
- by have [] := (leP x z); rewrite ?xy ?yz.
Qed.

Definition latticeMixin :=
  LatticeMixin meetC joinC meetA joinA joinKI meetKU leEmeet meetUl.

End TotalLatticeMixin.

Module Exports.
Notation totalLatticeMixin := of_.
Coercion latticeMixin : totalLatticeMixin >-> Order.Lattice.mixin_of.
End Exports.

End TotalLatticeMixin.
Import TotalLatticeMixin.Exports.

Module LePOrderMixin.
Section LePOrderMixin.
Variable (T : eqType).

Record of_ := Build {
  le : rel T;
  lt : rel T;
  le_refl  : reflexive le;
  le_anti  : antisymmetric le;
  le_trans : transitive le;
  lt_def   : forall x y, lt x y = (y != x) && le x y;
}.

Definition porderMixin (m : of_) : porderMixin T :=
   POrderMixin (@lt_def m) (@le_refl m) (@le_anti m) (@le_trans m).

End LePOrderMixin.

Module Exports.
Notation lePOrderMixin := of_.
Notation LePOrderMixin := Build.
Coercion porderMixin : lePOrderMixin >-> POrder.mixin_of.
End Exports.

End LePOrderMixin.
Import LePOrderMixin.Exports.

Module LtPOrderMixin.
Section LtPOrderMixin.
Variable (T : eqType).

Record of_ := Build {
  le : rel T;
  lt : rel T;
  lt_irr   : irreflexive lt;
  lt_trans : transitive lt;
  le_def   : forall x y, le x y = (x == y) || lt x y;
}.

Variable (m : of_).

Fact lt_asym x y : (lt m x y && lt m y x) = false.
Proof.
by apply/negP => /andP [] xy /(lt_trans xy); apply/negP; rewrite (lt_irr m x).
Qed.

Fact lt_def x y : lt m x y = (y != x) && le m x y.
Proof. by rewrite le_def eq_sym; case: eqP => //= <-; rewrite lt_irr. Qed.

Fact le_refl : reflexive (le m).
Proof. by move=> ?; rewrite le_def eqxx. Qed.

Fact le_anti : antisymmetric (le m).
Proof.
by move=> ? ?; rewrite !le_def eq_sym -orb_andr lt_asym orbF => /eqP.
Qed.

Fact le_trans : transitive (le m).
Proof.
by move=> y x z; rewrite !le_def => /predU1P [-> //|ltxy] /predU1P [<-|ltyz];
  rewrite ?ltxy ?(lt_trans ltxy ltyz) // ?orbT.
Qed.

Definition porderMixin : porderMixin T :=
   @POrderMixin _ (le m) (lt m) lt_def le_refl le_anti le_trans.

End LtPOrderMixin.

Module Exports.
Notation ltPOrderMixin := of_.
Notation LtPOrderMixin := Build.
Coercion porderMixin : ltPOrderMixin >-> POrder.mixin_of.
End Exports.

End LtPOrderMixin.
Import LtPOrderMixin.Exports.

Module MeetJoinMixin.
Section MeetJoinMixin.

Variable (disp : unit) (T : choiceType).

Record of_ (disp : unit) (T : choiceType) := Build {
  le : rel T;
  lt : rel T;
  meet : T -> T -> T;
  join : T -> T -> T;
  meetC : commutative meet;
  joinC : commutative join;
  meetA : associative meet;
  joinA : associative join;
  joinKI : forall y x : T, meet x (join x y) = x;
  meetKU : forall y x : T, join x (meet x y) = x;
  meetUl : left_distributive meet join;
  meetxx : idempotent meet;
  le_def : forall x y : T, le x y = (meet x y == x);
  lt_def : forall x y : T, lt x y = (y != x) && le x y;
}.


Variable (m : of_ disp T).

Fact le_refl : reflexive (le m).
Proof. by move=> x; rewrite le_def meetxx. Qed.

Fact le_anti : antisymmetric (le m).
Proof. by move=> x y; rewrite !le_def meetC => /andP [] /eqP {2}<- /eqP ->. Qed.

Fact le_trans : transitive (le m).
Proof.
move=> y x z; rewrite !le_def => /eqP lexy /eqP leyz; apply/eqP.
by rewrite -[in LHS]lexy -meetA leyz lexy.
Qed.

Definition porderMixin : lePOrderMixin T :=
  LePOrderMixin le_refl le_anti le_trans (lt_def m).

Definition latticeMixin : latticeMixin (POrderType disp T porderMixin) :=
  @LatticeMixin disp (POrderType disp T porderMixin) (meet m) (join m)
                (meetC m) (joinC m) (meetA m) (joinA m)
                (joinKI m) (meetKU m) (le_def m) (meetUl m).

End MeetJoinMixin.

Module Exports.
Notation meetJoinMixin := of_.
Notation MeetJoinMixin := Build.
Coercion porderMixin : meetJoinMixin >-> lePOrderMixin.
Coercion latticeMixin : meetJoinMixin >-> Lattice.mixin_of.
End Exports.

End MeetJoinMixin.
Import MeetJoinMixin.Exports.

Module LeOrderMixin.
Section LeOrderMixin.

Record of_ (disp : unit) (T : choiceType) := Build {
  le : rel T;
  lt : rel T;
  meet : T -> T -> T;
  join : T -> T -> T;
  le_anti : antisymmetric le;
  le_trans : transitive le;
  le_total : total le;
  lt_def : forall x y, lt x y = (y != x) && le x y;
  meet_def : forall x y, meet x y = if le x y then x else y;
  join_def : forall x y, join x y = if le y x then x else y;
}.

Variable (disp : unit) (T : choiceType) (m : of_ disp T).

Fact le_refl : reflexive (le m).
Proof. by move=> x; case: (le m x x) (le_total m x x). Qed.

Definition T_porderType : porderType disp :=
  POrderType
    disp T
    (LePOrderMixin le_refl (@le_anti _ _ m) (@le_trans _ _ m) (lt_def m)).
Definition T_latticeType : latticeType disp :=
  LatticeType T_porderType (le_total m : totalLatticeMixin T_porderType).

Implicit Types (x y z : T_latticeType).

Fact meetE x y : meet m x y = x `&` y. Proof. by rewrite meet_def. Qed.
Fact joinE x y : join m x y = x `|` y. Proof. by rewrite join_def. Qed.
Fact meetC : commutative (meet m).
Proof. by move=> *; rewrite !meetE meetC. Qed.
Fact joinC : commutative (join m).
Proof. by move=> *; rewrite !joinE joinC. Qed.
Fact meetA : associative (meet m).
Proof. by move=> *; rewrite !meetE meetA. Qed.
Fact joinA : associative (join m).
Proof. by move=> *; rewrite !joinE joinA. Qed.
Fact joinKI y x : meet m x (join m x y) = x.
Proof. by rewrite meetE joinE joinKI. Qed.
Fact meetKU y x : join m x (meet m x y) = x.
Proof. by rewrite meetE joinE meetKU. Qed.
Fact meetUl : left_distributive (meet m) (join m).
Proof. by move=> *; rewrite !meetE !joinE meetUl. Qed.
Fact meetxx : idempotent (meet m).
Proof. by move=> *; rewrite meetE meetxx. Qed.
Fact le_def x y : x <= y = (meet m x y == x).
Proof. by rewrite meetE (eq_meetl x y). Qed.

Definition latticeMixin : meetJoinMixin disp T :=
  @MeetJoinMixin
    _ _ (le m) (lt m) (meet m) (join m)
    meetC joinC meetA joinA joinKI meetKU meetUl meetxx le_def (lt_def m).

Definition totalMixin :
  Total.mixin_of (LatticeType (POrderType disp T latticeMixin) latticeMixin)
  := le_total m.

End LeOrderMixin.

Module Exports.
Notation leOrderMixin := of_.
Notation LeOrderMixin := Build.
Coercion latticeMixin : leOrderMixin >-> meetJoinMixin.
Coercion totalMixin : leOrderMixin >-> Total.mixin_of.
End Exports.

End LeOrderMixin.
Import LeOrderMixin.Exports.

Module LtOrderMixin.

Record of_ (disp : unit) (T : choiceType) := Build {
  le : rel T;
  lt : rel T;
  meet : T -> T -> T;
  join : T -> T -> T;
  lt_irr   : irreflexive lt;
  lt_trans : transitive lt;
  lt_total : forall x y, x != y -> lt x y || lt y x;
  le_def   : forall x y, le x y = (x == y) || lt x y;
  meet_def : forall x y, meet x y = if lt x y then x else y;
  join_def : forall x y, join x y = if lt y x then x else y;
}.

Section LtOrderMixin.

Variable (disp : unit) (T : choiceType) (m : of_ disp T).

Fact le_total : total (le m).
Proof.
by move=> x y; rewrite !le_def (eq_sym y); case: (altP eqP); [|apply: lt_total].
Qed.

Definition T_porderType : porderType disp :=
  POrderType disp T (LtPOrderMixin (lt_irr m) (@lt_trans _ _ m) (le_def m)).
Definition T_latticeType : latticeType disp :=
  LatticeType T_porderType (le_total : totalLatticeMixin T_porderType).

Implicit Types (x y z : T_latticeType).

Fact leP x y :
  le_xor_gt x y (x <= y) (y < x) (y `&` x) (x `&` y) (y `|` x) (x `|` y).
Proof. by apply/lcomparable_leP/le_total. Qed.
Fact meetE x y : meet m x y = x `&` y.
Proof. by rewrite meet_def (_ : lt m x y = (x < y)) //; case: (leP y). Qed.
Fact joinE x y : join m x y = x `|` y.
Proof. by rewrite join_def (_ : lt m y x = (y < x)) //; case: leP. Qed.
Fact meetC : commutative (meet m).
Proof. by move=> *; rewrite !meetE meetC. Qed.
Fact joinC : commutative (join m).
Proof. by move=> *; rewrite !joinE joinC. Qed.
Fact meetA : associative (meet m).
Proof. by move=> *; rewrite !meetE meetA. Qed.
Fact joinA : associative (join m).
Proof. by move=> *; rewrite !joinE joinA. Qed.
Fact joinKI y x : meet m x (join m x y) = x.
Proof. by rewrite meetE joinE joinKI. Qed.
Fact meetKU y x : join m x (meet m x y) = x.
Proof. by rewrite meetE joinE meetKU. Qed.
Fact meetUl : left_distributive (meet m) (join m).
Proof. by move=> *; rewrite !meetE !joinE meetUl. Qed.
Fact meetxx : idempotent (meet m).
Proof. by move=> *; rewrite meetE meetxx. Qed.
Fact le_def' x y : x <= y = (meet m x y == x).
Proof. by rewrite meetE (eq_meetl x y). Qed.

Definition latticeMixin : meetJoinMixin disp T :=
  @MeetJoinMixin
    _ _ (le m) (lt m) (meet m) (join m)
    meetC joinC meetA joinA joinKI meetKU meetUl meetxx
    le_def' (@lt_def _ T_latticeType).

Definition totalMixin :
  Total.mixin_of (LatticeType (POrderType disp T latticeMixin) latticeMixin)
  := le_total.

End LtOrderMixin.

Module Exports.
Notation ltOrderMixin := of_.
Notation LtOrderMixin := Build.
Coercion latticeMixin : ltOrderMixin >-> meetJoinMixin.
Coercion totalMixin : ltOrderMixin >-> Total.mixin_of.
End Exports.

End LtOrderMixin.
Import LtOrderMixin.Exports.

(*************)
(* INSTANCES *)
(*************)

Module NatOrder.
Section NatOrder.

Lemma minnE x y : minn x y = if (x <= y)%N then x else y.
Proof. by case: leqP => [/minn_idPl|/ltnW /minn_idPr]. Qed.

Lemma maxnE x y : maxn x y = if (y <= x)%N then x else y.
Proof. by case: leqP => [/maxn_idPl|/ltnW/maxn_idPr]. Qed.

Lemma ltn_def x y : (x < y)%N = (y != x) && (x <= y)%N.
Proof. by rewrite ltn_neqAle eq_sym. Qed.

Definition orderMixin :=
  LeOrderMixin total_display anti_leq leq_trans leq_total ltn_def minnE maxnE.

Canonical porderType := POrderType total_display nat orderMixin.
Canonical latticeType := LatticeType nat orderMixin.
Canonical orderType := OrderType nat orderMixin.
Canonical blatticeType := BLatticeType nat (BLatticeMixin leq0n).

Lemma leEnat: le = leq.
Proof. by []. Qed.

Lemma ltEnat (n m : nat): (n < m) = (n < m)%N.
Proof. by []. Qed.

End NatOrder.
Module Exports.
Canonical porderType.
Canonical latticeType.
Canonical orderType.
Canonical blatticeType.
Definition leEnat := leEnat.
Definition ltEnat := ltEnat.
End Exports.
End NatOrder.

Module ProductOrder.
Section ProductOrder.
Context {disp1 disp2 disp3 : unit}.

Section POrder.
Variable (T : porderType disp1) (T' : porderType disp2).

Definition le (x y : T * T') := (x.1 <= y.1) && (x.2 <= y.2).

Fact refl : reflexive le.
Proof. by move=> ?; rewrite /le !lexx. Qed.

Fact anti : antisymmetric le.
Proof.
case=> [? ?] [? ?].
by rewrite andbAC andbA andbAC -andbA => /= /andP [] /le_anti -> /le_anti ->.
Qed.

Fact trans : transitive le.
Proof.
rewrite /le => y x z /andP [] hxy ? /andP [] /(le_trans hxy) ->.
by apply: le_trans.
Qed.

Definition porderMixin := LePOrderMixin refl anti trans (rrefl _).
Canonical porderType := POrderType disp3 (T * T') porderMixin.

End POrder.

Section Lattice.
Variable (T : latticeType disp1) (T' : latticeType disp2).
Implicit Types (x y : T * T').

Definition meet x y := (x.1 `&` y.1, x.2 `&` y.2).
Definition join x y := (x.1 `|` y.1, x.2 `|` y.2).

Fact meetC : commutative meet.
Proof. by move=> ? ?; congr pair; rewrite meetC. Qed.

Fact joinC : commutative join.
Proof. by move=> ? ?; congr pair; rewrite joinC. Qed.

Fact meetA : associative meet.
Proof. by move=> ? ? ?; congr pair; rewrite meetA. Qed.

Fact joinA : associative join.
Proof. by move=> ? ? ?; congr pair; rewrite joinA. Qed.

Fact joinKI y x : meet x (join x y) = x.
Proof. by case: x => ? ?; congr pair; rewrite joinKI. Qed.

Fact meetKU y x : join x (meet x y) = x.
Proof. by case: x => ? ?; congr pair; rewrite meetKU. Qed.

Fact leEmeet x y : (x <= y) = (meet x y == x).
Proof. by rewrite /POrderDef.le /= /le /meet eqE /= -!leEmeet. Qed.

Fact meetUl : left_distributive meet join.
Proof. by move=> ? ? ?; congr pair; rewrite meetUl. Qed.

Definition latticeMixin :=
  Lattice.Mixin meetC joinC meetA joinA joinKI meetKU leEmeet meetUl.
Canonical latticeType := LatticeType (T * T') latticeMixin.

End Lattice.

Section BLattice.
Variable (T : blatticeType disp1) (T' : blatticeType disp2).

Fact le0x (x : T * T') : (0, 0) <= x.
Proof. by rewrite /POrderDef.le /= /le !le0x. Qed.

Canonical blatticeType := BLatticeType (T * T') (BLattice.Mixin le0x).

End BLattice.

Section TBLattice.
Variable (T : tblatticeType disp1) (T' : tblatticeType disp2).

Fact lex1 (x : T * T') : x <= (top, top).
Proof. by rewrite /POrderDef.le /= /le !lex1. Qed.

Canonical tblatticeType := TBLatticeType (T * T') (TBLattice.Mixin lex1).

End TBLattice.

Section CBLattice.
Variable (T : cblatticeType disp1) (T' : cblatticeType disp2).
Implicit Types (x y : T * T').

Definition sub x y := (x.1 `\` y.1, x.2 `\` y.2).

Lemma subKI x y : y `&` (sub x y) = 0.
Proof. by congr pair; rewrite subKI. Qed.

Lemma joinIB x y : (x `&` y) `|` (sub x y) = x.
Proof. by case: x => ? ?; congr pair; rewrite joinIB. Qed.

Definition cblatticeMixin := CBLattice.Mixin subKI joinIB.
Canonical cblatticeType := CBLatticeType (T * T') cblatticeMixin.

End CBLattice.

Section CTBLattice.
Variable (T : ctblatticeType disp1) (T' : ctblatticeType disp2).
Implicit Types (x y : T * T').

Definition compl x := (~` x.1, ~` x.2).

Lemma complE x : compl x = sub 1 x.
Proof. by congr pair; rewrite complE. Qed.

Definition ctblatticeMixin := CTBLattice.Mixin complE.
Canonical ctblatticeType := CTBLatticeType (T * T') ctblatticeMixin.
(* Let default_ctblatticeType := [default_ctblatticeType of T * T']. *)

End CTBLattice.

Canonical finPOrderType (T : finPOrderType disp1) (T' : finPOrderType disp2) :=
  [finPOrderType of T * T'].

Canonical finLatticeType
          (T : finLatticeType disp1) (T' : finLatticeType disp2) :=
  [finLatticeType of T * T'].

Canonical finClatticeType
          (T : finCLatticeType disp1) (T' : finCLatticeType disp2) :=
  [finCLatticeType of T * T'].

End ProductOrder.

Module Exports.
Canonical porderType.
Canonical latticeType.
Canonical blatticeType.
Canonical tblatticeType.
Canonical cblatticeType.
Canonical ctblatticeType.
Canonical finPOrderType.
Canonical finLatticeType.
Canonical finClatticeType.
End Exports.
End ProductOrder.

Module ProdLexOrder.
Section ProdLexOrder.
Context {disp1 disp2 disp3 : unit}.

Section POrder.
Variable (T : porderType disp1) (T' : porderType disp2).
Implicit Types (x y : T * T').

Definition le x y := (x.1 <= y.1) && ((x.1 >= y.1) ==> (x.2 <= y.2)).

Fact refl : reflexive le.
Proof. by move=> ?; by rewrite /le !lexx. Qed.

Fact anti : antisymmetric le.
Proof.
rewrite /le => -[x x'] [y y'] /=; case_eq (y <= x); case_eq (x <= y) => //.
by move=> //= hxy hyx /le_anti ->; move/andP/le_anti: (conj hxy hyx) => ->.
Qed.

Fact trans : transitive le.
Proof.
move=> y x z /andP [hxy /implyP hxy'] /andP [hyz /implyP hyz'].
rewrite /le (le_trans hxy) //=; apply/implyP => hzx.
by apply/le_trans/hxy'/(le_trans hyz): (hyz' (le_trans hzx hxy)).
Qed.

Definition porderMixin := LePOrderMixin refl anti trans (rrefl _).
Canonical porderType := POrderType disp3 (T * T') porderMixin.

End POrder.

Section Total.
Variable (T : orderType disp1) (T' : orderType disp2).
Implicit Types (x y : T * T').

Fact total : totalLatticeMixin [porderType of T * T'].
Proof.
move=> x y; rewrite /POrderDef.le /= /le; case: (ltgtP x.1 y.1) => _ //=.
by apply: le_total.
Qed.

Canonical latticeType := LatticeType (T * T') total.
Canonical totalType := LatticeType (T * T') total.

End Total.

End ProdLexOrder.

Module Exports.
Canonical porderType.
Canonical latticeType.
Canonical totalType.
End Exports.
End ProdLexOrder.

Module SeqProdOrder.
Section SeqProdOrder.
Context {disp disp' : unit}.

Section POrder.
Variable T : porderType disp.
Implicit Types s : seq T.

Fixpoint le s1 s2 :=
  if s1 is x1 :: s1' then
    if s2 is x2 :: s2' then (x1 <= x2) && le s1' s2' else false
  else
    true.

Fact refl : reflexive le.
Proof. by elim=> //= ? ? ?; rewrite !lexx. Qed.

Fact anti : antisymmetric le.
Proof.
elim=> [|? ? ih] [|? ?] //=.
by rewrite andbAC andbA andbAC -andbA => /andP [] /le_anti -> /ih ->.
Qed.

Fact trans : transitive le.
Proof.
elim=> [|y ys ih] [|x xs] [|z zs] //=.
by case/andP => [] xy xys /andP [] /(le_trans xy) -> /(ih _ _ xys).
Qed.

Definition porderMixin := LePOrderMixin refl anti trans (rrefl _).
Canonical porderType := POrderType disp' (seq T) porderMixin.

End POrder.

Section BLattice.
Variable T : latticeType disp.
Implicit Types s : seq T.

Fixpoint meet s1 s2 :=
  match s1, s2 with
    | x1 :: s1', x2 :: s2' => (x1 `&` x2) :: meet s1' s2'
    | _, _ => [::]
  end.

Fixpoint join s1 s2 :=
  match s1, s2 with
    | [::], _ => s2
    | _, [::] => s1
    | x1 :: s1', x2 :: s2' => (x1 `|` x2) :: join s1' s2'
  end.

Fact meetC : commutative meet.
Proof. by elim=> [|? ? ih] [|? ?] //=; rewrite meetC ih. Qed.

Fact joinC : commutative join.
Proof. by elim=> [|? ? ih] [|? ?] //=; rewrite joinC ih. Qed.

Fact meetA : associative meet.
Proof. by elim=> [|? ? ih] [|? ?] [|? ?] //=; rewrite meetA ih. Qed.

Fact joinA : associative join.
Proof. by elim=> [|? ? ih] [|? ?] [|? ?] //=; rewrite joinA ih. Qed.

Fact meetss s : meet s s = s.
Proof. by elim: s => [|? ? ih] //=; rewrite meetxx ih. Qed.

Fact joinKI y x : meet x (join x y) = x.
Proof.
elim: x y => [|? ? ih] [|? ?] //=; rewrite (meetxx, joinKI) ?ih //.
by congr cons; rewrite meetss.
Qed.

Fact meetKU y x : join x (meet x y) = x.
Proof. by elim: x y => [|? ? ih] [|? ?] //=; rewrite meetKU ih. Qed.

Fact leEmeet x y : (x <= y) = (meet x y == x).
Proof.
rewrite /POrderDef.le /=.
by elim: x y => [|? ? ih] [|? ?] //=; rewrite /eq_op /= leEmeet ih.
Qed.

Fact meetUl : left_distributive meet join.
Proof. by elim=> [|? ? ih] [|? ?] [|? ?] //=; rewrite meetUl ih. Qed.

Fact le0x s : [::] <= s.
Proof. by []. Qed.

Definition latticeMixin :=
  Lattice.Mixin meetC joinC meetA joinA joinKI meetKU leEmeet meetUl.
Canonical latticeType := LatticeType (seq T) latticeMixin.
Canonical blatticeType := BLatticeType (seq T) (BLattice.Mixin le0x).

End BLattice.

End SeqProdOrder.

Module Exports.
Canonical porderType.
Canonical latticeType.
Canonical blatticeType.
End Exports.
End SeqProdOrder.

Module SeqLexOrder.
Section SeqLexOrder.
Context {disp : unit}.

Section POrder.
Variable T : porderType disp.
Implicit Types s : seq T.

Fixpoint le s1 s2 :=
  if s1 is x1 :: s1' then
    if s2 is x2 :: s2' then
      (x1 < x2) || (x1 == x2) && le s1' s2'
    else
      false
  else
    true.

Fact refl: reflexive le.
Proof. by elim => [|x s ih] //=; rewrite eqxx ih orbT. Qed.

Fact anti: antisymmetric le.
Proof.
move=> x y /andP []; elim: x y => [|x sx ih] [|y sy] //=.
by case: comparableP => //= -> lesxsy /(ih _ lesxsy) ->.
Qed.

Fact trans: transitive le.
Proof.
elim=> [|y sy ih] [|x sx] [|z sz] //=.
case: (comparableP x y) => //=; case: (comparableP y z) => //=.
- by move=> -> -> lesxsy /(ih _ _ lesxsy) ->; rewrite eqxx orbT.
- by move=> ltyz ->; rewrite ltyz.
- by move=> -> ->.
- by move=> ltyz /lt_trans - /(_ _ ltyz) ->.
Qed.

Definition porderMixin := LePOrderMixin refl anti trans (rrefl _).
Canonical porderType := POrderType disp (seq T) porderMixin.

Fact lexi_le_head x sx y sy: x :: sx <= y :: sy -> x <= y.
Proof. by case/orP => [/ltW|/andP [/eqP-> _]]. Qed.

End POrder.

Section Total.
Variable T : orderType disp.
Implicit Types s : seq T.

Fact total : totalLatticeMixin [porderType of seq T].
Proof.
rewrite /totalLatticeMixin /= /POrderDef.le /=.
by elim=> [|? ? ih] [|? ?] //=;case: ltgtP => //=.
Qed.

Fact le0x s : [::] <= s.
Proof. by []. Qed.

Canonical latticeType := LatticeType (seq T) total.
Canonical blatticeType := BLatticeType (seq T) (BLattice.Mixin le0x).
Canonical totalType := LatticeType (seq T) total.

End Total.

End SeqLexOrder.

Module Exports.
Canonical porderType.
Canonical latticeType.
Canonical blatticeType.
Canonical totalType.
Definition lexi_le_head := @lexi_le_head.
Arguments lexi_le_head {disp}.
End Exports.
End SeqLexOrder.

Module Def.
Export POrderDef.
Export LatticeDef.
Export TotalDef.
Export BLatticeDef.
Export TBLatticeDef.
Export CBLatticeDef.
Export CTBLatticeDef.
End Def.

Module Syntax.
Export POSyntax.
Export TotalSyntax.
Export LatticeSyntax.
Export BLatticeSyntax.
Export TBLatticeSyntax.
Export CBLatticeSyntax.
Export CTBLatticeSyntax.
Export ConverseSyntax.
End Syntax.

Module LTheory.
Export POCoercions.
Export ConversePOrder.
Export POrderTheory.

Export ConverseLattice.
Export LatticeTheoryMeet.
Export LatticeTheoryJoin.
Export BLatticeTheory.
Export ConverseTBLattice.
Export TBLatticeTheory.
End LTheory.

Module CTheory.
Export LTheory CBLatticeTheory CTBLatticeTheory.
End CTheory.

Module TTheory.
Export LTheory TotalTheory.
End TTheory.

Module Theory.
Export CTheory TotalTheory.
End Theory.

End Order.

Export Order.POrder.Exports.
Export Order.FinPOrder.Exports.
Export Order.Lattice.Exports.
Export Order.BLattice.Exports.
Export Order.TBLattice.Exports.
Export Order.FinLattice.Exports.
Export Order.CBLattice.Exports.
Export Order.CTBLattice.Exports.
Export Order.FinCLattice.Exports.
Export Order.Total.Exports.
Export Order.FinTotal.Exports.

Export Order.TotalLatticeMixin.Exports.
Export Order.LePOrderMixin.Exports.
Export Order.LtPOrderMixin.Exports.
Export Order.MeetJoinMixin.Exports.
Export Order.LeOrderMixin.Exports.
Export Order.LtOrderMixin.Exports.
Export Order.NatOrder.Exports.

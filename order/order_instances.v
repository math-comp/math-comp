(* (c) Copyright 2006-2019 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import path div fintype tuple finfun bigop finset prime.
From mathcomp Require Import preorder porder lattice total_order.
From mathcomp Require Import complemented_lattice.

(******************************************************************************)
(*                 Instances of preorder and order structures                 *)
(*                                                                            *)
(* NB: See the header of order.v for general remarks about the preorder and   *)
(*     order structures in MathComp, and the files in this directory.         *)
(*                                                                            *)
(* We provide aliases for various types and their displays:                   *)
(*            natdvd := nat (associated with display dvd_display)             *)
(*                   == an alias for nat which is canonically ordered using   *)
(*                      divisibility predicate dvdn                           *)
(*                      Notation %|, %<|, gcd, lcm are used instead of        *)
(*                      <=, <, meet and join.                                 *)
(*              T^d  := dual T,                                               *)
(*                      where dual is a new definition for (fun T => T)       *)
(*                      (associated with dual_display d where d is a display) *)
(*                   == an alias for T, such that if T is canonically         *)
(*                      ordered, then T^d is canonically ordered with the     *)
(*                      dual order, and displayed with an extra ^d in the     *)
(*                      notation, i.e.,  <=^d, <^d, >=<^d, ><^d, `&`^d, `|`^d *)
(*                      are used and displayed instead of                     *)
(*                      <=, <, >=<, ><, `&`, `|`                              *)
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
(*     T *lexi[d] T' := T * T'                                                *)
(*                   == an alias for the cartesian product such that,         *)
(*                      if T and T' are canonically ordered,                  *)
(*                      then T *lexi[d] T' is canonically ordered in          *)
(*                      lexicographic order,                                  *)
(*                      i.e., (x1, x2) <= (y1, y2) =                          *)
(*                              (x1 <= y1) && ((x1 >= y1) ==> (x2 <= y2))     *)
(*                      and   (x1, x2) < (y1, y2) =                           *)
(*                              (x1 <= y1) && ((x1 >= y1) ==> (x2 < y2))      *)
(*                      and displayed in display d                            *)
(*           T *l T' := T *lexi[lexi_display d d'] T'                         *)
(*                      where d and d' are the displays of T and T',          *)
(*                      respectively, and lexi_display adds an extra ^l to    *)
(*                      all notations                                         *)
(*  seqprod_with d T := seq T                                                 *)
(*                   == an alias for seq, such that if T is canonically       *)
(*                      ordered, then seqprod_with d T is canonically ordered *)
(*                      in product order, i.e.,                               *)
(*                      [:: x1, .., xn] <= [y1, .., yn] =                     *)
(*                        (x1 <= y1) && ... && (xn <= yn)                     *)
(*                      and displayed in display d                            *)
(* n.-tupleprod[d] T == same with n.tuple T                                   *)
(*         seqprod T := seqprod_with (seqprod_display d) T                    *)
(*                      where d is the display of T, and seqprod_display adds *)
(*                      an extra ^sp to all notations                         *)
(*    n.-tupleprod T := n.-tuple[seqprod_display d] T                         *)
(*                      where d is the display of T                           *)
(*  seqlexi_with d T := seq T                                                 *)
(*                   == an alias for seq, such that if T is canonically       *)
(*                      ordered, then seqprod_with d T is canonically ordered *)
(*                      in lexicographic order, i.e.,                         *)
(*                      [:: x1, .., xn] <= [y1, .., yn] =                     *)
(*                        (x1 <= x2) && ((x1 >= y1) ==> ((x2 <= y2) && ...))  *)
(*                      and displayed in display d                            *)
(* n.-tuplelexi[d] T == same with n.tuple T                                   *)
(*         seqlexi T := lexiprod_with (seqlexi_display d) T                   *)
(*                      where d is the display of T, and seqlexi_display adds *)
(*                      an extra ^sl to all notations                         *)
(*    n.-tuplelexi T := n.-tuple[seqlexi_display d] T                         *)
(*                      where d is the display of T                           *)
(*     {subset[d] T} := {set T}                                               *)
(*                   == an alias for set which is canonically ordered by the  *)
(*                      subset order and displayed in display d               *)
(*        {subset T} := {subset[subset_display] T}                            *)
(*                                                                            *)
(* We provide expected instances of ordered types for bool, nat (for leq and  *)
(* and dvdn), 'I_n, 'I_n.+1 (with a top and bottom), nat for dvdn,            *)
(* T *prod[disp] T', T *lexi[disp] T', {t : T & T' x} (with lexicographic     *)
(* ordering), seqprod_with d T (using product order), seqlexi_with d T        *)
(* (with lexicographic ordering), n.-tupleprod[disp] (using product order),   *)
(* n.-tuplelexi[d] T (with lexicographic ordering), on {subset[disp] T}       *)
(* (using subset order) and all possible finite type instances.               *)
(* (Use `HB.about type` to discover the instances on type.)                   *)
(*                                                                            *)
(* In order to get a canonical order on prod, seq, tuple or set, one may      *)
(* import modules DefaultProdOrder or DefaultProdLexiOrder,                   *)
(* DefaultSeqProdOrder or DefaultSeqLexiOrder,                                *)
(* DefaultTupleProdOrder or DefaultTupleLexiOrder,                            *)
(* and DefaultSetSubsetOrder.                                                 *)
(*                                                                            *)
(* We provide Order.enum_val, Order.enum_rank, and Order.enum_rank_in, which  *)
(* are monotonic variations of enum_val, enum_rank, and enum_rank_in          *)
(* whenever the type is preorderType, and their monotonicity is provided if   *)
(* this order is total. The theory is in the module Order (Order.enum_valK,   *)
(* Order.enum_rank_inK, etc) but Order.Enum can be imported to shorten these. *)
(*                                                                            *)
(* We provide an opaque monotonous bijection tagnat.sig / tagnat.rank between *)
(* the finite types {i : 'I_n & 'I_(p_ i)} and 'I_(\sum_i p_ i):              *)
(*  tagnat.sig  : 'I_(\sum_i p_ i) -> {i : 'I_n & 'I_(p_ i)}                  *)
(*  tagnat.rank : {i : 'I_n & 'I_(p_ i)} -> 'I_(\sum_i p_ i)                  *)
(*  tagnat.sig1 : 'I_(\sum_i p_ i) -> 'I_n                                    *)
(*  tagnat.sig2 : forall p : 'I_(\sum_i p_ i), 'I_(p_ (tagnat.sig1 p))        *)
(*  tagnat.Rank : forall i, 'I_(p_ i) -> 'I_(\sum_i p_ i)                     *)
(*                                                                            *)
(* Acknowledgments: The files in this directory are based on prior work by    *)
(* D. Dreyer, G. Gonthier, A. Nanevski, P-Y Strub, B. Ziliani                 *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope order_scope.

(* Reserved notations for divisibility *)
Reserved Notation "x %<| y"  (at level 70, no associativity).

Reserved Notation "\gcd_ i F"
  (at level 34, F at level 41, i at level 0,
           format "'[' \gcd_ i '/  '  F ']'").
Reserved Notation "\gcd_ ( i <- r | P ) F"
  (at level 34, F at level 41, i, r at level 60,
           format "'[' \gcd_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\gcd_ ( i <- r ) F"
  (F at level 41,
           format "'[' \gcd_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\gcd_ ( m <= i < n | P ) F"
  (F at level 41, i, n at level 60,
           format "'[' \gcd_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\gcd_ ( m <= i < n ) F"
  (F at level 41,
           format "'[' \gcd_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\gcd_ ( i | P ) F"
  (F at level 41,
           format "'[' \gcd_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\gcd_ ( i : t | P ) F" (F at level 41).
Reserved Notation "\gcd_ ( i : t ) F" (F at level 41).
Reserved Notation "\gcd_ ( i < n | P ) F"
  (F at level 41, n at level 60,
           format "'[' \gcd_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\gcd_ ( i < n ) F"
  (F at level 41,
           format "'[' \gcd_ ( i  <  n )  F ']'").
Reserved Notation "\gcd_ ( i 'in' A | P ) F"
  (F at level 41, A at level 60,
           format "'[' \gcd_ ( i  'in'  A  |  P ) '/  '  F ']'").
Reserved Notation "\gcd_ ( i 'in' A ) F"
  (F at level 41,
           format "'[' \gcd_ ( i  'in'  A ) '/  '  F ']'").

Reserved Notation "\lcm_ i F"
  (at level 34, F at level 41, i at level 0,
           format "'[' \lcm_ i '/  '  F ']'").
Reserved Notation "\lcm_ ( i <- r | P ) F"
  (at level 34, F at level 41, i, r at level 60,
           format "'[' \lcm_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\lcm_ ( i <- r ) F"
  (F at level 41,
           format "'[' \lcm_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\lcm_ ( m <= i < n | P ) F"
  (F at level 41, i, n at level 60,
           format "'[' \lcm_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\lcm_ ( m <= i < n ) F"
  (F at level 41,
           format "'[' \lcm_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\lcm_ ( i | P ) F"
  (F at level 41,
           format "'[' \lcm_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\lcm_ ( i : t | P ) F" (F at level 41).
Reserved Notation "\lcm_ ( i : t ) F" (F at level 41).
Reserved Notation "\lcm_ ( i < n | P ) F"
  (F at level 41, n at level 60,
           format "'[' \lcm_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\lcm_ ( i < n ) F"
  (F at level 41,
           format "'[' \lcm_ ( i  <  n )  F ']'").
Reserved Notation "\lcm_ ( i 'in' A | P ) F"
  (F at level 41, A at level 60,
           format "'[' \lcm_ ( i  'in'  A  |  P ) '/  '  F ']'").
Reserved Notation "\lcm_ ( i 'in' A ) F"
  (F at level 41,
           format "'[' \lcm_ ( i  'in'  A ) '/  '  F ']'").

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

(* Reserved notations for product ordering of seq *)
Reserved Notation "x <=^sp y" (at level 70, y at next level).
Reserved Notation "x >=^sp y" (at level 70, y at next level).
Reserved Notation "x <^sp y" (at level 70, y at next level).
Reserved Notation "x >^sp y" (at level 70, y at next level).
Reserved Notation "x <=^sp y :> T" (at level 70, y at next level).
Reserved Notation "x >=^sp y :> T" (at level 70, y at next level).
Reserved Notation "x <^sp y :> T" (at level 70, y at next level).
Reserved Notation "x >^sp y :> T" (at level 70, y at next level).
Reserved Notation "<=^sp y" (at level 35).
Reserved Notation ">=^sp y" (at level 35).
Reserved Notation "<^sp y" (at level 35).
Reserved Notation ">^sp y" (at level 35).
Reserved Notation "<=^sp y :> T" (at level 35, y at next level).
Reserved Notation ">=^sp y :> T" (at level 35, y at next level).
Reserved Notation "<^sp y :> T" (at level 35, y at next level).
Reserved Notation ">^sp y :> T" (at level 35, y at next level).
Reserved Notation "x >=<^sp y" (at level 70, no associativity).
Reserved Notation ">=<^sp x" (at level 35).
Reserved Notation ">=<^sp y :> T" (at level 35, y at next level).
Reserved Notation "x ><^sp y" (at level 70, no associativity).
Reserved Notation "><^sp x" (at level 35).
Reserved Notation "><^sp y :> T" (at level 35, y at next level).

Reserved Notation "x <=^sp y <=^sp z" (at level 70, y, z at next level).
Reserved Notation "x <^sp y <=^sp z" (at level 70, y, z at next level).
Reserved Notation "x <=^sp y <^sp z" (at level 70, y, z at next level).
Reserved Notation "x <^sp y <^sp z" (at level 70, y, z at next level).
Reserved Notation "x <=^sp y ?= 'iff' c" (at level 70, y, c at next level,
  format "x '[hv'  <=^sp  y '/'  ?=  'iff'  c ']'").
Reserved Notation "x <=^sp y ?= 'iff' c :> T" (at level 70, y, c at next level,
  format "x '[hv'  <=^sp  y '/'  ?=  'iff'  c  :> T ']'").

Reserved Notation "\bot^sp".
Reserved Notation "\top^sp".

Reserved Notation "A `&^sp` B"  (at level 48, left associativity).
Reserved Notation "A `|^sp` B" (at level 52, left associativity).
Reserved Notation "A `\^sp` B" (at level 50, left associativity).
Reserved Notation "~^sp` A" (at level 35, right associativity).

Reserved Notation "\meet^sp_ i F"
  (at level 34, F at level 41, i at level 0,
           format "'[' \meet^sp_ i '/  '  F ']'").
Reserved Notation "\meet^sp_ ( i <- r | P ) F"
  (at level 34, F at level 41, i, r at level 60,
           format "'[' \meet^sp_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\meet^sp_ ( i <- r ) F"
  (F at level 41,
           format "'[' \meet^sp_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\meet^sp_ ( m <= i < n | P ) F"
  (F at level 41, i, n at level 60,
           format "'[' \meet^sp_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\meet^sp_ ( m <= i < n ) F"
  (F at level 41,
           format "'[' \meet^sp_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\meet^sp_ ( i | P ) F"
  (F at level 41,
           format "'[' \meet^sp_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\meet^sp_ ( i : t | P ) F" (F at level 41).
Reserved Notation "\meet^sp_ ( i : t ) F" (F at level 41).
Reserved Notation "\meet^sp_ ( i < n | P ) F"
  (F at level 41, n at level 60,
           format "'[' \meet^sp_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\meet^sp_ ( i < n ) F"
  (F at level 41,
           format "'[' \meet^sp_ ( i  <  n )  F ']'").
Reserved Notation "\meet^sp_ ( i 'in' A | P ) F"
  (F at level 41, A at level 60,
           format "'[' \meet^sp_ ( i  'in'  A  |  P ) '/  '  F ']'").
Reserved Notation "\meet^sp_ ( i 'in' A ) F"
  (F at level 41,
           format "'[' \meet^sp_ ( i  'in'  A ) '/  '  F ']'").

Reserved Notation "\join^sp_ i F"
  (at level 34, F at level 41, i at level 0,
           format "'[' \join^sp_ i '/  '  F ']'").
Reserved Notation "\join^sp_ ( i <- r | P ) F"
  (at level 34, F at level 41, i, r at level 60,
           format "'[' \join^sp_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\join^sp_ ( i <- r ) F"
  (F at level 41,
           format "'[' \join^sp_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\join^sp_ ( m <= i < n | P ) F"
  (F at level 41, i, n at level 60,
           format "'[' \join^sp_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\join^sp_ ( m <= i < n ) F"
  (F at level 41,
           format "'[' \join^sp_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\join^sp_ ( i | P ) F"
  (F at level 41,
           format "'[' \join^sp_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\join^sp_ ( i : t | P ) F" (F at level 41).
Reserved Notation "\join^sp_ ( i : t ) F" (F at level 41).
Reserved Notation "\join^sp_ ( i < n | P ) F"
  (F at level 41, n at level 60,
           format "'[' \join^sp_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\join^sp_ ( i < n ) F"
  (F at level 41,
           format "'[' \join^sp_ ( i  <  n )  F ']'").
Reserved Notation "\join^sp_ ( i 'in' A | P ) F"
  (F at level 41, A at level 60,
           format "'[' \join^sp_ ( i  'in'  A  |  P ) '/  '  F ']'").
Reserved Notation "\join^sp_ ( i 'in' A ) F"
  (F at level 41,
           format "'[' \join^sp_ ( i  'in'  A ) '/  '  F ']'").

Reserved Notation "\min^sp_ i F"
  (at level 34, F at level 41, i at level 0,
           format "'[' \min^sp_ i '/  '  F ']'").
Reserved Notation "\min^sp_ ( i <- r | P ) F"
  (at level 34, F at level 41, i, r at level 60,
           format "'[' \min^sp_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\min^sp_ ( i <- r ) F"
  (F at level 41,
           format "'[' \min^sp_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\min^sp_ ( m <= i < n | P ) F"
  (F at level 41, i, n at level 60,
           format "'[' \min^sp_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\min^sp_ ( m <= i < n ) F"
  (F at level 41,
           format "'[' \min^sp_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\min^sp_ ( i | P ) F"
  (F at level 41,
           format "'[' \min^sp_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\min^sp_ ( i : t | P ) F" (F at level 41).
Reserved Notation "\min^sp_ ( i : t ) F" (F at level 41).
Reserved Notation "\min^sp_ ( i < n | P ) F"
  (F at level 41, n at level 60,
           format "'[' \min^sp_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\min^sp_ ( i < n ) F"
  (F at level 41,
           format "'[' \min^sp_ ( i  <  n )  F ']'").
Reserved Notation "\min^sp_ ( i 'in' A | P ) F"
  (F at level 41, A at level 60,
           format "'[' \min^sp_ ( i  'in'  A  |  P ) '/  '  F ']'").
Reserved Notation "\min^sp_ ( i 'in' A ) F"
  (F at level 41,
           format "'[' \min^sp_ ( i  'in'  A ) '/  '  F ']'").

Reserved Notation "\max^sp_ i F"
  (at level 34, F at level 41, i at level 0,
           format "'[' \max^sp_ i '/  '  F ']'").
Reserved Notation "\max^sp_ ( i <- r | P ) F"
  (at level 34, F at level 41, i, r at level 60,
           format "'[' \max^sp_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\max^sp_ ( i <- r ) F"
  (F at level 41,
           format "'[' \max^sp_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\max^sp_ ( m <= i < n | P ) F"
  (F at level 41, i, n at level 60,
           format "'[' \max^sp_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\max^sp_ ( m <= i < n ) F"
  (F at level 41,
           format "'[' \max^sp_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\max^sp_ ( i | P ) F"
  (F at level 41,
           format "'[' \max^sp_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\max^sp_ ( i : t | P ) F" (F at level 41).
Reserved Notation "\max^sp_ ( i : t ) F" (F at level 41).
Reserved Notation "\max^sp_ ( i < n | P ) F"
  (F at level 41, n at level 60,
           format "'[' \max^sp_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\max^sp_ ( i < n ) F"
  (F at level 41,
           format "'[' \max^sp_ ( i  <  n )  F ']'").
Reserved Notation "\max^sp_ ( i 'in' A | P ) F"
  (F at level 41, A at level 60,
           format "'[' \max^sp_ ( i  'in'  A  |  P ) '/  '  F ']'").
Reserved Notation "\max^sp_ ( i 'in' A ) F"
  (F at level 41,
           format "'[' \max^sp_ ( i  'in'  A ) '/  '  F ']'").

(* Reserved notations for lexicographic ordering of prod *)
Reserved Notation "x <=^l y" (at level 70, y at next level).
Reserved Notation "x >=^l y" (at level 70, y at next level).
Reserved Notation "x <^l y" (at level 70, y at next level).
Reserved Notation "x >^l y" (at level 70, y at next level).
Reserved Notation "x <=^l y :> T" (at level 70, y at next level).
Reserved Notation "x >=^l y :> T" (at level 70, y at next level).
Reserved Notation "x <^l y :> T" (at level 70, y at next level).
Reserved Notation "x >^l y :> T" (at level 70, y at next level).
Reserved Notation "<=^l y" (at level 35).
Reserved Notation ">=^l y" (at level 35).
Reserved Notation "<^l y" (at level 35).
Reserved Notation ">^l y" (at level 35).
Reserved Notation "<=^l y :> T" (at level 35, y at next level).
Reserved Notation ">=^l y :> T" (at level 35, y at next level).
Reserved Notation "<^l y :> T" (at level 35, y at next level).
Reserved Notation ">^l y :> T" (at level 35, y at next level).
Reserved Notation "x >=<^l y" (at level 70, no associativity).
Reserved Notation ">=<^l x" (at level 35).
Reserved Notation ">=<^l y :> T" (at level 35, y at next level).
Reserved Notation "x ><^l y" (at level 70, no associativity).
Reserved Notation "><^l x" (at level 35).
Reserved Notation "><^l y :> T" (at level 35, y at next level).

Reserved Notation "x <=^l y <=^l z" (at level 70, y, z at next level).
Reserved Notation "x <^l y <=^l z" (at level 70, y, z at next level).
Reserved Notation "x <=^l y <^l z" (at level 70, y, z at next level).
Reserved Notation "x <^l y <^l z" (at level 70, y, z at next level).
Reserved Notation "x <=^l y ?= 'iff' c" (at level 70, y, c at next level,
  format "x '[hv'  <=^l  y '/'  ?=  'iff'  c ']'").
Reserved Notation "x <=^l y ?= 'iff' c :> T" (at level 70, y, c at next level,
  format "x '[hv'  <=^l  y '/'  ?=  'iff'  c  :> T ']'").

Reserved Notation "\bot^l".
Reserved Notation "\top^l".

Reserved Notation "A `&^l` B"  (at level 48, left associativity).
Reserved Notation "A `|^l` B" (at level 52, left associativity).
Reserved Notation "A `\^l` B" (at level 50, left associativity).
Reserved Notation "~^l` A" (at level 35, right associativity).

Reserved Notation "\meet^l_ i F"
  (at level 34, F at level 41, i at level 0,
           format "'[' \meet^l_ i '/  '  F ']'").
Reserved Notation "\meet^l_ ( i <- r | P ) F"
  (at level 34, F at level 41, i, r at level 60,
           format "'[' \meet^l_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\meet^l_ ( i <- r ) F"
  (F at level 41,
           format "'[' \meet^l_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\meet^l_ ( m <= i < n | P ) F"
  (F at level 41, i, n at level 60,
           format "'[' \meet^l_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\meet^l_ ( m <= i < n ) F"
  (F at level 41,
           format "'[' \meet^l_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\meet^l_ ( i | P ) F"
  (F at level 41,
           format "'[' \meet^l_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\meet^l_ ( i : t | P ) F" (F at level 41).
Reserved Notation "\meet^l_ ( i : t ) F" (F at level 41).
Reserved Notation "\meet^l_ ( i < n | P ) F"
  (F at level 41, n at level 60,
           format "'[' \meet^l_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\meet^l_ ( i < n ) F"
  (F at level 41,
           format "'[' \meet^l_ ( i  <  n )  F ']'").
Reserved Notation "\meet^l_ ( i 'in' A | P ) F"
  (F at level 41, A at level 60,
           format "'[' \meet^l_ ( i  'in'  A  |  P ) '/  '  F ']'").
Reserved Notation "\meet^l_ ( i 'in' A ) F"
  (F at level 41,
           format "'[' \meet^l_ ( i  'in'  A ) '/  '  F ']'").

Reserved Notation "\join^l_ i F"
  (at level 34, F at level 41, i at level 0,
           format "'[' \join^l_ i '/  '  F ']'").
Reserved Notation "\join^l_ ( i <- r | P ) F"
  (at level 34, F at level 41, i, r at level 60,
           format "'[' \join^l_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\join^l_ ( i <- r ) F"
  (F at level 41,
           format "'[' \join^l_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\join^l_ ( m <= i < n | P ) F"
  (F at level 41, i, n at level 60,
           format "'[' \join^l_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\join^l_ ( m <= i < n ) F"
  (F at level 41,
           format "'[' \join^l_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\join^l_ ( i | P ) F"
  (F at level 41,
           format "'[' \join^l_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\join^l_ ( i : t | P ) F" (F at level 41).
Reserved Notation "\join^l_ ( i : t ) F" (F at level 41).
Reserved Notation "\join^l_ ( i < n | P ) F"
  (F at level 41, n at level 60,
           format "'[' \join^l_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\join^l_ ( i < n ) F"
  (F at level 41,
           format "'[' \join^l_ ( i  <  n )  F ']'").
Reserved Notation "\join^l_ ( i 'in' A | P ) F"
  (F at level 41, A at level 60,
           format "'[' \join^l_ ( i  'in'  A  |  P ) '/  '  F ']'").
Reserved Notation "\join^l_ ( i 'in' A ) F"
  (F at level 41,
           format "'[' \join^l_ ( i  'in'  A ) '/  '  F ']'").

Reserved Notation "\min^l_ i F"
  (at level 34, F at level 41, i at level 0,
           format "'[' \min^l_ i '/  '  F ']'").
Reserved Notation "\min^l_ ( i <- r | P ) F"
  (at level 34, F at level 41, i, r at level 60,
           format "'[' \min^l_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\min^l_ ( i <- r ) F"
  (F at level 41,
           format "'[' \min^l_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\min^l_ ( m <= i < n | P ) F"
  (F at level 41, i, n at level 60,
           format "'[' \min^l_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\min^l_ ( m <= i < n ) F"
  (F at level 41,
           format "'[' \min^l_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\min^l_ ( i | P ) F"
  (F at level 41,
           format "'[' \min^l_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\min^l_ ( i : t | P ) F" (F at level 41).
Reserved Notation "\min^l_ ( i : t ) F" (F at level 41).
Reserved Notation "\min^l_ ( i < n | P ) F"
  (F at level 41, n at level 60,
           format "'[' \min^l_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\min^l_ ( i < n ) F"
  (F at level 41,
           format "'[' \min^l_ ( i  <  n )  F ']'").
Reserved Notation "\min^l_ ( i 'in' A | P ) F"
  (F at level 41, A at level 60,
           format "'[' \min^l_ ( i  'in'  A  |  P ) '/  '  F ']'").
Reserved Notation "\min^l_ ( i 'in' A ) F"
  (F at level 41,
           format "'[' \min^l_ ( i  'in'  A ) '/  '  F ']'").

Reserved Notation "\max^l_ i F"
  (at level 34, F at level 41, i at level 0,
           format "'[' \max^l_ i '/  '  F ']'").
Reserved Notation "\max^l_ ( i <- r | P ) F"
  (at level 34, F at level 41, i, r at level 60,
           format "'[' \max^l_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\max^l_ ( i <- r ) F"
  (F at level 41,
           format "'[' \max^l_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\max^l_ ( m <= i < n | P ) F"
  (F at level 41, i, n at level 60,
           format "'[' \max^l_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\max^l_ ( m <= i < n ) F"
  (F at level 41,
           format "'[' \max^l_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\max^l_ ( i | P ) F"
  (F at level 41,
           format "'[' \max^l_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\max^l_ ( i : t | P ) F" (F at level 41).
Reserved Notation "\max^l_ ( i : t ) F" (F at level 41).
Reserved Notation "\max^l_ ( i < n | P ) F"
  (F at level 41, n at level 60,
           format "'[' \max^l_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\max^l_ ( i < n ) F"
  (F at level 41,
           format "'[' \max^l_ ( i  <  n )  F ']'").
Reserved Notation "\max^l_ ( i 'in' A | P ) F"
  (F at level 41, A at level 60,
           format "'[' \max^l_ ( i  'in'  A  |  P ) '/  '  F ']'").
Reserved Notation "\max^l_ ( i 'in' A ) F"
  (F at level 41,
           format "'[' \max^l_ ( i  'in'  A ) '/  '  F ']'").

(* Reserved notations for lexicographic ordering of seq *)
Reserved Notation "x <=^sl y" (at level 70, y at next level).
Reserved Notation "x >=^sl y" (at level 70, y at next level).
Reserved Notation "x <^sl y" (at level 70, y at next level).
Reserved Notation "x >^sl y" (at level 70, y at next level).
Reserved Notation "x <=^sl y :> T" (at level 70, y at next level).
Reserved Notation "x >=^sl y :> T" (at level 70, y at next level).
Reserved Notation "x <^sl y :> T" (at level 70, y at next level).
Reserved Notation "x >^sl y :> T" (at level 70, y at next level).
Reserved Notation "<=^sl y" (at level 35).
Reserved Notation ">=^sl y" (at level 35).
Reserved Notation "<^sl y" (at level 35).
Reserved Notation ">^sl y" (at level 35).
Reserved Notation "<=^sl y :> T" (at level 35, y at next level).
Reserved Notation ">=^sl y :> T" (at level 35, y at next level).
Reserved Notation "<^sl y :> T" (at level 35, y at next level).
Reserved Notation ">^sl y :> T" (at level 35, y at next level).
Reserved Notation "x >=<^sl y" (at level 70, no associativity).
Reserved Notation ">=<^sl x" (at level 35).
Reserved Notation ">=<^sl y :> T" (at level 35, y at next level).
Reserved Notation "x ><^sl y" (at level 70, no associativity).
Reserved Notation "><^sl x" (at level 35).
Reserved Notation "><^sl y :> T" (at level 35, y at next level).

Reserved Notation "x <=^sl y <=^sl z" (at level 70, y, z at next level).
Reserved Notation "x <^sl y <=^sl z" (at level 70, y, z at next level).
Reserved Notation "x <=^sl y <^sl z" (at level 70, y, z at next level).
Reserved Notation "x <^sl y <^sl z" (at level 70, y, z at next level).
Reserved Notation "x <=^sl y ?= 'iff' c" (at level 70, y, c at next level,
  format "x '[hv'  <=^sl  y '/'  ?=  'iff'  c ']'").
Reserved Notation "x <=^sl y ?= 'iff' c :> T" (at level 70, y, c at next level,
  format "x '[hv'  <=^sl  y '/'  ?=  'iff'  c  :> T ']'").

Reserved Notation "\bot^sl".
Reserved Notation "\top^sl".

Reserved Notation "A `&^sl` B"  (at level 48, left associativity).
Reserved Notation "A `|^sl` B" (at level 52, left associativity).
Reserved Notation "A `\^sl` B" (at level 50, left associativity).
Reserved Notation "~^sl` A" (at level 35, right associativity).

Module Order.

Import total_order.Order.
Import total_order.Order.Theory.
Import complemented_lattice.Order.
Import complemented_lattice.Order.Theory.

(********************)
(* Instances on nat *)
(********************)

(******************************************************************************)
(* This is an example of creation of multiple instances on the same type,     *)
(* with distinct displays, using natural numbers.                             *)
(* We declare two distinct canonical orders:                                  *)
(* - leq which is total, and where meet and join are minn and maxn, on nat    *)
(* - dvdn which is partial, and where meet and join are gcdn and lcmn,        *)
(*   on natdvd                                                                *)
(******************************************************************************)

(******************************************************************************)
(* The Module NatOrder defines leq as the canonical order on the type nat,    *)
(* i.e., without creating an alias. We define and use nat_display and proceed *)
(* like a standard canonical structure declaration, except that we use this   *)
(* display. We also use a single factory LeOrderMixin to instantiate three    *)
(* different canonical declarations porderType, distrLatticeType, orderType.  *)
(* We finish by providing theorems to convert the operations of ordered and   *)
(* lattice types to their definition without structure abstraction.           *)
(******************************************************************************)

Module NatOrder.
Section NatOrder.
  
Fact nat_display : disp_t. Proof. exact. Qed.

Fact ltn_def n m : (n < m)%N = (m != n) && (n <= m)%N.
Proof. by rewrite ltn_neqAle eq_sym. Qed.

#[export] HB.instance Definition _ :=
  isPOrder.Build nat_display nat ltn_def leqnn anti_leq leq_trans.
#[export] HB.instance Definition _ :=
  POrder_isTotal.Build nat_display nat leq_total.
#[export] HB.instance Definition _ := hasBottom.Build nat_display nat leq0n.

Lemma leEnat : le = leq. Proof. by []. Qed.
Lemma ltEnat : lt = ltn. Proof. by []. Qed.
Lemma minEnat : min = minn. Proof. by []. Qed.
Lemma maxEnat : max = maxn. Proof. by []. Qed.
Lemma botEnat : \bot = 0%N :> nat. Proof. by []. Qed.

End NatOrder.

Module Exports.
HB.reexport NatOrder.
Definition leEnat := leEnat.
Definition ltEnat := ltEnat.
Definition minEnat := minEnat.
Definition maxEnat := maxEnat.
Definition botEnat := botEnat.
End Exports.
End NatOrder.
HB.export NatOrder.Exports.

Module NatMonotonyTheory.
Section NatMonotonyTheory.

Context {disp : disp_t} {T : preorderType disp}.
Variables (D : {pred nat}) (f : nat -> T).
Hypothesis Dconvex : {in D &, forall i j k, i < k < j -> k \in D}.

Lemma homo_ltn_lt_in : {in D, forall i, i.+1 \in D -> f i < f i.+1} ->
  {in D &, {homo f : i j / i < j}}.
Proof. by apply: homo_ltn_in Dconvex; apply: lt_trans. Qed.

Lemma nondecn_inP : {in D, forall i, i.+1 \in D -> f i <= f i.+1} ->
  {in D &, {homo f : i j / i <= j}}.
Proof. by apply: homo_leq_in Dconvex => //; apply: le_trans. Qed.

Lemma nhomo_ltn_lt_in : {in D, forall i, i.+1 \in D -> f i > f i.+1} ->
  {in D &, {homo f : i j /~ i < j}}.
Proof.
move=> f_dec; apply: homo_sym_in.
by apply: homo_ltn_in Dconvex f_dec => ? ? ? ? /lt_trans->.
Qed.

Lemma nonincn_inP : {in D, forall i, i.+1 \in D -> f i >= f i.+1} ->
  {in D &, {homo f : i j /~ i <= j}}.
Proof.
move=> /= f_dec; apply: homo_sym_in.
by apply: homo_leq_in Dconvex f_dec => //= ? ? ? ? /le_trans->.
Qed.

Lemma homo_ltn_lt : (forall i, f i < f i.+1) -> {homo f : i j / i < j}.
Proof. by apply: homo_ltn; apply: lt_trans. Qed.

Lemma nondecnP : (forall i, f i <= f i.+1) -> {homo f : i j / i <= j}.
Proof. by apply: homo_leq => //; apply: le_trans. Qed.

Lemma nhomo_ltn_lt : (forall i, f i > f i.+1) -> {homo f : i j /~ i < j}.
Proof.
move=> f_dec; apply: homo_sym.
by apply: homo_ltn f_dec => ? ? ? ? /lt_trans->.
Qed.

Lemma nonincnP : (forall i, f i >= f i.+1) -> {homo f : i j /~ i <= j}.
Proof.
move=> /= f_dec; apply: homo_sym.
by apply: homo_leq f_dec => //= ? ? ? ? /le_trans->.
Qed.

End NatMonotonyTheory.
Arguments homo_ltn_lt_in {disp T} [D f].
Arguments nondecn_inP {disp T} [D f].
Arguments nhomo_ltn_lt_in {disp T} [D f].
Arguments nonincn_inP {disp T} [D f].
Arguments homo_ltn_lt {disp T} [f].
Arguments nondecnP {disp T} [f].
Arguments nhomo_ltn_lt {disp T} [f].
Arguments nonincnP {disp T} [f].

Section NatMonotonyTheory.

Context {disp : disp_t} {T : porderType disp}.
Variables (D : {pred nat}) (f : nat -> T).
Hypothesis Dconvex : {in D &, forall i j k, i < k < j -> k \in D}.

Lemma incn_inP : {in D, forall i, i.+1 \in D -> f i < f i.+1} ->
  {in D &, {mono f : i j / i <= j}}.
Proof. by move=> f_inc; apply/le_mono_in/homo_ltn_lt_in. Qed.

Lemma decn_inP : {in D, forall i, i.+1 \in D -> f i > f i.+1} ->
  {in D &, {mono f : i j /~ i <= j}}.
Proof. by move=> f_dec; apply/le_nmono_in/nhomo_ltn_lt_in. Qed.

Lemma incnP : (forall i, f i < f i.+1) -> {mono f : i j / i <= j}.
Proof. by move=> f_inc; apply/le_mono/homo_ltn_lt. Qed.

Lemma decnP : (forall i, f i > f i.+1) -> {mono f : i j /~ i <= j}.
Proof. by move=> f_dec; apply/le_nmono/nhomo_ltn_lt. Qed.

End NatMonotonyTheory.
Arguments incn_inP {disp T} [D f].
Arguments decn_inP {disp T} [D f].
Arguments incnP {disp T} [f].
Arguments decnP {disp T} [f].

End NatMonotonyTheory.

(****************************************************************************)
(* The Module DvdSyntax introduces a new set of notations using the newly   *)
(* created display dvd_display. We first define the display as an opaque    *)
(* definition of type disp_t, and we use it as the first argument of the    *)
(* operator which display we want to change from the default one (here le,  *)
(* lt, dvd sdvd, meet, join, top and bottom, as well as big op notations on *)
(* gcd and lcm). This notations will now be used for any ordered type which *)
(* first parameter is set to dvd_display.                                   *)
(****************************************************************************)

Fact dvd_display : disp_t. Proof. exact. Qed.

Module DvdSyntax.

Notation dvd := (@le dvd_display _).
Notation "@ 'dvd' T" := (@le dvd_display T)
  (at level 10, T at level 8, only parsing) : function_scope.
Notation sdvd := (@lt dvd_display _).
Notation "@ 'sdvd' T" := (@lt dvd_display T)
  (at level 10, T at level 8, only parsing) : function_scope.

Notation "x %| y" := (dvd x y) : order_scope.
Notation "x %<| y" := (sdvd x y) : order_scope.

Notation nat0 := (@top dvd_display _).
Notation nat1 := (@bottom dvd_display _).

Notation gcd := (@meet dvd_display _).
Notation "@ 'gcd' T" := (@meet dvd_display T)
  (at level 10, T at level 8, only parsing) : function_scope.
Notation lcm := (@join dvd_display _).
Notation "@ 'lcm' T" := (@join dvd_display T)
  (at level 10, T at level 8, only parsing) : function_scope.

Notation "\gcd_ ( i <- r | P ) F" :=
  (\big[gcd/nat0]_(i <- r | P%B) F%O) : order_scope.
Notation "\gcd_ ( i <- r ) F" :=
  (\big[gcd/nat0]_(i <- r) F%O) : order_scope.
Notation "\gcd_ ( i | P ) F" :=
  (\big[gcd/nat0]_(i | P%B) F%O) : order_scope.
Notation "\gcd_ i F" :=
  (\big[gcd/nat0]_i F%O) : order_scope.
Notation "\gcd_ ( i : I | P ) F" :=
  (\big[gcd/nat0]_(i : I | P%B) F%O) (only parsing) :
  order_scope.
Notation "\gcd_ ( i : I ) F" :=
  (\big[gcd/nat0]_(i : I) F%O) (only parsing) : order_scope.
Notation "\gcd_ ( m <= i < n | P ) F" :=
  (\big[gcd/nat0]_(m <= i < n | P%B) F%O) : order_scope.
Notation "\gcd_ ( m <= i < n ) F" :=
  (\big[gcd/nat0]_(m <= i < n) F%O) : order_scope.
Notation "\gcd_ ( i < n | P ) F" :=
  (\big[gcd/nat0]_(i < n | P%B) F%O) : order_scope.
Notation "\gcd_ ( i < n ) F" :=
  (\big[gcd/nat0]_(i < n) F%O) : order_scope.
Notation "\gcd_ ( i 'in' A | P ) F" :=
  (\big[gcd/nat0]_(i in A | P%B) F%O) : order_scope.
Notation "\gcd_ ( i 'in' A ) F" :=
  (\big[gcd/nat0]_(i in A) F%O) : order_scope.

Notation "\lcm_ ( i <- r | P ) F" :=
  (\big[lcm/nat1]_(i <- r | P%B) F%O) : order_scope.
Notation "\lcm_ ( i <- r ) F" :=
  (\big[lcm/nat1]_(i <- r) F%O) : order_scope.
Notation "\lcm_ ( i | P ) F" :=
  (\big[lcm/nat1]_(i | P%B) F%O) : order_scope.
Notation "\lcm_ i F" :=
  (\big[lcm/nat1]_i F%O) : order_scope.
Notation "\lcm_ ( i : I | P ) F" :=
  (\big[lcm/nat1]_(i : I | P%B) F%O) (only parsing) :
  order_scope.
Notation "\lcm_ ( i : I ) F" :=
  (\big[lcm/nat1]_(i : I) F%O) (only parsing) : order_scope.
Notation "\lcm_ ( m <= i < n | P ) F" :=
  (\big[lcm/nat1]_(m <= i < n | P%B) F%O) : order_scope.
Notation "\lcm_ ( m <= i < n ) F" :=
  (\big[lcm/nat1]_(m <= i < n) F%O) : order_scope.
Notation "\lcm_ ( i < n | P ) F" :=
  (\big[lcm/nat1]_(i < n | P%B) F%O) : order_scope.
Notation "\lcm_ ( i < n ) F" :=
  (\big[lcm/nat1]_(i < n) F%O) : order_scope.
Notation "\lcm_ ( i 'in' A | P ) F" :=
  (\big[lcm/nat1]_(i in A | P%B) F%O) : order_scope.
Notation "\lcm_ ( i 'in' A ) F" :=
  (\big[lcm/nat1]_(i in A) F%O) : order_scope.

End DvdSyntax.

(******************************************************************************)
(* The Module NatDvd defines dvdn as the canonical order on NatDvd.t, which   *)
(* is abbreviated using the notation natdvd at the end of the module.         *)
(* We use the newly defined dvd_display, described above.                     *)
(* We first recover structures that are common to both nat and natdvd         *)
(* (eqType, choiceType, countType) through the copy mechanism, then we use    *)
(* a single factory MeetJoinMixin to instantiate both porderType and          *)
(* distrLatticeType canonical structures, and end with top and bottom.        *)
(* We finish by providing theorems to convert the operations of ordered and   *)
(* lattice types to their definition without structure abstraction.           *)
(******************************************************************************)

Module NatDvd.
Section NatDvd.
Definition t := nat.
Implicit Types (m n p : t).

#[export] HB.instance Definition _ := Choice.copy t nat.

Fact dvdn_anti : antisymmetric dvdn.
Proof. by move=> a b => /andP[] /gcdn_idPl + /gcdn_idPr => ->. Qed.

(* Note that this where the dvd_display is associated with the type NatDvd.t. *)
#[export] HB.instance Definition _ :=
  @Le_isPOrder.Build dvd_display t dvdn dvdnn dvdn_anti dvdn_trans.
#[export] HB.instance Definition _ := @hasBottom.Build _ t 1 dvd1n.
#[export] HB.instance Definition _ := @hasTop.Build _ t 0 dvdn0.
#[export] HB.instance Definition _ :=
  @POrder_MeetJoin_isLattice.Build dvd_display t gcdn lcmn dvdn_gcd dvdn_lcm.

Import DvdSyntax.

Fact meetUl : @left_distributive t t gcd lcm.
Proof.
move=> [|m'] [|n'] [|p']; rewrite ?joinxx ?join1x ?joinx1 ?meet1x ?meetx1//=.
- by rewrite meetKUC.
- by rewrite meetUK.
apply: eqn_from_log; rewrite ?(gcdn_gt0, lcmn_gt0)//= => p.
by rewrite !(logn_gcd, logn_lcm) ?(gcdn_gt0, lcmn_gt0)// minn_maxl.
Qed.

#[export] HB.instance Definition _ :=
  Lattice_Meet_isDistrLattice.Build dvd_display t meetUl.

Lemma dvdE : dvd = dvdn :> rel t. Proof. by []. Qed.
Lemma nat1E : nat1 = 1%N :> t. Proof. by []. Qed.
Lemma nat0E : nat0 = 0%N :> t. Proof. by []. Qed.
Lemma sdvdE (m n : t) : (m %<| n) = (n != m) && (m %| n).
Proof. exact/lt_def. Qed.
Lemma gcdE : gcd = gcdn :> (t -> t -> t). Proof. by []. Qed.
Lemma lcmE : lcm = lcmn :> (t -> t -> t). Proof. by []. Qed.

End NatDvd.
Module Exports.
HB.reexport NatDvd.
Notation natdvd := t.
Definition dvdEnat := dvdE.
Definition nat1E := nat1E.
Definition nat0E := nat0E.
Definition sdvdEnat := sdvdE.
Definition gcdEnat := gcdE.
Definition lcmEnat := lcmE.
End Exports.
End NatDvd.
HB.export NatDvd.Exports.

(************************)
(* Instances on ordinal *)
(************************)

Module OrdinalOrder.
Section OrdinalOrder.

Fact ord_display : disp_t. Proof. exact. Qed.

Section PossiblyTrivial.
Context (n : nat).

#[export] HB.instance Definition _ :=
  [SubChoice_isSubOrder of 'I_n by <: with ord_display].

Lemma leEord : (le : rel 'I_n) = leq. Proof. by []. Qed.
Lemma ltEord : (lt : rel 'I_n) = (fun m n => m < n)%N. Proof. by []. Qed.
End PossiblyTrivial.

Section NonTrivial.
Context (n' : nat).
Let n := n'.+1.

#[export] HB.instance Definition _ := @hasBottom.Build _ 'I_n ord0 leq0n.
#[export] HB.instance Definition _ := @hasTop.Build _ 'I_n ord_max (@leq_ord _).

Lemma botEord : \bot = ord0. Proof. by []. Qed.
Lemma topEord : \top = ord_max. Proof. by []. Qed.

End NonTrivial.

End OrdinalOrder.

Module Exports.
HB.reexport OrdinalOrder.
Definition leEord := leEord.
Definition ltEord := ltEord.
Definition botEord := botEord.
Definition topEord := topEord.
End Exports.
End OrdinalOrder.
HB.export OrdinalOrder.Exports.

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

(******************************)
(* Definition of prod_display *)
(******************************)

Fact prod_display_unit (_ _ : unit) : unit. Proof. exact: tt. Qed.

Definition prod_display (displ dispr : disp_t) : disp_t :=
  Disp (prod_display_unit (d1 displ) (d1 dispr))
       (prod_display_unit (d2 displ) (d2 dispr)).

Fact seqprod_display (disp : disp_t) : disp_t. Proof. exact: disp. Qed.

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

Module Import SeqProdSyntax.

Notation "<=^sp%O" := (@le (seqprod_display _) _) : function_scope.
Notation ">=^sp%O" := (@ge (seqprod_display _) _)  : function_scope.
Notation ">=^sp%O" := (@ge (seqprod_display _) _)  : function_scope.
Notation "<^sp%O" := (@lt (seqprod_display _) _) : function_scope.
Notation ">^sp%O" := (@gt (seqprod_display _) _) : function_scope.
Notation "<?=^sp%O" := (@leif (seqprod_display _) _) : function_scope.
Notation ">=<^sp%O" := (@comparable (seqprod_display _) _) : function_scope.
Notation "><^sp%O" := (fun x y => ~~ (@comparable (seqprod_display _) _ x y)) :
  function_scope.

Notation "<=^sp y" := (>=^sp%O y) : order_scope.
Notation "<=^sp y :> T" := (<=^sp (y : T)) (only parsing) : order_scope.
Notation ">=^sp y"  := (<=^sp%O y) : order_scope.
Notation ">=^sp y :> T" := (>=^sp (y : T)) (only parsing) : order_scope.

Notation "<^sp y" := (>^sp%O y) : order_scope.
Notation "<^sp y :> T" := (<^sp (y : T)) (only parsing) : order_scope.
Notation ">^sp y" := (<^sp%O y) : order_scope.
Notation ">^sp y :> T" := (>^sp (y : T)) (only parsing) : order_scope.

Notation "x <=^sp y" := (<=^sp%O x y) : order_scope.
Notation "x <=^sp y :> T" := ((x : T) <=^sp (y : T)) (only parsing) : order_scope.
Notation "x >=^sp y" := (y <=^sp x) (only parsing) : order_scope.
Notation "x >=^sp y :> T" := ((x : T) >=^sp (y : T)) (only parsing) : order_scope.

Notation "x <^sp y"  := (<^sp%O x y) : order_scope.
Notation "x <^sp y :> T" := ((x : T) <^sp (y : T)) (only parsing) : order_scope.
Notation "x >^sp y"  := (y <^sp x) (only parsing) : order_scope.
Notation "x >^sp y :> T" := ((x : T) >^sp (y : T)) (only parsing) : order_scope.

Notation "x <=^sp y <=^sp z" := ((x <=^sp y) && (y <=^sp z)) : order_scope.
Notation "x <^sp y <=^sp z" := ((x <^sp y) && (y <=^sp z)) : order_scope.
Notation "x <=^sp y <^sp z" := ((x <=^sp y) && (y <^sp z)) : order_scope.
Notation "x <^sp y <^sp z" := ((x <^sp y) && (y <^sp z)) : order_scope.

Notation "x <=^sp y ?= 'iff' C" := (<?=^sp%O x y C) : order_scope.
Notation "x <=^sp y ?= 'iff' C :> T" := ((x : T) <=^sp (y : T) ?= iff C)
  (only parsing) : order_scope.

Notation ">=<^sp y" := [pred x | >=<^sp%O x y] : order_scope.
Notation ">=<^sp y :> T" := (>=<^sp (y : T)) (only parsing) : order_scope.
Notation "x >=<^sp y" := (>=<^sp%O x y) : order_scope.

Notation "><^sp y" := [pred x | ~~ (>=<^sp%O x y)] : order_scope.
Notation "><^sp y :> T" := (><^sp (y : T)) (only parsing) : order_scope.
Notation "x ><^sp y" := (~~ (><^sp%O x y)) : order_scope.

(* The following Local Notations are here to define the \join^sp_ and         *)
(* \meet^sp_ notations later. Do not remove them.                             *)
Local Notation "\bot" := (@bottom (seqprod_display _) _).
Local Notation "\top" := (@top (seqprod_display _) _).
Local Notation meet := (@meet (seqprod_display _) _).
Local Notation join := (@join (seqprod_display _) _).
Local Notation min := (@min (seqprod_display _) _).
Local Notation max := (@max (seqprod_display _) _).

Notation "x `&^sp` y" :=  (meet x y) : order_scope.
Notation "x `|^sp` y" := (join x y) : order_scope.

Notation "\join^sp_ ( i <- r | P ) F" :=
  (\big[join / \bot]_(i <- r | P%B) F%O) : order_scope.
Notation "\join^sp_ ( i <- r ) F" :=
  (\big[join / \bot]_(i <- r) F%O) : order_scope.
Notation "\join^sp_ ( i | P ) F" :=
  (\big[join / \bot]_(i | P%B) F%O) : order_scope.
Notation "\join^sp_ i F" :=
  (\big[join / \bot]_i F%O) : order_scope.
Notation "\join^sp_ ( i : I | P ) F" :=
  (\big[join / \bot]_(i : I | P%B) F%O) (only parsing) : order_scope.
Notation "\join^sp_ ( i : I ) F" :=
  (\big[join / \bot]_(i : I) F%O) (only parsing) : order_scope.
Notation "\join^sp_ ( m <= i < n | P ) F" :=
 (\big[join / \bot]_(m <= i < n | P%B) F%O) : order_scope.
Notation "\join^sp_ ( m <= i < n ) F" :=
 (\big[join / \bot]_(m <= i < n) F%O) : order_scope.
Notation "\join^sp_ ( i < n | P ) F" :=
 (\big[join / \bot]_(i < n | P%B) F%O) : order_scope.
Notation "\join^sp_ ( i < n ) F" :=
 (\big[join / \bot]_(i < n) F%O) : order_scope.
Notation "\join^sp_ ( i 'in' A | P ) F" :=
 (\big[join / \bot]_(i in A | P%B) F%O) : order_scope.
Notation "\join^sp_ ( i 'in' A ) F" :=
 (\big[join / \bot]_(i in A) F%O) : order_scope.

Notation "\meet^sp_ ( i <- r | P ) F" :=
  (\big[meet / \top]_(i <- r | P%B) F%O) : order_scope.
Notation "\meet^sp_ ( i <- r ) F" :=
  (\big[meet / \top]_(i <- r) F%O) : order_scope.
Notation "\meet^sp_ ( i | P ) F" :=
  (\big[meet / \top]_(i | P%B) F%O) : order_scope.
Notation "\meet^sp_ i F" :=
  (\big[meet / \top]_i F%O) : order_scope.
Notation "\meet^sp_ ( i : I | P ) F" :=
  (\big[meet / \top]_(i : I | P%B) F%O) (only parsing) : order_scope.
Notation "\meet^sp_ ( i : I ) F" :=
  (\big[meet / \top]_(i : I) F%O) (only parsing) : order_scope.
Notation "\meet^sp_ ( m <= i < n | P ) F" :=
 (\big[meet / \top]_(m <= i < n | P%B) F%O) : order_scope.
Notation "\meet^sp_ ( m <= i < n ) F" :=
 (\big[meet / \top]_(m <= i < n) F%O) : order_scope.
Notation "\meet^sp_ ( i < n | P ) F" :=
 (\big[meet / \top]_(i < n | P%B) F%O) : order_scope.
Notation "\meet^sp_ ( i < n ) F" :=
 (\big[meet / \top]_(i < n) F%O) : order_scope.
Notation "\meet^sp_ ( i 'in' A | P ) F" :=
 (\big[meet / \top]_(i in A | P%B) F%O) : order_scope.
Notation "\meet^sp_ ( i 'in' A ) F" :=
 (\big[meet / \top]_(i in A) F%O) : order_scope.

Notation "\min^sp_ i F" :=
  (\big[min/top]_i F) : order_scope.
Notation "\min^sp_ ( i <- r | P ) F" :=
  (\big[min/top]_(i <- r | P%B) F%O) : order_scope.
Notation "\min^sp_ ( i < r ) F" :=
  (\big[min/top]_(i <- r) F%O) : order_scope.
Notation "\min^sp_ ( m <= i < n | P ) F" :=
  (\big[min/top]_(m <= i < n | P%B) F%O) : order_scope.
Notation "\min^sp_ ( m <= i < n ) F" :=
  (\big[min/top]_(m <= i < n) F%O) : order_scope.
Notation "\min^sp_ ( i | P ) F" :=
  (\big[min/top]_(i | P%B) F%O) : order_scope.
Notation "\min^sp_ ( i : t | P ) F" :=
  (\big[min/top]_(i : t | P%B) F%O) (only parsing) : order_scope.
Notation "\min^sp_ ( i : t ) F" :=
  (\big[min/top]_(i : t) F%O) (only parsing) : order_scope.
Notation "\min^sp_ ( i < n | P ) F" :=
  (\big[min/top]_(i < n | P%B) F%O) : order_scope.
Notation "\min^sp_ ( i < n ) F" :=
  (\big[min/top]_(i < n) F%O) : order_scope.
Notation "\min^sp_ ( i 'in' A | P ) F" :=
  (\big[min/top]_(i in A | P%B) F%O) : order_scope.
Notation "\min^sp_ ( i 'in' A ) F" :=
  (\big[min/top]_(i in A) F%O) : order_scope.

Notation "\max^sp_ i F" :=
  (\big[max/bottom]_i F%O) : order_scope.
Notation "\max^sp_ ( i <- r | P ) F" :=
  (\big[max/bottom]_(i <- r | P%B) F%O) : order_scope.
Notation "\max^sp_ ( i < r ) F" :=
  (\big[max/bottom]_(i <- r) F%O) : order_scope.
Notation "\max^sp_ ( m <= i < n | P ) F" :=
  (\big[max/bottom]_(m <= i < n | P%B) F%O) : order_scope.
Notation "\max^sp_ ( m <= i < n ) F" :=
  (\big[max/bottom]_(m <= i < n) F%O) : order_scope.
Notation "\max^sp_ ( i | P ) F" :=
  (\big[max/bottom]_(i | P%B) F%O) : order_scope.
Notation "\max^sp_ ( i : t | P ) F" :=
  (\big[max/bottom]_(i : t | P%B) F%O) (only parsing) : order_scope.
Notation "\max^sp_ ( i : t ) F" :=
  (\big[max/bottom]_(i : t) F%O) (only parsing) : order_scope.
Notation "\max^sp_ ( i < n | P ) F" :=
  (\big[max/bottom]_(i < n | P%B) F%O) : order_scope.
Notation "\max^sp_ ( i < n ) F" :=
  (\big[max/bottom]_(i < n) F%O) : order_scope.
Notation "\max^sp_ ( i 'in' A | P ) F" :=
  (\big[max/bottom]_(i in A | P%B) F%O) : order_scope.
Notation "\max^sp_ ( i 'in' A ) F" :=
  (\big[max/bottom]_(i in A) F%O) : order_scope.

End SeqProdSyntax.

(******************************)
(* Definition of lexi_display *)
(******************************)

Fact lexi_display (disp _ : disp_t) : disp_t. Proof. exact: disp. Qed.

Fact seqlexi_display (disp : disp_t) : disp_t. Proof. exact: disp. Qed.

Module Import LexiSyntax.

Notation "<=^l%O" := (@le (lexi_display _ _) _) : function_scope.
Notation ">=^l%O" := (@ge (lexi_display _ _) _) : function_scope.
Notation ">=^l%O" := (@ge (lexi_display _ _) _) : function_scope.
Notation "<^l%O" := (@lt (lexi_display _ _) _) : function_scope.
Notation ">^l%O" := (@gt (lexi_display _ _) _) : function_scope.
Notation "<?=^l%O" := (@leif (lexi_display _ _) _) : function_scope.
Notation ">=<^l%O" := (@comparable (lexi_display _ _) _) : function_scope.
Notation "><^l%O" := (fun x y => ~~ (@comparable (lexi_display _ _) _ x y)) :
  function_scope.

Notation "<=^l y" := (>=^l%O y) : order_scope.
Notation "<=^l y :> T" := (<=^l (y : T)) (only parsing) : order_scope.
Notation ">=^l y"  := (<=^l%O y) : order_scope.
Notation ">=^l y :> T" := (>=^l (y : T)) (only parsing) : order_scope.

Notation "<^l y" := (>^l%O y) : order_scope.
Notation "<^l y :> T" := (<^l (y : T)) (only parsing) : order_scope.
Notation ">^l y" := (<^l%O y) : order_scope.
Notation ">^l y :> T" := (>^l (y : T)) (only parsing) : order_scope.

Notation "x <=^l y" := (<=^l%O x y) : order_scope.
Notation "x <=^l y :> T" := ((x : T) <=^l (y : T)) (only parsing) : order_scope.
Notation "x >=^l y" := (y <=^l x) (only parsing) : order_scope.
Notation "x >=^l y :> T" := ((x : T) >=^l (y : T)) (only parsing) : order_scope.

Notation "x <^l y"  := (<^l%O x y) : order_scope.
Notation "x <^l y :> T" := ((x : T) <^l (y : T)) (only parsing) : order_scope.
Notation "x >^l y"  := (y <^l x) (only parsing) : order_scope.
Notation "x >^l y :> T" := ((x : T) >^l (y : T)) (only parsing) : order_scope.

Notation "x <=^l y <=^l z" := ((x <=^l y) && (y <=^l z)) : order_scope.
Notation "x <^l y <=^l z" := ((x <^l y) && (y <=^l z)) : order_scope.
Notation "x <=^l y <^l z" := ((x <=^l y) && (y <^l z)) : order_scope.
Notation "x <^l y <^l z" := ((x <^l y) && (y <^l z)) : order_scope.

Notation "x <=^l y ?= 'iff' C" := (<?=^l%O x y C) : order_scope.
Notation "x <=^l y ?= 'iff' C :> T" := ((x : T) <=^l (y : T) ?= iff C)
  (only parsing) : order_scope.

Notation ">=<^l y" := [pred x | >=<^l%O x y] : order_scope.
Notation ">=<^l y :> T" := (>=<^l (y : T)) (only parsing) : order_scope.
Notation "x >=<^l y" := (>=<^l%O x y) : order_scope.

Notation "><^l y" := [pred x | ~~ (>=<^l%O x y)] : order_scope.
Notation "><^l y :> T" := (><^l (y : T)) (only parsing) : order_scope.
Notation "x ><^l y" := (~~ (><^l%O x y)) : order_scope.

Notation meetlexi := (@meet (lexi_display _ _) _).
Notation joinlexi := (@join (lexi_display _ _) _).

Notation "x `&^l` y" :=  (meetlexi x y) : order_scope.
Notation "x `|^l` y" := (joinlexi x y) : order_scope.

(* The following Local Notations are here to define the \join^l_ and \meet^l_ *)
(* notations later. Do not remove them.                                       *)
Local Notation "\bot" := (@bottom (lexi_display _ _) _).
Local Notation "\top" := (@top (lexi_display _ _) _).
Local Notation meet := (@meet (lexi_display _ _) _).
Local Notation join := (@join (lexi_display _ _) _).
Local Notation min := (@min (lexi_display _ _) _).
Local Notation max := (@max (lexi_display _ _) _).

Notation "\join^l_ ( i <- r | P ) F" :=
  (\big[join / \bot]_(i <- r | P%B) F%O) : order_scope.
Notation "\join^l_ ( i <- r ) F" :=
  (\big[join / \bot]_(i <- r) F%O) : order_scope.
Notation "\join^l_ ( i | P ) F" :=
  (\big[join / \bot]_(i | P%B) F%O) : order_scope.
Notation "\join^l_ i F" :=
  (\big[join / \bot]_i F%O) : order_scope.
Notation "\join^l_ ( i : I | P ) F" :=
  (\big[join / \bot]_(i : I | P%B) F%O) (only parsing) : order_scope.
Notation "\join^l_ ( i : I ) F" :=
  (\big[join / \bot]_(i : I) F%O) (only parsing) : order_scope.
Notation "\join^l_ ( m <= i < n | P ) F" :=
 (\big[join / \bot]_(m <= i < n | P%B) F%O) : order_scope.
Notation "\join^l_ ( m <= i < n ) F" :=
 (\big[join / \bot]_(m <= i < n) F%O) : order_scope.
Notation "\join^l_ ( i < n | P ) F" :=
 (\big[join / \bot]_(i < n | P%B) F%O) : order_scope.
Notation "\join^l_ ( i < n ) F" :=
 (\big[join / \bot]_(i < n) F%O) : order_scope.
Notation "\join^l_ ( i 'in' A | P ) F" :=
 (\big[join / \bot]_(i in A | P%B) F%O) : order_scope.
Notation "\join^l_ ( i 'in' A ) F" :=
 (\big[join / \bot]_(i in A) F%O) : order_scope.

Notation "\meet^l_ ( i <- r | P ) F" :=
  (\big[meet / \top]_(i <- r | P%B) F%O) : order_scope.
Notation "\meet^l_ ( i <- r ) F" :=
  (\big[meet / \top]_(i <- r) F%O) : order_scope.
Notation "\meet^l_ ( i | P ) F" :=
  (\big[meet / \top]_(i | P%B) F%O) : order_scope.
Notation "\meet^l_ i F" :=
  (\big[meet / \top]_i F%O) : order_scope.
Notation "\meet^l_ ( i : I | P ) F" :=
  (\big[meet / \top]_(i : I | P%B) F%O) (only parsing) : order_scope.
Notation "\meet^l_ ( i : I ) F" :=
  (\big[meet / \top]_(i : I) F%O) (only parsing) : order_scope.
Notation "\meet^l_ ( m <= i < n | P ) F" :=
 (\big[meet / \top]_(m <= i < n | P%B) F%O) : order_scope.
Notation "\meet^l_ ( m <= i < n ) F" :=
 (\big[meet / \top]_(m <= i < n) F%O) : order_scope.
Notation "\meet^l_ ( i < n | P ) F" :=
 (\big[meet / \top]_(i < n | P%B) F%O) : order_scope.
Notation "\meet^l_ ( i < n ) F" :=
 (\big[meet / \top]_(i < n) F%O) : order_scope.
Notation "\meet^l_ ( i 'in' A | P ) F" :=
 (\big[meet / \top]_(i in A | P%B) F%O) : order_scope.
Notation "\meet^l_ ( i 'in' A ) F" :=
 (\big[meet / \top]_(i in A) F%O) : order_scope.

Notation "\min^l_ i F" :=
  (\big[min/top]_i F) : order_scope.
Notation "\min^l_ ( i <- r | P ) F" :=
  (\big[min/top]_(i <- r | P%B) F%O) : order_scope.
Notation "\min^l_ ( i < r ) F" :=
  (\big[min/top]_(i <- r) F%O) : order_scope.
Notation "\min^l_ ( m <= i < n | P ) F" :=
  (\big[min/top]_(m <= i < n | P%B) F%O) : order_scope.
Notation "\min^l_ ( m <= i < n ) F" :=
  (\big[min/top]_(m <= i < n) F%O) : order_scope.
Notation "\min^l_ ( i | P ) F" :=
  (\big[min/top]_(i | P%B) F%O) : order_scope.
Notation "\min^l_ ( i : t | P ) F" :=
  (\big[min/top]_(i : t | P%B) F%O) (only parsing) : order_scope.
Notation "\min^l_ ( i : t ) F" :=
  (\big[min/top]_(i : t) F%O) (only parsing) : order_scope.
Notation "\min^l_ ( i < n | P ) F" :=
  (\big[min/top]_(i < n | P%B) F%O) : order_scope.
Notation "\min^l_ ( i < n ) F" :=
  (\big[min/top]_(i < n) F%O) : order_scope.
Notation "\min^l_ ( i 'in' A | P ) F" :=
  (\big[min/top]_(i in A | P%B) F%O) : order_scope.
Notation "\min^l_ ( i 'in' A ) F" :=
  (\big[min/top]_(i in A) F%O) : order_scope.

Notation "\max^l_ i F" :=
  (\big[max/bottom]_i F%O) : order_scope.
Notation "\max^l_ ( i <- r | P ) F" :=
  (\big[max/bottom]_(i <- r | P%B) F%O) : order_scope.
Notation "\max^l_ ( i < r ) F" :=
  (\big[max/bottom]_(i <- r) F%O) : order_scope.
Notation "\max^l_ ( m <= i < n | P ) F" :=
  (\big[max/bottom]_(m <= i < n | P%B) F%O) : order_scope.
Notation "\max^l_ ( m <= i < n ) F" :=
  (\big[max/bottom]_(m <= i < n) F%O) : order_scope.
Notation "\max^l_ ( i | P ) F" :=
  (\big[max/bottom]_(i | P%B) F%O) : order_scope.
Notation "\max^l_ ( i : t | P ) F" :=
  (\big[max/bottom]_(i : t | P%B) F%O) (only parsing) : order_scope.
Notation "\max^l_ ( i : t ) F" :=
  (\big[max/bottom]_(i : t) F%O) (only parsing) : order_scope.
Notation "\max^l_ ( i < n | P ) F" :=
  (\big[max/bottom]_(i < n | P%B) F%O) : order_scope.
Notation "\max^l_ ( i < n ) F" :=
  (\big[max/bottom]_(i < n) F%O) : order_scope.
Notation "\max^l_ ( i 'in' A | P ) F" :=
  (\big[max/bottom]_(i in A | P%B) F%O) : order_scope.
Notation "\max^l_ ( i 'in' A ) F" :=
  (\big[max/bottom]_(i in A) F%O) : order_scope.

End LexiSyntax.

Module Import SeqLexiSyntax.

Notation "<=^l%O" := (@le (seqlexi_display _ _) _) : function_scope.
Notation ">=^l%O" := (@ge (seqlexi_display _ _) _) : function_scope.
Notation ">=^l%O" := (@ge (seqlexi_display _ _) _) : function_scope.
Notation "<^l%O" := (@lt (seqlexi_display _ _) _) : function_scope.
Notation ">^l%O" := (@gt (seqlexi_display _ _) _) : function_scope.
Notation "<?=^l%O" := (@leif (seqlexi_display _ _) _) : function_scope.
Notation ">=<^l%O" := (@comparable (seqlexi_display _ _) _) : function_scope.
Notation "><^l%O" := (fun x y => ~~ (@comparable (seqlexi_display _ _) _ x y)) :
  function_scope.

Notation "<=^l y" := (>=^l%O y) : order_scope.
Notation "<=^l y :> T" := (<=^l (y : T)) (only parsing) : order_scope.
Notation ">=^l y"  := (<=^l%O y) : order_scope.
Notation ">=^l y :> T" := (>=^l (y : T)) (only parsing) : order_scope.

Notation "<^l y" := (>^l%O y) : order_scope.
Notation "<^l y :> T" := (<^l (y : T)) (only parsing) : order_scope.
Notation ">^l y" := (<^l%O y) : order_scope.
Notation ">^l y :> T" := (>^l (y : T)) (only parsing) : order_scope.

Notation "x <=^l y" := (<=^l%O x y) : order_scope.
Notation "x <=^l y :> T" := ((x : T) <=^l (y : T)) (only parsing) : order_scope.
Notation "x >=^l y" := (y <=^l x) (only parsing) : order_scope.
Notation "x >=^l y :> T" := ((x : T) >=^l (y : T)) (only parsing) : order_scope.

Notation "x <^l y"  := (<^l%O x y) : order_scope.
Notation "x <^l y :> T" := ((x : T) <^l (y : T)) (only parsing) : order_scope.
Notation "x >^l y"  := (y <^l x) (only parsing) : order_scope.
Notation "x >^l y :> T" := ((x : T) >^l (y : T)) (only parsing) : order_scope.

Notation "x <=^l y <=^l z" := ((x <=^l y) && (y <=^l z)) : order_scope.
Notation "x <^l y <=^l z" := ((x <^l y) && (y <=^l z)) : order_scope.
Notation "x <=^l y <^l z" := ((x <=^l y) && (y <^l z)) : order_scope.
Notation "x <^l y <^l z" := ((x <^l y) && (y <^l z)) : order_scope.

Notation "x <=^l y ?= 'iff' C" := (<?=^l%O x y C) : order_scope.
Notation "x <=^l y ?= 'iff' C :> T" := ((x : T) <=^l (y : T) ?= iff C)
  (only parsing) : order_scope.

Notation ">=<^l y" := [pred x | >=<^l%O x y] : order_scope.
Notation ">=<^l y :> T" := (>=<^l (y : T)) (only parsing) : order_scope.
Notation "x >=<^l y" := (>=<^l%O x y) : order_scope.

Notation "><^l y" := [pred x | ~~ (>=<^l%O x y)] : order_scope.
Notation "><^l y :> T" := (><^l (y : T)) (only parsing) : order_scope.
Notation "x ><^l y" := (~~ (><^l%O x y)) : order_scope.

Notation meetlexi := (@meet (seqlexi_display _) _).
Notation joinlexi := (@join (seqlexi_display _) _).

Notation "x `&^l` y" :=  (meetlexi x y) : order_scope.
Notation "x `|^l` y" := (joinlexi x y) : order_scope.

(* The following Local Notations are here to define the \join^l_ and \meet^l_ *)
(* notations later. Do not remove them.                                       *)
Local Notation "\bot" := (@bottom (lexi_display _ _) _).
Local Notation "\top" := (@top (lexi_display _ _) _).
Local Notation meet := (@meet (lexi_display _ _) _).
Local Notation join := (@join (lexi_display _ _) _).
Local Notation min := (@min (lexi_display _ _) _).
Local Notation max := (@max (lexi_display _ _) _).

Notation "\join^l_ ( i <- r | P ) F" :=
  (\big[join / \bot]_(i <- r | P%B) F%O) : order_scope.
Notation "\join^l_ ( i <- r ) F" :=
  (\big[join / \bot]_(i <- r) F%O) : order_scope.
Notation "\join^l_ ( i | P ) F" :=
  (\big[join / \bot]_(i | P%B) F%O) : order_scope.
Notation "\join^l_ i F" :=
  (\big[join / \bot]_i F%O) : order_scope.
Notation "\join^l_ ( i : I | P ) F" :=
  (\big[join / \bot]_(i : I | P%B) F%O) (only parsing) : order_scope.
Notation "\join^l_ ( i : I ) F" :=
  (\big[join / \bot]_(i : I) F%O) (only parsing) : order_scope.
Notation "\join^l_ ( m <= i < n | P ) F" :=
 (\big[join / \bot]_(m <= i < n | P%B) F%O) : order_scope.
Notation "\join^l_ ( m <= i < n ) F" :=
 (\big[join / \bot]_(m <= i < n) F%O) : order_scope.
Notation "\join^l_ ( i < n | P ) F" :=
 (\big[join / \bot]_(i < n | P%B) F%O) : order_scope.
Notation "\join^l_ ( i < n ) F" :=
 (\big[join / \bot]_(i < n) F%O) : order_scope.
Notation "\join^l_ ( i 'in' A | P ) F" :=
 (\big[join / \bot]_(i in A | P%B) F%O) : order_scope.
Notation "\join^l_ ( i 'in' A ) F" :=
 (\big[join / \bot]_(i in A) F%O) : order_scope.

Notation "\meet^l_ ( i <- r | P ) F" :=
  (\big[meet / \top]_(i <- r | P%B) F%O) : order_scope.
Notation "\meet^l_ ( i <- r ) F" :=
  (\big[meet / \top]_(i <- r) F%O) : order_scope.
Notation "\meet^l_ ( i | P ) F" :=
  (\big[meet / \top]_(i | P%B) F%O) : order_scope.
Notation "\meet^l_ i F" :=
  (\big[meet / \top]_i F%O) : order_scope.
Notation "\meet^l_ ( i : I | P ) F" :=
  (\big[meet / \top]_(i : I | P%B) F%O) (only parsing) : order_scope.
Notation "\meet^l_ ( i : I ) F" :=
  (\big[meet / \top]_(i : I) F%O) (only parsing) : order_scope.
Notation "\meet^l_ ( m <= i < n | P ) F" :=
 (\big[meet / \top]_(m <= i < n | P%B) F%O) : order_scope.
Notation "\meet^l_ ( m <= i < n ) F" :=
 (\big[meet / \top]_(m <= i < n) F%O) : order_scope.
Notation "\meet^l_ ( i < n | P ) F" :=
 (\big[meet / \top]_(i < n | P%B) F%O) : order_scope.
Notation "\meet^l_ ( i < n ) F" :=
 (\big[meet / \top]_(i < n) F%O) : order_scope.
Notation "\meet^l_ ( i 'in' A | P ) F" :=
 (\big[meet / \top]_(i in A | P%B) F%O) : order_scope.
Notation "\meet^l_ ( i 'in' A ) F" :=
 (\big[meet / \top]_(i in A) F%O) : order_scope.

Notation "\min^l_ i F" :=
  (\big[min/top]_i F) : order_scope.
Notation "\min^l_ ( i <- r | P ) F" :=
  (\big[min/top]_(i <- r | P%B) F%O) : order_scope.
Notation "\min^l_ ( i < r ) F" :=
  (\big[min/top]_(i <- r) F%O) : order_scope.
Notation "\min^l_ ( m <= i < n | P ) F" :=
  (\big[min/top]_(m <= i < n | P%B) F%O) : order_scope.
Notation "\min^l_ ( m <= i < n ) F" :=
  (\big[min/top]_(m <= i < n) F%O) : order_scope.
Notation "\min^l_ ( i | P ) F" :=
  (\big[min/top]_(i | P%B) F%O) : order_scope.
Notation "\min^l_ ( i : t | P ) F" :=
  (\big[min/top]_(i : t | P%B) F%O) (only parsing) : order_scope.
Notation "\min^l_ ( i : t ) F" :=
  (\big[min/top]_(i : t) F%O) (only parsing) : order_scope.
Notation "\min^l_ ( i < n | P ) F" :=
  (\big[min/top]_(i < n | P%B) F%O) : order_scope.
Notation "\min^l_ ( i < n ) F" :=
  (\big[min/top]_(i < n) F%O) : order_scope.
Notation "\min^l_ ( i 'in' A | P ) F" :=
  (\big[min/top]_(i in A | P%B) F%O) : order_scope.
Notation "\min^l_ ( i 'in' A ) F" :=
  (\big[min/top]_(i in A) F%O) : order_scope.

Notation "\max^l_ i F" :=
  (\big[max/bottom]_i F%O) : order_scope.
Notation "\max^l_ ( i <- r | P ) F" :=
  (\big[max/bottom]_(i <- r | P%B) F%O) : order_scope.
Notation "\max^l_ ( i < r ) F" :=
  (\big[max/bottom]_(i <- r) F%O) : order_scope.
Notation "\max^l_ ( m <= i < n | P ) F" :=
  (\big[max/bottom]_(m <= i < n | P%B) F%O) : order_scope.
Notation "\max^l_ ( m <= i < n ) F" :=
  (\big[max/bottom]_(m <= i < n) F%O) : order_scope.
Notation "\max^l_ ( i | P ) F" :=
  (\big[max/bottom]_(i | P%B) F%O) : order_scope.
Notation "\max^l_ ( i : t | P ) F" :=
  (\big[max/bottom]_(i : t | P%B) F%O) (only parsing) : order_scope.
Notation "\max^l_ ( i : t ) F" :=
  (\big[max/bottom]_(i : t) F%O) (only parsing) : order_scope.
Notation "\max^l_ ( i < n | P ) F" :=
  (\big[max/bottom]_(i < n | P%B) F%O) : order_scope.
Notation "\max^l_ ( i < n ) F" :=
  (\big[max/bottom]_(i < n) F%O) : order_scope.
Notation "\max^l_ ( i 'in' A | P ) F" :=
  (\big[max/bottom]_(i in A | P%B) F%O) : order_scope.
Notation "\max^l_ ( i 'in' A ) F" :=
  (\big[max/bottom]_(i in A) F%O) : order_scope.

End SeqLexiSyntax.

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

(*********************************************************)
(* We declare lexicographic ordering on dependent pairs. *)
(*********************************************************)

Module SigmaOrder.
Section SigmaOrder.

Context {disp1 disp2 : disp_t}.

Section POrder.
Context (T : porderType disp1) (T' : T -> porderType disp2).
Implicit Types (x y : {t : T & T' t}).

Definition le x y := (tag x <= tag y) &&
  ((tag x >= tag y) ==> (tagged x <= tagged_as x y)).
Definition lt x y := (tag x <= tag y) &&
  ((tag x >= tag y) ==> (tagged x < tagged_as x y)).

Fact refl : reflexive le.
Proof. by move=> [x x']; rewrite /le tagged_asE/= !lexx. Qed.

Fact anti : antisymmetric le.
Proof.
rewrite /le => -[x x'] [y y']/=; case: comparableP => //= eq_xy.
by case: _ / eq_xy in y' *; rewrite !tagged_asE => /le_anti ->.
Qed.

Fact trans : transitive le.
Proof.
move=> [y y'] [x x'] [z z'] /andP[/= lexy lexy'] /andP[/= leyz leyz'].
rewrite /= /le (le_trans lexy) //=; apply/implyP => lezx.
elim: _ / (@le_anti _ _ x y) in y' z' lexy' leyz' *; last first.
  by rewrite lexy (le_trans leyz).
elim: _ / (@le_anti _ _ x z) in z' leyz' *; last by rewrite (le_trans lexy).
by rewrite lexx !tagged_asE/= in lexy' leyz' *; rewrite (le_trans lexy').
Qed.

Fact lt_le_def x y : lt x y = le x y && ~~ le y x.
Proof.
rewrite /lt /le; case: x y => [x x'] [y y']//=.
case: (comparableP x y) => //= xy.
by subst y; rewrite !tagged_asE lt_le_def.
Qed.

#[export] HB.instance Definition _ :=
  isPreorder.Build disp2 {t : T & T' t} lt_le_def refl trans.
#[export] HB.instance Definition _ :=
  Preorder_isPOrder.Build disp2 {t : T & T' t} anti.

Lemma leEsig x y : (x <= y) =
  (tag x <= tag y) && ((tag x >= tag y) ==> (tagged x <= tagged_as x y)).
Proof. by []. Qed.

Lemma ltEsig x y : (x < y) =
  (tag x <= tag y) && ((tag x >= tag y) ==> (tagged x < tagged_as x y)).
Proof. by []. Qed.

Lemma le_Taggedl x (u : T' (tag x)) : (Tagged T' u <= x) = (u <= tagged x).
Proof. by case: x => [t v]/= in u *; rewrite leEsig/= lexx/= tagged_asE. Qed.

Lemma le_Taggedr x (u : T' (tag x)) : (x <= Tagged T' u) = (tagged x <= u).
Proof. by case: x => [t v]/= in u *; rewrite leEsig/= lexx/= tagged_asE. Qed.

Lemma lt_Taggedl x (u : T' (tag x)) : (Tagged T' u < x) = (u < tagged x).
Proof. by case: x => [t v]/= in u *; rewrite ltEsig/= lexx/= tagged_asE. Qed.

Lemma lt_Taggedr x (u : T' (tag x)) : (x < Tagged T' u) = (tagged x < u).
Proof. by case: x => [t v]/= in u *; rewrite ltEsig/= lexx/= tagged_asE. Qed.

End POrder.

Section BPOrder.
Context (T : bPOrderType disp1) (T' : T -> bPOrderType disp2).

Fact le0x (x : {t : T & T' t}) : Tagged T' (\bot : T' \bot) <= x.
Proof. by rewrite leEsig /= !le0x implybT. Qed.

#[export] HB.instance Definition _ := hasBottom.Build _ {t : T & T' t} le0x.

Lemma botEsig : \bot = Tagged T' (\bot : T' \bot). Proof. by []. Qed.

End BPOrder.

Section TPOrder.
Context (T : tPOrderType disp1) (T' : T -> tPOrderType disp2).

Fact lex1 (x : {t : T & T' t}) : x <= Tagged T' (\top : T' \top).
Proof.
rewrite leEsig /=; case: comparableP (lex1 (tag x)) => //=.
by case: x => //= x px x0; rewrite x0 in px *; rewrite tagged_asE lex1.
Qed.

#[export] HB.instance Definition _ := hasTop.Build _ {t : T & T' t} lex1.

Lemma topEsig : \top = Tagged T' (\top : T' \top). Proof. by []. Qed.

End TPOrder.

Section Total.
Context (T : orderType disp1) (T' : T -> orderType disp2).
Implicit Types (x y : {t : T & T' t}).

Fact total : total (<=%O : rel {t : T & T' t}).
Proof.
move=> x y; rewrite !leEsig; case: (ltgtP (tag x) (tag y)) => //=.
case: x y => [x x'] [y y']/= eqxy; elim: _ /eqxy in y' *.
by rewrite !tagged_asE le_total.
Qed.

#[export] HB.instance Definition _ :=
  POrder_isTotal.Build _ {t : T & T' t} total.

End Total.

(* FIXME: use HB.saturate *)
#[export] HB.instance Definition _
  (T : bOrderType disp1) (T' : T -> bOrderType disp2) :=
    POrder.on {t : T & T' t}.
#[export] HB.instance Definition _
  (T : tOrderType disp1) (T' : T -> tOrderType disp2) :=
    POrder.on {t : T & T' t}.
#[export] HB.instance Definition _
  (T : tbOrderType disp1) (T' : T -> tbOrderType disp2) :=
    POrder.on {t : T & T' t}.

#[export] HB.instance Definition _
  (T : finPOrderType disp1) (T' : T -> finPOrderType disp2) :=
    POrder.on {t : T & T' t}.
#[export] HB.instance Definition _
  (T : finBPOrderType disp1) (T' : T -> finBPOrderType disp2) :=
    POrder.on {t : T & T' t}.
#[export] HB.instance Definition _
  (T : finTPOrderType disp1) (T' : T -> finTPOrderType disp2) :=
    POrder.on {t : T & T' t}.
#[export] HB.instance Definition _
  (T : finTBPOrderType disp1) (T' : T -> finTBPOrderType disp2) :=
    POrder.on {t : T & T' t}.
#[export] HB.instance Definition _
  (T : finOrderType disp1) (T' : T -> finOrderType disp2) :=
    POrder.on {t : T & T' t}.
#[export] HB.instance Definition _
  (T : finTBOrderType disp1) (T' : T -> finTBOrderType disp2) :=
    POrder.on {t : T & T' t}.
(* /FIXME *)

End SigmaOrder.

Module Exports.
HB.reexport SigmaOrder.
Definition leEsig := @leEsig.
Definition ltEsig := @ltEsig.
Definition le_Taggedl := @le_Taggedl.
Definition lt_Taggedl := @lt_Taggedl.
Definition le_Taggedr := @le_Taggedr.
Definition lt_Taggedr := @lt_Taggedr.
Definition topEsig := @topEsig.
Definition botEsig := @botEsig.
End Exports.
End SigmaOrder.
HB.export SigmaOrder.Exports.

(*************************************************)
(* We declare an alias of the cartesian product, *)
(* which has canonical lexicographic order.      *)
(*************************************************)

Module ProdLexiOrder.

Local Open Scope type_scope. (* FIXME *)

Definition type (disp : disp_t) (T T' : Type) := T * T'.
Definition type_
  (disp1 disp2 : disp_t) (T : preorderType disp1) (T' : preorderType disp2) :=
  type (lexi_display disp1 disp2) T T'.

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

Let le x y := (x.1 <= y.1) && ((x.1 >= y.1) ==> (x.2 <= y.2)).
Let lt x y := (x.1 <= y.1) && ((x.1 >= y.1) ==> (x.2 < y.2)).

Fact refl : reflexive le.
Proof. by move=> ?; rewrite /le !lexx. Qed.

Fact trans : transitive le.
Proof.
move=> y x z /andP [hxy /implyP hxy'] /andP [hyz /implyP hyz'].
rewrite /le (le_trans hxy) //=; apply/implyP => hzx.
by apply/le_trans/hxy'/(le_trans hyz): (hyz' (le_trans hzx hxy)).
Qed.

Fact lt_le_def x y : lt x y = le x y && ~~ le y x.
Proof.
rewrite /lt /le; case: x y => [x1 x2] [y1 y2]/=.
case/boolP: (x1 <= y1); case/boolP: (y1 <= x1) => //= _ _.
exact/lt_le_def.
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

Definition le x y := (x.1 <= y.1) && ((x.1 >= y.1) ==> (x.2 <= y.2)).
Definition lt x y := (x.1 <= y.1) && ((x.1 >= y.1) ==> (x.2 < y.2)).

#[export] HB.instance Definition _ :=
  @isDuallyPreorder.Build disp3 (T1 * T2) le lt
    (@lt_le_def _ _ T1' T2') (@lt_le_def _ _ T1^d T2^d)
    (@refl _ _ T1' T2') (@refl _ _ T1^d T2^d)
    (@trans _ _ T1' T2') (@trans _ _ T1^d T2^d).

Lemma leEprodlexi x y :
  (x <= y) = (x.1 <= y.1) && ((x.1 >= y.1) ==> (x.2 <= y.2)).
Proof. by []. Qed.

Lemma ltEprodlexi x y :
  (x < y) = (x.1 <= y.1) && ((x.1 >= y.1) ==> (x.2 < y.2)).
Proof. by []. Qed.

Lemma lexi_pair (x1 y1 : T1) (x2 y2 : T2) :
  ((x1, x2) <= (y1, y2) :> T1 * T2) = (x1 <= y1) && ((x1 >= y1) ==> (x2 <= y2)).
Proof. by []. Qed.

Lemma ltxi_pair (x1 y1 : T1) (x2 y2 : T2) :
  ((x1, x2) < (y1, y2) :> T1 * T2) = (x1 <= y1) && ((x1 >= y1) ==> (x2 < y2)).
Proof. by []. Qed.

End Preorder.

Lemma sub_prod_lexi (disp1 disp2 disp3 disp4 : disp_t)
  (T1 : preorderType disp1) (T2 : preorderType disp2) :
  subrel (<=%O : rel (T1 *prod[disp3] T2)) (<=%O : rel (type disp4 T1 T2)).
Proof.
case=> [x1 x2] [y1 y2]; rewrite leEprod leEprodlexi /= => /andP[] -> ->.
exact: implybT.
Qed.

Section BPreorder.
Context (disp1 disp2 : disp_t).
Context (T1 : bPreorderType disp1) (T2 : bPreorderType disp2).
Local Notation "T1 * T2" := (type (Disp tt tt) T1 T2) : type_scope.
Implicit Types (x : T1 * T2).

Fact le0x x : (\bot, \bot) <= x :> T1 * T2.
Proof. by rewrite leEprodlexi !le0x implybT. Qed.

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

Lemma botEprodlexi : \bot = (\bot, \bot) :> T1 * T2. Proof. by []. Qed.

End BPreorder.

Section TPreorder.
Context (disp1 disp2 disp3 : disp_t).
Context (T1 : tPreorderType disp1) (T2 : tPreorderType disp2).
Local Notation "T1 * T2" := (type disp3 T1 T2) : type_scope.

#[export] HB.instance Definition _ :=
  @hasTop.Build disp3 (T1 * T2) (\top, \top) (@le0x _ _ T1^d T2^d).

Lemma topEprodlexi : \top = (\top, \top) :> T1 * T2. Proof. by []. Qed.

End TPreorder.

Section POrder.
Context (disp1 disp2 disp3 : disp_t).
Context (T1 : porderType disp1) (T2 : porderType disp2).

Fact anti : antisymmetric (@le disp1 disp2 disp2 T1 T2).
Proof.
by rewrite /le => -[x x'] [y y'] /=; case: comparableP => //= -> /le_anti->.
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

End POrder.

Section Total.
Context (disp1 disp2 disp3 : disp_t).
Context (T1 : orderType disp1) (T2 : orderType disp2).
Local Notation "T1 * T2" := (type disp3 T1 T2) : type_scope.

Fact total : total (<=%O : rel (T1 * T2)).
Proof.
by move=> x y; rewrite !leEprodlexi; case: ltgtP => //= _; exact: le_total.
Qed.

(* FIXME: In order to dualize this instance, we have to dualize the           *)
(* [POrder_isTotal] factory. However, [min] and max are not definitional dual *)
(* (while [min x y] and [max y x] are).                                       *)
#[export] HB.instance Definition _ := POrder_isTotal.Build _ (T1 * T2) total.

End Total.

(* FIXME: use HB.saturate *)
Section ProdLexiOrder.
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
  (T1 : bOrderType disp1) (T2 : bOrderType disp2) :=
    Total.on (type disp3 T1 T2).
#[export] HB.instance Definition _
  (T1 : tOrderType disp1) (T2 : tOrderType disp2) :=
    Total.on (type disp3 T1 T2).
#[export] HB.instance Definition _
  (T1 : tbOrderType disp1) (T2 : tbOrderType disp2) :=
    Total.on (type disp3 T1 T2).
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
  (T1 : finOrderType disp1) (T2 : finOrderType disp2) :=
    POrder.on (type disp3 T1 T2).
#[export] HB.instance Definition _
  (T1 : finTBOrderType disp1) (T2 : finTBOrderType disp2) :=
    POrder.on (type disp3 T1 T2).

End ProdLexiOrder.
(* /FIXME *)

Module Exports.

HB.reexport ProdLexiOrder.

Notation "T *lexi[ d ] T'" := (type d T T')
  (at level 70, d at next level, format "T  *lexi[ d ]  T'") : type_scope.
Notation "T *l T'" := (type_ T T')
  (at level 70, format "T  *l  T'") : type_scope.

Definition leEprodlexi := @leEprodlexi.
Definition ltEprodlexi := @ltEprodlexi.
Definition lexi_pair := @lexi_pair.
Definition ltxi_pair := @ltxi_pair.
Definition topEprodlexi := @topEprodlexi.
Definition botEprodlexi := @botEprodlexi.
Definition sub_prod_lexi := @sub_prod_lexi.

End Exports.
End ProdLexiOrder.
HB.export ProdLexiOrder.Exports.

Module DefaultProdLexiOrder.
Section DefaultProdLexiOrder.
Context {disp1 disp2 : disp_t}.

Let prodlexi T1 T2 := T1 *lexi[lexi_display disp1 disp2] T2.

(* FIXME: Scopes of arguments are broken in several places.                   *)
(* FIXME: Declaring a bunch of copies is still a bit painful.                 *)
HB.instance Definition _ (T1 : preorderType disp1) (T2 : preorderType disp2) :=
  Preorder.copy (T1 * T2)%type (prodlexi T1 T2).
HB.instance Definition _ (T1 : bPreorderType disp1) (T2 : bPreorderType disp2) :=
  BPreorder.copy (T1 * T2)%type (prodlexi T1 T2).
HB.instance Definition _ (T1 : tPreorderType disp1) (T2 : tPreorderType disp2) :=
  TPreorder.copy (T1 * T2)%type (prodlexi T1 T2).
HB.instance Definition _ (T1 : tbPreorderType disp1) (T2 : tbPreorderType disp2) :=
  TBPreorder.copy (T1 * T2)%type (prodlexi T1 T2).
HB.instance Definition _ (T1 : porderType disp1) (T2 : porderType disp2) :=
  POrder.copy (T1 * T2)%type (prodlexi T1 T2).
HB.instance Definition _ (T1 : bPOrderType disp1) (T2 : bPOrderType disp2) :=
  BPOrder.copy (T1 * T2)%type (prodlexi T1 T2).
HB.instance Definition _ (T1 : tPOrderType disp1) (T2 : tPOrderType disp2) :=
  TPOrder.copy (T1 * T2)%type (prodlexi T1 T2).
HB.instance Definition _ (T1 : tbPOrderType disp1) (T2 : tbPOrderType disp2) :=
  TBPOrder.copy (T1 * T2)%type (prodlexi T1 T2).
HB.instance Definition _ (T1 : orderType disp1) (T2 : orderType disp2) :=
  Total.copy (T1 * T2)%type (prodlexi T1 T2).
HB.instance Definition _ (T1 : bOrderType disp1) (T2 : bOrderType disp2) :=
  BTotal.copy (T1 * T2)%type (prodlexi T1 T2).
HB.instance Definition _ (T1 : tOrderType disp1) (T2 : tOrderType disp2) :=
  TTotal.copy (T1 * T2)%type (prodlexi T1 T2).
HB.instance Definition _ (T1 : tbOrderType disp1) (T2 : tbOrderType disp2) :=
  TBTotal.copy (T1 * T2)%type (prodlexi T1 T2).
HB.instance Definition _
  (T1 : finPreorderType disp1) (T2 : finPreorderType disp2) :=
  FinPreorder.copy (T1 * T2)%type (prodlexi T1 T2).
HB.instance Definition _
  (T1 : finBPreorderType disp1) (T2 : finBPreorderType disp2) :=
  FinBPreorder.copy (T1 * T2)%type (prodlexi T1 T2).
HB.instance Definition _
  (T1 : finTPreorderType disp1) (T2 : finTPreorderType disp2) :=
  FinTPreorder.copy (T1 * T2)%type (prodlexi T1 T2).
HB.instance Definition _
  (T1 : finTBPreorderType disp1) (T2 : finTBPreorderType disp2) :=
  FinTBPreorder.copy (T1 * T2)%type (prodlexi T1 T2).
HB.instance Definition _
  (T1 : finPOrderType disp1) (T2 : finPOrderType disp2) :=
  FinPOrder.copy (T1 * T2)%type (prodlexi T1 T2).
HB.instance Definition _
  (T1 : finBPOrderType disp1) (T2 : finBPOrderType disp2) :=
  FinBPOrder.copy (T1 * T2)%type (prodlexi T1 T2).
HB.instance Definition _
  (T1 : finTPOrderType disp1) (T2 : finTPOrderType disp2) :=
  FinTPOrder.copy (T1 * T2)%type (prodlexi T1 T2).
HB.instance Definition _
  (T1 : finTBPOrderType disp1) (T2 : finTBPOrderType disp2) :=
  FinTBPOrder.copy (T1 * T2)%type (prodlexi T1 T2).
HB.instance Definition _
  (T1 : finOrderType disp1) (T2 : finOrderType disp2) :=
  FinTotal.copy (T1 * T2)%type (prodlexi T1 T2).
HB.instance Definition _
  (T1 : finTBOrderType disp1) (T2 : finTBOrderType disp2) :=
  FinTBTotal.copy (T1 * T2)%type (prodlexi T1 T2).

End DefaultProdLexiOrder.
End DefaultProdLexiOrder.

(*****************************************)
(* We declare an alias of the sequences, *)
(* which has canonical product order.    *)
(*****************************************)

Module SeqProdOrder.
Section SeqProdOrder.

Definition type (disp : disp_t) T := seq T.
Definition type_ (disp : disp_t) (T : preorderType disp) :=
  type (seqprod_display disp) T.

Context {disp disp' : disp_t}.

Local Notation seq := (type disp').

#[export] HB.instance Definition _ (T : eqType) := Equality.on (seq T).
#[export] HB.instance Definition _ (T : choiceType) := Choice.on (seq T).
#[export] HB.instance Definition _ (T : countType) := Countable.on (seq T).

Section Preorder.
Context (T : preorderType disp).
Implicit Types (s : seq T).

Fixpoint le s1 s2 := if s1 isn't x1 :: s1' then true else
                     if s2 isn't x2 :: s2' then false else
                     (x1 <= x2) && le s1' s2'.

Fact refl : reflexive le. Proof. by elim=> //= ? ? ?; rewrite !lexx. Qed.

Fact trans : transitive le.
Proof.
elim=> [|y ys ihs] [|x xs] [|z zs] //= /andP[xy xys] /andP[yz yzs].
by rewrite (le_trans xy)// ihs.
Qed.

#[export] HB.instance Definition _ :=
  isPreorder.Build disp' (seq T) (rrefl _) refl trans.

Lemma leEseq s1 s2 : (s1 <= s2) = if s1 isn't x1 :: s1' then true else
                                  if s2 isn't x2 :: s2' then false else
                                  (x1 <= x2) && (s1' <= s2' :> seq _).
Proof. by case: s1. Qed.

Lemma le0s s : [::] <= s :> seq _. Proof. by []. Qed.

Lemma les0 s : (s <= [::]) = (s == [::]). Proof. by rewrite leEseq. Qed.

Lemma le_cons x1 s1 x2 s2 :
   (x1 :: s1 <= x2 :: s2 :> seq _) = (x1 <= x2) && (s1 <= s2).
Proof. by []. Qed.

#[export] HB.instance Definition _ := hasBottom.Build _ (seq T) le0s.

Lemma botEseq : \bot = [::] :> seq T.
Proof. by []. Qed.
End Preorder.

Section POrder.
Variable T : porderType disp.
Implicit Types s : seq T.

Fact anti : antisymmetric (@le T).
Proof.
by elim=> [|x s ihs] [|y s'] //=; rewrite andbACA => /andP[/le_anti-> /ihs->].
Qed.

#[export] HB.instance Definition _ :=
  Preorder_isPOrder.Build disp' (seq T) anti.

End POrder.

Section MeetSemilattice.
Context (T : meetSemilatticeType disp).
Implicit Types (s : seq T).

Fixpoint meet s1 s2 :=
  match s1, s2 with
    | x1 :: s1', x2 :: s2' => (x1 `&` x2) :: meet s1' s2'
    | _, _ => [::]
  end.

Fact lexI s1 s2 s3 : (s1 <= meet s2 s3) = (s1 <= s2) && (s1 <= s3).
Proof.
elim: s1 s2 s3 => [|x s1 IHs1] [|y s2] [|z s3] //=; first by rewrite andbF.
by rewrite leEseq lexI IHs1 andbACA.
Qed.

#[export] HB.instance Definition _ :=
  @POrder_isMeetSemilattice.Build _ (seq T) meet lexI.

Lemma meetEseq s1 s2 : s1 `&` s2 =  [seq x.1 `&` x.2 | x <- zip s1 s2].
Proof. by elim: s1 s2 => [|x s1 ihs1] [|y s2]//=; rewrite -ihs1. Qed.

Lemma meet_cons x1 s1 x2 s2 :
  (x1 :: s1 : seq T) `&` (x2 :: s2) = (x1 `&` x2) :: s1 `&` s2.
Proof. by []. Qed.

End MeetSemilattice.

Section JoinSemilattice.
Context (T : joinSemilatticeType disp).
Implicit Types (s : seq T).

Fixpoint join s1 s2 :=
  match s1, s2 with
    | [::], _ => s2 | _, [::] => s1
    | x1 :: s1', x2 :: s2' => (x1 `|` x2) :: join s1' s2'
  end.

Fact leUx s1 s2 s3 : (join s1 s2 <= s3) = (s1 <= s3) && (s2 <= s3).
Proof.
elim : s1 s2 s3 => [|x s1 IHs1] [|y s2] [|z s3] //=; first by rewrite andbT.
by rewrite leEseq leUx IHs1 andbACA.
Qed.

#[export] HB.instance Definition _ :=
  @POrder_isJoinSemilattice.Build _ (seq T) join leUx.

Lemma joinEseq s1 s2 : s1 `|` s2 =
  match s1, s2 with
    | [::], _ => s2 | _, [::] => s1
    | x1 :: s1', x2 :: s2' => (x1 `|` x2) :: ((s1' : seq _) `|` s2')
  end.
Proof. by case: s1. Qed.

Lemma join_cons x1 s1 x2 s2 :
  (x1 :: s1 : seq T) `|` (x2 :: s2) = (x1 `|` x2) :: s1 `|` s2.
Proof. by []. Qed.

End JoinSemilattice.

(* FIXME: use HB.saturate *)
#[export] HB.instance Definition _ (T : latticeType disp) := POrder.on (seq T).
(* /FIXME *)

Section DistrLattice.
Context (T : distrLatticeType disp).

Fact meetUl : left_distributive (@meet T) (@join T).
Proof. by elim=> [|? ? ih] [|? ?] [|? ?] //=; rewrite meetUl ih. Qed.

#[export] HB.instance Definition _ :=
  Lattice_Meet_isDistrLattice.Build _ (seq T) meetUl.

End DistrLattice.

End SeqProdOrder.

Module Exports.

HB.reexport SeqProdOrder.

Notation seqprod_with := type.
Notation seqprod := type_.

Definition leEseq := @leEseq.
Definition le0s := @le0s.
Definition les0 := @les0.
Definition le_cons := @le_cons.
Definition botEseq := @botEseq.
Definition meetEseq := @meetEseq.
Definition meet_cons := @meet_cons.
Definition joinEseq := @joinEseq.

End Exports.
End SeqProdOrder.
HB.export SeqProdOrder.Exports.

Module DefaultSeqProdOrder.
Section DefaultSeqProdOrder.
Context {disp : disp_t}.

Notation seqprod := (seqprod_with (seqprod_display disp)).

HB.instance Definition _ (T : preorderType disp) :=
  BPreorder.copy (seq T) (seqprod T).
HB.instance Definition _ (T : porderType disp) :=
  BPOrder.copy (seq T) (seqprod T).
HB.instance Definition _ (T : meetSemilatticeType disp) :=
  BMeetSemilattice.copy (seq T) (seqprod T).
HB.instance Definition _ (T : joinSemilatticeType disp) :=
  BJoinSemilattice.copy (seq T) (seqprod T).
HB.instance Definition _ (T : latticeType disp) :=
  BLattice.copy (seq T) (seqprod T).
HB.instance Definition _ (T : distrLatticeType disp) :=
  BDistrLattice.copy (seq T) (seqprod T).

End DefaultSeqProdOrder.
End DefaultSeqProdOrder.

(*********************************************)
(* We declare an alias of the sequences,     *)
(* which has canonical lexicographic order.  *)
(*********************************************)

Module SeqLexiOrder.
Section SeqLexiOrder.

Definition type (disp : disp_t) T := seq T.
Definition type_ (disp : disp_t) (T : preorderType disp) :=
  type (seqlexi_display disp) T.

Context {disp disp' : disp_t}.

Local Notation seq := (type disp').

#[export] HB.instance Definition _ (T : eqType) := Equality.on (seq T).
#[export] HB.instance Definition _ (T : choiceType) := Choice.on (seq T).
#[export] HB.instance Definition _ (T : countType) := Countable.on (seq T).

Section Preorder.
Context (T : preorderType disp).
Implicit Types (s : seq T).

Fixpoint le s1 s2 := if s1 isn't x1 :: s1' then true else
                     if s2 isn't x2 :: s2' then false else
                       (x1 <= x2) && ((x1 >= x2) ==> le s1' s2').
Fixpoint lt s1 s2 := if s2 isn't x2 :: s2' then false else
                     if s1 isn't x1 :: s1' then true else
                       (x1 <= x2) && ((x1 >= x2) ==> lt s1' s2').

Fact refl: reflexive le.
Proof. by elim => [|x s ih] //=; rewrite lexx. Qed.

Fact trans: transitive le.
Proof.
elim=> [|y sy ihs] [|x sx] [|z sz] //= /andP[] xy /implyP yx /andP[] yz /implyP zy /=.
rewrite (le_trans xy yz)/=; apply/implyP => zx.
apply/ihs; first exact/yx/(le_trans yz zx).
exact/zy/(le_trans zx xy).
Qed.

Lemma lt_le_def s1 s2 : lt  s1 s2 = le s1 s2 && ~~ le s2 s1.
Proof.
elim: s1 s2 => [|x s1 ihs1] [|y s2]//=; rewrite ihs1.
by case: (x <= y); case (y <= x).
Qed.

#[export] HB.instance Definition _ :=
  isPreorder.Build disp' (seq T) lt_le_def refl trans.

Lemma leEseqlexi s1 s2 :
  (s1 <= s2) = if s1 isn't x1 :: s1' then true else
               if s2 isn't x2 :: s2' then false else
               (x1 <= x2) && ((x1 >= x2) ==> (s1' <= s2' :> seq T)).
Proof. by case: s1. Qed.

Lemma ltEseqlexi s1 s2 :
  (s1 < s2) = if s2 isn't x2 :: s2' then false else
              if s1 isn't x1 :: s1' then true else
              (x1 <= x2) && ((x1 >= x2) ==> (s1' < s2' :> seq T)).
Proof. by case: s1. Qed.

Lemma lexi0s s : [::] <= s :> seq T. Proof. by []. Qed.

Lemma lexis0 s : (s <= [::]) = (s == [::]). Proof. by rewrite leEseqlexi. Qed.

Lemma ltxi0s s : ([::] < s :> seq T) = (s != [::]). Proof. by case: s. Qed.

Lemma ltxis0 s : (s < [::]) = false. Proof. by rewrite ltEseqlexi. Qed.

Lemma lexi_cons x1 s1 x2 s2 :
  (x1 :: s1 <= x2 :: s2 :> seq T) = (x1 <= x2) && ((x1 >= x2) ==> (s1 <= s2)).
Proof. by []. Qed.

Lemma ltxi_cons x1 s1 x2 s2 :
  (x1 :: s1 < x2 :: s2 :> seq T) = (x1 <= x2) && ((x1 >= x2) ==> (s1 < s2)).
Proof. by []. Qed.

Lemma lexi_lehead x s1 y s2 : x :: s1 <= y :: s2 :> seq T -> x <= y.
Proof. by rewrite lexi_cons => /andP[]. Qed.

Lemma ltxi_lehead x s1 y s2 : x :: s1 < y :: s2 :> seq T -> x <= y.
Proof. by rewrite ltxi_cons => /andP[]. Qed.

Lemma eqhead_lexiE (x : T) s1 s2 : (x :: s1 <= x :: s2 :> seq _) = (s1 <= s2).
Proof. by rewrite lexi_cons lexx. Qed.

Lemma eqhead_ltxiE (x : T) s1 s2 : (x :: s1 < x :: s2 :> seq _) = (s1 < s2).
Proof. by rewrite ltxi_cons lexx. Qed.

#[export] HB.instance Definition _ := hasBottom.Build _ (seq T) lexi0s.

End Preorder.

Lemma sub_seqprod_lexi d (T : preorderType disp) :
   subrel (<=%O : rel (seqprod_with d T)) (<=%O : rel (seq T)).
Proof.
elim=> [|x1 s1 ihs1] [|x2 s2]//=; rewrite le_cons lexi_cons /=.
by move=> /andP[-> /ihs1->]; rewrite implybT.
Qed.

Section POrder.
Variable T : porderType disp.
Implicit Types s : seq T.

Fact anti: antisymmetric (@le T).
Proof.
move=> x y /andP []; elim: x y => [|x sx ih] [|y sy] //=.
by case: comparableP => //= -> lesxsy /(ih _ lesxsy) ->.
Qed.

#[export] HB.instance Definition _ :=
  Preorder_isPOrder.Build disp' (seq T) anti.

Lemma neqhead_lexiE (x y : T) s1 s2 : x != y ->
  (x :: s1 <= y :: s2 :> seq _) = (x < y).
Proof. by rewrite lexi_cons; case: comparableP. Qed.

Lemma neqhead_ltxiE (x y : T) s1 s2 : x != y ->
  (x :: s1 < y :: s2 :> seq _) = (x < y).
Proof. by rewrite ltxi_cons; case: (comparableP x y). Qed.

End POrder.

Section Total.
Context (T : orderType disp).

Fact total : total (<=%O : rel (seq T)).
Proof.
by elim=> [|x1 s1 ihs1] [|x2 s2]//=; rewrite !lexi_cons; case: ltgtP => /=.
Qed.

#[export] HB.instance Definition _ := POrder_isTotal.Build _ (seq T) total.

End Total.

End SeqLexiOrder.

Module Exports.

HB.reexport SeqLexiOrder.

Notation seqlexi_with := type.
Notation seqlexi := type_.

Definition leEseqlexi := @leEseqlexi.
Definition lexi0s := @lexi0s.
Definition lexis0 := @lexis0.
Definition lexi_cons := @lexi_cons.
Definition lexi_lehead := @lexi_lehead.
Definition eqhead_lexiE := @eqhead_lexiE.

Definition ltEseqltxi := @ltEseqlexi.
Definition ltxi0s := @ltxi0s.
Definition ltxis0 := @ltxis0.
Definition ltxi_cons := @ltxi_cons.
Definition ltxi_lehead := @ltxi_lehead.
Definition eqhead_ltxiE := @eqhead_ltxiE.
Definition sub_seqprod_lexi := @sub_seqprod_lexi.

Definition neqhead_lexiE := @neqhead_lexiE.
Definition neqhead_ltxiE := @neqhead_ltxiE.

End Exports.
End SeqLexiOrder.
HB.export SeqLexiOrder.Exports.

Module DefaultSeqLexiOrder.
Section DefaultSeqLexiOrder.
Context {disp : disp_t}.

Notation seqlexi := (seqlexi_with (seqlexi_display disp)).

HB.instance Definition _ (T : preorderType disp) :=
  BPreorder.copy (seq T) (seqlexi T).
HB.instance Definition _ (T : porderType disp) :=
  BPOrder.copy (seq T) (seqlexi T).
HB.instance Definition _ (T : orderType disp) :=
  BTotal.copy (seq T) (seqlexi T).

End DefaultSeqLexiOrder.
End DefaultSeqLexiOrder.

(***************************************)
(* We declare an alias of the tuples,  *)
(* which has canonical product order.  *)
(***************************************)

Module TupleProdOrder.
Import DefaultSeqProdOrder.

Section TupleProdOrder.

Definition type (disp : disp_t) n T := n.-tuple T.
Definition type_ (disp : disp_t) n (T : preorderType disp) :=
  type (seqprod_display disp) n T.

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

Notation "n .-tupleprod" := n.-tupleprod[seqprod_display disp].

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
(* We declare an alias of the tuples,        *)
(* which has canonical lexicographic order.  *)
(*********************************************)

Module TupleLexiOrder.
Section TupleLexiOrder.
Import DefaultSeqLexiOrder.

Definition type (disp : disp_t) n T := n.-tuple T.
Definition type_ (disp : disp_t) n (T : preorderType disp) :=
  type (seqlexi_display disp) n T.

Context {disp disp' : disp_t}.
Local Notation "n .-tuple" := (type disp' n) : type_scope.

Section Basics.
Context (n : nat).
#[export] HB.instance Definition _ (T : eqType) := Equality.on (n.-tuple T).
#[export] HB.instance Definition _ (T : choiceType) :=
  SubChoice.on (n.-tuple T).
#[export] HB.instance Definition _ (T : countType) :=
  SubCountable.on (n.-tuple T).
#[export] HB.instance Definition _ (T : finType) :=
  SubFinite.on (n.-tuple T).
End Basics.

Section Preorder.
Implicit Types (T : preorderType disp).

#[export]
HB.instance Definition _ n T :=
  [SubChoice_isSubPreorder of n.-tuple T by <: with disp'].

End Preorder.

Lemma sub_tprod_lexi d n (T : preorderType disp) :
   subrel (<=%O : rel (n.-tupleprod[d] T)) (<=%O : rel (n.-tuple T)).
Proof. exact: sub_seqprod_lexi. Qed.

Section BPreorder.
Context (n : nat) (T : bPreorderType disp).
Implicit Types (t : n.-tuple T).

Fact le0x t : [tuple \bot | _ < n] <= t :> n.-tuple T.
Proof. by apply: sub_seqprod_lexi; apply: le0x (t : n.-tupleprod T). Qed.

#[export] HB.instance Definition _ := hasBottom.Build _ (n.-tuple T) le0x.

Lemma botEtlexi : \bot = [tuple \bot | _ < n] :> n.-tuple T. Proof. by []. Qed.

End BPreorder.

Section TPreorder.
Context (n : nat) (T : tPreorderType disp).
Implicit Types (t : n.-tuple T).

Fact lex1 t : t <= [tuple \top | _ < n].
Proof. by apply: sub_seqprod_lexi; apply: lex1 (t : n.-tupleprod T). Qed.

#[export] HB.instance Definition _ := hasTop.Build _ (n.-tuple T) lex1.

Lemma topEtlexi : \top = [tuple \top | _ < n] :> n.-tuple T. Proof. by []. Qed.

End TPreorder.

Section POrder.
Implicit Types (n : nat) (T : porderType disp).

#[export] HB.instance Definition _ n T :=
  [SubChoice_isSubPOrder of n.-tuple T by <: with disp'].

Lemma lexi_tupleP n T (t1 t2 : n.-tuple T) :
   reflect (exists k : 'I_n.+1, forall i : 'I_n, (i <= k)%N ->
               tnth t1 i <= tnth t2 i ?= iff (i != k :> nat)) (t1 <= t2).
Proof.
elim: n => [|n IHn] in t1 t2 *.
  by rewrite tuple0 [t2]tuple0/= lexx; constructor; exists ord0 => -[].
case: (tupleP t1) (tupleP t2) => [x1 {}t1] [x2 {}t2].
rewrite [_ <= _]lexi_cons; apply: (iffP idP) => [|[k leif_xt12]].
  case: comparableP => //= [ltx12 _|-> /IHn[k kP]].
    exists ord0 => i; rewrite leqn0 => /eqP/(@ord_inj n.+1 i ord0)->.
    by apply/leifP; rewrite !tnth0.
  exists (lift ord0 k) => i; case: (unliftP ord0 i) => [j ->|-> _].
    by rewrite !ltnS => /kP; rewrite !tnthS.
  by apply/leifP; rewrite !tnth0 eqxx.
have /= := leif_xt12 ord0 isT; rewrite !tnth0 => leif_x12.
rewrite leif_x12/=; move: leif_x12 leif_xt12 => /leifP.
case: (unliftP ord0 k) => {k} [k-> /eqP<-{x2}|-> /lt_geF->//] leif_xt12.
rewrite lexx implyTb; apply/IHn; exists k => i le_ik.
by have := leif_xt12 (lift ord0 i) le_ik; rewrite !tnthS.
Qed.

Lemma ltxi_tupleP n T (t1 t2 : n.-tuple T) :
   reflect (exists k : 'I_n, forall i : 'I_n, (i <= k)%N ->
               tnth t1 i <= tnth t2 i ?= iff (i != k :> nat)) (t1 < t2).
Proof.
elim: n => [|n IHn] in t1 t2 *.
  by rewrite tuple0 [t2]tuple0/= ltxx; constructor => - [] [].
case: (tupleP t1) (tupleP t2) => [x1 {}t1] [x2 {}t2].
rewrite [_ < _]ltxi_cons; apply: (iffP idP) => [|[k leif_xt12]].
  case: (comparableP x1 x2) => //= [ltx12 _|-> /IHn[k kP]].
    exists ord0 => i; rewrite leqn0 => /eqP/(@ord_inj n.+1 i ord0)->.
    by apply/leifP; rewrite !tnth0.
  exists (lift ord0 k) => i; case: (unliftP ord0 i) => {i} [i ->|-> _].
    by rewrite !ltnS => /kP; rewrite !tnthS.
  by apply/leifP; rewrite !tnth0 eqxx.
have /= := leif_xt12 ord0 isT; rewrite !tnth0 => leif_x12.
rewrite leif_x12/=; move: leif_x12 leif_xt12 => /leifP.
case: (unliftP ord0 k) => {k} [k-> /eqP<-{x2}|-> /lt_geF->//] leif_xt12.
rewrite lexx implyTb; apply/IHn; exists k => i le_ik.
by have := leif_xt12 (lift ord0 i) le_ik; rewrite !tnthS.
Qed.

Lemma ltxi_tuplePlt n T (t1 t2 : n.-tuple T) : reflect
  (exists2 k : 'I_n, forall i : 'I_n, (i < k)%N -> tnth t1 i = tnth t2 i
                                                 & tnth t1 k < tnth t2 k)
  (t1 < t2).
Proof.
apply: (iffP (ltxi_tupleP _ _)) => [[k kP]|[k kP ltk12]].
  exists k => [i i_lt|]; last by rewrite (lt_leif (kP _ _)) ?eqxx ?leqnn.
  by have /eqTleif->// := kP i (ltnW i_lt); rewrite ltn_eqF.
by exists k => i; case: ltngtP => //= [/kP-> _|/ord_inj-> _]; apply/leifP.
Qed.

End POrder.

#[export] HB.instance Definition _ n (T : orderType disp) :=
  [SubChoice_isSubOrder of n.-tuple T by <: with disp'].

(* FIXME: use HB.saturate *)
#[export] HB.instance Definition _ (n : nat) (T : tbPreorderType disp) :=
  Preorder.on (n.-tuple T).
#[export] HB.instance Definition _ (n : nat) (T : bPOrderType disp) :=
  POrder.on (n.-tuple T).
#[export] HB.instance Definition _ (n : nat) (T : tPOrderType disp) :=
  POrder.on (n.-tuple T).
#[export] HB.instance Definition _ (n : nat) (T : tbPOrderType disp) :=
  POrder.on (n.-tuple T).
#[export] HB.instance Definition _ (n : nat) (T : bOrderType disp) :=
  POrder.on (n.-tuple T).
#[export] HB.instance Definition _ (n : nat) (T : tOrderType disp) :=
  POrder.on (n.-tuple T).
#[export] HB.instance Definition _ (n : nat) (T : tbOrderType disp) :=
  POrder.on (n.-tuple T).
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
#[export] HB.instance Definition _ (n : nat) (T : finOrderType disp) :=
  POrder.on (n.-tuple T).
#[export] HB.instance Definition _ (n : nat) (T : finTBOrderType disp) :=
  POrder.on (n.-tuple T).
(* /FIXME *)

End TupleLexiOrder.

Module Exports.

HB.reexport TupleLexiOrder.

Notation "n .-tuplelexi[ disp ]" := (type disp n)
  (format "n .-tuplelexi[ disp ]") : type_scope.
Notation "n .-tuplelexi" := (type_ n)
  (format "n .-tuplelexi") : type_scope.

Definition topEtlexi := @topEtlexi.
Definition botEtlexi := @botEtlexi.
Definition sub_tprod_lexi := @sub_tprod_lexi.
Definition lexi_tupleP := @lexi_tupleP.
Arguments lexi_tupleP {disp disp' n T t1 t2}.
Definition ltxi_tupleP := @ltxi_tupleP.
Arguments ltxi_tupleP {disp disp' n T t1 t2}.
Definition ltxi_tuplePlt := @ltxi_tuplePlt.
Arguments ltxi_tuplePlt {disp disp' n T t1 t2}.

End Exports.
End TupleLexiOrder.
HB.export TupleLexiOrder.Exports.

Module DefaultTupleLexiOrder.
Section DefaultTupleLexiOrder.
Context {disp : disp_t}.

Notation "n .-tuplelexi" := n.-tuplelexi[seqlexi_display disp].

HB.instance Definition _ n (T : preorderType disp) :=
  Preorder.copy (n.-tuple T) (n.-tuplelexi T).
HB.instance Definition _ n (T : bPreorderType disp) :=
  BPreorder.copy (n.-tuple T) (n.-tuplelexi T).
HB.instance Definition _ n (T : tPreorderType disp) :=
  TPreorder.copy (n.-tuple T) (n.-tuplelexi T).
HB.instance Definition _ n (T : tbPreorderType disp) :=
  TBPreorder.copy (n.-tuple T) (n.-tuplelexi T).
HB.instance Definition _ n (T : porderType disp) :=
  POrder.copy (n.-tuple T) (n.-tuplelexi T).
HB.instance Definition _ n (T : bPOrderType disp) :=
  BPOrder.copy (n.-tuple T) (n.-tuplelexi T).
HB.instance Definition _ n (T : tPOrderType disp) :=
  TPOrder.copy (n.-tuple T) (n.-tuplelexi T).
HB.instance Definition _ n (T : tbPOrderType disp) :=
  TBPOrder.copy (n.-tuple T) (n.-tuplelexi T).
HB.instance Definition _ n (T : orderType disp) :=
  Lattice.copy (n.-tuple T) (n.-tuplelexi T).
HB.instance Definition _ n (T : orderType disp) :=
  DistrLattice.copy (n.-tuple T) (n.-tuplelexi T).
HB.instance Definition _ n (T : orderType disp) :=
  Total.copy (n.-tuple T) (n.-tuplelexi T).
HB.instance Definition _ n (T : bOrderType disp) :=
  BTotal.copy (n.-tuple T) (n.-tuplelexi T).
HB.instance Definition _ n (T : tOrderType disp) :=
  TTotal.copy (n.-tuple T) (n.-tuplelexi T).
HB.instance Definition _ n (T : tbOrderType disp) :=
  TBTotal.copy (n.-tuple T) (n.-tuplelexi T).
HB.instance Definition _ n (T : finPreorderType disp) :=
  FinPreorder.copy (n.-tuple T) (n.-tuplelexi T).
HB.instance Definition _ n (T : finBPreorderType disp) :=
  FinBPreorder.copy (n.-tuple T) (n.-tuplelexi T).
HB.instance Definition _ n (T : finTPreorderType disp) :=
  FinTPreorder.copy (n.-tuple T) (n.-tuplelexi T).
HB.instance Definition _ n (T : finTBPreorderType disp) :=
  FinTBPreorder.copy (n.-tuple T) (n.-tuplelexi T).
HB.instance Definition _ n (T : finPOrderType disp) :=
  FinPOrder.copy (n.-tuple T) (n.-tuplelexi T).
HB.instance Definition _ n (T : finBPOrderType disp) :=
  FinBPOrder.copy (n.-tuple T) (n.-tuplelexi T).
HB.instance Definition _ n (T : finTPOrderType disp) :=
  FinTPOrder.copy (n.-tuple T) (n.-tuplelexi T).
HB.instance Definition _ n (T : finTBPOrderType disp) :=
  FinTBPOrder.copy (n.-tuple T) (n.-tuplelexi T).
HB.instance Definition _ n (T : finOrderType disp) :=
  FinTotal.copy (n.-tuple T) (n.-tuplelexi T).
HB.instance Definition _ n (T : finTBOrderType disp) :=
  FinTBTotal.copy (n.-tuple T) (n.-tuplelexi T).

End DefaultTupleLexiOrder.
End DefaultTupleLexiOrder.

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

(* Some lemmas about [Order.enum 'I_n] *)
(* TOTHINK: move to OrdinalOrder? *)
Section Ordinal.
Import OrdinalOrder.Exports.

Lemma enum_ord n : enum 'I_n = fintype.enum 'I_n.
Proof.
rewrite (sorted_sort le_trans)// -(@sorted_map _ _ (val : 'I_n -> nat))/=.
by rewrite val_enum_ord iota_sorted.
Qed.

Lemma val_enum_ord n : [seq val i | i <- enum 'I_n] = iota 0 n.
Proof. by rewrite enum_ord val_enum_ord. Qed.

Lemma size_enum_ord n : size (enum 'I_n) = n.
Proof. by rewrite -cardE card_ord. Qed.

Lemma nth_enum_ord (n : nat) (i0 : 'I_n) (m : nat) :
  (m < n)%N -> nth i0 (enum 'I_n) m = m :> nat.
Proof. by move=> lemn; rewrite enum_ord nth_enum_ord. Qed.

Lemma nth_ord_enum (n : nat) (i0 i : 'I_n) : nth i0 (enum 'I_n) i = i.
Proof. by rewrite enum_ord nth_ord_enum. Qed.

Lemma index_enum_ord (n : nat) (i : 'I_n) : index i (enum 'I_n) = i.
Proof. by rewrite enum_ord index_enum_ord. Qed.

End Ordinal.

(* This module should be exported on demand, as in module tagnat below *)
Module Import EnumVal.
Import OrdinalOrder.Exports.

Section EnumVal.
Variables (d : disp_t) (T : finPreorderType d).
Implicit Types (x : T) (A : {pred T}).

Definition enum_rank_in x0 A (Ax0 : x0 \in A) x :=
  insubd (Ordinal (@enum_rank_subproof _ x0 A Ax0)) (index x (enum A)).

Definition enum_rank x := @enum_rank_in x T (erefl true) x.

Definition enum_val A i := nth (@enum_default _ A i) (enum A) i.
Prenex Implicits enum_val.

Lemma enum_valP A i : @enum_val A i \in A.
Proof.
suff: enum_val i \in enum A by rewrite mem_enum.
by apply: mem_nth; rewrite -cardE.
Qed.

Lemma enum_val_nth A x i : @enum_val A i = nth x (enum A) i.
Proof. by apply: set_nth_default; rewrite cardE in i *. Qed.

Lemma nth_enum_rank_in x00 x0 A Ax0 :
  {in A, cancel (@enum_rank_in x0 A Ax0) (nth x00 (enum A))}.
Proof.
move=> x Ax; rewrite /= insubdK ?nth_index ?mem_enum //.
by rewrite cardE [_ \in _]index_mem mem_enum.
Qed.

Lemma nth_enum_rank x0 : cancel enum_rank (nth x0 (enum T)).
Proof. by move=> x; apply: nth_enum_rank_in. Qed.

Lemma enum_rankK_in x0 A Ax0 :
   {in A, cancel (@enum_rank_in x0 A Ax0) enum_val}.
Proof. by move=> x; apply: nth_enum_rank_in. Qed.

Lemma enum_rankK : cancel enum_rank enum_val.
Proof. by move=> x; apply: enum_rankK_in. Qed.

Lemma enum_valK_in x0 A Ax0 : cancel enum_val (@enum_rank_in x0 A Ax0).
Proof.
move=> x; apply: ord_inj; rewrite insubdK.
  by rewrite cardE [_ \in _]index_mem mem_nth // -cardE.
by rewrite index_uniq ?enum_uniq // -cardE.
Qed.

Lemma enum_valK : cancel enum_val enum_rank.
Proof. by move=> x; apply: enum_valK_in. Qed.

Lemma enum_rank_inj : injective enum_rank.
Proof. exact: can_inj enum_rankK. Qed.

Lemma enum_val_inj A : injective (@enum_val A).
Proof. by move=> i; apply: can_inj (enum_valK_in (enum_valP i)) (i). Qed.

Lemma enum_val_bij_in x0 A : x0 \in A -> {on A, bijective (@enum_val A)}.
Proof.
move=> Ax0; exists (enum_rank_in Ax0) => [i _|]; last exact: enum_rankK_in.
exact: enum_valK_in.
Qed.

Lemma eq_enum_rank_in (x0 y0 : T) A (Ax0 : x0 \in A) (Ay0 : y0 \in A) :
  {in A, enum_rank_in Ax0 =1 enum_rank_in Ay0}.
Proof. by move=> x xA; apply: enum_val_inj; rewrite !enum_rankK_in. Qed.

Lemma enum_rank_in_inj (x0 y0 : T) A (Ax0 : x0 \in A) (Ay0 : y0 \in A) :
  {in A &, forall x y, enum_rank_in Ax0 x = enum_rank_in Ay0 y -> x = y}.
Proof. by move=> x y xA yA /(congr1 enum_val); rewrite !enum_rankK_in. Qed.

Lemma enum_rank_bij : bijective enum_rank.
Proof. by move: enum_rankK enum_valK; exists (@enum_val T). Qed.

Lemma enum_val_bij : bijective (@enum_val T).
Proof. by move: enum_rankK enum_valK; exists enum_rank. Qed.

End EnumVal.
Arguments enum_val {d T A}.
Arguments enum_rank {d T}.

Section EnumVal.
Variables (d : disp_t) (T : finPOrderType d).
Implicit Types (x : T) (A : {pred T}).

Section total.
(* We circumvent a shortcoming of finOrderType *)
(* which requires the type to be nonempty and we do not want to rule this out *)
Hypothesis (leT_total : total (<=%O : rel T)).

Lemma le_enum_val A : {mono @enum_val _ _ A : i j / i <= j}.
Proof.
apply: le_mono => i j le_ij.
rewrite /enum_val (set_nth_default (enum_default j)) -?cardE//.
apply: (sorted_ltn_nth lt_trans); rewrite -?topredE/= -?cardE//.
by rewrite lt_sorted_uniq_le enum_uniq/= sort_sorted.
Qed.

Lemma le_enum_rank_in x0 A (Ax0 : x0 \in A) :
  {in A &, {mono enum_rank_in Ax0 : x y / x <= y}}.
Proof.
apply: can_mono_in (@in2W _ _ predT predT _ (@le_enum_val A)) => //.
exact/onW_can_in/enum_rankK_in.
Qed.

Lemma le_enum_rank : {mono @enum_rank d T : i j / i <= j}.
Proof. exact: (can_mono (@enum_rankK _ _) (@le_enum_val predT)). Qed.

End total.
End EnumVal.

End EnumVal.

Notation enum_val := enum_val.
Notation enum_rank_in := enum_rank_in.
Notation enum_rank := enum_rank.
Notation enum_valP := enum_valP.
Notation enum_val_nth := enum_val_nth.
Notation nth_enum_rank_in := nth_enum_rank_in.
Notation nth_enum_rank := nth_enum_rank.
Notation enum_rankK_in := enum_rankK_in.
Notation enum_rankK := enum_rankK.
Notation enum_valK_in := enum_valK_in.
Notation enum_valK := enum_valK.
Notation enum_rank_inj := enum_rank_inj.
Notation enum_val_inj := enum_val_inj.
Notation enum_val_bij_in := enum_val_bij_in.
Notation eq_enum_rank_in := eq_enum_rank_in.
Notation enum_rank_in_inj := enum_rank_in_inj.
Notation enum_rank_bij := enum_rank_bij.
Notation enum_val_bij := enum_val_bij.
Notation le_enum_val := le_enum_val.
Notation le_enum_rank_in := le_enum_rank_in.
Notation le_enum_rank := le_enum_rank.

Module Syntax.
Export DvdSyntax.
End Syntax.

Module Exports.
HB.reexport.
End Exports.

End Order.

Export Order.Exports.

Export Order.Syntax.

(* FIXME: check if covered by Order.Exports *)
(* Export Order.NatOrder.Exports. *)
(* Export Order.NatMonotonyTheory. *)
(* Export Order.NatDvd.Exports. *)
(* Export Order.OrdinalOrder.Exports. *)
(* Export Order.BoolOrder.Exports. *)
(* Export Order.ProdOrder.Exports. *)
(* Export Order.SigmaOrder.Exports. *)
(* Export Order.ProdLexiOrder.Exports. *)
(* Export Order.SeqProdOrder.Exports. *)
(* Export Order.SeqLexiOrder.Exports. *)
(* Export Order.TupleProdOrder.Exports. *)
(* Export Order.TupleLexiOrder.Exports. *)

Module DefaultProdOrder := Order.DefaultProdOrder.
Module DefaultSeqProdOrder := Order.DefaultSeqProdOrder.
Module DefaultTupleProdOrder := Order.DefaultTupleProdOrder.
Module DefaultProdLexiOrder := Order.DefaultProdLexiOrder.
Module DefaultSeqLexiOrder := Order.DefaultSeqLexiOrder.
Module DefaultTupleLexiOrder := Order.DefaultTupleLexiOrder.

Module tagnat.
Section tagnat.

Import total_order.Order.Theory Order.EnumVal.

Context {n : nat} {p_ : 'I_n -> nat}.

Local Notation ordsum := 'I_(\sum_i p_ i)%N.
Local Notation T := {i & 'I_(p_ i)}.

Implicit Types (i : 'I_n) (s : ordsum) (p : T).

Lemma card : #|{: T}| = \sum_i p_ i.
Proof.
rewrite card_tagged sumnE/= big_map big_enum.
by apply: eq_bigr => i _; rewrite card_ord.
Qed.

Definition sig : ordsum -> T  := enum_val \o cast_ord (esym card).
Definition rank : T -> ordsum := cast_ord card \o enum_rank.

Lemma sigK : cancel sig rank.
Proof.
by move=> s; rewrite /sig/rank/= enum_valK cast_ord_comp cast_ord_id.
Qed.
Lemma sig_inj : injective sig. Proof. exact: can_inj sigK. Qed.

Lemma rankK : cancel rank sig.
Proof.
by move=> p; rewrite /sig/rank/= cast_ord_comp cast_ord_id enum_rankK.
Qed.
Lemma rank_inj : injective rank. Proof. exact: can_inj rankK. Qed.

Definition sig1 s : 'I_n             := tag (sig s).
Definition sig2 s : 'I_(p_ (sig1 s)) := tagged (sig s).
Definition Rank i (j : 'I_(p_ i))    := rank (Tagged _ j).

Lemma sigE12 s : sig s = @Tagged _ (sig1 s) _ (sig2 s).
Proof. by rewrite /sig1 /sig2; case: sig. Qed.

Lemma rankE p : rank p = @Rank (tag p) (tagged p). Proof. by case: p. Qed.

Lemma sig2K s : Rank (sig2 s) = s. Proof. by rewrite -rankE sigK. Qed.

Lemma Rank1K i0 (k : 'I_(p_ i0)) : sig1 (Rank k) = i0.
Proof. by rewrite /sig1 /Rank/= rankK/=. Qed.

Lemma Rank2K i0 (k : 'I_(p_ i0)) :
  sig2 (Rank k) = cast_ord (congr1 p_ (esym (Rank1K k))) k.
Proof. by apply: val_inj; rewrite /sig2/sig1/Rank/= rankK. Qed.
#[local] Hint Resolve sigK rankK : core.

Lemma rank_bij : bijective rank. Proof. by exists sig. Qed.
Lemma sig_bij  : bijective sig.  Proof. by exists rank. Qed.

Lemma rank_bij_on : {on [pred _ | true], bijective rank}.
Proof. exact/onW_bij/rank_bij. Qed.

Lemma sig_bij_on : {on [pred _ | true], bijective sig}.
Proof. exact/onW_bij/sig_bij. Qed.

Lemma le_sig : {mono sig : i j / i <= j}.
Proof. by move=> i j; rewrite /sig/= le_enum_val//; apply: le_total. Qed.

Lemma le_sig1 : {homo sig1 : i j / i <= j}.
Proof. by move=> i j; rewrite /sig1/= -le_sig leEsig/=; case: leP. Qed.

Lemma le_rank : {mono rank : p q / p <= q}.
Proof. exact: can_mono le_sig. Qed.

Lemma le_Rank i : {mono @Rank i : j k / j <= k}.
Proof. by move=> j k; rewrite /Rank le_rank/= leEsig/= tagged_asE lexx. Qed.

Lemma lt_sig : {mono sig : i j / i < j}.
Proof. by move=> i j; rewrite !ltNge le_sig. Qed.

Lemma lt_rank : {mono rank : p q / p < q}.
Proof. by move=> p q; rewrite !ltNge le_rank. Qed.

Lemma lt_Rank i : {mono @Rank i : j k / j < k}.
Proof. by move=> j k; rewrite !ltNge le_Rank. Qed.

Lemma eq_Rank i i' (j : 'I_(p_ i)) (j': 'I_(p_ i')) :
  (Rank j == Rank j' :> nat) = (i == i') && (j == j' :> nat).
Proof.
rewrite val_eqE /Rank -(can_eq sigK) !rankK.
case: (i =P i') => ii' /=; last by case: eqVneq => // -[].
by case: _ / ii' in j' *; rewrite eq_Tagged.
Qed.

Lemma rankEsum p : rank p = \sum_(i < n | (i < tag p)%N) p_ i + tagged p :> nat.
Proof.
pose sum p := \sum_(i < n | (i < tag p)%N) p_ i + tagged p.
rewrite -/(sum _); have sumlt : forall p, (sum p < \sum_i p_ i)%N.
  rewrite /sum => -[/= i j].
  rewrite [ltnRHS](bigID [pred i' : 'I__ | (i' < i)%N])/= ltn_add2l.
  by rewrite (bigD1 i) ?ltnn//= ltn_addr.
suff: rank =1 (fun p => Ordinal (sumlt p)) by move=> /(_ p)/(congr1 val).
apply: (Order.mono_unique _ _ le_rank) => //=.
- exact: le_total.
- by rewrite card card_ord.
apply: le_mono => /= -[i j] -[i' j']; rewrite ltEsig/= !ltEord/= /sum leEord/=.
case: (ltngtP i i') => //= [ltii' _|/val_inj ii']; last first.
  by rewrite -ii' in j' *; rewrite tagged_asE => ltjj'; rewrite ltn_add2l.
rewrite ltn_addr// (@leq_trans (\sum_(i0 < n | (i0 < i)%N) p_ i0 + p_ i))%N//.
  by rewrite ltn_add2l.
rewrite [leqRHS](bigID [pred i' : 'I__ | (i' < i)%N])/=.
rewrite leq_add//; last first.
  by rewrite (bigD1 i) ?ltnn ?ltii'//= leq_addr.
rewrite [leqRHS](eq_bigl [pred k : 'I_n | (k < i)%N])// => k/=.
by case: (ltnP k i); rewrite ?andbF// => /ltn_trans->.
Qed.

Lemma RankEsum i j : @Rank i j = \sum_(k < n | (k < i)%N) p_ k + j :> nat.
Proof. by rewrite /Rank rankEsum/=. Qed.

Lemma rect s : s = \sum_(i < n | (i < sig1 s)%N) p_ i + sig2 s :> nat.
Proof. by rewrite -[s]sigK rankEsum /= sigK. Qed.

Lemma eqRank (i0 j : nat) (li0 : (i0 < n)%N) (lj : (j < p_ (Ordinal li0))%N) :
  (\sum_(i < n | (i < i0)%N) p_ i) + j = Rank (Ordinal lj) :> nat.
Proof. by rewrite RankEsum. Qed.

End tagnat.
End tagnat.
Arguments tagnat.Rank {n p_}.

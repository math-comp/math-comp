(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)

(* - Reserved notation for various arithmetic and algebraic operations:       *)
(*     e.[a1, ..., a_n] evaluation (e.g., polynomials).                       *)
(*                 e`_i indexing (number list, integer pi-part).              *)
(*                 x^-1 inverse (group, field).                               *)
(*       x *+ n, x *- n integer multiplier (modules and rings).               *)
(*       x ^+ n, x ^- n integer exponent (groups and rings).                  *)
(*       x *: A, A :* x external product (scaling/module product in rings,    *)
(*                      left/right cosets in groups).                         *)
(*             A :&: B  intersection (of sets, groups, subspaces, ...).       *)
(*     A :|: B, a |: B  union, union with a singleton (of sets).              *)
(*     A :\: B, A :\ b  relative complement (of sets, subspaces, ...).        *)
(*        <<A>>, <[a]>  generated group/subspace, generated cycle/line.       *)
(*       'C[x], 'C_A[x] point centralisers (in groups and F-algebras).        *)
(*       'C(A), 'C_B(A) centralisers (in groups and matrix and F_algebras).   *)
(*                'Z(A) centers (in groups and matrix and F-algebras).        *)
(*       m %/ d, m %% d Euclidean division and remainder (nat, polynomials).  *)
(*               d %| m Euclidean divisibility (nat, polynomial).             *)
(*       m = n %[mod d] equality mod d (also defined for <>, ==, and !=).     *)
(*               e^`(n) nth formal derivative (groups, polynomials).          *)
(*                e^`() simple formal derivative (polynomials only).          *)
(*                 `|x| norm, absolute value, distance (rings, int, nat).     *)
(*      x <= y ?= iff C x is less than y, and equal iff C holds (nat, rings). *)
(*     x <= y :> T, etc cast comparison (rings, all comparison operators).    *)
(*    [rec a1, ..., an] standard shorthand for hidden recursor (see prime.v). *)
(*   The interpretation of these notations is not defined here, but the       *)
(*   declarations help maintain consistency across the library.               *)

(* Reserved notation for evaluation *)
Reserved Notation "e .[ x ]"
  (at level 2, left associativity, format "e .[ x ]").

Reserved Notation "e .[ x1 , x2 , .. , xn ]" (at level 2, left associativity,
  format "e '[ ' .[ x1 , '/'  x2 , '/'  .. , '/'  xn ] ']'").

(* Reserved notation for subscripting and superscripting *)
Reserved Notation "s `_ i" (at level 3, i at level 2, left associativity,
  format "s `_ i").
Reserved Notation "x ^-1" (at level 3, left associativity, format "x ^-1").

(* Reserved notation for integer multipliers and exponents *)
Reserved Notation "x *+ n" (at level 40, left associativity).
Reserved Notation "x *- n" (at level 40, left associativity).
Reserved Notation "x ^+ n" (at level 29, left associativity).
Reserved Notation "x ^- n" (at level 29, left associativity).

(* Reserved notation for external multiplication. *)
Reserved Notation "x *: A" (at level 40).
Reserved Notation "A :* x" (at level 40).

(* Reserved notation for set-theretic operations. *)
Reserved Notation "A :&: B"  (at level 48, left associativity).
Reserved Notation "A :|: B" (at level 52, left associativity).
Reserved Notation "a |: A" (at level 52, left associativity).
Reserved Notation "A :\: B" (at level 50, left associativity).
Reserved Notation "A :\ b" (at level 50, left associativity).

(* Reserved notation for generated structures *)
Reserved Notation "<< A >>"  (at level 0, format "<< A >>").
Reserved Notation "<[ a ] >"  (at level 0, format "<[ a ] >").

(* Reserved notation for centralisers and centers. *)
Reserved Notation "''C' [ x ]" (at level 8, format "''C' [ x ]").
Reserved Notation "''C_' A [ x ]"
  (at level 8, A at level 2, format "''C_' A [ x ]").
Reserved Notation "''C' ( A )" (at level 8, format "''C' ( A )").
Reserved Notation "''C_' B ( A )"
  (at level 8, B at level 2, format "''C_' B ( A )").
Reserved Notation "''Z' ( A )" (at level 8, format "''Z' ( A )").
(* Compatibility with group action centraliser notation. *)
Reserved Notation "''C_' ( A ) [ x ]" (at level 8, only parsing).
Reserved Notation "''C_' ( B ) ( A )" (at level 8, only parsing).

(* Reserved notation for Euclidean division and divisibility. *)
Reserved Notation "m %/ d" (at level 40, no associativity). 
Reserved Notation "m %% d" (at level 40, no associativity). 
Reserved Notation "m %| d" (at level 70, no associativity). 
Reserved Notation "m = n %[mod d ]" (at level 70, n at next level,
  format "'[hv ' m '/'  =  n '/'  %[mod  d ] ']'").
Reserved Notation "m == n %[mod d ]" (at level 70, n at next level,
  format "'[hv ' m '/'  ==  n '/'  %[mod  d ] ']'").
Reserved Notation "m <> n %[mod d ]" (at level 70, n at next level,
  format "'[hv ' m '/'  <>  n '/'  %[mod  d ] ']'").
Reserved Notation "m != n %[mod d ]" (at level 70, n at next level,
  format "'[hv ' m '/'  !=  n '/'  %[mod  d ] ']'").

(* Reserved notation for derivatives. *)
Reserved Notation "a ^` ()" (at level 8, format "a ^` ()").
Reserved Notation "a ^` ( n )" (at level 8, format "a ^` ( n )").

(* Reserved notation for absolute value. *)
Reserved Notation  "`| x |" (at level 0, x at level 99, format "`| x |").

(* Reserved notation for conditional comparison *)
Reserved Notation "x <= y ?= 'iff' c" (at level 70, y, c at next level,
  format "x '[hv'  <=  y '/'  ?=  'iff'  c ']'").

(* Reserved notation for cast comparison. *)
Reserved Notation "x <= y :> T" (at level 70, y at next level).
Reserved Notation "x >= y :> T" (at level 70, y at next level, only parsing).
Reserved Notation "x < y :> T" (at level 70, y at next level).
Reserved Notation "x > y :> T" (at level 70, y at next level, only parsing).
Reserved Notation "x <= y ?= 'iff' c :> T" (at level 70, y, c at next level,
  format "x '[hv'  <=  y '/'  ?=  'iff'  c  :> T ']'").
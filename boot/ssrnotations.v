(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)

(******************************************************************************)
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
(******************************************************************************)

(* Reserved notation for evaluation *)
Reserved Notation "e .[ x ]" (left associativity, format "e .[ x ]").

Reserved Notation "e .[ x1 , x2 , .. , xn ]" (left associativity,
  format "e '[ ' .[ x1 , '/'  x2 , '/'  .. , '/'  xn ] ']'").

(* Reserved notation for subscripting and superscripting *)
Reserved Notation "s `_ i" (at level 3, i at level 2, left associativity,
  format "s `_ i").
Reserved Notation "x ^-1" (left associativity, format "x ^-1").

(* Reserved notation for integer multipliers and exponents *)
Reserved Notation "x *+ n" (at level 40, left associativity).
Reserved Notation "x *- n" (at level 40, left associativity).
Reserved Notation "x ^+ n" (at level 29, left associativity).
Reserved Notation "x ^- n" (at level 29, left associativity).

(* Reserved notation for external multiplication. *)
Reserved Notation "x *: A" (at level 40).
Reserved Notation "A :* x" (at level 40).

(* Reserved notation for conjugation and lifting of actions to sets. *)
Reserved Notation "x ^*" (format "x ^*", left associativity).

(* Reserved notation for set-theoretic operations. *)
Reserved Notation "A :&: B"  (at level 48, left associativity).
Reserved Notation "A :|: B" (at level 52, left associativity).
Reserved Notation "a |: A" (at level 52, left associativity).
Reserved Notation "A :\: B" (at level 50, left associativity).
Reserved Notation "A :\ b" (at level 50, left associativity).

(* Reserved notation for generated structures *)
Reserved Notation "<< A >>"  (format "<< A >>").
Reserved Notation "<[ a ] >"  (format "<[ a ] >").

(* Reserved notation for the order of an element (group, polynomial, etc)  *)
Reserved Notation "#[ x ]" (format "#[ x ]").

(* Reserved notation for centralisers and centers. *)
Reserved Notation "''C' [ x ]" (format "''C' [ x ]").
Reserved Notation "''C_' A [ x ]" (A at level 2, format "''C_' A [ x ]").
Reserved Notation "''C' ( A )" (format "''C' ( A )").
Reserved Notation "''C_' B ( A )" (B at level 2, format "''C_' B ( A )").
Reserved Notation "''Z' ( A )" (format "''Z' ( A )").
(* Compatibility with group action centraliser notation. *)
Reserved Notation "''C_' ( A ) [ x ]".
Reserved Notation "''C_' ( B ) ( A )".

(* Reserved notation for Euclidean division and divisibility. *)
Reserved Notation "m %/ d" (at level 40, no associativity).
Reserved Notation "m %% d" (at level 40, no associativity).
Reserved Notation "m %| d" (at level 70, no associativity).
#[warning="-postfix-notation-not-level-1"]
Reserved Notation "m = n %[mod d ]"
  (format "'[hv ' m '/'  =  n '/'  %[mod  d ] ']'").
#[warning="-postfix-notation-not-level-1"]
Reserved Notation "m == n %[mod d ]" (at level 70, n at next level,
  format "'[hv ' m '/'  ==  n '/'  %[mod  d ] ']'").
#[warning="-postfix-notation-not-level-1"]
Reserved Notation "m <> n %[mod d ]"
  (format "'[hv ' m '/'  <>  n '/'  %[mod  d ] ']'").
#[warning="-postfix-notation-not-level-1"]
Reserved Notation "m != n %[mod d ]" (at level 70, n at next level,
  format "'[hv ' m '/'  !=  n '/'  %[mod  d ] ']'").

(* Reserved notation for derivatives. *)
Reserved Notation "a ^` ()" (format "a ^` ()").
Reserved Notation "a ^` ( n )" (format "a ^` ( n )").

(* Reserved notation for absolute value. *)
Reserved Notation  "`| x |" (x at level 99, format "`| x |").

(* Reserved notation for conditional comparison *)
Reserved Notation "x <= y ?= 'iff' c" (c at next level,
  format "x '[hv'  <=  y '/'  ?=  'iff'  c ']'").

(* Reserved notation for cast comparison. *)
Reserved Notation "x <= y :> T".
Reserved Notation "x >= y :> T".
Reserved Notation "x < y :> T".
Reserved Notation "x > y :> T".
Reserved Notation "x <= y ?= 'iff' c :> T" (c at next level,
  format "x '[hv'  <=  y '/'  ?=  'iff'  c  :> T ']'").

(* Reserved notation for dot product. *)
Reserved Notation "'[ u , v ]" (format "'[hv' ''[' u , '/ '  v ] ']'").
Reserved Notation "'[ u ]" (format "''[' u ]").

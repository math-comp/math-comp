(* (c) Copyright 2006-2019 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
Require Import choice path finset finfun fintype bigop.

(*****************************************************************************)
(* This file provides representations for finite sets over a choiceType K,   *)
(* finite maps with keys in a choiceType K and the values in an arbitrary    *)
(* type V, and total functions from K to V with finite support.              *)
(* The domain (resp. support) of a finite map (resp. fintely supported       *)
(* function) is a finite set, and so is the codomain (resp. image) when V    *)
(* is a choice type.                                                         *)
(*                                                                           *)
(*                {fset K} == finite sets of elements of K                   *)
(*           {fmap K -> V} == finitely supported maps from K to V.           *)
(* {fsfun K -> T for dflt} == finitely supported functions                   *)
(*                     with default value dflt : K -> V outside the support  *)
(*                                                                           *)
(********* finite sets *******************************************************)
(*                                                                           *)
(* In the remainder, A and B are of type {fset K}.                           *)
(*                                                                           *)
(* - {fset K} is provided with a canonical structure of predType, in order   *)
(*   to enable the notation "a \in A"                                        *)
(* - There is a coercion from {fset K} to Type in order to interpret any     *)
(*   finset A as the subType of elements a : K such that a \in A.            *)
(*   Because of this coercion, writing a : A makes sense.                    *)
(*                                                                           *)
(* The following notations are in the %fset scope                            *)
(*            fset0 == the empty finite set                                  *)
(*         [fset k] == the singleton finite set {k}                          *)
(*          A `&` B == the intersection of A and B                           *)
(*          A `|` B == the union of A and B                                  *)
(*           a |` B == the union of singleton a and B                        *)
(*          A `\` B == the complement of B in A                              *)
(*           A `\ b == A without b                                           *)
(*          A `*` B == the cartesian product of A and B                      *)
(* [disjoint A & B] := A `&` B == 0                                          *)
(*         A `<=` B == A is a subset of B                                    *)
(*          A `<` B == A is a proper subset of B                             *)
(*            #|`A| == cardinal of A                                         *)
(*    fincl AsubB a == turns a : A  into an element of B                     *)
(*                     using a proof AsubB of A \fsubset B                   *)
(*         fsub B A == turns A : {fset K} into a {set B}                     *)
(*           f @` A == the image set of the collective predicate A by f.     *)
(*      f @2`(A, B) == the image set of A x B by the binary function f.      *)
(*           [` aA] == an element a of A such that val [` aA] = a            *)
(*                     where aA is a proof of a \in A                        *)
(*                                                                           *)
(* In order to support the following notations, we introduce three canonical *)
(* structure that reflect the finiteness of a predicate, in the following    *)
(* notations, p (resp q) are such finite predicates, which are ultimately    *)
(* represented by elements A (resp B) from {fset K}.                         *)
(*                                                                           *)
(*    [fset x in p | P] == the set of all x of type K, such that             *)
(*                         x \in p and P x where P is a predicate on K       *)
(*  [fset x in p | P & Q] := [set x in p | P && Q].                          *)
(*                                                                           *)
(* [fset E | x in p] == the set of all the values of the expression E, for x *)
(*                     drawn from the collective finite predicate p.         *)
(* [fset E | x in p & P] == the set of values of E for x drawn from p, such  *)
(*                     that P is true.                                       *)
(* [fset E | x in p, y in q] == the set of values of E for x drawn from p and*)
(*                     and y drawn from q; q may depend on x.                *)
(* [fset E | x in p, y in q & P] == the set of values of E for x drawn from  *)
(*                    p and y drawn from q; such that P is true.             *)
(* [fsetval x in p] == the set of (val x) for x in the finite predicate p    *)
(* [fsetval x in p | P ] == the set of (val x) for x in p, such that P       *)
(* [fsetval x in p | P & Q] := [fsetval x in p | P && Q]                     *)
(*                                                                           *)
(* For each notation above, there is an additional one with ':' instead of   *)
(* 'in' which is used to range over the finite type A instead of the finite  *)
(* set A, and the optional predicate is over A instead of K                  *)
(* For example:                                                              *)
(*    [fset x : A | P] := [fset x in {: A} | P]                              *)
(*                     == the set of all x of type A, such that P x          *)
(* [fset E | x : A] == the set of all the values of the expression E, for x  *)
(*                     drawn from the finite type A                          *)
(*                                                                           *)
(* For each [fset ...] or [fsetval ...] notation, there is a keyed variant   *)
(* written [fset[key] ...] or [fsetval[key] ...] for locking                 *)
(*                                                                           *)
(******* finite maps *********************************************************)
(*                                                                           *)
(* Finite maps are finite functions (from finfun) where the domain is        *)
(* obtained by the coercion of a {fset A} to the finType of its elements     *)
(* Operations on finmap:                                                     *)
(* The following notations are in the %fmap scope                            *)
(*                                                                           *)
(*           f.[? k] == returns Some v if k maps to v, otherwise None        *)
(*             f.[p] == returns v if p has type k \in f, and k maps to v     *)
(*        f.[k <- v] == f extended with the mapping k -> v                   *)
(*            domf f == finite set (of type {fset K}) of keys of f           *)
(*          codomf f == finite set (of type {fset V}) of values of f         *)
(*           k \in f == k is a key of f                                      *)
(*                   := k \in domf f                                         *)
(*            [fmap] == the empty finite map                                 *)
(* [fmap x : S => E] == the finmap defined by E on the support S             *)
(*           f.[& A] == f restricted to A (intersected with domf f)          *)
(*           f.[\ A] := f.[& domf `\` A]                                     *)
(*                   == f where all the keys in A have been removed          *)
(*           f.[~ k] := f.[\ [fset k]]                                       *)
(*             f + g == concatenation of f and g,                            *)
(*                      the keys of g override the keys of f                 *)
(*                                                                           *)
(******* finitely supported functions ****************************************)
(*                                                                           *)
(* Operation on function with finite support, i.e. finmap with default value *)
(* for elements outside of the support. Contrarly to finmap, these are total *)
(* function, so we provide a coercion to Funclass                            *)
(*                                                                           *)
(* {fsfun K -> T for dflt_fun} == finitely supported functions with default  *)
(*                                value dflt : K -> V outside the support    *)
(* {fsfun K -> T of x => dflt} := {fsfun K -> T for fun x => dflt}           *)
(*    {fsfun K -> T with dflt} := {fsfun K -> T for fun=> dflt}              *)
(*              {fsfun K -> K} := {fsfun K -> T for fun x => x}              *)
(*                                                                           *)
(*         [fsfun for dflt_fun] == the default fsfun                         *)
(*         [fsfun of x => dflt] == the default fsfun                         *)
(*    [fsfun x : A => F | dflt] == the fsfun which takes value F on type A   *)
(*                                 x has type A : {fset T}                   *)
(*   [fsfun x in A => F | dflt] == the fsfun which takes value F on set A    *)
(*                                 x has type T, and x in A : {fset T}       *)
(* we also provide untyped variants and variants where default is ommitted   *)
(* e.g.  [fsfun x : A => F] [fsfun x => F | default] [fsfun]...              *)
(* and many variants to give the possibility to insert a key : unit          *)
(* to prevent conversion from diverging, e.g.                                *)
(* [fsfun[key] x : A => F | default] and [fsfun[key] x in A => F | default]  *)
(*                ...                                                        *)
(*     (f \o g)%fsfun == composition of fsfun                                *)
(*     fsinjectiveb f == boolean predicate of injectivity of f               *)
(*****************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Reserved Notation "A `=` B" (at level 70, no associativity).
Reserved Notation "A `<>` B" (at level 70, no associativity).
Reserved Notation "A `==` B" (at level 70, no associativity).
Reserved Notation "A `!=` B" (at level 70, no associativity).
Reserved Notation "A `=P` B" (at level 70, no associativity).

Reserved Notation "f @`[ key ] A" (at level 24, key at level 0).
Reserved Notation "f @2`[ key ] ( A , B )"
  (at level 24, format "f  @2`[ key ]  ( A ,  B )").
Reserved Notation "f @` A" (at level 24).
Reserved Notation "f @2` ( A , B )" (at level 24, format "f  @2`  ( A ,  B )").

(* unary *)
Reserved Notation "[ 'fset' E | x : T 'in' A ]" (at level 0, E, x at level 99).
Reserved Notation "[ 'fset' E | x 'in' A ]" (at level 0, E, x at level 99).
Reserved Notation "[ 'fset' E | x : A ]" (at level 0, E, x at level 99).
Reserved Notation "[ 'fset'  x  :  T  'in'  A ]" (at level 0, x at level 99).
Reserved Notation "[ 'fset'  x  :  T  'in'  A  |  P ]"
  (at level 0, x at level 99).
Reserved Notation "[ 'fset' x 'in' A | P ]" (at level 0, x at level 99).
Reserved Notation "[ 'fset' x 'in' A ]" (at level 0, x at level 99).
Reserved Notation "[ 'fset' x : T | P ]" (at level 0, x at level 99).
Reserved Notation "[ 'fset' x : T | P & Q ]" (at level 0, x at level 99).
Reserved Notation "[ 'fset'  x  :  T  'in' A  |  P  &  Q ]"
  (at level 0, x at level 99).
Reserved Notation "[ 'fset' x 'in' A | P & Q ]" (at level 0, x at level 99).

(* binary *)
Reserved Notation "[ 'fset' E | x : T 'in' A , y : T' 'in' B ]"
  (at level 0, E, x at level 99, A at level 200, y at level 99).
Reserved Notation "[ 'fset' E | x 'in' A , y 'in' B ]"
  (at level 0, E, x at level 99, A at level 200, y at level 99).

(* keyed parse only *)
Reserved Notation "[ 'fset[' key ] E | x : T 'in' A ]"
  (at level 0, E, x at level 99).
Reserved Notation "[ 'fset[' key ] E | x 'in' A ]"
  (at level 0, E, x at level 99).
Reserved Notation "[ 'fset[' key ] E | x : A ]" (at level 0, E, x at level 99).
Reserved Notation "[ 'fset[' key ] E | x 'in' A & P ]"
  (at level 0, E, x at level 99).
Reserved Notation "[ 'fset[' key ] E | x : A & P ]"
  (at level 0, E, x at level 99).
Reserved Notation "[ 'fset[' key ] E | x : T 'in' A , y : T' 'in' B ]"
  (at level 0, E, x at level 99, A at level 200, y at level 99).
Reserved Notation "[ 'fset[' key ] E | x 'in' A , y 'in' B ]"
  (at level 0, E, x at level 99, A at level 200, y at level 99).
Reserved Notation "[ 'fset[' key ] E | x : A , y : B ]"
  (at level 0, E, x at level 99, A at level 200, y at level 99).
Reserved Notation "[ 'fset[' key ] E | x : A , y 'in' B ]"
  (at level 0, E, x, y at level 99).
Reserved Notation "[ 'fset[' key ] E | x 'in' A , y : B ]"
  (at level 0, E, x, y at level 99).
Reserved Notation "[ 'fset[' key ] E | x 'in' A , y 'in' B & P ]"
  (at level 0, E, x, y at level 99).
Reserved Notation "[ 'fset[' key ] E | x : A , y 'in' B & P ]"
  (at level 0, E, x, y at level 99).
Reserved Notation "[ 'fset[' key ] E | x 'in' A , y : B & P ]"
  (at level 0, E, x, y at level 99).
Reserved Notation "[ 'fset[' key ] E | x : A , y : B & P ]"
  (at level 0, E, x, y at level 99).

Reserved Notation "[ 'fset[' key ]  x  :  T  'in'  A ]"
  (at level 0, x at level 99).
Reserved Notation "[ 'fset[' key ]  x  :  T  'in'  A  |  P ]"
  (at level 0, x at level 99).
Reserved Notation "[ 'fset[' key ] x 'in' A | P ]" (at level 0, x at level 99).
Reserved Notation "[ 'fset[' key ] x 'in' A ]" (at level 0, x at level 99).
Reserved Notation "[ 'fset[' key ] x : T | P ]" (at level 0, x at level 99).
Reserved Notation "[ 'fset[' key ] x : T | P & Q ]" (at level 0, x at level 99).
Reserved Notation "[ 'fset[' key ]  x  :  T  'in' A  |  P  &  Q ]"
  (at level 0, x at level 99).
Reserved Notation "[ 'fset[' key ] x 'in' A | P & Q ]"
  (at level 0, x at level 99).

(* printing only *)
Reserved Notation "[ 'f' 'set' E | x 'in' A ]"
  (at level 0, E, x at level 99,
   format "[ '[hv' 'f' 'set'  E '/ '  |  x  'in'  A ] ']'").
Reserved Notation "[ 'f' 'set' E | x : A ]"
  (at level 0, E, x at level 99,
   format "[ '[hv' 'f' 'set'  E '/ '  |  x  :  A ] ']'").
Reserved Notation "[ 'f' 'set' x 'in' A | P ]"
  (at level 0, x at level 99, format "[ 'f' 'set'  x  'in'  A  |  P ]").
Reserved Notation "[ 'f' 'set' x 'in' A ]"
  (at level 0, x at level 99, format "[ 'f' 'set'  x  'in'  A ]").
Reserved Notation "[ 'f' 'set' x : T | P ]"
  (at level 0, x at level 99, format "[ 'f' 'set'  x  :  T  |  P ]").
Reserved Notation "[ 'f' 'set' x : T | P & Q ]"
  (at level 0, x at level 99, format "[ 'f' 'set'  x  :  T  |  P  &  Q ]").
Reserved Notation "[ 'f' 'set' x 'in' A | P & Q ]"
  (at level 0, x at level 99, format "[ 'f' 'set'  x  'in'  A  |  P  &  Q ]").
(* binary printing only *)
Reserved Notation "[ 'f' 'set' E | x 'in' A , y 'in' B ]"
  (at level 0, E, x at level 99, A at level 200, y at level 99,
   format "[ '[hv' 'f' 'set'  E '/ '  |  x  'in'  A , '/' y  'in'  B ] ']'").

Reserved Notation "{fset K }" (at level 0, format "{fset  K }").
Reserved Notation "[ 'fset' a ]"
  (at level 0, a at level 99, format "[ 'fset'  a ]").
Reserved Notation "[ 'fset' a : T ]"
  (at level 0, a at level 99, format "[ 'fset'  a   :  T ]").
Reserved Notation "A `&` B" (at level 48, left associativity).
Reserved Notation "A `*` B" (at level 46, left associativity).
Reserved Notation "A `+` B" (at level 54, left associativity).
Reserved Notation "A +` B"  (at level 54, left associativity).
Reserved Notation "A `|` B" (at level 52, left associativity).
Reserved Notation "a |` A"  (at level 52, left associativity).
Reserved Notation "A `\` B" (at level 50, left associativity).
Reserved Notation "A `\ b"  (at level 50, left associativity).
Reserved Notation "A `<=` B" (at level 70, no associativity).
Reserved Notation "A `<` B" (at level 70, no associativity).

(* This is left-associative due to historical limitations of the .. Notation. *)
Reserved Notation "[ 'fset' a1 ; a2 ; .. ; an ]"
  (at level 0, a1 at level 99, format "[ 'fset'  a1 ;  a2 ;  .. ;  an ]").

Reserved Notation "[ 'disjoint' A & B ]".

(* Comprehensions *)
Reserved Notation "[ 'fset' E | x 'in' A & P ]" (at level 0, E, x at level 99).
Reserved Notation "[ 'fset' E | x : A & P ]" (at level 0, E, x at level 99).
Reserved Notation "[ 'fset' E | x : A , y 'in' B ]"
  (at level 0, E, x, y at level 99).
Reserved Notation "[ 'fset' E | x 'in' A , y : B ]"
  (at level 0, E, x, y at level 99).
Reserved Notation "[ 'fset' E | x : A , y : B ]"
  (at level 0, E, x, y at level 99).
Reserved Notation "[ 'fset' E | x 'in' A , y 'in' B & P ]"
  (at level 0, E, x, y at level 99).
Reserved Notation "[ 'fset' E | x : A , y 'in' B & P ]"
  (at level 0, E, x, y at level 99).
Reserved Notation "[ 'fset' E | x 'in' A , y : B & P ]"
  (at level 0, E, x, y at level 99).
Reserved Notation "[ 'fset' E | x : A , y : B & P ]"
  (at level 0, E, x, y at level 99).

Reserved Notation "[ 'fsetval' x 'in' A ]" (at level 0, x at level 99).
Reserved Notation "[ 'fsetval' x 'in' A | P ]" (at level 0, x at level 99).
Reserved Notation "[ 'fsetval' x 'in' A | P & Q ]" (at level 0, x at level 99).
Reserved Notation "[ 'fsetval' x : A ]" (at level 0, x at level 99).
Reserved Notation "[ 'fsetval' x : A | P ]" (at level 0, x at level 99).
Reserved Notation "[ 'fsetval' x : A | P & Q ]" (at level 0, x at level 99).

(* keyed parse only *)
Reserved Notation "[ 'fsetval[' key ] x 'in' A ]" (at level 0, x at level 99).
Reserved Notation "[ 'fsetval[' key ] x 'in' A | P ]"
  (at level 0, x at level 99).
Reserved Notation "[ 'fsetval[' key ] x 'in' A | P & Q ]"
  (at level 0, x at level 99).
Reserved Notation "[ 'fsetval[' key ] x : A ]" (at level 0, x at level 99).
Reserved Notation "[ 'fsetval[' key ] x : A | P ]" (at level 0, x at level 99).
Reserved Notation "[ 'fsetval[' key ] x : A | P & Q ]"
  (at level 0, x at level 99).

(* Print-only variants to work around the Coq pretty-printer K-term kink. *)
Reserved Notation "[ 'f' 'set' E | x 'in' A & P ]"
  (at level 0, E, x at level 99,
   format "[ '[hv' 'f' 'set'  E '/ '  |  x  'in'  A '/ '  &  P ] ']'").
Reserved Notation "[ 'f' 'set' E | x : A & P ]"
  (at level 0, E, x at level 99,
   format "[ '[hv' 'f' 'set'  E '/ '  |  x  :  A '/ '  &  P ] ']'").
Reserved Notation "[ 'f' 'set' E | x : A , y 'in' B ]"
  (at level 0, E, x, y at level 99, format
   "[ '[hv' 'f' 'set'  E '/ '  |  x  :  A , '/   '  y  'in'  B ] ']'").
Reserved Notation "[ 'f' 'set' E | x 'in' A , y : B ]"
  (at level 0, E, x, y at level 99, format
   "[ '[hv' 'f' 'set'  E '/ '  |  x  'in'  A , '/   '  y  :  B ] ']'").
Reserved Notation "[ 'f' 'set' E | x : A , y : B ]"
  (at level 0, E, x, y at level 99, format
   "[ '[hv' 'f' 'set'  E '/ '  |  x  :  A , '/   '  y  :  B ] ']'").
Reserved Notation "[ 'f' 'set' E | x 'in' A , y 'in' B & P ]"
  (at level 0, E, x, y at level 99, format
   "[ '[hv' 'f' 'set'  E '/ '  |  x  'in'  A , '/   '  y  'in'  B '/ '  &  P ] ']'").
Reserved Notation "[ 'f' 'set' E | x : A , y 'in' B & P ]"
  (at level 0, E, x, y at level 99, format
   "[ '[hv' 'f' 'set'  E '/ '  |  x  :  A , '/   '  y  'in'  B  &  P ] ']'").
Reserved Notation "[ 'f' 'set' E | x 'in' A , y : B & P ]"
  (at level 0, E, x, y at level 99, format
   "[ '[hv' 'f' 'set'  E '/ '  |  x  'in'  A , '/   '  y  :  B  &  P ] ']'").
Reserved Notation "[ 'f' 'set' E | x : A , y : B & P ]"
  (at level 0, E, x, y at level 99, format
   "[ '[hv' 'f' 'set'  E '/ '  |  x  :  A , '/   '  y  :  B  &  P ] ']'").

Reserved Notation "[ 'f' 'setval' x 'in' A ]"
  (at level 0, x at level 99, format "[ 'f' 'setval'  x  'in'  A ]").
Reserved Notation "[ 'f' 'setval' x 'in' A | P ]"
  (at level 0, x at level 99, format "[ 'f' 'setval'  x  'in'  A  |  P ]").
Reserved Notation "[ 'f' 'setval' x 'in' A | P & Q ]"
  (at level 0, x at level 99,
   format "[ 'f' 'setval'  x  'in'  A  |  P  &  Q ]").
Reserved Notation "[ 'f' 'setval' x : A ]"
  (at level 0, x at level 99, format "[ 'f' 'setval'  x  :  A ]").
Reserved Notation "[ 'f' 'setval' x : A | P ]"
  (at level 0, x at level 99, format "[ 'f' 'setval'  x  :  A  |  P ]").
Reserved Notation "[ 'f' 'setval' x : A | P & Q ]"
  (at level 0, x at level 99, format "[ 'f' 'setval'  x  :  A  |  P  &  Q ]").

Reserved Notation "\bigcup_ ( i <- r | P ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \bigcup_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\bigcup_ ( i <- r ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \bigcup_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\bigcup_ ( i | P ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \bigcup_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\bigcup_ ( i 'in' A | P ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \bigcup_ ( i  'in'  A  |  P ) '/  '  F ']'").
Reserved Notation "\bigcup_ ( i 'in' A ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \bigcup_ ( i  'in'  A ) '/  '  F ']'").

Reserved Notation "{fmap T }" (at level 0, format "{fmap  T }").
Reserved Notation "x .[ k <- v ]"
  (at level 2, k at level 200, v at level 200, format "x .[ k  <-  v ]").
Reserved Notation "x .[~ k ]" (at level 2, k at level 200, format "x .[~  k ]").
Reserved Notation "x .[& k ]" (at level 2, k at level 200, format "x .[&  k ]").
Reserved Notation "x .[\ k ]" (at level 2, k at level 200, format "x .[\  k ]").
Reserved Notation "x .[? k ]" (at level 2, k at level 200, format "x .[?  k ]").
Reserved Infix "`~`" (at level 52).
Reserved Notation "[ 'fset' k ]" (at level 0, k at level 99, format "[ 'fset'  k ]").

(* Copy of the ssrbool shim to ensure compatibility with MathComp v1.8.0. *)
Definition PredType : forall T pT, (pT -> pred T) -> predType T.
exact PredType || exact mkPredType.
Defined.
Arguments PredType [T pT] toP.

Local Notation predOfType T := (pred_of_simpl (@pred_of_argType T)).

Definition oextract (T : Type) (o : option T) : o -> T :=
  if o is Some t return o -> T then fun=> t else False_rect T \o notF.

Lemma oextractE (T : Type) (x : T) (xP : Some x) : oextract xP = x.
Proof. by []. Qed.

Lemma Some_oextract T (x : option T) (x_ex : x) : Some (oextract x_ex) = x.
Proof. by case: x x_ex. Qed.

Definition ojoin T (x : option (option T)) :=
  if x is Some y then y else None.

Lemma Some_ojoin T (x : option (option T)) : x -> Some (ojoin x) = x.
Proof. by case : x. Qed.

Lemma ojoinT T (x : option (option T)) : ojoin x -> x.
Proof. by case: x. Qed.

Lemma TaggedP (T1 : Type) (T2 : T1 -> Type) (P : forall x, T2 x -> Type) :
    (forall t : {x : T1 & T2 x}, P _ (tagged t)) ->
  forall (x : T1) (y : T2 x), P x y.
Proof. by move=> /(_ (Tagged _ _)). Qed.
Arguments TaggedP {T1} T2.

Module Type SortKeysSig.
Section SortKeys.
Variable (K : choiceType).
Implicit Types (k : K) (ks : seq K).

Axiom f : seq K -> seq K.
Axiom perm : forall s, perm_eq (f s) (undup s).
Axiom uniq : forall s, uniq (f s).
Axiom E : forall (s : seq K), f s =i s.
Axiom eq : forall (s s' : seq K), s =i s' <-> f s = f s'.
End SortKeys.
End SortKeysSig.

Module SortKeys : SortKeysSig.
Section SortKeys.
Variable (K : choiceType).
Implicit Types (k : K) (ks : seq K).
Definition f (s : seq K) := choose (perm_eq (undup s)) (undup s).
Fact perm s : perm_eq (f s) (undup s).
Proof. by rewrite perm_sym chooseP. Qed.
Fact uniq s : uniq (f s).
Proof. by rewrite (perm_uniq (perm _)) undup_uniq. Qed.
Fact E (s : seq K) : f s =i s.
Proof. by move=> x; rewrite (perm_mem (perm _)) mem_undup. Qed.
Lemma eq (s s' : seq K) : s =i s' <-> f s = f s'.
Proof.
split=> [eq_ss'|eq_ss' k]; last by rewrite -E eq_ss' E.
rewrite /f; have peq_ss' : perm_eq (undup s) (undup s').
  by apply: uniq_perm; rewrite ?undup_uniq // => x; rewrite !mem_undup.
rewrite (@choose_id _ _ _ (undup s')) //=; apply: eq_choose => x /=.
by apply: sym_left_transitive; [exact: perm_sym | exact: (@perm_trans)|].
Qed.
End SortKeys.
End SortKeys.

Hint Resolve SortKeys.perm : core.
Hint Resolve SortKeys.uniq : core.
Hint Resolve SortKeys.E : core.

Notation sort_keys      := SortKeys.f.
Notation sort_keys_perm := SortKeys.perm.
Notation sort_keys_uniq := SortKeys.uniq.
Notation sort_keysE     := SortKeys.E.
Notation eq_sort_keys   := SortKeys.eq.

Section ChoiceKeys.
Variable (K : choiceType).
Implicit Types (k : K) (ks : seq K).

Lemma mem_sort_keys ks k : k \in ks -> k \in sort_keys ks.
Proof. by rewrite sort_keysE. Qed.

Lemma mem_sort_keys_intro ks k : k \in sort_keys ks -> k \in ks.
Proof. by rewrite sort_keysE. Qed.

Lemma sort_keys_nil : sort_keys [::] = [::] :> seq K.
Proof.
have := sort_keysE ([::] : seq K).
by case: sort_keys => //= a l /(_ a); rewrite mem_head.
Qed.

Lemma sort_keys_id ks : sort_keys (sort_keys ks) = sort_keys ks.
Proof. by have /eq_sort_keys := sort_keysE ks. Qed.

Definition canonical_keys ks := sort_keys ks == ks.

Lemma canonical_uniq ks : canonical_keys ks -> uniq ks.
Proof. by move=> /eqP <-; exact: sort_keys_uniq. Qed.

Lemma canonical_sort_keys ks : canonical_keys (sort_keys ks).
Proof. by rewrite /canonical_keys sort_keys_id. Qed.

Lemma canonical_eq_keys ks ks' :
  canonical_keys ks -> canonical_keys ks' ->
  ks =i ks' -> ks = ks'.
Proof.
move=> /eqP; case: _ /; move=> /eqP; case: _ / => eq_ks_ks'.
by apply/eq_sort_keys => x; rewrite -sort_keysE eq_ks_ks' sort_keysE.
Qed.

Lemma size_sort_keys ks : size (sort_keys ks) = size (undup ks).
Proof. exact: perm_size. Qed.

End ChoiceKeys.
Arguments eq_sort_keys {K s s'}.

(***************)
(* Finite sets *)
(***************)

Section Def.
Variables (K : choiceType).

Structure finSet : Type := mkFinSet {
  enum_fset :> seq K;
  _ : canonical_keys enum_fset
}.

Definition finset_of (_ : phant K) := finSet.

End Def.

Identity Coercion type_of_finset : finset_of >-> finSet.
Notation "{fset T }" := (@finset_of _ (Phant T)) : type_scope.

Definition pred_of_finset (K : choiceType)
  (f : finSet K) : pred K := fun k => k \in (enum_fset f).
Canonical finSetPredType (K : choiceType) := PredType (@pred_of_finset K).

Section FinSetCanonicals.

Variable (K : choiceType).

Canonical fsetType := Eval hnf in [subType for (@enum_fset K)].
Definition fset_eqMixin := Eval hnf in [eqMixin of {fset K} by <:].
Canonical fset_eqType := Eval hnf in EqType {fset K} fset_eqMixin.
Definition fset_choiceMixin := Eval hnf in [choiceMixin of {fset K} by <:].
Canonical fset_choiceType := Eval hnf in ChoiceType {fset K} fset_choiceMixin.

End FinSetCanonicals.

Section FinTypeSet.

Variables (K : choiceType) (A : finSet K).

Lemma keys_canonical : canonical_keys (enum_fset A).
Proof. by case: A. Qed.

Lemma fset_uniq : uniq (enum_fset A).
Proof. by rewrite canonical_uniq // keys_canonical. Qed.

Record fset_sub_type : predArgType :=
  FSetSub {fsval : K; fsvalP : in_mem fsval (@mem K _ A)}.

Canonical fset_sub_subType := Eval hnf in [subType for fsval].
Definition fset_sub_eqMixin := Eval hnf in [eqMixin of fset_sub_type by <:].
Canonical fset_sub_eqType := Eval hnf in EqType fset_sub_type fset_sub_eqMixin.
Definition fset_sub_choiceMixin := Eval hnf in [choiceMixin of fset_sub_type by <:].
Canonical fset_sub_choiceType := Eval hnf in ChoiceType fset_sub_type fset_sub_choiceMixin.
Definition fset_countMixin (T : countType) := Eval hnf in [countMixin of {fset T} by <:].
Canonical fset_countType (T : countType) := Eval hnf in CountType {fset T} (fset_countMixin T).


Definition fset_sub_enum : seq fset_sub_type :=
  undup (pmap insub (enum_fset A)).

Lemma mem_fset_sub_enum x : x \in fset_sub_enum.
Proof. by rewrite mem_undup mem_pmap -valK map_f // fsvalP. Qed.

Lemma val_fset_sub_enum : map val fset_sub_enum = enum_fset A.
Proof.
rewrite /fset_sub_enum undup_id ?pmap_sub_uniq ?fset_uniq//.
rewrite (pmap_filter (@insubK _ _ _)); apply/all_filterP.
by apply/allP => x; rewrite isSome_insub.
Qed.

Definition fset_sub_pickle x := index x fset_sub_enum.
Definition fset_sub_unpickle n := nth None (map some fset_sub_enum) n.
Lemma fset_sub_pickleK : pcancel fset_sub_pickle fset_sub_unpickle.
Proof.
rewrite /fset_sub_unpickle => x.
by rewrite (nth_map x) ?nth_index ?index_mem ?mem_fset_sub_enum.
Qed.

Definition fset_sub_countMixin := CountMixin fset_sub_pickleK.
Canonical fset_sub_countType := Eval hnf in CountType fset_sub_type fset_sub_countMixin.

Definition fset_sub_finMixin :=
  Eval hnf in UniqFinMixin (undup_uniq _) mem_fset_sub_enum.
Canonical fset_sub_finType := Eval hnf in FinType fset_sub_type fset_sub_finMixin.
Canonical fset_sub_subfinType := [subFinType of fset_sub_type].

Lemma enum_fsetE : enum_fset A = [seq val i | i <- enum fset_sub_type].
Proof. by rewrite enumT unlock val_fset_sub_enum. Qed.

Lemma cardfE : size (enum_fset A) = #|fset_sub_type|.
Proof. by rewrite cardE enum_fsetE size_map. Qed.

End FinTypeSet.

Identity Coercion finSet_sub_type : finset_of >-> finSet.
Coercion fset_sub_type : finSet >-> predArgType.
Hint Resolve fsvalP fset_uniq mem_fset_sub_enum : core.

Declare Scope fset_scope.
Delimit Scope fset_scope with fset.
Local Open Scope fset_scope.

Notation "[` kf ]" := (FSetSub kf) (format "[`  kf ]") : fset_scope.

Lemma fsetsubE (T : choiceType) (A : {fset T}) (x : A) (xA : val x \in A) :
 [` xA] = x.
Proof. by apply/val_inj => /=. Qed.

Notation "#|` A |" := (size (enum_fset A))
  (at level 0, A at level 99, format "#|`  A |") : nat_scope.
Definition fset_predT {T : choiceType} {A : {fset T}} : simpl_pred A := @predT A.
Definition set_of_fset (K : choiceType) (A : {fset K}) : {set A} :=
  [set x in {: A}].

Arguments pred_of_finset : simpl never.

Section SeqFset.

Variable finset_key : unit.
Definition seq_fset : forall K : choiceType, seq K -> {fset K} :=
   locked_with finset_key (fun K s => mkFinSet (@canonical_sort_keys K s)).

Variable (K : choiceType) (s : seq K).

Lemma seq_fsetE : seq_fset s =i s.
Proof. by move=> a; rewrite [seq_fset]unlock sort_keysE. Qed.

Lemma size_seq_fset : size (seq_fset s) = size (undup s).
Proof. by rewrite [seq_fset]unlock /= size_sort_keys. Qed.

Lemma seq_fset_uniq  : uniq (seq_fset s).
Proof. by rewrite [seq_fset]unlock /= sort_keys_uniq. Qed.

Lemma seq_fset_perm : perm_eq (seq_fset s) (undup s).
Proof. by rewrite [seq_fset]unlock //= sort_keys_perm. Qed.

End SeqFset.

Hint Resolve keys_canonical : core.
Hint Resolve sort_keys_uniq : core.

Canonical  finSetSubType K := [subType for (@enum_fset K)].
Definition finSetEqMixin (K : choiceType) := [eqMixin of {fset K} by <:].
Canonical  finSetEqType  (K : choiceType) := EqType {fset K} (finSetEqMixin K).
Definition finSetChoiceMixin (K : choiceType) := [choiceMixin of {fset K} by <:].
Canonical  finSetChoiceType  (K : choiceType) := ChoiceType {fset K} (finSetChoiceMixin K).

Section FinPredStruct.

Structure finpredType (T : eqType) := FinPredType {
  finpred_sort :> Type;
  tofinpred : finpred_sort -> pred T;
  _ : {finpred_seq : finpred_sort -> seq T |
       ((forall p, uniq (finpred_seq p))
       * forall p x, x \in finpred_seq p = tofinpred p x)%type}
}.

Canonical finpredType_predType (T : eqType) (fpT : finpredType T) :=
  @PredType T (finpred_sort fpT) (@tofinpred T fpT).

Definition enum_finpred  (T : eqType) (fpT : finpredType T) :
    fpT -> seq T :=
  let: FinPredType _ _ (exist s _) := fpT in s.

Lemma enum_finpred_uniq (T : eqType) (fpT : finpredType T) (p : fpT) :
   uniq (enum_finpred p).
Proof. by case: fpT p => ?? [s sE] p; rewrite sE. Qed.

Lemma enum_finpredE (T : eqType) (fpT : finpredType T) (p : fpT) :
   enum_finpred p =i p.
Proof. by case: fpT p => ?? [s sE] p x; rewrite sE -topredE. Qed.

Lemma mkFinPredType_of_subproof (T : eqType) (pT : predType T)
   (fpred_seq : pT -> seq T) (pred_fsetE : forall p, fpred_seq p =i p) :
  forall p x, x \in fpred_seq p = topred p x.
Proof. by move=> p x; rewrite topredE pred_fsetE. Qed.

Definition mkFinPredType_of (T : eqType) (U : Type) :=
  fun (pT : predType T) & pred_sort pT -> U =>
  fun a (pT' := @PredType T U a) & phant_id pT' pT =>
  fun (fpred_seq : pT' -> seq T)
      (fpred_seq_uniq : forall p, uniq (fpred_seq p))
      (fpred_seqE : forall p, fpred_seq p =i p) =>
  @FinPredType T U a (exist _ fpred_seq
   (fpred_seq_uniq, (mkFinPredType_of_subproof fpred_seqE))).

Definition clone_finpredType (T : eqType) (U : Type) :=
  fun (pT : finpredType T) & finpred_sort pT -> U =>
  fun a pP (pT' := @FinPredType T U a pP) & phant_id pT' pT => pT'.

Structure is_finite (T : eqType) (P : pred T) := IsFinite {
  seq_of_is_finite :> seq T;
  _ : uniq seq_of_is_finite;
  _ : forall x, x \in seq_of_is_finite = P x;
}.

Lemma is_finite_uniq (T : eqType) (P : pred T) (p : is_finite P) : uniq p.
Proof. by case: p. Qed.

Lemma is_finiteE (T : eqType) (P : pred T) (p : is_finite P) x :
  x \in (seq_of_is_finite p) = P x.
Proof. by case: p. Qed.

Structure finpred (T : eqType) (pT : predType T) := FinPred {
  pred_of_finpred :> pT;
  _ : is_finite [pred x in pred_of_finpred]
}.

Definition enum_fin (T : eqType) (pT : predType T) (p : finpred pT) : seq T :=
  let: FinPred _ fp := p in fp.

Lemma enum_fin_uniq (T : eqType) (pT : predType T) (p : finpred pT) :
  uniq (enum_fin p).
Proof. by case: p => ?[]. Qed.

Lemma enum_finE  (T : eqType) (pT : predType T) (p : finpred pT) :
  enum_fin p =i (pred_of_finpred p).
Proof. by case: p => ?[]. Qed.

Canonical fin_finpred (T : eqType) (pT : finpredType T) (p : pT) :=
  @FinPred _ _ p (@IsFinite _ _ (enum_finpred p)
                            (enum_finpred_uniq p) (enum_finpredE p)).

Definition finpred_of (T : eqType) (pT : predType T) (p : pT)
 (fp : finpred pT) & phantom pT fp : finpred pT := fp.

Structure finmempred (T : eqType) := FinMemPred {
  pred_of_finmempred :> mem_pred T;
  _ : is_finite (fun x => in_mem x pred_of_finmempred)
}.

Definition enum_finmem (T : eqType) (p : finmempred T) : seq T :=
  let: FinMemPred _ fp := p in fp.

Lemma enum_finmem_uniq (T : eqType) (p : finmempred T) :
  uniq (enum_finmem p).
Proof. by case: p => ?[]. Qed.

Lemma enum_finmemE  (T : eqType) (p : finmempred T) :
  enum_finmem p =i p.
Proof. by case: p => ?[]. Qed.

Definition finmempred_of (T : eqType) (P : pred T)
 (mP : finmempred T) & phantom (mem_pred T) mP : finmempred T := mP.

Canonical mem_fin (T : eqType) (pT : predType T) (p : finpred pT) :=
  @FinMemPred  _ (mem p)
   (@IsFinite _ _ (enum_fin p) (enum_fin_uniq p) (enum_finE p)).

End FinPredStruct.

Notation "[ 'finpredType' 'of' T ]" := (@clone_finpredType _ T _ id _ _ id)
  (at level 0, format "[ 'finpredType'  'of'  T ]") : form_scope.

Notation mkFinPredType T s s_uniq sE :=
  (@mkFinPredType_of _ T _ id _ id s s_uniq sE).

Section CanonicalFinPred.

Canonical fset_finpredType (T: choiceType) :=
  mkFinPredType (finSet T) (@enum_fset T) (@fset_uniq T)  (fun _ _ => erefl).

Canonical pred_finpredType (T : finType) :=
  mkFinPredType (pred T) (fun P => enum_mem (mem P)) (@enum_uniq T) (@mem_enum T).

Canonical simpl_pred_finpredType (T : finType) :=
  mkFinPredType (simpl_pred T) (fun P => enum_mem (mem P)) (@enum_uniq T) (@mem_enum T).

Canonical fset_finpred (T: choiceType) (A : finSet T) :=
  @FinPred _ _ (enum_fset A)
     (@IsFinite _ _ (enum_fset A) (fset_uniq _) (fun=> erefl)).

Program Canonical subfinset_finpred (T : choiceType)
  (A : finmempred T) (Q : pred T) :=
  @FinPred _ _ [pred x in A | Q x]
          (@IsFinite _ _ [seq x <- enum_finmem A | Q x] _ _).
Next Obligation. by rewrite filter_uniq// enum_finmem_uniq. Qed.
Next Obligation. by rewrite !inE !mem_filter andbC enum_finmemE. Qed.

Canonical seq_finpredType (T : eqType) :=
  mkFinPredType (seq T) undup (@undup_uniq T) (@mem_undup T).

End CanonicalFinPred.

Local Notation imfset_def key :=
  (fun (T K : choiceType) (f : T -> K) (p : finmempred T)
       of phantom (mem_pred T) p => seq_fset key [seq f x | x <- enum_finmem p]).
Local Notation imfset2_def key :=
  (fun (K T1 : choiceType) (T2 : T1 -> choiceType)
       (f : forall x : T1, T2 x -> K)
       (p1 : finmempred T1) (p2 : forall x : T1, finmempred (T2 x))
   of phantom (mem_pred T1) p1 & phantom (forall x, mem_pred (T2 x)) p2 =>
  seq_fset key [seq f x y | x <- enum_finmem p1, y <- enum_finmem (p2 x)]).

Module Type ImfsetSig.
Parameter imfset : forall (key : unit) (T K : choiceType)
       (f : T -> K) (p : finmempred T),
  phantom (mem_pred T) p ->  {fset K}.
Parameter imfset2 : forall (key : unit) (K T1 : choiceType)
       (T2 : T1 -> choiceType)(f : forall x : T1, T2 x -> K)
       (p1 : finmempred T1) (p2 : forall x : T1, finmempred (T2 x)),
  phantom (mem_pred T1) p1 -> phantom (forall x, mem_pred (T2 x)) p2 -> {fset K}.
Axiom imfsetE : forall key, imfset key = imfset_def key.
Axiom imfset2E : forall key, imfset2 key = imfset2_def key.
End ImfsetSig.

Module Imfset : ImfsetSig.
Definition imfset key := imfset_def key.
Definition imfset2 key := imfset2_def key.
Lemma imfsetE key : imfset key = imfset_def key. Proof. by []. Qed.
Lemma imfset2E key : imfset2 key = imfset2_def key. Proof. by []. Qed.
End Imfset.

Notation imfset key f p :=
   (Imfset.imfset key f (Phantom _ (pred_of_finmempred p))).
Notation imfset2 key f p q :=
   (Imfset.imfset2 key f (Phantom _ (pred_of_finmempred p))
                   (Phantom _ (fun x => (pred_of_finmempred (q x))))).
Canonical imfset_unlock k := Unlockable (Imfset.imfsetE k).
Canonical imfset2_unlock k := Unlockable (Imfset.imfset2E k).

Notation "A `=` B" := (A = B :> {fset _}) (only parsing) : fset_scope.
Notation "A `<>` B" := (A <> B :> {fset _}) (only parsing) : fset_scope.
Notation "A `==` B" := (A == B :> {fset _}) (only parsing) : fset_scope.
Notation "A `!=` B" := (A != B :> {fset _}) (only parsing) : fset_scope.
Notation "A `=P` B" := (A =P B :> {fset _}) (only parsing) : fset_scope.

Notation "f @`[ key ] A" :=
  (Imfset.imfset key f (Phantom _ (mem A))) : fset_scope.
Notation "f @2`[ key ] ( A , B )" :=
   (Imfset.imfset2 key f (Phantom _ (mem A)) (Phantom _ (fun x => (mem (B x)))))
  : fset_scope.

Fact imfset_key : unit. Proof. exact: tt. Qed.

Notation "f @` A" := (f @`[imfset_key] A) : fset_scope.
Notation "f @2` ( A , B )" := (f @2`[imfset_key] (A, B)) : fset_scope.

(* unary *)
Notation "[ 'fset' E | x : T 'in' A ]" :=
  ((fun x : T => E) @` A) (only parsing) : fset_scope.
Notation "[ 'fset' E | x 'in' A ]" :=
  [fset E | x : _ in A] (only parsing) : fset_scope.
Notation "[ 'fset' E | x : A ]" :=
  [fset E | x : _ in {: A} ] (only parsing) : fset_scope.
Notation "[ 'fset'  x  :  T  'in'  A ]" :=
  [fset (x : T) | x in A] (only parsing) : fset_scope.
Notation "[ 'fset'  x  :  T  'in'  A  |  P ]" :=
  [fset (x : T) | x in [pred x in A | P]] (only parsing) : fset_scope.
Notation "[ 'fset' x 'in' A | P ]" :=
  [fset x : _ in A | P] (only parsing) : fset_scope.
Notation "[ 'fset' x 'in' A ]" :=
  [fset x : _ in A ] (only parsing) : fset_scope.
Notation "[ 'fset' x : T | P ]" :=
  [fset x in {: T} | P] (only parsing) : fset_scope.
Notation "[ 'fset' x : T | P & Q ]" :=
  [fset x : T | P && Q] (only parsing) : fset_scope.
Notation "[ 'fset'  x  :  T  'in' A  |  P  &  Q ]" :=
  [fset x : T in A | P && Q] (only parsing) : fset_scope.
Notation "[ 'fset' x 'in' A | P & Q ]" :=
  [fset x in A | P && Q] (only parsing) : fset_scope.

(* binary *)
Notation "[ 'fset' E | x : T 'in' A , y : T' 'in' B ]" :=
  ((fun (x : T) (y : T') => E) @2` (A, fun x => B)) (only parsing) : fset_scope.
Notation "[ 'fset' E | x 'in' A , y 'in' B ]" :=
  [fset E | x : _ in A, y : _ in B] (only parsing) : fset_scope.

(* keyed parse only *)
Notation "[ 'fset[' key ] E | x : T 'in' A ]" :=
  ((fun x : T => E) @`[key] A) (only parsing) : fset_scope.
Notation "[ 'fset[' key ] E | x 'in' A ]" :=
  [fset[key] E | x : _ in A] (only parsing) : fset_scope.
Notation "[ 'fset[' key ] E | x : A ]" :=
  [fset[key] E | x : _ in {: A} ] (only parsing) : fset_scope.
Notation "[ 'fset[' key ]  x  :  T  'in'  A ]" :=
  [fset[key] (x : T) | x in A] (only parsing) : fset_scope.
Notation "[ 'fset[' key ]  x  :  T  'in'  A  |  P ]" :=
  [fset[key] (x : T) | x in [pred x in A | P]] (only parsing) : fset_scope.
Notation "[ 'fset[' key ] x 'in' A | P ]" :=
  [fset[key] x : _ in A | P] (only parsing) : fset_scope.
Notation "[ 'fset[' key ] x 'in' A ]" :=
  [fset[key] x : _ in A ] (only parsing) : fset_scope.
Notation "[ 'fset[' key ] x : T | P ]" :=
  [fset[key] x in {: T} | P] (only parsing) : fset_scope.
Notation "[ 'fset[' key ] x : T | P & Q ]" :=
  [fset[key] x : T | P && Q] (only parsing) : fset_scope.
Notation "[ 'fset[' key ]  x  :  T  'in' A  |  P  &  Q ]" :=
  [fset[key] x : T in A | P && Q] (only parsing) : fset_scope.
Notation "[ 'fset[' key ] x 'in' A | P & Q ]" :=
  [fset[key] x in A | P && Q] (only parsing) : fset_scope.

Notation "[ 'fset[' key ] E | x : T 'in' A , y : T' 'in' B ]" :=
  ((fun (x : T) (y : T') => E) @2` (A, fun x => B))
  (only parsing) : fset_scope.
Notation "[ 'fset[' key ] E | x 'in' A , y 'in' B ]" :=
  [fset[key] E | x : _ in A, y : _ in B] (only parsing) : fset_scope.
Notation "[ 'fset[' key ] E | x : A , y : B ]" :=
  [fset[key] E | x : _ in {: A}, y : _ in {: B}] (only parsing) : fset_scope.

(* printing only *)
Notation "[ 'f' 'set' E | x 'in' A ]" := [fset[_] E | x in A] : fset_scope.
Notation "[ 'f' 'set' E | x : A ]" := [fset[_] E | x : A] : fset_scope.
Notation "[ 'f' 'set' x 'in' A | P ]" := [fset[_] x in A | P] : fset_scope.
Notation "[ 'f' 'set' x 'in' A ]" := [fset[_] x in A] : fset_scope.
Notation "[ 'f' 'set' x : T | P ]" := [fset[_] x : T | P] : fset_scope.
Notation "[ 'f' 'set' x : T | P & Q ]" := [fset[_] x : T | P & Q] : fset_scope.
Notation "[ 'f' 'set' x 'in' A | P & Q ]" :=
  [fset[_] x in A | P & Q] : fset_scope.
(* binary printing only*)
Notation "[ 'f' 'set' E | x 'in' A , y 'in' B ]" :=
  [fset[_] E | x in A, y in B] : fset_scope.

Section Ops.

Context {K K': choiceType}.
Implicit Types (a b c : K) (A B C D : {fset K}) (E : {fset K'}) (s : seq K).

Definition fset0 : {fset K} :=
  @mkFinSet K [::] (introT eqP (@sort_keys_nil K)).
(* very transparent, to ensure x \in fset0 is convertible to false *)

Fact fset1_key : unit. Proof. exact: tt. Qed.
Definition fset1 a : {fset K} := [fset[fset1_key] x in [:: a]].

Fact fsetU_key : unit. Proof. exact: tt. Qed.
Definition fsetU A B := [fset[fsetU_key] x in enum_fset A ++ enum_fset B].

Fact fsetI_key : unit. Proof. exact: tt. Qed.
Definition fsetI A B := [fset[fsetI_key] x in A | x \in B].

Fact fsetD_key : unit. Proof. exact: tt. Qed.
Definition fsetD A B := [fset[fsetD_key] x in A | x \notin B].

Fact fsetM_key : unit. Proof. exact: tt. Qed.
Definition fsetM A E := [fset[fsetM_key] (x, y) | x : K in A, y : K' in E].

Definition fsubset A B := fsetI A B == A.

Definition fproper A B := fsubset A B && ~~ fsubset B A.

Definition fdisjoint A B := (fsetI A B == fset0).

End Ops.

Notation "[ 'fset' a ]" := (fset1 a) : fset_scope.
Notation "[ 'fset' a : T ]" := [fset (a : T)] : fset_scope.
Notation "A `|` B" := (fsetU A B) : fset_scope.
Notation "a |` A" := ([fset a] `|` A) : fset_scope.

(* This is left-associative due to historical limitations of the .. Notation. *)
Notation "[ 'fset' a1 ; a2 ; .. ; an ]" :=
  (fsetU .. (a1 |` [fset a2]) .. [fset an]) : fset_scope.
Notation "A `&` B" := (fsetI A B) : fset_scope.
Notation "A `*` B" := (fsetM A B) : fset_scope.
Notation "A `\` B" := (fsetD A B) : fset_scope.
Notation "A `\ a" := (A `\` [fset a]) : fset_scope.

Notation "A `<=` B" := (fsubset A B) : fset_scope.
Notation "A `<` B" := (fproper A B) : fset_scope.

Notation "[ 'disjoint' A & B ]" := (fdisjoint A B) : fset_scope.

(* Comprehensions *)
Notation "[ 'fset' E | x 'in' A & P ]" :=
  [fset E | x in [pred x in A | P]] (only parsing) : fset_scope.
Notation "[ 'fset' E | x : A & P ]" :=
  [fset E | x in {: A} & P] (only parsing) : fset_scope.
Notation "[ 'fset' E | x : A , y 'in' B ]" :=
  [fset E | x in {: A}, y in B] (only parsing) : fset_scope.
Notation "[ 'fset' E | x 'in' A , y : B ]" :=
  [fset E | x in A, y in {: B}] (only parsing) : fset_scope.
Notation "[ 'fset' E | x : A , y : B ]" :=
  [fset E | x in {: A}, y in {: B}] (only parsing) : fset_scope.
Notation "[ 'fset' E | x 'in' A , y 'in' B & P ]" :=
  [fset E | x in A, y in [pred y in B | P]] (only parsing) : fset_scope.
Notation "[ 'fset' E | x : A , y 'in' B & P ]" :=
  [fset E | x in {: A}, y in B & P] (only parsing) : fset_scope.
Notation "[ 'fset' E | x 'in' A , y : B & P ]" :=
  [fset E | x in A, y in {: B} & P] (only parsing) : fset_scope.
Notation "[ 'fset' E | x : A , y : B & P ]" :=
  [fset E | x in {: A}, y in {: B} & P] (only parsing) : fset_scope.

Notation "[ 'fsetval' x 'in' A ]" :=
  [fset val x | x in A] (only parsing) : fset_scope.
Notation "[ 'fsetval' x 'in' A | P ]" :=
  [fset val x | x in A & P] (only parsing) : fset_scope.
Notation "[ 'fsetval' x 'in' A | P & Q ]" :=
  [fsetval x in A | (P && Q)] (only parsing) : fset_scope.
Notation "[ 'fsetval' x : A ]" :=
  [fset val x | x in {: A}] (only parsing) : fset_scope.
Notation "[ 'fsetval' x : A | P ]" :=
  [fset val x | x in {: A} & P] (only parsing) : fset_scope.
Notation "[ 'fsetval' x : A | P & Q ]" :=
  [fsetval x in {: A} | (P && Q)] (only parsing) : fset_scope.

(* keyed parse only *)
Notation "[ 'fset[' key ] E | x 'in' A & P ]" :=
  [fset[key] E | x in [pred x in A | P]] (only parsing) : fset_scope.
Notation "[ 'fset[' key ] E | x : A & P ]" :=
  [fset[key] E | x in {: A} & P] (only parsing) : fset_scope.
Notation "[ 'fset[' key ] E | x : A , y 'in' B ]" :=
  [fset[key] E | x in {: A}, y in B] (only parsing) : fset_scope.
Notation "[ 'fset[' key ] E | x 'in' A , y : B ]" :=
  [fset[key] E | x in A, y in {: B}] (only parsing) : fset_scope.
Notation "[ 'fset[' key ] E | x : A , y : B ]" :=
  [fset[key] E | x in {: A}, y in {: B}] (only parsing) : fset_scope.
Notation "[ 'fset[' key ] E | x 'in' A , y 'in' B & P ]" :=
  [fset[key] E | x in A, y in [pred y in B | P]] (only parsing) : fset_scope.
Notation "[ 'fset[' key ] E | x : A , y 'in' B & P ]" :=
  [fset[key] E | x in {: A}, y in B & P] (only parsing) : fset_scope.
Notation "[ 'fset[' key ] E | x 'in' A , y : B & P ]" :=
  [fset[key] E | x in A, y in {: B} & P] (only parsing) : fset_scope.
Notation "[ 'fset[' key ] E | x : A , y : B & P ]" :=
  [fset[key] E | x in {: A}, y in {: B} & P] (only parsing) : fset_scope.

Notation "[ 'fsetval[' key ] x 'in' A ]" :=
  [fset[key] val x | x in A] (only parsing) : fset_scope.
Notation "[ 'fsetval[' key ] x 'in' A | P ]" :=
  [fset[key] val x | x in A & P] (only parsing) : fset_scope.
Notation "[ 'fsetval[' key ] x 'in' A | P & Q ]" :=
  [fsetval[key] x in A | (P && Q)] (only parsing) : fset_scope.
Notation "[ 'fsetval[' key ] x : A ]" :=
  [fset[key] val x | x in {: A}] (only parsing) : fset_scope.
Notation "[ 'fsetval[' key ] x : A | P ]" :=
  [fset[key] val x | x in {: A} & P] (only parsing) : fset_scope.
Notation "[ 'fsetval[' key ] x : A | P & Q ]" :=
  [fsetval[key] x in {: A} | (P && Q)] (only parsing) : fset_scope.

(* Print-only variants to work around the Coq pretty-printer K-term kink. *)
  Notation "[ 'f' 'set' E | x 'in' A & P ]" :=
  [fset[_] E | x in A & P] : fset_scope.
Notation "[ 'f' 'set' E | x : A & P ]" := [fset[_] E | x : A & P] : fset_scope.
Notation "[ 'f' 'set' E | x : A , y 'in' B ]" :=
  [fset[_] E | x : A, y in B] : fset_scope.
Notation "[ 'f' 'set' E | x 'in' A , y : B ]" :=
  [fset[_] E | x in A, y : B] : fset_scope.
Notation "[ 'f' 'set' E | x : A , y : B ]" :=
  [fset[_] E | x : A, y : B] : fset_scope.
Notation "[ 'f' 'set' E | x 'in' A , y 'in' B & P ]" :=
  [fset[_] E | x in A, y in B & P] : fset_scope.
Notation "[ 'f' 'set' E | x : A , y 'in' B & P ]" :=
  [fset[_] E | x : A, y in B & P] : fset_scope.
Notation "[ 'f' 'set' E | x 'in' A , y : B & P ]" :=
  [fset[_] E | x in A, y : B & P] : fset_scope.
Notation "[ 'f' 'set' E | x : A , y : B & P ]" :=
  [fset[_] E | x : A, y : B & P] : fset_scope.

Notation "[ 'f' 'setval' x 'in' A ]" := [fset[_] val x | x in A] : fset_scope.
Notation "[ 'f' 'setval' x 'in' A | P ]" :=
  [fset[_] val x | x in A & P] : fset_scope.
Notation "[ 'f' 'setval' x 'in' A | P & Q ]" :=
  [fsetval[_] x in A | (P && Q)] : fset_scope.
Notation "[ 'f' 'setval' x : A ]" := [fsetval[_] x : A] : fset_scope.
Notation "[ 'f' 'setval' x : A | P ]" := [fsetval[_] x : A | P] : fset_scope.
Notation "[ 'f' 'setval' x : A | P & Q ]" :=
  [fsetval[_] x : A | (P && Q)] : fset_scope.

Section imfset.

Variables (key : unit) (K : choiceType).
Implicit Types (A B : {fset K}).

Lemma imfsetP (T : choiceType) (f : T -> K) (p : finmempred T) (k : K) :
  reflect (exists2 x : T, in_mem x p & k = f x) (k \in imfset key f p).
Proof.
rewrite unlock seq_fsetE /=; apply: (iffP mapP) => [] [x xp eqkf];
by exists x => //=; move: xp; rewrite enum_finmemE.
Qed.

Lemma in_imfset (T : choiceType) (f : T -> K) (p : finmempred T) (x : T) :
   in_mem x p -> f x \in imfset key f p.
Proof. by move=> px; apply/imfsetP; exists x. Qed.

Lemma imfset_rec (T : choiceType) (f : T -> K) (p : finmempred T)
  (P : imfset key f p -> Prop) :
  (forall (x : T) (px : in_mem x p), P [` in_imfset f px ]) -> forall k, P k.
Proof.
move=> PP v; have /imfsetP [k pk vv_eq] := valP v.
pose vP := in_imfset f pk; suff -> : P v = P [` vP] by apply: PP.
by congr P; apply/val_inj => /=; rewrite vv_eq.
Qed.

Lemma mem_imfset (T : choiceType) (f : T -> K) (p : finmempred T) :
  injective f -> forall (x : T), (f x \in imfset key f p) = (in_mem x p).
Proof. by move=> f_inj x; rewrite unlock seq_fsetE mem_map// enum_finmemE. Qed.

Lemma imfset2P (T1 : choiceType) (T2 : T1 -> choiceType)
      (f : forall x, T2 x -> K) (p1 : finmempred T1)
      (p2 : forall x, finmempred (T2 x)) k :
  reflect (exists2 x : T1, in_mem x p1
         & exists2 y : T2 x, in_mem y (p2 x) & k = f x y)
          (k \in imfset2 key f p1 p2).
Proof.
rewrite unlock !seq_fsetE; apply: (iffP allpairsPdep).
  move=> [x [y]]; rewrite !enum_finmemE => -[xp yp ->].
  by exists x => //; exists y.
by move=> [x xp [y yp ->]]; exists x, y; rewrite ?enum_finmemE.
Qed.

Lemma in_imfset2  (T1 : choiceType) (T2 : T1 -> choiceType)
      (f : forall x, T2 x -> K) (p1 : finmempred T1)
      (p2 : forall x, finmempred (T2 x)) (x : T1) (y : T2 x) :
   in_mem x p1 -> in_mem y (p2 x) -> f x y \in imfset2 key f p1 p2.
Proof. by move=> xD1 yD2; apply/imfset2P; exists x => //; exists y. Qed.

Lemma mem_imfset2 (T1 : choiceType) (T2 : T1 -> choiceType)
    (f : forall x, T2 x -> K)
    (g := fun t : {x : T1 & T2 x} => f (tag t) (tagged t))
    (p1 : finmempred T1)
    (p2 : forall x, finmempred (T2 x)) (x : T1) (y : T2 x) :
   injective g ->
   f x y \in imfset2 key f p1 p2 = (in_mem x p1) && (in_mem y (p2 x)).
Proof.
move=> f_inj; rewrite unlock seq_fsetE.
apply/allpairsPdep/idP => [[t1 [t2]]|]; last first.
  by move=> /andP[xp1 xp2]; exists x, y; rewrite ?enum_finmemE.
rewrite !enum_finmemE => -[pt1 pt2]; elim/(TaggedP T2): _ / t2 => t in pt1 pt2 *.
by elim/(TaggedP T2): _ / y => ? /f_inj->; apply/andP.
Qed.

Lemma enum_imfset (T : choiceType) (f : T -> K) (p : finmempred T) :
   {in p &, injective f} ->
   perm_eq (imfset key f p) [seq f x | x <- enum_finmem p].
Proof.
move=> f_inj; rewrite unlock -[X in perm_eq _ X]undup_id ?seq_fset_perm//.
rewrite map_inj_in_uniq ?enum_finmem_uniq // => ??.
by rewrite ?enum_finmemE; apply: f_inj.
Qed.

Lemma enum_imfset2  (T1 : choiceType) (T2 : T1 -> choiceType)
      (f : forall x, T2 x -> K) (p1 : finmempred T1)
      (p2 : forall x, finmempred (T2 x)) :
   {in  [pred t | p1 (tag t) & p2 _ (tagged t)] &,
        injective (fun t : sigT T2 => f (tag t) (tagged t))} ->
   perm_eq (imfset2 key f p1 p2)
           [seq f x y | x <- enum_finmem p1, y <- enum_finmem (p2 x)].
Proof.
move=> f_inj; rewrite unlock.
apply: uniq_perm => [||i]; rewrite ?seq_fset_uniq ?seq_fsetE //.
rewrite allpairs_uniq_dep ?enum_finmem_uniq//.
  by move=> x; rewrite enum_finmem_uniq.
move=> t0 t0' /allpairsPdep[t1 [t2]]; rewrite !enum_finmemE => -[tp1 tp2 ->/=].
move=> /allpairsPdep[t1' [t2']]; rewrite !enum_finmemE => -[t'p1 t'p2 ->/=].
by apply: (f_inj (Tagged _ _) (Tagged _ _)); rewrite ?inE/=; apply/andP.
Qed.

End imfset.

Section in_imfset.

Variable (key : unit) (K : choiceType).
Implicit Types (A B : {fset K}) (a b : K).

Lemma in_fset (p : finmempred K) (k : K) : (k \in imfset key id p) = in_mem k p.
Proof. by rewrite mem_imfset; apply: inj_id. Qed.

Lemma val_in_fset A (p : finmempred _) (k : A) :
   (val k \in imfset key val p) = (in_mem k p).
Proof. by rewrite mem_imfset ?in_finmempred //; exact: val_inj. Qed.

Lemma in_fset_val A (p : finmempred [eqType of A]) (k : K) :
  (k \in imfset key val p) = if insub k is Some a then in_mem a p else false.
Proof.
have [a _ <- /=|kNA] := insubP; first by rewrite val_in_fset.
by apply/imfsetP => [] [a _ k_def]; move: kNA; rewrite k_def [_ \in _]valP.
Qed.

Lemma in_fset_valT A (p : finmempred _) (k : K) (kA : k \in A) :
  (k \in imfset key val p) = in_mem [` kA] p.
Proof. by rewrite in_fset_val insubT /=. Qed.

Lemma in_fset_valP A (p : finmempred _) (k : K) :
  reflect {kA : k \in A & in_mem [` kA] p} (k \in imfset key val p).
Proof.
apply: (iffP (imfsetP _ _ _ _)) => [|[kA xkA]]; last by exists [`kA].
by move=> /sig2_eqW[/= x Xx ->]; exists (valP x); rewrite fsetsubE.
Qed.

Lemma in_fset_valF A (p : finmempred [eqType of A]) (k : K) : k \notin A ->
  (k \in imfset key val p) = false.
Proof. by apply: contraNF => /imfsetP[/= a Xa->]. Qed.

Lemma in_fset_nil a : a \in [fset[key] x in [::]] = false.
Proof. by rewrite !mem_imfset. Qed.

Lemma in_fset_cons x (xs : seq K) a :
  (a \in [fset[key] x in x :: xs]) = ((a == x) || (a \in [fset[key] x in xs])).
Proof. by rewrite !mem_imfset. Qed.

Lemma in_fset_cat (xs ys : seq K) a :
  (a \in [fset[key] x in xs ++ ys]) =
  ((a \in [fset[key] x in xs]) || (a \in [fset[key] x in ys])).
Proof. by rewrite !mem_imfset//= mem_cat. Qed.

Definition in_fset_ (key : unit) :=
  (in_fset_cons, in_fset_nil, in_fset_cat, in_fset).

Lemma card_in_imfset (T T' : choiceType) (f : T -> T') (p : finmempred T) :
   {in p &, injective f} -> #|` (imfset key f p)| = (size (enum_finmem p)).
Proof.
move=> f_inj; rewrite unlock /= size_seq_fset undup_id ?size_map//.
rewrite map_inj_in_uniq ?enum_finmem_uniq// => ??.
by rewrite !enum_finmemE; apply: f_inj.
Qed.

Lemma card_imfset (T T' : choiceType) (f : T -> T') (p : finmempred _) :
  injective f -> #|` (imfset key f p)| = size (enum_finmem p).
Proof. by move=> f_inj; rewrite card_in_imfset //= => x y ? ?; apply: f_inj. Qed.

Lemma leq_imfset_card (T T' : choiceType) (f : T -> T') (p : finmempred _) :
   (#|` imfset key f p| <= size (enum_finmem p))%N.
Proof. by rewrite unlock size_seq_fset (leq_trans (size_undup _)) ?size_map. Qed.

End in_imfset.

Section Theory.

Variables (key : unit) (K K': choiceType).
Implicit Types (a b x : K) (A B C D : {fset K}) (E : {fset K'})
         (pA pB pC : pred K) (s : seq K).

Lemma fsetP {A B} : A =i B <-> A = B.
Proof. by split=> [eqAB|-> //]; apply/val_inj/canonical_eq_keys => //= a. Qed.

CoInductive in_fset_spec (A : {fset K}) (x : K) : K -> bool -> Prop :=
 | InFset (u : A) & x = val u : in_fset_spec A x (val u) true
 | OutFset of x \notin A : in_fset_spec A x x false.

Lemma in_fsetP A x : in_fset_spec A x x (x \in A).
Proof.
have [xA|xNA] := boolP (x \in A); last by constructor.
by have {2}-> : x = val [` xA] by []; constructor.
Qed.

Lemma fset_eqP {A B} : reflect (A =i B) (A == B).
Proof. exact: (equivP eqP (iff_sym fsetP)). Qed.

Lemma in_fset0 x : x \in fset0 = false. Proof. by []. Qed.

Lemma in_fset1 a' a : a \in [fset a'] = (a == a').
Proof. by rewrite !in_fset_ orbF. Qed.

Lemma in_fsetU A B a : (a \in A `|` B) = (a \in A) || (a \in B).
Proof. by rewrite !in_fset_. Qed.

Lemma in_fset1U a' A a : (a \in a' |` A) = (a == a') || (a \in A).
Proof. by rewrite in_fsetU in_fset1. Qed.

Lemma in_fsetI A B a : (a \in A `&` B) = (a \in A) && (a \in B).
Proof. by rewrite in_fset. Qed.

Lemma in_fsetD A B a : (a \in A `\` B) = (a \notin B) && (a \in A).
Proof. by rewrite in_fset andbC. Qed.

Lemma in_fsetD1 A b a : (a \in A `\ b) = (a != b) && (a \in A).
Proof. by rewrite in_fsetD in_fset1. Qed.

Lemma in_fsetM A E (u : K * K') : (u \in A `*` E) = (u.1 \in A) && (u.2 \in E).
Proof. by case: u => /= x y; rewrite mem_imfset2//= => -[??] [??] [-> ->]. Qed.

Definition in_fsetE :=
  (@in_fset_ imfset_key,
   val_in_fset, in_fset0, in_fset1,
   in_fsetU, in_fsetI, in_fsetD, in_fsetM,
   in_fset1U, in_fsetD1).

Let inE := (inE, in_fsetE).

Lemma fsetIC (A B : {fset K}) : A `&` B = B `&` A.
Proof. by apply/fsetP => a; rewrite !inE andbC. Qed.

Lemma fsetUC (A B : {fset K}) : A `|` B = B `|` A.
Proof. by apply/fsetP => a; rewrite !inE orbC. Qed.

Lemma fset0I A : fset0 `&` A = fset0.
Proof. by apply/fsetP => x; rewrite !inE andFb. Qed.

Lemma fsetI0 A : A `&` fset0 = fset0.
Proof. by rewrite fsetIC fset0I. Qed.

Lemma fsetIA A B C : A `&` (B `&` C) = A `&` B `&` C.
Proof. by apply/fsetP=> x; rewrite !inE andbA. Qed.

Lemma fsetICA A B C : A `&` (B `&` C) = B `&` (A `&` C).
Proof. by rewrite !fsetIA (fsetIC A). Qed.

Lemma fsetIAC A B C : A `&` B `&` C = A `&` C `&` B.
Proof. by rewrite -!fsetIA (fsetIC B). Qed.

Lemma fsetIACA A B C D : (A `&` B) `&` (C `&` D) = (A `&` C) `&` (B `&` D).
Proof. by rewrite -!fsetIA (fsetICA B). Qed.

Lemma fsetIid A : A `&` A = A.
Proof. by apply/fsetP=> x; rewrite inE andbb. Qed.

Lemma fsetIIl A B C : A `&` B `&` C = (A `&` C) `&` (B `&` C).
Proof. by rewrite fsetIA !(fsetIAC _ C) -(fsetIA _ C) fsetIid. Qed.

Lemma fsetIIr A B C : A `&` (B `&` C) = (A `&` B) `&` (A `&` C).
Proof. by rewrite !(fsetIC A) fsetIIl. Qed.

Lemma fsetUA A B C : A `|` (B `|` C) = A `|` B `|` C.
Proof. by apply/fsetP => x; rewrite !inE orbA. Qed.

Lemma fsetUCA A B C : A `|` (B `|` C) = B `|` (A `|` C).
Proof. by rewrite !fsetUA (fsetUC B). Qed.

Lemma fsetUAC A B C : A `|` B `|` C = A `|` C `|` B.
Proof. by rewrite -!fsetUA (fsetUC B). Qed.

Lemma fsetUACA A B C D : (A `|` B) `|` (C `|` D) = (A `|` C) `|` (B `|` D).
Proof. by rewrite -!fsetUA (fsetUCA B). Qed.

Lemma fsetUid A : A `|` A = A.
Proof. by apply/fsetP=> x; rewrite inE orbb. Qed.

Lemma fsetUUl A B C : A `|` B `|` C = (A `|` C) `|` (B `|` C).
Proof. by rewrite fsetUA !(fsetUAC _ C) -(fsetUA _ C) fsetUid. Qed.

Lemma fsetUUr A B C : A `|` (B `|` C) = (A `|` B) `|` (A `|` C).
Proof. by rewrite !(fsetUC A) fsetUUl. Qed.

(* distribute /cancel *)

Lemma fsetIUr A B C : A `&` (B `|` C) = (A `&` B) `|` (A `&` C).
Proof. by apply/fsetP=> x; rewrite !inE andb_orr. Qed.

Lemma fsetIUl A B C : (A `|` B) `&` C = (A `&` C) `|` (B `&` C).
Proof. by apply/fsetP=> x; rewrite !inE andb_orl. Qed.

Lemma fsetUIr A B C : A `|` (B `&` C) = (A `|` B) `&` (A `|` C).
Proof. by apply/fsetP=> x; rewrite !inE orb_andr. Qed.

Lemma fsetUIl A B C : (A `&` B) `|` C = (A `|` C) `&` (B `|` C).
Proof. by apply/fsetP=> x; rewrite !inE orb_andl. Qed.

Lemma fsetUKC A B : (A `|` B) `&` A = A.
Proof. by apply/fsetP=> x; rewrite !inE orbK. Qed.

Lemma fsetUK A B : (B `|` A) `&` A = A.
Proof. by rewrite fsetUC fsetUKC. Qed.

Lemma fsetKUC A B : A `&` (B `|` A) = A.
Proof. by rewrite fsetIC fsetUK. Qed.

Lemma fsetKU A B : A `&` (A `|` B) = A.
Proof. by rewrite fsetIC fsetUKC. Qed.

Lemma fsetIKC A B : (A `&` B) `|` A = A.
Proof. by apply/fsetP=> x; rewrite !inE andbK. Qed.

Lemma fsetIK A B : (B `&` A) `|` A = A.
Proof. by rewrite fsetIC fsetIKC. Qed.

Lemma fsetKIC A B : A `|` (B `&` A) = A.
Proof. by rewrite fsetUC fsetIK. Qed.

Lemma fsetKI A B : A `|` (A `&` B) = A.
Proof. by rewrite fsetIC fsetKIC. Qed.

Lemma fsetUKid A B : B `|` A `|` A = B `|` A.
Proof. by rewrite -fsetUA fsetUid. Qed.

Lemma fsetUKidC A B : A `|` B `|` A = A `|` B.
Proof. by rewrite fsetUAC fsetUid. Qed.

Lemma fsetKUid A B : A `|` (A `|` B) = A `|` B.
Proof. by rewrite fsetUA fsetUid. Qed.

Lemma fsetKUidC A B : A `|` (B `|` A) = B `|` A.
Proof. by rewrite fsetUCA fsetUid. Qed.

Lemma fsetIKid A B : B `&` A `&` A = B `&` A.
Proof. by rewrite -fsetIA fsetIid. Qed.

Lemma fsetIKidC A B : A `&` B `&` A = A `&` B.
Proof. by rewrite fsetIAC fsetIid. Qed.

Lemma fsetKIid A B : A `&` (A `&` B) = A `&` B.
Proof. by rewrite fsetIA fsetIid. Qed.

Lemma fsetKIidC A B : A `&` (B `&` A) = B `&` A.
Proof. by rewrite fsetICA fsetIid. Qed.

(* subset *)

Lemma fsubsetP {A B} : reflect {subset A <= B} (A `<=` B).
Proof.
apply: (iffP fset_eqP) => AsubB a; first by rewrite -AsubB inE => /andP[].
by rewrite inE; have [/AsubB|] := boolP (a \in A).
Qed.

Lemma fset_sub_val A (p : finmempred [eqType of A]) :
  (imfset key val p) `<=` A.
Proof. by apply/fsubsetP => k /in_fset_valP []. Qed.

Lemma fset_sub A (P : pred K) : [fset x in A | P x] `<=` A.
Proof. by apply/fsubsetP => k; rewrite in_fset inE /= => /andP []. Qed.

Lemma fsetD_eq0 (A B : {fset K}) : (A `\` B == fset0) = (A `<=` B).
Proof.
apply/fset_eqP/fsubsetP => sAB a.
  by move=> aA; have := sAB a; rewrite !inE aA andbT => /negPn.
by rewrite !inE andbC; apply/negP => /andP [/sAB ->].
Qed.

Lemma fsubset_refl A : A `<=` A. Proof. exact/fsubsetP. Qed.
Hint Resolve fsubset_refl : core.

Definition fincl A B (AsubB : A `<=` B) (a : A) : B :=
  [` (fsubsetP AsubB) _ (valP a)].

Definition fsub B A : {set B} := [set x : B | val x \in A].

Lemma fsubE A B (AsubB : A `<=` B) :
  fsub B A = [set fincl AsubB x | x : A].
Proof.
apply/setP => x; rewrite in_set; apply/idP/imsetP => [|[[a aA] aA' ->]] //.
by move=> xA; exists [` xA]=> //; apply: val_inj.
Qed.

Lemma fincl_fsub A B (AsubB : A `<=` B) (a : A) :
  fincl AsubB a \in fsub B A.
Proof. by rewrite inE /= (valP a). Qed.

Lemma in_fsub B A (b : B) : (b \in fsub B A) = (val b \in A).
Proof. by rewrite inE. Qed.

Lemma subset_fsubE C A B : A `<=` C -> B `<=` C ->
   (fsub C A \subset fsub C B) = (A `<=` B).
Proof.
move=> sAC sBC; apply/subsetP/fsubsetP => sAB a; last first.
  by rewrite !inE => /sAB.
by move=> aA; have := sAB _ (fincl_fsub sAC [` aA]); rewrite inE.
Qed.

Lemma fsubset_trans : transitive (@fsubset K).
Proof. by move=>??? s t ; apply/fsubsetP => a /(fsubsetP s) /(fsubsetP t). Qed.

Lemma subset_fsub A B C : A `<=` B -> B `<=` C ->
  fsub C A \subset fsub C B.
Proof. by move=> sAB sBC; rewrite subset_fsubE // (fsubset_trans sAB). Qed.

Lemma fsetIidPl {A B} : reflect (A `&` B = A) (A `<=` B).
Proof. exact: eqP. Qed.

Lemma fsetIidPr {A B} : reflect (A `&` B = B) (B `<=` A).
Proof. by rewrite fsetIC; apply: fsetIidPl. Qed.

Lemma fsubsetIidl A B : (A `<=` A `&` B) = (A `<=` B).
Proof.
by apply/fsubsetP/fsubsetP=> sAB a aA; have := sAB _ aA; rewrite !inE ?aA.
Qed.

Lemma fsubsetIidr A B : (B `<=` A `&` B) = (B `<=` A).
Proof. by rewrite fsetIC fsubsetIidl. Qed.

Lemma fsetUidPr A B : reflect (A `|` B = B) (A `<=` B).
Proof.
apply: (iffP fsubsetP) => sAB; last by move=> a aA; rewrite -sAB inE aA.
by apply/fsetP => b; rewrite inE; have [/sAB|//] := boolP (_ \in _).
Qed.

Lemma fsetUidPl A B : reflect (A `|` B = A) (B `<=` A).
Proof. by rewrite fsetUC; apply/fsetUidPr. Qed.

Lemma fsubsetUl A B : A `<=` A `|` B.
Proof. by apply/fsubsetP => a; rewrite inE => ->. Qed.
Hint Resolve fsubsetUl : core.

Lemma fsubsetUr A B : B `<=` A `|` B.
Proof. by rewrite fsetUC. Qed.
Hint Resolve fsubsetUr : core.

Lemma fsubsetU1 x A : A `<=` x |` A.
Proof. by rewrite fsubsetUr. Qed.
Hint Resolve fsubsetU1 : core.

Lemma fsubsetU A B C : (A `<=` B) || (A `<=` C) -> A `<=` B `|` C.
Proof. by move=> /orP [] /fsubset_trans ->. Qed.

Lemma fincl_inj A B (AsubB : A `<=` B) : injective (fincl AsubB).
Proof. by move=> a b [eq_ab]; apply: val_inj. Qed.
Hint Resolve fincl_inj : core.

Lemma fsub_inj B : {in [pred A | A `<=` B] &, injective (fsub B)}.
Proof.
move=> A A'; rewrite -!topredE /= => sAB sA'B /setP eqAA'; apply/fsetP => a.
apply/idP/idP => mem_a.
  by have := eqAA' (fincl sAB [` mem_a]); rewrite !inE // => <-.
by have := eqAA' (fincl sA'B [` mem_a]); rewrite !inE // => ->.
Qed.
Hint Resolve fsub_inj : core.

Lemma eqEfsubset A B : (A == B) = (A `<=` B) && (B `<=` A).
Proof.
apply/eqP/andP => [-> //|[/fsubsetP AB /fsubsetP BA]].
by apply/fsetP=> x; apply/idP/idP=> [/AB|/BA].
Qed.

Lemma subEfproper A B : A `<=` B = (A == B) || (A `<` B).
Proof. by rewrite eqEfsubset -andb_orr orbN andbT. Qed.

Lemma fproper_sub A B : A `<` B -> A `<=` B.
Proof. by rewrite subEfproper orbC => ->. Qed.

Lemma eqVfproper A B : A `<=` B -> A = B \/ A `<` B.
Proof. by rewrite subEfproper => /predU1P. Qed.

Lemma fproperEneq A B : A `<` B = (A != B) && (A `<=` B).
Proof. by rewrite andbC eqEfsubset negb_and andb_orr andbN. Qed.

Lemma fproper_neq A B : A `<` B -> A != B.
Proof. by rewrite fproperEneq; case/andP. Qed.

Lemma fproper_irrefl A : ~~ (A `<` A).
Proof. by rewrite fproperEneq eqxx. Qed.

Lemma eqEfproper A B : (A == B) = (A `<=` B) && ~~ (A `<` B).
Proof. by rewrite negb_and negbK andb_orr andbN eqEfsubset. Qed.

Lemma card_fsub B A : A `<=` B -> #|fsub B A| = #|` A|.
Proof.
by move=> sAB; rewrite cardfE fsubE card_imset //; apply: fincl_inj.
Qed.

Lemma eqEfcard A B : (A == B) = (A `<=` B) &&
  (#|` B| <= #|` A|)%N.
Proof.
rewrite -(inj_in_eq (@fsub_inj (A `|` B))) -?topredE //=.
by rewrite eqEcard !(@subset_fsubE (A `|` B)) ?(@card_fsub (A `|` B)).
Qed.

Lemma fproperEcard A B :
  (A `<` B) = (A `<=` B) && (#|` A| < #|` B|)%N.
Proof. by rewrite fproperEneq ltnNge andbC eqEfcard; case: (A `<=` B). Qed.

Lemma fsubset_leqif_cards A B : A `<=` B -> (#|` A| <= #|` B| ?= iff (A == B))%N.
Proof.
rewrite -!(@card_fsub (A `|` B)) // -(@subset_fsubE (A `|` B)) //.
by move=> /subset_leqif_cards; rewrite (inj_in_eq (@fsub_inj _)) -?topredE /=.
Qed.

Lemma fsub0set A : fset0 `<=` A.
Proof. by apply/fsubsetP=> x; rewrite inE. Qed.
Hint Resolve fsub0set : core.

Lemma fsubset0 A : (A `<=` fset0) = (A == fset0).
Proof. by rewrite eqEfsubset fsub0set andbT. Qed.

Lemma fproper0 A : (fset0 `<` A) = (A != fset0).
Proof. by rewrite /fproper fsub0set fsubset0. Qed.

Lemma fproperE A B : (A `<` B) = (A `<=` B) && ~~ (B `<=` A).
Proof. by []. Qed.

Lemma fsubEproper A B : (A `<=` B) = (A == B) || (A `<` B).
Proof. by rewrite fproperEneq; case: eqP => //= ->; apply: fsubset_refl. Qed.

Lemma fsubset_leq_card A B : A `<=` B -> (#|` A| <= #|` B|)%N.
Proof. by move=> /fsubset_leqif_cards ->. Qed.

Lemma fproper_ltn_card A B : A `<` B -> (#|` A| < #|` B|)%N.
Proof. by rewrite fproperEcard => /andP []. Qed.

Lemma fsubset_cardP A B : #|` A| = #|` B| ->
  reflect (A =i B) (A `<=` B).
Proof.
move=> eq_cardAB; apply: (iffP idP) => [/eqVfproper [->//|]|/fsetP -> //].
by rewrite fproperEcard eq_cardAB ltnn andbF.
Qed.

Lemma fproper_sub_trans B A C : A `<` B -> B `<=` C -> A `<` C.
Proof.
rewrite !fproperEcard => /andP [sAB lt_AB] sBC.
by rewrite (fsubset_trans sAB) //= (leq_trans lt_AB) // fsubset_leq_card.
Qed.

Lemma fsub_proper_trans B A C :
  A `<=` B -> B `<` C -> A `<` C.
Proof.
rewrite !fproperEcard => sAB /andP [sBC lt_BC].
by rewrite (fsubset_trans sAB) //= (leq_ltn_trans _ lt_BC) // fsubset_leq_card.
Qed.

Lemma fsubset_neq0 A B : A `<=` B -> A != fset0 -> B != fset0.
Proof. by rewrite -!fproper0 => sAB /fproper_sub_trans->. Qed.

(* fsub is a morphism *)

Lemma fsub0 A : fsub A fset0 = set0 :> {set A}.
Proof. by apply/setP => x; rewrite !inE. Qed.

Lemma fsubT A : fsub A A = [set : A].
Proof. by apply/setP => x; rewrite !inE (valP x). Qed.

Lemma fsub1 A a (aA : a \in A) : fsub A [fset a] = [set [` aA]] :> {set A}.
Proof. by apply/setP=> x; rewrite !inE; congr eq_op. Qed.

Lemma fsubU C A B : fsub C (A `|` B) = fsub C A :|: fsub C B.
Proof. by apply/setP => x; rewrite !inE. Qed.

Lemma fsubI C A B : fsub C (A `&` B) = fsub C A :&: fsub C B.
Proof. by apply/setP => x; rewrite !inE. Qed.

Lemma fsubD C A B : fsub C (A `\` B) = fsub C A :\: fsub C B.
Proof. by apply/setP => x; rewrite !inE andbC. Qed.

Lemma fsubD1 C A b (bC : b \in C) : fsub C (A `\ b) = fsub C A :\ [` bC].
Proof. by rewrite fsubD fsub1. Qed.

Lemma fsub_eq0 A B : A `<=` B -> (fsub B A == set0) = (A == fset0).
Proof.
by move=> sAB; rewrite -fsub0 (inj_in_eq (@fsub_inj _)) -?topredE /=.
Qed.

Lemma fset_0Vmem A : (A = fset0) + {x : K | x \in A}.
Proof.
have [|[x mem_x]] := set_0Vmem (fsub A A); last first.
  by right; exists (val x); rewrite inE // in mem_x.
by move=> /eqP; rewrite fsub_eq0 // => /eqP; left.
Qed.

Lemma fset1P x a : reflect (x = a) (x \in [fset a]).
Proof. by rewrite inE; exact: eqP. Qed.

Lemma fset11 x : x \in [fset x].
Proof. by rewrite inE. Qed.

Lemma fset1_inj : injective (@fset1 K).
Proof. by move=> a b eqsab; apply/fset1P; rewrite -eqsab fset11. Qed.

Lemma fset1UP x a B : reflect (x = a \/ x \in B) (x \in a |` B).
Proof. by rewrite !inE; exact: predU1P. Qed.

Lemma fset_cons a s : [fset[key] x in a :: s] = a |` [fset[key] x in s].
Proof. by apply/fsetP=> x; rewrite in_fset_cons !inE. Qed.

Lemma fset_nil : [fset[key] x in [::] : seq K] = fset0.
Proof. by apply/fsetP=> x; rewrite in_fset_nil. Qed.

Lemma fset_cat s s' :
   [fset[key] x in s ++ s'] = [fset[key] x in s] `|` [fset[key] x in s'].
Proof. by apply/fsetP=> x; rewrite !inE !in_fset_cat. Qed.

Lemma fset1U1 x B : x \in x |` B. Proof. by rewrite !inE eqxx. Qed.

Lemma fset1Ur x a B : x \in B -> x \in a |` B.
Proof. by move=> Bx; rewrite !inE predU1r. Qed.

(* We need separate lemmas for the explicit enumerations since they *)
(* associate on the left.                                           *)
Lemma fsetU1l x A b : x \in A -> x \in A `|` [fset b].
Proof. by move=> Ax; rewrite !inE Ax. Qed.

Lemma fsetU11 x B : x \in x |` B.
Proof. by rewrite !inE eqxx. Qed.

Lemma fsetU1r A b : b \in A `|` [fset b].
Proof. by rewrite !inE eqxx orbT. Qed.

Lemma fsetD1P x A b : reflect (x != b /\ x \in A) (x \in A `\ b).
Proof. by rewrite !inE; exact: andP. Qed.

Lemma fsetD11 b A : (b \in A `\ b) = false. Proof. by rewrite !inE eqxx. Qed.

Lemma fsetD1K a A : a \in A -> a |` (A `\ a) = A.
Proof.
by move=> Aa; apply/fsetP=> x; rewrite !inE; case: eqP => // ->.
Qed.

Lemma fsetU1K a B : a \notin B -> (a |` B) `\ a = B.
Proof.
by move/negPf=> nBa; apply/fsetP=> x; rewrite !inE; case: eqP => // ->.
Qed.

Lemma fset2P x a b : reflect (x = a \/ x = b) (x \in [fset a; b]).
Proof.
by rewrite !inE; apply: (iffP orP) => [] [] /eqP ->; [left|right|left|right].
Qed.

Lemma in_fset2 x a b : (x \in [fset a; b]) = (x == a) || (x == b).
Proof. by rewrite !inE. Qed.

Lemma fset21 a b : a \in [fset a; b]. Proof. by rewrite fset1U1. Qed.

Lemma fset22 a b : b \in [fset a; b]. Proof. by rewrite in_fset2 eqxx orbT. Qed.

Lemma fsetUP x A B : reflect (x \in A \/ x \in B) (x \in A `|` B).
Proof. by rewrite !inE; exact: orP. Qed.

Lemma fsetULVR x A B : x \in A `|` B -> (x \in A) + (x \in B).
Proof. by rewrite inE; case: (x \in A); [left|right]. Qed.

Lemma fsetUS A B C : A `<=` B -> C `|` A `<=` C `|` B.
Proof.
move=> sAB; apply/fsubsetP=> x; rewrite !inE.
by case: (x \in C) => //; exact: (fsubsetP sAB).
Qed.

Lemma fsetSU A B C : A `<=` B -> A `|` C `<=` B `|` C.
Proof. by move=> sAB; rewrite -!(fsetUC C) fsetUS. Qed.

Lemma fsetUSS A B C D : A `<=` C -> B `<=` D -> A `|` B `<=` C `|` D.
Proof. by move=> /(fsetSU B) /fsubset_trans sAC /(fsetUS C)/sAC. Qed.

Lemma fset0U A : fset0 `|` A = A.
Proof. by apply/fsetP => x; rewrite !inE orFb. Qed.

Lemma fsetU0 A : A `|` fset0 = A.
Proof. by rewrite fsetUC fset0U. Qed.

(* intersection *)

Lemma fsetIP x A B : reflect (x \in A /\ x \in B) (x \in A `&` B).
Proof. by rewrite inE; apply: andP. Qed.

Lemma fsetIS A B C : A `<=` B -> C `&` A `<=` C `&` B.
Proof.
move=> sAB; apply/fsubsetP=> x; rewrite !inE.
by case: (x \in C) => //; exact: (fsubsetP sAB).
Qed.

Lemma fsetSI A B C : A `<=` B -> A `&` C `<=` B `&` C.
Proof. by move=> sAB; rewrite -!(fsetIC C) fsetIS. Qed.

Lemma fsetISS A B C D : A `<=` C -> B `<=` D -> A `&` B `<=` C `&` D.
Proof. by move=> /(fsetSI B) /fsubset_trans sAC /(fsetIS C) /sAC. Qed.

(* difference *)

Lemma fsetDP A B x : reflect (x \in A /\ x \notin B) (x \in A `\` B).
Proof. by rewrite inE andbC; apply: andP. Qed.

Lemma fsetSD C A B : A `<=` B -> A `\` C `<=` B `\` C.
Proof.
move=> sAB; apply/fsubsetP=> x; rewrite !inE.
by case: (x \in C) => //; exact: (fsubsetP sAB).
Qed.

Lemma fsetDS C A B : A `<=` B -> C `\` B `<=` C `\` A.
Proof.
move=> sAB; apply/fsubsetP=> x; rewrite !inE ![_ && (_ \in _)]andbC.
by case: (x \in C) => //; apply: contra; exact: (fsubsetP sAB).
Qed.

Lemma fsetDSS A B C D : A `<=` C -> D `<=` B -> A `\` B `<=` C `\` D.
Proof. by move=> /(fsetSD B) /fsubset_trans sAC /(fsetDS C) /sAC. Qed.

Lemma fsetD0 A : A `\` fset0 = A.
Proof. by apply/fsetP=> x; rewrite !inE. Qed.

Lemma fset0D A : fset0 `\` A = fset0.
Proof. by apply/fsetP=> x; rewrite !inE andbF. Qed.

Lemma fsetDv A : A `\` A = fset0.
Proof. by apply/fsetP=> x; rewrite !inE andNb. Qed.

Lemma fsetID B A : A `&` B `|` A `\` B = A.
Proof. by apply/fsetP=> x; rewrite !inE; do ?case: (_ \in _). Qed.

Lemma fsetDUl A B C : (A `|` B) `\` C = (A `\` C) `|` (B `\` C).
Proof. by apply/fsetP=> x; rewrite !inE; do ?case: (_ \in _). Qed.

Lemma fsetDUr A B C : A `\` (B `|` C) = (A `\` B) `&` (A `\` C).
Proof. by apply/fsetP=> x; rewrite !inE; do ?case: (_ \in _). Qed.

Lemma fsetDIl A B C : (A `&` B) `\` C = (A `\` C) `&` (B `\` C).
Proof. by apply/fsetP=> x; rewrite !inE; do ?case: (_ \in _). Qed.

Lemma fsetIDA A B C : A `&` (B `\` C) = (A `&` B) `\` C.
Proof. by apply/fsetP=> x; rewrite !inE; do ?case: (_ \in _). Qed.

Lemma fsetIDAC A B C : (A `\` B) `&` C = (A `&` C) `\` B.
Proof. by apply/fsetP=> x; rewrite !inE; do ?case: (_ \in _). Qed.

Lemma fsetDIr A B C : A `\` (B `&` C) = (A `\` B) `|` (A `\` C).
Proof. by apply/fsetP=> x; rewrite !inE; do ?case: (_ \in _). Qed.

Lemma fsetDDl A B C : (A `\` B) `\` C = A `\` (B `|` C).
Proof. by apply/fsetP=> x; rewrite !inE; do ?case: (_ \in _). Qed.

Lemma fsetDDr A B C : A `\` (B `\` C) = (A `\` B) `|` (A `&` C).
Proof. by apply/fsetP=> x; rewrite !inE; do ?case: (_ \in _). Qed.

Lemma fsetDK A B : B `<=` A -> A `\` (A `\` B) = B.
Proof. by rewrite fsetDDr => /fsetIidPr->; rewrite fsetDv fset0U. Qed.

Lemma fsetUDl (A B C : {fset K}) : A `|` (B `\` C) = (A `|` B) `\` (C `\` A).
Proof. by apply/fsetP=> x; rewrite !inE; do ?case: (_ \in _). Qed.

Lemma fsetUDr (A B C : {fset K}) : (A `\` B) `|` C = (A `|` C) `\` (B `\` C).
Proof. by apply/fsetP=> x; rewrite !inE; do ?case: (_ \in _). Qed.

(* other inclusions *)

Lemma fsubsetIl A B : A `&` B `<=` A.
Proof. by apply/fsubsetP=> x; rewrite inE => /andP []. Qed.

Lemma fsubsetIr A B : A `&` B `<=` B.
Proof. by apply/fsubsetP=> x; rewrite inE => /andP []. Qed.

Lemma fsubsetDl A B : A `\` B `<=` A.
Proof. by apply/fsubsetP=> x; rewrite inE => /andP []. Qed.

Lemma fsubD1set A x : A `\ x `<=` A.
Proof. by rewrite fsubsetDl. Qed.

Lemma fsubsetD2l C A B : A `<=` C -> B `<=` C -> (C `\` B `<=` C `\` A) = (A `<=` B).
Proof.
move=> sAC sBC; apply/idP/idP; last exact: fsetDS.
by move=> /(@fsetDS C); rewrite !fsetDK //; apply; apply: fsubsetDl.
Qed.

Hint Resolve fsubsetIl fsubsetIr fsubsetDl fsubD1set : core.

(* cardinal lemmas for fsets *)

Lemma card_finset (T : finType) (P : pred T) : #|` [fset x in P] | = #|P|.
Proof. by rewrite card_imfset //= -cardE. Qed.

Lemma card_fset (T : choiceType) (A : {fset T}) : #|` [fset x in A] | = #|` A|.
Proof. by rewrite card_imfset. Qed.

Lemma card_fseq (T : choiceType) (s : seq T) : #|` [fset x in s] | = size (undup s).
Proof. by rewrite card_imfset. Qed.

Lemma cardfs0 : #|` @fset0 K| = 0.
Proof. by rewrite -(@card_fsub fset0) // fsub0 cards0. Qed.

Lemma cardfT0 : #|{: @fset0 K}| = 0.
Proof. by rewrite -cardfE cardfs0. Qed.

Lemma cardfs_eq0 A : (#|` A| == 0) = (A == fset0).
Proof. by rewrite -(@card_fsub A) // cards_eq0 fsub_eq0. Qed.

Lemma cardfs0_eq A : #|` A| = 0 -> A = fset0.
Proof. by move=> /eqP; rewrite cardfs_eq0 => /eqP. Qed.

Lemma fset0Pn A : reflect (exists x, x \in A) (A != fset0).
Proof.
rewrite -cardfs_eq0 cardfE; apply: (equivP existsP).
by split=> [] [a aP]; [exists (val a); apply: valP|exists [` aP]].
Qed.

Lemma cardfs_gt0 A : (0 < #|` A|)%N = (A != fset0).
Proof. by rewrite lt0n cardfs_eq0. Qed.

Lemma cardfs1 x : #|` [fset x]| = 1.
Proof. by rewrite card_imfset. Qed.

Lemma cardfsUI A B : #|` A `|` B| + #|` A `&` B| = #|` A| + #|` B|.
Proof.
rewrite -!(@card_fsub (A `|` B)) ?(fsubset_trans (fsubsetIl _ _)) //.
by rewrite fsubU fsubI cardsUI.
Qed.

Lemma cardfsU A B : #|` A `|` B| = (#|` A| + #|` B| - #|` A `&` B|)%N.
Proof. by rewrite -cardfsUI addnK. Qed.

Lemma cardfsI A B : #|` A `&` B| = (#|` A| + #|` B| - #|` A `|` B|)%N.
Proof. by rewrite  -cardfsUI addKn. Qed.

Lemma cardfsID B A : #|` A `&` B| + #|` A `\` B| = #|` A|.
Proof. by rewrite -!(@card_fsub A) // fsubI fsubD cardsID. Qed.

Lemma cardfsD A B : #|` A `\` B| = (#|` A| - #|` A `&` B|)%N.
Proof. by rewrite -(cardfsID B A) addKn. Qed.

Lemma mem_fset1U a A : a \in A -> a |` A = A.
Proof.
move=> aA; apply/fsetP => x; rewrite !inE orbC.
by have [//|/=] := boolP (_ \in A); apply: contraNF => /eqP ->.
Qed.

Lemma mem_fsetD1 a A : a \notin A -> A `\ a = A.
Proof.
move=> aA; apply/fsetP => x; rewrite !inE andbC.
by have [/= xA|//] := boolP (_ \in A); apply: contraNneq aA => <-.
Qed.

Lemma fsetI1 a A : A `&` [fset a] = if a \in A then [fset a] else fset0.
Proof.
apply/fsetP => x; rewrite (fun_if (fun X => _ \in X)) !inE.
by have [[->|?] []] := (altP (x =P a), boolP (a \in A)); rewrite ?andbF.
Qed.

Lemma cardfsU1 a A : #|` a |` A| = (a \notin A) + #|` A|.
Proof.
have [aA|aNA] := boolP (a \in A); first by rewrite mem_fset1U.
rewrite cardfsU -addnBA ?fsubset_leq_card // fsetIC -cardfsD.
by rewrite mem_fsetD1 // cardfs1.
Qed.

Lemma cardfs2 a b : #|` [fset a; b]| = (a != b).+1.
Proof. by rewrite !cardfsU1 cardfs1 inE addn1. Qed.

Lemma cardfsD1 a A : #|` A| = (a \in A) + #|` A `\ a|.
Proof.
rewrite -(cardfsID [fset a]) fsetI1 (fun_if (fun A => #|` A|)).
by rewrite cardfs0 cardfs1; case: (_ \in _).
Qed.

(* other inclusions *)

Lemma fsub1set A x : ([fset x] `<=` A) = (x \in A).
Proof.
rewrite -(@subset_fsubE (x |` A)) // fsub1 ?fset1U1 // => xxA.
by rewrite sub1set inE.
Qed.

Lemma cardfs1P A : reflect (exists x, A = [fset x]) (#|` A| == 1).
Proof.
apply: (iffP idP) => [|[x ->]]; last by rewrite cardfs1.
rewrite eq_sym eqn_leq cardfs_gt0=> /andP[/fset0Pn[x Ax] leA1].
by exists x; apply/eqP; rewrite eq_sym eqEfcard fsub1set cardfs1 leA1 Ax.
Qed.

Lemma fsubset1 A x : (A `<=` [fset x]) = (A == [fset x]) || (A == fset0).
Proof.
rewrite eqEfcard cardfs1 -cardfs_eq0 orbC andbC.
by case: posnP => // A0; rewrite (cardfs0_eq A0) fsub0set.
Qed.

Arguments fsetIidPl {A B}.

Lemma cardfsDS A B : B `<=` A -> #|` A `\` B| = (#|` A| - #|` B|)%N.
Proof. by rewrite cardfsD => /fsetIidPr->. Qed.

Lemma fsubIset A B C : (B `<=` A) || (C `<=` A) -> (B `&` C `<=` A).
Proof. by case/orP; apply: fsubset_trans; rewrite (fsubsetIl, fsubsetIr). Qed.

Lemma fsubsetI A B C : (A `<=` B `&` C) = (A `<=` B) && (A `<=` C).
Proof.
rewrite !(sameP fsetIidPl eqP) fsetIA; have [-> //| ] := altP (A `&` B =P A).
by apply: contraNF => /eqP <-; rewrite -fsetIA -fsetIIl fsetIAC.
Qed.

Lemma fsubsetIP A B C : reflect (A `<=` B /\ A `<=` C) (A `<=` B `&` C).
Proof. by rewrite fsubsetI; exact: andP. Qed.

Lemma fsubUset A B C : (B `|` C `<=` A) = (B `<=` A) && (C `<=` A).
Proof.
apply/idP/idP => [subA|/andP [AB CA]]; last by rewrite -[A]fsetUid fsetUSS.
by rewrite !(fsubset_trans _ subA).
Qed.

Lemma fsubUsetP A B C : reflect (A `<=` C /\ B `<=` C) (A `|` B `<=` C).
Proof. by rewrite fsubUset; exact: andP. Qed.

Lemma fsubDset A B C : (A `\` B `<=` C) = (A `<=` B `|` C).
Proof.
apply/fsubsetP/fsubsetP=> sABC x; rewrite !inE.
  by case Bx: (x \in B) => // Ax; rewrite sABC ?in_fsetD ?Bx.
by case Bx: (x \in B) => //; move/sABC; rewrite inE Bx.
Qed.

Lemma fsetU_eq0 A B : (A `|` B == fset0) = (A == fset0) && (B == fset0).
Proof. by rewrite -!fsubset0 fsubUset. Qed.

Lemma fsubsetD1 A B x : (A `<=` B `\ x) = (A `<=` B) && (x \notin A).
Proof.
do !rewrite -(@subset_fsubE (x |` A `|` B)) ?fsubDset ?fsetUA // 1?fsetUAC //.
rewrite fsubD1 => [|mem_x]; first by rewrite -fsetUA fset1U1.
by rewrite subsetD1 // inE.
Qed.

Lemma fsubsetD1P A B x : reflect (A `<=` B /\ x \notin A) (A `<=` B `\ x).
Proof. by rewrite fsubsetD1; exact: andP. Qed.

Lemma fsubsetPn A B : reflect (exists2 x, x \in A & x \notin B) (~~ (A `<=` B)).
Proof.
 rewrite -fsetD_eq0; apply: (iffP (fset0Pn _)) => [[x]|[x xA xNB]].
  by rewrite inE => /andP[]; exists x.
by exists x; rewrite inE xA xNB.
Qed.

Lemma fproperD1 A x : x \in A -> A `\ x `<` A.
Proof.
move=> Ax; rewrite fproperE fsubsetDl; apply/fsubsetPn; exists x=> //.
by rewrite in_fsetD1 Ax eqxx.
Qed.

Lemma fproperIr A B : ~~ (B `<=` A) -> A `&` B `<` B.
Proof. by move=> nsAB; rewrite fproperE fsubsetIr fsubsetI negb_and nsAB. Qed.

Lemma fproperIl A B : ~~ (A `<=` B) -> A `&` B `<` A.
Proof. by move=> nsBA; rewrite fproperE fsubsetIl fsubsetI negb_and nsBA orbT. Qed.

Lemma fproperUr A B : ~~ (A `<=` B) ->  B `<` A `|` B.
Proof. by rewrite fproperE fsubsetUr fsubUset fsubset_refl /= andbT. Qed.

Lemma fproperUl A B : ~~ (B `<=` A) ->  A `<` A `|` B.
Proof. by move=> not_sBA; rewrite fsetUC fproperUr. Qed.

Lemma fproper1set A x : ([fset x] `<` A) -> (x \in A).
Proof. by move/fproper_sub; rewrite fsub1set. Qed.

Lemma fproperIset A B C : (B `<` A) || (C `<` A) -> (B `&` C `<` A).
Proof. by case/orP; apply: fsub_proper_trans; rewrite (fsubsetIl, fsubsetIr). Qed.

Lemma fproperI A B C : (A `<` B `&` C) -> (A `<` B) && (A `<` C).
Proof.
move=> pAI; apply/andP.
by split; apply: (fproper_sub_trans pAI); rewrite (fsubsetIl, fsubsetIr).
Qed.

Lemma fproperU A B C : (B `|` C `<` A) -> (B `<` A) && (C `<` A).
Proof.
move=> pUA; apply/andP.
by split; apply: fsub_proper_trans pUA; rewrite (fsubsetUr, fsubsetUl).
Qed.

Lemma fsetDpS C A B : B `<=` C ->  A `<` B -> C `\` B `<` C `\` A.
Proof.
move=> subBC subAB; rewrite fproperEneq fsetDS 1?fproper_sub// andbT.
apply/negP => /eqP /(congr1 (fsetD C)); rewrite !fsetDK // => [eqAB//|].
 by rewrite eqAB (negPf (fproper_irrefl _)) in subAB.
by apply: fsubset_trans subBC; apply: fproper_sub.
Qed.

Lemma fproperD2l C A B : A `<=` C -> B `<=` C -> (C `\` B `<` C `\` A) = (A `<` B).
Proof.
move=> sAC sBC; apply/idP/idP; last exact: fsetDpS.
by move=> /(@fsetDpS C); rewrite !fsetDK //; apply; apply: fsubsetDl.
Qed.

Lemma fsetI_eq0 A B : (A `&` B == fset0) = [disjoint A & B].
Proof. by []. Qed.

Lemma fdisjoint_sub {A B} : [disjoint A & B]%fset ->
  forall C : {fset K}, [disjoint fsub C A & fsub C B]%bool.
Proof.
move=> disjointAB C; apply/pred0P => a /=; rewrite !inE.
by have /eqP /fsetP /(_ (val a)) := disjointAB; rewrite !inE.
Qed.

Lemma disjoint_fsub C A B : A `|` B `<=` C ->
  [disjoint fsub C A & fsub C B]%bool = [disjoint A & B].
Proof.
move=> ABsubC.
apply/idP/idP=> [/pred0P DAB|/fdisjoint_sub->//]; apply/eqP/fsetP=> a.
rewrite !inE; have [aC|] := boolP (a \in A `|` B); last first.
  by rewrite !inE => /norP [/negPf-> /negPf->].
by have /= := DAB [` fsubsetP ABsubC _ aC]; rewrite !inE.
Qed.

Lemma fdisjointP {A B} :
  reflect (forall a, a \in A -> a \notin B) [disjoint A & B]%fset.
Proof.
apply: (iffP eqP) => [AIB_eq0 a aA|neq_ab].
  by have /fsetP /(_ a) := AIB_eq0; rewrite !inE aA /= => ->.
apply/fsetP => a; rewrite !inE.
by case: (boolP (a \in A)) => // /neq_ab /negPf ->.
Qed.

Lemma fsetDidPl A B : reflect (A `\` B = A) [disjoint A & B]%fset.
Proof.
apply: (iffP fdisjointP)=> [NB|<- a]; last by rewrite inE => /andP[].
apply/fsetP => a; rewrite !inE andbC.
by case: (boolP (a \in A)) => //= /NB ->.
Qed.

Lemma disjoint_fsetI0 A B : [disjoint A & B] -> A `&` B = fset0.
Proof. by rewrite -fsetI_eq0; move/eqP. Qed.

Lemma fsubsetD A B C :
  (A `<=` (B `\` C)) = (A `<=` B) && [disjoint A & C]%fset.
Proof.
pose D := A `|` B `|` C.
have AD : A `<=` D by rewrite /D -fsetUA fsubsetUl.
have BD : B `<=` D by rewrite /D fsetUAC fsubsetUr.
rewrite -(@subset_fsubE D) //; last first.
  by rewrite fsubDset (fsubset_trans BD) // fsubsetUr.
rewrite fsubD subsetD !subset_fsubE // disjoint_fsub //.
by rewrite /D fsetUAC fsubsetUl.
Qed.

Lemma fsubsetDP A B C :
   reflect (A `<=` B /\ [disjoint A & C]%fset) (A `<=` (B `\` C)).
Proof. by rewrite fsubsetD; apply: andP. Qed.

Lemma fdisjoint_sym A B : [disjoint A & B] = [disjoint B & A].
Proof. by rewrite -!fsetI_eq0 fsetIC. Qed.

Lemma fdisjointP_sym {A B} :
  reflect (forall a, a \in A -> a \notin B) [disjoint B & A]%fset.
Proof. by rewrite fdisjoint_sym; apply: fdisjointP. Qed.

Lemma fdisjointWl A B C :
  A `<=` B -> [disjoint B & C] -> [disjoint A & C].
Proof.
move=> AsubB; rewrite -!(@disjoint_fsub (B `|` C)) ?fsetSU //.
by apply: disjointWl; rewrite subset_fsub.
Qed.

Lemma fdisjointWr A B C :
  A `<=` B -> [disjoint C & B] -> [disjoint C & A].
Proof.
move=> BsubC; rewrite -!(@disjoint_fsub (C `|` B)) ?fsetUS //.
by apply: disjointWr; rewrite subset_fsub.
Qed.

Lemma fdisjoint0X A : [disjoint fset0 & A].
Proof. by rewrite -fsetI_eq0 fset0I. Qed.

Lemma fdisjointX0 A : [disjoint A & fset0].
Proof. by rewrite -fsetI_eq0 fsetI0. Qed.

Lemma fdisjoint1X x A : [disjoint [fset x] & A] = (x \notin A).
Proof.
rewrite -(@disjoint_fsub (x |` A)) //.
by rewrite (@eq_disjoint1 _ [` fset1U1 _ _]) ?inE =>// ?; rewrite !inE.
Qed.

Lemma fdisjointX1 x A : [disjoint A & [fset x]] = (x \notin A).
Proof. by rewrite fdisjoint_sym fdisjoint1X. Qed.

Lemma fdisjointUX A B C :
   [disjoint A `|` B & C] = [disjoint A & C]%fset && [disjoint B & C]%fset.
Proof. by rewrite -!fsetI_eq0 fsetIUl fsetU_eq0. Qed.

Lemma fdisjointXU A B C :
   [disjoint A & B `|` C] = [disjoint A & B]%fset && [disjoint A & C]%fset.
Proof. by rewrite -!fsetI_eq0 fsetIUr fsetU_eq0. Qed.

Lemma fdisjointU1X x A B :
   [disjoint x |` A & B]%fset = (x \notin B) && [disjoint A & B]%fset.
Proof. by rewrite fdisjointUX fdisjoint1X. Qed.

Lemma fsubK A B : A `<=` B -> [fsetval k in fsub B A] = A.
Proof.
move=> AsubB; apply/fsetP => k /=; symmetry.
have [kB|kNB] := (boolP (k \in B)).
   by rewrite in_fset_valT /= inE.
by rewrite in_fset_valF //; apply: contraNF kNB; apply/fsubsetP.
Qed.

Lemma FSetK A (X : {set A}) : fsub A [fsetval k in X] = X.
Proof. by apply/setP => x; rewrite !inE. Qed.

End Theory.
Hint Resolve fsubset_refl : core.
Hint Resolve fsubset_trans : core.
Hint Resolve fproper_irrefl : core.
Hint Resolve fsub0set : core.

Module Import FSetInE.
Definition inE := (inE, in_fsetE).
End FSetInE.

Section Enum.

Lemma enum_fset0 (T : choiceType) :
  enum [finType of fset0] = [::] :> seq (@fset0 T).
Proof. by rewrite enumT unlock. Qed.

Lemma enum_fset1 (T : choiceType) (x : T) :
  enum [finType of [fset x]] = [:: [`fset11 x]].
Proof.
apply/perm_small_eq=> //; apply/uniq_perm => //.
  by apply/enum_uniq.
case=> [y hy]; rewrite mem_seq1 mem_enum /in_mem /=.
by rewrite eqE /=; rewrite in_fset1 in hy.
Qed.

End Enum.

Section ImfsetTh.
Variables (key : unit) (K V : choiceType).
Implicit Types (f : K -> V) (g : V -> K) (A V : {fset K}).

Lemma imfset_id (A : {fset K}) : id @` A = A.
Proof. by apply/fsetP=> a; rewrite in_fset. Qed.

Lemma imfset_comp f g (p : finmempred _) :
  imfset key (g \o f) p = g @` (imfset key f p).
Proof.
apply/fsetP=> a; apply/imfsetP/imfsetP=> [[/= x xA ->]|].
  by exists (f x); rewrite // in_imfset.
by move=> [/= x /imfsetP [/= y yA ->] ->]; exists y.
Qed.

Lemma subset_imfset f (p q : finmempred _) : {subset p <= q} ->
  imfset key f p `<=` imfset key f q.
Proof.
move=> subPQ; apply/fsubsetP=> x /imfsetP [y /= yA ->].
by rewrite in_imfset //= [in_mem _ _]subPQ.
Qed.

Lemma eq_imfset (f f' : K -> V) (p q : finmempred _):
  f =1 f' -> (forall x, in_mem x p = in_mem x q) ->
  imfset key f p = imfset key f' q.
Proof.
move=> eq_f eqP; apply/fsetP => x; apply/imfsetP/imfsetP => /= [] [k Pk ->];
by exists k => //=; rewrite ?eq_f ?eqP in Pk *.
Qed.

End ImfsetTh.

Section PowerSetTheory.
Variable (K : choiceType).

Fact fpowerset_key : unit. Proof. exact: tt. Qed.
Definition fpowerset (A : {fset K}) : {fset {fset K}} :=
  [fset[fpowerset_key] [fsetval y in Y : {set A}] | Y in powerset [set: A]].

Lemma fpowersetE A B : (B \in fpowerset A) = (B `<=` A).
Proof.
apply/imfsetP/fsubsetP => /= [[Z _ -> y /in_fset_valP [] //]|/fsubsetP subYX].
exists (fsub _ B); last by rewrite fsubK.
by rewrite powersetE /= -fsubT subset_fsub ?fsubset_refl.
Qed.

Lemma fpowersetCE (X A B : {fset K}) :
 (A \in fpowerset (X `\` B)) = (A `<=` X) && [disjoint A & B]%fset.
Proof. by rewrite fpowersetE fsubsetD. Qed.

Lemma fpowersetS A B : (fpowerset A `<=` fpowerset B) = (A `<=` B).
Proof.
apply/fsubsetP/fsubsetP => [sub_pA_pB a|subAB X].
  by have := sub_pA_pB [fset a]; rewrite !fpowersetE !fsub1set.
by rewrite !fpowersetE => /fsubsetP XA; apply/fsubsetP => x /XA /subAB.
Qed.

Lemma fpowerset0 : fpowerset fset0 = [fset fset0].
Proof. by apply/fsetP=> X; rewrite inE fpowersetE fsubset0. Qed.

Lemma fpowerset1 (x : K) : fpowerset [fset x] = [fset fset0; [fset x]].
Proof. by apply/fsetP => X; rewrite !inE fpowersetE fsubset1 orbC. Qed.

Lemma fpowersetI A B : fpowerset (A `&` B) = fpowerset A `&` fpowerset B.
Proof. by apply/fsetP=> X; rewrite inE !fpowersetE fsubsetI. Qed.

Lemma card_fpowerset (A : {fset K}) : #|` fpowerset A| = 2 ^ #|` A|.
Proof.
rewrite !card_imfset; first by rewrite -cardE card_powerset cardsE cardfE.
by move=> X Y /fsetP eqXY; apply/setP => x; have := eqXY (val x); rewrite !inE.
Qed.

End PowerSetTheory.

Section FinTypeFset.
Variables (T : finType).

Definition pickle (s : {fset T}) :=
  [set x in s].

Definition unpickle (s : {set T}) :=
  [fset x | x in s]%fset.

Lemma pickleK : cancel pickle unpickle.
Proof. by move=> s; apply/fsetP=> x; rewrite !inE. Qed.

Lemma unpickleK : cancel unpickle pickle.
Proof. by move=> s; apply/setP=> x; rewrite !inE. Qed.

Definition fset_finMixin := CanFinMixin pickleK.
Canonical fset_finType := Eval hnf in FinType {fset T} fset_finMixin.

Lemma card_fsets : #|{:{fset T}}| = 2^#|T|.
Proof.
rewrite -(card_image (can_inj pickleK)) /=.
rewrite -cardsT -card_powerset powersetT; apply: eq_card.
move=> x; rewrite !inE; apply/mapP; exists (unpickle x).
  by rewrite mem_enum. by rewrite unpickleK.
Qed.
End FinTypeFset.

Section BigFSet.
Variable (R : Type) (idx : R) (op : Monoid.law idx).
Variable (I : choiceType).

Lemma big_seq_fsetE (X : {fset I}) (P : pred I) (F : I -> R) :
  \big[op/idx]_(i <- X | P i) F i = \big[op/idx]_(x : X | P (val x)) F (val x).
Proof. by rewrite enum_fsetE big_map enumT. Qed.

Lemma big1_fset (X : {fset I}) (P : pred I) (F : I -> R) :
  (forall i, i \in X -> P i -> F i = idx) ->
  \big[op/idx]_(i <- X | P i) F i = idx.
Proof. by move=> Fid; rewrite big_seq_fsetE big1//= => -[]. Qed.

Lemma big_fset0 (P : pred fset0) (F : @fset0 I -> R) :
  \big[op/idx]_(i : fset0 | P i) F i = idx.
Proof. by rewrite /index_enum -enumT /= enum_fset0 big_nil. Qed.

Lemma big_seq_fset0 (F : I -> R): \big[op/idx]_(i <- fset0) F i = idx.
Proof. by rewrite big_seq_fsetE big_fset0. Qed.

Lemma big_fset1 (a : I) (F : [fset a] -> R) :
  \big[op/idx]_(i : [fset a]) F i = F [` fset11 a].
Proof. by rewrite /index_enum -enumT enum_fset1 big_seq1. Qed.

Lemma big_seq_fset1 (a : I) (F : I -> R) :
  \big[op/idx]_(i <- [fset a]) F i = F a.
Proof. by rewrite big_seq_fsetE big_fset1. Qed.

End BigFSet.

Notation eq_big_imfset := (perm_big _ (enum_imfset _ _)).

Section BigComFSet.
Variable (R : Type) (idx : R) (op : Monoid.com_law idx).
Variable (I J : choiceType).

Lemma big_fset (X : finmempred _) (P : pred I) (F : I -> R) :
  \big[op/idx]_(i <- [fset i in X | P i]) F i = \big[op/idx]_(i <- enum_finmem X | P i) F i.
Proof. by rewrite !eq_big_imfset//= !big_map !big_filter_cond big_andbC. Qed.

Lemma big_fset_condE (X : {fset I}) (P : pred I) (F : I -> R) :
  \big[op/idx]_(i <- X | P i) F i = \big[op/idx]_(i <- [fset i in X | P i]) F i.
Proof. by rewrite big_fset. Qed.

Lemma eq_fbig_cond (A B : {fset I}) (P Q : pred I) (F G : I -> R) :
  [fset x in A | P x] =i [fset x in B | Q x] ->
  (forall x, x \in A -> P x -> F x = G x) ->
  \big[op/idx]_(i <- A | P i) F i = \big[op/idx]_(i <- B | Q i) G i.
Proof.
move=> /fsetP eqABPQ FG; rewrite big_fset_condE [in RHS]big_fset_condE -eqABPQ.
rewrite big_seq_cond [in RHS]big_seq_cond; apply: eq_bigr => i.
by rewrite in_fset !inE => /andP[/andP[??] _]; apply: FG.
Qed.

Lemma eq_fbig (A B : {fset I}) (F G : I -> R) :
  A =i B -> (forall x, x \in A -> F x = G x) ->
  \big[op/idx]_(i <- A) F i = \big[op/idx]_(i <- B) G i.
Proof.
by move=> AB FG; apply: eq_fbig_cond => x; rewrite ?inE/= -?AB// => /FG.
Qed.

Lemma eq_fbigl_cond (A B : {fset I}) (P Q : pred I) (F : I -> R) :
  [fset x in A | P x] =i [fset x in B | Q x] ->
  \big[op/idx]_(i <- A | P i) F i = \big[op/idx]_(i <- B | Q i) F i.
Proof. by move=> AB; apply: eq_fbig_cond. Qed.

Lemma eq_fbigl (A B : {fset I}) (F : I -> R) :
  A =i B -> \big[op/idx]_(i <- A) F i = \big[op/idx]_(i <- B) F i.
Proof. by move=> AB; apply: eq_fbig. Qed.

Lemma eq_fbigr (A : {fset I}) (P : pred I) (F G : I -> R) :
  (forall x, x \in A -> P x -> F x = G x) ->
  \big[op/idx]_(i <- A | P i) F i = \big[op/idx]_(i <- A | P i) G i.
Proof. by apply: eq_fbig_cond. Qed.

Lemma big_fsetID  (B : pred I) (A : {fset I}) (F : I -> R) :
   \big[op/idx]_(i <- A) F i =
   op (\big[op/idx]_(i <- [fset x in A | B x]) F i)
      (\big[op/idx]_(i <- [fset x in A | ~~ B x]) F i).
Proof. by rewrite !big_fset; apply: bigID. Qed.

Lemma big_fsetIDcond (B : pred I) (A : {fset I}) (P : pred I) (F : I -> R) :
   \big[op/idx]_(i <- A | P i) F i =
   op (\big[op/idx]_(i <- [fset x in A | B x] | P i) F i)
      (\big[op/idx]_(i <- [fset x in A | ~~ B x] | P i) F i).
Proof. by rewrite big_mkcond (big_fsetID B) // -!big_mkcond. Qed.

Lemma big_fsetD1 (a : I) (A : {fset I}) (F : I -> R) : a \in A ->
  \big[op/idx]_(i <- A) F i = op (F a) (\big[op/idx]_(i <- A `\ a) F i).
Proof.
move=> aA; rewrite (big_fsetID (mem [fset a])); congr (op _ _); last first.
  by apply: eq_fbigl=> i; rewrite !inE/= andbC.
rewrite (_ : [fset _ | _ in _ & _] = [fset a]) ?big_seq_fset1//=.
by apply/fsetP=> i; rewrite !inE /= andbC; case: eqP => //->.
Qed.

Lemma big_fsetU1 (a : I) (A : {fset I}) (F : I -> R) : a \notin A ->
   \big[op/idx]_(i <- (a |` A)) F i = op (F a) (\big[op/idx]_(i <- A) F i).
Proof.
move=> aNA; rewrite eq_big_imfset//= big_map undup_id ?big_cat ?big_seq_fset1//.
rewrite cat_uniq ?fset_uniq andbT//=; apply/hasPn=> /= x xA; rewrite !inE/=.
by apply: contraNneq aNA => <-.
Qed.

Lemma big_fset_incl (A : {fset I}) B F : A `<=` B ->
  (forall x, x \in B -> x \notin A -> F x = idx) ->
  \big[op/idx]_(x <- A) F x = \big[op/idx]_(x <- B) F x.
Proof.
move=> subAB Fid; rewrite [in RHS](big_fsetID (mem A)) /=.
rewrite [X in op _ X]big1_fset ?Monoid.mulm1; last first.
  by move=> i; rewrite !inE /= => /andP[iB iNA _]; apply: Fid.
by apply: eq_fbigl => i; rewrite !inE /= -(@in_fsetI _ B A) (fsetIidPr _).
Qed.

Lemma big_imfset key (h : I -> J) (A : finmempred _)
   (G : J -> R) : {in A &, injective h} ->
   \big[op/idx]_(j <- imfset key h A) G j =
   \big[op/idx]_(i <- enum_finmem A) G (h i).
Proof. by move=> h_inj; rewrite eq_big_imfset// big_map. Qed.

End BigComFSet.
Arguments big_fsetD1 {R idx op I} a [A F].


Notation eq_big_imfset2 := (perm_big _ (enum_imfset2 _ _)).

Section BigComImfset2.
Variables (R : Type) (idx : R) (op : Monoid.com_law idx)
          (I : choiceType) (J : I -> choiceType) (K : choiceType).

Lemma big_imfset2 key (A : finmempred I) (B : forall i, finmempred (J i))
      (h : forall i : I, J i -> K) (F : K -> R) :
   {in  [pred t : {i : I & J i} | A (tag t) & B _ (tagged t)] &,
        injective (fun t => h (tag t) (tagged t))} ->
   \big[op/idx]_(k <- imfset2 key h A B) F k =
   \big[op/idx]_(i <- enum_finmem A)
     \big[op/idx]_(j <- enum_finmem (B i)) F (h i j).
Proof.
move=> h_inj; rewrite eq_big_imfset2 //.
rewrite -(map_allpairs (fun t => h (tag t) (tagged t)) (fun=> Tagged _)).
by rewrite big_map big_allpairs_dep.
Qed.

End BigComImfset2.

Section BigFsetDep.
Variables (R : Type) (idx : R) (op : Monoid.com_law idx)
          (I : choiceType) (J : choiceType) (K : choiceType).

Lemma pair_big_dep_cond (A : {fset I}) (B : I -> {fset J})
      (P : pred I) (Q : I -> pred J) (F : I -> J -> R) :
   \big[op/idx]_(i <- A | P i) \big[op/idx]_(j <- B i | Q i j) F i j =
   \big[op/idx]_(p <- [fset ((i, j) : I * J) | i in [fset i in A | P i],
                             j in [fset j in B i | Q i j]]) F p.1 p.2.
Proof.
rewrite big_imfset2 //=; last by move=> [??] [??] _ _ /= [-> ->].
by rewrite big_fset /=; apply: eq_bigr => i _; rewrite big_fset.
Qed.
End BigFsetDep.

Section BigComImfset.
Variables (R : Type) (idx : R) (op : Monoid.com_law idx)
          (I : choiceType) (J : choiceType) (K : choiceType).


Lemma partition_big_imfset (h : I -> J) (A : {fset I}) (F : I -> R) :
   \big[op/idx]_(i <- A) F i =
   \big[op/idx]_(j <- [fset h x | x in A]) \big[op/idx]_(i <- A | h i == j) F i.
Proof.
transitivity (\big[op/idx]_(i <- [fset (h i, i) | i in A]) F i.2).
   by rewrite eq_big_imfset ?big_map// => i j ? ? [].
transitivity (\big[op/idx]_(i <- [fset ij | ij in
  [seq (i1, i2) | i1 <- [fset h x | x in A], i2 <- A]]) if h i.2 == i.1 then F i.2 else idx).
  rewrite -big_mkcond; apply: eq_fbigl_cond;
    move=> x; rewrite !inE/= andbT.
  apply/imfsetP/idP => [[i /= iA -> /=]|].
    rewrite eqxx andbT; apply/allpairsP; exists (h i, i) => /=.
    by rewrite in_imfset.
  by move=> /andP[/allpairsP[[/= j i] [/imfsetP[/=a aA ->] iA ->/= /eqP<-]]]; exists i.
rewrite eq_big_imfset //= big_map undup_id.
  by rewrite big_allpairs; apply: eq_bigr => i /= _; rewrite -big_mkcond.
by rewrite allpairs_uniq => //= -[j0 i0] [j1 i1] /=.
Qed.

End BigComImfset.

Notation "\bigcup_ ( i <- r | P ) F" :=
  (\big[@fsetU _/fset0]_(i <- r | P%fset) F%fset) : fset_scope.

Notation "\bigcup_ ( i <- r ) F" :=
  (\big[@fsetU _/fset0]_(i <- r) F%fset) : fset_scope.

Notation "\bigcup_ ( i | P ) F" :=
  (\big[@fsetU _/fset0]_(i | P) F%fset) : fset_scope.

Notation "\bigcup_ ( i 'in' A | P ) F" :=
  (\big[@fsetU _/fset0]_(i in A | P) F%fset) : fset_scope.

Notation "\bigcup_ ( i 'in' A ) F" :=
  (\big[@fsetU _/fset0]_(i in A) F%fset) : fset_scope.

Section FSetMonoids.

Import Monoid.
Variable (T : choiceType).

Canonical fsetU_monoid := Law (@fsetUA T) (@fset0U T) (@fsetU0 T).
Canonical fsetU_comoid := ComLaw (@fsetUC T).

End FSetMonoids.
Section BigFOpsSeq.

Variables (T : choiceType) (I : eqType) (r : seq I).
Implicit Types (P : pred I) (F :  I -> {fset T}).

Lemma bigfcup_undup P F :
   \bigcup_(i <- undup r | P i) F i = \bigcup_(i <- r | P i) F i.
Proof. by rewrite big_undup => //= A; rewrite fsetUid. Qed.

Lemma bigfcup_sup j P F : j \in r -> P j -> F j `<=` \bigcup_(i <- r | P i) F i.
Proof.
move=> jr Pj; rewrite -bigfcup_undup big_mkcond.
by rewrite (bigD1_seq j) ?mem_undup ?undup_uniq ?Pj //= fsubsetUl.
Qed.

Lemma bigfcupP x F P :
  reflect (exists2 i : I, (i \in r) && P i & x \in F i)
          (x \in \bigcup_(i <- r | P i) F i).
Proof.
apply: (iffP idP) => [|[i /andP[ri Pi]]]; last first.
  by apply: fsubsetP x; rewrite bigfcup_sup.
rewrite big_seq_cond; elim/big_rec: _ => [|i _ /andP[ri Pi] _ /fsetUP[|//]].
  by rewrite in_fset0.
by exists i; rewrite ?ri.
Qed.

Lemma bigfcupsP (U : {fset T}) P F :
  reflect (forall i : I, i \in r -> P i -> F i `<=` U)
          (\bigcup_(i <- r | P i) F i `<=` U).
Proof.
apply: (iffP idP) => [sFU i ri Pi| sFU].
  by apply: fsubset_trans sFU; apply: bigfcup_sup.
by apply/fsubsetP=> x /bigfcupP[i /andP[ri Pi]]; apply/fsubsetP/sFU.
Qed.

End BigFOpsSeq.

(* ** Induction Principles *)
Lemma finSet_rect (T : choiceType) (P : {fset T} -> Type) :
  (forall X, (forall Y, Y `<` X -> P Y) -> P X) -> forall X, P X.
Proof.
move=> ih X; move: (leqnn #|` X|); move: (X in Y in _ <= Y) => Y.
elim: #|` _| X => [|n IHn] {Y} X.
  rewrite leqn0 cardfs_eq0 => /eqP ->; apply: ih.
  by move=> Y /fproper_ltn_card.
move=> Xleq; apply: ih => Y XsubY; apply: IHn.
by rewrite -ltnS (leq_trans _ Xleq) // fproper_ltn_card.
Qed.

Lemma fset_bounded_coind (T : choiceType) (P : {fset T} -> Type) (U : {fset T}):
  (forall X, (forall Y, Y `<=` U -> X `<` Y -> P Y) -> P X) ->
   forall X, X `<=` U -> P X.
Proof.
move=> Psuper X XsubU; rewrite -[X](fsetDK XsubU)//.
have {XsubU}: (U `\` X) `<=` U by rewrite fsubsetDl.
elim: (_ `\` X) => {}X IHX XsubU.
apply: Psuper => Y /fsetDK<-; rewrite fproperD2l ?fsubsetDl //.
by move=> /IHX; apply; rewrite fsubsetDl.
Qed.

Section Fixpoints.
Variables (T : choiceType) (U : {fset T}).

Definition sub_fun (F : {fset T} -> {fset T}) (X : {set U}) : {set U} :=
  fsub U (F [fsetval x in X]).

Lemma fset_fsub X : X `<=` U -> [fsetval x in fsub U X] = X.
Proof.
move=> XU; apply/fsetP => x; apply/in_fset_valP/idP.
  by move=> [xU/=]; rewrite in_fsub.
by move=> xX; exists (fsubsetP XU x xX); rewrite /= in_fsub.
Qed.

Variable (F : {fset T} -> {fset T}).
Hypothesis (F_mono : {homo F : X Y / X `<=` Y}).
Hypothesis (F_bound : {homo F : X / X `<=` U}).

Notation Fsub := (sub_fun F).
Notation iterF := (fun i => iter i F fset0).

Lemma Fsub_mono : {homo Fsub : X Y / X \subset Y}.
Proof.
move=> X Y subXY; apply: subset_fsub; last by apply/F_bound/fset_sub_val.
by apply/F_mono/subset_imfset/subsetP.
Qed.
Hint Resolve Fsub_mono : core.

Definition fixfset := [fsetval x in fixset Fsub].

Lemma fset_iterFE i : iterF i = [fsetval x in iter i Fsub set0].
Proof.
elim: i => [|i /= -> /=]; last by rewrite fset_fsub // F_bound//= fset_sub_val.
by apply/fsetP=> x; rewrite in_fset_val /=; case: insub=> //= ?; rewrite !inE.
Qed.

Lemma fset_iterF_sub i : iterF i `<=` U.
Proof. by rewrite /= fset_iterFE fset_sub_val. Qed.

Lemma fixfsetK : F fixfset = fixfset.
Proof.
by rewrite /fixfset -[in RHS]fixsetK// fset_fsub// F_bound//= fset_sub_val.
Qed.
Hint Resolve fixfsetK : core.

Lemma fixfsetKn k : iter k F fixfset = fixfset.
Proof. by rewrite iter_fix. Qed.

Lemma iter_sub_ffix k : iterF k `<=` fixfset.
Proof.
by rewrite /fixfset !fset_iterFE; apply/subset_imfset/subsetP/iter_sub_fix.
Qed.

Definition ffix_order (x : T) :=
 if x \in U =P true is ReflectT xU then fix_order Fsub [` xU] else 0.

Lemma ffix_order_le_max (x : T) : ffix_order x <= #|` U|.
Proof.
by rewrite /ffix_order; case: eqP => //= x_in; rewrite cardfE fix_order_le_max.
Qed.

Lemma in_iter_ffix_orderE (x : T) :
  (x \in iterF (ffix_order x)) = (x \in fixfset).
Proof.
rewrite /ffix_order; case: eqP => [xU|/negP xNU]; last first.
  by rewrite !inE /fixfset in_fset_valF.
by rewrite fset_iterFE !in_fset_valT /= in_iter_fix_orderE.
Qed.

Lemma ffix_order_gt0 (x : T) : (ffix_order x > 0) = (x \in fixfset).
Proof.
rewrite /ffix_order; case: eqP => [xU|/negP xNU]; last by rewrite in_fset_valF.
by rewrite fix_order_gt0 in_fset_valT.
Qed.

Lemma ffix_order_eq0 (x : T) : (ffix_order x == 0) = (x \notin fixfset).
Proof. by rewrite -ffix_order_gt0 -ltnNge ltnS leqn0. Qed.

Lemma in_iter_ffixE (x : T) k : (x \in iterF k) = (0 < ffix_order x <= k).
Proof.
rewrite /ffix_order fset_iterFE; case: eqP => [xU|/negP xNU];
by [rewrite in_fset_valF|rewrite in_fset_valT /= in_iter_fixE].
Qed.

Lemma in_iter_ffix (x : T) k : x \in fixfset -> ffix_order x <= k ->
  x \in iterF k.
Proof. by move=> x_in xk; rewrite in_iter_ffixE ffix_order_gt0 x_in xk. Qed.

Lemma notin_iter_ffix (x : T) k : k < ffix_order x -> x \notin iterF k.
Proof. by move=> k_le; rewrite in_iter_ffixE negb_and orbC -ltnNge k_le. Qed.

Lemma ffix_order_small x k : x \in iterF k -> ffix_order x <= k.
Proof. by rewrite in_iter_ffixE => /andP[]. Qed.

Lemma ffix_order_big x k : x \in fixfset -> x \notin iterF k ->
   ffix_order x > k.
Proof. by move=> x_in; rewrite in_iter_ffixE ffix_order_gt0 x_in -ltnNge. Qed.

Lemma le_ffix_order (x y : T) : y \in iterF (ffix_order x) ->
  ffix_order y <= ffix_order x.
Proof. exact: ffix_order_small. Qed.

End Fixpoints.

(***************)
(* Finite Maps *)
(***************)

Section DefMap.
Variables (K : choiceType) (V : Type).

Record finMap : Type := FinMap {
  domf : {fset K};
  ffun_of_fmap :> {ffun domf -> V}
}.

Definition finmap_of (_ : phant (K -> V)) := finMap.

Let T_ (domf : {fset K}) :=  {ffun domf -> V}.
Local Notation finMap' := {domf : _ & T_ domf}.

End DefMap.

Notation "{fmap T }" := (@finmap_of _ _ (Phant T)) : type_scope.

Definition pred_of_finmap (K : choiceType) (V : Type)
  (f : {fmap K -> V}) : pred K := mem (domf f).
Canonical finMapPredType (K : choiceType) (V : Type) :=
  PredType (@pred_of_finmap K V).

Declare Scope fmap_scope.
Delimit Scope fmap_scope with fmap.
Local Open Scope fmap_scope.
Notation "f .[ kf ]" := (f [` kf]) : fmap_scope.
Arguments ffun_of_fmap : simpl never.

Notation "[ 'fmap' x : aT => F ]" := (FinMap [ffun x : aT => F])
  (at level 0, x ident, only parsing) : fun_scope.

Notation "[ 'fmap' : aT => F ]" := (FinMap [ffun _ : aT => F])
  (at level 0, only parsing) : fun_scope.

Notation "[ 'fmap' x => F ]" := [fmap x : _ => F]
  (at level 0, x ident, format "[ 'fmap'  x  =>  F ]") : fun_scope.

Notation "[ 'fmap' => F ]" := [fmap: _ => F]
  (at level 0, format "[ 'fmap' =>  F ]") : fun_scope.

Canonical finmap_of_finfun (K : choiceType) V (A : {fset K}) (f : {ffun A -> V}) := FinMap f.
Arguments finmap_of_finfun /.
Arguments ffun_of_fmap : simpl nomatch.

Section OpsMap.

Variables (K : choiceType).

Definition fmap0 V : {fmap K -> V} := FinMap (ffun0 (cardfT0 K)).

Definition fnd V (A : {fset K}) (f : {ffun A -> V}) (k : K) :=
  omap f (insub k).

Inductive fnd_spec V (A : {fset K}) (f : {ffun A -> V}) k :
  bool -> option A -> option V -> Type :=
| FndIn  (kf : k \in A) : fnd_spec f k true (some [` kf]) (some (f.[kf]))
| FndOut (kNf : k \notin A) : fnd_spec f k false None None.

Definition setf V (f : {fmap K -> V}) (k0 : K) (v0 : V) : {fmap K -> V} :=
  [fmap k : k0 |` domf f => if val k == k0 then v0
                            else odflt v0 (fnd f (val k))].

End OpsMap.

Prenex Implicits fnd setf.
Arguments fmap0 {K V}.
Arguments setf : simpl never.
Arguments fnd : simpl never.

Notation "[ 'fmap' 'of' T ]" := (fmap0 : {fmap T}) (only parsing) : fmap_scope.
Notation "[fmap]" := fmap0 : fmap_scope.
Notation "x .[ k <- v ]" := (setf x k v) : fmap_scope.
Notation "f .[? k ]" := (fnd f k) : fmap_scope.

Section FinMapCanonicals.
Variable K : choiceType.

Let finMap_on (V : Type) (d : {fset K}) := {ffun d -> V}.
Local Notation finMap_ V := {d : _ & finMap_on V d}.

Definition finMap_encode V (f : {fmap K -> V}) := Tagged (finMap_on V) (ffun_of_fmap f).
Definition finMap_decode V (f : finMap_ V) := FinMap (tagged f).
Lemma finMap_codeK V : cancel (@finMap_encode V) (@finMap_decode V).
Proof. by case. Qed.

Section FinMapEqType.
Variable V : eqType.

Definition finMap_eqMixin := CanEqMixin (@finMap_codeK V).
Canonical finMap_eqType := EqType {fmap K -> V} finMap_eqMixin.

End FinMapEqType.

Section FinMapChoiceType.
Variable V : choiceType.

Definition finMap_choiceMixin := CanChoiceMixin (@finMap_codeK V).
Canonical finMap_choiceType := ChoiceType {fmap K -> V} finMap_choiceMixin.

End FinMapChoiceType.

End FinMapCanonicals.

Section FinMapTheory.
Variables (K : choiceType).

Lemma fndP V (f : {fmap K -> V}) k :
  fnd_spec f k (k \in domf f) (insub k) (f.[? k]).
Proof.
rewrite /fnd; case: insubP=> [[k' k'f] _ {k} <- /=|kNf].
  by rewrite k'f; constructor.
by rewrite (negPf kNf); constructor.
Qed.

Lemma fndSome V (f : {fmap K -> V}) (k : K) :
  f.[? k] = (k \in f) :> bool.
Proof. by case: fndP. Qed.

Lemma not_fnd V (f : {fmap K -> V}) (k : K) :
  k \notin f -> f.[? k] = None.
Proof. by case: fndP. Qed.

Lemma getfE V (f : {fmap K -> V}) (k : domf f)
      (kf : val k \in domf f) : f.[kf] = f k :> V.
Proof. by congr (_ _); apply: val_inj. Qed.

Lemma eq_getf V (f : {fmap K -> V}) k (kf kf' : k \in domf f) :
  f.[kf] = f.[kf'] :> V.
Proof. by rewrite (@getfE _ _ [` kf']). Qed.

Lemma Some_fnd V (f : {fmap K -> V}) (k : domf f) :
  Some (f k) = f.[? val k].
Proof. by case: fndP (valP k) => // ? _; rewrite getfE. Qed.

Lemma in_fnd V (f : {fmap K -> V}) (k : K)
      (kf : k \in domf f) : f.[? k] = Some f.[kf].
Proof. by rewrite Some_fnd. Qed.

Lemma fnd_if V (cond : bool) (f g : {fmap K -> V}) (k : K) :
  ((if cond then f else g) : finMap _ _).[? k] =
  if cond then f.[? k] else g.[? k].
Proof. by case: cond. Qed.

Lemma getfP V (f g : {fmap K -> V}) : domf f = domf g ->
  (forall k (kMf : k \in f) (kMg : k \in g), f.[kMf] = g.[kMg]) -> f = g.
Proof.
move: f g => [kf f] [kg g] /= eq_kfg; case: _ / eq_kfg in g * => {kg}.
move=> eq_fg; congr FinMap; apply/ffunP => /= x.
by do [rewrite -!getfE; do ?exact: valP] => *.
Qed.

Lemma fmapP V (f g : {fmap K -> V}) :
      (forall k, f.[? k] = g.[? k]) <-> f = g.
Proof.
split=> [fnd_fg|-> //]; apply: getfP => [|k kMf kMg].
  by apply/fsetP => x; rewrite -!fndSome fnd_fg.
by apply: Some_inj; rewrite !Some_fnd.
Qed.

Lemma fnd_fmap0 V k : ([fmap] : {fmap K -> V}).[? k] = None.
Proof. by rewrite not_fnd // in_fset0. Qed.

Lemma mem_setf V (f : {fmap K -> V}) (k0 : K) (v0 : V) :
  f.[k0 <- v0] =i predU1 k0 (mem (domf f)).
Proof. by move=> k; rewrite !inE. Qed.

Lemma dom_setf V (f : {fmap K -> V}) (k0 : K) (v0 : V) :
  domf (f.[k0 <- v0]) = k0 |` domf f.
Proof. by apply/fsetP=> k; rewrite mem_setf. Qed.

Lemma fnd_set_in V (f : {fmap K -> V}) k0 v0 (x : domf f.[k0 <- v0]) :
  val x != k0 -> val x \in f.
Proof. by have := valP x; rewrite mem_setf inE; case: eqP. Qed.

Lemma setfK V (f : {fmap K -> V}) k0 v0 (x : domf f.[k0 <- v0]):
   f.[k0 <- v0] x = if (val x != k0) =P true isn't ReflectT xNk0 then v0
                    else f.[fnd_set_in xNk0].
Proof.
case: eqP => [p|]; rewrite ?ffunE/=; last by case: (altP eqP).
by rewrite (negPf p) in_fnd ?fnd_set_in// => xf; apply: eq_getf.
Qed.

Lemma fnd_set V (f : {fmap K -> V}) k0 v0 k :
   f.[k0 <- v0].[? k] = if k == k0 then Some v0 else f.[? k].
Proof.
case: fndP => [ksf|]; last first.
  by rewrite mem_setf inE negb_or => /andP [/negPf ->]; case: fndP.
rewrite setfK; case: eqP => [kNk0|/negPn/=]; last by rewrite negbK => ->.
by rewrite Some_fnd (negPf kNk0).
Qed.

Lemma fmap_nil V (f : {fmap K -> V}) : domf f = fset0 -> f = [fmap].
Proof.
by move=> kf0; apply: getfP => //= k ? kMg; have := kMg; rewrite !inE.
Qed.

Lemma getf_set V (f : {fmap K -> V}) (k : K) (v : V) (kf' : k \in _) :
   f.[k <- v].[kf'] = v.
Proof. by apply: Some_inj; rewrite Some_fnd fnd_set eqxx. Qed.

Lemma setf_get V (f : {fmap K -> V}) (k : domf f) :
  f.[val k <- f k] = f.
Proof. by apply/fmapP=> k'; rewrite fnd_set Some_fnd; case: eqP => [->|]. Qed.

Lemma setfNK V (f : {fmap K -> V}) (k k' : K) (v : V)
      (k'f : k' \in _) (k'f' : k' \in _):
   f.[k <- v].[k'f'] = if k' == k then v else f.[k'f].
Proof. by apply: Some_inj; rewrite Some_fnd !fnd_set in_fnd; case: ifP. Qed.

Lemma domf0 V : domf [fmap of K -> V] = fset0. Proof. by apply/fsetP => x. Qed.

End FinMapTheory.

Section ReduceOp.

Variable (K : choiceType) (V : Type).
Implicit Types (f : {fmap K -> option V}).

Lemma reducef_subproof f (x : [fsetval x : domf f | f x]) :
  f (fincl (fset_sub_val _ _) x).
Proof.
set y := (y in f y); suff : val y \in [fsetval x : domf f | f x].
  by rewrite val_in_fset.
by suff -> : val y = val x by exact: valP.
Qed.

Definition reducef f : {fmap K -> V} :=
  [fmap x => oextract (@reducef_subproof f x)].

Lemma domf_reduce f : domf (reducef f) = [fsetval x : domf f | f x].
Proof. by []. Qed.

Lemma mem_reducef f k : k \in reducef f = ojoin f.[? k].
Proof.
rewrite inE; case: fndP => [kf|] /=; first by rewrite in_fset_valT.
by apply: contraNF; apply: (fsubsetP (fset_sub_val _ _)).
Qed.

Lemma fnd_reducef f k : (reducef f).[? k] = ojoin f.[? k].
Proof.
case: fndP => /= [kf|]; last by rewrite mem_reducef; case: ojoin.
rewrite ffunE /= Some_oextract; apply: Some_inj; rewrite Some_fnd.
by rewrite Some_ojoin // ojoinT // -mem_reducef.
Qed.

Lemma get_reducef f k (krf : k \in reducef f) (kf : k \in f):
  Some (reducef f).[krf] = f.[kf].
Proof. by rewrite Some_fnd fnd_reducef in_fnd. Qed.

End ReduceOp.

Arguments reducef : simpl never.

Section RestrictionOps.
Variable (K : choiceType) (V : Type).
Implicit Types (f g : {fmap K -> V}).

Definition filterf f (P : pred K) : {fmap K -> V} :=
   [fmap x : [fset x in domf f | P x] => f (fincl (fset_sub _ _) x)].

Definition restrictf f (A : {fset K}) : {fmap K -> V} :=
  filterf f (mem A).

Notation "x .[& A ]" := (restrictf x A) : fmap_scope.
Notation "x .[\ A ]" := (x.[& domf x `\` A]) : fmap_scope.
Notation "x .[~ k ]" := (x.[\ [fset k]]) : fmap_scope.

Lemma domf_filterf f (P : pred K) :
 domf (filterf f P) = [fset k in domf f | P k].
Proof. by []. Qed.

Lemma mem_filterf f (P : pred K) (k : K) :
  (k \in domf (filterf f P)) = (k \in f) && (P k) :> bool.
Proof. by rewrite !inE. Qed.

Lemma mem_restrictf f (A : {fset K}) (k : K) :
   k \in f.[& A] = (k \in A) && (k \in f) :> bool.
Proof. by rewrite mem_filterf andbC. Qed.

Lemma mem_remf f (A : {fset K}) (k : K) :
   k \in f.[\ A] = (k \notin A) && (k \in f) :> bool.
Proof. by rewrite mem_restrictf inE -andbA andbb. Qed.

Lemma mem_remf1 f (k' k : K) :
   k \in f.[~ k'] = (k != k') && (k \in f) :> bool.
Proof. by rewrite mem_remf inE. Qed.

Lemma domf_restrict f A : domf f.[& A] = A `&` domf f.
Proof. by apply/fsetP=> k'; rewrite mem_restrictf !inE. Qed.

Lemma domf_rem f A : domf f.[\ A] = domf f `\` A.
Proof. by rewrite domf_restrict fsetIDAC fsetIid. Qed.

Lemma mem_remfF f (k : K) : k \in f.[~ k] = false.
Proof. by rewrite mem_remf1 eqxx. Qed.

Lemma fnd_filterf f P k : (filterf f P).[? k] = if P k then f.[? k] else None.
Proof.
case: fndP => [kff|]; last first.
  by rewrite in_fset => /nandP [/not_fnd->|/negPf-> //]; rewrite if_same.
by have := kff; rewrite in_fset => /andP [kf ->]; rewrite ffunE Some_fnd.
Qed.

Lemma get_filterf f P k (kff : k \in filterf f P) (kf : k \in f) :
  (filterf f P).[kff] = f.[kf].
Proof.
apply: Some_inj; rewrite !Some_fnd /= fnd_filterf.
by move: kff; rewrite !(in_fset, inE) => /andP [? ->].
Qed.

Lemma fnd_restrict f A (k : K) :
   f.[& A].[? k] = if k \in A then f.[? k] else None.
Proof. by rewrite fnd_filterf. Qed.

Lemma fnd_rem f A (k : K) : f.[\ A].[? k] = if k \in A then None else f.[? k].
Proof.
rewrite fnd_restrict inE.
by case: fndP => ?; rewrite ?(andbT, andbF) //=; case: (_ \in _).
Qed.

Lemma restrictf_comp f A B : f.[& A].[& B] = f.[& A `&` B].
Proof.
by apply/fmapP=> k; rewrite !fnd_restrict !inE; do !case: (_ \in _).
Qed.

Lemma remf_comp f A B : f.[\ A].[\ B] = f.[\ A `|` B].
Proof. by apply/fmapP=> k; rewrite !fnd_rem inE; do !case: (_ \in _). Qed.

Lemma restrictfT f : f.[& domf f] = f.
Proof. by apply/fmapP=> k; rewrite fnd_restrict; case: fndP. Qed.

Lemma restrictf0 f : f.[& fset0] = [fmap].
Proof. by apply/fmapP => k; rewrite fnd_restrict !(inE, not_fnd). Qed.

Lemma remf0 f : f.[\ fset0] = f. Proof. by rewrite fsetD0 restrictfT. Qed.

Lemma fnd_rem1 f (k k' : K) :
  f.[~ k].[? k'] = if k' != k then f.[? k'] else None.
Proof. by rewrite fnd_rem inE; case: eqP. Qed.

Lemma getf_restrict f A (k : K) (kf : k \in f) (kfA : k \in f.[& A]) :
      f.[& A].[kfA] = f.[kf].
Proof. by rewrite get_filterf. Qed.

Lemma setf_restrict f A (k : K) (v : V) :
  f.[& A].[k <- v] = f.[k <- v].[& k |` A].
Proof.
by apply/fmapP=> k'; rewrite !(fnd_set, fnd_restrict, inE); case: eqP.
Qed.

Lemma setf_rem f A (k : K) (v : V) :
  f.[\ A].[k <- v] = f.[k <- v].[\ (A `\ k)].
Proof. by rewrite setf_restrict fsetUDl. Qed.

Lemma setf_rem1 f (k : K) (v : V) : f.[~ k].[k <- v] = f.[k <- v].
Proof. by rewrite setf_rem fsetDv remf0. Qed.

Lemma setfC f k1 k2 v1 v2 : f.[k1 <- v1].[k2 <- v2] =
   if k2 == k1 then f.[k2 <- v2] else f.[k2 <- v2].[k1 <- v1].
Proof.
apply/fmapP => k. rewrite fnd_if !fnd_set.
have [[->|kNk2] [// <-|k2Nk1]] // := (altP (k =P k2), altP (k2 =P k1)).
by rewrite (negPf kNk2).
Qed.

Lemma restrictf_mkdom f A : f.[& A] = f.[& domf f `&` A].
Proof.
apply/fmapP=> k; rewrite !fnd_restrict inE.
by case: fndP => ?; rewrite ?(andbT, andbF) //=; case: (_ \in _).
Qed.

Lemma restrictf_id f A : [disjoint domf f & A] -> f.[& A] = [fmap].
Proof. by move=> dAf; rewrite restrictf_mkdom (eqP dAf) restrictf0. Qed.

Lemma remf_id f A : [disjoint domf f & A] -> f.[\ A] = f.
Proof. by move=> /fsetDidPl ->; rewrite restrictfT. Qed.

Lemma remf1_id f k : k \notin f -> f.[~ k] = f.
Proof. by move=> kNf; rewrite remf_id //= fdisjointX1. Qed.

Lemma restrictf_set f A (k : K) (v : V) :
  f.[k <- v].[& A] = if k \in A then f.[& A].[k <- v] else f.[& A].
Proof.
apply/fmapP => k' /=; rewrite !(fnd_if, fnd_set, fnd_restrict).
by case: eqP => [->|]; do !case: ifP.
Qed.

Lemma remf_set f A (k : K) (v : V) :
  f.[k <- v].[\ A] = if k \in A then f.[\ A] else f.[\ A].[k <- v].
Proof.
apply/fmapP => k' /=; rewrite !(fnd_if, fnd_rem, fnd_set, inE).
by case: eqP => [->|]; do !case: (_ \in _).
Qed.

Lemma remf1_set f (k k' : K) (v : V) :
  f.[k' <- v].[~ k] = if k == k' then f.[~ k] else f.[~ k].[k' <- v].
Proof. by rewrite remf_set inE eq_sym. Qed.

Lemma setf_inj f f' k v : k \notin f -> k \notin f' ->
                          f.[k <- v] = f'.[k <- v]-> f = f'.
Proof.
move=> kf kf' eq_fkv; apply/fmapP => k'.
have := congr1 (fun g => g.[? k']) eq_fkv.
by rewrite !fnd_set; case: eqP => // ->; rewrite !not_fnd.
Qed.

End RestrictionOps.

Arguments filterf : simpl never.
Arguments restrictf : simpl never.
Notation "x .[& A ]" := (restrictf x A) : fmap_scope.
Notation "x .[\ A ]" := (x.[& domf x `\` A]) : fmap_scope.
Notation "x .[~ k ]" := (x.[\ [fset k]]) : fmap_scope.

Section Cat.
Variables (K : choiceType) (V : Type).
Implicit Types (f g : {fmap K -> V}).

Definition catf (f g : {fmap K -> V}) :=
  [fmap k : (domf f `\` domf g) `|` domf g=>
          match fsetULVR (valP k) with
            | inl kfDg => f.[fsubsetP (fsubsetDl _ _) _ kfDg]
            | inr kg => g.[kg]
          end].

Local Notation "f + g" := (catf f g) : fset_scope.

Lemma domf_cat f g : domf (f + g) = domf f `|` domf g.
Proof.
by apply/fsetP=> x; rewrite !inE; case: (boolP (_ \in domf _)); rewrite ?orbT.
Qed.

Lemma mem_catf f g k : k \in domf (f + g) = (k \in f) || (k \in g).
Proof. by rewrite domf_cat inE. Qed.

Lemma fnd_cat f g k :
  (f + g).[? k] = if k \in domf g then g.[? k] else f.[? k].
Proof.
case: fndP => //= [kfg|]; rewrite /catf /=.
  rewrite ffunE /=; case: fsetULVR => [kf|kg]; last by rewrite Some_fnd kg.
  by rewrite -in_fnd; move: kf; rewrite inE => /andP[/negPf ->].
by rewrite mem_catf => /norP [kNf kNg]; rewrite !not_fnd // if_same.
Qed.

Lemma catfE f g : f + g = f.[\ domf g] + g.
Proof. by apply/fmapP=> k; rewrite !(fnd_cat, fnd_rem); case: ifP. Qed.

Lemma getf_catl f g k (kfg : k \in domf (f + g))
      (kf : k \in domf f) : k \notin domf g -> (f + g).[kfg] = f.[kf].
Proof.
by move=> kNg; apply: Some_inj; rewrite Some_fnd fnd_cat (negPf kNg) in_fnd.
Qed.

Lemma getf_catr f g k (kfg : k \in domf (f + g))
      (kg : k \in domf g) : (f + g).[kfg] = g.[kg].
Proof. by apply: Some_inj; rewrite Some_fnd fnd_cat kg in_fnd. Qed.

Lemma catf0 f : f + [fmap] = f.
Proof. by apply/fmapP => k; rewrite fnd_cat in_fset0. Qed.

Lemma cat0f f : [fmap] + f = f.
Proof.
apply/fmapP => k; rewrite fnd_cat; case: ifPn => //= kf.
by rewrite !not_fnd ?inE.
Qed.

Lemma catf_setl f g k (v : V) :
  f.[k <- v] + g = if k \in g then f + g else (f + g).[k <- v].
Proof.
apply/fmapP=> k'; rewrite !(fnd_if, fnd_cat, fnd_set).
by have [->|Nkk'] := altP eqP; do !case: (_ \in _).
Qed.

Lemma catf_setr f g k (v : V) : f + g.[k <- v] = (f + g).[k <- v].
Proof.
apply/fmapP=> k'; rewrite !(fnd_cat, fnd_set, mem_setf, inE).
by have [->|Nkk'] := altP eqP; do !case: (_ \in _).
Qed.

Lemma restrictf_cat f g A : (f + g).[& A] = f.[& A] + g.[& A].
Proof.
apply/fmapP => k'; rewrite !(fnd_cat, fnd_restrict) mem_restrictf.
by case: (_ \in _).
Qed.

Lemma restrictf_cat_domr f g : (f + g).[& domf g] = g.
Proof.
rewrite catfE restrictf_cat restrictf_comp.
by rewrite fsetIDAC fsetDIl fsetDv fsetI0 restrictf0 restrictfT cat0f.
Qed.

Lemma remf_cat f g A : (f + g).[\ A] = f.[\ A] + g.[\ A].
Proof.
by apply/fmapP => k'; rewrite !(fnd_cat, fnd_rem) mem_remf; case: (_ \in _).
Qed.

Lemma catf_restrictl A f g : f.[& A] + g = (f + g).[& A `|` domf g].
Proof.
apply/fmapP=> k; rewrite !(fnd_cat, fnd_restrict) !inE.
by do !case: (_ \in _).
Qed.

Lemma catf_reml A f g : f.[\ A] + g = (f + g).[\ A `\` domf g].
Proof.
by apply/fmapP=> k; rewrite !(fnd_cat, fnd_rem) inE; case: (_ \in _).
Qed.

Lemma catf_rem1l k f g :
  f.[~ k] + g = if k \in g then f + g else (f + g).[~ k].
Proof.
apply/fmapP => k'; rewrite !(fnd_if, fnd_cat, fnd_rem1).
by have [->|?] := altP eqP; do !case: (_ \in _).
Qed.

Lemma setf_catr f g k (v : V) : (f + g).[k <- v] = f + g.[k <- v].
Proof. by rewrite catf_setr. Qed.

Lemma setf_catl f g k (v : V) : (f + g).[k <- v] = f.[k <- v] + g.[~ k].
Proof. by rewrite catf_setl mem_remf1 eqxx /= !setf_catr setf_rem1. Qed.

Lemma catfA f g h : f + (g + h) = f + g + h.
Proof.
by apply/fmapP => k; rewrite !fnd_cat !mem_catf; do !case: (_ \in _).
Qed.

Lemma catfC f g : f + g = g + f.[\ domf g].
Proof.
apply/fmapP=> k; rewrite !fnd_cat fnd_rem domf_rem inE.
by have [|kNg] //= := boolP (_ \in domf g); rewrite (not_fnd kNg); case: fndP.
Qed.

Lemma disjoint_catfC f g : [disjoint domf f & domf g] -> f + g = g + f.
Proof. by move=> dfg; rewrite catfC remf_id. Qed.

Lemma catfAC f g h : f + g + h = f + h + g.[\ domf h].
Proof. by rewrite -!catfA [X in _ + X]catfC. Qed.

Lemma disjoint_catfAC f g h : [disjoint domf g & domf h]%fmap ->
     f + g + h = f + h + g.
Proof. by move=> dgh; rewrite catfAC remf_id. Qed.

Lemma catfCA f g h : f + (g + h) = g + (f.[\ domf g] + h).
Proof. by rewrite !catfA [X in X + _]catfC. Qed.

Lemma disjoint_catfCA f g h : [disjoint domf f & domf g]%fmap ->
     f + (g + h) = g + (f + h).
Proof. by move=> dfg; rewrite catfCA remf_id. Qed.

Lemma catfIs f g h : f + h = g + h -> f.[\ domf h] = g.[\ domf h].
Proof.
move=> /fmapP eq_fg_fh; apply/fmapP => k; have := eq_fg_fh k.
by rewrite !fnd_cat !fnd_rem; case: ifP.
Qed.

Lemma disjoint_catfIs h f g :
  [disjoint domf f & domf h] -> [disjoint domf g & domf h] ->
  f + h = g + h -> f = g.
Proof. by move=> dfg dgh /catfIs; rewrite !remf_id. Qed.

Lemma restrict_catfsI f g h : f + g = f + h -> g.[& domf h] = h.[& domf g].
Proof.
move=> /fmapP eq_fg_fh; apply/fmapP => k; have := eq_fg_fh k.
rewrite !fnd_cat !fnd_restrict.
by do ![case: (boolP (_ \in domf _)) => ? //=] => _; rewrite not_fnd.
Qed.

Lemma disjoint_catfsI h f g :
  [disjoint domf f & domf h] -> [disjoint domf g & domf h] ->
  h + f = h + g -> f = g.
Proof.
move=> dfg dgh; rewrite -disjoint_catfC // -[RHS]disjoint_catfC //.
by apply: disjoint_catfIs.
Qed.

End Cat.

Module Import FmapE.
Definition fmapE := (fndSome, getfE, setfK, fnd_set, getf_set,
  setfNK, fnd_reducef, get_reducef, fnd_filterf, get_filterf,
  fnd_restrict, getf_restrict, fnd_rem, fnd_rem1,
  restrictfT, restrictf0, restrictf_id, remf_id, remf1_id,
  fnd_cat).
End FmapE.

Arguments catf : simpl never.
Notation "f + g" := (catf f g) : fset_scope.

Section FinMapKeyType.
Variables (K V : choiceType).
Implicit Types (f g : {fmap K -> V}).

Definition codomf f : {fset V} := [fset f k | k : domf f].

Lemma mem_codomf f v : (v \in codomf f) = [exists x : domf f, f x == v].
Proof.
apply: sameP existsP.
by apply: (iffP (imfsetP _ _ _ _)) => /= [[x _ ->]|[x /eqP <-]]; exists x.
Qed.

Lemma codomfP f v : reflect (exists x, f.[? x] = Some v) (v \in codomf f).
Proof.
apply: (iffP (imfsetP _ _ _ _)) => /= [[x _ ->]|[k]].
  by exists (val x); rewrite Some_fnd.
by case: fndP => //= kf [<-]; exists [` kf].
Qed.

Lemma codomfPn f v : reflect (forall x, f.[? x] != Some v) (v \notin codomf f).
Proof.
rewrite mem_codomf negb_exists; apply: (iffP forallP) => f_eq_v x /=.
  by case: fndP => //= kf; rewrite f_eq_v.
by apply: contraNneq (f_eq_v (val x)) => <-; rewrite Some_fnd.
Qed.

Lemma codomf0 : codomf [fmap] = fset0.
Proof.
apply/fsetP=> k; rewrite inE; apply/negP => /codomfP [k'].
by rewrite not_fnd //= inE.
Qed.

Lemma in_codomf f (k : domf f) : f k \in codomf f.
Proof. by rewrite in_imfset. Qed.

Lemma fndSomeP f (k : K) (v : V):
  (f.[? k] = Some v) <-> {kf : k \in f & f.[kf] = v}.
Proof.
split => [fk|[kf fk]]; last by rewrite in_fnd fk.
have kf : k \in f by rewrite -fndSome fk.
by exists kf; apply: Some_inj; rewrite Some_fnd.
Qed.

Lemma codomf_restrict f (A : {fset K})  :
  codomf f.[& A] = [fset f k | k : domf f & val k \in A].
Proof.
apply/fsetP=> v; apply/imfsetP/imfsetP => /= [] [k kP ->].
  have := valP k; rewrite inE => /andP [kf kA]; exists [` kf] => //.
  by rewrite !ffunE; apply: eq_getf.
have kA : val k \in [fset x | x in domf f & x \in A] by rewrite !inE (valP k).
by exists [` kA]; rewrite // ?ffunE !getfE.
Qed.

Lemma codomf_restrict_exists f (A : {fset K})  :
  codomf f.[& A] = [fset v in codomf f
                   | [exists k : domf f, (val k \in A) && (f k == v)]].
Proof.
rewrite codomf_restrict; apply/fsetP => v; rewrite !(in_fset, inE) /=; apply/imfsetP/idP.
  by move=> [k kA ->]; rewrite in_codomf /=; apply/existsP; exists k; apply/andP.
by move=> /andP[fkdom /existsP [k /andP[kA /eqP<-]]]; exists k.
Qed.

Lemma codomf_rem f (A : {fset K})  :
  codomf f.[\ A] = [fset f k | k : domf f & val k \notin A].
Proof.
rewrite codomf_restrict.
by apply: eq_imfset => //= x /=; rewrite -!topredE /= !inE (valP x) andbT.
Qed.

Lemma codomf_rem_exists f (A : {fset K})  :
  codomf f.[\ A] = [fset v in codomf f
                   | [exists k : domf f, (val k \notin A) && (f k == v)]].
Proof.
rewrite codomf_restrict_exists; apply: eq_imfset => x //=.
  rewrite !inE; case: (_ \in _) => //=.
apply/existsP/existsP => [] /= [k]; rewrite ?inE;
by do 2?[move=>/andP []]; exists k; rewrite ?inE; do 2?[apply/andP; split].
Qed.

Lemma in_codomf_rem1 f (k : K) (kf : k \in domf f)  :
  codomf f.[~ k] =
  if [exists k' : domf f, (val k' != k) && (f k' == f.[kf])] then codomf f
  else codomf f `\ f.[kf].
Proof.
apply/fsetP => v; rewrite codomf_rem_exists (fun_if (fun x => v \in x)) !(in_fset, inE).
have [vf|vNf] := boolP (_ \in codomf f); rewrite /= ?(andbF,andbT) ?if_same //.
rewrite -/(_ || _); apply/existsP/idP => /= [[k' /andP[xk /eqP <-]]|].
  rewrite orbC -implybE; apply/implyP => eq_fk.
  by rewrite inE /= in xk; apply/existsP; exists k'; rewrite // xk eq_fk.
have /imfsetP /= [[l lf] _ ->] := vf; rewrite orbC.
have [->|neq_f _] := altP (f.[lf] =P _).
  by move=> /existsP [m /andP[Nmk /eqP <-]]; exists m; rewrite eqxx inE Nmk.
exists [` lf]; rewrite eqxx andbT inE /=.
apply: contra neq_f => /eqP eq_lk; rewrite eq_lk in lf *.
by apply/eqP; congr f.[_]; apply: bool_irrelevance.
Qed.

Lemma codomf_set f (k : K) (v : V) (kf : k \in domf f) :
  codomf f.[k <- v] = v |` codomf f.[~ k].
Proof.
rewrite -setf_rem1; apply/fsetP=> v'; rewrite !inE.
have [->|neq_v'v] /= := altP eqP.
  by apply/codomfP; exists k; rewrite fnd_set eqxx.
apply/codomfP/codomfP => [] [k' fk'_eq]; exists k';
move: fk'_eq; rewrite fnd_set.
  by have [_ [eq_vv']|//] := altP eqP; rewrite eq_vv' eqxx in neq_v'v *.
by have [->|//] := altP eqP; rewrite fnd_rem inE eqxx.
Qed.

End FinMapKeyType.

Module Import FinmapInE.
Definition inE := (inE, mem_codomf, mem_catf, mem_remfF,
                   mem_filterf, mem_reducef, mem_restrictf,
                   mem_remf, mem_remf1, mem_setf).
End FinmapInE.

Section FsfunDef.

Variables (K : choiceType) (V : eqType) (default : K -> V).

Record fsfun := Fsfun {
  fmap_of_fsfun : {fmap K -> V};
  _ : [forall k : domf fmap_of_fsfun,
       fmap_of_fsfun k != default (val k)]
}.

Canonical fsfun_subType := Eval hnf in [subType for fmap_of_fsfun].
Definition fsfun_eqMixin := [eqMixin of fsfun by <:].
Canonical  fsfun_eqType := EqType fsfun fsfun_eqMixin.

Fact fsfun_subproof (f : fsfun) :
  forall (k : K) (kf : k \in fmap_of_fsfun f),
  (fmap_of_fsfun f).[kf]%fmap != default k.
Proof.
case:f => f f_stable k kf /=.
exact: (forallP f_stable [` kf]).
Qed.

Definition fun_of_fsfun (f : fsfun) (k : K) :=
  odflt (default k) (fmap_of_fsfun f).[? k]%fmap.
End FsfunDef.

Coercion fun_of_fsfun : fsfun >-> Funclass.

Module Type FinSuppSig.
Axiom fs : forall (K : choiceType) (V : eqType) (default : K -> V),
  fsfun default -> {fset K}.
Axiom E : fs = (fun K V d f => domf (@fmap_of_fsfun K V d f)).
End FinSuppSig.
Module FinSupp : FinSuppSig.
Definition fs := (fun K V d f => domf (@fmap_of_fsfun K V d f)).
Definition E := erefl fs.
End FinSupp.
Notation finsupp := FinSupp.fs.
Canonical unlockable_finsupp := Unlockable FinSupp.E.

Section FSfunBasics.

Variables (K : choiceType) (V : eqType) (default : K -> V).
Implicit Types (f : fsfun default) (k : K) (v : V).

Lemma mem_finsupp f k : (k \in finsupp f) = (f k != default k).
Proof.
rewrite /fun_of_fsfun [finsupp]unlock; case: fndP; rewrite ?eqxx //=.
by move=> kf; rewrite fsfun_subproof.
Qed.

Lemma memNfinsupp f k : (k \notin finsupp f) = (f k == default k).
Proof. by rewrite mem_finsupp negbK. Qed.

Lemma fsfun_dflt f k : k \notin finsupp f -> f k = default k.
Proof. by rewrite mem_finsupp negbK => /eqP. Qed.

CoInductive fsfun_spec f k : V -> bool -> Type :=
  | FsfunOut : k \notin finsupp f -> fsfun_spec f k (default k) false
  | FsfunIn  (kf : k \in finsupp f) : fsfun_spec f k (f k) true.

Lemma finsuppP f k : fsfun_spec f k (f k) (k \in finsupp f).
Proof.
have [kf|kNf] := boolP (_ \in _); first by constructor.
by rewrite fsfun_dflt // ; constructor.
Qed.

Lemma fsfunP f f' : f =1 f' <-> f = f'.
Proof.
split=> [eq_fg|->//]; apply/val_inj/fmapP => k.
have := eq_fg k; rewrite /(f _) /(f' _) /=.
case: fndP; case: fndP => //= kf kf'; first by move->.
  by move/eqP/negPn; rewrite fsfun_subproof.
by move/eqP/negPn; rewrite eq_sym fsfun_subproof.
Qed.

Lemma fsfun_injective_inP  f (T : {fset K}) :
  reflect {in T &, injective f} (injectiveb [ffun x : T => f (val x)]).
Proof.
apply: (iffP (@injectiveP _ _ _)) => f_inj a b; last first.
  by rewrite !ffunE => *; apply: val_inj; apply: f_inj => //; apply: valP.
move=> aT bT eq_ga_gb; have := f_inj.[aT].[bT]; rewrite !ffunE /=.
by move=> /(_ eq_ga_gb) /(congr1 val).
Qed.

Definition fsfun_of_can_ffun (T : {fset K}) (g : {ffun T -> V})
          (can_g : forall k : T,  g k != default (val k)) :=
  @Fsfun K V default (FinMap g) (appP forallP idP can_g).

Lemma fsfun_of_can_ffunE (T : {fset K}) (g : {ffun T -> V})
          (can_g : forall k : T ,  g k != default (val k)) k (kg : k \in T) :
  (fsfun_of_can_ffun can_g) k = g.[kg].
Proof. by rewrite/fun_of_fsfun in_fnd. Qed.

End FSfunBasics.

Notation "{ 'fsfun' ty 'for' dflt }" := (fsfun (dflt : ty))
  (at level 0, format "{ 'fsfun' ty  'for'  dflt }") : type_scope.
Notation "{ 'fsfun' ty 'of' x => dflt }" := {fsfun ty for fun x => dflt}
  (at level 0, x at level 99,
   format "{ 'fsfun'  ty  'of'  x  =>  dflt }") : type_scope.
Notation "{ 'fsfun' ty 'with' dflt }" := {fsfun ty of _ => dflt}
  (at level 0, format "{ 'fsfun'  ty  'with'  dflt }") : type_scope.
Notation "{ 'fsfun' ty }" := {fsfun ty of x => x}
  (at level 0, format "{ 'fsfun'  ty }") : type_scope.

Notation "{ 'fsfun' 'for' dflt }" := {fsfun _ for dflt}
  (at level 0, only parsing) : type_scope.
Notation "{ 'fsfun' 'of' x : T => dflt }" := {fsfun T -> _ of x => dflt}
  (at level 0, x at level 99, only parsing) : type_scope.
Notation "{ 'fsfun' 'of' x => dflt }" := {fsfun of x : _ => dflt}
  (at level 0, x at level 99, only parsing) : type_scope.
Notation "{ 'fsfun' 'with' dflt }" := {fsfun of _ => dflt}
  (at level 0, only parsing) : type_scope.

Module Type FsfunSig.
Section FsfunSig.
Variables (K : choiceType) (V : eqType) (default : K -> V).

Parameter of_ffun : forall (S : {fset K}), (S -> V) -> unit -> fsfun default.
Variables (S : {fset K}) (h : S -> V).
Axiom of_ffunE :forall key x, of_ffun h key x = odflt (default x) (omap h (insub x)).

End FsfunSig.
End FsfunSig.

Module Fsfun : FsfunSig.
Section FsfunOfFinfun.

Variables (K : choiceType) (V : eqType) (default : K -> V)
          (S : {fset K}) (h : S -> V).

Let fmap :=
  [fmap a : [fsetval a in {: S} | h a != default (val a)]
   => h (fincl (fset_sub_val _ _) a)].

Fact fmapP a : fmap a != default (val a).
Proof.
rewrite ffunE; have /in_fset_valP [a_in_S] := valP a.
by have -> : [` a_in_S] = fincl (fset_sub_val _ _) a by exact/val_inj.
Qed.

Definition of_ffun (k : unit) := fsfun_of_can_ffun fmapP.

Lemma of_ffunE key x : of_ffun key x = odflt (default x) (omap h (insub x)).
Proof.
rewrite /fun_of_fsfun /=.
case: insubP => /= [u _ <-|xNS]; last first.
  case: fndP => //= kf; rewrite !ffunE /=.
  by set y := (X in h X); rewrite (valP y) in xNS.
case: fndP => /= [kf|].
  by rewrite ffunE; congr (h _); apply/val_inj => //.
by rewrite inE /= -topredE /= negbK => /eqP ->.
Qed.

End FsfunOfFinfun.
End Fsfun.
Canonical fsfun_of_funE K V default S h key x :=
   Unlockable (@Fsfun.of_ffunE K V default S h key x).

Fact fsfun_key : unit. Proof. exact: tt. Qed.

Definition fsfun_of_ffun key (K : choiceType) (V : eqType)
  (S : {fset K}) (h : S -> V) (default : K -> V) :=
  (Fsfun.of_ffun default h key).

Definition fsfun_choiceMixin (K V : choiceType) (d : K -> V) :=
  [choiceMixin of fsfun d by <:].
Canonical  fsfun_choiceType (K V : choiceType) (d : K -> V) :=
  ChoiceType (fsfun d) (fsfun_choiceMixin d).

Declare Scope fsfun_scope.
Delimit Scope fsfun_scope with fsfun.

Notation "[ 'fsfun[' key ] x : aT => F | default ]" :=
  (fsfun_of_ffun key (fun x : aT => F) (fun x => default))
  (at level 0, x at level 99, only parsing) : fun_scope.

Notation "[ 'fsfun' x : aT => F | default ]" :=
  [fsfun[fsfun_key] x : aT => F | default]
  (at level 0, x at level 99, only parsing) : fun_scope.

Notation "[ 'fsfun[' key ] x : aT => F ]" := [fsfun[key] x : aT => F | _]
  (at level 0, x at level 99, only parsing) : fun_scope.

Notation "[ 'fsfun' x : aT => F ]" := [fsfun x : aT => F | _]
  (at level 0, x at level 99, only parsing) : fun_scope.

Notation "[ 'fsfun[' key ] x => F | default ]" :=
  [fsfun[key] x : _ => F | default ]
  (at level 0, x at level 99, only parsing) : fun_scope.

Notation "[ 'fsfun' x => F | default ]" := [fsfun x : _ => F | default]
  (at level 0, x at level 99, only parsing) : fun_scope.

Notation "[ 'fsfun[' key ] x => F ]" := [fsfun[key] x => F | _]
  (at level 0, x at level 99, only parsing) : fun_scope.

Notation "[ 'fsfun' x => F ]" := [fsfun x => F | _]
  (at level 0, x at level 99, only parsing) : fun_scope.

Notation "[ 'fsfun[' key ]=> F | default ]" :=
  [fsfun[key] _ => F | default ]
  (at level 0, only parsing) : fun_scope.

Notation "[ 'fsfun=>' F | default ]" := [fsfun _ => F | default]
  (at level 0, only parsing) : fun_scope.

Notation "[ 'fsfun[' key ]=> F ]" := [fsfun[key]=> F | _]
  (at level 0, only parsing) : fun_scope.

Notation "[ 'fsfun=>' F ]" := [fsfun=> F | _]
  (at level 0, only parsing) : fun_scope.

Definition fsfun_of_fun key (K : choiceType) (V : eqType)
   (S : {fset K}) (h : K -> V) default :=
  [fsfun[key] x : S => h (val x) | default x].

Notation "[ 'fsfun[' key ] x 'in' S => F | default ]" :=
  (fsfun_of_fun key S (fun x => F) (fun x => default))
  (at level 0, x at level 99, only parsing) : fun_scope.

Notation "[ 'fsfun' x 'in' S => F | default ]" :=
  [fsfun[fsfun_key] x in S => F | default]
  (at level 0, x at level 99, only parsing) : fun_scope.

Notation "[ 'fsfun[' key ] x 'in' S => F ]" :=
  [fsfun[key] x in S => F | _]
  (at level 0, x at level 99, only parsing) : fun_scope.

Notation "[ 'fsfun' x 'in' S => F ]" :=
  [fsfun[fsfun_key] x in S => F | _]
  (at level 0, x at level 99, only parsing) : fun_scope.

Notation "[ 'fsfun[' key ] 'in' S => F | default ]" :=
  [fsfun[key] _ in S => F | default]
  (at level 0, only parsing) : fun_scope.

Notation "[ 'fsfun' 'in' S => F | default ]" :=
  [fsfun[fsfun_key] in S => F | default]
  (at level 0, only parsing) : fun_scope.

Notation "[ 'fsfun[' key ] 'in' S => F ]" :=
  [fsfun[key] in S => F | _]
  (at level 0, only parsing) : fun_scope.

Notation "[ 'fsfun' 'in' S => F ]" :=
  [fsfun[fsfun_key] in S => F | _]
  (at level 0, only parsing) : fun_scope.

(* only printing *)
Notation "[ 'fs' 'fun' x : aT => F ]" := [fsfun[_] x : aT => F]
  (at level 0, x at level 99,
  format "[ 'fs' 'fun'  x  :  aT  =>  F ]") : fun_scope.

Notation "[ 'fs' 'fun' x 'in' aT => F ]" := [fsfun[_] x in aT => F]
  (at level 0, x at level 99,
  format "[ 'fs' 'fun'  x  'in'  aT  =>  F ]") : fun_scope.

Fact fsfun0_key : unit. Proof. exact: tt. Qed.
Notation "[ 'fsfun' 'for' default ]" := (fsfun_of_ffun fsfun0_key [fmap] default)
  (at level 0, only parsing) : fun_scope.

Notation "[ 'fsfun' 'of' x => default ]" := [fsfun for fun x => default]
  (at level 0,  x at level 99, only parsing) : fun_scope.

Notation "[ 'fsfun' 'with' default ]" := [fsfun of _ => default]
  (at level 0, only parsing) : fun_scope.

Notation "[ 'fsfun' ]" := [fsfun for _]
 (at level 0, format "[ 'fsfun' ]") : fun_scope.

Section FsfunTheory.
Variables (key : unit) (K : choiceType) (V : eqType) (default : K -> V).

Lemma fsfun_ffun (S : {fset K}) (h : S -> V) (x : K) :
  [fsfun[key] a : S => h a | default a] x =
  odflt (default x) (omap h (insub x)).
Proof. by rewrite unlock. Qed.

Lemma fsfun_fun (S : {fset K}) (h : K -> V) (x : K) :
  [fsfun[key] a in S => h a | default a] x =
   if x \in S then h x else (default x).
Proof. by rewrite fsfun_ffun; case: insubP => //= [u -> ->|/negPf ->]. Qed.

Lemma fsfun0E : [fsfun for default] =1 default.
Proof. by move=> x; rewrite unlock insubF ?inE. Qed.

Definition fsfunE := (fsfun_fun, fsfun0E).

Lemma finsupp_sub  (S : {fset K}) (h : S -> V) :
  finsupp [fsfun[key] a : S => h a | default a] `<=` S.
Proof.
apply/fsubsetP => a; rewrite mem_finsupp unlock /=.
by case: insubP => //=; rewrite eqxx.
Qed.

Lemma finsupp0 : finsupp [fsfun for default] = fset0.
Proof. by apply/fsetP => x; rewrite !inE mem_finsupp fsfunE eqxx. Qed.

Lemma fsfun0_inj : injective default -> injective [fsfun for default].
Proof. by move=> def_inj x y; rewrite !fsfunE => /def_inj. Qed.

Lemma in_finsupp0 x : x \in finsupp [fsfun for default] = false.
Proof. by rewrite finsupp0 inE. Qed.

End FsfunTheory.

Section FsWith.
Variables (K : choiceType) (V : eqType) (default : K -> V).
Implicit Types (f : {fsfun K -> V for default}) (x z : K) (y : V).

Definition fun_delta_key (d : fun_delta K V) := let: FunDelta x y := d in x.

Definition app_fsdelta (d : fun_delta K V) f : {fsfun K -> V for default} :=
  [fsfun z in fun_delta_key d |` finsupp f => [eta f with d] z].

Definition app_fswithout x f : {fsfun K -> V for default} :=
  app_fsdelta (x |-> default x)%FUN_DELTA f.

End FsWith.

Arguments app_fsdelta {K V default}.
Arguments app_fswithout {K V default}.

Notation "[ 'fsfun' f 'with' d1 , .. , dn ]" :=
  (app_fsdelta d1%FUN_DELTA .. (app_fsdelta dn%FUN_DELTA f) ..)
  (at level 0, f at level 99, format
  "'[hv' [ '[' 'fsfun' '/ '  f ']' '/'  'with'  '[' d1 , '/'  .. , '/'  dn ']' ] ']'") : fun_scope.

Notation "[ 'fsfun' f 'without' x1 , .. , xn ]" :=
  (app_fswithout x1 .. (app_fswithout xn f) ..)
  (at level 0, f at level 99, format
  "'[hv' [ '[' 'fsfun' '/ '  f ']' '/'  'without'  '[' x1 , '/'  .. , '/'  xn ']' ] ']'") : fun_scope.

Section FsWithTheory.
Variables (K : choiceType) (V : eqType) (default : K -> V).
Implicit Types (f : {fsfun K -> V for default}) (x z : K) (y : V).

Lemma fsfun_withE f x y z :
  [fsfun f with x |-> y] z = if z == x then y else f z.
Proof. by rewrite fsfunE !inE/= mem_finsupp; case: eqP; case: eqP. Qed.

Lemma fsfun_with f x y : [fsfun f with x |-> y] x = y.
Proof. by rewrite fsfun_withE eqxx. Qed.

Lemma fsfun_with_id f x : [fsfun f with x |-> f x] = f.
Proof. by apply/fsfunP=> z; rewrite fsfun_withE; case: eqP => [->|]. Qed.

Lemma finsupp_with f x y : finsupp [fsfun f with x |-> y] =
  if y == default x then finsupp f `\ x else x |` finsupp f.
Proof.
apply/fsetP=> z; rewrite mem_finsupp fsfun_withE (fun_if (fun p => z \in p)).
rewrite (fun_if (fun t => t != _)) -mem_finsupp !inE.
by case: (altP (z =P x)) => [->|_]; case: (altP (y =P _)).
Qed.

Lemma finsupp_without f x z : finsupp [fsfun f without x] = finsupp f `\ x.
Proof. by rewrite finsupp_with eqxx. Qed.

End FsWithTheory.

Module Import FsfunInE2.
Definition inE := (inE, in_finsupp0).
End FsfunInE2.

Section FsfunIdTheory.

Variables (K : choiceType).
Implicit Types (f g : {fsfun K -> K}).

Fact fsfun_comp_key : unit. Proof. exact: tt. Qed.
Definition fsfun_comp g f : {fsfun _} :=
  [fsfun[fsfun_comp_key] k in finsupp f `|` finsupp g => g (f k)].

Notation "g \o f" := (fsfun_comp g f) : fsfun_scope.

Lemma fscompE g f : (g \o f)%fsfun =1 g \o f.
Proof.
move=> k; rewrite fsfun_ffun; case: insubP => //= [u _ <- //|].
by rewrite inE => /norP [kNf kNg]; rewrite !fsfun_dflt.
Qed.

Lemma fscomp0f : left_id [fsfun] fsfun_comp.
Proof. by move=> f; apply/fsfunP=> k; rewrite fscompE /= fsfun0E. Qed.

Lemma fscompA : associative fsfun_comp.
Proof. by move=> f g h; apply/fsfunP => k; rewrite !fscompE /= !fscompE. Qed.

Lemma fscomp_inj g f : injective f -> injective g -> injective (g \o f)%fsfun.
Proof. by move=> f_inj g_inj k k'; rewrite !fscompE => /= /g_inj /f_inj. Qed.

Definition fsinjectiveb : pred {fsfun K -> K} :=
  [pred f | (injectiveb [ffun a : finsupp f => f (val a)])
            && [forall a : finsupp f, f (val a) \in finsupp f]].

Lemma fsinjP {f} : [<->
  (*0*) injective f;
  (*1*) let S := finsupp f in {in S &, injective f}
        /\ forall a : S, f (val a) \in S;
  (*2*) exists2 S : {fset K}, (finsupp f `<=` S) & {in S &, injective f}
        /\ forall a : S, f (val a) \in S].
Proof.
do ?[apply: AllIffConj] => [f_inj|[f_inj f_st]|[S fS [f_inj f_st]] a b].
- split=> [a b ? ?|a]; first exact: f_inj.
  rewrite mem_finsupp (inj_eq f_inj) -mem_finsupp; apply/valP.
- by exists (finsupp f)=> //; apply: fsubset_refl.
have Nfinsupp := contra (fsubsetP fS _).
wlog /andP [aS bNS] : a b / (a \in S) && (b \notin S) => [hwlog|]; last first.
  rewrite (fsfun_dflt (Nfinsupp _ bNS)) => fb_eq_a.
  by move: bNS; rewrite -fb_eq_a (f_st.[aS]).
have [[aS|aNS] [bS|bNS]] := (boolP (a \in S), boolP (b \in S)); first 3 last.
- by rewrite !fsfun_dflt // ?Nfinsupp.
- exact: f_inj.
- by apply: hwlog; rewrite aS.
by move=> fab; symmetry; apply: hwlog; rewrite // bS.
Qed.

Lemma fsinjectiveP f : reflect (injective f) (fsinjectiveb f).
Proof.
apply: equivP (fsinjP 1 0) => /=;
by apply: (iffP andP)=> -[/fsfun_injective_inP ? /forallP ?].
Qed.

Lemma fsinjectivebP f :
  reflect (exists2 S : {fset K}, (finsupp f `<=` S)
           & {in S &, injective f} /\ forall a : S, f (val a) \in S)
        (fsinjectiveb f).
Proof. by apply/(iffP (fsinjectiveP _)) => /(fsinjP 0 2). Qed.

End FsfunIdTheory.

Arguments fsinjP {K f}.
Arguments fsinjectiveP {K f}.
Arguments fsinjectivebP {K f}.

Definition inE := inE.

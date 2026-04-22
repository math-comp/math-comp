(* (c) Copyright 2006-2019 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype bigop finset preorder porder.

(******************************************************************************)
(*                     Semilattice and lattice structures                     *)
(*                                                                            *)
(* NB: See CONTRIBUTING.md for an introduction to HB concepts and commands.   *)
(*                                                                            *)
(* NB: See the header of all_order.v for general remarks about the preorder   *)
(*     and order structures in MathComp, and the files in this directory.     *)
(*                                                                            *)
(* * Interfaces                                                               *)
(* We provide the following interfaces for types equipped with an order:      *)
(*                                                                            *)
(*     meetSemilatticeType d == the type of meet semilattices                 *)
(*                              The HB class is called MeetSemilattice.       *)
(*    bMeetSemilatticeType d == meetSemilatticeType with a bottom element     *)
(*                              The HB class is called BMeetSemilattice.      *)
(*    tMeetSemilatticeType d == meetSemilatticeType with a top element        *)
(*                              The HB class is called TMeetSemilattice.      *)
(*   tbMeetSemilatticeType d == meetSemilatticeType with both a top and a     *)
(*                              bottom                                        *)
(*                              The HB class is called TBMeetSemilattice.     *)
(*     joinSemilatticeType d == the type of join semilattices                 *)
(*                              The HB class is called JoinSemilattice.       *)
(*    bJoinSemilatticeType d == joinSemilatticeType with a bottom element     *)
(*                              The HB class is called BJoinSemilattice.      *)
(*    tJoinSemilatticeType d == joinSemilatticeType with a top element        *)
(*                              The HB class is called TJoinSemilattice.      *)
(*   tbJoinSemilatticeType d == joinSemilatticeType with both a top and a     *)
(*                              bottom                                        *)
(*                              The HB class is called TBJoinSemilattice.     *)
(*             latticeType d == the type of lattices                          *)
(*                              The HB class is called Lattice.               *)
(*            bLatticeType d == latticeType with a bottom element             *)
(*                              The HB class is called BLattice.              *)
(*            tLatticeType d == latticeType with a top element                *)
(*                              The HB class is called TLattice.              *)
(*           tbLatticeType d == latticeType with both a top and a bottom      *)
(*                              The HB class is called TBLattice.             *)
(*        distrLatticeType d == the type of distributive lattices             *)
(*                              The HB class is called DistrLattice.          *)
(*       bDistrLatticeType d == distrLatticeType with a bottom element        *)
(*                              The HB class is called BDistrLattice.         *)
(*       tDistrLatticeType d == distrLatticeType with a top element           *)
(*                              The HB class is called TDistrLattice.         *)
(*      tbDistrLatticeType d == distrLatticeType with both a top and a bottom *)
(*                              The HB class is called TBDistrLattice.        *)
(*  finMeetSemilatticeType d == the type of finite meet semilattice types     *)
(*                              The HB class is called FinMeetSemilattice.    *)
(* finBMeetSemilatticeType d == finMeetSemilatticeType with a bottom element  *)
(*                              Note that finTMeetSemilatticeType is just     *)
(*                              finTBLatticeType.                             *)
(*                              The HB class is called FinBMeetSemilattice.   *)
(*  finJoinSemilatticeType d == the type of finite join semilattice types     *)
(*                              The HB class is called FinJoinSemilattice.    *)
(* finTJoinSemilatticeType d == finJoinSemilatticeType with a top element     *)
(*                              Note that finBJoinSemilatticeType is just     *)
(*                              finTBLatticeType.                             *)
(*                              The HB class is called FinTJoinSemilattice.   *)
(*          finLatticeType d == the type of finite lattices                   *)
(*                              The HB class is called FinLattice.            *)
(*        finTBLatticeType d == the type of nonempty finite lattices          *)
(*                              The HB class is called FinTBLattice.          *)
(*     finDistrLatticeType d == the type of finite distributive lattices      *)
(*                              The HB class is called FinDistrLattice.       *)
(*   finTBDistrLatticeType d == the type of nonempty finite distributive      *)
(*                              lattices                                      *)
(*                              The HB class is called FinTBDistrLattice.     *)
(*                                                                            *)
(* and their joins with subType:                                              *)
(*                                                                            *)
(*     meetSubLattice d T P d' == join of latticeType d' and subType          *)
(*                                (P : pred T) such that val is monotonic and *)
(*                                a morphism for meet                         *)
(*                                The HB class is called MeetSubLattice.      *)
(*     joinSubLattice d T P d' == join of latticeType d' and subType          *)
(*                                (P : pred T) such that val is monotonic and *)
(*                                a morphism for join                         *)
(*                                The HB class is called JoinSubLattice.      *)
(*         subLattice d T P d' == join of JoinSubLattice and MeetSubLattice   *)
(*                                The HB class is called SubLattice.          *)
(*    bJoinSubLattice d T P d' == join of JoinSubLattice and BLattice         *)
(*                                such that val is a morphism for \bot        *)
(*                                The HB class is called BJoinSubLattice.     *)
(*    tMeetSubLattice d T P d' == join of MeetSubLattice and TLattice         *)
(*                                such that val is a morphism for \top        *)
(*                                The HB class is called TMeetSubLattice.     *)
(*        bSubLattice d T P d' == join of SubLattice and BLattice             *)
(*                                such that val is a morphism for \bot        *)
(*                                The HB class is called BSubLattice.         *)
(*        tSubLattice d T P d' == join of SubLattice and TLattice             *)
(*                                such that val is a morphism for \top        *)
(*                                The HB class is called BSubLattice.         *)
(*   subPOrderLattice d T P d' == join of SubPOrder and Lattice               *)
(*                                The HB class is called SubPOrderLattice.    *)
(*  subPOrderBLattice d T P d' == join of SubPOrder and BLattice              *)
(*                                The HB class is called SubPOrderBLattice.   *)
(*  subPOrderTLattice d T P d' == join of SubPOrder and TLattice              *)
(*                                The HB class is called SubPOrderTLattice.   *)
(* subPOrderTBLattice d T P d' == join of SubPOrder and TBLattice             *)
(*                                The HB class is called SubPOrderTBLattice.  *)
(*    meetSubBLattice d T P d' == join of MeetSubLattice and BLattice         *)
(*                                The HB class is called MeetSubBLattice.     *)
(*    meetSubTLattice d T P d' == join of MeetSubLattice and TLattice         *)
(*                                The HB class is called MeetSubTLattice.     *)
(*   meetSubTBLattice d T P d' == join of MeetSubLattice and TBLattice        *)
(*                                The HB class is called MeetSubTBLattice.    *)
(*    joinSubBLattice d T P d' == join of JoinSubLattice and BLattice         *)
(*                                The HB class is called JoinSubBLattice.     *)
(*    joinSubTLattice d T P d' == join of JoinSubLattice and TLattice         *)
(*                                The HB class is called JoinSubTLattice.     *)
(*   joinSubTBLattice d T P d' == join of JoinSubLattice and TBLattice        *)
(*                                The HB class is called JoinSubTBLattice.    *)
(*        subBLattice d T P d' == join of SubLattice and BLattice             *)
(*                                The HB class is called SubBLattice.         *)
(*        subTLattice d T P d' == join of SubLattice and TLattice             *)
(*                                The HB class is called SubTLattice.         *)
(*       subTBLattice d T P d' == join of SubLattice and TBLattice            *)
(*                                The HB class is called SubTBLattice.        *)
(*   bJoinSubTLattice d T P d' == join of BJoinSubLattice and TBLattice       *)
(*                                The HB class is called BJoinSubTLattice.    *)
(*   tMeetSubBLattice d T P d' == join of TMeetSubLattice and TBLattice       *)
(*                                The HB class is called TMeetSubBLattice.    *)
(*       bSubTLattice d T P d' == join of BSubLattice and TBLattice           *)
(*                                The HB class is called BSubTLattice.        *)
(*       tSubBLattice d T P d' == join of TSubLattice and TBLattice           *)
(*                                The HB class is called TSubBLattice.        *)
(*      tbSubBLattice d T P d' == join of BSubLattice and TSubLattice         *)
(*                                The HB class is called TBSubLattice.        *)
(*                                                                            *)
(* Morphisms between the above structures:                                    *)
(*                                                                            *)
(* MeetLatticeMorphism.type d T d' T',                                        *)
(* JoinLatticeMorphism.type d T d' T',                                        *)
(* LatticeMorphism.type d T d' T' == nondecreasing function between two       *)
(*                           lattices which are morphism for meet, join, and  *)
(*                           meet/join respectively                           *)
(* BLatticeMorphism.type d T d' T' := {blmorphism T -> T'},                   *)
(* TLatticeMorphism.type d T d' T' := {tlmorphism T -> T'},                   *)
(* TBLatticeMorphism.type d T d' T' := {tblmorphism T -> T'}                  *)
(*                        == nondecreasing function between two lattices with *)
(*                           bottom/top which are morphism for bottom/top     *)
(*                                                                            *)
(* Closedness predicates for the algebraic structures:                        *)
(*                                                                            *)
(*  meetLatticeClosed d T == predicate closed under meet on T : latticeType d *)
(*                           The HB class is MeetLatticeClosed.               *)
(*  joinLatticeClosed d T == predicate closed under join on T : latticeType d *)
(*                           The HB class is JoinLatticeClosed.               *)
(*      latticeClosed d T == predicate closed under meet and join             *)
(*                           The HB class is JoinLatticeClosed.               *)
(*     bLatticeClosed d T == predicate that contains bottom                   *)
(*                           The HB class is BLatticeClosed.                  *)
(*     tLatticeClosed d T == predicate that contains top                      *)
(*                           The HB class is TLatticeClosed.                  *)
(*    tbLatticeClosed d T == predicate that contains top and bottom           *)
(*                           the HB class ie TBLatticeClosed.                 *)
(* bJoinLatticeClosed d T == predicate that contains bottom and is closed     *)
(*                           under join                                       *)
(*                           The HB class is BJoinLatticeClosed.              *)
(* tMeetLatticeClosed d T == predicate that contains top and is closed under  *)
(*                           meet                                             *)
(*                           The HB class is TMeetLatticeClosed.              *)
(*                                                                            *)
(* * Order relations and operations:                                          *)
(* In general, an overloaded relation or operation on ordered types takes the *)
(* following arguments:                                                       *)
(* 1. a display d of type Order.disp_t,                                       *)
(* 2. an instance T of the minimal structure it operates on, and              *)
(* 3. operands.                                                               *)
(* Here is the exhaustive list of all such operations together with their     *)
(* default notation (defined in order_scope unless specified otherwise).      *)
(*                                                                            *)
(* For T of type meetSemilatticeType d, and x, y of type T:                   *)
(*         x `&` y :=  @Order.meet d T x y                                    *)
(*                 ==  the meet of x and y                                    *)
(* For T of type joinSemilatticeType d, and x, y of type T:                   *)
(*         x `|` y :=  @Order.join d T x y                                    *)
(*                 ==  the join of x and y                                    *)
(*                                                                            *)
(* For T of type tMeetSemilatticeType d:                                      *)
(* \meet_<range> e :=  \big[Order.meet / Order.top]_<range> e                 *)
(*                 ==  iterated meet of a meet-semilattice with a top         *)
(*                     the possible <range>s are documented in bigop.v        *)
(* For T of type bJoinSemilatticeType d:                                      *)
(* \join_<range> e :=  \big[Order.join / Order.bottom]_<range> e              *)
(*                 ==  iterated join of a join-semilattice with a bottom      *)
(*                     the possible <range>s are documented in bigop.v        *)
(*                                                                            *)
(* The following notations are provided to build substructures:               *)
(* [SubPOrder_isSubLattice of U by <: with disp] ==                           *)
(* [SubPOrder_isSubLattice of U by <:] ==                                     *)
(* [SubChoice_isSubLattice of U by <: with disp] ==                           *)
(* [SubChoice_isSubLattice of U by <:] == latticeType mixin for a subType     *)
(*                          whose base type is a latticeType and whose        *)
(*                          predicate is a latticeClosed                      *)
(* [SubPOrder_isBSubLattice of U by <: with disp] ==                          *)
(* [SubPOrder_isBSubLattice of U by <:] ==                                    *)
(* [SubChoice_isBSubLattice of U by <: with disp] ==                          *)
(* [SubChoice_isBSubLattice of U by <:] == blatticeType mixin for a subType   *)
(*                          whose base type is a blatticeType and whose       *)
(*                          predicate is both a latticeClosed                 *)
(*                          and a bLatticeClosed                              *)
(* [SubPOrder_isTSubLattice of U by <: with disp] ==                          *)
(* [SubPOrder_isTSubLattice of U by <:] ==                                    *)
(* [SubChoice_isTSubLattice of U by <: with disp] ==                          *)
(* [SubChoice_isTSubLattice of U by <:] == tlatticeType mixin for a subType   *)
(*                          whose base type is a tlatticeType and whose       *)
(*                          predicate is both a latticeClosed                 *)
(*                          and a tLatticeClosed                              *)
(* [SubPOrder_isTBSubLattice of U by <: with disp] ==                         *)
(* [SubPOrder_isTBSubLattice of U by <:] ==                                   *)
(* [SubChoice_isTBSubLattice of U by <: with disp] ==                         *)
(* [SubChoice_isTBSubLattice of U by <:] == tblatticeType mixin for a subType *)
(*                          whose base type is a tblatticeType and whose      *)
(*                          predicate is both a latticeClosed                 *)
(*                          and a tbLatticeClosed                             *)
(*                                                                            *)
(* Acknowledgments: The files in this directory are based on prior work by    *)
(* D. Dreyer, G. Gonthier, A. Nanevski, P-Y Strub, B. Ziliani                 *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope order_scope.

(* Reserved notations for lattice operations *)
Reserved Notation "A `&` B"  (at level 48, left associativity).
Reserved Notation "A `|` B" (at level 52, left associativity).
Reserved Notation "A `\` B" (at level 50, left associativity).
Reserved Notation "~` A" (at level 35, right associativity).

(* Reserved notations for dual order *)
Reserved Notation "A `&^d` B"  (at level 48, left associativity).
Reserved Notation "A `|^d` B" (at level 52, left associativity).
Reserved Notation "A `\^d` B" (at level 50, left associativity).
Reserved Notation "~^d` A" (at level 35, right associativity).

(* Reserved notations for iterative meet and join *)
Reserved Notation "\meet_ i F"
  (at level 34, F at level 41, i at level 0,
           format "'[' \meet_ i '/  '  F ']'").
Reserved Notation "\meet_ ( i <- r | P ) F"
  (at level 34, F at level 41, i, r at level 60,
           format "'[' \meet_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\meet_ ( i <- r ) F"
  (F at level 41,
           format "'[' \meet_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\meet_ ( m <= i < n | P ) F"
  (F at level 41, i, n at level 60,
           format "'[' \meet_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\meet_ ( m <= i < n ) F"
  (F at level 41,
           format "'[' \meet_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\meet_ ( i | P ) F"
  (F at level 41,
           format "'[' \meet_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\meet_ ( i : t | P ) F" (F at level 41).
Reserved Notation "\meet_ ( i : t ) F" (F at level 41).
Reserved Notation "\meet_ ( i < n | P ) F"
  (F at level 41, n at level 60,
           format "'[' \meet_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\meet_ ( i < n ) F"
  (F at level 41,
           format "'[' \meet_ ( i  <  n )  F ']'").
Reserved Notation "\meet_ ( i 'in' A | P ) F"
  (F at level 41, A at level 60,
           format "'[' \meet_ ( i  'in'  A  |  P ) '/  '  F ']'").
Reserved Notation "\meet_ ( i 'in' A ) F"
  (F at level 41,
           format "'[' \meet_ ( i  'in'  A ) '/  '  F ']'").

Reserved Notation "\join_ i F"
  (at level 34, F at level 41, i at level 0,
           format "'[' \join_ i '/  '  F ']'").
Reserved Notation "\join_ ( i <- r | P ) F"
  (at level 34, F at level 41, i, r at level 60,
           format "'[' \join_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\join_ ( i <- r ) F"
  (F at level 41,
           format "'[' \join_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\join_ ( m <= i < n | P ) F"
  (F at level 41, i, n at level 60,
           format "'[' \join_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\join_ ( m <= i < n ) F"
  (F at level 41,
           format "'[' \join_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\join_ ( i | P ) F"
  (F at level 41,
           format "'[' \join_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\join_ ( i : t | P ) F" (F at level 41).
Reserved Notation "\join_ ( i : t ) F" (F at level 41).
Reserved Notation "\join_ ( i < n | P ) F"
  (F at level 41, n at level 60,
           format "'[' \join_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\join_ ( i < n ) F"
  (F at level 41,
           format "'[' \join_ ( i  <  n )  F ']'").
Reserved Notation "\join_ ( i 'in' A | P ) F"
  (F at level 41, A at level 60,
           format "'[' \join_ ( i  'in'  A  |  P ) '/  '  F ']'").
Reserved Notation "\join_ ( i 'in' A ) F"
  (F at level 41,
           format "'[' \join_ ( i  'in'  A ) '/  '  F ']'").

Reserved Notation "\meet^d_ i F"
  (at level 34, F at level 41, i at level 0,
           format "'[' \meet^d_ i '/  '  F ']'").
Reserved Notation "\meet^d_ ( i <- r | P ) F"
  (at level 34, F at level 41, i, r at level 60,
           format "'[' \meet^d_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\meet^d_ ( i <- r ) F"
  (F at level 41,
           format "'[' \meet^d_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\meet^d_ ( m <= i < n | P ) F"
  (F at level 41, i, n at level 60,
           format "'[' \meet^d_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\meet^d_ ( m <= i < n ) F"
  (F at level 41,
           format "'[' \meet^d_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\meet^d_ ( i | P ) F"
  (F at level 41,
           format "'[' \meet^d_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\meet^d_ ( i : t | P ) F" (F at level 41).
Reserved Notation "\meet^d_ ( i : t ) F" (F at level 41).
Reserved Notation "\meet^d_ ( i < n | P ) F"
  (F at level 41, n at level 60,
           format "'[' \meet^d_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\meet^d_ ( i < n ) F"
  (F at level 41,
           format "'[' \meet^d_ ( i  <  n )  F ']'").
Reserved Notation "\meet^d_ ( i 'in' A | P ) F"
  (F at level 41, A at level 60,
           format "'[' \meet^d_ ( i  'in'  A  |  P ) '/  '  F ']'").
Reserved Notation "\meet^d_ ( i 'in' A ) F"
  (F at level 41,
           format "'[' \meet^d_ ( i  'in'  A ) '/  '  F ']'").

Reserved Notation "\join^d_ i F"
  (at level 34, F at level 41, i at level 0,
           format "'[' \join^d_ i '/  '  F ']'").
Reserved Notation "\join^d_ ( i <- r | P ) F"
  (at level 34, F at level 41, i, r at level 60,
           format "'[' \join^d_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\join^d_ ( i <- r ) F"
  (F at level 41,
           format "'[' \join^d_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\join^d_ ( m <= i < n | P ) F"
  (F at level 41, i, n at level 60,
           format "'[' \join^d_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\join^d_ ( m <= i < n ) F"
  (F at level 41,
           format "'[' \join^d_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\join^d_ ( i | P ) F"
  (F at level 41,
           format "'[' \join^d_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\join^d_ ( i : t | P ) F" (F at level 41).
Reserved Notation "\join^d_ ( i : t ) F" (F at level 41).
Reserved Notation "\join^d_ ( i < n | P ) F"
  (F at level 41, n at level 60,
           format "'[' \join^d_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\join^d_ ( i < n ) F"
  (F at level 41,
           format "'[' \join^d_ ( i  <  n )  F ']'").
Reserved Notation "\join^d_ ( i 'in' A | P ) F"
  (F at level 41, A at level 60,
           format "'[' \join^d_ ( i  'in'  A  |  P ) '/  '  F ']'").
Reserved Notation "\join^d_ ( i 'in' A ) F"
  (F at level 41,
           format "'[' \join^d_ ( i  'in'  A ) '/  '  F ']'").

Reserved Notation "'{' 'mlmorphism' U '->' V '}'"
  (U at level 98, V at level 99, format "{ 'mlmorphism'  U  ->  V }").
Reserved Notation "'{' 'jlmorphism' U '->' V '}'"
  (U at level 98, V at level 99, format "{ 'jlmorphism'  U  ->  V }").
Reserved Notation "'{' 'lmorphism' U '->' V '}'"
  (U at level 98, V at level 99, format "{ 'lmorphism'  U  ->  V }").
Reserved Notation "'{' 'blmorphism' U '->' V '}'"
  (U at level 98, V at level 99, format "{ 'blmorphism'  U  ->  V }").
Reserved Notation "'{' 'tlmorphism' U '->' V '}'"
  (U at level 98, V at level 99, format "{ 'tlmorphism'  U  ->  V }").
Reserved Notation "'{' 'tblmorphism' U '->' V '}'"
  (U at level 98, V at level 99, format "{ 'tblmorphism'  U  ->  V }").

Module Order.

Export Order.
Import Order.Theory.

#[key="T", primitive]
HB.mixin Record POrder_isMeetSemilattice d (T : Type) & POrder d T := {
  meet : T -> T -> T;
  lexI : forall x y z, (x <= meet y z) = (x <= y) && (x <= z);
}.

#[key="T", primitive]
HB.mixin Record POrder_isJoinSemilattice d T & POrder d T := {
  join : T -> T -> T;
  leUx : forall x y z, (join x y <= z) = (x <= z) && (y <= z);
}.

#[short(type="meetSemilatticeType")]
HB.structure Definition MeetSemilattice d :=
  { T of POrder d T & POrder_isMeetSemilattice d T }.

#[short(type="bMeetSemilatticeType")]
HB.structure Definition BMeetSemilattice d :=
  { T of MeetSemilattice d T & hasBottom d T }.

#[short(type="tMeetSemilatticeType")]
HB.structure Definition TMeetSemilattice d :=
  { T of MeetSemilattice d T & hasTop d T }.

#[short(type="tbMeetSemilatticeType")]
HB.structure Definition TBMeetSemilattice d :=
  { T of BMeetSemilattice d T & hasTop d T }.

#[short(type="joinSemilatticeType")]
HB.structure Definition JoinSemilattice d :=
  { T of POrder d T & POrder_isJoinSemilattice d T }.

#[short(type="bJoinSemilatticeType")]
HB.structure Definition BJoinSemilattice d :=
  { T of JoinSemilattice d T & hasBottom d T }.

#[short(type="tJoinSemilatticeType")]
HB.structure Definition TJoinSemilattice d :=
  { T of JoinSemilattice d T & hasTop d T }.

#[short(type="tbJoinSemilatticeType")]
HB.structure Definition TBJoinSemilattice d :=
  { T of BJoinSemilattice d T & hasTop d T }.

#[short(type="latticeType")]
HB.structure Definition Lattice d :=
  { T of JoinSemilattice d T & POrder_isMeetSemilattice d T }.

#[short(type="bLatticeType")]
HB.structure Definition BLattice d := { T of Lattice d T & hasBottom d T }.

#[short(type="tLatticeType")]
HB.structure Definition TLattice d := { T of Lattice d T & hasTop d T }.

#[short(type="tbLatticeType")]
HB.structure Definition TBLattice d := { T of BLattice d T & hasTop d T }.

#[key="T", primitive]
HB.mixin Record Lattice_isDistributive d (T : Type) & Lattice d T := {
  meetUl : @left_distributive T T meet join;
  joinIl : @left_distributive T T join meet; (* dual of meetUl *)
}.

#[short(type="distrLatticeType")]
HB.structure Definition DistrLattice d :=
  { T of Lattice_isDistributive d T & Lattice d T }.

#[short(type="bDistrLatticeType")]
HB.structure Definition BDistrLattice d :=
  { T of DistrLattice d T & hasBottom d T }.

#[short(type="tDistrLatticeType")]
HB.structure Definition TDistrLattice d :=
  { T of DistrLattice d T & hasTop d T }.

#[short(type="tbDistrLatticeType")]
HB.structure Definition TBDistrLattice d :=
  { T of BDistrLattice d T  & hasTop d T }.

Section LatticeDef.
Context {disp : disp_t} {T : latticeType disp}.

Variant lel_xor_gt (x y : T) :
  T -> T -> T -> T -> T -> T -> T -> T -> bool -> bool -> Set :=
  | LelNotGt of x <= y : lel_xor_gt x y x x y y x x y y true false
  | GtlNotLe of y < x  : lel_xor_gt x y y y x x y y x x false true.

Variant ltl_xor_ge (x y : T) :
  T -> T -> T -> T -> T -> T -> T -> T -> bool -> bool -> Set :=
  | LtlNotGe of x < y  : ltl_xor_ge x y x x y y x x y y false true
  | GelNotLt of y <= x : ltl_xor_ge x y y y x x y y x x true false.

Variant comparel (x y : T) :
   T -> T -> T -> T -> T -> T -> T -> T ->
   bool -> bool -> bool -> bool -> bool -> bool -> Set :=
  | ComparelLt of x < y : comparel x y
    x x y y x x y y false false false true false true
  | ComparelGt of y < x : comparel x y
    y y x x y y x x false false true false true false
  | ComparelEq of x = y : comparel x y
    x x x x x x x x true true true true false false.

Variant incomparel (x y : T) :
  T -> T -> T -> T -> T -> T -> T -> T ->
  bool -> bool -> bool -> bool -> bool -> bool -> bool -> bool -> Set :=
  | InComparelLt of x < y : incomparel x y
    x x y y x x y y false false false true false true true true
  | InComparelGt of y < x : incomparel x y
    y y x x y y x x false false true false true false true true
  | InComparel of x >< y  : incomparel x y
    x y y x (meet y x) (meet x y) (join y x) (join x y)
    false false false false false false false false
  | InComparelEq of x = y : incomparel x y
    x x x x x x x x true true true true false false true true.

End LatticeDef.

Module LatticeSyntax.

Notation "x `&` y" := (meet x y) : order_scope.
Notation "x `|` y" := (join x y) : order_scope.

End LatticeSyntax.
HB.export LatticeSyntax.

Module BLatticeSyntax.

Notation "\join_ ( i <- r | P ) F" :=
  (\big[@join _ _ / \bot]_(i <- r | P%B) F%O) : order_scope.
Notation "\join_ ( i <- r ) F" :=
  (\big[@join _ _ / \bot]_(i <- r) F%O) : order_scope.
Notation "\join_ ( i | P ) F" :=
  (\big[@join _ _ / \bot]_(i | P%B) F%O) : order_scope.
Notation "\join_ i F" :=
  (\big[@join _ _ / \bot]_i F%O) : order_scope.
Notation "\join_ ( i : I | P ) F" :=
  (\big[@join _ _ / \bot]_(i : I | P%B) F%O) (only parsing) : order_scope.
Notation "\join_ ( i : I ) F" :=
  (\big[@join _ _ / \bot]_(i : I) F%O) (only parsing) : order_scope.
Notation "\join_ ( m <= i < n | P ) F" :=
  (\big[@join _ _ / \bot]_(m <= i < n | P%B) F%O) : order_scope.
Notation "\join_ ( m <= i < n ) F" :=
  (\big[@join _ _ / \bot]_(m <= i < n) F%O) : order_scope.
Notation "\join_ ( i < n | P ) F" :=
  (\big[@join _ _ / \bot]_(i < n | P%B) F%O) : order_scope.
Notation "\join_ ( i < n ) F" :=
  (\big[@join _ _ / \bot]_(i < n) F%O) : order_scope.
Notation "\join_ ( i 'in' A | P ) F" :=
  (\big[@join _ _ / \bot]_(i in A | P%B) F%O) : order_scope.
Notation "\join_ ( i 'in' A ) F" :=
  (\big[@join _ _ / \bot]_(i in A) F%O) : order_scope.

End BLatticeSyntax.
HB.export BLatticeSyntax.

Module TLatticeSyntax.

Notation "\meet_ ( i <- r | P ) F" :=
  (\big[meet / \top]_(i <- r | P%B) F%O) : order_scope.
Notation "\meet_ ( i <- r ) F" :=
  (\big[meet / \top]_(i <- r) F%O) : order_scope.
Notation "\meet_ ( i | P ) F" :=
  (\big[meet / \top]_(i | P%B) F%O) : order_scope.
Notation "\meet_ i F" :=
  (\big[meet / \top]_i F%O) : order_scope.
Notation "\meet_ ( i : I | P ) F" :=
  (\big[meet / \top]_(i : I | P%B) F%O) (only parsing) : order_scope.
Notation "\meet_ ( i : I ) F" :=
  (\big[meet / \top]_(i : I) F%O) (only parsing) : order_scope.
Notation "\meet_ ( m <= i < n | P ) F" :=
 (\big[meet / \top]_(m <= i < n | P%B) F%O) : order_scope.
Notation "\meet_ ( m <= i < n ) F" :=
 (\big[meet / \top]_(m <= i < n) F%O) : order_scope.
Notation "\meet_ ( i < n | P ) F" :=
 (\big[meet / \top]_(i < n | P%B) F%O) : order_scope.
Notation "\meet_ ( i < n ) F" :=
 (\big[meet / \top]_(i < n) F%O) : order_scope.
Notation "\meet_ ( i 'in' A | P ) F" :=
 (\big[meet / \top]_(i in A | P%B) F%O) : order_scope.
Notation "\meet_ ( i 'in' A ) F" :=
 (\big[meet / \top]_(i in A) F%O) : order_scope.

End TLatticeSyntax.
HB.export TLatticeSyntax.

(**********)
(* FINITE *)
(**********)

#[short(type="finMeetSemilatticeType")]
HB.structure Definition FinMeetSemilattice d :=
  { T of Finite T & MeetSemilattice d T }.

#[short(type="finBMeetSemilatticeType")]
HB.structure Definition FinBMeetSemilattice d :=
  { T of Finite T & BMeetSemilattice d T }.

#[short(type="finJoinSemilatticeType")]
HB.structure Definition FinJoinSemilattice d :=
  { T of Finite T & JoinSemilattice d T }.

#[short(type="finTJoinSemilatticeType")]
HB.structure Definition FinTJoinSemilattice d :=
  { T of Finite T & TJoinSemilattice d T }.

#[short(type="finLatticeType")]
HB.structure Definition FinLattice d := { T of Finite T & Lattice d T }.

#[short(type="finTBLatticeType")]
HB.structure Definition FinTBLattice d := { T of Finite T & TBLattice d T }.

#[short(type="finDistrLatticeType")]
HB.structure Definition FinDistrLattice d :=
  { T of Finite T & DistrLattice d T }.

#[short(type="finTBDistrLatticeType")]
HB.structure Definition FinTBDistrLattice d :=
  { T of Finite T & TBDistrLattice d T }.

(*************)
(* MORPHISMS *)
(*************)

Definition meet_morphism d (T : latticeType d) d' (T' : latticeType d')
  (f : T -> T') : Prop := {morph f : x y / x `&` y}.

Definition join_morphism d (T : latticeType d) d' (T' : latticeType d')
  (f : T -> T') : Prop := {morph f : x y / x `|` y}.

HB.mixin Record isMeetLatticeMorphism d (T : latticeType d)
    d' (T' : latticeType d') (apply : T -> T') := {
  omorphI_subproof : meet_morphism apply;
}.

HB.mixin Record isJoinLatticeMorphism d (T : latticeType d)
    d' (T' : latticeType d') (apply : T -> T') := {
  omorphU_subproof : join_morphism apply;
}.

HB.structure Definition MeetLatticeMorphism d (T : latticeType d)
    d' (T' : latticeType d') :=
  {f of isMeetLatticeMorphism d T d' T' f & @OrderMorphism d T d' T' f}.

HB.structure Definition JoinLatticeMorphism d (T : latticeType d)
    d' (T' : latticeType d') :=
  {f of isJoinLatticeMorphism d T d' T' f & @OrderMorphism d T d' T' f}.

HB.structure Definition LatticeMorphism d (T : latticeType d)
    d' (T' : latticeType d') :=
  {f of @MeetLatticeMorphism d T d' T' f & @JoinLatticeMorphism d T d' T' f}.

HB.mixin Record isBLatticeMorphism d (T : bLatticeType d)
    d' (T' : bLatticeType d') (apply : T -> T') := {
  omorph0_subproof : apply \bot = \bot;
}.

HB.mixin Record isTLatticeMorphism d (T : tLatticeType d)
    d' (T' : tLatticeType d') (apply : T -> T') := {
  omorph1_subproof : apply \top = \top;
}.

HB.structure Definition BLatticeMorphism d (T : bLatticeType d)
    d' (T' : bLatticeType d') := {f of isBLatticeMorphism d T d' T' f}.

HB.structure Definition TLatticeMorphism d (T : tLatticeType d)
    d' (T' : tLatticeType d') := {f of isTLatticeMorphism d T d' T' f}.

HB.structure Definition TBLatticeMorphism d (T : tbLatticeType d)
    d' (T' : tbLatticeType d') :=
  {f of @BLatticeMorphism d T d' T' f & @TLatticeMorphism d T d' T' f}.

Module LatticeMorphismExports.
Notation "{ 'mlmorphism' T -> T' }" :=
  (@MeetLatticeMorphism.type _ T%type _ T'%type) : type_scope.
Notation "{ 'jlmorphism' T -> T' }" :=
  (@JoinLatticeMorphism.type _ T%type _ T'%type) : type_scope.
Notation "{ 'lmorphism' T -> T' }" :=
  (@LatticeMorphism.type _ T%type _ T'%type) : type_scope.
Notation "{ 'blmorphism' T -> T' }" :=
  (@BLatticeMorphism.type _ T%type _ T'%type) : type_scope.
Notation "{ 'tlmorphism' T -> T' }" :=
  (@TLatticeMorphism.type _ T%type _ T'%type) : type_scope.
Notation "{ 'tblmorphism' T -> T' }" :=
  (@TBLatticeMorphism.type _ T%type _ T'%type) : type_scope.
Notation "[ 'mlmorphism' 'of' f 'as' g ]" :=
  (MeetLatticeMorphism.clone _ _ _ _ f%function g)
  (format "[ 'mlmorphism'  'of'  f  'as'  g ]") : form_scope.
Notation "[ 'mlmorphism' 'of' f ]" :=
  (MeetLatticeMorphism.clone _ _ _ _ f%function _)
  (format "[ 'mlmorphism'  'of'  f ]") : form_scope.
Notation "[ 'jlmorphism' 'of' f 'as' g ]" :=
  (JoinLatticeMorphism.clone _ _ _ _ f%function g)
  (format "[ 'jlmorphism'  'of'  f  'as'  g ]") : form_scope.
Notation "[ 'jlmorphism' 'of' f ]" :=
  (JoinLatticeMorphism.clone _ _ _ _ f%function _)
  (format "[ 'jlmorphism'  'of'  f ]") : form_scope.
Notation "[ 'lmorphism' 'of' f 'as' g ]" :=
  (LatticeMorphism.clone _ _ _ _ f%function g)
  (format "[ 'lmorphism'  'of'  f  'as'  g ]") : form_scope.
Notation "[ 'lmorphism' 'of' f ]" :=
  (LatticeMorphism.clone _ _ _ _ f%function _)
  (format "[ 'lmorphism'  'of'  f ]") : form_scope.
End LatticeMorphismExports.
HB.export LatticeMorphismExports.

(*************)
(* STABILITY *)
(*************)

Module Import ClosedPredicates.
Section ClosedPredicates.

Variable (d : disp_t) (T : latticeType d).
Variable S : {pred T}.

Definition meet_closed := {in S &, forall u v, u `&` v \in S}.

Definition join_closed := {in S &, forall u v, u `|` v \in S}.

End ClosedPredicates.
End ClosedPredicates.

HB.mixin Record isMeetLatticeClosed d (T : latticeType d) (S : {pred T}) := {
  opredI : meet_closed S;
}.

HB.mixin Record isJoinLatticeClosed d (T : latticeType d) (S : {pred T}) := {
  opredU : join_closed S;
}.

HB.mixin Record isBLatticeClosed d (T : bLatticeType d) (S : {pred T}) := {
  opred0 : \bot \in S;
}.

HB.mixin Record isTLatticeClosed d (T : tLatticeType d) (S : {pred T}) := {
  opred1 : \top \in S;
}.

#[short(type="meetLatticeClosed")]
HB.structure Definition MeetLatticeClosed d T :=
  {S of isMeetLatticeClosed d T S}.

#[short(type="joinLatticeClosed")]
HB.structure Definition JoinLatticeClosed d T :=
  {S of isJoinLatticeClosed d T S}.

#[short(type="latticeClosed")]
HB.structure Definition LatticeClosed d T :=
  {S of @MeetLatticeClosed d T S & @JoinLatticeClosed d T S}.

#[short(type="bLatticeClosed")]
HB.structure Definition BLatticeClosed d T := {S of isBLatticeClosed d T S}.

#[short(type="bJoinLatticeClosed")]
HB.structure Definition BJoinLatticeClosed d T :=
  {S of isBLatticeClosed d T S & @JoinLatticeClosed d T S}.

#[short(type="tLatticeClosed")]
HB.structure Definition TLatticeClosed d T := {S of isTLatticeClosed d T S}.

#[short(type="tMeetLatticeClosed")]
HB.structure Definition TMeetLatticeClosed d T :=
  {S of isTLatticeClosed d T S & @MeetLatticeClosed d T S}.

#[short(type="tbLatticeClosed")]
HB.structure Definition TBLatticeClosed d (T : tbLatticeType d) :=
  {S of @BLatticeClosed d T S & @TLatticeClosed d T S}.

(************)
(* SUBTYPES *)
(************)

HB.mixin Record isMeetSubLattice d (T : latticeType d) (S : pred T) d' U
    & SubType T S U & Lattice d' U := {
  valI_subproof : {morph (val : U -> T) : x y / x `&` y};
}.

HB.mixin Record isJoinSubLattice d (T : latticeType d) (S : pred T) d' U
    & SubType T S U & Lattice d' U := {
  valU_subproof : {morph (val : U -> T) : x y / x `|` y};
}.

#[short(type="subPOrderLattice")]
HB.structure Definition SubPOrderLattice d (T : latticeType d) S d' :=
  { U of @SubPOrder d T S d' U & Lattice d' U }.

#[short(type="subPOrderBLattice")]
HB.structure Definition SubPOrderBLattice d (T : latticeType d) S d' :=
  { U of @SubPOrderLattice d T S d' U & BLattice d' U }.

#[short(type="subPOrderTLattice")]
HB.structure Definition SubPOrderTLattice d (T : latticeType d) S d' :=
  { U of @SubPOrderLattice d T S d' U & TLattice d' U }.

#[short(type="subPOrderTBLattice")]
HB.structure Definition SubPOrderTBLattice d (T : latticeType d) S d' :=
  { U of @SubPOrderLattice d T S d' U & TBLattice d' U }.

#[short(type="meetSubLattice")]
HB.structure Definition MeetSubLattice d (T : latticeType d) S d' :=
  { U of @SubPOrderLattice d T S d' U & isMeetSubLattice d T S d' U }.

#[short(type="meetSubBLattice")]
HB.structure Definition MeetSubBLattice d (T : latticeType d) S d' :=
  { U of @MeetSubLattice d T S d' U & BLattice d' U }.

#[short(type="meetSubTLattice")]
HB.structure Definition MeetSubTLattice d (T : latticeType d) S d' :=
  { U of @MeetSubLattice d T S d' U & TLattice d' U }.

#[short(type="meetSubTBLattice")]
HB.structure Definition MeetSubTBLattice d (T : latticeType d) S d' :=
  { U of @MeetSubLattice d T S d' U & TBLattice d' U }.

#[short(type="joinSubLattice")]
HB.structure Definition JoinSubLattice d (T : latticeType d) S d' :=
  { U of @SubPOrderLattice d T S d' U & isJoinSubLattice d T S d' U }.

#[short(type="joinSubBLattice")]
HB.structure Definition JoinSubBLattice d (T : latticeType d) S d' :=
  { U of @JoinSubLattice d T S d' U & BLattice d' U }.

#[short(type="joinSubTLattice")]
HB.structure Definition JoinSubTLattice d (T : latticeType d) S d' :=
  { U of @JoinSubLattice d T S d' U & TLattice d' U }.

#[short(type="joinSubTBLattice")]
HB.structure Definition JoinSubTBLattice d (T : latticeType d) S d' :=
  { U of @JoinSubLattice d T S d' U & TBLattice d' U }.

#[short(type="subLattice")]
HB.structure Definition SubLattice d (T : latticeType d) S d' :=
  { U of @MeetSubLattice d T S d' U & @JoinSubLattice d T S d' U }.

#[short(type="subBLattice")]
HB.structure Definition SubBLattice d (T : latticeType d) S d' :=
  { U of @SubLattice d T S d' U & BLattice d' U }.

#[short(type="subTLattice")]
HB.structure Definition SubTLattice d (T : latticeType d) S d' :=
  { U of @SubLattice d T S d' U & TLattice d' U }.

#[short(type="subTBLattice")]
HB.structure Definition SubTBLattice d (T : latticeType d) S d' :=
  { U of @SubLattice d T S d' U & TBLattice d' U }.

HB.mixin Record isBSubLattice d (T : bLatticeType d) (S : pred T) d' U
    & SubType T S U & BLattice d' U := {
  val0_subproof : (val : U -> T) \bot = \bot;
}.

#[short(type="bJoinSubLattice")]
HB.structure Definition BJoinSubLattice d (T : bLatticeType d) S d' :=
  { U of @JoinSubLattice d T S d' U & BLattice d' U & isBSubLattice d T S d' U }.

#[short(type="bJoinSubTLattice")]
HB.structure Definition BJoinSubTLattice d (T : bLatticeType d) S d' :=
  { U of @BJoinSubLattice d T S d' U & TBLattice d' U }.

#[short(type="bSubLattice")]
HB.structure Definition BSubLattice d (T : bLatticeType d) S d' :=
  { U of @SubLattice d T S d' U & @BJoinSubLattice d T S d' U }.

#[short(type="bSubTLattice")]
HB.structure Definition BSubTLattice d (T : bLatticeType d) S d' :=
  { U of @BSubLattice d T S d' U & TBLattice d' U }.

HB.mixin Record isTSubLattice d (T : tLatticeType d) (S : pred T) d' U
    & SubType T S U & TLattice d' U := {
  val1_subproof : (val : U -> T) \top = \top;
}.

#[short(type="tMeetSubLattice")]
HB.structure Definition TMeetSubLattice d (T : tLatticeType d) S d' :=
  { U of @MeetSubLattice d T S d' U & TLattice d' U & isTSubLattice d T S d' U }.

#[short(type="tMeetSubBLattice")]
HB.structure Definition TMeetSubBLattice d (T : tLatticeType d) S d' :=
  { U of @TMeetSubLattice d T S d' U & TBLattice d' U }.

#[short(type="tSubLattice")]
HB.structure Definition TSubLattice d (T : tLatticeType d) S d' :=
  { U of @SubLattice d T S d' U & @TMeetSubLattice d T S d' U }.

#[short(type="tSubBLattice")]
HB.structure Definition TSubBLattice d (T : tLatticeType d) S d' :=
  { U of @TSubLattice d T S d' U & TBLattice d' U }.

#[export] HB.instance Definition _
  d (T : latticeType d) (S : pred T) d' (U : meetSubLattice S d') :=
    isMeetLatticeMorphism.Build d' U d T val valI_subproof.

#[export] HB.instance Definition _
  d (T : latticeType d) (S : pred T) d' (U : joinSubLattice S d') :=
    isJoinLatticeMorphism.Build d' U d T val valU_subproof.

#[export] HB.instance Definition _
  d (T : bLatticeType d) (S : pred T) d' (U : bJoinSubLattice S d') :=
    isBLatticeMorphism.Build d' U d T val val0_subproof.

#[export] HB.instance Definition _
  d (T : tLatticeType d) (S : pred T) d' (U : tMeetSubLattice S d') :=
    isTLatticeMorphism.Build d' U d T val val1_subproof.

(********)
(* DUAL *)
(********)

Notation dual_meet := (@meet (dual_display _) _).
Notation dual_join := (@join (dual_display _) _).

Module Import DualSyntax.

Notation "x `&^d` y" := (dual_meet x y) : order_scope.
Notation "x `|^d` y" := (dual_join x y) : order_scope.

(* The following Local Notations are here to define the \join^d_ and \meet^d_ *)
(* notations later. Do not remove them.                                       *)
Local Notation "\bot" := dual_bottom.
Local Notation "\top" := dual_top.
Local Notation join := dual_join.
Local Notation meet := dual_meet.
Local Notation min := dual_min.
Local Notation max := dual_max.

Notation "\join^d_ ( i <- r | P ) F" :=
  (\big[join / \bot]_(i <- r | P%B) F%O) : order_scope.
Notation "\join^d_ ( i <- r ) F" :=
  (\big[join / \bot]_(i <- r) F%O) : order_scope.
Notation "\join^d_ ( i | P ) F" :=
  (\big[join / \bot]_(i | P%B) F%O) : order_scope.
Notation "\join^d_ i F" :=
  (\big[join / \bot]_i F%O) : order_scope.
Notation "\join^d_ ( i : I | P ) F" :=
  (\big[join / \bot]_(i : I | P%B) F%O) (only parsing) : order_scope.
Notation "\join^d_ ( i : I ) F" :=
  (\big[join / \bot]_(i : I) F%O) (only parsing) : order_scope.
Notation "\join^d_ ( m <= i < n | P ) F" :=
 (\big[join / \bot]_(m <= i < n | P%B) F%O) : order_scope.
Notation "\join^d_ ( m <= i < n ) F" :=
 (\big[join / \bot]_(m <= i < n) F%O) : order_scope.
Notation "\join^d_ ( i < n | P ) F" :=
 (\big[join / \bot]_(i < n | P%B) F%O) : order_scope.
Notation "\join^d_ ( i < n ) F" :=
 (\big[join / \bot]_(i < n) F%O) : order_scope.
Notation "\join^d_ ( i 'in' A | P ) F" :=
 (\big[join / \bot]_(i in A | P%B) F%O) : order_scope.
Notation "\join^d_ ( i 'in' A ) F" :=
 (\big[join / \bot]_(i in A) F%O) : order_scope.

Notation "\meet^d_ ( i <- r | P ) F" :=
  (\big[meet / \top]_(i <- r | P%B) F%O) : order_scope.
Notation "\meet^d_ ( i <- r ) F" :=
  (\big[meet / \top]_(i <- r) F%O) : order_scope.
Notation "\meet^d_ ( i | P ) F" :=
  (\big[meet / \top]_(i | P%B) F%O) : order_scope.
Notation "\meet^d_ i F" :=
  (\big[meet / \top]_i F%O) : order_scope.
Notation "\meet^d_ ( i : I | P ) F" :=
  (\big[meet / \top]_(i : I | P%B) F%O) (only parsing) : order_scope.
Notation "\meet^d_ ( i : I ) F" :=
  (\big[meet / \top]_(i : I) F%O) (only parsing) : order_scope.
Notation "\meet^d_ ( m <= i < n | P ) F" :=
 (\big[meet / \top]_(m <= i < n | P%B) F%O) : order_scope.
Notation "\meet^d_ ( m <= i < n ) F" :=
 (\big[meet / \top]_(m <= i < n) F%O) : order_scope.
Notation "\meet^d_ ( i < n | P ) F" :=
 (\big[meet / \top]_(i < n | P%B) F%O) : order_scope.
Notation "\meet^d_ ( i < n ) F" :=
 (\big[meet / \top]_(i < n) F%O) : order_scope.
Notation "\meet^d_ ( i 'in' A | P ) F" :=
 (\big[meet / \top]_(i in A | P%B) F%O) : order_scope.
Notation "\meet^d_ ( i 'in' A ) F" :=
 (\big[meet / \top]_(i in A) F%O) : order_scope.

End DualSyntax.

(*
FIXME: we have two issues in the dual instance declarations in the DualOrder
module below:
1. HB.saturate is slow, and
2. if we declare them by HB.instance, some declarations fail because it unfolds
   [dual] and the generated instance does not typecheck
   (math-comp/hierarchy-builder#257).
*)
Module DualOrder.

HB.instance Definition _ d (T : joinSemilatticeType d) :=
  POrder_isMeetSemilattice.Build (dual_display d) T^d (fun x y z => leUx y z x).

Lemma meetEdual d (T : joinSemilatticeType d) (x y : T) :
  ((x : T^d) `&^d` y) = (x `|` y).
Proof. by []. Qed.

HB.instance Definition _ d (T : meetSemilatticeType d) :=
  POrder_isJoinSemilattice.Build (dual_display d) T^d (fun x y z => lexI z x y).

Lemma joinEdual d (T : meetSemilatticeType d) (x y : T) :
  ((x : T^d) `|^d` y) = (x `&` y).
Proof. by []. Qed.

HB.saturate.

HB.instance Definition _ d (T : distrLatticeType d) :=
  Lattice_isDistributive.Build (dual_display d) T^d joinIl meetUl.

HB.saturate.

End DualOrder.
HB.export DualOrder.

(**********)
(* THEORY *)
(**********)

Module Import MeetTheory.
Section MeetTheory.
Context {disp : disp_t} {L : meetSemilatticeType disp}.
Implicit Types (x y : L).

(* interaction with order *)

Lemma lexI x y z : (x <= y `&` z) = (x <= y) && (x <= z).
Proof. exact: lexI. Qed.

Lemma leIr x y : y `&` x <= x.
Proof. by have:= le_refl (meet y x); rewrite lexI => /andP []. Qed.

Lemma leIl x y : x `&` y <= x.
Proof. by have:= le_refl (meet x y); rewrite lexI => /andP []. Qed.

Lemma leIxl x y z : y <= x -> y `&` z <= x.
Proof. exact/le_trans/leIl. Qed.

Lemma leIxr x y z : z <= x -> y `&` z <= x.
Proof. exact/le_trans/leIr. Qed.

Lemma leIx2 x y z : (y <= x) || (z <= x) -> y `&` z <= x.
Proof. by case/orP => [/leIxl|/leIxr]. Qed.

Lemma leEmeet x y : (x <= y) = (x `&` y == x).
Proof. by rewrite eq_le lexI leIl lexx. Qed.

Lemma eq_meetl x y : (x `&` y == x) = (x <= y).
Proof. by apply/esym/leEmeet. Qed.

Lemma eq_meetr x y : (x `&` y == y) = (y <= x).
Proof. by rewrite eq_le lexI leIr lexx andbT. Qed.

Lemma meet_idPl {x y} : reflect (x `&` y = x) (x <= y).
Proof. by rewrite -eq_meetl; apply/eqP. Qed.
Lemma meet_idPr {x y} : reflect (y `&` x = x) (x <= y).
Proof. by rewrite -eq_meetr; apply/eqP. Qed.

Lemma meet_l x y : x <= y -> x `&` y = x. Proof. exact/meet_idPl. Qed.
Lemma meet_r x y : y <= x -> x `&` y = y. Proof. exact/meet_idPr. Qed.

Lemma leIidl x y : (x <= x `&` y) = (x <= y).
Proof. by rewrite lexI lexx. Qed.
Lemma leIidr x y : (x <= y `&` x) = (x <= y).
Proof. by rewrite lexI lexx andbT. Qed.

Lemma leI2 x y z t : x <= z -> y <= t -> x `&` y <= z `&` t.
Proof. by move=> xz yt; rewrite lexI !leIx2 ?xz ?yt ?orbT //. Qed.

(* algebraic properties *)

Lemma meetC : commutative (@meet _ L).
Proof. by move=> x y; apply: le_anti; rewrite !lexI !leIr !leIl. Qed.

Lemma meetA : associative (@meet _ L).
Proof.
move=> x y z; apply: le_anti.
rewrite !lexI leIr leIl /= andbT -andbA.
rewrite ![_ `&` (_ `&` _) <= _]leIxr ?(leIr, leIl) //=.
by rewrite leIxl ?leIl // leIxl // leIr.
Qed.

HB.instance Definition _ := SemiGroup.isComLaw.Build L meet meetA meetC.

Lemma meetxx : idempotent_op (@meet _ L).
Proof. by move=> x; apply/eqP; rewrite -leEmeet. Qed.
Lemma meetAC : right_commutative (@meet _ L).
Proof. by move=> x y z; rewrite -!meetA [X in _ `&` X]meetC. Qed.
Lemma meetCA : left_commutative (@meet _ L).
Proof. by move=> x y z; rewrite !meetA [X in X `&` _]meetC. Qed.
Lemma meetACA : interchange (@meet _ L) (@meet _ L).
Proof. by move=> x y z t; rewrite !meetA [X in X `&` _]meetAC. Qed.

Lemma meetKI y x : x `&` (x `&` y) = x `&` y.
Proof. by rewrite meetA meetxx. Qed.
Lemma meetIK y x : (x `&` y) `&` y = x `&` y.
Proof. by rewrite -meetA meetxx. Qed.
Lemma meetKIC y x : x `&` (y `&` x) = x `&` y.
Proof. by rewrite meetC meetIK meetC. Qed.
Lemma meetIKC y x : y `&` x `&` y = x `&` y.
Proof. by rewrite meetAC meetC meetxx. Qed.

End MeetTheory.
End MeetTheory.

Arguments meet_idPl {disp L x y}.
Arguments meet_idPr {disp L x y}.

Module Import BMeetTheory.
Section BMeetTheory.
Context {disp : disp_t} {L : bMeetSemilatticeType disp}.

Lemma meet0x : left_zero \bot (@meet _ L).
Proof. by move=> x; apply/eqP; rewrite -leEmeet. Qed.

Lemma meetx0 : right_zero \bot (@meet _ L).
Proof. by move=> x; rewrite meetC meet0x. Qed.

HB.instance Definition _ := Monoid.isMulLaw.Build L \bot meet meet0x meetx0.

End BMeetTheory.
End BMeetTheory.

Module Import TMeetTheory.
Section TMeetTheory.
Context {disp : disp_t} {L : tMeetSemilatticeType disp}.
Implicit Types (I : finType) (T : eqType) (x y : L).

Lemma meetx1 : right_id \top (@meet _ L).
Proof. by move=> x; apply/eqP; rewrite -leEmeet. Qed.

Lemma meet1x : left_id \top (@meet _ L).
Proof. by move=> x; apply/eqP; rewrite meetC meetx1. Qed.

Lemma meet_eq1 x y : (x `&` y == \top) = (x == \top) && (y == \top).
Proof.
apply/idP/idP; last by move=> /andP[/eqP-> /eqP->]; rewrite meetx1.
by move=> /eqP xIy1; rewrite -!le1x -xIy1 leIl leIr.
Qed.

HB.instance Definition _ := Monoid.isMonoidLaw.Build L \top meet meet1x meetx1.

Lemma meets_inf_seq T (r : seq T) (P : {pred T}) (F : T -> L) (x : T) :
  x \in r -> P x -> \meet_(i <- r | P i) F i <= F x.
Proof. by move=> xr Px; rewrite (big_rem x) ?Px //= leIl. Qed.

Lemma meets_max_seq T (r : seq T) (P : {pred T}) (F : T -> L) (x : T) (u : L) :
  x \in r -> P x -> F x <= u -> \meet_(x <- r | P x) F x <= u.
Proof. by move=> ? ?; apply/le_trans/meets_inf_seq. Qed.

Lemma meets_inf I (j : I) (P : {pred I}) (F : I -> L) :
   P j -> \meet_(i | P i) F i <= F j.
Proof. exact: meets_inf_seq. Qed.

Lemma meets_max I (j : I) (u : L) (P : {pred I}) (F : I -> L) :
   P j -> F j <= u -> \meet_(i | P i) F i <= u.
Proof. exact: meets_max_seq. Qed.

Lemma meets_ge J (r : seq J) (P : {pred J}) (F : J -> L) (u : L) :
  (forall x : J, P x -> u <= F x) -> u <= \meet_(x <- r | P x) F x.
Proof. by move=> leFm; elim/big_rec: _ => // i x Px xu; rewrite lexI leFm. Qed.

Lemma meetsP_seq T (r : seq T) (P : {pred T}) (F : T -> L) (l : L) :
  reflect (forall x : T, x \in r -> P x -> l <= F x)
          (l <= \meet_(x <- r | P x) F x).
Proof.
apply: (iffP idP) => leFm => [x xr Px|].
  exact/(le_trans leFm)/meets_inf_seq.
by rewrite big_seq_cond meets_ge// => x /andP[/leFm].
Qed.

Lemma meetsP I (l : L) (P : {pred I}) (F : I -> L) :
   reflect (forall i : I, P i -> l <= F i) (l <= \meet_(i | P i) F i).
Proof. by apply: (iffP (meetsP_seq _ _ _ _)) => H ? ?; apply: H. Qed.

Lemma le_meets I (A B : {set I}) (F : I -> L) :
   A \subset B -> \meet_(i in B) F i <= \meet_(i in A) F i.
Proof. by move=> /subsetP AB; apply/meetsP => i iA; apply/meets_inf/AB. Qed.

Lemma meets_setU I (A B : {set I}) (F : I -> L) :
   \meet_(i in (A :|: B)) F i = \meet_(i in A) F i `&` \meet_(i in B) F i.
Proof.
rewrite -!big_enum; have /= <- := @big_cat _ _ meet.
apply/eq_big_idem; first exact: meetxx.
by move=> ?; rewrite mem_cat !fintype.mem_enum inE.
Qed.

Lemma meets_seq I (r : seq I) (F : I -> L) :
   \meet_(i <- r) F i = \meet_(i in r) F i.
Proof.
by rewrite -big_enum; apply/eq_big_idem => ?; rewrite /= ?meetxx ?fintype.mem_enum.
Qed.

End TMeetTheory.
End TMeetTheory.

Module Import JoinTheory.
Section JoinTheory.
Context {disp : disp_t} {L : joinSemilatticeType disp}.
Implicit Types (x y : L).

(* interaction with order *)

Lemma leUx x y z : (x `|` y <= z) = (x <= z) && (y <= z).
Proof. exact: leUx. Qed.

Lemma leUr x y : x <= y `|` x. Proof. exact: (@leIr _ L^d). Qed.
Lemma leUl x y : x <= x `|` y. Proof. exact: (@leIl _ L^d). Qed.

Lemma lexUl x y z : x <= y -> x <= y `|` z.
Proof. exact: (@leIxl _ L^d). Qed.
Lemma lexUr x y z : x <= z -> x <= y `|` z.
Proof. exact: (@leIxr _ L^d). Qed.
Lemma lexU2 x y z : (x <= y) || (x <= z) -> x <= y `|` z.
Proof. exact: (@leIx2 _ L^d). Qed.

Lemma leEjoin x y : (x <= y) = (x `|` y == y).
Proof. by rewrite [LHS](@leEmeet _ L^d) meetC. Qed.

Lemma eq_joinl x y : (x `|` y == x) = (y <= x).
Proof. exact: (@eq_meetl _ L^d). Qed.
Lemma eq_joinr x y : (x `|` y == y) = (x <= y).
Proof. exact: (@eq_meetr _ L^d). Qed.

Lemma join_idPl {x y} : reflect (y `|` x = y) (x <= y).
Proof. exact: (@meet_idPl _ L^d). Qed.
Lemma join_idPr {x y} : reflect (x `|` y = y) (x <= y).
Proof. exact: (@meet_idPr _ L^d). Qed.

Lemma join_l x y : y <= x -> x `|` y = x. Proof. exact/join_idPl. Qed.
Lemma join_r x y : x <= y -> x `|` y = y. Proof. exact/join_idPr. Qed.

Lemma leUidl x y : (x `|` y <= y) = (x <= y).
Proof. exact: (@leIidr _ L^d). Qed.
Lemma leUidr x y : (y `|` x <= y) = (x <= y).
Proof. exact: (@leIidl _ L^d). Qed.

Lemma leU2 x y z t : x <= z -> y <= t -> x `|` y <= z `|` t.
Proof. exact: (@leI2 _ L^d). Qed.

(* algebraic properties *)

Lemma joinC : commutative (@join _ L). Proof. exact: (@meetC _ L^d). Qed.
Lemma joinA : associative (@join _ L). Proof. exact: (@meetA _ L^d). Qed.

HB.instance Definition _ := SemiGroup.isComLaw.Build L join joinA joinC.

Lemma joinxx : idempotent_op (@join _ L).
Proof. exact: (@meetxx _ L^d). Qed.
Lemma joinAC : right_commutative (@join _ L).
Proof. exact: (@meetAC _ L^d). Qed.
Lemma joinCA : left_commutative (@join _ L).
Proof. exact: (@meetCA _ L^d). Qed.
Lemma joinACA : interchange (@join _ L) (@join _ L).
Proof. exact: (@meetACA _ L^d). Qed.

Lemma joinKU y x : x `|` (x `|` y) = x `|` y.
Proof. exact: (@meetKI _ L^d). Qed.
Lemma joinUK y x : (x `|` y) `|` y = x `|` y.
Proof. exact: (@meetIK _ L^d). Qed.
Lemma joinKUC y x : x `|` (y `|` x) = x `|` y.
Proof. exact: (@meetKIC _ L^d). Qed.
Lemma joinUKC y x : y `|` x `|` y = x `|` y.
Proof. exact: (@meetIKC _ L^d). Qed.

End JoinTheory.
End JoinTheory.

Arguments join_idPl {disp L x y}.
Arguments join_idPr {disp L x y}.

Module Import BJoinTheory.
Section BJoinTheory.
Context {disp : disp_t} {L : bJoinSemilatticeType disp}.
Implicit Types (I : finType) (T : eqType) (x y : L).

Lemma joinx0 : right_id \bot (@join _ L).
Proof. exact: (@meetx1 _ L^d). Qed.
Lemma join0x : left_id \bot (@join _ L).
Proof. exact: (@meet1x _ L^d). Qed.

Lemma join_eq0 x y : (x `|` y == \bot) = (x == \bot) && (y == \bot).
Proof. exact: (@meet_eq1 _ L^d). Qed.

HB.instance Definition _ := Monoid.isMonoidLaw.Build L \bot join join0x joinx0.

Lemma joins_sup_seq T (r : seq T) (P : {pred T}) (F : T -> L) (x : T) :
  x \in r -> P x -> F x <= \join_(i <- r | P i) F i.
Proof. exact: (@meets_inf_seq _ L^d). Qed.

Lemma joins_min_seq T (r : seq T) (P : {pred T}) (F : T -> L) (x : T) (l : L) :
  x \in r -> P x -> l <= F x -> l <= \join_(x <- r | P x) F x.
Proof. exact: (@meets_max_seq _ L^d). Qed.

Lemma joins_sup I (j : I) (P : {pred I}) (F : I -> L) :
  P j -> F j <= \join_(i | P i) F i.
Proof. exact: (@meets_inf _ L^d). Qed.

Lemma joins_min I (j : I) (l : L) (P : {pred I}) (F : I -> L) :
  P j -> l <= F j -> l <= \join_(i | P i) F i.
Proof. exact: (@meets_max _ L^d). Qed.

Lemma joins_le J (r : seq J) (P : {pred J}) (F : J -> L) (u : L) :
  (forall x : J, P x -> F x <= u) -> \join_(x <- r | P x) F x <= u.
Proof. exact: (@meets_ge _ L^d). Qed.

Lemma joinsP_seq T (r : seq T) (P : {pred T}) (F : T -> L) (u : L) :
  reflect (forall x : T, x \in r -> P x -> F x <= u)
          (\join_(x <- r | P x) F x <= u).
Proof. exact: (@meetsP_seq _ L^d). Qed.

Lemma joinsP I (u : L) (P : {pred I}) (F : I -> L) :
  reflect (forall i : I, P i -> F i <= u) (\join_(i | P i) F i <= u).
Proof. exact: (@meetsP _ L^d). Qed.

Lemma le_joins I (A B : {set I}) (F : I -> L) :
  A \subset B -> \join_(i in A) F i <= \join_(i in B) F i.
Proof. exact: (@le_meets _ L^d). Qed.

Lemma joins_setU I (A B : {set I}) (F : I -> L) :
  \join_(i in (A :|: B)) F i = \join_(i in A) F i `|` \join_(i in B) F i.
Proof. exact: (@meets_setU _ L^d). Qed.

Lemma joins_seq I (r : seq I) (F : I -> L) :
  \join_(i <- r) F i = \join_(i in r) F i.
Proof. exact: (@meets_seq _ L^d). Qed.

End BJoinTheory.
End BJoinTheory.

Module Import TJoinTheory.
Section TJoinTheory.
Context {disp : disp_t} {L : tJoinSemilatticeType disp}.

Lemma joinx1 : right_zero \top (@join _ L). Proof. exact: (@meetx0 _ L^d). Qed.
Lemma join1x : left_zero \top (@join _ L). Proof. exact: (@meet0x _ L^d). Qed.

HB.instance Definition _ := Monoid.isMulLaw.Build L \top join join1x joinx1.

End TJoinTheory.
End TJoinTheory.

Module Import LatticeTheory.
Section LatticeTheory.
Context {disp : disp_t} {L : latticeType disp}.
Implicit Types (x y : L).

Lemma meetUK x y : (x `&` y) `|` y = y. Proof. exact/join_idPr/leIr. Qed.
Lemma meetUKC x y : (y `&` x) `|` y = y. Proof. by rewrite meetC meetUK. Qed.
Lemma meetKUC y x : x `|` (y `&` x) = x. Proof. by rewrite joinC meetUK. Qed.
Lemma meetKU y x : x `|` (x `&` y) = x. Proof. by rewrite meetC meetKUC. Qed.

Lemma joinIK x y : (x `|` y) `&` y = y. Proof. exact/meet_idPr/leUr. Qed.
Lemma joinIKC x y : (y `|` x) `&` y = y. Proof. by rewrite joinC joinIK. Qed.
Lemma joinKIC y x : x `&` (y `|` x) = x. Proof. by rewrite meetC joinIK. Qed.
Lemma joinKI y x : x `&` (x `|` y) = x. Proof. by rewrite joinC joinKIC. Qed.

(* comparison predicates *)

Lemma lcomparableP x y : incomparel x y
  (min y x) (min x y) (max y x) (max x y)
  (y `&` x) (x `&` y) (y `|` x) (x `|` y)
  (y == x) (x == y) (x >= y) (x <= y) (x > y) (x < y) (y >=< x) (x >=< y).
Proof.
by case: (comparableP x) => [hxy|hxy|hxy|->]; do 1?have hxy' := ltW hxy;
   rewrite ?(meetxx, joinxx);
   rewrite ?(meet_l hxy', meet_r hxy', join_l hxy', join_r hxy');
   constructor.
Qed.

Lemma lcomparable_ltgtP x y : x >=< y ->
  comparel x y (min y x) (min x y) (max y x) (max x y)
               (y `&` x) (x `&` y) (y `|` x) (x `|` y)
               (y == x) (x == y) (x >= y) (x <= y) (x > y) (x < y).
Proof. by case: (lcomparableP x) => // *; constructor. Qed.

Lemma lcomparable_leP x y : x >=< y ->
  lel_xor_gt x y (min y x) (min x y) (max y x) (max x y)
                 (y `&` x) (x `&` y) (y `|` x) (x `|` y) (x <= y) (y < x).
Proof. by move/lcomparable_ltgtP => [/ltW xy|xy|->]; constructor. Qed.

Lemma lcomparable_ltP x y : x >=< y ->
  ltl_xor_ge x y (min y x) (min x y) (max y x) (max x y)
                 (y `&` x) (x `&` y) (y `|` x) (x `|` y) (y <= x) (x < y).
Proof. by move=> /lcomparable_ltgtP [xy|/ltW xy|->]; constructor. Qed.

End LatticeTheory.
End LatticeTheory.

Module Import LatticeMorphismTheory.
Section LatticeMorphismTheory.

Section Properties.

Variables (d : disp_t) (T : latticeType d) (d' : disp_t) (T' : latticeType d').

Lemma omorphI (f : {mlmorphism T -> T'}) : {morph f : x y / x `&` y}.
Proof. exact: omorphI_subproof. Qed.

Lemma omorphU (f : {jlmorphism T -> T'}) : {morph f : x y / x `|` y}.
Proof. exact: omorphU_subproof. Qed.

End Properties.

Section IdCompFun.

Variables (d : disp_t) (T : latticeType d) (d' : disp_t) (T' : latticeType d').
Variables (d'' : disp_t) (T'' : latticeType d'').

Section MeetCompFun.

Variables (f : {mlmorphism T' -> T''}) (g : {mlmorphism T -> T'}).

Fact idfun_is_meet_morphism : meet_morphism (@idfun T). Proof. by []. Qed.
#[export]
HB.instance Definition _ := isMeetLatticeMorphism.Build d T d T idfun
  idfun_is_meet_morphism.

Fact comp_is_meet_morphism : meet_morphism (f \o g).
Proof. by move=> x y; rewrite /= !omorphI. Qed.
#[export]
HB.instance Definition _ := isMeetLatticeMorphism.Build d T d'' T'' (f \o g)
  comp_is_meet_morphism.

End MeetCompFun.

Section JoinCompFun.

Variables (f : {jlmorphism T' -> T''}) (g : {jlmorphism T -> T'}).

Fact idfun_is_join_morphism : join_morphism (@idfun T). Proof. by []. Qed.
#[export]
HB.instance Definition _ := isJoinLatticeMorphism.Build d T d T idfun
  idfun_is_join_morphism.

Fact comp_is_join_morphism : join_morphism (f \o g).
Proof. by move=> x y; rewrite /= !omorphU. Qed.
#[export]
HB.instance Definition _ := isJoinLatticeMorphism.Build d T d'' T'' (f \o g)
  comp_is_join_morphism.

End JoinCompFun.

End IdCompFun.

End LatticeMorphismTheory.
End LatticeMorphismTheory.

Module Import BLatticeMorphismTheory.
Section BLatticeMorphismTheory.

Section Properties.

Variables (d : disp_t) (T : bLatticeType d).
Variables (d' : disp_t) (T' : bLatticeType d').
Variables (f : {blmorphism T -> T'}).

Lemma omorph0 : f \bot = \bot.
Proof. exact: omorph0_subproof. Qed.

End Properties.

Section IdCompFun.

Variables (d : disp_t) (T : bLatticeType d).
Variables (d' : disp_t) (T' : bLatticeType d').
Variables (d'' : disp_t) (T'' : bLatticeType d'').
Variables (f : {blmorphism T' -> T''}) (g : {blmorphism T -> T'}).

Fact idfun_is_bottom_morphism : (@idfun T) \bot = \bot. Proof. by []. Qed.
#[export]
HB.instance Definition _ := isBLatticeMorphism.Build d T d T idfun
  idfun_is_bottom_morphism.

Fact comp_is_bottom_morphism : (f \o g) \bot = \bot.
Proof. by rewrite /= !omorph0. Qed.
#[export]
HB.instance Definition _ := isBLatticeMorphism.Build d T d'' T'' (f \o g)
  comp_is_bottom_morphism.

End IdCompFun.

End BLatticeMorphismTheory.
End BLatticeMorphismTheory.

Module Import TLatticeMorphismTheory.
Section TLatticeMorphismTheory.

Section Properties.

Variables (d : disp_t) (T : tLatticeType d).
Variables (d' : disp_t) (T' : tLatticeType d').
Variables (f : {tlmorphism T -> T'}).

Lemma omorph1 : f \top = \top.
Proof. exact: omorph1_subproof. Qed.

End Properties.

Section IdCompFun.

Variables (d : disp_t) (T : tLatticeType d).
Variables (d' : disp_t) (T' : tLatticeType d').
Variables (d'' : disp_t) (T'' : tLatticeType d'').
Variables (f : {tlmorphism T' -> T''}) (g : {tlmorphism T -> T'}).

Fact idfun_is_top_morphism : (@idfun T) \top = \top. Proof. by []. Qed.
#[export]
HB.instance Definition _ := isTLatticeMorphism.Build d T d T idfun
  idfun_is_top_morphism.

Fact comp_is_top_morphism : (f \o g) \top = \top.
Proof. by rewrite /= !omorph1. Qed.
#[export]
HB.instance Definition _ := isTLatticeMorphism.Build d T d'' T'' (f \o g)
  comp_is_top_morphism.

End IdCompFun.

End TLatticeMorphismTheory.
End TLatticeMorphismTheory.

Module Import LatticePred.
Section LatticePred.

Variables (d : disp_t) (T : latticeType d).

Lemma opredI (S : meetLatticeClosed T) : {in S &, forall u v, u `&` v \in S}.
Proof. exact: opredI. Qed.

Lemma opredU (S : joinLatticeClosed T) : {in S &, forall u v, u `|` v \in S}.
Proof. exact: opredU. Qed.

End LatticePred.

Section BLatticePred.

Variables (d : disp_t) (T : bLatticeType d).

Lemma opred0 (S : bLatticeClosed T) : \bot \in S.
Proof. exact: opred0. Qed.

Lemma opred_joins (S : bJoinLatticeClosed T) I r (P : pred I) F :
  (forall i, P i -> F i \in S) -> \join_(i <- r | P i) F i \in S.
Proof. by move=> FS; elim/big_ind: _; [exact: opred0 | exact: opredU |]. Qed.

End BLatticePred.

Section TLatticePred.

Variables (d : disp_t) (T : tLatticeType d).

Lemma opred1 (S : tLatticeClosed T) : \top \in S.
Proof. exact: opred1. Qed.

Lemma opred_meets (S : tMeetLatticeClosed T) I r (P : pred I) F :
  (forall i, P i -> F i \in S) -> \meet_(i <- r | P i) F i \in S.
Proof. by move=> FS; elim/big_ind: _; [exact: opred1 | exact: opredI |]. Qed.

End TLatticePred.
End LatticePred.

Module Import DistrLatticeTheory.
Section DistrLatticeTheory.
Context {disp : disp_t} {L : distrLatticeType disp}.

Lemma meetUl : left_distributive (@meet _ L) (@join _ L).
Proof. exact: meetUl. Qed.

Lemma meetUr : right_distributive (@meet _ L) (@join _ L).
Proof. by move=> x y z; rewrite ![x `&` _]meetC meetUl. Qed.

Lemma joinIl : left_distributive (@join _ L) (@meet _ L).
Proof. exact: joinIl. Qed.

Lemma joinIr : right_distributive (@join _ L) (@meet _ L).
Proof. by move=> x y z; rewrite ![x `|` _]joinC joinIl. Qed.

#[warning="-HB.no-new-instance"]
HB.instance Definition _ := Monoid.isAddLaw.Build L meet join meetUl meetUr.
HB.instance Definition _ := Monoid.isAddLaw.Build L join meet joinIl joinIr.

End DistrLatticeTheory.
End DistrLatticeTheory.

Module Import BDistrLatticeTheory.
Section BDistrLatticeTheory.
Context {disp : disp_t} {L : bDistrLatticeType disp}.
Implicit Types (x y z : L).

Lemma leU2l_le y t x z : x `&` t = \bot -> x `|` y <= z `|` t -> x <= z.
Proof.
by move=> xIt0 /(leI2 (lexx x)); rewrite joinKI meetUr xIt0 joinx0 leIidl.
Qed.

Lemma leU2r_le y t x z : x `&` t = \bot -> y `|` x <= t `|` z -> x <= z.
Proof. by rewrite joinC [_ `|` z]joinC => /leU2l_le H /H. Qed.

Lemma disjoint_lexUl z x y : x `&` z = \bot -> (x <= y `|` z) = (x <= y).
Proof.
move=> xz0; apply/idP/idP=> xy; last by rewrite lexU2 ?xy.
by apply: (@leU2l_le x z); rewrite ?joinxx.
Qed.

Lemma disjoint_lexUr z x y : x `&` z = \bot -> (x <= z `|` y) = (x <= y).
Proof. by move=> xz0; rewrite joinC; rewrite disjoint_lexUl. Qed.

Lemma leU2E x y z t : x `&` t = \bot -> y `&` z = \bot ->
  (x `|` y <= z `|` t) = (x <= z) && (y <= t).
Proof.
move=> dxt dyz; apply/idP/andP; last by case=> ? ?; exact: leU2.
by move=> lexyzt; rewrite (leU2l_le _ lexyzt) // (leU2r_le _ lexyzt).
Qed.

Lemma joins_disjoint (I : finType) (d : L) (P : {pred I}) (F : I -> L) :
   (forall i : I, P i -> d `&` F i = \bot) -> d `&` \join_(i | P i) F i = \bot.
Proof.
move=> d_Fi_disj; have : \big[andb/true]_(i | P i) (d `&` F i == \bot).
  rewrite big_all_cond; apply/allP => i _ /=.
  by apply/implyP => /d_Fi_disj ->.
elim/big_rec2: _ => [|i y]; first by rewrite meetx0.
case; rewrite (andbF, andbT) // => Pi /(_ isT) dy /eqP dFi.
by rewrite meetUr dy dFi joinxx.
Qed.

End BDistrLatticeTheory.
End BDistrLatticeTheory.

Module Import TDistrLatticeTheory.
Section TDistrLatticeTheory.
Context {disp : disp_t} {L : tDistrLatticeType disp}.
Implicit Types (x y : L).

Lemma leI2l_le y t x z : y `|` z = \top -> x `&` y <= z `&` t -> x <= z.
Proof. by rewrite joinC; exact: (@leU2l_le _ L^d). Qed.

Lemma leI2r_le y t x z : y `|` z = \top -> y `&` x <= t `&` z -> x <= z.
Proof. by rewrite joinC; exact: (@leU2r_le _ L^d). Qed.

Lemma cover_leIxl z x y : z `|` y = \top -> (x `&` z <= y) = (x <= y).
Proof. by rewrite joinC; exact: (@disjoint_lexUl _ L^d). Qed.

Lemma cover_leIxr z x y : z `|` y = \top -> (z `&` x <= y) = (x <= y).
Proof. by rewrite joinC; exact: (@disjoint_lexUr _ L^d). Qed.

Lemma leI2E x y z t : x `|` t = \top -> y `|` z = \top ->
  (x `&` y <= z `&` t) = (x <= z) && (y <= t).
Proof. by move=> ? ?; apply: (@leU2E _ L^d); rewrite meetC. Qed.

Lemma meets_total (I : finType) (d : L) (P : {pred I}) (F : I -> L) :
   (forall i : I, P i -> d `|` F i = \top) -> d `|` \meet_(i | P i) F i = \top.
Proof. exact: (@joins_disjoint _ L^d). Qed.

End TDistrLatticeTheory.
End TDistrLatticeTheory.

(*************)
(* FACTORIES *)
(*************)

(* meetSemilatticeType and joinSemilatticeType *)

HB.factory Record POrder_Meet_isSemilattice d T & POrder d T := {
  meet : T -> T -> T;
  meetC : commutative meet;
  meetA : associative meet;
  leEmeet : forall x y, (x <= y) = (meet x y == x);
}.

HB.builders Context d T & POrder_Meet_isSemilattice d T.

Fact meetxx : idempotent_op meet.
Proof. by move=> x; apply/eqP; rewrite -leEmeet. Qed.

Fact lexI x y z : (x <= meet y z) = (x <= y) && (x <= z).
Proof.
rewrite !leEmeet; apply/eqP/andP => [<-|[/eqP<- /eqP<-]].
  split; apply/eqP; last by rewrite meetA -meetA meetxx.
  by rewrite -!meetA (meetC z) (meetA y) meetxx.
by rewrite -!meetA (meetC z) -meetA (meetA y) !meetxx.
Qed.

HB.instance Definition _ := @POrder_isMeetSemilattice.Build d T meet lexI.

HB.end.

HB.factory Record POrder_Join_isSemilattice d T & POrder d T := {
  join : T -> T -> T;
  joinC : commutative join;
  joinA : associative join;
  leEjoin : forall x y, (y <= x) = (join x y == x);
}.

HB.builders Context d T & POrder_Join_isSemilattice d T.

Fact joinxx : idempotent_op join.
Proof. by move=> x; apply/eqP; rewrite -leEjoin. Qed.

Fact leUx x y z : (join x y <= z) = (x <= z) && (y <= z).
rewrite !leEjoin; apply/eqP/andP => [<-|[/eqP<- /eqP<-]].
  split; apply/eqP; last by rewrite joinA -joinA joinxx.
  by rewrite -joinA (joinC _ x) (joinA x) joinxx.
by rewrite -!joinA (joinC y) -joinA (joinA x) !joinxx.
Qed.

HB.instance Definition _ := @POrder_isJoinSemilattice.Build d T join leUx.

HB.end.

(* latticeType *)

HB.factory Record POrder_MeetJoin_isLattice d T & POrder d T := {
  meet : T -> T -> T;
  join : T -> T -> T;
  meetP : forall x y z, (x <= meet y z) = (x <= y) && (x <= z);
  joinP : forall x y z, (join x y <= z) = (x <= z) && (y <= z);
}.

HB.builders Context d T & POrder_MeetJoin_isLattice d T.
HB.instance Definition _ := @POrder_isMeetSemilattice.Build d T meet meetP.
HB.instance Definition _ := @POrder_isJoinSemilattice.Build d T join joinP.
HB.end.

HB.factory Record POrder_isLattice d T & POrder d T := {
  meet : T -> T -> T;
  join : T -> T -> T;
  meetC : commutative meet;
  joinC : commutative join;
  meetA : associative meet;
  joinA : associative join;
  joinKI : forall y x, meet x (join x y) = x;
  meetKU : forall y x, join x (meet x y) = x;
  leEmeet : forall x y, (x <= y) = (meet x y == x);
}.

HB.builders Context d T & POrder_isLattice d T.

Fact leEjoin x y : (y <= x) = (join x y == x).
Proof.
rewrite leEmeet; apply/eqP/eqP => <-.
  by rewrite meetC meetKU.
by rewrite joinC joinKI.
Qed.

Fact meetxx : idempotent_op meet.
Proof. by move=> x; apply/eqP; rewrite -leEmeet. Qed.

Fact lexI x y z : (x <= meet y z) = (x <= y) && (x <= z).
Proof.
rewrite !leEmeet; apply/eqP/andP => [<-|[/eqP<- /eqP<-]].
  split; apply/eqP; last by rewrite meetA -meetA meetxx.
  by rewrite -!meetA (meetC z) (meetA y) meetxx.
by rewrite -!meetA (meetC z) -meetA (meetA y) !meetxx.
Qed.

Fact joinxx : idempotent_op join.
Proof. by move=> x; apply/eqP; rewrite -leEjoin. Qed.

Fact leUx x y z : (join x y <= z) = (x <= z) && (y <= z).
rewrite !leEjoin; apply/eqP/andP => [<-|[/eqP<- /eqP<-]].
  split; apply/eqP; last by rewrite joinA -joinA joinxx.
  by rewrite -joinA (joinC _ x) (joinA x) joinxx.
by rewrite -!joinA (joinC y) -joinA (joinA x) !joinxx.
Qed.

HB.instance Definition _ := @POrder_MeetJoin_isLattice.Build d T
  meet join lexI leUx.

HB.end.

(* distrLatticeType *)

HB.factory Record Lattice_Meet_isDistrLattice d T & Lattice d T := {
  meetUl : @left_distributive T T meet join;
}.

HB.builders Context d T & Lattice_Meet_isDistrLattice d T.

Let meetUr : right_distributive (@meet _ T) (@join _ T).
Proof. by move=> x y z; rewrite ![x `&` _]meetC meetUl. Qed.

Let joinIl : left_distributive (@join _ T) (@meet _ T).
Proof. by move=> x y z; rewrite meetUr joinIK meetUl -joinA meetUKC. Qed.

HB.instance Definition _ := Lattice_isDistributive.Build d T meetUl joinIl.

HB.end.

HB.factory Record POrder_Meet_isDistrLattice d T & POrder d T := {
  meet : T -> T -> T;
  join : T -> T -> T;
  meetC : commutative meet;
  joinC : commutative join;
  meetA : associative meet;
  joinA : associative join;
  joinKI : forall y x, meet x (join x y) = x;
  meetKU : forall y x, join x (meet x y) = x;
  leEmeet : forall x y, (x <= y) = (meet x y == x);
  meetUl : left_distributive meet join;
}.

HB.builders Context d T & POrder_Meet_isDistrLattice d T.

HB.instance Definition _ := @POrder_isLattice.Build d T
  meet join meetC joinC meetA joinA joinKI meetKU leEmeet.
HB.instance Definition _ :=
  Lattice_Meet_isDistrLattice.Build d T meetUl.

HB.end.

HB.factory Record isMeetJoinDistrLattice (d : disp_t) T & Choice T := {
  le : rel T;
  lt : rel T;
  meet : T -> T -> T;
  join : T -> T -> T;
  le_def : forall x y : T, le x y = (meet x y == x);
  lt_def : forall x y : T, lt x y = (y != x) && le x y;
  meetC : commutative meet;
  joinC : commutative join;
  meetA : associative meet;
  joinA : associative join;
  joinKI : forall y x : T, meet x (join x y) = x;
  meetKU : forall y x : T, join x (meet x y) = x;
  meetUl : left_distributive meet join;
  meetxx : idempotent_op meet;
}.

HB.builders Context d T & isMeetJoinDistrLattice d T.

Fact le_refl : reflexive le. Proof. by move=> x; rewrite le_def meetxx. Qed.

Fact le_anti : antisymmetric le.
Proof. by move=> x y; rewrite !le_def meetC => /andP [] /eqP {2}<- /eqP ->. Qed.

Fact le_trans : transitive le.
Proof.
move=> y x z; rewrite !le_def => /eqP lexy /eqP leyz; apply/eqP.
by rewrite -[in LHS]lexy -meetA leyz lexy.
Qed.

Fact lt_le_def x y : lt x y = (le x y) && ~~ (le y x).
Proof.
rewrite lt_def andbC; case/boolP: (le x y) => //= xy.
congr negb; apply/eqP/idP => [->|yx]; first exact/le_refl.
by apply/le_anti/andP; split.
Qed.

HB.instance Definition _ := isPreorder.Build d T
  lt_le_def le_refl le_trans.
HB.instance Definition _ := Preorder_isPOrder.Build d T le_anti.

HB.instance Definition _ := @POrder_Meet_isDistrLattice.Build d T
  meet join meetC joinC meetA joinA joinKI meetKU le_def meetUl.

HB.end.

HB.factory Record IsoLattice disp T & POrder disp T := {
  disp' : disp_t;
  T' : latticeType disp';
  f : T -> T';
  f' : T' -> T;
  f_can : cancel f f';
  f'_can : cancel f' f;
  f_mono : {mono f : x y / x <= y};
}.

HB.builders Context disp T & IsoLattice disp T.

Definition meet (x y : T) := f' (meet (f x) (f y)).
Definition join (x y : T) := f' (join (f x) (f y)).

Fact lexI x y z : (x <= meet y z) = (x <= y) && (x <= z).
Proof. by rewrite -!f_mono f'_can lexI. Qed.
Fact leUx x y z : (join x y <= z) = (x <= z) && (y <= z).
Proof. by rewrite -!f_mono f'_can leUx. Qed.
HB.instance Definition _ := POrder_MeetJoin_isLattice.Build _ T lexI leUx.

HB.end.

HB.factory Record IsoDistrLattice disp T & POrder disp T := {
  disp' : disp_t;
  T' : distrLatticeType disp';
  f : T -> T';
  f' : T' -> T;
  f_can : cancel f f';
  f'_can : cancel f' f;
  f_mono : {mono f : x y / x <= y};
}.

HB.builders Context disp T & IsoDistrLattice disp T.

HB.instance Definition _ := IsoLattice.Build _ T f_can f'_can f_mono.

Fact meetUl : left_distributive (meet : T -> T -> T) join.
Proof. by move=> x y z; rewrite /meet /join /= !f'_can meetUl. Qed.

HB.instance Definition _ := Lattice_Meet_isDistrLattice.Build _ T meetUl.

HB.end.

(* morphisms *)

HB.factory Record isLatticeMorphism d (T : latticeType d)
    d' (T' : latticeType d') (f : T -> T') & @OrderMorphism d T d' T' f := {
  omorphI_subproof : meet_morphism f;
  omorphU_subproof : join_morphism f;
}.

HB.builders Context d T d' T' f & isLatticeMorphism d T d' T' f.
HB.instance Definition _ := isMeetLatticeMorphism.Build d T d' T' f
  omorphI_subproof.
HB.instance Definition _ := isJoinLatticeMorphism.Build d T d' T' f
  omorphU_subproof.
HB.end.

(* stability *)

HB.factory Record isLatticeClosed d (T : latticeType d) (S : {pred T}) := {
  opredI : meet_closed S;
  opredU : join_closed S;
}.

HB.builders Context d T S & isLatticeClosed d T S.
HB.instance Definition _ := isMeetLatticeClosed.Build d T S opredI.
HB.instance Definition _ := isJoinLatticeClosed.Build d T S opredU.
HB.end.

HB.factory Record isTBLatticeClosed d (T : tbLatticeType d) (S : {pred T}) := {
  opredI : meet_closed S;
  opredU : join_closed S;
  opred0 : \bot \in S;
  opred1 : \top \in S;
}.

HB.builders Context d T S & isTBLatticeClosed d T S.
HB.instance Definition _ := isLatticeClosed.Build d T S opredI opredU.
HB.instance Definition _ := isBLatticeClosed.Build d T S opred0.
HB.instance Definition _ := isTLatticeClosed.Build d T S opred1.
HB.end.

(* subtypes *)

HB.factory Record SubPOrder_isSubLattice d (T : latticeType d) S d' U
    & @SubPOrder d T S d' U := {
  opredI_subproof : meet_closed S;
  opredU_subproof : join_closed S;
}.

HB.builders Context d T S d' U & SubPOrder_isSubLattice d T S d' U.

HB.instance Definition _ := isLatticeClosed.Build d T S
  opredI_subproof opredU_subproof.

Let inU v Sv : U := Sub v Sv.
Let meetU (u1 u2 : U) : U := inU (opredI (valP u1) (valP u2)).
Let joinU (u1 u2 : U) : U := inU (opredU (valP u1) (valP u2)).

Fact lexI x y z : (x <= meetU y z) = (x <= y) && (x <= z).
Proof. by rewrite -!le_val !SubK lexI. Qed.
Fact leUx x y z : (joinU x y <= z) = (x <= z) && (y <= z).
Proof. by rewrite -!le_val !SubK leUx. Qed.
HB.instance Definition _ := POrder_MeetJoin_isLattice.Build d' U lexI leUx.

Fact valI : meet_morphism (val : U -> T).
Proof. by move=> x y; rewrite !SubK. Qed.
Fact valU : join_morphism (val : U -> T).
Proof. by move=> x y; rewrite !SubK. Qed.
HB.instance Definition _ := isMeetSubLattice.Build d T S d' U valI.
HB.instance Definition _ := isJoinSubLattice.Build d T S d' U valU.
HB.end.

HB.factory Record SubChoice_isSubLattice d (T : latticeType d) S (d' : disp_t) U
    & SubChoice T S U := {
  opredI_subproof : meet_closed S;
  opredU_subproof : join_closed S;
}.

HB.builders Context d T S d' U & SubChoice_isSubLattice d T S d' U.
HB.instance Definition _ := SubChoice_isSubPOrder.Build d T S d' U.
HB.instance Definition _ := SubPOrder_isSubLattice.Build d T S d' U
  opredI_subproof opredU_subproof.
HB.end.

HB.factory Record SubPOrder_isBSubLattice d (T : bLatticeType d) S d' U
    & @SubPOrder d T S d' U & Lattice d' U := {
  opred0_subproof : \bot \in S;
}.

HB.builders Context d T S d' U & SubPOrder_isBSubLattice d T S d' U.

Let inU v Sv : U := Sub v Sv.
Let zeroU : U := inU opred0_subproof.

Fact le0x x : zeroU <= x. Proof. by rewrite -le_val /= SubK le0x. Qed.
HB.instance Definition _ := hasBottom.Build d' U le0x.

Fact val0 : (val : U -> T) \bot = \bot. Proof. by rewrite SubK. Qed.
#[warning="-HB.no-new-instance"]
HB.instance Definition _ := isBSubLattice.Build d T S d' U val0.
HB.end.

HB.factory Record SubChoice_isBSubLattice
    d (T : bLatticeType d) S (d' : disp_t) U & SubChoice T S U := {
  opredI_subproof : meet_closed S;
  opredU_subproof : join_closed S;
  opred0_subproof : \bot \in S;
}.

HB.builders Context d T S d' U & SubChoice_isBSubLattice d T S d' U.
HB.instance Definition _ := SubChoice_isSubLattice.Build d T S d' U
  opredI_subproof opredU_subproof.
HB.instance Definition _ := SubPOrder_isBSubLattice.Build d T S d' U
  opred0_subproof.
HB.end.

HB.factory Record SubPOrder_isTSubLattice d (T : tLatticeType d) S d' U
    & @SubPOrder d T S d' U & Lattice d' U := {
  opred1_subproof : \top \in S;
}.

HB.builders Context d T S d' U & SubPOrder_isTSubLattice d T S d' U.

Let inU v Sv : U := Sub v Sv.
Let oneU : U := inU opred1_subproof.

Fact lex1 x : x <= oneU. Proof. by rewrite -le_val /= SubK lex1. Qed.
HB.instance Definition _ := hasTop.Build d' U lex1.

Fact val1 : (val : U -> T) \top = \top. Proof. by rewrite SubK. Qed.
#[warning="-HB.no-new-instance"]
HB.instance Definition _ := isTSubLattice.Build d T S d' U val1.
HB.end.

HB.factory Record SubChoice_isTSubLattice
    d (T : tLatticeType d) S (d' : disp_t) U & SubChoice T S U := {
  opredI_subproof : meet_closed S;
  opredU_subproof : join_closed S;
  opred1_subproof : \top \in S;
}.

HB.builders Context d T S d' U & SubChoice_isTSubLattice d T S d' U.
HB.instance Definition _ := SubChoice_isSubLattice.Build d T S d' U
  opredI_subproof opredU_subproof.
HB.instance Definition _ := SubPOrder_isTSubLattice.Build d T S d' U
  opred1_subproof.
HB.end.

#[short(type="tbSubLattice")]
HB.structure Definition TBSubLattice d (T : tbLatticeType d) S d' :=
  { U of @BSubLattice d T S d' U & @TSubLattice d T S d' U}.

#[export]
HB.instance Definition _ (d : disp_t) (T : tbLatticeType d) (S : pred T) d'
    (U : TBSubLattice.type S d') := BLatticeMorphism.on (val : U -> T).

HB.factory Record SubPOrder_isTBSubLattice d (T : tbLatticeType d) S d' U
    & @SubPOrder d T S d' U & Lattice d' U := {
  opred0_subproof : \bot \in S;
  opred1_subproof : \top \in S;
}.

HB.builders Context d T S d' U & SubPOrder_isTBSubLattice d T S d' U.
HB.instance Definition _ := SubPOrder_isBSubLattice.Build d T S d' U
  opred0_subproof.
HB.instance Definition _ := SubPOrder_isTSubLattice.Build d T S d' U
  opred1_subproof.
HB.end.

HB.factory Record SubChoice_isTBSubLattice d (T : tbLatticeType d) S
    (d' : disp_t) U & SubChoice T S U := {
  opredI_subproof : meet_closed S;
  opredU_subproof : join_closed S;
  opred0_subproof : \bot \in S;
  opred1_subproof : \top \in S;
}.

HB.builders Context d T S d' U & SubChoice_isTBSubLattice d T S d' U.
HB.instance Definition _ := SubChoice_isSubLattice.Build d T S d' U
  opredI_subproof opredU_subproof.
HB.instance Definition _ := SubPOrder_isTBSubLattice.Build d T S d' U
  opred0_subproof opred1_subproof.
HB.end.

Module SubOrderExports.

Notation "[ 'SubPOrder_isSubLattice' 'of' U 'by' <: ]" :=
  (SubPOrder_isSubLattice.Build _ _ _ _ U (@opredI _ _ _) (@opredU _ _ _))
  (format "[ 'SubPOrder_isSubLattice'  'of'  U  'by'  <: ]")
  : form_scope.
Notation "[ 'SubPOrder_isSubLattice' 'of' U 'by' <: 'with' disp ]" :=
  (SubPOrder_isSubLattice.Build _ _ _ disp U (@opredI _ _ _) (@opredU _ _ _))
  (format "[ 'SubPOrder_isSubLattice'  'of'  U  'by'  <:  'with'  disp ]")
  : form_scope.
Notation "[ 'SubChoice_isSubLattice' 'of' U 'by' <: ]" :=
  (SubChoice_isSubLattice.Build _ _ _ _ U (@opredI _ _ _) (@opredU _ _ _))
  (format "[ 'SubChoice_isSubLattice'  'of'  U  'by'  <: ]")
    : form_scope.
Notation "[ 'SubChoice_isSubLattice' 'of' U 'by' <: 'with' disp ]" :=
  (SubChoice_isSubLattice.Build _ _ _ disp U (@opredI _ _ _) (@opredU _ _ _))
  (format "[ 'SubChoice_isSubLattice'  'of'  U  'by'  <:  'with'  disp ]")
    : form_scope.
Notation "[ 'SubPOrder_isBSubLattice' 'of' U 'by' <: ]" :=
  (SubPOrder_isBSubLattice.Build _ _ _ _ U (opred0 _))
  (format "[ 'SubPOrder_isBSubLattice'  'of'  U  'by'  <: ]")
  : form_scope.
Notation "[ 'SubPOrder_isBSubLattice' 'of' U 'by' <: 'with' disp ]" :=
  (SubPOrder_isBSubLattice.Build _ _ _ disp U (opred0 _))
  (format "[ 'SubPOrder_isBSubLattice'  'of'  U  'by'  <:  'with'  disp ]")
  : form_scope.
Notation "[ 'SubChoice_isBSubLattice' 'of' U 'by' <: ]" :=
  (SubChoice_isBSubLattice.Build _ _ _ _ U
     (@opredI _ _ _) (@opredU _ _ _) (opred0 _))
  (format "[ 'SubChoice_isBSubLattice'  'of'  U  'by'  <: ]")
  : form_scope.
Notation "[ 'SubChoice_isBSubLattice' 'of' U 'by' <: 'with' disp ]" :=
  (SubChoice_isBSubLattice.Build _ _ _ disp U
     (@opredI _ _ _) (@opredU _ _ _) (opred0 _))
  (format "[ 'SubChoice_isBSubLattice'  'of'  U  'by'  <:  'with'  disp ]")
  : form_scope.
Notation "[ 'SubPOrder_isTSubLattice' 'of' U 'by' <: ]" :=
  (SubPOrder_isTSubLattice.Build _ _ _ _ U (opred1 _))
  (format "[ 'SubPOrder_isTSubLattice'  'of'  U  'by'  <: ]")
  : form_scope.
Notation "[ 'SubPOrder_isTSubLattice' 'of' U 'by' <: 'with' disp ]" :=
  (SubPOrder_isTSubLattice.Build _ _ _ disp U (opred1 _))
  (format "[ 'SubPOrder_isTSubLattice'  'of'  U  'by'  <:  'with'  disp ]")
  : form_scope.
Notation "[ 'SubChoice_isTSubLattice' 'of' U 'by' <: ]" :=
  (SubChoice_isTSubLattice.Build _ _ _ _ U
     (@opredI _ _ _) (@opredU _ _ _) (opred1 _))
  (format "[ 'SubChoice_isTSubLattice'  'of'  U  'by'  <: ]")
  : form_scope.
Notation "[ 'SubChoice_isTSubLattice' 'of' U 'by' <: 'with' disp ]" :=
  (SubChoice_isTSubLattice.Build _ _ _ disp U
     (@opredI _ _ _) (@opredU _ _ _) (opred1 _))
  (format "[ 'SubChoice_isTSubLattice'  'of'  U  'by'  <:  'with'  disp ]")
  : form_scope.
Notation "[ 'SubPOrder_isTBSubLattice' 'of' U 'by' <: ]" :=
  (SubPOrder_isTBSubLattice.Build _ _ _ _ U (opred0 _) (opred1 _))
  (format "[ 'SubPOrder_isTBSubLattice'  'of'  U  'by'  <: ]")
  : form_scope.
Notation "[ 'SubPOrder_isTBSubLattice' 'of' U 'by' <: 'with' disp ]" :=
  (SubPOrder_isTBSubLattice.Build _ _ _ disp U (opred0 _) (opred1 _))
  (format "[ 'SubPOrder_isTBSubLattice'  'of'  U  'by'  <:  'with'  disp ]")
  : form_scope.
Notation "[ 'SubChoice_isTBSubLattice' 'of' U 'by' <: ]" :=
  (SubChoice_isTBSubLattice.Build _ _ _ _ U
     (@opredI _ _ _) (@opredU _ _ _) (opred0 _) (opred1 _))
  (format "[ 'SubChoice_isTBSubLattice'  'of'  U  'by'  <: ]")
  : form_scope.
Notation "[ 'SubChoice_isTBSubLattice' 'of' U 'by' <: 'with' disp ]" :=
  (SubChoice_isTBSubLattice.Build _ _ _ disp U
     (@opredI _ _ _) (@opredU _ _ _) (opred0 _) (opred1 _))
  (format "[ 'SubChoice_isTBSubLattice'  'of'  U  'by'  <:  'with'  disp ]")
  : form_scope.

End SubOrderExports.
HB.export SubOrderExports.

Module Syntax.
Export Order.Syntax.
Export DualSyntax.
Export LatticeSyntax.
Export BLatticeSyntax.
Export TLatticeSyntax.
End Syntax.

Module Theory.
Export Order.Theory.
Export MeetTheory.
Export BMeetTheory.
Export TMeetTheory.
Export JoinTheory.
Export BJoinTheory.
Export TJoinTheory.
Export LatticeTheory.
Export DistrLatticeTheory.
Export BDistrLatticeTheory.
Export TDistrLatticeTheory.
Export DualOrder. (* FIXME? *)

Export LatticeMorphismTheory.
Export BLatticeMorphismTheory.
Export TLatticeMorphismTheory.

Export ClosedPredicates.
Export LatticePred.

End Theory.

Module Exports.
HB.reexport.
End Exports.
End Order.

Export Order.Exports.

Export Order.Syntax.

Export Order.MeetSemilattice.Exports.
Export Order.BMeetSemilattice.Exports.
Export Order.TMeetSemilattice.Exports.
Export Order.TBMeetSemilattice.Exports.
Export Order.JoinSemilattice.Exports.
Export Order.BJoinSemilattice.Exports.
Export Order.TJoinSemilattice.Exports.
Export Order.TBJoinSemilattice.Exports.
Export Order.Lattice.Exports.
Export Order.BLattice.Exports.
Export Order.TLattice.Exports.
Export Order.TBLattice.Exports.
Export Order.DistrLattice.Exports.
Export Order.BDistrLattice.Exports.
Export Order.TDistrLattice.Exports.
Export Order.TBDistrLattice.Exports.
Export Order.FinMeetSemilattice.Exports.
Export Order.FinBMeetSemilattice.Exports.
Export Order.FinJoinSemilattice.Exports.
Export Order.FinTJoinSemilattice.Exports.
Export Order.FinLattice.Exports.
Export Order.FinTBLattice.Exports.
Export Order.FinDistrLattice.Exports.
Export Order.FinTBDistrLattice.Exports.

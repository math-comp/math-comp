(* (c) Copyright 2006-2019 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice seq.
From mathcomp Require Import path fintype tuple bigop finset div prime finfun.
From mathcomp Require Import finset.

(******************************************************************************)
(*                   Types equipped with order relations                      *)
(*                                                                            *)
(* NB: See CONTRIBUTING.md for an introduction to HB concepts and commands.   *)
(*                                                                            *)
(* This file and order.v define types equipped with order relations.          *)
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
(* Alternative notation displays can be defined by :                          *)
(* 1. declaring a new opaque definition of type unit. Using the idiom         *)
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
(* * Interfaces                                                               *)
(* We provide the following interfaces for types equipped with an order:      *)
(*                                                                            *)
(*            preorderType d == the type of preordered types                  *)
(*                              The HB class is called Preorder.              *)
(*           bPreorderType d == preorderType with a bottom element (\bot)     *)
(*                              The HB class is called BPreorder.             *)
(*           tPreorderType d == preorderType with a top element (\top)        *)
(*                              The HB class is called TPreorder.             *)
(*          tbPreorderType d == preorderType with both a top and a bottom     *)
(*                              The HB class is called TBPreorder.            *)
(*         finPreorderType d == the type of partially preordered finite types *)
(*                              The HB class is called FinPreorder.           *)
(*        finBPreorderType d == finPreorderType with a bottom element         *)
(*                              The HB class is called FinBPreorder.          *)
(*        finTPreorderType d == finPreorderType with a top element            *)
(*                              The HB class is called FinTPreorder.          *)
(*       finTBPreorderType d == finPreorderType with both a top and a bottom  *)
(*                              The HB class is called FinTBPreorder.         *)
(*                                                                            *)
(* and their joins with subType:                                              *)
(*                                                                            *)
(*          subPreorder d T P d' == join of preorderType d' and subType       *)
(*                                (P : pred T) such that val is monotonic     *)
(*                                The HB class is called SubPreorder.         *)
(*                                                                            *)
(* Morphisms between the above structures:                                    *)
(*                                                                            *)
(* OrderMorphism.type d T d' T' == nondecreasing function between the two     *)
(*                                 preorder                                   *)
(*                              := {omorphism T -> T'}                        *)
(*                                                                            *)
(* TODO: Check this section * Useful lemmas:                                  *)
(* On orderType, leP, ltP, and ltgtP are the three main lemmas for case       *)
(* analysis.                                                                  *)
(* On porderType, one may use comparableP, comparable_leP, comparable_ltP,    *)
(* and comparable_ltgtP, which are the four main lemmas for case analysis.    *)
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
(* For T of type preorderType d, x and y of type T, and C of type bool:       *)
(*          x <= y :=  @Order.le d T x y                                      *)
(*                 <-> x is less than or equal to y.                          *)
(*           x < y :=  @Order.lt d T x y                                      *)
(*                 <-> x is less than y, i.e., (y != x) && (x <= y).          *)
(*          x >= y :=  y <= x                                                 *)
(*                 <-> x is greater than or equal to y.                       *)
(*           x > y :=  y < x                                                  *)
(*                 <-> x is greater than y.                                   *)
(*         x >=< y :=  @Order.comparable d T x y  (:= (x <= y) || (y <= x))   *)
(*                 <-> x and y are comparable.                                *)
(*          x >< y :=  ~~ x >=< y                                             *)
(*                 <-> x and y are incomparable.                              *)
(* x <= y ?= iff C :=  @Order.leif d T x y C  (:= (x <= y) * ((x == y) = C))  *)
(*                 <-> x is less than y, or equal iff C is true.              *)
(*  x < y ?<= if C :=  @Order.lteif d T x y C (:= if C then x <= y else x < y)*)
(*                 <-> x is smaller than y, and strictly if C is false.       *)
(*   Order.min x y :=  if x < y then x else y                                 *)
(*   Order.max x y :=  if x < y then y else x                                 *)
(*        f \min g ==  the function x |-> Order.min (f x) (g x);              *)
(*                     f \min g simplifies on application.                    *)
(*        f \max g ==  the function x |-> Order.max (f x) (g x);              *)
(*                     f \max g simplifies on application.                    *)
(* nondecreasing f <-> the function f : T -> T' is nondecreasing,             *)
(*                     where T and T' are porderType                          *)
(*                 :=  {homo f : x y / x <= y}                                *)
(* Unary (partially applied) versions of order notations:                     *)
(*            >= y :=  @Order.le d T y                                        *)
(*                 ==  a predicate characterizing elements greater than or    *)
(*                     equal to y                                             *)
(*             > y :=  @Order.lt d T y                                        *)
(*            <= y :=  @Order.ge d T y                                        *)
(*             < y :=  @Order.gt d T y                                        *)
(*           >=< y :=  [pred x | @Order.comparable d T x y]                   *)
(*            >< y :=  [pred x | ~~ @Order.comparable d T x y]                *)
(* 0-ary versions of order notations (in function_scope):                     *)
(*            <=%O :=  @Order.le         d T                                  *)
(*             <%O :=  @Order.lt         d T                                  *)
(*            >=%O :=  @Order.ge         d T                                  *)
(*             >%O :=  @Order.gt         d T                                  *)
(*           >=<%O :=  @Order.comparable d T                                  *)
(*           <?=%O :=  @Order.leif       d T                                  *)
(*          <?<=%O :=  @Order.lteif      d T                                  *)
(* -> These conventions are compatible with Haskell's,                        *)
(*    where ((< y) x) = (x < y) = ((<) x y),                                  *)
(*    except that we write <%O instead of (<).                                *)
(*                                                                            *)
(* For T of type bPreorderType d:                                             *)
(*            \bot :=  @Order.bottom d T                                      *)
(*                 ==  the bottom element of type T                           *)
(* For T of type tPreorderType d:                                             *)
(*            \top :=  @Order.top d T                                         *)
(*                 ==  the top element of type T                              *)
(*                                                                            *)
(* For preorderType we provide the following operations:                      *)
(*   [arg min_(i < i0 | P) M] == a value i : T minimizing M : R, subject to   *)
(*                      the condition P (i may appear in P and M), and        *)
(*                      provided P holds for i0.                              *)
(*   [arg max_(i > i0 | P) M] == a value i maximizing M subject to P and      *)
(*                      provided P holds for i0.                              *)
(*   [arg min_(i < i0 in A) M] == an i \in A minimizing M if i0 \in A.        *)
(*   [arg max_(i > i0 in A) M] == an i \in A maximizing M if i0 \in A.        *)
(*   [arg min_(i < i0) M] == an i : T minimizing M, given i0 : T.             *)
(*   [arg max_(i > i0) M] == an i : T maximizing M, given i0 : T.             *)
(* with head symbols Order.arg_min and Order.arg_max                          *)
(* The user may use extremumP or extremum_inP to eliminate them.              *)
(*                                                                            *)
(* -> patterns for contextual rewriting:                                      *)
(*      leLHS := (X in (X <= _)%O)%pattern                                    *)
(*      leRHS := (X in (_ <= X)%O)%pattern                                    *)
(*      ltLHS := (X in (X < _)%O)%pattern                                     *)
(*      ltRHS := (X in (_ < X)%O)%pattern                                     *)
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
(* The following notations are provided to build substructures:               *)
(* [SubChoice_isSubPreorder of U by <: with disp] ==                          *)
(* [SubChoice_isSubPreorder of U by <:] == preorderType mixin for a subType   *)
(*                          whose base type is a preorderType                 *)
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
(* We also provide specialized versions of some theorems from path.v.         *)
(*                                                                            *)
(* We provide Order.enum_val, Order.enum_rank, and Order.enum_rank_in, which  *)
(* are monotonic variations of enum_val, enum_rank, and enum_rank_in          *)
(* whenever the type is porderType, and their monotonicity is provided if     *)
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
(* Acknowledgments: This file is based on prior work by D. Dreyer, G.         *)
(* Gonthier, A. Nanevski, P-Y Strub, B. Ziliani                               *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope order_scope.

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
Reserved Notation ">=< y" (at level 35).
Reserved Notation ">=< y :> T" (at level 35, y at next level).
Reserved Notation "x >< y" (at level 70, no associativity).
Reserved Notation ">< x" (at level 35).
Reserved Notation ">< y :> T" (at level 35, y at next level).
Reserved Notation "f \min g" (at level 50, left associativity).
Reserved Notation "f \max g" (at level 50, left associativity).

Reserved Notation "x < y ?<= 'if' c" (at level 70, y, c at next level,
  format "x '[hv'  <  y '/'  ?<=  'if'  c ']'").
Reserved Notation "x < y ?<= 'if' c :> T" (at level 70, y, c at next level,
  format "x '[hv'  <  y '/'  ?<=  'if'  c  :> T ']'").

(* Reserved notations for bottom/top elements *)
Reserved Notation "\bot" (at level 0).
Reserved Notation "\top" (at level 0).

(* Reserved notations for dual order *)
Reserved Notation "x <=^d y" (at level 70, y at next level).
Reserved Notation "x >=^d y" (at level 70, y at next level).
Reserved Notation "x <^d y" (at level 70, y at next level).
Reserved Notation "x >^d y" (at level 70, y at next level).
Reserved Notation "x <=^d y :> T" (at level 70, y at next level).
Reserved Notation "x >=^d y :> T" (at level 70, y at next level).
Reserved Notation "x <^d y :> T" (at level 70, y at next level).
Reserved Notation "x >^d y :> T" (at level 70, y at next level).
Reserved Notation "<=^d y" (at level 35).
Reserved Notation ">=^d y" (at level 35).
Reserved Notation "<^d y" (at level 35).
Reserved Notation ">^d y" (at level 35).
Reserved Notation "<=^d y :> T" (at level 35, y at next level).
Reserved Notation ">=^d y :> T" (at level 35, y at next level).
Reserved Notation "<^d y :> T" (at level 35, y at next level).
Reserved Notation ">^d y :> T" (at level 35, y at next level).
Reserved Notation "x >=<^d y" (at level 70, no associativity).
Reserved Notation ">=<^d y" (at level 35).
Reserved Notation ">=<^d y :> T" (at level 35, y at next level).
Reserved Notation "x ><^d y" (at level 70, no associativity).
Reserved Notation "><^d x" (at level 35).
Reserved Notation "><^d y :> T" (at level 35, y at next level).

Reserved Notation "x <=^d y <=^d z" (at level 70, y, z at next level).
Reserved Notation "x <^d y <=^d z" (at level 70, y, z at next level).
Reserved Notation "x <=^d y <^d z" (at level 70, y, z at next level).
Reserved Notation "x <^d y <^d z" (at level 70, y, z at next level).
Reserved Notation "x <=^d y ?= 'iff' c" (at level 70, y, c at next level,
  format "x '[hv'  <=^d  y '/'  ?=  'iff'  c ']'").
Reserved Notation "x <=^d y ?= 'iff' c :> T" (at level 70, y, c at next level,
  format "x '[hv'  <=^d  y '/'  ?=  'iff'  c  :> T ']'").
Reserved Notation "x <^d y ?<= 'if' c" (at level 70, y, c at next level,
  format "x '[hv'  <^d  y '/'  ?<=  'if'  c ']'").
Reserved Notation "x <^d y ?<= 'if' c :> T" (at level 70, y, c at next level,
  format "x '[hv'  <^d  y '/'  ?<=  'if'  c  :> T ']'").

Reserved Notation "\bot^d" (at level 0).
Reserved Notation "\top^d" (at level 0).

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

Reserved Notation "\bot^p" (at level 0).
Reserved Notation "\top^p" (at level 0).

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

Reserved Notation "\bot^sp" (at level 0).
Reserved Notation "\top^sp" (at level 0).

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

Reserved Notation "\bot^l" (at level 0).
Reserved Notation "\top^l" (at level 0).

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

Reserved Notation "\bot^sl" (at level 0).
Reserved Notation "\top^sl" (at level 0).

(* Reserved notations for divisibility *)
Reserved Notation "x %<| y"  (at level 70, no associativity).

Reserved Notation "\min_ i F"
  (at level 41, F at level 41, i at level 0,
           format "'[' \min_ i '/  '  F ']'").
Reserved Notation "\min_ ( i <- r | P ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \min_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\min_ ( i <- r ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \min_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\min_ ( m <= i < n | P ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \min_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\min_ ( m <= i < n ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \min_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\min_ ( i | P ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \min_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\min_ ( i : t | P ) F"
  (at level 41, F at level 41, i at level 50).
Reserved Notation "\min_ ( i : t ) F"
  (at level 41, F at level 41, i at level 50).
Reserved Notation "\min_ ( i < n | P ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \min_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\min_ ( i < n ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \min_ ( i  <  n )  F ']'").
Reserved Notation "\min_ ( i 'in' A | P ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \min_ ( i  'in'  A  |  P ) '/  '  F ']'").
Reserved Notation "\min_ ( i 'in' A ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \min_ ( i  'in'  A ) '/  '  F ']'").

Reserved Notation "\max_ i F"
  (at level 41, F at level 41, i at level 0,
           format "'[' \max_ i '/  '  F ']'").
Reserved Notation "\max_ ( i <- r | P ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \max_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\max_ ( i <- r ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \max_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\max_ ( m <= i < n | P ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \max_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\max_ ( m <= i < n ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \max_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\max_ ( i | P ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \max_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\max_ ( i : t | P ) F"
  (at level 41, F at level 41, i at level 50).
Reserved Notation "\max_ ( i : t ) F"
  (at level 41, F at level 41, i at level 50).
Reserved Notation "\max_ ( i < n | P ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \max_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\max_ ( i < n ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \max_ ( i  <  n )  F ']'").
Reserved Notation "\max_ ( i 'in' A | P ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \max_ ( i  'in'  A  |  P ) '/  '  F ']'").
Reserved Notation "\max_ ( i 'in' A ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \max_ ( i  'in'  A ) '/  '  F ']'").

Reserved Notation "\min^d_ i F"
  (at level 41, F at level 41, i at level 0,
           format "'[' \min^d_ i '/  '  F ']'").
Reserved Notation "\min^d_ ( i <- r | P ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \min^d_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\min^d_ ( i <- r ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \min^d_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\min^d_ ( m <= i < n | P ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \min^d_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\min^d_ ( m <= i < n ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \min^d_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\min^d_ ( i | P ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \min^d_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\min^d_ ( i : t | P ) F"
  (at level 41, F at level 41, i at level 50).
Reserved Notation "\min^d_ ( i : t ) F"
  (at level 41, F at level 41, i at level 50).
Reserved Notation "\min^d_ ( i < n | P ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \min^d_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\min^d_ ( i < n ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \min^d_ ( i  <  n )  F ']'").
Reserved Notation "\min^d_ ( i 'in' A | P ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \min^d_ ( i  'in'  A  |  P ) '/  '  F ']'").
Reserved Notation "\min^d_ ( i 'in' A ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \min^d_ ( i  'in'  A ) '/  '  F ']'").

Reserved Notation "\max^d_ i F"
  (at level 41, F at level 41, i at level 0,
           format "'[' \max^d_ i '/  '  F ']'").
Reserved Notation "\max^d_ ( i <- r | P ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \max^d_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\max^d_ ( i <- r ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \max^d_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\max^d_ ( m <= i < n | P ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \max^d_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\max^d_ ( m <= i < n ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \max^d_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\max^d_ ( i | P ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \max^d_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\max^d_ ( i : t | P ) F"
  (at level 41, F at level 41, i at level 50).
Reserved Notation "\max^d_ ( i : t ) F"
  (at level 41, F at level 41, i at level 50).
Reserved Notation "\max^d_ ( i < n | P ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \max^d_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\max^d_ ( i < n ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \max^d_ ( i  <  n )  F ']'").
Reserved Notation "\max^d_ ( i 'in' A | P ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \max^d_ ( i  'in'  A  |  P ) '/  '  F ']'").
Reserved Notation "\max^d_ ( i 'in' A ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \max^d_ ( i  'in'  A ) '/  '  F ']'").

Reserved Notation "'{' 'omorphism' U '->' V '}'"
  (at level 0, U at level 98, V at level 99,
   format "{ 'omorphism'  U  ->  V }").

Module Order.

#[projections(primitive)] Record disp_t := Disp {d1 : unit; d2 : unit}.

#[key="T", primitive]
HB.mixin Record isDuallyPreorder (d : disp_t) T of Equality T := {
  le       : rel T;
  lt       : rel T;
  lt_def   : forall x y, lt x y = (le x y) && ~~ (le y x);
  gt_def   : forall x y, lt y x = (le y x) && ~~ (le x y);
  le_refl  : reflexive     le;
  ge_refl  : reflexive     (fun x y => le y x);
  le_trans : transitive    le;
  ge_trans : transitive    (fun x y => le y x);
}.

#[short(type="preorderType")]
HB.structure Definition Preorder (d : disp_t) :=
  { T of Choice T & isDuallyPreorder d T }.

#[key="T", primitive]
HB.mixin Record hasBottom d T of Preorder d T := {
  bottom : T;
  le0x : forall x, le bottom x;
}.

#[key="T", primitive]
HB.mixin Record hasTop d T of Preorder d T := {
  top : T;
  lex1 : forall x, le x top;
}.

#[short(type="bPreorderType")]
HB.structure Definition BPreorder d := { T of hasBottom d T & Preorder d T }.
#[short(type="tPreorderType")]
HB.structure Definition TPreorder d := { T of hasTop d T & Preorder d T }.
#[short(type="tbPreorderType")]
HB.structure Definition TBPreorder d := { T of hasTop d T & BPreorder d T }.

Section PreorderDef.

Variable (disp : disp_t) (T : preorderType disp).

Local Notation "x <= y" := (le x y) : order_scope.
Local Notation "x < y" := (lt x y) : order_scope.

Definition comparable : rel T := fun (x y : T) => (x <= y) || (y <= x).
Local Notation "x >=< y" := (comparable x y) : order_scope.
Local Notation "x >< y" := (~~ (x >=< y)) : order_scope.

Definition ge : simpl_rel T := [rel x y | y <= x].
Definition gt : simpl_rel T := [rel x y | y < x].
Definition leif (x y : T) C : Prop := ((x <= y) * ((x == y) = C))%type.

Definition le_of_leif x y C (le_xy : @leif x y C) := le_xy.1 : le x y.

Definition lteif (x y : T) C := if C then x <= y else x < y.

Variant le_xor_gt (x y : T) :
  T -> T -> T -> T -> bool -> bool -> Set :=
  | LeNotGt of x <= y : le_xor_gt x y x x y y true false
  | GtNotLe of y < x  : le_xor_gt x y y y x x false true.

Variant lt_xor_ge (x y : T) :
  T -> T -> T -> T -> bool -> bool -> Set :=
  | LtNotGe of x < y  : lt_xor_ge x y x x y y false true
  | GeNotLt of y <= x : lt_xor_ge x y y y x x true false.

Definition min (x y : T) := if x < y then x else y.
Definition max (x y : T) := if x < y then y else x.

Variant compare (x y : T) :
   T -> T -> T -> T ->
   bool -> bool -> bool -> bool -> bool -> bool -> Set :=
  | CompareLt of x < y : compare x y
    x x y y false false false true false true
  | CompareGt of y < x : compare x y
    y y x x false false true false true false
  | CompareEq of x = y : compare x y
    x x x x true true true true false false.

Variant incompare (x y : T) :
   T -> T -> T -> T ->
  bool -> bool -> bool -> bool -> bool -> bool -> bool -> bool -> Set :=
  | InCompareLt of x < y : incompare x y
    x x y y false false false true false true true true
  | InCompareGt of y < x : incompare x y
    y y x x false false true false true false true true
  | InCompare of x >< y  : incompare x y
    x y y x false false false false false false false false
  | InCompareEq of x = y : incompare x y
    x x x x true true true true false false true true.

Definition arg_min {I : finType} := @extremum T I le.
Definition arg_max {I : finType} := @extremum T I ge.

(* Lifted min/max operations. *)
Section LiftedPreorder.
Variable T' : Type.
Implicit Type f : T' -> T.
Definition min_fun f g x := min (f x) (g x).
Definition max_fun f g x := max (f x) (g x).
End LiftedPreorder.

Definition nondecreasing disp' (T' : preorderType disp') (f : T -> T') : Prop :=
  {homo f : x y / x <= y}.

End PreorderDef.

Prenex Implicits lt le leif lteif.
Arguments ge {_ _}.
Arguments gt {_ _}.
Arguments min {_ _}.
Arguments max {_ _}.
Arguments comparable {_ _}.
Arguments min_fun {_ _ _} f g _ /.
Arguments max_fun {_ _ _} f g _ /.

Module Import Def.

Notation nondecreasing := nondecreasing.
Notation min := min.
Notation max := max.

End Def.

Module Import PreOSyntax.

Notation "<=%O" := le : function_scope.
Notation ">=%O" := ge : function_scope.
Notation "<%O" := lt : function_scope.
Notation ">%O" := gt : function_scope.
Notation "<?=%O" := leif : function_scope.
Notation "<?<=%O" := lteif : function_scope.
Notation ">=<%O" := comparable : function_scope.
Notation "><%O" := (fun x y => ~~ (comparable x y)) : function_scope.

Notation "<= y" := (ge y) : order_scope.
Notation "<= y :> T" := (<= (y : T)) (only parsing) : order_scope.
Notation ">= y"  := (le y) : order_scope.
Notation ">= y :> T" := (>= (y : T)) (only parsing) : order_scope.

Notation "< y" := (gt y) : order_scope.
Notation "< y :> T" := (< (y : T)) (only parsing) : order_scope.
Notation "> y" := (lt y) : order_scope.
Notation "> y :> T" := (> (y : T)) (only parsing) : order_scope.

Notation "x <= y" := (le x y) : order_scope.
Notation "x <= y :> T" := ((x : T) <= (y : T)) (only parsing) : order_scope.
Notation "x >= y" := (y <= x) (only parsing) : order_scope.
Notation "x >= y :> T" := ((x : T) >= (y : T)) (only parsing) : order_scope.

Notation "x < y"  := (lt x y) : order_scope.
Notation "x < y :> T" := ((x : T) < (y : T)) (only parsing) : order_scope.
Notation "x > y"  := (y < x) (only parsing) : order_scope.
Notation "x > y :> T" := ((x : T) > (y : T)) (only parsing) : order_scope.

Notation "x <= y <= z" := ((x <= y) && (y <= z)) : order_scope.
Notation "x < y <= z" := ((x < y) && (y <= z)) : order_scope.
Notation "x <= y < z" := ((x <= y) && (y < z)) : order_scope.
Notation "x < y < z" := ((x < y) && (y < z)) : order_scope.

Notation "x <= y ?= 'iff' C" := (leif x y C) : order_scope.
Notation "x <= y ?= 'iff' C :> T" := ((x : T) <= (y : T) ?= iff C)
  (only parsing) : order_scope.

Notation "x < y ?<= 'if' C" := (lteif x y C) : order_scope.
Notation "x < y ?<= 'if' C :> T" := ((x : T) < (y : T) ?<= if C)
  (only parsing) : order_scope.

Notation ">=< y" := [pred x | comparable x y] : order_scope.
Notation ">=< y :> T" := (>=< (y : T)) (only parsing) : order_scope.
Notation "x >=< y" := (comparable x y) : order_scope.

Notation ">< y" := [pred x | ~~ comparable x y] : order_scope.
Notation ">< y :> T" := (>< (y : T)) (only parsing) : order_scope.
Notation "x >< y" := (~~ (comparable x y)) : order_scope.

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
   format "[ 'arg'  'max_' ( i  >  i0 )  F ]") : order_scope.

Notation "f \min g" := (min_fun f g) : function_scope.
Notation "f \max g" := (max_fun f g) : function_scope.

Notation leLHS := (X in (X <= _)%O)%pattern.
Notation leRHS := (X in (_ <= X)%O)%pattern.
Notation ltLHS := (X in (X < _)%O)%pattern.
Notation ltRHS := (X in (_ < X)%O)%pattern.

Notation "\bot" := bottom : order_scope.
Notation "\top" := top : order_scope.

End PreOSyntax.
HB.export PreOSyntax.

Module PreOCoercions.
Coercion le_of_leif : leif >-> is_true.
End PreOCoercions.
HB.export PreOCoercions.

(**********)
(* FINITE *)
(**********)

#[short(type="finPreorderType")]
HB.structure Definition FinPreorder d := { T of Finite T & Preorder d T }.

#[short(type="finBPreorderType")]
HB.structure Definition FinBPreorder d := { T of FinPreorder d T & hasBottom d T }.

#[short(type="finTPreorderType")]
HB.structure Definition FinTPreorder d := { T of FinPreorder d T & hasTop d T }.

#[short(type="finTBPreorderType")]
HB.structure Definition FinTBPreorder d := { T of FinBPreorder d T & hasTop d T }.

(********)
(* DUAL *)
(********)

Definition dual T : Type := T.
Definition dual_display (d : disp_t) := {| d1 := d2 d; d2 := d1 d |}.

Notation dual_le := (@le (dual_display _) _).
Notation dual_lt := (@lt (dual_display _) _).
Notation dual_comparable := (@comparable (dual_display _) _).
Notation dual_ge := (@ge (dual_display _) _).
Notation dual_gt := (@gt (dual_display _) _).
Notation dual_leif := (@leif (dual_display _) _).
Notation dual_lteif := (@lteif (dual_display _) _).
Notation dual_max := (@max (dual_display _) _).
Notation dual_min := (@min (dual_display _) _).
Notation dual_bottom := (@bottom (dual_display _) _).
Notation dual_top := (@top (dual_display _) _).

Module Import DualSyntax.

Notation "T ^d" := (dual T) (at level 2, format "T ^d") : type_scope.
Notation "<=^d%O" := dual_le : function_scope.
Notation ">=^d%O" := dual_ge : function_scope.
Notation "<^d%O" := dual_lt : function_scope.
Notation ">^d%O" := dual_gt : function_scope.
Notation "<?=^d%O" := dual_leif : function_scope.
Notation "<?<=^d%O" := dual_lteif : function_scope.
Notation ">=<^d%O" := dual_comparable : function_scope.
Notation "><^d%O" := (fun x y => ~~ dual_comparable x y) : function_scope.

Notation "<=^d y" := (>=^d%O y) : order_scope.
Notation "<=^d y :> T" := (<=^d (y : T)) (only parsing) : order_scope.
Notation ">=^d y" := (<=^d%O y) : order_scope.
Notation ">=^d y :> T" := (>=^d (y : T)) (only parsing) : order_scope.

Notation "<^d y" := (>^d%O y) : order_scope.
Notation "<^d y :> T" := (<^d (y : T)) (only parsing) : order_scope.
Notation ">^d y" := (<^d%O y) : order_scope.
Notation ">^d y :> T" := (>^d (y : T)) (only parsing) : order_scope.

Notation "x <=^d y" := (<=^d%O x y) : order_scope.
Notation "x <=^d y :> T" := ((x : T) <=^d (y : T)) (only parsing) : order_scope.
Notation "x >=^d y" := (y <=^d x) (only parsing) : order_scope.
Notation "x >=^d y :> T" := ((x : T) >=^d (y : T)) (only parsing) : order_scope.

Notation "x <^d y" := (<^d%O x y) : order_scope.
Notation "x <^d y :> T" := ((x : T) <^d (y : T)) (only parsing) : order_scope.
Notation "x >^d y" := (y <^d x) (only parsing) : order_scope.
Notation "x >^d y :> T" := ((x : T) >^d (y : T)) (only parsing) : order_scope.

Notation "x <=^d y <=^d z" := ((x <=^d y) && (y <=^d z)) : order_scope.
Notation "x <^d y <=^d z" := ((x <^d y) && (y <=^d z)) : order_scope.
Notation "x <=^d y <^d z" := ((x <=^d y) && (y <^d z)) : order_scope.
Notation "x <^d y <^d z" := ((x <^d y) && (y <^d z)) : order_scope.

Notation "x <=^d y ?= 'iff' C" := (<?=^d%O x y C) : order_scope.
Notation "x <=^d y ?= 'iff' C :> T" := ((x : T) <=^d (y : T) ?= iff C)
  (only parsing) : order_scope.

Notation "x <^d y ?<= 'if' C" := (<?<=^d%O x y C) : order_scope.
Notation "x <^d y ?<= 'if' C :> T" := ((x : T) <^d (y : T) ?<= if C)
  (only parsing) : order_scope.

Notation ">=<^d x" := (>=<^d%O x) : order_scope.
Notation ">=<^d y :> T" := (>=<^d (y : T)) (only parsing) : order_scope.
Notation "x >=<^d y" := (>=<^d%O x y) : order_scope.

Notation "><^d y" := [pred x | ~~ dual_comparable x y] : order_scope.
Notation "><^d y :> T" := (><^d (y : T)) (only parsing) : order_scope.
Notation "x ><^d y" := (~~ (><^d%O x y)) : order_scope.

Notation "\bot^d" := dual_bottom : order_scope.
Notation "\top^d" := dual_top : order_scope.

End DualSyntax.

Module DualPreorder.

HB.instance Definition _ (T : eqType) := Equality.on T^d.
HB.instance Definition _ (T : choiceType) := Choice.on T^d.
HB.instance Definition _ (T : countType) := Countable.on T^d.
HB.instance Definition _ (T : finType) := Finite.on T^d.

HB.instance Definition _ (d : disp_t) (T : preorderType d) :=
  isDuallyPreorder.Build (dual_display d) T^d
    gt_def lt_def ge_refl le_refl ge_trans le_trans.

Lemma leEdual (d : disp_t) (T : preorderType d) (x y : T) :
  (x <=^d y :> T^d) = (y <= x).
Proof. by []. Qed.
Lemma ltEdual (d : disp_t) (T : preorderType d) (x y : T) :
  (x <^d y :> T^d) = (y < x).
Proof. by []. Qed.

HB.instance Definition _ d (T : tPreorderType d) :=
  hasBottom.Build (dual_display d) T^d lex1.

Lemma botEdual d (T : tPreorderType d) : (dual_bottom : T^d) = \top :> T.
Proof. by []. Qed.

HB.instance Definition _ d (T : bPreorderType d) :=
  hasTop.Build (dual_display d) T^d le0x.

Lemma topEdual d (T : bPreorderType d) : (dual_top : T^d) = \bot :> T.
Proof. by []. Qed.

End DualPreorder.
HB.export DualPreorder.

(**********)
(* THEORY *)
(**********)

Module Import PreorderTheory.
Section PreorderTheory.

Context {disp : disp_t} {T : preorderType disp}.

Implicit Types (x y : T) (s : seq T).

Definition nondecreasing disp' (T' : preorderType disp') (f : T -> T') : Prop :=
  {homo f : x y / x <= y}.

Lemma geE x y : ge x y = (y <= x). Proof. by []. Qed.
Lemma gtE x y : gt x y = (y < x). Proof. by []. Qed.

Lemma lexx (x : T) : x <= x.
Proof. exact: le_refl. Qed.
Hint Resolve lexx : core.

Definition le_refl : reflexive le := lexx.
Definition ge_refl : reflexive ge := lexx.
Hint Resolve le_refl : core.

Lemma le_trans: transitive (<=%O : rel T).
Proof. exact: le_trans. Qed.

Lemma ge_trans: transitive (>=%O : rel T).
Proof. by move=> ? ? ? ? /le_trans; apply. Qed.

Lemma le_le_trans x y z t : z <= x -> y <= t -> x <= y -> z <= t.
Proof. by move=> + /(le_trans _)/[apply]; apply: le_trans. Qed.

Lemma lt_le_def x y: (x < y) = (x <= y) && ~~ (y <= x).
Proof. exact: lt_def. Qed.

Lemma ltxx x: x < x = false.
Proof. by rewrite lt_le_def andbN. Qed.

Definition lt_irreflexive : irreflexive lt := ltxx.
Hint Resolve lt_irreflexive : core.

Definition ltexx := (lexx, ltxx).

Lemma lt_eqF x y: x < y -> x == y = false.
Proof. by apply: contraTF => /eqP ->; rewrite ltxx. Qed.

Lemma gt_eqF x y : y < x -> x == y = false.
Proof. by move=> /lt_eqF; rewrite eq_sym. Qed.

Lemma ltW x y: x < y -> x <= y.
Proof. by rewrite lt_le_def => /andP[]. Qed.

Lemma lt_le_trans y x z: x < y -> y <= z -> x < z.
Proof.
rewrite !lt_le_def => /andP[] xy /negP yx yz.
apply/andP; split; first exact/(le_trans xy).
by apply/negP => /(le_trans yz).
Qed.

Lemma lt_trans: transitive (<%O : rel T).
Proof. by move=> y x z le1 /ltW le2; apply/(@lt_le_trans y). Qed.

Lemma le_lt_trans y x z: x <= y -> y < z -> x < z.
Proof.
rewrite !lt_le_def => xy /andP[] yz /negP zy.
apply/andP; split; first exact/(le_trans xy).
by apply/negP => /(fun zx => le_trans zx xy).
Qed.

Lemma lt_nsym x y : x < y -> y < x -> False.
Proof. by move=> xy /(lt_trans xy); rewrite ltxx. Qed.

Lemma lt_asym x y : x < y < x = false.
Proof. by apply/negP => /andP []; apply: lt_nsym. Qed.

Lemma le_gtF x y: x <= y -> y < x = false.
Proof.
by move=> le_xy; apply/negP => /lt_le_trans /(_ le_xy); rewrite ltxx.
Qed.

Lemma lt_geF x y : x < y -> y <= x = false.
Proof. by apply: contraTF => /le_gtF ->. Qed.

Definition lt_gtF x y hxy := le_gtF (@ltW x y hxy).

Lemma lt_leAnge x y : (x < y) = (x <= y) && ~~ (y <= x).
Proof. exact: lt_le_def. Qed.

Lemma lt_le_asym x y : x < y <= x = false.
Proof. by apply/negP; move=> /andP[] xy /(lt_le_trans xy); rewrite ltxx. Qed.

Lemma le_lt_asym x y : x <= y < x = false.
Proof. by rewrite andbC lt_le_asym. Qed.

Lemma le_path_min x s : path <=%O x s -> all (>= x) s.
Proof. exact/order_path_min/le_trans. Qed.

Lemma lt_path_min x s : path <%O x s -> all (> x) s.
Proof. exact/order_path_min/lt_trans. Qed.

Lemma le_path_sortedE x s : path <=%O x s = all (>= x) s && sorted <=%O s.
Proof. exact/path_sortedE/le_trans. Qed.

Lemma lt_path_sortedE x s : path <%O x s = all (> x) s && sorted <%O s.
Proof. exact/path_sortedE/lt_trans. Qed.

Lemma le_sorted_pairwise s : sorted <=%O s = pairwise <=%O s.
Proof. exact/sorted_pairwise/le_trans. Qed.

Lemma lt_sorted_pairwise s : sorted <%O s = pairwise <%O s.
Proof. exact/sorted_pairwise/lt_trans. Qed.

Lemma le_path_pairwise x s : path <=%O x s = pairwise <=%O (x :: s).
Proof. exact/path_pairwise/le_trans. Qed.

Lemma lt_path_pairwise x s : path <%O x s = pairwise <%O (x :: s).
Proof. exact/path_pairwise/lt_trans. Qed.

Lemma lt_sorted_is_uniq_le s : sorted <%O s -> uniq s && sorted <=%O s.
Proof.
rewrite le_sorted_pairwise lt_sorted_pairwise uniq_pairwise -pairwise_relI.
apply/sub_pairwise => x y/= /[dup] + /ltW ->.
by case: eqVneq => // ->; rewrite ltxx.
Qed.

Lemma le_sorted_mask m s : sorted <=%O s -> sorted <=%O (mask m s).
Proof. exact/sorted_mask/le_trans. Qed.

Lemma lt_sorted_mask m s : sorted <%O s -> sorted <%O (mask m s).
Proof. exact/sorted_mask/lt_trans. Qed.

Lemma le_sorted_filter a s : sorted <=%O s -> sorted <=%O (filter a s).
Proof. exact/sorted_filter/le_trans. Qed.

Lemma lt_sorted_filter a s : sorted <%O s -> sorted <%O (filter a s).
Proof. exact/sorted_filter/lt_trans. Qed.

Lemma le_path_mask x m s : path <=%O x s -> path <=%O x (mask m s).
Proof. exact/path_mask/le_trans. Qed.

Lemma lt_path_mask x m s : path <%O x s -> path <%O x (mask m s).
Proof. exact/path_mask/lt_trans. Qed.

Lemma le_path_filter x a s : path <=%O x s -> path <=%O x (filter a s).
Proof. exact/path_filter/le_trans. Qed.

Lemma lt_path_filter x a s : path <%O x s -> path <%O x (filter a s).
Proof. exact/path_filter/lt_trans. Qed.

Lemma le_sorted_ltn_nth (x0 : T) (s : seq T) : sorted <=%O s ->
 {in [pred n | (n < size s)%N] &,
    {homo nth x0 s : i j / (i < j)%N >-> i <= j}}.
Proof. exact/sorted_ltn_nth/le_trans. Qed.

Lemma le_sorted_leq_nth (x0 : T) (s : seq T) : sorted <=%O s ->
  {in [pred n | (n < size s)%N] &,
    {homo nth x0 s : i j / (i <= j)%N >-> i <= j}}.
Proof. exact/sorted_leq_nth/le_refl/le_trans. Qed.

Lemma lt_sorted_leq_nth (x0 : T) (s : seq T) : sorted <%O s ->
  {in [pred n | (n < size s)%N] &,
    {mono nth x0 s : i j / (i <= j)%N >-> i <= j}}.
Proof.
move=> /[dup] lt_s /lt_sorted_is_uniq_le /andP[s_uniq le_s] i j ilt jlt.
case/boolP: (i <= j)%N; first exact/le_sorted_leq_nth.
rewrite -ltnNge => /(sorted_ltn_nth lt_trans x0 lt_s j i jlt ilt).
by rewrite lt_le_def => /andP[_] /negPf.
Qed.

Lemma lt_sorted_ltn_nth (x0 : T) (s : seq T) : sorted <%O s ->
  {in [pred n | (n < size s)%N] &,
    {mono nth x0 s : i j / (i < j)%N >-> i < j}}.
Proof.
move=> ss i j ilt jlt.
rewrite lt_le_def (lt_sorted_leq_nth x0 ss)// (lt_sorted_leq_nth x0 ss)//.
by rewrite -ltnNge andbC ltn_neqAle -andbA andbb.
Qed.

Lemma subseq_le_path x s1 s2 : subseq s1 s2 -> path <=%O x s2 -> path <=%O x s1.
Proof. exact/subseq_path/le_trans. Qed.

Lemma subseq_lt_path x s1 s2 : subseq s1 s2 -> path <%O x s2 -> path <%O x s1.
Proof. exact/subseq_path/lt_trans. Qed.

Lemma subseq_le_sorted s1 s2 : subseq s1 s2 -> sorted <=%O s2 -> sorted <=%O s1.
Proof. exact/subseq_sorted/le_trans. Qed.

Lemma subseq_lt_sorted s1 s2 : subseq s1 s2 -> sorted <%O s2 -> sorted <%O s1.
Proof. exact/subseq_sorted/lt_trans. Qed.

Lemma lt_sorted_uniq s : sorted <%O s -> uniq s.
Proof. exact/sorted_uniq/ltxx/lt_trans. Qed.

Lemma lt_sorted_eq s1 s2 :
  sorted <%O s1 -> sorted <%O s2 -> s1 =i s2 -> s1 = s2.
Proof. exact/irr_sorted_eq/ltxx/lt_trans. Qed.

Lemma filter_lt_nth x0 s i : sorted <%O s -> (i < size s)%N ->
  [seq x <- s | x < nth x0 s i] = take i s.
Proof.
move=> ss i_lt/=; rewrite -[X in filter _ X](mkseq_nth x0) filter_map.
under eq_in_filter => j do
  [rewrite ?mem_iota => j_s /=; rewrite lt_sorted_ltn_nth//].
by rewrite (filter_iota_ltn 0) ?map_nth_iota0 // ltnW.
Qed.

Lemma count_lt_nth x0 s i : sorted <%O s -> (i < size s)%N ->
  count (< nth x0 s i) s = i.
Proof.
by move=> ss i_lt; rewrite -size_filter/= filter_lt_nth// size_take i_lt.
Qed.

Lemma filter_le_nth x0 s i : sorted <%O s -> (i < size s)%N ->
  [seq x <- s | x <= nth x0 s i] = take i.+1 s.
Proof.
move=> ss i_lt/=; rewrite -[X in filter _ X](mkseq_nth x0) filter_map.
under eq_in_filter => j do
  [rewrite ?mem_iota => j_s /=; rewrite lt_sorted_leq_nth//].
by rewrite (filter_iota_leq 0)// map_nth_iota0.
Qed.

Lemma count_le_nth x0 s i : sorted <%O s -> (i < size s)%N ->
  count (<= nth x0 s i) s = i.+1.
Proof.
by move=> ss i_lt; rewrite -size_filter/= filter_le_nth// size_takel.
Qed.

Lemma sorted_filter_lt x s :
  sorted <=%O s -> [seq y <- s | y < x] = take (count (< x) s) s.
Proof.
elim: s => [//|y s IHs]/=; rewrite (path_sortedE le_trans) => /andP[le_y_s ss].
case: ifP => [|ltyxF]; rewrite IHs//.
rewrite (@eq_in_count _ _ pred0) ?count_pred0/= ?take0// => z.
by move=> /(allP le_y_s) yz; apply: contraFF ltyxF; apply: le_lt_trans.
Qed.

Lemma sorted_filter_le x s :
  sorted <=%O s -> [seq y <- s | y <= x] = take (count (<= x) s) s.
Proof.
elim: s => [//|y s IHs]/=; rewrite (path_sortedE le_trans) => /andP[le_y_s ss].
case: ifP => [|leyxF]; rewrite IHs//.
rewrite (@eq_in_count _ _ pred0) ?count_pred0/= ?take0// => z.
by move=> /(allP le_y_s) yz; apply: contraFF leyxF; apply: le_trans.
Qed.

Lemma nth_count_le x x0 s i : sorted <=%O s ->
  (i < count (<= x) s)%N -> nth x0 s i <= x.
Proof.
move=> ss iltc; rewrite -(nth_take _ iltc) -sorted_filter_le //.
by apply/(all_nthP _ (filter_all (<= x) _)); rewrite size_filter.
Qed.

Lemma nth_count_lt x x0 s i : sorted <=%O s ->
  (i < count (< x) s)%N -> nth x0 s i < x.
Proof.
move=> ss iltc; rewrite -(nth_take _ iltc) -sorted_filter_lt //.
by apply/(all_nthP _ (filter_all (< x) _)); rewrite size_filter.
Qed.

Lemma sort_le_id s : sorted <=%O s -> sort <=%O s = s.
Proof. exact/sorted_sort/le_trans. Qed.

Lemma sort_lt_id s : sorted <%O s -> sort <%O s = s.
Proof. exact/sorted_sort/lt_trans. Qed.

Lemma comparable_leNgt x y : x >=< y -> (x <= y) = ~~ (y < x).
Proof.
rewrite /comparable lt_le_def.
by case: (x <= y) => //=; case: (y <= x).
Qed.

Lemma comparable_ltNge x y : x >=< y -> (x < y) = ~~ (y <= x).
Proof.
rewrite /comparable lt_le_def.
by case: (x <= y) => //=; case: (y <= x).
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
Proof. by rewrite lt_le_def => /incomparable_leF ->. Qed.

Lemma le_comparable (x y : T) : x <= y -> x >=< y.
Proof. by rewrite /comparable => ->. Qed.

Lemma lt_comparable (x y : T) : x < y -> x >=< y.
Proof. by rewrite /comparable => /ltW ->. Qed.

Lemma ge_comparable (x y : T) : y <= x -> x >=< y.
Proof. by rewrite /comparable orbC => ->. Qed.

Lemma gt_comparable (x y : T) : y < x -> x >=< y.
Proof. by rewrite /comparable orbC => /ltW ->. Qed.

(* leif *)

Lemma leif_refl x C : reflect (x <= x ?= iff C) C.
Proof. by apply: (iffP idP) => [-> | <-] //; split; rewrite ?eqxx. Qed.

Lemma eq_leif x y C : x <= y ?= iff C -> (x == y) = C.
Proof. by move=> []. Qed.

Lemma eqTleif x y C : x <= y ?= iff C -> C -> x = y.
Proof. by move=> [] _ <- /eqP. Qed.

(* lteif *)

Lemma lteif_trans x y z C1 C2 :
  x < y ?<= if C1 -> y < z ?<= if C2 -> x < z ?<= if C1 && C2.
Proof.
case: C1 C2 => [][];
  [exact: le_trans | exact: le_lt_trans | exact: lt_le_trans | exact: lt_trans].
Qed.

Lemma lteifxx x C : (x < x ?<= if C) = C.
Proof. by case: C; rewrite /= ltexx. Qed.

Lemma lteifNF x y C : y < x ?<= if ~~ C -> x < y ?<= if C = false.
Proof. by case: C => [/lt_geF|/le_gtF]. Qed.

Lemma lteifS x y C : x < y -> x < y ?<= if C.
Proof. by case: C => //= /ltW. Qed.

Lemma lteifT x y : x < y ?<= if true = (x <= y). Proof. by []. Qed.

Lemma lteifF x y : x < y ?<= if false = (x < y). Proof. by []. Qed.

Lemma lteif_orb x y : {morph lteif x y : p q / p || q}.
Proof.
case=> [][] /=.
- by rewrite orbb.
- by case/boolP: (x < y) => [/ltW -> //|_]; rewrite orbF.
- by case/boolP: (x < y) => [/ltW ->|].
- by rewrite orbb.
Qed.

Lemma lteif_andb x y : {morph lteif x y : p q / p && q}.
Proof.
case=> [][] /=.
- by rewrite andbb.
- by rewrite lt_le_def andbA andbb.
- by rewrite andbC lt_le_def andbA andbb.
- by rewrite andbb.
Qed.

Lemma lteif_imply C1 C2 x y : C1 ==> C2 -> x < y ?<= if C1 -> x < y ?<= if C2.
Proof. by case: C1 C2 => [][] //= _ /ltW. Qed.

Lemma lteifW C x y : x < y ?<= if C -> x <= y.
Proof. by case: C => // /ltW. Qed.

Lemma ltrW_lteif C x y : x < y -> x < y ?<= if C.
Proof. by case: C => // /ltW. Qed.

(* min and max *)

Lemma minElt x y : min x y = if x < y then x else y. Proof. by []. Qed.
Lemma maxElt x y : max x y = if x < y then y else x. Proof. by []. Qed.

Lemma minxx : idempotent (min : T -> T -> T).
Proof. by rewrite /min => x; rewrite ltxx. Qed.

Lemma maxxx : idempotent (max : T -> T -> T).
Proof. by rewrite /max => x; rewrite ltxx. Qed.

Lemma min_minKx x y : min (min x y) y = min x y.
Proof. by rewrite !(fun_if, if_arg) ltxx/=; case: (x < y). Qed.

Lemma min_minxK x y : min x (min x y) = min x y.
Proof. by rewrite !(fun_if, if_arg) ltxx/=; case: (x < y). Qed.

Lemma max_maxKx x y : max (max x y) y = max x y.
Proof. by rewrite !(fun_if, if_arg) ltxx/=; case: (x < y). Qed.

Lemma max_maxxK x y : max x (max x y) = max x y.
Proof. by rewrite !(fun_if, if_arg) ltxx/=; case: (x < y). Qed.

Lemma comparable_minl z : {in >=< z &, forall x y, min x y >=< z}.
Proof. by move=> x y cmp_xz cmp_yz; rewrite /min; case: ifP. Qed.

Lemma comparable_minr z : {in >=<%O z &, forall x y, z >=< min x y}.
Proof. by move=> x y cmp_xz cmp_yz; rewrite /min; case: ifP. Qed.

Lemma comparable_maxl z : {in >=< z &, forall x y, max x y >=< z}.
Proof. by move=> x y cmp_xz cmp_yz; rewrite /max; case: ifP. Qed.

Lemma comparable_maxr z : {in >=<%O z &, forall x y, z >=< max x y}.
Proof. by move=> x y cmp_xz cmp_yz; rewrite /max; case: ifP. Qed.

Section Comparable2.
Variables (z x y : T) (cmp_xy : x >=< y).

Lemma comparable_le_min : (z <= min x y) = (z <= x) && (z <= y).
Proof.
move: cmp_xy; rewrite /min /comparable lt_le_def.
case/boolP: (x <= y) => xy/=; case/boolP: (y <= x) => yx//= _.
- by rewrite andbC; case/boolP: (z <= y) => zy //=; apply/esym/(le_trans zy).
- by case/boolP: (z <= x) => zx //=; apply/esym/(le_trans zx).
- by rewrite andbC; case/boolP: (z <= y) => zy //=; apply/esym/(le_trans zy).
Qed.

Lemma comparable_ge_min : (min x y <= z) = (x <= z) || (y <= z).
Proof.
move: cmp_xy; rewrite /min /comparable lt_le_def.
case/boolP: (x <= y) => xy/=; case/boolP: (y <= x) => yx//= _.
- rewrite orbC; case/boolP: (y <= z) => //= /negP yz.
  by apply/esym/negP => /(le_trans yx).
- by case/boolP: (x <= z) => //= /negP xz; apply/esym/negP => /(le_trans xy).
- rewrite orbC; case/boolP: (y <= z) => //= /negP yz.
  by apply/esym/negP => /(le_trans yx).
Qed.

Lemma comparable_lt_min : (z < min x y) = (z < x) && (z < y).
Proof.
move: cmp_xy; rewrite /min /comparable !lt_le_def.
case/boolP: (x <= y) => xy/=; case/boolP: (y <= x) => yx//= _.
- rewrite -!lt_le_def; case/boolP: (z < x) => //= /negP zx.
  by apply/negP => zy; apply/zx/(lt_le_trans zy).
- rewrite -!lt_le_def; case/boolP: (z < x) => //= zx; apply/esym/(lt_trans zx).
  by rewrite lt_le_def xy yx.
- rewrite -!lt_le_def andbC; case/boolP: (z < y) => //= zy; apply/esym/(lt_trans zy).
  by rewrite lt_le_def xy yx.
Qed.

Lemma comparable_gt_min : (min x y < z) = (x < z) || (y < z).
Proof.
move: cmp_xy; rewrite /min /comparable !lt_le_def.
case/boolP: (x <= y) => xy/=; case/boolP: (y <= x) => yx//= _.
- rewrite -!lt_le_def orbC; case/boolP: (y < z) => //= /negP yz.
  by apply/esym/negP => xz; apply/yz/(le_lt_trans yx).
- rewrite -!lt_le_def; case/boolP: (x < z) => //= /negP xz.
  by apply/esym/negP => yz; apply/xz/(le_lt_trans xy).
- rewrite -!lt_le_def orbC; case/boolP: (y < z) => //= /negP yz.
  by apply/esym/negP => xz; apply/yz/(le_lt_trans yx).
Qed.

Lemma comparable_le_max : (z <= max x y) = (z <= x) || (z <= y).
Proof.
move: cmp_xy; rewrite /max /comparable lt_le_def.
case/boolP: (x <= y) => xy/=; case/boolP: (y <= x) => yx//= _.
- case/boolP: (z <= x) => //= /negP zx.
  by apply/esym/negP => zy; apply/zx/(le_trans zy).
- rewrite orbC; case/boolP: (z <= y) => //= /negP zy.
  by apply/esym/negP => zx; apply/zy/(le_trans zx).
- case/boolP: (z <= x) => //= /negP zx.
  by apply/esym/negP => zy; apply/zx/(le_trans zy).
Qed.

Lemma comparable_ge_max : (max x y <= z) = (x <= z) && (y <= z).
Proof.
move: cmp_xy; rewrite /max /comparable lt_le_def.
case/boolP: (x <= y) => xy/=; case/boolP: (y <= x) => yx//= _.
- case/boolP: (x <= z) => //= xz.
  by apply/esym/(le_trans yx).
- rewrite andbC; case/boolP: (y <= z) => //= yz.
  by apply/esym/(le_trans xy).
- case/boolP: (x <= z) => //= xz.
  by apply/esym/(le_trans yx).
Qed.

Lemma comparable_lt_max : (z < max x y) = (z < x) || (z < y).
Proof.
move: cmp_xy; rewrite /max /comparable !lt_le_def.
case/boolP: (x <= y) => xy/=; case/boolP: (y <= x) => yx//= _.
- rewrite -!lt_le_def; case/boolP: (z < x) => //= /negP zx.
  by apply/esym/negP => zy; apply/zx/(lt_le_trans zy).
- rewrite -!lt_le_def orbC; case/boolP: (z < y) => //= /negP zy.
  by apply/esym/negP => zx; apply/zy/(lt_le_trans zx).
- rewrite -!lt_le_def; case/boolP: (z < x) => //= /negP zx.
  by apply/esym/negP => zy; apply/zx/(lt_le_trans zy).
Qed.

Lemma comparable_gt_max : (max x y < z) = (x < z) && (y < z).
Proof.
move: cmp_xy; rewrite /max /comparable !lt_le_def.
case/boolP: (x <= y) => xy/=; case/boolP: (y <= x) => yx//= _.
- rewrite -!lt_le_def; case/boolP: (x < z) => //= xz.
  by apply/esym/(le_lt_trans yx).
- rewrite -!lt_le_def andbC; case/boolP: (y < z) => //= yz.
  by apply/esym/(le_lt_trans xy).
- rewrite -!lt_le_def; case/boolP: (x < z) => //= xz.
  by apply/esym/(le_lt_trans yx).
Qed.

Lemma comparable_minxK : max (min x y) y = y.
Proof. by rewrite !(fun_if, if_arg) ltxx/=; case: (x < y). Qed.

Lemma comparable_minKx : max x (min x y) = x.
Proof. by rewrite !(fun_if, if_arg) ltxx/=; case: (x < y). Qed.

Lemma comparable_maxxK : min (max x y) y = y.
Proof. by rewrite !(fun_if, if_arg) ltxx/=; case: (x < y). Qed.

Lemma comparable_maxKx : min x (max x y) = x.
Proof. by rewrite !(fun_if, if_arg) ltxx/=; case: (x < y). Qed.

Lemma comparable_lteif_minr C :
  (z < min x y ?<= if C) = (z < x ?<= if C) && (z < y ?<= if C).
Proof. by case: C; rewrite /= (comparable_le_min, comparable_lt_min). Qed.

Lemma comparable_lteif_minl C :
  (min x y < z ?<= if C) = (x < z ?<= if C) || (y < z ?<= if C).
Proof. by case: C; rewrite /= (comparable_ge_min, comparable_gt_min). Qed.

Lemma comparable_lteif_maxr C :
  (z < max x y ?<= if C) = (z < x ?<= if C) || (z < y ?<= if C).
Proof. by case: C; rewrite /= (comparable_le_max, comparable_lt_max). Qed.

Lemma comparable_lteif_maxl C :
  (max x y < z ?<= if C) = (x < z ?<= if C) && (y < z ?<= if C).
Proof. by case: C; rewrite /= (comparable_ge_max, comparable_gt_max). Qed.

End Comparable2.

Section Comparable3.
Variables (x y z : T) (cmp_xy : x >=< y) (cmp_xz : x >=< z) (cmp_yz : y >=< z).

Lemma comparable_minA : min x (min y z) = min (min x y) z.
Proof.
move: cmp_xy cmp_xz cmp_yz; rewrite !(fun_if, if_arg)/= !lt_le_def.
case/boolP: (x <= y) => xy;
  case/boolP: (y <= x) => yx;
  case/boolP: (x <= z) => xz;
  case/boolP: (z <= x) => zx;
  case/boolP: (y <= z) => yz;
  case/boolP: (z <= y) => zy //= _ _ _.
- by move: zx; rewrite (le_trans zy yx).
- by move: zx; rewrite (le_trans zy yx).
- by move: zy; rewrite (le_trans zx xy).
- by move: zy; rewrite (le_trans zx xy).
- by move: zx; rewrite (le_trans zy yx).
- by move: zx; rewrite (le_trans zy yx).
Qed.

Lemma comparable_maxA : max x (max y z) = max (max x y) z.
Proof.
move: cmp_xy cmp_xz cmp_yz; rewrite !(fun_if, if_arg)/= !lt_le_def.
case/boolP: (x <= y) => xy;
  case/boolP: (y <= x) => yx;
  case/boolP: (x <= z) => xz;
  case/boolP: (z <= x) => zx;
  case/boolP: (y <= z) => yz;
  case/boolP: (z <= y) => zy //= _ _ _.
- by move: zx; rewrite (le_trans zy yx).
- by move: zx; rewrite (le_trans zy yx).
- by move: zy; rewrite (le_trans zx xy).
- by move: zy; rewrite (le_trans zx xy).
- by move: zx; rewrite (le_trans zy yx).
- by move: zx; rewrite (le_trans zy yx).
Qed.

Lemma comparable_min_maxl : min (max x y) z = max (min x z) (min y z).
Proof.
move: cmp_xy cmp_xz cmp_yz; rewrite !(fun_if, if_arg)/= !lt_le_def.
case/boolP: (x <= y) => xy;
  case/boolP: (y <= x) => yx;
  case/boolP: (x <= z) => xz;
  case/boolP: (z <= x) => zx;
  case/boolP: (y <= z) => yz;
  case/boolP: (z <= y) => zy;
  rewrite ?lexx => //= _ _ _.
- by move: zx; rewrite (le_trans zy yx).
- by move: zx; rewrite (le_trans zy yx).
- by move: zy; rewrite (le_trans zx xy).
- by move: zy; rewrite (le_trans zx xy).
- by move: zx; rewrite (le_trans zy yx).
- by move: zx; rewrite (le_trans zy yx).
Qed.

Lemma comparable_max_minr :
  max x (min y z) = min (max x y) (max x z).
Proof.
move: cmp_xy cmp_xz cmp_yz; rewrite !(fun_if, if_arg)/= !lt_le_def.
case/boolP: (x <= y) => xy;
  case/boolP: (y <= x) => yx;
  case/boolP: (x <= z) => xz;
  case/boolP: (z <= x) => zx;
  case/boolP: (y <= z) => yz;
  case/boolP: (z <= y) => zy;
  rewrite ?lexx => //= _ _ _.
- by move: zx; rewrite (le_trans zy yx).
- by move: zx; rewrite (le_trans zy yx).
- by move: zy; rewrite (le_trans zx xy).
- by move: zy; rewrite (le_trans zx xy).
- by move: zx; rewrite (le_trans zy yx).
- by move: zx; rewrite (le_trans zy yx).
Qed.

End Comparable3.

Section ArgExtremum.

Context (I : finType) (i0 : I) (P : {pred I}) (F : I -> T) (Pi0 : P i0).
Hypothesis F_comparable : {in P &, forall i j, F i >=< F j}.

Lemma comparable_arg_minP: extremum_spec <=%O P F (arg_min i0 P F).
Proof.
by apply: extremum_inP => // [x _|y x z _ _ _]; [apply: lexx|apply: le_trans].
Qed.

Lemma comparable_arg_maxP: extremum_spec >=%O P F (arg_max i0 P F).
Proof.
apply: extremum_inP => // [x _|y x z _ _ _|]; [exact: lexx|exact: ge_trans|].
by move=> x y xP yP; rewrite orbC [_ || _]F_comparable.
Qed.

End ArgExtremum.

(* monotonicity *)

Lemma comparable_bigl x x0 op I (P : pred I) F (s : seq I) :
  {in >=< x &, forall y z, op y z >=< x} -> x0 >=< x ->
  {in P, forall i, F i >=< x} -> \big[op/x0]_(i <- s | P i) F i >=< x.
Proof. by move=> *; elim/big_ind : _. Qed.

Lemma comparable_bigr x x0 op I (P : pred I) F (s : seq I) :
  {in >=<%O x &, forall y z, x >=< op y z} -> x >=< x0 ->
  {in P, forall i, x >=< F i} -> x >=< \big[op/x0]_(i <- s | P i) F i.
Proof. by move=> *; elim/big_ind : _. Qed.

Section bigminmax.

Variables (I : Type) (r : seq I) (f : I -> T) (x0 x : T) (P : pred I).

Lemma bigmax_lt : x0 < x -> (forall i, P i -> f i < x) ->
  \big[max/x0]_(i <- r | P i) f i < x.
Proof. by move=> ? ?; elim/big_ind: _ => // *; rewrite maxElt; case: ifPn. Qed.

Lemma lt_bigmin : x < x0 -> (forall i, P i -> x < f i) ->
  x < \big[min/x0]_(i <- r | P i) f i.
Proof. by move=> ? ?; elim/big_ind: _ => // *; rewrite minElt; case: ifPn. Qed.

End bigminmax.

End PreorderTheory.
#[global] Hint Resolve comparable_minr comparable_minl : core.
#[global] Hint Resolve comparable_maxr comparable_maxl : core.

Section ContraTheory.
Context {disp1 disp2 : disp_t} {T1 : preorderType disp1} {T2 : preorderType disp2}.
Implicit Types (x y : T1) (z t : T2) (b : bool) (m n : nat) (P : Prop).

Lemma comparable_contraTle b x y : x >=< y -> (y < x -> ~~ b) -> (b -> x <= y).
Proof. by move=> /comparable_leNgt ->; case: (y < x); case: b. Qed.

Lemma comparable_contraTlt b x y : x >=< y -> (y <= x -> ~~ b) -> (b -> x < y).
Proof. by move=> /comparable_ltNge ->; case: (y <= x); case: b. Qed.

Lemma comparable_contraPle P x y : x >=< y -> (y < x -> ~ P) -> (P -> x <= y).
Proof. by move=> /comparable_leNgt -> np p; apply/negP => /np. Qed.

Lemma comparable_contraPlt P x y : x >=< y -> (y <= x -> ~ P) -> (P -> x < y).
Proof. by move=> /comparable_ltNge -> np p; apply/negP => /np. Qed.

Lemma comparable_contraNle b x y : x >=< y -> (y < x -> b) -> (~~ b -> x <= y).
Proof. by move=> /comparable_leNgt ->; case: (y < x); case: b. Qed.

Lemma comparable_contraNlt b x y : x >=< y -> (y <= x -> b) -> (~~ b -> x < y).
Proof. by move=> /comparable_ltNge ->; case: (y <= x); case: b. Qed.

Lemma comparable_contra_not_le P x y : x >=< y -> (y < x -> P) -> (~ P -> x <= y).
Proof. by move=> /comparable_leNgt -> np p; apply/negP => /np. Qed.

Lemma comparable_contra_not_lt P x y : x >=< y -> (y <= x -> P) -> (~ P -> x < y).
Proof. by move=> /comparable_ltNge -> np p; apply/negP => /np. Qed.

Lemma comparable_contraFle b x y : x >=< y -> (y < x -> b) -> (b = false -> x <= y).
Proof. by move=> /comparable_leNgt -> np /negP p; apply/negP => /np. Qed.

Lemma comparable_contraFlt b x y : x >=< y -> (y <= x -> b) -> (b = false -> x < y).
Proof. by move=> /comparable_ltNge -> np /negP p; apply/negP => /np. Qed.

Lemma comparable_contra_leq_le m n x y : x >=< y ->
  (y < x -> (n < m)%N) -> ((m <= n)%N -> x <= y).
Proof. by rewrite ltnNge; apply/comparable_contraTle. Qed.

Lemma comparable_contra_leq_lt m n x y : x >=< y ->
  (y <= x -> (n < m)%N) -> ((m <= n)%N -> x < y).
Proof. by rewrite ltnNge; apply/comparable_contraTlt. Qed.

Lemma comparable_contra_ltn_le m n x y : x >=< y ->
  (y < x -> (n <= m)%N) -> ((m < n)%N -> x <= y).
Proof. by rewrite ltnNge; apply/comparable_contraNle. Qed.

Lemma comparable_contra_ltn_lt m n x y : x >=< y ->
  (y <= x -> (n <= m)%N) -> ((m < n)%N -> x < y).
Proof. by rewrite ltnNge; apply/comparable_contraNlt. Qed.

Lemma comparable_contra_le x y z t : z >=< t ->
  (t < z -> y < x) -> (x <= y -> z <= t).
Proof.
rewrite /comparable lt_le_def; case: (z <= t) => //= -> /(_ erefl) yx.
by move=> /(lt_le_trans yx); rewrite ltxx.
Qed.

Lemma comparable_contra_le_lt x y z t : z >=< t ->
  (t <= z -> y < x) -> (x <= y -> z < t).
Proof.
rewrite /comparable [z < t]lt_le_def orbC; case: (t <= z) => /= [_|-> //].
by move=> /(_ erefl) yx /(lt_le_trans yx); rewrite ltxx.
Qed.

Lemma comparable_contra_lt_le x y z t : z >=< t ->
  (t < z -> y <= x) -> (x < y -> z <= t).
Proof.
rewrite /comparable lt_le_def; case: (z <= t) => //= -> /(_ erefl) yx.
by move=> /(le_lt_trans yx); rewrite ltxx.
Qed.

Lemma comparable_contra_lt x y z t : z >=< t ->
 (t <= z -> y <= x) -> (x < y -> z < t).
Proof.
rewrite /comparable [z < t]lt_le_def orbC; case: (t <= z) => /= [_|-> //].
by move=> /(_ erefl) yx /(le_lt_trans yx); rewrite ltxx.
Qed.

End ContraTheory.

Section PreorderMonotonyTheory.

Context {disp disp' : disp_t}.
Context {T : preorderType disp} {T' : preorderType disp'}.
Implicit Types (m n p : nat) (x y z : T) (u v w : T').
Variables (D D' : {pred T}) (f : T -> T').

Hint Resolve lexx lt_le_def : core.

Lemma leW_mono : {mono f : x y / x <= y} -> {mono f : x y / x < y}.
Proof. by move=> fmono x y; rewrite !lt_le_def !fmono. Qed.

Lemma leW_nmono : {mono f : x y /~ x <= y} -> {mono f : x y /~ x < y}.
Proof. by move=> fmono x y; rewrite !lt_le_def !fmono. Qed.

Lemma leW_mono_in :
  {in D &, {mono f : x y / x <= y}} -> {in D &, {mono f : x y / x < y}}.
Proof. by move=> fmono x y xD yD; rewrite !lt_le_def !fmono. Qed.

Lemma leW_nmono_in :
  {in D &, {mono f : x y /~ x <= y}} -> {in D &, {mono f : x y /~ x < y}}.
Proof. by move=> fmono x y xD yD; rewrite !lt_le_def !fmono. Qed.

End PreorderMonotonyTheory.

End PreorderTheory.

#[global] Hint Resolve lexx le_refl ltxx lt_irreflexive ltW lt_eqF : core.

Arguments leif_refl {disp T x C}.

Module Import BPreorderTheory.
Section BPreorderTheory.
Context {disp : disp_t} {T : bPreorderType disp}.
Implicit Types (x y : T).

Lemma le0x x : \bot <= x. Proof. exact: le0x. Qed.

Lemma ltx0 x : (x < \bot) = false.
Proof. exact/le_gtF/le0x. Qed.

End BPreorderTheory.
End BPreorderTheory.

Module Import TPreorderTheory.
Section TPreorderTheory.
Context {disp : disp_t} {T : tPreorderType disp}.
Implicit Types (x y : T).

Lemma lex1 x : x <= \top. Proof. exact: lex1. Qed.
Lemma lt1x x : (\top < x) = false. Proof. exact: (@ltx0 _ T^d). Qed.

End TPreorderTheory.
End TPreorderTheory.

#[global] Hint Extern 0 (is_true (\bot <= _)) => exact: le0x : core.
#[global] Hint Extern 0 (is_true (_ <= \top)) => exact: lex1 : core.

(*************)
(* FACTORIES *)
(*************)

(* preorder *)

HB.factory Record isPreorder (d : disp_t) T of Equality T := {
  le       : rel T;
  lt       : rel T;
  lt_def   : forall x y, lt x y = (le x y) && ~~ (le y x);
  le_refl  : reflexive     le;
  le_trans : transitive    le;
}.

HB.builders Context (d : disp_t) T of isPreorder d T.
(* TODO: print nice error message when keyed type is not provided *)

Let ge_trans : transitive (fun x y => le y x).
Proof. by move=> x y z /[swap]; apply: le_trans. Qed.

HB.instance Definition _ := @isDuallyPreorder.Build d T
  le _ lt_def (fun x y => lt_def y x) le_refl le_refl le_trans ge_trans.
HB.end.

HB.factory Record Le_isPreorder (d : disp_t) T of Equality T := {
  le       : rel T;
  le_refl  : reflexive     le;
  le_trans : transitive    le;
}.

HB.builders Context (d : disp_t) T of Le_isPreorder d T.
(* TODO: print nice error message when keyed type is not provided *)

HB.instance Definition _ := @isPreorder.Build d T
  le _ (fun _ _ => erefl) le_refl le_trans.
HB.end.

HB.factory Record LtLe_isPreorder (d : disp_t) T of Equality T := {
  le : rel T;
  lt : rel T;
  le_def   : forall x y, le x y = (x == y) || lt x y;
  lt_irr   : irreflexive lt;
  lt_trans : transitive lt;
}.
HB.builders Context (d : disp_t) T of LtLe_isPreorder d T.

Let le_refl : reflexive le. Proof. by move=> x; rewrite le_def eqxx. Qed.

Let le_trans : transitive le.
Proof.
move=> y x z; rewrite !le_def; case: (eqVneq x y) => [->|]//= neq_xy.
by case: (eqVneq y z) => /= [<- ->|_ /lt_trans yx /yx ->]; rewrite orbT.
Qed.

Let lt_le_def x y : lt x y = (le x y) && ~~ (le y x).
Proof.
rewrite !le_def eq_sym; have [->|_ /=] := eqVneq x y; first by rewrite lt_irr.
case/boolP: (lt x y) => //= xy; apply/esym/negP => /(lt_trans xy).
by rewrite lt_irr.
Qed.

HB.instance Definition _ := @isPreorder.Build d T
  le lt lt_le_def le_refl le_trans .

HB.end.

HB.factory Record Lt_isPreorder (d : disp_t) T of Equality T := {
  lt       : rel T;
  lt_irr   : irreflexive lt;
  lt_trans : transitive  lt;
}.

HB.builders Context (d : disp_t) (T : Type) of Lt_isPreorder d T.
HB.instance Definition _ := @LtLe_isPreorder.Build d T
  _ lt (fun _ _ => erefl) lt_irr lt_trans.
HB.end.

Module PreCancelPartial.
Section PreCancelPartial.
Variables (disp : disp_t) (T : choiceType).
Variables (disp' : disp_t) (T' : preorderType disp') (f : T -> T').

Definition le (x y : T) := f x <= f y.
Definition lt (x y : T) := f x < f y.

Fact refl : reflexive le. Proof. by move=> ?; apply: lexx. Qed.
Fact trans : transitive le. Proof. by move=> ? ? ?; apply: le_trans. Qed.
Fact ge_trans : transitive (fun x y => le y x). Proof. by move=> ? ? ?; apply: ge_trans. Qed.
Fact lt_le_def x y : lt x y = le x y && ~~ le y x.
Proof. exact: lt_le_def. Qed.

Definition PrePcan := isPreorder.Build disp T lt_le_def refl trans.

End PreCancelPartial.
End PreCancelPartial.

(* FIXME
Fail #[export]
HB.instance Definition _ (disp : disp_t) (T : choiceType)
  (disp' : disp_t) (T' : porderType disp') (f : T -> T')
  (f_inj : injective f): isPreorder disp (inj_type f_inj) :=
  @PreCancelPartial.PrePcan disp (inj_type f_inj) disp' T' f.
 *)

#[export]
HB.instance Definition _ (disp : disp_t) (T : Type)
  (disp' : disp_t) (T' : preorderType disp') (f : T -> T')
  (f' : T' -> option T) (f_can : pcancel f f') : isPreorder disp (pcan_type f_can) :=
  @PreCancelPartial.PrePcan disp (pcan_type f_can) disp' T' f.

#[export]
HB.instance Definition _ (disp : disp_t) (T : Type)
  (disp' : disp_t) (T' : preorderType disp') (f : T -> T')
  (f' : T' -> T) (f_can : cancel f f') : isPreorder disp (can_type f_can) :=
  @PreCancelPartial.PrePcan disp (can_type f_can) disp' T' f.

(* Morphism hierarchy. *)

Definition order_morphism d (T : preorderType d) d' (T' : preorderType d')
  (f : T -> T') : Prop := {mono f : x y / x <= y}.

HB.mixin Record isOrderMorphism d (T : preorderType d) d' (T' : preorderType d')
    (apply : T -> T') := {
  omorph_le_subproof : {homo apply : x y / x <= y} ;
}.

HB.structure Definition OrderMorphism d (T : preorderType d)
  d' (T' : preorderType d') := {f of isOrderMorphism d T d' T' f}.

Module OrderMorphismExports.
Notation "{ 'omorphism' T -> T' }" :=
  (@OrderMorphism.type _ T%type _ T'%type) : type_scope.
End OrderMorphismExports.
HB.export OrderMorphismExports.

Module Import OrderMorphismTheory.
Section OrderMorphismTheory.

Lemma omorph_le (d : disp_t) (T : preorderType d) (d' : disp_t) (T' : preorderType d')
(f : {omorphism T -> T'}) : {homo f : x y / x <= y}.
Proof. exact: omorph_le_subproof. Qed.

Section IdCompFun.

Variables (d : disp_t) (T : preorderType d) (d' : disp_t) (T' : preorderType d').
Variables (d'' : disp_t) (T'' : preorderType d'').
Variables (f : {omorphism T' -> T''}) (g : {omorphism T -> T'}).

Fact idfun_is_nondecreasing : nondecreasing (@idfun T).
Proof. by []. Qed.
#[export]
HB.instance Definition _ := isOrderMorphism.Build d T d T idfun
  idfun_is_nondecreasing.

Fact comp_is_nondecreasing : nondecreasing (f \o g).
Proof. by move=> ? ? ?; do 2 apply: omorph_le. Qed.

#[export]
HB.instance Definition _ := isOrderMorphism.Build d T d'' T'' (f \o g)
  comp_is_nondecreasing.

End IdCompFun.

End OrderMorphismTheory.
End OrderMorphismTheory.

HB.mixin Record isSubPreorder d (T : preorderType d) (S : pred T) d' U
    of SubType T S U & Preorder d' U := {
  le_val : {mono (val : U -> T) : x y / x <= y};
}.

#[short(type="subPreorder")]
HB.structure Definition SubPreorder d (T : preorderType d) S d' :=
  { U of SubEquality T S U & Preorder d' U & isSubPreorder d T S d' U }.

Module Import SubPreorderTheory.
Section SubPreorderTheory.
Context (d : disp_t) (T : preorderType d) (S : pred T).
Context (d' : disp_t) (U : SubPreorder.type S d').
Local Notation val := (val : U -> T).
#[deprecated(since="mathcomp 2.3.0", note="Use le_val instead.")]
Lemma leEsub x y : (x <= y) = (val x <= val y). Proof. by rewrite le_val. Qed.
Lemma lt_val : {mono val : x y / x < y}.
Proof. by move=> x y; rewrite !lt_leAnge !le_val. Qed.
#[deprecated(since="mathcomp 2.3.0", note="Use lt_val instead.")]
Lemma ltEsub x y : (x < y) = (val x < val y). Proof. by rewrite lt_val. Qed.
Lemma le_wval : {homo val : x y / x <= y}. Proof. exact/mono2W/le_val. Qed.
Lemma lt_wval : {homo val : x y / x < y}. Proof. exact/mono2W/lt_val. Qed.
HB.instance Definition _ := isOrderMorphism.Build d' U d T val le_wval.
End SubPreorderTheory.
Arguments lt_val {d T S d' U} x y.
Arguments le_wval {d T S d' U} x y.
Arguments lt_wval {d T S d' U} x y.
End SubPreorderTheory.

HB.factory Record SubChoice_isSubPreorder d (T : preorderType d) S (d' : disp_t) U
    of SubChoice T S U := {}.

HB.builders Context d T S d' U of SubChoice_isSubPreorder d T S d' U.
HB.instance Definition _ : isPreorder d' U :=
  @PreCancelPartial.PrePcan d' U d T val.
Fact valD : order_morphism (val : U -> T). Proof. by []. Qed.
HB.instance Definition _ := isSubPreorder.Build d T S d' U valD.
HB.end.

Module SubOrderExports.

Notation "[ 'SubChoice_isSubPreorder' 'of' U 'by' <: ]" :=
  (SubChoice_isSubPreorder.Build _ _ _ _ U)
  (at level 0, format "[ 'SubChoice_isSubPreorder'  'of'  U  'by'  <: ]")
  : form_scope.
Notation "[ 'SubChoice_isSubPreorder' 'of' U 'by' <: 'with' disp ]" :=
  (SubChoice_isSubPreorder.Build _ _ _ disp U)
  (at level 0, format "[ 'SubChoice_isSubPreorder'  'of'  U  'by'  <:  'with'  disp ]")
  : form_scope.

End SubOrderExports.
HB.export SubOrderExports.

(*************)
(* INSTANCES *)
(*************)

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

Lemma ltn_def x y : (x < y)%N = (x <= y)%N && ~~ (y <= x)%N.
Proof. by rewrite -ltnNge andbC; case: (ltnP x y) => //= /ltnW. Qed.

#[export]
HB.instance Definition _ :=
  isPreorder.Build nat_display nat ltn_def leqnn leq_trans.

#[export]
HB.instance Definition _ := hasBottom.Build nat_display nat leq0n.

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
Implicit Types (m n p : nat).

Definition t := nat.

#[export]
HB.instance Definition _ := Choice.copy t nat.

(* Note that this where the dvd_display is associated with the type NatDvd.t. *)
#[export]
HB.instance Definition _ := @Le_isPreorder.Build
  dvd_display t dvdn dvdnn dvdn_trans.

(* NatDvd.t is associated below with the notation "natdvd".                   *)

#[export]
HB.instance Definition _ := @hasBottom.Build _ t 1 dvd1n.

#[export]
HB.instance Definition _ := @hasTop.Build _ t 0 dvdn0.

Import DvdSyntax.
Lemma dvdE : dvd = dvdn :> rel t. Proof. by []. Qed.
Lemma nat1E : nat1 = 1%N :> t. Proof. by []. Qed.
Lemma nat0E : nat0 = 0%N :> t. Proof. by []. Qed.

End NatDvd.
Module Exports.
HB.reexport NatDvd.
Notation natdvd := t.
Definition dvdEnat := dvdE.
Definition nat1E := nat1E.
Definition nat0E := nat0E.
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

#[export]
HB.instance Definition _ :=
  [SubChoice_isSubPreorder of 'I_n by <: with ord_display].

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

Fact ltn_def x y : (x < y)%N = (x <= y)%N && ~~ (y <= x)%N.
Proof. by case: x y => [] []. Qed.

#[export] HB.instance Definition _ := @isPreorder.Build bool_display bool
   _ _ ltn_def leqnn leq_trans.
#[export] HB.instance Definition _ := @hasBottom.Build _ bool false leq0n.
#[export] HB.instance Definition _ := @hasTop.Build _ bool true leq_b1.

Lemma leEbool : le = (leq : rel bool). Proof. by []. Qed.
Lemma ltEbool x y : (x < y) = (x < y)%N. Proof. by []. Qed.

End BoolOrder.
Module Exports.
HB.reexport BoolOrder.
Definition leEbool := leEbool.
Definition ltEbool := ltEbool.
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

#[export]
HB.instance Definition _ := @isDuallyPreorder.Build disp3 (T1 * T2) le lt
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
  (x1, x2) <= (y1, y2) :> T1 * T2 = (x1 <= y1) && (x2 <= y2).
Proof. by []. Qed.

Lemma lt_pair (x1 y1 : T1) (x2 y2 : T2) :
  (x1, x2) < (y1, y2) :> T1 * T2
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

#[export]
HB.instance Definition _ :=
  @hasBottom.Build disp3 (T1 * T2) (\bot, \bot) (@le0x _ _ T1' T2').

Lemma botEprod : \bot = (\bot, \bot) :> T1 * T2. Proof. by []. Qed.

End BPreorder.

Section TPreorder.
Context (disp1 disp2 disp3 : disp_t).
Context (T1 : tPreorderType disp1) (T2 : tPreorderType disp2).
Local Notation "T1 * T2" := (type disp3 T1 T2) : type_scope.

#[export]
HB.instance Definition _ :=
  @hasTop.Build disp3 (T1 * T2) (\top, \top) (@le0x _ _ T1^d T2^d).

Lemma topEprod : \top = (\top, \top) :> T1 * T2. Proof. by []. Qed.

End TPreorder.

(* FIXME: use HB.saturate *)
#[export]
HB.instance Definition _ (disp1 disp2 disp3 : disp_t)
  (T1 : tbPreorderType disp1) (T2 : tbPreorderType disp2) :=
  Preorder.on (type disp3 T1 T2).

(* FIXME: use HB.saturate *)
Section FinPreorder.
Context (disp1 disp2 disp3 : disp_t).

#[export]
HB.instance Definition _ (T1 : finPreorderType disp1)
  (T2 : finPreorderType disp2) := Preorder.on (type disp3 T1 T2).
#[export]
HB.instance Definition _ (T1 : finBPreorderType disp1)
  (T2 : finBPreorderType disp2) := Preorder.on (type disp3 T1 T2).
#[export]
HB.instance Definition _ (T1 : finTPreorderType disp1)
  (T2 : finTPreorderType disp2) := Preorder.on (type disp3 T1 T2).
#[export]
HB.instance Definition _ (T1 : finTBPreorderType disp1)
  (T2 : finTBPreorderType disp2) := Preorder.on (type disp3 T1 T2).

End FinPreorder.

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

End DefaultProdOrder.
End DefaultProdOrder.

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

#[export]
HB.instance Definition _ := @isDuallyPreorder.Build disp3 (T1 * T2) le lt
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
   (x1, x2) <= (y1, y2) :> T1 * T2 = (x1 <= y1) && ((x1 >= y1) ==> (x2 <= y2)).
Proof. by []. Qed.

Lemma ltxi_pair (x1 y1 : T1) (x2 y2 : T2) :
   (x1, x2) < (y1, y2) :> T1 * T2 = (x1 <= y1) && ((x1 >= y1) ==> (x2 < y2)).
Proof. by []. Qed.

End Preorder.

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

#[export]
HB.instance Definition _ :=
  @hasBottom.Build disp3 (T1 * T2) (\bot, \bot) (@le0x _ _ T1' T2').

Lemma botEprodlexi : \bot = (\bot, \bot) :> T1 * T2. Proof. by []. Qed.

End BPreorder.

Section TPreorder.
Context (disp1 disp2 disp3 : disp_t).
Context (T1 : tPreorderType disp1) (T2 : tPreorderType disp2).
Local Notation "T1 * T2" := (type disp3 T1 T2) : type_scope.

#[export]
HB.instance Definition _ :=
  @hasTop.Build disp3 (T1 * T2) (\top, \top) (@le0x _ _ T1^d T2^d).

Lemma topEprodlexi : \top = (\top, \top) :> T1 * T2. Proof. by []. Qed.

End TPreorder.

(* FIXME: use HB.saturate *)
#[export]
HB.instance Definition _ (disp1 disp2 disp3 : disp_t)
  (T1 : tbPreorderType disp1) (T2 : tbPreorderType disp2) :=
  Preorder.on (type disp3 T1 T2).

Lemma sub_prod_lexi (disp1 disp2 disp3 disp4 : disp_t)
  (T1 : preorderType disp1) (T2 : preorderType disp2) :
  subrel (<=%O : rel (T1 *prod[disp3] T2)) (<=%O : rel (type disp4 T1 T2)).
Proof.
case=> [x1 x2] [y1 y2]; rewrite leEprod leEprodlexi /= => /andP[] -> ->.
exact: implybT.
Qed.

(* FIXME: use HB.saturate *)
Section ProdLexiOrder.
Context (disp1 disp2 disp3 : disp_t).

#[export]
HB.instance Definition _ (T1 : bPreorderType disp1)
  (T2 : bPreorderType disp2) := Preorder.on (type disp3 T1 T2).
#[export]
HB.instance Definition _ (T1 : tPreorderType disp1)
  (T2 : tPreorderType disp2) := Preorder.on (type disp3 T1 T2).
#[export]
HB.instance Definition _ (T1 : tbPreorderType disp1)
  (T2 : tbPreorderType disp2) := Preorder.on (type disp3 T1 T2).
#[export]
HB.instance Definition _ (T1 : finPreorderType disp1)
  (T2 : finPreorderType disp2) := Preorder.on (type disp3 T1 T2).
#[export]
HB.instance Definition _ (T1 : finBPreorderType disp1)
  (T2 : finBPreorderType disp2) := Preorder.on (type disp3 T1 T2).
#[export]
HB.instance Definition _ (T1 : finTPreorderType disp1)
  (T2 : finTPreorderType disp2) := Preorder.on (type disp3 T1 T2).
#[export]
HB.instance Definition _ (T1 : finTBPreorderType disp1)
  (T2 : finTBPreorderType disp2) := Preorder.on (type disp3 T1 T2).

End ProdLexiOrder.

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

#[export]
HB.instance Definition _ := isPreorder.Build disp' (seq T) (rrefl _) refl trans.

Lemma leEseq s1 s2 : s1 <= s2 = if s1 isn't x1 :: s1' then true else
                                if s2 isn't x2 :: s2' then false else
                                (x1 <= x2) && (s1' <= s2' :> seq _).
Proof. by case: s1. Qed.

Lemma le0s s : [::] <= s :> seq _. Proof. by []. Qed.

Lemma les0 s : s <= [::] = (s == [::]). Proof. by rewrite leEseq. Qed.

Lemma le_cons x1 s1 x2 s2 :
   x1 :: s1 <= x2 :: s2 :> seq _ = (x1 <= x2) && (s1 <= s2).
Proof. by []. Qed.

#[export]
HB.instance Definition _ := hasBottom.Build _ (seq T) le0s.

Lemma botEseq : \bot = [::] :> seq T.
Proof. by []. Qed.
End Preorder.

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

End Exports.
End SeqProdOrder.
HB.export SeqProdOrder.Exports.

Module DefaultSeqProdOrder.
Section DefaultSeqProdOrder.
Context {disp : disp_t}.

Notation seqprod := (seqprod_with (seqprod_display disp)).

HB.instance Definition _ (T : preorderType disp) :=
  Preorder.copy (seq T) (seqprod T).
HB.instance Definition _ (T : preorderType disp) :=
  BPreorder.copy (seq T) (seqprod T).

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

#[export]
HB.instance Definition _ := isPreorder.Build disp' (seq T) lt_le_def refl trans.

Lemma leEseqlexi s1 s2 :
   s1 <= s2 = if s1 isn't x1 :: s1' then true else
              if s2 isn't x2 :: s2' then false else
              (x1 <= x2) && ((x1 >= x2) ==> (s1' <= s2' :> seq T)).
Proof. by case: s1. Qed.

Lemma ltEseqlexi s1 s2 :
   s1 < s2 = if s2 isn't x2 :: s2' then false else
              if s1 isn't x1 :: s1' then true else
              (x1 <= x2) && ((x1 >= x2) ==> (s1' < s2' :> seq T)).
Proof. by case: s1. Qed.

Lemma lexi0s s : [::] <= s :> seq T. Proof. by []. Qed.

Lemma lexis0 s : s <= [::] = (s == [::]). Proof. by rewrite leEseqlexi. Qed.

Lemma ltxi0s s : ([::] < s :> seq T) = (s != [::]). Proof. by case: s. Qed.

Lemma ltxis0 s : s < [::] = false. Proof. by rewrite ltEseqlexi. Qed.

Lemma lexi_cons x1 s1 x2 s2 :
  x1 :: s1 <= x2 :: s2 :> seq T = (x1 <= x2) && ((x1 >= x2) ==> (s1 <= s2)).
Proof. by []. Qed.

Lemma ltxi_cons x1 s1 x2 s2 :
  x1 :: s1 < x2 :: s2 :> seq T = (x1 <= x2) && ((x1 >= x2) ==> (s1 < s2)).
Proof. by []. Qed.

Lemma lexi_lehead x s1 y s2 : x :: s1 <= y :: s2 :> seq T -> x <= y.
Proof. by rewrite lexi_cons => /andP[]. Qed.

Lemma ltxi_lehead x s1 y s2 : x :: s1 < y :: s2 :> seq T -> x <= y.
Proof. by rewrite ltxi_cons => /andP[]. Qed.

Lemma eqhead_lexiE (x : T) s1 s2 : (x :: s1 <= x :: s2 :> seq _) = (s1 <= s2).
Proof. by rewrite lexi_cons lexx. Qed.

Lemma eqhead_ltxiE (x : T) s1 s2 : (x :: s1 < x :: s2 :> seq _) = (s1 < s2).
Proof. by rewrite ltxi_cons lexx. Qed.

#[export]
HB.instance Definition _ := hasBottom.Build _ (seq T) lexi0s.

End Preorder.

Lemma sub_seqprod_lexi d (T : preorderType disp) :
   subrel (<=%O : rel (seqprod_with d T)) (<=%O : rel (seq T)).
Proof.
elim=> [|x1 s1 ihs1] [|x2 s2]//=; rewrite le_cons lexi_cons /=.
by move=> /andP[-> /ihs1->]; rewrite implybT.
Qed.

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

End Exports.
End SeqLexiOrder.
HB.export SeqLexiOrder.Exports.

Module DefaultSeqLexiOrder.
Section DefaultSeqLexiOrder.
Context {disp : disp_t}.

Notation seqlexi := (seqlexi_with (seqlexi_display disp)).

HB.instance Definition _ (T : preorderType disp) :=
  Preorder.copy (seq T) (seqlexi T).
HB.instance Definition _ (T : preorderType disp) :=
  BPreorder.copy (seq T) (seqlexi T).

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
   t1 <= t2 = [forall i, tnth t1 i <= tnth t2 i].
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
  t1 < t2 = [exists i, tnth t1 i < tnth t2 i] &&
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

#[export]
HB.instance Definition _ := hasBottom.Build _ (n.-tuple T) le0x.

Lemma botEtprod : \bot = [tuple \bot | _ < n] :> n.-tuple T.
Proof. by []. Qed.

End BPreorder.

Section TPreorder.
Context (n : nat) (T : tPreorderType disp).
Implicit Types (t : n.-tuple T).

Fact lex1 t : t <= [tuple \top | _ < n] :> n.-tuple T.
Proof. by rewrite leEtprod; apply/forallP => i; rewrite tnth_mktuple lex1. Qed.

#[export]
HB.instance Definition _ := hasTop.Build _ (n.-tuple T) lex1.

Lemma topEtprod : \top = [tuple \top | _ < n] :> n.-tuple T.
Proof. by []. Qed.

End TPreorder.

(* FIXME: use HB.saturate *)
#[export]
HB.instance Definition _ (n : nat) (T : tbPreorderType disp) :=
  Preorder.on (n.-tuple T).
#[export]
HB.instance Definition _ (n : nat) (T : finPreorderType disp) :=
  Preorder.on (n.-tuple T).
#[export]
HB.instance Definition _ (n : nat) (T : finPreorderType disp) :=
  Preorder.on (n.-tuple T).
#[export]
HB.instance Definition _ (n : nat) (T : finBPreorderType disp) :=
  Preorder.on (n.-tuple T).
#[export]
HB.instance Definition _ (n : nat) (T : finTPreorderType disp) :=
  Preorder.on (n.-tuple T).
#[export]
HB.instance Definition _ (n : nat) (T : finTBPreorderType disp) :=
  Preorder.on (n.-tuple T).

End TupleProdOrder.

Module Exports.

HB.reexport TupleProdOrder.

Notation "n .-tupleprod[ disp ]" := (type disp n)
  (at level 2, disp at next level, format "n .-tupleprod[ disp ]") :
  type_scope.
Notation "n .-tupleprod" := (type_ n)
  (at level 2, format "n .-tupleprod") : type_scope.

Definition leEtprod := @leEtprod.
Definition ltEtprod := @ltEtprod.
Definition botEtprod := @botEtprod.
Definition topEtprod := @topEtprod.

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

#[export] HB.instance Definition _ n T := SubChoice.on (n.-tuple T).
#[export] HB.instance Definition _ n T :=
  [SubChoice_isSubPreorder of n.-tuple T by <: with disp'].

End Preorder.

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

(* FIXME: use HB.saturate *)
#[export]
HB.instance Definition _ (n : nat) (T : bPreorderType disp) :=
  Preorder.on (n.-tuple T).
#[export]
HB.instance Definition _ (n : nat) (T : tPreorderType disp) :=
  Preorder.on (n.-tuple T).
#[export]
HB.instance Definition _ (n : nat) (T : tbPreorderType disp) :=
  Preorder.on (n.-tuple T).

Lemma sub_tprod_lexi d n (T : preorderType disp) :
   subrel (<=%O : rel (n.-tupleprod[d] T)) (<=%O : rel (n.-tuple T)).
Proof. exact: sub_seqprod_lexi. Qed.

End TupleLexiOrder.

Module Exports.

HB.reexport TupleLexiOrder.

Notation "n .-tuplelexi[ disp ]" := (type disp n)
  (at level 2, disp at next level, format "n .-tuplelexi[ disp ]") :
  type_scope.
Notation "n .-tuplelexi" := (type_ n)
  (at level 2, format "n .-tuplelexi") : type_scope.

Definition topEtlexi := @topEtlexi.
Definition botEtlexi := @botEtlexi.
Definition sub_tprod_lexi := @sub_tprod_lexi.

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

Lemma le_def A B : A \subset B = (A :&: B == A).
Proof. exact/setIidPl/eqP. Qed.

#[export]
HB.instance Definition _ := Choice.on {subset T}.

#[export]
HB.instance Definition _ := Le_isPreorder.Build disp {subset T}
  (@subxx _ _) (fun A B => @subset_trans _ B A).

#[export]
HB.instance Definition _ := hasBottom.Build disp {subset T} (@sub0set _).

#[export]
HB.instance Definition _ := hasTop.Build disp {subset T} (@subsetT _).

Lemma leEsubset A B : (A <= B) = (A \subset B).
Proof. by []. Qed.

End SetSubsetOrder.

Module Exports.
Arguments type disp T%type.
Notation "{ 'subset' [ d ] T }" := (type d T)
  (at level 0, d at next level, format "{ 'subset' [ d ]  T }") : type_scope.
Notation "{ 'subset' T }" := {subset[subset_display] T}
  (at level 0, format "{ 'subset' T }") : type_scope.

HB.reexport.

Definition leEsubset := @leEsubset.

End Exports.
End SetSubsetOrder.
Export SetSubsetOrder.Exports.

Module DefaultSetSubsetOrder.

HB.instance Definition _ (T : finType) :=
  TBPreorder.copy {set T} {subset T}.

End DefaultSetSubsetOrder.

Notation enum A := (sort <=%O (enum A)).

Section Enum.
Variables (d : disp_t) (T : finPreorderType d).

Lemma cardE (A : {pred T}) : #|A| = size (enum A).
Proof. by rewrite size_sort cardE. Qed.

Lemma mem_enum (A : {pred T}) : enum A =i A.
Proof. by move=> x; rewrite mem_sort mem_enum. Qed.

Lemma enum_uniq (A : {pred T}) : uniq (enum A).
Proof. by rewrite sort_uniq enum_uniq. Qed.

Lemma cardT : #|T| = size (enum T).
Proof. by rewrite cardT size_sort. Qed.

Lemma enumT : enum T = sort <=%O (Finite.enum T).
Proof. by rewrite enumT. Qed.

Lemma enum0 : enum (pred0 : {pred T}) = [::].
Proof. by rewrite enum0. Qed.

Lemma enum1 (x : T) : enum (pred1 x) = [:: x].
Proof. by rewrite enum1. Qed.

Lemma eq_enum (A B : {pred T}) : A =i B -> enum A = enum B.
Proof. by move=> /eq_enum->. Qed.

Lemma eq_cardT (A : {pred T}) : A =i predT -> #|A| = size (enum T).
Proof. by move=> /eq_enum<-; rewrite cardE. Qed.

Lemma set_enum (A : {set T}) : [set x in enum A] = A.
Proof. by apply/setP => x; rewrite inE mem_enum. Qed.

Lemma enum_set0 : enum (set0 : {set T}) = [::].
Proof. by rewrite enum_set0. Qed.

Lemma enum_setT : enum [set: T] = sort <=%O (Finite.enum T).
Proof. by rewrite enum_setT. Qed.

Lemma enum_set1 (a : T) : enum [set a] = [:: a].
Proof. by rewrite enum_set1. Qed.

End Enum.

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

Lemma mono_sorted_enum d d' (T : finPreorderType d)
    (T' : preorderType d') (f : T -> T') :
    total (<=%O : rel T) -> {mono f : x y / (x <= y)%O} ->
  sorted <=%O [seq f x | x <- enum T].
Proof.
move=> /sort_sorted ss_sorted lef; wlog [x0 x'0] : / (T * T')%type.
  by case: (enum T) => // x ? => /(_ (x, f x)).
rewrite (sorted_pairwise le_trans).
apply/(pairwiseP x'0) => i j; rewrite !inE !size_map -!cardT.
move=> ilt jlt ij; rewrite !(nth_map x0) -?cardT// lef.
by rewrite (sorted_leq_nth le_trans le_refl) ?inE -?cardT// 1?ltnW.
Qed.

(* This module should be exported on demand, as in module tagnat below *)
Module Import EnumVal.
Section EnumVal.
Import OrdinalOrder.Exports.
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
move=> x; apply: ord_inj; rewrite insubdK; last first.
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

Module Syntax.
Export PreOSyntax.
Export DualSyntax.
Export DvdSyntax.
End Syntax.

Module Theory.
Export PreorderTheory.
Export PreOCoercions.
Export BPreorderTheory.
Export TPreorderTheory.
Export DualPreorder. (* FIXME? *)

Export OrderMorphismTheory.

Export SubPreorderTheory.
End Theory.

Module Exports.
HB.reexport.
End Exports.

End Order.

Export Order.Exports.

Export Order.Syntax.

Export Order.Preorder.Exports.
Export Order.BPreorder.Exports.
Export Order.TPreorder.Exports.
Export Order.TBPreorder.Exports.
Export Order.FinPreorder.Exports.
Export Order.FinBPreorder.Exports.
Export Order.FinTPreorder.Exports.
Export Order.FinTBPreorder.Exports.

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

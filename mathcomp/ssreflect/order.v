(* (c) Copyright 2006-2019 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice seq.
From mathcomp Require Import path fintype tuple bigop finset div prime finfun.
From mathcomp Require Import finset.

(******************************************************************************)
(* This files defines types equipped with order relations.                    *)
(*                                                                            *)
(* Use one of the following modules implementing different theories:          *)
(*   Order.LTheory: partially ordered types and lattices excluding complement *)
(*                  and totality related theorems.                            *)
(*   Order.CTheory: complemented lattices including Order.LTheory.            *)
(*   Order.TTheory: totally ordered types including Order.LTheory.            *)
(*    Order.Theory: ordered types including all of the above theory modules   *)
(*                                                                            *)
(* To access the definitions, notations, and the theory from, say,            *)
(* "Order.Xyz", insert "Import Order.Xyz." at the top of your scripts.        *)
(* Notations are accessible by opening the scope "order_scope" bound to the   *)
(* delimiting key "O".                                                        *)
(*                                                                            *)
(* We provide the following structures of ordered types                       *)
(*           porderType d == the type of partially ordered types              *)
(*          latticeType d == the type of non-distributive lattices            *)
(*         bLatticeType d == latticeType with a bottom element                *)
(*        tbLatticeType d == latticeType with both a top and a bottom         *)
(*     distrLatticeType d == the type of distributive lattices                *)
(*    bDistrLatticeType d == distrLatticeType with a bottom element           *)
(*   tbDistrLatticeType d == distrLatticeType with both a top and a bottom    *)
(*   cbDistrLatticeType d == the type of sectionally complemented distributive*)
(*                           lattices                                         *)
(*                           (lattices with bottom and a difference operation)*)
(*  ctbDistrLatticeType d == the type of complemented distributive lattices   *)
(*                           (lattices with top, bottom, difference,          *)
(*                            and complement)                                 *)
(*            orderType d == the type of totally ordered types                *)
(*        finPOrderType d == the type of partially ordered finite types       *)
(*       finLatticeType d == the type of nonempty finite non-distributive     *)
(*                           lattices                                         *)
(*  finDistrLatticeType d == the type of nonempty finite distributive lattices*)
(* finCDistrLatticeType d == the type of nonempty finite complemented         *)
(*                           distributive lattices                            *)
(*         finOrderType d == the type of nonempty totally ordered finite types*)
(*                                                                            *)
(* Each generic partial order and lattice operations symbols also has a first *)
(* argument which is the display, the second which is the minimal structure   *)
(* they operate on and then the operands. Here is the exhaustive list of all  *)
(* such symbols for partial orders and lattices together with their default   *)
(* display (as displayed by Check). We document their meaning in the          *)
(* paragraph after the next.                                                  *)
(*                                                                            *)
(* For porderType T                                                           *)
(*   @Order.le          disp T     == <=%O    (in fun_scope)                  *)
(*   @Order.lt          disp T     == <%O     (in fun_scope)                  *)
(*   @Order.comparable  disp T     == >=<%O   (in fun_scope)                  *)
(*   @Order.ge          disp T     == >=%O    (in fun_scope)                  *)
(*   @Order.gt          disp T     == >%O     (in fun_scope)                  *)
(*   @Order.leif        disp T     == <?=%O   (in fun_scope)                  *)
(*   @Order.lteif       disp T     == <?<=%O  (in fun_scope)                  *)
(* For latticeType T                                                          *)
(*   @Order.meet        disp T x y == x `&` y (in order_scope)                *)
(*   @Order.join        disp T x y == x `|` y (in order_scope)                *)
(* For bLatticeType T                                                         *)
(*   @Order.bottom      disp T     == 0       (in order_scope)                *)
(* For tbLatticeType T                                                        *)
(*   @Order.top         disp T     == 1       (in order_scope)                *)
(* For cbDistrLatticeType T                                                   *)
(*   @Order.sub         disp T x y == x `|` y (in order_scope)                *)
(* For ctbDistrLatticeType T                                                  *)
(*   @Order.compl       disp T x   == ~` x    (in order_scope)                *)
(*                                                                            *)
(* This first argument named either d, disp or display, of type unit,         *)
(* configures the printing of notations.                                      *)
(* Instantiating d with tt or an unknown key will lead to a default           *)
(* display for notations, i.e. we have:                                       *)
(* For x, y of type T, where T is canonically a porderType d:                 *)
(*            x <= y <-> x is less than or equal to y.                        *)
(*             x < y <-> x is less than y (:= (y != x) && (x <= y)).          *)
(*           min x y <-> if x < y then x else y                               *)
(*           max x y <-> if x < y then y else x                               *)
(*            x >= y <-> x is greater than or equal to y (:= y <= x).         *)
(*             x > y <-> x is greater than y (:= y < x).                      *)
(*   x <= y ?= iff C <-> x is less than y, or equal iff C is true.            *)
(*    x < y ?<= if C <-> x is smaller than y, and strictly if C is false.     *)
(*           x >=< y <-> x and y are comparable (:= (x <= y) || (y <= x)).    *)
(*            x >< y <-> x and y are incomparable (:= ~~ x >=< y).            *)
(*          f \min g <-> the function x |-> Order.min (f x) (g x);            *)
(*                       f \min g simplifies on application.                  *)
(*          f \max g <-> the function x |-> Order.max (f x) (g x);            *)
(*                       f \max g simplifies on application.                  *)
(* For x, y of type T, where T is canonically a latticeType d:                *)
(*           x `&` y == the meet of x and y.                                  *)
(*           x `|` y == the join of x and y.                                  *)
(* In a type T, where T is canonically a bLatticeType d:                      *)
(*                 0 == the bottom element.                                   *)
(*   \join_<range> e == iterated join of a lattice with a bottom.             *)
(* In a type T, where T is canonically a tbLatticeType d:                     *)
(*                 1 == the top element.                                      *)
(*   \meet_<range> e == iterated meet of a lattice with a top.                *)
(* For x, y of type T, where T is canonically a cbDistrLatticeType d:         *)
(*           x `\` y == the (sectional) complement of y in [0, x].            *)
(* For x of type T, where T is canonically a ctbDistrLatticeType d:           *)
(*              ~` x == the complement of x in [0, 1].                        *)
(*                                                                            *)
(* There are three distinct uses of the symbols                               *)
(*   <, <=, >, >=, _ <= _ ?= iff _, >=<, and ><                               *)
(*   in the default display:                                                  *)
(* they can be 0-ary, unary (prefix), and binary (infix).                     *)
(* 0. <%O, <=%O, >%O, >=%O, <?=%O, >=<%O, and ><%O stand respectively for     *)
(*    lt, le, gt, ge, leif (_ <= _ ?= iff _), comparable, and incomparable.   *)
(* 1. (< x),  (<= x), (> x), (>= x), (>=< x), and (>< x) stand respectively   *)
(*    for (>%O x), (>=%O x), (<%O x), (<=%O x), (>=<%O x), and (><%O x).      *)
(*    So (< x) is a predicate characterizing elements smaller than x.         *)
(* 2. (x < y), (x <= y), ... mean what they are expected to.                  *)
(*  These conventions are compatible with Haskell's,                          *)
(*   where ((< y) x) = (x < y) = ((<) x y),                                   *)
(*   except that we write <%O instead of (<).                                 *)
(*                                                                            *)
(* Alternative notation displays can be defined by :                          *)
(* 1. declaring a new opaque definition of type unit. Using the idiom         *)
(*    `Lemma my_display : unit. Proof. exact: tt. Qed.`                       *)
(* 2. using this symbol to tag canonical porderType structures using          *)
(*    `Canonical my_porderType := POrderType my_display my_type my_mixin`,    *)
(* 3. declaring notations for the main operations of this library, by         *)
(*    setting the first argument of the definition to the display, e.g.       *)
(*    `Notation my_syndef_le x y := @Order.le my_display _ x y.` or           *)
(*    `Notation "x <=< y" := @Order.lt my_display _ x y (at level ...).`      *)
(*    Non overloaded notations will default to the default display.           *)
(*                                                                            *)
(* One may use displays either for convenience or to disambiguate between     *)
(* different structures defined on "copies" of a type (as explained below.)   *)
(* We provide the following "copies" of types,                                *)
(* the first one is a *documented example*                                    *)
(*            natdvd := nat                                                   *)
(*                   == a "copy" of nat which is canonically ordered using    *)
(*                      divisibility predicate dvdn.                          *)
(*                      Notation %|, %<|, gcd, lcm are used instead of        *)
(*                      <=, <, meet and join.                                 *)
(*              T^d  := dual T,                                               *)
(*                      where dual is a new definition for (fun T => T)       *)
(*                   == a "copy" of T, such that if T is canonically ordered, *)
(*                      then T^d is canonically ordered with the dual         *)
(*                      order, and displayed with an extra ^d in the notation *)
(*                      i.e. <=^d, <^d, >=<^d, ><^d, `&`^d, `|`^d are         *)
(*                      used and displayed instead of                         *)
(*                      <=, <, >=<, ><, `&`, `|`                              *)
(*     T *prod[d] T' := T * T'                                                *)
(*                   == a "copy" of the cartesian product such that,          *)
(*                      if T and T' are canonically ordered,                  *)
(*                      then T *prod[d] T' is canonically ordered in product  *)
(*                      order.                                                *)
(*                      i.e. (x1, x2) <= (y1, y2) =                           *)
(*                             (x1 <= y1) && (x2 <= y2),                      *)
(*                      and displayed in display d                            *)
(*           T *p T' := T *prod[prod_display] T'                              *)
(*                      where prod_display adds an extra ^p to all notations  *)
(*     T *lexi[d] T' := T * T'                                                *)
(*                   == a "copy" of the cartesian product such that,          *)
(*                      if T and T' are canonically ordered,                  *)
(*                      then T *lexi[d] T' is canonically ordered in          *)
(*                      lexicographic order                                   *)
(*                      i.e. (x1, x2) <= (y1, y2) =                           *)
(*                             (x1 <= y1) && ((x1 >= y1) ==> (x2 <= y2))      *)
(*                      and  (x1, x2) < (y1, y2) =                            *)
(*                             (x1 <= y1) && ((x1 >= y1) ==> (x2 < y2))       *)
(*                      and displayed in display d                            *)
(*           T *l T' := T *lexi[lexi_display] T'                              *)
(*                      where lexi_display adds an extra ^l to all notations  *)
(*  seqprod_with d T := seq T                                                 *)
(*                   == a "copy" of seq, such that if T is canonically        *)
(*                      ordered, then seqprod_with d T is canonically ordered *)
(*                      in product order i.e.                                 *)
(*                      [:: x1, .., xn] <= [y1, .., yn] =                     *)
(*                        (x1 <= y1) && ... && (xn <= yn)                     *)
(*                      and displayed in display d                            *)
(* n.-tupleprod[d] T == same with n.tuple T                                   *)
(*         seqprod T := seqprod_with prod_display T                           *)
(*    n.-tupleprod T := n.-tuple[prod_display] T                              *)
(*  seqlexi_with d T := seq T                                                 *)
(*                   == a "copy" of seq, such that if T is canonically        *)
(*                      ordered, then seqprod_with d T is canonically ordered *)
(*                      in lexicographic order i.e.                           *)
(*                      [:: x1, .., xn] <= [y1, .., yn] =                     *)
(*                        (x1 <= x2) && ((x1 >= y1) ==> ((x2 <= y2) && ...))  *)
(*                      and displayed in display d                            *)
(* n.-tuplelexi[d] T == same with n.tuple T                                   *)
(*         seqlexi T := lexiprod_with lexi_display T                          *)
(*    n.-tuplelexi T := n.-tuple[lexi_display] T                              *)
(*     {subset[d] T} := {set T}                                               *)
(*                   == a "copy" of set which is canonically ordered by the   *)
(*                      subset order and displayed in display d               *)
(*        {subset T} := {subset[subset_display] T}                            *)
(*                                                                            *)
(* Beware that canonical structure inference will not try to find the copy of *)
(* the structures that fits the display one mentioned, but will rather        *)
(* determine which canonical structure and display to use depending on the    *)
(* copy of the type one provided. In this sense they are merely displays      *)
(* to inform the user of what the inference did, rather than additional       *)
(* input for the inference.                                                   *)
(*                                                                            *)
(* Existing displays are either dual_display d (where d is a display),        *)
(* dvd_display (both explained above), ring_display (from algebra/ssrnum      *)
(* to change the scope of the usual notations to ring_scope). We also provide *)
(* lexi_display and prod_display for lexicographic and product order          *)
(* respectively.                                                              *)
(* The default display is tt and users can define their own as explained      *)
(* above.                                                                     *)
(*                                                                            *)
(* For porderType we provide the following operations                         *)
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
(* In order to build the above structures, one must provide the appropriate   *)
(* factory instance to the following structure constructors. The list of      *)
(* possible factories is indicated after each constructor. Each factory is    *)
(* documented in the next paragraph.                                          *)
(* NB: Since each mixim_of record of structure in this library is an internal *)
(* interface that is not designed to be used by users directly, one should    *)
(* not build structure instances from their Mixin constructors.               *)
(*                                                                            *)
(* POrderType disp T pord_mixin                                               *)
(*                  == builds a porderType from a canonical choiceType        *)
(*                     instance of T where pord_mixin can be of types         *)
(*                       lePOrderMixin, ltPOrderMixin, meetJoinMixin,         *)
(*                       leOrderMixin, or ltOrderMixin                        *)
(*                     or computed using PcanPOrderMixin or CanPOrderMixin.   *)
(*                     disp is a display as explained above                   *)
(*                                                                            *)
(* LatticeType T lat_mixin                                                    *)
(*                  == builds a latticeType from a porderType where lat_mixin *)
(*                     can be of types                                        *)
(*                       latticeMixin, distrLatticePOrderMixin,               *)
(*                       totalPOrderMixin, meetJoinMixin, leOrderMixin, or    *)
(*                       ltOrderMixin                                         *)
(*                     or computed using IsoLatticeMixin.                     *)
(*                                                                            *)
(* BLatticeType T bot_mixin                                                   *)
(*                  == builds a bLatticeType from a latticeType and bottom    *)
(*                     where bot_mixin is of type bottomMixin.                *)
(*                                                                            *)
(* TBLatticeType T top_mixin                                                  *)
(*                  == builds a tbLatticeType from a bLatticeType and top     *)
(*                     where top_mixin is of type topMixin.                   *)
(*                                                                            *)
(* DistrLatticeType T lat_mixin                                               *)
(*                  == builds a distrLatticeType from a porderType where      *)
(*                     lat_mixin can be of types                              *)
(*                       distrLatticeMixin, distrLatticePOrderMixin,          *)
(*                       totalLatticeMixin, totalPOrderMixin, meetJoinMixin,  *)
(*                       leOrderMixin, or ltOrderMixin                        *)
(*                     or computed using IsoLatticeMixin.                     *)
(*                                                                            *)
(* CBDistrLatticeType T sub_mixin                                             *)
(*                  == builds a cbDistrLatticeType from a bDistrLatticeType   *)
(*                     and a difference operation where sub_mixin is of type  *)
(*                     cbDistrLatticeMixin.                                   *)
(*                                                                            *)
(* CTBDistrLatticeType T compl_mixin                                          *)
(*                  == builds a ctbDistrLatticeType from a tbDistrLatticeType *)
(*                     and a complement operation where compl_mixin is of     *)
(*                     type ctbDistrLatticeMixin.                             *)
(*                                                                            *)
(* OrderType T ord_mixin                                                      *)
(*                  == builds an orderType from a distrLatticeType where      *)
(*                     ord_mixin can be of types                              *)
(*                       totalOrderMixin, totalPOrderMixin, totalLatticeMixin,*)
(*                       leOrderMixin, or ltOrderMixin                        *)
(*                     or computed using MonoTotalMixin.                      *)
(*                                                                            *)
(* Additionally:                                                              *)
(* - [porderType of _] ... notations are available to recover structures on   *)
(*    "copies" of the types, as in eqType, choiceType, ssralg...              *)
(* - [finPOrderType of _] ... notations to compute joins between finite types *)
(*                            and ordered types                               *)
(*                                                                            *)
(* List of possible factories:                                                *)
(*                                                                            *)
(* - lePOrderMixin == on a choiceType, takes le, lt,                          *)
(*                    reflexivity, antisymmetry and transitivity of le.       *)
(*                    (can build:  porderType)                                *)
(*                                                                            *)
(* - ltPOrderMixin == on a choiceType, takes le, lt,                          *)
(*                    irreflexivity and transitivity of lt.                   *)
(*                    (can build:  porderType)                                *)
(*                                                                            *)
(* - latticeMixin == on a porderType, takes meet, join,                       *)
(*                   commutativity and associativity of meet and join, and    *)
(*                   some absorption laws.                                    *)
(*                   (can build:  latticeType)                                *)
(*                                                                            *)
(* - distrLatticeMixin ==                                                     *)
(*                   on a latticeType, takes distributivity of meet over join.*)
(*                   (can build:  distrLatticeType)                           *)
(*                                                                            *)
(* - distrLatticePOrderMixin == on a porderType, takes meet, join,            *)
(*                   commutativity and associativity of meet and join, and    *)
(*                   the absorption and distributive laws.                    *)
(*                   (can build:  latticeType, distrLatticeType)              *)
(*                                                                            *)
(* - meetJoinMixin == on a choiceType, takes le, lt, meet, join,              *)
(*                    commutativity and associativity of meet and join,       *)
(*                    the absorption and distributive laws, and               *)
(*                    idempotence of meet.                                    *)
(*                    (can build:  porderType, latticeType, distrLatticeType) *)
(*                                                                            *)
(* - meetJoinLeMixin == on a porderType, takes meet, join, and a proof that   *)
(*                    those are respectvely the greatest lower bound and the  *)
(*                    least upper bound.                                      *)
(*                    (can build: latticeType)                                *)
(*                                                                            *)
(* - leOrderMixin == on a choiceType, takes le, lt, meet, join,               *)
(*                   antisymmetry, transitivity and totality of le.           *)
(*                   (can build:  porderType, latticeType, distrLatticeType,  *)
(*                                orderType)                                  *)
(*                                                                            *)
(* - ltOrderMixin == on a choiceType, takes le, lt, meet, join,               *)
(*                   irreflexivity, transitivity and totality of lt.          *)
(*                   (can build:  porderType, latticeType, distrLatticeType,  *)
(*                                orderType)                                  *)
(*                                                                            *)
(* - totalPOrderMixin == on a porderType T, totality of the order of T        *)
(*                    := total (<=%O : rel T)                                 *)
(*                   (can build: latticeType, distrLatticeType, orderType)    *)
(*                                                                            *)
(* - totalLatticeMixin == on a latticeType T, totality of the order of T      *)
(*                    := total (<=%O : rel T)                                 *)
(*                   (can build distrLatticeType, orderType)                  *)
(*                                                                            *)
(* - totalOrderMixin == on a distrLatticeType T, totality of the order of T   *)
(*                    := total (<=%O : rel T)                                 *)
(*                   (can build: orderType)                                   *)
(*    NB: the above three mixins are kept separate from each other (even      *)
(*        though they are convertible), in order to avoid ambiguous coercion  *)
(*        paths.                                                              *)
(*                                                                            *)
(* - bottomMixin, topMixin, cbDistrLatticeMixin, ctbDistrLatticeMixin         *)
(*                == mixins with one extra operation                          *)
(*                   (respectively bottom, top, difference, and complement)   *)
(*                                                                            *)
(* Additionally:                                                              *)
(* - [porderMixin of T by <:] creates a porderMixin by subtyping.             *)
(* - [totalOrderMixin of T by <:] creates the associated totalOrderMixin.     *)
(* - PCanPOrderMixin, CanPOrderMixin create porderMixin from cancellations    *)
(* - MonoTotalMixin creates a totalPOrderMixin from monotonicity              *)
(* - IsoLatticeMixin creates a distrLatticeMixin from an ordered structure    *)
(*   isomorphism (i.e., cancel f f', cancel f' f, {mono f : x y / x <= y})    *)
(*                                                                            *)
(* List of "big pack" notations:                                              *)
(* - DistrLatticeOfChoiceType builds a distrLatticeType from a choiceType and *)
(*   a meetJoinMixin.                                                         *)
(* - DistrLatticeOfPOrderType builds a distrLatticeType from a porderType and *)
(*   a distrLatticePOrderMixin.                                               *)
(* - OrderOfChoiceType builds an orderType from a choiceType, and a           *)
(*   leOrderMixin or a ltOrderMixin.                                          *)
(* - OrderOfPOrder builds an orderType from a porderType and a                *)
(*   totalPOrderMixin.                                                        *)
(* - OrderOfLattice builds an orderType from a latticeType and a              *)
(*   totalLatticeMixin.                                                       *)
(* NB: These big pack notations should be used only to construct instances on *)
(*     the fly, e.g., in the middle of a proof, and should not be used to     *)
(*     declare canonical instances. See field/algebraics_fundamentals.v for   *)
(*     an example usage.                                                      *)
(*                                                                            *)
(* We provide the following canonical instances of ordered types              *)
(* - all possible structures on bool                                          *)
(* - porderType, latticeType, distrLatticeType, orderType and bLatticeType    *)
(*   on nat for the leq order                                                 *)
(* - porderType, latticeType, distrLatticeType, orderType and finPOrderType   *)
(*   on 'I_n and bLatticeType, tbLatticeType, bDistrLatticeType,              *)
(*   tbDistrLatticeType, finLatticeType, finDistrLatticeType and finOrderType *)
(*   on 'I_n.+1 (to guarantee it is nonempty).                                *)
(* - porderType, latticeType, distrLatticeType, bLatticeType, tbLatticeType,  *)
(*   on nat for the dvdn order, where meet and join are respectively gcdn and *)
(*   lcmn                                                                     *)
(* - porderType, latticeType, distrLatticeType, orderType, bLatticeType,      *)
(*   tbLatticeType, cbDistrLatticeType, ctbDistrLatticeType                   *)
(*   on T *prod[disp] T' a "copy" of T * T'                                   *)
(*     using product order (and T *p T' its specialization to prod_display)   *)
(* - porderType, latticeType, distrLatticeType, and orderType, on             *)
(*     T *lexi[disp] T' another "copy" of T * T', with lexicographic ordering *)
(*     (and T *l T' its specialization to lexi_display)                       *)
(* - porderType, latticeType, distrLatticeType, and orderType, on             *)
(*     {t : T & T' x} with lexicographic ordering                             *)
(* - porderType, latticeType, distrLatticeType, orderType, bLatticeType,      *)
(*   tbLatticeType, cbDistrLatticeType, ctbDistrLatticeType                   *)
(*   on seqprod_with disp T a "copy" of seq T                                 *)
(*     using product order (and seqprod T' its specialization to prod_display)*)
(* - porderType, latticeType, distrLatticeType, and orderType, on             *)
(*     seqlexi_with disp T another "copy" of seq T, with lexicographic        *)
(*     ordering (and seqlexi T its specialization to lexi_display)            *)
(* - porderType, latticeType, distrLatticeType, orderType, bLatticeType,      *)
(*   tbLatticeType, cbDistrLatticeType, ctbDistrLatticeType                   *)
(*   on n.-tupleprod[disp] a "copy" of n.-tuple T                             *)
(*     using product order (and n.-tupleprod T its specialization             *)
(*     to prod_display)                                                       *)
(* - porderType, latticeType, distrLatticeType, and orderType, on             *)
(*     n.-tuplelexi[d] T another "copy" of n.-tuple T, with lexicographic     *)
(*     ordering (and n.-tuplelexi T its specialization to lexi_display)       *)
(* - porderType, latticeType, distrLatticeType, orderType, bLatticeType,      *)
(*   tbLatticeType, cbDistrLatticeType, ctbDistrLatticeType                   *)
(*   on {subset[disp] T} a "copy" of {set T} using subset order               *)
(*     (and {subset T} its specialization to subset_display)                  *)
(* and all possible finite type instances                                     *)
(*                                                                            *)
(* In order to get a canonical order on prod, seq, tuple or set, one may      *)
(*   import modules DefaultProdOrder or DefaultProdLexiOrder,                 *)
(*   DefaultSeqProdOrder or DefaultSeqLexiOrder,                              *)
(*   DefaultTupleProdOrder or DefaultTupleLexiOrder                           *)
(*   and DefaultSetSubsetOrder.                                               *)
(*                                                                            *)
(* On orderType, leP ltP ltgtP are the three main lemmas for case analysis.   *)
(* On porderType, one may use comparableP, comparable_leP, comparable_ltP,    *)
(*   and comparable_ltgtP, which are the four main lemmas for case analysis.  *)
(*                                                                            *)
(* We also provide specialized versions of some theorems from path.v.         *)
(*                                                                            *)
(* We provide Order.enum_val, Order.enum_rank, and Order.enum_rank_in, which  *)
(* are monotonous variations of enum_val, enum_rank, and enum_rank_in         *)
(* whenever the type is porderType, and their monotonicity is provided if     *)
(* this order is total. The theory is in the module Order (Order.enum_valK,   *)
(* Order.enum_rank_inK, etc) but Order.Enum can be imported to shorten these. *)
(******************************************************************************)
(* We provide an opaque monotonous bijection tagnat.sig / tagnat.rank between *)
(* the finite types {i : 'I_n & 'I_(p_ i)} and 'I_(\sum_i p_ i):              *)
(*  tagnat.sig  : 'I_(\sum_i p_ i) -> {i : 'I_n & 'I_(p_ i)}                  *)
(*  tagnat.rank : {i : 'I_n & 'I_(p_ i)} -> 'I_(\sum_i p_ i)                  *)
(*  tagnat.sig1 : 'I_(\sum_i p_ i) -> 'I_n                                    *)
(*  tagnat.sig2 : forall p : 'I_(\sum_i p_ i), 'I_(p_ (tagnat.sig1 p))        *)
(*  tagnat.Rank : forall i, 'I_(p_ i) -> 'I_(\sum_i p_ i)                     *)
(******************************************************************************)
(* This file is based on prior work by                                        *)
(* D. Dreyer, G. Gonthier, A. Nanevski, P-Y Strub, B. Ziliani                 *)
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

(* Reserved notation for lattice operations. *)
Reserved Notation "A `&` B"  (at level 48, left associativity).
Reserved Notation "A `|` B" (at level 52, left associativity).
Reserved Notation "A `\` B" (at level 50, left associativity).
Reserved Notation "~` A" (at level 35, right associativity).

(* Notations for dual partial and total order *)
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

(* Reserved notation for dual lattice operations. *)
Reserved Notation "A `&^d` B"  (at level 48, left associativity).
Reserved Notation "A `|^d` B" (at level 52, left associativity).
Reserved Notation "A `\^d` B" (at level 50, left associativity).
Reserved Notation "~^d` A" (at level 35, right associativity).

Reserved Notation "0^d" (at level 0).
Reserved Notation "1^d" (at level 0).

(* Reserved notations for product ordering of prod or seq *)
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

(* Reserved notation for dual lattice operations. *)
Reserved Notation "A `&^p` B"  (at level 48, left associativity).
Reserved Notation "A `|^p` B" (at level 52, left associativity).
Reserved Notation "A `\^p` B" (at level 50, left associativity).
Reserved Notation "~^p` A" (at level 35, right associativity).

(* Reserved notations for lexicographic ordering of prod or seq *)
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

(* Reserved notations for divisibility *)
Reserved Notation "x %<| y"  (at level 70, no associativity).

Reserved Notation "\gcd_ i F"
  (at level 41, F at level 41, i at level 0,
           format "'[' \gcd_ i '/  '  F ']'").
Reserved Notation "\gcd_ ( i <- r | P ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \gcd_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\gcd_ ( i <- r ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \gcd_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\gcd_ ( m <= i < n | P ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \gcd_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\gcd_ ( m <= i < n ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \gcd_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\gcd_ ( i | P ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \gcd_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\gcd_ ( i : t | P ) F"
  (at level 41, F at level 41, i at level 50).
Reserved Notation "\gcd_ ( i : t ) F"
  (at level 41, F at level 41, i at level 50).
Reserved Notation "\gcd_ ( i < n | P ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \gcd_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\gcd_ ( i < n ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \gcd_ ( i  <  n )  F ']'").
Reserved Notation "\gcd_ ( i 'in' A | P ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \gcd_ ( i  'in'  A  |  P ) '/  '  F ']'").
Reserved Notation "\gcd_ ( i 'in' A ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \gcd_ ( i  'in'  A ) '/  '  F ']'").

Reserved Notation "\lcm_ i F"
  (at level 41, F at level 41, i at level 0,
           format "'[' \lcm_ i '/  '  F ']'").
Reserved Notation "\lcm_ ( i <- r | P ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \lcm_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\lcm_ ( i <- r ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \lcm_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\lcm_ ( m <= i < n | P ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \lcm_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\lcm_ ( m <= i < n ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \lcm_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\lcm_ ( i | P ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \lcm_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\lcm_ ( i : t | P ) F"
  (at level 41, F at level 41, i at level 50).
Reserved Notation "\lcm_ ( i : t ) F"
  (at level 41, F at level 41, i at level 50).
Reserved Notation "\lcm_ ( i < n | P ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \lcm_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\lcm_ ( i < n ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \lcm_ ( i  <  n )  F ']'").
Reserved Notation "\lcm_ ( i 'in' A | P ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \lcm_ ( i  'in'  A  |  P ) '/  '  F ']'").
Reserved Notation "\lcm_ ( i 'in' A ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \lcm_ ( i  'in'  A ) '/  '  F ']'").

(* Reserved notation for dual lattice operations. *)
Reserved Notation "A `&^l` B"  (at level 48, left associativity).
Reserved Notation "A `|^l` B" (at level 52, left associativity).
Reserved Notation "A `\^l` B" (at level 50, left associativity).
Reserved Notation "~^l` A" (at level 35, right associativity).

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
  (at level 41, F at level 41, i at level 50).
Reserved Notation "\meet_ ( i : t ) F"
  (at level 41, F at level 41, i at level 50).
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
  (at level 41, F at level 41, i at level 50).
Reserved Notation "\join_ ( i : t ) F"
  (at level 41, F at level 41, i at level 50).
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

Reserved Notation "\meet^d_ i F"
  (at level 41, F at level 41, i at level 0,
           format "'[' \meet^d_ i '/  '  F ']'").
Reserved Notation "\meet^d_ ( i <- r | P ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \meet^d_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\meet^d_ ( i <- r ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \meet^d_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\meet^d_ ( m <= i < n | P ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \meet^d_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\meet^d_ ( m <= i < n ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \meet^d_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\meet^d_ ( i | P ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \meet^d_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\meet^d_ ( i : t | P ) F"
  (at level 41, F at level 41, i at level 50).
Reserved Notation "\meet^d_ ( i : t ) F"
  (at level 41, F at level 41, i at level 50).
Reserved Notation "\meet^d_ ( i < n | P ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \meet^d_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\meet^d_ ( i < n ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \meet^d_ ( i  <  n )  F ']'").
Reserved Notation "\meet^d_ ( i 'in' A | P ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \meet^d_ ( i  'in'  A  |  P ) '/  '  F ']'").
Reserved Notation "\meet^d_ ( i 'in' A ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \meet^d_ ( i  'in'  A ) '/  '  F ']'").

Reserved Notation "\join^d_ i F"
  (at level 41, F at level 41, i at level 0,
           format "'[' \join^d_ i '/  '  F ']'").
Reserved Notation "\join^d_ ( i <- r | P ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \join^d_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\join^d_ ( i <- r ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \join^d_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\join^d_ ( m <= i < n | P ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \join^d_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\join^d_ ( m <= i < n ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \join^d_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\join^d_ ( i | P ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \join^d_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\join^d_ ( i : t | P ) F"
  (at level 41, F at level 41, i at level 50).
Reserved Notation "\join^d_ ( i : t ) F"
  (at level 41, F at level 41, i at level 50).
Reserved Notation "\join^d_ ( i < n | P ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \join^d_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\join^d_ ( i < n ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \join^d_ ( i  <  n )  F ']'").
Reserved Notation "\join^d_ ( i 'in' A | P ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \join^d_ ( i  'in'  A  |  P ) '/  '  F ']'").
Reserved Notation "\join^d_ ( i 'in' A ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \join^d_ ( i  'in'  A ) '/  '  F ']'").

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

Reserved Notation "\meet^p_ i F"
  (at level 41, F at level 41, i at level 0,
           format "'[' \meet^p_ i '/  '  F ']'").
Reserved Notation "\meet^p_ ( i <- r | P ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \meet^p_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\meet^p_ ( i <- r ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \meet^p_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\meet^p_ ( m <= i < n | P ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \meet^p_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\meet^p_ ( m <= i < n ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \meet^p_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\meet^p_ ( i | P ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \meet^p_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\meet^p_ ( i : t | P ) F"
  (at level 41, F at level 41, i at level 50).
Reserved Notation "\meet^p_ ( i : t ) F"
  (at level 41, F at level 41, i at level 50).
Reserved Notation "\meet^p_ ( i < n | P ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \meet^p_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\meet^p_ ( i < n ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \meet^p_ ( i  <  n )  F ']'").
Reserved Notation "\meet^p_ ( i 'in' A | P ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \meet^p_ ( i  'in'  A  |  P ) '/  '  F ']'").
Reserved Notation "\meet^p_ ( i 'in' A ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \meet^p_ ( i  'in'  A ) '/  '  F ']'").

Reserved Notation "\join^p_ i F"
  (at level 41, F at level 41, i at level 0,
           format "'[' \join^p_ i '/  '  F ']'").
Reserved Notation "\join^p_ ( i <- r | P ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \join^p_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\join^p_ ( i <- r ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \join^p_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\join^p_ ( m <= i < n | P ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \join^p_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\join^p_ ( m <= i < n ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \join^p_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\join^p_ ( i | P ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \join^p_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\join^p_ ( i : t | P ) F"
  (at level 41, F at level 41, i at level 50).
Reserved Notation "\join^p_ ( i : t ) F"
  (at level 41, F at level 41, i at level 50).
Reserved Notation "\join^p_ ( i < n | P ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \join^p_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\join^p_ ( i < n ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \join^p_ ( i  <  n )  F ']'").
Reserved Notation "\join^p_ ( i 'in' A | P ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \join^p_ ( i  'in'  A  |  P ) '/  '  F ']'").
Reserved Notation "\join^p_ ( i 'in' A ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \join^p_ ( i  'in'  A ) '/  '  F ']'").

Module Order.

(**************)
(* STRUCTURES *)
(**************)

HB.mixin Record isPOrdered (d : unit) T of hasDecEq T := {
  le       : rel T;
  lt       : rel T;
  lt_def   : forall x y, lt x y = (y != x) && (le x y);
  le_refl  : reflexive     le;
  le_anti  : antisymmetric le;
  le_trans : transitive    le;
}.

#[short(type="porderType")]
HB.structure Definition POrder (d : unit) :=
  { T of Choice T & isPOrdered d T }.

HB.factory Record isLePOrdered (d : unit) T of hasDecEq T := {
  le       : rel T;
  le_refl  : reflexive     le;
  le_anti  : antisymmetric le;
  le_trans : transitive    le;
}.

HB.builders Context (d : unit) T of isLePOrdered d T.
(* TODO: print nice error message when keyed type is not provided *)
HB.instance Definition _ := @isPOrdered.Build d T
  le _ (fun _ _ => erefl) le_refl le_anti le_trans.
HB.end.

HB.factory Record isLtLePOrdered (d : unit) T of hasDecEq T := {
  le : rel T;
  lt : rel T;
  le_def   : forall x y, le x y = (x == y) || lt x y;
  lt_irr   : irreflexive lt;
  lt_trans : transitive lt;
}.
HB.builders Context (d : unit) T of isLtLePOrdered d T.

Let le_refl : reflexive le. Proof. by move=> x; rewrite le_def eqxx. Qed.

Let le_anti : antisymmetric le.
Proof.
move=> x y; rewrite !le_def [y == _]eq_sym.
have [//|neq_xy/=] := eqVneq x y => /andP[xy yx].
by have := lt_trans xy yx; rewrite lt_irr.
Qed.

Let le_trans : transitive le.
Proof.
move=> y x z; rewrite !le_def; case: (eqVneq x y) => [->|]//= neq_xy.
by case: (eqVneq y z) => /= [<- ->|_ /lt_trans yx /yx ->]; rewrite orbT.
Qed.

Let lt_def x y : lt x y = (y != x) && (le x y).
Proof. by rewrite le_def; case: eqVneq => //= ->; rewrite lt_irr. Qed.

HB.instance Definition _ := @isPOrdered.Build d T
  le lt lt_def le_refl le_anti le_trans.

HB.end.

HB.factory Record isLtPOrdered (d : unit) T of hasDecEq T := {
  lt       : rel T;
  lt_irr   : irreflexive lt;
  lt_trans : transitive  lt;
}.
#[key="T"]
HB.builders Context (d : unit) (T : Type) of isLtPOrdered d T.
HB.instance Definition _ := @isLtLePOrdered.Build d T
  _ lt (fun _ _ => erefl) lt_irr lt_trans.
HB.end.

Module POrderExports.
Arguments le_trans {d s} [_ _ _].
Notation "[ 'porderType' 'of' T 'for' cT ]" := (POrder.clone _ T%type cT)
  (at level 0, format "[ 'porderType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'porderType' 'of' T 'for' cT 'with' disp ]" :=
  (POrder.clone disp T%type cT)
  (at level 0, format "[ 'porderType'  'of'  T  'for'  cT  'with'  disp ]") :
  form_scope.
Notation "[ 'porderType' 'of' T ]" := [porderType of T%type for _]
  (at level 0, format "[ 'porderType'  'of'  T ]") : form_scope.
Notation "[ 'porderType' 'of' T 'with' disp ]" :=
  [porderType of T%type for _ with disp]
  (at level 0, format "[ 'porderType'  'of'  T  'with' disp ]") : form_scope.
End POrderExports.
HB.export POrderExports.
(* Bind Scope order_scope with POrder.sort. *)

Section POrderDef.

Variable (disp : unit) (T : porderType disp).

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
Definition arg_max {I : finType}  := @extremum T I ge.

(* Lifted min/max operations. *)
Section LiftedPOrder.
Variable T' : Type.
Implicit Type f : T' -> T.
Definition min_fun f g x := min (f x) (g x).
Definition max_fun f g x := max (f x) (g x).
End LiftedPOrder.

End POrderDef.

Prenex Implicits lt le leif lteif.
Arguments ge {_ _}.
Arguments gt {_ _}.
Arguments min {_ _}.
Arguments max {_ _}.
Arguments comparable {_ _}.
Arguments min_fun {_ _ _} f g _ /.
Arguments max_fun {_ _ _} f g _ /.

Module Import POSyntax.

Notation "<=%O" := le : fun_scope.
Notation ">=%O" := ge : fun_scope.
Notation "<%O" := lt : fun_scope.
Notation ">%O" := gt : fun_scope.
Notation "<?=%O" := leif : fun_scope.
Notation "<?<=%O" := lteif : fun_scope.
Notation ">=<%O" := comparable : fun_scope.
Notation "><%O" := (fun x y => ~~ (comparable x y)) : fun_scope.

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

Notation "f \min g" := (min_fun f g) : order_scope.
Notation "f \max g" := (max_fun f g) : order_scope.

Notation leLHS := (X in (X <= _)%O)%pattern.
Notation leRHS := (X in (_ <= X)%O)%pattern.
Notation ltLHS := (X in (X < _)%O)%pattern.
Notation ltRHS := (X in (_ < X)%O)%pattern.

End POSyntax.
HB.export POSyntax.

Module POCoercions.
Coercion le_of_leif : leif >-> is_true.
End POCoercions.
HB.export POCoercions.

(* HB.mixin Record POrder_isJoinSemiLattice *)
(*     d (T : indexed Type) of POrder d T := { *)
(*   join : T -> T -> T; *)
(*   joinC : commutative join; *)
(*   joinA : associative join; *)
(*   le_defU : forall x y, (x <= y) = (join x y == y); *)
(* }. *)
(* #[short(type="joinSemiLatticeType")] *)
(* HB.structure Definition JoinSemiLattice d := *)
(*   { T of POrder_isJoinSemiLattice d T & POrder d T }. *)

(* HB.mixin Record POrder_isMeetSemiLattice *)
(*     d (T : indexed Type) of POrder d T := { *)
(*   meet : T -> T -> T; *)
(*   meetC : commutative meet; *)
(*   meetA : associative meet; *)
(*   le_def : forall x y, (x <= y) = (meet x y == x); *)
(* }. *)
(* #[short(type="meetSemiLatticeType")] *)
(* HB.structure Definition MeetSemiLattice d := *)
(*   { T of POrder_isMeetSemiLattice d T & POrder d T }. *)

#[key="T"]
HB.mixin Record POrder_isLattice d (T : Type) of POrder d T := {
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
(* HB.builders Context d T of POrder_isLattice d T. *)

(* Let le_defU : forall x y, (x <= y) = (join x y == y). *)
(* Proof. Admitted. *)

(* HB.instance Definition _ := @POrder_isMeetSemiLattice.Build d T *)
(*   meet meetC meetA le_def. *)
(* HB.instance Definition _ := @POrder_isJoinSemiLattice.Build d T *)
(*   join joinC joinA le_defU. *)
(* HB.end. *)

#[short(type="latticeType")]
HB.structure Definition Lattice d :=
  { T of POrder_isLattice d T & POrder d T }.

Module LatticeExports.
Notation "[ 'latticeType' 'of' T 'for' cT ]" := (Lattice.clone _ T%type cT)
  (at level 0, format "[ 'latticeType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'latticeType' 'of' T 'for' cT 'with' disp ]" :=
  (Lattice.clone disp T%type cT)
  (at level 0, format "[ 'latticeType'  'of'  T  'for'  cT  'with'  disp ]") :
  form_scope.
Notation "[ 'latticeType' 'of' T ]" := [latticeType of T%type for _]
  (at level 0, format "[ 'latticeType'  'of'  T ]") : form_scope.
Notation "[ 'latticeType' 'of' T 'with' disp ]" :=
  [latticeType of T%type for _ with disp]
  (at level 0, format "[ 'latticeType'  'of'  T  'with' disp ]") : form_scope.
End LatticeExports.
HB.export LatticeExports.

Section LatticeDef.
Context {disp : unit} {T : latticeType disp}.

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

#[key="T"]
HB.mixin Record hasBottom d (T : Type) of POrder d T := {
  bottom : T;
  le0x : forall x, bottom <= x;
}.
(* TODO: Restore when we remove the mathcomp attribute *)
(* HB.structure Definition BPOrder d := { T of hasBottom d T & POrder d T }. *)
#[short(type="bLatticeType")]
HB.structure Definition BLattice d := { T of hasBottom d T & Lattice d T }.

Module BLatticeExports.
Notation "[ 'bLatticeType' 'of' T 'for' cT ]" := (BLattice.clone _ T%type cT)
  (at level 0, format "[ 'bLatticeType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'bLatticeType' 'of' T ]" := [bLatticeType of T%type for _]
  (at level 0, format "[ 'bLatticeType'  'of'  T ]") : form_scope.
(* Notation "[ 'bLatticeType' 'of' T 'for' cT 'with' disp ]" := *)
(*   (@clone_with T _ cT disp _ id) *)
(*   (at level 0, *)
(*    format "[ 'bLatticeType'  'of'  T  'for'  cT  'with'  disp ]") : *)
(*   form_scope. *)
(* Notation "[ 'bLatticeType' 'of' T 'with' disp ]" := *)
(*   [bLatticeType of T for _ with disp] *)
(*   (at level 0, format "[ 'bLatticeType'  'of'  T  'with' disp ]") : *)
(*   form_scope. *)
End BLatticeExports.
HB.export BLatticeExports.

Module BLatticeSyntax.
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
HB.export BLatticeSyntax.

#[key="T"]
HB.mixin Record hasTop d (T : Type) of POrder d T := {
  top : T;
  lex1 : forall x, x <= top;
}.
(* TODO: Restore when we remove the mathcomp attribute *)
(* HB.structure Definition TPOrder d := { T of hasBottom d T & POrder d T }. *)
(* HB.structure Definition TLattice d := { T of hasTop d T & Lattice d T }. *)
(* HB.structure Definition TBOrder d := { T of hasTop d T & BPOrder d T }. *)
#[short(type="tbLatticeType")]
HB.structure Definition TBLattice d := { T of hasTop d T & BLattice d T }.

Module TBLatticeExports.
(* FIXME: clone? *)
End TBLatticeExports.
HB.export TBLatticeExports.

Module TBLatticeSyntax.

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
HB.export TBLatticeSyntax.

(* TODO: rename to lattice_ismeet_distributive ? *)
#[key="T"]
HB.mixin Record Lattice_MeetIsDistributive d (T : Type) of Lattice d T := {
  meetUl : @left_distributive T T meet join;
}.
#[short(type="distrLatticeType")]
HB.structure Definition DistrLattice d :=
  { T of Lattice_MeetIsDistributive d T & Lattice d T }.

Module DistrLatticeExports.
(* FIXME: clone? *)
End DistrLatticeExports.
HB.export DistrLatticeExports.

#[short(type="bDistrLatticeType")]
HB.structure Definition BDistrLattice d :=
  { T of hasBottom d T & DistrLattice d T}.

Module BDistrLatticeExports.
Notation "[ 'bDistrLatticeType' 'of' T ]" := (BDistrLattice.clone _ T%type _)
  (at level 0, format "[ 'bDistrLatticeType'  'of'  T ]") : form_scope.
End BDistrLatticeExports.
HB.export BDistrLatticeExports.

#[short(type="tbDistrLatticeType")]
HB.structure Definition TBDistrLattice d :=
  { T of TBLattice d T & BDistrLattice d T }.

Module TBDistrLatticeExports.
Notation "[ 'tbDistrLatticeType' 'of' T ]" := (TBDistrLattice.clone _ T%type _)
  (at level 0, format "[ 'tbDistrLatticeType'  'of'  T ]") : form_scope.
End TBDistrLatticeExports.
HB.export TBDistrLatticeExports.

#[key="T"]
HB.mixin Record hasSub d (T : Type) of BDistrLattice d T := {
  sub    : T -> T -> T;
  subKI  : forall x y, y `&` sub x y = bottom;
  joinIB : forall x y, (x `&` y) `|` sub x y = x
}.

#[short(type="cbDistrLatticeType")]
HB.structure Definition CBDistrLattice d :=
  { T of hasSub d T & BDistrLattice d T }.

Module CBDistrLatticeExports.
(*Notation "[ 'cbDistrLatticeType' 'of' T 'for' cT ]" := (@CBDistrLattice.clone _ T%type cT)
  (at level 0, format "[ 'cbDistrLatticeType'  'of'  T  'for'  cT ]") :
  form_scope.
Notation "[ 'cbDistrLatticeType' 'of' T 'for' cT 'with' disp ]" :=
  (@CBDistrLattice.clone disp T%type cT)
  (at level 0,
   format "[ 'cbDistrLatticeType'  'of'  T  'for'  cT  'with'  disp ]") :
  form_scope.
Notation "[ 'cbDistrLatticeType' 'of' T ]" := [cbDistrLatticeType of T for _]
  (at level 0, format "[ 'cbDistrLatticeType'  'of'  T ]") : form_scope.
Notation "[ 'cbDistrLatticeType' 'of' T 'with' disp ]" :=
  [cbDistrLatticeType of T for _ with disp]
  (at level 0, format "[ 'cbDistrLatticeType'  'of'  T  'with' disp ]") :
    form_scope.*)
End CBDistrLatticeExports.

HB.export CBDistrLatticeExports.

Module Import CBDistrLatticeSyntax.
Notation "x `\` y" := (sub x y) : order_scope.
End CBDistrLatticeSyntax.

#[key="T"]
HB.mixin Record hasCompl d (T : Type) of
         TBDistrLattice d T & CBDistrLattice d T := {
  compl : T -> T;
  complE : forall x : T, compl x = (top : T) `\` x (* FIXME? *)
}.

#[short(type="ctbDistrLatticeType")]
HB.structure Definition CTBDistrLattice d :=
  { T of hasCompl d T & TBDistrLattice d T & CBDistrLattice d T }.

Module CTBDistrLatticeExports.
(* Notation "[ 'ctbDistrLatticeType' 'of' T 'for' cT ]" := (@clone T _ cT _ id) *)
(*   (at level 0, format "[ 'ctbDistrLatticeType'  'of'  T  'for'  cT ]") : *)
(*   form_scope. *)
(* Notation "[ 'ctbDistrLatticeType' 'of' T 'for' cT 'with' disp ]" := *)
(*   (@clone_with T _ cT disp _ id) *)
(*   (at level 0, *)
(*    format "[ 'ctbDistrLatticeType'  'of'  T  'for'  cT  'with'  disp ]") *)
(*   : form_scope. *)
(* Notation "[ 'ctbDistrLatticeType' 'of' T ]" := [ctbDistrLatticeType of T for _] *)
(*   (at level 0, format "[ 'ctbDistrLatticeType'  'of'  T ]") : form_scope. *)
(* Notation "[ 'ctbDistrLatticeType' 'of' T 'with' disp ]" := *)
(*   [ctbDistrLatticeType of T for _ with disp] *)
(*   (at level 0, format "[ 'ctbDistrLatticeType'  'of'  T  'with' disp ]") : *)
(*   form_scope. *)
(* Notation "[ 'default_ctbDistrLatticeType' 'of' T ]" := *)
(*   (@pack T _ _ _ id _ _ id (Mixin (fun=> erefl))) *)
(*   (at level 0, format "[ 'default_ctbDistrLatticeType'  'of'  T ]") : *)
(*   form_scope. *)
End CTBDistrLatticeExports.
HB.export CTBDistrLatticeExports.

Module Import CTBDistrLatticeSyntax.
Notation "~` A" := (compl A) : order_scope.
End CTBDistrLatticeSyntax.

HB.mixin Record DistrLattice_isTotal d T of DistrLattice d T :=
  { le_total : total (<=%O : rel T) }.

#[short(type="orderType")]
HB.structure Definition Total d :=
  { T of DistrLattice_isTotal d T & DistrLattice d T }.

Module TotalExports.
(* Notation "[ 'orderType' 'of' T 'for' cT ]" := (@clone T _ cT _ id) *)
(*   (at level 0, format "[ 'orderType'  'of'  T  'for'  cT ]") : form_scope. *)
(* Notation "[ 'orderType' 'of' T 'for' cT 'with' disp ]" := *)
(*   (@clone_with T _ cT disp _ id) *)
(*   (at level 0, format "[ 'orderType'  'of'  T  'for'  cT  'with'  disp ]") : *)
(*   form_scope. *)
(* Notation "[ 'orderType' 'of' T ]" := [orderType of T for _] *)
(*   (at level 0, format "[ 'orderType'  'of'  T ]") : form_scope. *)
(* Notation "[ 'orderType' 'of' T 'with' disp ]" := *)
(*   [orderType of T for _ with disp] *)
(*   (at level 0, format "[ 'orderType'  'of'  T  'with' disp ]") : form_scope. *)
End TotalExports.

HB.export TotalExports.

(**********)
(* FINITE *)
(**********)

#[short(type="finPOrderType")]
HB.structure Definition FinPOrder d := { T of Finite T & POrder d T }.

Module FinPOrderExports.
Notation "[ 'finPOrderType' 'of' T ]" := (FinPOrder.clone _ T%type _ )
  (at level 0, format "[ 'finPOrderType'  'of'  T ]") : form_scope.
End FinPOrderExports.
HB.export FinPOrderExports.

#[short(type="finLatticeType")]
HB.structure Definition FinLattice d := { T of Finite T & TBLattice d T }.

Module FinLatticeExports.
Notation "[ 'finLatticeType' 'of' T ]" := (FinLattice.clone _ T%type _ )
  (at level 0, format "[ 'finLatticeType'  'of'  T ]") : form_scope.
End FinLatticeExports.
HB.export FinLatticeExports.

#[short(type="finDistrLatticeType")]
HB.structure Definition FinDistrLattice d :=
  { T of Finite T & TBDistrLattice d T }.

Module FinDistrLatticeExports.
Notation "[ 'finDistrLatticeType' 'of' T ]" := (FinDistrLattice.clone _ T%type _ )
  (at level 0, format "[ 'finDistrLatticeType'  'of'  T ]") : form_scope.
End FinDistrLatticeExports.
HB.export FinDistrLatticeExports.

#[short(type="finCDistrLatticeType")]
HB.structure Definition FinCDistrLattice d :=
  { T of Finite T & CTBDistrLattice d T }.

Module FinCDistrLatticeExports.
Notation "[ 'finCDistrLatticeType' 'of' T ]" := (FinCDistrLattice.clone _ T%type _ )
  (at level 0, format "[ 'finCDistrLatticeType'  'of'  T ]") : form_scope.
End FinCDistrLatticeExports.
HB.export FinCDistrLatticeExports.


#[short(type="finOrderType")]
HB.structure Definition FinTotal d :=
  { T of Total d T & FinDistrLattice d T }.

Module FinTotalExports.
Notation "[ 'finOrderType' 'of' T ]" := (FinTotal.clone _ T%type _ )
  (at level 0, format "[ 'finOrderType'  'of'  T ]") : form_scope.
End FinTotalExports.
HB.export FinTotalExports.

(********)
(* DUAL *)
(********)

Definition dual T : Type := T.
Definition dual_display : unit -> unit. Proof. exact. Qed.

Notation dual_le := (@le (dual_display _) _).
Notation dual_lt := (@lt (dual_display _) _).
Notation dual_comparable := (@comparable (dual_display _) _).
Notation dual_ge := (@ge (dual_display _) _).
Notation dual_gt := (@gt (dual_display _) _).
Notation dual_leif := (@leif (dual_display _) _).
Notation dual_lteif := (@lteif (dual_display _) _).
Notation dual_max := (@max (dual_display _) _).
Notation dual_min := (@min (dual_display _) _).
Notation dual_meet := (@meet (dual_display _) _).
Notation dual_join := (@join (dual_display _) _).
Notation dual_bottom := (@bottom (dual_display _) _).
Notation dual_top := (@top (dual_display _) _).

Module Import DualSyntax.

Notation "T ^d" := (dual T) (at level 2, format "T ^d") : type_scope.
Notation "<=^d%O" := dual_le : fun_scope.
Notation ">=^d%O" := dual_ge : fun_scope.
Notation "<^d%O" := dual_lt : fun_scope.
Notation ">^d%O" := dual_gt : fun_scope.
Notation "<?=^d%O" := dual_leif : fun_scope.
Notation "<?<=^d%O" := dual_lteif : fun_scope.
Notation ">=<^d%O" := dual_comparable : fun_scope.
Notation "><^d%O" := (fun x y => ~~ dual_comparable x y) : fun_scope.

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

Notation "x `&^d` y" := (dual_meet x y) : order_scope.
Notation "x `|^d` y" := (dual_join x y) : order_scope.

Notation "0^d" := dual_bottom : order_scope.
Notation "1^d" := dual_top : order_scope.

(* The following Local Notations are here to define the \join^d_ and \meet^d_ *)
(* notations later. Do not remove them.                                       *)
Local Notation "0" := dual_bottom.
Local Notation "1" := dual_top.
Local Notation join := dual_join.
Local Notation meet := dual_meet.

Notation "\join^d_ ( i <- r | P ) F" :=
  (\big[join/0]_(i <- r | P%B) F%O) : order_scope.
Notation "\join^d_ ( i <- r ) F" :=
  (\big[join/0]_(i <- r) F%O) : order_scope.
Notation "\join^d_ ( i | P ) F" :=
  (\big[join/0]_(i | P%B) F%O) : order_scope.
Notation "\join^d_ i F" :=
  (\big[join/0]_i F%O) : order_scope.
Notation "\join^d_ ( i : I | P ) F" :=
  (\big[join/0]_(i : I | P%B) F%O) (only parsing) : order_scope.
Notation "\join^d_ ( i : I ) F" :=
  (\big[join/0]_(i : I) F%O) (only parsing) : order_scope.
Notation "\join^d_ ( m <= i < n | P ) F" :=
 (\big[join/0]_(m <= i < n | P%B) F%O) : order_scope.
Notation "\join^d_ ( m <= i < n ) F" :=
 (\big[join/0]_(m <= i < n) F%O) : order_scope.
Notation "\join^d_ ( i < n | P ) F" :=
 (\big[join/0]_(i < n | P%B) F%O) : order_scope.
Notation "\join^d_ ( i < n ) F" :=
 (\big[join/0]_(i < n) F%O) : order_scope.
Notation "\join^d_ ( i 'in' A | P ) F" :=
 (\big[join/0]_(i in A | P%B) F%O) : order_scope.
Notation "\join^d_ ( i 'in' A ) F" :=
 (\big[join/0]_(i in A) F%O) : order_scope.

Notation "\meet^d_ ( i <- r | P ) F" :=
  (\big[meet/1]_(i <- r | P%B) F%O) : order_scope.
Notation "\meet^d_ ( i <- r ) F" :=
  (\big[meet/1]_(i <- r) F%O) : order_scope.
Notation "\meet^d_ ( i | P ) F" :=
  (\big[meet/1]_(i | P%B) F%O) : order_scope.
Notation "\meet^d_ i F" :=
  (\big[meet/1]_i F%O) : order_scope.
Notation "\meet^d_ ( i : I | P ) F" :=
  (\big[meet/1]_(i : I | P%B) F%O) (only parsing) : order_scope.
Notation "\meet^d_ ( i : I ) F" :=
  (\big[meet/1]_(i : I) F%O) (only parsing) : order_scope.
Notation "\meet^d_ ( m <= i < n | P ) F" :=
 (\big[meet/1]_(m <= i < n | P%B) F%O) : order_scope.
Notation "\meet^d_ ( m <= i < n ) F" :=
 (\big[meet/1]_(m <= i < n) F%O) : order_scope.
Notation "\meet^d_ ( i < n | P ) F" :=
 (\big[meet/1]_(i < n | P%B) F%O) : order_scope.
Notation "\meet^d_ ( i < n ) F" :=
 (\big[meet/1]_(i < n) F%O) : order_scope.
Notation "\meet^d_ ( i 'in' A | P ) F" :=
 (\big[meet/1]_(i in A | P%B) F%O) : order_scope.
Notation "\meet^d_ ( i 'in' A ) F" :=
 (\big[meet/1]_(i in A) F%O) : order_scope.

End DualSyntax.

(**********)
(* THEORY *)
(**********)

Module Import POrderTheory.
Section POrderTheory.

Context {disp : unit} {T : porderType disp}.

Implicit Types (x y : T) (s : seq T).

Lemma geE x y : ge x y = (y <= x). Proof. by []. Qed.
Lemma gtE x y : gt x y = (y < x). Proof. by []. Qed.

Lemma lexx (x : T) : x <= x.
Proof. exact: le_refl. Qed.
Hint Resolve lexx : core.

Definition le_refl : reflexive le := lexx.
Definition ge_refl : reflexive ge := lexx.
Hint Resolve le_refl : core.

Lemma le_anti: antisymmetric (<=%O : rel T).
Proof. exact: le_anti. Qed.

Lemma ge_anti: antisymmetric (>=%O : rel T).
Proof. by move=> x y /le_anti. Qed.

Lemma le_trans: transitive (<=%O : rel T).
Proof. exact: le_trans. Qed.

Lemma ge_trans: transitive (>=%O : rel T).
Proof. by move=> ? ? ? ? /le_trans; apply. Qed.

Lemma le_le_trans x y z t : z <= x -> y <= t -> x <= y -> z <= t.
Proof. by move=> + /(le_trans _)/[apply]; apply: le_trans. Qed.

Lemma lt_def x y: (x < y) = (y != x) && (x <= y).
Proof. exact: lt_def. Qed.

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

Lemma lt_sorted_uniq_le s : sorted <%O s = uniq s && sorted <=%O s.
Proof.
rewrite le_sorted_pairwise lt_sorted_pairwise uniq_pairwise -pairwise_relI.
by apply/eq_pairwise => ? ?; rewrite lt_neqAle.
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
rewrite lt_sorted_uniq_le => /andP[s_uniq le_s].
apply: (total_homo_mono_in _ _ ltn_neqAle lt_neqAle le_anti leq_total) => //.
move=> i j ilt jlt ltij; rewrite lt_neqAle le_sorted_leq_nth// 1?ltnW//.
by rewrite nth_uniq// ltn_eqF.
Qed.

Lemma lt_sorted_ltn_nth (x0 : T) (s : seq T) : sorted <%O s ->
  {in [pred n | (n < size s)%N] &,
    {mono nth x0 s : i j / (i < j)%N >-> i < j}}.
Proof.
move=> ss; have := lt_sorted_leq_nth x0 ss.
exact: (anti_mono_in _ ltn_neqAle lt_neqAle anti_leq).
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

Lemma le_sorted_eq s1 s2 :
  sorted <=%O s1 -> sorted <=%O s2 -> perm_eq s1 s2 -> s1 = s2.
Proof. exact/sorted_eq/le_anti/le_trans. Qed.

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

Lemma count_lt_le_mem x s : (count (< x) s < count (<= x) s)%N = (x \in s).
Proof.
have := count_predUI (pred1 x) (< x) s.
have -> : count (predI (pred1 x) (< x)) s = 0%N.
  rewrite (@eq_count _ _ pred0) ?count_pred0 // => y /=.
  by rewrite lt_def; case: eqP => //= ->; rewrite eqxx.
have /eq_count-> : [predU1 x & < x] =1 (<= x) by move=> y /=; rewrite le_eqVlt.
by rewrite addn0 => ->; rewrite -add1n leq_add2r -has_count has_pred1.
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
move=> c_xy; apply/idP/idP => [/le_gtF/negP/negP//|]; rewrite lt_neqAle.
by move: c_xy => /orP [] -> //; rewrite andbT negbK => /eqP ->.
Qed.

Lemma comparable_ltNge x y : x >=< y -> (x < y) = ~~ (y <= x).
Proof.
move=> c_xy; apply/idP/idP => [/lt_geF/negP/negP//|].
by rewrite lt_neqAle eq_le; move: c_xy => /orP [] -> //; rewrite andbT.
Qed.

Lemma comparable_ltgtP x y : x >=< y ->
  compare x y (min y x) (min x y) (max y x) (max x y)
  (y == x) (x == y) (x >= y) (x <= y) (x > y) (x < y).
Proof.
rewrite /min /max />=<%O !le_eqVlt [y == x]eq_sym.
have := (eqVneq x y, (boolP (x < y), boolP (y < x))).
move=> [[->//|neq_xy /=] [[] xy [] //=]] ; do ?by rewrite ?ltxx; constructor.
  by rewrite ltxx in xy.
by rewrite le_gtF // ltW.
Qed.

Lemma comparable_leP x y : x >=< y ->
  le_xor_gt x y (min y x) (min x y) (max y x) (max x y) (x <= y) (y < x).
Proof. by move=> /comparable_ltgtP [?|?|->]; constructor; rewrite // ltW. Qed.

Lemma comparable_ltP x y : x >=< y ->
  lt_xor_ge x y (min y x) (min x y) (max y x) (max x y) (y <= x) (x < y).
Proof. by move=> /comparable_ltgtP [?|?|->]; constructor; rewrite // ltW. Qed.

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

Lemma comparableP x y : incompare x y
  (min y x) (min x y) (max y x) (max x y)
  (y == x) (x == y) (x >= y) (x <= y) (x > y) (x < y)
  (y >=< x) (x >=< y).
Proof.
rewrite ![y >=< _]comparable_sym; have [c_xy|i_xy] := boolP (x >=< y).
  by case: (comparable_ltgtP c_xy) => ?; constructor.
by rewrite /min /max ?incomparable_eqF ?incomparable_leF;
   rewrite ?incomparable_ltF// 1?comparable_sym //; constructor.
Qed.

Lemma le_comparable (x y : T) : x <= y -> x >=< y.
Proof. by case: comparableP. Qed.

Lemma lt_comparable (x y : T) : x < y -> x >=< y.
Proof. by case: comparableP. Qed.

Lemma ge_comparable (x y : T) : y <= x -> x >=< y.
Proof. by case: comparableP. Qed.

Lemma gt_comparable (x y : T) : y < x -> x >=< y.
Proof. by case: comparableP. Qed.

(* leif *)

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

Lemma ltNleif x y C : x <= y ?= iff ~~ C -> (x < y) = C.
Proof. by move=> /lt_leif; rewrite negbK. Qed.

Lemma eq_leif x y C : x <= y ?= iff C -> (x == y) = C.
Proof. by move=> /leifP; case: C comparableP => [] []. Qed.

Lemma eqTleif x y C : x <= y ?= iff C -> C -> x = y.
Proof. by move=> /eq_leif<-/eqP. Qed.

(* lteif *)

Lemma lteif_trans x y z C1 C2 :
  x < y ?<= if C1 -> y < z ?<= if C2 -> x < z ?<= if C1 && C2.
Proof.
case: C1 C2 => [][];
  [exact: le_trans | exact: le_lt_trans | exact: lt_le_trans | exact: lt_trans].
Qed.

Lemma lteif_anti C1 C2 x y :
  (x < y ?<= if C1) && (y < x ?<= if C2) = C1 && C2 && (x == y).
Proof. by case: C1 C2 => [][]; rewrite lte_anti. Qed.

Lemma lteifxx x C : (x < x ?<= if C) = C.
Proof. by case: C; rewrite /= ltexx. Qed.

Lemma lteifNF x y C : y < x ?<= if ~~ C -> x < y ?<= if C = false.
Proof. by case: C => [/lt_geF|/le_gtF]. Qed.

Lemma lteifS x y C : x < y -> x < y ?<= if C.
Proof. by case: C => //= /ltW. Qed.

Lemma lteifT x y : x < y ?<= if true = (x <= y). Proof. by []. Qed.

Lemma lteifF x y : x < y ?<= if false = (x < y). Proof. by []. Qed.

Lemma lteif_orb x y : {morph lteif x y : p q / p || q}.
Proof. by case=> [][] /=; case: comparableP. Qed.

Lemma lteif_andb x y : {morph lteif x y : p q / p && q}.
Proof. by case=> [][] /=; case: comparableP. Qed.

Lemma lteif_imply C1 C2 x y : C1 ==> C2 -> x < y ?<= if C1 -> x < y ?<= if C2.
Proof. by case: C1 C2 => [][] //= _ /ltW. Qed.

Lemma lteifW C x y : x < y ?<= if C -> x <= y.
Proof. by case: C => // /ltW. Qed.

Lemma ltrW_lteif C x y : x < y -> x < y ?<= if C.
Proof. by case: C => // /ltW. Qed.

Lemma lteifN C x y : x < y ?<= if ~~ C -> ~~ (y < x ?<= if C).
Proof. by case: C => /=; case: comparableP. Qed.

(* min and max *)

Lemma minElt x y : min x y = if x < y then x else y. Proof. by []. Qed.
Lemma maxElt x y : max x y = if x < y then y else x. Proof. by []. Qed.

Lemma minEle x y : min x y = if x <= y then x else y.
Proof. by case: comparableP. Qed.

Lemma maxEle x y : max x y = if x <= y then y else x.
Proof. by case: comparableP. Qed.

Lemma comparable_minEgt x y : x >=< y -> min x y = if x > y then y else x.
Proof. by case: comparableP. Qed.
Lemma comparable_maxEgt x y : x >=< y -> max x y = if x > y then x else y.
Proof. by case: comparableP. Qed.
Lemma comparable_minEge x y : x >=< y -> min x y = if x >= y then y else x.
Proof. by case: comparableP. Qed.
Lemma comparable_maxEge x y : x >=< y -> max x y = if x >= y then x else y.
Proof. by case: comparableP. Qed.

Lemma min_l x y : x <= y -> min x y = x. Proof. by case: comparableP. Qed.
Lemma min_r x y : y <= x -> min x y = y. Proof. by case: comparableP. Qed.
Lemma max_l x y : y <= x -> max x y = x. Proof. by case: comparableP. Qed.
Lemma max_r x y : x <= y -> max x y = y. Proof. by case: comparableP. Qed.

Lemma minxx : idempotent (min : T -> T -> T).
Proof. by rewrite /min => x; rewrite ltxx. Qed.

Lemma maxxx : idempotent (max : T -> T -> T).
Proof. by rewrite /max => x; rewrite ltxx. Qed.

Lemma eq_minl x y : (min x y == x) = (x <= y).
Proof. by rewrite !(fun_if, if_arg) eqxx; case: comparableP. Qed.

Lemma eq_maxr x y : (max x y == y) = (x <= y).
Proof. by rewrite !(fun_if, if_arg) eqxx; case: comparableP. Qed.

Lemma min_idPl x y : reflect (min x y = x) (x <= y).
Proof. by apply: (iffP idP); rewrite (rwP eqP) eq_minl. Qed.

Lemma max_idPr x y : reflect (max x y = y) (x <= y).
Proof. by apply: (iffP idP); rewrite (rwP eqP) eq_maxr. Qed.

Lemma min_minKx x y : min (min x y) y = min x y.
Proof. by rewrite !(fun_if, if_arg) ltxx/=; case: comparableP. Qed.

Lemma min_minxK x y : min x (min x y) = min x y.
Proof. by rewrite !(fun_if, if_arg) ltxx/=; case: comparableP. Qed.

Lemma max_maxKx x y : max (max x y) y = max x y.
Proof. by rewrite !(fun_if, if_arg) ltxx/=; case: comparableP. Qed.

Lemma max_maxxK x y : max x (max x y) = max x y.
Proof. by rewrite !(fun_if, if_arg) ltxx/=; case: comparableP. Qed.

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

Lemma comparable_minC : min x y = min y x.
Proof. by case: comparableP cmp_xy. Qed.

Lemma comparable_maxC : max x y = max y x.
Proof. by case: comparableP cmp_xy. Qed.

Lemma comparable_eq_minr : (min x y == y) = (y <= x).
Proof. by rewrite !(fun_if, if_arg) eqxx; case: comparableP cmp_xy. Qed.

Lemma comparable_eq_maxl : (max x y == x) = (y <= x).
Proof. by rewrite !(fun_if, if_arg) eqxx; case: comparableP cmp_xy. Qed.

Lemma comparable_min_idPr : reflect (min x y = y) (y <= x).
Proof. by apply: (iffP idP); rewrite (rwP eqP) comparable_eq_minr. Qed.

Lemma comparable_max_idPl : reflect (max x y = x) (y <= x).
Proof. by apply: (iffP idP); rewrite (rwP eqP) comparable_eq_maxl. Qed.

Lemma comparable_le_minr : (z <= min x y) = (z <= x) && (z <= y).
Proof.
case: comparableP cmp_xy => // [||<-//]; rewrite ?andbb//; last rewrite andbC;
  by case: (comparableP z) => // [/lt_trans xlt/xlt|->] /ltW.
Qed.

Lemma comparable_le_minl : (min x y <= z) = (x <= z) || (y <= z).
Proof.
case: comparableP cmp_xy => // [||<-//]; rewrite ?orbb//; last rewrite orbC;
  by move=> xy _; apply/idP/idP => [->|/orP[]]//; apply/le_trans/ltW.
Qed.

Lemma comparable_lt_minr : (z < min x y) = (z < x) && (z < y).
Proof.
case: comparableP cmp_xy => // [||<-//]; rewrite ?andbb//; last rewrite andbC;
  by case: (comparableP z) => // /lt_trans xlt/xlt.
Qed.

Lemma comparable_lt_minl : (min x y < z) = (x < z) || (y < z).
Proof.
case: comparableP cmp_xy => // [||<-//]; rewrite ?orbb//; last rewrite orbC;
  by move=> xy _; apply/idP/idP => [->|/orP[]]//; apply/lt_trans.
Qed.

Lemma comparable_le_maxr : (z <= max x y) = (z <= x) || (z <= y).
Proof.
case: comparableP cmp_xy => // [||<-//]; rewrite ?orbb//; first rewrite orbC;
  by move=> xy _; apply/idP/idP => [->|/orP[]]// /le_trans->//; apply/ltW.
Qed.

Lemma comparable_le_maxl : (max x y <= z) = (x <= z) && (y <= z).
Proof.
case: comparableP cmp_xy => // [||<-//]; rewrite ?andbb//; first rewrite andbC;
  by case: (comparableP z) => // [ylt /lt_trans /(_ _)/ltW|->/ltW]->.
Qed.

Lemma comparable_lt_maxr : (z < max x y) = (z < x) || (z < y).
Proof.
case: comparableP cmp_xy => // [||<-//]; rewrite ?orbb//; first rewrite orbC;
  by move=> xy _; apply/idP/idP => [->|/orP[]]// /lt_trans->.
Qed.

Lemma comparable_lt_maxl : (max x y < z) = (x < z) && (y < z).
Proof.
case: comparableP cmp_xy => // [||<-//]; rewrite ?andbb//; first rewrite andbC;
by case: (comparableP z) => // ylt /lt_trans->.
Qed.

Lemma comparable_minxK : max (min x y) y = y.
Proof. by rewrite !(fun_if, if_arg) ltxx/=; case: comparableP cmp_xy. Qed.

Lemma comparable_minKx : max x (min x y) = x.
Proof. by rewrite !(fun_if, if_arg) ltxx/=; case: comparableP cmp_xy. Qed.

Lemma comparable_maxxK : min (max x y) y = y.
Proof. by rewrite !(fun_if, if_arg) ltxx/=; case: comparableP cmp_xy. Qed.

Lemma comparable_maxKx : min x (max x y) = x.
Proof. by rewrite !(fun_if, if_arg) ltxx/=; case: comparableP cmp_xy. Qed.

Lemma comparable_lteifNE C : x >=< y -> x < y ?<= if ~~ C = ~~ (y < x ?<= if C).
Proof. by case: C => /=; case: comparableP. Qed.

Lemma comparable_lteif_minr C :
  (z < Order.min x y ?<= if C) = (z < x ?<= if C) && (z < y ?<= if C).
Proof. by case: C; rewrite /= (comparable_le_minr, comparable_lt_minr). Qed.

Lemma comparable_lteif_minl C :
  (Order.min x y < z ?<= if C) = (x < z ?<= if C) || (y < z ?<= if C).
Proof. by case: C; rewrite /= (comparable_le_minl, comparable_lt_minl). Qed.

Lemma comparable_lteif_maxr C :
  (z < Order.max x y ?<= if C) = (z < x ?<= if C) || (z < y ?<= if C).
Proof. by case: C; rewrite /= (comparable_le_maxr, comparable_lt_maxr). Qed.

Lemma comparable_lteif_maxl C :
  (Order.max x y < z ?<= if C) = (x < z ?<= if C) && (y < z ?<= if C).
Proof. by case: C; rewrite /= (comparable_le_maxl, comparable_lt_maxl). Qed.

End Comparable2.

Section Comparable3.
Variables (x y z : T) (cmp_xy : x >=< y) (cmp_xz : x >=< z) (cmp_yz : y >=< z).
Let P := comparableP.

Lemma comparable_minA : min x (min y z) = min (min x y) z.
Proof.
move: cmp_xy cmp_xz cmp_yz; rewrite !(fun_if, if_arg)/=.
move: (P x y) (P x z) (P y z) => [xy|xy|xy|<-] [xz|xz|xz|<-]// []//= yz.
- by have := lt_trans xy (lt_trans yz xz); rewrite ltxx.
- by have := lt_trans xy (lt_trans xz yz); rewrite ltxx.
- by have := lt_trans xy xz; rewrite yz ltxx.
Qed.

Lemma comparable_maxA : max x (max y z) = max (max x y) z.
Proof.
move: cmp_xy cmp_xz cmp_yz; rewrite !(fun_if, if_arg)/=.
move: (P x y) (P x z) (P y z) => [xy|xy|xy|<-] [xz|xz|xz|<-]// []//= yz.
- by have := lt_trans xy (lt_trans yz xz); rewrite ltxx.
- by have := lt_trans xy (lt_trans xz yz); rewrite ltxx.
- by have := lt_trans xy xz; rewrite yz ltxx.
Qed.

Lemma comparable_max_minl : max (min x y) z = min (max x z) (max y z).
Proof.
move: cmp_xy cmp_xz cmp_yz; rewrite !(fun_if, if_arg)/=.
move: (P x y) (P x z) (P y z).
move=> [xy|xy|xy|<-] [xz|xz|xz|<-] [yz|yz|yz|//->]//= _; rewrite ?ltxx//.
- by have := lt_trans xy (lt_trans yz xz); rewrite ltxx.
- by have := lt_trans xy (lt_trans xz yz); rewrite ltxx.
Qed.

Lemma comparable_min_maxl : min (max x y) z = max (min x z) (min y z).
Proof.
move: cmp_xy cmp_xz cmp_yz; rewrite !(fun_if, if_arg)/=.
move: (P x y) (P x z) (P y z).
move=> [xy|xy|xy|<-] [xz|xz|xz|<-] []yz//= _; rewrite ?ltxx//.
- by have := lt_trans xy (lt_trans yz xz); rewrite ltxx.
- by have := lt_trans xy yz; rewrite ltxx.
- by have := lt_trans xy (lt_trans xz yz); rewrite ltxx.
- by have := lt_trans xy xz; rewrite yz ltxx.
Qed.

End Comparable3.

Lemma comparable_minAC x y z : x >=< y -> x >=< z -> y >=< z ->
  min (min x y) z = min (min x z) y.
Proof.
move=> xy xz yz; rewrite -comparable_minA// [min y z]comparable_minC//.
by rewrite comparable_minA// 1?comparable_sym.
Qed.

Lemma comparable_maxAC x y z : x >=< y -> x >=< z -> y >=< z ->
  max (max x y) z = max (max x z) y.
Proof.
move=> xy xz yz; rewrite -comparable_maxA// [max y z]comparable_maxC//.
by rewrite comparable_maxA// 1?comparable_sym.
Qed.

Lemma comparable_minCA x y z : x >=< y -> x >=< z -> y >=< z ->
  min x (min y z) = min y (min x z).
Proof.
move=> xy xz yz; rewrite comparable_minA// [min x y]comparable_minC//.
by rewrite -comparable_minA// 1?comparable_sym.
Qed.

Lemma comparable_maxCA x y z : x >=< y -> x >=< z -> y >=< z ->
  max x (max y z) = max y (max x z).
Proof.
move=> xy xz yz; rewrite comparable_maxA// [max x y]comparable_maxC//.
by rewrite -comparable_maxA// 1?comparable_sym.
Qed.

Lemma comparable_minACA x y z t :
    x >=< y -> x >=< z -> x >=< t -> y >=< z -> y >=< t -> z >=< t ->
  min (min x y) (min z t) = min (min x z) (min y t).
Proof.
move=> xy xz xt yz yt zt; rewrite comparable_minA// ?comparable_minl//.
rewrite [min _ z]comparable_minAC// -comparable_minA// ?comparable_minl//.
by rewrite inE comparable_sym.
Qed.

Lemma comparable_maxACA x y z t :
    x >=< y -> x >=< z -> x >=< t -> y >=< z -> y >=< t -> z >=< t ->
  max (max x y) (max z t) = max (max x z) (max y t).
Proof.
move=> xy xz xt yz yt zt; rewrite comparable_maxA// ?comparable_maxl//.
rewrite [max _ z]comparable_maxAC// -comparable_maxA// ?comparable_maxl//.
by rewrite inE comparable_sym.
Qed.

Lemma comparable_max_minr x y z : x >=< y -> x >=< z -> y >=< z ->
  max x (min y z) = min (max x y) (max x z).
Proof.
move=> xy xz yz; rewrite ![max x _]comparable_maxC// ?comparable_minr//.
by rewrite comparable_max_minl// 1?comparable_sym.
Qed.

Lemma comparable_min_maxr x y z : x >=< y -> x >=< z -> y >=< z ->
  min x (max y z) = max (min x y) (min x z).
Proof.
move=> xy xz yz; rewrite ![min x _]comparable_minC// ?comparable_maxr//.
by rewrite comparable_min_maxl// 1?comparable_sym.
Qed.

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

Lemma nmono_leif (f : T -> T) C : {mono f : x y /~ x <= y} ->
  forall x y, (f x <= f y ?= iff C) = (y <= x ?= iff C).
Proof. by move=> mf x y; rewrite /leif !eq_le !mf. Qed.

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

Lemma bigmax_le : x0 <= x -> (forall i, P i -> f i <= x) ->
  \big[max/x0]_(i <- r | P i) f i <= x.
Proof. by move=> ? ?; elim/big_ind: _ => // *; rewrite maxEle; case: ifPn. Qed.

Lemma bigmax_lt : x0 < x -> (forall i, P i -> f i < x) ->
  \big[max/x0]_(i <- r | P i) f i < x.
Proof. by move=> ? ?; elim/big_ind: _ => // *; rewrite maxElt; case: ifPn. Qed.

Lemma lt_bigmin : x < x0 -> (forall i, P i -> x < f i) ->
  x < \big[min/x0]_(i <- r | P i) f i.
Proof. by move=> ? ?; elim/big_ind: _ => // *; rewrite minElt; case: ifPn. Qed.

Lemma le_bigmin : x <= x0 -> (forall i, P i -> x <= f i) ->
  x <= \big[min/x0]_(i <- r | P i) f i.
Proof. by move=> ? ?; elim/big_ind: _ => // *; rewrite minEle; case: ifPn. Qed.

End bigminmax.

End POrderTheory.
#[global] Hint Resolve comparable_minr comparable_minl : core.
#[global] Hint Resolve comparable_maxr comparable_maxl : core.

Section ContraTheory.
Context {disp1 disp2 : unit} {T1 : porderType disp1} {T2 : porderType disp2}.
Implicit Types (x y : T1) (z t : T2) (b : bool) (m n : nat) (P : Prop).

Lemma comparable_contraTle b x y : x >=< y -> (y < x -> ~~ b) -> (b -> x <= y).
Proof. by case: comparableP; case: b. Qed.

Lemma comparable_contraTlt b x y : x >=< y -> (y <= x -> ~~ b) -> (b -> x < y).
Proof. by case: comparableP; case: b. Qed.

Lemma comparable_contraPle P x y : x >=< y -> (y < x -> ~ P) -> (P -> x <= y).
Proof. by case: comparableP => // _ _ /(_ isT). Qed.

Lemma comparable_contraPlt P x y : x >=< y -> (y <= x -> ~ P) -> (P -> x < y).
Proof. by case: comparableP => // _ _ /(_ isT). Qed.

Lemma comparable_contraNle b x y : x >=< y -> (y < x -> b) -> (~~ b -> x <= y).
Proof. by case: comparableP; case: b. Qed.

Lemma comparable_contraNlt b x y : x >=< y -> (y <= x -> b) -> (~~ b -> x < y).
Proof. by case: comparableP; case: b. Qed.

Lemma comparable_contra_not_le P x y : x >=< y -> (y < x -> P) -> (~ P -> x <= y).
Proof. by case: comparableP => // _ _ /(_ isT). Qed.

Lemma comparable_contra_not_lt P x y : x >=< y -> (y <= x -> P) -> (~ P -> x < y).
Proof. by case: comparableP => // _ _ /(_ isT). Qed.

Lemma comparable_contraFle b x y : x >=< y -> (y < x -> b) -> (b = false -> x <= y).
Proof. by case: comparableP; case: b => // _ _ /implyP. Qed.

Lemma comparable_contraFlt b x y : x >=< y -> (y <= x -> b) -> (b = false -> x < y).
Proof. by case: comparableP; case: b => // _ _ /implyP. Qed.

Lemma contra_leT b x y : (~~ b -> x < y) -> (y <= x -> b).
Proof. by case: comparableP; case: b. Qed.

Lemma contra_ltT b x y : (~~ b -> x <= y) -> (y < x -> b).
Proof. by case: comparableP; case: b. Qed.

Lemma contra_leN b x y : (b -> x < y) -> (y <= x -> ~~ b).
Proof. by case: comparableP; case: b. Qed.

Lemma contra_ltN b x y : (b -> x <= y) -> (y < x -> ~~ b).
Proof. by case: comparableP; case: b. Qed.

Lemma contra_le_not P x y : (P -> x < y) -> (y <= x -> ~ P).
Proof. by case: comparableP => // _ PF _ /PF. Qed.

Lemma contra_lt_not P x y : (P -> x <= y) -> (y < x -> ~ P).
Proof. by case: comparableP => // _ PF _ /PF. Qed.

Lemma contra_leF b x y : (b -> x < y) -> (y <= x -> b = false).
Proof. by case: comparableP; case: b => // _ /implyP. Qed.

Lemma contra_ltF b x y : (b -> x <= y) -> (y < x -> b = false).
Proof. by case: comparableP; case: b => // _ /implyP. Qed.

Lemma comparable_contra_leq_le m n x y : x >=< y ->
  (y < x -> (n < m)%N) -> ((m <= n)%N -> x <= y).
Proof. by case: comparableP; case: ltngtP. Qed.

Lemma comparable_contra_leq_lt m n x y : x >=< y ->
  (y <= x -> (n < m)%N) -> ((m <= n)%N -> x < y).
Proof. by case: comparableP; case: ltngtP. Qed.

Lemma comparable_contra_ltn_le m n x y : x >=< y ->
  (y < x -> (n <= m)%N) -> ((m < n)%N -> x <= y).
Proof. by case: comparableP; case: ltngtP. Qed.

Lemma comparable_contra_ltn_lt m n x y : x >=< y ->
  (y <= x -> (n <= m)%N) -> ((m < n)%N -> x < y).
Proof. by case: comparableP; case: ltngtP. Qed.

Lemma contra_le_leq x y m n : ((n < m)%N -> y < x) -> (x <= y -> (m <= n)%N).
Proof. by case: comparableP; case: ltngtP. Qed.

Lemma contra_le_ltn x y m n : ((n <= m)%N -> y < x) -> (x <= y -> (m < n)%N).
Proof. by case: comparableP; case: ltngtP. Qed.

Lemma contra_lt_leq x y m n : ((n < m)%N -> y <= x) -> (x < y -> (m <= n)%N).
Proof. by case: comparableP; case: ltngtP. Qed.

Lemma contra_lt_ltn x y m n : ((n <= m)%N -> y <= x) -> (x < y -> (m < n)%N).
Proof. by case: comparableP; case: ltngtP. Qed.

Lemma comparable_contra_le x y z t : z >=< t ->
  (t < z -> y < x) -> (x <= y -> z <= t).
Proof. by do 2![case: comparableP => //= ?]. Qed.

Lemma comparable_contra_le_lt x y z t : z >=< t ->
  (t <= z -> y < x) -> (x <= y -> z < t).
Proof. by do 2![case: comparableP => //= ?]. Qed.

Lemma comparable_contra_lt_le x y z t : z >=< t ->
  (t < z -> y <= x) -> (x < y -> z <= t).
Proof. by do 2![case: comparableP => //= ?]. Qed.

Lemma comparable_contra_lt x y z t : z >=< t ->
 (t <= z -> y <= x) -> (x < y -> z < t).
Proof. by do 2![case: comparableP => //= ?]. Qed.

End ContraTheory.

Section POrderMonotonyTheory.

Context {disp disp' : unit}.
Context {T : porderType disp} {T' : porderType disp'}.
Implicit Types (m n p : nat) (x y z : T) (u v w : T').
Variables (D D' : {pred T}) (f : T -> T').

Let leT_anti := @le_anti _ T.
Let leT'_anti := @le_anti _ T'.
Hint Resolve lexx lt_neqAle lt_def : core.

Let ge_antiT : antisymmetric (>=%O : rel T).
Proof. by move=> ? ? /le_anti. Qed.

Lemma ltW_homo : {homo f : x y / x < y} -> {homo f : x y / x <= y}.
Proof. exact: homoW. Qed.

Lemma ltW_nhomo : {homo f : x y /~ x < y} -> {homo f : x y /~ x <= y}.
Proof. by apply: homoW=> // x y; rewrite eq_sym. Qed.

Lemma inj_homo_lt :
  injective f -> {homo f : x y / x <= y} -> {homo f : x y / x < y}.
Proof. exact: inj_homo. Qed.

Lemma inj_nhomo_lt :
  injective f -> {homo f : x y /~ x <= y} -> {homo f : x y /~ x < y}.
Proof. by apply: inj_homo=> // x y; rewrite eq_sym. Qed.

Lemma inc_inj : {mono f : x y / x <= y} -> injective f.
Proof. exact: mono_inj. Qed.

Lemma dec_inj : {mono f : x y /~ x <= y} -> injective f.
Proof. exact: mono_inj. Qed.

Lemma leW_mono : {mono f : x y / x <= y} -> {mono f : x y / x < y}.
Proof. exact: anti_mono. Qed.

Lemma leW_nmono : {mono f : x y /~ x <= y} -> {mono f : x y /~ x < y}.
Proof. by apply: anti_mono=> // x y; rewrite eq_sym. Qed.

(* Monotony in D D' *)
Lemma ltW_homo_in :
  {in D & D', {homo f : x y / x < y}} -> {in D & D', {homo f : x y / x <= y}}.
Proof. exact: homoW_in. Qed.

Lemma ltW_nhomo_in :
  {in D & D', {homo f : x y /~ x < y}} -> {in D & D', {homo f : x y /~ x <= y}}.
Proof. by apply: homoW_in=> // x y; rewrite eq_sym. Qed.

Lemma inj_homo_lt_in :
    {in D & D', injective f} ->  {in D & D', {homo f : x y / x <= y}} ->
  {in D & D', {homo f : x y / x < y}}.
Proof. exact: inj_homo_in. Qed.

Lemma inj_nhomo_lt_in :
    {in D & D', injective f} -> {in D & D', {homo f : x y /~ x <= y}} ->
  {in D & D', {homo f : x y /~ x < y}}.
Proof. by apply: inj_homo_in=> // x y; rewrite eq_sym. Qed.

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
Proof. by apply: anti_mono_in=> // x y; rewrite eq_sym. Qed.

End POrderMonotonyTheory.

End POrderTheory.

#[global] Hint Resolve lexx le_refl ltxx lt_irreflexive ltW lt_eqF : core.

Arguments leifP {disp T x y C}.
Arguments leif_refl {disp T x C}.
Arguments mono_in_leif [disp T A f C].
Arguments nmono_in_leif [disp T A f C].
Arguments mono_leif [disp T f C].
Arguments nmono_leif [disp T f C].
Arguments min_idPl {disp T x y}.
Arguments max_idPr {disp T x y}.
Arguments comparable_min_idPr {disp T x y _}.
Arguments comparable_max_idPl {disp T x y _}.

Module Import DualPOrder.
Section DualPOrder.

HB.instance Definition _ (T : eqType) := Equality.on T^d.
HB.instance Definition _ (T : choiceType) := Choice.on T^d.
HB.instance Definition _ (T : countType) := Countable.on T^d.
HB.instance Definition _ (T : finType) := Finite.on T^d.

Context {disp : unit}.
Variable T : porderType disp.

Lemma dual_lt_def (x y : T) : gt x y = (y != x) && ge x y.
Proof. by apply: lt_neqAle. Qed.

Fact dual_le_anti : antisymmetric (@ge _ T).
Proof. by move=> x y /andP [xy yx]; apply/le_anti/andP; split. Qed.

HB.instance Definition _ :=
  isPOrdered.Build
    (dual_display disp) (T^d)
    dual_lt_def lexx dual_le_anti
    (fun y z x zy yx => @le_trans _ _ y x z yx zy).

Lemma leEdual (x y : T) : (x <=^d y :> T^d) = (y <= x). Proof. by []. Qed.
Lemma ltEdual (x y : T) : (x <^d y :> T^d) = (y < x). Proof. by []. Qed.

End DualPOrder.

HB.instance Definition _ d (T : finPOrderType d) := FinPOrder.on T^d.

End DualPOrder.

Module Import DualLattice.
Section DualLattice.
Context {disp : unit}.
Variable L : latticeType disp.
Implicit Types (x y : L).

Lemma meetC : commutative (@meet _ L). Proof. exact: meetC. Qed.
Lemma joinC : commutative (@join _ L). Proof. exact: joinC. Qed.

Lemma meetA : associative (@meet _ L). Proof. exact: meetA. Qed.
Lemma joinA : associative (@join _ L). Proof. exact: joinA. Qed.

Lemma joinKI y x : x `&` (x `|` y) = x. Proof. exact: joinKI. Qed.
Lemma meetKU y x : x `|` (x `&` y) = x. Proof. exact: meetKU. Qed.

Lemma joinKIC y x : x `&` (y `|` x) = x. Proof. by rewrite joinC joinKI. Qed.
Lemma meetKUC y x : x `|` (y `&` x) = x. Proof. by rewrite meetC meetKU. Qed.

Lemma meetUK x y : (x `&` y) `|` y = y.
Proof. by rewrite joinC meetC meetKU. Qed.
Lemma joinIK x y : (x `|` y) `&` y = y.
Proof. by rewrite joinC meetC joinKI. Qed.

Lemma meetUKC x y : (y `&` x) `|` y = y. Proof. by rewrite meetC meetUK. Qed.
Lemma joinIKC x y : (y `|` x) `&` y = y. Proof. by rewrite joinC joinIK. Qed.

Lemma leEmeet x y : (x <= y) = (x `&` y == x).
Proof. exact: leEmeet. Qed.

Lemma leEjoin x y : (x <= y) = (x `|` y == y).
Proof. by rewrite leEmeet; apply/eqP/eqP => <-; rewrite (joinKI, meetUK). Qed.

Fact dual_leEmeet (x y : L^d) : (x <= y) = (x `|` y == x).
Proof. by rewrite [LHS]leEjoin joinC. Qed.

HB.instance Definition _ :=
  @POrder_isLattice.Build
    (dual_display disp) L^d
    join meet joinC meetC joinA meetA meetKU joinKI dual_leEmeet.

Lemma meetEdual x y : ((x : L^d) `&^d` y) = (x `|` y). Proof. by []. Qed.
Lemma joinEdual x y : ((x : L^d) `|^d` y) = (x `&` y). Proof. by []. Qed.

End DualLattice.
End DualLattice.

Module Import LatticeTheoryMeet.
Section LatticeTheoryMeet.
Context {disp : unit} {L : latticeType disp}.
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
rewrite !leEmeet; apply/eqP/andP => [<-|[/eqP<- /eqP<-]].
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

Lemma meet_l x y : x <= y -> x `&` y = x. Proof. exact/meet_idPl. Qed.
Lemma meet_r x y : y <= x -> x `&` y = y. Proof. exact/meet_idPr. Qed.

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
Context {disp : unit} {L : latticeType disp}.
Implicit Types (x y : L).

(* lattice theory *)
Lemma joinAC : right_commutative (@join _ L).
Proof. exact: (@meetAC _ [latticeType of L^d]). Qed.
Lemma joinCA : left_commutative (@join _ L).
Proof. exact: (@meetCA _ [latticeType of L^d]). Qed.
Lemma joinACA : interchange (@join _ L) (@join _ L).
Proof. exact: (@meetACA _ [latticeType of L^d]). Qed.

Lemma joinxx x : x `|` x = x.
Proof. exact: (@meetxx _ [latticeType of L^d]). Qed.

Lemma joinKU y x : x `|` (x `|` y) = x `|` y.
Proof. exact: (@meetKI _ [latticeType of L^d]). Qed.
Lemma joinUK y x : (x `|` y) `|` y = x `|` y.
Proof. exact: (@meetIK _ [latticeType of L^d]). Qed.
Lemma joinKUC y x : x `|` (y `|` x) = x `|` y.
Proof. exact: (@meetKIC _ [latticeType of L^d]). Qed.
Lemma joinUKC y x : y `|` x `|` y = x `|` y.
Proof. exact: (@meetIKC _ [latticeType of L^d]). Qed.

(* interaction with order *)
Lemma leUx x y z : (x `|` y <= z) = (x <= z) && (y <= z).
Proof. exact: (@lexI _ [latticeType of L^d]). Qed.
Lemma lexUl x y z : x <= y -> x <= y `|` z.
Proof. exact: (@leIxl _ [latticeType of L^d]). Qed.
Lemma lexUr x y z : x <= z -> x <= y `|` z.
Proof. exact: (@leIxr _ [latticeType of L^d]). Qed.
Lemma lexU2 x y z : (x <= y) || (x <= z) -> x <= y `|` z.
Proof. exact: (@leIx2 _ [latticeType of L^d]). Qed.

Lemma leUr x y : x <= y `|` x.
Proof. exact: (@leIr _ [latticeType of L^d]). Qed.
Lemma leUl x y : x <= x `|` y.
Proof. exact: (@leIl _ [latticeType of L^d]). Qed.

Lemma join_idPr {x y} : reflect (x `|` y = y) (x <= y).
Proof. exact: (@meet_idPr _ [latticeType of L^d]). Qed.
Lemma join_idPl {x y} : reflect (y `|` x = y) (x <= y).
Proof. exact: (@meet_idPl _ [latticeType of L^d]). Qed.

Lemma join_l x y : y <= x -> x `|` y = x. Proof. exact/join_idPl. Qed.
Lemma join_r x y : x <= y -> x `|` y = y. Proof. exact/join_idPr. Qed.

Lemma leUidl x y : (x `|` y <= y) = (x <= y).
Proof. exact: (@leIidr _ [latticeType of L^d]). Qed.
Lemma leUidr x y : (y `|` x <= y) = (x <= y).
Proof. exact: (@leIidl _ [latticeType of L^d]). Qed.

Lemma eq_joinl x y : (x `|` y == x) = (y <= x).
Proof. exact: (@eq_meetl _ [latticeType of L^d]). Qed.
Lemma eq_joinr x y : (x `|` y == y) = (x <= y).
Proof. exact: (@eq_meetr _ [latticeType of L^d]). Qed.

Lemma leU2 x y z t : x <= z -> y <= t -> x `|` y <= z `|` t.
Proof. exact: (@leI2 _ [latticeType of L^d]). Qed.

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

End LatticeTheoryJoin.
End LatticeTheoryJoin.

Arguments meet_idPl {disp L x y}.
Arguments join_idPl {disp L x y}.

Module Import DistrLatticeTheory.
Section DistrLatticeTheory.
Context {disp : unit}.
Variable L : distrLatticeType disp.
Implicit Types (x y : L).

Lemma meetUl : left_distributive (@meet _ L) (@join _ L).
Proof. exact: meetUl. Qed.

Lemma meetUr : right_distributive (@meet _ L) (@join _ L).
Proof. by move=> x y z; rewrite meetC meetUl ![_ `&` x]meetC. Qed.

Lemma joinIl : left_distributive (@join _ L) (@meet _ L).
Proof. by move=> x y z; rewrite meetUr joinIK meetUl -joinA meetUKC. Qed.

Lemma joinIr : right_distributive (@join _ L) (@meet _ L).
Proof. by move=> x y z; rewrite !(joinC x) -joinIl. Qed.

HB.instance Definition _ := Lattice_MeetIsDistributive.Build _ L^d joinIl.

End DistrLatticeTheory.
End DistrLatticeTheory.

Module Import TotalTheory.
Section TotalTheory.
Context {disp : unit} {T : orderType disp}.
Implicit Types (x y z t : T) (s : seq T).

Definition le_total : total (<=%O : rel T) := le_total.
Hint Resolve le_total : core.

Lemma ge_total : total (>=%O : rel T).
Proof. by move=> ? ?; apply: le_total. Qed.
Hint Resolve ge_total : core.

Lemma comparableT x y : x >=< y. Proof. exact: le_total. Qed.
Hint Resolve comparableT : core.

Lemma sort_le_sorted s : sorted <=%O (sort <=%O s).
Proof. exact: sort_sorted. Qed.
Hint Resolve sort_le_sorted : core.

Lemma sort_lt_sorted s : sorted <%O (sort <=%O s) = uniq s.
Proof. by rewrite lt_sorted_uniq_le sort_uniq sort_le_sorted andbT. Qed.

Lemma perm_sort_leP s1 s2 : reflect (sort <=%O s1 = sort <=%O s2) (perm_eq s1 s2).
Proof. exact/perm_sortP/le_anti/le_trans/le_total. Qed.

Lemma filter_sort_le p s : filter p (sort <=%O s) = sort <=%O (filter p s).
Proof. exact/filter_sort/le_trans/le_total. Qed.

Lemma mask_sort_le s (m : bitseq) :
  {m_s : bitseq | mask m_s (sort <=%O s) = sort <=%O (mask m s)}.
Proof. exact/mask_sort/le_trans/le_total. Qed.

Lemma sorted_mask_sort_le s (m : bitseq) :
  sorted <=%O (mask m s) -> {m_s : bitseq | mask m_s (sort <=%O s) = mask m s}.
Proof. exact/sorted_mask_sort/le_trans/le_total. Qed.

Lemma subseq_sort_le : {homo sort <=%O : s1 s2 / @subseq T s1 s2}.
Proof. exact/subseq_sort/le_trans/le_total. Qed.

Lemma sorted_subseq_sort_le s1 s2 :
  subseq s1 s2 -> sorted <=%O s1 -> subseq s1 (sort <=%O s2).
Proof. exact/sorted_subseq_sort/le_trans/le_total. Qed.

Lemma mem2_sort_le s x y : x <= y -> mem2 s x y -> mem2 (sort <=%O s) x y.
Proof. exact/mem2_sort/le_trans/le_total. Qed.

Lemma leNgt x y : (x <= y) = ~~ (y < x). Proof. exact: comparable_leNgt. Qed.

Lemma ltNge x y : (x < y) = ~~ (y <= x). Proof. exact: comparable_ltNge. Qed.

Definition ltgtP x y := LatticeTheoryJoin.lcomparable_ltgtP (comparableT x y).
Definition leP x y := LatticeTheoryJoin.lcomparable_leP (comparableT x y).
Definition ltP x y := LatticeTheoryJoin.lcomparable_ltP (comparableT x y).

Lemma wlog_le P :
     (forall x y, P y x -> P x y) -> (forall x y, x <= y -> P x y) ->
   forall x y, P x y.
Proof. by move=> sP hP x y; case: (leP x y) => [| /ltW] /hP // /sP. Qed.

Lemma wlog_lt P :
    (forall x, P x x) ->
    (forall x y, (P y x -> P x y)) -> (forall x y, x < y -> P x y) ->
  forall x y, P x y.
Proof. by move=> rP sP hP x y; case: (ltgtP x y) => [||->] // /hP // /sP. Qed.

Lemma neq_lt x y : (x != y) = (x < y) || (y < x). Proof. by case: ltgtP. Qed.

Lemma lt_total x y : x != y -> (x < y) || (y < x). Proof. by case: ltgtP. Qed.

Lemma eq_leLR x y z t :
  (x <= y -> z <= t) -> (y < x -> t < z) -> (x <= y) = (z <= t).
Proof. by rewrite !ltNge => ? /contraTT ?; apply/idP/idP. Qed.

Lemma eq_leRL x y z t :
  (x <= y -> z <= t) -> (y < x -> t < z) -> (z <= t) = (x <= y).
Proof. by move=> *; symmetry; apply: eq_leLR. Qed.

Lemma eq_ltLR x y z t :
  (x < y -> z < t) -> (y <= x -> t <= z) -> (x < y) = (z < t).
Proof. by rewrite !leNgt => ? /contraTT ?; apply/idP/idP. Qed.

Lemma eq_ltRL x y z t :
  (x < y -> z < t) -> (y <= x -> t <= z) -> (z < t) = (x < y).
Proof. by move=> *; symmetry; apply: eq_ltLR. Qed.

(* max and min is join and meet *)

Lemma meetEtotal x y : x `&` y = min x y. Proof. by case: leP. Qed.
Lemma joinEtotal x y : x `|` y = max x y. Proof. by case: leP. Qed.

(* max and min theory *)

Lemma minEgt x y : min x y = if x > y then y else x. Proof. by case: ltP. Qed.
Lemma maxEgt x y : max x y = if x > y then x else y. Proof. by case: ltP. Qed.
Lemma minEge x y : min x y = if x >= y then y else x. Proof. by case: leP. Qed.
Lemma maxEge x y : max x y = if x >= y then x else y. Proof. by case: leP. Qed.

Lemma minC : commutative (min : T -> T -> T).
Proof. by move=> x y; apply: comparable_minC. Qed.

Lemma maxC : commutative (max : T -> T -> T).
Proof. by move=> x y; apply: comparable_maxC. Qed.

Lemma minA : associative (min : T -> T -> T).
Proof. by move=> x y z; apply: comparable_minA. Qed.

Lemma maxA : associative (max : T -> T -> T).
Proof. by move=> x y z; apply: comparable_maxA. Qed.

Lemma minAC : right_commutative (min : T -> T -> T).
Proof. by move=> x y z; apply: comparable_minAC. Qed.

Lemma maxAC : right_commutative (max : T -> T -> T).
Proof. by move=> x y z; apply: comparable_maxAC. Qed.

Lemma minCA : left_commutative (min : T -> T -> T).
Proof. by move=> x y z; apply: comparable_minCA. Qed.

Lemma maxCA : left_commutative (max : T -> T -> T).
Proof. by move=> x y z; apply: comparable_maxCA. Qed.

Lemma minACA : interchange (min : T -> T -> T) min.
Proof. by move=> x y z t; apply: comparable_minACA. Qed.

Lemma maxACA : interchange (max : T -> T -> T) max.
Proof. by move=> x y z t; apply: comparable_maxACA. Qed.

Lemma eq_minr x y : (min x y == y) = (y <= x).
Proof. exact: comparable_eq_minr. Qed.

Lemma eq_maxl x y : (max x y == x) = (y <= x).
Proof. exact: comparable_eq_maxl. Qed.

Lemma min_idPr x y : reflect (min x y = y) (y <= x).
Proof. exact: comparable_min_idPr. Qed.

Lemma max_idPl x y : reflect (max x y = x) (y <= x).
Proof. exact: comparable_max_idPl. Qed.

Lemma le_minr z x y : (z <= min x y) = (z <= x) && (z <= y).
Proof. exact: comparable_le_minr. Qed.

Lemma le_minl z x y : (min x y <= z) = (x <= z) || (y <= z).
Proof. exact: comparable_le_minl. Qed.

Lemma lt_minr z x y : (z < min x y) = (z < x) && (z < y).
Proof. exact: comparable_lt_minr. Qed.

Lemma lt_minl z x y : (min x y < z) = (x < z) || (y < z).
Proof. exact: comparable_lt_minl. Qed.

Lemma le_maxr z x y : (z <= max x y) = (z <= x) || (z <= y).
Proof. exact: comparable_le_maxr. Qed.

Lemma le_maxl z x y : (max x y <= z) = (x <= z) && (y <= z).
Proof. exact: comparable_le_maxl. Qed.

Lemma lt_maxr z x y : (z < max x y) = (z < x) || (z < y).
Proof. exact: comparable_lt_maxr. Qed.

Lemma lt_maxl z x y : (max x y < z) = (x < z) && (y < z).
Proof. exact: comparable_lt_maxl. Qed.

Lemma minxK x y : max (min x y) y = y. Proof. exact: comparable_minxK. Qed.
Lemma minKx x y : max x (min x y) = x. Proof. exact: comparable_minKx. Qed.
Lemma maxxK x y : min (max x y) y = y. Proof. exact: comparable_maxxK. Qed.
Lemma maxKx x y : min x (max x y) = x. Proof. exact: comparable_maxKx. Qed.

Lemma max_minl : left_distributive (max : T -> T -> T) min.
Proof. by move=> x y z; apply: comparable_max_minl. Qed.

Lemma min_maxl : left_distributive (min : T -> T -> T) max.
Proof. by move=> x y z; apply: comparable_min_maxl. Qed.

Lemma max_minr : right_distributive (max : T -> T -> T) min.
Proof. by move=> x y z; apply: comparable_max_minr. Qed.

Lemma min_maxr : right_distributive (min : T -> T -> T) max.
Proof. by move=> x y z; apply: comparable_min_maxr. Qed.

HB.instance Definition _ := SemiGroup.isComLaw.Build T max maxA maxC.
HB.instance Definition _ := SemiGroup.isComLaw.Build T min minA minC.

Lemma leIx x y z : (meet y z <= x) = (y <= x) || (z <= x).
Proof. by rewrite meetEtotal le_minl. Qed.

Lemma lexU x y z : (x <= join y z) = (x <= y) || (x <= z).
Proof. by rewrite joinEtotal le_maxr. Qed.

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

(* lteif *)

Lemma lteifNE x y C : x < y ?<= if ~~ C = ~~ (y < x ?<= if C).
Proof. by case: C => /=; case: leP. Qed.

Lemma lteif_minr z x y C :
  (z < Order.min x y ?<= if C) = (z < x ?<= if C) && (z < y ?<= if C).
Proof. by case: C; rewrite /= (le_minr, lt_minr). Qed.

Lemma lteif_minl z x y C :
  (Order.min x y < z ?<= if C) = (x < z ?<= if C) || (y < z ?<= if C).
Proof. by case: C; rewrite /= (le_minl, lt_minl). Qed.

Lemma lteif_maxr z x y C :
  (z < Order.max x y ?<= if C) = (z < x ?<= if C) || (z < y ?<= if C).
Proof. by case: C; rewrite /= (le_maxr, lt_maxr). Qed.

Lemma lteif_maxl z x y C :
  (Order.max x y < z ?<= if C) = (x < z ?<= if C) && (y < z ?<= if C).
Proof. by case: C; rewrite /= (le_maxl, lt_maxl). Qed.

Section ArgExtremum.

Context (I : finType) (i0 : I) (P : {pred I}) (F : I -> T) (Pi0 : P i0).

Lemma arg_minP: extremum_spec <=%O P F (arg_min i0 P F).
Proof. by apply: extremumP => //; apply: le_trans. Qed.

Lemma arg_maxP: extremum_spec >=%O P F (arg_max i0 P F).
Proof. by apply: extremumP => //; [apply: ge_refl | apply: ge_trans]. Qed.

End ArgExtremum.

Lemma count_le_gt x s : count (<= x) s = size s - count (> x) s.
Proof.
by rewrite -(count_predC (> x)) addKn; apply: eq_count => y; rewrite /= leNgt.
Qed.

Lemma count_lt_ge x s : count (< x) s = size s - count (>= x) s.
Proof.
by rewrite -(count_predC (>= x)) addKn; apply: eq_count => y; rewrite /= ltNge.
Qed.

Section bigminmax_Type.
Variables (I : Type) (r : seq I) (x : T).
Implicit Types (P : pred I) (F : I -> T).

Lemma bigmin_mkcond P F : \big[min/x]_(i <- r | P i) F i =
  \big[min/x]_(i <- r) (if P i then F i else x).
Proof. by rewrite big_mkcond_idem //= minxx. Qed.

Lemma bigmax_mkcond P F :
  \big[max/x]_(i <- r | P i) F i = \big[max/x]_(i <- r) if P i then F i else x.
Proof. by rewrite big_mkcond_idem //= maxxx. Qed.

Lemma bigmin_split P F1 F2 :
  \big[min/x]_(i <- r | P i) (min (F1 i) (F2 i)) =
    min (\big[min/x]_(i <- r | P i) F1 i) (\big[min/x]_(i <- r | P i) F2 i).
Proof. by rewrite big_split_idem //= minxx. Qed.

Lemma bigmax_split P F1 F2 :
  \big[max/x]_(i <- r | P i) (max (F1 i) (F2 i)) =
    max (\big[max/x]_(i <- r | P i) F1 i) (\big[max/x]_(i <- r | P i) F2 i).
Proof. by rewrite big_split_idem //= maxxx. Qed.

Lemma bigmin_idl P F :
  \big[min/x]_(i <- r | P i) F i = min x (\big[min/x]_(i <- r | P i) F i).
Proof. by rewrite minC big_id_idem //= minxx. Qed.

Lemma bigmax_idl P F :
  \big[max/x]_(i <- r | P i) F i = max x (\big[max/x]_(i <- r | P i) F i).
Proof. by rewrite maxC big_id_idem //= maxxx. Qed.

Lemma bigmin_idr P F :
  \big[min/x]_(i <- r | P i) F i = min (\big[min/x]_(i <- r | P i) F i) x.
Proof. by rewrite [LHS]bigmin_idl minC. Qed.

Lemma bigmax_idr P F :
  \big[max/x]_(i <- r | P i) F i = max (\big[max/x]_(i <- r | P i) F i) x.
Proof. by rewrite [LHS]bigmax_idl maxC. Qed.

Lemma bigminID a P F : \big[min/x]_(i <- r | P i) F i =
  min (\big[min/x]_(i <- r | P i && a i) F i)
      (\big[min/x]_(i <- r | P i && ~~ a i) F i).
Proof. by rewrite (bigID_idem _ _ a) //= minxx. Qed.

Lemma bigmaxID a P F : \big[max/x]_(i <- r | P i) F i =
  max (\big[max/x]_(i <- r | P i && a i) F i)
      (\big[max/x]_(i <- r | P i && ~~ a i) F i).
Proof. by rewrite (bigID_idem _ _ a) //= maxxx. Qed.

End bigminmax_Type.

Let le_minr_id (x y : T) : x >= min x y. Proof. by rewrite le_minl lexx. Qed.
Let le_maxr_id (x y : T) : x <= max x y. Proof. by rewrite le_maxr lexx. Qed.

Lemma sub_bigmin [x0] I r (P P' : {pred I}) (F : I -> T) :
    (forall i, P' i -> P i) ->
  \big[min/x0]_(i <- r | P i) F i <= \big[min/x0]_(i <- r | P' i) F i.
Proof. exact: (sub_le_big ge_refl). Qed.

Lemma sub_bigmax [x0] I r (P P' : {pred I}) (F : I -> T) :
    (forall i, P i -> P' i) ->
  \big[max/x0]_(i <- r | P i) F i <= \big[max/x0]_(i <- r | P' i) F i.
Proof. exact: sub_le_big. Qed.

Lemma sub_bigmin_seq [x0] (I : eqType) r r' P (F : I -> T) : {subset r' <= r} ->
  \big[min/x0]_(i <- r | P i) F i <= \big[min/x0]_(i <- r' | P i) F i.
Proof. exact: (idem_sub_le_big ge_refl _ minxx). Qed.

Lemma sub_bigmax_seq [x0] (I : eqType) r r' P (F : I -> T) : {subset r <= r'} ->
  \big[max/x0]_(i <- r | P i) F i <= \big[max/x0]_(i <- r' | P i) F i.
Proof. exact: (idem_sub_le_big _ _ maxxx). Qed.

Lemma sub_bigmin_cond [x0] (I : eqType) r r' P P' (F : I -> T) :
    {subset [seq i <- r | P i] <= [seq i <- r' | P' i]} ->
  \big[min/x0]_(i <- r' | P' i) F i <= \big[min/x0]_(i <- r | P i) F i.
Proof. exact: (idem_sub_le_big_cond ge_refl _ minxx). Qed.

Lemma sub_bigmax_cond [x0] (I : eqType) r r' P P' (F : I -> T) :
    {subset [seq i <- r | P i] <= [seq i <- r' | P' i]} ->
  \big[max/x0]_(i <- r | P i) F i <= \big[max/x0]_(i <- r' | P' i) F i.
Proof. exact: (idem_sub_le_big_cond _ _ maxxx). Qed.

Lemma sub_in_bigmin [x0] [I : eqType] (r : seq I) (P P' : {pred I}) F :
    {in r, forall i, P' i -> P i} ->
  \big[min/x0]_(i <- r | P i) F i <= \big[min/x0]_(i <- r | P' i) F i.
Proof. exact: (sub_in_le_big ge_refl). Qed.

Lemma sub_in_bigmax [x0] [I : eqType] (r : seq I) (P P' : {pred I}) F :
    {in r, forall i, P i -> P' i} ->
  \big[max/x0]_(i <- r | P i) F i <= \big[max/x0]_(i <- r | P' i) F i.
Proof. exact: sub_in_le_big. Qed.

Lemma le_bigmin_nat [x0] n m n' m' P (F : nat -> T) :
    (n <= n')%N -> (m' <= m)%N ->
  \big[min/x0]_(n <= i < m | P i) F i <= \big[min/x0]_(n' <= i < m' | P i) F i.
Proof. exact: (le_big_nat ge_refl). Qed.

Lemma le_bigmax_nat [x0] n m n' m' P (F : nat -> T) :
    (n' <= n)%N -> (m <= m')%N ->
  \big[max/x0]_(n <= i < m | P i) F i <= \big[max/x0]_(n' <= i < m' | P i) F i.
Proof. exact: le_big_nat. Qed.

Lemma le_bigmin_nat_cond [x0] n m n' m' (P P' : pred nat) (F : nat -> T) :
    (n <= n')%N -> (m' <= m)%N -> (forall i, (n' <= i < m')%N -> P' i -> P i) ->
  \big[min/x0]_(n <= i < m | P i) F i <= \big[min/x0]_(n' <= i < m' | P' i) F i.
Proof. exact: (le_big_nat_cond ge_refl). Qed.

Lemma le_bigmax_nat_cond [x0] n m n' m' (P P' : {pred nat}) (F : nat -> T) :
    (n' <= n)%N -> (m <= m')%N -> (forall i, (n <= i < m)%N -> P i -> P' i) ->
  \big[max/x0]_(n <= i < m | P i) F i <= \big[max/x0]_(n' <= i < m' | P' i) F i.
Proof. exact: le_big_nat_cond. Qed.

Lemma le_bigmin_ord [x0] n m (P : pred nat) (F : nat -> T) : (m <= n)%N ->
  \big[min/x0]_(i < n | P i) F i <= \big[min/x0]_(i < m | P i) F i.
Proof. exact: (le_big_ord ge_refl). Qed.

Lemma le_bigmax_ord [x0] n m (P : {pred nat}) (F : nat -> T) : (n <= m)%N ->
  \big[max/x0]_(i < n | P i) F i <= \big[max/x0]_(i < m | P i) F i.
Proof. exact: le_big_ord. Qed.

Lemma le_bigmin_ord_cond [x0] n m (P P' : pred nat) (F : nat -> T) :
    (m <= n)%N -> (forall i : 'I_m, P' i -> P i) ->
  \big[min/x0]_(i < n | P i) F i <= \big[min/x0]_(i < m | P' i) F i.
Proof. exact: (le_big_ord_cond ge_refl). Qed.

Lemma le_bigmax_ord_cond [x0] n m (P P' : {pred nat}) (F : nat -> T) :
    (n <= m)%N -> (forall i : 'I_n, P i -> P' i) ->
  \big[max/x0]_(i < n | P i) F i <= \big[max/x0]_(i < m | P' i) F i.
Proof. exact: le_big_ord_cond. Qed.

Lemma subset_bigmin [x0] [I : finType] [A A' P : {pred I}] (F : I -> T) :
    A' \subset A ->
  \big[min/x0]_(i in A | P i) F i <= \big[min/x0]_(i in A' | P i) F i.
Proof. exact: (subset_le_big ge_refl). Qed.

Lemma subset_bigmax [x0] [I : finType] (A A' P : {pred I}) (F : I -> T) :
    A \subset A' ->
  \big[max/x0]_(i in A | P i) F i <= \big[max/x0]_(i in A' | P i) F i.
Proof. exact: subset_le_big. Qed.

Lemma subset_bigmin_cond [x0] (I : finType) (A A' P P' : {pred I}) (F : I -> T) :
    [set i in A' | P' i]  \subset [set i in A | P i] ->
  \big[min/x0]_(i in A | P i) F i <= \big[min/x0]_(i in A' | P' i) F i.
Proof. exact: (subset_le_big_cond ge_refl). Qed.

Lemma subset_bigmax_cond [x0] (I : finType) (A A' P P' : {pred I}) (F : I -> T) :
    [set i in A | P i]  \subset [set i in A' | P' i] ->
  \big[max/x0]_(i in A | P i) F i <= \big[max/x0]_(i in A' | P' i) F i.
Proof. exact: subset_le_big_cond. Qed.

Section bigminmax_finType.
Variable (I : finType) (x : T).
Implicit Types (P : pred I) (F : I -> T).

Lemma bigminD1 j P F : P j ->
  \big[min/x]_(i | P i) F i = min (F j) (\big[min/x]_(i | P i && (i != j)) F i).
Proof. by move/(bigD1 _) ->. Qed.

Lemma bigmaxD1 j P F : P j ->
  \big[max/x]_(i | P i) F i = max (F j) (\big[max/x]_(i | P i && (i != j)) F i).
Proof. by move/(bigD1 _) ->. Qed.

Lemma bigmin_le_cond j P F : P j -> \big[min/x]_(i | P i) F i <= F j.
Proof.
have := mem_index_enum j; rewrite unlock; elim: (index_enum I) => //= i l ih.
rewrite inE => /orP [/eqP-> ->|/ih leminlfi Pi]; first by rewrite le_minl lexx.
by case: ifPn => Pj; [rewrite le_minl leminlfi// orbC|exact: leminlfi].
Qed.

Lemma le_bigmax_cond j P F : P j -> F j <= \big[max/x]_(i | P i) F i.
Proof. by move=> Pj; rewrite (bigmaxD1 _ Pj) le_maxr lexx. Qed.

Lemma bigmin_le j F : \big[min/x]_i F i <= F j.
Proof. exact: bigmin_le_cond. Qed.

Lemma le_bigmax F j : F j <= \big[max/x]_i F i.
Proof. exact: le_bigmax_cond. Qed.

Lemma bigmin_inf j P m F : P j -> F j <= m -> \big[min/x]_(i | P i) F i <= m.
Proof. by move=> Pj ?; apply: le_trans (bigmin_le_cond _ Pj) _. Qed.

(* NB: as of [2022-08-02], bigop.bigmax_sup already exists for nat *)
Lemma bigmax_sup j P m F : P j -> m <= F j -> m <= \big[max/x]_(i | P i) F i.
Proof. by move=> Pj ?; apply: le_trans (le_bigmax_cond _ Pj). Qed.

Lemma bigmin_geP m P F :
  reflect (m <= x /\ forall i, P i -> m <= F i)
          (m <= \big[min/x]_(i | P i) F i).
Proof.
apply: (iffP idP) => [lemFi|[lemx lemPi]]; [split|exact: le_bigmin].
- by rewrite (le_trans lemFi)// bigmin_idl le_minl lexx.
- by move=> i Pi; rewrite (le_trans lemFi)// (bigminD1 _ Pi)// le_minl lexx.
Qed.

Lemma bigmax_leP m P F :
  reflect (x <= m /\ forall i, P i -> F i <= m)
          (\big[max/x]_(i | P i) F i <= m).
Proof.
apply: (iffP idP) => [|[? ?]]; last exact: bigmax_le.
rewrite bigmax_idl le_maxl => /andP[-> leFm]; split=> // i Pi.
by apply: le_trans leFm; exact: le_bigmax_cond.
Qed.

Lemma bigmin_gtP m P F :
  reflect (m < x /\ forall i, P i -> m < F i) (m < \big[min/x]_(i | P i) F i).
Proof.
apply: (iffP idP) => [lemFi|[lemx lemPi]]; [split|exact: lt_bigmin].
- by rewrite (lt_le_trans lemFi)// bigmin_idl le_minl lexx.
- by move=> i Pi; rewrite (lt_le_trans lemFi)// (bigminD1 _ Pi)// le_minl lexx.
Qed.

Lemma bigmax_ltP m P F :
  reflect (x < m /\ forall i, P i -> F i < m) (\big[max/x]_(i | P i) F i < m).
Proof.
apply: (iffP idP) => [|[? ?]]; last exact: bigmax_lt.
rewrite bigmax_idl lt_maxl => /andP[-> ltFm]; split=> // i Pi.
by apply: le_lt_trans ltFm; exact: le_bigmax_cond.
Qed.

Lemma bigmin_eq_arg j P F : P j -> (forall i, P i -> F i <= x) ->
  \big[min/x]_(i | P i) F i = F [arg min_(i < j | P i) F i].
Proof.
move=> Pi0; case: arg_minP => //= i Pi PF PFx.
apply/eqP; rewrite eq_le bigmin_le_cond //=.
by apply/bigmin_geP; split => //; exact: PFx.
Qed.

Lemma bigmax_eq_arg j P F : P j -> (forall i, P i -> x <= F i) ->
  \big[max/x]_(i | P i) F i = F [arg max_(i > j | P i) F i].
Proof.
move=> Pi0; case: arg_maxP => //= i Pi PF PxF.
apply/eqP; rewrite eq_le le_bigmax_cond // andbT.
by apply/bigmax_leP; split => //; exact: PxF.
Qed.

Lemma eq_bigmin j P F : P j -> (forall i, P i -> F i <= x) ->
  {i0 | i0 \in P & \big[min/x]_(i | P i) F i = F i0}.
Proof.
by move=> Pi0 Hx; rewrite (bigmin_eq_arg Pi0) //; eexists=> //; case: arg_minP.
Qed.

Lemma eq_bigmax j P F : P j -> (forall i, P i -> x <= F i) ->
  {i0 | i0 \in P & \big[max/x]_(i | P i) F i = F i0}.
Proof.
by move=> Pi0 Hx; rewrite (bigmax_eq_arg Pi0) //; eexists=> //; case: arg_maxP.
Qed.

Lemma le_bigmin2 P F1 F2 : (forall i, P i -> F1 i <= F2 i) ->
  \big[min/x]_(i | P i) F1 i <= \big[min/x]_(i | P i) F2 i.
Proof.
move=> FG; elim/big_ind2 : _ => // a b e f ba fe.
rewrite le_minl 2!le_minr ba fe /= andbT.
move: (le_total a e) => /orP[/(le_trans ba)-> // | /(le_trans fe)->].
by rewrite orbT.
Qed.

Lemma le_bigmax2 P F1 F2 : (forall i, P i -> F1 i <= F2 i) ->
  \big[max/x]_(i | P i) F1 i <= \big[max/x]_(i | P i) F2 i.
Proof.
move=> FG; elim/big_ind2 : _ => // a b e f ba fe.
rewrite le_maxr 2!le_maxl ba fe /= andbT; have [//|/= af] := leP f a.
by rewrite (le_trans ba) // (le_trans _ fe) // ltW.
Qed.

End bigminmax_finType.

End TotalTheory.

#[global] Hint Resolve le_total : core.
#[global] Hint Resolve ge_total : core.
#[global] Hint Resolve comparableT : core.
#[global] Hint Resolve sort_le_sorted : core.

Arguments min_idPr {disp T x y}.
Arguments max_idPl {disp T x y}.
Arguments bigmin_mkcond {disp T I r}.
Arguments bigmax_mkcond {disp T I r}.
Arguments bigminID {disp T I r}.
Arguments bigmaxID {disp T I r}.
Arguments bigminD1 {disp T I x} j.
Arguments bigmaxD1 {disp T I x} j.
Arguments bigmin_inf {disp T I x} j.
Arguments bigmax_sup {disp T I x} j.
Arguments bigmin_eq_arg {disp T I} x j.
Arguments bigmax_eq_arg {disp T I} x j.
Arguments eq_bigmin {disp T I x} j.
Arguments eq_bigmax {disp T I x} j.

(* contra lemmas *)

Section ContraTheory.
Context {disp1 disp2 : unit} {T1 : porderType disp1} {T2 : orderType disp2}.
Implicit Types (x y : T1) (z t : T2) (b : bool) (m n : nat) (P : Prop).

Lemma contraTle b z t : (t < z -> ~~ b) -> (b -> z <= t).
Proof. exact: comparable_contraTle. Qed.

Lemma contraTlt b z t : (t <= z -> ~~ b) -> (b -> z < t).
Proof. exact: comparable_contraTlt. Qed.

Lemma contraPle P z t : (t < z -> ~ P) -> (P -> z <= t).
Proof. exact: comparable_contraPle. Qed.

Lemma contraPlt P z t : (t <= z -> ~ P) -> (P -> z < t).
Proof. exact: comparable_contraPlt. Qed.

Lemma contraNle b z t : (t < z -> b) -> (~~ b -> z <= t).
Proof. exact: comparable_contraNle. Qed.

Lemma contraNlt b z t : (t <= z -> b) -> (~~ b -> z < t).
Proof. exact: comparable_contraNlt. Qed.

Lemma contra_not_le P z t : (t < z -> P) -> (~ P -> z <= t).
Proof. exact: comparable_contra_not_le. Qed.

Lemma contra_not_lt P z t : (t <= z -> P) -> (~ P -> z < t).
Proof. exact: comparable_contra_not_lt. Qed.

Lemma contraFle b z t : (t < z -> b) -> (b = false -> z <= t).
Proof. exact: comparable_contraFle. Qed.

Lemma contraFlt b z t : (t <= z -> b) -> (b = false -> z < t).
Proof. exact: comparable_contraFlt. Qed.

Lemma contra_leq_le m n z t : (t < z -> (n < m)%N) -> ((m <= n)%N -> z <= t).
Proof. exact: comparable_contra_leq_le. Qed.

Lemma contra_leq_lt m n z t : (t <= z -> (n < m)%N) -> ((m <= n)%N -> z < t).
Proof. exact: comparable_contra_leq_lt. Qed.

Lemma contra_ltn_le m n z t : (t < z -> (n <= m)%N) -> ((m < n)%N -> z <= t).
Proof. exact: comparable_contra_ltn_le. Qed.

Lemma contra_ltn_lt m n z t : (t <= z -> (n <= m)%N) -> ((m < n)%N -> z < t).
Proof. exact: comparable_contra_ltn_lt. Qed.

Lemma contra_le x y z t : (t < z -> y < x) -> (x <= y -> z <= t).
Proof. exact: comparable_contra_le. Qed.

Lemma contra_le_lt x y z t : (t <= z -> y < x) -> (x <= y -> z < t).
Proof. exact: comparable_contra_le_lt. Qed.

Lemma contra_lt_le x y z t : (t < z -> y <= x) -> (x < y -> z <= t).
Proof. exact: comparable_contra_lt_le. Qed.

Lemma contra_lt x y z t : (t <= z -> y <= x) -> (x < y -> z < t).
Proof. exact: comparable_contra_lt. Qed.

End ContraTheory.

Section TotalMonotonyTheory.

Context {disp : unit} {disp' : unit}.
Context {T : orderType disp} {T' : porderType disp'}.
Variables (D : {pred T}) (f : T -> T').
Implicit Types (x y z : T) (u v w : T').

Let leT_anti    := @le_anti _ T.
Let leT'_anti   := @le_anti _ T'.
Let ltT_neqAle  := @lt_neqAle _ T.
Let ltT'_neqAle := @lt_neqAle _ T'.
Let ltT_def     := @lt_def _ T.
Let leT_total   := @le_total _ T.

Lemma le_mono : {homo f : x y / x < y} -> {mono f : x y / x <= y}.
Proof. exact: total_homo_mono. Qed.

Lemma le_nmono : {homo f : x y /~ x < y} -> {mono f : x y /~ x <= y}.
Proof. exact: total_homo_mono. Qed.

Lemma le_mono_in :
  {in D &, {homo f : x y / x < y}} -> {in D &, {mono f : x y / x <= y}}.
Proof. exact: total_homo_mono_in. Qed.

Lemma le_nmono_in :
  {in D &, {homo f : x y /~ x < y}} -> {in D &, {mono f : x y /~ x <= y}}.
Proof. exact: total_homo_mono_in. Qed.

End TotalMonotonyTheory.
End TotalTheory.

Module Import BLatticeTheory.
Section BLatticeTheory.
Context {disp : unit} {L : bLatticeType disp}.
Implicit Types (I : finType) (T : eqType) (x y z : L).
Local Notation "0" := bottom.

(* Non-distributive lattice theory with 0 & 1*)
Lemma le0x x : 0 <= x. Proof. exact: le0x. Qed.
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

Lemma join_eq0 x y : (x `|` y == 0) = (x == 0) && (y == 0).
Proof.
apply/idP/idP; last by move=> /andP [/eqP-> /eqP->]; rewrite joinx0.
by move=> /eqP xUy0; rewrite -!lex0 -!xUy0 ?leUl ?leUr.
Qed.

Variant eq0_xor_gt0 x : bool -> bool -> Set :=
    Eq0NotPOs : x = 0 -> eq0_xor_gt0 x true false
  | POsNotEq0 : 0 < x -> eq0_xor_gt0 x false true.

Lemma posxP x : eq0_xor_gt0 x (x == 0) (0 < x).
Proof. by rewrite lt0x; have [] := eqVneq; constructor; rewrite ?lt0x. Qed.

HB.instance Definition _ := Monoid.isComLaw.Build L 0 join
  (@joinA _ L) (@joinC _ L) join0x.

Lemma joins_sup_seq T (r : seq T) (P : {pred T}) (F : T -> L) (x : T) :
  x \in r -> P x -> F x <= \join_(i <- r | P i) F i.
Proof. by move=> xr Px; rewrite (big_rem x) ?Px //= leUl. Qed.

Lemma joins_min_seq T (r : seq T) (P : {pred T}) (F : T -> L) (x : T) (l : L) :
  x \in r -> P x -> l <= F x -> l <= \join_(x <- r | P x) F x.
Proof. by move=> ? ? /le_trans; apply; apply: joins_sup_seq. Qed.

Lemma joins_sup I (j : I) (P : {pred I}) (F : I -> L) :
  P j -> F j <= \join_(i | P i) F i.
Proof. exact: joins_sup_seq. Qed.

Lemma joins_min I (j : I) (l : L) (P : {pred I}) (F : I -> L) :
  P j -> l <= F j -> l <= \join_(i | P i) F i.
Proof. exact: joins_min_seq. Qed.

Lemma joins_le J (r : seq J) (P : {pred J}) (F : J -> L) (u : L) :
  (forall x : J, P x -> F x <= u) -> \join_(x <- r | P x) F x <= u.
Proof. by move=> leFm; elim/big_rec: _ => // i x Px xu; rewrite leUx leFm. Qed.

Lemma joinsP_seq T (r : seq T) (P : {pred T}) (F : T -> L) (u : L) :
  reflect (forall x : T, x \in r -> P x -> F x <= u)
          (\join_(x <- r | P x) F x <= u).
Proof.
apply: (iffP idP) => leFm => [x xr Px|].
  exact/(le_trans _ leFm)/joins_sup_seq.
by rewrite big_seq_cond joins_le// => x /andP[/leFm].
Qed.

Lemma joinsP I (u : L) (P : {pred I}) (F : I -> L) :
  reflect (forall i : I, P i -> F i <= u) (\join_(i | P i) F i <= u).
Proof. by apply: (iffP (joinsP_seq _ _ _ _)) => H ? ?; apply: H. Qed.

Lemma le_joins I (A B : {set I}) (F : I -> L) :
  A \subset B -> \join_(i in A) F i <= \join_(i in B) F i.
Proof. by move=> /subsetP AB; apply/joinsP => i iA; apply/joins_sup/AB. Qed.

Lemma joins_setU I (A B : {set I}) (F : I -> L) :
  \join_(i in (A :|: B)) F i = \join_(i in A) F i `|` \join_(i in B) F i.
Proof.
rewrite -!big_enum; have /= <- := @big_cat _ _ [the Monoid.com_law _ of join].
apply/eq_big_idem; first exact: joinxx.
by move=> ?; rewrite mem_cat !mem_enum inE.
Qed.

Lemma joins_seq I (r : seq I) (F : I -> L) :
  \join_(i <- r) F i = \join_(i in r) F i.
Proof.
by rewrite -big_enum; apply/eq_big_idem => ?; rewrite /= ?joinxx ?mem_enum.
Qed.

End BLatticeTheory.

End BLatticeTheory.

Module Import DualTBLattice.
Section DualTBLattice.
Context {disp : unit} {L : tbLatticeType disp}.

Lemma lex1 (x : L) : x <= top. Proof. exact: lex1. Qed.

HB.instance Definition _ := hasBottom.Build _ L^d lex1.
(* FIXME: BUG? *)
(* HB.instance Definition _ := TBLattice.on L^d. *)
HB.instance Definition _ := hasTop.Build _ L^d (@le0x _ L).

Lemma botEdual : (dual_bottom : L^d) = 1 :> L. Proof. by []. Qed.
Lemma topEdual : (dual_top : L^d) = 0 :> L. Proof. by []. Qed.

End DualTBLattice.

HB.instance Definition _ d (T : finLatticeType d) := FinLattice.on T^d.

End DualTBLattice.

Module Import TBLatticeTheory.
Section TBLatticeTheory.
Context {disp : unit} {L : tbLatticeType disp}.
Implicit Types (I : finType) (T : eqType) (x y : L).

Local Notation "1" := top.

Hint Resolve le0x lex1 : core.

Lemma meetx1 : right_id 1 (@meet _ L).
Proof. exact: (@joinx0 _ [the tbLatticeType _ of L^d]). Qed.

Lemma meet1x : left_id 1 (@meet _ L).
Proof. exact: (@join0x _ [the tbLatticeType _ of L^d]). Qed.

Lemma joinx1 : right_zero 1 (@join _ L).
Proof. exact: (@meetx0 _ [the tbLatticeType _ of L^d]). Qed.

Lemma join1x : left_zero 1 (@join _ L).
Proof. exact: (@meet0x _ [the tbLatticeType _ of L^d]). Qed.

Lemma le1x x : (1 <= x) = (x == 1).
Proof. exact: (@lex0 _ [the tbLatticeType _ of L^d]). Qed.

Lemma meet_eq1 x y : (x `&` y == 1) = (x == 1) && (y == 1).
Proof. exact: (@join_eq0 _ [the tbLatticeType _ of L^d]). Qed.

HB.instance Definition _ := Monoid.isComLaw.Build L 1 meet
  (@meetA _ L) (@meetC _ L) meet1x.

HB.instance Definition _ := Monoid.isMulLaw.Build L 0 meet
  (@meet0x _ L) (@meetx0 _ _).
HB.instance Definition _ := Monoid.isMulLaw.Build L 1 join join1x joinx1.

Lemma meets_inf_seq T (r : seq T) (P : {pred T}) (F : T -> L) (x : T) :
  x \in r -> P x -> \meet_(i <- r | P i) F i <= F x.
Proof. exact: (@joins_sup_seq _ [the tbLatticeType _ of L^d]). Qed.

Lemma meets_max_seq T (r : seq T) (P : {pred T}) (F : T -> L) (x : T) (u : L) :
  x \in r -> P x -> F x <= u -> \meet_(x <- r | P x) F x <= u.
Proof. exact: (@joins_min_seq _ [the tbLatticeType _ of L^d]). Qed.

Lemma meets_inf I (j : I) (P : {pred I}) (F : I -> L) :
   P j -> \meet_(i | P i) F i <= F j.
Proof. exact: (@joins_sup _ [the tbLatticeType _ of L^d]). Qed.

Lemma meets_max I (j : I) (u : L) (P : {pred I}) (F : I -> L) :
   P j -> F j <= u -> \meet_(i | P i) F i <= u.
Proof. exact: (@joins_min _ [the tbLatticeType _ of L^d]). Qed.

Lemma meets_ge J (r : seq J) (P : {pred J}) (F : J -> L) (u : L) :
  (forall x : J, P x -> u <= F x) -> u <= \meet_(x <- r | P x) F x.
Proof. exact: (@joins_le _ [the tbLatticeType _ of L^d]). Qed.

Lemma meetsP I (l : L) (P : {pred I}) (F : I -> L) :
   reflect (forall i : I, P i -> l <= F i) (l <= \meet_(i | P i) F i).
Proof. exact: (@joinsP _ [the tbLatticeType _ of L^d]). Qed.

Lemma meetsP_seq T (r : seq T) (P : {pred T}) (F : T -> L) (l : L) :
  reflect (forall x : T, x \in r -> P x -> l <= F x)
          (l <= \meet_(x <- r | P x) F x).
Proof. exact: (@joinsP_seq _ [the tbLatticeType _ of L^d]). Qed.

Lemma le_meets I (A B : {set I}) (F : I -> L) :
   A \subset B -> \meet_(i in B) F i <= \meet_(i in A) F i.
Proof. exact: (@le_joins _ [the tbLatticeType _ of L^d]). Qed.

Lemma meets_setU I (A B : {set I}) (F : I -> L) :
   \meet_(i in (A :|: B)) F i = \meet_(i in A) F i `&` \meet_(i in B) F i.
Proof. exact: (@joins_setU _ [the tbLatticeType _ of L^d]). Qed.

Lemma meets_seq I (r : seq I) (F : I -> L) :
   \meet_(i <- r) F i = \meet_(i in r) F i.
Proof. exact: (@joins_seq _ [the tbLatticeType _ of L^d]). Qed.

End TBLatticeTheory.

End TBLatticeTheory.

Module Import BDistrLatticeTheory.
Section BDistrLatticeTheory.
Context {disp : unit} {L : bDistrLatticeType disp}.
Implicit Types (I : finType) (T : eqType) (x y z : L).
Local Notation "0" := bottom.
(* Distributive lattice theory with 0 & 1*)

Lemma leU2l_le y t x z : x `&` t = 0 -> x `|` y <= z `|` t -> x <= z.
Proof.
by move=> xIt0 /(leI2 (lexx x)); rewrite joinKI meetUr xIt0 joinx0 leIidl.
Qed.

Lemma leU2r_le y t x z : x `&` t = 0 -> y `|` x <= t `|` z -> x <= z.
Proof. by rewrite joinC [_ `|` z]joinC => /leU2l_le H /H. Qed.

Lemma disjoint_lexUl z x y : x `&` z = 0 -> (x <= y `|` z) = (x <= y).
Proof.
move=> xz0; apply/idP/idP=> xy; last by rewrite lexU2 ?xy.
by apply: (@leU2l_le x z); rewrite ?joinxx.
Qed.

Lemma disjoint_lexUr z x y : x `&` z = 0 -> (x <= z `|` y) = (x <= y).
Proof. by move=> xz0; rewrite joinC; rewrite disjoint_lexUl. Qed.

Lemma leU2E x y z t : x `&` t = 0 -> y `&` z = 0 ->
  (x `|` y <= z `|` t) = (x <= z) && (y <= t).
Proof.
move=> dxt dyz; apply/idP/andP; last by case=> ? ?; exact: leU2.
by move=> lexyzt; rewrite (leU2l_le _ lexyzt) // (leU2r_le _ lexyzt).
Qed.

Lemma joins_disjoint I (d : L) (P : {pred I}) (F : I -> L) :
   (forall i : I, P i -> d `&` F i = 0) -> d `&` \join_(i | P i) F i = 0.
Proof.
move=> d_Fi_disj; have : \big[andb/true]_(i | P i) (d `&` F i == 0).
  rewrite big_all_cond; apply/allP => i _ /=.
  by apply/implyP => /d_Fi_disj ->.
elim/big_rec2: _ => [|i y]; first by rewrite meetx0.
case; rewrite (andbF, andbT) // => Pi /(_ isT) dy /eqP dFi.
by rewrite meetUr dy dFi joinxx.
Qed.

End BDistrLatticeTheory.
End BDistrLatticeTheory.

Module Import DualTBDistrLattice.
Section DualTBDistrLattice.
Context {disp : unit} {L : tbDistrLatticeType disp}.

HB.instance Definition _ := BDistrLattice.on L^d.
HB.instance Definition _ := TBDistrLattice.on L^d.

End DualTBDistrLattice.

HB.instance Definition _ d (T : finDistrLatticeType d) :=
  FinDistrLattice.on T^d.

End DualTBDistrLattice.

Module Import TBDistrLatticeTheory.
Section TBDistrLatticeTheory.
Context {disp : unit} {L : tbDistrLatticeType disp}.
Implicit Types (I : finType) (T : eqType) (x y : L).

Local Notation "1" := top.

Local Notation Ld := [the tbDistrLatticeType _ of L^d].

Lemma leI2l_le y t x z : y `|` z = 1 -> x `&` y <= z `&` t -> x <= z.
Proof. by rewrite joinC; exact: (@leU2l_le _ Ld). Qed.

Lemma leI2r_le y t x z : y `|` z = 1 -> y `&` x <= t `&` z -> x <= z.
Proof. by rewrite joinC; exact: (@leU2r_le _ Ld). Qed.

Lemma cover_leIxl z x y : z `|` y = 1 -> (x `&` z <= y) = (x <= y).
Proof. by rewrite joinC; exact: (@disjoint_lexUl _ Ld). Qed.

Lemma cover_leIxr z x y : z `|` y = 1 -> (z `&` x <= y) = (x <= y).
Proof. by rewrite joinC; exact: (@disjoint_lexUr _ Ld). Qed.

Lemma leI2E x y z t : x `|` t = 1 -> y `|` z = 1 ->
  (x `&` y <= z `&` t) = (x <= z) && (y <= t).
Proof. by move=> ? ?; apply: (@leU2E _ Ld); rewrite meetC. Qed.

HB.instance Definition _ := Monoid.isAddLaw.Build L meet join
  (@meetUl _ L) (@meetUr _ _).
HB.instance Definition _ := Monoid.isAddLaw.Build L join meet
  (@joinIl _ L) (@joinIr _ _).

Lemma meets_total I (d : L) (P : {pred I}) (F : I -> L) :
   (forall i : I, P i -> d `|` F i = 1) -> d `|` \meet_(i | P i) F i = 1.
Proof. exact: (@joins_disjoint _ Ld). Qed.

End TBDistrLatticeTheory.
End TBDistrLatticeTheory.

Module Import CBDistrLatticeTheory.
Section CBDistrLatticeTheory.
Context {disp : unit} {L : cbDistrLatticeType disp}.
Implicit Types (x y z : L).
Local Notation "0" := bottom.

Lemma subKI x y : y `&` (x `\` y) = 0.
Proof. exact: subKI. Qed.

Lemma subIK x y : (x `\` y) `&` y = 0.
Proof. by rewrite meetC subKI. Qed.

Lemma meetIB z x y : (z `&` y) `&` (x `\` y) = 0.
Proof. by rewrite -meetA subKI meetx0. Qed.

Lemma meetBI z x y : (x `\` y) `&` (z `&` y) = 0.
Proof. by rewrite meetC meetIB. Qed.

Lemma joinIB y x : (x `&` y) `|` (x `\` y) = x.
Proof. exact: joinIB. Qed.

Lemma joinBI y x : (x `\` y) `|` (x `&` y) = x.
Proof. by rewrite joinC joinIB. Qed.

Lemma joinIBC y x : (y `&` x) `|` (x `\` y) = x.
Proof. by rewrite meetC joinIB. Qed.

Lemma joinBIC y x : (x `\` y) `|` (y `&` x) = x.
Proof. by rewrite meetC joinBI. Qed.

Lemma leBx x y : x `\` y <= x.
Proof. by rewrite -{2}[x](joinIB y) lexU2 // lexx orbT. Qed.
Hint Resolve leBx : core.

Lemma subxx x : x `\` x = 0. Proof. by have := subKI x x; rewrite meet_r. Qed.

Lemma leBl z x y : x <= y -> x `\` z <= y `\` z.
Proof.
rewrite -{1}[x](joinIB z) -{1}[y](joinIB z).
by rewrite leU2E ?meetIB ?meetBI // => /andP [].
Qed.

Lemma subKU y x : y `|` (x `\` y) = y `|` x.
Proof.
apply/eqP; rewrite eq_le leU2 //= leUx leUl.
by apply/meet_idPl; have := joinIB y x; rewrite joinIl join_l.
Qed.

Lemma subUK y x : (x `\` y) `|` y = x `|` y.
Proof. by rewrite joinC subKU joinC. Qed.

Lemma leBKU y x : y <= x -> y `|` (x `\` y) = x.
Proof. by move=> /join_r {2}<-; rewrite subKU. Qed.

Lemma leBUK y x : y <= x -> (x `\` y) `|` y = x.
Proof. by move=> leyx; rewrite joinC leBKU. Qed.

Lemma leBLR x y z : (x `\` y <= z) = (x <= y `|` z).
Proof.
apply/idP/idP; first by move=> /join_r <-; rewrite joinA subKU joinAC leUr.
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
Proof. by move=> lexy; rewrite leBLR joinxB meet_r ?leBUK ?leUr ?lexUl. Qed.

Lemma leB2 x y z t : x <= z -> t <= y -> x `\` y <= z `\` t.
Proof. by move=> /(@leBl t) ? /(@leBr x) /le_trans ->. Qed.

Lemma meet_eq0E_sub z x y : x <= z -> (x `&` y == 0) = (x <= z `\` y).
Proof.
move=> xz; apply/idP/idP; last by move=> /meet_r <-; rewrite -meetA meetBI.
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
rewrite joinCA -joinA [_ `|` x]joinC ![x `|` _]join_l //.
by rewrite -joinIl leUr /= meetUl {1}[_ `&` z]meetC ?meetBI joinx0.
Qed.

Lemma subBx x y z : (x `\` y) `\` z = x `\` (y `|` z).
Proof.
apply/eqP; rewrite eq_sub leBr ?leUl //=.
by rewrite subxU joinIr subKU -joinIr meet_l ?leUr //= -meetA subIK meetx0.
Qed.

Lemma subxB x y z : x `\` (y `\` z) = (x `\` y) `|` (x `&` z).
Proof.
rewrite -[y in RHS](joinIB z) subxU joinIl subxI -joinA joinBI join_r //.
by rewrite joinBx meetKU meetA meetAC subIK meet0x joinx0 meet_r.
Qed.

Lemma joinBK x y : (y `|` x) `\` x = (y `\` x).
Proof. by rewrite subUx subxx joinx0. Qed.

Lemma joinBKC x y : (x `|` y) `\` x = (y `\` x).
Proof. by rewrite subUx subxx join0x. Qed.

Lemma disj_le x y : x `&` y == 0 -> x <= y = (x == 0).
Proof. by rewrite [x == 0]eq_sym -eq_meetl => /eqP ->. Qed.

Lemma disj_leC x y : y `&` x == 0 -> x <= y = (x == 0).
Proof. by rewrite meetC => /disj_le. Qed.

Lemma disj_subl x y : x `&` y == 0 -> x `\` y = x.
Proof. by move=> dxy; apply/eqP; rewrite eq_sub dxy lexx leUr. Qed.

Lemma disj_subr x y : x `&` y == 0 -> y `\` x = y.
Proof. by rewrite meetC => /disj_subl. Qed.

Lemma lt0B x y : x < y -> 0 < y `\` x.
Proof. by move=> ?; rewrite lt_leAnge le0x leBLR joinx0 /= lt_geF. Qed.

End CBDistrLatticeTheory.
End CBDistrLatticeTheory.

Module Import CTBDistrLatticeTheory.
Section CTBDistrLatticeTheory.
Context {disp : unit} {L : ctbDistrLatticeType disp}.
Implicit Types (x y z : L).
Local Notation "0" := bottom.
Local Notation "1" := top.

Lemma complE x : ~` x = 1 `\` x.
Proof. exact: complE. Qed.

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

End CTBDistrLatticeTheory.
End CTBDistrLatticeTheory.

(*************)
(* FACTORIES *)
(*************)

HB.factory Record POrder_isMeetDistrLattice d T of POrder d T := {
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

HB.builders
  Context d T of POrder_isMeetDistrLattice d T.

HB.instance Definition _ :=
  POrder_isLattice.Build d T meetC joinC meetA joinA joinKI meetKU leEmeet.
HB.instance Definition _ :=
  Lattice_MeetIsDistributive.Build d T meetUl.

HB.end.

HB.factory Record Lattice_isTotal d T of Lattice d T := {
  le_total : total (<=%O : rel T)
}.

HB.builders Context d T of Lattice_isTotal d T.

Implicit Types (x y z : T).

Let comparableT x y : x >=< y := le_total x y.

Fact meetUl : @left_distributive T T meet join.
Proof.
pose leP x y := lcomparable_leP (comparableT x y).
move=> x y z; case: (leP x z); case: (leP y z); case: (leP x y);
  case: (leP x z); case: (leP y z); case: (leP x y) => //= xy yz xz _ _ _;
  rewrite ?joinxx //.
- by move: (le_lt_trans xz (lt_trans yz xy)); rewrite ltxx.
- by move: (lt_le_trans xz (le_trans xy yz)); rewrite ltxx.
Qed.

HB.instance Definition _ :=
  Lattice_MeetIsDistributive.Build d T meetUl.
HB.instance Definition _ :=
  DistrLattice_isTotal.Build d T comparableT.

HB.end.

HB.factory Record POrder_isTotal d T of POrder d T := {
  le_total : total (<=%O : rel T) }.

HB.builders
  Context d T of POrder_isTotal d T.

Implicit Types (x y z : T).

Let comparableT x y : x >=< y := le_total x y.

Fact ltgtP x y :
  compare x y (min y x) (min x y) (max y x) (max x y)
              (y == x) (x == y) (x >= y) (x <= y) (x > y) (x < y).
Proof. exact: comparable_ltgtP. Qed.

Fact leP x y : le_xor_gt x y
  (min y x) (min x y) (max y x) (max x y) (x <= y) (y < x).
Proof. exact: comparable_leP. Qed.

Definition meet := @min _ [porderType of T].
Definition join := @max _ [porderType of T].

Fact meetC : commutative meet.
Proof. by move=> x y; rewrite /meet; have [] := ltgtP. Qed.

Fact joinC : commutative join.
Proof. by move=> x y; rewrite /join; have [] := ltgtP. Qed.

Fact meetA : associative meet.
Proof.
move=> x y z; rewrite /meet /min !(fun_if, if_arg).
case: (leP z y) (leP y x) (leP z x) => [] zy [] yx [] zx//=.
  by have := le_lt_trans (le_trans zy yx) zx; rewrite ltxx.
by apply/eqP; rewrite eq_le zx ltW// (lt_trans yx).
Qed.

Fact joinA : associative join.
Proof.
move=> x y z; rewrite /meet /min !(fun_if, if_arg).
case: (leP z y) (leP y x) (leP z x) => [] zy [] yx [] zx//=.
  by have := le_lt_trans (le_trans zy yx) zx; rewrite ltxx.
by apply/eqP; rewrite eq_le zx ltW// (lt_trans yx).
Qed.

Fact joinKI y x : meet x (join x y) = x.
Proof.
rewrite /meet /join /min /max !(fun_if, if_arg).
by have []// := ltgtP x y; rewrite ltxx.
Qed.

Fact meetKU y x : join x (meet x y) = x.
Proof.
rewrite /meet /join /min /max !(fun_if, if_arg).
by have []// := ltgtP x y; rewrite ltxx.
Qed.

Fact leEmeet x y : (x <= y) = (meet x y == x).
Proof. by rewrite /meet; case: leP => ?; rewrite ?eqxx ?lt_eqF. Qed.

HB.instance Definition _ :=
  POrder_isLattice.Build d T meetC joinC meetA joinA joinKI meetKU leEmeet.
HB.instance Definition _ :=
  Lattice_isTotal.Build d T comparableT.
HB.end.

(* was MeetJoinMixin *)
HB.factory Record isMeetJoinDistrLattice (d : unit) T of Choice T := {
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
  meetxx : idempotent meet;
}.

HB.builders
  Context (d : unit) T of isMeetJoinDistrLattice d T.

Fact le_refl : reflexive le. Proof. by move=> x; rewrite le_def meetxx. Qed.

Fact le_anti : antisymmetric le.
Proof. by move=> x y; rewrite !le_def meetC => /andP [] /eqP {2}<- /eqP ->. Qed.

Fact le_trans : transitive le.
Proof.
move=> y x z; rewrite !le_def => /eqP lexy /eqP leyz; apply/eqP.
by rewrite -[in LHS]lexy -meetA leyz lexy.
Qed.

HB.instance Definition _ := isPOrdered.Build d T
  lt_def le_refl le_anti le_trans.

HB.instance Definition _ := POrder_isMeetDistrLattice.Build d T
  meetC joinC meetA joinA joinKI meetKU le_def meetUl.

HB.end.

(* FIXME: doesn't typecheck

HB.factory Record leOrder T of Choice T := {
  le : rel T;
  lt : rel T;
  meet : T -> T -> T;
  join : T -> T -> T;
  lt_def : forall x y, lt x y = (y != x) && le x y;
  meet_def : forall x y, meet x y = if lt x y then x else y;
  join_def : forall x y, join x y = if lt x y then y else x;
  le_anti : antisymmetric le;
  le_trans : transitive le;
  le_total : total le;
}.*)

(* workaround *)
HB.factory Record isOrdered (d : unit) T of Choice T := {
  le : rel T;
  lt : rel T;
  meet : T -> T -> T;
  join : T -> T -> T;
  lt_def : forall x y, lt x y = (y != x) && le x y;
  meet_def : forall x y, meet x y = match lt x y with
                               | true => x
                               | false => y
                               end;
  join_def : forall x y, join x y = match lt x y with
                               | true => y
                               | false => x
                               end;
  le_anti : antisymmetric le;
  le_trans : transitive le;
  le_total : total le;
}.

HB.builders
  Context (d : unit) T of isOrdered d T.

Fact le_refl : reflexive le.
Proof. by move=> x; case: (le x x) (le_total x x). Qed.

HB.instance Definition _ := isPOrdered.Build d T
  lt_def le_refl le_anti le_trans.

Section GeneratedOrder.

Local Definition T' := T.
HB.instance Definition _ := POrder.on T'.
HB.instance Definition _ := POrder_isTotal.Build d T' le_total.
Implicit Types (x y z : T').

Fact meetE x y : meet x y = x `&` y. Proof. by rewrite meet_def. Qed.
Fact joinE x y : join x y = x `|` y. Proof. by rewrite join_def. Qed.
Fact meetC : commutative meet.
Proof. by move=> *; rewrite !meetE meetC. Qed.
Fact joinC : commutative join.
Proof. by move=> *; rewrite !joinE joinC. Qed.
Fact meetA : associative meet.
Proof. by move=> *; rewrite !meetE meetA. Qed.
Fact joinA : associative join.
Proof. by move=> *; rewrite !joinE joinA. Qed.
Fact joinKI y x : meet x (join x y) = x.
Proof. by rewrite meetE joinE joinKI. Qed.
Fact meetKU y x : join x (meet x y) = x.
Proof. by rewrite meetE joinE meetKU. Qed.
Fact meetUl : left_distributive meet join.
Proof. by move=> *; rewrite !meetE !joinE meetUl. Qed.
Fact meetxx : idempotent meet.
Proof. by move=> *; rewrite meetE meetxx. Qed.
Fact le_def x y : x <= y = (meet x y == x).
Proof. by rewrite meetE (eq_meetl x y). Qed.

End GeneratedOrder.

HB.instance Definition _ :=
  POrder_isMeetDistrLattice.Build d T meetC joinC meetA joinA
                                      joinKI meetKU le_def meetUl.
HB.instance Definition _ := DistrLattice_isTotal.Build d T le_total.

HB.end.

(* was LtOrderMixin *)
HB.factory Record LtOrder (d : unit) T of Choice T := {
  le : rel T;
  lt : rel T;
  meet : T -> T -> T;
  join : T -> T -> T;
  le_def   : forall x y, le x y = (x == y) || lt x y;
  meet_def : forall x y, meet x y = match lt x y with
                               | true => x
                               | false => y
                               end;
  join_def : forall x y, join x y = match lt x y with
                               | true => y
                               | false => x
                               end;
  lt_irr   : irreflexive lt;
  lt_trans : transitive lt;
  lt_total : forall x y, x != y -> lt x y || lt y x;
}.

HB.builders
  Context d T of LtOrder d T.

Fact lt_def x y : lt x y = (y != x) && le x y.
Proof. by rewrite le_def; case: eqVneq => //= ->; rewrite lt_irr. Qed.

Fact meet_def_le x y : meet x y = if lt x y then x else y.
Proof. by rewrite meet_def lt_def; case: eqP. Qed.

Fact join_def_le x y : join x y = if lt x y then y else x.
Proof. by rewrite join_def lt_def; case: eqP. Qed.

Fact le_anti : antisymmetric le.
Proof.
move=> x y; rewrite !le_def; case: eqVneq => //= _ /andP [] hxy.
by move/(lt_trans hxy); rewrite lt_irr.
Qed.

Fact le_trans : transitive le.
Proof.
move=> y x z; rewrite !le_def; case: eqVneq => [->|_] //=.
by case: eqVneq => [-> ->|_ hxy /(lt_trans hxy) ->]; rewrite orbT.
Qed.

Fact le_total : total le.
Proof. by move=> x y; rewrite !le_def; case: eqVneq => //; exact: lt_total. Qed.

HB.instance Definition _ :=
  isOrdered.Build d T lt_def meet_def_le join_def_le le_anti le_trans le_total.
HB.end.

HB.factory Record MonoTotal disp T of POrder disp T := {
  disp' : unit;
  T' : orderType disp';
  f : T -> T';
  f_mono : {mono f : x y / x <= y}
}.
HB.builders Context disp T of MonoTotal disp T.
Lemma totalT : total (<=%O : rel T).
Proof. by move=> x y; rewrite -!f_mono le_total. Qed.
HB.instance Definition _ := POrder_isTotal.Build disp T totalT.
HB.end.

Module CancelPartial.
Section CancelPartial.
Variables (disp : unit) (T : choiceType).
Variables (disp' : unit) (T' : porderType disp') (f : T -> T').

Section PCan.
Variables (f' : T' -> option T) (f_can : pcancel f f').

Definition le (x y : T) := f x <= f y.
Definition lt (x y : T) := f x < f y.

Fact refl : reflexive le. Proof. by move=> ?; apply: lexx. Qed.
Fact anti : antisymmetric le.
Proof. by move=> x y /le_anti /(pcan_inj f_can). Qed.
Fact trans : transitive le. Proof. by move=> y x z xy /(le_trans xy). Qed.
Fact lt_def x y : lt x y = (y != x) && le x y.
Proof. by rewrite /lt lt_def (inj_eq (pcan_inj f_can)). Qed.

Definition Pcan := isPOrdered.Build disp T lt_def refl anti trans.

End PCan.

Definition Can f' (f_can : cancel f f') := Pcan (can_pcan f_can).

End CancelPartial.
End CancelPartial.

Notation PcanPartial := CancelPartial.Pcan.
Notation CanPartial := CancelPartial.Can.

#[export]
HB.instance Definition _ (disp : unit) (T : choiceType)
  (disp' : unit) (T' : porderType disp') (f : T -> T')
  (f' : T' -> option T) (f_can : pcancel f f') : isPOrdered disp (pcan_type f_can) :=
  PcanPartial disp (f_can : @pcancel _ (pcan_type f_can)  f f').

#[export]
HB.instance Definition _ (disp : unit) (T : choiceType)
  (disp' : unit) (T' : porderType disp') (f : T -> T') (f' : T' ->  T)
  (f_can : cancel f f') : isPOrdered disp (can_type f_can) :=
  CanPartial disp (f_can : @cancel _ (can_type f_can)  f f').

Section CancelTotal.
Variables (disp : unit) (T : choiceType).
Variables (disp' : unit) (T' : orderType disp') (f : T -> T').

Section PCan.

Variables (f' : T' -> option T) (f_can : pcancel f f').

#[local]
HB.instance Definition _ :=
   MonoTotal.Build disp (pcan_type f_can) (fun _ _ => erefl).

Definition PcanTotal : DistrLattice_isTotal _ (pcan_type f_can) :=
  Total.on (pcan_type f_can).

End PCan.

Section Can.

Variables (f' : T' -> T) (f_can : cancel f f').

#[local]
HB.instance Definition _ :=
   MonoTotal.Build disp (can_type f_can) (fun _ _ => erefl).

Definition CanTotal : DistrLattice_isTotal _ (can_type f_can) :=
  Total.on (can_type f_can).

End Can.
End CancelTotal.

HB.factory Record IsoLattice disp T of POrder disp T := {
  disp' : unit;
  T' : latticeType disp';
  f : T -> T';
  f' : T' -> T;
  f_can : cancel f f';
  f'_can : cancel f' f;
  f_mono : {mono f : x y / x <= y};
}.

HB.builders Context disp T of IsoLattice disp T.

Definition meet (x y : T) := f' (meet (f x) (f y)).
Definition join (x y : T) := f' (join (f x) (f y)).

Lemma meetC : commutative meet. Proof. by move=> x y; rewrite /meet meetC. Qed.
Lemma joinC : commutative join. Proof. by move=> x y; rewrite /join joinC. Qed.
Lemma meetA : associative meet.
Proof. by move=> y x z; rewrite /meet !f'_can meetA. Qed.
Lemma joinA : associative join.
Proof. by move=> y x z; rewrite /join !f'_can joinA. Qed.
Lemma joinKI y x : meet x (join x y) = x.
Proof. by rewrite /meet /join f'_can joinKI f_can. Qed.
Lemma meetKI y x : join x (meet x y) = x.
Proof. by rewrite /join /meet f'_can meetKU f_can. Qed.
Lemma meet_eql x y : (x <= y) = (meet x y == x).
Proof. by rewrite /meet -(can_eq f_can) f'_can eq_meetl f_mono. Qed.

HB.instance Definition _ := POrder_isLattice.Build _ T
  meetC joinC meetA joinA joinKI meetKI meet_eql.

HB.end.

HB.factory Record IsoDistrLattice disp T of POrder disp T := {
  disp' : unit;
  T' : distrLatticeType disp';
  f : T -> T';
  f' : T' -> T;
  f_can : cancel f f';
  f'_can : cancel f' f;
  f_mono : {mono f : x y / x <= y};
}.

HB.builders Context disp T of IsoDistrLattice disp T.

HB.instance Definition _ := IsoLattice.Build _ T f_can f'_can f_mono.

Lemma meetUl : left_distributive (meet : T -> T -> T) join.
Proof. by move=> x y z; rewrite /meet /join /= !f'_can meetUl. Qed.

HB.instance Definition _ := Lattice_MeetIsDistributive.Build _ T meetUl.

HB.end.

Module CanExports.
#[deprecated(since="mathcomp 2.0.0", note="use Order.MonoTotal instead.")]
Notation MonoTotalMixin d T := (MonoTotal d T).
#[deprecated(since="mathcomp 2.0.0", note="use Order.PcanPartial instead.")]
Notation PcanPOrderMixin := PcanPartial.
#[deprecated(since="mathcomp 2.0.0", note="use Order.CanPartial instead.")]
Notation CanPOrderMixin := CanPartial.
#[deprecated(since="mathcomp 2.0.0", note="use Order.PcanTotal instead.")]
Notation PcanOrderMixin := PcanTotal.
#[deprecated(since="mathcomp 2.0.0", note="use Order.CanTotal instead.")]
Notation CanOrderMixin := CanTotal.
#[deprecated(since="mathcomp 2.0.0", note="use Order.IsoLattice instead.")]
Notation IsoLatticeMixin d T := (IsoLattice d T).
#[deprecated(since="mathcomp 2.0.0", note="use Order.IsoDistrLattice instead.")]
Notation IsoDistrLatticeMixin d T := (IsoDistrLattice d T).
End CanExports.
Export CanExports.

Module SubOrder.

Section Partial.
Context {disp : unit} {T : porderType disp} (P : {pred T}) (sT : subType P).

#[export]
HB.instance Definition _ : isPOrdered disp (sub_type sT) :=
  PcanPartial disp (valK : @pcancel _ (sub_type sT) val insub).

Lemma leEsub (x y : sub_type sT) : (x <= y) = (val x <= val y).
Proof. by []. Qed.
Lemma ltEsub (x y : sub_type sT) : (x < y) = (val x < val y).
Proof. by []. Qed.

End Partial.

Section Total.
Context {disp : unit} {T : orderType disp} (P : {pred T}) (sT : subType P).

#[export]
HB.instance Definition _ :=
  MonoTotal.Build _ (sub_type sT) (fun _ _ => erefl).

End Total.

Module Exports.
HB.reexport SubOrder.
Notation "[ 'POrder' 'of' T 'by' <: ]" :=
  (POrder.copy T%type (sub_type T))
  (at level 0, format "[ 'POrder'  'of'  T  'by'  <: ]") : form_scope.

Notation "[ 'IsPOrdered' 'of' T 'by' <: ]" :=
  (fun d => (PcanPartial d (valK : @pcancel (_ : porderType d)
                                                    T%type val insub) :
   (isPOrdered d T%type)) _)
  (at level 0, format "[ 'IsPOrdered'  'of'  T  'by'  <: ]") : form_scope.

Notation "[ 'IsTotal' 'of' T 'by' <: ]" :=
  (MonoTotal.Build _ T (fun _ _ => erefl))
  (at level 0, only parsing) : form_scope.

Notation "[ 'Order' 'of' T 'by' <: ]" :=
  (Total.copy T%type (sub_type T))
  (at level 0, only parsing) : form_scope.

Definition leEsub := @leEsub.
Definition ltEsub := @ltEsub.
End Exports.
End SubOrder.
HB.export SubOrder.Exports.

(*************)
(* INSTANCES *)
(*************)

(*******************************)
(* Canonical structures on nat *)
(*******************************)

(******************************************************************************)
(* This is an example of creation of multiple canonical declarations on the   *)
(* same type, with distinct displays, on the example of natural numbers.      *)
(* We declare two distinct canonical orders:                                  *)
(* - leq which is total, and where meet and join are minn and maxn, on nat    *)
(* - dvdn which is partial, and where meet and join are gcdn and lcmn,        *)
(*   on a "copy" of nat we name natdiv                                        *)
(******************************************************************************)

(******************************************************************************)
(* The Module NatOrder defines leq as the canonical order on the type nat,    *)
(* i.e. without creating a "copy". We define and use nat_display and proceed  *)
(* like standard canonical structure declaration, except we use this display. *)
(* We also use a single factory LeOrderMixin to instantiate three different   *)
(* canonical declarations porderType, distrLatticeType, orderType             *)
(* We finish by providing theorems to convert the operations of ordered and   *)
(* lattice types to their definition without structure abstraction.           *)
(******************************************************************************)

Module NatOrder.
Section NatOrder.

Lemma nat_display : unit. Proof. exact: tt. Qed.

Lemma ltn_def x y : (x < y)%N = (y != x) && (x <= y)%N.
Proof. by rewrite ltn_neqAle eq_sym. Qed.

#[export]
HB.instance Definition _ :=
  isOrdered.Build nat_display nat ltn_def (fun _ _ => erefl) (fun _ _ => erefl)
                  anti_leq leq_trans leq_total.

#[export]
HB.instance Definition _ := hasBottom.Build nat_display nat leq0n.

Lemma leEnat : le = leq. Proof. by []. Qed.
Lemma ltEnat : lt = ltn. Proof. by []. Qed.
Lemma minEnat : min = minn. Proof. by []. Qed.
Lemma maxEnat : max = maxn. Proof. by []. Qed.
Lemma botEnat : 0%O = 0%N :> nat. Proof. by []. Qed.

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

Context {disp : unit} {T : porderType disp}.
Variables (D : {pred nat}) (f : nat -> T).
Hypothesis Dconvex : {in D &, forall i j k, i < k < j -> k \in D}.

Lemma homo_ltn_lt_in : {in D, forall i, i.+1 \in D -> f i < f i.+1} ->
  {in D &, {homo f : i j / i < j}}.
Proof. by apply: homo_ltn_in Dconvex; apply: lt_trans. Qed.

Lemma incn_inP : {in D, forall i, i.+1 \in D -> f i < f i.+1} ->
  {in D &, {mono f : i j / i <= j}}.
Proof. by move=> f_inc; apply/le_mono_in/homo_ltn_lt_in. Qed.

Lemma nondecn_inP : {in D, forall i, i.+1 \in D -> f i <= f i.+1} ->
  {in D &, {homo f : i j / i <= j}}.
Proof. by apply: homo_leq_in Dconvex => //; apply: le_trans. Qed.

Lemma nhomo_ltn_lt_in : {in D, forall i, i.+1 \in D -> f i > f i.+1} ->
  {in D &, {homo f : i j /~ i < j}}.
Proof.
move=> f_dec; apply: homo_sym_in.
by apply: homo_ltn_in Dconvex f_dec => ? ? ? ? /lt_trans->.
Qed.

Lemma decn_inP : {in D, forall i, i.+1 \in D -> f i > f i.+1} ->
  {in D &, {mono f : i j /~ i <= j}}.
Proof. by move=> f_dec; apply/le_nmono_in/nhomo_ltn_lt_in. Qed.

Lemma nonincn_inP : {in D, forall i, i.+1 \in D -> f i >= f i.+1} ->
  {in D &, {homo f : i j /~ i <= j}}.
Proof.
move=> /= f_dec; apply: homo_sym_in.
by apply: homo_leq_in Dconvex f_dec => //= ? ? ? ? /le_trans->.
Qed.

Lemma homo_ltn_lt : (forall i, f i < f i.+1) -> {homo f : i j / i < j}.
Proof. by apply: homo_ltn; apply: lt_trans. Qed.

Lemma incnP : (forall i, f i < f i.+1) -> {mono f : i j / i <= j}.
Proof. by move=> f_inc; apply/le_mono/homo_ltn_lt. Qed.

Lemma nondecnP : (forall i, f i <= f i.+1) -> {homo f : i j / i <= j}.
Proof. by apply: homo_leq => //; apply: le_trans. Qed.

Lemma nhomo_ltn_lt : (forall i, f i > f i.+1) -> {homo f : i j /~ i < j}.
Proof.
move=> f_dec; apply: homo_sym.
by apply: homo_ltn f_dec => ? ? ? ? /lt_trans->.
Qed.

Lemma decnP : (forall i, f i > f i.+1) -> {mono f : i j /~ i <= j}.
Proof. by move=> f_dec; apply/le_nmono/nhomo_ltn_lt. Qed.

Lemma nonincnP : (forall i, f i >= f i.+1) -> {homo f : i j /~ i <= j}.
Proof.
move=> /= f_dec; apply: homo_sym.
by apply: homo_leq f_dec => //= ? ? ? ? /le_trans->.
Qed.

End NatMonotonyTheory.
Arguments homo_ltn_lt_in {disp T} [D f].
Arguments incn_inP {disp T} [D f].
Arguments nondecn_inP {disp T} [D f].
Arguments nhomo_ltn_lt_in {disp T} [D f].
Arguments decn_inP {disp T} [D f].
Arguments nonincn_inP {disp T} [D f].
Arguments homo_ltn_lt {disp T} [f].
Arguments incnP {disp T} [f].
Arguments nondecnP {disp T} [f].
Arguments nhomo_ltn_lt {disp T} [f].
Arguments decnP {disp T} [f].
Arguments nonincnP {disp T} [f].

End NatMonotonyTheory.

(****************************************************************************)
(* The Module DvdSyntax introduces a new set of notations using the newly   *)
(* created display dvd_display. We first define the display as an opaque    *)
(* definition of type unit, and we use it as the first argument of the      *)
(* operator which display we want to change from the default one (here le,  *)
(* lt, dvd sdvd, meet, join, top and bottom, as well as big op notations on *)
(* gcd and lcm). This notations will now be used for any ordered type which *)
(* first parameter is set to dvd_display.                                   *)
(****************************************************************************)

Lemma dvd_display : unit. Proof. exact: tt. Qed.

Module DvdSyntax.

Notation dvd := (@le dvd_display _).
Notation "@ 'dvd' T" :=
  (@le dvd_display T) (at level 10, T at level 8, only parsing) : fun_scope.
Notation sdvd := (@lt dvd_display _).
Notation "@ 'sdvd' T" :=
  (@lt dvd_display T) (at level 10, T at level 8, only parsing) : fun_scope.

Notation "x %| y" := (dvd x y) : order_scope.
Notation "x %<| y" := (sdvd x y) : order_scope.

Notation gcd := (@meet dvd_display _).
Notation "@ 'gcd' T" :=
  (@meet dvd_display T) (at level 10, T at level 8, only parsing) : fun_scope.
Notation lcm := (@join dvd_display _).
Notation "@ 'lcm' T" :=
  (@join dvd_display T) (at level 10, T at level 8, only parsing) : fun_scope.

Notation nat0 := (@top dvd_display _).
Notation nat1 := (@bottom dvd_display _).

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
(* We use the newly defined dvd_display, described above. This looks          *)
(* like standard canonical structure declaration, except we use a display and *)
(* we declare it on a "copy" of the type.                                     *)
(* We first recover structures that are common to both nat and natdiv         *)
(* (eqType, choiceType, countType) through the clone mechanisms, then we use  *)
(* a single factory MeetJoinMixin to instantiate both porderType and          *)
(* distrLatticeType canonical structures, and end with top and bottom.        *)
(* We finish by providing theorems to convert the operations of ordered and   *)
(* lattice types to their definition without structure abstraction.           *)
(******************************************************************************)

Module NatDvd.
Section NatDvd.

Implicit Types m n p : nat.

Lemma lcmnn n : lcmn n n = n.
Proof. by case: n => // n; rewrite /lcmn gcdnn mulnK. Qed.

Lemma le_def m n : m %| n = (gcdn m n == m)%N.
Proof. by apply/gcdn_idPl/eqP. Qed.

Lemma joinKI n m : gcdn m (lcmn m n) = m.
Proof. by rewrite (gcdn_idPl _)// dvdn_lcml. Qed.

Lemma meetKU n m : lcmn m (gcdn m n) = m.
Proof. by rewrite (lcmn_idPl _)// dvdn_gcdl. Qed.

Lemma meetUl : left_distributive gcdn lcmn.
Proof.
move=> [|m'] [|n'] [|p'] //=; rewrite ?lcmnn ?lcm0n ?lcmn0 ?gcd0n ?gcdn0//.
- by rewrite gcdnC meetKU.
- by rewrite lcmnC gcdnC meetKU.
apply: eqn_from_log; rewrite ?(gcdn_gt0, lcmn_gt0)//= => p.
by rewrite !(logn_gcd, logn_lcm) ?(gcdn_gt0, lcmn_gt0)// minn_maxl.
Qed.

Definition t := nat.

#[export]
HB.instance Definition _ := Choice.copy t nat.

#[export]
HB.instance Definition _ := isMeetJoinDistrLattice.Build
  dvd_display t le_def (fun _ _ => erefl)
  gcdnC lcmnC gcdnA lcmnA joinKI meetKU meetUl gcdnn.

#[export]
HB.instance Definition _ := hasBottom.Build _ t (dvd1n : forall m : t, (1 %| m)).

#[export]
HB.instance Definition _ := hasTop.Build _ t (dvdn0 : forall m : t, (m %| 0)).

Import DvdSyntax.
Lemma dvdE : dvd = dvdn :> rel t. Proof. by []. Qed.
Lemma sdvdE (m n : t) : m %<| n = (n != m) && (m %| n). Proof. by []. Qed.
Lemma gcdE : gcd = gcdn :> (t -> t -> t). Proof. by []. Qed.
Lemma lcmE : lcm = lcmn :> (t -> t -> t). Proof. by []. Qed.
Lemma nat1E : nat1 = 1%N :> t. Proof. by []. Qed.
Lemma nat0E : nat0 = 0%N :> t. Proof. by []. Qed.

End NatDvd.
Module Exports.
HB.reexport NatDvd.
Notation natdvd := t.
Definition dvdEnat := dvdE.
Definition sdvdEnat := sdvdE.
Definition gcdEnat := gcdE.
Definition lcmEnat := lcmE.
Definition nat1E := nat1E.
Definition nat0E := nat0E.
End Exports.
End NatDvd.
HB.export NatDvd.Exports.

(***********************************)
(* Canonical structures on ordinal *)
(***********************************)

Module OrdinalOrder.
Section OrdinalOrder.

Lemma ord_display : unit. Proof. exact: tt. Qed.

Section PossiblyTrivial.
Variable (n : nat).

#[export]
HB.instance Definition _ := [Order of 'I_n by <:].

Lemma leEord : (le : rel 'I_n) = leq. Proof. by []. Qed.
Lemma ltEord : (lt : rel 'I_n) = (fun m n => m < n)%N. Proof. by []. Qed.
End PossiblyTrivial.

Section NonTrivial.
Variable (n' : nat).
Let n := n'.+1.

#[export]
HB.instance Definition _ :=
   hasBottom.Build _ 'I_n (leq0n : forall x, ord0 <= x).
#[export]
HB.instance Definition _ :=
   hasTop.Build _ 'I_n (@leq_ord _ : forall x, x <= ord_max).

Lemma botEord : 0%O = ord0. Proof. by []. Qed.
Lemma topEord : 1%O = ord_max. Proof. by []. Qed.

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

(*******************************)
(* Canonical structure on bool *)
(*******************************)

Module BoolOrder.
Section BoolOrder.
Implicit Types (x y : bool).

Fact bool_display : unit. Proof. exact: tt. Qed.

Fact andbE x y : x && y = if (x < y)%N then x else y.
Proof. by case: x y => [] []. Qed.

Fact orbE x y : x || y = if (x < y)%N then y else x.
Proof. by case: x y => [] []. Qed.

Fact ltn_def x y : (x < y)%N = (y != x) && (x <= y)%N.
Proof. by case: x y => [] []. Qed.

Fact anti : antisymmetric (leq : rel bool).
Proof. by move=> x y /anti_leq /(congr1 odd); rewrite !oddb. Qed.

Definition sub x y := x && ~~ y.

Lemma subKI x y : y && sub x y = false. Proof. by case: x y => [] []. Qed.
Lemma joinIB x y : (x && y) || sub x y = x. Proof. by case: x y => [] []. Qed.

#[export] HB.instance Definition _ := @isOrdered.Build bool_display bool
   _ _ andb orb ltn_def andbE orbE anti leq_trans leq_total.
#[export] HB.instance Definition _ := @hasBottom.Build _ bool false leq0n.
#[export] HB.instance Definition _ := @hasTop.Build _ bool true leq_b1.
#[export] HB.instance Definition _ := @hasSub.Build _ bool sub subKI joinIB.
#[export] HB.instance Definition _ := @hasCompl.Build _ bool
  negb (fun x => erefl : ~~ x = sub true x).

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

(*******************************)
(* Definition of prod_display. *)
(*******************************)

Fact prod_display : unit. Proof. by []. Qed.

Module Import ProdSyntax.

Notation "<=^p%O" := (@le prod_display _) : fun_scope.
Notation ">=^p%O" := (@ge prod_display _)  : fun_scope.
Notation ">=^p%O" := (@ge prod_display _)  : fun_scope.
Notation "<^p%O" := (@lt prod_display _) : fun_scope.
Notation ">^p%O" := (@gt prod_display _) : fun_scope.
Notation "<?=^p%O" := (@leif prod_display _) : fun_scope.
Notation ">=<^p%O" := (@comparable prod_display _) : fun_scope.
Notation "><^p%O" := (fun x y => ~~ (@comparable prod_display _ x y)) :
  fun_scope.

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
Local Notation "0" := (@bottom prod_display _).
Local Notation "1" := (@top prod_display _).
Local Notation meet := (@meet prod_display _).
Local Notation join := (@join prod_display _).

Notation "x `&^p` y" :=  (meet x y) : order_scope.
Notation "x `|^p` y" := (join x y) : order_scope.

Notation "\join^p_ ( i <- r | P ) F" :=
  (\big[join/0]_(i <- r | P%B) F%O) : order_scope.
Notation "\join^p_ ( i <- r ) F" :=
  (\big[join/0]_(i <- r) F%O) : order_scope.
Notation "\join^p_ ( i | P ) F" :=
  (\big[join/0]_(i | P%B) F%O) : order_scope.
Notation "\join^p_ i F" :=
  (\big[join/0]_i F%O) : order_scope.
Notation "\join^p_ ( i : I | P ) F" :=
  (\big[join/0]_(i : I | P%B) F%O) (only parsing) : order_scope.
Notation "\join^p_ ( i : I ) F" :=
  (\big[join/0]_(i : I) F%O) (only parsing) : order_scope.
Notation "\join^p_ ( m <= i < n | P ) F" :=
 (\big[join/0]_(m <= i < n | P%B) F%O) : order_scope.
Notation "\join^p_ ( m <= i < n ) F" :=
 (\big[join/0]_(m <= i < n) F%O) : order_scope.
Notation "\join^p_ ( i < n | P ) F" :=
 (\big[join/0]_(i < n | P%B) F%O) : order_scope.
Notation "\join^p_ ( i < n ) F" :=
 (\big[join/0]_(i < n) F%O) : order_scope.
Notation "\join^p_ ( i 'in' A | P ) F" :=
 (\big[join/0]_(i in A | P%B) F%O) : order_scope.
Notation "\join^p_ ( i 'in' A ) F" :=
 (\big[join/0]_(i in A) F%O) : order_scope.

Notation "\meet^p_ ( i <- r | P ) F" :=
  (\big[meet/1]_(i <- r | P%B) F%O) : order_scope.
Notation "\meet^p_ ( i <- r ) F" :=
  (\big[meet/1]_(i <- r) F%O) : order_scope.
Notation "\meet^p_ ( i | P ) F" :=
  (\big[meet/1]_(i | P%B) F%O) : order_scope.
Notation "\meet^p_ i F" :=
  (\big[meet/1]_i F%O) : order_scope.
Notation "\meet^p_ ( i : I | P ) F" :=
  (\big[meet/1]_(i : I | P%B) F%O) (only parsing) : order_scope.
Notation "\meet^p_ ( i : I ) F" :=
  (\big[meet/1]_(i : I) F%O) (only parsing) : order_scope.
Notation "\meet^p_ ( m <= i < n | P ) F" :=
 (\big[meet/1]_(m <= i < n | P%B) F%O) : order_scope.
Notation "\meet^p_ ( m <= i < n ) F" :=
 (\big[meet/1]_(m <= i < n) F%O) : order_scope.
Notation "\meet^p_ ( i < n | P ) F" :=
 (\big[meet/1]_(i < n | P%B) F%O) : order_scope.
Notation "\meet^p_ ( i < n ) F" :=
 (\big[meet/1]_(i < n) F%O) : order_scope.
Notation "\meet^p_ ( i 'in' A | P ) F" :=
 (\big[meet/1]_(i in A | P%B) F%O) : order_scope.
Notation "\meet^p_ ( i 'in' A ) F" :=
 (\big[meet/1]_(i in A) F%O) : order_scope.

End ProdSyntax.

(*******************************)
(* Definition of lexi_display. *)
(*******************************)

Fact lexi_display : unit. Proof. by []. Qed.

Module Import LexiSyntax.

Notation "<=^l%O" := (@le lexi_display _) : fun_scope.
Notation ">=^l%O" := (@ge lexi_display _) : fun_scope.
Notation ">=^l%O" := (@ge lexi_display _) : fun_scope.
Notation "<^l%O" := (@lt lexi_display _) : fun_scope.
Notation ">^l%O" := (@gt lexi_display _) : fun_scope.
Notation "<?=^l%O" := (@leif lexi_display _) : fun_scope.
Notation ">=<^l%O" := (@comparable lexi_display _) : fun_scope.
Notation "><^l%O" := (fun x y => ~~ (@comparable lexi_display _ x y)) :
  fun_scope.

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

Notation meetlexi := (@meet lexi_display _).
Notation joinlexi := (@join lexi_display _).

Notation "x `&^l` y" :=  (meetlexi x y) : order_scope.
Notation "x `|^l` y" := (joinlexi x y) : order_scope.

End LexiSyntax.

(*************************************************)
(* We declare a "copy" of the cartesian product, *)
(* which has canonical product order.            *)
(*************************************************)

Module ProdOrder.
Section ProdOrder.

Local Open Scope type_scope. (* FIXME *)

Definition type (disp : unit) (T T' : Type) := T * T'.

Context {disp1 disp2 disp3 : unit}.

Local Notation "T * T'" := (type disp3 T T') : type_scope.

#[export] HB.instance Definition _ (T T' : eqType) := Equality.on (T * T').
#[export] HB.instance Definition _ (T T' : choiceType) := Choice.on (T * T').
#[export] HB.instance Definition _ (T T' : countType) := Countable.on (T * T').
#[export] HB.instance Definition _ (T T' : finType) := Finite.on (T * T').

Section POrder.
Variable (T : porderType disp1) (T' : porderType disp2).

Implicit Types (x y : T * T').

Definition le x y := (x.1 <= y.1) && (x.2 <= y.2).

Fact refl : reflexive le. Proof. by move=> ?; rewrite /le !lexx. Qed.

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

#[export]
HB.instance Definition _ :=
  isPOrdered.Build disp3 (T * T') (rrefl _) refl anti trans.

Lemma leEprod x y : (x <= y) = (x.1 <= y.1) && (x.2 <= y.2). Proof. by []. Qed.

Lemma ltEprod x y : (x < y) = [&& x != y, x.1 <= y.1 & x.2 <= y.2].
Proof. by rewrite lt_neqAle. Qed.

Lemma le_pair (x1 y1 : T) (x2 y2 : T') :
  (x1, x2) <= (y1, y2) :> T * T' = (x1 <= y1) && (x2 <= y2).
Proof. by []. Qed.

Lemma lt_pair (x1 y1 : T) (x2 y2 : T') : (x1, x2) < (y1, y2) :> T * T' =
  [&& (x1 != y1) || (x2 != y2), x1 <= y1 & x2 <= y2].
Proof. by rewrite ltEprod negb_and. Qed.

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
Proof. by rewrite eqE /= -!leEmeet. Qed.

#[export]
HB.instance Definition _ := POrder_isLattice.Build
  _ (T * T') meetC joinC meetA joinA joinKI meetKU leEmeet.

Lemma meetEprod x y : x `&` y = (x.1 `&` y.1, x.2 `&` y.2). Proof. by []. Qed.

Lemma joinEprod x y : x `|` y = (x.1 `|` y.1, x.2 `|` y.2). Proof. by []. Qed.

End Lattice.

Section BLattice.
Variable (T : bLatticeType disp1) (T' : bLatticeType disp2).

Fact le0x (x : T * T') : (0, 0) <= x :> T * T'.
Proof. by rewrite /<=%O /= /le !le0x. Qed.

#[export]
HB.instance Definition _ := hasBottom.Build _ (T * T') le0x.

Lemma botEprod : 0 = (0, 0) :> T * T'. Proof. by []. Qed.

End BLattice.

Section TBLattice.
Variable (T : tbLatticeType disp1) (T' : tbLatticeType disp2).

Fact lex1 (x : T * T') : x <= (top, top).
Proof. by rewrite /<=%O /= /le !lex1. Qed.

#[export]
HB.instance Definition _ := hasTop.Build _ (T * T') lex1.

Lemma topEprod : 1 = (1, 1) :> T * T'. Proof. by []. Qed.

End TBLattice.

Section DistrLattice.
Variable (T : distrLatticeType disp1) (T' : distrLatticeType disp2).

Fact meetUl : left_distributive (@meet T T') (@join T T').
Proof. by move=> ? ? ?; congr pair; rewrite meetUl. Qed.

#[export]
HB.instance Definition _ := Lattice_MeetIsDistributive.Build _ (T * T') meetUl.

End DistrLattice.

(* FIXME: the canonical (t)bDistrLatticeType instances of products should be  *)
(*        automatically generated. *)
#[export]
HB.instance Definition _
  (T : bDistrLatticeType disp1) (T' : bDistrLatticeType disp2) :=
  DistrLattice.on (T * T').

#[export]
HB.instance Definition _
  (T : tbDistrLatticeType disp1) (T' : tbDistrLatticeType disp2) :=
  DistrLattice.on (T * T').
(* /FIXME *)

Section CBDistrLattice.
Variable (T : cbDistrLatticeType disp1) (T' : cbDistrLatticeType disp2).
Implicit Types (x y : T * T').

Definition sub x y := (x.1 `\` y.1, x.2 `\` y.2).

Lemma subKI x y : y `&` sub x y = 0. Proof. by congr pair; rewrite subKI. Qed.

Lemma joinIB x y : x `&` y `|` sub x y = x.
Proof. by case: x => ? ?; congr pair; rewrite joinIB. Qed.

#[export]
HB.instance Definition _ := hasSub.Build _ (T * T') subKI joinIB.

Lemma subEprod x y : x `\` y = (x.1 `\` y.1, x.2 `\` y.2). Proof. by []. Qed.

End CBDistrLattice.

Section CTBDistrLattice.
Variable (T : ctbDistrLatticeType disp1) (T' : ctbDistrLatticeType disp2).
Implicit Types (x y : T * T').

Definition compl x : T * T' := (~` x.1, ~` x.2).

Lemma complE x : compl x = sub 1 x. Proof. by congr pair; rewrite complE. Qed.

#[export]
HB.instance Definition _ := hasCompl.Build _ (T * T') complE.

Lemma complEprod x : ~` x = (~` x.1, ~` x.2). Proof. by []. Qed.

End CTBDistrLattice.

(* FIXME *)
#[export]
HB.instance Definition _ (T : finPOrderType disp1)
  (T' : finPOrderType disp2) := POrder.on (T * T').
#[export]
HB.instance Definition _ (T : finLatticeType disp1)
  (T' : finLatticeType disp2) := Lattice.on (T * T').
#[export]
HB.instance Definition _ (T : finDistrLatticeType disp1)
  (T' : finDistrLatticeType disp2) := DistrLattice.on (T * T').
#[export]
HB.instance Definition _ (T : finCDistrLatticeType disp1)
  (T' : finCDistrLatticeType disp2) := CTBDistrLattice.on (T * T').
(* /FIXME *)

End ProdOrder.

Module Exports.
HB.reexport ProdOrder.
Notation "T *prod[ d ] T'" := (type d T T')
  (at level 70, d at next level, format "T  *prod[ d ]  T'") : type_scope.
Notation "T *p T'" := (type prod_display T T')
  (at level 70, format "T  *p  T'") : type_scope.
Definition leEprod := @leEprod.
Definition ltEprod := @ltEprod.
Definition le_pair := @le_pair.
Definition lt_pair := @lt_pair.
Definition meetEprod := @meetEprod.
Definition joinEprod := @joinEprod.
Definition botEprod := @botEprod.
Definition topEprod := @topEprod.
Definition subEprod := @subEprod.
Definition complEprod := @complEprod.
End Exports.
End ProdOrder.
HB.export ProdOrder.Exports.

Module DefaultProdOrder.
Section DefaultProdOrder.
Context {disp1 disp2 : unit}.

(* FIXME: Scopes of arguments are broken in several places.                   *)
(* FIXME: Declaring a bunch of copies is still a bit painful.                 *)
HB.instance Definition _ (T : porderType disp1) (T' : porderType disp2) :=
  POrder.copy (T * T')%type (T *p T').
HB.instance Definition _ (T : latticeType disp1) (T' : latticeType disp2) :=
  Lattice.copy (T * T')%type (T *p T').
HB.instance Definition _ (T : bLatticeType disp1) (T' : bLatticeType disp2) :=
  BLattice.copy (T * T')%type (T *p T').
HB.instance Definition _ (T : tbLatticeType disp1) (T' : tbLatticeType disp2) :=
  TBLattice.copy (T * T')%type (T *p T').
HB.instance Definition _
    (T : distrLatticeType disp1) (T' : distrLatticeType disp2) :=
  DistrLattice.copy (T * T')%type (T *p T').
HB.instance Definition _
    (T : bDistrLatticeType disp1) (T' : bDistrLatticeType disp2) :=
  BDistrLattice.copy (T * T')%type (T *p T').
HB.instance Definition _
    (T : tbDistrLatticeType disp1) (T' : tbDistrLatticeType disp2) :=
  TBDistrLattice.copy (T * T')%type (T *p T').
HB.instance Definition _
    (T : cbDistrLatticeType disp1) (T' : cbDistrLatticeType disp2) :=
  CBDistrLattice.copy (T * T')%type (T *p T').
HB.instance Definition _
    (T : ctbDistrLatticeType disp1) (T' : ctbDistrLatticeType disp2) :=
  CTBDistrLattice.copy (T * T')%type (T *p T').
HB.instance Definition _ (T : finPOrderType disp1) (T' : finPOrderType disp2) :=
  FinPOrder.copy (T * T')%type (T *p T').
HB.instance Definition _
    (T : finLatticeType disp1) (T' : finLatticeType disp2) :=
  FinLattice.copy (T * T')%type (T *p T').
HB.instance Definition _
    (T : finDistrLatticeType disp1) (T' : finDistrLatticeType disp2) :=
  FinDistrLattice.copy (T * T')%type (T *p T').
HB.instance Definition _
    (T : finCDistrLatticeType disp1) (T' : finCDistrLatticeType disp2) :=
  FinCDistrLattice.copy (T * T')%type (T *p T').

End DefaultProdOrder.
End DefaultProdOrder.

(********************************************************)
(* We declare lexicographic ordering on dependent pairs *)
(********************************************************)

Module SigmaOrder.
Section SigmaOrder.

Context {disp1 disp2 : unit}.

Section POrder.

Variable (T : porderType disp1) (T' : T -> porderType disp2).
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

Fact lt_def x y : lt x y = (y != x) && le x y.
Proof.
rewrite /lt /le; case: x y => [x x'] [y y']//=; rewrite andbCA.
case: (comparableP x y) => //= xy; last first.
  by case: _ / xy in y' *; rewrite !tagged_asE eq_Tagged/= lt_def.
by rewrite andbT; symmetry; apply: contraTneq xy => -[yx _]; rewrite yx ltxx.
Qed.

#[export]
HB.instance Definition _ :=
  isPOrdered.Build disp2 {t : T & T' t} lt_def refl anti trans.

Lemma leEsig x y : x <= y =
  (tag x <= tag y) && ((tag x >= tag y) ==> (tagged x <= tagged_as x y)).
Proof. by []. Qed.

Lemma ltEsig x y : x < y =
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

(* FIXME *)
#[export]
HB.instance Definition _ (T : finPOrderType disp1)
  (T' : T -> finPOrderType disp2) := POrder.on {t : T & T' t}.
(* /FIXME *)

Section Total.
Variable (T : orderType disp1) (T' : T -> orderType disp2).
Implicit Types (x y : {t : T & T' t}).

Fact total : total (<=%O : rel {t : T & T' t}).
move=> x y; rewrite !leEsig; case: (ltgtP (tag x) (tag y)) => //=.
case: x y => [x x'] [y y']/= eqxy; elim: _ /eqxy in y' *.
by rewrite !tagged_asE le_total.
Qed.

#[export]
HB.instance Definition _ := POrder_isTotal.Build _ {t : T & T' t} total.

End Total.

Section FinDistrLattice.
Variable (T : finOrderType disp1) (T' : T -> finOrderType disp2).

Fact le0x (x : {t : T & T' t}) : Tagged T' (0 : T' 0) <= x.
Proof.
rewrite leEsig /=; case: comparableP (le0x (tag x)) => //=.
by case: x => //= x px x0; rewrite x0 in px *; rewrite tagged_asE le0x.
Qed.
#[export]
HB.instance Definition _ := hasBottom.Build _ {t : T & T' t} le0x.

Lemma botEsig : 0 = Tagged T' (0 : T' 0). Proof. by []. Qed.

Fact lex1 (x : {t : T & T' t}) : x <= Tagged T' (1 : T' 1).
Proof.
rewrite leEsig /=; case: comparableP (lex1 (tag x)) => //=.
by case: x => //= x px x0; rewrite x0 in px *; rewrite tagged_asE lex1.
Qed.
#[export]
HB.instance Definition _ := hasTop.Build _ {t : T & T' t} lex1.

Lemma topEsig : 1 = Tagged T' (1 : T' 1). Proof. by []. Qed.

End FinDistrLattice.

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
(* We declare a "copy" of the cartesian product, *)
(* which has canonical lexicographic order.      *)
(*************************************************)

Module ProdLexiOrder.
Section ProdLexiOrder.

Local Open Scope type_scope. (* FIXME *)

Definition type (disp : unit) (T T' : Type) := T * T'.

Context {disp1 disp2 disp3 : unit}.

Local Notation "T * T'" := (type disp3 T T') : type_scope.

#[export] HB.instance Definition _ (T T' : eqType) := Equality.on (T * T').
#[export] HB.instance Definition _ (T T' : choiceType) := Choice.on (T * T').
#[export] HB.instance Definition _ (T T' : countType) := Countable.on (T * T').
#[export] HB.instance Definition _ (T T' : finType) := Finite.on (T * T').

Section POrder.
Variable (T : porderType disp1) (T' : porderType disp2).

Implicit Types (x y : T * T').

Definition le x y := (x.1 <= y.1) && ((x.1 >= y.1) ==> (x.2 <= y.2)).
Definition lt x y := (x.1 <= y.1) && ((x.1 >= y.1) ==> (x.2 < y.2)).

Fact refl : reflexive le.
Proof. by move=> ?; rewrite /le !lexx. Qed.

Fact anti : antisymmetric le.
Proof.
by rewrite /le => -[x x'] [y y'] /=; case: comparableP => //= -> /le_anti->.
Qed.

Fact trans : transitive le.
Proof.
move=> y x z /andP [hxy /implyP hxy'] /andP [hyz /implyP hyz'].
rewrite /le (le_trans hxy) //=; apply/implyP => hzx.
by apply/le_trans/hxy'/(le_trans hyz): (hyz' (le_trans hzx hxy)).
Qed.

Fact lt_def x y : lt x y = (y != x) && le x y.
Proof.
rewrite /lt /le; case: x y => [x1 x2] [y1 y2]//=; rewrite xpair_eqE.
by case: (comparableP x1 y1); rewrite lt_def.
Qed.

#[export]
HB.instance Definition _ :=
  isPOrdered.Build disp3 (T * T') lt_def refl anti trans.

Lemma leEprodlexi x y :
  (x <= y) = (x.1 <= y.1) && ((x.1 >= y.1) ==> (x.2 <= y.2)).
Proof. by []. Qed.

Lemma ltEprodlexi x y :
  (x < y) = (x.1 <= y.1) && ((x.1 >= y.1) ==> (x.2 < y.2)).
Proof. by []. Qed.

Lemma lexi_pair (x1 y1 : T) (x2 y2 : T') :
   (x1, x2) <= (y1, y2) :> T * T' = (x1 <= y1) && ((x1 >= y1) ==> (x2 <= y2)).
Proof. by []. Qed.

Lemma ltxi_pair (x1 y1 : T) (x2 y2 : T') :
   (x1, x2) < (y1, y2) :> T * T' = (x1 <= y1) && ((x1 >= y1) ==> (x2 < y2)).
Proof. by []. Qed.

End POrder.

(* FIXME *)
#[export]
HB.instance Definition _ (T : finPOrderType disp1)
  (T' : finPOrderType disp2) := POrder.on (T * T').
(* /FIXME *)

Section Total.
Variable (T : orderType disp1) (T' : orderType disp2).
Implicit Types (x y : T * T').

Fact total : total (<=%O: rel [porderType of T * T']).
Proof.
move=> x y; rewrite /<=%O /= /le; case: ltgtP => //= _; exact: le_total.
Qed.

#[export]
HB.instance Definition _ := POrder_isTotal.Build _ (T * T') total.

End Total.

Section FinDistrLattice.
Variable (T : finOrderType disp1) (T' : finOrderType disp2).

Fact le0x (x : T * T') : (0, 0) <= x :> T * T'.
Proof. by case: x => // x1 x2; rewrite leEprodlexi/= !le0x implybT. Qed.

#[export]
HB.instance Definition _ := hasBottom.Build _ (T * T') le0x.

Lemma botEprodlexi : 0 = (0, 0) :> T * T'. Proof. by []. Qed.

Fact lex1 (x : T * T') : x <= (1, 1) :> T * T'.
Proof. by case: x => // x1 x2; rewrite leEprodlexi/= !lex1 implybT. Qed.

#[export]
HB.instance Definition _ := hasTop.Build _ (T * T') lex1.

Lemma topEprodlexi : 1 = (1, 1) :> T * T'. Proof. by []. Qed.

End FinDistrLattice.

Lemma sub_prod_lexi d (T : porderType disp1) (T' : porderType disp2) :
   subrel (<=%O : rel (T *prod[d] T')) (<=%O : rel (T * T')).
Proof.
by case=> [x1 x2] [y1 y2]; rewrite leEprod leEprodlexi /=; case: comparableP.
Qed.

End ProdLexiOrder.

Module Exports.

HB.reexport ProdLexiOrder.

Notation "T *lexi[ d ] T'" := (type d T T')
  (at level 70, d at next level, format "T  *lexi[ d ]  T'") : type_scope.
Notation "T *l T'" := (type lexi_display T T')
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
Context {disp1 disp2 : unit}.

HB.instance Definition _ (T : porderType disp1) (T' : porderType disp2) :=
  POrder.copy (T * T')%type (T *l T').
HB.instance Definition _ (T : orderType disp1) (T' : orderType disp2) :=
  Total.copy (T * T')%type (T *l T').
HB.instance Definition _ (T : finOrderType disp1) (T' : finOrderType disp2) :=
  FinTotal.copy (T * T')%type (T *l T').

End DefaultProdLexiOrder.
End DefaultProdLexiOrder.

(*****************************************)
(* We declare a "copy" of the sequences, *)
(* which has canonical product order.    *)
(*****************************************)

Module SeqProdOrder.
Section SeqProdOrder.

Definition type (disp : unit) T := seq T.

Context {disp disp' : unit}.

Local Notation seq := (type disp').

#[export] HB.instance Definition _ (T : eqType) := Equality.on (seq T).
#[export] HB.instance Definition _ (T : choiceType) := Choice.on (seq T).
#[export] HB.instance Definition _ (T : countType) := Countable.on (seq T).

Section POrder.
Variable T : porderType disp.
Implicit Types s : seq T.

Fixpoint le s1 s2 := if s1 isn't x1 :: s1' then true else
                     if s2 isn't x2 :: s2' then false else
                     (x1 <= x2) && le s1' s2'.

Fact refl : reflexive le. Proof. by elim=> //= ? ? ?; rewrite !lexx. Qed.

Fact anti : antisymmetric le.
Proof.
by elim=> [|x s ihs] [|y s'] //=; rewrite andbACA => /andP[/le_anti-> /ihs->].
Qed.

Fact trans : transitive le.
Proof.
elim=> [|y ys ihs] [|x xs] [|z zs] //= /andP[xy xys] /andP[yz yzs].
by rewrite (le_trans xy)// ihs.
Qed.

#[export]
HB.instance Definition _ := isPOrdered.Build disp' (seq T) (rrefl _) refl anti trans.

Lemma leEseq s1 s2 : s1 <= s2 = if s1 isn't x1 :: s1' then true else
                                if s2 isn't x2 :: s2' then false else
                                (x1 <= x2) && (s1' <= s2' :> seq _).
Proof. by case: s1. Qed.

Lemma le0s s : [::] <= s :> seq _. Proof. by []. Qed.

Lemma les0 s : s <= [::] = (s == [::]). Proof. by rewrite leEseq. Qed.

Lemma le_cons x1 s1 x2 s2 :
   x1 :: s1 <= x2 :: s2 :> seq _ = (x1 <= x2) && (s1 <= s2).
Proof. by []. Qed.

End POrder.

Section Lattice.
Variable T : latticeType disp.
Implicit Types s : seq T.

Fixpoint meet s1 s2 :=
  match s1, s2 with
    | x1 :: s1', x2 :: s2' => (x1 `&` x2) :: meet s1' s2'
    | _, _ => [::]
  end.

Fixpoint join s1 s2 :=
  match s1, s2 with
    | [::], _ => s2 | _, [::] => s1
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
by rewrite /<=%O /=; elim: x y => [|? ? ih] [|? ?] //=; rewrite eqE leEmeet ih.
Qed.

#[export]
HB.instance Definition _ :=
  POrder_isLattice.Build _ (seq T) meetC joinC meetA joinA joinKI meetKU leEmeet.

Lemma meetEseq s1 s2 : s1 `&` s2 =  [seq x.1 `&` x.2 | x <- zip s1 s2].
Proof. by elim: s1 s2 => [|x s1 ihs1] [|y s2]//=; rewrite -ihs1. Qed.

Lemma meet_cons x1 s1 x2 s2 :
  (x1 :: s1 : seq T) `&` (x2 :: s2) = (x1 `&` x2) :: s1 `&` s2.
Proof. by []. Qed.

Lemma joinEseq s1 s2 : s1 `|` s2 =
  match s1, s2 with
    | [::], _ => s2 | _, [::] => s1
    | x1 :: s1', x2 :: s2' => (x1 `|` x2) :: ((s1' : seq _) `|` s2')
  end.
Proof. by case: s1. Qed.

Lemma join_cons x1 s1 x2 s2 :
  (x1 :: s1 : seq T) `|` (x2 :: s2) = (x1 `|` x2) :: s1 `|` s2.
Proof. by []. Qed.

#[export]
HB.instance Definition _ := hasBottom.Build _ (seq T) (@le0s _).

Lemma botEseq : 0 = [::] :> seq T.
Proof. by []. Qed.

End Lattice.

Section DistrLattice.
Variable T : distrLatticeType disp.

Fact meetUl : left_distributive (@meet T) (@join T).
Proof. by elim=> [|? ? ih] [|? ?] [|? ?] //=; rewrite meetUl ih. Qed.

#[export]
HB.instance Definition _ :=
  Lattice_MeetIsDistributive.Build _ (seq T) meetUl.

End DistrLattice.

End SeqProdOrder.

Module Exports.

HB.reexport SeqProdOrder.

Notation seqprod_with := type.
Notation seqprod := (type prod_display).

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
Context {disp : unit}.

HB.instance Definition _ (T : porderType disp) :=
  POrder.copy (seq T) (seqprod T).
HB.instance Definition _ (T : latticeType disp) :=
  BLattice.copy (seq T) (seqprod T).
HB.instance Definition _ (T : distrLatticeType disp) :=
  BDistrLattice.copy (seq T) (seqprod T).

End DefaultSeqProdOrder.
End DefaultSeqProdOrder.

(*********************************************)
(* We declare a "copy" of the sequences,     *)
(* which has canonical lexicographic order.  *)
(*********************************************)

Module SeqLexiOrder.
Section SeqLexiOrder.

Definition type (disp : unit) T := seq T.

Context {disp disp' : unit}.

Local Notation seq := (type disp').

#[export] HB.instance Definition _ (T : eqType) := Equality.on (seq T).
#[export] HB.instance Definition _ (T : choiceType) := Choice.on (seq T).
#[export] HB.instance Definition _ (T : countType) := Countable.on (seq T).

Section POrder.
Variable T : porderType disp.
Implicit Types s : seq T.

Fixpoint le s1 s2 := if s1 isn't x1 :: s1' then true else
                     if s2 isn't x2 :: s2' then false else
                       (x1 <= x2) && ((x1 >= x2) ==> le s1' s2').
Fixpoint lt s1 s2 := if s2 isn't x2 :: s2' then false else
                     if s1 isn't x1 :: s1' then true else
                       (x1 <= x2) && ((x1 >= x2) ==> lt s1' s2').

Fact refl: reflexive le.
Proof. by elim => [|x s ih] //=; rewrite lexx. Qed.

Fact anti: antisymmetric le.
Proof.
move=> x y /andP []; elim: x y => [|x sx ih] [|y sy] //=.
by case: comparableP => //= -> lesxsy /(ih _ lesxsy) ->.
Qed.

Fact trans: transitive le.
Proof.
elim=> [|y sy ihs] [|x sx] [|z sz] //=; case: (comparableP x y) => //= [xy|->].
  by move=> _ /andP[/(lt_le_trans xy) xz _]; rewrite (ltW xz)// lt_geF.
by case: comparableP => //= _; apply: ihs.
Qed.

Lemma lt_def s1 s2 : lt  s1 s2 = (s2 != s1) && le s1 s2.
Proof.
elim: s1 s2 => [|x s1 ihs1] [|y s2]//=.
by rewrite eqseq_cons ihs1; case: comparableP.
Qed.

#[export]
HB.instance Definition _ := isPOrdered.Build disp' (seq T) lt_def refl anti trans.

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

Lemma neqhead_lexiE (x y : T) s1 s2 : x != y ->
  (x :: s1 <= y :: s2 :> seq _) = (x < y).
Proof. by rewrite lexi_cons; case: comparableP. Qed.

Lemma neqhead_ltxiE (x y : T) s1 s2 : x != y ->
  (x :: s1 < y :: s2 :> seq _) = (x < y).
Proof. by rewrite ltxi_cons; case: (comparableP x y). Qed.

End POrder.

Section Total.
Variable T : orderType disp.
Implicit Types s : seq T.

Fact total : total (<=%O : rel (seq T)).
Proof.
by elim=> [|x1 s1 ihs1] [|x2 s2]//=; rewrite !lexi_cons; case: ltgtP => /=.
Qed.

#[export]
HB.instance Definition _ := POrder_isTotal.Build _ (seq T) total.
#[export]
HB.instance Definition _ := hasBottom.Build _ (seq T) (@lexi0s _).

End Total.

Lemma sub_seqprod_lexi d (T : porderType disp) :
   subrel (<=%O : rel (seqprod_with d T)) (<=%O : rel (seq T)).
Proof.
elim=> [|x1 s1 ihs1] [|x2 s2]//=; rewrite le_cons lexi_cons /=.
by move=> /andP[-> /ihs1->]; rewrite implybT.
Qed.

End SeqLexiOrder.

Module Exports.

HB.reexport SeqLexiOrder.

Notation seqlexi_with := type.
Notation seqlexi := (type lexi_display).

Definition leEseqlexi := @leEseqlexi.
Definition lexi0s := @lexi0s.
Definition lexis0 := @lexis0.
Definition lexi_cons := @lexi_cons.
Definition lexi_lehead := @lexi_lehead.
Definition eqhead_lexiE := @eqhead_lexiE.
Definition neqhead_lexiE := @neqhead_lexiE.

Definition ltEseqltxi := @ltEseqlexi.
Definition ltxi0s := @ltxi0s.
Definition ltxis0 := @ltxis0.
Definition ltxi_cons := @ltxi_cons.
Definition ltxi_lehead := @ltxi_lehead.
Definition eqhead_ltxiE := @eqhead_ltxiE.
Definition neqhead_ltxiE := @neqhead_ltxiE.
Definition sub_seqprod_lexi := @sub_seqprod_lexi.

End Exports.
End SeqLexiOrder.
HB.export SeqLexiOrder.Exports.

Module DefaultSeqLexiOrder.
Section DefaultSeqLexiOrder.
Context {disp : unit}.

HB.instance Definition _ (T : porderType disp) :=
  POrder.copy (seq T) (seqlexi T).
HB.instance Definition _ (T : orderType disp) :=
  BDistrLattice.copy (seq T) (seqlexi T).
HB.instance Definition _ (T : orderType disp) :=
  Total.copy (seq T) (seqlexi T).

End DefaultSeqLexiOrder.
End DefaultSeqLexiOrder.

(***************************************)
(* We declare a "copy" of the tuples,  *)
(* which has canonical product order.  *)
(***************************************)

Module TupleProdOrder.
Import DefaultSeqProdOrder.

Section TupleProdOrder.

Definition type (disp : unit) n T := n.-tuple T.

Context {disp disp' : unit}.
Local Notation "n .-tuple" := (type disp' n) : type_scope.

Section Basics.
Variable (n : nat).
#[export] HB.instance Definition _ (T : eqType) := Equality.on (n.-tuple T).
#[export] HB.instance Definition _ (T : choiceType) := Choice.on (n.-tuple T).
#[export] HB.instance Definition _ (T : countType) := Countable.on (n.-tuple T).
#[export] HB.instance Definition _ (T : finType) := Finite.on (n.-tuple T).
End Basics.

Section POrder.
Implicit Types (T : porderType disp).

#[export] HB.instance Definition _ n T := [POrder of n.-tuple T by <:].

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
  t1 < t2 = [exists i, tnth t1 i != tnth t2 i] &&
            [forall i, tnth t1 i <= tnth t2 i].
Proof. by rewrite lt_neqAle leEtprod eqEtuple negb_forall. Qed.

End POrder.

Section Lattice.
Variables (n : nat) (T : latticeType disp).
Implicit Types (t : n.-tuple T).

Definition meet t1 t2 : n.-tuple T :=
  [tuple of [seq x.1 `&` x.2 | x <- zip t1 t2]].
Definition join t1 t2 : n.-tuple T :=
  [tuple of [seq x.1 `|` x.2 | x <- zip t1 t2]].

Fact tnth_meet t1 t2 i : tnth (meet t1 t2) i = tnth t1 i `&` tnth t2 i.
Proof.
rewrite tnth_map -(tnth_map fst) -(tnth_map snd) -/unzip1 -/unzip2.
by rewrite !(tnth_nth (tnth_default t1 i))/= unzip1_zip ?unzip2_zip ?size_tuple.
Qed.

Fact tnth_join t1 t2 i : tnth (join t1 t2) i = tnth t1 i `|` tnth t2 i.
Proof.
rewrite tnth_map -(tnth_map fst) -(tnth_map snd) -/unzip1 -/unzip2.
by rewrite !(tnth_nth (tnth_default t1 i))/= unzip1_zip ?unzip2_zip ?size_tuple.
Qed.

Fact meetC : commutative meet.
Proof. by move=> t1 t2; apply: eq_from_tnth => i; rewrite !tnth_meet meetC. Qed.

Fact joinC : commutative join.
Proof. by move=> t1 t2; apply: eq_from_tnth => i; rewrite !tnth_join joinC. Qed.

Fact meetA : associative meet.
Proof.
by move=> t1 t2 t3; apply: eq_from_tnth => i; rewrite !tnth_meet meetA.
Qed.

Fact joinA : associative join.
Proof.
by move=> t1 t2 t3; apply: eq_from_tnth => i; rewrite !tnth_join joinA.
Qed.

Fact joinKI t2 t1 : meet t1 (join t1 t2) = t1.
Proof. by apply: eq_from_tnth => i; rewrite tnth_meet tnth_join joinKI. Qed.

Fact meetKU y x : join x (meet x y) = x.
Proof. by apply: eq_from_tnth => i; rewrite tnth_join tnth_meet meetKU. Qed.

Fact leEmeet t1 t2 : (t1 <= t2) = (meet t1 t2 == t1).
Proof.
rewrite leEtprod eqEtuple; apply: eq_forallb => /= i.
by rewrite tnth_meet leEmeet.
Qed.

#[export]
HB.instance Definition _ := POrder_isLattice.Build
  _ (n.-tuple T) meetC joinC meetA joinA joinKI meetKU leEmeet.

Lemma meetEtprod t1 t2 :
  t1 `&` t2 = [tuple of [seq x.1 `&` x.2 | x <- zip t1 t2]].
Proof. by []. Qed.

Lemma joinEtprod t1 t2 :
  t1 `|` t2 = [tuple of [seq x.1 `|` x.2 | x <- zip t1 t2]].
Proof. by []. Qed.

End Lattice.

Section BLattice.
Variables (n : nat) (T : bLatticeType disp).
Implicit Types (t : n.-tuple T).

Fact le0x t : [tuple of nseq n 0] <= t :> n.-tuple T.
Proof. by rewrite leEtprod; apply/forallP => i; rewrite tnth_nseq le0x. Qed.

#[export]
HB.instance Definition _ := hasBottom.Build _ (n.-tuple T) le0x.

Lemma botEtprod : 0 = [tuple of nseq n 0] :> n.-tuple T. Proof. by []. Qed.

End BLattice.

Section TBLattice.
Variables (n : nat) (T : tbLatticeType disp).
Implicit Types (t : n.-tuple T).

Fact lex1 t : t <= [tuple of nseq n 1] :> n.-tuple T.
Proof. by rewrite leEtprod; apply/forallP => i; rewrite tnth_nseq lex1. Qed.

#[export]
HB.instance Definition _ := hasTop.Build _ (n.-tuple T) lex1.

Lemma topEtprod : 1 = [tuple of nseq n 1] :> n.-tuple T. Proof. by []. Qed.

End TBLattice.

Section DistrLattice.
Variables (n : nat) (T : distrLatticeType disp).
Implicit Types (t : n.-tuple T).

Fact meetUl : left_distributive (@meet n T) (@join n T).
Proof.
move=> t1 t2 t3; apply: eq_from_tnth => i.
by rewrite !(tnth_meet, tnth_join) meetUl.
Qed.

#[export]
HB.instance Definition _ :=
  Lattice_MeetIsDistributive.Build _ (n.-tuple T) meetUl.

End DistrLattice.

(* FIXME *)
#[export]
HB.instance Definition _ (n : nat) (T : bDistrLatticeType disp) :=
  DistrLattice.on (n.-tuple T).
#[export]
HB.instance Definition _ (n : nat) (T : tbDistrLatticeType disp) :=
  DistrLattice.on (n.-tuple T).
(* /FIXME *)

Section CBDistrLattice.
Variables (n : nat) (T : cbDistrLatticeType disp).
Implicit Types (t : n.-tuple T).

Definition sub t1 t2 : n.-tuple T :=
  [tuple of [seq x.1 `\` x.2 | x <- zip t1 t2]].

Fact tnth_sub t1 t2 i : tnth (sub t1 t2) i = tnth t1 i `\` tnth t2 i.
Proof.
rewrite tnth_map -(tnth_map fst) -(tnth_map snd) -/unzip1 -/unzip2.
by rewrite !(tnth_nth (tnth_default t1 i))/= unzip1_zip ?unzip2_zip ?size_tuple.
Qed.

Lemma subKI t1 t2 : t2 `&` sub t1 t2 = 0.
Proof.
by apply: eq_from_tnth => i; rewrite tnth_meet tnth_sub subKI tnth_nseq.
Qed.

Lemma joinIB t1 t2 : t1 `&` t2 `|` sub t1 t2 = t1.
Proof.
by apply: eq_from_tnth => i; rewrite tnth_join tnth_meet tnth_sub joinIB.
Qed.

#[export] HB.instance Definition _ := hasSub.Build _ (n.-tuple T) subKI joinIB.

Lemma subEtprod t1 t2 :
  t1 `\` t2 = [tuple of [seq x.1 `\` x.2 | x <- zip t1 t2]].
Proof. by []. Qed.

End CBDistrLattice.

Section CTBDistrLattice.
Variables (n : nat) (T : ctbDistrLatticeType disp).
Implicit Types (t : n.-tuple T).

Definition compl t : n.-tuple T := map_tuple compl t.

Fact tnth_compl t i : tnth (compl t) i = ~` tnth t i.
Proof. by rewrite tnth_map. Qed.

Lemma complE t : compl t = sub 1 t.
Proof.
by apply: eq_from_tnth => i; rewrite tnth_compl tnth_sub complE tnth_nseq.
Qed.

#[export] HB.instance Definition _ := hasCompl.Build _ (n.-tuple T) complE.

Lemma complEtprod t : ~` t = [tuple of [seq ~` x | x <- t]].
Proof. by []. Qed.

End CTBDistrLattice.

(* FIXME *)
#[export]
HB.instance Definition _ (n : nat) (T : finPOrderType disp) :=
  POrder.on (n.-tuple T).
#[export]
HB.instance Definition _ (n : nat) (T : finLatticeType disp) :=
  Lattice.on (n.-tuple T).
#[export]
HB.instance Definition _ (n : nat) (T : finDistrLatticeType disp) :=
  DistrLattice.on (n.-tuple T).
#[export]
HB.instance Definition _ (n : nat) (T : finCDistrLatticeType disp) :=
  CTBDistrLattice.on (n.-tuple T).
(* /FIXME *)

End TupleProdOrder.

Module Exports.

HB.reexport TupleProdOrder.

Notation "n .-tupleprod[ disp ]" := (type disp n)
  (at level 2, disp at next level, format "n .-tupleprod[ disp ]") :
  type_scope.
Notation "n .-tupleprod" := (n.-tupleprod[prod_display])
  (at level 2, format "n .-tupleprod") : type_scope.

Definition leEtprod := @leEtprod.
Definition ltEtprod := @ltEtprod.
Definition meetEtprod := @meetEtprod.
Definition joinEtprod := @joinEtprod.
Definition botEtprod := @botEtprod.
Definition topEtprod := @topEtprod.
Definition subEtprod := @subEtprod.
Definition complEtprod := @complEtprod.

Definition tnth_meet := @tnth_meet.
Definition tnth_join := @tnth_join.
Definition tnth_sub := @tnth_sub.
Definition tnth_compl := @tnth_compl.

End Exports.
End TupleProdOrder.
HB.export TupleProdOrder.Exports.

Module DefaultTupleProdOrder.
Section DefaultTupleProdOrder.
Context {disp : unit}.

HB.instance Definition _ n (T : porderType disp) :=
  POrder.copy (n.-tuple T) (n.-tupleprod T).
HB.instance Definition _ n (T : latticeType disp) :=
  Lattice.copy (n.-tuple T) (n.-tupleprod T).
HB.instance Definition _ n (T : bLatticeType disp) :=
  BLattice.copy (n.-tuple T) (n.-tupleprod T).
HB.instance Definition _ n (T : tbLatticeType disp) :=
  TBLattice.copy (n.-tuple T) (n.-tupleprod T).
HB.instance Definition _ n (T : distrLatticeType disp) :=
  DistrLattice.copy (n.-tuple T) (n.-tupleprod T).
HB.instance Definition _ n (T : bDistrLatticeType disp) :=
  BDistrLattice.copy (n.-tuple T) (n.-tupleprod T).
HB.instance Definition _ n (T : tbDistrLatticeType disp) :=
  TBDistrLattice.copy (n.-tuple T) (n.-tupleprod T).
HB.instance Definition _ n (T : cbDistrLatticeType disp) :=
  CBDistrLattice.copy (n.-tuple T) (n.-tupleprod T).
HB.instance Definition _ n (T : ctbDistrLatticeType disp) :=
  CTBDistrLattice.copy (n.-tuple T) (n.-tupleprod T).
HB.instance Definition _ n (T : finPOrderType disp) :=
  FinPOrder.copy (n.-tuple T) (n.-tupleprod T).
HB.instance Definition _ n (T : finLatticeType disp) :=
  FinLattice.copy (n.-tuple T) (n.-tupleprod T).
HB.instance Definition _ n (T : finDistrLatticeType disp) :=
  FinDistrLattice.copy (n.-tuple T) (n.-tupleprod T).
HB.instance Definition _ n (T : finCDistrLatticeType disp) :=
  FinCDistrLattice.copy (n.-tuple T) (n.-tupleprod T).

End DefaultTupleProdOrder.
End DefaultTupleProdOrder.

(*********************************************)
(* We declare a "copy" of the tuples,        *)
(* which has canonical lexicographic order.  *)
(*********************************************)

Module TupleLexiOrder.
Section TupleLexiOrder.
Import DefaultSeqLexiOrder.

Definition type (disp : unit) n T := n.-tuple T.

Context {disp disp' : unit}.
Local Notation "n .-tuple" := (type disp' n) : type_scope.

Section Basics.
Variable (n : nat).
#[export] HB.instance Definition _ (T : eqType) := Equality.on (n.-tuple T).
#[export] HB.instance Definition _ (T : choiceType) := Choice.on (n.-tuple T).
#[export] HB.instance Definition _ (T : countType) := Countable.on (n.-tuple T).
#[export] HB.instance Definition _ (T : finType) := Finite.on (n.-tuple T).
End Basics.

Section POrder.
Implicit Types (T : porderType disp).

#[export] HB.instance Definition _ n T := [POrder of n.-tuple T by <:].

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

(* FIXME *)
#[export]
HB.instance Definition _ (n : nat) (T : finPOrderType disp) :=
  POrder.on (n.-tuple T).
(* /FIXME *)

#[export]
HB.instance Definition _ (n : nat) (T : orderType disp) :=
  [Order of n.-tuple T by <:].

Section BDistrLattice.
Variables (n : nat) (T : finOrderType disp).
Implicit Types (t : n.-tuple T).

Fact le0x t : [tuple of nseq n 0] <= t :> n.-tuple T.
Proof. by apply: sub_seqprod_lexi; apply: le0x (t : n.-tupleprod T). Qed.

#[export] HB.instance Definition _ := hasBottom.Build _ (n.-tuple T) le0x.

Lemma botEtlexi : 0 = [tuple of nseq n 0] :> n.-tuple T. Proof. by []. Qed.

End BDistrLattice.

Section TBDistrLattice.
Variables (n : nat) (T : finOrderType disp).
Implicit Types (t : n.-tuple T).

Fact lex1 t : t <= [tuple of nseq n 1].
Proof. by apply: sub_seqprod_lexi; apply: lex1 (t : n.-tupleprod T). Qed.

#[export] HB.instance Definition _ := hasTop.Build _ (n.-tuple T) lex1.

Lemma topEtlexi : 1 = [tuple of nseq n 1] :> n.-tuple T. Proof. by []. Qed.

End TBDistrLattice.

Lemma sub_tprod_lexi d n (T : porderType disp) :
   subrel (<=%O : rel (n.-tupleprod[d] T)) (<=%O : rel (n.-tuple T)).
Proof. exact: sub_seqprod_lexi. Qed.

End TupleLexiOrder.

Module Exports.

HB.reexport TupleLexiOrder.

Notation "n .-tuplelexi[ disp ]" := (type disp n)
  (at level 2, disp at next level, format "n .-tuplelexi[ disp ]") :
  type_scope.
Notation "n .-tuplelexi" := (n.-tuplelexi[lexi_display])
  (at level 2, format "n .-tuplelexi") : type_scope.

Definition lexi_tupleP := @lexi_tupleP.
Arguments lexi_tupleP {disp disp' n T t1 t2}.
Definition ltxi_tupleP := @ltxi_tupleP.
Arguments ltxi_tupleP {disp disp' n T t1 t2}.
Definition ltxi_tuplePlt := @ltxi_tuplePlt.
Arguments ltxi_tuplePlt {disp disp' n T t1 t2}.
Definition topEtlexi := @topEtlexi.
Definition botEtlexi := @botEtlexi.
Definition sub_tprod_lexi := @sub_tprod_lexi.

End Exports.
End TupleLexiOrder.
HB.export TupleLexiOrder.Exports.

Module DefaultTupleLexiOrder.
Section DefaultTupleLexiOrder.
Context {disp : unit}.

HB.instance Definition _ n (T : porderType disp) :=
  POrder.copy (n.-tuple T) (n.-tuplelexi T).
HB.instance Definition _ n (T : finPOrderType disp) :=
  FinPOrder.copy (n.-tuple T) (n.-tuplelexi T).
HB.instance Definition _ n (T : orderType disp) :=
  Lattice.copy (n.-tuple T) (n.-tuplelexi T).
HB.instance Definition _ n (T : orderType disp) :=
  DistrLattice.copy (n.-tuple T) (n.-tuplelexi T).
HB.instance Definition _ n (T : orderType disp) :=
  Total.copy (n.-tuple T) (n.-tuplelexi T).
HB.instance Definition _ n (T : finOrderType disp) :=
  BLattice.copy (n.-tuple T) (n.-tuplelexi T).
HB.instance Definition _ n (T : finOrderType disp) :=
  TBLattice.copy (n.-tuple T) (n.-tuplelexi T).
HB.instance Definition _ n (T : finOrderType disp) :=
  FinTotal.copy (n.-tuple T) (n.-tuplelexi T).

End DefaultTupleLexiOrder.
End DefaultTupleLexiOrder.

Module Import DualOrder.
Section DualOrder.
Context {disp : unit}.
Variable O : orderType disp.

Lemma dual_total : total (<=%O : rel O^d).
Proof. by move=> x y; exact: le_total. Qed.

#[export]
HB.instance Definition _ := DistrLattice_isTotal.Build _ O^d dual_total.

End DualOrder.

#[export]
HB.instance Definition _ d (T : finOrderType d) := FinTotal.on T^d.

Section DualOrderTheory.

Context {disp : unit} {T : orderType disp}.
Implicit Type s : seq T.

Lemma sorted_filter_gt x s :
  sorted <=%O s -> [seq y <- s | x < y] = drop (count (<= x) s) s.
Proof.
move=> s_sorted; rewrite count_le_gt -[LHS]revK -filter_rev.
rewrite (@sorted_filter_lt _ [the orderType _ of T^d]).
  by rewrite take_rev revK count_rev.
by rewrite rev_sorted.
Qed.

Lemma sorted_filter_ge x s :
  sorted <=%O s -> [seq y <- s | x <= y] = drop (count (< x) s) s.
Proof.
move=> s_sorted; rewrite count_lt_ge -[LHS]revK -filter_rev.
rewrite (@sorted_filter_le _ [the orderType _ of T^d]).
  by rewrite take_rev revK count_rev.
by rewrite rev_sorted.
Qed.

Lemma nth_count_ge x x0 s i : sorted <=%O s ->
  (count (< x) s <= i < size s)%N -> x <= nth x0 s i.
Proof.
move=> ss /andP[ige ilt]; rewrite -(subnKC ige) -nth_drop -sorted_filter_ge //.
apply/(all_nthP _ (filter_all _ _)).
by rewrite size_filter ltn_subLR // count_lt_ge subnK // count_size.
Qed.

Lemma nth_count_gt x x0 s i : sorted <=%O s ->
  (count (<= x) s <= i < size s)%N -> x < nth x0 s i.
Proof.
move=> ss /andP[ige ilt]; rewrite -(subnKC ige) -nth_drop -sorted_filter_gt //.
apply/(all_nthP _ (filter_all _ _)).
by rewrite size_filter ltn_subLR // count_le_gt subnK // count_size.
Qed.

Lemma nth_count_eq x x0 s i : sorted <=%O s ->
  (count (< x) s <= i < count (<= x) s)%N -> nth x0 s i = x.
Proof.
move=> ss /andP[ige ilt]; apply/le_anti.
by rewrite nth_count_le// nth_count_ge// ige (leq_trans ilt (count_size _ _)).
Qed.

End DualOrderTheory.

End DualOrder.

(*********************************************)
(* We declare a "copy" of the sets,          *)
(* which is canonically ordered by inclusion *)
(*********************************************)
Module SetSubsetOrder.
Section SetSubsetOrder.

Definition type (disp : unit) (T : finType) := {set T}.
Definition type_of (disp : unit) (T : finType) of phant T := type disp T.
Identity Coercion type_of_type_of : type_of >-> type.

Context {disp : unit} {T : finType}.
Local Notation "{ 'subset' T }" := (type_of disp (Phant T)).
Implicit Type (A B C : {subset T}).

Lemma le_def A B : A \subset B = (A :&: B == A).
Proof. exact/setIidPl/eqP. Qed.

Lemma setKUC B A : A :&: (A :|: B) = A.
Proof. by rewrite setUC setKU. Qed.

Lemma setKIC B A : A :|: (A :&: B) = A.
Proof. by rewrite setIC setKI. Qed.

#[export]
HB.instance Definition _ := Choice.on {subset T}.

#[export]
HB.instance Definition _ := isMeetJoinDistrLattice.Build disp {subset T}
  le_def (fun _ _ => erefl) (@setIC _) (@setUC _) (@setIA _) (@setUA _)
  setKUC setKIC (@setIUl _) (@setIid _).

#[export]
HB.instance Definition _ := hasBottom.Build disp {subset T} (@sub0set _).

#[export]
HB.instance Definition _ := hasTop.Build disp {subset T} (@subsetT _).

Lemma setIDv A B : B :&: (A :\: B) = set0.
Proof.
apply/eqP; rewrite -subset0; apply/subsetP => x.
by rewrite !inE => /and3P[->].
Qed.

#[export]
HB.instance Definition _ := hasSub.Build disp {subset T} setIDv (@setID _).

Lemma setTDsym A : ~: A = setT :\: A.
Proof. by rewrite setTD. Qed.

#[export]
HB.instance Definition _ := hasCompl.Build disp {subset T} setTDsym.

Lemma leEsubset A B : (A <= B) = (A \subset B).
Proof. by []. Qed.
Lemma meetEsubset A B : A `&` B = A :&: B.
Proof. by []. Qed.
Lemma joinEsubset A B : A `|` B = A :|: B.
Proof. by []. Qed.
Lemma botEsubset : 0 = set0 :> {subset T}.
Proof. by []. Qed.
Lemma topEsubset : 1 = setT :> {subset T}.
Proof. by []. Qed.
Lemma subEsubset A B : A `\` B = A :\: B.
Proof. by []. Qed.
Lemma complEsubset A : ~` A = ~: A.
Proof. by []. Qed.

Lemma subset_display : unit. Proof. exact: tt. Qed.

End SetSubsetOrder.

Module Exports.
Notation "{ 'subset' [ d ] T }" := (type_of d (Phant T))
  (at level 2, d at next level, format "{ 'subset' [ d ]  T }") : type_scope.
Notation "{ 'subset' T }" := {subset[subset_display] T}
  (at level 2, format "{ 'subset' T }") : type_scope.

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
Section DefaultSetSubsetOrder.
Context {disp : unit}.

HB.instance Definition _ (T : finType) := CTBDistrLattice.copy {set T} {subset T}.

End DefaultSetSubsetOrder.
End DefaultSetSubsetOrder.

Notation enum A := (sort <=%O (enum A)).

Section Enum.
Variables (d : unit) (T : finPOrderType d).

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

Lemma mono_sorted_enum d d' (T : finPOrderType d)
    (T' : porderType d') (f : T -> T') :
    total (<=%O : rel T) -> {mono f : x y / (x <= y)%O} ->
  sorted <=%O [seq f x | x <- Order.enum T].
Proof.
move=> /sort_sorted ss_sorted lef; wlog [x0 x'0] : / (T * T')%type.
  by case: (Order.enum T) => // x ? => /(_ (x, f x)).
rewrite (sorted_pairwise le_trans).
apply/(pairwiseP x'0) => i j; rewrite !inE !size_map -!Order.cardT.
move=> ilt jlt ij; rewrite !(nth_map x0) -?Order.cardT// lef.
by rewrite (sorted_leq_nth le_trans le_refl) ?inE -?Order.cardT// 1?ltnW.
Qed.

Lemma mono_unique d (T T' : finPOrderType d) (f g : T -> T') :
    total (<=%O : rel T) -> (#|T'| <= #|T|)%N ->
    {mono f : x y / x <= y} -> {mono g : x y / x <= y} ->
  f =1 g.
Proof.
move=> le_total leT'T lef leg x0; move: {+}x0.
suff: finfun f = finfun g by move=> /ffunP + x => /(_ x); rewrite !ffunE.
apply: (can_inj fgraphK); apply/val_inj => /=; rewrite !codomE.
under eq_map do rewrite ffunE; under [RHS]eq_map do rewrite ffunE.
have [finj ginj] := (inc_inj lef, inc_inj leg).
have [f' fK f'K] := inj_card_bij finj leT'T.
have [g' gK g'K] := inj_card_bij ginj leT'T.
apply/eqP; have : [seq f i | i <- Order.enum T] = [seq g i | i <- Order.enum T].
  apply: (@sorted_eq _ <=%O le_trans le_anti); rewrite ?mono_sorted_enum//.
  apply: uniq_perm; rewrite ?map_inj_uniq ?sort_uniq ?fintype.enum_uniq//.
  move=> x; apply/mapP/mapP => -[y _ ->].
    by exists (g' (f y)); rewrite ?Order.mem_enum.
  by exists (f' (g y)); rewrite ?Order.mem_enum.
move=> /eqP; rewrite !eq_map_all all_map [in X in _ -> X]all_map.
by have /permPl/perm_all-> := perm_sort <=%O (fintype.enum T).
Qed.

(* This module should be exported on demand, as in module tagnat below *)
Module Import EnumVal.
Section EnumVal.
Import OrdinalOrder.Exports.
Variables (d : unit) (T : finPOrderType d).
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

Section total.
(* We circumvent a shortcomming of finOrderType *)
(* which requires the type to be nonempty and we do not want to rule this out *)
Hypothesis (leT_total : total (<=%O : rel T)).

Lemma le_enum_val A : {mono @enum_val A : i j / i <= j}.
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

Lemma le_enum_rank : {mono enum_rank : i j / i <= j}.
Proof. exact: can_mono enum_rankK (@le_enum_val predT). Qed.

End total.
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
Notation le_enum_val := le_enum_val.
Notation le_enum_rank_in := le_enum_rank_in.
Notation le_enum_rank := le_enum_rank.

Module Syntax.
Export POSyntax.
Export LatticeSyntax.
Export BLatticeSyntax.
Export TBLatticeSyntax.
Export CBDistrLatticeSyntax.
Export CTBDistrLatticeSyntax.
Export DualSyntax.
Export DvdSyntax.
End Syntax.

Module LTheory.
Export POCoercions.
Export POrderTheory.
Export DualPOrder.

Export DualLattice.
Export LatticeTheoryMeet.
Export LatticeTheoryJoin.
Export DistrLatticeTheory.
Export BLatticeTheory.
Export DualTBLattice.
Export TBLatticeTheory.
Export BDistrLatticeTheory.
Export DualTBDistrLattice.
Export TBDistrLatticeTheory.
Export DualOrder. (* FIXME? *)
End LTheory.

Module CTheory.
Export LTheory CBDistrLatticeTheory CTBDistrLatticeTheory.
End CTheory.

Module TTheory.
Export LTheory TotalTheory.
End TTheory.

Module Theory.
Export CTheory TotalTheory.
End Theory.

Module Exports. HB.reexport. End Exports.
End Order.
Export Order.Exports.

Export Order.Syntax.

Export Order.POrder.Exports.
Export Order.FinPOrder.Exports.
Export Order.Lattice.Exports.
Export Order.BLattice.Exports.
Export Order.TBLattice.Exports.
Export Order.FinLattice.Exports.
Export Order.DistrLattice.Exports.
Export Order.BDistrLattice.Exports.
Export Order.TBDistrLattice.Exports.
Export Order.FinDistrLattice.Exports.
Export Order.CBDistrLattice.Exports.
Export Order.CTBDistrLattice.Exports.
Export Order.FinCDistrLattice.Exports.
Export Order.Total.Exports.
Export Order.FinTotal.Exports.

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

Import Order.Theory.

Module tagnat.
Section tagnat.
Import Order.EnumVal.

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

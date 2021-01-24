(* (c) Copyright 2006-2019 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice seq.
From mathcomp Require Import path fintype tuple bigop finset div prime finfun.
From mathcomp Require Import relorder finset.

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
(*              porderType d == the type of partially ordered types           *)
(*             bPOrderType d == porderType with a bottom element              *)
(*             tPOrderType d == porderType with a top element                 *)
(*            tbPOrderType d == porderType with both a top and a bottom       *)
(*     meetSemilatticeType d == the type of meet semilattices                 *)
(*    bMeetSemilatticeType d == meetSemilatticeType with a bottom element     *)
(*    tMeetSemilatticeType d == meetSemilatticeType with a top element        *)
(*   tbMeetSemilatticeType d == meetSemilatticeType with both a top and a     *)
(*                              bottom                                        *)
(*     joinSemilatticeType d == the type of join semilattices                 *)
(*    bJoinSemilatticeType d == joinSemilatticeType with a bottom element     *)
(*    tJoinSemilatticeType d == joinSemilatticeType with a top element        *)
(*   tbJoinSemilatticeType d == joinSemilatticeType with both a top and a     *)
(*                              bottom                                        *)
(*             latticeType d == the type of non-distributive lattices         *)
(*            bLatticeType d == latticeType with a bottom element             *)
(*            tLatticeType d == latticeType with a top element                *)
(*           tbLatticeType d == latticeType with both a top and a bottom      *)
(*        distrLatticeType d == the type of distributive lattices             *)
(*       bDistrLatticeType d == distrLatticeType with a bottom element        *)
(*       tDistrLatticeType d == distrLatticeType with a top element           *)
(*      tbDistrLatticeType d == distrLatticeType with both a top and a bottom *)
(*      cbDistrLatticeType d == the type of sectionally complemented          *)
(*                              distributive lattices (lattices with a bottom *)
(*                              and a difference operation)                   *)
(*     ctbDistrLatticeType d == the type of complemented distributive         *)
(*                              lattices (lattices with top, bottom,          *)
(*                              difference, and complement)                   *)
(*               orderType d == the type of totally ordered types             *)
(*              bOrderType d == orderType with a bottom element               *)
(*              tOrderType d == orderType with a top element                  *)
(*             tbOrderType d == orderType with both a top and a bottom        *)
(*           finPOrderType d == the type of partially ordered finite types    *)
(*          finBPOrderType d == finPOrderType with a bottom element           *)
(*          finTPOrderType d == finPOrderType with a top element              *)
(*         finTBPOrderType d == finPOrderType with both a top and a bottom    *)
(*  finMeetSemilatticeType d == the type of finite meet semilattices          *)
(* finBMeetSemilatticeType d == finMeetSemilatticeType with a bottom element  *)
(*  finJoinSemilatticeType d == the type of finite join semilattices          *)
(* finTJoinSemilatticeType d == finJoinSemilatticeType with a top element     *)
(*          finLatticeType d == the type of finite non-distributive lattices  *)
(*        finTBLatticeType d == finLatticeType with both a top and a bottom   *)
(*                              (nonempty finite non-distributive lattices)   *)
(*     finDistrLatticeType d == the type of finite distributive lattices      *)
(*   finTBDistrLatticeType d == finDistrLatticeType with both a top and a     *)
(*                              bottom (nonempty finite distributive lattices)*)
(*  finCTBDistrLatticeType d == the type of finite complemented distributive  *)
(*                              lattices with both a top and a bottom         *)
(*            finOrderType d == the type of totally ordered finite types      *)
(*          finTBOrderType d == finOrderType with both a top and a bottom     *)
(*                              (nonempty totally ordered finite types)       *)
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
(* For bPOrderType T                                                          *)
(*   @Order.bottom      disp T     == 0       (in order_scope)                *)
(* For tPOrderType T                                                          *)
(*   @Order.top         disp T     == 1       (in order_scope)                *)
(* For meetSemilatticeType T                                                  *)
(*   @Order.meet        disp T x y == x `&` y (in order_scope)                *)
(* For joinSemilatticeType T                                                  *)
(*   @Order.join        disp T x y == x `|` y (in order_scope)                *)
(* For cbDistrLatticeType T                                                   *)
(*   @Order.sub         disp T x y == x `\` y (in order_scope)                *)
(* For ctbDistrLatticeType T                                                  *)
(*   @Order.compl       disp T x   == ~` x    (in order_scope)                *)
(*                                                                            *)
(* This first argument named either d, disp or display, of type unit,         *)
(* configures the printing of notations.                                      *)
(* Instantiating d with tt or an unknown key will lead to a default           *)
(* display for notations, i.e. we have:                                       *)
(* For x, y of type T, where T is canonically a porderType d:                 *)
(*              x <= y <-> x is less than or equal to y.                      *)
(*               x < y <-> x is less than y (:= (y != x) && (x <= y)).        *)
(*             min x y <-> if x < y then x else y                             *)
(*             max x y <-> if x < y then y else x                             *)
(*              x >= y <-> x is greater than or equal to y (:= y <= x).       *)
(*               x > y <-> x is greater than y (:= y < x).                    *)
(*     x <= y ?= iff C <-> x is less than y, or equal iff C is true.          *)
(*      x < y ?<= if C <-> x is smaller than y, and strictly if C is false.   *)
(*             x >=< y <-> x and y are comparable (:= (x <= y) || (y <= x)).  *)
(*              x >< y <-> x and y are incomparable (:= ~~ x >=< y).          *)
(* In a type T, where T is canonically a bPOrderType d:                       *)
(*                   0 == the bottom element.                                 *)
(* In a type T, where T is canonically a tPOrderType d:                       *)
(*                   1 == the top element.                                    *)
(*            f \min g <-> the function x |-> Order.min (f x) (g x);          *)
(*                         f \min g simplifies on application.                *)
(*            f \max g <-> the function x |-> Order.max (f x) (g x);          *)
(*                         f \max g simplifies on application.                *)
(* For x, y of type T, where T is canonically a meetSemilatticeType d:        *)
(*             x `&` y == the meet of x and y.                                *)
(* For x, y of type T, where T is canonically a joinSemilatticeType d:        *)
(*             x `|` y == the join of x and y.                                *)
(* In a type T, where T is canonically a tMeetSemilatticeType d:              *)
(*     \meet_<range> e == iterated meet of a lattice with a top.              *)
(* In a type T, where T is canonically a bJoinSemilatticeType d:              *)
(*     \join_<range> e == iterated join of a lattice with a bottom.           *)
(* For x, y of type T, where T is canonically a cbDistrLatticeType d:         *)
(*             x `\` y == the (sectional) complement of y in [0, x].          *)
(* For x of type T, where T is canonically a ctbDistrLatticeType d:           *)
(*                ~` x == the complement of x in [0, 1].                      *)
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
(*    `Fact my_display : unit. Proof. exact: tt. Qed.`                        *)
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
(*      == builds a porderType from a canonical choiceType instance of T      *)
(*         where pord_mixin can be of types                                   *)
(*           lePOrderMixin, ltPOrderMixin, meetJoinMixin, leOrderMixin,       *)
(*           ltOrderMixin,                                                    *)
(*         or computed using PcanPOrderMixin or CanPOrderMixin.               *)
(*         disp is a display as explained above                               *)
(*                                                                            *)
(* BPOrderType T bot_mixin                                                    *)
(*      == builds a bPOrderType from a canonical porderType instance of T     *)
(*         and bot_mixin of type bottomMixin.                                 *)
(*                                                                            *)
(* TPOrderType T top_mixin                                                    *)
(*      == builds a tPOrderType from a canonical porderType instance of T     *)
(*         and top_mixin of type topMixin.                                    *)
(*                                                                            *)
(* MeetSemilatticeType T meet_mixin                                           *)
(*      == builds a meetSemilatticeType from a canonical porderType instance  *)
(*         of T where meet_mixin can be of types                              *)
(*           meetMixin, latticePOrderMixin, distrLatticePOrderMixin,          *)
(*           meetJoinMixin, leOrderMixin, ltOrderMixin, totalPOrderMixin,     *)
(*           totalJoinSemilatticeMixin,                                       *)
(*         or computed using IsoLatticeMixin.                                 *)
(*                                                                            *)
(* JoinSemilatticeType T join_mixin                                           *)
(*      == builds a joinSemilatticeType from a canonical porderType instance  *)
(*         of T where join_mixin can be of types                              *)
(*           joinMixin, latticePOrderMixin, distrLatticePOrderMixin,          *)
(*           meetJoinMixin, leOrderMixin, ltOrderMixin, totalPOrderMixin,     *)
(*           totalMeetSemilatticeMixin,                                       *)
(*         or computed using IsoLatticeMixin.                                 *)
(*                                                                            *)
(* DistrLatticeType T lat_mixin                                               *)
(*      == builds a distrLatticeType from a canonical latticeType instance    *)
(*         of T where lat_mixin can be of types                               *)
(*           distrLatticeMixin, distrLatticePOrderMixin, meetJoinMixin,       *)
(*           leOrderMixin, ltOrderMixin, totalPOrderMixin, totalLatticeMixin, *)
(*           totalMeetSemilatticeMixin, totalJoinSemilatticeMixin,            *)
(*         or computed using IsoLatticeMixin.                                 *)
(*                                                                            *)
(* CBDistrLatticeType T sub_mixin                                             *)
(*      == builds a cbDistrLatticeType from a canonical bDistrLatticeType     *)
(*         instance of T and sub_mixin of type cbDistrLatticeMixin.           *)
(*                                                                            *)
(* CTBDistrLatticeType T compl_mixin                                          *)
(*      == builds a ctbDistrLatticeType from canonical tbDistrLatticeType and *)
(*         cbDistrLatticeType instances of T and compl_mixin of type          *)
(*         ctbDistrLatticeMixin.                                              *)
(*                                                                            *)
(* OrderType T ord_mixin                                                      *)
(*      == builds an orderType from a canonical distrLatticeType instance     *)
(*         of T where ord_mixin can be of types                               *)
(*           leOrderMixin, ltOrderMixin, totalPOrderMixin,                    *)
(*           totalMeetSemilatticeMixin, totalJoinSemilatticeMixin,            *)
(*           totalLatticeMixin, totalOrderMixin,                              *)
(*         or computed using MonoTotalMixin.                                  *)
(*                                                                            *)
(* Additionally:                                                              *)
(* - [porderType of T] ... notations are available to recover structures on   *)
(*     "copies" of the types, as in eqType, choiceType, ssralg...             *)
(* - [tbPOrderType of T] [latticeType of T] [bLatticeType of T]               *)
(*   [finPOrderType of T] ... notations to compute an instance from canonical *)
(*     instances of poorer structures on T, e.g., a tbPOrderType instance of  *)
(*     T can be constructed from bPOrderType and tPOrderType instances of T   *)
(*     which share the same underlying porderType instance.                   *)
(*                                                                            *)
(* List of possible factories:                                                *)
(*                                                                            *)
(* - lePOrderMixin == on a choiceType, takes le, lt,                          *)
(*         reflexivity, antisymmetry and transitivity of le.                  *)
(*         (can build:  porderType)                                           *)
(*                                                                            *)
(* - ltPOrderMixin == on a choiceType, takes le, lt,                          *)
(*         irreflexivity and transitivity of lt.                              *)
(*         (can build:  porderType)                                           *)
(*                                                                            *)
(* - meetMixin == on a porderType, takes meet, commutativity and              *)
(*         associativity of meet, and a proof of                              *)
(*         (x <= y) = (meet x y == x) for any x, y.                           *)
(*         (can build:  meetSemilatticeType)                                  *)
(*                                                                            *)
(* - joinMixin == on a porderType, takes join, commutativity and              *)
(*         associativity of join, and a proof of                              *)
(*         (y <= x) = (join x y == x) for any x, y.                           *)
(*         (can build:  joinSemilatticeType)                                  *)
(*                                                                            *)
(* - latticePOrderMixin == on a porderType, takes meet, join,                 *)
(*         commutativity and associativity of meet and join, and              *)
(*         some absorption laws.                                              *)
(*         (can build:  meetSemilatticeType, joinSemilatticeType, latticeType)*)
(*                                                                            *)
(* - distrLatticeMixin                                                        *)
(*      == on a latticeType, takes distributivity of meet over join.          *)
(*         (can build:  distrLatticeType)                                     *)
(*                                                                            *)
(* - distrLatticePOrderMixin == on a porderType, takes meet, join,            *)
(*         commutativity and associativity of meet and join, and              *)
(*         the absorption and distributive laws.                              *)
(*         (can build:  meetSemilatticeType, joinSemilatticeType,             *)
(*                      latticeType, distrLatticeType)                        *)
(*                                                                            *)
(* - meetJoinMixin == on a choiceType, takes le, lt, meet, join,              *)
(*         commutativity and associativity of meet and join,                  *)
(*         the absorption and distributive laws, and idempotence of meet.     *)
(*         (can build:  porderType, meetSemilatticeType, joinSemilatticeType, *)
(*                      latticeType, distrLatticeType)                        *)
(*                                                                            *)
(* - meetJoinLeMixin == on a porderType, takes meet, join, and a proof that   *)
(*                    those are respectvely the greatest lower bound and the  *)
(*                    least upper bound.                                      *)
(*                    (can build: latticeType)                                *)
(*                                                                            *)
(* - leOrderMixin == on a choiceType, takes le, lt, meet, join,               *)
(*         antisymmetry, transitivity and totality of le.                     *)
(*         (can build:  porderType, meetSemilatticeType, joinSemilatticeType, *)
(*                      latticeType, distrLatticeType, orderType)             *)
(*                                                                            *)
(* - ltOrderMixin == on a choiceType, takes le, lt, meet, join,               *)
(*         irreflexivity, transitivity and totality of lt.                    *)
(*         (can build:  porderType, meetSemilatticeType, joinSemilatticeType, *)
(*                      latticeType, distrLatticeType, orderType)             *)
(*                                                                            *)
(* - totalPOrderMixin                                                         *)
(*      == on a porderType T, totality of the order of T                      *)
(*      := total (<=%O : rel T)                                               *)
(*         (can build:  meetSemilatticeType, joinSemilatticeType, latticeType,*)
(*                      distrLatticeType, orderType)                          *)
(*                                                                            *)
(* - totalMeetSemilatticeMixin                                                *)
(*      == on a meetSemilatticeType T, totality of the order of T             *)
(*      := total (<=%O : rel T)                                               *)
(*         (can build:  joinSemilatticeType, latticeType, distrLatticeType,   *)
(*                      orderType)                                            *)
(*                                                                            *)
(* - totalJoinSemilatticeMixin                                                *)
(*      == on a joinSemilatticeType T, totality of the order of T             *)
(*      := total (<=%O : rel T)                                               *)
(*         (can build:  meetSemilatticeType, latticeType, distrLatticeType,   *)
(*                      orderType)                                            *)
(*                                                                            *)
(* - totalLatticeMixin                                                        *)
(*      == on a latticeType T, totality of the order of T                     *)
(*      := total (<=%O : rel T)                                               *)
(*         (can build:  distrLatticeType, orderType)                          *)
(*                                                                            *)
(* - totalOrderMixin                                                          *)
(*      == on a distrLatticeType T, totality of the order of T                *)
(*      := total (<=%O : rel T)                                               *)
(*         (can build: orderType)                                             *)
(*    NB: the above three mixins are kept separate from each other (even      *)
(*        though they are convertible), in order to avoid ambiguous coercion  *)
(*        paths.                                                              *)
(*                                                                            *)
(* - bottomMixin, topMixin, cbDistrLatticeMixin, ctbDistrLatticeMixin         *)
(*      == mixins with one extra operation                                    *)
(*         (respectively bottom, top, difference, and complement)             *)
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
(* - LatticeOfPOrder builds a latticeType from a porderType and a             *)
(*   latticePOrderMixin.                                                      *)
(* - DistrLatticeOfPOrderType builds a distrLatticeType from a porderType and *)
(*   a distrLatticePOrderMixin.                                               *)
(* - OrderOfLattice builds an orderType from a latticeType and a              *)
(*   totalLatticeMixin.                                                       *)
(* - OrderOfPOrder builds an orderType from a porderType and a                *)
(*   totalPOrderMixin.                                                        *)
(* - OrderOfMeetSemilattice builds an orderType from a meetSemilatticeType    *)
(*   and a totalMeetSemilatticeMixin.                                         *)
(* - OrderOfJoinSemilattice builds an orderType from a joinSemilatticeType    *)
(*   and a totalJoinSemilatticeMixin.                                         *)
(* - LatticeOfChoiceType builds a latticeType from a choiceType and a         *)
(*   meetJoinMixin.                                                           *)
(* - DistrLatticeOfChoiceType builds a distrLatticeType from a choiceType and *)
(*   a distrMeetJoinMixin.                                                    *)
(* - OrderOfChoiceType builds an orderType from a choiceType, and a           *)
(*   leOrderMixin or a ltOrderMixin.                                          *)
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

Import RelOrder.Theory.

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

Definition dual T : Type := T.
Fact dual_display : unit -> unit. Proof. exact. Qed.

Module Import DualSyntax.
Notation "T ^d" := (dual T) (at level 2, format "T ^d") : type_scope.
End DualSyntax.

(**************)
(* STRUCTURES *)
(**************)

Module POrder.
Section ClassDef.

Set Primitive Projections.

Record mixin_of (T : eqType) := Mixin {
  le : rel T;
  lt : rel T;
  rel_mixin : RelOrder.POrder.mixin_of le lt;
}.

Record class_of (T : Type) := Class {
  base  : Choice.class_of T;
  mixin : mixin_of (Equality.Pack base);
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> Choice.class_of.

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack disp T c.
Definition clone_with disp' c of phant_id class c := @Pack disp' T c.

Definition pack :=
  fun bT b & phant_id (Choice.class bT) b =>
  fun m => Pack disp (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
End ClassDef.

Module Exports.
Coercion base : class_of >-> Choice.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion Mixin : RelOrder.POrder.mixin_of >-> mixin_of.
Coercion rel_mixin : mixin_of >-> RelOrder.POrder.mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Canonical eqType.
Canonical choiceType.
Notation porderType := type.
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

Section POrderDef.

Variables (disp : unit) (T : porderType disp).

Let ord := POrder _ _ (POrder.class T).

Definition le : rel T := RelOrder.le ord.
Local Notation "x <= y" := (le x y) : order_scope.

Definition lt : rel T := RelOrder.lt ord.
Local Notation "x < y" := (lt x y) : order_scope.

Definition comparable : rel T := fun (x y : T) => (x <= y) || (y <= x).

Definition ge : simpl_rel T := [rel x y | y <= x].
Definition gt : simpl_rel T := [rel x y | y < x].

Definition leif (x y : T) C : Prop := ((x <= y) * ((x == y) = C))%type.

Definition le_of_leif x y C (le_xy : @leif x y C) := le_xy.1 : le x y.

Definition lteif x y C := if C then x <= y else x < y.

Definition min x y := if x < y then x else y.
Definition max x y := if x < y then y else x.

Definition arg_min {I : finType} := @extremum T I le.
Definition arg_max {I : finType} := @extremum T I ge.

(* Lifted min/max operations. *)
Section LiftedPOrder.
Variable T' : Type.
Implicit Type f : T' -> T.
Definition min_fun f g x := min (f x) (g x).
Definition max_fun f g x := min (f x) (g x).
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

Notation dual_le := (@le (dual_display _) _).
Notation dual_lt := (@lt (dual_display _) _).
Notation dual_comparable := (@comparable (dual_display _) _).
Notation dual_ge := (@ge (dual_display _) _).
Notation dual_gt := (@gt (dual_display _) _).
Notation dual_leif := (@leif (dual_display _) _).
Notation dual_lteif := (@lteif (dual_display _) _).
Notation dual_max := (@max (dual_display _) _).
Notation dual_min := (@min (dual_display _) _).

Notation le_xor_gt := (RelOrder.le_xor_gt le lt).
Notation lt_xor_ge := (RelOrder.lt_xor_ge le lt).
Notation compare := (RelOrder.compare lt).
Notation incompare := (RelOrder.incompare lt comparable).

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

Notation ">=<^d y" := [pred x | >=<^d%O x y] : order_scope.
Notation ">=<^d y :> T" := (>=<^d (y : T)) (only parsing) : order_scope.
Notation "x >=<^d y" := (>=<^d%O x y) : order_scope.

Notation "><^d y" := [pred x | ~~ (>=<^d%O x y)] : order_scope.
Notation "><^d y :> T" := (><^d (y : T)) (only parsing) : order_scope.
Notation "x ><^d y" := (~~ (><^d%O x y)) : order_scope.

End POSyntax.

Module Import POCoercions.
Coercion le_of_leif : leif >-> is_true.
End POCoercions.

Module BPOrder.
Section ClassDef.

Set Primitive Projections.

Record mixin_of (T : eqType) (ord : {pOrder T}) := Mixin {
  bottom : T;
  rel_mixin : RelOrder.BPOrder.mixin_of ord bottom;
}.

Record class_of (T : Type) := Class {
  base  : POrder.class_of T;
  mixin : mixin_of (POrder _ _ base);
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> POrder.class_of.

Definition rel_class T (c : class_of T) :=
  RelOrder.BPOrder.Class (rel_mixin (mixin c)).

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack disp T c.
Definition clone_with disp' c of phant_id class c := @Pack disp' T c.

Definition pack :=
  fun bT b & phant_id (@POrder.class disp bT) b =>
  fun m => Pack disp (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition porderType := @POrder.Pack disp cT class.
End ClassDef.

Module Exports.
Coercion base : class_of >-> POrder.class_of.
Coercion rel_class : class_of >-> RelOrder.BPOrder.class_of.
Coercion Mixin : RelOrder.BPOrder.mixin_of >-> mixin_of.
Coercion rel_mixin : mixin_of >-> RelOrder.BPOrder.mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion porderType : type >-> POrder.type.
Canonical eqType.
Canonical choiceType.
Canonical porderType.
Notation bPOrderType := type.
Notation BPOrderType T m := (@pack T _ _ _ id m).
Notation "[ 'bPOrderType' 'of' T 'for' cT ]" := (@clone T _ cT _ id)
  (at level 0, format "[ 'bPOrderType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'bPOrderType' 'of' T 'for' cT 'with' disp ]" :=
  (@clone_with T _ cT disp _ id)
  (at level 0, format "[ 'bPOrderType'  'of'  T  'for'  cT  'with'  disp ]") :
  form_scope.
Notation "[ 'bPOrderType' 'of' T ]" := [bPOrderType of T for _]
  (at level 0, format "[ 'bPOrderType'  'of'  T ]") : form_scope.
Notation "[ 'bPOrderType' 'of' T 'with' disp ]" :=
  [bPOrderType of T for _ with disp]
  (at level 0, format "[ 'bPOrderType'  'of'  T  'with' disp ]") : form_scope.
End Exports.

End BPOrder.
Import BPOrder.Exports.

Module TPOrder.
Section ClassDef.

Set Primitive Projections.

Record mixin_of (T : eqType) (ord : {pOrder T}) := Mixin {
  top : T;
  rel_mixin : RelOrder.TPOrder.mixin_of ord top;
}.

Record class_of (T : Type) := Class {
  base  : POrder.class_of T;
  mixin : mixin_of (POrder _ _ base);
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> POrder.class_of.

Definition rel_class T (c : class_of T) :=
  RelOrder.TPOrder.Class (rel_mixin (mixin c)).

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variable (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack disp T c.
Definition clone_with disp' c of phant_id class c := @Pack disp' T c.

Definition pack :=
  fun bT b & phant_id (@POrder.class disp bT) b =>
  fun m => Pack disp (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition porderType := @POrder.Pack disp cT class.
End ClassDef.

Module Exports.
Coercion base : class_of >-> POrder.class_of.
Coercion rel_class : class_of >-> RelOrder.TPOrder.class_of.
Coercion Mixin : RelOrder.TPOrder.mixin_of >-> mixin_of.
Coercion rel_mixin : mixin_of >-> RelOrder.TPOrder.mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion porderType : type >-> POrder.type.
Canonical eqType.
Canonical choiceType.
Canonical porderType.
Notation tPOrderType := type.
Notation TPOrderType T m := (@pack T _ _ _ id m).
Notation "[ 'tPOrderType' 'of' T 'for' cT ]" := (@clone T _ cT _ id)
  (at level 0, format "[ 'tPOrderType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'tPOrderType' 'of' T 'for' cT 'with' disp ]" :=
  (@clone_with T _ cT disp _ id)
  (at level 0, format "[ 'tPOrderType'  'of'  T  'for'  cT  'with'  disp ]") :
  form_scope.
Notation "[ 'tPOrderType' 'of' T ]" := [tPOrderType of T for _]
  (at level 0, format "[ 'tPOrderType'  'of'  T ]") : form_scope.
Notation "[ 'tPOrderType' 'of' T 'with' disp ]" :=
  [tPOrderType of T for _ with disp]
  (at level 0, format "[ 'tPOrderType'  'of'  T  'with' disp ]") : form_scope.
End Exports.

End TPOrder.
Import TPOrder.Exports.

Module TBPOrder.

Section ClassDef.

Set Primitive Projections.

Record class_of (T : Type) := Class {
  base  : BPOrder.class_of T;
  mixin : TPOrder.mixin_of (POrder _ _ base);
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> BPOrder.class_of.
Local Coercion base2 T (c : class_of T) : TPOrder.class_of T :=
  @TPOrder.Class T c (mixin c).

Definition rel_class T (c : class_of T) :=
  @RelOrder.TBPOrder.Class _ _ _ _ _ c (mixin c).

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Definition pack :=
  fun bT b & phant_id (@BPOrder.class disp bT) b =>
  fun mT m & phant_id (@TPOrder.class disp mT) (TPOrder.Class m) =>
  Pack disp (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition porderType := @POrder.Pack disp cT class.
Definition bPOrderType := @BPOrder.Pack disp cT class.
Definition tPOrderType := @TPOrder.Pack disp cT class.
Definition bPOrder_tPOrderType := @TPOrder.Pack disp bPOrderType class.
End ClassDef.

Module Exports.
Coercion base : class_of >-> BPOrder.class_of.
Coercion base2 : class_of >-> TPOrder.class_of.
Coercion rel_class : class_of >-> RelOrder.TBPOrder.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion porderType : type >-> POrder.type.
Coercion bPOrderType : type >-> BPOrder.type.
Coercion tPOrderType : type >-> TPOrder.type.
Canonical eqType.
Canonical choiceType.
Canonical porderType.
Canonical bPOrderType.
Canonical tPOrderType.
Canonical bPOrder_tPOrderType.
Notation tbPOrderType := type.
Notation "[ 'tbPOrderType' 'of' T ]" := (@pack T _ _ _ id _ _ id)
  (at level 0, format "[ 'tbPOrderType'  'of'  T ]") : form_scope.
End Exports.

End TBPOrder.
Import TBPOrder.Exports.

Definition bottom (disp : unit) (T : bPOrderType disp) : T :=
  RelOrder.bottom (BPOrder le lt _ (BPOrder.class T)).

Definition top (disp : unit) (T : tPOrderType disp) : T :=
  RelOrder.top (TPOrder le lt _ (TPOrder.class T)).

Arguments bottom {disp T}.
Arguments top {disp T}.

Notation dual_bottom := (@bottom (dual_display _) _).
Notation dual_top := (@top (dual_display _) _).

Module Import TBPOrderSyntax.
Notation "0" := bottom : order_scope.
Notation "1" := top : order_scope.
Notation "0^d" := dual_bottom : order_scope.
Notation "1^d" := dual_top : order_scope.
End TBPOrderSyntax.

Module MeetSemilattice.
Section ClassDef.

Set Primitive Projections.

Record mixin_of (T : eqType) (ord : {pOrder T}) := Mixin {
  meet : T -> T -> T;
  rel_mixin : RelOrder.Meet.mixin_of ord meet;
}.

Record class_of (T : Type) := Class {
  base  : POrder.class_of T;
  mixin : mixin_of (POrder _ _ base);
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> POrder.class_of.

Definition rel_class T (c : class_of T) :=
  RelOrder.Meet.Class (rel_mixin (mixin c)).

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack disp T c.
Definition clone_with disp' c of phant_id class c := @Pack disp' T c.

Definition pack :=
  fun bT b & phant_id (@POrder.class disp bT) b =>
  fun m => Pack disp (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition porderType := @POrder.Pack disp cT class.
End ClassDef.

Module Exports.
Coercion base : class_of >-> POrder.class_of.
Coercion rel_class : class_of >-> RelOrder.Meet.class_of.
Coercion Mixin : RelOrder.Meet.mixin_of >-> mixin_of.
Coercion rel_mixin : mixin_of >-> RelOrder.Meet.mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion porderType : type >-> POrder.type.
Canonical eqType.
Canonical choiceType.
Canonical porderType.
Notation meetSemilatticeType := type.
Notation MeetSemilatticeType T m := (@pack T _ _ _ id m).
Notation "[ 'meetSemilatticeType' 'of' T 'for' cT ]" := (@clone T _ cT _ id)
  (at level 0, format "[ 'meetSemilatticeType'  'of'  T  'for'  cT ]") :
  form_scope.
Notation "[ 'meetSemilatticeType' 'of' T 'for' cT 'with' disp ]" :=
  (@clone_with T _ cT disp _ id)
  (at level 0,
   format "[ 'meetSemilatticeType'  'of'  T  'for'  cT  'with'  disp ]") :
  form_scope.
Notation "[ 'meetSemilatticeType' 'of' T ]" := [meetSemilatticeType of T for _]
  (at level 0, format "[ 'meetSemilatticeType'  'of'  T ]") : form_scope.
Notation "[ 'meetSemilatticeType' 'of' T 'with' disp ]" :=
  [meetSemilatticeType of T for _ with disp]
  (at level 0, format "[ 'meetSemilatticeType'  'of'  T  'with' disp ]") :
  form_scope.
End Exports.

End MeetSemilattice.
Import MeetSemilattice.Exports.

Module BMeetSemilattice.
Section ClassDef.

Set Primitive Projections.

Record class_of (T : Type) := Class {
  base  : MeetSemilattice.class_of T;
  mixin : BPOrder.mixin_of (POrder _ _ base);
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> MeetSemilattice.class_of.
Local Coercion base2 T (c : class_of T) : BPOrder.class_of T :=
  @BPOrder.Class T c (mixin c).

Definition rel_class T (c : class_of T) :=
  @RelOrder.BMeet.Class _ _ _ _ _ c (mixin c).

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Definition pack :=
  fun bT b & phant_id (@MeetSemilattice.class disp bT) b =>
  fun mT m & phant_id (@BPOrder.class disp mT) (BPOrder.Class m) =>
  Pack disp (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition porderType := @POrder.Pack disp cT class.
Definition bPOrderType := @BPOrder.Pack disp cT class.
Definition meetSemilatticeType := @MeetSemilattice.Pack disp cT class.
Definition bPOrder_meetSemilatticeType :=
  @MeetSemilattice.Pack disp bPOrderType class.
End ClassDef.

Module Exports.
Coercion base : class_of >-> MeetSemilattice.class_of.
Coercion base2 : class_of >-> BPOrder.class_of.
Coercion rel_class : class_of >-> RelOrder.BMeet.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion porderType : type >-> POrder.type.
Coercion bPOrderType : type >-> BPOrder.type.
Coercion meetSemilatticeType : type >-> MeetSemilattice.type.
Canonical eqType.
Canonical choiceType.
Canonical porderType.
Canonical bPOrderType.
Canonical meetSemilatticeType.
Canonical bPOrder_meetSemilatticeType.
Notation bMeetSemilatticeType := type.
Notation "[ 'bMeetSemilatticeType' 'of' T ]" := (@pack T _ _ _ id _ _ id)
  (at level 0, format "[ 'bMeetSemilatticeType'  'of'  T ]") : form_scope.
End Exports.

End BMeetSemilattice.
Import BMeetSemilattice.Exports.

Module TMeetSemilattice.
Section ClassDef.

Set Primitive Projections.

Record class_of (T : Type) := Class {
  base  : MeetSemilattice.class_of T;
  mixin : TPOrder.mixin_of (POrder _ _ base);
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> MeetSemilattice.class_of.
Local Coercion base2 T (c : class_of T) : TPOrder.class_of T :=
  @TPOrder.Class T c (mixin c).

Definition rel_class T (c : class_of T) :=
  @RelOrder.TMeet.Class _ _ _ _ _ c (mixin c).

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Definition pack :=
  fun bT b & phant_id (@MeetSemilattice.class disp bT) b =>
  fun mT m & phant_id (@TPOrder.class disp mT) (TPOrder.Class m) =>
  Pack disp (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition porderType := @POrder.Pack disp cT class.
Definition tPOrderType := @TPOrder.Pack disp cT class.
Definition meetSemilatticeType := @MeetSemilattice.Pack disp cT class.
Definition tPOrder_meetSemilatticeType :=
  @MeetSemilattice.Pack disp tPOrderType class.
End ClassDef.

Module Exports.
Coercion base : class_of >-> MeetSemilattice.class_of.
Coercion base2 : class_of >-> TPOrder.class_of.
Coercion rel_class : class_of >-> RelOrder.TMeet.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion porderType : type >-> POrder.type.
Coercion tPOrderType : type >-> TPOrder.type.
Coercion meetSemilatticeType : type >-> MeetSemilattice.type.
Canonical eqType.
Canonical choiceType.
Canonical porderType.
Canonical tPOrderType.
Canonical meetSemilatticeType.
Canonical tPOrder_meetSemilatticeType.
Notation tMeetSemilatticeType := type.
Notation "[ 'tMeetSemilatticeType' 'of' T ]" := (@pack T _ _ _ id _ _ id)
  (at level 0, format "[ 'tMeetSemilatticeType'  'of'  T ]") : form_scope.
End Exports.

End TMeetSemilattice.
Import TMeetSemilattice.Exports.

Module TBMeetSemilattice.
Section ClassDef.

Set Primitive Projections.

Record class_of (T : Type) := Class {
  base  : BMeetSemilattice.class_of T;
  mixin : TPOrder.mixin_of (POrder _ _ base);
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> BMeetSemilattice.class_of.
Local Coercion base2 T (c : class_of T) : TMeetSemilattice.class_of T :=
  @TMeetSemilattice.Class T c (mixin c).
Local Coercion base3 T (c : class_of T) : TBPOrder.class_of T :=
  @TBPOrder.Class T c (mixin c).

Definition rel_class T (c : class_of T) :=
  @RelOrder.TBMeet.Class _ _ _ _ _ _ c (mixin c).

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Definition pack :=
  fun bT b & phant_id (@BMeetSemilattice.class disp bT) b =>
  fun mT m & phant_id (@TPOrder.class disp mT) (TPOrder.Class m) =>
  Pack disp (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition porderType := @POrder.Pack disp cT class.
Definition bPOrderType := @BPOrder.Pack disp cT class.
Definition tPOrderType := @TPOrder.Pack disp cT class.
Definition tbPOrderType := @TBPOrder.Pack disp cT class.
Definition meetSemilatticeType := @MeetSemilattice.Pack disp cT class.
Definition bMeetSemilatticeType := @BMeetSemilattice.Pack disp cT class.
Definition tMeetSemilatticeType := @TMeetSemilattice.Pack disp cT class.
Definition bPOrder_tMeetSemilatticeType :=
  @TMeetSemilattice.Pack disp bPOrderType class.
Definition tPOrder_bMeetSemilatticeType :=
  @BMeetSemilattice.Pack disp tPOrderType class.
Definition tbPOrder_meetSemilatticeType :=
  @MeetSemilattice.Pack disp tbPOrderType class.
Definition tbPOrder_bMeetSemilatticeType :=
  @BMeetSemilattice.Pack disp tbPOrderType class.
Definition tbPOrder_tMeetSemilatticeType :=
  @TMeetSemilattice.Pack disp tbPOrderType class.
Definition bMeetSemilattice_tMeetSemilatticeType :=
  @TMeetSemilattice.Pack disp bMeetSemilatticeType class.
End ClassDef.

Module Exports.
Coercion base : class_of >-> BMeetSemilattice.class_of.
Coercion base2 : class_of >-> TMeetSemilattice.class_of.
Coercion base3 : class_of >-> TBPOrder.class_of.
Coercion rel_class : class_of >-> RelOrder.TBMeet.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion porderType : type >-> POrder.type.
Coercion bPOrderType : type >-> BPOrder.type.
Coercion tPOrderType : type >-> TPOrder.type.
Coercion tbPOrderType : type >-> TBPOrder.type.
Coercion meetSemilatticeType : type >-> MeetSemilattice.type.
Coercion bMeetSemilatticeType : type >-> BMeetSemilattice.type.
Coercion tMeetSemilatticeType : type >-> TMeetSemilattice.type.
Canonical eqType.
Canonical choiceType.
Canonical porderType.
Canonical bPOrderType.
Canonical tPOrderType.
Canonical tbPOrderType.
Canonical meetSemilatticeType.
Canonical bMeetSemilatticeType.
Canonical tMeetSemilatticeType.
Canonical bPOrder_tMeetSemilatticeType.
Canonical tPOrder_bMeetSemilatticeType.
Canonical tbPOrder_meetSemilatticeType.
Canonical tbPOrder_bMeetSemilatticeType.
Canonical tbPOrder_tMeetSemilatticeType.
Canonical bMeetSemilattice_tMeetSemilatticeType.
Notation tbMeetSemilatticeType := type.
Notation "[ 'tbMeetSemilatticeType' 'of' T ]" := (@pack T _ _ _ id _ _ id)
  (at level 0, format "[ 'tbMeetSemilatticeType'  'of'  T ]") : form_scope.
End Exports.

End TBMeetSemilattice.
Import TBMeetSemilattice.Exports.

Module JoinSemilattice.
Section ClassDef.

Set Primitive Projections.

Record mixin_of (T : eqType) (ord : {pOrder T}) := Mixin {
  join : T -> T -> T;
  rel_mixin : RelOrder.Join.mixin_of ord join;
}.

Record class_of (T : Type) := Class {
  base  : POrder.class_of T;
  mixin : mixin_of (POrder _ _ base);
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> POrder.class_of.

Definition rel_class T (c : class_of T) :=
  RelOrder.Join.Class (rel_mixin (mixin c)).

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack disp T c.
Definition clone_with disp' c of phant_id class c := @Pack disp' T c.

Definition pack :=
  fun bT b & phant_id (@POrder.class disp bT) b =>
  fun m => Pack disp (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition porderType := @POrder.Pack disp cT class.
End ClassDef.

Module Exports.
Coercion base : class_of >-> POrder.class_of.
Coercion rel_class : class_of >-> RelOrder.Join.class_of.
Coercion Mixin : RelOrder.Join.mixin_of >-> mixin_of.
Coercion rel_mixin : mixin_of >-> RelOrder.Join.mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion porderType : type >-> POrder.type.
Canonical eqType.
Canonical choiceType.
Canonical porderType.
Notation joinSemilatticeType := type.
Notation JoinSemilatticeType T m := (@pack T _ _ _ id m).
Notation "[ 'joinSemilatticeType' 'of' T 'for' cT ]" := (@clone T _ cT _ id)
  (at level 0, format "[ 'joinSemilatticeType'  'of'  T  'for'  cT ]") :
  form_scope.
Notation "[ 'joinSemilatticeType' 'of' T 'for' cT 'with' disp ]" :=
  (@clone_with T _ cT disp _ id)
  (at level 0,
   format "[ 'joinSemilatticeType'  'of'  T  'for'  cT  'with'  disp ]") :
  form_scope.
Notation "[ 'joinSemilatticeType' 'of' T ]" := [joinSemilatticeType of T for _]
  (at level 0, format "[ 'joinSemilatticeType'  'of'  T ]") : form_scope.
Notation "[ 'joinSemilatticeType' 'of' T 'with' disp ]" :=
  [joinSemilatticeType of T for _ with disp]
  (at level 0, format "[ 'joinSemilatticeType'  'of'  T  'with' disp ]") :
  form_scope.
End Exports.

End JoinSemilattice.
Import JoinSemilattice.Exports.

Module BJoinSemilattice.
Section ClassDef.

Set Primitive Projections.

Record class_of (T : Type) := Class {
  base  : JoinSemilattice.class_of T;
  mixin : BPOrder.mixin_of (POrder _ _ base);
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> JoinSemilattice.class_of.
Local Coercion base2 T (c : class_of T) : BPOrder.class_of T :=
  @BPOrder.Class T c (mixin c).

Definition rel_class T (c : class_of T) :=
  @RelOrder.BJoin.Class _ _ _ _ _ c (mixin c).

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Definition pack :=
  fun bT b & phant_id (@JoinSemilattice.class disp bT) b =>
  fun mT m & phant_id (@BPOrder.class disp mT) (BPOrder.Class m) =>
  Pack disp (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition porderType := @POrder.Pack disp cT class.
Definition bPOrderType := @BPOrder.Pack disp cT class.
Definition joinSemilatticeType := @JoinSemilattice.Pack disp cT class.
Definition bPOrder_joinSemilatticeType :=
  @JoinSemilattice.Pack disp bPOrderType class.
End ClassDef.

Module Exports.
Coercion base : class_of >-> JoinSemilattice.class_of.
Coercion base2 : class_of >-> BPOrder.class_of.
Coercion rel_class : class_of >-> RelOrder.BJoin.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion porderType : type >-> POrder.type.
Coercion bPOrderType : type >-> BPOrder.type.
Coercion joinSemilatticeType : type >-> JoinSemilattice.type.
Canonical eqType.
Canonical choiceType.
Canonical porderType.
Canonical bPOrderType.
Canonical joinSemilatticeType.
Canonical bPOrder_joinSemilatticeType.
Notation bJoinSemilatticeType := type.
Notation "[ 'bJoinSemilatticeType' 'of' T ]" := (@pack T _ _ _ id _ _ id)
  (at level 0, format "[ 'bJoinSemilatticeType'  'of'  T ]") : form_scope.
End Exports.

End BJoinSemilattice.
Import BJoinSemilattice.Exports.

Module TJoinSemilattice.
Section ClassDef.

Set Primitive Projections.

Record class_of (T : Type) := Class {
  base  : JoinSemilattice.class_of T;
  mixin : TPOrder.mixin_of (POrder _ _ base);
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> JoinSemilattice.class_of.
Local Coercion base2 T (c : class_of T) : TPOrder.class_of T :=
  @TPOrder.Class T c (mixin c).

Definition rel_class T (c : class_of T) :=
  @RelOrder.TJoin.Class _ _ _ _ _ c (mixin c).

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Definition pack :=
  fun bT b & phant_id (@JoinSemilattice.class disp bT) b =>
  fun mT m & phant_id (@TPOrder.class disp mT) (TPOrder.Class m) =>
  Pack disp (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition porderType := @POrder.Pack disp cT class.
Definition tPOrderType := @TPOrder.Pack disp cT class.
Definition joinSemilatticeType := @JoinSemilattice.Pack disp cT class.
Definition tPOrder_joinSemilatticeType :=
  @JoinSemilattice.Pack disp tPOrderType class.
End ClassDef.

Module Exports.
Coercion base : class_of >-> JoinSemilattice.class_of.
Coercion base2 : class_of >-> TPOrder.class_of.
Coercion rel_class : class_of >-> RelOrder.TJoin.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion porderType : type >-> POrder.type.
Coercion tPOrderType : type >-> TPOrder.type.
Coercion joinSemilatticeType : type >-> JoinSemilattice.type.
Canonical eqType.
Canonical choiceType.
Canonical porderType.
Canonical tPOrderType.
Canonical joinSemilatticeType.
Canonical tPOrder_joinSemilatticeType.
Notation tJoinSemilatticeType := type.
Notation "[ 'tJoinSemilatticeType' 'of' T ]" := (@pack T _ _ _ id _ _ id)
  (at level 0, format "[ 'tJoinSemilatticeType'  'of'  T ]") : form_scope.
End Exports.

End TJoinSemilattice.
Import TJoinSemilattice.Exports.

Module TBJoinSemilattice.
Section ClassDef.

Set Primitive Projections.

Record class_of (T : Type) := Class {
  base  : BJoinSemilattice.class_of T;
  mixin : TPOrder.mixin_of (POrder _ _ base);
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> BJoinSemilattice.class_of.
Local Coercion base2 T (c : class_of T) : TJoinSemilattice.class_of T :=
  @TJoinSemilattice.Class T c (mixin c).
Local Coercion base3 T (c : class_of T) : TBPOrder.class_of T :=
  @TBPOrder.Class T c (mixin c).

Definition rel_class T (c : class_of T) :=
  @RelOrder.TBJoin.Class _ _ _ _ _ _ c (mixin c).

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Definition pack :=
  fun bT b & phant_id (@BJoinSemilattice.class disp bT) b =>
  fun mT m & phant_id (@TPOrder.class disp mT) (TPOrder.Class m) =>
  Pack disp (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition porderType := @POrder.Pack disp cT class.
Definition bPOrderType := @BPOrder.Pack disp cT class.
Definition tPOrderType := @TPOrder.Pack disp cT class.
Definition tbPOrderType := @TBPOrder.Pack disp cT class.
Definition joinSemilatticeType := @JoinSemilattice.Pack disp cT class.
Definition bJoinSemilatticeType := @BJoinSemilattice.Pack disp cT class.
Definition tJoinSemilatticeType := @TJoinSemilattice.Pack disp cT class.
Definition bPOrder_tJoinSemilatticeType :=
  @TJoinSemilattice.Pack disp bPOrderType class.
Definition tPOrder_bJoinSemilatticeType :=
  @BJoinSemilattice.Pack disp tPOrderType class.
Definition tbPOrder_joinSemilatticeType :=
  @JoinSemilattice.Pack disp tbPOrderType class.
Definition tbPOrder_bJoinSemilatticeType :=
  @BJoinSemilattice.Pack disp tbPOrderType class.
Definition tbPOrder_tJoinSemilatticeType :=
  @TJoinSemilattice.Pack disp tbPOrderType class.
Definition bJoinSemilattice_tJoinSemilatticeType :=
  @TJoinSemilattice.Pack disp bJoinSemilatticeType class.
End ClassDef.

Module Exports.
Coercion base : class_of >-> BJoinSemilattice.class_of.
Coercion base2 : class_of >-> TJoinSemilattice.class_of.
Coercion base3 : class_of >-> TBPOrder.class_of.
Coercion rel_class : class_of >-> RelOrder.TBJoin.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion porderType : type >-> POrder.type.
Coercion bPOrderType : type >-> BPOrder.type.
Coercion tPOrderType : type >-> TPOrder.type.
Coercion tbPOrderType : type >-> TBPOrder.type.
Coercion joinSemilatticeType : type >-> JoinSemilattice.type.
Coercion bJoinSemilatticeType : type >-> BJoinSemilattice.type.
Coercion tJoinSemilatticeType : type >-> TJoinSemilattice.type.
Canonical eqType.
Canonical choiceType.
Canonical porderType.
Canonical bPOrderType.
Canonical tPOrderType.
Canonical tbPOrderType.
Canonical joinSemilatticeType.
Canonical bJoinSemilatticeType.
Canonical tJoinSemilatticeType.
Canonical bPOrder_tJoinSemilatticeType.
Canonical tPOrder_bJoinSemilatticeType.
Canonical tbPOrder_joinSemilatticeType.
Canonical tbPOrder_bJoinSemilatticeType.
Canonical tbPOrder_tJoinSemilatticeType.
Canonical bJoinSemilattice_tJoinSemilatticeType.
Notation tbJoinSemilatticeType := type.
Notation "[ 'tbJoinSemilatticeType' 'of' T ]" := (@pack T _ _ _ id _ _ id)
  (at level 0, format "[ 'tbJoinSemilatticeType'  'of'  T ]") : form_scope.
End Exports.

End TBJoinSemilattice.
Import TBJoinSemilattice.Exports.

Module Lattice.
Section ClassDef.

Set Primitive Projections.

Record class_of (T : Type) := Class {
  base  : MeetSemilattice.class_of T;
  mixin : JoinSemilattice.mixin_of (POrder _ _ base);
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> MeetSemilattice.class_of.
Local Coercion base2 T (c : class_of T) : JoinSemilattice.class_of T :=
  @JoinSemilattice.Class T c (mixin c).

Definition rel_class T (c : class_of T) :=
  @RelOrder.Lattice.Class _ _ _ _ _ c (mixin c).

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Definition pack :=
  fun bT b & phant_id (@MeetSemilattice.class disp bT) b =>
  fun mT m &
      phant_id (@JoinSemilattice.class disp mT) (JoinSemilattice.Class m) =>
  Pack disp (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition porderType := @POrder.Pack disp cT class.
Definition meetSemilatticeType := @MeetSemilattice.Pack disp cT class.
Definition joinSemilatticeType := @JoinSemilattice.Pack disp cT class.
Definition meetSemilattice_joinSemilatticeType :=
  @JoinSemilattice.Pack disp meetSemilatticeType class.
End ClassDef.

Module Exports.
Coercion base : class_of >-> MeetSemilattice.class_of.
Coercion base2 : class_of >-> JoinSemilattice.class_of.
Coercion rel_class : class_of >-> RelOrder.Lattice.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion porderType : type >-> POrder.type.
Coercion meetSemilatticeType : type >-> MeetSemilattice.type.
Coercion joinSemilatticeType : type >-> JoinSemilattice.type.
Canonical eqType.
Canonical choiceType.
Canonical porderType.
Canonical meetSemilatticeType.
Canonical joinSemilatticeType.
Canonical meetSemilattice_joinSemilatticeType.
Notation latticeType := type.
Notation "[ 'latticeType' 'of' T ]" := (@pack T _ _ _ id _ _ id)
  (at level 0, format "[ 'latticeType'  'of'  T ]") : form_scope.
End Exports.

End Lattice.
Import Lattice.Exports.

Module BLattice.
Section ClassDef.

Set Primitive Projections.

Record class_of (T : Type) := Class {
  base  : Lattice.class_of T;
  mixin : BPOrder.mixin_of (POrder _ _ base);
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> Lattice.class_of.
Local Coercion base2 T (c : class_of T) : BMeetSemilattice.class_of T :=
  @BMeetSemilattice.Class T c (mixin c).
Local Coercion base3 T (c : class_of T) : BJoinSemilattice.class_of T :=
  @BJoinSemilattice.Class T c (mixin c).

Definition rel_class T (c : class_of T) :=
  @RelOrder.BLattice.Class _ _ _ _ _ _ c (mixin c).

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Definition pack :=
  fun bT b & phant_id (@Lattice.class disp bT) b =>
  fun mT m & phant_id (@BPOrder.class disp mT) (BPOrder.Class m) =>
  Pack disp (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition porderType := @POrder.Pack disp cT class.
Definition bPOrderType := @BPOrder.Pack disp cT class.
Definition meetSemilatticeType := @MeetSemilattice.Pack disp cT class.
Definition bMeetSemilatticeType := @BMeetSemilattice.Pack disp cT class.
Definition joinSemilatticeType := @JoinSemilattice.Pack disp cT class.
Definition bJoinSemilatticeType := @BJoinSemilattice.Pack disp cT class.
Definition latticeType := @Lattice.Pack disp cT class.
Definition meetSemilattice_bJoinSemilatticeType :=
  @BJoinSemilattice.Pack disp meetSemilatticeType class.
Definition joinSemilattice_bMeetSemilatticeType :=
  @BMeetSemilattice.Pack disp joinSemilatticeType class.
Definition lattice_bPOrderType := @BPOrder.Pack disp latticeType class.
Definition lattice_bMeetSemilatticeType :=
  @BMeetSemilattice.Pack disp latticeType class.
Definition lattice_bJoinSemilatticeType :=
  @BJoinSemilattice.Pack disp latticeType class.
Definition bMeetSemilattice_bJoinSemilatticeType :=
  @BJoinSemilattice.Pack disp bMeetSemilatticeType class.
End ClassDef.

Module Exports.
Coercion base : class_of >-> Lattice.class_of.
Coercion base2 : class_of >-> BMeetSemilattice.class_of.
Coercion base3 : class_of >-> BJoinSemilattice.class_of.
Coercion rel_class : class_of >-> RelOrder.BLattice.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion porderType : type >-> POrder.type.
Coercion bPOrderType : type >-> BPOrder.type.
Coercion meetSemilatticeType : type >-> MeetSemilattice.type.
Coercion bMeetSemilatticeType : type >-> BMeetSemilattice.type.
Coercion joinSemilatticeType : type >-> JoinSemilattice.type.
Coercion bJoinSemilatticeType : type >-> BJoinSemilattice.type.
Coercion latticeType : type >-> Lattice.type.
Canonical eqType.
Canonical choiceType.
Canonical porderType.
Canonical bPOrderType.
Canonical meetSemilatticeType.
Canonical bMeetSemilatticeType.
Canonical joinSemilatticeType.
Canonical bJoinSemilatticeType.
Canonical latticeType.
Canonical meetSemilattice_bJoinSemilatticeType.
Canonical joinSemilattice_bMeetSemilatticeType.
Canonical lattice_bPOrderType.
Canonical lattice_bMeetSemilatticeType.
Canonical lattice_bJoinSemilatticeType.
Canonical bMeetSemilattice_bJoinSemilatticeType.
Notation bLatticeType := type.
Notation "[ 'bLatticeType' 'of' T ]" := (@pack T _ _ _ id _ _ id)
  (at level 0, format "[ 'bLatticeType'  'of'  T ]") : form_scope.
End Exports.

End BLattice.
Import BLattice.Exports.

Module TLattice.
Section ClassDef.

Set Primitive Projections.

Record class_of (T : Type) := Class {
  base  : Lattice.class_of T;
  mixin : TPOrder.mixin_of (POrder _ _ base);
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> Lattice.class_of.
Local Coercion base2 T (c : class_of T) : TMeetSemilattice.class_of T :=
  @TMeetSemilattice.Class T c (mixin c).
Local Coercion base3 T (c : class_of T) : TJoinSemilattice.class_of T :=
  @TJoinSemilattice.Class T c (mixin c).

Definition rel_class T (c : class_of T) :=
  @RelOrder.TLattice.Class _ _ _ _ _ _ c (mixin c).

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Definition pack :=
  fun bT b & phant_id (@Lattice.class disp bT) b =>
  fun mT m & phant_id (@TPOrder.class disp mT) (TPOrder.Class m) =>
  Pack disp (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition porderType := @POrder.Pack disp cT class.
Definition tPOrderType := @TPOrder.Pack disp cT class.
Definition meetSemilatticeType := @MeetSemilattice.Pack disp cT class.
Definition tMeetSemilatticeType := @TMeetSemilattice.Pack disp cT class.
Definition joinSemilatticeType := @JoinSemilattice.Pack disp cT class.
Definition tJoinSemilatticeType := @TJoinSemilattice.Pack disp cT class.
Definition latticeType := @Lattice.Pack disp cT class.
Definition meetSemilattice_tJoinSemilatticeType :=
  @TJoinSemilattice.Pack disp meetSemilatticeType class.
Definition joinSemilattice_tMeetSemilatticeType :=
  @TMeetSemilattice.Pack disp joinSemilatticeType class.
Definition lattice_tPOrderType := @TPOrder.Pack disp latticeType class.
Definition lattice_tMeetSemilatticeType :=
  @TMeetSemilattice.Pack disp latticeType class.
Definition lattice_tJoinSemilatticeType :=
  @TJoinSemilattice.Pack disp latticeType class.
Definition tMeetSemilattice_tJoinSemilatticeType :=
  @TJoinSemilattice.Pack disp tMeetSemilatticeType class.
End ClassDef.

Module Exports.
Coercion base : class_of >-> Lattice.class_of.
Coercion base2 : class_of >-> TMeetSemilattice.class_of.
Coercion base3 : class_of >-> TJoinSemilattice.class_of.
Coercion rel_class : class_of >-> RelOrder.TLattice.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion porderType : type >-> POrder.type.
Coercion tPOrderType : type >-> TPOrder.type.
Coercion meetSemilatticeType : type >-> MeetSemilattice.type.
Coercion tMeetSemilatticeType : type >-> TMeetSemilattice.type.
Coercion joinSemilatticeType : type >-> JoinSemilattice.type.
Coercion tJoinSemilatticeType : type >-> TJoinSemilattice.type.
Coercion latticeType : type >-> Lattice.type.
Canonical eqType.
Canonical choiceType.
Canonical porderType.
Canonical tPOrderType.
Canonical meetSemilatticeType.
Canonical tMeetSemilatticeType.
Canonical joinSemilatticeType.
Canonical tJoinSemilatticeType.
Canonical latticeType.
Canonical meetSemilattice_tJoinSemilatticeType.
Canonical joinSemilattice_tMeetSemilatticeType.
Canonical lattice_tPOrderType.
Canonical lattice_tMeetSemilatticeType.
Canonical lattice_tJoinSemilatticeType.
Canonical tMeetSemilattice_tJoinSemilatticeType.
Notation tLatticeType := type.
Notation "[ 'tLatticeType' 'of' T ]" := (@pack T _ _ _ id _ _ id)
  (at level 0, format "[ 'tLatticeType'  'of'  T ]") : form_scope.
End Exports.

End TLattice.
Import TLattice.Exports.

Module TBLattice.
Section ClassDef.

Set Primitive Projections.

Record class_of (T : Type) := Class {
  base  : BLattice.class_of T;
  mixin : TPOrder.mixin_of (POrder _ _ base);
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> BLattice.class_of.
Local Coercion base2 T (c : class_of T) : TLattice.class_of T :=
  @TLattice.Class T c (mixin c).
Local Coercion base3 T (c : class_of T) : TBMeetSemilattice.class_of T :=
  @TBMeetSemilattice.Class T c (mixin c).
Local Coercion base4 T (c : class_of T) : TBJoinSemilattice.class_of T :=
  @TBJoinSemilattice.Class T c (mixin c).

Definition rel_class T (c : class_of T) :=
  @RelOrder.TBLattice.Class _ _ _ _ _ _ _ c (mixin c).

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Definition pack :=
  fun bT b & phant_id (@BLattice.class disp bT) b =>
  fun mT m & phant_id (@TPOrder.class disp mT) (TPOrder.Class m) =>
  Pack disp (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition porderType := @POrder.Pack disp cT class.
Definition bPOrderType := @BPOrder.Pack disp cT class.
Definition tPOrderType := @TPOrder.Pack disp cT class.
Definition tbPOrderType := @TBPOrder.Pack disp cT class.
Definition meetSemilatticeType := @MeetSemilattice.Pack disp cT class.
Definition bMeetSemilatticeType := @BMeetSemilattice.Pack disp cT class.
Definition tMeetSemilatticeType := @TMeetSemilattice.Pack disp cT class.
Definition tbMeetSemilatticeType := @TBMeetSemilattice.Pack disp cT class.
Definition joinSemilatticeType := @JoinSemilattice.Pack disp cT class.
Definition bJoinSemilatticeType := @BJoinSemilattice.Pack disp cT class.
Definition tJoinSemilatticeType := @TJoinSemilattice.Pack disp cT class.
Definition tbJoinSemilatticeType := @TBJoinSemilattice.Pack disp cT class.
Definition latticeType := @Lattice.Pack disp cT class.
Definition bLatticeType := @BLattice.Pack disp cT class.
Definition tLatticeType := @TLattice.Pack disp cT class.
Definition bPOrder_tLatticeType := @TLattice.Pack disp bPOrderType class.
Definition tPOrder_bLatticeType := @BLattice.Pack disp tPOrderType class.
Definition tbPOrder_latticeType := @Lattice.Pack disp tbPOrderType class.
Definition tbPOrder_bLatticeType := @BLattice.Pack disp tbPOrderType class.
Definition tbPOrder_tLatticeType := @TLattice.Pack disp tbPOrderType class.
Definition meetSemilattice_tbJoinSemilatticeType :=
  @TBJoinSemilattice.Pack disp meetSemilatticeType class.
Definition bMeetSemilattice_tJoinSemilatticeType :=
  @TJoinSemilattice.Pack disp bMeetSemilatticeType class.
Definition bMeetSemilattice_tbJoinSemilatticeType :=
  @TBJoinSemilattice.Pack disp bMeetSemilatticeType class.
Definition bMeetSemilattice_tLatticeType :=
  @TLattice.Pack disp bMeetSemilatticeType class.
Definition tMeetSemilattice_bJoinSemilatticeType :=
  @BJoinSemilattice.Pack disp tMeetSemilatticeType class.
Definition tMeetSemilattice_tbJoinSemilatticeType :=
  @TBJoinSemilattice.Pack disp tMeetSemilatticeType class.
Definition tMeetSemilattice_bLatticeType :=
  @BLattice.Pack disp tMeetSemilatticeType class.
Definition tbMeetSemilattice_joinSemilatticeType :=
  @JoinSemilattice.Pack disp tbMeetSemilatticeType class.
Definition tbMeetSemilattice_bJoinSemilatticeType :=
  @BJoinSemilattice.Pack disp tbMeetSemilatticeType class.
Definition tbMeetSemilattice_tJoinSemilatticeType :=
  @TJoinSemilattice.Pack disp tbMeetSemilatticeType class.
Definition tbMeetSemilattice_tbJoinSemilatticeType :=
  @TBJoinSemilattice.Pack disp tbMeetSemilatticeType class.
Definition tbMeetSemilattice_latticeType :=
  @Lattice.Pack disp tbMeetSemilatticeType class.
Definition tbMeetSemilattice_bLatticeType :=
  @BLattice.Pack disp tbMeetSemilatticeType class.
Definition tbMeetSemilattice_tLatticeType :=
  @TLattice.Pack disp tbMeetSemilatticeType class.
Definition bJoinSemilattice_tLatticeType :=
  @TLattice.Pack disp bJoinSemilatticeType class.
Definition tJoinSemilattice_bLatticeType :=
  @BLattice.Pack disp tJoinSemilatticeType class.
Definition tbJoinSemilattice_latticeType :=
  @Lattice.Pack disp tbJoinSemilatticeType class.
Definition tbJoinSemilattice_bLatticeType :=
  @BLattice.Pack disp tbJoinSemilatticeType class.
Definition tbJoinSemilattice_tLatticeType :=
  @TLattice.Pack disp tbJoinSemilatticeType class.
Definition bLattice_tLatticeType := @TLattice.Pack disp bLatticeType class.
End ClassDef.

Module Exports.
Coercion base : class_of >-> BLattice.class_of.
Coercion base2 : class_of >-> TLattice.class_of.
Coercion base3 : class_of >-> TBMeetSemilattice.class_of.
Coercion base4 : class_of >-> TBJoinSemilattice.class_of.
Coercion rel_class : class_of >-> RelOrder.TBLattice.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion porderType : type >-> POrder.type.
Coercion bPOrderType : type >-> BPOrder.type.
Coercion tPOrderType : type >-> TPOrder.type.
Coercion tbPOrderType : type >-> TBPOrder.type.
Coercion meetSemilatticeType : type >-> MeetSemilattice.type.
Coercion bMeetSemilatticeType : type >-> BMeetSemilattice.type.
Coercion tMeetSemilatticeType : type >-> TMeetSemilattice.type.
Coercion tbMeetSemilatticeType : type >-> TBMeetSemilattice.type.
Coercion joinSemilatticeType : type >-> JoinSemilattice.type.
Coercion bJoinSemilatticeType : type >-> BJoinSemilattice.type.
Coercion tJoinSemilatticeType : type >-> TJoinSemilattice.type.
Coercion tbJoinSemilatticeType : type >-> TBJoinSemilattice.type.
Coercion latticeType : type >-> Lattice.type.
Coercion bLatticeType : type >-> BLattice.type.
Coercion tLatticeType : type >-> TLattice.type.
Canonical eqType.
Canonical choiceType.
Canonical porderType.
Canonical bPOrderType.
Canonical tPOrderType.
Canonical tbPOrderType.
Canonical meetSemilatticeType.
Canonical bMeetSemilatticeType.
Canonical tMeetSemilatticeType.
Canonical tbMeetSemilatticeType.
Canonical joinSemilatticeType.
Canonical bJoinSemilatticeType.
Canonical tJoinSemilatticeType.
Canonical tbJoinSemilatticeType.
Canonical latticeType.
Canonical bLatticeType.
Canonical tLatticeType.
Canonical bPOrder_tLatticeType.
Canonical tPOrder_bLatticeType.
Canonical tbPOrder_latticeType.
Canonical tbPOrder_bLatticeType.
Canonical tbPOrder_tLatticeType.
Canonical meetSemilattice_tbJoinSemilatticeType.
Canonical bMeetSemilattice_tJoinSemilatticeType.
Canonical bMeetSemilattice_tbJoinSemilatticeType.
Canonical bMeetSemilattice_tLatticeType.
Canonical tMeetSemilattice_bJoinSemilatticeType.
Canonical tMeetSemilattice_tbJoinSemilatticeType.
Canonical tMeetSemilattice_bLatticeType.
Canonical tbMeetSemilattice_joinSemilatticeType.
Canonical tbMeetSemilattice_bJoinSemilatticeType.
Canonical tbMeetSemilattice_tJoinSemilatticeType.
Canonical tbMeetSemilattice_tbJoinSemilatticeType.
Canonical tbMeetSemilattice_latticeType.
Canonical tbMeetSemilattice_bLatticeType.
Canonical tbMeetSemilattice_tLatticeType.
Canonical bJoinSemilattice_tLatticeType.
Canonical tJoinSemilattice_bLatticeType.
Canonical tbJoinSemilattice_latticeType.
Canonical tbJoinSemilattice_bLatticeType.
Canonical tbJoinSemilattice_tLatticeType.
Canonical bLattice_tLatticeType.
Notation tbLatticeType := type.
Notation "[ 'tbLatticeType' 'of' T ]" := (@pack T _ _ _ id _ _ id)
  (at level 0, format "[ 'tbLatticeType'  'of'  T ]") : form_scope.
End Exports.

End TBLattice.
Import TBLattice.Exports.

Definition meet (disp : unit) (T : meetSemilatticeType disp) : T -> T -> T :=
  RelOrder.meet (MeetOrder _ _ _ (MeetSemilattice.class T)).

Definition join (disp : unit) (T : joinSemilatticeType disp) : T -> T -> T :=
  RelOrder.join (JoinOrder _ _ _ (JoinSemilattice.class T)).

Arguments meet {disp T}.
Arguments join {disp T}.

Notation dual_meet := (@meet (dual_display _) _).
Notation dual_join := (@join (dual_display _) _).

Notation lel_xor_gt := (RelOrder.lel_xor_gt le lt).
Notation ltl_xor_ge := (RelOrder.ltl_xor_ge le lt).
Notation comparel := (RelOrder.comparel lt).
Notation incomparel := (RelOrder.incomparel lt comparable meet join).

Module Import LatticeSyntax.

Notation "x `&` y" := (meet x y) : order_scope.
Notation "x `|` y" := (join x y) : order_scope.
Notation "x `&^d` y" := (dual_meet x y) : order_scope.
Notation "x `|^d` y" := (dual_join x y) : order_scope.

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

End LatticeSyntax.

Module DistrLattice.
Section ClassDef.

Set Primitive Projections.

Record class_of (T : Type) := Class {
  base  : Lattice.class_of T;
  mixin : RelOrder.DistrLattice.mixin_of (RelOrder.Lattice.Pack _ base);
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> Lattice.class_of.

Definition rel_class T (c : class_of T) :=
  RelOrder.DistrLattice.Class (mixin c).

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack disp T c.
Definition clone_with disp' c of phant_id class c := @Pack disp' T c.

Definition pack :=
  fun bT b & phant_id (@Lattice.class disp bT) b =>
  fun m => Pack disp (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition porderType := @POrder.Pack disp cT class.
Definition meetSemilatticeType := @MeetSemilattice.Pack disp cT class.
Definition joinSemilatticeType := @JoinSemilattice.Pack disp cT class.
Definition latticeType := @Lattice.Pack disp cT class.
End ClassDef.

Module Exports.
Coercion base : class_of >-> Lattice.class_of.
Coercion rel_class : class_of >-> RelOrder.DistrLattice.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion porderType : type >-> POrder.type.
Coercion meetSemilatticeType : type >-> MeetSemilattice.type.
Coercion joinSemilatticeType : type >-> JoinSemilattice.type.
Coercion latticeType : type >-> Lattice.type.
Canonical eqType.
Canonical choiceType.
Canonical porderType.
Canonical meetSemilatticeType.
Canonical joinSemilatticeType.
Canonical latticeType.
Notation distrLatticeType := type.
Notation DistrLatticeType T m := (@pack T _ _ _ id m).
Notation "[ 'distrLatticeType' 'of' T 'for' cT ]" := (@clone T _ cT _ id)
  (at level 0, format "[ 'distrLatticeType'  'of'  T  'for'  cT ]") :
  form_scope.
Notation "[ 'distrLatticeType' 'of' T 'for' cT 'with' disp ]" :=
  (@clone_with T _ cT disp _ id)
  (at level 0,
   format "[ 'distrLatticeType'  'of'  T  'for'  cT  'with'  disp ]") :
  form_scope.
Notation "[ 'distrLatticeType' 'of' T ]" := [distrLatticeType of T for _]
  (at level 0, format "[ 'distrLatticeType'  'of'  T ]") : form_scope.
Notation "[ 'distrLatticeType' 'of' T 'with' disp ]" :=
  [distrLatticeType of T for _ with disp]
  (at level 0, format "[ 'distrLatticeType'  'of'  T  'with' disp ]") :
  form_scope.
End Exports.

End DistrLattice.
Import DistrLattice.Exports.

Module BDistrLattice.
Section ClassDef.

Set Primitive Projections.

Record class_of (T : Type) := Class {
  base  : DistrLattice.class_of T;
  mixin : BPOrder.mixin_of (POrder _ _ base);
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> DistrLattice.class_of.
Local Coercion base2 T (c : class_of T) : BLattice.class_of T :=
  @BLattice.Class T c (mixin c).

Definition rel_class T (c : class_of T) :=
  @RelOrder.BDistrLattice.Class _ _ _ _ _ _ c (mixin c).

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Definition pack :=
  fun bT b & phant_id (@DistrLattice.class disp bT) b =>
  fun mT m & phant_id (@BPOrder.class disp mT) (BPOrder.Class m) =>
  Pack disp (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition porderType := @POrder.Pack disp cT class.
Definition bPOrderType := @BPOrder.Pack disp cT class.
Definition meetSemilatticeType := @MeetSemilattice.Pack disp cT class.
Definition bMeetSemilatticeType := @BMeetSemilattice.Pack disp cT class.
Definition joinSemilatticeType := @JoinSemilattice.Pack disp cT class.
Definition bJoinSemilatticeType := @BJoinSemilattice.Pack disp cT class.
Definition latticeType := @Lattice.Pack disp cT class.
Definition bLatticeType := @BLattice.Pack disp cT class.
Definition distrLatticeType := @DistrLattice.Pack disp cT class.
Definition bPOrder_distrLatticeType :=
  @DistrLattice.Pack disp bPOrderType class.
Definition bMeetSemilattice_distrLatticeType :=
  @DistrLattice.Pack disp bMeetSemilatticeType class.
Definition bJoinSemilattice_distrLatticeType :=
  @DistrLattice.Pack disp bJoinSemilatticeType class.
Definition bLattice_distrLatticeType :=
  @DistrLattice.Pack disp bLatticeType class.
End ClassDef.

Module Exports.
Coercion base : class_of >-> DistrLattice.class_of.
Coercion base2 : class_of >-> BLattice.class_of.
Coercion rel_class : class_of >-> RelOrder.BDistrLattice.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion porderType : type >-> POrder.type.
Coercion bPOrderType : type >-> BPOrder.type.
Coercion meetSemilatticeType : type >-> MeetSemilattice.type.
Coercion bMeetSemilatticeType : type >-> BMeetSemilattice.type.
Coercion joinSemilatticeType : type >-> JoinSemilattice.type.
Coercion bJoinSemilatticeType : type >-> BJoinSemilattice.type.
Coercion latticeType : type >-> Lattice.type.
Coercion bLatticeType : type >-> BLattice.type.
Coercion distrLatticeType : type >-> DistrLattice.type.
Canonical eqType.
Canonical choiceType.
Canonical porderType.
Canonical bPOrderType.
Canonical meetSemilatticeType.
Canonical bMeetSemilatticeType.
Canonical joinSemilatticeType.
Canonical bJoinSemilatticeType.
Canonical latticeType.
Canonical bLatticeType.
Canonical distrLatticeType.
Canonical bPOrder_distrLatticeType.
Canonical bMeetSemilattice_distrLatticeType.
Canonical bJoinSemilattice_distrLatticeType.
Canonical bLattice_distrLatticeType.
Notation bDistrLatticeType := type.
Notation "[ 'bDistrLatticeType' 'of' T ]" := (@pack T _ _ _ id _ _ id)
  (at level 0, format "[ 'bDistrLatticeType'  'of'  T ]") : form_scope.
End Exports.

End BDistrLattice.
Import BDistrLattice.Exports.

Module TDistrLattice.
Section ClassDef.

Set Primitive Projections.

Record class_of (T : Type) := Class {
  base  : DistrLattice.class_of T;
  mixin : TPOrder.mixin_of (POrder _ _ base);
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> DistrLattice.class_of.
Local Coercion base2 T (c : class_of T) : TLattice.class_of T :=
  @TLattice.Class T c (mixin c).

Definition rel_class T (c : class_of T) :=
  @RelOrder.TDistrLattice.Class _ _ _ _ _ _ c (mixin c).

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Definition pack :=
  fun bT b & phant_id (@DistrLattice.class disp bT) b =>
  fun mT m & phant_id (@TPOrder.class disp mT) (TPOrder.Class m) =>
  Pack disp (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition porderType := @POrder.Pack disp cT class.
Definition tPOrderType := @TPOrder.Pack disp cT class.
Definition meetSemilatticeType := @MeetSemilattice.Pack disp cT class.
Definition tMeetSemilatticeType := @TMeetSemilattice.Pack disp cT class.
Definition joinSemilatticeType := @JoinSemilattice.Pack disp cT class.
Definition tJoinSemilatticeType := @TJoinSemilattice.Pack disp cT class.
Definition latticeType := @Lattice.Pack disp cT class.
Definition tLatticeType := @TLattice.Pack disp cT class.
Definition distrLatticeType := @DistrLattice.Pack disp cT class.
Definition tPOrder_distrLatticeType :=
  @DistrLattice.Pack disp tPOrderType class.
Definition tMeetSemilattice_distrLatticeType :=
  @DistrLattice.Pack disp tMeetSemilatticeType class.
Definition tJoinSemilattice_distrLatticeType :=
  @DistrLattice.Pack disp tJoinSemilatticeType class.
Definition tLattice_distrLatticeType :=
  @DistrLattice.Pack disp tLatticeType class.
End ClassDef.

Module Exports.
Coercion base : class_of >-> DistrLattice.class_of.
Coercion base2 : class_of >-> TLattice.class_of.
Coercion rel_class : class_of >-> RelOrder.TDistrLattice.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion porderType : type >-> POrder.type.
Coercion tPOrderType : type >-> TPOrder.type.
Coercion meetSemilatticeType : type >-> MeetSemilattice.type.
Coercion tMeetSemilatticeType : type >-> TMeetSemilattice.type.
Coercion joinSemilatticeType : type >-> JoinSemilattice.type.
Coercion tJoinSemilatticeType : type >-> TJoinSemilattice.type.
Coercion latticeType : type >-> Lattice.type.
Coercion tLatticeType : type >-> TLattice.type.
Coercion distrLatticeType : type >-> DistrLattice.type.
Canonical eqType.
Canonical choiceType.
Canonical porderType.
Canonical tPOrderType.
Canonical meetSemilatticeType.
Canonical tMeetSemilatticeType.
Canonical joinSemilatticeType.
Canonical tJoinSemilatticeType.
Canonical latticeType.
Canonical tLatticeType.
Canonical distrLatticeType.
Canonical tPOrder_distrLatticeType.
Canonical tMeetSemilattice_distrLatticeType.
Canonical tJoinSemilattice_distrLatticeType.
Canonical tLattice_distrLatticeType.
Notation tDistrLatticeType := type.
Notation "[ 'tDistrLatticeType' 'of' T ]" := (@pack T _ _ _ id _ _ id)
  (at level 0, format "[ 'tDistrLatticeType'  'of'  T ]") : form_scope.
End Exports.

End TDistrLattice.
Import TDistrLattice.Exports.

Module TBDistrLattice.
Section ClassDef.

Set Primitive Projections.

Record class_of (T : Type) := Class {
  base  : BDistrLattice.class_of T;
  mixin : TPOrder.mixin_of (POrder _ _ base);
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> BDistrLattice.class_of.
Local Coercion base2 T (c : class_of T) : TDistrLattice.class_of T :=
  @TDistrLattice.Class T c (mixin c).
Local Coercion base3 T (c : class_of T) : TBLattice.class_of T :=
  @TBLattice.Class T c (mixin c).

Definition rel_class T (c : class_of T) :=
  @RelOrder.TBDistrLattice.Class _ _ _ _ _ _ _ c (mixin c).

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Definition pack :=
  fun bT b & phant_id (@BDistrLattice.class disp bT) b =>
  fun mT m & phant_id (@TPOrder.class disp mT) (TPOrder.Class m) =>
  Pack disp (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition porderType := @POrder.Pack disp cT class.
Definition bPOrderType := @BPOrder.Pack disp cT class.
Definition tPOrderType := @TPOrder.Pack disp cT class.
Definition tbPOrderType := @TBPOrder.Pack disp cT class.
Definition meetSemilatticeType := @MeetSemilattice.Pack disp cT class.
Definition bMeetSemilatticeType := @BMeetSemilattice.Pack disp cT class.
Definition tMeetSemilatticeType := @TMeetSemilattice.Pack disp cT class.
Definition tbMeetSemilatticeType := @TBMeetSemilattice.Pack disp cT class.
Definition joinSemilatticeType := @JoinSemilattice.Pack disp cT class.
Definition bJoinSemilatticeType := @BJoinSemilattice.Pack disp cT class.
Definition tJoinSemilatticeType := @TJoinSemilattice.Pack disp cT class.
Definition tbJoinSemilatticeType := @TBJoinSemilattice.Pack disp cT class.
Definition latticeType := @Lattice.Pack disp cT class.
Definition bLatticeType := @BLattice.Pack disp cT class.
Definition tLatticeType := @TLattice.Pack disp cT class.
Definition tbLatticeType := @TBLattice.Pack disp cT class.
Definition distrLatticeType := @DistrLattice.Pack disp cT class.
Definition bDistrLatticeType := @BDistrLattice.Pack disp cT class.
Definition tDistrLatticeType := @TDistrLattice.Pack disp cT class.
Definition distrLattice_tbPOrderType :=
  @TBPOrder.Pack disp distrLatticeType class.
Definition distrLattice_tbMeetSemilatticeType :=
  @TBMeetSemilattice.Pack disp distrLatticeType class.
Definition distrLattice_tbJoinSemilatticeType :=
  @TBJoinSemilattice.Pack disp distrLatticeType class.
Definition distrLattice_tbLatticeType :=
  @TBLattice.Pack disp distrLatticeType class.
Definition bDistrLattice_tPOrderType :=
  @TPOrder.Pack disp bDistrLatticeType class.
Definition bDistrLattice_tbPOrderType :=
  @TBPOrder.Pack disp bDistrLatticeType class.
Definition bDistrLattice_tMeetSemilatticeType :=
  @TMeetSemilattice.Pack disp bDistrLatticeType class.
Definition bDistrLattice_tbMeetSemilatticeType :=
  @TBMeetSemilattice.Pack disp bDistrLatticeType class.
Definition bDistrLattice_tJoinSemilatticeType :=
  @TJoinSemilattice.Pack disp bDistrLatticeType class.
Definition bDistrLattice_tbJoinSemilatticeType :=
  @TBJoinSemilattice.Pack disp bDistrLatticeType class.
Definition bDistrLattice_tLatticeType :=
  @TLattice.Pack disp bDistrLatticeType class.
Definition bDistrLattice_tbLatticeType :=
  @TBLattice.Pack disp bDistrLatticeType class.
Definition tDistrLattice_bPOrderType :=
  @BPOrder.Pack disp tDistrLatticeType class.
Definition tDistrLattice_tbPOrderType :=
  @TBPOrder.Pack disp tDistrLatticeType class.
Definition tDistrLattice_bMeetSemilatticeType :=
  @BMeetSemilattice.Pack disp tDistrLatticeType class.
Definition tDistrLattice_tbMeetSemilatticeType :=
  @TBMeetSemilattice.Pack disp tDistrLatticeType class.
Definition tDistrLattice_bJoinSemilatticeType :=
  @BJoinSemilattice.Pack disp tDistrLatticeType class.
Definition tDistrLattice_tbJoinSemilatticeType :=
  @TBJoinSemilattice.Pack disp tDistrLatticeType class.
Definition tDistrLattice_bLatticeType :=
  @BLattice.Pack disp tDistrLatticeType class.
Definition tDistrLattice_tbLatticeType :=
  @TBLattice.Pack disp tDistrLatticeType class.
Definition tDistrLattice_bDistrLatticeType :=
  @BDistrLattice.Pack disp tDistrLatticeType class.
End ClassDef.

Module Exports.
Coercion base : class_of >-> BDistrLattice.class_of.
Coercion base2 : class_of >-> TDistrLattice.class_of.
Coercion base3 : class_of >-> TBLattice.class_of.
Coercion rel_class : class_of >-> RelOrder.TBDistrLattice.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion bPOrderType : type >-> BPOrder.type.
Coercion tPOrderType : type >-> TPOrder.type.
Coercion tbPOrderType : type >-> TBPOrder.type.
Coercion meetSemilatticeType : type >-> MeetSemilattice.type.
Coercion bMeetSemilatticeType : type >-> BMeetSemilattice.type.
Coercion tMeetSemilatticeType : type >-> TMeetSemilattice.type.
Coercion tbMeetSemilatticeType : type >-> TBMeetSemilattice.type.
Coercion joinSemilatticeType : type >-> JoinSemilattice.type.
Coercion bJoinSemilatticeType : type >-> BJoinSemilattice.type.
Coercion tJoinSemilatticeType : type >-> TJoinSemilattice.type.
Coercion tbJoinSemilatticeType : type >-> TBJoinSemilattice.type.
Coercion latticeType : type >-> Lattice.type.
Coercion bLatticeType : type >-> BLattice.type.
Coercion tLatticeType : type >-> TLattice.type.
Coercion tbLatticeType : type >-> TBLattice.type.
Coercion distrLatticeType : type >-> DistrLattice.type.
Coercion bDistrLatticeType : type >-> BDistrLattice.type.
Coercion tDistrLatticeType : type >-> TDistrLattice.type.
Canonical eqType.
Canonical choiceType.
Canonical porderType.
Canonical bPOrderType.
Canonical tPOrderType.
Canonical tbPOrderType.
Canonical meetSemilatticeType.
Canonical bMeetSemilatticeType.
Canonical tMeetSemilatticeType.
Canonical tbMeetSemilatticeType.
Canonical joinSemilatticeType.
Canonical bJoinSemilatticeType.
Canonical tJoinSemilatticeType.
Canonical tbJoinSemilatticeType.
Canonical latticeType.
Canonical bLatticeType.
Canonical tLatticeType.
Canonical tbLatticeType.
Canonical distrLatticeType.
Canonical bDistrLatticeType.
Canonical tDistrLatticeType.
Canonical distrLattice_tbPOrderType.
Canonical distrLattice_tbMeetSemilatticeType.
Canonical distrLattice_tbJoinSemilatticeType.
Canonical distrLattice_tbLatticeType.
Canonical bDistrLattice_tPOrderType.
Canonical bDistrLattice_tbPOrderType.
Canonical bDistrLattice_tMeetSemilatticeType.
Canonical bDistrLattice_tbMeetSemilatticeType.
Canonical bDistrLattice_tJoinSemilatticeType.
Canonical bDistrLattice_tbJoinSemilatticeType.
Canonical bDistrLattice_tLatticeType.
Canonical bDistrLattice_tbLatticeType.
Canonical tDistrLattice_bPOrderType.
Canonical tDistrLattice_tbPOrderType.
Canonical tDistrLattice_bMeetSemilatticeType.
Canonical tDistrLattice_tbMeetSemilatticeType.
Canonical tDistrLattice_bJoinSemilatticeType.
Canonical tDistrLattice_tbJoinSemilatticeType.
Canonical tDistrLattice_bLatticeType.
Canonical tDistrLattice_tbLatticeType.
Canonical tDistrLattice_bDistrLatticeType.
Notation tbDistrLatticeType := type.
Notation "[ 'tbDistrLatticeType' 'of' T ]" := (@pack T _ _ _ id _ _ id)
  (at level 0, format "[ 'tbDistrLatticeType'  'of'  T ]") : form_scope.
End Exports.

End TBDistrLattice.
Import TBDistrLattice.Exports.

Module CBDistrLattice.
Section ClassDef.

Set Primitive Projections.

Record mixin_of (T0 : Type) (b : BDistrLattice.class_of T0)
                (T := BDistrLattice.Pack tt b) := Mixin {
  sub : T -> T -> T;
  subKI  : forall x y, y `&` sub x y = bottom;
  joinIB : forall x y, (x `&` y) `|` sub x y = x;
}.

Record class_of (T : Type) := Class {
  base  : BDistrLattice.class_of T;
  mixin : mixin_of base;
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> BDistrLattice.class_of.

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack disp T c.
Definition clone_with disp' c of phant_id class c := @Pack disp' T c.

Definition pack :=
  fun bT b & phant_id (@BDistrLattice.class disp bT) b =>
  fun m => Pack disp (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition porderType := @POrder.Pack disp cT class.
Definition bPOrderType := @BPOrder.Pack disp cT class.
Definition meetSemilatticeType := @MeetSemilattice.Pack disp cT class.
Definition bMeetSemilatticeType := @BMeetSemilattice.Pack disp cT class.
Definition joinSemilatticeType := @JoinSemilattice.Pack disp cT class.
Definition bJoinSemilatticeType := @BJoinSemilattice.Pack disp cT class.
Definition latticeType := @Lattice.Pack disp cT class.
Definition bLatticeType := @BLattice.Pack disp cT class.
Definition distrLatticeType := @DistrLattice.Pack disp cT class.
Definition bDistrLatticeType := @BDistrLattice.Pack disp cT class.
End ClassDef.

Module Exports.
Coercion base : class_of >-> BDistrLattice.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion porderType : type >-> POrder.type.
Coercion bPOrderType : type >-> BPOrder.type.
Coercion meetSemilatticeType : type >-> MeetSemilattice.type.
Coercion bMeetSemilatticeType : type >-> BMeetSemilattice.type.
Coercion joinSemilatticeType : type >-> JoinSemilattice.type.
Coercion bJoinSemilatticeType : type >-> BJoinSemilattice.type.
Coercion latticeType : type >-> Lattice.type.
Coercion bLatticeType : type >-> BLattice.type.
Coercion distrLatticeType : type >-> DistrLattice.type.
Coercion bDistrLatticeType : type >-> BDistrLattice.type.
Canonical eqType.
Canonical choiceType.
Canonical porderType.
Canonical bPOrderType.
Canonical meetSemilatticeType.
Canonical bMeetSemilatticeType.
Canonical joinSemilatticeType.
Canonical bJoinSemilatticeType.
Canonical latticeType.
Canonical bLatticeType.
Canonical distrLatticeType.
Canonical bDistrLatticeType.
Notation cbDistrLatticeType := type.
Notation CBDistrLatticeType T m := (@pack T _ _ _ id m).
Notation "[ 'cbDistrLatticeType' 'of' T 'for' cT ]" := (@clone T _ cT _ id)
  (at level 0, format "[ 'cbDistrLatticeType'  'of'  T  'for'  cT ]") :
  form_scope.
Notation "[ 'cbDistrLatticeType' 'of' T 'for' cT 'with' disp ]" :=
  (@clone_with T _ cT disp _ id)
  (at level 0,
   format "[ 'cbDistrLatticeType'  'of'  T  'for'  cT  'with'  disp ]") :
  form_scope.
Notation "[ 'cbDistrLatticeType' 'of' T ]" := [cbDistrLatticeType of T for _]
  (at level 0, format "[ 'cbDistrLatticeType'  'of'  T ]") : form_scope.
Notation "[ 'cbDistrLatticeType' 'of' T 'with' disp ]" :=
  [cbDistrLatticeType of T for _ with disp]
  (at level 0, format "[ 'cbDistrLatticeType'  'of'  T  'with' disp ]") :
  form_scope.
End Exports.

End CBDistrLattice.
Import CBDistrLattice.Exports.

Definition sub {disp : unit} {T : cbDistrLatticeType disp} : T -> T -> T :=
  CBDistrLattice.sub (CBDistrLattice.mixin (CBDistrLattice.class T)).

Module Import CBDistrLatticeSyntax.
Notation "x `\` y" := (sub x y) : order_scope.
End CBDistrLatticeSyntax.

Module CTBDistrLattice.
Section ClassDef.

Set Primitive Projections.

Record mixin_of (T0 : Type) (b : TBDistrLattice.class_of T0)
                (T := TBDistrLattice.Pack tt b) (sub : T -> T -> T) := Mixin {
  compl : T -> T;
  complE : forall x, compl x = sub top x
}.

Record class_of (T : Type) := Class {
  base  : TBDistrLattice.class_of T;
  mixin1 : CBDistrLattice.mixin_of base;
  mixin2 : @mixin_of _ base (CBDistrLattice.sub mixin1);
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> TBDistrLattice.class_of.
Local Coercion base2 T (c : class_of T) : CBDistrLattice.class_of T :=
  CBDistrLattice.Class (mixin1 c).

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack disp T c.
Definition clone_with disp' c of phant_id class c := @Pack disp' T c.

Definition pack :=
  fun bT b & phant_id (@TBDistrLattice.class disp bT) b =>
  fun mT m0 & phant_id (@CBDistrLattice.class disp mT) (CBDistrLattice.Class m0) =>
  fun m1 => Pack disp (@Class T b m0 m1).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition porderType := @POrder.Pack disp cT class.
Definition bPOrderType := @BPOrder.Pack disp cT class.
Definition tPOrderType := @TPOrder.Pack disp cT class.
Definition tbPOrderType := @TBPOrder.Pack disp cT class.
Definition meetSemilatticeType := @MeetSemilattice.Pack disp cT class.
Definition bMeetSemilatticeType := @BMeetSemilattice.Pack disp cT class.
Definition tMeetSemilatticeType := @TMeetSemilattice.Pack disp cT class.
Definition tbMeetSemilatticeType := @TBMeetSemilattice.Pack disp cT class.
Definition joinSemilatticeType := @JoinSemilattice.Pack disp cT class.
Definition bJoinSemilatticeType := @BJoinSemilattice.Pack disp cT class.
Definition tJoinSemilatticeType := @TJoinSemilattice.Pack disp cT class.
Definition tbJoinSemilatticeType := @TBJoinSemilattice.Pack disp cT class.
Definition latticeType := @Lattice.Pack disp cT class.
Definition bLatticeType := @BLattice.Pack disp cT class.
Definition tLatticeType := @TLattice.Pack disp cT class.
Definition tbLatticeType := @TBLattice.Pack disp cT class.
Definition distrLatticeType := @DistrLattice.Pack disp cT class.
Definition bDistrLatticeType := @BDistrLattice.Pack disp cT class.
Definition tDistrLatticeType := @TDistrLattice.Pack disp cT class.
Definition tbDistrLatticeType := @TBDistrLattice.Pack disp cT class.
Definition cbDistrLatticeType := @CBDistrLattice.Pack disp cT class.
Definition cbDistrLattice_tPOrderType :=
  @TPOrder.Pack disp cbDistrLatticeType class.
Definition cbDistrLattice_tbPOrderType :=
  @TBPOrder.Pack disp cbDistrLatticeType class.
Definition cbDistrLattice_tMeetSemilatticeType :=
  @TMeetSemilattice.Pack disp cbDistrLatticeType class.
Definition cbDistrLattice_tbMeetSemilatticeType :=
  @TBMeetSemilattice.Pack disp cbDistrLatticeType class.
Definition cbDistrLattice_tJoinSemilatticeType :=
  @TJoinSemilattice.Pack disp cbDistrLatticeType class.
Definition cbDistrLattice_tbJoinSemilatticeType :=
  @TBJoinSemilattice.Pack disp cbDistrLatticeType class.
Definition cb_tLatticeType := @TLattice.Pack disp cbDistrLatticeType class.
Definition cb_tbLatticeType := @TBLattice.Pack disp cbDistrLatticeType class.
Definition cb_tDistrLatticeType :=
  @TDistrLattice.Pack disp cbDistrLatticeType class.
Definition cb_tbDistrLatticeType :=
  @TBDistrLattice.Pack disp cbDistrLatticeType class.
End ClassDef.

Module Exports.
Coercion base : class_of >-> TBDistrLattice.class_of.
Coercion base2 : class_of >-> CBDistrLattice.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion porderType : type >-> POrder.type.
Coercion bPOrderType : type >-> BPOrder.type.
Coercion tPOrderType : type >-> TPOrder.type.
Coercion tbPOrderType : type >-> TBPOrder.type.
Coercion meetSemilatticeType : type >-> MeetSemilattice.type.
Coercion bMeetSemilatticeType : type >-> BMeetSemilattice.type.
Coercion tMeetSemilatticeType : type >-> TMeetSemilattice.type.
Coercion tbMeetSemilatticeType : type >-> TBMeetSemilattice.type.
Coercion joinSemilatticeType : type >-> JoinSemilattice.type.
Coercion bJoinSemilatticeType : type >-> BJoinSemilattice.type.
Coercion tJoinSemilatticeType : type >-> TJoinSemilattice.type.
Coercion tbJoinSemilatticeType : type >-> TBJoinSemilattice.type.
Coercion latticeType : type >-> Lattice.type.
Coercion bLatticeType : type >-> BLattice.type.
Coercion tLatticeType : type >-> TLattice.type.
Coercion tbLatticeType : type >-> TBLattice.type.
Coercion distrLatticeType : type >-> DistrLattice.type.
Coercion bDistrLatticeType : type >-> BDistrLattice.type.
Coercion tDistrLatticeType : type >-> TDistrLattice.type.
Coercion tbDistrLatticeType : type >-> TBDistrLattice.type.
Coercion cbDistrLatticeType : type >-> CBDistrLattice.type.
Canonical eqType.
Canonical choiceType.
Canonical porderType.
Canonical bPOrderType.
Canonical tPOrderType.
Canonical tbPOrderType.
Canonical meetSemilatticeType.
Canonical bMeetSemilatticeType.
Canonical tMeetSemilatticeType.
Canonical tbMeetSemilatticeType.
Canonical joinSemilatticeType.
Canonical bJoinSemilatticeType.
Canonical tJoinSemilatticeType.
Canonical tbJoinSemilatticeType.
Canonical latticeType.
Canonical bLatticeType.
Canonical tLatticeType.
Canonical tbLatticeType.
Canonical distrLatticeType.
Canonical bDistrLatticeType.
Canonical tDistrLatticeType.
Canonical tbDistrLatticeType.
Canonical cbDistrLatticeType.
Canonical cbDistrLattice_tPOrderType.
Canonical cbDistrLattice_tbPOrderType.
Canonical cbDistrLattice_tMeetSemilatticeType.
Canonical cbDistrLattice_tbMeetSemilatticeType.
Canonical cbDistrLattice_tJoinSemilatticeType.
Canonical cbDistrLattice_tbJoinSemilatticeType.
Canonical cb_tLatticeType.
Canonical cb_tbLatticeType.
Canonical cb_tDistrLatticeType.
Canonical cb_tbDistrLatticeType.
Notation ctbDistrLatticeType := type.
Notation CTBDistrLatticeType T m := (@pack T _ _ _ id _ _ id m).
Notation "[ 'ctbDistrLatticeType' 'of' T 'for' cT ]" := (@clone T _ cT _ id)
  (at level 0, format "[ 'ctbDistrLatticeType'  'of'  T  'for'  cT ]") :
  form_scope.
Notation "[ 'ctbDistrLatticeType' 'of' T 'for' cT 'with' disp ]" :=
  (@clone_with T _ cT disp _ id)
  (at level 0,
   format "[ 'ctbDistrLatticeType'  'of'  T  'for'  cT  'with'  disp ]")
  : form_scope.
Notation "[ 'ctbDistrLatticeType' 'of' T ]" := [ctbDistrLatticeType of T for _]
  (at level 0, format "[ 'ctbDistrLatticeType'  'of'  T ]") : form_scope.
Notation "[ 'ctbDistrLatticeType' 'of' T 'with' disp ]" :=
  [ctbDistrLatticeType of T for _ with disp]
  (at level 0, format "[ 'ctbDistrLatticeType'  'of'  T  'with' disp ]") :
  form_scope.
Notation "[ 'default_ctbDistrLatticeType' 'of' T ]" :=
  (@pack T _ _ _ id _ _ id (Mixin (fun=> erefl)))
  (at level 0, format "[ 'default_ctbDistrLatticeType'  'of'  T ]") :
  form_scope.
End Exports.

End CTBDistrLattice.
Import CTBDistrLattice.Exports.

Definition compl {disp : unit} {T : ctbDistrLatticeType disp} : T -> T :=
  CTBDistrLattice.compl (CTBDistrLattice.mixin2 (CTBDistrLattice.class T)).

Module Import CTBDistrLatticeSyntax.
Notation "~` A" := (compl A) : order_scope.
End CTBDistrLatticeSyntax.

Module Total.
Section ClassDef.

Set Primitive Projections.

Record class_of (T : Type) := Class {
  base  : DistrLattice.class_of T;
  mixin : RelOrder.Total.mixin_of (RelOrder.DistrLattice.Pack _ base);
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> DistrLattice.class_of.

Definition rel_class T (c : class_of T) :=
  @RelOrder.Total.Class _ _ _ _ _ c (@mixin _ c).

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c & phant_id class c := @Pack disp T c.
Definition clone_with disp' c & phant_id class c := @Pack disp' T c.

Definition pack :=
  fun bT b & phant_id (@DistrLattice.class disp bT) b =>
  fun m => Pack disp (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition porderType := @POrder.Pack disp cT class.
Definition meetSemilatticeType := @MeetSemilattice.Pack disp cT class.
Definition joinSemilatticeType := @JoinSemilattice.Pack disp cT class.
Definition latticeType := @Lattice.Pack disp cT class.
Definition distrLatticeType := @DistrLattice.Pack disp cT class.
End ClassDef.

Module Exports.
Coercion base : class_of >-> DistrLattice.class_of.
Arguments mixin [T] c.
Coercion rel_class : class_of >-> RelOrder.Total.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion porderType : type >-> POrder.type.
Coercion meetSemilatticeType : type >-> MeetSemilattice.type.
Coercion joinSemilatticeType : type >-> JoinSemilattice.type.
Coercion latticeType : type >-> Lattice.type.
Coercion distrLatticeType : type >-> DistrLattice.type.
Canonical eqType.
Canonical choiceType.
Canonical porderType.
Canonical meetSemilatticeType.
Canonical joinSemilatticeType.
Canonical latticeType.
Canonical distrLatticeType.
Notation orderType := type.
Notation OrderType T m := (@pack T _ _ _ id m).
Notation "[ 'orderType' 'of' T 'for' cT ]" := (@clone T _ cT _ id)
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

Module BTotal.
Section ClassDef.

Set Primitive Projections.

Record class_of (T : Type) := Class {
  base  : Total.class_of T;
  mixin : BPOrder.mixin_of (POrder _ _ base);
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> Total.class_of.
Local Coercion base2 T (c : class_of T) : BDistrLattice.class_of T :=
  @BDistrLattice.Class T c (mixin c).

Definition rel_class T (c : class_of T) :=
  @RelOrder.BTotal.Class _ _ _ _ _ _ c (mixin c).

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Definition pack :=
  fun bT b & phant_id (@Total.class disp bT) b =>
  fun mT m & phant_id (@BPOrder.class disp mT) (BPOrder.Class m) =>
  Pack disp (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition porderType := @POrder.Pack disp cT class.
Definition bPOrderType := @BPOrder.Pack disp cT class.
Definition meetSemilatticeType := @MeetSemilattice.Pack disp cT class.
Definition bMeetSemilatticeType := @BMeetSemilattice.Pack disp cT class.
Definition joinSemilatticeType := @JoinSemilattice.Pack disp cT class.
Definition bJoinSemilatticeType := @BJoinSemilattice.Pack disp cT class.
Definition latticeType := @Lattice.Pack disp cT class.
Definition bLatticeType := @BLattice.Pack disp cT class.
Definition distrLatticeType := @DistrLattice.Pack disp cT class.
Definition bDistrLatticeType := @BDistrLattice.Pack disp cT class.
Definition orderType := @Total.Pack disp cT class.
Definition bPOrder_orderType := @Total.Pack disp bPOrderType class.
Definition bMeetSemilattice_orderType :=
  @Total.Pack disp bMeetSemilatticeType class.
Definition bJoinSemilattice_orderType :=
  @Total.Pack disp bJoinSemilatticeType class.
Definition bLattice_orderType := @Total.Pack disp bLatticeType class.
Definition bDistrLattice_orderType := @Total.Pack disp bDistrLatticeType class.
End ClassDef.

Module Exports.
Coercion base : class_of >-> Total.class_of.
Coercion base2 : class_of >-> BDistrLattice.class_of.
Coercion rel_class : class_of >-> RelOrder.BTotal.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion porderType : type >-> POrder.type.
Coercion bPOrderType : type >-> BPOrder.type.
Coercion meetSemilatticeType : type >-> MeetSemilattice.type.
Coercion bMeetSemilatticeType : type >-> BMeetSemilattice.type.
Coercion joinSemilatticeType : type >-> JoinSemilattice.type.
Coercion bJoinSemilatticeType : type >-> BJoinSemilattice.type.
Coercion latticeType : type >-> Lattice.type.
Coercion bLatticeType : type >-> BLattice.type.
Coercion distrLatticeType : type >-> DistrLattice.type.
Coercion bDistrLatticeType : type >-> BDistrLattice.type.
Coercion orderType : type >-> Total.type.
Canonical eqType.
Canonical choiceType.
Canonical porderType.
Canonical bPOrderType.
Canonical meetSemilatticeType.
Canonical bMeetSemilatticeType.
Canonical joinSemilatticeType.
Canonical bJoinSemilatticeType.
Canonical latticeType.
Canonical bLatticeType.
Canonical distrLatticeType.
Canonical bDistrLatticeType.
Canonical orderType.
Canonical bPOrder_orderType.
Canonical bMeetSemilattice_orderType.
Canonical bJoinSemilattice_orderType.
Canonical bLattice_orderType.
Canonical bDistrLattice_orderType.
Notation bOrderType := type.
Notation "[ 'bOrderType' 'of' T ]" := (@pack T _ _ _ id _ _ id)
  (at level 0, format "[ 'bOrderType'  'of'  T ]") : form_scope.
End Exports.

End BTotal.
Import BTotal.Exports.

Module TTotal.
Section ClassDef.

Set Primitive Projections.

Record class_of (T : Type) := Class {
  base  : Total.class_of T;
  mixin : TPOrder.mixin_of (POrder _ _ base);
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> Total.class_of.
Local Coercion base2 T (c : class_of T) : TDistrLattice.class_of T :=
  @TDistrLattice.Class T c (mixin c).

Definition rel_class T (c : class_of T) :=
  @RelOrder.TTotal.Class _ _ _ _ _ _ c (mixin c).

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Definition pack :=
  fun bT b & phant_id (@Total.class disp bT) b =>
  fun mT m & phant_id (@TPOrder.class disp mT) (TPOrder.Class m) =>
  Pack disp (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition porderType := @POrder.Pack disp cT class.
Definition tPOrderType := @TPOrder.Pack disp cT class.
Definition meetSemilatticeType := @MeetSemilattice.Pack disp cT class.
Definition tMeetSemilatticeType := @TMeetSemilattice.Pack disp cT class.
Definition joinSemilatticeType := @JoinSemilattice.Pack disp cT class.
Definition tJoinSemilatticeType := @TJoinSemilattice.Pack disp cT class.
Definition latticeType := @Lattice.Pack disp cT class.
Definition tLatticeType := @TLattice.Pack disp cT class.
Definition distrLatticeType := @DistrLattice.Pack disp cT class.
Definition tDistrLatticeType := @TDistrLattice.Pack disp cT class.
Definition orderType := @Total.Pack disp cT class.
Definition tPOrder_orderType := @Total.Pack disp tPOrderType class.
Definition tMeetSemilattice_orderType :=
  @Total.Pack disp tMeetSemilatticeType class.
Definition tJoinSemilattice_orderType :=
  @Total.Pack disp tJoinSemilatticeType class.
Definition tLattice_orderType := @Total.Pack disp tLatticeType class.
Definition tDistrLattice_orderType := @Total.Pack disp tDistrLatticeType class.
End ClassDef.

Module Exports.
Coercion base : class_of >-> Total.class_of.
Coercion base2 : class_of >-> TDistrLattice.class_of.
Coercion rel_class : class_of >-> RelOrder.TTotal.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion porderType : type >-> POrder.type.
Coercion tPOrderType : type >-> TPOrder.type.
Coercion meetSemilatticeType : type >-> MeetSemilattice.type.
Coercion tMeetSemilatticeType : type >-> TMeetSemilattice.type.
Coercion joinSemilatticeType : type >-> JoinSemilattice.type.
Coercion tJoinSemilatticeType : type >-> TJoinSemilattice.type.
Coercion latticeType : type >-> Lattice.type.
Coercion tLatticeType : type >-> TLattice.type.
Coercion distrLatticeType : type >-> DistrLattice.type.
Coercion tDistrLatticeType : type >-> TDistrLattice.type.
Coercion orderType : type >-> Total.type.
Canonical eqType.
Canonical choiceType.
Canonical porderType.
Canonical tPOrderType.
Canonical meetSemilatticeType.
Canonical tMeetSemilatticeType.
Canonical joinSemilatticeType.
Canonical tJoinSemilatticeType.
Canonical latticeType.
Canonical tLatticeType.
Canonical distrLatticeType.
Canonical tDistrLatticeType.
Canonical orderType.
Canonical tPOrder_orderType.
Canonical tMeetSemilattice_orderType.
Canonical tJoinSemilattice_orderType.
Canonical tLattice_orderType.
Canonical tDistrLattice_orderType.
Notation tOrderType := type.
Notation "[ 'tOrderType' 'of' T ]" := (@pack T _ _ _ id _ _ id)
  (at level 0, format "[ 'tOrderType'  'of'  T ]") : form_scope.
End Exports.

End TTotal.
Import TTotal.Exports.

Module TBTotal.
Section ClassDef.

Set Primitive Projections.

Record class_of (T : Type) := Class {
  base  : BTotal.class_of T;
  mixin : TPOrder.mixin_of (POrder _ _ base);
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> BTotal.class_of.
Local Coercion base2 T (c : class_of T) : TTotal.class_of T :=
  @TTotal.Class T c (mixin c).
Local Coercion base3 T (c : class_of T) : TBDistrLattice.class_of T :=
  @TBDistrLattice.Class T c (mixin c).

Definition rel_class T (c : class_of T) :=
  @RelOrder.TBTotal.Class _ _ _ _ _ _ _ c (mixin c).

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Definition pack :=
  fun bT b & phant_id (@BTotal.class disp bT) b =>
  fun mT m & phant_id (@TPOrder.class disp mT) (TPOrder.Class m) =>
  Pack disp (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition porderType := @POrder.Pack disp cT class.
Definition bPOrderType := @BPOrder.Pack disp cT class.
Definition tPOrderType := @TPOrder.Pack disp cT class.
Definition tbPOrderType := @TBPOrder.Pack disp cT class.
Definition meetSemilatticeType := @MeetSemilattice.Pack disp cT class.
Definition bMeetSemilatticeType := @BMeetSemilattice.Pack disp cT class.
Definition tMeetSemilatticeType := @TMeetSemilattice.Pack disp cT class.
Definition tbMeetSemilatticeType := @TBMeetSemilattice.Pack disp cT class.
Definition joinSemilatticeType := @JoinSemilattice.Pack disp cT class.
Definition bJoinSemilatticeType := @BJoinSemilattice.Pack disp cT class.
Definition tJoinSemilatticeType := @TJoinSemilattice.Pack disp cT class.
Definition tbJoinSemilatticeType := @TBJoinSemilattice.Pack disp cT class.
Definition latticeType := @Lattice.Pack disp cT class.
Definition bLatticeType := @BLattice.Pack disp cT class.
Definition tLatticeType := @TLattice.Pack disp cT class.
Definition tbLatticeType := @TBLattice.Pack disp cT class.
Definition distrLatticeType := @DistrLattice.Pack disp cT class.
Definition bDistrLatticeType := @BDistrLattice.Pack disp cT class.
Definition tDistrLatticeType := @TDistrLattice.Pack disp cT class.
Definition tbDistrLatticeType := @TBDistrLattice.Pack disp cT class.
Definition orderType := @Total.Pack disp cT class.
Definition bOrderType := @BTotal.Pack disp cT class.
Definition tOrderType := @TTotal.Pack disp cT class.
Definition order_tbPOrderType := @TBPOrder.Pack disp orderType class.
Definition order_tbMeetSemilatticeType :=
  @TBMeetSemilattice.Pack disp orderType class.
Definition order_tbJoinSemilatticeType :=
  @TBJoinSemilattice.Pack disp orderType class.
Definition order_tbLatticeType := @TBLattice.Pack disp orderType class.
Definition order_tbDistrLatticeType :=
  @TBDistrLattice.Pack disp orderType class.
Definition bOrder_tPOrderType := @TPOrder.Pack disp bOrderType class.
Definition bOrder_tbPOrderType := @TBPOrder.Pack disp bOrderType class.
Definition bOrder_tMeetSemilatticeType :=
  @TMeetSemilattice.Pack disp bOrderType class.
Definition bOrder_tbMeetSemilatticeType :=
  @TBMeetSemilattice.Pack disp bOrderType class.
Definition bOrder_tJoinSemilatticeType :=
  @TJoinSemilattice.Pack disp bOrderType class.
Definition bOrder_tbJoinSemilatticeType :=
  @TBJoinSemilattice.Pack disp bOrderType class.
Definition bOrder_tLatticeType := @TLattice.Pack disp bOrderType class.
Definition bOrder_tbLatticeType := @TBLattice.Pack disp bOrderType class.
Definition bOrder_tDistrLatticeType :=
  @TDistrLattice.Pack disp bOrderType class.
Definition bOrder_tbDistrLatticeType :=
  @TBDistrLattice.Pack disp bOrderType class.
Definition tOrder_bPOrderType := @BPOrder.Pack disp tOrderType class.
Definition tOrder_tbPOrderType := @TBPOrder.Pack disp tOrderType class.
Definition tOrder_bMeetSemilatticeType :=
  @BMeetSemilattice.Pack disp tOrderType class.
Definition tOrder_tbMeetSemilatticeType :=
  @TBMeetSemilattice.Pack disp tOrderType class.
Definition tOrder_bJoinSemilatticeType :=
  @BJoinSemilattice.Pack disp tOrderType class.
Definition tOrder_tbJoinSemilatticeType :=
  @TBJoinSemilattice.Pack disp tOrderType class.
Definition tOrder_bLatticeType := @BLattice.Pack disp tOrderType class.
Definition tOrder_tbLatticeType := @TBLattice.Pack disp tOrderType class.
Definition tOrder_bDistrLatticeType :=
  @BDistrLattice.Pack disp tOrderType class.
Definition tOrder_tbDistrLatticeType :=
  @TBDistrLattice.Pack disp tOrderType class.
Definition tOrder_bOrderType := @BTotal.Pack disp tOrderType class.
End ClassDef.

Module Exports.
Coercion base : class_of >-> BTotal.class_of.
Coercion base2 : class_of >-> TTotal.class_of.
Coercion base3 : class_of >-> TBDistrLattice.class_of.
Coercion rel_class : class_of >-> RelOrder.TBTotal.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion porderType : type >-> POrder.type.
Coercion bPOrderType : type >-> BPOrder.type.
Coercion tPOrderType : type >-> TPOrder.type.
Coercion tbPOrderType : type >-> TBPOrder.type.
Coercion meetSemilatticeType : type >-> MeetSemilattice.type.
Coercion bMeetSemilatticeType : type >-> BMeetSemilattice.type.
Coercion tMeetSemilatticeType : type >-> TMeetSemilattice.type.
Coercion tbMeetSemilatticeType : type >-> TBMeetSemilattice.type.
Coercion joinSemilatticeType : type >-> JoinSemilattice.type.
Coercion bJoinSemilatticeType : type >-> BJoinSemilattice.type.
Coercion tJoinSemilatticeType : type >-> TJoinSemilattice.type.
Coercion tbJoinSemilatticeType : type >-> TBJoinSemilattice.type.
Coercion latticeType : type >-> Lattice.type.
Coercion bLatticeType : type >-> BLattice.type.
Coercion tLatticeType : type >-> TLattice.type.
Coercion tbLatticeType : type >-> TBLattice.type.
Coercion distrLatticeType : type >-> DistrLattice.type.
Coercion bDistrLatticeType : type >-> BDistrLattice.type.
Coercion tDistrLatticeType : type >-> TDistrLattice.type.
Coercion tbDistrLatticeType : type >-> TBDistrLattice.type.
Coercion orderType : type >-> Total.type.
Coercion bOrderType : type >-> BTotal.type.
Coercion tOrderType : type >-> TTotal.type.
Canonical eqType.
Canonical choiceType.
Canonical porderType.
Canonical bPOrderType.
Canonical tPOrderType.
Canonical tbPOrderType.
Canonical meetSemilatticeType.
Canonical bMeetSemilatticeType.
Canonical tMeetSemilatticeType.
Canonical tbMeetSemilatticeType.
Canonical joinSemilatticeType.
Canonical bJoinSemilatticeType.
Canonical tJoinSemilatticeType.
Canonical tbJoinSemilatticeType.
Canonical latticeType.
Canonical bLatticeType.
Canonical tLatticeType.
Canonical tbLatticeType.
Canonical distrLatticeType.
Canonical bDistrLatticeType.
Canonical tDistrLatticeType.
Canonical tbDistrLatticeType.
Canonical orderType.
Canonical bOrderType.
Canonical tOrderType.
Canonical order_tbPOrderType.
Canonical order_tbMeetSemilatticeType.
Canonical order_tbJoinSemilatticeType.
Canonical order_tbLatticeType.
Canonical order_tbDistrLatticeType.
Canonical bOrder_tPOrderType.
Canonical bOrder_tbPOrderType.
Canonical bOrder_tMeetSemilatticeType.
Canonical bOrder_tbMeetSemilatticeType.
Canonical bOrder_tJoinSemilatticeType.
Canonical bOrder_tbJoinSemilatticeType.
Canonical bOrder_tLatticeType.
Canonical bOrder_tbLatticeType.
Canonical bOrder_tDistrLatticeType.
Canonical bOrder_tbDistrLatticeType.
Canonical tOrder_bPOrderType.
Canonical tOrder_tbPOrderType.
Canonical tOrder_bMeetSemilatticeType.
Canonical tOrder_tbMeetSemilatticeType.
Canonical tOrder_bJoinSemilatticeType.
Canonical tOrder_tbJoinSemilatticeType.
Canonical tOrder_bLatticeType.
Canonical tOrder_tbLatticeType.
Canonical tOrder_bDistrLatticeType.
Canonical tOrder_tbDistrLatticeType.
Canonical tOrder_bOrderType.
Notation tbOrderType := type.
Notation "[ 'tbOrderType' 'of' T ]" := (@pack T _ _ _ id _ _ id)
  (at level 0, format "[ 'tbOrderType'  'of'  T ]") : form_scope.
End Exports.

End TBTotal.
Import TBTotal.Exports.

Module RelOrderCoercions.
Section RelOrderCoercions.
Variable (disp : unit).

Definition pOrder (T : porderType disp) : {pOrder T} :=
  POrder le lt (POrder.class T).

Definition bPOrder (T : bPOrderType disp) : {bPOrder T} :=
  @RelOrder.BPOrder.Pack _ _ le lt bottom (nosimpl (BPOrder.class T)).

Definition tPOrder (T : tPOrderType disp) : {tPOrder T} :=
  @RelOrder.TPOrder.Pack _ _ le lt top (nosimpl (TPOrder.class T)).

Definition tbPOrder (T : tbPOrderType disp) : {tbPOrder T} :=
  @RelOrder.TBPOrder.Pack _ _ le lt bottom top (nosimpl (TBPOrder.class T)).

Definition meetOrder (T : meetSemilatticeType disp) : {meetOrder T} :=
  @RelOrder.Meet.Pack _ _ le lt meet (nosimpl (MeetSemilattice.class T)).

Definition bMeetOrder (T : bMeetSemilatticeType disp) : {bMeetOrder T} :=
  @RelOrder.BMeet.Pack
    _ _ le lt meet bottom (nosimpl (BMeetSemilattice.class T)).

Definition tMeetOrder (T : tMeetSemilatticeType disp) : {tMeetOrder T} :=
  @RelOrder.TMeet.Pack _ _ le lt meet top (nosimpl (TMeetSemilattice.class T)).

Definition tbMeetOrder (T : tbMeetSemilatticeType disp) : {tbMeetOrder T} :=
  @RelOrder.TBMeet.Pack
    _ _ le lt meet bottom top (nosimpl (TBMeetSemilattice.class T)).

Definition joinOrder (T : joinSemilatticeType disp) : {joinOrder T} :=
  @RelOrder.Join.Pack _ _ le lt join (nosimpl (JoinSemilattice.class T)).

Definition bJoinOrder (T : bJoinSemilatticeType disp) : {bJoinOrder T} :=
  @RelOrder.BJoin.Pack
    _ _ le lt join bottom (nosimpl (BJoinSemilattice.class T)).

Definition tJoinOrder (T : tJoinSemilatticeType disp) : {tJoinOrder T} :=
  @RelOrder.TJoin.Pack _ _ le lt join top (nosimpl (TJoinSemilattice.class T)).

Definition tbJoinOrder (T : tbJoinSemilatticeType disp) : {tbJoinOrder T} :=
  @RelOrder.TBJoin.Pack
    _ _ le lt join bottom top (nosimpl (TBJoinSemilattice.class T)).

Definition lattice (T : latticeType disp) : {lattice T} :=
  @RelOrder.Lattice.Pack _ _ le lt meet join (nosimpl (Lattice.class T)).

Definition bLattice (T : bLatticeType disp) : {bLattice T} :=
  @RelOrder.BLattice.Pack
    _ _ le lt meet join bottom (nosimpl (BLattice.class T)).

Definition tLattice (T : tLatticeType disp) : {tLattice T} :=
  @RelOrder.TLattice.Pack _ _ le lt meet join top (nosimpl (TLattice.class T)).

Definition tbLattice (T : tbLatticeType disp) : {tbLattice T} :=
  @RelOrder.TBLattice.Pack
    _ _ le lt meet join bottom top (nosimpl (TBLattice.class T)).

Definition distrLattice (T : distrLatticeType disp) : {distrLattice T} :=
  @RelOrder.DistrLattice.Pack
    _ _ le lt meet join (nosimpl (DistrLattice.class T)).

Definition bDistrLattice (T : bDistrLatticeType disp) : {bDistrLattice T} :=
  @RelOrder.BDistrLattice.Pack
    _ _ le lt meet join bottom (nosimpl (BDistrLattice.class T)).

Definition tDistrLattice (T : tDistrLatticeType disp) : {tDistrLattice T} :=
  @RelOrder.TDistrLattice.Pack
    _ _ le lt meet join top (nosimpl (TDistrLattice.class T)).

Definition tbDistrLattice (T : tbDistrLatticeType disp) : {tbDistrLattice T} :=
  @RelOrder.TBDistrLattice.Pack
    _ _ le lt meet join bottom top (nosimpl (TBDistrLattice.class T)).

Definition totalOrder (T : orderType disp) : {totalOrder T} :=
  @RelOrder.Total.Pack _ _ le lt meet join (nosimpl (Total.class T)).

Definition bTotalOrder (T : bOrderType disp) : {bTotalOrder T} :=
  @RelOrder.BTotal.Pack _ _ le lt meet join bottom (nosimpl (BTotal.class T)).

Definition tTotalOrder (T : tOrderType disp) : {tTotalOrder T} :=
  @RelOrder.TTotal.Pack _ _ le lt meet join top (nosimpl (TTotal.class T)).

Definition tbTotalOrder (T : tbOrderType disp) : {tbTotalOrder T} :=
  @RelOrder.TBTotal.Pack
    _ _ le lt meet join bottom top (nosimpl (TBTotal.class T)).

End RelOrderCoercions.

Module Exports.

Coercion pOrder : POrder.type >-> RelOrder.POrder.order.
Coercion bPOrder : BPOrder.type >-> RelOrder.BPOrder.order.
Coercion tPOrder : TPOrder.type >-> RelOrder.TPOrder.order.
Coercion tbPOrder : TBPOrder.type >-> RelOrder.TBPOrder.order.
Coercion meetOrder : MeetSemilattice.type >-> RelOrder.Meet.order.
Coercion bMeetOrder : BMeetSemilattice.type >-> RelOrder.BMeet.order.
Coercion tMeetOrder : TMeetSemilattice.type >-> RelOrder.TMeet.order.
Coercion tbMeetOrder : TBMeetSemilattice.type >-> RelOrder.TBMeet.order.
Coercion joinOrder : JoinSemilattice.type >-> RelOrder.Join.order.
Coercion bJoinOrder : BJoinSemilattice.type >-> RelOrder.BJoin.order.
Coercion tJoinOrder : TJoinSemilattice.type >-> RelOrder.TJoin.order.
Coercion tbJoinOrder : TBJoinSemilattice.type >-> RelOrder.TBJoin.order.
Coercion lattice : Lattice.type >-> RelOrder.Lattice.order.
Coercion bLattice : BLattice.type >-> RelOrder.BLattice.order.
Coercion tLattice : TLattice.type >-> RelOrder.TLattice.order.
Coercion tbLattice : TBLattice.type >-> RelOrder.TBLattice.order.
Coercion distrLattice : DistrLattice.type >-> RelOrder.DistrLattice.order.
Coercion bDistrLattice : BDistrLattice.type >-> RelOrder.BDistrLattice.order.
Coercion tDistrLattice : TDistrLattice.type >-> RelOrder.TDistrLattice.order.
Coercion tbDistrLattice : TBDistrLattice.type >-> RelOrder.TBDistrLattice.order.
Coercion totalOrder : Total.type >-> RelOrder.Total.order.
Coercion bTotalOrder : BTotal.type >-> RelOrder.BTotal.order.
Coercion tTotalOrder : TTotal.type >-> RelOrder.TTotal.order.
Coercion tbTotalOrder : TBTotal.type >-> RelOrder.TBTotal.order.

Canonical pOrder.
Canonical bPOrder.
Canonical tPOrder.
Canonical tbPOrder.
Canonical meetOrder.
Canonical bMeetOrder.
Canonical tMeetOrder.
Canonical tbMeetOrder.
Canonical joinOrder.
Canonical bJoinOrder.
Canonical tJoinOrder.
Canonical tbJoinOrder.
Canonical lattice.
Canonical bLattice.
Canonical tLattice.
Canonical tbLattice.
Canonical distrLattice.
Canonical bDistrLattice.
Canonical tDistrLattice.
Canonical tbDistrLattice.
Canonical totalOrder.
Canonical bTotalOrder.
Canonical tTotalOrder.
Canonical tbTotalOrder.

End Exports.
End RelOrderCoercions.
Import RelOrderCoercions.Exports.

(**********)
(* FINITE *)
(**********)

Module FinPOrder.
Section ClassDef.

Set Primitive Projections.

Record class_of (T : Type) := Class {
  base  : POrder.class_of T;
  mixin : Finite.mixin_of (Equality.Pack base)
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> POrder.class_of.
Local Coercion base2 T (c : class_of T) : Finite.class_of T :=
  Finite.Class (mixin c).

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Definition pack :=
  fun bT b & phant_id (@POrder.class disp bT) b =>
  fun mT m & phant_id (@Finite.class mT) (@Finite.Class _ _ m) =>
  Pack disp (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition countType := @Countable.Pack cT class.
Definition finType := @Finite.Pack cT class.
Definition porderType := @POrder.Pack disp cT class.
Definition count_porderType := @POrder.Pack disp countType class.
Definition fin_porderType := @POrder.Pack disp finType class.
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

Module FinBPOrder.
Section ClassDef.

Set Primitive Projections.

Record class_of (T : Type) := Class {
  base  : BPOrder.class_of T;
  mixin : Finite.mixin_of (Equality.Pack base)
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> BPOrder.class_of.
Local Coercion base2 T (c : class_of T) : FinPOrder.class_of T :=
  @FinPOrder.Class T c (mixin c).

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Definition pack :=
  fun bT b & phant_id (@BPOrder.class disp bT) b =>
  fun mT m & phant_id (@Finite.class mT) (@Finite.Class _ _ m) =>
  Pack disp (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition countType := @Countable.Pack cT class.
Definition finType := @Finite.Pack cT class.
Definition porderType := @POrder.Pack disp cT class.
Definition bPOrderType := @BPOrder.Pack disp cT class.
Definition finPOrderType := @FinPOrder.Pack disp cT class.
Definition count_bPOrderType := @BPOrder.Pack disp countType class.
Definition fin_bPOrderType := @BPOrder.Pack disp finType class.
Definition finPOrder_bPOrderType := @BPOrder.Pack disp finPOrderType class.
End ClassDef.

Module Exports.
Coercion base : class_of >-> BPOrder.class_of.
Coercion base2 : class_of >-> FinPOrder.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion countType : type >-> Countable.type.
Coercion finType : type >-> Finite.type.
Coercion porderType : type >-> POrder.type.
Coercion bPOrderType : type >-> BPOrder.type.
Coercion finPOrderType : type >-> FinPOrder.type.
Canonical eqType.
Canonical choiceType.
Canonical countType.
Canonical finType.
Canonical porderType.
Canonical bPOrderType.
Canonical finPOrderType.
Canonical count_bPOrderType.
Canonical fin_bPOrderType.
Canonical finPOrder_bPOrderType.
Notation finBPOrderType := type.
Notation "[ 'finBPOrderType' 'of' T ]" := (@pack T _ _ _ id _ _ id)
  (at level 0, format "[ 'finBPOrderType'  'of'  T ]") : form_scope.
End Exports.

End FinBPOrder.
Import FinBPOrder.Exports.

Module FinTPOrder.
Section ClassDef.

Set Primitive Projections.

Record class_of (T : Type) := Class {
  base  : TPOrder.class_of T;
  mixin : Finite.mixin_of (Equality.Pack base)
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> TPOrder.class_of.
Local Coercion base2 T (c : class_of T) : FinPOrder.class_of T :=
  @FinPOrder.Class T c (mixin c).

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Definition pack :=
  fun bT b & phant_id (@TPOrder.class disp bT) b =>
  fun mT m & phant_id (@Finite.class mT) (@Finite.Class _ _ m) =>
  Pack disp (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition countType := @Countable.Pack cT class.
Definition finType := @Finite.Pack cT class.
Definition porderType := @POrder.Pack disp cT class.
Definition tPOrderType := @TPOrder.Pack disp cT class.
Definition finPOrderType := @FinPOrder.Pack disp cT class.
Definition count_tPOrderType := @TPOrder.Pack disp countType class.
Definition fin_tPOrderType := @TPOrder.Pack disp finType class.
Definition finPOrder_tPOrderType := @TPOrder.Pack disp finPOrderType class.
End ClassDef.

Module Exports.
Coercion base : class_of >-> TPOrder.class_of.
Coercion base2 : class_of >-> FinPOrder.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion countType : type >-> Countable.type.
Coercion finType : type >-> Finite.type.
Coercion porderType : type >-> POrder.type.
Coercion tPOrderType : type >-> TPOrder.type.
Coercion finPOrderType : type >-> FinPOrder.type.
Canonical eqType.
Canonical choiceType.
Canonical countType.
Canonical finType.
Canonical porderType.
Canonical tPOrderType.
Canonical finPOrderType.
Canonical count_tPOrderType.
Canonical fin_tPOrderType.
Canonical finPOrder_tPOrderType.
Notation finTPOrderType := type.
Notation "[ 'finTPOrderType' 'of' T ]" := (@pack T _ _ _ id _ _ id)
  (at level 0, format "[ 'finTPOrderType'  'of'  T ]") : form_scope.
End Exports.

End FinTPOrder.
Import FinTPOrder.Exports.

Module FinTBPOrder.
Section ClassDef.

Set Primitive Projections.

Record class_of (T : Type) := Class {
  base  : TBPOrder.class_of T;
  mixin : Finite.mixin_of (Equality.Pack base)
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> TBPOrder.class_of.
Local Coercion base2 T (c : class_of T) : FinBPOrder.class_of T :=
  @FinBPOrder.Class T c (mixin c).
Local Coercion base3 T (c : class_of T) : FinTPOrder.class_of T :=
  @FinTPOrder.Class T c (mixin c).

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Definition pack :=
  fun bT b & phant_id (@TBPOrder.class disp bT) b =>
  fun mT m & phant_id (@Finite.class mT) (@Finite.Class _ _ m) =>
  Pack disp (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition countType := @Countable.Pack cT class.
Definition finType := @Finite.Pack cT class.
Definition porderType := @POrder.Pack disp cT class.
Definition bPOrderType := @BPOrder.Pack disp cT class.
Definition tPOrderType := @TPOrder.Pack disp cT class.
Definition tbPOrderType := @TBPOrder.Pack disp cT class.
Definition finPOrderType := @FinPOrder.Pack disp cT class.
Definition finBPOrderType := @FinBPOrder.Pack disp cT class.
Definition finTPOrderType := @FinTPOrder.Pack disp cT class.
Definition count_tbPOrderType := @TBPOrder.Pack disp countType class.
Definition fin_tbPOrderType := @TBPOrder.Pack disp finType class.
Definition finPOrder_tbPOrderType := @TBPOrder.Pack disp finPOrderType class.
Definition finBPOrder_tPOrderType := @TPOrder.Pack disp finBPOrderType class.
Definition finBPOrder_tbPOrderType := @TBPOrder.Pack disp finBPOrderType class.
Definition finTPOrder_bPOrderType := @BPOrder.Pack disp finTPOrderType class.
Definition finTPOrder_tbPOrderType := @TBPOrder.Pack disp finTPOrderType class.
Definition finBPOrder_finTPOrderType :=
  @FinTPOrder.Pack disp finBPOrderType class.
End ClassDef.

Module Exports.
Coercion base : class_of >-> TBPOrder.class_of.
Coercion base2 : class_of >-> FinBPOrder.class_of.
Coercion base3 : class_of >-> FinTPOrder.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion countType : type >-> Countable.type.
Coercion finType : type >-> Finite.type.
Coercion porderType : type >-> POrder.type.
Coercion bPOrderType : type >-> BPOrder.type.
Coercion tPOrderType : type >-> TPOrder.type.
Coercion tbPOrderType : type >-> TBPOrder.type.
Coercion finPOrderType : type >-> FinPOrder.type.
Coercion finBPOrderType : type >-> FinBPOrder.type.
Coercion finTPOrderType : type >-> FinTPOrder.type.
Canonical eqType.
Canonical choiceType.
Canonical countType.
Canonical finType.
Canonical porderType.
Canonical bPOrderType.
Canonical tPOrderType.
Canonical tbPOrderType.
Canonical finPOrderType.
Canonical finBPOrderType.
Canonical finTPOrderType.
Canonical count_tbPOrderType.
Canonical fin_tbPOrderType.
Canonical finPOrder_tbPOrderType.
Canonical finBPOrder_tPOrderType.
Canonical finBPOrder_tbPOrderType.
Canonical finTPOrder_bPOrderType.
Canonical finTPOrder_tbPOrderType.
Canonical finBPOrder_finTPOrderType.
Notation finTBPOrderType := type.
Notation "[ 'finTBPOrderType' 'of' T ]" := (@pack T _ _ _ id _ _ id)
  (at level 0, format "[ 'finTBPOrderType'  'of'  T ]") : form_scope.
End Exports.

End FinTBPOrder.
Import FinTBPOrder.Exports.

Module FinMeetSemilattice.
Section ClassDef.

Set Primitive Projections.

Record class_of (T : Type) := Class {
  base : MeetSemilattice.class_of T;
  mixin : Finite.mixin_of (Equality.Pack base);
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> MeetSemilattice.class_of.
Local Coercion base2 T (c : class_of T) : FinPOrder.class_of T :=
  @FinPOrder.Class T c (mixin c).

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Definition pack :=
  fun bT b & phant_id (@MeetSemilattice.class disp bT) b =>
  fun mT m & phant_id (@Finite.class mT) (@Finite.Class _ _ m) =>
  Pack disp (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition countType := @Countable.Pack cT class.
Definition finType := @Finite.Pack cT class.
Definition porderType := @POrder.Pack disp cT class.
Definition finPOrderType := @FinPOrder.Pack disp cT class.
Definition meetSemilatticeType := @MeetSemilattice.Pack disp cT class.
Definition count_meetSemilatticeType :=
  @MeetSemilattice.Pack disp countType class.
Definition fin_meetSemilatticeType := @MeetSemilattice.Pack disp finType class.
Definition finPOrder_meetSemilatticeType :=
  @MeetSemilattice.Pack disp finPOrderType class.
End ClassDef.

Module Exports.
Coercion base : class_of >-> MeetSemilattice.class_of.
Coercion base2 : class_of >-> FinPOrder.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion countType : type >-> Countable.type.
Coercion finType : type >-> Finite.type.
Coercion porderType : type >-> POrder.type.
Coercion finPOrderType : type >-> FinPOrder.type.
Coercion meetSemilatticeType : type >-> MeetSemilattice.type.
Canonical eqType.
Canonical choiceType.
Canonical countType.
Canonical finType.
Canonical porderType.
Canonical finPOrderType.
Canonical meetSemilatticeType.
Canonical count_meetSemilatticeType.
Canonical fin_meetSemilatticeType.
Canonical finPOrder_meetSemilatticeType.
Notation finMeetSemilatticeType := type.
Notation "[ 'finMeetSemilatticeType' 'of' T ]" := (@pack T _ _ _ id _ _ id)
  (at level 0, format "[ 'finMeetSemilatticeType'  'of'  T ]") : form_scope.
End Exports.

End FinMeetSemilattice.
Import FinMeetSemilattice.Exports.

Module FinBMeetSemilattice.
Section ClassDef.

Set Primitive Projections.

Record class_of (T : Type) := Class {
  base : BMeetSemilattice.class_of T;
  mixin : Finite.mixin_of (Equality.Pack base);
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> BMeetSemilattice.class_of.
Local Coercion base2 T (c : class_of T) : FinMeetSemilattice.class_of T :=
  @FinMeetSemilattice.Class T c (mixin c).
Local Coercion base3 T (c : class_of T) : FinBPOrder.class_of T :=
  @FinBPOrder.Class T c (mixin c).

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Definition pack :=
  fun bT b & phant_id (@BMeetSemilattice.class disp bT) b =>
  fun mT m & phant_id (@Finite.class mT) (@Finite.Class _ _ m) =>
  Pack disp (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition countType := @Countable.Pack cT class.
Definition finType := @Finite.Pack cT class.
Definition porderType := @POrder.Pack disp cT class.
Definition bPorderType := @BPOrder.Pack disp cT class.
Definition finPOrderType := @FinPOrder.Pack disp cT class.
Definition finBPOrderType := @FinBPOrder.Pack disp cT class.
Definition meetSemilatticeType := @MeetSemilattice.Pack disp cT class.
Definition bMeetSemilatticeType := @BMeetSemilattice.Pack disp cT class.
Definition finMeetSemilatticeType := @FinMeetSemilattice.Pack disp cT class.
Definition count_bMeetSemilatticeType :=
  @BMeetSemilattice.Pack disp countType class.
Definition fin_bMeetSemilatticeType :=
  @BMeetSemilattice.Pack disp finType class.
Definition finPOrder_bMeetSemilatticeType :=
  @BMeetSemilattice.Pack disp finPOrderType class.
Definition finBPOrder_meetSemilatticeType :=
  @MeetSemilattice.Pack disp finBPOrderType class.
Definition finBPOrder_bMeetSemilatticeType :=
  @BMeetSemilattice.Pack disp finBPOrderType class.
Definition finMeetSemilattice_bPOrderType :=
  @BPOrder.Pack disp finMeetSemilatticeType class.
Definition finMeetSemilattice_finBPOrderType :=
  @FinBPOrder.Pack disp finMeetSemilatticeType class.
Definition finMeetSemilattice_bMeetSemilatticeType :=
  @BMeetSemilattice.Pack disp finMeetSemilatticeType class.
End ClassDef.

Module Exports.
Coercion base : class_of >-> BMeetSemilattice.class_of.
Coercion base2 : class_of >-> FinMeetSemilattice.class_of.
Coercion base3 : class_of >-> FinBPOrder.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion countType : type >-> Countable.type.
Coercion finType : type >-> Finite.type.
Coercion porderType : type >-> POrder.type.
Coercion bPorderType : type >-> BPOrder.type.
Coercion finPOrderType : type >-> FinPOrder.type.
Coercion finBPOrderType : type >-> FinBPOrder.type.
Coercion meetSemilatticeType : type >-> MeetSemilattice.type.
Coercion bMeetSemilatticeType : type >-> BMeetSemilattice.type.
Coercion finMeetSemilatticeType : type >-> FinMeetSemilattice.type.
Canonical eqType.
Canonical choiceType.
Canonical countType.
Canonical finType.
Canonical porderType.
Canonical bPorderType.
Canonical finPOrderType.
Canonical finBPOrderType.
Canonical meetSemilatticeType.
Canonical bMeetSemilatticeType.
Canonical finMeetSemilatticeType.
Canonical count_bMeetSemilatticeType.
Canonical fin_bMeetSemilatticeType.
Canonical finPOrder_bMeetSemilatticeType.
Canonical finBPOrder_meetSemilatticeType.
Canonical finBPOrder_bMeetSemilatticeType.
Canonical finMeetSemilattice_bPOrderType.
Canonical finMeetSemilattice_finBPOrderType.
Canonical finMeetSemilattice_bMeetSemilatticeType.
Notation finBMeetSemilatticeType := type.
Notation "[ 'finBMeetSemilatticeType' 'of' T ]" := (@pack T _ _ _ id _ _ id)
  (at level 0, format "[ 'finBMeetSemilatticeType'  'of'  T ]") : form_scope.
End Exports.

End FinBMeetSemilattice.
Import FinBMeetSemilattice.Exports.

Module FinJoinSemilattice.
Section ClassDef.

Set Primitive Projections.

Record class_of (T : Type) := Class {
  base : JoinSemilattice.class_of T;
  mixin : Finite.mixin_of (Equality.Pack base);
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> JoinSemilattice.class_of.
Local Coercion base2 T (c : class_of T) : FinPOrder.class_of T :=
  @FinPOrder.Class T c (mixin c).

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Definition pack :=
  fun bT b & phant_id (@JoinSemilattice.class disp bT) b =>
  fun mT m & phant_id (@Finite.class mT) (@Finite.Class _ _ m) =>
  Pack disp (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition countType := @Countable.Pack cT class.
Definition finType := @Finite.Pack cT class.
Definition porderType := @POrder.Pack disp cT class.
Definition finPOrderType := @FinPOrder.Pack disp cT class.
Definition joinSemilatticeType := @JoinSemilattice.Pack disp cT class.
Definition count_joinSemilatticeType :=
  @JoinSemilattice.Pack disp countType class.
Definition fin_joinSemilatticeType := @JoinSemilattice.Pack disp finType class.
Definition finPOrder_joinSemilatticeType :=
  @JoinSemilattice.Pack disp finPOrderType class.
End ClassDef.

Module Exports.
Coercion base : class_of >-> JoinSemilattice.class_of.
Coercion base2 : class_of >-> FinPOrder.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion countType : type >-> Countable.type.
Coercion finType : type >-> Finite.type.
Coercion porderType : type >-> POrder.type.
Coercion finPOrderType : type >-> FinPOrder.type.
Coercion joinSemilatticeType : type >-> JoinSemilattice.type.
Canonical eqType.
Canonical choiceType.
Canonical countType.
Canonical finType.
Canonical porderType.
Canonical finPOrderType.
Canonical joinSemilatticeType.
Canonical count_joinSemilatticeType.
Canonical fin_joinSemilatticeType.
Canonical finPOrder_joinSemilatticeType.
Notation finJoinSemilatticeType := type.
Notation "[ 'finJoinSemilatticeType' 'of' T ]" := (@pack T _ _ _ id _ _ id)
  (at level 0, format "[ 'finJoinSemilatticeType'  'of'  T ]") : form_scope.
End Exports.

End FinJoinSemilattice.
Import FinJoinSemilattice.Exports.

Module FinTJoinSemilattice.
Section ClassDef.

Set Primitive Projections.

Record class_of (T : Type) := Class {
  base : TJoinSemilattice.class_of T;
  mixin : Finite.mixin_of (Equality.Pack base);
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> TJoinSemilattice.class_of.
Local Coercion base2 T (c : class_of T) : FinJoinSemilattice.class_of T :=
  @FinJoinSemilattice.Class T c (mixin c).
Local Coercion base3 T (c : class_of T) : FinTPOrder.class_of T :=
  @FinTPOrder.Class T c (mixin c).

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Definition pack :=
  fun bT b & phant_id (@TJoinSemilattice.class disp bT) b =>
  fun mT m & phant_id (@Finite.class mT) (@Finite.Class _ _ m) =>
  Pack disp (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition countType := @Countable.Pack cT class.
Definition finType := @Finite.Pack cT class.
Definition porderType := @POrder.Pack disp cT class.
Definition tPOrderType := @TPOrder.Pack disp cT class.
Definition finPOrderType := @FinPOrder.Pack disp cT class.
Definition finTPOrderType := @FinTPOrder.Pack disp cT class.
Definition joinSemilatticeType := @JoinSemilattice.Pack disp cT class.
Definition tJoinSemilatticeType := @TJoinSemilattice.Pack disp cT class.
Definition finJoinSemilatticeType := @FinJoinSemilattice.Pack disp cT class.
Definition count_tJoinSemilatticeType :=
  @TJoinSemilattice.Pack disp countType class.
Definition fin_tJoinSemilatticeType :=
  @TJoinSemilattice.Pack disp finType class.
Definition finPOrder_tJoinSemilatticeType :=
  @TJoinSemilattice.Pack disp finPOrderType class.
Definition finTPOrder_joinSemilatticeType :=
  @JoinSemilattice.Pack disp finTPOrderType class.
Definition finTPOrder_tJoinSemilatticeType :=
  @TJoinSemilattice.Pack disp finTPOrderType class.
Definition finJoinSemilattice_tPOrderType :=
  @TPOrder.Pack disp finJoinSemilatticeType class.
Definition finJoinSemilattice_finTPOrderType :=
  @FinTPOrder.Pack disp finJoinSemilatticeType class.
Definition finJoinSemilattice_tJoinSemilatticeType :=
  @TJoinSemilattice.Pack disp finJoinSemilatticeType class.
End ClassDef.

Module Exports.
Coercion base : class_of >-> TJoinSemilattice.class_of.
Coercion base2 : class_of >-> FinJoinSemilattice.class_of.
Coercion base3 : class_of >-> FinTPOrder.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion countType : type >-> Countable.type.
Coercion finType : type >-> Finite.type.
Coercion porderType : type >-> POrder.type.
Coercion tPOrderType : type >-> TPOrder.type.
Coercion finPOrderType : type >-> FinPOrder.type.
Coercion finTPOrderType : type >-> FinTPOrder.type.
Coercion joinSemilatticeType : type >-> JoinSemilattice.type.
Coercion tJoinSemilatticeType : type >-> TJoinSemilattice.type.
Coercion finJoinSemilatticeType : type >-> FinJoinSemilattice.type.
Canonical eqType.
Canonical choiceType.
Canonical countType.
Canonical finType.
Canonical porderType.
Canonical tPOrderType.
Canonical finPOrderType.
Canonical finTPOrderType.
Canonical joinSemilatticeType.
Canonical tJoinSemilatticeType.
Canonical finJoinSemilatticeType.
Canonical count_tJoinSemilatticeType.
Canonical fin_tJoinSemilatticeType.
Canonical finPOrder_tJoinSemilatticeType.
Canonical finTPOrder_joinSemilatticeType.
Canonical finTPOrder_tJoinSemilatticeType.
Canonical finJoinSemilattice_tPOrderType.
Canonical finJoinSemilattice_finTPOrderType.
Canonical finJoinSemilattice_tJoinSemilatticeType.
Notation finTJoinSemilatticeType := type.
Notation "[ 'finTJoinSemilatticeType' 'of' T ]" := (@pack T _ _ _ id _ _ id)
  (at level 0, format "[ 'finTJoinSemilatticeType'  'of'  T ]") : form_scope.
End Exports.

End FinTJoinSemilattice.
Import FinTJoinSemilattice.Exports.

Module FinLattice.
Section ClassDef.

Set Primitive Projections.

Record class_of (T : Type) := Class {
  base : Lattice.class_of T;
  mixin : Finite.mixin_of (Equality.Pack base);
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> Lattice.class_of.
Local Coercion base2 T (c : class_of T) : FinMeetSemilattice.class_of T :=
  @FinMeetSemilattice.Class T c (mixin c).
Local Coercion base3 T (c : class_of T) : FinJoinSemilattice.class_of T :=
  @FinJoinSemilattice.Class T c (mixin c).

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Definition pack :=
  fun bT b & phant_id (@Lattice.class disp bT) b =>
  fun mT m & phant_id (@Finite.class mT) (@Finite.Class _ _ m) =>
  Pack disp (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition countType := @Countable.Pack cT class.
Definition finType := @Finite.Pack cT class.
Definition porderType := @POrder.Pack disp cT class.
Definition finPOrderType := @FinPOrder.Pack disp cT class.
Definition meetSemilatticeType := @MeetSemilattice.Pack disp cT class.
Definition finMeetSemilatticeType := @FinMeetSemilattice.Pack disp cT class.
Definition joinSemilatticeType := @JoinSemilattice.Pack disp cT class.
Definition finJoinSemilatticeType := @FinJoinSemilattice.Pack disp cT class.
Definition latticeType := @Lattice.Pack disp cT class.
Definition count_latticeType := @Lattice.Pack disp countType class.
Definition fin_latticeType := @Lattice.Pack disp finType class.
Definition finPOrder_latticeType := @Lattice.Pack disp finPOrderType class.
Definition finMeetSemilattice_joinSemilatticeType :=
  @JoinSemilattice.Pack disp finMeetSemilatticeType class.
Definition finMeetSemilattice_latticeType :=
  @Lattice.Pack disp finMeetSemilatticeType class.
Definition finJoinSemilattice_meetSemilatticeType :=
  @MeetSemilattice.Pack disp finJoinSemilatticeType class.
Definition finJoinSemilattice_latticeType :=
  @Lattice.Pack disp finJoinSemilatticeType class.
Definition finJoinSemilattice_finMeetSemilatticeType :=
  @FinMeetSemilattice.Pack disp finJoinSemilatticeType class.
End ClassDef.

Module Exports.
Coercion base : class_of >-> Lattice.class_of.
Coercion base2 : class_of >-> FinMeetSemilattice.class_of.
Coercion base3 : class_of >-> FinJoinSemilattice.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion countType : type >-> Countable.type.
Coercion finType : type >-> Finite.type.
Coercion porderType : type >-> POrder.type.
Coercion finPOrderType : type >-> FinPOrder.type.
Coercion meetSemilatticeType : type >-> MeetSemilattice.type.
Coercion finMeetSemilatticeType : type >-> FinMeetSemilattice.type.
Coercion joinSemilatticeType : type >-> JoinSemilattice.type.
Coercion finJoinSemilatticeType : type >-> FinJoinSemilattice.type.
Coercion latticeType : type >-> Lattice.type.
Canonical eqType.
Canonical choiceType.
Canonical countType.
Canonical finType.
Canonical porderType.
Canonical finPOrderType.
Canonical meetSemilatticeType.
Canonical finMeetSemilatticeType.
Canonical joinSemilatticeType.
Canonical finJoinSemilatticeType.
Canonical latticeType.
Canonical count_latticeType.
Canonical fin_latticeType.
Canonical finPOrder_latticeType.
Canonical finMeetSemilattice_joinSemilatticeType.
Canonical finMeetSemilattice_latticeType.
Canonical finJoinSemilattice_meetSemilatticeType.
Canonical finJoinSemilattice_latticeType.
Canonical finJoinSemilattice_finMeetSemilatticeType.
Notation finLatticeType := type.
Notation "[ 'finLatticeType' 'of' T ]" := (@pack T _ _ _ id _ _ id)
  (at level 0, format "[ 'finLatticeType'  'of'  T ]") : form_scope.
End Exports.

End FinLattice.
Import FinLattice.Exports.

Module FinTBLattice.
Section ClassDef.

Set Primitive Projections.

Record class_of (T : Type) := Class {
  base : TBLattice.class_of T;
  mixin : Finite.mixin_of (Equality.Pack base);
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> TBLattice.class_of.
Local Coercion base2 T (c : class_of T) : FinTBPOrder.class_of T :=
  @FinTBPOrder.Class T c (mixin c).
Local Coercion base3 T (c : class_of T) : FinLattice.class_of T :=
  @FinLattice.Class T c (mixin c).
Local Coercion base4 T (c : class_of T) : FinBMeetSemilattice.class_of T :=
  @FinBMeetSemilattice.Class T c (mixin c).
Local Coercion base5 T (c : class_of T) : FinTJoinSemilattice.class_of T :=
  @FinTJoinSemilattice.Class T c (mixin c).

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Definition pack :=
  fun bT b & phant_id (@TBLattice.class disp bT) b =>
  fun mT m & phant_id (@Finite.class mT) (@Finite.Class _ _ m) =>
  Pack disp (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition countType := @Countable.Pack cT class.
Definition finType := @Finite.Pack cT class.
Definition porderType := @POrder.Pack disp cT class.
Definition bPOrderType := @BPOrder.Pack disp cT class.
Definition tPOrderType := @TPOrder.Pack disp cT class.
Definition tbPOrderType := @TBPOrder.Pack disp cT class.
Definition finPOrderType := @FinPOrder.Pack disp cT class.
Definition finBPOrderType := @FinBPOrder.Pack disp cT class.
Definition finTPOrderType := @FinTPOrder.Pack disp cT class.
Definition finTBPOrderType := @FinTBPOrder.Pack disp cT class.
Definition meetSemilatticeType := @MeetSemilattice.Pack disp cT class.
Definition bMeetSemilatticeType := @BMeetSemilattice.Pack disp cT class.
Definition tMeetSemilatticeType := @TMeetSemilattice.Pack disp cT class.
Definition tbMeetSemilatticeType := @TBMeetSemilattice.Pack disp cT class.
Definition finMeetSemilatticeType := @FinMeetSemilattice.Pack disp cT class.
Definition finBMeetSemilatticeType := @FinBMeetSemilattice.Pack disp cT class.
Definition joinSemilatticeType := @JoinSemilattice.Pack disp cT class.
Definition bJoinSemilatticeType := @BJoinSemilattice.Pack disp cT class.
Definition tJoinSemilatticeType := @TJoinSemilattice.Pack disp cT class.
Definition tbJoinSemilatticeType := @TBJoinSemilattice.Pack disp cT class.
Definition finJoinSemilatticeType := @FinJoinSemilattice.Pack disp cT class.
Definition finTJoinSemilatticeType := @FinTJoinSemilattice.Pack disp cT class.
Definition latticeType := @Lattice.Pack disp cT class.
Definition bLatticeType := @BLattice.Pack disp cT class.
Definition tLatticeType := @TLattice.Pack disp cT class.
Definition tbLatticeType := @TBLattice.Pack disp cT class.
Definition finLatticeType := @FinLattice.Pack disp cT class.
Definition count_tMeetSemilatticeType :=
  @TMeetSemilattice.Pack disp countType class.
Definition count_tbMeetSemilatticeType :=
  @TBMeetSemilattice.Pack disp countType class.
Definition count_bJoinSemilatticeType :=
  @BJoinSemilattice.Pack disp countType class.
Definition count_tbJoinSemilatticeType :=
  @TBJoinSemilattice.Pack disp countType class.
Definition count_bLatticeType := @BLattice.Pack disp countType class.
Definition count_tLatticeType := @TLattice.Pack disp countType class.
Definition count_tbLatticeType := @TBLattice.Pack disp countType class.
Definition fin_tMeetSemilatticeType :=
  @TMeetSemilattice.Pack disp finType class.
Definition fin_tbMeetSemilatticeType :=
  @TBMeetSemilattice.Pack disp finType class.
Definition fin_bJoinSemilatticeType :=
  @BJoinSemilattice.Pack disp finType class.
Definition fin_tbJoinSemilatticeType :=
  @TBJoinSemilattice.Pack disp finType class.
Definition fin_bLatticeType := @BLattice.Pack disp finType class.
Definition fin_tLatticeType := @TLattice.Pack disp finType class.
Definition fin_tbLatticeType := @TBLattice.Pack disp finType class.
Definition finPOrder_tMeetSemilatticeType :=
  @TMeetSemilattice.Pack disp finPOrderType class.
Definition finPOrder_tbMeetSemilatticeType :=
  @TBMeetSemilattice.Pack disp finPOrderType class.
Definition finPOrder_bJoinSemilatticeType :=
  @BJoinSemilattice.Pack disp finPOrderType class.
Definition finPOrder_tbJoinSemilatticeType :=
  @TBJoinSemilattice.Pack disp finPOrderType class.
Definition finPOrder_bLatticeType := @BLattice.Pack disp finPOrderType class.
Definition finPOrder_tLatticeType := @TLattice.Pack disp finPOrderType class.
Definition finPOrder_tbLatticeType := @TBLattice.Pack disp finPOrderType class.
Definition finBPOrder_tMeetSemilatticeType :=
  @TMeetSemilattice.Pack disp finBPOrderType class.
Definition finBPOrder_tbMeetSemilatticeType :=
  @TBMeetSemilattice.Pack disp finBPOrderType class.
Definition finBPOrder_joinSemilatticeType :=
  @JoinSemilattice.Pack disp finBPOrderType class.
Definition finBPOrder_bJoinSemilatticeType :=
  @BJoinSemilattice.Pack disp finBPOrderType class.
Definition finBPOrder_tJoinSemilatticeType :=
  @TJoinSemilattice.Pack disp finBPOrderType class.
Definition finBPOrder_tbJoinSemilatticeType :=
  @TBJoinSemilattice.Pack disp finBPOrderType class.
Definition finBPOrder_latticeType := @Lattice.Pack disp finBPOrderType class.
Definition finBPOrder_bLatticeType := @BLattice.Pack disp finBPOrderType class.
Definition finBPOrder_tLatticeType := @TLattice.Pack disp finBPOrderType class.
Definition finBPOrder_tbLatticeType :=
  @TBLattice.Pack disp finBPOrderType class.
Definition finTPOrder_meetSemilatticeType :=
  @MeetSemilattice.Pack disp finTPOrderType class.
Definition finTPOrder_bMeetSemilatticeType :=
  @BMeetSemilattice.Pack disp finTPOrderType class.
Definition finTPOrder_tMeetSemilatticeType :=
  @TMeetSemilattice.Pack disp finTPOrderType class.
Definition finTPOrder_tbMeetSemilatticeType :=
  @TBMeetSemilattice.Pack disp finTPOrderType class.
Definition finTPOrder_bJoinSemilatticeType :=
  @BJoinSemilattice.Pack disp finTPOrderType class.
Definition finTPOrder_tbJoinSemilatticeType :=
  @TBJoinSemilattice.Pack disp finTPOrderType class.
Definition finTPOrder_latticeType := @Lattice.Pack disp finTPOrderType class.
Definition finTPOrder_bLatticeType := @BLattice.Pack disp finTPOrderType class.
Definition finTPOrder_tLatticeType := @TLattice.Pack disp finTPOrderType class.
Definition finTPOrder_tbLatticeType :=
  @TBLattice.Pack disp finTPOrderType class.
Definition finTBPOrder_meetSemilatticeType :=
  @MeetSemilattice.Pack disp finTBPOrderType class.
Definition finTBPOrder_bMeetSemilatticeType :=
  @BMeetSemilattice.Pack disp finTBPOrderType class.
Definition finTBPOrder_tMeetSemilatticeType :=
  @TMeetSemilattice.Pack disp finTBPOrderType class.
Definition finTBPOrder_tbMeetSemilatticeType :=
  @TBMeetSemilattice.Pack disp finTBPOrderType class.
Definition finTBPOrder_joinSemilatticeType :=
  @JoinSemilattice.Pack disp finTBPOrderType class.
Definition finTBPOrder_bJoinSemilatticeType :=
  @BJoinSemilattice.Pack disp finTBPOrderType class.
Definition finTBPOrder_tJoinSemilatticeType :=
  @TJoinSemilattice.Pack disp finTBPOrderType class.
Definition finTBPOrder_tbJoinSemilatticeType :=
  @TBJoinSemilattice.Pack disp finTBPOrderType class.
Definition finTBPOrder_latticeType := @Lattice.Pack disp finTBPOrderType class.
Definition finTBPOrder_bLatticeType :=
  @BLattice.Pack disp finTBPOrderType class.
Definition finTBPOrder_tLatticeType :=
  @TLattice.Pack disp finTBPOrderType class.
Definition finTBPOrder_tbLatticeType :=
  @TBLattice.Pack disp finTBPOrderType class.
Definition finMeetSemilattice_tPOrderType :=
  @TPOrder.Pack disp finMeetSemilatticeType class.
Definition finMeetSemilattice_tbPOrderType :=
  @TBPOrder.Pack disp finMeetSemilatticeType class.
Definition finMeetSemilattice_finTPOrderType :=
  @FinTPOrder.Pack disp finMeetSemilatticeType class.
Definition finMeetSemilattice_finTBPOrderType :=
  @FinTBPOrder.Pack disp finMeetSemilatticeType class.
Definition finMeetSemilattice_tMeetSemilatticeType :=
  @TMeetSemilattice.Pack disp finMeetSemilatticeType class.
Definition finMeetSemilattice_tbMeetSemilatticeType :=
  @TBMeetSemilattice.Pack disp finMeetSemilatticeType class.
Definition finMeetSemilattice_bJoinSemilatticeType :=
  @BJoinSemilattice.Pack disp finMeetSemilatticeType class.
Definition finMeetSemilattice_tJoinSemilatticeType :=
  @TJoinSemilattice.Pack disp finMeetSemilatticeType class.
Definition finMeetSemilattice_tbJoinSemilatticeType :=
  @TBJoinSemilattice.Pack disp finMeetSemilatticeType class.
Definition finMeetSemilattice_bLatticeType :=
  @BLattice.Pack disp finMeetSemilatticeType class.
Definition finMeetSemilattice_tLatticeType :=
  @TLattice.Pack disp finMeetSemilatticeType class.
Definition finMeetSemilattice_tbLatticeType :=
  @TBLattice.Pack disp finMeetSemilatticeType class.
Definition finBMeetSemilattice_tPOrderType :=
  @TPOrder.Pack disp finBMeetSemilatticeType class.
Definition finBMeetSemilattice_tbPOrderType :=
  @TBPOrder.Pack disp finBMeetSemilatticeType class.
Definition finBMeetSemilattice_finTPOrderType :=
  @FinTPOrder.Pack disp finBMeetSemilatticeType class.
Definition finBMeetSemilattice_finTBPOrderType :=
  @FinTBPOrder.Pack disp finBMeetSemilatticeType class.
Definition finBMeetSemilattice_tMeetSemilatticeType :=
  @TMeetSemilattice.Pack disp finBMeetSemilatticeType class.
Definition finBMeetSemilattice_tbMeetSemilatticeType :=
  @TBMeetSemilattice.Pack disp finBMeetSemilatticeType class.
Definition finBMeetSemilattice_joinSemilatticeType :=
  @JoinSemilattice.Pack disp finBMeetSemilatticeType class.
Definition finBMeetSemilattice_bJoinSemilatticeType :=
  @BJoinSemilattice.Pack disp finBMeetSemilatticeType class.
Definition finBMeetSemilattice_tJoinSemilatticeType :=
  @TJoinSemilattice.Pack disp finBMeetSemilatticeType class.
Definition finBMeetSemilattice_tbJoinSemilatticeType :=
  @TBJoinSemilattice.Pack disp finBMeetSemilatticeType class.
Definition finBMeetSemilattice_latticeType :=
  @Lattice.Pack disp finBMeetSemilatticeType class.
Definition finBMeetSemilattice_bLatticeType :=
  @BLattice.Pack disp finBMeetSemilatticeType class.
Definition finBMeetSemilattice_tLatticeType :=
  @TLattice.Pack disp finBMeetSemilatticeType class.
Definition finBMeetSemilattice_tbLatticeType :=
  @TBLattice.Pack disp finBMeetSemilatticeType class.
Definition finJoinSemilattice_bPOrderType :=
  @BPOrder.Pack disp finJoinSemilatticeType class.
Definition finJoinSemilattice_tbPOrderType :=
  @TBPOrder.Pack disp finJoinSemilatticeType class.
Definition finJoinSemilattice_finBPOrderType :=
  @FinBPOrder.Pack disp finJoinSemilatticeType class.
Definition finJoinSemilattice_finTBPOrderType :=
  @FinTBPOrder.Pack disp finJoinSemilatticeType class.
Definition finJoinSemilattice_bMeetSemilatticeType :=
  @BMeetSemilattice.Pack disp finJoinSemilatticeType class.
Definition finJoinSemilattice_tMeetSemilatticeType :=
  @TMeetSemilattice.Pack disp finJoinSemilatticeType class.
Definition finJoinSemilattice_tbMeetSemilatticeType :=
  @TBMeetSemilattice.Pack disp finJoinSemilatticeType class.
Definition finJoinSemilattice_finBMeetSemilatticeType :=
  @FinBMeetSemilattice.Pack disp finJoinSemilatticeType class.
Definition finJoinSemilattice_bJoinSemilatticeType :=
  @BJoinSemilattice.Pack disp finJoinSemilatticeType class.
Definition finJoinSemilattice_tbJoinSemilatticeType :=
  @TBJoinSemilattice.Pack disp finJoinSemilatticeType class.
Definition finJoinSemilattice_bLatticeType :=
  @BLattice.Pack disp finJoinSemilatticeType class.
Definition finJoinSemilattice_tLatticeType :=
  @TLattice.Pack disp finJoinSemilatticeType class.
Definition finJoinSemilattice_tbLatticeType :=
  @TBLattice.Pack disp finJoinSemilatticeType class.
Definition finTJoinSemilattice_bPOrderType :=
  @BPOrder.Pack disp finTJoinSemilatticeType class.
Definition finTJoinSemilattice_tbPOrderType :=
  @TBPOrder.Pack disp finTJoinSemilatticeType class.
Definition finTJoinSemilattice_finBPOrderType :=
  @FinBPOrder.Pack disp finTJoinSemilatticeType class.
Definition finTJoinSemilattice_finTBPOrderType :=
  @FinTBPOrder.Pack disp finTJoinSemilatticeType class.
Definition finTJoinSemilattice_meetSemilatticeType :=
  @MeetSemilattice.Pack disp finTJoinSemilatticeType class.
Definition finTJoinSemilattice_bMeetSemilatticeType :=
  @BMeetSemilattice.Pack disp finTJoinSemilatticeType class.
Definition finTJoinSemilattice_tMeetSemilatticeType :=
  @TMeetSemilattice.Pack disp finTJoinSemilatticeType class.
Definition finTJoinSemilattice_tbMeetSemilatticeType :=
  @TBMeetSemilattice.Pack disp finTJoinSemilatticeType class.
Definition finTJoinSemilattice_finMeetSemilatticeType :=
  @FinMeetSemilattice.Pack disp finTJoinSemilatticeType class.
Definition finTJoinSemilattice_finBMeetSemilatticeType :=
  @FinBMeetSemilattice.Pack disp finTJoinSemilatticeType class.
Definition finTJoinSemilattice_bJoinSemilatticeType :=
  @BJoinSemilattice.Pack disp finTJoinSemilatticeType class.
Definition finTJoinSemilattice_tbJoinSemilatticeType :=
  @TBJoinSemilattice.Pack disp finTJoinSemilatticeType class.
Definition finTJoinSemilattice_latticeType :=
  @Lattice.Pack disp finTJoinSemilatticeType class.
Definition finTJoinSemilattice_bLatticeType :=
  @BLattice.Pack disp finTJoinSemilatticeType class.
Definition finTJoinSemilattice_tLatticeType :=
  @TLattice.Pack disp finTJoinSemilatticeType class.
Definition finTJoinSemilattice_tbLatticeType :=
  @TBLattice.Pack disp finTJoinSemilatticeType class.
Definition finLattice_bPOrderType := @BPOrder.Pack disp finLatticeType class.
Definition finLattice_tPOrderType := @TPOrder.Pack disp finLatticeType class.
Definition finLattice_tbPOrderType := @TBPOrder.Pack disp finLatticeType class.
Definition finLattice_finBPOrderType :=
  @FinBPOrder.Pack disp finLatticeType class.
Definition finLattice_finTPOrderType :=
  @FinTPOrder.Pack disp finLatticeType class.
Definition finLattice_finTBPOrderType :=
  @FinTBPOrder.Pack disp finLatticeType class.
Definition finLattice_bMeetSemilatticeType :=
  @BMeetSemilattice.Pack disp finLatticeType class.
Definition finLattice_tMeetSemilatticeType :=
  @TMeetSemilattice.Pack disp finLatticeType class.
Definition finLattice_tbMeetSemilatticeType :=
  @TBMeetSemilattice.Pack disp finLatticeType class.
Definition finLattice_finBMeetSemilatticeType :=
  @FinBMeetSemilattice.Pack disp finLatticeType class.
Definition finLattice_bJoinSemilatticeType :=
  @BJoinSemilattice.Pack disp finLatticeType class.
Definition finLattice_tJoinSemilatticeType :=
  @TJoinSemilattice.Pack disp finLatticeType class.
Definition finLattice_tbJoinSemilatticeType :=
  @TBJoinSemilattice.Pack disp finLatticeType class.
Definition finLattice_finTJoinSemilatticeType :=
  @FinTJoinSemilattice.Pack disp finLatticeType class.
Definition finLattice_bLatticeType := @BLattice.Pack disp finLatticeType class.
Definition finLattice_tLatticeType := @TLattice.Pack disp finLatticeType class.
Definition finLattice_tbLatticeType :=
 @TBLattice.Pack disp finLatticeType class.
End ClassDef.

Module Exports.
Coercion base : class_of >-> TBLattice.class_of.
Coercion base2 : class_of >-> FinTBPOrder.class_of.
Coercion base3 : class_of >-> FinLattice.class_of.
Coercion base4 : class_of >-> FinBMeetSemilattice.class_of.
Coercion base5 : class_of >-> FinTJoinSemilattice.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion countType : type >-> Countable.type.
Coercion finType : type >-> Finite.type.
Coercion porderType : type >-> POrder.type.
Coercion bPOrderType : type >-> BPOrder.type.
Coercion tPOrderType : type >-> TPOrder.type.
Coercion tbPOrderType : type >-> TBPOrder.type.
Coercion finPOrderType : type >-> FinPOrder.type.
Coercion finBPOrderType : type >-> FinBPOrder.type.
Coercion finTPOrderType : type >-> FinTPOrder.type.
Coercion finTBPOrderType : type >-> FinTBPOrder.type.
Coercion meetSemilatticeType : type >-> MeetSemilattice.type.
Coercion bMeetSemilatticeType : type >-> BMeetSemilattice.type.
Coercion tMeetSemilatticeType : type >-> TMeetSemilattice.type.
Coercion tbMeetSemilatticeType : type >-> TBMeetSemilattice.type.
Coercion finMeetSemilatticeType : type >-> FinMeetSemilattice.type.
Coercion finBMeetSemilatticeType : type >-> FinBMeetSemilattice.type.
Coercion joinSemilatticeType : type >-> JoinSemilattice.type.
Coercion bJoinSemilatticeType : type >-> BJoinSemilattice.type.
Coercion tJoinSemilatticeType : type >-> TJoinSemilattice.type.
Coercion tbJoinSemilatticeType : type >-> TBJoinSemilattice.type.
Coercion finJoinSemilatticeType : type >-> FinJoinSemilattice.type.
Coercion finTJoinSemilatticeType : type >-> FinTJoinSemilattice.type.
Coercion latticeType : type >-> Lattice.type.
Coercion bLatticeType : type >-> BLattice.type.
Coercion tLatticeType : type >-> TLattice.type.
Coercion tbLatticeType : type >-> TBLattice.type.
Coercion finLatticeType : type >-> FinLattice.type.
Canonical eqType.
Canonical choiceType.
Canonical countType.
Canonical finType.
Canonical porderType.
Canonical bPOrderType.
Canonical tPOrderType.
Canonical tbPOrderType.
Canonical finPOrderType.
Canonical finBPOrderType.
Canonical finTPOrderType.
Canonical finTBPOrderType.
Canonical meetSemilatticeType.
Canonical bMeetSemilatticeType.
Canonical tMeetSemilatticeType.
Canonical tbMeetSemilatticeType.
Canonical finMeetSemilatticeType.
Canonical finBMeetSemilatticeType.
Canonical joinSemilatticeType.
Canonical bJoinSemilatticeType.
Canonical tJoinSemilatticeType.
Canonical tbJoinSemilatticeType.
Canonical finJoinSemilatticeType.
Canonical finTJoinSemilatticeType.
Canonical latticeType.
Canonical bLatticeType.
Canonical tLatticeType.
Canonical tbLatticeType.
Canonical finLatticeType.
Canonical count_tMeetSemilatticeType.
Canonical count_tbMeetSemilatticeType.
Canonical count_bJoinSemilatticeType.
Canonical count_tbJoinSemilatticeType.
Canonical count_bLatticeType.
Canonical count_tLatticeType.
Canonical count_tbLatticeType.
Canonical fin_tMeetSemilatticeType.
Canonical fin_tbMeetSemilatticeType.
Canonical fin_bJoinSemilatticeType.
Canonical fin_tbJoinSemilatticeType.
Canonical fin_bLatticeType.
Canonical fin_tLatticeType.
Canonical fin_tbLatticeType.
Canonical finPOrder_tMeetSemilatticeType.
Canonical finPOrder_tbMeetSemilatticeType.
Canonical finPOrder_bJoinSemilatticeType.
Canonical finPOrder_tbJoinSemilatticeType.
Canonical finPOrder_bLatticeType.
Canonical finPOrder_tLatticeType.
Canonical finPOrder_tbLatticeType.
Canonical finBPOrder_tMeetSemilatticeType.
Canonical finBPOrder_tbMeetSemilatticeType.
Canonical finBPOrder_joinSemilatticeType.
Canonical finBPOrder_bJoinSemilatticeType.
Canonical finBPOrder_tJoinSemilatticeType.
Canonical finBPOrder_tbJoinSemilatticeType.
Canonical finBPOrder_latticeType.
Canonical finBPOrder_bLatticeType.
Canonical finBPOrder_tLatticeType.
Canonical finBPOrder_tbLatticeType.
Canonical finTPOrder_meetSemilatticeType.
Canonical finTPOrder_bMeetSemilatticeType.
Canonical finTPOrder_tMeetSemilatticeType.
Canonical finTPOrder_tbMeetSemilatticeType.
Canonical finTPOrder_bJoinSemilatticeType.
Canonical finTPOrder_tbJoinSemilatticeType.
Canonical finTPOrder_latticeType.
Canonical finTPOrder_bLatticeType.
Canonical finTPOrder_tLatticeType.
Canonical finTPOrder_tbLatticeType.
Canonical finTBPOrder_meetSemilatticeType.
Canonical finTBPOrder_bMeetSemilatticeType.
Canonical finTBPOrder_tMeetSemilatticeType.
Canonical finTBPOrder_tbMeetSemilatticeType.
Canonical finTBPOrder_joinSemilatticeType.
Canonical finTBPOrder_bJoinSemilatticeType.
Canonical finTBPOrder_tJoinSemilatticeType.
Canonical finTBPOrder_tbJoinSemilatticeType.
Canonical finTBPOrder_latticeType.
Canonical finTBPOrder_bLatticeType.
Canonical finTBPOrder_tLatticeType.
Canonical finTBPOrder_tbLatticeType.
Canonical finMeetSemilattice_tPOrderType.
Canonical finMeetSemilattice_tbPOrderType.
Canonical finMeetSemilattice_finTPOrderType.
Canonical finMeetSemilattice_finTBPOrderType.
Canonical finMeetSemilattice_tMeetSemilatticeType.
Canonical finMeetSemilattice_tbMeetSemilatticeType.
Canonical finMeetSemilattice_bJoinSemilatticeType.
Canonical finMeetSemilattice_tJoinSemilatticeType.
Canonical finMeetSemilattice_tbJoinSemilatticeType.
Canonical finMeetSemilattice_bLatticeType.
Canonical finMeetSemilattice_tLatticeType.
Canonical finMeetSemilattice_tbLatticeType.
Canonical finBMeetSemilattice_tPOrderType.
Canonical finBMeetSemilattice_tbPOrderType.
Canonical finBMeetSemilattice_finTPOrderType.
Canonical finBMeetSemilattice_finTBPOrderType.
Canonical finBMeetSemilattice_tMeetSemilatticeType.
Canonical finBMeetSemilattice_tbMeetSemilatticeType.
Canonical finBMeetSemilattice_joinSemilatticeType.
Canonical finBMeetSemilattice_bJoinSemilatticeType.
Canonical finBMeetSemilattice_tJoinSemilatticeType.
Canonical finBMeetSemilattice_tbJoinSemilatticeType.
Canonical finBMeetSemilattice_latticeType.
Canonical finBMeetSemilattice_bLatticeType.
Canonical finBMeetSemilattice_tLatticeType.
Canonical finBMeetSemilattice_tbLatticeType.
Canonical finJoinSemilattice_bPOrderType.
Canonical finJoinSemilattice_tbPOrderType.
Canonical finJoinSemilattice_finBPOrderType.
Canonical finJoinSemilattice_finTBPOrderType.
Canonical finJoinSemilattice_bMeetSemilatticeType.
Canonical finJoinSemilattice_tMeetSemilatticeType.
Canonical finJoinSemilattice_tbMeetSemilatticeType.
Canonical finJoinSemilattice_finBMeetSemilatticeType.
Canonical finJoinSemilattice_bJoinSemilatticeType.
Canonical finJoinSemilattice_tbJoinSemilatticeType.
Canonical finJoinSemilattice_bLatticeType.
Canonical finJoinSemilattice_tLatticeType.
Canonical finJoinSemilattice_tbLatticeType.
Canonical finTJoinSemilattice_bPOrderType.
Canonical finTJoinSemilattice_tbPOrderType.
Canonical finTJoinSemilattice_finBPOrderType.
Canonical finTJoinSemilattice_finTBPOrderType.
Canonical finTJoinSemilattice_meetSemilatticeType.
Canonical finTJoinSemilattice_bMeetSemilatticeType.
Canonical finTJoinSemilattice_tMeetSemilatticeType.
Canonical finTJoinSemilattice_tbMeetSemilatticeType.
Canonical finTJoinSemilattice_finMeetSemilatticeType.
Canonical finTJoinSemilattice_finBMeetSemilatticeType.
Canonical finTJoinSemilattice_bJoinSemilatticeType.
Canonical finTJoinSemilattice_tbJoinSemilatticeType.
Canonical finTJoinSemilattice_latticeType.
Canonical finTJoinSemilattice_bLatticeType.
Canonical finTJoinSemilattice_tLatticeType.
Canonical finTJoinSemilattice_tbLatticeType.
Canonical finLattice_bPOrderType.
Canonical finLattice_tPOrderType.
Canonical finLattice_tbPOrderType.
Canonical finLattice_finBPOrderType.
Canonical finLattice_finTPOrderType.
Canonical finLattice_finTBPOrderType.
Canonical finLattice_bMeetSemilatticeType.
Canonical finLattice_tMeetSemilatticeType.
Canonical finLattice_tbMeetSemilatticeType.
Canonical finLattice_finBMeetSemilatticeType.
Canonical finLattice_bJoinSemilatticeType.
Canonical finLattice_tJoinSemilatticeType.
Canonical finLattice_tbJoinSemilatticeType.
Canonical finLattice_finTJoinSemilatticeType.
Canonical finLattice_bLatticeType.
Canonical finLattice_tLatticeType.
Canonical finLattice_tbLatticeType.
Notation finTBLatticeType := type.
Notation "[ 'finTBLatticeType' 'of' T ]" := (@pack T _ _ _ id _ _ id)
  (at level 0, format "[ 'finTBLatticeType'  'of'  T ]") : form_scope.
End Exports.

End FinTBLattice.
Import FinTBLattice.Exports.

Module FinDistrLattice.
Section ClassDef.

Set Primitive Projections.

Record class_of (T : Type) := Class {
  base : DistrLattice.class_of T;
  mixin : Finite.mixin_of (Equality.Pack base);
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> DistrLattice.class_of.
Local Coercion base2 T (c : class_of T) : FinLattice.class_of T :=
  @FinLattice.Class T c (mixin c).

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Definition pack :=
  fun bT b & phant_id (@DistrLattice.class disp bT) b =>
  fun mT m & phant_id (@Finite.class mT) (@Finite.Class _ _ m) =>
  Pack disp (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition countType := @Countable.Pack cT class.
Definition finType := @Finite.Pack cT class.
Definition porderType := @POrder.Pack disp cT class.
Definition finPOrderType := @FinPOrder.Pack disp cT class.
Definition meetSemilatticeType := @MeetSemilattice.Pack disp cT class.
Definition finMeetSemilatticeType := @FinMeetSemilattice.Pack disp cT class.
Definition joinSemilatticeType := @JoinSemilattice.Pack disp cT class.
Definition finJoinSemilatticeType := @FinJoinSemilattice.Pack disp cT class.
Definition latticeType := @Lattice.Pack disp cT class.
Definition finLatticeType := @FinLattice.Pack disp cT class.
Definition distrLatticeType := @DistrLattice.Pack disp cT class.
Definition count_distrLatticeType := @DistrLattice.Pack disp countType class.
Definition fin_distrLatticeType := @DistrLattice.Pack disp finType class.
Definition finPOrder_distrLatticeType :=
  @DistrLattice.Pack disp finPOrderType class.
Definition finMeetSemilattice_distrLatticeType :=
  @DistrLattice.Pack disp finMeetSemilatticeType class.
Definition finJoinSemilattice_distrLatticeType :=
  @DistrLattice.Pack disp finJoinSemilatticeType class.
Definition finLattice_distrLatticeType :=
  @DistrLattice.Pack disp finLatticeType class.
End ClassDef.

Module Exports.
Coercion base : class_of >-> DistrLattice.class_of.
Coercion base2 : class_of >-> FinLattice.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion countType : type >-> Countable.type.
Coercion finType : type >-> Finite.type.
Coercion porderType : type >-> POrder.type.
Coercion finPOrderType : type >-> FinPOrder.type.
Coercion meetSemilatticeType : type >-> MeetSemilattice.type.
Coercion finMeetSemilatticeType : type >-> FinMeetSemilattice.type.
Coercion joinSemilatticeType : type >-> JoinSemilattice.type.
Coercion finJoinSemilatticeType : type >-> FinJoinSemilattice.type.
Coercion latticeType : type >-> Lattice.type.
Coercion finLatticeType : type >-> FinLattice.type.
Coercion distrLatticeType : type >-> DistrLattice.type.
Canonical eqType.
Canonical choiceType.
Canonical countType.
Canonical finType.
Canonical porderType.
Canonical finPOrderType.
Canonical meetSemilatticeType.
Canonical finMeetSemilatticeType.
Canonical joinSemilatticeType.
Canonical finJoinSemilatticeType.
Canonical latticeType.
Canonical finLatticeType.
Canonical distrLatticeType.
Canonical count_distrLatticeType.
Canonical fin_distrLatticeType.
Canonical finPOrder_distrLatticeType.
Canonical finMeetSemilattice_distrLatticeType.
Canonical finJoinSemilattice_distrLatticeType.
Canonical finLattice_distrLatticeType.
Notation finDistrLatticeType := type.
Notation "[ 'finDistrLatticeType' 'of' T ]" := (@pack T _ _ _ id _ _ id)
  (at level 0, format "[ 'finDistrLatticeType'  'of'  T ]") : form_scope.
End Exports.

End FinDistrLattice.
Import FinDistrLattice.Exports.

Module FinTBDistrLattice.
Section ClassDef.

Set Primitive Projections.

Record class_of (T : Type) := Class {
  base : TBDistrLattice.class_of T;
  mixin : Finite.mixin_of (Equality.Pack base);
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> TBDistrLattice.class_of.
Local Coercion base2 T (c : class_of T) : FinTBLattice.class_of T :=
  @FinTBLattice.Class T c (mixin c).
Local Coercion base3 T (c : class_of T) : FinDistrLattice.class_of T :=
  @FinDistrLattice.Class T c (mixin c).

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Definition pack :=
  fun bT b & phant_id (@TBDistrLattice.class disp bT) b =>
  fun mT m & phant_id (@Finite.class mT) (@Finite.Class _ _ m) =>
  Pack disp (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition countType := @Countable.Pack cT class.
Definition finType := @Finite.Pack cT class.
Definition porderType := @POrder.Pack disp cT class.
Definition bPOrderType := @BPOrder.Pack disp cT class.
Definition tPOrderType := @TPOrder.Pack disp cT class.
Definition tbPOrderType := @TBPOrder.Pack disp cT class.
Definition finPOrderType := @FinPOrder.Pack disp cT class.
Definition finBPOrderType := @FinBPOrder.Pack disp cT class.
Definition finTPOrderType := @FinTPOrder.Pack disp cT class.
Definition finTBPOrderType := @FinTBPOrder.Pack disp cT class.
Definition meetSemilatticeType := @MeetSemilattice.Pack disp cT class.
Definition bMeetSemilatticeType := @BMeetSemilattice.Pack disp cT class.
Definition tMeetSemilatticeType := @TMeetSemilattice.Pack disp cT class.
Definition tbMeetSemilatticeType := @TBMeetSemilattice.Pack disp cT class.
Definition finMeetSemilatticeType := @FinMeetSemilattice.Pack disp cT class.
Definition finBMeetSemilatticeType := @FinBMeetSemilattice.Pack disp cT class.
Definition joinSemilatticeType := @JoinSemilattice.Pack disp cT class.
Definition bJoinSemilatticeType := @BJoinSemilattice.Pack disp cT class.
Definition tJoinSemilatticeType := @TJoinSemilattice.Pack disp cT class.
Definition tbJoinSemilatticeType := @TBJoinSemilattice.Pack disp cT class.
Definition finJoinSemilatticeType := @FinJoinSemilattice.Pack disp cT class.
Definition finTJoinSemilatticeType := @FinTJoinSemilattice.Pack disp cT class.
Definition latticeType := @Lattice.Pack disp cT class.
Definition bLatticeType := @BLattice.Pack disp cT class.
Definition tLatticeType := @TLattice.Pack disp cT class.
Definition tbLatticeType := @TBLattice.Pack disp cT class.
Definition finLatticeType := @FinLattice.Pack disp cT class.
Definition finTBLatticeType := @FinTBLattice.Pack disp cT class.
Definition distrLatticeType := @DistrLattice.Pack disp cT class.
Definition bDistrLatticeType := @BDistrLattice.Pack disp cT class.
Definition tDistrLatticeType := @TDistrLattice.Pack disp cT class.
Definition tbDistrLatticeType := @TBDistrLattice.Pack disp cT class.
Definition finDistrLatticeType := @FinDistrLattice.Pack disp cT class.
Definition count_bDistrLatticeType := @BDistrLattice.Pack disp countType class.
Definition count_tDistrLatticeType := @TDistrLattice.Pack disp countType class.
Definition count_tbDistrLatticeType :=
  @TBDistrLattice.Pack disp countType class.
Definition fin_bDistrLatticeType := @BDistrLattice.Pack disp finType class.
Definition fin_tDistrLatticeType := @TDistrLattice.Pack disp finType class.
Definition fin_tbDistrLatticeType := @TBDistrLattice.Pack disp finType class.
Definition finPOrder_bDistrLatticeType :=
  @BDistrLattice.Pack disp finPOrderType class.
Definition finPOrder_tDistrLatticeType :=
  @TDistrLattice.Pack disp finPOrderType class.
Definition finPOrder_tbDistrLatticeType :=
  @TBDistrLattice.Pack disp finPOrderType class.
Definition finBPOrder_distrLatticeType :=
  @DistrLattice.Pack disp finBPOrderType class.
Definition finBPOrder_bDistrLatticeType :=
  @BDistrLattice.Pack disp finBPOrderType class.
Definition finBPOrder_tDistrLatticeType :=
  @TDistrLattice.Pack disp finBPOrderType class.
Definition finBPOrder_tbDistrLatticeType :=
  @TBDistrLattice.Pack disp finBPOrderType class.
Definition finTPOrder_distrLatticeType :=
  @DistrLattice.Pack disp finTPOrderType class.
Definition finTPOrder_bDistrLatticeType :=
  @BDistrLattice.Pack disp finTPOrderType class.
Definition finTPOrder_tDistrLatticeType :=
  @TDistrLattice.Pack disp finTPOrderType class.
Definition finTPOrder_tbDistrLatticeType :=
  @TBDistrLattice.Pack disp finTPOrderType class.
Definition finTBPOrder_distrLatticeType :=
  @DistrLattice.Pack disp finTBPOrderType class.
Definition finTBPOrder_bDistrLatticeType :=
  @BDistrLattice.Pack disp finTBPOrderType class.
Definition finTBPOrder_tDistrLatticeType :=
  @TDistrLattice.Pack disp finTBPOrderType class.
Definition finTBPOrder_tbDistrLatticeType :=
  @TBDistrLattice.Pack disp finTBPOrderType class.
Definition finMeetSemilattice_bDistrLatticeType :=
  @BDistrLattice.Pack disp finMeetSemilatticeType class.
Definition finMeetSemilattice_tDistrLatticeType :=
  @TDistrLattice.Pack disp finMeetSemilatticeType class.
Definition finMeetSemilattice_tbDistrLatticeType :=
  @TBDistrLattice.Pack disp finMeetSemilatticeType class.
Definition finBMeetSemilattice_distrLatticeType :=
  @DistrLattice.Pack disp finBMeetSemilatticeType class.
Definition finBMeetSemilattice_bDistrLatticeType :=
  @BDistrLattice.Pack disp finBMeetSemilatticeType class.
Definition finBMeetSemilattice_tDistrLatticeType :=
  @TDistrLattice.Pack disp finBMeetSemilatticeType class.
Definition finBMeetSemilattice_tbDistrLatticeType :=
  @TBDistrLattice.Pack disp finBMeetSemilatticeType class.
Definition finJoinSemilattice_bDistrLatticeType :=
  @BDistrLattice.Pack disp finJoinSemilatticeType class.
Definition finJoinSemilattice_tDistrLatticeType :=
  @TDistrLattice.Pack disp finJoinSemilatticeType class.
Definition finJoinSemilattice_tbDistrLatticeType :=
  @TBDistrLattice.Pack disp finJoinSemilatticeType class.
Definition finTJoinSemilattice_distrLatticeType :=
  @DistrLattice.Pack disp finTJoinSemilatticeType class.
Definition finTJoinSemilattice_bDistrLatticeType :=
  @BDistrLattice.Pack disp finTJoinSemilatticeType class.
Definition finTJoinSemilattice_tDistrLatticeType :=
  @TDistrLattice.Pack disp finTJoinSemilatticeType class.
Definition finTJoinSemilattice_tbDistrLatticeType :=
  @TBDistrLattice.Pack disp finTJoinSemilatticeType class.
Definition finLattice_bDistrLatticeType :=
  @BDistrLattice.Pack disp finLatticeType class.
Definition finLattice_tDistrLatticeType :=
  @TDistrLattice.Pack disp finLatticeType class.
Definition finLattice_tbDistrLatticeType :=
  @TBDistrLattice.Pack disp finLatticeType class.
Definition finTBLattice_distrLatticeType :=
  @DistrLattice.Pack disp finTBLatticeType class.
Definition finTBLattice_bDistrLatticeType :=
  @BDistrLattice.Pack disp finTBLatticeType class.
Definition finTBLattice_tDistrLatticeType :=
  @TDistrLattice.Pack disp finTBLatticeType class.
Definition finTBLattice_tbDistrLatticeType :=
  @TBDistrLattice.Pack disp finTBLatticeType class.
Definition finDistrLattice_bPOrderType :=
  @BPOrder.Pack disp finDistrLatticeType class.
Definition finDistrLattice_tPOrderType :=
  @TPOrder.Pack disp finDistrLatticeType class.
Definition finDistrLattice_tbPOrderType :=
  @TBPOrder.Pack disp finDistrLatticeType class.
Definition finDistrLattice_finBPOrderType :=
  @FinBPOrder.Pack disp finDistrLatticeType class.
Definition finDistrLattice_finTPOrderType :=
  @FinTPOrder.Pack disp finDistrLatticeType class.
Definition finDistrLattice_finTBPOrderType :=
  @FinTBPOrder.Pack disp finDistrLatticeType class.
Definition finDistrLattice_bMeetSemilatticeType :=
  @BMeetSemilattice.Pack disp finDistrLatticeType class.
Definition finDistrLattice_tMeetSemilatticeType :=
  @TMeetSemilattice.Pack disp finDistrLatticeType class.
Definition finDistrLattice_tbMeetSemilatticeType :=
  @TBMeetSemilattice.Pack disp finDistrLatticeType class.
Definition finDistrLattice_finBMeetSemilatticeType :=
  @FinBMeetSemilattice.Pack disp finDistrLatticeType class.
Definition finDistrLattice_bJoinSemilatticeType :=
  @BJoinSemilattice.Pack disp finDistrLatticeType class.
Definition finDistrLattice_tJoinSemilatticeType :=
  @TJoinSemilattice.Pack disp finDistrLatticeType class.
Definition finDistrLattice_tbJoinSemilatticeType :=
  @TBJoinSemilattice.Pack disp finDistrLatticeType class.
Definition finDistrLattice_finTJoinSemilatticeType :=
  @FinTJoinSemilattice.Pack disp finDistrLatticeType class.
Definition finDistrLattice_bLatticeType :=
  @BLattice.Pack disp finDistrLatticeType class.
Definition finDistrLattice_tLatticeType :=
  @TLattice.Pack disp finDistrLatticeType class.
Definition finDistrLattice_tbLatticeType :=
  @TBLattice.Pack disp finDistrLatticeType class.
Definition finDistrLattice_finTBLatticeType :=
  @FinTBLattice.Pack disp finDistrLatticeType class.
Definition finDistrLattice_bDistrLatticeType :=
  @BDistrLattice.Pack disp finDistrLatticeType class.
Definition finDistrLattice_tDistrLatticeType :=
  @TDistrLattice.Pack disp finDistrLatticeType class.
Definition finDistrLattice_tbDistrLatticeType :=
  @TBDistrLattice.Pack disp finDistrLatticeType class.
End ClassDef.

Module Exports.
Coercion base : class_of >-> TBDistrLattice.class_of.
Coercion base2 : class_of >-> FinTBLattice.class_of.
Coercion base3 : class_of >-> FinDistrLattice.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion countType : type >-> Countable.type.
Coercion finType : type >-> Finite.type.
Coercion porderType : type >-> POrder.type.
Coercion bPOrderType : type >-> BPOrder.type.
Coercion tPOrderType : type >-> TPOrder.type.
Coercion tbPOrderType : type >-> TBPOrder.type.
Coercion finPOrderType : type >-> FinPOrder.type.
Coercion finBPOrderType : type >-> FinBPOrder.type.
Coercion finTPOrderType : type >-> FinTPOrder.type.
Coercion finTBPOrderType : type >-> FinTBPOrder.type.
Coercion meetSemilatticeType : type >-> MeetSemilattice.type.
Coercion bMeetSemilatticeType : type >-> BMeetSemilattice.type.
Coercion tMeetSemilatticeType : type >-> TMeetSemilattice.type.
Coercion tbMeetSemilatticeType : type >-> TBMeetSemilattice.type.
Coercion finMeetSemilatticeType : type >-> FinMeetSemilattice.type.
Coercion finBMeetSemilatticeType : type >-> FinBMeetSemilattice.type.
Coercion joinSemilatticeType : type >-> JoinSemilattice.type.
Coercion bJoinSemilatticeType : type >-> BJoinSemilattice.type.
Coercion tJoinSemilatticeType : type >-> TJoinSemilattice.type.
Coercion tbJoinSemilatticeType : type >-> TBJoinSemilattice.type.
Coercion finJoinSemilatticeType : type >-> FinJoinSemilattice.type.
Coercion finTJoinSemilatticeType : type >-> FinTJoinSemilattice.type.
Coercion latticeType : type >-> Lattice.type.
Coercion bLatticeType : type >-> BLattice.type.
Coercion tLatticeType : type >-> TLattice.type.
Coercion tbLatticeType : type >-> TBLattice.type.
Coercion finLatticeType : type >-> FinLattice.type.
Coercion finTBLatticeType : type >-> FinTBLattice.type.
Coercion distrLatticeType : type >-> DistrLattice.type.
Coercion bDistrLatticeType : type >-> BDistrLattice.type.
Coercion tDistrLatticeType : type >-> TDistrLattice.type.
Coercion tbDistrLatticeType : type >-> TBDistrLattice.type.
Coercion finDistrLatticeType : type >-> FinDistrLattice.type.
Canonical eqType.
Canonical choiceType.
Canonical countType.
Canonical finType.
Canonical porderType.
Canonical bPOrderType.
Canonical tPOrderType.
Canonical tbPOrderType.
Canonical finPOrderType.
Canonical finBPOrderType.
Canonical finTPOrderType.
Canonical finTBPOrderType.
Canonical meetSemilatticeType.
Canonical bMeetSemilatticeType.
Canonical tMeetSemilatticeType.
Canonical tbMeetSemilatticeType.
Canonical finMeetSemilatticeType.
Canonical finBMeetSemilatticeType.
Canonical joinSemilatticeType.
Canonical bJoinSemilatticeType.
Canonical tJoinSemilatticeType.
Canonical tbJoinSemilatticeType.
Canonical finJoinSemilatticeType.
Canonical finTJoinSemilatticeType.
Canonical latticeType.
Canonical bLatticeType.
Canonical tLatticeType.
Canonical tbLatticeType.
Canonical finLatticeType.
Canonical finTBLatticeType.
Canonical distrLatticeType.
Canonical bDistrLatticeType.
Canonical tDistrLatticeType.
Canonical tbDistrLatticeType.
Canonical finDistrLatticeType.
Canonical count_bDistrLatticeType.
Canonical count_tDistrLatticeType.
Canonical count_tbDistrLatticeType.
Canonical fin_bDistrLatticeType.
Canonical fin_tDistrLatticeType.
Canonical fin_tbDistrLatticeType.
Canonical finPOrder_bDistrLatticeType.
Canonical finPOrder_tDistrLatticeType.
Canonical finPOrder_tbDistrLatticeType.
Canonical finBPOrder_distrLatticeType.
Canonical finBPOrder_bDistrLatticeType.
Canonical finBPOrder_tDistrLatticeType.
Canonical finBPOrder_tbDistrLatticeType.
Canonical finTPOrder_distrLatticeType.
Canonical finTPOrder_bDistrLatticeType.
Canonical finTPOrder_tDistrLatticeType.
Canonical finTPOrder_tbDistrLatticeType.
Canonical finTBPOrder_distrLatticeType.
Canonical finTBPOrder_bDistrLatticeType.
Canonical finTBPOrder_tDistrLatticeType.
Canonical finTBPOrder_tbDistrLatticeType.
Canonical finMeetSemilattice_bDistrLatticeType.
Canonical finMeetSemilattice_tDistrLatticeType.
Canonical finMeetSemilattice_tbDistrLatticeType.
Canonical finBMeetSemilattice_distrLatticeType.
Canonical finBMeetSemilattice_bDistrLatticeType.
Canonical finBMeetSemilattice_tDistrLatticeType.
Canonical finBMeetSemilattice_tbDistrLatticeType.
Canonical finJoinSemilattice_bDistrLatticeType.
Canonical finJoinSemilattice_tDistrLatticeType.
Canonical finJoinSemilattice_tbDistrLatticeType.
Canonical finTJoinSemilattice_distrLatticeType.
Canonical finTJoinSemilattice_bDistrLatticeType.
Canonical finTJoinSemilattice_tDistrLatticeType.
Canonical finTJoinSemilattice_tbDistrLatticeType.
Canonical finLattice_bDistrLatticeType.
Canonical finLattice_tDistrLatticeType.
Canonical finLattice_tbDistrLatticeType.
Canonical finTBLattice_distrLatticeType.
Canonical finTBLattice_bDistrLatticeType.
Canonical finTBLattice_tDistrLatticeType.
Canonical finTBLattice_tbDistrLatticeType.
Canonical finDistrLattice_bPOrderType.
Canonical finDistrLattice_tPOrderType.
Canonical finDistrLattice_tbPOrderType.
Canonical finDistrLattice_finBPOrderType.
Canonical finDistrLattice_finTPOrderType.
Canonical finDistrLattice_finTBPOrderType.
Canonical finDistrLattice_bMeetSemilatticeType.
Canonical finDistrLattice_tMeetSemilatticeType.
Canonical finDistrLattice_tbMeetSemilatticeType.
Canonical finDistrLattice_finBMeetSemilatticeType.
Canonical finDistrLattice_bJoinSemilatticeType.
Canonical finDistrLattice_tJoinSemilatticeType.
Canonical finDistrLattice_tbJoinSemilatticeType.
Canonical finDistrLattice_finTJoinSemilatticeType.
Canonical finDistrLattice_bLatticeType.
Canonical finDistrLattice_tLatticeType.
Canonical finDistrLattice_tbLatticeType.
Canonical finDistrLattice_finTBLatticeType.
Canonical finDistrLattice_bDistrLatticeType.
Canonical finDistrLattice_tDistrLatticeType.
Canonical finDistrLattice_tbDistrLatticeType.
Notation finTBDistrLatticeType := type.
Notation "[ 'finTBDistrLatticeType' 'of' T ]" := (@pack T _ _ _ id _ _ id)
  (at level 0, format "[ 'finTBDistrLatticeType'  'of'  T ]") : form_scope.
End Exports.

End FinTBDistrLattice.
Import FinTBDistrLattice.Exports.

Module FinCTBDistrLattice.
Section ClassDef.

Set Primitive Projections.

Record class_of (T : Type) := Class {
  base  : CTBDistrLattice.class_of T;
  mixin : Finite.mixin_of (Equality.Pack base);
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> CTBDistrLattice.class_of.
Local Coercion base2 T (c : class_of T) : FinTBDistrLattice.class_of T :=
  @FinTBDistrLattice.Class T c (mixin c).

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Definition pack :=
  fun bT b & phant_id (@CTBDistrLattice.class disp bT) b =>
  fun mT m & phant_id (@Finite.class mT) (@Finite.Class _ _ m) =>
  Pack disp (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition countType := @Countable.Pack cT class.
Definition finType := @Finite.Pack cT class.
Definition porderType := @POrder.Pack disp cT class.
Definition bPOrderType := @BPOrder.Pack disp cT class.
Definition tPOrderType := @TPOrder.Pack disp cT class.
Definition tbPOrderType := @TBPOrder.Pack disp cT class.
Definition finPOrderType := @FinPOrder.Pack disp cT class.
Definition finBPOrderType := @FinBPOrder.Pack disp cT class.
Definition finTPOrderType := @FinTPOrder.Pack disp cT class.
Definition finTBPOrderType := @FinTBPOrder.Pack disp cT class.
Definition meetSemilatticeType := @MeetSemilattice.Pack disp cT class.
Definition bMeetSemilatticeType := @BMeetSemilattice.Pack disp cT class.
Definition tMeetSemilatticeType := @TMeetSemilattice.Pack disp cT class.
Definition tbMeetSemilatticeType := @TBMeetSemilattice.Pack disp cT class.
Definition finMeetSemilatticeType := @FinMeetSemilattice.Pack disp cT class.
Definition finBMeetSemilatticeType := @FinBMeetSemilattice.Pack disp cT class.
Definition joinSemilatticeType := @JoinSemilattice.Pack disp cT class.
Definition bJoinSemilatticeType := @BJoinSemilattice.Pack disp cT class.
Definition tJoinSemilatticeType := @TJoinSemilattice.Pack disp cT class.
Definition tbJoinSemilatticeType := @TBJoinSemilattice.Pack disp cT class.
Definition finJoinSemilatticeType := @FinJoinSemilattice.Pack disp cT class.
Definition finTJoinSemilatticeType := @FinTJoinSemilattice.Pack disp cT class.
Definition latticeType := @Lattice.Pack disp cT class.
Definition bLatticeType := @BLattice.Pack disp cT class.
Definition tLatticeType := @TLattice.Pack disp cT class.
Definition tbLatticeType := @TBLattice.Pack disp cT class.
Definition finLatticeType := @FinLattice.Pack disp cT class.
Definition finTBLatticeType := @FinTBLattice.Pack disp cT class.
Definition distrLatticeType := @DistrLattice.Pack disp cT class.
Definition bDistrLatticeType := @BDistrLattice.Pack disp cT class.
Definition tDistrLatticeType := @TDistrLattice.Pack disp cT class.
Definition tbDistrLatticeType := @TBDistrLattice.Pack disp cT class.
Definition finDistrLatticeType := @FinDistrLattice.Pack disp cT class.
Definition finTBDistrLatticeType := @FinTBDistrLattice.Pack disp cT class.
Definition cbDistrLatticeType := @CBDistrLattice.Pack disp cT class.
Definition ctbDistrLatticeType := @CTBDistrLattice.Pack disp cT class.
Definition count_cbDistrLatticeType :=
  @CBDistrLattice.Pack disp countType class.
Definition count_ctbDistrLatticeType :=
  @CTBDistrLattice.Pack disp countType class.
Definition fin_cbDistrLatticeType := @CBDistrLattice.Pack disp finType class.
Definition fin_ctbDistrLatticeType := @CTBDistrLattice.Pack disp finType class.
Definition finPOrder_cbDistrLatticeType :=
  @CBDistrLattice.Pack disp finPOrderType class.
Definition finPOrder_ctbDistrLatticeType :=
  @CTBDistrLattice.Pack disp finPOrderType class.
Definition finBPOrder_cbDistrLatticeType :=
  @CBDistrLattice.Pack disp finBPOrderType class.
Definition finBPOrder_ctbDistrLatticeType :=
  @CTBDistrLattice.Pack disp finBPOrderType class.
Definition finTPOrder_cbDistrLatticeType :=
  @CBDistrLattice.Pack disp finTPOrderType class.
Definition finTPOrder_ctbDistrLatticeType :=
  @CTBDistrLattice.Pack disp finTPOrderType class.
Definition finTBPOrder_cbDistrLatticeType :=
  @CBDistrLattice.Pack disp finTBPOrderType class.
Definition finTBPOrder_ctbDistrLatticeType :=
  @CTBDistrLattice.Pack disp finTBPOrderType class.
Definition finMeetSemilattice_cbDistrLatticeType :=
  @CBDistrLattice.Pack disp finMeetSemilatticeType class.
Definition finMeetSemilattice_ctbDistrLatticeType :=
  @CTBDistrLattice.Pack disp finMeetSemilatticeType class.
Definition finBMeetSemilattice_cbDistrLatticeType :=
  @CBDistrLattice.Pack disp finBMeetSemilatticeType class.
Definition finBMeetSemilattice_ctbDistrLatticeType :=
  @CTBDistrLattice.Pack disp finBMeetSemilatticeType class.
Definition finJoinSemilattice_cbDistrLatticeType :=
  @CBDistrLattice.Pack disp finJoinSemilatticeType class.
Definition finJoinSemilattice_ctbDistrLatticeType :=
  @CTBDistrLattice.Pack disp finJoinSemilatticeType class.
Definition finTJoinSemilattice_cbDistrLatticeType :=
  @CBDistrLattice.Pack disp finTJoinSemilatticeType class.
Definition finTJoinSemilattice_ctbDistrLatticeType :=
  @CTBDistrLattice.Pack disp finTJoinSemilatticeType class.
Definition finLattice_cbDistrLatticeType :=
  @CBDistrLattice.Pack disp finLatticeType class.
Definition finLattice_ctbDistrLatticeType :=
  @CTBDistrLattice.Pack disp finLatticeType class.
Definition finTBLattice_cbDistrLatticeType :=
  @CBDistrLattice.Pack disp finTBLatticeType class.
Definition finTBLattice_ctbDistrLatticeType :=
  @CTBDistrLattice.Pack disp finTBLatticeType class.
Definition finDistrLattice_cbDistrLatticeType :=
  @CBDistrLattice.Pack disp finDistrLatticeType class.
Definition finDistrLattice_ctbDistrLatticeType :=
  @CTBDistrLattice.Pack disp finDistrLatticeType class.
Definition finTBDistrLattice_cbDistrLatticeType :=
  @CBDistrLattice.Pack disp finTBDistrLatticeType class.
Definition finTBDistrLattice_ctbDistrLatticeType :=
  @CTBDistrLattice.Pack disp finTBDistrLatticeType class.
End ClassDef.

Module Exports.
Coercion base : class_of >-> CTBDistrLattice.class_of.
Coercion base2 : class_of >-> FinTBDistrLattice.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion countType : type >-> Countable.type.
Coercion finType : type >-> Finite.type.
Coercion porderType : type >-> POrder.type.
Coercion bPOrderType : type >-> BPOrder.type.
Coercion tPOrderType : type >-> TPOrder.type.
Coercion tbPOrderType : type >-> TBPOrder.type.
Coercion finPOrderType : type >-> FinPOrder.type.
Coercion finBPOrderType : type >-> FinBPOrder.type.
Coercion finTPOrderType : type >-> FinTPOrder.type.
Coercion finTBPOrderType : type >-> FinTBPOrder.type.
Coercion meetSemilatticeType : type >-> MeetSemilattice.type.
Coercion bMeetSemilatticeType : type >-> BMeetSemilattice.type.
Coercion tMeetSemilatticeType : type >-> TMeetSemilattice.type.
Coercion tbMeetSemilatticeType : type >-> TBMeetSemilattice.type.
Coercion finMeetSemilatticeType : type >-> FinMeetSemilattice.type.
Coercion finBMeetSemilatticeType : type >-> FinBMeetSemilattice.type.
Coercion joinSemilatticeType : type >-> JoinSemilattice.type.
Coercion bJoinSemilatticeType : type >-> BJoinSemilattice.type.
Coercion tJoinSemilatticeType : type >-> TJoinSemilattice.type.
Coercion tbJoinSemilatticeType : type >-> TBJoinSemilattice.type.
Coercion finJoinSemilatticeType : type >-> FinJoinSemilattice.type.
Coercion finTJoinSemilatticeType : type >-> FinTJoinSemilattice.type.
Coercion latticeType : type >-> Lattice.type.
Coercion bLatticeType : type >-> BLattice.type.
Coercion tLatticeType : type >-> TLattice.type.
Coercion tbLatticeType : type >-> TBLattice.type.
Coercion finLatticeType : type >-> FinLattice.type.
Coercion finTBLatticeType : type >-> FinTBLattice.type.
Coercion distrLatticeType : type >-> DistrLattice.type.
Coercion bDistrLatticeType : type >-> BDistrLattice.type.
Coercion tDistrLatticeType : type >-> TDistrLattice.type.
Coercion tbDistrLatticeType : type >-> TBDistrLattice.type.
Coercion finDistrLatticeType : type >-> FinDistrLattice.type.
Coercion finTBDistrLatticeType : type >-> FinTBDistrLattice.type.
Coercion cbDistrLatticeType : type >-> CBDistrLattice.type.
Coercion ctbDistrLatticeType : type >-> CTBDistrLattice.type.
Canonical eqType.
Canonical choiceType.
Canonical countType.
Canonical finType.
Canonical porderType.
Canonical bPOrderType.
Canonical tPOrderType.
Canonical tbPOrderType.
Canonical finPOrderType.
Canonical finBPOrderType.
Canonical finTPOrderType.
Canonical finTBPOrderType.
Canonical meetSemilatticeType.
Canonical bMeetSemilatticeType.
Canonical tMeetSemilatticeType.
Canonical tbMeetSemilatticeType.
Canonical finMeetSemilatticeType.
Canonical finBMeetSemilatticeType.
Canonical joinSemilatticeType.
Canonical bJoinSemilatticeType.
Canonical tJoinSemilatticeType.
Canonical tbJoinSemilatticeType.
Canonical finJoinSemilatticeType.
Canonical finTJoinSemilatticeType.
Canonical latticeType.
Canonical bLatticeType.
Canonical tLatticeType.
Canonical tbLatticeType.
Canonical finLatticeType.
Canonical finTBLatticeType.
Canonical distrLatticeType.
Canonical bDistrLatticeType.
Canonical tDistrLatticeType.
Canonical tbDistrLatticeType.
Canonical finDistrLatticeType.
Canonical finTBDistrLatticeType.
Canonical cbDistrLatticeType.
Canonical ctbDistrLatticeType.
Canonical count_cbDistrLatticeType.
Canonical count_ctbDistrLatticeType.
Canonical fin_cbDistrLatticeType.
Canonical fin_ctbDistrLatticeType.
Canonical finPOrder_cbDistrLatticeType.
Canonical finPOrder_ctbDistrLatticeType.
Canonical finBPOrder_cbDistrLatticeType.
Canonical finBPOrder_ctbDistrLatticeType.
Canonical finTPOrder_cbDistrLatticeType.
Canonical finTPOrder_ctbDistrLatticeType.
Canonical finTBPOrder_cbDistrLatticeType.
Canonical finTBPOrder_ctbDistrLatticeType.
Canonical finMeetSemilattice_cbDistrLatticeType.
Canonical finMeetSemilattice_ctbDistrLatticeType.
Canonical finBMeetSemilattice_cbDistrLatticeType.
Canonical finBMeetSemilattice_ctbDistrLatticeType.
Canonical finJoinSemilattice_cbDistrLatticeType.
Canonical finJoinSemilattice_ctbDistrLatticeType.
Canonical finTJoinSemilattice_cbDistrLatticeType.
Canonical finTJoinSemilattice_ctbDistrLatticeType.
Canonical finLattice_cbDistrLatticeType.
Canonical finLattice_ctbDistrLatticeType.
Canonical finTBLattice_cbDistrLatticeType.
Canonical finTBLattice_ctbDistrLatticeType.
Canonical finDistrLattice_cbDistrLatticeType.
Canonical finDistrLattice_ctbDistrLatticeType.
Canonical finTBDistrLattice_cbDistrLatticeType.
Canonical finTBDistrLattice_ctbDistrLatticeType.
Notation finCTBDistrLatticeType := type.
Notation "[ 'finCTBDistrLatticeType' 'of' T ]" := (@pack T _ _ _ id _ _ id)
  (at level 0, format "[ 'finCTBDistrLatticeType'  'of'  T ]") : form_scope.
End Exports.

End FinCTBDistrLattice.
Import FinCTBDistrLattice.Exports.

Module FinTotal.
Section ClassDef.

Set Primitive Projections.

Record class_of (T : Type) := Class {
  base : Total.class_of T;
  mixin : Finite.mixin_of (Equality.Pack base);
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> Total.class_of.
Local Coercion base2 T (c : class_of T) : FinDistrLattice.class_of T :=
  @FinDistrLattice.Class T c (mixin c).

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Definition pack :=
  fun bT b & phant_id (@Total.class disp bT) b =>
  fun mT m & phant_id (@Finite.class mT) (@Finite.Class _ _ m) =>
  Pack disp (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition countType := @Countable.Pack cT class.
Definition finType := @Finite.Pack cT class.
Definition porderType := @POrder.Pack disp cT class.
Definition finPOrderType := @FinPOrder.Pack disp cT class.
Definition meetSemilatticeType := @MeetSemilattice.Pack disp cT class.
Definition finMeetSemilatticeType := @FinMeetSemilattice.Pack disp cT class.
Definition joinSemilatticeType := @JoinSemilattice.Pack disp cT class.
Definition finJoinSemilatticeType := @FinJoinSemilattice.Pack disp cT class.
Definition latticeType := @Lattice.Pack disp cT class.
Definition finLatticeType := @FinLattice.Pack disp cT class.
Definition distrLatticeType := @DistrLattice.Pack disp cT class.
Definition finDistrLatticeType := @FinDistrLattice.Pack disp cT class.
Definition orderType := @Total.Pack disp cT class.
Definition order_countType := @Countable.Pack orderType class.
Definition order_finType := @Finite.Pack orderType class.
Definition order_finPOrderType := @FinPOrder.Pack disp orderType class.
Definition order_finMeetSemilatticeType :=
  @FinMeetSemilattice.Pack disp orderType class.
Definition order_finJoinSemilatticeType :=
  @FinJoinSemilattice.Pack disp orderType class.
Definition order_finLatticeType := @FinLattice.Pack disp orderType class.
Definition order_finDistrLatticeType :=
  @FinDistrLattice.Pack disp orderType class.
End ClassDef.

Module Exports.
Coercion base : class_of >-> Total.class_of.
Coercion base2 : class_of >-> FinDistrLattice.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion countType : type >-> Countable.type.
Coercion finType : type >-> Finite.type.
Coercion porderType : type >-> POrder.type.
Coercion finPOrderType : type >-> FinPOrder.type.
Coercion meetSemilatticeType : type >-> MeetSemilattice.type.
Coercion finMeetSemilatticeType : type >-> FinMeetSemilattice.type.
Coercion joinSemilatticeType : type >-> JoinSemilattice.type.
Coercion finJoinSemilatticeType : type >-> FinJoinSemilattice.type.
Coercion latticeType : type >-> Lattice.type.
Coercion finLatticeType : type >-> FinLattice.type.
Coercion distrLatticeType : type >-> DistrLattice.type.
Coercion finDistrLatticeType : type >-> FinDistrLattice.type.
Coercion orderType : type >-> Total.type.
Canonical eqType.
Canonical choiceType.
Canonical countType.
Canonical finType.
Canonical porderType.
Canonical finPOrderType.
Canonical meetSemilatticeType.
Canonical finMeetSemilatticeType.
Canonical joinSemilatticeType.
Canonical finJoinSemilatticeType.
Canonical latticeType.
Canonical finLatticeType.
Canonical distrLatticeType.
Canonical finDistrLatticeType.
Canonical orderType.
Canonical order_countType.
Canonical order_finType.
Canonical order_finPOrderType.
Canonical order_finMeetSemilatticeType.
Canonical order_finJoinSemilatticeType.
Canonical order_finLatticeType.
Canonical order_finDistrLatticeType.
Notation finOrderType := type.
Notation "[ 'finOrderType' 'of' T ]" := (@pack T _ _ _ id _ _ id)
  (at level 0, format "[ 'finOrderType'  'of'  T ]") : form_scope.
End Exports.
End FinTotal.
Import FinTotal.Exports.

Module FinTBTotal.
Section ClassDef.

Set Primitive Projections.

Record class_of (T : Type) := Class {
  base : TBTotal.class_of T;
  mixin : Finite.mixin_of (Equality.Pack base);
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> TBTotal.class_of.
Local Coercion base2 T (c : class_of T) : FinTBDistrLattice.class_of T :=
  @FinTBDistrLattice.Class T c (mixin c).
Local Coercion base3 T (c : class_of T) : FinTotal.class_of T :=
  @FinTotal.Class T c (mixin c).

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Definition pack :=
  fun bT b & phant_id (@TBTotal.class disp bT) b =>
  fun mT m & phant_id (@Finite.class mT) (@Finite.Class _ _ m) =>
  Pack disp (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition countType := @Countable.Pack cT class.
Definition finType := @Finite.Pack cT class.
Definition porderType := @POrder.Pack disp cT class.
Definition bPOrderType := @BPOrder.Pack disp cT class.
Definition tPOrderType := @TPOrder.Pack disp cT class.
Definition tbPOrderType := @TBPOrder.Pack disp cT class.
Definition finPOrderType := @FinPOrder.Pack disp cT class.
Definition finBPOrderType := @FinBPOrder.Pack disp cT class.
Definition finTPOrderType := @FinTPOrder.Pack disp cT class.
Definition finTBPOrderType := @FinTBPOrder.Pack disp cT class.
Definition meetSemilatticeType := @MeetSemilattice.Pack disp cT class.
Definition bMeetSemilatticeType := @BMeetSemilattice.Pack disp cT class.
Definition tMeetSemilatticeType := @TMeetSemilattice.Pack disp cT class.
Definition tbMeetSemilatticeType := @TBMeetSemilattice.Pack disp cT class.
Definition finMeetSemilatticeType := @FinMeetSemilattice.Pack disp cT class.
Definition finBMeetSemilatticeType := @FinBMeetSemilattice.Pack disp cT class.
Definition joinSemilatticeType := @JoinSemilattice.Pack disp cT class.
Definition bJoinSemilatticeType := @BJoinSemilattice.Pack disp cT class.
Definition tJoinSemilatticeType := @TJoinSemilattice.Pack disp cT class.
Definition tbJoinSemilatticeType := @TBJoinSemilattice.Pack disp cT class.
Definition finJoinSemilatticeType := @FinJoinSemilattice.Pack disp cT class.
Definition finTJoinSemilatticeType := @FinTJoinSemilattice.Pack disp cT class.
Definition latticeType := @Lattice.Pack disp cT class.
Definition bLatticeType := @BLattice.Pack disp cT class.
Definition tLatticeType := @TLattice.Pack disp cT class.
Definition tbLatticeType := @TBLattice.Pack disp cT class.
Definition finLatticeType := @FinLattice.Pack disp cT class.
Definition finTBLatticeType := @FinTBLattice.Pack disp cT class.
Definition distrLatticeType := @DistrLattice.Pack disp cT class.
Definition bDistrLatticeType := @BDistrLattice.Pack disp cT class.
Definition tDistrLatticeType := @TDistrLattice.Pack disp cT class.
Definition tbDistrLatticeType := @TBDistrLattice.Pack disp cT class.
Definition finDistrLatticeType := @FinDistrLattice.Pack disp cT class.
Definition finTBDistrLatticeType := @FinTBDistrLattice.Pack disp cT class.
Definition orderType := @Total.Pack disp cT class.
Definition bOrderType := @BTotal.Pack disp cT class.
Definition tOrderType := @TTotal.Pack disp cT class.
Definition tbOrderType := @TBTotal.Pack disp cT class.
Definition finOrderType := @FinTotal.Pack disp cT class.
Definition count_bOrderType := @BTotal.Pack disp countType class.
Definition count_tOrderType := @TTotal.Pack disp countType class.
Definition count_tbOrderType := @TBTotal.Pack disp countType class.
Definition fin_bOrderType := @BTotal.Pack disp finType class.
Definition fin_tOrderType := @TTotal.Pack disp finType class.
Definition fin_tbOrderType := @TBTotal.Pack disp finType class.
Definition finPOrder_bOrderType := @BTotal.Pack disp finPOrderType class.
Definition finPOrder_tOrderType := @TTotal.Pack disp finPOrderType class.
Definition finPOrder_tbOrderType := @TBTotal.Pack disp finPOrderType class.
Definition finBPOrder_orderType := @Total.Pack disp finBPOrderType class.
Definition finBPOrder_bOrderType := @BTotal.Pack disp finBPOrderType class.
Definition finBPOrder_tOrderType := @TTotal.Pack disp finBPOrderType class.
Definition finBPOrder_tbOrderType := @TBTotal.Pack disp finBPOrderType class.
Definition finBPOrder_finOrderType := @FinTotal.Pack disp finBPOrderType class.
Definition finTPOrder_orderType := @Total.Pack disp finTPOrderType class.
Definition finTPOrder_bOrderType := @BTotal.Pack disp finTPOrderType class.
Definition finTPOrder_tOrderType := @TTotal.Pack disp finTPOrderType class.
Definition finTPOrder_tbOrderType := @TBTotal.Pack disp finTPOrderType class.
Definition finTPOrder_finOrderType := @FinTotal.Pack disp finTPOrderType class.
Definition finTBPOrder_orderType := @Total.Pack disp finTBPOrderType class.
Definition finTBPOrder_bOrderType := @BTotal.Pack disp finTBPOrderType class.
Definition finTBPOrder_tOrderType := @TTotal.Pack disp finTBPOrderType class.
Definition finTBPOrder_tbOrderType := @TBTotal.Pack disp finTBPOrderType class.
Definition finTBPOrder_finOrderType :=
  @FinTotal.Pack disp finTBPOrderType class.
Definition finMeetSemilattice_bOrderType :=
  @BTotal.Pack disp finMeetSemilatticeType class.
Definition finMeetSemilattice_tOrderType :=
  @TTotal.Pack disp finMeetSemilatticeType class.
Definition finMeetSemilattice_tbOrderType :=
  @TBTotal.Pack disp finMeetSemilatticeType class.
Definition finBMeetSemilattice_orderType :=
  @Total.Pack disp finBMeetSemilatticeType class.
Definition finBMeetSemilattice_bOrderType :=
  @BTotal.Pack disp finBMeetSemilatticeType class.
Definition finBMeetSemilattice_tOrderType :=
  @TTotal.Pack disp finBMeetSemilatticeType class.
Definition finBMeetSemilattice_tbOrderType :=
  @TBTotal.Pack disp finBMeetSemilatticeType class.
Definition finBMeetSemilattice_finOrderType :=
  @FinTotal.Pack disp finBMeetSemilatticeType class.
Definition finJoinSemilattice_bOrderType :=
  @BTotal.Pack disp finJoinSemilatticeType class.
Definition finJoinSemilattice_tOrderType :=
  @TTotal.Pack disp finJoinSemilatticeType class.
Definition finJoinSemilattice_tbOrderType :=
  @TBTotal.Pack disp finJoinSemilatticeType class.
Definition finTJoinSemilattice_orderType :=
  @Total.Pack disp finTJoinSemilatticeType class.
Definition finTJoinSemilattice_bOrderType :=
  @BTotal.Pack disp finTJoinSemilatticeType class.
Definition finTJoinSemilattice_tOrderType :=
  @TTotal.Pack disp finTJoinSemilatticeType class.
Definition finTJoinSemilattice_tbOrderType :=
  @TBTotal.Pack disp finTJoinSemilatticeType class.
Definition finTJoinSemilattice_finOrderType :=
  @FinTotal.Pack disp finTJoinSemilatticeType class.
Definition finLattice_bOrderType := @BTotal.Pack disp finLatticeType class.
Definition finLattice_tOrderType := @TTotal.Pack disp finLatticeType class.
Definition finLattice_tbOrderType := @TBTotal.Pack disp finLatticeType class.
Definition finTBLattice_orderType := @Total.Pack disp finTBLatticeType class.
Definition finTBLattice_bOrderType := @BTotal.Pack disp finTBLatticeType class.
Definition finTBLattice_tOrderType := @TTotal.Pack disp finTBLatticeType class.
Definition finTBLattice_tbOrderType :=
  @TBTotal.Pack disp finTBLatticeType class.
Definition finTBLattice_finOrderType :=
  @FinTotal.Pack disp finTBLatticeType class.
Definition finDistrLattice_bOrderType :=
  @BTotal.Pack disp finDistrLatticeType class.
Definition finDistrLattice_tOrderType :=
  @TTotal.Pack disp finDistrLatticeType class.
Definition finDistrLattice_tbOrderType :=
  @TBTotal.Pack disp finDistrLatticeType class.
Definition finTBDistrLattice_orderType :=
  @Total.Pack disp finTBDistrLatticeType class.
Definition finTBDistrLattice_bOrderType :=
  @BTotal.Pack disp finTBDistrLatticeType class.
Definition finTBDistrLattice_tOrderType :=
  @TTotal.Pack disp finTBDistrLatticeType class.
Definition finTBDistrLattice_tbOrderType :=
  @TBTotal.Pack disp finTBDistrLatticeType class.
Definition finTBDistrLattice_finOrderType :=
  @FinTotal.Pack disp finTBDistrLatticeType class.
Definition finOrder_bPOrderType := @BPOrder.Pack disp finOrderType class.
Definition finOrder_tPOrderType := @TPOrder.Pack disp finOrderType class.
Definition finOrder_tbPOrderType := @TBPOrder.Pack disp finOrderType class.
Definition finOrder_bMeetSemilatticeType :=
  @BMeetSemilattice.Pack disp finOrderType class.
Definition finOrder_tMeetSemilatticeType :=
  @TMeetSemilattice.Pack disp finOrderType class.
Definition finOrder_tbMeetSemilatticeType :=
  @TBMeetSemilattice.Pack disp finOrderType class.
Definition finOrder_bJoinSemilatticeType :=
  @BJoinSemilattice.Pack disp finOrderType class.
Definition finOrder_tJoinSemilatticeType :=
  @TJoinSemilattice.Pack disp finOrderType class.
Definition finOrder_tbJoinSemilatticeType :=
  @TBJoinSemilattice.Pack disp finOrderType class.
Definition finOrder_bLatticeType := @BLattice.Pack disp finOrderType class.
Definition finOrder_tLatticeType := @TLattice.Pack disp finOrderType class.
Definition finOrder_tbLatticeType := @TBLattice.Pack disp finOrderType class.
Definition finOrder_bDistrLatticeType :=
  @BDistrLattice.Pack disp finOrderType class.
Definition finOrder_tDistrLatticeType :=
  @TDistrLattice.Pack disp finOrderType class.
Definition finOrder_tbDistrLatticeType :=
  @TBDistrLattice.Pack disp finOrderType class.
Definition finOrder_bOrderType := @BTotal.Pack disp finOrderType class.
Definition finOrder_tOrderType := @TTotal.Pack disp finOrderType class.
Definition finOrder_tbOrderType := @TBTotal.Pack disp finOrderType class.
End ClassDef.

Module Exports.
Coercion base : class_of >-> TBTotal.class_of.
Coercion base2 : class_of >-> FinTBDistrLattice.class_of.
Coercion base3 : class_of >-> FinTotal.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion countType : type >-> Countable.type.
Coercion finType : type >-> Finite.type.
Coercion porderType : type >-> POrder.type.
Coercion bPOrderType : type >-> BPOrder.type.
Coercion tPOrderType : type >-> TPOrder.type.
Coercion tbPOrderType : type >-> TBPOrder.type.
Coercion finPOrderType : type >-> FinPOrder.type.
Coercion finBPOrderType : type >-> FinBPOrder.type.
Coercion finTPOrderType : type >-> FinTPOrder.type.
Coercion finTBPOrderType : type >-> FinTBPOrder.type.
Coercion meetSemilatticeType : type >-> MeetSemilattice.type.
Coercion bMeetSemilatticeType : type >-> BMeetSemilattice.type.
Coercion tMeetSemilatticeType : type >-> TMeetSemilattice.type.
Coercion tbMeetSemilatticeType : type >-> TBMeetSemilattice.type.
Coercion finMeetSemilatticeType : type >-> FinMeetSemilattice.type.
Coercion finBMeetSemilatticeType : type >-> FinBMeetSemilattice.type.
Coercion joinSemilatticeType : type >-> JoinSemilattice.type.
Coercion bJoinSemilatticeType : type >-> BJoinSemilattice.type.
Coercion tJoinSemilatticeType : type >-> TJoinSemilattice.type.
Coercion tbJoinSemilatticeType : type >-> TBJoinSemilattice.type.
Coercion finJoinSemilatticeType : type >-> FinJoinSemilattice.type.
Coercion finTJoinSemilatticeType : type >-> FinTJoinSemilattice.type.
Coercion latticeType : type >-> Lattice.type.
Coercion bLatticeType : type >-> BLattice.type.
Coercion tLatticeType : type >-> TLattice.type.
Coercion tbLatticeType : type >-> TBLattice.type.
Coercion finLatticeType : type >-> FinLattice.type.
Coercion finTBLatticeType : type >-> FinTBLattice.type.
Coercion distrLatticeType : type >-> DistrLattice.type.
Coercion bDistrLatticeType : type >-> BDistrLattice.type.
Coercion tDistrLatticeType : type >-> TDistrLattice.type.
Coercion tbDistrLatticeType : type >-> TBDistrLattice.type.
Coercion finDistrLatticeType : type >-> FinDistrLattice.type.
Coercion finTBDistrLatticeType : type >-> FinTBDistrLattice.type.
Coercion orderType : type >-> Total.type.
Coercion bOrderType : type >-> BTotal.type.
Coercion tOrderType : type >-> TTotal.type.
Coercion tbOrderType : type >-> TBTotal.type.
Coercion finOrderType : type >-> FinTotal.type.
Canonical eqType.
Canonical choiceType.
Canonical countType.
Canonical finType.
Canonical porderType.
Canonical bPOrderType.
Canonical tPOrderType.
Canonical tbPOrderType.
Canonical finPOrderType.
Canonical finBPOrderType.
Canonical finTPOrderType.
Canonical finTBPOrderType.
Canonical meetSemilatticeType.
Canonical bMeetSemilatticeType.
Canonical tMeetSemilatticeType.
Canonical tbMeetSemilatticeType.
Canonical finMeetSemilatticeType.
Canonical finBMeetSemilatticeType.
Canonical joinSemilatticeType.
Canonical bJoinSemilatticeType.
Canonical tJoinSemilatticeType.
Canonical tbJoinSemilatticeType.
Canonical finJoinSemilatticeType.
Canonical finTJoinSemilatticeType.
Canonical latticeType.
Canonical bLatticeType.
Canonical tLatticeType.
Canonical tbLatticeType.
Canonical finLatticeType.
Canonical finTBLatticeType.
Canonical distrLatticeType.
Canonical bDistrLatticeType.
Canonical tDistrLatticeType.
Canonical tbDistrLatticeType.
Canonical finDistrLatticeType.
Canonical finTBDistrLatticeType.
Canonical orderType.
Canonical bOrderType.
Canonical tOrderType.
Canonical tbOrderType.
Canonical finOrderType.
Canonical count_bOrderType.
Canonical count_tOrderType.
Canonical count_tbOrderType.
Canonical fin_bOrderType.
Canonical fin_tOrderType.
Canonical fin_tbOrderType.
Canonical finPOrder_bOrderType.
Canonical finPOrder_tOrderType.
Canonical finPOrder_tbOrderType.
Canonical finBPOrder_orderType.
Canonical finBPOrder_bOrderType.
Canonical finBPOrder_tOrderType.
Canonical finBPOrder_tbOrderType.
Canonical finBPOrder_finOrderType.
Canonical finTPOrder_orderType.
Canonical finTPOrder_bOrderType.
Canonical finTPOrder_tOrderType.
Canonical finTPOrder_tbOrderType.
Canonical finTPOrder_finOrderType.
Canonical finTBPOrder_orderType.
Canonical finTBPOrder_bOrderType.
Canonical finTBPOrder_tOrderType.
Canonical finTBPOrder_tbOrderType.
Canonical finTBPOrder_finOrderType.
Canonical finMeetSemilattice_bOrderType.
Canonical finMeetSemilattice_tOrderType.
Canonical finMeetSemilattice_tbOrderType.
Canonical finBMeetSemilattice_orderType.
Canonical finBMeetSemilattice_bOrderType.
Canonical finBMeetSemilattice_tOrderType.
Canonical finBMeetSemilattice_tbOrderType.
Canonical finBMeetSemilattice_finOrderType.
Canonical finJoinSemilattice_bOrderType.
Canonical finJoinSemilattice_tOrderType.
Canonical finJoinSemilattice_tbOrderType.
Canonical finTJoinSemilattice_orderType.
Canonical finTJoinSemilattice_bOrderType.
Canonical finTJoinSemilattice_tOrderType.
Canonical finTJoinSemilattice_tbOrderType.
Canonical finTJoinSemilattice_finOrderType.
Canonical finLattice_bOrderType.
Canonical finLattice_tOrderType.
Canonical finLattice_tbOrderType.
Canonical finTBLattice_orderType.
Canonical finTBLattice_bOrderType.
Canonical finTBLattice_tOrderType.
Canonical finTBLattice_tbOrderType.
Canonical finTBLattice_finOrderType.
Canonical finDistrLattice_bOrderType.
Canonical finDistrLattice_tOrderType.
Canonical finDistrLattice_tbOrderType.
Canonical finTBDistrLattice_orderType.
Canonical finTBDistrLattice_bOrderType.
Canonical finTBDistrLattice_tOrderType.
Canonical finTBDistrLattice_tbOrderType.
Canonical finTBDistrLattice_finOrderType.
Canonical finOrder_bPOrderType.
Canonical finOrder_tPOrderType.
Canonical finOrder_tbPOrderType.
Canonical finOrder_bMeetSemilatticeType.
Canonical finOrder_tMeetSemilatticeType.
Canonical finOrder_tbMeetSemilatticeType.
Canonical finOrder_bJoinSemilatticeType.
Canonical finOrder_tJoinSemilatticeType.
Canonical finOrder_tbJoinSemilatticeType.
Canonical finOrder_bLatticeType.
Canonical finOrder_tLatticeType.
Canonical finOrder_tbLatticeType.
Canonical finOrder_bDistrLatticeType.
Canonical finOrder_tDistrLatticeType.
Canonical finOrder_tbDistrLatticeType.
Canonical finOrder_bOrderType.
Canonical finOrder_tOrderType.
Canonical finOrder_tbOrderType.
Notation finTBOrderType := type.
Notation "[ 'finTBOrderType' 'of' T ]" := (@pack T _ _ _ id _ _ id)
  (at level 0, format "[ 'finTBOrderType'  'of'  T ]") : form_scope.
End Exports.

End FinTBTotal.
Import FinTBTotal.Exports.

Module Import DualOrder.
Section DualOrder.

Canonical dual_eqType (T : eqType) := EqType T [eqMixin of T^d].
Canonical dual_choiceType (T : choiceType) := [choiceType of T^d].
Canonical dual_countType (T : countType) := [countType of T^d].
Canonical dual_finType (T : finType) := [finType of T^d].

Context {disp : unit}.

Canonical dual_porderType (T : porderType disp) :=
  POrderType (dual_display disp) T^d
             (RelOrder.POrder.class (RelOrder.DualPOrder.dual_pOrder T)).
Canonical dual_tPOrderType (T : bPOrderType disp) :=
  TPOrderType T^d (RelOrder.TPOrder.class (RelOrder.DualOrder.dual_tPOrder T)).
Canonical dual_bPOrderType (T : tPOrderType disp) :=
  BPOrderType T^d (RelOrder.BPOrder.class (RelOrder.DualOrder.dual_bPOrder T)).
Canonical dual_tbPOrderType (T : tbPOrderType disp) := [tbPOrderType of T^d].
Canonical dual_meetSemilatticeType (T : joinSemilatticeType disp) :=
  MeetSemilatticeType
    T^d (RelOrder.Meet.class (RelOrder.DualOrder.dual_meetOrder T)).
Canonical dual_bMeetSemilatticeType (T : tJoinSemilatticeType disp) :=
  [bMeetSemilatticeType of T^d].
Canonical dual_tMeetSemilatticeType (T : bJoinSemilatticeType disp) :=
  [tMeetSemilatticeType of T^d].
Canonical dual_tbMeetSemilatticeType (T : tbJoinSemilatticeType disp) :=
  [tbMeetSemilatticeType of T^d].
Canonical dual_joinSemilatticeType (T : meetSemilatticeType disp) :=
  JoinSemilatticeType
    T^d (RelOrder.Join.class (RelOrder.DualOrder.dual_joinOrder T)).
Canonical dual_bJoinSemilatticeType (T : tMeetSemilatticeType disp) :=
  [bJoinSemilatticeType of T^d].
Canonical dual_tJoinSemilatticeType (T : bMeetSemilatticeType disp) :=
  [tJoinSemilatticeType of T^d].
Canonical dual_tbJoinSemilatticeType (T : tbMeetSemilatticeType disp) :=
  [tbJoinSemilatticeType of T^d].
Canonical dual_latticeType (T : latticeType disp) := [latticeType of T^d].
Canonical dual_bLatticeType (T : tLatticeType disp) := [bLatticeType of T^d].
Canonical dual_tLatticeType (T : bLatticeType disp) := [tLatticeType of T^d].
Canonical dual_tbLatticeType (T : tbLatticeType disp) := [tbLatticeType of T^d].
Canonical dual_distrLatticeType (T : distrLatticeType disp) :=
  DistrLatticeType
    T^d (RelOrder.DistrLattice.class (RelOrder.DualOrder.dual_distrLattice T)).
Canonical dual_bDistrLatticeType (T : tDistrLatticeType disp) :=
  [bDistrLatticeType of T^d].
Canonical dual_tDistrLatticeType (T : bDistrLatticeType disp) :=
  [tDistrLatticeType of T^d].
Canonical dual_tbDistrLatticeType (T : tbDistrLatticeType disp) :=
  [tbDistrLatticeType of T^d].
Canonical dual_orderType (T : orderType disp) :=
  OrderType T^d (RelOrder.Total.class (RelOrder.DualOrder.dual_totalOrder T)).
Canonical dual_bOrderType (T : tOrderType disp) := [bOrderType of T^d].
Canonical dual_tOrderType (T : bOrderType disp) := [tOrderType of T^d].
Canonical dual_tbOrderType (T : tbOrderType disp) := [tbOrderType of T^d].
Canonical dual_finPOrderType (T : finPOrderType disp) :=
  [finPOrderType of T^d].
Canonical dual_finBPOrderType (T : finTPOrderType disp) :=
  [finBPOrderType of T^d].
Canonical dual_finTPOrderType (T : finBPOrderType disp) :=
  [finTPOrderType of T^d].
Canonical dual_finTBPOrderType (T : finTBPOrderType disp) :=
  [finTBPOrderType of T^d].
Canonical dual_finMeetSemilatticeType (T : finJoinSemilatticeType disp) :=
  [finMeetSemilatticeType of T^d].
Canonical dual_finBMeetSemilatticeType (T : finTJoinSemilatticeType disp) :=
  [finBMeetSemilatticeType of T^d].
Canonical dual_finJoinSemilatticeType (T : finMeetSemilatticeType disp) :=
  [finJoinSemilatticeType of T^d].
Canonical dual_finTJoinSemilatticeType (T : finBMeetSemilatticeType disp) :=
  [finTJoinSemilatticeType of T^d].
Canonical dual_finLatticeType (T : finLatticeType disp) :=
  [finLatticeType of T^d].
Canonical dual_finTBLatticeType (T : finTBLatticeType disp) :=
  [finTBLatticeType of T^d].
Canonical dual_finDistrLatticeType (T : finDistrLatticeType disp) :=
  [finDistrLatticeType of T^d].
Canonical dual_finTBDistrLatticeType (T : finTBDistrLatticeType disp) :=
  [finTBDistrLatticeType of T^d].
Canonical dual_finOrderType (T : finOrderType disp) :=
  [finOrderType of T^d].
Canonical dual_finTBOrderType (T : finTBOrderType disp) :=
  [finTBOrderType of T^d].

Lemma leEdual (T : porderType disp) (x y : T) : (x <=^d y :> T^d) = (y <= x).
Proof. by []. Qed.

Lemma ltEdual (T : porderType disp) (x y : T) : (x <^d y :> T^d) = (y < x).
Proof. by []. Qed.

Lemma botEdual (T : bPOrderType disp) : (1 : T^d) = (0 : T). Proof. by []. Qed.

Lemma topEdual (T : tPOrderType disp) : (0 : T^d) = (1 : T). Proof. by []. Qed.

Lemma meetEdual (T : joinSemilatticeType disp) x y :
  ((x : T^d) `&^d` y) = (x `|` y).
Proof. by []. Qed.

Lemma joinEdual (T : meetSemilatticeType disp) x y :
  ((x : T^d) `|^d` y) = (x `&` y).
Proof. by []. Qed.

End DualOrder.
End DualOrder.

(**********)
(* THEORY *)
(**********)

Module Import POrderTheory.
Section POrderTheory.

Context {disp : unit} {T : porderType disp}.

Implicit Types (x y : T) (s : seq T).

Lemma geE x y : ge x y = (y <= x). Proof. by []. Qed.
Lemma gtE x y : gt x y = (y < x). Proof. by []. Qed.

Lemma lexx x : x <= x. Proof. exact: lexx. Qed.
Hint Resolve lexx : core.

Definition le_refl : reflexive le := lexx.
Definition ge_refl : reflexive ge := lexx.

Lemma le_anti: antisymmetric (<=%O : rel T). Proof. exact: le_anti. Qed.
Lemma ge_anti: antisymmetric (>=%O : rel T). Proof. exact: ge_anti. Qed.
Lemma le_trans: transitive (<=%O : rel T). Proof. exact: le_trans. Qed.
Lemma ge_trans: transitive (>=%O : rel T). Proof. exact: ge_trans. Qed.

Lemma le_le_trans x y z t : z <= x -> y <= t -> x <= y -> z <= t.
Proof. by move=> + /(le_trans _)/[apply]; apply: le_trans. Qed.

Lemma lt_def x y: (x < y) = (y != x) && (x <= y).
Proof. exact: lt_def. Qed.

Lemma lt_neqAle x y: (x < y) = (x != y) && (x <= y).
Proof. exact: lt_neqAle. Qed.

Lemma ltxx x: x < x = false. Proof. exact: ltxx. Qed.

Definition lt_irreflexive : irreflexive lt := ltxx.
Hint Resolve lt_irreflexive : core.

Definition ltexx := (lexx, ltxx).

Lemma le_eqVlt x y: (x <= y) = (x == y) || (x < y). Proof. exact: le_eqVlt. Qed.
Lemma lt_eqF x y: x < y -> x == y = false. Proof. exact: lt_eqF. Qed.
Lemma gt_eqF x y : y < x -> x == y = false. Proof. exact: gt_eqF. Qed.
Lemma eq_le x y: (x == y) = (x <= y <= x). Proof. exact: eq_le. Qed.
Lemma ltW x y: x < y -> x <= y. Proof. exact: ltW. Qed.

Lemma lt_le_trans y x z: x < y -> y <= z -> x < z.
Proof. exact: lt_le_trans. Qed.

Lemma lt_trans: transitive (<%O : rel T).
Proof. exact: lt_trans. Qed.

Lemma le_lt_trans y x z: x <= y -> y < z -> x < z.
Proof. exact: le_lt_trans. Qed.

Lemma lt_nsym x y : x < y -> y < x -> False.
Proof. exact: lt_nsym. Qed.

Lemma lt_asym x y : x < y < x = false.
Proof. exact: lt_asym. Qed.

Lemma le_gtF x y: x <= y -> y < x = false.
Proof. exact: le_gtF. Qed.

Lemma lt_geF x y : (x < y) -> y <= x = false.
Proof. exact: lt_geF. Qed.

Definition lt_gtF x y hxy := le_gtF (@ltW x y hxy).

Lemma lt_leAnge x y : (x < y) = (x <= y) && ~~ (y <= x).
Proof. exact: lt_leAnge. Qed.

Lemma lt_le_asym x y : x < y <= x = false.
Proof. exact: lt_le_asym. Qed.

Lemma le_lt_asym x y : x <= y < x = false.
Proof. exact: le_lt_asym. Qed.

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
Proof. exact: lt_sorted_uniq_le. Qed.

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
Proof. exact: le_sorted_ltn_nth. Qed.

Lemma le_sorted_leq_nth (x0 : T) (s : seq T) : sorted <=%O s ->
  {in [pred n | (n < size s)%N] &,
    {homo nth x0 s : i j / (i <= j)%N >-> i <= j}}.
Proof. exact: le_sorted_leq_nth. Qed.

Lemma lt_sorted_leq_nth (x0 : T) (s : seq T) : sorted <%O s ->
  {in [pred n | (n < size s)%N] &,
    {mono nth x0 s : i j / (i <= j)%N >-> i <= j}}.
Proof. exact: lt_sorted_leq_nth. Qed.

Lemma lt_sorted_ltn_nth (x0 : T) (s : seq T) : sorted <%O s ->
  {in [pred n | (n < size s)%N] &,
    {mono nth x0 s : i j / (i < j)%N >-> i < j}}.
Proof. exact: lt_sorted_ltn_nth. Qed.

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
Proof. exact: lt_sorted_eq. Qed.

Lemma le_sorted_eq s1 s2 :
  sorted <=%O s1 -> sorted <=%O s2 -> perm_eq s1 s2 -> s1 = s2.
Proof. exact: le_sorted_eq. Qed.

Lemma filter_lt_nth x0 s i : sorted <%O s -> (i < size s)%N ->
  [seq x <- s | x < nth x0 s i] = take i s.
Proof. exact: filter_lt_nth. Qed.

Lemma count_lt_nth x0 s i : sorted <%O s -> (i < size s)%N ->
  count (< nth x0 s i) s = i.
Proof. exact: count_lt_nth. Qed.

Lemma filter_le_nth x0 s i : sorted <%O s -> (i < size s)%N ->
  [seq x <- s | x <= nth x0 s i] = take i.+1 s.
Proof. exact: filter_le_nth. Qed.

Lemma count_le_nth x0 s i : sorted <%O s -> (i < size s)%N ->
  count (<= nth x0 s i) s = i.+1.
Proof. exact: count_le_nth. Qed.

Lemma count_lt_le_mem x s : (count (< x) s < count (<= x) s)%N = (x \in s).
Proof. exact: count_lt_le_mem. Qed.

Lemma sorted_filter_lt x s :
  sorted <=%O s -> [seq y <- s | y < x] = take (count (< x) s) s.
Proof. exact: sorted_filter_lt. Qed.

Lemma sorted_filter_le x s :
  sorted <=%O s -> [seq y <- s | y <= x] = take (count (<= x) s) s.
Proof. exact: sorted_filter_le. Qed.

Lemma nth_count_le x x0 s i : sorted <=%O s ->
  (i < count (<= x) s)%N -> nth x0 s i <= x.
Proof. exact: nth_count_le. Qed.

Lemma nth_count_lt x x0 s i : sorted <=%O s ->
  (i < count (< x) s)%N -> nth x0 s i < x.
Proof. exact: nth_count_lt. Qed.

Lemma sort_le_id s : sorted <=%O s -> sort <=%O s = s.
Proof. exact: sort_le_id. Qed.

Lemma sort_lt_id s : sorted <%O s -> sort <%O s = s.
Proof. exact/sorted_sort/lt_trans. Qed.

Lemma comparable_leNgt x y : x >=< y -> (x <= y) = ~~ (y < x).
Proof. exact: comparable_leNgt. Qed.

Lemma comparable_ltNge x y : x >=< y -> (x < y) = ~~ (y <= x).
Proof. exact: comparable_ltNge. Qed.

Lemma comparable_ltgtP x y : x >=< y ->
  compare x y (min y x) (min x y) (max y x) (max x y)
  (y == x) (x == y) (x >= y) (x <= y) (x > y) (x < y).
Proof. exact: comparable_ltgtP. Qed.

Lemma comparable_leP x y : x >=< y ->
  le_xor_gt x y (min y x) (min x y) (max y x) (max x y) (x <= y) (y < x).
Proof. exact: comparable_leP. Qed.

Lemma comparable_ltP x y : x >=< y ->
  lt_xor_ge x y (min y x) (min x y) (max y x) (max x y) (y <= x) (x < y).
Proof. exact: comparable_ltP. Qed.

Lemma comparable_sym x y : (y >=< x) = (x >=< y).
Proof. exact: comparable_sym. Qed.

Lemma comparablexx x : x >=< x.
Proof. exact: comparablexx. Qed.

Lemma incomparable_eqF x y : (x >< y) -> (x == y) = false.
Proof. exact: incomparable_eqF. Qed.

Lemma incomparable_leF x y : (x >< y) -> (x <= y) = false.
Proof. exact: incomparable_leF. Qed.

Lemma incomparable_ltF x y : (x >< y) -> (x < y) = false.
Proof. exact: incomparable_ltF. Qed.

Lemma comparableP x y : incompare x y
  (min y x) (min x y) (max y x) (max x y)
  (y == x) (x == y) (x >= y) (x <= y) (x > y) (x < y)
  (y >=< x) (x >=< y).
Proof. exact: comparableP. Qed.

Lemma le_comparable (x y : T) : x <= y -> x >=< y.
Proof. exact: le_comparable. Qed.

Lemma lt_comparable (x y : T) : x < y -> x >=< y.
Proof. exact: lt_comparable. Qed.

Lemma ge_comparable (x y : T) : y <= x -> x >=< y.
Proof. exact: ge_comparable. Qed.

Lemma gt_comparable (x y : T) : y < x -> x >=< y.
Proof. exact: gt_comparable. Qed.

(* leif *)

Lemma leifP x y C : reflect (x <= y ?= iff C) (if C then x == y else x < y).
Proof. exact: leifP. Qed.

Lemma leif_refl x C : reflect (x <= x ?= iff C) C.
Proof. exact: leif_refl. Qed.

Lemma leif_trans x1 x2 x3 C12 C23 :
  x1 <= x2 ?= iff C12 -> x2 <= x3 ?= iff C23 -> x1 <= x3 ?= iff C12 && C23.
Proof. exact: leif_trans. Qed.

Lemma leif_le x y : x <= y -> x <= y ?= iff (x >= y).
Proof. exact: leif_le. Qed.

Lemma leif_eq x y : x <= y -> x <= y ?= iff (x == y).
Proof. by []. Qed.

Lemma ge_leif x y C : x <= y ?= iff C -> (y <= x) = C.
Proof. exact: ge_leif. Qed.

Lemma lt_leif x y C : x <= y ?= iff C -> (x < y) = ~~ C.
Proof. exact: lt_leif. Qed.

Lemma ltNleif x y C : x <= y ?= iff ~~ C -> (x < y) = C.
Proof. exact: ltNleif. Qed.

Lemma eq_leif x y C : x <= y ?= iff C -> (x == y) = C.
Proof. exact: eq_leif. Qed.

Lemma eqTleif x y C : x <= y ?= iff C -> C -> x = y.
Proof. exact: eqTleif. Qed.

(* lteif *)

Lemma lteif_trans x y z C1 C2 :
  x < y ?<= if C1 -> y < z ?<= if C2 -> x < z ?<= if C1 && C2.
Proof. exact: lteif_trans. Qed.

Lemma lteif_anti C1 C2 x y :
  (x < y ?<= if C1) && (y < x ?<= if C2) = C1 && C2 && (x == y).
Proof. exact: lteif_anti. Qed.

Lemma lteifxx x C : (x < x ?<= if C) = C.
Proof. exact: lteifxx. Qed.

Lemma lteifNF x y C : y < x ?<= if ~~ C -> x < y ?<= if C = false.
Proof. exact: lteifNF. Qed.

Lemma lteifS x y C : x < y -> x < y ?<= if C.
Proof. exact: lteifS. Qed.

Lemma lteifT x y : x < y ?<= if true = (x <= y). Proof. by []. Qed.

Lemma lteifF x y : x < y ?<= if false = (x < y). Proof. by []. Qed.

Lemma lteif_orb x y : {morph lteif x y : p q / p || q}.
Proof. exact: lteif_orb. Qed.

Lemma lteif_andb x y : {morph lteif x y : p q / p && q}.
Proof. exact: lteif_andb. Qed.

Lemma lteif_imply C1 C2 x y : C1 ==> C2 -> x < y ?<= if C1 -> x < y ?<= if C2.
Proof. exact: lteif_imply. Qed.

Lemma lteifW C x y : x < y ?<= if C -> x <= y.
Proof. exact: lteifW. Qed.

Lemma ltrW_lteif C x y : x < y -> x < y ?<= if C.
Proof. exact: ltrW_lteif. Qed.

Lemma lteifN C x y : x < y ?<= if ~~ C -> ~~ (y < x ?<= if C).
Proof. exact: lteifN. Qed.

(* min and max *)

Lemma minElt x y : min x y = if x < y then x else y. Proof. by []. Qed.
Lemma maxElt x y : max x y = if x < y then y else x. Proof. by []. Qed.

Lemma minEle x y : min x y = if x <= y then x else y.
Proof. exact: minEle. Qed.

Lemma maxEle x y : max x y = if x <= y then y else x.
Proof. exact: maxEle. Qed.

Lemma comparable_minEgt x y : x >=< y -> min x y = if x > y then y else x.
Proof. exact: comparable_minEgt. Qed.
Lemma comparable_maxEgt x y : x >=< y -> max x y = if x > y then x else y.
Proof. exact: comparable_maxEgt. Qed.
Lemma comparable_minEge x y : x >=< y -> min x y = if x >= y then y else x.
Proof. exact: comparable_minEge. Qed.
Lemma comparable_maxEge x y : x >=< y -> max x y = if x >= y then x else y.
Proof. exact: comparable_maxEge. Qed.

Lemma min_l x y : x <= y -> min x y = x. Proof. exact: min_l. Qed.
Lemma min_r x y : y <= x -> min x y = y. Proof. exact: min_r. Qed.
Lemma max_l x y : y <= x -> max x y = x. Proof. exact: max_l. Qed.
Lemma max_r x y : x <= y -> max x y = y. Proof. exact: max_r. Qed.

Lemma minxx : idempotent (min : T -> T -> T). Proof. exact: minxx. Qed.
Lemma maxxx : idempotent (max : T -> T -> T). Proof. exact: maxxx. Qed.

Lemma eq_minl x y : (min x y == x) = (x <= y). Proof. exact: eq_minl. Qed.
Lemma eq_maxr x y : (max x y == y) = (x <= y). Proof. exact: eq_maxr. Qed.

Lemma min_idPl x y : reflect (min x y = x) (x <= y).
Proof. exact: min_idPl. Qed.

Lemma max_idPr x y : reflect (max x y = y) (x <= y).
Proof. exact: max_idPr. Qed.

Lemma min_minKx x y : min (min x y) y = min x y. Proof. exact: min_minKx. Qed.
Lemma min_minxK x y : min x (min x y) = min x y. Proof. exact: min_minxK. Qed.
Lemma max_maxKx x y : max (max x y) y = max x y. Proof. exact: max_maxKx. Qed.
Lemma max_maxxK x y : max x (max x y) = max x y. Proof. exact: max_maxxK. Qed.

Lemma comparable_minl z : {in >=< z &, forall x y, min x y >=< z}.
Proof. exact: comparable_minl. Qed.

Lemma comparable_minr z : {in >=<%O z &, forall x y, z >=< min x y}.
Proof. exact: comparable_minr. Qed.

Lemma comparable_maxl z : {in >=< z &, forall x y, max x y >=< z}.
Proof. exact: comparable_maxl. Qed.

Lemma comparable_maxr z : {in >=<%O z &, forall x y, z >=< max x y}.
Proof. exact: comparable_maxr. Qed.

Section Comparable2.
Variables (z x y : T) (cmp_xy : x >=< y).

Lemma comparable_minC : min x y = min y x. Proof. exact: comparable_minC. Qed.
Lemma comparable_maxC : max x y = max y x. Proof. exact: comparable_maxC. Qed.

Lemma comparable_eq_minr : (min x y == y) = (y <= x).
Proof. exact: comparable_eq_minr. Qed.

Lemma comparable_eq_maxl : (max x y == x) = (y <= x).
Proof. exact: comparable_eq_maxl. Qed.

Lemma comparable_min_idPr : reflect (min x y = y) (y <= x).
Proof. exact: comparable_min_idPr. Qed.

Lemma comparable_max_idPl : reflect (max x y = x) (y <= x).
Proof. exact: comparable_max_idPl. Qed.

Lemma comparable_le_minr : (z <= min x y) = (z <= x) && (z <= y).
Proof. exact: comparable_le_minr. Qed.

Lemma comparable_le_minl : (min x y <= z) = (x <= z) || (y <= z).
Proof. exact: comparable_le_minl. Qed.

Lemma comparable_lt_minr : (z < min x y) = (z < x) && (z < y).
Proof. exact: comparable_lt_minr. Qed.

Lemma comparable_lt_minl : (min x y < z) = (x < z) || (y < z).
Proof. exact: comparable_lt_minl. Qed.

Lemma comparable_le_maxr : (z <= max x y) = (z <= x) || (z <= y).
Proof. exact: comparable_le_maxr. Qed.

Lemma comparable_le_maxl : (max x y <= z) = (x <= z) && (y <= z).
Proof. exact: comparable_le_maxl. Qed.

Lemma comparable_lt_maxr : (z < max x y) = (z < x) || (z < y).
Proof. exact: comparable_lt_maxr. Qed.

Lemma comparable_lt_maxl : (max x y < z) = (x < z) && (y < z).
Proof. exact: comparable_lt_maxl. Qed.

Lemma comparable_minxK : max (min x y) y = y.
Proof. exact: comparable_minxK. Qed.

Lemma comparable_minKx : max x (min x y) = x.
Proof. exact: comparable_minKx. Qed.

Lemma comparable_maxxK : min (max x y) y = y.
Proof. exact: comparable_maxxK. Qed.

Lemma comparable_maxKx : min x (max x y) = x.
Proof. exact: comparable_maxKx. Qed.

Lemma comparable_lteifNE C : x >=< y -> x < y ?<= if ~~ C = ~~ (y < x ?<= if C).
Proof. exact: comparable_lteifNE. Qed.

Lemma comparable_lteif_minr C :
  (z < min x y ?<= if C) = (z < x ?<= if C) && (z < y ?<= if C).
Proof. exact: comparable_lteif_minr. Qed.

Lemma comparable_lteif_minl C :
  (min x y < z ?<= if C) = (x < z ?<= if C) || (y < z ?<= if C).
Proof. exact: comparable_lteif_minl. Qed.

Lemma comparable_lteif_maxr C :
  (z < max x y ?<= if C) = (z < x ?<= if C) || (z < y ?<= if C).
Proof. exact: comparable_lteif_maxr. Qed.

Lemma comparable_lteif_maxl C :
  (max x y < z ?<= if C) = (x < z ?<= if C) && (y < z ?<= if C).
Proof. exact: comparable_lteif_maxl. Qed.

End Comparable2.

Section Comparable3.
Variables (x y z : T) (cmp_xy : x >=< y) (cmp_xz : x >=< z) (cmp_yz : y >=< z).
Let P := comparableP.

Lemma comparable_minA : min x (min y z) = min (min x y) z.
Proof. exact: comparable_minA. Qed.

Lemma comparable_maxA : max x (max y z) = max (max x y) z.
Proof. exact: comparable_maxA. Qed.

Lemma comparable_max_minl : max (min x y) z = min (max x z) (max y z).
Proof. exact: comparable_max_minl. Qed.

Lemma comparable_min_maxl : min (max x y) z = max (min x z) (min y z).
Proof. exact: comparable_min_maxl. Qed.

End Comparable3.

Lemma comparable_minAC x y z : x >=< y -> x >=< z -> y >=< z ->
  min (min x y) z = min (min x z) y.
Proof. exact: comparable_minAC. Qed.

Lemma comparable_maxAC x y z : x >=< y -> x >=< z -> y >=< z ->
  max (max x y) z = max (max x z) y.
Proof. exact: comparable_maxAC. Qed.

Lemma comparable_minCA x y z : x >=< y -> x >=< z -> y >=< z ->
  min x (min y z) = min y (min x z).
Proof. exact: comparable_minCA. Qed.

Lemma comparable_maxCA x y z : x >=< y -> x >=< z -> y >=< z ->
  max x (max y z) = max y (max x z).
Proof. exact: comparable_maxCA. Qed.

Lemma comparable_minACA x y z t :
    x >=< y -> x >=< z -> x >=< t -> y >=< z -> y >=< t -> z >=< t ->
  min (min x y) (min z t) = min (min x z) (min y t).
Proof. exact: comparable_minACA. Qed.

Lemma comparable_maxACA x y z t :
    x >=< y -> x >=< z -> x >=< t -> y >=< z -> y >=< t -> z >=< t ->
  max (max x y) (max z t) = max (max x z) (max y t).
Proof. exact: comparable_maxACA. Qed.

Lemma comparable_max_minr x y z : x >=< y -> x >=< z -> y >=< z ->
  max x (min y z) = min (max x y) (max x z).
Proof. exact: comparable_max_minr. Qed.

Lemma comparable_min_maxr x y z : x >=< y -> x >=< z -> y >=< z ->
  min x (max y z) = max (min x y) (min x z).
Proof. exact: comparable_min_maxr. Qed.

Section ArgExtremum.

Context (I : finType) (i0 : I) (P : {pred I}) (F : I -> T) (Pi0 : P i0).
Hypothesis F_comparable : {in P &, forall i j, F i >=< F j}.

Lemma comparable_arg_minP : extremum_spec <=%O P F (arg_min i0 P F).
Proof. exact: comparable_arg_minP. Qed.

Lemma comparable_arg_maxP : extremum_spec >=%O P F (arg_max i0 P F).
Proof. exact: comparable_arg_maxP. Qed.

End ArgExtremum.

(* monotonicity *)

Lemma mono_in_leif (A : {pred T}) (f : T -> T) C :
   {in A &, {mono f : x y / x <= y}} ->
  {in A &, forall x y, (f x <= f y ?= iff C) = (x <= y ?= iff C)}.
Proof. exact: mono_in_leif. Qed.

Lemma mono_leif (f : T -> T) C :
    {mono f : x y / x <= y} ->
  forall x y, (f x <= f y ?= iff C) = (x <= y ?= iff C).
Proof. exact: mono_leif. Qed.

Lemma nmono_in_leif (A : {pred T}) (f : T -> T) C :
    {in A &, {mono f : x y /~ x <= y}} ->
  {in A &, forall x y, (f x <= f y ?= iff C) = (y <= x ?= iff C)}.
Proof. exact: nmono_in_leif. Qed.

Lemma nmono_leif (f : T -> T) C : {mono f : x y /~ x <= y} ->
  forall x y, (f x <= f y ?= iff C) = (y <= x ?= iff C).
Proof. exact: nmono_leif. Qed.

Lemma comparable_bigl x x0 op I (P : pred I) F (s : seq I) :
  {in >=< x &, forall y z, op y z >=< x} -> x0 >=< x ->
  {in P, forall i, F i >=< x} -> \big[op/x0]_(i <- s | P i) F i >=< x.
Proof. exact: comparable_bigl. Qed.

Lemma comparable_bigr x x0 op I (P : pred I) F (s : seq I) :
  {in >=<%O x &, forall y z, x >=< op y z} -> x >=< x0 ->
  {in P, forall i, x >=< F i} -> x >=< \big[op/x0]_(i <- s | P i) F i.
Proof. exact: comparable_bigr. Qed.

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

Section ContraTheory.
Context {disp1 disp2 : unit} {T1 : porderType disp1} {T2 : porderType disp2}.
Implicit Types (x y : T1) (z t : T2) (b : bool) (m n : nat) (P : Prop).

Lemma comparable_contraTle b x y : x >=< y -> (y < x -> ~~ b) -> (b -> x <= y).
Proof. exact: comparable_contraTle. Qed.

Lemma comparable_contraTlt b x y : x >=< y -> (y <= x -> ~~ b) -> (b -> x < y).
Proof. exact: comparable_contraTlt. Qed.

Lemma comparable_contraPle P x y : x >=< y -> (y < x -> ~ P) -> (P -> x <= y).
Proof. exact: comparable_contraPle. Qed.

Lemma comparable_contraPlt P x y : x >=< y -> (y <= x -> ~ P) -> (P -> x < y).
Proof. exact: comparable_contraPlt. Qed.

Lemma comparable_contraNle b x y : x >=< y -> (y < x -> b) -> (~~ b -> x <= y).
Proof. exact: comparable_contraNle. Qed.

Lemma comparable_contraNlt b x y : x >=< y -> (y <= x -> b) -> (~~ b -> x < y).
Proof. exact: comparable_contraNlt. Qed.

Lemma comparable_contra_not_le P x y : x >=< y -> (y < x -> P) -> (~ P -> x <= y).
Proof. exact: comparable_contra_not_le. Qed.

Lemma comparable_contra_not_lt P x y : x >=< y -> (y <= x -> P) -> (~ P -> x < y).
Proof. exact: comparable_contra_not_lt. Qed.

Lemma comparable_contraFle b x y : x >=< y -> (y < x -> b) -> (b = false -> x <= y).
Proof. exact: comparable_contraFle. Qed.

Lemma comparable_contraFlt b x y : x >=< y -> (y <= x -> b) -> (b = false -> x < y).
Proof. exact: comparable_contraFlt. Qed.

Lemma contra_leT b x y : (~~ b -> x < y) -> (y <= x -> b).
Proof. exact: contra_leT. Qed.

Lemma contra_ltT b x y : (~~ b -> x <= y) -> (y < x -> b).
Proof. exact: contra_ltT. Qed.

Lemma contra_leN b x y : (b -> x < y) -> (y <= x -> ~~ b).
Proof. exact: contra_leN. Qed.

Lemma contra_ltN b x y : (b -> x <= y) -> (y < x -> ~~ b).
Proof. exact: contra_ltN. Qed.

Lemma contra_le_not P x y : (P -> x < y) -> (y <= x -> ~ P).
Proof. exact: contra_le_not. Qed.

Lemma contra_lt_not P x y : (P -> x <= y) -> (y < x -> ~ P).
Proof. exact: contra_lt_not. Qed.

Lemma contra_leF b x y : (b -> x < y) -> (y <= x -> b = false).
Proof. exact: contra_leF. Qed.

Lemma contra_ltF b x y : (b -> x <= y) -> (y < x -> b = false).
Proof. exact: contra_ltF. Qed.

Lemma comparable_contra_leq_le m n x y : x >=< y ->
  (y < x -> (n < m)%N) -> ((m <= n)%N -> x <= y).
Proof. exact: comparable_contra_leq_le. Qed.

Lemma comparable_contra_leq_lt m n x y : x >=< y ->
  (y <= x -> (n < m)%N) -> ((m <= n)%N -> x < y).
Proof. exact: comparable_contra_leq_lt. Qed.

Lemma comparable_contra_ltn_le m n x y : x >=< y ->
  (y < x -> (n <= m)%N) -> ((m < n)%N -> x <= y).
Proof. exact: comparable_contra_ltn_le. Qed.

Lemma comparable_contra_ltn_lt m n x y : x >=< y ->
  (y <= x -> (n <= m)%N) -> ((m < n)%N -> x < y).
Proof. exact: comparable_contra_ltn_lt. Qed.

Lemma contra_le_leq x y m n : ((n < m)%N -> y < x) -> (x <= y -> (m <= n)%N).
Proof. exact: contra_le_leq. Qed.

Lemma contra_le_ltn x y m n : ((n <= m)%N -> y < x) -> (x <= y -> (m < n)%N).
Proof. exact: contra_le_ltn. Qed.

Lemma contra_lt_leq x y m n : ((n < m)%N -> y <= x) -> (x < y -> (m <= n)%N).
Proof. exact: contra_lt_leq. Qed.

Lemma contra_lt_ltn x y m n : ((n <= m)%N -> y <= x) -> (x < y -> (m < n)%N).
Proof. exact: contra_lt_ltn. Qed.

Lemma comparable_contra_le x y z t : z >=< t ->
  (t < z -> y < x) -> (x <= y -> z <= t).
Proof. exact: comparable_contra_le. Qed.

Lemma comparable_contra_le_lt x y z t : z >=< t ->
  (t <= z -> y < x) -> (x <= y -> z < t).
Proof. exact: comparable_contra_le_lt. Qed.

Lemma comparable_contra_lt_le x y z t : z >=< t ->
  (t < z -> y <= x) -> (x < y -> z <= t).
Proof. exact: comparable_contra_lt_le. Qed.

Lemma comparable_contra_lt x y z t : z >=< t ->
 (t <= z -> y <= x) -> (x < y -> z < t).
Proof. exact: comparable_contra_lt. Qed.

End ContraTheory.

Section POrderMonotonyTheory.

Context {disp disp' : unit} {T : porderType disp} {T' : porderType disp'}.
Implicit Types (m n p : nat) (x y z : T) (u v w : T').
Variables (D D' : {pred T}) (f : T -> T').

Lemma ltW_homo : {homo f : x y / x < y} -> {homo f : x y / x <= y}.
Proof. exact: ltW_homo. Qed.

Lemma ltW_nhomo : {homo f : x y /~ x < y} -> {homo f : x y /~ x <= y}.
Proof. exact: ltW_nhomo. Qed.

Lemma inj_homo_lt :
  injective f -> {homo f : x y / x <= y} -> {homo f : x y / x < y}.
Proof. exact: inj_homo_lt. Qed.

Lemma inj_nhomo_lt :
  injective f -> {homo f : x y /~ x <= y} -> {homo f : x y /~ x < y}.
Proof. exact: inj_nhomo_lt. Qed.

Lemma inc_inj : {mono f : x y / x <= y} -> injective f.
Proof. exact: inc_inj. Qed.

Lemma dec_inj : {mono f : x y /~ x <= y} -> injective f.
Proof. exact: dec_inj. Qed.

Lemma leW_mono : {mono f : x y / x <= y} -> {mono f : x y / x < y}.
Proof. exact: leW_mono. Qed.

Lemma leW_nmono : {mono f : x y /~ x <= y} -> {mono f : x y /~ x < y}.
Proof. exact: leW_nmono. Qed.

(* Monotony in D D' *)
Lemma ltW_homo_in :
  {in D & D', {homo f : x y / x < y}} -> {in D & D', {homo f : x y / x <= y}}.
Proof. exact: ltW_homo_in. Qed.

Lemma ltW_nhomo_in :
  {in D & D', {homo f : x y /~ x < y}} -> {in D & D', {homo f : x y /~ x <= y}}.
Proof. exact: ltW_nhomo_in. Qed.

Lemma inj_homo_lt_in :
    {in D & D', injective f} ->  {in D & D', {homo f : x y / x <= y}} ->
  {in D & D', {homo f : x y / x < y}}.
Proof. exact: inj_homo_lt_in. Qed.

Lemma inj_nhomo_lt_in :
    {in D & D', injective f} -> {in D & D', {homo f : x y /~ x <= y}} ->
  {in D & D', {homo f : x y /~ x < y}}.
Proof. exact: inj_nhomo_lt_in. Qed.

Lemma inc_inj_in : {in D &, {mono f : x y / x <= y}} -> {in D &, injective f}.
Proof. exact: inc_inj_in. Qed.

Lemma dec_inj_in : {in D &, {mono f : x y /~ x <= y}} -> {in D &, injective f}.
Proof. exact: dec_inj_in. Qed.

Lemma leW_mono_in :
  {in D &, {mono f : x y / x <= y}} -> {in D &, {mono f : x y / x < y}}.
Proof. exact: leW_mono_in. Qed.

Lemma leW_nmono_in :
  {in D &, {mono f : x y /~ x <= y}} -> {in D &, {mono f : x y /~ x < y}}.
Proof. exact: leW_nmono_in. Qed.

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

Module Import BPOrderTheory.
Section BPOrderTheory.
Context {disp : unit} {T : bPOrderType disp}.
Implicit Types (x y : T).

Lemma le0x x : 0 <= x. Proof. exact: le0x. Qed.
Lemma lex0 x : (x <= 0) = (x == 0). Proof. exact: lex0. Qed.
Lemma ltx0 x : (x < 0) = false. Proof. exact: ltx0. Qed.
Lemma lt0x x : (0 < x) = (x != 0). Proof. exact: lt0x. Qed.

Variant eq0_xor_gt0 x : bool -> bool -> Set :=
    Eq0NotPOs : x = 0 -> eq0_xor_gt0 x true false
  | POsNotEq0 : 0 < x -> eq0_xor_gt0 x false true.

Lemma posxP x : eq0_xor_gt0 x (x == 0) (0 < x).
Proof. by rewrite lt0x; have [] := eqVneq; constructor; rewrite ?lt0x. Qed.

End BPOrderTheory.
End BPOrderTheory.

Module Import TPOrderTheory.
Section TPOrderTheory.
Context {disp : unit} {T : tPOrderType disp}.
Implicit Types (x y : T).

Lemma lex1 (x : T) : x <= 1. Proof. exact: lex1. Qed.
Lemma le1x x : (1 <= x) = (x == 1). Proof. exact: le1x. Qed.
Lemma lt1x x : (1 < x) = false. Proof. exact: lt1x. Qed.
Lemma ltx1 x : (x < 1) = (x != 1). Proof. exact: ltx1. Qed.

End TPOrderTheory.
End TPOrderTheory.

#[global] Hint Extern 0 (is_true (0 <= _)) => exact: le0x : core.
#[global] Hint Extern 0 (is_true (_ <= 1)) => exact: lex1 : core.

Module Import MeetTheory.
Section MeetTheory.
Context {disp : unit} {L : meetSemilatticeType disp}.
Implicit Types (x y : L).

Lemma meetC : commutative (@meet _ L). Proof. exact: meetC. Qed.
Lemma meetA : associative (@meet _ L). Proof. exact: meetA. Qed.
Lemma leEmeet x y : (x <= y) = (x `&` y == x). Proof. exact: leEmeet. Qed.

Lemma meetxx : idempotent (@meet _ L). Proof. exact: meetxx. Qed.
Lemma meetAC : right_commutative (@meet _ L). Proof. exact: meetAC. Qed.
Lemma meetCA : left_commutative (@meet _ L). Proof. exact: meetCA. Qed.
Lemma meetACA : interchange (@meet _ L) (@meet _ L). Proof. exact: meetACA. Qed.

Lemma meetKI y x : x `&` (x `&` y) = x `&` y. Proof. exact: meetKI. Qed.
Lemma meetIK y x : (x `&` y) `&` y = x `&` y. Proof. exact: meetIK. Qed.
Lemma meetKIC y x : x `&` (y `&` x) = x `&` y. Proof. exact: meetKIC. Qed.
Lemma meetIKC y x : y `&` x `&` y = x `&` y. Proof. exact: meetIKC. Qed.

(* interaction with order *)

Lemma lexI x y z : (x <= y `&` z) = (x <= y) && (x <= z).
Proof. exact: lexI. Qed.

Lemma leIxl x y z : y <= x -> y `&` z <= x. Proof. exact: leIxl. Qed.
Lemma leIxr x y z : z <= x -> y `&` z <= x. Proof. exact: leIxr. Qed.

Lemma leIx2 x y z : (y <= x) || (z <= x) -> y `&` z <= x.
Proof. exact: leIx2. Qed.

Lemma leIr x y : y `&` x <= x. Proof. exact: leIr. Qed.
Lemma leIl x y : x `&` y <= x. Proof. exact: leIl. Qed.

Lemma meet_idPl {x y} : reflect (x `&` y = x) (x <= y).
Proof. exact: meet_idPl. Qed.
Lemma meet_idPr {x y} : reflect (y `&` x = x) (x <= y).
Proof. exact: meet_idPr. Qed.

Lemma meet_l x y : x <= y -> x `&` y = x. Proof. exact: meet_l. Qed.
Lemma meet_r x y : y <= x -> x `&` y = y. Proof. exact: meet_r. Qed.

Lemma leIidl x y : (x <= x `&` y) = (x <= y). Proof. exact: leIidl. Qed.
Lemma leIidr x y : (x <= y `&` x) = (x <= y). Proof. exact: leIidr. Qed.

Lemma eq_meetl x y : (x `&` y == x) = (x <= y). Proof. exact: eq_meetl. Qed.
Lemma eq_meetr x y : (x `&` y == y) = (y <= x). Proof. exact: eq_meetr. Qed.

Lemma leI2 x y z t : x <= z -> y <= t -> x `&` y <= z `&` t.
Proof. exact: leI2. Qed.

End MeetTheory.
End MeetTheory.

Arguments meet_idPl {disp L x y}.
Arguments meet_idPr {disp L x y}.

Module Import BMeetTheory.
Section BMeetTheory.
Context {disp : unit} {L : bMeetSemilatticeType disp}.

Lemma meet0x : left_zero 0 (@meet _ L). Proof. exact: meet0x. Qed.
Lemma meetx0 : right_zero 0 (@meet _ L). Proof. exact: meetx0. Qed.

Canonical meet_muloid := Monoid.MulLaw meet0x meetx0.

End BMeetTheory.
End BMeetTheory.

Module Import TMeetTheory.
Section TMeetTheory.
Context {disp : unit} {L : tMeetSemilatticeType disp}.
Implicit Types (I : finType) (T : eqType) (x y : L).

Lemma meetx1 : right_id 1 (@meet _ L). Proof. exact: meetx1. Qed.
Lemma meet1x : left_id 1 (@meet _ L). Proof. exact: meet1x. Qed.

Lemma meet_eq1 x y : (x `&` y == 1) = (x == 1) && (y == 1).
Proof. exact: meet_eq1. Qed.

Canonical meet_monoid := Monoid.Law meetA meet1x meetx1.
Canonical meet_comoid := Monoid.ComLaw meetC.

Lemma meets_inf_seq T (r : seq T) (P : {pred T}) (F : T -> L) (x : T) :
  x \in r -> P x -> \meet_(i <- r | P i) F i <= F x.
Proof. exact: meets_inf_seq. Qed.

Lemma meets_max_seq T (r : seq T) (P : {pred T}) (F : T -> L) (x : T) (u : L) :
  x \in r -> P x -> F x <= u -> \meet_(x <- r | P x) F x <= u.
Proof. exact: meets_max_seq. Qed.

Lemma meets_inf I (j : I) (P : {pred I}) (F : I -> L) :
   P j -> \meet_(i | P i) F i <= F j.
Proof. exact: meets_inf_seq. Qed.

Lemma meets_max I (j : I) (u : L) (P : {pred I}) (F : I -> L) :
   P j -> F j <= u -> \meet_(i | P i) F i <= u.
Proof. exact: meets_max_seq. Qed.

Lemma meets_ge J (r : seq J) (P : {pred J}) (F : J -> L) (u : L) :
  (forall x : J, P x -> u <= F x) -> u <= \meet_(x <- r | P x) F x.
Proof. exact: meets_ge. Qed.

Lemma meetsP_seq T (r : seq T) (P : {pred T}) (F : T -> L) (l : L) :
  reflect (forall x : T, x \in r -> P x -> l <= F x)
          (l <= \meet_(x <- r | P x) F x).
Proof. exact: meetsP_seq. Qed.

Lemma meetsP I (l : L) (P : {pred I}) (F : I -> L) :
   reflect (forall i : I, P i -> l <= F i) (l <= \meet_(i | P i) F i).
Proof. exact: meetsP. Qed.

Lemma le_meets I (A B : {set I}) (F : I -> L) :
   A \subset B -> \meet_(i in B) F i <= \meet_(i in A) F i.
Proof. exact: le_meets. Qed.

Lemma meets_setU I (A B : {set I}) (F : I -> L) :
   \meet_(i in (A :|: B)) F i = \meet_(i in A) F i `&` \meet_(i in B) F i.
Proof. exact: meets_setU. Qed.

Lemma meets_seq I (r : seq I) (F : I -> L) :
   \meet_(i <- r) F i = \meet_(i in r) F i.
Proof. exact: meets_seq. Qed.

End TMeetTheory.

#[deprecated(since="mathcomp 1.13.0", note="Use meets_inf_seq instead.")]
Notation meet_inf_seq := meets_inf_seq.
#[deprecated(since="mathcomp 1.13.0", note="Use meets_max_seq instead.")]
Notation meet_max_seq := meets_max_seq.
#[deprecated(since="mathcomp 1.13.0", note="Use meets_seq instead.")]
Notation meet_seq := meets_seq.

End TMeetTheory.

Module Import JoinTheory.
Section JoinTheory.
Context {disp : unit} {L : joinSemilatticeType disp}.
Implicit Types (x y : L).

Lemma joinC : commutative (@join _ L). Proof. exact: joinC. Qed.
Lemma joinA : associative (@join _ L). Proof. exact: joinA. Qed.
Lemma leEjoin x y : (x <= y) = (x `|` y == y). Proof. exact: leEjoin. Qed.

Lemma joinxx : idempotent (@join _ L). Proof. exact: joinxx. Qed.
Lemma joinAC : right_commutative (@join _ L). Proof. exact: joinAC. Qed.
Lemma joinCA : left_commutative (@join _ L). Proof. exact: joinCA. Qed.
Lemma joinACA : interchange (@join _ L) (@join _ L). Proof. exact: joinACA. Qed.

Lemma joinKU y x : x `|` (x `|` y) = x `|` y. Proof. exact: joinKU. Qed.
Lemma joinUK y x : (x `|` y) `|` y = x `|` y. Proof. exact: joinUK. Qed.
Lemma joinKUC y x : x `|` (y `|` x) = x `|` y. Proof. exact: joinKUC. Qed.
Lemma joinUKC y x : y `|` x `|` y = x `|` y. Proof. exact: joinUKC. Qed.

(* interaction with order *)
Lemma leUx x y z : (x `|` y <= z) = (x <= z) && (y <= z).
Proof. exact: leUx. Qed.
Lemma lexUl x y z : x <= y -> x <= y `|` z. Proof. exact: lexUl. Qed.
Lemma lexUr x y z : x <= z -> x <= y `|` z. Proof. exact: lexUr. Qed.
Lemma lexU2 x y z : (x <= y) || (x <= z) -> x <= y `|` z.
Proof. exact: lexU2. Qed.

Lemma leUr x y : x <= y `|` x. Proof. exact: leUr. Qed.
Lemma leUl x y : x <= x `|` y. Proof. exact: leUl. Qed.

Lemma join_idPl {x y} : reflect (y `|` x = y) (x <= y).
Proof. exact: join_idPl. Qed.
Lemma join_idPr {x y} : reflect (x `|` y = y) (x <= y).
Proof. exact: join_idPr. Qed.

Lemma join_l x y : y <= x -> x `|` y = x. Proof. exact: join_l. Qed.
Lemma join_r x y : x <= y -> x `|` y = y. Proof. exact: join_r. Qed.

Lemma leUidl x y : (x `|` y <= y) = (x <= y). Proof. exact: leUidl. Qed.
Lemma leUidr x y : (y `|` x <= y) = (x <= y). Proof. exact: leUidr. Qed.

Lemma eq_joinl x y : (x `|` y == x) = (y <= x). Proof. exact: eq_joinl. Qed.
Lemma eq_joinr x y : (x `|` y == y) = (x <= y). Proof. exact: eq_joinr. Qed.

Lemma leU2 x y z t : x <= z -> y <= t -> x `|` y <= z `|` t.
Proof. exact: leU2. Qed.

End JoinTheory.
End JoinTheory.

Arguments join_idPl {disp L x y}.
Arguments join_idPr {disp L x y}.

Module Import BJoinTheory.
Section BJoinTheory.
Context {disp : unit} {L : bJoinSemilatticeType disp}.
Implicit Types (I : finType) (T : eqType) (x y : L).

Lemma joinx0 : right_id 0 (@join _ L). Proof. exact: joinx0. Qed.
Lemma join0x : left_id 0 (@join _ L). Proof. exact: join0x. Qed.

Lemma join_eq0 x y : (x `|` y == 0) = (x == 0) && (y == 0).
Proof. exact: join_eq0. Qed.

Canonical join_monoid := Monoid.Law joinA join0x joinx0.
Canonical join_comoid := Monoid.ComLaw joinC.

Lemma joins_sup_seq T (r : seq T) (P : {pred T}) (F : T -> L) (x : T) :
  x \in r -> P x -> F x <= \join_(i <- r | P i) F i.
Proof. exact: joins_sup_seq. Qed.

Lemma joins_min_seq T (r : seq T) (P : {pred T}) (F : T -> L) (x : T) (l : L) :
  x \in r -> P x -> l <= F x -> l <= \join_(x <- r | P x) F x.
Proof. exact: joins_min_seq. Qed.

Lemma joins_sup I (j : I) (P : {pred I}) (F : I -> L) :
  P j -> F j <= \join_(i | P i) F i.
Proof. exact: joins_sup. Qed.

Lemma joins_min I (j : I) (l : L) (P : {pred I}) (F : I -> L) :
  P j -> l <= F j -> l <= \join_(i | P i) F i.
Proof. exact: joins_min. Qed.

Lemma joins_le J (r : seq J) (P : {pred J}) (F : J -> L) (u : L) :
  (forall x : J, P x -> F x <= u) -> \join_(x <- r | P x) F x <= u.
Proof. exact: joins_le. Qed.

Lemma joinsP_seq T (r : seq T) (P : {pred T}) (F : T -> L) (u : L) :
  reflect (forall x : T, x \in r -> P x -> F x <= u)
          (\join_(x <- r | P x) F x <= u).
Proof. exact: joinsP_seq. Qed.

Lemma joinsP I (u : L) (P : {pred I}) (F : I -> L) :
  reflect (forall i : I, P i -> F i <= u) (\join_(i | P i) F i <= u).
Proof. exact: joinsP. Qed.

Lemma le_joins I (A B : {set I}) (F : I -> L) :
  A \subset B -> \join_(i in A) F i <= \join_(i in B) F i.
Proof. exact: le_joins. Qed.

Lemma joins_setU I (A B : {set I}) (F : I -> L) :
  \join_(i in (A :|: B)) F i = \join_(i in A) F i `|` \join_(i in B) F i.
Proof. exact: joins_setU. Qed.

Lemma joins_seq I (r : seq I) (F : I -> L) :
  \join_(i <- r) F i = \join_(i in r) F i.
Proof. exact: joins_seq. Qed.

End BJoinTheory.

#[deprecated(since="mathcomp 1.13.0", note="Use joins_sup_seq instead.")]
Notation join_sup_seq := joins_sup_seq.
#[deprecated(since="mathcomp 1.13.0", note="Use joins_min_seq instead.")]
Notation join_min_seq := joins_min_seq.
#[deprecated(since="mathcomp 1.13.0", note="Use joins_sup instead.")]
Notation join_sup := joins_sup.
#[deprecated(since="mathcomp 1.13.0", note="Use joins_min instead.")]
Notation join_min := joins_min.
#[deprecated(since="mathcomp 1.13.0", note="Use joins_seq instead.")]
Notation join_seq := joins_seq.

End BJoinTheory.

Module Import TJoinTheory.
Section TJoinTheory.
Context {disp : unit} {L : tJoinSemilatticeType disp}.

Lemma joinx1 : right_zero 1 (@join _ L). Proof. exact: joinx1. Qed.
Lemma join1x : left_zero 1 (@join _ L). Proof. exact: join1x. Qed.

Canonical join_muloid := Monoid.MulLaw join1x joinx1.

End TJoinTheory.
End TJoinTheory.

Module Import LatticeTheory.
Section LatticeTheory.
Context {disp : unit} {L : latticeType disp}.
Implicit Types (x y : L).

Lemma meetUK x y : (x `&` y) `|` y = y. Proof. exact: meetUK. Qed.
Lemma meetUKC x y : (y `&` x) `|` y = y. Proof. exact: meetUKC. Qed.
Lemma meetKUC y x : x `|` (y `&` x) = x. Proof. exact: meetKUC. Qed.
Lemma meetKU y x : x `|` (x `&` y) = x. Proof. exact: meetKU. Qed.
Lemma joinIK x y : (x `|` y) `&` y = y. Proof. exact: joinIK. Qed.
Lemma joinIKC x y : (y `|` x) `&` y = y. Proof. exact: joinIKC. Qed.
Lemma joinKIC y x : x `&` (y `|` x) = x. Proof. exact: joinKIC. Qed.
Lemma joinKI y x : x `&` (x `|` y) = x. Proof. exact: joinKI. Qed.

(* comparison predicates *)

Lemma lcomparableP x y : incomparel x y
  (min y x) (min x y) (max y x) (max x y)
  (y `&` x) (x `&` y) (y `|` x) (x `|` y)
  (y == x) (x == y) (x >= y) (x <= y) (x > y) (x < y) (y >=< x) (x >=< y).
Proof. exact: lcomparableP. Qed.

Lemma lcomparable_ltgtP x y : x >=< y ->
  comparel x y (min y x) (min x y) (max y x) (max x y)
               (y `&` x) (x `&` y) (y `|` x) (x `|` y)
               (y == x) (x == y) (x >= y) (x <= y) (x > y) (x < y).
Proof. exact: lcomparable_ltgtP. Qed.

Lemma lcomparable_leP x y : x >=< y ->
  lel_xor_gt x y (min y x) (min x y) (max y x) (max x y)
                 (y `&` x) (x `&` y) (y `|` x) (x `|` y) (x <= y) (y < x).
Proof. exact: lcomparable_leP. Qed.

Lemma lcomparable_ltP x y : x >=< y ->
  ltl_xor_ge x y (min y x) (min x y) (max y x) (max x y)
                 (y `&` x) (x `&` y) (y `|` x) (x `|` y) (y <= x) (x < y).
Proof. exact: lcomparable_ltP. Qed.

End LatticeTheory.
End LatticeTheory.

Module Import DistrLatticeTheory.
Section DistrLatticeTheory.
Context {disp : unit}.
Variable L : distrLatticeType disp.
Implicit Types (x y : L).

Lemma meetUl : left_distributive (@meet _ L) (@join _ L).
Proof. exact: meetUl. Qed.

Lemma joinIl : left_distributive (@join _ L) (@meet _ L).
Proof. exact: joinIl. Qed.

Lemma meetUr : right_distributive (@meet _ L) (@join _ L).
Proof. exact: meetUr. Qed.

Lemma joinIr : right_distributive (@join _ L) (@meet _ L).
Proof. exact: joinIr. Qed.

End DistrLatticeTheory.
End DistrLatticeTheory.

Module Import BDistrLatticeTheory.
Section BDistrLatticeTheory.
Context {disp : unit} {L : bDistrLatticeType disp}.
Implicit Types (I : finType) (T : eqType) (x y z : L).
Local Notation "0" := bottom.
(* Distributive lattice theory with 0 *)

Canonical join_addoid := Monoid.AddLaw (@meetUl _ L) (@meetUr _ _).

Lemma leU2l_le y t x z : x `&` t = 0 -> x `|` y <= z `|` t -> x <= z.
Proof. exact: leU2l_le. Qed.

Lemma leU2r_le y t x z : x `&` t = 0 -> y `|` x <= t `|` z -> x <= z.
Proof. exact: leU2r_le. Qed.

Lemma disjoint_lexUl z x y : x `&` z = 0 -> (x <= y `|` z) = (x <= y).
Proof. exact: disjoint_lexUl. Qed.

Lemma disjoint_lexUr z x y : x `&` z = 0 -> (x <= z `|` y) = (x <= y).
Proof. exact: disjoint_lexUr. Qed.

Lemma leU2E x y z t : x `&` t = 0 -> y `&` z = 0 ->
  (x `|` y <= z `|` t) = (x <= z) && (y <= t).
Proof. exact: leU2E. Qed.

Lemma joins_disjoint I (d : L) (P : {pred I}) (F : I -> L) :
   (forall i : I, P i -> d `&` F i = 0) -> d `&` \join_(i | P i) F i = 0.
Proof. exact: joins_disjoint. Qed.

End BDistrLatticeTheory.
End BDistrLatticeTheory.

Module Import TDistrLatticeTheory.
Section TDistrLatticeTheory.
Context {disp : unit} {L : tDistrLatticeType disp}.
Implicit Types (I : finType) (T : eqType) (x y : L).
Local Notation "1" := top.
(* Distributive lattice theory with 1 *)

Canonical meet_addoid := Monoid.AddLaw (@joinIl _ L) (@joinIr _ _).

Lemma leI2l_le y t x z : y `|` z = 1 -> x `&` y <= z `&` t -> x <= z.
Proof. exact: leI2l_le. Qed.

Lemma leI2r_le y t x z : y `|` z = 1 -> y `&` x <= t `&` z -> x <= z.
Proof. exact: leI2r_le. Qed.

Lemma cover_leIxl z x y : z `|` y = 1 -> (x `&` z <= y) = (x <= y).
Proof. exact: cover_leIxl. Qed.

Lemma cover_leIxr z x y : z `|` y = 1 -> (z `&` x <= y) = (x <= y).
Proof. exact: cover_leIxr. Qed.

Lemma leI2E x y z t : x `|` t = 1 -> y `|` z = 1 ->
  (x `&` y <= z `&` t) = (x <= z) && (y <= t).
Proof. exact: leI2E. Qed.

Lemma meets_total I (d : L) (P : {pred I}) (F : I -> L) :
   (forall i : I, P i -> d `|` F i = 1) -> d `|` \meet_(i | P i) F i = 1.
Proof. exact: meets_total. Qed.

End TDistrLatticeTheory.
End TDistrLatticeTheory.

Module Import TotalTheory.
Section TotalTheory.
Context {disp : unit} {T : orderType disp}.
Implicit Types (x y z t : T) (s : seq T).

Lemma le_total : total (<=%O : rel T). Proof. exact: le_total. Qed.
(* FIXME *)
Lemma ge_total : total (>=%O : rel T). Proof. exact: ge_total. Qed.
Lemma comparableT x y : x >=< y. Proof. exact: le_total. Qed.
Hint Resolve le_total ge_total comparableT : core.

Lemma leNgt x y : (x <= y) = ~~ (y < x). Proof. exact: leNgt. Qed.
Lemma ltNge x y : (x < y) = ~~ (y <= x). Proof. exact: ltNge. Qed.

Definition ltgtP x y := LatticeTheory.lcomparable_ltgtP (comparableT x y).
Definition leP x y := LatticeTheory.lcomparable_leP (comparableT x y).
Definition ltP x y := LatticeTheory.lcomparable_ltP (comparableT x y).

Lemma wlog_le P :
     (forall x y, P y x -> P x y) -> (forall x y, x <= y -> P x y) ->
   forall x y, P x y.
Proof. exact: wlog_le. Qed.

Lemma wlog_lt P :
    (forall x, P x x) ->
    (forall x y, (P y x -> P x y)) -> (forall x y, x < y -> P x y) ->
  forall x y, P x y.
Proof. exact: wlog_lt. Qed.

Lemma neq_lt x y : (x != y) = (x < y) || (y < x). Proof. by case: ltgtP. Qed.

Lemma lt_total x y : x != y -> (x < y) || (y < x). Proof. by case: ltgtP. Qed.

Lemma eq_leLR x y z t :
  (x <= y -> z <= t) -> (y < x -> t < z) -> (x <= y) = (z <= t).
Proof. exact: eq_leLR. Qed.

Lemma eq_leRL x y z t :
  (x <= y -> z <= t) -> (y < x -> t < z) -> (z <= t) = (x <= y).
Proof. exact: eq_leRL. Qed.

Lemma eq_ltLR x y z t :
  (x < y -> z < t) -> (y <= x -> t <= z) -> (x < y) = (z < t).
Proof. exact: eq_ltLR. Qed.

Lemma eq_ltRL x y z t :
  (x < y -> z < t) -> (y <= x -> t <= z) -> (z < t) = (x < y).
Proof. exact: eq_ltRL. Qed.

Lemma sort_le_sorted s : sorted <=%O (sort <=%O s).
Proof. exact: sort_le_sorted. Qed.
Hint Resolve sort_le_sorted : core.

Lemma sort_lt_sorted s : sorted <%O (sort <=%O s) = uniq s.
Proof. exact: sort_lt_sorted. Qed.

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

Lemma count_le_gt x s : count (<= x) s = size s - count (> x) s.
Proof. exact: count_le_gt. Qed.

Lemma count_lt_ge x s : count (< x) s = size s - count (>= x) s.
Proof. exact: count_lt_ge. Qed.

Lemma sorted_filter_gt x s :
  sorted <=%O s -> [seq y <- s | x < y] = drop (count (<= x) s) s.
Proof. exact: sorted_filter_gt. Qed.

Lemma sorted_filter_ge x s :
  sorted <=%O s -> [seq y <- s | x <= y] = drop (count (< x) s) s.
Proof. exact: sorted_filter_ge. Qed.

Lemma nth_count_ge x x0 s i : sorted <=%O s ->
  (count (< x) s <= i < size s)%N -> x <= nth x0 s i.
Proof. exact: nth_count_ge. Qed.

Lemma nth_count_gt x x0 s i : sorted <=%O s ->
  (count (<= x) s <= i < size s)%N -> x < nth x0 s i.
Proof. exact: nth_count_gt. Qed.

Lemma nth_count_eq x x0 s i : sorted <=%O s ->
  (count (< x) s <= i < count (<= x) s)%N -> nth x0 s i = x.
Proof. exact: nth_count_eq. Qed.

(* max and min is join and meet *)

Lemma meetEtotal x y : x `&` y = min x y. Proof. by case: leP. Qed.
Lemma joinEtotal x y : x `|` y = max x y. Proof. by case: leP. Qed.

(* max and min theory *)

Lemma minEgt x y : min x y = if x > y then y else x. Proof. by case: ltP. Qed.
Lemma maxEgt x y : max x y = if x > y then x else y. Proof. by case: ltP. Qed.
Lemma minEge x y : min x y = if x >= y then y else x. Proof. by case: leP. Qed.
Lemma maxEge x y : max x y = if x >= y then x else y. Proof. by case: leP. Qed.

Lemma minC : commutative (min : T -> T -> T). Proof. exact: minC. Qed.
Lemma maxC : commutative (max : T -> T -> T). Proof. exact: maxC. Qed.
Lemma minA : associative (min : T -> T -> T). Proof. exact: minA. Qed.
Lemma maxA : associative (max : T -> T -> T). Proof. exact: maxA. Qed.
Lemma minAC : right_commutative (min : T -> T -> T). Proof. exact: minAC. Qed.
Lemma maxAC : right_commutative (max : T -> T -> T). Proof. exact: maxAC. Qed.
Lemma minCA : left_commutative (min : T -> T -> T). Proof. exact: minCA. Qed.
Lemma maxCA : left_commutative (max : T -> T -> T). Proof. exact: maxCA. Qed.
Lemma minACA : interchange (min : T -> T -> T) min. Proof. exact: minACA. Qed.
Lemma maxACA : interchange (max : T -> T -> T) max. Proof. exact: maxACA. Qed.

Lemma eq_minr x y : (min x y == y) = (y <= x). Proof. exact: eq_minr. Qed.
Lemma eq_maxl x y : (max x y == x) = (y <= x). Proof. exact: eq_maxl. Qed.

Lemma min_idPr x y : reflect (min x y = y) (y <= x).
Proof. exact: min_idPr. Qed.

Lemma max_idPl x y : reflect (max x y = x) (y <= x).
Proof. exact: max_idPl. Qed.

Lemma le_minr z x y : (z <= min x y) = (z <= x) && (z <= y).
Proof. exact: le_minr. Qed.

Lemma le_minl z x y : (min x y <= z) = (x <= z) || (y <= z).
Proof. exact: le_minl. Qed.

Lemma lt_minr z x y : (z < min x y) = (z < x) && (z < y).
Proof. exact: lt_minr. Qed.

Lemma lt_minl z x y : (min x y < z) = (x < z) || (y < z).
Proof. exact: lt_minl. Qed.

Lemma le_maxr z x y : (z <= max x y) = (z <= x) || (z <= y).
Proof. exact: le_maxr. Qed.

Lemma le_maxl z x y : (max x y <= z) = (x <= z) && (y <= z).
Proof. exact: le_maxl. Qed.

Lemma lt_maxr z x y : (z < max x y) = (z < x) || (z < y).
Proof. exact: lt_maxr. Qed.

Lemma lt_maxl z x y : (max x y < z) = (x < z) && (y < z).
Proof. exact: lt_maxl. Qed.

Lemma minxK x y : max (min x y) y = y. Proof. exact: minxK. Qed.
Lemma minKx x y : max x (min x y) = x. Proof. exact: minKx. Qed.
Lemma maxxK x y : min (max x y) y = y. Proof. exact: maxxK. Qed.
Lemma maxKx x y : min x (max x y) = x. Proof. exact: maxKx. Qed.

Lemma max_minl : left_distributive (max : T -> T -> T) min.
Proof. exact: max_minl. Qed.

Lemma min_maxl : left_distributive (min : T -> T -> T) max.
Proof. exact: min_maxl. Qed.

Lemma max_minr : right_distributive (max : T -> T -> T) min.
Proof. exact: max_minr. Qed.

Lemma min_maxr : right_distributive (min : T -> T -> T) max.
Proof. exact: min_maxr. Qed.

Lemma leIx x y z : (meet y z <= x) = (y <= x) || (z <= x).
Proof. exact: leIx. Qed.

Lemma lexU x y z : (x <= join y z) = (x <= y) || (x <= z).
Proof. exact: lexU. Qed.

Lemma ltxI x y z : (x < meet y z) = (x < y) && (x < z).
Proof. exact: ltxI. Qed.

Lemma ltIx x y z : (meet y z < x) = (y < x) || (z < x).
Proof. exact: ltIx. Qed.

Lemma ltxU x y z : (x < join y z) = (x < y) || (x < z).
Proof. exact: ltxU. Qed.

Lemma ltUx x y z : (join y z < x) = (y < x) && (z < x).
Proof. exact: ltUx. Qed.

Definition ltexI := (@lexI _ T, ltxI).
Definition lteIx := (leIx, ltIx).
Definition ltexU := (lexU, ltxU).
Definition lteUx := (@leUx _ T, ltUx).

(* lteif *)

Lemma lteifNE x y C : x < y ?<= if ~~ C = ~~ (y < x ?<= if C).
Proof. exact: lteifNE. Qed.

Lemma lteif_minr z x y C :
  (z < min x y ?<= if C) = (z < x ?<= if C) && (z < y ?<= if C).
Proof. exact: lteif_minr. Qed.

Lemma lteif_minl z x y C :
  (min x y < z ?<= if C) = (x < z ?<= if C) || (y < z ?<= if C).
Proof. exact: lteif_minl. Qed.

Lemma lteif_maxr z x y C :
  (z < max x y ?<= if C) = (z < x ?<= if C) || (z < y ?<= if C).
Proof. exact: lteif_maxr. Qed.

Lemma lteif_maxl z x y C :
  (max x y < z ?<= if C) = (x < z ?<= if C) && (y < z ?<= if C).
Proof. exact: lteif_maxl. Qed.

Section ArgExtremum.

Context (I : finType) (i0 : I) (P : {pred I}) (F : I -> T) (Pi0 : P i0).

Lemma arg_minP: extremum_spec <=%O P F (arg_min i0 P F).
Proof. exact: comparable_arg_minP. Qed.

Lemma arg_maxP: extremum_spec >=%O P F (arg_max i0 P F).
Proof. exact: comparable_arg_maxP. Qed.

End ArgExtremum.

Section bigminmax_Type.
Variables (I : Type) (r : seq I) (x : T).
Implicit Types (P : pred I) (F : I -> T).

Lemma bigmin_mkcond P F : \big[min/x]_(i <- r | P i) F i =
  \big[min/x]_(i <- r) (if P i then F i else x).
Proof. rewrite big_mkcond_idem ?minxx//; [exact: minA|exact: minC]. Qed.

Lemma bigmax_mkcond P F :
  \big[max/x]_(i <- r | P i) F i = \big[max/x]_(i <- r) if P i then F i else x.
Proof. by rewrite big_mkcond_idem ?maxxx//; [exact: maxA|exact: maxC]. Qed.

Lemma bigmin_split P F1 F2 :
  \big[min/x]_(i <- r | P i) (min (F1 i) (F2 i)) =
    min (\big[min/x]_(i <- r | P i) F1 i) (\big[min/x]_(i <- r | P i) F2 i).
Proof. rewrite big_split_idem ?minxx//; [exact: minA|exact: minC]. Qed.

Lemma bigmax_split P F1 F2 :
  \big[max/x]_(i <- r | P i) (max (F1 i) (F2 i)) =
    max (\big[max/x]_(i <- r | P i) F1 i) (\big[max/x]_(i <- r | P i) F2 i).
Proof. by rewrite big_split_idem ?maxxx//; [exact: maxA|exact: maxC]. Qed.

Lemma bigmin_idl P F :
  \big[min/x]_(i <- r | P i) F i = min x (\big[min/x]_(i <- r | P i) F i).
Proof. rewrite minC big_id_idem ?minxx//; exact: minA. Qed.

Lemma bigmax_idl P F :
  \big[max/x]_(i <- r | P i) F i = max x (\big[max/x]_(i <- r | P i) F i).
Proof. by rewrite maxC big_id_idem ?maxxx//; exact: maxA. Qed.

Lemma bigmin_idr P F :
  \big[min/x]_(i <- r | P i) F i = min (\big[min/x]_(i <- r | P i) F i) x.
Proof. by rewrite [LHS]bigmin_idl minC. Qed.

Lemma bigmax_idr P F :
  \big[max/x]_(i <- r | P i) F i = max (\big[max/x]_(i <- r | P i) F i) x.
Proof. by rewrite [LHS]bigmax_idl maxC. Qed.

Lemma bigminID a P F : \big[min/x]_(i <- r | P i) F i =
  min (\big[min/x]_(i <- r | P i && a i) F i)
      (\big[min/x]_(i <- r | P i && ~~ a i) F i).
Proof. by rewrite (bigID_idem minA minC _ _ a) ?minxx. Qed.

Lemma bigmaxID a P F : \big[max/x]_(i <- r | P i) F i =
  max (\big[max/x]_(i <- r | P i && a i) F i)
      (\big[max/x]_(i <- r | P i && ~~ a i) F i).
Proof. by rewrite (bigID_idem maxA maxC _ _ a) ?maxxx. Qed.

End bigminmax_Type.

Let le_minr_id (x y : T) : x >= min x y. Proof. by rewrite le_minl lexx. Qed.
Let le_maxr_id (x y : T) : x <= max x y. Proof. by rewrite le_maxr lexx. Qed.

Lemma sub_bigmin [x0] I r (P P' : {pred I}) (F : I -> T) :
    (forall i, P' i -> P i) ->
  \big[min/x0]_(i <- r | P i) F i <= \big[min/x0]_(i <- r | P' i) F i.
Proof. exact: (sub_le_big minA minC ge_refl). Qed.

Lemma sub_bigmax [x0] I r (P P' : {pred I}) (F : I -> T) :
    (forall i, P i -> P' i) ->
  \big[max/x0]_(i <- r | P i) F i <= \big[max/x0]_(i <- r | P' i) F i.
Proof. exact: (sub_le_big maxA maxC). Qed.

Lemma sub_bigmin_seq [x0] (I : eqType) r r' P (F : I -> T) : {subset r' <= r} ->
  \big[min/x0]_(i <- r | P i) F i <= \big[min/x0]_(i <- r' | P i) F i.
Proof. exact: (idem_sub_le_big minA minC ge_refl _ minxx). Qed.

Lemma sub_bigmax_seq [x0] (I : eqType) r r' P (F : I -> T) : {subset r <= r'} ->
  \big[max/x0]_(i <- r | P i) F i <= \big[max/x0]_(i <- r' | P i) F i.
Proof. exact: (idem_sub_le_big maxA maxC _ _ maxxx). Qed.

Lemma sub_bigmin_cond [x0] (I : eqType) r r' P P' (F : I -> T) :
    {subset [seq i <- r | P i] <= [seq i <- r' | P' i]} ->
  \big[min/x0]_(i <- r' | P' i) F i <= \big[min/x0]_(i <- r | P i) F i.
Proof. exact: (idem_sub_le_big_cond minA minC ge_refl _ minxx). Qed.

Lemma sub_bigmax_cond [x0] (I : eqType) r r' P P' (F : I -> T) :
    {subset [seq i <- r | P i] <= [seq i <- r' | P' i]} ->
  \big[max/x0]_(i <- r | P i) F i <= \big[max/x0]_(i <- r' | P' i) F i.
Proof. exact: (idem_sub_le_big_cond maxA maxC _ _ maxxx). Qed.

Lemma sub_in_bigmin [x0] [I : eqType] (r : seq I) (P P' : {pred I}) F :
    {in r, forall i, P' i -> P i} ->
  \big[min/x0]_(i <- r | P i) F i <= \big[min/x0]_(i <- r | P' i) F i.
Proof. exact: (sub_in_le_big minA minC ge_refl). Qed.

Lemma sub_in_bigmax [x0] [I : eqType] (r : seq I) (P P' : {pred I}) F :
    {in r, forall i, P i -> P' i} ->
  \big[max/x0]_(i <- r | P i) F i <= \big[max/x0]_(i <- r | P' i) F i.
Proof. exact: (sub_in_le_big maxA maxC). Qed.

Lemma le_bigmin_nat [x0] n m n' m' P (F : nat -> T) :
    (n <= n')%N -> (m' <= m)%N ->
  \big[min/x0]_(n <= i < m | P i) F i <= \big[min/x0]_(n' <= i < m' | P i) F i.
Proof. exact: (le_big_nat minA minC ge_refl). Qed.

Lemma le_bigmax_nat [x0] n m n' m' P (F : nat -> T) :
    (n' <= n)%N -> (m <= m')%N ->
  \big[max/x0]_(n <= i < m | P i) F i <= \big[max/x0]_(n' <= i < m' | P i) F i.
Proof. exact: (le_big_nat maxA maxC). Qed.

Lemma le_bigmin_nat_cond [x0] n m n' m' (P P' : pred nat) (F : nat -> T) :
    (n <= n')%N -> (m' <= m)%N -> (forall i, (n' <= i < m')%N -> P' i -> P i) ->
  \big[min/x0]_(n <= i < m | P i) F i <= \big[min/x0]_(n' <= i < m' | P' i) F i.
Proof. exact: (le_big_nat_cond minA minC ge_refl). Qed.

Lemma le_bigmax_nat_cond [x0] n m n' m' (P P' : {pred nat}) (F : nat -> T) :
    (n' <= n)%N -> (m <= m')%N -> (forall i, (n <= i < m)%N -> P i -> P' i) ->
  \big[max/x0]_(n <= i < m | P i) F i <= \big[max/x0]_(n' <= i < m' | P' i) F i.
Proof. exact: (le_big_nat_cond maxA maxC). Qed.

Lemma le_bigmin_ord [x0] n m (P : pred nat) (F : nat -> T) : (m <= n)%N ->
  \big[min/x0]_(i < n | P i) F i <= \big[min/x0]_(i < m | P i) F i.
Proof. exact: (le_big_ord minA minC ge_refl). Qed.

Lemma le_bigmax_ord [x0] n m (P : {pred nat}) (F : nat -> T) : (n <= m)%N ->
  \big[max/x0]_(i < n | P i) F i <= \big[max/x0]_(i < m | P i) F i.
Proof. exact: (le_big_ord maxA maxC). Qed.

Lemma le_bigmin_ord_cond [x0] n m (P P' : pred nat) (F : nat -> T) :
    (m <= n)%N -> (forall i : 'I_m, P' i -> P i) ->
  \big[min/x0]_(i < n | P i) F i <= \big[min/x0]_(i < m | P' i) F i.
Proof. exact: (le_big_ord_cond minA minC ge_refl). Qed.

Lemma le_bigmax_ord_cond [x0] n m (P P' : {pred nat}) (F : nat -> T) :
    (n <= m)%N -> (forall i : 'I_n, P i -> P' i) ->
  \big[max/x0]_(i < n | P i) F i <= \big[max/x0]_(i < m | P' i) F i.
Proof. exact: (le_big_ord_cond maxA maxC). Qed.

Lemma subset_bigmin [x0] [I : finType] [A A' P : {pred I}] (F : I -> T) :
    A' \subset A ->
  \big[min/x0]_(i in A | P i) F i <= \big[min/x0]_(i in A' | P i) F i.
Proof. exact: (subset_le_big minA minC ge_refl). Qed.

Lemma subset_bigmax [x0] [I : finType] (A A' P : {pred I}) (F : I -> T) :
    A \subset A' ->
  \big[max/x0]_(i in A | P i) F i <= \big[max/x0]_(i in A' | P i) F i.
Proof. exact: (subset_le_big maxA maxC). Qed.

Lemma subset_bigmin_cond [x0] (I : finType) (A A' P P' : {pred I}) (F : I -> T) :
    [set i in A' | P' i]  \subset [set i in A | P i] ->
  \big[min/x0]_(i in A | P i) F i <= \big[min/x0]_(i in A' | P' i) F i.
Proof. exact: (subset_le_big_cond minA minC ge_refl). Qed.

Lemma subset_bigmax_cond [x0] (I : finType) (A A' P P' : {pred I}) (F : I -> T) :
    [set i in A | P i]  \subset [set i in A' | P' i] ->
  \big[max/x0]_(i in A | P i) F i <= \big[max/x0]_(i in A' | P' i) F i.
Proof. exact: (subset_le_big_cond maxA maxC). Qed.

Section bigminmax_finType.
Variable (I : finType) (x : T).
Implicit Types (P : pred I) (F : I -> T).

Lemma bigminD1 j P F : P j ->
  \big[min/x]_(i | P i) F i = min (F j) (\big[min/x]_(i | P i && (i != j)) F i).
Proof. by move/(bigD1_AC minA minC) ->. Qed.

Lemma bigmaxD1 j P F : P j ->
  \big[max/x]_(i | P i) F i = max (F j) (\big[max/x]_(i | P i && (i != j)) F i).
Proof. by move/(bigD1_AC maxA maxC) ->. Qed.

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
  {i0 | i0 \in I & \big[min/x]_(i | P i) F i = F i0}.
Proof. by move=> Pi0 Hx; rewrite (bigmin_eq_arg Pi0) //; eexists. Qed.

Lemma eq_bigmax j P F : P j -> (forall i, P i -> x <= F i) ->
  {i0 | i0 \in I & \big[max/x]_(i | P i) F i = F i0}.
Proof. by move=> Pi0 Hx; rewrite (bigmax_eq_arg Pi0) //; eexists. Qed.

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
Proof. exact: contraTle. Qed.

Lemma contraTlt b z t : (t <= z -> ~~ b) -> (b -> z < t).
Proof. exact: contraTlt. Qed.

Lemma contraPle P z t : (t < z -> ~ P) -> (P -> z <= t).
Proof. exact: contraPle. Qed.

Lemma contraPlt P z t : (t <= z -> ~ P) -> (P -> z < t).
Proof. exact: contraPlt. Qed.

Lemma contraNle b z t : (t < z -> b) -> (~~ b -> z <= t).
Proof. exact: contraNle. Qed.

Lemma contraNlt b z t : (t <= z -> b) -> (~~ b -> z < t).
Proof. exact: contraNlt. Qed.

Lemma contra_not_le P z t : (t < z -> P) -> (~ P -> z <= t).
Proof. exact: contra_not_le. Qed.

Lemma contra_not_lt P z t : (t <= z -> P) -> (~ P -> z < t).
Proof. exact: contra_not_lt. Qed.

Lemma contraFle b z t : (t < z -> b) -> (b = false -> z <= t).
Proof. exact: contraFle. Qed.

Lemma contraFlt b z t : (t <= z -> b) -> (b = false -> z < t).
Proof. exact: contraFlt. Qed.

Lemma contra_leq_le m n z t : (t < z -> (n < m)%N) -> ((m <= n)%N -> z <= t).
Proof. exact: contra_leq_le. Qed.

Lemma contra_leq_lt m n z t : (t <= z -> (n < m)%N) -> ((m <= n)%N -> z < t).
Proof. exact: contra_leq_lt. Qed.

Lemma contra_ltn_le m n z t : (t < z -> (n <= m)%N) -> ((m < n)%N -> z <= t).
Proof. exact: contra_ltn_le. Qed.

Lemma contra_ltn_lt m n z t : (t <= z -> (n <= m)%N) -> ((m < n)%N -> z < t).
Proof. exact: contra_ltn_lt. Qed.

Lemma contra_le x y z t : (t < z -> y < x) -> (x <= y -> z <= t).
Proof. exact: contra_le. Qed.

Lemma contra_le_lt x y z t : (t <= z -> y < x) -> (x <= y -> z < t).
Proof. exact: contra_le_lt. Qed.

Lemma contra_lt_le x y z t : (t < z -> y <= x) -> (x < y -> z <= t).
Proof. exact: contra_lt_le. Qed.

Lemma contra_lt x y z t : (t <= z -> y <= x) -> (x < y -> z < t).
Proof. exact: contra_lt. Qed.

End ContraTheory.

Section TotalMonotonyTheory.

Context {disp : unit} {disp' : unit}.
Context {T : orderType disp} {T' : porderType disp'}.
Variables (D : {pred T}) (f : T -> T').

Lemma le_mono : {homo f : x y / x < y} -> {mono f : x y / x <= y}.
Proof. exact: le_mono. Qed.

Lemma le_nmono : {homo f : x y /~ x < y} -> {mono f : x y /~ x <= y}.
Proof. exact: le_nmono. Qed.

Lemma le_mono_in :
  {in D &, {homo f : x y / x < y}} -> {in D &, {mono f : x y / x <= y}}.
Proof. exact: le_mono_in. Qed.

Lemma le_nmono_in :
  {in D &, {homo f : x y /~ x < y}} -> {in D &, {mono f : x y /~ x <= y}}.
Proof. exact: le_nmono_in. Qed.

End TotalMonotonyTheory.
End TotalTheory.

Module Import CBDistrLatticeTheory.
Section CBDistrLatticeTheory.
Context {disp : unit} {L : cbDistrLatticeType disp}.
Implicit Types (x y z : L).
Local Notation "0" := bottom.

Lemma subKI x y : y `&` (x `\` y) = 0.
Proof. by case: L x y => ? [?[]]. Qed.

Lemma subIK x y : (x `\` y) `&` y = 0.
Proof. by rewrite meetC subKI. Qed.

Lemma meetIB z x y : (z `&` y) `&` (x `\` y) = 0.
Proof. by rewrite -meetA subKI meetx0. Qed.

Lemma meetBI z x y : (x `\` y) `&` (z `&` y) = 0.
Proof. by rewrite meetC meetIB. Qed.

Lemma joinIB y x : (x `&` y) `|` (x `\` y) = x.
Proof. by case: L x y => ? [?[]]. Qed.

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
by case/andP=> ?; rewrite -meet_eq0E_sub.
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
Proof. by case: L x => [?[? ?[]]]. Qed.

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

Module RelOrderMixin.
Module Exports.

(* Alternative constructors for some relorder factories that lets us infer    *)
(* order instances from types rather than relation:                           *)

Definition BottomMixin (disp : unit) (T : porderType disp) bottom :
  (forall x : T, bottom <= x) -> bottomRelMixin T := @BottomRelMixin _ _ bottom.

Definition TopMixin (disp : unit) (T : porderType disp) top :
  (forall x : T, x <= top) -> topRelMixin T := @TopRelMixin _ _ top.

Definition MeetMixin (disp : unit) (T : porderType disp) meet :
  commutative meet -> associative meet ->
  (forall x y : T, x <= y = (meet x y == x)) -> meetRelMixin T :=
  @MeetRelMixin _ _ meet.

Definition JoinMixin (disp : unit) (T : porderType disp) join :
  commutative join -> associative join ->
  (forall x y : T, y <= x = (join x y == x)) -> joinRelMixin T :=
  @JoinRelMixin _ _ join.

Definition DistrLatticeMixin (disp : unit) (T : latticeType disp) :
  left_distributive (@meet _ T) (@join _ T) -> distrLatticeRelMixin T :=
  @DistrLatticeRelMixin _ _.

Definition LatticePOrderMixin (disp : unit) (T : porderType disp) meet join :
  commutative meet -> commutative join ->
  associative meet -> associative join ->
  (forall y x : T, meet x (join x y) = x) ->
  (forall y x : T, join x (meet x y) = x) ->
  (forall x y : T, x <= y = (meet x y == x)) -> latticePOrderRelMixin T :=
  @LatticePOrderRelMixin _ _ meet join.

Definition DistrLatticePOrderMixin
           (disp : unit) (T : porderType disp) meet join :
  commutative meet -> commutative join ->
  associative meet -> associative join ->
  (forall y x : T, meet x (join x y) = x) ->
  (forall y x : T, join x (meet x y) = x) ->
  (forall x y : T, x <= y = (meet x y == x)) ->
  left_distributive meet join -> latticePOrderRelMixin T :=
  @DistrLatticePOrderRelMixin _ _ meet join.

(* Big pack notations: *)

Definition LatticeOfPOrderType
           disp (T : porderType disp) (m : latticePOrderRelMixin T) :
  latticeType disp :=
  [latticeType of JoinSemilatticeType (MeetSemilatticeType T m) m].

Definition DistrLatticeOfPOrderType
           disp (T : porderType disp) (m : distrLatticePOrderRelMixin T) :
  distrLatticeType disp := DistrLatticeType (LatticeOfPOrderType m) m.

Definition OrderOfLatticeType
           disp (T : latticeType disp) (m : totalLatticeRelMixin T) :
  orderType disp := OrderType (DistrLatticeType T m) m.

Definition OrderOfPOrderType
           disp (T : porderType disp) (m : totalPOrderRelMixin T) :
  orderType disp := @OrderOfLatticeType _ (LatticeOfPOrderType m) m.

Definition OrderOfMeetSemilatticeType
           disp (T : meetSemilatticeType disp) (m : totalMeetOrderRelMixin T) :
  orderType disp :=
  @OrderOfLatticeType _ [latticeType of JoinSemilatticeType T m] m.

Definition OrderOfJoinSemilatticeType
           disp (T : joinSemilatticeType disp) (m : totalJoinOrderRelMixin T) :
  orderType disp :=
  @OrderOfLatticeType _ [latticeType of MeetSemilatticeType T m] m.

Definition LatticeOfChoiceType
           disp (T : choiceType) (m : meetJoinMixin T) : latticeType disp :=
  [latticeType of JoinSemilatticeType
                    (MeetSemilatticeType (POrderType disp T m) m) m].

Definition DistrLatticeOfChoiceType
           disp (T : choiceType) (m : distrMeetJoinMixin T) :
  distrLatticeType disp := DistrLatticeType (LatticeOfChoiceType disp m) m.

Definition OrderOfChoiceType disp (T : choiceType) (m : leOrderMixin T) :
  orderType disp := @OrderOfLatticeType _ (LatticeOfChoiceType disp m) m.

End Exports.
End RelOrderMixin.
Import RelOrderMixin.Exports.

Module TotalLatticeMixin.
Section TotalLatticeMixin.
Variable (disp : unit) (T : latticeType disp).

Definition of_ (phT : phant T) := total (<=%O : rel T).

Definition mixin phT (m : of_ phT) : totalLatticeRelMixin T := m.

End TotalLatticeMixin.

Module Exports.
Notation totalLatticeMixin T := (of_ (Phant T)).
Coercion mixin : of_ >-> totalLatticeRelMixin.
End Exports.
End TotalLatticeMixin.
Import TotalLatticeMixin.Exports.

Module TotalPOrderMixin.
Section TotalPOrderMixin.
Variable (disp : unit) (T : porderType disp).

Definition of_ (phT : phant T) := total (<=%O : rel T).

Definition mixin phT (m : of_ phT) : totalPOrderRelMixin T := m.

End TotalPOrderMixin.

Module Exports.
Notation totalPOrderMixin T := (of_ (Phant T)).
Coercion mixin : of_ >-> totalPOrderRelMixin.
End Exports.
End TotalPOrderMixin.
Import TotalPOrderMixin.Exports.

Module TotalMeetSemilatticeMixin.
Section TotalMeetSemilatticeMixin.
Variable (disp : unit) (T : meetSemilatticeType disp).

Definition of_ (phT : phant T) := total (<=%O : rel T).

Definition mixin phT (m : of_ phT) : totalMeetOrderRelMixin T := m.

End TotalMeetSemilatticeMixin.

Module Exports.
Notation totalMeetSemilatticeMixin T := (of_ (Phant T)).
Coercion mixin : of_ >-> totalMeetOrderRelMixin.
End Exports.
End TotalMeetSemilatticeMixin.
Import TotalMeetSemilatticeMixin.Exports.

Module TotalJoinSemilatticeMixin.
Section TotalJoinSemilatticeMixin.
Variable (disp : unit) (T : joinSemilatticeType disp).

Definition of_ (phT : phant T) := total (<=%O : rel T).

Definition mixin phT (m : of_ phT) : totalJoinOrderRelMixin T := m.

End TotalJoinSemilatticeMixin.

Module Exports.
Notation totalJoinSemilatticeMixin T := (of_ (Phant T)).
Coercion mixin : of_ >-> totalJoinOrderRelMixin.
End Exports.
End TotalJoinSemilatticeMixin.
Import TotalJoinSemilatticeMixin.Exports.

Module CBDistrLatticeMixin.
Section CBDistrLatticeMixin.
Variable (disp : unit) (T : bDistrLatticeType disp).

Record of_ := Build {
  sub : T -> T -> T;
  subKI  : forall x y, y `&` sub x y = bottom;
  joinIB : forall x y, (x `&` y) `|` sub x y = x;
}.

Definition cbDistrLatticeMixin (m : of_) :=
  @CBDistrLattice.Mixin _ _ (sub m) (subKI m) (joinIB m).

End CBDistrLatticeMixin.

Module Exports.
Coercion cbDistrLatticeMixin : of_ >-> CBDistrLattice.mixin_of.
Notation cbDistrLatticeMixin := of_.
Notation CBDistrLatticeMixin := Build.
End Exports.

End CBDistrLatticeMixin.
Import CBDistrLatticeMixin.Exports.

Module CTBDistrLatticeMixin.
Section CTBDistrLatticeMixin.
Variable (disp : unit) (T : tbDistrLatticeType disp) (sub : T -> T -> T).

Record of_ := Build {
  compl : T -> T;
  complE : forall x, compl x = sub top x
}.

Definition ctbDistrLatticeMixin (m : of_) :=
  @CTBDistrLattice.Mixin _ _ sub (compl m) (complE m).

End CTBDistrLatticeMixin.

Module Exports.
Coercion ctbDistrLatticeMixin : of_ >-> CTBDistrLattice.mixin_of.
Notation ctbDistrLatticeMixin := of_.
Notation CTBDistrLatticeMixin := Build.
End Exports.

End CTBDistrLatticeMixin.
Import CTBDistrLatticeMixin.Exports.

Module CanMixin.
Section CanMixin.

Section Total.

Variables (disp : unit) (T : porderType disp).
Variables (disp' : unit) (T' : orderType disp') (f : T -> T').

Lemma MonoTotal : {mono f : x y / x <= y} ->
  totalPOrderMixin T' -> totalPOrderMixin T.
Proof. by move=> f_mono T'tot x y; rewrite -/le -!f_mono le_total. Qed.

End Total.

Section Order.

Variables (T : choiceType) (disp : unit).

Section Partial.
Variables (T' : porderType disp) (f : T -> T').

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

Definition PcanPOrder := LePOrderMixin lt_def refl anti trans.

End PCan.

Definition CanPOrder f' (f_can : cancel f f') := PcanPOrder (can_pcan f_can).

End Partial.

Section Total.

Variables (T' : orderType disp) (f : T -> T').

Section PCan.

Variables (f' : T' -> option T) (f_can : pcancel f f').

Let T_porderType := POrderType disp T (PcanPOrder f_can).

Let total_le : total (le f).
Proof. by apply: (@MonoTotal _ T_porderType _ _ f) => //; apply: le_total. Qed.

Definition PcanOrder := LeOrderMixin
  (@lt_def _ _ _ f_can) (fun _ _ => erefl) (fun _ _ => erefl)
  (@anti _ _ _ f_can) (@trans _ _) total_le.

End PCan.

Definition CanOrder f' (f_can : cancel f f') := PcanOrder (can_pcan f_can).

End Total.
End Order.

Section MeetSemilattice.

Variables (disp : unit) (T : porderType disp).
Variables (disp' : unit) (T' : meetSemilatticeType disp') (f : T -> T').

Variables (f' : T' -> T) (f_can : cancel f f') (f'_can : cancel f' f).
Variable (f_mono : {mono f : x y / x <= y}).

Definition meet (x y : T) := f' (meet (f x) (f y)).

Lemma meetC : commutative meet. Proof. by move=> x y; rewrite /meet meetC. Qed.
Lemma meetA : associative meet.
Proof. by move=> y x z; rewrite /meet !f'_can meetA. Qed.
Lemma meet_eql x y : (x <= y) = (meet x y == x).
Proof. by rewrite /meet -(can_eq f_can) f'_can eq_meetl f_mono. Qed.

Definition IsoMeetSemilattice := MeetMixin meetC meetA meet_eql.

End MeetSemilattice.

Section JoinSemilattice.

Variables (disp : unit) (T : porderType disp).
Variables (disp' : unit) (T' : joinSemilatticeType disp') (f : T -> T').

Variables (f' : T' -> T) (f_can : cancel f f') (f'_can : cancel f' f).
Variable (f_mono : {mono f : x y / x <= y}).

Definition join (x y : T) := f' (join (f x) (f y)).

Lemma joinC : commutative join. Proof. by move=> x y; rewrite /join joinC. Qed.
Lemma joinA : associative join.
Proof. by move=> y x z; rewrite /join !f'_can joinA. Qed.
Lemma join_eql x y : (y <= x) = (join x y == x).
Proof. by rewrite /join -(can_eq f_can) f'_can eq_joinl f_mono. Qed.

Definition IsoJoinSemilattice := JoinMixin joinC joinA join_eql.

End JoinSemilattice.

Section DistrLattice.

Variables (disp : unit) (T : porderType disp).
Variables (disp' : unit) (T' : distrLatticeType disp') (f : T -> T').

Variables (f' : T' -> T) (f_can : cancel f f') (f'_can : cancel f' f).
Variable (f_mono : {mono f : x y / x <= y}).

Lemma meetUl : left_distributive (meet f f') (join f f').
Proof. by move=> x y z; rewrite /meet /join !f'_can meetUl. Qed.

Definition IsoDistrLattice :=
  @DistrLatticeMixin
    _ [latticeType of JoinSemilatticeType
        (MeetSemilatticeType T (IsoMeetSemilattice f_can f'_can f_mono))
        (IsoJoinSemilattice f_can f'_can f_mono)] meetUl.

End DistrLattice.

End CanMixin.

Module Exports.
Notation MonoTotalMixin := MonoTotal.
Notation PcanPOrderMixin := PcanPOrder.
Notation CanPOrderMixin := CanPOrder.
Notation PcanOrderMixin := PcanOrder.
Notation CanOrderMixin := CanOrder.
Notation IsoMeetMixin := IsoMeetSemilattice.
Notation IsoJoinMixin := IsoJoinSemilattice.
Notation IsoDistrLatticeMixin := IsoDistrLattice.
End Exports.
End CanMixin.
Import CanMixin.Exports.

Module SubOrder.

Section Partial.
Context {disp : unit} {T : porderType disp} (P : {pred T}) (sT : subType P).

Definition sub_POrderMixin := PcanPOrderMixin (@valK _ _ sT).
Canonical sub_POrderType := Eval hnf in POrderType disp sT sub_POrderMixin.

Lemma leEsub (x y : sT) : (x <= y) = (val x <= val y). Proof. by []. Qed.
Lemma ltEsub (x y : sT) : (x < y) = (val x < val y). Proof. by []. Qed.

End Partial.

Section Total.
Context {disp : unit} {T : orderType disp} (P : {pred T}) (sT : subType P).

Definition sub_TotalOrderMixin : totalPOrderMixin sT :=
  @MonoTotalMixin _ _ _ _ val (fun _ _ => erefl) (@le_total _ T).
Canonical sub_MeetSemilatticeType :=
  Eval hnf in MeetSemilatticeType sT sub_TotalOrderMixin.
Canonical sub_JoinSemilatticeType :=
  Eval hnf in JoinSemilatticeType sT sub_TotalOrderMixin.
Canonical sub_LatticeType := [latticeType of sT].
Canonical sub_DistrLatticeType :=
  Eval hnf in DistrLatticeType sT sub_TotalOrderMixin.
Canonical sub_OrderType := Eval hnf in OrderType sT sub_TotalOrderMixin.

End Total.
Arguments sub_TotalOrderMixin {disp T} [P].

Module Exports.
Notation "[ 'porderMixin' 'of' T 'by' <: ]" :=
  (sub_POrderMixin _ : lePOrderMixin [eqType of T])
  (at level 0, format "[ 'porderMixin'  'of'  T  'by'  <: ]") : form_scope.

Notation "[ 'totalOrderMixin' 'of' T 'by' <: ]" :=
  (sub_TotalOrderMixin _ : totalPOrderMixin T)
  (at level 0, only parsing) : form_scope.

Canonical sub_POrderType.
Canonical sub_MeetSemilatticeType.
Canonical sub_JoinSemilatticeType.
Canonical sub_LatticeType.
Canonical sub_DistrLatticeType.
Canonical sub_OrderType.

Definition leEsub := @leEsub.
Definition ltEsub := @ltEsub.
End Exports.
End SubOrder.
Import SubOrder.Exports.

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

Fact nat_display : unit. Proof. exact: tt. Qed.

Lemma ltn_def x y : (x < y)%N = (y != x) && (x <= y)%N.
Proof. by rewrite ltn_neqAle eq_sym. Qed.

Definition orderMixin :=
  LeOrderMixin ltn_def (fun _ _ => erefl) (fun _ _ => erefl)
               anti_leq leq_trans leq_total.

Canonical porderType := POrderType nat_display nat orderMixin.
Canonical bPOrderType := BPOrderType nat (BottomMixin leq0n).
Canonical meetSemilatticeType := MeetSemilatticeType nat orderMixin.
Canonical bMeetSemilatticeType := [bMeetSemilatticeType of nat].
Canonical joinSemilatticeType := JoinSemilatticeType nat orderMixin.
Canonical bJoinSemilatticeType := [bJoinSemilatticeType of nat].
Canonical latticeType := [latticeType of nat].
Canonical bLatticeType := [bLatticeType of nat].
Canonical distrLatticeType := DistrLatticeType nat orderMixin.
Canonical bDistrLatticeType := [bDistrLatticeType of nat].
Canonical orderType := OrderType nat orderMixin.
Canonical bOrderType := [bOrderType of nat].

Lemma leEnat : le = leq. Proof. by []. Qed.
Lemma ltEnat : lt = ltn. Proof. by []. Qed.
Lemma minEnat : min = minn. Proof. by []. Qed.
Lemma maxEnat : max = maxn. Proof. by []. Qed.
Lemma botEnat : 0%O = 0%N :> nat. Proof. by []. Qed.

End NatOrder.

Module Exports.
Canonical porderType.
Canonical bPOrderType.
Canonical meetSemilatticeType.
Canonical bMeetSemilatticeType.
Canonical joinSemilatticeType.
Canonical bJoinSemilatticeType.
Canonical latticeType.
Canonical bLatticeType.
Canonical distrLatticeType.
Canonical bDistrLatticeType.
Canonical orderType.
Canonical bOrderType.
Definition leEnat := leEnat.
Definition ltEnat := ltEnat.
Definition minEnat := minEnat.
Definition maxEnat := maxEnat.
Definition botEnat := botEnat.
End Exports.
End NatOrder.

Module NatMonotonyTheory.
Section NatMonotonyTheory.
Import NatOrder.Exports.

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

Fact dvd_display : unit. Proof. exact: tt. Qed.

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

Definition t_distrLatticeMixin :=
  DistrMeetJoinMixin le_def (fun _ _ => erefl _)
                     gcdnC lcmnC gcdnA lcmnA joinKI meetKU meetUl gcdnn.

Definition t := nat.

Canonical eqType := [eqType of t].
Canonical choiceType := [choiceType of t].
Canonical countType := [countType of t].
Canonical porderType := POrderType dvd_display t t_distrLatticeMixin.
Canonical bPOrderType :=
  BPOrderType t (BottomMixin (dvd1n : forall m : t, (1 %| m))).
Canonical tPOrderType :=
  TPOrderType t (TopMixin (dvdn0 : forall m : t, (m %| 0))).
Canonical tbPOrderType := [tbPOrderType of t].
Canonical meetSemilatticeType := MeetSemilatticeType t t_distrLatticeMixin.
Canonical bMeetSemilatticeType := [bMeetSemilatticeType of t].
Canonical tMeetSemilatticeType := [tMeetSemilatticeType of t].
Canonical tbMeetSemilatticeType := [tbMeetSemilatticeType of t].
Canonical joinSemilatticeType := JoinSemilatticeType t t_distrLatticeMixin.
Canonical bJoinSemilatticeType := [bJoinSemilatticeType of t].
Canonical tJoinSemilatticeType := [tJoinSemilatticeType of t].
Canonical tbJoinSemilatticeType := [tbJoinSemilatticeType of t].
Canonical latticeType := [latticeType of t].
Canonical bLatticeType := [bLatticeType of t].
Canonical tLatticeType := [tLatticeType of t].
Canonical tbLatticeType := [tbLatticeType of t].
Canonical distrLatticeType := DistrLatticeType t t_distrLatticeMixin.
Canonical bDistrLatticeType := [bDistrLatticeType of t].
Canonical tDistrLatticeType := [tDistrLatticeType of t].
Canonical tbDistrLatticeType := [tbDistrLatticeType of t].

Import DvdSyntax.
Lemma dvdE : dvd = dvdn :> rel t. Proof. by []. Qed.
Lemma sdvdE (m n : t) : m %<| n = (n != m) && (m %| n). Proof. by []. Qed.
Lemma gcdE : gcd = gcdn :> (t -> t -> t). Proof. by []. Qed.
Lemma lcmE : lcm = lcmn :> (t -> t -> t). Proof. by []. Qed.
Lemma nat1E : nat1 = 1%N :> t. Proof. by []. Qed.
Lemma nat0E : nat0 = 0%N :> t. Proof. by []. Qed.

End NatDvd.
Module Exports.
Notation natdvd := t.
Canonical eqType.
Canonical choiceType.
Canonical countType.
Canonical porderType.
Canonical bPOrderType.
Canonical tPOrderType.
Canonical tbPOrderType.
Canonical meetSemilatticeType.
Canonical bMeetSemilatticeType.
Canonical tMeetSemilatticeType.
Canonical tbMeetSemilatticeType.
Canonical joinSemilatticeType.
Canonical bJoinSemilatticeType.
Canonical tJoinSemilatticeType.
Canonical tbJoinSemilatticeType.
Canonical latticeType.
Canonical bLatticeType.
Canonical tLatticeType.
Canonical tbLatticeType.
Canonical distrLatticeType.
Canonical bDistrLatticeType.
Canonical tDistrLatticeType.
Canonical tbDistrLatticeType.
Definition dvdEnat := dvdE.
Definition sdvdEnat := sdvdE.
Definition gcdEnat := gcdE.
Definition lcmEnat := lcmE.
Definition nat1E := nat1E.
Definition nat0E := nat0E.
End Exports.
End NatDvd.

(***********************************)
(* Canonical structures on ordinal *)
(***********************************)

Module OrdinalOrder.
Section OrdinalOrder.
Import NatOrder.

Lemma ord_display : unit. Proof. exact: tt. Qed.

Section PossiblyTrivial.
Variable (n : nat).

Definition porderMixin := [porderMixin of 'I_n by <:].
Canonical porderType := POrderType ord_display 'I_n (porderMixin).

Definition orderMixin := [totalOrderMixin of 'I_n by <:].
Canonical meetSemilatticeType := MeetSemilatticeType 'I_n orderMixin.
Canonical joinSemilatticeType := JoinSemilatticeType 'I_n orderMixin.
Canonical latticeType := [latticeType of 'I_n].
Canonical distrLatticeType := DistrLatticeType 'I_n orderMixin.
Canonical orderType := OrderType 'I_n orderMixin.
Canonical finPOrderType := [finPOrderType of 'I_n].
Canonical finLatticeType := [finLatticeType of 'I_n].
Canonical finDistrLatticeType := [finDistrLatticeType of 'I_n].
Canonical finOrderType := [finOrderType of 'I_n].

Lemma leEord : (le : rel 'I_n) = leq. Proof. by []. Qed.
Lemma ltEord : (lt : rel 'I_n) = (fun m n => m < n)%N. Proof. by []. Qed.
End PossiblyTrivial.

Section NonTrivial.
Variable (n' : nat).
Let n := n'.+1.

Canonical bPOrderType :=
  BPOrderType 'I_n (BottomMixin (leq0n : forall x, ord0 <= x)).
Canonical tPOrderType :=
  TPOrderType 'I_n (TopMixin (@leq_ord _ : forall x, x <= ord_max)).
Canonical tbPOrderType := [tbPOrderType of 'I_n].
Canonical bMeetSemilatticeType := [bMeetSemilatticeType of 'I_n].
Canonical tMeetSemilatticeType := [tMeetSemilatticeType of 'I_n].
Canonical tbMeetSemilatticeType := [tbMeetSemilatticeType of 'I_n].
Canonical bJoinSemilatticeType := [bJoinSemilatticeType of 'I_n].
Canonical tJoinSemilatticeType := [tJoinSemilatticeType of 'I_n].
Canonical tbJoinSemilatticeType := [tbJoinSemilatticeType of 'I_n].
Canonical bLatticeType := [bLatticeType of 'I_n].
Canonical tLatticeType := [tLatticeType of 'I_n].
Canonical tbLatticeType := [tbLatticeType of 'I_n].
Canonical bDistrLatticeType := [bDistrLatticeType of 'I_n].
Canonical tDistrLatticeType := [tDistrLatticeType of 'I_n].
Canonical tbDistrLatticeType := [tbDistrLatticeType of 'I_n].
Canonical bOrderType := [bOrderType of 'I_n].
Canonical tOrderType := [tOrderType of 'I_n].
Canonical tbOrderType := [tbOrderType of 'I_n].

Lemma botEord : 0%O = ord0. Proof. by []. Qed.
Lemma topEord : 1%O = ord_max. Proof. by []. Qed.

End NonTrivial.

End OrdinalOrder.

Module Exports.
Canonical porderType.
Canonical bPOrderType.
Canonical tPOrderType.
Canonical tbPOrderType.
Canonical meetSemilatticeType.
Canonical bMeetSemilatticeType.
Canonical tMeetSemilatticeType.
Canonical tbMeetSemilatticeType.
Canonical joinSemilatticeType.
Canonical bJoinSemilatticeType.
Canonical tJoinSemilatticeType.
Canonical tbJoinSemilatticeType.
Canonical latticeType.
Canonical bLatticeType.
Canonical tLatticeType.
Canonical tbLatticeType.
Canonical distrLatticeType.
Canonical bDistrLatticeType.
Canonical tDistrLatticeType.
Canonical tbDistrLatticeType.
Canonical orderType.
Canonical bOrderType.
Canonical tOrderType.
Canonical tbOrderType.
Canonical finPOrderType.
Canonical finLatticeType.
Canonical finDistrLatticeType.
Canonical finOrderType.

Definition leEord := leEord.
Definition ltEord := ltEord.
Definition botEord := botEord.
Definition topEord := topEord.
End Exports.
End OrdinalOrder.

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

Definition orderMixin :=
  LeOrderMixin ltn_def andbE orbE anti leq_trans leq_total.

Canonical porderType := POrderType bool_display bool orderMixin.
Canonical bPOrderType := BPOrderType bool (@BottomMixin _ _ false leq0n).
Canonical tPOrderType := TPOrderType bool (@TopMixin _ _ true leq_b1).
Canonical tbPOrderType := [tbPOrderType of bool].
Canonical meetSemilatticeType := MeetSemilatticeType bool orderMixin.
Canonical bMeetSemilatticeType := [bMeetSemilatticeType of bool].
Canonical tMeetSemilatticeType := [tMeetSemilatticeType of bool].
Canonical tbMeetSemilatticeType := [tbMeetSemilatticeType of bool].
Canonical joinSemilatticeType := JoinSemilatticeType bool orderMixin.
Canonical bJoinSemilatticeType := [bJoinSemilatticeType of bool].
Canonical tJoinSemilatticeType := [tJoinSemilatticeType of bool].
Canonical tbJoinSemilatticeType := [tbJoinSemilatticeType of bool].
Canonical latticeType := [latticeType of bool].
Canonical bLatticeType := [bLatticeType of bool].
Canonical tLatticeType := [tLatticeType of bool].
Canonical tbLatticeType := [tbLatticeType of bool].
Canonical distrLatticeType := DistrLatticeType bool orderMixin.
Canonical bDistrLatticeType := [bDistrLatticeType of bool].
Canonical tDistrLatticeType := [tDistrLatticeType of bool].
Canonical tbDistrLatticeType := [tbDistrLatticeType of bool].
Canonical orderType := OrderType bool orderMixin.
Canonical bOrderType := [bOrderType of bool].
Canonical tOrderType := [tOrderType of bool].
Canonical tbOrderType := [tbOrderType of bool].
Canonical cbDistrLatticeType := CBDistrLatticeType bool
  (@CBDistrLatticeMixin _ _ (fun x y => x && ~~ y) subKI joinIB).
Canonical ctbDistrLatticeType := CTBDistrLatticeType bool
  (@CTBDistrLatticeMixin _ _ sub negb (fun x => erefl : ~~ x = sub true x)).

Canonical finPOrderType := [finPOrderType of bool].
Canonical finBPOrderType := [finBPOrderType of bool].
Canonical finTPOrderType := [finTPOrderType of bool].
Canonical finTBPOrderType := [finTBPOrderType of bool].
Canonical finMeetSemilatticeType := [finMeetSemilatticeType of bool].
Canonical finBMeetSemilatticeType := [finBMeetSemilatticeType of bool].
Canonical finJoinSemilatticeType := [finJoinSemilatticeType of bool].
Canonical finTJoinSemilatticeType := [finTJoinSemilatticeType of bool].
Canonical finLatticeType :=  [finLatticeType of bool].
Canonical finTBLatticeType :=  [finTBLatticeType of bool].
Canonical finDistrLatticeType :=  [finDistrLatticeType of bool].
Canonical finTBDistrLatticeType :=  [finTBDistrLatticeType of bool].
Canonical finCTBDistrLatticeType := [finCTBDistrLatticeType of bool].
Canonical finOrderType := [finOrderType of bool].
Canonical finTBOrderType := [finTBOrderType of bool].

Lemma leEbool : le = (leq : rel bool). Proof. by []. Qed.
Lemma ltEbool x y : (x < y) = (x < y)%N. Proof. by []. Qed.
Lemma andEbool : meet = andb. Proof. by []. Qed.
Lemma orEbool : meet = andb. Proof. by []. Qed.
Lemma subEbool x y : x `\` y = x && ~~ y. Proof. by []. Qed.
Lemma complEbool : compl = negb. Proof. by []. Qed.

End BoolOrder.
Module Exports.
Canonical porderType.
Canonical bPOrderType.
Canonical tPOrderType.
Canonical tbPOrderType.
Canonical meetSemilatticeType.
Canonical bMeetSemilatticeType.
Canonical tMeetSemilatticeType.
Canonical tbMeetSemilatticeType.
Canonical joinSemilatticeType.
Canonical bJoinSemilatticeType.
Canonical tJoinSemilatticeType.
Canonical tbJoinSemilatticeType.
Canonical latticeType.
Canonical bLatticeType.
Canonical tLatticeType.
Canonical tbLatticeType.
Canonical distrLatticeType.
Canonical bDistrLatticeType.
Canonical tDistrLatticeType.
Canonical tbDistrLatticeType.
Canonical orderType.
Canonical bOrderType.
Canonical tOrderType.
Canonical tbOrderType.
Canonical cbDistrLatticeType.
Canonical ctbDistrLatticeType.
Canonical finPOrderType.
Canonical finBPOrderType.
Canonical finTPOrderType.
Canonical finTBPOrderType.
Canonical finMeetSemilatticeType.
Canonical finBMeetSemilatticeType.
Canonical finJoinSemilatticeType.
Canonical finTJoinSemilatticeType.
Canonical finLatticeType.
Canonical finTBLatticeType.
Canonical finDistrLatticeType.
Canonical finTBDistrLatticeType.
Canonical finCTBDistrLatticeType.
Canonical finOrderType.
Canonical finTBOrderType.
Definition leEbool := leEbool.
Definition ltEbool := ltEbool.
Definition andEbool := andEbool.
Definition orEbool := orEbool.
Definition subEbool := subEbool.
Definition complEbool := complEbool.
End Exports.
End BoolOrder.

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

Definition type (disp : unit) (T T' : Type) := (T * T')%type.

Context {disp1 disp2 disp3 : unit}.

Local Notation "T * T'" := (type disp3 T T') : type_scope.

Canonical eqType (T T' : eqType) := Eval hnf in [eqType of T * T'].
Canonical choiceType (T T' : choiceType) := Eval hnf in [choiceType of T * T'].
Canonical countType (T T' : countType) := Eval hnf in [countType of T * T'].
Canonical finType (T T' : finType) := Eval hnf in [finType of T * T'].

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

Definition porderMixin := LePOrderMixin (rrefl _) refl anti trans.
Canonical porderType := POrderType disp3 (T * T') porderMixin.

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

Section BPOrder.
Variable (T : bPOrderType disp1) (T' : bPOrderType disp2).

Fact le0x (x : T * T') : (0, 0) <= x :> T * T'.
Proof. by rewrite leEprod !le0x. Qed.

Canonical bPOrderType := BPOrderType (T * T') (BottomMixin le0x).

Lemma botEprod : 0 = (0, 0) :> T * T'. Proof. by []. Qed.

End BPOrder.

Section TPOrder.
Variable (T : tPOrderType disp1) (T' : tPOrderType disp2).

Fact lex1 (x : T * T') : x <= (1, 1).
Proof. by rewrite leEprod !lex1. Qed.

Canonical tPOrderType := TPOrderType (T * T') (TopMixin lex1).

Lemma topEprod : 1 = (1, 1) :> T * T'. Proof. by []. Qed.

End TPOrder.

Canonical tbPOrderType (T : tbPOrderType disp1) (T' : tbPOrderType disp2) :=
  [tbPOrderType of T * T'].

Section MeetSemilattice.
Variable (T : meetSemilatticeType disp1) (T' : meetSemilatticeType disp2).
Implicit Types (x y : T * T').

Definition meet x y := (x.1 `&` y.1, x.2 `&` y.2).

Fact meetC : commutative meet.
Proof. by move=> ? ?; congr pair; rewrite meetC. Qed.

Fact meetA : associative meet.
Proof. by move=> ? ? ?; congr pair; rewrite meetA. Qed.

Fact leEmeet x y : (x <= y) = (meet x y == x).
Proof. by rewrite eqE /= -!leEmeet. Qed.

Definition meetMixin := MeetMixin meetC meetA leEmeet.
Canonical meetSemilatticeType := MeetSemilatticeType (T * T') meetMixin.

Lemma meetEprod x y : x `&` y = (x.1 `&` y.1, x.2 `&` y.2). Proof. by []. Qed.

End MeetSemilattice.

Canonical bMeetSemilatticeType
          (T : bMeetSemilatticeType disp1) (T' : bMeetSemilatticeType disp2) :=
  [bMeetSemilatticeType of T * T'].
Canonical tMeetSemilatticeType
          (T : tMeetSemilatticeType disp1) (T' : tMeetSemilatticeType disp2) :=
  [tMeetSemilatticeType of T * T'].
Canonical tbMeetSemilatticeType
          (T : tbMeetSemilatticeType disp1)
          (T' : tbMeetSemilatticeType disp2) :=
  [tbMeetSemilatticeType of T * T'].

Section JoinSemilattice.
Variable (T : joinSemilatticeType disp1) (T' : joinSemilatticeType disp2).
Implicit Types (x y : T * T').

Definition join x y := (x.1 `|` y.1, x.2 `|` y.2).

Fact joinC : commutative join.
Proof. by move=> ? ?; congr pair; rewrite joinC. Qed.

Fact joinA : associative join.
Proof. by move=> ? ? ?; congr pair; rewrite joinA. Qed.

Fact leEjoin x y : (y <= x) = (join x y == x).
Proof. by rewrite eqE /= !eq_joinl. Qed.

Definition joinMixin := JoinMixin joinC joinA leEjoin.
Canonical joinSemilatticeType := JoinSemilatticeType (T * T') joinMixin.

Lemma joinEprod x y : x `|` y = (x.1 `|` y.1, x.2 `|` y.2). Proof. by []. Qed.

End JoinSemilattice.

Canonical bJoinSemilatticeType
          (T : bJoinSemilatticeType disp1) (T' : bJoinSemilatticeType disp2) :=
  [bJoinSemilatticeType of T * T'].
Canonical tJoinSemilatticeType
          (T : tJoinSemilatticeType disp1) (T' : tJoinSemilatticeType disp2) :=
  [tJoinSemilatticeType of T * T'].
Canonical tbJoinSemilatticeType
          (T : tbJoinSemilatticeType disp1)
          (T' : tbJoinSemilatticeType disp2) :=
  [tbJoinSemilatticeType of T * T'].

Canonical latticeType (T : latticeType disp1) (T' : latticeType disp2) :=
  [latticeType of T * T'].
Canonical bLatticeType (T : bLatticeType disp1) (T' : bLatticeType disp2) :=
  [bLatticeType of T * T'].
Canonical tLatticeType (T : tLatticeType disp1) (T' : tLatticeType disp2) :=
  [tLatticeType of T * T'].
Canonical tbLatticeType (T : tbLatticeType disp1) (T' : tbLatticeType disp2) :=
  [tbLatticeType of T * T'].

Section DistrLattice.
Variable (T : distrLatticeType disp1) (T' : distrLatticeType disp2).

Fact meetUl : left_distributive (@meet T T') (@join T T').
Proof. by move=> ? ? ?; congr pair; rewrite meetUl. Qed.

Definition distrLatticeMixin := DistrLatticeMixin meetUl.
Canonical distrLatticeType := DistrLatticeType (T * T') distrLatticeMixin.

End DistrLattice.

Canonical bDistrLatticeType
          (T : bDistrLatticeType disp1) (T' : bDistrLatticeType disp2) :=
  [bDistrLatticeType of T * T'].
Canonical tDistrLatticeType
          (T : tDistrLatticeType disp1) (T' : tDistrLatticeType disp2) :=
  [tDistrLatticeType of T * T'].
Canonical tbDistrLatticeType
          (T : tbDistrLatticeType disp1) (T' : tbDistrLatticeType disp2) :=
  [tbDistrLatticeType of T * T'].

Section CBDistrLattice.
Variable (T : cbDistrLatticeType disp1) (T' : cbDistrLatticeType disp2).
Implicit Types (x y : T * T').

Definition sub x y := (x.1 `\` y.1, x.2 `\` y.2).

Lemma subKI x y : y `&` sub x y = 0. Proof. by congr pair; rewrite subKI. Qed.

Lemma joinIB x y : x `&` y `|` sub x y = x.
Proof. by case: x => ? ?; congr pair; rewrite joinIB. Qed.

Definition cbDistrLatticeMixin := CBDistrLatticeMixin subKI joinIB.
Canonical cbDistrLatticeType := CBDistrLatticeType (T * T') cbDistrLatticeMixin.

Lemma subEprod x y : x `\` y = (x.1 `\` y.1, x.2 `\` y.2). Proof. by []. Qed.

End CBDistrLattice.

Section CTBDistrLattice.
Variable (T : ctbDistrLatticeType disp1) (T' : ctbDistrLatticeType disp2).
Implicit Types (x y : T * T').

Definition compl x : T * T' := (~` x.1, ~` x.2).

Lemma complE x : compl x = sub 1 x. Proof. by congr pair; rewrite complE. Qed.

Definition ctbDistrLatticeMixin := CTBDistrLatticeMixin complE.
Canonical ctbDistrLatticeType :=
  CTBDistrLatticeType (T * T') ctbDistrLatticeMixin.

Lemma complEprod x : ~` x = (~` x.1, ~` x.2). Proof. by []. Qed.

End CTBDistrLattice.

Canonical finPOrderType (T : finPOrderType disp1)
  (T' : finPOrderType disp2) := [finPOrderType of T * T'].

Canonical finBPOrderType (T : finBPOrderType disp1)
  (T' : finBPOrderType disp2) := [finBPOrderType of T * T'].

Canonical finTPOrderType (T : finTPOrderType disp1)
  (T' : finTPOrderType disp2) := [finTPOrderType of T * T'].

Canonical finTBPOrderType (T : finTBPOrderType disp1)
  (T' : finTBPOrderType disp2) := [finTBPOrderType of T * T'].

Canonical finMeetSemilatticeType (T : finMeetSemilatticeType disp1)
  (T' : finMeetSemilatticeType disp2) := [finMeetSemilatticeType of T * T'].

Canonical finBMeetSemilatticeType (T : finBMeetSemilatticeType disp1)
  (T' : finBMeetSemilatticeType disp2) := [finBMeetSemilatticeType of T * T'].

Canonical finJoinSemilatticeType (T : finJoinSemilatticeType disp1)
  (T' : finJoinSemilatticeType disp2) := [finJoinSemilatticeType of T * T'].

Canonical finTJoinSemilatticeType (T : finTJoinSemilatticeType disp1)
  (T' : finTJoinSemilatticeType disp2) := [finTJoinSemilatticeType of T * T'].

Canonical finLatticeType (T : finLatticeType disp1)
  (T' : finLatticeType disp2) := [finLatticeType of T * T'].

Canonical finTBLatticeType (T : finTBLatticeType disp1)
  (T' : finTBLatticeType disp2) := [finTBLatticeType of T * T'].

Canonical finDistrLatticeType (T : finDistrLatticeType disp1)
  (T' : finDistrLatticeType disp2) := [finDistrLatticeType of T * T'].

Canonical finTBDistrLatticeType (T : finTBDistrLatticeType disp1)
  (T' : finTBDistrLatticeType disp2) := [finTBDistrLatticeType of T * T'].

Canonical finCTBDistrLatticeType (T : finCTBDistrLatticeType disp1)
  (T' : finCTBDistrLatticeType disp2) := [finCTBDistrLatticeType of T * T'].

End ProdOrder.

Module Exports.

Notation "T *prod[ d ] T'" := (type d T T')
  (at level 70, d at next level, format "T  *prod[ d ]  T'") : type_scope.
Notation "T *p T'" := (type prod_display T T')
  (at level 70, format "T  *p  T'") : type_scope.

Canonical eqType.
Canonical choiceType.
Canonical countType.
Canonical finType.
Canonical porderType.
Canonical bPOrderType.
Canonical tPOrderType.
Canonical tbPOrderType.
Canonical meetSemilatticeType.
Canonical bMeetSemilatticeType.
Canonical tMeetSemilatticeType.
Canonical tbMeetSemilatticeType.
Canonical joinSemilatticeType.
Canonical bJoinSemilatticeType.
Canonical tJoinSemilatticeType.
Canonical tbJoinSemilatticeType.
Canonical bLatticeType.
Canonical tLatticeType.
Canonical tbLatticeType.
Canonical distrLatticeType.
Canonical tDistrLatticeType.
Canonical tbDistrLatticeType.
Canonical cbDistrLatticeType.
Canonical ctbDistrLatticeType.
Canonical finPOrderType.
Canonical finBPOrderType.
Canonical finTPOrderType.
Canonical finTBPOrderType.
Canonical finMeetSemilatticeType.
Canonical finBMeetSemilatticeType.
Canonical finJoinSemilatticeType.
Canonical finTJoinSemilatticeType.
Canonical finLatticeType.
Canonical finTBLatticeType.
Canonical finDistrLatticeType.
Canonical finTBDistrLatticeType.
Canonical finCTBDistrLatticeType.

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
Import ProdOrder.Exports.

Module DefaultProdOrder.
Section DefaultProdOrder.
Context {disp1 disp2 : unit}.

Canonical prod_porderType (T : porderType disp1) (T' : porderType disp2) :=
  [porderType of T * T' for [porderType of T *p T']].
Canonical prod_bPOrderType (T : bPOrderType disp1) (T' : bPOrderType disp2) :=
  [bPOrderType of T * T' for [bPOrderType of T *p T']].
Canonical prod_tPOrderType (T : tPOrderType disp1) (T' : tPOrderType disp2) :=
  [tPOrderType of T * T' for [tPOrderType of T *p T']].
Canonical prod_tbPOrderType
    (T : tbPOrderType disp1) (T' : tbPOrderType disp2) :=
  [tbPOrderType of T * T'].
Canonical prod_meetSemilatticeType
    (T : meetSemilatticeType disp1) (T' : meetSemilatticeType disp2) :=
  [meetSemilatticeType of T * T' for [meetSemilatticeType of T *p T']].
Canonical prod_bMeetSemilatticeType
    (T : bMeetSemilatticeType disp1) (T' : bMeetSemilatticeType disp2) :=
  [bMeetSemilatticeType of T * T'].
Canonical prod_tMeetSemilatticeType
    (T : tMeetSemilatticeType disp1) (T' : tMeetSemilatticeType disp2) :=
  [tMeetSemilatticeType of T * T'].
Canonical prod_tbMeetSemilatticeType
    (T : tbMeetSemilatticeType disp1) (T' : tbMeetSemilatticeType disp2) :=
  [tbMeetSemilatticeType of T * T'].
Canonical prod_joinSemilatticeType
    (T : joinSemilatticeType disp1) (T' : joinSemilatticeType disp2) :=
  [joinSemilatticeType of T * T' for [joinSemilatticeType of T *p T']].
Canonical prod_bJoinSemilatticeType
    (T : bJoinSemilatticeType disp1) (T' : bJoinSemilatticeType disp2) :=
  [bJoinSemilatticeType of T * T'].
Canonical prod_tJoinSemilatticeType
    (T : tJoinSemilatticeType disp1) (T' : tJoinSemilatticeType disp2) :=
  [tJoinSemilatticeType of T * T'].
Canonical prod_tbJoinSemilatticeType
    (T : tbJoinSemilatticeType disp1) (T' : tbJoinSemilatticeType disp2) :=
  [tbJoinSemilatticeType of T * T'].
Canonical prod_latticeType (T : latticeType disp1) (T' : latticeType disp2) :=
  [latticeType of T * T'].
Canonical prod_bLatticeType (T : bLatticeType disp1)
    (T' : bLatticeType disp2) := [bLatticeType of T * T'].
Canonical prod_tLatticeType (T : tLatticeType disp1)
    (T' : tLatticeType disp2) := [tLatticeType of T * T'].
Canonical prod_tbLatticeType (T : tbLatticeType disp1)
    (T' : tbLatticeType disp2) := [tbLatticeType of T * T'].
Canonical prod_distrLatticeType
    (T : distrLatticeType disp1) (T' : distrLatticeType disp2) :=
  [distrLatticeType of T * T' for [distrLatticeType of T *p T']].
Canonical prod_bDistrLatticeType (T : bDistrLatticeType disp1)
    (T' : bDistrLatticeType disp2) := [bDistrLatticeType of T * T'].
Canonical prod_tDistrLatticeType (T : tDistrLatticeType disp1)
    (T' : tDistrLatticeType disp2) := [tDistrLatticeType of T * T'].
Canonical prod_tbDistrLatticeType (T : tbDistrLatticeType disp1)
    (T' : tbDistrLatticeType disp2) := [tbDistrLatticeType of T * T'].
Canonical prod_cbDistrLatticeType
    (T : cbDistrLatticeType disp1) (T' : cbDistrLatticeType disp2) :=
  [cbDistrLatticeType of T * T' for [cbDistrLatticeType of T *p T']].
Canonical prod_ctbDistrLatticeType
    (T : ctbDistrLatticeType disp1) (T' : ctbDistrLatticeType disp2) :=
  [ctbDistrLatticeType of T * T' for [ctbDistrLatticeType of T *p T']].
Canonical prod_finPOrderType (T : finPOrderType disp1)
  (T' : finPOrderType disp2) := [finPOrderType of T * T'].
Canonical prod_finBPOrderType (T : finBPOrderType disp1)
  (T' : finBPOrderType disp2) := [finBPOrderType of T * T'].
Canonical prod_finTPOrderType (T : finTPOrderType disp1)
  (T' : finTPOrderType disp2) := [finTPOrderType of T * T'].
Canonical prod_finTBPOrderType (T : finTBPOrderType disp1)
  (T' : finTBPOrderType disp2) := [finTBPOrderType of T * T'].
Canonical prod_finMeetSemilatticeType (T : finMeetSemilatticeType disp1)
  (T' : finMeetSemilatticeType disp2) := [finMeetSemilatticeType of T * T'].
Canonical prod_finBMeetSemilatticeType (T : finBMeetSemilatticeType disp1)
  (T' : finBMeetSemilatticeType disp2) := [finBMeetSemilatticeType of T * T'].
Canonical prod_finJoinSemilatticeType (T : finJoinSemilatticeType disp1)
  (T' : finJoinSemilatticeType disp2) := [finJoinSemilatticeType of T * T'].
Canonical prod_finTJoinSemilatticeType (T : finTJoinSemilatticeType disp1)
  (T' : finTJoinSemilatticeType disp2) := [finTJoinSemilatticeType of T * T'].
Canonical prod_finLatticeType (T : finLatticeType disp1)
  (T' : finLatticeType disp2) := [finLatticeType of T * T'].
Canonical prod_finTBLatticeType (T : finTBLatticeType disp1)
  (T' : finTBLatticeType disp2) := [finTBLatticeType of T * T'].
Canonical prod_finDistrLatticeType (T : finDistrLatticeType disp1)
  (T' : finDistrLatticeType disp2) := [finDistrLatticeType of T * T'].
Canonical prod_finTBDistrLatticeType (T : finTBDistrLatticeType disp1)
  (T' : finTBDistrLatticeType disp2) := [finTBDistrLatticeType of T * T'].
Canonical prod_finCTBDistrLatticeType (T : finCTBDistrLatticeType disp1)
  (T' : finCTBDistrLatticeType disp2) := [finCTBDistrLatticeType of T * T'].

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

Definition porderMixin := LePOrderMixin lt_def refl anti trans.
Canonical porderType := POrderType disp2 {t : T & T' t} porderMixin.

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

Section BPOrder.
Variable (T : bPOrderType disp1) (T' : T -> bPOrderType disp2).

Fact le0x (x : {t : T & T' t}) : Tagged T' (0 : T' 0) <= x.
Proof. by rewrite leEsig /=; case: comparableP (le0x (tag x)) => //=. Qed.

Canonical bPOrderType := BPOrderType {t : T & T' t} (BottomMixin le0x).

Lemma botEsig : 0 = Tagged T' (0 : T' 0). Proof. by []. Qed.

End BPOrder.

Section TPOrder.
Variable (T : tPOrderType disp1) (T' : T -> tPOrderType disp2).

Fact lex1 (x : {t : T & T' t}) : x <= Tagged T' (1 : T' 1).
Proof.
rewrite leEsig /=; case: comparableP (lex1 (tag x)) => //=.
by case: x => //= p px x0; rewrite x0 in px *; rewrite tagged_asE lex1.
Qed.

Canonical tPOrderType := TPOrderType {t : T & T' t} (TopMixin lex1).

Lemma topEsig : 1 = Tagged T' (1 : T' 1). Proof. by []. Qed.

End TPOrder.

Canonical tbPOrderType
    (T : tbPOrderType disp1) (T' : T -> tbPOrderType disp2) :=
  [tbPOrderType of {t : T & T' t}].

Section Total.
Variable (T : orderType disp1) (T' : T -> orderType disp2).
Implicit Types (x y : {t : T & T' t}).

Fact total : totalPOrderMixin {t : T & T' t}.
Proof.
move=> x y; rewrite !leEsig; case: (ltgtP (tag x) (tag y)) => //=.
case: x y => [x x'] [y y']/= eqxy; elim: _ /eqxy in y' *.
by rewrite !tagged_asE le_total.
Qed.

Canonical meetSemilatticeType := MeetSemilatticeType {t : T & T' t} total.
Canonical joinSemilatticeType := JoinSemilatticeType {t : T & T' t} total.
Canonical latticeType := [latticeType of {t : T & T' t}].
Canonical distrLatticeType := DistrLatticeType {t : T & T' t} total.
Canonical orderType := OrderType {t : T & T' t} total.

End Total.

Section BTotal.
Variable (T : bOrderType disp1) (T' : T -> bOrderType disp2).

Canonical bMeetSemilatticeType := [bMeetSemilatticeType of {t : T & T' t}].
Canonical bJoinSemilatticeType := [bJoinSemilatticeType of {t : T & T' t}].
Canonical bLatticeType := [bLatticeType of {t : T & T' t}].
Canonical bDistrLatticeType := [bDistrLatticeType of {t : T & T' t}].
Canonical bOrderType := [bOrderType of {t : T & T' t}].

End BTotal.

Section TTotal.
Variable (T : tOrderType disp1) (T' : T -> tOrderType disp2).

Canonical tMeetSemilatticeType := [tMeetSemilatticeType of {t : T & T' t}].
Canonical tJoinSemilatticeType := [tJoinSemilatticeType of {t : T & T' t}].
Canonical tLatticeType := [tLatticeType of {t : T & T' t}].
Canonical tDistrLatticeType := [tDistrLatticeType of {t : T & T' t}].
Canonical tOrderType := [tOrderType of {t : T & T' t}].

End TTotal.

Section TBTotal.
Variable (T : tbOrderType disp1) (T' : T -> tbOrderType disp2).

Canonical tbMeetSemilatticeType := [tbMeetSemilatticeType of {t : T & T' t}].
Canonical tbJoinSemilatticeType := [tbJoinSemilatticeType of {t : T & T' t}].
Canonical tbLatticeType := [tbLatticeType of {t : T & T' t}].
Canonical tbDistrLatticeType := [tbDistrLatticeType of {t : T & T' t}].
Canonical tbOrderType := [tbOrderType of {t : T & T' t}].

End TBTotal.

Canonical finPOrderType (T : finPOrderType disp1)
  (T' : T -> finPOrderType disp2) := [finPOrderType of {t : T & T' t}].
Canonical finBPOrderType (T : finBPOrderType disp1)
  (T' : T -> finBPOrderType disp2) := [finBPOrderType of {t : T & T' t}].
Canonical finTPOrderType (T : finTPOrderType disp1)
  (T' : T -> finTPOrderType disp2) := [finTPOrderType of {t : T & T' t}].
Canonical finTBPOrderType (T : finTBPOrderType disp1)
  (T' : T -> finTBPOrderType disp2) := [finTBPOrderType of {t : T & T' t}].

Section FinTotal.
Variable (T : finOrderType disp1) (T' : T -> finOrderType disp2).

Canonical finLatticeType := [finLatticeType of {t : T & T' t}].
Canonical finDistrLatticeType := [finDistrLatticeType of {t : T & T' t}].
Canonical finOrderType := [finOrderType of {t : T & T' t}].

End FinTotal.

Section FinTBTotal.
Variable (T : finTBOrderType disp1) (T' : T -> finTBOrderType disp2).

Canonical finTBLatticeType := [finTBLatticeType of {t : T & T' t}].
Canonical finTBDistrLatticeType := [finTBDistrLatticeType of {t : T & T' t}].
Canonical finTBOrderType := [finTBOrderType of {t : T & T' t}].

End FinTBTotal.

End SigmaOrder.

Module Exports.

Canonical porderType.
Canonical bPOrderType.
Canonical tPOrderType.
Canonical tbPOrderType.
Canonical meetSemilatticeType.
Canonical joinSemilatticeType.
Canonical latticeType.
Canonical distrLatticeType.
Canonical orderType.
Canonical bMeetSemilatticeType.
Canonical bJoinSemilatticeType.
Canonical bLatticeType.
Canonical bDistrLatticeType.
Canonical bOrderType.
Canonical tMeetSemilatticeType.
Canonical tJoinSemilatticeType.
Canonical tLatticeType.
Canonical tDistrLatticeType.
Canonical tOrderType.
Canonical tbMeetSemilatticeType.
Canonical tbJoinSemilatticeType.
Canonical tbLatticeType.
Canonical tbDistrLatticeType.
Canonical tbOrderType.
Canonical finPOrderType.
Canonical finBPOrderType.
Canonical finTPOrderType.
Canonical finTBPOrderType.
Canonical finLatticeType.
Canonical finDistrLatticeType.
Canonical finOrderType.
Canonical finTBLatticeType.
Canonical finTBDistrLatticeType.
Canonical finTBOrderType.

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
Import SigmaOrder.Exports.

(*************************************************)
(* We declare a "copy" of the cartesian product, *)
(* which has canonical lexicographic order.      *)
(*************************************************)

Module ProdLexiOrder.
Section ProdLexiOrder.

Definition type (disp : unit) (T T' : Type) := (T * T')%type.

Context {disp1 disp2 disp3 : unit}.

Local Notation "T * T'" := (type disp3 T T') : type_scope.

Canonical eqType (T T' : eqType) := Eval hnf in [eqType of T * T'].
Canonical choiceType (T T' : choiceType) := Eval hnf in [choiceType of T * T'].
Canonical countType (T T' : countType) := Eval hnf in [countType of T * T'].
Canonical finType (T T' : finType) := Eval hnf in [finType of T * T'].

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

Definition porderMixin := LePOrderMixin lt_def refl anti trans.
Canonical porderType := POrderType disp3 (T * T') porderMixin.

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

Section BPOrder.
Variable (T : bPOrderType disp1) (T' : bPOrderType disp2).

Fact le0x (x : T * T') : (0, 0) <= x :> T * T'.
Proof. by case: x => // x1 x2; rewrite leEprodlexi/= !le0x implybT. Qed.

Canonical bPOrderType := BPOrderType (T * T') (BottomMixin le0x).

Lemma botEprodlexi : 0 = (0, 0) :> T * T'. Proof. by []. Qed.

End BPOrder.

Section TPOrder.
Variable (T : tPOrderType disp1) (T' : tPOrderType disp2).

Fact lex1 (x : T * T') : x <= (1, 1) :> T * T'.
Proof. by case: x => // x1 x2; rewrite leEprodlexi/= !lex1 implybT. Qed.

Canonical tPOrderType := TPOrderType (T * T') (TopMixin lex1).

Lemma topEprodlexi : 1 = (1, 1) :> T * T'. Proof. by []. Qed.

End TPOrder.

Canonical tbPOrderType (T : tbPOrderType disp1) (T' : tbPOrderType disp2) :=
  [tbPOrderType of T * T'].

Section Total.
Variable (T : orderType disp1) (T' : orderType disp2).
Implicit Types (x y : T * T').

Fact total : totalPOrderMixin (T * T').
Proof.
by move=> x y; rewrite !leEprodlexi; case: ltgtP => //= _; exact: le_total.
Qed.

Canonical meetSemilatticeType := MeetSemilatticeType (T * T') total.
Canonical joinSemilatticeType := JoinSemilatticeType (T * T') total.
Canonical latticeType := [latticeType of T * T'].
Canonical distrLatticeType := DistrLatticeType (T * T') total.
Canonical orderType := OrderType (T * T') total.

End Total.

Section BTotal.
Variable (T : bOrderType disp1) (T' : bOrderType disp2).

Canonical bMeetSemilatticeType := [bMeetSemilatticeType of T * T'].
Canonical bJoinSemilatticeType := [bJoinSemilatticeType of T * T'].
Canonical bLatticeType := [bLatticeType of T * T'].
Canonical bDistrLatticeType := [bDistrLatticeType of T * T'].
Canonical bOrderType := [bOrderType of T * T'].

End BTotal.

Section TTotal.
Variable (T : tOrderType disp1) (T' : tOrderType disp2).

Canonical tMeetSemilatticeType := [tMeetSemilatticeType of T * T'].
Canonical tJoinSemilatticeType := [tJoinSemilatticeType of T * T'].
Canonical tLatticeType := [tLatticeType of T * T'].
Canonical tDistrLatticeType := [tDistrLatticeType of T * T'].
Canonical tOrderType := [tOrderType of T * T'].

End TTotal.

Section TBTotal.
Variable (T : tbOrderType disp1) (T' : tbOrderType disp2).

Canonical tbMeetSemilatticeType := [tbMeetSemilatticeType of T * T'].
Canonical tbJoinSemilatticeType := [tbJoinSemilatticeType of T * T'].
Canonical tbLatticeType := [tbLatticeType of T * T'].
Canonical tbDistrLatticeType := [tbDistrLatticeType of T * T'].
Canonical tbOrderType := [tbOrderType of T * T'].

End TBTotal.

Canonical finPOrderType (T : finPOrderType disp1)
    (T' : finPOrderType disp2) := [finPOrderType of T * T'].
Canonical finBPOrderType (T : finBPOrderType disp1)
    (T' : finBPOrderType disp2) := [finBPOrderType of T * T'].
Canonical finTPOrderType (T : finTPOrderType disp1)
    (T' : finTPOrderType disp2) := [finTPOrderType of T * T'].
Canonical finTBPOrderType (T : finTBPOrderType disp1)
    (T' : finTBPOrderType disp2) := [finTBPOrderType of T * T'].

Section FinTotal.
Variable (T : finOrderType disp1) (T' : finOrderType disp2).

Canonical finLatticeType := [finLatticeType of T * T'].
Canonical finDistrLatticeType := [finDistrLatticeType of T * T'].
Canonical finOrderType := [finOrderType of T * T'].

End FinTotal.

Section FinTBTotal.
Variable (T : finTBOrderType disp1) (T' : finTBOrderType disp2).

Canonical finTBLatticeType := [finTBLatticeType of T * T'].
Canonical finTBDistrLatticeType := [finTBDistrLatticeType of T * T'].
Canonical finTBOrderType := [finTBOrderType of T * T'].

End FinTBTotal.

Lemma sub_prod_lexi d (T : POrder.Exports.porderType disp1)
                      (T' : POrder.Exports.porderType disp2) :
   subrel (<=%O : rel (T *prod[d] T')) (<=%O : rel (T * T')).
Proof.
by case=> [x1 x2] [y1 y2]; rewrite leEprod leEprodlexi /=; case: comparableP.
Qed.

End ProdLexiOrder.

Module Exports.

Notation "T *lexi[ d ] T'" := (type d T T')
  (at level 70, d at next level, format "T  *lexi[ d ]  T'") : type_scope.
Notation "T *l T'" := (type lexi_display T T')
  (at level 70, format "T  *l  T'") : type_scope.

Canonical eqType.
Canonical choiceType.
Canonical countType.
Canonical finType.
Canonical porderType.
Canonical bPOrderType.
Canonical tPOrderType.
Canonical tbPOrderType.
Canonical meetSemilatticeType.
Canonical joinSemilatticeType.
Canonical latticeType.
Canonical distrLatticeType.
Canonical orderType.
Canonical bMeetSemilatticeType.
Canonical bJoinSemilatticeType.
Canonical bLatticeType.
Canonical bDistrLatticeType.
Canonical bOrderType.
Canonical tMeetSemilatticeType.
Canonical tJoinSemilatticeType.
Canonical tLatticeType.
Canonical tDistrLatticeType.
Canonical tOrderType.
Canonical tbMeetSemilatticeType.
Canonical tbJoinSemilatticeType.
Canonical tbLatticeType.
Canonical tbDistrLatticeType.
Canonical tbOrderType.
Canonical finPOrderType.
Canonical finBPOrderType.
Canonical finTPOrderType.
Canonical finTBPOrderType.
Canonical finLatticeType.
Canonical finDistrLatticeType.
Canonical finOrderType.
Canonical finTBLatticeType.
Canonical finTBDistrLatticeType.
Canonical finTBOrderType.

Definition leEprodlexi := @leEprodlexi.
Definition ltEprodlexi := @ltEprodlexi.
Definition lexi_pair := @lexi_pair.
Definition ltxi_pair := @ltxi_pair.
Definition topEprodlexi := @topEprodlexi.
Definition botEprodlexi := @botEprodlexi.
Definition sub_prod_lexi := @sub_prod_lexi.

End Exports.
End ProdLexiOrder.
Import ProdLexiOrder.Exports.

Module DefaultProdLexiOrder.
Section DefaultProdLexiOrder.
Context {disp1 disp2 : unit}.

Canonical prodlexi_porderType
    (T : porderType disp1) (T' : porderType disp2) :=
  [porderType of T * T' for [porderType of T *l T']].
Canonical prodlexi_bPOrderType
    (T : bPOrderType disp1) (T' : bPOrderType disp2) :=
  [bPOrderType of T * T' for [bPOrderType of T *l T']].
Canonical prodlexi_tPOrderType
    (T : tPOrderType disp1) (T' : tPOrderType disp2) :=
  [tPOrderType of T * T' for [tPOrderType of T *l T']].
Canonical prodlexi_tbPOrderType (T : tbPOrderType disp1)
    (T' : tbPOrderType disp2) := [tbPOrderType of T * T'].
Canonical prodlexi_meetSemilatticeType
    (T : orderType disp1) (T' : orderType disp2) :=
  [meetSemilatticeType of T * T' for [meetSemilatticeType of T *l T']].
Canonical prodlexi_joinSemilatticeType
    (T : orderType disp1) (T' : orderType disp2) :=
  [joinSemilatticeType of T * T' for [joinSemilatticeType of T *l T']].
Canonical prodlexi_latticeType (T : orderType disp1)
    (T' : orderType disp2) := [latticeType of T * T'].
Canonical prodlexi_distrLatticeType
    (T : orderType disp1) (T' : orderType disp2) :=
  [distrLatticeType of T * T' for [distrLatticeType of T *l T']].
Canonical prodlexi_orderType
    (T : orderType disp1) (T' : orderType disp2) :=
  [orderType of T * T' for [orderType of T *l T']].
Canonical prodlexi_bMeetSemilatticeType (T : bOrderType disp1)
    (T' : bOrderType disp2) := [bMeetSemilatticeType of T * T'].
Canonical prodlexi_bJoinSemilatticeType (T : bOrderType disp1)
    (T' : bOrderType disp2) := [bJoinSemilatticeType of T * T'].
Canonical prodlexi_bLatticeType (T : bOrderType disp1)
    (T' : bOrderType disp2) := [bLatticeType of T * T'].
Canonical prodlexi_bDistrLatticeType (T : bOrderType disp1)
    (T' : bOrderType disp2) := [bDistrLatticeType of T * T'].
Canonical prodlexi_bOrderType (T : bOrderType disp1)
    (T' : bOrderType disp2) := [bOrderType of T * T'].
Canonical prodlexi_tMeetSemilatticeType (T : tOrderType disp1)
    (T' : tOrderType disp2) := [tMeetSemilatticeType of T * T'].
Canonical prodlexi_tJoinSemilatticeType (T : tOrderType disp1)
    (T' : tOrderType disp2) := [tJoinSemilatticeType of T * T'].
Canonical prodlexi_tLatticeType (T : tOrderType disp1)
    (T' : tOrderType disp2) := [tLatticeType of T * T'].
Canonical prodlexi_tDistrLatticeType (T : tOrderType disp1)
    (T' : tOrderType disp2) := [tDistrLatticeType of T * T'].
Canonical prodlexi_tOrderType (T : tOrderType disp1)
    (T' : tOrderType disp2) := [tOrderType of T * T'].
Canonical prodlexi_tbMeetSemilatticeType (T : tbOrderType disp1)
    (T' : tbOrderType disp2) := [tbMeetSemilatticeType of T * T'].
Canonical prodlexi_tbJoinSemilatticeType (T : tbOrderType disp1)
    (T' : tbOrderType disp2) := [tbJoinSemilatticeType of T * T'].
Canonical prodlexi_tbLatticeType (T : tbOrderType disp1)
    (T' : tbOrderType disp2) := [tbLatticeType of T * T'].
Canonical prodlexi_tbDistrLatticeType (T : tbOrderType disp1)
    (T' : tbOrderType disp2) := [tbDistrLatticeType of T * T'].
Canonical prodlexi_tbOrderType (T : tbOrderType disp1)
    (T' : tbOrderType disp2) := [tbOrderType of T * T'].
Canonical prodlexi_finPOrderType (T : finPOrderType disp1)
    (T' : finPOrderType disp2) := [finPOrderType of T * T'].
Canonical prodlexi_finBPOrderType (T : finBPOrderType disp1)
    (T' : finBPOrderType disp2) := [finBPOrderType of T * T'].
Canonical prodlexi_finTPOrderType (T : finTPOrderType disp1)
    (T' : finTPOrderType disp2) := [finTPOrderType of T * T'].
Canonical prodlexi_finTBPOrderType (T : finTBPOrderType disp1)
    (T' : finTBPOrderType disp2) := [finTBPOrderType of T * T'].
Canonical prodlexi_finLatticeType (T : finOrderType disp1)
    (T' : finOrderType disp2) := [finLatticeType of T * T'].
Canonical prodlexi_finDistrLatticeType (T : finOrderType disp1)
    (T' : finOrderType disp2) := [finDistrLatticeType of T * T'].
Canonical prodlexi_finOrderType (T : finOrderType disp1)
    (T' : finOrderType disp2) := [finOrderType of T * T'].
Canonical prodlexi_finTBLatticeType (T : finTBOrderType disp1)
    (T' : finTBOrderType disp2) := [finTBLatticeType of T * T'].
Canonical prodlexi_finTBDistrLatticeType (T : finTBOrderType disp1)
    (T' : finTBOrderType disp2) := [finTBDistrLatticeType of T * T'].
Canonical prodlexi_finTBOrderType (T : finTBOrderType disp1)
    (T' : finTBOrderType disp2) := [finTBOrderType of T * T'].

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

Canonical eqType (T : eqType) := Eval hnf in [eqType of seq T].
Canonical choiceType (T : choiceType) := Eval hnf in [choiceType of seq T].
Canonical countType (T : countType) := Eval hnf in [countType of seq T].

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

Definition porderMixin := LePOrderMixin (rrefl _) refl anti trans.
Canonical porderType := POrderType disp' (seq T) porderMixin.

Lemma leEseq s1 s2 : s1 <= s2 = if s1 isn't x1 :: s1' then true else
                                if s2 isn't x2 :: s2' then false else
                                (x1 <= x2) && (s1' <= s2' :> seq _).
Proof. by case: s1. Qed.

Lemma le0s s : [::] <= s :> seq _. Proof. by []. Qed.

Lemma les0 s : s <= [::] = (s == [::]). Proof. by rewrite leEseq. Qed.

Lemma le_cons x1 s1 x2 s2 :
   x1 :: s1 <= x2 :: s2 :> seq _ = (x1 <= x2) && (s1 <= s2).
Proof. by []. Qed.

Canonical bPOrderType := BPOrderType (seq T) (BottomMixin le0s).

Lemma botEseq : 0 = [::] :> seq T.
Proof. by []. Qed.

End POrder.

Section MeetSemilattice.
Variable T : meetSemilatticeType disp.
Implicit Types s : seq T.

Fixpoint meet s1 s2 :=
  match s1, s2 with
    | x1 :: s1', x2 :: s2' => (x1 `&` x2) :: meet s1' s2'
    | _, _ => [::]
  end.

Fact meetC : commutative meet.
Proof. by elim=> [|? ? ih] [|? ?] //=; rewrite meetC ih. Qed.

Fact meetA : associative meet.
Proof. by elim=> [|? ? ih] [|? ?] [|? ?] //=; rewrite meetA ih. Qed.

Fact leEmeet x y : (x <= y) = (meet x y == x).
Proof. by elim: x y => [|? ? ih] [|? ?] //=; rewrite leEseq leEmeet ih. Qed.

Definition meetMixin := MeetMixin meetC meetA leEmeet.
Canonical meetSemilatticeType := MeetSemilatticeType (seq T) meetMixin.
Canonical bMeetSemilatticeType := [bMeetSemilatticeType of seq T].

Lemma meetEseq s1 s2 : s1 `&` s2 =  [seq x.1 `&` x.2 | x <- zip s1 s2].
Proof. by elim: s1 s2 => [|x s1 ihs1] [|y s2]//=; rewrite -ihs1. Qed.

Lemma meet_cons x1 s1 x2 s2 :
  (x1 :: s1 : seq T) `&` (x2 :: s2) = (x1 `&` x2) :: s1 `&` s2.
Proof. by []. Qed.

End MeetSemilattice.

Section JoinSemilattice.
Variable T : joinSemilatticeType disp.
Implicit Types s : seq T.

Fixpoint join s1 s2 :=
  match s1, s2 with
    | [::], _ => s2 | _, [::] => s1
    | x1 :: s1', x2 :: s2' => (x1 `|` x2) :: join s1' s2'
  end.

Fact joinC : commutative join.
Proof. by elim=> [|? ? ih] [|? ?] //=; rewrite joinC ih. Qed.

Fact joinA : associative join.
Proof. by elim=> [|? ? ih] [|? ?] [|? ?] //=; rewrite joinA ih. Qed.

Fact leEjoin x y : (y <= x) = (join x y == x).
Proof.
by elim: x y => [|? ? ih] [|? ?]; rewrite ?eqxx // leEseq -eq_joinl ih.
Qed.

Definition joinMixin := JoinMixin joinC joinA leEjoin.
Canonical joinSemilatticeType := JoinSemilatticeType (seq T) joinMixin.
Canonical bJoinSemilatticeType := [bJoinSemilatticeType of seq T].

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

Section Lattice.
Variable T : latticeType disp.

Canonical latticeType := [latticeType of seq T].
Canonical bLatticeType := [bLatticeType of seq T].

End Lattice.

Section DistrLattice.
Variable T : distrLatticeType disp.

Fact meetUl : left_distributive (@meet T) (@join T).
Proof. by elim=> [|? ? ih] [|? ?] [|? ?] //=; rewrite meetUl ih. Qed.

Definition distrLatticeMixin := DistrLatticeMixin meetUl.
Canonical distrLatticeType := DistrLatticeType (seq T) distrLatticeMixin.
Canonical bDistrLatticeType := [bDistrLatticeType of seq T].

End DistrLattice.

End SeqProdOrder.

Module Exports.

Notation seqprod_with := type.
Notation seqprod := (type prod_display).

Canonical eqType.
Canonical choiceType.
Canonical countType.
Canonical porderType.
Canonical bPOrderType.
Canonical meetSemilatticeType.
Canonical bMeetSemilatticeType.
Canonical joinSemilatticeType.
Canonical bJoinSemilatticeType.
Canonical latticeType.
Canonical bLatticeType.
Canonical distrLatticeType.
Canonical bDistrLatticeType.

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
Import SeqProdOrder.Exports.

Module DefaultSeqProdOrder.
Section DefaultSeqProdOrder.
Context {disp : unit}.

Canonical seqprod_porderType (T : porderType disp) :=
  [porderType of seq T for [porderType of seqprod T]].
Canonical seqprod_bPOrderType (T : porderType disp) :=
  [bPOrderType of seq T for [bPOrderType of seqprod T]].
Canonical seqprod_meetSemilatticeType (T : meetSemilatticeType disp) :=
  [meetSemilatticeType of seq T for [meetSemilatticeType of seqprod T]].
Canonical seqprod_bMeetSemilatticeType (T : meetSemilatticeType disp) :=
  [bMeetSemilatticeType of seq T].
Canonical seqprod_joinSemilatticeType (T : joinSemilatticeType disp) :=
  [joinSemilatticeType of seq T for [joinSemilatticeType of seqprod T]].
Canonical seqprod_bJoinSemilatticeType (T : joinSemilatticeType disp) :=
  [bJoinSemilatticeType of seq T].
Canonical seqprod_latticeType (T : latticeType disp) :=
  [latticeType of seq T].
Canonical seqprod_bLatticeType (T : latticeType disp) :=
  [bLatticeType of seq T].
Canonical seqprod_distrLatticeType (T : distrLatticeType disp) :=
  [distrLatticeType of seq T for [distrLatticeType of seqprod T]].
Canonical seqprod_bDistrLatticeType (T : distrLatticeType disp) :=
  [bDistrLatticeType of seq T].

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

Canonical eqType (T : eqType) := Eval hnf in [eqType of seq T].
Canonical choiceType (T : choiceType) := Eval hnf in [choiceType of seq T].
Canonical countType (T : countType) := Eval hnf in [countType of seq T].

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

Definition porderMixin := LePOrderMixin lt_def refl anti trans.
Canonical porderType := POrderType disp' (seq T) porderMixin.

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

Canonical bPOrderType := BPOrderType (seq T) (BottomMixin lexi0s).

Lemma botEseqlexi : 0 = [::] :> seq T.
Proof. by []. Qed.

End POrder.

Section Total.
Variable T : orderType disp.
Implicit Types s : seq T.

Fact total : totalPOrderMixin (seq T).
Proof.
by elim=> [|x1 s1 ihs2] [|x2 s2] //=; rewrite !lexi_cons; case: ltgtP => /=.
Qed.

Canonical meetSemilatticeType := MeetSemilatticeType (seq T) total.
Canonical bMeetSemilatticeType := [bMeetSemilatticeType of seq T].
Canonical joinSemilatticeType := JoinSemilatticeType (seq T) total.
Canonical bJoinSemilatticeType := [bJoinSemilatticeType of seq T].
Canonical latticeType := [latticeType of seq T].
Canonical bLatticeType := [bLatticeType of seq T].
Canonical distrLatticeType := DistrLatticeType (seq T) total.
Canonical bDistrLatticeType := [bDistrLatticeType of seq T].
Canonical orderType := OrderType (seq T) total.
Canonical bOrderType := [bOrderType of seq T].

End Total.

Lemma sub_seqprod_lexi d (T : POrder.Exports.porderType disp) :
   subrel (<=%O : rel (seqprod_with d T)) (<=%O : rel (seq T)).
Proof.
elim=> [|x1 s1 ihs1] [|x2 s2]//=; rewrite le_cons lexi_cons /=.
by case/andP=> -> /ihs1 ->; rewrite implybT.
Qed.

End SeqLexiOrder.

Module Exports.

Notation seqlexi_with := type.
Notation seqlexi := (type lexi_display).

Canonical eqType.
Canonical choiceType.
Canonical countType.
Canonical porderType.
Canonical bPOrderType.
Canonical meetSemilatticeType.
Canonical bMeetSemilatticeType.
Canonical joinSemilatticeType.
Canonical bJoinSemilatticeType.
Canonical latticeType.
Canonical bLatticeType.
Canonical distrLatticeType.
Canonical bDistrLatticeType.
Canonical orderType.
Canonical bOrderType.

Definition leEseqlexi := @leEseqlexi.
Definition lexi0s := @lexi0s.
Definition lexis0 := @lexis0.
Definition lexi_cons := @lexi_cons.
Definition lexi_lehead := @lexi_lehead.
Definition eqhead_lexiE := @eqhead_lexiE.
Definition neqhead_lexiE := @neqhead_lexiE.

Definition ltEseqlexi := @ltEseqlexi.
Definition ltxi0s := @ltxi0s.
Definition ltxis0 := @ltxis0.
Definition ltxi_cons := @ltxi_cons.
Definition ltxi_lehead := @ltxi_lehead.
Definition eqhead_ltxiE := @eqhead_ltxiE.
Definition neqhead_ltxiE := @neqhead_ltxiE.

Definition botEseqlexi := @botEseqlexi.
Definition sub_seqprod_lexi := @sub_seqprod_lexi.

End Exports.
End SeqLexiOrder.
Import SeqLexiOrder.Exports.

Module DefaultSeqLexiOrder.
Section DefaultSeqLexiOrder.
Context {disp : unit}.

Canonical seqlexi_porderType (T : porderType disp) :=
  [porderType of seq T for [porderType of seqlexi T]].
Canonical seqlexi_bPOrderType (T : porderType disp) :=
  [bPOrderType of seq T for [bPOrderType of seqlexi T]].
Canonical seqlexi_meetSemilatticeType (T : orderType disp) :=
  [meetSemilatticeType of seq T for [meetSemilatticeType of seqlexi T]].
Canonical seqlexi_bMeetSemilatticeType (T : orderType disp) :=
  [bMeetSemilatticeType of seq T].
Canonical seqlexi_joinSemilatticeType (T : orderType disp) :=
  [joinSemilatticeType of seq T for [joinSemilatticeType of seqlexi T]].
Canonical seqlexi_bJoinSemilatticeType (T : orderType disp) :=
  [bJoinSemilatticeType of seq T].
Canonical seqlexi_latticeType (T : orderType disp) := [latticeType of seq T].
Canonical seqlexi_bLatticeType (T : orderType disp) := [bLatticeType of seq T].
Canonical seqlexi_distrLatticeType (T : orderType disp) :=
  [distrLatticeType of seq T for [distrLatticeType of seqlexi T]].
Canonical seqlexi_bDistrLatticeType (T : orderType disp) :=
  [bDistrLatticeType of seq T].
Canonical seqlexi_orderType (T : orderType disp) :=
  [orderType of seq T for [orderType of seqlexi T]].
Canonical seqlexi_bOrderType (T : orderType disp) := [bOrderType of seq T].

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

Canonical eqType (T : eqType) := Eval hnf in [eqType of n.-tuple T].
Canonical choiceType (T : choiceType) := Eval hnf in [choiceType of n.-tuple T].
Canonical countType (T : countType) := Eval hnf in [countType of n.-tuple T].
Canonical finType (T : finType) := Eval hnf in [finType of n.-tuple T].
End Basics.

Section POrder.
Implicit Types (T : porderType disp).

Definition porderMixin n T := [porderMixin of n.-tuple T by <:].
Canonical porderType n T := POrderType disp' (n.-tuple T) (porderMixin n T).

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

Section BPOrder.
Variables (n : nat) (T : bPOrderType disp).

Fact le0x t : [tuple of nseq n 0] <= t :> n.-tuple T.
Proof. by rewrite leEtprod; apply/forallP => i; rewrite tnth_nseq le0x. Qed.

Canonical bPOrderType := BPOrderType (n.-tuple T) (BottomMixin le0x).

Lemma botEtprod : 0 = [tuple of nseq n 0] :> n.-tuple T. Proof. by []. Qed.

End BPOrder.

Section TPOrder.
Variables (n : nat) (T : tPOrderType disp).

Fact lex1 t : t <= [tuple of nseq n 1] :> n.-tuple T.
Proof. by rewrite leEtprod; apply/forallP => i; rewrite tnth_nseq lex1. Qed.

Canonical tPOrderType := TPOrderType (n.-tuple T) (TopMixin lex1).

Lemma topEtprod : 1 = [tuple of nseq n 1] :> n.-tuple T. Proof. by []. Qed.

End TPOrder.

Canonical tbPOrderType (n : nat) (T : tbPOrderType disp) :=
  [tbPOrderType of n.-tuple T].

Section MeetSemilattice.
Variables (n : nat) (T : meetSemilatticeType disp).
Implicit Types (t : n.-tuple T).

Definition meet t1 t2 : n.-tuple T :=
  [tuple of [seq x.1 `&` x.2 | x <- zip t1 t2]].

Fact tnth_meet t1 t2 i : tnth (meet t1 t2) i = tnth t1 i `&` tnth t2 i.
Proof.
rewrite tnth_map -(tnth_map fst) -(tnth_map snd) -/unzip1 -/unzip2.
by rewrite !(tnth_nth (tnth_default t1 i))/= unzip1_zip ?unzip2_zip ?size_tuple.
Qed.

Fact meetC : commutative meet.
Proof. by move=> t1 t2; apply: eq_from_tnth => i; rewrite !tnth_meet meetC. Qed.

Fact meetA : associative meet.
Proof.
by move=> t1 t2 t3; apply: eq_from_tnth => i; rewrite !tnth_meet meetA.
Qed.

Fact leEmeet t1 t2 : (t1 <= t2) = (meet t1 t2 == t1).
Proof.
rewrite leEtprod eqEtuple; apply: eq_forallb => /= i.
by rewrite tnth_meet leEmeet.
Qed.

Definition meetMixin := MeetMixin meetC meetA leEmeet.
Canonical meetSemilatticeType := MeetSemilatticeType (n.-tuple T) meetMixin.

Lemma meetEtprod t1 t2 :
  t1 `&` t2 = [tuple of [seq x.1 `&` x.2 | x <- zip t1 t2]].
Proof. by []. Qed.

End MeetSemilattice.

Canonical bMeetSemilatticeType (n : nat) (T : bMeetSemilatticeType disp) :=
  [bMeetSemilatticeType of n.-tuple T].
Canonical tMeetSemilatticeType (n : nat) (T : tMeetSemilatticeType disp) :=
  [tMeetSemilatticeType of n.-tuple T].
Canonical tbMeetSemilatticeType (n : nat) (T : tbMeetSemilatticeType disp) :=
  [tbMeetSemilatticeType of n.-tuple T].

Section JoinSemilattice.
Variables (n : nat) (T : joinSemilatticeType disp).
Implicit Types (t : n.-tuple T).

Definition join t1 t2 : n.-tuple T :=
  [tuple of [seq x.1 `|` x.2 | x <- zip t1 t2]].

Fact tnth_join t1 t2 i : tnth (join t1 t2) i = tnth t1 i `|` tnth t2 i.
Proof.
rewrite tnth_map -(tnth_map fst) -(tnth_map snd) -/unzip1 -/unzip2.
by rewrite !(tnth_nth (tnth_default t1 i))/= unzip1_zip ?unzip2_zip ?size_tuple.
Qed.

Fact joinC : commutative join.
Proof. by move=> t1 t2; apply: eq_from_tnth => i; rewrite !tnth_join joinC. Qed.

Fact joinA : associative join.
Proof.
by move=> t1 t2 t3; apply: eq_from_tnth => i; rewrite !tnth_join joinA.
Qed.

Fact leEjoin t1 t2 : (t2 <= t1) = (join t1 t2 == t1).
Proof.
rewrite leEtprod eqEtuple; apply: eq_forallb => /= i.
by rewrite tnth_join eq_joinl.
Qed.

Definition joinMixin := JoinMixin joinC joinA leEjoin.
Canonical joinSemilatticeType := JoinSemilatticeType (n.-tuple T) joinMixin.

Lemma joinEtprod t1 t2 :
  t1 `|` t2 = [tuple of [seq x.1 `|` x.2 | x <- zip t1 t2]].
Proof. by []. Qed.

End JoinSemilattice.

Canonical bJoinSemilatticeType (n : nat) (T : bJoinSemilatticeType disp) :=
  [bJoinSemilatticeType of n.-tuple T].
Canonical tJoinSemilatticeType (n : nat) (T : tJoinSemilatticeType disp) :=
  [tJoinSemilatticeType of n.-tuple T].
Canonical tbJoinSemilatticeType (n : nat) (T : tbJoinSemilatticeType disp) :=
  [tbJoinSemilatticeType of n.-tuple T].
Canonical latticeType (n : nat) (T : latticeType disp) :=
  [latticeType of n.-tuple T].
Canonical bLatticeType (n : nat) (T : bLatticeType disp) :=
  [bLatticeType of n.-tuple T].
Canonical tLatticeType (n : nat) (T : tLatticeType disp) :=
  [tLatticeType of n.-tuple T].
Canonical tbLatticeType (n : nat) (T : tbLatticeType disp) :=
  [tbLatticeType of n.-tuple T].

Section DistrLattice.
Variables (n : nat) (T : distrLatticeType disp).

Fact meetUl : left_distributive (@meet n T) (@join n T).
Proof.
move=> t1 t2 t3; apply: eq_from_tnth => i.
by rewrite !(tnth_meet, tnth_join) meetUl.
Qed.

Definition distrLatticeMixin := DistrLatticeMixin meetUl.
Canonical distrLatticeType := DistrLatticeType (n.-tuple T) distrLatticeMixin.

End DistrLattice.

Canonical bDistrLatticeType (n : nat) (T : bDistrLatticeType disp) :=
  [bDistrLatticeType of n.-tuple T].
Canonical tDistrLatticeType (n : nat) (T : tDistrLatticeType disp) :=
  [tDistrLatticeType of n.-tuple T].
Canonical tbDistrLatticeType (n : nat) (T : tbDistrLatticeType disp) :=
  [tbDistrLatticeType of n.-tuple T].

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

Definition cbDistrLatticeMixin := CBDistrLatticeMixin subKI joinIB.
Canonical cbDistrLatticeType :=
  CBDistrLatticeType (n.-tuple T) cbDistrLatticeMixin.

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

Definition ctbDistrLatticeMixin := CTBDistrLatticeMixin complE.
Canonical ctbDistrLatticeType :=
  CTBDistrLatticeType (n.-tuple T) ctbDistrLatticeMixin.

Lemma complEtprod t : ~` t = [tuple of [seq ~` x | x <- t]].
Proof. by []. Qed.

End CTBDistrLattice.

Canonical finPOrderType n (T : finPOrderType disp) :=
  [finPOrderType of n.-tuple T].

Canonical finBPOrderType n (T : finBPOrderType disp) :=
  [finBPOrderType of n.-tuple T].

Canonical finTPOrderType n (T : finTPOrderType disp) :=
  [finTPOrderType of n.-tuple T].

Canonical finTBPOrderType n (T : finTBPOrderType disp) :=
  [finTBPOrderType of n.-tuple T].

Canonical finMeetSemilatticeType n (T : finMeetSemilatticeType disp) :=
  [finMeetSemilatticeType of n.-tuple T].

Canonical finBMeetSemilatticeType n (T : finBMeetSemilatticeType disp) :=
  [finBMeetSemilatticeType of n.-tuple T].

Canonical finJoinSemilatticeType n (T : finJoinSemilatticeType disp) :=
  [finJoinSemilatticeType of n.-tuple T].

Canonical finTJoinSemilatticeType n (T : finTJoinSemilatticeType disp) :=
  [finTJoinSemilatticeType of n.-tuple T].

Canonical finLatticeType n (T : finLatticeType disp) :=
  [finLatticeType of n.-tuple T].

Canonical finTBLatticeType n (T : finTBLatticeType disp) :=
  [finTBLatticeType of n.-tuple T].

Canonical finDistrLatticeType n (T : finDistrLatticeType disp) :=
  [finDistrLatticeType of n.-tuple T].

Canonical finTBDistrLatticeType n (T : finTBDistrLatticeType disp) :=
  [finTBDistrLatticeType of n.-tuple T].

Canonical finCTBDistrLatticeType n (T : finCTBDistrLatticeType disp) :=
  [finCTBDistrLatticeType of n.-tuple T].

End TupleProdOrder.

Module Exports.

Notation "n .-tupleprod[ disp ]" := (type disp n)
  (at level 2, disp at next level, format "n .-tupleprod[ disp ]") :
  type_scope.
Notation "n .-tupleprod" := (n.-tupleprod[prod_display])
  (at level 2, format "n .-tupleprod") : type_scope.

Canonical eqType.
Canonical choiceType.
Canonical countType.
Canonical finType.
Canonical porderType.
Canonical bPOrderType.
Canonical tPOrderType.
Canonical tbPOrderType.
Canonical meetSemilatticeType.
Canonical bMeetSemilatticeType.
Canonical tMeetSemilatticeType.
Canonical tbMeetSemilatticeType.
Canonical joinSemilatticeType.
Canonical bJoinSemilatticeType.
Canonical tJoinSemilatticeType.
Canonical tbJoinSemilatticeType.
Canonical latticeType.
Canonical bLatticeType.
Canonical tLatticeType.
Canonical tbLatticeType.
Canonical distrLatticeType.
Canonical bDistrLatticeType.
Canonical tDistrLatticeType.
Canonical tbDistrLatticeType.
Canonical cbDistrLatticeType.
Canonical ctbDistrLatticeType.
Canonical finPOrderType.
Canonical finBPOrderType.
Canonical finTPOrderType.
Canonical finTBPOrderType.
Canonical finMeetSemilatticeType.
Canonical finBMeetSemilatticeType.
Canonical finJoinSemilatticeType.
Canonical finTJoinSemilatticeType.
Canonical finLatticeType.
Canonical finTBLatticeType.
Canonical finDistrLatticeType.
Canonical finTBDistrLatticeType.
Canonical finCTBDistrLatticeType.

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
Import TupleProdOrder.Exports.

Module DefaultTupleProdOrder.
Section DefaultTupleProdOrder.
Context {disp : unit}.

Canonical tprod_porderType n (T : porderType disp) :=
  [porderType of n.-tuple T for [porderType of n.-tupleprod T]].
Canonical tprod_bPOrderType n (T : bPOrderType disp) :=
  [bPOrderType of n.-tuple T for [bPOrderType of n.-tupleprod T]].
Canonical tprod_tPOrderType n (T : tPOrderType disp) :=
  [tPOrderType of n.-tuple T for [tPOrderType of n.-tupleprod T]].
Canonical tprod_tbPOrderType n (T : tbPOrderType disp) :=
  [tbPOrderType of n.-tuple T].
Canonical tprod_meetSemilatticeType n (T : meetSemilatticeType disp) :=
  [meetSemilatticeType of n.-tuple T
                       for [meetSemilatticeType of n.-tupleprod T]].
Canonical tprod_bMeetSemilatticeType n (T : bMeetSemilatticeType disp) :=
  [bMeetSemilatticeType of n.-tuple T].
Canonical tprod_tMeetSemilatticeType n (T : tMeetSemilatticeType disp) :=
  [tMeetSemilatticeType of n.-tuple T].
Canonical tprod_tbMeetSemilatticeType n (T : tbMeetSemilatticeType disp) :=
  [tbMeetSemilatticeType of n.-tuple T].
Canonical tprod_joinSemilatticeType n (T : joinSemilatticeType disp) :=
  [joinSemilatticeType of n.-tuple T
                       for [joinSemilatticeType of n.-tupleprod T]].
Canonical tprod_bJoinSemilatticeType n (T : bJoinSemilatticeType disp) :=
  [bJoinSemilatticeType of n.-tuple T].
Canonical tprod_tJoinSemilatticeType n (T : tJoinSemilatticeType disp) :=
  [tJoinSemilatticeType of n.-tuple T].
Canonical tprod_tbJoinSemilatticeType n (T : tbJoinSemilatticeType disp) :=
  [tbJoinSemilatticeType of n.-tuple T].
Canonical tprod_latticeType n (T : latticeType disp) :=
  [latticeType of n.-tuple T].
Canonical tprod_bLatticeType n (T : bLatticeType disp) :=
  [bLatticeType of n.-tuple T].
Canonical tprod_tLatticeType n (T : tLatticeType disp) :=
  [tLatticeType of n.-tuple T].
Canonical tprod_tbLatticeType n (T : tbLatticeType disp) :=
  [tbLatticeType of n.-tuple T].
Canonical tprod_distrLatticeType n (T : distrLatticeType disp) :=
  [distrLatticeType of n.-tuple T for [distrLatticeType of n.-tupleprod T]].
Canonical tprod_bDistrLatticeType n (T : bDistrLatticeType disp) :=
  [bDistrLatticeType of n.-tuple T].
Canonical tprod_tDistrLatticeType n (T : tDistrLatticeType disp) :=
  [tDistrLatticeType of n.-tuple T].
Canonical tprod_tbDistrLatticeType n (T : tbDistrLatticeType disp) :=
  [tbDistrLatticeType of n.-tuple T].
Canonical tprod_cbDistrLatticeType n (T : cbDistrLatticeType disp) :=
  [cbDistrLatticeType of n.-tuple T for [cbDistrLatticeType of n.-tupleprod T]].
Canonical tprod_ctbDistrLatticeType n (T : ctbDistrLatticeType disp) :=
  [ctbDistrLatticeType of n.-tuple T for
                       [ctbDistrLatticeType of n.-tupleprod T]].
Canonical tprod_finPOrderType n (T : finPOrderType disp) :=
  [finPOrderType of n.-tuple T].
Canonical tprod_finBPOrderType n (T : finBPOrderType disp) :=
  [finBPOrderType of n.-tuple T].
Canonical tprod_finTPOrderType n (T : finTPOrderType disp) :=
  [finTPOrderType of n.-tuple T].
Canonical tprod_finTBPOrderType n (T : finTBPOrderType disp) :=
  [finTBPOrderType of n.-tuple T].
Canonical tprod_finMeetSemilatticeType n (T : finMeetSemilatticeType disp) :=
  [finMeetSemilatticeType of n.-tuple T].
Canonical tprod_finBMeetSemilatticeType n (T : finBMeetSemilatticeType disp) :=
  [finBMeetSemilatticeType of n.-tuple T].
Canonical tprod_finJoinSemilatticeType n (T : finJoinSemilatticeType disp) :=
  [finJoinSemilatticeType of n.-tuple T].
Canonical tprod_finTJoinSemilatticeType n (T : finTJoinSemilatticeType disp) :=
  [finTJoinSemilatticeType of n.-tuple T].
Canonical tprod_finLatticeType n (T : finLatticeType disp) :=
  [finLatticeType of n.-tuple T].
Canonical tprod_finTBLatticeType n (T : finTBLatticeType disp) :=
  [finTBLatticeType of n.-tuple T].
Canonical tprod_finDistrLatticeType n (T : finDistrLatticeType disp) :=
  [finDistrLatticeType of n.-tuple T].
Canonical tprod_finTBDistrLatticeType n (T : finTBDistrLatticeType disp) :=
  [finTBDistrLatticeType of n.-tuple T].
Canonical tprod_finCTBDistrLatticeType n (T : finCTBDistrLatticeType disp) :=
  [finCTBDistrLatticeType of n.-tuple T].

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

Canonical eqType (T : eqType) := Eval hnf in [eqType of n.-tuple T].
Canonical choiceType (T : choiceType) := Eval hnf in [choiceType of n.-tuple T].
Canonical countType (T : countType) := Eval hnf in [countType of n.-tuple T].
Canonical finType (T : finType) := Eval hnf in [finType of n.-tuple T].
End Basics.

Section POrder.
Implicit Types (T : porderType disp).

Definition porderMixin n T := [porderMixin of n.-tuple T by <:].
Canonical porderType n T := POrderType disp' (n.-tuple T) (porderMixin n T).

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

Section BPOrder.
Variables (n : nat) (T : bPOrderType disp).

Fact le0x t : [tuple of nseq n 0] <= t :> n.-tuple T.
Proof. by apply: sub_seqprod_lexi; apply: le0x (t : n.-tupleprod T). Qed.

Canonical bPOrderType := BPOrderType (n.-tuple T) (BottomMixin le0x).

Lemma botEtlexi : 0 = [tuple of nseq n 0] :> n.-tuple T. Proof. by []. Qed.

End BPOrder.

Section TPOrder.
Variables (n : nat) (T : tPOrderType disp).

Fact lex1 t : t <= [tuple of nseq n 1] :> n.-tuple T.
Proof. by apply: sub_seqprod_lexi; apply: lex1 (t : n.-tupleprod T). Qed.

Canonical tPOrderType := TPOrderType (n.-tuple T) (TopMixin lex1).

Lemma topEtlexi : 1 = [tuple of nseq n 1] :> n.-tuple T. Proof. by []. Qed.

End TPOrder.

Canonical tbPOrderType n (T : tbPOrderType disp) :=
  [tbPOrderType of n.-tuple T].

Section Total.
Variables (n : nat) (T : orderType disp).

Definition total : totalPOrderMixin (n.-tuple T) :=
  [totalOrderMixin of n.-tuple T by <:].
Canonical meetSemilatticeType := MeetSemilatticeType (n.-tuple T) total.
Canonical joinSemilatticeType := JoinSemilatticeType (n.-tuple T) total.
Canonical latticeType := [latticeType of n.-tuple T].
Canonical distrLatticeType := DistrLatticeType (n.-tuple T) total.
Canonical orderType := OrderType (n.-tuple T) total.

End Total.

Section BTotal.
Variable (n : nat) (T : bOrderType disp).

Canonical bMeetSemilatticeType := [bMeetSemilatticeType of n.-tuple T].
Canonical bJoinSemilatticeType := [bJoinSemilatticeType of n.-tuple T].
Canonical bLatticeType := [bLatticeType of n.-tuple T].
Canonical bDistrLatticeType := [bDistrLatticeType of n.-tuple T].
Canonical bOrderType := [bOrderType of n.-tuple T].

End BTotal.

Section TTotal.
Variable (n : nat) (T : tOrderType disp).

Canonical tMeetSemilatticeType := [tMeetSemilatticeType of n.-tuple T].
Canonical tJoinSemilatticeType := [tJoinSemilatticeType of n.-tuple T].
Canonical tLatticeType := [tLatticeType of n.-tuple T].
Canonical tDistrLatticeType := [tDistrLatticeType of n.-tuple T].
Canonical tOrderType := [tOrderType of n.-tuple T].

End TTotal.

Section TBTotal.
Variable (n : nat) (T : tbOrderType disp).

Canonical tbMeetSemilatticeType := [tbMeetSemilatticeType of n.-tuple T].
Canonical tbJoinSemilatticeType := [tbJoinSemilatticeType of n.-tuple T].
Canonical tbLatticeType := [tbLatticeType of n.-tuple T].
Canonical tbDistrLatticeType := [tbDistrLatticeType of n.-tuple T].
Canonical tbOrderType := [tbOrderType of n.-tuple T].

End TBTotal.

Canonical finPOrderType (n : nat) (T : finPOrderType disp) :=
  [finPOrderType of n.-tuple T].
Canonical finBPOrderType (n : nat) (T : finBPOrderType disp) :=
  [finBPOrderType of n.-tuple T].
Canonical finTPOrderType (n : nat) (T : finTPOrderType disp) :=
  [finTPOrderType of n.-tuple T].
Canonical finTBPOrderType (n : nat) (T : finTBPOrderType disp) :=
  [finTBPOrderType of n.-tuple T].

Section FinTotal.
Variable (n : nat) (T : finOrderType disp).

Canonical finLatticeType := [finLatticeType of n.-tuple T].
Canonical finDistrLatticeType := [finDistrLatticeType of n.-tuple T].
Canonical finOrderType := [finOrderType of n.-tuple T].

End FinTotal.

Section FinTBTotal.
Variable (n : nat) (T : finTBOrderType disp).

Canonical finTBLatticeType := [finTBLatticeType of n.-tuple T].
Canonical finTBDistrLatticeType := [finTBDistrLatticeType of n.-tuple T].
Canonical finTBOrderType := [finTBOrderType of n.-tuple T].

End FinTBTotal.

Lemma sub_tprod_lexi d n (T : POrder.Exports.porderType disp) :
   subrel (<=%O : rel (n.-tupleprod[d] T)) (<=%O : rel (n.-tuple T)).
Proof. exact: sub_seqprod_lexi. Qed.

End TupleLexiOrder.

Module Exports.

Notation "n .-tuplelexi[ disp ]" := (type disp n)
  (at level 2, disp at next level, format "n .-tuplelexi[ disp ]") :
  type_scope.
Notation "n .-tuplelexi" := (n.-tuplelexi[lexi_display])
  (at level 2, format "n .-tuplelexi") : type_scope.

Canonical eqType.
Canonical choiceType.
Canonical countType.
Canonical finType.
Canonical porderType.
Canonical bPOrderType.
Canonical tPOrderType.
Canonical tbPOrderType.
Canonical meetSemilatticeType.
Canonical joinSemilatticeType.
Canonical latticeType.
Canonical distrLatticeType.
Canonical orderType.
Canonical bMeetSemilatticeType.
Canonical bJoinSemilatticeType.
Canonical bLatticeType.
Canonical bDistrLatticeType.
Canonical bOrderType.
Canonical tMeetSemilatticeType.
Canonical tJoinSemilatticeType.
Canonical tLatticeType.
Canonical tDistrLatticeType.
Canonical tOrderType.
Canonical tbMeetSemilatticeType.
Canonical tbJoinSemilatticeType.
Canonical tbLatticeType.
Canonical tbDistrLatticeType.
Canonical tbOrderType.
Canonical finPOrderType.
Canonical finBPOrderType.
Canonical finTPOrderType.
Canonical finTBPOrderType.
Canonical finLatticeType.
Canonical finDistrLatticeType.
Canonical finOrderType.
Canonical finTBLatticeType.
Canonical finTBDistrLatticeType.
Canonical finTBOrderType.

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
Import TupleLexiOrder.Exports.

Module DefaultTupleLexiOrder.
Section DefaultTupleLexiOrder.
Context {disp : unit}.

Canonical tlexi_porderType n (T : porderType disp) :=
  [porderType of n.-tuple T for [porderType of n.-tuplelexi T]].
Canonical tlexi_bPOrderType n (T : bPOrderType disp) :=
  [bPOrderType of n.-tuple T for [bPOrderType of n.-tuplelexi T]].
Canonical tlexi_tPOrderType n (T : tPOrderType disp) :=
  [tPOrderType of n.-tuple T for [tPOrderType of n.-tuplelexi T]].
Canonical tlexi_tbPOrderType n (T : tbPOrderType disp) :=
  [tbPOrderType of n.-tuple T].
Canonical tlexi_meetSemilatticeType n (T : orderType disp) :=
  [meetSemilatticeType of n.-tuple T
                       for [meetSemilatticeType of n.-tuplelexi T]].
Canonical tlexi_joinSemilatticeType n (T : orderType disp) :=
  [joinSemilatticeType of n.-tuple T
                       for [joinSemilatticeType of n.-tuplelexi T]].
Canonical tlexi_latticeType n (T : orderType disp) :=
  [latticeType of n.-tuple T].
Canonical tlexi_distrLatticeType n (T : orderType disp) :=
  [distrLatticeType of n.-tuple T for [distrLatticeType of n.-tuplelexi T]].
Canonical tlexi_orderType n (T : orderType disp) :=
  [orderType of n.-tuple T for [orderType of n.-tuplelexi T]].
Canonical tlexi_bMeetSemilatticeType n (T : bOrderType disp) :=
  [bMeetSemilatticeType of n.-tuple T].
Canonical tlexi_bJoinSemilatticeType n (T : bOrderType disp) :=
  [bJoinSemilatticeType of n.-tuple T].
Canonical tlexi_bLatticeType n (T : bOrderType disp) :=
  [bLatticeType of n.-tuple T].
Canonical tlexi_bDistrLatticeType n (T : bOrderType disp) :=
  [bDistrLatticeType of n.-tuple T].
Canonical tlexi_bOrderType n (T : bOrderType disp) :=
  [bOrderType of n.-tuple T].
Canonical tlexi_tMeetSemilatticeType n (T : tOrderType disp) :=
  [tMeetSemilatticeType of n.-tuple T].
Canonical tlexi_tJoinSemilatticeType n (T : tOrderType disp) :=
  [tJoinSemilatticeType of n.-tuple T].
Canonical tlexi_tLatticeType n (T : tOrderType disp) :=
  [tLatticeType of n.-tuple T].
Canonical tlexi_tDistrLatticeType n (T : tOrderType disp) :=
  [tDistrLatticeType of n.-tuple T].
Canonical tlexi_tOrderType n (T : tOrderType disp) :=
  [tOrderType of n.-tuple T].
Canonical tlexi_tbMeetSemilatticeType n (T : tbOrderType disp) :=
  [tbMeetSemilatticeType of n.-tuple T].
Canonical tlexi_tbJoinSemilatticeType n (T : tbOrderType disp) :=
  [tbJoinSemilatticeType of n.-tuple T].
Canonical tlexi_tbLatticeType n (T : tbOrderType disp) :=
  [tbLatticeType of n.-tuple T].
Canonical tlexi_tbDistrLatticeType n (T : tbOrderType disp) :=
  [tbDistrLatticeType of n.-tuple T].
Canonical tlexi_tbOrderType n (T : tbOrderType disp) :=
  [tbOrderType of n.-tuple T].
Canonical tlexi_finPOrderType n (T : finPOrderType disp) :=
  [finPOrderType of n.-tuple T].
Canonical tlexi_finBPOrderType n (T : finBPOrderType disp) :=
  [finBPOrderType of n.-tuple T].
Canonical tlexi_finTPOrderType n (T : finTPOrderType disp) :=
  [finTPOrderType of n.-tuple T].
Canonical tlexi_finTBPOrderType n (T : finTBPOrderType disp) :=
  [finTBPOrderType of n.-tuple T].
Canonical tlexi_finLatticeType n (T : finOrderType disp) :=
  [finLatticeType of n.-tuple T].
Canonical tlexi_finDistrLatticeType n (T : finOrderType disp) :=
  [finDistrLatticeType of n.-tuple T].
Canonical tlexi_finOrderType n (T : finOrderType disp) :=
  [finOrderType of n.-tuple T].
Canonical tlexi_finTBLatticeType n (T : finTBOrderType disp) :=
  [finTBLatticeType of n.-tuple T].
Canonical tlexi_finTBDistrLatticeType n (T : finTBOrderType disp) :=
  [finTBDistrLatticeType of n.-tuple T].
Canonical tlexi_finTBOrderType n (T : finTBOrderType disp) :=
  [finTBOrderType of n.-tuple T].

End DefaultTupleLexiOrder.
End DefaultTupleLexiOrder.

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

Definition t_distrLatticeMixin :=
  DistrMeetJoinMixin le_def (fun _ _ => erefl _) (@setIC _) (@setUC _)
                (@setIA _) (@setUA _) setKUC setKIC (@setIUl _) (@setIid _).

Lemma subset_display : unit. Proof. exact: tt. Qed.

Canonical eqType := [eqType of {subset T}].
Canonical choiceType := [choiceType of {subset T}].
Canonical countType := [countType of {subset T}].
Canonical finType := [finType of {subset T}].
Canonical porderType :=
  POrderType subset_display {subset T} t_distrLatticeMixin.
Canonical bPOrderType := BPOrderType {subset T}
  (BottomMixin (@sub0set _ : forall A, (set0 <= A :> {subset T})%O)).
Canonical tPOrderType := TPOrderType {subset T}
  (TopMixin (@subsetT _ : forall A, (A <= setT :> {subset T})%O)).
Canonical tbPOrderType := [tbPOrderType of {subset T}].
Canonical meetSemilatticeType :=
  MeetSemilatticeType {subset T} t_distrLatticeMixin.
Canonical bMeetSemilatticeType := [bMeetSemilatticeType of {subset T}].
Canonical tMeetSemilatticeType := [tMeetSemilatticeType of {subset T}].
Canonical tbMeetSemilatticeType := [tbMeetSemilatticeType of {subset T}].
Canonical joinSemilatticeType :=
  JoinSemilatticeType {subset T} t_distrLatticeMixin.
Canonical bJoinSemilatticeType := [bJoinSemilatticeType of {subset T}].
Canonical tJoinSemilatticeType := [tJoinSemilatticeType of {subset T}].
Canonical tbJoinSemilatticeType := [tbJoinSemilatticeType of {subset T}].
Canonical latticeType := [latticeType of {subset T}].
Canonical bLatticeType := [bLatticeType of {subset T}].
Canonical tLatticeType := [tLatticeType of {subset T}].
Canonical tbLatticeType := [tbLatticeType of {subset T}].
Canonical distrLatticeType := DistrLatticeType {subset T} t_distrLatticeMixin.
Canonical bDistrLatticeType := [bDistrLatticeType of {subset T}].
Canonical tDistrLatticeType := [tDistrLatticeType of {subset T}].
Canonical tbDistrLatticeType := [tbDistrLatticeType of {subset T}].

Lemma setIDv A B : B :&: (A :\: B) = set0.
Proof.
apply/eqP; rewrite -subset0; apply/subsetP => x.
by rewrite !inE => /and3P[->].
Qed.

Definition t_cbdistrLatticeMixin := CBDistrLatticeMixin setIDv (@setID _).
Canonical cbDistrLatticeType :=
  CBDistrLatticeType {subset T} t_cbdistrLatticeMixin.

Lemma setTDsym A : ~: A = setT :\: A.
Proof. by rewrite setTD. Qed.

Definition t_ctbdistrLatticeMixin := CTBDistrLatticeMixin setTDsym.
Canonical ctbDistrLatticeType :=
  CTBDistrLatticeType {subset T} t_ctbdistrLatticeMixin.

Canonical finPOrderType := [finPOrderType of {subset T}].
Canonical finBPOrderType := [finPOrderType of {subset T}].
Canonical finTPOrderType := [finPOrderType of {subset T}].
Canonical finTBPOrderType := [finPOrderType of {subset T}].
Canonical finLatticeType := [finLatticeType of {subset T}].
Canonical finBLatticeType := [finLatticeType of {subset T}].
Canonical finTLatticeType := [finLatticeType of {subset T}].
Canonical finTBLatticeType := [finLatticeType of {subset T}].
Canonical finDistrLatticeType := [finDistrLatticeType of {subset T}].
Canonical finBDistrLatticeType := [finDistrLatticeType of {subset T}].
Canonical finTDistrLatticeType := [finDistrLatticeType of {subset T}].
Canonical finTBDistrLatticeType := [finDistrLatticeType of {subset T}].
Canonical finCTBDistrLatticeType := [finCTBDistrLatticeType of {subset T}].

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

End SetSubsetOrder.

Module Exports.
Notation "{ 'subset' [ d ] T }" := (type_of d (Phant T))
  (at level 2, d at next level, format "{ 'subset' [ d ]  T }") : type_scope.
Notation "{ 'subset' T }" := {subset[subset_display] T}
  (at level 2, format "{ 'subset' T }") : type_scope.

Canonical eqType.
Canonical choiceType.
Canonical countType.
Canonical finType.
Canonical porderType.
Canonical bPOrderType.
Canonical tPOrderType.
Canonical tbPOrderType.
Canonical meetSemilatticeType.
Canonical bMeetSemilatticeType.
Canonical tMeetSemilatticeType.
Canonical tbMeetSemilatticeType.
Canonical joinSemilatticeType.
Canonical bJoinSemilatticeType.
Canonical tJoinSemilatticeType.
Canonical tbJoinSemilatticeType.
Canonical latticeType.
Canonical bLatticeType.
Canonical tLatticeType.
Canonical tbLatticeType.
Canonical distrLatticeType.
Canonical bDistrLatticeType.
Canonical tDistrLatticeType.
Canonical tbDistrLatticeType.
Canonical cbDistrLatticeType.
Canonical ctbDistrLatticeType.
Canonical finPOrderType.
Canonical finBPOrderType.
Canonical finTPOrderType.
Canonical finTBPOrderType.
Canonical finLatticeType.
Canonical finBLatticeType.
Canonical finTLatticeType.
Canonical finTBLatticeType.
Canonical finDistrLatticeType.
Canonical finCTBDistrLatticeType.

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

Canonical subset_porderType (T : finType) :=
  [porderType of {set T} for [porderType of {subset T}]].
Canonical subset_bPOrderType (T : finType) :=
  [bPOrderType of {set T} for [bPOrderType of {subset T}]].
Canonical subset_tPOrderType (T : finType) :=
  [tPOrderType of {set T} for [tPOrderType of {subset T}]].
Canonical subset_tbPOrderType (T : finType) := [tbPOrderType of {set T}].
Canonical subset_meetSemilatticeType (T : finType) :=
  [meetSemilatticeType of {set T} for [meetSemilatticeType of {subset T}]].
Canonical subset_bMeetSemilatticeType (T : finType) :=
  [bMeetSemilatticeType of {set T}].
Canonical subset_tMeetSemilatticeType (T : finType) :=
  [tMeetSemilatticeType of {set T}].
Canonical subset_tbMeetSemilatticeType (T : finType) :=
  [tbMeetSemilatticeType of {set T}].
Canonical subset_joinSemilatticeType (T : finType) :=
  [joinSemilatticeType of {set T} for [joinSemilatticeType of {subset T}]].
Canonical subset_bJoinSemilatticeType (T : finType) :=
  [bJoinSemilatticeType of {set T}].
Canonical subset_tJoinSemilatticeType (T : finType) :=
  [tJoinSemilatticeType of {set T}].
Canonical subset_tbJoinSemilatticeType (T : finType) :=
  [tbJoinSemilatticeType of {set T}].
Canonical subset_latticeType (T : finType) := [latticeType of {set T}].
Canonical subset_bLatticeType (T : finType) := [bLatticeType of {set T}].
Canonical subset_tLatticeType (T : finType) := [tLatticeType of {set T}].
Canonical subset_tbLatticeType (T : finType) := [tbLatticeType of {set T}].
Canonical subset_distrLatticeType (T : finType) :=
  [distrLatticeType of {set T} for [distrLatticeType of {subset T}]].
Canonical subset_bDistrLatticeType (T : finType) :=
  [bDistrLatticeType of {set T}].
Canonical subset_tbDistrLatticeType (T : finType) :=
  [tbDistrLatticeType of {set T}].
Canonical subset_cbDistrLatticeType (T : finType) :=
  [cbDistrLatticeType of {set T} for [cbDistrLatticeType of {subset T}]].
Canonical subset_ctbDistrLatticeType (T : finType) :=
  [ctbDistrLatticeType of {set T} for [ctbDistrLatticeType of {subset T}]].
Canonical subset_finPOrderType (T : finType) :=
  [finPOrderType of {set T}].
Canonical subset_finLatticeType (T : finType) :=
  [finLatticeType of {set T}].
Canonical subset_finDistrLatticeType (T : finType) :=
  [finDistrLatticeType of {set T}].
Canonical subset_finCTBDistrLatticeType (T : finType) :=
  [finCTBDistrLatticeType of {set T}].

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
Export DualSyntax.
Export POSyntax.
Export TBPOrderSyntax.
Export LatticeSyntax.
Export CBDistrLatticeSyntax.
Export CTBDistrLatticeSyntax.
Export DvdSyntax.
Export ProdSyntax.
Export LexiSyntax.
End Syntax.

Module LTheory.
Export POCoercions.
Export DualOrder.

Export POrderTheory.
Export BPOrderTheory.
Export TPOrderTheory.
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

End Order.

Export RelOrder.Syntax.
Export Order.Syntax.

Export RelOrder.POrder.Exports RelOrder.BPOrder.Exports.
Export RelOrder.TPOrder.Exports RelOrder.TBPOrder.Exports.
Export RelOrder.Meet.Exports RelOrder.BMeet.Exports.
Export RelOrder.TMeet.Exports RelOrder.TBMeet.Exports.
Export RelOrder.Join.Exports RelOrder.BJoin.Exports.
Export RelOrder.TJoin.Exports RelOrder.TBJoin.Exports.
Export RelOrder.Lattice.Exports RelOrder.BLattice.Exports.
Export RelOrder.TLattice.Exports RelOrder.TBLattice.Exports.
Export RelOrder.DistrLattice.Exports RelOrder.BDistrLattice.Exports.
Export RelOrder.TDistrLattice.Exports RelOrder.TBDistrLattice.Exports.
Export RelOrder.Total.Exports RelOrder.BTotal.Exports.
Export RelOrder.TTotal.Exports RelOrder.TBTotal.Exports.

Export Order.POrder.Exports.
Export Order.BPOrder.Exports.
Export Order.TPOrder.Exports.
Export Order.TBPOrder.Exports.
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
Export Order.CBDistrLattice.Exports.
Export Order.CTBDistrLattice.Exports.
Export Order.Total.Exports.
Export Order.BTotal.Exports.
Export Order.TTotal.Exports.
Export Order.TBTotal.Exports.
Export Order.FinPOrder.Exports.
Export Order.FinBPOrder.Exports.
Export Order.FinTPOrder.Exports.
Export Order.FinTBPOrder.Exports.
Export Order.FinMeetSemilattice.Exports.
Export Order.FinBMeetSemilattice.Exports.
Export Order.FinJoinSemilattice.Exports.
Export Order.FinTJoinSemilattice.Exports.
Export Order.FinLattice.Exports.
Export Order.FinTBLattice.Exports.
Export Order.FinDistrLattice.Exports.
Export Order.FinTBDistrLattice.Exports.
Export Order.FinCTBDistrLattice.Exports.
Export Order.FinTotal.Exports.
Export Order.FinTBTotal.Exports.
Export Order.RelOrderCoercions.Exports.

Export RelOrder.DualOrder.Exports.
Export RelOrder.LePOrderMixin.Exports.
Export RelOrder.BottomRelMixin.Exports.
Export RelOrder.TopRelMixin.Exports.
Export RelOrder.MeetRelMixin.Exports.
Export RelOrder.JoinRelMixin.Exports.
Export RelOrder.DistrLatticeRelMixin.Exports.
Export RelOrder.LatticePOrderRelMixin.Exports.
Export RelOrder.DistrLatticePOrderRelMixin.Exports.
Export RelOrder.TotalLatticeRelMixin.Exports.
Export RelOrder.TotalPOrderRelMixin.Exports.
Export RelOrder.TotalMeetOrderRelMixin.Exports.
Export RelOrder.TotalJoinOrderRelMixin.Exports.
Export RelOrder.LtPOrderMixin.Exports.
Export RelOrder.MeetJoinMixin.Exports.
Export RelOrder.DistrMeetJoinMixin.Exports.
Export RelOrder.LeOrderMixin.Exports.
Export RelOrder.LtOrderMixin.Exports.

Export Order.RelOrderMixin.Exports.
Export Order.TotalLatticeMixin.Exports.
Export Order.TotalPOrderMixin.Exports.
Export Order.TotalMeetSemilatticeMixin.Exports.
Export Order.TotalJoinSemilatticeMixin.Exports.
Export Order.CBDistrLatticeMixin.Exports.
Export Order.CTBDistrLatticeMixin.Exports.
Export Order.TotalLatticeMixin.Exports.
Export Order.TotalPOrderMixin.Exports.
Export Order.TotalMeetSemilatticeMixin.Exports.
Export Order.TotalJoinSemilatticeMixin.Exports.
Export Order.CanMixin.Exports.
Export Order.SubOrder.Exports.

Export Order.NatOrder.Exports.
Export Order.NatMonotonyTheory.
Export Order.NatDvd.Exports.
Export Order.OrdinalOrder.Exports.
Export Order.BoolOrder.Exports.
Export Order.ProdOrder.Exports.
Export Order.SigmaOrder.Exports.
Export Order.ProdLexiOrder.Exports.
Export Order.SeqProdOrder.Exports.
Export Order.SeqLexiOrder.Exports.
Export Order.TupleProdOrder.Exports.
Export Order.TupleLexiOrder.Exports.

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

Definition sig : ordsum -> T  := enum_val \o (cast_ord (esym card)).
Definition rank : T -> ordsum := (cast_ord card) \o enum_rank.

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

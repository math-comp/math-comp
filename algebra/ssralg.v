(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
From mathcomp Require Import choice fintype finfun bigop prime binomial.
From mathcomp Require Export comoid.

(******************************************************************************)
(*                            Ring-like structures                            *)
(*                                                                            *)
(* NB: See CONTRIBUTING.md for an introduction to HB concepts and commands.   *)
(*                                                                            *)
(* Reference: Francois Garillot, Georges Gonthier, Assia Mahboubi, Laurence   *)
(* Rideau, Packaging mathematical structures, TPHOLs 2009                     *)
(*                                                                            *)
(* This file defines the following algebraic structures:                      *)
(*                                                                            *)
(*  semiPzRingType == non-commutative semi rings                              *)
(*                    (NModule with a multiplication)                         *)
(*                    The HB class is called PzSemiRing.                      *)
(*  semiNzRingType == non-commutative non-trivial semi rings                  *)
(*                    (NModule with a multiplication)                         *)
(*                    The HB class is called NzSemiRing.                      *)
(* comPzSemiRingType == commutative semi rings                                *)
(*                    The HB class is called ComPzSemiRing.                   *)
(* comNzSemiRingType == commutative non-trivial semi rings                    *)
(*                    The HB class is called ComNzSemiRing.                   *)
(*      pzRingType == non-commutative rings                                   *)
(*                    (semi rings with an opposite)                           *)
(*                    The HB class is called PzRing.                          *)
(*      nzRingType == non-commutative non-trivial rings                       *)
(*                    (semi rings with an opposite)                           *)
(*                    The HB class is called NzRing.                          *)
(*   comPzRingType == commutative rings                                       *)
(*                    The HB class is called ComPzRing.                       *)
(*   comNzRingType == commutative non-trivial rings                           *)
(*                    The HB class is called ComNzRing.                       *)
(*      lmodType R == module with left multiplication by external scalars     *)
(*                    in the pzRing R                                         *)
(*                    The HB class is called Lmodule.                         *)
(*      lalgType R == left algebra, ring with scaling                         *)
(*                    that associates on the left                             *)
(*                    The HB class is called Lalgebra.                        *)
(*       algType R == ring with scaling that associates both left and right   *)
(*                    The HB class is called Algebra.                         *)
(*    comAlgType R == commutative algType                                     *)
(*                    The HB class is called ComAlgebra.                      *)
(*    unitRingType == Rings whose units have computable inverses              *)
(*                    The HB class is called UnitRing.                        *)
(* comUnitRingType == commutative UnitRing                                    *)
(*                    The HB class is called ComUnitRing.                     *)
(*   unitAlgType R == algebra with computable inverses                        *)
(*                    The HB class is called UnitAlgebra.                     *)
(*comUnitAlgType R == commutative UnitAlgebra                                 *)
(*                    The HB class is called ComUnitAlgebra.                  *)
(*     idomainType == integral, commutative, ring with partial inverses       *)
(*                    The HB class is called IntegralDomain.                  *)
(*       fieldType == commutative fields                                      *)
(*                    The HB class is called Field.                           *)
(*    decFieldType == fields with a decidable first order theory              *)
(*                    The HB class is called DecidableField.                  *)
(* closedFieldType == algebraically closed fields                             *)
(*                    The HB class is called ClosedField.                     *)
(*                                                                            *)
(* and their joins with subType:                                              *)
(*                                                                            *)
(*   subPzSemiRingType R P == join of pzSemiRingType and                      *)
(*                            subType (P : pred R) such that val is a         *)
(*                            semiring morphism                               *)
(*                            The HB class is called SubPzSemiRing.           *)
(*   subNzSemiRingType R P == join of nzSemiRingType and                      *)
(*                            subType (P : pred R) such that val is a         *)
(*                            semiring morphism                               *)
(*                            The HB class is called SubNzSemiRing.           *)
(*subComPzSemiRingType R P == join of comPzSemiRingType and                   *)
(*                            subType (P : pred R) such that val is a morphism*)
(*                            The HB class is called SubComPzSemiRing.        *)
(*subComNzSemiRingType R P == join of comNzSemiRingType and                   *)
(*                            subType (P : pred R) such that val is a morphism*)
(*                            The HB class is called SubComNzSemiRing.        *)
(*       subPzRingType R P == join of pzRingType and subType (P : pred R)     *)
(*                            such that val is a morphism                     *)
(*                            The HB class is called SubPzRing.               *)
(*    subComPzRingType R P == join of comPzRingType and subType (P : pred R)  *)
(*                            such that val is a morphism                     *)
(*                            The HB class is called SubComPzRing.            *)
(*       subNzRingType R P == join of nzRingType and subType (P : pred R)     *)
(*                            such that val is a morphism                     *)
(*                            The HB class is called SubNzRing.               *)
(*    subComNzRingType R P == join of comNzRingType and subType (P : pred R)  *)
(*                            such that val is a morphism                     *)
(*                            The HB class is called SubComNzRing.            *)
(*       subLmodType R V P == join of lmodType and subType (P : pred V)       *)
(*                            such that val is scalable                       *)
(*                            The HB class is called SubLmodule.              *)
(*       subLalgType R V P == join of lalgType and subType (P : pred V)       *)
(*                            such that val is linear                         *)
(*                            The HB class is called SubLalgebra.             *)
(*        subAlgType R V P == join of algType and subType (P : pred V)        *)
(*                            such that val is linear                         *)
(*                            The HB class is called SubAlgebra.              *)
(*     subUnitRingType R P == join of unitRingType and subType (P : pred R)   *)
(*                            such that val is a ring morphism                *)
(*                            The HB class is called SubUnitRing.             *)
(*  subComUnitRingType R P == join of comUnitRingType and subType (P : pred R)*)
(*                            such that val is a ring morphism                *)
(*                            The HB class is called SubComUnitRing.          *)
(*      subIdomainType R P == join of idomainType and subType (P : pred R)    *)
(*                            such that val is a ring morphism                *)
(*                            The HB class is called SubIntegralDomain.       *)
(*            subField R P == join of fieldType and subType (P : pred R)      *)
(*                            such that val is a ring morphism                *)
(*                            The HB class is called SubField.                *)
(*                                                                            *)
(* Morphisms between the above structures (see below for details):            *)
(*                                                                            *)
(*      {rmorphism R -> S} == semi ring (resp. ring) morphism between         *)
(*                            semiPzRingType (resp. pzRingType) instances     *)
(*                            R and S.                                        *)
(*                            The HB class is called RMorphism.               *)
(*     {linear U -> V | s} == linear functions of type U -> V, where U is a   *)
(*                            left module over a ring R, V is a Z-module, and *)
(*                            s is a scaling operator of type R -> V -> V.    *)
(*                            The HB class is called Linear.                  *)
(* {lrmorphism A -> B | s} == linear ring morphisms of type A -> B, where A   *)
(*                            is a left algebra over a ring R, B is a ring,   *)
(*                            and s is a scaling operator of type R -> B -> B.*)
(*                            The HB class is called LRMorphism.              *)
(*                                                                            *)
(* -> The scaling operator s above should be one of *:%R, *%R, or a           *)
(*    combination nu \; *:%R or nu \; *%R with a ring morphism nu; otherwise  *)
(*    some of the theory (e.g., the linearZ rule) will not apply. To enable   *)
(*    the overloading of the scaling operator, we use the following           *)
(*    structures:                                                             *)
(*                                                                            *)
(*     GRing.Scale.law R V == scaling morphisms of type R -> V -> V           *)
(*                            The HB class is called Scale.Law.               *)
(*                                                                            *)
(* Closedness predicates for the algebraic structures:                        *)
(*                                                                            *)
(*  opprClosed V == predicate closed under opposite on V : zmodType           *)
(*                  The HB class is called OppClosed.                         *)
(*  addrClosed V == predicate closed under addition on V : nmodType           *)
(*                  The HB class is called AddClosed.                         *)
(*  zmodClosed V == predicate closed under opposite and addition on V         *)
(*                  The HB class is called ZmodClosed.                        *)
(* mulr2Closed R == predicate closed under multiplication on                  *)
(*                  R : semiPzRingType                                        *)
(*                  The HB class is called Mul2Closed.                        *)
(*  mulrClosed R == predicate closed under multiplication and for 1           *)
(*                  The HB class is called MulClosed.                         *)
(*  smulClosed R == predicate closed under multiplication and for -1          *)
(*                  The HB class is called SmulClosed.                        *)
(* semiring2Closed R == predicate closed under addition and multiplication    *)
(*                  The HB class is called Semiring2Closed.                   *)
(* semiringClosed R == predicate closed under semiring operations             *)
(*                  The HB class is called SemiringClosed.                    *)
(* subringClosed R == predicate closed under ring operations                  *)
(*                  The HB class is called SubringClosed.                     *)
(*   divClosed R == predicate closed under division                           *)
(*                  The HB class is called DivClosed.                         *)
(*  sdivClosed R == predicate closed under division and opposite              *)
(*                  The HB class is called SdivClosed.                        *)
(* submodClosed R == predicate closed under lmodType operations               *)
(*                  The HB class is called SubmodClosed.                      *)
(* subalgClosed R == predicate closed under lalgType operations               *)
(*                  The HB class is called SubalgClosed.                      *)
(* divringClosed R == predicate closed under unitRing operations              *)
(*                  The HB class is called DivringClosed.                     *)
(* divalgClosed R S == predicate closed under (S : unitAlg R) operations      *)
(*                  The HB class is called DivalgClosed.                      *)
(*                                                                            *)
(* Canonical properties of the algebraic structures:                          *)
(*  * Nmodule (additive abelian monoids):                                     *)
(*                     0 == the zero (additive identity) of a Nmodule         *)
(*                 x + y == the sum of x and y (in a Nmodule)                 *)
(*                x *+ n == n times x, with n in nat (non-negative), i.e.,    *)
(*                          x + (x + .. (x + x)..) (n terms); x *+ 1 is thus  *)
(*                          convertible to x, and x *+ 2 to x + x             *)
(*        \sum_<range> e == iterated sum for a Zmodule (cf bigop.v)           *)
(*                  e`_i == nth 0 e i, when e : seq M and M has a zmodType    *)
(*                          structure                                         *)
(*             support f == 0.-support f, i.e., [pred x | f x != 0]           *)
(*         addr_closed S <-> collective predicate S is closed under finite    *)
(*                           sums (0 and x + y in S, for x, y in S)           *)
(* [SubChoice_isSubNmodule of U by <:] == nmodType mixin for a subType whose  *)
(*                          base type is a nmodType and whose predicate's is  *)
(*                          a nmodClosed                                      *)
(*                                                                            *)
(*  * Zmodule (additive abelian groups):                                      *)
(*                   - x == the opposite (additive inverse) of x              *)
(*                 x - y == the difference of x and y; this is only notation  *)
(*                          for x + (- y)                                     *)
(*                x *- n == notation for - (x *+ n), the opposite of x *+ n   *)
(*         oppr_closed S <-> collective predicate S is closed under opposite  *)
(*         zmod_closed S <-> collective predicate S is closed under zmodType  *)
(*                          operations (0 and x - y in S, for x, y in S)      *)
(*                          This property coerces to oppr_pred and addr_pred. *)
(* [SubChoice_isSubZmodule of U by <:] == zmodType mixin for a subType whose  *)
(*                          base type is a zmodType and whose predicate's     *)
(*                          is a zmodClosed                                   *)
(*                                                                            *)
(*  * PzSemiRing (non-commutative semirings):                                 *)
(*                    R^c == the converse (semi)ring for R: R^c is convertible*)
(*                           to R but when R has a canonical (semi)NzRingType *)
(*                           structure R^c has the converse one:              *)
(*                           if x y : R^c, then x * y = (y : R) * (x : R)     *)
(*                      1 == the multiplicative identity element of a semiring*)
(*                   n%:R == the semiring image of an n in nat; this is just  *)
(*                           notation for 1 *+ n, so 1%:R is convertible to 1 *)
(*                           and 2%:R to 1 + 1                                *)
(*               <number> == <number>%:R with <number> a sequence of digits   *)
(*                  x * y == the semiring product of x and y                  *)
(*        \prod_<range> e == iterated product for a semiring (cf bigop.v)     *)
(*                 x ^+ n == x to the nth power with n in nat (non-negative), *)
(*                           i.e., x * (x * .. (x * x)..) (n factors); x ^+ 1 *)
(*                           is thus convertible to x, and x ^+ 2 to x * x    *)
(*         GRing.comm x y <-> x and y commute, i.e., x * y = y * x            *)
(*           GRing.lreg x <-> x if left-regular, i.e., *%R x is injective     *)
(*           GRing.rreg x <-> x if right-regular, i.e., *%R^~ x is injective  *)
(*               [char R] == the characteristic of R, defined as the set of   *)
(*                           prime numbers p such that p%:R = 0 in R          *)
(*                           The set [char R] has at most one element, and is *)
(*                           implemented as a pred_nat collective predicate   *)
(*                           (see prime.v); thus the statement p \in [char R] *)
(*                           can be read as `R has characteristic p', while   *)
(*                           [char R] =i pred0 means `R has characteristic 0' *)
(*                           when R is a field.                               *)
(*     Frobenius_aut chRp == the Frobenius automorphism mapping x in R to     *)
(*                           x ^+ p, where chRp : p \in [char R] is a proof   *)
(*                           that R has (non-zero) characteristic p           *)
(*          mulr_closed S <-> collective predicate S is closed under finite   *)
(*                           products (1 and x * y in S for x, y in S)        *)
(*      semiring_closed S <-> collective predicate S is closed under semiring *)
(*                           operations (0, 1, x + y and x * y in S)          *)
(* [SubNmodule_isSubPzSemiRing of R by <:] ==                                 *)
(* [SubChoice_isSubPzSemiRing of R by <:] == semiPzRingType mixin for a       *)
(*                           subType whose base type is a pzSemiRingType and  *)
(*                           whose predicate's is a semiringClosed            *)
(*                                                                            *)
(*  * PzSemiRing (non-commutative non-trivial semirings):                     *)
(* [SubNmodule_isSubNzSemiRing of R by <:] ==                                 *)
(* [SubChoice_isSubNzSemiRing of R by <:] == semiNzRingType mixin for a       *)
(*                           subType whose base type is a nzSemiRingType and  *)
(*                           whose predicate's is a semiringClosed            *)
(*                                                                            *)
(*  * PzRing (non-commutative rings):                                         *)
(*         GRing.sign R b := (-1) ^+ b in R : nzRingType, with b : bool       *)
(*                           This is a parsing-only helper notation, to be    *)
(*                           used for defining more specific instances.       *)
(*         smulr_closed S <-> collective predicate S is closed under products *)
(*                           and opposite (-1 and x * y in S for x, y in S)   *)
(*       subring_closed S <-> collective predicate S is closed under ring     *)
(*                           operations (1, x - y and x * y in S)             *)
(* [SubZmodule_isSubPzRing of R by <:] ==                                     *)
(* [SubChoice_isSubPzRing of R by <:] == pzRingType mixin for a subType whose *)
(*                           base                                             *)
(*                           type is a pzRingType and whose predicate's is a  *)
(*                           subringClosed                                    *)
(*                                                                            *)
(*  * NzRing (non-commutative non-trivial rings):                             *)
(* [SubZmodule_isSubNzRing of R by <:] ==                                     *)
(* [SubChoice_isSubNzRing of R by <:] == nzRingType mixin for a subType whose *)
(*                           base                                             *)
(*                           type is a nzRingType and whose predicate's is a  *)
(*                           subringClosed                                    *)
(*                                                                            *)
(*  * ComPzSemiRing (commutative PzSemiRings):                                *)
(* [SubNmodule_isSubComPzSemiRing of R by <:] ==                              *)
(* [SubChoice_isSubComPzSemiRing of R by <:] == comPzSemiRingType mixin for a *)
(*                           subType whose base type is a comPzSemiRingType   *)
(*                          and whose predicate's is a semiringClosed         *)
(*                                                                            *)
(*  * ComNzSemiRing (commutative NzSemiRings):                                *)
(* [SubNmodule_isSubComNzSemiRing of R by <:] ==                              *)
(* [SubChoice_isSubComNzSemiRing of R by <:] == comNzSemiRingType mixin for a *)
(*                           subType whose base type is a comNzSemiRingType   *)
(*                          and whose predicate's is a semiringClosed         *)
(*                                                                            *)
(*  * ComPzRing (commutative PzRings):                                        *)
(* [SubZmodule_isSubComPzRing of R by <:] ==                                  *)
(* [SubChoice_isSubComPzRing of R by <:] == comPzRingType mixin for a         *)
(*                           subType whose base type is a comPzRingType and   *)
(*                           whose predicate's is a subringClosed             *)
(*                                                                            *)
(*  * ComNzRing (commutative NzRings):                                        *)
(* [SubZmodule_isSubComNzRing of R by <:] ==                                  *)
(* [SubChoice_isSubComNzRing of R by <:] == comNzRingType mixin for a         *)
(*                           subType whose base type is a comNzRingType and   *)
(*                           whose predicate's is a subringClosed             *)
(*                                                                            *)
(*  * UnitRing (NzRings whose units have computable inverses):                *)
(*     x \is a GRing.unit <=> x is a unit (i.e., has an inverse)              *)
(*                   x^-1 == the ring inverse of x, if x is a unit, else x    *)
(*                  x / y == x divided by y (notation for x * y^-1)           *)
(*                 x ^- n := notation for (x ^+ n)^-1, the inverse of x ^+ n  *)
(*         invr_closed S <-> collective predicate S is closed under inverse   *)
(*         divr_closed S <-> collective predicate S is closed under division  *)
(*                           (1 and x / y in S)                               *)
(*        sdivr_closed S <-> collective predicate S is closed under division  *)
(*                           and opposite (-1 and x / y in S, for x, y in S)  *)
(*      divring_closed S <-> collective predicate S is closed under unitRing  *)
(*                           operations (1, x - y and x / y in S)             *)
(* [SubNzRing_isSubUnitRing of R by <:] ==                                    *)
(* [SubChoice_isSubUnitRing of R by <:] == unitRingType mixin for a subType   *)
(*                           whose base type is a unitRingType and whose      *)
(*                           predicate's is a divringClosed and whose ring    *)
(*                           structure is compatible with the base type's     *)
(*                                                                            *)
(*  * ComUnitRing (commutative rings with computable inverses):               *)
(* [SubChoice_isSubComUnitRing of R by <:] == comUnitRingType mixin for a     *)
(*                           subType whose base type is a comUnitRingType and *)
(*                           whose predicate's is a divringClosed and whose   *)
(*                           ring structure is compatible with the base       *)
(*                           type's                                           *)
(*                                                                            *)
(*  * IntegralDomain (integral, commutative, ring with partial inverses):     *)
(* [SubComUnitRing_isSubIntegralDomain R by <:] ==                            *)
(* [SubChoice_isSubIntegralDomain R by <:] == mixin axiom for a idomain       *)
(*                           subType                                          *)
(*                                                                            *)
(*  * Field (commutative fields):                                             *)
(*  GRing.Field.axiom inv == field axiom: x != 0 -> inv x * x = 1 for all x   *)
(*                           This is equivalent to the property above, but    *)
(*                           does not require a unitRingType as inv is an     *)
(*                           explicit argument.                               *)
(* [SubIntegralDomain_isSubField of R by <:] == mixin axiom for a field       *)
(*                           subType                                          *)
(*                                                                            *)
(*  * DecidableField (fields with a decidable first order theory):            *)
(*           GRing.term R == the type of formal expressions in a unit ring R  *)
(*                           with formal variables 'X_k, k : nat, and         *)
(*                           manifest constants x%:T, x : R                   *)
(*                           The notation of all the ring operations is       *)
(*                           redefined for terms, in scope %T.                *)
(*        GRing.formula R == the type of first order formulas over R; the %T  *)
(*                           scope binds the logical connectives /\, \/, ~,   *)
(*                           ==>, ==, and != to formulae; GRing.True/False    *)
(*                           and GRing.Bool b denote constant formulae, and   *)
(*                           quantifiers are written 'forall/'exists 'X_k, f  *)
(*                             GRing.Unit x tests for ring units              *)
(*                             GRing.If p_f t_f e_f emulates if-then-else     *)
(*                             GRing.Pick p_f t_f e_f emulates fintype.pick   *)
(*                             foldr GRing.Exists/Forall q_f xs can be used   *)
(*                               to write iterated quantifiers                *)
(*         GRing.eval e t == the value of term t with valuation e : seq R     *)
(*                           (e maps 'X_i to e`_i)                            *)
(*  GRing.same_env e1 e2 <-> environments e1 and e2 are extensionally equal   *)
(*        GRing.qf_form f == f is quantifier-free                             *)
(*        GRing.holds e f == the intuitionistic CiC interpretation of the     *)
(*                           formula f holds with valuation e                 *)
(*      GRing.qf_eval e f == the value (in bool) of a quantifier-free f       *)
(*          GRing.sat e f == valuation e satisfies f (only in a decField)     *)
(*          GRing.sol n f == a sequence e of size n such that e satisfies f,  *)
(*                           if one exists, or [::] if there is no such e     *)
(*        'exists 'X_i, u1 == 0 /\ ... /\ u_m == 0 /\ v1 != 0 ... /\ v_n != 0 *)
(*                                                                            *)
(*  * Lmodule (module with left multiplication by external scalars).          *)
(*                 a *: v == v scaled by a, when v is in an Lmodule V and a   *)
(*                           is in the scalar Ring of V                       *)
(*        scaler_closed S <-> collective predicate S is closed under scaling  *)
(*        linear_closed S <-> collective predicate S is closed under linear   *)
(*                           combinations (a *: u + v in S when u, v in S)    *)
(*        submod_closed S <-> collective predicate S is closed under lmodType *)
(*                           operations (0 and a *: u + v in S)               *)
(* [SubZmodule_isSubLmodule of V by <:] ==                                    *)
(* [SubChoice_isSubLmodule of V by <:] == mixin axiom for a subType of an     *)
(*                           lmodType                                         *)
(*                                                                            *)
(*  * Lalgebra (left algebra, ring with scaling that associates on the left): *)
(*                    R^o == the regular algebra of R: R^o is convertible to  *)
(*                           R, but when R has a nzRingType structure then    *)
(*                           R^o extends it to an lalgType structure by       *)
(*                           letting R act on itself: if x : R and y : R^o    *)
(*                           then x *: y = x * (y : R)                        *)
(*                   k%:A == the image of the scalar k in an L-algebra; this  *)
(*                           is simply notation for k *: 1                    *)
(*        subalg_closed S <-> collective predicate S is closed under lalgType *)
(*                           operations (1, a *: u + v and u * v in S)        *)
(* [SubNzRing_SubLmodule_isSubLalgebra of V by <:] ==                         *)
(* [SubChoice_isSubLalgebra of V by <:] == mixin axiom for a subType of an    *)
(*                           lalgType                                         *)
(*                                                                            *)
(*  * Algebra (ring with scaling that associates both left and right):        *)
(* [SubLalgebra_isSubAlgebra of V by <:] ==                                   *)
(* [SubChoice_isSubAlgebra of V by <:] == mixin axiom for a subType of an     *)
(*                           algType                                          *)
(*                                                                            *)
(*  * UnitAlgebra (algebra with computable inverses):                         *)
(*        divalg_closed S <-> collective predicate S is closed under all      *)
(*                           unitAlgType operations (1, a *: u + v and u / v  *)
(*                           are in S fo u, v in S)                           *)
(*                                                                            *)
(*   In addition to this structure hierarchy, we also develop a separate,     *)
(* parallel hierarchy for morphisms linking these structures:                 *)
(*                                                                            *)
(* * RMorphism (semiring or ring morphisms):                                  *)
(*       multiplicative f <-> f of type R -> S is multiplicative, i.e., f     *)
(*                           maps 1 and * in R to 1 and * in S, respectively  *)
(*                           R and S must have canonical pzSemiRingType       *)
(*                           instances                                        *)
(*     {rmorphism R -> S} == the interface type for semiring morphisms; both  *)
(*                           R and S must have pzSemiRingType instances       *)
(*                           When both R and S have pzRingType instances, it  *)
(*                           is a ring morphism.                              *)
(*                        := GRing.RMorphism.type R S                         *)
(*                                                                            *)
(*  -> If R and S are UnitRings the f also maps units to units and inverses   *)
(*     of units to inverses; if R is a field then f is a field isomorphism    *)
(*     between R and its image.                                               *)
(*  -> Additive properties (raddf_suffix, see below) are duplicated and       *)
(*     specialised for RMorphism (as rmorph_suffix). This allows more         *)
(*     precise rewriting and cleaner chaining: although raddf lemmas will     *)
(*     recognize RMorphism functions, the converse will not hold (we cannot   *)
(*     add reverse inheritance rules because of incomplete backtracking in    *)
(*     the Canonical Projection unification), so one would have to insert a   *)
(*     /= every time one switched from additive to multiplicative rules.      *)
(*                                                                            *)
(* * Linear (linear functions):                                               *)
(*       scalable_for s f <-> f of type U -> V is scalable for the scaling    *)
(*                           operator s of type R -> V -> V, i.e.,            *)
(*                           f morphs a *: _ to s a _; R, U, and V must be a  *)
(*                           pzRingType, an lmodType R, and a zmodType,       *)
(*                           respectively.                                    *)
(*                        := forall a, {morph f : u / a *: u >-> s a u}       *)
(*             scalable f <-> f of type U -> V is scalable, i.e., f morphs    *)
(*                           scaling on U to scaling on V, a *: _ to a *: _;  *)
(*                           U and V must be an lmodType R for the same       *)
(*                           pzRingType R.                                    *)
(*                        := scalable_for *:%R f                              *)
(*         linear_for s f <-> f of type U -> V is linear for s of type        *)
(*                           R -> V -> V, i.e.,                               *)
(*                           f (a *: u + v) = s a (f u) + f v;                *)
(*                           R, U, and V must be a pzRingType, an lmodType R, *)
(*                           and a zmodType, respectively.                    *)
(*               linear f <-> f of type U -> V is linear, i.e.,               *)
(*                           f (f *: u + v) = a *: f u + f v;                 *)
(*                           U and V must be lmodType R for the same          *)
(*                           pzRingType R.                                    *)
(*                        := linear_for *:%R f                                *)
(*               scalar f <-> f of type U -> R is a scalar function, i.e.,    *)
(*                           f (a *: u + v) = a * f u + f v;                  *)
(*                           R and U must be a pzRingType and an lmodType R,  *)
(*                           respectively.                                    *)
(*                        := linear_for *%R f                                 *)
(*    {linear U -> V | s} == the interface type for functions linear for the  *)
(*                           scaling operator s of type R -> V -> V, i.e., a  *)
(*                           structure that encapsulates two properties       *)
(*                           semi_additive f and scalable_for s f for         *)
(*                           functions f : U -> V; R, U, and V must be a      *)
(*                           pzRingType, an lmodType R, and a zmodType,       *)
(*                           respectively                                     *)
(*                        := @GRing.Linear.type R U V s                       *)
(*        {linear U -> V} == the interface type for linear functions, of type *)
(*                           U -> V where both U and V must be lmodType R for *)
(*                           the same pzRingType R                            *)
(*                        := {linear U -> V | *:%R}                           *)
(*             {scalar U} == the interface type for scalar functions of type  *)
(*                           U -> R where U must be an lmodType R             *)
(*                        := {linear U -> V | *%R}                            *)
(*          (a *: u)%Rlin == transient forms that simplify to a *: u, a * u,  *)
(*           (a * u)%Rlin    nu a *: u, and nu a * u, respectively, and are   *)
(*       (a *:^nu u)%Rlin    created by rewriting with the linearZ lemma      *)
(*        (a *^nu u)%Rlin    The forms allows the RHS of linearZ to be matched*)
(*                           reliably, using the GRing.Scale.law structure.   *)
(* -> Similarly to Ring morphisms, additive properties are specialized for    *)
(*    linear functions.                                                       *)
(* -> Although {scalar U} is convertible to {linear U -> R^o}, it does not    *)
(*    actually use R^o, so that rewriting preserves the canonical structure   *)
(*    of the range of scalar functions.                                       *)
(* -> The generic linearZ lemma uses a set of bespoke interface structures to *)
(*    ensure that both left-to-right and right-to-left rewriting work even in *)
(*    the presence of scaling functions that simplify non-trivially (e.g.,    *)
(*    idfun \; *%R). Because most of the canonical instances and projections  *)
(*    are coercions the machinery will be mostly invisible (with only the     *)
(*    {linear ...} structure and %Rlin notations showing), but users should   *)
(*    beware that in (a *: f u)%Rlin, a actually occurs in the f u subterm.   *)
(* -> The simpler linear_LR, or more specialized linearZZ and scalarZ rules   *)
(*    should be used instead of linearZ if there are complexity issues, as    *)
(*    well as for explicit forward and backward application, as the main      *)
(*    parameter of linearZ is a proper sub-interface of {linear fUV | s}.     *)
(*                                                                            *)
(* * LRMorphism (linear ring morphisms, i.e., algebra morphisms):             *)
(* {lrmorphism A -> B | s} == the interface type for ring morphisms linear    *)
(*                           for the scaling operator s of type R -> B -> B,  *)
(*                           i.e., the join of ring morphisms                 *)
(*                           {rmorphism A -> B} and linear functions          *)
(*                           {linear A -> B | s}; R, A, and B must be a       *)
(*                           pzRingType, an lalgType R, and a nzRingType,     *)
(*                           respectively                                     *)
(*                        := @GRing.LRMorphism.type R A B s                   *)
(*    {lrmorphism A -> B} == the interface type for algebra morphisms, where  *)
(*                           A and B must be lalgType R for the same          *)
(*                           pzRingType R                                     *)
(*                        := {lrmorphism A -> B | *:%R}                       *)
(*  -> Linear and rmorphism properties do not need to be specialized for      *)
(*     as we supply inheritance join instances in both directions.            *)
(* Finally we supply some helper notation for morphisms:                      *)
(*                    x^f == the image of x under some morphism               *)
(*                           This notation is only reserved (not defined)     *)
(*                           here; it is bound locally in sections where some *)
(*                           morphism is used heavily (e.g., the container    *)
(*                           morphism in the parametricity sections of poly   *)
(*                           and matrix, or the Frobenius section here)       *)
(*                     \0 == the constant null function, which has a          *)
(*                           canonical linear structure, and simplifies on    *)
(*                           application (see ssrfun.v)                       *)
(*                 f \+ g == the additive composition of f and g, i.e., the   *)
(*                           function x |-> f x + g x; f \+ g is canonically  *)
(*                           linear when f and g are, and simplifies on       *)
(*                           application (see ssrfun.v)                       *)
(*                 f \- g == the function x |-> f x - g x, canonically        *)
(*                           linear when f and g are, and simplifies on       *)
(*                           application                                      *)
(*                   \- g == the function x |-> - f x, canonically linear     *)
(*                           when f is, and simplifies on application         *)
(*                k \*: f == the function x |-> k *: f x, which is            *)
(*                           canonically linear when f is and simplifies on   *)
(*                           application (this is a shorter alternative to    *)
(*                           *:%R k \o f)                                     *)
(*         GRing.in_alg A == the ring morphism that injects R into A, where A *)
(*                           has an lalgType R structure; GRing.in_alg A k    *)
(*                           simplifies to k%:A                               *)
(*                a \*o f == the function x |-> a * f x, canonically linear   *)
(*                           when f is and its codomain is an algType         *)
(*                           and which simplifies on application              *)
(*                a \o* f == the function x |-> f x * a, canonically linear   *)
(*                           when f is and its codomain is an lalgType        *)
(*                           and which simplifies on application              *)
(*                 f \* g == the function x |-> f x * g x; f \* g             *)
(*                           simplifies on application                        *)
(* The Lemmas about these structures are contained in both the GRing module   *)
(* and in the submodule GRing.Theory, which can be imported when unqualified  *)
(* access to the theory is needed (GRing.Theory also allows the unqualified   *)
(* use of additive, linear, Linear, etc). The main GRing module should NOT be *)
(* imported.                                                                  *)
(*   Notations are defined in scope ring_scope (delimiter %R), except term    *)
(* and formula notations, which are in term_scope (delimiter %T).             *)
(*   This library also extends the conventional suffixes described in library *)
(* ssrbool.v with the following:                                              *)
(*   0 -- ring 0, as in addr0 : x + 0 = x                                     *)
(*   1 -- ring 1, as in mulr1 : x * 1 = x                                     *)
(*   D -- ring addition, as in linearD : f (u + v) = f u + f v                *)
(*   B -- ring subtraction, as in opprB : - (x - y) = y - x                   *)
(*   M -- ring multiplication, as in invfM : (x * y)^-1 = x^-1 * y^-1         *)
(*  Mn -- ring by nat multiplication, as in raddfMn : f (x *+ n) = f x *+ n   *)
(*   N -- ring opposite, as in mulNr : (- x) * y = - (x * y)                  *)
(*   V -- ring inverse, as in mulVr : x^-1 * x = 1                            *)
(*   X -- ring exponentiation, as in rmorphXn : f (x ^+ n) = f x ^+ n         *)
(*   Z -- (left) module scaling, as in linearZ : f (a *: v)  = s *: f v       *)
(* The operator suffixes D, B, M and X are also used for the corresponding    *)
(* operations on nat, as in natrX : (m ^ n)%:R = m%:R ^+ n. For the binary    *)
(* power operator, a trailing "n" suffix is used to indicate the operator     *)
(* suffix applies to the left-hand ring argument, as in                       *)
(*   expr1n : 1 ^+ n = 1 vs. expr1 : x ^+ 1 = x.                              *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope ring_scope.
Declare Scope term_scope.
Declare Scope linear_ring_scope.

Reserved Notation "+%R" (at level 0).
Reserved Notation "-%R" (at level 0).
Reserved Notation "*%R" (at level 0, format " *%R").
Reserved Notation "*:%R" (at level 0, format " *:%R").
Reserved Notation "n %:R" (at level 2, left associativity, format "n %:R").
Reserved Notation "k %:A" (at level 2, left associativity, format "k %:A").
Reserved Notation "[ 'char' F ]" (at level 0, format "[ 'char'  F ]").

Reserved Notation "x %:T" (at level 2, left associativity, format "x %:T").
Reserved Notation "''X_' i" (at level 8, i at level 2, format "''X_' i").
(* Patch for recurring Coq parser bug: Coq seg faults when a level 200 *)
(* notation is used as a pattern.                                      *)
Reserved Notation "''exists' ''X_' i , f"
  (at level 199, i at level 2, right associativity,
   format "'[hv' ''exists'  ''X_' i , '/ '  f ']'").
Reserved Notation "''forall' ''X_' i , f"
  (at level 199, i at level 2, right associativity,
   format "'[hv' ''forall'  ''X_' i , '/ '  f ']'").

Reserved Notation "x ^f" (at level 2, left associativity, format "x ^f").

Reserved Notation "\0" (at level 0).
Reserved Notation "f \+ g" (at level 50, left associativity).
Reserved Notation "f \- g" (at level 50, left associativity).
Reserved Notation "\- f" (at level 35, f at level 35).
Reserved Notation "a \*o f" (at level 40).
Reserved Notation "a \o* f" (at level 40).
Reserved Notation "a \*: f" (at level 40).
Reserved Notation "f \* g" (at level 40, left associativity).

Reserved Notation "'{' 'additive' U '->' V '}'"
  (at level 0, U at level 98, V at level 99,
   format "{ 'additive'  U  ->  V }").
Reserved Notation "'{' 'rmorphism' U '->' V '}'"
  (at level 0, U at level 98, V at level 99,
   format "{ 'rmorphism'  U  ->  V }").
Reserved Notation "'{' 'lrmorphism' U '->' V '|' s '}'"
  (at level 0, U at level 98, V at level 99,
   format "{ 'lrmorphism'  U  ->  V  |  s }").
Reserved Notation "'{' 'lrmorphism' U '->' V '}'"
  (at level 0, U at level 98, V at level 99,
   format "{ 'lrmorphism'  U  ->  V }").
Reserved Notation "'{' 'linear' U '->' V '|' s '}'"
  (at level 0, U at level 98, V at level 99,
   format "{ 'linear'  U  ->  V  |  s }").
Reserved Notation "'{' 'linear' U '->' V '}'"
  (at level 0, U at level 98, V at level 99,
   format "{ 'linear'  U  ->  V }").

Declare Scope ring_scope.
Delimit Scope ring_scope with R.
Declare Scope term_scope.
Delimit Scope term_scope with T.
Local Open Scope ring_scope.

Module Import GRing.

Export GRing.

Import Monoid.Theory.

Local Notation "0" := (@zero _) : ring_scope.
Local Notation "+%R" := (@add _) : function_scope.
Local Notation "x + y" := (add x y) : ring_scope.

Local Notation "x *+ n" := (natmul x n) : ring_scope.

Local Notation "\sum_ ( i <- r | P ) F" := (\big[+%R/0]_(i <- r | P) F).
Local Notation "\sum_ ( m <= i < n ) F" := (\big[+%R/0]_(m <= i < n) F).
Local Notation "\sum_ ( i < n ) F" := (\big[+%R/0]_(i < n) F).
Local Notation "\sum_ ( i 'in' A ) F" := (\big[+%R/0]_(i in A) F).

Local Notation "s `_ i" := (nth 0 s i) : ring_scope.

Section NmoduleTheory.

Variable V : nmodType.
Implicit Types x y : V.

Lemma addrA : associative (@add V).
Proof. exact: addrA. Qed.

Lemma addrC : commutative (@add V).
Proof. exact: addrC. Qed.

Lemma add0r : left_id (@zero V) add.
Proof. exact: add0r. Qed.

Lemma addr0 : right_id (@zero V) add.
Proof. exact: addr0. Qed.

Lemma addrCA : @left_commutative V V +%R. Proof. exact: addrCA. Qed.
Lemma addrAC : @right_commutative V V +%R. Proof. exact: addrAC. Qed.
Lemma addrACA : @interchange V +%R +%R. Proof. exact: addrACA. Qed.

Lemma mulr0n x : x *+ 0 = 0. Proof. exact: mulr0n. Qed.
Lemma mulr1n x : x *+ 1 = x. Proof. exact: mulr1n. Qed.
Lemma mulr2n x : x *+ 2 = x + x. Proof. exact: mulr2n. Qed.
Lemma mulrS x n : x *+ n.+1 = x + (x *+ n). Proof. exact: mulrS. Qed.
Lemma mulrSr x n : x *+ n.+1 = x *+ n + x. Proof. exact: mulrSr. Qed.

Lemma mulrb x (b : bool) : x *+ b = (if b then x else 0).
Proof. exact: mulrb. Qed.

Lemma mul0rn n : 0 *+ n = 0 :> V. Proof. exact: mul0rn. Qed.

Lemma mulrnDl n : {morph (fun x => x *+ n) : x y / x + y}.
Proof. exact: mulrnDl. Qed.

Lemma mulrnDr x m n : x *+ (m + n) = x *+ m + x *+ n.
Proof. exact: mulrnDr. Qed.

Lemma mulrnA x m n : x *+ (m * n) = x *+ m *+ n. Proof. exact: mulrnA. Qed.

Lemma mulrnAC x m n : x *+ m *+ n = x *+ n *+ m. Proof. exact: mulrnAC. Qed.

Lemma iter_addr n x y : iter n (+%R x) y = x *+ n + y.
Proof. exact: iter_addr. Qed.

Lemma iter_addr_0 n x : iter n (+%R x) 0 = x *+ n.
Proof. exact: iter_addr_0. Qed.

Lemma sumrMnl I r P (F : I -> V) n :
  \sum_(i <- r | P i) F i *+ n = (\sum_(i <- r | P i) F i) *+ n.
Proof. exact: sumrMnl. Qed.

Lemma sumrMnr x I r P (F : I -> nat) :
  \sum_(i <- r | P i) x *+ F i = x *+ (\sum_(i <- r | P i) F i).
Proof. exact: sumrMnr. Qed.

Lemma sumr_const (I : finType) (A : pred I) x : \sum_(i in A) x = x *+ #|A|.
Proof. exact: sumr_const. Qed.

Lemma sumr_const_nat m n x : \sum_(n <= i < m) x = x *+ (m - n).
Proof. exact: sumr_const_nat. Qed.

Definition addr_closed := nmod_closed.

End NmoduleTheory.

Local Notation "-%R" := (@opp _) : ring_scope.
Local Notation "- x" := (opp x) : ring_scope.
Local Notation "x - y" := (x + - y) : ring_scope.

Local Notation "x *- n" := (- (x *+ n)) : ring_scope.

Section ZmoduleTheory.

Variable V : zmodType.
Implicit Types x y : V.

Lemma addNr : @left_inverse V V V 0 -%R +%R. Proof. exact: addNr. Qed.
Lemma addrN : @right_inverse V V V 0 -%R +%R. Proof. exact: addrN. Qed.
Definition subrr := addrN.

Lemma addKr : @left_loop V V -%R +%R. Proof. exact: addKr. Qed.
Lemma addNKr : @rev_left_loop V V -%R +%R. Proof. exact: addNKr. Qed.
Lemma addrK : @right_loop V V -%R +%R. Proof. exact: addrK. Qed.
Lemma addrNK : @rev_right_loop V V -%R +%R. Proof. exact: addrNK. Qed.
Definition subrK := addrNK.
Lemma subKr x : involutive (fun y => x - y). Proof. exact: subKr. Qed.
Lemma addrI : @right_injective V V V +%R. Proof. exact: addrI. Qed.
Lemma addIr : @left_injective V V V +%R. Proof. exact: addIr. Qed.
Lemma subrI : right_injective (fun x y => x - y). Proof. exact: subrI. Qed.
Lemma subIr : left_injective (fun x y => x - y). Proof. exact: subIr. Qed.
Lemma opprK : @involutive V -%R. Proof. exact: opprK. Qed.
Lemma oppr_inj : @injective V V -%R. Proof. exact: oppr_inj. Qed.
Lemma oppr0 : -0 = 0 :> V. Proof. exact: oppr0. Qed.
Lemma oppr_eq0 x : (- x == 0) = (x == 0). Proof. exact: oppr_eq0. Qed.

Lemma subr0 x : x - 0 = x. Proof. exact: subr0. Qed.
Lemma sub0r x : 0 - x = - x. Proof. exact: sub0r. Qed.

Lemma opprB x y : - (x - y) = y - x. Proof. exact: opprB. Qed.
Lemma opprD : {morph -%R: x y / x + y : V}. Proof. exact: opprD. Qed.
Lemma addrKA z x y : (x + z) - (z + y) = x - y. Proof. exact: addrKA. Qed.
Lemma subrKA z x y : (x - z) + (z + y) = x + y. Proof. exact: subrKA. Qed.
Lemma addr0_eq x y : x + y = 0 -> - x = y. Proof. exact: addr0_eq. Qed.
Lemma subr0_eq x y : x - y = 0 -> x = y. Proof. exact: subr0_eq. Qed.
Lemma subr_eq x y z : (x - z == y) = (x == y + z). Proof. exact: subr_eq. Qed.
Lemma subr_eq0 x y : (x - y == 0) = (x == y). Proof. exact: subr_eq0. Qed.
Lemma addr_eq0 x y : (x + y == 0) = (x == - y). Proof. exact: addr_eq0. Qed.
Lemma eqr_opp x y : (- x == - y) = (x == y). Proof. exact: eqr_opp. Qed.
Lemma eqr_oppLR x y : (- x == y) = (x == - y). Proof. exact: eqr_oppLR. Qed.
Lemma mulNrn x n : (- x) *+ n = x *- n. Proof. exact: mulNrn. Qed.

Lemma mulrnBl n : {morph (fun x => x *+ n) : x y / x - y}.
Proof. exact: mulrnBl. Qed.

Lemma mulrnBr x m n : n <= m -> x *+ (m - n) = x *+ m - x *+ n.
Proof. exact: mulrnBr. Qed.

Lemma sumrN I r P (F : I -> V) :
  (\sum_(i <- r | P i) - F i = - (\sum_(i <- r | P i) F i)).
Proof. exact: sumrN. Qed.

Lemma sumrB I r (P : pred I) (F1 F2 : I -> V) :
  \sum_(i <- r | P i) (F1 i - F2 i)
     = \sum_(i <- r | P i) F1 i - \sum_(i <- r | P i) F2 i.
Proof. exact: sumrB. Qed.

Lemma telescope_sumr n m (f : nat -> V) : n <= m ->
  \sum_(n <= k < m) (f k.+1 - f k) = f m - f n.
Proof. exact: telescope_sumr. Qed.

Lemma telescope_sumr_eq n m (f u : nat -> V) : n <= m ->
    (forall k, (n <= k < m)%N -> u k = f k.+1 - f k) ->
  \sum_(n <= k < m) u k = f m - f n.
Proof. exact: telescope_sumr_eq. Qed.

Section ClosedPredicates.

Variable S : {pred V}.

Definition oppr_closed := oppr_closed S.
Definition subr_2closed := subr_closed S.
Definition zmod_closed := zmod_closed S.
 
Lemma zmod_closedN : zmod_closed -> oppr_closed.
Proof. exact: zmod_closedN. Qed.

Lemma zmod_closedD : zmod_closed -> nmod_closed S.
Proof. by move=> z; split; [case: z|apply/zmod_closedD]. Qed.

End ClosedPredicates.

End ZmoduleTheory.

Arguments addrI {V} y [x1 x2].
Arguments addIr {V} x [x1 x2].
Arguments opprK {V}.
Arguments oppr_inj {V} [x1 x2].
Arguments telescope_sumr_eq {V n m} f u.

HB.mixin Record Nmodule_isPzSemiRing R of Nmodule R := {
  one : R;
  mul : R -> R -> R;
  mulrA : associative mul;
  mul1r : left_id one mul;
  mulr1 : right_id one mul;
  mulrDl : left_distributive mul +%R;
  mulrDr : right_distributive mul +%R;
  mul0r : left_zero zero mul;
  mulr0 : right_zero zero mul;
}.

#[short(type="pzSemiRingType")]
HB.structure Definition PzSemiRing :=
  { R of Nmodule_isPzSemiRing R & Nmodule R }.

HB.factory Record isPzSemiRing R of Choice R := {
  zero : R;
  add : R -> R -> R;
  one : R;
  mul : R -> R -> R;
  addrA : associative add;
  addrC : commutative add;
  add0r : left_id zero add;
  mulrA : associative mul;
  mul1r : left_id one mul;
  mulr1 : right_id one mul;
  mulrDl : left_distributive mul add;
  mulrDr : right_distributive mul add;
  mul0r : left_zero zero mul;
  mulr0 : right_zero zero mul;
}.

HB.builders Context R of isPzSemiRing R.
  HB.instance Definition _ := @isNmodule.Build R
    zero add addrA addrC add0r.
  HB.instance Definition _ := @Nmodule_isPzSemiRing.Build R
    one mul mulrA mul1r mulr1 mulrDl mulrDr mul0r mulr0.
HB.end.

Module PzSemiRingExports.
Bind Scope ring_scope with PzSemiRing.sort.
End PzSemiRingExports.
HB.export PzSemiRingExports.

HB.mixin Record PzSemiRing_isNonZero R of PzSemiRing R := {
  oner_neq0 : @one R != 0
}.

#[short(type="nzSemiRingType")]
HB.structure Definition NzSemiRing :=
  { R of PzSemiRing_isNonZero R & PzSemiRing R }.

#[deprecated(since="mathcomp 2.4.0",
             note="Use NzSemiRing instead.")]
Notation SemiRing R := (NzSemiRing R) (only parsing).

Module SemiRing.
#[deprecated(since="mathcomp 2.4.0",
             note="Use NzSemiRing.sort instead.")]
Notation sort := (NzSemiRing.sort) (only parsing).
#[deprecated(since="mathcomp 2.4.0",
             note="Use NzSemiRing.on instead.")]
Notation on R := (NzSemiRing.on R) (only parsing).
#[deprecated(since="mathcomp 2.4.0",
             note="Use NzSemiRing.copy instead.")]
Notation copy T U := (NzSemiRing.copy T U) (only parsing).
End SemiRing.

HB.factory Record Nmodule_isNzSemiRing R of Nmodule R := {
  one : R;
  mul : R -> R -> R;
  mulrA : associative mul;
  mul1r : left_id one mul;
  mulr1 : right_id one mul;
  mulrDl : left_distributive mul +%R;
  mulrDr : right_distributive mul +%R;
  mul0r : left_zero zero mul;
  mulr0 : right_zero zero mul;
  oner_neq0 : one != 0
}.

HB.builders Context R of Nmodule_isNzSemiRing R.
  HB.instance Definition _ :=
    Nmodule_isPzSemiRing.Build R mulrA mul1r mulr1 mulrDl mulrDr mul0r mulr0.
  HB.instance Definition _ := PzSemiRing_isNonZero.Build R oner_neq0.
HB.end.

Module Nmodule_isSemiRing.
#[deprecated(since="mathcomp 2.4.0",
             note="Use Nmodule_isNzSemiRing.Build instead.")]
Notation Build R := (Nmodule_isNzSemiRing.Build R) (only parsing).
End Nmodule_isSemiRing.

#[deprecated(since="mathcomp 2.4.0",
             note="Use Nmodule_isNzSemiRing instead.")]
Notation Nmodule_isSemiRing R := (Nmodule_isNzSemiRing R) (only parsing).

HB.factory Record isNzSemiRing R of Choice R := {
  zero : R;
  add : R -> R -> R;
  one : R;
  mul : R -> R -> R;
  addrA : associative add;
  addrC : commutative add;
  add0r : left_id zero add;
  mulrA : associative mul;
  mul1r : left_id one mul;
  mulr1 : right_id one mul;
  mulrDl : left_distributive mul add;
  mulrDr : right_distributive mul add;
  mul0r : left_zero zero mul;
  mulr0 : right_zero zero mul;
  oner_neq0 : one != zero
}.

Module isSemiRing.
#[deprecated(since="mathcomp 2.4.0",
             note="Use isNzSemiRing.Build instead.")]
Notation Build R := (isNzSemiRing.Build R) (only parsing).
End isSemiRing.


#[deprecated(since="mathcomp 2.4.0",
             note="Use isNzSemiRing instead.")]
Notation isSemiRing R := (isNzSemiRing R) (only parsing).

HB.builders Context R of isNzSemiRing R.
  HB.instance Definition _ := @isNmodule.Build R
    zero add addrA addrC add0r.
  HB.instance Definition _ := @Nmodule_isNzSemiRing.Build R
    one mul mulrA mul1r mulr1 mulrDl mulrDr mul0r mulr0 oner_neq0.
HB.end.

Module NzSemiRingExports.
Bind Scope ring_scope with NzSemiRing.sort.
End NzSemiRingExports.
HB.export NzSemiRingExports.

Definition exp R x n := iterop n (@mul R) x (@one R).
Arguments exp : simpl never.
Definition comm R x y := @mul R x y = mul y x.
Definition lreg R x := injective (@mul R x).
Definition rreg R x := injective ((@mul R)^~ x).

Local Notation "1" := (@one _) : ring_scope.
Local Notation "n %:R" := (1 *+ n) : ring_scope.
Local Notation "*%R" := (@mul _) : function_scope.
Local Notation "x * y" := (mul x y) : ring_scope.
Local Notation "x ^+ n" := (exp x n) : ring_scope.

Local Notation "\prod_ ( i <- r | P ) F" := (\big[*%R/1]_(i <- r | P) F).
Local Notation "\prod_ ( i | P ) F" := (\big[*%R/1]_(i | P) F).
Local Notation "\prod_ ( i 'in' A ) F" := (\big[*%R/1]_(i in A) F).
Local Notation "\prod_ ( m <= i < n ) F" := (\big[*%R/1%R]_(m <= i < n) F%R).

(* The ``field'' characteristic; the definition, and many of the theorems,   *)
(* has to apply to rings as well; indeed, we need the Frobenius automorphism *)
(* results for a non commutative ring in the proof of Gorenstein 2.6.3.      *)
Definition char (R : pzSemiRingType) : nat_pred :=
  [pred p | prime p & p%:R == 0 :> R].

Local Notation has_char0 L := (char L =i pred0).

(* Converse ring tag. *)
Definition converse R : Type := R.
Local Notation "R ^c" := (converse R) (at level 2, format "R ^c") : type_scope.

Section PzSemiRingTheory.

Variable R : pzSemiRingType.
Implicit Types x y : R.

#[export]
HB.instance Definition _ := Monoid.isLaw.Build R 1 *%R mulrA mul1r mulr1.
#[export]
HB.instance Definition _ := Monoid.isMulLaw.Build R 0 *%R mul0r mulr0.
#[export]
HB.instance Definition _ := Monoid.isAddLaw.Build R *%R +%R mulrDl mulrDr.

Lemma mulr_suml I r P (F : I -> R) x :
  (\sum_(i <- r | P i) F i) * x = \sum_(i <- r | P i) F i * x.
Proof. exact: big_distrl. Qed.

Lemma mulr_sumr I r P (F : I -> R) x :
  x * (\sum_(i <- r | P i) F i) = \sum_(i <- r | P i) x * F i.
Proof. exact: big_distrr. Qed.

Lemma mulrnAl x y n : (x *+ n) * y = (x * y) *+ n.
Proof. by elim: n => [|n IHn]; rewrite ?mul0r // !mulrS mulrDl IHn. Qed.

Lemma mulrnAr x y n : x * (y *+ n) = (x * y) *+ n.
Proof. by elim: n => [|n IHn]; rewrite ?mulr0 // !mulrS mulrDr IHn. Qed.

Lemma mulr_natl x n : n%:R * x = x *+ n.
Proof. by rewrite mulrnAl mul1r. Qed.

Lemma mulr_natr x n : x * n%:R = x *+ n.
Proof. by rewrite mulrnAr mulr1. Qed.

Lemma natrD m n : (m + n)%:R = m%:R + n%:R :> R. Proof. exact: mulrnDr. Qed.
Lemma natr1 n : n%:R + 1 = n.+1%:R :> R. Proof. by rewrite mulrSr. Qed.
Lemma nat1r n : 1 + n%:R = n.+1%:R :> R. Proof. by rewrite mulrS. Qed.

Definition natr_sum := big_morph (natmul 1) natrD (mulr0n 1).

Lemma natrM m n : (m * n)%:R = m%:R * n%:R :> R.
Proof. by rewrite mulrnA mulr_natr. Qed.

Lemma expr0 x : x ^+ 0 = 1. Proof. by []. Qed.
Lemma expr1 x : x ^+ 1 = x. Proof. by []. Qed.
Lemma expr2 x : x ^+ 2 = x * x. Proof. by []. Qed.

Lemma exprS x n : x ^+ n.+1 = x * x ^+ n.
Proof. by case: n => //; rewrite mulr1. Qed.

Lemma expr0n n : 0 ^+ n = (n == 0%N)%:R :> R.
Proof. by case: n => // n; rewrite exprS mul0r. Qed.

Lemma expr1n n : 1 ^+ n = 1 :> R.
Proof. by elim: n => // n IHn; rewrite exprS mul1r. Qed.

Lemma exprD x m n : x ^+ (m + n) = x ^+ m * x ^+ n.
Proof. by elim: m => [|m IHm]; rewrite ?mul1r // !exprS -mulrA -IHm. Qed.

Lemma exprSr x n : x ^+ n.+1 = x ^+ n * x.
Proof. by rewrite -addn1 exprD expr1. Qed.

Lemma expr_sum x (I : Type) (s : seq I) (P : pred I) F :
  x ^+ (\sum_(i <- s | P i) F i) = \prod_(i <- s | P i) x ^+ F i :> R.
Proof. exact: (big_morph _ (exprD _)). Qed.

Lemma commr_sym x y : comm x y -> comm y x. Proof. by []. Qed.
Lemma commr_refl x : comm x x. Proof. by []. Qed.

Lemma commr0 x : comm x 0.
Proof. by rewrite /comm mulr0 mul0r. Qed.

Lemma commr1 x : comm x 1.
Proof. by rewrite /comm mulr1 mul1r. Qed.

Lemma commrD x y z : comm x y -> comm x z -> comm x (y + z).
Proof. by rewrite /comm mulrDl mulrDr => -> ->. Qed.

Lemma commr_sum (I : Type) (s : seq I) (P : pred I) (F : I -> R) x :
  (forall i, P i -> comm x (F i)) -> comm x (\sum_(i <- s | P i) F i).
Proof.
move=> comm_x_F; rewrite /comm mulr_suml mulr_sumr.
by apply: eq_bigr => i /comm_x_F.
Qed.

Lemma commrMn x y n : comm x y -> comm x (y *+ n).
Proof.
rewrite /comm => com_xy.
by elim: n => [|n IHn]; rewrite ?commr0 // mulrS commrD.
Qed.

Lemma commrM x y z : comm x y -> comm x z -> comm x (y * z).
Proof. by move=> com_xy; rewrite /comm mulrA com_xy -!mulrA => ->. Qed.

Lemma commr_prod (I : Type) (s : seq I) (P : pred I) (F : I -> R) x :
  (forall i, P i -> comm x (F i)) -> comm x (\prod_(i <- s | P i) F i).
Proof. exact: (big_ind _ (commr1 x) (@commrM x)). Qed.

Lemma commr_nat x n : comm x n%:R. Proof. exact/commrMn/commr1. Qed.

Lemma commrX x y n : comm x y -> comm x (y ^+ n).
Proof.
rewrite /comm => com_xy.
by elim: n => [|n IHn]; rewrite ?commr1 // exprS commrM.
Qed.

Lemma exprMn_comm x y n : comm x y -> (x * y) ^+ n = x ^+ n * y ^+ n.
Proof.
move=> com_xy; elim: n => /= [|n IHn]; first by rewrite mulr1.
by rewrite !exprS IHn !mulrA; congr (_ * _); rewrite -!mulrA -commrX.
Qed.

Lemma exprMn_n x m n : (x *+ m) ^+ n = x ^+ n *+ (m ^ n) :> R.
Proof.
elim: n => [|n IHn]; first by rewrite mulr1n.
by rewrite exprS IHn mulrnAl mulrnAr -mulrnA exprS -expnSr.
Qed.

Lemma exprM x m n : x ^+ (m * n) = x ^+ m ^+ n.
Proof.
elim: m => [|m IHm]; first by rewrite expr1n.
by rewrite mulSn exprD IHm exprS exprMn_comm //; apply: commrX.
Qed.

Lemma exprAC x m n : (x ^+ m) ^+ n = (x ^+ n) ^+ m.
Proof. by rewrite -!exprM mulnC. Qed.

Lemma expr_mod n x i : x ^+ n = 1 -> x ^+ (i %% n) = x ^+ i.
Proof.
move=> xn1; rewrite {2}(divn_eq i n) exprD mulnC exprM xn1.
by rewrite expr1n mul1r.
Qed.

Lemma expr_dvd n x i : x ^+ n = 1 -> n %| i -> x ^+ i = 1.
Proof.
by move=> xn1 dvd_n_i; rewrite -(expr_mod i xn1) (eqnP dvd_n_i).
Qed.

Lemma natrX n k : (n ^ k)%:R = n%:R ^+ k :> R.
Proof. by rewrite exprMn_n expr1n. Qed.

Lemma mulrI_eq0 x y : lreg x -> (x * y == 0) = (y == 0).
Proof. by move=> reg_x; rewrite -{1}(mulr0 x) (inj_eq reg_x). Qed.

Lemma lreg1 : lreg (1 : R).
Proof. by move=> x y; rewrite !mul1r. Qed.

Lemma lregM x y : lreg x -> lreg y -> lreg (x * y).
Proof. by move=> reg_x reg_y z t; rewrite -!mulrA => /reg_x/reg_y. Qed.

Lemma lregMl (a b: R) : lreg (a * b) -> lreg b.
Proof. by move=> rab c c' eq_bc; apply/rab; rewrite -!mulrA eq_bc. Qed.

Lemma rregMr (a b: R) : rreg (a * b) -> rreg a.
Proof. by move=> rab c c' eq_ca; apply/rab; rewrite !mulrA eq_ca. Qed.

Lemma lregX x n : lreg x -> lreg (x ^+ n).
Proof.
by move=> reg_x; elim: n => [|n]; [apply: lreg1 | rewrite exprS; apply: lregM].
Qed.

Lemma iter_mulr n x y : iter n ( *%R x) y = x ^+ n * y.
Proof. by elim: n => [|n ih]; rewrite ?expr0 ?mul1r //= ih exprS -mulrA. Qed.

Lemma iter_mulr_1 n x : iter n ( *%R x) 1 = x ^+ n.
Proof. by rewrite iter_mulr mulr1. Qed.

Lemma prodr_const (I : finType) (A : pred I) x : \prod_(i in A) x = x ^+ #|A|.
Proof. by rewrite big_const -iteropE. Qed.

Lemma prodr_const_nat n m x : \prod_(n <= i < m) x = x ^+ (m - n).
Proof. by rewrite big_const_nat -iteropE. Qed.

Lemma prodrXr x I r P (F : I -> nat) :
  \prod_(i <- r | P i) x ^+ F i = x ^+ (\sum_(i <- r | P i) F i).
Proof. by rewrite (big_morph _ (exprD _) (erefl _)). Qed.

Lemma prodrM_comm {I : eqType} r (P : pred I) (F G : I -> R) :
    (forall i j, P i -> P j -> comm (F i) (G j)) ->
  \prod_(i <- r | P i) (F i * G i) =
    \prod_(i <- r | P i) F i * \prod_(i <- r | P i) G i.
Proof.
move=> FG; elim: r => [|i r IHr]; rewrite !(big_nil, big_cons) ?mulr1//.
case: ifPn => // Pi; rewrite IHr !mulrA; congr (_ * _); rewrite -!mulrA.
by rewrite commr_prod // => j Pj; apply/commr_sym/FG.
Qed.

Lemma prodrMl_comm {I : finType} (A : pred I) (x : R) F :
    (forall i, A i -> comm x (F i)) ->
  \prod_(i in A) (x * F i) = x ^+ #|A| * \prod_(i in A) F i.
Proof. by move=> xF; rewrite prodrM_comm ?prodr_const// => i j _ /xF. Qed.

Lemma prodrMr_comm {I : finType} (A : pred I) (x : R) F :
    (forall i, A i -> comm x (F i)) ->
  \prod_(i in A) (F i * x) = \prod_(i in A) F i * x ^+ #|A|.
Proof. by move=> xF; rewrite prodrM_comm ?prodr_const// => i j /xF. Qed.

Lemma prodrMn (I : Type) (s : seq I) (P : pred I) (F : I -> R) (g : I -> nat) :
  \prod_(i <- s | P i) (F i *+ g i) =
  \prod_(i <- s | P i) (F i) *+ \prod_(i <- s | P i) g i.
Proof.
by elim/big_rec3: _ => // i y1 y2 y3 _ ->; rewrite mulrnAr mulrnAl -mulrnA.
Qed.

Lemma prodrMn_const n (I : finType) (A : pred I) (F : I -> R) :
  \prod_(i in A) (F i *+ n) = \prod_(i in A) F i *+ n ^ #|A|.
Proof. by rewrite prodrMn prod_nat_const. Qed.

Lemma natr_prod I r P (F : I -> nat) :
  (\prod_(i <- r | P i) F i)%:R = \prod_(i <- r | P i) (F i)%:R :> R.
Proof. exact: (big_morph _ natrM). Qed.

Lemma exprDn_comm x y n (cxy : comm x y) :
  (x + y) ^+ n = \sum_(i < n.+1) (x ^+ (n - i) * y ^+ i) *+ 'C(n, i).
Proof.
elim: n => [|n IHn]; rewrite big_ord_recl mulr1 ?big_ord0 ?addr0 //=.
rewrite exprS {}IHn /= mulrDl !big_distrr /= big_ord_recl mulr1 subn0.
rewrite !big_ord_recr /= !binn !subnn !mul1r !subn0 bin0 !exprS -addrA.
congr (_ + _); rewrite addrA -big_split /=; congr (_ + _).
apply: eq_bigr => i _; rewrite !mulrnAr !mulrA -exprS -subSn ?(valP i) //.
by rewrite subSS (commrX _ (commr_sym cxy)) -mulrA -exprS -mulrnDr.
Qed.

Lemma exprD1n x n : (x + 1) ^+ n = \sum_(i < n.+1) x ^+ i *+ 'C(n, i).
Proof.
rewrite addrC (exprDn_comm n (commr_sym (commr1 x))).
by apply: eq_bigr => i _; rewrite expr1n mul1r.
Qed.

Lemma sqrrD1 x : (x + 1) ^+ 2 = x ^+ 2 + x *+ 2 + 1.
Proof.
rewrite exprD1n !big_ord_recr big_ord0 /= add0r.
by rewrite addrC addrA addrAC.
Qed.

Definition Frobenius_aut p of p \in char R := fun x => x ^+ p.

Section ClosedPredicates.

Variable S : {pred R}.

Definition mulr_2closed := {in S &, forall u v, u * v \in S}.
Definition mulr_closed := 1 \in S /\ mulr_2closed.
Definition semiring_closed := addr_closed S /\ mulr_closed.

Lemma semiring_closedD : semiring_closed -> addr_closed S. Proof. by case. Qed.

Lemma semiring_closedM : semiring_closed -> mulr_closed. Proof. by case. Qed.

End ClosedPredicates.

End PzSemiRingTheory.

Section NzSemiRingTheory.

Variable R : nzSemiRingType.
Implicit Types x y : R.

Lemma oner_eq0 : (1 == 0 :> R) = false. Proof. exact: negbTE oner_neq0. Qed.

Lemma lastr_eq0 (s : seq R) x : x != 0 -> (last x s == 0) = (last 1 s == 0).
Proof. by case: s => [|y s] /negPf // ->; rewrite oner_eq0. Qed.

Lemma lreg_neq0 x : lreg x -> x != 0.
Proof. by move=> reg_x; rewrite -[x]mulr1 mulrI_eq0 ?oner_eq0. Qed.

(* FIXME: Generalize to `pzSemiRingType` once `char` has a sensible
   definition. *)
Section FrobeniusAutomorphism.

Variable p : nat.
Hypothesis charFp : p \in char R.

Lemma charf0 : p%:R = 0 :> R. Proof. by apply/eqP; case/andP: charFp. Qed.
Lemma charf_prime : prime p. Proof. by case/andP: charFp. Qed.
Hint Resolve charf_prime : core.

Lemma mulrn_char x : x *+ p = 0. Proof. by rewrite -mulr_natl charf0 mul0r. Qed.

Lemma natr_mod_char n : (n %% p)%:R = n%:R :> R.
Proof. by rewrite {2}(divn_eq n p) natrD mulrnA mulrn_char add0r. Qed.

Lemma dvdn_charf n : (p %| n)%N = (n%:R == 0 :> R).
Proof.
apply/idP/eqP=> [/dvdnP[n' ->]|n0]; first by rewrite natrM charf0 mulr0.
apply/idPn; rewrite -prime_coprime // => /eqnP pn1.
have [a _ /dvdnP[b]] := Bezoutl n (prime_gt0 charf_prime).
move/(congr1 (fun m => m%:R : R))/eqP.
by rewrite natrD !natrM charf0 n0 !mulr0 pn1 addr0 oner_eq0.
Qed.

Lemma charf_eq : char R =i (p : nat_pred).
Proof.
move=> q; apply/andP/eqP=> [[q_pr q0] | ->]; last by rewrite charf0.
by apply/eqP; rewrite eq_sym -dvdn_prime2 // dvdn_charf.
Qed.

Lemma bin_lt_charf_0 k : 0 < k < p -> 'C(p, k)%:R = 0 :> R.
Proof. by move=> lt0kp; apply/eqP; rewrite -dvdn_charf prime_dvd_bin. Qed.

Local Notation "x ^f" := (Frobenius_aut charFp x).

Lemma Frobenius_autE x : x^f = x ^+ p. Proof. by []. Qed.
Local Notation fE := Frobenius_autE.

Lemma Frobenius_aut0 : 0^f = 0.
Proof. by rewrite fE -(prednK (prime_gt0 charf_prime)) exprS mul0r. Qed.

Lemma Frobenius_aut1 : 1^f = 1.
Proof. by rewrite fE expr1n. Qed.

Lemma Frobenius_autD_comm x y (cxy : comm x y) : (x + y)^f = x^f + y^f.
Proof.
have defp := prednK (prime_gt0 charf_prime).
rewrite !fE exprDn_comm // big_ord_recr subnn -defp big_ord_recl /= defp.
rewrite subn0 mulr1 mul1r bin0 binn big1 ?addr0 // => i _.
by rewrite -mulr_natl bin_lt_charf_0 ?mul0r //= -{2}defp ltnS (valP i).
Qed.

Lemma Frobenius_autMn x n : (x *+ n)^f = x^f *+ n.
Proof.
elim: n => [|n IHn]; first exact: Frobenius_aut0.
by rewrite !mulrS Frobenius_autD_comm ?IHn //; apply: commrMn.
Qed.

Lemma Frobenius_aut_nat n : (n%:R)^f = n%:R.
Proof. by rewrite Frobenius_autMn Frobenius_aut1. Qed.

Lemma Frobenius_autM_comm x y : comm x y -> (x * y)^f = x^f * y^f.
Proof. exact: exprMn_comm. Qed.

Lemma Frobenius_autX x n : (x ^+ n)^f = x^f ^+ n.
Proof. by rewrite !fE -!exprM mulnC. Qed.

End FrobeniusAutomorphism.

Section Char2.

Hypothesis charR2 : 2 \in char R.

Lemma addrr_char2 x : x + x = 0. Proof. by rewrite -mulr2n mulrn_char. Qed.

End Char2.

End NzSemiRingTheory.

#[short(type="pzRingType")]
HB.structure Definition PzRing := { R of PzSemiRing R & Zmodule R }.

HB.factory Record Zmodule_isPzRing R of Zmodule R := {
  one : R;
  mul : R -> R -> R;
  mulrA : associative mul;
  mul1r : left_id one mul;
  mulr1 : right_id one mul;
  mulrDl : left_distributive mul +%R;
  mulrDr : right_distributive mul +%R;
}.

HB.builders Context R of Zmodule_isPzRing R.
  Local Notation "1" := one.
  Local Notation "x * y" := (mul x y).
  Lemma mul0r : @left_zero R R 0 mul.
  Proof. by move=> x; apply: (addIr (1 * x)); rewrite -mulrDl !add0r mul1r. Qed.
  Lemma mulr0 : @right_zero R R 0 mul.
  Proof. by move=> x; apply: (addIr (x * 1)); rewrite -mulrDr !add0r mulr1. Qed.
  HB.instance Definition _ := Nmodule_isPzSemiRing.Build R
    mulrA mul1r mulr1 mulrDl mulrDr mul0r mulr0.
HB.end.

HB.factory Record isPzRing R of Choice R := {
  zero : R;
  opp : R -> R;
  add : R -> R -> R;
  one : R;
  mul : R -> R -> R;
  addrA : associative add;
  addrC : commutative add;
  add0r : left_id zero add;
  addNr : left_inverse zero opp add;
  mulrA : associative mul;
  mul1r : left_id one mul;
  mulr1 : right_id one mul;
  mulrDl : left_distributive mul add;
  mulrDr : right_distributive mul add;
}.

HB.builders Context R of isPzRing R.
  HB.instance Definition _ := @isZmodule.Build R
    zero opp add addrA addrC add0r addNr.
  HB.instance Definition _ := @Zmodule_isPzRing.Build R
    one mul mulrA mul1r mulr1 mulrDl mulrDr.
HB.end.

Module PzRingExports.
Bind Scope ring_scope with PzRing.sort.
End PzRingExports.
HB.export PzRingExports.

#[short(type="nzRingType")]
HB.structure Definition NzRing := { R of NzSemiRing R & Zmodule R }.

#[deprecated(since="mathcomp 2.4.0",
             note="Use NzRing instead.")]
Notation Ring R := (NzRing R) (only parsing).

Module Ring.
#[deprecated(since="mathcomp 2.4.0",
             note="Use NzRing.sort instead.")]
Notation sort := (NzRing.sort) (only parsing).
#[deprecated(since="mathcomp 2.4.0",
             note="Use NzRing.on instead.")]
Notation on R := (NzRing.on R) (only parsing).
#[deprecated(since="mathcomp 2.4.0",
             note="Use NzRing.copy instead.")]
Notation copy T U := (NzRing.copy T U) (only parsing).
End Ring.

HB.factory Record Zmodule_isNzRing R of Zmodule R := {
  one : R;
  mul : R -> R -> R;
  mulrA : associative mul;
  mul1r : left_id one mul;
  mulr1 : right_id one mul;
  mulrDl : left_distributive mul +%R;
  mulrDr : right_distributive mul +%R;
  oner_neq0 : one != 0
}.

Module Zmodule_isRing.
#[deprecated(since="mathcomp 2.4.0",
             note="Use Zmodule_isNzRing.Build instead.")]
Notation Build R := (Zmodule_isNzRing.Build R) (only parsing).
End Zmodule_isRing.

#[deprecated(since="mathcomp 2.4.0",
             note="Use Zmodule_isNzRing instead.")]
Notation Zmodule_isRing R := (Zmodule_isNzRing R) (only parsing).

HB.builders Context R of Zmodule_isNzRing R.
  HB.instance Definition _ := Zmodule_isPzRing.Build R 
    mulrA mul1r mulr1 mulrDl mulrDr.
  HB.instance Definition _ := PzSemiRing_isNonZero.Build R oner_neq0.
HB.end.

HB.factory Record isNzRing R of Choice R := {
  zero : R;
  opp : R -> R;
  add : R -> R -> R;
  one : R;
  mul : R -> R -> R;
  addrA : associative add;
  addrC : commutative add;
  add0r : left_id zero add;
  addNr : left_inverse zero opp add;
  mulrA : associative mul;
  mul1r : left_id one mul;
  mulr1 : right_id one mul;
  mulrDl : left_distributive mul add;
  mulrDr : right_distributive mul add;
  oner_neq0 : one != zero
}.

Module isRing.
#[deprecated(since="mathcomp 2.4.0",
             note="Use isNzRing.Build instead.")]
Notation Build R := (isNzRing.Build R) (only parsing).
End isRing.

#[deprecated(since="mathcomp 2.4.0",
             note="Use isNzRing instead.")]
Notation isRing R := (isNzRing R) (only parsing).

HB.builders Context R of isNzRing R.
  HB.instance Definition _ := @isZmodule.Build R
    zero opp add addrA addrC add0r addNr.
  HB.instance Definition _ := @Zmodule_isNzRing.Build R
    one mul mulrA mul1r mulr1 mulrDl mulrDr oner_neq0.
HB.end.

Module NzRingExports.
Bind Scope ring_scope with NzRing.sort.
End NzRingExports.
HB.export NzRingExports.

Notation sign R b := (exp (- @one R) (nat_of_bool b)) (only parsing).

Local Notation "- 1" := (- (1)) : ring_scope.

Section PzRingTheory.

Variable R : pzRingType.
Implicit Types x y : R.

Lemma mulrN x y : x * (- y) = - (x * y).
Proof. by apply: (addrI (x * y)); rewrite -mulrDr !subrr mulr0. Qed.
Lemma mulNr x y : (- x) * y = - (x * y).
Proof. by apply: (addrI (x * y)); rewrite -mulrDl !subrr mul0r. Qed.
Lemma mulrNN x y : (- x) * (- y) = x * y.
Proof. by rewrite mulrN mulNr opprK. Qed.
Lemma mulN1r x : -1 * x = - x.
Proof. by rewrite mulNr mul1r. Qed.
Lemma mulrN1 x : x * -1 = - x.
Proof. by rewrite mulrN mulr1. Qed.

Lemma mulrBl x y z : (y - z) * x = y * x - z * x.
Proof. by rewrite mulrDl mulNr. Qed.

Lemma mulrBr x y z : x * (y - z) = x * y - x * z.
Proof. by rewrite mulrDr mulrN. Qed.

Lemma natrB m n : n <= m -> (m - n)%:R = m%:R - n%:R :> R.
Proof. exact: mulrnBr. Qed.

Lemma commrN x y : comm x y -> comm x (- y).
Proof. by move=> com_xy; rewrite /comm mulrN com_xy mulNr. Qed.

Lemma commrN1 x : comm x (-1). Proof. exact/commrN/commr1. Qed.

Lemma commrB x y z : comm x y -> comm x z -> comm x (y - z).
Proof. by move=> com_xy com_xz; apply: commrD => //; apply: commrN. Qed.

Lemma commr_sign x n : comm x ((-1) ^+ n).
Proof. exact: (commrX n (commrN1 x)). Qed.

Lemma signr_odd n : (-1) ^+ (odd n) = (-1) ^+ n :> R.
Proof.
elim: n => //= n IHn; rewrite exprS -{}IHn.
by case/odd: n; rewrite !mulN1r ?opprK.
Qed.

Lemma mulr_sign (b : bool) x : (-1) ^+ b * x = (if b then - x else x).
Proof. by case: b; rewrite ?mulNr mul1r. Qed.

Lemma signr_addb b1 b2 : (-1) ^+ (b1 (+) b2) = (-1) ^+ b1 * (-1) ^+ b2 :> R.
Proof. by rewrite mulr_sign; case: b1 b2 => [] []; rewrite ?opprK. Qed.

Lemma signrE (b : bool) : (-1) ^+ b = 1 - b.*2%:R :> R.
Proof. by case: b; rewrite ?subr0 // opprD addNKr. Qed.

Lemma signrN b : (-1) ^+ (~~ b) = - (-1) ^+ b :> R.
Proof. by case: b; rewrite ?opprK. Qed.

Lemma mulr_signM (b1 b2 : bool) x1 x2 :
  ((-1) ^+ b1 * x1) * ((-1) ^+ b2 * x2) = (-1) ^+ (b1 (+) b2) * (x1 * x2).
Proof.
by rewrite signr_addb -!mulrA; congr (_ * _); rewrite !mulrA commr_sign.
Qed.

Lemma exprNn x n : (- x) ^+ n = (-1) ^+ n * x ^+ n :> R.
Proof. by rewrite -mulN1r exprMn_comm // /comm mulN1r mulrN mulr1. Qed.

Lemma sqrrN x : (- x) ^+ 2 = x ^+ 2. Proof. exact: mulrNN. Qed.

Lemma sqrr_sign n : ((-1) ^+ n) ^+ 2 = 1 :> R.
Proof. by rewrite exprAC sqrrN !expr1n. Qed.

Lemma signrMK n : @involutive R ( *%R ((-1) ^+ n)).
Proof. by move=> x; rewrite mulrA -expr2 sqrr_sign mul1r. Qed.

Lemma mulrI0_lreg x : (forall y, x * y = 0 -> y = 0) -> lreg x.
Proof.
move=> reg_x y z eq_xy_xz; apply/eqP; rewrite -subr_eq0 [y - z]reg_x //.
by rewrite mulrBr eq_xy_xz subrr.
Qed.

Lemma lregN x : lreg x -> lreg (- x).
Proof. by move=> reg_x y z; rewrite !mulNr => /oppr_inj/reg_x. Qed.

Lemma lreg_sign n : lreg ((-1) ^+ n : R). Proof. exact/lregX/lregN/lreg1. Qed.

Lemma prodrN (I : finType) (A : pred I) (F : I -> R) :
  \prod_(i in A) - F i = (- 1) ^+ #|A| * \prod_(i in A) F i.
Proof.
rewrite -sum1_card; elim/big_rec3: _ => [|i x n _ _ ->]; first by rewrite mulr1.
by rewrite exprS !mulrA mulN1r !mulNr commrX //; apply: commrN1.
Qed.

Lemma exprBn_comm x y n (cxy : comm x y) :
  (x - y) ^+ n =
    \sum_(i < n.+1) ((-1) ^+ i * x ^+ (n - i) * y ^+ i) *+ 'C(n, i).
Proof.
rewrite exprDn_comm; last exact: commrN.
by apply: eq_bigr => i _; congr (_ *+ _); rewrite -commr_sign -mulrA -exprNn.
Qed.

Lemma subrXX_comm x y n (cxy : comm x y) :
  x ^+ n - y ^+ n = (x - y) * (\sum_(i < n) x ^+ (n.-1 - i) * y ^+ i).
Proof.
case: n => [|n]; first by rewrite big_ord0 mulr0 subrr.
rewrite mulrBl !big_distrr big_ord_recl big_ord_recr /= subnn mulr1 mul1r.
rewrite subn0 -!exprS opprD -!addrA; congr (_ + _); rewrite addrA -sumrB.
rewrite big1 ?add0r // => i _; rewrite !mulrA -exprS -subSn ?(valP i) //.
by rewrite subSS (commrX _ (commr_sym cxy)) -mulrA -exprS subrr.
Qed.

Lemma subrX1 x n : x ^+ n - 1 = (x - 1) * (\sum_(i < n) x ^+ i).
Proof.
rewrite -!(opprB 1) mulNr -{1}(expr1n _ n).
rewrite (subrXX_comm _ (commr_sym (commr1 x))); congr (- (_ * _)).
by apply: eq_bigr => i _; rewrite expr1n mul1r.
Qed.

Lemma sqrrB1 x : (x - 1) ^+ 2 = x ^+ 2 - x *+ 2 + 1.
Proof. by rewrite -sqrrN opprB addrC sqrrD1 sqrrN mulNrn. Qed.

Lemma subr_sqr_1 x : x ^+ 2 - 1 = (x - 1) * (x + 1).
Proof. by rewrite subrX1 !big_ord_recr big_ord0 /= addrAC add0r. Qed.

Section ClosedPredicates.

Variable S : {pred R}.

Definition smulr_closed := -1 \in S /\ mulr_2closed S.
Definition subring_closed := [/\ 1 \in S, subr_2closed S & mulr_2closed S].

Lemma smulr_closedM : smulr_closed -> mulr_closed S.
Proof. by case=> SN1 SM; split=> //; rewrite -[1]mulr1 -mulrNN SM. Qed.

Lemma smulr_closedN : smulr_closed -> oppr_closed S.
Proof. by case=> SN1 SM x Sx; rewrite -mulN1r SM. Qed.

Lemma subring_closedB : subring_closed -> zmod_closed S.
Proof. by case=> S1 SB _; split; rewrite // -(subrr 1) SB. Qed.

Lemma subring_closedM : subring_closed -> smulr_closed.
Proof.
by case=> S1 SB SM; split; rewrite ?(zmod_closedN (subring_closedB _)).
Qed.

Lemma subring_closed_semi : subring_closed -> semiring_closed S.
Proof.
by move=> ringS; split; [apply/zmod_closedD/subring_closedB | case: ringS].
Qed.

End ClosedPredicates.

End PzRingTheory.

Section NzRingTheory.

Variable R : nzRingType.
Implicit Types x y : R.

Lemma signr_eq0 n : ((-1) ^+ n == 0 :> R) = false.
Proof. by rewrite -signr_odd; case: odd; rewrite ?oppr_eq0 oner_eq0. Qed.

(* FIXME: Generalize to `pzSemiRingType` once `char` has a sensible
   definition. *)
Section FrobeniusAutomorphism.

Variable p : nat.
Hypothesis charFp : p \in char R.

Hint Resolve charf_prime : core.

Local Notation "x ^f" := (Frobenius_aut charFp x).

Lemma Frobenius_autN x : (- x)^f = - x^f.
Proof.
apply/eqP; rewrite -subr_eq0 opprK addrC.
by rewrite -(Frobenius_autD_comm _ (commrN _)) // subrr Frobenius_aut0.
Qed.

Lemma Frobenius_autB_comm x y : comm x y -> (x - y)^f = x^f - y^f.
Proof.
by move/commrN/Frobenius_autD_comm->; rewrite Frobenius_autN.
Qed.

End FrobeniusAutomorphism.

Lemma exprNn_char x n : (char R).-nat n -> (- x) ^+ n = - (x ^+ n).
Proof.
pose p := pdiv n; have [|n_gt1 charRn] := leqP n 1; first by case: (n) => [|[]].
have charRp: p \in char R by rewrite (pnatPpi charRn) // pi_pdiv.
have /p_natP[e ->]: p.-nat n by rewrite -(eq_pnat _ (charf_eq charRp)).
elim: e => // e IHe; rewrite expnSr !exprM {}IHe.
by rewrite -Frobenius_autE Frobenius_autN.
Qed.

Section Char2.

Hypothesis charR2 : 2 \in char R.

Lemma oppr_char2 x : - x = x.
Proof. by apply/esym/eqP; rewrite -addr_eq0 addrr_char2. Qed.

Lemma subr_char2 x y : x - y = x + y. Proof. by rewrite oppr_char2. Qed.

Lemma addrK_char2 x : involutive (+%R^~ x).
Proof. by move=> y; rewrite /= -subr_char2 addrK. Qed.

Lemma addKr_char2 x : involutive (+%R x).
Proof. by move=> y; rewrite -{1}[x]oppr_char2 addKr. Qed.

End Char2.

End NzRingTheory.

Section ConverseRing.
#[export]
HB.instance Definition _ (T : eqType) := Equality.on T^c.
#[export]
HB.instance Definition _ (T : choiceType) := Choice.on T^c.
#[export]
HB.instance Definition _ (U : nmodType) := Nmodule.on U^c.
#[export]
HB.instance Definition _ (U : zmodType) := Zmodule.on U^c.
#[export]
HB.instance Definition _ (R : pzSemiRingType) :=
  let mul' (x y : R) := y * x in
  let mulrA' x y z := esym (mulrA z y x) in
  let mulrDl' x y z := mulrDr z x y in
  let mulrDr' x y z := mulrDl y z x in
  Nmodule_isPzSemiRing.Build R^c
    mulrA' mulr1 mul1r mulrDl' mulrDr' mulr0 mul0r.
#[export]
HB.instance Definition _ (R : pzRingType) := PzSemiRing.on R^c.
#[export]
HB.instance Definition _ (R : nzSemiRingType) :=
  PzSemiRing_isNonZero.Build R^c oner_neq0.
#[export]
HB.instance Definition _ (R : nzRingType) := NzSemiRing.on R^c.
End ConverseRing.

Lemma rev_prodr (R : pzSemiRingType)
  (I : Type) (r : seq I) (P : pred I) (E : I -> R) :
  \prod_(i <- r | P i) (E i : R^c) = \prod_(i <- rev r | P i) E i.
Proof. by rewrite rev_big_rev. Qed.

Section SemiRightRegular.

Variable R : pzSemiRingType.
Implicit Types x y : R.

Lemma mulIr_eq0 x y : rreg x -> (y * x == 0) = (y == 0).
Proof. exact: (@mulrI_eq0 R^c). Qed.

Lemma rreg1 : rreg (1 : R).
Proof. exact: (@lreg1 R^c). Qed.

Lemma rregM x y : rreg x -> rreg y -> rreg (x * y).
Proof. by move=> reg_x reg_y; apply: (@lregM R^c). Qed.

Lemma revrX x n : (x : R^c) ^+ n = (x : R) ^+ n.
Proof. by elim: n => // n IHn; rewrite exprS exprSr IHn. Qed.

Lemma rregX x n : rreg x -> rreg (x ^+ n).
Proof. by move/(@lregX R^c x n); rewrite revrX. Qed.

End SemiRightRegular.

Lemma rreg_neq0 (R : nzSemiRingType) (x : R) : rreg x -> x != 0.
Proof. exact: (@lreg_neq0 R^c). Qed.

Section RightRegular.

Variable R : pzRingType.
Implicit Types x y : R.

Lemma mulIr0_rreg x : (forall y, y * x = 0 -> y = 0) -> rreg x.
Proof. exact: (@mulrI0_lreg R^c). Qed.

Lemma rregN x : rreg x -> rreg (- x). Proof. exact: (@lregN R^c). Qed.

End RightRegular.

HB.mixin Record Zmodule_isLmodule (R : pzRingType) V of Zmodule V := {
  scale : R -> V -> V;
  scalerA : forall a b v, scale a (scale b v) = scale (a * b) v;
  scale1r : left_id 1 scale;
  scalerDr : right_distributive scale +%R;
  scalerDl : forall v, {morph scale^~ v: a b / a + b}
}.
#[short(type="lmodType")]
HB.structure Definition Lmodule (R : pzRingType) :=
  {M of Zmodule M & Zmodule_isLmodule R M}.

(* FIXME: see #1126 and #1127 *)
Arguments scalerA [R s] (a b)%ring_scope v.

Module LmodExports.
Bind Scope ring_scope with Lmodule.sort.
End LmodExports.
HB.export LmodExports.

Local Notation "*:%R" := (@scale _ _) : function_scope.
Local Notation "a *: v" := (scale a v) : ring_scope.

Section LmoduleTheory.

Variables (R : pzRingType) (V : lmodType R).
Implicit Types (a b c : R) (u v : V).

Lemma scale0r v : 0 *: v = 0.
Proof. by apply: (addIr (1 *: v)); rewrite -scalerDl !add0r. Qed.

Lemma scaler0 a : a *: 0 = 0 :> V.
Proof. by rewrite -{1}(scale0r 0) scalerA mulr0 scale0r. Qed.

Lemma scaleNr a v : - a *: v = - (a *: v).
Proof. by apply: (addIr (a *: v)); rewrite -scalerDl !addNr scale0r. Qed.

Lemma scaleN1r v : (- 1) *: v = - v.
Proof. by rewrite scaleNr scale1r. Qed.

Lemma scalerN a v : a *: (- v) = - (a *: v).
Proof. by apply: (addIr (a *: v)); rewrite -scalerDr !addNr scaler0. Qed.

Lemma scalerBl a b v : (a - b) *: v = a *: v - b *: v.
Proof. by rewrite scalerDl scaleNr. Qed.

Lemma scalerBr a u v : a *: (u - v) = a *: u - a *: v.
Proof. by rewrite scalerDr scalerN. Qed.

Lemma scaler_nat n v : n%:R *: v = v *+ n.
Proof.
elim: n => /= [|n]; first by rewrite scale0r.
by rewrite !mulrS scalerDl ?scale1r => ->.
Qed.

Lemma scaler_sign (b : bool) v: (-1) ^+ b *: v = (if b then - v else v).
Proof. by case: b; rewrite ?scaleNr scale1r. Qed.

Lemma signrZK n : @involutive V ( *:%R ((-1) ^+ n)).
Proof. by move=> u; rewrite scalerA -expr2 sqrr_sign scale1r. Qed.

Lemma scalerMnl a v n : a *: v *+ n = (a *+ n) *: v.
Proof.
elim: n => [|n IHn]; first by rewrite !mulr0n scale0r.
by rewrite !mulrSr IHn scalerDl.
Qed.

Lemma scalerMnr a v n : a *: v *+ n = a *: (v *+ n).
Proof.
elim: n => [|n IHn]; first by rewrite !mulr0n scaler0.
by rewrite !mulrSr IHn scalerDr.
Qed.

Lemma scaler_suml v I r (P : pred I) F :
  (\sum_(i <- r | P i) F i) *: v = \sum_(i <- r | P i) F i *: v.
Proof. exact: (big_morph _ (scalerDl v) (scale0r v)). Qed.

Lemma scaler_sumr a I r (P : pred I) (F : I -> V) :
  a *: (\sum_(i <- r | P i) F i) = \sum_(i <- r | P i) a *: F i.
Proof. exact: big_endo (scalerDr a) (scaler0 a) I r P F. Qed.

Section ClosedPredicates.

Variable S : {pred V}.

Definition scaler_closed := forall a, {in S, forall v, a *: v \in S}.
Definition linear_closed := forall a, {in S &, forall u v, a *: u + v \in S}.
Definition submod_closed := 0 \in S /\ linear_closed.

Lemma linear_closedB : linear_closed -> subr_2closed S.
Proof. by move=> Slin u v Su Sv; rewrite addrC -scaleN1r Slin. Qed.

Lemma submod_closedB : submod_closed -> zmod_closed S.
Proof. by case=> S0 /linear_closedB. Qed.

Lemma submod_closedZ : submod_closed -> scaler_closed.
Proof. by case=> S0 Slin a v Sv; rewrite -[a *: v]addr0 Slin. Qed.

End ClosedPredicates.

End LmoduleTheory.

(* TOTHINK: Can I change `NzRing` to `PzRing`? *)
HB.mixin Record Lmodule_isLalgebra R V of NzRing V & Lmodule R V := {
  scalerAl : forall (a : R) (u v : V), a *: (u * v) = (a *: u) * v
}.
#[short(type="lalgType")]
HB.structure Definition Lalgebra R :=
  {A of Lmodule_isLalgebra R A & NzRing A & Lmodule R A}.

Module LalgExports.
Bind Scope ring_scope with Lalgebra.sort.
End LalgExports.
HB.export LalgExports.

(* Scalar injection (see the definition of in_alg A below). *)
Local Notation "k %:A" := (k *: 1) : ring_scope.

(* Regular ring algebra tag. *)
Definition regular R : Type := R.
Local Notation "R ^o" := (regular R) (at level 2, format "R ^o") : type_scope.

Section RegularAlgebra.
#[export]
HB.instance Definition _ (V : nmodType) := Nmodule.on V^o.
#[export]
HB.instance Definition _ (V : zmodType) := Zmodule.on V^o.
#[export]
HB.instance Definition _ (R : pzSemiRingType) := PzSemiRing.on R^o.
#[export]
HB.instance Definition _ (R : pzRingType) := PzRing.on R^o.
#[export]
HB.instance Definition _ (R : pzRingType) :=
  @Zmodule_isLmodule.Build R R^o
    (@mul R) (@mulrA R) (@mul1r R) (@mulrDr R) (fun v a b => mulrDl a b v).
#[export]
HB.instance Definition _ (R : nzSemiRingType) := NzSemiRing.on R^o.
#[export]
HB.instance Definition _ (R : nzRingType) := NzRing.on R^o.
#[export]
HB.instance Definition _ (R : nzRingType) :=
  Lmodule_isLalgebra.Build R R^o mulrA.
End RegularAlgebra.

Section LalgebraTheory.

Variables (R : pzRingType) (A : lalgType R).
Implicit Types x y : A.

Lemma mulr_algl a x : (a *: 1) * x = a *: x.
Proof. by rewrite -scalerAl mul1r. Qed.

Section ClosedPredicates.

Variable S : {pred A}.

Definition subalg_closed := [/\ 1 \in S, linear_closed S & mulr_2closed S].

Lemma subalg_closedZ : subalg_closed -> submod_closed S.
Proof. by case=> S1 Slin _; split; rewrite // -(subrr 1) linear_closedB. Qed.

Lemma subalg_closedBM : subalg_closed -> subring_closed S.
Proof. by case=> S1 Slin SM; split=> //; apply: linear_closedB. Qed.

End ClosedPredicates.

End LalgebraTheory.

(* Morphism hierarchy. *)

(* Lifted multiplication. *)
Section LiftedSemiRing.
Variables (R : pzSemiRingType) (T : Type).
Implicit Type f : T -> R.
Definition mull_fun a f x := a * f x.
Definition mulr_fun a f x := f x * a.
Definition mul_fun f g x := f x * g x.
End LiftedSemiRing.

(* Lifted linear operations. *)
Section LiftedScale.
Variables (R : pzRingType) (U : Type) (V : lmodType R) (A : lalgType R).
Definition scale_fun a (f : U -> V) x := a *: f x.
Definition in_alg k : A := k%:A.
End LiftedScale.

Local Notation "\0" := (null_fun _) : function_scope.
Local Notation "f \+ g" := (add_fun f g) : function_scope.
Local Notation "f \- g" := (sub_fun f g) : function_scope.
Local Notation "\- f" := (opp_fun f) : function_scope.
Local Notation "a \*: f" := (scale_fun a f) : function_scope.
Local Notation "x \*o f" := (mull_fun x f) : function_scope.
Local Notation "x \o* f" := (mulr_fun x f) : function_scope.
Local Notation "f \* g" := (mul_fun f g) : function_scope.

Arguments in_alg  {_} A _ /.
Arguments mull_fun {_ _}  a f _ /.
Arguments mulr_fun {_ _} a f _ /.
Arguments scale_fun {_ _ _} a f _ /.
Arguments mul_fun {_ _} f g _ /.

Section AdditiveTheory.

Section SemiRingProperties.

Variables (R S : pzSemiRingType) (f : {additive R -> S}).

Lemma raddfMnat n x : f (n%:R * x) = n%:R * f x.
Proof. by rewrite !mulr_natl raddfMn. Qed.

End SemiRingProperties.

Section MulFun.

Variables (R : pzSemiRingType) (U : nmodType) (a : R) (f : {additive U -> R}).

Fact mull_fun_is_semi_additive : semi_additive (a \*o f).
Proof. by split=> [|x y]; rewrite /= ?raddf0 ?mulr0// raddfD mulrDr. Qed.
#[export]
HB.instance Definition _ := isSemiAdditive.Build U R (a \*o f)
  mull_fun_is_semi_additive.

Fact mulr_fun_is_semi_additive : semi_additive (a \o* f).
Proof. by split=> [|x y]; rewrite /= ?raddf0 ?mul0r// raddfD mulrDl. Qed.
#[export]
HB.instance Definition _ := isSemiAdditive.Build U R (a \o* f)
  mulr_fun_is_semi_additive.

End MulFun.

Section Properties.

Variables (U V : zmodType) (f : {additive U -> V}).

Lemma raddfN : {morph f : x / - x}. Proof. exact: raddfN. Qed.
Lemma raddfB : {morph f : x y / x - y}. Proof. exact: raddfB. Qed.

Lemma raddf_inj : (forall x, f x = 0 -> x = 0) -> injective f.
Proof. exact: raddf_inj. Qed.

Lemma raddfMNn n : {morph f : x / x *- n}. Proof. exact: raddfMNn. Qed.

End Properties.

Section RingProperties.

Variables (R S : pzRingType) (f : {additive R -> S}).

Lemma raddfMsign n x : f ((-1) ^+ n * x) = (-1) ^+ n * f x.
Proof. by rewrite !(mulr_sign, =^~ signr_odd) (fun_if f) raddfN. Qed.

Variables (U : lmodType R) (V : lmodType S) (h : {additive U -> V}).

Lemma raddfZnat n u : h (n%:R *: u) = n%:R *: h u.
Proof. by rewrite !scaler_nat raddfMn. Qed.

Lemma raddfZsign n u : h ((-1) ^+ n *: u) = (-1) ^+ n *: h u.
Proof. by rewrite !(scaler_sign, =^~ signr_odd) (fun_if h) raddfN. Qed.

End RingProperties.

Section ScaleFun.

Variables (R : pzRingType) (U : zmodType) (V : lmodType R).
Variables (a : R) (f : {additive U -> V}).

#[export]
HB.instance Definition _ := isAdditive.Build V V ( *:%R a) (@scalerBr R V a).
#[export]
HB.instance Definition _ := Additive.copy (a \*: f) (f \; *:%R a).

End ScaleFun.

End AdditiveTheory.

Definition multiplicative (R S : pzSemiRingType) (f : R -> S) : Prop :=
  {morph f : x y / x * y}%R * (f 1 = 1).

HB.mixin Record isMultiplicative (R S : pzSemiRingType) (f : R -> S) := {
  rmorphism_subproof : multiplicative f
}.

HB.structure Definition RMorphism (R S : pzSemiRingType) :=
  {f of @Additive R S f & isMultiplicative R S f}.
(* FIXME: remove the @ once
   https://github.com/math-comp/hierarchy-builder/issues/319 is fixed *)

Module RMorphismExports.
Notation "{ 'rmorphism' U -> V }" := (RMorphism.type U%type V%type)
  : type_scope.
End RMorphismExports.
HB.export RMorphismExports.

Section RmorphismTheory.

Section Properties.

Variables (R S : pzSemiRingType) (f : {rmorphism R -> S}).

Lemma rmorph0 : f 0 = 0. Proof. exact: raddf0. Qed.
Lemma rmorphD : {morph f : x y / x + y}. Proof. exact: raddfD. Qed.
Lemma rmorphMn n : {morph f : x / x *+ n}. Proof. exact: raddfMn. Qed.
Lemma rmorph_sum I r (P : pred I) E :
  f (\sum_(i <- r | P i) E i) = \sum_(i <- r | P i) f (E i).
Proof. exact: raddf_sum. Qed.

Lemma rmorphismMP : multiplicative f. Proof. exact: rmorphism_subproof. Qed.
Lemma rmorph1 : f 1 = 1. Proof. by case: rmorphismMP. Qed.
Lemma rmorphM : {morph f: x y  / x * y}. Proof. by case: rmorphismMP. Qed.

Lemma rmorph_prod I r (P : pred I) E :
  f (\prod_(i <- r | P i) E i) = \prod_(i <- r | P i) f (E i).
Proof. exact: (big_morph f rmorphM rmorph1). Qed.

Lemma rmorphXn n : {morph f : x / x ^+ n}.
Proof. by elim: n => [|n IHn] x; rewrite ?rmorph1 // !exprS rmorphM IHn. Qed.

Lemma rmorph_nat n : f n%:R = n%:R. Proof. by rewrite rmorphMn rmorph1. Qed.

Lemma rmorph_char p : p \in char R -> p \in char S.
Proof. by rewrite !inE -rmorph_nat => /andP[-> /= /eqP->]; rewrite rmorph0. Qed.

Lemma rmorph_eq_nat x n : injective f -> (f x == n%:R) = (x == n%:R).
Proof. by move/inj_eq <-; rewrite rmorph_nat. Qed.

Lemma rmorph_eq1 x : injective f -> (f x == 1) = (x == 1).
Proof. exact: rmorph_eq_nat 1%N. Qed.

Lemma can2_rmorphism f' : cancel f f' -> cancel f' f -> multiplicative f'.
Proof.
move=> fK f'K.
by split=> [x y|]; apply: (canLR fK); rewrite /= (rmorphM, rmorph1) ?f'K.
Qed.

End Properties.

Section Projections.

Variables (R S T : pzSemiRingType).
Variables (f : {rmorphism S -> T}) (g : {rmorphism R -> S}).

Fact idfun_is_multiplicative : multiplicative (@idfun R).
Proof. by []. Qed.
#[export]
HB.instance Definition _ := isMultiplicative.Build R R idfun
  idfun_is_multiplicative.

Fact comp_is_multiplicative : multiplicative (f \o g).
Proof. by split=> [x y|] /=; rewrite ?rmorph1 ?rmorphM. Qed.
#[export]
HB.instance Definition _ := isMultiplicative.Build R T (f \o g)
  comp_is_multiplicative.

End Projections.

Section Properties.

Variables (R S : pzRingType) (f : {rmorphism R -> S}).

Lemma rmorphN : {morph f : x / - x}. Proof. exact: raddfN. Qed.
Lemma rmorphB : {morph f: x y / x - y}. Proof. exact: raddfB. Qed.
Lemma rmorphMNn n : {morph f : x / x *- n}. Proof. exact: raddfMNn. Qed.
Lemma rmorphMsign n : {morph f : x / (- 1) ^+ n * x}.
Proof. exact: raddfMsign. Qed.

Lemma rmorphN1 : f (- 1) = (- 1). Proof. by rewrite rmorphN rmorph1. Qed.

Lemma rmorph_sign n : f ((- 1) ^+ n) = (- 1) ^+ n.
Proof. by rewrite rmorphXn /= rmorphN1. Qed.

End Properties.

Section InAlgebra.

Variables (R : pzRingType) (A : lalgType R).

Fact in_alg_is_additive : additive (in_alg A).
Proof. move=> x y; exact: scalerBl. Qed.
#[export]
HB.instance Definition _ := isAdditive.Build R A (in_alg A) in_alg_is_additive.

Fact in_alg_is_rmorphism : multiplicative (in_alg A).
Proof.
split=> [x y|] /=; last exact/scale1r.
by rewrite -scalerAl mul1r scalerA.
Qed.
#[export]
HB.instance Definition _ := isMultiplicative.Build R A (in_alg A)
  in_alg_is_rmorphism.

Lemma in_algE a : in_alg A a = a%:A. Proof. by []. Qed.

End InAlgebra.

End RmorphismTheory.

Module Scale.

HB.mixin Record isLaw (R : pzRingType) (V : zmodType) (op : R -> V -> V) := {
  N1op_subproof : op (-1) =1 -%R;
  op_additive_subproof : forall a, additive (op a);
}.

#[export]
HB.structure Definition Law R V := {op of isLaw R V op}.
Definition law := Law.type.

Section ScaleLaw.

Variables (R : pzRingType) (V : zmodType) (s_law : law R V).

Lemma N1op : s_law (-1) =1 -%R. Proof. exact: N1op_subproof. Qed.
Fact opB a : additive (s_law a). Proof. exact: op_additive_subproof. Qed.

Variables (aR : pzRingType) (nu : {rmorphism aR -> R}).
Fact compN1op : (nu \; s_law) (-1) =1 -%R.
Proof. by move=> v; rewrite /= rmorphN1 N1op. Qed.

End ScaleLaw.

Module Exports. HB.reexport. End Exports.

End Scale.
Export Scale.Exports.

#[export]
HB.instance Definition _ (R : pzRingType) := Scale.isLaw.Build R R *%R
  (@mulN1r R) (@mulrBr R).

#[export]
HB.instance Definition _ (R : pzRingType) (U : lmodType R) :=
  Scale.isLaw.Build R U *:%R (@scaleN1r R U) (@scalerBr R U).

#[export]
HB.instance Definition _ (R : pzRingType) (V : zmodType) (s : Scale.law R V)
    (aR : nzRingType) (nu : {rmorphism aR -> R}) :=
  Scale.isLaw.Build aR V (nu \; s)
    (@Scale.compN1op _ _ s _ nu) (fun a => Scale.opB _ _).

#[export, non_forgetful_inheritance]
HB.instance Definition _ (R : pzRingType) (V : zmodType) (s : Scale.law R V) a :=
 isAdditive.Build V V (s a) (Scale.opB s a).

Definition scalable_for (R : pzRingType) (U : lmodType R) (V : zmodType)
    (s : R -> V -> V) (f : U -> V) :=
  forall a, {morph f : u / a *: u >-> s a u}.

HB.mixin Record isScalable (R : pzRingType) (U : lmodType R) (V : zmodType)
    (s : R -> V -> V) (f : U -> V) := {
  linear_subproof : scalable_for s f;
}.

HB.structure Definition Linear (R : pzRingType) (U : lmodType R) (V : zmodType)
    (s : R -> V -> V) :=
  {f of @Additive U V f & isScalable R U V s f}.

Definition linear_for (R : pzRingType) (U : lmodType R) (V : zmodType)
    (s : R -> V -> V) (f : U -> V) :=
  forall a, {morph f : u v / a *: u + v >-> s a u + v}.

Lemma additive_linear (R : pzRingType) (U : lmodType R) V
  (s : Scale.law R V) (f : U -> V) : linear_for s f -> additive f.
Proof. by move=> Lsf x y; rewrite -scaleN1r addrC Lsf Scale.N1op addrC. Qed.

Lemma scalable_linear (R : pzRingType) (U : lmodType R) V
  (s : Scale.law R V) (f : U -> V) : linear_for s f -> scalable_for s f.
Proof.
by move=> Lsf a v; rewrite -[a *:v](addrK v) (additive_linear Lsf) Lsf addrK.
Qed.

HB.factory Record isLinear (R : pzRingType) (U : lmodType R) (V : zmodType)
    (s : Scale.law R V) (f : U -> V) := {
  linear_subproof : linear_for s f;
}.
HB.builders Context R U V s f of isLinear R U V s f.
HB.instance Definition _ := isAdditive.Build U V f
  (additive_linear linear_subproof).
HB.instance Definition _ := isScalable.Build R U V s f
  (scalable_linear linear_subproof).
HB.end.

Module LinearExports.
Notation scalable f := (scalable_for *:%R f).
Notation linear f := (linear_for *:%R f).
Notation scalar f := (linear_for *%R f).
Module Linear.
Section Linear.
Variables (R : pzRingType) (U : lmodType R) (V : zmodType) (s : R -> V -> V).
(* Support for right-to-left rewriting with the generic linearZ rule. *)
Local Notation mapUV := (@Linear.type R U V s).
Definition map_class := mapUV.
Definition map_at (a : R) := mapUV.
Structure map_for a s_a := MapFor {map_for_map : mapUV; _ : s a = s_a}.
Definition unify_map_at a (f : map_at a) := MapFor f (erefl (s a)).
Structure wrapped := Wrap {unwrap : mapUV}.
Definition wrap (f : map_class) := Wrap f.
End Linear.
End Linear.
Notation "{ 'linear' U -> V | s }" := (@Linear.type _ U%type V%type s)
  : type_scope.
Notation "{ 'linear' U -> V }" := {linear U%type -> V%type | *:%R}
  : type_scope.
Notation "{ 'scalar' U }" := {linear U -> _ | *%R}
  (at level 0, format "{ 'scalar'  U }") : type_scope.
(* Support for right-to-left rewriting with the generic linearZ rule. *)
Coercion Linear.map_for_map : Linear.map_for >-> Linear.type.
Coercion Linear.unify_map_at : Linear.map_at >-> Linear.map_for.
Canonical Linear.unify_map_at.
Coercion Linear.unwrap : Linear.wrapped >-> Linear.type.
Coercion Linear.wrap : Linear.map_class >-> Linear.wrapped.
Canonical Linear.wrap.
End LinearExports.
HB.export LinearExports.

Section LinearTheory.

Variable R : pzRingType.

Section GenericProperties.

Variables (U : lmodType R) (V : zmodType) (s : R -> V -> V).
Variable f : {linear U -> V | s}.

Lemma linear0 : f 0 = 0. Proof. exact: raddf0. Qed.
Lemma linearN : {morph f : x / - x}. Proof. exact: raddfN. Qed.
Lemma linearD : {morph f : x y / x + y}. Proof. exact: raddfD. Qed.
Lemma linearB : {morph f : x y / x - y}. Proof. exact: raddfB. Qed.
Lemma linearMn n : {morph f : x / x *+ n}. Proof. exact: raddfMn. Qed.
Lemma linearMNn n : {morph f : x / x *- n}. Proof. exact: raddfMNn. Qed.
Lemma linear_sum I r (P : pred I) E :
  f (\sum_(i <- r | P i) E i) = \sum_(i <- r | P i) f (E i).
Proof. exact: raddf_sum. Qed.

Lemma linearZ_LR : scalable_for s f. Proof. exact: linear_subproof. Qed.
Lemma linearP a : {morph f : u v / a *: u + v >-> s a u + v}.
Proof. by move=> u v /=; rewrite linearD linearZ_LR. Qed.

End GenericProperties.

Section BidirectionalLinearZ.

Variables (U : lmodType R) (V : zmodType) (s : R -> V -> V).

(*   The general form of the linearZ lemma uses some bespoke interfaces to   *)
(* allow right-to-left rewriting when a composite scaling operation such as  *)
(* conjC \; *%R has been expanded, say in a^* * f u. This redex is matched   *)
(* by using the Scale.law interface to recognize a "head" scaling operation  *)
(* h (here *%R), stow away its "scalar" c, then reconcile h c and s a, once  *)
(* s is known, that is, once the Linear.map structure for f has been found.  *)
(* In general, s and a need not be equal to h and c; indeed they need not    *)
(* have the same type! The unification is performed by the unify_map_at      *)
(* default instance for the Linear.map_for U s a h_c sub-interface of        *)
(* Linear.map; the h_c pattern uses the Scale.law structure to insure it is  *)
(* inferred when rewriting right-to-left.                                    *)
(*   The wrap on the rhs allows rewriting f (a *: b *: u) into a *: b *: f u *)
(* with rewrite !linearZ /= instead of rewrite linearZ /= linearZ /=.        *)
(* Without it, the first rewrite linearZ would produce                       *)
(*    (a *: apply (map_for_map (@check_map_at .. a f)) (b *: u)%R)%Rlin      *)
(* and matching the second rewrite LHS would bypass the unify_map_at default *)
(* instance for b, reuse the one for a, and subsequently fail to match the   *)
(* b *: u argument. The extra wrap / unwrap ensures that this can't happen.  *)
(* In the RL direction, the wrap / unwrap will be inserted on the redex side *)
(* as needed, without causing unnecessary delta-expansion: using an explicit *)
(* identity function would have Coq normalize the redex to head normal, then *)
(* reduce the identity to expose the map_for_map projection, and the         *)
(* expanded Linear.map structure would then be exposed in the result.        *)
(*   Most of this machinery will be invisible to a casual user, because all  *)
(* the projections and default instances involved are declared as coercions. *)

Variables (S : pzRingType) (h : Scale.law S V).

Lemma linearZ c a (h_c := h c) (f : Linear.map_for U s a h_c) u :
  f (a *: u) = h_c (Linear.wrap f u).
Proof. by rewrite linearZ_LR; case: f => f /= ->. Qed.

End BidirectionalLinearZ.

Section LmodProperties.

Variables (U V : lmodType R) (f : {linear U -> V}).

Lemma linearZZ : scalable f. Proof. exact: linearZ_LR. Qed.
Lemma linearPZ : linear f. Proof. exact: linearP. Qed.

Lemma can2_scalable f' : cancel f f' -> cancel f' f -> scalable f'.
Proof. by move=> fK f'K a x; apply: (canLR fK); rewrite linearZ_LR f'K. Qed.

Lemma can2_linear f' : cancel f f' -> cancel f' f -> linear f'.
Proof. by move=> fK f'K a x y /=; apply: (canLR fK); rewrite linearP !f'K. Qed.

End LmodProperties.

Section ScalarProperties.

Variable (U : lmodType R) (f : {scalar U}).

Lemma scalarZ : scalable_for *%R f. Proof. exact: linearZ_LR. Qed.
Lemma scalarP : scalar f. Proof. exact: linearP. Qed.

End ScalarProperties.

Section LinearLmod.

Variables (W U : lmodType R) (V : zmodType).

Section Plain.

Variable (s : R -> V -> V).
Variables (f : {linear U -> V | s}) (h : {linear W -> U}).

Lemma idfun_is_scalable : scalable (@idfun U). Proof. by []. Qed.
#[export]
HB.instance Definition _ := isScalable.Build R U U *:%R idfun idfun_is_scalable.

Lemma opp_is_scalable : scalable (-%R : U -> U).
Proof. by move=> a v /=; rewrite scalerN. Qed.
#[export]
HB.instance Definition _ := isScalable.Build R U U *:%R -%R opp_is_scalable.

Lemma comp_is_scalable : scalable_for s (f \o h).
Proof. by move=> a v /=; rewrite !linearZ_LR. Qed.
#[export]
HB.instance Definition _ := isScalable.Build R W V s (f \o h) comp_is_scalable.

End Plain.

Section Scale.

Variable (s : Scale.law R V) (f g : {linear U -> V | s}).

Lemma null_fun_is_scalable : scalable_for s (\0 : U -> V).
Proof. by move=> a v /=; rewrite raddf0. Qed.
#[export]
HB.instance Definition _ :=
  isScalable.Build R U V s \0 null_fun_is_scalable.

Lemma add_fun_is_scalable : scalable_for s (add_fun f g).
Proof. by move=> a u; rewrite /= !linearZ_LR raddfD. Qed.
#[export]
HB.instance Definition _ :=
  isScalable.Build R U V s (add_fun f g) add_fun_is_scalable.

Lemma sub_fun_is_scalable : scalable_for s (f \- g).
Proof. by move=> a u; rewrite /= !linearZ_LR raddfB. Qed.
#[export]
HB.instance Definition _ := isScalable.Build R U V s (f \- g) sub_fun_is_scalable.

Lemma opp_fun_is_scalable : scalable_for s (opp_fun g).
Proof. by move=> a u; rewrite /= linearZ_LR raddfN. Qed.
#[export]
HB.instance Definition _ :=
  isScalable.Build R U V s (opp_fun g) opp_fun_is_scalable.

End Scale.

End LinearLmod.

Section LinearLalg.

Variables (A : lalgType R) (U : lmodType R).

Variables (a : A) (f : {linear U -> A}).

Fact mulr_fun_is_scalable : scalable (a \o* f).
Proof. by move=> k x /=; rewrite linearZ scalerAl. Qed.
#[export]
HB.instance Definition _ := isScalable.Build R U A *:%R (a \o* f)
  mulr_fun_is_scalable.

End LinearLalg.

End LinearTheory.

HB.structure Definition LRMorphism (R : pzRingType) (A : lalgType R) (B : pzRingType)
    (s : R -> B -> B) :=
  {f of @RMorphism A B f & isScalable R A B s f}.
(* FIXME: remove the @ once
   https://github.com/math-comp/hierarchy-builder/issues/319 is fixed *)

Module LRMorphismExports.
Notation "{ 'lrmorphism' A -> B | s }" := (@LRMorphism.type _ A%type B%type s)
  : type_scope.
Notation "{ 'lrmorphism' A -> B }" := {lrmorphism A%type -> B%type | *:%R}
  : type_scope.
End LRMorphismExports.
HB.export LRMorphismExports.

Section LRMorphismTheory.

Variables (R : pzRingType) (A B : lalgType R) (C : nzRingType)
  (s : R -> C -> C).
Variables (f : {lrmorphism A -> B}) (g : {lrmorphism B -> C | s}).

#[export] HB.instance Definition _ := RMorphism.on (@idfun A).
#[export] HB.instance Definition _ := RMorphism.on (g \o f).

Lemma rmorph_alg a : f a%:A = a%:A.
Proof. by rewrite linearZ rmorph1. Qed.

End LRMorphismTheory.

HB.mixin Record PzSemiRing_hasCommutativeMul R of PzSemiRing R := {
  mulrC : commutative (@mul R)
}.

Module SemiRing_hasCommutativeMul.
#[deprecated(since="mathcomp 2.4.0",
             note="Use PzSemiRing_hasCommutativeMul.Build instead.")]
Notation Build R := (PzSemiRing_hasCommutativeMul.Build R) (only parsing).
End SemiRing_hasCommutativeMul.

#[deprecated(since="mathcomp 2.4.0",
             note="Use PzSemiRing_hasCommutativeMul instead.")]
Notation SemiRing_hasCommutativeMul R :=
  (PzSemiRing_hasCommutativeMul R) (only parsing).

#[short(type="comPzSemiRingType")]
HB.structure Definition ComPzSemiRing :=
  {R of PzSemiRing R & PzSemiRing_hasCommutativeMul R}.

Module ComPzSemiRingExports.
Bind Scope ring_scope with ComPzSemiRing.sort.
End ComPzSemiRingExports.
HB.export ComPzSemiRingExports.

HB.factory Record Nmodule_isComPzSemiRing R of Nmodule R := {
  one : R;
  mul : R -> R -> R;
  mulrA : associative mul;
  mulrC : commutative mul;
  mul1r : left_id one mul;
  mulrDl : left_distributive mul add;
  mul0r : left_zero zero mul;
}.

HB.builders Context R of Nmodule_isComPzSemiRing R.
  Definition mulr1 := Monoid.mulC_id mulrC mul1r.
  Definition mulrDr := Monoid.mulC_dist mulrC mulrDl.
  Lemma mulr0 : right_zero zero mul.
  Proof. by move=> x; rewrite mulrC mul0r. Qed.
  HB.instance Definition _ := Nmodule_isPzSemiRing.Build R
    mulrA mul1r mulr1 mulrDl mulrDr mul0r mulr0.
  HB.instance Definition _ := PzSemiRing_hasCommutativeMul.Build R mulrC.
HB.end.

#[short(type="comNzSemiRingType")]
HB.structure Definition ComNzSemiRing :=
  {R of NzSemiRing R & PzSemiRing_hasCommutativeMul R}.

#[deprecated(since="mathcomp 2.4.0",
             note="Use ComNzSemiRing instead.")]
Notation ComSemiRing R := (ComNzSemiRing R) (only parsing).

Module ComSemiRing.
#[deprecated(since="mathcomp 2.4.0",
             note="Use ComNzSemiRing.sort instead.")]
Notation sort := (ComNzSemiRing.sort) (only parsing).
#[deprecated(since="mathcomp 2.4.0",
             note="Use ComNzSemiRing.on instead.")]
Notation on R := (ComNzSemiRing.on R) (only parsing).
#[deprecated(since="mathcomp 2.4.0",
             note="Use ComNzSemiRing.copy instead.")]
Notation copy T U := (ComNzSemiRing.copy T U) (only parsing).
End ComSemiRing.

Module ComNzSemiRingExports.
Bind Scope ring_scope with ComNzSemiRing.sort.
End ComNzSemiRingExports.
HB.export ComNzSemiRingExports.

HB.factory Record Nmodule_isComNzSemiRing R of Nmodule R := {
  one : R;
  mul : R -> R -> R;
  mulrA : associative mul;
  mulrC : commutative mul;
  mul1r : left_id one mul;
  mulrDl : left_distributive mul add;
  mul0r : left_zero zero mul;
  oner_neq0 : one != zero
}.

Module Nmodule_isComSemiRing.
#[deprecated(since="mathcomp 2.4.0",
             note="Use Nmodule_isComNzSemiRing.Build instead.")]
Notation Build R := (Nmodule_isComNzSemiRing.Build R) (only parsing).
End Nmodule_isComSemiRing.

#[deprecated(since="mathcomp 2.4.0",
             note="Use Nmodule_isComNzSemiRing instead.")]
Notation Nmodule_isComSemiRing R := (Nmodule_isComNzSemiRing R) (only parsing).

HB.builders Context R of Nmodule_isComNzSemiRing R.
  Definition mulr1 := Monoid.mulC_id mulrC mul1r.
  Definition mulrDr := Monoid.mulC_dist mulrC mulrDl.
  Lemma mulr0 : right_zero zero mul.
  Proof. by move=> x; rewrite mulrC mul0r. Qed.
  HB.instance Definition _ := Nmodule_isNzSemiRing.Build R
    mulrA mul1r mulr1 mulrDl mulrDr mul0r mulr0 oner_neq0.
  HB.instance Definition _ := PzSemiRing_hasCommutativeMul.Build R mulrC.
HB.end.

Section ComSemiRingTheory.

Variable R : comPzSemiRingType.
Implicit Types x y : R.

#[export]
HB.instance Definition _ := SemiGroup.isCommutativeLaw.Build R *%R mulrC.
Lemma mulrCA : @left_commutative R R *%R. Proof. exact: mulmCA. Qed.
Lemma mulrAC : @right_commutative R R *%R. Proof. exact: mulmAC. Qed.
Lemma mulrACA : @interchange R *%R *%R. Proof. exact: mulmACA. Qed.

Lemma exprMn n : {morph (fun x => x ^+ n) : x y / x * y}.
Proof. by move=> x y; exact/exprMn_comm/mulrC. Qed.

Lemma prodrXl n I r (P : pred I) (F : I -> R) :
  \prod_(i <- r | P i) F i ^+ n = (\prod_(i <- r | P i) F i) ^+ n.
Proof. by rewrite (big_morph _ (exprMn n) (expr1n _ n)). Qed.

Lemma prodr_undup_exp_count (I : eqType) r (P : pred I) (F : I -> R) :
  \prod_(i <- undup r | P i) F i ^+ count_mem i r = \prod_(i <- r | P i) F i.
Proof. exact: big_undup_iterop_count.  Qed.

Lemma prodrMl {I : finType} (A : pred I) (x : R) F :
  \prod_(i in A) (x * F i) = x ^+ #|A| * \prod_(i in A) F i.
Proof. by rewrite big_split ?prodr_const. Qed.

Lemma prodrMr {I : finType} (A : pred I) (x : R) F :
  \prod_(i in A) (F i * x) = \prod_(i in A) F i * x ^+ #|A|.
Proof. by rewrite big_split ?prodr_const. Qed.

Lemma exprDn x y n :
  (x + y) ^+ n = \sum_(i < n.+1) (x ^+ (n - i) * y ^+ i) *+ 'C(n, i).
Proof. by rewrite exprDn_comm //; apply: mulrC. Qed.

Lemma sqrrD x y : (x + y) ^+ 2 = x ^+ 2 + x * y *+ 2 + y ^+ 2.
Proof. by rewrite exprDn !big_ord_recr big_ord0 /= add0r mulr1 mul1r. Qed.

End ComSemiRingTheory.

Section ComNzSemiRingTheory.

Variable R : comNzSemiRingType.
Implicit Types x y : R.

Section FrobeniusAutomorphism.

Variables (p : nat) (charRp : p \in char R).

Lemma Frobenius_aut_is_semi_additive : semi_additive (Frobenius_aut charRp).
Proof.
by split=> [|x y]; [exact: Frobenius_aut0 | exact/Frobenius_autD_comm/mulrC].
Qed.

Lemma Frobenius_aut_is_multiplicative : multiplicative (Frobenius_aut charRp).
Proof.
by split=> [x y|]; [exact/Frobenius_autM_comm/mulrC | exact: Frobenius_aut1].
Qed.

#[export]
HB.instance Definition _ := isSemiAdditive.Build R R (Frobenius_aut charRp)
  Frobenius_aut_is_semi_additive.
#[export]
HB.instance Definition _ := isMultiplicative.Build R R (Frobenius_aut charRp)
  Frobenius_aut_is_multiplicative.

End FrobeniusAutomorphism.

Lemma exprDn_char x y n : (char R).-nat n -> (x + y) ^+ n = x ^+ n + y ^+ n.
Proof.
pose p := pdiv n; have [|n_gt1 charRn] := leqP n 1; first by case: (n) => [|[]].
have charRp: p \in char R by rewrite (pnatPpi charRn) ?pi_pdiv.
have{charRn} /p_natP[e ->]: p.-nat n by rewrite -(eq_pnat _ (charf_eq charRp)).
by elim: e => // e IHe; rewrite !expnSr !exprM IHe -Frobenius_autE rmorphD.
Qed.

Lemma rmorph_comm (S : nzSemiRingType) (f : {rmorphism R -> S}) x y :
  comm (f x) (f y).
Proof. by red; rewrite -!rmorphM mulrC. Qed.

End ComNzSemiRingTheory.

#[short(type="comPzRingType")]
HB.structure Definition ComPzRing := {R of PzRing R & ComPzSemiRing R}.

HB.factory Record PzRing_hasCommutativeMul R of PzRing R := {
  mulrC : commutative (@mul R)
}.

Module Ring_hasCommutativeMul.
#[deprecated(since="mathcomp 2.4.0",
             note="Use PzRing_hasCommutativeMul.Build instead.")]
Notation Build R := (PzRing_hasCommutativeMul.Build R) (only parsing).
End Ring_hasCommutativeMul.

#[deprecated(since="mathcomp 2.4.0",
             note="Use PzRing_hasCommutativeMul instead.")]
Notation Ring_hasCommutativeMul R :=
  (PzRing_hasCommutativeMul R) (only parsing).

HB.builders Context R of PzRing_hasCommutativeMul R.
HB.instance Definition _ := PzSemiRing_hasCommutativeMul.Build R mulrC.
HB.end.

HB.factory Record Zmodule_isComPzRing R of Zmodule R := {
  one : R;
  mul : R -> R -> R;
  mulrA : associative mul;
  mulrC : commutative mul;
  mul1r : left_id one mul;
  mulrDl : left_distributive mul add;
}.

HB.builders Context R of Zmodule_isComPzRing R.
  Definition mulr1 := Monoid.mulC_id mulrC mul1r.
  Definition mulrDr := Monoid.mulC_dist mulrC mulrDl.
  HB.instance Definition _ := Zmodule_isPzRing.Build R
    mulrA mul1r mulr1 mulrDl mulrDr.
  HB.instance Definition _ := PzRing_hasCommutativeMul.Build R mulrC.
HB.end.

Module ComPzRingExports.
Bind Scope ring_scope with ComPzRing.sort.
End ComPzRingExports.
HB.export ComPzRingExports.

#[short(type="comNzRingType")]
HB.structure Definition ComNzRing := {R of NzRing R & ComNzSemiRing R}.

#[deprecated(since="mathcomp 2.4.0",
             note="Use ComNzRing instead.")]
Notation ComRing R := (ComNzRing R) (only parsing).

Module ComRing.
#[deprecated(since="mathcomp 2.4.0",
             note="Use ComNzRing.sort instead.")]
Notation sort := (ComNzRing.sort) (only parsing).
#[deprecated(since="mathcomp 2.4.0",
             note="Use ComNzRing.on instead.")]
Notation on R := (ComNzRing.on R) (only parsing).
#[deprecated(since="mathcomp 2.4.0",
             note="Use ComNzRing.copy instead.")]
Notation copy T U := (ComNzRing.copy T U) (only parsing).
End ComRing.

HB.factory Record Zmodule_isComNzRing R of Zmodule R := {
  one : R;
  mul : R -> R -> R;
  mulrA : associative mul;
  mulrC : commutative mul;
  mul1r : left_id one mul;
  mulrDl : left_distributive mul add;
  oner_neq0 : one != zero
}.

Module Zmodule_isComRing.
#[deprecated(since="mathcomp 2.4.0",
             note="Use Zmodule_isComNzRing.Build instead.")]
Notation Build R := (Zmodule_isComNzRing.Build R) (only parsing).
End Zmodule_isComRing.

#[deprecated(since="mathcomp 2.4.0",
             note="Use Zmodule_isComNzRing instead.")]
Notation Zmodule_isComRing R := (Zmodule_isComNzRing R) (only parsing).

HB.builders Context R of Zmodule_isComNzRing R.
  Definition mulr1 := Monoid.mulC_id mulrC mul1r.
  Definition mulrDr := Monoid.mulC_dist mulrC mulrDl.
  HB.instance Definition _ := Zmodule_isNzRing.Build R
    mulrA mul1r mulr1 mulrDl mulrDr oner_neq0.
  HB.instance Definition _ := PzRing_hasCommutativeMul.Build R mulrC.
HB.end.

Module ComNzRingExports.
Bind Scope ring_scope with ComNzRing.sort.
End ComNzRingExports.
HB.export ComNzRingExports.

Section ComPzRingTheory.

Variable R : comPzRingType.
Implicit Types x y : R.

Lemma exprBn x y n :
  (x - y) ^+ n =
     \sum_(i < n.+1) ((-1) ^+ i * x ^+ (n - i) * y ^+ i) *+ 'C(n, i).
Proof. by rewrite exprBn_comm //; apply: mulrC. Qed.

Lemma subrXX x y n :
  x ^+ n - y ^+ n = (x - y) * (\sum_(i < n) x ^+ (n.-1 - i) * y ^+ i).
Proof. by rewrite -subrXX_comm //; apply: mulrC. Qed.

Lemma sqrrB x y : (x - y) ^+ 2 = x ^+ 2 - x * y *+ 2 + y ^+ 2.
Proof. by rewrite sqrrD mulrN mulNrn sqrrN. Qed.

Lemma subr_sqr x y : x ^+ 2 - y ^+ 2 = (x - y) * (x + y).
Proof. by rewrite subrXX !big_ord_recr big_ord0 /= add0r mulr1 mul1r. Qed.

Lemma subr_sqrDB x y : (x + y) ^+ 2 - (x - y) ^+ 2 = x * y *+ 4.
Proof.
rewrite sqrrD sqrrB -!(addrAC _ (y ^+ 2)) opprB.
by rewrite [LHS]addrC addrA subrK -mulrnDr.
Qed.

Section ScaleLinear.

Variables (U V : lmodType R) (b : R) (f : {linear U -> V}).

Lemma scale_is_scalable : scalable ( *:%R b : V -> V).
Proof. by move=> a v /=; rewrite !scalerA mulrC. Qed.
#[export]
HB.instance Definition _ := isScalable.Build R V V *:%R ( *:%R b)
  scale_is_scalable.

Lemma scale_fun_is_scalable : scalable (b \*: f).
Proof. by move=> a v /=; rewrite !linearZ. Qed.
#[export]
HB.instance Definition _ := isScalable.Build R U V *:%R (b \*: f)
  scale_fun_is_scalable.

End ScaleLinear.

End ComPzRingTheory.

HB.mixin Record Lalgebra_isAlgebra (R : pzRingType) V of Lalgebra R V := {
  scalerAr : forall k (x y : V), k *: (x * y) = x * (k *: y);
}.
#[short(type="algType")]
HB.structure Definition Algebra (R : pzRingType) :=
  {A of Lalgebra_isAlgebra R A & Lalgebra R A}.

Module AlgExports.
Bind Scope ring_scope with Algebra.sort.
End AlgExports.
HB.export AlgExports.

HB.factory Record Lalgebra_isComAlgebra R V of ComNzRing V & Lalgebra R V := {}.
HB.builders Context (R : pzRingType) V of Lalgebra_isComAlgebra R V.

Lemma scalarAr k (x y : V) : k *: (x * y) = x * (k *: y).
Proof. by rewrite mulrC scalerAl mulrC. Qed.

HB.instance Definition lalgebra_is_algebra : Lalgebra_isAlgebra R V :=
  Lalgebra_isAlgebra.Build R V scalarAr.

HB.end.

#[short(type="comAlgType")]
HB.structure Definition ComAlgebra R := {V of ComNzRing V & Algebra R V}.

Module ComAlgExports.
Bind Scope ring_scope with ComAlgebra.sort.
End ComAlgExports.
HB.export ComAlgExports.

Section AlgebraTheory.
Variables (R : comNzRingType).
#[export]
HB.instance Definition _ :=
  PzSemiRing_hasCommutativeMul.Build R^c (fun _ _ => mulrC _ _).
#[export]
HB.instance Definition _ := ComNzSemiRing.on R^o.
#[export]
HB.instance Definition _ := Lalgebra_isComAlgebra.Build R R^o.
End AlgebraTheory.

Section AlgebraTheory.

(* TODO: MC-1 port (R has been changed from comNzRingType to pzRingType) *)
Variables (R : pzRingType) (A : algType R).
Implicit Types (k : R) (x y : A).

Lemma scalerCA k x y : k *: x * y = x * (k *: y).
Proof. by rewrite -scalerAl scalerAr. Qed.

Lemma mulr_algr a x : x * a%:A = a *: x.
Proof. by rewrite -scalerAr mulr1. Qed.

Lemma comm_alg a x : comm a%:A x.
Proof. by rewrite /comm mulr_algr mulr_algl. Qed.

Lemma exprZn k x n : (k *: x) ^+ n = k ^+ n *: x ^+ n.
Proof.
elim: n => [|n IHn]; first by rewrite !expr0 scale1r.
by rewrite !exprS IHn -scalerA scalerAr scalerAl.
Qed.

Lemma scaler_prod I r (P : pred I) (F : I -> R) (G : I -> A) :
  \prod_(i <- r | P i) (F i *: G i) =
    \prod_(i <- r | P i) F i *: \prod_(i <- r | P i) G i.
Proof.
elim/big_rec3: _ => [|i x a _ _ ->]; first by rewrite scale1r.
by rewrite -scalerAl -scalerAr scalerA.
Qed.

Lemma scaler_prodl (I : finType) (S : pred I) (F : I -> A) k :
  \prod_(i in S) (k *: F i)  = k ^+ #|S| *: \prod_(i in S) F i.
Proof. by rewrite scaler_prod prodr_const. Qed.

Lemma scaler_prodr (I : finType) (S : pred I) (F : I -> R) x :
  \prod_(i in S) (F i *: x)  = \prod_(i in S) F i *: x ^+ #|S|.
Proof. by rewrite scaler_prod prodr_const. Qed.

Variables (U : lmodType R) (a : A) (f : {linear U -> A}).

Lemma mull_fun_is_scalable : scalable (a \*o f).
Proof. by move=> k x /=; rewrite linearZ scalerAr. Qed.
#[export]
HB.instance Definition _ := isScalable.Build R U A *:%R (a \*o f)
  mull_fun_is_scalable.

End AlgebraTheory.

HB.mixin Record NzRing_hasMulInverse R of NzRing R := {
  unit_subdef : pred R;
  inv : R -> R;
  mulVr_subproof : {in unit_subdef, left_inverse 1 inv *%R};
  divrr_subproof : {in unit_subdef, right_inverse 1 inv *%R};
  unitrP_subproof : forall x y, y * x = 1 /\ x * y = 1 -> unit_subdef x;
  invr_out_subproof : {in [predC unit_subdef], inv =1 id}
}.

Module Ring_hasMulInverse.
#[deprecated(since="mathcomp 2.4.0",
             note="Use NzRing_hasMulInverse.Build instead.")]
Notation Build R := (NzRing_hasMulInverse.Build R) (only parsing).
End Ring_hasMulInverse.

#[deprecated(since="mathcomp 2.4.0",
             note="Use NzRing_hasMulInverse instead.")]
Notation Ring_hasMulInverse R := (NzRing_hasMulInverse R) (only parsing).

#[short(type="unitRingType")]
HB.structure Definition UnitRing := {R of NzRing_hasMulInverse R & NzRing R}.

Module UnitRingExports.
Bind Scope ring_scope with UnitRing.sort.
End UnitRingExports.
HB.export UnitRingExports.

Definition unit_pred {R : unitRingType} :=
  Eval cbv [ unit_subdef NzRing_hasMulInverse.unit_subdef ] in
    (fun u : R => unit_subdef u).
Arguments unit_pred _ _ /.
Definition unit {R : unitRingType} := [qualify a u : R | unit_pred u].

Local Notation "x ^-1" := (inv x).
Local Notation "x / y" := (x * y^-1).
Local Notation "x ^- n" := ((x ^+ n)^-1).

Section UnitRingTheory.

Variable R : unitRingType.
Implicit Types x y : R.

Lemma divrr : {in unit, right_inverse 1 (@inv R) *%R}.
Proof. exact: divrr_subproof. Qed.
Definition mulrV := divrr.

Lemma mulVr : {in unit, left_inverse 1 (@inv R) *%R}.
Proof. exact: mulVr_subproof. Qed.

Lemma invr_out x : x \isn't a unit -> x^-1 = x.
Proof. exact: invr_out_subproof. Qed.

Lemma unitrP x : reflect (exists y, y * x = 1 /\ x * y = 1) (x \is a unit).
Proof.
apply: (iffP idP) => [Ux | []]; last exact: unitrP_subproof.
by exists x^-1; rewrite divrr ?mulVr.
Qed.

Lemma mulKr : {in unit, left_loop (@inv R) *%R}.
Proof. by move=> x Ux y; rewrite mulrA mulVr ?mul1r. Qed.

Lemma mulVKr : {in unit, rev_left_loop (@inv R) *%R}.
Proof. by move=> x Ux y; rewrite mulrA mulrV ?mul1r. Qed.

Lemma mulrK : {in unit, right_loop (@inv R) *%R}.
Proof. by move=> x Ux y; rewrite -mulrA divrr ?mulr1. Qed.

Lemma mulrVK : {in unit, rev_right_loop (@inv R) *%R}.
Proof. by move=> x Ux y; rewrite -mulrA mulVr ?mulr1. Qed.
Definition divrK := mulrVK.

Lemma mulrI : {in @unit R, right_injective *%R}.
Proof. by move=> x Ux; apply: can_inj (mulKr Ux). Qed.

Lemma mulIr : {in @unit R, left_injective *%R}.
Proof. by move=> x Ux; apply: can_inj (mulrK Ux). Qed.

(* Due to noncommutativity, fractions are inverted. *)
Lemma telescope_prodr n m (f : nat -> R) :
    (forall k, n < k < m -> f k \is a unit) -> n < m ->
  \prod_(n <= k < m) (f k / f k.+1) = f n / f m.
Proof.
move=> Uf ltnm; rewrite (telescope_big (fun i j => f i / f j)) ?ltnm//.
by move=> k ltnkm /=; rewrite mulrA divrK// Uf.
Qed.

Lemma telescope_prodr_eq n m (f u : nat -> R) : n < m ->
    (forall k, n < k < m -> f k \is a unit) ->
    (forall k, (n <= k < m)%N -> u k = f k / f k.+1) ->
  \prod_(n <= k < m) u k = f n / f m.
Proof.
by move=> ? ? uE; under eq_big_nat do rewrite uE //=; exact: telescope_prodr.
Qed.

Lemma commrV x y : comm x y -> comm x y^-1.
Proof.
have [Uy cxy | /invr_out-> //] := boolP (y \in unit).
by apply: (canLR (mulrK Uy)); rewrite -mulrA cxy mulKr.
Qed.

Lemma unitrE x : (x \is a unit) = (x / x == 1).
Proof.
apply/idP/eqP=> [Ux | xx1]; first exact: divrr.
by apply/unitrP; exists x^-1; rewrite -commrV.
Qed.

Lemma invrK : involutive (@inv R).
Proof.
move=> x; case Ux: (x \in unit); last by rewrite !invr_out ?Ux.
rewrite -(mulrK Ux _^-1) -mulrA commrV ?mulKr //.
by apply/unitrP; exists x; rewrite divrr ?mulVr.
Qed.

Lemma invr_inj : injective (@inv R). Proof. exact: inv_inj invrK. Qed.

Lemma unitrV x : (x^-1 \in unit) = (x \in unit).
Proof. by rewrite !unitrE invrK commrV. Qed.

Lemma unitr1 : 1 \in @unit R.
Proof. by apply/unitrP; exists 1; rewrite mulr1. Qed.

Lemma invr1 : 1^-1 = 1 :> R.
Proof. by rewrite -{2}(mulVr unitr1) mulr1. Qed.

Lemma div1r x : 1 / x = x^-1. Proof. by rewrite mul1r. Qed.
Lemma divr1 x : x / 1 = x. Proof. by rewrite invr1 mulr1. Qed.

Lemma natr_div m d :
  d %| m -> d%:R \is a @unit R -> (m %/ d)%:R = m%:R / d%:R :> R.
Proof.
by rewrite dvdn_eq => /eqP def_m unit_d; rewrite -{2}def_m natrM mulrK.
Qed.

Lemma divrI : {in unit, right_injective (fun x y => x / y)}.
Proof. by move=> x /mulrI/inj_comp; apply; apply: invr_inj. Qed.

Lemma divIr : {in unit, left_injective (fun x y => x / y)}.
Proof. by move=> x; rewrite -unitrV => /mulIr. Qed.

Lemma unitr0 : (0 \is a @unit R) = false.
Proof. by apply/unitrP=> [[x [_ /esym/eqP]]]; rewrite mul0r oner_eq0. Qed.

Lemma invr0 : 0^-1 = 0 :> R.
Proof. by rewrite invr_out ?unitr0. Qed.

Lemma unitrN1 : -1 \is a @unit R.
Proof. by apply/unitrP; exists (-1); rewrite mulrNN mulr1. Qed.

Lemma invrN1 : (-1)^-1 = -1 :> R.
Proof. by rewrite -{2}(divrr unitrN1) mulN1r opprK. Qed.

Lemma invr_sign n : ((-1) ^- n) = (-1) ^+ n :> R.
Proof. by rewrite -signr_odd; case: (odd n); rewrite (invr1, invrN1). Qed.

Lemma unitrMl x y : y \is a unit -> (x * y \is a unit) = (x \is a unit).
Proof.
move=> Uy; wlog Ux: x y Uy / x \is a unit => [WHxy|].
  by apply/idP/idP=> Ux; first rewrite -(mulrK Uy x); rewrite WHxy ?unitrV.
rewrite Ux; apply/unitrP; exists (y^-1 * x^-1).
by rewrite -!mulrA mulKr ?mulrA ?mulrK ?divrr ?mulVr.
Qed.

Lemma unitrMr x y : x \is a unit -> (x * y \is a unit) = (y \is a unit).
Proof.
move=> Ux; apply/idP/idP=> [Uxy | Uy]; last by rewrite unitrMl.
by rewrite -(mulKr Ux y) unitrMl ?unitrV.
Qed.

Lemma unitr_prod {I : Type} (P : pred I) (E : I -> R) (r : seq I) :
  (forall i, P i -> E i \is a GRing.unit) ->
    (\prod_(i <- r | P i) E i \is a GRing.unit).
Proof.
by move=> Eunit; elim/big_rec: _ => [/[!unitr1] |i x /Eunit/unitrMr->].
Qed.

Lemma unitr_prod_in {I : eqType} (P : pred I) (E : I -> R) (r : seq I) :
  {in r, forall i, P i -> E i \is a GRing.unit} ->
    (\prod_(i <- r | P i) E i \is a GRing.unit).
Proof.
by rewrite big_seq_cond => H; apply: unitr_prod => i /andP[]; exact: H.
Qed.

Lemma invrM : {in unit &, forall x y, (x * y)^-1 = y^-1 * x^-1}.
Proof.
move=> x y Ux Uy; have Uxy: (x * y \in unit) by rewrite unitrMl.
by apply: (mulrI Uxy); rewrite divrr ?mulrA ?mulrK ?divrr.
Qed.

Lemma unitrM_comm x y :
  comm x y -> (x * y \is a unit) = (x \is a unit) && (y \is a unit).
Proof.
move=> cxy; apply/idP/andP=> [Uxy | [Ux Uy]]; last by rewrite unitrMl.
suffices Ux: x \in unit by rewrite unitrMr in Uxy.
apply/unitrP; case/unitrP: Uxy => z [zxy xyz]; exists (y * z).
rewrite mulrA xyz -{1}[y]mul1r -{1}zxy cxy -!mulrA (mulrA x) (mulrA _ z) xyz.
by rewrite mul1r -cxy.
Qed.

Lemma unitrX x n : x \is a unit -> x ^+ n \is a unit.
Proof.
by move=> Ux; elim: n => [|n IHn]; rewrite ?unitr1 // exprS unitrMl.
Qed.

Lemma unitrX_pos x n : n > 0 -> (x ^+ n \in unit) = (x \in unit).
Proof.
case: n => // n _; rewrite exprS unitrM_comm; last exact: commrX.
by case Ux: (x \is a unit); rewrite // unitrX.
Qed.

Lemma exprVn x n : x^-1 ^+ n = x ^- n.
Proof.
elim: n => [|n IHn]; first by rewrite !expr0 ?invr1.
case Ux: (x \is a unit); first by rewrite exprSr exprS IHn -invrM // unitrX.
by rewrite !invr_out ?unitrX_pos ?Ux.
Qed.

Lemma exprB m n x : n <= m -> x \is a unit -> x ^+ (m - n) = x ^+ m / x ^+ n.
Proof. by move/subnK=> {2}<- Ux; rewrite exprD mulrK ?unitrX. Qed.

Lemma invr_neq0 x : x != 0 -> x^-1 != 0.
Proof.
move=> nx0; case Ux: (x \is a unit); last by rewrite invr_out ?Ux.
by apply/eqP=> x'0; rewrite -unitrV x'0 unitr0 in Ux.
Qed.

Lemma invr_eq0 x : (x^-1 == 0) = (x == 0).
Proof. by apply: negb_inj; apply/idP/idP; move/invr_neq0; rewrite ?invrK. Qed.

Lemma invr_eq1 x : (x^-1 == 1) = (x == 1).
Proof. by rewrite (inv_eq invrK) invr1. Qed.

Lemma rev_unitrP (x y : R^c) : y * x = 1 /\ x * y = 1 -> x \is a unit.
Proof. by case=> [yx1 xy1]; apply/unitrP; exists y. Qed.

#[export]
HB.instance Definition _ :=
  NzRing_hasMulInverse.Build R^c mulrV mulVr rev_unitrP invr_out.

#[export]
HB.instance Definition _ := UnitRing.on R^o.

End UnitRingTheory.

Arguments invrK {R}.
Arguments invr_inj {R} [x1 x2].
Arguments telescope_prodr_eq {R n m} f u.

Lemma rev_prodrV (R : unitRingType)
  (I : Type) (r : seq I) (P : pred I) (E : I -> R) :
  (forall i, P i -> E i \is a GRing.unit) ->
  \prod_(i <- r | P i) (E i)^-1 = ((\prod_(i <- r | P i) (E i : R^c))^-1).
Proof.
move=> Eunit; symmetry.
apply: (big_morph_in GRing.unit _ _ (unitr1 R^c) (@invrM _) (invr1 _)) Eunit.
by move=> x y xunit; rewrite unitrMr.
Qed.

Section UnitRingClosedPredicates.

Variables (R : unitRingType) (S : {pred R}).

Definition invr_closed := {in S, forall x, x^-1 \in S}.
Definition divr_2closed := {in S &, forall x y, x / y \in S}.
Definition divr_closed := 1 \in S /\ divr_2closed.
Definition sdivr_closed := -1 \in S /\ divr_2closed.
Definition divring_closed := [/\ 1 \in S, subr_2closed S & divr_2closed].

Lemma divr_closedV : divr_closed -> invr_closed.
Proof. by case=> S1 Sdiv x Sx; rewrite -[x^-1]mul1r Sdiv. Qed.

Lemma divr_closedM : divr_closed -> mulr_closed S.
Proof.
by case=> S1 Sdiv; split=> // x y Sx Sy; rewrite -[y]invrK -[y^-1]mul1r !Sdiv.
Qed.

Lemma sdivr_closed_div : sdivr_closed -> divr_closed.
Proof. by case=> SN1 Sdiv; split; rewrite // -(divrr (@unitrN1 _)) Sdiv. Qed.

Lemma sdivr_closedM : sdivr_closed -> smulr_closed S.
Proof.
by move=> Sdiv; have [_ SM] := divr_closedM (sdivr_closed_div Sdiv); case: Sdiv.
Qed.

Lemma divring_closedBM : divring_closed -> subring_closed S.
Proof. by case=> S1 SB Sdiv; split=> //; case: divr_closedM. Qed.

Lemma divring_closed_div : divring_closed -> sdivr_closed.
Proof.
case=> S1 SB Sdiv; split; rewrite ?zmod_closedN //.
exact/subring_closedB/divring_closedBM.
Qed.

End UnitRingClosedPredicates.

Section UnitRingMorphism.

Variables (R S : unitRingType) (f : {rmorphism R -> S}).

Lemma rmorph_unit x : x \in unit -> f x \in unit.
Proof.
case/unitrP=> y [yx1 xy1]; apply/unitrP.
by exists (f y); rewrite -!rmorphM // yx1 xy1 rmorph1.
Qed.

Lemma rmorphV : {in unit, {morph f: x / x^-1}}.
Proof.
move=> x Ux; rewrite /= -[(f x)^-1]mul1r.
by apply: (canRL (mulrK (rmorph_unit Ux))); rewrite -rmorphM mulVr ?rmorph1.
Qed.

Lemma rmorph_div x y : y \in unit -> f (x / y) = f x / f y.
Proof. by move=> Uy; rewrite rmorphM /= rmorphV. Qed.

End UnitRingMorphism.

#[short(type="comUnitRingType")]
HB.structure Definition ComUnitRing := {R of ComNzRing R & UnitRing R}.

Module ComUnitRingExports.
Bind Scope ring_scope with ComUnitRing.sort.
End ComUnitRingExports.
HB.export ComUnitRingExports.

(* TODO_HB: fix the name (was ComUnitRingMixin) *)
HB.factory Record ComNzRing_hasMulInverse R of ComNzRing R := {
  unit : {pred R};
  inv : R -> R;
  mulVx : {in unit, left_inverse 1 inv *%R};
  unitPl : forall x y, y * x = 1 -> unit x;
  invr_out : {in [predC unit], inv =1 id}
}.

Module ComRing_hasMulInverse.
#[deprecated(since="mathcomp 2.4.0",
             note="Use ComNzRing_hasMulInverse.Build instead.")]
Notation Build R := (ComNzRing_hasMulInverse.Build R) (only parsing).
End ComRing_hasMulInverse.

#[deprecated(since="mathcomp 2.4.0",
             note="Use ComNzRing_hasMulInverse instead.")]
Notation ComRing_hasMulInverse R := (ComNzRing_hasMulInverse R) (only parsing).

HB.builders Context R of ComNzRing_hasMulInverse R.

Fact mulC_mulrV : {in unit, right_inverse 1 inv *%R}.
Proof. by move=> x Ux /=; rewrite mulrC mulVx. Qed.

Fact mulC_unitP x y : y * x = 1 /\ x * y = 1 -> unit x.
Proof. by case=> yx _; apply: unitPl yx. Qed.

HB.instance Definition _ :=
  NzRing_hasMulInverse.Build R mulVx mulC_mulrV mulC_unitP invr_out.

HB.end.

#[short(type="unitAlgType")]
HB.structure Definition UnitAlgebra R := {V of Algebra R V & UnitRing V}.

Module UnitAlgebraExports.
Bind Scope ring_scope with UnitAlgebra.sort.
End UnitAlgebraExports.
HB.export UnitAlgebraExports.

#[short(type="comUnitAlgType")]
HB.structure Definition ComUnitAlgebra R := {V of ComAlgebra R V & UnitRing V}.

Module ComUnitAlgebraExports.
Bind Scope ring_scope with UnitAlgebra.sort.
End ComUnitAlgebraExports.
HB.export ComUnitAlgebraExports.

Section ComUnitRingTheory.

Variable R : comUnitRingType.
Implicit Types x y : R.

Lemma unitrM x y : (x * y \in unit) = (x \in unit) && (y \in unit).
Proof. exact/unitrM_comm/mulrC. Qed.

Lemma unitrPr x : reflect (exists y, x * y = 1) (x \in unit).
Proof.
by apply: (iffP (unitrP x)) => [[y []] | [y]]; exists y; rewrite // mulrC.
Qed.

Lemma mulr1_eq x y : x * y = 1 -> x^-1 = y.
Proof.
by move=> xy_eq1; rewrite -[LHS]mulr1 -xy_eq1; apply/mulKr/unitrPr; exists y.
Qed.

Lemma divr1_eq x y : x / y = 1 -> x = y. Proof. by move/mulr1_eq/invr_inj. Qed.

Lemma divKr x : x \is a unit -> {in unit, involutive (fun y => x / y)}.
Proof. by move=> Ux y Uy; rewrite /= invrM ?unitrV // invrK mulrC divrK. Qed.

Lemma expr_div_n x y n : (x / y) ^+ n = x ^+ n / y ^+ n.
Proof. by rewrite exprMn exprVn. Qed.

Lemma unitr_prodP (I : eqType) (r : seq I) (P : pred I) (E : I -> R) :
  reflect {in r, forall i, P i -> E i \is a GRing.unit}
    (\prod_(i <- r | P i) E i \is a GRing.unit).
Proof.
rewrite (big_morph [in unit] unitrM (@unitr1 _) ) big_all_cond.
exact: 'all_implyP.
Qed.

Lemma prodrV (I : eqType) (r : seq I) (P : pred I) (E : I -> R) :
  (forall i, P i -> E i \is a GRing.unit) ->
  \prod_(i <- r | P i) (E i)^-1 = (\prod_(i <- r | P i) E i)^-1.
Proof.
by move=> /rev_prodrV->; rewrite rev_prodr (perm_big r)// perm_rev.
Qed.

(* TODO: HB.saturate *)
#[export] HB.instance Definition _ := ComUnitRing.on R^c.
#[export] HB.instance Definition _ := ComUnitRing.on R^o.
(* /TODO *)

End ComUnitRingTheory.

Section UnitAlgebraTheory.

Variable (R : comUnitRingType) (A : unitAlgType R).
Implicit Types (k : R) (x y : A).

Lemma scaler_injl : {in unit, @right_injective R A A *:%R}.
Proof.
move=> k Uk x1 x2 Hx1x2.
by rewrite -[x1]scale1r -(mulVr Uk) -scalerA Hx1x2 scalerA mulVr // scale1r.
Qed.

Lemma scaler_unit k x : k \in unit -> (k *: x \in unit) = (x \in unit).
Proof.
move=> Uk; apply/idP/idP=> [Ukx | Ux]; apply/unitrP; last first.
  exists (k^-1 *: x^-1).
  by rewrite -!scalerAl -!scalerAr !scalerA !mulVr // !mulrV // scale1r.
exists (k *: (k *: x)^-1); split.
  apply: (mulrI Ukx).
  by rewrite mulr1 mulrA -scalerAr mulrV // -scalerAl mul1r.
apply: (mulIr Ukx).
by rewrite mul1r -mulrA -scalerAl mulVr // -scalerAr mulr1.
Qed.

Lemma invrZ k x : k \in unit -> x \in unit -> (k *: x)^-1 = k^-1 *: x^-1.
Proof.
move=> Uk Ux; have Ukx: (k *: x \in unit) by rewrite scaler_unit.
apply: (mulIr Ukx).
by rewrite mulVr // -scalerAl -scalerAr scalerA !mulVr // scale1r.
Qed.

Section ClosedPredicates.

Variables S : {pred A}.

Definition divalg_closed := [/\ 1 \in S, linear_closed S & divr_2closed S].

Lemma divalg_closedBdiv : divalg_closed -> divring_closed S.
Proof. by case=> S1 /linear_closedB. Qed.

Lemma divalg_closedZ : divalg_closed -> subalg_closed S.
Proof. by case=> S1 Slin Sdiv; split=> //; have [] := @divr_closedM A S. Qed.

End ClosedPredicates.

End UnitAlgebraTheory.

Module ClosedExports.

Notation oppr_closed := oppr_closed.
Notation addr_closed := addr_closed.
Notation mulr_closed := mulr_closed.
Notation zmod_closed := zmod_closed.
Notation smulr_closed := smulr_closed.
Notation invr_closed := invr_closed.
Notation divr_closed := divr_closed.
Notation scaler_closed := scaler_closed.
Notation linear_closed := linear_closed.
Notation submod_closed := submod_closed.
Notation semiring_closed := semiring_closed.
Notation subring_closed := subring_closed.
Notation sdivr_closed := sdivr_closed.
Notation subalg_closed := subalg_closed.
Notation divring_closed := divring_closed.
Notation divalg_closed := divalg_closed.

Coercion zmod_closedD : zmod_closed >-> nmod_closed.
Coercion zmod_closedN : zmod_closed >-> oppr_closed.
Coercion smulr_closedN : smulr_closed >-> oppr_closed.
Coercion smulr_closedM : smulr_closed >-> mulr_closed.
Coercion divr_closedV : divr_closed >-> invr_closed.
Coercion divr_closedM : divr_closed >-> mulr_closed.
Coercion submod_closedZ : submod_closed >-> scaler_closed.
Coercion submod_closedB : submod_closed >-> zmod_closed.
Coercion semiring_closedD : semiring_closed >-> addr_closed.
Coercion semiring_closedM : semiring_closed >-> mulr_closed.
Coercion subring_closedB : subring_closed >-> zmod_closed.
Coercion subring_closedM : subring_closed >-> smulr_closed.
Coercion subring_closed_semi : subring_closed >-> semiring_closed.
Coercion sdivr_closedM : sdivr_closed >-> smulr_closed.
Coercion sdivr_closed_div : sdivr_closed >-> divr_closed.
Coercion subalg_closedZ : subalg_closed >-> submod_closed.
Coercion subalg_closedBM : subalg_closed >-> subring_closed.
Coercion divring_closedBM : divring_closed >-> subring_closed.
Coercion divring_closed_div : divring_closed >-> sdivr_closed.
Coercion divalg_closedZ : divalg_closed >-> subalg_closed.
Coercion divalg_closedBdiv : divalg_closed >-> divring_closed.

End ClosedExports.

(* Reification of the theory of rings with units, in named style  *)
Section TermDef.

Variable R : Type.

Inductive term : Type :=
| Var of nat
| Const of R
| NatConst of nat
| Add of term & term
| Opp of term
| NatMul of term & nat
| Mul of term & term
| Inv of term
| Exp of term & nat.

Inductive formula : Type :=
| Bool of bool
| Equal of term & term
| Unit of term
| And of formula & formula
| Or of formula & formula
| Implies of formula & formula
| Not of formula
| Exists of nat & formula
| Forall of nat & formula.

End TermDef.

Bind Scope term_scope with term.
Bind Scope term_scope with formula.
Arguments Add {R} t1%T t2%T.
Arguments Opp {R} t1%T.
Arguments NatMul {R} t1%T n%N.
Arguments Mul {R} t1%T t2%T.
Arguments Inv {R} t1%T.
Arguments Exp {R} t1%T n%N.
Arguments Equal {R} t1%T t2%T.
Arguments Unit {R} t1%T.
Arguments And {R} f1%T f2%T.
Arguments Or {R} f1%T f2%T.
Arguments Implies {R} f1%T f2%T.
Arguments Not {R} f1%T.
Arguments Exists {R} i%N f1%T.
Arguments Forall {R} i%N f1%T.

Arguments Bool {R} b.
Arguments Const {R} x.

Notation True := (Bool true).
Notation False := (Bool false).

Local Notation "''X_' i" := (Var _ i) : term_scope.
Local Notation "n %:R" := (NatConst _ n) : term_scope.
Local Notation "x %:T" := (Const x) : term_scope.
Local Notation "0" := 0%:R%T : term_scope.
Local Notation "1" := 1%:R%T : term_scope.
Local Infix "+" := Add : term_scope.
Local Notation "- t" := (Opp t) : term_scope.
Local Notation "t - u" := (Add t (- u)) : term_scope.
Local Infix "*" := Mul : term_scope.
Local Infix "*+" := NatMul : term_scope.
Local Notation "t ^-1" := (Inv t) : term_scope.
Local Notation "t / u" := (Mul t u^-1) : term_scope.
Local Infix "^+" := Exp : term_scope.
Local Infix "==" := Equal : term_scope.
Local Infix "/\" := And : term_scope.
Local Infix "\/" := Or : term_scope.
Local Infix "==>" := Implies : term_scope.
Local Notation "~ f" := (Not f) : term_scope.
Local Notation "x != y" := (Not (x == y)) : term_scope.
Local Notation "''exists' ''X_' i , f" := (Exists i f) : term_scope.
Local Notation "''forall' ''X_' i , f" := (Forall i f) : term_scope.

Section Substitution.

Variable R : Type.

Fixpoint tsubst (t : term R) (s : nat * term R) :=
  match t with
  | 'X_i => if i == s.1 then s.2 else t
  | _%:T | _%:R => t
  | t1 + t2 => tsubst t1 s + tsubst t2 s
  | - t1 => - tsubst t1 s
  | t1 *+ n => tsubst t1 s *+ n
  | t1 * t2 => tsubst t1 s * tsubst t2 s
  | t1^-1 => (tsubst t1 s)^-1
  | t1 ^+ n => tsubst t1 s ^+ n
  end%T.

Fixpoint fsubst (f : formula R) (s : nat * term R) :=
  match f with
  | Bool _ => f
  | t1 == t2 => tsubst t1 s == tsubst t2 s
  | Unit t1 => Unit (tsubst t1 s)
  | f1 /\ f2 => fsubst f1 s /\ fsubst f2 s
  | f1 \/ f2 => fsubst f1 s \/ fsubst f2 s
  | f1 ==> f2 => fsubst f1 s ==> fsubst f2 s
  | ~ f1 => ~ fsubst f1 s
  | ('exists 'X_i, f1) => 'exists 'X_i, if i == s.1 then f1 else fsubst f1 s
  | ('forall 'X_i, f1) => 'forall 'X_i, if i == s.1 then f1 else fsubst f1 s
  end%T.

End Substitution.

Section EvalTerm.

Variable R : unitRingType.

(* Evaluation of a reified term into R a ring with units *)
Fixpoint eval (e : seq R) (t : term R) {struct t} : R :=
  match t with
  | ('X_i)%T => e`_i
  | (x%:T)%T => x
  | (n%:R)%T => n%:R
  | (t1 + t2)%T => eval e t1 + eval e t2
  | (- t1)%T => - eval e t1
  | (t1 *+ n)%T => eval e t1 *+ n
  | (t1 * t2)%T => eval e t1 * eval e t2
  | t1^-1%T => (eval e t1)^-1
  | (t1 ^+ n)%T => eval e t1 ^+ n
  end.

Definition same_env (e e' : seq R) := nth 0 e =1 nth 0 e'.

Lemma eq_eval e e' t : same_env e e' -> eval e t = eval e' t.
Proof. by move=> eq_e; elim: t => //= t1 -> // t2 ->. Qed.

Lemma eval_tsubst e t s :
  eval e (tsubst t s) = eval (set_nth 0 e s.1 (eval e s.2)) t.
Proof.
case: s => i u; elim: t => //=; do 2?[move=> ? -> //] => j.
by rewrite nth_set_nth /=; case: (_ == _).
Qed.

(* Evaluation of a reified formula *)
Fixpoint holds (e : seq R) (f : formula R) {struct f} : Prop :=
  match f with
  | Bool b => b
  | (t1 == t2)%T => eval e t1 = eval e t2
  | Unit t1 => eval e t1 \in unit
  | (f1 /\ f2)%T => holds e f1 /\ holds e f2
  | (f1 \/ f2)%T => holds e f1 \/ holds e f2
  | (f1 ==> f2)%T => holds e f1 -> holds e f2
  | (~ f1)%T => ~ holds e f1
  | ('exists 'X_i, f1)%T => exists x, holds (set_nth 0 e i x) f1
  | ('forall 'X_i, f1)%T => forall x, holds (set_nth 0 e i x) f1
  end.

Lemma same_env_sym e e' : same_env e e' -> same_env e' e.
Proof. exact: fsym. Qed.

(* Extensionality of formula evaluation *)
Lemma eq_holds e e' f : same_env e e' -> holds e f -> holds e' f.
Proof.
pose sv := set_nth (0 : R).
have eq_i i v e1 e2: same_env e1 e2 -> same_env (sv e1 i v) (sv e2 i v).
  by move=> eq_e j; rewrite !nth_set_nth /= eq_e.
elim: f e e' => //=.
- by move=> t1 t2 e e' eq_e; rewrite !(eq_eval _ eq_e).
- by move=> t e e' eq_e; rewrite (eq_eval _ eq_e).
- by move=> f1 IH1 f2 IH2 e e' eq_e; move/IH2: (eq_e); move/IH1: eq_e; tauto.
- by move=> f1 IH1 f2 IH2 e e' eq_e; move/IH2: (eq_e); move/IH1: eq_e; tauto.
- by move=> f1 IH1 f2 IH2 e e' eq_e f12; move/IH1: (same_env_sym eq_e); eauto.
- by move=> f1 IH1 e e'; move/same_env_sym; move/IH1; tauto.
- by move=> i f1 IH1 e e'; move/(eq_i i)=> eq_e [x f_ex]; exists x; eauto.
by move=> i f1 IH1 e e'; move/(eq_i i); eauto.
Qed.

(* Evaluation and substitution by a constant *)
Lemma holds_fsubst e f i v :
  holds e (fsubst f (i, v%:T)%T) <-> holds (set_nth 0 e i v) f.
Proof.
elim: f e => //=; do [
  by move=> *; rewrite !eval_tsubst
| move=> f1 IHf1 f2 IHf2 e; move: (IHf1 e) (IHf2 e); tauto
| move=> f IHf e; move: (IHf e); tauto
| move=> j f IHf e].
- case eq_ji: (j == i); first rewrite (eqP eq_ji).
    by split=> [] [x f_x]; exists x; rewrite set_set_nth eqxx in f_x *.
  split=> [] [x f_x]; exists x; move: f_x; rewrite set_set_nth eq_sym eq_ji;
     have:= IHf (set_nth 0 e j x); tauto.
case eq_ji: (j == i); first rewrite (eqP eq_ji).
  by split=> [] f_ x; move: (f_ x); rewrite set_set_nth eqxx.
split=> [] f_ x; move: (IHf (set_nth 0 e j x)) (f_ x);
  by rewrite set_set_nth eq_sym eq_ji; tauto.
Qed.

(* Boolean test selecting terms in the language of rings *)
Fixpoint rterm (t : term R) :=
  match t with
  | _^-1 => false
  | t1 + t2 | t1 * t2 => rterm t1 && rterm t2
  | - t1 | t1 *+ _ | t1 ^+ _ => rterm t1
  | _ => true
  end%T.

(* Boolean test selecting formulas in the theory of rings *)
Fixpoint rformula (f : formula R) :=
  match f with
  | Bool _ => true
  | t1 == t2 => rterm t1 && rterm t2
  | Unit t1 => false
  | f1 /\ f2 | f1 \/ f2 | f1 ==> f2 => rformula f1 && rformula f2
  | ~ f1 | ('exists 'X__, f1) | ('forall 'X__, f1) => rformula f1
  end%T.

(* Upper bound of the names used in a term *)
Fixpoint ub_var (t : term R) :=
  match t with
  | 'X_i => i.+1
  | t1 + t2 | t1 * t2 => maxn (ub_var t1) (ub_var t2)
  | - t1 | t1 *+ _ | t1 ^+ _ | t1^-1 => ub_var t1
  | _ => 0%N
  end%T.

(* Replaces inverses in the term t by fresh variables, accumulating the *)
(* substitution. *)
Fixpoint to_rterm (t : term R) (r : seq (term R)) (n : nat) {struct t} :=
  match t with
  | t1^-1 =>
    let: (t1', r1) := to_rterm t1 r n in
      ('X_(n + size r1), rcons r1 t1')
  | t1 + t2 =>
    let: (t1', r1) := to_rterm t1 r n in
    let: (t2', r2) := to_rterm t2 r1 n in
      (t1' + t2', r2)
  | - t1 =>
   let: (t1', r1) := to_rterm t1 r n in
     (- t1', r1)
  | t1 *+ m =>
   let: (t1', r1) := to_rterm t1 r n in
     (t1' *+ m, r1)
  | t1 * t2 =>
    let: (t1', r1) := to_rterm t1 r n in
    let: (t2', r2) := to_rterm t2 r1 n in
      (Mul t1' t2', r2)
  | t1 ^+ m =>
       let: (t1', r1) := to_rterm t1 r n in
     (t1' ^+ m, r1)
  | _ => (t, r)
  end%T.

Lemma to_rterm_id t r n : rterm t -> to_rterm t r n = (t, r).
Proof.
elim: t r n => //.
- by move=> t1 IHt1 t2 IHt2 r n /= /andP[rt1 rt2]; rewrite {}IHt1 // IHt2.
- by move=> t IHt r n /= rt; rewrite {}IHt.
- by move=> t IHt r n m /= rt; rewrite {}IHt.
- by move=> t1 IHt1 t2 IHt2 r n /= /andP[rt1 rt2]; rewrite {}IHt1 // IHt2.
- by move=> t IHt r n m /= rt; rewrite {}IHt.
Qed.

(* A ring formula stating that t1 is equal to 0 in the ring theory. *)
(* Also applies to non commutative rings.                           *)
Definition eq0_rform t1 :=
  let m := ub_var t1 in
  let: (t1', r1) := to_rterm t1 [::] m in
  let fix loop r i := match r with
  | [::] => t1' == 0
  | t :: r' =>
    let f := 'X_i * t == 1 /\ t * 'X_i == 1 in
     'forall 'X_i, (f \/ 'X_i == t /\ ~ ('exists 'X_i,  f)) ==> loop r' i.+1
  end%T
  in loop r1 m.

(* Transformation of a formula in the theory of rings with units into an *)
(* equivalent formula in the sub-theory of rings.                        *)
Fixpoint to_rform f :=
  match f with
  | Bool b => f
  | t1 == t2 => eq0_rform (t1 - t2)
  | Unit t1 => eq0_rform (t1 * t1^-1 - 1)
  | f1 /\ f2 => to_rform f1 /\ to_rform f2
  | f1 \/ f2 =>  to_rform f1 \/ to_rform f2
  | f1 ==> f2 => to_rform f1 ==> to_rform f2
  | ~ f1 => ~ to_rform f1
  | ('exists 'X_i, f1) => 'exists 'X_i, to_rform f1
  | ('forall 'X_i, f1) => 'forall 'X_i, to_rform f1
  end%T.

(* The transformation gives a ring formula. *)
Lemma to_rform_rformula f : rformula (to_rform f).
Proof.
suffices eq0_ring t1: rformula (eq0_rform t1) by elim: f => //= => f1 ->.
rewrite /eq0_rform; move: (ub_var t1) => m; set tr := _ m.
suffices: all rterm (tr.1 :: tr.2).
  case: tr => {}t1 r /= /andP[t1_r].
  by elim: r m => [|t r IHr] m; rewrite /= ?andbT // => /andP[->]; apply: IHr.
have: all rterm [::] by [].
rewrite {}/tr; elim: t1 [::] => //=.
- move=> t1 IHt1 t2 IHt2 r.
  move/IHt1; case: to_rterm => {r IHt1}t1 r /= /andP[t1_r].
  move/IHt2; case: to_rterm => {r IHt2}t2 r /= /andP[t2_r].
  by rewrite t1_r t2_r.
- by move=> t1 IHt1 r /IHt1; case: to_rterm.
- by move=> t1 IHt1 n r /IHt1; case: to_rterm.
- move=> t1 IHt1 t2 IHt2 r.
  move/IHt1; case: to_rterm => {r IHt1}t1 r /= /andP[t1_r].
  move/IHt2; case: to_rterm => {r IHt2}t2 r /= /andP[t2_r].
  by rewrite t1_r t2_r.
- move=> t1 IHt1 r.
  by move/IHt1; case: to_rterm => {r IHt1}t1 r /=; rewrite all_rcons.
- by move=> t1 IHt1 n r /IHt1; case: to_rterm.
Qed.

(* Correctness of the transformation. *)
Lemma to_rformP e f : holds e (to_rform f) <-> holds e f.
Proof.
suffices{e f} equal0_equiv e t1 t2:
  holds e (eq0_rform (t1 - t2)) <-> (eval e t1 == eval e t2).
- elim: f e => /=; try tauto.
  + move=> t1 t2 e.
    by split; [move/equal0_equiv/eqP | move/eqP/equal0_equiv].
  + by move=> t1 e; rewrite unitrE; apply: equal0_equiv.
  + by move=> f1 IHf1 f2 IHf2 e; move: (IHf1 e) (IHf2 e); tauto.
  + by move=> f1 IHf1 f2 IHf2 e; move: (IHf1 e) (IHf2 e); tauto.
  + by move=> f1 IHf1 f2 IHf2 e; move: (IHf1 e) (IHf2 e); tauto.
  + by move=> f1 IHf1 e; move: (IHf1 e); tauto.
  + by move=> n f1 IHf1 e; split=> [] [x] /IHf1; exists x.
  + by move=> n f1 IHf1 e; split=> Hx x; apply/IHf1.
rewrite -(add0r (eval e t2)) -(can2_eq (subrK _) (addrK _)).
rewrite -/(eval e (t1 - t2)); move: (t1 - t2)%T => {t1 t2} t.
have sub_var_tsubst s t0: s.1 >= ub_var t0 -> tsubst t0 s = t0.
  elim: t0 {t} => //=.
  - by move=> n; case: ltngtP.
  - by move=> t1 IHt1 t2 IHt2; rewrite geq_max => /andP[/IHt1-> /IHt2->].
  - by move=> t1 IHt1 /IHt1->.
  - by move=> t1 IHt1 n /IHt1->.
  - by move=> t1 IHt1 t2 IHt2; rewrite geq_max => /andP[/IHt1-> /IHt2->].
  - by move=> t1 IHt1 /IHt1->.
  - by move=> t1 IHt1 n /IHt1->.
pose fix rsub t' m r : term R :=
  if r is u :: r' then tsubst (rsub t' m.+1 r') (m, u^-1)%T else t'.
pose fix ub_sub m r : Prop :=
  if r is u :: r' then ub_var u <= m /\ ub_sub m.+1 r' else true.
suffices{t} rsub_to_r t r0 m: m >= ub_var t -> ub_sub m r0 ->
  let: (t', r) := to_rterm t r0 m in
  [/\ take (size r0) r = r0,
      ub_var t' <= m + size r, ub_sub m r & rsub t' m r = t].
- have:= rsub_to_r t [::] _ (leqnn _); rewrite /eq0_rform.
  case: (to_rterm _ _ _) => [t1' r1] [//|_ _ ub_r1 def_t].
  rewrite -{2}def_t {def_t}.
  elim: r1 (ub_var t) e ub_r1 => [|u r1 IHr1] m e /= => [_|[ub_u ub_r1]].
    by split=> /eqP.
  rewrite eval_tsubst /=; set y := eval e u; split=> t_eq0.
    apply/IHr1=> //; apply: t_eq0.
    rewrite nth_set_nth /= eqxx -(eval_tsubst e u (m, Const _)).
    rewrite sub_var_tsubst //= -/y.
    case Uy: (y \in unit); [left | right]; first by rewrite mulVr ?divrr.
    split=> [|[z]]; first by rewrite invr_out ?Uy.
    rewrite nth_set_nth /= eqxx.
    rewrite -!(eval_tsubst _ _ (m, Const _)) !sub_var_tsubst // -/y => yz1.
    by case/unitrP: Uy; exists z.
  move=> x def_x; apply/IHr1=> //; suff ->: x = y^-1 by []; move: def_x.
  rewrite nth_set_nth /= eqxx -(eval_tsubst e u (m, Const _)).
  rewrite sub_var_tsubst //= -/y; case=> [[xy1 yx1] | [xy nUy]].
    by rewrite -[y^-1]mul1r -[1]xy1 mulrK //; apply/unitrP; exists x.
  rewrite invr_out //; apply/unitrP=> [[z yz1]]; case: nUy; exists z.
  rewrite nth_set_nth /= eqxx -!(eval_tsubst _ _ (m, _%:T)%T).
  by rewrite !sub_var_tsubst.
have rsub_id r t0 n: ub_var t0 <= n -> rsub t0 n r = t0.
  by elim: r n => //= t1 r IHr n let0n; rewrite IHr ?sub_var_tsubst ?leqW.
have rsub_acc r s t1 m1:
  ub_var t1 <= m1 + size r -> rsub t1 m1 (r ++ s) = rsub t1 m1 r.
  elim: r t1 m1 => [|t1 r IHr] t2 m1 /=; first by rewrite addn0; apply: rsub_id.
  by move=> letmr; rewrite IHr ?addSnnS.
elim: t r0 m => /=; try do [
  by move=> n r m hlt hub; rewrite take_size (ltn_addr _ hlt) rsub_id
| by move=> n r m hlt hub; rewrite leq0n take_size rsub_id
| move=> t1 IHt1 t2 IHt2 r m; rewrite geq_max; case/andP=> hub1 hub2 hmr;
  case: to_rterm {hub1 hmr}(IHt1 r m hub1 hmr) => t1' r1;
  case=> htake1 hub1' hsub1 <-;
  case: to_rterm {IHt2 hub2 hsub1}(IHt2 r1 m hub2 hsub1) => t2' r2 /=;
  rewrite geq_max; case=> htake2 -> hsub2 /= <-;
  rewrite -{1 2}(cat_take_drop (size r1) r2) htake2; set r3 := drop _ _;
  rewrite size_cat addnA (leq_trans _ (leq_addr _ _)) //;
  split=> {hsub2}//;
   first by [rewrite takel_cat // -htake1 size_take geq_min leqnn orbT];
  rewrite -(rsub_acc r1 r3 t1') {hub1'}// -{htake1}htake2 {r3}cat_take_drop;
  by elim: r2 m => //= u r2 IHr2 m; rewrite IHr2
| do [ move=> t1 IHt1 r m; do 2!move=> /IHt1{}IHt1
     | move=> t1 IHt1 n r m; do 2!move=> /IHt1{}IHt1];
  case: to_rterm IHt1 => t1' r1 [-> -> hsub1 <-]; split=> {hsub1}//;
  by elim: r1 m => //= u r1 IHr1 m; rewrite IHr1].
move=> t1 IH r m letm /IH {IH} /(_ letm) {letm}.
case: to_rterm => t1' r1 /= [def_r ub_t1' ub_r1 <-].
rewrite size_rcons addnS leqnn -{1}cats1 takel_cat ?def_r; last first.
  by rewrite -def_r size_take geq_min leqnn orbT.
elim: r1 m ub_r1 ub_t1' {def_r} => /= [|u r1 IHr1] m => [_|[->]].
  by rewrite addn0 eqxx.
by rewrite -addSnnS => /IHr1 IH /IH[_ _ ub_r1 ->].
Qed.

(* Boolean test selecting formulas which describe a constructible set, *)
(* i.e. formulas without quantifiers.                                  *)

(* The quantifier elimination check. *)
Fixpoint qf_form (f : formula R) :=
  match f with
  | Bool _ | _ == _ | Unit _ => true
  | f1 /\ f2 | f1 \/ f2 | f1 ==> f2 => qf_form f1 && qf_form f2
  | ~ f1 => qf_form f1
  | _ => false
  end%T.

(* Boolean holds predicate for quantifier free formulas *)
Definition qf_eval e := fix loop (f : formula R) : bool :=
  match f with
  | Bool b => b
  | t1 == t2 => (eval e t1 == eval e t2)%bool
  | Unit t1 => eval e t1 \in unit
  | f1 /\ f2 => loop f1 && loop f2
  | f1 \/ f2 => loop f1 || loop f2
  | f1 ==> f2 => (loop f1 ==> loop f2)%bool
  | ~ f1 => ~~ loop f1
  |_ => false
  end%T.

(* qf_eval is equivalent to holds *)
Lemma qf_evalP e f : qf_form f -> reflect (holds e f) (qf_eval e f).
Proof.
elim: f => //=; try by move=> *; apply: idP.
- by move=> t1 t2 _; apply: eqP.
- move=> f1 IHf1 f2 IHf2 /= /andP[/IHf1[] f1T]; last by right; case.
  by case/IHf2; [left | right; case].
- move=> f1 IHf1 f2 IHf2 /= /andP[/IHf1[] f1F]; first by do 2 left.
  by case/IHf2; [left; right | right; case].
- move=> f1 IHf1 f2 IHf2 /= /andP[/IHf1[] f1T]; last by left.
  by case/IHf2; [left | right; move/(_ f1T)].
by move=> f1 IHf1 /IHf1[]; [right | left].
Qed.

Implicit Type bc : seq (term R) * seq (term R).

(* Quantifier-free formula are normalized into DNF. A DNF is *)
(* represented by the type seq (seq (term R) * seq (term R)), where we *)
(* separate positive and negative literals *)

(* DNF preserving conjunction *)
Definition and_dnf bcs1 bcs2 :=
  \big[cat/nil]_(bc1 <- bcs1)
     map (fun bc2 => (bc1.1 ++ bc2.1, bc1.2 ++ bc2.2)) bcs2.

(* Computes a DNF from a qf ring formula *)
Fixpoint qf_to_dnf (f : formula R) (neg : bool) {struct f} :=
  match f with
  | Bool b => if b (+) neg then [:: ([::], [::])] else [::]
  | t1 == t2 => [:: if neg then ([::], [:: t1 - t2]) else ([:: t1 - t2], [::])]
  | f1 /\ f2 => (if neg then cat else and_dnf) [rec f1, neg] [rec f2, neg]
  | f1 \/ f2 => (if neg then and_dnf else cat) [rec f1, neg] [rec f2, neg]
  | f1 ==> f2 => (if neg then and_dnf else cat) [rec f1, ~~ neg] [rec f2, neg]
  | ~ f1 => [rec f1, ~~ neg]
  | _ =>  if neg then [:: ([::], [::])] else [::]
  end%T where "[ 'rec' f , neg ]" := (qf_to_dnf f neg).

(* Conversely, transforms a DNF into a formula *)
Definition dnf_to_form :=
  let pos_lit t := And (t == 0) in let neg_lit t := And (t != 0) in
  let cls bc := Or (foldr pos_lit True bc.1 /\ foldr neg_lit True bc.2) in
  foldr cls False.

(* Catenation of dnf is the Or of formulas *)
Lemma cat_dnfP e bcs1 bcs2 :
  qf_eval e (dnf_to_form (bcs1 ++ bcs2))
    = qf_eval e (dnf_to_form bcs1 \/ dnf_to_form bcs2).
Proof.
by elim: bcs1 => //= bc1 bcs1 IH1; rewrite -orbA; congr orb; rewrite IH1.
Qed.

(* and_dnf is the And of formulas *)
Lemma and_dnfP e bcs1 bcs2 :
  qf_eval e (dnf_to_form (and_dnf bcs1 bcs2))
   = qf_eval e (dnf_to_form bcs1 /\ dnf_to_form bcs2).
Proof.
elim: bcs1 => [|bc1 bcs1 IH1] /=; first by rewrite /and_dnf big_nil.
rewrite /and_dnf big_cons -/(and_dnf bcs1 bcs2) cat_dnfP  /=.
rewrite {}IH1 /= andb_orl; congr orb.
elim: bcs2 bc1 {bcs1} => [|bc2 bcs2 IH] bc1 /=; first by rewrite andbF.
rewrite {}IH /= andb_orr; congr orb => {bcs2}.
suffices aux (l1 l2 : seq (term R)) g : let redg := foldr (And \o g) True in
  qf_eval e (redg (l1 ++ l2)) = qf_eval e (redg l1 /\ redg l2)%T.
+ by rewrite 2!aux /= 2!andbA -andbA -andbCA andbA andbCA andbA.
by elim: l1 => [| t1 l1 IHl1] //=; rewrite -andbA IHl1.
Qed.

Lemma qf_to_dnfP e :
  let qev f b := qf_eval e (dnf_to_form (qf_to_dnf f b)) in
  forall f, qf_form f && rformula f -> qev f false = qf_eval e f.
Proof.
move=> qev; have qevT f: qev f true = ~~ qev f false.
  rewrite {}/qev; elim: f => //=; do [by case | move=> f1 IH1 f2 IH2 | ].
  - by move=> t1 t2; rewrite !andbT !orbF.
  - by rewrite and_dnfP cat_dnfP negb_and -IH1 -IH2.
  - by rewrite and_dnfP cat_dnfP negb_or -IH1 -IH2.
  - by rewrite and_dnfP cat_dnfP /= negb_or IH1 -IH2 negbK.
  by move=> t1 ->; rewrite negbK.
rewrite /qev; elim=> //=; first by case.
- by move=> t1 t2 _; rewrite subr_eq0 !andbT orbF.
- move=> f1 IH1 f2 IH2; rewrite andbCA -andbA andbCA andbA; case/andP.
  by rewrite and_dnfP /= => /IH1-> /IH2->.
- move=> f1 IH1 f2 IH2; rewrite andbCA -andbA andbCA andbA; case/andP.
  by rewrite cat_dnfP /= => /IH1-> => /IH2->.
- move=> f1 IH1 f2 IH2; rewrite andbCA -andbA andbCA andbA; case/andP.
  by rewrite cat_dnfP /= [qf_eval _ _]qevT -implybE => /IH1 <- /IH2->.
by move=> f1 IH1 /IH1 <-; rewrite -qevT.
Qed.

Lemma dnf_to_form_qf bcs : qf_form (dnf_to_form bcs).
Proof.
by elim: bcs => //= [[clT clF] _ ->] /=; elim: clT => //=; elim: clF.
Qed.

Definition dnf_rterm cl := all rterm cl.1 && all rterm cl.2.

Lemma qf_to_dnf_rterm f b : rformula f -> all dnf_rterm (qf_to_dnf f b).
Proof.
set ok := all dnf_rterm.
have cat_ok bcs1 bcs2: ok bcs1 -> ok bcs2 -> ok (bcs1 ++ bcs2).
  by move=> ok1 ok2; rewrite [ok _]all_cat; apply/andP.
have and_ok bcs1 bcs2: ok bcs1 -> ok bcs2 -> ok (and_dnf bcs1 bcs2).
  rewrite /and_dnf unlock; elim: bcs1 => //= cl1 bcs1 IH1; rewrite -andbA.
  case/and3P=> ok11 ok12 ok1 ok2; rewrite cat_ok ?{}IH1 {bcs1 ok1}//.
  elim: bcs2 ok2 => //= cl2 bcs2 IH2 /andP[ok2 /IH2->].
  by rewrite /dnf_rterm !all_cat ok11 ok12 /= !andbT.
elim: f b => //=; [ by do 2!case | | | | | by auto | | ];
  try by repeat case/andP || intro; case: ifP; auto.
by rewrite /dnf_rterm => ?? [] /= ->.
Qed.

Lemma dnf_to_rform bcs : rformula (dnf_to_form bcs) = all dnf_rterm bcs.
Proof.
elim: bcs => //= [[cl1 cl2] bcs ->]; rewrite {2}/dnf_rterm /=; congr (_ && _).
by congr andb; [elim: cl1 | elim: cl2] => //= t cl ->; rewrite andbT.
Qed.

Section If.

Variables (pred_f then_f else_f : formula R).

Definition If := (pred_f /\ then_f \/ ~ pred_f /\ else_f)%T.

Lemma If_form_qf :
  qf_form pred_f -> qf_form then_f -> qf_form else_f -> qf_form If.
Proof. by move=> /= -> -> ->. Qed.

Lemma If_form_rf :
  rformula pred_f -> rformula then_f -> rformula else_f -> rformula If.
Proof. by move=> /= -> -> ->. Qed.

Lemma eval_If e :
  let ev := qf_eval e in ev If = (if ev pred_f then ev then_f else ev else_f).
Proof. by rewrite /=; case: ifP => _; rewrite ?orbF. Qed.

End If.

Section Pick.

Variables (I : finType) (pred_f then_f : I -> formula R) (else_f : formula R).

Definition Pick :=
  \big[Or/False]_(p : {ffun pred I})
    ((\big[And/True]_i (if p i then pred_f i else ~ pred_f i))
    /\ (if pick p is Some i then then_f i else else_f))%T.

Lemma Pick_form_qf :
   (forall i, qf_form (pred_f i)) ->
   (forall i, qf_form (then_f i)) ->
    qf_form else_f ->
  qf_form Pick.
Proof.
move=> qfp qft qfe; have mA := (big_morph qf_form) true andb.
rewrite mA // big1 //= => p _.
rewrite mA // big1 => [|i _]; first by case: pick.
by rewrite fun_if if_same /= qfp.
Qed.

Lemma eval_Pick e (qev := qf_eval e) :
  let P i := qev (pred_f i) in
  qev Pick = (if pick P is Some i then qev (then_f i) else qev else_f).
Proof.
move=> P; rewrite ((big_morph qev) false orb) //= big_orE /=.
apply/existsP/idP=> [[p] | true_at_P].
  rewrite ((big_morph qev) true andb) //= big_andE /=.
  case/andP=> /forallP-eq_p_P.
  rewrite (@eq_pick _ _ P) => [|i]; first by case: pick.
  by move/(_ i): eq_p_P => /=; case: (p i) => //= /negPf.
exists [ffun i => P i] => /=; apply/andP; split.
  rewrite ((big_morph qev) true andb) //= big_andE /=.
  by apply/forallP=> i; rewrite /= ffunE; case Pi: (P i) => //=; apply: negbT.
rewrite (@eq_pick _ _ P) => [|i]; first by case: pick true_at_P.
by rewrite ffunE.
Qed.

End Pick.

Section MultiQuant.

Variable f : formula R.
Implicit Types (I : seq nat) (e : seq R).

Lemma foldExistsP I e :
  (exists2 e', {in [predC I], same_env e e'} & holds e' f)
    <-> holds e (foldr Exists f I).
Proof.
elim: I e => /= [|i I IHi] e.
  by split=> [[e' eq_e] |]; [apply: eq_holds => i; rewrite eq_e | exists e].
split=> [[e' eq_e f_e'] | [x]]; last set e_x := set_nth 0 e i x.
  exists e'`_i; apply/IHi; exists e' => // j.
  by have:= eq_e j; rewrite nth_set_nth /= !inE; case: eqP => // ->.
case/IHi=> e' eq_e f_e'; exists e' => // j.
by have:= eq_e j; rewrite nth_set_nth /= !inE; case: eqP.
Qed.

Lemma foldForallP I e :
  (forall e', {in [predC I], same_env e e'} -> holds e' f)
    <-> holds e (foldr Forall f I).
Proof.
elim: I e => /= [|i I IHi] e.
  by split=> [|f_e e' eq_e]; [apply | apply: eq_holds f_e => i; rewrite eq_e].
split=> [f_e' x | f_e e' eq_e]; first set e_x := set_nth 0 e i x.
  apply/IHi=> e' eq_e; apply: f_e' => j.
  by have:= eq_e j; rewrite nth_set_nth /= !inE; case: eqP.
move/IHi: (f_e e'`_i); apply=> j.
by have:= eq_e j; rewrite nth_set_nth /= !inE; case: eqP => // ->.
Qed.

End MultiQuant.

End EvalTerm.

Prenex Implicits dnf_rterm.

Definition integral_domain_axiom (R : pzRingType) :=
  forall x y : R, x * y = 0 -> (x == 0) || (y == 0).

HB.mixin Record ComUnitRing_isIntegral R of ComUnitRing R := {
  mulf_eq0_subproof : integral_domain_axiom R;
}.

#[mathcomp(axiom="integral_domain_axiom"), short(type="idomainType")]
HB.structure Definition IntegralDomain :=
  {R of ComUnitRing_isIntegral R & ComUnitRing R}.

Module IntegralDomainExports.
Bind Scope ring_scope with IntegralDomain.sort.
End IntegralDomainExports.
HB.export IntegralDomainExports.

Section IntegralDomainTheory.

Variable R : idomainType.
Implicit Types x y : R.

Lemma mulf_eq0 x y : (x * y == 0) = (x == 0) || (y == 0).
Proof.
apply/eqP/idP; first exact: mulf_eq0_subproof.
by case/pred2P=> ->; rewrite (mulr0, mul0r).
Qed.

Lemma prodf_eq0 (I : finType) (P : pred I) (F : I -> R) :
  reflect (exists2 i, P i & (F i == 0)) (\prod_(i | P i) F i == 0).
Proof.
apply: (iffP idP) => [|[i Pi /eqP Fi0]]; last first.
  by rewrite (bigD1 i) //= Fi0 mul0r.
elim: (index_enum _) => [|i r IHr]; first by rewrite big_nil oner_eq0.
rewrite big_cons /=; have [Pi | _] := ifP; last exact: IHr.
by rewrite mulf_eq0; case/orP=> // Fi0; exists i.
Qed.

Lemma prodf_seq_eq0 I r (P : pred I) (F : I -> R) :
  (\prod_(i <- r | P i) F i == 0) = has (fun i => P i && (F i == 0)) r.
Proof. by rewrite (big_morph _ mulf_eq0 (oner_eq0 _)) big_has_cond. Qed.

Lemma mulf_neq0 x y : x != 0 -> y != 0 -> x * y != 0.
Proof. by move=> x0 y0; rewrite mulf_eq0; apply/norP. Qed.

Lemma prodf_neq0 (I : finType) (P : pred I) (F : I -> R) :
  reflect (forall i, P i -> (F i != 0)) (\prod_(i | P i) F i != 0).
Proof. by rewrite (sameP (prodf_eq0 _ _) exists_inP); apply: exists_inPn. Qed.

Lemma prodf_seq_neq0 I r (P : pred I) (F : I -> R) :
  (\prod_(i <- r | P i) F i != 0) = all (fun i => P i ==> (F i != 0)) r.
Proof.
rewrite prodf_seq_eq0 -all_predC; apply: eq_all => i /=.
by rewrite implybE negb_and.
Qed.

Lemma expf_eq0 x n : (x ^+ n == 0) = (n > 0) && (x == 0).
Proof.
elim: n => [|n IHn]; first by rewrite oner_eq0.
by rewrite exprS mulf_eq0 IHn andKb.
Qed.

Lemma sqrf_eq0 x : (x ^+ 2 == 0) = (x == 0). Proof. exact: expf_eq0. Qed.

Lemma expf_neq0 x m : x != 0 -> x ^+ m != 0.
Proof. by move=> x_nz; rewrite expf_eq0; apply/nandP; right. Qed.

Lemma natf_neq0 n : (n%:R != 0 :> R) = (char R)^'.-nat n.
Proof.
have [-> | /prod_prime_decomp->] := posnP n; first by rewrite eqxx.
rewrite !big_seq; elim/big_rec: _ => [|[p e] s /=]; first by rewrite oner_eq0.
case/mem_prime_decomp=> p_pr _ _; rewrite pnatM pnatX eqn0Ngt orbC => <-.
by rewrite natrM natrX mulf_eq0 expf_eq0 negb_or negb_and pnatE ?inE p_pr.
Qed.

Lemma natf0_char n : n > 0 -> n%:R == 0 :> R -> exists p, p \in char R.
Proof.
move=> n_gt0 nR_0; exists (pdiv n`_(char R)).
apply: pnatP (pdiv_dvd _); rewrite ?part_pnat // ?pdiv_prime //.
by rewrite ltn_neqAle eq_sym partn_eq1 // -natf_neq0 nR_0 /=.
Qed.

Lemma charf'_nat n : (char R)^'.-nat n = (n%:R != 0 :> R).
Proof.
have [-> | n_gt0] := posnP n; first by rewrite eqxx.
apply/idP/idP => [|nz_n]; last first.
  by apply/pnatP=> // p p_pr p_dvd_n; apply: contra nz_n => /dvdn_charf <-.
apply: contraL => n0; have [// | p charRp] := natf0_char _ n0.
have [p_pr _] := andP charRp; rewrite (eq_pnat _ (eq_negn (charf_eq charRp))).
by rewrite p'natE // (dvdn_charf charRp) n0.
Qed.

Lemma charf0P : char R =i pred0 <-> (forall n, (n%:R == 0 :> R) = (n == 0)%N).
Proof.
split=> charF0 n; last by rewrite !inE charF0 andbC; case: eqP => // ->.
have [-> | n_gt0] := posnP; first exact: eqxx.
by apply/negP; case/natf0_char=> // p; rewrite charF0.
Qed.

Lemma eqf_sqr x y : (x ^+ 2 == y ^+ 2) = (x == y) || (x == - y).
Proof. by rewrite -subr_eq0 subr_sqr mulf_eq0 subr_eq0 addr_eq0. Qed.

Lemma mulfI x : x != 0 -> injective ( *%R x).
Proof.
move=> nz_x y z; apply: contra_eq => neq_yz.
by rewrite -subr_eq0 -mulrBr mulf_neq0 ?subr_eq0.
Qed.

Lemma mulIf x : x != 0 -> injective ( *%R^~ x).
Proof. by move=> nz_x y z; rewrite -!(mulrC x); apply: mulfI. Qed.

Lemma divfI x : x != 0 -> injective (fun y => x / y).
Proof. by move/mulfI/inj_comp; apply; apply: invr_inj. Qed.

Lemma divIf y : y != 0 -> injective (fun x => x / y).
Proof. by rewrite -invr_eq0; apply: mulIf. Qed.

Lemma sqrf_eq1 x : (x ^+ 2 == 1) = (x == 1) || (x == -1).
Proof. by rewrite -subr_eq0 subr_sqr_1 mulf_eq0 subr_eq0 addr_eq0. Qed.

Lemma expfS_eq1 x n :
  (x ^+ n.+1 == 1) = (x == 1) || (\sum_(i < n.+1) x ^+ i == 0).
Proof. by rewrite -![_ == 1]subr_eq0 subrX1 mulf_eq0. Qed.

Lemma lregP x : reflect (lreg x) (x != 0).
Proof. by apply: (iffP idP) => [/mulfI | /lreg_neq0]. Qed.

Lemma rregP x : reflect (rreg x) (x != 0).
Proof. by apply: (iffP idP) => [/mulIf | /rreg_neq0]. Qed.

#[export]
HB.instance Definition _ := IntegralDomain.on R^o.

End IntegralDomainTheory.

Arguments lregP {R x}.
Arguments rregP {R x}.

Definition field_axiom (R : unitRingType) := forall x : R, x != 0 -> x \in unit.

HB.mixin Record UnitRing_isField R of UnitRing R := {
  fieldP : field_axiom R;
}.

#[mathcomp(axiom="field_axiom"), short(type="fieldType")]
HB.structure Definition Field := { R of IntegralDomain R & UnitRing_isField R }.

Module FieldExports.
Bind Scope ring_scope with Field.sort.
End FieldExports.
HB.export FieldExports.

#[export] HB.instance Definition regular_field (F : fieldType) := Field.on F^o.

Lemma IdomainMixin (R : unitRingType): Field.axiom R -> IntegralDomain.axiom R.
Proof.
move=> m x y xy0; apply/norP=> [[]] /m Ux /m.
by rewrite -(unitrMr _ Ux) xy0 unitr0.
Qed.

HB.factory Record ComUnitRing_isField R of ComUnitRing R := {
  fieldP : field_axiom R;
}.
HB.builders Context R of ComUnitRing_isField R.
HB.instance Definition _ :=
  ComUnitRing_isIntegral.Build R (IdomainMixin fieldP).
HB.instance Definition _ := UnitRing_isField.Build R fieldP.
HB.end.

HB.factory Record ComNzRing_isField R of ComNzRing R := {
  inv : R -> R;
  mulVf : forall x, x != 0 -> inv x * x = 1;
  invr0 : inv 0 = 0;
}.

Module ComRing_isField.
#[deprecated(since="mathcomp 2.4.0",
             note="Use ComNzRing_isField.Build instead.")]
Notation Build R := (ComNzRing_isField.Build R) (only parsing).
End ComRing_isField.

#[deprecated(since="mathcomp 2.4.0",
             note="Use ComNzRing_isField instead.")]
Notation ComRing_isField R := (ComNzRing_isField R) (only parsing).

HB.builders Context R of ComNzRing_isField R.

Fact intro_unit (x y : R) : y * x = 1 -> x != 0.
Proof.
move=> yx1; apply: contraNneq (@oner_neq0 R) => x0.
by rewrite -yx1 x0 mulr0.
Qed.

Fact inv_out : {in predC (predC1 0), inv =1 id}.
Proof. by move=> x /negbNE/eqP->; exact: invr0. Qed.

HB.instance Definition _ : ComNzRing_hasMulInverse R :=
  ComNzRing_hasMulInverse.Build R mulVf intro_unit inv_out.

HB.instance Definition _ : ComUnitRing_isField R :=
  ComUnitRing_isField.Build R (fun x x_neq_0 => x_neq_0).

HB.end.

Section FieldTheory.

Variable F : fieldType.
Implicit Types x y : F.

Lemma unitfE x : (x \in unit) = (x != 0).
Proof. by apply/idP/idP=> [/(memPn _)-> | /fieldP]; rewrite ?unitr0. Qed.

Lemma mulVf x : x != 0 -> x^-1 * x = 1.
Proof. by rewrite -unitfE; apply: mulVr. Qed.
Lemma divff x : x != 0 -> x / x = 1.
Proof. by rewrite -unitfE; apply: divrr. Qed.
Definition mulfV := divff.
Lemma mulKf x : x != 0 -> cancel ( *%R x) ( *%R x^-1).
Proof. by rewrite -unitfE; apply: mulKr. Qed.
Lemma mulVKf x : x != 0 -> cancel ( *%R x^-1) ( *%R x).
Proof. by rewrite -unitfE; apply: mulVKr. Qed.
Lemma mulfK x : x != 0 -> cancel ( *%R^~ x) ( *%R^~ x^-1).
Proof. by rewrite -unitfE; apply: mulrK. Qed.
Lemma mulfVK x : x != 0 -> cancel ( *%R^~ x^-1) ( *%R^~ x).
Proof. by rewrite -unitfE; apply: divrK. Qed.
Definition divfK := mulfVK.

Lemma invfM : {morph @inv F : x y / x * y}.
Proof.
move=> x y; have [->|nzx] := eqVneq x 0; first by rewrite !(mul0r, invr0).
have [->|nzy] := eqVneq y 0; first by rewrite !(mulr0, invr0).
by rewrite mulrC invrM ?unitfE.
Qed.

Lemma invf_div x y : (x / y)^-1 = y / x.
Proof. by rewrite invfM invrK mulrC. Qed.

Lemma divKf x : x != 0 -> involutive (fun y => x / y).
Proof. by move=> nz_x y; rewrite invf_div mulrC divfK. Qed.

Lemma expfB_cond m n x : (x == 0) + n <= m -> x ^+ (m - n) = x ^+ m / x ^+ n.
Proof.
move/subnK=> <-; rewrite addnA addnK !exprD.
have [-> | nz_x] := eqVneq; first by rewrite !mulr0 !mul0r.
by rewrite mulfK ?expf_neq0.
Qed.

Lemma expfB m n x : n < m -> x ^+ (m - n) = x ^+ m / x ^+ n.
Proof. by move=> lt_n_m; apply: expfB_cond; case: eqP => // _; apply: ltnW. Qed.

Lemma prodfV I r (P : pred I) (E : I -> F) :
  \prod_(i <- r | P i) (E i)^-1 = (\prod_(i <- r | P i) E i)^-1.
Proof. by rewrite (big_morph _ invfM (invr1 F)). Qed.

Lemma prodf_div I r (P : pred I) (E D : I -> F) :
  \prod_(i <- r | P i) (E i / D i) =
     \prod_(i <- r | P i) E i / \prod_(i <- r | P i) D i.
Proof. by rewrite big_split prodfV. Qed.

Lemma telescope_prodf n m (f : nat -> F) :
    (forall k, n < k < m -> f k != 0) -> n < m ->
  \prod_(n <= k < m) (f k.+1 / f k) = f m / f n.
Proof.
move=> nz_f ltnm; apply: invr_inj; rewrite prodf_div !invf_div -prodf_div.
by apply: telescope_prodr => // k /nz_f; rewrite unitfE.
Qed.

Lemma telescope_prodf_eq n m (f u : nat -> F) :
    (forall k, n < k < m -> f k != 0) -> n < m ->
    (forall k, n <= k < m -> u k = f k.+1 / f k) ->
  \prod_(n <= k < m) u k = f m / f n.
Proof.
by move=> ? ? uE; under eq_big_nat do rewrite uE //=; exact: telescope_prodf.
Qed.

Lemma addf_div x1 y1 x2 y2 :
  y1 != 0 -> y2 != 0 -> x1 / y1 + x2 / y2 = (x1 * y2 + x2 * y1) / (y1 * y2).
Proof. by move=> nzy1 nzy2; rewrite invfM mulrDl !mulrA mulrAC !mulfK. Qed.

Lemma mulf_div x1 y1 x2 y2 : (x1 / y1) * (x2 / y2) = (x1 * x2) / (y1 * y2).
Proof. by rewrite mulrACA -invfM. Qed.

Lemma eqr_div x y z t : y != 0 -> t != 0 -> (x / y == z / t) = (x * t == z * y).
Proof.
move=> yD0 tD0; rewrite -[x in RHS](divfK yD0) -[z in RHS](divfK tD0) mulrAC.
by apply/eqP/eqP => [->|/(mulIf yD0)/(mulIf tD0)].
Qed.

Lemma eqr_sum_div I r P (f : I -> F) c a : c != 0 ->
  \big[+%R/0]_(x <- r | P x) (f x / c) == a
  = (\big[+%R/0]_(x <- r | P x) f x == a * c).
Proof.
by move=> ?; rewrite -mulr_suml -(divr1 a) eqr_div ?oner_eq0// mulr1 divr1.
Qed.

Lemma char0_natf_div :
  char F =i pred0 -> forall m d, d %| m -> (m %/ d)%:R = m%:R / d%:R :> F.
Proof.
move/charf0P=> char0F m [|d] d_dv_m; first by rewrite divn0 invr0 mulr0.
by rewrite natr_div // unitfE char0F.
Qed.

Section FieldMorphismInj.

Variables (R : nzRingType) (f : {rmorphism F -> R}).

Lemma fmorph_eq0 x : (f x == 0) = (x == 0).
Proof.
have [-> | nz_x] := eqVneq x; first by rewrite rmorph0 eqxx.
apply/eqP; move/(congr1 ( *%R (f x^-1)))/eqP.
by rewrite -rmorphM mulVf // mulr0 rmorph1 ?oner_eq0.
Qed.

Lemma fmorph_inj : injective f.
Proof. by apply/raddf_inj => x /eqP; rewrite fmorph_eq0 => /eqP. Qed.

Lemma fmorph_eq : {mono f : x y / x == y}.
Proof. exact: inj_eq fmorph_inj. Qed.

Lemma fmorph_eq1 x : (f x == 1) = (x == 1).
Proof. by rewrite -(inj_eq fmorph_inj) rmorph1. Qed.

Lemma fmorph_char : char R =i char F.
Proof. by move=> p; rewrite !inE -fmorph_eq0 rmorph_nat. Qed.

End FieldMorphismInj.

Section FieldMorphismInv.

Variables (R : unitRingType) (f : {rmorphism F -> R}).

Lemma fmorph_unit x : (f x \in unit) = (x != 0).
Proof.
have [-> |] := eqVneq x; first by rewrite rmorph0 unitr0.
by rewrite -unitfE; apply: rmorph_unit.
Qed.

Lemma fmorphV : {morph f: x / x^-1}.
Proof.
move=> x; have [-> | nz_x] := eqVneq x 0; first by rewrite !(invr0, rmorph0).
by rewrite rmorphV ?unitfE.
Qed.

Lemma fmorph_div : {morph f : x y / x / y}.
Proof. by move=> x y; rewrite rmorphM /= fmorphV. Qed.

End FieldMorphismInv.

Section ModuleTheory.

Variable V : lmodType F.
Implicit Types (a : F) (v : V).

Lemma scalerK a : a != 0 -> cancel ( *:%R a : V -> V) ( *:%R a^-1).
Proof. by move=> nz_a v; rewrite scalerA mulVf // scale1r. Qed.

Lemma scalerKV a : a != 0 -> cancel ( *:%R a^-1 : V -> V) ( *:%R a).
Proof. by rewrite -invr_eq0 -{3}[a]invrK; apply: scalerK. Qed.

Lemma scalerI a : a != 0 -> injective ( *:%R a : V -> V).
Proof. by move=> nz_a; apply: can_inj (scalerK nz_a). Qed.

Lemma scaler_eq0 a v : (a *: v == 0) = (a == 0) || (v == 0).
Proof.
have [-> | nz_a] := eqVneq a; first by rewrite scale0r eqxx.
by rewrite (can2_eq (scalerK nz_a) (scalerKV nz_a)) scaler0.
Qed.

End ModuleTheory.

Lemma char_lalg (A : lalgType F) : char A =i char F.
Proof. by move=> p; rewrite inE -scaler_nat scaler_eq0 oner_eq0 orbF. Qed.

End FieldTheory.

Arguments fmorph_inj {F R} f [x1 x2].
Arguments telescope_prodf_eq {F n m} f u.

Definition decidable_field_axiom (R : unitRingType)
    (s : seq R -> pred (formula R)) :=
  forall e f, reflect (holds e f) (s e f).

HB.mixin Record Field_isDecField R of UnitRing R := {
  sat : seq R -> pred (formula R);
  satP : decidable_field_axiom sat;
}.

#[mathcomp(axiom="decidable_field_axiom"), short(type="decFieldType")]
HB.structure Definition DecidableField := { F of Field F & Field_isDecField F }.

Module DecFieldExports.
Bind Scope ring_scope with DecidableField.sort.
End DecFieldExports.
HB.export DecFieldExports.

Section DecidableFieldTheory.

Variable F : decFieldType.
Implicit Type f : formula F.

Fact sol_subproof n f :
  reflect (exists s, (size s == n) && sat s f)
          (sat [::] (foldr Exists f (iota 0 n))).
Proof.
apply: (iffP (satP _ _)) => [|[s]]; last first.
  case/andP=> /eqP sz_s /satP f_s; apply/foldExistsP.
  exists s => // i; rewrite !inE mem_iota -leqNgt add0n => le_n_i.
  by rewrite !nth_default ?sz_s.
case/foldExistsP=> e e0 f_e; set s := take n (set_nth 0 e n 0).
have sz_s: size s = n by rewrite size_take size_set_nth leq_max leqnn.
exists s; rewrite sz_s eqxx; apply/satP; apply: eq_holds f_e => i.
case: (leqP n i) => [le_n_i | lt_i_n].
  by rewrite -e0 ?nth_default ?sz_s // !inE mem_iota -leqNgt.
by rewrite nth_take // nth_set_nth /= eq_sym eqn_leq leqNgt lt_i_n.
Qed.

Definition sol n f :=
  if sol_subproof n f is ReflectT sP then xchoose sP else nseq n 0.

Lemma size_sol n f : size (sol n f) = n.
Proof.
rewrite /sol; case: sol_subproof => [sP | _]; last exact: size_nseq.
by case/andP: (xchooseP sP) => /eqP.
Qed.

Lemma solP n f : reflect (exists2 s, size s = n & holds s f) (sat (sol n f) f).
Proof.
rewrite /sol; case: sol_subproof => [sP | sPn].
  case/andP: (xchooseP sP) => _ ->; left.
  by case: sP => s; case/andP; move/eqP=> <-; move/satP; exists s.
apply: (iffP (satP _ _)); first by exists (nseq n 0); rewrite ?size_nseq.
by case=> s sz_s; move/satP=> f_s; case: sPn; exists s; rewrite sz_s eqxx.
Qed.

Lemma eq_sat f1 f2 :
  (forall e, holds e f1 <-> holds e f2) -> sat^~ f1 =1 sat^~ f2.
Proof. by move=> eqf12 e; apply/satP/satP; case: (eqf12 e). Qed.

Lemma eq_sol f1 f2 :
  (forall e, holds e f1 <-> holds e f2) -> sol^~ f1 =1 sol^~ f2.
Proof.
rewrite /sol => /eq_sat eqf12 n.
do 2![case: sol_subproof] => //= [f1s f2s | ns1 [s f2s] | [s f1s] []].
- by apply: eq_xchoose => s; rewrite eqf12.
- by case: ns1; exists s; rewrite -eqf12.
by exists s; rewrite eqf12.
Qed.

End DecidableFieldTheory.

Arguments satP {F e f} : rename.
Arguments solP {F n f} : rename.

Section QE_Mixin.

Variable F : Field.type.
Implicit Type f : formula F.

Variable proj : nat -> seq (term F) * seq (term F) -> formula F.
(* proj is the elimination of a single existential quantifier *)

(* The elimination projector is well_formed. *)
Definition wf_QE_proj :=
  forall i bc (bc_i := proj i bc),
  dnf_rterm bc -> qf_form bc_i && rformula bc_i.

(* The elimination projector is valid *)
Definition valid_QE_proj :=
  forall i bc (ex_i_bc := ('exists 'X_i, dnf_to_form [:: bc])%T) e,
  dnf_rterm bc -> reflect (holds e ex_i_bc) (qf_eval e (proj i bc)).

Hypotheses (wf_proj : wf_QE_proj) (ok_proj : valid_QE_proj).

Let elim_aux f n := foldr Or False (map (proj n) (qf_to_dnf f false)).

Fixpoint quantifier_elim f :=
  match f with
  | f1 /\ f2 => (quantifier_elim f1) /\ (quantifier_elim f2)
  | f1 \/ f2 => (quantifier_elim f1) \/ (quantifier_elim f2)
  | f1 ==> f2 => (~ quantifier_elim f1) \/ (quantifier_elim f2)
  | ~ f => ~ quantifier_elim f
  | ('exists 'X_n, f) => elim_aux (quantifier_elim f) n
  | ('forall 'X_n, f) => ~ elim_aux (~ quantifier_elim f) n
  | _ => f
  end%T.

Lemma quantifier_elim_wf f :
  let qf := quantifier_elim f in rformula f -> qf_form qf && rformula qf.
Proof.
suffices aux_wf f0 n : let qf := elim_aux f0 n in
  rformula f0 -> qf_form qf && rformula qf.
- by elim: f => //=; do ?[  move=> f1 IH1 f2 IH2;
                     case/andP=> rf1 rf2;
                     case/andP:(IH1 rf1)=> -> ->;
                     case/andP:(IH2 rf2)=> -> -> //
                  |  move=> n f1 IH rf1;
                     case/andP: (IH rf1)=> qff rf;
                     rewrite aux_wf ].
rewrite /elim_aux => rf.
suffices or_wf fs : let ofs := foldr Or False fs in
  all (@qf_form F) fs && all (@rformula F) fs -> qf_form ofs && rformula ofs.
- apply: or_wf.
  suffices map_proj_wf bcs: let mbcs := map (proj n) bcs in
    all dnf_rterm bcs -> all (@qf_form _) mbcs && all (@rformula _) mbcs.
    by apply/map_proj_wf/qf_to_dnf_rterm.
  elim: bcs => [|bc bcs ihb] bcsr //= /andP[rbc rbcs].
  by rewrite andbAC andbA wf_proj //= andbC ihb.
elim: fs => //= g gs ihg; rewrite -andbA => /and4P[-> qgs -> rgs] /=.
by apply: ihg; rewrite qgs rgs.
Qed.

Lemma quantifier_elim_rformP e f :
  rformula f -> reflect (holds e f) (qf_eval e (quantifier_elim f)).
Proof.
pose rc e n f := exists x, qf_eval (set_nth 0 e n x) f.
have auxP f0 e0 n0: qf_form f0 && rformula f0 ->
  reflect (rc e0 n0 f0) (qf_eval e0 (elim_aux f0 n0)).
+ rewrite /elim_aux => cf; set bcs := qf_to_dnf f0 false.
  apply: (@iffP (rc e0 n0 (dnf_to_form bcs))); last first.
  - by case=> x; rewrite -qf_to_dnfP //; exists x.
  - by case=> x; rewrite qf_to_dnfP //; exists x.
  have: all dnf_rterm bcs by case/andP: cf => _; apply: qf_to_dnf_rterm.
  elim: {f0 cf}bcs => [|bc bcs IHbcs] /=; first by right; case.
  case/andP=> r_bc /IHbcs {IHbcs}bcsP.
  have f_qf := dnf_to_form_qf [:: bc].
  case: ok_proj => //= [ex_x|no_x].
    left; case: ex_x => x /(qf_evalP _ f_qf); rewrite /= orbF => bc_x.
    by exists x; rewrite /= bc_x.
  apply: (iffP bcsP) => [[x bcs_x] | [x]] /=.
    by exists x; rewrite /= bcs_x orbT.
  case/orP => [bc_x|]; last by exists x.
  by case: no_x; exists x; apply/(qf_evalP _ f_qf); rewrite /= bc_x.
elim: f e => //.
- by move=> b e _; apply: idP.
- by move=> t1 t2 e _; apply: eqP.
- move=> f1 IH1 f2 IH2 e /= /andP[/IH1[] f1e]; last by right; case.
  by case/IH2; [left | right; case].
- move=> f1 IH1 f2 IH2 e /= /andP[/IH1[] f1e]; first by do 2!left.
  by case/IH2; [left; right | right; case].
- move=> f1 IH1 f2 IH2 e /= /andP[/IH1[] f1e]; last by left.
  by case/IH2; [left | right; move/(_ f1e)].
- by move=> f IHf e /= /IHf[]; [right | left].
- move=> n f IHf e /= rf; have rqf := quantifier_elim_wf rf.
  by apply: (iffP (auxP _ _ _ rqf)) => [] [x]; exists x; apply/IHf.
move=> n f IHf e /= rf; have rqf := quantifier_elim_wf rf.
case: auxP => // [f_x|no_x]; first by right=> no_x; case: f_x => x /IHf[].
by left=> x; apply/IHf=> //; apply/idPn=> f_x; case: no_x; exists x.
Qed.

Definition proj_sat e f := qf_eval e (quantifier_elim (to_rform f)).

Lemma proj_satP : DecidableField.axiom proj_sat.
Proof.
move=> e f; have fP := quantifier_elim_rformP e (to_rform_rformula f).
by apply: (iffP fP); move/to_rformP.
Qed.

End QE_Mixin.

HB.factory Record Field_QE_isDecField F of Field F := {
  proj : nat -> seq (term F) * seq (term F) -> formula F;
  wf_proj : wf_QE_proj proj;
  ok_proj : valid_QE_proj proj;
}.
HB.builders Context F of Field_QE_isDecField F.

HB.instance Definition qe_is_def_field : Field_isDecField F :=
  Field_isDecField.Build F (proj_satP wf_proj ok_proj).
HB.end.

(* Axiom == all non-constant monic polynomials have a root *)
Definition closed_field_axiom (R : pzRingType) :=
  forall n (P : nat -> R), n > 0 ->
   exists x : R, x ^+ n = \sum_(i < n) P i * (x ^+ i).

HB.mixin Record DecField_isAlgClosed F of DecidableField F := {
  solve_monicpoly : closed_field_axiom F;
}.

#[mathcomp(axiom="closed_field_axiom"), short(type="closedFieldType")]
HB.structure Definition ClosedField :=
  { F of DecidableField F & DecField_isAlgClosed F }.

Module ClosedFieldExports.
Bind Scope ring_scope with ClosedField.sort.
End ClosedFieldExports.
HB.export ClosedFieldExports.

Section ClosedFieldTheory.

Variable F : closedFieldType.

Lemma imaginary_exists : {i : F | i ^+ 2 = -1}.
Proof.
have /sig_eqW[i Di2] := @solve_monicpoly F 2 (nth 0 [:: -1]) isT.
by exists i; rewrite Di2 !big_ord_recl big_ord0 mul0r mulr1 !addr0.
Qed.

End ClosedFieldTheory.

Lemma lalgMixin (R : pzRingType) (A : lalgType R) (B : lmodType R) (f : B -> A) :
     phant B -> injective f -> scalable f ->
   forall mulB, {morph f : x y / mulB x y >-> x * y} ->
 forall a u v, a *: (mulB u v) = mulB (a *: u) v.
Proof.
by move=> _ injf fZ mulB fM a x y; apply: injf; rewrite !(fZ, fM) scalerAl.
Qed.

Lemma comRingMixin (R : comPzRingType) (T : pzRingType) (f : T -> R) :
  phant T -> injective f -> {morph f : x y / x * y} -> commutative (@mul T).
Proof. by move=> _ inj_f fM x y; apply: inj_f; rewrite !fM mulrC. Qed.

Lemma algMixin (R : pzRingType) (A : algType R) (B : lalgType R) (f : B -> A) :
    phant B -> injective f -> {morph f : x y / x * y} -> scalable f ->
  forall k (x y : B), k *: (x * y) = x * (k *: y).
Proof.
by move=> _ inj_f fM fZ a x y; apply: inj_f; rewrite !(fM, fZ) scalerAr.
Qed.

(* Mixins for stability properties *)

HB.mixin Record isMul2Closed (R : pzSemiRingType) (S : {pred R}) := {
  rpredM : mulr_2closed S
}.

HB.mixin Record isMul1Closed (R : pzSemiRingType) (S : {pred R}) := {
  rpred1 : 1 \in S
}.

HB.mixin Record isInvClosed (R : unitRingType) (S : {pred R}) := {
  rpredVr : invr_closed S
}.

HB.mixin Record isScaleClosed (R : pzRingType) (V : lmodType R)
    (S : {pred V}) := {
  rpredZ : scaler_closed S
}.

(* Structures for stability properties *)

Local Notation addrClosed := addrClosed.
Local Notation opprClosed := opprClosed.

#[short(type="mulr2Closed")]
HB.structure Definition Mul2Closed R := {S of isMul2Closed R S}.

#[short(type="mulrClosed")]
HB.structure Definition MulClosed R := {S of Mul2Closed R S & isMul1Closed R S}.

#[short(type="smulClosed")]
HB.structure Definition SmulClosed (R : pzRingType) :=
  {S of OppClosed R S & MulClosed R S}.

#[short(type="semiring2Closed")]
HB.structure Definition Semiring2Closed (R : pzSemiRingType) :=
  {S of AddClosed R S & Mul2Closed R S}.

#[short(type="semiringClosed")]
HB.structure Definition SemiringClosed (R : pzSemiRingType) :=
  {S of AddClosed R S & MulClosed R S}.

#[short(type="subringClosed")]
HB.structure Definition SubringClosed (R : pzRingType) :=
  {S of ZmodClosed R S & MulClosed R S}.

#[short(type="divClosed")]
HB.structure Definition DivClosed (R : unitRingType) :=
  {S of MulClosed R S & isInvClosed R S}.

#[short(type="sdivClosed")]
HB.structure Definition SdivClosed (R : unitRingType) :=
  {S of SmulClosed R S & isInvClosed R S}.

#[short(type="submodClosed")]
HB.structure Definition SubmodClosed (R : pzRingType) (V : lmodType R) :=
  {S of ZmodClosed V S & isScaleClosed R V S}.

#[short(type="subalgClosed")]
HB.structure Definition SubalgClosed (R : pzRingType) (A : lalgType R) :=
  {S of SubringClosed A S & isScaleClosed R A S}.

#[short(type="divringClosed")]
HB.structure Definition DivringClosed (R : unitRingType) :=
  {S of SubringClosed R S & isInvClosed R S}.

#[short(type="divalgClosed")]
HB.structure Definition DivalgClosed (R : pzRingType) (A : unitAlgType R) :=
  {S of DivringClosed A S & isScaleClosed R A S}.

(* Factories for stability properties *)

HB.factory Record isMulClosed (R : pzSemiRingType) (S : {pred R}) := {
  rpred1M : mulr_closed S
}.

HB.builders Context R S of isMulClosed R S.
HB.instance Definition _ := isMul2Closed.Build R S (proj2 rpred1M).
HB.instance Definition _ := isMul1Closed.Build R S (proj1 rpred1M).
HB.end.

HB.factory Record isSmulClosed (R : pzRingType) (S : R -> bool) := {
  smulr_closed_subproof : smulr_closed S
}.

HB.builders Context R S of isSmulClosed R S.
HB.instance Definition _ := isMulClosed.Build R S
  (smulr_closedM smulr_closed_subproof).
HB.instance Definition _ := isOppClosed.Build R S
  (smulr_closedN smulr_closed_subproof).
HB.end.

HB.factory Record isSemiringClosed (R : pzSemiRingType) (S : R -> bool) := {
  semiring_closed_subproof : semiring_closed S
}.

HB.builders Context R S of isSemiringClosed R S.
HB.instance Definition _ := isAddClosed.Build R S
  (semiring_closedD semiring_closed_subproof).
HB.instance Definition _ := isMulClosed.Build R S
  (semiring_closedM semiring_closed_subproof).
HB.end.

HB.factory Record isSubringClosed (R : pzRingType) (S : R -> bool) := {
  subring_closed_subproof : subring_closed S
}.

HB.builders Context R S of isSubringClosed R S.
HB.instance Definition _ := isZmodClosed.Build R S
  (subring_closedB subring_closed_subproof).
HB.instance Definition _ := isSmulClosed.Build R S
  (subring_closedM subring_closed_subproof).
HB.end.

HB.factory Record isDivClosed (R : unitRingType) (S : R -> bool) := {
  divr_closed_subproof : divr_closed S
}.

HB.builders Context R S of isDivClosed R S.
#[warning="-HB.no-new-instance"]
HB.instance Definition _ := isInvClosed.Build R S
  (divr_closedV divr_closed_subproof).
HB.instance Definition _ := isMulClosed.Build R S
  (divr_closedM divr_closed_subproof).
HB.end.

HB.factory Record isSdivClosed (R : unitRingType) (S : R -> bool) := {
  sdivr_closed_subproof : sdivr_closed S
}.

HB.builders Context R S of isSdivClosed R S.
HB.instance Definition _ := isDivClosed.Build R S
  (sdivr_closed_div sdivr_closed_subproof).
HB.instance Definition _ := isSmulClosed.Build R S
  (sdivr_closedM sdivr_closed_subproof).
HB.end.

HB.factory Record isSubmodClosed (R : pzRingType) (V : lmodType R)
    (S : V -> bool) := {
  submod_closed_subproof : submod_closed S
}.

HB.builders Context R V S of isSubmodClosed R V S.
HB.instance Definition _ := isZmodClosed.Build V S
  (submod_closedB submod_closed_subproof).
HB.instance Definition _ := isScaleClosed.Build R V S
  (submod_closedZ submod_closed_subproof).
HB.end.

HB.factory Record isSubalgClosed (R : pzRingType) (A : lalgType R)
    (S : A -> bool) := {
  subalg_closed_subproof : subalg_closed S
}.

HB.builders Context R A S of isSubalgClosed R A S.
HB.instance Definition _ := isSubmodClosed.Build R A S
  (subalg_closedZ subalg_closed_subproof).
HB.instance Definition _ := isSubringClosed.Build A S
  (subalg_closedBM subalg_closed_subproof).
HB.end.

HB.factory Record isDivringClosed (R : unitRingType) (S : R -> bool) := {
  divring_closed_subproof : divring_closed S
}.

HB.builders Context R S of isDivringClosed R S.
HB.instance Definition _ := isSubringClosed.Build R S
  (divring_closedBM divring_closed_subproof).
HB.instance Definition _ := isSdivClosed.Build R S
  (divring_closed_div divring_closed_subproof).
HB.end.

HB.factory Record isDivalgClosed (R : comUnitRingType) (A : unitAlgType R)
    (S : A -> bool) := {
  divalg_closed_subproof : divalg_closed S
}.

HB.builders Context R A S of isDivalgClosed R A S.
HB.instance Definition _ := isDivringClosed.Build A S
  (divalg_closedBdiv divalg_closed_subproof).
HB.instance Definition _ := isSubalgClosed.Build R A S
  (divalg_closedZ divalg_closed_subproof).
HB.end.

Section NmodulePred.

Variables (V : nmodType).

Section Add.

Variable S : addrClosed V.

Lemma rpred0D : addr_closed S. Proof. exact: nmod_closed_subproof. Qed.

End Add.

End NmodulePred.

Section ZmodulePred.

Variables (V : zmodType).

Section Opp.

Variable S : opprClosed V.

End Opp.

Section Sub.

Variable S : zmodClosed V.

Lemma zmodClosedP : zmod_closed S.
Proof. split; [ exact: (@rpred0D V S).1 | exact: rpredB ]. Qed.

End Sub.

End ZmodulePred.

Section SemiRingPred.

Variables (R : pzSemiRingType).

Section Mul.

Variable S : mulrClosed R.

Lemma rpred1M : mulr_closed S.
Proof. exact: (conj rpred1 rpredM). Qed.

Lemma rpred_prod I r (P : pred I) F :
  (forall i, P i -> F i \in S) -> \prod_(i <- r | P i) F i \in S.
Proof. by move=> IH; elim/big_ind: _; [apply: rpred1 | apply: rpredM |]. Qed.

Lemma rpredX n : {in S, forall u, u ^+ n \in S}.
Proof. by move=> u Su; rewrite -(card_ord n) -prodr_const rpred_prod. Qed.

End Mul.

Lemma rpred_nat (S : semiringClosed R) n : n%:R \in S.
Proof. by rewrite rpredMn ?rpred1. Qed.

Lemma semiringClosedP (rngS : semiringClosed R) : semiring_closed rngS.
Proof. split; [ exact: rpred0D | exact: rpred1M ]. Qed.

End SemiRingPred.

Section RingPred.

Variables (R : pzRingType).

Lemma rpredMsign (S : opprClosed R) n x : ((-1) ^+ n * x \in S) = (x \in S).
Proof. by rewrite -signr_odd mulr_sign; case: ifP => // _; rewrite rpredN. Qed.

Lemma rpredN1 (S : smulClosed R) : -1 \in S.
Proof. by rewrite rpredN rpred1. Qed.

Lemma rpred_sign (S : smulClosed R) n : (-1) ^+ n \in S.
Proof. by rewrite rpredX ?rpredN1. Qed.

Lemma subringClosedP (rngS : subringClosed R) : subring_closed rngS.
Proof.
split; [ exact: rpred1 | exact: (zmodClosedP rngS).2 | exact: rpredM ].
Qed.

End RingPred.

Section LmodPred.

Variables (R : pzRingType) (V : lmodType R).

Lemma rpredZsign (S : opprClosed V) n u : ((-1) ^+ n *: u \in S) = (u \in S).
Proof. by rewrite -signr_odd scaler_sign fun_if if_arg rpredN if_same. Qed.

Lemma rpredZnat (S : addrClosed V) n : {in S, forall u, n%:R *: u \in S}.
Proof. by move=> u Su; rewrite /= scaler_nat rpredMn. Qed.

Lemma submodClosedP (modS : submodClosed V) : submod_closed modS.
Proof.
split; first exact (@rpred0D V modS).1.
by move=> a u v uS vS; apply: rpredD; first exact: rpredZ.
Qed.

End LmodPred.

Section LalgPred.

Variables (R : pzRingType) (A : lalgType R).

Lemma subalgClosedP (algS : subalgClosed A) : subalg_closed algS.
Proof.
split; [ exact: rpred1 | | exact: rpredM ].
by move=> a u v uS vS; apply: rpredD; first exact: rpredZ.
Qed.

End LalgPred.

Section UnitRingPred.

Variable R : unitRingType.

Section Div.

Variable S : divClosed R.

Lemma rpredV x : (x^-1 \in S) = (x \in S).
Proof. by apply/idP/idP=> /rpredVr; rewrite ?invrK. Qed.

Lemma rpred_div : {in S &, forall x y, x / y \in S}.
Proof. by move=> x y Sx Sy; rewrite /= rpredM ?rpredV. Qed.

Lemma rpredXN n : {in S, forall x, x ^- n \in S}.
Proof. by move=> x Sx; rewrite /= rpredV rpredX. Qed.

Lemma rpredMl x y : x \in S -> x \is a unit-> (x * y \in S) = (y \in S).
Proof.
move=> Sx Ux; apply/idP/idP=> [Sxy | /(rpredM _ _ Sx)-> //].
by rewrite -(mulKr Ux y); rewrite rpredM ?rpredV.
Qed.

Lemma rpredMr x y : x \in S -> x \is a unit -> (y * x \in S) = (y \in S).
Proof.
move=> Sx Ux; apply/idP/idP=> [Sxy | /rpredM-> //].
by rewrite -(mulrK Ux y); rewrite rpred_div.
Qed.

Lemma rpred_divr x y : x \in S -> x \is a unit -> (y / x \in S) = (y \in S).
Proof. by rewrite -rpredV -unitrV; apply: rpredMr. Qed.

Lemma rpred_divl x y : x \in S -> x \is a unit -> (x / y \in S) = (y \in S).
Proof. by rewrite -(rpredV y); apply: rpredMl. Qed.

End Div.

Lemma divringClosedP (divS : divringClosed R) : divring_closed divS.
Proof. split; [ exact: rpred1 | exact: rpredB | exact: rpred_div ]. Qed.

Fact unitr_sdivr_closed : @sdivr_closed R unit.
Proof. by split=> [|x y Ux Uy]; rewrite ?unitrN1 // unitrMl ?unitrV. Qed.

#[export]
HB.instance Definition _ := isSdivClosed.Build R unit_pred unitr_sdivr_closed.

Implicit Type x : R.

Lemma unitrN x : (- x \is a unit) = (x \is a unit). Proof. exact: rpredN. Qed.

Lemma invrN x : (- x)^-1 = - x^-1.
Proof.
have [Ux | U'x] := boolP (x \is a unit); last by rewrite !invr_out ?unitrN.
by rewrite -mulN1r invrM ?unitrN1 // invrN1 mulrN1.
Qed.

Lemma divrNN x y : (- x) / (- y) = x / y.
Proof. by rewrite invrN mulrNN. Qed.

Lemma divrN x y : x / (- y) = - (x / y).
Proof. by rewrite invrN mulrN. Qed.

Lemma invr_signM n x : ((-1) ^+ n * x)^-1 = (-1) ^+ n * x^-1.
Proof. by rewrite -signr_odd !mulr_sign; case: ifP => // _; rewrite invrN. Qed.

Lemma divr_signM (b1 b2 : bool) x1 x2:
  ((-1) ^+ b1 * x1) / ((-1) ^+ b2 * x2) = (-1) ^+ (b1 (+) b2) * (x1 / x2).
Proof. by rewrite invr_signM mulr_signM. Qed.

End UnitRingPred.

Section FieldPred.

Variable F : fieldType.
Implicit Types x y : F.

Section ModuleTheory.

Variable V : lmodType F.
Implicit Types (a : F) (v : V).

Lemma rpredZeq (S : submodClosed V) a v :
  (a *: v \in S) = (a == 0) || (v \in S).
Proof.
have [-> | nz_a] := eqVneq; first by rewrite scale0r rpred0.
by apply/idP/idP; first rewrite -{2}(scalerK nz_a v); apply: rpredZ.
Qed.

End ModuleTheory.

Section Predicates.

Context (S : divClosed F).

Lemma fpredMl x y : x \in S -> x != 0 -> (x * y \in S) = (y \in S).
Proof. by rewrite -!unitfE; apply: rpredMl. Qed.

Lemma fpredMr x y : x \in S -> x != 0 -> (y * x \in S) = (y \in S).
Proof. by rewrite -!unitfE; apply: rpredMr. Qed.

Lemma fpred_divl x y : x \in S -> x != 0 -> (x / y \in S) = (y \in S).
Proof. by rewrite -!unitfE; apply: rpred_divl. Qed.

Lemma fpred_divr x y : x \in S -> x != 0 -> (y / x \in S) = (y \in S).
Proof. by rewrite -!unitfE; apply: rpred_divr. Qed.

End Predicates.

End FieldPred.

HB.mixin Record isSubPzSemiRing (R : pzSemiRingType) (S : pred R) U
    of SubNmodule R S U & PzSemiRing U := {
  valM_subproof : multiplicative (val : U -> R);
}.

Module isSubSemiRing.
#[deprecated(since="mathcomp 2.4.0",
             note="Use isSubPzSemiRing.Build instead.")]
Notation Build R S U := (isSubPzSemiRing.Build R S U) (only parsing).
End isSubSemiRing.

#[deprecated(since="mathcomp 2.4.0",
             note="Use isSubPzSemiRing instead.")]
Notation isSubSemiRing R S U := (isSubPzSemiRing R S U) (only parsing).

#[short(type="subPzSemiRingType")]
HB.structure Definition SubPzSemiRing (R : pzSemiRingType) (S : pred R) :=
  { U of SubNmodule R S U & PzSemiRing U & isSubPzSemiRing R S U }.

#[short(type="subNzSemiRingType")]
HB.structure Definition SubNzSemiRing (R : nzSemiRingType) (S : pred R) :=
  { U of SubNmodule R S U & NzSemiRing U & isSubPzSemiRing R S U }.

#[deprecated(since="mathcomp 2.4.0",
             note="Use SubNzSemiRing instead.")]
Notation SubSemiRing R := (SubNzSemiRing R) (only parsing).

Module SubSemiRing.
#[deprecated(since="mathcomp 2.4.0",
             note="Use SubNzSemiRing.sort instead.")]
Notation sort := (SubNzSemiRing.sort) (only parsing).
#[deprecated(since="mathcomp 2.4.0",
             note="Use SubNzSemiRing.on instead.")]
Notation on R := (SubNzSemiRing.on R) (only parsing).
#[deprecated(since="mathcomp 2.4.0",
             note="Use SubNzSemiRing.copy instead.")]
Notation copy T U := (SubNzSemiRing.copy T U) (only parsing).
End SubSemiRing.

Section multiplicative.
Context (R : pzSemiRingType) (S : pred R) (U : SubPzSemiRing.type S).
Notation val := (val : U -> R).
#[export]
HB.instance Definition _ := isMultiplicative.Build U R val valM_subproof.
Lemma val1 : val 1 = 1. Proof. exact: rmorph1. Qed.
Lemma valM : {morph val : x y / x * y}. Proof. exact: rmorphM. Qed.
Lemma valM1 : multiplicative val. Proof. exact: valM_subproof. Qed.
End multiplicative.

HB.factory Record SubNmodule_isSubPzSemiRing (R : pzSemiRingType) S U
    of SubNmodule R S U := {
  mulr_closed_subproof : mulr_closed S
}.

HB.builders Context R S U of SubNmodule_isSubPzSemiRing R S U.

HB.instance Definition _ := isMulClosed.Build R S mulr_closed_subproof.

Let inU v Sv : U := Sub v Sv.
Let oneU : U := inU (@rpred1 _ (MulClosed.clone R S _)).
Let mulU (u1 u2 : U) := inU (rpredM _ _ (valP u1) (valP u2)).

Lemma mulrA : associative mulU.
Proof. by move=> x y z; apply: val_inj; rewrite !SubK mulrA. Qed.
Lemma mul1r : left_id oneU mulU.
Proof. by move=> x; apply: val_inj; rewrite !SubK mul1r. Qed.
Lemma mulr1 : right_id oneU mulU.
Proof. by move=> x; apply: val_inj; rewrite !SubK mulr1. Qed.
Lemma mulrDl : left_distributive mulU +%R.
Proof.
by move=> x y z; apply: val_inj; rewrite !(SubK, raddfD)/= !SubK mulrDl.
Qed.
Lemma mulrDr : right_distributive mulU +%R.
Proof.
by move=> x y z; apply: val_inj; rewrite !(SubK, raddfD)/= !SubK mulrDr.
Qed.
Lemma mul0r : left_zero 0%R mulU.
Proof. by move=> x; apply: val_inj; rewrite SubK val0 mul0r. Qed.
Lemma mulr0 : right_zero 0%R mulU.
Proof. by move=> x; apply: val_inj; rewrite SubK val0 mulr0. Qed.
HB.instance Definition _ := Nmodule_isPzSemiRing.Build U
  mulrA mul1r mulr1 mulrDl mulrDr mul0r mulr0.

Lemma valM : multiplicative (val : U -> R).
Proof. by split=> [x y|] /=; rewrite !SubK. Qed.
HB.instance Definition _ := isSubPzSemiRing.Build R S U valM.
HB.end.

HB.factory Record SubNmodule_isSubNzSemiRing (R : nzSemiRingType) S U
    of SubNmodule R S U := {
  mulr_closed_subproof : mulr_closed S
}.

Module SubNmodule_isSubSemiRing.
#[deprecated(since="mathcomp 2.4.0",
             note="Use SubNmodule_isSubNzSemiRing.Build instead.")]
Notation Build R S U := (SubNmodule_isSubNzSemiRing.Build R S U) (only parsing).
End SubNmodule_isSubSemiRing.

#[deprecated(since="mathcomp 2.4.0",
             note="Use SubNmodule_isSubNzSemiRing instead.")]
Notation SubNmodule_isSubSemiRing R S U :=
  (SubNmodule_isSubNzSemiRing R S U) (only parsing).

HB.builders Context R S U of SubNmodule_isSubNzSemiRing R S U.

HB.instance Definition _ := SubNmodule_isSubPzSemiRing.Build R S U
  mulr_closed_subproof.

Lemma oner_neq0 : (1 : U) != 0.
Proof. by rewrite -(inj_eq val_inj) SubK raddf0 oner_neq0. Qed.
HB.instance Definition _ := PzSemiRing_isNonZero.Build U oner_neq0.
HB.end.

#[short(type="subComPzSemiRingType")]
HB.structure Definition SubComPzSemiRing (R : pzSemiRingType) S :=
  {U of SubPzSemiRing R S U & ComPzSemiRing U}.

HB.factory Record SubPzSemiRing_isSubComPzSemiRing (R : comPzSemiRingType) S U
    of SubPzSemiRing R S U := {}.

HB.builders Context R S U of SubPzSemiRing_isSubComPzSemiRing R S U.
Lemma mulrC : @commutative U U *%R.
Proof. by move=> x y; apply: val_inj; rewrite !rmorphM mulrC. Qed.
HB.instance Definition _ := PzSemiRing_hasCommutativeMul.Build U mulrC.
HB.end.

#[short(type="subComNzSemiRingType")]
HB.structure Definition SubComNzSemiRing (R : nzSemiRingType) S :=
  {U of SubNzSemiRing R S U & ComNzSemiRing U}.

#[deprecated(since="mathcomp 2.4.0",
             note="Use SubComNzSemiRing instead.")]
Notation SubComSemiRing R := (SubComNzSemiRing R) (only parsing).

Module SubComSemiRing.
#[deprecated(since="mathcomp 2.4.0",
             note="Use SubComNzSemiRing.sort instead.")]
Notation sort  := (SubComNzSemiRing.sort) (only parsing).
#[deprecated(since="mathcomp 2.4.0",
             note="Use SubComNzSemiRing.on instead.")]
Notation on R := (SubComNzSemiRing.on R) (only parsing).
#[deprecated(since="mathcomp 2.4.0",
             note="Use SubComNzSemiRing.copy instead.")]
Notation copy T U := (SubComNzSemiRing.copy T U) (only parsing).
End SubComSemiRing.

HB.factory Record SubNzSemiRing_isSubComNzSemiRing (R : comNzSemiRingType) S U
    of SubNzSemiRing R S U := {}.

Module SubSemiRing_isSubComSemiRing.
#[deprecated(since="mathcomp 2.4.0",
             note="Use SubNzSemiRing_isSubComNzSemiRing.Build instead.")]
Notation Build R S U :=
  (SubNzSemiRing_isSubComNzSemiRing.Build R S U) (only parsing).
End SubSemiRing_isSubComSemiRing.

#[deprecated(since="mathcomp 2.4.0",
             note="Use SubNzSemiRing_isSubComNzSemiRing instead.")]
Notation SubSemiRing_isSubComSemiRing R S U :=
  (SubNzSemiRing_isSubComNzSemiRing R S U) (only parsing).

HB.builders Context R S U of SubNzSemiRing_isSubComNzSemiRing R S U.
Lemma mulrC : @commutative U U *%R.
Proof. by move=> x y; apply: val_inj; rewrite !rmorphM mulrC. Qed.
HB.instance Definition _ := PzSemiRing_hasCommutativeMul.Build U mulrC.
HB.end.

#[short(type="pzSubRingType")]
HB.structure Definition SubPzRing (R : pzRingType) (S : pred R) :=
  { U of SubPzSemiRing R S U & PzRing U & isSubZmodule R S U }.

HB.factory Record SubZmodule_isSubPzRing (R : pzRingType) S U
    of SubZmodule R S U := {
  subring_closed_subproof : subring_closed S
}.

HB.builders Context R S U of SubZmodule_isSubPzRing R S U.

HB.instance Definition _ := isSubringClosed.Build R S subring_closed_subproof.

Let inU v Sv : U := Sub v Sv.
Let oneU : U := inU (@rpred1 _ (MulClosed.clone R S _)).
Let mulU (u1 u2 : U) := inU (rpredM _ _ (valP u1) (valP u2)).

HB.instance Definition _ := SubNmodule_isSubPzSemiRing.Build R S U
  (smulr_closedM (subring_closedM subring_closed_subproof)).
HB.end.

#[short(type="nzSubRingType")]
HB.structure Definition SubNzRing (R : nzRingType) (S : pred R) :=
  { U of SubNzSemiRing R S U & NzRing U & isSubBaseAddUMagma R S U }.

#[deprecated(since="mathcomp 2.4.0",
             note="Use SubNzRing instead.")]
Notation SubRing R := (SubNzRing R) (only parsing).

Module SubRing.
#[deprecated(since="mathcomp 2.4.0",
             note="Use SubNzRing.sort instead.")]
Notation sort := (SubNzRing.sort) (only parsing).
#[deprecated(since="mathcomp 2.4.0",
             note="Use SubNzRing.on instead.")]
Notation on R := (SubNzRing.on R) (only parsing).
#[deprecated(since="mathcomp 2.4.0",
             note="Use SubNzRing.copy instead.")]
Notation copy T U := (SubNzRing.copy T U) (only parsing).
End SubRing.

HB.factory Record SubZmodule_isSubNzRing (R : nzRingType) S U
    of SubZmodule R S U := {
  subring_closed_subproof : subring_closed S
}.

Module SubZmodule_isSubRing.
#[deprecated(since="mathcomp 2.4.0",
             note="Use SubZmodule_isSubNzRing.Build instead.")]
Notation Build R S U := (SubZmodule_isSubNzRing.Build R S U) (only parsing).
End SubZmodule_isSubRing.

#[deprecated(since="mathcomp 2.4.0",
             note="Use SubZmodule_isSubNzRing instead.")]
Notation SubZmodule_isSubRing R S U :=
  (SubZmodule_isSubNzRing R S U) (only parsing).

HB.builders Context R S U of SubZmodule_isSubNzRing R S U.

HB.instance Definition _ := isSubringClosed.Build R S subring_closed_subproof.

Let inU v Sv : U := Sub v Sv.
Let oneU : U := inU (@rpred1 _ (MulClosed.clone R S _)).
Let mulU (u1 u2 : U) := inU (rpredM _ _ (valP u1) (valP u2)).

HB.instance Definition _ := SubNmodule_isSubNzSemiRing.Build R S U
  (smulr_closedM (subring_closedM subring_closed_subproof)).
HB.end.

#[short(type="subComPzRingType")]
HB.structure Definition SubComPzRing (R : pzRingType) S :=
  {U of SubPzRing R S U & ComPzRing U}.

HB.factory Record SubPzRing_isSubComPzRing (R : comPzRingType) S U
    of SubPzRing R S U := {}.

HB.builders Context R S U of SubPzRing_isSubComPzRing R S U.
Lemma mulrC : @commutative U U *%R.
Proof. by move=> x y; apply: val_inj; rewrite !rmorphM mulrC. Qed.
HB.instance Definition _ := PzRing_hasCommutativeMul.Build U mulrC.
HB.end.

#[short(type="subComNzRingType")]
HB.structure Definition SubComNzRing (R : nzRingType) S :=
  {U of SubNzRing R S U & ComNzRing U}.

#[deprecated(since="mathcomp 2.4.0",
             note="Use SubComNzRing instead.")]
Notation SubComRing R := (SubComNzRing R) (only parsing).

Module SubComRing.
#[deprecated(since="mathcomp 2.4.0",
             note="Use SubComNzRing.sort instead.")]
Notation sort := (SubComNzRing.sort) (only parsing).
#[deprecated(since="mathcomp 2.4.0",
             note="Use SubComNzRing.on instead.")]
Notation on R := (SubComNzRing.on R) (only parsing).
#[deprecated(since="mathcomp 2.4.0",
             note="Use SubComNzRing.copy instead.")]
Notation copy T U := (SubComNzRing.copy T U) (only parsing).
End SubComRing.

HB.factory Record SubNzRing_isSubComNzRing (R : comNzRingType) S U
    of SubNzRing R S U := {}.

Module SubRing_isSubComRing.
#[deprecated(since="mathcomp 2.4.0",
             note="Use SubNzRing_isSubComNzRing.Build instead.")]
Notation Build R S U := (SubNzRing_isSubComNzRing.Build R S U) (only parsing).
End SubRing_isSubComRing.

#[deprecated(since="mathcomp 2.4.0",
             note="Use SubNzRing_isSubComNzRing instead.")]
Notation SubRing_isSubComRing R S U :=
  (SubNzRing_isSubComNzRing R S U) (only parsing).

HB.builders Context R S U of SubNzRing_isSubComNzRing R S U.
Lemma mulrC : @commutative U U *%R.
Proof. by move=> x y; apply: val_inj; rewrite !rmorphM mulrC. Qed.
HB.instance Definition _ := PzRing_hasCommutativeMul.Build U mulrC.
HB.end.

HB.mixin Record isSubLmodule (R : pzRingType) (V : lmodType R) (S : pred V)
   W of SubZmodule V S W & Lmodule R W := {
 valZ : scalable (val : W -> V);
}.

#[short(type="subLmodType")]
HB.structure Definition SubLmodule (R : pzRingType) (V : lmodType R)
    (S : pred V) :=
  { W of SubZmodule V S W & Zmodule_isLmodule R W & isSubLmodule R V S W}.

Section linear.
Context (R : pzRingType) (V : lmodType R) (S : pred V) (W : SubLmodule.type S).
Notation val := (val : W -> V).
#[export]
HB.instance Definition _ := isScalable.Build R W V *:%R val valZ.
End linear.

HB.factory Record SubZmodule_isSubLmodule (R : pzRingType) (V : lmodType R) S W
    of SubZmodule V S W := {
  submod_closed_subproof : submod_closed S
}.

HB.builders Context (R : pzRingType) (V : lmodType R) S W
  of SubZmodule_isSubLmodule R V S W.

HB.instance Definition _ := isSubmodClosed.Build R V S submod_closed_subproof.

Let inW v Sv : W := Sub v Sv.
Let scaleW a (w : W) := inW (rpredZ a _ (valP w)).

Lemma scalerA' a b v : scaleW a (scaleW b v) = scaleW (a * b) v.
Proof. by apply: val_inj; rewrite !SubK scalerA. Qed.
Lemma scale1r : left_id 1 scaleW.
Proof. by move=> x; apply: val_inj; rewrite SubK scale1r. Qed.
Lemma scalerDr : right_distributive scaleW +%R.
Proof.
by move=> a u v; apply: val_inj; rewrite !(SubK, raddfD)/= !SubK.
Qed.
Lemma scalerDl v : {morph scaleW^~ v : a b / a + b}.
Proof.
by move=> a b; apply: val_inj; rewrite !(SubK, raddfD)/= !SubK scalerDl.
Qed.
HB.instance Definition _ := Zmodule_isLmodule.Build R W
  scalerA' scale1r scalerDr scalerDl.

Fact valZ : scalable (val : W -> _). Proof. by move=> k w; rewrite SubK. Qed.
HB.instance Definition _ := isSubLmodule.Build R V S W valZ.
HB.end.

#[short(type="subLalgType")]
HB.structure Definition SubLalgebra (R : pzRingType) (V : lalgType R) S :=
  {W of SubNzRing V S W & @SubLmodule R V S W & Lalgebra R W}.

HB.factory Record SubNzRing_SubLmodule_isSubLalgebra (R : pzRingType)
    (V : lalgType R) S W of SubNzRing V S W & @SubLmodule R V S W := {}.

Module SubRing_SubLmodule_isSubLalgebra.
#[deprecated(since="mathcomp 2.4.0",
             note="Use SubNzRing_SubLmodule_isSubLalgebra.Build instead.")]
Notation Build R V S U :=
  (SubNzRing_SubLmodule_isSubLalgebra.Build R V S U) (only parsing).
End SubRing_SubLmodule_isSubLalgebra.

#[deprecated(since="mathcomp 2.4.0",
             note="Use SubNzRing_SubLmodule_isSubLalgebra instead.")]
Notation SubRing_SubLmodule_isSubLalgebra R V S U :=
  (SubNzRing_SubLmodule_isSubLalgebra R V S U) (only parsing).

HB.builders Context (R : pzRingType) (V : lalgType R) S W
  of SubNzRing_SubLmodule_isSubLalgebra R V S W.
Lemma scalerAl (a : R) (u v : W) : a *: (u * v) = a *: u * v.
Proof. by apply: val_inj; rewrite !(linearZ, rmorphM)/= linearZ scalerAl. Qed.
HB.instance Definition _ := Lmodule_isLalgebra.Build R W scalerAl.
HB.end.

#[short(type="subAlgType")]
HB.structure Definition SubAlgebra (R : pzRingType) (V : algType R) S :=
  {W of @SubLalgebra R V S W & Algebra R W}.

HB.factory Record SubLalgebra_isSubAlgebra (R : pzRingType)
    (V : algType R) S W of @SubLalgebra R V S W := {}.

HB.builders Context (R : pzRingType) (V : algType R) S W
  of SubLalgebra_isSubAlgebra R V S W.
Lemma scalerAr (k : R) (x y : W) : k *: (x * y) = x * (k *: y).
Proof. by apply: val_inj; rewrite !(linearZ, rmorphM)/= linearZ scalerAr. Qed.
HB.instance Definition _ := Lalgebra_isAlgebra.Build R W scalerAr.
HB.end.

#[short(type="subUnitRingType")]
HB.structure Definition SubUnitRing (R : nzRingType) (S : pred R) :=
  {U of SubNzRing R S U & UnitRing U}.

HB.factory Record SubNzRing_isSubUnitRing (R : unitRingType) S U
    of SubNzRing R S U := {
  divring_closed_subproof : divring_closed S
}.

HB.builders Context (R : unitRingType) S U of SubNzRing_isSubUnitRing R S U.

HB.instance Definition _ := isDivringClosed.Build R S divring_closed_subproof.

Let inU v Sv : U := Sub v Sv.
Let invU (u : U) := inU (rpredVr _ (valP u)).

Lemma mulVr : {in [pred x | val x \is a unit], left_inverse 1 invU *%R}.
Proof.
by move=> x /[!inE] xu; apply: val_inj; rewrite rmorphM rmorph1 /= SubK mulVr.
Qed.
Lemma divrr : {in [pred x | val x \is a unit], right_inverse 1 invU *%R}.
by move=> x /[!inE] xu; apply: val_inj; rewrite rmorphM rmorph1 /= SubK mulrV.
Qed.
Lemma unitrP (x y : U) : y * x = 1 /\ x * y = 1 -> val x \is a unit.
Proof.
move=> -[/(congr1 val) yx1 /(congr1 val) xy1].
by apply: rev_unitrP (val y) _; rewrite !rmorphM rmorph1 /= in yx1 xy1.
Qed.
Lemma invr_out : {in [pred x | val x \isn't a unit], invU =1 id}.
Proof.
by move=> x /[!inE] xNU; apply: val_inj; rewrite SubK invr_out.
Qed.
HB.instance Definition _ := NzRing_hasMulInverse.Build U
  mulVr divrr unitrP invr_out.
HB.end.

#[short(type="subComUnitRingType")]
HB.structure Definition SubComUnitRing (R : comUnitRingType) (S : pred R) :=
  {U of SubComNzRing R S U & SubUnitRing R S U}.

#[short(type="subIdomainType")]
HB.structure Definition SubIntegralDomain (R : idomainType) (S : pred R) :=
  {U of SubComNzRing R S U & IntegralDomain U}.

HB.factory Record SubComUnitRing_isSubIntegralDomain (R : idomainType) S U
  of SubComUnitRing R S U := {}.

HB.builders Context (R : idomainType) S U
  of SubComUnitRing_isSubIntegralDomain R S U.
Lemma id : IntegralDomain.axiom U.
Proof.
move=> x y /(congr1 val)/eqP; rewrite rmorphM /=.
by rewrite -!(inj_eq val_inj) rmorph0 -mulf_eq0.
Qed.
HB.instance Definition _ := ComUnitRing_isIntegral.Build U id.
HB.end.

#[short(type="subFieldType")]
HB.structure Definition SubField (F : fieldType) (S : pred F) :=
  {U of SubIntegralDomain F S U & Field U}.

HB.factory Record SubIntegralDomain_isSubField (F : fieldType) S U
    of SubIntegralDomain F S U := {
  subfield_subproof : {mono (val : U -> F) : u / u \in unit}
}.

HB.builders Context (F : fieldType) S U of SubIntegralDomain_isSubField F S U.
Lemma fieldP : Field.axiom U.
Proof.
by move=> u; rewrite -(inj_eq val_inj) rmorph0 -unitfE subfield_subproof.
Qed.
HB.instance Definition _ := UnitRing_isField.Build U fieldP.
HB.end.

HB.factory Record SubChoice_isSubPzSemiRing (R : pzSemiRingType) S U
    of SubChoice R S U := {
  semiring_closed_subproof : semiring_closed S
}.

HB.builders Context (R : pzSemiRingType) S U of SubChoice_isSubPzSemiRing R S U.
HB.instance Definition _ := SubChoice_isSubNmodule.Build R S U
  (semiring_closedD semiring_closed_subproof).
HB.instance Definition _ := SubNmodule_isSubPzSemiRing.Build R S U
  (semiring_closedM semiring_closed_subproof).
HB.end.

HB.factory Record SubChoice_isSubNzSemiRing (R : nzSemiRingType) S U
    of SubChoice R S U := {
  semiring_closed_subproof : semiring_closed S
}.

Module SubChoice_isSubSemiRing.
#[deprecated(since="mathcomp 2.4.0",
             note="Use SubChoice_isSubNzSemiRing.Build instead.")]
Notation Build R S U := (SubChoice_isSubNzSemiRing.Build R S U) (only parsing).
End SubChoice_isSubSemiRing.

#[deprecated(since="mathcomp 2.4.0",
             note="Use SubChoice_isSubNzSemiRing instead.")]
Notation SubChoice_isSubSemiRing R S U :=
  (SubChoice_isSubNzSemiRing R S U) (only parsing).

HB.builders Context (R : nzSemiRingType) S U of SubChoice_isSubNzSemiRing R S U.
HB.instance Definition _ := SubChoice_isSubNmodule.Build R S U
  (semiring_closedD semiring_closed_subproof).
HB.instance Definition _ := SubNmodule_isSubNzSemiRing.Build R S U
  (semiring_closedM semiring_closed_subproof).
HB.end.

HB.factory Record SubChoice_isSubComPzSemiRing (R : comPzSemiRingType) S U
    of SubChoice R S U := {
  semiring_closed_subproof : semiring_closed S
}.

HB.builders Context (R : comPzSemiRingType) S U
  of SubChoice_isSubComPzSemiRing R S U.
HB.instance Definition _ := SubChoice_isSubPzSemiRing.Build R S U
  semiring_closed_subproof.
HB.instance Definition _ := SubPzSemiRing_isSubComPzSemiRing.Build R S U.
HB.end.

HB.factory Record SubChoice_isSubComNzSemiRing (R : comNzSemiRingType) S U
    of SubChoice R S U := {
  semiring_closed_subproof : semiring_closed S
}.

Module SubChoice_isSubComSemiRing.
#[deprecated(since="mathcomp 2.4.0",
             note="Use SubChoice_isSubComNzSemiRing.Build instead.")]
Notation Build R S U :=
  (SubChoice_isSubComNzSemiRing.Build R S U) (only parsing).
End SubChoice_isSubComSemiRing.

#[deprecated(since="mathcomp 2.4.0",
             note="Use SubChoice_isSubComNzSemiRing instead.")]
Notation SubChoice_isSubComSemiRing R S U :=
  (SubChoice_isSubComNzSemiRing R S U) (only parsing).

HB.builders Context (R : comNzSemiRingType) S U
  of SubChoice_isSubComNzSemiRing R S U.
HB.instance Definition _ := SubChoice_isSubNzSemiRing.Build R S U
  semiring_closed_subproof.
HB.instance Definition _ := SubNzSemiRing_isSubComNzSemiRing.Build R S U.
HB.end.

HB.factory Record SubChoice_isSubPzRing (R : pzRingType) S U of SubChoice R S U := {
  subring_closed_subproof : subring_closed S
}.

HB.builders Context (R : pzRingType) S U of SubChoice_isSubPzRing R S U.
HB.instance Definition _ := SubChoice_isSubZmodule.Build R S U
  (subring_closedB subring_closed_subproof).
HB.instance Definition _ := SubZmodule_isSubPzRing.Build R S U
  subring_closed_subproof.
HB.end.

HB.factory Record SubChoice_isSubNzRing (R : nzRingType) S U of SubChoice R S U := {
  subring_closed_subproof : subring_closed S
}.

Module SubChoice_isSubRing.
#[deprecated(since="mathcomp 2.4.0",
             note="Use SubChoice_isSubNzRing.Build instead.")]
Notation Build R S U := (SubChoice_isSubNzRing.Build R S U) (only parsing).
End SubChoice_isSubRing.

#[deprecated(since="mathcomp 2.4.0",
             note="Use SubChoice_isSubNzRing instead.")]
Notation SubChoice_isSubRing R S U :=
  (SubChoice_isSubNzRing R S U) (only parsing).

HB.builders Context (R : nzRingType) S U of SubChoice_isSubNzRing R S U.
HB.instance Definition _ := SubChoice_isSubZmodule.Build R S U
  (subring_closedB subring_closed_subproof).
HB.instance Definition _ := SubZmodule_isSubNzRing.Build R S U
  subring_closed_subproof.
HB.end.

HB.factory Record SubChoice_isSubComPzRing (R : comPzRingType) S U
    of SubChoice R S U := {
  subring_closed_subproof : subring_closed S
}.

HB.builders Context (R : comPzRingType) S U of SubChoice_isSubComPzRing R S U.
HB.instance Definition _ := SubChoice_isSubPzRing.Build R S U
  subring_closed_subproof.
HB.instance Definition _ := SubPzRing_isSubComPzRing.Build R S U.
HB.end.

HB.factory Record SubChoice_isSubComNzRing (R : comNzRingType) S U
    of SubChoice R S U := {
  subring_closed_subproof : subring_closed S
}.

Module SubChoice_isSubComRing.
#[deprecated(since="mathcomp 2.4.0",
             note="Use SubChoice_isSubComNzRing.Build instead.")]
Notation Build R S U := (SubChoice_isSubComNzRing.Build R S U) (only parsing).
End SubChoice_isSubComRing.

#[deprecated(since="mathcomp 2.4.0",
             note="Use SubChoice_isSubComNzRing instead.")]
Notation SubChoice_isSubComRing R S U :=
  (SubChoice_isSubComNzRing R S U) (only parsing).

HB.builders Context (R : comNzRingType) S U of SubChoice_isSubComNzRing R S U.
HB.instance Definition _ := SubChoice_isSubNzRing.Build R S U
  subring_closed_subproof.
HB.instance Definition _ := SubNzRing_isSubComNzRing.Build R S U.
HB.end.

HB.factory Record SubChoice_isSubLmodule (R : pzRingType) (V : lmodType R) S W
    of SubChoice V S W := {
  submod_closed_subproof : submod_closed S
}.

HB.builders Context (R : pzRingType) (V : lmodType R) S W
  of SubChoice_isSubLmodule R V S W.
HB.instance Definition _ := SubChoice_isSubZmodule.Build V S W
  (submod_closedB submod_closed_subproof).
HB.instance Definition _ := SubZmodule_isSubLmodule.Build R V S W
  submod_closed_subproof.
HB.end.

HB.factory Record SubChoice_isSubLalgebra (R : pzRingType) (A : lalgType R) S W
    of SubChoice A S W := {
  subalg_closed_subproof : subalg_closed S
}.

HB.builders Context (R : pzRingType) (A : lalgType R) S W
  of SubChoice_isSubLalgebra R A S W.
HB.instance Definition _ := SubChoice_isSubNzRing.Build A S W
  (subalg_closedBM subalg_closed_subproof).
HB.instance Definition _ := SubZmodule_isSubLmodule.Build R A S W
  (subalg_closedZ subalg_closed_subproof).
HB.instance Definition _ := SubNzRing_SubLmodule_isSubLalgebra.Build R A S W.
HB.end.

HB.factory Record SubChoice_isSubAlgebra (R : pzRingType) (A : algType R) S W
    of SubChoice A S W := {
  subalg_closed_subproof : subalg_closed S
}.

HB.builders Context (R : pzRingType) (A : algType R) S W
  of SubChoice_isSubAlgebra R A S W.
HB.instance Definition _ := SubChoice_isSubLalgebra.Build R A S W
  subalg_closed_subproof.
HB.instance Definition _ := SubLalgebra_isSubAlgebra.Build R A S W.
HB.end.

HB.factory Record SubChoice_isSubUnitRing (R : unitRingType) S U
    of SubChoice R S U := {
  divring_closed_subproof : divring_closed S
}.

HB.builders Context (R : unitRingType) S U of SubChoice_isSubUnitRing R S U.
HB.instance Definition _ := SubChoice_isSubNzRing.Build R S U
  (divring_closedBM divring_closed_subproof).
HB.instance Definition _ := SubNzRing_isSubUnitRing.Build R S U
  divring_closed_subproof.
HB.end.

HB.factory Record SubChoice_isSubComUnitRing (R : comUnitRingType) S U
    of SubChoice R S U := {
  divring_closed_subproof : divring_closed S
}.

HB.builders Context (R : comUnitRingType) S U
  of SubChoice_isSubComUnitRing R S U.
HB.instance Definition _ := SubChoice_isSubComNzRing.Build R S U
  (divring_closedBM divring_closed_subproof).
HB.instance Definition _ := SubNzRing_isSubUnitRing.Build R S U
  divring_closed_subproof.
HB.end.

HB.factory Record SubChoice_isSubIntegralDomain (R : idomainType) S U
    of SubChoice R S U := {
  divring_closed_subproof : divring_closed S
}.

HB.builders Context (R : idomainType) S U
  of SubChoice_isSubIntegralDomain R S U.
HB.instance Definition _ := SubChoice_isSubComUnitRing.Build R S U
  divring_closed_subproof.
HB.instance Definition _ := SubComUnitRing_isSubIntegralDomain.Build R S U.
HB.end.

Module SubExports.

Notation "[ 'SubChoice_isSubNmodule' 'of' U 'by' <: ]" :=
  (SubChoice_isSubNmodule.Build _ _ U rpred0D)
  (at level 0, format "[ 'SubChoice_isSubNmodule'  'of'  U  'by'  <: ]")
  : form_scope.
Notation "[ 'SubChoice_isSubZmodule' 'of' U 'by' <: ]" :=
  (SubChoice_isSubZmodule.Build _ _ U (zmodClosedP _))
  (at level 0, format "[ 'SubChoice_isSubZmodule'  'of'  U  'by'  <: ]")
  : form_scope.
Notation "[ 'SubNmodule_isSubNzSemiRing' 'of' U 'by' <: ]" :=
  (SubNmodule_isSubNzSemiRing.Build _ _ U (@rpred1M _ _))
  (at level 0, format "[ 'SubNmodule_isSubNzSemiRing'  'of'  U  'by'  <: ]")
  : form_scope.
#[deprecated(since="mathcomp 2.4.0",
             note="Use [ SubNmodule_isSubNzSemiRing of U by <: ] instead.")]
Notation "[ 'SubNmodule_isSubSemiRing' 'of' U 'by' <: ]" :=
  (SubNmodule_isSubNzSemiRing.Build _ _ U (@rpred1M _ _))
  (at level 0, format "[ 'SubNmodule_isSubSemiRing'  'of'  U  'by'  <: ]")
  : form_scope.
Notation "[ 'SubChoice_isSubNzSemiRing' 'of' U 'by' <: ]" :=
  (SubChoice_isSubNzSemiRing.Build _ _ U (semiringClosedP _))
  (at level 0, format "[ 'SubChoice_isSubNzSemiRing'  'of'  U  'by'  <: ]")
  : form_scope.
#[deprecated(since="mathcomp 2.4.0",
             note="Use [ 'SubChoice_isSubNzSemiRing' of U by <: ] instead.")]
Notation "[ 'SubChoice_isSubSemiRing' 'of' U 'by' <: ]" :=
  (SubChoice_isSubNzSemiRing.Build _ _ U (semiringClosedP _))
  (at level 0, format "[ 'SubChoice_isSubSemiRing'  'of'  U  'by'  <: ]")
  : form_scope.
Notation "[ 'SubNzSemiRing_isSubComNzSemiRing' 'of' U 'by' <: ]" :=
  (SubNzSemiRing_isSubComNzSemiRing.Build _ _ U)
  (at level 0, format "[ 'SubNzSemiRing_isSubComNzSemiRing'  'of'  U  'by'  <: ]")
  : form_scope.
#[deprecated(since="mathcomp 2.4.0",
        note="Use [ 'SubNzSemiRing_isSubComNzSemiRing' of U by <: ] instead.")]
Notation "[ 'SubSemiRing_isSubComSemiRing' 'of' U 'by' <: ]" :=
  (SubNzSemiRing_isSubComNzSemiRing.Build _ _ U)
  (at level 0, format "[ 'SubSemiRing_isSubComSemiRing'  'of'  U  'by'  <: ]")
  : form_scope.
Notation "[ 'SubChoice_isSubComNzSemiRing' 'of' U 'by' <: ]" :=
  (SubChoice_isSubComNzSemiRing.Build _ _ U (semiringClosedP _))
  (at level 0, format "[ 'SubChoice_isSubComNzSemiRing'  'of'  U  'by'  <: ]")
  : form_scope.
#[deprecated(since="mathcomp 2.4.0",
             note="Use [ 'SubChoice_isSubComNzSemiRing' of U by <: ] instead.")]
Notation "[ 'SubChoice_isSubComSemiRing' 'of' U 'by' <: ]" :=
  (SubChoice_isSubComNzSemiRing.Build _ _ U (semiringClosedP _))
  (at level 0, format "[ 'SubChoice_isSubComSemiRing'  'of'  U  'by'  <: ]")
  : form_scope.
Notation "[ 'SubZmodule_isSubNzRing' 'of' U 'by' <: ]" :=
  (SubZmodule_isSubNzRing.Build _ _ U (subringClosedP _))
  (at level 0, format "[ 'SubZmodule_isSubNzRing'  'of'  U  'by'  <: ]")
  : form_scope.
#[deprecated(since="mathcomp 2.4.0",
             note="Use [ 'SubZmodule_isSubNzRing' of U by <: ] instead.")]
Notation "[ 'SubZmodule_isSubRing' 'of' U 'by' <: ]" :=
  (SubZmodule_isSubNzRing.Build _ _ U (subringClosedP _))
  (at level 0, format "[ 'SubZmodule_isSubRing'  'of'  U  'by'  <: ]")
  : form_scope.
Notation "[ 'SubChoice_isSubNzRing' 'of' U 'by' <: ]" :=
  (SubChoice_isSubNzRing.Build _ _ U (subringClosedP _))
  (at level 0, format "[ 'SubChoice_isSubNzRing'  'of'  U  'by'  <: ]")
  : form_scope.
#[deprecated(since="mathcomp 2.4.0",
             note="Use [ 'SubChoice_isSubNzRing' of U by <: ] instead.")]
Notation "[ 'SubChoice_isSubRing' 'of' U 'by' <: ]" :=
  (SubChoice_isSubNzRing.Build _ _ U (subringClosedP _))
  (at level 0, format "[ 'SubChoice_isSubRing'  'of'  U  'by'  <: ]")
  : form_scope.
Notation "[ 'SubNzRing_isSubComNzRing' 'of' U 'by' <: ]" :=
  (SubNzRing_isSubComNzRing.Build _ _ U)
  (at level 0, format "[ 'SubNzRing_isSubComNzRing'  'of'  U  'by'  <: ]")
  : form_scope.
#[deprecated(since="mathcomp 2.4.0",
             note="Use [ 'SubNzRing_isSubComNzRing' of U by <: ] instead.")]
Notation "[ 'SubRing_isSubComRing' 'of' U 'by' <: ]" :=
  (SubNzRing_isSubComNzRing.Build _ _ U)
  (at level 0, format "[ 'SubRing_isSubComRing'  'of'  U  'by'  <: ]")
  : form_scope.
Notation "[ 'SubChoice_isSubComNzRing' 'of' U 'by' <: ]" :=
  (SubChoice_isSubComNzRing.Build _ _ U (subringClosedP _))
  (at level 0, format "[ 'SubChoice_isSubComNzRing'  'of'  U  'by'  <: ]")
  : form_scope.
#[deprecated(since="mathcomp 2.4.0",
             note="Use [ 'SubChoice_isSubComNzRing' of U by <: ] instead.")]
Notation "[ 'SubChoice_isSubComRing' 'of' U 'by' <: ]" :=
  (SubChoice_isSubComNzRing.Build _ _ U (subringClosedP _))
  (at level 0, format "[ 'SubChoice_isSubComRing'  'of'  U  'by'  <: ]")
  : form_scope.
Notation "[ 'SubZmodule_isSubLmodule' 'of' U 'by' <: ]" :=
  (SubZmodule_isSubLmodule.Build _ _ _ U (submodClosedP _))
  (at level 0, format "[ 'SubZmodule_isSubLmodule'  'of'  U  'by'  <: ]")
  : form_scope.
Notation "[ 'SubChoice_isSubLmodule' 'of' U 'by' <: ]" :=
  (SubChoice_isSubLmodule.Build _ _ _ U (submodClosedP _))
  (at level 0, format "[ 'SubChoice_isSubLmodule'  'of'  U  'by'  <: ]")
  : form_scope.
Notation "[ 'SubNzRing_SubLmodule_isSubLalgebra' 'of' U 'by' <: ]" :=
  (SubNzRing_SubLmodule_isSubLalgebra.Build _ _ _ U)
  (at level 0,
    format "[ 'SubNzRing_SubLmodule_isSubLalgebra'  'of'  U  'by'  <: ]")
  : form_scope.
#[deprecated(since="mathcomp 2.4.0",
      note="Use [ 'SubNzRing_SubLmodule_isSubLalgebra' of U by <: ] instead.")]
Notation "[ 'SubRing_SubLmodule_isSubLalgebra' 'of' U 'by' <: ]" :=
  (SubNzRing_SubLmodule_isSubLalgebra.Build _ _ _ U)
  (at level 0, format "[ 'SubRing_SubLmodule_isSubLalgebra'  'of'  U  'by'  <: ]")
  : form_scope.
Notation "[ 'SubChoice_isSubLalgebra' 'of' U 'by' <: ]" :=
  (SubChoice_isSubLalgebra.Build _ _ _ U (subalgClosedP _))
  (at level 0, format "[ 'SubChoice_isSubLalgebra'  'of'  U  'by'  <: ]")
  : form_scope.
Notation "[ 'SubLalgebra_isSubAlgebra' 'of' U 'by' <: ]" :=
  (SubLalgebra_isSubAlgebra.Build _ _ _ U)
  (at level 0, format "[ 'SubLalgebra_isSubAlgebra'  'of'  U  'by'  <: ]")
  : form_scope.
Notation "[ 'SubChoice_isSubAlgebra' 'of' U 'by' <: ]" :=
  (SubChoice_isSubAlgebra.Build _ _ _ U (subalgClosedP _))
  (at level 0, format "[ 'SubChoice_isSubAlgebra'  'of'  U  'by'  <: ]")
  : form_scope.
Notation "[ 'SubNzRing_isSubUnitRing' 'of' U 'by' <: ]" :=
  (SubNzRing_isSubUnitRing.Build _ _ U (divringClosedP _))
  (at level 0, format "[ 'SubNzRing_isSubUnitRing'  'of'  U  'by'  <: ]")
  : form_scope.
#[deprecated(since="mathcomp 2.4.0",
             note="Use [ 'SubNzRing_isSubUnitRing' of U by <: ] instead.")]
Notation "[ 'SubRing_isSubUnitRing' 'of' U 'by' <: ]" :=
  (SubNzRing_isSubUnitRing.Build _ _ U (divringClosedP _))
  (at level 0, format "[ 'SubRing_isSubUnitRing'  'of'  U  'by'  <: ]")
  : form_scope.
Notation "[ 'SubChoice_isSubUnitRing' 'of' U 'by' <: ]" :=
  (SubChoice_isSubUnitRing.Build _ _ U (divringClosedP _))
  (at level 0, format "[ 'SubChoice_isSubUnitRing'  'of'  U  'by'  <: ]")
  : form_scope.
Notation "[ 'SubChoice_isSubComUnitRing' 'of' U 'by' <: ]" :=
  (SubChoice_isSubComUnitRing.Build _ _ U (divringClosedP _))
  (at level 0, format "[ 'SubChoice_isSubComUnitRing'  'of'  U  'by'  <: ]")
  : form_scope.
Notation "[ 'SubComUnitRing_isSubIntegralDomain' 'of' U 'by' <: ]" :=
  (SubComUnitRing_isSubIntegralDomain.Build _ _ U)
  (at level 0,
    format "[ 'SubComUnitRing_isSubIntegralDomain'  'of'  U  'by'  <: ]")
  : form_scope.
Notation "[ 'SubChoice_isSubIntegralDomain' 'of' U 'by' <: ]" :=
  (SubChoice_isSubIntegralDomain.Build _ _ U (divringClosedP _))
  (at level 0, format "[ 'SubChoice_isSubIntegralDomain'  'of'  U  'by'  <: ]")
  : form_scope.
Notation "[ 'SubIntegralDomain_isSubField' 'of' U 'by' <: ]" :=
  (SubIntegralDomain_isSubField.Build _ _ U (frefl _))
  (at level 0, format "[ 'SubIntegralDomain_isSubField'  'of'  U  'by'  <: ]")
  : form_scope.

End SubExports.
HB.export SubExports.

Module Theory.

Definition addrA := @addrA.
Definition addrC := @addrC.
Definition add0r := @add0r.
Definition addNr := @addNr.
Definition addr0 := addr0.
Definition addrN := addrN.
Definition subrr := subrr.
Definition addrCA := addrCA.
Definition addrAC := addrAC.
Definition addrACA := addrACA.
Definition addKr := addKr.
Definition addNKr := addNKr.
Definition addrK := addrK.
Definition addrNK := addrNK.
Definition subrK := subrK.
Definition subKr := subKr.
Definition addrI := @addrI.
Definition addIr := @addIr.
Definition subrI := @subrI.
Definition subIr := @subIr.
Arguments addrI {V} y [x1 x2].
Arguments addIr {V} x [x1 x2].
Arguments subrI {V} y [x1 x2].
Arguments subIr {V} x [x1 x2].
Definition opprK := @opprK.
Arguments opprK {V}.
Definition oppr_inj := @oppr_inj.
Arguments oppr_inj {V} [x1 x2].
Definition oppr0 := oppr0.
Definition oppr_eq0 := oppr_eq0.
Definition opprD := opprD.
Definition opprB := opprB.
Definition addrKA := addrKA.
Definition subrKA := subrKA.
Definition subr0 := subr0.
Definition sub0r := sub0r.
Definition subr_eq := subr_eq.
Definition addr0_eq := addr0_eq.
Definition subr0_eq := subr0_eq.
Definition subr_eq0 := subr_eq0.
Definition addr_eq0 := addr_eq0.
Definition eqr_opp := eqr_opp.
Definition eqr_oppLR := eqr_oppLR.
Definition sumrN := sumrN.
Definition sumrB := sumrB.
Definition sumrMnl := sumrMnl.
Definition sumrMnr := sumrMnr.
Definition sumr_const := sumr_const.
Definition sumr_const_nat := sumr_const_nat.
Definition telescope_sumr := telescope_sumr.
Definition telescope_sumr_eq := @telescope_sumr_eq.
Arguments telescope_sumr_eq {V n m} f u.
Definition mulr0n := mulr0n.
Definition mulr1n := mulr1n.
Definition mulr2n := mulr2n.
Definition mulrS := mulrS.
Definition mulrSr := mulrSr.
Definition mulrb := mulrb.
Definition mul0rn := mul0rn.
Definition mulNrn := mulNrn.
Definition mulrnDl := mulrnDl.
Definition mulrnDr := mulrnDr.
Definition mulrnBl := mulrnBl.
Definition mulrnBr := mulrnBr.
Definition mulrnA := mulrnA.
Definition mulrnAC := mulrnAC.
Definition iter_addr := iter_addr.
Definition iter_addr_0 := iter_addr_0.
Definition mulrA := @mulrA.
Definition mul1r := @mul1r.
Definition mulr1 := @mulr1.
Definition mulrDl := @mulrDl.
Definition mulrDr := @mulrDr.
Definition oner_neq0 := @oner_neq0.
Definition oner_eq0 := oner_eq0.
Definition mul0r := @mul0r.
Definition mulr0 := @mulr0.
Definition mulrN := mulrN.
Definition mulNr := mulNr.
Definition mulrNN := mulrNN.
Definition mulN1r := mulN1r.
Definition mulrN1 := mulrN1.
Definition mulr_suml := mulr_suml.
Definition mulr_sumr := mulr_sumr.
Definition mulrBl := mulrBl.
Definition mulrBr := mulrBr.
Definition mulrnAl := mulrnAl.
Definition mulrnAr := mulrnAr.
Definition mulr_natl := mulr_natl.
Definition mulr_natr := mulr_natr.
Definition natrD := natrD.
Definition nat1r := nat1r.
Definition natr1 := natr1.
Arguments natr1 {R} n.
Arguments nat1r {R} n.
Definition natrB := natrB.
Definition natr_sum := natr_sum.
Definition natrM := natrM.
Definition natrX := natrX.
Definition expr0 := expr0.
Definition exprS := exprS.
Definition expr1 := expr1.
Definition expr2 := expr2.
Definition expr0n := expr0n.
Definition expr1n := expr1n.
Definition exprD := exprD.
Definition exprSr := exprSr.
Definition expr_sum := expr_sum.
Definition commr_sym := commr_sym.
Definition commr_refl := commr_refl.
Definition commr0 := commr0.
Definition commr1 := commr1.
Definition commrN := commrN.
Definition commrN1 := commrN1.
Definition commrD := commrD.
Definition commrB := commrB.
Definition commr_sum := commr_sum.
Definition commr_prod := commr_prod.
Definition commrMn := commrMn.
Definition commrM := commrM.
Definition commr_nat := commr_nat.
Definition commrX := commrX.
Definition exprMn_comm := exprMn_comm.
Definition commr_sign := commr_sign.
Definition exprMn_n := exprMn_n.
Definition exprM := exprM.
Definition exprAC := exprAC.
Definition expr_mod := expr_mod.
Definition expr_dvd := expr_dvd.
Definition signr_odd := signr_odd.
Definition signr_eq0 := signr_eq0.
Definition mulr_sign := mulr_sign.
Definition signr_addb := signr_addb.
Definition signrN := signrN.
Definition signrE := signrE.
Definition mulr_signM := mulr_signM.
Definition exprNn := exprNn.
Definition sqrrN := sqrrN.
Definition sqrr_sign := sqrr_sign.
Definition signrMK := signrMK.
Definition mulrI_eq0 := mulrI_eq0.
Definition lreg_neq0 := lreg_neq0.
Definition mulrI0_lreg := mulrI0_lreg.
Definition lregN := lregN.
Definition lreg1 := lreg1.
Definition lregM := lregM.
Definition lregX := lregX.
Definition lreg_sign := lreg_sign.
Definition lregP {R x} := @lregP R x.
Definition mulIr_eq0 := mulIr_eq0.
Definition mulIr0_rreg := mulIr0_rreg.
Definition rreg_neq0 := rreg_neq0.
Definition rregN := rregN.
Definition rreg1 := rreg1.
Definition rregM := rregM.
Definition revrX := revrX.
Definition rregX := rregX.
Definition rregP {R x} := @rregP R x.
Definition exprDn_comm := exprDn_comm.
Definition exprBn_comm := exprBn_comm.
Definition subrXX_comm := subrXX_comm.
Definition exprD1n := exprD1n.
Definition subrX1 := subrX1.
Definition sqrrD1 := sqrrD1.
Definition sqrrB1 := sqrrB1.
Definition subr_sqr_1 := subr_sqr_1.
Definition charf0 := charf0.
Definition charf_prime := charf_prime.
Definition mulrn_char := mulrn_char.
Definition dvdn_charf := dvdn_charf.
Definition charf_eq := charf_eq.
Definition bin_lt_charf_0 := bin_lt_charf_0.
Definition Frobenius_autE := Frobenius_autE.
Definition Frobenius_aut0 := Frobenius_aut0.
Definition Frobenius_aut1 := Frobenius_aut1.
Definition Frobenius_autD_comm := Frobenius_autD_comm.
Definition Frobenius_autMn := Frobenius_autMn.
Definition Frobenius_aut_nat := Frobenius_aut_nat.
Definition Frobenius_autM_comm := Frobenius_autM_comm.
Definition Frobenius_autX := Frobenius_autX.
Definition Frobenius_autN := Frobenius_autN.
Definition Frobenius_autB_comm := Frobenius_autB_comm.
Definition exprNn_char := exprNn_char.
Definition addrr_char2 := addrr_char2.
Definition oppr_char2 := oppr_char2.
Definition addrK_char2 := addrK_char2.
Definition addKr_char2 := addKr_char2.
Definition iter_mulr := iter_mulr.
Definition iter_mulr_1 := iter_mulr_1.
Definition prodr_const := prodr_const.
Definition prodr_const_nat := prodr_const_nat.
Definition mulrC := @mulrC.
Definition mulrCA := mulrCA.
Definition mulrAC := mulrAC.
Definition mulrACA := mulrACA.
Definition exprMn := exprMn.
Definition prodrXl := prodrXl.
Definition prodrXr := prodrXr.
Definition prodrN := prodrN.
Definition prodrMn_const := prodrMn_const.
Definition prodrM_comm := prodrM_comm.
Definition prodrMl_comm := prodrMl_comm.
Definition prodrMr_comm := prodrMr_comm.
Definition prodrMl := prodrMl.
Definition prodrMr := prodrMr.
Definition prodrMn := prodrMn.
Definition rev_prodr := rev_prodr.
Definition natr_prod := natr_prod.
Definition prodr_undup_exp_count := prodr_undup_exp_count.
Definition exprDn := exprDn.
Definition exprBn := exprBn.
Definition subrXX := subrXX.
Definition sqrrD := sqrrD.
Definition sqrrB := sqrrB.
Definition subr_sqr := subr_sqr.
Definition subr_sqrDB := subr_sqrDB.
Definition exprDn_char := exprDn_char.
Definition mulrV := mulrV.
Definition divrr := divrr.
Definition mulVr := mulVr.
Definition invr_out := invr_out.
Definition unitrP {R x} := @unitrP R x.
Definition mulKr := mulKr.
Definition mulVKr := mulVKr.
Definition mulrK := mulrK.
Definition mulrVK := mulrVK.
Definition divrK := divrK.
Definition mulrI := mulrI.
Definition mulIr := mulIr.
Definition divrI := divrI.
Definition divIr := divIr.
Definition telescope_prodr := telescope_prodr.
Definition telescope_prodr_eq := @telescope_prodr_eq.
Arguments telescope_prodr_eq {R n m} f u.
Definition commrV := commrV.
Definition unitrE := unitrE.
Definition invrK := @invrK.
Arguments invrK {R}.
Definition invr_inj := @invr_inj.
Arguments invr_inj {R} [x1 x2].
Definition unitrV := unitrV.
Definition unitr1 := unitr1.
Definition invr1 := invr1.
Definition divr1 := divr1.
Definition div1r := div1r.
Definition natr_div := natr_div.
Definition unitr0 := unitr0.
Definition invr0 := invr0.
Definition unitrN1 := unitrN1.
Definition unitrN := unitrN.
Definition invrN1 := invrN1.
Definition invrN := invrN.
Definition divrNN := divrNN.
Definition divrN := divrN.
Definition invr_sign := invr_sign.
Definition unitrMl := unitrMl.
Definition unitrMr := unitrMr.
Definition invrM := invrM.
Definition unitr_prod := unitr_prod.
Definition unitr_prod_in := unitr_prod_in.
Definition invr_eq0 := invr_eq0.
Definition invr_eq1 := invr_eq1.
Definition invr_neq0 := invr_neq0.
Definition rev_unitrP := rev_unitrP.
Definition rev_prodrV := rev_prodrV.
Definition unitrM_comm := unitrM_comm.
Definition unitrX := unitrX.
Definition unitrX_pos := unitrX_pos.
Definition exprVn := exprVn.
Definition exprB := exprB.
Definition invr_signM := invr_signM.
Definition divr_signM := divr_signM.
Definition rpred0D := @rpred0D.
Definition rpred0 := rpred0.
Definition rpredD := rpredD.
Definition rpredNr := @rpredNr.
Definition rpred_sum := rpred_sum.
Definition rpredMn := rpredMn.
Definition rpredN := rpredN.
Definition rpredB := rpredB.
Definition rpredBC := rpredBC.
Definition rpredMNn := rpredMNn.
Definition rpredDr := rpredDr.
Definition rpredDl := rpredDl.
Definition rpredBr := rpredBr.
Definition rpredBl := rpredBl.
Definition zmodClosedP := zmodClosedP.
Definition rpredMsign := rpredMsign.
Definition rpred1M := @rpred1M.
Definition rpred1 := @rpred1.
Definition rpredM := @rpredM.
Definition rpred_prod := rpred_prod.
Definition rpredX := rpredX.
Definition rpred_nat := rpred_nat.
Definition rpredN1 := rpredN1.
Definition rpred_sign := rpred_sign.
Definition semiringClosedP := semiringClosedP.
Definition subringClosedP := subringClosedP.
Definition rpredZsign := rpredZsign.
Definition rpredZnat := rpredZnat.
Definition submodClosedP := submodClosedP.
Definition subalgClosedP := subalgClosedP.
Definition rpredZ := @rpredZ.
Definition rpredVr := @rpredVr.
Definition rpredV := rpredV.
Definition rpred_div := rpred_div.
Definition rpredXN := rpredXN.
Definition rpredZeq := rpredZeq.
Definition char_lalg := char_lalg.
Definition rpredMr := rpredMr.
Definition rpredMl := rpredMl.
Definition rpred_divr := rpred_divr.
Definition rpred_divl := rpred_divl.
Definition divringClosedP := divringClosedP.
Definition eq_eval := eq_eval.
Definition eval_tsubst := eval_tsubst.
Definition eq_holds := eq_holds.
Definition holds_fsubst := holds_fsubst.
Definition unitrM := unitrM.
Definition unitr_prodP := unitr_prodP.
Definition prodrV := prodrV.
Definition unitrPr {R x} := @unitrPr R x.
Definition expr_div_n := expr_div_n.
Definition mulr1_eq := mulr1_eq.
Definition divr1_eq := divr1_eq.
Definition divKr := divKr.
Definition mulf_eq0 := mulf_eq0.
Definition prodf_eq0 := prodf_eq0.
Definition prodf_seq_eq0 := prodf_seq_eq0.
Definition mulf_neq0 := mulf_neq0.
Definition prodf_neq0 := prodf_neq0.
Definition prodf_seq_neq0 := prodf_seq_neq0.
Definition expf_eq0 := expf_eq0.
Definition sqrf_eq0 := sqrf_eq0.
Definition expf_neq0 := expf_neq0.
Definition natf_neq0 := natf_neq0.
Definition natf0_char := natf0_char.
Definition charf'_nat := charf'_nat.
Definition charf0P := charf0P.
Definition eqf_sqr := eqf_sqr.
Definition mulfI := mulfI.
Definition mulIf := mulIf.
Definition divfI := divfI.
Definition divIf := divIf.
Definition sqrf_eq1 := sqrf_eq1.
Definition expfS_eq1 := expfS_eq1.
Definition fieldP := @fieldP.
Definition unitfE := unitfE.
Definition mulVf := mulVf.
Definition mulfV := mulfV.
Definition divff := divff.
Definition mulKf := mulKf.
Definition mulVKf := mulVKf.
Definition mulfK := mulfK.
Definition mulfVK := mulfVK.
Definition divfK := divfK.
Definition divKf := divKf.
Definition invfM := invfM.
Definition invf_div := invf_div.
Definition expfB_cond := expfB_cond.
Definition expfB := expfB.
Definition prodfV := prodfV.
Definition prodf_div := prodf_div.
Definition telescope_prodf := telescope_prodf.
Definition telescope_prodf_eq := @telescope_prodf_eq.
Arguments telescope_prodf_eq {F n m} f u.
Definition addf_div := addf_div.
Definition mulf_div := mulf_div.
Definition eqr_div := eqr_div.
Definition eqr_sum_div := eqr_sum_div.
Definition char0_natf_div := char0_natf_div.
Definition fpredMr := fpredMr.
Definition fpredMl := fpredMl.
Definition fpred_divr := fpred_divr.
Definition fpred_divl := fpred_divl.
Definition satP {F e f} := @satP F e f.
Definition eq_sat := eq_sat.
Definition solP {F n f} := @solP F n f.
Definition eq_sol := eq_sol.
Definition size_sol := size_sol.
Definition solve_monicpoly := @solve_monicpoly.
Definition semi_additive := semi_additive.
Definition additive := additive.
Definition raddf0 := raddf0.
Definition raddf_eq0 := raddf_eq0.
Definition raddf_inj := raddf_inj.
Definition raddfN := raddfN.
Definition raddfD := raddfD.
Definition raddfB := raddfB.
Definition raddf_sum := raddf_sum.
Definition raddfMn := raddfMn.
Definition raddfMNn := raddfMNn.
Definition raddfMnat := raddfMnat.
Definition raddfMsign := raddfMsign.
Definition can2_semi_additive := can2_semi_additive.
Definition can2_additive := can2_additive.
Definition multiplicative := multiplicative.
Definition rmorph0 := rmorph0.
Definition rmorphN := rmorphN.
Definition rmorphD := rmorphD.
Definition rmorphB := rmorphB.
Definition rmorph_sum := rmorph_sum.
Definition rmorphMn := rmorphMn.
Definition rmorphMNn := rmorphMNn.
Definition rmorphismMP := rmorphismMP.
Definition rmorph1 := rmorph1.
Definition rmorph_eq1 := rmorph_eq1.
Definition rmorphM := rmorphM.
Definition rmorphMsign := rmorphMsign.
Definition rmorph_nat := rmorph_nat.
Definition rmorph_eq_nat := rmorph_eq_nat.
Definition rmorph_prod := rmorph_prod.
Definition rmorphXn := rmorphXn.
Definition rmorphN1 := rmorphN1.
Definition rmorph_sign := rmorph_sign.
Definition rmorph_char := rmorph_char.
Definition can2_rmorphism := can2_rmorphism.
Definition rmorph_comm := rmorph_comm.
Definition rmorph_unit := rmorph_unit.
Definition rmorphV := rmorphV.
Definition rmorph_div := rmorph_div.
Definition fmorph_eq0 := fmorph_eq0.
Definition fmorph_inj := @fmorph_inj.
Arguments fmorph_inj {F R} f [x1 x2].
Definition fmorph_eq := fmorph_eq.
Definition fmorph_eq1 := fmorph_eq1.
Definition fmorph_char := fmorph_char.
Definition fmorph_unit := fmorph_unit.
Definition fmorphV := fmorphV.
Definition fmorph_div := fmorph_div.
Definition scalerA := scalerA.
Definition scale1r := @scale1r.
Definition scalerDr := @scalerDr.
Definition scalerDl := @scalerDl.
Definition scaler0 := scaler0.
Definition scale0r := scale0r.
Definition scaleNr := scaleNr.
Definition scaleN1r := scaleN1r.
Definition scalerN := scalerN.
Definition scalerBl := scalerBl.
Definition scalerBr := scalerBr.
Definition scaler_nat := scaler_nat.
Definition scalerMnl := scalerMnl.
Definition scalerMnr := scalerMnr.
Definition scaler_suml := scaler_suml.
Definition scaler_sumr := scaler_sumr.
Definition scaler_eq0 := scaler_eq0.
Definition scalerK := scalerK.
Definition scalerKV := scalerKV.
Definition scalerI := scalerI.
Definition scalerAl := @scalerAl.
Definition mulr_algl := mulr_algl.
Definition scaler_sign := scaler_sign.
Definition signrZK := signrZK.
Definition scalerCA := scalerCA.
Definition scalerAr := @scalerAr.
Definition mulr_algr := mulr_algr.
Definition comm_alg := comm_alg.
Definition exprZn := exprZn.
Definition scaler_prodl := scaler_prodl.
Definition scaler_prodr := scaler_prodr.
Definition scaler_prod := scaler_prod.
Definition scaler_injl := scaler_injl.
Definition scaler_unit := scaler_unit.
Definition invrZ := invrZ.
Definition raddfZnat := raddfZnat.
Definition raddfZsign := raddfZsign.
Definition in_algE := in_algE.
Definition scalable_for := scalable_for.
Definition linear_for := linear_for.
Definition additive_linear := additive_linear.
Definition scalable_linear := scalable_linear.
Definition linear0 := linear0.
Definition linearN := linearN.
Definition linearD := linearD.
Definition linearB := linearB.
Definition linear_sum := linear_sum.
Definition linearMn := linearMn.
Definition linearMNn := linearMNn.
Definition linearP := linearP.
Definition linearZ_LR := linearZ_LR.
Definition linearZ := linearZ.
Definition linearPZ := linearPZ.
Definition linearZZ := linearZZ.
Definition scalarP := scalarP.
Definition scalarZ := scalarZ.
Definition can2_scalable := can2_scalable.
Definition can2_linear := can2_linear.
Definition rmorph_alg := rmorph_alg.
Definition imaginary_exists := imaginary_exists.

Definition raddf := (raddf0, raddfN, raddfD, raddfMn).

Definition rmorphE :=
  (rmorphD, rmorph0, rmorphB, rmorphN, rmorphMNn, rmorphMn, rmorph1, rmorphXn).

Definition linearE :=
  (linearD, linear0, linearB, linearMNn, linearMn, linearZ).

Notation null_fun V := (null_fun V) (only parsing).
Notation in_alg A := (in_alg A) (only parsing).

End Theory.

Module AllExports. HB.reexport. End AllExports.

End GRing.

Export AllExports.
Export Scale.Exports.
Export ClosedExports.

#[deprecated(since="mathcomp 2.4.0",
             note="Use nzSemiRingType instead.")]
Notation semiRingType := (nzSemiRingType) (only parsing).
#[deprecated(since="mathcomp 2.4.0",
             note="Use nzRingType instead.")]
Notation ringType := (nzRingType) (only parsing).
#[deprecated(since="mathcomp 2.4.0",
             note="Use comNzSemiRingType instead.")]
Notation comSemiRingType := (comNzSemiRingType) (only parsing).
#[deprecated(since="mathcomp 2.4.0",
             note="Use comNzRingType instead.")]
Notation comRingType := (comNzRingType) (only parsing).
#[deprecated(since="mathcomp 2.4.0",
             note="Use subNzSemiRingType instead.")]
Notation subSemiRingType := (subNzSemiRingType) (only parsing).
#[deprecated(since="mathcomp 2.4.0",
             note="Use subComNzSemiRingType instead.")]
Notation subComSemiRingType := (subComNzSemiRingType) (only parsing).
#[deprecated(since="mathcomp 2.4.0",
             note="Use nzSubRingType instead.")]
Notation subRingType := (nzSubRingType) (only parsing).
#[deprecated(since="mathcomp 2.4.0",
             note="Use subComNzRingType instead.")]
Notation subComNzRingType := (subComNzRingType) (only parsing).

Notation addrClosed := addrClosed.
Notation opprClosed := opprClosed.

Variant Ione := IOne : Ione.
Inductive Inatmul :=
  | INatmul : Ione -> nat -> Inatmul
  | IOpp : Inatmul -> Inatmul.
Variant Idummy_placeholder :=.

Definition parse (x : Number.int) : Inatmul :=
  match x with
  | Number.IntDecimal (Decimal.Pos u) => INatmul IOne (Nat.of_uint u)
  | Number.IntDecimal (Decimal.Neg u) => IOpp (INatmul IOne (Nat.of_uint u))
  | Number.IntHexadecimal (Hexadecimal.Pos u) =>
      INatmul IOne (Nat.of_hex_uint u)
  | Number.IntHexadecimal (Hexadecimal.Neg u) =>
      IOpp (INatmul IOne (Nat.of_hex_uint u))
  end.

Definition print (x : Inatmul) : option Number.int :=
  match x with
  | INatmul IOne n =>
      Some (Number.IntDecimal (Decimal.Pos (Nat.to_uint n)))
  | IOpp (INatmul IOne n) =>
      Some (Number.IntDecimal (Decimal.Neg (Nat.to_uint n)))
  | _ => None
  end.

Arguments GRing.one {_}.
Set Warnings "-via-type-remapping,-via-type-mismatch".
Number Notation Idummy_placeholder parse print (via Inatmul
  mapping [[natmul] => INatmul, [opp] => IOpp, [one] => IOne])
  : ring_scope.
Set Warnings "via-type-remapping,via-type-mismatch".
Arguments GRing.one : clear implicits.

Notation "0" := (@zero _) : ring_scope.
Notation "-%R" := (@opp _) : ring_scope.
Notation "- x" := (opp x) : ring_scope.
Notation "+%R" := (@add _) : function_scope.
Notation "x + y" := (add x y) : ring_scope.
Notation "x - y" := (add x (- y)) : ring_scope.
Arguments natmul : simpl never.
Notation "x *+ n" := (natmul x n) : ring_scope.
Notation "x *- n" := (opp (x *+ n)) : ring_scope.
Notation "s `_ i" := (seq.nth 0%R s%R i) : ring_scope.
Notation support := 0.-support.

Notation "1" := (@one _) : ring_scope.
Notation "- 1" := (opp 1) : ring_scope.

Notation "n %:R" := (natmul 1 n) : ring_scope.
Arguments GRing.char R%type.
Notation "[ 'char' R ]" := (GRing.char R) : ring_scope.
Notation has_char0 R := (GRing.char R =i pred0).
Notation Frobenius_aut chRp := (Frobenius_aut chRp).
Notation "*%R" := (@mul _) : function_scope.
Notation "x * y" := (mul x y) : ring_scope.
Arguments exp : simpl never.
Notation "x ^+ n" := (exp x n) : ring_scope.
Notation "x ^-1" := (inv x) : ring_scope.
Notation "x ^- n" := (inv (x ^+ n)) : ring_scope.
Notation "x / y" := (mul x y^-1) : ring_scope.

Notation "*:%R" := (@scale _ _) : function_scope.
Notation "a *: m" := (scale a m) : ring_scope.
Notation "k %:A" := (scale k 1) : ring_scope.
Notation "\0" := (null_fun _) : ring_scope.
Notation "f \+ g" := (add_fun f g) : ring_scope.
Notation "f \- g" := (sub_fun f g) : ring_scope.
Notation "\- f" := (opp_fun f) : ring_scope.
Notation "a \*: f" := (scale_fun a f) : ring_scope.
Notation "x \*o f" := (mull_fun x f) : ring_scope.
Notation "x \o* f" := (mulr_fun x f) : ring_scope.
Notation "f \* g" := (mul_fun f g) : ring_scope.

Arguments mull_fun {_ _}  a f _ /.
Arguments mulr_fun {_ _} a f _ /.
Arguments scale_fun {_ _ _} a f _ /.
Arguments mul_fun {_ _} f g _ /.

Notation "\sum_ ( i <- r | P ) F" :=
  (\big[+%R/0%R]_(i <- r | P%B) F%R) : ring_scope.
Notation "\sum_ ( i <- r ) F" :=
  (\big[+%R/0%R]_(i <- r) F%R) : ring_scope.
Notation "\sum_ ( m <= i < n | P ) F" :=
  (\big[+%R/0%R]_(m <= i < n | P%B) F%R) : ring_scope.
Notation "\sum_ ( m <= i < n ) F" :=
  (\big[+%R/0%R]_(m <= i < n) F%R) : ring_scope.
Notation "\sum_ ( i | P ) F" :=
  (\big[+%R/0%R]_(i | P%B) F%R) : ring_scope.
Notation "\sum_ i F" :=
  (\big[+%R/0%R]_i F%R) : ring_scope.
Notation "\sum_ ( i : t | P ) F" :=
  (\big[+%R/0%R]_(i : t | P%B) F%R) (only parsing) : ring_scope.
Notation "\sum_ ( i : t ) F" :=
  (\big[+%R/0%R]_(i : t) F%R) (only parsing) : ring_scope.
Notation "\sum_ ( i < n | P ) F" :=
  (\big[+%R/0%R]_(i < n | P%B) F%R) : ring_scope.
Notation "\sum_ ( i < n ) F" :=
  (\big[+%R/0%R]_(i < n) F%R) : ring_scope.
Notation "\sum_ ( i 'in' A | P ) F" :=
  (\big[+%R/0%R]_(i in A | P%B) F%R) : ring_scope.
Notation "\sum_ ( i 'in' A ) F" :=
  (\big[+%R/0%R]_(i in A) F%R) : ring_scope.

Notation "\prod_ ( i <- r | P ) F" :=
  (\big[*%R/1%R]_(i <- r | P%B) F%R) : ring_scope.
Notation "\prod_ ( i <- r ) F" :=
  (\big[*%R/1%R]_(i <- r) F%R) : ring_scope.
Notation "\prod_ ( m <= i < n | P ) F" :=
  (\big[*%R/1%R]_(m <= i < n | P%B) F%R) : ring_scope.
Notation "\prod_ ( m <= i < n ) F" :=
  (\big[*%R/1%R]_(m <= i < n) F%R) : ring_scope.
Notation "\prod_ ( i | P ) F" :=
  (\big[*%R/1%R]_(i | P%B) F%R) : ring_scope.
Notation "\prod_ i F" :=
  (\big[*%R/1%R]_i F%R) : ring_scope.
Notation "\prod_ ( i : t | P ) F" :=
  (\big[*%R/1%R]_(i : t | P%B) F%R) (only parsing) : ring_scope.
Notation "\prod_ ( i : t ) F" :=
  (\big[*%R/1%R]_(i : t) F%R) (only parsing) : ring_scope.
Notation "\prod_ ( i < n | P ) F" :=
  (\big[*%R/1%R]_(i < n | P%B) F%R) : ring_scope.
Notation "\prod_ ( i < n ) F" :=
  (\big[*%R/1%R]_(i < n) F%R) : ring_scope.
Notation "\prod_ ( i 'in' A | P ) F" :=
  (\big[*%R/1%R]_(i in A | P%B) F%R) : ring_scope.
Notation "\prod_ ( i 'in' A ) F" :=
  (\big[*%R/1%R]_(i in A) F%R) : ring_scope.

Notation "R ^c" := (converse R) (at level 2, format "R ^c") : type_scope.
Notation "R ^o" := (regular R) (at level 2, format "R ^o") : type_scope.

Bind Scope term_scope with term.
Bind Scope term_scope with formula.

Notation "''X_' i" := (Var _ i) : term_scope.
Notation "n %:R" := (NatConst _ n) : term_scope.
Notation "0" := 0%:R%T : term_scope.
Notation "1" := 1%:R%T : term_scope.
Notation "x %:T" := (Const x) : term_scope.
Infix "+" := Add : term_scope.
Notation "- t" := (Opp t) : term_scope.
Notation "t - u" := (Add t (- u)) : term_scope.
Infix "*" := Mul : term_scope.
Infix "*+" := NatMul : term_scope.
Notation "t ^-1" := (Inv t) : term_scope.
Notation "t / u" := (Mul t u^-1) : term_scope.
Infix "^+" := Exp : term_scope.
Infix "==" := Equal : term_scope.
Notation "x != y" := (GRing.Not (x == y)) : term_scope.
Infix "/\" := And : term_scope.
Infix "\/" := Or : term_scope.
Infix "==>" := Implies : term_scope.
Notation "~ f" := (Not f) : term_scope.
Notation "''exists' ''X_' i , f" := (Exists i f) : term_scope.
Notation "''forall' ''X_' i , f" := (Forall i f) : term_scope.

(* Lifting Structure from the codomain of finfuns. *)

Section Sum.

Variables (aT : finType) (rT : nmodType).
Variables (I : Type) (r : seq I) (P : pred I) (F : I -> {ffun aT -> rT}).

Lemma sum_ffunE x : (\sum_(i <- r | P i) F i) x = \sum_(i <- r | P i) F i x.
Proof. by elim/big_rec2: _ => // [|i _ y _ <-]; rewrite !ffunE. Qed.

Lemma sum_ffun :
  \sum_(i <- r | P i) F i = [ffun x => \sum_(i <- r | P i) F i x].
Proof. by apply/ffunP=> i; rewrite sum_ffunE ffunE. Qed.

End Sum.

Section FinFunSemiRing.

(* As rings require 1 != 0 in order to lift a ring structure over finfuns     *)
(* we need evidence that the domain is non-empty.                             *)

Variable (aT : finType) (R : pzSemiRingType).

Definition ffun_one : {ffun aT -> R} := [ffun => 1].
Definition ffun_mul (f g : {ffun aT -> R}) := [ffun x => f x * g x].

Fact ffun_mulA : associative ffun_mul.
Proof. by move=> f1 f2 f3; apply/ffunP=> i; rewrite !ffunE mulrA. Qed.
Fact ffun_mul_1l : left_id ffun_one ffun_mul.
Proof. by move=> f; apply/ffunP=> i; rewrite !ffunE mul1r. Qed.
Fact ffun_mul_1r : right_id ffun_one ffun_mul.
Proof. by move=> f; apply/ffunP=> i; rewrite !ffunE mulr1. Qed.
Fact ffun_mul_addl :  left_distributive ffun_mul (@ffun_add _ _).
Proof. by move=> f1 f2 f3; apply/ffunP=> i; rewrite !ffunE mulrDl. Qed.
Fact ffun_mul_addr :  right_distributive ffun_mul (@ffun_add _ _).
Proof. by move=> f1 f2 f3; apply/ffunP=> i; rewrite !ffunE mulrDr. Qed.
Fact ffun_mul_0l :  left_zero (@ffun_zero _ _) ffun_mul.
Proof. by move=> f; apply/ffunP=> i; rewrite !ffunE mul0r. Qed.
Fact ffun_mul_0r :  right_zero (@ffun_zero _ _) ffun_mul.
Proof. by move=> f; apply/ffunP=> i; rewrite !ffunE mulr0. Qed.

#[export]
HB.instance Definition _ := Nmodule_isPzSemiRing.Build {ffun aT -> R}
  ffun_mulA ffun_mul_1l ffun_mul_1r ffun_mul_addl ffun_mul_addr
  ffun_mul_0l ffun_mul_0r.
Definition ffun_semiring : pzSemiRingType := {ffun aT -> R}.
End FinFunSemiRing.

Section FinFunSemiRing.

Variable (aT : finType) (R : nzSemiRingType) (a : aT).

Fact ffun1_nonzero : ffun_one aT R != 0.
Proof. by apply/eqP => /ffunP/(_ a)/eqP; rewrite !ffunE oner_eq0. Qed.

(* TODO_HB uncomment once ffun_ring below is fixed
#[export]
HB.instance Definition _ := PzSemiRing_isNonZero.Build {ffun aT -> R}
  ffun1_nonzero.
*)

End FinFunSemiRing.

HB.instance Definition _ (aT : finType) (R : pzRingType) :=
  Zmodule_isPzRing.Build {ffun aT -> R}
  (@ffun_mulA _ _) (@ffun_mul_1l _ _) (@ffun_mul_1r _ _)
  (@ffun_mul_addl _ _) (@ffun_mul_addr _ _).

(* As nzRings require 1 != 0 in order to lift a ring structure over finfuns   *)
(* we need evidence that the domain is non-empty.                             *)

Section FinFunRing.

Variable (aT : finType) (R : nzRingType) (a : aT).

(* TODO_HB: doesn't work in combination with ffun_semiring above *)
HB.instance Definition _ :=
  PzSemiRing_isNonZero.Build {ffun aT -> R} (@ffun1_nonzero _ _ a).

Definition ffun_ring : nzRingType := {ffun aT -> R}.

End FinFunRing.

(* TODO_HB do FinFunComSemiRing once above is fixed *)
Section FinFunComRing.

Variable (aT : finType) (R : comPzRingType) (a : aT).

Fact ffun_mulC : commutative (@ffun_mul aT R).
Proof. by move=> f1 f2; apply/ffunP=> i; rewrite !ffunE mulrC. Qed.

(* TODO_HB
#[export]
HB.instance Definition _ :=
  Ring_hasCommutativeMul.Build (ffun_ring _ a) ffun_mulC.
*)

End FinFunComRing.

Section FinFunLmod.

Variable (R : pzRingType) (aT : finType) (rT : lmodType R).

Implicit Types f g : {ffun aT -> rT}.

Definition ffun_scale k f := [ffun a => k *: f a].

Fact ffun_scaleA k1 k2 f :
  ffun_scale k1 (ffun_scale k2 f) = ffun_scale (k1 * k2) f.
Proof. by apply/ffunP=> a; rewrite !ffunE scalerA. Qed.
Fact ffun_scale1 : left_id 1 ffun_scale.
Proof. by move=> f; apply/ffunP=> a; rewrite !ffunE scale1r. Qed.
Fact ffun_scale_addr k : {morph (ffun_scale k) : x y / x + y}.
Proof. by move=> f g; apply/ffunP=> a; rewrite !ffunE scalerDr. Qed.
Fact ffun_scale_addl u : {morph (ffun_scale)^~ u : k1 k2 / k1 + k2}.
Proof. by move=> k1 k2; apply/ffunP=> a; rewrite !ffunE scalerDl. Qed.

#[export]
HB.instance Definition _ := Zmodule_isLmodule.Build R {ffun aT -> rT}
  ffun_scaleA ffun_scale1 ffun_scale_addr ffun_scale_addl.

End FinFunLmod.

(* External direct product. *)

Section PairSemiRing.

Variables R1 R2 : pzSemiRingType.

Definition mul_pair (x y : R1 * R2) := (x.1 * y.1, x.2 * y.2).

Fact pair_mulA : associative mul_pair.
Proof. by move=> x y z; congr (_, _); apply: mulrA. Qed.

Fact pair_mul1l : left_id (1, 1) mul_pair.
Proof. by case=> x1 x2; congr (_, _); apply: mul1r. Qed.

Fact pair_mul1r : right_id (1, 1) mul_pair.
Proof. by case=> x1 x2; congr (_, _); apply: mulr1. Qed.

Fact pair_mulDl : left_distributive mul_pair +%R.
Proof. by move=> x y z; congr (_, _); apply: mulrDl. Qed.

Fact pair_mulDr : right_distributive mul_pair +%R.
Proof. by move=> x y z; congr (_, _); apply: mulrDr. Qed.

Fact pair_mul0r : left_zero 0 mul_pair.
Proof. by move=> x; congr (_, _); apply: mul0r. Qed.

Fact pair_mulr0 : right_zero 0 mul_pair.
Proof. by move=> x; congr (_, _); apply: mulr0. Qed.

#[export]
HB.instance Definition _ := Nmodule_isPzSemiRing.Build (R1 * R2)%type
  pair_mulA pair_mul1l pair_mul1r pair_mulDl pair_mulDr pair_mul0r pair_mulr0.

Fact fst_is_multiplicative : multiplicative fst. Proof. by []. Qed.
#[export]
HB.instance Definition _ := isMultiplicative.Build (R1 * R2)%type R1 fst
  fst_is_multiplicative.
Fact snd_is_multiplicative : multiplicative snd. Proof. by []. Qed.
#[export]
HB.instance Definition _ := isMultiplicative.Build (R1 * R2)%type R2 snd
  snd_is_multiplicative.

End PairSemiRing.

Section PairSemiRing.

Variables R1 R2 : nzSemiRingType.

Fact pair_one_neq0 : 1 != 0 :> R1 * R2.
Proof. by rewrite xpair_eqE oner_eq0. Qed.

#[export]
HB.instance Definition _ := PzSemiRing_isNonZero.Build (R1 * R2)%type
  pair_one_neq0.

End PairSemiRing.

Section PairComSemiRing.

Variables R1 R2 : comPzSemiRingType.

Fact pair_mulC : commutative (@mul_pair R1 R2).
Proof. by move=> x y; congr (_, _); apply: mulrC. Qed.

#[export]
HB.instance Definition _ := PzSemiRing_hasCommutativeMul.Build (R1 * R2)%type
  pair_mulC.

End PairComSemiRing.

(* TODO: HB.saturate *)
#[export]
HB.instance Definition _ (R1 R2 : nzRingType) := NzSemiRing.on (R1 * R1)%type.
#[export]
HB.instance Definition _ (R1 R2 : comNzRingType) := NzSemiRing.on (R1 * R1)%type.
(* /TODO *)

Section PairLmod.

Variables (R : pzRingType) (V1 V2 : lmodType R).

Definition scale_pair a (v : V1 * V2) : V1 * V2 := (a *: v.1, a *: v.2).

Fact pair_scaleA a b u : scale_pair a (scale_pair b u) = scale_pair (a * b) u.
Proof. by congr (_, _); apply: scalerA. Qed.

Fact pair_scale1 u : scale_pair 1 u = u.
Proof. by case: u => u1 u2; congr (_, _); apply: scale1r. Qed.

Fact pair_scaleDr : right_distributive scale_pair +%R.
Proof. by move=> a u v; congr (_, _); apply: scalerDr. Qed.

Fact pair_scaleDl u : {morph scale_pair^~ u: a b / a + b}.
Proof. by move=> a b; congr (_, _); apply: scalerDl. Qed.

#[export]
HB.instance Definition _ := Zmodule_isLmodule.Build R (V1 * V2)%type
  pair_scaleA pair_scale1 pair_scaleDr pair_scaleDl.

Fact fst_is_scalable : scalable fst. Proof. by []. Qed.
#[export]
HB.instance Definition _ :=
  isScalable.Build R (V1 * V2)%type V1 *:%R fst fst_is_scalable.
Fact snd_is_scalable : scalable snd. Proof. by []. Qed.
#[export]
HB.instance Definition _ :=
  isScalable.Build R (V1 * V2)%type V2 *:%R snd snd_is_scalable.

End PairLmod.

Section PairLalg.

Variables (R : pzRingType) (A1 A2 : lalgType R).

Fact pair_scaleAl a (u v : A1 * A2) : a *: (u * v) = (a *: u) * v.
Proof. by congr (_, _); apply: scalerAl. Qed.

#[export]
HB.instance Definition _ := Lmodule_isLalgebra.Build R (A1 * A2)%type
  pair_scaleAl.

#[export]
HB.instance Definition _ := RMorphism.on (@fst A1 A2).
#[export]
HB.instance Definition _ := RMorphism.on (@snd A1 A2).

End PairLalg.

Section PairAlg.

(* TODO: MC-1 port (R has been changed from comNzRingType to nzRingType) *)
Variables (R : nzRingType) (A1 A2 : algType R).

Fact pair_scaleAr a (u v : A1 * A2) : a *: (u * v) = u * (a *: v).
Proof. by congr (_, _); apply: scalerAr. Qed.

#[export]
HB.instance Definition _ := Lalgebra_isAlgebra.Build R (A1 * A2)%type
  pair_scaleAr.

End PairAlg.

Section PairUnitRing.

Variables R1 R2 : unitRingType.

Definition pair_unitr :=
  [qualify a x : R1 * R2 | (x.1 \is a GRing.unit) && (x.2 \is a GRing.unit)].
Definition pair_invr x :=
  if x \is a pair_unitr then (x.1^-1, x.2^-1) else x.

Lemma pair_mulVl : {in pair_unitr, left_inverse 1 pair_invr *%R}.
Proof.
rewrite /pair_invr=> x; case: ifP => // /andP[Ux1 Ux2] _.
by congr (_, _); apply: mulVr.
Qed.

Lemma pair_mulVr : {in pair_unitr, right_inverse 1 pair_invr *%R}.
Proof.
rewrite /pair_invr=> x; case: ifP => // /andP[Ux1 Ux2] _.
by congr (_, _); apply: mulrV.
Qed.

Lemma pair_unitP x y : y * x = 1 /\ x * y = 1 -> x \is a pair_unitr.
Proof.
case=> [[y1x y2x] [x1y x2y]]; apply/andP.
by split; apply/unitrP; [exists y.1 | exists y.2].
Qed.

Lemma pair_invr_out : {in [predC pair_unitr], pair_invr =1 id}.
Proof. by rewrite /pair_invr => x /negPf/= ->. Qed.

#[export]
HB.instance Definition _ := NzRing_hasMulInverse.Build (R1 * R2)%type
  pair_mulVl pair_mulVr pair_unitP pair_invr_out.

End PairUnitRing.

(* TODO: HB.saturate *)
#[export]
HB.instance Definition _ (R1 R2 : comUnitRingType) :=
  UnitRing.on (R1 * R2)%type.
#[export]
HB.instance Definition _ (R : nzRingType) (A1 A2 : comAlgType R) :=
  Algebra.on (A1 * A2)%type.
#[export]
HB.instance Definition _ (R : nzRingType) (A1 A2 : unitAlgType R) :=
  Algebra.on (A1 * A2)%type.
#[export]
HB.instance Definition _ (R : nzRingType) (A1 A2 : comUnitAlgType R) :=
  Algebra.on (A1 * A2)%type.
(* /TODO *)

Lemma pairMnE (M1 M2 : zmodType) (x : M1 * M2) n :
  x *+ n = (x.1 *+ n, x.2 *+ n).
Proof. by case: x => x y; elim: n => //= n; rewrite !mulrS => ->. Qed.

(* begin hide *)

(* Testing subtype hierarchy
Section Test0.

Variables (T : choiceType) (S : {pred T}).

Inductive B := mkB x & x \in S.
Definition vB u := let: mkB x _ := u in x.

HB.instance Definition _ := [isSub for vB].
HB.instance Definition _ := [Choice of B by <:].

End Test0.

Section Test1.

Variables (R : unitRingType) (S : divringClosed R).

HB.instance Definition _ := [SubChoice_isSubUnitRing of B S by <:].

End Test1.

Section Test2.

Variables (R : comUnitRingType) (A : unitAlgType R) (S : divalgClosed A).

HB.instance Definition _ := [SubZmodule_isSubLmodule of B S by <:].
HB.instance Definition _ := [SubNzRing_SubLmodule_isSubLalgebra of B S by <:].
HB.instance Definition _ := [SubLalgebra_isSubAlgebra of B S by <:].

End Test2.

Section Test3.

Variables (F : fieldType) (S : divringClosed F).

HB.instance Definition _ := [SubRing_isSubComNzRing of B S by <:].
HB.instance Definition _ := [SubComUnitRing_isSubIntegralDomain of B S by <:].
HB.instance Definition _ := [SubIntegralDomain_isSubField of B S by <:].

End Test3.

*)

(* end hide *)

(* Algebraic structure of bool *)

HB.instance Definition _ := Zmodule_isComNzRing.Build bool
  andbA andbC andTb andb_addl isT.

Fact mulVb (b : bool) : b != 0 -> b * b = 1.
Proof. by case: b. Qed.

Fact invb_out (x y : bool) : y * x = 1 -> x != 0.
Proof. by case: x; case: y. Qed.

HB.instance Definition _ := ComNzRing_hasMulInverse.Build bool
  mulVb invb_out (fun x => fun => erefl x).

Lemma bool_fieldP : Field.axiom bool. Proof. by []. Qed.

HB.instance Definition _ := ComUnitRing_isField.Build bool bool_fieldP.

(* Algebraic structure of nat *)

HB.instance Definition _ := Nmodule_isComNzSemiRing.Build nat
  mulnA mulnC mul1n mulnDl mul0n erefl.

HB.instance Definition _ (R : pzSemiRingType) :=
  isMultiplicative.Build nat R (natmul 1) (natrM R, mulr1n 1).

Lemma natr0E : 0 = 0%N. Proof. by []. Qed.
Lemma natr1E : 1 = 1%N. Proof. by []. Qed.
Lemma natn n : n%:R = n.
Proof. by elim: n => [//|n IHn]; rewrite -nat1r IHn. Qed.
Lemma natrDE n m : n + m = (n + m)%N. Proof. by []. Qed.
Lemma natrME n m : n * m = (n * m)%N. Proof. by []. Qed.
Lemma natrXE n m : n ^+ m = (n ^ m)%N. Proof. by []. Qed.
Definition natrE := (natr0E, natr1E, natn, natrDE, natrME, natrXE).

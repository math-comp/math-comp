(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path.
From mathcomp Require Import div fintype tuple finfun.

(******************************************************************************)
(* This file provides a generic definition for iterating an operator over a   *)
(* set of indices (bigop); this big operator is parameterized by the return   *)
(* type (R), the type of indices (I), the operator (op), the default value on *)
(* empty lists (idx), the range of indices (r), the filter applied on this    *)
(* range (P) and the expression we are iterating (F). The definition is not   *)
(* to be used directly, but via the wide range of notations provided and      *)
(* which support a natural use of big operators.                              *)
(*   To improve performance of the Coq typechecker on large expressions, the  *)
(* bigop constant is OPAQUE. It can however be unlocked to reveal the         *)
(* transparent constant reducebig, to let Coq expand summation on an explicit *)
(* sequence with an explicit test.                                            *)
(*   The lemmas can be classified according to the operator being iterated:   *)
(*  1. Results independent of the operator: extensionality with respect to    *)
(*     the range of indices, to the filtering predicate or to the expression  *)
(*     being iterated; reindexing, widening or narrowing of the range of      *)
(*     indices; we provide lemmas for the special cases where indices are     *)
(*     natural numbers or bounded natural numbers ("ordinals"). We supply     *)
(*     several "functional" induction principles that can be used with the    *)
(*     ssreflect 1.3 "elim" tactic to do induction over the index range for   *)
(*     up to 3 bigops simultaneously.                                         *)
(*  2. Results depending on the properties of the operator:                   *)
(*     We distinguish: monoid laws (op is associative, idx is an identity     *)
(*     element), abelian monoid laws (op is also commutative), and laws with  *)
(*     a distributive operation (semirings). Examples of such results are     *)
(*     splitting, permuting, and exchanging bigops.                           *)
(* A special section is dedicated to big operators on natural numbers.        *)
(******************************************************************************)
(* Notations:                                                                 *)
(* The general form for iterated operators is                                 *)
(*         <bigop>_<range> <general_term>                                     *)
(* - <bigop> is one of \big[op/idx], \sum, \prod, or \max (see below).        *)
(* - <general_term> can be any expression.                                    *)
(* - <range> binds an index variable in <general_term>; <range> is one of     *)
(*    (i <- s)     i ranges over the sequence s.                              *)
(*    (m <= i < n) i ranges over the nat interval m, m+1, ..., n-1.           *)
(*    (i < n)      i ranges over the (finite) type 'I_n (i.e., ordinal n).    *)
(*    (i : T)      i ranges over the finite type T.                           *)
(*    i or (i)     i ranges over its (inferred) finite type.                  *)
(*    (i in A)     i ranges over the elements that satisfy the collective     *)
(*                 predicate A (the domain of A must be a finite type).       *)
(*    (i <- s | <condition>) limits the range to the i for which <condition>  *)
(*                 holds. <condition> can be any expression that coerces to   *)
(*                 bool, and may mention the bound index i. All six kinds of  *)
(*                 ranges above can have a <condition> part.                  *)
(* - One can use the "\big[op/idx]" notations for any operator.               *)
(* - BIG_F and BIG_P are pattern abbreviations for the <general_term> and     *)
(*   <condition> part of a \big ... expression; for (i in A) and (i in A | C) *)
(*   ranges the term matched by BIG_P will include the i \in A condition.     *)
(* - The (locked) head constant of a \big notation is bigop.                  *)
(* - The "\sum", "\prod" and "\max" notations in the %N scope are used for    *)
(*   natural numbers with addition, multiplication and maximum (and their     *)
(*   corresponding neutral elements), respectively.                           *)
(* - The "\sum" and "\prod" reserved notations are overloaded in ssralg in    *)
(*   the %R scope; in mxalgebra, vector & falgebra in the %MS and %VS scopes; *)
(*   "\prod" is also overloaded in fingroup, in the %g and %G scopes.         *)
(* - We reserve "\bigcup" and "\bigcap" notations for iterated union and      *)
(*   intersection (of sets, groups, vector spaces, etc).                      *)
(******************************************************************************)
(* Tips for using lemmas in this file:                                        *)
(* To apply a lemma for a specific operator: if no special property is        *)
(* required for the operator, simply apply the lemma; if the lemma needs      *)
(* certain properties for the operator, make sure the appropriate Canonical   *)
(* instances are declared.                                                    *)
(******************************************************************************)
(* Interfaces for operator properties are packaged in the Monoid submodule:   *)
(*     Monoid.law idx == interface (keyed on the operator) for associative    *)
(*                       operators with identity element idx.                 *)
(* Monoid.com_law idx == extension (telescope) of Monoid.law for operators    *)
(*                       that are also commutative.                           *)
(* Monoid.mul_law abz == interface for operators with absorbing (zero)        *)
(*                       element abz.                                         *)
(* Monoid.add_law idx mop == extension of Monoid.com_law for operators over   *)
(*                       which operation mop distributes (mop will often also *)
(*                       have a Monoid.mul_law idx structure).                *)
(* [law of op], [com_law of op], [mul_law of op], [add_law mop of op] ==      *)
(*                       syntax for cloning Monoid structures.                *)
(*      Monoid.Theory == submodule containing basic generic algebra lemmas    *)
(*                       for operators satisfying the Monoid interfaces.      *)
(*       Monoid.simpm == generic monoid simplification rewrite multirule.     *)
(* Monoid structures are predeclared for many basic operators: (_ && _)%B,    *)
(* (_ || _)%B, (_ (+) _)%B (exclusive or) , (_ + _)%N, (_ * _)%N, maxn,       *)
(* gcdn, lcmn and (_ ++ _)%SEQ (list concatenation).                          *)
(******************************************************************************)
(* Additional documentation for this file:                                    *)
(* Y. Bertot, G. Gonthier, S. Ould Biha and I. Pasca.                         *)
(* Canonical Big Operators. In TPHOLs 2008, LNCS vol. 5170, Springer.         *)
(* Article available at:                                                      *)
(*     http://hal.inria.fr/docs/00/33/11/93/PDF/main.pdf                      *)
(******************************************************************************)
(* Examples of use in: poly.v, matrix.v                                       *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope big_scope.

Reserved Notation "\big [ op / idx ]_ i F"
  (at level 36, F at level 36, op, idx at level 10, i at level 0,
     right associativity,
           format "'[' \big [ op / idx ]_ i '/  '  F ']'").
Reserved Notation "\big [ op / idx ]_ ( i <- r | P ) F"
  (at level 36, F at level 36, op, idx at level 10, i, r at level 50,
           format "'[' \big [ op / idx ]_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\big [ op / idx ]_ ( i <- r ) F"
  (at level 36, F at level 36, op, idx at level 10, i, r at level 50,
           format "'[' \big [ op / idx ]_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\big [ op / idx ]_ ( m <= i < n | P ) F"
  (at level 36, F at level 36, op, idx at level 10, m, i, n at level 50,
           format "'[' \big [ op / idx ]_ ( m  <=  i  <  n  |  P )  F ']'").
Reserved Notation "\big [ op / idx ]_ ( m <= i < n ) F"
  (at level 36, F at level 36, op, idx at level 10, i, m, n at level 50,
           format "'[' \big [ op / idx ]_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\big [ op / idx ]_ ( i | P ) F"
  (at level 36, F at level 36, op, idx at level 10, i at level 50,
           format "'[' \big [ op / idx ]_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\big [ op / idx ]_ ( i : t | P ) F"
  (at level 36, F at level 36, op, idx at level 10, i at level 50,
           format "'[' \big [ op / idx ]_ ( i   :  t   |  P ) '/  '  F ']'").
Reserved Notation "\big [ op / idx ]_ ( i : t ) F"
  (at level 36, F at level 36, op, idx at level 10, i at level 50,
           format "'[' \big [ op / idx ]_ ( i   :  t ) '/  '  F ']'").
Reserved Notation "\big [ op / idx ]_ ( i < n | P ) F"
  (at level 36, F at level 36, op, idx at level 10, i, n at level 50,
           format "'[' \big [ op / idx ]_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\big [ op / idx ]_ ( i < n ) F"
  (at level 36, F at level 36, op, idx at level 10, i, n at level 50,
           format "'[' \big [ op / idx ]_ ( i  <  n )  F ']'").
Reserved Notation "\big [ op / idx ]_ ( i 'in' A | P ) F"
  (at level 36, F at level 36, op, idx at level 10, i, A at level 50,
           format "'[' \big [ op / idx ]_ ( i  'in'  A  |  P ) '/  '  F ']'").
Reserved Notation "\big [ op / idx ]_ ( i 'in' A ) F"
  (at level 36, F at level 36, op, idx at level 10, i, A at level 50,
           format "'[' \big [ op / idx ]_ ( i  'in'  A ) '/  '  F ']'").

Reserved Notation "\sum_ i F"
  (at level 41, F at level 41, i at level 0,
           right associativity,
           format "'[' \sum_ i '/  '  F ']'").
Reserved Notation "\sum_ ( i <- r | P ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \sum_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\sum_ ( i <- r ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \sum_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\sum_ ( m <= i < n | P ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \sum_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\sum_ ( m <= i < n ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \sum_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\sum_ ( i | P ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \sum_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\sum_ ( i : t | P ) F"
  (at level 41, F at level 41, i at level 50). (* only parsing *)
Reserved Notation "\sum_ ( i : t ) F"
  (at level 41, F at level 41, i at level 50). (* only parsing *)
Reserved Notation "\sum_ ( i < n | P ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \sum_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\sum_ ( i < n ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \sum_ ( i  <  n ) '/  '  F ']'").
Reserved Notation "\sum_ ( i 'in' A | P ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \sum_ ( i  'in'  A  |  P ) '/  '  F ']'").
Reserved Notation "\sum_ ( i 'in' A ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \sum_ ( i  'in'  A ) '/  '  F ']'").

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
  (at level 41, F at level 41, i at level 50). (* only parsing *)
Reserved Notation "\max_ ( i : t ) F"
  (at level 41, F at level 41, i at level 50). (* only parsing *)
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

Reserved Notation "\prod_ i F"
  (at level 36, F at level 36, i at level 0,
           format "'[' \prod_ i '/  '  F ']'").
Reserved Notation "\prod_ ( i <- r | P ) F"
  (at level 36, F at level 36, i, r at level 50,
           format "'[' \prod_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\prod_ ( i <- r ) F"
  (at level 36, F at level 36, i, r at level 50,
           format "'[' \prod_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\prod_ ( m <= i < n | P ) F"
  (at level 36, F at level 36, i, m, n at level 50,
           format "'[' \prod_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\prod_ ( m <= i < n ) F"
  (at level 36, F at level 36, i, m, n at level 50,
           format "'[' \prod_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\prod_ ( i | P ) F"
  (at level 36, F at level 36, i at level 50,
           format "'[' \prod_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\prod_ ( i : t | P ) F"
  (at level 36, F at level 36, i at level 50). (* only parsing *)
Reserved Notation "\prod_ ( i : t ) F"
  (at level 36, F at level 36, i at level 50). (* only parsing *)
Reserved Notation "\prod_ ( i < n | P ) F"
  (at level 36, F at level 36, i, n at level 50,
           format "'[' \prod_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\prod_ ( i < n ) F"
  (at level 36, F at level 36, i, n at level 50,
           format "'[' \prod_ ( i  <  n ) '/  '  F ']'").
Reserved Notation "\prod_ ( i 'in' A | P ) F"
  (at level 36, F at level 36, i, A at level 50,
           format "'[' \prod_ ( i  'in'  A  |  P )  F ']'").
Reserved Notation "\prod_ ( i 'in' A ) F"
  (at level 36, F at level 36, i, A at level 50,
           format "'[' \prod_ ( i  'in'  A ) '/  '  F ']'").

Reserved Notation "\bigcup_ i F"
  (at level 41, F at level 41, i at level 0,
           format "'[' \bigcup_ i '/  '  F ']'").
Reserved Notation "\bigcup_ ( i <- r | P ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \bigcup_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\bigcup_ ( i <- r ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \bigcup_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\bigcup_ ( m <= i < n | P ) F"
  (at level 41, F at level 41, m, i, n at level 50,
           format "'[' \bigcup_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\bigcup_ ( m <= i < n ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \bigcup_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\bigcup_ ( i | P ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \bigcup_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\bigcup_ ( i : t | P ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \bigcup_ ( i   :  t   |  P ) '/  '  F ']'").
Reserved Notation "\bigcup_ ( i : t ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \bigcup_ ( i   :  t ) '/  '  F ']'").
Reserved Notation "\bigcup_ ( i < n | P ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \bigcup_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\bigcup_ ( i < n ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \bigcup_ ( i  <  n ) '/  '  F ']'").
Reserved Notation "\bigcup_ ( i 'in' A | P ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \bigcup_ ( i  'in'  A  |  P ) '/  '  F ']'").
Reserved Notation "\bigcup_ ( i 'in' A ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \bigcup_ ( i  'in'  A ) '/  '  F ']'").

Reserved Notation "\bigcap_ i F"
  (at level 41, F at level 41, i at level 0,
           format "'[' \bigcap_ i '/  '  F ']'").
Reserved Notation "\bigcap_ ( i <- r | P ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \bigcap_ ( i  <-  r  |  P )  F ']'").
Reserved Notation "\bigcap_ ( i <- r ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \bigcap_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\bigcap_ ( m <= i < n | P ) F"
  (at level 41, F at level 41, m, i, n at level 50,
           format "'[' \bigcap_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\bigcap_ ( m <= i < n ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \bigcap_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\bigcap_ ( i | P ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \bigcap_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\bigcap_ ( i : t | P ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \bigcap_ ( i   :  t   |  P ) '/  '  F ']'").
Reserved Notation "\bigcap_ ( i : t ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \bigcap_ ( i   :  t ) '/  '  F ']'").
Reserved Notation "\bigcap_ ( i < n | P ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \bigcap_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\bigcap_ ( i < n ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \bigcap_ ( i  <  n ) '/  '  F ']'").
Reserved Notation "\bigcap_ ( i 'in' A | P ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \bigcap_ ( i  'in'  A  |  P ) '/  '  F ']'").
Reserved Notation "\bigcap_ ( i 'in' A ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \bigcap_ ( i  'in'  A ) '/  '  F ']'").

Module Monoid.

Section Definitions.
Variables (T : Type) (idm : T).

Structure law := Law {
  operator : T -> T -> T;
  _ : associative operator;
  _ : left_id idm operator;
  _ : right_id idm operator
}.
Local Coercion operator : law >-> Funclass.

Structure com_law := ComLaw {
   com_operator : law;
   _ : commutative com_operator
}.
Local Coercion com_operator : com_law >-> law.

Structure mul_law := MulLaw {
  mul_operator : T -> T -> T;
  _ : left_zero idm mul_operator;
  _ : right_zero idm mul_operator
}.
Local Coercion mul_operator : mul_law >-> Funclass.

Structure add_law (mul : T -> T -> T) := AddLaw {
  add_operator : com_law;
  _ : left_distributive mul add_operator;
  _ : right_distributive mul add_operator
}.
Local Coercion add_operator : add_law >-> com_law.

Let op_id (op1 op2 : T -> T -> T) := phant_id op1 op2.

Definition clone_law op :=
  fun (opL : law) & op_id opL op =>
  fun opmA op1m opm1 (opL' := @Law op opmA op1m opm1)
    & phant_id opL' opL => opL'.

Definition clone_com_law op :=
  fun (opL : law) (opC : com_law) & op_id opL op & op_id opC op =>
  fun opmC (opC' := @ComLaw opL opmC) & phant_id opC' opC => opC'.

Definition clone_mul_law op :=
  fun (opM : mul_law) & op_id opM op =>
  fun op0m opm0 (opM' := @MulLaw op op0m opm0) & phant_id opM' opM => opM'.

Definition clone_add_law mop aop :=
  fun (opC : com_law) (opA : add_law mop) & op_id opC aop & op_id opA aop =>
  fun mopDm mopmD (opA' := @AddLaw mop opC mopDm mopmD)
    & phant_id opA' opA => opA'.

End Definitions.

Module Import Exports.
Coercion operator : law >-> Funclass.
Coercion com_operator : com_law >-> law.
Coercion mul_operator : mul_law >-> Funclass.
Coercion add_operator : add_law >-> com_law.
Notation "[ 'law' 'of' f ]" := (@clone_law _ _ f _ id _ _ _ id)
  (at level 0, format"[ 'law'  'of'  f ]") : form_scope.
Notation "[ 'com_law' 'of' f ]" := (@clone_com_law _ _ f _ _ id id _ id)
  (at level 0, format "[ 'com_law'  'of'  f ]") : form_scope.
Notation "[ 'mul_law' 'of' f ]" := (@clone_mul_law _ _ f _ id _ _ id)
  (at level 0, format"[ 'mul_law'  'of'  f ]") : form_scope.
Notation "[ 'add_law' m 'of' a ]" := (@clone_add_law _ _ m a _ _ id id _ _ id)
  (at level 0, format "[ 'add_law'  m  'of'  a ]") : form_scope.
End Exports.

Section CommutativeAxioms.

Variable (T : Type) (zero one : T) (mul add : T -> T -> T) (inv : T -> T).
Hypothesis mulC : commutative mul.

Lemma mulC_id : left_id one mul -> right_id one mul.
Proof. by move=> mul1x x; rewrite mulC. Qed.

Lemma mulC_zero : left_zero zero mul -> right_zero zero mul.
Proof. by move=> mul0x x; rewrite mulC. Qed.

Lemma mulC_dist : left_distributive mul add -> right_distributive mul add.
Proof. by move=> mul_addl x y z; rewrite !(mulC x). Qed.

End CommutativeAxioms.

Module Theory.

Section Theory.
Variables (T : Type) (idm : T).

Section Plain.
Variable mul : law idm.
Lemma mul1m : left_id idm mul. Proof. by case mul. Qed.
Lemma mulm1 : right_id idm mul. Proof. by case mul. Qed.
Lemma mulmA : associative mul. Proof. by case mul. Qed.
Lemma iteropE n x : iterop n mul x idm = iter n (mul x) idm.
Proof. by case: n => // n; rewrite iterSr mulm1 iteropS. Qed.
End Plain.

Section Commutative.
Variable mul : com_law idm.
Lemma mulmC : commutative mul. Proof. by case mul. Qed.
Lemma mulmCA : left_commutative mul.
Proof. by move=> x y z; rewrite !mulmA (mulmC x). Qed.
Lemma mulmAC : right_commutative mul.
Proof. by move=> x y z; rewrite -!mulmA (mulmC y). Qed.
Lemma mulmACA : interchange mul mul.
Proof. by move=> x y z t; rewrite -!mulmA (mulmCA y). Qed.
End Commutative.

Section Mul.
Variable mul : mul_law idm.
Lemma mul0m : left_zero idm mul. Proof. by case mul. Qed.
Lemma mulm0 : right_zero idm mul. Proof. by case mul. Qed.
End Mul.

Section Add.
Variables (mul : T -> T -> T) (add : add_law idm mul).
Lemma addmA : associative add. Proof. exact: mulmA. Qed.
Lemma addmC : commutative add. Proof. exact: mulmC. Qed.
Lemma addmCA : left_commutative add. Proof. exact: mulmCA. Qed.
Lemma addmAC : right_commutative add. Proof. exact: mulmAC. Qed.
Lemma add0m : left_id idm add. Proof. exact: mul1m. Qed.
Lemma addm0 : right_id idm add. Proof. exact: mulm1. Qed.
Lemma mulmDl : left_distributive mul add. Proof. by case add. Qed.
Lemma mulmDr : right_distributive mul add. Proof. by case add. Qed.
End Add.

Definition simpm := (mulm1, mulm0, mul1m, mul0m, mulmA).

End Theory.

#[deprecated(since="mathcomp 1.12.0", note="Use mulmDl instead.")]
Notation mulm_addl := mulmDl (only parsing).
#[deprecated(since="mathcomp 1.12.0", note="Use mulmDr instead.")]
Notation mulm_addr := mulmDr (only parsing).

End Theory.
Include Theory.

End Monoid.
Export Monoid.Exports.

Section PervasiveMonoids.

Import Monoid.

Canonical andb_monoid := Law andbA andTb andbT.
Canonical andb_comoid := ComLaw andbC.

Canonical andb_muloid := MulLaw andFb andbF.
Canonical orb_monoid := Law orbA orFb orbF.
Canonical orb_comoid := ComLaw orbC.
Canonical orb_muloid := MulLaw orTb orbT.
Canonical addb_monoid := Law addbA addFb addbF.
Canonical addb_comoid := ComLaw addbC.
Canonical orb_addoid := AddLaw andb_orl andb_orr.
Canonical andb_addoid := AddLaw orb_andl orb_andr.
Canonical addb_addoid := AddLaw andb_addl andb_addr.

Canonical addn_monoid := Law addnA add0n addn0.
Canonical addn_comoid := ComLaw addnC.
Canonical muln_monoid := Law mulnA mul1n muln1.
Canonical muln_comoid := ComLaw mulnC.
Canonical muln_muloid := MulLaw mul0n muln0.
Canonical addn_addoid := AddLaw mulnDl mulnDr.

Canonical maxn_monoid := Law maxnA max0n maxn0.
Canonical maxn_comoid := ComLaw maxnC.
Canonical maxn_addoid := AddLaw maxnMl maxnMr.

Canonical gcdn_monoid := Law gcdnA gcd0n gcdn0.
Canonical gcdn_comoid := ComLaw gcdnC.
Canonical gcdnDoid := AddLaw muln_gcdl muln_gcdr.

Canonical lcmn_monoid := Law lcmnA lcm1n lcmn1.
Canonical lcmn_comoid := ComLaw lcmnC.
Canonical lcmn_addoid := AddLaw muln_lcml muln_lcmr.

Canonical cat_monoid T := Law (@catA T) (@cat0s T) (@cats0 T).

End PervasiveMonoids.

(* Unit test for the [...law of ...] Notations
Definition myp := addn. Definition mym := muln.
Canonical myp_mon := [law of myp].
Canonical myp_cmon := [com_law of myp].
Canonical mym_mul := [mul_law of mym].
Canonical myp_add := [add_law _ of myp].
Print myp_add.
Print Canonical Projections.
*)

Delimit Scope big_scope with BIG.
Open Scope big_scope.

(* The bigbody wrapper is a workaround for a quirk of the Coq pretty-printer, *)
(* which would fail to redisplay the \big notation when the <general_term> or *)
(* <condition> do not depend on the bound index. The BigBody constructor      *)
(* packages both in in a term in which i occurs; it also depends on the       *)
(* iterated <op>, as this can give more information on the expected type of   *)
(* the <general_term>, thus allowing for the insertion of coercions.          *)
Variant bigbody R I := BigBody of I & (R -> R -> R) & bool & R.

Definition applybig {R I} (body : bigbody R I) x :=
  let: BigBody _ op b v := body in if b then op v x else x.

Definition reducebig R I idx r (body : I -> bigbody R I) :=
  foldr (applybig \o body) idx r.

Module Type BigOpSig.
Parameter bigop : forall R I, R -> seq I -> (I -> bigbody R I) -> R.
Axiom bigopE : bigop = reducebig.
End BigOpSig.

Module BigOp : BigOpSig.
Definition bigop := reducebig.
Lemma bigopE : bigop = reducebig. Proof. by []. Qed.
End BigOp.

Notation bigop := BigOp.bigop (only parsing).
Canonical bigop_unlock := Unlockable BigOp.bigopE.

Definition index_iota m n := iota m (n - m).

Lemma mem_index_iota m n i : i \in index_iota m n = (m <= i < n).
Proof.
rewrite mem_iota; case le_m_i: (m <= i) => //=.
by rewrite -leq_subLR subSn // -subn_gt0 -subnDA subnKC // subn_gt0.
Qed.

(* Legacy mathcomp scripts have been relying on the fact that enum A and      *)
(* filter A (index_enum T) are convertible. This is likely to change in the   *)
(* next mathcomp release when enum, pick, subset and card are generalised to  *)
(* predicates with finite support in a choiceType - in fact the two will only *)
(* be equal up to permutation in this new theory.                             *)
(*  It is therefore advisable to stop relying on this, and use the new        *)
(* facilities provided in this library: lemmas big_enumP, big_enum, big_image *)
(* and such. Users wishing to test compliance should change the Defined in    *)
(* index_enum_key to Qed, and comment out the filter_index_enum compatibility *)
(* definition below (or Import Deprecation.Reject).                           *)
Fact index_enum_key : unit. Proof. split. Defined. (* Qed. *)
Definition index_enum (T : finType) :=
  locked_with index_enum_key (Finite.enum T).

Lemma deprecated_filter_index_enum T P : filter P (index_enum T) = enum P.
Proof. by rewrite [index_enum T]unlock. Qed.

Lemma mem_index_enum T i : i \in index_enum T.
Proof. by rewrite [index_enum T]unlock -enumT mem_enum. Qed.
Hint Resolve mem_index_enum : core.

Lemma index_enum_uniq T : uniq (index_enum T).
Proof. by rewrite [index_enum T]unlock -enumT enum_uniq. Qed.

Notation "\big [ op / idx ]_ ( i <- r | P ) F" :=
  (bigop idx r (fun i => BigBody i op P%B F)) : big_scope.
Notation "\big [ op / idx ]_ ( i <- r ) F" :=
  (bigop idx r (fun i => BigBody i op true F)) : big_scope.
Notation "\big [ op / idx ]_ ( m <= i < n | P ) F" :=
  (bigop idx (index_iota m n) (fun i : nat => BigBody i op P%B F))
     : big_scope.
Notation "\big [ op / idx ]_ ( m <= i < n ) F" :=
  (bigop idx (index_iota m n) (fun i : nat => BigBody i op true F))
     : big_scope.
Notation "\big [ op / idx ]_ ( i | P ) F" :=
  (bigop idx (index_enum _) (fun i => BigBody i op P%B F)) : big_scope.
Notation "\big [ op / idx ]_ i F" :=
  (bigop idx (index_enum _) (fun i => BigBody i op true F)) : big_scope.
Notation "\big [ op / idx ]_ ( i : t | P ) F" :=
  (bigop idx (index_enum _) (fun i : t => BigBody i op P%B F))
     (only parsing) : big_scope.
Notation "\big [ op / idx ]_ ( i : t ) F" :=
  (bigop idx (index_enum _) (fun i : t => BigBody i op true F))
     (only parsing) : big_scope.
Notation "\big [ op / idx ]_ ( i < n | P ) F" :=
  (\big[op/idx]_(i : ordinal n | P%B) F) : big_scope.
Notation "\big [ op / idx ]_ ( i < n ) F" :=
  (\big[op/idx]_(i : ordinal n) F) : big_scope.
Notation "\big [ op / idx ]_ ( i 'in' A | P ) F" :=
  (\big[op/idx]_(i | (i \in A) && P) F) : big_scope.
Notation "\big [ op / idx ]_ ( i 'in' A ) F" :=
  (\big[op/idx]_(i | i \in A) F) : big_scope.

Notation BIG_F := (F in \big[_/_]_(i <- _ | _) F i)%pattern.
Notation BIG_P := (P in \big[_/_]_(i <- _ | P i) _)%pattern.

Local Notation "+%N" := addn (at level 0, only parsing).
Notation "\sum_ ( i <- r | P ) F" :=
  (\big[+%N/0%N]_(i <- r | P%B) F%N) : nat_scope.
Notation "\sum_ ( i <- r ) F" :=
  (\big[+%N/0%N]_(i <- r) F%N) : nat_scope.
Notation "\sum_ ( m <= i < n | P ) F" :=
  (\big[+%N/0%N]_(m <= i < n | P%B) F%N) : nat_scope.
Notation "\sum_ ( m <= i < n ) F" :=
  (\big[+%N/0%N]_(m <= i < n) F%N) : nat_scope.
Notation "\sum_ ( i | P ) F" :=
  (\big[+%N/0%N]_(i | P%B) F%N) : nat_scope.
Notation "\sum_ i F" :=
  (\big[+%N/0%N]_i F%N) : nat_scope.
Notation "\sum_ ( i : t | P ) F" :=
  (\big[+%N/0%N]_(i : t | P%B) F%N) (only parsing) : nat_scope.
Notation "\sum_ ( i : t ) F" :=
  (\big[+%N/0%N]_(i : t) F%N) (only parsing) : nat_scope.
Notation "\sum_ ( i < n | P ) F" :=
  (\big[+%N/0%N]_(i < n | P%B) F%N) : nat_scope.
Notation "\sum_ ( i < n ) F" :=
  (\big[+%N/0%N]_(i < n) F%N) : nat_scope.
Notation "\sum_ ( i 'in' A | P ) F" :=
  (\big[+%N/0%N]_(i in A | P%B) F%N) : nat_scope.
Notation "\sum_ ( i 'in' A ) F" :=
  (\big[+%N/0%N]_(i in A) F%N) : nat_scope.

Local Notation "*%N" := muln (at level 0, only parsing).
Notation "\prod_ ( i <- r | P ) F" :=
  (\big[*%N/1%N]_(i <- r | P%B) F%N) : nat_scope.
Notation "\prod_ ( i <- r ) F" :=
  (\big[*%N/1%N]_(i <- r) F%N) : nat_scope.
Notation "\prod_ ( m <= i < n | P ) F" :=
  (\big[*%N/1%N]_(m <= i < n | P%B) F%N) : nat_scope.
Notation "\prod_ ( m <= i < n ) F" :=
  (\big[*%N/1%N]_(m <= i < n) F%N) : nat_scope.
Notation "\prod_ ( i | P ) F" :=
  (\big[*%N/1%N]_(i | P%B) F%N) : nat_scope.
Notation "\prod_ i F" :=
  (\big[*%N/1%N]_i F%N) : nat_scope.
Notation "\prod_ ( i : t | P ) F" :=
  (\big[*%N/1%N]_(i : t | P%B) F%N) (only parsing) : nat_scope.
Notation "\prod_ ( i : t ) F" :=
  (\big[*%N/1%N]_(i : t) F%N) (only parsing) : nat_scope.
Notation "\prod_ ( i < n | P ) F" :=
  (\big[*%N/1%N]_(i < n | P%B) F%N) : nat_scope.
Notation "\prod_ ( i < n ) F" :=
  (\big[*%N/1%N]_(i < n) F%N) : nat_scope.
Notation "\prod_ ( i 'in' A | P ) F" :=
  (\big[*%N/1%N]_(i in A | P%B) F%N) : nat_scope.
Notation "\prod_ ( i 'in' A ) F" :=
  (\big[*%N/1%N]_(i in A) F%N) : nat_scope.

Notation "\max_ ( i <- r | P ) F" :=
  (\big[maxn/0%N]_(i <- r | P%B) F%N) : nat_scope.
Notation "\max_ ( i <- r ) F" :=
  (\big[maxn/0%N]_(i <- r) F%N) : nat_scope.
Notation "\max_ ( i | P ) F" :=
  (\big[maxn/0%N]_(i | P%B) F%N) : nat_scope.
Notation "\max_ i F" :=
  (\big[maxn/0%N]_i F%N) : nat_scope.
Notation "\max_ ( i : I | P ) F" :=
  (\big[maxn/0%N]_(i : I | P%B) F%N) (only parsing) : nat_scope.
Notation "\max_ ( i : I ) F" :=
  (\big[maxn/0%N]_(i : I) F%N) (only parsing) : nat_scope.
Notation "\max_ ( m <= i < n | P ) F" :=
 (\big[maxn/0%N]_(m <= i < n | P%B) F%N) : nat_scope.
Notation "\max_ ( m <= i < n ) F" :=
 (\big[maxn/0%N]_(m <= i < n) F%N) : nat_scope.
Notation "\max_ ( i < n | P ) F" :=
 (\big[maxn/0%N]_(i < n | P%B) F%N) : nat_scope.
Notation "\max_ ( i < n ) F" :=
 (\big[maxn/0%N]_(i < n) F%N) : nat_scope.
Notation "\max_ ( i 'in' A | P ) F" :=
 (\big[maxn/0%N]_(i in A | P%B) F%N) : nat_scope.
Notation "\max_ ( i 'in' A ) F" :=
 (\big[maxn/0%N]_(i in A) F%N) : nat_scope.

(* Induction loading *)
Lemma big_load R (K K' : R -> Type) idx op I r (P : pred I) F :
  K (\big[op/idx]_(i <- r | P i) F i) * K' (\big[op/idx]_(i <- r | P i) F i)
  -> K' (\big[op/idx]_(i <- r | P i) F i).
Proof. by case. Qed.

Arguments big_load [R] K [K'] idx op [I].

Section Elim3.

Variables (R1 R2 R3 : Type) (K : R1 -> R2 -> R3 -> Type).
Variables (id1 : R1) (op1 : R1 -> R1 -> R1).
Variables (id2 : R2) (op2 : R2 -> R2 -> R2).
Variables (id3 : R3) (op3 : R3 -> R3 -> R3).

Hypothesis Kid : K id1 id2 id3.

Lemma big_rec3 I r (P : pred I) F1 F2 F3
    (K_F : forall i y1 y2 y3, P i -> K y1 y2 y3 ->
       K (op1 (F1 i) y1) (op2 (F2 i) y2) (op3 (F3 i) y3)) :
  K (\big[op1/id1]_(i <- r | P i) F1 i)
    (\big[op2/id2]_(i <- r | P i) F2 i)
    (\big[op3/id3]_(i <- r | P i) F3 i).
Proof. by rewrite unlock; elim: r => //= i r; case: ifP => //; apply: K_F. Qed.

Hypothesis Kop : forall x1 x2 x3 y1 y2 y3,
  K x1 x2 x3 -> K y1 y2 y3-> K (op1 x1 y1) (op2 x2 y2) (op3 x3 y3).
Lemma big_ind3 I r (P : pred I) F1 F2 F3
   (K_F : forall i, P i -> K (F1 i) (F2 i) (F3 i)) :
  K (\big[op1/id1]_(i <- r | P i) F1 i)
    (\big[op2/id2]_(i <- r | P i) F2 i)
    (\big[op3/id3]_(i <- r | P i) F3 i).
Proof. by apply: big_rec3 => i x1 x2 x3 /K_F; apply: Kop. Qed.

End Elim3.

Arguments big_rec3 [R1 R2 R3] K [id1 op1 id2 op2 id3 op3] _ [I r P F1 F2 F3].
Arguments big_ind3 [R1 R2 R3] K [id1 op1 id2 op2 id3 op3] _ _ [I r P F1 F2 F3].

Section Elim2.

Variables (R1 R2 : Type) (K : R1 -> R2 -> Type) (f : R2 -> R1).
Variables (id1 : R1) (op1 : R1 -> R1 -> R1).
Variables (id2 : R2) (op2 : R2 -> R2 -> R2).

Hypothesis Kid : K id1 id2.

Lemma big_rec2 I r (P : pred I) F1 F2
    (K_F : forall i y1 y2, P i -> K y1 y2 ->
       K (op1 (F1 i) y1) (op2 (F2 i) y2)) :
  K (\big[op1/id1]_(i <- r | P i) F1 i) (\big[op2/id2]_(i <- r | P i) F2 i).
Proof. by rewrite unlock; elim: r => //= i r; case: ifP => //; apply: K_F. Qed.

Hypothesis Kop : forall x1 x2 y1 y2,
  K x1 x2 -> K y1 y2 -> K (op1 x1 y1) (op2 x2 y2).
Lemma big_ind2 I r (P : pred I) F1 F2 (K_F : forall i, P i -> K (F1 i) (F2 i)) :
  K (\big[op1/id1]_(i <- r | P i) F1 i) (\big[op2/id2]_(i <- r | P i) F2 i).
Proof. by apply: big_rec2 => i x1 x2 /K_F; apply: Kop. Qed.

Hypotheses (f_op : {morph f : x y / op2 x y >-> op1 x y}) (f_id : f id2 = id1).
Lemma big_morph I r (P : pred I) F :
  f (\big[op2/id2]_(i <- r | P i) F i) = \big[op1/id1]_(i <- r | P i) f (F i).
Proof. by rewrite unlock; elim: r => //= i r <-; rewrite -f_op -fun_if. Qed.

End Elim2.

Arguments big_rec2 [R1 R2] K [id1 op1 id2 op2] _ [I r P F1 F2].
Arguments big_ind2 [R1 R2] K [id1 op1 id2 op2] _ _ [I r P F1 F2].
Arguments big_morph [R1 R2] f [id1 op1 id2 op2] _ _ [I].

Section Elim1.

Variables (R : Type) (K : R -> Type) (f : R -> R).
Variables (idx : R) (op op' : R -> R -> R).

Hypothesis Kid : K idx.

Lemma big_rec I r (P : pred I) F
    (Kop : forall i x, P i -> K x -> K (op (F i) x)) :
  K (\big[op/idx]_(i <- r | P i) F i).
Proof. by rewrite unlock; elim: r => //= i r; case: ifP => //; apply: Kop. Qed.

Hypothesis Kop : forall x y, K x -> K y -> K (op x y).
Lemma big_ind I r (P : pred I) F (K_F : forall i, P i -> K (F i)) :
  K (\big[op/idx]_(i <- r | P i) F i).
Proof. by apply: big_rec => // i x /K_F /Kop; apply. Qed.

Hypothesis Kop' : forall x y, K x -> K y -> op x y = op' x y.
Lemma eq_big_op I r (P : pred I) F (K_F : forall i, P i -> K (F i)) :
  \big[op/idx]_(i <- r | P i) F i = \big[op'/idx]_(i <- r | P i) F i.
Proof.
by elim/(big_load K): _; elim/big_rec2: _ => // i _ y Pi [Ky <-]; auto.
Qed.

Hypotheses (fM : {morph f : x y / op x y}) (f_id : f idx = idx).
Lemma big_endo I r (P : pred I) F :
  f (\big[op/idx]_(i <- r | P i) F i) = \big[op/idx]_(i <- r | P i) f (F i).
Proof. exact: big_morph. Qed.

End Elim1.

Arguments big_rec [R] K [idx op] _ [I r P F].
Arguments big_ind [R] K [idx op] _ _ [I r P F].
Arguments eq_big_op [R] K [idx op] op' _ _ _ [I].
Arguments big_endo [R] f [idx op] _ _ [I].

Section Extensionality.

Variables (R : Type) (idx : R) (op : R -> R -> R).

Section SeqExtension.

Variable I : Type.

Lemma foldrE r : foldr op idx r = \big[op/idx]_(x <- r) x.
Proof. by rewrite unlock. Qed.

Lemma big_filter r (P : pred I) F :
  \big[op/idx]_(i <- filter P r) F i = \big[op/idx]_(i <- r | P i) F i.
Proof. by rewrite unlock; elim: r => //= i r <-; case (P i). Qed.

Lemma big_filter_cond r (P1 P2 : pred I) F :
  \big[op/idx]_(i <- filter P1 r | P2 i) F i
     = \big[op/idx]_(i <- r | P1 i && P2 i) F i.
Proof.
rewrite -big_filter -(big_filter r); congr bigop.
by rewrite -filter_predI; apply: eq_filter => i; apply: andbC.
Qed.

Lemma eq_bigl r (P1 P2 : pred I) F :
    P1 =1 P2 ->
  \big[op/idx]_(i <- r | P1 i) F i = \big[op/idx]_(i <- r | P2 i) F i.
Proof. by move=> eqP12; rewrite -!(big_filter r) (eq_filter eqP12). Qed.

(* A lemma to permute aggregate conditions. *)
Lemma big_andbC r (P Q : pred I) F :
  \big[op/idx]_(i <- r | P i && Q i) F i
    = \big[op/idx]_(i <- r | Q i && P i) F i.
Proof. by apply: eq_bigl => i; apply: andbC. Qed.

Lemma eq_bigr r (P : pred I) F1 F2 : (forall i, P i -> F1 i = F2 i) ->
  \big[op/idx]_(i <- r | P i) F1 i = \big[op/idx]_(i <- r | P i) F2 i.
Proof. by move=> eqF12; elim/big_rec2: _ => // i x _ /eqF12-> ->. Qed.

Lemma eq_big r (P1 P2 : pred I) F1 F2 :
    P1 =1 P2 -> (forall i, P1 i -> F1 i = F2 i) ->
  \big[op/idx]_(i <- r | P1 i) F1 i = \big[op/idx]_(i <- r | P2 i) F2 i.
Proof. by move/eq_bigl <-; move/eq_bigr->. Qed.

Lemma congr_big r1 r2 (P1 P2 : pred I) F1 F2 :
    r1 = r2 -> P1 =1 P2 -> (forall i, P1 i -> F1 i = F2 i) ->
  \big[op/idx]_(i <- r1 | P1 i) F1 i = \big[op/idx]_(i <- r2 | P2 i) F2 i.
Proof. by move=> <-{r2}; apply: eq_big. Qed.

Lemma big_nil (P : pred I) F : \big[op/idx]_(i <- [::] | P i) F i = idx.
Proof. by rewrite unlock. Qed.

Lemma big_cons i r (P : pred I) F :
    let x := \big[op/idx]_(j <- r | P j) F j in
  \big[op/idx]_(j <- i :: r | P j) F j = if P i then op (F i) x else x.
Proof. by rewrite unlock. Qed.

Lemma big_map J (h : J -> I) r (P : pred I) F :
  \big[op/idx]_(i <- map h r | P i) F i
     = \big[op/idx]_(j <- r | P (h j)) F (h j).
Proof. by rewrite unlock; elim: r => //= j r ->. Qed.

Lemma big_nth x0 r (P : pred I) F :
  \big[op/idx]_(i <- r | P i) F i
     = \big[op/idx]_(0 <= i < size r | P (nth x0 r i)) (F (nth x0 r i)).
Proof. by rewrite -[r in LHS](mkseq_nth x0) big_map /index_iota subn0. Qed.

Lemma big_hasC r (P : pred I) F :
  ~~ has P r -> \big[op/idx]_(i <- r | P i) F i = idx.
Proof.
by rewrite -big_filter has_count -size_filter -eqn0Ngt unlock => /nilP->.
Qed.

Lemma big_pred0_eq (r : seq I) F : \big[op/idx]_(i <- r | false) F i = idx.
Proof. by rewrite big_hasC // has_pred0. Qed.

Lemma big_pred0 r (P : pred I) F :
  P =1 xpred0 -> \big[op/idx]_(i <- r | P i) F i = idx.
Proof. by move/eq_bigl->; apply: big_pred0_eq. Qed.

Lemma big_cat_nested r1 r2 (P : pred I) F :
    let x := \big[op/idx]_(i <- r2 | P i) F i in
  \big[op/idx]_(i <- r1 ++ r2 | P i) F i = \big[op/x]_(i <- r1 | P i) F i.
Proof. by rewrite unlock /reducebig foldr_cat. Qed.

Lemma big_catl r1 r2 (P : pred I) F :
    ~~ has P r2 ->
  \big[op/idx]_(i <- r1 ++ r2 | P i) F i = \big[op/idx]_(i <- r1 | P i) F i.
Proof. by rewrite big_cat_nested => /big_hasC->. Qed.

Lemma big_catr r1 r2 (P : pred I) F :
     ~~ has P r1 ->
  \big[op/idx]_(i <- r1 ++ r2 | P i) F i = \big[op/idx]_(i <- r2 | P i) F i.
Proof.
rewrite -big_filter -(big_filter r2) filter_cat.
by rewrite has_count -size_filter; case: filter.
Qed.

End SeqExtension.

Lemma big_map_id J (h : J -> R) r (P : pred R) :
  \big[op/idx]_(i <- map h r | P i) i
     = \big[op/idx]_(j <- r | P (h j)) h j.
Proof. exact: big_map. Qed.

(* The following lemmas can be used to localise extensionality to a specific  *)
(* index sequence. This is done by ssreflect rewriting, before applying       *)
(* congruence or induction lemmas.                                            *)
Lemma big_seq_cond (I : eqType) r (P : pred I) F :
  \big[op/idx]_(i <- r | P i) F i
    = \big[op/idx]_(i <- r | (i \in r) && P i) F i.
Proof.
by rewrite -!(big_filter r); congr bigop; apply: eq_in_filter => i ->.
Qed.

Lemma big_seq (I : eqType) (r : seq I) F :
  \big[op/idx]_(i <- r) F i = \big[op/idx]_(i <- r | i \in r) F i.
Proof. by rewrite big_seq_cond big_andbC. Qed.

Lemma eq_big_seq (I : eqType) (r : seq I) F1 F2 :
  {in r, F1 =1 F2} -> \big[op/idx]_(i <- r) F1 i = \big[op/idx]_(i <- r) F2 i.
Proof. by move=> eqF; rewrite !big_seq (eq_bigr _ eqF). Qed.

(* Similar lemmas for exposing integer indexing in the predicate. *)
Lemma big_nat_cond m n (P : pred nat) F :
  \big[op/idx]_(m <= i < n | P i) F i
    = \big[op/idx]_(m <= i < n | (m <= i < n) && P i) F i.
Proof.
by rewrite big_seq_cond; apply: eq_bigl => i; rewrite mem_index_iota.
Qed.

Lemma big_nat m n F :
  \big[op/idx]_(m <= i < n) F i = \big[op/idx]_(m <= i < n | m <= i < n) F i.
Proof. by rewrite big_nat_cond big_andbC. Qed.

Lemma congr_big_nat m1 n1 m2 n2 P1 P2 F1 F2 :
    m1 = m2 -> n1 = n2 ->
    (forall i, m1 <= i < n2 -> P1 i = P2 i) ->
    (forall i, P1 i && (m1 <= i < n2) -> F1 i = F2 i) ->
  \big[op/idx]_(m1 <= i < n1 | P1 i) F1 i
    = \big[op/idx]_(m2 <= i < n2 | P2 i) F2 i.
Proof.
move=> <- <- eqP12 eqF12; rewrite big_seq_cond (big_seq_cond _ P2).
apply: eq_big => i; rewrite ?inE /= !mem_index_iota.
  by apply: andb_id2l; apply: eqP12.
by rewrite andbC; apply: eqF12.
Qed.

Lemma eq_big_nat m n F1 F2 :
    (forall i, m <= i < n -> F1 i = F2 i) ->
  \big[op/idx]_(m <= i < n) F1 i = \big[op/idx]_(m <= i < n) F2 i.
Proof. by move=> eqF; apply: congr_big_nat. Qed.

Lemma big_geq m n (P : pred nat) F :
  m >= n -> \big[op/idx]_(m <= i < n | P i) F i = idx.
Proof. by move=> ge_m_n; rewrite /index_iota (eqnP ge_m_n) big_nil. Qed.

Lemma big_ltn_cond m n (P : pred nat) F :
    m < n -> let x := \big[op/idx]_(m.+1 <= i < n | P i) F i in
  \big[op/idx]_(m <= i < n | P i) F i = if P m then op (F m) x else x.
Proof. by case: n => [//|n] le_m_n; rewrite /index_iota subSn // big_cons. Qed.

Lemma big_ltn m n F :
     m < n ->
  \big[op/idx]_(m <= i < n) F i = op (F m) (\big[op/idx]_(m.+1 <= i < n) F i).
Proof. by move=> lt_mn; apply: big_ltn_cond. Qed.

Lemma big_addn m n a (P : pred nat) F :
  \big[op/idx]_(m + a <= i < n | P i) F i =
     \big[op/idx]_(m <= i < n - a | P (i + a)) F (i + a).
Proof.
rewrite /index_iota -subnDA addnC iotaDl big_map.
by apply: eq_big => ? *; rewrite addnC.
Qed.

Lemma big_add1 m n (P : pred nat) F :
  \big[op/idx]_(m.+1 <= i < n | P i) F i =
     \big[op/idx]_(m <= i < n.-1 | P (i.+1)) F (i.+1).
Proof.
by rewrite -addn1 big_addn subn1; apply: eq_big => ? *; rewrite addn1.
Qed.

Lemma big_nat_recl n m F : m <= n ->
  \big[op/idx]_(m <= i < n.+1) F i =
     op (F m) (\big[op/idx]_(m <= i < n) F i.+1).
Proof. by move=> lemn; rewrite big_ltn // big_add1. Qed.

Lemma big_mkord n (P : pred nat) F :
  \big[op/idx]_(0 <= i < n | P i) F i = \big[op/idx]_(i < n | P i) F i.
Proof.
rewrite /index_iota subn0 -(big_map (@nat_of_ord n)).
by congr bigop; rewrite /index_enum 2!unlock val_ord_enum.
Qed.

Lemma big_nat_widen m n1 n2 (P : pred nat) F :
     n1 <= n2 ->
  \big[op/idx]_(m <= i < n1 | P i) F i
      = \big[op/idx]_(m <= i < n2 | P i && (i < n1)) F i.
Proof.
move=> len12; symmetry; rewrite -big_filter filter_predI big_filter.
have [ltn_trans eq_by_mem] := (ltn_trans, irr_sorted_eq ltn_trans ltnn).
congr bigop; apply: eq_by_mem; rewrite ?sorted_filter ?iota_ltn_sorted // => i.
rewrite mem_filter !mem_index_iota andbCA andbA andb_idr => // /andP[_].
by move/leq_trans->.
Qed.

Lemma big_ord_widen_cond n1 n2 (P : pred nat) (F : nat -> R) :
     n1 <= n2 ->
  \big[op/idx]_(i < n1 | P i) F i
      = \big[op/idx]_(i < n2 | P i && (i < n1)) F i.
Proof. by move/big_nat_widen=> len12; rewrite -big_mkord len12 big_mkord. Qed.

Lemma big_ord_widen n1 n2 (F : nat -> R) :
    n1 <= n2 ->
  \big[op/idx]_(i < n1) F i = \big[op/idx]_(i < n2 | i < n1) F i.
Proof. by move=> le_n12; apply: (big_ord_widen_cond (predT)). Qed.

Lemma big_ord_widen_leq n1 n2 (P : pred 'I_(n1.+1)) F :
    n1 < n2 ->
  \big[op/idx]_(i < n1.+1 | P i) F i
      = \big[op/idx]_(i < n2 | P (inord i) && (i <= n1)) F (inord i).
Proof.
move=> len12; pose g G i := G (inord i : 'I_(n1.+1)).
rewrite -(big_ord_widen_cond (g _ P) (g _ F) len12) {}/g.
by apply: eq_big => i *; rewrite inord_val.
Qed.

Lemma big_ord0 P F : \big[op/idx]_(i < 0 | P i) F i = idx.
Proof. by rewrite big_pred0 => [|[]]. Qed.

Lemma big_mask_tuple I n m (t : n.-tuple I) (P : pred I) F :
  \big[op/idx]_(i <- mask m t | P i) F i
    = \big[op/idx]_(i < n | nth false m i && P (tnth t i)) F (tnth t i).
Proof.
rewrite [t in LHS]tuple_map_ord/= -map_mask big_map.
by rewrite mask_enum_ord big_filter_cond/= enumT.
Qed.

Lemma big_mask I r m (P : pred I) (F : I -> R) (r_ := tnth (in_tuple r)) :
  \big[op/idx]_(i <- mask m r | P i) F i
    = \big[op/idx]_(i < size r | nth false m i && P (r_ i)) F (r_ i).
Proof. exact: (big_mask_tuple _ (in_tuple r)). Qed.

Lemma big_tnth I r (P : pred I) F (r_ := tnth (in_tuple r)) :
  \big[op/idx]_(i <- r | P i) F i
    = \big[op/idx]_(i < size r | P (r_ i)) (F (r_ i)).
Proof.
rewrite /= -[r in LHS](mask_true (leqnn (size r))) big_mask//.
by apply: eq_bigl => i /=; rewrite nth_nseq ltn_ord.
Qed.

Lemma big_index_uniq (I : eqType) (r : seq I) (E : 'I_(size r) -> R) :
    uniq r ->
  \big[op/idx]_i E i = \big[op/idx]_(x <- r) oapp E idx (insub (index x r)).
Proof.
move=> Ur; apply/esym; rewrite big_tnth.
by under [LHS]eq_bigr do rewrite index_uniq// valK.
Qed.

Lemma big_tuple I n (t : n.-tuple I) (P : pred I) F :
  \big[op/idx]_(i <- t | P i) F i
     = \big[op/idx]_(i < n | P (tnth t i)) F (tnth t i).
Proof. by rewrite big_tnth tvalK; case: _ / (esym _). Qed.

Lemma big_ord_narrow_cond n1 n2 (P : pred 'I_n2) F (le_n12 : n1 <= n2) :
    let w := widen_ord le_n12 in
  \big[op/idx]_(i < n2 | P i && (i < n1)) F i
    = \big[op/idx]_(i < n1 | P (w i)) F (w i).
Proof.
case: n1 => [|n1] /= in le_n12 *.
  by rewrite big_ord0 big_pred0 // => i; rewrite andbF.
rewrite (big_ord_widen_leq _ _ le_n12); apply: eq_big => i.
  by apply: andb_id2r => le_i_n1; congr P; apply: val_inj; rewrite /= inordK.
by case/andP=> _ le_i_n1; congr F; apply: val_inj; rewrite /= inordK.
Qed.

Lemma big_ord_narrow_cond_leq n1 n2 (P : pred _) F (le_n12 : n1 <= n2) :
    let w := @widen_ord n1.+1 n2.+1 le_n12 in
  \big[op/idx]_(i < n2.+1 | P i && (i <= n1)) F i
  = \big[op/idx]_(i < n1.+1 | P (w i)) F (w i).
Proof. exact: (@big_ord_narrow_cond n1.+1 n2.+1). Qed.

Lemma big_ord_narrow n1 n2 F (le_n12 : n1 <= n2) :
    let w := widen_ord le_n12 in
  \big[op/idx]_(i < n2 | i < n1) F i = \big[op/idx]_(i < n1) F (w i).
Proof. exact: (big_ord_narrow_cond (predT)). Qed.

Lemma big_ord_narrow_leq n1 n2 F (le_n12 : n1 <= n2) :
    let w := @widen_ord n1.+1 n2.+1 le_n12 in
  \big[op/idx]_(i < n2.+1 | i <= n1) F i = \big[op/idx]_(i < n1.+1) F (w i).
Proof. exact: (big_ord_narrow_cond_leq (predT)). Qed.

Lemma big_ord_recl n F :
  \big[op/idx]_(i < n.+1) F i =
     op (F ord0) (\big[op/idx]_(i < n) F (@lift n.+1 ord0 i)).
Proof.
pose G i := F (inord i); have eqFG i: F i = G i by rewrite /G inord_val.
under eq_bigr do rewrite eqFG; under [in RHS]eq_bigr do rewrite eqFG.
by rewrite -(big_mkord _ (fun _ => _) G) eqFG big_ltn // big_add1 /= big_mkord.
Qed.

Lemma big_nseq_cond I n a (P : pred I) F :
  \big[op/idx]_(i <- nseq n a | P i) F i
    = if P a then iter n (op (F a)) idx else idx.
Proof. by rewrite unlock; elim: n => /= [|n ->]; case: (P a). Qed.

Lemma big_nseq I n a (F : I -> R):
  \big[op/idx]_(i <- nseq n a) F i = iter n (op (F a)) idx.
Proof. exact: big_nseq_cond. Qed.

End Extensionality.

Variant big_enum_spec (I : finType) (P : pred I) : seq I -> Type :=
  BigEnumSpec e of
    forall R idx op (F : I -> R),
      \big[op/idx]_(i <- e) F i = \big[op/idx]_(i | P i) F i
  & uniq e /\ (forall i, i \in e = P i)
  & (let cP := [pred i | P i] in perm_eq e (enum cP) /\ size e = #|cP|)
  : big_enum_spec P e.

(*   This lemma can be used to introduce an enumeration into a non-abelian    *)
(* bigop, in one of three ways:                                               *)
(*   have [e big_e [Ue mem_e] [e_enum size_e]] := big_enumP P.                *)
(* gives a permutation e of enum P alongside a equation big_e for converting  *)
(* between bigops iterating on (i <- e) and ones on (i | P i). Usually not    *)
(* all properties of e are needed, but see below the big_distr_big_dep proof  *)
(* where most are.                                                            *)
(*   rewrite -big_filter; have [e ...] := big_enumP.                          *)
(* uses big_filter to do this conversion first, and then abstracts the        *)
(* resulting filter P (index_enum T) enumeration as an e with the same        *)
(* properties (see big_enum_cond below for an example of this usage).         *)
(*   Finally                                                                  *)
(*   rewrite -big_filter; case def_e: _ / big_enumP => [e ...]                *)
(* does the same while remembering the definition of e.                       *)

Lemma big_enumP I P : big_enum_spec P (filter P (index_enum I)).
Proof.
set e := filter P _; have Ue: uniq e by apply/filter_uniq/index_enum_uniq.
have mem_e i: i \in e = P i by rewrite mem_filter mem_index_enum andbT.
split=> // [R idx op F | cP]; first by rewrite big_filter.
suffices De: perm_eq e (enum cP) by rewrite (perm_size De) cardE.
by apply/uniq_perm=> // [|i]; rewrite ?enum_uniq ?mem_enum ?mem_e.
Qed.

Section BigConst.

Variables (R : Type) (idx : R) (op : R -> R -> R).

Lemma big_const_seq I r (P : pred I) x :
  \big[op/idx]_(i <- r | P i) x = iter (count P r) (op x) idx.
Proof. by rewrite unlock; elim: r => //= i r ->; case: (P i). Qed.

Lemma big_const (I : finType) (A : {pred I}) x :
  \big[op/idx]_(i in A) x = iter #|A| (op x) idx.
Proof.
by have [e <- _ [_ <-]] := big_enumP A; rewrite big_const_seq count_predT.
Qed.

Lemma big_const_nat m n x :
  \big[op/idx]_(m <= i < n) x = iter (n - m) (op x) idx.
Proof. by rewrite big_const_seq count_predT size_iota. Qed.

Lemma big_const_ord n x :
  \big[op/idx]_(i < n) x = iter n (op x) idx.
Proof. by rewrite big_const card_ord. Qed.

End BigConst.

Section MonoidProperties.

Import Monoid.Theory.

Variable R : Type.

Variable idx : R.
Local Notation "1" := idx.

Section Plain.

Variable op : Monoid.law 1.

Local Notation "*%M" := op (at level 0).
Local Notation "x * y" := (op x y).

Lemma foldlE x r : foldl *%M x r = \big[*%M/1]_(y <- x :: r) y.
Proof.
by rewrite -foldrE; elim: r => [|y r IHr]/= in x *; rewrite ?mulm1 ?mulmA ?IHr.
Qed.

Lemma foldl_idx r : foldl *%M 1 r = \big[*%M/1]_(x <- r) x.
Proof. by rewrite foldlE big_cons mul1m. Qed.

Lemma eq_big_idx_seq idx' I r (P : pred I) F :
     right_id idx' *%M -> has P r ->
   \big[*%M/idx']_(i <- r | P i) F i =\big[*%M/1]_(i <- r | P i) F i.
Proof.
move=> op_idx'; rewrite -!(big_filter _ _ r) has_count -size_filter.
case/lastP: (filter P r) => {r}// r i _.
by rewrite -cats1 !(big_cat_nested, big_cons, big_nil) op_idx' mulm1.
Qed.

Lemma eq_big_idx idx' (I : finType) i0 (P : pred I) F :
     P i0 -> right_id idx' *%M ->
  \big[*%M/idx']_(i | P i) F i =\big[*%M/1]_(i | P i) F i.
Proof.
by move=> Pi0 op_idx'; apply: eq_big_idx_seq => //; apply/hasP; exists i0.
Qed.

Lemma big1_eq I r (P : pred I) : \big[*%M/1]_(i <- r | P i) 1 = 1.
Proof.
by rewrite big_const_seq; elim: (count _ _) => //= n ->; apply: mul1m.
Qed.

Lemma big1 I r (P : pred I) F :
  (forall i, P i -> F i = 1) -> \big[*%M/1]_(i <- r | P i) F i = 1.
Proof. by move/(eq_bigr _)->; apply: big1_eq. Qed.

Lemma big1_seq (I : eqType) r (P : pred I) F :
    (forall i, P i && (i \in r) -> F i = 1) ->
  \big[*%M/1]_(i <- r | P i) F i = 1.
Proof. by move=> eqF1; rewrite big_seq_cond big_andbC big1. Qed.

Lemma big_seq1 I (i : I) F : \big[*%M/1]_(j <- [:: i]) F j = F i.
Proof. by rewrite unlock /= mulm1. Qed.

Lemma big_mkcond I r (P : pred I) F :
  \big[*%M/1]_(i <- r | P i) F i =
     \big[*%M/1]_(i <- r) (if P i then F i else 1).
Proof. by rewrite unlock; elim: r => //= i r ->; case P; rewrite ?mul1m. Qed.

Lemma big_mkcondr I r (P Q : pred I) F :
  \big[*%M/1]_(i <- r | P i && Q i) F i =
     \big[*%M/1]_(i <- r | P i) (if Q i then F i else 1).
Proof. by rewrite -big_filter_cond big_mkcond big_filter. Qed.

Lemma big_mkcondl I r (P Q : pred I) F :
  \big[*%M/1]_(i <- r | P i && Q i) F i =
     \big[*%M/1]_(i <- r | Q i) (if P i then F i else 1).
Proof. by rewrite big_andbC big_mkcondr. Qed.

Lemma big_uncond I (r : seq I) (P : pred I) F :
  (forall i, ~~ P i -> F i = 1) ->
  \big[*%M/1]_(i <- r | P i) F i = \big[*%M/1]_(i <- r) F i.
Proof.
move=> F_eq1; rewrite big_mkcond; apply: eq_bigr => i.
by case: (P i) (F_eq1 i) => // ->.
Qed.

Lemma big_rmcond_in (I : eqType) (r : seq I) (P : pred I) F :
  (forall i, i \in r -> ~~ P i -> F i = 1) ->
  \big[*%M/1]_(i <- r | P i) F i = \big[*%M/1]_(i <- r) F i.
Proof.
move=> F_eq1; rewrite big_seq_cond [RHS]big_seq_cond !big_mkcondl big_uncond//.
by move=> i /F_eq1; case: ifP => // _ ->.
Qed.

Lemma big_cat I r1 r2 (P : pred I) F :
  \big[*%M/1]_(i <- r1 ++ r2 | P i) F i =
     \big[*%M/1]_(i <- r1 | P i) F i * \big[*%M/1]_(i <- r2 | P i) F i.
Proof.
rewrite !(big_mkcond _ P) unlock.
by elim: r1 => /= [|i r1 ->]; rewrite (mul1m, mulmA).
Qed.

Lemma big_allpairs_dep I1 (I2 : I1 -> Type) J (h : forall i1, I2 i1 -> J)
    (r1 : seq I1) (r2 : forall i1, seq (I2 i1)) (F : J -> R) :
  \big[*%M/1]_(i <- [seq h i1 i2 | i1 <- r1, i2 <- r2 i1]) F i =
    \big[*%M/1]_(i1 <- r1) \big[*%M/1]_(i2 <- r2 i1) F (h i1 i2).
Proof.
elim: r1 => [|i1 r1 IHr1]; first by rewrite !big_nil.
by rewrite big_cat IHr1 big_cons big_map.
Qed.

Lemma big_allpairs I1 I2 (r1 : seq I1) (r2 : seq I2) F :
  \big[*%M/1]_(i <- [seq (i1, i2) | i1 <- r1, i2 <- r2]) F i =
    \big[*%M/1]_(i1 <- r1) \big[op/idx]_(i2 <- r2) F (i1, i2).
Proof. exact: big_allpairs_dep. Qed.

Lemma big_pred1_eq (I : finType) (i : I) F :
  \big[*%M/1]_(j | j == i) F j = F i.
Proof.
have [e1 <- _ [e_enum _]] := big_enumP (pred1 i).
by rewrite (perm_small_eq _ e_enum) enum1 ?big_seq1.
Qed.

Lemma big_pred1 (I : finType) i (P : pred I) F :
  P =1 pred1 i -> \big[*%M/1]_(j | P j) F j = F i.
Proof. by move/(eq_bigl _ _)->; apply: big_pred1_eq. Qed.

Lemma big_cat_nat n m p (P : pred nat) F : m <= n -> n <= p ->
  \big[*%M/1]_(m <= i < p | P i) F i =
   (\big[*%M/1]_(m <= i < n | P i) F i) * (\big[*%M/1]_(n <= i < p | P i) F i).
Proof.
move=> le_mn le_np; rewrite -big_cat -{2}(subnKC le_mn) -iotaD subnDA.
by rewrite subnKC // leq_sub.
Qed.

Lemma big_nat1 n F : \big[*%M/1]_(n <= i < n.+1) F i = F n.
Proof. by rewrite big_ltn // big_geq // mulm1. Qed.

Lemma big_nat_recr n m F : m <= n ->
  \big[*%M/1]_(m <= i < n.+1) F i = (\big[*%M/1]_(m <= i < n) F i) * F n.
Proof. by move=> lemn; rewrite (@big_cat_nat n) ?leqnSn // big_nat1. Qed.

Lemma big_ord_recr n F :
  \big[*%M/1]_(i < n.+1) F i =
     (\big[*%M/1]_(i < n) F (widen_ord (leqnSn n) i)) * F ord_max.
Proof.
transitivity (\big[*%M/1]_(0 <= i < n.+1) F (inord i)).
  by rewrite big_mkord; apply: eq_bigr=> i _; rewrite inord_val.
rewrite big_nat_recr // big_mkord; congr (_ * F _); last first.
  by apply: val_inj; rewrite /= inordK.
by apply: eq_bigr => [] i _; congr F; apply: ord_inj; rewrite inordK //= leqW.
Qed.

Lemma big_sumType (I1 I2 : finType) (P : pred (I1 + I2)) F :
  \big[*%M/1]_(i | P i) F i =
        (\big[*%M/1]_(i | P (inl _ i)) F (inl _ i))
      * (\big[*%M/1]_(i | P (inr _ i)) F (inr _ i)).
Proof.
by rewrite ![index_enum _]unlock [@Finite.enum in LHS]unlock/= big_cat !big_map.
Qed.

Lemma big_split_ord m n (P : pred 'I_(m + n)) F :
  \big[*%M/1]_(i | P i) F i =
        (\big[*%M/1]_(i | P (lshift n i)) F (lshift n i))
      * (\big[*%M/1]_(i | P (rshift m i)) F (rshift m i)).
Proof.
rewrite -(big_map _ _ (lshift n) _ P F) -(big_map _ _ (@rshift m _) _ P F).
rewrite -big_cat; congr bigop; apply: (inj_map val_inj).
rewrite map_cat -!map_comp (map_comp (addn m)) /=.
by rewrite ![index_enum _]unlock unlock !val_ord_enum -iotaDl addn0 iotaD.
Qed.

Lemma big_flatten I rr (P : pred I) F :
  \big[*%M/1]_(i <- flatten rr | P i) F i
    = \big[*%M/1]_(r <- rr) \big[*%M/1]_(i <- r | P i) F i.
Proof.
by elim: rr => [|r rr IHrr]; rewrite ?big_nil //= big_cat big_cons -IHrr.
Qed.

End Plain.

Section Abelian.

Variable op : Monoid.com_law 1.

Local Notation "'*%M'" := op (at level 0).
Local Notation "x * y" := (op x y).

Lemma perm_big (I : eqType) r1 r2 (P : pred I) F :
    perm_eq r1 r2 ->
  \big[*%M/1]_(i <- r1 | P i) F i = \big[*%M/1]_(i <- r2 | P i) F i.
Proof.
move/permP; rewrite !(big_mkcond _ _ P).
elim: r1 r2 => [|i r1 IHr1] r2 eq_r12.
  by case: r2 eq_r12 => // i r2 /(_ (pred1 i)); rewrite /= eqxx.
have r2i: i \in r2 by rewrite -has_pred1 has_count -eq_r12 /= eqxx.
case/splitPr: r2 / r2i => [r3 r4] in eq_r12 *; rewrite big_cat /= !big_cons.
rewrite mulmCA; congr (_ * _); rewrite -big_cat; apply: IHr1 => a.
by move/(_ a): eq_r12; rewrite !count_cat /= addnCA; apply: addnI.
Qed.

Lemma big_enum_cond (I : finType) (A : {pred I}) (P : pred I) F :
  \big[*%M/1]_(i <- enum A | P i) F i = \big[*%M/1]_(i in A | P i) F i.
Proof.
by rewrite -big_filter_cond; have [e _ _ [/perm_big->]] := big_enumP.
Qed.

Lemma big_enum (I : finType) (A : {pred I}) F :
  \big[*%M/1]_(i <- enum A) F i = \big[*%M/1]_(i in A) F i.
Proof. by rewrite big_enum_cond big_andbC. Qed.

Lemma big_uniq (I : finType) (r : seq I) F :
  uniq r -> \big[*%M/1]_(i <- r) F i = \big[*%M/1]_(i in r) F i.
Proof.
move=> uniq_r; rewrite -big_enum; apply: perm_big.
by rewrite uniq_perm ?enum_uniq // => i; rewrite mem_enum.
Qed.

Lemma big_rem (I : eqType) r x (P : pred I) F :
    x \in r ->
  \big[*%M/1]_(y <- r | P y) F y
    = (if P x then F x else 1) * \big[*%M/1]_(y <- rem x r | P y) F y.
Proof.
by move/perm_to_rem/(perm_big _)->; rewrite !(big_mkcond _ _ P) big_cons.
Qed.

Lemma big_undup (I : eqType) (r : seq I) (P : pred I) F :
    idempotent *%M ->
  \big[*%M/1]_(i <- undup r | P i) F i = \big[*%M/1]_(i <- r | P i) F i.
Proof.
move=> idM; rewrite -!(big_filter _ _ _ P) filter_undup.
elim: {P r}(filter P r) => //= i r IHr.
case: ifP => [r_i | _]; rewrite !big_cons {}IHr //.
by rewrite (big_rem _ _ r_i) mulmA idM.
Qed.

Lemma eq_big_idem (I : eqType) (r1 r2 : seq I) (P : pred I) F :
    idempotent *%M -> r1 =i r2 ->
  \big[*%M/1]_(i <- r1 | P i) F i = \big[*%M/1]_(i <- r2 | P i) F i.
Proof.
move=> idM eq_r; rewrite -big_undup // -(big_undup r2) //; apply/perm_big.
by rewrite uniq_perm ?undup_uniq // => i; rewrite !mem_undup eq_r.
Qed.

Lemma big_undup_iterop_count (I : eqType) (r : seq I) (P : pred I) F :
  \big[*%M/1]_(i <- undup r | P i) iterop (count_mem i r) *%M (F i) 1
    = \big[*%M/1]_(i <- r | P i) F i.
Proof.
rewrite -[RHS](perm_big _ F (perm_count_undup _)) big_flatten big_map.
by rewrite big_mkcond; apply: eq_bigr => i _; rewrite big_nseq_cond iteropE.
Qed.

Lemma big_split I r (P : pred I) F1 F2 :
  \big[*%M/1]_(i <- r | P i) (F1 i * F2 i) =
    \big[*%M/1]_(i <- r | P i) F1 i * \big[*%M/1]_(i <- r | P i) F2 i.
Proof.
by elim/big_rec3: _ => [|i x y _ _ ->]; rewrite ?mulm1 // mulmCA -!mulmA mulmCA.
Qed.

Lemma bigID I r (a P : pred I) F :
  \big[*%M/1]_(i <- r | P i) F i =
    \big[*%M/1]_(i <- r | P i && a i) F i *
    \big[*%M/1]_(i <- r | P i && ~~ a i) F i.
Proof.
rewrite !(big_mkcond _ _ _ F) -big_split.
by apply: eq_bigr => i; case: (a i); rewrite !simpm.
Qed.
Arguments bigID [I r].

Lemma bigU (I : finType) (A B : pred I) F :
    [disjoint A & B] ->
  \big[*%M/1]_(i in [predU A & B]) F i =
    (\big[*%M/1]_(i in A) F i) * (\big[*%M/1]_(i in B) F i).
Proof.
move=> dAB; rewrite (bigID (mem A)).
congr (_ * _); apply: eq_bigl => i; first by rewrite orbK.
by have:= pred0P dAB i; rewrite andbC /= !inE; case: (i \in A).
Qed.

Lemma bigD1 (I : finType) j (P : pred I) F :
  P j -> \big[*%M/1]_(i | P i) F i
    = F j * \big[*%M/1]_(i | P i && (i != j)) F i.
Proof.
move=> Pj; rewrite (bigID (pred1 j)); congr (_ * _).
by apply: big_pred1 => i; rewrite /= andbC; case: eqP => // ->.
Qed.
Arguments bigD1 [I] j [P F].

Lemma bigD1_seq (I : eqType) (r : seq I) j F :
    j \in r -> uniq r ->
  \big[*%M/1]_(i <- r) F i = F j * \big[*%M/1]_(i <- r | i != j) F i.
Proof. by move=> /big_rem-> /rem_filter->; rewrite big_filter. Qed.

Lemma cardD1x (I : finType) (A : pred I) j :
  A j -> #|SimplPred A| = 1 + #|[pred i | A i & i != j]|.
Proof.
move=> Aj; rewrite (cardD1 j) [j \in A]Aj; congr (_ + _).
by apply: eq_card => i; rewrite inE /= andbC.
Qed.
Arguments cardD1x [I A].

Lemma partition_big (I J : finType) (P : pred I) p (Q : pred J) F :
    (forall i, P i -> Q (p i)) ->
      \big[*%M/1]_(i | P i) F i =
         \big[*%M/1]_(j | Q j) \big[*%M/1]_(i | P i && (p i == j)) F i.
Proof.
move=> Qp; transitivity (\big[*%M/1]_(i | P i && Q (p i)) F i).
  by apply: eq_bigl => i; case Pi: (P i); rewrite // Qp.
have [n leQn] := ubnP #|Q|; elim: n => // n IHn in Q {Qp} leQn *.
case: (pickP Q) => [j Qj | Q0]; last first.
  by rewrite !big_pred0 // => i; rewrite Q0 andbF.
rewrite (bigD1 j) // -IHn; last by rewrite ltnS (cardD1x j Qj) in leQn.
rewrite (bigID (fun i => p i == j)); congr (_ * _); apply: eq_bigl => i.
  by case: eqP => [-> | _]; rewrite !(Qj, simpm).
by rewrite andbA.
Qed.

Arguments partition_big [I J P] p Q [F].

Lemma big_image_cond I (J : finType) (h : J -> I) (A : pred J) (P : pred I) F :
  \big[*%M/1]_(i <- [seq h j | j in A] | P i) F i
     = \big[*%M/1]_(j in A | P (h j)) F (h j).
Proof. by rewrite big_map big_enum_cond. Qed.

Lemma big_image I (J : finType) (h : J -> I) (A : pred J) F :
  \big[*%M/1]_(i <- [seq h j | j in A]) F i = \big[*%M/1]_(j in A) F (h j).
Proof. by rewrite big_map big_enum. Qed.

Lemma big_image_cond_id (J : finType) (h : J -> R) (A : pred J) (P : pred R) :
  \big[*%M/1]_(i <- [seq h j | j in A] | P i) i
    = \big[*%M/1]_(j in A | P (h j)) h j.
Proof. exact: big_image_cond. Qed.

Lemma big_image_id (J : finType) (h : J -> R) (A : pred J) :
  \big[*%M/1]_(i <- [seq h j | j in A]) i = \big[*%M/1]_(j in A) h j.
Proof. exact: big_image. Qed.

Lemma reindex_omap (I J : finType) (h : J -> I) h' (P : pred I) F :
    (forall i, P i -> omap h (h' i) = some i) ->
  \big[*%M/1]_(i | P i) F i =
    \big[*%M/1]_(j | P (h j) && (h' (h j) == some j)) F (h j).
Proof.
move=> h'K; have [n lePn] := ubnP #|P|; elim: n => // n IHn in P h'K lePn *.
case: (pickP P) => [i Pi | P0]; last first.
  by rewrite !big_pred0 // => j; rewrite P0.
have := h'K i Pi; case h'i_eq : (h' i) => [/= j|//] [hj_eq].
rewrite (bigD1 i Pi) (bigD1 j) hj_eq ?Pi ?h'i_eq ?eqxx //=; congr (_ * _).
rewrite {}IHn => [|k /andP[]|]; [|by auto | by rewrite (cardD1x i) in lePn].
apply: eq_bigl => k; rewrite andbC -andbA (andbCA (P _)); case: eqP => //= hK.
congr (_ && ~~ _); apply/eqP/eqP => [|->//].
by move=> /(congr1 h'); rewrite h'i_eq hK => -[].
Qed.
Arguments reindex_omap [I J] h h' [P F].

Lemma reindex_onto (I J : finType) (h : J -> I) h' (P : pred I) F :
    (forall i, P i -> h (h' i) = i) ->
  \big[*%M/1]_(i | P i) F i =
    \big[*%M/1]_(j | P (h j) && (h' (h j) == j)) F (h j).
Proof.
by move=> h'K; rewrite (reindex_omap h (some \o h'))//= => i Pi; rewrite h'K.
Qed.
Arguments reindex_onto [I J] h h' [P F].

Lemma reindex (I J : finType) (h : J -> I) (P : pred I) F :
    {on [pred i | P i], bijective h} ->
  \big[*%M/1]_(i | P i) F i = \big[*%M/1]_(j | P (h j)) F (h j).
Proof.
case=> h' hK h'K; rewrite (reindex_onto h h' h'K).
by apply: eq_bigl => j; rewrite !inE; case Pi: (P _); rewrite //= hK ?eqxx.
Qed.
Arguments reindex [I J] h [P F].

Lemma reindex_inj (I : finType) (h : I -> I) (P : pred I) F :
  injective h -> \big[*%M/1]_(i | P i) F i = \big[*%M/1]_(j | P (h j)) F (h j).
Proof. by move=> injh; apply: reindex (onW_bij _ (injF_bij injh)). Qed.
Arguments reindex_inj [I h P F].

Lemma bigD1_ord n j (P : pred 'I_n) F :
  P j -> \big[*%M/1]_(i < n | P i) F i
    = F j * \big[*%M/1]_(i < n.-1 | P (lift j i)) F (lift j i).
Proof.
move=> Pj; rewrite (bigD1 j Pj) (reindex_omap (lift j) (unlift j))/=.
  by under eq_bigl do rewrite liftK eq_sym eqxx neq_lift ?andbT.
by move=> i; case: unliftP => [k ->|->]; rewrite ?eqxx ?andbF.
Qed.

Lemma big_enum_val_cond (I : finType) (A : pred I) (P : pred I) F :
  \big[op/idx]_(x in A | P x) F x =
  \big[op/idx]_(i < #|A| | P (enum_val i)) F (enum_val i).
Proof.
have [A_eq0|/card_gt0P[x0 x0A]] := posnP #|A|.
  rewrite !big_pred0 // => i; last by rewrite card0_eq.
  by have: false by move: i => []; rewrite A_eq0.
rewrite (reindex (enum_val : 'I_#|A| -> I)).
  by apply: eq_big => [x|x Px]; rewrite ?enum_valP.
by apply: subon_bij (enum_val_bij_in x0A) => y /andP[].
Qed.
Arguments big_enum_val_cond [I A] P F.

Lemma big_enum_rank_cond (I : finType) (A : pred I) x (xA : x \in A) P F
  (h := enum_rank_in xA) :
  \big[op/idx]_(i < #|A| | P i) F i = \big[op/idx]_(s in A | P (h s)) F (h s).
Proof.
rewrite big_enum_val_cond {}/h.
by apply: eq_big => [i|i Pi]; rewrite ?enum_valK_in.
Qed.
Arguments big_enum_rank_cond [I A x] xA P F.

Lemma big_enum_val (I : finType) (A : pred I) F :
  \big[op/idx]_(x in A) F x = \big[op/idx]_(i < #|A|) F (enum_val i).
Proof. by rewrite -(big_enum_val_cond predT) big_mkcondr. Qed.
Arguments big_enum_val [I A] F.

Lemma big_enum_rank (I : finType) (A : pred I) x (xA : x \in A) F
  (h := enum_rank_in xA) :
  \big[op/idx]_(i < #|A|) F i = \big[op/idx]_(s in A) F (h s).
Proof. by rewrite (big_enum_rank_cond xA) big_mkcondr. Qed.
Arguments big_enum_rank [I A x] xA F.

Lemma big_nat_rev m n P F :
  \big[*%M/1]_(m <= i < n | P i) F i
     = \big[*%M/1]_(m <= i < n | P (m + n - i.+1)) F (m + n - i.+1).
Proof.
case: (ltnP m n) => ltmn; last by rewrite !big_geq.
rewrite -{3 4}(subnK (ltnW ltmn)) addnA.
do 2!rewrite (big_addn _ _ 0) big_mkord; rewrite (reindex_inj rev_ord_inj) /=.
by apply: eq_big => [i | i _]; rewrite /= -addSn subnDr addnC addnBA.
Qed.

Lemma sig_big_dep (I : finType) (J : I -> finType)
    (P : pred I) (Q : forall {i}, pred (J i)) (F : forall {i}, J i -> R) :
  \big[op/idx]_(i | P i) \big[op/idx]_(j : J i | Q j) F j =
  \big[op/idx]_(p : {i : I & J i} | P (tag p) && Q (tagged p)) F (tagged p).
Proof.
pose s := [seq Tagged J j | i <- index_enum I, j <- index_enum (J i)].
rewrite [LHS]big_mkcond big_mkcondl [RHS]big_mkcond -[RHS](@perm_big _ s).
  rewrite big_allpairs_dep/=; apply: eq_bigr => i _; rewrite -big_mkcond/=.
  by case: P; rewrite // big1.
rewrite uniq_perm ?index_enum_uniq//.
  by rewrite allpairs_uniq_dep// => [|i|[i j] []]; rewrite ?index_enum_uniq.
by move=> [i j]; rewrite ?mem_index_enum; apply/allpairsPdep; exists i, j.
Qed.

Lemma pair_big_dep (I J : finType) (P : pred I) (Q : I -> pred J) F :
  \big[*%M/1]_(i | P i) \big[*%M/1]_(j | Q i j) F i j =
    \big[*%M/1]_(p | P p.1 && Q p.1 p.2) F p.1 p.2.
Proof.
rewrite sig_big_dep; apply: (reindex (fun x => Tagged (fun=> J) x.2)).
by exists (fun x => (projT1 x, projT2 x)) => -[].
Qed.

Lemma pair_big (I J : finType) (P : pred I) (Q : pred J) F :
  \big[*%M/1]_(i | P i) \big[*%M/1]_(j | Q j) F i j =
    \big[*%M/1]_(p | P p.1 && Q p.2) F p.1 p.2.
Proof. exact: pair_big_dep. Qed.

Lemma pair_bigA (I J : finType) (F : I -> J -> R) :
  \big[*%M/1]_i \big[*%M/1]_j F i j = \big[*%M/1]_p F p.1 p.2.
Proof. exact: pair_big_dep. Qed.

Lemma exchange_big_dep I J rI rJ (P : pred I) (Q : I -> pred J)
                       (xQ : pred J) F :
    (forall i j, P i -> Q i j -> xQ j) ->
  \big[*%M/1]_(i <- rI | P i) \big[*%M/1]_(j <- rJ | Q i j) F i j =
    \big[*%M/1]_(j <- rJ | xQ j) \big[*%M/1]_(i <- rI | P i && Q i j) F i j.
Proof.
move=> PQxQ; pose p u := (u.2, u.1).
under [LHS]eq_bigr do rewrite big_tnth; rewrite [LHS]big_tnth.
under [RHS]eq_bigr do rewrite big_tnth; rewrite [RHS]big_tnth.
rewrite !pair_big_dep (reindex_onto (p _ _) (p _ _)) => [|[]] //=.
apply: eq_big => [] [j i] //=; symmetry; rewrite eqxx andbT andb_idl //.
by case/andP; apply: PQxQ.
Qed.
Arguments exchange_big_dep [I J rI rJ P Q] xQ [F].

Lemma exchange_big I J rI rJ (P : pred I) (Q : pred J) F :
  \big[*%M/1]_(i <- rI | P i) \big[*%M/1]_(j <- rJ | Q j) F i j =
    \big[*%M/1]_(j <- rJ | Q j) \big[*%M/1]_(i <- rI | P i) F i j.
Proof.
rewrite (exchange_big_dep Q) //.
by under eq_bigr => i Qi do under eq_bigl do rewrite Qi andbT.
Qed.

Lemma exchange_big_dep_nat m1 n1 m2 n2 (P : pred nat) (Q : rel nat)
                           (xQ : pred nat) F :
    (forall i j, m1 <= i < n1 -> m2 <= j < n2 -> P i -> Q i j -> xQ j) ->
  \big[*%M/1]_(m1 <= i < n1 | P i) \big[*%M/1]_(m2 <= j < n2 | Q i j) F i j =
    \big[*%M/1]_(m2 <= j < n2 | xQ j)
       \big[*%M/1]_(m1 <= i < n1 | P i && Q i j) F i j.
Proof.
move=> PQxQ; under eq_bigr do rewrite big_seq_cond.
rewrite big_seq_cond /= (exchange_big_dep xQ) => [|i j]; last first.
  by rewrite !mem_index_iota => /andP[mn_i Pi] /andP[mn_j /PQxQ->].
rewrite 2!(big_seq_cond _ _ _ xQ); apply: eq_bigr => j /andP[-> _] /=.
by rewrite [rhs in _ = rhs]big_seq_cond; apply: eq_bigl => i; rewrite -andbA.
Qed.
Arguments exchange_big_dep_nat [m1 n1 m2 n2 P Q] xQ [F].

Lemma exchange_big_nat m1 n1 m2 n2 (P Q : pred nat) F :
  \big[*%M/1]_(m1 <= i < n1 | P i) \big[*%M/1]_(m2 <= j < n2 | Q j) F i j =
    \big[*%M/1]_(m2 <= j < n2 | Q j) \big[*%M/1]_(m1 <= i < n1 | P i) F i j.
Proof.
rewrite (exchange_big_dep_nat Q) //.
by under eq_bigr => i Qi do under eq_bigl do rewrite Qi andbT.
Qed.

End Abelian.

End MonoidProperties.

Arguments big_filter [R idx op I].
Arguments big_filter_cond [R idx op I].
Arguments congr_big [R idx op I r1] r2 [P1] P2 [F1] F2.
Arguments eq_big [R idx op I r P1] P2 [F1] F2.
Arguments eq_bigl [R idx op I r P1] P2.
Arguments eq_bigr [R idx op I r P F1] F2.
Arguments eq_big_idx [R idx op idx' I] i0 [P F].
Arguments big_seq_cond [R idx op I r].
Arguments eq_big_seq [R idx op I r F1] F2.
Arguments congr_big_nat [R idx op m1 n1] m2 n2 [P1] P2 [F1] F2.
Arguments big_map [R idx op I J] h [r].
Arguments big_nth [R idx op I] x0 [r].
Arguments big_catl [R idx op I r1 r2 P F].
Arguments big_catr [R idx op I r1 r2 P F].
Arguments big_geq [R idx op m n P F].
Arguments big_ltn_cond [R idx op m n P F].
Arguments big_ltn [R idx op m n F].
Arguments big_addn [R idx op].
Arguments big_mkord [R idx op n].
Arguments big_nat_widen [R idx op] .
Arguments big_ord_widen_cond [R idx op n1].
Arguments big_ord_widen [R idx op n1].
Arguments big_ord_widen_leq [R idx op n1].
Arguments big_ord_narrow_cond [R idx op n1 n2 P F].
Arguments big_ord_narrow_cond_leq [R idx op n1 n2 P F].
Arguments big_ord_narrow [R idx op n1 n2 F].
Arguments big_ord_narrow_leq [R idx op n1 n2 F].
Arguments big_mkcond [R idx op I r].
Arguments big1_eq [R idx op I].
Arguments big1_seq [R idx op I].
Arguments big1 [R idx op I].
Arguments big_pred1 [R idx op I] i [P F].
Arguments perm_big [R idx op I r1] r2 [P F].
Arguments big_uniq [R idx op I] r [F].
Arguments big_rem [R idx op I r] x [P F].
Arguments bigID [R idx op I r].
Arguments bigU [R idx op I].
Arguments bigD1 [R idx op I] j [P F].
Arguments bigD1_seq [R idx op I r] j [F].
Arguments bigD1_ord [R idx op n] j [P F].
Arguments partition_big [R idx op I J P] p Q [F].
Arguments reindex_omap [R idx op I J] h h' [P F].
Arguments reindex_onto [R idx op I J] h h' [P F].
Arguments reindex [R idx op I J] h [P F].
Arguments reindex_inj [R idx op I h P F].
Arguments big_enum_val_cond [R idx op I A] P F.
Arguments big_enum_rank_cond [R idx op I A x] xA P F.
Arguments big_enum_val [R idx op I A] F.
Arguments big_enum_rank [R idx op I A x] xA F.
Arguments sig_big_dep [R idx op I J].
Arguments pair_big_dep [R idx op I J].
Arguments pair_big [R idx op I J].
Arguments big_allpairs_dep {R idx op I1 I2 J h r1 r2 F}.
Arguments big_allpairs {R idx op I1 I2 r1 r2 F}.
Arguments exchange_big_dep [R idx op I J rI rJ P Q] xQ [F].
Arguments exchange_big_dep_nat [R idx op m1 n1 m2 n2 P Q] xQ [F].
Arguments big_ord_recl [R idx op].
Arguments big_ord_recr [R idx op].
Arguments big_nat_recl [R idx op].
Arguments big_nat_recr [R idx op].

Section Distributivity.

Import Monoid.Theory.

Variable R : Type.
Variables zero one : R.
Local Notation "0" := zero.
Local Notation "1" := one.
Variable times : Monoid.mul_law 0.
Local Notation "*%M" := times (at level 0).
Local Notation "x * y" := (times x y).
Variable plus : Monoid.add_law 0 *%M.
Local Notation "+%M" := plus (at level 0).
Local Notation "x + y" := (plus x y).

Lemma big_distrl I r a (P : pred I) F :
  \big[+%M/0]_(i <- r | P i) F i * a = \big[+%M/0]_(i <- r | P i) (F i * a).
Proof. by rewrite (big_endo ( *%M^~ a)) ?mul0m // => x y; apply: mulmDl. Qed.

Lemma big_distrr I r a (P : pred I) F :
  a * \big[+%M/0]_(i <- r | P i) F i = \big[+%M/0]_(i <- r | P i) (a * F i).
Proof. by rewrite big_endo ?mulm0 // => x y; apply: mulmDr. Qed.

Lemma big_distrlr I J rI rJ (pI : pred I) (pJ : pred J) F G :
  (\big[+%M/0]_(i <- rI | pI i) F i) * (\big[+%M/0]_(j <- rJ | pJ j) G j)
   = \big[+%M/0]_(i <- rI | pI i) \big[+%M/0]_(j <- rJ | pJ j) (F i * G j).
Proof. by rewrite big_distrl; under eq_bigr do rewrite big_distrr. Qed.

Lemma big_distr_big_dep (I J : finType) j0 (P : pred I) (Q : I -> pred J) F :
  \big[*%M/1]_(i | P i) \big[+%M/0]_(j | Q i j) F i j =
     \big[+%M/0]_(f in pfamily j0 P Q) \big[*%M/1]_(i | P i) F i (f i).
Proof.
pose fIJ := {ffun I -> J}; pose Pf := pfamily j0 (_ : seq I) Q.
have [r big_r [Ur mem_r] _] := big_enumP P.
symmetry; transitivity (\big[+%M/0]_(f in Pf r) \big[*%M/1]_(i <- r) F i (f i)).
  by apply: eq_big => // f; apply: eq_forallb => i; rewrite /= mem_r.
rewrite -{P mem_r}big_r; elim: r Ur => /= [_ | i r IHr].
  rewrite (big_pred1 [ffun=> j0]) ?big_nil //= => f.
  apply/familyP/eqP=> /= [Df |->{f} i]; last by rewrite ffunE !inE.
  by apply/ffunP=> i; rewrite ffunE; apply/eqP/Df.
case/andP=> /negbTE nri; rewrite big_cons big_distrl => {}/IHr<-.
rewrite (partition_big (fun f : fIJ => f i) (Q i)) => [|f]; last first.
  by move/familyP/(_ i); rewrite /= inE /= eqxx.
pose seti j (f : fIJ) := [ffun k => if k == i then j else f k].
apply: eq_bigr => j Qij.
rewrite (reindex_onto (seti j) (seti j0)) => [|f /andP[_ /eqP fi]]; last first.
  by apply/ffunP=> k; rewrite !ffunE; case: eqP => // ->.
rewrite big_distrr; apply: eq_big => [f | f eq_f]; last first.
  rewrite big_cons ffunE eqxx !big_seq; congr (_ * _).
  by apply: eq_bigr => k; rewrite ffunE; case: eqP nri => // -> ->.
rewrite !ffunE !eqxx andbT; apply/andP/familyP=> /= [[Pjf fij0] k | Pff].
  have:= familyP Pjf k; rewrite /= ffunE inE; case: eqP => // -> _.
  by rewrite nri -(eqP fij0) !ffunE !inE !eqxx.
split; [apply/familyP | apply/eqP/ffunP] => k; have:= Pff k; rewrite !ffunE.
  by rewrite inE; case: eqP => // ->.
by case: eqP => // ->; rewrite nri /= => /eqP.
Qed.

Lemma big_distr_big (I J : finType) j0 (P : pred I) (Q : pred J) F :
  \big[*%M/1]_(i | P i) \big[+%M/0]_(j | Q j) F i j =
     \big[+%M/0]_(f in pffun_on j0 P Q) \big[*%M/1]_(i | P i) F i (f i).
Proof.
rewrite (big_distr_big_dep j0); apply: eq_bigl => f.
by apply/familyP/familyP=> Pf i; case: ifP (Pf i).
Qed.

Lemma bigA_distr_big_dep (I J : finType) (Q : I -> pred J) F :
  \big[*%M/1]_i \big[+%M/0]_(j | Q i j) F i j
    = \big[+%M/0]_(f in family Q) \big[*%M/1]_i F i (f i).
Proof.
have [j _ | J0] := pickP J; first by rewrite (big_distr_big_dep j).
have Q0 i: Q i =i pred0 by move=> /J0/esym/notF[].
transitivity (iter #|I| ( *%M 0) 1).
  by rewrite -big_const; apply/eq_bigr=> i; have /(big_pred0 _)-> := Q0 i.
have [i _ | I0] := pickP I.
  rewrite (cardD1 i) //= mul0m big_pred0 // => f.
  by apply/familyP=> /(_ i); rewrite Q0.
have f: I -> J by move=> /I0/esym/notF[].
rewrite eq_card0 // (big_pred1 (finfun f)) ?big_pred0 // => g.
by apply/familyP/eqP=> _; first apply/ffunP; move=> /I0/esym/notF[].
Qed.

Lemma bigA_distr_big (I J : finType) (Q : pred J) (F : I -> J -> R) :
  \big[*%M/1]_i \big[+%M/0]_(j | Q j) F i j
    = \big[+%M/0]_(f in ffun_on Q) \big[*%M/1]_i F i (f i).
Proof. exact: bigA_distr_big_dep. Qed.

Lemma bigA_distr_bigA (I J : finType) F :
  \big[*%M/1]_(i : I) \big[+%M/0]_(j : J) F i j
    = \big[+%M/0]_(f : {ffun I -> J}) \big[*%M/1]_i F i (f i).
Proof. by rewrite bigA_distr_big; apply: eq_bigl => ?; apply/familyP. Qed.

End Distributivity.

Arguments big_distrl [R zero times plus I r].
Arguments big_distrr [R zero times plus I r].
Arguments big_distr_big_dep [R zero one times plus I J].
Arguments big_distr_big [R zero one times plus I J].
Arguments bigA_distr_big_dep [R zero one times plus I J].
Arguments bigA_distr_big [R zero one times plus I J].
Arguments bigA_distr_bigA [R zero one times plus I J].

Section BigBool.

Section Seq.

Variables (I : Type) (r : seq I) (P B : pred I).

Lemma big_has : \big[orb/false]_(i <- r) B i = has B r.
Proof. by rewrite unlock. Qed.

Lemma big_all : \big[andb/true]_(i <- r) B i = all B r.
Proof. by rewrite unlock. Qed.

Lemma big_has_cond : \big[orb/false]_(i <- r | P i) B i = has (predI P B) r.
Proof. by rewrite big_mkcond unlock. Qed.

Lemma big_all_cond :
  \big[andb/true]_(i <- r | P i) B i = all [pred i | P i ==> B i] r.
Proof. by rewrite big_mkcond unlock. Qed.

End Seq.

Section FinType.

Variables (I : finType) (P B : pred I).

Lemma big_orE : \big[orb/false]_(i | P i) B i = [exists (i | P i), B i].
Proof. by rewrite big_has_cond; apply/hasP/existsP=> [] [i]; exists i. Qed.

Lemma big_andE : \big[andb/true]_(i | P i) B i = [forall (i | P i), B i].
Proof.
rewrite big_all_cond; apply/allP/forallP=> /= allB i; rewrite allB //.
exact: mem_index_enum.
Qed.

End FinType.

End BigBool.

Section NatConst.

Variables (I : finType) (A : pred I).

Lemma sum_nat_const n : \sum_(i in A) n = #|A| * n.
Proof. by rewrite big_const iter_addn_0 mulnC. Qed.

Lemma sum1_card : \sum_(i in A) 1 = #|A|.
Proof. by rewrite sum_nat_const muln1. Qed.

Lemma sum1_count J (r : seq J) (a : pred J) : \sum_(j <- r | a j) 1 = count a r.
Proof. by rewrite big_const_seq iter_addn_0 mul1n. Qed.

Lemma sum1_size J (r : seq J) : \sum_(j <- r) 1 = size r.
Proof. by rewrite sum1_count count_predT. Qed.

Lemma prod_nat_const n : \prod_(i in A) n = n ^ #|A|.
Proof. by rewrite big_const -Monoid.iteropE. Qed.

Lemma sum_nat_const_nat n1 n2 n : \sum_(n1 <= i < n2) n = (n2 - n1) * n.
Proof. by rewrite big_const_nat iter_addn_0 mulnC. Qed.

Lemma prod_nat_const_nat n1 n2 n : \prod_(n1 <= i < n2) n = n ^ (n2 - n1).
Proof. by rewrite big_const_nat -Monoid.iteropE. Qed.

End NatConst.

Lemma sumnE r : sumn r = \sum_(i <- r) i. Proof. exact: foldrE. Qed.

Lemma leqif_sum (I : finType) (P C : pred I) (E1 E2 : I -> nat) :
    (forall i, P i -> E1 i <= E2 i ?= iff C i) ->
  \sum_(i | P i) E1 i <= \sum_(i | P i) E2 i ?= iff [forall (i | P i), C i].
Proof.
move=> leE12; rewrite -big_andE.
by elim/big_rec3: _ => // i Ci m1 m2 /leE12; apply: leqif_add.
Qed.

Lemma leq_sum I r (P : pred I) (E1 E2 : I -> nat) :
    (forall i, P i -> E1 i <= E2 i) ->
  \sum_(i <- r | P i) E1 i <= \sum_(i <- r | P i) E2 i.
Proof. by move=> leE12; elim/big_ind2: _ => // m1 m2 n1 n2; apply: leq_add. Qed.

Lemma sumnB I r (P : pred I) (E1 E2 : I -> nat) :
     (forall i, P i -> E1 i <= E2 i) ->
  \sum_(i <- r | P i) (E2 i - E1 i) =
  \sum_(i <- r | P i) E2 i - \sum_(i <- r | P i) E1 i.
Proof. by move=> /(_ _ _)/subnK-/(eq_bigr _)<-; rewrite big_split addnK. Qed.

Lemma sum_nat_eq0 (I : finType) (P : pred I) (E : I -> nat) :
  (\sum_(i | P i) E i == 0)%N = [forall (i | P i), E i == 0%N].
Proof. by rewrite eq_sym -(@leqif_sum I P _ (fun _ => 0%N) E) ?big1_eq. Qed.

Lemma prodn_cond_gt0 I r (P : pred I) F :
  (forall i, P i -> 0 < F i) -> 0 < \prod_(i <- r | P i) F i.
Proof. by move=> Fpos; elim/big_ind: _ => // n1 n2; rewrite muln_gt0 => ->. Qed.

Lemma prodn_gt0 I r (P : pred I) F :
  (forall i, 0 < F i) -> 0 < \prod_(i <- r | P i) F i.
Proof. by move=> Fpos; apply: prodn_cond_gt0. Qed.

Lemma leq_bigmax_cond (I : finType) (P : pred I) F i0 :
  P i0 -> F i0 <= \max_(i | P i) F i.
Proof. by move=> Pi0; rewrite (bigD1 i0) ?leq_maxl. Qed.
Arguments leq_bigmax_cond [I P F].

Lemma leq_bigmax (I : finType) F (i0 : I) : F i0 <= \max_i F i.
Proof. exact: leq_bigmax_cond. Qed.
Arguments leq_bigmax [I F].

Lemma bigmax_leqP (I : finType) (P : pred I) m F :
  reflect (forall i, P i -> F i <= m) (\max_(i | P i) F i <= m).
Proof.
apply: (iffP idP) => leFm => [i Pi|].
  by apply: leq_trans leFm; apply: leq_bigmax_cond.
by elim/big_ind: _ => // m1 m2; rewrite geq_max => ->.
Qed.

Lemma bigmax_sup (I : finType) i0 (P : pred I) m F :
  P i0 -> m <= F i0 -> m <= \max_(i | P i) F i.
Proof. by move=> Pi0 le_m_Fi0; apply: leq_trans (leq_bigmax_cond i0 Pi0). Qed.
Arguments bigmax_sup [I] i0 [P m F].

Lemma bigmax_eq_arg (I : finType) i0 (P : pred I) F :
  P i0 -> \max_(i | P i) F i = F [arg max_(i > i0 | P i) F i].
Proof.
move=> Pi0; case: arg_maxnP => //= i Pi maxFi.
by apply/eqP; rewrite eqn_leq leq_bigmax_cond // andbT; apply/bigmax_leqP.
Qed.
Arguments bigmax_eq_arg [I] i0 [P F].

Lemma eq_bigmax_cond (I : finType) (A : pred I) F :
  #|A| > 0 -> {i0 | i0 \in A & \max_(i in A) F i = F i0}.
Proof.
case: (pickP A) => [i0 Ai0 _ | ]; last by move/eq_card0->.
by exists [arg max_(i > i0 in A) F i]; [case: arg_maxnP | apply: bigmax_eq_arg].
Qed.

Lemma eq_bigmax (I : finType) F : #|I| > 0 -> {i0 : I | \max_i F i = F i0}.
Proof. by case/(eq_bigmax_cond F) => x _ ->; exists x. Qed.

Lemma expn_sum m I r (P : pred I) F :
  (m ^ (\sum_(i <- r | P i) F i) = \prod_(i <- r | P i) m ^ F i)%N.
Proof. exact: (big_morph _ (expnD m)). Qed.

Lemma dvdn_biglcmP (I : finType) (P : pred I) F m :
  reflect (forall i, P i -> F i %| m) (\big[lcmn/1%N]_(i | P i) F i %| m).
Proof.
apply: (iffP idP) => [dvFm i Pi | dvFm].
  by rewrite (bigD1 i) // dvdn_lcm in dvFm; case/andP: dvFm.
by elim/big_ind: _ => // p q p_m; rewrite dvdn_lcm p_m.
Qed.

Lemma biglcmn_sup (I : finType) i0 (P : pred I) F m :
  P i0 -> m %| F i0 -> m %| \big[lcmn/1%N]_(i | P i) F i.
Proof.
by move=> Pi0 m_Fi0; rewrite (dvdn_trans m_Fi0) // (bigD1 i0) ?dvdn_lcml.
Qed.
Arguments biglcmn_sup [I] i0 [P F m].

Lemma dvdn_biggcdP (I : finType) (P : pred I) F m :
  reflect (forall i, P i -> m %| F i) (m %| \big[gcdn/0]_(i | P i) F i).
Proof.
apply: (iffP idP) => [dvmF i Pi | dvmF].
  by rewrite (bigD1 i) // dvdn_gcd in dvmF; case/andP: dvmF.
by elim/big_ind: _ => // p q m_p; rewrite dvdn_gcd m_p.
Qed.

Lemma biggcdn_inf (I : finType) i0 (P : pred I) F m :
  P i0 -> F i0 %| m -> \big[gcdn/0]_(i | P i) F i %| m.
Proof. by move=> Pi0; apply: dvdn_trans; rewrite (bigD1 i0) ?dvdn_gcdl. Qed.
Arguments biggcdn_inf [I] i0 [P F m].

#[deprecated(since="mathcomp 1.12.0", note="Use big_enumP instead.")]
Notation filter_index_enum := deprecated_filter_index_enum (only parsing).
#[deprecated(since="mathcomp 1.12.0", note="Use big_rmcond_in instead.")]
Notation big_rmcond := big_rmcond_in (only parsing).
#[deprecated(since="mathcomp 1.12.0", note="Use big_rmcond_in instead.")]
Notation big_uncond_in := big_rmcond_in (only parsing).

(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice.
From mathcomp Require Import fintype div path tuple bigop prime finset.

(******************************************************************************)
(* This file defines the main interface for finite groups :                   *)
(*          finGroupType == the structure for finite types with a group law.  *)
(*           {group gT}  == type of groups with elements of type gT.          *)
(*      baseFinGroupType == the structure for finite types with a monoid law  *)
(*                          and an involutive antimorphism; finGroupType is   *)
(*                          derived from baseFinGroupType (via a telescope).  *)
(*    FinGroupType mulVg == the finGroupType structure for an existing        *)
(*                          baseFinGroupType structure, built from a proof of *)
(*                          the left inverse group axiom for that structure's *)
(*                          operations.                                       *)
(*  BaseFinGroupType bgm == the baseFingroupType structure built by packaging *)
(*                          bgm : FinGroup.mixin_of T for a type T with an    *)
(*                          existing finType structure.                       *)
(* FinGroup.BaseMixin mulA mul1x invK invM ==                                 *)
(*                          the mixin for a baseFinGroupType structure, built *)
(*                          from proofs of the baseFinGroupType axioms.       *)
(* FinGroup.Mixin mulA mul1x mulVg ==                                         *)
(*                          the mixin for a baseFinGroupType structure, built *)
(*                          from proofs of the group axioms.                  *)
(* [baseFinGroupType of T] == a clone of an existing baseFinGroupType         *)
(*                          structure on T, for T (the existing structure     *)
(*                          might be for some delta-expansion of T).          *)
(*   [finGroupType of T] == a clone of an existing finGroupType structure on  *)
(*                          T, for the canonical baseFinGroupType structure   *)
(*                          of T (the existing structure might be for the     *)
(*                          baseFinGroupType of some delta-expansion of T).   *)
(*          [group of G] == a clone for an existing {group gT} structure on   *)
(*                          G : {set gT} (the existing structure might be for *)
(*                          some delta-expansion of G).                       *)
(* If gT implements finGroupType, then we can form {set gT}, the type of      *)
(* finite sets with elements of type gT (as finGroupType extends finType).    *)
(* The group law extends pointwise to {set gT}, which thus implements a sub-  *)
(* interface baseFinGroupType of finGroupType. To be consistent with the      *)
(* predType interface, this is done by coercion to FinGroup.arg_sort, an      *)
(* alias for FinGroup.sort. Accordingly, all pointwise group operations below *)
(* have arguments of type (FinGroup.arg_sort) gT and return results of type   *)
(* FinGroup.sort gT.                                                          *)
(*   The notations below are declared in two scopes:                          *)
(*      group_scope (delimiter %g) for point operations and set constructs.   *)
(*      Group_scope (delimiter %G) for explicit {group gT} structures.        *)
(* These scopes should not be opened globally, although group_scope is often  *)
(* opened locally in group-theory files (via Import GroupScope).              *)
(*   As {group gT} is both a subtype and an interface structure for {set gT}, *)
(* the fact that a given G : {set gT} is a group can (and usually should) be  *)
(* inferred by type inference with canonical structures. This means that all  *)
(* `group' constructions (e.g., the normaliser 'N_G(H)) actually define sets  *)
(* with a canonical {group gT} structure; the %G delimiter can be used to     *)
(* specify the actual {group gT} structure (e.g., 'N_G(H)%G).                 *)
(*  Operations on elements of a group:                                        *)
(*                x * y == the group product of x and y.                      *)
(*               x ^+ n == the nth power of x, i.e., x * ... * x (n times).   *)
(*                 x^-1 == the group inverse of x.                            *)
(*               x ^- n == the inverse of x ^+ n (notation for (x ^+ n)^-1).  *)
(*                    1 == the unit element.                                  *)
(*                x ^ y == the conjugate of x by y (i.e., y^-1 * (x * y)).    *)
(*            [~ x, y]  == the commutator of x and y (i.e., x^-1 * x ^ y).    *)
(*     [~ x1, ..., xn]  == the commutator of x1, ..., xn (associating left).  *)
(*    \prod_(i ...) x i == the product of the x i (order-sensitive).          *)
(*         commute x y  <-> x and y commute.                                  *)
(*      centralises x A <-> x centralises A.                                  *)
(*                'C[x] == the set of elements that commute with x.           *)
(*              'C_G[x] == the set of elements of G that commute with x.      *)
(*                <[x]> == the cyclic subgroup generated by the element x.    *)
(*                 #[x] == the order of the element x, i.e., #|<[x]>|.        *)
(*  Operations on subsets/subgroups of a finite group:                        *)
(*                H * G == {xy | x \in H, y \in G}.                           *)
(*   1 or [1] or [1 gT] == the unit group.                                    *)
(*          [set: gT]%G == the group of all x : gT (in Group_scope).          *)
(*          group_set G == G contains 1 and is closed under binary product;   *)
(*                         this is the characteristic property of the         *)
(*                         {group gT} subtype of {set gT}.                    *)
(*             [subg G] == the subtype, set, or group of all x \in G: this    *)
(*                         notation is defined simultaneously in %type, %g    *)
(*                         and %G scopes, and G must denote a {group gT}      *)
(*                         structure (G is in the %G scope).                  *)
(*          subg, sgval == the projection into and injection from [subg G].   *)
(*                  H^# == the set H minus the unit element.                  *)
(*               repr H == some element of H if 1 \notin H != set0, else 1.   *)
(*                         (repr is defined over sets of a baseFinGroupType,  *)
(*                         so it can be used, e.g., to pick right cosets.)    *)
(*               x *: H == left coset of H by x.                              *)
(*          lcosets H G == the set of the left cosets of H by elements of G.  *)
(*               H :* x == right coset of H by x.                             *)
(*          rcosets H G == the set of the right cosets of H by elements of G. *)
(*             #|G : H| == the index of H in G, i.e., #|rcosets G H|.         *)
(*               H :^ x == the conjugate of H by x.                           *)
(*               x ^: H == the conjugate class of x in H.                     *)
(*            classes G == the set of all conjugate classes of G.             *)
(*              G :^: H == {G :^ x | x \in H}.                                *)
(*    class_support G H == {x ^ y | x \in G, y \in H}.                        *)
(*        commg_set G H == {[~ x, y] | x \in G, y \in H}; NOT the commutator! *)
(*                <<H>> == the subgroup generated by the set H.               *)
(*            [~: G, H] == the commmutator subgroup of G and H, i.e.,         *)
(*                         <<commg_set G H>>>.                                *)
(*     [~: H1, ..., Hn] == commutator subgroup of H1, ..., Hn (left assoc.).  *)
(*              H <*> G == the subgroup generated by sets H and G (H join G). *)
(*            (H * G)%G == the join of G H : {group gT} (convertible, but not *)
(*                         identical to (G <*> H)%G).                         *)
(* (\prod_(i ...) H i)%G == the group generated by the H i.                   *)
(* {in G, centralised H} <-> G centralises H.                                 *)
(* {in G, normalised H} <-> G normalises H.                                   *)
(*                      <-> forall x, x \in G -> H :^ x = H.                  *)
(*                'N(H) == the normaliser of H.                               *)
(*              'N_G(H) == the normaliser of H in G.                          *)
(*               H <| G <=> H is a normal subgroup of G.                      *)
(*                'C(H) == the centraliser of H.                              *)
(*              'C_G(H) == the centraliser of H in G.                         *)
(*            gcore H G == the largest subgroup of H normalised by G.         *)
(*                         If H is a subgroup of G, this is the largest       *)
(*                         normal subgroup of G contained in H).              *)
(*            abelian H <=> H is abelian.                                     *)
(*          subgroups G == the set of subgroups of G, i.e., the set of all    *)
(*                         H : {group gT} such that H \subset G.              *)
(* In the notation below G is a variable that is bound in P.                  *)
(*          [max G | P] <=> G is the largest group such that P holds.         *)
(*     [max H of G | P] <=> H is the largest group G such that P holds.       *)
(*      [max G | P & Q] := [max G | P && Q], likewise [max H of G | P & Q].   *)
(*          [min G | P] <=> G is the smallest group such that P holds.        *)
(*      [min G | P & Q] := [min G | P && Q], likewise [min H of G | P & Q].   *)
(*     [min H of G | P] <=> H is the smallest group G such that P holds.      *)
(* In addition to the generic suffixes described in ssrbool.v and finset.v,   *)
(* we associate the following suffixes to group operations:                   *)
(*   1 - identity element, as in group1 : 1 \in G.                            *)
(*   M - multiplication, as is invMg : (x * y)^-1 = y^-1 * x^-1.              *)
(*       Also nat multiplication, for expgM : x ^+ (m * n) = x ^+ m ^+ n.     *)
(*   D - (nat) addition, for expgD : x ^+ (m + n) = x ^+ m * x ^+ n.          *)
(*   V - inverse, as in mulgV : x * x^-1 = 1.                                 *)
(*   X - exponentiation, as in conjXg : (x ^+ n) ^ y = (x ^ y) ^+ n.          *)
(*   J - conjugation, as in orderJ : #[x ^ y] = #[x].                         *)
(*   R - commutator, as in conjRg : [~ x, y] ^ z = [~ x ^ z, y ^ z].          *)
(*   Y - join, as in centY : 'C(G <*> H) = 'C(G) :&: 'C(H).                   *)
(* We sometimes prefix these with an `s' to indicate a set-lifted operation,  *)
(* e.g., conjsMg : (A * B) :^ x = A :^ x * B :^ x.                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope group_scope.
Declare Scope Group_scope.

Delimit Scope group_scope with g.
Delimit Scope Group_scope with G.

(* This module can be imported to open the scope for group element *)
(* operations locally to a file, without exporting the Open to     *)
(* clients of that file (as Open would do).                        *)
Module GroupScope.
Open Scope group_scope.
End GroupScope.
Import GroupScope.

(* These are the operation notations introduced by this file. *)
Reserved Notation "[ ~ x1 , x2 , .. , xn ]" (at level 0,
  format  "'[ ' [ ~  x1 , '/'  x2 , '/'  .. , '/'  xn ] ']'").
Reserved Notation "[ 1 gT ]" (at level 0, format "[ 1  gT ]").
Reserved Notation "[ 1 ]" (at level 0, format "[ 1 ]").
Reserved Notation "[ 'subg' G ]" (at level 0, format "[ 'subg'  G ]").
Reserved Notation "A ^#" (at level 2, format "A ^#").
Reserved Notation "A :^ x" (at level 35, right associativity).
Reserved Notation "x ^: B" (at level 35, right associativity).
Reserved Notation "A :^: B" (at level 35, right associativity).
Reserved Notation "#| B : A |" (at level 0, B, A at level 99,
  format "#| B  :  A |").
Reserved Notation "''N' ( A )" (at level 8, format "''N' ( A )").
Reserved Notation "''N_' G ( A )" (at level 8, G at level 2,
  format "''N_' G ( A )").
Reserved Notation "A <| B" (at level 70, no associativity).
Reserved Notation "A <*> B" (at level 40, left associativity).
Reserved Notation "[ ~: A1 , A2 , .. , An ]" (at level 0,
  format "[ ~: '['  A1 , '/'  A2 , '/'  .. , '/'  An ']' ]").
Reserved Notation "[ 'max' A 'of' G | gP ]" (at level 0,
  format "[ '[hv' 'max'  A  'of'  G '/ '  |  gP ']' ]").
Reserved Notation "[ 'max' G | gP ]" (at level 0,
  format "[ '[hv' 'max'  G '/ '  |  gP ']' ]").
Reserved Notation "[ 'max' A 'of' G | gP & gQ ]" (at level 0,
  format "[ '[hv' 'max'  A  'of'  G '/ '  |  gP '/ '  &  gQ ']' ]").
Reserved Notation "[ 'max' G | gP & gQ ]" (at level 0,
  format "[ '[hv' 'max'  G '/ '  |  gP '/ '  &  gQ ']' ]").
Reserved Notation "[ 'min' A 'of' G | gP ]" (at level 0,
  format "[ '[hv' 'min'  A  'of'  G '/ '  |  gP ']' ]").
Reserved Notation "[ 'min' G | gP ]" (at level 0,
  format "[ '[hv' 'min'  G '/ '  |  gP ']' ]").
Reserved Notation "[ 'min' A 'of' G | gP & gQ ]" (at level 0,
  format "[ '[hv' 'min'  A  'of'  G '/ '  |  gP '/ '  &  gQ ']' ]").
Reserved Notation "[ 'min' G | gP & gQ ]" (at level 0,
  format "[ '[hv' 'min'  G '/ '  |  gP '/ '  &  gQ ']' ]").

(* We split the group axiomatisation in two. We define a  *)
(* class of "base groups", which are basically monoids    *)
(* with an involutive antimorphism, from which we derive  *)
(* the class of groups proper. This allows us to reuse    *)
(* much of the group notation and algebraic axioms for    *)
(* group subsets, by defining a base group class on them. *)
(*   We use class/mixins here rather than telescopes to   *)
(* be able to interoperate with the type coercions.       *)
(* Another potential benefit (not exploited here) would   *)
(* be to define a class for infinite groups, which could  *)
(* share all of the algebraic laws.                       *)

HB.mixin Record isMulBaseGroup G := {
  mulg_subdef : G -> G -> G;
  oneg_subdef : G;
  invg_subdef : G -> G;
  mulgA_subproof : associative mulg_subdef ;
  mul1g_subproof : left_id oneg_subdef  mulg_subdef ;
  invgK_subproof : involutive invg_subdef ;
  invMg_subproof : {morph invg_subdef  : x y / mulg_subdef  x y >-> mulg_subdef  y x}
}.

(* We want to use sort as a coercion class, both to infer         *)
(* argument scopes properly, and to allow groups and cosets to    *)
(* coerce to the base group of group subsets.                     *)
(*   However, the return type of group operations should NOT be a *)
(* coercion class, since this would trump the real (head-normal)  *)
(* coercion class for concrete group types, thus spoiling the     *)
(* coercion of A * B to pred_sort in x \in A * B, or rho * tau to *)
(* ffun and Funclass in (rho * tau) x, when rho tau : perm T.     *)
(*   Therefore we define an alias of sort for argument types, and *)
(* make it the default coercion FinGroup.base_type >-> Sortclass  *)
(* so that arguments of a functions whose parameters are of type, *)
(* say, gT : finGroupType, can be coerced to the coercion class   *)
(* of arg_sort. Care should be taken, however, to declare the     *)
(* return type of functions and operators as FinGroup.sort gT     *)
(* rather than gT, e.g., mulg : gT -> gT -> FinGroup.sort gT.     *)
(* Note that since we do this here and in quotient.v for all the  *)
(* basic functions, the inferred return type should generally be  *)
(* correct.                                                       *)

#[arg_sort, short(type="baseFinGroupType")]
HB.structure Definition BaseFinGroup := { G of isMulBaseGroup G & Finite G }.

Module BaseFinGroupExports.
Bind Scope group_scope with BaseFinGroup.arg_sort.
Bind Scope group_scope with BaseFinGroup.sort.
Notation "[ 'baseFinGroupType' 'of' T ]" := (@BaseFinGroup.clone T _)
  (at level 0, format "[ 'baseFinGroupType'  'of'  T ]") : form_scope.
End BaseFinGroupExports.
HB.export BaseFinGroupExports.

Module Notations.
Section ElementOps.

Variable T : baseFinGroupType.
Notation rT := (BaseFinGroup.sort T).

Definition oneg : rT := Eval unfold oneg_subdef in @oneg_subdef T.
Definition mulg : T -> T -> rT := Eval unfold mulg_subdef in @mulg_subdef T.
Definition invg : T -> rT := Eval unfold invg_subdef in @invg_subdef T.
Definition expgn_rec (x : T) n : rT := iterop n mulg x oneg.

End ElementOps.

Definition expgn := nosimpl expgn_rec.

Notation "1" := (@oneg _) : group_scope.
Notation "x1 * x2" := (mulg x1 x2) : group_scope.
Notation "x ^-1" := (invg x) : group_scope.
Notation "x ^+ n" := (expgn x n) : group_scope.
Notation "x ^- n" := (x ^+ n)^-1 : group_scope.
End Notations.
HB.export Notations.

HB.mixin Record BaseFinGroup_isGroup G of BaseFinGroup G := {
  mulVg_subproof :
    left_inverse (@oneg [the BaseFinGroup.type of G]) (@invg _) (@mulg _)
}.

#[short(type="finGroupType")]
HB.structure Definition FinGroup :=
  { G of BaseFinGroup_isGroup G & BaseFinGroup G }.

Module FinGroupExports.
Notation "[ 'finGroupType' 'of' T ]" := (@FinGroup.clone T _)
  (at level 0, format "[ 'finGroupType'  'of'  T ]") : form_scope.
Bind Scope group_scope with FinGroup.sort.
End FinGroupExports.
HB.export FinGroupExports.

HB.factory Record isMulGroup G of Finite G := {
  mulg : G -> G -> G;
  oneg : G;
  invg : G -> G;
  mulgA : associative mulg;
  mul1g : left_id oneg mulg;
  mulVg : left_inverse oneg invg mulg;
}.

HB.builders Context G of isMulGroup G.

Notation "1" := oneg.
Infix "*" := mulg.
Notation "x ^-1" := (invg x).

Lemma mk_invgK : involutive invg.
Proof.
have mulV21 x: x^-1^-1 * 1 = x by rewrite -(mulVg x) mulgA mulVg mul1g.
by move=> x; rewrite -[_ ^-1]mulV21 -(mul1g 1) mulgA !mulV21.
Qed.

Lemma mk_invMg : {morph invg : x y / x * y >-> y * x}.
Proof.
have mulgV x: x * x^-1 = 1 by rewrite -{1}[x]mk_invgK mulVg.
move=> x y /=; rewrite -[y^-1 * _]mul1g -(mulVg (x * y)) -2!mulgA (mulgA y).
by rewrite mulgV mul1g mulgV -(mulgV (x * y)) mulgA mulVg mul1g.
Qed.

HB.instance Definition _ := 
  isMulBaseGroup.Build G mulgA mul1g mk_invgK mk_invMg.
HB.instance Definition _ := BaseFinGroup_isGroup.Build G mulVg.

HB.end.

#[compress_coercions]
HB.instance Definition _ (T : baseFinGroupType) :
    Finite (BaseFinGroup.arg_sort T) :=
  Finite.class [the finType of (T : Type)].

(* Arguments of conjg are restricted to true groups to avoid an *)
(* improper interpretation of A ^ B with A and B sets, namely:  *)
(*       {x^-1 * (y * z) | y \in A, x, z \in B}                 *)
Definition conjg (T : finGroupType) (x y : T) := y^-1 * (x * y).
Notation "x1 ^ x2" := (conjg x1 x2) : group_scope.

Definition commg (T : finGroupType) (x y : T) := x^-1 * x ^ y.
Notation "[ ~ x1 , x2 , .. , xn ]" := (commg .. (commg x1 x2) .. xn)
  : group_scope.

Prenex Implicits mulg invg expgn conjg commg.

Notation "\prod_ ( i <- r | P ) F" :=
  (\big[mulg/1]_(i <- r | P%B) F%g) : group_scope.
Notation "\prod_ ( i <- r ) F" :=
  (\big[mulg/1]_(i <- r) F%g) : group_scope.
Notation "\prod_ ( m <= i < n | P ) F" :=
  (\big[mulg/1]_(m <= i < n | P%B) F%g) : group_scope.
Notation "\prod_ ( m <= i < n ) F" :=
  (\big[mulg/1]_(m <= i < n) F%g) : group_scope.
Notation "\prod_ ( i | P ) F" :=
  (\big[mulg/1]_(i | P%B) F%g) : group_scope.
Notation "\prod_ i F" :=
  (\big[mulg/1]_i F%g) : group_scope.
Notation "\prod_ ( i : t | P ) F" :=
  (\big[mulg/1]_(i : t | P%B) F%g) (only parsing) : group_scope.
Notation "\prod_ ( i : t ) F" :=
  (\big[mulg/1]_(i : t) F%g) (only parsing) : group_scope.
Notation "\prod_ ( i < n | P ) F" :=
  (\big[mulg/1]_(i < n | P%B) F%g) : group_scope.
Notation "\prod_ ( i < n ) F" :=
  (\big[mulg/1]_(i < n) F%g) : group_scope.
Notation "\prod_ ( i 'in' A | P ) F" :=
  (\big[mulg/1]_(i in A | P%B) F%g) : group_scope.
Notation "\prod_ ( i 'in' A ) F" :=
  (\big[mulg/1]_(i in A) F%g) : group_scope.

Section PreGroupIdentities.

Variable T : baseFinGroupType.
Implicit Types x y z : T.
Local Notation mulgT := (@mulg T).

Lemma mulgA : associative mulgT.  Proof. exact: mulgA_subproof. Qed.
Lemma mul1g : left_id 1 mulgT.  Proof. exact: mul1g_subproof. Qed.
Lemma invgK : @involutive T invg. Proof. exact: invgK_subproof. Qed.
Lemma invMg x y : (x * y)^-1 = y^-1 * x^-1. Proof. exact: invMg_subproof. Qed.

Lemma invg_inj : @injective T T invg. Proof. exact: can_inj invgK. Qed.

Lemma eq_invg_sym x y : (x^-1 == y) = (x == y^-1).
Proof. by apply: (inv_eq invgK). Qed.

Lemma invg1 : 1^-1 = 1 :> T.
Proof. by apply: invg_inj; rewrite -{1}[1^-1]mul1g invMg invgK mul1g. Qed.

Lemma eq_invg1 x : (x^-1 == 1) = (x == 1).
Proof. by rewrite eq_invg_sym invg1. Qed.

Lemma mulg1 : right_id 1 mulgT.
Proof. by move=> x; apply: invg_inj; rewrite invMg invg1 mul1g. Qed.

HB.instance Definition _ := Monoid.isLaw.Build T 1 mulgT mulgA mul1g mulg1.

Lemma expgnE x n : x ^+ n = expgn_rec x n. Proof. by []. Qed.

Lemma expg0 x : x ^+ 0 = 1. Proof. by []. Qed.
Lemma expg1 x : x ^+ 1 = x. Proof. by []. Qed.

Lemma expgS x n : x ^+ n.+1 = x * x ^+ n.
Proof. by case: n => //; rewrite mulg1. Qed.

Lemma expg1n n : 1 ^+ n = 1 :> T.
Proof. by elim: n => // n IHn; rewrite expgS mul1g. Qed.

Lemma expgD x n m : x ^+ (n + m) = x ^+ n * x ^+ m.
Proof. by elim: n => [|n IHn]; rewrite ?mul1g // !expgS IHn mulgA. Qed.

Lemma expgSr x n : x ^+ n.+1 = x ^+ n * x.
Proof. by rewrite -addn1 expgD expg1. Qed.

Lemma expgM x n m : x ^+ (n * m) = x ^+ n ^+ m.
Proof.
elim: m => [|m IHm]; first by rewrite muln0 expg0.
by rewrite mulnS expgD IHm expgS.
Qed.

Lemma expgAC x m n : x ^+ m ^+ n = x ^+ n ^+ m.
Proof. by rewrite -!expgM mulnC. Qed.

Definition commute x y := x * y = y * x.

Lemma commute_refl x : commute x x.
Proof. by []. Qed.

Lemma commute_sym x y : commute x y -> commute y x.
Proof. by []. Qed.

Lemma commute1 x : commute x 1.
Proof. by rewrite /commute mulg1 mul1g. Qed.

Lemma commuteM x y z : commute x y ->  commute x z ->  commute x (y * z).
Proof. by move=> cxy cxz; rewrite /commute -mulgA -cxz !mulgA cxy. Qed.

Lemma commuteX x y n : commute x y ->  commute x (y ^+ n).
Proof.
by move=> cxy; case: n; [apply: commute1 | elim=> // n; apply: commuteM].
Qed.

Lemma commuteX2 x y m n : commute x y -> commute (x ^+ m) (y ^+ n).
Proof. by move=> cxy; apply/commuteX/commute_sym/commuteX. Qed.

Lemma expgVn x n : x^-1 ^+ n = x ^- n.
Proof. by elim: n => [|n IHn]; rewrite ?invg1 // expgSr expgS invMg IHn. Qed.

Lemma expgMn x y n : commute x y -> (x * y) ^+ n  = x ^+ n * y ^+ n.
Proof.
move=> cxy; elim: n => [|n IHn]; first by rewrite mulg1.
by rewrite !expgS IHn -mulgA (mulgA y) (commuteX _ (commute_sym cxy)) !mulgA.
Qed.

End PreGroupIdentities.

#[global] Hint Resolve commute1 : core.
Arguments invg_inj {T} [x1 x2].
Prenex Implicits commute invgK.

Section GroupIdentities.

Variable T : finGroupType.
Implicit Types x y z : T.
Local Notation mulgT := (@mulg T).

Lemma mulVg : left_inverse 1 invg mulgT. Proof. exact: mulVg_subproof. Qed.

Lemma mulgV : right_inverse 1 invg mulgT.
Proof. by move=> x; rewrite -{1}(invgK x) mulVg. Qed.

Lemma mulKg : left_loop invg mulgT.
Proof. by move=> x y; rewrite mulgA mulVg mul1g. Qed.

Lemma mulKVg : rev_left_loop invg mulgT.
Proof. by move=> x y; rewrite mulgA mulgV mul1g. Qed.

Lemma mulgI : right_injective mulgT.
Proof. by move=> x; apply: can_inj (mulKg x). Qed.

Lemma mulgK : right_loop invg mulgT.
Proof. by move=> x y; rewrite -mulgA mulgV mulg1. Qed.

Lemma mulgKV : rev_right_loop invg mulgT.
Proof. by move=> x y; rewrite -mulgA mulVg mulg1. Qed.

Lemma mulIg : left_injective mulgT.
Proof. by move=> x; apply: can_inj (mulgK x). Qed.

Lemma eq_invg_mul x y : (x^-1 == y :> T) = (x * y == 1 :> T).
Proof. by rewrite -(inj_eq (@mulgI x)) mulgV eq_sym. Qed.

Lemma eq_mulgV1 x y : (x == y) = (x * y^-1 == 1 :> T).
Proof. by rewrite -(inj_eq invg_inj) eq_invg_mul. Qed.

Lemma eq_mulVg1 x y : (x == y) = (x^-1 * y == 1 :> T).
Proof. by rewrite -eq_invg_mul invgK. Qed.

Lemma commuteV x y : commute x y -> commute x y^-1.
Proof. by move=> cxy; apply: (@mulIg y); rewrite mulgKV -mulgA cxy mulKg. Qed.

Lemma conjgE x y : x ^ y = y^-1 * (x * y). Proof. by []. Qed.

Lemma conjgC x y : x * y = y * x ^ y.
Proof. by rewrite mulKVg. Qed.

Lemma conjgCV x y : x * y = y ^ x^-1 * x.
Proof. by rewrite -mulgA mulgKV invgK. Qed.

Lemma conjg1 x : x ^ 1 = x.
Proof. by rewrite conjgE commute1 mulKg. Qed.

Lemma conj1g x : 1 ^ x = 1.
Proof. by rewrite conjgE mul1g mulVg. Qed.

Lemma conjMg x y z : (x * y) ^ z = x ^ z * y ^ z.
Proof. by rewrite !conjgE !mulgA mulgK. Qed.

Lemma conjgM x y z : x ^ (y * z) = (x ^ y) ^ z.
Proof. by rewrite !conjgE invMg !mulgA. Qed.

Lemma conjVg x y : x^-1 ^ y = (x ^ y)^-1.
Proof. by rewrite !conjgE !invMg invgK mulgA. Qed.

Lemma conjJg x y z : (x ^ y) ^ z = (x ^ z) ^ y ^ z.
Proof. by rewrite 2!conjMg conjVg. Qed.

Lemma conjXg x y n : (x ^+ n) ^ y = (x ^ y) ^+ n.
Proof. by elim: n => [|n IHn]; rewrite ?conj1g // !expgS conjMg IHn. Qed.

Lemma conjgK : @right_loop T T invg conjg.
Proof. by move=> y x; rewrite -conjgM mulgV conjg1. Qed.

Lemma conjgKV : @rev_right_loop T T invg conjg.
Proof. by move=> y x; rewrite -conjgM mulVg conjg1. Qed.

Lemma conjg_inj : @left_injective T T T conjg.
Proof. by move=> y; apply: can_inj (conjgK y). Qed.

Lemma conjg_eq1 x y : (x ^ y == 1) = (x == 1).
Proof. by rewrite (canF_eq (conjgK _)) conj1g. Qed.

Lemma conjg_prod I r (P : pred I) F z :
  (\prod_(i <- r | P i) F i) ^ z = \prod_(i <- r | P i) (F i ^ z).
Proof.
by apply: (big_morph (conjg^~ z)) => [x y|]; rewrite ?conj1g ?conjMg.
Qed.

Lemma commgEl x y : [~ x, y] = x^-1 * x ^ y. Proof. by []. Qed.

Lemma commgEr x y : [~ x, y] = y^-1 ^ x * y.
Proof. by rewrite -!mulgA. Qed.

Lemma commgC x y : x * y = y * x * [~ x, y].
Proof. by rewrite -mulgA !mulKVg. Qed.

Lemma commgCV x y : x * y = [~ x^-1, y^-1] * (y * x).
Proof. by rewrite commgEl !mulgA !invgK !mulgKV. Qed.

Lemma conjRg x y z : [~ x, y] ^ z = [~ x ^ z, y ^ z].
Proof. by rewrite !conjMg !conjVg. Qed.

Lemma invg_comm x y : [~ x, y]^-1 = [~ y, x].
Proof. by rewrite commgEr conjVg invMg invgK. Qed.

Lemma commgP x y : reflect (commute x y) ([~ x, y] == 1 :> T).
Proof. by rewrite [[~ x, y]]mulgA -invMg -eq_mulVg1 eq_sym; apply: eqP. Qed.

Lemma conjg_fixP x y : reflect (x ^ y = x) ([~ x, y] == 1 :> T).
Proof. by rewrite -eq_mulVg1 eq_sym; apply: eqP. Qed.

Lemma commg1_sym x y : ([~ x, y] == 1 :> T) = ([~ y, x] == 1 :> T).
Proof. by rewrite -invg_comm (inv_eq invgK) invg1. Qed.

Lemma commg1 x : [~ x, 1] = 1.
Proof. exact/eqP/commgP. Qed.

Lemma comm1g x : [~ 1, x] = 1.
Proof. by rewrite -invg_comm commg1 invg1. Qed.

Lemma commgg x : [~ x, x] = 1.
Proof. exact/eqP/commgP. Qed.

Lemma commgXg x n : [~ x, x ^+ n] = 1.
Proof. exact/eqP/commgP/commuteX. Qed.

Lemma commgVg x : [~ x, x^-1] = 1.
Proof. exact/eqP/commgP/commuteV. Qed.

Lemma commgXVg x n : [~ x, x ^- n] = 1.
Proof. exact/eqP/commgP/commuteV/commuteX. Qed.

(* Other commg identities should slot in here. *)

End GroupIdentities.

Hint Rewrite mulg1 @mul1g invg1 @mulVg mulgV (@invgK) mulgK mulgKV
             @invMg @mulgA : gsimpl.

Ltac gsimpl := autorewrite with gsimpl; try done.

Definition gsimp := (@mulg1, @mul1g, (@invg1, @invgK), (@mulgV, @mulVg)).
Definition gnorm := (gsimp, (@mulgK, @mulgKV, (@mulgA, @invMg))).

Arguments mulgI [T].
Arguments mulIg [T].
Arguments conjg_inj {T} x [x1 x2].
Arguments commgP {T x y}.
Arguments conjg_fixP {T x y}.

Section Repr.
(* Plucking a set representative. *)

Variable gT : baseFinGroupType.
Implicit Type A : {set gT}.

Definition repr A := if 1 \in A then 1 else odflt 1 [pick x in A].

Lemma mem_repr A x : x \in A -> repr A \in A.
Proof.
by rewrite /repr; case: ifP => // _; case: pickP => // A0; rewrite [x \in A]A0.
Qed.

Lemma card_mem_repr A : #|A| > 0 -> repr A \in A.
Proof. by rewrite lt0n => /existsP[x]; apply: mem_repr. Qed.

Lemma repr_set1 x : repr [set x] = x.
Proof. by apply/set1P/card_mem_repr; rewrite cards1. Qed.

Lemma repr_set0 : repr set0 = 1.
Proof. by rewrite /repr; case: pickP => [x|_] /[!inE]. Qed.

End Repr.

Arguments mem_repr [gT A].

Section BaseSetMulDef.
(* We only assume a baseFinGroupType to allow this construct to be iterated. *)
Variable gT : baseFinGroupType.
Implicit Types A B : {set gT}.

(* Set-lifted group operations. *)

Definition set_mulg A B := mulg @2: (A, B).
Definition set_invg A := invg @^-1: A.

(* The pre-group structure of group subsets. *)

Lemma set_mul1g : left_id [set 1] set_mulg.
Proof.
move=> A; apply/setP=> y; apply/imset2P/idP=> [[_ x /set1P-> Ax ->] | Ay].
  by rewrite mul1g.
by exists (1 : gT) y; rewrite ?(set11, mul1g).
Qed.

Lemma set_mulgA : associative set_mulg.
Proof.
move=> A B C; apply/setP=> y.
apply/imset2P/imset2P=> [[x1 z Ax1 /imset2P[x2 x3 Bx2 Cx3 ->] ->]| [z x3]].
  by exists (x1 * x2) x3; rewrite ?mulgA //; apply/imset2P; exists x1 x2.
case/imset2P=> x1 x2 Ax1 Bx2 -> Cx3 ->.
by exists x1 (x2 * x3); rewrite ?mulgA //; apply/imset2P; exists x2 x3.
Qed.

Lemma set_invgK : involutive set_invg.
Proof. by move=> A; apply/setP=> x; rewrite !inE invgK. Qed.

Lemma set_invgM : {morph set_invg : A B / set_mulg A B >-> set_mulg B A}.
Proof.
move=> A B; apply/setP=> z; rewrite inE.
apply/imset2P/imset2P=> [[x y Ax By /(canRL invgK)->] | [y x]].
  by exists y^-1 x^-1; rewrite ?invMg // inE invgK.
by rewrite !inE => By1 Ax1 ->; exists x^-1 y^-1; rewrite ?invMg.
Qed.

HB.instance Definition set_base_group := isMulBaseGroup.Build (set_type gT)
  set_mulgA set_mul1g set_invgK set_invgM.
HB.instance Definition _ : isMulBaseGroup {set gT} := set_base_group.

End BaseSetMulDef.

(* Time to open the bag of dirty tricks. When we define groups down below *)
(* as a subtype of {set gT}, we need them to be able to coerce to sets in *)
(* both set-style contexts (x \in G) and monoid-style contexts (G * H),   *)
(* and we need the coercion function to be EXACTLY the structure          *)
(* projection in BOTH cases -- otherwise the canonical unification breaks.*)
(*   Alas, Coq doesn't let us use the same coercion function twice, even  *)
(* when the targets are convertible. Our workaround (ab)uses the module   *)
(* system to declare two different identity coercions on an alias class.  *)

Module GroupSet.
Definition sort (gT : baseFinGroupType) := {set gT}.
End GroupSet.
Identity Coercion GroupSet_of_sort : GroupSet.sort >-> set_of.

Module Type GroupSetBaseGroupSig.
Definition sort (gT : baseFinGroupType) :=
  BaseFinGroup.arg_sort [the baseFinGroupType of {set gT}].
End GroupSetBaseGroupSig.

Module MakeGroupSetBaseGroup (Gset_base : GroupSetBaseGroupSig).
Identity Coercion of_sort : Gset_base.sort >-> BaseFinGroup.arg_sort.
End MakeGroupSetBaseGroup.

Module Export GroupSetBaseGroup := MakeGroupSetBaseGroup GroupSet.
HB.instance Definition _ gT : Finite (GroupSet.sort gT) :=
   Finite.class [the finType of {set gT}].

Section GroupSetMulDef.
(* Some of these constructs could be defined on a baseFinGroupType. *)
(* We restrict them to proper finGroupType because we only develop  *)
(* the theory for that case.                                        *)
Variable gT : finGroupType.
Implicit Types A B : {set gT}.
Implicit Type x y : gT.

Definition lcoset A x := mulg x @: A.
Definition rcoset A x := mulg^~ x @: A.
Definition lcosets A B := lcoset A @: B.
Definition rcosets A B := rcoset A @: B.
Definition indexg B A := #|rcosets A B|.

Definition conjugate A x := conjg^~ x @: A.
Definition conjugates A B := conjugate A @: B.
Definition class x B := conjg x @: B.
Definition classes A := class^~ A @: A.
Definition class_support A B := conjg @2: (A, B).

Definition commg_set A B := commg @2: (A, B).

(* These will only be used later, but are defined here so that we can *)
(* keep all the Notation together.                                    *)
Definition normaliser A := [set x | conjugate A x \subset A].
Definition centraliser A := \bigcap_(x in A) normaliser [set x].
Definition abelian A := A \subset centraliser A.
Definition normal A B := (A \subset B) && (B \subset normaliser A).

(* "normalised" and "centralise[s|d]" are intended to be used with   *)
(* the {in ...} form, as in abelian below.                           *)
Definition normalised A := forall x, conjugate A x = A.
Definition centralises x A := forall y, y \in A -> commute x y.
Definition centralised A := forall x, centralises x A.

End GroupSetMulDef.

Arguments lcoset _ _%g _%g.
Arguments rcoset _ _%g _%g.
Arguments rcosets _ _%g _%g.
Arguments lcosets _ _%g _%g.
Arguments indexg _ _%g _%g.
Arguments conjugate _ _%g _%g.
Arguments conjugates _ _%g _%g.
Arguments class _ _%g _%g.
Arguments classes _ _%g.
Arguments class_support _ _%g _%g.
Arguments commg_set _ _%g _%g.
Arguments normaliser _ _%g.
Arguments centraliser _ _%g.
Arguments abelian _ _%g.
Arguments normal _ _%g _%g.
Arguments normalised _ _%g.
Arguments centralises _ _%g _%g.
Arguments centralised _ _%g.

Notation "[ 1 gT ]" := (1 : {set gT}) : group_scope.
Notation "[ 1 ]" := [1 FinGroup.sort _] : group_scope.

Notation "A ^#" := (A :\ 1) : group_scope.

Notation "x *: A" := ([set x%g] * A) : group_scope.
Notation "A :* x" := (A * [set x%g]) : group_scope.
Notation "A :^ x" := (conjugate A x) : group_scope.
Notation "x ^: B" := (class x B) : group_scope.
Notation "A :^: B" := (conjugates A B) : group_scope.

Notation "#| B : A |" := (indexg B A) : group_scope.

(* No notation for lcoset and rcoset, which are to be used mostly  *)
(* in curried form; x *: B and A :* 1 denote singleton products,   *)
(* so we can use mulgA, mulg1, etc, on, say, A :* 1 * B :* x.      *)
(* No notation for the set commutator generator set commg_set.     *)

Notation "''N' ( A )" := (normaliser A) : group_scope.
Notation "''N_' G ( A )" := (G%g :&: 'N(A)) : group_scope.
Notation "A <| B" := (normal A B) : group_scope.
Notation "''C' ( A )" := (centraliser A) : group_scope.
Notation "''C_' G ( A )" := (G%g :&: 'C(A)) : group_scope.
Notation "''C_' ( G ) ( A )" := 'C_G(A) (only parsing) : group_scope.
Notation "''C' [ x ]" := 'N([set x%g]) : group_scope.
Notation "''C_' G [ x ]" := 'N_G([set x%g]) : group_scope.
Notation "''C_' ( G ) [ x ]" := 'C_G[x] (only parsing) : group_scope.

Prenex Implicits repr lcoset rcoset lcosets rcosets normal.
Prenex Implicits conjugate conjugates class classes class_support.
Prenex Implicits commg_set normalised centralised abelian.

Section BaseSetMulProp.
(* Properties of the purely multiplicative structure. *)
Variable gT : baseFinGroupType.
Implicit Types A B C D : {set gT}.
Implicit Type x y z : gT.

(* Set product. We already have all the pregroup identities, so we *)
(* only need to add the monotonicity rules.                        *)

Lemma mulsgP A B x :
  reflect (imset2_spec mulg (mem A) (fun _ => mem B) x) (x \in A * B).
Proof. exact: imset2P. Qed.

Lemma mem_mulg A B x y : x \in A -> y \in B -> x * y \in A * B.
Proof. by move=> Ax By; apply/mulsgP; exists x y. Qed.

Lemma prodsgP (I : finType) (P : pred I) (A : I -> {set gT}) x :
  reflect (exists2 c, forall i, P i -> c i \in A i & x = \prod_(i | P i) c i)
          (x \in \prod_(i | P i) A i).
Proof.
have [r big_r [Ur mem_r] _] := big_enumP P.
pose inA c := all (fun i => c i \in A i); rewrite -big_r; set piAx := x \in _.
suffices{big_r} IHr: reflect (exists2 c, inA c r & x = \prod_(i <- r) c i) piAx.
  apply: (iffP IHr) => -[c inAc ->]; do [exists c; last by rewrite big_r].
    by move=> i Pi; rewrite (allP inAc) ?mem_r.
  by apply/allP=> i; rewrite mem_r => /inAc.
elim: {P mem_r}r x @piAx Ur => /= [x _ | i r IHr x /andP[r'i /IHr{}IHr]].
  by rewrite unlock; apply: (iffP set1P) => [-> | [] //]; exists (fun=> x).
rewrite big_cons; apply: (iffP idP) => [|[c /andP[Aci Ac] ->]]; last first.
  by rewrite big_cons mem_mulg //; apply/IHr=> //; exists c.
case/mulsgP=> c_i _ Ac_i /IHr[c /allP-inAcr ->] ->{x}.
exists [eta c with i |-> c_i]; rewrite /= ?big_cons eqxx ?Ac_i.
  by apply/allP=> j rj; rewrite /= ifN ?(memPn r'i) ?inAcr.
by congr (_ * _); apply: eq_big_seq => j rj; rewrite ifN ?(memPn r'i).
Qed.

Lemma mem_prodg (I : finType) (P : pred I) (A : I -> {set gT}) c :
  (forall i, P i -> c i \in A i) -> \prod_(i | P i) c i \in \prod_(i | P i) A i.
Proof. by move=> Ac; apply/prodsgP; exists c. Qed.

Lemma mulSg A B C : A \subset B -> A * C \subset B * C.
Proof. exact: imset2Sl. Qed.

Lemma mulgS A B C : B \subset C -> A * B \subset A * C.
Proof. exact: imset2Sr. Qed.

Lemma mulgSS A B C D : A \subset B -> C \subset D -> A * C \subset B * D.
Proof. exact: imset2S. Qed.

Lemma mulg_subl A B : 1 \in B -> A \subset A * B.
Proof. by move=> B1; rewrite -{1}(mulg1 A) mulgS ?sub1set. Qed.

Lemma mulg_subr A B : 1 \in A -> B \subset A * B.
Proof. by move=> A1; rewrite -{1}(mul1g B) mulSg ?sub1set. Qed.

Lemma mulUg A B C : (A :|: B) * C = (A * C) :|: (B * C).
Proof. exact: imset2Ul. Qed.

Lemma mulgU A B C : A * (B :|: C) = (A * B) :|: (A * C).
Proof. exact: imset2Ur. Qed.

(* Set (pointwise) inverse. *)

Lemma invUg A B : (A :|: B)^-1 = A^-1 :|: B^-1.
Proof. exact: preimsetU. Qed.

Lemma invIg A B : (A :&: B)^-1 = A^-1 :&: B^-1.
Proof. exact: preimsetI. Qed.

Lemma invDg A B : (A :\: B)^-1 = A^-1 :\: B^-1.
Proof. exact: preimsetD. Qed.

Lemma invCg A : (~: A)^-1 = ~: A^-1.
Proof. exact: preimsetC. Qed.

Lemma invSg A B : (A^-1 \subset B^-1) = (A \subset B).
Proof. by rewrite !(sameP setIidPl eqP) -invIg (inj_eq invg_inj). Qed.

Lemma mem_invg x A : (x \in A^-1) = (x^-1 \in A).
Proof. by rewrite inE. Qed.

Lemma memV_invg x A : (x^-1 \in A^-1) = (x \in A).
Proof. by rewrite inE invgK. Qed.

Lemma card_invg A : #|A^-1| = #|A|.
Proof. exact/card_preimset/invg_inj. Qed.

(* Product with singletons. *)

Lemma set1gE : 1 = [set 1] :> {set gT}. Proof. by []. Qed.
Lemma set1gP x : reflect (x = 1) (x \in [1 gT]).
Proof. exact: set1P. Qed.

Lemma mulg_set1 x y : [set x] :* y = [set x * y].
Proof. by rewrite [_ * _]imset2_set1l imset_set1. Qed.

Lemma invg_set1 x : [set x]^-1 = [set x^-1].
Proof. by apply/setP=> y; rewrite !inE inv_eq //; apply: invgK. Qed.

End BaseSetMulProp.

Arguments set1gP {gT x}.
Arguments mulsgP {gT A B x}.
Arguments prodsgP {gT I P A x}.

Section GroupSetMulProp.
(* Constructs that need a finGroupType *)
Variable gT : finGroupType.
Implicit Types A B C D : {set gT}.
Implicit Type x y z : gT.

(* Left cosets. *)

Lemma lcosetE A x : lcoset A x = x *: A.
Proof. by rewrite [_ * _]imset2_set1l. Qed.

Lemma card_lcoset A x : #|x *: A| = #|A|.
Proof. by rewrite -lcosetE (card_imset _ (mulgI _)). Qed.

Lemma mem_lcoset A x y : (y \in x *: A) = (x^-1 * y \in A).
Proof. by rewrite -lcosetE [_ x](can_imset_pre _ (mulKg _)) inE. Qed.

Lemma lcosetP A x y : reflect (exists2 a, a \in A & y = x * a) (y \in x *: A).
Proof. by rewrite -lcosetE; apply: imsetP. Qed.

Lemma lcosetsP A B C :
  reflect (exists2 x, x \in B & C = x *: A) (C \in lcosets A B).
Proof. by apply: (iffP imsetP) => [] [x Bx ->]; exists x; rewrite ?lcosetE. Qed.

Lemma lcosetM A x y : (x * y) *: A = x *: (y *: A).
Proof. by rewrite -mulg_set1 mulgA. Qed.

Lemma lcoset1 A : 1 *: A = A.
Proof. exact: mul1g. Qed.

Lemma lcosetK : left_loop invg (fun x A => x *: A).
Proof. by move=> x A; rewrite -lcosetM mulVg mul1g. Qed.

Lemma lcosetKV : rev_left_loop invg (fun x A => x *: A).
Proof. by move=> x A; rewrite -lcosetM mulgV mul1g. Qed.

Lemma lcoset_inj : right_injective (fun x A => x *: A).
Proof. by move=> x; apply: can_inj (lcosetK x). Qed.

Lemma lcosetS x A B : (x *: A \subset x *: B) = (A \subset B).
Proof.
apply/idP/idP=> sAB; last exact: mulgS.
by rewrite -(lcosetK x A) -(lcosetK x B) mulgS.
Qed.

Lemma sub_lcoset x A B : (A \subset x *: B) = (x^-1 *: A \subset B).
Proof. by rewrite -(lcosetS x^-1) lcosetK. Qed.

Lemma sub_lcosetV x A B : (A \subset x^-1 *: B) = (x *: A \subset B).
Proof. by rewrite sub_lcoset invgK. Qed.

(* Right cosets. *)

Lemma rcosetE A x : rcoset A x = A :* x.
Proof. by rewrite [_ * _]imset2_set1r. Qed.

Lemma card_rcoset A x : #|A :* x| = #|A|.
Proof. by rewrite -rcosetE (card_imset _ (mulIg _)). Qed.

Lemma mem_rcoset A x y : (y \in A :* x) = (y * x^-1 \in A).
Proof. by rewrite -rcosetE  [_ x](can_imset_pre A (mulgK _)) inE. Qed.

Lemma rcosetP A x y : reflect (exists2 a, a \in A & y = a * x) (y \in A :* x).
Proof. by rewrite -rcosetE; apply: imsetP. Qed.

Lemma rcosetsP A B C :
  reflect (exists2 x, x \in B & C = A :* x) (C \in rcosets A B).
Proof. by apply: (iffP imsetP) => [] [x Bx ->]; exists x; rewrite ?rcosetE. Qed.

Lemma rcosetM A x y : A :* (x * y) = A :* x :* y.
Proof. by rewrite -mulg_set1 mulgA. Qed.

Lemma rcoset1 A : A :* 1 = A.
Proof. exact: mulg1. Qed.

Lemma rcosetK : right_loop invg (fun A x => A :* x).
Proof. by move=> x A; rewrite -rcosetM mulgV mulg1. Qed.

Lemma rcosetKV : rev_right_loop invg (fun A x => A :* x).
Proof. by move=> x A; rewrite -rcosetM mulVg mulg1. Qed.

Lemma rcoset_inj : left_injective (fun A x => A :* x).
Proof. by move=> x; apply: can_inj (rcosetK x). Qed.

Lemma rcosetS x A B : (A :* x \subset B :* x) = (A \subset B).
Proof.
apply/idP/idP=> sAB; last exact: mulSg.
by rewrite -(rcosetK x A) -(rcosetK x B) mulSg.
Qed.

Lemma sub_rcoset x A B : (A \subset B :* x) = (A :* x ^-1 \subset B).
Proof. by rewrite -(rcosetS x^-1) rcosetK. Qed.

Lemma sub_rcosetV x A B : (A \subset B :* x^-1) = (A :* x \subset B).
Proof. by rewrite sub_rcoset invgK. Qed.

(* Inverse maps lcosets to rcosets *)
Lemma invg_lcosets A B : (lcosets A B)^-1 = rcosets A^-1 B^-1.
Proof.
rewrite /A^-1/= -![_^-1](can_imset_pre _ invgK) -[RHS]imset_comp -imset_comp.
by apply: eq_imset => x /=; rewrite lcosetE rcosetE invMg invg_set1.
Qed.

(* Conjugates. *)

Lemma conjg_preim A x : A :^ x = (conjg^~ x^-1) @^-1: A.
Proof. exact: can_imset_pre (conjgK _). Qed.

Lemma mem_conjg A x y : (y \in A :^ x) = (y ^ x^-1 \in A).
Proof. by rewrite conjg_preim inE. Qed.

Lemma mem_conjgV A x y : (y \in A :^ x^-1) = (y ^ x \in A).
Proof. by rewrite mem_conjg invgK. Qed.

Lemma memJ_conjg A x y : (y ^ x \in A :^ x) = (y \in A).
Proof. by rewrite mem_conjg conjgK. Qed.

Lemma conjsgE A x : A :^ x = x^-1 *: (A :* x).
Proof. by apply/setP=> y; rewrite mem_lcoset mem_rcoset -mulgA mem_conjg. Qed.

Lemma conjsg1 A : A :^ 1 = A.
Proof. by rewrite conjsgE invg1 mul1g mulg1. Qed.

Lemma conjsgM A x y : A :^ (x * y) = (A :^ x) :^ y.
Proof. by rewrite !conjsgE invMg -!mulg_set1 !mulgA. Qed.

Lemma conjsgK : @right_loop _ gT invg conjugate.
Proof. by move=> x A; rewrite -conjsgM mulgV conjsg1. Qed.

Lemma conjsgKV : @rev_right_loop _ gT invg conjugate.
Proof. by move=> x A; rewrite -conjsgM mulVg conjsg1. Qed.

Lemma conjsg_inj : @left_injective _ gT _ conjugate.
Proof. by move=> x; apply: can_inj (conjsgK x). Qed.

Lemma cardJg A x : #|A :^ x| = #|A|.
Proof. by rewrite (card_imset _ (conjg_inj x)). Qed.

Lemma conjSg A B x : (A :^ x \subset B :^ x) = (A \subset B).
Proof. by rewrite !conjsgE lcosetS rcosetS. Qed.

Lemma properJ A B x : (A :^ x \proper B :^ x) = (A \proper B).
Proof. by rewrite /proper !conjSg. Qed.

Lemma sub_conjg A B x : (A :^ x \subset B) = (A \subset B :^ x^-1).
Proof. by rewrite -(conjSg A _ x) conjsgKV. Qed.

Lemma sub_conjgV A B x : (A :^ x^-1 \subset B) = (A \subset B :^ x).
Proof. by rewrite -(conjSg _ B x) conjsgKV. Qed.

Lemma conjg_set1 x y : [set x] :^ y = [set x ^ y].
Proof. by rewrite [_ :^ _]imset_set1. Qed.

Lemma conjs1g x : 1 :^ x = 1.
Proof. by rewrite conjg_set1 conj1g. Qed.

Lemma conjsg_eq1 A x : (A :^ x == 1%g) = (A == 1%g).
Proof. by rewrite (canF_eq (conjsgK x)) conjs1g. Qed.

Lemma conjsMg A B x : (A * B) :^ x = A :^ x * B :^ x.
Proof. by rewrite !conjsgE !mulgA rcosetK. Qed.

Lemma conjIg A B x : (A :&: B) :^ x = A :^ x :&: B :^ x.
Proof. by rewrite !conjg_preim preimsetI. Qed.

Lemma conj0g x : set0 :^ x = set0.
Proof. exact: imset0. Qed.

Lemma conjTg x : [set: gT] :^ x = [set: gT].
Proof. by rewrite conjg_preim preimsetT. Qed.

Lemma bigcapJ I r (P : pred I) (B : I -> {set gT}) x :
  \bigcap_(i <- r | P i) (B i :^ x) = (\bigcap_(i <- r | P i) B i) :^ x.
Proof.
by rewrite (big_endo (conjugate^~ x)) => // [B1 B2|]; rewrite (conjTg, conjIg).
Qed.

Lemma conjUg A B x : (A :|: B) :^ x = A :^ x :|: B :^ x.
Proof. by rewrite !conjg_preim preimsetU. Qed.

Lemma bigcupJ I r (P : pred I) (B : I -> {set gT}) x :
  \bigcup_(i <- r | P i) (B i :^ x) = (\bigcup_(i <- r | P i) B i) :^ x.
Proof.
rewrite (big_endo (conjugate^~ x)) => // [B1 B2|]; first by rewrite conjUg.
exact: imset0.
Qed.

Lemma conjCg A x : (~: A) :^ x = ~: A :^ x.
Proof. by rewrite !conjg_preim preimsetC. Qed.

Lemma conjDg A B x : (A :\: B) :^ x = A :^ x :\: B :^ x.
Proof. by rewrite !setDE !(conjCg, conjIg). Qed.

Lemma conjD1g A x : A^# :^ x = (A :^ x)^#.
Proof. by rewrite conjDg conjs1g. Qed.

(* Classes; not much for now. *)

Lemma memJ_class x y A : y \in A -> x ^ y \in x ^: A.
Proof. exact: imset_f. Qed.

Lemma classS x A B : A \subset B -> x ^: A \subset x ^: B.
Proof. exact: imsetS. Qed.

Lemma class_set1 x y :  x ^: [set y] = [set x ^ y].
Proof. exact: imset_set1. Qed.

Lemma class1g x A : x \in A -> 1 ^: A = 1.
Proof.
move=> Ax; apply/setP=> y.
by apply/imsetP/set1P=> [[a Aa]|] ->; last exists x; rewrite ?conj1g.
Qed.

Lemma classVg x A : x^-1 ^: A = (x ^: A)^-1.
Proof.
apply/setP=> xy; rewrite inE; apply/imsetP/imsetP=> [] [y Ay def_xy].
  by rewrite def_xy conjVg invgK; exists y.
by rewrite -[xy]invgK def_xy -conjVg; exists y.
Qed.

Lemma mem_classes x A : x \in A -> x ^: A \in classes A.
Proof. exact: imset_f. Qed.

Lemma memJ_class_support A B x y :
   x \in A -> y \in B -> x ^ y \in class_support A B.
Proof. by move=> Ax By; apply: imset2_f. Qed.

Lemma class_supportM A B C :
  class_support A (B * C) = class_support (class_support A B) C.
Proof.
apply/setP=> x; apply/imset2P/imset2P=> [[a y Aa] | [y c]].
  case/mulsgP=> b c Bb Cc -> ->{x y}.
  by exists (a ^ b) c; rewrite ?(imset2_f, conjgM).
case/imset2P=> a b Aa Bb -> Cc ->{x y}.
by exists a (b * c); rewrite ?(mem_mulg, conjgM).
Qed.

Lemma class_support_set1l A x : class_support [set x] A = x ^: A.
Proof. exact: imset2_set1l. Qed.

Lemma class_support_set1r A x : class_support A [set x] = A :^ x.
Proof. exact: imset2_set1r. Qed.

Lemma classM x A B : x ^: (A * B) = class_support (x ^: A) B.
Proof. by rewrite -!class_support_set1l class_supportM. Qed.

Lemma class_lcoset x y A : x ^: (y *: A) = (x ^ y) ^: A.
Proof. by rewrite classM class_set1 class_support_set1l. Qed.

Lemma class_rcoset x A y : x ^: (A :* y) = (x ^: A) :^ y.
Proof. by rewrite -class_support_set1r classM. Qed.

(* Conjugate set. *)

Lemma conjugatesS A B C : B \subset C -> A :^: B \subset A :^: C.
Proof. exact: imsetS. Qed.

Lemma conjugates_set1 A x : A :^: [set x] = [set A :^ x].
Proof. exact: imset_set1. Qed.

Lemma conjugates_conj A x B : (A :^ x) :^: B = A :^: (x *: B).
Proof.
rewrite /conjugates [x *: B]imset2_set1l -imset_comp.
by apply: eq_imset => y /=; rewrite conjsgM.
Qed.

(* Class support. *)

Lemma class_supportEl A B : class_support A B = \bigcup_(x in A) x ^: B.
Proof. exact: curry_imset2l. Qed.

Lemma class_supportEr A B : class_support A B = \bigcup_(x in B) A :^ x.
Proof. exact: curry_imset2r. Qed.

(* Groups (at last!) *)

Definition group_set A := (1 \in A) && (A * A \subset A).

Lemma group_setP A :
  reflect (1 \in A /\ {in A & A, forall x y, x * y \in A}) (group_set A).
Proof.
apply: (iffP andP) => [] [A1 AM]; split=> {A1}//.
  by move=> x y Ax Ay; apply: (subsetP AM); rewrite mem_mulg.
by apply/subsetP=> _ /mulsgP[x y Ax Ay ->]; apply: AM.
Qed.

Structure group_type : Type := Group {
  gval :> GroupSet.sort gT;
  _ : group_set gval
}.

Definition group_of of phant gT : predArgType := group_type.
Local Notation groupT := (group_of (Phant gT)).
Identity Coercion type_of_group : group_of >-> group_type.

HB.instance Definition _ := [IsSUB for gval].
#[hnf] HB.instance Definition _ := [Finite of group_type by <:].

(* No predType or baseFinGroupType structures, as these would hide the *)
(* group-to-set coercion and thus spoil unification.                  *)
HB.instance Definition _ := SubFinite.copy groupT group_type.

Definition group (A : {set gT}) gA : groupT := @Group A gA.

Definition clone_group G :=
  let: Group _ gP := G return {type of Group for G} -> groupT in fun k => k gP.

Lemma group_inj : injective gval. Proof. exact: val_inj. Qed.
Lemma groupP (G : groupT) : group_set G. Proof. by case: G. Qed.

Lemma congr_group (H K : groupT) : H = K -> H :=: K.
Proof. exact: congr1. Qed.

Lemma isgroupP A : reflect (exists G : groupT, A = G) (group_set A).
Proof. by apply: (iffP idP) => [gA | [[B gB] -> //]]; exists (Group gA). Qed.

Lemma group_set_one : group_set 1.
Proof. by rewrite /group_set set11 mulg1 subxx. Qed.

Canonical one_group := group group_set_one.
Canonical set1_group := @group [set 1] group_set_one.

Lemma group_setT (phT : phant gT) : group_set (setTfor phT).
Proof. by apply/group_setP; split=> [|x y _ _]; rewrite inE. Qed.

Canonical setT_group phT := group (group_setT phT).

End GroupSetMulProp.

Arguments lcosetP {gT A x y}.
Arguments lcosetsP {gT A B C}.
Arguments rcosetP {gT A x y}.
Arguments rcosetsP {gT A B C}.
Arguments group_setP {gT A}.
Prenex Implicits group_set mulsgP set1gP.

Notation "{ 'group' gT }" := (group_of (Phant gT))
  (at level 0, format "{ 'group'  gT }") : type_scope.

Notation "[ 'group' 'of' G ]" := (clone_group (@group _ G))
  (at level 0, format "[ 'group'  'of'  G ]") : form_scope.

Bind Scope Group_scope with group_type.
Bind Scope Group_scope with group_of.
Notation "1" := (one_group _) : Group_scope.
Notation "[ 1 gT ]" := (1%G : {group gT}) : Group_scope.
Notation "[ 'set' : gT ]" := (setT_group (Phant gT)) : Group_scope.

(* These definitions come early so we can establish the Notation. *)
HB.lock
Definition generated (gT : finGroupType) (A : {set gT}) :=
  \bigcap_(G : {group gT} | A \subset G) G.
Canonical generated_unlockable := Unlockable generated.unlock.

Definition gcore (gT : finGroupType) (A B : {set gT}) := \bigcap_(x in B) A :^ x.
Definition joing (gT : finGroupType) (A B : {set gT}) := generated (A :|: B).
Definition commutator (gT : finGroupType) (A B : {set gT}) := generated (commg_set A B).
Definition cycle (gT : finGroupType) (x : gT) := generated [set x].
Definition order (gT : finGroupType) (x : gT) := #|cycle x|.

Arguments commutator _ _%g _%g.
Arguments joing _ _%g _%g.
Arguments generated _ _%g.

(* Helper notation for defining new groups that need a bespoke finGroupType. *)
(* The actual group for such a type (say, my_gT) will be the full group,     *)
(* i.e., [set: my_gT] or [set: my_gT]%G, but Coq will not recognize          *)
(* specific notation for these because of the coercions inserted during type *)
(* inference, unless they are defined as [set: gsort my_gT] using the        *)
(* Notation below.                                                           *)
Notation gsort gT := (BaseFinGroup.arg_sort gT%type) (only parsing).
Notation "<< A >>"  := (generated A) : group_scope.
Notation "<[ x ] >"  := (cycle x) : group_scope.
Notation "#[ x ]"  := (order x) : group_scope.
Notation "A <*> B" := (joing A B) : group_scope.
Notation "[ ~: A1 , A2 , .. , An ]" :=
  (commutator .. (commutator A1 A2) .. An) : group_scope.

Prenex Implicits order cycle gcore.

Section GroupProp.

Variable gT : finGroupType.
Notation sT := {set gT}.
Implicit Types A B C D : sT.
Implicit Types x y z : gT.
Implicit Types G H K : {group gT}.

Section OneGroup.

Variable G : {group gT}.

Lemma valG : val G = G. Proof. by []. Qed.

(* Non-triviality. *)

Lemma group1 : 1 \in G. Proof. by case/group_setP: (valP G). Qed.
#[local] Hint Resolve group1 : core.

Lemma group1_contra x : x \notin G -> x != 1.
Proof. by apply: contraNneq => ->. Qed.

Lemma sub1G : [1 gT] \subset G. Proof. by rewrite sub1set. Qed.
Lemma subG1 : (G \subset [1]) = (G :==: 1).
Proof. by rewrite eqEsubset sub1G andbT. Qed.

Lemma setI1g : 1 :&: G = 1. Proof. exact: (setIidPl sub1G). Qed.
Lemma setIg1 : G :&: 1 = 1. Proof. exact: (setIidPr sub1G). Qed.

Lemma subG1_contra H : G \subset H -> G :!=: 1 -> H :!=: 1.
Proof. by move=> sGH; rewrite -subG1; apply: contraNneq => <-. Qed.

Lemma repr_group : repr G = 1. Proof. by rewrite /repr group1. Qed.

Lemma cardG_gt0 : 0 < #|G|.
Proof. by rewrite lt0n; apply/existsP; exists (1 : gT). Qed.

Lemma indexg_gt0 A : 0 < #|G : A|.
Proof.
rewrite lt0n; apply/existsP; exists A.
by rewrite -{2}[A]mulg1 -rcosetE; apply: imset_f.
Qed.

Lemma trivgP : reflect (G :=: 1) (G \subset [1]).
Proof. by rewrite subG1; apply: eqP. Qed.

Lemma trivGP : reflect (G = 1%G) (G \subset [1]).
Proof. by rewrite subG1; apply: eqP. Qed.

Lemma proper1G : ([1] \proper G) = (G :!=: 1).
Proof. by rewrite properEneq sub1G andbT eq_sym. Qed.

Lemma in_one_group x : (x \in 1%G) = (x == 1).
Proof. by rewrite -[x \in _]/(x \in [set 1]) !inE. Qed.

Definition inE := (in_one_group, inE).

Lemma trivgPn : reflect (exists2 x, x \in G & x != 1) (G :!=: 1).
Proof.
rewrite -subG1.
by apply: (iffP subsetPn) => [] [x Gx x1]; exists x; rewrite ?inE in x1 *.
Qed.

Lemma trivg_card_le1 : (G :==: 1) = (#|G| <= 1).
Proof. by rewrite eq_sym eqEcard cards1 sub1G. Qed.

Lemma trivg_card1 : (G :==: 1) = (#|G| == 1%N).
Proof. by rewrite trivg_card_le1 eqn_leq cardG_gt0 andbT. Qed.

Lemma cardG_gt1 : (#|G| > 1) = (G :!=: 1).
Proof. by rewrite trivg_card_le1 ltnNge. Qed.

Lemma card_le1_trivg : #|G| <= 1 -> G :=: 1.
Proof. by rewrite -trivg_card_le1; move/eqP. Qed.

Lemma card1_trivg : #|G| = 1%N -> G :=: 1.
Proof. by move=> G1; rewrite card_le1_trivg ?G1. Qed.

(* Inclusion and product. *)

Lemma mulG_subl A : A \subset A * G.
Proof. exact: mulg_subl group1. Qed.

Lemma mulG_subr A : A \subset ((G : {set gT}) * A ).
Proof. exact: mulg_subr group1. Qed.

Lemma mulGid : (G : {set gT}) * G = G.
Proof.
by apply/eqP; rewrite eqEsubset mulG_subr andbT; case/andP: (valP G).
Qed.

Lemma mulGS A B : (G * A \subset G * B) = (A \subset G * B).
Proof.
apply/idP/idP; first exact: subset_trans (mulG_subr A).
by move/(mulgS G); rewrite mulgA mulGid.
Qed.

Lemma mulSG A B : (A * G \subset B * G) = (A \subset B * G).
Proof.
apply/idP/idP; first exact: subset_trans (mulG_subl A).
by move/(mulSg G); rewrite -mulgA mulGid.
Qed.

Lemma mul_subG A B : A \subset G -> B \subset G -> A * B \subset G.
Proof. by move=> sAG sBG; rewrite -mulGid mulgSS. Qed.

(* Membership lemmas *)

Lemma groupM x y : x \in G -> y \in G -> x * y \in G.
Proof. by case/group_setP: (valP G) x y. Qed.

Lemma groupX x n : x \in G -> x ^+ n \in G.
Proof. by move=> Gx; elim: n => [|n IHn]; rewrite ?group1 // expgS groupM. Qed.

Lemma groupVr x : x \in G -> x^-1 \in G.
Proof.
move=> Gx; rewrite -(mul1g x^-1) -mem_rcoset ((G :* x =P G) _) //.
by rewrite eqEcard card_rcoset leqnn mul_subG ?sub1set.
Qed.

Lemma groupVl x : x^-1 \in G -> x \in G.
Proof. by move/groupVr; rewrite invgK. Qed.

Lemma groupV x : (x^-1 \in G) = (x \in G).
Proof. by apply/idP/idP; [apply: groupVl | apply: groupVr]. Qed.

Lemma groupMl x y : x \in G -> (x * y \in G) = (y \in G).
Proof.
move=> Gx; apply/idP/idP=> [Gxy|]; last exact: groupM.
by rewrite -(mulKg x y) groupM ?groupVr.
Qed.

Lemma groupMr x y : x \in G -> (y * x \in G) = (y \in G).
Proof. by move=> Gx; rewrite -[_ \in G]groupV invMg groupMl groupV. Qed.

Definition in_group := (group1, groupV, (groupMl, groupX)).

Lemma groupJ x y : x \in G -> y \in G -> x ^ y \in G.
Proof. by move=> Gx Gy; rewrite !in_group. Qed.

Lemma groupJr x y : y \in G -> (x ^ y \in G) = (x \in G).
Proof. by move=> Gy; rewrite groupMl (groupMr, groupV). Qed.

Lemma groupR x y : x \in G -> y \in G -> [~ x, y] \in G.
Proof. by move=> Gx Gy; rewrite !in_group. Qed.

Lemma group_prod I r (P : pred I) F :
  (forall i, P i -> F i \in G) -> \prod_(i <- r | P i) F i \in G.
Proof. by move=> G_P; elim/big_ind: _ => //; apply: groupM. Qed.

(* Inverse is an anti-morphism. *)

Lemma invGid : G^-1 = G. Proof. by apply/setP=> x; rewrite inE groupV. Qed.

Lemma inv_subG A : (A^-1 \subset G) = (A \subset G).
Proof. by rewrite -{1}invGid invSg. Qed.

Lemma invg_lcoset x : (x *: G)^-1 = G :* x^-1.
Proof. by rewrite invMg invGid invg_set1. Qed.

Lemma invg_rcoset x : (G :* x)^-1 = x^-1 *: G.
Proof. by rewrite invMg invGid invg_set1. Qed.

Lemma memV_lcosetV x y : (y^-1 \in x^-1 *: G) = (y \in G :* x).
Proof. by rewrite -invg_rcoset memV_invg. Qed.

Lemma memV_rcosetV x y : (y^-1 \in G :* x^-1) = (y \in x *: G).
Proof. by rewrite -invg_lcoset memV_invg. Qed.

(* Product idempotence *)

Lemma mulSgGid A x : x \in A -> A \subset G -> A * G = G.
Proof.
move=> Ax sAG; apply/eqP; rewrite eqEsubset -{2}mulGid mulSg //=.
apply/subsetP=> y Gy; rewrite -(mulKVg x y) mem_mulg // groupMr // groupV.
exact: (subsetP sAG).
Qed.

Lemma mulGSgid A x : x \in A -> A \subset G -> G * A = G.
Proof.
rewrite -memV_invg -invSg invGid => Ax sAG.
by apply: invg_inj; rewrite invMg invGid (mulSgGid Ax).
Qed.

(* Left cosets *)

Lemma lcoset_refl x : x \in x *: G.
Proof. by rewrite mem_lcoset mulVg group1. Qed.

Lemma lcoset_sym x y : (x \in y *: G) = (y \in x *: G).
Proof. by rewrite !mem_lcoset -groupV invMg invgK. Qed.

Lemma lcoset_eqP {x y} : reflect (x *: G = y *: G) (x \in y *: G).
Proof.
suffices <-: (x *: G == y *: G) = (x \in y *: G) by apply: eqP.
by rewrite eqEsubset !mulSG !sub1set lcoset_sym andbb.
Qed.

Lemma lcoset_transl x y z : x \in y *: G -> (x \in z *: G) = (y \in z *: G).
Proof. by move=> Gyx; rewrite -2!(lcoset_sym z) (lcoset_eqP Gyx). Qed.

Lemma lcoset_trans x y z : x \in y *: G -> y \in z *: G -> x \in z *: G.
Proof. by move/lcoset_transl->. Qed.

Lemma lcoset_id x : x \in G -> x *: G = G.
Proof. by move=> Gx; rewrite (lcoset_eqP (_ : x \in 1 *: G)) mul1g. Qed.

(* Right cosets, with an elimination form for repr. *)

Lemma rcoset_refl x : x \in G :* x.
Proof. by rewrite mem_rcoset mulgV group1. Qed.

Lemma rcoset_sym x y : (x \in G :* y) = (y \in G :* x).
Proof. by rewrite -!memV_lcosetV lcoset_sym. Qed.

Lemma rcoset_eqP {x y} : reflect (G :* x = G :* y) (x \in G :* y).
Proof.
suffices <-: (G :* x == G :* y) = (x \in G :* y) by apply: eqP.
by rewrite eqEsubset !mulGS !sub1set rcoset_sym andbb.
Qed.

Lemma rcoset_transl x y z : x \in G :* y -> (x \in G :* z) = (y \in G :* z).
Proof. by move=> Gyx; rewrite -2!(rcoset_sym z) (rcoset_eqP Gyx). Qed.

Lemma rcoset_trans x y z : x \in G :* y -> y \in G :* z -> x \in G :* z.
Proof. by move/rcoset_transl->. Qed.

Lemma rcoset_id x : x \in G -> G :* x = G.
Proof. by move=> Gx; rewrite (rcoset_eqP (_ : x \in G :* 1)) mulg1. Qed.

(* Elimination form. *)

Variant rcoset_repr_spec x : gT -> Type :=
  RcosetReprSpec g : g \in G -> rcoset_repr_spec x (g * x).

Lemma mem_repr_rcoset x : repr (G :* x) \in G :* x.
Proof. exact: mem_repr (rcoset_refl x). Qed.

(* This form sometimes fails because ssreflect 1.1 delegates matching to the *)
(* (weaker) primitive Coq algorithm for general (co)inductive type families. *)
Lemma repr_rcosetP x : rcoset_repr_spec x (repr (G :* x)).
Proof.
by rewrite -[repr _](mulgKV x); split; rewrite -mem_rcoset mem_repr_rcoset.
Qed.

Lemma rcoset_repr x : G :* (repr (G :* x)) = G :* x.
Proof. exact/rcoset_eqP/mem_repr_rcoset. Qed.

(* Coset spaces. *)

Lemma mem_rcosets A x : (G :* x \in rcosets G A) = (x \in G * A).
Proof.
apply/rcosetsP/mulsgP=> [[a Aa /rcoset_eqP/rcosetP[g]] | ]; first by exists g a.
by case=> g a Gg Aa ->{x}; exists a; rewrite // rcosetM rcoset_id.
Qed.

Lemma mem_lcosets A x : (x *: G \in lcosets G A) = (x \in A * G).
Proof.
rewrite -[LHS]memV_invg invg_lcoset invg_lcosets.
by rewrite -[RHS]memV_invg invMg invGid mem_rcosets.
Qed.

(* Conjugates. *)

Lemma group_setJ A x : group_set (A :^ x) = group_set A.
Proof. by rewrite /group_set mem_conjg conj1g -conjsMg conjSg. Qed.

Lemma group_set_conjG x : group_set (G :^ x).
Proof. by rewrite group_setJ groupP. Qed.

Canonical conjG_group x := group (group_set_conjG x).

Lemma conjGid : {in G, normalised G}.
Proof. by move=> x Gx; apply/setP=> y; rewrite mem_conjg groupJr ?groupV. Qed.

Lemma conj_subG x A : x \in G -> A \subset G -> A :^ x \subset G.
Proof. by move=> Gx sAG; rewrite -(conjGid Gx) conjSg. Qed.

(* Classes *)

Lemma class1G : 1 ^: G = 1. Proof. exact: class1g group1. Qed.

Lemma classes1 : [1] \in classes G. Proof. by rewrite -class1G mem_classes. Qed.

Lemma classGidl x y : y \in G -> (x ^ y) ^: G = x ^: G.
Proof. by move=> Gy; rewrite -class_lcoset lcoset_id. Qed.

Lemma classGidr x : {in G, normalised (x ^: G)}.
Proof. by move=> y Gy /=; rewrite -class_rcoset rcoset_id. Qed.

Lemma class_refl x : x \in x ^: G.
Proof. by apply/imsetP; exists 1; rewrite ?conjg1. Qed.
#[local] Hint Resolve class_refl : core.

Lemma class_eqP x y : reflect (x ^: G = y ^: G) (x \in y ^: G).
Proof.
by apply: (iffP idP) => [/imsetP[z Gz ->] | <-]; rewrite ?class_refl ?classGidl.
Qed.

Lemma class_sym x y : (x \in y ^: G) = (y \in x ^: G).
Proof. by apply/idP/idP=> /class_eqP->. Qed.

Lemma class_transl x y z : x \in y ^: G -> (x \in z ^: G) = (y \in z ^: G).
Proof. by rewrite -!(class_sym z) => /class_eqP->. Qed.

Lemma class_trans x y z : x \in y ^: G -> y \in z ^: G -> x \in z ^: G.
Proof. by move/class_transl->. Qed.

Lemma repr_class x : {y | y \in G & repr (x ^: G) = x ^ y}.
Proof.
set z := repr _; have: #|[set y in G | z == x ^ y]| > 0.
  have: z \in x ^: G by apply: (mem_repr x).
  by case/imsetP=> y Gy ->; rewrite (cardD1 y) inE Gy eqxx.
by move/card_mem_repr; move: (repr _) => y /setIdP[Gy /eqP]; exists y.
Qed.

Lemma classG_eq1 x : (x ^: G == 1) = (x == 1).
Proof.
apply/eqP/eqP=> [xG1 | ->]; last exact: class1G.
by have:= class_refl x; rewrite xG1 => /set1P.
Qed.

Lemma class_subG x A : x \in G -> A \subset G -> x ^: A \subset G.
Proof.
move=> Gx sAG; apply/subsetP=> _ /imsetP[y Ay ->].
by rewrite groupJ // (subsetP sAG).
Qed.

Lemma repr_classesP xG :
  reflect (repr xG \in G /\ xG = repr xG ^: G) (xG \in classes G).
Proof.
apply: (iffP imsetP) => [[x Gx ->] | []]; last by exists (repr xG).
by have [y Gy ->] := repr_class x; rewrite classGidl ?groupJ.
Qed.

Lemma mem_repr_classes xG : xG \in classes G -> repr xG \in xG.
Proof. by case/repr_classesP=> _ {2}->; apply: class_refl. Qed.

Lemma classes_gt0 : 0 < #|classes G|.
Proof. by rewrite (cardsD1 1) classes1. Qed.

Lemma classes_gt1 : (#|classes G| > 1) = (G :!=: 1).
Proof.
rewrite (cardsD1 1) classes1 ltnS lt0n cards_eq0.
apply/set0Pn/trivgPn=> [[xG /setD1P[nt_xG]] | [x Gx ntx]].
  by case/imsetP=> x Gx def_xG; rewrite def_xG classG_eq1 in nt_xG; exists x.
by exists (x ^: G); rewrite !inE classG_eq1 ntx; apply: imset_f.
Qed.

Lemma mem_class_support A x : x \in A -> x \in class_support A G.
Proof. by move=> Ax; rewrite -[x]conjg1 memJ_class_support. Qed.

Lemma class_supportGidl A x :
  x \in G -> class_support (A :^ x) G = class_support A G.
Proof.
by move=> Gx; rewrite -class_support_set1r -class_supportM lcoset_id.
Qed.

Lemma class_supportGidr A : {in G, normalised (class_support A G)}.
Proof.
by move=> x Gx /=; rewrite -class_support_set1r -class_supportM rcoset_id.
Qed.

Lemma class_support_subG A : A \subset G -> class_support A G \subset G.
Proof.
by move=> sAG; rewrite class_supportEr; apply/bigcupsP=> x Gx; apply: conj_subG.
Qed.

Lemma sub_class_support A : A \subset class_support A G.
Proof. by rewrite class_supportEr (bigcup_max 1) ?conjsg1. Qed.

Lemma class_support_id : class_support G G = G.
Proof.
by apply/eqP; rewrite eqEsubset sub_class_support class_support_subG.
Qed.

Lemma class_supportD1 A : (class_support A G)^# =  cover (A^# :^: G).
Proof.
rewrite cover_imset class_supportEr setDE big_distrl /=.
by apply: eq_bigr => x _; rewrite -setDE conjD1g.
Qed.

(* Subgroup Type construction. *)
(* We only expect to use this for abstract groups, so we don't project *)
(* the argument to a set.                                              *)

Inductive subg_of : predArgType := Subg x & x \in G.
Definition sgval u := let: Subg x _ := u in x.
Definition subg_of_SUB := Eval hnf in [IsSUB for sgval].
HB.instance Definition _ := subg_of_SUB.
#[hnf] HB.instance Definition _ := [Finite of subg_of by <:].

Lemma subgP u : sgval u \in G.
Proof. exact: valP. Qed.
Lemma subg_inj : injective sgval.
Proof. exact: val_inj. Qed.
Lemma congr_subg u v : u = v -> sgval u = sgval v.
Proof. exact: congr1. Qed.

Definition subg_one := Subg group1.
Definition subg_inv u := Subg (groupVr (subgP u)).
Definition subg_mul u v := Subg (groupM (subgP u) (subgP v)).
Lemma subg_oneP : left_id subg_one subg_mul.
Proof. by move=> u; apply: val_inj; apply: mul1g. Qed.

Lemma subg_invP : left_inverse subg_one subg_inv subg_mul.
Proof. by move=> u; apply: val_inj; apply: mulVg. Qed.
Lemma subg_mulP : associative subg_mul.
Proof. by move=> u v w; apply: val_inj; apply: mulgA. Qed.

HB.instance Definition _ := isMulGroup.Build subg_of
  subg_mulP subg_oneP subg_invP.

Lemma sgvalM : {in setT &, {morph sgval : x y / x * y}}. Proof. by []. Qed.
Lemma valgM : {in setT &, {morph val : x y / (x : subg_of) * y >-> x * y}}.
Proof. by []. Qed.

Definition subg : gT -> subg_of := insubd (1 : subg_of).
Lemma subgK x : x \in G -> val (subg x) = x.
Proof. by move=> Gx; rewrite insubdK. Qed.
Lemma sgvalK : cancel sgval subg.
Proof. by case=> x Gx; apply: val_inj; apply: subgK. Qed.
Lemma subg_default x : (x \in G) = false -> val (subg x) = 1.
Proof. by move=> Gx; rewrite val_insubd Gx. Qed.
Lemma subgM : {in G &, {morph subg : x y / x * y}}.
Proof. by move=> x y Gx Gy; apply: val_inj; rewrite /= !subgK ?groupM. Qed.

End OneGroup.

#[local] Hint Resolve group1 : core.

Lemma groupD1_inj G H : G^# = H^# -> G :=: H.
Proof. by move/(congr1 (setU 1)); rewrite !setD1K. Qed.

Lemma invMG G H : (G * H)^-1 = H * G.
Proof. by rewrite invMg !invGid. Qed.

Lemma mulSGid G H : H \subset G -> H * G = G.
Proof. exact: mulSgGid (group1 H). Qed.

Lemma mulGSid G H : H \subset G -> G * H = G.
Proof. exact: mulGSgid (group1 H). Qed.

Lemma mulGidPl G H : reflect (G * H = G) (H \subset G).
Proof. by apply: (iffP idP) => [|<-]; [apply: mulGSid | apply: mulG_subr]. Qed.

Lemma mulGidPr G H : reflect (G * H = H) (G \subset H).
Proof. by apply: (iffP idP) => [|<-]; [apply: mulSGid | apply: mulG_subl]. Qed.

Lemma comm_group_setP G H : reflect (commute G H) (group_set (G * H)).
Proof.
rewrite /group_set (subsetP (mulG_subl _ _)) ?group1 // andbC.
have <-: #|G * H| <= #|H * G| by rewrite -invMG card_invg.
by rewrite -mulgA mulGS mulgA mulSG -eqEcard eq_sym; apply: eqP.
Qed.

Lemma card_lcosets G H : #|lcosets H G| = #|G : H|.
Proof. by rewrite -card_invg invg_lcosets !invGid. Qed.

(* Group Modularity equations *)

Lemma group_modl A B G : A \subset G -> A * (B :&: G) = A * B :&: G.
Proof.
move=> sAG; apply/eqP; rewrite eqEsubset subsetI mulgS ?subsetIl //.
rewrite -{2}mulGid mulgSS ?subsetIr //.
apply/subsetP => _ /setIP[/mulsgP[a b Aa Bb ->] Gab].
by rewrite mem_mulg // inE Bb -(groupMl _ (subsetP sAG _ Aa)).
Qed.

Lemma group_modr A B G : B \subset G -> (G :&: A) * B = G :&: A * B.
Proof.
move=> sBG; apply: invg_inj; rewrite !(invMg, invIg) invGid !(setIC G).
by rewrite group_modl // -invGid invSg.
Qed.

End GroupProp.

#[global] Hint Extern 0 (is_true (1%g \in _)) => apply: group1 : core.
#[global] Hint Extern 0 (is_true (0 < #|_|)) => apply: cardG_gt0 : core.
#[global] Hint Extern 0 (is_true (0 < #|_ : _|)) => apply: indexg_gt0 : core.

Notation "G :^ x" := (conjG_group G x) : Group_scope.

Notation "[ 'subg' G ]" := (subg_of G) : type_scope.
Notation "[ 'subg' G ]" := [set: subg_of G] : group_scope.
Notation "[ 'subg' G ]" := [set: subg_of G]%G : Group_scope.

Prenex Implicits subg sgval subg_of.
Bind Scope group_scope with subg_of.
Arguments subgK {gT G}.
Arguments sgvalK {gT G}.
Arguments subg_inj {gT G} [u1 u2] eq_u12 : rename.

Arguments trivgP {gT G}.
Arguments trivGP {gT G}.
Arguments lcoset_eqP {gT G x y}.
Arguments rcoset_eqP {gT G x y}.
Arguments mulGidPl {gT G H}.
Arguments mulGidPr {gT G H}.
Arguments comm_group_setP {gT G H}.
Arguments class_eqP {gT G x y}.
Arguments repr_classesP {gT G xG}.

Section GroupInter.

Variable gT : finGroupType.
Implicit Types A B : {set gT}.
Implicit Types G H : {group gT}.

Lemma group_setI G H : group_set (G :&: H).
Proof.
apply/group_setP; split=> [|x y]; rewrite !inE ?group1 //.
by case/andP=> Gx Hx; rewrite !groupMl.
Qed.

Canonical setI_group G H := group (group_setI G H).

Section Nary.

Variables (I : finType) (P : pred I) (F : I -> {group gT}).

Lemma group_set_bigcap : group_set (\bigcap_(i | P i) F i).
Proof.
by elim/big_rec: _ => [|i G _ gG]; rewrite -1?(insubdK 1%G gG) groupP.
Qed.

Canonical bigcap_group := group group_set_bigcap.

End Nary.

Lemma group_set_generated (A : {set gT}) : group_set <<A>>.
Proof. by rewrite unlock group_set_bigcap. Qed.

Canonical generated_group A := group (group_set_generated A).
Canonical gcore_group G A : {group _} := Eval hnf in [group of gcore G A].
Canonical commutator_group A B : {group _} := Eval hnf in [group of [~: A, B]].
Canonical joing_group A B : {group _} := Eval hnf in [group of A <*> B].
Canonical cycle_group x : {group _} := Eval hnf in [group of <[x]>].

Definition joinG G H := joing_group G H.

Definition subgroups A := [set G : {group gT} | G \subset A].

Lemma order_gt0 (x : gT) : 0 < #[x].
Proof. exact: cardG_gt0. Qed.

End GroupInter.

#[global] Hint Resolve order_gt0 : core.

Arguments generated_group _ _%g.
Arguments joing_group _ _%g _%g.
Arguments subgroups _ _%g.

Notation "G :&: H" := (setI_group G H) : Group_scope.
Notation "<< A >>"  := (generated_group A) : Group_scope.
Notation "<[ x ] >"  := (cycle_group x) : Group_scope.
Notation "[ ~: A1 , A2 , .. , An ]" :=
  (commutator_group .. (commutator_group A1 A2) .. An) : Group_scope.
Notation "A <*> B" := (joing_group A B) : Group_scope.
Notation "G * H" := (joinG G H) : Group_scope.
Prenex Implicits joinG subgroups.

Notation "\prod_ ( i <- r | P ) F" :=
  (\big[joinG/1%G]_(i <- r | P%B) F%G) : Group_scope.
Notation "\prod_ ( i <- r ) F" :=
  (\big[joinG/1%G]_(i <- r) F%G) : Group_scope.
Notation "\prod_ ( m <= i < n | P ) F" :=
  (\big[joinG/1%G]_(m <= i < n | P%B) F%G) : Group_scope.
Notation "\prod_ ( m <= i < n ) F" :=
  (\big[joinG/1%G]_(m <= i < n) F%G) : Group_scope.
Notation "\prod_ ( i | P ) F" :=
  (\big[joinG/1%G]_(i | P%B) F%G) : Group_scope.
Notation "\prod_ i F" :=
  (\big[joinG/1%G]_i F%G) : Group_scope.
Notation "\prod_ ( i : t | P ) F" :=
  (\big[joinG/1%G]_(i : t | P%B) F%G) (only parsing) : Group_scope.
Notation "\prod_ ( i : t ) F" :=
  (\big[joinG/1%G]_(i : t) F%G) (only parsing) : Group_scope.
Notation "\prod_ ( i < n | P ) F" :=
  (\big[joinG/1%G]_(i < n | P%B) F%G) : Group_scope.
Notation "\prod_ ( i < n ) F" :=
  (\big[joinG/1%G]_(i < n) F%G) : Group_scope.
Notation "\prod_ ( i 'in' A | P ) F" :=
  (\big[joinG/1%G]_(i in A | P%B) F%G) : Group_scope.
Notation "\prod_ ( i 'in' A ) F" :=
  (\big[joinG/1%G]_(i in A) F%G) : Group_scope.

Section Lagrange.

Variable gT : finGroupType.
Implicit Types G H K : {group gT}.

Lemma LagrangeI G H : (#|G :&: H| * #|G : H|)%N = #|G|.
Proof.
rewrite -[#|G|]sum1_card (partition_big_imset (rcoset H)) /=.
rewrite mulnC -sum_nat_const; apply: eq_bigr => _ /rcosetsP[x Gx ->].
rewrite -(card_rcoset _ x) -sum1_card; apply: eq_bigl => y.
by rewrite rcosetE (sameP eqP rcoset_eqP) group_modr ?sub1set // !inE.
Qed.

Lemma divgI G H : #|G| %/ #|G :&: H| = #|G : H|.
Proof. by rewrite -(LagrangeI G H) mulKn ?cardG_gt0. Qed.

Lemma divg_index G H : #|G| %/ #|G : H| = #|G :&: H|.
Proof. by rewrite -(LagrangeI G H) mulnK. Qed.

Lemma dvdn_indexg G H : #|G : H| %| #|G|.
Proof. by rewrite -(LagrangeI G H) dvdn_mull. Qed.

Theorem Lagrange G H : H \subset G -> (#|H| * #|G : H|)%N = #|G|.
Proof. by move/setIidPr=> sHG; rewrite -{1}sHG LagrangeI. Qed.

Lemma cardSg G H : H \subset G -> #|H| %| #|G|.
Proof. by move/Lagrange <-; rewrite dvdn_mulr. Qed.

Lemma lognSg p G H : G \subset H -> logn p #|G| <= logn p #|H|.
Proof. by move=> sGH; rewrite dvdn_leq_log ?cardSg. Qed.

Lemma piSg G H : G \subset H -> {subset \pi(gval G) <= \pi(gval H)}.
Proof.
move=> sGH p; rewrite !mem_primes !cardG_gt0 => /and3P[-> _ pG].
exact: dvdn_trans (cardSg sGH).
Qed.

Lemma divgS G H : H \subset G -> #|G| %/ #|H| = #|G : H|.
Proof. by move/Lagrange <-; rewrite mulKn. Qed.

Lemma divg_indexS G H : H \subset G -> #|G| %/ #|G : H| = #|H|.
Proof. by move/Lagrange <-; rewrite mulnK. Qed.

Lemma coprimeSg G H p : H \subset G -> coprime #|G| p -> coprime #|H| p.
Proof. by move=> sHG; apply: coprime_dvdl (cardSg sHG). Qed.

Lemma coprimegS G H p : H \subset G -> coprime p #|G| -> coprime p #|H|.
Proof. by move=> sHG; apply: coprime_dvdr (cardSg sHG). Qed.

Lemma indexJg G H x : #|G :^ x : H :^ x| = #|G : H|.
Proof. by rewrite -!divgI -conjIg !cardJg. Qed.

Lemma indexgg G : #|G : G| = 1%N.
Proof. by rewrite -divgS // divnn cardG_gt0. Qed.

Lemma rcosets_id G : rcosets G G = [set G : {set gT}].
Proof.
apply/esym/eqP; rewrite eqEcard sub1set [#|_|]indexgg cards1 andbT.
by apply/rcosetsP; exists 1; rewrite ?mulg1.
Qed.

Lemma Lagrange_index G H K :
  H \subset G -> K \subset H -> (#|G : H| * #|H : K|)%N = #|G : K|.
Proof.
move=> sHG sKH; apply/eqP; rewrite mulnC -(eqn_pmul2l (cardG_gt0 K)).
by rewrite mulnA !Lagrange // (subset_trans sKH).
Qed.

Lemma indexgI G H : #|G : G :&: H| = #|G : H|.
Proof. by rewrite -divgI divgS ?subsetIl. Qed.

Lemma indexgS G H K : H \subset K -> #|G : K| %| #|G : H|.
Proof.
move=> sHK; rewrite -(@dvdn_pmul2l #|G :&: K|) ?cardG_gt0 // LagrangeI.
by rewrite -(Lagrange (setIS G sHK)) mulnAC LagrangeI dvdn_mulr.
Qed.

Lemma indexSg G H K : H \subset K -> K \subset G -> #|K : H| %| #|G : H|.
Proof.
move=> sHK sKG; rewrite -(@dvdn_pmul2l #|H|) ?cardG_gt0 //.
by rewrite !Lagrange ?(cardSg, subset_trans sHK).
Qed.

Lemma indexg_eq1 G H : (#|G : H| == 1%N) = (G \subset H).
Proof.
rewrite eqn_leq -(leq_pmul2l (cardG_gt0 (G :&: H))) LagrangeI muln1.
by rewrite indexg_gt0 andbT (sameP setIidPl eqP) eqEcard subsetIl.
Qed.

Lemma indexg_gt1 G H : (#|G : H| > 1) = ~~ (G \subset H).
Proof. by rewrite -indexg_eq1 eqn_leq indexg_gt0 andbT -ltnNge. Qed.

Lemma index1g G H : H \subset G -> #|G : H| = 1%N -> H :=: G.
Proof. by move=> sHG iHG; apply/eqP; rewrite eqEsubset sHG -indexg_eq1 iHG. Qed.

Lemma indexg1 G : #|G : 1| = #|G|.
Proof. by rewrite -divgS ?sub1G // cards1 divn1. Qed.

Lemma indexMg G A : #|G * A : G| = #|A : G|.
Proof.
apply/eq_card/setP/eqP; rewrite eqEsubset andbC imsetS ?mulG_subr //.
by apply/subsetP=> _ /rcosetsP[x GAx ->]; rewrite mem_rcosets.
Qed.

Lemma rcosets_partition_mul G H : partition (rcosets H G) (H * G).
Proof.
set HG := H * G; have sGHG: {subset G <= HG} by apply/subsetP/mulG_subr.
have defHx x: x \in HG -> [set y in HG | rcoset H x == rcoset H y] = H :* x.
  move=> HGx; apply/setP=> y; rewrite inE !rcosetE (sameP eqP rcoset_eqP).
  by rewrite rcoset_sym; apply/andb_idl/subsetP; rewrite mulGS sub1set.
have:= preim_partitionP (rcoset H) HG; congr (partition _ _); apply/setP=> Hx.
apply/imsetP/idP=> [[x HGx ->] | ]; first by rewrite defHx // mem_rcosets.
by case/rcosetsP=> x /sGHG-HGx ->; exists x; rewrite ?defHx.
Qed.

Lemma rcosets_partition G H : H \subset G -> partition (rcosets H G) G.
Proof. by move=> sHG; have:= rcosets_partition_mul G H; rewrite mulSGid. Qed.

Lemma LagrangeMl G H : (#|G| * #|H : G|)%N = #|G * H|.
Proof.
rewrite mulnC -(card_uniform_partition _ (rcosets_partition_mul H G)) //.
by move=> _ /rcosetsP[x Hx ->]; rewrite card_rcoset.
Qed.

Lemma LagrangeMr G H : (#|G : H| * #|H|)%N = #|G * H|.
Proof. by rewrite mulnC LagrangeMl -card_invg invMg !invGid. Qed.

Lemma mul_cardG G H : (#|G| * #|H| = #|G * H|%g * #|G :&: H|)%N.
Proof. by rewrite -LagrangeMr -(LagrangeI G H) -mulnA mulnC. Qed.

Lemma dvdn_cardMg G H : #|G * H| %| #|G| * #|H|.
Proof. by rewrite mul_cardG dvdn_mulr. Qed.

Lemma cardMg_divn G H : #|G * H| = (#|G| * #|H|) %/ #|G :&: H|.
Proof. by rewrite mul_cardG mulnK ?cardG_gt0. Qed.

Lemma cardIg_divn G H : #|G :&: H| = (#|G| * #|H|) %/ #|G * H|.
Proof. by rewrite mul_cardG mulKn // (cardD1 (1 * 1)) mem_mulg. Qed.

Lemma TI_cardMg G H : G :&: H = 1 -> #|G * H| = (#|G| * #|H|)%N.
Proof. by move=> tiGH; rewrite mul_cardG tiGH cards1 muln1. Qed.

Lemma cardMg_TI G H : #|G| * #|H| <= #|G * H| -> G :&: H = 1.
Proof.
move=> leGH; apply: card_le1_trivg.
rewrite -(@leq_pmul2l #|G * H|); first by rewrite -mul_cardG muln1.
by apply: leq_trans leGH; rewrite muln_gt0 !cardG_gt0.
Qed.

Lemma coprime_TIg G H : coprime #|G| #|H| -> G :&: H = 1.
Proof.
move=> coGH; apply/eqP; rewrite trivg_card1 -dvdn1 -{}(eqnP coGH).
by rewrite dvdn_gcd /= {2}setIC !cardSg ?subsetIl.
Qed.

Lemma prime_TIg G H : prime #|G| -> ~~ (G \subset H) -> G :&: H = 1.
Proof.
case/primeP=> _ /(_ _ (cardSg (subsetIl G H))).
rewrite (sameP setIidPl eqP) eqEcard subsetIl => /pred2P[/card1_trivg|] //= ->.
by case/negP.
Qed.

Lemma prime_meetG G H : prime #|G| -> G :&: H != 1 -> G \subset H.
Proof. by move=> prG; apply: contraR; move/prime_TIg->. Qed.

Lemma coprime_cardMg G H : coprime #|G| #|H| -> #|G * H| = (#|G| * #|H|)%N.
Proof. by move=> coGH; rewrite TI_cardMg ?coprime_TIg. Qed.

Lemma coprime_index_mulG G H K :
  H \subset G -> K \subset G -> coprime #|G : H| #|G : K| -> H * K = G.
Proof.
move=> sHG sKG co_iG_HK; apply/eqP; rewrite eqEcard mul_subG //=.
rewrite -(@leq_pmul2r #|H :&: K|) ?cardG_gt0 // -mul_cardG.
rewrite -(Lagrange sHG) -(LagrangeI K H) mulnAC setIC -mulnA.
rewrite !leq_pmul2l ?cardG_gt0 // dvdn_leq // -(Gauss_dvdr _ co_iG_HK).
by rewrite -(indexgI K) Lagrange_index ?indexgS ?subsetIl ?subsetIr.
Qed.

End Lagrange.

Section GeneratedGroup.

Variable gT : finGroupType.
Implicit Types x y z : gT.
Implicit Types A B C D : {set gT}.
Implicit Types G H K : {group gT}.

Lemma subset_gen A : A \subset <<A>>.
Proof. rewrite [@generated]unlock; exact/bigcapsP. Qed.

Lemma sub_gen A B : A \subset B -> A \subset <<B>>.
Proof. by move/subset_trans=> -> //; apply: subset_gen. Qed.

Lemma mem_gen x A : x \in A -> x \in <<A>>.
Proof. exact: subsetP (subset_gen A) x. Qed.

Lemma generatedP x A : reflect (forall G, A \subset G -> x \in G) (x \in <<A>>).
Proof. rewrite [@generated]unlock; exact: bigcapP. Qed.

Lemma gen_subG A G : (<<A>> \subset G) = (A \subset G).
Proof.
apply/idP/idP=> [|sAG]; first exact: subset_trans (subset_gen A).
by apply/subsetP=> x /generatedP; apply.
Qed.

Lemma genGid G : <<G>> = G.
Proof. by apply/eqP; rewrite eqEsubset gen_subG subset_gen andbT. Qed.

Lemma genGidG G : <<G>>%G = G.
Proof. by apply: val_inj; apply: genGid. Qed.

Lemma gen_set_id A : group_set A -> <<A>> = A.
Proof. by move=> gA; apply: (genGid (group gA)). Qed.

Lemma genS A B : A \subset B -> <<A>> \subset <<B>>.
Proof. by move=> sAB; rewrite gen_subG sub_gen. Qed.

Lemma gen0 : <<set0>> = 1 :> {set gT}.
Proof. by apply/eqP; rewrite eqEsubset sub1G gen_subG sub0set. Qed.

Lemma gen_expgs A : {n | <<A>> = (1 |: A) ^+ n}.
Proof.
set B := (1 |: A); pose N := #|gT|.
have BsubG n : B ^+ n \subset <<A>>.
  by elim: n => [|n IHn]; rewrite ?expgS ?mul_subG ?subUset ?sub1G ?subset_gen.
have B_1 n : 1 \in B ^+ n.
  by elim: n => [|n IHn]; rewrite ?set11 // expgS mulUg mul1g inE IHn.
case: (pickP (fun i : 'I_N => B ^+ i.+1 \subset B ^+ i)) => [n fixBn | no_fix].
  exists n; apply/eqP; rewrite eqEsubset BsubG andbT.
  rewrite -[B ^+ n]gen_set_id ?genS ?subsetUr //.
    by apply: subset_trans fixBn; rewrite expgS mulUg subsetU ?mulg_subl ?orbT.
  rewrite /group_set B_1 /=.
  elim: {2}(n : nat) => [|m IHm]; first by rewrite mulg1.
  by apply: subset_trans fixBn; rewrite !expgSr mulgA mulSg.
suffices: N < #|B ^+ N| by rewrite ltnNge max_card.
have [] := ubnPgeq N; elim=> [|n IHn] lt_nN; first by rewrite cards1.
apply: leq_ltn_trans (IHn (ltnW lt_nN)) (proper_card _).
by rewrite /proper (no_fix (Ordinal lt_nN)) expgS mulUg mul1g subsetUl.
Qed.

Lemma gen_prodgP A x :
  reflect (exists n, exists2 c, forall i : 'I_n, c i \in A & x = \prod_i c i)
          (x \in <<A>>).
Proof.
apply: (iffP idP) => [|[n [c Ac ->]]]; last first.
  by apply: group_prod => i _; rewrite mem_gen ?Ac.
have [n ->] := gen_expgs A; rewrite /expgn /expgn_rec Monoid.iteropE /=.
rewrite -[n]card_ord -big_const => /prodsgP[/= c Ac def_x]. 
have{Ac def_x} ->: x = \prod_(i | c i \in A) c i.
  rewrite big_mkcond {x}def_x; apply: eq_bigr => i _.
  by case/setU1P: (Ac i isT) => -> //; rewrite if_same.
have [e <- [_ /= mem_e] _] := big_enumP [preim c of A].
pose t := in_tuple e; rewrite -[e]/(val t) big_tuple.
by exists (size e), (c \o tnth t) => // i; rewrite -mem_e mem_tnth.
Qed.

Lemma genD A B : A \subset <<A :\: B>> -> <<A :\: B>> = <<A>>.
Proof.
by move=> sAB; apply/eqP; rewrite eqEsubset genS (subsetDl, gen_subG).
Qed.

Lemma genV A : <<A^-1>> = <<A>>.
Proof.
apply/eqP; rewrite eqEsubset !gen_subG -!(invSg _ <<_>>) invgK.
by rewrite !invGid !subset_gen.
Qed.

Lemma genJ A z : <<A :^z>> = <<A>> :^ z.
Proof.
by apply/eqP; rewrite eqEsubset sub_conjg !gen_subG conjSg -?sub_conjg !sub_gen.
Qed.

Lemma conjYg A B z : (A <*> B) :^z = A :^ z <*> B :^ z.
Proof. by rewrite -genJ conjUg. Qed.

Lemma genD1 A x : x \in <<A :\ x>> -> <<A :\ x>> = <<A>>.
Proof.
move=> gA'x; apply/eqP; rewrite eqEsubset genS; last by rewrite subsetDl.
rewrite gen_subG; apply/subsetP=> y Ay.
by case: (y =P x) => [-> //|]; move/eqP=> nyx; rewrite mem_gen // !inE nyx.
Qed.

Lemma genD1id A : <<A^#>> = <<A>>.
Proof. by rewrite genD1 ?group1. Qed.

Notation joingT := (@joing gT) (only parsing).
Notation joinGT := (@joinG gT) (only parsing).

Lemma joingE A B : A <*> B = <<A :|: B>>. Proof. by []. Qed.

Lemma joinGE G H : (G * H)%G = (G <*> H)%G. Proof. by []. Qed.

Lemma joingC : commutative joingT.
Proof. by move=> A B; rewrite /joing setUC. Qed.

Lemma joing_idr A B : A <*> <<B>> = A <*> B.
Proof.
apply/eqP; rewrite eqEsubset gen_subG subUset gen_subG /=.
by rewrite -subUset subset_gen genS // setUS // subset_gen.
Qed.

Lemma joing_idl A B : <<A>> <*> B = A <*> B.
Proof. by rewrite -!(joingC B) joing_idr. Qed.

Lemma joing_subl A B : A \subset A <*> B.
Proof. by rewrite sub_gen ?subsetUl. Qed.

Lemma joing_subr A B : B \subset A <*> B.
Proof. by rewrite sub_gen ?subsetUr. Qed.

Lemma join_subG A B G : (A <*> B \subset G) = (A \subset G) && (B \subset G).
Proof. by rewrite gen_subG subUset. Qed.

Lemma joing_idPl G A : reflect (G <*> A = G) (A \subset G).
Proof.
apply: (iffP idP) => [sHG | <-]; last by rewrite joing_subr.
by rewrite joingE (setUidPl sHG) genGid.
Qed.

Lemma joing_idPr A G : reflect (A <*> G = G) (A \subset G).
Proof. by rewrite joingC; apply: joing_idPl. Qed.

Lemma joing_subP A B G :
  reflect (A \subset G /\ B \subset G) (A <*> B \subset G).
Proof. by rewrite join_subG; apply: andP. Qed.

Lemma joing_sub A B C : A <*> B = C -> A \subset C /\ B \subset C.
Proof. by move <-; apply/joing_subP. Qed.

Lemma genDU A B C : A \subset C -> <<C :\: A>> = <<B>> -> <<A :|: B>> = <<C>>.
Proof.
move=> sAC; rewrite -joingE -joing_idr => <- {B}; rewrite joing_idr.
by congr <<_>>; rewrite setDE setUIr setUCr setIT; apply/setUidPr.
Qed.

Lemma joingA : associative joingT.
Proof. by move=> A B C; rewrite joing_idl joing_idr /joing setUA. Qed.

Lemma joing1G G : 1 <*> G = G.
Proof. by rewrite -gen0 joing_idl /joing set0U genGid. Qed.

Lemma joingG1 G : G <*> 1 = G.
Proof. by rewrite joingC joing1G. Qed.

Lemma genM_join G H : <<G * H>> = G <*> H.
Proof.
apply/eqP; rewrite eqEsubset gen_subG /= -{1}[G <*> H]mulGid.
rewrite genS; last by rewrite subUset mulG_subl mulG_subr.
by rewrite mulgSS ?(sub_gen, subsetUl, subsetUr).
Qed.

Lemma mulG_subG G H K : (G * H \subset K) = (G \subset K) && (H \subset K).
Proof. by rewrite -gen_subG genM_join join_subG. Qed.

Lemma mulGsubP K H G : reflect (K \subset G /\ H \subset G) (K * H \subset G).
Proof. by rewrite mulG_subG; apply: andP. Qed.

Lemma mulG_sub K H A : K * H = A -> K \subset A /\ H \subset A.
Proof. by move <-; rewrite mulG_subl mulG_subr. Qed.

Lemma trivMg G H : (G * H == 1) = (G :==: 1) && (H :==: 1).
Proof.
by rewrite !eqEsubset -{2}[1]mulGid mulgSS ?sub1G // !andbT mulG_subG.
Qed.

Lemma comm_joingE G H : commute G H -> G <*> H = G * H.
Proof.
by move/comm_group_setP=> gGH; rewrite -genM_join; apply: (genGid (group gGH)).
Qed.

Lemma joinGC : commutative joinGT.
Proof. by move=> G H; apply: val_inj; apply: joingC. Qed.

Lemma joinGA : associative joinGT.
Proof. by move=> G H K; apply: val_inj; apply: joingA. Qed.

Lemma join1G : left_id 1%G joinGT.
Proof. by move=> G; apply: val_inj; apply: joing1G. Qed.

Lemma joinG1 : right_id 1%G joinGT.
Proof. by move=> G; apply: val_inj; apply: joingG1. Qed.

HB.instance Definition _ := Monoid.isComLaw.Build {group gT} 1%G joinGT
  joinGA joinGC join1G.

Lemma bigprodGEgen I r (P : pred I) (F : I -> {set gT}) :
  (\prod_(i <- r | P i) <<F i>>)%G :=: << \bigcup_(i <- r | P i) F i >>.
Proof.
elim/big_rec2: _ => /= [|i A _ _ ->]; first by rewrite gen0.
by rewrite joing_idl joing_idr.
Qed.

Lemma bigprodGE I r (P : pred I) (F : I -> {group gT}) :
  (\prod_(i <- r | P i) F i)%G :=: << \bigcup_(i <- r | P i) F i >>.
Proof.
rewrite -bigprodGEgen /=; apply: congr_group.
by apply: eq_bigr => i _; rewrite genGidG.
Qed.

Lemma mem_commg A B x y : x \in A -> y \in B -> [~ x, y] \in [~: A, B].
Proof. by move=> Ax By; rewrite mem_gen ?imset2_f. Qed.

Lemma commSg A B C : A \subset B -> [~: A, C] \subset [~: B, C].
Proof. by move=> sAC; rewrite genS ?imset2S. Qed.

Lemma commgS A B C : B \subset C -> [~: A, B] \subset [~: A, C].
Proof. by move=> sBC; rewrite genS ?imset2S. Qed.

Lemma commgSS A B C D :
  A \subset B -> C \subset D -> [~: A, C] \subset [~: B, D].
Proof. by move=> sAB sCD; rewrite genS ?imset2S. Qed.

Lemma der1_subG G : [~: G, G] \subset G.
Proof.
by rewrite gen_subG; apply/subsetP=> _ /imset2P[x y Gx Gy ->]; apply: groupR.
Qed.

Lemma comm_subG A B G : A \subset G -> B \subset G -> [~: A, B] \subset G.
Proof.
by move=> sAG sBG; apply: subset_trans (der1_subG G); apply: commgSS.
Qed.

Lemma commGC A B : [~: A, B] = [~: B, A].
Proof.
rewrite -[[~: A, B]]genV; congr <<_>>; apply/setP=> z; rewrite inE.
by apply/imset2P/imset2P=> [] [x y Ax Ay]; last rewrite -{1}(invgK z);
  rewrite -invg_comm => /invg_inj->; exists y x.
Qed.

Lemma conjsRg A B x : [~: A, B] :^ x = [~: A :^ x, B :^ x].
Proof.
wlog suffices: A B x / [~: A, B] :^ x \subset [~: A :^ x, B :^ x].
  move=> subJ; apply/eqP; rewrite eqEsubset subJ /= -sub_conjgV.
  by rewrite -{2}(conjsgK x A) -{2}(conjsgK x B).
rewrite -genJ gen_subG; apply/subsetP=> _ /imsetP[_ /imset2P[y z Ay Bz ->] ->].
by rewrite conjRg mem_commg ?memJ_conjg.
Qed.

End GeneratedGroup.

Arguments gen_prodgP {gT A x}.
Arguments joing_idPl {gT G A}.
Arguments joing_idPr {gT A G}.
Arguments mulGsubP {gT K H G}.
Arguments joing_subP {gT A B G}.

Section Cycles.

(* Elementary properties of cycles and order, needed in perm.v.  *)
(* More advanced results on the structure of cyclic groups will  *)
(* be given in cyclic.v.                                         *)

Variable gT : finGroupType.
Implicit Types x y : gT.
Implicit Types G : {group gT}.

Import Monoid.Theory.

Lemma cycle1 : <[1]> = [1 gT].
Proof. exact: genGid. Qed.

Lemma order1 : #[1 : gT] = 1%N.
Proof. by rewrite /order cycle1 cards1. Qed.

Lemma cycle_id x : x \in <[x]>.
Proof. by rewrite mem_gen // set11. Qed.

Lemma mem_cycle x i : x ^+ i \in <[x]>.
Proof. by rewrite groupX // cycle_id. Qed.

Lemma cycle_subG x G : (<[x]> \subset G) = (x \in G).
Proof. by rewrite gen_subG sub1set. Qed.

Lemma cycle_eq1 x : (<[x]> == 1) = (x == 1).
Proof. by rewrite eqEsubset sub1G andbT cycle_subG inE. Qed.

Lemma orderE x : #[x] = #|<[x]>|. Proof. by []. Qed.

Lemma order_eq1 x : (#[x] == 1%N) = (x == 1).
Proof. by rewrite -trivg_card1 cycle_eq1. Qed.

Lemma order_gt1 x : (#[x] > 1) = (x != 1).
Proof. by rewrite ltnNge -trivg_card_le1 cycle_eq1. Qed.

Lemma cycle_traject x : <[x]> =i traject (mulg x) 1 #[x].
Proof.
set t := _ 1; apply: fsym; apply/subset_cardP; last first.
  by apply/subsetP=> _ /trajectP[i _ ->]; rewrite -iteropE mem_cycle.
rewrite (card_uniqP _) ?size_traject //; case def_n: #[_] => // [n].
rewrite looping_uniq; apply: contraL (card_size (t n)) => /loopingP t_xi.
rewrite -ltnNge size_traject -def_n ?subset_leq_card //.
rewrite -(eq_subset_r (in_set _)) {}/t; set G := finset _.
rewrite -[x]mulg1 -[G]gen_set_id ?genS ?sub1set ?inE ?(t_xi 1%N)//.
apply/group_setP; split=> [|y z]; rewrite !inE ?(t_xi 0) //.
by do 2!case/trajectP=> ? _ ->; rewrite -!iteropE -expgD [x ^+ _]iteropE.
Qed.

Lemma cycle2g x : #[x] = 2 -> <[x]> = [set 1; x].
Proof. by move=> ox; apply/setP=> y; rewrite cycle_traject ox !inE mulg1. Qed.

Lemma cyclePmin x y : y \in <[x]> -> {i | i < #[x] & y = x ^+ i}.
Proof.
rewrite cycle_traject; set tx := traject _ _ #[x] => tx_y; pose i := index y tx.
have lt_i_x : i < #[x] by rewrite -index_mem size_traject in tx_y.
by exists i; rewrite // [x ^+ i]iteropE /= -(nth_traject _ lt_i_x) nth_index.
Qed.

Lemma cycleP x y : reflect (exists i, y = x ^+ i) (y \in <[x]>).
Proof.
by apply: (iffP idP) => [/cyclePmin[i _]|[i ->]]; [exists i | apply: mem_cycle].
Qed.

Lemma expg_order x : x ^+ #[x] = 1.
Proof.
have: uniq (traject (mulg x) 1 #[x]).
  by apply/card_uniqP; rewrite size_traject -(eq_card (cycle_traject x)).
case/cyclePmin: (mem_cycle x #[x]) => [] [//|i] ltix.
rewrite -(subnKC ltix) addSnnS /= expgD; move: (_ - _) => j x_j1.
case/andP=> /trajectP[]; exists j; first exact: leq_addl.
by apply: (mulgI (x ^+ i.+1)); rewrite -iterSr iterS -iteropE -expgS mulg1.
Qed.

Lemma expg_mod p k x : x ^+ p = 1 -> x ^+ (k %% p) = x ^+ k.
Proof.
move=> xp.
by rewrite {2}(divn_eq k p) expgD mulnC expgM xp expg1n mul1g.
Qed.

Lemma expg_mod_order x i : x ^+ (i %% #[x]) = x ^+ i.
Proof. by rewrite expg_mod // expg_order. Qed.

Lemma invg_expg x : x^-1 = x ^+ #[x].-1.
Proof. by apply/eqP; rewrite eq_invg_mul -expgS prednK ?expg_order. Qed.

Lemma invg2id x : #[x] = 2 -> x^-1 = x.
Proof. by move=> ox; rewrite invg_expg ox. Qed.

Lemma cycleX x i : <[x ^+ i]> \subset <[x]>.
Proof. by rewrite cycle_subG; apply: mem_cycle. Qed.

Lemma cycleV x : <[x^-1]> = <[x]>.
Proof.
by apply/eqP; rewrite eq_sym eqEsubset !cycle_subG groupV -groupV !cycle_id.
Qed.

Lemma orderV x : #[x^-1] = #[x].
Proof. by rewrite /order cycleV. Qed.

Lemma cycleJ x y : <[x ^ y]> = <[x]> :^ y.
Proof. by rewrite -genJ conjg_set1. Qed.

Lemma orderJ x y : #[x ^ y] = #[x].
Proof. by rewrite /order cycleJ cardJg. Qed.

End Cycles.

Section Normaliser.

Variable gT : finGroupType.
Implicit Types x y z : gT.
Implicit Types A B C D : {set gT}.
Implicit Type G H K : {group gT}.

Lemma normP x A : reflect (A :^ x = A) (x \in 'N(A)).
Proof.
suffices ->: (x \in 'N(A)) = (A :^ x == A) by apply: eqP.
by rewrite eqEcard cardJg leqnn andbT inE.
Qed.
Arguments normP {x A}.

Lemma group_set_normaliser A : group_set 'N(A).
Proof.
apply/group_setP; split=> [|x y Nx Ny]; rewrite inE ?conjsg1 //.
by rewrite conjsgM !(normP _).
Qed.

Canonical normaliser_group A := group (group_set_normaliser A).

Lemma normsP A B : reflect {in A, normalised B} (A \subset 'N(B)).
Proof.
apply: (iffP subsetP) => nBA x Ax; last by rewrite inE nBA //.
by apply/normP; apply: nBA.
Qed.
Arguments normsP {A B}.

Lemma memJ_norm x y A : x \in 'N(A) -> (y ^ x \in A) = (y \in A).
Proof. by move=> Nx; rewrite -{1}(normP Nx) memJ_conjg. Qed.

Lemma norms_cycle x y : (<[y]> \subset 'N(<[x]>)) = (x ^ y \in <[x]>).
Proof. by rewrite cycle_subG inE -cycleJ cycle_subG. Qed.

Lemma norm1 : 'N(1) =  setT :> {set gT}.
Proof. by apply/setP=> x; rewrite !inE conjs1g subxx. Qed.

Lemma norms1 A : A \subset 'N(1).
Proof. by rewrite norm1 subsetT. Qed.

Lemma normCs A : 'N(~: A) = 'N(A).
Proof. by apply/setP=> x; rewrite -groupV !inE conjCg setCS sub_conjg. Qed.

Lemma normG G : G \subset 'N(G).
Proof. by apply/normsP; apply: conjGid. Qed.

Lemma normT : 'N([set: gT]) = [set: gT].
Proof. by apply/eqP; rewrite -subTset normG. Qed.

Lemma normsG A G : A \subset G -> A \subset 'N(G).
Proof. by move=> sAG; apply: subset_trans (normG G). Qed.

Lemma normC A B : A \subset 'N(B) -> commute A B.
Proof.
move/subsetP=> nBA; apply/setP=> u.
apply/mulsgP/mulsgP=> [[x y Ax By] | [y x By Ax]] -> {u}.
  by exists (y ^ x^-1) x; rewrite -?conjgCV // memJ_norm // groupV nBA.
by exists x (y ^ x); rewrite -?conjgC // memJ_norm // nBA.
Qed.

Lemma norm_joinEl G H : G \subset 'N(H) -> G <*> H = G * H.
Proof. by move/normC/comm_joingE. Qed.

Lemma norm_joinEr G H : H \subset 'N(G) -> G <*> H = G * H.
Proof. by move/normC=> cHG; apply: comm_joingE. Qed.

Lemma norm_rlcoset G x : x \in 'N(G) -> G :* x = x *: G.
Proof. by rewrite -sub1set => /normC. Qed.

Lemma rcoset_mul G x y : x \in 'N(G) -> (G :* x) * (G :* y) = G :* (x * y).
Proof.
move/norm_rlcoset=> GxxG.
by rewrite mulgA -(mulgA _ _ G) -GxxG mulgA mulGid -mulgA mulg_set1.
Qed.

Lemma normJ A x : 'N(A :^ x) = 'N(A) :^ x.
Proof.
by apply/setP=> y; rewrite mem_conjg !inE -conjsgM conjgCV conjsgM conjSg.
Qed.

Lemma norm_conj_norm x A B :
  x \in 'N(A) -> (A \subset 'N(B :^ x)) = (A \subset 'N(B)).
Proof. by move=> Nx; rewrite normJ -sub_conjgV (normP _) ?groupV. Qed.

Lemma norm_gen A : 'N(A) \subset 'N(<<A>>).
Proof. by apply/normsP=> x Nx; rewrite -genJ (normP Nx). Qed.

Lemma class_norm x G : G \subset 'N(x ^: G).
Proof. by apply/normsP=> y; apply: classGidr. Qed.

Lemma class_normal x G : x \in G -> x ^: G <| G.
Proof. by move=> Gx; rewrite /normal class_norm class_subG. Qed.

Lemma class_sub_norm G A x : G \subset 'N(A) -> (x ^: G \subset A) = (x \in A).
Proof.
move=> nAG; apply/subsetP/idP=> [-> // | Ax xy]; first exact: class_refl.
by case/imsetP=> y Gy ->; rewrite memJ_norm ?(subsetP nAG).
Qed.

Lemma class_support_norm A G : G \subset 'N(class_support A G).
Proof. by apply/normsP; apply: class_supportGidr. Qed.

Lemma class_support_sub_norm A B G :
  A \subset G -> B \subset 'N(G) -> class_support A B \subset G.
Proof.
move=> sAG nGB; rewrite class_supportEr.
by apply/bigcupsP=> x Bx; rewrite -(normsP nGB x Bx) conjSg.
Qed.

Section norm_trans.

Variables (A B C D : {set gT}).
Hypotheses (nBA : A \subset 'N(B)) (nCA : A \subset 'N(C)).

Lemma norms_gen : A \subset 'N(<<B>>).
Proof. exact: subset_trans nBA (norm_gen B). Qed.

Lemma norms_norm : A \subset 'N('N(B)).
Proof. by apply/normsP=> x Ax; rewrite -normJ (normsP nBA). Qed.

Lemma normsI : A \subset 'N(B :&: C).
Proof. by apply/normsP=> x Ax; rewrite conjIg !(normsP _ x Ax). Qed.

Lemma normsU : A \subset 'N(B :|: C).
Proof. by apply/normsP=> x Ax; rewrite conjUg !(normsP _ x Ax). Qed.

Lemma normsIs : B \subset 'N(D) -> A :&: B \subset 'N(C :&: D).
Proof.
move/normsP=> nDB; apply/normsP=> x; case/setIP=> Ax Bx.
by rewrite conjIg (normsP nCA) ?nDB.
Qed.

Lemma normsD : A \subset 'N(B :\: C).
Proof. by apply/normsP=> x Ax; rewrite conjDg !(normsP _ x Ax). Qed.

Lemma normsM : A \subset 'N(B * C).
Proof. by apply/normsP=> x Ax; rewrite conjsMg !(normsP _ x Ax). Qed.

Lemma normsY : A \subset 'N(B <*> C).
Proof. by apply/normsP=> x Ax; rewrite -genJ conjUg !(normsP _ x Ax). Qed.

Lemma normsR : A \subset 'N([~: B, C]).
Proof. by apply/normsP=> x Ax; rewrite conjsRg !(normsP _ x Ax). Qed.

Lemma norms_class_support : A \subset 'N(class_support B C).
Proof.
apply/subsetP=> x Ax; rewrite inE sub_conjg class_supportEr.
apply/bigcupsP=> y Cy; rewrite -sub_conjg -conjsgM conjgC conjsgM.
by rewrite (normsP nBA) // bigcup_sup ?memJ_norm ?(subsetP nCA).
Qed.

End norm_trans.

Lemma normsIG A B G : A \subset 'N(B) -> A :&: G \subset 'N(B :&: G).
Proof. by move/normsIs->; rewrite ?normG. Qed.

Lemma normsGI A B G : A \subset 'N(B) -> G :&: A \subset 'N(G :&: B).
Proof. by move=> nBA; rewrite !(setIC G) normsIG. Qed.

Lemma norms_bigcap I r (P : pred I) A (B_ : I -> {set gT}) :
    A \subset \bigcap_(i <- r | P i) 'N(B_ i) ->
  A \subset 'N(\bigcap_(i <- r | P i) B_ i).
Proof.
elim/big_rec2: _ => [|i B N _ IH /subsetIP[nBiA /IH]]; last exact: normsI.
by rewrite normT.
Qed.

Lemma norms_bigcup I r (P : pred I) A (B_ : I -> {set gT}) :
    A \subset \bigcap_(i <- r | P i) 'N(B_ i) ->
  A \subset 'N(\bigcup_(i <- r | P i) B_ i).
Proof.
move=> nBA; rewrite -normCs setC_bigcup norms_bigcap //.
by rewrite (eq_bigr _ (fun _ _ => normCs _)).
Qed.

Lemma normsD1 A B : A \subset 'N(B) -> A \subset 'N(B^#).
Proof. by move/normsD->; rewrite ?norms1. Qed.

Lemma normD1 A : 'N(A^#) = 'N(A).
Proof.
apply/eqP; rewrite eqEsubset normsD1 //.
rewrite -{2}(setID A 1) setIC normsU //; apply/normsP=> x _; apply/setP=> y.
by rewrite conjIg conjs1g !inE mem_conjg; case: eqP => // ->; rewrite conj1g.
Qed.

Lemma normalP A B : reflect (A \subset B /\ {in B, normalised A}) (A <| B).
Proof. by apply: (iffP andP)=> [] [sAB]; move/normsP. Qed.

Lemma normal_sub A B : A <| B -> A \subset B.
Proof. by case/andP. Qed.

Lemma normal_norm A B : A <| B -> B \subset 'N(A).
Proof. by case/andP. Qed.

Lemma normalS G H K : K \subset H -> H \subset G -> K <| G -> K <| H.
Proof.
by move=> sKH sHG /andP[_ nKG]; rewrite /(K <| _) sKH (subset_trans sHG).
Qed.

Lemma normal1 G : 1 <| G.
Proof. by rewrite /normal sub1set group1 norms1. Qed.

Lemma normal_refl G : G <| G.
Proof. by rewrite /(G <| _) normG subxx. Qed.

Lemma normalG G : G <| 'N(G).
Proof. by rewrite /(G <| _) normG subxx. Qed.

Lemma normalSG G H : H \subset G -> H <| 'N_G(H).
Proof. by move=> sHG; rewrite /normal subsetI sHG normG subsetIr. Qed.

Lemma normalJ A B x : (A :^ x <| B :^ x) = (A <| B).
Proof. by rewrite /normal normJ !conjSg. Qed.

Lemma normalM G A B : A <| G -> B <| G -> A * B <| G.
Proof.
by case/andP=> sAG nAG /andP[sBG nBG]; rewrite /normal mul_subG ?normsM.
Qed.

Lemma normalY G A B : A <| G -> B <| G -> A <*> B <| G.
Proof.
by case/andP=> sAG ? /andP[sBG ?]; rewrite /normal join_subG sAG sBG ?normsY.
Qed.

Lemma normalYl G H : (H <| H <*> G) = (G \subset 'N(H)).
Proof. by rewrite /normal joing_subl join_subG normG. Qed.

Lemma normalYr G H : (H <| G <*> H) = (G \subset 'N(H)).
Proof. by rewrite joingC normalYl. Qed.

Lemma normalI G A B : A <| G -> B <| G -> A :&: B <| G.
Proof.
by case/andP=> sAG nAG /andP[_ nBG]; rewrite /normal subIset ?sAG // normsI.
Qed.

Lemma norm_normalI G A : G \subset 'N(A) -> G :&: A <| G.
Proof. by move=> nAG; rewrite /normal subsetIl normsI ?normG. Qed.

Lemma normalGI G H A : H \subset G -> A <| G -> H :&: A <| H.
Proof.
by move=> sHG /andP[_ nAG]; apply: norm_normalI (subset_trans sHG nAG).
Qed.

Lemma normal_subnorm G H : (H <| 'N_G(H)) = (H \subset G).
Proof. by rewrite /normal subsetIr subsetI normG !andbT. Qed.

Lemma normalD1 A G : (A^# <| G) = (A <| G).
Proof. by rewrite /normal normD1 subDset (setUidPr (sub1G G)). Qed.

Lemma gcore_sub A G : gcore A G \subset A.
Proof. by rewrite (bigcap_min 1) ?conjsg1. Qed.

Lemma gcore_norm A G : G \subset 'N(gcore A G).
Proof.
apply/subsetP=> x Gx; rewrite inE; apply/bigcapsP=> y Gy.
by rewrite sub_conjg -conjsgM bigcap_inf ?groupM ?groupV.
Qed.

Lemma gcore_normal A G : A \subset G -> gcore A G <| G.
Proof.
by move=> sAG; rewrite /normal gcore_norm (subset_trans (gcore_sub A G)).
Qed.

Lemma gcore_max A B G : B \subset A -> G \subset 'N(B) -> B \subset gcore A G.
Proof.
move=> sBA nBG; apply/bigcapsP=> y Gy.
by rewrite -sub_conjgV (normsP nBG) ?groupV.
Qed.

Lemma sub_gcore A B G :
  G \subset 'N(B) -> (B \subset gcore A G) = (B \subset A).
Proof.
move=> nBG; apply/idP/idP=> [sBAG | sBA]; last exact: gcore_max.
exact: subset_trans (gcore_sub A G).
Qed.

(* An elementary proof that subgroups of index 2 are normal; it is almost as  *)
(* short as the "advanced" proof using group actions; besides, the fact that  *)
(* the coset is equal to the complement is used in extremal.v.                *)
Lemma rcoset_index2 G H x :
  H \subset G -> #|G : H| = 2 -> x \in G :\: H -> H :* x = G :\: H.
Proof.
move=> sHG indexHG => /setDP[Gx notHx]; apply/eqP.
rewrite eqEcard -(leq_add2l #|G :&: H|) cardsID -(LagrangeI G H) indexHG muln2.
rewrite (setIidPr sHG) card_rcoset addnn leqnn andbT.
apply/subsetP=> _ /rcosetP[y Hy ->]; apply/setDP.
by rewrite !groupMl // (subsetP sHG).
Qed.

Lemma index2_normal G H : H \subset G -> #|G : H| = 2 -> H <| G.
Proof.
move=> sHG indexHG; rewrite /normal sHG; apply/subsetP=> x Gx.
case Hx: (x \in H); first by rewrite inE conjGid.
rewrite inE conjsgE mulgA -sub_rcosetV -invg_rcoset.
by rewrite !(rcoset_index2 sHG) ?inE ?groupV ?Hx // invDg !invGid.
Qed.

Lemma cent1P x y : reflect (commute x y) (x \in 'C[y]).
Proof.
rewrite [x \in _]inE conjg_set1 sub1set !inE (sameP eqP conjg_fixP)commg1_sym.
exact: commgP.
Qed.

Lemma cent1id x : x \in 'C[x]. Proof. exact/cent1P. Qed.

Lemma cent1E x y : (x \in 'C[y]) = (x * y == y * x).
Proof. by rewrite (sameP (cent1P x y) eqP). Qed.

Lemma cent1C x y : (x \in 'C[y]) = (y \in 'C[x]).
Proof. by rewrite !cent1E eq_sym. Qed.

Canonical centraliser_group A : {group _} := Eval hnf in [group of 'C(A)].

Lemma cent_set1 x : 'C([set x]) = 'C[x].
Proof. by apply: big_pred1 => y /=; rewrite !inE. Qed.

Lemma cent1J x y : 'C[x ^ y] = 'C[x] :^ y.
Proof. by rewrite -conjg_set1 normJ. Qed.

Lemma centP A x : reflect (centralises x A) (x \in 'C(A)).
Proof. by apply: (iffP bigcapP) => cxA y /cxA/cent1P. Qed.

Lemma centsP A B : reflect {in A, centralised B} (A \subset 'C(B)).
Proof. by apply: (iffP subsetP) => cAB x /cAB/centP. Qed.

Lemma centsC A B : (A \subset 'C(B)) = (B \subset 'C(A)).
Proof. by apply/centsP/centsP=> cAB x ? y ?; rewrite /commute -cAB. Qed.

Lemma cents1 A : A \subset 'C(1).
Proof. by rewrite centsC sub1G. Qed.

Lemma cent1T : 'C(1) = setT :> {set gT}.
Proof. by apply/eqP; rewrite -subTset cents1. Qed.

Lemma cent11T : 'C[1] = setT :> {set gT}.
Proof. by rewrite -cent_set1 cent1T. Qed.

Lemma cent_sub A : 'C(A) \subset 'N(A).
Proof.
apply/subsetP=> x /centP cAx; rewrite inE.
by apply/subsetP=> _ /imsetP[y Ay ->]; rewrite /conjg -cAx ?mulKg.
Qed.

Lemma cents_norm A B : A \subset 'C(B) -> A \subset 'N(B).
Proof. by move=> cAB; apply: subset_trans (cent_sub B). Qed.

Lemma centC A B : A \subset 'C(B) -> commute A B.
Proof. by move=> cAB; apply: normC (cents_norm cAB). Qed.

Lemma cent_joinEl G H : G \subset 'C(H) -> G <*> H = G * H.
Proof. by move=> cGH; apply: norm_joinEl (cents_norm cGH). Qed.

Lemma cent_joinEr G H : H \subset 'C(G) -> G <*> H = G * H.
Proof. by move=> cGH; apply: norm_joinEr (cents_norm cGH). Qed.

Lemma centJ A x : 'C(A :^ x) = 'C(A) :^ x.
Proof.
apply/setP=> y; rewrite mem_conjg; apply/centP/centP=> cAy z Az.
  by apply: (conjg_inj x); rewrite 2!conjMg conjgKV cAy ?memJ_conjg.
by apply: (conjg_inj x^-1); rewrite 2!conjMg cAy -?mem_conjg.
Qed.

Lemma cent_norm A : 'N(A) \subset 'N('C(A)).
Proof. by apply/normsP=> x nCx; rewrite -centJ (normP nCx). Qed.

Lemma norms_cent A B : A \subset 'N(B) -> A \subset 'N('C(B)).
Proof. by move=> nBA; apply: subset_trans nBA (cent_norm B). Qed.

Lemma cent_normal A : 'C(A) <| 'N(A).
Proof. by rewrite /(_ <| _) cent_sub cent_norm. Qed.

Lemma centS A B : B \subset A -> 'C(A) \subset 'C(B).
Proof. by move=> sAB; rewrite centsC (subset_trans sAB) 1?centsC. Qed.

Lemma centsS A B C : A \subset B -> C \subset 'C(B) -> C \subset 'C(A).
Proof. by move=> sAB cCB; apply: subset_trans cCB (centS sAB). Qed.

Lemma centSS A B C D :
  A \subset C -> B \subset D -> C \subset 'C(D) -> A \subset 'C(B).
Proof. by move=> sAC sBD cCD; apply: subset_trans (centsS sBD cCD). Qed.

Lemma centI A B : 'C(A) <*> 'C(B) \subset 'C(A :&: B).
Proof. by rewrite gen_subG subUset !centS ?(subsetIl, subsetIr). Qed.

Lemma centU A B : 'C(A :|: B) = 'C(A) :&: 'C(B).
Proof.
apply/eqP; rewrite eqEsubset subsetI 2?centS ?(subsetUl, subsetUr) //=.
by rewrite centsC subUset -centsC subsetIl -centsC subsetIr.
Qed.

Lemma cent_gen A : 'C(<<A>>) = 'C(A).
Proof. by apply/setP=> x; rewrite -!sub1set centsC gen_subG centsC. Qed.

Lemma cent_cycle x : 'C(<[x]>) = 'C[x].
Proof. by rewrite cent_gen cent_set1. Qed.

Lemma sub_cent1 A x : (A \subset 'C[x]) = (x \in 'C(A)).
Proof. by rewrite -cent_cycle centsC cycle_subG. Qed.

Lemma cents_cycle x y : commute x y -> <[x]> \subset 'C(<[y]>).
Proof. by move=> cxy; rewrite cent_cycle cycle_subG; apply/cent1P. Qed.

Lemma cycle_abelian x : abelian <[x]>.
Proof. exact: cents_cycle. Qed.

Lemma centY A B : 'C(A <*> B) = 'C(A) :&: 'C(B).
Proof. by rewrite cent_gen centU. Qed.

Lemma centM G H : 'C(G * H) = 'C(G) :&: 'C(H).
Proof. by rewrite -cent_gen genM_join centY. Qed.

Lemma cent_classP x G : reflect (x ^: G = [set x]) (x \in 'C(G)).
Proof.
apply: (iffP (centP _ _)) => [Cx | Cx1 y Gy].
  apply/eqP; rewrite eqEsubset sub1set class_refl andbT.
  by apply/subsetP=> _ /imsetP[y Gy ->]; rewrite !inE conjgE Cx ?mulKg.
by apply/commgP/conjg_fixP/set1P; rewrite -Cx1; apply/imsetP; exists y.
Qed.

Lemma commG1P A B : reflect ([~: A, B] = 1) (A \subset 'C(B)).
Proof.
apply: (iffP (centsP A B)) => [cAB | cAB1 x Ax y By].
  apply/trivgP; rewrite gen_subG; apply/subsetP=> _ /imset2P[x y Ax Ay ->].
  by rewrite inE; apply/commgP; apply: cAB.
by apply/commgP; rewrite -in_set1 -[[set 1]]cAB1 mem_commg.
Qed.

Lemma abelianE A : abelian A = (A \subset 'C(A)). Proof. by []. Qed.

Lemma abelian1 : abelian [1 gT]. Proof. exact: sub1G. Qed.

Lemma abelianS A B : A \subset B -> abelian B -> abelian A.
Proof. by move=> sAB; apply: centSS. Qed.

Lemma abelianJ A x : abelian (A :^ x) = abelian A.
Proof. by rewrite /abelian centJ conjSg. Qed.

Lemma abelian_gen A : abelian <<A>> = abelian A.
Proof. by rewrite /abelian cent_gen gen_subG. Qed.

Lemma abelianY A B :
  abelian (A <*> B) = [&& abelian A, abelian B & B \subset 'C(A)].
Proof.
rewrite /abelian join_subG /= centY !subsetI -!andbA; congr (_ && _).
by rewrite centsC andbA andbb andbC.
Qed.

Lemma abelianM G H :
  abelian (G * H) = [&& abelian G, abelian H & H \subset 'C(G)].
Proof. by rewrite -abelian_gen genM_join abelianY. Qed.

Section SubAbelian.

Variable A B C : {set gT}.
Hypothesis cAA : abelian A.

Lemma sub_abelian_cent : C \subset A -> A \subset 'C(C).
Proof. by move=> sCA; rewrite centsC (subset_trans sCA). Qed.

Lemma sub_abelian_cent2 : B \subset A -> C \subset A -> B \subset 'C(C).
Proof. by move=> sBA; move/sub_abelian_cent; apply: subset_trans. Qed.

Lemma sub_abelian_norm : C \subset A -> A \subset 'N(C).
Proof. by move=> sCA; rewrite cents_norm ?sub_abelian_cent. Qed.

Lemma sub_abelian_normal : (C \subset A) = (C <| A).
Proof.
by rewrite /normal; case sHG: (C \subset A); rewrite // sub_abelian_norm.
Qed.

End SubAbelian.

End Normaliser.

Arguments normP {gT x A}.
Arguments centP {gT A x}.
Arguments normsP {gT A B}.
Arguments cent1P {gT x y}.
Arguments normalP {gT A B}.
Arguments centsP {gT A B}.
Arguments commG1P {gT A B}.

Arguments normaliser_group _ _%g.
Arguments centraliser_group _ _%g.

Notation "''N' ( A )" := (normaliser_group A) : Group_scope.
Notation "''C' ( A )" := (centraliser_group A) : Group_scope.
Notation "''C' [ x ]" := (normaliser_group [set x%g]) : Group_scope.
Notation "''N_' G ( A )" := (setI_group G 'N(A)) : Group_scope.
Notation "''C_' G ( A )" := (setI_group G 'C(A)) : Group_scope.
Notation "''C_' ( G ) ( A )" := (setI_group G 'C(A))
  (only parsing) : Group_scope.
Notation "''C_' G [ x ]" := (setI_group G 'C[x]) : Group_scope.
Notation "''C_' ( G ) [ x ]" := (setI_group G 'C[x])
  (only parsing) : Group_scope.

#[global] Hint Extern 0 (is_true (_ \subset _)) => apply: normG : core.
#[global] Hint Extern 0 (is_true (_ <| _)) => apply: normal_refl : core.

Section MinMaxGroup.

Variable gT : finGroupType.
Implicit Types gP : pred {group gT}.

Definition maxgroup A gP := maxset (fun A => group_set A && gP <<A>>%G) A.
Definition mingroup A gP := minset (fun A => group_set A && gP <<A>>%G) A.

Variable gP : pred {group gT}.
Arguments gP _%G.

Lemma ex_maxgroup : (exists G, gP G) -> {G : {group gT} | maxgroup G gP}.
Proof.
move=> exP; have [A maxA]: {A | maxgroup A gP}.
  apply: ex_maxset; case: exP => G gPG.
  by exists (G : {set gT}); rewrite groupP genGidG.
by exists <<A>>%G; rewrite /= gen_set_id; case/andP: (maxsetp maxA).
Qed.

Lemma ex_mingroup : (exists G, gP G) -> {G : {group gT} | mingroup G gP}.
Proof.
move=> exP; have [A minA]: {A | mingroup A gP}.
  apply: ex_minset; case: exP => G gPG.
  by exists (G : {set gT}); rewrite groupP genGidG.
by exists <<A>>%G; rewrite /= gen_set_id; case/andP: (minsetp minA).
Qed.

Variable G : {group gT}.

Lemma mingroupP :
  reflect (gP G /\ forall H, gP H -> H \subset G -> H :=: G) (mingroup G gP).
Proof.
apply: (iffP minsetP); rewrite /= groupP genGidG /= => [] [-> minG].
  by split=> // H gPH sGH; apply: minG; rewrite // groupP genGidG.
by split=> // A; case/andP=> gA gPA; rewrite -(gen_set_id gA); apply: minG.
Qed.

Lemma maxgroupP :
  reflect (gP G /\ forall H, gP H -> G \subset H -> H :=: G) (maxgroup G gP).
Proof.
apply: (iffP maxsetP); rewrite /= groupP genGidG /= => [] [-> maxG].
  by split=> // H gPH sGH; apply: maxG; rewrite // groupP genGidG.
by split=> // A; case/andP=> gA gPA; rewrite -(gen_set_id gA); apply: maxG.
Qed.

Lemma maxgroupp : maxgroup G gP -> gP G. Proof. by case/maxgroupP. Qed.

Lemma mingroupp : mingroup G gP -> gP G. Proof. by case/mingroupP. Qed.

Hypothesis gPG : gP G.

Lemma maxgroup_exists : {H : {group gT} | maxgroup H gP & G \subset H}.
Proof.
have [A maxA sGA]: {A | maxgroup A gP & G \subset A}.
  by apply: maxset_exists; rewrite groupP genGidG.
by exists <<A>>%G; rewrite /= gen_set_id; case/andP: (maxsetp maxA).
Qed.

Lemma mingroup_exists : {H : {group gT} | mingroup H gP & H \subset G}.
Proof.
have [A maxA sGA]: {A | mingroup A gP & A \subset G}.
  by apply: minset_exists; rewrite groupP genGidG.
by exists <<A>>%G; rewrite /= gen_set_id; case/andP: (minsetp maxA).
Qed.

End MinMaxGroup.

Arguments mingroup {gT} A%g gP.
Arguments maxgroup {gT} A%g gP.
Arguments mingroupP {gT gP G}.
Arguments maxgroupP {gT gP G}.

Notation "[ 'max' A 'of' G | gP ]" :=
  (maxgroup A (fun G : {group _} => gP)) : group_scope.
Notation "[ 'max' G | gP ]" := [max gval G of G | gP] : group_scope.
Notation "[ 'max' A 'of' G | gP & gQ ]" :=
  [max A of G | gP && gQ] : group_scope.
Notation "[ 'max' G | gP & gQ ]" := [max G | gP && gQ] : group_scope.
Notation "[ 'min' A 'of' G | gP ]" :=
  (mingroup A (fun G : {group _} => gP)) : group_scope.
Notation "[ 'min' G | gP ]" := [min gval G of G | gP] : group_scope.
Notation "[ 'min' A 'of' G | gP & gQ ]" :=
  [min A of G | gP && gQ] : group_scope.
Notation "[ 'min' G | gP & gQ ]" := [min G | gP && gQ] : group_scope.

HB.reexport.

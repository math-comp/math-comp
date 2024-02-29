(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import path div finpred.

(******************************************************************************)
(*                             Finite types                                   *)
(*                                                                            *)
(* NB: See CONTRIBUTING.md for an introduction to HB concepts and commands.   *)
(*                                                                            *)
(* This file defines an interface for finite types:                           *)
(*                                                                            *)
(*       finType == type with finitely many inhabitants                       *)
(*                  The HB class is called Finite.                            *)
(*  subFinType P == join of finType and subType P                             *)
(*                  The HB class is called SubFinite.                         *)
(*                                                                            *)
(*    The Finite interface describes Types with finitely many elements,       *)
(* supplying a duplicate-free sequence of all the elements. It is a subclass  *)
(* of Countable and thus of Choice and Equality.                              *)
(*                                                                            *)
(* Bounded integers are supported by the following type and operations:       *)
(*                                                                            *)
(*    'I_n, ordinal n == the finite subType of integers i < n, whose          *)
(*                       enumeration is {0, ..., n.-1}                        *)
(*                       'I_n coerces to nat, so all the integer arithmetic   *)
(*                       functions can be used with 'I_n.                     *)
(*     Ordinal lt_i_n == the element of 'I_n with (nat) value i, given        *)
(*                       lt_i_n : i < n                                       *)
(*       nat_of_ord i == the nat value of i : 'I_n (this function is a        *)
(*                       coercion so it is not usually displayed)             *)
(*         ord_enum n == the explicit increasing sequence of the i : 'I_n     *)
(*  cast_ord eq_n_m i == the element j : 'I_m with the same value as i : 'I_n *)
(*                       given eq_n_m : n = m (indeed, i : nat and j : nat    *)
(*                       are convertible)                                     *)
(*           ordS n i == the successor of i : 'I_n along the cyclic structure *)
(*                       of 'I_n, reduces in nat to i.+1 %% n                 *)
(*       ord_pred n i == the predecessor of i : 'I_n along the cyclic         *)
(*                       structure of 'I_n, reduces in nat to (i + n).-1 %% n *)
(* widen_ord le_n_m i == a j : 'I_m with the same value as i : 'I_n, given    *)
(*                       le_n_m : n <= m                                      *)
(*          rev_ord i == the complement to n.-1 of i : 'I_n, such that        *)
(*                       i + rev_ord i = n.-1                                 *)
(*            inord k == the i : 'I_n.+1 with value k (n is inferred from the *)
(*                       context)                                             *)
(*          sub_ord k == the i : 'I_n.+1 with value n - k (n is inferred from *)
(*                       the context)                                         *)
(*               ord0 == the i : 'I_n.+1 with value 0 (n is inferred from the *)
(*                       context)                                             *)
(*            ord_max == the i : 'I_n.+1 with value n (n is inferred from the *)
(*                       context)                                             *)
(*           bump h k == k.+1 if k >= h, else k (this is a nat function)      *)
(*         unbump h k == k.-1 if k > h, else k (this is a nat function)       *)
(*           lift i j == the j' : 'I_n with value bump i j, where i : 'I_n    *)
(*                       and j : 'I_n.-1                                      *)
(*         unlift i j == None if i = j, else Some j', where j' : 'I_n.-1 has  *)
(*                       value unbump i j, given i, j : 'I_n                  *)
(*         lshift n j == the i : 'I_(m + n) with value j : 'I_m               *)
(*         rshift m k == the i : 'I_(m + n) with value m + k, k : 'I_n        *)
(*          unsplit u == either lshift n j or rshift m k, depending on        *)
(*                       whether if u : 'I_m + 'I_n is inl j or inr k         *)
(*            split i == the u : 'I_m + 'I_n such that i = unsplit u; the     *)
(*                       type 'I_(m + n) of i determines the split            *)
(*                                                                            *)
(* Finally, every type T with a finType structure supports the following      *)
(* operations:                                                                *)
(*                                                                            *)
(*           enum A == a duplicate-free list of all the x \in A, where A is a *)
(*                     collective predicate over T                            *)
(*             #|A| == the cardinal of A, i.e., the number of x \in A         *)
(*       enum_val i == the i'th item of enum A, where i : 'I_(#|A|)           *)
(*      enum_rank x == the i : 'I_(#|T|) such that enum_val i = x             *)
(* enum_rank_in Ax0 x == some i : 'I_(#|A|) such that enum_val i = x if       *)
(*                     x \in A, given Ax0 : x0 \in A                          *)
(*      A \subset B <=> all x \in A satisfy x \in B                           *)
(*      A \proper B <=> all x \in A satisfy x \in B but not the converse      *)
(* [disjoint A & B] <=> no x \in A satisfies x \in B                          *)
(*        image f A == the sequence of f x for all x : T such that x \in A    *)
(*                     (where a is an applicative predicate), of length #|P|. *)
(*                     The codomain of F can be any type, but image f A can   *)
(*                     only be used as a collective predicate is it is an     *)
(*                     eqType                                                 *)
(*          codom f == a sequence spanning the codomain of f (:= image f T)   *)
(*  [seq F | x : T in A] := image (fun x : T => F) A                          *)
(*       [seq F | x : T] := [seq F | x <- {: T}]                              *)
(*      [seq F | x in A], [seq F | x] == variants without casts               *)
(*        iinv im_y == some x such that P x holds and f x = y, given          *)
(*                     im_y : y \in image f P                                 *)
(*     invF inj_f y == the x such that f x = y, for inj_j : injective f with  *)
(*                     f : T -> T                                             *)
(*  dinjectiveb A f <=> the restriction of f : T -> R to A is injective       *)
(*                     (this is a boolean predicate, R must be an eqType)     *)
(*     injectiveb f <=> f : T -> R is injective (boolean predicate)           *)
(*         pred0b A <=> no x : T satisfies x \in A                            *)
(*    [forall x, P] <=> P (in which x can appear) is true for all values of x *)
(*                     x must range over a finType                            *)
(*    [exists x, P] <=> P is true for some value of x                         *)
(*      [forall (x | C), P] := [forall x, C ==> P]                            *)
(*       [forall x in A, P] := [forall (x | x \in A), P]                      *)
(*      [exists (x | C), P] := [exists x, C && P]                             *)
(*       [exists x in A, P] := [exists (x | x \in A), P]                      *)
(* and typed variants [forall x : T, P], [forall (x : T | C), P],             *)
(*   [exists x : T, P], [exists x : T in A, P], etc                           *)
(* -> The outer brackets can be omitted when nesting finitary quantifiers,    *)
(*    e.g., [forall i in I, forall j in J, exists a, f i j == a].             *)
(*       'forall_pP <-> view for [forall x, p _], for pP : reflect .. (p _)   *)
(*       'exists_pP <-> view for [exists x, p _], for pP : reflect .. (p _)   *)
(*    'forall_in_pP <-> view for [forall x in .., p _], for pP as above       *)
(*    'exists_in_pP <-> view for [exists x in .., p _], for pP as above       *)
(*     [pick x | P] == Some x, for an x such that P holds, or None if there   *)
(*                     is no such x                                           *)
(*     [pick x : T] == Some x with x : T, provided T is nonempty, else None   *)
(*    [pick x in A] == Some x, with x \in A, or None if A is empty            *)
(* [pick x in A | P] == Some x, with x \in A such that P holds, else None     *)
(*   [pick x | P & Q] := [pick x | P & Q]                                     *)
(* [pick x in A | P & Q] := [pick x | P & Q]                                  *)
(* and (un)typed variants [pick x : T | P], [pick x : T in A], [pick x], etc  *)
(* [arg min_(i < i0 | P) M] == a value i : T minimizing M : nat, subject      *)
(*                   to the condition P (i may appear in P and M), and        *)
(*                   provided P holds for i0                                  *)
(* [arg max_(i > i0 | P) M] == a value i maximizing M subject to P and        *)
(*                   provided P holds for i0                                  *)
(* [arg min_(i < i0 in A) M] == an i \in A minimizing M if i0 \in A           *)
(* [arg max_(i > i0 in A) M] == an i \in A maximizing M if i0 \in A           *)
(* [arg min_(i < i0) M] == an i : T minimizing M, given i0 : T                *)
(* [arg max_(i > i0) M] == an i : T maximizing M, given i0 : T                *)
(*   These are special instances of                                           *)
(* [arg[ord]_(i < i0 | P) F] == a value i : I, minimizing F wrt ord : rel T   *)
(*                              such that for all j : T, ord (F i) (F j)      *)
(*                              subject to the condition P, and provided P i0 *)
(*                              where I : finType, T : eqType and F : I -> T  *)
(* [arg[ord]_(i < i0 in A) F] == an i \in A minimizing F wrt ord, if i0 \in A *)
(* [arg[ord]_(i < i0) F] == an i : T minimizing F wrt ord, given i0 : T       *)
(*                                                                            *)
(*    We define the following interfaces and structures:                      *)
(*  Finite.axiom e <-> every x : T occurs exactly once in e : seq T.          *)
(* [Finite of T by <:] == a finType structure for T, when T has a subType     *)
(*                   structure over an existing finType.                      *)
(*   We define or propagate the finType structure appropriately for all basic *)
(* types : unit, bool, void, option, prod, sum, sig and sigT. We also define  *)
(* a generic type constructor for finite subtypes based on an explicit        *)
(* enumeration:                                                               *)
(*          seq_sub s == the subType of all x \in s, where s : seq T for some *)
(*                       eqType T; seq_sub s has a canonical finType instance *)
(*                       when T is a choiceType                               *)
(*   adhoc_seq_sub_choiceType s, adhoc_seq_sub_finType s ==                   *)
(*                       non-canonical instances for seq_sub s, s : seq T,    *)
(*                       which can be used when T is not a choiceType         *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope fin_quant_scope.

Definition finite_axiom (T : eqType) e :=
  forall x : T, count_mem x e = 1.

HB.mixin Record isFinite T of Equality T := {
  enum_subdef : seq T;
  enumP_subdef : finite_axiom enum_subdef
}.
(* Finiteness could be stated more simply by bounding the range of the pickle *)
(* function supplied by the Countable interface, but this would yield         *)
(* a useless computational interpretation due to the wasteful Peano integer   *)
(* encodings.                                                                 *)

(* TODO: this should not be a factory because enum_subdef will not be kept intact *)
(* HB.factory Record isFinite T of Choice T := { *)
(*   enum_subdef : seq T; *)
(*   enumP_subdef : finite_axiom enum_subdef *)
(* }. *)
(* HB.builders Context T of isFinite T. *)
(*   Definition enum : seq T. Admitted. *)
(*   Definition enumP : sorted prec enum. Admitted. *)
(*   HB.instance Definition _ := Choice_isFinite T enum enumP. *)
(* HB.end. *)

#[short(type="finType")]
HB.structure Definition Finite := {T of isFinite T & Countable T }.
(* As with Countable, the interface explicitly includes the somewhat redundant*)
(* Equality, Choice and Countable superclasses to ensure the forgetful        *)
(* inheritance criterion is met.                                              *)

Module Export FiniteNES.
Module Finite.

HB.lock Definition enum T :=
  sort prec_eq (isFinite.enum_subdef (Finite.class T)).
Canonical enum_unlockable := Unlockable enum.unlock.

Notation axiom := finite_axiom.
#[deprecated(since="mathcomp 2.0.0", note="Use isFinite.Build instead.")]
Notation EnumMixin m := (@isFinite.Build _ _ m).

Lemma uniq_axiom (T : eqType) e : uniq e -> e =i T -> axiom e.
Proof. by move=> Ue sT x; rewrite count_uniq_mem ?sT. Qed.

Lemma enum_prec_eq_sorted T : sorted prec_eq (enum T).
Proof. by rewrite unlock; apply/sort_sorted/prec_eq_total. Qed.

Lemma enumP T : axiom (enum T).
Proof.
by move=> x; rewrite unlock (permP (permEl (perm_sort _ _))) enumP_subdef.
Qed.

Lemma mem_enum T x : x \in enum T.
Proof. by rewrite -has_pred1 has_count enumP. Qed.

Lemma enum_uniq T : uniq (enum T).
Proof. by apply: count_mem_uniq => x; rewrite enumP mem_enum. Qed.

Section WithCountType.

Variable T : countType.

Definition UniqMixin_deprecated e Ue (eT : e =i T) :=
  @isFinite.Build T e (uniq_axiom Ue eT).

Variable n : nat.

Definition count_enum := pmap (@pickle_inv T) (iota 0 n).

Hypothesis ubT : forall x : T, pickle x < n.

Lemma count_axiom : axiom count_enum.
Proof.
apply: uniq_axiom (pmap_uniq (@pickle_invK T) (iota_uniq _ _)) _ => x.
by rewrite mem_pmap -pickleK_inv map_f // mem_iota ubT.
Qed.

Definition CountMixin_deprecated := @isFinite.Build _ _ count_axiom.

End WithCountType.
#[deprecated(since="mathcomp 2.0.0",
  note="Use isFinite.Build and Finite.uniq_enumP instead.")]
Notation UniqMixin := UniqMixin_deprecated.
#[deprecated(since="mathcomp 2.0.0",
  note="Use isFinite.Build and Finite.count_enumP instead.")]
Notation CountMixin := CountMixin_deprecated.
End Finite.
Canonical finEnum_unlock := Unlockable Finite.enum.unlock.
End FiniteNES.

Section finpred_finType.

Program Definition finpred_finType (T : finType) P := @Finpred T P _.
Next Obligation. by exists (Finite.enum T) => x _; apply: Finite.mem_enum. Qed.

Canonical Finpred_finType (T : finType) (P : pred T) b :=
  @InferFinpred T P (finpred_finType P) (TryFinType b).

End finpred_finType.

Section CanonicalFinType.
Variable (T : eqType) (s : seq T).

Definition fin_type of finite_axiom s : Type := T.

Variable (f : finite_axiom s).
Notation fT := (fin_type f).

Definition fin_pickle (x : fT) : nat := index x s.
Definition fin_unpickle (n : nat) : option fT :=
  nth None (map some s) n.
Lemma fin_pickleK : pcancel fin_pickle fin_unpickle.
Proof.
move=> x; rewrite /fin_pickle/fin_unpickle.
rewrite -(index_map Some_inj) nth_index ?map_f//.
by apply/count_memPn=> /eqP; rewrite f.
Qed.

HB.instance Definition _ := Equality.on fT.
HB.instance Definition _ := isCountable.Build fT fin_pickleK.
HB.instance Definition _ := isFinite.Build fT f.

End CanonicalFinType.

#[deprecated(since="mathcomp 2.0.0", note="Use isFinite.Build instead.")]
Notation FinMixin x := (@isFinite.Build _ _ x).
#[deprecated(since="mathcomp 2.0.0",
  note="Use isFinite.Build with Finite.uniq_enumP instead.")]
Notation UniqFinMixin := Finite.UniqMixin_deprecated.
#[deprecated(since="mathcomp 2.0.0", note="Use Finite.clone instead.")]
Notation "[ 'finType' 'of' T 'for' cT ]" := (Finite.clone T%type cT)
  (at level 0, format "[ 'finType'  'of'  T  'for'  cT ]") : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use Finite.clone instead.")]
Notation "[ 'finType' 'of' T ]" := (Finite.clone T%type _)
  (at level 0, format "[ 'finType'  'of'  T ]") : form_scope.

Module FiniteQuant.

Variant quantified := Quantified of bool.

Bind Scope fin_quant_scope with quantified.

Notation "F ^*" := (Quantified F) (at level 2).
Notation "F ^~" := (~~ F) (at level 2).

Section Definitions.

Variable T : finType.
Implicit Types (B : quantified) (x y : T).

Definition quant0b Bp := pred0b [pred x : T | let: F^* := Bp x x in F].
(* The first redundant argument protects the notation from  Coq's K-term      *)
(* display kludge; the second protects it from simpl and /=.                  *)
Definition ex B x y := B.
(* Binding the predicate value rather than projecting it prevents spurious    *)
(* unfolding of the boolean connectives by unification.                       *)
Definition all B x y := let: F^* := B in F^~^*.
Definition all_in C B x y := let: F^* := B in (C ==> F)^~^*.
Definition ex_in C B x y :=  let: F^* := B in (C && F)^*.

End Definitions.

Notation "[ x | B ]" := (quant0b (fun x => B x)) (at level 0, x name).
Notation "[ x : T | B ]" := (quant0b (fun x : T => B x)) (at level 0, x name).

Module Exports.

Notation ", F" := F^* (at level 200, format ", '/ '  F") : fin_quant_scope.

Notation "[ 'forall' x B ]" := [x | all B]
  (at level 0, x at level 99, B at level 200,
   format "[ '[hv' 'forall'  x B ] ']'") : bool_scope.

Notation "[ 'forall' x : T B ]" := [x : T | all B]
  (at level 0, x at level 99, B at level 200, only parsing) : bool_scope.
Notation "[ 'forall' ( x | C ) B ]" := [x | all_in C B]
  (at level 0, x at level 99, B at level 200,
   format "[ '[hv' '[' 'forall'  ( x '/  '  |  C ) ']' B ] ']'") : bool_scope.
Notation "[ 'forall' ( x : T | C ) B ]" := [x : T | all_in C B]
  (at level 0, x at level 99, B at level 200, only parsing) : bool_scope.
Notation "[ 'forall' x 'in' A B ]" := [x | all_in (x \in A) B]
  (at level 0, x at level 99, B at level 200,
   format "[ '[hv' '[' 'forall'  x '/  '  'in'  A ']' B ] ']'") : bool_scope.
Notation "[ 'forall' x : T 'in' A B ]" := [x : T | all_in (x \in A) B]
  (at level 0, x at level 99, B at level 200, only parsing) : bool_scope.
Notation ", 'forall' x B" := [x | all B]^*
  (at level 200, x at level 99, B at level 200,
   format ", '/ '  'forall'  x B") : fin_quant_scope.
Notation ", 'forall' x : T B" := [x : T | all B]^*
  (at level 200, x at level 99, B at level 200, only parsing) : fin_quant_scope.
Notation ", 'forall' ( x | C ) B" := [x | all_in C B]^*
  (at level 200, x at level 99, B at level 200,
   format ", '/ '  '[' 'forall'  ( x '/  '  |  C ) ']' B") : fin_quant_scope.
Notation ", 'forall' ( x : T | C ) B" := [x : T | all_in C B]^*
  (at level 200, x at level 99, B at level 200, only parsing) : fin_quant_scope.
Notation ", 'forall' x 'in' A B" := [x | all_in (x \in A) B]^*
  (at level 200, x at level 99, B at level 200,
   format ", '/ '  '[' 'forall'  x '/  '  'in'  A ']' B") : bool_scope.
Notation ", 'forall' x : T 'in' A B" := [x : T | all_in (x \in A) B]^*
  (at level 200, x at level 99, B at level 200, only parsing) : bool_scope.

Notation "[ 'exists' x B ]" := [x | ex B]^~
  (at level 0, x at level 99, B at level 200,
   format "[ '[hv' 'exists'  x B ] ']'") : bool_scope.
Notation "[ 'exists' x : T B ]" := [x : T | ex B]^~
  (at level 0, x at level 99, B at level 200, only parsing) : bool_scope.
Notation "[ 'exists' ( x | C ) B ]" := [x | ex_in C B]^~
  (at level 0, x at level 99, B at level 200,
   format "[ '[hv' '[' 'exists'  ( x '/  '  |  C ) ']' B ] ']'") : bool_scope.
Notation "[ 'exists' ( x : T | C ) B ]" := [x : T | ex_in C B]^~
  (at level 0, x at level 99, B at level 200, only parsing) : bool_scope.
Notation "[ 'exists' x 'in' A B ]" := [x | ex_in (x \in A) B]^~
  (at level 0, x at level 99, B at level 200,
   format "[ '[hv' '[' 'exists'  x '/  '  'in'  A ']' B ] ']'") : bool_scope.
Notation "[ 'exists' x : T 'in' A B ]" := [x : T | ex_in (x \in A) B]^~
  (at level 0, x at level 99, B at level 200, only parsing) : bool_scope.
Notation ", 'exists' x B" := [x | ex B]^~^*
  (at level 200, x at level 99, B at level 200,
   format ", '/ '  'exists'  x B") : fin_quant_scope.
Notation ", 'exists' x : T B" := [x : T | ex B]^~^*
  (at level 200, x at level 99, B at level 200, only parsing) : fin_quant_scope.
Notation ", 'exists' ( x | C ) B" := [x | ex_in C B]^~^*
  (at level 200, x at level 99, B at level 200,
   format ", '/ '  '[' 'exists'  ( x '/  '  |  C ) ']' B") : fin_quant_scope.
Notation ", 'exists' ( x : T | C ) B" := [x : T | ex_in C B]^~^*
  (at level 200, x at level 99, B at level 200, only parsing) : fin_quant_scope.
Notation ", 'exists' x 'in' A B" := [x | ex_in (x \in A) B]^~^*
  (at level 200, x at level 99, B at level 200,
   format ", '/ '  '[' 'exists'  x '/  '  'in'  A ']' B") : bool_scope.
Notation ", 'exists' x : T 'in' A B" := [x : T | ex_in (x \in A) B]^~^*
  (at level 200, x at level 99, B at level 200, only parsing) : bool_scope.

End Exports.

End FiniteQuant.
Export FiniteQuant.Exports.

Section FinOpsTheory.
Variable T : finType.
Implicit Types (A : {finpred T}) (x : T).

Lemma fintype_le1P : reflect (forall x, all_equal_to x) (#|T| <= 1).
Proof. by apply: (iffP (@card_le1_eqP T T)); [exact: in2T | exact: in2W]. Qed.

Lemma fintype1 : #|T| = 1 -> {x : T | all_equal_to x}.
Proof.
move=> /(@mem_card1 T T)[x ex]; exists x => y.
by suff: y \in T by rewrite ex => /eqP.
Qed.

Lemma fintype1P : reflect (exists x, all_equal_to x) (#|T| == 1).
Proof.
apply: (iffP idP) => [/eqP/fintype1|] [x eqx]; first by exists x.
by apply/(@card1P _ T); exists x => y; rewrite eqx [RHS]inE eqxx.
Qed.

Lemma predT_subset (P : {pred T}) : T \subset P -> forall x, x \in P.
Proof. by move/(@subsetP _ T) => + x; apply. Qed.

Lemma enumT : enum T = Finite.enum T.
Proof.
apply: (sorted_eq (@prec_eq_trans T) (@prec_eq_antisymmetric T)).
- exact: enum_prec_eq_sorted.
- exact: Finite.enum_prec_eq_sorted.
apply: uniq_perm (Finite.enum_uniq T) _ => // x.
by rewrite mem_enum Finite.mem_enum.
Qed.

Lemma cardT : #|T| = size (enum T). Proof. by rewrite (cardE T). Qed.

Lemma eq_cardT A : A =i predT -> #|A| = size (enum T).
Proof. exact: (@eq_card_trans T T) cardT. Qed.

Lemma cardC A : #|A| + #|[predC A]| = #|T|.
Proof. by rewrite -[RHS](cardID A); congr (_ + _); apply/eq_card. Qed.

Lemma cardC1 x : #|predC1 x| = #|T|.-1.
Proof. by rewrite -(cardC (pred1 x)) card1. Qed.

Lemma max_card A : #|A| <= #|T|.
Proof. by rewrite -(cardC A) leq_addr. Qed.

Lemma fintype0 : T -> #|T| <> 0. Proof. by move=> x /(@card0_eq _ T)/(_ x). Qed.

End FinOpsTheory.
Arguments fintype_le1P {T}.
Arguments fintype1P {T}.

(**********************************************************************)
(*                                                                    *)
(*  Boolean quantifiers for finType                                   *)
(*                                                                    *)
(**********************************************************************)

Section QuantifierCombinators.

Variables (T : finType) (P : pred T) (PP : T -> Prop).
Hypothesis viewP : forall x, reflect (PP x) (P x).

Lemma existsPP : reflect (exists x, PP x) [exists x, P x].
Proof. by apply: (iffP pred0Pn) => -[x /viewP]; exists x. Qed.

Lemma forallPP : reflect (forall x, PP x) [forall x, P x].
Proof. by apply: (iffP pred0P) => /= allP x; have /viewP//=-> := allP x. Qed.

End QuantifierCombinators.

Notation "'exists_ view" := (existsPP (fun _ => view))
  (at level 4, right associativity, format "''exists_' view").
Notation "'forall_ view" := (forallPP (fun _ => view))
  (at level 4, right associativity, format "''forall_' view").

Section Quantifiers.

Variables (T : finType) (rT : T -> eqType).
Implicit Types (D P : pred T) (f : forall x, rT x).

Lemma forallP P : reflect (forall x, P x) [forall x, P x].
Proof. exact: 'forall_idP. Qed.

Lemma eqfunP f1 f2 : reflect (forall x, f1 x = f2 x) [forall x, f1 x == f2 x].
Proof. exact: 'forall_eqP. Qed.

Lemma forall_inP D P : reflect (forall x, D x -> P x) [forall (x | D x), P x].
Proof. exact: 'forall_implyP. Qed.

Lemma forall_inPP D P PP : (forall x, reflect (PP x) (P x)) ->
  reflect (forall x, D x -> PP x) [forall (x | D x), P x].
Proof. by move=> vP; apply: (iffP (forall_inP _ _)) => /(_ _ _) /vP. Qed.

Lemma eqfun_inP D f1 f2 :
  reflect {in D, forall x, f1 x = f2 x} [forall (x | x \in D), f1 x == f2 x].
Proof. exact: (forall_inPP _ (fun=> eqP)). Qed.

Lemma existsP P : reflect (exists x, P x) [exists x, P x].
Proof. exact: 'exists_idP. Qed.

Lemma existsb P (x : T) : P x -> [exists x, P x].
Proof. by move=> Px; apply/existsP; exists x. Qed.

Lemma exists_eqP f1 f2 :
  reflect (exists x, f1 x = f2 x) [exists x, f1 x == f2 x].
Proof. exact: 'exists_eqP. Qed.

Lemma exists_inP D P : reflect (exists2 x, D x & P x) [exists (x | D x), P x].
Proof. by apply: (iffP 'exists_andP) => [[x []] | [x]]; exists x. Qed.

Lemma exists_inb D P (x : T) : D x -> P x -> [exists (x | D x), P x].
Proof. by move=> Dx Px; apply/exists_inP; exists x. Qed.

Lemma exists_inPP D P PP : (forall x, reflect (PP x) (P x)) ->
  reflect (exists2 x, D x & PP x) [exists (x | D x), P x].
Proof. by move=> vP; apply: (iffP (exists_inP _ _)) => -[x?/vP]; exists x. Qed.

Lemma exists_eq_inP D f1 f2 :
  reflect (exists2 x, D x & f1 x = f2 x) [exists (x | D x), f1 x == f2 x].
Proof. exact: (exists_inPP _ (fun=> eqP)). Qed.

Lemma eq_existsb P1 P2 : P1 =1 P2 -> [exists x, P1 x] = [exists x, P2 x].
Proof. by move=> eqP12; congr (_ != 0); apply: eq_card. Qed.

Lemma eq_existsb_in D P1 P2 :
    (forall x, D x -> P1 x = P2 x) ->
  [exists (x | D x), P1 x] = [exists (x | D x), P2 x].
Proof. by move=> eqP12; apply: eq_existsb => x; apply: andb_id2l => /eqP12. Qed.

Lemma eq_forallb P1 P2 : P1 =1 P2 -> [forall x, P1 x] = [forall x, P2 x].
Proof. by move=> eqP12; apply/negb_inj/eq_existsb=> /= x; rewrite eqP12. Qed.

Lemma eq_forallb_in D P1 P2 :
    (forall x, D x -> P1 x = P2 x) ->
  [forall (x | D x), P1 x] = [forall (x | D x), P2 x].
Proof.
by move=> eqP12; apply: eq_forallb => i; case Di: (D i); rewrite // eqP12.
Qed.

Lemma negb_forall P : ~~ [forall x, P x] = [exists x, ~~ P x].
Proof. by []. Qed.

Lemma negb_forall_in D P :
  ~~ [forall (x | D x), P x] = [exists (x | D x), ~~ P x].
Proof. by apply: eq_existsb => x; rewrite negb_imply. Qed.

Lemma negb_exists P : ~~ [exists x, P x] = [forall x, ~~ P x].
Proof. by apply/negbLR/esym/eq_existsb=> x; apply: negbK. Qed.

Lemma negb_exists_in D P :
  ~~ [exists (x | D x), P x] = [forall (x | D x), ~~ P x].
Proof. by rewrite negb_exists; apply/eq_forallb => x; rewrite [~~ _]fun_if. Qed.

Lemma existsPn P :
  reflect (forall x, ~~ P x) (~~ [exists x, P x]).
Proof. rewrite negb_exists. exact: forallP. Qed.

Lemma forallPn P :
  reflect (exists x, ~~ P x) (~~ [forall x, P x]).
Proof. rewrite negb_forall. exact: existsP. Qed.

Lemma exists_inPn D P :
  reflect (forall x, x \in D -> ~~ P x) (~~ [exists x in D, P x]).
Proof. rewrite negb_exists_in. exact: forall_inP. Qed.

Lemma forall_inPn D P :
  reflect (exists2 x, x \in D & ~~ P x) (~~ [forall x in D, P x]).
Proof. rewrite negb_forall_in. exact: exists_inP. Qed.

End Quantifiers.

Arguments forallP {T P}.
Arguments eqfunP {T rT f1 f2}.
Arguments forall_inP {T D P}.
Arguments eqfun_inP {T rT D f1 f2}.
Arguments existsP {T P}.
Arguments existsb {T P}.
Arguments exists_eqP {T rT f1 f2}.
Arguments exists_inP {T D P}.
Arguments exists_inb {T D P}.
Arguments exists_eq_inP {T rT D f1 f2}.
Arguments existsPn {T P}.
Arguments exists_inPn {T D P}.
Arguments forallPn {T P}.
Arguments forall_inPn {T D P}.

Notation "'exists_in_ view" := (exists_inPP _ (fun _ => view))
  (at level 4, right associativity, format "''exists_in_' view").
Notation "'forall_in_ view" := (forall_inPP _ (fun _ => view))
  (at level 4, right associativity, format "''forall_in_' view").

(**********************************************************************)
(*                                                                    *)
(*  Boolean injectivity test for functions with a finType domain      *)
(*                                                                    *)
(**********************************************************************)

Section Injectiveb.

Variables (aT : finType) (rT : eqType) (f : aT -> rT).
Implicit Type D : {finpred aT}.

Definition injectiveb := @dinjectiveb aT rT f aT.

Lemma injectivePn :
  reflect (exists x, exists2 y, x != y & f x = f y) (~~ injectiveb).
Proof.
apply: (iffP (dinjectivePn _ _)) => [[x _ [y nxy eqfxy]] | [x [y nxy eqfxy]]];
 by exists x => //; exists y => //; rewrite inE /= andbT eq_sym in nxy *.
Qed.

Lemma injectiveP : reflect (injective f) injectiveb.
Proof.
by apply: (iffP (dinjectiveP _ _)) => injf x y => [|_ _]; apply: injf.
Qed.

End Injectiveb.

Definition codom (T : finType) T' f := @image T T' f T.

Section Image.

Variable T : finType.
Implicit Type A : {finpred T}.

Section SizeImage.

Variables (T' : Type) (f : T -> T').

Lemma size_codom : size (codom f) = #|T|.
Proof. exact: size_image. Qed.

Lemma codomE : codom f = map f (enum T).
Proof. by []. Qed.

End SizeImage.

Variables (T' : eqType) (f : T -> T').

Lemma codomP y : reflect (exists x, y = f x) (y \in codom f).
Proof. by apply: (iffP (@imageP _ _ _ _ y)) => [][x]; exists x. Qed.

Lemma codom_f x : f x \in codom f.
Proof. exact: image_f. Qed.

Lemma image_codom A : {subset image f A <= codom f}.
Proof. by move=> _ /imageP[x _ ->]; apply: codom_f. Qed.

Section Injective.

Hypothesis injf : injective f.

Lemma image_iinv A y (fTy : y \in codom f) :
  (y \in image f A) = (iinv fTy \in A).
Proof. by rewrite -(mem_image injf) ?f_iinv. Qed.

Lemma iinv_f x fTfx : @iinv _ _ f T (f x) fTfx = x.
Proof. by apply: in_iinv_f; first apply: in2W. Qed.

Lemma image_pre (B : pred T') : image f [preim f of B] =i [predI B & codom f].
Proof.
move=> y; rewrite /image.
have /(eq_mem_map f)-> :
    enum [preim f of B] =i [seq x <- Finite.enum T | preim f B x].
  move=> x; rewrite mem_enum mem_filter andb_idr// => _.
  by rewrite -has_pred1 has_count Finite.enumP.  (* FIXME: simplify proof *)
by rewrite -filter_map mem_filter -enumT.
Qed.

Lemma bij_on_codom (x0 : T) : {on [pred y in codom f], bijective f}.
Proof.
pose g y := iinv (valP (insigd (codom_f x0) y)).
by exists g => [x fAfx | y fAy]; first apply: injf; rewrite f_iinv insubdK.
Qed.

(* TODO: generalize in section ChoiceInjective in finpred.v *)
Lemma bij_on_image A (x0 : T) : {on [pred y in image f A], bijective f}.
Proof. exact: subon_bij (@image_codom A) (bij_on_codom x0). Qed.

End Injective.

Fixpoint preim_seq s :=
  if s is y :: s' then
    (if pick (preim f (pred1 y)) is Some x then cons x else id) (preim_seq s')
    else [::].

Lemma map_preim (s : seq T') : {subset s <= codom f} -> map f (preim_seq s) = s.
Proof.
elim: s => //= y s IHs; case: pickP => [x /eqP fx_y | nfTy] fTs.
  by rewrite /= fx_y IHs // => z s_z; apply: fTs; apply: predU1r.
by case/imageP: (fTs y (mem_head y s)) => x _ fx_y; case/eqP: (nfTy x).
Qed.

End Image.

Prenex Implicits codom iinv.
Arguments codomP {T T' f y}.

Section ChoiceCardFunImage.

Variables (T : choiceType) (T' : finType) (f : T -> T').
Implicit Type A : {finpred T}.

Lemma leq_card_in A : {in A &, injective f} -> #|A| <= #|T'|.
Proof. by move=> /card_in_image<-; apply: (max_card [seq f x | x in A]). Qed.

End ChoiceCardFunImage.
Arguments leq_card_in [T T'] f.

Section CardFunImage.

Variables (T T' : finType) (f : T -> T').
Implicit Type A : {finpred T}.

Hypothesis injf : injective f.

Lemma card_codom : #|codom f| = #|T|.
Proof. exact: card_image. Qed.

Lemma card_preim (B : {finpred T'}) : #|[preim f of B]| = #|[predI codom f & B]|.
Proof.
rewrite -(card_image injf); apply: (@eq_card _ [seq f x | x in [preim f of B]]).
by move=> y; rewrite [y \in _]image_pre inE andbC.
Qed.

Lemma leq_card : #|T| <= #|T'|.
Proof. exact: (@leq_card_in _ _ _ T (in2W injf)). Qed.

Hypothesis card_range : #|T| >= #|T'|.

Let eq_card : #|T| = #|T'|. Proof. by apply/eqP; rewrite eqn_leq leq_card. Qed.

Lemma inj_card_onto y : y \in codom f.
Proof.
move: y; apply/(@subset_cardP T' [pred x | x \in codom f] predT).
  by rewrite card_codom.
by rewrite subset_predT.
Qed.

Lemma inj_card_bij :  bijective f.
Proof.
by exists (fun y => iinv (inj_card_onto y)) => y; rewrite ?iinv_f ?f_iinv.
Qed.

End CardFunImage.
Arguments leq_card [T T'] f.

Lemma bij_eq_card (T T' : finType) (f : T -> T') : bijective f -> #|T| = #|T'|.
Proof. by move=> [g /can_inj/leq_card + /can_inj/leq_card]; case: ltngtP. Qed.

Section FinCancel.

Variables (T : finType) (f g : T -> T).

Section Inv.

Hypothesis injf : injective f.

Lemma injF_onto y : y \in codom f. Proof. exact: inj_card_onto. Qed.
Definition invF y := iinv (injF_onto y).
Lemma invF_f : cancel f invF. Proof. by move=> x; apply: iinv_f. Qed.
Lemma f_invF : cancel invF f. Proof. by move=> y; apply: f_iinv. Qed.
Lemma injF_bij : bijective f. Proof. exact: inj_card_bij. Qed.

End Inv.

Hypothesis fK : cancel f g.

Lemma canF_sym : cancel g f.
Proof. exact/(bij_can_sym (injF_bij (can_inj fK))). Qed.

Lemma canF_LR x y : x = g y -> f x = y.
Proof. exact: canLR canF_sym. Qed.

Lemma canF_RL x y : g x = y -> x = f y.
Proof. exact: canRL canF_sym. Qed.

Lemma canF_eq x y : (f x == y) = (x == g y).
Proof. exact: (can2_eq fK canF_sym). Qed.

Lemma canF_invF : g =1 invF (can_inj fK).
Proof. by move=> y; apply: (canLR fK); rewrite f_invF. Qed.

End FinCancel.

Section EqImage.

Variables (T : finType) (T' : Type).

Lemma eq_image (A B : {pred T}) (f g : T -> T') :
  A =i B -> f =1 g -> image f A = image g B.
Proof.
by move=> eqAB eqfg; rewrite /image (eq_enum eqAB) (eq_map eqfg).
Qed.

Lemma eq_codom (f g : T -> T') : f =1 g -> codom f = codom g.
Proof. exact: eq_image. Qed.

Lemma eq_invF f g injf injg : f =1 g -> @invF T f injf =1 @invF T g injg.
Proof.
by move=> eq_fg x; apply: (canLR (invF_f injf)); rewrite eq_fg f_invF.
Qed.

End EqImage.

(* Standard finTypes *)

Lemma unit_enumP : Finite.axiom [::tt]. Proof. by case. Qed.
HB.instance Definition _ := isFinite.Build unit unit_enumP.
Lemma card_unit : #|{: unit}| = 1. Proof. by rewrite cardT enumT unlock. Qed.

Lemma bool_enumP : Finite.axiom [:: true; false]. Proof. by case. Qed.
HB.instance Definition _ := isFinite.Build bool bool_enumP.
Lemma card_bool : #|{: bool}| = 2.
Proof. by rewrite cardT enumT unlock size_sort. Qed.

Lemma void_enumP : Finite.axiom (Nil void). Proof. by case. Qed.
HB.instance Definition _ := isFinite.Build void void_enumP.
Lemma card_void : #|{: void}| = 0. Proof. by rewrite cardT enumT unlock. Qed.

Local Notation enumF T := (Finite.enum T).

Section OptionFinType.

Variable T : finType.

Definition option_enum := None :: map some (enumF T).

Lemma option_enumP : Finite.axiom option_enum.
Proof. by case=> [x|]; rewrite /= count_map (count_pred0, Finite.enumP). Qed.

HB.instance Definition _ := isFinite.Build (option T) option_enumP.

Lemma card_option : #|{: option T}| = #|T|.+1.
Proof. by rewrite !cardT !enumT [in LHS]unlock size_sort /= size_map. Qed.

End OptionFinType.

Section TransferFinTypeFromCount.

Variables (eT : countType) (fT : finType) (f : eT -> fT).

Lemma pcan_enumP g : pcancel f g -> Finite.axiom (undup (pmap g (enumF fT))).
Proof.
move=> fK x; rewrite count_uniq_mem ?undup_uniq // mem_undup.
by rewrite mem_pmap -fK map_f // -enumT mem_enum.
Qed.

Definition PCanIsFinite g fK := @isFinite.Build _ _ (@pcan_enumP g fK).

Definition CanIsFinite g (fK : cancel f g) := PCanIsFinite (can_pcan fK).

End TransferFinTypeFromCount.

#[deprecated(since="mathcomp 2.0.0",
  note="Use pcan_type instead or PCanIsFInite.")]
Notation PcanFinMixin := PCanIsFinite.
#[deprecated(since="mathcomp 2.0.0",
  note="Use can_type instead or CanIsFinite.")]
Notation CanFinMixin := CanIsFinite.

Section TransferFinType.

Variables (eT : Type) (fT : finType) (f : eT -> fT).

HB.instance Definition _ (g : fT -> option eT) (fK : pcancel f g) :=
  isFinite.Build (pcan_type fK) (@pcan_enumP (pcan_type fK) fT f g fK).

HB.instance Definition _ (g : fT -> eT) (fK : cancel f g) :=
  isFinite.Build (can_type fK) (@pcan_enumP (can_type fK) fT f _ (can_pcan fK)).

End TransferFinType.

#[short(type="subFinType")]
HB.structure Definition SubFinite (T : Type) (P : pred T) :=
  { sT of Finite sT & isSub T P sT }.

Section SubFinType.

Variables (T : choiceType) (P : pred T).
Import Finite.

Implicit Type sT : subFinType P.

Lemma codom_val sT x : (x \in codom (val : sT -> T)) = P x.
Proof.
by apply/codomP/idP=> [[u ->]|Px]; last exists (Sub x Px); rewrite ?valP ?SubK.
Qed.

End SubFinType.

#[deprecated(since="mathcomp 2.0.0", note="Use SubFinite.clone instead.")]
Notation "[ 'subFinType' 'of' T ]" := (SubFinite.clone _ _ T%type _)
  (at level 0, format "[ 'subFinType'  'of'  T ]") : form_scope.

HB.factory Record SubCountable_isFinite (T : finType) P (sT : Type)
  of SubCountable T P sT := { }.

HB.builders Context (T : finType) (P : pred T) (sT : Type)
  (a : SubCountable_isFinite T P sT).

Definition sub_enum : seq sT := pmap insub (enumF T).

Lemma mem_sub_enum u : u \in sub_enum.
Proof. by rewrite mem_pmap_sub -enumT mem_enum. Qed.

Lemma sub_enum_uniq : uniq sub_enum.
Proof. by rewrite pmap_sub_uniq // -enumT. Qed.

Lemma val_sub_enum : map val sub_enum = enum [pred x | P x].
Proof.
rewrite pmap_filter; last exact: insubK.
apply: (sorted_eq (@prec_eq_trans _) (@prec_eq_antisymmetric _)).
- by rewrite sorted_filter ?Finite.enum_prec_eq_sorted//; apply: prec_eq_trans.
- exact: enum_prec_eq_sorted.
apply: uniq_perm => [|//| x]; first exact/filter_uniq/Finite.enum_uniq.
by rewrite mem_filter Finite.mem_enum andbT isSome_insub mem_enum.
Qed.

HB.instance Definition SubFinMixin := isFinite.Build sT
  (Finite.uniq_axiom sub_enum_uniq mem_sub_enum).
HB.end.

(* This assumes that T has a subCountType structure over a type that  *)
(* has a finType structure.                                           *)

HB.instance Definition _ (T : finType) (P : pred T) (sT : subType P) :=
  (SubCountable_isFinite.Build _ _ (sub_type sT)).

Notation "[ 'Finite' 'of' T 'by' <: ]" := (Finite.copy T%type (sub_type T%type))
  (at level 0, format "[ 'Finite'  'of'  T  'by'  <: ]") : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use [Finite of _ by <:] instead.")]
Notation "[ 'finMixin' 'of' T 'by' <: ]" := [Finite of T%type by <:]
  (at level 0, format "[ 'finMixin'  'of'  T  'by'  <: ]") : form_scope.

Section SubCountable_isFiniteTheory.

Variables (T : finType) (P : pred T) (sfT : subFinType P).

Lemma card_sub : #|sfT| = #|[pred x | P x]|.
Proof.
rewrite -(@eq_card _ (codom (\val : sfT -> T)) [pred x | P x] (codom_val sfT)).
by rewrite (card_image val_inj).
Qed.

Lemma eq_card_sub (A : {pred sfT}) : A =i predT -> #|A| = #|[pred x | P x]|.
Proof. exact: eq_card_trans card_sub. Qed.

End SubCountable_isFiniteTheory.

(* (* Regression for the subFinType stack *) *)
(* Record myb : Type := MyB {myv : bool; _ : ~~ myv}. *)
(* HB.instance Definition myb_sub : isSub bool (fun x => ~~ x) myb := *)
(*    [isSub for myv]. *)
(* HB.instance Definition _ := [Finite of myb by <:]. *)
(* Check [subFinType of myb]. *)
(* Check [finType of myb]. *)

Section CardSig.

Variables (T : finType) (P : pred T).

HB.instance Definition _ := [Finite of {x | P x} by <:].

Lemma card_sig : #|{: {x | P x}}| = #|[pred x | P x]|.
Proof. exact: card_sub. Qed.

End CardSig.

(* Subtype for an explicit enumeration. *)
Section SeqSubType.

Variables (T : eqType) (s : seq T).

Fact seq_sub_axiom : Finite.axiom (seq_sub_enum s).
Proof. exact: Finite.uniq_axiom (undup_uniq _) (@mem_seq_sub_enum T s). Qed.
Definition seq_sub_isFinite := isFinite.Build (seq_sub s) seq_sub_axiom.

(* Beware: these are not the canonical instances, as they are not consistent  *)
(* with the generic sub_choiceType canonical instance.                        *)
Definition adhoc_seq_sub_finType := HB.pack_for finType (seq_sub s)
  seq_sub_isFinite (seq_sub_isCountable s)
  (Choice.class (adhoc_seq_sub_choiceType s)).

End SeqSubType.

Section SeqFinType.

Variables (T : choiceType) (s : seq T).
Local Notation sT := (seq_sub s).

HB.instance Definition _ := [Choice of sT by <:].
HB.instance Definition _ : isCountable sT := seq_sub_isCountable s.
HB.instance Definition _ : isFinite sT := seq_sub_isFinite s.

Lemma card_seq_sub : uniq s -> #|{:sT}| = size s.
Proof.
move=> Us; rewrite cardE enumT unlock /= size_sort /seq_sub_enum.
rewrite undup_id ?pmap_sub_uniq// size_pmap; apply/eqP; rewrite -all_count.
by apply/allP => x xs; rewrite insubT.
Qed.

End SeqFinType.

(**********************************************************************)
(*                                                                    *)
(*  Ordinal finType : {0, ... , n-1}                                  *)
(*                                                                    *)
(**********************************************************************)

Section OrdinalSub.

Variable n : nat.

Inductive ordinal : predArgType := Ordinal m of m < n.

Coercion nat_of_ord i := let: Ordinal m _ := i in m.

HB.instance Definition _ := [isSub of ordinal for nat_of_ord].
HB.instance Definition _ := [Countable of ordinal by <:].

Lemma ltn_ord (i : ordinal) : i < n. Proof. exact: valP i. Qed.

Lemma ord_inj : injective nat_of_ord. Proof. exact: val_inj. Qed.

Definition ord_enum : seq ordinal := pmap insub (iota 0 n).

Lemma val_ord_enum : map val ord_enum = iota 0 n.
Proof.
rewrite pmap_filter; last exact: insubK.
by apply/all_filterP; apply/allP=> i; rewrite mem_iota isSome_insub.
Qed.

Lemma ord_enum_uniq : uniq ord_enum.
Proof. by rewrite pmap_sub_uniq ?iota_uniq. Qed.

Lemma mem_ord_enum (i : ordinal) : i \in ord_enum.
Proof. by rewrite -(mem_map ord_inj) val_ord_enum mem_iota ltn_ord. Qed.

HB.instance Definition _ := isFinite.Build ordinal
  (Finite.uniq_axiom ord_enum_uniq mem_ord_enum).

End OrdinalSub.

Notation "''I_' n" := (ordinal n)
  (at level 8, n at level 2, format "''I_' n").

#[global] Hint Resolve ltn_ord : core.

Section OrdinalEnum.

Variable n : nat.

Lemma val_enum_ord : perm_eq (map val (enum 'I_n)) (iota 0 n).
Proof.
apply: uniq_perm; rewrite ?map_inj_uniq ?iota_uniq//; first exact: val_inj.
rewrite -val_ord_enum enumT unlock/=.
by apply: eq_mem_map => /= i; rewrite mem_sort.
Qed.

(*
Lemma val_enum_ord : map val (enum 'I_n) = iota 0 n.
Proof.
Abort.
(* probably not provable anymore since nat_hasChoice in choice.v is opaque *)
by rewrite enumT unlock val_ord_enum. Qed. *)

Lemma size_enum_ord : size (enum 'I_n) = n.
Proof. by rewrite -(size_map val) (perm_size val_enum_ord) size_iota. Qed.

Lemma card_ord : #|'I_n| = n.
Proof. by rewrite cardE size_enum_ord. Qed.

Lemma nth_enum_ord i0 m : m < n -> nth i0 (enum 'I_n) m = m :> nat.
Abort. (* probably no longer provable either *)
(* by move=> ?; rewrite -(nth_map _ 0) (size_enum_ord, val_enum_ord) // nth_iota. *)

Lemma nth_ord_enum (i0 i : 'I_n) : nth i0 (enum 'I_n) i = i.
Abort. (* probably no longer provable either *)
(* by apply: val_inj; apply: nth_enum_ord. *)

Lemma index_enum_ord (i : 'I_n) : index i (enum 'I_n) = i.
Abort. (* probably no longer provable either *)
(* by rewrite -[in LHS](nth_ord_enum i i) index_uniq ?(enum_uniq, size_enum_ord). *)

Lemma mask_enum_ord m :
  mask m (enum 'I_n) = [seq i <- enum 'I_n | nth false m (val i)].
Abort. (* probably no longer provable either *)
(* rewrite mask_filter ?enum_uniq//; apply: eq_filter => i.
by rewrite in_mask ?enum_uniq ?mem_enum// index_enum_ord. *)

End OrdinalEnum.

Lemma enum_ord0 : enum 'I_0 = [::].
Proof. by apply/eqP; rewrite -size_eq0 size_enum_ord. Qed.

Lemma widen_ord_proof n m (i : 'I_n) : n <= m -> i < m.
Proof. exact: leq_trans. Qed.
Definition widen_ord n m le_n_m i := Ordinal (@widen_ord_proof n m i le_n_m).

Lemma cast_ord_proof n m (i : 'I_n) : n = m -> i < m.
Proof. by move <-. Qed.
Definition cast_ord n m eq_n_m i := Ordinal (@cast_ord_proof n m i eq_n_m).

Lemma cast_ord_id n eq_n i : cast_ord eq_n i = i :> 'I_n.
Proof. exact: val_inj. Qed.

Lemma cast_ord_comp n1 n2 n3 eq_n2 eq_n3 i :
  @cast_ord n2 n3 eq_n3 (@cast_ord n1 n2 eq_n2 i) =
    cast_ord (etrans eq_n2 eq_n3) i.
Proof. exact: val_inj. Qed.

Lemma cast_ordK n1 n2 eq_n :
  cancel (@cast_ord n1 n2 eq_n) (cast_ord (esym eq_n)).
Proof. by move=> i; apply: val_inj. Qed.

Lemma cast_ordKV n1 n2 eq_n :
  cancel (cast_ord (esym eq_n)) (@cast_ord n1 n2 eq_n).
Proof. by move=> i; apply: val_inj. Qed.

Lemma cast_ord_inj n1 n2 eq_n : injective (@cast_ord n1 n2 eq_n).
Proof. exact: can_inj (cast_ordK eq_n). Qed.

Fact ordS_subproof n (i : 'I_n) : i.+1 %% n < n.
Proof. by case: n i => [|n] [m m_lt]//=; rewrite ltn_pmod. Qed.
Definition ordS n (i : 'I_n) := Ordinal (ordS_subproof i).

Fact ord_pred_subproof n (i : 'I_n) : (i + n).-1 %% n < n.
Proof. by case: n i => [|n] [m m_lt]//=; rewrite ltn_pmod. Qed.
Definition ord_pred n (i : 'I_n) := Ordinal (ord_pred_subproof i).

Lemma ordSK n : cancel (@ordS n) (@ord_pred n).
Proof.
move=> [i ilt]; apply/val_inj => /=.
case: (ltngtP i.+1) (ilt) => // [Silt|<-]; last by rewrite modnn/= modn_small.
by rewrite [i.+1 %% n]modn_small// addSn/= modnDr modn_small.
Qed.

Lemma ord_predK n : cancel (@ord_pred n) (@ordS n).
Proof.
move=> [[|i] ilt]; apply/val_inj => /=.
  by rewrite [n.-1 %% n]modn_small// prednK// modnn.
by rewrite modnDr [i %% n]modn_small ?modn_small// ltnW.
Qed.

Lemma ordS_bij n : bijective (@ordS n).
Proof. exact: (Bijective (@ordSK n) (@ord_predK n)). Qed.

Lemma ordS_inj n : injective (@ordS n).
Proof. exact: (bij_inj (ordS_bij n)). Qed.

Lemma ord_pred_bij n : bijective (@ord_pred n).
Proof. exact (Bijective (@ord_predK n) (@ordSK n)). Qed.

Lemma ord_pred_inj n : injective (@ord_pred n).
Proof. exact: (bij_inj (ord_pred_bij n)). Qed.

Lemma rev_ord_proof n (i : 'I_n) : n - i.+1  < n.
Proof. by case: n i => [|n] [i lt_i_n] //; rewrite ltnS subSS leq_subr. Qed.
Definition rev_ord n i := Ordinal (@rev_ord_proof n i).

Lemma rev_ordK {n} : involutive (@rev_ord n).
Proof.
by case: n => [|n] [i lti] //; apply: val_inj; rewrite /= !subSS subKn.
Qed.

Lemma rev_ord_inj {n} : injective (@rev_ord n).
Proof. exact: inv_inj rev_ordK. Qed.

Lemma inj_leq m n (f : 'I_m -> 'I_n) : injective f -> m <= n.
Proof. by move=> /leq_card; rewrite !card_ord. Qed.
Arguments inj_leq [m n] f _.

(* bijection between any finType T and the Ordinal finType of its cardinal *)

Lemma enum_rank_subproof (T : finType) x0 (A : {pred T}) : x0 \in A -> 0 < #|A|.
Proof. by move=> Ax0; rewrite (cardD1 x0) Ax0. Qed.

HB.lock
Definition enum_rank_in (T : finType) x0 (A : {pred T}) (Ax0 : x0 \in A) x :=
  insubd (Ordinal (@enum_rank_subproof T x0 [eta A] Ax0)) (index x (enum A)).
Canonical unlockable_enum_rank_in := Unlockable enum_rank_in.unlock.

Section EnumRank.

Variable T : finType.
Implicit Type A : {pred T}.

Definition enum_rank x := @enum_rank_in T x T (erefl true) x.

Lemma enum_default A : 'I_(#|A|) -> T.
Proof. by rewrite cardE; case: (enum A) => [|//] []. Qed.

Definition enum_val A i := nth (@enum_default [eta A] i) (enum A) i.
Prenex Implicits enum_val.

Lemma enum_valP A i : @enum_val A i \in A.
Proof. by rewrite -mem_enum mem_nth -?cardE. Qed.

Lemma enum_val_nth A x i : @enum_val A i = nth x (enum A) i.
Proof. by apply: set_nth_default; rewrite cardE in i *; apply: ltn_ord. Qed.

Lemma nth_image T' y0 (f : T -> T') A (i : 'I_#|A|) :
  nth y0 (image f A) i = f (enum_val i).
Proof. by rewrite -(nth_map _ y0) // -cardE. Qed.

Lemma nth_codom T' y0 (f : T -> T') (i : 'I_#|T|) :
  nth y0 (codom f) i = f (enum_val i).
Proof. exact: nth_image. Qed.

Lemma nth_enum_rank_in x00 x0 A Ax0 :
  {in A, cancel (@enum_rank_in T x0 A Ax0) (nth x00 (enum A))}.
Proof.
move=> x Ax; rewrite enum_rank_in.unlock insubdK ?nth_index ?mem_enum //.
by rewrite cardE [_ \in _]index_mem mem_enum.
Qed.

Lemma nth_enum_rank x0 : cancel enum_rank (nth x0 (enum T)).
Proof. by move=> x; apply: nth_enum_rank_in. Qed.

Lemma enum_rankK_in x0 A Ax0 :
   {in A, cancel (@enum_rank_in T x0 A Ax0) enum_val}.
Proof. by move=> x; apply: nth_enum_rank_in. Qed.

Lemma enum_rankK : cancel enum_rank enum_val.
Proof. by move=> x; apply: enum_rankK_in. Qed.

Lemma enum_valK_in x0 A Ax0 : cancel enum_val (@enum_rank_in T x0 A Ax0).
Proof.
move=> x; apply: ord_inj; rewrite enum_rank_in.unlock insubdK; last first.
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

(* Due to the limitations of the Coq unification patterns, P can only be      *)
(* inferred from the premise of this lemma, not its conclusion. As a result   *)
(* this lemma will only be usable in forward chaining style.                  *)
Lemma fin_all_exists U (P : forall x : T, U x -> Prop) :
  (forall x, exists u, P x u) -> (exists u, forall x, P x (u x)).
Proof.
move=> ex_u; pose Q m x := enum_rank x < m -> {ux | P x ux}.
suffices: forall m, m <= #|T| -> exists w : forall x, Q m x, True.
  case/(_ #|T|)=> // w _; pose u x := sval (w x (ltn_ord _)).
  by exists u => x; rewrite {}/u; case: (w x _).
elim=> [|m IHm] ltmX; first by have w x: Q 0 x by []; exists w.
have{IHm} [w _] := IHm (ltnW ltmX); pose i := Ordinal ltmX.
have [u Pu] := ex_u (enum_val i); suffices w' x: Q m.+1 x by exists w'.
rewrite /Q ltnS leq_eqVlt (val_eqE _ i); case: eqP => [def_i _ | _ /w //].
by rewrite -def_i enum_rankK in u Pu; exists u.
Qed.

Lemma fin_all_exists2 U (P Q : forall x : T, U x -> Prop) :
    (forall x, exists2 u, P x u & Q x u) ->
  (exists2 u, forall x, P x (u x) & forall x, Q x (u x)).
Proof.
move=> ex_u; have (x): exists u, P x u /\ Q x u by have [u] := ex_u x; exists u.
by case/fin_all_exists=> u /all_and2[]; exists u.
Qed.

End EnumRank.

Arguments enum_val_inj {T A} [i1 i2] : rename.
Arguments enum_rank_inj {T} [x1 x2].
Prenex Implicits enum_val enum_rank enum_valK enum_rankK.

Lemma enum_rank_ord n i : enum_rank i = cast_ord (esym (card_ord n)) i.
Abort. (* probably no longer provable either *)
(* apply: val_inj; rewrite /enum_rank enum_rank_in.unlock.
by rewrite insubdK ?index_enum_ord // card_ord [_ \in _]ltn_ord. *)

Lemma enum_val_ord n i : enum_val i = cast_ord (card_ord n) i.
Abort. (* probably no longer provable either *)
(* by apply: canLR (@enum_rankK _) _; apply: val_inj; rewrite enum_rank_ord. *)

(* The integer bump / unbump operations. *)

Definition bump h i := (h <= i) + i.
Definition unbump h i := i - (h < i).

Lemma bumpK h : cancel (bump h) (unbump h).
Proof.
rewrite /bump /unbump => i.
have [le_hi | lt_ih] := leqP h i; first by rewrite ltnS le_hi subn1.
by rewrite ltnNge ltnW ?subn0.
Qed.

Lemma neq_bump h i : h != bump h i.
Proof.
rewrite /bump eqn_leq; have [le_hi | lt_ih] := leqP h i.
  by rewrite ltnNge le_hi andbF.
by rewrite leqNgt lt_ih.
Qed.

Lemma unbumpKcond h i : bump h (unbump h i) = (i == h) + i.
Proof.
rewrite /bump /unbump leqNgt -subSKn.
case: (ltngtP i h) => /= [-> | ltih | ->] //; last by rewrite ltnn.
by rewrite subn1 /= leqNgt !(ltn_predK ltih, ltih, add1n).
Qed.

Lemma unbumpK {h} : {in predC1 h, cancel (unbump h) (bump h)}.
Proof. by move=> i /negbTE-neq_h_i; rewrite unbumpKcond neq_h_i. Qed.

Lemma bumpDl h i k : bump (k + h) (k + i) = k + bump h i.
Proof. by rewrite /bump leq_add2l addnCA. Qed.

Lemma bumpS h i : bump h.+1 i.+1 = (bump h i).+1.
Proof. exact: addnS. Qed.

Lemma unbumpDl h i k : unbump (k + h) (k + i) = k + unbump h i.
Proof.
apply: (can_inj (bumpK (k + h))).
by rewrite bumpDl !unbumpKcond eqn_add2l addnCA.
Qed.

Lemma unbumpS h i : unbump h.+1 i.+1 = (unbump h i).+1.
Proof. exact: unbumpDl 1. Qed.

Lemma leq_bump h i j : (i <= bump h j) = (unbump h i <= j).
Proof.
rewrite /bump leq_subLR.
case: (leqP i h) (leqP h j) => [le_i_h | lt_h_i] [le_h_j | lt_j_h] //.
  by rewrite leqW (leq_trans le_i_h).
by rewrite !(leqNgt i) ltnW (leq_trans _ lt_h_i).
Qed.

Lemma leq_bump2 h i j : (bump h i <= bump h j) = (i <= j).
Proof. by rewrite leq_bump bumpK. Qed.

Lemma bumpC h1 h2 i :
  bump h1 (bump h2 i) = bump (bump h1 h2) (bump (unbump h2 h1) i).
Proof.
rewrite {1 5}/bump -leq_bump addnCA; congr (_ + (_ + _)).
rewrite 2!leq_bump /unbump /bump; case: (leqP h1 h2) => [le_h12 | lt_h21].
  by rewrite subn0 ltnS le_h12 subn1.
by rewrite subn1 (ltn_predK lt_h21) (leqNgt h1) lt_h21 subn0.
Qed.

(* The lift operations on ordinals; to avoid a messy dependent type, *)
(* unlift is a partial operation (returns an option).                *)

Lemma lift_subproof n h (i : 'I_n.-1) : bump h i < n.
Proof. by case: n i => [[]|n] //= i; rewrite -addnS (leq_add (leq_b1 _)). Qed.

Definition lift n (h : 'I_n) (i : 'I_n.-1) := Ordinal (lift_subproof h i).

Lemma unlift_subproof n (h : 'I_n) (u : {j | j != h}) : unbump h (val u) < n.-1.
Proof.
case: n h u => [|n h] [] //= j ne_jh.
rewrite -(leq_bump2 h.+1) bumpS unbumpK // /bump.
case: (ltngtP n h) => [|_|eq_nh]; rewrite ?(leqNgt _ h) ?ltn_ord //.
by rewrite ltn_neqAle [j <= _](valP j) {2}eq_nh andbT.
Qed.

Definition unlift n (h i : 'I_n) :=
  omap (fun u : {j | j != h} => Ordinal (unlift_subproof u)) (insub i).

Variant unlift_spec n h i : option 'I_n.-1 -> Type :=
  | UnliftSome j of i = lift h j : unlift_spec h i (Some j)
  | UnliftNone   of i = h        : unlift_spec h i None.

Lemma unliftP n (h i : 'I_n) : unlift_spec h i (unlift h i).
Proof.
rewrite /unlift; case: insubP => [u nhi | ] def_i /=; constructor.
  by apply: val_inj; rewrite /= def_i unbumpK.
by rewrite negbK in def_i; apply/eqP.
Qed.

Lemma neq_lift n (h : 'I_n) i : h != lift h i.
Proof. exact: neq_bump. Qed.

Lemma eq_liftF n (h : 'I_n) i : (h == lift h i) = false.
Proof. exact/negbTE/neq_lift. Qed.

Lemma lift_eqF n (h : 'I_n) i : (lift h i == h) = false.
Proof. by rewrite eq_sym eq_liftF. Qed.

Lemma unlift_none n (h : 'I_n) : unlift h h = None.
Proof. by case: unliftP => // j Dh; case/eqP: (neq_lift h j). Qed.

Lemma unlift_some n (h i : 'I_n) :
  h != i -> {j | i = lift h j & unlift h i = Some j}.
Proof.
rewrite eq_sym => /eqP neq_ih.
by case Dui: (unlift h i) / (unliftP h i) => [j Dh|//]; exists j.
Qed.

Lemma lift_inj n (h : 'I_n) : injective (lift h).
Proof. by move=> i1 i2 [/(can_inj (bumpK h))/val_inj]. Qed.
Arguments lift_inj {n h} [i1 i2] eq_i12h : rename.

Lemma liftK n (h : 'I_n) : pcancel (lift h) (unlift h).
Proof. by move=> i; case: (unlift_some (neq_lift h i)) => j /lift_inj->. Qed.

(* Shifting and splitting indices, for cutting and pasting arrays *)

Lemma lshift_subproof m n (i : 'I_m) : i < m + n.
Proof. by apply: leq_trans (valP i) _; apply: leq_addr. Qed.

Lemma rshift_subproof m n (i : 'I_n) : m + i < m + n.
Proof. by rewrite ltn_add2l. Qed.

Definition lshift m n (i : 'I_m) := Ordinal (lshift_subproof n i).
Definition rshift m n (i : 'I_n) := Ordinal (rshift_subproof m i).

Lemma lshift_inj m n : injective (@lshift m n).
Proof. by move=> ? ? /(f_equal val) /= /val_inj. Qed.

Lemma rshift_inj m n : injective (@rshift m n).
Proof. by move=> ? ? /(f_equal val) /addnI /val_inj. Qed.

Lemma eq_lshift m n i j : (@lshift m n i == @lshift m n j) = (i == j).
Proof. by rewrite (inj_eq (@lshift_inj _ _)). Qed.

Lemma eq_rshift m n i j : (@rshift m n i == @rshift m n j) = (i == j).
Proof. by rewrite (inj_eq (@rshift_inj _ _)). Qed.

Lemma eq_lrshift m n i j : (@lshift m n i == @rshift m n j) = false.
Proof.
apply/eqP=> /(congr1 val)/= def_i; have := ltn_ord i.
by rewrite def_i -ltn_subRL subnn.
Qed.

Lemma eq_rlshift m n i j : (@rshift m n i == @lshift m n j) = false.
Proof. by rewrite eq_sym eq_lrshift. Qed.

Definition eq_shift := (eq_lshift, eq_rshift, eq_lrshift, eq_rlshift).

Lemma split_subproof m n (i : 'I_(m + n)) : i >= m -> i - m < n.
Proof. by move/subSn <-; rewrite leq_subLR. Qed.

Definition split {m n} (i : 'I_(m + n)) : 'I_m + 'I_n :=
  match ltnP (i) m with
  | LtnNotGeq lt_i_m =>  inl _ (Ordinal lt_i_m)
  | GeqNotLtn ge_i_m =>  inr _ (Ordinal (split_subproof ge_i_m))
  end.

Variant split_spec m n (i : 'I_(m + n)) : 'I_m + 'I_n -> bool -> Type :=
  | SplitLo (j : 'I_m) of i = j :> nat     : split_spec i (inl _ j) true
  | SplitHi (k : 'I_n) of i = m + k :> nat : split_spec i (inr _ k) false.

Lemma splitP m n (i : 'I_(m + n)) : split_spec i (split i) (i < m).
Proof.
(* We need to prevent the case on ltnP from rewriting the hidden constructor  *)
(* argument types of the match branches exposed by unfolding split. If the    *)
(* match representation is changed to omit these then this proof could reduce *)
(* to by rewrite /split; case: ltnP; [left | right. rewrite subnKC].          *)
set lt_i_m := i < m; rewrite /split.
by case: _ _ _ _ {-}_ lt_i_m / ltnP; [left | right; rewrite subnKC].
Qed.

Variant split_ord_spec m n (i : 'I_(m + n)) : 'I_m + 'I_n -> bool -> Type :=
  | SplitOrdLo (j : 'I_m) of i = lshift _ j : split_ord_spec i (inl _ j) true
  | SplitOrdHi (k : 'I_n) of i = rshift _ k : split_ord_spec i (inr _ k) false.

Lemma split_ordP m n (i : 'I_(m + n)) : split_ord_spec i (split i) (i < m).
Proof. by case: splitP; [left|right]; apply: val_inj. Qed.

Definition unsplit {m n} (jk : 'I_m + 'I_n) :=
  match jk with inl j => lshift n j | inr k => rshift m k end.

Lemma ltn_unsplit m n (jk : 'I_m + 'I_n) : (unsplit jk < m) = jk.
Proof. by case: jk => [j|k]; rewrite /= ?ltn_ord // ltnNge leq_addr. Qed.

Lemma splitK {m n} : cancel (@split m n) unsplit.
Proof. by move=> i; case: split_ordP. Qed.

Lemma unsplitK {m n} : cancel (@unsplit m n) split.
Proof.
by move=> [j|k]; case: split_ordP => ? /eqP; rewrite eq_shift// => /eqP->.
Qed.

Section OrdinalPos.

Variable n' : nat.
Local Notation n := n'.+1.

Definition ord0 := Ordinal (ltn0Sn n').
Definition ord_max := Ordinal (ltnSn n').

Lemma leq_ord (i : 'I_n) : i <= n'. Proof. exact: valP i. Qed.

Lemma sub_ord_proof m : n' - m < n.
Proof.  by rewrite ltnS leq_subr. Qed.
Definition sub_ord m := Ordinal (sub_ord_proof m).

Lemma sub_ordK (i : 'I_n) : n' - (n' - i) = i.
Proof. by rewrite subKn ?leq_ord. Qed.

Definition inord m : 'I_n := insubd ord0 m.

Lemma inordK m : m < n -> inord m = m :> nat.
Proof. by move=> lt_m; rewrite val_insubd lt_m. Qed.

Lemma inord_val (i : 'I_n) : inord i = i.
Proof. by rewrite /inord /insubd valK. Qed.

Lemma enum_ordSl : enum 'I_n = ord0 :: map (lift ord0) (enum 'I_n').
Abort. (* probably no longer provable either *)
(* apply: (inj_map val_inj); rewrite val_enum_ord /= -map_comp.
by rewrite (map_comp (addn 1)) val_enum_ord -iotaDl. *)

Lemma enum_ordSr :
  enum 'I_n = rcons (map (widen_ord (leqnSn _)) (enum 'I_n')) ord_max.
Abort. (* probably no longer provable either *)
(* apply: (inj_map val_inj); rewrite val_enum_ord.
rewrite -[in iota _  _]addn1 iotaD/= cats1 map_rcons; congr (rcons _ _).
by rewrite -map_comp/= (@eq_map _ _ _ val) ?val_enum_ord. *)

Lemma lift_max (i : 'I_n') : lift ord_max i = i :> nat.
Proof. by rewrite /= /bump leqNgt ltn_ord. Qed.

Lemma lift0 (i : 'I_n') : lift ord0 i = i.+1 :> nat. Proof. by []. Qed.

End OrdinalPos.

Arguments ord0 {n'}.
Arguments ord_max {n'}.
Arguments inord {n'}.
Arguments sub_ord {n'}.
Arguments sub_ordK {n'}.
Arguments inord_val {n'}.

Lemma ord1 : all_equal_to (ord0 : 'I_1).
Proof. by case=> [[] // ?]; apply: val_inj. Qed.

(* Product of two fintypes which is a fintype *)
Section ProdFinType.

Variable T1 T2 : finType.

Definition prod_enum := [seq (x1, x2) | x1 <- enum T1, x2 <- enum T2].

(* TODO: move in seq.v *)
Lemma size_allpairsX T1' T2' (s1 : seq T1') (s2 : seq T2') P1 P2 :
  size [seq x <- [seq (x1, x2) | x1 <- s1, x2 <- s2] | [predX P1 & P2] x]
  = size [seq x <- s1 | P1 x] * size [seq x <- s2 | P2 x].
Proof.
elim: s1 => [//|x1 s1 IHs1].
rewrite filter_cat size_cat IHs1 filter_map /preim/= -[P1 x1]/(x1 \in P1).
by case: (x1 \in P1); rewrite size_map// filter_pred0.
Qed.

(* TODO: /move above *)
Lemma supportIl (T : eqType) (A B : {finpred T}) :
  support [predI A & B] =i filter [in B] (support A).
Proof. by move=> x; rewrite mem_support mem_filter mem_support andbC. Qed.

Lemma supportIr (T : eqType) (A B : {finpred T}) :
  support [predI A & B] =i filter [in A] (support B).
Proof. by move=> x; rewrite mem_support mem_filter mem_support. Qed.

Lemma enumIl (T : choiceType) (A B : {finpred T}) :
  enum [predI A & B] = filter [in B] (enum A).
Proof.
rewrite unlock filter_sort; [|exact:prec_eq_total|exact: prec_eq_trans].
apply: (sorted_eq (@prec_eq_trans _) (@prec_eq_antisymmetric _)).  (* TODO: rename prec_eq_antisymmetric in prec_eq_anti *)
- exact/sort_sorted/prec_eq_total.
- exact/sort_sorted/prec_eq_total.
apply: uniq_perm; rewrite ?sort_uniq ?filter_uniq// => x.
by rewrite !mem_sort supportIl.
Qed.

Lemma enumIr (T : choiceType) (A B : {finpred T}) :
  enum [predI A & B] = filter [in B] (enum A).
Proof. by rewrite -enumIl; apply: eq_enum => x; rewrite inE andbC. Qed.

Lemma enum_fin (T : finType) (A : {finpred T}) :
  enum A = filter [in A] (enum T).
Proof.
by rewrite -enumIl; apply: eq_enum => x; rewrite /= [in RHS]inE andb_idl.
Qed.
(* TODO: move above/ *)

Lemma predX_prod_enum (A1 : {finpred T1}) (A2 : {finpred T2}) :
  count [predX A1 & A2] prod_enum = #|A1| * #|A2|.
Proof. by rewrite !cardE /prod_enum -size_filter size_allpairsX 2!enum_fin. Qed.

Lemma prod_enumP : Finite.axiom prod_enum.
Proof.
by case=> x1 x2; rewrite (predX_prod_enum (pred1 x1) (pred1 x2)) !card1.
Qed.

HB.instance Definition _ := isFinite.Build (T1 * T2)%type prod_enumP.

Lemma cardX (A1 : {pred T1}) (A2 : {pred T2}) :
  #|[predX A1 & A2]| = #|A1| * #|A2|.
Proof.
rewrite -predX_prod_enum cardE enum_fin size_filter.
have upe : uniq prod_enum by apply: allpairs_uniq => // [[x1 y1] [x2 y2]].
rewrite -[enum _]undup_id// -[prod_enum]undup_id//.
apply: eq_count_undup => [[x y] /andP/=[xA1 yA2]]; rewrite mem_enum/= !inE.
by have:= (count_uniq_mem (x, y) upe); case: in_mem => //; rewrite prod_enumP.
Qed.

Lemma card_prod : #|{: T1 * T2}| = #|T1| * #|T2|.
Proof. by rewrite -cardX; apply: eq_card; case. Qed.

Lemma eq_card_prod (A : {pred (T1 * T2)}) : A =i predT -> #|A| = #|T1| * #|T2|.
Proof. exact: eq_card_trans card_prod. Qed.

End ProdFinType.

Section TagFinType.

Variables (I : finType) (T_ : I -> finType).

Definition tag_enum :=
  flatten [seq [seq Tagged T_ x | x <- enumF (T_ i)] | i <- enumF I].

Lemma tag_enumP : Finite.axiom tag_enum.
Proof.
case=> i x; rewrite -(Finite.enumP i) /tag_enum -enumT.
elim: (enum I) => //= j e IHe; rewrite count_cat count_map {}IHe; congr (_ + _).
case: eqP => [-> | ne_j_i]; rewrite /preim/= /Tagged /eq_op/= /tag_eq/=.
  under eq_count => y do rewrite /= tagged_asE eqxx/=.
  by apply/eqP; rewrite -enumT count_uniq_mem ?mem_enum.
by have /eqP/negbTE-> := ne_j_i; rewrite /= count_pred0.
Qed.

HB.instance Definition _ := isFinite.Build {i : I & T_ i} tag_enumP.

Lemma card_tagged :
  #|{: {i : I & T_ i}}| = sumn (map (fun i => #|T_ i|) (enum I)).
Proof.
rewrite cardE ![in LHS]enumT unlock size_sort size_flatten /shape -map_comp.
rewrite enumT; congr (sumn _).
by apply: eq_map => i /=; rewrite -enumT size_map -cardE.
Qed.

End TagFinType.

Section SumFinType.

Variables T1 T2 : finType.

Definition sum_enum :=
  [seq inl _ x | x <- enumF T1] ++ [seq inr _ y | y <- enumF T2].

Lemma sum_enum_uniq : uniq sum_enum.
Proof.
rewrite cat_uniq -!enumT !(enum_uniq, map_inj_uniq); try by move=> ? ? [].
by rewrite andbT; apply/hasP=> [[_ /mapP[x _ ->] /mapP[]]].
Qed.

Lemma mem_sum_enum u : u \in sum_enum.
Proof. by case: u => x; rewrite mem_cat -!enumT map_f ?mem_enum ?orbT. Qed.

HB.instance Definition sum_isFinite := isFinite.Build (T1 + T2)%type
  (Finite.uniq_axiom sum_enum_uniq mem_sum_enum).

Lemma card_sum : #|{: T1 + T2}| = #|T1| + #|T2|.
Proof.
by rewrite !cardT !enumT [in LHS]unlock size_sort size_cat !size_map.
Qed.

End SumFinType.

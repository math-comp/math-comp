(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

(******************************************************************************)
(* This file contains the definitions of:                                     *)
(*   choiceType == interface for types with a choice operator.                *)
(*    countType == interface for countable types (implies choiceType).        *)
(* subCountType == interface for types that are both subType and countType.   *)
(*  xchoose exP == a standard x such that P x, given exP : exists x : T, P x  *)
(*                 when T is a choiceType. The choice depends only on the     *)
(*                 extent of P (in particular, it is independent of exP).     *)
(*   choose P x0 == if P x0, a standard x such that P x.                      *)
(*      pickle x == a nat encoding the value x : T, where T is a countType.   *)
(*    unpickle n == a partial inverse to pickle: unpickle (pickle x) = Some x *)
(*  pickle_inv n == a sharp partial inverse to pickle pickle_inv n = Some x   *)
(*                  if and only if pickle x = n.                              *)
(*            choiceMixin T == type of choice mixins; the exact contents is   *)
(*                        documented below in the Choice submodule.           *)
(*           ChoiceType T m == the packed choiceType class for T and mixin m. *)
(* [choiceType of T for cT] == clone for T of the choiceType cT.              *)
(*        [choiceType of T] == clone for T of the choiceType inferred for T.  *)
(*            CountType T m == the packed countType class for T and mixin m.  *)
(*  [countType of T for cT] == clone for T of the countType cT.               *)
(*        [count Type of T] == clone for T of the countType inferred for T.   *)
(* [choiceMixin of T by <:] == Choice mixin for T when T has a subType p      *)
(*                        structure with p : pred cT and cT has a Choice      *)
(*                        structure; the corresponding structure is Canonical.*)
(*  [countMixin of T by <:] == Count mixin for a subType T of a countType.    *)
(*  PcanChoiceMixin fK == Choice mixin for T, given f : T -> cT where cT has  *)
(*                        a Choice structure, a left inverse partial function *)
(*                        g and fK : pcancel f g.                             *)
(*   CanChoiceMixin fK == Choice mixin for T, given f : T -> cT, g and        *)
(*                        fK : cancel f g.                                    *)
(*   PcanCountMixin fK == Count mixin for T, given f : T -> cT where cT has   *)
(*                        a Countable structure, a left inverse partial       *)
(*                        function g and fK : pcancel f g.                    *)
(*    CanCountMixin fK == Count mixin for T, given f : T -> cT, g and         *)
(*                        fK : cancel f g.                                    *)
(*      GenTree.tree T == generic n-ary tree type with nat-labeled nodes and  *)
(*                        T-labeled leaves, for example GenTree.Leaf (x : T), *)
(*                        GenTree.Node 5 [:: t; t']. GenTree.tree is equipped *)
(*                        with canonical eqType, choiceType, and countType    *)
(*                        instances, and so simple datatypes can be similarly *)
(*                        equipped by encoding into GenTree.tree and using    *)
(*                        the mixins above.                                   *)
(*        CodeSeq.code == bijection from seq nat to nat.                      *)
(*      CodeSeq.decode == bijection inverse to CodeSeq.code.                  *)
(* In addition to the lemmas relevant to these definitions, this file also    *)
(* contains definitions of a Canonical choiceType and countType instances for *)
(* all basic datatypes (e.g., nat, bool, subTypes, pairs, sums, etc.).        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require ssrsearch.

(******************************************************************************)
(**** ssrfun contents                                                      ****)
(******************************************************************************)

(** header **)
(*    nfun n A R == A -> ... A -> R (with n A arguments).                     *)
(*   ndfun n A R == forall (i1 : D) (x1 : A i1) ... (xn : A i_n), R           *)
(*      S <--> T == S and T are equipotent types (i.e., S -> T and T -> S).   *)
(* move_view S T == an S -> T wrapper that does _NOT_ coerce to S -> T, but   *)
(*                  is usable as an S -> T move/ view. Useful for views with  *)
(*                  indeterminate T, to force matching the top assumption     *)
(*                  with S and prevent overapplication of the view.           *)
(*      Forall P == forall x, P x for P : A -> S with A a Type and S a sort.  *)
(*                  A forallSort structure implicit argument handles the      *)
(*                  nonuniform forall typing rules for Type/Set/Prop (SProp,  *)
(*                  which follows a different pattern, is not handled). The   *)
(*                  Forall combinator can be used as a rewrite or projection  *)
(*                  head constant, and for congruence (i.e., congr Forall).   *)
(*  \Forall x ... z, E == Forall (fun x => ... Forall (fun z => E) ... ).     *)
(*       ForallI == change the first forall in the goal into a Forall (this   *)
(*                  might be a non-dependent forall, i.e., P -> Q).           *)
(*   ForallI pat == change the term described by pat into a Forall.           *)
(*   wrappedType == specialization of wrapped to Type, which coerces to Type  *)
(*                  and whose default instance has 4 wrapping layers.         *)
(*   wrappedProp == specialization of wrapped to Prop, which coerces to Type  *)
(*                  and whose default instance has 4 wrapping layers.         *)

(* option complements *)

Lemma isSome_map S T (f : S -> T) u : isSome (omap f u) = u.
Proof. by case: u. Qed.

Lemma isSome_bind S T (f : S -> option T) u : isSome (obind f u) -> u.
Proof. by case: u. Qed.

Lemma ocancel_id T f x : @ocancel T T f id -> f x -> f x = Some x.
Proof. by move=> /(_ x); case: f => //= _ ->. Qed.

(* n-ary function type constructors. *)

Definition nfun n A := iter n (fun R => A -> R).
Definition ndfun n {D} A := iter n (fun R => forall (i : D) (x : A i), R).

(* More eq groupoid lemmas (in addition to the existing esymK). *)
(* Most of these are in Logic, under a different naming convention. *)

Section EqGroupoid.

Variables (S R : Type) (T U : S -> Type) (V : R -> Type).
Variables (f : S -> R) (g : forall x, T x) (h : forall x, T x -> U x).
Variable (k : forall x, T x -> V (f x)).
Variables x1 x2 x3 x4 : S.
Hypotheses (eq12 : x1 = x2) (eq23 : x2 = x3) (eq34 : x3 = x4).

Definition etransr (eq31 : x3 = x1) : x3 = x2 := etrans eq31 eq12.
Definition etransl (eq13 : x1 = x3) : x2 = x3 := etrans (esym eq12) eq13.

Lemma etrans_refl : etrans (erefl x1) eq12 = eq12.
Proof. by case: x2 / eq12. Defined.

Lemma etrans_reflr : etrans eq12 (erefl x2) = eq12. Proof. by []. Defined.

Lemma etrans_syml : etrans (esym eq12) eq12 = erefl x2.
Proof. by case: x2 / eq12. Defined.

Lemma etrans_symr : etrans eq12 (esym eq12) = erefl x1.
Proof. by case: x2 / eq12. Defined.

Lemma esym_trans : esym (etrans eq12 eq23) = etrans (esym eq23) (esym eq12).
Proof. by case: x3 / eq23; case: x2 / eq12. Defined.

Lemma etransA : etrans eq12 (etrans eq23 eq34) = etrans (etrans eq12 eq23) eq34.
Proof. by case: x4 / eq34. Defined.

Lemma etransKl : etrans (esym eq12) (etrans eq12 eq23) = eq23.
Proof. by case: x3 / eq23; apply: etrans_syml. Defined.

Lemma etransKVl (eq13 : x1 = x3) : etrans eq12 (etrans (esym eq12) eq13) = eq13.
Proof. by case: x3 / eq13; apply: etrans_symr. Defined.

Lemma etransKr : etrans (etrans eq12 eq23) (esym eq23) = eq12.
Proof. by case: x3 / eq23. Defined.

Lemma etransKVr (eq32 : x3 = x2) : etrans (etrans eq12 (esym eq32)) eq32 = eq12.
Proof. by case: x2 / eq32 eq12. Defined.

(* Transport action. *)

Notation ecastT E y := (ecast x (T x) E y).

Lemma ecast_refl y : ecastT (erefl x1) y = y. Proof. by []. Defined.

Lemma ecast_trans y : ecastT (etrans eq12 eq23) y = ecastT eq23 (ecastT eq12 y).
Proof. by case: x3 / eq23. Defined.

Lemma ecastK y : ecastT (esym eq12) (ecastT eq12 y) = y.
Proof. by case: x2 / eq12. Defined.

Lemma ecastKv y : ecastT eq12 (ecastT (esym eq12) y) = y.
Proof. by case: x2 / eq12 y. Defined.

(* Congruence morphism. *)

Notation "e ^f" := (congr1 f e) (at level 8, format "e ^f") : type_scope.

Lemma congr1refl : (erefl x1)^f = erefl (f x1). Proof. by []. Defined.

Lemma congr1trans : (etrans eq12 eq23)^f = etrans eq12^f eq23^f.
Proof. by case: x3 / eq23. Defined.

Lemma congr1sym : (esym eq12)^f = esym eq12^f.
Proof. by case: x2 / eq12. Defined.

Lemma ecast_congr1 z :
  ecast y (V y) (congr1 f eq12) z = ecast x (V (f x)) eq12 z.
Proof. by case: x2 / eq12. Defined.

Lemma ecast_congrT y : ecast U U (congr1 T eq12) y = ecast x (T x) eq12 y.
Proof. by case: x2 / eq12. Defined.

(* Cast substitution *)

Lemma ecast_const y : ecast x R eq12 y = y. Proof. by case: x2 / eq12. Defined.

Lemma ecast_subst : ecast x (T x) eq12 (g x1) = g x2.
Proof. by case: x2 / eq12. Defined.

Lemma ecast_subst_fun y : ecast x (U x) eq12 (h y) = h (ecast x (T x) eq12 y).
Proof. by case: x2 / eq12. Defined.

Lemma ecast_subst_congr z :
  ecast y (V y) (congr1 f eq12) (k z) = k (ecast x (T x) eq12 z).
Proof. by case: x2 / eq12. Defined.

End EqGroupoid.

Lemma congr1idl T h (id_h : id =1 h) x : congr1 h (id_h x) = id_h (h x : T).
Proof.
set Exhx := id_h x; set Exy := Exhx; set y := h x in Exy *.
transitivity (etrans (etrans (esym Exy) Exhx) (congr1 h Exy)).
  by rewrite etrans_syml etrans_refl.
by case: y / Exy; rewrite etrans_refl.
Defined.

Lemma congr1idr T h (h_id : h =1 id) x : congr1 h (h_id x) = h_id (h x : T).
Proof.
pose id_h x := esym (h_id x).
by rewrite -[h_id x]esymK congr1sym (congr1idl id_h) esymK.
Defined.

(* Making nat equalities normalize to erefl on ground instances. *)

Definition nat_cast : forall m n, m = n -> m = n :=
  let fix addr i j := if i is i1.+1 then addr i1 j.+1 else j in
  let eqn i j k := addr i j = addr i k in
  let fix loop i j1 k1 : eqn i j1 k1 -> eqn i j1 k1 := match j1, k1 with
    j.+1, k.+1 => loop i.+1 j k | 0, 0 => fun=> erefl | _, _ => id
  end in loop 0.
Arguments nat_cast {m n} eq_mn : simpl never.

Lemma nat_castK n Enn : @nat_cast n n Enn = erefl n.
Proof.
rewrite /nat_cast; set loop := (loop in loop 0).
set addr := fix addr i j := if i is k.+1 then addr k j.+1 else j in loop *.
rewrite -[n]/(addr 0 n) -[loop 0 _ _]/(loop 0 n n) in Enn *.
elim: n => [|n IHn] //= in (m := 0) Enn *; apply: (IHn m.+1 Enn).
Defined.

Lemma nat_castE m n Emn : @nat_cast m n Emn = Emn.
Proof. by case: n / Emn; apply: nat_castK. Qed.

Lemma nat_cast_irr m n Emn1 Emn2 : @nat_cast m n Emn1 = nat_cast Emn2.
Proof. by case: n / {Emn2}(nat_cast Emn2) in Emn1 *; apply: nat_castK. Defined.

Polymorphic Lemma nat_cast_r@{i} n (T : forall m, m = n -> Type@{i}) :
  T n (erefl n) -> forall m (Emn : m = n), T m (nat_cast Emn).
Proof.
move=> Tnn m Emn; case: m / {Emn}(nat_cast (esym Emn)) (Emn) => Emn.
by rewrite nat_castK.
Defined.

Polymorphic Lemma nat_castS@{i} m n (Emn : m = n) (Emn1 : m.+1 = n.+1)
             (T : nat -> Type@{i}) (x : T m.+1) :
  ecast n (T n) (nat_cast Emn1) x = ecast n (T n.+1) (nat_cast Emn) x.
Proof.
by case: n / {Emn}(nat_cast Emn) in x Emn1 *; rewrite nat_castK.
Defined.

(******************************************************************************)
(* A wrapper for view lemmas with an indeterminate conclusion (of the form    *)
(* forall ... T ..., pattern -> T), and for which the intended view pattern   *)
(* may fail to match some assumptions. This wrapper ensures that such views   *)
(* are only used in the forward direction (as in move/), and only with the    *)
(* appropriate move_viewP hint, preventing its application to an arbitrary    *)
(* assumption A by the instatiation to A -> T' of its indeterminate           *)
(* conclusion T. This is similar to the implies wrapper, except move_viewP is *)
(* NOT declared as a coercion - it must be used explicitly to apply the view  *)
(* manually to an assumption (as in, move_viewP my_view some_assumption).     *)
(******************************************************************************)

Variant move_view S T := MoveView of S -> T.
Definition move_viewP {S T} mv : S -> T := let: MoveView v := mv in v.
Hint View for move/ move_viewP|2.

(******************************************************************************)
(* Type-level equivalence                                                     *)
(******************************************************************************)

Variant equivT S T := EquivT of S -> T & T -> S.
Notation "S <--> T" := (equivT S T) (at level 95, no associativity).

Definition equivT_refl S : S <--> S := EquivT id id.
Definition equivT_transl {S T U} : S <--> T -> S <--> U -> T <--> U :=
  fun '(EquivT S_T T_S) '(EquivT S_U U_S) => EquivT (S_U \o T_S) (S_T \o U_S).
Definition equivT_sym {S T} : S <--> T -> T <--> S :=
   equivT_transl^~ (equivT_refl S).
Definition equivT_trans {S T U} : S <--> T -> T <--> U -> S <--> U :=
   equivT_transl \o equivT_sym.
Definition equivT_transr {S T U} eqST : U <--> S -> U <--> T :=
   equivT_trans^~ eqST.
Definition equivT_Prop (P Q : Prop) : (P <--> Q) <-> (P <-> Q).
Proof. split; destruct 1; split; assumption. Defined.
Definition equivT_LR {S T} '(EquivT S_T _) : S -> T := S_T.
Definition equivT_RL {S T} '(EquivT _ T_S) : T -> S := T_S.

Hint View for move/ equivT_LR|2 equivT_RL|2.
Hint View for apply/ equivT_RL|2 equivT_LR|2.

(******************************************************************************)
(*   A generic Forall "constructor" for the Gallina forall quantifier, i.e.,  *)
(*   \Forall x, P := Forall (fun x => P) := forall x, P.                      *)
(* The main use of Forall is to apply congruence to a forall equality:        *)
(*    congr1 Forall : forall P Q, P = Q -> Forall P = Forall Q.               *)
(* in particular in a classical setting with function extensionality, where   *)
(* we can have (forall x, P x = Q x) -> (forall x, P x) = (forall x, Q x).    *)
(*   We use a forallSort structure to factor the ad hoc PTS product formation *)
(* rules; forallSort is keyed on the type of the entire forall expression, or *)
(* (up to subsumption) the type of the forall body - this is always a sort.   *)
(*   This implementation has two important limitations:                       *)
(*     1) It cannot handle the SProp sort and its typing rules. However, its  *)
(*        main application is extensionality, which is not compatible with    *)
(*        SProp because an (A : SProp) -> B "function" is not a generic       *)
(*        (A : Type) -> B function as SProp is not included in Type.          *)
(*     2) The Forall constructor can't be inserted by a straightforward       *)
(*        unfold (as in, rewrite -[forall x, _]/(Forall _)) because of the    *)
(*        way Coq unification handles Type constraints. The ForallI tactic    *)
(*        mitigates this issue, but there are additional issues with its      *)
(*        implementation -- see below.                                        *)
(******************************************************************************)

Structure forallSort A :=
  ForallSort {forall_sort :> Type; _ : (A -> forall_sort) -> forall_sort}.

Notation mkForallSort A S := (@ForallSort A S (fun T => forall x, T x)).
Polymorphic Definition TypeForall (S := Type) (A : S) := mkForallSort A S.
Canonical TypeForall.

Canonical PropForall A := mkForallSort A Prop.

(* This is just a special case of TypeForall, but it provides a projection    *)
(* for the Set sort "constant".                                               *)
Canonical SetForall (A : Set) := mkForallSort A Set.

Definition Forall {A} {S : forallSort A} :=
  let: ForallSort _ F := S return (A -> S) -> S in F.

Notation "\Forall x .. z , T" :=
   (Forall (fun x => .. (Forall (fun z => T)) ..))
  (at level 200, x binder, z binder, T at level 200,
   format "'[hv' '\Forall'  '[' x .. z , ']' '/ '  T ']'") : type_scope.

(*  The ForallI implementation has to work around several Coq 8.12 issues:    *)
(*    - Coq unification defers Type constraints so we must ensure the type    *)
(*      constraint for the forall term F is processed, and the resulting      *)
(*      sort unified with the forall_sort projection _BEFORE_ F is unified    *)
(*      with a Forall _ pattern, because the inferred forallSort structure    *)
(*      determines the actual shape of that pattern. This is done by passing  *)
(*      F to erefl, then constraining the type of erefl to Forall _ = _. Note *)
(*      that putting a redundant F on the right hand side would break due to  *)
(*      incomplete handling of subtyping.                                     *)
(*    - ssr rewrite and Coq replace do not handle universe constraints.       *)
(*      and rewrite does not handle subsumption of the redex type. This means *)
(*      we cannot use rewrite, replace or fold, and must resort to primitive  *)
(*      equality destruction.                                                 *)
(*    - ssr case: and set do not recognize ssrpatternarg parameters, so we    *)
(*      must rely on ssrmatching.ssrpattern.                                  *)
Tactic Notation "ForallI" ssrpatternarg(pat) :=
  let F := fresh "F" in ssrmatching.ssrpattern pat => F;
  case: F / (@erefl _ F : Forall _ = _).
Tactic Notation "ForallI" := ForallI (forall x, _).

(* An alternative, more complete implementation. Needs to be simplified by 
   making use of the sort polymorphism introdced in Coq 8.19
(******************************************************************************)
(*   A generic Forall "constructor" for the Gallina forall quantifier, i.e.,  *)
(*   \Forall x, P := Forall (fun x => P) := forall x, P.                      *)
(* The main use of Forall is to apply congruence to a forall equality:        *)
(*    congr1 Forall : forall P Q, P = Q -> Forall P = Forall Q.               *)
(* in particular in a classical setting with function extensionality, where   *)
(* we can have (forall x, P x = Q x) -> (forall x, P x) = (forall x, Q x).    *)
(*   We use a forallSort structure to factor the ad hoc PTS product formation *)
(* rules; forallSort is keyed on the type of the entire forall expression, or *)
(* (up to subsumption) the type of the forall body - this is always a sort.   *)
(*   This implementation has two important limitations:                       *)
(*     1) It cannot handle the SProp sort and its typing rules. However, its  *)
(*        main application is extensionality, which is not compatible with    *)
(*        SProp because an (A : SProp) -> B "function" is not a generic       *)
(*        (A : Type) -> B function as SProp is not included in Type.          *)
(*     2) The Forall constructor can't be inserted by a straightforward       *)
(*        unfold (as in, rewrite -[forall x, _]/(Forall _)) because of the    *)
(*        way Coq unification handles Type constraints. The ForallI tactic    *)
(*        mitigates this issue, but there are additional issues with its      *)
(*        implementation -- see below.                                        *)
(******************************************************************************)

Module Forall.

Section Definitions.

Set Universe Polymorphism.

Structure sort@{i m n | i < m, m < n} : Type@{n} := PackSort {
  sort_ : Type@{m};
  #[canonical=no] ForallType (A : Type@{i}) : (A -> sort_) -> sort_;
  #[canonical=no] ForallSProp (A : SProp) : (A -> sort_) -> sort_
}.
Local Coercion sort_ : sort >-> Sortclass.

Local Notation make_forall := (fun _ B => forall x, B x) (only parsing).
Notation Sort S := (@PackSort S make_forall make_forall).
Definition PropSort@{i m n}  : sort@{i m n} := Sort Prop.
Definition SPropSort@{i m n} : sort@{i m n} := Sort SProp.
Definition SetSort@{m n}     : sort@{Set m n} := Sort Set.
Definition TypeSort@{i m n}  : sort@{i m n} := Sort Type@{i}.

Structure argSort@{i m n} : Type@{n} := ArgSort {
  arg_sort : Type@{m};
  #[canonical=no] pred_sort : arg_sort -> sort@{i m n} -> Type@{m};
  #[canonical=no] Forall A S : pred_sort A S -> S
}.
Local Coercion arg_sort : argSort >-> Sortclass.

Notation Arg sA F := (@ArgSort sA (fun A S => A -> S) (fun A S => F S A)).
Definition PropArg@{i m n} := Arg Prop ForallType@{i m n}.
Definition SPropArg@{i m n} := Arg SProp ForallSProp@{i m n}.
Definition SetArg@{i m n} := Arg Set ForallType@{i m n}.
Definition TypeArg@{i j m n} := Arg Type@{j} ForallType@{i m n}.

Structure labeled@{n} (S : Type@{n}) : Type@{n} := LabelSProp { get : S }.
Definition LabelInSProp := LabelSProp.
Definition LabelInProp := LabelInSProp.
Definition LabelProp := LabelInProp.
Definition LabelType@{n} S F := @LabelProp@{n} S F.

Variant cast@{n} {T : Type@{n}} (x : T) : T -> Type@{n} := Cast : cast x x.
Definition cast_to {T x y} (Exy : @cast T x y) B :=
  let: Cast in cast _ y := Exy return B x -> B y in id.
Arguments cast_to {T x y} Exy B.
Definition cast_from {T x y} (Exy : @cast T x y) B :=
  let: Cast in cast _ y := Exy return B y -> B x in id.  
Arguments cast_from {T x y} Exy B.

Structure pattern@{i m n} sA (S : sort@{i m n}) A B := Pattern {
   pattern_ : labeled S;
   #[canonical=no] cast_pattern : cast (get pattern_) (@Forall sA A S B)
}.

Definition SPropPattern@{i m n} S (A : SProp) B :=
  @Pattern SPropArg@{i m n} S A B (LabelSProp (ForallSProp B)) (Cast _).
Definition TypePattern@{i m n} S A B :=
  @Pattern TypeArg@{i i m n} S A B (LabelType (ForallType B)) (Cast _).

Structure predPattern@{i m n} sA A S : Type@{n} := PredPattern {
  pred_pattern : labeled@{n} Type@{m};
  #[canonical=no] coerce_pred_pattern :
     get pred_pattern -> @pred_sort@{i m n} sA A S
}.

Definition SPropPredPattern@{i m n} (A : SProp) S :=
  @PredPattern@{i m n} SPropArg A S (LabelSProp (A -> S)) id.
Definition PropPredPattern@{i m n} (A : Prop) S :=
  @PredPattern@{i m n} PropArg A S (LabelProp (A -> S)) id.
Definition PredInPropPattern@{i j m n} (A : Type@{j}) :=
  @PredPattern@{i m n} TypeArg A PropSort
    (@LabelInProp Type@{m} (A -> Prop)) id.
Definition PredInSPropPattern@{i j m n} (A : Type@{j}) :=
  @PredPattern@{i m n} TypeArg A SPropSort
    (@LabelInSProp Type@{m} (A -> SProp)) id.
Definition TypePredPattern@{i j k m n} (A : Type@{j}) :=
  @PredPattern@{i m n} TypeArg A TypeSort
    (@LabelType Type@{m} (A -> Type@{k})) id.

End Definitions.

Module Exports.

Coercion sort_ : sort >-> Sortclass.
Canonical PropSort.
Canonical SPropSort.
Canonical SetSort.
Canonical TypeSort.

Coercion arg_sort : argSort >-> Sortclass.
Arguments Forall {sA} A%type S%type P%type : rename.
Canonical PropArg.
Canonical SPropArg.
Canonical SetArg.
Canonical TypeArg.

Canonical LabelType.
Arguments cast_to {T x y} Exy B.
Arguments cast_from {T x y} Exy B.

Coercion pattern_ : pattern >-> labeled.
Canonical SPropPattern.
Canonical TypePattern.

Coercion pred_pattern : predPattern >-> labeled.
Canonical SPropPredPattern.
Canonical PredInPropPattern.
Canonical PredInSPropPattern.
Canonical PropPredPattern.
Canonical TypePredPattern.

Definition Forall {sA A S sB} B := Forall A S (@coerce_pred_pattern sA A S sB B).

Notation "\Forall x .. z , T" :=
   (Forall (fun x => .. (Forall (fun z => T)) ..))
  (at level 200, x binder, z binder, T at level 200,
   format "'[hv' '\Forall'  '[' x .. z , ']' '/ '  T ']'") : type_scope.

(*  The ForallI implementation has to work around several Coq 8.12 issues:    *)
(*    - Coq unification defers Type constraints so we must ensure the type    *)
(*      constraint for the forall term F is processed, and the resulting      *)
(*      sort unified with the forall_sort projection _BEFORE_ F is unified    *)
(*      with a Forall _ pattern, because the inferred forallSort structure    *)
(*      determines the actual shape of that pattern. This is done by passing  *)
(*      F to erefl, then constraining the type of erefl to Forall _ = _. Note *)
(*      that putting a redundant F on the right hand side would break due to  *)
(*      incomplete handling of subtyping.                                     *)
(*    - ssr rewrite and Coq replace do not handle universe constraints.       *)
(*      and rewrite does not handle subsumption of the redex type. This means *)
(*      we cannot use rewrite, replace or fold, and must resort to primitive  *)
(*      equality destruction.                                                 *)
(*    - ssr case: and set do not recognize ssrpatternarg parameters, so we    *)
(*      must rely on ssrmatching.ssrpattern.                                  *)

Tactic Notation "ForallI" ssrpatternarg(pat) :=
  let F := fresh "F" in let A := fresh "A" in
  ssrmatching.ssrpattern pat;
  set A := (A in let F := forall x : A, _ in _) => F;
  case: {A} F / (let S : sort := _ in @erefl S F : @Forall _ A S _ _ = _).
Tactic Notation "ForallI" := ForallI (forall x, _).

(*
Tactic Notation "ForallI" ssrpatternarg(pat) :=
  let F := fresh "F" in ssrmatching.ssrpattern pat => F;
  case: F / (@erefl _ F : ForallType _ = _).
Tactic Notation "ForallI" := ForallI (forall x, _).
*)

End Exports.
End Forall.
Export Forall.Exports.
*)

(******************************************************************************)
(*   We define specialized copies of the wrapped structure of ssrfun for Prop *)
(* and Type, as we need more than two alternative rules (indeed, 3 for Prop   *)
(* and 4 for Type). We need separate copies for Prop and Type as universe     *)
(* polymorphism cannot instantiate Type with Prop.                            *)
(******************************************************************************)

Structure wrappedProp := WrapProp {unwrap_Prop :> Prop}.
Definition wrap4Prop := WrapProp.
Definition wrap3Prop := wrap4Prop.
Definition wrap2Prop := wrap3Prop.
Canonical wrap1Prop P := wrap2Prop P.

Polymorphic Structure wrappedType@{i} := WrapType {unwrap_Type :> Type@{i}}.
Polymorphic Definition wrap4Type@{i} := WrapType@{i}.
Polymorphic Definition wrap3Type@{i} := wrap4Type@{i}.
Polymorphic Definition wrap2Type@{i} := wrap3Type@{i}.
Polymorphic Definition wrap1Type@{i} (T : Type@{i}) := wrap2Type T.
Canonical wrap1Type.

(******************************************************************************)
(*    Universe polymorphic dependent pairs (i.e., sigT in Init.Datatypes),    *)
(* with more supporting Notation, in particular for constructors and non      *)
(* dependent pairs.                                                           *)
(******************************************************************************)

Polymorphic Variant dpair@{i} {A : Type@{i}} (T : A -> Type@{i}) : Type@{i} :=
  Dpair x of T x.

Notation "{ 'dpair' x .. z , T }" :=
    (dpair (fun x => .. (dpair (fun z => T)) .. ))
  (at level 0, x binder, z binder,
   format "{ '[hv' 'dpair' '['  x '/'  .. '/'  z , ']' '/ '  T } ']'")
  : type_scope.
Notation "{ 'pair' S , T }" := {dpair _ : S, T}
  (at level 0, format "{ 'pair'  S ,  T }") : type_scope.

Arguments Dpair {A T} x y.
Polymorphic Definition Pair@{i} {S T : Type@{i}} : S -> T -> {pair S, T} :=
  @Dpair S (fun=> T).
Notation "[ 'dpair' x := y , v : T ]" := (@Dpair _ (fun x => T) y v)
  (at level 0, x ident, v at level 99,
   format "[ 'dpair' '[hv'  x  :=  y , '/'  v  :  T ] ']'") : form_scope.
Notation "[ 'dpair' x : A := y , v : T ]" := (@Dpair A (fun x => T) y v)
  (at level 0, x ident, v at level 99, only parsing) : form_scope.
Notation "[ 'dpair' x , v : T ]" := (@Dpair _ (fun x => T) x v)
  (at level 0, x ident, v at level 99,
   format "[ 'dpair'  x , '/'  v  :  T ]") : form_scope.
Notation "[ 'dpair' x : A , v : T ]" := (@Dpair A (fun x => T) x v)
  (at level 0, x ident, v at level 99, only parsing) : form_scope.
Notation "[ 'dpair' := y , v ]" := (Dpair y v)
  (at level 0, only parsing) : form_scope.
Notation "[ 'pair' x , y ]" := (Pair x y)
  (at level 0, format "[ 'pair' '[hv'  x , '/'  y ] ']'") : form_scope.

Polymorphic Definition dfst@{i} {A T} : @dpair@{i} A T -> A :=
  fun '(Dpair x _) => x.
Notation "u .1d" := (dfst u) (at level 2, format "u .1d") : pair_scope.
Polymorphic Definition dsnd@{i} {A T} : forall u : @dpair@{i} A T, T u.1d :=
  fun '(Dpair _ y) => y.
Notation "u .2d" := (dsnd u) (at level 2, format "u .2d") : pair_scope.  
Polymorphic Definition ndsnd@{i} {S T : Type@{i}} : {pair S, T} -> T := dsnd.
Notation "u .2nd" := (ndsnd u) (at level 2, format "u .2nd") : pair_scope.  

Polymorphic Lemma dpair_eta@{i} S T u : u = @Dpair@{i} S T u.1d u.2d.
Proof. by case: u. Defined.

(******************************************************************************)
(*    The Context module provides support for a shallow embedding of Gallina  *)
(* contexts, allowing abstraction over (fully) dependent sequences of binders *)
(* as well as instantiation of such abstrations. It defines:                  *)
(*    context == type of sequences of dependent types                         *)
(*                  [ctx (X1 : A1) (X2 : A2) .... (Xn : An)]                  *)
(*               where X1 may appear in T2, ... and X1, ..., Xn-1 in Tn.      *)
(*               Null is the null context, and Abs A ctxA is the context      *)
(*               starting with (x : A), and continuing with ctxA x : context. *)
(* --> The %ctx scope is bound to type context, and open by default.          *)
(*  [ctx (X1 : A1) ... (Xn : An), C] := Notation for a context that begins    *)
(*               with (X1 : A1) .. (Xn : An) and continues with C (in which   *)
(*               X1 .. Xn may appear. The notation supports the usual binder  *)
(*               conventions: type can be omitted or grouped, and parentheses *)
(*               may be omitted when there is only a single constraint. Also, *)
(*               the ', C' part may be omitted when C is Null, so that        *)
(*               [ctx (X1 : A1) .. (Xn : An)] denotes a contex of length n.   *)
(*               Furthermore if n = 1 X1 may be omitted if it does not occur  *)
(*               in C, e.g., when C is Null, so [ctx: A] denotes a context of *)
(*               length 1.                                                    *)
(* --> Below we assume ctx : context is [ctx (X1 : A1) .. (Xn : An)], and     *)
(*     ctx2 : context is [ctx (Y1 : B1) .. (Ym : Bm)].                        *)
(*  telescope == a context >-> Sortclass coercion, interpreting a context as  *)
(*               the coresponding type of dependent value sequences, i.e.,    *)
(*               v : ctx means v : {dpair (X1 : A1) ... (Xn : An), unit}.     *)
(* --> The %tele scope is bound to telescope, but not open by defaut.         *)
(*  [tele x : A := y, v : ctx] == the telescope in [ctx x : A, ctx] that      *)
(*               consists of y followed by v (i.e., [dpair y, v]). The ': A'  *)
(*               type constraint may be omitted, ':= y' can be omitted if     *)
(*               y = x; alternatively x and both type constraints can be      *)
(*               can be omitted, and further v can also be omitted if ctx is  *)
(*               Null (and v is tt).                                          *)
(*  ctx /.v T == the type of dependent functions with arguments in ctx and    *)
(*               whose result type T may depend on a telescope v : ctx.       *)
(*            := forall (X1 : A1) .. (Xn : An),                               *)
(*                 let v := [tele X1 : A1, .. [tele:= Xn] ..] in T.           *)
(* --> ctx /.v T is notation for under (fun v : ctx => T).                    *)
(*    ctx / T := ctx /.v T where T does not depend on v.     n                *)
(*            := forall (X1 : A1) .. (Xn : An), T.                            *)
(*   A ->.x B := forall x, B (alternative notation).                          *)
(*     cf.[v] == apply cf : ctx /.v T to the contents of telescope v : ctx.   *)
(*            := let: Dpair y1 (Dpair y2 ...) := v return T in cf y1 ... yn   *)
(* --> cf.[v] is notation for subst cf v.                                     *)
(*   wType_subst cT v == WrapType cT.[v] with the computation interlocked so  *)
(*               the WrapType constructor is only exposed AFTER w2 has been   *)
(*               decomposed and passed to cT.                                 *)
(*      abs f == the function of type ctx /.v T derived from f : ctx ->.v T,  *)
(*               which maps X1 .. Xn to f [tele X1, .. [tele:= Xn] ..].       *)
(*   cf =* cg <-> functions cf, cg : ctx /.v T are extensionally equal.       *)
(*            := forall X1 .. Xn, cf X1 .. Xn = cg X1 .. Xn.                  *)
(*  ctx :+ cT == extend ctx on the right with cT : ctx / Type.                *)
(*            := [ctx (X1 : A1) .... (Xn : An) (Xn+1: cT X1 ... Xn)].         *)
(* (v :+ z)%tele == the ctx :+ cT telescope (for cT : ctx / Type) obtained by *)
(*                 extending telescope v : ctx with z : cT.[v].               *)
(* split_extend vz == the decomposition of vz : ctx :+ cT into a dependent    *)
(*              telescope-value pair of type {dpair v : ctx, cT.[v]}.         *)
(*  ctx ++ ctx2 == sum (non-dependent concatenation) of ctx, ctx2 : context.  *)
(*              := [ctx (X1 : A1) ... (Xn : An) (Y1 : B1) .. (Ym : Bm)].      *)
(* --> ctx ++ ctx2 is notation for sum ctx ctx2.                              *)
(* (v ++ w)%tele == the ctx ++ ctx2 telescope obtained by concatenating       *)
(*                v : ctx and w : ctx'.                                       *)
(* split_sum vw == the decomposition of vw : ctx ++ ctx2 into a pair of       *)
(*               telescopes of type {pair ctx, ctx2}.                         *)
(* split_sum_under cvw == decomposition of cvw : ctx / (ctx1 ++ ctx2) into    *)
(*               a pair of functions of type {pair ctx / ctx1, ctx / ctx2}.   *)
(*   map g cf == the ctx / T function obtained by composing g : S -> T with   *)
(*               cf : ctx / S, and which maps X1 .. Xn to g (cf X1 ... Xn).   *)
(* map2 h cf cg == the ctx / R function obtained by composing f : S -> T -> R *)
(*               with both cf : ctx / S and cg : ctx / T, which thus maps     *)
(*               X1..Xn to h (cf X1..Xn) (cg X1..Xn).                         *)
(*  dmap g cf == the (ctx :+ map S w) / R function obtained by composing      *)
(*               the dependent function g : S ->.x T x -> R with cf : ctx / S *)
(*               and which maps X1 .. Xn (Xn+1 : T (cf X1..Xn)) to            *)
(*               f (cf X1..Xn) Xn+1.                                          *)
(*  map_sum h cf cg == a (ctx + ctx') / R function obtained by composing      *)
(*               h : S -> T -> R with cf : ctx / S and cg : ctx' / T, and     *)
(*               which maps X1..Xn Y1..Ym to h (cf X1..Xn) (cg Y1..Yn).       *)
(* Because some uses of Context involve self-application, all the contents of *)
(* this module is universe polymorphic.                                       *)
(******************************************************************************)

Module Context.

Set Universe Polymorphism.
Set Printing Universes.

Inductive context@{i} : Type@{i+1} := Null | Abs (A : Type@{i}) of A -> context.
Arguments Abs A ctxA : clear implicits.

Fixpoint telescope@{i} (ctx : context@{i}) : Type@{i} :=
  if ctx is Abs A ctxA then dpair@{i} (fun x => telescope (ctxA x)) else unit.
Coercion telescope : context >-> Sortclass.

Declare Scope context_scope.
Declare Scope telescope_scope.

Bind Scope context_scope with context.
Bind Scope telescope_scope with telescope.

Delimit Scope context_scope with ctx.
Delimit Scope telescope_scope with tele.

Local Open Scope context_scope.

Notation "[ 'ctx' x .. z , C ]" :=
   (Abs _ (fun x => .. (Abs _ (fun z => C)) .. ))
   (at level 0, x binder, z binder,
    format "[ 'ctx'  x  ..  z ,  C ]") : form_scope. 
Notation "[ 'ctx' x .. z ]" :=
   (Abs _ (fun x => .. (Abs _ (fun z => Null)) .. ))
   (at level 0, x binder, z binder,
    format "[ 'ctx'  x  ..  z ]") : form_scope. 
Notation "[ 'ctx' : A , C ]" := (Abs A (fun=> C))
   (at level 0, format "[ 'ctx' :  A ,  C ]") : form_scope. 
Notation "[ 'ctx' : A ]" := [ctx: A , Null]
  (at level 0, format "[ 'ctx' :  A  ]") : form_scope.

Definition TelePair@{i} A ctxA y v : Abs@{i} A ctxA := @Dpair A ctxA y v.
Notation "[ 'tele' x := y , v : ctx ]" := (@TelePair _ (fun x => ctx) y v)
  (at level 0, x ident, v at level 99,
   format "[ 'tele' '[hv'  x  :=  y , '/'  v  :  ctx ] ']'") : form_scope.
Notation "[ 'tele' x , v : ctx ]" := (@TelePair _ (fun x => ctx) x v)
  (at level 0, x ident, v at level 99,
   format "[ 'tele'  x ,  v  :  ctx ]") : form_scope.
Notation "[ 'tele' := y , v ]" := (@TelePair _ _ y v)
  (at level 0, only parsing) : form_scope.
Notation "[ 'tele' := y ]" := (@TelePair _ (fun=> Null) y tt)
  (at level 0, format "[ 'tele' :=  y ]") : form_scope.

Reserved Notation "ctx /. v T"
  (at level 40, v ident, T at next level, format "ctx  /. v  T").
Reserved Notation "ctx ++. v T"
  (at level 60, v ident, T at next level, format "ctx  ++. v  T").
(*Notation "A ->. x T" := (forall x : A, T)
  (at level 99, x ident, T at level 200, right associativity, only parsing). *)
Reserved Notation "cf =* cg" (at level 70).
Reserved Notation "s :+ x" (at level 60).

Implicit Type ctx : context.

(* Operator definitions. *)

Fixpoint under@{i j} {ctx : context@{j}} : (ctx -> Type@{i}) -> Type@{i} :=
  if ctx isn't Abs A ctxA then @^~ tt else
  fun T => forall x, ctxA x /.v T [tele:= x, v]
where "ctx /. v T" := (@under ctx (fun v => T)) : context_scope.
Notation "ctx / T" := (ctx /._ T) : context_scope.

Fixpoint eq_under@{i j} {ctx} : forall {T} (cT1 cT2 : @under@{i j} ctx T), Prop :=
  if ctx isn't Abs A ctxA then fun=> eq else
  fun T cT1 cT2 => forall x : A, cT1 x =* cT2 x
where "c1 =* c2" := (eq_under c1 c2) : type_scope.

Fixpoint subst@{i j} {ctx} : forall {T}, @under@{i j} ctx T -> forall v, T v :=
  if ctx isn't Abs A ctxA then fun T y 'tt => y else
  fun T cf '(Dpair x v) => (cf x).[v]
where "cf .[ v ]" := (subst cf v) : context_scope.

Fixpoint abs@{i j} {ctx : context@{j}} :
    forall {T : ctx -> Type@{i}}, (forall v, T v) -> @under@{i j} ctx T :=
  if ctx isn't Abs A ctxA then fun T : unit -> Type@{i} => @^~ tt else
  fun T f x => abs (fun v => f [tele:= x, v]).

Fixpoint wType_subst@{i j} {ctx : context@{j}} :
    @under@{i j} ctx (fun=> Type@{j}) -> ctx -> wrappedType :=
  if ctx isn't Abs A ctxA then fun T _ => WrapType T else
  fun cT '(Dpair x v) => wType_subst (cT x) v.

Fixpoint join@{i} {ctx : context@{i}} : (ctx -> context@{i}) -> context@{i} :=
  if ctx isn't Abs A ctxA then @^~ tt else
  fun K => [ctx x, ctxA x ++.v K [tele:= x, v]]
where "ctx ++. v ctx2" := (@join ctx (fun v => ctx2)) : context_scope.
Notation "ctx ++ ctx2" := (@join ctx (fun=> ctx2)) : context_scope.

Definition extend@{i} ctx (cT : ctx -> Type@{i}) := ctx ++.v [ctx: cT v].
Notation "ctx :+ cT" := (@extend ctx cT) : context_scope.

Fixpoint join_tele@{i} {ctx} :
    forall {K : ctx -> context} v, K v -> join@{i} K :=
  if ctx isn't Abs A ctxA then fun K 'tt w => w else
  fun K '(Dpair x v) w => [tele:= x, v ++ w]
where "v ++ w" := (@join_tele _ _ v w) : telescope_scope.

Fixpoint split_join@{i} {ctx} : forall {K}, ctx ++.v K v -> {dpair v, K v} :=
  if ctx isn't Abs A ctxA then (@Dpair Null@{i})^~ tt else fun K '(Dpair x u) =>
  let: Dpair v w := split_join u in [dpair:= [tele:= x, v], w].

Definition split_extend@{i} {ctx cT} (u : ctx :+ cT) : {dpair v, cT v} :=
  let: Dpair v w := split_join@{i} u in [dpair:= v, w.1d].

Lemma join_teleK@{i} ctx K v w :
   @split_join@{i} ctx K (v ++ w) = [dpair:= v, w].
Proof. by elim: ctx v => [|A ctxA IH] [] //= x v in K w *; rewrite IH. Defined.

Definition extend_tele@{i} {ctx cT} v z : ctx :+ cT :=
  @join_tele@{i} ctx _ v [tele:= z].
Notation "v :+ z" := (@extend_tele _ _ v z) : telescope_scope.

Lemma extend_teleK@{i} ctx cT v z :
  split_extend@{i} (v :+ z) = [dpair v : ctx, z : cT v].
Proof. by rewrite /split_extend join_teleK. Defined.

Variant depth := FullDepth | PartialDepth of nat.
Definition as_deep h k :=
  if k isn't PartialDepth k1 then true else
  if h isn't PartialDepth h1 then false else h1 <= k1.
Notation "h <= k" := (as_deep h k) : telescope_scope.

Fixpoint trunc_rec@{i} (ctx : context@{i}) h1 : context@{i} :=
  if ctx isn't Abs A ctxA then Null else if h1 isn't h.+1 then Null else
  [ctx x, trunc_rec (ctxA x) h].
Definition truncate@{i} ctx h :=
  if h is PartialDepth h1 then trunc_rec@{i} ctx h1 else ctx.
Notation "ctx `_ h" := (truncate ctx h) : context_scope.

Fixpoint trunc_tele_rec@{i} {ctx : context} h1 : ctx -> trunc_rec@{i} ctx h1 :=
  if ctx isn't Abs A ctxA then fun=>tt else if h1 isn't h.+1 then fun=> tt else
  fun v => [tele:= v.1d, @trunc_tele_rec (ctxA _) h v.2d].
Definition truncate_tele@{i} {ctx : context@{i}} (v : ctx) h : ctx`_h :=
  if h is PartialDepth h1 then trunc_tele_rec h1 v else v.
Notation "v `_ n" := (truncate_tele v n) : telescope_scope.

Fixpoint truncC_rec@{i} {ctx h1 k1} :
   trunc_rec@{i} (trunc_rec ctx h1) k1 -> trunc_rec (trunc_rec ctx k1) h1 :=
  if ctx isn't Abs A ctxA then id else
  if k1 isn't k.+1 then fun=> tt else if h1 isn't h.+1 then id else
  fun v => [tele:= v.1d, @truncC_rec (ctxA _) h k v.2d].
Definition truncC@{i} {ctx h k} : ctx`_h`_k -> ctx`_k`_h :=
  if k isn't PartialDepth k1 then id else if h isn't PartialDepth h1 then id else
  truncC_rec@{i}.

Lemma truncCK@{i} {ctx h k} : cancel (@truncC@{i} ctx h k) truncC.
Proof.
case: h k => [|h] [|k] //=; elim: ctx h k => // A ctxA IH [|h] [|k] /= [] // x v.
by rewrite IH.
Qed.

Fixpoint truncV_rec@{i} {ctx h1} : trunc_rec@{i} ctx h1 -> option ctx :=
  if ctx isn't Abs A ctxA then Some else
  if h1 isn't h.+1 then fun=> None else fun v =>
  omap (Dpair v.1d) (@truncV_rec (ctxA _) h v.2d).
Definition truncV@{i} {ctx h} : ctx`_h -> option ctx :=
  if h is PartialDepth h1 then @truncV_rec@{i} ctx h1 else Some.

Notation "h >= v" := (isSome (truncV v`_h)) : telescope_scope.

Lemma truncKV@{i} ctx h : ocancel (fun v => @truncV@{i} ctx h (v`_h)) id.
Proof.
case: h => //=; elim: ctx => [_ []|] //= A ctx IH [|h] [x v] //=.
by case: truncV_rec (IH x h v) => //= _ ->.
Qed.

Lemma truncVK@{i} ctx h : ocancel (@truncV@{i} ctx h) (fun v => v`_h)%tele.
Proof.
case: h => //=; elim: ctx => [_ []|] //= A ctx IH [|h] // [x v] /=.
by case: truncV_rec (IH x h v) => //= _ ->.
Qed.


Fact truncE_P@{i} ctx h k (v : ctx`_h`_k) : (h <= k)%tele -> truncV@{i} v.
Proof.
case: h k v => [|h] [] //=; elim: ctx h => //= A ctx IH [|h] [|k] //= [x v] lehk.
by rewrite isSome_map IH.
Qed.

Definition truncE@{i} {h k ctx} (lehk : (h <= k)%tele) (v : ctx`_h`_k) : ctx`_h :=
  (if truncV v is Some w as ow return ow -> _ then fun=> w else
   fun ff => match notF ff with end) (truncE_P@{i} v lehk).

Definition truncW@{i} {h k ctx} (lekh : (k <= h)%tele) (v : ctx`_h) : ctx`_k :=
  truncE@{i} lekh (truncC v`_k).

Lemma truncE_K@{i} h k ctx (lehk : (h <= k)%tele) :
  cancel (@truncE@{i} h k ctx lehk) (fun v => v`_k)%tele.
Proof. by rewrite /truncE => v; case: truncV (truncVK v) (truncE_P _ _). Qed.

Lemma truncK@{i} h k ctx (lehk : (h <= k)%tele) :
  cancel (fun v : ctx`_h => (v`_k)%tele) (@truncE@{i} h k ctx lehk). 
Proof. by rewrite /truncE => v; case: truncV (truncE_P _ _) (truncKV k v). Qed.

Definition Xtrunc@{i} h (ctx : context@{i}) (cT : ctx -> Type@{i}) :
  ctx`_h -> ctx + (ctx :+ cT)`_h.
Proof.
case: h => /=; first by left.
do [fix IH 1] in ctx cT *; case: ctx => [|A ctxA] /= in cT *; first by left.
case=> [|h /= [x]]; first by right.
by case/(IH _ (fun v => cT [tele:= x, v])); [left | right]; exists x.
Defined.

Definition truncX@{i} h (ctx : context@{i}) (cT : ctx -> Type@{i}) :
  (ctx :+ cT)`_h -> ctx`_h.
Proof.
case: h ctx cT => [_ _ /split_extend[]|] //=; fix IHh 1 => -[|h] [|A ctxA] //= cT.
case=> x /IHh; apply: Dpair x.
Defined.

Lemma truncX_tele@{i} h ctx cT v z : @truncX@{i} h ctx cT (v :+ z)`_h = (v`_h)%tele.
Proof.
case: h ctx cT v z => [*|] /=; first by rewrite extend_teleK.
by elim=> [|h IHh] /= [|A ctxA] //= cT [x v] z; rewrite IHh -/trunc_rec. 
Qed.

Lemma Xtrunc_eqV@{i} h (ctx : context@{i}) (cT : ctx -> Type@{i}) (v : ctx`_h) :
  truncV v = Xtrunc cT v :> bool.
Proof.
case: h ctx cT v => //=; elim=> [|h IHh] [|A ctxA] //= cT [x v] /=.
by set cTx := fun u => cT _; rewrite isSome_map (IHh _ cTx); case: (_ v).
Qed.

Record map@{i} (ctx1 ctx2 : context@{i}) := {
  apply {h} : ctx1`_h -> ctx2`_h;
  mapW {h k} v lekh : apply (@truncW h k ctx1 lekh v) = truncW lekh (apply v);
  mapV {h} v : truncV (@apply h v) = truncV v :> bool
}.
Coercion apply : map >-> Funclass.

Lemma map_truncV@{i} h ctx1 ctx2 (f : map@{i} ctx1 ctx2) v :
  truncV (f h v) = truncV v :> bool.
Proof.
case: h v => //= h.
  f (truncW (leqnn h) v) = truncW (leqnn h) (f h v).
have: h < ctx1.
have: ctx2 <= h.

|f h v|   
Some (witis inl w then 
 [x v]; exists x.
 => //.


rewrite (ocancel_id (truncE_P _ _)). Qed.
Lemma truncK@{i} h ctx (lehk : (h <= k)%tele) (v : ctx`_h) :
  
(*
Definition map@{i} {S T : Type@{i}} {ctx} g (cf : ctx / S) : ctx / T :=
  abs (fun v => g cf.[v]).

Definition map2@{i} {S T R : Type@{i}} {ctx} h (cf : ctx / S) (cg : ctx / T) :=
  abs (fun v => h cf.[v] cg.[v]) : ctx / R.

Definition dmap@{i} {S : Type@{i}} {T : S -> Type@{i}} {R : Type@{i}} {ctx}
           (g : forall x, T x -> R) (cf : ctx / S) :=
  let cg vz := let: Dpair v z := split_extend vz in g cf.[v] z in
  abs cg : (ctx :+ (fun v => T cf.[v])) / R.

Definition map_sum@{i} {S T R : Type@{i}} {ctx ctx2 : context@{i}}
      (h : S -> T -> R) (cf : ctx / S) (cg : ctx2 / T) : (ctx ++ ctx2) / R :=
  let ch uv := let: Dpair u v := split_join uv in h cf.[u] cg.[v] in abs ch.
*)
(* Basic identities; most are transparent as they may be used for dependent   *)
(* type transport, e.g., in subst_dmap below.                                 *)

Lemma subst_abs@{i} ctx (T : ctx -> Type@{i}) (h : forall v, T v) v :
  (abs@{i} h).[v] = h v.
Proof. by elim: ctx v => [|A ctxA IH] /= [] // x v in T h *; apply: IH. Defined.

Lemma congr_subst@{i} (ctx : context@{i}) (T : ctx -> Type@{i}) :
  forall (cT1 cT2 : ctx /.v T v) v, cT1 =* cT2 -> cT1.[v] = cT2.[v].
Proof. by elim: ctx T => [|A ctxA IH] T cT1 cT2 [] //= *; apply/IH. Defined.

Lemma abs_subst@{i} ctx (T : ctx -> Type@{i}) (cT : ctx /.v T v) :
  abs@{i} (fun v => cT.[v]) =* cT.
Proof. by elim: ctx T cT => /=. Defined.
(*
Lemma subst_map@{i} {S T : Type@{i}} {ctx} (g : S -> T) (cf : ctx / S) v :
  (map@{i} g cf).[v] = g cf.[v].
Proof. exact: subst_abs. Defined.

Lemma subst_map2@{i} {S T R : Type@{i}} {ctx}
                     (h : S -> T -> R) (cf : ctx / S) (cg : ctx / T) v :
  (map2@{i} h cf cg).[v] = h cf.[v] cg.[v].
Proof. exact: subst_abs. Defined.

Lemma subst_dmap@{i} {S : Type@{i}} {T : S -> Type@{i}} {R : Type@{i}} {ctx}
                       (g : forall x : S, T x -> R) (cf : ctx / S) v z :
  (dmap@{i} g cf).[v :+ z] = g cf.[v] z.
Proof. by rewrite subst_abs extend_teleK. Defined.

Lemma subst_sum@{i} {S T R : Type@{i}} {ctx ctx2}
                    (h : S -> T -> R) (cf : ctx / S) (cg : ctx2 / T) v w :
  (map_sum@{i} h cf cg).[v ++ w] = h cf.[v] cg.[w].
Proof. by rewrite subst_abs join_teleK. Defined.
*)

Lemma unwrap_subst@{i j} {ctx : context@{i}} (cT : ctx / Type@{j}) v :
  wType_subst cT v = WrapType cT.[v].
Proof. by elim: ctx v cT => [|A ctxA IH] [] //=. Qed. 

End Context.

(*
(******************************************************************************)
(*    The Context module provides support for a shallow embedding of Gallina  *)
(* contexts, allowing abstraction over (fully) dependent sequences of binders *)
(* as well as instantiation of such abstrations. It defines:                  *)
(*    context == type of sequences of dependent types                         *)
(*                  [ctx (X1 : A1) (X2 : A2) .... (Xn : An)]                  *)
(*               where X1 may appear in T2, ... and X1, ..., Xn-1 in Tn.      *)
(*               Null is the null context, and Abs A ctxA is the context      *)
(*               starting with (x : A), and continuing with ctxA x : context. *)
(* --> The %ctx scope is bound to type context, and open by default.          *)
(*  [ctx (X1 : A1) ... (Xn : An), C] := Notation for a context that begins    *)
(*               with (X1 : A1) .. (Xn : An) and continues with C (in which   *)
(*               X1 .. Xn may appear. The notation supports the usual binder  *)
(*               conventions: type can be omitted or grouped, and parentheses *)
(*               may be omitted when there is only a single constraint. Also, *)
(*               the ', C' part may be omitted when C is Null, so that        *)
(*               [ctx (X1 : A1) .. (Xn : An)] denotes a contex of length n.   *)
(*               Furthermore if n = 1 X1 may be omitted if it does not occur  *)
(*               in C, e.g., when C is Null, so [ctx: A] denotes a context of *)
(*               length 1.                                                    *)
(* --> Below we assume ctx : context is [ctx (X1 : A1) .. (Xn : An)], and     *)
(*     ctx2 : context is [ctx (Y1 : B1) .. (Ym : Bm)].                        *)
(*  telescope == a context >-> Sortclass coercion, interpreting a context as  *)
(*               the coresponding type of dependent value sequences, i.e.,    *)
(*               v : ctx means v : {dpair (X1 : A1) ... (Xn : An), unit}.     *)
(* --> The %tele scope is bound to telescope, but not open by defaut.         *)
(*  [tele x : A := y, v : ctx] == the telescope in [ctx x : A, ctx] that      *)
(*               consists of y followed by v (i.e., [dpair y, v]). The ': A'  *)
(*               type constraint may be omitted, ':= y' can be omitted if     *)
(*               y = x; alternatively x and both type constraints can be      *)
(*               can be omitted, and further v can also be omitted if ctx is  *)
(*               Null (and v is tt).                                          *)
(*  ctx /.v T == the type of dependent functions with arguments in ctx and    *)
(*               whose result type T may depend on a telescope v : ctx.       *)
(*            := forall (X1 : A1) .. (Xn : An),                               *)
(*                 let v := [tele X1 : A1, .. [tele:= Xn] ..] in T.           *)
(* --> ctx /.v T is notation for under (fun v : ctx => T).                    *)
(*    ctx / T := ctx /.v T where T does not depend on v.     n                *)
(*            := forall (X1 : A1) .. (Xn : An), T.                            *)
(*   A ->.x B := forall x, B (alternative notation).                          *)
(*     cf.[v] == apply cf : ctx /.v T to the contents of telescope v : ctx.   *)
(*            := let: Dpair y1 (Dpair y2 ...) := v return T in cf y1 ... yn   *)
(* --> cf.[v] is notation for subst cf v.                                     *)
(*   wType_subst cT v == WrapType cT.[v] with the computation interlocked so  *)
(*               the WrapType constructor is only exposed AFTER w2 has been   *)
(*               decomposed and passed to cT.                                 *)
(*      abs f == the function of type ctx /.v T derived from f : ctx ->.v T,  *)
(*               which maps X1 .. Xn to f [tele X1, .. [tele:= Xn] ..].       *)
(*   cf =* cg <-> functions cf, cg : ctx /.v T are extensionally equal.       *)
(*            := forall X1 .. Xn, cf X1 .. Xn = cg X1 .. Xn.                  *)
(*  ctx :+ cT == extend ctx on the right with cT : ctx / Type.                *)
(*            := [ctx (X1 : A1) .... (Xn : An) (Xn+1: cT X1 ... Xn)].         *)
(* (v :+ z)%tele == the ctx :+ cT telescope (for cT : ctx / Type) obtained by *)
(*                 extending telescope v : ctx with z : cT.[v].               *)
(* split_extend vz == the decomposition of vz : ctx :+ cT into a dependent    *)
(*              telescope-value pair of type {dpair v : ctx, cT.[v]}.         *)
(*  ctx ++ ctx2 == sum (non-dependent concatenation) of ctx, ctx2 : context.  *)
(*              := [ctx (X1 : A1) ... (Xn : An) (Y1 : B1) .. (Ym : Bm)].      *)
(* --> ctx ++ ctx2 is notation for sum ctx ctx2.                              *)
(* (v ++ w)%tele == the ctx ++ ctx2 telescope obtained by concatenating       *)
(*                v : ctx and w : ctx'.                                       *)
(* split_sum vw == the decomposition of vw : ctx ++ ctx2 into a pair of       *)
(*               telescopes of type {pair ctx, ctx2}.                         *)
(* split_sum_under cvw == decomposition of cvw : ctx / (ctx1 ++ ctx2) into    *)
(*               a pair of functions of type {pair ctx / ctx1, ctx / ctx2}.   *)
(*   map g cf == the ctx / T function obtained by composing g : S -> T with   *)
(*               cf : ctx / S, and which maps X1 .. Xn to g (cf X1 ... Xn).   *)
(* map2 h cf cg == the ctx / R function obtained by composing f : S -> T -> R *)
(*               with both cf : ctx / S and cg : ctx / T, which thus maps     *)
(*               X1..Xn to h (cf X1..Xn) (cg X1..Xn).                         *)
(*  dmap g cf == the (ctx :+ map S w) / R function obtained by composing      *)
(*               the dependent function g : S ->.x T x -> R with cf : ctx / S *)
(*               and which maps X1 .. Xn (Xn+1 : T (cf X1..Xn)) to            *)
(*               f (cf X1..Xn) Xn+1.                                          *)
(*  map_sum h cf cg == a (ctx + ctx') / R function obtained by composing      *)
(*               h : S -> T -> R with cf : ctx / S and cg : ctx' / T, and     *)
(*               which maps X1..Xn Y1..Ym to h (cf X1..Xn) (cg Y1..Yn).       *)
(* Because some uses of Context involve self-application, all the contents of *)
(* this module is universe polymorphic.                                       *)
(******************************************************************************)

Module Context.

Set Universe Polymorphism.

Fixpoint context@{i j} n : Type@{i} :=
  if n is m.+1 then {dpair A : Type@{j}, A -> context m} else unit.
Definition Null@{i j} : context@{i j} 0 := tt.
Definition Abs@{i j} {n A} ctxA : context n.+1 :=
  @Dpair@{i} Type@{j} (fun A => A -> context n) A ctxA.

Fixpoint telescope@{i j} {n} : context@{i j} n -> Type@{j} :=
  if n isn't m.+1 then fun=> unit else
  fun '(Dpair A ctxA) => {dpair x : A, telescope (ctxA x)}.
Coercion telescope : context >-> Sortclass.

Declare Scope context_scope.
Declare Scope tele_scope.

Bind Scope context_scope with context.
Bind Scope telescope_scope with telescope.

Delimit Scope context_scope with ctx.
Delimit Scope telescope_scope with tele.

Local Open Scope context_scope.

Notation "[ 'ctx' x .. z , C ]" :=
   (Abs (fun x => .. (Abs (fun z => C)) .. ))
   (at level 0, x binder, z binder,
    format "[ 'ctx'  x  ..  z ,  C ]") : form_scope. 
Notation "[ 'ctx' x .. z ]" :=
   (Abs (fun x => .. (Abs (fun z => Null)) .. ))
   (at level 0, x binder, z binder,
    format "[ 'ctx'  x  ..  z ]") : form_scope. 
Notation "[ 'ctx' : A , C ]" := (Abs (fun _ : A => C))
   (at level 0, format "[ 'ctx' :  A ,  C ]") : form_scope. 
Notation "[ 'ctx' : A ]" := [ctx: A , Null]
  (at level 0, format "[ 'ctx' :  A  ]") : form_scope.

Notation Tele x ctx := (@Dpair _ (fun x => telescope ctx)) (only parsing).
Notation "[ 'tele' x := y , v : ctx ]" := (Tele x ctx y v%tele)
  (at level 0, x ident, v at level 99,
   format "[ 'tele' '[hv'  x  :=  y , '/'  v  :  ctx ] ']'") : form_scope.
Notation "[ 'tele' x , v : ctx ]" := (Tele x ctx x v%tele)
  (at level 0, x ident, v at level 99,
   format "[ 'tele'  x ,  v  :  ctx ]") : form_scope.
Notation "[ 'tele' := y , v ]" := (Tele x _ y v%tele)
  (at level 0, only parsing) : form_scope.
Notation "[ 'tele' := y ]" := (Tele _ Null y tt)
  (at level 0, format "[ 'tele' :=  y ]") : form_scope.

Reserved Notation "ctx /. v T"
  (at level 40, v ident, T at next level, format "ctx  /. v  T").
Reserved Notation "ctx ++. v T"
  (at level 60, v ident, T at next level, format "ctx  ++. v  T").
(*
Notation "A ->. x T" := (forall x : A, T)
  (at level 99, x ident, T at level 200, right associativity, only parsing).
*)
Reserved Notation "cf =* cg" (at level 70).
Reserved Notation "s :+ x" (at level 60).

(* Operator definitions. *)

Fixpoint under@{i j k} {n} :
    forall {ctx}, (@telescope@{i j} n ctx -> Type@{k}) -> Type@{k} :=
  if n isn't m.+1 then fun=> @^~ tt else
  fun '(Dpair A ctx) T => forall x : A, ctx x /.v T [tele:= x, v]
where "ctx /. v T" := (@under _ ctx (fun v => T)) : context_scope.
Notation "ctx / T" := (ctx /._ T) : context_scope.

Fixpoint eq_under@{i j k} {n} :
    forall {ctx T}, @under@{i j k} n ctx T -> ctx /.v T v -> Prop :=
  if n isn't m.+1 then fun _ _ cf cg => cf = cg else
  fun '(Dpair A ctxA) T cf cg => forall x : A, cf x =* cg x
where "c1 =* c2" := (eq_under c1 c2) : type_scope.

Fixpoint subst@{i j k} {n} :
    forall {ctx T}, @under@{i j k} n ctx T -> forall v, T v :=
  if n isn't m.+1 then fun _ T y 'tt => y else
  fun '(Dpair A ctxA) T cf '(Dpair x v) => (cf x).[v]
where "cf .[ v ]" := (subst cf v) : context_scope.

Fixpoint abs@{i j k} {n} :
    forall {ctx} {T : _ -> Type@{k}},
       (forall v, T v) -> @under@{i j k} n ctx T :=
  if n isn't m.+1 then fun _ T => @^~ tt else
  fun '(Dpair A ctxA) T f x => abs (fun v => f [tele:= x, v]).

Lemma subst_abs@{i j k} n ctx T h v : (@abs@{i j k} n ctx T h).[v] = h v.
Proof.
by elim: n ctx v => [_ []|n IHn] //= [A ctxA] [x v] in T h *; apply: IHn.
Defined.

Lemma subst_eq@{i j k} n ctx T (cf cg : @under@{i j k} n ctx T) :
   cf =* cg -> forall v, cf.[v] = cg.[v].
Proof.
elim: n ctx => /= [[] | n IHn [A ctx]] in T cf cg * => eq_fg [] //= x v.
exact: IHn.
Defined.

Lemma abs_subst@{i j k} n ctx T cf : @abs@{i j k} n ctx T (subst cf) =* cf.
Proof. by elim: n ctx T cf => //= n IHn [] /=. Defined.

Fixpoint wType_subst@{i j k} {n} :
    forall {ctx}, @under@{i j k} n ctx (fun=> Type@{j}) -> ctx -> wrappedType :=
  if n isn't m.+1 then fun _ T _ => WrapType T else
  fun '(Dpair A ctxA) cT '(Dpair x v) => wType_subst (cT x) v.

Lemma unwrap_subst@{i j k} n ctx cT v :
  @wType_subst@{i j k} n ctx cT v = WrapType cT.[v].
Proof. by elim: n ctx v cT => [_|n IHn [A ctxA]] [] /=. Qed. 

Fixpoint join@{i j} m n :
    forall {ctx}, (@telescope@{i j} m ctx -> context n) -> context (m + n) :=
  if m is 0 then fun=> @^~ tt else
  fun '(Dpair A ctx) Kctx => [ctx x, ctx x ++.v Kctx [tele:= x, v]]
where
  "ctx1 ++. v ctx2" := (join (fun v : telescope ctx1 => ctx2)) : context_scope.
Notation "ctx1 ++ ctx2" := (join (fun _ : ctx1 => ctx2)) : context_scope.

Fixpoint join_tele@{i j} {m n} :
    forall {ctx Kctx v}, telescope (Kctx v) -> @join@{i j} m n ctx Kctx :=
  if m is 0 then fun _ _ 'tt w => w else
  fun '(Dpair A ctxA) ctx_n '(Dpair x v) w => [tele:= x, v ++ w]
where "v ++ w" := (@join_tele _ _ _ _ v w) : telescope_scope.

Definition extend@{i j} {n} (ctx : context@{i j} n) (cT : ctx -> Type@{j}) :=
  ctx ++.v [ctx: cT v] : context (n + 1).
Notation "ctx :+ cT" := (@extend _ ctx cT) : context_scope.

Definition extend_tele@{i j} {n ctx cT} v z : ctx :+ cT :=
  @join_tele@{i j} n 1 ctx (fun v => [ctx: cT v]) v [pair z, tt].
Notation "v :+ z" := (@extend_tele _ _ _ v z) : telescope_scope.

Fixpoint split_join@{i j} m n :
     forall ctx Kctx, @join@{i j} m n ctx Kctx -> dpair@{j} Kctx :=
  if m is 0 then fun _ _ w => [dpair:= tt, w] else
  fun '(Dpair A ctxA) ctx_n '(Dpair x v) =>
  let: Dpair v w := split_join v in [dpair:= [tele:= x, v], w].

Lemma join_teleK@{i j} m n ctx Kctx v w :
  @split_join@{i j} m n ctx Kctx (v ++ w) = [dpair v, w : Kctx v].
Proof.
by elim: m ctx v => /= [_|m IHm [A ctxA]] [] //= x v in Kctx w *; rewrite IHm.
Defined.

Definition split_extend@{i j} n ctx cT (vz : @extend n ctx cT) :=
  let: Dpair v (Dpair z _) := split_join@{i j} vz in [dpair v, z : cT v].

Lemma extend_teleK@{i j} n ctx (cT : _ -> Type@{j}) v z :
  @split_extend@{i j} n ctx cT (v :+ z) = [dpair v, z : cT v].
Proof. by rewrite /split_extend join_teleK. Qed.

Lemma split_joinK@{i j} m n ctx Kctx uv :
  (let (u, v) := @split_join@{i j} m n ctx Kctx uv in u ++ v)%tele = uv.
Proof.
elim: m ctx Kctx uv => [|m IHm] //= [A ctx] Kctx [x uv] /=.
by rewrite -[uv in RHS]IHm; case: split_join.
Defined.

Lemma split_extendK@{i j} n ctx cT vz :
  (let (v, z) := @split_extend@{i j} n ctx cT vz in v :+ z)%tele = vz.
Proof.
by rewrite -[RHS]split_joinK /split_extend; case: split_join=> v [z []] /=.
Defined.

Fixpoint truncate@{i j} {n} (ctx : context@{i j} n) m : context@{i j} m :=
  if m isn't m.+1 then Null else
  (if n is 0 return context n -> _ then fun ctx => [ctx: unit, ctx`_m] else
   fun '(Dpair A ctx) => [ctx x, (ctx x)`_m]) ctx
where "ctx `_ m" := (truncate ctx m) : context_scope.

Definition chop@{i j} {n} ctx k := @truncate@{i j} n ctx (n - k).
Notation "ctx :\ k" := (chop ctx k).

Definition cast_chop@{i j} {n k1 k2 ctx} (Ek : k1 = k2) v := 
  ecast m (@chop@{i j} n ctx m) (nat_cast Ek) v.

Lemma cast_chopK@{i j} n k1 k2 ctx (Ek : k1 = k2) :
  cancel (@cast_chop@{i j} n k1 k2 ctx Ek) (cast_chop (esym Ek)).
Proof.
by rewrite /cast_chop; case: _ / (nat_cast Ek) (esym _) => E; rewrite nat_castK.
Defined.

Lemma cast_chopKV@{i j} n k1 k2 ctx (Ek : k1 = k2) :
  cancel (cast_chop (esym Ek)) (@cast_chop@{i j} n k1 k2 ctx Ek).
Proof.
by rewrite /cast_chop; case: _ / (nat_cast Ek) (esym _) => E; rewrite nat_castK.
Defined.

Fixpoint truncate_tele@{i j} {n} {ctx : context@{i j} n} (v : ctx) m : ctx`_m :=
  if m isn't m.+1 then tt else
  (if n is 0 return forall ctx : context n, ctx -> (ctx`_m.+1)%ctx then
     fun ctx v => [tele:= tt, v`_m]
   else fun '(Dpair A ctx) '(Dpair x v) => [tele:= x, v`_m]) ctx v
where "v `_ m" := (truncate_tele v m) : telescope_scope.

Definition chop_tele@{i j} {n ctx} (v : @telescope@{i j} n ctx) k :=
  (v`_(n - k))%tele : ctx :\ k.
Notation "v :\ k" := (chop_tele v k) : telescope_scope.

Fixpoint no_trunc@{i j} {n} : forall {ctx : context@{i j} n}, ctx`_n -> ctx :=
  if n isn't n1.+1 then fun=> id else
  fun '(Dpair A ctx) '(Dpair x v) => [tele:= x, no_trunc v].
Definition chop0@{i j} n : forall ctx : context@{i j} n, ctx :\ 0 -> ctx :=
  if n is 0 then @no_trunc 0 else @no_trunc _.

Lemma chopK@{i j} n ctx v : @chop0@{i j} n ctx (v :\ 0) = v.
Proof.
rewrite /chop0 /chop /chop_tele; case: n ctx v => [[] [] //| n1].
set n := n1.+1; rewrite -[n - 0]/n.
by elim: {n1}n => [_ [] | n IHn] //= [A ctx] /= [x v]; rewrite IHn.
Defined.

Lemma chop0K@{i j} n ctx v : (@chop0@{i j} n ctx v :\ 0)%tele = v.
Proof.
case: n ctx v => [[] [] // | n1]; set n := n1.+1.
rewrite /chop0 /chop /chop_tele /n -/n -[n - 0]/n.
by elim: {n1}n => [_ [] | n IHn] //= [A ctx] /= [x v]; rewrite IHn.
Defined.

Fixpoint trunc_proj@{i j} n m1 m2 :
    m1 <= m2 -> forall ctx : context@{i j} n, ctx`_m2`_m1 -> ctx`_m1 :=
  match m1, m2 with
  | 0, _ => fun _ _ => id
  | _.+1, 0 => fun ff => match notF ff with end
  | m1.+1, m2.+1 => fun lem12 : m1 <= m2 =>
    if n is 0 then
      fun ctx '(Dpair x v) => [tele:= x, @trunc_proj 0 m1 m2 lem12 ctx v]
    else
      fun '(Dpair A ctx) '(Dpair x v) => [tele:= x, trunc_proj lem12 v]
  end.

Fixpoint trunc_unproj@{i j} n m1 m2 :
    m1 <= m2 -> forall ctx : context@{i j} n, ctx`_m1 -> ctx`_m2`_m1 :=
  match m1, m2 with
  | 0, _ => fun _ _ => id
  | _.+1, 0 => fun ff => match notF ff with end
  | m1.+1, m2.+1 => fun lem12 : m1 <= m2 =>
    if n is 0 then
      fun ctx '(Dpair x v) => [tele:= x, @trunc_unproj 0 m1 m2 lem12 ctx v]
    else
      fun '(Dpair A ctx) '(Dpair x v) => [tele:= x, trunc_unproj lem12 v]
  end.

Local Definition rechop_cast n k1 k2 : n - k1 - k2 = n - (k1 + k2) :=
  nat_cast (esym (subnDA k1 n k2)).

Definition rechop@{i j} {n k1 k2 ctx} (v : ctx :\ k1 :\ k2) : ctx :\ (k1 + k2)
  := ecast m ctx`_m (rechop_cast n k1 k2) (trunc_proj@{i j} (leq_subr _ _) v).

Definition chopD@{i j} {n k1 k2 ctx} (v : ctx :\ (k1 + k2)) : ctx :\ k1 :\ k2 :=
  trunc_unproj@{i j} (leq_subr _ _)
    (ecast m ctx`_m (esym (rechop_cast n k1 k2)) v).

Lemma trunc_projK@{i j} n m1 m2 (lem12 : m1 <= m2) ctx :
  cancel (@trunc_proj@{i j} n _ _ lem12 ctx) (@trunc_unproj n _ _ lem12 ctx).
Proof.
elim: m1 m2 lem12 n ctx => // m1 IHm [|m2] //= lem12.
by case=> [|n [A]] ctx /= [x v] /=; rewrite IHm.
Defined.

Lemma trunc_unprojK@{i j} n m1 m2 (lem12 : m1 <= m2) ctx :
  cancel (@trunc_unproj@{i j} n _ _ lem12 ctx) (@trunc_proj n _ _ lem12 ctx).
Proof.
elim: m1 m2 lem12 n ctx => // m1 IHm [|m2] //= lem12.
by case=> [|n [A]] ctx /= [x v] /=; rewrite IHm.
Defined.

Lemma rechopK@{i j} n k1 k2 ctx : cancel (@rechop@{i j} n k1 k2 ctx) chopD.
Proof.
by move=> v; rewrite /rechop /chopD; case: _ / rechop_cast; apply: trunc_projK.
Defined.

Lemma chopDK@{i j} n k1 k2 ctx : cancel chopD (@rechop@{i j} n k1 k2 ctx).
Proof.
by rewrite /chop => v; rewrite /rechop trunc_unprojK; case: _ / rechop_cast v.
Defined.

Lemma trunc_proj_tele@{i j} n m1 m2 (lem12 : m1 <= m2) ctx v :
  @trunc_proj@{i j} n m1 m2 lem12 ctx v`_m2`_m1 = (v`_m1)%tele.
Proof. 
elim: m1 m2 lem12 n ctx v => [|m1 IHm] [|m2] //= lem12 [|n].
  by case=> -[] /=; rewrite IHm.
by case=> A ctx /= [x v] /=; rewrite IHm.
Defined.

Lemma rechop_tele@{i j} n k1 k2 ctx v :
  @rechop@{i j} n k1 k2 ctx (v :\ k1 :\ k2) = (v :\ (k1 + k2))%tele.
Proof.
by rewrite /rechop trunc_proj_tele /chop /chop_tele; case: _ / rechop_cast.
Defined.

Lemma chopD_tele@{i j} n k1 k2 ctx v :
  @chopD@{i j} n k1 k2 ctx (v :\ (k1 + k2)) = (v :\ k1 :\ k2)%tele.
Proof. by rewrite -rechop_tele rechopK. Defined.

Lemma trunc_unproj_tele@{i j} n m1 m2 (lem12 : m1 <= m2) ctx v :
  @trunc_unproj@{i j} n m1 m2 lem12 ctx v`_m1 = (v`_m2`_m1)%tele.
Proof. by rewrite -(trunc_proj_tele lem12) trunc_projK. Defined.

Definition chopW@{i j} {n k1} k2 {ctx} (v : ctx :\ k1) : ctx :\ (k1 + k2) :=
  @rechop@{i j} n k1 k2 ctx (v :\ k2).

Lemma chopW_tele@{i j} n k1 k2 ctx v :
  @chopW@{i j} n k1 k2 ctx (v :\ k1) = (v :\ (k1 + k2))%tele.
Proof. exact: rechop_tele. Defined.

Lemma rechopW@{i j} n k1 k2 k3 ctx v :
  cast_chop (addnA k1 k2 k3) (rechop (chopW k3 v)) =
    chopW k3 (@rechop@{i j} n k1 k2 ctx v).
Proof.
rewrite /chopW /rechop /chop_tele /cast_chop /chop in v *.
rewrite /rechop_cast; case: _ / nat_cast (esym _ in RHS).
case: _ / nat_cast; case: _ / nat_cast (leq_subr _ _) => le31.
case: _ / (nat_cast _) => E; rewrite {E}nat_castK.
move: (leq_subr _ _) (leq_subr _ _) => le21 le32.
move: (n - k1) (_ - k2) (_ - k3) => h1 h2 h3 in v le31 le21 le32 *.
elim: h3 h2 h1 n => [|h3 IHh] // [|h2] [|h1] [|n] //= in ctx v le31 le32 le21 *.
  by case: v => -[] v /=; rewrite IHh.
by case: ctx v => A ctx /= [x v] /=; rewrite IHh.
Defined.

Fixpoint trunc_extend@{i j} n m :
    m <= n -> forall (ctx : context@{i j} n) cT, (ctx :+ cT)`_m -> ctx`_m :=
  match m, n with
  | 0, _ => fun _ _ _ => id | _, 0 => fun ff => match notF ff with end
  | m.+1, n.+1 => fun (lemn : m <= n) '(Dpair A ctx) cT '(Dpair x v) =>
    [tele:= x, trunc_extend lemn v]
  end.

Fixpoint extend_trunc@{i j} n m :
    m <= n -> forall (ctx : context@{i j} n) cT, ctx`_m -> (ctx :+ cT)`_m :=
  match m, n with
  | 0, _ => fun _ _ _ => id | _, 0 => fun ff => match notF ff with end
  | m.+1, n.+1 => fun (lemn : m <= n) '(Dpair A ctx) cT '(Dpair x v) =>
    [tele:= x, extend_trunc lemn _ v]
  end.

Definition chop_extend_cast n k : n + 1 - k.+1 = n - k :=
  nat_cast (congr1 (subn^~ k.+1) (addn1 n)). 
Definition chop_extend@{i j} {n k ctx cT} (v : (ctx :+ cT) :\ k.+1) : ctx :\ k
  := trunc_extend@{i j} (leq_subr _ _) (ecast m _`_m (chop_extend_cast n k) v).
Definition extend_chop@{i j} {n k ctx cT} (v : ctx :\ k) : (ctx :+ cT) :\ k.+1
  := ecast m _`_m (esym (chop_extend_cast n k))
    (extend_trunc@{i j} (leq_subr _ _) cT v).
  
Lemma trunc_extendK@{i j} n m (lemn : m <= n) ctx cT :
  cancel (@trunc_extend@{i j} n m lemn ctx cT) (extend_trunc lemn cT).
Proof.
elim: m n ctx cT lemn => [|m IHm] [|n] //= [A ctx] cT lemn /= [x v] /=.
by rewrite IHm.
Defined.

Lemma extend_truncK@{i j} n m (lemn : m <= n) ctx cT :
  cancel (extend_trunc lemn cT) (@trunc_extend@{i j} n m lemn ctx cT).
Proof.
elim: m n ctx cT lemn => [|m IHm] [|n] //= [A ctx] cT lemn /= [x v] /=.
by rewrite IHm.
Defined.

Lemma chop_extendK@{i j} n k ctx cT :
  cancel (@chop_extend@{i j} n k ctx cT) extend_chop.
Proof.
by move=> v; rewrite /extend_chop trunc_extendK; case: _ / chop_extend_cast.
Defined.

Lemma extend_chopK@{i j} n k ctx cT :
  cancel extend_chop (@chop_extend@{i j} n k ctx cT).
Proof.
rewrite /chop /extend_chop /chop_extend; move: (leq_subr _ _) => lenkn v.
by case: _ / chop_extend_cast in v lenkn *; apply: extend_truncK.
Defined.

Lemma trunc_extend_tele@{i j} n m (lemn : m <= n) ctx cT v z :
  @trunc_extend@{i j} n m lemn ctx cT (v :+ z)`_m = (v`_m)%tele.
Proof.
elim: m n ctx v => [|m IHm] [|n] //= [A ctx] /= [x v] /= in lemn cT z *.
by rewrite IHm.
Defined.

Lemma extend_trunc_tele@{i j} n m (lemn : m <= n) ctx cT v z :
  @extend_trunc@{i j} n m lemn ctx cT v`_m = ((v :+ z)`_m)%tele.
Proof. by rewrite -(trunc_extend_tele lemn z) trunc_extendK. Defined.

Lemma extend_chop_tele@{i j} n k ctx cT v z :
  @extend_chop@{i j} n k ctx cT (v :\ k) = ((v :+ z) :\ k.+1)%tele.
Proof.
by rewrite /extend_chop (extend_trunc_tele _ z); case: _ / chop_extend_cast.
Defined.

Lemma chop_extend_tele@{i j} n k ctx cT v z :
  @chop_extend@{i j} n k ctx cT ((v :+ z) :\ k.+1) = (v :\ k)%tele.
Proof. by rewrite -extend_chop_tele extend_chopK. Defined.

Lemma chop_extendW@{i j} n k1 k2 ctx cT v :
  @chop_extend@{i j} n (k1 + k2) ctx cT (@chopW _ k1.+1 k2 _ v)
    = chopW k2 (chop_extend v).
Proof.
rewrite /chop_extend /chopW /rechop /chop_tele /chop /chop_extend_cast in v *.
do !move: (leq_subr _ _); do 2!move: (congr1 _ _).
rewrite -[n.+1 - k1.+1]/(n - k1) -[n.+1 - (k1 + k2).+1]/(n - (k1 + k2)).
do 2!case: _ / rechop_cast; move=> E; case: _ / {E}(nat_cast E).
move=> E; rewrite {E}nat_castK; move: (_ - k1.+1) (_ - k2) => h1 h2 in v *.
elim: h2 h1 n ctx cT v => [|h2 IHh] [|h1] [|n] //= [A ctx] /= cT [x v] /=.
by move=> leh1n leh21 leh21' leh2n; rewrite -IHh.
Defined.

Lemma extend_chopW@{i j} n k1 k2 ctx cT v :
  @extend_chop@{i j} n (k1 + k2) ctx cT (chopW k2 v)
    = chopW k2 (extend_chop v).
Proof. by rewrite -[RHS]chop_extendK chop_extendW extend_chopK. Defined.

End Context.
*)

(******************************************************************************)
(*   Support for generic skolemization lemmas: distributing a series of       *)
(* over an aggregate of conjunctions or of (possibly) dependent tuple types,  *)
(* respectively. The set of conjunction or pairing operators supported can be *)
(* extended by declaring new instances of the supporting structures defined   *)
(* below. These support arbitrary n-ary conjuctions and most dependent record *)
(* types respectively (however, overlapping dependencies are not supported).  *)
(*   Factories for deriving instances from Coq-generated recursion principles *)
(* are provided, though instances can also be defined directly.               *)
(*   The structures for tuples use a more sophisticated design than the ones  *)
(* for conjunctions, using a datatype to describe operators as combinations   *)
(* of (possibly dependent) pairs. For n-ary conjunctions we can just use the  *)
(* integer n.                                                                 *)
(*   The exported user interface for these two modules consists of two lemmas *)
(* Lemma all_and {t e} {g : genAllAnd false t e} : g -> eval t e.             *)
(* Lemma all_pair {t} {g : genSig AtTop t} : g -> eval t g.                   *)
(******************************************************************************)

Module GenericSkolem.

Module And.

Implicit Types P Q R : Prop.

Definition operator n := nfun n Prop Prop.

Definition add_arg args P Q : Prop := args (P -> Q).

Fixpoint intro_ args {n} : operator n -> Prop :=
  if n isn't m.+1 then args else 
  fun a => forall P, intro_ (add_arg args P) (a P).
Definition intro {n} := @intro_ id n.

Fixpoint elim_ (args : Prop -> Prop) {n} : operator n -> Prop :=
  if n isn't m.+1 then fun Q => forall R, args R -> Q -> R
  else fun a => forall P, elim_ (add_arg args P) (a P).
Definition elim {n} := @elim_ id n.

Inductive term := Arg | Op n a of @intro n a & nat -> term.

Definition env := seq nat -> Prop.
Definition valid (e : env) : Prop := forall s, e s.

Fixpoint eval_op {n} : operator n -> (nat -> wrappedProp) -> wrappedProp :=
  if n isn't m.+1 then fun P _ => WrapProp P else
  fun a e_ => let: WrapProp P := e_ m in eval_op (a P) e_.

Fixpoint eval t e : wrappedProp :=
  if t isn't Op n a _ t_ then WrapProp (e [::]) else
  eval_op a (fun i => eval (t_ i) (e \o cons i)).

Fact evalP e t : valid e -> eval t e.
Proof.
elim: t e => //= n a Ca t IHg e eV.
do [rewrite /intro; set args := id] in Ca *; have argsP Q: args Q -> Q by [].
elim: n => /= [|n IHn] in a (args) argsP Ca *; first exact: argsP.
set P := eval _ _; have ->: P = WrapProp P by case: P.
by apply: IHn (Ca _) => Q /argsP; apply; apply/IHg=> s /=.
Qed.

Variant class_of P := Class (t : term) e & P -> valid e.
Structure genAnd :=
  GenAnd {gen_and :> wrappedProp; _ : class_of gen_and}.
Structure properGenAnd :=
  ProperGenAnd {proper_gen_and :> Prop; _ : class_of proper_gen_and}.

Definition trivial_gen_and P :=
  @GenAnd (wrap2Prop P) (@Class P Arg (fun=> P) (fun Pprf _ => Pprf)).

Coercion pclass g := let: ProperGenAnd _ Cg := g return class_of g in Cg.
Definition nontrivial_gen_and (g : properGenAnd) := @GenAnd (wrap1Prop g) g.

Definition class g := let: GenAnd _ Cg := g return class_of g in Cg.

Definition ProperGenAndOf n a (Ca : @intro n a) (Ka : elim a) :
  iter n (fun T => genAnd -> T) properGenAnd.
Proof.
pose extNfun T f x n : T := if n is m.+1 then f m else x.
move/Op in Ca; do [rewrite /elim; set args := id] in Ka *.
pose te := (fun=> Arg, fun=> fun=> True) : (nat -> term) * (nat -> env).
have teP: args (forall i, valid (te.2 i)) by split.
have argsP Q R: (Q -> R) -> args Q -> args R by move=> H /H.
elim: n => /= [|n IHn] in a (te) (args) Ka argsP teP *.
  exists a; case: te => t_ e_ /= in teP *.
  pose e s := if s is i :: s1 then e_ i s1 else True.
  by apply: (@Class a (Ca t_) e) => A [] //=; apply: Ka teP A.
move=> g; set P := g : Prop; pose te1 := let: Class t e _ := class g in
  let: (t_, e_) := te in (extNfun _ t_ t, extNfun _ e_ e).
apply: (IHn (a P) te1 _ (Ka P)) => [Q R Q_R|].
  abstract (by apply: argsP => P_Q /P_Q/Q_R).
abstract (by case: te class @te1 teP => _ e_ [_ e PeV] /=;
             apply: argsP => e_P /PeV-eV []).
Defined.
Arguments ProperGenAndOf n {a} Ca Ka.

Fact Prop_prod_ind : @elim 2 prod. Proof. by move=> P Q R PQ_R []. Defined.
Definition generic_prod2 g1 g2 :=
  let genProd2 := @ProperGenAndOf 2 prod (@pair) Prop_prod_ind g1 g2 in
  @ProperGenAnd (g1 * g2) genProd2.  

Definition generic_and2 := ProperGenAndOf 2 conj and_ind.

Definition generic_and3 := ProperGenAndOf 3 And3 and3_ind.

Definition generic_and4 := ProperGenAndOf 4 And4 and4_ind.

Definition generic_and5 := ProperGenAndOf 5 And5 and5_ind.

Variant position := AtTop | InForall.
Structure genAllAnd (p : position) (t : term) e := GenAllAnd {
  gen_all_and :> genAnd; _ : gen_all_and -> valid e}.

Definition trivial_all_and t e wP PeV :=
  @GenAllAnd InForall t e (@GenAnd wP (@Class wP t e PeV)) PeV.

Fact nontrivial_all_andP t A e (g : forall x, genAllAnd InForall t (e x)) :
  (forall x : A, g x) -> valid (fun s => forall x, e x s).
Proof. by move=> gA s x /=; case: (g x) (gA x) => Q PeV /PeV; apply. Qed.
Definition nontrivial_all_and p t A e g :=
  @GenAllAnd p t  _ (trivial_gen_and _) (@nontrivial_all_andP t A e g).

End And.

Module Pair.

Set Universe Polymorphism.
Import Context.
Open Scope context_scope.

Inductive arity :=
 | Arg of nat | CstT | CstP
 | Push of arity | Trunc of nat & arity 
 | Prod of arity & arity | Sigma of nat & arity.
Definition ArgT := Arg 0.

Declare Scope arity_scope.
Bind Scope arity_scope with arity.
Delimit Scope arity_scope with arity.
Implicit Type a : arity.

Fixpoint label_arity a n K : arity * nat :=
  match a with
  | Arg _ => K (Arg n) n.+1 | CstT | CstP => K a n
  | Push a1 => label_arity a1 n (K \o Push)
  | Trunc h a1 => label_arity a1 n (K \o Trunc h)
  | Prod a1 a2 =>
    label_arity a1 n (fun b m => label_arity a2 m (K \o Prod b))
  | Sigma h a1 => label_arity a1 n (K \o Sigma h)
  end.

Fixpoint subst_arity a args := match a with
 | Arg i => args i | CstT | CstP => a
 | Push a1 => Push a1.[args] | Trunc k a1 => Trunc k a1.[args]
 | Prod a1 a2 => Prod a1.[args] a2.[args]
 | Sigma k a1 => Sigma k a1.[args]
 end where "a .[ args ]" := (subst_arity a args) : arity_scope.

Fixpoint env_@{i j} (ctx : context@{j}) (Lctx : ctx -> context@{j}) a : context@{i} :=
  match a return context@{i} with
  | Arg _ | CstT => [ctx: ctx /.v (Lctx v / Type@{j})]
  | CstP => [ctx: ctx /.v (Lctx v / Prop)]
  | Trunc h a1 => env_ (fun v => (Lctx v)`_h) a1
  | Push a1 => env_ (fun _ : join Lctx => Null) a1
  | Prod a1 a2 => env_ Lctx a1 ++ env_ Lctx a2
  | Sigma k a1 =>
    let Lctx1 cT v := Lctx v :+ fun u => cT.[v].[u] in
    [ctx cT : ctx /.v (Lctx v / Type@{j}), env_ (Lctx1 cT) a1]
  end.
Notation env := (env_ Null).
Definition operator@{i j k} a := env_@{i j k} Null a / Type@{k}.

Record map@{i j} {h1 h2} ctx1 ctx2 : Type@{i} := Map {
  apply_map : forall k, @chop@{i j} h1 ctx1 k -> @chop@{i j} h2 ctx2 k;
  mapW k1 k2 v : chopW k2 (@apply_map k1 v) = apply_map (chopW k2 v)
}.
Coercion apply_map : map >-> Funclass.
Arguments mapW {hi h2 ctx1 ctx2} f k1 k2 v : rename.

Definition map0@{i j} {h1 h2 ctx1 ctx2} f v :=
  chop0 (@apply_map@{i j} h1 h2 ctx1 ctx2 f 0 (v :\ 0)%tele).

Lemma map0W@{i j} {h1 h2 ctx1 ctx2} f v k :
  (@map0@{i j} h1 h2 ctx1 ctx2 f v :\ k)%tele = f k (v :\ k)%tele.
Proof. by rewrite -!(chopW_tele 0 k) chop0K mapW. Defined.

Definition chop_map@{i j} {h1 h2 ctx1 ctx2} k :
  @map@{i j} h1 h2 ctx1 ctx2 -> map (ctx1 :\ k) (ctx2 :\ k).
Proof.
move=> f; exists (fun k1 v => chopD (f (k + k1) (rechop v))) => k1 k2 v.
rewrite -[LHS]rechopK -[rechop _](cast_chopK (addnA k k1 k2)) rechopW chopDK.
rewrite mapW -rechopW /cast_chop.
by case: _ / (nat_cast _) (esym _) => E; rewrite nat_castK.
Defined.

Definition extend_map@{i j} {h1 h2 ctx1 ctx2} cT1 cT2 :
  let ctx1T := ctx1 :+ cT1 in let ctx2T := ctx2 :+ cT2 in
  forall f (h : forall v, cT1 v -> cT2 (@map0@{i j} h1 h2 ctx1 ctx2 f v)),
  map ctx1T ctx2T.
Proof.
move=> ctx1T ctx2T f h; have @fT k: ctx1T :\ k -> ctx2T :\ k.
  case: k => [|k] v; last exact: extend_chop (f k (chop_extend v)).
  by case/chop0/split_extend: v => v z; apply: ((map0 f v :+ h v z) :\ 0)%tele.
exists fT => -[|k1] k2 v /=; last by rewrite chop_extendW -extend_chopW -mapW.
rewrite -[v in RHS]chop0K -[chop0 _ in RHS]split_extendK.
case: split_extend => {}v z; rewrite !chopW_tele.
case: k2 => [|k2] /=; first by rewrite chopK extend_teleK.
by rewrite chop_extend_tele -extend_chop_tele map0W.
Defined.

Definition const_map@{i j} h ctx v : map@{i j} Null ctx :=
  @Map 0 h Null _ (fun k _ => v :\ k)%tele (fun k1 k2 _ => chopW_tele k1 k2 v).

Definition map_ctx_env@{i j k} {a h0 h1 ctx0 ctx1} :
  map ctx1 ctx0 -> @env_@{i j k} h0 ctx0 a -> @env_@{i j k} h1 ctx1 a.
Proof.
do [fix IHa 1] in a h0 h1 ctx1 ctx0 * => f.
case: a => [i|||a1 a2|k a|k a] /=;
  try by case=> T; split=> //; apply/abs=> v; apply: T.[map0 f v].
- by case/split_join=> e1 e2; apply: join_tele; apply: IHa f _.
- exact: IHa (chop_map k f).
case=> T e; pose Tf v := T.[f k v]; exists (abs Tf).
apply: IHa e; apply: extend_map (f) _ => v z.
by rewrite map0W -[T.[_]](subst_abs@{j k j} Tf).
Defined.

Definition subst_ctx_env@{i j k} a h ctx v : @env_ h ctx a -> env a :=
  map_ctx_env@{i j k} (const_map v).

Axiom skip@{i} : forall {T : Type@{i}}, T.

Fact subn_minl h k : h - minn k h = h - k.
Proof. by case: leqP => // /ltnW/eqnP->; rewrite subnn. Qed.

Fixpoint eval_env@{i j k} a args (eval_arg : forall i, env (args i) -> Type@{k})
  : forall {h ctx}, @env_@{i j k} h ctx (subst_arity h a args) -> env_ ctx a :=
  match a with
  | Arg i => fun h ctx e =>
   [pair abs (fun v => eval_arg i (subst_ctx_env v e)), tt]
  | CstT | CstP => fun _ _ => id
  | Prod a1 a2 => fun h ctx e =>
    let: Dpair e1 e2 := split_join e in
    (eval_env eval_arg e1 ++ eval_env eval_arg e2)%tele
  | Trunc k0 a1 => fun h ctx e =>
    let e1 := ecast k (env_ (ctx`_k) _) (nat_cast (subn_minl h k0)) e in
    eval_env eval_arg e1
  | Sigma k0 a1 => fun h ctx e =>
    let etype k := [ctx T : _ / Type@{k}, env_ (ctx :+ (fun v => T.[v`_k])) _]
    in let: Dpair T e1 := ecast k (etype k) (nat_cast (subn_minl h k0)) e 
    in [tele:= T, eval_env eval_arg e1]
  end.

(*
Definition eval_env@{i j k}
    a args (eval_arg : forall i h (ctx : context h),
                       ctx -> env_@{i j k} ctx (args i) -> Type@{k})
    h0 h1 (ctx0 : context h0) (ctx1 : context h1) 
    (ctx10 : forall k, ctx1 :\ k -> ctx0 :\ k) 
    (ctx10W : forall k h v, chopW k (ctx10 h v) = ctx10 (h + k) (chopW k v)) :
  env_@{i j k} ctx0 (subst_arity h1 a args) -> env_@{i j k} ctx1 a.
Proof.
have minnI h k : h - k = h - minn k h.
  by case: leqP => // /ltnW/eqnP->; rewrite subnn.
do [move: a; fix IHa 1 => -[i|||a1 a2|k1 a1|k1 a1]/=]
  in h0 h1 ctx1 ctx0 ctx10 ctx10W *.
- move/(eval_arg i _ ctx0)=> cT; split=> //; apply/abs=> w.
  exact/cT/chop0/ctx10/chop_tele.
- case=> cT _; split=> //; apply/abs=> w.
  exact/(subst cT)/chop0/ctx10/chop_tele.
- case=> cT _; split=> //; apply/abs=> w.
  exact/(subst cT)/chop0/ctx10/chop_tele.
- have{} IHa := IHa _ h0 h1 ctx1 ctx0 ctx10 ctx10W.
  by case/split_join=> /IHa-e1 /IHa-e2; apply: (e1 ++ e2)%tele.
- rewrite /chop (nat_cast (minnI h1 k1)) -!/(chop _ _); set k2 := minn k1 h1.
  apply: IHa (fun k v => chopD (ctx10 (k2 + k) (rechop v))) _ => k h v.
  rewrite -[LHS]rechopK -[rechop _](cast_chopK (addnA k2 h k)) rechopW.
  rewrite chopDK ctx10W -rechopW /cast_chop.
  by case: _ / (nat_cast _) (esym _) => E; rewrite nat_castK.
rewrite /chop /chop_tele (nat_cast (minnI h1 k1)) -!/(_ :\ _).
set k2 := minn k1 h1 => -[cT]; set ctx0T := ctx0 :+ _ => e.
pose cTf v := cT.[ctx10 k2 v]; exists (abs cTf); set ctx1T := ctx1 :+ _.
have @ctx10T k: ctx1T :\ k -> ctx0T :\ k.
  case: k => [|k] v; last exact: extend_chop (ctx10 _ (chop_extend v)).
  case/chop0/split_extend: v => v z.
  refine ((chop0 (ctx10 0 (v :\ 0)) :+ _) :\ 0)%tele.
  rewrite -[z in cT.[z]](@rechop_tele _ 0 k2) chop0K.
  rewrite [z in cT.[z]](ctx10W _ 0 _) /chopW rechop_tele.
  by rewrite -[cT.[_]](subst_abs@{j k j} cTf).
rewrite {+}/eq_rect {+}/eq_rect_r /= -[Logic.eq_sym]/(@esym) in ctx10T.
apply: IHa (ctx10T) _ e => k [|h] v /=; last first.
  by rewrite chop_extendW -extend_chopW -ctx10W.
rewrite -[v in RHS]chop0K -[chop0 _ in RHS]split_extendK.
case: split_extend => {}v z; case: k => [|k] /=.
  by rewrite [LHS]chopW_tele [in RHS]chopW_tele !chopK extend_teleK.
rewrite [LHS]chopW_tele [in RHS]chopW_tele chop_extend_tele -extend_chop_tele.
by rewrite -(chopW_tele 0) chop0K ctx10W chopW_tele.
Defined.
*)

Fixpoint hyps_@{i j k} {h ctx a} :
    @env_@{i j k} h ctx a -> ctx -> context@{i j} (env_depth a) :=
  match a with
  | Arg _ | CstT | CstP => fun cT v => [ctx: cT.1d.[v]]
  | Prod a1 a2 => fun e v =>
    let: Dpair e1 e2 := split_join e in hyps_ e1 v ++ hyps_ e2 v
  | Trunc k a1 => fun (e : env_ _ a1) v => hyps_ e (v :\ k)
  | Sigma k a1 => fun '(Dpair cT e1) v => [ctx x, hyps_ e1 (v :+ x)]
end.

Definition intro@{i j k} a (s : operator a) : Type@{j} :=
  env a /.e (hyps_@{i j k} e tt / s.[e]).
Arguments intro : clear implicits.

Definition elim@{i j k} a s (Cs : intro@{i j k} a s) :=
  env a /.e forall G, hyps_ e tt /.h G Cs.[e].[h] -> forall sv, G sv.
Arguments elim : clear implicits.

Inductive term@{i j k} : Type@{i} :=
  ArgTerm | OpTerm a s of intro@{i j k} a s & nat -> term.

Fixpoint term_arity@{i j k} (t : term@{i j k}) :=
  if t isn't OpTerm a _ _ t_ then CstT else a.[term_arity \o t_]%arity.
Coercion term_arity : term >-> arity.

Fixpoint eval@{i j k} (t : term@{i j k}) : env t -> Type@{k} :=
  if t isn't OpTerm a s _ t_ then fun e => e.1d.[tt] else
  fun e => s.[eval_env (fun i => @eval (t_ i)) e].
(*
Fixpoint eval_rec@{i j k} (t : term) {h0 ctx0} v0 : env_ ctx0 t -> Type@{k} :=
  if t isn't OpTerm a s _ t_ then fun e => e.1d.[v0] else
  let eval_arg i := @eval_rec (t_ i) in
  let ctx10 k _ := (v0 :\ k)%tele in
  let ctx10W k h v := chopW_tele h k v0 in
  fun e => s.[@eval_env@{i j k} a t_ eval_arg h0 0 ctx0 Null ctx10 ctx10W e].
Definition eval@{i j k} (t : term) : env t -> Type@{k} :=
  eval_rec@{i j k} (tt : Null).
*)
Arguments eval t e : clear implicits.

Definition valid@{i j k} a (e : env a) : Type@{j} := hyps_@{i j k} e tt.

Lemma map0_chop_map@{i j} {h1 h2 ctx1 ctx2} f k v :
  map0 (@chop_map@{i j} h1 h2 ctx1 ctx2 k f) (v :\ k) = (map0 f v :\ k)%tele.
Proof. by rewrite -[RHS]chopK -chopD_tele map0W -rechop_tele. Defined.

Lemma subst_valid@{i j k} a h ctx e v :
  @hyps_ h ctx a e v -> valid@{i j k} (subst_ctx_env v e).
Proof.
rewrite /subst_ctx_env /valid; set ctx1 := Null; set h1 := 0 in ctx1 *.
set f : map ctx1 ctx := const_map _; set v1 : ctx1 := tt.
have ->: v = map0 f v1 by rewrite [RHS]chopK.
do [fix IHa 1] in a h (h1) ctx (ctx1) {v1}(v := v1) {v}(f) e *.
case: a => [i|||a1 a2|k a|k a] /= in e *;
  try by case: e => /= T _ [x _]; rewrite subst_abs.    
- case/split_join: e => e1 e2 /split_join[He1 He2].
  by rewrite join_teleK; apply: join_tele; apply: IHa.
- by rewrite -map0_chop_map; apply/IHa.
case: e => T e /= [x He]; set Tx1 := _.[_].
have @x1: Tx1 by rewrite [Tx1]subst_abs -map0W.
exists x1; apply: IHa; rewrite /map0 /= chopK extend_teleK chopK.
by rewrite /eq_rect_r /eq_rect ecastKv ecastK.
Qed.

Lemma evalP@{i j k} (t : term) e : valid e -> eval@{i j k} t e.
Proof.
elim: t e => [? []|a s Cs t_ IHt] //= e.
rewrite /valid => He; refine Cs.[_].[_] => {s Cs}.
do [set h := 0; set ctx : context h := Null; set v : ctx := tt] in e He *.
elim: a => [i|||a1 IHa1 a2 IHa2|k a IHa|k a IHa] //= in (h) (ctx) e (v) He *.
- by split=> //; rewrite subst_abs; apply/IHt/subst_valid.
- case/split_join: e He => e1 e2 /split_join[He1 He2].
  by rewrite join_teleK; apply: join_tele; [apply: IHa1 | apply: IHa2].
- by do [rewrite /chop_tele /chop; case: _ / (nat_cast _)] in e He *; apply/IHa.
rewrite /chop_tele /chop; case: _ / (nat_cast _).
by case: e He => T e /= [x /IHa]; exists x.
Qed.

(*Lemma evalP@{i j k} (t : term) e : valid e -> eval@{i j k} t e.
Proof.
rewrite /valid /eval.
elim: t => [|a s Cs t_ IHt]/= in (h0 := 0) (ctx0 := Null) (v0 := tt : Null) e *.
  by case.
move=> He; refine Cs.[_].[_] => {s Cs}; set eval_arg := fun i => @eval_rec _.
move: e He; set h1 := 0; set ctx1 : context h1 := Null; set v1 : ctx1 := tt.
set ctx10 := fun k (v : ctx1 :\ k) => chop_tele _ _ : ctx0 :\ k.
set ctx10W : forall k h v, chopW k (ctx10 h v) = ctx10 (h + k) (chopW k v) :=
  fun _ _ _ => chopW_tele _ _ _.
have ->: v0 = chop0 (ctx10 0 (v1 :\ 0)%tele) by rewrite chopK.
do [move: a; fix IHa 1 => -[i|||a1 a2|k0 a1|k0 a1]]
  in h0 (h1) ctx0 (ctx1) {v0} (v1) (ctx10) (ctx10W) *.
- by move=> e He; split=> //; rewrite subst_abs; apply: IHt He.
- by case=> T _ /= [x _] /=; split=> //; rewrite subst_abs.  
- by case=> P _ /= [Pprf _] /=; split=> //; rewrite subst_abs.  
- rewrite /= /ssr_have => e; case/split_join: e => e1 e2 /split_join[x1 x2].
  by rewrite join_teleK; apply: join_tele; apply: IHa.
- simpl; set k1 := minn k0 h1 => e He; set e1 := eval_env _ _.
  rewrite /eq_rect_r /chop_tele /chop; elim/nat_cast_r: _ / _ => /= in e He *.
  apply: IHa; rewrite -ctx10W rechopK chopK -/(v1 :\ k1)%tele.
  by congr (hyps_ e _): He; rewrite -(chopW_tele 0 k1) chop0K ctx10W chopW_tele.
simpl; set k1 := minn k0 h1; set E1 := eq_rect_r _ _.
rewrite /chop_tele /chop; elim/nat_cast_r: _ / _; rewrite {}/E1 /eq_rect_r.
case=> A e /= [x He]; set A1 := _.[_].
have @x1: A1.
  rewrite /A1 subst_abs -/(v1 :\ k1)%tele -(chopW_tele 0 k1) -(ctx10W k1 0).
  by rewrite -[ctx10 0 _]chop0K chopW_tele; apply: x.
exists x1; apply: IHa; rewrite chopK extend_teleK chopK; congr hyps_: He.
rewrite -/(v1 :\ 0)%tele; set v0 := chop0 _ in x1 *; congr extend_tele.
rewrite -!/(chopW_tele _ _ _) {}/x1 /eq_rect_r /= -/esym /eq_rect ecastKv.
by rewrite !ecastK ecastKv.
Qed.
*)

Definition all_env_@{i j k} {A : Type@{k}} {h a ctx0 ctx1} :
      (forall x : A, map ctx1 (ctx0 x)) ->
      (forall x : A, @env_@{i j k} h (ctx0 x) a) ->
  @env_@{i j k} h ctx1 a.
Proof.
do [fix IHa 1] in a h ctx0 ctx1 *.
case: a => [i|||a1 a2|k a|k a] /= f e;
  try by split=> //; apply/abs=> v; apply: (forall x, (e x).1d.[map0 (f x) v]).
- by apply: join_tele; apply: IHa f _ => x; case/split_join: (e x).
- by apply: IHa e => x; apply: chop_map.
pose T v := forall x, (e x).1d.[f x k v]; pose eT x := (e x).2d.
exists (abs T); apply: IHa eT => x; apply: extend_map (f x) _ => v z.
by rewrite map0W; move: x; rewrite -/(T _) -(subst_abs T).
Defined.

Definition null_map@{i j} :=
  @Map@{i j} 0 0 Null Null (fun=> id) (fun _ _ _ => erefl).

Definition all_env@{i j k} {A a} (e : _ -> env@{i j k} a) :=
  @all_env_ A 0 a (fun=>Null) Null (fun=> null_map) e.

Lemma all_envP@{i j k} A a e :
  (forall x, valid (e x)) -> valid (@all_env@{i j k} A a e).
Proof.
move=> He; rewrite /valid /all_env; set ctx1 := Null; set ctx0 := fun=> Null.
set h := 0 in ctx0 ctx1 *; set v : ctx1 := tt.
set f : forall x, map ctx1 (ctx0 x) := fun=> null_map.
change (forall x, env_ (ctx0 x) a) in e.
change (forall x, hyps_ (e x) (map0 (f x) v)) in He.
do [fix IHa 1] in a (h) (ctx0) (ctx1) (f) e (v) He *.
case: a => [i|||a1 a2|k a|k a] //= in e He *;
  try by split=> //; rewrite subst_abs => x; case: (He x).
- by rewrite join_teleK; apply/join_tele; apply/IHa=> x;
    case/split_join: (e x) (He x) => e1 e2 /= /split_join[].
- by apply/IHa=> x; rewrite map0_chop_map.
set T := _.[_]; have @z: T.
  by rewrite [T]subst_abs => x; rewrite -map0W; case: (e x) (He x) => T1 e1 [].
exists z; apply/IHa=> x; rewrite /map0 /= chopK extend_teleK.
rewrite /eq_rect_r /eq_rect ecastKv ecastK chopK.
by case: (e x) (He x) => T1 e1 [].
Qed.

Variant position := Pos (at_top : bool) (in_forall : bool).
Definition AtTop := Pos true true.
Definition InForall := Pos false true.
Definition InSig := Pos false false.

Record class_of@{i j k} (t : term@{i j k}) (T : Type@{k}) : Type :=
  Class {class_env :> env@{i j k} t; classP : T -> valid class_env}.

Structure genSig@{i j k} (p : position) t :=
  GenSig {gen_sig :> wrappedType@{k}; _ : class_of@{i j k} t gen_sig}.
Coercion genSig_class@{i j k} p t (g : genSig@{i j k} p t) :=
  let: GenSig _ Cg := g return class_of t g in Cg.

Structure properGenSig@{i j k} t := ProperGenSig {
  proper_gen_sig :> Type@{k}; _ : class_of@{i j k} t proper_gen_sig}.
Coercion properGenSig_class@{i j k} t g :=
  let: ProperGenSig _ Cg := g return class_of@{i j k} t g in Cg.

Definition nontrivial_gen_sig@{i j k} b t (g : properGenSig@{i j k} t) :=
  @GenSig (Pos false b) t (wrap1Type g) g.

Fact generic_forallP@{i j k} t (A : Type@{k})
    (g : A -> genSig@{i j k} InForall t) :
  (forall x : A, g x) -> @valid@{i j k} t (all_env g).
Proof. by move=> gA; apply/all_envP=> x; apply/classP/gA. Qed.
Definition generic_forall@{i j k} b t (A : Type@{k}) g :=
  @GenSig (Pos b true) t (wrap2Type _) (Class (@generic_forallP@{i j k} t A g)).

Definition trivial_gen_sig@{i j k} (T : Type@{k}) :=
  @GenSig@{i j k} InSig ArgTerm (wrap3Type T)
     (@Class ArgTerm T [pair T, tt] (fun x => [pair x, tt])).

Fixpoint term_ctx@{i j k l} n : context@{l i} n :=
  if n is 0 then Null else [ctx: term@{i j k}, term_ctx _].

Fixpoint args_of_ctx@{i j k l} n : term_ctx@{i j k l} n -> nat -> term :=
  if n isn't m.+1 then fun _ _ => ArgTerm else
  fun '(Dpair t e) i => if i isn't j.+1 then t else args_of_ctx e j.

Definition term_of_ctx a n s (Cs : intro a s) (e : term_ctx n) :=
  OpTerm Cs (args_of_ctx e).

Fixpoint gen_env_ctx@{i j k} {h} ctx a args : context (env_depth a) :=
  match a 
return context (env_depth a)
with
  | Arg i => [ctx: ctx / genSig@{i j k} InSig (args i)]
  | CstT => [ctx: @under@{j k j} h ctx (fun=> Type@{k})]
  | CstP => [ctx: @under@{j k j} h ctx (fun=> Prop)]
  | Prod a1 a2 => gen_env_ctx ctx a1 args ++ gen_env_ctx ctx a2 args
  | Trunc k0 a1 => gen_env_ctx (ctx :\ k0) a1 args
  | Sigma k0 a1 =>
      [ctx cT : (ctx :\ k0) / Type@{k},
        gen_env_ctx (ctx :+ (fun v => subst@{j k j} cT (v :\ k0))) a1 args]
  end.

Definition abs_env_ctx@{i j k} {h0 h1 a ctx0 ctx1}
   (f : @map@{i j k} h1 h0 : (ctx /.v env_@{i j k} (ctx0 v) a) -> @env_@{i j k} h ctx a.
move/subst; do [fix IHa 1] in a h ctx *.
case: a => [i|||a1 a2|k a|k a] /=;
  try exact: (fun e => [pair abs (fun v => (e v).1d), tt]).
- by move=> e; apply/join_tele; apply/IHa=> /e/split_join[].
- e; pose e' := all_env (subst e).

Fixpoint env_of_ctx@{i j k} ctx a args
          : gen_env_ctx@{i j k} ctx a args -> env_ ctx a.[args] :=
  match a
return 
gen_env_ctx@{i j k} ctx a args -> env_ ctx a.[args]
 with
  | CstT | CstP => id
  | Arg _ => fun e => 
  | Prod a1 a2 => fun e v => let: Dpair e1 e2 := split_join e in
    [pair env_of_ctx e1 v, env_of_ctx e2 v]
  | Trunc k a1 => fun e v => @env_of_ctx (ctx :\ k) a1 args e (v :\ k)
  | Sigma k a1 => fun '(Dpair cA eA) v =>
    let e_ x := env_of_ctx eA (v :+ x) in
    [dpair A : Type@{j} := cA.[v :\ k], e_ : _]
  end.

Fixpoint expr_env_of_ctx@{i j} ctx a args
           : gen_env_ctx@{i j} ctx a args -> ctx -> env a :=
  match a with
  | Arg _ => fun e v => gen_sig (dfst e).[v]
  | CstT | CstP => fun e v => (dfst e).[v]
  | Prod a1 a2 => fun e v => let: Dpair e1 e2 := split_sum e in
    [pair expr_env_of_ctx e1 v, expr_env_of_ctx e2 v]
  | Sigma a1 => fun '(Dpair cA eA) v =>
    let e_ x := expr_env_of_ctx eA (v :+ x) in
    [dpair A : Type@{j} := cA.[v], e_ : _]
  end.

Lemma env_of_ctxP@{i j} a args ctx s Cs (e : gen_env_ctx@{i j} ctx a args) v :
    elim@{i j} a s Cs -> wrapped_subst s (expr_env_of_ctx e v) ->
  valid (env_of_ctx e v).
Proof.
rewrite unwrap_subst /=; set e_s := expr_env_of_ctx _ _.
move/(fun e => e.[e_s])/(_ (fun=> _)); apply; apply/abs=> {s Cs}/intro_substP/=.
elim: a => //= [i|a1 IHa1 a2 IHa2|a IHa] in ctx v e e_s *; first exact: classP.
  by case: split_sum @e_s => e1 e2 /= [/IHa1-v1 /IHa2].
by case: e @e_s => A eA /= [x /IHa]; exists x.
Qed.

Definition RectProper@{i j} a0 :=
  let a_n := label_args a0 0 pair in let a := a_n.1 in let n := a_n.2 in
  fun s Cs (Es : elim@{i j} a s Cs) =>
  let t := @term_of_ctx a n s Cs in
  let S e := properGenSig (t e) in
  let gctx e := gen_env_ctx Nil a (args_of_ctx e) in
  let R e := gctx e / S e in
  @abs (term_ctx n) R (fun e => @abs (gctx e) (fun=> S e) (fun ge =>
  let Pack := @ProperGenSig (t e) in
  let PackT (wT : wrappedType) := class_of (t e) wT -> S e in
  let wT := wrapped_subst s (expr_env_of_ctx ge tt) in 
  let PackC := let: WrapType T := wT return PackT wT in Pack T in
  PackC (@Class (t e) wT (env_of_ctx ge tt) (env_of_ctxP Es)))).
Arguments RectProper a0 s {Cs} Es.

Definition generic_prod@{i j} := Eval hnf in
  RectProper@{i j} (Prod ArgT ArgT) (@prod) (@prod_rect).

Definition generic_sig@{i j} := Eval hnf in
   RectProper@{i j} (Sigma CstP) (@sig) (@sig_rect).

Definition generic_dpair@{i j} := Eval hnf in
   let dpair_rect (A : Type@{j}) (T : A -> Type@{j})
                  (G : {dpair x, T x} -> Type@{j}) IH u :=
     let: Dpair x y := u return G u in IH x y in
   RectProper@{i j} (Sigma ArgT) (@dpair) dpair_rect.

Definition generic_sig2@{i j} := Eval hnf in
   @RectProper@{i j} (Sigma (Prod CstP CstP)) (@sig2) (@exist2) (@sig2_rect).

Definition generic_sigT@{i j} := Eval hnf in
   @RectProper@{i j} (Sigma ArgT) (@sigT) (@existT) (@sigT_rect).

Definition generic_sigT2@{i j} := Eval hnf in
   @RectProper@{i j} (Sigma (Prod ArgT ArgT)) (@sigT2) (@existT2) (@sigT2_rect).

End SkolemizeSig.
End SkolemizeSig.
  
Fixpoint env_@{i j} (ctx : context@{i}) a : context@{i} :=
  match a with
  | Arg _ | CstT => [ctx: ctx / Type@{j}]
  | CstP => [ctx: ctx / Prop]
  | Prod a1 a2 => env_ ctx a1 ++ env_ ctx a2
  | Sigma a1 => [ctx cT : ctx / Type@{j}, env_ (ctx :+ cT) a1]
  | Curtail a1 => env_ (dfst (split_extend ctx))
  end.
Definition operator@{i j} a := (env_@{i j} Nil a / Type@{j}).

Fixpoint env@{i j} a : Type@{i} :=
  match a with
  | Arg _ | CstT => Type@{j} | CstP => Prop
  | Prod a1 a2 => {pair env a1, env a2}
  | Sigma a1 => {dpair A : Type@{j}, A -> env a1}
  end.

Fixpoint subst_env@{i j} {ctx a} : env_@{i j} ctx a -> ctx -> env a :=
  match a with
  | Arg _ | CstT | CstP => fun '(Dpair cT _) v => cT.[v]
  | Prod a1 a2 => fun e v =>
    let: Dpair e1 e2 := split_sum e in [pair subst_env e1 v, subst_env e2 v]
  | Sigma a1 => fun '(Dpair cT e) v =>
    [dpair T : Type@{j} := cT.[v], (fun x => subst_env e (v :+ x)) : T -> _]
  end.

Fixpoint env_under@{i j} ctx a : ctx / env@{i j} a -> env_ ctx a :=
  match a return ctx / env a -> env_ ctx a with
  | Arg _ | CstT | CstP => fun cT => [val cT, tt : Nil@{i}]
  | Prod a1 a2 => fun e =>
    (env_under (map dfst e) + env_under (map ndsnd e))%val
  | Sigma a1 => fun e =>
    [val cT := map dfst e, env_under (dmap@{i j} dsnd e) : env_ (ctx :+ cT) a1]
  end.
Coercion env_value@{i j} {a} (e : env@{i j} a) := @env_under Nil a e.

Fixpoint intro_@{i j} a : env@{i j} a -> context@{j} :=
  match a with
  | Arg _ | CstT | CstP => fun T => [ctx: T]
  | Prod a1 a2 => fun e => intro_ (dfst e) + intro_ (ndsnd e)
  | Sigma a1 => fun e => [ctx x : dfst e, intro_ (dsnd e x)]
  end.
Arguments intro_ : clear implicits.

Definition intro@{i j} a (s : operator a) : Type@{i} :=
  env_@{i j} Nil a /.e (intro_ a (subst_env e tt) / s.[e]).
Arguments intro : clear implicits.

Definition elim@{i j} a s (Cs : intro@{i j} a s) :=
  let IH e G := intro_ a (subst_env e _) /.eIH G Cs.[e].[eIH] in
  env_ Nil a /.e (forall G, IH e G -> forall sv, G sv).
Arguments elim : clear implicits.

Inductive term@{i j} : Type@{i} :=
  ArgTerm | OpTerm a s of intro@{i j} a s & nat -> term.

Fixpoint term_arity@{i j} (t : term@{i j}) :=
  if t isn't OpTerm a _ _ t_ then CstT else a.[term_arity \o t_]%arity.
Coercion term_arity : term >-> arity.

Fixpoint chop@{i j} a args (rec : forall i, env (args i) -> Type@{j}) :
    env@{i j} a.[args] -> env a :=
  match a with
  | Arg i => rec i | CstT | CstP => id
  | Prod a1 a2 => fun '(Dpair e1 e2) => [pair chop rec e1, chop rec e2]
  | Sigma a1 => fun '(Dpair A eA) =>
    [dpair A : Type@{j}, (fun x => chop rec (eA x)) : A -> env a1]
  end.

Fixpoint eval@{i j} (t : term@{i j}) : env t -> Type@{j} :=
  if t isn't OpTerm a s _ t_ then id else
  fun e => s.[chop (fun i => @eval (t_ i)) e].
Arguments eval t e : clear implicits.

Fixpoint valid@{i j} a : env@{i j} a -> Type@{j} :=
  match a with
  | Arg _ | CstT | CstP => id
  | Prod a1 a2 => fun e => {pair valid (dfst e), valid (ndsnd e)}
  | Sigma a1 => fun e => {dpair x : dfst e, valid (dsnd e x)}
  end.

(*
Fixpoint valid_value@{i j} a : forall e, valid@{i j} e -> intro_ a e :=
  match a with
  | Arg _ | CstT | CstP => fun T x => [val x, tt : Nil@{j}]
  | Prod a1 a2 => fun e '(Dpair v1 v2) => (valid_value v1 + valid_value v2)%val
  | Sigma a1 => fun e '(Dpair x e_x) => [val:= x, valid_value e_x]
  end.
Coercion valid_value : valid >-> value.
*)

Lemma intro_substP@{i j} a ctx (e: ctx / env a) v :
  valid e.[v] <--> intro_ a (subst_env@{i j} (env_under e) v).
Proof.
have pair_unit T: T <--> {pair T, unit} by split=> [|[]].
elim: a => //= [a1 IHa1 a2 IHa2 | a1 IHa1] in ctx v e *.
  rewrite sum_valK /= -2!(subst_map _ e).
  by split=> [|/split_sum] [/IHa1-Ie1 /IHa2-Ie2] //; apply: sum_val.
have @Dev: ((map dfst e).[v] = dfst e.[v])%type by apply: subst_map.
split=> [[x] | [x /IHa1]]; last by rewrite subst_dmap; exists (ecast U U Dev x).
by exists (ecast U U (esym Dev) x); apply/IHa1; rewrite subst_dmap ecastKv.
Qed.

Lemma evalP@{i j} t e : valid e -> @eval@{i j} t e.
Proof.
elim: t => /= [|a s Cs t_ IHt] in e * => // v; set r := (rec in chop rec e).
suffices{s Cs} v1: valid (chop r e) by apply/Cs.[_].[_]/intro_substP.
elim: a e v => //= [_ IH1 _ IH2 [_ _] [/IH1? /IH2] // | a IHa [A eA] [x /IHa]].
by exists x.
Qed.

Fixpoint all_env@{i j} {A : Type@{j}} {a} : (A -> env@{i j} a) -> env a :=
  match a return (A -> env a) -> env a with
  | Arg _ | CstT => fun T : A -> Type@{j} => forall x, T x
  | CstP => fun P : A -> Prop => forall x, P x
  | Prod a1 a2 => fun e => [pair all_env (dfst \o e), all_env (ndsnd \o e)]
  | Sigma a1 => fun e =>
    let e1 y := all_env (fun x => dsnd (e x) (y x)) in
    [dpair T : Type@{j} := forall x, dfst (e x), e1 : T -> env a1]
  end.

Lemma all_envP@{i j} {A : Type@{j}} {a eA} :
  (forall x : A, valid (eA x)) -> valid (@all_env@{i j} A a eA).
Proof.
elim: a => //= [a1 IHa1 a2 IHa2|a1 IHa1] in eA * => vA.
  by split; [apply/IHa1 | apply/IHa2] => x /=; case: (eA x) (vA x) => e1 e2 [].
by exists (fun x => dfst (vA x)); apply/IHa1=> x; case: (vA x).
Qed.

Variant position := Pos (at_top : bool) (in_forall : bool).
Definition AtTop := Pos true true.
Definition InForall := Pos false true.
Definition InSig := Pos false false.

Record class_of@{i j} (t : term@{i j}) (T : Type@{j}) : Type :=
  Class {class_env :> env@{i j} t; classP : T -> valid class_env}.

Structure genSig@{i j} (p : position) t :=
  GenSig {gen_sig :> wrappedType@{j}; _ : class_of@{i j} t gen_sig}.
Coercion genSig_class@{i j} p t (g : genSig@{i j} p t) :=
  let: GenSig _ Cg := g return class_of t g in Cg.

Structure properGenSig@{i j} t :=
  ProperGenSig {proper_gen_sig :> Type@{j}; _ : class_of@{i j} t proper_gen_sig}.
Coercion properGenSig_class@{i j} t g :=
  let: ProperGenSig _ Cg := g return class_of@{i j} t g in Cg.

Definition nontrivial_gen_sig@{i j} b t (g : properGenSig@{i j} t) :=
  @GenSig (Pos false b) t (wrap1Type g) g.

Fact generic_forallP@{i j} t (A : Type@{j}) (g : A -> genSig@{i j} InForall t) :
  (forall x : A, g x) -> @valid@{i j} t (all_env g).
Proof. by move=> gA; apply/all_envP=> x; apply/classP/gA. Qed.
Definition generic_forall@{i j} b t (A : Type@{j}) g :=
  @GenSig (Pos b true) t (wrap2Type _) (Class (@generic_forallP@{i j} t A g)).

Definition trivial_gen_sig@{i j} (T : Type@{j}) :=
  @GenSig@{i j} InSig ArgTerm (wrap3Type T) (@Class ArgTerm T T id).

Fixpoint label_args@{} a n K : arity * nat :=
  match a with
  | Arg _ => K (Arg n) n.+1 | CstT | CstP => K a n
  | Prod a1 a2 => label_args a1 n (fun b1 n1 => label_args a2 n1 (K \o Prod b1))
  | Sigma a1 => label_args a1 n (K \o Sigma)
  end.

Definition term_ctx@{i j} n := iter n (fun ctx => [ctx: term@{i j}, ctx]) Nil.

Fixpoint args_of_ctx@{i j} n : term_ctx@{i j} n -> nat -> term :=
  if n isn't m.+1 then fun _ _ => ArgTerm else
  fun '(Dpair t e) i => if i isn't j.+1 then t else args_of_ctx e j.

Definition term_of_ctx a n s (Cs : intro a s) (e : term_ctx n) :=
  OpTerm Cs (args_of_ctx e).

Fixpoint gen_env_ctx@{i j} ctx a (args : nat -> term@{i j}) : context@{i} :=
  match a with
  | Arg i => [ctx: ctx / genSig InSig (args i), Nil@{i}]
  | CstT => [ctx: ctx / Type@{j}, Nil@{i}]
  | CstP => [ctx: ctx / Prop, Nil@{i}]
  | Prod a1 a2 => gen_env_ctx ctx a1 args + gen_env_ctx ctx a2 args
  | Sigma a1 => [ctx cT : ctx / Type@{j}, gen_env_ctx (ctx :+ cT) a1 args]
  end.

Fixpoint env_of_ctx@{i j} ctx a args
          : gen_env_ctx@{i j} ctx a args -> ctx -> env a.[args] :=
  match a with
  | Arg _ | CstT | CstP => fun e v => (dfst e).[v]
  | Prod a1 a2 => fun e v => let: Dpair e1 e2 := split_sum e in
    [pair env_of_ctx e1 v, env_of_ctx e2 v]
  | Sigma a1 => fun '(Dpair cA eA) v =>
    let e_ x := env_of_ctx eA (v :+ x) in
    [dpair A : Type@{j} := cA.[v], e_ : _]
  end.

Fixpoint expr_env_of_ctx@{i j} ctx a args
           : gen_env_ctx@{i j} ctx a args -> ctx -> env a :=
  match a with
  | Arg _ => fun e v => gen_sig (dfst e).[v]
  | CstT | CstP => fun e v => (dfst e).[v]
  | Prod a1 a2 => fun e v => let: Dpair e1 e2 := split_sum e in
    [pair expr_env_of_ctx e1 v, expr_env_of_ctx e2 v]
  | Sigma a1 => fun '(Dpair cA eA) v =>
    let e_ x := expr_env_of_ctx eA (v :+ x) in
    [dpair A : Type@{j} := cA.[v], e_ : _]
  end.

Lemma env_of_ctxP@{i j} a args ctx s Cs (e : gen_env_ctx@{i j} ctx a args) v :
    elim@{i j} a s Cs -> wrapped_subst s (expr_env_of_ctx e v) ->
  valid (env_of_ctx e v).
Proof.
rewrite unwrap_subst /=; set e_s := expr_env_of_ctx _ _.
move/(fun e => e.[e_s])/(_ (fun=> _)); apply; apply/abs=> {s Cs}/intro_substP/=.
elim: a => //= [i|a1 IHa1 a2 IHa2|a IHa] in ctx v e e_s *; first exact: classP.
  by case: split_sum @e_s => e1 e2 /= [/IHa1-v1 /IHa2].
by case: e @e_s => A eA /= [x /IHa]; exists x.
Qed.

Definition RectProper@{i j} a0 :=
  let a_n := label_args a0 0 pair in let a := a_n.1 in let n := a_n.2 in
  fun s Cs (Es : elim@{i j} a s Cs) =>
  let t := @term_of_ctx a n s Cs in
  let S e := properGenSig (t e) in
  let gctx e := gen_env_ctx Nil a (args_of_ctx e) in
  let R e := gctx e / S e in
  @abs (term_ctx n) R (fun e => @abs (gctx e) (fun=> S e) (fun ge =>
  let Pack := @ProperGenSig (t e) in
  let PackT (wT : wrappedType) := class_of (t e) wT -> S e in
  let wT := wrapped_subst s (expr_env_of_ctx ge tt) in 
  let PackC := let: WrapType T := wT return PackT wT in Pack T in
  PackC (@Class (t e) wT (env_of_ctx ge tt) (env_of_ctxP Es)))).
Arguments RectProper a0 s {Cs} Es.

Definition generic_prod@{i j} := Eval hnf in
  RectProper@{i j} (Prod ArgT ArgT) (@prod) (@prod_rect).

Definition generic_sig@{i j} := Eval hnf in
   RectProper@{i j} (Sigma CstP) (@sig) (@sig_rect).

Definition generic_dpair@{i j} := Eval hnf in
   let dpair_rect (A : Type@{j}) (T : A -> Type@{j})
                  (G : {dpair x, T x} -> Type@{j}) IH u :=
     let: Dpair x y := u return G u in IH x y in
   RectProper@{i j} (Sigma ArgT) (@dpair) dpair_rect.

Definition generic_sig2@{i j} := Eval hnf in
   @RectProper@{i j} (Sigma (Prod CstP CstP)) (@sig2) (@exist2) (@sig2_rect).

Definition generic_sigT@{i j} := Eval hnf in
   @RectProper@{i j} (Sigma ArgT) (@sigT) (@existT) (@sigT_rect).

Definition generic_sigT2@{i j} := Eval hnf in
   @RectProper@{i j} (Sigma (Prod ArgT ArgT)) (@sigT2) (@existT2) (@sigT2_rect).

End SkolemizeSig.
End SkolemizeSig.

Module Exports.

Import SkolemizeAnd.

Canonical trivial_gen_and.
Canonical nontrivial_gen_and.
Canonical generic_prod2.
Canonical generic_and2.
Canonical generic_and3.
Canonical generic_and4.
Canonical generic_and4.
Canonical trivial_all_and.
Canonical nontrivial_all_and.

Lemma all_and {g E} {ga : genAllAnd false g E} : ga -> eval E g.
Proof. by case: ga => P P_Ev /P_Ev; apply: evalP. Qed.

Import SkolemizeSig.

Canonical trivial_gen_sig.
Canonical nontrivial_gen_sig.
Canonical generic_prod.
Canonical generic_dpair.
Canonical generic_sig.
Canonical generic_sig2.
Canonical generic_sigT.
Canonical generic_sigT2.
Canonical generic_forall.

Lemma all_sig {t} {g : genSig AtTop t} : g -> eval t g.
Proof. by move/classP/evalP. Qed.

End Exports.

End GenericSkolem.
Export GenericSkolem.Exports.

Goal (forall x y, nat * {n & {m | m < n < x} & {m & {p | n < p & p < y} & {p | p * x < m}}}) -> True.
Proof.
move/all_sig=> /=.

 -[f_nat [f_n [f_m1 /= m1P] [f_m2 [f_p1 np1P p1yP]] [f_p2 /= p2P]]].

(*
Variant arg_of {A R} (f : A -> R) : R -> Type := Arg x : arg_of f (f x).
Notation arg_val y := (let: Arg x := y in x).
Arguments Arg {A R f}.

Section LocalProperties.

Context {A1 A2 A3 : Type}.
Context (d1 : mem_pred A1) (d2 : mem_pred A2) (d3 : mem_pred A3).

Definition forall1 P := forall (x : A1), P x : Prop.
Definition forall2 P := forall (x : A1) (y : A2), P x y : Prop.
Definition forall3 P := forall (x : A1) (y : A2) (z : A3), P x y z : Prop.

Definition all1pred := arg_of forall1.
Definition all2pred := arg_of forall2.
Definition all3pred := arg_of forall3.

Definition for1_all x Q : all1pred Q -> Prop := fun '(Arg P) => P x.
Definition for2_all x y Q : all2pred Q -> Prop := fun '(Arg P) => P x y.
Definition for3_all x y z Q : all3pred Q -> Prop := fun '(Arg P) => P x y z.

Definition in1_all Q : all1pred Q -> Prop := fun '(Arg P) =>
  forall x, in_mem x d1 -> P x.

Definition in11_all Q : all2pred Q -> Prop := fun '(Arg P) =>
  forall x y, in_mem x d1 -> in_mem y d2 -> P x y.

Definition in111_all Q : all3pred Q -> Prop := fun '(Arg P) =>
  forall x y z, in_mem x d1 -> in_mem y d2 -> in_mem z d3 -> P x y z.

Lemma all2_and2 {P Q : A1 -> A2 -> Prop} :
  (forall x y, P x y /\ Q x y) -> (forall x y, P x y) /\ (forall x y, Q x y).
Proof. by move=> /(_ _)/all_and2-/all_and2. Qed.

Lemma all3_and2 {P Q : A1 -> A2 -> A3 -> Prop} :
    (forall x y z, P x y z /\ Q x y z) ->
  (forall x y z, P x y z) /\ (forall x y z, Q x y z).
Proof. by move=> /(_ _ _)/all_and2-/all2_and2. Qed.

Lemma all2_and3 {P Q R : A1 -> A2 -> Prop} :
    (forall x y, [/\ P x y, Q x y & R x y]) ->
  [/\ forall x y, P x y, forall x y, Q x y & forall x y, R x y].
Proof. by move=> /(_ _)/all_and3-/all_and3. Qed.

Lemma all3_and3 {P Q R : A1 -> A2 -> A3 -> Prop} :
    (forall x y z, [/\ P x y z, Q x y z & R x y z]) ->
  [/\ forall x y z, P x y z, forall x y z, Q x y z & forall x y z, R x y z].
Proof. by move=> /(_ _ _)/all_and3-/all2_and3. Qed.

End LocalProperties.

Arguments forall1 {A1} P /.
Arguments forall2 {A1 A2} P /.
Arguments forall3 {A1 A2 A3} P /.
Arguments for1_all {A1} x Q P : simpl never.
Arguments for2_all {A1 A2} x y Q P : simpl never.
Arguments for3_all {A1 A2 A3} x y z Q P : simpl never.
Notation "{ 'for' x , Q }" := (for1_all x Q (Arg _))
  (at level 0, format "{ '[' 'for'  x , '/ '  Q ']' }", only printing)
   : type_scope.
Notation "{ 'for' x & y , Q }" := (for2_all x y Q (Arg _))
  (at level 0, format "{ '[' 'for'  x  &  y , '/ '  Q ']' }") : type_scope.
Notation "{ 'for' x & y & z , Q }" := (for3_all x y z Q (Arg _))
 (at level 0, format "{ '[' 'for'  x  &  y  &  z , '/ '  Q ']' }") : type_scope.

Definition in2_all {A1} d1 := @in11_all A1 A1 d1 d1.
Definition in3_all {A1} d1 := @in111_all A1 A1 A1 d1 d1 d1.
Definition in12_all {A1 A2} d1 d2 := @in111_all A1 A2 A2 d1 d2 d2.
Definition in21_all {A1 A2} d1 d2 := @in111_all A1 A1 A2 d1 d1 d2.

Arguments in1_all {A1} d1 Q P : simpl never.
Arguments in2_all {A1} d1 Q P : simpl never.
Arguments in3_all {A1} d1 Q P : simpl never.
Arguments in11_all {A1 A2} d1 d2 Q P : simpl never.
Arguments in12_all {A1 A2} d1 d2 Q P : simpl never.
Arguments in21_all {A1 A2} d1 d2 Q P : simpl never.
Arguments in111_all {A1 A2 A3} d1 d2 d3 Q P : simpl never.

Notation "{ 'in' d1 , Q }" :=
  (in1_all (mem d1) Q (Arg _)) : type_scope.
Notation "{ 'in' d1 & , Q }" :=
  (in2_all (mem d1) Q (Arg _)) : type_scope.
Notation "{ 'in' d1 & & , Q }" :=
  (in3_all (mem d1) Q (Arg _)) : type_scope.
Notation "{ 'in' d1 && , Q }" :=
  (in3_all (mem d1) Q (Arg _)) (only parsing) : type_scope.
Notation "{ 'in' d1 & d2 , Q }" :=
  (in11_all (mem d1) (mem d2) Q (Arg _)) : type_scope.
Notation "{ 'in' d1 & d2 & , Q }" :=
  (in12_all (mem d1) (mem d2) Q (Arg _)) : type_scope.
Notation "{ 'in' d1 & & d2 , Q }" :=
  (in21_all (mem d1) (mem d2) Q (Arg _)) : type_scope.
Notation "{ 'in' d1 && d2 , Q }" :=
  (in21_all (mem d1) (mem d2) Q (Arg _)) (only parsing) : type_scope.
Notation "{ 'in' d1 & d2 & d3 , Q }" :=
  (in111_all (mem d1) (mem d2) (mem d3) Q (Arg _)) : type_scope.

Section PairProperties.

Context {A} (d : mem_pred A).

Definition dup1all2_with Q of @all2pred A A Q := A -> Q.
Definition dup2all1_with Q of @all1pred A Q := A -> A -> Q.

Lemma undup1all2 {Q P} : @dup1all2_with Q P <-> Q.
Proof. by case: Q / P => /= P; split=> allP x //; apply: allP. Qed.

Lemma undup2all1 {Q P} : @dup2all1_with Q P <-> Q.
Proof. by case: Q / P => /= P; split=> allP x //; apply: allP. Qed.

Definition dup1all2_arg Q (P : all2pred Q) :=
  let: Arg P in arg_of _ Q := P return all3pred (dup1all2_with P) in
  Arg (fun=> P).

Lemma undup1all_in3 Q P : in3_all d _ (dup1all2_arg P) <-> in2_all d Q P.
Proof. by case: Q / P => P; split=> [Q x y d1x | Q _ x y _]; apply: (Q x). Qed.

Definition dup2all1_arg Q (P : @all1pred A Q) :=
  let: Arg P in arg_of _ Q := P return all3pred (dup2all1_with P) in
  Arg (fun _ _ => P).

Lemma undup2all_in3 Q P : in3_all d _ (dup2all1_arg P) <-> in1_all d Q P.
Proof.
by case: Q / P => P; split=> [Q x ? | Q _ _ x _ _]; [apply: (Q x x) | apply: Q].
Qed.

Definition pair_all3_with Q1 Q2 : all3pred Q1 -> all3pred Q2 -> Prop :=
  fun '(Arg P1) '(Arg P2) => forall x y z : A, P1 x y z * P2 x y z.

Lemma split_all3 {Q1 Q2 P1 P2} : @pair_all3_with Q1 Q2 P1 P2 <-> Q1 /\ Q2.
Proof.
case: Q1 / P1 => /= P1; case: Q2 / P2 => /= P2.
split=> [Q12 | [Q1 Q2] x y z]; last by split; move: x y z.
by split=> x y z; case: (Q12 x y z).
Qed.

Definition split_all3_arg Q1 Q2 (P1 : all3pred Q1) (P2 : all3pred Q2) :=
  let: Arg P1 in arg_of _ Q1 := P1 return all3pred (pair_all3_with P1 P2) in
  let: Arg P2 in arg_of _ Q2 := P2
    return all3pred (pair_all3_with (Arg P1) P2) in
  Arg (fun x y z : A => P1 x y z * P2 x y z)%type.

Lemma split_all_in3 {Q1 Q2 P1 P2} :
   in3_all d (pair_all3_with P1 P2) (split_all3_arg P1 P2)
  <-> in3_all d Q1 P1 /\ in3_all d Q2 P2.
Proof.
case: Q1 / P1 => P1; case: Q2 / P2 => P2 /=.
split=> [Q | [Q1 Q2]]; [split|] => x y z d_x d_y d_z; try by case: (Q x y z).
by split; move: x y z d_x d_y d_z.
Qed.

End PairProperties.

Arguments dup1all2_with {A} Q P.
Arguments dup2all1_with {A} Q P.
Arguments pair_all3_with {A} Q1 Q2 P1 P2.

Notation dup1all2 Q := (dup1all2_with Q (Arg _)).
Notation dup2all1 Q := (dup2all1_with Q (Arg _)).
Notation pair_all3 Q1 Q2 := (pair_all3_with Q1 Q2 (Arg _) (Arg _)).

*)

Reserved Notation "{ 'for' x & y , P }" (at level 0,
  format "'[hv' { 'for'  x  &  y , '/ '  P } ']'").
Reserved Notation "{ 'for' x & y & z , P }" (at level 0,
  format "'[hv' { 'for'  x  &  y   &  z , '/ '  P } ']'").
Reserved Notation "{ 'in' <= S , P }" (at level 0,
  format "'[hv' { 'in'  <=  S , '/ '  P } ']'").

Definition identify_source T : Type := T.
Definition identify_target T : Type := T.
Variant identical3 {T} x : T -> T -> Prop := Identical3 : @identical3 T x x x.
Structure identify {T} (x y : T) :=
  Identify {common_value :> identify_target T; _ : identical3 x y common_value}.

Canonical trivial_identify {T} (x : identify_source T) :=
  Identify (@Identical3 T x).
Coercion trivial_identify : identify_source >-> identify.

Section MoreLocalProperties.

Context {T1 T2 T3 : Type} {T : predArgType}.
Implicit Type A : {pred T}.

Local Notation "{ 'allA' P }" := (forall A : {pred T}, P A : Prop) (at level 0).
Local Notation "{ 'all2' P }" := (forall x y, P x y : Prop) (at level 0).
Local Notation "{ 'all3' P }" := (forall x y z, P x y z: Prop) (at level 0).
Local Notation ph := (phantom _).

Definition prop_for2 (x : T1) (y : T2) P & ph {all2 P} := P x y.
Definition prop_for3 (x : T1) (y : T2) (z : T3) P & ph {all3 P} := P x y z.
Definition prop_within d P & ph {allA P} := forall A, sub_mem (mem A) d -> P A.

Lemma for2E x y P phP : @prop_for2 x y P phP = P x y. Proof. by []. Qed.
Lemma for3E x y z P phP : @prop_for3 x y z P phP = P x y z. Proof. by []. Qed.

Lemma withinW A P : {allA P} -> prop_within (mem A) (inPhantom {allA P}).
Proof. by move=> allP ? _; apply: allP. Qed.

Lemma withinT P : prop_within (mem T) (inPhantom {allA P}) -> {allA P}.
Proof. by move=> allP A; apply: allP. Qed.

Lemma sub_within d d' P :
  sub_mem d d' -> forall phP, @prop_within d' P phP -> @prop_within d P phP.
Proof. by move=> sdd' phP Pd' A /(_ _ _)/sdd'-/Pd'. Qed.

End MoreLocalProperties.

Notation "{ 'for' x & y , P }" :=
  (prop_for2 x y (inPhantom P)) : type_scope.
Notation "{ 'for' x & y & z , P }" :=
  (prop_for3 x y z (inPhantom P)) : type_scope.
Notation "{ 'in' <= S , P }" :=
  (prop_within (mem S) (inPhantom P)) : type_scope.

(*
Class identical_value {T} (x y : T) := IdenticalValue {}.
Instance duplicate_value {T} x : @identical_value T x x := IdenticalValue x x.
*)

Section PairProperties.

Context {T : Type} (d : mem_pred T).

Local Notation "{ 'all1' P }" := (forall x : T, P x : Prop) (at level 0).
Local Notation "{ 'all2' P }" := (forall x y : T, P x y : Prop) (at level 0).
Local Notation "{ 'all3' P }" := (forall x y z : T, P x y z: Prop) (at level 0).

Structure phantomProp (P : Prop) : Type :=
  PhantomProp {phantom_Prop :> Prop; _ : P = phantom_Prop}.
Canonical PropPhantom P := @PhantomProp P P erefl.
Local Notation ph := phantomProp.
Coercion phantom_of_Prop P phP : phantom Prop P :=
  let: PhantomProp Q defQ := phP in
  let: erefl in _ = P := esym defQ return phantom Prop P in inPhantom Q.

Ltac elimPh phP := (case: phP => phP; case: phP /).

Definition prop_dup_body P (phP : ph {all1 P}) x y :=
  forall u : identify x y, P (common_value u).
Arguments prop_dup_body P phP x y / : clear implicits.
Local Notation prop_dup P phP := (forall x y, prop_dup_body P phP x y).

Definition prop2_dup_body P (phP : ph {all2 P}) x y z :=
  forall u : identify y z, P x (common_value u).
Arguments prop2_dup_body P phP x y z / : clear implicits.
Local Notation prop2_dup P phP := (forall x y z, prop2_dup_body P phP x y z).

Definition prop2_pair_body P Q (phP : ph {all2 P}) (_ : ph {all2 Q}) x y :=
  (P x y * Q x y)%type.
Arguments prop2_pair_body P Q phP phQ x y / : clear implicits.
Local Notation prop2_pair P Q phP phQ :=
  (forall x y, prop2_pair_body P Q phP phQ x y).

Definition prop3_pair_body P Q (phP : ph {all3 P}) (_ : ph {all3 Q}) x y z :=
  (P x y z * Q x y z)%type.
Arguments prop3_pair_body P Q phP phQ x y z / : clear implicits.
Local Notation prop3_pair P Q phP phQ :=
  (forall x y z, prop3_pair_body P Q phP phQ x y z).

Lemma prop_dupE P phP : prop_dup P phP <-> phP.
Proof. by elimPh phP; split=> P_ /= *; apply: P_. Qed.

Lemma prop_in2_dup P phP :
  prop_in2 d (inPhantom (prop_dup P phP)) <-> prop_in1 d phP.
Proof. by elimPh phP; split=> Pd x * => [|[_ []]]; apply Pd. Qed.

Lemma prop2_dupE P phP : prop2_dup P phP <-> phP.
Proof. by elimPh phP; split=> P_ /= *; apply: P_. Qed.

Lemma prop_in3_dup P phP :
  prop_in3 d (inPhantom (prop2_dup P phP)) <-> prop_in2 d phP.
Proof. by elimPh phP; split=> Pd x * => [|[_ []]]; apply Pd. Qed.

Lemma prop2_pairE P Q phP phQ : prop2_pair P Q phP phQ <-> phP /\ phQ.
Proof. by elimPh phP; elimPh phQ; split=> [/all_and|] []. Qed.

Lemma prop3_pairE P Q phP phQ : prop3_pair P Q phP phQ <-> phP /\ phQ.
Proof. by elimPh phP; elimPh phQ; split=> [/all_and|] []. Qed.

Lemma prop_in2_pair P Q phP phQ :
       prop_in2 d (inPhantom (prop2_pair P Q phP phQ))
   <-> prop_in2 d phP /\ prop_in2 d phQ.
Proof. by elimPh phP; elimPh phQ; split=> [/all_and|] []; split; auto. Qed.

Lemma prop_in3_pair P Q phP phQ :
       prop_in3 d (inPhantom (prop3_pair P Q phP phQ))
   <-> prop_in3 d phP /\ prop_in3 d phQ.
Proof. by elimPh phP; elimPh phQ; split=> [/all_and|] []; split; auto. Qed.

End PairProperties.

Notation prop_dup Q :=
  (forall x y, prop_dup_body (PropPhantom Q) x y).
Notation prop2_dup Q :=
  (forall x y z, prop2_dup_body (PropPhantom Q) x y z).
Notation prop_dup2 Q := (prop2_dup (prop_dup Q)).
Notation prop2_pair Q1 Q2 :=
  (forall x y, prop2_pair_body (PropPhantom Q1) (PropPhantom Q2)).
Notation prop3_pair Q1 Q2 :=
  (forall x y z, prop3_pair_body (PropPhantom Q1) (PropPhantom Q2) x y z).

Section RelDefs.

Variables (T : Type) (R : rel T).
Implicit Types (x y z : T) (A C : {pred T}).

Definition maximal z := forall x, R z x -> R x z.

Definition minimal z := forall x, R x z -> R z x.

Definition upper_bound A z := {in A, forall x, R x z}.

Definition lower_bound A z := {in A, forall x, R z x}.

Definition preorder := prop3_pair (prop_dup2 (reflexive R)) (transitive R).

Definition partial_order := prop3_pair preorder (prop2_dup (antisymmetric R)).

Definition total_order := prop3_pair partial_order (prop2_dup (total R)).

Definition nonempty A := exists x, x \in A.

Definition minimum_of A z := z \in A /\ lower_bound A z.

Definition maximum_of A z := z \in A /\ upper_bound A z.

Definition well_order := forall A, nonempty A -> exists! z, minimum_of A z.

Definition chain C := {in C & &, total_order}.

Definition wo_chain C := {in <= C, well_order}.

Lemma preorderE : preorder <-> reflexive R /\ transitive R.
Proof. by rewrite [preorder]prop3_pairE /= prop2_dupE /= prop_dupE. Qed.

Lemma preorder_in A :
  {in A & &, preorder} <-> {in A, reflexive R} /\ {in A & &, transitive R}.
Proof. by rewrite prop_in3_pair prop_in3_dup prop_in2_dup. Qed.

Lemma partial_orderE :
  partial_order <-> [/\ reflexive R, transitive R & antisymmetric R].
Proof.
by rewrite [partial_order]prop3_pairE /= preorderE prop2_dupE; split=> [[]|] [].
Qed.

Lemma partial_order_in A :
    {in A & &, partial_order}
  <-> [/\ {in A, reflexive R}, {in A & &, transitive R}
        & {in A &, antisymmetric R}].
Proof. by rewrite prop_in3_pair preorder_in prop_in3_dup; split=> [[]|] []. Qed.

Lemma total_orderE :
  total_order <-> [/\ reflexive R, transitive R, antisymmetric R & total R].
Proof.
rewrite [total_order]prop3_pairE /= partial_orderE prop2_dupE /=.
by split=> [[]|] [].
Qed.

Lemma total_order_in A :
    {in A & &, total_order}
  <-> [/\ {in A, reflexive R}, {in A & &, transitive R},
          {in A &, antisymmetric R} & {in A &, total R}].
Proof.
by rewrite prop_in3_pair partial_order_in prop_in3_dup; split=> [[]|] [].
Qed.

Lemma antisymmetric_wo_chain C :
    {in C &, antisymmetric R} ->
    {in <= C, forall A, nonempty A -> exists z, minimum_of A z} ->
  wo_chain C.
Proof.
move=> Ranti Rwo A sAC /Rwo[//|z [Az lbAz]]; exists z; split=> // x [Ax lbAx].
by apply: Ranti; rewrite ?sAC ?lbAx ?lbAz.
Qed.

Lemma antisymmetric_well_order :
    antisymmetric R -> (forall A, nonempty A -> exists z, minimum_of A z) ->
  well_order.
Proof.
by move=> Ranti /withinW/(antisymmetric_wo_chain (in2W Ranti))/withinT.
Qed.

End RelDefs.

Lemma wo_chainW (T : eqType) R C : @wo_chain T R C -> chain R C.
Proof.
have ne_cons x s: nonempty [mem x :: s : seq T] by exists x; apply: mem_head.
have all_mem s: all [mem s : seq T] s by apply/allP.
move=> Rwo; have Rtotal: {in C &, total R}.
  move=> x y Cx Cy; have /Rwo[] := ne_cons x [::y]; first exact/allP/and3P.
  by move=> z [] [] /or3P[] // /eqP-> /allP/and3P[] => [_|] ->; rewrite ?orbT.
have Rxx: {in C, reflexive R} by move=> x Cx; rewrite -[R x x]orbb Rtotal.
have Ranti: {in C &, antisymmetric R}.
  move=> x y Cx Cy; have /Rwo[] := ne_cons x [::y]; first exact/allP/and3P.
  move=> z [_ Uz] /andP[Rxy Ryx]; have /and3P[xy_x xy_y _] := all_mem [:: x; y].
  by rewrite -(Uz x) ?(Uz y); split=> //; apply/allP; rewrite /= (Rxy, Ryx) Rxx.
suffices Rtr: {in C & &, transitive R} by apply/total_order_in.
move=> y x z Cy Cx Cz Rxy Ryz; pose A := [mem [:: x; y; z]].
have /and4P[Ax Ay Az _]: all A _ := all_mem _.
have [] := Rwo A; first 1 [exact/allP/and4P | apply: ne_cons].
move=> _ [[/or4P[]// /eqP-> /allP/and4P[// Ryx Rzy _ _]] _].
  by rewrite (Ranti x y) ?Rxy.
by rewrite (Ranti z y) ?Rzy.
Qed.

Lemma well_order_total (T : eqType) (R : rel T) : well_order R -> total_order R.
Proof. by move/withinW/wo_chainW/in3T. Qed.

(* Alternatively, one can deduce the localized variant from the global one.

Lemma well_order_total (T : eqType) (R : rel T) : well_order R -> total_order R.
Proof. 
have inU1l x (A : {pred T}): x \in xpredU1 x A by apply/predU1l.
have inU12r (x y : T): y \in xpred2 x y by apply/predU1r/eqxx.
have exU1 (x : T) A: nonempty (xpredU1 x A) by exists x; apply: inU1l.
move=> Rwo; have Rtotal: total R.
  move=> x y; have /Rwo[z [[/pred2P/=xyz]]] := exU1 x (pred1 y).
  by case: xyz orbC => [-> _ | -> ->] ->.
have Rxx: reflexive R by move=> x; have:= Rtotal x x; rewrite orbb.
have Ranti: antisymmetric R.
  move=> x y /andP[Rxy Ryx]; have /Rwo[z [_ Uz]] := exU1 x (pred1 y).
  by transitivity z; first apply/esym; apply/Uz; split=> [|_ /pred2P[]->] /=.
suffices Rtr: transitive R by apply/total_orderE.
move=> y x z Rxy Ryz; pose A := pred3 x y z.
have [Ax Ay Az]: [/\ A x, A y & A z] by rewrite /= !eqxx !orbT.
have /Rwo[t [[At minAt] _]]: exists t, A t by exists x.
case/predU1P: At => [-> -> //| /pred2P[]->] in minAt *.
  by rewrite (Ranti x y) // Rxy minAt.
by rewrite (Ranti z y) // Ryz minAt.
Qed.

Lemma well_order_total_in (T : eqType) (R : rel T) (C : {pred T}) :
  {in <= C, well_order R} -> {in C & &, total_order R}.
Proof.
move=> Rwo; pose T' := {x | x \in C}; pose R' := relpre (val : T' -> T) R.
without loss u0: / T' by move=> IH x y z Cx; apply: IH (Cx); exists x.
have defR: {in C &, R =2 relpre (insubd u0) R'}.
  by move=> x y Cx Cy /=; rewrite !insubdK.
suffices /total_orderE[R'xx R'tr R'anti R'tot]: total_order R'.
  apply/total_order_in; split=> [x Cx | y x z Cy Cx Cz | x y Cx Cy | x y Cx Cy];
    rewrite !defR //; [apply: R'xx | apply: R'tr | | apply: R'tot].
  by move/R'anti/(congr1 val); rewrite !insubdK.
apply/well_order_total=> A neA; pose B := [pred x in C | insubd u0 x \in A].
have sAB u: u \in A -> val u \in B by rewrite inE (valP u) valKd.
have memB x: x \in B -> exists2 u, u \in A & x = val u.
  by case/andP=> Cx Ax; exists (insubd u0 x); rewrite ?insubdK.
have /Rwo[? /andP[]//|_ [[/memB[w Aw ->] minBw] Uw]]: nonempty B.
  by case: neA => u /sAB-Bu; exists (val u).
exists w; do 2?[split] => // [u Au | v [Av minAv]]; first exact/minBw/sAB.
by apply/val_inj/Uw; split=> [|_ /memB[u Au ->]]; [apply/sAB | apply/minAv].
Qed.

end alternative *)

Section Zorn.

Class classical_logic := ClassicalLogic {
  functional_extensionality_dep A B f g :
    (forall x : A, f x = g x :> B x) -> f = g;
  propositional_extensionality P Q :
    P <-> Q -> P = Q;
  constructive_indefinite_description A P :
    (exists x : A, P x) -> {x : A | P x}
}.

Context `{classical_logic_axioms : classical_logic}.

Notation DFEXT := (@functional_extensionality_dep _ _ _).
Definition exists_witness {A} := @constructive_indefinite_description _ A.
Notation EXW := exists_witness.

Ltac eqProp := apply: propositional_extensionality; split.

Lemma function_extensionality {A B} (f g : A -> B) : f =1 g -> f = g.
Proof. exact: DFEXT. Qed.
Notation FEXT := function_extensionality.

Lemma pred_extensionality {T} (A B : {pred T}) : A =i B -> A = B.
Proof. exact: FEXT. Qed.
Notation pEXT := pred_extensionality.

Lemma generic_forall_extensionality {A} {S : forallSort A} {P Q : A -> S} :
  P =1 Q -> Forall P = Forall Q.
Proof. by move/FEXT->. Qed.
Notation AEXT := generic_forall_extensionality.

Lemma Pred_extensionality {T} P Q : (forall x : T, P x <-> Q x) -> P = Q.
Proof. by move=> eqPQ; apply/FEXT=> x; eqProp=> /eqPQ. Qed.
Notation PEXT := Pred_extensionality.

Lemma PropT (P : Prop) : P -> P = True. Proof. by move=> Psat; eqProp. Qed.
Lemma PropF P : ~ P -> P = False. Proof. by move=> Punsat; eqProp. Qed.

Lemma proof_irrelevance (P : Prop) (Pprf1 Pprf2 : P) : Pprf1 = Pprf2.
Proof. by move: (Pprf1) Pprf2; rewrite (PropT Pprf1) => -[] []. Qed.

(* An short-scale reflection proof of Diaconescu's theorem. *)
(* Uses only PROPEXT and CEPS. *)
Theorem Diaconescu_decidability P : {P} + {~ P}.
Proof.
pose R b := if b then (True, P) else (P, True).
pose inR Rb c : Prop := if c then Rb.1 else Rb.2.
have inR_nonempty b: exists c, inR (R b) c by exists b; case b.
pose f b := EXW (inR_nonempty b).
have [fTF | not_fTF] := boolP (sval (f true) ==> sval (f false)).
  by left; do 2![case: (f _) => -[] //=] in fTF *.
right=> Ptrue; case/negP: not_fTF; apply/implyP.
rewrite /f; do 2!move: (inR_nonempty _); rewrite /R.
by rewrite (PropT Ptrue) => exT exF; rewrite (proof_irrelevance exT exF).
Qed.

Definition decide P : bool := Diaconescu_decidability P.
Lemma decP P : reflect P (decide P). Proof. exact: sumboolP. Qed.

Lemma rwP P b : reflect P b -> P = b.
Proof. by move/rwP/propositional_extensionality. Qed.

Lemma decE P : decide P = P :> Prop. Proof. exact/esym/rwP/decP. Qed.

Notation "[ 'dec' x | P ]" := (fun x => decide P)
  (at level 0, x ident, P at level 200,
   format "[ 'dec'  x  |  P ]") : form_scope.
Notation "[ 'dec' x : T | P ]" := (fun x : T => decide P)
  (at level 0, x ident, P, T at level 200, only parsing) : form_scope.
Notation "[ 'dec' x | P , y 'in' A ]" := [dec x | exists2 y, y \in A & P]
  (at level 0, x ident, y ident, A, P at level 200,
   format "[ 'dec'  x  |  P , y  'in'  A ]") : form_scope.
Notation "[ 'dec' x : T | P , y 'in' A ]" :=
    [dec x : T | exists2 y, y \in A & P]
  (at level 0, x ident, y ident, T, A, P at level 200,
   only parsing) : form_scope.
Notation "[ 'union' B , x 'in' A ]" := [dec y | y \in B, x in A]
  (at level 0, x ident, A, B at level 200,
   format "[ 'union'  B ,  x  'in'  A ]") : form_scope.

(* Boolean evaluation in Prop.                                                *)

Variant BoolProp : Prop -> Type :=
 | TrueProp : BoolProp True
 | FalseProp : BoolProp False.

Lemma PropB P : BoolProp P.
Proof. by case: (decP P) => [/PropT-> | /PropF->]; [left | right]. Qed.

Lemma notB : ((~ True) = False) * ((~ False) = True).
Proof. by rewrite /not; split; eqProp. Qed.

Lemma andB : left_id True and * right_id True and
          * (left_zero False and * right_zero False and * idempotent and).
Proof. by do ![split] => /PropB[]; eqProp=> // -[]. Qed.

Lemma orB : left_id False or * right_id False or
          * (left_zero True or * right_zero True or * idempotent or).
Proof. do ![split] => /PropB[]; eqProp=> -[] //; by [left | right]. Qed.

Lemma implyB : let imply (P Q : Prop) :=  P -> Q in
    (imply False =1 fun=> True) * (imply^~ False =1 not)
  * (left_id True imply * right_zero True imply * self_inverse True imply).
Proof. by do ![split] => /PropB[]; eqProp=> //; apply. Qed.

Lemma decide_or P Q : P \/ Q -> {P} + {Q}.
Proof. by case/PropB: P; [left | rewrite orB; right]. Qed.

(* Boolean algebra in Prop                                                   *)

Lemma notK P : (~ ~ P) = P. Proof. by case/PropB: P; rewrite !notB. Qed.

Lemma not_inj : injective not. Proof. exact: inv_inj notK. Qed.

Lemma andC : commutative and.
Proof. by move=> P Q; eqProp=> -[]. Qed.

Lemma andA : associative and.
Proof. by move=> P Q R; eqProp=> -[] => [?|] []. Qed.

Lemma andCA : left_commutative and.
Proof. by move=> P Q R; rewrite !andA (andC P). Qed.

Lemma andAC : right_commutative and.
Proof. by move=> P Q R; rewrite -!andA (andC Q). Qed.

Lemma andACA : interchange and and.
Proof. by move=> P Q R S; rewrite !andA (andAC P). Qed.

Lemma orNp P Q : (~ P \/ Q) = (P -> Q).
Proof. by case/PropB: P; rewrite notB orB implyB. Qed.

Lemma implyNp P Q : (~ P -> Q : Prop) = (P \/ Q).
Proof. by rewrite -orNp notK. Qed.

Lemma implypN (P Q : Prop) : (P -> ~ Q) = ~ (P /\ Q).
Proof. by case/PropB: P; rewrite implyB andB ?notB. Qed.

Lemma orNN P Q : (~ P \/ ~ Q) = (~ (P /\ Q)).
Proof. by rewrite orNp implypN. Qed.

Lemma andNN P Q : (~ P /\ ~ Q) = (~ (P \/ Q)).
Proof. by rewrite -[LHS]notK -orNN !notK. Qed.

Lemma orC : commutative or.
Proof. by move=> P Q; apply/not_inj; rewrite -!andNN andC. Qed.

Lemma orpN P Q : (P \/ ~ Q) = (Q -> P). Proof. by rewrite orC orNp. Qed.

Lemma implyNN P Q : (~ P -> ~ Q) = (Q -> P).
Proof. by rewrite implyNp orpN. Qed.

Lemma orA : associative or.
Proof. by move=> P Q R; apply/not_inj; rewrite -!andNN andA. Qed.

Lemma orCA : left_commutative or.
Proof. by move=> P Q R; rewrite !orA (orC P). Qed.

Lemma orAC : right_commutative or.
Proof. by move=> P Q R; rewrite -!orA (orC Q). Qed.

Lemma orACA : interchange or or.
Proof. by move=> P Q R S; rewrite !orA (orAC P). Qed.

Lemma or_andr : right_distributive or and.
Proof. by case/PropB=> Q R; rewrite !orB ?andB. Qed.

Lemma or_andl : left_distributive or and.
Proof. by move=> P Q R; rewrite -!(orC R) or_andr. Qed.

Lemma and_orr : right_distributive and or.
Proof. by move=> P Q R; apply/not_inj; rewrite -!(orNN, andNN) or_andr. Qed.

Lemma and_orl : left_distributive and or.
Proof. by move=> P Q R; apply/not_inj; rewrite -!(orNN, andNN) or_andl. Qed.

(******************************************************************************)
(* Derived connectives expansion.                                             *)
(******************************************************************************)

Lemma and3E P Q R : [/\ P, Q & R] = (P /\ Q /\ R).
Proof. by eqProp=> [[] | [? []]]. Qed.

Lemma and4E P Q R S : [/\ P, Q, R & S] = (P /\ Q /\ R /\ S).
Proof. by eqProp=> [[] | [? [? []]]]. Qed.

Lemma and5E P Q R S T : [/\ P, Q, R, S & T] = (P /\ Q /\ R /\ S /\ T).
Proof. by eqProp=> [[] | [? [? [? []]]]]. Qed.

Lemma or3E P Q R : [\/ P, Q | R] = (P \/ Q \/ R).
Proof. by rewrite -(decE P) -(decE Q) -(decE R) (rwP or3P) -2!(rwP orP). Qed.

Lemma or4E P Q R S : [\/ P, Q, R | S] = (P \/ Q \/ R \/ S).
Proof.
by rewrite -(decE P) -(decE Q) -(decE R) -(decE S) (rwP or4P) -3!(rwP orP).
Qed.

Lemma exists2E A P Q : (exists2 x : A, P x & Q x) = (exists x, P x /\ Q x).
Proof. by eqProp=> -[x]; last case; exists x. Qed.

Lemma inhabitedE T: inhabited T = exists x : T, True.
Proof. by eqProp; case. Qed.

Definition oepsilon {T} P :=
  if decP (exists x : T, P x) isn't ReflectT Psat then None else
  Some (sval (exists_witness Psat)).

Variant oepsilon_spec {T} (P : T -> Prop) : option T -> Type :=
 | SomeEpsilon x of P x : oepsilon_spec P (Some x)
 | NoEpsilon of (forall x, ~ P x) : oepsilon_spec P None.
Lemma oepsilonP {T} P : @oepsilon_spec T P (oepsilon P).
Proof.
rewrite /oepsilon; case: decP => [Psat | noP]; first by left; case: EXW.
by right=> x Px; case: noP; exists x.
Qed.

Lemma exists2_witness {T} P Q :
  (exists2 x, P x & Q x) -> {x : T | P x & Q x}.
Proof. by rewrite exists2E=> /EXW[x []]; exists x. Qed.
Notation EX2W := exists2_witness.

Lemma inhabited_witness T: inhabited T -> T.
Proof. by rewrite inhabitedE => /EXW[]. Qed.

(******************************************************************************)
(*   A set of tools (tactics, views, and rewrite rules) to facilitate the     *)
(* handling of classical negation. The core functionality of these tools is   *)
(* implemented by three sets of canonical structures that provide for the     *)
(* simplification of negation statements (e.g., using de Morgan laws), the    *)
(* conversion from constructive statements in Type to purely logical ones in  *)
(* Prop (equivalently, expansion rules for the statement inhabited T), and    *)
(* conversely extraction of constructive contents from logical statements.    *)
(*   Except for bool predicates and operators, all definitions are treated    *)
(* transparently when matching statements for either simplification or        *)
(* conversion; this is achieved by using the wrapper telescope pattern, first *)
(* delegating the matching of specific logical connectives, predicates, or    *)
(* type constructors to an auxiliary structure that FAILS to match unknown    *)
(* operators, thus triggers the expansion of defined constants. If this       *)
(* ultimately fails then the wrapper is expanded, and the primary structure   *)
(* instance for the expanded wrapper provides an alternative default rule:    *)
(* not simplifying ~ P, not expanding inhabited T, or not extracting any      *)
(* contents from a proposition P, respectively.                               *)
(*   Additional rules, for intermediate wrapper instances, are used to handle *)
(* forall statements (for which canonical instances are not yet supported),   *)
(* as well as addiitonal simplifications, such as inhabited P = P :> Prop.    *)
(*   Finally various tertiary structures are used to match deeper patterns,   *)
(* such as bounded forall statements of the form forall x, P x -> Q x, or     *)
(* inequalites x != y (i.e., is_true (~~ (x == y))). As mentioned above,      *)
(* tertiary rules for bool subexpressions do not try to expand definitions,   *)
(* as this would lead to the undesireable expansion of some standard          *)
(* definitions. This is simply achieved by NOT using the wrapper telescope    *)
(* pattern, and just having a default instance alongside those for specific   *)
(* predicates and connectives.                                                *)
(******************************************************************************)

(******************************************************************************)
(* The negatedProp structure provides simplification of the Prop negation     *)
(* (~ _) for standard connectives and predicates. The instances below cover   *)
(* the pervasive and ssrbool Prop connectives, decidable equality, as well as *)
(* bool propositions (i.e., the is_true predicate), together with a few bool  *)
(* connectives and predicates: negation ~~, equality ==, and nat <= and <.    *)
(* Others can be added (e.g., Order.le/lt) by declaring appropriate instances *)
(* of bool_negation and bool_affirmation, while other Prop connectives and    *)
(* predicates can be added by declaring instances of proper_negatedProp.      *)
(******************************************************************************)

(* The implementation follows the wrapper telescope pattern outlined above:   *)
(* negatedProp instances match on the wrappedProp wrapper to try three        *)
(* generic matching rules, in sucession:                                      *)
(*   Rule 1: match a specific connective or predicate with an instance of the *)
(*           properNegatedProp secondary structure, expanding definitions     *)
(*           if needed, but failing if no proper match is found.              *)
(*   Rule 2: match a forall statement (including (T : Type) -> P statements). *)
(*   Rule 3: match any Prop but return the trivial simplification.            *)
(* The simplified proposition is returned as a projection parameter nP rather *)
(* than a Structure member, so that applying the corresponding views or       *)
(* rewrite rules doesn't expose the inferred structures; properNegatedProp    *)
(* does similarly. Also, negatedProp similarly returns a 'trivial' bool flag  *)
(* that is set when Rule 3 is used, but this is actually used in the reverse  *)
(* direction: views notP and rewrite rule notE force trivial := false, thus   *)
(* excluding trivial instances.                                               *)

Structure negatedProp (trivial : bool) nP :=
  NegatedProp {negated_Prop :> wrappedProp; _ : (~ negated_Prop) = nP}.

Structure properNegatedProp nP := ProperNegatedProp {
  proper_negated_Prop :> Prop; _ : (~ proper_negated_Prop) = nP}.

Local Notation nProp t nP P := (unwrap_Prop (@negated_Prop t nP P)).
Local Notation nPred t nP P x := (nProp t (nP x) (P x)).
Local Notation pnProp nP P := (@proper_negated_Prop nP P).

(* User views and rewrite rules. The plain versions (notP, notE and notI) do  *)
(* not match trivial instances; lax_XXX versions allow them. In addition,     *)
(* the negation introduction rewrite rule notI does not match forall or ->    *)
(* statements - lax_notI must be used for these.                              *)

Lemma lax_notE {t nP} P : (~ nProp t nP P) = nP. Proof. by case: P. Qed.
Lemma lax_notP {t nP P} : ~ nProp t nP P -> nP. Proof. by rewrite lax_notE. Qed.
Definition lax_notI {t nP} P : nProp t nP P = (~ nP) := canRL notK (lax_notE P).

Definition notE {nP} P : (~ nProp false nP P) = nP := lax_notE P.
Definition notP {nP P} := MoveView (@lax_notP false nP P).

Fact proper_nPropP nP P : (~ pnProp nP P) = nP. Proof. by case: P. Qed.
Definition notI {nP} P : pnProp nP P = ~ nP := canRL notK (proper_nPropP P).

(* Rule 1: proper negation simplification, delegated to properNegatedProp. *)
Canonical proper_nProp nP P :=
  @NegatedProp false nP (wrap1Prop (pnProp nP P)) (proper_nPropP P).

(* Rule 2: forall_nProp is defined below as it uses exists_nProp. *)

(* Rule 3: trivial negation. *)
Canonical trivial_nProp P := @NegatedProp true (~ P) (wrap3Prop P) erefl.

(* properNegatedProp instances. *)

Canonical True_nProp := @ProperNegatedProp False True notB.1.
Canonical False_nProp := @ProperNegatedProp True False notB.2.
Canonical not_nProp P := @ProperNegatedProp P (~ P) (notK P).

Fact and_nPropP P tQ nQ Q : (~ (P /\ nProp tQ nQ Q)) = (P -> nQ).
Proof. by rewrite -implypN lax_notE. Qed.
Canonical and_nProp P tQ nQ Q :=
  ProperNegatedProp (@and_nPropP P tQ nQ Q).

Fact and3_nPropP P Q tR nR R : (~ [/\ P, Q & nProp tR nR R]) = (P -> Q -> nR). 
Proof. by hnf; rewrite and3E notE. Qed.
Canonical and3_nProp P Q tR nR R :=
  ProperNegatedProp (@and3_nPropP P Q tR nR R).

Fact and4_nPropP P Q R tS nS S :
  (~ [/\ P, Q, R & nProp tS nS S]) = (P -> Q -> R -> nS). 
Proof. by hnf; rewrite and4E notE. Qed.
Canonical and4_nProp P Q R tS nS S :=
  ProperNegatedProp (@and4_nPropP P Q R tS nS S).

Fact and5_nPropP P Q R S tT nT T :
  (~ [/\ P, Q, R, S & nProp tT nT T]) = (P -> Q -> R -> S -> nT). 
Proof. by hnf; rewrite and5E notE. Qed.
Canonical and5_nProp P Q R S tT nT T :=
  ProperNegatedProp (@and5_nPropP P Q R S tT nT T).

Fact or_nPropP tP nP P tQ nQ Q :
  (~ (nProp tP nP P \/ nProp tQ nQ Q)) = (nP /\ nQ).
Proof. by rewrite -andNN !lax_notE. Qed.
Canonical or_nProp tP nP P tQ nQ Q :=
  ProperNegatedProp (@or_nPropP tP nP P tQ nQ Q).

Fact or3_nPropP tP nP P tQ nQ Q tR nR R :
  (~ [\/ nProp tP nP P, nProp tQ nQ Q | nProp tR nR R]) = [/\ nP, nQ & nR]. 
Proof. by rewrite or3E notE and3E. Qed.
Canonical or3_nProp tP nP P tQ nQ Q tR nR R :=
  ProperNegatedProp (@or3_nPropP tP nP P tQ nQ Q tR nR R).

Fact or4_nPropP tP nP P tQ nQ Q tR nR R tS nS S :
  (~ [\/ nProp tP nP P, nProp tQ nQ Q, nProp tR nR R | nProp tS nS S])
     = [/\ nP, nQ, nR & nS]. 
Proof. by rewrite or4E notE and4E. Qed.
Canonical or4_nProp tP nP P tQ nQ Q tR nR R tS nS S :=
  ProperNegatedProp (@or4_nPropP tP nP P tQ nQ Q tR nR R tS nS S).

(*   The andRHS tertiary structure used to simplify (~ (P -> False)) to P,    *)
(* both here for the imply_nProp instance and for bounded_forall_nProp below. *)
(* Because the andRHS instances match the Prop RETURNED by negatedProp they   *)
(* do not need to expand definitions, hence do not need to use the wrapper    *)
(* telescope pattern.                                         *)

Notation and_def binary P Q PQ := (PQ = if binary then P /\ Q else Q)%type.
Structure andRHS binary P Q PQ :=
  AndRHS {and_RHS :> Prop; _ : (P /\ and_RHS) = PQ; _ : and_def binary P Q PQ}.
Canonical unary_and_rhs P := @AndRHS false P P P True (andB.1.2 P) erefl.
Canonical binary_and_rhs P Q := @AndRHS true P Q (P /\ Q) Q erefl erefl.

Fact imply_nPropP b P nQ PnQ tR (nR : andRHS b P nQ PnQ) R :
  (~ (P -> nProp tR nR R)) = PnQ.
Proof. by rewrite -orNp {R}lax_notE; case: nR. Qed.
Canonical imply_nProp b P nQ PnQ tR nR R :=
  ProperNegatedProp (@imply_nPropP b P nQ PnQ tR nR R).

Fact exists_nPropP A tP nP P :
  (~ exists x : A, nPred tP nP P x) = (forall x : A, nP x).
Proof.
eqProp=> [nEP x | AnP [x]]; last by rewrite -/(~ _) lax_notE.
by rewrite -(lax_notE (P x)) => Px; case: nEP; exists x.
Qed.
Canonical exists_nProp A tP nP P :=
  ProperNegatedProp (@exists_nPropP A tP nP P).

Fact exists2_nPropP A P tQ nQ Q :
  (~ exists2 x : A, P x & nPred tQ nQ Q x) = (forall x : A, P x -> nQ x).
Proof. by rewrite exists2E notE. Qed.
Canonical exists2_nProp A P tQ nQ Q :=
  ProperNegatedProp (@exists2_nPropP A P tQ nQ Q).

Fact inhabited_nPropP T : (~ inhabited T) = (T -> False).
Proof. by rewrite inhabitedE notE. Qed.
Canonical inhabited_nProp T := ProperNegatedProp (inhabited_nPropP T).

(* Rule 2: forall negation, including (T : Type) -> P statements.             *)
(*   We use tertiary structures to recognize bounded foralls and simplify,    *)
(* e.g., ~ forall x, P -> Q to exists2 x, P & ~ Q, or even exists x, P when   *)
(* Q :=  False (as above for imply).                                          *)
(*   As forall_body_nProp and forall_body_proper_nProp are telescopes   *)
(* over negatedProp and properNegatedProp, respectively, their instances *)
(* match instances declared above without the need to expand definitions,     *)
(* hence do not need to use the wrapper telescope idiom.                      *)

Structure negatedForallBody bounded P nQ tR nR := NegatedForallBody {
  negated_forall_body :> negatedProp tR nR; _ : and_def bounded P nQ nR}.
Structure properNegatedForallBody b P nQ nR := ProperNegatedForallBody {
  proper_negated_forall_body :> properNegatedProp nR; _ : and_def b P nQ nR}.
Notation nBody b P nQ t nR x := (negatedForallBody b (P x) (nQ x) t (nR x)).

(* The explicit argument to fun_if is a workaround for a bug in the Coq       *)
(* unification code that prevents default instances from ever matching match  *)
(* constructs. Furthermore rewriting with ifE would not work here, because    *)
(* the if_expr definition would be expanded by the eta expansion needed to    *)
(* match the exists_nProp rule.                                            *)
Fact forall_nPropP A b P nQ tR nR (R : forall x, nBody b P nQ tR nR x) :
  (~ forall x : A, R x) = if b then exists2 x, P x & nQ x else exists x, nQ x.
Proof.
rewrite exists2E -(fun_if (fun P => exists x, idfun P x)) notI /=; congr not.
by apply/AEXT=> x; rewrite if_arg lax_notI; case: (R x) => _ <-.
Qed.
Canonical forall_nProp A b P nQ tR nR (R : forall x, nBody b P nQ tR nR x) :=
  @NegatedProp false _ (wrap2Prop (forall x : A, R x)) (forall_nPropP R).

Fact proper_nBodyP b P nQ nR :
  properNegatedForallBody b P nQ nR -> and_def b P nQ nR.
Proof. by case. Qed.
Canonical proper_nBody b P nQ nR R :=
  let def_nR := @proper_nBodyP b P nQ nR R in
  @NegatedForallBody b P nQ false nR (proper_nProp R) def_nR.
Canonical nonproper_nBody tP nP P :=
  @NegatedForallBody false True nP tP nP P erefl.

Fact andRHS_def b P Q PQ : andRHS b P Q PQ -> and_def b P Q PQ.
Proof. by case. Qed.
Canonical bounded_nBody b P nQ PnQ tR nR R :=
  ProperNegatedForallBody (@imply_nProp b P nQ PnQ tR nR R) (andRHS_def nR).
Canonical unbounded_nBody nQ Q :=
  @ProperNegatedForallBody false True nQ nQ Q erefl.

(*    The properNegatedProp instance that handles boolean statements. We use  *)
(* two tertiary structures to handle positive and negative boolean statements *)
(* so that the contra tactic below will mostly subsume the collection of      *)
(* contraXX lemmas in ssrbool and eqtype.                                     *)
(*    We only match manifest ~~ connectives, the true and false constants,    *)
(* and the ==, <=%N, and <%N predicates. In particular we do not use de       *)
(* Morgan laws to push boolean negation into connectives, as we did above for *)
(* Prop connectives. It will be up to the user to use rewriting to put the    *)
(* negated statement in its desired shape.                                    *)

Structure negatedBool nP :=
  NegatedBool {negated_bool :> bool; _ : (~ negated_bool) = nP}.
Structure positedBool P :=
  PositedBool {posited_bool :> bool; _ : is_true posited_bool = P}.

Local Fact is_true_nPropP nP (b : negatedBool nP) : (~ b) = nP.
Proof. by case: b. Qed.
Canonical is_true_nProp nP b := ProperNegatedProp (@is_true_nPropP nP b).

Local Fact true_negP : (~ true) = False. Proof. by eqProp. Qed.
Local Fact true_posP : (true : Prop) = True. Proof. by eqProp. Qed.
Local Fact false_negP : (~ false) = True. Proof. by eqProp. Qed.
Local Fact false_posP : (false : Prop) = False. Proof. by eqProp. Qed.
Canonical true_neg := NegatedBool true_negP.
Canonical true_pos := PositedBool true_posP.
Canonical false_neg := NegatedBool false_negP.
Canonical false_pos := PositedBool false_posP.

Local Fact id_negP (b : bool) : (~ b) = ~~ b. Proof. exact/rwP/negP. Qed.
Canonical id_neg b := NegatedBool (id_negP b).
Canonical id_pos (b : bool) := @PositedBool b b erefl.

Local Fact negb_negP P (b : positedBool P) : (~ ~~ b) = P.
Proof. by rewrite (rwP negP) negbK; case: b. Qed.
Canonical negb_neg P b := NegatedBool (@negb_negP P b).
Local Fact negb_posP nP (b : negatedBool nP) : (~~ b = nP :> Prop).
Proof. by rewrite -(rwP negP) notE. Qed.
Canonical negb_pos nP b := PositedBool (@negb_posP nP b).

(* We use a tertiary structure to handle the negation of nat comparisons, and *)
(* simplify ~ m <= n to n < m, and ~ m < n to n <= m. As m < n is merely      *)
(* notation for m.+1 <= n, we need to dispatch on the left hand side of the   *)
(* comparison to perform the latter simplification.                           *)

Structure negatedLeqLHS n lt_nm :=
  NegatedLeqLHS {negated_leq_LHS :> nat; _ : (n < negated_leq_LHS) = lt_nm}.
Canonical neg_ltn_LHS n m := @NegatedLeqLHS n (n <= m) m.+1 erefl.
Canonical neg_leq_LHS n m := @NegatedLeqLHS n (n < m) m erefl.

Local Fact leq_negP n lt_nm (m : negatedLeqLHS n lt_nm) : (~ m <= n) = lt_nm.
Proof. by rewrite notE -ltnNge; case: m => /= m ->. Qed.
Canonical leq_neg n lt_nm m := NegatedBool (@leq_negP n lt_nm m).

(*   We use two tertiary structures to simplify negation of boolean constant  *)
(* and decidable equalities, simplifying b <> true to ~~ b, b <> false to b,  *)
(* x <> y to x != y, and ~ x != y to x = y. We do need to use the wrapper     *)
(* telescope pattern here, as we want to simplify instances of x <> y when y  *)
(* evaluates to true or false. Since we only need two rules (true/false RHS   *)
(* or generic eqType RHS) we can use the generic wrapped type from ssrfun.    *)
(* The actual matching of the true and false RHS is delegated to a fourth     *)
(* level bool_eq_negation_rhs structure. Finally observe that the ~ x != y to *)
(* x = y simplification can be handled by a bool_affirmation instance.        *)

Structure neqRHS nP T x :=
  NeqRHS {neq_RHS :> wrapped T; _ : (x <> unwrap neq_RHS) = nP}. 
Structure boolNeqRHS nP (x : bool) :=
  BoolNeqRHS {bool_neq_RHS; _ : (x <> bool_neq_RHS) = nP}.

Local Fact eq_nPropP nP T x (y : neqRHS nP x) : (x <> unwrap y :> T) = nP.
Proof. by case: y. Qed.
Canonical eq_nProp nP T x y := ProperNegatedProp (@eq_nPropP nP T x y).

Local Fact bool_neqP nP x y : (x <> @bool_neq_RHS nP x y) = nP.
Proof. by case: y. Qed.
Canonical bool_neq nP x y := @NeqRHS nP bool x (wrap _) (@bool_neqP nP x y).
Canonical true_neq nP b := BoolNeqRHS (@is_true_nPropP nP b).
Local Fact false_neqP P (b : positedBool P) : (b <> false :> bool) = P.
Proof. by rewrite (rwP eqP) eqbF_neg notE. Qed.
Canonical false_neq P b := BoolNeqRHS (@false_neqP P b).

Local Fact eqType_neqP (T : eqType) (x y : T) : (x <> y) = (x != y).
Proof. by rewrite (rwP eqP) (rwP negP). Qed.
Canonical eqType_neq (T : eqType) x y :=
  @NeqRHS (x != y) T x (Wrap y) (eqType_neqP x y).
Local Fact eq_op_posP (T : eqType) x y : (x == y :> T : Prop) = (x = y).
Proof. exact/esym/rwP/eqP. Qed.
Canonical eq_op_pos T x y := PositedBool (@eq_op_posP T x y).

(******************************************************************************)
(* The witnessedType structure provides conversion between Type and Prop in   *)
(* goals; the conversion is mostly used in the Type-to-Prop direction, e.g.,  *)
(* as a preprocessing step preceding proof by contradiction (see absurd_not   *)
(* below), but the Prop-to-Type direction is required for contraposition.     *)
(*   Thus witnessedType associates to a type T a "witness" proposition P      *)
(* equivalent to the existence of an x of type T. As in a `{classical_logic}  *)
(* context inhabited T is such a proposition, witnessedType can be understood *)
(* as providing simplification for inhabited T, much like negatedProp         *)
(* provides simplification for ~ P for standard connectives and predicates.   *)
(******************************************************************************)

(*  Similarly to negatedProp, witnessedType returns the witness proposition   *)
(* via a projection argument P, but does not need to signal "trivial"         *)
(* instances as the default value for P is nontrivial (namely, inhabited T),  *)
(* while the "trivial" case where P = T is actually desireable and handled    *)
(* by an extra top-priority rule.                                             *)

Structure witnessedType P := WitnessedType {
 witnessed_Type :> wrappedType; _ : inhabited witnessed_Type = P}.
Structure properWitnessedType P := ProperWitnessedType {
  proper_witnessed_Type :> Type; _ : inhabited proper_witnessed_Type = P}.
Local Notation wType P T := (unwrap_Type (@witnessed_Type P T)).
Local Notation wTycon P T x := (wType (P x) (T x)).

(* User interface lemmas. *)

Lemma witnessedType_intro {P : Prop} T : P -> wType P T.
Proof. by case: T => /= T <- /inhabited_witness. Qed.
Local Coercion witnessedType_intro : witnessedType >-> Funclass.

Lemma witnessedType_elim {P} T : wType P T -> P.
Proof. by case: T => /= T <-. Qed.
Local Notation wTypeP := witnessedType_elim.

(* Helper lemma and tactic. *)

Local Fact eq_inhabited T (P : Prop) : (T -> P) -> (P -> T) -> inhabited T = P.
Proof. by move=> T_P P_T; eqProp=> [[/T_P] | /P_T]. Qed.
Ltac eqInh := apply: eq_inhabited.

(* Rule 1: Prop goals are left as is. *)
Canonical Prop_wType P :=
  @WitnessedType P (wrap1Type P) (eq_inhabited (@id P) id).

(* Rule 2: Specific type constructors (sigs, sums, and pairs) are delegated   *)
(* to the secondary properWitnessedType structure.                            *)
Lemma proper_wTypeP P (T : properWitnessedType P) : inhabited T = P.
Proof. by case: T. Qed.
Canonical proper_wType P T :=
  @WitnessedType P (wrap2Type _) (@proper_wTypeP P T).

(* Rule 3: Forall (and -> as a special case). *)
Local Fact forall_wTypeP A P T :
  inhabited (forall x : A, wTycon P T x) = (forall x : A, P x) .
Proof. by do [eqInh=> allP x; have:= allP x] => [/wTypeP | /T]. Qed.
Canonical forall_wType A P T :=
  @WitnessedType _ (wrap3Type _) (@forall_wTypeP A P T).

(* Rule 4: Default to inhabited if all else fails. *)
Canonical inhabited_wType T := @WitnessedType (inhabited T) (wrap4Type T) erefl.

(* Specific proper_witnessedType instances. *)

Local Fact void_wTypeP : inhabited void = False. Proof. by eqInh. Qed.
Canonical void_wType := ProperWitnessedType void_wTypeP.

Local Fact unit_wTypeP : inhabited unit = True. Proof. by eqInh. Qed.
Canonical unit_wType := ProperWitnessedType unit_wTypeP.

Local Fact pair_wTypeP P Q S T : inhabited (wType P S * wType Q T) = (P /\ Q).
Proof. by eqInh=> [[/wTypeP-isP /wTypeP] | [/S-x /T]]. Qed.
Canonical pair_wType P Q S T := ProperWitnessedType (@pair_wTypeP P Q S T).

Local Fact sum_wTypeP P Q S T : inhabited (wType P S + wType Q T) = (P \/ Q).
Proof. by eqInh=> [[] /wTypeP | /decide_or[/S | /T]]; by [left | right]. Qed.
Canonical sum_wType P Q S T := ProperWitnessedType (@sum_wTypeP P Q S T).

Local Fact sumbool_wTypeP P Q : inhabited ({P} + {Q}) = (P \/ Q).
Proof. by eqInh=> [[] | /decide_or[]]; by [left | right]. Qed.
Canonical sumbool_wType P Q := ProperWitnessedType (@sumbool_wTypeP P Q).

Local Fact sumor_wTypeP P Q T : inhabited (wType P T + {Q}) = (P \/ Q). 
Proof. by eqInh=> [[/wTypeP|] | /decide_or[/T|]]; by [left | right]. Qed.
Canonical sumor_wType P Q T := ProperWitnessedType (@sumor_wTypeP P Q T).

Local Fact sig1_wTypeP T P : inhabited {x : T | P x} = (exists x : T, P x). 
Proof. by eqInh=> [[x Px] | /EXW//]; exists x. Qed.
Canonical sig1_wType T P := ProperWitnessedType (@sig1_wTypeP T P).

Local Fact sig2_wTypeP T P Q :
  inhabited {x : T | P x & Q x} = exists2 x : T, P x & Q x. 
Proof. by eqInh=> [[x Px Qx] | /EX2W//]; exists x. Qed.
Canonical sig2_wType T P Q := ProperWitnessedType (@sig2_wTypeP T P Q).

Local Fact sigT_wTypeP A P T :
  inhabited {x : A & wTycon P T x} = (exists x : A, P x).
Proof. by eqInh=> [[x /wTypeP] | /EXW[x /T]]; exists x. Qed.
Canonical sigT_wType A P T := ProperWitnessedType (@sigT_wTypeP A P T).

Local Fact sigT2_wTypeP A P Q S T :
  inhabited {x : A & wTycon P S x & wTycon Q T x} = (exists2 x : A, P x & Q x).
Proof. by eqInh=> [[x /wTypeP-Px /wTypeP] | /EX2W[x /S-y /T]]; exists x. Qed.
Canonical sigT2_wType A P Q S T :=
  ProperWitnessedType (@sigT2_wTypeP A P Q S T).

(******************************************************************************)
(*    The witnessProp structure provides for conversion of some Prop          *)
(* assumptions to Type values with some constructive contents, e.g., convert  *)
(* a P \/ Q assumption to a {P} + {Q} sumbool value. This is not the same as  *)
(* the forward direction of witnessedType, because instances here match the   *)
(* Prop statement: witness_Prop find a T such that P -> T while witnessedType *)
(* finds a P such that P -> T (and T -> P for the converse direction).        *)
(******************************************************************************)

(*   The implementation follows the wrapper telescope pattern similarly to    *)
(* negatedProp, with three rules, one for Prop constructors with proper       *)
(* constructive contents, one for forall propositions (also with proper       *)
(* constructive contents) and one default rule that just returns P : Prop as  *)
(* is (thus, with no other contents except the provability of P).             *)
(*   The witnessProp structure also uses projection parameters to return the  *)
(* inferred Type T together with a bool 'trivial' flag that is set when the   *)
(* trivial rule is used. Here, however, this flag is used in both directions: *)
(* the 'witness' view forces it to false to prevent trivial instances, but    *)
(* the flag is also used to fine tune the choice of T, selecting between      *)
(* sum, sumor, and sumbool, between sig and sigT, and sig2 and sigT2. This    *)
(* relies on the fact that the tactic engine will eagerly iota reduce the     *)
(* returned type, so that the user will never see the conditionals specified  *)
(* in the proper_witness_Prop instances.                                      *)
(*   However, it would not be possible to construct the specialised types     *)
(* for trivial witnesses (e.g., {P} + {Q}) using the types returned by        *)
(* witnessProp instances, since thes are in Type, and the information that    *)
(* they are actully in Prop has been lost. This is solved by returning an     *)
(* additional Prop P0 that is a copy of the matched Prop P when               *)
(* trivial = true. (We put P0 = True when trivial = false, as we only need to *)
(* ensure P -> P0.)                                                           *)
(*  Caveat: although P0 should in principle be the last parameter of          *)
(* witness_Prop, and we use this order for the wProp and wPred projector      *)
(* local notation, it is important to put P0 BEFORE T, to circumvent an       *)
(* incompleteness in Coq's implementation of higher-order pattern unification *)
(* that would cause the trivial rule to fail for the body of an exists.       *)
(* In such a case the rule needs to unify (1) ?P0 x ~ ?P and (2) ?T x ~ ?P    *)
(* for some type A some x : A in the context of ?P, but not ?P0 nor ?T. This  *)
(* succeeds easily if (1) is performed before (2), setting ?P := ?P0 x and    *)
(* ?T := ?P0, but if (2) is attempted first Coq tries to perform ?P := ?T x,  *)
(* which fails Type/Prop universe constraints, and then fails outright,       *)
(* instead of using pattern unification to solve (2) as ?P := ?Q x, ?T := ?Q  *)
(* for a fresh ?Q : A -> Prop.                                                *)

Structure witnessProp (trivial : bool) (P0 : Prop) (T : Type) :=
  WitnessProp {witness_Prop :> wrappedProp; _ : witness_Prop -> T * P0}.
Structure properWitnessProp T :=
  ProperWitnessProp {proper_witness_Prop :> Prop; _ : proper_witness_Prop -> T}.

Local Notation wProp t T P0 P := (unwrap_Prop (@witness_Prop t P0 T P)).
Local Notation wPred t T P0 P x := (wProp t (T x) (P0 x) (P x)).

Local Fact wPropP t T P0 P : wProp t T P0 P -> T * P0. Proof. by case: P. Qed.
Lemma lax_witness {t T P0 P} : move_view (wProp t T P0 P) T.
Proof. by split=> /wPropP[]. Qed.
Definition witness {T P0 P} := @lax_witness false T P0 P.

(* Rule 1: proper instances (except forall), delegated to an auxiliary        *)
(* structures.                                                                *)
Local Fact proper_wPropP T P : wrap1Prop (@proper_witness_Prop T P) -> T * True.
Proof. by case: P => _ P_T {}/P_T. Qed.
Canonical proper_wProp T P := WitnessProp false (@proper_wPropP T P).

(* Rule 2: forall types (including implication); as only proper instances are *)
(* allowed, we set trivial = false for the recursive body instance.           *)
Local Fact forall_wPropP A T P0 P :
  wrap2Prop (forall x : A, wPred false T P0 P x) -> (forall x, T x) * True.
Proof. by move=> P_A; split=> // x; have /witness := P_A x. Qed.
Canonical forall_wProp A T P0 P := WitnessProp false (@forall_wPropP A T P0 P).

(* Rule 3: trivial (proof) self-witness. *)
Canonical trivial_wProp P :=
  WitnessProp true (fun p : wrap3Prop P => (p, p) : P * P).

(* Specific proper_witnesss_Prop instances. *)

Canonical inhabited_wProp T := ProperWitnessProp (@inhabited_witness T).

(* Conjunctions P /\ Q are a little delicate to handle, as we should not      *)
(* produce a proper instance (and thus fail) if neither P nor Q is proper.    *)
(* We use a tertiary structure for this : nand_bool b, which has instances    *)
(* only for booleans b0 such that ~~ (b0 && b). We allow the witness_Prop     *)
(* instance for P to return an arbitrary 'trivial' flag s, but then force the *)
(* 'trivial' flag for Q to be an instance of nand_bool s.                     *)

Structure nandBool b := NandBool {nand_bool :> bool; _ : ~~ (nand_bool && b)}.
Canonical nand_false_bool b := @NandBool b false isT.
Canonical nand_true_bool := @NandBool false true isT.

Local Fact and_wPropP s S P0 P (t : nandBool s) T Q0 Q :
  wProp s S P0 P /\ wProp t T Q0 Q -> S * T.
Proof. by case=> /lax_witness-x /lax_witness. Qed.
Canonical and_wProp s S P0 P t T Q0 Q :=
  ProperWitnessProp (@and_wPropP s S P0 P t T Q0 Q).

(* The first : Type cast ensures the return type of the inner 'if' is not     *)
(* incorrectly set to 'Set', while the second merely ensures the S + T        *)
(* notation is resolved correctly).                                           *)
Local Fact or_wPropP s S P0 P t T Q0 Q :
    wProp s S P0 P \/ wProp t T Q0 Q ->
  if t then if s then {P0} + {Q0} : Type else S + {Q0} else S + T : Type.
Proof.
by case: s t => -[] in P Q *; (case/decide_or=> /wPropP[]; [left | right]).
Qed.
Canonical or_wProp s S P0 P t T Q0 Q :=
  ProperWitnessProp (@or_wPropP s S P0 P t T Q0 Q).

Local Fact exists_wPropP A t T P0 P :
  (exists x : A, wPred t T P0 P x) -> if t then {x | P0 x} else {x & T x}.
Proof. by case/EXW => x /wPropP[]; case t; exists x. Qed.
Canonical exists_wProp A t T P0 P :=
  ProperWitnessProp (@exists_wPropP A t T P0 P).

(* Note the expanded expression for st = s && t, which will be reduced to     *)
(* true or false by iota reduction when s and t are known.                    *)
Local Fact exists2_wPropP A s S P0 P t T Q0 Q (st := if s then t else false) :
    (exists2 x : A, wPred s S P0 P x & wPred t T Q0 Q x) ->
  if st then {x | P0 x & Q0 x} else {x : A & S x & T x}.
Proof. by case/EX2W=> x /wPropP[P0x y] /wPropP[]; case: ifP; exists x. Qed.
Canonical exists2_wProp A s S P0 P t T Q0 Q :=
  ProperWitnessProp (@exists2_wPropP A s S P0 P t T Q0 Q).

(******************************************************************************)
(*   User lemmas and tactics for proof by contradiction and contraposition.   *)
(******************************************************************************)

(* Helper lemmas:                                                             *)
(*   push_goal_copy make a copy of the goal that can then be matched with     *)
(*     witnessedType and negatedProp instances to generate a contradiction    *)
(*     assuption, without disturbing the original for of the goal.            *)
(*   assume_not_with turns the copy generated by push_identity into an        *)
(*     equivalent negative assumption, which can then be simplified using the *)
(*     lax_notP and lax_witness views.                                        *)
(*   absurd and absurdW replace the goal with False; absurdW does this under  *)
(*     an assumption, and is used to weaken proof-by-assuming-negation to     *)
(*     proof-by-contradiction.                                                *)
(*   contra_Type converts an arbitrary function goal (with assumption and     *)
(*     conclusion in Type) to an equivalent contrapositive Prop implication.  *)
(*   contra_notP simplifies a contrapositive ~ Q -> ~ P goal using            *)
(*     negatedProp instances.                                               *)

Local Fact push_goal_copy {T} : ((T -> T) -> T) -> T. Proof. exact. Qed.
Local Fact assume_not_with {R P T} : (~ P -> R) -> (wType P T -> R) -> R.
Proof. by move=> nP_T T_R; have [/T|] := decP P. Qed.

Local Fact absurdW {S T} : (S -> False) -> S -> T. Proof. by []. Qed.

Local Fact contra_Type {P Q S T} : (~ Q -> ~ P) -> wType P S -> wType Q T.
Proof. by rewrite implyNN => P_Q /wTypeP/P_Q/T. Qed.

Local Fact contra_notP tP tQ (nP nQ : Prop) P Q :
  (nP -> nQ) -> (~ nProp tP nP P -> ~ nProp tQ nQ Q).
Proof. by rewrite 2!lax_notE. Qed.

(* Lemma and tactic assume_not: add a goal negation assumption. The tactic    *)
(* also works for goals in Type, simplifies the added assumption, and         *)
(* and exposes its top-level constructive contents.                           *)
Lemma assume_not {P} : (~ P -> P) -> P. Proof. by rewrite implyNp orB. Qed.
Ltac assume_not :=
  apply push_goal_copy; apply: assume_not_with => /lax_notP-/lax_witness.

(* Lemma and tactic absurd_not: proof by contradiction. Same as assume_not,   *)
(* but the goal is erased and replaced by False.                              *)
(* Caveat: absurd_not cannot be used as a move/ view because its conclusion   *)
(* is indeterminate. The more general notP defined above can be used instead. *)
Lemma absurd_not {P} : (~ P -> False) -> P. Proof. by move/notP. Qed.
Ltac absurd_not := assume_not; apply: absurdW.

(* Tactic contra: proof by contraposition. Assume the negation of the goal    *)
(* conclusion, and prove the negation of a given assumption. The defective    *)
(* form contra (which can also be written contrapose) expects the assumption  *)
(* to be pushed on the goal which thus has the form assumption -> conclusion. *)
(*   As with assume_not, contra allows both assumption and conclusion to be   *)
(* in Type, simplifies the negation of both assumption and conclusion, and    *)
(* exposes the constructive contents of the negated conclusion.               *)
(*   The contra tactic also supports a limited form of the ':' discharge      *)
(* pseudo tactical, whereby contra: <d-items> means move: <d-items>; contra.  *)
(* The only <d-items> allowed are one term, possibly preceded by a clear      *)
(* switch.                                                                    *)
Ltac contrapose := apply: contra_Type; apply: contra_notP => /lax_witness.
Tactic Notation "contra" := contrapose.
Tactic Notation "contra" ":" constr(H) := move: (H); contra.
Tactic Notation "contra" ":" ident(H) := move: H; contra.
Tactic Notation "contra" ":" "{" hyp_list(Hs) "}" constr(H) :=
  contra: (H); clear Hs.
Tactic Notation "contra" ":" "{" hyp_list(Hs) "}" ident(H) :=
  contra: H; clear Hs.
Tactic Notation "contra" ":" "{" "-" "}" constr(H) := contra: (H).

(* Lemma and tactic absurd: proof by assumption contradiction. The defective  *)
(* form and the lemma simply replaces the entire goal with False (just as the *)
(* the Ltac exfalso), leaving the user to derive a contradiction from the     *)
(* assumptions. The ':' form absurd: <d-items> replaces the goal with the     *)
(* negation of the (single) <d-item> (as with contra:, a clear switch is also *)
(* allowed. Finally the Ltac absurd term form is also supported.              *)
Lemma absurd T : False -> T. Proof. by []. Qed.
Tactic Notation (at level 0) "absurd" := apply absurd.
Tactic Notation (at level 0) "absurd" constr(P) := have []: ~ P.
Tactic Notation "absurd" ":" constr(H) := absurd; contra: (H) => _.
Tactic Notation "absurd" ":" ident(H) := absurd; contra: H => _.
Tactic Notation "absurd" ":" "{" hyp_list(Hs) "}" constr(H) :=
  absurd: (H) => _; clear Hs.
Tactic Notation "absurd" ":" "{" hyp_list(Hs) "}" ident(H) :=
  absurd: H => _; clear Hs.

(******************************************************************************)

Fact dec_eqMixin {T} : Equality.mixin_of T.
Proof. exists (fun x => [dec y | x = y]) => x y; apply: decP. Qed.
Definition DecEqType {T} := EqType T dec_eqMixin.

Lemma well_order_WF T (R : rel T) :
   well_order R <-> antisymmetric R /\ well_founded (fun x y => ~~ R y x).
Proof.
set R' := fun x y => is_true _; split=> [Rwo | [Ranti Rwf]].
  split; first by have /total_orderE[] := @well_order_total DecEqType R Rwo.
  pose A := [dec x | ~ Acc R' x].
  move=> x; absurd_not=> Ax; have{x Ax}: nonempty A by exists x; apply/decP.
  case/Rwo=> x [[/decP-Ax minAx] _]; case: Ax; split=> y; rewrite /R'.
  by contra=> Ay; apply: minAx; apply/decP.
move=> A [x Ax]; elim: x / (Rwf x) => x _ IHx in Ax *.
have [lbAx | /notP[y Ay /IHx]] := decP (lower_bound R A x); last exact.
by exists x; split=> // y [Ay lbAy]; apply: Ranti; rewrite lbAx ?lbAy.
Qed.

Lemma Zorn's_lemma T (R : rel T) (S : {pred T}) :
  {in S & &, preorder R} ->
  {in <= S, forall C, wo_chain R C -> exists2 z, z \in S & upper_bound R C z} ->
  {z : T | z \in S & {in S, maximal R z}}.
Proof.
suffices{T R S} Zorn (T : eqType) (R : rel T) (Well := wo_chain R) :
    preorder R -> (forall C, Well C -> {z | upper_bound R C z}) ->
  {z | maximal R z}.
- case/preorder_in=> Rxx Rtr UBch; pose T1 := {x | x \in S}.
  have S_T1 (u : T1): val u \in S by case: u.
  have [|C1 chC1|u maxT1u] := Zorn (@DecEqType T1) (relpre val R); last 1 first.
  - by exists (val u) => // x Sx Rux; apply: (maxT1u (Sub x Sx)).
  - by apply/preorderE; split=> [x|y x z]; [apply: Rxx | apply: Rtr].
  pose C := [pred x | oapp (mem C1) false (insub x)].
  have sC1C u: u \in C1 -> val u \in C by rewrite inE valK.
  have memC x: x \in C -> {u | u \in C1 & val u = x}.
    by rewrite inE; case: insubP => //= u _ <-; exists u.
  apply/EXW; suffices /UBch[_ /memC[u _ <-]//|z Sz ubCz]: wo_chain R C.
    by exists (Sub z Sz) => u C1u; apply/ubCz/sC1C.
  move=> A sAC [x0 Ax0].
  have [||w [[C1w minC1w] Uw]] := chC1 [preim val of A].
  - by move=> v /sAC; rewrite inE valK.
  - by have /sAC/memC[u0 C1u0 Du0] := Ax0; exists u0; rewrite inE Du0.
  exists (val w); do ?[split] => // [y Ay | y [Ay minAy]].
    by case/sAC/memC: Ay (Ay) => v C1v <-; apply: minC1w.
  have /sAC/memC[v C1v Dv] := Ay; rewrite (Uw v) //.
  by split=> [|u Au]; rewrite ?inE /= Dv // minAy.
case/preorderE=> Rxx Rtr UBch; absurd_not=> nomaxR.
pose R' := [rel x y | R x y && ~~ R y x].
have{nomaxR} /all_sig[f fP] C: {z | Well C -> upper_bound R' C z}.
  have /UBch[z0 _]: Well pred0 by move=> A sA0 [x /sA0].
  have [/UBch[y RCy]|] := decP (Well C); last by exists z0.
  have [z Ryz notRzy] := nomaxR y; exists z => _ x /RCy-Rxy /=.
  by rewrite (Rtr y) //=; contra: notRzy => /Rtr->.
have notCf C: Well C -> f C \notin C.
  by move/fP=> R'Cf; apply/negP=> /R'Cf/=; rewrite Rxx ?andbF.
pose f_ind X := Well X /\ {in X, forall x, f [pred y in X | ~~ R x y] = x}.
pose init_seg (X Y : {pred T}) :=
  {subset X <= Y} /\ {in Y, forall y, y \notin X -> upper_bound R X y}.
have init_total Y Z: f_ind Y -> f_ind Z -> {init_seg Y Z} + {init_seg Z Y}.
  move=> indY indZ; pose iniYZ := [dec X | init_seg X Y /\ init_seg X Z].
  pose I := [union X, X in iniYZ]; pose I1 := [predU1 f I & I].
  have [iIY iIZ]: init_seg I Y /\ init_seg I Z.
    split; split=> [x /decP[X /decP[[sXY _] [sXZ _]]]|]; try by move: (x).
      move=> y Yy /decP-I'y x /decP[X iXYZ Xx]; have /decP[[_ RXY] _] := iXYZ.
      by rewrite RXY //; contra: I'y; exists X.
    move=> z Zz /decP-I'z x /decP[X iXYZ Xx]; have /decP[_ [_ RXZ]] := iXYZ.
    by rewrite RXZ //; contra: I'z; exists X.
  have maxI: {in iniYZ, forall X, {subset X <= I}}; last clearbody I.
    by move=> X sXYZ x Xx; apply/decP; exists X.
  have Ich: Well I by have [Ych _] := indY; apply: sub_within Ych; case: iIY.
  generally have iI1, iI1Y: Y indY iIY {iniYZ maxI} / {I = Y} + {init_seg I1 Y}.
    have [[Ych fY] [sIY RIY]] := (indY, iIY).
    have /wo_chainW/total_order_in[_ _ RYanti _] := Ych.
    have [sYI | /notP-ltIY] := decP {subset Y <= I}; [left | right].
      by apply/pEXT=> y; apply/idP/idP=> [/sIY | /sYI].
    have{ltIY} /Ych[_ /andP[]//| z [[/andP/=[I'z Yz]]]]: nonempty [predD Y & I].
      by have [y] := ltIY; exists y; apply/andP.
    move=> minYz _; suffices Dz: f I = z.
      rewrite /I1 Dz; do 2?[split] => // [x /predU1P[->|/sIY] // | y Yy].
      by case/norP=> /= z'y I'y x /predU1P[->|/RIY->//]; apply/minYz/andP.
    rewrite -(fY z Yz); congr f; apply/esym/pEXT=> x /=.
    apply/idP/idP=> [/andP[Yx] | Ix]; first by contra=> I'x; apply/minYz/andP.
    have Yx := sIY x Ix; rewrite inE Yx /=; contra: (I'z) => Rzx.
    by rewrite (RYanti z x) // Rzx RIY.    
  case: iI1Y {iI1}(iI1 Z) => [<- _| iI1Y [||<-|iI1Z]//]; [by left | by right |].
  by case/notCf/negP: Ich; apply/(maxI I1); [apply/decP|apply/predU1l].
pose U := [dec x | exists2 X, x \in X & f_ind X].
have Umax X: f_ind X -> init_seg X U.
  move=> indX; split=> [x Xx | y]; first by apply/decP; exists X.
  case/decP=> Y Yy indY notXy x Xx.
  by have [[sYX _]|[_ ->//]] := init_total Y X indY indX; rewrite sYX in notXy.
have RUanti: {in U &, antisymmetric R}.
  move=> x y /decP[X Xx indX] /decP[Y Yy indY].
  without loss [sXY _]: x y X Y Xx Yy {indX} indY / init_seg X Y.
    move=> IH. 
    by case: (init_total X Y) => // {}/IH-IH; [|rewrite andbC] => /IH->.
  have [/wo_chainW/total_order_in[_ _ RYanti _] _] := indY.
  by apply: RYanti => //; apply: sXY.
have Uch: Well U.
  apply: antisymmetric_wo_chain => // A sAU [x0 Ax0].
  have /sAU/decP[X Xx0 indX] := Ax0.
  pose B := [predI A & X]; have sBX: {subset B <= X} by move=> y /andP[].
  have [[Xch _] /Umax[sXU iXU]] := (indX, indX).
  have{x0 Ax0 Xx0} /Xch[//|z [[/andP[/= Az Xz] minBz] _]]: nonempty B.
    by exists x0; apply/andP.
  exists z; split=> // y Ay; have Uy := sAU y Ay.
  by have [Xy | /iXU->//] := boolP (y \in X); apply/minBz/andP.
pose U1 := [predU1 f U & U]; have notUfU: f U \notin U by apply: notCf.
suffices indU1: f_ind U1.
  by have [sU1U _] := Umax U1 indU1; rewrite sU1U ?inE ?eqxx in notUfU.
have RU1fU: upper_bound R U1 (f U) by move=> x /predU1P[-> // | /fP/andP[]] .
split=> [A sAU1 neA | x U1x].
  have [sAfU | {neA}/notP[x Ax fU'x]] := decP {subset A <= pred1 (f U)}.
    have AfU: f U \in A by have [x Ax] := neA; have /sAfU/eqP<- := Ax.
    by exists (f U); split=> [|y [/sAfU/eqP//]]; split=> // _ /sAfU/eqP->.
  have Ux: x \in U by case/sAU1/orP: Ax => // /idPn.
  pose B := [predI A & U]; have sBU: {subset B <= U} by move=> y /andP[].
  have /Uch[//|z [[/andP[/= Az Uz] minBz] _]]: nonempty B.
    by exists x; apply/andP.
  have{minBz} minAz: lower_bound R A z.
    move=> y Ay; case/sAU1/predU1P: (Ay) => [->|/= Uy]; first exact/RU1fU/sAU1.
    exact/minBz/andP.
  exists z; do ?[split] => // y [Ay minAy].
  have /sAU1/predU1P[Dy|Uy] := Ay; last by apply: RUanti; rewrite ?minAz ?minAy.
  by have /andP[_] := fP U Uch z Uz; rewrite -Dy minAy.
have /predU1P[-> | /decP[X Xx indX]] := U1x.
  congr f; apply/pEXT=> y; apply/idP/idP=> [|Uy]; last first.
    by rewrite !inE Uy orbT; case/andP: (fP U Uch y Uy).
  by case/andP=> /predU1P[->|//]; rewrite Rxx.
have{indX} [[_ f_indX] /Umax[sXU iXU]] := (indX, indX).
rewrite -[RHS]f_indX //; congr f; apply/pEXT=> y; apply/andb_id2r=> notRyx.
apply/idP/idP=> [U1y | Xy]; last exact/predU1r/sXU.
by contra: notRyx => notXy; have /predU1P[->|/iXU->] := U1y; first apply/RU1fU.
Qed.

Theorem Hausdorff_maximal_principle T R (S C : {pred T}) :
    {in S & &, preorder R} -> chain R C -> {subset C <= S} ->
  {M : {pred T} |
    [/\ {subset C <= M}, {subset M <= S}
      & forall X, chain R X -> {subset M <= X} -> {subset X <= S} -> M = X]}.
Proof.
case/preorder_in=> Rxx Rtr Cch sCS.
pose CSch := [dec X | [/\ chain R X, {subset C <= X} & {subset X <= S}]].
pose Rch (X : {pred T}) := [dec Y : {pred T} | {subset X <= Y}].
have: {in CSch & &, preorder Rch}.
  apply: in3W; apply/preorderE; split=> [X | X Y Z]; first exact/decP.
  by move=> /decP-sXY /decP-sYZ; apply/decP=> x /sXY/sYZ.
case/Zorn's_lemma=> [XX CSchXX XXwo | M /decP[Mch sCM sMS] maxM]; last first.
  exists M; split=> // X Xch sMX sXS.
  suffices /decP-sXM: Rch X M by apply/pEXT=> x; apply/idP/idP=> [/sMX|/sXM].
  by apply: maxM; apply/decP=> //; split=> // x /sCM/sMX.
have{XXwo} /(@wo_chainW DecEqType)/total_order_in[_ _ _ XXch] := XXwo.
without loss XX_C: XX CSchXX XXch / C \in XX.
  have CSchC: C \in CSch by apply/decP; split.
  have RchC_CSch X: X \in CSch -> Rch C X by case/decP=> _ sCX _; apply/decP.
  pose XX1 := [dec X | X = C \/ X \in XX].
  have CSchXX1: {subset XX1 <= CSch} by move=> X /decP[-> | /CSchXX].
  case/(_ XX1)=> // [||Z CSchZ ubZ]; first 2 [by apply/decP; left].
    move=> X Y /decP[-> /CSchXX1/RchC_CSch-> //| XX_X].
    by rewrite orbC => /decP[-> | /XXch->//]; rewrite RchC_CSch ?CSchXX.
  by exists Z => // X XX_X; apply/ubZ/decP; right.
pose D := [union X, X in XX].
have sCD: {subset C <= D} by move=> x Cx; apply/decP; exists C.
have sDS: {subset D <= S} by move=> x /decP[X /CSchXX/decP[_ _ sXS] /sXS].
have in2D: {in D &, forall x y, exists X, [/\ X \in XX, x \in X & y \in X]}.
  move=> x y /decP[X XX_X Xx] /decP[Y XX_Y Yy]; have:= XXch X Y XX_X XX_Y.
  by case/orP=> [/decP/(_ x Xx)|/decP/(_ y Yy)]; [exists Y | exists X].
exists D => [|X XX_X]; last by apply/decP=> x Xx; apply/decP; exists X.
apply/decP; split=> //; first apply/total_order_in.
by split; first 1 [exact: (sub_in1 sDS) | exact: (sub_in3 sDS)];
  move=> x y _ /(in2D x)[//|X [/CSchXX/decP[Xch _ _] Xx Xy]];
  have /total_order_in[_ _ anti tot] := Xch; do [apply: anti | apply: tot].
Qed.

Theorem well_ordering_principle T : {R : rel T | well_order R}.
Proof.
have{T} [T ->]: {T1 : eqType | T = T1} by exists (@DecEqType T).
pose srel := pred T * rel T : Type.
pose loc (R : srel) := [rel x y | [&& x \in R.1, y \in R.1 & R.2 x y]].
pose pwo := [dec R : srel | wo_chain R.2 R.1].
pose init_seg (R S : srel) :=
  {in R.1 & S.1, forall x y, S.2 x y = (y \in R.1) ==> R.2 x y}.
pose initR R := [dec S | {subset R.1 <= S.1} /\ init_seg R S].
have initRR: reflexive initR by move=> R; apply/decP; split=> // x y _ ->.
have initRtr: transitive initR.
  move=> R2 R1 R3 /decP[D12 R12] /decP[D23 R23]; apply/decP.
  split=> [x /D12/D23// | x y D1x D3y]; rewrite R23 ?(D12 x) //.
  by case D2y: (y \in R2.1); [apply: R12 | rewrite (contraFF (D12 y))].
have: {in pwo & &, preorder initR} by apply: in3W; apply/preorderE.
case/Zorn's_lemma=> [C pwoC Cch | [D R] /decP/=pwoR maxR].
  have{Cch} /(@wo_chainW DecEqType)/total_order_in[_ _ _ Cch] := Cch.
  pose D := [union S.1, S in C]; pose R x := [dec y | loc S x y, S in C].
  exists (D, R).
    apply/decP=> /= X sXD [x Xx]; have /sXD/decP[R0 CR0 /= D0x] := Xx.
    have /pwoC/decP/=R0wo := CR0.
    have{x Xx D0x}: nonempty [predI X & R0.1] by exists x; apply/andP.
    case/R0wo=> [_ /andP[]// |z [[/andP/=[Xz D0z] min0z] _]].
    have{R0 CR0 R0wo D0z min0z} minXz: lower_bound R X z.
      move=> y Xy; have /sXD/decP[R1 /= CR1 D1y] := Xy.
      have /orP[/decP/=[D10 R10] | /decP/=[D01 R01]] := Cch _ _ CR1 CR0.
        by apply/decP; exists R0; rewrite //= D0z min0z ?inE ?Xy D10.
      apply/decP; exists R1; rewrite //= R01 ?(D1y, D01) //=.
      by apply/implyP=> D0y; apply/min0z/andP.
    exists z; split=> // y [{}/minXz/decP[R0 CR0 R0zy] minXy].
    case/minXy/decP: Xz => {minXy} R1 CR1 R1yz.
    without loss /decP[D01 R01]: y z R0 R1 CR0 CR1 R0zy R1yz / initR R0 R1.
      by move=> IH; have /orP[/(IH y z)-> | /(IH z y)-> ] := Cch _ _ CR0 CR1.
    have{R1yz R0zy} [/and3P[D1y D1z R1zy] /and3P[D0z D0y R0yz]] := (R1yz, R0zy).
    have /pwoC/decP/wo_chainW/total_order_in[_ _ R1anti _] := CR1.
    by apply: R1anti => //; rewrite R1zy R01 // D0y R0yz.
  move=> R0 CR0; apply/decP; split=> [x D0x|]; first by apply/decP; exists R0.
  move=> x y D0x Dy; apply/decP/idP=> [[R1 CR1 /and3P[D1x D1y R1xy]] | R0xy].
    have /orP[/decP[_ R10] | /decP[_ <- //]] := Cch _ _ CR1 CR0.
    by apply/implyP=> D0y; rewrite R10 // D1y R1xy.
  case/decP: Dy => R1 CR1 D1y.
  have /orP[/decP[D10 _] | /decP[D01 R01]] := Cch _ _ CR1 CR0.
    by exists R0; rewrite //= D0x (implyP R0xy) D10.
  by exists R1; rewrite //= D1y D01 ?R01.
exists R; apply: withinT; apply: sub_within (pwoR) => z _; assume_not=> notDz.
pose Rz x := predU1 z (if x \in D then R x else pred0).
have /maxR/(_ _)/decP: ([predU1 z & D] : pred T, Rz : rel T) \in pwo.
  apply/decP=> X sXxD neX; pose XD := [predI X & D].
  have [{neX}/pwoR[_ /andP[]//|x] | sXz] := decP (nonempty XD); last first.
    have{sXz} sXz x: x \in X -> x = z.
      move=> Xx; case/sXxD/predU1P: (Xx) => // Dx.
      by case: sXz; exists x; apply/andP.
    have [x Xx] := neX; exists x; have /sXz-eq_xz := Xx.
    by split=> [|_ [/sXz-> //]]; split=> // _ /sXz->; apply/predU1l.
  case=> -[/andP/=[Xx Dx] minXDx] Ux; exists x; split=> [|y [Xy minXy]].
    split=> // y Xy; have /sXxD/predU1P[-> | Dy] := Xy; first exact/predU1l.
    by rewrite /= Dx; apply/predU1r/minXDx/andP.
  have Dy: y \in D.
    have /minXy/= := Xx; case: ifP => // _ /idPn[].
    by rewrite negb_or andbT (memPn notDz).
  apply: Ux; split=> [|t /andP[/minXy]]; first exact/andP.
  by rewrite /= Dy => /predU1P[-> /idPn[]|].   
case=> [|/= -> //]; last exact/predU1l.
apply/decP; split=> [x|x y /= Dx]; first exact: predU1r.
rewrite Dx => /predU1P[-> | /= Dy]; first by rewrite eqxx (negPf notDz).
by rewrite Dy -implyNb (memPn notDz).
Qed.

End Zorn.

(* Technical definitions about coding and decoding of nat sequences, which    *)
(* are used below to define various Canonical instances of the choice and     *)
(* countable interfaces.                                                      *)

Module CodeSeq.

(* Goedel-style one-to-one encoding of seq nat into nat.                      *)
(* The code for [:: n1; ...; nk] has binary representation                    *)
(*          1 0 ... 0 1 ... 1 0 ... 0 1 0 ... 0                               *)
(*            <----->         <----->   <----->                               *)
(*             nk 0s           n2 0s     n1 0s                                *)

Definition code := foldr (fun n m => 2 ^ n * m.*2.+1) 0.

Fixpoint decode_rec (v q r : nat) {struct q} :=
  match q, r with
  | 0, _         => [:: v]
  | q'.+1, 0     => v :: [rec 0, q', q']
  | q'.+1, 1     => [rec v.+1, q', q']
  | q'.+1, r'.+2 => [rec v, q', r']
  end where "[ 'rec' v , q , r ]" := (decode_rec v q r).

Definition decode n := if n is 0 then [::] else [rec 0, n.-1, n.-1].

Lemma decodeK : cancel decode code.
Proof.
have m2s: forall n, n.*2 - n = n by move=> n; rewrite -addnn addnK.
case=> //= n; rewrite -[n.+1]mul1n -(expn0 2) -[n in RHS]m2s.
elim: n {2 4}n {1 3}0 => [|q IHq] [|[|r]] v //=; rewrite {}IHq ?mul1n ?m2s //.
by rewrite expnSr -mulnA mul2n.
Qed.

Lemma codeK : cancel code decode.
Proof.
elim=> //= v s IHs; rewrite -[_ * _]prednK ?muln_gt0 ?expn_gt0 //=.
set two := 2; rewrite -[v in RHS]addn0; elim: v 0 => [|v IHv {IHs}] q.
  rewrite mul1n add0n /= -{}[in RHS]IHs; case: (code s) => // u; pose n := u.+1.
  by transitivity [rec q, n + u.+1, n.*2]; [rewrite addnn | elim: n => //=].
rewrite expnS -mulnA mul2n -{1}addnn -[_ * _]prednK ?muln_gt0 ?expn_gt0 //.
set u := _.-1 in IHv *; set n := u; rewrite [in u1 in _ + u1]/n.
by rewrite [in RHS]addSnnS -{}IHv; elim: n.
Qed.

Lemma ltn_code s : all (fun j => j < code s) s.
Proof.
elim: s => //= i s IHs; rewrite -[_.+1]muln1 leq_mul 1?ltn_expl //=.
apply: sub_all IHs => j /leqW lejs; rewrite -[j.+1]mul1n leq_mul ?expn_gt0 //.
by rewrite ltnS -[j]mul1n -mul2n leq_mul.
Qed.

Lemma gtn_decode n : all (ltn^~ n) (decode n).
Proof. by rewrite -{1}[n]decodeK ltn_code. Qed.

End CodeSeq.

Section OtherEncodings.
(* Miscellaneous encodings: option T -c-> seq T, T1 * T2 -c-> {i : T1 & T2}   *)
(* T1 + T2 -c-> option T1 * option T2, unit -c-> bool; bool -c-> nat is       *)
(* already covered in ssrnat by the nat_of_bool coercion, the odd predicate,  *)
(* and their "cancellation" lemma oddb. We use these encodings to propagate   *)
(* canonical structures through these type constructors so that ultimately    *)
(* all Choice and Countable instanced derive from nat and the seq and sigT    *)
(* constructors.                                                              *)

Variables T T1 T2 : Type.

Definition seq_of_opt := @oapp T _ (nseq 1) [::].
Lemma seq_of_optK : cancel seq_of_opt ohead. Proof. by case. Qed.

Definition tag_of_pair (p : T1 * T2) := @Tagged T1 p.1 (fun _ => T2) p.2.
Definition pair_of_tag (u : {i : T1 & T2}) := (tag u, tagged u).
Lemma tag_of_pairK : cancel tag_of_pair pair_of_tag. Proof. by case. Qed.
Lemma pair_of_tagK : cancel pair_of_tag tag_of_pair. Proof. by case. Qed.

Definition opair_of_sum (s : T1 + T2) :=
  match s with inl x => (Some x, None) | inr y => (None, Some y) end.
Definition sum_of_opair p :=
  oapp (some \o @inr T1 T2) (omap (@inl _ T2) p.1) p.2.
Lemma opair_of_sumK : pcancel opair_of_sum sum_of_opair. Proof. by case. Qed.

Lemma bool_of_unitK : cancel (fun _ => true) (fun _ => tt).
Proof. by case. Qed.

End OtherEncodings.

Prenex Implicits seq_of_opt tag_of_pair pair_of_tag opair_of_sum sum_of_opair.
Prenex Implicits seq_of_optK tag_of_pairK pair_of_tagK opair_of_sumK.

(* Generic variable-arity tree type, providing an encoding target for         *)
(* miscellaneous user datatypes. The GenTree.tree type can be combined with   *)
(* a sigT type to model multi-sorted concrete datatypes.                      *)
Module GenTree.

Section Def.

Variable T : Type.

Unset Elimination Schemes.
Inductive tree := Leaf of T | Node of nat & seq tree.

Definition tree_rect K IH_leaf IH_node :=
  fix loop t : K t := match t with
  | Leaf x => IH_leaf x
  | Node n f0 =>
    let fix iter_pair f : foldr (fun t => prod (K t)) unit f :=
      if f is t :: f' then (loop t, iter_pair f') else tt in
    IH_node n f0 (iter_pair f0)
  end.
Definition tree_rec (K : tree -> Set) := @tree_rect K.
Definition tree_ind K IH_leaf IH_node :=
  fix loop t : K t : Prop := match t with
  | Leaf x => IH_leaf x
  | Node n f0 =>
    let fix iter_conj f : foldr (fun t => and (K t)) True f :=
        if f is t :: f' then conj (loop t) (iter_conj f') else Logic.I
      in IH_node n f0 (iter_conj f0)
    end.

Fixpoint encode t : seq (nat + T) :=
  match t with
  | Leaf x => [:: inr _ x]
  | Node n f => inl _ n.+1 :: extend (flatten (map encode f)) (inl _ 0)
  end.

Definition decode_step c fs := 
  match c with
  | inr x => (Leaf x :: fs.1, fs.2)
  | inl 0 => ([::], fs.1 :: fs.2)
  | inl n.+1 => (Node n fs.1 :: head [::] fs.2, behead fs.2)
  end.

Definition decode c := ohead (foldr decode_step ([::], [::]) c).1.

Lemma codeK : pcancel encode decode.
Proof.
move=> t; rewrite /decode; set fs := (_, _).
suffices ->: foldr decode_step fs (encode t) = (t :: fs.1, fs.2) by [].
elim: t => //= n f IHt in (fs) *; elim: f IHt => //= t f IHf [].
by rewrite rcons_cat foldr_cat => -> /= /IHf[-> -> ->].
Qed.

End Def.

End GenTree.
Arguments GenTree.codeK : clear implicits.

Definition tree_eqMixin (T : eqType) := PcanEqMixin (GenTree.codeK T).
Canonical tree_eqType (T : eqType) := EqType (GenTree.tree T) (tree_eqMixin T).

(* Structures for Types with a choice function, and for Types with countably  *)
(* many elements. The two concepts are closely linked: we indeed make         *)
(* Countable a subclass of Choice, as countable choice is valid in CiC. This  *)
(* apparent redundancy is needed to ensure the consistency of the Canonical   *)
(* inference, as the canonical Choice for a given type may differ from the    *)
(* countable choice for its canonical Countable structure, e.g., for options. *)
(*   The Choice interface exposes two choice functions; for T : choiceType    *)
(* and P : pred T, we provide:                                                *)
(*    xchoose : (exists x, P x) -> T                                          *)
(*    choose : pred T -> T -> T                                               *)
(*   While P (xchoose exP) will always hold, P (choose P x0) will be true if  *)
(* and only if P x0 holds. Both xchoose and choose are extensional in P and   *)
(* do not depend on the witness exP or x0 (provided P x0 holds). Note that    *)
(* xchoose is slightly more powerful, but less convenient to use.             *)
(*   However, neither choose nor xchoose are composable: it would not be      *)
(* be possible to extend the Choice structure to arbitrary pairs using only   *)
(* these functions, for instance. Internally, the interfaces provides a       *)
(* subtly stronger operation, Choice.InternalTheory.find, which performs a    *)
(* limited search using an integer parameter only rather than a full value as *)
(* [x]choose does. This is not a restriction in a constructive theory, where  *)
(* all types are concrete and hence countable. In the case of an axiomatic    *)
(* theory, such as that of the Coq reals library, postulating a suitable      *)
(* axiom of choice suppresses the need for guidance. Nevertheless this        *)
(* operation is just what is needed to make the Choice interface compose.     *)
(*   The Countable interface provides three functions; for T : countType we   *)
(* get pickle : T -> nat, and unpickle, pickle_inv : nat -> option T.         *)
(* The functions provide an effective embedding of T in nat: unpickle is a    *)
(* left inverse to pickle, which satisfies pcancel pickle unpickle, i.e.,     *)
(* unpickle \o pickle =1 some; pickle_inv is a more precise inverse for which *)
(* we also have ocancel pickle_inv pickle. Both unpickle and pickle need to   *)
(* be partial functions to allow for possibly empty types such as {x | P x}.  *)
(*   The names of these functions underline the correspondence with the       *)
(* notion of "Serializable" types in programming languages.                   *)
(*   Finally, we need to provide a join class to let type inference unify     *)
(* subType and countType class constraints, e.g., for a countable subType of  *)
(* an uncountable choiceType (the issue does not arise earlier with eqType or *)
(* choiceType because in practice the base type of an Equality/Choice subType *)
(* is always an Equality/Choice Type).                                        *)

Module Choice.

Section ClassDef.

Record mixin_of T := Mixin {
  find : pred T -> nat -> option T;
  _ : forall P n, oapp P true (find P n);
  _ : forall P : pred T, (exists x, P x) -> exists n, find P n;
  _ : forall P Q n, subpred P Q -> 
        [/\ find P n ==> find Q n
          & oapp P false (find Q n) -> find P n = find Q n]
}.

Set Primitive Projections.
Record class_of T := Class {base : Equality.class_of T; mixin : mixin_of T}.
Unset Primitive Projections.
Local Coercion base : class_of >->  Equality.class_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.

Definition pack m :=
  fun b bT & phant_id (Equality.class bT) b => Pack (@Class T b m).

(* Inheritance *)
Definition eqType := @Equality.Pack cT class.

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> Equality.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Notation choiceType := type.
Notation choiceMixin := mixin_of.
Notation ChoiceType T m := (@pack T m _ _ id).
Notation "[ 'choiceType' 'of' T 'for' cT ]" :=  (@clone T cT _ idfun)
  (at level 0, format "[ 'choiceType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'choiceType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'choiceType'  'of'  T ]") : form_scope.

End Exports.

Module InternalTheory.
Section InternalTheory.
(* Inner choice function. *)
Definition find T := find (mixin (class T)).

Variable T : choiceType.
Implicit Types P Q : pred T.

Lemma correct P n : oapp P true (find P n).
Proof. by case: T => _ [_ []] //= in P n *. Qed.

Lemma findP P n x : find P n = Some x -> P x.
Proof. by move=> Dx; have:= correct P n; rewrite Dx. Qed.

Lemma complete P : (exists x, P x) -> (exists n, find P n).
Proof. by case: T => _ [_ []] //= in P *. Qed.

Lemma stable P Q n :
     subpred P Q ->
  [/\ find P n ==> find Q n
    & oapp P false (find Q n) -> find P n = find Q n].
Proof. by case: T => _ [_ []] //= in P Q n *. Qed.

Lemma extensional P Q : P =1 Q -> find P =1 find Q.
Proof.
move=> eqPQ n; have /(stable n)[]: subpred P Q by move=> x; rewrite eqPQ.
case: (find Q n) (correct Q n) => [x /= | ]; last by case: (find P n).
by rewrite eqPQ => -> _ ->.
Qed.

Fact xchoose_subproof P :
    (exists x, P x) ->
  {x | exists2 m, find P m = Some x & forall n, find P n -> m <= n}.
Proof. by case/complete/ex_minnP=> m; case Dx: find => // [x]; exists x, m. Qed.

End InternalTheory.
End InternalTheory.

End Choice.
Export Choice.Exports.

Lemma DecChoiceMixin `{classical_logic} T : Choice.mixin_of T.
Proof.
have [R Rwo] := well_ordering_principle T.
pose (minR A neA := exists_witness (Rwo A neA)).
pose (dec_ne (A : pred T) := decP (nonempty A)).
pose f A := if dec_ne A is ReflectT neA then Some (sval (minR A neA)) else None.
exists (fun A n => f A) => [A n | A neA | A B n sAB]; rewrite {}/f.
- by case: (dec_ne A) => //= neA; case: (minR _ _) => z /= [[Az _] _].
- by exists 0; case: (dec_ne A).
case: dec_ne (dec_ne B) => [neA | noA] [neB | noB] //=; first 1 last. 
- by have [x Ax] := neA; case: noB; exists x; apply: sAB.
- by move: (sval _) => x; split=> // Ax; case: noA; exists x.
case: (minR A _) => x [[Ax minAx] Ux]; case: minR => y /= [[By minBy] _].
by split=> // Ay; rewrite (Ux y) //; split=> // z /sAB/minBy.
Qed.
Definition DecChoiceType `{classical_logic} {T} :=
  [choiceType of T for ChoiceType DecEqType (DecChoiceMixin T)].

Section ChoiceTheory.

Implicit Type T : choiceType.
Import Choice.InternalTheory CodeSeq.
Local Notation dc := decode.

Section OneType.

Variable T : choiceType.
Implicit Types P Q : pred T.

Definition xchoose P exP := sval (@xchoose_subproof T P exP).

Lemma xchooseP P exP : P (@xchoose P exP).
Proof. by rewrite /xchoose; case: xchoose_subproof => x [m /= /findP]. Qed.

Lemma eq_xchoose P Q exP exQ : P =1 Q -> @xchoose P exP = @xchoose Q exQ.
Proof.
rewrite /xchoose => /extensional-eqPQ.
case: (xchoose_subproof exP) => x [m /= DfPm minPm]; rewrite eqPQ in DfPm.
case: (xchoose_subproof exQ) => y [n /= DfQn minQn].
apply/Some_inj; rewrite -DfPm (@anti_leq m n) //.
by rewrite minPm ?eqPQ ?DfQn // minQn ?DfPm.
Qed.

Lemma sigW P : (exists x, P x) -> {x | P x}.
Proof. by move=> exP; exists (xchoose exP); apply: xchooseP. Qed.

Lemma sig2W P Q : (exists2 x, P x & Q x) -> {x | P x & Q x}.
Proof.
move=> exPQ; have [|x /andP[]] := @sigW (predI P Q); last by exists x.
by have [x Px Qx] := exPQ; exists x; apply/andP.
Qed.

Lemma sig_eqW (vT : eqType) (lhs rhs : T -> vT) :
  (exists x, lhs x = rhs x) -> {x | lhs x = rhs x}.
Proof.
move=> exP; suffices [x /eqP-Ex]: {x | lhs x == rhs x} by exists x.
by apply: sigW; have [x /eqP Ex] := exP; exists x.
Qed.

Lemma sig2_eqW (vT : eqType) (P : pred T) (lhs rhs : T -> vT) :
  (exists2 x, P x & lhs x = rhs x) -> {x | P x & lhs x = rhs x}.
Proof.
move=> exP; suffices [x Px /eqP-Ex]: {x | P x & lhs x == rhs x} by exists x.
by apply: sig2W; have [x Px /eqP-Ex] := exP; exists x.
Qed.

Definition choose P x0 :=
  if insub x0 : {? x | P x} is Some (exist x Px) then
    xchoose (ex_intro [eta P] x Px)
  else x0.

Lemma chooseP P x0 : P x0 -> P (choose P x0).
Proof. by move=> Px0; rewrite /choose insubT xchooseP. Qed.

Lemma choosePeq P x0 : P (choose P x0) = P x0.
Proof. by case Px0: (P x0); [rewrite chooseP | rewrite /choose insubF]. Qed.

Lemma choose_id P x0 y0 : P x0 -> P y0 -> choose P x0 = choose P y0.
Proof. by move=> Px0 Py0; rewrite /choose !insubT /=; apply: eq_xchoose. Qed.

Lemma eq_choose P Q : P =1 Q -> choose P =1 choose Q.
Proof.
rewrite /choose => eqPQ x0.
do [case: insubP; rewrite eqPQ] => [[x Px] Qx0 _| ?]; last by rewrite insubN.
by rewrite insubT; apply: eq_xchoose.
Qed.

Variant xchoose_spec P : T -> Type :=
  XchooseSpec x of P x & (forall y, P y -> choose P y = x) : xchoose_spec P x.

Lemma xchooseEchoose P exP : xchoose_spec P (@xchoose P exP).
Proof.
split=> [|y Py]; first exact: xchooseP.
by rewrite /choose insubT //=; apply: eq_xchoose.
Qed.

Definition prec_eq x y := choose (pred2 x y) x == x.

Definition prec x y := (x != y) && prec_eq x y.

Lemma prec_irreflexive : irreflexive prec.
Proof. by move=> x; rewrite /prec eqxx. Qed.

Lemma precW x y : prec x y -> prec_eq x y. Proof. by case/andP. Qed.

Lemma precNge x y : prec x y = ~~ prec_eq y x.
Proof.
rewrite /prec /prec_eq; set xy := pred2 x y; set z := choose xy x.
rewrite -(@eq_choose xy) => [|? /=]; last by rewrite orbC.
rewrite -(@choose_id xy x) /= ?eqxx ?orbT // -/z andbC eq_sym.
by have /pred2P[]: xy z => [|->|->]; rewrite ?chooseP //= eqxx ?andbN.
Qed.

Lemma prec_eqNgt x y : prec_eq x y = ~~ prec y x.
Proof. by rewrite precNge negbK. Qed.

Lemma prec_eq_reflexive : reflexive prec_eq.
Proof. by move=> x; rewrite prec_eqNgt prec_irreflexive. Qed.

Lemma prec_eqVprec x y : prec_eq x y = (x == y) || prec x y.
Proof. by rewrite /prec; case: eqP => // ->; apply: prec_eq_reflexive. Qed.

Lemma prec_eq_total x y : prec_eq x y || prec_eq y x.
Proof. by rewrite prec_eqVprec precNge -orbA orNb orbT. Qed.

Lemma prec_eq_antisymmetric : antisymmetric prec_eq.
Proof.
by move=> x y; rewrite prec_eqVprec precNge; case: eqP; rewrite ?andNb.
Qed.

Lemma prec_antisymmetric : antisymmetric prec.
Proof. by move=> x y; rewrite precNge andbCA andNb andbF. Qed.

Lemma choose_stable P Q x :
  subpred P Q -> P x -> P (choose Q x) -> choose P x = choose Q x.
Proof.
move=> sPQ Px; have Qx: Q x by [rewrite sPQ]; rewrite /choose !insubT /=.
rewrite /xchoose; case: xchoose_subproof => y [m /= Dy minQm].
case: xchoose_subproof => z [n /= Dz minPn] Py.
have [[_ EfPQm] [/implyP-sfPQn _]] := (stable m sPQ, stable n sPQ).
suffices Dm: m = n by apply/Some_inj; rewrite -Dz -Dm EfPQm Dy.
by apply/anti_leq; rewrite minPn ?EfPQm ?Dy // minQm ?sfPQn ?Dz. 
Qed.

Lemma choose_prec_eq P x0 y :
  P x0 -> P y -> prec_eq (choose P x0) y.
Proof.
move=> Px0 Py; apply/eqP; set x := choose P x0; set xy := pred2 x y.
have Dx: x = choose P x by apply: choose_id; rewrite ?chooseP.
rewrite [RHS]Dx; apply: choose_stable => [z||]; rewrite -?Dx /= ?eqxx //.
by case/pred2P=> -> //; rewrite chooseP.
Qed.

Lemma prec_eq_well : well_order prec_eq.
Proof.
move=> A [x Ax]; exists (choose A x); split=> [|y [Ay minAy]].
  by split=> [|y]; [apply: chooseP | apply: choose_prec_eq].
by apply/prec_eq_antisymmetric; rewrite minAy ?choose_prec_eq ?[_ \in A]chooseP.
Qed.

Lemma prec_eq_trans : transitive prec_eq.
Proof. by case/well_order_total/total_orderE: prec_eq_well. Qed.

Lemma prec_eq_prec_trans y x z : prec_eq x y -> prec y z -> prec x z.
Proof. by rewrite !precNge => lexy; apply/contra=> /prec_eq_trans->. Qed.

Lemma prec_prec_eq_trans y x z : prec x y -> prec_eq y z -> prec x z.
Proof. by rewrite !precNge => /contra-ltxy leyz; apply/ltxy/prec_eq_trans. Qed.

Lemma prec_trans : transitive prec.
Proof. by move=> y x z /precW; apply: prec_eq_prec_trans. Qed.

Section CanChoice.

Variables (sT : Type) (f : sT -> T).

Lemma PcanChoiceMixin f' : pcancel f f' -> choiceMixin sT.
Proof.
move=> fK; pose liftP sP := [pred x | oapp sP false (f' x)].
pose sf sP := [fun n => obind f' (find (liftP sP) n)].
exists sf => [sP n | sP [y sPy] | sP sQ n ssPQ] /=.
- by have:= correct (liftP sP) n; case: find => //= x; case: (f' x).
- have [|n Pn] := @complete T (liftP sP); first by exists (f y); rewrite /= fK.
  exists n; case Df: (find _ n) Pn => //= [x] _.
  by have:= findP Df => /=; case: (f' x).
have: subpred (liftP sP) (liftP sQ) by move=> x /=; case: (f' x).
case/(stable n)=> sfPQ EfPQ; split=> [|PfQn]; last first.
   by rewrite EfPQ //; case: find PfQn.
case Dx: find sfPQ => //= [x]; case Dy: find => //= [y] _.
by apply/implyP=> _; have /findP/= := Dy; case: (f' y).
Qed.

Definition CanChoiceMixin f' (fK : cancel f f') :=
  PcanChoiceMixin (can_pcan fK).

End CanChoice.

Section SubChoice.

Variables (P : pred T) (sT : subType P).

Definition sub_choiceMixin := PcanChoiceMixin (@valK T P sT).
Definition sub_choiceClass := @Choice.Class sT (sub_eqMixin sT) sub_choiceMixin.
Canonical sub_choiceType := Choice.Pack sub_choiceClass.

End SubChoice.

Fact seq_choiceMixin : choiceMixin (seq T).
Proof.
pose r f := [fun xs => fun x : T => f (x :: xs) : option (seq T)].
pose fix f sP ns xs {struct ns} :=
  if ns is n :: ns1 then let fr := r (f sP ns1) xs in obind fr (find fr n)
  else if sP xs then Some xs else None.
exists (fun sP nn => f sP (dc nn) nil) => [sP n | sP [ys] | sP sQ n ssPQ].
- elim: {n}(dc n) nil => [|n ns IHs] xs /=; first by case: ifP => // sPxs [<-].
  by case: (find _ n) => //= [x]; apply: IHs.
- rewrite -(cats0 ys); elim/last_ind: ys nil => [|ys y IHs] xs /=.
    by move=> sPxs; exists 0; rewrite /= sPxs.
  rewrite cat_rcons => /IHs[n1 sPn1] {IHs}.
  have /complete[n]: exists z, f sP (dc n1) (z :: xs) by exists y.
  case Df: (find _ n)=> // [x] _; exists (code (n :: dc n1)).
  by rewrite codeK /= Df /= (findP Df).
elim: {n}(dc n) nil => [|n ns IHs] xs /=.
  by do [split; case: ifP] => //= [/ssPQ-> | _ ->].
have: subpred (fun x => f sP ns (x :: xs)) (fun x => f sQ ns (x :: xs)).
  by move=> x /=; have [/implyP] := IHs (x :: xs). 
case/(stable n) => srfPQ ErfPQ.
split.
  apply/implyP; case Dy: find srfPQ => //= [x].
  by case Dz: find => //= [y]; move/findP: Dz.
case Dx: find => //= [x] Pfx; have [_ /(_ Pfx)EfPQ] := IHs (x :: xs).
by rewrite ErfPQ; rewrite Dx /= EfPQ //; case: (f) Pfx.
Qed.
Canonical seq_choiceType := Eval hnf in ChoiceType (seq T) seq_choiceMixin.

End OneType.

Section TagChoice.

Variables (I : choiceType) (T_ : I -> choiceType).

Fact tagged_choiceMixin : choiceMixin {i : I & T_ i}.
Proof.
pose mkT i (x : T_ i) := Tagged T_ x.
pose ft P n := [fun i => omap (mkT i) (find (P \o mkT i) n)].
pose fi P := [fun ni nt => obind (ft P nt) (find [pred i | ft P nt i] ni)].
pose f P := [fun n => if dc n is [:: ni; nt] then fi P ni nt else None].
exists f => [P n | P [[i x] /= Px] | P Q n sPQ] /=.
- case: (dc n) => [|ni [|nt []]] //=; case: (find _ _) => //= [i].
  by case Df: (find _ _) => //= [x]; have:= findP Df.
- have /complete[nt Pnt]: exists y, (P \o mkT i) y by exists x.
  have{Pnt}: exists j, ft P nt j by exists i => /=; case: find Pnt.
  case/complete=> ni Pn; exists (code [:: ni; nt]); rewrite /f codeK /=.
  by case Df: find Pn => //= [j] _; have:= findP Df.
case: (dc n) => [|ni [|nt []]] //=.
have sPQi i: subpred (P \o mkT i) (Q \o mkT i) by move=> x /sPQ.
have /(stable ni)[sftPQi EftPQi]: subpred [eta ft P nt] [eta ft Q nt].
  move=> i /=; have [+ _] := stable nt (sPQi i).
  by case: find => //= [x]; case: find.
split.
  case Dx: find sftPQi => //= [x]; case Dy: find => //= [y] _.
  by apply/implyP=> _; move/findP: Dy.
case Di: find => //= [i]; case Dx: find => //= [x] Px.
by have [_ EfPQi] := stable nt (sPQi i); rewrite EftPQi Di /= EfPQi Dx.
Qed.
Canonical tagged_choiceType :=
  Eval hnf in ChoiceType {i : I & T_ i} tagged_choiceMixin.

End TagChoice.

Fact nat_choiceMixin : choiceMixin nat.
Proof.
pose f := [fun (P : pred nat) n => if P n then Some n else None].
exists f => [P n | P [n Pn] | P Q n sPQ] /=; first by case: ifP.
  by exists n; rewrite Pn.
by split; [case: ifP => // /sPQ-> | case: (Q n) => //= ->].
Qed.
Canonical nat_choiceType := Eval hnf in ChoiceType nat nat_choiceMixin.

Definition bool_choiceMixin := CanChoiceMixin oddb.
Canonical bool_choiceType := Eval hnf in ChoiceType bool bool_choiceMixin.
Canonical bitseq_choiceType := Eval hnf in [choiceType of bitseq].

Definition unit_choiceMixin := CanChoiceMixin bool_of_unitK.
Canonical unit_choiceType := Eval hnf in ChoiceType unit unit_choiceMixin.

Definition void_choiceMixin := PcanChoiceMixin (of_voidK unit).
Canonical void_choiceType := Eval hnf in ChoiceType void void_choiceMixin.

Definition option_choiceMixin T := CanChoiceMixin (@seq_of_optK T).
Canonical option_choiceType T :=
  Eval hnf in ChoiceType (option T) (option_choiceMixin T).

Definition sig_choiceMixin T (P : pred T) : choiceMixin {x | P x} :=
   sub_choiceMixin _.
Canonical sig_choiceType T (P : pred T) :=
 Eval hnf in ChoiceType {x | P x} (sig_choiceMixin P).

Definition prod_choiceMixin T1 T2 := CanChoiceMixin (@tag_of_pairK T1 T2).
Canonical prod_choiceType T1 T2 :=
  Eval hnf in ChoiceType (T1 * T2) (prod_choiceMixin T1 T2).

Definition sum_choiceMixin T1 T2 := PcanChoiceMixin (@opair_of_sumK T1 T2).
Canonical sum_choiceType T1 T2 :=
  Eval hnf in ChoiceType (T1 + T2) (sum_choiceMixin T1 T2).

Definition tree_choiceMixin T := PcanChoiceMixin (GenTree.codeK T).
Canonical tree_choiceType T := ChoiceType (GenTree.tree T) (tree_choiceMixin T).

End ChoiceTheory.

Prenex Implicits xchoose choose.
Notation "[ 'choiceMixin' 'of' T 'by' <: ]" :=
  (sub_choiceMixin _ : choiceMixin T)
  (at level 0, format "[ 'choiceMixin'  'of'  T  'by'  <: ]") : form_scope.

Module Countable.

Record mixin_of (T : Type) : Type := Mixin {
  pickle : T -> nat;
  unpickle : nat -> option T;
  pickleK : pcancel pickle unpickle
}.

Definition EqMixin T m := PcanEqMixin (@pickleK T m).
Definition ChoiceMixin T m := PcanChoiceMixin (@pickleK T m).

Section ClassDef.

Set Primitive Projections.
Record class_of T := Class { base : Choice.class_of T; mixin : mixin_of T }.
Unset Primitive Projections.
Local Coercion base : class_of >-> Choice.class_of.

Structure type : Type := Pack {sort : Type; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.

Definition pack m :=
  fun bT b & phant_id (Choice.class bT) b => Pack (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Choice.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Notation countType := type.
Notation CountType T m := (@pack T m _ _ id).
Notation CountMixin := Mixin.
Notation CountChoiceMixin := ChoiceMixin.
Notation "[ 'countType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
 (at level 0, format "[ 'countType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'countType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'countType'  'of'  T ]") : form_scope.

End Exports.

End Countable.
Export Countable.Exports.

Definition unpickle T := Countable.unpickle (Countable.class T).
Definition pickle T := Countable.pickle (Countable.class T).
Arguments unpickle {T} n.
Arguments pickle {T} x.

Section CountableTheory.

Variable T : countType.

Lemma pickleK : @pcancel nat T pickle unpickle.
Proof. exact: Countable.pickleK. Qed.

Definition pickle_inv n :=
  obind (fun x : T => if pickle x == n then Some x else None) (unpickle n).

Lemma pickle_invK : ocancel pickle_inv pickle.
Proof.
by rewrite /pickle_inv => n; case def_x: (unpickle n) => //= [x]; case: eqP.
Qed.

Lemma pickleK_inv : pcancel pickle pickle_inv.
Proof. by rewrite /pickle_inv => x; rewrite pickleK /= eqxx. Qed.

Lemma pcan_pickleK sT f f' :
  @pcancel T sT f f' -> pcancel (pickle \o f) (pcomp f' unpickle).
Proof. by move=> fK x; rewrite /pcomp pickleK /= fK. Qed.

Definition PcanCountMixin sT f f' (fK : pcancel f f') :=
  @CountMixin sT _ _ (pcan_pickleK fK).

Definition CanCountMixin sT f f' (fK : cancel f f') :=
  @PcanCountMixin sT _ _ (can_pcan fK).

Definition sub_countMixin P sT := PcanCountMixin (@valK T P sT).

Definition pickle_seq s := CodeSeq.code (map (@pickle T) s).
Definition unpickle_seq n := Some (pmap (@unpickle T) (CodeSeq.decode n)).
Lemma pickle_seqK : pcancel pickle_seq unpickle_seq.
Proof. by move=> s; rewrite /unpickle_seq CodeSeq.codeK (map_pK pickleK). Qed.

Definition seq_countMixin := CountMixin pickle_seqK.
Canonical seq_countType := Eval hnf in CountType (seq T) seq_countMixin.

End CountableTheory.

Notation "[ 'countMixin' 'of' T 'by' <: ]" :=
    (sub_countMixin _ : Countable.mixin_of T)
  (at level 0, format "[ 'countMixin'  'of'  T  'by'  <: ]") : form_scope.

Arguments pickle_inv {T} n.
Arguments pickleK {T} x.
Arguments pickleK_inv {T} x.
Arguments pickle_invK {T} n : rename.

Section SubCountType.

Variables (T : choiceType) (P : pred T).
Import Countable.

Structure subCountType : Type :=
  SubCountType {subCount_sort :> subType P; _ : mixin_of subCount_sort}.

Coercion sub_countType (sT : subCountType) :=
  Eval hnf in pack (let: SubCountType _ m := sT return mixin_of sT in m) id.
Canonical sub_countType.

Definition pack_subCountType U :=
  fun sT cT & sub_sort sT * sort cT -> U * U =>
  fun b m   & phant_id (Class b m) (class cT) => @SubCountType sT m.

End SubCountType.

(* This assumes that T has both countType and subType structures. *)
Notation "[ 'subCountType' 'of' T ]" :=
    (@pack_subCountType _ _ T _ _ id _ _ id)
  (at level 0, format "[ 'subCountType'  'of'  T ]") : form_scope.

Section TagCountType.

Variables (I : countType) (T_ : I -> countType).

Definition pickle_tagged (u : {i : I & T_ i}) :=
  CodeSeq.code [:: pickle (tag u); pickle (tagged u)].
Definition unpickle_tagged s :=
  if CodeSeq.decode s is [:: ni; nx] then
    obind (fun i => omap (@Tagged I i T_) (unpickle nx)) (unpickle ni)
  else None.
Lemma pickle_taggedK : pcancel pickle_tagged unpickle_tagged.
Proof.
by case=> i x; rewrite /unpickle_tagged CodeSeq.codeK /= pickleK /= pickleK.
Qed.

Definition tag_countMixin := CountMixin pickle_taggedK.
Canonical tag_countType := Eval hnf in CountType {i : I & T_ i} tag_countMixin.

End TagCountType.

(* The remaining Canonicals for standard datatypes. *)
Section CountableDataTypes.

Implicit Type T : countType.

Lemma nat_pickleK : pcancel id (@Some nat). Proof. by []. Qed.
Definition nat_countMixin := CountMixin nat_pickleK.
Canonical nat_countType := Eval hnf in CountType nat nat_countMixin.

Definition bool_countMixin := CanCountMixin oddb.
Canonical bool_countType := Eval hnf in CountType bool bool_countMixin.
Canonical bitseq_countType :=  Eval hnf in [countType of bitseq].

Definition unit_countMixin := CanCountMixin bool_of_unitK.
Canonical unit_countType := Eval hnf in CountType unit unit_countMixin.

Definition void_countMixin := PcanCountMixin (of_voidK unit).
Canonical void_countType := Eval hnf in CountType void void_countMixin.

Definition option_countMixin T := CanCountMixin (@seq_of_optK T).
Canonical option_countType T :=
  Eval hnf in CountType (option T) (option_countMixin T).

Definition sig_countMixin T (P : pred T) := [countMixin of {x | P x} by <:].
Canonical sig_countType T (P : pred T) :=
  Eval hnf in CountType {x | P x} (sig_countMixin P).
Canonical sig_subCountType T (P : pred T) :=
  Eval hnf in [subCountType of {x | P x}].

Definition prod_countMixin T1 T2 := CanCountMixin (@tag_of_pairK T1 T2).
Canonical prod_countType T1 T2 :=
  Eval hnf in CountType (T1 * T2) (prod_countMixin T1 T2).

Definition sum_countMixin T1 T2 := PcanCountMixin (@opair_of_sumK T1 T2).
Canonical sum_countType T1 T2 :=
  Eval hnf in CountType (T1 + T2) (sum_countMixin T1 T2).

Definition tree_countMixin T := PcanCountMixin (GenTree.codeK T).
Canonical tree_countType T := CountType (GenTree.tree T) (tree_countMixin T).

End CountableDataTypes.

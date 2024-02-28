(* (c) Copyright 2024 Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import path div.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*  Tests for unification order and priorities. *)

Structure tag1 := MkTag1 {untag1 : unit}.
Definition untag1d := untag1.
Canonical Tag1 u := MkTag1 u.
Structure tag2 := MkTag2 {untag2 : unit}.
Definition untag2d := untag2.
Canonical Tag2 u := MkTag2 u.
Structure testS (u : unit) := TestS { projTest : Prop -> Prop }.
Arguments projTest : clear implicits.
Definition HD (u0 u : unit) A := A /\ A.
Definition HP (u0 u : unit) A := A /\ A.
Definition Dpat u1 t2 u := TestS u1 (HD (untag1d t2) u).
Definition Ppat u1 t2 u := TestS u1 (HP (untag1 t2) u).
Canonical Dtest t1 t2 u := Dpat (untag1d t1) t2 u.
Canonical Ptest t1 t2 u := Ppat (untag1 t1) t2 u.
Structure testB := TestB { projB : bool }.
Definition testN b := negb b.
Canonical NtestB b := TestB (testN b).

Goal False.
pose D (x : unit) := True.
have a1 : D (untag1 _) by [].
have a2 : D (untag2 _) by [].
(* unfold in EXPECTED type before INFERRED type *)
pose A (a : D (untag1d _)) := a : D (untag2d _).
(* prioritize solving projection in INFERRED type over those in EXPECTED type *)
pose B := a1 _ : D (untag2 _).
(* unify arguments LEFT TO RIGHT *)
pose C (K : forall x, D x * D x -> Prop) := K _ (a1 _, a2 _).
(* resolve projections in rewrite RULE before REDEX *)
have E (e : forall u, D (untag1 u) = (u = u))
       (H : forall u, ~ D (untag2 u)) : False.
  refine (H _ _). rewrite e. split.
(* unfold in rewrite REDEX before RULE *)
have E' (e : forall u, D (untag1d u) = (u = u)): D (untag2d _).
  rewrite e. split.
(* unfold in INSTANCE parameters before unfolding in PROJECTION parameters   *)
(* unfold in INSTANCE field arguments before unfolding in VALUE arguments    *)
(* unfold in INSTANCE structure before unfolding in PROJECTION structure arg *)
(* unfold in VALUE extra args before unfolding in PROJECTION extraargs       *)
pose FD (a : HD (untag2d _) (untag1d _) (D (untag2d _))) :=
  a : projTest (untag2d _) (Dpat _ _ (untag2d _)) (D (untag1d _)).
(* canonical structure resolution priority for projections                *)
(*    - in PROJECTION parameters over those in INSTANCE parameters        *)
(*    - in VALUE arguments over those in INSTANCE field arguments         *)
(*    - in PROJECTION structure argument over those in INSTANCE structure *)
(*    - in PROJECTION extraargs over those in VALUE extra args            *)
pose FP (a : HP (untag2 _) (untag1 _) (D (untag2 _))) :=
  a : projTest (untag2 _) (Ppat _ _ (untag2 _)) (D (untag1 _)).
(* canonical structures are not recognized in the condition of an "if" *)
pose ite b := if b then tt else tt.
have b0 : bool := true.
pose Fok (a : D (ite (projB _))) := a : D (ite (testN b0)).
pose Ffail0 (a : D (if projB _ then tt else tt)) :=
  a : D (if testN b0 then tt else tt).
pose Ffail1 (a : D (ite (projB _))) := a : D (if testN b0 then tt else tt).
pose Ffail2 (a : D (if testN b0 then tt else tt)) := a : D (ite (projB _)). 
Abort.

(* A structure that matches an arbitrayry (possible dependent) function.      *)
(*   It can be used to decompose an arbitrary application (?f ?a) using the   *)
(* pattern (?ef ?a) where ?ef : funPattern ?f. Note that the simple (?f ?a)   *)
(* pattern cannot reliably be used for this purpose, because the unification  *)
(* algorithm interprets this as a second-order pattern, unfolding the matchee *)
(* an even deferring the constraint.                                          *)
(*   We use a special case of this pattern to force unification priority.     *)
(* Matching (?m ?p) to (MatchArg a) when ?m : matchArg will match a to ?p     *)
(* giving priority to ?p for canonical structure resolution. In particular    *)
(* we can use this to give priority to the value pattern C ?p1 ... ?pn of     *)
(* a canonical instance, as opposed to the matched value C a1 .. an, which is *)
(* the default and problematic if some of the ai are themselves projections,  *)
(* particularly projections with a default instance.                          *)
Structure matchArg {T} := DeclareMatchArg { apply_match_arg :> T -> T }.
Add Printing Constructor matchArg.
Definition MatchArg {T} : T -> T := id.
Canonical MatchArgPattern T := @DeclareMatchArg T MatchArg.

(* Should work when CS resolution bug is fixed.
Structure funPattern A R (f : forall a : A, R a) :=
  FunPattern { apply_fun_pattern :> forall a, R a }.
Add Printing Constructor funPattern.
Definition MatchArg {T} := @id T.
Definition matchArg {T} := funPattern (@MatchArg T).
Identity Coercion pattern_of_matchArg : matchArg >-> funPattern.
Canonical MatchFunPattern A R f := @FunPattern A R f f.
*)

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

(*       infer_type t :: When t : inferType T is unconstrained, this pattern  *)
(*                       will unify with any e : T while instantiating T to   *)
(*                       the actual inferred type of e.                       *)
(*  *** This is useful because Coq usually defers unification constraints     *)
(*      that arise from the types of unification variables. Using infer_type  *)
(*      allows the synchronous resolution of structures such as forallSort    *)
(*      that depend on types.                                                 *)

Structure inferType T := BuildInferType {infer_type : T}.
Canonical InferType {T} x := @BuildInferType T x.

(* Sundry ssrfun additions. *)

Arguments tag_of_tag2 {_ _ _} _.
Definition tag2_of_tag {I T1_ T2_} (z : {x : I & T1_ x * T2_ x}%type) :=
  let y := tagged z in Tagged2 T1_ T2_ y.1 y.2.

Lemma tag_of_tag2K {I T1_ T2_} : cancel (@tag_of_tag2 I T1_ T2_) tag2_of_tag.
Proof. by case. Qed.

Lemma tag2_of_tagK {I T1_ T2_} : cancel tag2_of_tag (@tag_of_tag2 I T1_ T2_).
Proof. by case=> ? []. Qed.

(* End of ssrfun complements. *)

(* Corresponding eqtype additions. *)

#[hnf] HB.instance Definition _ (I : eqType) (T1_ T2_ : I -> eqType) :=
   Equality.copy {i : I & T1_ i & T2_ i} (can_type tag_of_tag2K).

Definition otagged_at {I : eqType} {i T_} (w : {i : I & T_ i}) :=
  if tag w =P i isn't ReflectT Ewi then None else
  ecast i (option (T_ i)) Ewi (Some (tagged w)).

Lemma TaggedK {I : eqType} {i T_} : pcancel (@Tagged I i T_) otagged_at.
Proof.
by rewrite /otagged_at => y; case: eqP => //= Eii; rewrite eq_axiomK.
Qed.

Lemma Tagged2K {I : eqType} {i T1_ T2_ y1} :
  pcancel (@Tagged2 I i T1_ T2_ y1) (omap snd \o otagged_at \o tag_of_tag2).
Proof. by move=> y2; rewrite /= TaggedK. Qed.

(* End of eqtype complements. *)

(*   This module provides facilities for handling (boolean) predicates with   *)
(* finite support, i.e., for which an explicit list of the values for which   *)
(* the predicate holds can given. These facilities include an extensive and   *)
(* extensible infrastructure for inferring this support. We always assume     *)
(* the type T of values has Equality, but as noted some of the operations and *)
(* theory also need T to have Choice. We define                               *)
(*   {finpred T} == the type of predicates with finite support. This type     *)
(*                  coerces to {pred T}, and this coercion will unify with    *)
(*                  many predicates that have finite support, thereby         *)
(*                  inferring said support (see list below).                  *)
(*     finpred T == the representation type for predicates with finite        *)
(*                  support. This type is used to declare arguments of        *)
(*                  finpred operations. Predicates P with finite support will *)
(*                  coerce or reverse coerce to finpred T, but the resulting  *)
(*                  finpred may not preserve the shape of P - it can present  *)
(*                  a predicate P' convertible but not identical to P.        *)
(*                  ***For this reason {finpred T} should always be used      *)
(*                  for declaring lemma contexts.***                          *)
(* card P, #|P| == the cardinal of the support of a finpred P.                *)
(*     pred0b P == the finpred P is empty (always false).                     *)
(*    P \subset Q <=> the finpred P is a subset of the (plain) predicate Q    *)
(*    P \proper Q <=> the finpred P is a proper subset of the finpred Q.      *)
(*    support P == the support of a finpred P, i.e., a duplicate-free         *)
(*                 sequence of the values on which P holds. Note that suppprt *)
(*                 is NOT extensional: support P and support Q may differ for *)
(*                 equivalent (or even convertible!) P and Q.                 *)
(*       enum P == a standard enumeration of the support of P, using a Choice *)
(*                 structure on T; this is both extensional and stable -      *)
(*                 enum P is a subsequence of enum Q when {subset P <= Q}     *)
(*       pick P == Some standard x such that P x, or None if P is empty.      *)
(*                 pick P is extensional and requires Choice on T.            *)
(*                                                                            *)
(* Shape of predicates that can be inferred as finpred's                      *)
(* (T : choiceType unless stated otherwise):                                  *)
(* - [pred x in P]                       with P : finpred T                   *)
(* - [pred x | P x && Q x]               with P : finpred T or Q : finpred T  *)
(*   e.g., [pred x | ([in P] x) && Q x] with P : finpred T                    *)
(* - [pred x | (x \in P) || (x \in Q)]   with P, Q : finpred T                *)
(* - [pred x | P x]                      with P : pred T and T : finType      *)
(* - [pred x : T | def x ]               where def's sort can be inferred to  *)
(*                                       be of type finPred T                 *)
(*                                                                            *)

Record finpredEnvelope (T : eqType) (P : {pred T}) :=
  FinpredEnvelope {envelope_seq :> seq T; _ : {subset P <= envelope_seq}}.

#[projections(primitive)]
Structure labeledPred (T : eqType) := LabelPred {mem_labeled :> {pred T}}.

#[projections(primitive)]
Record finpred T := PackFinpred {
  #[reversible=no] mem_finpred :> labeledPred T;
  envelope : finpredEnvelope mem_finpred
}.
Add Printing Constructor finpred.
Arguments PackFinpred {T} P F : rename.
Definition Finpred T P (F : @finpredEnvelope T P) :=
 PackFinpred (LabelPred P) F.
Arguments Finpred {T} P F.

HB.lock Definition support {T} (F : finpred T) :=
  undup (filter [in F] (envelope F)).
Canonical support_unlockable := Unlockable support.unlock.

Lemma support_uniq T F : uniq (@support T F).
Proof. by rewrite support.unlock undup_uniq. Qed.
#[export] Hint Resolve support_uniq : core.

Lemma mem_support T F : @support T F =i F.
Proof.
case: F => F [s sFs] x.
by rewrite support.unlock mem_undup mem_filter; apply/andb_idr/sFs.
Qed.
Local Definition inE := (mem_support, inE).

Lemma eq_support T (F1 F2 : finpred T) :
  F1 =i F2 <-> perm_eq (support F1) (support F2).
Proof.
split=> [eqF | /perm_mem-eqF x]; last by rewrite -!mem_support.
by apply/uniq_perm=> // x; rewrite !inE.
Qed.

Structure inferFinpred (T : eqType) (P : {pred T}) (F : finpred T) :=
  InferFinpred { finpred_pilot :> bool }.

Definition TryCoercedFinpred T := @id (labeledPred T).
Definition TryInferFinpred T (P0 : labeledPred T) :=
  fun (P1 P2 : {pred T}) & finpredEnvelope P2 => P0.
Canonical LabelPatternFinpred T P F eF :=
  let pF x := @finpred_pilot T P F (eF x) in
  TryCoercedFinpred (TryInferFinpred (LabelPred P) pF (envelope F)).

Structure coercedFinpred (T : eqType) := CoercedFinpred {
  pred_of_coerced :> {pred T};
  #[canonical=no] envelope_of_coerced : finpredEnvelope pred_of_coerced
}.
Notation DeclareCoercedFinpred P F := (@CoercedFinpred _ P (envelope F)).

Coercion FinpredOfCoerced T (A : coercedFinpred T) :=
  PackFinpred (TryCoercedFinpred (LabelPred [eta pred_of_coerced A]))
              (envelope_of_coerced A).
Canonical FinpredOfCoerced.

Definition TryFinType := @id bool.
Definition TryIfThenElse := TryFinType.
Definition TryOp := TryIfThenElse.
Definition TryFalse b := TryOp (MatchArg b).

Canonical InferredFinpred T P (P0 := @LabelPred T P) eF :=
  PackFinpred (TryInferFinpred P0 (fun x => TryFalse (P x)) eF) eF.
Arguments InferredFinpred {T} P eF.
Notation "P" := (InferredFinpred P _) (at level 8, only printing) : form_scope.

Variant finpredTarget (T : eqType) :=
  FinpredTarget (P0 P1 P2 : {pred T}) of finpred T.
#[reversible=yes] Coercion target_of_finpred T P (F : finpred T) :=
  FinpredTarget P P (fun x => TryFalse (P x)) F.
#[reversible=yes] Coercion pred_finpred_target T P F eF P0 :=
  @FinpredTarget T P0 P (fun x => @finpred_pilot T P F (eF x)) F.

#[projections(primitive)]
Structure labeledFinpred T :=
  LabelFinpred {#[reversible=no] unlabel_finpred :> finpred T}.
Canonical LabelInferredFinpred T P eF :=
  LabelFinpred (@InferredFinpred T P eF).
Canonical LabelCoercedFinpred T F := LabelFinpred (@FinpredOfCoerced T F).
Canonical DefaultLabeledFinpred T F := @LabelFinpred T F.

#[projections(primitive)]
Structure finpredPattern (T : eqType) (phT : phant T) :=
  PackFinpredPattern {finpred_of_pattern :> labeledFinpred T}.
Definition FinpredPattern {T} := @PackFinpredPattern T (Phant T).
Notation "{ 'finpred' T }" := (finpredPattern (Phant T))
   (at level 0, T at level 100, format "{ 'finpred'  T }") : type_scope.
Canonical InferredFinpredPattern T P eF :=
  FinpredPattern (@LabelInferredFinpred T P eF).
Notation "P" := (@InferredFinpredPattern _ P _)
  (at level 8, only printing) : form_scope.
Definition finpredPatternDisplayTarget (T : eqType) := {finpred T}.
Coercion CoercedFinpredPattern T F :=
  FinpredPattern (@LabelCoercedFinpred T F).
Canonical CoercedFinpredPattern.
Coercion DefaultFinpredPattern T F :=
  FinpredPattern (@DefaultLabeledFinpred T F) : finpredPatternDisplayTarget T.
Canonical DefaultFinpredPattern.

Variant finpredPatternTarget (T : eqType) := FinpredPatternTarget of {pred T}.
#[reversible=yes] Coercion target_of_finpred_pattern T phT :=
  fun F : @finpredPattern T phT =>  FinpredPatternTarget F.
#[reversible=yes] Coercion finpred_pattern_target_of_pred T P :=
  @FinpredPatternTarget T P.

Structure coerciblePredType T := CoerciblePredType {
  coerciblePredType_sort :> Type;
  #[canonical=no] coerce_sort_to_pred : coerciblePredType_sort -> {pred T}
}.
Coercion coerce_sort_to_pred : coerciblePredType_sort >-> pred_sort.
Definition TryPredType := @id Type.
Canonical PredTypeCoercible T (pT : predType T) :=
  @CoerciblePredType T (TryPredType pT) (@topred T pT).

Definition LabeledFinpredReverseCoercion
           T pT (P0 : pT) (P : labeledPred T) (F : @finpredEnvelope T P) F0 :=
  @LabelFinpred T (reverse_coercion F0 P0).
Canonical LabelFinpredReverseCoercion T pT P0 (F : finpred T) :=
  @LabeledFinpredReverseCoercion T (TryPredType pT) P0 F (envelope F) F.
Canonical FinpredReverseCoercionPattern T pT P0 eF :=
  let F := @PackFinpred T (LabelPred (@coerce_sort_to_pred T pT P0)) eF in
  FinpredPattern (LabeledFinpredReverseCoercion P0 eF F).
Notation "P0" := (@FinpredReverseCoercionPattern _ _ P0 _)
   (at level 8, only printing) : form_scope.

Program Definition finpred0 T := @Finpred T pred0 _.
Next Obligation. by exists nil. Qed.
Canonical Finpred0 T := InferFinpred pred0 (finpred0 T) (TryFalse false).

Program Definition finpred1 T a := @Finpred T (pred1 a) _.
Next Obligation. by exists [:: a] => x; rewrite inE. Qed.

Program Definition finpred1x T a := @Finpred T [pred x | a == x] _.
Next Obligation. by exists [:: a] => x; rewrite inE eq_sym. Qed.

Program Definition finpredU T (A B : finpred T) := @Finpred T [predU A & B] _.
Next Obligation.
by exists (support A ++ support B) => x; rewrite mem_cat !mem_support.
Qed.

Program Definition finpredIr T (A : finpred T) (P : {pred T}) :=
  @Finpred T [predI A & P] _.
Next Obligation. by exists (support A) => x /andP[]; rewrite mem_support. Qed.

Program Definition finpredIl (T : eqType) (P : {pred T}) (A : finpred T) :=
  @Finpred T [predI P & A] _.
Next Obligation. by exists (support A) => x /andP[]; rewrite mem_support. Qed.

Program Definition finpred_leq n := @Finpred nat [pred m | m <= n] _.
Next Obligation. by exists (iota 0 n.+1) => m; rewrite mem_iota. Qed.

Program Definition finpredUx T (A B : finpred T) :=
  @Finpred T [pred x | (x \in A) (+) (x \in B)] _.
Next Obligation.
exists (support (finpredU A B)) => x; rewrite mem_support !inE.
by case: (x \in A).
Qed.

Program Definition finpredIf (T : eqType) (P : pred T) (A B : finpred T) :=
  @Finpred T [pred x | if P x then x \in A else x \in B] _.
Next Obligation.
exists (support (finpredU A B)) => x; rewrite mem_support !inE.
by case: ifP => _ ->; rewrite ?orbT.
Qed.

Program Definition finpredIfr T (A : finpred T) (P : pred T) (B : finpred T) :=
  @Finpred T [pred x | if x \in A then P x else x \in B] _.
Next Obligation.
by exists (support (finpredU A B)) => x; rewrite mem_support !inE; case: ifP.
Qed.

Fixpoint envelope_of_seq {T} (s : seq _) : finpredEnvelope [pred x in s] :=
  if s isn't x :: s' then envelope (finpred0 T) else
  envelope (finpredU (finpred1 x) (Finpred _ (envelope_of_seq s'))).
Coercion finpred_seq T s := Finpred _ (@envelope_of_seq T s).
Coercion CoercedFinpred_seq T s :=
   DeclareCoercedFinpred (@mem_seq T s) s.
Canonical CoercedFinpred_seq.

Structure labeled_bool := LabelBool {unlabel_bool :> bool}.
Structure op_finpred {T : eqType} (P : pred T) (A : finpred T) :=
  OpFinpred {opFinpred_pilot :> labeled_bool}.
Canonical InferOpFinpred T P A (m : matchArg) (eA : @op_finpred T P A) :=
  @InferFinpred T P A (TryOp (m (eA : bool))).

Definition LabelBinop {T : eqType}
  (op : bool -> bool -> bool) (P P1 : pred T) (a b : bool) := 
  fun F : forall A B : finpred T, finpred T => @id labeled_bool.
Definition LabelOneBinop {T : eqType} (P : pred T) a b op F :=
  @LabelBinop T op P P (TryFalse a) (TryFalse b) F (LabelBool (op a b)).
Fixpoint LabelManyBinop {T : eqType} (P : pred T) a b op0 Fs :=
  if Fs isn't (op, F) :: Fs' then LabelBool (op0 a b) else
  LabelBinop op P P (TryFalse a) (TryFalse b) F (LabelManyBinop P a b op0 Fs').

Canonical InferBinFinpred {T : eqType} (PQ : (pred T)) op F
    P Q A B (eA : inferFinpred P A) (eB : inferFinpred Q B) c :=
  OpFinpred PQ (F A B)
    (LabelBinop op PQ (fun x => op (P x) (Q x)) eA eB F c).

Canonical FinpredU T P a b := LabelOneBinop P a b orb (@finpredU T).
Canonical FinpredUx T P a b := LabelOneBinop P a b xorb (@finpredUx T).

Definition LabelTerminalOp {T : eqType} (op : {pred T}) (F : finpred T) :=
  @id labeled_bool.
Definition LabelOneTerminalOp T op F x :=
  @LabelTerminalOp T op F (LabelBool (op x)).
Canonical InferTerminalFinpred {T} P F x :=
  OpFinpred P F (@LabelTerminalOp T P F x).

Definition TryIdK := tt.
Definition TryIdConv := TryIdK.

Definition LabelIr (T : Type) a b & bool := LabelBool (a && b).
Definition LabelSigma T a b (eP : unit) ea (eb : T -> bool) (ec : unit) :=
  @LabelIr T a b ea.
Definition LabelIl T a b (eNa : bool) eb :=
  @LabelSigma T a b tt (TryFalse a) (fun=> eb) TryIdConv.
Definition TryConst := @id bool.
Canonical LabelI T a b := LabelIl T a b (TryConst a) (TryFalse b).

Canonical FinpredIr T a b P Q A (eA : inferFinpred P A) :=
  @OpFinpred T (fun x => P x && Q x) (finpredIr A Q) (LabelIr T a b eA).

Structure not_finpred (T : eqType) (P : {pred T}) :=
  NotFinpred {notFin_pilot :> bool}.
Canonical ConstNotFin T a a1 := @NotFinpred T (fun=> a) (TryConst a1).
Canonical NegbNotFin T P a := @NotFinpred T P (negb a).
Canonical GeqNotFin T m n m1 n1 := @NotFinpred T (fun x => m <= n x) (m1 <= n1).

Canonical FinpredIl T a b P Q B
  (nFa : not_finpred P) (eB : inferFinpred Q B) :=
  @OpFinpred T (fun x => P x && Q x) (finpredIl P B) (LabelIl T a b nFa eB).

HB.mixin Record isSigmaType (I : eqType) (T_ : I -> eqType) T := {
  to_sigma : T -> {x : I & T_ x};
  of_sigma : {x : I & T_ x} -> T;
  of_sigmaK : cancel of_sigma to_sigma;
  to_sigmaK : cancel to_sigma of_sigma
}.

#[short(type=sigmaEqType)]
HB.structure Definition SigmaEqType I T_ :=
  {T of isSigmaType I T_ T & Equality T}.

HB.instance Definition _ I T_ :=
  @isSigmaType.Build I T_ _ id id (frefl _) (frefl _).

HB.instance Definition _ (T1 T2 : eqType) :=
  isSigmaType.Build T1 (fun=> T2) _  pair_of_tagK tag_of_pairK.

HB.instance Definition _ (I : eqType) (T1_ T2_ : I -> eqType) :=
  isSigmaType.Build _ _ _ (@tag2_of_tagK I T1_ T2_) tag_of_tag2K.

(* To be revised once extra_args of default canonical projections are fixed
Structure labelSmashArg X C T (x : X) (c : C) := (* x, y not free in d *)
  LabelSmashArg { smashArg_val : T }.
Structure smashArg X C T Z (x : X) (c : C) (z : Z) :=
  SmashArg { smashArgLabel :> labelSmashArg T x c}.

Definition TrySmashProd T := @id T.
Definition TrySmashLambda T z (eta_z : T) (isEta : bool) := @TrySmashProd T z.
Definition TrySmashIf T z := @TrySmashLambda T z (MatchArg z) false.
Definition TrySmashApp T z (app_z : T) := @TrySmashIf T z.
Definition TrySmashConst T (z : T) := TrySmashApp z (MatchArg z).
Definition TrySmashVar := TrySmashConst.

(* The target term is convertible to x. *)
Canonical LabelSmashVar X x := @LabelSmashArg X unit X x tt (TrySmashVar x).
Canonical SmashVar X x := SmashArg x (@LabelSmashVar X x).

(* Neither x nor y occur in c. *)
Canonical LabelSmashConst X C x c := @LabelSmashArg X C C x c (TrySmashConst c).
Canonical SmashConst X C x c := SmashArg c (@LabelSmashConst X C x c).

(* Default case only succeeds if by conversion y does not occur in z *)
Canonical LabelSmashConv X T x z := @LabelSmashArg X unit T x tt z.
Canonical SmashConv X T x z := SmashArg z (@LabelSmashConv X T x z).

Definition LabelSmashApp X C A R a x c & forall a : A, R a & A :=
  @LabelSmashArg X C (R a) x c.
Canonical MatchSmashApp X C A R a x c z0 (m : matchArg) f (ef : funPattern f) :=
  @LabelSmashApp X C A R a x c (TrySmashVar f) (TrySmashVar a)
     (TrySmashApp z0 (m (ef a))).
Canonical SmashApp X Cf Ca A0 R0 a0 (x : X) (cf : Cf) (ca : Ca) (z : R0 a0)
       A R (f : forall a : A, R a) a
       (ef : smashArg (forall a, R0 a) x cf f) (ea : smashArg A0 x ca a) :=
  SmashArg (f a)
    (LabelSmashApp x (cf, ca) (smashArg_val ef) (smashArg_val ea) z).

Structure smashFunBody A R (f : forall a, R a) (a : A) (z : R a) (eta : bool) :=
  SmashFunBody {smashFun_body : R a}.
Canonical SmashEtaBody A R f a (ef : funPattern f) :=
  @SmashFunBody A R f a (f a) true (ef a).
Canonical SmashLambdaBody A R f a z :=
  @SmashFunBody A R f a (TrySmashVar z) false z.

Structure smashType X CA Cf x A cA (cf : Cf) Cb (cb : forall a : A, Cb a) :=
  SmashType { smashType_Type :> @smashArg X CA Type Type x cA A }.
Canonical SmashConstType X A Cb x cb :=
  @SmashType X _ _ x A A cb Cb cb (SmashConst x A).
Canonical SmashDependentType X CA Cf A x cA cf eA :=
  @SmashType X CA Cf x A cA cf (fun=> Cf) (fun=> cf) eA.

Definition LabelSmashLambda X C A R x c (A0 A1 : Type) R1
                           & forall a : A1, R1 a :=
  @LabelSmashArg X C (forall a : A, R a) x c.
Canonical MatchSmashLambda X C A R x c f0 f isEta (m : matchArg) eb z :=
  let ef a := @smashFun_body A R f0 a (f a) isEta (eb a) in
  @LabelSmashLambda X C A R x c (TrySmashVar A) A R f
     (TrySmashLambda f0 (m ef) z).
Canonical SmashLambda X A0 R0 (x : X) (z : forall a : A0, R0 a)
       CA Cf A Cb cA cf cb (eA : @smashType X CA Cf x A cA cf Cb cb) R1 R
       f (efa : forall a, smashArg (R1 a) x (cb a) (f a : R a)) :=
  let ef a := smashArg_val (efa a) in
  SmashArg f (LabelSmashLambda x (cA, cf) (smashArg_val eA) ef z).

Definition LabelSmashIf X C x c
    (T0 T : bool -> Type) (t0 t : bool)  & T true & T false :=
  @LabelSmashArg X C (T t) x c.
Canonical MatchSmashIf X C T x c t b_tt b_ff :=
  @LabelSmashIf X C x c
    (TrySmashVar T) T (TrySmashVar t) t (TrySmashVar b_tt) (TrySmashVar b_ff)
    (TrySmashIf (if t return T t then b_tt else b_ff)).
Canonical SmashIf X CT Ct Cbt Cbf x cT ct cbt cbf
             T (eT : @smashArg X CT (bool -> Type) _ x cT T)
             t (et : @smashArg X Ct bool _ x ct t)
             b_tt (ebt : @smashArg X Cbt (T true) _ x cbt b_tt)
             b_ff (ebf : @smashArg X Cbf (T false) _ x cbf b_ff) z :=
  SmashArg (if t return T t then b_tt else b_ff)
           (@LabelSmashIf X _ x (CT, Ct, Cbt, Cbf) (smashArg_val eT) T
                   (smashArg_val et) t (smashArg_val ebt) (smashArg_val ebf) z).

#[universes(polymorphic=yes)]
Definition LabelSmashProd X C x c
    (sA : Forall.argSort) (S : Forall.sort)
    (A0 A : sA) & Forall.pred_sort A S :=
  @LabelSmashArg X C S x c.

#[universes(polymorphic=yes)]
Canonical MatchSmashProd X C x c sA S A R (z : @Forall.pattern sA S A R) :=
  @LabelSmashProd X C x c sA S (TrySmashVar A) A (TrySmashVar R)
    (TrySmashProd (Forall.get z)).

#[universes(polymorphic=yes)]
Canonical SmashProd X CA CR (x : X) (cA : CA) (cR : CR)
           (sA : Forall.argSort) (S : Forall.sort)
            A (eA : smashArg sA x cA A)
            R (eR : smashArg (Forall.pred_sort A S) x cR R) z :=
  SmashArg (@Forall.Forall sA A S R)
       (LabelSmashProd x (cA, cR) (smashArg_val eA) (smashArg_val eR) z).

Structure manifestSigmaPred I T_ (P : forall x : I, pred (T_ x)) :=
  ManifestSigmaPred {manifestSigmaPred_pilot :> unit}.
Definition LabelSigmaPred I T_ (P P1 P2 : forall x : I, pred (T_ x)) :=
  ManifestSigmaPred P tt.
Canonical MatchSigmaPred I T_ P1 P2 :=
  @LabelSigmaPred I T_ (fun x y => P1 x y && P2 x y)
                       (fun x y => TrySmashVar (P1 x y)) P2.

Structure splaySigmaPred I T_ (pT := forall x : I, {pred (T_ x)})
                         (P : pT) (P1 : {pred I}) (P2 : pT) :=
  SplaySigmaPred{ sigmaPred_label :> manifestSigmaPred P }.
Canonical InferSigmaPred I T_ C P P1 P2 c
    (eP1 : forall x y, @smashArg I C bool bool x c (P1 x)) :=
  SplaySigmaPred P1 P2
    (@LabelSigmaPred I T_ P (fun x y => smashArg_val (eP1 x y)) P2).
*)

Structure splaySigmaPred I T_ (pT := forall x : I, {pred T_ x})
                         (P : pT) (P1 : {pred I}) (P2 : pT) :=
  SplaySigmaPred{ sigmaPred_pilot :> unit }.
Canonical InferSigmaPred I T_ P1 P2 :=
  @SplaySigmaPred I T_ (fun x y => P1 x && P2 x y) P1 P2 tt.

Program Definition finpredSigma I T_ (T : sigmaEqType T_)
                      (A : finpred I) (B : forall x, finpred (T_ x)) :=
  @Finpred T [preim to_sigma of [pred z | tag z \in A & tagged z \in B _]] _.
Next Obligation.
exists [seq of_sigma (Tagged T_ y) | x <- support A, y <- support (B x)] => z.
rewrite !inE; set a := tag _; set b := tagged _ => /andP[Aa Bb].
apply/allpairsPdep; exists a, b; split; try by rewrite mem_support.
by apply/(canRL to_sigmaK); case: (to_sigma z) @a @b {Aa Bb}.
Qed.

Program Definition finpred_idK (T : eqType) f (fK : f =1 id) (P : {pred T}) 
  (E : finpredEnvelope [preim f of P]) := @Finpred T P _.
Next Obligation.
by case: E => s fPs; exists s => z; rewrite -[z in z \in P -> _]fK => /fPs. 
Qed.

Structure finpredIdPreim (T : eqType) (f : T -> T) (fK : f =1 id)
    (P Pf : {pred T}) (Cf : finpredEnvelope Pf) (FC : finpred T -> finpred T) :=
  FinpredIdPreim {finpredIdPreim_pilot :> unit}.
Canonical FinpredIdConvPreim T f fK P Cf :=
  @FinpredIdPreim T f fK P P Cf id TryIdConv.
Canonical FinpredIdKPreim T f fK P Cf :=
  @FinpredIdPreim T f fK P [preim f of P] Cf (fun=> finpred_idK fK Cf) TryIdK.

Canonical FinpredSigma I T_ (T : sigmaEqType T_) a b (P : {pred T})
                       (P0 := fun x y => P (of_sigma (Tagged T_ y)))
                       P1 P2 (eP : splaySigmaPred P0 P1 P2)
                       A (eA : @inferFinpred I P1 A)
                       B (eB : forall x, @inferFinpred (T_ x) (P2 x) (B x))
                       (C := finpredSigma T A B) (E := envelope C)
                       FC (eC : finpredIdPreim to_sigmaK P E FC) :=
  @OpFinpred T P (FC C) (LabelSigma a b eP eA eB eC).

Record finPreimFun (A B T : eqType) := FinPreimFun {
  finPreim_fun :> A -> B -> T;
  has_finPreim :> {b : T -> seq B | forall x y, y \in b (finPreim_fun x y)}
}.
Add Printing Constructor finPreimFun.

Program Definition PcanFinPreim A {B T} f g (fK : pcancel f g) :=
  @FinPreimFun A B T (fun=> f) _.
Next Obligation. by exists (seq_of_opt \o g) => _ y /=; rewrite fK inE. Qed.
Arguments PcanFinPreim A {B T} f g fK.
Definition CanFinPreim A {B T} f g (fK : cancel f g) :=
  @PcanFinPreim A B T f (Some \o g) (can_pcan fK).
Arguments CanFinPreim A {B T} f g fK.
Program Definition ComposeFinPreim {A B C T}
    (f : finPreimFun A C T) (g : finPreimFun A B C) :=
  @FinPreimFun A B T (fun x y => f x (g x y)) _.
Next Obligation.
case: f g => f [bf bfP] [g [bg bgP]] /=.
by exists (flatten \o map bg \o bf) => x y; apply/flatten_mapP; exists (g x y).
Qed.

Definition TryVal T := @id T.

Structure labelFinPreimExpr (A T : eqType) (x : A) :=
  LabelFinPreimExpr { finPreim_expr : T }.
Definition LabelFinPreimApp {A B T} (f : finPreimFun A B T) (x : A)
                                  (z z0 : labelFinPreimExpr T x) (y : B) := z0.
Definition OneFinPreimApp {A B T} x y fxy (f : finPreimFun A B T) :=
  let z := LabelFinPreimExpr x (f x y) in
  LabelFinPreimApp f z (LabelFinPreimExpr x fxy) (TryVal y).
Fixpoint ManyFinPreimApp {A B T} x y f0xy (fs : seq (finPreimFun A B T)) :=
  if fs isn't f :: fs' then LabelFinPreimExpr x f0xy else
  let z := LabelFinPreimExpr x (f x y) in
  @LabelFinPreimApp A B T f x z (ManyFinPreimApp x y f0xy fs') (TryVal y).
About ecast.
Canonical LabelValFinPreim {A T : eqType} {P} (B : @subEqType T P) x y :=
  let z := LabelFinPreimExpr x (TryVal (val y)) in
  @LabelFinPreimApp A B T (PcanFinPreim A val _ valK) x z z y.

Definition finPreim_pair A (T1 T2 : eqType) (y1 : T1) :=
  @CanFinPreim A T2 _ (pair y1) snd (frefl _).
Canonical FinPreim_pair A x (T1 T2 : eqType) (y1 : T1) (y2 : T2) :=
  OneFinPreimApp x y2 (y1, y2) (finPreim_pair A T2 y1).

Definition finPreim_Tagged A (I : eqType) i (T_ : I -> eqType) :=
  PcanFinPreim A (@Tagged I i T_) otagged_at TaggedK.

Canonical FinPreim_Tagged A x (I : eqType) (T_ : I -> eqType) i y :=
  OneFinPreimApp x y (Tagged T_ y) (finPreim_Tagged A i T_).

Definition finPreim_Tagged2 A (I : eqType) i (T1_ T2_ : I -> eqType) y1 :=
  PcanFinPreim A (@Tagged2 I i T1_ T2_ y1) _ Tagged2K.
Canonical FinPreim_Tagged2 A x (I : eqType) (T1_ T2_ : I -> eqType) i y1 y2 :=
  OneFinPreimApp x y2 (@Tagged2 I i T1_ T2_ y1 y2) (finPreim_Tagged2 A T2_ y1).

Canonical LabelVarFinPreim {A} x := @LabelFinPreimExpr A A x x.
Definition MarkComp T := @id T.
Definition IdFinPreim A := @CanFinPreim A A A id id (frefl _).
Structure inferFinPreimApp (A : eqType) T (f : finPreimFun A A T) (x : A) :=
  InferFinPreimApp { labeled_finPreim_expr :> labelFinPreimExpr T x }.
Canonical InferFinPreimVar A x :=
  InferFinPreimApp (IdFinPreim A) (LabelVarFinPreim x).
Canonical InferFinPreimComp A B T f g x (y : inferFinPreimApp g x) z :=
  InferFinPreimApp (ComposeFinPreim f g)
     (@LabelFinPreimApp A B T (MarkComp f) x z z (finPreim_expr y)).

Structure inferFinPreim A T (fF : finpred T) (F : finpred A) (x : A) :=
  InferFinPreimPreimage { finPreim_val : T }.

Program Definition finpred_preim A T (f : finPreimFun _ A _) (fF : finpred T) :=
  @Finpred A [preim (fun x => f x x) of mem_finpred fF] _.
Next Obligation.
case: f => f [g fk] /=; exists (flatten (map g (support fF))) => x Ffx.
by apply/flatten_mapP; exists (f x x); rewrite ?mem_support.
Qed.

Definition TryPreim T := @id T.
Definition TryVar := TryPreim.

Canonical FinpredNopreim A (F : finpred A) (x : A) :=
  @InferFinPreimPreimage A A F F x (TryVar x).
Canonical FinpredPreim A T Ff f x (fx : inferFinPreimApp f x) :=
  @InferFinPreimPreimage A T Ff (finpred_preim f Ff) x
     (TryPreim (finPreim_expr fx)).

Definition LabelPreimPred {A T : eqType} (b : labeled_bool)
  (P : {pred A}) (Ff : finpred T) (f : A -> T) := b.
Canonical InferPreimPred {A T : eqType} P b (Ff : finpred T) (F : finpred A)
    (eF : forall x : A, inferFinPreim Ff F x) :=
  OpFinpred P F (LabelPreimPred b P Ff (fun x => finPreim_val (eF x))).
Definition FinpredPredFor (A T : eqType) z0 (P : {pred T}) Ff f :=
  @LabelPreimPred A T z0 [preim f of P] Ff (fun x => TryVar (TryVal (f x))).
Definition OneFinpredPred A T b0 Ff :=
  @FinpredPredFor A T (LabelBool b0) (mem_finpred Ff) Ff.
Fixpoint ManyFinpredPred {A T : eqType} b0 Ffs f :=
  if Ffs isn't Ff :: Ffs' then LabelBool b0 else
  @FinpredPredFor A T (ManyFinpredPred b0 Ffs' f) (mem_finpred Ff) Ff f.
Arguments FinpredPredFor A {T} z0 P Ff f.
Arguments OneFinpredPred A {T} b0 Ff f.
Arguments ManyFinpredPred A {T} b0 Ffs f.

Canonical Finpred_finpred {A T} y0 (F : finpred T) f :=
  OneFinpredPred A (mem_labeled F y0) F f.
Canonical Finpred_seq {A T} s f y0 :=
  @OneFinpredPred A T (mem_seq s y0) (finpred_seq s) f.
Canonical Finpred_leq A m0 n m := OneFinpredPred A (m0 <= n) (finpred_leq n) m.
Canonical Finpred_eq (A T : eqType) (a x0 y0 : T) y :=
  ManyFinpredPred A (x0 == y0 :> T) [:: finpred1 a; finpred1x a] y.

Definition finPreim_succ A := @CanFinPreim A _ _ succn predn (frefl _).
Canonical FinPreim_succ A x n := OneFinPreimApp x n n.+1 (finPreim_succ A).

Program Definition FinPreim_nat A T f g 
  (bf : forall x n, n <= g (f x n)) := @FinPreimFun A nat T f _.
Next Obligation.
by exists (fun y => iota 0 (g y).+1) => x n; rewrite mem_iota ltnS bf.
Qed.

Definition finPreim_pred A :=
  @FinPreim_nat A _ (fun=> predn) succn (fun _ n => leqSpred n).
Canonical FinPreim_pred A x y := OneFinPreimApp x y y.-1 (finPreim_pred A).

Definition finPreim_addnl A m_ :=
  @FinPreim_nat A _ (fun x n => n + m_ x) id (fun _ _ => leq_addr _ _).
Definition finPreim_addnr A m :=
  @FinPreim_nat A _ (fun x n => m + n) id (fun _ _ => leq_addl _ _).
Canonical FinPreim_addn A m m_ x n m0 n0 :=
  ManyFinPreimApp x n (m0 + n0) [:: finPreim_addnr A m; finPreim_addnl m_].

Definition finPreim_double A := @CanFinPreim A _ _ double half doubleK.
Canonical FinPreim_double A x n := OneFinPreimApp x n n.*2 (finPreim_double A).

Program Definition finPreim_half A :=
  @FinPreim_nat A _ (fun=> half) (fun n => n.*2.+1) _.
Next Obligation. by rewrite -leq_half_double. Qed.
Canonical FinPreim_half A x n := OneFinPreimApp x n (half n) (finPreim_half A).

Definition finPreim_mulnl A m_ :=
  @FinPreim_nat A _ (fun x n => n * (m_ x).+1) id
                    (fun _ _ => @leq_pmulr _ _.+1 isT).
Definition finPreim_mulnr A m :=
  @FinPreim_nat A _ (fun x n => m.+1 * n) id (fun _ _ => leq_addr _ _).
Canonical FinPreim_muln A m m_ x n m0 n0 :=
  ManyFinPreimApp x n (m0 * n0) [:: finPreim_mulnr A m; finPreim_mulnl m_].

Program Definition finPreim_expnl A m_ :=
  @FinPreim_nat A _ (fun x n => n ^ (m_ x).+1) id _.
Next Obligation. by case: n => //= n; rewrite expnS leq_pmulr // expn_gt0. Qed.
Program Definition finPreim_expnr A n2 :=
  @FinPreim_nat A _ (fun x m => n2.+2 ^ m) id _.
Next Obligation. by case: n => //= b; rewrite ltnW 1?ltn_expl. Qed.
Canonical FinPreim_expn A m n2 x n m0 n0 :=
  ManyFinPreimApp x n (m0 ^ n0) [:: finPreim_expnr A n2; finPreim_expnl m].

Definition finPreim_maxnl A m_ :=
  @FinPreim_nat A _ (fun x n => maxn n (m_ x)) id (fun _ _ => leq_maxl _ _).
Definition finPreim_maxnr A m :=
  @FinPreim_nat A _ (fun x n => maxn m n) id (fun _ _ => leq_maxr _ _).
Canonical FinPreim_maxn A m m_ x n m0 n0 :=
  ManyFinPreimApp x n (m0 * n0) [:: finPreim_maxnr A m; finPreim_maxnl m_].

Definition LabelPreimFinpred {A T : eqType}
   (Pf : {pred A}) (P P0 : {pred T}) (f : A -> T) := @id labeled_bool.
Definition LabelOnePreimFinpred {A T : eqType} op P f x0 Q0 :=
  @LabelPreimFinpred A T (fun x => op (f x) P) P
    (fun y => TryFalse (P y)) (fun x => TryVar (f x))
    (LabelBool (op x0 Q0)).
Canonical InferPreimFinpred {A T : eqType} c (Pf : {pred A}) (P : {pred T}) F Ff
           (eF : inferFinpred P F) (eFf : forall x, inferFinPreim F Ff x) :=
  OpFinpred Pf Ff
     (LabelPreimFinpred Pf P (fun=> eF) (fun x => finPreim_val (eFf x)) c).
Canonical Finpred_in {A T} P f x0 Q0 :=
  @LabelOnePreimFinpred A T (fun x P => x \in P) P f x0 Q0.

Structure finPreimOp (A B1 B2 T : eqType) := FinPreimOp {
  finPreim_op :> A -> B1 -> B2 -> T;
  finPreimOp_bounded : {b : T -> seq B1 * seq B2
    | forall x y1 y2 (bxy := b (finPreim_op x y1 y2)),
        (y1 \in bxy.1) || (y2 \in bxy.2)}}.
Program Definition FinPreimOp_nat A T h b
   (hb : forall x m1 m2, minn m1 m2 <= b (h x m1 m2)) :=
  @FinPreimOp A _ _ T h _.
Next Obligation.
pose bs z := iota 0 (b z).+1; exists (fun z => (bs z, bs z)) => x m1 m2 /=.
by rewrite !mem_iota /= !ltnS -geq_min.
Qed.

Definition LabelFinPreimAppOp {A B1 B2 T} (h : finPreimOp A B1 B2 T)
           (x : A) (z z0 : labelFinPreimExpr T x) (y1 : B1) (y2 : B2) := z0.
Definition OneFinPreimOp {A B1 B2 T} x y1 y2 hxy (h : finPreimOp A B1 B2 T) :=
  let z := LabelFinPreimExpr x (h x y1 y2) in
  LabelFinPreimAppOp h z (LabelFinPreimExpr x hxy) (TryVal y1) (TryVal y2).
Fixpoint ManyFinPreimOps {A B1 B2 T} x y1 y2 hxy hs :=
  if hs isn't h :: hs' then LabelFinPreimExpr x hxy else
  let z := LabelFinPreimExpr x (@finPreim_op A B1 B2 T h x y1 y2) in
  let z0 := ManyFinPreimOps x y1 y2 hxy hs' in
  LabelFinPreimAppOp h z z0 (TryVal y1) (TryVal y2).

Program Definition ComposeFinPreimOp {A B1 B2 T} (h : finPreimOp A B1 B2 T)
  (g1 : finPreimFun A A B1) (g2 : finPreimFun A A B2) :=
  @FinPreimFun A A T (fun x y => h x (g1 x y) (g2 x y)) _.
Next Obligation.
case: h g1 g2 => h [b hb] [g1 [b1 gb1]] [g2 [b2 gb2]] /=.
exists (fun z => flatten (map b1 (b z).1) ++ flatten (map b2 (b z).2)) => x y.
set y1 := g1 x y; set y2 := g2 x y; set z := h x y1 y2.
rewrite mem_cat; apply/orP; case/orP: (hb x y1 y2) => bz; [left | right].
  by apply/flatten_mapP; exists (g1 x y).
by apply/flatten_mapP; exists (g2 x y).
Qed.
Canonical InferFinPreimCompOp {A B1 B2 T} h g1 g2 x
     (y1 : inferFinPreimApp g1 x) (y2 : inferFinPreimApp g2 x) z :=
  InferFinPreimApp (ComposeFinPreimOp h g1 g2)
    (@LabelFinPreimAppOp A B1 B2 T h x z z
       (finPreim_expr y1) (finPreim_expr y2)).

Definition finPreim_minn A :=
  @FinPreimOp_nat A nat (fun=> minn) id (fun _ _ _ => leqnn _).
Canonical FinPreim_minn A x y1 y2 :=
  OneFinPreimOp x y1 y2 (minn y1 y2) (finPreim_minn A).

(******************************************************************************)
(*************************** Unit Tests          ******************************)
(******************************************************************************)


(*Definition t1 (T : choiceType) (A : {set T}) : finPred T :=
  [pred x in A]. *)

(*
Arguments InferredFinpredPattern {T} _ _.
Lemma foo (D := fun T (x : T) => True) (T : eqType) (a b : T)
  (G : forall T A, D {finpred T} A -> D {pred T} A) :
   D {pred _} [pred x : {n | 5 < n} | sval x == 3].
apply: G.
Abort.
*)

(*
Lemma foo (D := fun T (x : T) => True) (T : eqType) (a b : T)
  (G : forall T A, D {finpred T} A -> D {pred T} A) :
   D {pred _} [pred x | x.1 == a & x.2 == b].
apply: G.
by [].
Print Canonical Projections S.
suff G1 L: D (labelFinPreimExpr _ N) L -> D nat (finPreim_expr L).
have: D nat N.+1.
Set Printing All.
have bar A m n : @FinPreim_succ A m n = @FinPreim_IDN A m n.
  congr LabelFinPreimApp.

Label
Lemma foo (D := fun T (x : T) => True) (T : eqType)
  (G : forall A, D {finpred nat} A -> D {pred nat} A) :
   D {pred nat} [pred n | n < N].
refine (G _ _).
Print Canonical Projections S.
suff G1 L: D (labelFinPreimExpr _ N) L -> D nat (finPreim_expr L).
have: D nat N.+1.
Set Printing All.
have bar A m n : @FinPreim_succ A m n = @FinPreim_IDN A m n.
  congr LabelFinPreimApp.

Label
split.
refine (G1 _ _).
Print Canonical Projections IDN.
have: D _ FinPreim_succ.
rewrite /FinPreim_succ.
rewrite /OneFinPreimApp.
rewrite {1}/finPreim_succ.
rewrite /CanFinPreim /PcanFinPreim.
 simpl.
have: D _ FinPreim_succ.
rewrite /FinPreim_succ.
rewrite /OneFinPreimApp. simpl.
refine (G _ _).

have: D (finpred T) pred0.

refine (P _ _ _).
have: D _ [in s].
refine (P _ _).
rewrite /in_mem.  /=.
apply: P.
Definition D {T} (x : T) := True.
Set Printing Implicit.
Lemma foo2 (T : eqType) (x : T) 
           (P : forall A : {finpred T}, D A -> x \in A) : False.
suff Q (L : labeled_pred T) : D L -> x \in L.
have foo (A : {finpred T}) : x \in [pred x in A | x == x].
eapply Q.
Show Existentials.
*)

Definition t1' (T : choiceType) (P : finpred T) : {finpred T} :=
  [pred x in P] : {pred T}.
Definition t2 (T : choiceType) (P : {finpred T}) (Q : pred T) : finpred T :=
  [pred x | ([in P] x) && (Q x)].
Fail Definition t3 (T : choiceType) (A : {set T}) (Q : pred T) : finpred T :=
   [pred x | (x \in A) && (Q x)].
Definition t4 (T : choiceType) (P : finpred T) (Q : finpred T) : finpred T :=
   [pred x | (x \in P) || (x \in Q)].
Fail Definition t5 (T : finType) (P : pred T) : finpred T :=
   [pred x | P x].
Definition def (T : choiceType) (P Q : {pred T}) : pred T := [pred x : T | P x && Q x].
Definition t6 (T : choiceType) (P : finpred T) Q : finpred T :=
   [pred x : T | def P Q x ].

Fail Check fun (T : choiceType) (P : finpred T) => [eta P] : finpred T.
Fail Check fun (T : choiceType) (P : finpred T) => [in P] : finpred T.
Fail Check fun (T : choiceType) (A : {set T}) => [in A] : finpred T.
Fail Check fun (T : choiceType) (P : finpred T) (Q : pred T) =>
   (fun x => (P x) && (Q x)) : finpred T.
Fail Check fun (T : choiceType) (A : {set T}) (Q : pred T) =>
   (fun x => (x \in A) && (Q x)) : finpred T.
Fail Check fun (T : choiceType) (P : finpred T) (Q : finpred T) =>
   (fun x => (P x) || (Q x)) : finpred T.

Fail Check fun (T : choiceType) (P : finpred T) (Q : pred T) =>
  enum [pred x in P | Q x].

Fail Check fun (T : choiceType) (A : {set T}) => enum A.

(* Some operator definitions. *)

HB.lock Definition card {T} P := size (@support T P).
Canonical card_unlockable := Unlockable card.unlock.

(* A is at level 99 to allow the notation #|G : H| in groups. *)
Reserved Notation "#| A |" (at level 0, A at level 99, format "#| A |").
Notation "#| A |" := (card ((*pred_set*) A)) (only parsing): nat_scope.  (* TODO *)
Notation "#| A |" := (card A) (only printing): nat_scope.

Definition pred0b {T} P := @card T P == 0.

HB.lock Definition enum {T : choiceType} P := sort prec_eq (@support T P).
Canonical enum_unlockable := Unlockable enum.unlock.
Definition pick {T} P := ohead (@enum T P).
Definition pick_pred {T} := @id {pred T}.

Notation "[ 'pick' x | P ]" := (pick (pick_pred (fun x => P%B)))
  (at level 0, x name, format "[ 'pick'  x  |  P  ]") : form_scope.
Notation "[ 'pick' x : T | P ]" := (pick (pick_pred (fun x : T => P%B)))
  (at level 0, x name, only parsing) : form_scope.
Definition pick_true T (x : T) := true.
Reserved Notation "[ 'pick' x : T ]"
  (at level 0, x name, format "[ 'pick'  x : T ]").
Notation "[ 'pick' x : T ]" := [pick x : T | pick_true x]
  (only parsing) : form_scope.
Notation "[ 'pick' x : T ]" := [pick x : T | pick_true _]
  (only printing) : form_scope.
Notation "[ 'pick' x ]" := [pick x : _]
  (at level 0, x name, only parsing) : form_scope.
Notation "[ 'pick' x | P & Q ]" := [pick x | P && Q ]
  (at level 0, x name,
   format "[ '[hv ' 'pick'  x  |  P '/ '   &  Q ] ']'") : form_scope.
Notation "[ 'pick' x : T | P & Q ]" := [pick x : T | P && Q ]
  (at level 0, x name, only parsing) : form_scope.
Notation "[ 'pick' x 'in' A ]" := [pick x | x \in A]
  (at level 0, x name, format "[ 'pick'  x  'in'  A  ]") : form_scope.
Notation "[ 'pick' x : T 'in' A ]" := [pick x : T | x \in A]
  (at level 0, x name, only parsing) : form_scope.
Notation "[ 'pick' x 'in' A | P ]" := [pick x | x \in A & P ]
  (at level 0, x name,
   format "[ '[hv ' 'pick'  x  'in'  A '/ '   |  P ] ']'") : form_scope.
Notation "[ 'pick' x : T 'in' A | P ]" := [pick x : T | x \in A & P ]
  (at level 0, x name, only parsing) : form_scope.
Notation "[ 'pick' x 'in' A | P & Q ]" := [pick x in A | P && Q]
  (at level 0, x name, format
  "[ '[hv ' 'pick'  x  'in'  A '/ '   |  P '/ '  &  Q ] ']'") : form_scope.
Notation "[ 'pick' x : T 'in' A | P & Q ]" := [pick x : T in A | P && Q]
  (at level 0, x name, only parsing) : form_scope.

(******************************************************************************)
(*************************** fintype starts here ******************************)
(******************************************************************************)

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

Definition disjoint (T : eqType) (A : finpred T) (B : {pred T}) :=
  @pred0b T [predI A & B].

Notation "[ 'disjoint' A & B ]" := (disjoint A B)
  (at level 0,
   format "'[hv' [ 'disjoint' '/  '  A '/'  &  B ] ']'") : bool_scope.

HB.lock
Definition subset (T : eqType) (A : finpred T) (B : {pred T}) : bool :=
  pred0b [pred x in A | x \notin B].
Canonical subset_unlock := Unlockable subset.unlock.

Notation "A \subset B" := (subset A B)
  (at level 70, no associativity) : bool_scope.

Definition proper (T : eqType) (A B : finpred T) :=
  @subset T A B && ~~ subset B A.
Notation "A \proper B" := (proper A B)
  (at level 70, no associativity) : bool_scope.

(* image, xinv, inv, and ordinal operations will be defined later. *)

Section EqOpsTheory.
Variable T : eqType.
Implicit Types (A B C : {finpred T}) (F : finpred T) (P Q : {pred T}).
Implicit Types (x : T) (s : seq T).

Variant pick_spec (P : pred T) : option T -> Type :=
  | Pick x of P x         : pick_spec P (Some x)
  | Nopick of P =i xpred0 : pick_spec P None.

Lemma eq_card A B : A =i B -> #|A| = #|B|.
Proof. by rewrite unlock => /eq_support/perm_size. Qed.

Lemma eq_pred0b A B : A =i B -> pred0b A = pred0b B.
Proof. by unfold pred0b => /eq_card->. Qed.

Lemma eq_card_trans A B n : #|A| = n -> B =i A -> #|B| = n.
Proof. by move=> <- /eq_card. Qed.

Lemma card_uniqP s : reflect (#|s| = size s) (uniq s).
Proof.
rewrite (uniq_size_uniq (support_uniq s) (mem_support _)) eq_sym unlock.
exact: eqP.
Qed.

Lemma card0 : #|@pred0 T| = 0. Proof. exact/(card_uniqP [::]). Qed.

Lemma card1 x : #|pred1 x| = 1.
Proof. by rewrite -(@eq_card [:: x]) => [|y /[!inE]//]; apply/card_uniqP. Qed.

Lemma eq_card0 A : A =i pred0 -> #|A| = 0.
Proof. exact: eq_card_trans card0. Qed.

Lemma eq_card1 x A : A =i pred1 x -> #|A| = 1.
Proof. exact: eq_card_trans (card1 x). Qed.

Lemma cardUI A B : #|[predU A & B]| + #|[predI A & B]| = #|A| + #|B|.
Proof.
pose U := [predU A & B].
have Dcard A1: {subset A1 <= U} -> #|A1| = count [in A1] (support U).
  move=> sA1U; rewrite unlock -size_filter; apply/perm_size.
  rewrite uniq_perm ?filter_uniq // => x; rewrite mem_filter !inE.
  exact/esym/andb_idr/sA1U.
rewrite !Dcard ?count_predUI // => x /[!inE]; try case/andP; move=> -> //.
exact: orbT.
Qed.

Lemma cardID P A : #|[predI A & P]| + #|[pred x in A | x \notin P]| = #|A|.
Proof.
rewrite -cardUI addnC [in LHS]eq_card0 => [|x] /=.
  by apply: eq_card => x /[!inE]/=; rewrite -andb_orr orbN andbT.
by rewrite !inE andbACA andbN andbF.
Qed.

Lemma cardU1 x A : #|[predU1 x & A]| = (x \notin A) + #|A|.
Proof.
case Ax: (x \in A); first by apply/eq_card => y /[!inE]; case: eqP => // ->.
rewrite /= -(card1 x) -cardUI addnC.
by rewrite [in RHS]eq_card0 // => y /[!inE]; case: eqP => // ->.
Qed.

(* notes:

today:
Lemma cardU1 (T : finType) (x : T) (A : {pred T}) : #|[predU1 x & A]| = (x \notin A) + #|A|.

options for the future:
Lemma cardU1 (T : choiceType) (x : T) (A : finPred T) :
  #|[predU1 x & A]| = (x \notin A) + #|A|.
Lemma cardU1 (T : choiceType) (x : T) A S (_ : finPred_aux T [predU1 x & A] S) :
  #|S| = (x \notin A) + #|A|.
rewrite cardU1. (* works no matter how you derive the finiteness of [predU1 x & A] \*)

*)

Lemma card2 x y : #|pred2 x y| = (x != y).+1.
Proof. by rewrite cardU1 inE card1 addn1. Qed.
(* The cardU1 match succeeds but exposes a finpred1 y structure, as it        *)
(* matches the finpred structures directly, and the inner finpred1 is not     *)
(* labeled by a call to reverse_coercion.                                     *)
(* TO CHECK: it appears the top calls to reverse_coercion fail to match       *)
(* because of universe constraints ?!?                                        *)

Lemma cardD1 x A : #|A| = (x \in A) + #|[predD1 A & x]|.
Proof.
apply/(@addnI (x \notin A)); rewrite addnA addn_negb -cardU1.
have <-: x \notin [predD1 A & x] = 1 :> nat by rewrite !inE eqxx.
by rewrite -[RHS]cardU1; apply/eq_card=> y /[!inE]; rewrite orb_andr orbN.
(* The [RHS] makes this rewrite work by matching the (_ + _) as a whole       *)
(* rather than piecewise. The LHS of the (_ + _) cannot match because of the  *)
(* extraarg default projection bug: trying to match (?x \in ?A) where ?x : T  *)
(* and ?A : {finpred T}, with (y \in P), will always fail, even when P would  *)
(* unify with ?A coerced to {pred T}), because it actually tries to match     *)
(* (P x) with (mem_labeled ?A x), where x : T is a fresh variable. This fails *)
(* because mem_labeled only has a default instance, which cannot match due to *)
(* the presence of the extraarg x.                                            *)
(*   Matching the (_ + _) globally fixes this because although first it fails *)
(* matching the nat_of_bool (?x \notin ?A) LHS initially as above, ultimately *)
(* it expands the definition of addn to a fix expression, which gets pushed   *)
(* as a stack item, leading to a the following unification problem            *)
(*      nat_of_bool | ZApp (?x \notin ?A), ZFix (fix 0 ...), ZApp (#|?A|)     *)
(*      nat_of_bool | ZApp (y \notin P), ZFix (fix 0 ...), ZApp (#|P|)        *)
(* which Coq can resolve because it matches stacks RIGHT TO LEFT, even though *)
(* it matches application lists LEFT TO RIGHT, the match of the cardinals     *)
(* succeeds because #|P| already contains the finpred inferred for P, and     *)
(* then the P to ?A match succeeds by conversion since ?A has been resolved.  *)
Qed.

Lemma card_undup s : #|undup s| = #|s|.
Proof. by apply/eq_card=> x; rewrite !inE mem_undup. Qed.

Lemma card_size s : #|s| <= size s.
Proof.
by rewrite unlock (uniq_leq_size (support_uniq _))// => x /[!inE].
Qed.

Lemma card0_eq A : #|A| = 0 -> A =i pred0.
Proof. by move=> + x; apply/contra_eqF=> Ax; rewrite (cardD1 x) Ax. Qed.

Lemma card0P A : reflect (forall x, x \notin A) (#|A| == 0).
Proof.
apply: (iffP eqP) => [A0 x|A0]; first by rewrite card0_eq.
by apply/eq_card0=> x; apply/idPn/A0.
Qed.

Lemma card_gt0P A : reflect (exists x, x \in A) (#|A| > 0).
Proof.
apply: (iffP idP) => [|[x]]; last by rewrite lt0n; apply/contraL=> /card0P->.
by rewrite unlock -has_predT => /hasP[x /[!inE]]; exists x.
Qed.

Lemma pred0P A: reflect ((A : {pred T}) =1 pred0) (pred0b A).
Proof. by apply: (iffP eqP); [apply: card0_eq | apply: eq_card0]. Qed.

Lemma pred0Pn A : reflect (exists x, x \in A) (~~ pred0b A).
Proof. by rewrite -lt0n; apply: card_gt0P. Qed.

Lemma card_le1P {A} : reflect {in A, forall x, A =i pred1 x} (#|A| <= 1).
Proof.
rewrite leq_eqVlt ltnNge orbC; case: posnP => [A0 | Agt0].
  by apply/ReflectT=> x; rewrite card0_eq.
apply/(iffP idP)=> A1; last by case/card_gt0P: Agt0 => x /A1/eq_card1->.
move=> x xA y; rewrite (cardD1 x) xA in A1; have{A1} := card0P _ A1 y.
by rewrite !inE; case: eqP => [->|_ /negbTE].
Qed.

Lemma mem_card1 A : #|A| = 1 -> {x | A =i pred1 x}.
Proof.
move=> A1; suffices [x xA]: {x | x \in A}.
  by exists x; apply/(card_le1P _ x xA); rewrite A1.  
rewrite unlock in A1; case defA: (support A) A1 => // [x s] _.
by exists x; rewrite -mem_support defA mem_head.
Qed.

Lemma card1P A : reflect (exists x, A =i pred1 x) (#|A| == 1).
Proof.
by apply: (iffP idP) => [/eqP/mem_card1[x inA]|[x /eq_card1/eqP//]]; exists x.
Qed.

Lemma card_le1_eqP A :
  reflect {in A &, forall x, all_equal_to x} (#|A| <= 1).
Proof.
apply: (iffP card_le1P) => [Ale1 x y /Ale1-> /eqP // | all_eq x xA y].
by apply/idP/eqP=> [/(all_eq x y xA) | ->].
Qed.

Lemma subsetE A P : (A \subset P) = pred0b [predD A & P].
Proof. by rewrite unlock; apply/eq_pred0b => /= x; rewrite inE andbC. Qed.

Lemma subsetP A P : reflect {subset A <= P} (A \subset P).
Proof.
rewrite unlock; apply: (iffP (pred0P _)) => /=[AP0 x | sAP x /=].
  by apply/implyP/idPn; rewrite negb_imply [_ && _]AP0.
by rewrite -negb_imply; apply/negbF/implyP/sAP.
Qed.

Lemma subsetPn A P :
 reflect (exists2 x, x \in A & x \notin P) (~~ (A \subset P)).
Proof.
rewrite unlock; apply: (iffP (pred0Pn _)) => [[x] | [x Ax P'x]].
  by case/andP; exists x.
by exists x; rewrite /= inE P'x andbT.
Qed.

Lemma subset_leq_card A B : A \subset B -> #|A| <= #|B|.
Proof.
move=> sAB; rewrite -(cardID A B) (@eq_card _ A) ?leq_addr// => x.
by rewrite !inE andbC; case Ax: (x \in A) => //; apply: subsetP Ax.
Qed.

Lemma subxx F : F \subset F.
Proof. exact/subsetP. Qed.
(* TODO: understand why we need the argument F *)
Hint Resolve subxx : core.

Lemma eq_subset A B : A =i B -> subset A =1 subset B.
Proof.
by move=> eqAB C; rewrite !unlock; apply: eq_pred0b => /= x; rewrite !inE eqAB.
Qed.

Lemma eq_subset_r P Q : P =i Q -> (@subset T)^~ P =1 (@subset T)^~ Q.
Proof.
by move=> eqPQ A; rewrite !unlock; apply/eq_pred0b => x; rewrite !inE eqPQ.
Qed.

Lemma eq_subxx A P : A =i P -> A \subset P.
Proof. by move/eq_subset_r <-. Qed.

Lemma subset_predT F : F \subset T.
Proof. exact/subsetP. Qed.

Lemma subset_pred1 P x : (pred1 x \subset P) = (x \in P).
Proof. by apply/subsetP/idP=> [-> | Px y /eqP->] //; apply: eqxx. Qed.

Lemma subset_eqP A B : reflect (A =i B) ((A \subset B) && (B \subset A)).
Proof.
apply: (iffP andP) => [[sAB sBA] x| eqAB]; last by rewrite !eq_subxx.
by apply/idP/idP; apply: subsetP.
Qed.

Lemma subset_cardP A B : #|A| = #|B| -> reflect (A =i B) (A \subset B).
Proof.
move=> eqcAB; case: (subsetP A B) (subset_eqP A B) => //= sAB.
case: (subsetP B A) => [//|[]] x Bx; apply: contraFT (ltnn #|A|) => A'x.
rewrite [leqRHS]eqcAB (cardD1 x B) Bx ltnS.
by apply/subset_leq_card/subsetP=> y Ay; rewrite inE (memPn A'x) ?sAB.
Qed.

Lemma subset_leqif_card A B : A \subset B -> #|A| <= #|B| ?= iff (B \subset A).
Proof.
move=> sAB; split; [exact: subset_leq_card | apply/eqP/idP].
  by move/subset_cardP=> sABP; rewrite (eq_subset_r (sABP sAB)).
by move=> sBA; apply: eq_card; apply/subset_eqP; rewrite sAB.
Qed.

Lemma subset_trans A B P : A \subset B -> B \subset P -> A \subset P.
Proof. by move/subsetP=> sAB /subsetP=> sBP; apply/subsetP=> x /sAB/sBP. Qed.

Lemma subset_all s P : (s \subset P) = all [in P] s.
Proof. exact: (sameP (subsetP s P) allP). Qed.

Lemma subset_cons s x : s \subset x :: s.
Proof. by apply/(subsetP s) => y /[!inE] ->; rewrite orbT. Qed.

Lemma subset_cons2 s1 s2 x : s1 \subset s2 -> x :: s1 \subset x :: s2.
Proof.
move=> ?; apply/(subsetP (x :: s1)) => y /[!inE]; case: eqP => // _.
exact: (subsetP s1).
Qed.

Lemma subset_catl s s' : s \subset s ++ s'.
Proof. by apply/(subsetP s)=> x xins; rewrite mem_cat xins. Qed.

Lemma subset_catr s s' : s \subset s' ++ s.
Proof. by apply/(subsetP s) => x xins; rewrite mem_cat xins orbT. Qed.

Lemma subset_cat2 s1 s2 s3 : s1 \subset s2 -> s3 ++ s1 \subset s3 ++ s2.
Proof.
move=> /(subsetP s1) s12; apply/(subsetP (s3 ++ s1)) => x.
by rewrite !mem_cat => /orP[->|/s12->]; rewrite ?orbT.
Qed.

Lemma filter_subset P s : [seq a <- s | P a] \subset s.
Proof. by apply/subsetP=> x; rewrite mem_filter => /andP[]. Qed.

Lemma subset_filter P s1 s2 :
  s1 \subset s2 -> [seq a <- s1 | P a] \subset [seq a <- s2 | P a].
Proof.
move/subsetP=> s12; apply/(subsetP (filter _ _))=> x.
by rewrite !mem_filter=> /andP[-> /s12].
Qed.

Lemma properE A B : A \proper B = (A \subset B) && ~~ (B \subset A).
Proof. by []. Qed.

Lemma properP A B :
  reflect (A \subset B /\ (exists2 x, x \in B & x \notin A)) (A \proper B).
Proof. by rewrite properE; apply: (iffP andP) => [] [-> /subsetPn]. Qed.

Lemma proper_sub A B : A \proper B -> A \subset B.
Proof. by case/andP. Qed.

Lemma proper_subn A B : A \proper B -> ~~ (B \subset A).
Proof. by case/andP. Qed.

Lemma proper_trans A B C : A \proper B -> B \proper C -> A \proper C.
Proof.
case/properP=> sAB [x Bx nAx] /properP[sBC [y Cy nBy]].
rewrite properE (subset_trans sAB) //=; apply/subsetPn; exists y => //.
by apply: contra nBy; apply: subsetP.
Qed.

Lemma proper_sub_trans A B C : A \proper B -> B \subset C -> A \proper C.
Proof.
case/properP=> sAB [x Bx nAx] sBC; rewrite properE (subset_trans sAB) //.
by apply/subsetPn; exists x; rewrite ?(subsetP _ _ sBC).
Qed.

Lemma sub_proper_trans A B C : A \subset B -> B \proper C -> A \proper C.
Proof.
move=> sAB /properP[sBC [x Cx nBx]]; rewrite properE (subset_trans sAB) //.
by apply/subsetPn; exists x => //; apply: contra nBx; apply: subsetP.
Qed.

Lemma proper_card A B : A \proper B -> #|A| < #|B|.
Proof.
by case/andP=> sAB nsAB; rewrite ltn_neqAle !(subset_leqif_card sAB) andbT.
Qed.

Lemma proper_irrefl A : ~~ (A \proper A).
Proof. by rewrite properE subxx. Qed.

Lemma properxx A : (A \proper A) = false.
Proof. by rewrite properE subxx. Qed.

Lemma eq_proper A B : A =i B -> proper A =1 proper B.
Proof.
move=> eAB C; congr (_ && _); first exact: (eq_subset eAB).
by rewrite (eq_subset_r eAB).
Qed.

Lemma eq_proper_r A B : A =i B -> (@proper T)^~ A =1 (@proper T)^~ B.
Proof.
move=> eAB C; congr (_ && _); first exact: (eq_subset_r eAB).
by rewrite (eq_subset eAB).
Qed.

Lemma card_geqP {A n} :
  reflect (exists s, [/\ uniq s, size s = n & {subset s <= A}]) (n <= #|A|).
Proof.
apply: (iffP idP) => [n_le_A|[s] [uniq_s size_s /(subsetP s) subA]]; last first.
rewrite -size_s -(card_uniqP _ uniq_s).
  exact: (subset_leq_card subA).
exists (take n (support A)); rewrite take_uniq ?support_uniq // size_take.
split=> //; last by move=> x /mem_take; rewrite mem_support.
case: (ltnP n (size (support A))) => // size_A.
by apply/eqP; rewrite eqn_leq size_A /=; rewrite unlock in n_le_A.
Qed.

Lemma card_gt1P A :
  reflect (exists x y, [/\ x \in A, y \in A & x != y]) (1 < #|A|).
Proof.
apply: (iffP card_geqP) => [[s] []|[x] [y] [xA yA xDy]].
  case: s => [|a [|b []]]//= /[!(inE, andbT)] aDb _ subD.
  by exists a, b; rewrite aDb !subD ?inE ?eqxx ?orbT.
by exists [:: x; y]; rewrite /= !inE xDy; split=> // z /[!inE] /pred2P[]->.
Qed.

Lemma card_gt2P A :
  reflect (exists x y z,
              [/\ x \in A, y \in A & z \in A] /\ [/\ x != y, y != z & z != x])
          (2 < #|A|).
Proof.
apply: (iffP card_geqP) => [[s] []|[x] [y] [z] [[xD yD zD] [xDy xDz yDz]]].
  case: s => [|x [|y [|z []]]]//=; rewrite !inE !andbT negb_or -andbA.
  case/and3P => xDy xDz yDz _ subA.
  by exists x, y, z; rewrite xDy yDz eq_sym xDz !subA ?inE ?eqxx ?orbT.
exists [:: x; y; z]; rewrite /= !inE negb_or xDy xDz eq_sym yDz; split=> // u.
by rewrite !inE => /or3P [] /eqP->.
Qed.

Lemma disjoint_sym A B : [disjoint A & B] = [disjoint B & A].
Proof. by congr (_ == 0); apply: eq_card => x; apply: andbC. Qed.

Lemma eq_disjoint A B : A =i B -> disjoint A =1 disjoint B.
Proof.
by move=> eqAB C; congr (_ == 0); apply: eq_card => x /=; rewrite !inE eqAB.
Qed.

Lemma eq_disjoint_r P Q : P =i Q -> (@disjoint T)^~ P =1 (@disjoint T)^~ Q.
Proof.
by move=> eqPQ A; congr (_ == 0); apply: eq_card => x /=; rewrite !inE eqPQ.
Qed.

Lemma subset_disjoint A P : (A \subset P) = [disjoint A & [predC P]].
Proof.
apply/subsetP/pred0P => [sAP x | + x] /=.
  by rewrite -negb_imply; apply/negbF/implyP=> /sAP.
by move/(_ x)/negbT; rewrite /= -negb_imply negbK => /implyP.
Qed.

Lemma disjoint_subset A P : [disjoint A & P] = (A \subset [predC P]).
Proof.
by rewrite subset_disjoint; apply: eq_disjoint_r => x; rewrite !inE negbK.
Qed.

Lemma disjointFr A P x : [disjoint A & P] -> x \in A -> x \in P = false.
Proof. by move/pred0P/(_ x) => /= + Ax; rewrite Ax. Qed.

Lemma disjointFl A P x : [disjoint A & P] -> x \in P -> x \in A = false.
Proof. by move/pred0P/(_ x) => /= + Px; rewrite Px andbT. Qed.

Lemma disjointWl A B P : A \subset B -> [disjoint B & P] -> [disjoint A & P].
Proof. by rewrite 2!disjoint_subset; apply: subset_trans. Qed.

Lemma disjointWr A P B : A \subset P -> [disjoint B & P] -> [disjoint B & A].
Proof.
rewrite 2!disjoint_subset => /subsetP-sAB /subsetP-sPB'.
by apply/subsetP => x /sPB'; apply/contra/sAB.
Qed.

Lemma disjointW A B C P :
  A \subset B -> C \subset P -> [disjoint B & P] -> [disjoint A & C].
Proof. by move=> sAB sCP B'P; apply/(disjointWl sAB)/(disjointWr sCP). Qed.

Lemma disjoint0 P : [disjoint pred0 & P].
Proof. exact/pred0P. Qed.

Lemma eq_disjoint0 A P : A =i pred0 -> [disjoint A & P].
Proof. by move/(@eq_disjoint _ pred0)->; apply: disjoint0. Qed.

Lemma disjoint1 x P : [disjoint pred1 x & P] = (x \notin P).
Proof.
apply/pred0P/idP=> [/(_ x) /= /[!(inE, eqxx)] /= -> // | + y].
by apply/contraNF=> /andP[/eqP<-].
Qed.

Lemma eq_disjoint1 x A P : A =i pred1 x ->  [disjoint A & P] = (x \notin P).
Proof. by move/(@eq_disjoint _ (pred1 x))->; apply: disjoint1. Qed.

Lemma disjointU A B P :
  [disjoint [predU A & B] & P] = [disjoint A & P] && [disjoint B & P].
Proof.
case: [disjoint A & P] / (altP (pred0P [predI A & P])) => [A0|] /=.
  by apply/eq_pred0b => x; rewrite !inE andb_orl [_ && _]A0.
apply/contraNF=> /= /pred0P-nABC; apply/pred0P=> x /=.
by apply: contraFF (nABC x); rewrite /= andb_orl => ->.
Qed.

Lemma disjointU1 x A P :
  [disjoint [predU1 x & A] & P] = (x \notin P) && [disjoint A & P].
Proof. by rewrite (disjointU (pred1 x)) disjoint1. Qed.

Lemma disjoint_cons x s P :
  [disjoint x :: s & P] = (x \notin P) && [disjoint s & P].
Proof. exact: (disjointU1 x [pred x | x \in s] P). Qed.

Lemma disjoint_has s P : [disjoint s & P] = ~~ has [in P] s.
Proof.
apply/negbRL; apply/pred0Pn/hasP => [[x /andP[]]|[x]]; exists x => //.
exact/andP.
Qed.

Lemma disjoint_cat s1 s2 P :
  [disjoint s1 ++ s2 & P] = [disjoint s1 & P] && [disjoint s2 & P].
Proof. by rewrite !disjoint_has has_cat negb_or. Qed.

End EqOpsTheory.

Lemma map_subset {T T' : eqType} (s1 s2 : seq T) (f : T -> T') :
  s1 \subset s2 -> [seq f x | x <- s1 ] \subset [seq f x | x <- s2].
Proof.
move=> /(subsetP s1) s1s2; apply/(subsetP (map _ _)) => _ /mapP[y]/[swap]-> ys1.
by apply/mapP; exists y => //; apply: s1s2.
Qed.

#[global] Hint Resolve subxx : core.

Arguments pred0P {T A}.
Arguments pred0Pn {T A}.
Arguments card_le1P {T A}.
Arguments card_le1_eqP {T A}.
Arguments card1P {T A}.
Arguments subsetP {T A P}.
Arguments subsetPn {T A P}.
Arguments subset_eqP {T A B}.
Arguments card_uniqP {T s}.
Arguments card_geqP {T A n}.
Arguments card_gt0P {T A}.
Arguments card_gt1P {T A}.
Arguments card_gt2P {T A}.
Arguments properP {T A B}.

Section ChoiceOpsTheory.
Variable T : choiceType.
Implicit Types (A B : {finpred T}).
Implicit Types (x : T).

Lemma mem_enum A : enum A =i A.
Proof. by rewrite unlock => x; rewrite mem_sort inE. Qed.

Lemma enum_uniq (A : finpred T) : uniq (enum A).
Proof. by rewrite unlock sort_uniq. Qed.
Hint Resolve enum_uniq : core.

Lemma enum0 : enum pred0 = Nil T.
Proof.
by apply: size0nil; move: (@card0 T); rewrite !unlock size_sort.
Qed.

Lemma enum1 x : enum (pred1 x) = [:: x].
Proof.
apply: perm_small_eq => //; apply: uniq_perm => // y.
by rewrite mem_enum /= !inE.
Qed.

Lemma pickP A : pick_spec (A : {pred T}) (pick (pick_pred A)).
Proof.
rewrite /pick; case: (enum _) (mem_enum A) => [|x s] Axs /=.
  by right; apply: fsym.
by left; rewrite -[_ x]Axs mem_head.
Qed.

(* Should we keep it? *)
Definition set_pickP A : pick_spec [in A] (pick A) := pickP A.

Lemma enum_prec_eq_sorted (A : finpred T) : sorted prec_eq (enum A).
Proof. by rewrite unlock sort_sorted//; apply: prec_eq_total. Qed.
Local Hint Resolve enum_prec_eq_sorted.

Lemma eq_enum A B : A =i B -> enum A = enum B.
Proof.
move=> AB; apply: (@sorted_eq _ prec_eq) => //.
- exact: prec_eq_trans.
- exact: prec_eq_antisymmetric.
by apply: uniq_perm => // x; rewrite !mem_enum.
Qed.

Lemma eq_pick A B :
  (A : {pred T}) =1 (B : {pred T}) -> pick (pick_pred A) = pick (pick_pred B).
Proof. by rewrite /pick => /eq_enum->. Qed.

Lemma cardE A : #|A| = size (enum A).
Proof. by rewrite !unlock size_sort. Qed.

End ChoiceOpsTheory.
#[export] Hint Extern 0 (is_true (uniq (enum _))) =>
  solve [apply: enum_uniq] : core.

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

Section ChoiceInjectiveb.

Variables (aT : choiceType) (rT : eqType) (f : aT -> rT).
Implicit Type D : {finpred aT}.

Definition dinjectiveb D := uniq (map f (enum D)).

Lemma dinjectivePn D :
  reflect (exists2 x, x \in D & exists2 y, y \in [predD1 D & x] & f x = f y)
          (~~ dinjectiveb D).
Proof.
apply: (iffP idP) => [injf | [x Dx [y Dxy eqfxy]]]; last first.
  move: Dx; rewrite -(mem_enum D) => /rot_to[i E defE].
  rewrite /dinjectiveb -(rot_uniq i) -map_rot defE /=; apply/nandP; left.
  rewrite inE /= -(mem_enum D) -(mem_rot i) defE inE in Dxy.
  rewrite andb_orr andbC andbN in Dxy.
  by rewrite eqfxy map_f //; case/andP: Dxy.
pose p := [pred x in D | has (fun y => (y != x) && (f x == f y)) (enum D)].
case: (pickP p) => [x /=/andP[Dx /hasP[y Dy /andP[ynx /eqP eqfxy]]] | no_p].
  by exists x => //; exists y => //; rewrite inE ynx/= -mem_enum.
rewrite /dinjectiveb map_inj_in_uniq ?enum_uniq // in injf => x y Dx Dy eqfxy.
apply: contraNeq (negbT (no_p x)) => ne_xy /=; rewrite /p inE -mem_enum Dx/=.
by apply/hasP; exists y => //; rewrite eq_sym ne_xy/=; apply/eqP.
Qed.

Lemma dinjectiveP D : reflect {in D &, injective f} (dinjectiveb D).
Proof.
rewrite -[dinjectiveb D]negbK.
case: dinjectivePn=> [noinjf | injf]; constructor.
  case: noinjf => x Dx [y /andP[neqxy /= Dy] eqfxy] injf.
  by case/eqP: neqxy; apply: injf.
move=> x y Dx Dy /= eqfxy; apply/eqP; apply/idPn=> nxy; case: injf.
by exists x => //; exists y => //=; rewrite inE /= eq_sym nxy.
Qed.

End ChoiceInjectiveb.

Section FinInjectiveb.

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

End FinInjectiveb.

Definition image (T : choiceType) T' f (A : {finpred T}) : seq T' :=
  map f (enum A).
Notation "[ 'seq' F | x 'in' A ]" := (image (fun x => F) A)
  (at level 0, F at level 99, x binder,
   format "'[hv' [ 'seq'  F '/ '  |  x  'in'  A ] ']'") : seq_scope.
Notation "[ 'seq' F | x ]" :=
  [seq F | x in @predT
    (* kludge for getting the type of x *)
    match _, (fun x => I) with
    | T, f
      => match match f return T -> True with f' => f' end with
         | _ => T
         end
    end]
  (at level 0, F at level 99, x binder, only parsing) : seq_scope.
Notation "[ 'seq' F | x : T ]" := [seq F | x : T in @predT T]
  (at level 0, F at level 99, x name, only printing,
   format "'[hv' [ 'seq'  F '/ '  |  x  :  T ] ']'") : seq_scope.
Notation "[ 'seq' F , x ]" := [seq F | x ]
  (at level 0, F at level 99, x binder, only parsing) : seq_scope.

Definition codom (T : finType) T' f := @image T T' f T.

Section ChoiceImage.

Variable T : choiceType.
Implicit Type A : {finpred T}.

Section ChoiceSizeImage.

Variables (T' : Type) (f : T -> T').

Lemma size_image A : size (image f A) = #|A|.
Proof. by rewrite size_map -cardE. Qed.

End ChoiceSizeImage.

Variables (T' : eqType) (f : T -> T').

Lemma imageP A y : reflect (exists2 x, x \in A & y = f x) (y \in image f A).
Proof.
by apply: (iffP mapP) => [] [x Ax y_fx]; exists x; rewrite // mem_enum in Ax *.
Qed.

Remark iinv_proof A y : y \in image f A -> {x | x \in A & f x = y}.
Proof.
move=> fy; pose b := [predI A & [pred x | f x == y]].
case: (pickP b) => [x /andP[Ax /eqP] | nfy]; first by exists x.
by case/negP: fy => /imageP[x Ax fx_y]; case/andP: (nfy x); rewrite inE fx_y.
Qed.

Definition iinv A y fAy := s2val (@iinv_proof A y fAy).

Lemma f_iinv A y fAy : f (@iinv A y fAy) = y.
Proof. exact: s2valP' (iinv_proof fAy). Qed.

Lemma mem_iinv A y fAy : @iinv A y fAy \in A.
Proof. exact: s2valP (iinv_proof fAy). Qed.

Lemma in_iinv_f A : {in A &, injective f} ->
  forall x fAfx, x \in A -> @iinv A (f x) fAfx = x.
Proof.
by move=> injf x fAfx Ax; apply: injf => //; [apply: mem_iinv | apply: f_iinv].
Qed.

Lemma preim_iinv A B y fAy : preim f B (@iinv A y fAy) = B y.
Proof. by rewrite /= f_iinv. Qed.

Lemma image_f A x : x \in A -> f x \in image f A.
Proof. by move=> Ax; apply/imageP; exists x. Qed.

Lemma image_pred0 : image f pred0 =i pred0.
Proof. by move=> x; rewrite /image /= enum0. Qed.

Section ChoiceInjective.

Hypothesis injf : injective f.

Lemma mem_image A x : (f x \in image f A) = (x \in A).
Proof. by rewrite mem_map ?mem_enum. Qed.

Lemma pre_image A : [preim f of image f A] =i A.
Proof. by move=> x; rewrite inE /= mem_image. Qed.

End ChoiceInjective.

End ChoiceImage.
Arguments imageP {T T' f A y}.

Section FinImage.

Variable T : finType.
Implicit Type A : {finpred T}.

Section FinSizeImage.

Variables (T' : Type) (f : T -> T').

Lemma size_codom : size (codom f) = #|T|.
Proof. exact: size_image. Qed.

Lemma codomE : codom f = map f (enum T).
Proof. by []. Qed.

End FinSizeImage.

Variables (T' : eqType) (f : T -> T').

Lemma codomP y : reflect (exists x, y = f x) (y \in codom f).
Proof. by apply: (iffP (@imageP _ _ _ _ y)) => [][x]; exists x. Qed.

Lemma codom_f x : f x \in codom f.
Proof. exact: image_f. Qed.

Lemma image_codom A : {subset image f A <= codom f}.
Proof. by move=> _ /imageP[x _ ->]; apply: codom_f. Qed.

Section FinInjective.

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

(* TODO: generalize in section ChoiceInjective above *)
Lemma bij_on_image A (x0 : T) : {on [pred y in image f A], bijective f}.
Proof. exact: subon_bij (@image_codom A) (bij_on_codom x0). Qed.

End FinInjective.

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

End FinImage.

Prenex Implicits codom iinv.
Arguments codomP {T T' f y}.

Lemma flatten_imageP (aT : choiceType) (rT : eqType)
                     (A : aT -> seq rT) (P : {finpred aT}) (y : rT) :
  reflect (exists2 x, x \in P & y \in A x) (y \in flatten [seq A x | x in P]).
Proof.
by apply: (iffP flatten_mapP) => [][x Px]; exists x; rewrite ?mem_enum in Px *.
Qed.
Arguments flatten_imageP {aT rT A P y}.

Section ChoiceCardFunImage.

Variables (T : choiceType) (T' : eqType) (f : T -> T').
Implicit Type A : {finpred T}.

Lemma leq_image_card A : #|image f A| <= #|A|.
Proof. by rewrite (cardE A) -(size_map f) card_size. Qed.

Lemma card_in_image A : {in A &, injective f} -> #|image f A| = #|A|.
Proof.
move=> injf; rewrite (cardE A) -(size_map f); apply/card_uniqP.
by rewrite map_inj_in_uniq// => x y; rewrite !mem_enum; apply: injf.
Qed.

Lemma image_injP A : reflect {in A &, injective f} (#|image f A| == #|A|).
Proof.
apply: (iffP eqP) => [eqfA |]; last exact: card_in_image.
by apply/dinjectiveP; apply/card_uniqP; rewrite size_map -cardE.
Qed.

Hypothesis injf : injective f.

Lemma card_image A : #|image f A| = #|A|.
Proof. by apply: card_in_image; apply: in2W. Qed.

End ChoiceCardFunImage.
Arguments image_injP {T T' f A}.

Section ChoiceFinCardFunImage.

Variables (T : choiceType) (T' : finType) (f : T -> T').
Implicit Type A : {finpred T}.

Lemma leq_card_in A : {in A &, injective f} -> #|A| <= #|T'|.
Proof. by move=> /card_in_image<-; apply: (max_card [seq f x | x in A]). Qed.

End ChoiceFinCardFunImage.
Arguments leq_card_in [T T'] f.

Section FinCardFunImage.

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

End FinCardFunImage.
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
Proof. by case=> [x|]; rewrite /= count_map (Finite.enumP, count_pred0). Qed.

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

Record seq_sub : Type := SeqSub {ssval : T; ssvalP : in_mem ssval (@mem T _ s)}.

HB.instance Definition _ := [isSub for ssval].
HB.instance Definition _ := [Equality of seq_sub by <:].

Definition seq_sub_enum : seq seq_sub := undup (pmap insub s).

Lemma mem_seq_sub_enum x : x \in seq_sub_enum.
Proof. by rewrite mem_undup mem_pmap -valK map_f ?ssvalP. Qed.

Lemma val_seq_sub_enum : uniq s -> map val seq_sub_enum = s.
Proof.
move=> Us; rewrite /seq_sub_enum undup_id ?pmap_sub_uniq //.
rewrite (pmap_filter (insubK _)); apply/all_filterP.
by apply/allP => x; rewrite isSome_insub.
Qed.

Definition seq_sub_pickle x := index x seq_sub_enum.
Definition seq_sub_unpickle n := nth None (map some seq_sub_enum) n.
Lemma seq_sub_pickleK : pcancel seq_sub_pickle seq_sub_unpickle.
Proof.
rewrite /seq_sub_unpickle => x.
by rewrite (nth_map x) ?nth_index ?index_mem ?mem_seq_sub_enum.
Qed.

Definition seq_sub_isCountable := isCountable.Build seq_sub seq_sub_pickleK.
Fact seq_sub_axiom : Finite.axiom seq_sub_enum.
Proof. exact: Finite.uniq_axiom (undup_uniq _) mem_seq_sub_enum. Qed.
Definition seq_sub_isFinite := isFinite.Build seq_sub seq_sub_axiom.

(* Beware: these are not the canonical instances, as they are not consistent  *)
(* with the generic sub_choiceType canonical instance.                        *)
Definition adhoc_seq_sub_choiceType : choiceType := pcan_type seq_sub_pickleK.
Definition adhoc_seq_sub_countType := HB.pack_for countType seq_sub
  seq_sub_isCountable (Choice.class adhoc_seq_sub_choiceType).
Definition adhoc_seq_sub_finType := HB.pack_for finType seq_sub
  seq_sub_isFinite seq_sub_isCountable (Choice.class adhoc_seq_sub_choiceType).

End SeqSubType.

Section SeqReplace.
Variables (T : eqType).
Implicit Types (s : seq T).

Lemma seq_sub_default s : size s > 0 -> seq_sub s.
Proof. by case: s => // x s _; exists x; rewrite mem_head. Qed.

Lemma seq_subE s (s_gt0 : size s > 0) :
  s = map val (map (insubd (seq_sub_default s_gt0)) s : seq (seq_sub s)).
Proof. by rewrite -map_comp map_id_in// => x x_in_s /=; rewrite insubdK. Qed.

End SeqReplace.
Notation in_sub_seq s_gt0 := (insubd (seq_sub_default s_gt0)).

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

Section Extrema.

Variant extremum_spec {T : Type} (ord : rel T) {I : Type}
  (P : pred I) (F : I -> T) : I -> Type :=
  ExtremumSpec (i : I) of P i & (forall j : I, P j -> ord (F i) (F j)) :
                   extremum_spec ord P F i.

Let arg_pred {T : eqType} ord {I : eqType} (P : {finpred I}) (F : I -> T) :=
  [pred i | i \in P & all (fun j => ord (F i) (F j)) (support P)].

Section Extremum.

Context {T : eqType} {I : choiceType} (ord : rel T).
Context (i0 : I) (P : {finpred I}) (F : I -> T).  (* TODO: should it be "finpred I" for the definition of extremum? *)

Definition extremum := odflt i0 (pick (arg_pred ord P F)).

Hypothesis ord_refl : reflexive ord.
Hypothesis ord_trans : transitive ord.
Hypothesis ord_total : total ord.
Hypothesis Pi0 : i0 \in P.

Lemma extremumP : extremum_spec ord [in P] F extremum.
Proof.
rewrite /extremum; case: pickP => [i /andP[Pi /allP min_i] | no_i].
  by split=> //= j Pj; apply: min_i; rewrite mem_support.
have := sort_sorted ord_total [seq F i | i <- enum P].
set s := sort _ _ => ss; have s_gt0 : size s > 0
   by rewrite size_sort size_map -cardE; apply/card_gt0P; exists i0.
pose t0 := nth (F i0) s 0; have: t0 \in s by rewrite mem_nth.
rewrite mem_sort => /mapP/sig2_eqW[it0]; rewrite mem_enum => it0P def_t0.
have /negP[/=] := no_i it0; rewrite inE it0P/=; apply/allP => j /[!inE] Pj.
have /(nthP (F i0))[k g_lt <-] : F j \in s by rewrite mem_sort map_f ?mem_enum.
by rewrite -def_t0 sorted_leq_nth.
Qed.

End Extremum.

Section ExtremumIn.

Context {T : eqType} {I : choiceType} (ord : rel T).
Context (i0 : I) (P : {finpred I}) (F : I -> T).  (* TODO: or finpred I ? *)

Hypothesis ord_refl : {in P, reflexive (relpre F ord)}.
Hypothesis ord_trans : {in P & P & P, transitive (relpre F ord)}.
Hypothesis ord_total : {in P &, total (relpre F ord)}.
Hypothesis Pi0 : i0 \in P.

Lemma extremum_inP : extremum_spec ord [in P] F (extremum ord i0 P F).
Proof.
rewrite /extremum; case: pickP => [i /andP[Pi /allP min_i] | no_i].
  by split=> //= j Pj; apply: min_i; rewrite mem_support.
pose TP := seq_sub [seq F i | i <- enum P].
have FPP (iP : {i | i \in P}) : F (proj1_sig iP) \in [seq F i | i <- enum P].
  by rewrite map_f// mem_enum; apply: valP.
pose FP := SeqSub (FPP _).
have []//= := @extremumP _ _ (relpre val ord) (exist [in P] i0 Pi0)
    [pred x | val x \in P] FP.
- by move=> [/= _/mapP[i iP ->]]; apply: ord_refl; rewrite mem_enum in iP.
- move=> [/= _/mapP[j jP ->]] [/= _/mapP[i iP ->]] [/= _/mapP[k kP ->]].
  by apply: ord_trans; rewrite !mem_enum in iP jP kP.
- move=> [/= _/mapP[i iP ->]] [/= _/mapP[j jP ->]].
  by apply: ord_total; rewrite !mem_enum in iP jP.
- rewrite /FP => -[/= i Pi] _ /(_ (exist _ _ _))/= ordF.
  have/negP/negP/= := no_i i; rewrite inE Pi/= -has_predC => /hasP/sig2W[j].
  by rewrite !inE => Pj; rewrite ordF.
Qed.

End ExtremumIn.

Notation "[ 'arg[' ord ]_( i < i0 | P ) F ]" :=
    (extremum ord i0 [pred i | P%B] (fun i => F))
  (at level 0, ord, i, i0 at level 10,
   format "[ 'arg[' ord ]_( i  <  i0  |  P )  F ]") : nat_scope.

Notation "[ 'arg[' ord ]_( i < i0 'in' A ) F ]" :=
    [arg[ord]_(i < i0 | i \in A) F]
  (at level 0, ord, i, i0 at level 10,
   format "[ 'arg[' ord ]_( i  <  i0  'in'  A )  F ]") : nat_scope.

Notation "[ 'arg[' ord ]_( i < i0 ) F ]" := [arg[ord]_(i < i0 | true) F]
  (at level 0, ord, i, i0 at level 10,
   format "[ 'arg[' ord ]_( i  <  i0 )  F ]") : nat_scope.

Section ArgMinMax.

Variables (I : choiceType) (i0 : I).
Variables (P : {finpred I}) (F : I -> nat) (Pi0 : i0 \in P).

Definition arg_min := extremum leq i0 P F.
Definition arg_max := extremum geq i0 P F.

Lemma arg_minnP : extremum_spec leq [in P] F arg_min.
Proof. by apply: extremumP => //; [apply: leq_trans|apply: leq_total]. Qed.

Lemma arg_maxnP : extremum_spec geq [in P] F arg_max.
Proof.
apply: extremumP => //; first exact: leqnn.
  by move=> n m p mn np; apply: leq_trans mn.
by move=> ??; apply: leq_total.
Qed.

End ArgMinMax.

End Extrema.

Notation "[ 'arg' 'min_' ( i < i0 | P ) F ]" :=
    (arg_min i0 [pred i | P%B] (fun i => F))
  (at level 0, i, i0 at level 10,
   format "[ 'arg'  'min_' ( i  <  i0  |  P )  F ]") : nat_scope.

Notation "[ 'arg' 'min_' ( i < i0 'in' A ) F ]" :=
    [arg min_(i < i0 | i \in A) F]
  (at level 0, i, i0 at level 10,
   format "[ 'arg'  'min_' ( i  <  i0  'in'  A )  F ]") : nat_scope.

Notation "[ 'arg' 'min_' ( i < i0 ) F ]" := [arg min_(i < i0 | true) F]
  (at level 0, i, i0 at level 10,
   format "[ 'arg'  'min_' ( i  <  i0 )  F ]") : nat_scope.

Notation "[ 'arg' 'max_' ( i > i0 | P ) F ]" :=
     (arg_max i0 [pred i | P%B] (fun i => F))
  (at level 0, i, i0 at level 10,
   format "[ 'arg'  'max_' ( i  >  i0  |  P )  F ]") : nat_scope.

Notation "[ 'arg' 'max_' ( i > i0 'in' A ) F ]" :=
    [arg max_(i > i0 | i \in A) F]
  (at level 0, i, i0 at level 10,
   format "[ 'arg'  'max_' ( i  >  i0  'in'  A )  F ]") : nat_scope.

Notation "[ 'arg' 'max_' ( i > i0 ) F ]" := [arg max_(i > i0 | true) F]
  (at level 0, i, i0 at level 10,
   format "[ 'arg'  'max_' ( i  >  i0 )  F ]") : nat_scope.

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
Proof. by move=> x; rewrite !inE mem_filter inE andbC. Qed.

Lemma supportIr (T : eqType) (A B : {finpred T}) :
  support [predI A & B] =i filter [in A] (support B).
Proof. by move=> x; rewrite !inE mem_filter inE. Qed.

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
Admitted. (*
case=> i x; rewrite -(enumP i) /tag_enum -enumT.
elim: (enum I) => //= j e IHe.
rewrite count_cat count_map {}IHe; congr (_ + _).
rewrite -size_filter -cardE /=; case: eqP => [-> | ne_j_i].
  by apply: (@eq_card1 _ x) => y; rewrite -topredE /= tagged_asE ?eqxx.
by apply: eq_card0 => y.
Qed. *)

HB.instance Definition _ := isFinite.Build {i : I & T_ i} tag_enumP.

Lemma card_tagged :
  #|{: {i : I & T_ i}}| = sumn (map (fun i => #|T_ i|) (enum I)).
Proof.
Admitted. (*
rewrite cardE !enumT [in LHS]unlock size_flatten /shape -map_comp.
by congr (sumn _); apply: eq_map => i; rewrite /= size_map -enumT -cardE.
Qed. *)

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
Admitted. (*
Proof. by rewrite !cardT !enumT [in LHS]unlock size_cat !size_map. Qed. *)

End SumFinType.
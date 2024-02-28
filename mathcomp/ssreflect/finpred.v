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

(*   matchedArg T == a special-purpose wrapper type that provides some        *)
(*                   control over unification priorities (see below).         *)
(*     MatchedArg == a special constructor for matchedArg T (with T implicit) *)
(*       matchArg == singleton structure type for MatchArg (with T implicit)  *)
(* --> these are used as follows:                                             *)
(*  + Let us write v1 ~ v2 :> T for the unification problem which Coq solves  *)
(*    by unifying v1 and v2 at type T while giving PRIORITY to projectors in  *)
(*    v1 during canonical structure resolution AND also unfolding definitions *)
(*    in  v2 rather than in v1 (the two are bundled in the Coq algorithm).    *)
(*  + Then unifying ?m v1 with MatchedArg v2 at type matchedArg T, where      *)
(*    ?m : matchArg is a free unification variable, ensures that Coq always   *)
(*    solves v1 ~ v2 :> T, and fails promptly if this fails.                  *)
(*  + In short both (?m v1) ~ (MatchedArg v2) AND (MatchedArg v2) ~ (?m v1)   *)
(*    reduce to v1 ~ v2.                                                      *)
(*  + The wrapper type serves as a reminder that MatchedArg or (m : matchArg) *)
(*    wrappers must be inserted.                                              *)
(*  One important use for this feature is to match the pattern p_i for an     *)
(*  argument of a canonical instance (C p_1 ... p_n) of a projection f of     *)
(*  a structure S to the corresponding argument a_i of a value (C a_1 .. a_n) *)
(*  which we are unifying with f (?s : S), i.e., for which we are trying to   *)
(*  infer an instance of S. In this case Coq ALWAYS solve a_i ~ p_i, whereas  *)
(*  p_i ~ a_i may be needed to allow inferring canonical instances of         *)
(*  (recursive) projections in p_i for projections in a_i, when the latter    *)
(*  have default instances. Using (MatchedArg a_i) instead of a_i, and        *)
(*  (m p_i) with m : matchArg instead of p_i, ensures this.                   *)
Variant matchedArg T := PackMatchedArg of T.
Structure matchArg {T} := { apply_matchArg : T -> matchedArg T }.
Coercion apply_matchArg : matchArg >-> Funclass.
Variant matchArgLock := MatchArgLock.
Example MatchArgKey : matchArgLock. Proof. split. Qed.
Definition MatchedArg {T} (a : T) := let () := MatchArgKey in PackMatchedArg a.
Canonical MatchArgPattern T := {| apply_matchArg := @MatchedArg T |}.
(*   Implementation notes: MatchArg is defined as a locked constant to ensure *)
(* that if p ~ a fails then both ?m p ~ MatchArg a AND MatchArg a ~ ?m p fail *)
(* quickly, with the strategy followed by Coq's abstract unification machine  *)
(*   We write v1 =~= v2 for either v1 ~ v2 OR v2 ~ v1, and v|z1;z2;z3 for the *)
(* stack decomposition of a term z3[z2[z1[v]]], where the stack items z_i are *)
(* bits of execution context, e.g., ZApp(u_1,...,u_n) == [_] u_1 ... u_n or   *)
(* ZCase(b) == match [_] with .. b .. end, as in the Debug "unification" log. *)
(*   Then unifying MatchArg a with ?m p == apply_matchArg ?m p goes through   *)
(* the following sequence of problems                                         *)
(*    MatchedArg a =~= apply_matchArg ?m p                                    *)
(*    MatchedArg|Zapp(T, a) =~= apply_matchArg|Zapp(T, ?m, p) -- stack decomp *)
(*           ?m ~ MatchArgPattern T -- matching canonical sructure            *)
(*           p ~ a  -- extararg unification                                   *)
(*  If p ~ a succeed we are done; otherwise we go through:                    *)
(*   MatchedArg|Zapp(T, a) =~= ?m|Zcase(T);Zapp(p) -- unfold apply_matchArg   *)
(*  or                                                                        *)
(*   MatchArgKey|Zcase(a) =~= apply_matchArg ?m p -- unfold MatchArg          *)
(*  and then in either case                                                   *)
(*   MatchArgKey|Zcase(a) =~= ?m|Zcase(T);Zapp(p) -- fail, different stacks   *)
(*  If we had used PackMatchedArg insread of MatchedArg then we would have    *)
(*  ended up with                                                             *)
(*   PackMatchedArg|Zapp(T, a) =~= ?m|Zcase(T);Zapp(p)                        *)
(*                          a =~= p -- the "consume" heuristice               *)
(*  forcing us to solve a =~= p all over again, and even possibly diverging   *)
(* on a ~ p.                                                                  *)

(* Should work when CS resolution bug is fixed.
(* A structure that matches an arbitrayry (possible dependent) function.      *)
(*   It can be used to decompose an arbitrary application (?f ?a) using the   *)
(* pattern (?ef ?a) where ?ef : funPattern ?f. Note that the simple (?f ?a)   *)
(* pattern cannot reliably be used for this purpose, because the unification  *)
(* algorithm interprets this as a second-order pattern, unfolding the matchee *)
(* an even deferring the constraint.                                          *)
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

Declare Scope coerced_scope.
Delimit Scope coerced_scope with coerced.
Open Scope coerced_scope.
Reserved Notation "P" (at level 8, only printing).

Record finpredEnvelope (T : eqType) (P : {pred T}) :=
  FinpredEnvelope {envelope_seq :> seq T; _ : {subset P <= envelope_seq}}.
Add Printing Constructor finpredEnvelope.

(* Eta convertibility for finpred_seq construction and ManifestCoerced case. *)
#[projections(primitive)]
Record finpred T :=
  Finpred { finpred_pred; envelope : @finpredEnvelope T finpred_pred}.
Add Printing Constructor finpred.
Arguments Finpred {T} P E : rename.

Variant finpredPilot := TryInferFinpred.
Definition TryCoercedFinpred := TryInferFinpred.

Structure appliedFinpred (T : eqType) := AppliedFinpred {
(* resorting to unnamed fields because the #[canonical=no] attibute is *)
(* ignored in Coq 8.18 *)
  _ : T; _ : finpred T; _ : finpredPilot;
  applied_finpred_holds :> bool
}.

Definition finpred_source_class := finpred.
#[reversible=no, warnings="-uniform-inheritance"]
Coercion apply_finpred {T} x (F : finpred_source_class T) :=
  @AppliedFinpred T x F TryCoercedFinpred (finpred_pred F x).
Canonical finpred_predType T :=
  PredType (fun (F : finpred T) x => apply_finpred x F).
#[reversible=no, warnings="-uniform-inheritance"]
Coercion mem_finpred T (F : finpred T) : {pred T} :=
  fun x => apply_finpred x F.
Arguments mem_finpred {T} F x /.

HB.lock Definition support {T} (F : finpred T) :=
  undup (filter (finpred_pred F) (envelope F)).
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

Structure appliedFinpredMatch T (finT := finpred T) (x : T)
   (F : finT) (Px : matchedArg bool) (Px1 : bool) (F1 : finT) :=
  AppliedFinpredMatch {applied_finpred_pilot : finpredPilot}.

Structure coercedFinpredApp T (F : finpred T) (x : T) :=
  PackCoercedFinpredApp { apply_coerced_finpred :> bool }.
   (* app_of_coerced_finpred == finpred_pred F x *)
Notation CoercedFinpredApp A x :=
   (PackCoercedFinpredApp A x ((A : {pred _}) x)).
Canonical ManifestCoercedFinpredApp T F x :=
  PackCoercedFinpredApp F x (@finpred_pred T F x).
Canonical ManifestCoercedApplyFinpredApp T F x :=
  PackCoercedFinpredApp F x (@apply_finpred T x F).

Definition InferredFinpred := @Finpred.
Arguments InferredFinpred {T} P E : rename.
Notation "P" := (InferredFinpred P _) : coerced_scope.

Structure inferFinpred (T : eqType) (P : {pred T}) (F : finpred T) :=
  InferFinpred { finpred_pilot :> bool }. (* mem_finpred F == P *)

Definition TryFinType := @id bool.
Definition TryIfThenElse (mb : matchedArg bool) := TryFinType.
Definition TryOp := TryIfThenElse.
Definition TryFalse b := TryOp (MatchedArg b) b.

Canonical MatchCoercedFinpred T F x eFx (m : matchArg) :=
  let Fx0 := @apply_coerced_finpred T F x eFx in
  let Fx1 := finpred_pred F x in
  AppliedFinpredMatch x F (m Fx0) (TryFalse Fx1) F TryCoercedFinpred. 

Canonical MatchInferredFinpred T F x P E eF (m : matchArg) :=
  let Fx := @finpred_pilot T P F eF in
  let etaF := InferredFinpred (finpred_pred F) (envelope F) in
  AppliedFinpredMatch x (InferredFinpred P E) (m (P x)) Fx etaF TryInferFinpred.
  
Canonical MatchAppliedFinpred T x F Px eF :=
  let iF := @applied_finpred_pilot T x F (MatchedArg Px) (TryFalse Px) F eF in
  AppliedFinpred x F iF Px.

Variant finpredTarget (T : eqType) :=
  FinpredTarget (P0 P1 P2 : {pred T}) of finpred T.
#[reversible=yes, warnings="-uniform-inheritance"] 
Coercion target_of_finpred T P (F : finpred T) :=
  FinpredTarget P P (fun x => TryFalse (P x)) F.
#[reversible=no, warnings="-uniform-inheritance -ambiguous-paths"]
Coercion pred_finpred_target T P F eF P0 :=
  @FinpredTarget T P0 P (fun x => @finpred_pilot T P F (eF x)) F.

Structure labeledFinpred T :=
  LabelFinpred {#[reversible=no] unlabel_finpred :> finpred T}.
Add Printing Constructor labeledFinpred.
Canonical LabelInferredFinpred T P E :=
  LabelFinpred (@InferredFinpred T P E).
Canonical LabelCoercedFinpred T F := @LabelFinpred T F.

Structure finpredPattern (T : eqType) (phT : phant T) :=
  PackFinpredPattern {finpred_of_pattern :> labeledFinpred T}.
Definition FinpredPattern {T} := @PackFinpredPattern T (Phant T).
Notation "{ 'finpred' T }" := (finpredPattern (Phant T))
   (at level 0, T at level 100, format "{ 'finpred'  T }") : type_scope.
Canonical InferredFinpredPattern T P eF :=
  FinpredPattern (@LabelInferredFinpred T P eF).
Notation "P" := (@InferredFinpredPattern _ P _) : coerced_scope.

#[reversible=no]
Coercion CoercedFinpredPattern T (F : finpred_source_class T) :=
  FinpredPattern (LabelCoercedFinpred F).
Canonical CoercedFinpredPattern.
Canonical finpredPattern_predType (T : eqType) :=
  PredType (fun (F : {finpred T}) x => apply_finpred x F).

Variant finpredPatternTarget (T : eqType) := FinpredPatternTarget of {pred T}.
#[reversible=yes]
Coercion target_of_finpred_pattern T phT (F : @finpredPattern T phT) :=
   FinpredPatternTarget (fun x => apply_finpred x F).
#[reversible=no, warnings="-uniform-inheritance"]
Coercion finpred_pattern_target_of_pred (T : eqType) (P : {pred T}) :=
  @FinpredPatternTarget T [eta P].

Structure coerciblePredType T := CoerciblePredType {
  coerciblePredType_sort :> Type;
  #[canonical=no] coerce_sort_to_pred : coerciblePredType_sort -> {pred T}
}.
Coercion coerce_sort_to_pred : coerciblePredType_sort >-> pred_sort.
Definition TryPredType := @id Type.
Canonical PredTypeCoercible T (pT : predType T) :=
  @CoerciblePredType T (TryPredType pT) (@topred T pT).

Definition LabeledFinpredReverseCoercion T pT P0 P & @finpredEnvelope T P :=
  fun F0 => LabelFinpred (@reverse_coercion (finpred T) pT F0 P0).
Canonical LabelFinpredReverseCoercion T pT P0 (F : finpred T) :=
  @LabeledFinpredReverseCoercion T (TryPredType pT) P0 F (envelope F) F.
Canonical FinpredReverseCoercionPattern (T : eqType) pT P0 eF :=
  let F := Finpred (@coerce_sort_to_pred T pT P0) eF in
  FinpredPattern (LabeledFinpredReverseCoercion P0 eF F).
Notation "P0" := (@FinpredReverseCoercionPattern _ _ P0 _) : coerced_scope.

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

Program Definition finpredIr T (A : finpred T) (P : pred T) :=
  @Finpred T [pred x in A | P x] _.
Next Obligation. by exists (support A) => x /andP[]; rewrite mem_support. Qed.

Program Definition finpredIl (T : eqType) (P : pred T) (A : finpred T) :=
  @Finpred T [pred x | P x & x \in A] _.
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
#[warnings="-uniform-inheritance"]
Coercion finpred_seq T s := Finpred _ (@envelope_of_seq T s).
Canonical CoercedFinpred_seq (T : eqType) (s : seq T) x :=
  PackCoercedFinpredApp s x (mem_seq s x).

Structure labeled_bool := LabelBool {unlabel_bool :> bool}.
Add Printing Constructor labeled_bool.
Structure op_finpred {T : eqType} (P : pred T) (A : finpred T) :=
  OpFinpred {opFinpred_pilot :> labeled_bool}.
Add Printing Constructor op_finpred.
Canonical InferOpFinpred T P A (m : matchArg) (eA : @op_finpred T P A) b :=
  @InferFinpred T P A (TryOp (m (eA : bool)) b).

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
Definition LabelIl T a b (eNa : matchedArg bool) eb :=
  @LabelSigma T a b tt (TryFalse a) (fun=> eb) TryIdConv.
Definition TryConst := @id bool.
Canonical LabelI T a b := LabelIl T a b (MatchedArg (TryConst a)) (TryFalse b).

Canonical FinpredIr T a b P Q A (eA : inferFinpred P A) :=
  @OpFinpred T (fun x => P x && Q x) (finpredIr A Q) (LabelIr T a b eA).

Structure not_finpred (T : eqType) (P : {pred T}) :=
  NotFinpred {notFin_pilot :> bool}.
Add Printing Constructor not_finpred.
Canonical ConstNotFin T a a1 := @NotFinpred T (fun=> a) (TryConst a1).
Canonical NegbNotFin T P a := @NotFinpred T P (negb a).
Canonical GeqNotFin T m n m1 n1 := @NotFinpred T (fun x => m <= n x) (m1 <= n1).
(* Cut off spurrious attempt to infer a finpred structure for                 *)
(* @notFin_pilot T P ?n when P x is of the form applied_finpred_holds ...;    *)
(* this would actually succeed for if T were finite.                          *)
Example AppliedFinpredFinite (T : eqType) (x : T) : appliedFinpred T.
Proof. by split=> //; [apply: finpred0 | left]. Qed.
Canonical finpredFin T P x := @NotFinpred T P (@AppliedFinpredFinite T x).

Canonical FinpredIl T a b P Q B
  (m : matchArg) (nFa : not_finpred P) (eB : inferFinpred Q B) :=
  @OpFinpred T (fun x => P x && Q x) (finpredIl P B)
               (LabelIl T a b (m (nFa : bool)) eB).

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

Definition finPreim_subType A (T : eqType) P (B : @subEqType T P) :=
  @PcanFinPreim A B T val _ valK.
Canonical LabelValFinPreim {A T : eqType} {P} (B : @subEqType T P) x (y : B) :=
  let z := LabelFinPreimExpr x (TryVal (val y)) in
  @LabelFinPreimApp A B T (finPreim_subType A B) x z z y.

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
  @Finpred A [preim (fun x => f x x) of fF] _.
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
  @FinpredPredFor A T (LabelBool b0) (finpred_pred Ff) Ff.
Fixpoint ManyFinpredPred {A T : eqType} b0 Ffs f :=
  if Ffs isn't Ff :: Ffs' then LabelBool b0 else
  @FinpredPredFor A T (ManyFinpredPred b0 Ffs' f) (finpred_pred Ff) Ff f.
Arguments FinpredPredFor A {T} z0 P Ff f.
Arguments OneFinpredPred A {T} b0 Ff f.
Arguments ManyFinpredPred A {T} b0 Ffs f.

Canonical Finpred_finpred {A T} y0 (F : finpred T) f :=
  OneFinpredPred A (apply_finpred y0 F) F f.
Canonical Finpred_seq {A T} s f y0 :=
  @OneFinpredPred A T (mem_seq s y0) (finpred_seq s) f.
Canonical Finpred_leq A m0 n m := OneFinpredPred A (m0 <= n) (finpred_leq n) m.
Canonical Finpred_eq (A T : eqType) (a x0 y0 : T) y :=
  ManyFinpredPred A (x0 == y0 :> T) [:: finpred1 a; finpred1x a] y.
Canonical Finpred_eq_op (A T : eqType) eT0 (a x0 y0 : T) y :=
  ManyFinpredPred A (hasDecEq.eq_op eT0 x0 y0) [:: finpred1 a; finpred1x a] y.
Canonical Finpred_eqn A n m0 n0 y :=
  ManyFinpredPred A (eqn m0 n0) [:: finpred_leq n; finpred1 n; finpred1x n] y.

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
Definition LabelOnePreimFinpred {A T : eqType} pT op in_pT (P : pT) f y0 P0 :=
  @LabelPreimFinpred A T (fun x => op (f x) P) (in_pT P)
    (fun y => TryFalse (in_pT P y)) (fun x => TryVar (f x))
    (LabelBool (op y0 P0)).
Canonical InferPreimFinpred {A T : eqType} c (Pf : {pred A}) (P : {pred T}) F Ff
         (eF : T -> inferFinpred P F) (eFf : forall x, inferFinPreim F Ff x) :=
  OpFinpred Pf Ff
     (LabelPreimFinpred Pf P [eta eF] (fun x => finPreim_val (eFf x)) c).
Canonical Finpred_in {A T} P f y0 P0 :=
  @LabelOnePreimFinpred A T (mem_pred T) in_mem pred_of_mem P f y0 P0.

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
Lemma foo (D := fun T (x : T) => True)
  (G : forall (T : eqType) A, D {finpred T} A -> D {pred T} A)
  (T : eqType) (a b : T) (P Q : {finpred T}) :
   D {pred _} [pred x : {n | 5 < n} | sval x == 3].
Set Printing All.
Set Debug "unification".
refine (G _ _ _).
Abort.
Lemma foo (a : T) A B (D := fun U (z : U) => Prop) : True.
Set Printing Coercions.
Close Scope coerced_scope.
Undelimit Scope coerced_scope.
Set Printing Width 160.
Set Printing Implicit.
Set Debug "unification".
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

Definition disjoint (T : eqType) (A : finpred T) (mB : mem_pred T) :=
  @pred0b T [pred x in A | in_mem x mB].

Notation "[ 'disjoint' A & B ]" := (disjoint A (mem B))
  (at level 0,
   format "'[hv' [ 'disjoint' '/  '  A '/'  &  B ] ']'") : bool_scope.

HB.lock
Definition subset (T : eqType) (A : finpred T) (mB : mem_pred T) : bool :=
  pred0b [pred x in A | ~~ (in_mem x mB)].
Canonical subset_unlock := Unlockable subset.unlock.

Notation "A \subset B" := (subset A (mem B))
  (at level 70, no associativity) : bool_scope.

Definition proper (T : eqType) (A B : finpred T) :=
  (A \subset B) && ~~ (B \subset A).
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
have Dcard C: {subset C <= U} -> #|C| = count [in C] (support U).
  move=> sCU; rewrite unlock -size_filter; apply/perm_size.
  rewrite uniq_perm ?filter_uniq // => x.
  by rewrite mem_filter !inE andb_idr // => /sCU.
rewrite !{}Dcard ?count_predUI // => x /[!inE]; try case/andP; move=> -> //.
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

Lemma cardD1 x A : #|A| = (x \in A) + #|[predD1 A & x]|.
Proof.
apply/(@addnI (x \notin A)); rewrite addnA addn_negb -cardU1.
have <-: x \notin [predD1 A & x] = 1 :> nat by rewrite !inE eqxx.
by rewrite -cardU1; apply/eq_card=> y /[!inE]; rewrite orb_andr orbN.
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
rewrite unlock; apply: (iffP (pred0P _)) => [AP0 x | sAP x] /=.
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
Hint Resolve subxx : core.

Lemma eq_subset A B : A =i B -> forall P, (A \subset P) = (B \subset P).
Proof.
by move=> eqAB C; rewrite !unlock; apply: eq_pred0b => /= x; rewrite !inE eqAB.
Qed.

Lemma eq_subset_r P Q : P =i Q -> forall A, (A \subset P) = (A \subset Q).
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
move/subsetP=> s12; apply/subsetP=> x.
by rewrite !mem_filter => /andP[-> /s12].
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

Lemma eq_disjoint A B : A =i B -> forall P, [disjoint A & P] = [disjoint B & P].
Proof.
by move=> eqAB C; congr (_ == 0); apply: eq_card => x /=; rewrite !inE eqAB.
Qed.

Lemma eq_disjoint_r P Q :
  P =i Q -> forall A, [disjoint A & P] = [disjoint A & Q].
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
Proof. by move/eq_disjoint->; apply: disjoint0. Qed.

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
Local Hint Resolve enum_prec_eq_sorted : core.

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

(**********************************************************************)
(*                                                                    *)
(*  Boolean injectivity test for functions with a finpred domain      *)
(*                                                                    *)
(**********************************************************************)

Section Injectiveb.

Variables (aT rT : eqType) (f : aT -> rT).
Implicit Type D : {finpred aT}.

Definition dinjectiveb (D : finpred aT) := uniq (map f (support D)).

Lemma dinjectivePn D :
  reflect (exists2 x, x \in D & exists2 y, y \in [predD1 D & x] & f x = f y)
          (~~ dinjectiveb D).
Proof.
apply: (iffP idP) => [injf | [x Dx [y Dxy eqfxy]]]; last first.
  move: Dx; rewrite -mem_support => /rot_to[i E defE].
  rewrite /dinjectiveb -(rot_uniq i) -map_rot defE /=; apply/nandP; left.
  rewrite inE /= -mem_support -(mem_rot i) defE inE in Dxy.
  rewrite andb_orr andbC andbN in Dxy.
  by rewrite eqfxy map_f //; case/andP: Dxy.
pose P := [pred x in D | ~~ [disjoint [predD1 D & x] & [pred y | f x == f y]]].
have [noP | /pred0Pn[x /andP[Dx]]] := altP (@pred0P _ P); last first.
  by case/pred0Pn=> y /andP[Dy /eqP-Efxy]; exists x => //; exists y.
rewrite /dinjectiveb map_inj_in_uniq ?support_uniq // in injf => x y Dx Dy Efxy.
apply/esym; apply: contraFeq (noP x) => x'y /=; rewrite -mem_support Dx /=.
by apply/pred0Pn; exists y; rewrite !inE x'y -mem_support Dy Efxy eqxx.
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

End Injectiveb.

Definition image (T : choiceType) T' f (A : finpred T) : seq T' :=
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
apply: (iffP eqP); [rewrite [in RHS]unlock=> eqfA | exact: card_in_image].
apply/dinjectiveP/card_uniqP; rewrite size_map -{}eqfA.
by apply/esym/eq_card/eq_mem_map; rewrite unlock; apply: mem_sort.
Qed.

Hypothesis injf : injective f.

Lemma card_image A : #|image f A| = #|A|.
Proof. by apply: card_in_image; apply: in2W. Qed.

End ChoiceCardFunImage.
Arguments image_injP {T T' f A}.

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

(* Beware: these are not the canonical instances, as they are not consistent  *)
(* with the generic sub_choiceType canonical instance.                        *)
Definition adhoc_seq_sub_choiceType : choiceType := pcan_type seq_sub_pickleK.
Definition adhoc_seq_sub_countType := HB.pack_for countType seq_sub
  seq_sub_isCountable (Choice.class adhoc_seq_sub_choiceType).

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

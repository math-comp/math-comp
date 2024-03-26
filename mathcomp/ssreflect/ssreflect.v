(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From Coq Require Export ssreflect.
Global Set SsrOldRewriteGoalsOrder.
Global Set Asymmetric Patterns.
Global Set Bullet Behavior "None".

(******************************************************************************)
(* v8.20 additions:                                                           *)
(*                                                                            *)
(* [elaborate x] == triggers coq elaboration to fill the holes of the term x  *)
(*                  The main use case is to trigger typeclass inference in    *)
(*                  the body of a ssreflect have := [elaborate body].         *)
(*                                                                            *)
(*   Intro pattern ltac views:                                                *)
(*   - calling rewrite from an intro pattern, use with parsimony              *)
(*     => /[1! rules]  := rewrite rules                                       *)
(*     => /[! rules]   := rewrite !rules                                      *)
(*                                                                            *)
(*     vm_compute == A class to trigger reduction by rewriting.               *)
(* --> Usage: rewrite [pattern]vm_compute.                                    *)
(* --> Alternatively one may redefine a lemma as in algebra/rat.v :           *)
(*     Lemma rat_vm_compute n (x : rat) : vm_compute_eq n%:Q x -> n%:Q = x.   *)
(*     Proof. exact. Qed.                                                     *)
(*                                                                            *)
(*   V, V%coerced == reserved only printing notation for declaring printing   *)
(*                   rules for coercion-like expressions C ... V ... which    *)
(*                   should be displayed as V. This is declared at level 8 so *)
(*                   V will be displayed as (V), with parentheses, if V is an *)
(*                   application or infix expression.                         *)
(*        -> Usage: Notation "V" := (C ... V ...) : coerced_scope.            *)
(*           To display the %coerced tag: Close Scope coerced_scope.          *)
(*           To further disable the notation : Undelimit Scope coerced_scope. *)
(*                                                                            *)
(*   matchedArg T == a special-purpose wrapper type that provides some        *)
(*                   control over unification priorities (see below).         *)
(*     MatchedArg == a special constructor for matchedArg T (with T implicit) *)
(*       matchArg == singleton structure type for MatchArg (with T implicit)  *)
(* --> Usage:                                                                 *)
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
(*                                                                            *)
(*    infer_type t == a pattern that will unify with any e : T, while         *)
(*                    instantiating T to the actual inferred type of e, when  *)
(*                    t : inferType T is unconstrained.                       *)
(* --> This is useful because Coq sometimes defers unification constraints    *)
(*     that arise from the types of unification variables. Using infer_type   *)
(*     allows the synchronous resolution of structures such as forallSort     *)
(*     that depend on types.                                                  *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "[ 'elaborate' x ]" (at level 0).

Notation "[ 'elaborate' x ]" := (ltac:(refine x)) (only parsing).

Module Export ipat.

Notation "'[' '1' '!' rules ']'"     := (ltac:(rewrite rules))
  (at level 0, rules at level 200, only parsing) : ssripat_scope.
Notation "'[' '!' rules ']'"         := (ltac:(rewrite !rules))
  (at level 0, rules at level 200, only parsing) : ssripat_scope.

End ipat.

(* A class to trigger reduction by rewriting.                           *)
(* Usage: rewrite [pattern]vm_compute.                                  *)
(* Alternatively one may redefine a lemma as in algebra/rat.v :         *)
(* Lemma rat_vm_compute n (x : rat) : vm_compute_eq n%:Q x -> n%:Q = x. *)
(* Proof. exact. Qed.                                                   *)

Class vm_compute_eq {T : Type} (x y : T) := vm_compute : x = y.

#[global]
Hint Extern 0 (@vm_compute_eq _ _ _) =>
       vm_compute; reflexivity : typeclass_instances.

Reserved Notation "V" (at level 8, only printing).
Declare Scope coerced_scope.
Delimit Scope coerced_scope with coerced.
Open Scope coerced_scope.

(*   Implementation notes: MatchArg is defined as a locked constant to ensure *)
(* that if p ~ a fails then both ?m p ~ MatchArg a AND MatchArg a ~ ?m p fail *)
(* quickly, with the strategy followed by Coq's abstract unification machine  *)
(*   We write v1 =~= v2 for either v1 ~ v2 OR v2 ~ v1, and v|z1;z2;z3 for the *)
(* stack decomposition of a term z3[z2[z1[v]]], where the stack items z_i are *)
(* bits of execution context, e.g., ZApp(u_1,...,u_n) == [_] u_1 ... u_n or   *)
(* ZCase(b) == match [_] with .. => b end, as in the Debug "unification" log. *)
(*   Then unifying MatchArg a with ?m p goes through the following sequence   *)
(* of problems:                                                               *)
(*    MatchedArg a =~= ?m p (:= MatchArg.apply ?m p)                          *)
(*    MatchedArg|Zapp(T, a) =~= MatchArg.apply|Zapp(T, ?m, p) -- stack decomp *)
(*           ?m ~ MatchArg.Pattern T -- matching canonical sructure           *)
(*           p ~ a  -- extararg unification                                   *)
(*  If p ~ a succeed we are done; otherwise we go through:                    *)
(*   MatchArg.Matched|Zapp(T, a) =~= ?m|Zcase(T);Zapp(p) -- unfold apply   *)
(*  or                                                                        *)
(*   MatchArg.Key|Zcase(a) =~= MatchArg.apply ?m p -- unfold MatchArg         *)
(*  and then in either case                                                   *)
(*   MatchArgKey|Zcase(a) =~= ?m|Zcase(T);Zapp(p) -- fail, different stacks   *)
(*  If we had used PackMatchedArg insread of MatchedArg then we would have    *)
(*  ended up with                                                             *)
(*   PackMatchedArg|Zapp(T, a) =~= ?m|Zcase(T);Zapp(p)                        *)
(*                          a =~= p -- the "consume" heuristice               *)
(*  forcing us to solve a =~= p all over again, and even possibly diverging   *)
(* on a ~ p.                                                                  *)
Module MatchArg.

Variant matched T := Matched of T.
Structure matcher {T} := { apply : T -> matched T }.
Variant lock := Lock. Example Key : lock. Proof. exact Lock. Qed.
Definition Matcher {T} a := let: Lock := Key in @Matched T a.
Definition Pattern T := {| apply := @Matcher T |}.
End MatchArg.
Notation matchedArg := MatchArg.matched.
Notation matchArg := MatchArg.matcher.
Coercion MatchArg.apply : matchArg >-> Funclass.
Notation MatchedArg := MatchArg.Matcher.
Canonical MatchArg.Pattern.

Structure inferType T := BuildInferType {infer_type : T}.
Canonical InferType {T} x := @BuildInferType T x.

#[deprecated(since="mathcomp 2.4", note="Use `Arguments def : simpl never` instead (should work fine since Coq 8.18).")]
Notation nosimpl t := (nosimpl t).

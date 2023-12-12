Require Setoid.
From mathcomp Require Import ssreflect ssrfun.
From Coq Require Export ssrbool.

(******************************************************************************)
(* Local additions:                                                           *)
(*        [in A] == the applicative counterpart of a collective predicate A:  *)
(*                  [in A] x beta-expands to x \in A. This is similar to      *)
(*                  mem A, except that mem A x only simplfies to x \in A.     *)
(* --> These will become part of the core SSReflect library in later Coq      *)
(* versions.                                                                  *)
(*   For the sake of backwards compatibility, this file also replicates       *)
(* v8.13-15 additions, including a generalization of the statments of         *)
(* `homoRL_in`, `homoLR_in`, `homo_mono_in`, `monoLR_in`, `monoRL_in`, and    *)
(* `can_mono_in`.                                                             *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*******************)
(* v8.20 additions *)
(*******************)

Notation "[ 'in' A ]" := (in_mem^~ (mem A))
  (at level 0, format "[ 'in'  A ]") : function_scope.

(* The notations below are already defined in Coq.ssr.ssrbool, but we redefine*)
(* them in different notation scopes (mostly fun_scope -> function_scope, in  *)
(* order to replace the former with the latter).                              *)

Notation "[ 'pred' : T | E ]" := (SimplPred (fun _ : T => E%B)) :
  function_scope.
Notation "[ 'pred' x | E ]" := (SimplPred (fun x => E%B)) : function_scope.
Notation "[ 'pred' x | E1 & E2 ]" := [pred x | E1 && E2 ] : function_scope.
Notation "[ 'pred' x : T | E ]" :=
  (SimplPred (fun x : T => E%B)) (only parsing) : function_scope.
Notation "[ 'pred' x : T | E1 & E2 ]" :=
  [pred x : T | E1 && E2 ] (only parsing) : function_scope.

Notation "[ 'rel' x y | E ]" := (SimplRel (fun x y => E%B))
  (only parsing) : function_scope.
Notation "[ 'rel' x y : T | E ]" :=
  (SimplRel (fun x y : T => E%B)) (only parsing) : function_scope.

Notation "[ 'mem' A ]" :=
  (pred_of_simpl (simpl_of_mem (mem A))) (only parsing) : function_scope.

Notation "[ 'pred' x 'in' A ]" := [pred x | x \in A] : function_scope.
Notation "[ 'pred' x 'in' A | E ]" := [pred x | x \in A & E] : function_scope.
Notation "[ 'pred' x 'in' A | E1 & E2 ]" :=
  [pred x | x \in A & E1 && E2 ] : function_scope.

Notation "[ 'rel' x y 'in' A & B | E ]" :=
  [rel x y | (x \in A) && (y \in B) && E] : function_scope.
Notation "[ 'rel' x y 'in' A & B ]" :=
  [rel x y | (x \in A) && (y \in B)] : function_scope.
Notation "[ 'rel' x y 'in' A | E ]" := [rel x y in A & A | E] : function_scope.
Notation "[ 'rel' x y 'in' A ]" := [rel x y in A & A] : function_scope.

(* Both bodies and the scope have been changed for the following notations.   *)
Notation "[ 'predI' A & B ]" := (predI [in A] [in B]) : function_scope.
Notation "[ 'predU' A & B ]" := (predU [in A] [in B]) : function_scope.
Notation "[ 'predD' A & B ]" := (predD [in A] [in B]) : function_scope.
Notation "[ 'predC' A ]" := (predC [in A]) : function_scope.
Notation "[ 'preim' f 'of' A ]" := (preim f [in A]) : function_scope.

(*******************)
(* v8.17 additions *)
(*******************)

Lemma all_sig2_cond {I T} (C : pred I) P Q :
    T -> (forall x, C x -> {y : T | P x y & Q x y}) ->
  {f : I -> T | forall x, C x -> P x (f x) & forall x, C x -> Q x (f x)}.
Proof.
by move=> /all_sig_cond/[apply]-[f Pf]; exists f => i Di; have [] := Pf i Di.
Qed.

Lemma can_in_pcan [rT aT : Type] (A : {pred aT}) [f : aT -> rT] [g : rT -> aT] :
  {in A, cancel f g} -> {in A, pcancel f (fun y : rT => Some (g y))}.
Proof. by move=> fK x Ax; rewrite fK. Qed.

Lemma pcan_in_inj [rT aT : Type] [A : {pred aT}]
    [f : aT -> rT] [g : rT -> option aT] :
  {in A, pcancel f g} -> {in A &, injective f}.
Proof. by move=> fK x y Ax Ay /(congr1 g); rewrite !fK// => -[]. Qed.

Lemma in_inj_comp A B C (f : B -> A) (h : C -> B) (P : pred B) (Q : pred C) :
  {in P &, injective f} -> {in Q &, injective h} -> {homo h : x / Q x >-> P x} ->
  {in Q &, injective (f \o h)}.
Proof.
by move=> Pf Qh QP x y xQ yQ xy; apply Qh => //; apply Pf => //; apply QP.
Qed.

Lemma can_in_comp [A B C : Type] (D : {pred B}) (D' : {pred C})
    [f : B -> A] [h : C -> B] [f' : A -> B] [h' : B -> C] :
  {homo h : x / x \in D' >-> x \in D} ->
  {in D, cancel f f'} -> {in D', cancel h h'} ->
  {in D', cancel (f \o h) (h' \o f')}.
Proof. by move=> hD fK hK c cD /=; rewrite fK ?hK ?hD. Qed.

Lemma pcan_in_comp [A B C : Type] (D : {pred B}) (D' : {pred C})
    [f : B -> A] [h : C -> B] [f' : A -> option B] [h' : B -> option C] :
  {homo h : x / x \in D' >-> x \in D} ->
  {in D, pcancel f f'} -> {in D', pcancel h h'} ->
  {in D', pcancel (f \o h) (obind h' \o f')}.
Proof. by move=> hD fK hK c cD /=; rewrite fK/= ?hK ?hD. Qed.

Definition pred_oapp T (D : {pred T}) : pred (option T) :=
  [pred x | oapp (mem D) false x].

Lemma ocan_in_comp [A B C : Type] (D : {pred B}) (D' : {pred C})
    [f : B -> option A] [h : C -> option B] [f' : A -> B] [h' : B -> C] :
  {homo h : x / x \in D' >-> x \in pred_oapp D} ->
  {in D, ocancel f f'} -> {in D', ocancel h h'} ->
  {in D', ocancel (obind f \o h) (h' \o f')}.
Proof.
move=> hD fK hK c cD /=; rewrite -[RHS]hK/=; case hcE : (h c) => [b|]//=.
have bD : b \in D by have := hD _ cD; rewrite hcE inE.
by rewrite -[b in RHS]fK; case: (f b) => //=; have /hK := cD; rewrite hcE.
Qed.

Lemma eqbLR (b1 b2 : bool) : b1 = b2 -> b1 -> b2.
Proof. by move->. Qed.

Lemma eqbRL (b1 b2 : bool) : b1 = b2 -> b2 -> b1.
Proof. by move->. Qed.

Lemma homo_mono1 [aT rT : Type] [f : aT -> rT] [g : rT -> aT]
    [aP : pred aT] [rP : pred rT] :
  cancel g f ->
  {homo f : x / aP x >-> rP x} ->
  {homo g : x / rP x >-> aP x} -> {mono g : x / rP x >-> aP x}.
Proof. by move=> gK fP gP x; apply/idP/idP => [/fP|/gP//]; rewrite gK. Qed.

Lemma if_and b1 b2 T (x y : T) :
  (if b1 && b2 then x else y) = (if b1 then if b2 then x else y else y).
Proof. by case: b1 b2 => [] []. Qed.

Lemma if_or b1 b2 T (x y : T) :
  (if b1 || b2 then x else y) = (if b1 then x else if b2 then x else y).
Proof. by case: b1 b2 => [] []. Qed.

Lemma if_implyb b1 b2 T (x y : T) :
  (if b1 ==> b2 then x else y) = (if b1 then if b2 then x else y else x).
Proof. by case: b1 b2 => [] []. Qed.

Lemma if_implybC b1 b2 T (x y : T) :
  (if b1 ==> b2 then x else y) = (if b2 then x else if b1 then y else x).
Proof. by case: b1 b2 => [] []. Qed.

Lemma if_add b1 b2 T (x y : T) :
  (if b1 (+) b2 then x else y) = (if b1 then if b2 then y else x else if b2 then x else y).
Proof. by case: b1 b2 => [] []. Qed.

(**********************)
(* not yet backported *)
(**********************)

Lemma relpre_trans {T' T : Type} {leT : rel T} {f : T' -> T} :
  transitive leT -> transitive (relpre f leT).
Proof. by move=> + y x z; apply. Qed.

Class classical_logic := {
  functional_extensionality_dep :
       forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
       (forall x : A, f x = g x) -> f = g;
  propositional_extensionality :
       forall P Q : Prop, P <-> Q -> P = Q;
  constructive_indefinite_description :
    forall (A : Type) (P : A -> Prop),
    (exists x : A, P x) -> {x : A | P x}
}.


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
Proof. by elimPh phP; elimPh phQ; split=> [] /=; clear d; firstorder. Qed.
(* or rather import skolemization to avoid the fragility of firstorder relying on unused context variables *)
(* by elimPh phP; elimPh phQ; split=> [/all_and|] [].*)

Lemma prop3_pairE P Q phP phQ : prop3_pair P Q phP phQ <-> phP /\ phQ.
Proof. 
by elimPh phP; elimPh phQ; split=> [] /=; clear d; firstorder. Qed.
(* or import skolemization? *)
(* by elimPh phP; elimPh phQ; split=> [/all_and|] []. *)

Lemma prop_in2_pair P Q phP phQ :
       prop_in2 d (inPhantom (prop2_pair P Q phP phQ))
   <-> prop_in2 d phP /\ prop_in2 d phQ.
Proof. by firstorder. Qed.
(* or import skolemization? *)
(* by elimPh phP; elimPh phQ; split=> [/all_and|] []; split; auto. *)

Lemma prop_in3_pair P Q phP phQ :
       prop_in3 d (inPhantom (prop3_pair P Q phP phQ))
   <-> prop_in3 d phP /\ prop_in3 d phQ.
Proof. by rewrite /=; firstorder. Qed.
(* or import skolemization? *)
(* by elimPh phP; elimPh phQ; split=> [/all_and|] []; split; auto. *)

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

From mathcomp Require Import ssreflect ssrfun.
From Coq Require Export ssrbool.

(* 8.11 addition in Coq but renamed *)
#[deprecated(since="mathcomp 1.15", note="Use rel_of_simpl instead.")]
Notation rel_of_simpl_rel := rel_of_simpl.

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

(******************)
(* v8.15 addtions *)
(******************)

Section ReflectCombinators.

Variables (P Q : Prop) (p q : bool).

Hypothesis rP : reflect P p.
Hypothesis rQ : reflect Q q.

Lemma negPP : reflect (~ P) (~~ p).
Proof. by apply:(iffP negP); apply: contra_not => /rP. Qed.

Lemma andPP : reflect (P /\ Q) (p && q).
Proof. by apply: (iffP andP) => -[/rP ? /rQ ?]. Qed.

Lemma orPP : reflect (P \/ Q) (p || q).
Proof. by apply: (iffP orP) => -[/rP ?|/rQ ?]; tauto. Qed.

Lemma implyPP : reflect (P -> Q) (p ==> q).
Proof. by apply: (iffP implyP) => pq /rP /pq /rQ. Qed.

End ReflectCombinators.
Arguments negPP {P p}.
Arguments andPP {P Q p q}.
Arguments orPP {P Q p q}.
Arguments implyPP {P Q p q}.
Prenex Implicits negPP andPP orPP implyPP.

(*******************)
(* v8.16 additions *)
(*******************)

(******************************************************************************)
(*          pred_oapp T D := [pred x | oapp (mem D) false x]                  *)
(******************************************************************************)

Lemma mono1W_in (aT rT : predArgType) (f : aT -> rT) (aD : {pred aT})
    (aP : pred aT) (rP : pred rT) :
  {in aD, {mono f : x / aP x >-> rP x}} ->
  {in aD, {homo f : x / aP x >-> rP x}}.
Proof. by move=> fP x xD xP; rewrite fP. Qed.
Arguments mono1W_in [aT rT f aD aP rP].

#[deprecated(since="mathcomp 1.14.0", note="Use mono1W_in instead.")]
Notation mono2W_in := mono1W_in.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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

(********************)
(* Future additions *)
(********************)

Notation "[ 'in' A ]" := (in_mem^~ (mem A))
  (at level 0, format "[ 'in'  A ]") : fun_scope.

Notation "[ 'predI' A & B ]" := (predI [in A] [in B]) : fun_scope.
Notation "[ 'predU' A & B ]" := (predU [in A] [in B]) : fun_scope.
Notation "[ 'predD' A & B ]" := (predD [in A] [in B]) : fun_scope.
Notation "[ 'predC' A ]" := (predC [in A]) : fun_scope.
Notation "[ 'preim' f 'of' A ]" := (preim f [in A]) : fun_scope.

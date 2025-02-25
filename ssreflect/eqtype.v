(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool.

(******************************************************************************)
(*                      Types with a decidable equality                       *)
(*                                                                            *)
(* NB: See CONTRIBUTING.md for an introduction to HB concepts and commands.   *)
(*                                                                            *)
(* This file defines two "base" combinatorial structures:                     *)
(*      eqType == types with a decidable equality                             *)
(*                The HB class is called Equality.                            *)
(*                The equality operation on an eqType is proof-irrelevant     *)
(*                (lemma eq_irrelevance).                                     *)
(*                The main notation is the boolean equality "==", see below.  *)
(*   subType P == types isomorphic to {x : T | P x}                           *)
(*                with P : pred T for some type T                             *)
(*                The HB class is called SubType.                             *)
(* subEqType P == join of eqType and subType P                                *)
(*                The HB class is called SubEquality.                         *)
(*                                                                            *)
(* The eqType interface supports the following operations (in bool_scope):    *)
(*              x == y <=> x compares equal to y (this is a boolean test)     *)
(*         x == y :> T <=> x == y at type T                                   *)
(*              x != y <=> x and y compare unequal                            *)
(*         x != y :> T <=> x and y compare unequal at type T                  *)
(*              x =P y :: a proof of reflect (x = y) (x == y); x =P y coerces *)
(*                        to x == y -> x = y                                  *)
(*              eqbLHS := (X in (X == _))%pattern (for rewriting)             *)
(*              eqbRHS := (X in (_ == X))%pattern (for rewriting)             *)
(*               eq_op == the boolean relation behind the == notation         *)
(*                        (see lemma eqE below for generic folding            *)
(*                        of equality predicates)                             *)
(*                 eqP == proof of Equality.axiom eq_op behind the =P notation*)
(*    Equality.axiom e <-> e : rel T is a valid comparison decision procedure *)
(*                        for type T: reflect (x = y) (e x y) for all x y : T *)
(*             pred1 a == the singleton predicate [pred x | x == a]           *)
(* pred2, pred3, pred4 == pair, triple, quad predicates                       *)
(*            predC1 a == [pred x | x != a]                                   *)
(*      [predU1 a & A] == [pred x | (x == a) || (x \in A)]                    *)
(*      [predD1 A & a] == [pred x | x != a & x \in A]                         *)
(*  predU1 a P, predD1 P a == applicative versions of the above               *)
(*              frel f == the relation associated with f : T -> T             *)
(*                     := [rel x y | f x == y]                                *)
(*       invariant f k == elements of T whose k-class is f-invariant          *)
(*                     := [pred x | k (f x) == k x] with f : T -> T           *)
(*  [fun x : T => e0 with a1 |-> e1, .., a_n |-> e_n]                         *)
(*  [eta f with a1 |-> e1, .., a_n |-> e_n] ==                                *)
(*    the auto-expanding function that maps x = a_i to e_i, and other values  *)
(*    of x to e0 (resp. f x). In the first form the `: T' is optional and x   *)
(*    can occur in a_i or e_i                                                 *)
(*          dfwith f x == fun j => x if j = i, and f j otherwise, given       *)
(*                        f : forall k, T k and x : T i                       *)
(*  We also define:                                                           *)
(*   tagged_as u v == v cast as T_(tag u) if tag v == tag u, else u           *)
(*  -> We have u == v <=> (tag u == tag v) && (tagged u == tagged_as u v)     *)
(*                                                                            *)
(* The subType interface supports the following operations:                   *)
(*     \val == the generic injection from a subType S of T into T             *)
(*             For example, if u : {x : T | P}, then val u : T                *)
(*             val is injective because P is proof-irrelevant (P is in bool,  *)
(*             and the is_true coercion expands to P = true).                 *)
(*     valP == the generic proof of P (val u) for u : subType P               *)
(* Sub x Px == The generic constructor for a subType P; Px is a proof of P x  *)
(*             and P should be inferred from the expected return type.        *)
(*  insub x == the generic partial projection of T into a subType S of T      *)
(*             This returns an option S; if S : subType P then                *)
(*                insub x = Some u with val u = x if P x,                     *)
(*                          None if ~~ P x                                    *)
(*             The insubP lemma encapsulates this dichotomy.                  *)
(*             P should be inferred from the expected return type.            *)
(*  innew x == total (non-option) variant of insub when P = predT             *)
(* {? x | P} == option {x | P} (syntax for casting insub x)                   *)
(* insubd u0 x == the generic projection with default value u0                *)
(*             := odflt u0 (insub x)                                          *)
(* insigd A0 x == special case of insubd for S == {x | x \in A}, where A0 is  *)
(*                a proof of x0 \in A                                         *)
(* insub_eq x == transparent version of insub x that expands to Some/None     *)
(*               when P x can evaluate                                        *)
(*                                                                            *)
(* * Sub                                                                      *)
(* ** Specific notations                                                      *)
(*   [isSub of S for S_val] == subtype for S where S_val : S -> T is the      *)
(*     first projection of a type S isomorphic to {x : T | P}; if S_val is    *)
(*     specified, then it replaces the inferred projector.                    *)
(*   [isSub for S_val] := [isSub of _ for S_val]                              *)
(*     It clones the canonical subType structure for S.                       *)
(*   [isNew of S for S_val] == subtype for S where S_val : S -> T is the      *)
(*     projection of a type S isomorphic to T; in this case P must be predT   *)
(*   [isNew for S_val] := [isNew of _ for S_val]                              *)
(*   [isSub for S_val by Srect], [isNew for S_val by Srect] ==                *)
(*     variants of the above where the eliminator is explicitly provided.     *)
(*     Here S no longer needs to be syntactically identical to {x | P x} or   *)
(*     wrapped T, but it must have a derived constructor S_Sub satisfying an  *)
(*     eliminator Srect identical to the one the Coq Inductive command would  *)
(*     have generated, and S_val (S_Sub x Px) (resp. S_val (S_sub x) for the  *)
(*     newType form) must be convertible to x.                                *)
(*     variant of the above when S is a wrapper type for T (so P = predT).    *)
(*   Subtypes inherit the eqType structure of their base types; the generic   *)
(*   structure should be explicitly instantiated using the                    *)
(*     [Equality of S by <:]                                                  *)
(*   construct; this pattern is repeated for all the combinatorial interfaces *)
(*   (Choice, Countable, Finite).                                             *)
(*                                                                            *)
(* List of factories with a dedicated alias (not generated automatically):    *)
(*   inj_type injf == alias of T to copy an interface from another T' already *)
(*                    equipped with it and injf : injective f with f : T -> T'*)
(*    pcan_type fK == alias of T to similarly derive an interface from f and  *)
(*                    a left inverse partial function g and fK : pcancel f g  *)
(*     can_type fK == alias of T to similarly derive an interface from f and  *)
(*                    a left inverse function g and fK : cancel f g           *)
(*     sub_type sT == alias of sT : subType _                                 *)
(*                                                                            *)
(*       comparable T <-> equality on T is decidable.                         *)
(*                    := forall x y : T, decidable (x = y)                    *)
(*  comparableMixin compT == equality mixin for compT : comparable T          *)
(*                                                                            *)
(* The eqType interface is implemented for most standard datatypes:           *)
(*  bool, unit, void, option, prod (denoted A * B), sum (denoted A + B),      *)
(*  sig (denoted {x | P}), sigT (denoted {i : I & T}).                        *)
(*                                                                            *)
(*   We add the following to the standard suffixes documented in ssrbool.v:   *)
(*  1, 2, 3, 4 -- explicit enumeration predicate for 1 (singleton), 2, 3, or  *)
(*                4 values                                                    *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope eq_scope.
Declare Scope fun_delta_scope.

Add Search Blacklist "Builders_".
Add Search Blacklist "__canonical__".
Add Search Blacklist "__to__".
Add Search Blacklist "_between_".
Add Search Blacklist "_mixin".

Definition eq_axiom T (e : rel T) := forall x y, reflect (x = y) (e x y).

HB.mixin Record hasDecEq T := { eq_op : rel T; eqP : eq_axiom eq_op }.

#[mathcomp(axiom="eq_axiom"), short(type="eqType")]
HB.structure Definition Equality := { T of hasDecEq T }.

(* eqE is a generic lemma that can be used to fold back recursive comparisons *)
(* after using partial evaluation to simplify comparisons on concrete         *)
(* instances. The eqE lemma can be used e.g. like so: rewrite !eqE /= -!eqE.  *)
(* For instance, with the above rewrite, n.+1 == n.+1 gets simplified to      *)
(* n == n. For this to work, we need to declare equality _mixins_             *)
(* as canonical. Canonical declarations remove the need for specific          *)
(* inverses to eqE (like eqbE, eqnE, eqseqE, etc.) for new recursive          *)
(* comparisons, but can only be used for manifest mixing with a bespoke       *)
(* comparison function, and so is incompatible with PcanEqMixin and the like  *)
(* - this is why the tree_hasDecEq for GenTree.tree in library choice is not  *)
(* declared Canonical.                                                        *)
Lemma eqE (T : eqType) x : eq_op x = hasDecEq.eq_op (Equality.class T) x.
Proof. by []. Qed.

Arguments eqP {T x y} : rename.

Delimit Scope eq_scope with EQ.
Open Scope eq_scope.

Notation "x == y" := (eq_op x y)
  (at level 70, no associativity) : bool_scope.
Notation "x == y :> T" := ((x : T) == (y : T))
  (at level 70, y at next level) : bool_scope.
Notation "x != y" := (~~ (x == y))
  (at level 70, no associativity) : bool_scope.
Notation "x != y :> T" := (~~ (x == y :> T))
  (at level 70, y at next level) : bool_scope.
Notation "x =P y" := (eqP : reflect (x = y) (x == y))
  (at level 70, no associativity) : eq_scope.
Notation "x =P y :> T" := (eqP : reflect (x = y :> T) (x == y :> T))
  (at level 70, y at next level, no associativity) : eq_scope.

Notation eqbLHS := (X in (X == _))%pattern.
Notation eqbRHS := (X in (_ == X))%pattern.

Lemma eq_refl (T : eqType) (x : T) : x == x. Proof. exact/eqP. Qed.
Notation eqxx := eq_refl.

Lemma eq_sym (T : eqType) (x y : T) : (x == y) = (y == x).
Proof. exact/eqP/eqP. Qed.

#[global] Hint Resolve eq_refl eq_sym : core.

Variant eq_xor_neq (T : eqType) (x y : T) : bool -> bool -> Set :=
  | EqNotNeq of x = y : eq_xor_neq x y true true
  | NeqNotEq of x != y : eq_xor_neq x y false false.

Lemma eqVneq (T : eqType) (x y : T) : eq_xor_neq x y (y == x) (x == y).
Proof. by rewrite eq_sym; case: (altP eqP); constructor. Qed.

Arguments eqVneq {T} x y, {T x y}.

Section Contrapositives.

Variables (T1 T2 : eqType).
Implicit Types (A : pred T1) (b : bool) (P : Prop) (x : T1) (z : T2).

Lemma contraTeq b x y : (x != y -> ~~ b) -> b -> x = y.
Proof. by move=> imp hyp; apply/eqP; apply: contraTT hyp. Qed.

Lemma contraNeq b x y : (x != y -> b) -> ~~ b -> x = y.
Proof. by move=> imp hyp; apply/eqP; apply: contraNT hyp. Qed.

Lemma contraFeq b x y : (x != y -> b) -> b = false -> x = y.
Proof. by move=> imp /negbT; apply: contraNeq. Qed.

Lemma contraPeq P x y : (x != y -> ~ P) -> P -> x = y.
Proof. by move=> imp HP; apply: contraTeq isT => /imp /(_ HP). Qed.

Lemma contra_not_eq P x y : (x != y -> P) -> ~ P -> x = y.
Proof. by move=> imp; apply: contraPeq => /imp HP /(_ HP). Qed.

Lemma contra_not_neq P x y : (x = y -> P) -> ~ P -> x != y.
Proof. by move=> imp; apply: contra_notN => /eqP. Qed.

Lemma contraTneq b x y : (x = y -> ~~ b) -> b -> x != y.
Proof. by move=> imp; apply: contraTN => /eqP. Qed.

Lemma contraNneq b x y : (x = y -> b) -> ~~ b -> x != y.
Proof. by move=> imp; apply: contraNN => /eqP. Qed.

Lemma contraFneq b x y : (x = y -> b) -> b = false -> x != y.
Proof. by move=> imp /negbT; apply: contraNneq. Qed.

Lemma contraPneq P x y : (x = y -> ~ P) -> P -> x != y.
Proof. by move=> imp; apply: contraPN => /eqP. Qed.

Lemma contra_eqN b x y : (b -> x != y) -> x = y -> ~~ b.
Proof. by move=> imp /eqP; apply: contraL. Qed.

Lemma contra_eqF b x y : (b -> x != y) -> x = y -> b = false.
Proof. by move=> imp /eqP; apply: contraTF. Qed.

Lemma contra_eqT b x y : (~~ b -> x != y) -> x = y -> b.
Proof. by move=> imp /eqP; apply: contraLR. Qed.

Lemma contra_neqN b x y : (b -> x = y) -> x != y -> ~~ b.
Proof. by move=> imp; apply: contraNN => /imp->. Qed.

Lemma contra_neqF b x y : (b -> x = y) -> x != y -> b = false.
Proof. by move=> imp; apply: contraNF => /imp->. Qed.

Lemma contra_neqT b x y : (~~ b -> x = y) -> x != y -> b.
Proof. by move=> imp; apply: contraNT => /imp->. Qed.

Lemma contra_eq_not P x y : (P -> x != y) -> x = y -> ~ P.
Proof. by move=> imp /eqP; apply: contraTnot. Qed.

Lemma contra_neq_not P x y : (P -> x = y) -> x != y -> ~ P.
Proof. by move=> imp;apply: contraNnot => /imp->. Qed.

Lemma contra_eq z1 z2 x1 x2 : (x1 != x2 -> z1 != z2) -> z1 = z2 -> x1 = x2.
Proof. by move=> imp /eqP; apply: contraTeq. Qed.

Lemma contra_neq z1 z2 x1 x2 : (x1 = x2 -> z1 = z2) -> z1 != z2 -> x1 != x2.
Proof. by move=> imp; apply: contraNneq => /imp->. Qed.

Lemma contra_neq_eq z1 z2 x1 x2 : (x1 != x2 -> z1 = z2) -> z1 != z2 -> x1 = x2.
Proof. by move=> imp; apply: contraNeq => /imp->. Qed.

Lemma contra_eq_neq z1 z2 x1 x2 : (z1 = z2 -> x1 != x2) -> x1 = x2 -> z1 != z2.
Proof. by move=> imp; apply: contra_eqN => /eqP /imp. Qed.

Lemma memPn A x : reflect {in A, forall y, y != x} (x \notin A).
Proof.
apply: (iffP idP) => [notDx y | notDx]; first by apply: contraTneq => ->.
exact: contraL (notDx x) _.
Qed.

Lemma memPnC A x : reflect {in A, forall y, x != y} (x \notin A).
Proof. by apply: (iffP (memPn A x)) => A'x y /A'x; rewrite eq_sym. Qed.

Lemma ifN_eq R x y vT vF : x != y -> (if x == y then vT else vF) = vF :> R.
Proof. exact: ifN. Qed.

Lemma ifN_eqC R x y vT vF : x != y -> (if y == x then vT else vF) = vF :> R.
Proof. by rewrite eq_sym; apply: ifN. Qed.

End Contrapositives.

Arguments memPn {T1 A x}.
Arguments memPnC {T1 A x}.

Theorem eq_irrelevance (T : eqType) x y : forall e1 e2 : x = y :> T, e1 = e2.
Proof.
pose proj z e := if x =P z is ReflectT e0 then e0 else e.
suff: injective (proj y) by rewrite /proj => injp e e'; apply: injp; case: eqP.
pose join (e : x = _) := etrans (esym e).
apply: can_inj (join x y (proj x (erefl x))) _.
by case: y /; case: _ / (proj x _).
Qed.

Corollary eq_axiomK (T : eqType) (x : T) : all_equal_to (erefl x).
Proof. by move=> eq_x_x; apply: eq_irrelevance. Qed.

(* We use the module system to circumvent a silly limitation that  *)
(* forbids using the same constant to coerce to different targets. *)
Module Type EqTypePredSig.
Parameter sort : eqType -> predArgType.
End EqTypePredSig.
Module MakeEqTypePred (eqmod : EqTypePredSig).
Coercion eqmod.sort : eqType >-> predArgType.
End MakeEqTypePred.
Module Export EqTypePred := MakeEqTypePred eqtype.Equality.

Lemma unit_eqP : Equality.axiom (fun _ _ : unit => true).
Proof. by do 2!case; left. Qed.

HB.instance Definition _ := hasDecEq.Build unit unit_eqP.

(* Comparison for booleans. *)

(* This is extensionally equal, but not convertible to Bool.eqb. *)
Definition eqb b := addb (~~ b).

Lemma eqbP : Equality.axiom eqb.
Proof. by do 2!case; constructor. Qed.

HB.instance Definition _ := hasDecEq.Build bool eqbP.

Lemma eqbE : eqb = eq_op. Proof. by []. Qed.

Lemma bool_irrelevance (b : bool) (p1 p2 : b) : p1 = p2.
Proof. exact: eq_irrelevance. Qed.

Lemma negb_add b1 b2 : ~~ (b1 (+) b2) = (b1 == b2).
Proof. by rewrite -addNb. Qed.

Lemma negb_eqb b1 b2 : (b1 != b2) = b1 (+) b2.
Proof. by rewrite -addNb negbK. Qed.

Lemma eqb_id b : (b == true) = b.
Proof. by case: b. Qed.

Lemma eqbF_neg b : (b == false) = ~~ b.
Proof. by case: b. Qed.

Lemma eqb_negLR b1 b2 : (~~ b1 == b2) = (b1 == ~~ b2).
Proof. by case: b1; case: b2. Qed.

(* Equality-based predicates.       *)

Notation xpred1 := (fun a1 x => x == a1).
Notation xpred2 := (fun a1 a2 x => (x == a1) || (x == a2)).
Notation xpred3 := (fun a1 a2 a3 x => [|| x == a1, x == a2 | x == a3]).
Notation xpred4 :=
  (fun a1 a2 a3 a4 x => [|| x == a1, x == a2, x == a3 | x == a4]).
Notation xpredU1 := (fun a1 (p : pred _) x => (x == a1) || p x).
Notation xpredC1 := (fun a1 x => x != a1).
Notation xpredD1 := (fun (p : pred _) a1 x => (x != a1) && p x).

Section EqPred.

Variable T : eqType.

Definition pred1 (a1 : T) := SimplPred (xpred1 a1).
Definition pred2 (a1 a2 : T) := SimplPred (xpred2 a1 a2).
Definition pred3 (a1 a2 a3 : T) := SimplPred (xpred3 a1 a2 a3).
Definition pred4 (a1 a2 a3 a4 : T) := SimplPred (xpred4 a1 a2 a3 a4).
Definition predU1 (a1 : T) p := SimplPred (xpredU1 a1 p).
Definition predC1 (a1 : T) := SimplPred (xpredC1 a1).
Definition predD1 p (a1 : T) := SimplPred (xpredD1 p a1).

Lemma pred1E : pred1 =2 eq_op. Proof. by move=> x y; apply: eq_sym. Qed.

Variables (T2 : eqType) (x y : T) (z u : T2) (b : bool).

Lemma predU1P : reflect (x = y \/ b) ((x == y) || b).
Proof. by apply: (iffP orP); do [case=> [/eqP|]; [left | right]]. Qed.

Lemma pred2P : reflect (x = y \/ z = u) ((x == y) || (z == u)).
Proof. by apply: (iffP orP); do [case=> /eqP; [left | right]]. Qed.

Lemma predD1P : reflect (x <> y /\ b) ((x != y) && b).
Proof. by apply: (iffP andP)=> [] [] // /eqP. Qed.

Lemma predU1l : x = y -> (x == y) || b.
Proof. by move->; rewrite eqxx. Qed.

Lemma predU1r : b -> (x == y) || b.
Proof. by move->; rewrite orbT. Qed.

End EqPred.

Arguments predU1P {T x y b}.
Arguments pred2P {T T2 x y z u}.
Arguments predD1P {T x y b}.
Prenex Implicits pred1 pred2 pred3 pred4 predU1 predC1 predD1.

Notation "[ 'predU1' x & A ]" := (predU1 x [in A])
  (at level 0, format "[ 'predU1'  x  &  A ]") : function_scope.
Notation "[ 'predD1' A & x ]" := (predD1 [in A] x)
  (at level 0, format "[ 'predD1'  A  &  x ]") : function_scope.

(* Lemmas for reflected equality and functions.   *)

Section EqFun.

Section Exo.

Variables (aT rT : eqType) (D : pred aT) (f : aT -> rT) (g : rT -> aT).

Lemma inj_eq : injective f -> forall x y, (f x == f y) = (x == y).
Proof. by move=> inj_f x y; apply/eqP/eqP=> [|-> //]; apply: inj_f. Qed.

Lemma can_eq : cancel f g -> forall x y, (f x == f y) = (x == y).
Proof. by move/can_inj; apply: inj_eq. Qed.

Lemma bij_eq : bijective f -> forall x y, (f x == f y) = (x == y).
Proof. by move/bij_inj; apply: inj_eq. Qed.

Lemma can2_eq : cancel f g -> cancel g f -> forall x y, (f x == y) = (x == g y).
Proof. by move=> fK gK x y; rewrite -[y in LHS]gK; apply: can_eq. Qed.

Lemma inj_in_eq :
  {in D &, injective f} -> {in D &, forall x y, (f x == f y) = (x == y)}.
Proof. by move=> inj_f x y Dx Dy; apply/eqP/eqP=> [|-> //]; apply: inj_f. Qed.

Lemma can_in_eq :
  {in D, cancel f g} -> {in D &, forall x y, (f x == f y) = (x == y)}.
Proof. by move/can_in_inj; apply: inj_in_eq. Qed.

End Exo.

Section Endo.

Variable T : eqType.

Definition frel f := [rel x y : T | f x == y].

Lemma inv_eq f : involutive f -> forall x y : T, (f x == y) = (x == f y).
Proof. by move=> fK; apply: can2_eq. Qed.

Lemma eq_frel f f' : f =1 f' -> frel f =2 frel f'.
Proof. by move=> eq_f x y; rewrite /= eq_f. Qed.

End Endo.

Variable aT : Type.

(* The invariant of a function f wrt a projection k is the pred of points  *)
(* that have the same projection as their image.                           *)

Definition invariant (rT : eqType) f (k : aT -> rT) :=
  [pred x | k (f x) == k x].

Variables (rT1 rT2 : eqType) (f : aT -> aT) (h : rT1 -> rT2) (k : aT -> rT1).

Lemma invariant_comp : subpred (invariant f k) (invariant f (h \o k)).
Proof. by move=> x eq_kfx; rewrite /= (eqP eq_kfx). Qed.

Lemma invariant_inj : injective h -> invariant f (h \o k) =1 invariant f k.
Proof. by move=> inj_h x; apply: (inj_eq inj_h). Qed.

End EqFun.

Prenex Implicits frel.

(* The coercion to rel must be explicit for derived Notations to unparse. *)
Notation coerced_frel f := (rel_of_simpl (frel f)) (only parsing).

Section FunWith.

Variables (aT : eqType) (rT : Type).

Variant fun_delta : Type := FunDelta of aT & rT.

Definition fwith x y (f : aT -> rT) := [fun z => if z == x then y else f z].

Definition app_fdelta df f z :=
  let: FunDelta x y := df in if z == x then y else f z.

End FunWith.

Prenex Implicits fwith.

Notation "x |-> y" := (FunDelta x y)
  (at level 190, no associativity,
   format "'[hv' x '/ '  |->  y ']'") : fun_delta_scope.

Delimit Scope fun_delta_scope with FUN_DELTA.
Arguments app_fdelta {aT rT%type} df%FUN_DELTA f z.

Notation "[ 'fun' z : T => F 'with' d1 , .. , dn ]" :=
  (SimplFunDelta (fun z : T =>
     app_fdelta d1%FUN_DELTA .. (app_fdelta dn%FUN_DELTA  (fun _ => F)) ..))
  (at level 0, z name, only parsing) : function_scope.

Notation "[ 'fun' z => F 'with' d1 , .. , dn ]" :=
  (SimplFunDelta (fun z =>
     app_fdelta d1%FUN_DELTA .. (app_fdelta dn%FUN_DELTA (fun _ => F)) ..))
  (at level 0, z name, format
   "'[hv' [ '[' 'fun'  z  => '/ '  F ']' '/'  'with'  '[' d1 , '/'  .. , '/'  dn ']' ] ']'"
   ) : function_scope.

Notation "[ 'eta' f 'with' d1 , .. , dn ]" :=
  (SimplFunDelta (fun _ =>
     app_fdelta d1%FUN_DELTA .. (app_fdelta dn%FUN_DELTA f) ..))
  (at level 0, format
  "'[hv' [ '[' 'eta' '/ '  f ']' '/'  'with'  '[' d1 , '/'  .. , '/'  dn ']' ] ']'"
  ) : function_scope.

Section DFunWith.
Variables (I : eqType) (T : I -> Type) (f : forall i, T i).

Definition dfwith i (x : T i) (j : I) : T j :=
  if (i =P j) is ReflectT ij then ecast j (T j) ij x else f j.

Lemma dfwith_in i x : dfwith x i = x.
Proof. by rewrite /dfwith; case: eqP => // ii; rewrite eq_axiomK. Qed.

Lemma dfwith_out i (x : T i) j : i != j -> dfwith x j = f j.
Proof. by rewrite /dfwith; case: eqP. Qed.

Variant dfwith_spec i (x : T i) : forall j, T j -> Type:=
  | DFunWithIn : dfwith_spec x x
  | DFunWithOut j : i != j -> dfwith_spec x (f j).

Lemma dfwithP i (x : T i) (j : I) : dfwith_spec x (dfwith x j).
Proof.
by case: (eqVneq i j) => [<-|nij];
   [rewrite dfwith_in|rewrite dfwith_out//]; constructor.
Qed.

End DFunWith.
Arguments dfwith {I T} f [i] x.

(* Various EqType constructions.                                         *)

Section ComparableType.

Variable T : Type.

Definition comparable := forall x y : T, decidable (x = y).

Hypothesis compare_T : comparable.

Definition compareb x y : bool := compare_T x y.

Lemma compareP : Equality.axiom compareb.
Proof. by move=> x y; apply: sumboolP. Qed.

Definition comparableMixin := hasDecEq.Build T compareP.

End ComparableType.

Definition eq_comparable (T : eqType) : comparable T :=
  fun x y => decP (x =P y).

#[key="sub_sort"]
HB.mixin Record isSub (T : Type) (P : pred T) (sub_sort : Type) := {
  val_subdef : sub_sort -> T;
  Sub : forall x, P x -> sub_sort;
  Sub_rect : forall K (_ : forall x Px, K (@Sub x Px)) u, K u;
  SubK_subproof : forall x Px, val_subdef (@Sub x Px) = x
}.

#[short(type="subType")]
HB.structure Definition SubType (T : Type) (P : pred T) := { S of isSub T P S }.

Notation val := (isSub.val_subdef (SubType.on _)).
Notation "\val" := (isSub.val_subdef (SubType.on _)) (only parsing).
Notation "\val" := (isSub.val_subdef _) (only printing).

#[short(type="subEqType")]
HB.structure Definition SubEquality T (P : pred T) :=
  { sT of Equality sT & isSub T P sT}.

Section SubType.

Variables (T : Type) (P : pred T).

(* Generic proof that the second property holds by conversion.                *)
(* The vrefl_rect alias is used to flag generic proofs of the first property. *)
Lemma vrefl : forall x, P x -> x = x. Proof. by []. Qed.
Definition vrefl_rect := vrefl.

Section Theory.

Variable sT : subType P.

Local Notation val := (isSub.val_subdef (SubType.on sT)).
Local Notation Sub := (@Sub _ _ sT).

Lemma SubK x Px : val (@Sub x Px) = x. Proof. exact: SubK_subproof. Qed.

Variant Sub_spec : sT -> Type := subSpec x Px : Sub_spec (Sub x Px).

Lemma SubP u : Sub_spec u.
Proof. by elim/(@Sub_rect _ _ sT) : u. Qed.
(* BUG in elim? sT could be inferred from u *)

Definition insub x := if idP is ReflectT Px then Some (Sub x Px) else None.

Definition insubd u0 x := odflt u0 (insub x).

Variant insub_spec x : option sT -> Type :=
  | InsubSome u of P x & val u = x : insub_spec x (Some u)
  | InsubNone   of ~~ P x          : insub_spec x None.

Lemma insubP x : insub_spec x (insub x).
Proof.
by rewrite /insub; case: {-}_ / idP; [left; rewrite ?SubK | right; apply/negP].
Qed.

Lemma insubT x Px : insub x = Some (Sub x Px).
Proof.
do [case: insubP => [/SubP[y Py] _ <- | /negP// ]; rewrite SubK]  in Px *.
by rewrite (bool_irrelevance Px Py).
Qed.

Lemma insubF x : P x = false -> insub x = None.
Proof. by move/idP; case: insubP. Qed.

Lemma insubN x : ~~ P x -> insub x = None.
Proof. by move/negPf/insubF. Qed.

Lemma isSome_insub : ([eta insub] : pred T) =1 P.
Proof. by apply: fsym => x; case: insubP => // /negPf. Qed.

Lemma insubK : ocancel insub val.
Proof. by move=> x; case: insubP. Qed.

Lemma valP u : P (val u).
Proof. by case/SubP: u => x Px; rewrite SubK. Qed.

Lemma valK : pcancel val insub.
Proof. by case/SubP=> x Px; rewrite SubK; apply: insubT. Qed.

Lemma val_inj : injective val.
Proof. exact: pcan_inj valK. Qed.

Lemma valKd u0 : cancel val (insubd u0).
Proof. by move=> u; rewrite /insubd valK. Qed.

Lemma val_insubd u0 x : val (insubd u0 x) = if P x then x else val u0.
Proof. by rewrite /insubd; case: insubP => [u -> | /negPf->]. Qed.

Lemma insubdK u0 : {in P, cancel (insubd u0) val}.
Proof. by move=> x Px; rewrite val_insubd [P x]Px. Qed.

Let insub_eq_aux x isPx : P x = isPx -> option sT :=
  if isPx as b return _ = b -> _ then fun Px => Some (Sub x Px) else fun=> None.
Definition insub_eq x := insub_eq_aux (erefl (P x)).

Lemma insub_eqE : insub_eq =1 insub.
Proof.
rewrite /insub_eq => x; set b := P x; rewrite [in LHS]/b in (Db := erefl b) *.
by case: b in Db *; [rewrite insubT | rewrite insubF].
Qed.

End Theory.

End SubType.

(* Arguments val {T P sT} u : rename. *)
Arguments Sub {T P sT} x Px : rename.
Arguments vrefl {T P} x Px.
Arguments vrefl_rect {T P} x Px.
Arguments insub {T P sT} x.
Arguments insubd {T P sT} u0 x.
Arguments insubT [T] P [sT x].
Arguments val_inj {T P sT} [u1 u2] eq_u12 : rename.
Arguments valK {T P sT} u : rename.
Arguments valKd {T P sT} u0 u : rename.
Arguments insubK {T P} sT x.
Arguments insubdK {T P sT} u0 [x] Px.

Local Notation inlined_sub_rect :=
  (fun K K_S u => let (x, Px) as u return K u := u in K_S x Px).

Local Notation inlined_new_rect :=
  (fun K K_S u => let (x) as u return K u := u in K_S x).

Reserved Notation "[ 'isSub' 'for' v ]"
  (at level 0, format "[ 'isSub'  'for'  v ]").

Notation "[ 'isSub' 'for' v ]" :=
  (@isSub.phant_Build _ _ _ v _ inlined_sub_rect vrefl_rect)
  (only parsing) : form_scope.

Notation "[ 'isSub' 'of'  T  'for' v ]" :=
  (@isSub.phant_Build _ _ T v _ inlined_sub_rect vrefl_rect)
  (only parsing) : form_scope.

Notation "[ 'isSub' 'for' v 'by' rec ]" :=
 (@isSub.phant_Build _ _ _ v _ rec vrefl)
 (at level 0, format "[ 'isSub'  'for'  v  'by'  rec ]") : form_scope.

Notation "[ 'isSub' 'for' v ]" := (@isSub.phant_Build _ _ _ v _ _ _)
  (only printing, at level 0, format "[ 'isSub'  'for'  v ]") : form_scope.

Reserved Notation "[ 'isNew' 'for' v ]"
  (at level 0, format "[ 'isNew'  'for'  v ]").

Definition NewMixin T U v c Urec sk :=
  let Urec' P IH := Urec P (fun x : T => IH x isT : P _) in
  @isSub.phant_Build _ _ U v (fun x _ => c x) Urec' sk.

Notation "[ 'isNew' 'for' v ]" :=
  (@NewMixin _ _ v _ inlined_new_rect vrefl_rect) (only parsing) : form_scope.

Notation "[ 'isNew' 'for' v ]" := (@NewMixin _ _ v _ _ _)
  (only printing, at level 0, format "[ 'isNew'  'for'  v ]") : form_scope.

Notation "[ 'isNew' 'of'  T  'for' v ]" :=
  (@NewMixin _ T v _ inlined_new_rect vrefl_rect) (only parsing) : form_scope.

Definition innew T nT x := @Sub T predT nT x (erefl true).
Arguments innew {T nT}.

Lemma innew_val T nT : cancel val (@innew T nT).
Proof. by move=> u; apply: val_inj; apply: SubK. Qed.

HB.instance Definition _ T (P : pred T) := [isSub of sig P for sval].

(* Shorthand for sigma types over collective predicates. *)
Notation "{ x 'in' A }" := {x | x \in A}
  (at level 0, x at level 99, format  "{ x  'in'  A }") : type_scope.
Notation "{ x 'in' A | P }" := {x | (x \in A) && P}
  (at level 0, x at level 99, format  "{ x  'in'  A  |  P }") : type_scope.

(* Shorthand for the return type of insub. *)
Notation "{ ? x : T | P }" := (option {x : T | is_true P})
  (at level 0, x at level 99, only parsing) : type_scope.
Notation "{ ? x | P }" := {? x : _ | P}
  (at level 0, x at level 99, format  "{ ?  x  |  P }") : type_scope.
Notation "{ ? x 'in' A }" := {? x | x \in A}
  (at level 0, x at level 99, format  "{ ?  x  'in'  A }") : type_scope.
Notation "{ ? x 'in' A | P }" := {? x | (x \in A) && P}
  (at level 0, x at level 99, format  "{ ?  x  'in'  A  |  P }") : type_scope.

(* A variant of injection with default that infers a collective predicate *)
(* from the membership proof for the default value.                       *)
Definition insigd T (A : mem_pred T) x (Ax : in_mem x A) :=
  insubd (exist [eta A] x Ax).

(* There should be a rel definition for the subType equality op, but this *)
(* seems to cause the simpl tactic to diverge on expressions involving == *)
(* on 4+ nested subTypes in a "strict" position (e.g., after ~~).         *)
(* Definition feq f := [rel x y | f x == f y].                            *)

Section TransferType.

Variables (T T' : Type) (f : T -> T').

Definition inj_type of injective f : Type := T.
Definition pcan_type g of pcancel f g : Type := T.
Definition can_type g of cancel f g : Type := T.

End TransferType.

Section TransferEqType.

Variables (T : Type) (eT : eqType) (f : T -> eT).

Lemma inj_eqAxiom : injective f -> Equality.axiom (fun x y => f x == f y).
Proof. by move=> f_inj x y; apply: (iffP eqP) => [|-> //]; apply: f_inj. Qed.

HB.instance Definition _ f_inj := hasDecEq.Build (inj_type f_inj)
  (inj_eqAxiom f_inj).

HB.instance Definition _ g (fK : pcancel f g) := Equality.copy (pcan_type fK)
  (inj_type (pcan_inj fK)).

HB.instance Definition _ g (fK : cancel f g) := Equality.copy (can_type fK)
  (inj_type (can_inj fK)).

Definition deprecated_InjEqMixin f_inj := hasDecEq.Build T (inj_eqAxiom f_inj).
Definition deprecated_PcanEqMixin g (fK : pcancel f g) :=
  deprecated_InjEqMixin (pcan_inj fK).
Definition deprecated_CanEqMixin g (fK : cancel f g) :=
  deprecated_InjEqMixin (can_inj fK).

End TransferEqType.

Definition sub_type T (P : pred T) (sT : subType P) : Type := sT.
HB.instance Definition _ T (P : pred T) (sT : subType P) :=
  SubType.on (sub_type sT).

Section SubEqType.

Variables (T : eqType) (P : pred T) (sT : subType P).

Local Notation ev_ax := (fun T v => @Equality.axiom T (fun x y => v x == v y)).
Lemma val_eqP : ev_ax sT val. Proof. exact: inj_eqAxiom val_inj. Qed.

#[hnf] HB.instance Definition _ := Equality.copy (sub_type sT) (pcan_type valK).

End SubEqType.

Lemma val_eqE (T : eqType) (P : pred T) (sT : subEqType P)
   (u v : sT) : (val u == val v) = (u == v).
Proof. exact/val_eqP/eqP. Qed.

Arguments val_eqP {T P sT x y}.

Notation "[ 'Equality' 'of' T 'by' <: ]" := (Equality.copy T%type (sub_type T%type))
  (at level 0, format "[ 'Equality'  'of'  T  'by'  <: ]") : form_scope.

HB.instance Definition _ := Equality.copy void (pcan_type (of_voidK unit)).
HB.instance Definition _ (T : eqType) (P : pred T) :=
  [Equality of {x | P x} by <:].

Section ProdEqType.

Variable T1 T2 : eqType.

Definition pair_eq : rel (T1 * T2) := fun u v => (u.1 == v.1) && (u.2 == v.2).

Lemma pair_eqP : Equality.axiom pair_eq.
Proof.
move=> [x1 x2] [y1 y2] /=; apply: (iffP andP) => [[]|[<- <-]] //=.
by do 2!move/eqP->.
Qed.

HB.instance Definition _ := hasDecEq.Build (T1 * T2)%type pair_eqP.

Lemma pair_eqE : pair_eq = eq_op :> rel _. Proof. by []. Qed.

Lemma xpair_eqE (x1 y1 : T1) (x2 y2 : T2) :
  ((x1, x2) == (y1, y2)) = ((x1 == y1) && (x2 == y2)).
Proof. by []. Qed.

Lemma pair_eq1 (u v : T1 * T2) : u == v -> u.1 == v.1.
Proof. by case/andP. Qed.

Lemma pair_eq2 (u v : T1 * T2) : u == v -> u.2 == v.2.
Proof. by case/andP. Qed.

End ProdEqType.

Arguments pair_eq {T1 T2} u v /.
Arguments pair_eqP {T1 T2}.

Definition predX T1 T2 (p1 : pred T1) (p2 : pred T2) :=
  [pred z | p1 z.1 & p2 z.2].

Notation "[ 'predX' A1 & A2 ]" := (predX [in A1] [in A2])
  (at level 0, format "[ 'predX'  A1  &  A2 ]") : function_scope.

Section OptionEqType.

Variable T : eqType.

Definition opt_eq (u v : option T) : bool :=
  oapp (fun x => oapp (eq_op x) false v) (~~ v) u.

Lemma opt_eqP : Equality.axiom opt_eq.
Proof.
case=> [x|] [y|] /=; by [constructor | apply: (iffP eqP) => [|[]] ->].
Qed.

HB.instance Definition _ := hasDecEq.Build (option T) opt_eqP.

End OptionEqType.

Arguments opt_eq {T} !u !v.

Section TaggedAs.

Variables (I : eqType) (T_ : I -> Type).
Implicit Types u v : {i : I & T_ i}.

Definition tagged_as u v :=
  if tag u =P tag v is ReflectT eq_uv then
    eq_rect_r T_ (tagged v) eq_uv
  else tagged u.

Lemma tagged_asE u x : tagged_as u (Tagged T_ x) = x.
Proof.
by rewrite /tagged_as /=; case: eqP => // eq_uu; rewrite [eq_uu]eq_axiomK.
Qed.

End TaggedAs.

Section TagEqType.

Variables (I : eqType) (T_ : I -> eqType).
Implicit Types u v : {i : I & T_ i}.

Definition tag_eq u v := (tag u == tag v) && (tagged u == tagged_as u v).

Lemma tag_eqP : Equality.axiom tag_eq.
Proof.
rewrite /tag_eq => [] [i x] [j] /=.
case: eqP => [<-|Hij] y; last by right; case.
by apply: (iffP eqP) => [->|<-]; rewrite tagged_asE.
Qed.

HB.instance Definition _ := hasDecEq.Build {i : I & T_ i} tag_eqP.

Lemma tag_eqE : tag_eq = eq_op. Proof. by []. Qed.

Lemma eq_tag u v : u == v -> tag u = tag v.
Proof. by move/eqP->. Qed.

Lemma eq_Tagged u x :(u == Tagged _ x) = (tagged u == x).
Proof. by rewrite -tag_eqE /tag_eq eqxx tagged_asE. Qed.

End TagEqType.

Arguments tag_eq {I T_} !u !v.
Arguments tag_eqP {I T_ x y}.

Section SumEqType.

Variables T1 T2 : eqType.
Implicit Types u v : T1 + T2.

Definition sum_eq u v :=
  match u, v with
  | inl x, inl y | inr x, inr y => x == y
  | _, _ => false
  end.

Lemma sum_eqP : Equality.axiom sum_eq.
Proof. case=> x [] y /=; by [right | apply: (iffP eqP) => [->|[->]]]. Qed.

HB.instance Definition _ := hasDecEq.Build (T1 + T2)%type sum_eqP.

Lemma sum_eqE : sum_eq = eq_op. Proof. by []. Qed.

End SumEqType.

Arguments sum_eq {T1 T2} !u !v.
Arguments sum_eqP {T1 T2 x y}.

Section MonoHomoTheory.

Variables (aT rT : eqType) (f : aT -> rT).
Variables (aR aR' : rel aT) (rR rR' : rel rT).

Hypothesis aR_refl : reflexive aR.
Hypothesis rR_refl : reflexive rR.
Hypothesis aR'E : forall x y, aR' x y = (x != y) && (aR x y).
Hypothesis rR'E : forall x y, rR' x y = (x != y) && (rR x y).

Let aRE x y : aR x y = (x == y) || (aR' x y).
Proof. by rewrite aR'E; case: eqVneq => //= ->; apply: aR_refl. Qed.
Let rRE x y : rR x y = (x == y) || (rR' x y).
Proof. by rewrite rR'E; case: eqVneq => //= ->; apply: rR_refl. Qed.

Section InDom.
Variable D : pred aT.

Section DifferentDom.
Variable D' : pred aT.

Lemma homoW_in : {in D & D', {homo f : x y / aR' x y >-> rR' x y}} ->
                 {in D & D', {homo f : x y / aR x y >-> rR x y}}.
Proof.
by move=> mf x y xD yD /[!aRE]/orP[/eqP->|/mf]; rewrite rRE ?eqxx// orbC => ->.
Qed.

Lemma inj_homo_in : {in D & D', injective f} ->
  {in D & D', {homo f : x y / aR x y >-> rR x y}} ->
  {in D & D', {homo f : x y / aR' x y >-> rR' x y}}.
Proof.
move=> fI mf x y xD yD /[!(aR'E, rR'E)] /andP[neq_xy xy].
by rewrite mf ?andbT//; apply: contra_neq neq_xy; apply: fI.
Qed.

End DifferentDom.

Hypothesis aR_anti : antisymmetric aR.
Hypothesis rR_anti : antisymmetric rR.

Lemma mono_inj_in : {in D &, {mono f : x y / aR x y >-> rR x y}} ->
                 {in D &, injective f}.
Proof. by move=> mf x y ?? eqf; apply/aR_anti; rewrite -!mf// eqf rR_refl. Qed.

Lemma anti_mono_in : {in D &, {mono f : x y / aR x y >-> rR x y}} ->
                     {in D &, {mono f : x y / aR' x y >-> rR' x y}}.
Proof.
move=> mf x y ??; rewrite rR'E aR'E mf// (@inj_in_eq _ _ D)//.
exact: mono_inj_in.
Qed.

Lemma total_homo_mono_in : total aR ->
    {in D &, {homo f : x y / aR' x y >-> rR' x y}} ->
   {in D &, {mono f : x y / aR x y >-> rR x y}}.
Proof.
move=> aR_tot mf x y xD yD.
have [->|neq_xy] := eqVneq x y; first by rewrite ?eqxx ?aR_refl ?rR_refl.
have [xy|] := (boolP (aR x y)); first by rewrite rRE mf ?orbT// aR'E neq_xy.
have /orP [->//|] := aR_tot x y.
rewrite aRE eq_sym (negPf neq_xy) /= => /mf -/(_ yD xD).
rewrite rR'E => /andP[Nfxfy fyfx] _; apply: contra_neqF Nfxfy => fxfy.
by apply/rR_anti; rewrite fyfx fxfy.
Qed.

End InDom.

Let D := @predT aT.

Lemma homoW : {homo f : x y / aR' x y >-> rR' x y} ->
                 {homo f : x y / aR x y >-> rR x y}.
Proof. by move=> mf ???; apply: (@homoW_in D D) => // ????; apply: mf. Qed.

Lemma inj_homo : injective f ->
  {homo f : x y / aR x y >-> rR x y} ->
  {homo f : x y / aR' x y >-> rR' x y}.
Proof.
by move=> fI mf ???; apply: (@inj_homo_in D D) => //????; [apply: fI|apply: mf].
Qed.

Hypothesis aR_anti : antisymmetric aR.
Hypothesis rR_anti : antisymmetric rR.

Lemma mono_inj : {mono f : x y / aR x y >-> rR x y} -> injective f.
Proof. by move=> mf x y eqf; apply/aR_anti; rewrite -!mf eqf rR_refl. Qed.

Lemma anti_mono : {mono f : x y / aR x y >-> rR x y} ->
                  {mono f : x y / aR' x y >-> rR' x y}.
Proof. by move=> mf x y; rewrite rR'E aR'E mf inj_eq //; apply: mono_inj. Qed.

Lemma total_homo_mono : total aR ->
    {homo f : x y / aR' x y >-> rR' x y} ->
   {mono f : x y / aR x y >-> rR x y}.
Proof.
move=> /(@total_homo_mono_in D rR_anti) hmf hf => x y.
by apply: hmf => // ?? _ _; apply: hf.
Qed.

End MonoHomoTheory.

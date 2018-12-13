(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
(* -*- coding : utf-8 -*- *)

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrfun ssrbool eqtype ssrnat choice seq fintype.

(*****************************************************************************)
(* Provided a base type T, this files defines an interface for quotients Q   *)
(* of the type T with explicit functions for canonical surjection (\pi       *)
(* : T -> Q) and for choosing a representative (repr : Q -> T).  It then     *)
(* provide a helper to quotient T by a decidable equivalence relation (e     *)
(* : rel T) if T is a choiceType (or encodable as a choiceType modulo e).    *)
(*                                                                           *)
(* See "Pragamatic Quotient Types in Coq", proceedings of ITP2013,           *)
(* by Cyril Cohen.                                                           *)
(*                                                                           *)
(* *** Generic Quotienting ***                                               *)
(*   QuotClass (reprK : cancel repr pi) == builds the quotient which         *)
(*              canonical surjection function is pi and which                *)
(*              representative selection function is repr.                   *)
(*   QuotType Q class == packs the quotClass class to build a quotType       *)
(*                       You may declare such elements as Canonical          *)
(*            \pi_Q x == the class in Q of the element x of T                *)
(*              \pi x == the class of x where Q is inferred from the context *)
(*             repr c == canonical representative in T of the class c        *)
(*    [quotType of Q] == clone of the canonical quotType structure of Q on T *)
(*     x = y %[mod Q] := \pi_Q x = \pi_Q y                                   *)
(*                    <-> x and y are equal modulo Q                         *)
(*    x <> y %[mod Q] := \pi_Q x <> \pi_Q y                                  *)
(*    x == y %[mod Q] := \pi_Q x == \pi_Q y                                  *)
(*    x != y %[mod Q] := \pi_Q x != \pi_Q y                                  *)
(*                                                                           *)
(* The quotient_scope is delimited by %qT                                    *)
(* The most useful lemmas are piE and reprK                                  *)
(*                                                                           *)
(* *** Morphisms ***                                                         *)
(* One may declare existing functions and predicates as liftings of some     *)
(* morphisms for a quotient.                                                 *)
(*    PiMorph1 pi_f == where pi_f : {morph \pi : x / f x >-> fq x}           *)
(*                     declares fq : Q -> Q as the lifting of f : T -> T     *)
(*    PiMorph2 pi_g == idem with pi_g : {morph \pi : x y / g x y >-> gq x y} *)
(*     PiMono1 pi_p == idem with pi_p : {mono \pi : x / p x >-> pq x}        *)
(*     PiMono2 pi_r == idem with pi_r : {morph \pi : x y / r x y >-> rq x y} *)
(*   PiMorph11 pi_f == idem with pi_f : {morph \pi : x / f x >-> fq x}       *)
(*                     where fq : Q -> Q' and f : T -> T'.                   *)
(*       PiMorph eq == Most general declaration of compatibility,            *)
(*                     /!\ use with caution /!\                              *)
(* One can use the following helpers to build the liftings which may or      *)
(* may not satisfy the above properties (but if they do not, it is           *)
(* probably not a good idea to define them):                                 *)
(*       lift_op1 Q f := lifts f : T -> T                                    *)
(*       lift_op2 Q g := lifts g : T -> T -> T                               *)
(*      lift_fun1 Q p := lifts p : T -> R                                    *)
(*      lift_fun2 Q r := lifts r : T -> T -> R                               *)
(*   lift_op11 Q Q' f := lifts f : T -> T'                                   *)
(* There is also the special case of constants and embedding functions       *)
(* that one may define and declare as compatible with Q using:               *)
(*    lift_cst Q x := lifts x : T to Q                                       *)
(*       PiConst c := declare the result c of the previous construction as   *)
(*                    compatible with Q                                      *)
(*  lift_embed Q e := lifts e : R -> T to R -> Q                             *)
(*       PiEmbed f := declare the result f of the previous construction as   *)
(*                    compatible with Q                                      *)
(*                                                                           *)
(* *** Quotients that have an eqType structure ***                           *)
(* Having a canonical (eqQuotType e) structure enables piE to replace terms  *)
(* of the form (x == y) by terms of the form (e x' y') if x and y are        *)
(* canonical surjections of some x' and y'.                                  *)
(*    EqQuotType e Q m == builds an (eqQuotType e) structure on Q from the   *)
(*                        morphism property m                                *)
(*                        where m : {mono \pi : x y / e x y >-> x == y}      *)
(*   [eqQuotType of Q] == clones the canonical eqQuotType structure of Q     *)
(*                                                                           *)
(* *** Equivalence and quotient by an equivalence ***                        *)
(*  EquivRel r er es et == builds an equiv_rel structure based on the        *)
(*                         reflexivity, symmetry and transitivity property   *)
(*                         of a boolean relation.                            *)
(*          {eq_quot e} == builds the quotType of T by equiv                 *)
(*                         where e : rel T is an equiv_rel                   *)
(*                         and T is a choiceType or a (choiceTypeMod e)      *)
(*                         it is canonically an eqType, a choiceType,        *)
(*                         a quotType and an eqQuotType.                     *)
(*    x = y %[mod_eq e] := x = y %[mod {eq_quot e}]                          *)
(*                      <-> x and y are equal modulo e                       *)
(*    ...                                                                    *)
(*****************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "\pi_ Q" (at level 0, format "\pi_ Q").
Reserved Notation "\pi" (at level 0, format "\pi").
Reserved Notation "{pi_ Q a }"
         (at level 0, Q at next level, format "{pi_ Q  a }").
Reserved Notation "{pi a }" (at level 0, format "{pi  a }").
Reserved Notation "x == y %[mod_eq e ]" (at level 70, y at next level,
  no associativity,   format "'[hv ' x '/'  ==  y '/'  %[mod_eq  e ] ']'").
Reserved Notation "x = y %[mod_eq e ]" (at level 70, y at next level,
  no associativity,   format "'[hv ' x '/'  =  y '/'  %[mod_eq  e ] ']'").
Reserved Notation "x != y %[mod_eq e ]" (at level 70, y at next level,
  no associativity,   format "'[hv ' x '/'  !=  y '/'  %[mod_eq  e ] ']'").
Reserved Notation "x <> y %[mod_eq e ]" (at level 70, y at next level,
  no associativity,   format "'[hv ' x '/'  <>  y '/'  %[mod_eq  e ] ']'").
Reserved Notation "{eq_quot e }" (at level 0, e at level 0,
  format "{eq_quot  e }", only parsing).

Delimit Scope quotient_scope with qT.
Local Open Scope quotient_scope.

(*****************************************)
(* Definition of the quotient interface. *)
(*****************************************)

Section QuotientDef.

Variable T : Type.

Record quot_mixin_of qT := QuotClass {
  quot_repr : qT -> T;
  quot_pi : T -> qT;
  _ : cancel quot_repr quot_pi
}.

Notation quot_class_of := quot_mixin_of.

Record quotType := QuotTypePack {
  quot_sort :> Type;
  quot_class : quot_class_of quot_sort
}.

Variable qT : quotType.
Definition pi_phant of phant qT := quot_pi (quot_class qT).
Local Notation "\pi" := (pi_phant (Phant qT)).
Definition repr_of := quot_repr (quot_class qT).

Lemma repr_ofK : cancel repr_of \pi.
Proof. by rewrite /pi_phant /repr_of /=; case: qT=> [? []]. Qed.

Definition QuotType_clone (Q : Type) qT cT 
  of phant_id (quot_class qT) cT := @QuotTypePack Q cT.

End QuotientDef.

Arguments repr_ofK {T qT}.

(****************************)
(* Protecting some symbols. *)
(****************************)

Module Type PiSig.
Parameter f : forall (T : Type) (qT : quotType T), phant qT -> T -> qT.
Axiom E : f = pi_phant.
End PiSig.

Module Pi : PiSig.
Definition f := pi_phant.
Definition E := erefl f.
End Pi.

Module MPi : PiSig.
Definition f := pi_phant.
Definition E := erefl f.
End MPi.

Module Type ReprSig.
Parameter f : forall (T : Type) (qT : quotType T), qT -> T.
Axiom E : f = repr_of.
End ReprSig.

Module Repr : ReprSig.
Definition f := repr_of.
Definition E := erefl f.
End Repr.

(*******************)
(* Fancy Notations *)
(*******************)

Notation repr := Repr.f.
Notation "\pi_ Q" := (@Pi.f _ _ (Phant Q)) : quotient_scope.
Notation "\pi" := (@Pi.f _ _ (Phant _))  (only parsing) : quotient_scope.
Notation "x == y %[mod Q ]" := (\pi_Q x == \pi_Q y) : quotient_scope.
Notation "x = y %[mod Q ]" := (\pi_Q x = \pi_Q y) : quotient_scope.
Notation "x != y %[mod Q ]" := (\pi_Q x != \pi_Q y) : quotient_scope.
Notation "x <> y %[mod Q ]" := (\pi_Q x <> \pi_Q y) : quotient_scope.

Local Notation "\mpi" := (@MPi.f _ _ (Phant _)).
Canonical mpi_unlock := Unlockable MPi.E.
Canonical pi_unlock := Unlockable Pi.E.
Canonical repr_unlock := Unlockable Repr.E.

Notation quot_class_of := quot_mixin_of.
Notation QuotType Q m := (@QuotTypePack _ Q m).
Notation "[ 'quotType' 'of' Q ]" := (@QuotType_clone _ Q _ _ id)
 (at level 0, format "[ 'quotType'  'of'  Q ]") : form_scope.

Arguments repr {T qT} x.

(************************)
(* Exporting the theory *)
(************************)

Section QuotTypeTheory.

Variable T : Type.
Variable qT : quotType T.

Lemma reprK : cancel repr \pi_qT.
Proof. by move=> x; rewrite !unlock repr_ofK. Qed.

Variant pi_spec (x : T) : T -> Type :=
  PiSpec y of x = y %[mod qT] : pi_spec x y.

Lemma piP (x : T) : pi_spec x (repr (\pi_qT x)).
Proof. by constructor; rewrite reprK. Qed.

Lemma mpiE : \mpi =1 \pi_qT.
Proof. by move=> x; rewrite !unlock. Qed.

Lemma quotW P : (forall y : T, P (\pi_qT y)) -> forall x : qT, P x.
Proof. by move=> Py x; rewrite -[x]reprK; apply: Py. Qed.

Lemma quotP P : (forall y : T, repr (\pi_qT y) = y -> P (\pi_qT y))
  -> forall x : qT, P x.
Proof. by move=> Py x; rewrite -[x]reprK; apply: Py; rewrite reprK. Qed.

End QuotTypeTheory.

Arguments reprK {T qT} x.

(*******************)
(* About morphisms *)
(*******************)

(* This was pi_morph T (x : T) := PiMorph { pi_op : T; _ : x = pi_op }. *)
Structure equal_to T (x : T) := EqualTo {
   equal_val : T;
   _         : x = equal_val
}.
Lemma equal_toE (T : Type) (x : T) (m : equal_to x) : equal_val m = x.
Proof. by case: m. Qed.

Notation piE := (@equal_toE _ _).

Canonical equal_to_pi T (qT : quotType T) (x : T) :=
  @EqualTo _ (\pi_qT x) (\pi x) (erefl _).

Arguments EqualTo {T x equal_val}.

Section Morphism.

Variables T U : Type.
Variable (qT : quotType T).
Variable (qU : quotType U).

Variable (f : T -> T) (g : T -> T -> T) (p : T -> U) (r : T -> T -> U).
Variable (fq : qT -> qT) (gq : qT -> qT -> qT) (pq : qT -> U) (rq : qT -> qT -> U).
Variable (h : T -> U) (hq : qT -> qU).
Hypothesis pi_f : {morph \pi : x / f x >-> fq x}.
Hypothesis pi_g : {morph \pi : x y / g x y >-> gq x y}.
Hypothesis pi_p : {mono \pi : x / p x >-> pq x}.
Hypothesis pi_r : {mono \pi : x y / r x y >-> rq x y}.
Hypothesis pi_h : forall (x : T), \pi_qU (h x) = hq (\pi_qT x).
Variables (a b : T) (x : equal_to (\pi_qT a)) (y : equal_to (\pi_qT b)).

(* Internal Lemmmas : do not use directly *)
Lemma pi_morph1 : \pi (f a) = fq (equal_val x). Proof. by rewrite !piE. Qed.
Lemma pi_morph2 : \pi (g a b) = gq (equal_val x) (equal_val y). Proof. by rewrite !piE. Qed.
Lemma pi_mono1 : p a = pq (equal_val x). Proof. by rewrite !piE. Qed.
Lemma pi_mono2 : r a b = rq (equal_val x) (equal_val y). Proof. by rewrite !piE. Qed.
Lemma pi_morph11 : \pi (h a) = hq (equal_val x). Proof. by rewrite !piE. Qed.

End Morphism.

Arguments pi_morph1 {T qT f fq}.
Arguments pi_morph2 {T qT g gq}.
Arguments pi_mono1 {T U qT p pq}.
Arguments pi_mono2 {T U qT r rq}.
Arguments pi_morph11 {T U qT qU h hq}.

Notation "{pi_ Q a }" := (equal_to (\pi_Q a)) : quotient_scope.
Notation "{pi a }" := (equal_to (\pi a)) : quotient_scope.

(* Declaration of morphisms *)
Notation PiMorph pi_x := (EqualTo pi_x).
Notation PiMorph1 pi_f :=
  (fun a (x : {pi a}) => EqualTo (pi_morph1 pi_f a x)).
Notation PiMorph2 pi_g :=
  (fun a b (x : {pi a}) (y : {pi b}) => EqualTo (pi_morph2 pi_g a b x y)).
Notation PiMono1 pi_p :=
  (fun a (x : {pi a}) => EqualTo (pi_mono1 pi_p a x)).
Notation PiMono2 pi_r :=
  (fun a b (x : {pi a}) (y : {pi b}) => EqualTo (pi_mono2 pi_r a b x y)).
Notation PiMorph11 pi_f :=
  (fun a (x : {pi a}) => EqualTo (pi_morph11 pi_f a x)).

(* lifiting helpers *)
Notation lift_op1 Q f := (locked (fun x : Q => \pi_Q (f (repr x)) : Q)).
Notation lift_op2 Q g := 
  (locked (fun x y : Q => \pi_Q (g (repr x) (repr y)) : Q)).
Notation lift_fun1 Q f := (locked (fun x : Q => f (repr x))).
Notation lift_fun2 Q g := (locked (fun x y : Q => g (repr x) (repr y))).
Notation lift_op11 Q Q' f := (locked (fun x : Q => \pi_Q' (f (repr x)) : Q')).

(* constant declaration *)
Notation lift_cst Q x := (locked (\pi_Q x : Q)).
Notation PiConst a := (@EqualTo _ _ a (lock _)).

(* embedding declaration, please don't redefine \pi *)
Notation lift_embed qT e := (locked (fun x => \pi_qT (e x) : qT)).

Lemma eq_lock T T' e : e =1 (@locked (T -> T') (fun x : T => e x)).
Proof. by rewrite -lock. Qed.
Prenex Implicits eq_lock.

Notation PiEmbed e := 
  (fun x => @EqualTo _ _ (e x) (eq_lock (fun _ => \pi _) _)).

(********************)
(* About eqQuotType *)
(********************)

Section EqQuotTypeStructure.

Variable T : Type.
Variable eq_quot_op : rel T.

Definition eq_quot_mixin_of (Q : Type) (qc : quot_class_of T Q)
  (ec : Equality.class_of Q) :=
  {mono \pi_(QuotTypePack qc) : x y /
   eq_quot_op x y >-> @eq_op (Equality.Pack ec) x y}.

Record eq_quot_class_of (Q : Type) : Type := EqQuotClass {
  eq_quot_quot_class :> quot_class_of T Q;
  eq_quot_eq_mixin :> Equality.class_of Q;
  pi_eq_quot_mixin :> eq_quot_mixin_of eq_quot_quot_class eq_quot_eq_mixin
}.

Record eqQuotType : Type := EqQuotTypePack {
  eq_quot_sort :> Type;
  _ : eq_quot_class_of eq_quot_sort;
 
}.

Implicit Type eqT : eqQuotType.

Definition eq_quot_class eqT : eq_quot_class_of eqT :=
  let: EqQuotTypePack _ cT as qT' := eqT return eq_quot_class_of qT' in cT.

Canonical eqQuotType_eqType eqT := EqType eqT (eq_quot_class eqT).
Canonical eqQuotType_quotType eqT := QuotType eqT (eq_quot_class eqT).

Coercion eqQuotType_eqType : eqQuotType >-> eqType.
Coercion eqQuotType_quotType : eqQuotType >-> quotType.

Definition EqQuotType_pack Q :=
  fun (qT : quotType T) (eT : eqType) qc ec 
  of phant_id (quot_class qT) qc & phant_id (Equality.class eT) ec => 
    fun m => EqQuotTypePack (@EqQuotClass Q qc ec m).

Definition EqQuotType_clone (Q : Type) eqT cT 
  of phant_id (eq_quot_class eqT) cT := @EqQuotTypePack Q cT.

Lemma pi_eq_quot eqT : {mono \pi_eqT : x y / eq_quot_op x y >-> x == y}.
Proof. by case: eqT => [] ? []. Qed.

Canonical pi_eq_quot_mono eqT := PiMono2 (pi_eq_quot eqT).

End EqQuotTypeStructure.

Notation EqQuotType e Q m := (@EqQuotType_pack _ e Q _ _ _ _ id id m).
Notation "[ 'eqQuotType' e 'of' Q ]" := (@EqQuotType_clone _ e Q _ _ id)
 (at level 0, format "[ 'eqQuotType'  e  'of'  Q ]") : form_scope.

(**************************************************************************)
(* Even if a quotType is a natural subType, we do not make this subType   *)
(* canonical, to allow the user to define the subtyping he wants. However *)
(* one can:                                                               *)
(* - get the eqMixin and the choiceMixin by subtyping                     *)
(* - get the subType structure and maybe declare it Canonical.            *)
(**************************************************************************)

Module QuotSubType.
Section SubTypeMixin.

Variable T : eqType.
Variable qT : quotType T.

Definition Sub x (px : repr (\pi_qT x) == x) := \pi_qT x.

Lemma qreprK x Px : repr (@Sub x Px) = x.
Proof. by rewrite /Sub (eqP Px). Qed.

Lemma sortPx (x : qT) : repr (\pi_qT (repr x)) == repr x.
Proof. by rewrite !reprK eqxx. Qed.

Lemma sort_Sub (x : qT) : x = Sub (sortPx x).
Proof. by rewrite /Sub reprK. Qed.

Lemma reprP K (PK : forall x Px, K (@Sub x Px)) u : K u.
Proof. by rewrite (sort_Sub u); apply: PK. Qed.

Canonical subType  := SubType _ _ _ reprP qreprK.
Definition eqMixin := Eval hnf in [eqMixin of qT by <:].

Canonical eqType := EqType qT eqMixin.

End SubTypeMixin.

Definition choiceMixin (T : choiceType) (qT : quotType T) :=
  Eval hnf in [choiceMixin of qT by <:].
Canonical choiceType (T : choiceType) (qT : quotType T) :=
  ChoiceType qT (@choiceMixin T qT).

Definition countMixin (T : countType) (qT : quotType T) :=
  Eval hnf in [countMixin of qT by <:].
Canonical countType (T : countType) (qT : quotType T) :=
  CountType qT (@countMixin T qT).

Section finType.
Variables (T : finType) (qT : quotType T).
Canonical subCountType := [subCountType of qT].
Definition finMixin := Eval hnf in [finMixin of qT by <:].
End finType.

End QuotSubType.

Notation "[ 'subType' Q 'of' T 'by' %/ ]" :=
(@SubType T _ Q _ _ (@QuotSubType.reprP _ _) (@QuotSubType.qreprK _ _))
(at level 0, format "[ 'subType'  Q  'of'  T  'by'  %/ ]") : form_scope.

Notation "[ 'eqMixin' 'of' Q 'by' <:%/ ]" := 
  (@QuotSubType.eqMixin _ _: Equality.class_of Q)
  (at level 0, format "[ 'eqMixin'  'of'  Q  'by'  <:%/ ]") : form_scope.

Notation "[ 'choiceMixin' 'of' Q 'by' <:%/ ]" := 
  (@QuotSubType.choiceMixin _ _: Choice.mixin_of Q)
  (at level 0, format "[ 'choiceMixin'  'of'  Q  'by'  <:%/ ]") : form_scope.

Notation "[ 'countMixin' 'of' Q 'by' <:%/ ]" := 
  (@QuotSubType.countMixin _ _: Countable.mixin_of Q)
  (at level 0, format "[ 'countMixin'  'of'  Q  'by'  <:%/ ]") : form_scope.

Notation "[ 'finMixin' 'of' Q 'by' <:%/ ]" := 
  (@QuotSubType.finMixin _ _: Finite.mixin_of Q)
  (at level 0, format "[ 'finMixin'  'of'  Q  'by'  <:%/ ]") : form_scope.

(****************************************************)
(* Definition of a (decidable) equivalence relation *)
(****************************************************)

Section EquivRel.

Variable T : Type.

Lemma left_trans (e : rel T) :
  symmetric e -> transitive e -> left_transitive e.
Proof. by move=> s t ? * ?; apply/idP/idP; apply: t; rewrite // s. Qed.

Lemma right_trans (e : rel T) :
  symmetric e -> transitive e -> right_transitive e.
Proof. by move=> s t ? * x; rewrite ![e x _]s; apply: left_trans. Qed.

Variant equiv_class_of (equiv : rel T) :=
  EquivClass of reflexive equiv & symmetric equiv & transitive equiv.

Record equiv_rel := EquivRelPack {
  equiv :> rel T;
  _ : equiv_class_of equiv
}.

Variable e : equiv_rel.

Definition equiv_class :=
  let: EquivRelPack _ ce as e' := e return equiv_class_of e' in ce.

Definition equiv_pack (r : rel T) ce of phant_id ce equiv_class :=
  @EquivRelPack r ce.

Lemma equiv_refl x : e x x. Proof. by case: e => [] ? []. Qed.
Lemma equiv_sym : symmetric e. Proof. by case: e => [] ? []. Qed.
Lemma equiv_trans : transitive e. Proof. by case: e => [] ? []. Qed.

Lemma eq_op_trans (T' : eqType) : transitive (@eq_op T').
Proof. by move=> x y z; move/eqP->; move/eqP->. Qed.

Lemma equiv_ltrans: left_transitive e.
Proof. by apply: left_trans; [apply: equiv_sym|apply: equiv_trans]. Qed.

Lemma equiv_rtrans: right_transitive e.
Proof. by apply: right_trans; [apply: equiv_sym|apply: equiv_trans]. Qed.

End EquivRel.

Hint Resolve equiv_refl : core.

Notation EquivRel r er es et := (@EquivRelPack _ r (EquivClass er es et)).
Notation "[ 'equiv_rel' 'of' e ]" := (@equiv_pack _ _ e _ id)
 (at level 0, format "[ 'equiv_rel'  'of'  e ]") : form_scope.

(**************************************************)
(* Encoding to another type modulo an equivalence *)
(**************************************************)

Section EncodingModuloRel.

Variables (D E : Type) (ED : E -> D) (DE : D -> E) (e : rel D).

Variant encModRel_class_of (r : rel D) :=
  EncModRelClassPack of (forall x, r x x -> r (ED (DE x)) x) & (r =2 e).

Record encModRel := EncModRelPack {
  enc_mod_rel :> rel D;
  _ : encModRel_class_of enc_mod_rel
}.

Variable r : encModRel.

Definition encModRelClass := 
  let: EncModRelPack _ c as r' := r return encModRel_class_of r' in c.

Definition encModRelP (x : D) : r x x -> r (ED (DE x)) x.
Proof. by case: r => [] ? [] /= he _ /he. Qed.

Definition encModRelE : r =2 e. Proof. by case: r => [] ? []. Qed.

Definition encoded_equiv : rel E := [rel x y | r (ED x) (ED y)].

End EncodingModuloRel.

Notation EncModRelClass m :=
  (EncModRelClassPack (fun x _ => m x) (fun _ _ => erefl _)).
Notation EncModRel r m := (@EncModRelPack _ _ _ _ _ r (EncModRelClass m)).

Section EncodingModuloEquiv.

Variables (D E : Type) (ED : E -> D) (DE : D -> E) (e : equiv_rel D).
Variable (r : encModRel ED DE e).

Lemma enc_mod_rel_is_equiv : equiv_class_of (enc_mod_rel r).
Proof.
split => [x|x y|y x z]; rewrite !encModRelE //; first by rewrite equiv_sym.
by move=> exy /(equiv_trans exy).
Qed.

Definition enc_mod_rel_equiv_rel := EquivRelPack enc_mod_rel_is_equiv.

Definition encModEquivP (x : D) : r (ED (DE x)) x.
Proof. by rewrite encModRelP ?encModRelE. Qed.

Local Notation e' := (encoded_equiv r).

Lemma encoded_equivE : e' =2 [rel x y | e (ED x) (ED y)].
Proof. by move=> x y; rewrite /encoded_equiv /= encModRelE. Qed.
Local Notation e'E := encoded_equivE.

Lemma encoded_equiv_is_equiv : equiv_class_of e'.
Proof.
split => [x|x y|y x z]; rewrite !e'E //=; first by rewrite equiv_sym.
by move=> exy /(equiv_trans exy).
Qed.

Canonical encoded_equiv_equiv_rel := EquivRelPack encoded_equiv_is_equiv.

Lemma encoded_equivP x : e' (DE (ED x)) x.
Proof. by rewrite /encoded_equiv /= encModEquivP. Qed.

End EncodingModuloEquiv.

(**************************************)
(* Quotient by a equivalence relation *)
(**************************************)

Module EquivQuot.
Section EquivQuot.

Variables (D : Type) (C : choiceType) (CD : C -> D) (DC : D -> C).
Variables (eD : equiv_rel D) (encD : encModRel CD DC eD).
Notation eC := (encoded_equiv encD).

Definition canon x := choose (eC x) (x).

Record equivQuotient := EquivQuotient {
  erepr : C;
  _ : (frel canon) erepr erepr
}.

Definition type_of of (phantom (rel _) encD) := equivQuotient.

Lemma canon_id : forall x, (invariant canon canon) x.
Proof.
move=> x /=; rewrite /canon (@eq_choose _ _ (eC x)).
  by rewrite (@choose_id _ (eC x) _ x) ?chooseP ?equiv_refl.
by move=> y; apply: equiv_ltrans; rewrite equiv_sym /= chooseP.
Qed.

Definition pi := locked (fun x => EquivQuotient (canon_id x)).

Lemma ereprK : cancel erepr pi.
Proof.
unlock pi; case=> x hx; move/eqP:(hx)=> hx'.
exact: (@val_inj _ _ [subType for erepr]).
Qed.

Local Notation encDE := (encModRelE encD).
Local Notation encDP := (encModEquivP encD).
Canonical encD_equiv_rel := EquivRelPack (enc_mod_rel_is_equiv encD).

Lemma pi_CD (x y : C) : reflect (pi x = pi y) (eC x y).
Proof.
apply: (iffP idP) => hxy.
  apply: (can_inj ereprK); unlock pi canon => /=.
  rewrite -(@eq_choose _ (eC x) (eC y)); last first.
    by move=> z; rewrite /eC /=; apply: equiv_ltrans.
  by apply: choose_id; rewrite ?equiv_refl //.
rewrite (equiv_trans (chooseP (equiv_refl _ _))) //=.
move: hxy => /(f_equal erepr) /=; unlock pi canon => /= ->.
by rewrite equiv_sym /= chooseP.
Qed.

Lemma pi_DC (x y : D) :
  reflect (pi (DC x) = pi (DC y)) (eD x y).
Proof.
apply: (iffP idP)=> hxy.
  apply/pi_CD; rewrite /eC /=.
  by rewrite (equiv_ltrans (encDP _)) (equiv_rtrans (encDP _)) /= encDE.
rewrite -encDE -(equiv_ltrans (encDP _)) -(equiv_rtrans (encDP _)) /=.
exact/pi_CD.
Qed.

Lemma equivQTP : cancel (CD \o erepr) (pi \o DC).
Proof.
by move=> x; rewrite /= (pi_CD _ (erepr x) _) ?ereprK /eC /= ?encDP.
Qed.

Local Notation qT := (type_of (Phantom (rel D) encD)).
Definition quotClass := QuotClass equivQTP.
Canonical quotType := QuotType qT quotClass.

Lemma eqmodP x y : reflect (x = y %[mod qT]) (eD x y).
Proof. by apply: (iffP (pi_DC _ _)); rewrite !unlock. Qed.

Fact eqMixin : Equality.mixin_of qT. Proof. exact: CanEqMixin ereprK. Qed.
Canonical eqType := EqType qT eqMixin.
Definition choiceMixin := CanChoiceMixin ereprK.
Canonical choiceType := ChoiceType qT choiceMixin.

Lemma eqmodE x y : x == y %[mod qT] = eD x y.
Proof. exact: sameP eqP (@eqmodP _ _). Qed.

Canonical eqQuotType := EqQuotType eD qT eqmodE.

End EquivQuot.
End EquivQuot.

Canonical EquivQuot.quotType.
Canonical EquivQuot.eqType.
Canonical EquivQuot.choiceType.
Canonical EquivQuot.eqQuotType.

Arguments EquivQuot.ereprK {D C CD DC eD encD}.

Notation "{eq_quot e }" :=
(@EquivQuot.type_of _ _ _ _ _ _ (Phantom (rel _) e)) : quotient_scope.
Notation "x == y %[mod_eq r ]" := (x == y %[mod {eq_quot r}]) : quotient_scope.
Notation "x = y %[mod_eq r ]" := (x = y %[mod {eq_quot r}]) : quotient_scope.
Notation "x != y %[mod_eq r ]" := (x != y %[mod {eq_quot r}]) : quotient_scope.
Notation "x <> y %[mod_eq r ]" := (x <> y %[mod {eq_quot r}]) : quotient_scope.

(***********************************************************)
(* If the type is directly a choiceType, no need to encode *)
(***********************************************************)

Section DefaultEncodingModuloRel.

Variables (D : choiceType) (r : rel D).

Definition defaultEncModRelClass :=
  @EncModRelClassPack D D id id r r (fun _ rxx => rxx) (fun _ _ => erefl _).

Canonical defaultEncModRel := EncModRelPack defaultEncModRelClass.

End DefaultEncodingModuloRel.

(***************************************************)
(* Recovering a potential countable type structure *)
(***************************************************)

Section CountEncodingModuloRel.

Variables (D : Type) (C : countType) (CD : C -> D) (DC : D -> C).
Variables (eD : equiv_rel D) (encD : encModRel CD DC eD).
Notation eC := (encoded_equiv encD).

Fact eq_quot_countMixin : Countable.mixin_of {eq_quot encD}.
Proof. exact: CanCountMixin EquivQuot.ereprK. Qed.
Canonical eq_quot_countType := CountType {eq_quot encD} eq_quot_countMixin.

End CountEncodingModuloRel.

Section EquivQuotTheory.

Variables (T : choiceType) (e : equiv_rel T) (Q : eqQuotType e).

Lemma eqmodE x y : x == y %[mod_eq e] = e x y.
Proof. by rewrite pi_eq_quot. Qed.

Lemma eqmodP x y : reflect (x = y %[mod_eq e]) (e x y).
Proof. by rewrite -eqmodE; apply/eqP. Qed.

End EquivQuotTheory.

Prenex Implicits eqmodE eqmodP.

Section EqQuotTheory.

Variables (T : Type) (e : rel T) (Q : eqQuotType e).

Lemma eqquotE x y : x == y %[mod Q] = e x y.
Proof. by rewrite pi_eq_quot. Qed.

Lemma eqquotP x y : reflect (x = y %[mod Q]) (e x y).
Proof. by rewrite -eqquotE; apply/eqP. Qed.

End EqQuotTheory.

Prenex Implicits eqquotE eqquotP.

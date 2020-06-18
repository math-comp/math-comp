(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice.
From mathcomp Require Import seq fintype.

(*****************************************************************************)
(* Provided a base type T, this files defines an interface for quotients Q   *)
(* of the type T with explicit functions for canonical surjection (\pi       *)
(* : T -> Q) and for choosing a representative (repr : Q -> T).  It then     *)
(* provides a helper to quotient T by a decidable equivalence relation (e    *)
(* : rel T) if T is a choiceType (or encodable as a choiceType modulo e).    *)
(*                                                                           *)
(* See "Pragmatic Quotient Types in Coq", proceedings of ITP2013,            *)
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

Declare Scope quotient_scope.

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
Reserved Notation "{eq_quot e }"
  (at level 0, e at level 0, format "{eq_quot  e }").

Delimit Scope quotient_scope with qT.
Local Open Scope quotient_scope.

(*****************************************)
(* Definition of the quotient interface. *)
(*****************************************)

HB.mixin Record IsQuotient T (qT : Type) := {
  repr_of : qT -> T;
  quot_pi_subdef : T -> qT;
  repr_ofK_subproof : cancel repr_of quot_pi_subdef
}.

#[short(type="quotType")]
HB.structure Definition Quotient T := { qT of IsQuotient T qT }.
Arguments repr_of [T qT] : rename.

Section QuotientDef.

Variable T : Type.
Variable qT : quotType T.
Definition pi_phant of phant qT := @quot_pi_subdef _ qT.
Local Notation "\pi" := (pi_phant (Phant qT)).

Lemma repr_ofK : cancel (@repr_of _ _) \pi.
Proof. exact: repr_ofK_subproof. Qed.

End QuotientDef.
Arguments repr_ofK {T qT}.

(****************************)
(* Protecting some symbols. *)
(****************************)

HB.lock Definition pi := pi_phant.
HB.lock Definition mpi := pi_phant.
HB.lock Definition repr := repr_of.

(*******************)
(* Fancy Notations *)
(*******************)

Notation "\pi_ Q" := (@pi _ _ (Phant Q)) : quotient_scope.
Notation "\pi" := (@pi _ _ (Phant _))  (only parsing) : quotient_scope.
Notation "x == y %[mod Q ]" := (\pi_Q x == \pi_Q y) : quotient_scope.
Notation "x = y %[mod Q ]" := (\pi_Q x = \pi_Q y) : quotient_scope.
Notation "x != y %[mod Q ]" := (\pi_Q x != \pi_Q y) : quotient_scope.
Notation "x <> y %[mod Q ]" := (\pi_Q x <> \pi_Q y) : quotient_scope.

Local Notation "\mpi" := (@mpi _ _ (Phant _)).
Canonical mpi_unlock := Unlockable mpi.unlock.
Canonical pi_unlock := Unlockable pi.unlock.
Canonical repr_unlock := Unlockable repr.unlock.

Notation "[ 'quotType' 'of' Q ]" := (Quotient.clone _ Q _)
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

(* Internal Lemmas : do not use directly *)
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

(* lifting helpers *)
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

HB.mixin Record IsEqQuotient T (eq_quot_op : rel T) (Q : Type) of
  IsQuotient T Q & HasDecEq Q := {
  pi_eq_quot : {mono \pi_Q : x y / eq_quot_op x y >-> x == y}
}.

#[short(type="eqQuotType")]
HB.structure Definition EqQuotient T eq_quot_op :=
  {Q of IsEqQuotient T eq_quot_op Q & Quotient T Q & HasDecEq Q}.
(*TODO : Check why there was no warning when we didn't put HasDecEq*)

Canonical pi_eq_quot_mono T eq_quot_op eqT :=
  PiMono2 (@pi_eq_quot T eq_quot_op eqT).

Notation "[ 'eqQuotType' e 'of' Q ]" := (EqQuotient.clone _ e Q _)
 (at level 0, format "[ 'eqQuotType'  e  'of'  Q ]") : form_scope.

(**************************************************************************)
(* Even if a quotType is a natural subType, we do not make this subType   *)
(* canonical, to allow the user to define the subtyping he wants. However *)
(* one can:                                                               *)
(* - get the HasDecEq and the HasChoice by subtyping                      *)
(* - get the subType structure and maybe declare it Canonical.            *)
(**************************************************************************)


Definition quot_type_subdef T (qT : quotType T) of phant qT : Type := qT.
Notation quot_type_of T Q := (@quot_type_subdef T _ (Phant Q)).
Notation quot_type Q := (quot_type_subdef (Phant Q)).
HB.instance Definition _ T (qT : quotType T) :=
  Quotient.copy (quot_type qT) qT.

Module QuotSubType.
Section QuotSubType.
Variable (T : eqType) (qT : quotType T).

Definition Sub x (px : repr (\pi_qT x) == x) := \pi_qT x.

Lemma qreprK x Px : repr (@Sub x Px) = x.
Proof. by rewrite /Sub (eqP Px). Qed.

Lemma sortPx (x : qT) : repr (\pi_qT (repr x)) == repr x.
Proof. by rewrite !reprK eqxx. Qed.

Lemma sort_Sub (x : qT) : x = Sub (sortPx x).
Proof. by rewrite /Sub reprK. Qed.

Lemma reprP K (PK : forall x Px, K (@Sub x Px)) u : K u.
Proof. by rewrite (sort_Sub u); apply: PK. Qed.

#[export]
HB.instance Definition _ := IsSUB.Build _ _ (quot_type qT) reprP qreprK.
#[export]
HB.instance Definition _ := [Equality of quot_type qT by <:].
End QuotSubType.
Module Exports. HB.reexport. End Exports.
End QuotSubType.
Export QuotSubType.Exports.

HB.instance Definition _ (T : choiceType) (qT : quotType T) :=
  [Choice of quot_type qT by <:].

HB.instance Definition _ (T : countType) (qT : quotType T) :=
  [Countable of quot_type qT by <:].

HB.instance Definition _ (T : finType) (qT : quotType T) :=
  [Finite of quot_type qT by <:].

Notation "[ 'SUB' Q 'of' T 'by' %/ ]" :=
  (SUB.copy Q%type (quot_type_of T Q))
  (at level 0, format "[ 'SUB'  Q  'of'  T  'by'  %/ ]") : form_scope.

Notation "[ 'SUB' Q 'by' %/ ]" :=
  (SUB.copy Q%type (quot_type Q))
  (at level 0, format "[ 'SUB'  Q  'by'  %/ ]") : form_scope.

Notation "[ 'Equality' 'of' Q 'by' <:%/ ]" :=
  (Equality.copy Q%type (quot_type Q))
  (at level 0, format "[ 'Equality'  'of'  Q  'by'  <:%/ ]") : form_scope.

Notation "[ 'Choice' 'of' Q 'by' <:%/ ]" := (Choice.copy Q%type (quot_type Q))
  (at level 0, format "[ 'Choice'  'of'  Q  'by'  <:%/ ]") : form_scope.

Notation "[ 'HasChoice' 'of' Q 'by' <:%/ ]" :=
  ([HasChoice of quot_type Q by <:] : HasChoice Q%type)
  (at level 0, format "[ 'HasChoice'  'of'  Q  'by'  <:%/ ]") : form_scope.

Notation "[ 'Countable' 'of' Q 'by' <:%/ ]" := (Countable.copy Q%type (quot_type Q))
  (at level 0, format "[ 'Countable'  'of'  Q  'by'  <:%/ ]") : form_scope.

Notation "[ 'IsCountable' 'of' Q 'by' <:%/ ]" :=
  ([IsCountable of quot_type Q by <:] : IsCountable Q%type)
  (at level 0, format "[ 'IsCountable'  'of'  Q  'by'  <:%/ ]") : form_scope.

Notation "[ 'Finite' 'of' Q 'by' <:%/ ]" := (Finite.copy Q%type (quot_type Q))
  (at level 0, format "[ 'Finite'  'of'  Q  'by'  <:%/ ]") : form_scope.

Notation "[ 'IsFinite' 'of' Q 'by' <:%/ ]" :=
  ([IsFinite of quot_type Q by <:] : IsFinite Q%type)
  (at level 0, format "[ 'IsFinite'  'of'  Q  'by'  <:%/ ]") : form_scope.

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
Proof. by move=> x y z /eqP -> /eqP ->. Qed.

Lemma equiv_ltrans: left_transitive e.
Proof. by apply: left_trans; [apply: equiv_sym|apply: equiv_trans]. Qed.

Lemma equiv_rtrans: right_transitive e.
Proof. by apply: right_trans; [apply: equiv_sym|apply: equiv_trans]. Qed.

End EquivRel.

#[global] Hint Resolve equiv_refl : core.

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
pose T : subType _ := HB.pack equivQuotient [IsSUB for erepr].
by unlock pi; case=> x hx; apply/(@val_inj _ _ T)/eqP.
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
Proof. by move=> x; rewrite /= (pi_CD _ (erepr x) _) ?ereprK /eC /= ?encDP. Qed.

Local Notation qT := (type_of (Phantom (rel D) encD)).
#[export]
HB.instance Definition _ := IsQuotient.Build D qT equivQTP.

Lemma eqmodP x y : reflect (x = y %[mod qT]) (eD x y).
Proof. by apply: (iffP (pi_DC _ _)); rewrite !unlock. Qed.

#[export]
HB.instance Definition _ := Choice.copy qT (can_type ereprK).

Lemma eqmodE x y : x == y %[mod qT] = eD x y.
Proof. exact: sameP eqP (@eqmodP _ _). Qed.

#[export]
HB.instance Definition _ := IsEqQuotient.Build _ eD qT eqmodE.

End EquivQuot.
Module Exports. HB.reexport. End Exports.
End EquivQuot.
Export EquivQuot.Exports.

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

HB.instance Definition _ :=
  Countable.copy {eq_quot encD} (can_type EquivQuot.ereprK).

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

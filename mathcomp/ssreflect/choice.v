(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
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
(*            HasChoice T == type of choice mixins; the exact contents is     *)
(*                        documented below in the Choice submodule.           *)
(*           ChoiceType T m == the packed choiceType class for T and mixin m. *)
(* [choiceType of T for cT] == clone for T of the choiceType cT.              *)
(*        [choiceType of T] == clone for T of the choiceType inferred for T.  *)
(*            CountType T m == the packed countType class for T and mixin m.  *)
(*  [countType of T for cT] == clone for T of the countType cT.               *)
(*        [count Type of T] == clone for T of the countType inferred for T.   *)
(* [HasChoice of T by <:] == Choice mixin for T when T has a subType p        *)
(*                        structure with p : pred cT and cT has a Choice      *)
(*                        structure; the corresponding structure is Canonical.*)
(*  [IsCountable of T by <:] == Count mixin for a subType T of a countType.    *)
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
Arguments decode_rec : simpl nomatch.

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
  | Node n f => inl _ n.+1 :: rcons (flatten (map encode f)) (inl _ 0)
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

HB.instance Definition _ (T : eqType) := Equality.copy (GenTree.tree T)
  (pcan_type (GenTree.codeK T)).

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

HB.mixin Record HasChoice T := Mixin {
  find_subdef : pred T -> nat -> option T;
  choice_correct_subdef {P n x} : find_subdef P n = Some x -> P x;
  choice_complete_subdef {P : pred T} : (exists x, P x) -> exists n, find_subdef P n;
  choice_extensional_subdef {P Q : pred T} : P =1 Q -> find_subdef P =1 find_subdef Q
}.

#[short(type="choiceType")]
HB.structure Definition Choice := { T of HasChoice T & HasDecEq T}.

Module Export ChoiceNamespace.
  Module Choice.

  Module InternalTheory.

  Notation find := find_subdef.

  Notation correct := choice_correct_subdef.
  Arguments correct {_ _ _ _}.

  Notation complete := choice_complete_subdef.
  Arguments complete {_ _}.

  Notation extensional := choice_extensional_subdef.
  Arguments extensional {_ _ _}.

  Section InternalTheory.

  Variable T : Choice.type.
  Implicit Types P Q : pred T.

  Fact xchoose_subproof P exP :
    {x | find P (ex_minn (@choice_complete_subdef _ P exP)) = Some x}.
  Proof.
  case: (ex_minnP (complete exP)) => n.
  by case: (find P n) => // x; exists x.
  Qed.

  End InternalTheory.
  End InternalTheory.
  End Choice.
End ChoiceNamespace.

Notation "[ 'HasChoice' 'of' T ]" := (Choice.on _ : HasChoice T)
  (at level 0, format "[ 'HasChoice'  'of'  T ]") : form_scope.
Notation "[ 'choiceType' 'of' T 'for' C ]" := (Choice.clone T C)
  (at level 0, format "[ 'choiceType'  'of'  T  'for'  C ]") : form_scope.
Notation "[ 'choiceType' 'of' T ]" := (Choice.clone T _)
  (at level 0, format "[ 'choiceType'  'of'  T ]") : form_scope.

Section ChoiceTheory.

Implicit Type T : choiceType.
Import Choice.InternalTheory CodeSeq.
Local Notation dc := decode.

Section OneType.

Variable T : choiceType.
Implicit Types P Q : pred T.

Definition xchoose P exP := sval (@xchoose_subproof T P exP).

Lemma xchooseP P exP : P (@xchoose P exP).
Proof. by rewrite /xchoose; case: (xchoose_subproof exP) => x /= /correct. Qed.

Lemma eq_xchoose P Q exP exQ : P =1 Q -> @xchoose P exP = @xchoose Q exQ.
Proof.
rewrite /xchoose => eqPQ.
case: (xchoose_subproof exP) => x; case: (xchoose_subproof exQ) => y /=.
case: ex_minnP => n; rewrite -(extensional eqPQ) => Pn minQn.
case: ex_minnP => m; rewrite !(extensional eqPQ) => Qm minPm.
by case: (eqVneq m n) => [-> -> [] //|]; rewrite eqn_leq minQn ?minPm.
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
move=> exP; suffices [x /eqP Ex]: {x | lhs x == rhs x} by exists x.
by apply: sigW; have [x /eqP Ex] := exP; exists x.
Qed.

Lemma sig2_eqW (vT : eqType) (P : pred T) (lhs rhs : T -> vT) :
  (exists2 x, P x & lhs x = rhs x) -> {x | P x & lhs x = rhs x}.
Proof.
move=> exP; suffices [x Px /eqP Ex]: {x | P x & lhs x == rhs x} by exists x.
by apply: sig2W; have [x Px /eqP Ex] := exP; exists x.
Qed.

Definition choose P x0 :=
  if insub x0 : {? x | P x} is Some (exist x Px) then
    xchoose (ex_intro [eta P] x Px)
  else x0.

Lemma chooseP P x0 : P x0 -> P (choose P x0).
Proof. by move=> Px0; rewrite /choose insubT xchooseP. Qed.

Lemma choose_id P x0 y0 : P x0 -> P y0 -> choose P x0 = choose P y0.
Proof. by move=> Px0 Py0; rewrite /choose !insubT /=; apply: eq_xchoose. Qed.

Lemma eq_choose P Q : P =1 Q -> choose P =1 choose Q.
Proof.
rewrite /choose => eqPQ x0.
do [case: insubP; rewrite eqPQ] => [[x Px] Qx0 _| ?]; last by rewrite insubN.
by rewrite insubT; apply: eq_xchoose.
Qed.

Section CanChoice.

Variables (sT : Type) (f : sT -> T).

Lemma PcanChoiceMixin f' : pcancel f f' -> HasChoice sT.
Proof.
move=> fK; pose liftP sP := [pred x | oapp sP false (f' x)].
pose sf sP := [fun n => obind f' (find (liftP sP) n)].
exists sf => [sP n x | sP [y sPy] | sP sQ eqPQ n] /=.
- by case Df: (find _ n) => //= [?] Dx; have:= correct Df; rewrite /= Dx.
- have [|n Pn] := @complete T (liftP sP); first by exists (f y); rewrite /= fK.
  exists n; case Df: (find _ n) Pn => //= [x] _.
  by have:= correct Df => /=; case: (f' x).
by congr (obind _ _); apply: extensional => x /=; case: (f' x) => /=.
Qed.

Definition CanChoiceMixin f' (fK : cancel f f') :=
  PcanChoiceMixin (can_pcan fK).

HB.instance Definition _ f' (fK : pcancel f f') : HasChoice (pcan_type fK) :=
  PcanChoiceMixin fK.
HB.instance Definition _ f' (fK : cancel f f') : HasChoice (can_type fK) :=
  CanChoiceMixin fK.

End CanChoice.

Section SubChoice.

Variables (P : pred T) (sT : subType P).

Definition sub_HasChoice := PcanChoiceMixin (@valK T P sT).

HB.instance Definition _ : HasChoice (sub_type sT) := sub_HasChoice.

End SubChoice.

Fact seq_HasChoice : HasChoice (seq T).
Proof.
pose r f := [fun xs => fun x : T => f (x :: xs) : option (seq T)].
pose fix f sP ns xs {struct ns} :=
  if ns is n :: ns1 then let fr := r (f sP ns1) xs in obind fr (find fr n)
  else if sP xs then Some xs else None.
exists (fun sP nn => f sP (dc nn) nil) => [sP n ys | sP [ys] | sP sQ eqPQ n].
- elim: {n}(dc n) nil => [|n ns IHs] xs /=; first by case: ifP => // sPxs [<-].
  by case: (find _ n) => //= [x]; apply: IHs.
- rewrite -(cats0 ys); elim/last_ind: ys nil => [|ys y IHs] xs /=.
    by move=> sPxs; exists 0; rewrite /= sPxs.
  rewrite cat_rcons => /IHs[n1 sPn1] {IHs}.
  have /complete[n]: exists z, f sP (dc n1) (z :: xs) by exists y.
  case Df: (find _ n)=> // [x] _; exists (code (n :: dc n1)).
  by rewrite codeK /= Df /= (correct Df).
elim: {n}(dc n) nil => [|n ns IHs] xs /=; first by rewrite eqPQ.
rewrite (@extensional _ _ (r (f sQ ns) xs)) => [|x]; last by rewrite IHs.
by case: find => /=.
Qed.
HB.instance Definition _ := seq_HasChoice.

End OneType.

Section TagChoice.

Variables (I : choiceType) (T_ : I -> choiceType).

Fact tagged_HasChoice : HasChoice {i : I & T_ i}.
Proof.
pose mkT i (x : T_ i) := Tagged T_ x.
pose ft tP n i := omap (mkT i) (find (tP \o mkT i) n).
pose fi tP ni nt := obind (ft tP nt) (find (ft tP nt) ni).
pose f tP n := if dc n is [:: ni; nt] then fi tP ni nt else None.
exists f => [tP n u | tP [[i x] tPxi] | sP sQ eqPQ n].
- rewrite /f /fi; case: (dc n) => [|ni [|nt []]] //=.
  case: (find _ _) => //= [i]; rewrite /ft.
  by case Df: (find _ _) => //= [x] [<-]; have:= correct Df.
- have /complete[nt tPnt]: exists y, (tP \o mkT i) y by exists x.
  have{tPnt}: exists j, ft tP nt j by exists i; rewrite /ft; case: find tPnt.
  case/complete=> ni tPn; exists (code [:: ni; nt]); rewrite /f codeK /fi.
  by case Df: find tPn => //= [j] _; have:= correct Df.
rewrite /f /fi; case: (dc n) => [|ni [|nt []]] //=.
rewrite (@extensional _ _ (ft sQ nt)) => [|i].
  by case: find => //= i; congr (omap _ _); apply: extensional => x /=.
by congr (omap _ _); apply: extensional => x /=.
Qed.
HB.instance Definition _ := tagged_HasChoice.

End TagChoice.

Fact nat_HasChoice : HasChoice nat.
Proof.
pose f := [fun (P : pred nat) n => if P n then Some n else None].
exists f => [P n m | P [n Pn] | P Q eqPQ n] /=; last by rewrite eqPQ.
  by case: ifP => // Pn [<-].
by exists n; rewrite Pn.
Qed.
HB.instance Definition _ := nat_HasChoice.

HB.instance Definition _ : HasChoice bool := CanChoiceMixin oddb.
HB.instance Definition _ := [HasChoice of bitseq].

HB.instance Definition _ := CanChoiceMixin bool_of_unitK.

HB.instance Definition _ := PcanChoiceMixin (of_voidK unit).

HB.instance Definition _ T : HasChoice (option T) :=
  CanChoiceMixin (@seq_of_optK (Choice.sort T)).

HB.instance Definition _ (T1 T2 : choiceType) : HasChoice (T1 * T2)%type :=
  CanChoiceMixin (@tag_of_pairK T1 T2).

HB.instance Definition _ (T1 T2 : choiceType) : HasChoice (T1 + T2)%type :=
  PcanChoiceMixin (@opair_of_sumK T1 T2).

HB.instance Definition _ T : HasChoice (GenTree.tree T) :=
  PcanChoiceMixin (GenTree.codeK T).

End ChoiceTheory.

#[short(type="subChoiceType")]
HB.structure Definition SubChoice T (P : pred T) :=
  { sT of Choice sT & IsSUB T P sT }.

Notation subChoiceType := SubChoice.type.

Prenex Implicits xchoose choose.
Notation "[ 'Choice' 'of' T 'by' <: ]" := (Choice.copy T%type (sub_type T))
  (at level 0, format "[ 'Choice'  'of'  T  'by'  <: ]") : form_scope.

Notation "[ 'HasChoice' 'of' T 'by' <: ]" :=
  (sub_HasChoice _ : HasChoice T)
  (at level 0, format "[ 'HasChoice'  'of'  T  'by'  <: ]") : form_scope.

HB.instance Definition _ (T : choiceType) (P : pred T) :=
  [Choice of {x | P x} by <:].

HB.mixin Record IsCountable (T : Type) : Type := {
  pickle : T -> nat;
  unpickle : nat -> option T;
  pickleK : pcancel pickle unpickle
}.
Arguments IsCountable.axioms_ T%type_scope.

#[short(type="countType")]
HB.structure Definition Countable := { T of Choice T & IsCountable T }.

Notation "[ 'IsCountable' 'of' T ]" := (Countable.on T : IsCountable T)
  (at level 0, format "[ 'IsCountable'  'of'  T ]") : form_scope.
Notation "[ 'countType' 'of' T 'for' cT ]" := (Countable.clone T cT)
(at level 0, format "[ 'countType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'countType' 'of' T ]" := (Countable.clone T _)
  (at level 0, format "[ 'countType'  'of'  T ]") : form_scope.

(* count_type cntT is a canonical count type generated by *)
(* cntT : IsCountable T *)
Definition count_type T of IsCountable T := T.
HB.instance Definition _ T (cntT : IsCountable T) :=
  Choice.copy (count_type cntT) (pcan_type (IsCountable.pickleK cntT)).
HB.instance Definition _ T (cntT : IsCountable T) :
  IsCountable (count_type cntT) := cntT.

Section CountableTheory.

Variable T : countType.

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

Definition PcanCountMixin sT (f : sT -> T) f' (fK : pcancel f f') :=
  IsCountable.Build sT (pcan_pickleK fK).

Definition CanCountMixin sT f f' (fK : cancel f f') :=
  @PcanCountMixin sT _ _ (can_pcan fK).

HB.instance Definition _ sT (f : sT -> T) f' (fK : pcancel f f') :
  IsCountable (pcan_type fK) := PcanCountMixin fK.
HB.instance Definition _ sT (f : sT -> T) f' (fK : cancel f f') :
  IsCountable (can_type fK) := CanCountMixin fK.

HB.instance Definition sub_IsCountable (P : pred T) (sT : subType P) :
  IsCountable (sub_type sT) := PcanCountMixin (@valK T P sT).

Definition pickle_seq s := CodeSeq.code (map (@pickle T) s).
Definition unpickle_seq n := Some (pmap (@unpickle T) (CodeSeq.decode n)).
Lemma pickle_seqK : pcancel pickle_seq unpickle_seq.
Proof. by move=> s; rewrite /unpickle_seq CodeSeq.codeK (map_pK pickleK). Qed.

HB.instance Definition seq_IsCountable := IsCountable.Build (seq T) pickle_seqK.

End CountableTheory.

Notation "[ 'Countable' 'of' T 'by' <: ]" :=
    (Countable.copy T%type (sub_type T))
  (at level 0, format "[ 'Countable'  'of'  T  'by'  <: ]") : form_scope.
Notation "[ 'IsCountable' 'of' T 'by' <: ]" := [Countable of T by <:]
  (at level 0, format "[ 'IsCountable'  'of'  T  'by'  <: ]") : form_scope.

Arguments pickle_inv {T} n.
Arguments pickleK {T} x : rename.
Arguments pickleK_inv {T} x.
Arguments pickle_invK {T} n : rename.

#[short(type="subCountType")]
HB.structure Definition SubCountable T (P : pred T) :=
  { sT of Countable sT & IsSUB T P sT}.

(* This assumes that T has both countType and subType structures. *)
(* TODO: replace with trivial pack *)
Notation "[ 'subCountType' 'of' T ]" := (SubCountable.clone _ _ T _)
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

HB.instance Definition tag_IsCountable :=
  IsCountable.Build {i : I & T_ i} pickle_taggedK.

End TagCountType.

(* The remaining Canonicals for standard datatypes. *)
Section CountableDataTypes.

Implicit Type T : countType.

Lemma nat_pickleK : pcancel id (@Some nat). Proof. by []. Qed.
HB.instance Definition _ : IsCountable nat := IsCountable.Build nat nat_pickleK.

HB.instance Definition _ := Countable.copy bool (can_type oddb).
HB.instance Definition _ : IsCountable bitseq := [IsCountable of bitseq].

HB.instance Definition _ := Countable.copy unit (can_type bool_of_unitK).

HB.instance Definition _ := Countable.copy void
  (pcan_type (of_voidK unit)).

HB.instance Definition _ T := Countable.copy (option T)
  (can_type (@seq_of_optK T)).

HB.instance Definition _ T (P : pred T) := [Countable of {x | P x} by <:].

HB.instance Definition _ T1 T2 :=
  Countable.copy (T1 * T2)%type (can_type (@tag_of_pairK T1 T2)).

HB.instance Definition _ (T1 T2 : countType) :=
  Countable.copy (T1 + T2)%type (pcan_type (@opair_of_sumK T1 T2)).

HB.instance Definition _ T := Countable.copy (GenTree.tree T)
   (pcan_type (GenTree.codeK T)).

End CountableDataTypes.

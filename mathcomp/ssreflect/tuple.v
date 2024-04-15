(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From mathcomp Require Import seq choice fintype path.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(******************************************************************************)
(* This file defines tuples, i.e., sequences with a fixed (known) length,     *)
(* and sequences with bounded length.                                         *)
(* For tuples we define:                                                      *)
(*         n.-tuple T == the type of n-tuples of elements of type T           *)
(*       [tuple of s] == the tuple whose underlying sequence (value) is s     *)
(*                       The size of s must be known: specifically, Coq must  *)
(*                       be able to infer a Canonical tuple projecting on s.  *)
(*         in_tuple s == the (size s).-tuple with value s                     *)
(*            [tuple] == the empty tuple                                      *)
(* [tuple x1; ..; xn] == the explicit n.-tuple <x1; ..; xn>                   *)
(*  [tuple E | i < n] == the n.-tuple with general term E (i : 'I_n is bound  *)
(*                       in E)                                                *)
(*        tcast Emn t == the m.-tuple t cast as an n.-tuple using Emn : m = n *)
(* As n.-tuple T coerces to seq t, all seq operations (size, nth, ...) can be *)
(* applied to t : n.-tuple T; we provide a few specialized instances when     *)
(* avoids the need for a default value.                                       *)
(*            tsize t == the size of t (the n in n.-tuple T)                  *)
(*           tnth t i == the i'th component of t, where i : 'I_n              *)
(*         [tnth t i] == the i'th component of t, where i : nat and i < n     *)
(*                       is convertible to true                               *)
(*            thead t == the first element of t, when n is m.+1 for some m    *)
(* For bounded sequences we define:                                           *)
(*         n.-bseq T  == the type of bounded sequences of elements of type T, *)
(*                       the length of a bounded sequence is smaller or       *)
(*                       or equal to n                                        *)
(*       [bseq of s]  == the bounded sequence whose underlying value is s     *)
(*                       The size of s must be known.                         *)
(*         in_bseq s  == the (size s).-bseq with value s                      *)
(*            [bseq]  == the empty bseq                                       *)
(*     insub_bseq n s == the n.-bseq of value s if size s <= n, else [bseq]   *)
(* [bseq x1; ..; xn]  == the explicit n.-bseq <x1; ..; xn>                    *)
(*    cast_bseq Emn t == the m.-bseq t cast as an n.-tuple using Emn : m = n  *)
(*   widen_bseq Lmn t == the m.-bseq t cast as an n.-tuple using Lmn : m <= n *)
(* Most seq constructors (cons, behead, cat, rcons, belast, take, drop, rot,  *)
(* rotr, map, ...) can be used to build tuples and bounded sequences via      *)
(* the [tuple of s] and [bseq of s] constructs respectively.                  *)
(*   Tuples and bounded sequences are actually instances of subType of seq,   *)
(* and inherit all combinatorial structures, including the finType structure. *)
(*   Some useful lemmas and definitions:                                      *)
(*     tuple0 : [tuple] is the only 0.-tuple                                  *)
(*     bseq0 : [bseq] is the only 0.-bseq                                     *)
(*     tupleP : elimination view for n.+1.-tuple                              *)
(*     ord_tuple n : the n.-tuple of all i : 'I_n                             *)
(******************************************************************************)

Section TupleDef.

Variables (n : nat) (T : Type).

Structure tuple_of : Type := Tuple {tval :> seq T; _ : size tval == n}.

HB.instance Definition _ := [isSub for tval].

Implicit Type t : tuple_of.

Definition tsize of tuple_of := n.

Lemma size_tuple t : size t = n.
Proof. exact: (eqP (valP t)). Qed.

Lemma tnth_default t : 'I_n -> T.
Proof. by rewrite -(size_tuple t); case: (tval t) => [|//] []. Qed.

Definition tnth t i := nth (tnth_default t i) t i.

Lemma tnth_nth x t i : tnth t i = nth x t i.
Proof. by apply: set_nth_default; rewrite size_tuple. Qed.

Lemma map_tnth_enum t : map (tnth t) (enum 'I_n) = t.
Proof.
case def_t: {-}(val t) => [|x0 t'].
  by rewrite [enum _]size0nil // -cardE card_ord -(size_tuple t) def_t.
apply: (@eq_from_nth _ x0) => [|i]; rewrite size_map.
  by rewrite -cardE size_tuple card_ord.
move=> lt_i_e; have lt_i_n: i < n by rewrite -cardE card_ord in lt_i_e.
by rewrite (nth_map (Ordinal lt_i_n)) // (tnth_nth x0) nth_enum_ord.
Qed.

Lemma eq_from_tnth t1 t2 : tnth t1 =1 tnth t2 -> t1 = t2.
Proof.
by move/eq_map=> eq_t; apply: val_inj; rewrite /= -!map_tnth_enum eq_t.
Qed.

End TupleDef.

Notation "n .-tuple" := (tuple_of n)
  (at level 2, format "n .-tuple") : type_scope.

Notation "{ 'tuple' n 'of' T }" := (n.-tuple T : predArgType)
  (at level 0, only parsing) : type_scope.

Notation "[ 'tuple' 'of' s ]" := (s : _.-tuple _)
  (at level 0, format "[ 'tuple'  'of'  s ]") : form_scope.

Notation "[ 'tnth' t i ]" := (tnth t (@Ordinal (tsize t) i (erefl true)))
  (at level 0, t, i at level 8, format "[ 'tnth'  t  i ]") : form_scope.

Canonical nil_tuple T := Tuple (isT : @size T [::] == 0).
Canonical cons_tuple n T x (t : n.-tuple T) :=
  Tuple (valP t : size (x :: t) == n.+1).

Notation "[ 'tuple' x1 ; .. ; xn ]" := [tuple of x1 :: .. [:: xn] ..]
  (at level 0, format "[ 'tuple' '['  x1 ; '/'  .. ; '/'  xn ']' ]")
  : form_scope.

Notation "[ 'tuple' ]" := [tuple of [::]]
  (at level 0, format "[ 'tuple' ]") : form_scope.

Section CastTuple.

Variable T : Type.

Definition in_tuple (s : seq T) := Tuple (eqxx (size s)).

Definition tcast m n (eq_mn : m = n) t :=
  let: erefl in _ = n := eq_mn return n.-tuple T in t.

Lemma tcastE m n (eq_mn : m = n) t i :
  tnth (tcast eq_mn t) i = tnth t (cast_ord (esym eq_mn) i).
Proof. by case: n / eq_mn in i *; rewrite cast_ord_id. Qed.

Lemma tcast_id n (eq_nn : n = n) t : tcast eq_nn t = t.
Proof. by rewrite (eq_axiomK eq_nn). Qed.

Lemma tcastK m n (eq_mn : m = n) : cancel (tcast eq_mn) (tcast (esym eq_mn)).
Proof. by case: n / eq_mn. Qed.

Lemma tcastKV m n (eq_mn : m = n) : cancel (tcast (esym eq_mn)) (tcast eq_mn).
Proof. by case: n / eq_mn. Qed.

Lemma tcast_trans m n p (eq_mn : m = n) (eq_np : n = p) t:
  tcast (etrans eq_mn eq_np) t = tcast eq_np (tcast eq_mn t).
Proof. by case: n / eq_mn eq_np; case: p /. Qed.

Lemma tvalK n (t : n.-tuple T) : in_tuple t = tcast (esym (size_tuple t)) t.
Proof. by apply: val_inj => /=; case: _ / (esym _). Qed.

Lemma val_tcast m n (eq_mn : m = n) (t : m.-tuple T) :
  tcast eq_mn t = t :> seq T.
Proof. by case: n / eq_mn. Qed.

Lemma in_tupleE s : in_tuple s = s :> seq T. Proof. by []. Qed.

End CastTuple.

Section SeqTuple.

Variables (n m : nat) (T U rT : Type).
Implicit Type t : n.-tuple T.

Lemma rcons_tupleP t x : size (rcons t x) == n.+1.
Proof. by rewrite size_rcons size_tuple. Qed.
Canonical rcons_tuple t x := Tuple (rcons_tupleP t x).

Lemma nseq_tupleP x : @size T (nseq n x) == n.
Proof. by rewrite size_nseq. Qed.
Canonical nseq_tuple x := Tuple (nseq_tupleP x).

Lemma iota_tupleP : size (iota m n) == n.
Proof. by rewrite size_iota. Qed.
Canonical iota_tuple := Tuple iota_tupleP.

Lemma behead_tupleP t : size (behead t) == n.-1.
Proof. by rewrite size_behead size_tuple. Qed.
Canonical behead_tuple t := Tuple (behead_tupleP t).

Lemma belast_tupleP x t : size (belast x t) == n.
Proof. by rewrite size_belast size_tuple. Qed.
Canonical belast_tuple x t := Tuple (belast_tupleP x t).

Lemma cat_tupleP t (u : m.-tuple T) : size (t ++ u) == n + m.
Proof. by rewrite size_cat !size_tuple. Qed.
Canonical cat_tuple t u := Tuple (cat_tupleP t u).

Lemma take_tupleP t : size (take m t) == minn m n.
Proof. by rewrite size_take size_tuple eqxx. Qed.
Canonical take_tuple t := Tuple (take_tupleP t).

Lemma drop_tupleP t : size (drop m t) == n - m.
Proof. by rewrite size_drop size_tuple. Qed.
Canonical drop_tuple t := Tuple (drop_tupleP t).

Lemma rev_tupleP t : size (rev t) == n.
Proof. by rewrite size_rev size_tuple. Qed.
Canonical rev_tuple t := Tuple (rev_tupleP t).

Lemma rot_tupleP t : size (rot m t) == n.
Proof. by rewrite size_rot size_tuple. Qed.
Canonical rot_tuple t := Tuple (rot_tupleP t).

Lemma rotr_tupleP t : size (rotr m t) == n.
Proof. by rewrite size_rotr size_tuple. Qed.
Canonical rotr_tuple t := Tuple (rotr_tupleP t).

Lemma map_tupleP f t : @size rT (map f t) == n.
Proof. by rewrite size_map size_tuple. Qed.
Canonical map_tuple f t := Tuple (map_tupleP f t).

Lemma scanl_tupleP f x t : @size rT (scanl f x t) == n.
Proof. by rewrite size_scanl size_tuple. Qed.
Canonical scanl_tuple f x t := Tuple (scanl_tupleP f x t).

Lemma pairmap_tupleP f x t : @size rT (pairmap f x t) == n.
Proof. by rewrite size_pairmap size_tuple. Qed.
Canonical pairmap_tuple f x t := Tuple (pairmap_tupleP f x t).

Lemma zip_tupleP t (u : n.-tuple U) : size (zip t u) == n.
Proof. by rewrite size1_zip !size_tuple. Qed.
Canonical zip_tuple t u := Tuple (zip_tupleP t u).

Lemma allpairs_tupleP f t (u : m.-tuple U) : @size rT (allpairs f t u) == n * m.
Proof. by rewrite size_allpairs !size_tuple. Qed.
Canonical allpairs_tuple f t u := Tuple (allpairs_tupleP f t u).

Lemma sort_tupleP r t : size (sort r t) == n.
Proof. by rewrite size_sort size_tuple. Qed.
Canonical sort_tuple r t := Tuple (sort_tupleP r t).

Definition thead (u : n.+1.-tuple T) := tnth u ord0.

Lemma tnth0 x t : tnth (x :: t) ord0 = x.
Proof. by []. Qed.


Lemma tnthS x t (i : 'I_n) : tnth (x :: t) i.+1 = tnth t i.
Proof. by rewrite (tnth_nth (tnth_default t i)). Qed.

Lemma theadE x t : thead (x :: t) = x. Proof. by []. Qed.

Lemma tuple0 : all_equal_to ([::] : 0.-tuple T).
Proof. by move=> t; apply: val_inj; case: t => [[]]. Qed.

Variant tuple1_spec : n.+1.-tuple T -> Type :=
  Tuple1spec x t : tuple1_spec (x :: t).

Lemma tupleP u : tuple1_spec u.
Proof.
case: u => [[|x s] //= sz_s]; pose t := @Tuple n _ s sz_s.
by rewrite (_ : Tuple _ = x :: t) //; apply: val_inj.
Qed.

Lemma tnth_map f t i : tnth (map f t) i = f (tnth t i) :> rT.
Proof. by apply: nth_map; rewrite size_tuple. Qed.

Lemma tnth_nseq x i : tnth (nseq n x) i = x.
Proof.
by rewrite !(tnth_nth (tnth_default (nseq_tuple x) i)) nth_nseq ltn_ord.
Qed.

End SeqTuple.

Lemma tnth_behead n T (t : n.+1.-tuple T) i :
  tnth (behead t) i = tnth t (inord i.+1).
Proof. by case/tupleP: t => x t; rewrite !(tnth_nth x) inordK ?ltnS. Qed.

Lemma tuple_eta n T (t : n.+1.-tuple T) : t = [tuple of thead t :: behead t]. (* BUG *)
Proof. by case/tupleP: t => x t; apply: val_inj. Qed.

Section tnth_shift.
Context {T : Type} {n1 n2} (t1 : n1.-tuple T) (t2 : n2.-tuple T).

Lemma tnth_lshift i : tnth [tuple of t1 ++ t2] (lshift n2 i) = tnth t1 i.
Proof.
have x0 := tnth_default t1 i; rewrite !(tnth_nth x0).
by rewrite nth_cat size_tuple /= ltn_ord.
Qed.

Lemma tnth_rshift j : tnth [tuple of t1 ++ t2] (rshift n1 j) = tnth t2 j.
Proof.
have x0 := tnth_default t2 j; rewrite !(tnth_nth x0).
by rewrite nth_cat size_tuple ltnNge leq_addr /= addKn.
Qed.
End tnth_shift.

Section TupleQuantifiers.

Variables (n : nat) (T : Type).
Implicit Types (a : pred T) (t : n.-tuple T).

Lemma forallb_tnth a t : [forall i, a (tnth t i)] = all a t.
Proof.
apply: negb_inj; rewrite -has_predC -has_map negb_forall.
apply/existsP/(has_nthP true) => [[i a_t_i] | [i lt_i_n a_t_i]].
  by exists i; rewrite ?size_tuple // -tnth_nth tnth_map.
rewrite size_tuple in lt_i_n; exists (Ordinal lt_i_n).
by rewrite -tnth_map (tnth_nth true).
Qed.

Lemma existsb_tnth a t : [exists i, a (tnth t i)] = has a t.
Proof. by apply: negb_inj; rewrite negb_exists -all_predC -forallb_tnth. Qed.

Lemma all_tnthP a t : reflect (forall i, a (tnth t i)) (all a t).
Proof. by rewrite -forallb_tnth; apply: forallP. Qed.

Lemma has_tnthP a t : reflect (exists i, a (tnth t i)) (has a t).
Proof. by rewrite -existsb_tnth; apply: existsP. Qed.

End TupleQuantifiers.

Arguments all_tnthP {n T a t}.
Arguments has_tnthP {n T a t}.

Section EqTuple.

Variables (n : nat) (T : eqType).

HB.instance Definition _ : hasDecEq (n.-tuple T) :=
  [Equality of n.-tuple T by <:].
Canonical tuple_predType := PredType (pred_of_seq : n.-tuple T -> pred T).

Lemma eqEtuple (t1 t2 : n.-tuple T) :
  (t1 == t2) = [forall i, tnth t1 i == tnth t2 i].
Proof. by apply/eqP/'forall_eqP => [->|/eq_from_tnth]. Qed.

Lemma memtE (t : n.-tuple T) : mem t = mem (tval t).
Proof. by []. Qed.

Lemma mem_tnth i (t : n.-tuple T) : tnth t i \in t.
Proof. by rewrite mem_nth ?size_tuple. Qed.

Lemma memt_nth x0 (t : n.-tuple T) i : i < n -> nth x0 t i \in t.
Proof. by move=> i_lt_n; rewrite mem_nth ?size_tuple. Qed.

Lemma tnthP (t : n.-tuple T) x : reflect (exists i, x = tnth t i) (x \in t).
Proof.
apply: (iffP idP) => [/(nthP x)[i ltin <-] | [i ->]]; last exact: mem_tnth.
by rewrite size_tuple in ltin; exists (Ordinal ltin); rewrite (tnth_nth x).
Qed.

Lemma seq_tnthP (s : seq T) x : x \in s -> {i | x = tnth (in_tuple s) i}.
Proof.
move=> s_x; pose i := index x s; have lt_i: i < size s by rewrite index_mem.
by exists (Ordinal lt_i); rewrite (tnth_nth x) nth_index.
Qed.

Lemma tuple_uniqP (t : n.-tuple T) : reflect (injective (tnth t)) (uniq t).
Proof.
case: {+}n => [|m] in t *; first by rewrite tuple0; constructor => -[].
pose x0 := tnth t ord0; apply/(equivP (uniqP x0)); split=> tinj i j.
  by rewrite !(tnth_nth x0) => /tinj/val_inj; apply; rewrite size_tuple inE.
rewrite !size_tuple !inE => im jm; have := tinj (Ordinal im) (Ordinal jm).
by rewrite !(tnth_nth x0) => /[apply]-[].
Qed.

End EqTuple.

HB.instance Definition _ n (T : choiceType) :=
  [Choice of n.-tuple T by <:].
HB.instance Definition _ n (T : countType) :=
  [Countable of n.-tuple T by <:].

Module Type FinTupleSig.
Section FinTupleSig.
Variables (n : nat) (T : finType).
Parameter enum : seq (n.-tuple T).
Axiom enumP : Finite.axiom enum.
Axiom size_enum : size enum = #|T| ^ n.
End FinTupleSig.
End FinTupleSig.

Module FinTuple : FinTupleSig.
Section FinTuple.
Variables (n : nat) (T : finType).

Definition enum : seq (n.-tuple T) :=
  let extend e := flatten (codom (fun x => map (cons x) e)) in
  pmap insub (iter n extend [::[::]]).

Lemma enumP : Finite.axiom enum.
Proof.
case=> /= t t_n; rewrite -(count_map _ (pred1 t)) (pmap_filter (insubK _)).
rewrite count_filter -(@eq_count _ (pred1 t)) => [|s /=]; last first.
  by rewrite isSome_insub; case: eqP=> // ->.
elim: n t t_n => [|m IHm] [|x t] //= {}/IHm; move: (iter m _ _) => em IHm.
transitivity (x \in T : nat); rewrite // -mem_enum codomE.
elim: (fintype.enum T) (enum_uniq T) => //= y e IHe /andP[/negPf ney].
rewrite count_cat count_map inE /preim /= [in LHS]/eq_op /= eq_sym => /IHe->.
by case: eqP => [->|_]; rewrite ?(ney, count_pred0, IHm).
Qed.

Lemma size_enum : size enum = #|T| ^ n.
Proof.
rewrite /= cardE size_pmap_sub; elim: n => //= m IHm.
rewrite expnS /codom /image_mem; elim: {2 3}(fintype.enum T) => //= x e IHe.
by rewrite count_cat {}IHe count_map IHm.
Qed.

End FinTuple.
End FinTuple.

Section UseFinTuple.

Variables (n : nat) (T : finType).

(* tuple_finMixin could, in principle, be made Canonical to allow for folding *)
(* Finite.enum of a finite tuple type (see comments around eqE in eqtype.v),  *)
(* but in practice it will not work because the mixin_enum projector          *)
(* has been buried under an opaque alias, to avoid some performance issues    *)
(* during type inference.                                                     *)
HB.instance Definition _ := isFinite.Build (n.-tuple T) (@FinTuple.enumP n T).

Lemma card_tuple : #|{:n.-tuple T}| = #|T| ^ n.
Proof. by rewrite [#|_|]cardT enumT unlock FinTuple.size_enum. Qed.

Lemma enum_tupleP (A : {pred T}) : size (enum A) == #|A|.
Proof. by rewrite -cardE. Qed.
Canonical enum_tuple A := Tuple (enum_tupleP A).

Definition ord_tuple : n.-tuple 'I_n := Tuple (introT eqP (size_enum_ord n)).
Lemma val_ord_tuple : val ord_tuple = enum 'I_n. Proof. by []. Qed.

Lemma tuple_map_ord U (t : n.-tuple U) : t = map (tnth t) ord_tuple.
Proof. by apply: val_inj => /=; rewrite map_tnth_enum. Qed.

Lemma tnth_ord_tuple i : tnth ord_tuple i = i.
Proof.
apply: val_inj; rewrite (tnth_nth i) -(nth_map _ 0) ?size_tuple //.
by rewrite /= enumT unlock val_ord_enum nth_iota.
Qed.

Section ImageTuple.

Variables (T' : Type) (f : T -> T') (A : {pred T}).

Canonical image_tuple : #|A|.-tuple T' := image f A.
Canonical codom_tuple : #|T|.-tuple T' := codom f.

End ImageTuple.

Section MkTuple.

Variables (T' : Type) (f : 'I_n -> T').

Definition mktuple := map_tuple f ord_tuple.

Lemma tnth_mktuple i : tnth mktuple i = f i.
Proof. by rewrite tnth_map tnth_ord_tuple. Qed.

Lemma nth_mktuple x0 (i : 'I_n) : nth x0 mktuple i = f i.
Proof. by rewrite -tnth_nth tnth_mktuple. Qed.

End MkTuple.

Lemma eq_mktuple T' (f1 f2 : 'I_n -> T') :
  f1 =1 f2 -> mktuple f1 = mktuple f2.
Proof. by move=> eq_f; apply eq_from_tnth=> i; rewrite !tnth_map eq_f. Qed.

End UseFinTuple.

Notation "[ 'tuple' F | i < n ]" := (mktuple (fun i : 'I_n => F))
  (at level 0, i at level 0,
   format "[ '[hv' 'tuple'  F '/'   |  i  <  n ] ']'") : form_scope.

Arguments eq_mktuple {n T'} [f1] f2 eq_f12.

Section BseqDef.

Variables (n : nat) (T : Type).

Structure bseq_of : Type := Bseq {bseqval :> seq T; _ : size bseqval <= n}.

HB.instance Definition _ := [isSub for bseqval].

Implicit Type bs : bseq_of.

Lemma size_bseq bs : size bs <= n.
Proof. by case: bs. Qed.

Definition bseq bs mkB : bseq_of :=
  mkB (let: Bseq _ bsP := bs return size bs <= n in bsP).

Lemma bseqE bs : bseq (fun sP => @Bseq bs sP) = bs.
Proof. by case: bs. Qed.

End BseqDef.

Canonical nil_bseq n T := Bseq (isT : @size T [::] <= n).
Canonical cons_bseq n T x (t : bseq_of n T) :=
  Bseq (valP t : size (x :: t) <= n.+1).

Notation "n .-bseq" := (bseq_of n)
  (at level 2, format "n .-bseq") : type_scope.

Notation "{ 'bseq' n 'of' T }" := (n.-bseq T : predArgType)
  (at level 0, only parsing) : type_scope.

Notation "[ 'bseq' 'of' s ]" := (bseq (fun sP => @Bseq _ _ s sP))
  (at level 0, format "[ 'bseq'  'of'  s ]") : form_scope.

Notation "[ 'bseq' x1 ; .. ; xn ]" := [bseq of x1 :: .. [:: xn] ..]
  (at level 0, format "[ 'bseq' '['  x1 ; '/'  .. ; '/'  xn ']' ]")
  : form_scope.

Notation "[ 'bseq' ]" := [bseq of [::]]
  (at level 0, format "[ 'bseq' ]") : form_scope.

Coercion bseq_of_tuple n T (t : n.-tuple T) : n.-bseq T :=
  Bseq (eq_leq (size_tuple t)).

Definition insub_bseq n T (s : seq T) : n.-bseq T := insubd [bseq] s.

Lemma size_insub_bseq n T (s : seq T) : size (insub_bseq n s) <= size s.
Proof. by rewrite /insub_bseq /insubd; case: insubP => // ? ? ->. Qed.

Section CastBseq.

Variable T : Type.

Definition in_bseq (s : seq T) : (size s).-bseq T := Bseq (leqnn (size s)).

Definition cast_bseq m n (eq_mn : m = n) bs :=
  let: erefl in _ = n := eq_mn return n.-bseq T in bs.

Definition widen_bseq m n (lemn : m <= n) (bs : m.-bseq T) : n.-bseq T :=
  @Bseq n T bs (leq_trans (size_bseq bs) lemn).

Lemma cast_bseq_id n (eq_nn : n = n) bs : cast_bseq eq_nn bs = bs.
Proof. by rewrite (eq_axiomK eq_nn). Qed.

Lemma cast_bseqK m n (eq_mn : m = n) :
  cancel (cast_bseq eq_mn) (cast_bseq (esym eq_mn)).
Proof. by case: n / eq_mn. Qed.

Lemma cast_bseqKV m n (eq_mn : m = n) :
  cancel (cast_bseq (esym eq_mn)) (cast_bseq eq_mn).
Proof. by case: n / eq_mn. Qed.

Lemma cast_bseq_trans m n p (eq_mn : m = n) (eq_np : n = p) bs :
  cast_bseq (etrans eq_mn eq_np) bs = cast_bseq eq_np (cast_bseq eq_mn bs).
Proof. by case: n / eq_mn eq_np; case: p /. Qed.

Lemma size_cast_bseq m n (eq_mn : m = n) (bs : m.-bseq T) :
  size (cast_bseq eq_mn bs) = size bs.
Proof. by case: n / eq_mn. Qed.

Lemma widen_bseq_id n (lenn : n <= n) (bs : n.-bseq T) :
  widen_bseq lenn bs = bs.
Proof. exact: val_inj. Qed.

Lemma cast_bseqEwiden m n (eq_mn : m = n) (bs : m.-bseq T) :
  cast_bseq eq_mn bs = widen_bseq (eq_leq eq_mn) bs.
Proof. by case: n / eq_mn; rewrite widen_bseq_id. Qed.

Lemma widen_bseqK m n (lemn : m <= n) (lenm : n <= m) :
   cancel (@widen_bseq m n lemn) (widen_bseq lenm).
Proof. by move=> t; apply: val_inj. Qed.

Lemma widen_bseq_trans m n p (lemn : m <= n) (lenp : n <= p) (bs : m.-bseq T) :
  widen_bseq (leq_trans lemn lenp) bs = widen_bseq lenp (widen_bseq lemn bs).
Proof. exact/val_inj. Qed.

Lemma size_widen_bseq m n (lemn : m <= n) (bs : m.-bseq T) :
  size (widen_bseq lemn bs) = size bs.
Proof. by []. Qed.

Lemma in_bseqE s : in_bseq s = s :> seq T. Proof. by []. Qed.

Lemma widen_bseq_in_bseq n (bs : n.-bseq T) :
  widen_bseq (size_bseq bs) (in_bseq bs) = bs.
Proof. exact: val_inj. Qed.

End CastBseq.

Section SeqBseq.

Variables (n m : nat) (T U rT : Type).
Implicit Type s : n.-bseq T.

Lemma rcons_bseqP s x : size (rcons s x) <= n.+1.
Proof. by rewrite size_rcons ltnS size_bseq. Qed.
Canonical rcons_bseq s x := Bseq (rcons_bseqP s x).

Lemma behead_bseqP s : size (behead s) <= n.-1.
Proof. rewrite size_behead -!subn1; apply/leq_sub2r/size_bseq. Qed.
Canonical behead_bseq s := Bseq (behead_bseqP s).

Lemma belast_bseqP x s : size (belast x s) <= n.
Proof. by rewrite size_belast; apply/size_bseq. Qed.
Canonical belast_bseq x s := Bseq (belast_bseqP x s).

Lemma cat_bseqP s (s' : m.-bseq T) : size (s ++ s') <= n + m.
Proof. by rewrite size_cat; apply/leq_add/size_bseq/size_bseq. Qed.
Canonical cat_bseq s (s' : m.-bseq T) := Bseq (cat_bseqP s s').

Lemma take_bseqP s : size (take m s) <= n.
Proof.
by rewrite size_take_min (leq_trans _ (size_bseq s)) // geq_minr.
Qed.
Canonical take_bseq s := Bseq (take_bseqP s).

Lemma drop_bseqP s : size (drop m s) <= n - m.
Proof. by rewrite size_drop; apply/leq_sub2r/size_bseq. Qed.
Canonical drop_bseq s := Bseq (drop_bseqP s).

Lemma rev_bseqP s : size (rev s) <= n.
Proof. by rewrite size_rev size_bseq. Qed.
Canonical rev_bseq s := Bseq (rev_bseqP s).

Lemma rot_bseqP s : size (rot m s) <= n.
Proof. by rewrite size_rot size_bseq. Qed.
Canonical rot_bseq s := Bseq (rot_bseqP s).

Lemma rotr_bseqP s : size (rotr m s) <= n.
Proof. by rewrite size_rotr size_bseq. Qed.
Canonical rotr_bseq s := Bseq (rotr_bseqP s).

Lemma map_bseqP f s : @size rT (map f s) <= n.
Proof. by rewrite size_map size_bseq. Qed.
Canonical map_bseq f s := Bseq (map_bseqP f s).

Lemma scanl_bseqP f x s : @size rT (scanl f x s) <= n.
Proof. by rewrite size_scanl size_bseq. Qed.
Canonical scanl_bseq f x s := Bseq (scanl_bseqP f x s).

Lemma pairmap_bseqP f x s : @size rT (pairmap f x s) <= n.
Proof. by rewrite size_pairmap size_bseq. Qed.
Canonical pairmap_bseq f x s := Bseq (pairmap_bseqP f x s).

Lemma allpairs_bseqP f s (s' : m.-bseq U) : @size rT (allpairs f s s') <= n * m.
Proof. by rewrite size_allpairs; apply/leq_mul/size_bseq/size_bseq. Qed.
Canonical allpairs_bseq f s (s' : m.-bseq U) := Bseq (allpairs_bseqP f s s').

Lemma sort_bseqP r s : size (sort r s) <= n.
Proof. by rewrite size_sort size_bseq. Qed.
Canonical sort_bseq r s := Bseq (sort_bseqP r s).

Lemma bseq0 : all_equal_to ([bseq] : 0.-bseq T).
Proof. by move=> s; apply: val_inj; case: s => [[]]. Qed.

End SeqBseq.

HB.instance Definition bseq_hasDecEq n (T : eqType) :=
  [Equality of n.-bseq T by <:].

Canonical bseq_predType n (T : eqType) :=
  Eval hnf in PredType (fun t : n.-bseq T => mem_seq t).

Lemma membsE n (T : eqType) (bs : n.-bseq T) : mem bs = mem (bseqval bs).
Proof. by []. Qed.

HB.instance Definition bseq_hasChoice n (T : choiceType) :=
  [Choice of n.-bseq T by <:].

HB.instance Definition bseq_isCountable n (T : countType) :=
  [Countable of n.-bseq T by <:].

Definition bseq_tagged_tuple n T (s : n.-bseq T) : {k : 'I_n.+1 & k.-tuple T} :=
  Tagged _ (in_tuple s : (Ordinal (size_bseq s : size s < n.+1)).-tuple _).
Arguments bseq_tagged_tuple {n T}.

Definition tagged_tuple_bseq n T (t : {k : 'I_n.+1 & k.-tuple T}) : n.-bseq T :=
  widen_bseq (leq_ord (tag t)) (tagged t).
Arguments tagged_tuple_bseq {n T}.

Lemma bseq_tagged_tupleK {n T} :
  cancel (@bseq_tagged_tuple n T) tagged_tuple_bseq.
Proof. by move=> bs; apply/val_inj. Qed.

Lemma tagged_tuple_bseqK {n T} :
  cancel (@tagged_tuple_bseq n T) bseq_tagged_tuple.
Proof.
move=> [[k lt_kn] t]; apply: eq_existT_curried => [|k_eq]; apply/val_inj.
  by rewrite /= size_tuple.
by refine (let: erefl := k_eq in _).
Qed.

Lemma bseq_tagged_tuple_bij {n T} : bijective (@bseq_tagged_tuple n T).
Proof. exact/Bijective/tagged_tuple_bseqK/bseq_tagged_tupleK. Qed.

Lemma tagged_tuple_bseq_bij {n T} : bijective (@tagged_tuple_bseq n T).
Proof. exact/Bijective/bseq_tagged_tupleK/tagged_tuple_bseqK. Qed.

#[global] Hint Resolve bseq_tagged_tuple_bij tagged_tuple_bseq_bij : core.

#[non_forgetful_inheritance]
HB.instance Definition _ n (T : finType) := isFinite.Build (n.-bseq T)
  (pcan_enumP (can_pcan (@bseq_tagged_tupleK n T))).

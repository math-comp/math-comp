(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

(******************************************************************************)
(*    The basic theory of paths over an eqType; this file is essentially a    *)
(* complement to seq.v. Paths are non-empty sequences that obey a progression *)
(* relation. They are passed around in three parts: the head and tail of the  *)
(* sequence, and a proof of a (boolean) predicate asserting the progression.  *)
(* This "exploded" view is rarely embarrassing, as the first two parameters   *)
(* are usually inferred from the type of the third; on the contrary, it saves *)
(* the hassle of constantly constructing and destructing a dependent record.  *)
(*    We define similarly cycles, for which we allow the empty sequence,      *)
(* which represents a non-rooted empty cycle; by contrast, the "empty" path   *)
(* from a point x is the one-item sequence containing only x.                 *)
(*   We allow duplicates; uniqueness, if desired (as is the case for several  *)
(* geometric constructions), must be asserted separately. We do provide       *)
(* shorthand, but only for cycles, because the equational properties of       *)
(* "path" and "uniq" are unfortunately incompatible (esp. wrt "cat").         *)
(*    We define notations for the common cases of function paths, where the   *)
(* progress relation is actually a function. In detail:                       *)
(*   path e x p == x :: p is an e-path [:: x_0; x_1; ... ; x_n], i.e., we     *)
(*                 have e x_i x_{i+1} for all i < n. The path x :: p starts   *)
(*                 at x and ends at last x p.                                 *)
(*  fpath f x p == x :: p is an f-path, where f is a function, i.e., p is of  *)
(*                 the form [:: f x; f (f x); ...]. This is just a notation   *)
(*                 for path (frel f) x p.                                     *)
(*   sorted e s == s is an e-sorted sequence: either s = [::], or s = x :: p  *)
(*                 is an e-path (this is often used with e = leq or ltn).     *)
(*    cycle e c == c is an e-cycle: either c = [::], or c = x :: p with       *)
(*                 x :: (rcons p x) an e-path.                                *)
(*   fcycle f c == c is an f-cycle, for a function f.                         *)
(* traject f x n == the f-path of size n starting at x                        *)
(*              := [:: x; f x; ...; iter n.-1 f x]                            *)
(* looping f x n == the f-paths of size greater than n starting at x loop     *)
(*                 back, or, equivalently, traject f x n contains all         *)
(*                 iterates of f at x.                                        *)
(* merge e s1 s2 == the e-sorted merge of sequences s1 and s2: this is always *)
(*                 a permutation of s1 ++ s2, and is e-sorted when s1 and s2  *)
(*                 are and e is total.                                        *)
(*     sort e s == a permutation of the sequence s, that is e-sorted when e   *)
(*                 is total (computed by a merge sort with the merge function *)
(*                 above).  This sort function is also designed to be stable. *)
(*   mem2 s x y == x, then y occur in the sequence (path) s; this is          *)
(*                 non-strict: mem2 s x x = (x \in s).                        *)
(*     next c x == the successor of the first occurrence of x in the sequence *)
(*                 c (viewed as a cycle), or x if x \notin c.                 *)
(*     prev c x == the predecessor of the first occurrence of x in the        *)
(*                 sequence c (viewed as a cycle), or x if x \notin c.        *)
(*    arc c x y == the sub-arc of the sequence c (viewed as a cycle) starting *)
(*                 at the first occurrence of x in c, and ending just before  *)
(*                 the next occurrence of y (in cycle order); arc c x y       *)
(*                 returns an unspecified sub-arc of c if x and y do not both *)
(*                 occur in c.                                                *)
(*  ucycle e c <-> ucycleb e c (ucycle e c is a Coercion target of type Prop) *)
(* ufcycle f c <-> c is a simple f-cycle, for a function f.                   *)
(*  shorten x p == the tail a duplicate-free subpath of x :: p with the same  *)
(*                 endpoints (x and last x p), obtained by removing all loops *)
(*                 from x :: p.                                               *)
(* rel_base e e' h b <-> the function h is a functor from relation e to       *)
(*                 relation e', EXCEPT at points whose image under h satisfy  *)
(*                 the "base" predicate b:                                    *)
(*                    e' (h x) (h y) = e x y UNLESS b (h x) holds             *)
(*                 This is the statement of the side condition of the path    *)
(*                 functorial mapping lemma map_path.                         *)
(* fun_base f f' h b <-> the function h is a functor from function f to f',   *)
(*                 except at the preimage of predicate b under h.             *)
(* We also provide three segmenting dependently-typed lemmas (splitP, splitPl *)
(* and splitPr) whose elimination split a path x0 :: p at an internal point x *)
(* as follows:                                                                *)
(*  - splitP applies when x \in p; it replaces p with (rcons p1 x ++ p2), so  *)
(*    that x appears explicitly at the end of the left part. The elimination  *)
(*    of splitP will also simultaneously replace take (index x p) with p1 and *)
(*    drop (index x p).+1 p with p2.                                          *)
(*  - splitPl applies when x \in x0 :: p; it replaces p with p1 ++ p2 and     *)
(*    simultaneously generates an equation x = last x0 p1.                    *)
(*  - splitPr applies when x \in p; it replaces p with (p1 ++ x :: p2), so x  *)
(*    appears explicitly at the start of the right part.                      *)
(* The parts p1 and p2 are computed using index/take/drop in all cases, but   *)
(* only splitP attempts to substitute the explicit values. The substitution   *)
(* of p can be deferred using the dependent equation generation feature of    *)
(* ssreflect, e.g.: case/splitPr def_p: {1}p / x_in_p => [p1 p2] generates    *)
(* the equation p = p1 ++ p2 instead of performing the substitution outright. *)
(*   Similarly, eliminating the loop removal lemma shortenP simultaneously    *)
(* replaces shorten e x p with a fresh constant p', and last x p with         *)
(* last x p'.                                                                 *)
(*   Note that although all "path" functions actually operate on the          *)
(* underlying sequence, we provide a series of lemmas that define their       *)
(* interaction with the path and cycle predicates, e.g., the cat_path equation*)
(* can be used to split the path predicate after splitting the underlying     *)
(* sequence.                                                                  *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Paths.

Variables (n0 : nat) (T : Type).

Section Path.

Variables (x0_cycle : T) (e : rel T).

Fixpoint path x (p : seq T) :=
  if p is y :: p' then e x y && path y p' else true.

Lemma cat_path x p1 p2 : path x (p1 ++ p2) = path x p1 && path (last x p1) p2.
Proof. by elim: p1 x => [|y p1 Hrec] x //=; rewrite Hrec -!andbA. Qed.

Lemma rcons_path x p y : path x (rcons p y) = path x p && e (last x p) y.
Proof. by rewrite -cats1 cat_path /= andbT. Qed.

Lemma take_path x p i : path x p -> path x (take i p).
Proof. elim: p x i => [//| x p] IHp x' [//| i] /= /andP[-> ?]; exact: IHp. Qed.

Lemma pathP x p x0 :
  reflect (forall i, i < size p -> e (nth x0 (x :: p) i) (nth x0 p i))
          (path x p).
Proof.
elim: p x => [|y p IHp] x /=; first by left.
apply: (iffP andP) => [[e_xy /IHp e_p [] //] | e_p].
by split; [apply: (e_p 0) | apply/(IHp y) => i; apply: e_p i.+1].
Qed.

Definition cycle p := if p is x :: p' then path x (rcons p' x) else true.

Lemma cycle_path p : cycle p = path (last x0_cycle p) p.
Proof. by case: p => //= x p; rewrite rcons_path andbC. Qed.

Lemma cycle_catC p q : cycle (p ++ q) = cycle (q ++ p).
Proof.
case: p q => [|x p] [|y q]; rewrite /= ?cats0 //=.
by rewrite !rcons_path !cat_path !last_cat /= -!andbA; do !bool_congr.
Qed.

Lemma rot_cycle p : cycle (rot n0 p) = cycle p.
Proof. by rewrite cycle_catC cat_take_drop. Qed.

Lemma rotr_cycle p : cycle (rotr n0 p) = cycle p.
Proof. by rewrite -rot_cycle rotrK. Qed.

Definition sorted s := if s is x :: s' then path x s' else true.

Lemma sortedP s x :
  reflect (forall i, i.+1 < size s -> e (nth x s i) (nth x s i.+1)) (sorted s).
Proof. by case: s => *; [constructor|apply: (iffP (pathP _ _ _)); apply]. Qed.

Lemma path_sorted x s : path x s -> sorted s.
Proof. by case: s => //= y s /andP[]. Qed.

Lemma path_min_sorted x s : all (e x) s -> path x s = sorted s.
Proof. by case: s => //= y s /andP [->]. Qed.

Lemma pairwise_sorted s : pairwise e s -> sorted s.
Proof. by elim: s => //= x s IHs /andP[/path_min_sorted -> /IHs]. Qed.

Lemma sorted_cat_cons s1 x s2 :
  sorted (s1 ++ x :: s2) = sorted (rcons s1 x) && path x s2.
Proof.
by case: s1 => [ | e1 s1] //=; rewrite -cat_rcons cat_path last_rcons.
Qed.

End Path.

Section PathEq.

Variables (e e' : rel T).

Lemma rev_path x p :
  path e (last x p) (rev (belast x p)) = path (fun z => e^~ z) x p.
Proof.
elim: p x => //= y p IHp x; rewrite rev_cons rcons_path -{}IHp andbC.
by rewrite -(last_cons x) -rev_rcons -lastI rev_cons last_rcons.
Qed.

Lemma rev_cycle p : cycle e (rev p) = cycle (fun z => e^~ z) p.
Proof.
case: p => //= x p; rewrite -rev_path last_rcons belast_rcons rev_cons.
by rewrite -[in LHS]cats1 cycle_catC.
Qed.

Lemma rev_sorted p : sorted e (rev p) = sorted (fun z => e^~ z) p.
Proof. by case: p => //= x p; rewrite -rev_path lastI rev_rcons. Qed.

Lemma path_relI x s :
  path [rel x y | e x y && e' x y] x s = path e x s && path e' x s.
Proof. by elim: s x => //= y s IHs x; rewrite andbACA IHs. Qed.

Lemma cycle_relI s :
  cycle [rel x y | e x y && e' x y] s = cycle e s && cycle e' s.
Proof. by case: s => [|? ?]; last apply: path_relI. Qed.

Lemma sorted_relI s :
  sorted [rel x y | e x y && e' x y] s = sorted e s && sorted e' s.
Proof. by case: s; last apply: path_relI. Qed.

End PathEq.

Section SubPath_in.

Variable (P : {pred T}) (e e' : rel T).
Hypothesis (ee' : {in P &, subrel e e'}).

Lemma sub_in_path x s : all P (x :: s) -> path e x s -> path e' x s.
Proof.
by elim: s x => //= y s ihs x /and3P [? ? ?] /andP [/ee' -> //]; apply/ihs/andP.
Qed.

Lemma sub_in_cycle s : all P s -> cycle e s -> cycle e' s.
Proof.
case: s => //= x s /andP [Px Ps].
by apply: sub_in_path; rewrite /= all_rcons Px.
Qed.

Lemma sub_in_sorted s : all P s -> sorted e s -> sorted e' s.
Proof. by case: s => //; apply: sub_in_path. Qed.

End SubPath_in.

Section EqPath_in.

Variable (P : {pred T}) (e e' : rel T).
Hypothesis (ee' : {in P &, e =2 e'}).

Let e_e' : {in P &, subrel e e'}. Proof. by move=> ? ? ? ?; rewrite ee'. Qed.
Let e'_e : {in P &, subrel e' e}. Proof. by move=> ? ? ? ?; rewrite ee'. Qed.

Lemma eq_in_path x s : all P (x :: s) -> path e x s = path e' x s.
Proof. by move=> Pxs; apply/idP/idP; apply: sub_in_path Pxs. Qed.

Lemma eq_in_cycle s : all P s -> cycle e s = cycle e' s.
Proof. by move=> Ps; apply/idP/idP; apply: sub_in_cycle Ps. Qed.

Lemma eq_in_sorted s : all P s -> sorted e s = sorted e' s.
Proof. by move=> Ps; apply/idP/idP; apply: sub_in_sorted Ps. Qed.

End EqPath_in.

Section SubPath.

Variables e e' : rel T.

Lemma sub_path : subrel e e' -> forall x p, path e x p -> path e' x p.
Proof. by move=> ? ? ?; apply/sub_in_path/all_predT; apply: in2W. Qed.

Lemma sub_cycle : subrel e e' -> subpred (cycle e) (cycle e').
Proof. by move=> ee' [] // ? ?; apply: sub_path. Qed.

Lemma sub_sorted : subrel e e' -> subpred (sorted e) (sorted e').
Proof. by move=> ee' [] //=; apply: sub_path. Qed.

Lemma eq_path : e =2 e' -> path e =2 path e'.
Proof. by move=> ? ? ?; apply/eq_in_path/all_predT; apply: in2W. Qed.

Lemma eq_cycle : e =2 e' -> cycle e =1 cycle e'.
Proof. by move=> ee' [] // ? ?; apply: eq_path. Qed.

Lemma eq_sorted : e =2 e' -> sorted e =1 sorted e'.
Proof. by move=> ee' [] // ? ?; apply: eq_path. Qed.

End SubPath.

Section Transitive_in.

Variables (P : {pred T}) (leT : rel T).

Lemma order_path_min_in x s :
  {in P & &, transitive leT} -> all P (x :: s) -> path leT x s -> all (leT x) s.
Proof.
move=> leT_tr; elim: s => //= y s ihs /and3P [Px Py Ps] /andP [xy ys].
rewrite xy {}ihs ?Px //=; case: s Ps ys => //= z s /andP [Pz Ps] /andP [yz ->].
by rewrite (leT_tr _ _ _ Py Px Pz).
Qed.

Hypothesis leT_tr : {in P & &, transitive leT}.

Lemma path_sorted_inE x s :
  all P (x :: s) -> path leT x s = all (leT x) s && sorted leT s.
Proof.
move=> Pxs; apply/idP/idP => [xs|/andP[/path_min_sorted<-//]].
by rewrite (order_path_min_in leT_tr) //; apply: path_sorted xs.
Qed.

Lemma sorted_pairwise_in s : all P s -> sorted leT s = pairwise leT s.
Proof.
by elim: s => //= x s IHs /andP [Px Ps]; rewrite path_sorted_inE ?IHs //= Px.
Qed.

Lemma path_pairwise_in x s :
  all P (x :: s) -> path leT x s = pairwise leT (x :: s).
Proof. by move=> Pxs; rewrite -sorted_pairwise_in. Qed.

Lemma cat_sorted2 s s' : sorted leT (s ++ s') -> sorted leT s * sorted leT s'.
Proof. by case: s => //= x s; rewrite cat_path => /andP[-> /path_sorted]. Qed.

Lemma sorted_mask_in m s : all P s -> sorted leT s -> sorted leT (mask m s).
Proof.
by move=> Ps; rewrite !sorted_pairwise_in ?all_mask //; exact: pairwise_mask.
Qed.

Lemma sorted_filter_in a s : all P s -> sorted leT s -> sorted leT (filter a s).
Proof. rewrite filter_mask; exact: sorted_mask_in. Qed.

Lemma path_mask_in x m s :
  all P (x :: s) -> path leT x s -> path leT x (mask m s).
Proof. exact/(sorted_mask_in (true :: m)). Qed.

Lemma path_filter_in x a s :
  all P (x :: s) -> path leT x s -> path leT x (filter a s).
Proof. by move=> Pxs; rewrite filter_mask; exact: path_mask_in. Qed.

Lemma sorted_ltn_nth_in x0 s : all P s -> sorted leT s ->
  {in [pred n | n < size s] &, {homo nth x0 s : i j / i < j >-> leT i j}}.
Proof. by move=> Ps; rewrite sorted_pairwise_in //; apply/pairwiseP. Qed.

Hypothesis leT_refl : {in P, reflexive leT}.

Lemma sorted_leq_nth_in x0 s : all P s -> sorted leT s ->
  {in [pred n | n < size s] &, {homo nth x0 s : i j / i <= j >-> leT i j}}.
Proof.
move=> Ps s_sorted x y xs ys; rewrite leq_eqVlt=> /predU1P[->|].
  exact/leT_refl/all_nthP.
exact: sorted_ltn_nth_in.
Qed.

End Transitive_in.

Section Transitive.

Variable (leT : rel T).

Lemma order_path_min x s : transitive leT -> path leT x s -> all (leT x) s.
Proof.
by move=> leT_tr; apply/order_path_min_in/all_predT => //; apply: in3W.
Qed.

Hypothesis leT_tr : transitive leT.

Lemma path_le x x' s : leT x x' -> path leT x' s -> path leT x s.
Proof.
by case: s => [//| x'' s xlex' /= /andP[x'lex'' ->]]; rewrite (leT_tr xlex').
Qed.

Let leT_tr' : {in predT & &, transitive leT}. Proof. exact: in3W. Qed.

Lemma path_sortedE x s : path leT x s = all (leT x) s && sorted leT s.
Proof. exact/path_sorted_inE/all_predT. Qed.

Lemma sorted_pairwise s : sorted leT s = pairwise leT s.
Proof. exact/sorted_pairwise_in/all_predT. Qed.

Lemma path_pairwise x s : path leT x s = pairwise leT (x :: s).
Proof. exact/path_pairwise_in/all_predT. Qed.

Lemma sorted_mask m s : sorted leT s -> sorted leT (mask m s).
Proof. exact/sorted_mask_in/all_predT. Qed.

Lemma sorted_filter a s : sorted leT s -> sorted leT (filter a s).
Proof. exact/sorted_filter_in/all_predT. Qed.

Lemma path_mask x m s : path leT x s -> path leT x (mask m s).
Proof. exact/path_mask_in/all_predT. Qed.

Lemma path_filter x a s : path leT x s -> path leT x (filter a s).
Proof. exact/path_filter_in/all_predT. Qed.

Lemma sorted_ltn_nth x0 s : sorted leT s ->
  {in [pred n | n < size s] &, {homo nth x0 s : i j / i < j >-> leT i j}}.
Proof. exact/sorted_ltn_nth_in/all_predT. Qed.

Hypothesis leT_refl : reflexive leT.

Lemma sorted_leq_nth x0 s : sorted leT s ->
  {in [pred n | n < size s] &, {homo nth x0 s : i j / i <= j >-> leT i j}}.
Proof. exact/sorted_leq_nth_in/all_predT. Qed.

Lemma take_sorted n s : sorted leT s -> sorted leT (take n s).
Proof. by rewrite -[s in sorted _ s](cat_take_drop n) => /cat_sorted2[]. Qed.

Lemma drop_sorted n s : sorted leT s -> sorted leT (drop n s).
Proof. by rewrite -[s in sorted _ s](cat_take_drop n) => /cat_sorted2[]. Qed.

End Transitive.

End Paths.

Arguments pathP {T e x p}.
Arguments sortedP {T e s}.
Arguments path_sorted {T e x s}.
Arguments path_min_sorted {T e x s}.
Arguments order_path_min_in {T P leT x s}.
Arguments path_sorted_inE {T P leT} leT_tr {x s}.
Arguments sorted_pairwise_in {T P leT} leT_tr {s}.
Arguments path_pairwise_in {T P leT} leT_tr {x s}.
Arguments sorted_mask_in {T P leT} leT_tr {m s}.
Arguments sorted_filter_in {T P leT} leT_tr {a s}.
Arguments path_mask_in {T P leT} leT_tr {x m s}.
Arguments path_filter_in {T P leT} leT_tr {x a s}.
Arguments sorted_ltn_nth_in {T P leT} leT_tr x0 {s}.
Arguments sorted_leq_nth_in {T P leT} leT_tr leT_refl x0 {s}.
Arguments order_path_min {T leT x s}.
Arguments path_sortedE {T leT} leT_tr x s.
Arguments sorted_pairwise {T leT} leT_tr s.
Arguments path_pairwise {T leT} leT_tr x s.
Arguments sorted_mask {T leT} leT_tr m {s}.
Arguments sorted_filter {T leT} leT_tr a {s}.
Arguments path_mask {T leT} leT_tr {x} m {s}.
Arguments path_filter {T leT} leT_tr {x} a {s}.
Arguments sorted_ltn_nth {T leT} leT_tr x0 {s}.
Arguments sorted_leq_nth {T leT} leT_tr leT_refl x0 {s}.

Section HomoPath.

Variables (T T' : Type) (P : {pred T}) (f : T -> T') (e : rel T) (e' : rel T').

Lemma path_map x s : path e' (f x) (map f s) = path (relpre f e') x s.
Proof. by elim: s x => //= y s <-. Qed.

Lemma cycle_map s : cycle e' (map f s) = cycle (relpre f e') s.
Proof. by case: s => //= ? ?; rewrite -map_rcons path_map. Qed.

Lemma sorted_map s : sorted e' (map f s) = sorted (relpre f e') s.
Proof. by case: s; last apply: path_map. Qed.

Lemma homo_path_in x s : {in P &, {homo f : x y / e x y >-> e' x y}} ->
  all P (x :: s) -> path e x s -> path e' (f x) (map f s).
Proof. by move=> f_mono; rewrite path_map; apply: sub_in_path. Qed.

Lemma homo_cycle_in s : {in P &, {homo f : x y / e x y >-> e' x y}} ->
  all P s -> cycle e s -> cycle e' (map f s).
Proof. by move=> f_mono; rewrite cycle_map; apply: sub_in_cycle. Qed.

Lemma homo_sorted_in s : {in P &, {homo f : x y / e x y >-> e' x y}} ->
  all P s -> sorted e s -> sorted e' (map f s).
Proof. by move=> f_mono; rewrite sorted_map; apply: sub_in_sorted. Qed.

Lemma mono_path_in x s : {in P &, {mono f : x y / e x y >-> e' x y}} ->
  all P (x :: s) -> path e' (f x) (map f s) = path e x s.
Proof. by move=> f_mono; rewrite path_map; apply: eq_in_path. Qed.

Lemma mono_cycle_in s : {in P &, {mono f : x y / e x y >-> e' x y}} ->
  all P s -> cycle e' (map f s) = cycle e s.
Proof. by move=> f_mono; rewrite cycle_map; apply: eq_in_cycle. Qed.

Lemma mono_sorted_in s : {in P &, {mono f : x y / e x y >-> e' x y}} ->
  all P s -> sorted e' (map f s) = sorted e s.
Proof. by case: s => // x s; apply: mono_path_in. Qed.

Lemma homo_path x s : {homo f : x y / e x y >-> e' x y} ->
  path e x s -> path e' (f x) (map f s).
Proof. by move=> f_homo; rewrite path_map; apply: sub_path. Qed.

Lemma homo_cycle : {homo f : x y / e x y >-> e' x y} ->
  {homo map f : s / cycle e s >-> cycle e' s}.
Proof. by move=> f_homo s hs; rewrite cycle_map (sub_cycle _ hs). Qed.

Lemma homo_sorted : {homo f : x y / e x y >-> e' x y} ->
  {homo map f : s / sorted e s >-> sorted e' s}.
Proof. by move/homo_path => ? []. Qed.

Lemma mono_path x s : {mono f : x y / e x y >-> e' x y} ->
  path e' (f x) (map f s) = path e x s.
Proof. by move=> f_mon; rewrite path_map; apply: eq_path. Qed.

Lemma mono_cycle : {mono f : x y / e x y >-> e' x y} ->
  {mono map f : s / cycle e s >-> cycle e' s}.
Proof. by move=> ? ?; rewrite cycle_map; apply: eq_cycle. Qed.

Lemma mono_sorted : {mono f : x y / e x y >-> e' x y} ->
  {mono map f : s / sorted e s >-> sorted e' s}.
Proof. by move=> f_mon [] //= x s; apply: mono_path. Qed.

End HomoPath.

Arguments path_map {T T' f e'}.
Arguments cycle_map {T T' f e'}.
Arguments sorted_map {T T' f e'}.
Arguments homo_path_in {T T' P f e e' x s}.
Arguments homo_cycle_in {T T' P f e e' s}.
Arguments homo_sorted_in {T T' P f e e' s}.
Arguments mono_path_in {T T' P f e e' x s}.
Arguments mono_cycle_in {T T' P f e e' s}.
Arguments mono_sorted_in {T T' P f e e' s}.
Arguments homo_path {T T' f e e' x s}.
Arguments homo_cycle {T T' f e e'}.
Arguments homo_sorted {T T' f e e'}.
Arguments mono_path {T T' f e e' x s}.
Arguments mono_cycle {T T' f e e'}.
Arguments mono_sorted {T T' f e e'}.

Section CycleAll2Rel.

Lemma cycle_all2rel (T : Type) (leT : rel T) :
  transitive leT -> forall s, cycle leT s = all2rel leT s.
Proof.
move=> leT_tr; elim=> //= x s IHs.
rewrite allrel_cons2 -{}IHs // (path_sortedE leT_tr) /= all_rcons -rev_sorted.
rewrite rev_rcons /= (path_sortedE (rev_trans leT_tr)) all_rev !andbA.
case: (boolP (leT x x && _ && _)) => //=.
case: s => //= y s /and3P[/and3P[_ xy _] yx sx].
rewrite rev_sorted rcons_path /= (leT_tr _ _ _ _ xy) ?andbT //.
by case: (lastP s) sx => //= {}s z; rewrite all_rcons last_rcons => /andP [->].
Qed.

Lemma cycle_all2rel_in (T : Type) (P : {pred T}) (leT : rel T) :
  {in P & &, transitive leT} ->
  forall s, all P s -> cycle leT s = all2rel leT s.
Proof.
move=> /in3_sig leT_tr _ /all_sigP [s ->].
by rewrite cycle_map allrel_mapl allrel_mapr; apply: cycle_all2rel.
Qed.

End CycleAll2Rel.

Section PreInSuffix.

Variables (T : eqType) (e : rel T).
Implicit Type s : seq T.

Local Notation path := (path e).
Local Notation sorted := (sorted e).

Lemma prefix_path x s1 s2 : prefix s1 s2 -> path x s2 -> path x s1.
Proof. by rewrite prefixE => /eqP <-; exact: take_path. Qed.

Lemma prefix_sorted s1 s2 : prefix s1 s2 -> sorted s2 -> sorted s1.
Proof. by rewrite prefixE => /eqP <-; exact: take_sorted. Qed.

Lemma infix_sorted s1 s2 : infix s1 s2 -> sorted s2 -> sorted s1.
Proof. by rewrite infixE => /eqP <- ?; apply/take_sorted/drop_sorted. Qed.

Lemma suffix_sorted s1 s2 : suffix s1 s2 -> sorted s2 -> sorted s1.
Proof. by rewrite suffixE => /eqP <-; exact: drop_sorted. Qed.

End PreInSuffix.

Section EqSorted.

Variables (T : eqType) (leT : rel T).
Implicit Type s : seq T.

Local Notation path := (path leT).
Local Notation sorted := (sorted leT).

Lemma subseq_path_in x s1 s2 :
  {in x :: s2 & &, transitive leT} -> subseq s1 s2 -> path x s2 -> path x s1.
Proof. by move=> tr /subseqP [m _ ->]; apply/(path_mask_in tr). Qed.

Lemma subseq_sorted_in s1 s2 :
  {in s2 & &, transitive leT} -> subseq s1 s2 -> sorted s2 -> sorted s1.
Proof. by move=> tr /subseqP [m _ ->]; apply/(sorted_mask_in tr). Qed.

Lemma sorted_ltn_index_in s : {in s & &, transitive leT} -> sorted s ->
  {in s &, forall x y, index x s < index y s -> leT x y}.
Proof.
case: s => // x0 s' leT_tr s_sorted x y xs ys.
move/(sorted_ltn_nth_in leT_tr x0 (allss (_ :: _)) s_sorted).
by rewrite ?nth_index ?[_ \in gtn _]index_mem //; apply.
Qed.

Lemma sorted_leq_index_in s :
  {in s & &, transitive leT} -> {in s, reflexive leT} -> sorted s ->
  {in s &, forall x y, index x s <= index y s -> leT x y}.
Proof.
case: s => // x0 s' leT_tr leT_refl s_sorted x y xs ys.
move/(sorted_leq_nth_in leT_tr leT_refl x0 (allss (_ :: _)) s_sorted).
by rewrite ?nth_index ?[_ \in gtn _]index_mem //; apply.
Qed.

Hypothesis leT_tr : transitive leT.

Lemma subseq_path x s1 s2 : subseq s1 s2 -> path x s2 -> path x s1.
Proof. by apply: subseq_path_in; apply: in3W. Qed.

Lemma subseq_sorted s1 s2 : subseq s1 s2 -> sorted s2 -> sorted s1.
Proof. by apply: subseq_sorted_in; apply: in3W. Qed.

Lemma sorted_uniq : irreflexive leT -> forall s, sorted s -> uniq s.
Proof. by move=> irr s; rewrite sorted_pairwise //; apply/pairwise_uniq. Qed.

Lemma sorted_eq : antisymmetric leT ->
  forall s1 s2, sorted s1 -> sorted s2 -> perm_eq s1 s2 -> s1 = s2.
Proof.
by move=> leT_asym s1 s2; rewrite !sorted_pairwise //; apply: pairwise_eq.
Qed.

Lemma irr_sorted_eq : irreflexive leT ->
  forall s1 s2, sorted s1 -> sorted s2 -> s1 =i s2 -> s1 = s2.
Proof.
move=> leT_irr s1 s2 s1_sort s2_sort eq_s12.
have: antisymmetric leT.
  by move=> m n /andP[? ltnm]; case/idP: (leT_irr m); apply: leT_tr ltnm.
by move/sorted_eq; apply=> //; apply: uniq_perm => //; apply: sorted_uniq.
Qed.

Lemma sorted_ltn_index s :
  sorted s -> {in s &, forall x y, index x s < index y s -> leT x y}.
Proof.
case: s => // x0 s' s_sorted x y xs ys /(sorted_ltn_nth leT_tr x0 s_sorted).
by rewrite ?nth_index ?[_ \in gtn _]index_mem //; apply.
Qed.

Lemma undup_path x s : path x s -> path x (undup s).
Proof. exact/subseq_path/undup_subseq. Qed.

Lemma undup_sorted s : sorted s -> sorted (undup s).
Proof. exact/subseq_sorted/undup_subseq. Qed.

Hypothesis leT_refl : reflexive leT.

Lemma sorted_leq_index s :
  sorted s -> {in s &, forall x y, index x s <= index y s -> leT x y}.
Proof.
case: s => // x0 s' s_sorted x y xs ys.
move/(sorted_leq_nth leT_tr leT_refl x0 s_sorted).
by rewrite ?nth_index ?[_ \in gtn _]index_mem //; apply.
Qed.

End EqSorted.

Arguments sorted_ltn_index_in {T leT s} leT_tr s_sorted.
Arguments sorted_leq_index_in {T leT s} leT_tr leT_refl s_sorted.
Arguments sorted_ltn_index {T leT} leT_tr {s}.
Arguments sorted_leq_index {T leT} leT_tr leT_refl {s}.

Section EqSorted_in.

Variables (T : eqType) (leT : rel T).
Implicit Type s : seq T.

Lemma sorted_uniq_in s :
  {in s & &, transitive leT} -> {in s, irreflexive leT} ->
  sorted leT s -> uniq s.
Proof.
move=> /in3_sig leT_tr /in1_sig leT_irr; case/all_sigP: (allss s) => s' ->.
by rewrite sorted_map (map_inj_uniq val_inj); exact: sorted_uniq.
Qed.

Lemma sorted_eq_in s1 s2 :
  {in s1 & &, transitive leT} -> {in s1 &, antisymmetric leT} ->
  sorted leT s1 -> sorted leT s2 -> perm_eq s1 s2 -> s1 = s2.
Proof.
move=> /in3_sig leT_tr /in2_sig/(_ _ _ _)/val_inj leT_anti + + /[dup] s1s2.
have /all_sigP[s1' ->] := allss s1.
have /all_sigP[{s1s2}s2 ->] : all [in s1] s2 by rewrite -(perm_all _ s1s2).
by rewrite !sorted_map => ss1' ss2 /(perm_map_inj val_inj)/(sorted_eq leT_tr)->.
Qed.

Lemma irr_sorted_eq_in s1 s2 :
  {in s1 & &, transitive leT} -> {in s1, irreflexive leT} ->
  sorted leT s1 -> sorted leT s2 -> s1 =i s2 -> s1 = s2.
Proof.
move=> /in3_sig leT_tr /in1_sig leT_irr + + /[dup] s1s2.
have /all_sigP[s1' ->] := allss s1.
have /all_sigP[s2' ->] : all [in s1] s2 by rewrite -(eq_all_r s1s2).
rewrite !sorted_map => ss1' ss2' {}s1s2; congr map.
by apply: (irr_sorted_eq leT_tr) => // x; rewrite -!(mem_map val_inj).
Qed.

End EqSorted_in.

Section EqPath.

Variables (n0 : nat) (T : eqType) (e : rel T).
Implicit Type p : seq T.

Variant split x : seq T -> seq T -> seq T -> Type :=
  Split p1 p2 : split x (rcons p1 x ++ p2) p1 p2.

Lemma splitP p x (i := index x p) :
  x \in p -> split x p (take i p) (drop i.+1 p).
Proof. by rewrite -has_pred1 => /split_find[? ? ? /eqP->]; constructor. Qed.

Variant splitl x1 x : seq T -> Type :=
  Splitl p1 p2 of last x1 p1 = x : splitl x1 x (p1 ++ p2).

Lemma splitPl x1 p x : x \in x1 :: p -> splitl x1 x p.
Proof.
rewrite inE; case: eqP => [->| _ /splitP[]]; first by rewrite -(cat0s p).
by split; apply: last_rcons.
Qed.

Variant splitr x : seq T -> Type :=
  Splitr p1 p2 : splitr x (p1 ++ x :: p2).

Lemma splitPr p x : x \in p -> splitr x p.
Proof. by case/splitP=> p1 p2; rewrite cat_rcons. Qed.

Fixpoint next_at x y0 y p :=
  match p with
  | [::] => if x == y then y0 else x
  | y' :: p' => if x == y then y' else next_at x y0 y' p'
  end.

Definition next p x := if p is y :: p' then next_at x y y p' else x.

Fixpoint prev_at x y0 y p :=
  match p with
  | [::]     => if x == y0 then y else x
  | y' :: p' => if x == y' then y else prev_at x y0 y' p'
  end.

Definition prev p x := if p is y :: p' then prev_at x y y p' else x.

Lemma next_nth p x :
  next p x = if x \in p then
               if p is y :: p' then nth y p' (index x p) else x
             else x.
Proof.
case: p => //= y0 p.
elim: p {2 3 5}y0 => [|y' p IHp] y /=; rewrite (eq_sym y) inE;
  by case: ifP => // _; apply: IHp.
Qed.

Lemma prev_nth p x :
  prev p x = if x \in p then
               if p is y :: p' then nth y p (index x p') else x
             else x.
Proof.
case: p => //= y0 p; rewrite inE orbC.
elim: p {2 5}y0 => [|y' p IHp] y; rewrite /= ?inE // (eq_sym y').
by case: ifP => // _; apply: IHp.
Qed.

Lemma mem_next p x : (next p x \in p) = (x \in p).
Proof.
rewrite next_nth; case p_x: (x \in p) => //.
case: p (index x p) p_x => [|y0 p'] //= i _; rewrite inE.
have [lt_ip | ge_ip] := ltnP i (size p'); first by rewrite orbC mem_nth.
by rewrite nth_default ?eqxx.
Qed.

Lemma mem_prev p x : (prev p x \in p) = (x \in p).
Proof.
rewrite prev_nth; case p_x: (x \in p) => //; case: p => [|y0 p] // in p_x *.
by apply mem_nth; rewrite /= ltnS index_size.
Qed.

(* ucycleb is the boolean predicate, but ucycle is defined as a Prop *)
(* so that it can be used as a coercion target. *)
Definition ucycleb p := cycle e p && uniq p.
Definition ucycle p : Prop := cycle e p && uniq p.

(* Projections, used for creating local lemmas. *)
Lemma ucycle_cycle p : ucycle p -> cycle e p.
Proof. by case/andP. Qed.

Lemma ucycle_uniq p : ucycle p -> uniq p.
Proof. by case/andP. Qed.

Lemma next_cycle p x : cycle e p -> x \in p -> e x (next p x).
Proof.
case: p => //= y0 p; elim: p {1 3 5}y0 => [|z p IHp] y /=; rewrite inE.
  by rewrite andbT; case: (x =P y) => // ->.
by case/andP=> eyz /IHp; case: (x =P y) => // ->.
Qed.

Lemma prev_cycle p x : cycle e p -> x \in p -> e (prev p x) x.
Proof.
case: p => //= y0 p; rewrite inE orbC.
elim: p {1 5}y0 => [|z p IHp] y /=; rewrite ?inE.
  by rewrite andbT; case: (x =P y0) => // ->.
by case/andP=> eyz /IHp; case: (x =P z) => // ->.
Qed.

Lemma rot_ucycle p : ucycle (rot n0 p) = ucycle p.
Proof. by rewrite /ucycle rot_uniq rot_cycle. Qed.

Lemma rotr_ucycle p : ucycle (rotr n0 p) = ucycle p.
Proof. by rewrite /ucycle rotr_uniq rotr_cycle. Qed.

(* The "appears no later" partial preorder defined by a path. *)

Definition mem2 p x y := y \in drop (index x p) p.

Lemma mem2l p x y : mem2 p x y -> x \in p.
Proof.
by rewrite /mem2 -!index_mem size_drop ltn_subRL; apply/leq_ltn_trans/leq_addr.
Qed.

Lemma mem2lf {p x y} : x \notin p -> mem2 p x y = false.
Proof. exact/contraNF/mem2l. Qed.

Lemma mem2r p x y : mem2 p x y -> y \in p.
Proof.
by rewrite -[in y \in p](cat_take_drop (index x p) p) mem_cat orbC /mem2 => ->.
Qed.

Lemma mem2rf {p x y} : y \notin p -> mem2 p x y = false.
Proof. exact/contraNF/mem2r. Qed.

Lemma mem2_cat p1 p2 x y :
  mem2 (p1 ++ p2) x y = mem2 p1 x y || mem2 p2 x y || (x \in p1) && (y \in p2).
Proof.
rewrite [LHS]/mem2 index_cat fun_if if_arg !drop_cat addKn.
case: ifPn => [p1x | /mem2lf->]; last by rewrite ltnNge leq_addr orbF.
by rewrite index_mem p1x mem_cat -orbA (orb_idl (@mem2r _ _ _)).
Qed.

Lemma mem2_splice p1 p3 x y p2 :
  mem2 (p1 ++ p3) x y -> mem2 (p1 ++ p2 ++ p3) x y.
Proof.
by rewrite !mem2_cat mem_cat andb_orr orbC => /or3P[]->; rewrite ?orbT.
Qed.

Lemma mem2_splice1 p1 p3 x y z :
  mem2 (p1 ++ p3) x y -> mem2 (p1 ++ z :: p3) x y.
Proof. exact: mem2_splice [::z]. Qed.

Lemma mem2_cons x p y z :
  mem2 (x :: p) y z = (if x == y then z \in x :: p else mem2 p y z).
Proof. by rewrite [LHS]/mem2 /=; case: ifP. Qed.

Lemma mem2_seq1 x y z : mem2 [:: x] y z = (y == x) && (z == x).
Proof. by rewrite mem2_cons eq_sym inE. Qed.

Lemma mem2_last y0 p x : mem2 p x (last y0 p) = (x \in p).
Proof.
apply/idP/idP; first exact: mem2l; rewrite -index_mem /mem2 => p_x.
by rewrite -nth_last -(subnKC p_x) -nth_drop mem_nth // size_drop subnSK.
Qed.

Lemma mem2l_cat {p1 p2 x} : x \notin p1 -> mem2 (p1 ++ p2) x =1 mem2 p2 x.
Proof. by move=> p1'x y; rewrite mem2_cat (negPf p1'x) mem2lf ?orbF. Qed.

Lemma mem2r_cat {p1 p2 x y} : y \notin p2 -> mem2 (p1 ++ p2) x y = mem2 p1 x y.
Proof.
by move=> p2'y; rewrite mem2_cat (negPf p2'y) -orbA orbC andbF mem2rf.
Qed.

Lemma mem2lr_splice {p1 p2 p3 x y} :
  x \notin p2 -> y \notin p2 -> mem2 (p1 ++ p2 ++ p3) x y = mem2 (p1 ++ p3) x y.
Proof.
move=> p2'x p2'y; rewrite catA !mem2_cat !mem_cat.
by rewrite (negPf p2'x) (negPf p2'y) (mem2lf p2'x) andbF !orbF.
Qed.

Lemma mem2E s x y :
  mem2 s x y = subseq (if x == y then [:: x] else [:: x; y]) s.
Proof.
elim: s => [| h s]; first by case: ifP.
rewrite mem2_cons => ->.
do 2 rewrite inE (fun_if subseq) !if_arg !sub1seq /=.
by have [->|] := eqVneq; case: eqVneq.
Qed.

Variant split2r x y : seq T -> Type :=
  Split2r p1 p2 of y \in x :: p2 : split2r x y (p1 ++ x :: p2).

Lemma splitP2r p x y : mem2 p x y -> split2r x y p.
Proof.
move=> pxy; have px := mem2l pxy.
have:= pxy; rewrite /mem2 (drop_nth x) ?index_mem ?nth_index //.
by case/splitP: px => p1 p2; rewrite cat_rcons.
Qed.

Fixpoint shorten x p :=
  if p is y :: p' then
    if x \in p then shorten x p' else y :: shorten y p'
  else [::].

Variant shorten_spec x p : T -> seq T -> Type :=
   ShortenSpec p' of path e x p' & uniq (x :: p') & {subset p' <= p} :
     shorten_spec x p (last x p') p'.

Lemma shortenP x p : path e x p -> shorten_spec x p (last x p) (shorten x p).
Proof.
move=> e_p; have: x \in x :: p by apply: mem_head.
elim: p x {1 3 5}x e_p => [|y2 p IHp] x y1.
  by rewrite mem_seq1 => _ /eqP->.
rewrite inE orbC /= => /andP[ey12 {}/IHp IHp].
case: ifPn => [y2p_x _ | not_y2p_x /eqP def_x].
  have [p' e_p' Up' p'p] := IHp _ y2p_x.
  by split=> // y /p'p; apply: predU1r.
have [p' e_p' Up' p'p] := IHp y2 (mem_head y2 p).
have{} p'p z: z \in y2 :: p' -> z \in y2 :: p.
  by rewrite !inE; case: (z == y2) => // /p'p.
rewrite -(last_cons y1) def_x; split=> //=; first by rewrite ey12.
by rewrite (contra (p'p y1)) -?def_x.
Qed.

End EqPath.

(* Ordered paths and sorting. *)

Section SortSeq.

Variables (T : Type) (leT : rel T).

Fixpoint merge s1 :=
  if s1 is x1 :: s1' then
    let fix merge_s1 s2 :=
      if s2 is x2 :: s2' then
        if leT x1 x2 then x1 :: merge s1' s2 else x2 :: merge_s1 s2'
      else s1 in
    merge_s1
  else id.

Arguments merge !s1 !s2 : rename.

Fixpoint merge_sort_push s1 ss :=
  match ss with
  | [::] :: ss' | [::] as ss' => s1 :: ss'
  | s2 :: ss' => [::] :: merge_sort_push (merge s2 s1) ss'
  end.

Fixpoint merge_sort_pop s1 ss :=
  if ss is s2 :: ss' then merge_sort_pop (merge s2 s1) ss' else s1.

Fixpoint merge_sort_rec ss s :=
  if s is [:: x1, x2 & s'] then
    let s1 := if leT x1 x2 then [:: x1; x2] else [:: x2; x1] in
    merge_sort_rec (merge_sort_push s1 ss) s'
  else merge_sort_pop s ss.

Definition sort := merge_sort_rec [::].

(* The following definition `sort_rec1` is an auxiliary function for          *)
(* inductive reasoning on `sort`. One can rewrite `sort le s` to              *)
(* `sort_rec1 le [::] s` by `sortE` and apply the simple structural induction *)
(* on `s` to reason about it.                                                 *)
Fixpoint sort_rec1 ss s :=
  if s is x :: s then sort_rec1 (merge_sort_push [:: x] ss) s else
  merge_sort_pop [::] ss.

Lemma sortE s : sort s = sort_rec1 [::] s.
Proof.
transitivity (sort_rec1 [:: nil] s); last by case: s.
rewrite /sort; move: [::] {2}_.+1 (ltnSn (size s)./2) => ss n.
by elim: n => // n IHn in ss s *; case: s => [|x [|y s]] //= /IHn->.
Qed.

Lemma count_merge (p : pred T) s1 s2 :
  count p (merge s1 s2) = count p (s1 ++ s2).
Proof.
rewrite count_cat; elim: s1 s2 => // x s1 IH1.
elim=> //= [|y s2 IH2]; first by rewrite addn0.
by case: leT; rewrite /= ?IH1 ?IH2 !addnA [_ + p y]addnAC [p x + p y]addnC.
Qed.

Lemma size_merge s1 s2 : size (merge s1 s2) = size (s1 ++ s2).
Proof. exact: (count_merge predT). Qed.

Lemma allrel_merge s1 s2 : allrel leT s1 s2 -> merge s1 s2 = s1 ++ s2.
Proof.
elim: s1 s2 => [|x s1 IHs1] [|y s2]; rewrite ?cats0 //=.
by rewrite allrel_consl /= -andbA => /and3P [-> _ /IHs1->].
Qed.

Lemma count_sort (p : pred T) s : count p (sort s) = count p s.
Proof.
rewrite sortE -[RHS]/(sumn [seq count p x | x <- [::]] + count p s).
elim: s [::] => [|x s ihs] ss.
  rewrite [LHS]/=; elim: ss [::] => //= s ss ihss t.
  by rewrite ihss count_merge count_cat addnCA addnA.
rewrite {}ihs -[in RHS]cat1s count_cat addnA; congr addn; rewrite addnC.
elim: {x s} ss [:: x] => [|[|x s] ss ihss] t //.
by rewrite [LHS]/= add0n ihss count_merge count_cat -addnA addnCA.
Qed.

Lemma pairwise_sort s : pairwise leT s -> sort s = s.
Proof.
pose catss := foldr (fun x => cat ^~ x) (Nil T).
rewrite -{1 3}[s]/(catss [::] ++ s) sortE; elim: s [::] => /= [|x s ihs] ss.
  elim: ss [::] => //= s ss ihss t; rewrite -catA => ssst.
  rewrite -ihss ?allrel_merge //; move: ssst; rewrite !pairwise_cat.
  by case/and4P.
rewrite (catA _ [:: _]) => ssxs.
suff x_ss_E: catss (merge_sort_push [:: x] ss) = catss ([:: x] :: ss).
  by rewrite -[catss _ ++ _]/(catss ([:: x] :: ss)) -x_ss_E ihs // x_ss_E.
move: ssxs; rewrite pairwise_cat => /and3P [_ + _].
elim: ss [:: x] => {x s ihs} //= -[|x s] ss ihss t h_pairwise;
  rewrite /= cats0 // allrel_merge ?ihss ?catA //.
by move: h_pairwise; rewrite -catA !pairwise_cat => /and4P [].
Qed.

Remark size_merge_sort_push s1 :
  let graded ss := forall i, size (nth [::] ss i) \in pred2 0 (2 ^ (i + 1)) in
  size s1 = 2 -> {homo merge_sort_push s1 : ss / graded ss}.
Proof.
set n := {2}1; rewrite -[RHS]/(2 ^ n) => graded sz_s1 ss.
elim: ss => [|s2 ss IHss] in (n) graded s1 sz_s1 * => sz_ss i //=.
  by case: i => [|[]] //; rewrite sz_s1 inE eqxx orbT.
case: s2 i => [|x s2] [|i] //= in sz_ss *; first by rewrite sz_s1 inE eqxx orbT.
  exact: (sz_ss i.+1).
rewrite addSnnS; apply: IHss i => [|i]; last by rewrite -addSnnS (sz_ss i.+1).
by rewrite size_merge size_cat sz_s1 (eqP (sz_ss 0)) addnn expnS mul2n.
Qed.

Section Stability.

Variable leT' : rel T.
Hypothesis (leT_total : total leT) (leT'_tr : transitive leT').

Let leT_lex := [rel x y | leT x y && (leT y x ==> leT' x y)].

Lemma merge_stable_path x s1 s2 :
  allrel leT' s1 s2 -> path leT_lex x s1 -> path leT_lex x s2 ->
  path leT_lex x (merge s1 s2).
Proof.
elim: s1 s2 x => //= x s1 ih1; elim => //= y s2 ih2 h.
rewrite allrel_cons2 => /and4P [xy' xs2 ys1 s1s2] /andP [hx xs1] /andP [hy ys2].
case: ifP => xy /=; rewrite (hx, hy) /=.
- by apply: ih1; rewrite ?allrel_consr ?ys1 //= xy xy' implybT.
- by apply: ih2; have:= leT_total x y; rewrite ?allrel_consl ?xs2 ?xy //= => ->.
Qed.

Lemma merge_stable_sorted s1 s2 :
  allrel leT' s1 s2 -> sorted leT_lex s1 -> sorted leT_lex s2 ->
  sorted leT_lex (merge s1 s2).
Proof.
case: s1 s2 => [|x s1] [|y s2] //=; rewrite allrel_consl allrel_consr /= -andbA.
case/and4P => [xy' xs2 ys1 s1s2] xs1 ys2; rewrite -/(merge (_ :: _)).
by case: ifP (leT_total x y) => /= xy yx; apply/merge_stable_path;
  rewrite /= ?(allrel_consl, allrel_consr, xs2, ys1, xy, yx, xy', implybT).
Qed.

End Stability.

Hypothesis leT_total : total leT.

Let leElex : leT =2 [rel x y | leT x y && (leT y x ==> true)].
Proof. by move=> ? ? /=; rewrite implybT andbT. Qed.

Lemma merge_path x s1 s2 :
  path leT x s1 -> path leT x s2 -> path leT x (merge s1 s2).
Proof. by rewrite !(eq_path leElex); apply/merge_stable_path/allrelT. Qed.

Lemma merge_sorted s1 s2 :
  sorted leT s1 -> sorted leT s2 -> sorted leT (merge s1 s2).
Proof. by rewrite !(eq_sorted leElex); apply/merge_stable_sorted/allrelT. Qed.

Hypothesis leT_tr : transitive leT.

Lemma sorted_merge s t : sorted leT (s ++ t) -> merge s t = s ++ t.
Proof. by rewrite sorted_pairwise // pairwise_cat => /and3P[/allrel_merge]. Qed.

Lemma sorted_sort s : sorted leT s -> sort s = s.
Proof. by rewrite sorted_pairwise //; apply/pairwise_sort. Qed.

Lemma mergeA : associative merge.
Proof.
elim=> // x xs IHxs; elim=> // y ys IHys; elim=> [|z zs IHzs] /=.
  by case: ifP.
case: ifP; case: ifP => /= lexy leyz.
- by rewrite lexy (leT_tr lexy leyz) -IHxs /= leyz.
- by rewrite lexy leyz -IHys.
- case: ifP => lexz; first by rewrite -IHxs //= leyz.
  by rewrite -!/(merge (_ :: _)) IHzs /= lexy.
- suff->: leT x z = false by rewrite leyz // -!/(merge (_ :: _)) IHzs /= lexy.
  by apply/contraFF/leT_tr: leyz; have := leT_total x y; rewrite lexy.
Qed.

End SortSeq.

Arguments merge {T} relT !s1 !s2 : rename.
Arguments size_merge {T} leT s1 s2.
Arguments allrel_merge {T leT s1 s2}.
Arguments pairwise_sort {T leT s}.
Arguments merge_path {T leT} leT_total {x s1 s2}.
Arguments merge_sorted {T leT} leT_total {s1 s2}.
Arguments sorted_merge {T leT} leT_tr {s t}.
Arguments sorted_sort {T leT} leT_tr {s}.
Arguments mergeA {T leT} leT_total leT_tr.

Section SortMap.
Variables (T T' : Type) (f : T' -> T).

Section Monotonicity.

Variables (leT' : rel T') (leT : rel T).
Hypothesis f_mono : {mono f : x y / leT' x y >-> leT x y}.

Lemma map_merge : {morph map f : s1 s2 / merge leT' s1 s2 >-> merge leT s1 s2}.
Proof.
elim=> //= x s1 IHs1; elim => [|y s2 IHs2] //=; rewrite f_mono.
by case: leT'; rewrite /= ?IHs1 ?IHs2.
Qed.

Lemma map_sort : {morph map f : s1 / sort leT' s1 >-> sort leT s1}.
Proof.
move=> s; rewrite !sortE -[[::] in RHS]/(map (map f) [::]).
elim: s [::] => /= [|x s ihs] ss; rewrite -/(map f [::]) -/(map f [:: _]);
  first by elim: ss [::] => //= x ss ihss ?; rewrite ihss map_merge.
rewrite ihs -/(map f [:: x]); congr sort_rec1.
by elim: ss [:: x] => {x s ihs} [|[|x s] ss ihss] //= ?; rewrite ihss map_merge.
Qed.

End Monotonicity.

Variable leT : rel T.

Lemma merge_map s1 s2 :
  merge leT (map f s1) (map f s2) = map f (merge (relpre f leT) s1 s2).
Proof. exact/esym/map_merge. Qed.

Lemma sort_map s : sort leT (map f s) = map f (sort (relpre f leT) s).
Proof. exact/esym/map_sort. Qed.

End SortMap.

Arguments map_merge {T T' f leT' leT}.
Arguments map_sort {T T' f leT' leT}.
Arguments merge_map {T T' f leT}.
Arguments sort_map {T T' f leT}.

Lemma sorted_sort_in T (P : {pred T}) (leT : rel T) :
  {in P & &, transitive leT} ->
  forall s : seq T, all P s -> sorted leT s -> sort leT s = s.
Proof.
move=> /in3_sig ? _ /all_sigP[s ->].
by rewrite sort_map sorted_map => /sorted_sort->.
Qed.

Arguments sorted_sort_in {T P leT} leT_tr {s}.

Section EqSortSeq.

Variables (T : eqType) (leT : rel T).

Lemma perm_merge s1 s2 : perm_eql (merge leT s1 s2) (s1 ++ s2).
Proof. by apply/permPl/permP => ?; rewrite count_merge. Qed.

Lemma mem_merge s1 s2 : merge leT s1 s2 =i s1 ++ s2.
Proof. by apply: perm_mem; rewrite perm_merge. Qed.

Lemma merge_uniq s1 s2 : uniq (merge leT s1 s2) = uniq (s1 ++ s2).
Proof. by apply: perm_uniq; rewrite perm_merge. Qed.

Lemma perm_sort s : perm_eql (sort leT s) s.
Proof. by apply/permPl/permP => ?; rewrite count_sort. Qed.

Lemma mem_sort s : sort leT s =i s. Proof. exact/perm_mem/permPl/perm_sort. Qed.

Lemma sort_uniq s : uniq (sort leT s) = uniq s.
Proof. exact/perm_uniq/permPl/perm_sort. Qed.

Lemma eq_count_merge (p : pred T) s1 s1' s2 s2' :
  count p s1 = count p s1' -> count p s2 = count p s2' ->
  count p (merge leT s1 s2) = count p (merge leT s1' s2').
Proof. by rewrite !count_merge !count_cat => -> ->. Qed.

End EqSortSeq.

Lemma perm_iota_sort (T : Type) (leT : rel T) x0 s :
  {i_s : seq nat | perm_eq i_s (iota 0 (size s)) &
                   sort leT s = map (nth x0 s) i_s}.
Proof.
exists (sort (relpre (nth x0 s) leT) (iota 0 (size s))).
  by rewrite perm_sort.
by rewrite -[s in LHS](mkseq_nth x0) sort_map.
Qed.

Lemma all_merge (T : Type) (P : {pred T}) (leT : rel T) s1 s2 :
  all P (merge leT s1 s2) = all P s1 && all P s2.
Proof.
elim: s1 s2 => //= x s1 IHs1; elim=> [|y s2 IHs2]; rewrite ?andbT //=.
by case: ifP => _; rewrite /= ?IHs1 ?IHs2 //=; bool_congr.
Qed.

Lemma all_sort (T : Type) (P : {pred T}) (leT : rel T) s :
  all P (sort leT s) = all P s.
Proof.
case: s => // x s; move: (x :: s) => {}s.
by rewrite -(mkseq_nth x s) sort_map !all_map; apply/perm_all/permPl/perm_sort.
Qed.

Lemma size_sort (T : Type) (leT : rel T) s : size (sort leT s) = size s.
Proof. exact: (count_sort _ predT). Qed.

Lemma ltn_sorted_uniq_leq s : sorted ltn s = uniq s && sorted leq s.
Proof.
rewrite (sorted_pairwise leq_trans) (sorted_pairwise ltn_trans) uniq_pairwise.
by rewrite -pairwise_relI; apply/eq_pairwise => ? ?; rewrite ltn_neqAle.
Qed.

Lemma iota_sorted i n : sorted leq (iota i n).
Proof. by elim: n i => // [[|n] //= IHn] i; rewrite IHn leqW. Qed.

Lemma iota_ltn_sorted i n : sorted ltn (iota i n).
Proof. by rewrite ltn_sorted_uniq_leq iota_sorted iota_uniq. Qed.

Section Stability_iota.

Variables (leN : rel nat) (leN_total : total leN).

Let lt_lex := [rel n m | leN n m && (leN m n ==> (n < m))].

Let Fixpoint push_invariant (ss : seq (seq nat)) :=
  if ss is s :: ss' then
    [&& sorted lt_lex s, allrel gtn s (flatten ss') & push_invariant ss']
  else
    true.

Let push_stable s1 ss :
  push_invariant (s1 :: ss) -> push_invariant (merge_sort_push leN s1 ss).
Proof.
elim: ss s1 => [] // [] //= m s2 ss ihss s1; rewrite -cat_cons allrel_catr.
move=> /and5P[sorted_s1 /andP[s1s2 s1ss] sorted_s2 s2ss hss]; apply: ihss.
rewrite /= hss andbT merge_stable_sorted //=; last by rewrite allrelC.
by apply/allrelP => ? ?; rewrite mem_merge mem_cat => /orP[]; apply/allrelP.
Qed.

Let pop_stable s1 ss :
  push_invariant (s1 :: ss) -> sorted lt_lex (merge_sort_pop leN s1 ss).
Proof.
elim: ss s1 => [s1 /and3P[]|s2 ss ihss s1] //=; rewrite allrel_catr.
move=> /and5P[sorted_s1 /andP[s1s2 s1ss] sorted_s2 s2ss hss]; apply: ihss.
rewrite /= hss andbT merge_stable_sorted //=; last by rewrite allrelC.
by apply/allrelP => ? ?; rewrite mem_merge mem_cat => /orP[]; apply/allrelP.
Qed.

Lemma sort_iota_stable n : sorted lt_lex (sort leN (iota 0 n)).
Proof.
rewrite sortE.
have/andP[]: all (gtn 0) (flatten [::]) && push_invariant [::] by [].
elim: n 0 [::] => [|n ihn] m ss hss1 hss2; first exact: pop_stable.
apply/ihn/push_stable; last by rewrite /= allrel1l hss1.
have: all (gtn m.+1) (flatten ([:: m] :: ss)).
  by rewrite /= leqnn; apply: sub_all hss1 => ? /leqW.
elim: ss [:: _] {hss1 hss2} => [|[|? ?] ? ihss] //= ? ?.
by rewrite ihss //= all_cat all_merge -andbA andbCA -!all_cat.
Qed.

End Stability_iota.

Lemma sort_pairwise_stable T (leT leT' : rel T) :
  total leT -> forall s : seq T, pairwise leT' s ->
  sorted [rel x y | leT x y && (leT y x ==> leT' x y)] (sort leT s).
Proof.
move=> leT_total s pairwise_s; case Ds: s => // [x s1].
rewrite -{s1}Ds -(mkseq_nth x s) sort_map.
apply/homo_sorted_in/sort_iota_stable/(fun _ _ => leT_total _ _)/allss => y z.
rewrite !mem_sort !mem_iota !leq0n add0n /= => ys zs /andP [->] /=.
by case: (leT _ _); first apply: pairwiseP.
Qed.

Lemma sort_stable T (leT leT' : rel T) :
  total leT -> transitive leT' -> forall s : seq T, sorted leT' s ->
  sorted [rel x y | leT x y && (leT y x ==> leT' x y)] (sort leT s).
Proof.
move=> leT_total leT'_tr s; rewrite sorted_pairwise //.
exact: sort_pairwise_stable.
Qed.

Lemma sort_stable_in T (P : {pred T}) (leT leT' : rel T) :
  {in P &, total leT} -> {in P & &, transitive leT'} ->
  forall s : seq T, all P s -> sorted leT' s ->
  sorted [rel x y | leT x y && (leT y x ==> leT' x y)] (sort leT s).
Proof.
move=> /in2_sig leT_total /in3_sig leT_tr _ /all_sigP[s ->].
by rewrite sort_map !sorted_map; apply: sort_stable.
Qed.

Lemma filter_sort T (leT : rel T) :
  total leT -> transitive leT ->
  forall p s, filter p (sort leT s) = sort leT (filter p s).
Proof.
move=> leT_total leT_tr p s; case Ds: s => // [x s1].
pose leN := relpre (nth x s) leT.
pose lt_lex := [rel n m | leN n m && (leN m n ==> (n < m))].
have lt_lex_tr: transitive lt_lex.
  rewrite /lt_lex /leN => ? ? ? /= /andP [xy xy'] /andP [yz yz'].
  rewrite (leT_tr _ _ _ xy yz); apply/implyP => zx; move: xy' yz'.
  by rewrite (leT_tr _ _ _ yz zx) (leT_tr _ _ _ zx xy); apply: ltn_trans.
rewrite -{s1}Ds -(mkseq_nth x s) !(filter_map, sort_map); congr map.
apply/(@irr_sorted_eq _ lt_lex); rewrite /lt_lex /leN //=.
- by move=> ?; rewrite /= ltnn implybF andbN.
- exact/sorted_filter/sort_iota_stable.
- exact/sort_stable/sorted_filter/iota_ltn_sorted/ltn_trans/ltn_trans.
- by move=> ?; rewrite !(mem_filter, mem_sort).
Qed.

Lemma filter_sort_in T (P : {pred T}) (leT : rel T) :
  {in P &, total leT} -> {in P & &, transitive leT} ->
  forall p s, all P s -> filter p (sort leT s) = sort leT (filter p s).
Proof.
move=> /in2_sig leT_total /in3_sig leT_tr p _ /all_sigP[s ->].
by rewrite !(sort_map, filter_map) filter_sort.
Qed.

Section Stability_mask.

Variables (T : Type) (leT : rel T).
Variables (leT_total : total leT) (leT_tr : transitive leT).

Lemma mask_sort s m :
  {m_s : bitseq | mask m_s (sort leT s) = sort leT (mask m s)}.
Proof.
case Ds: {-}s => [|x s1]; [by rewrite Ds; case: m; exists [::] | clear s1 Ds].
rewrite -(mkseq_nth x s) -map_mask !sort_map.
exists [seq i \in mask m (iota 0 (size s)) |
            i <- sort (xrelpre (nth x s) leT) (iota 0 (size s))].
rewrite -map_mask -filter_mask [in RHS]mask_filter ?iota_uniq ?filter_sort //.
by move=> ? ? ?; exact: leT_tr.
Qed.

Lemma sorted_mask_sort s m :
  sorted leT (mask m s) -> {m_s | mask m_s (sort leT s) = mask m s}.
Proof. by move/(sorted_sort leT_tr) <-; exact: mask_sort. Qed.

End Stability_mask.

Section Stability_mask_in.

Variables (T : Type) (P : {pred T}) (leT : rel T).
Hypothesis leT_total : {in P &, total leT}.
Hypothesis leT_tr : {in P & &, transitive leT}.

Let le_sT := relpre (val : sig P -> _) leT.
Let le_sT_total : total le_sT := in2_sig leT_total.
Let le_sT_tr : transitive le_sT := in3_sig leT_tr.

Lemma mask_sort_in s m :
  all P s -> {m_s : bitseq | mask m_s (sort leT s) = sort leT (mask m s)}.
Proof.
move=> /all_sigP [{}s ->]; case: (mask_sort (leT := le_sT) _ _ s m) => //.
by move=> m' m'E; exists m'; rewrite -map_mask !sort_map -map_mask m'E.
Qed.

Lemma sorted_mask_sort_in s m :
  all P s -> sorted leT (mask m s) -> {m_s | mask m_s (sort leT s) = mask m s}.
Proof.
move=> ? /(sorted_sort_in leT_tr _) <-; [exact: mask_sort_in | exact: all_mask].
Qed.

End Stability_mask_in.

Section Stability_subseq.

Variables (T : eqType) (leT : rel T).
Variables (leT_total : total leT) (leT_tr : transitive leT).

Lemma subseq_sort : {homo sort leT : t s / subseq t s}.
Proof.
move=> _ s /subseqP [m _ ->]; have [m' <-] := mask_sort leT_total leT_tr s m.
exact: mask_subseq.
Qed.

Lemma sorted_subseq_sort t s :
  subseq t s -> sorted leT t -> subseq t (sort leT s).
Proof. by move=> subseq_ts /(sorted_sort leT_tr) <-; exact: subseq_sort. Qed.

Lemma mem2_sort s x y : leT x y -> mem2 s x y -> mem2 (sort leT s) x y.
Proof.
move=> lexy /[!mem2E] /subseq_sort.
by case: eqP => // _; rewrite {1}/sort /= lexy /=.
Qed.

End Stability_subseq.

Section Stability_subseq_in.

Variables (T : eqType) (leT : rel T).

Lemma subseq_sort_in t s :
  {in s &, total leT} -> {in s & &, transitive leT} ->
  subseq t s -> subseq (sort leT t) (sort leT s).
Proof.
move=> leT_total leT_tr /subseqP [m _ ->].
have [m' <-] := mask_sort_in leT_total leT_tr m (allss _).
exact: mask_subseq.
Qed.

Lemma sorted_subseq_sort_in t s :
  {in s &, total leT} -> {in s & &, transitive leT} ->
  subseq t s -> sorted leT t -> subseq t (sort leT s).
Proof.
move=> ? leT_tr ? /(sorted_sort_in leT_tr) <-; last exact/allP/mem_subseq.
exact: subseq_sort_in.
Qed.

Lemma mem2_sort_in s :
  {in s &, total leT} -> {in s & &, transitive leT} ->
  forall x y, leT x y -> mem2 s x y -> mem2 (sort leT s) x y.
Proof.
move=> leT_total leT_tr x y lexy; rewrite !mem2E.
by move/subseq_sort_in; case: (_ == _); rewrite /sort /= ?lexy; apply.
Qed.

End Stability_subseq_in.

Lemma sort_sorted T (leT : rel T) :
  total leT -> forall s, sorted leT (sort leT s).
Proof.
move=> leT_total s; apply/sub_sorted/sort_stable => //= [? ? /andP[] //|].
by case: s => // x s; elim: s x => /=.
Qed.

Lemma sort_sorted_in T (P : {pred T}) (leT : rel T) :
  {in P &, total leT} -> forall s : seq T, all P s -> sorted leT (sort leT s).
Proof.
by move=> /in2_sig ? _ /all_sigP[s ->]; rewrite sort_map sorted_map sort_sorted.
Qed.

Arguments sort_sorted {T leT} leT_total s.
Arguments sort_sorted_in {T P leT} leT_total {s}.

Lemma perm_sortP (T : eqType) (leT : rel T) :
  total leT -> transitive leT -> antisymmetric leT ->
  forall s1 s2, reflect (sort leT s1 = sort leT s2) (perm_eq s1 s2).
Proof.
move=> leT_total leT_tr leT_asym s1 s2.
apply: (iffP idP) => eq12; last by rewrite -(perm_sort leT) eq12 perm_sort.
apply: (sorted_eq leT_tr leT_asym); rewrite ?sort_sorted //.
by rewrite perm_sort (permPl eq12) -(perm_sort leT).
Qed.

Lemma perm_sort_inP (T : eqType) (leT : rel T) (s1 s2 : seq T) :
  {in s1 &, total leT} -> {in s1 & &, transitive leT} ->
  {in s1 &, antisymmetric leT} ->
  reflect (sort leT s1 = sort leT s2) (perm_eq s1 s2).
Proof.
move=> /in2_sig leT_total /in3_sig leT_tr /in2_sig/(_ _ _ _)/val_inj leT_asym.
apply: (iffP idP) => s1s2; last by rewrite -(perm_sort leT) s1s2 perm_sort.
move: (s1s2); have /all_sigP[s1' ->] := allss s1.
have /all_sigP[{s1s2}s2 ->] : all [in s1] s2 by rewrite -(perm_all _ s1s2).
by rewrite !sort_map => /(perm_map_inj val_inj) /(perm_sortP leT_total)->.
Qed.

Lemma homo_sort_map (T : Type) (T' : eqType) (f : T -> T') leT leT' :
  antisymmetric (relpre f leT') -> transitive (relpre f leT') -> total leT ->
  {homo f : x y / leT x y >-> leT' x y} ->
  forall s : seq T, sort leT' (map f s) = map f (sort leT s).
Proof.
move=> leT'_asym leT'_trans leT_total f_homo s; case Ds: s => // [x s'].
rewrite -{}Ds -(mkseq_nth x s) [in RHS]sort_map -!map_comp /comp.
apply: (@sorted_eq_in _ leT') => [? ? ?|? ?|||]; rewrite ?mem_sort.
- by move=> /mapP[? _ ->] /mapP[? _ ->] /mapP[? _ ->]; apply/leT'_trans.
- by move=> /mapP[? _ ->] /mapP[? _ ->] /leT'_asym ->.
- apply: (sort_sorted_in _ (allss _)) => _ _ /mapP[y _ ->] /mapP[z _ ->].
  by case/orP: (leT_total (nth x s y) (nth x s z)) => /f_homo ->; rewrite ?orbT.
- by rewrite map_comp -sort_map; exact/homo_sorted/sort_sorted.
- by rewrite perm_sort perm_map // perm_sym perm_sort.
Qed.

Lemma homo_sort_map_in
      (T : Type) (T' : eqType) (P : {pred T}) (f : T -> T') leT leT' :
  {in P &, antisymmetric (relpre f leT')} ->
  {in P & &, transitive (relpre f leT')} -> {in P &, total leT} ->
  {in P &, {homo f : x y / leT x y >-> leT' x y}} ->
  forall s : seq T, all P s ->
        sort leT' [seq f x | x <- s] = [seq f x | x <- sort leT s].
Proof.
move=> /in2_sig leT'_asym /in3_sig leT'_trans /in2_sig leT_total.
move=> /in2_sig f_homo _ /all_sigP[s ->].
rewrite [in RHS]sort_map -!map_comp /comp.
by apply: homo_sort_map => // ? ? /leT'_asym /val_inj.
Qed.

(* Function trajectories. *)

Notation fpath f := (path (coerced_frel f)).
Notation fcycle f := (cycle (coerced_frel f)).
Notation ufcycle f := (ucycle (coerced_frel f)).

Prenex Implicits path next prev cycle ucycle mem2.

Section Trajectory.

Variables (T : Type) (f : T -> T).

Fixpoint traject x n := if n is n'.+1 then x :: traject (f x) n' else [::].

Lemma trajectS x n : traject x n.+1 = x :: traject (f x) n.
Proof. by []. Qed.

Lemma trajectSr x n : traject x n.+1 = rcons (traject x n) (iter n f x).
Proof. by elim: n x => //= n IHn x; rewrite IHn -iterSr. Qed.

Lemma last_traject x n : last x (traject (f x) n) = iter n f x.
Proof. by case: n => // n; rewrite iterSr trajectSr last_rcons. Qed.

Lemma traject_iteri x n :
  traject x n = iteri n (fun i => rcons^~ (iter i f x)) [::].
Proof. by elim: n => //= n <-; rewrite -trajectSr. Qed.

Lemma size_traject x n : size (traject x n) = n.
Proof. by elim: n x => //= n IHn x //=; rewrite IHn. Qed.

Lemma nth_traject i n : i < n -> forall x, nth x (traject x n) i = iter i f x.
Proof.
elim: n => // n IHn; rewrite ltnS => le_i_n x.
rewrite trajectSr nth_rcons size_traject.
by case: ltngtP le_i_n => [? _||->] //; apply: IHn.
Qed.

Lemma trajectD m n x :
  traject x (m + n) = traject x m ++ traject (iter m f x) n.
Proof. by elim: m => //m IHm in x *; rewrite addSn !trajectS IHm -iterSr. Qed.

Lemma take_traject n k x : k <= n -> take k (traject x n) = traject x k.
Proof. by move=> /subnKC<-; rewrite trajectD take_size_cat ?size_traject. Qed.

End Trajectory.

Section EqTrajectory.

Variables (T : eqType) (f : T -> T).

Lemma eq_fpath f' : f =1 f' -> fpath f =2 fpath f'.
Proof. by move/eq_frel/eq_path. Qed.

Lemma eq_fcycle f' : f =1 f' -> fcycle f =1 fcycle f'.
Proof. by move/eq_frel/eq_cycle. Qed.

Lemma fpathE x p : fpath f x p -> p = traject f (f x) (size p).
Proof. by elim: p => //= y p IHp in x * => /andP[/eqP{y}<- /IHp<-]. Qed.

Lemma fpathP x p : reflect (exists n, p = traject f (f x) n) (fpath f x p).
Proof.
apply: (iffP idP) => [/fpathE->|[n->]]; first by exists (size p).
by elim: n => //= n IHn in x *; rewrite eqxx IHn.
Qed.

Lemma fpath_traject x n : fpath f x (traject f (f x) n).
Proof. by apply/(fpathP x); exists n. Qed.

Definition looping x n := iter n f x \in traject f x n.

Lemma loopingP x n :
  reflect (forall m, iter m f x \in traject f x n) (looping x n).
Proof.
apply: (iffP idP) => loop_n; last exact: loop_n.
case: n => // n in loop_n *; elim=> [|m /= IHm]; first exact: mem_head.
move: (fpath_traject x n) loop_n; rewrite /looping !iterS -last_traject /=.
move: (iter m f x) IHm => y /splitPl[p1 p2 def_y].
rewrite cat_path last_cat def_y; case: p2 => // z p2 /and3P[_ /eqP-> _] _.
by rewrite inE mem_cat mem_head !orbT.
Qed.

Lemma trajectP x n y :
  reflect (exists2 i, i < n & y = iter i f x) (y \in traject f x n).
Proof.
elim: n x => [|n IHn] x /=; first by right; case.
rewrite inE; have [-> | /= neq_xy] := eqP; first by left; exists 0.
apply: {IHn}(iffP (IHn _)) => [[i] | [[|i]]] // lt_i_n ->.
  by exists i.+1; rewrite ?iterSr.
by exists i; rewrite ?iterSr.
Qed.

Lemma looping_uniq x n : uniq (traject f x n.+1) = ~~ looping x n.
Proof.
rewrite /looping; elim: n x => [|n IHn] x //.
rewrite [n.+1 in LHS]lock [iter]lock /= -!lock {}IHn -iterSr -negb_or inE.
congr (~~ _); apply: orb_id2r => /trajectP no_loop.
apply/idP/eqP => [/trajectP[m le_m_n def_x] | {1}<-]; last first.
  by rewrite iterSr -last_traject mem_last.
have loop_m: looping x m.+1 by rewrite /looping iterSr -def_x mem_head.
have/trajectP[[|i] // le_i_m def_fn1x] := loopingP _ _ loop_m n.+1.
by case: no_loop; exists i; rewrite -?iterSr // -ltnS (leq_trans le_i_m).
Qed.

End EqTrajectory.

Arguments fpathP {T f x p}.
Arguments loopingP {T f x n}.
Arguments trajectP {T f x n y}.
Prenex Implicits traject.

Section Fcycle.
Variables (T : eqType) (f : T -> T) (p : seq T) (f_p : fcycle f p).

Lemma nextE (x : T) (p_x : x \in p) : next p x = f x.
Proof. exact/esym/eqP/(next_cycle f_p). Qed.

Lemma mem_fcycle : {homo f : x / x \in p}.
Proof. by move=> x xp; rewrite -nextE// mem_next. Qed.

Lemma inj_cycle : {in p &, injective f}.
Proof.
apply: can_in_inj (iter (size p).-1 f) _ => x /rot_to[i q rip].
have /fpathE qxE : fcycle f (x :: q) by rewrite -rip rot_cycle.
have -> : size p = size (rcons q x) by rewrite size_rcons -(size_rot i) rip.
by rewrite -iterSr -last_traject prednK -?qxE ?size_rcons// last_rcons.
Qed.

End Fcycle.

Section UniqCycle.

Variables (n0 : nat) (T : eqType) (e : rel T) (p : seq T).

Hypothesis Up : uniq p.

Lemma prev_next : cancel (next p) (prev p).
Proof.
move=> x; rewrite prev_nth mem_next next_nth; case p_x: (x \in p) => //.
case Dp: p Up p_x => // [y q]; rewrite [uniq _]/= -Dp => /andP[q'y Uq] p_x.
rewrite -[RHS](nth_index y p_x); congr (nth y _ _); set i := index x p.
have: i <= size q by rewrite -index_mem -/i Dp in p_x.
case: ltngtP => // [lt_i_q|->] _; first by rewrite index_uniq.
by apply/eqP; rewrite nth_default // eqn_leq index_size leqNgt index_mem.
Qed.

Lemma next_prev : cancel (prev p) (next p).
Proof.
move=> x; rewrite next_nth mem_prev prev_nth; case p_x: (x \in p) => //.
case def_p: p p_x => // [y q]; rewrite -def_p => p_x.
rewrite index_uniq //; last by rewrite def_p ltnS index_size.
case q_x: (x \in q); first exact: nth_index.
rewrite nth_default; last by rewrite leqNgt index_mem q_x.
by apply/eqP; rewrite def_p inE q_x orbF eq_sym in p_x.
Qed.

Lemma cycle_next : fcycle (next p) p.
Proof.
case def_p: p Up => [|x q] Uq //; rewrite -[in next _]def_p.
apply/(pathP x)=> i; rewrite size_rcons => le_i_q.
rewrite -cats1 -cat_cons nth_cat le_i_q /= next_nth {}def_p mem_nth //.
rewrite index_uniq // nth_cat /= ltn_neqAle andbC -ltnS le_i_q.
by case: (i =P _) => //= ->; rewrite subnn nth_default.
Qed.

Lemma cycle_prev : cycle (fun x y => x == prev p y) p.
Proof.
apply: etrans cycle_next; symmetry; case def_p: p => [|x q] //.
by apply: eq_path; rewrite -def_p; apply: (can2_eq prev_next next_prev).
Qed.

Lemma cycle_from_next : (forall x, x \in p -> e x (next p x)) -> cycle e p.
Proof.
case: p (next p) cycle_next => //= [x q] n; rewrite -(belast_rcons x q x).
move: {q}(rcons q x) => q n_q /allP.
by elim: q x n_q => //= _ q IHq x /andP[/eqP <- n_q] /andP[-> /IHq->].
Qed.

Lemma cycle_from_prev : (forall x, x \in p -> e (prev p x) x) -> cycle e p.
Proof.
move=> e_p; apply: cycle_from_next => x.
by rewrite -mem_next => /e_p; rewrite prev_next.
Qed.

Lemma next_rot : next (rot n0 p) =1 next p.
Proof.
move=> x; have n_p := cycle_next; rewrite -(rot_cycle n0) in n_p.
case p_x: (x \in p); last by rewrite !next_nth mem_rot p_x.
by rewrite (eqP (next_cycle n_p _)) ?mem_rot.
Qed.

Lemma prev_rot : prev (rot n0 p) =1 prev p.
Proof.
move=> x; have p_p := cycle_prev; rewrite -(rot_cycle n0) in p_p.
case p_x: (x \in p); last by rewrite !prev_nth mem_rot p_x.
by rewrite (eqP (prev_cycle p_p _)) ?mem_rot.
Qed.

End UniqCycle.

Section UniqRotrCycle.

Variables (n0 : nat) (T : eqType) (p : seq T).

Hypothesis Up : uniq p.

Lemma next_rotr : next (rotr n0 p) =1 next p. Proof. exact: next_rot. Qed.

Lemma prev_rotr : prev (rotr n0 p) =1 prev p. Proof. exact: prev_rot. Qed.

End UniqRotrCycle.

Section UniqCycleRev.

Variable T : eqType.
Implicit Type p : seq T.

Lemma prev_rev p : uniq p -> prev (rev p) =1 next p.
Proof.
move=> Up x; case p_x: (x \in p); last first.
  by rewrite next_nth prev_nth mem_rev p_x.
case/rot_to: p_x (Up) => [i q def_p] Urp; rewrite -rev_uniq in Urp.
rewrite -(prev_rotr i Urp); do 2 rewrite -(prev_rotr 1) ?rotr_uniq //.
rewrite -rev_rot -(next_rot i Up) {i p Up Urp}def_p.
by case: q => // y q; rewrite !rev_cons !(=^~ rcons_cons, rotr1_rcons) /= eqxx.
Qed.

Lemma next_rev p : uniq p -> next (rev p) =1 prev p.
Proof. by move=> Up x; rewrite -[p in RHS]revK prev_rev // rev_uniq. Qed.

End UniqCycleRev.

Section MapPath.

Variables (T T' : Type) (h : T' -> T) (e : rel T) (e' : rel T').

Definition rel_base (b : pred T) :=
  forall x' y', ~~ b (h x') -> e (h x') (h y') = e' x' y'.

Lemma map_path b x' p' (Bb : rel_base b) :
    ~~ has (preim h b) (belast x' p') ->
  path e (h x') (map h p') = path e' x' p'.
Proof. by elim: p' x' => [|y' p' IHp'] x' //= /norP[/Bb-> /IHp'->]. Qed.

End MapPath.

Section MapEqPath.

Variables (T T' : eqType) (h : T' -> T) (e : rel T) (e' : rel T').

Hypothesis Ih : injective h.

Lemma mem2_map x' y' p' : mem2 (map h p') (h x') (h y') = mem2 p' x' y'.
Proof. by rewrite [LHS]/mem2 (index_map Ih) -map_drop mem_map. Qed.

Lemma next_map p : uniq p -> forall x, next (map h p) (h x) = h (next p x).
Proof.
move=> Up x; case p_x: (x \in p); last by rewrite !next_nth (mem_map Ih) p_x.
case/rot_to: p_x => i p' def_p.
rewrite -(next_rot i Up); rewrite -(map_inj_uniq Ih) in Up.
rewrite -(next_rot i Up) -map_rot {i p Up}def_p /=.
by case: p' => [|y p''] //=; rewrite !eqxx.
Qed.

Lemma prev_map p : uniq p -> forall x, prev (map h p) (h x) = h (prev p x).
Proof.
move=> Up x; rewrite -[x in LHS](next_prev Up) -(next_map Up).
by rewrite prev_next ?map_inj_uniq.
Qed.

End MapEqPath.

Definition fun_base (T T' : eqType) (h : T' -> T) f f' :=
  rel_base h (frel f) (frel f').

Section CycleArc.

Variable T : eqType.
Implicit Type p : seq T.

Definition arc p x y := let px := rot (index x p) p in take (index y px) px.

Lemma arc_rot i p : uniq p -> {in p, arc (rot i p) =2 arc p}.
Proof.
move=> Up x p_x y; congr (fun q => take (index y q) q); move: Up p_x {y}.
rewrite -{1 2 5 6}(cat_take_drop i p) /rot cat_uniq => /and3P[_ Up12 _].
rewrite !drop_cat !take_cat !index_cat mem_cat orbC.
case p2x: (x \in drop i p) => /= => [_ | p1x].
  rewrite index_mem p2x [x \in _](negbTE (hasPn Up12 _ p2x)) /= addKn.
  by rewrite ltnNge leq_addr catA.
by rewrite p1x index_mem p1x addKn ltnNge leq_addr /= catA.
Qed.

Lemma left_arc x y p1 p2 (p := x :: p1 ++ y :: p2) :
  uniq p -> arc p x y = x :: p1.
Proof.
rewrite /arc /p [index x _]/= eqxx rot0 -cat_cons cat_uniq index_cat.
move: (x :: p1) => xp1 /and3P[_ /norP[/= /negbTE-> _] _].
by rewrite eqxx addn0 take_size_cat.
Qed.

Lemma right_arc x y p1 p2 (p := x :: p1 ++ y :: p2) :
  uniq p -> arc p y x = y :: p2.
Proof.
rewrite -[p]cat_cons -rot_size_cat rot_uniq => Up.
by rewrite arc_rot ?left_arc ?mem_head.
Qed.

Variant rot_to_arc_spec p x y :=
    RotToArcSpec i p1 p2 of x :: p1 = arc p x y
                          & y :: p2 = arc p y x
                          & rot i p = x :: p1 ++ y :: p2 :
    rot_to_arc_spec p x y.

Lemma rot_to_arc p x y :
  uniq p -> x \in p -> y \in p -> x != y -> rot_to_arc_spec p x y.
Proof.
move=> Up p_x p_y ne_xy; case: (rot_to p_x) (p_y) (Up) => [i q def_p] q_y.
rewrite -(mem_rot i) def_p inE eq_sym (negbTE ne_xy) in q_y.
rewrite -(rot_uniq i) def_p.
case/splitPr: q / q_y def_p => q1 q2 def_p Uq12; exists i q1 q2 => //.
  by rewrite -(arc_rot i Up p_x) def_p left_arc.
by rewrite -(arc_rot i Up p_y) def_p right_arc.
Qed.

End CycleArc.

Prenex Implicits arc.

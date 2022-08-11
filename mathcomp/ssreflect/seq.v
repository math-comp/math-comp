(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

(******************************************************************************)
(* The seq type is the ssreflect type for sequences; it is an alias for the   *)
(* standard Coq list type. The ssreflect library equips it with many          *)
(* operations, as well as eqType and predType (and, later, choiceType)        *)
(* structures. The operations are geared towards reflection: they generally   *)
(* expect and provide boolean predicates, e.g., the membership predicate      *)
(* expects an eqType. To avoid any confusion we do not Import the Coq List    *)
(* module.                                                                    *)
(*   As there is no true subtyping in Coq, we don't use a type for non-empty  *)
(* sequences; rather, we pass explicitly the head and tail of the sequence.   *)
(*   The empty sequence is especially bothersome for subscripting, since it   *)
(* forces us to pass a default value. This default value can often be hidden  *)
(* by a notation.                                                             *)
(*   Here is the list of seq operations:                                      *)
(*  ** Constructors:                                                          *)
(*                        seq T == the type of sequences of items of type T.  *)
(*                       bitseq == seq bool.                                  *)
(*             [::], nil, Nil T == the empty sequence (of type T).            *)
(* x :: s, cons x s, Cons T x s == the sequence x followed by s (of type T).  *)
(*                       [:: x] == the singleton sequence.                    *)
(*           [:: x_0; ...; x_n] == the explicit sequence of the x_i.          *)
(*       [:: x_0, ..., x_n & s] == the sequence of the x_i, followed by s.    *)
(*                    rcons s x == the sequence s, followed by x.             *)
(*  All of the above, except rcons, can be used in patterns. We define a view *)
(* lastP and an induction principle last_ind that can be used to decompose    *)
(* or traverse a sequence in a right to left order. The view lemma lastP has  *)
(* a dependent family type, so the ssreflect tactic case/lastP: p => [|p' x]  *)
(* will generate two subgoals in which p has been replaced by [::] and by     *)
(* rcons p' x, respectively.                                                  *)
(*  ** Factories:                                                             *)
(*             nseq n x == a sequence of n x's.                               *)
(*          ncons n x s == a sequence of n x's, followed by s.                *)
(* seqn n x_0 ... x_n-1 == the sequence of the x_i; can be partially applied. *)
(*             iota m n == the sequence m, m + 1, ..., m + n - 1.             *)
(*            mkseq f n == the sequence f 0, f 1, ..., f (n - 1).             *)
(*  ** Sequential access:                                                     *)
(*      head x0 s == the head (zero'th item) of s if s is non-empty, else x0. *)
(*        ohead s == None if s is empty, else Some x when the head of s is x. *)
(*       behead s == s minus its head, i.e., s' if s = x :: s', else [::].    *)
(*       last x s == the last element of x :: s (which is non-empty).         *)
(*     belast x s == x :: s minus its last item.                              *)
(*  ** Dimensions:                                                            *)
(*         size s == the number of items (length) in s.                       *)
(*       shape ss == the sequence of sizes of the items of the sequence of    *)
(*                   sequences ss.                                            *)
(*  ** Random access:                                                         *)
(*         nth x0 s i == the item i of s (numbered from 0), or x0 if s does   *)
(*                       not have at least i+1 items (i.e., size x <= i)      *)
(*               s`_i == standard notation for nth x0 s i for a default x0,   *)
(*                       e.g., 0 for rings.                                   *)
(*   set_nth x0 s i y == s where item i has been changed to y; if s does not  *)
(*                       have an item i, it is first padded with copies of x0 *)
(*                       to size i+1.                                         *)
(*       incr_nth s i == the nat sequence s with item i incremented (s is     *)
(*                       first padded with 0's to size i+1, if needed).       *)
(*  ** Predicates:                                                            *)
(*          nilp s <=> s is [::].                                             *)
(*                 := (size s == 0).                                          *)
(*         x \in s == x appears in s (this requires an eqType for T).         *)
(*       index x s == the first index at which x appears in s, or size s if   *)
(*                    x \notin s.                                             *)
(*         has a s <=> a holds for some item in s, where a is an applicative  *)
(*                     bool predicate.                                        *)
(*         all a s <=> a holds for all items in s.                            *)
(*         'has_aP <-> the view reflect (exists2 x, x \in s & A x) (has a s), *)
(*                     where aP x : reflect (A x) (a x).                      *)
(*         'all_aP <=> the view for reflect {in s, forall x, A x} (all a s).  *)
(*      all2 r s t <=> the (bool) relation r holds for all _respective_ items *)
(*                    in s and t, which must also have the same size, i.e.,   *)
(*                    for s := [:: x1; ...; x_m] and t := [:: y1; ...; y_n],  *)
(*                    the condition [&& r x_1 y_1, ..., r x_n y_n & m == n].  *)
(*        find p s == the index of the first item in s for which p holds,     *)
(*                    or size s if no such item is found.                     *)
(*       count p s == the number of items of s for which p holds.             *)
(*   count_mem x s == the multiplicity of x in s, i.e., count (pred1 x) s.    *)
(*         tally s == a tally of s, i.e., a sequence of (item, multiplicity)  *)
(*                    pairs for all items in sequence s (without duplicates). *)
(* incr_tally bs x == increment the multiplicity of x in the tally bs, or add *)
(*                    x with multiplicity 1 at then end if x is not in bs.    *)
(* bs \is a wf_tally <=> bs is well-formed tally, with no duplicate items or  *)
(*                    null multiplicities.                                    *)
(*    tally_seq bs == the expansion of a tally bs into a sequence where each  *)
(*                    (x, n) pair expands into a sequence of n x's.           *)
(*      constant s <=> all items in s are identical (trivial if s = [::]).    *)
(*          uniq s <=> all the items in s are pairwise different.             *)
(*    subseq s1 s2 <=> s1 is a subsequence of s2, i.e., s1 = mask m s2 for    *)
(*                    some m : bitseq (see below).                            *)
(*     infix s1 s2 <=> s1 is a contiguous subsequence of s2, i.e.,            *)
(*                       s ++ s1 ++ s' = s2 for some sequences s, s'.         *)
(*    prefix s1 s2 <=> s1 is a subchain of s2 appearing at the beginning      *)
(*                       of s2.                                               *)
(*    suffix s1 s2 <=> s1 is a subchain of s2 appearing at the end of s2.     *)
(* infix_index s1 s2 <=> the first index at which s1 appears in s2,           *)
(*                       or (size s2).+1 if infix s1 s2 is false.             *)
(*   perm_eq s1 s2 <=> s2 is a permutation of s1, i.e., s1 and s2 have the    *)
(*                    items (with the same repetitions), but possibly in a    *)
(*                    different order.                                        *)
(*  perm_eql s1 s2 <-> s1 and s2 behave identically on the left of perm_eq.   *)
(*  perm_eqr s1 s2 <-> s1 and s2 behave identically on the right of perm_eq.  *)
(* --> These left/right transitive versions of perm_eq make it easier to      *)
(*  chain a sequence of equivalences.                                         *)
(*   permutations s == a duplicate-free list of all permutations of s.        *)
(*  ** Filtering:                                                             *)
(*           filter p s == the subsequence of s consisting of all the items   *)
(*                         for which the (boolean) predicate p holds.         *)
(*              rem x s == the subsequence of s, where the first occurrence   *)
(*                         of x has been removed (compare filter (predC1 x) s *)
(*                         where ALL occurrences of x are removed).           *)
(*              undup s == the subsequence of s containing only the first     *)
(*                         occurrence of each item in s, i.e., s with all     *)
(*                         duplicates removed.                                *)
(*             mask m s == the subsequence of s selected by m : bitseq, with  *)
(*                         item i of s selected by bit i in m (extra items or *)
(*                         bits are ignored.                                  *)
(*  ** Surgery:                                                               *)
(* s1 ++ s2, cat s1 s2 == the concatenation of s1 and s2.                     *)
(*            take n s == the sequence containing only the first n items of s *)
(*                        (or all of s if size s <= n).                       *)
(*            drop n s == s minus its first n items ([::] if size s <= n)     *)
(*             rot n s == s rotated left n times (or s if size s <= n).       *)
(*                     := drop n s ++ take n s                                *)
(*            rotr n s == s rotated right n times (or s if size s <= n).      *)
(*               rev s == the (linear time) reversal of s.                    *)
(*        catrev s1 s2 == the reversal of s1 followed by s2 (this is the      *)
(*                        recursive form of rev).                             *)
(*  ** Dependent iterator: for s : seq S and t : S -> seq T                   *)
(* [seq E | x <- s, y <- t] := flatten [seq [seq E | x <- t] | y <- s]        *)
(*                == the sequence of all the f x y, with x and y drawn from   *)
(*                   s and t, respectively, in row-major order,               *)
(*                   and where t is possibly dependent in elements of s       *)
(* allpairs_dep f s t := self expanding definition for                        *)
(*                       [seq f x y | x <- s, y <- t y]                       *)
(*  ** Iterators: for s == [:: x_1, ..., x_n], t == [:: y_1, ..., y_m],       *)
(* allpairs f s t := same as allpairs_dep but where t is non dependent,       *)
(*                    i.e. self expanding definition for                      *)
(*                      [seq f x y | x <- s, y <- t]                          *)
(*               := [:: f x_1 y_1; ...; f x_1 y_m; f x_2 y_1; ...; f x_n y_m] *)
(* allrel r xs ys := all [pred x | all (r x) ys] xs                           *)
(*                <=> r x y holds whenever x is in xs and y is in ys          *)
(*   all2rel r xs := allrel r xs xs                                           *)
(*                <=> the proposition r x y holds for all possible x, y in xs.*)
(*  pairwise r xs <=> the relation r holds for any i-th and j-th element of   *)
(*                    xs such that i < j.                                     *)
(*        map f s == the sequence [:: f x_1, ..., f x_n].                     *)
(*      pmap pf s == the sequence [:: y_i1, ..., y_ik] where i1 < ... < ik,   *)
(*                   pf x_i = Some y_i, and pf x_j = None iff j is not in     *)
(*                   {i1, ..., ik}.                                           *)
(*   foldr f a s == the right fold of s by f (i.e., the natural iterator).    *)
(*               := f x_1 (f x_2 ... (f x_n a))                               *)
(*        sumn s == x_1 + (x_2 + ... + (x_n + 0)) (when s : seq nat).         *)
(*   foldl f a s == the left fold of s by f.                                  *)
(*               := f (f ... (f a x_1) ... x_n-1) x_n                         *)
(*   scanl f a s == the sequence of partial accumulators of foldl f a s.      *)
(*               := [:: f a x_1; ...; foldl f a s]                            *)
(* pairmap f a s == the sequence of f applied to consecutive items in a :: s. *)
(*               := [:: f a x_1; f x_1 x_2; ...; f x_n-1 x_n]                 *)
(*       zip s t == itemwise pairing of s and t (dropping any extra items).   *)
(*               := [:: (x_1, y_1); ...; (x_mn, y_mn)] with mn = minn n m.    *)
(*      unzip1 s == [:: (x_1).1; ...; (x_n).1] when s : seq (S * T).          *)
(*      unzip2 s == [:: (x_1).2; ...; (x_n).2] when s : seq (S * T).          *)
(*     flatten s == x_1 ++ ... ++ x_n ++ [::] when s : seq (seq T).           *)
(*   reshape r s == s reshaped into a sequence of sequences whose sizes are   *)
(*                  given by r (truncating if s is too long or too short).    *)
(*               := [:: [:: x_1; ...; x_r1];                                  *)
(*                      [:: x_(r1 + 1); ...; x_(r0 + r1)];                    *)
(*                      ...;                                                  *)
(*                      [:: x_(r1 + ... + r(k-1) + 1); ...; x_(r0 + ... rk)]] *)
(* flatten_index sh r c == the index, in flatten ss, of the item of indexes   *)
(*                  (r, c) in any sequence of sequences ss of shape sh        *)
(*               := sh_1 + sh_2 + ... + sh_r + c                              *)
(* reshape_index sh i == the index, in reshape sh s, of the sequence          *)
(*                  containing the i-th item of s.                            *)
(* reshape_offset sh i == the offset, in the (reshape_index sh i)-th          *)
(*                  sequence of reshape sh s of the i-th item of s            *)
(*  ** Notation for manifest comprehensions:                                  *)
(*         [seq x <- s | C] := filter (fun x => C) s.                         *)
(*         [seq E | x <- s] := map (fun x => E) s.                            *)
(*   [seq x <- s | C1 & C2] := [seq x <- s | C1 && C2].                       *)
(*     [seq E | x <- s & C] := [seq E | x <- [seq x | C]].                    *)
(*  --> The above allow optional type casts on the eigenvariables, as in      *)
(*  [seq x : T <- s | C] or [seq E | x : T <- s, y : U <- t]. The cast may be *)
(*  needed as type inference considers E or C before s.                       *)
(*   We are quite systematic in providing lemmas to rewrite any composition   *)
(* of two operations. "rev", whose simplifications are not natural, is        *)
(* protected with nosimpl.                                                    *)
(*  ** The following are equivalent:                                          *)
(*  [<-> P0; P1; ..; Pn] <-> P0, P1, ..., Pn are all equivalent.              *)
(*                       := P0 -> P1 -> ... -> Pn -> P0                       *)
(*  if T : [<-> P0; P1; ..; Pn]  is such an equivalence, and i, j are in nat  *)
(*  then T i j is a proof of the equivalence Pi <-> Pj between Pi and Pj;     *)
(*  when i (resp. j) is out of bounds, Pi (resp. Pj) defaults to P0.          *)
(*  The tactic tfae splits the goal into n+1 implications to prove.           *)
(*  An example of use can be found in fingraph theorem orbitPcycle.           *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope seq_scope.

Reserved Notation "[ '<->' P0 ; P1 ; .. ; Pn ]"
  (at level 0, format "[ '<->' '['  P0 ;  '/' P1 ;  '/'  .. ;  '/'  Pn ']' ]").

Delimit Scope seq_scope with SEQ.
Open Scope seq_scope.

(* Inductive seq (T : Type) : Type := Nil | Cons of T & seq T. *)
Notation seq := list.
Bind Scope seq_scope with list.
Arguments cons {T%type} x s%SEQ : rename.
Arguments nil {T%type} : rename.
Notation Cons T := (@cons T) (only parsing).
Notation Nil T := (@nil T) (only parsing).

(* As :: and ++ are (improperly) declared in Init.datatypes, we only rebind   *)
(* them here.                                                                 *)
Infix "::" := cons : seq_scope.

Notation "[ :: ]" := nil (at level 0, format "[ :: ]") : seq_scope.

Notation "[ :: x1 ]" := (x1 :: [::])
  (at level 0, format "[ ::  x1 ]") : seq_scope.

Notation "[ :: x & s ]" := (x :: s) (at level 0, only parsing) : seq_scope.

Notation "[ :: x1 , x2 , .. , xn & s ]" := (x1 :: x2 :: .. (xn :: s) ..)
  (at level 0, format
  "'[hv' [ :: '['  x1 , '/'  x2 , '/'  .. , '/'  xn ']' '/ '  &  s ] ']'"
  ) : seq_scope.

Notation "[ :: x1 ; x2 ; .. ; xn ]" := (x1 :: x2 :: .. [:: xn] ..)
  (at level 0, format "[ :: '['  x1 ; '/'  x2 ; '/'  .. ; '/'  xn ']' ]"
  ) : seq_scope.

Section Sequences.

Variable n0 : nat.  (* numerical parameter for take, drop et al *)
Variable T : Type.  (* must come before the implicit Type     *)
Variable x0 : T.    (* default for head/nth *)

Implicit Types x y z : T.
Implicit Types m n : nat.
Implicit Type s : seq T.

Fixpoint size s := if s is _ :: s' then (size s').+1 else 0.

Lemma size0nil s : size s = 0 -> s = [::]. Proof. by case: s. Qed.

Definition nilp s := size s == 0.

Lemma nilP s : reflect (s = [::]) (nilp s).
Proof. by case: s => [|x s]; constructor. Qed.

Definition ohead s := if s is x :: _ then Some x else None.
Definition head s := if s is x :: _ then x else x0.

Definition behead s := if s is _ :: s' then s' else [::].

Lemma size_behead s : size (behead s) = (size s).-1.
Proof. by case: s. Qed.

(* Factories *)

Definition ncons n x := iter n (cons x).
Definition nseq n x := ncons n x [::].

Lemma size_ncons n x s : size (ncons n x s) = n + size s.
Proof. by elim: n => //= n ->. Qed.

Lemma size_nseq n x : size (nseq n x) = n.
Proof. by rewrite size_ncons addn0. Qed.

(* n-ary, dependently typed constructor. *)

Fixpoint seqn_type n := if n is n'.+1 then T -> seqn_type n' else seq T.

Fixpoint seqn_rec f n : seqn_type n :=
  if n is n'.+1 return seqn_type n then
    fun x => seqn_rec (fun s => f (x :: s)) n'
  else f [::].
Definition seqn := seqn_rec id.

(* Sequence catenation "cat".                                               *)

Fixpoint cat s1 s2 := if s1 is x :: s1' then x :: s1' ++ s2 else s2
where "s1 ++ s2" := (cat s1 s2) : seq_scope.

Lemma cat0s s : [::] ++ s = s. Proof. by []. Qed.
Lemma cat1s x s : [:: x] ++ s = x :: s. Proof. by []. Qed.
Lemma cat_cons x s1 s2 : (x :: s1) ++ s2 = x :: s1 ++ s2. Proof. by []. Qed.

Lemma cat_nseq n x s : nseq n x ++ s = ncons n x s.
Proof. by elim: n => //= n ->. Qed.

Lemma nseqD n1 n2 x : nseq (n1 + n2) x = nseq n1 x ++ nseq n2 x.
Proof. by rewrite cat_nseq /nseq /ncons iterD. Qed.

Lemma cats0 s : s ++ [::] = s.
Proof. by elim: s => //= x s ->. Qed.

Lemma catA s1 s2 s3 : s1 ++ s2 ++ s3 = (s1 ++ s2) ++ s3.
Proof. by elim: s1 => //= x s1 ->. Qed.

Lemma size_cat s1 s2 : size (s1 ++ s2) = size s1 + size s2.
Proof. by elim: s1 => //= x s1 ->. Qed.

Lemma cat_nilp s1 s2 : nilp (s1 ++ s2) = nilp s1 && nilp s2.
Proof. by case: s1. Qed.

(* last, belast, rcons, and last induction. *)

Fixpoint rcons s z := if s is x :: s' then x :: rcons s' z else [:: z].

Lemma rcons_cons x s z : rcons (x :: s) z = x :: rcons s z.
Proof. by []. Qed.

Lemma cats1 s z : s ++ [:: z] = rcons s z.
Proof. by elim: s => //= x s ->. Qed.

Fixpoint last x s := if s is x' :: s' then last x' s' else x.
Fixpoint belast x s := if s is x' :: s' then x :: (belast x' s') else [::].

Lemma lastI x s : x :: s = rcons (belast x s) (last x s).
Proof. by elim: s x => [|y s IHs] x //=; rewrite IHs. Qed.

Lemma last_cons x y s : last x (y :: s) = last y s.
Proof. by []. Qed.

Lemma size_rcons s x : size (rcons s x) = (size s).+1.
Proof. by rewrite -cats1 size_cat addnC. Qed.

Lemma size_belast x s : size (belast x s) = size s.
Proof. by elim: s x => [|y s IHs] x //=; rewrite IHs. Qed.

Lemma last_cat x s1 s2 : last x (s1 ++ s2) = last (last x s1) s2.
Proof. by elim: s1 x => [|y s1 IHs] x //=; rewrite IHs. Qed.

Lemma last_rcons x s z : last x (rcons s z) = z.
Proof. by rewrite -cats1 last_cat. Qed.

Lemma belast_cat x s1 s2 :
  belast x (s1 ++ s2) = belast x s1 ++ belast (last x s1) s2.
Proof. by elim: s1 x => [|y s1 IHs] x //=; rewrite IHs. Qed.

Lemma belast_rcons x s z : belast x (rcons s z) = x :: s.
Proof. by rewrite lastI -!cats1 belast_cat. Qed.

Lemma cat_rcons x s1 s2 : rcons s1 x ++ s2 = s1 ++ x :: s2.
Proof. by rewrite -cats1 -catA. Qed.

Lemma rcons_cat x s1 s2 : rcons (s1 ++ s2) x = s1 ++ rcons s2 x.
Proof. by rewrite -!cats1 catA. Qed.

Variant last_spec : seq T -> Type :=
  | LastNil        : last_spec [::]
  | LastRcons s x  : last_spec (rcons s x).

Lemma lastP s : last_spec s.
Proof. case: s => [|x s]; [left | rewrite lastI; right]. Qed.

Lemma last_ind P :
  P [::] -> (forall s x, P s -> P (rcons s x)) -> forall s, P s.
Proof.
move=> Hnil Hlast s; rewrite -(cat0s s).
elim: s [::] Hnil => [|x s2 IHs] s1 Hs1; first by rewrite cats0.
by rewrite -cat_rcons; apply/IHs/Hlast.
Qed.

(* Sequence indexing. *)

Fixpoint nth s n {struct n} :=
  if s is x :: s' then if n is n'.+1 then @nth s' n' else x else x0.

Fixpoint set_nth s n y {struct n} :=
  if s is x :: s' then if n is n'.+1 then x :: @set_nth s' n' y else y :: s'
  else ncons n x0 [:: y].

Lemma nth0 s : nth s 0 = head s. Proof. by []. Qed.

Lemma nth_default s n : size s <= n -> nth s n = x0.
Proof. by elim: s n => [|x s IHs] []. Qed.

Lemma if_nth s b n : b || (size s <= n) ->
  (if b then nth s n else x0) = nth s n.
Proof. by case: leqP; case: ifP => //= *; rewrite nth_default. Qed.

Lemma nth_nil n : nth [::] n = x0.
Proof. by case: n. Qed.

Lemma nth_seq1 n x : nth [:: x] n = if n == 0 then x else x0.
Proof. by case: n => [|[]]. Qed.

Lemma last_nth x s : last x s = nth (x :: s) (size s).
Proof. by elim: s x => [|y s IHs] x /=. Qed.

Lemma nth_last s : nth s (size s).-1 = last x0 s.
Proof. by case: s => //= x s; rewrite last_nth. Qed.

Lemma nth_behead s n : nth (behead s) n = nth s n.+1.
Proof. by case: s n => [|x s] [|n]. Qed.

Lemma nth_cat s1 s2 n :
  nth (s1 ++ s2) n = if n < size s1 then nth s1 n else nth s2 (n - size s1).
Proof. by elim: s1 n => [|x s1 IHs] []. Qed.

Lemma nth_rcons s x n :
  nth (rcons s x) n =
    if n < size s then nth s n else if n == size s then x else x0.
Proof. by elim: s n => [|y s IHs] [] //=; apply: nth_nil. Qed.

Lemma nth_rcons_default s i : nth (rcons s x0) i = nth s i.
Proof.
by rewrite nth_rcons; case: ltngtP => //[/ltnW ?|->]; rewrite nth_default.
Qed.

Lemma nth_ncons m x s n :
  nth (ncons m x s) n = if n < m then x else nth s (n - m).
Proof. by elim: m n => [|m IHm] []. Qed.

Lemma nth_nseq m x n : nth (nseq m x) n = (if n < m then x else x0).
Proof. by elim: m n => [|m IHm] []. Qed.

Lemma eq_from_nth s1 s2 :
    size s1 = size s2 -> (forall i, i < size s1 -> nth s1 i = nth s2 i) ->
  s1 = s2.
Proof.
elim: s1 s2 => [|x1 s1 IHs1] [|x2 s2] //= [eq_sz] eq_s12.
by rewrite [x1](eq_s12 0) // (IHs1 s2) // => i; apply: (eq_s12 i.+1).
Qed.

Lemma size_set_nth s n y : size (set_nth s n y) = maxn n.+1 (size s).
Proof.
rewrite maxnC; elim: s n => [|x s IHs] [|n] //=.
- by rewrite size_ncons addn1.
- by rewrite IHs maxnSS.
Qed.

Lemma set_nth_nil n y : set_nth [::] n y = ncons n x0 [:: y].
Proof. by case: n. Qed.

Lemma nth_set_nth s n y : nth (set_nth s n y) =1 [eta nth s with n |-> y].
Proof.
elim: s n => [|x s IHs] [|n] [|m] //=; rewrite ?nth_nil ?IHs // nth_ncons eqSS.
case: ltngtP => // [lt_nm | ->]; last by rewrite subnn.
by rewrite nth_default // subn_gt0.
Qed.

Lemma set_set_nth s n1 y1 n2 y2 (s2 := set_nth s n2 y2) :
  set_nth (set_nth s n1 y1) n2 y2 = if n1 == n2 then s2 else set_nth s2 n1 y1.
Proof.
have [-> | ne_n12] := eqVneq.
  apply: eq_from_nth => [|i _]; first by rewrite !size_set_nth maxnA maxnn.
  by do 2!rewrite !nth_set_nth /=; case: eqP.
apply: eq_from_nth => [|i _]; first by rewrite !size_set_nth maxnCA.
by do 2!rewrite !nth_set_nth /=; case: eqP => // ->; case: eqVneq ne_n12.
Qed.

(* find, count, has, all. *)

Section SeqFind.

Variable a : pred T.

Fixpoint find s := if s is x :: s' then if a x then 0 else (find s').+1 else 0.

Fixpoint filter s :=
  if s is x :: s' then if a x then x :: filter s' else filter s' else [::].

Fixpoint count s := if s is x :: s' then a x + count s' else 0.

Fixpoint has s := if s is x :: s' then a x || has s' else false.

Fixpoint all s := if s is x :: s' then a x && all s' else true.

Lemma size_filter s : size (filter s) = count s.
Proof. by elim: s => //= x s <-; case (a x). Qed.

Lemma has_count s : has s = (0 < count s).
Proof. by elim: s => //= x s ->; case (a x). Qed.

Lemma count_size s : count s <= size s.
Proof. by elim: s => //= x s; case: (a x); last apply: leqW. Qed.

Lemma all_count s : all s = (count s == size s).
Proof.
elim: s => //= x s; case: (a x) => _ //=.
by rewrite add0n eqn_leq andbC ltnNge count_size.
Qed.

Lemma filter_all s : all (filter s).
Proof. by elim: s => //= x s IHs; case: ifP => //= ->. Qed.

Lemma all_filterP s : reflect (filter s = s) (all s).
Proof.
apply: (iffP idP) => [| <-]; last exact: filter_all.
by elim: s => //= x s IHs /andP[-> Hs]; rewrite IHs.
Qed.

Lemma filter_id s : filter (filter s) = filter s.
Proof. by apply/all_filterP; apply: filter_all. Qed.

Lemma has_find s : has s = (find s < size s).
Proof. by elim: s => //= x s IHs; case (a x); rewrite ?leqnn. Qed.

Lemma find_size s : find s <= size s.
Proof. by elim: s => //= x s IHs; case (a x). Qed.

Lemma find_cat s1 s2 :
  find (s1 ++ s2) = if has s1 then find s1 else size s1 + find s2.
Proof.
by elim: s1 => //= x s1 IHs; case: (a x) => //; rewrite IHs (fun_if succn).
Qed.

Lemma has_nil : has [::] = false. Proof. by []. Qed.

Lemma has_seq1 x : has [:: x] = a x.
Proof. exact: orbF. Qed.

Lemma has_nseq n x : has (nseq n x) = (0 < n) && a x.
Proof. by elim: n => //= n ->; apply: andKb. Qed.

Lemma has_seqb (b : bool) x : has (nseq b x) = b && a x.
Proof. by rewrite has_nseq lt0b. Qed.

Lemma all_nil : all [::] = true. Proof. by []. Qed.

Lemma all_seq1 x : all [:: x] = a x.
Proof. exact: andbT. Qed.

Lemma all_nseq n x : all (nseq n x) = (n == 0) || a x.
Proof. by elim: n => //= n ->; apply: orKb. Qed.

Lemma all_nseqb (b : bool) x : all (nseq b x) = b ==> a x.
Proof. by rewrite all_nseq eqb0 implybE. Qed.

Lemma filter_nseq n x : filter (nseq n x) = nseq (a x * n) x.
Proof. by elim: n => /= [|n ->]; case: (a x). Qed.

Lemma count_nseq n x : count (nseq n x) = a x * n.
Proof. by rewrite -size_filter filter_nseq size_nseq. Qed.

Lemma find_nseq n x : find (nseq n x) = ~~ a x * n.
Proof. by elim: n => /= [|n ->]; case: (a x). Qed.

Lemma nth_find s : has s -> a (nth s (find s)).
Proof. by elim: s => //= x s IHs; case a_x: (a x). Qed.

Lemma before_find s i : i < find s -> a (nth s i) = false.
Proof. by elim: s i => //= x s IHs; case: ifP => // a'x [|i] // /(IHs i). Qed.

Lemma hasNfind s : ~~ has s -> find s = size s.
Proof. by rewrite has_find; case: ltngtP (find_size s). Qed.

Lemma filter_cat s1 s2 : filter (s1 ++ s2) = filter s1 ++ filter s2.
Proof. by elim: s1 => //= x s1 ->; case (a x). Qed.

Lemma filter_rcons s x :
  filter (rcons s x) = if a x then rcons (filter s) x else filter s.
Proof. by rewrite -!cats1 filter_cat /=; case (a x); rewrite /= ?cats0. Qed.

Lemma count_cat s1 s2 : count (s1 ++ s2) = count s1 + count s2.
Proof. by rewrite -!size_filter filter_cat size_cat. Qed.

Lemma has_cat s1 s2 : has (s1 ++ s2) = has s1 || has s2.
Proof. by elim: s1 => [|x s1 IHs] //=; rewrite IHs orbA. Qed.

Lemma has_rcons s x : has (rcons s x) = a x || has s.
Proof. by rewrite -cats1 has_cat has_seq1 orbC. Qed.

Lemma all_cat s1 s2 : all (s1 ++ s2) = all s1 && all s2.
Proof. by elim: s1 => [|x s1 IHs] //=; rewrite IHs andbA. Qed.

Lemma all_rcons s x : all (rcons s x) = a x && all s.
Proof. by rewrite -cats1 all_cat all_seq1 andbC. Qed.

End SeqFind.

Lemma eq_find a1 a2 : a1 =1 a2 -> find a1 =1 find a2.
Proof. by move=> Ea; elim=> //= x s IHs; rewrite Ea IHs. Qed.

Lemma eq_filter a1 a2 : a1 =1 a2 -> filter a1 =1 filter a2.
Proof. by move=> Ea; elim=> //= x s IHs; rewrite Ea IHs. Qed.

Lemma eq_count a1 a2 : a1 =1 a2 -> count a1 =1 count a2.
Proof. by move=> Ea s; rewrite -!size_filter (eq_filter Ea). Qed.

Lemma eq_has a1 a2 : a1 =1 a2 -> has a1 =1 has a2.
Proof. by move=> Ea s; rewrite !has_count (eq_count Ea). Qed.

Lemma eq_all a1 a2 : a1 =1 a2 -> all a1 =1 all a2.
Proof. by move=> Ea s; rewrite !all_count (eq_count Ea). Qed.

Lemma all_filter (p q : pred T) xs :
  all p (filter q xs) = all [pred i | q i ==> p i] xs.
Proof. by elim: xs => //= x xs <-; case: (q x). Qed.

Section SubPred.

Variable (a1 a2 : pred T).
Hypothesis s12 : subpred a1 a2.

Lemma sub_find s : find a2 s <= find a1 s.
Proof. by elim: s => //= x s IHs; case: ifP => // /(contraFF (@s12 x))->. Qed.

Lemma sub_has s : has a1 s -> has a2 s.
Proof. by rewrite !has_find; apply: leq_ltn_trans (sub_find s). Qed.

Lemma sub_count s : count a1 s <= count a2 s.
Proof.
by elim: s => //= x s; apply: leq_add; case a1x: (a1 x); rewrite // s12.
Qed.

Lemma sub_all s : all a1 s -> all a2 s.
Proof.
by rewrite !all_count !eqn_leq !count_size => /leq_trans-> //; apply: sub_count.
Qed.

End SubPred.

Lemma filter_pred0 s : filter pred0 s = [::]. Proof. by elim: s. Qed.

Lemma filter_predT s : filter predT s = s.
Proof. by elim: s => //= x s ->. Qed.

Lemma filter_predI a1 a2 s : filter (predI a1 a2) s = filter a1 (filter a2 s).
Proof. by elim: s => //= x s ->; rewrite andbC; case: (a2 x). Qed.

Lemma count_pred0 s : count pred0 s = 0.
Proof. by rewrite -size_filter filter_pred0. Qed.

Lemma count_predT s : count predT s = size s.
Proof. by rewrite -size_filter filter_predT. Qed.

Lemma count_predUI a1 a2 s :
  count (predU a1 a2) s + count (predI a1 a2) s = count a1 s + count a2 s.
Proof.
elim: s => //= x s IHs; rewrite /= addnACA [RHS]addnACA IHs.
by case: (a1 x) => //; rewrite addn0.
Qed.

Lemma count_predC a s : count a s + count (predC a) s = size s.
Proof. by elim: s => //= x s IHs; rewrite addnACA IHs; case: (a _). Qed.

Lemma count_filter a1 a2 s : count a1 (filter a2 s) = count (predI a1 a2) s.
Proof. by rewrite -!size_filter filter_predI. Qed.

Lemma has_pred0 s : has pred0 s = false.
Proof. by rewrite has_count count_pred0. Qed.

Lemma has_predT s : has predT s = (0 < size s).
Proof. by rewrite has_count count_predT. Qed.

Lemma has_predC a s : has (predC a) s = ~~ all a s.
Proof. by elim: s => //= x s ->; case (a x). Qed.

Lemma has_predU a1 a2 s : has (predU a1 a2) s = has a1 s || has a2 s.
Proof. by elim: s => //= x s ->; rewrite -!orbA; do !bool_congr. Qed.

Lemma all_pred0 s : all pred0 s = (size s == 0).
Proof. by rewrite all_count count_pred0 eq_sym. Qed.

Lemma all_predT s : all predT s.
Proof. by rewrite all_count count_predT. Qed.

Lemma allT (a : pred T) s : (forall x, a x) -> all a s.
Proof. by move/eq_all->; apply/all_predT. Qed.

Lemma all_predC a s : all (predC a) s = ~~ has a s.
Proof. by elim: s => //= x s ->; case (a x). Qed.

Lemma all_predI a1 a2 s : all (predI a1 a2) s = all a1 s && all a2 s.
Proof.
apply: (can_inj negbK); rewrite negb_and -!has_predC -has_predU.
by apply: eq_has => x; rewrite /= negb_and.
Qed.

(* Surgery: drop, take, rot, rotr.                                        *)

Fixpoint drop n s {struct s} :=
  match s, n with
  | _ :: s', n'.+1 => drop n' s'
  | _, _ => s
  end.

Lemma drop_behead : drop n0 =1 iter n0 behead.
Proof. by elim: n0 => [|n IHn] [|x s] //; rewrite iterSr -IHn. Qed.

Lemma drop0 s : drop 0 s = s. Proof. by case: s. Qed.

Lemma drop1 : drop 1 =1 behead. Proof. by case=> [|x [|y s]]. Qed.

Lemma drop_oversize n s : size s <= n -> drop n s = [::].
Proof. by elim: s n => [|x s IHs] []. Qed.

Lemma drop_size s : drop (size s) s = [::].
Proof. by rewrite drop_oversize // leqnn. Qed.

Lemma drop_cons x s :
  drop n0 (x :: s) = if n0 is n.+1 then drop n s else x :: s.
Proof. by []. Qed.

Lemma size_drop s : size (drop n0 s) = size s - n0.
Proof. by elim: s n0 => [|x s IHs] []. Qed.

Lemma drop_cat s1 s2 :
  drop n0 (s1 ++ s2) =
    if n0 < size s1 then drop n0 s1 ++ s2 else drop (n0 - size s1) s2.
Proof. by elim: s1 n0 => [|x s1 IHs] []. Qed.

Lemma drop_size_cat n s1 s2 : size s1 = n -> drop n (s1 ++ s2) = s2.
Proof. by move <-; elim: s1 => //=; rewrite drop0. Qed.

Lemma nconsK n x : cancel (ncons n x) (drop n).
Proof. by elim: n => // -[]. Qed.

Lemma drop_drop s n1 n2 : drop n1 (drop n2 s) = drop (n1 + n2) s.
Proof. by elim: s n2 => // x s ihs [|n2]; rewrite ?drop0 ?addn0 ?addnS /=. Qed.

Fixpoint take n s {struct s} :=
  match s, n with
  | x :: s', n'.+1 => x :: take n' s'
  | _, _ => [::]
  end.

Lemma take0 s : take 0 s = [::]. Proof. by case: s. Qed.

Lemma take_oversize n s : size s <= n -> take n s = s.
Proof. by elim: s n => [|x s IHs] [|n] //= /IHs->. Qed.

Lemma take_size s : take (size s) s = s.
Proof. exact: take_oversize. Qed.

Lemma take_cons x s :
  take n0 (x :: s) = if n0 is n.+1 then x :: (take n s) else [::].
Proof. by []. Qed.

Lemma drop_rcons s : n0 <= size s ->
  forall x, drop n0 (rcons s x) = rcons (drop n0 s) x.
Proof. by elim: s n0 => [|y s IHs] []. Qed.

Lemma cat_take_drop s : take n0 s ++ drop n0 s = s.
Proof. by elim: s n0 => [|x s IHs] [|n] //=; rewrite IHs. Qed.

Lemma size_takel s : n0 <= size s -> size (take n0 s) = n0.
Proof.
by move/subKn; rewrite -size_drop -[in size s](cat_take_drop s) size_cat addnK.
Qed.

Lemma size_take s : size (take n0 s) = if n0 < size s then n0 else size s.
Proof.
have [le_sn | lt_ns] := leqP (size s) n0; first by rewrite take_oversize.
by rewrite size_takel // ltnW.
Qed.

Lemma size_take_min s : size (take n0 s) = minn n0 (size s).
Proof. exact: size_take. Qed.

Lemma take_cat s1 s2 :
  take n0 (s1 ++ s2) =
    if n0 < size s1 then take n0 s1 else s1 ++ take (n0 - size s1) s2.
Proof.
elim: s1 n0 => [|x s1 IHs] [|n] //=.
by rewrite ltnS subSS -(fun_if (cons x)) -IHs.
Qed.

Lemma take_size_cat n s1 s2 : size s1 = n -> take n (s1 ++ s2) = s1.
Proof. by move <-; elim: s1 => [|x s1 IHs]; rewrite ?take0 //= IHs. Qed.

Lemma takel_cat s1 s2 : n0 <= size s1 -> take n0 (s1 ++ s2) = take n0 s1.
Proof.
by rewrite take_cat; case: ltngtP => // ->; rewrite subnn take0 take_size cats0.
Qed.

Lemma nth_drop s i : nth (drop n0 s) i = nth s (n0 + i).
Proof.
rewrite -[s in RHS]cat_take_drop nth_cat size_take ltnNge.
case: ltnP => [?|le_s_n0]; rewrite ?(leq_trans le_s_n0) ?leq_addr ?addKn //=.
by rewrite drop_oversize // !nth_default.
Qed.

Lemma find_ltn p s i : has p (take i s) -> find p s < i.
Proof. by elim: s i => [|y s ihs] [|i]//=; case: (p _) => //= /ihs. Qed.

Lemma has_take p s i : has p s -> has p (take i s) = (find p s < i).
Proof. by elim: s i => [|y s ihs] [|i]//=; case: (p _) => //= /ihs ->. Qed.

Lemma has_take_leq (p : pred T) (s : seq T) i : i <= size s ->
  has p (take i s) = (find p s < i).
Proof. by elim: s i => [|y s ihs] [|i]//=; case: (p _) => //= /ihs ->. Qed.

Lemma nth_take i : i < n0 -> forall s, nth (take n0 s) i = nth s i.
Proof.
move=> lt_i_n0 s; case lt_n0_s: (n0 < size s).
  by rewrite -[s in RHS]cat_take_drop nth_cat size_take lt_n0_s /= lt_i_n0.
by rewrite -[s in LHS]cats0 take_cat lt_n0_s /= cats0.
Qed.

Lemma take_min i j s : take (minn i j) s = take i (take j s).
Proof. by elim: s i j => //= a l IH [|i] [|j] //=; rewrite minnSS IH. Qed.

Lemma take_takel i j s : i <= j -> take i (take j s) = take i s.
Proof. by move=> ?; rewrite -take_min (minn_idPl _). Qed.

Lemma take_taker i j s : j <= i -> take i (take j s) = take j s.
Proof. by move=> ?; rewrite -take_min (minn_idPr _). Qed.

Lemma take_drop i j s : take i (drop j s) = drop j (take (i + j) s).
Proof. by rewrite addnC; elim: s i j => // x s IHs [|i] [|j] /=. Qed.

Lemma takeD i j s : take (i + j) s = take i s ++ take j (drop i s).
Proof.
elim: i j s => [|i IHi] [|j] [|a s] //; first by rewrite take0 addn0 cats0.
by rewrite addSn /= IHi.
Qed.

Lemma takeC i j s : take i (take j s) = take j (take i s).
Proof. by rewrite -!take_min minnC. Qed.

Lemma take_nseq i j x : i <= j -> take i (nseq j x) = nseq i x.
Proof. by move=>/subnKC <-; rewrite nseqD take_size_cat // size_nseq. Qed.

Lemma drop_nseq i j x : drop i (nseq j x) = nseq (j - i) x.
Proof.
case: (leqP i j) => [/subnKC {1}<-|/ltnW j_le_i].
  by rewrite nseqD drop_size_cat // size_nseq.
by rewrite drop_oversize ?size_nseq // (eqP j_le_i).
Qed.

(* drop_nth and take_nth below do NOT use the default n0, because the "n"  *)
(* can be inferred from the condition, whereas the nth default value x0    *)
(* will have to be given explicitly (and this will provide "d" as well).   *)

Lemma drop_nth n s : n < size s -> drop n s = nth s n :: drop n.+1 s.
Proof. by elim: s n => [|x s IHs] [|n] Hn //=; rewrite ?drop0 1?IHs. Qed.

Lemma take_nth n s : n < size s -> take n.+1 s = rcons (take n s) (nth s n).
Proof. by elim: s n => [|x s IHs] //= [|n] Hn /=; rewrite ?take0 -?IHs. Qed.

(* Rotation *)

Definition rot n s := drop n s ++ take n s.

Lemma rot0 s : rot 0 s = s.
Proof. by rewrite /rot drop0 take0 cats0. Qed.

Lemma size_rot s : size (rot n0 s) = size s.
Proof. by rewrite -[s in RHS]cat_take_drop /rot !size_cat addnC. Qed.

Lemma rot_oversize n s : size s <= n -> rot n s = s.
Proof. by move=> le_s_n; rewrite /rot take_oversize ?drop_oversize. Qed.

Lemma rot_size s : rot (size s) s = s.
Proof. exact: rot_oversize. Qed.

Lemma has_rot s a : has a (rot n0 s) = has a s.
Proof. by rewrite has_cat orbC -has_cat cat_take_drop. Qed.

Lemma rot_size_cat s1 s2 : rot (size s1) (s1 ++ s2) = s2 ++ s1.
Proof. by rewrite /rot take_size_cat ?drop_size_cat. Qed.

Definition rotr n s := rot (size s - n) s.

Lemma rotK : cancel (rot n0) (rotr n0).
Proof.
move=> s; rewrite /rotr size_rot -size_drop {2}/rot.
by rewrite rot_size_cat cat_take_drop.
Qed.

Lemma rot_inj : injective (rot n0). Proof. exact (can_inj rotK). Qed.

(* (efficient) reversal *)

Fixpoint catrev s1 s2 := if s1 is x :: s1' then catrev s1' (x :: s2) else s2.

Definition rev s := catrev s [::].

Lemma catrev_catl s t u : catrev (s ++ t) u = catrev t (catrev s u).
Proof. by elim: s u => /=. Qed.

Lemma catrev_catr s t u : catrev s (t ++ u) = catrev s t ++ u.
Proof. by elim: s t => //= x s IHs t; rewrite -IHs. Qed.

Lemma catrevE s t : catrev s t = rev s ++ t.
Proof. by rewrite -catrev_catr. Qed.

Lemma rev_cons x s : rev (x :: s) = rcons (rev s) x.
Proof. by rewrite -cats1 -catrevE. Qed.

Lemma size_rev s : size (rev s) = size s.
Proof. by elim: s => // x s IHs; rewrite rev_cons size_rcons IHs. Qed.

Lemma rev_nilp s : nilp (rev s) = nilp s.
Proof. by move: s (rev s) (size_rev s) => [|? ?] []. Qed.

Lemma rev_cat s t : rev (s ++ t) = rev t ++ rev s.
Proof. by rewrite -catrev_catr -catrev_catl. Qed.

Lemma rev_rcons s x : rev (rcons s x) = x :: rev s.
Proof. by rewrite -cats1 rev_cat. Qed.

Lemma revK : involutive rev.
Proof. by elim=> //= x s IHs; rewrite rev_cons rev_rcons IHs. Qed.

Lemma nth_rev n s : n < size s -> nth (rev s) n = nth s (size s - n.+1).
Proof.
elim/last_ind: s => // s x IHs in n *.
rewrite rev_rcons size_rcons ltnS subSS -cats1 nth_cat /=.
case: n => [|n] lt_n_s; first by rewrite subn0 ltnn subnn.
by rewrite subnSK //= leq_subr IHs.
Qed.

Lemma filter_rev a s : filter a (rev s) = rev (filter a s).
Proof. by elim: s => //= x s IH; rewrite fun_if !rev_cons filter_rcons IH. Qed.

Lemma count_rev a s : count a (rev s) = count a s.
Proof. by rewrite -!size_filter filter_rev size_rev. Qed.

Lemma has_rev a s : has a (rev s) = has a s.
Proof. by rewrite !has_count count_rev. Qed.

Lemma all_rev a s : all a (rev s) = all a s.
Proof. by rewrite !all_count count_rev size_rev. Qed.

Lemma rev_nseq n x : rev (nseq n x) = nseq n x.
Proof. by elim: n => // n IHn; rewrite -[in LHS]addn1 nseqD rev_cat IHn. Qed.

End Sequences.

Prenex Implicits size ncons nseq head ohead behead last rcons belast.
Arguments seqn {T} n.
Prenex Implicits cat take drop rot rotr catrev.
Prenex Implicits find count nth all has filter.
Arguments rev {T} s : simpl never.
Arguments nth : simpl nomatch.
Arguments set_nth : simpl nomatch.
Arguments take : simpl nomatch.
Arguments drop : simpl nomatch.

Arguments nilP {T s}.
Arguments all_filterP {T a s}.
Arguments rotK n0 {T} s : rename.
Arguments rot_inj {n0 T} [s1 s2] eq_rot_s12 : rename.
Arguments revK {T} s : rename.

Notation count_mem x := (count (pred_of_simpl (pred1 x))).

Infix "++" := cat : seq_scope.

Notation "[ 'seq' x <- s | C ]" := (filter (fun x => C%B) s)
 (at level 0, x at level 99,
  format "[ '[hv' 'seq'  x  <-  s '/ '  |  C ] ']'") : seq_scope.
Notation "[ 'seq' x <- s | C1 & C2 ]" := [seq x <- s | C1 && C2]
 (at level 0, x at level 99,
  format "[ '[hv' 'seq'  x  <-  s '/ '  |  C1 '/ '  &  C2 ] ']'") : seq_scope.
Notation "[ 'seq' x : T <- s | C ]" := (filter (fun x : T => C%B) s)
 (at level 0, x at level 99, only parsing).
Notation "[ 'seq' x : T <- s | C1 & C2 ]" := [seq x : T <- s | C1 && C2]
 (at level 0, x at level 99, only parsing).

#[deprecated(since="mathcomp 1.16",
             note="Use take_takel or take_min instead")]
Notation take_take := take_takel.

(* Double induction/recursion. *)
Lemma seq_ind2 {S T} (P : seq S -> seq T -> Type) :
    P [::] [::] ->
    (forall x y s t, size s = size t -> P s t -> P (x :: s) (y :: t)) ->
  forall s t, size s = size t -> P s t.
Proof.
by move=> Pnil Pcons; elim=> [|x s IHs] [|y t] //= [eq_sz]; apply/Pcons/IHs.
Qed.

Section FindSpec.
Variable (T : Type) (a : {pred T}) (s : seq T).

Variant find_spec : bool -> nat -> Type :=
| NotFound of ~~ has a s : find_spec false (size s)
| Found (i : nat) of i < size s & (forall x0, a (nth x0 s i)) &
  (forall x0 j, j < i -> a (nth x0 s j) = false) : find_spec true i.

Lemma findP : find_spec (has a s) (find a s).
Proof.
have [a_s|aNs] := boolP (has a s); last by rewrite hasNfind//; constructor.
by constructor=> [|x0|x0]; rewrite -?has_find ?nth_find//; apply: before_find.
Qed.

End FindSpec.
Arguments findP {T}.

Section RotRcons.

Variable T : Type.
Implicit Types (x : T) (s : seq T).

Lemma rot1_cons x s : rot 1 (x :: s) = rcons s x.
Proof. by rewrite /rot /= take0 drop0 -cats1. Qed.

Lemma rcons_inj s1 s2 x1 x2 :
  rcons s1 x1 = rcons s2 x2 :> seq T -> (s1, x1) = (s2, x2).
Proof. by rewrite -!rot1_cons => /rot_inj[-> ->]. Qed.

Lemma rcons_injl x : injective (rcons^~ x).
Proof. by move=> s1 s2 /rcons_inj[]. Qed.

Lemma rcons_injr s : injective (rcons s).
Proof. by move=> x1 x2 /rcons_inj[]. Qed.

End RotRcons.

Arguments rcons_inj {T s1 x1 s2 x2} eq_rcons : rename.
Arguments rcons_injl {T} x [s1 s2] eq_rcons : rename.
Arguments rcons_injr {T} s [x1 x2] eq_rcons : rename.

(* Equality and eqType for seq.                                          *)

Section EqSeq.

Variables (n0 : nat) (T : eqType) (x0 : T).
Local Notation nth := (nth x0).
Implicit Types (x y z : T) (s : seq T).

Fixpoint eqseq s1 s2 {struct s2} :=
  match s1, s2 with
  | [::], [::] => true
  | x1 :: s1', x2 :: s2' => (x1 == x2) && eqseq s1' s2'
  | _, _ => false
  end.

Lemma eqseqP : Equality.axiom eqseq.
Proof.
move; elim=> [|x1 s1 IHs] [|x2 s2]; do [by constructor | simpl].
have [<-|neqx] := x1 =P x2; last by right; case.
by apply: (iffP (IHs s2)) => [<-|[]].
Qed.

HB.instance Definition _ := hasDecEq.Build (seq T) eqseqP.

Lemma eqseqE : eqseq = eq_op. Proof. by []. Qed.

Lemma eqseq_cons x1 x2 s1 s2 :
  (x1 :: s1 == x2 :: s2) = (x1 == x2) && (s1 == s2).
Proof. by []. Qed.

Lemma eqseq_cat s1 s2 s3 s4 :
  size s1 = size s2 -> (s1 ++ s3 == s2 ++ s4) = (s1 == s2) && (s3 == s4).
Proof.
elim: s1 s2 => [|x1 s1 IHs] [|x2 s2] //= [sz12].
by rewrite !eqseq_cons -andbA IHs.
Qed.

Lemma eqseq_rcons s1 s2 x1 x2 :
  (rcons s1 x1 == rcons s2 x2) = (s1 == s2) && (x1 == x2).
Proof. by rewrite -(can_eq revK) !rev_rcons eqseq_cons andbC (can_eq revK). Qed.

Lemma size_eq0 s : (size s == 0) = (s == [::]).
Proof. exact: (sameP nilP eqP). Qed.

Lemma nilpE s : nilp s = (s == [::]). Proof. by case: s. Qed.

Lemma has_filter a s : has a s = (filter a s != [::]).
Proof. by rewrite -size_eq0 size_filter has_count lt0n. Qed.

(* mem_seq and index. *)
(* mem_seq defines a predType for seq. *)

Fixpoint mem_seq (s : seq T) :=
  if s is y :: s' then xpredU1 y (mem_seq s') else xpred0.

Definition seq_eqclass := seq T.
Identity Coercion seq_of_eqclass : seq_eqclass >-> seq.
Coercion pred_of_seq (s : seq_eqclass) : {pred T} := mem_seq s.

Canonical seq_predType := PredType (pred_of_seq : seq T -> pred T).
(* The line below makes mem_seq a canonical instance of topred. *)
Canonical mem_seq_predType := PredType mem_seq.

Lemma in_cons y s x : (x \in y :: s) = (x == y) || (x \in s).
Proof. by []. Qed.

Lemma in_nil x : (x \in [::]) = false.
Proof. by []. Qed.

Lemma mem_seq1 x y : (x \in [:: y]) = (x == y).
Proof. by rewrite in_cons orbF. Qed.

 (* to be repeated after the Section discharge. *)
Let inE := (mem_seq1, in_cons, inE).

Lemma forall_cons {P : T -> Prop} {a s} :
  {in a::s, forall x, P x} <-> P a /\ {in s, forall x, P x}.
Proof.
split=> [A|[A B]]; last by move => x /predU1P [-> //|]; apply: B.
by split=> [|b Hb]; apply: A; rewrite !inE ?eqxx ?Hb ?orbT.
Qed.

Lemma exists_cons {P : T -> Prop} {a s} :
  (exists2 x, x \in a::s & P x) <-> P a \/ exists2 x, x \in s & P x.
Proof.
split=> [[x /predU1P[->|x_s] Px]|]; [by left| by right; exists x|].
by move=> [?|[x x_s ?]]; [exists a|exists x]; rewrite ?inE ?eqxx ?x_s ?orbT.
Qed.

Lemma mem_seq2 x y z : (x \in [:: y; z]) = xpred2 y z x.
Proof. by rewrite !inE. Qed.

Lemma mem_seq3 x y z t : (x \in [:: y; z; t]) = xpred3 y z t x.
Proof. by rewrite !inE. Qed.

Lemma mem_seq4 x y z t u : (x \in [:: y; z; t; u]) = xpred4 y z t u x.
Proof. by rewrite !inE. Qed.

Lemma mem_cat x s1 s2 : (x \in s1 ++ s2) = (x \in s1) || (x \in s2).
Proof. by elim: s1 => //= y s1 IHs; rewrite !inE /= -orbA -IHs. Qed.

Lemma mem_rcons s y : rcons s y =i y :: s.
Proof. by move=> x; rewrite -cats1 /= mem_cat mem_seq1 orbC in_cons. Qed.

Lemma mem_head x s : x \in x :: s.
Proof. exact: predU1l. Qed.

Lemma mem_last x s : last x s \in x :: s.
Proof. by rewrite lastI mem_rcons mem_head. Qed.

Lemma mem_behead s : {subset behead s <= s}.
Proof. by case: s => // y s x; apply: predU1r. Qed.

Lemma mem_belast s y : {subset belast y s <= y :: s}.
Proof. by move=> x ys'x; rewrite lastI mem_rcons mem_behead. Qed.

Lemma mem_nth s n : n < size s -> nth s n \in s.
Proof.
by elim: s n => // x s IHs [_|n sz_s]; rewrite ?mem_head // mem_behead ?IHs.
Qed.

Lemma mem_take s x : x \in take n0 s -> x \in s.
Proof. by move=> s0x; rewrite -(cat_take_drop n0 s) mem_cat /= s0x. Qed.

Lemma mem_drop s x : x \in drop n0 s -> x \in s.
Proof. by move=> s0'x; rewrite -(cat_take_drop n0 s) mem_cat /= s0'x orbT. Qed.

Lemma last_eq s z x y : x != y -> z != y -> (last x s == y) = (last z s == y).
Proof. by move=> /negPf xz /negPf yz; case: s => [|t s]//; rewrite xz yz. Qed.

Section Filters.

Implicit Type a : pred T.

Lemma hasP {a s} : reflect (exists2 x, x \in s & a x) (has a s).
Proof.
elim: s => [|y s IHs] /=; first by right; case.
exact: equivP (orPP idP IHs) (iff_sym exists_cons).
Qed.

Lemma allP {a s} : reflect {in s, forall x, a x} (all a s).
Proof.
elim: s => [|/= y s IHs]; first by left.
exact: equivP (andPP idP IHs) (iff_sym forall_cons).
Qed.

Lemma hasPn a s : reflect {in s, forall x, ~~ a x} (~~ has a s).
Proof. by rewrite -all_predC; apply: allP. Qed.

Lemma allPn a s : reflect (exists2 x, x \in s & ~~ a x) (~~ all a s).
Proof. by rewrite -has_predC; apply: hasP. Qed.

Lemma allss s : all [in s] s. Proof. exact/allP. Qed.

Lemma mem_filter a x s : (x \in filter a s) = a x && (x \in s).
Proof.
rewrite andbC; elim: s => //= y s IHs.
rewrite (fun_if (fun s' : seq T => x \in s')) !in_cons {}IHs.
by case: eqP => [->|_]; case (a y); rewrite /= ?andbF.
Qed.

Variables (a : pred T) (s : seq T) (A : T -> Prop).
Hypothesis aP : forall x, reflect (A x) (a x).

Lemma hasPP : reflect (exists2 x, x \in s & A x) (has a s).
Proof. by apply: (iffP hasP) => -[x ? /aP]; exists x. Qed.

Lemma allPP : reflect {in s, forall x, A x} (all a s).
Proof. by apply: (iffP allP) => a_s x /a_s/aP. Qed.

End Filters.

Notation "'has_ view" := (hasPP _ (fun _ => view))
  (at level 4, right associativity, format "''has_' view").
Notation "'all_ view" := (allPP _ (fun _ => view))
  (at level 4, right associativity, format "''all_' view").

Section EqIn.

Variables a1 a2 : pred T.

Lemma eq_in_filter s : {in s, a1 =1 a2} -> filter a1 s = filter a2 s.
Proof. by elim: s => //= x s IHs /forall_cons [-> /IHs ->]. Qed.

Lemma eq_in_find s : {in s, a1 =1 a2} -> find a1 s = find a2 s.
Proof. by elim: s => //= x s IHs /forall_cons [-> /IHs ->]. Qed.

Lemma eq_in_count s : {in s, a1 =1 a2} -> count a1 s = count a2 s.
Proof. by move/eq_in_filter=> eq_a12; rewrite -!size_filter eq_a12. Qed.

Lemma eq_in_all s : {in s, a1 =1 a2} -> all a1 s = all a2 s.
Proof. by move=> eq_a12; rewrite !all_count eq_in_count. Qed.

Lemma eq_in_has s : {in s, a1 =1 a2} -> has a1 s = has a2 s.
Proof. by move/eq_in_filter=> eq_a12; rewrite !has_filter eq_a12. Qed.

End EqIn.

Lemma eq_has_r s1 s2 : s1 =i s2 -> has^~ s1 =1 has^~ s2.
Proof.
by move=> Es a; apply/hasP/hasP=> -[x sx ax]; exists x; rewrite ?Es in sx *.
Qed.

Lemma eq_all_r s1 s2 : s1 =i s2 -> all^~ s1 =1 all^~ s2.
Proof. by move=> Es a; apply/negb_inj; rewrite -!has_predC (eq_has_r Es). Qed.

Lemma has_sym s1 s2 : has [in s1] s2 = has [in s2] s1.
Proof. by apply/hasP/hasP=> -[x]; exists x. Qed.

Lemma has_pred1 x s : has (pred1 x) s = (x \in s).
Proof. by rewrite -(eq_has (mem_seq1^~ x)) (has_sym [:: x]) /= orbF. Qed.

Lemma mem_rev s : rev s =i s.
Proof. by move=> a; rewrite -!has_pred1 has_rev. Qed.

(* Constant sequences, i.e., the image of nseq. *)

Definition constant s := if s is x :: s' then all (pred1 x) s' else true.

Lemma all_pred1P x s : reflect (s = nseq (size s) x) (all (pred1 x) s).
Proof.
elim: s => [|y s IHs] /=; first by left.
case: eqP => [->{y} | ne_xy]; last by right=> [] [? _]; case ne_xy.
by apply: (iffP IHs) => [<- //| []].
Qed.

Lemma all_pred1_constant x s : all (pred1 x) s -> constant s.
Proof. by case: s => //= y s /andP[/eqP->]. Qed.

Lemma all_pred1_nseq x n : all (pred1 x) (nseq n x).
Proof. by rewrite all_nseq /= eqxx orbT. Qed.

Lemma mem_nseq n x y : (y \in nseq n x) = (0 < n) && (y == x).
Proof. by rewrite -has_pred1 has_nseq eq_sym.  Qed.

Lemma nseqP n x y : reflect (y = x /\ n > 0) (y \in nseq n x).
Proof. by rewrite mem_nseq andbC; apply: (iffP andP) => -[/eqP]. Qed.

Lemma constant_nseq n x : constant (nseq n x).
Proof. exact: all_pred1_constant (all_pred1_nseq x n). Qed.

(* Uses x0 *)
Lemma constantP s : reflect (exists x, s = nseq (size s) x) (constant s).
Proof.
apply: (iffP idP) => [| [x ->]]; last exact: constant_nseq.
case: s => [|x s] /=; first by exists x0.
by move/all_pred1P=> def_s; exists x; rewrite -def_s.
Qed.

(* Duplicate-freenes. *)

Fixpoint uniq s := if s is x :: s' then (x \notin s') && uniq s' else true.

Lemma cons_uniq x s : uniq (x :: s) = (x \notin s) && uniq s.
Proof. by []. Qed.

Lemma cat_uniq s1 s2 :
  uniq (s1 ++ s2) = [&& uniq s1, ~~ has [in s1] s2 & uniq s2].
Proof.
elim: s1 => [|x s1 IHs]; first by rewrite /= has_pred0.
by rewrite has_sym /= mem_cat !negb_or has_sym IHs -!andbA; do !bool_congr.
Qed.

Lemma uniq_catC s1 s2 : uniq (s1 ++ s2) = uniq (s2 ++ s1).
Proof. by rewrite !cat_uniq has_sym andbCA andbA andbC. Qed.

Lemma uniq_catCA s1 s2 s3 : uniq (s1 ++ s2 ++ s3) = uniq (s2 ++ s1 ++ s3).
Proof.
by rewrite !catA -!(uniq_catC s3) !(cat_uniq s3) uniq_catC !has_cat orbC.
Qed.

Lemma rcons_uniq s x : uniq (rcons s x) = (x \notin s) && uniq s.
Proof. by rewrite -cats1 uniq_catC. Qed.

Lemma filter_uniq s a : uniq s -> uniq (filter a s).
Proof.
elim: s => //= x s IHs /andP[s'x]; case: ifP => //= a_x /IHs->.
by rewrite mem_filter a_x s'x.
Qed.

Lemma rot_uniq s : uniq (rot n0 s) = uniq s.
Proof. by rewrite /rot uniq_catC cat_take_drop. Qed.

Lemma rev_uniq s : uniq (rev s) = uniq s.
Proof.
elim: s => // x s IHs.
by rewrite rev_cons -cats1 cat_uniq /= andbT andbC mem_rev orbF IHs.
Qed.

Lemma count_memPn x s : reflect (count_mem x s = 0) (x \notin s).
Proof. by rewrite -has_pred1 has_count -eqn0Ngt; apply: eqP. Qed.

Lemma count_uniq_mem s x : uniq s -> count_mem x s = (x \in s).
Proof.
elim: s => //= y s IHs /andP[/negbTE s'y /IHs-> {IHs}].
by rewrite in_cons; case: (eqVneq y x) => // <-; rewrite s'y.
Qed.

Lemma leq_uniq_countP x s1 s2 : uniq s1 ->
  reflect (x \in s1 -> x \in s2) (count_mem x s1 <= count_mem x s2).
Proof.
move/count_uniq_mem->; case: (boolP (_ \in _)) => //= _; last by constructor.
by rewrite -has_pred1 has_count; apply: (iffP idP) => //; apply.
Qed.

Lemma leq_uniq_count s1 s2 : uniq s1 -> {subset s1 <= s2} ->
  (forall x, count_mem x s1 <= count_mem x s2).
Proof. by move=> s1_uniq s1_s2 x; apply/leq_uniq_countP/s1_s2. Qed.

Lemma filter_pred1_uniq s x : uniq s -> x \in s -> filter (pred1 x) s = [:: x].
Proof.
move=> uniq_s s_x; rewrite (all_pred1P _ _ (filter_all _ _)).
by rewrite size_filter count_uniq_mem ?s_x.
Qed.

(* Removing duplicates *)

Fixpoint undup s :=
  if s is x :: s' then if x \in s' then undup s' else x :: undup s' else [::].

Lemma size_undup s : size (undup s) <= size s.
Proof. by elim: s => //= x s IHs; case: (x \in s) => //=; apply: ltnW. Qed.

Lemma mem_undup s : undup s =i s.
Proof.
move=> x; elim: s => //= y s IHs.
by case s_y: (y \in s); rewrite !inE IHs //; case: eqP => [->|].
Qed.

Lemma undup_uniq s : uniq (undup s).
Proof.
by elim: s => //= x s IHs; case s_x: (x \in s); rewrite //= mem_undup s_x.
Qed.

Lemma undup_id s : uniq s -> undup s = s.
Proof. by elim: s => //= x s IHs /andP[/negbTE-> /IHs->]. Qed.

Lemma ltn_size_undup s : (size (undup s) < size s) = ~~ uniq s.
Proof.
by elim: s => //= x s IHs; case s_x: (x \in s); rewrite //= ltnS size_undup.
Qed.

Lemma filter_undup p s : filter p (undup s) = undup (filter p s).
Proof.
elim: s => //= x s IHs; rewrite (fun_if undup) fun_if /= mem_filter /=.
by rewrite (fun_if (filter p)) /= IHs; case: ifP => -> //=; apply: if_same.
Qed.

Lemma undup_nil s : undup s = [::] -> s = [::].
Proof. by case: s => //= x s; rewrite -mem_undup; case: ifP; case: undup. Qed.

Lemma undup_cat s t :
  undup (s ++ t) = [seq x <- undup s | x \notin t] ++ undup t.
Proof. by elim: s => //= x s ->; rewrite mem_cat; do 2 case: in_mem => //=. Qed.

Lemma undup_rcons s x : undup (rcons s x) = rcons [seq y <- undup s | y != x] x.
Proof.
by rewrite -!cats1 undup_cat; congr cat; apply: eq_filter => y; rewrite inE.
Qed.

Lemma count_undup s p : count p (undup s) <= count p s.
Proof. by rewrite -!size_filter filter_undup size_undup. Qed.

(* Lookup *)

Definition index x := find (pred1 x).

Lemma index_size x s : index x s <= size s.
Proof. by rewrite /index find_size. Qed.

Lemma index_mem x s : (index x s < size s) = (x \in s).
Proof. by rewrite -has_pred1 has_find. Qed.

Lemma memNindex x s :  x \notin s -> index x s = size s.
Proof. by rewrite -has_pred1 => /hasNfind. Qed.

Lemma nth_index x s : x \in s -> nth s (index x s) = x.
Proof. by rewrite -has_pred1 => /(nth_find x0)/eqP. Qed.

Lemma index_cat x s1 s2 :
 index x (s1 ++ s2) = if x \in s1 then index x s1 else size s1 + index x s2.
Proof. by rewrite /index find_cat has_pred1. Qed.

Lemma index_ltn x s i : x \in take i s -> index x s < i.
Proof. by rewrite -has_pred1; apply: find_ltn. Qed.

Lemma in_take x s i : x \in s -> (x \in take i s) = (index x s < i).
Proof. by rewrite -?has_pred1; apply: has_take. Qed.

Lemma in_take_leq x s i : i <= size s -> (x \in take i s) = (index x s < i).
Proof. by rewrite -?has_pred1; apply: has_take_leq. Qed.

Lemma nthK s: uniq s -> {in gtn (size s), cancel (nth s) (index^~ s)}.
Proof.
elim: s => //= x s IHs /andP[s'x Us] i; rewrite inE ltnS eq_sym -if_neg.
by case: i => /= [_|i lt_i_s]; rewrite ?eqxx ?IHs ?(memPn s'x) ?mem_nth.
Qed.

Lemma index_uniq i s : i < size s -> uniq s -> index (nth s i) s = i.
Proof. by move/nthK. Qed.

Lemma index_head x s : index x (x :: s) = 0.
Proof. by rewrite /= eqxx. Qed.

Lemma index_last x s : uniq (x :: s) -> index (last x s) (x :: s) = size s.
Proof.
rewrite lastI rcons_uniq -cats1 index_cat size_belast.
by case: ifP => //=; rewrite eqxx addn0.
Qed.

Lemma nth_uniq s i j :
  i < size s -> j < size s -> uniq s -> (nth s i == nth s j) = (i == j).
Proof. by move=> lti ltj /nthK/can_in_eq->. Qed.

Lemma uniqPn s :
  reflect (exists i j, [/\ i < j, j < size s & nth s i = nth s j]) (~~ uniq s).
Proof.
apply: (iffP idP) => [|[i [j [ltij ltjs]]]]; last first.
  by apply: contra_eqN => Us; rewrite nth_uniq ?ltn_eqF // (ltn_trans ltij).
elim: s => // x s IHs /nandP[/negbNE | /IHs[i [j]]]; last by exists i.+1, j.+1.
by exists 0, (index x s).+1; rewrite !ltnS index_mem /= nth_index.
Qed.

Lemma uniqP s : reflect {in gtn (size s) &, injective (nth s)} (uniq s).
Proof.
apply: (iffP idP) => [/nthK/can_in_inj// | nth_inj].
apply/uniqPn => -[i [j [ltij ltjs /nth_inj/eqP/idPn]]].
by rewrite !inE (ltn_trans ltij ltjs) ltn_eqF //=; case.
Qed.

Lemma mem_rot s : rot n0 s =i s.
Proof. by move=> x; rewrite -[s in RHS](cat_take_drop n0) !mem_cat /= orbC. Qed.

Lemma eqseq_rot s1 s2 : (rot n0 s1 == rot n0 s2) = (s1 == s2).
Proof. exact/inj_eq/rot_inj. Qed.

Lemma drop_index s (n := index x0 s) : x0 \in s -> drop n s = x0 :: drop n.+1 s.
Proof. by move=> xs; rewrite (drop_nth x0) ?index_mem ?nth_index. Qed.

(* lemmas about the pivot pattern [_ ++ _ :: _] *)

Lemma index_pivot x s1 s2 (s := s1 ++ x :: s2) : x \notin s1 ->
  index x s = size s1.
Proof. by rewrite index_cat/= eqxx addn0; case: ifPn. Qed.

Lemma take_pivot x s2 s1 (s := s1 ++ x :: s2) : x \notin s1 ->
  take (index x s) s = s1.
Proof. by move=> /index_pivot->; rewrite take_size_cat. Qed.

Lemma rev_pivot x s1 s2 : rev (s1 ++ x :: s2) = rev s2 ++ x :: rev s1.
Proof. by rewrite rev_cat rev_cons cat_rcons. Qed.

Lemma eqseq_pivot2l x s1 s2 s3 s4 : x \notin s1 -> x \notin s3 ->
  (s1 ++ x :: s2 == s3 ++ x :: s4) = (s1 == s3) && (s2 == s4).
Proof.
move=> xNs1 xNs3; apply/idP/idP => [E|/andP[/eqP-> /eqP->]//].
suff S : size s1 = size s3 by rewrite eqseq_cat// eqseq_cons eqxx in E.
by rewrite -(index_pivot s2 xNs1) (eqP E) index_pivot.
Qed.

Lemma eqseq_pivot2r x s1 s2 s3 s4 : x \notin s2 -> x \notin s4 ->
  (s1 ++ x :: s2 == s3 ++ x :: s4) = (s1 == s3) && (s2 == s4).
Proof.
move=> xNs2 xNs4; rewrite -(can_eq revK) !rev_pivot.
by rewrite eqseq_pivot2l ?mem_rev // !(can_eq revK) andbC.
Qed.

Lemma eqseq_pivotl x s1 s2 s3 s4 : x \notin s1 -> x \notin s2 ->
  (s1 ++ x :: s2 == s3 ++ x :: s4) = (s1 == s3) && (s2 == s4).
Proof.
move=> xNs1 xNs2; apply/idP/idP => [E|/andP[/eqP-> /eqP->]//].
rewrite -(@eqseq_pivot2l x)//; have /eqP/(congr1 (count_mem x)) := E.
rewrite !count_cat/= eqxx !addnS (count_memPn _ _ xNs1) (count_memPn _ _ xNs2).
by move=> -[/esym/eqP]; rewrite addn_eq0 => /andP[/eqP/count_memPn].
Qed.

Lemma eqseq_pivotr x s1 s2 s3 s4 : x \notin s3 -> x \notin s4 ->
  (s1 ++ x :: s2 == s3 ++ x :: s4) = (s1 == s3) && (s2 == s4).
Proof. by move=> *; rewrite eq_sym eqseq_pivotl//; case: eqVneq => /=. Qed.

Lemma uniq_eqseq_pivotl x s1 s2 s3 s4 : uniq (s1 ++ x :: s2) ->
  (s1 ++ x :: s2 == s3 ++ x :: s4) = (s1 == s3) && (s2 == s4).
Proof.
by rewrite uniq_catC/= mem_cat => /andP[/norP[? ?] _]; rewrite eqseq_pivotl.
Qed.

Lemma uniq_eqseq_pivotr x s1 s2 s3 s4 : uniq (s3 ++ x :: s4) ->
  (s1 ++ x :: s2 == s3 ++ x :: s4) = (s1 == s3) && (s2 == s4).
Proof. by move=> ?; rewrite eq_sym uniq_eqseq_pivotl//; case: eqVneq => /=. Qed.

End EqSeq.
Arguments eqseq : simpl nomatch.

Section RotIndex.
Variables (T : eqType).
Implicit Types x y z : T.

Lemma rot_index s x (i := index x s) : x \in s ->
  rot i s = x :: (drop i.+1 s ++ take i s).
Proof. by move=> x_s; rewrite /rot drop_index. Qed.

Variant rot_to_spec s x := RotToSpec i s' of rot i s = x :: s'.

Lemma rot_to s x : x \in s -> rot_to_spec s x.
Proof. by move=> /rot_index /RotToSpec. Qed.

End RotIndex.

Definition inE := (mem_seq1, in_cons, inE).

Prenex Implicits mem_seq1 constant uniq undup index.

Arguments eqseq {T} !_ !_.
Arguments pred_of_seq {T} s x /.
Arguments eqseqP {T x y}.
Arguments hasP {T a s}.
Arguments hasPn {T a s}.
Arguments allP {T a s}.
Arguments allPn {T a s}.
Arguments nseqP {T n x y}.
Arguments count_memPn {T x s}.
Arguments uniqPn {T} x0 {s}.
Arguments uniqP {T} x0 {s}.
Arguments forall_cons {T P a s}.
Arguments exists_cons {T P a s}.

(* Since both `all [in s] s`, `all (mem s) s`, and `all (pred_of_seq s) s`    *)
(* may appear in goals, the following hint has to be declared using the       *)
(* `Hint Extern` command. Additionally, `mem` and `pred_of_seq` in the above  *)
(* terms do not reduce to each other; thus, stating `allss` in the form of    *)
(* one of them makes `apply: allss` fail for the other case. Since both `mem` *)
(* and `pred_of_seq` reduce to `mem_seq`, the following explicit type         *)
(* annotation for `allss` makes it work for both cases.                       *)
#[export] Hint Extern 0 (is_true (all _ _)) =>
  apply: (allss : forall T s, all (mem_seq s) s) : core.

Section NthTheory.

Lemma nthP (T : eqType) (s : seq T) x x0 :
  reflect (exists2 i, i < size s & nth x0 s i = x) (x \in s).
Proof.
apply: (iffP idP) => [|[n Hn <-]]; last exact: mem_nth.
by exists (index x s); [rewrite index_mem | apply nth_index].
Qed.

Variable T : Type.
Implicit Types (a : pred T) (x : T).

Lemma has_nthP a s x0 :
  reflect (exists2 i, i < size s & a (nth x0 s i)) (has a s).
Proof.
elim: s => [|x s IHs] /=; first by right; case.
case nax: (a x); first by left; exists 0.
by apply: (iffP IHs) => [[i]|[[|i]]]; [exists i.+1 | rewrite nax | exists i].
Qed.

Lemma all_nthP a s x0 :
  reflect (forall i, i < size s -> a (nth x0 s i)) (all a s).
Proof.
rewrite -(eq_all (fun x => negbK (a x))) all_predC.
case: (has_nthP _ _ x0) => [na_s | a_s]; [right=> a_s | left=> i lti].
  by case: na_s => i lti; rewrite a_s.
by apply/idPn=> na_si; case: a_s; exists i.
Qed.

Lemma set_nthE s x0 n x :
  set_nth x0 s n x = if n < size s
    then take n s ++ x :: drop n.+1 s
    else s ++ ncons (n - size s) x0 [:: x].
Proof.
elim: s n => [|a s IH] n /=; first by rewrite subn0 set_nth_nil.
case: n => [|n]; first by rewrite drop0.
by rewrite ltnS /=; case: ltnP (IH n) => _ ->.
Qed.

Lemma count_set_nth a s x0 n x :
  count a (set_nth x0 s n x) =
    count a s + a x - a (nth x0 s n) * (n < size s) + (a x0) * (n - size s).
Proof.
rewrite set_nthE; case: ltnP => [nlts|nges]; last first.
  rewrite -cat_nseq !count_cat count_nseq /=.
  by rewrite muln0 addn0 subn0 addnAC addnA.
have -> : n - size s = 0 by apply/eqP; rewrite subn_eq0 ltnW.
rewrite -[in count a s](cat_take_drop n s) [drop n s](drop_nth x0)//.
by rewrite !count_cat/= muln1 muln0 addn0 addnAC !addnA [in RHS]addnAC addnK.
Qed.

Lemma count_set_nth_ltn a s x0 n x : n < size s ->
  count a (set_nth x0 s n x) = count a s + a x - a (nth x0 s n).
Proof.
move=> nlts; rewrite count_set_nth nlts muln1.
have -> : n - size s = 0 by apply/eqP; rewrite subn_eq0 ltnW.
by rewrite muln0 addn0.
Qed.

Lemma count_set_nthF a s x0 n x : ~~ a x0 ->
  count a (set_nth x0 s n x) = count a s + a x - a (nth x0 s n).
Proof.
move=> /negbTE ax0; rewrite count_set_nth ax0 mul0n addn0.
case: ltnP => [_|nges]; first by rewrite muln1.
by rewrite nth_default// ax0 subn0.
Qed.

End NthTheory.

Lemma set_nth_default T s (y0 x0 : T) n : n < size s -> nth x0 s n = nth y0 s n.
Proof. by elim: s n => [|y s' IHs] [|n] //= /IHs. Qed.

Lemma headI T s (x : T) : rcons s x = head x s :: behead (rcons s x).
Proof. by case: s. Qed.

Arguments nthP {T s x}.
Arguments has_nthP {T a s}.
Arguments all_nthP {T a s}.

Definition bitseq := seq bool.
Canonical bitseq_eqType := Eval hnf in [eqType of bitseq].
Canonical bitseq_predType := Eval hnf in [predType of bitseq].

(* Generalizations of splitP (from path.v): split_find_nth and split_find *)
Section FindNth.
Variables (T : Type).
Implicit Types (x : T) (p : pred T) (s : seq T).

Variant split_find_nth_spec p : seq T -> seq T -> seq T -> T -> Type :=
  FindNth x s1 s2 of p x & ~~ has p s1 :
    split_find_nth_spec p (rcons s1 x ++ s2) s1 s2 x.

Lemma split_find_nth x0 p s (i := find p s) :
  has p s -> split_find_nth_spec p s (take i s) (drop i.+1 s) (nth x0 s i).
Proof.
move=> p_s; rewrite -[X in split_find_nth_spec _ X](cat_take_drop i s).
rewrite (drop_nth x0 _) -?has_find// -cat_rcons.
by constructor; [apply: nth_find | rewrite has_take -?leqNgt].
Qed.

Variant split_find_spec p : seq T -> seq T -> seq T -> Type :=
  FindSplit x s1 s2 of p x & ~~ has p s1 :
    split_find_spec p (rcons s1 x ++ s2) s1 s2.

Lemma split_find p s (i := find p s) :
  has p s -> split_find_spec p s (take i s) (drop i.+1 s).
Proof.
by case: s => // x ? in i * => ?; case: split_find_nth => //; constructor.
Qed.

Lemma nth_rcons_cat_find x0 p s1 s2 x (s := rcons s1 x ++ s2) :
   p x -> ~~ has p s1 -> nth x0 s (find p s) = x.
Proof.
move=> pz pNs1; rewrite /s  cat_rcons find_cat (negPf pNs1).
by rewrite nth_cat/= pz addn0 subnn ltnn.
Qed.

End FindNth.

(* Incrementing the ith nat in a seq nat, padding with 0's if needed. This  *)
(* allows us to use nat seqs as bags of nats.                               *)

Fixpoint incr_nth v i {struct i} :=
  if v is n :: v' then if i is i'.+1 then n :: incr_nth v' i' else n.+1 :: v'
  else ncons i 0 [:: 1].
Arguments incr_nth : simpl nomatch.

Lemma nth_incr_nth v i j : nth 0 (incr_nth v i) j = (i == j) + nth 0 v j.
Proof.
elim: v i j => [|n v IHv] [|i] [|j] //=; rewrite ?eqSS ?addn0 //; try by case j.
elim: i j => [|i IHv] [|j] //=; rewrite ?eqSS //; by case j.
Qed.

Lemma size_incr_nth v i :
  size (incr_nth v i) = if i < size v then size v else i.+1.
Proof.
elim: v i => [|n v IHv] [|i] //=; first by rewrite size_ncons /= addn1.
by rewrite IHv; apply: fun_if.
Qed.

Lemma incr_nth_inj v : injective (incr_nth v).
Proof.
move=> i j /(congr1 (nth 0 ^~ i)); apply: contra_eq => neq_ij.
by rewrite !nth_incr_nth eqn_add2r eqxx /nat_of_bool ifN_eqC.
Qed.

Lemma incr_nthC v i j :
  incr_nth (incr_nth v i) j = incr_nth (incr_nth v j) i.
Proof.
apply: (@eq_from_nth _ 0) => [|k _]; last by rewrite !nth_incr_nth addnCA.
by do !rewrite size_incr_nth leqNgt if_neg -/(maxn _ _); apply: maxnAC.
Qed.

(* Equality up to permutation *)

Section PermSeq.

Variable T : eqType.
Implicit Type s : seq T.

Definition perm_eq s1 s2 :=
  all [pred x | count_mem x s1 == count_mem x s2] (s1 ++ s2).

Lemma permP s1 s2 : reflect (count^~ s1 =1 count^~ s2) (perm_eq s1 s2).
Proof.
apply: (iffP allP) => /= [eq_cnt1 a | eq_cnt x _]; last exact/eqP.
have [n le_an] := ubnP (count a (s1 ++ s2)); elim: n => // n IHn in a le_an *.
have [/eqP|] := posnP (count a (s1 ++ s2)).
  by rewrite count_cat addn_eq0; do 2!case: eqP => // ->.
rewrite -has_count => /hasP[x s12x a_x]; pose a' := predD1 a x.
have cnt_a' s: count a s = count_mem x s + count a' s.
  rewrite -count_predUI -[LHS]addn0 -(count_pred0 s).
  by congr (_ + _); apply: eq_count => y /=; case: eqP => // ->.
rewrite !cnt_a' (eqnP (eq_cnt1 _ s12x)) (IHn a') // -ltnS.
apply: leq_trans le_an.
by rewrite ltnS cnt_a' -add1n leq_add2r -has_count has_pred1.
Qed.

Lemma perm_refl s : perm_eq s s.
Proof. exact/permP. Qed.
Hint Resolve perm_refl : core.

Lemma perm_sym : symmetric perm_eq.
Proof. by move=> s1 s2; apply/permP/permP=> eq_s12 a. Qed.

Lemma perm_trans : transitive perm_eq.
Proof. by move=> s2 s1 s3 /permP-eq12 /permP/(ftrans eq12)/permP. Qed.

Notation perm_eql s1 s2 := (perm_eq s1 =1 perm_eq s2).
Notation perm_eqr s1 s2 := (perm_eq^~ s1 =1 perm_eq^~ s2).

Lemma permEl s1 s2 : perm_eql s1 s2 -> perm_eq s1 s2. Proof. by move->. Qed.

Lemma permPl s1 s2 : reflect (perm_eql s1 s2) (perm_eq s1 s2).
Proof.
apply: (iffP idP) => [eq12 s3 | -> //]; apply/idP/idP; last exact: perm_trans.
by rewrite -!(perm_sym s3) => /perm_trans; apply.
Qed.

Lemma permPr s1 s2 : reflect (perm_eqr s1 s2) (perm_eq s1 s2).
Proof.
by apply/(iffP idP) => [/permPl eq12 s3| <- //]; rewrite !(perm_sym s3) eq12.
Qed.

Lemma perm_catC s1 s2 : perm_eql (s1 ++ s2) (s2 ++ s1).
Proof. by apply/permPl/permP=> a; rewrite !count_cat addnC. Qed.

Lemma perm_cat2l s1 s2 s3 : perm_eq (s1 ++ s2) (s1 ++ s3) = perm_eq s2 s3.
Proof.
apply/permP/permP=> eq23 a; apply/eqP;
  by move/(_ a)/eqP: eq23; rewrite !count_cat eqn_add2l.
Qed.

Lemma perm_catl s t1 t2 : perm_eq t1 t2 -> perm_eql (s ++ t1) (s ++ t2).
Proof. by move=> eq_t12; apply/permPl; rewrite perm_cat2l. Qed.

Lemma perm_cons x s1 s2 : perm_eq (x :: s1) (x :: s2) = perm_eq s1 s2.
Proof. exact: (perm_cat2l [::x]). Qed.

Lemma perm_cat2r s1 s2 s3 : perm_eq (s2 ++ s1) (s3 ++ s1) = perm_eq s2 s3.
Proof. by do 2!rewrite perm_sym perm_catC; apply: perm_cat2l. Qed.

Lemma perm_catr s1 s2 t : perm_eq s1 s2 -> perm_eql (s1 ++ t) (s2 ++ t).
Proof. by move=> eq_s12; apply/permPl; rewrite perm_cat2r. Qed.

Lemma perm_cat s1 s2 t1 t2 :
  perm_eq s1 s2 -> perm_eq t1 t2 -> perm_eq (s1 ++ t1) (s2 ++ t2).
Proof. by move=> /perm_catr-> /perm_catl->. Qed.

Lemma perm_catAC s1 s2 s3 : perm_eql ((s1 ++ s2) ++ s3) ((s1 ++ s3) ++ s2).
Proof. by apply/permPl; rewrite -!catA perm_cat2l perm_catC. Qed.

Lemma perm_catCA s1 s2 s3 : perm_eql (s1 ++ s2 ++ s3) (s2 ++ s1 ++ s3).
Proof. by apply/permPl; rewrite !catA perm_cat2r perm_catC. Qed.

Lemma perm_catACA s1 s2 s3 s4 :
  perm_eql ((s1 ++ s2) ++ (s3 ++ s4)) ((s1 ++ s3) ++ (s2 ++ s4)).
Proof. by apply/permPl; rewrite perm_catAC !catA perm_catAC. Qed.

Lemma perm_rcons x s : perm_eql (rcons s x) (x :: s).
Proof. by move=> /= s2; rewrite -cats1 perm_catC. Qed.

Lemma perm_rot n s : perm_eql (rot n s) s.
Proof. by move=> /= s2; rewrite perm_catC cat_take_drop. Qed.

Lemma perm_rotr n s : perm_eql (rotr n s) s.
Proof. exact: perm_rot. Qed.

Lemma perm_rev s : perm_eql (rev s) s.
Proof. by apply/permPl/permP=> i; rewrite count_rev. Qed.

Lemma perm_filter s1 s2 a :
  perm_eq s1 s2 -> perm_eq (filter a s1) (filter a s2).
Proof. by move/permP=> s12_count; apply/permP=> Q; rewrite !count_filter. Qed.

Lemma perm_filterC a s : perm_eql (filter a s ++ filter (predC a) s) s.
Proof.
apply/permPl; elim: s => //= x s IHs.
by case: (a x); last rewrite /= -cat1s perm_catCA; rewrite perm_cons.
Qed.

Lemma perm_size s1 s2 : perm_eq s1 s2 -> size s1 = size s2.
Proof. by move/permP=> eq12; rewrite -!count_predT eq12. Qed.

Lemma perm_mem s1 s2 : perm_eq s1 s2 -> s1 =i s2.
Proof. by move/permP=> eq12 x; rewrite -!has_pred1 !has_count eq12. Qed.

Lemma perm_nilP s : reflect (s = [::]) (perm_eq s [::]).
Proof. by apply: (iffP idP) => [/perm_size/eqP/nilP | ->]. Qed.

Lemma perm_consP x s t :
  reflect (exists i u, rot i t = x :: u /\ perm_eq u s)
          (perm_eq t (x :: s)).
Proof.
apply: (iffP idP) => [eq_txs | [i [u [Dt eq_us]]]].
  have /rot_to[i u Dt]: x \in t by rewrite (perm_mem eq_txs) mem_head.
  by exists i, u; rewrite -(perm_cons x) -Dt perm_rot.
by rewrite -(perm_rot i) Dt perm_cons.
Qed.

Lemma perm_has s1 s2 a : perm_eq s1 s2 -> has a s1 = has a s2.
Proof. by move/perm_mem/eq_has_r. Qed.

Lemma perm_all s1 s2 a : perm_eq s1 s2 -> all a s1 = all a s2.
Proof. by move/perm_mem/eq_all_r. Qed.

Lemma perm_small_eq s1 s2 : size s2 <= 1 -> perm_eq s1 s2 -> s1 = s2.
Proof.
move=> s2_le1 eqs12; move/perm_size: eqs12 s2_le1 (perm_mem eqs12).
by case: s2 s1 => [|x []] // [|y []] // _ _ /(_ x) /[!(inE, eqxx)] /eqP->.
Qed.

Lemma uniq_leq_size s1 s2 : uniq s1 -> {subset s1 <= s2} -> size s1 <= size s2.
Proof.
elim: s1 s2 => //= x s1 IHs s2 /andP[not_s1x Us1] /forall_cons[s2x ss12].
have [i s3 def_s2] := rot_to s2x; rewrite -(size_rot i s2) def_s2.
apply: IHs => // y s1y; have:= ss12 y s1y.
by rewrite -(mem_rot i) def_s2 inE (negPf (memPn _ y s1y)).
Qed.

Lemma leq_size_uniq s1 s2 :
  uniq s1 -> {subset s1 <= s2} -> size s2 <= size s1 -> uniq s2.
Proof.
elim: s1 s2 => [[] | x s1 IHs s2] // Us1x; have /andP[not_s1x Us1] := Us1x.
case/forall_cons => /rot_to[i s3 def_s2] ss12 le_s21.
rewrite -(rot_uniq i) -(size_rot i) def_s2 /= in le_s21 *.
have ss13 y (s1y : y \in s1): y \in s3.
  by have:= ss12 y s1y; rewrite -(mem_rot i) def_s2 inE (negPf (memPn _ y s1y)).
rewrite IHs // andbT; apply: contraL _ le_s21 => s3x; rewrite -leqNgt.
by apply/(uniq_leq_size Us1x)/allP; rewrite /= s3x; apply/allP.
Qed.

Lemma uniq_size_uniq s1 s2 :
  uniq s1 -> s1 =i s2 -> uniq s2 = (size s2 == size s1).
Proof.
move=> Us1 eqs12; apply/idP/idP=> [Us2 | /eqP eq_sz12].
  by rewrite eqn_leq !uniq_leq_size // => y; rewrite eqs12.
by apply: (leq_size_uniq Us1) => [y|]; rewrite (eqs12, eq_sz12).
Qed.

Lemma uniq_min_size s1 s2 :
    uniq s1 -> {subset s1 <= s2} -> size s2 <= size s1 ->
  (size s1 = size s2) * (s1 =i s2).
Proof.
move=> Us1 ss12 le_s21; have Us2: uniq s2 := leq_size_uniq Us1 ss12 le_s21.
suffices: s1 =i s2 by split; first by apply/eqP; rewrite -uniq_size_uniq.
move=> x; apply/idP/idP=> [/ss12// | s2x]; apply: contraLR le_s21 => not_s1x.
rewrite -ltnNge (@uniq_leq_size (x :: s1)) /= ?not_s1x //.
by apply/allP; rewrite /= s2x; apply/allP.
Qed.

Lemma eq_uniq s1 s2 : size s1 = size s2 -> s1 =i s2 -> uniq s1 = uniq s2.
Proof.
move=> eq_sz12 eq_s12.
by apply/idP/idP=> Us; rewrite (uniq_size_uniq Us) ?eq_sz12 ?eqxx.
Qed.

Lemma perm_uniq s1 s2 : perm_eq s1 s2 -> uniq s1 = uniq s2.
Proof. by move=> eq_s12; apply/eq_uniq; [apply/perm_size | apply/perm_mem]. Qed.

Lemma uniq_perm s1 s2 : uniq s1 -> uniq s2 -> s1 =i s2 -> perm_eq s1 s2.
Proof.
move=> Us1 Us2 eq12; apply/allP=> x _; apply/eqP.
by rewrite !count_uniq_mem ?eq12.
Qed.

Lemma perm_undup s1 s2 : s1 =i s2 -> perm_eq (undup s1) (undup s2).
Proof.
by move=> Es12; rewrite uniq_perm ?undup_uniq // => s; rewrite !mem_undup.
Qed.

Lemma count_mem_uniq s : (forall x, count_mem x s = (x \in s)) -> uniq s.
Proof.
move=> count1_s; have Uus := undup_uniq s.
suffices: perm_eq s (undup s) by move/perm_uniq->.
by apply/allP=> x _; apply/eqP; rewrite (count_uniq_mem x Uus) mem_undup.
Qed.

Lemma eq_count_undup a s1 s2 :
  {in a, s1 =i s2} -> count a (undup s1) = count a (undup s2).
Proof.
move=> s1_eq_s2; rewrite -!size_filter !filter_undup.
apply/perm_size/perm_undup => x.
by rewrite !mem_filter; case: (boolP (a x)) => //= /s1_eq_s2.
Qed.

Lemma catCA_perm_ind P :
    (forall s1 s2 s3, P (s1 ++ s2 ++ s3) -> P (s2 ++ s1 ++ s3)) ->
  (forall s1 s2, perm_eq s1 s2 -> P s1 -> P s2).
Proof.
move=> PcatCA s1 s2 eq_s12; rewrite -[s1]cats0 -[s2]cats0.
elim: s2 nil => [|x s2 IHs] s3 in s1 eq_s12 *.
  by case: s1 {eq_s12}(perm_size eq_s12).
have /rot_to[i s' def_s1]: x \in s1 by rewrite (perm_mem eq_s12) mem_head.
rewrite -(cat_take_drop i s1) -catA => /PcatCA.
rewrite catA -/(rot i s1) def_s1 /= -cat1s => /PcatCA/IHs/PcatCA; apply.
by rewrite -(perm_cons x) -def_s1 perm_rot.
Qed.

Lemma catCA_perm_subst R F :
    (forall s1 s2 s3, F (s1 ++ s2 ++ s3) = F (s2 ++ s1 ++ s3) :> R) ->
  (forall s1 s2, perm_eq s1 s2 -> F s1 = F s2).
Proof.
move=> FcatCA s1 s2 /catCA_perm_ind => ind_s12.
by apply: (ind_s12 (eq _ \o F)) => //= *; rewrite FcatCA.
Qed.

End PermSeq.

Notation perm_eql s1 s2 := (perm_eq s1 =1 perm_eq s2).
Notation perm_eqr s1 s2 := (perm_eq^~ s1 =1 perm_eq^~ s2).

Arguments permP {T s1 s2}.
Arguments permPl {T s1 s2}.
Arguments permPr {T s1 s2}.
Prenex Implicits perm_eq.
#[global] Hint Resolve perm_refl : core.

Section RotrLemmas.

Variables (n0 : nat) (T : Type) (T' : eqType).
Implicit Types (x : T) (s : seq T).

Lemma size_rotr s : size (rotr n0 s) = size s.
Proof. by rewrite size_rot. Qed.

Lemma mem_rotr (s : seq T') : rotr n0 s =i s.
Proof. by move=> x; rewrite mem_rot. Qed.

Lemma rotr_size_cat s1 s2 : rotr (size s2) (s1 ++ s2) = s2 ++ s1.
Proof. by rewrite /rotr size_cat addnK rot_size_cat. Qed.

Lemma rotr1_rcons x s : rotr 1 (rcons s x) = x :: s.
Proof. by rewrite -rot1_cons rotK. Qed.

Lemma has_rotr a s : has a (rotr n0 s) = has a s.
Proof. by rewrite has_rot. Qed.

Lemma rotr_uniq (s : seq T') : uniq (rotr n0 s) = uniq s.
Proof. by rewrite rot_uniq. Qed.

Lemma rotrK : cancel (@rotr T n0) (rot n0).
Proof.
move=> s; have [lt_n0s | ge_n0s] := ltnP n0 (size s).
  by rewrite -{1}(subKn (ltnW lt_n0s)) -{1}[size s]size_rotr; apply: rotK.
by rewrite -[in RHS](rot_oversize ge_n0s) /rotr (eqnP ge_n0s) rot0.
Qed.

Lemma rotr_inj : injective (@rotr T n0).
Proof. exact (can_inj rotrK). Qed.

Lemma take_rev s : take n0 (rev s) = rev (drop (size s - n0) s).
Proof.
set m := _ - n0; rewrite -[s in LHS](cat_take_drop m) rev_cat take_cat.
rewrite size_rev size_drop -minnE minnC leq_min ltnn /m.
by have [_|/eqnP->] := ltnP; rewrite ?subnn take0 cats0.
Qed.

Lemma rev_take s : rev (take n0 s) = drop (size s - n0) (rev s).
Proof. by rewrite -[s in take _ s]revK take_rev revK size_rev. Qed.

Lemma drop_rev s : drop n0 (rev s) = rev (take (size s - n0) s).
Proof.
set m := _ - n0; rewrite -[s in LHS](cat_take_drop m) rev_cat drop_cat.
rewrite size_rev size_drop -minnE minnC leq_min ltnn /m.
by have [_|/eqnP->] := ltnP; rewrite ?take0 // subnn drop0.
Qed.

Lemma rev_drop s : rev (drop n0 s) = take (size s - n0) (rev s).
Proof. by rewrite -[s in drop _ s]revK drop_rev revK size_rev. Qed.

Lemma rev_rotr s : rev (rotr n0 s) = rot n0 (rev s).
Proof. by rewrite rev_cat -take_rev -drop_rev. Qed.

Lemma rev_rot s : rev (rot n0 s) = rotr n0 (rev s).
Proof. by apply: canLR revK _; rewrite rev_rotr revK. Qed.

End RotrLemmas.

Arguments rotrK n0 {T} s : rename.
Arguments rotr_inj {n0 T} [s1 s2] eq_rotr_s12 : rename.

Section RotCompLemmas.

Variable T : Type.
Implicit Type s : seq T.

Lemma rotD m n s : m + n <= size s -> rot (m + n) s = rot m (rot n s).
Proof.
move=> sz_s; rewrite [LHS]/rot -[take _ s](cat_take_drop n).
rewrite 5!(catA, =^~ rot_size_cat) !cat_take_drop.
by rewrite size_drop !size_takel ?leq_addl ?addnK.
Qed.

Lemma rotS n s : n < size s -> rot n.+1 s = rot 1 (rot n s).
Proof. exact: (@rotD 1). Qed.

Lemma rot_add_mod m n s : n <= size s -> m <= size s ->
  rot m (rot n s) = rot (if m + n <= size s then m + n else m + n - size s) s.
Proof.
move=> Hn Hm; case: leqP => [/rotD // | /ltnW Hmn]; symmetry.
by rewrite -{2}(rotK n s) /rotr -rotD size_rot addnBA ?subnK ?addnK.
Qed.

Lemma rot_minn n s : rot n s = rot (minn n (size s)) s.
Proof.
by case: (leqP n (size s)) => // /leqW ?; rewrite rot_size rot_oversize.
Qed.

Definition rot_add s n m (k := size s) (p := minn m k + minn n k) :=
  locked (if p <= k then p else p - k).

Lemma leq_rot_add n m s : rot_add s n m <= size s.
Proof.
by unlock rot_add; case: ifP; rewrite // leq_subLR leq_add // geq_minr.
Qed.

Lemma rot_addC n m s : rot_add s n m = rot_add s m n.
Proof. by unlock rot_add; rewrite ![minn n _ + _]addnC. Qed.

Lemma rot_rot_add n m s : rot m (rot n s) = rot (rot_add s n m) s.
Proof.
unlock rot_add.
by rewrite (rot_minn n) (rot_minn m) rot_add_mod ?size_rot ?geq_minr.
Qed.

Lemma rot_rot m n s : rot m (rot n s) = rot n (rot m s).
Proof. by rewrite rot_rot_add rot_addC -rot_rot_add. Qed.

Lemma rot_rotr m n s : rot m (rotr n s) = rotr n (rot m s).
Proof. by rewrite [RHS]/rotr size_rot rot_rot. Qed.

Lemma rotr_rotr m n s : rotr m (rotr n s) = rotr n (rotr m s).
Proof. by rewrite /rotr !size_rot rot_rot. Qed.

End RotCompLemmas.

Section Mask.

Variables (n0 : nat) (T : Type).
Implicit Types (m : bitseq) (s : seq T).

Fixpoint mask m s {struct m} :=
  match m, s with
  | b :: m', x :: s' => if b then x :: mask m' s' else mask m' s'
  | _, _ => [::]
  end.

Lemma mask_false s n : mask (nseq n false) s = [::].
Proof. by elim: s n => [|x s IHs] [|n] /=. Qed.

Lemma mask_true s n : size s <= n -> mask (nseq n true) s = s.
Proof. by elim: s n => [|x s IHs] [|n] //= Hn; congr (_ :: _); apply: IHs. Qed.

Lemma mask0 m : mask m [::] = [::].
Proof. by case: m. Qed.

Lemma mask0s s : mask [::] s = [::]. Proof. by []. Qed.

Lemma mask1 b x : mask [:: b] [:: x] = nseq b x.
Proof. by case: b. Qed.

Lemma mask_cons b m x s : mask (b :: m) (x :: s) = nseq b x ++ mask m s.
Proof. by case: b. Qed.

Lemma size_mask m s : size m = size s -> size (mask m s) = count id m.
Proof. by move: m s; apply: seq_ind2 => // -[] x m s /= _ ->. Qed.

Lemma mask_cat m1 m2 s1 s2 :
  size m1 = size s1 -> mask (m1 ++ m2) (s1 ++ s2) = mask m1 s1 ++ mask m2 s2.
Proof. by move: m1 s1; apply: seq_ind2 => // -[] m1 x1 s1 /= _ ->. Qed.

Lemma mask_rcons b m x s : size m = size s ->
  mask (rcons m b) (rcons s x) = mask m s ++ nseq b x.
Proof. by move=> ms; rewrite -!cats1 mask_cat//; case: b. Qed.

Lemma all_mask a m s : all a s -> all a (mask m s).
Proof. by elim: s m => [|x s IHs] [|[] m]//= /andP[ax /IHs->]; rewrite ?ax. Qed.

Lemma has_mask_cons a b m x s :
  has a (mask (b :: m) (x :: s)) = b && a x || has a (mask m s).
Proof. by case: b. Qed.

Lemma has_mask a m s : has a (mask m s) -> has a s.
Proof. by apply/contraTT; rewrite -!all_predC; apply: all_mask. Qed.

Lemma rev_mask m s : size m = size s -> rev (mask m s) = mask (rev m) (rev s).
Proof.
move: m s; apply: seq_ind2 => //= b x m s eq_size_sm IH.
by case: b; rewrite !rev_cons mask_rcons ?IH ?size_rev// (cats1, cats0).
Qed.

Lemma mask_rot m s : size m = size s ->
   mask (rot n0 m) (rot n0 s) = rot (count id (take n0 m)) (mask m s).
Proof.
move=> Ems; rewrite mask_cat ?size_drop ?Ems // -rot_size_cat.
by rewrite size_mask -?mask_cat ?size_take ?Ems // !cat_take_drop.
Qed.

Lemma resize_mask m s : {m1 | size m1 = size s & mask m s = mask m1 s}.
Proof.
exists (take (size s) m ++ nseq (size s - size m) false).
  by elim: s m => [|x s IHs] [|b m] //=; rewrite (size_nseq, IHs).
by elim: s m => [|x s IHs] [|b m] //=; rewrite (mask_false, IHs).
Qed.

Lemma takeEmask i s : take i s = mask (nseq i true) s.
Proof. by elim: i s => [s|i IHi []// ? ?]; rewrite ?take0 //= IHi. Qed.

Lemma dropEmask i s :
  drop i s = mask (nseq i false ++ nseq (size s - i) true) s.
Proof. by elim: i s => [s|? ? []//]; rewrite drop0/= mask_true// subn0. Qed.

End Mask.
Arguments mask _ !_ !_.

Section EqMask.

Variables (n0 : nat) (T : eqType).
Implicit Types (s : seq T) (m : bitseq).

Lemma mem_mask_cons x b m y s :
  (x \in mask (b :: m) (y :: s)) = b && (x == y) || (x \in mask m s).
Proof. by case: b. Qed.

Lemma mem_mask x m s : x \in mask m s -> x \in s.
Proof. by rewrite -!has_pred1 => /has_mask. Qed.

Lemma in_mask x m s :
  uniq s -> x \in mask m s = (x \in s) && nth false m (index x s).
Proof.
elim: s m => [|y s IHs] [|[] m]//= /andP[yNs ?]; rewrite ?in_cons ?IHs //=;
by have [->|neq_xy] //= := eqVneq; rewrite ?andbF // (negPf yNs).
Qed.

Lemma mask_uniq s : uniq s -> forall m, uniq (mask m s).
Proof.
elim: s => [|x s IHs] Uxs [|b m] //=.
case: b Uxs => //= /andP[s'x Us]; rewrite {}IHs // andbT.
by apply: contra s'x; apply: mem_mask.
Qed.

Lemma mem_mask_rot m s :
  size m = size s -> mask (rot n0 m) (rot n0 s) =i mask m s.
Proof. by move=> Ems x; rewrite mask_rot // mem_rot. Qed.

End EqMask.

Section Subseq.

Variable T : eqType.
Implicit Type s : seq T.

Fixpoint subseq s1 s2 :=
  if s2 is y :: s2' then
    if s1 is x :: s1' then subseq (if x == y then s1' else s1) s2' else true
  else s1 == [::].

Lemma sub0seq s : subseq [::] s. Proof. by case: s. Qed.

Lemma subseq0 s : subseq s [::] = (s == [::]). Proof. by []. Qed.

Lemma subseq_refl s : subseq s s.
Proof. by elim: s => //= x s IHs; rewrite eqxx. Qed.
Hint Resolve subseq_refl : core.

Lemma subseqP s1 s2 :
  reflect (exists2 m, size m = size s2 & s1 = mask m s2) (subseq s1 s2).
Proof.
elim: s2 s1 => [|y s2 IHs2] [|x s1].
- by left; exists [::].
- by right=> -[m /eqP/nilP->].
- by left; exists (nseq (size s2).+1 false); rewrite ?size_nseq //= mask_false.
apply: {IHs2}(iffP (IHs2 _)) => [] [m sz_m def_s1].
  by exists ((x == y) :: m); rewrite /= ?sz_m // -def_s1; case: eqP => // ->.
case: eqP => [_ | ne_xy]; last first.
  by case: m def_s1 sz_m => [|[] m] //; [case | move=> -> [<-]; exists m].
pose i := index true m; have def_m_i: take i m = nseq (size (take i m)) false.
  apply/all_pred1P; apply/(all_nthP true) => j.
  rewrite size_take ltnNge geq_min negb_or -ltnNge => /andP[lt_j_i _].
  rewrite nth_take //= -negb_add addbF -addbT -negb_eqb.
  by rewrite [_ == _](before_find _ lt_j_i).
have lt_i_m: i < size m.
  rewrite ltnNge; apply/negP=> le_m_i; rewrite take_oversize // in def_m_i.
  by rewrite def_m_i mask_false in def_s1.
rewrite size_take lt_i_m in def_m_i.
exists (take i m ++ drop i.+1 m).
  rewrite size_cat size_take size_drop lt_i_m.
  by rewrite sz_m in lt_i_m *; rewrite subnKC.
rewrite {s1 def_s1}[s1](congr1 behead def_s1).
rewrite -[s2](cat_take_drop i) -[m in LHS](cat_take_drop i) {}def_m_i -cat_cons.
have sz_i_s2: size (take i s2) = i by apply: size_takel; rewrite sz_m in lt_i_m.
rewrite lastI cat_rcons !mask_cat ?size_nseq ?size_belast ?mask_false //=.
by rewrite (drop_nth true) // nth_index -?index_mem.
Qed.

Lemma mask_subseq m s : subseq (mask m s) s.
Proof. by apply/subseqP; have [m1] := resize_mask m s; exists m1. Qed.

Lemma subseq_trans : transitive subseq.
Proof.
move=> _ _ s /subseqP[m2 _ ->] /subseqP[m1 _ ->].
elim: s => [|x s IHs] in m2 m1 *; first by rewrite !mask0.
case: m1 => [|[] m1]; first by rewrite mask0.
  case: m2 => [|[] m2] //; first by rewrite /= eqxx IHs.
  case/subseqP: (IHs m2 m1) => m sz_m def_s; apply/subseqP.
  by exists (false :: m); rewrite //= sz_m.
case/subseqP: (IHs m2 m1) => m sz_m def_s; apply/subseqP.
by exists (false :: m); rewrite //= sz_m.
Qed.

Lemma cat_subseq s1 s2 s3 s4 :
  subseq s1 s3 -> subseq s2 s4 -> subseq (s1 ++ s2) (s3 ++ s4).
Proof.
case/subseqP=> m1 sz_m1 -> /subseqP [m2 sz_m2 ->]; apply/subseqP.
by exists (m1 ++ m2); rewrite ?size_cat ?mask_cat ?sz_m1 ?sz_m2.
Qed.

Lemma prefix_subseq s1 s2 : subseq s1 (s1 ++ s2).
Proof. by rewrite -[s1 in subseq s1]cats0 cat_subseq ?sub0seq. Qed.

Lemma suffix_subseq s1 s2 : subseq s2 (s1 ++ s2).
Proof. exact: cat_subseq (sub0seq s1) _. Qed.

Lemma take_subseq s i : subseq (take i s) s.
Proof. by rewrite -[s in X in subseq _ X](cat_take_drop i) prefix_subseq. Qed.

Lemma drop_subseq s i : subseq (drop i s) s.
Proof. by rewrite -[s in X in subseq _ X](cat_take_drop i) suffix_subseq. Qed.

Lemma mem_subseq s1 s2 : subseq s1 s2 -> {subset s1 <= s2}.
Proof. by case/subseqP=> m _ -> x; apply: mem_mask. Qed.

Lemma sub1seq x s : subseq [:: x] s = (x \in s).
Proof. by elim: s => //= y s /[1!inE]; case: ifP; rewrite ?sub0seq. Qed.

Lemma size_subseq s1 s2 : subseq s1 s2 -> size s1 <= size s2.
Proof. by case/subseqP=> m sz_m ->; rewrite size_mask -sz_m ?count_size. Qed.

Lemma size_subseq_leqif s1 s2 :
  subseq s1 s2 -> size s1 <= size s2 ?= iff (s1 == s2).
Proof.
move=> sub12; split; first exact: size_subseq.
apply/idP/eqP=> [|-> //]; case/subseqP: sub12 => m sz_m ->{s1}.
rewrite size_mask -sz_m // -all_count -(eq_all eqb_id).
by move/(@all_pred1P _ true)->; rewrite sz_m mask_true.
Qed.

Lemma subseq_anti : antisymmetric subseq.
Proof.
move=> s1 s2 /andP[] /size_subseq_leqif /leqifP.
by case: eqP => [//|_] + /size_subseq; rewrite ltnNge => /negP.
Qed.

Lemma subseq_cons s x : subseq s (x :: s).
Proof. exact: suffix_subseq [:: x] s. Qed.

Lemma cons_subseq s1 s2 x : subseq (x :: s1) s2 -> subseq s1 s2.
Proof. exact/subseq_trans/subseq_cons. Qed.

Lemma subseq_rcons s x : subseq s (rcons s x).
Proof. by rewrite -cats1 prefix_subseq. Qed.

Lemma subseq_uniq s1 s2 : subseq s1 s2 -> uniq s2 -> uniq s1.
Proof. by case/subseqP=> m _ -> Us2; apply: mask_uniq. Qed.

Lemma take_uniq s n : uniq s -> uniq (take n s).
Proof. exact/subseq_uniq/take_subseq. Qed.

Lemma drop_uniq s n : uniq s -> uniq (drop n s).
Proof. exact/subseq_uniq/drop_subseq. Qed.

Lemma undup_subseq s : subseq (undup s) s.
Proof.
elim: s => //= x s; case: (_ \in _); last by rewrite eqxx.
by case: (undup s) => //= y u; case: (_ == _) => //=; apply: cons_subseq.
Qed.

Lemma subseq_rev s1 s2 : subseq (rev s1) (rev s2) = subseq s1 s2.
Proof.
wlog suff W : s1 s2 / subseq s1 s2 -> subseq (rev s1) (rev s2).
  by apply/idP/idP => /W //; rewrite !revK.
by case/subseqP => m size_m ->; rewrite rev_mask // mask_subseq.
Qed.

Lemma subseq_cat2l s s1 s2 : subseq (s ++ s1) (s ++ s2) = subseq s1 s2.
Proof. by elim: s => // x s IHs; rewrite !cat_cons /= eqxx. Qed.

Lemma subseq_cat2r s s1 s2 : subseq (s1 ++ s) (s2 ++ s) = subseq s1 s2.
Proof. by rewrite -subseq_rev !rev_cat subseq_cat2l subseq_rev. Qed.

Lemma subseq_rot p s n :
  subseq p s -> exists2 k, k <= n & subseq (rot k p) (rot n s).
Proof.
move=> /subseqP[m size_m ->].
exists (count id (take n m)); last by rewrite -mask_rot // mask_subseq.
by rewrite (leq_trans (count_size _ _))// size_take_min geq_minl.
Qed.

End Subseq.

Prenex Implicits subseq.
Arguments subseqP {T s1 s2}.

#[global] Hint Resolve subseq_refl : core.

Section Rem.

Variables (T : eqType) (x : T).

Fixpoint rem s := if s is y :: t then (if y == x then t else y :: rem t) else s.

Lemma rem_cons y s : rem (y :: s) = if y == x then s else y :: rem s.
Proof. by []. Qed.

Lemma remE s : rem s = take (index x s) s ++ drop (index x s).+1 s.
Proof. by elim: s => //= y s ->; case: eqVneq; rewrite ?drop0. Qed.

Lemma rem_id s : x \notin s -> rem s = s.
Proof. by elim: s => //= y s IHs /norP[neq_yx /IHs->]; case: eqVneq neq_yx. Qed.

Lemma perm_to_rem s : x \in s -> perm_eq s (x :: rem s).
Proof.
move=> xs; rewrite remE -[X in perm_eq X](cat_take_drop (index x s)).
by rewrite drop_index// -cat1s perm_catCA cat1s.
Qed.

Lemma size_rem s : x \in s -> size (rem s) = (size s).-1.
Proof. by move/perm_to_rem/perm_size->. Qed.

Lemma rem_subseq s : subseq (rem s) s.
Proof.
elim: s => //= y s IHs; rewrite eq_sym.
by case: ifP => _; [apply: subseq_cons | rewrite eqxx].
Qed.

Lemma rem_uniq s : uniq s -> uniq (rem s).
Proof. by apply: subseq_uniq; apply: rem_subseq. Qed.

Lemma mem_rem s : {subset rem s <= s}.
Proof. exact: mem_subseq (rem_subseq s). Qed.

Lemma rem_filter s : uniq s -> rem s = filter (predC1 x) s.
Proof.
elim: s => //= y s IHs /andP[not_s_y /IHs->].
by case: eqP => //= <-; apply/esym/all_filterP; rewrite all_predC has_pred1.
Qed.

Lemma mem_rem_uniq s : uniq s -> rem s =i [predD1 s & x].
Proof. by move/rem_filter=> -> y; rewrite mem_filter. Qed.

Lemma mem_rem_uniqF s : uniq s -> x \in rem s = false.
Proof. by move/mem_rem_uniq->; rewrite inE eqxx. Qed.

Lemma count_rem P s : count P (rem s) = count P s - (x \in s) && P x.
Proof.
have [/perm_to_rem/permP->|xNs]/= := boolP (x \in s); first by rewrite addKn.
by rewrite subn0 rem_id.
Qed.

Lemma count_mem_rem y s : count_mem y (rem s) = count_mem y s - (x == y).
Proof.
rewrite count_rem; have []//= := boolP (x \in s).
by case: eqP => // <- /count_memPn->.
Qed.

End Rem.

Section Map.

Variables (n0 : nat) (T1 : Type) (x1 : T1).
Variables (T2 : Type) (x2 : T2) (f : T1 -> T2).

Fixpoint map s := if s is x :: s' then f x :: map s' else [::].

Lemma map_cons x s : map (x :: s) = f x :: map s.
Proof. by []. Qed.

Lemma map_nseq x : map (nseq n0 x) = nseq n0 (f x).
Proof. by elim: n0 => // *; congr (_ :: _). Qed.

Lemma map_cat s1 s2 : map (s1 ++ s2) = map s1 ++ map s2.
Proof. by elim: s1 => [|x s1 IHs] //=; rewrite IHs. Qed.

Lemma size_map s : size (map s) = size s.
Proof. by elim: s => //= x s ->. Qed.

Lemma behead_map s : behead (map s) = map (behead s).
Proof. by case: s. Qed.

Lemma nth_map n s : n < size s -> nth x2 (map s) n = f (nth x1 s n).
Proof. by elim: s n => [|x s IHs] []. Qed.

Lemma map_rcons s x : map (rcons s x) = rcons (map s) (f x).
Proof. by rewrite -!cats1 map_cat. Qed.

Lemma last_map s x : last (f x) (map s) = f (last x s).
Proof. by elim: s x => /=. Qed.

Lemma belast_map s x : belast (f x) (map s) = map (belast x s).
Proof. by elim: s x => //= y s IHs x; rewrite IHs. Qed.

Lemma filter_map a s : filter a (map s) = map (filter (preim f a) s).
Proof. by elim: s => //= x s IHs; rewrite (fun_if map) /= IHs. Qed.

Lemma find_map a s : find a (map s) = find (preim f a) s.
Proof. by elim: s => //= x s ->. Qed.

Lemma has_map a s : has a (map s) = has (preim f a) s.
Proof. by elim: s => //= x s ->. Qed.

Lemma all_map a s : all a (map s) = all (preim f a) s.
Proof. by elim: s => //= x s ->. Qed.

Lemma all_mapT (a : pred T2) s : (forall x, a (f x)) -> all a (map s).
Proof. by rewrite all_map => /allT->. Qed.

Lemma count_map a s : count a (map s) = count (preim f a) s.
Proof. by elim: s => //= x s ->. Qed.

Lemma map_take s : map (take n0 s) = take n0 (map s).
Proof. by elim: n0 s => [|n IHn] [|x s] //=; rewrite IHn. Qed.

Lemma map_drop s : map (drop n0 s) = drop n0 (map s).
Proof. by elim: n0 s => [|n IHn] [|x s] //=; rewrite IHn. Qed.

Lemma map_rot s : map (rot n0 s) = rot n0 (map s).
Proof. by rewrite /rot map_cat map_take map_drop. Qed.

Lemma map_rotr s : map (rotr n0 s) = rotr n0 (map s).
Proof. by apply: canRL (rotK n0) _; rewrite -map_rot rotrK. Qed.

Lemma map_rev s : map (rev s) = rev (map s).
Proof. by elim: s => //= x s IHs; rewrite !rev_cons -!cats1 map_cat IHs. Qed.

Lemma map_mask m s : map (mask m s) = mask m (map s).
Proof. by elim: m s => [|[|] m IHm] [|x p] //=; rewrite IHm. Qed.

Lemma inj_map : injective f -> injective map.
Proof. by move=> injf; elim=> [|x s IHs] [|y t] //= [/injf-> /IHs->]. Qed.

Lemma inj_in_map (A : {pred T1}) :
  {in A &, injective f} -> {in [pred s | all [in A] s] &, injective map}.
Proof.
move=> injf; elim=> [|x s IHs] [|y t] //= /andP[Ax As] /andP[Ay At].
by case=> /injf-> // /IHs->.
Qed.

End Map.

Notation "[ 'seq' E | i <- s ]" := (map (fun i => E) s)
  (at level 0, E at level 99, i name,
   format "[ '[hv' 'seq'  E '/ '  |  i  <-  s ] ']'") : seq_scope.

Notation "[ 'seq' E | i <- s & C ]" := [seq E | i <- [seq i <- s | C]]
  (at level 0, E at level 99, i name,
   format "[ '[hv' 'seq'  E '/ '  |  i  <-  s '/ '  &  C ] ']'") : seq_scope.

Notation "[ 'seq' E | i : T <- s ]" := (map (fun i : T => E) s)
  (at level 0, E at level 99, i name, only parsing) : seq_scope.

Notation "[ 'seq' E | i : T <- s & C ]" :=
  [seq E | i : T <- [seq i : T <- s | C]]
  (at level 0, E at level 99, i name, only parsing) : seq_scope.

Notation "[ 'seq' E : R | i <- s ]" := (@map _ R (fun i => E) s)
  (at level 0, E at level 99, i name, only parsing) : seq_scope.

Notation "[ 'seq' E : R | i <- s & C ]" := [seq E : R | i <- [seq i <- s | C]]
  (at level 0, E at level 99, i name, only parsing) : seq_scope.

Notation "[ 'seq' E : R | i : T <- s ]" := (@map T R (fun i : T => E) s)
  (at level 0, E at level 99, i name, only parsing) : seq_scope.

Notation "[ 'seq' E : R | i : T <- s & C ]" :=
  [seq E : R | i : T <- [seq i : T <- s | C]]
  (at level 0, E at level 99, i name, only parsing) : seq_scope.

Lemma filter_mask T a (s : seq T) : filter a s = mask (map a s) s.
Proof. by elim: s => //= x s <-; case: (a x). Qed.

Lemma all_sigP T a (s : seq T) : all a s -> {s' : seq (sig a) | s = map sval s'}.
Proof.
elim: s => /= [_|x s ihs /andP [ax /ihs [s' ->]]]; first by exists [::].
by exists (exist a x ax :: s').
Qed.

Section MiscMask.

Lemma leq_count_mask T (P : {pred T}) m s : count P (mask m s) <= count P s.
Proof.
by elim: s m => [|x s IHs] [|[] m]//=;
   rewrite ?leq_add2l (leq_trans (IHs _)) ?leq_addl.
Qed.

Variable (T : eqType).
Implicit Types (s : seq T) (m : bitseq).

Lemma mask_filter s m : uniq s -> mask m s = [seq i <- s | i \in mask m s].
Proof.
elim: m s => [|[] m IH] [|x s /= /andP[/negP xS uS]]; rewrite ?filter_pred0 //.
  rewrite inE eqxx /=; congr cons; rewrite [LHS]IH//.
  by apply/eq_in_filter => ? /[1!inE]; case: eqP => [->|].
by case: ifP => [/mem_mask //|_]; apply: IH.
Qed.

Lemma leq_count_subseq P s1 s2 : subseq s1 s2 -> count P s1 <= count P s2.
Proof. by move=> /subseqP[m _ ->]; rewrite leq_count_mask. Qed.

Lemma count_maskP s1 s2 :
  (forall x, count_mem x s1 <= count_mem x s2) <->
    exists2 m : bitseq, size m = size s2 & perm_eq s1 (mask m s2).
Proof.
split=> [s1_le|[m _ /permP s1ms2 x]]; last by rewrite s1ms2 leq_count_mask.
suff [m mP]: exists m, perm_eq s1 (mask m s2).
  by have [m' sm' eqm] := resize_mask m s2; exists m'; rewrite -?eqm.
elim: s2 => [|x s2 IHs]//= in s1 s1_le *.
  by exists [::]; apply/allP => x _/=; rewrite eqn_leq s1_le.
have [y|m s1s2] := IHs (rem x s1); first by rewrite count_mem_rem leq_subLR.
exists ((x \in s1) :: m); have [|/rem_id<-//] := boolP (x \in s1).
by move/perm_to_rem/permPl->; rewrite perm_cons.
Qed.

Lemma count_subseqP s1 s2 :
  (forall x, count_mem x s1 <= count_mem x s2) <->
    exists2 s, subseq s s2 & perm_eq s1 s.
Proof.
rewrite count_maskP; split=> [[m _]|[_/subseqP[m sm ->]]]; last by exists m.
by exists (mask m s2); rewrite ?mask_subseq.
Qed.

End MiscMask.

Section FilterSubseq.

Variable T : eqType.
Implicit Types (s : seq T) (a : pred T).

Lemma filter_subseq a s : subseq (filter a s) s.
Proof. by apply/subseqP; exists (map a s); rewrite ?size_map ?filter_mask. Qed.

Lemma subseq_filter s1 s2 a :
  subseq s1 (filter a s2) = all a s1 && subseq s1 s2.
Proof.
elim: s2 s1 => [|x s2 IHs] [|y s1] //=; rewrite ?andbF ?sub0seq //.
by case a_x: (a x); rewrite /= !IHs /=; case: eqP => // ->; rewrite a_x.
Qed.

Lemma subseq_uniqP s1 s2 :
  uniq s2 -> reflect (s1 = filter [in s1] s2) (subseq s1 s2).
Proof.
move=> uniq_s2; apply: (iffP idP) => [ss12 | ->]; last exact: filter_subseq.
apply/eqP; rewrite -size_subseq_leqif ?subseq_filter ?(introT allP) //.
apply/eqP/esym/perm_size.
rewrite uniq_perm ?filter_uniq ?(subseq_uniq ss12) // => x.
by rewrite mem_filter; apply: andb_idr; apply: (mem_subseq ss12).
Qed.

Lemma uniq_subseq_pivot x (s1 s2 s3 s4 : seq T) (s := s3 ++ x :: s4) :
  uniq s -> subseq (s1 ++ x :: s2) s = (subseq s1 s3 && subseq s2 s4).
Proof.
move=> uniq_s; apply/idP/idP => [sub_s'_s|/andP[? ?]]; last first.
  by rewrite cat_subseq //= eqxx.
have uniq_s' := subseq_uniq sub_s'_s uniq_s.
have/eqP {sub_s'_s uniq_s} := subseq_uniqP _ uniq_s sub_s'_s.
rewrite !filter_cat /= mem_cat inE eqxx orbT /=.
rewrite uniq_eqseq_pivotl // => /andP [/eqP -> /eqP ->].
by rewrite !filter_subseq.
Qed.

Lemma perm_to_subseq s1 s2 :
  subseq s1 s2 -> {s3 | perm_eq s2 (s1 ++ s3)}.
Proof.
elim Ds2: s2 s1 => [|y s2' IHs] [|x s1] //=; try by exists s2; rewrite Ds2.
case: eqP => [-> | _] /IHs[s3 perm_s2] {IHs}.
  by exists s3; rewrite perm_cons.
by exists (rcons s3 y); rewrite -cat_cons -perm_rcons -!cats1 catA perm_cat2r.
Qed.

Lemma subseq_rem x : {homo rem x : s1 s2 / @subseq T s1 s2}.
Proof.
move=> s1 s2; elim: s2 s1 => [|x2 s2 IHs2] [|x1 s1]; rewrite ?sub0seq //=.
have [->|_] := eqVneq x1 x2; first by case: eqP => //= _ /IHs2; rewrite eqxx.
move=> /IHs2/subseq_trans->//.
by have [->|_] := eqVneq x x2; [apply: rem_subseq|apply: subseq_cons].
Qed.

End FilterSubseq.

Arguments subseq_uniqP [T s1 s2].

Section EqMap.

Variables (n0 : nat) (T1 : eqType) (x1 : T1).
Variables (T2 : eqType) (x2 : T2) (f : T1 -> T2).
Implicit Type s : seq T1.

Lemma map_f s x : x \in s -> f x \in map f s.
Proof.
by elim: s => //= y s IHs /predU1P[->|/IHs]; [apply: predU1l | apply: predU1r].
Qed.

Lemma mapP s y : reflect (exists2 x, x \in s & y = f x) (y \in map f s).
Proof.
elim: s => [|x s IHs]; [by right; case|rewrite /= inE].
exact: equivP (orPP eqP IHs) (iff_sym exists_cons).
Qed.

Lemma subset_mapP (s : seq T1) (s' : seq T2) :
    {subset s' <= map f s} <-> exists2 t, all (mem s) t & s' = map f t.
Proof.
split => [|[r /allP/= rE ->] _ /mapP[x xr ->]]; last by rewrite map_f ?rE.
elim: s' => [|x s' IHs'] subss'; first by exists [::].
have /mapP[y ys ->] := subss' _ (mem_head _ _).
have [x' x's'|t st ->] := IHs'; first by rewrite subss'// inE x's' orbT.
by exists (y :: t); rewrite //= ys st.
Qed.

Lemma map_uniq s : uniq (map f s) -> uniq s.
Proof.
elim: s => //= x s IHs /andP[not_sfx /IHs->]; rewrite andbT.
by apply: contra not_sfx => sx; apply/mapP; exists x.
Qed.

Lemma map_inj_in_uniq s : {in s &, injective f} -> uniq (map f s) = uniq s.
Proof.
elim: s => //= x s IHs //= injf; congr (~~ _ && _).
  apply/mapP/idP=> [[y sy /injf] | ]; last by exists x.
  by rewrite mem_head mem_behead // => ->.
by apply: IHs => y z sy sz; apply: injf => //; apply: predU1r.
Qed.

Lemma map_subseq s1 s2 : subseq s1 s2 -> subseq (map f s1) (map f s2).
Proof.
case/subseqP=> m sz_m ->; apply/subseqP.
by exists m; rewrite ?size_map ?map_mask.
Qed.

Lemma nth_index_map s x0 x :
  {in s &, injective f} -> x \in s -> nth x0 s (index (f x) (map f s)) = x.
Proof.
elim: s => //= y s IHs inj_f s_x; rewrite (inj_in_eq inj_f) ?mem_head //.
move: s_x; rewrite inE; have [-> // | _] := eqVneq; apply: IHs.
by apply: sub_in2 inj_f => z; apply: predU1r.
Qed.

Lemma perm_map s t : perm_eq s t -> perm_eq (map f s) (map f t).
Proof. by move/permP=> Est; apply/permP=> a; rewrite !count_map Est. Qed.

Lemma sub_map s1 s2 : {subset s1 <= s2} -> {subset map f s1 <= map f s2}.
Proof. by move=> sub_s ? /mapP[x x_s ->]; rewrite map_f ?sub_s. Qed.

Lemma eq_mem_map s1 s2 : s1 =i s2 -> map f s1 =i map f s2.
Proof. by move=> Es x; apply/idP/idP; apply: sub_map => ?; rewrite Es. Qed.

Hypothesis Hf : injective f.

Lemma mem_map s x : (f x \in map f s) = (x \in s).
Proof. by apply/mapP/idP=> [[y Hy /Hf->] //|]; exists x. Qed.

Lemma index_map s x : index (f x) (map f s) = index x s.
Proof. by rewrite /index; elim: s => //= y s IHs; rewrite (inj_eq Hf) IHs. Qed.

Lemma map_inj_uniq s : uniq (map f s) = uniq s.
Proof. by apply: map_inj_in_uniq; apply: in2W. Qed.

Lemma undup_map_inj s : undup (map f s) = map f (undup s).
Proof. by elim: s => //= s0 s ->; rewrite mem_map //; case: (_ \in _). Qed.

Lemma perm_map_inj s t : perm_eq (map f s) (map f t) -> perm_eq s t.
Proof.
move/permP=> Est; apply/allP=> x _ /=.
have Dx: pred1 x =1 preim f (pred1 (f x)) by move=> y /=; rewrite inj_eq.
by rewrite !(eq_count Dx) -!count_map Est.
Qed.

End EqMap.

Arguments mapP {T1 T2 f s y}.
Arguments subset_mapP {T1 T2}.

Lemma map_of_seq (T1 : eqType) T2 (s : seq T1) (fs : seq T2) (y0 : T2) :
  {f | uniq s -> size fs = size s -> map f s = fs}.
Proof.
exists (fun x => nth y0 fs (index x s)) => uAs eq_sz.
apply/esym/(@eq_from_nth _ y0); rewrite ?size_map eq_sz // => i ltis.
by have x0 : T1 by [case: (s) ltis]; rewrite (nth_map x0) // index_uniq.
Qed.

Section MapComp.

Variable S T U : Type.

Lemma map_id (s : seq T) : map id s = s.
Proof. by elim: s => //= x s ->. Qed.

Lemma eq_map (f g : S -> T) : f =1 g -> map f =1 map g.
Proof. by move=> Ef; elim=> //= x s ->; rewrite Ef. Qed.

Lemma map_comp (f : T -> U) (g : S -> T) s : map (f \o g) s = map f (map g s).
Proof. by elim: s => //= x s ->. Qed.

Lemma mapK (f : S -> T) (g : T -> S) : cancel f g -> cancel (map f) (map g).
Proof. by move=> fK; elim=> //= x s ->; rewrite fK. Qed.

Lemma mapK_in (A : {pred S}) (f : S -> T) (g : T -> S) :
  {in A, cancel f g} -> {in [pred s | all [in A] s], cancel (map f) (map g)}.
Proof. by move=> fK; elim=> //= x s IHs /andP[/fK-> /IHs->]. Qed.

End MapComp.

Lemma eq_in_map (S : eqType) T (f g : S -> T) (s : seq S) : 
  {in s, f =1 g} <-> map f s = map g s.
Proof.
by elim: s => //= x s IHs; rewrite forall_cons IHs; split => -[-> ->].
Qed.

Lemma map_id_in (T : eqType) f (s : seq T) : {in s, f =1 id} -> map f s = s.
Proof. by move/eq_in_map->; apply: map_id. Qed.

(* Map a partial function *)

Section Pmap.

Variables (aT rT : Type) (f : aT -> option rT) (g : rT -> aT).

Fixpoint pmap s :=
  if s is x :: s' then let r := pmap s' in oapp (cons^~ r) r (f x) else [::].

Lemma map_pK : pcancel g f -> cancel (map g) pmap.
Proof. by move=> gK; elim=> //= x s ->; rewrite gK. Qed.

Lemma size_pmap s : size (pmap s) = count [eta f] s.
Proof. by elim: s => //= x s <-; case: (f _). Qed.

Lemma pmapS_filter s : map some (pmap s) = map f (filter [eta f] s).
Proof. by elim: s => //= x s; case fx: (f x) => //= [u] <-; congr (_ :: _). Qed.

Hypothesis fK : ocancel f g.

Lemma pmap_filter s : map g (pmap s) = filter [eta f] s.
Proof. by elim: s => //= x s <-; rewrite -{3}(fK x); case: (f _). Qed.

Lemma pmap_cat s t : pmap (s ++ t) = pmap s ++ pmap t.
Proof. by elim: s => //= x s ->; case/f: x. Qed.

Lemma all_pmap (p : pred rT) s :
  all p (pmap s) = all [pred i | oapp p true (f i)] s.
Proof. by elim: s => //= x s <-; case: f. Qed.

End Pmap.

Lemma eq_in_pmap (aT : eqType) rT (f1 f2 : aT -> option rT) s :
  {in s, f1 =1 f2} -> pmap f1 s = pmap f2 s.
Proof. by elim: s => //= a s IHs /forall_cons [-> /IHs ->]. Qed.

Lemma eq_pmap aT rT (f1 f2 : aT -> option rT) :
  f1 =1 f2 -> pmap f1 =1 pmap f2.
Proof. by move=> Ef; elim => //= a s ->; rewrite Ef. Qed.

Section EqPmap.

Variables (aT rT : eqType) (f : aT -> option rT) (g : rT -> aT).

Lemma mem_pmap s u : (u \in pmap f s) = (Some u \in map f s).
Proof. by elim: s => //= x s IHs; rewrite in_cons -IHs; case: (f x). Qed.

Hypothesis fK : ocancel f g.

Lemma can2_mem_pmap : pcancel g f -> forall s u, (u \in pmap f s) = (g u \in s).
Proof.
by move=> gK s u; rewrite -(mem_map (pcan_inj gK)) pmap_filter // mem_filter gK.
Qed.

Lemma pmap_uniq s : uniq s -> uniq (pmap f s).
Proof. move/(filter_uniq f); rewrite -(pmap_filter fK); exact: map_uniq. Qed.

Lemma perm_pmap s t : perm_eq s t -> perm_eq (pmap f s) (pmap f t).
Proof.
move=> eq_st; apply/(perm_map_inj Some_inj); rewrite !pmapS_filter.
exact/perm_map/perm_filter.
Qed.

End EqPmap.

Section PmapSub.

Variables (T : Type) (p : pred T) (sT : subType p).

Lemma size_pmap_sub s : size (pmap (insub : T -> option sT) s) = count p s.
Proof. by rewrite size_pmap (eq_count (isSome_insub _)). Qed.

End PmapSub.

Section EqPmapSub.

Variables (T : eqType) (p : pred T) (sT : subEqType p).

Let insT : T -> option sT := insub.

Lemma mem_pmap_sub s u : (u \in pmap insT s) = (val u \in s).
Proof. exact/(can2_mem_pmap (insubK _))/valK. Qed.

Lemma pmap_sub_uniq s : uniq s -> uniq (pmap insT s).
Proof. exact: (pmap_uniq (insubK _)). Qed.

End EqPmapSub.

(* Index sequence *)

Fixpoint iota m n := if n is n'.+1 then m :: iota m.+1 n' else [::].

Lemma size_iota m n : size (iota m n) = n.
Proof. by elim: n m => //= n IHn m; rewrite IHn. Qed.

Lemma iotaD m n1 n2 : iota m (n1 + n2) = iota m n1 ++ iota (m + n1) n2.
Proof. by elim: n1 m => [|n1 IHn1] m; rewrite ?addn0 // -addSnnS /= -IHn1. Qed.

Lemma iotaDl m1 m2 n : iota (m1 + m2) n = map (addn m1) (iota m2 n).
Proof. by elim: n m2 => //= n IHn m2; rewrite -addnS IHn. Qed.

Lemma nth_iota p m n i : i < n -> nth p (iota m n) i = m + i.
Proof.
by move/subnKC <-; rewrite addSnnS iotaD nth_cat size_iota ltnn subnn.
Qed.

Lemma mem_iota m n i : (i \in iota m n) = (m <= i < m + n).
Proof.
elim: n m => [|n IHn] /= m; first by rewrite addn0 ltnNge andbN.
by rewrite in_cons IHn addnS ltnS; case: ltngtP => // ->; rewrite leq_addr.
Qed.

Lemma iota_uniq m n : uniq (iota m n).
Proof. by elim: n m => //= n IHn m; rewrite mem_iota ltnn /=. Qed.

Lemma take_iota k m n : take k (iota m n) = iota m (minn k n).
Proof.
have [lt_k_n|le_n_k] := ltnP.
  by elim: k n lt_k_n m => [|k IHk] [|n] //= H m; rewrite IHk.
by apply: take_oversize; rewrite size_iota.
Qed.

Lemma drop_iota k m n : drop k (iota m n) = iota (m + k) (n - k).
Proof.
by elim: k m n => [|k IHk] m [|n] //=; rewrite ?addn0 // IHk addnS subSS.
Qed.

Lemma filter_iota_ltn m n j : j <= n ->
  [seq i <- iota m n | i < m + j] = iota m j.
Proof.
elim: n m j => [m j|n IHn m [|j] jlen]; first by rewrite leqn0 => /eqP ->.
  rewrite (@eq_in_filter _ _ pred0) ?filter_pred0// => i.
  by rewrite addn0 ltnNge mem_iota => /andP[->].
by rewrite /= addnS leq_addr -addSn IHn.
Qed.

Lemma filter_iota_leq n m j : j < n ->
  [seq i <- iota m n | i <= m + j] = iota m j.+1.
Proof.
elim: n m j => [//|n IHn] m [|j] jlen /=; rewrite leq_addr.
  rewrite (@eq_in_filter _ _ pred0) ?filter_pred0// => i.
  by rewrite addn0 leqNgt mem_iota => /andP[->].
by rewrite addnS -addSn IHn -1?ltnS.
Qed.

(* Making a sequence of a specific length, using indexes to compute items. *)

Section MakeSeq.

Variables (T : Type) (x0 : T).

Definition mkseq f n : seq T := map f (iota 0 n).

Lemma size_mkseq f n : size (mkseq f n) = n.
Proof. by rewrite size_map size_iota. Qed.

Lemma mkseqS f n : 
  mkseq f n.+1 = rcons (mkseq f n) (f n).
Proof. by rewrite /mkseq -addn1 iotaD add0n map_cat cats1. Qed.

Lemma eq_mkseq f g : f =1 g -> mkseq f =1 mkseq g.
Proof. by move=> Efg n; apply: eq_map Efg _. Qed.

Lemma nth_mkseq f n i : i < n -> nth x0 (mkseq f n) i = f i.
Proof. by move=> Hi; rewrite (nth_map 0) ?nth_iota ?size_iota. Qed.

Lemma mkseq_nth s : mkseq (nth x0 s) (size s) = s.
Proof.
by apply: (@eq_from_nth _ x0); rewrite size_mkseq // => i Hi; rewrite nth_mkseq.
Qed.

Variant mkseq_spec s : seq T -> Type :=
| MapIota n f : s = mkseq f n -> mkseq_spec s (mkseq f n).

Lemma mkseqP s : mkseq_spec s s.
Proof. by rewrite -[s]mkseq_nth; constructor. Qed.

Lemma map_nth_iota0 s i :
  i <= size s -> [seq nth x0 s j | j <- iota 0 i] = take i s.
Proof.
by move=> ile; rewrite -[s in RHS]mkseq_nth -map_take take_iota (minn_idPl _).
Qed.

Lemma map_nth_iota s i j : j <= size s - i ->
  [seq nth x0 s k | k <- iota i j] = take j (drop i s).
Proof.
elim: i => [|i IH] in s j *; first by rewrite subn0 drop0 => /map_nth_iota0->.
case: s => [|x s /IH<-]; first by rewrite leqn0 => /eqP->.
by rewrite -add1n iotaDl -map_comp.
Qed.

End MakeSeq.

Section MakeEqSeq.

Variable T : eqType.

Lemma mkseq_uniqP (f : nat -> T) n :
  reflect {in gtn n &, injective f} (uniq (mkseq f n)).
Proof.
apply: (equivP (uniqP (f 0))); rewrite size_mkseq.
by split=> injf i j lti ltj; have:= injf i j lti ltj; rewrite !nth_mkseq.
Qed.

Lemma mkseq_uniq (f : nat -> T) n : injective f -> uniq (mkseq f n).
Proof. by move/map_inj_uniq->; apply: iota_uniq. Qed.

Lemma perm_iotaP {s t : seq T} x0 (It := iota 0 (size t)) :
  reflect (exists2 Is, perm_eq Is It & s = map (nth x0 t) Is) (perm_eq s t).
Proof.
apply: (iffP idP) => [Est | [Is eqIst ->]]; last first.
  by rewrite -{2}[t](mkseq_nth x0) perm_map.
elim: t => [|x t IHt] in s It Est *.
  by rewrite (perm_small_eq _ Est) //; exists [::].
have /rot_to[k s1 Ds]: x \in s by rewrite (perm_mem Est) mem_head.
have [|Is1 eqIst1 Ds1] := IHt s1; first by rewrite -(perm_cons x) -Ds perm_rot.
exists (rotr k (0 :: map succn Is1)).
  by rewrite perm_rot /It /= perm_cons (iotaDl 1) perm_map.
by rewrite map_rotr /= -map_comp -(@eq_map _ _ (nth x0 t)) // -Ds1 -Ds rotK.
Qed.

End MakeEqSeq.

Arguments perm_iotaP {T s t}.

Section FoldRight.

Variables (T : Type) (R : Type) (f : T -> R -> R) (z0 : R).

Fixpoint foldr s := if s is x :: s' then f x (foldr s') else z0.

End FoldRight.

Section FoldRightComp.

Variables (T1 T2 : Type) (h : T1 -> T2).
Variables (R : Type) (f : T2 -> R -> R) (z0 : R).

Lemma foldr_cat s1 s2 : foldr f z0 (s1 ++ s2) = foldr f (foldr f z0 s2) s1.
Proof. by elim: s1 => //= x s1 ->. Qed.

Lemma foldr_rcons s x : foldr f z0 (rcons s x) = foldr f (f x z0) s.
Proof. by rewrite -cats1 foldr_cat. Qed.

Lemma foldr_map s : foldr f z0 (map h s) = foldr (fun x z => f (h x) z) z0 s.
Proof. by elim: s => //= x s ->. Qed.

End FoldRightComp.

(* Quick characterization of the null sequence. *)

Definition sumn := foldr addn 0.

Lemma sumn_ncons x n s : sumn (ncons n x s) = x * n + sumn s.
Proof. by rewrite mulnC; elim: n => //= n ->; rewrite addnA. Qed.

Lemma sumn_nseq x n : sumn (nseq n x) = x * n.
Proof. by rewrite sumn_ncons addn0. Qed.

Lemma sumn_cat s1 s2 : sumn (s1 ++ s2) = sumn s1 + sumn s2.
Proof. by elim: s1 => //= x s1 ->; rewrite addnA. Qed.

Lemma sumn_count T (a : pred T) s : sumn [seq a i : nat | i <- s] = count a s.
Proof. by elim: s => //= s0 s /= ->. Qed.

Lemma sumn_rcons s n : sumn (rcons s n) = sumn s + n.
Proof. by rewrite -cats1 sumn_cat /= addn0. Qed.

Lemma perm_sumn s1 s2 : perm_eq s1 s2 -> sumn s1 = sumn s2.
Proof.
by apply/catCA_perm_subst: s1 s2 => s1 s2 s3; rewrite !sumn_cat addnCA.
Qed.

Lemma sumn_rot s n : sumn (rot n s) = sumn s.
Proof. by apply/perm_sumn; rewrite perm_rot. Qed.

Lemma sumn_rev s : sumn (rev s) = sumn s.
Proof. by apply/perm_sumn; rewrite perm_rev. Qed.

Lemma natnseq0P s : reflect (s = nseq (size s) 0) (sumn s == 0).
Proof.
apply: (iffP idP) => [|->]; last by rewrite sumn_nseq.
by elim: s => //= x s IHs; rewrite addn_eq0 => /andP[/eqP-> /IHs <-].
Qed.

Lemma sumn_set_nth s x0 n x :
  sumn (set_nth x0 s n x) =
    sumn s + x - (nth x0 s n) * (n < size s) + x0 * (n - size s).
Proof.
rewrite set_nthE; case: ltnP => [nlts|nges]; last first.
  by rewrite sumn_cat sumn_ncons /= addn0 muln0 subn0 addnAC addnA.
have -> : n - size s = 0 by apply/eqP; rewrite subn_eq0 ltnW.
rewrite -[in sumn s](cat_take_drop n s) [drop n s](drop_nth x0)//.
by rewrite !sumn_cat /= muln1 muln0 addn0 addnAC !addnA [in RHS]addnAC addnK.
Qed.

Lemma sumn_set_nth_ltn s x0 n x : n < size s ->
  sumn (set_nth x0 s n x) = sumn s + x - nth x0 s n.
Proof.
move=> nlts; rewrite sumn_set_nth nlts muln1.
have -> : n - size s = 0 by apply/eqP; rewrite subn_eq0 ltnW.
by rewrite muln0 addn0.
Qed.

Lemma sumn_set_nth0 s n x : sumn (set_nth 0 s n x) = sumn s + x - nth 0 s n.
Proof.
rewrite sumn_set_nth mul0n addn0.
by case: ltnP => [_|nges]; rewrite ?muln1// nth_default.
Qed.

Section FoldLeft.

Variables (T R : Type) (f : R -> T -> R).

Fixpoint foldl z s := if s is x :: s' then foldl (f z x) s' else z.

Lemma foldl_rev z s : foldl z (rev s) = foldr (fun x z => f z x) z s.
Proof.
by elim/last_ind: s z => // s x IHs z; rewrite rev_rcons -cats1 foldr_cat -IHs.
Qed.

Lemma foldl_cat z s1 s2 : foldl z (s1 ++ s2) = foldl (foldl z s1) s2.
Proof.
by rewrite -(revK (s1 ++ s2)) foldl_rev rev_cat foldr_cat -!foldl_rev !revK.
Qed.

Lemma foldl_rcons z s x : foldl z (rcons s x) = f (foldl z s) x.
Proof. by rewrite -cats1 foldl_cat. Qed.

End FoldLeft.

Section Scan.

Variables (T1 : Type) (x1 : T1) (T2 : Type) (x2 : T2).
Variables (f : T1 -> T1 -> T2) (g : T1 -> T2 -> T1).

Fixpoint pairmap x s := if s is y :: s' then f x y :: pairmap y s' else [::].

Lemma size_pairmap x s : size (pairmap x s) = size s.
Proof. by elim: s x => //= y s IHs x; rewrite IHs. Qed.

Lemma pairmap_cat x s1 s2 :
  pairmap x (s1 ++ s2) = pairmap x s1 ++ pairmap (last x s1) s2.
Proof. by elim: s1 x => //= y s1 IHs1 x; rewrite IHs1. Qed.

Lemma nth_pairmap s n : n < size s ->
  forall x, nth x2 (pairmap x s) n = f (nth x1 (x :: s) n) (nth x1 s n).
Proof. by elim: s n => [|y s IHs] [|n] //= Hn x; apply: IHs. Qed.

Fixpoint scanl x s :=
  if s is y :: s' then let x' := g x y in x' :: scanl x' s' else [::].

Lemma size_scanl x s : size (scanl x s) = size s.
Proof. by elim: s x => //= y s IHs x; rewrite IHs. Qed.

Lemma scanl_cat x s1 s2 :
  scanl x (s1 ++ s2) = scanl x s1 ++ scanl (foldl g x s1) s2.
Proof. by elim: s1 x => //= y s1 IHs1 x; rewrite IHs1. Qed.

Lemma scanl_rcons x s1 y  :
  scanl x (rcons s1 y) =  rcons (scanl x s1) (foldl g x (rcons s1 y)).
Proof. by rewrite -!cats1 scanl_cat foldl_cat. Qed.

Lemma nth_cons_scanl s n : n <= size s ->
  forall x, nth x1 (x :: scanl x s) n = foldl g x (take n s).
Proof. by elim: s n => [|y s IHs] [|n] Hn x //=; rewrite IHs. Qed.

Lemma nth_scanl s n : n < size s ->
  forall x, nth x1 (scanl x s) n = foldl g x (take n.+1 s).
Proof. by move=> n_lt x; rewrite -nth_cons_scanl. Qed.

Lemma scanlK :
  (forall x, cancel (g x) (f x)) -> forall x, cancel (scanl x) (pairmap x).
Proof. by move=> Hfg x s; elim: s x => //= y s IHs x; rewrite Hfg IHs. Qed.

Lemma pairmapK :
  (forall x, cancel (f x) (g x)) -> forall x, cancel (pairmap x) (scanl x).
Proof. by move=> Hgf x s; elim: s x => //= y s IHs x; rewrite Hgf IHs. Qed.

End Scan.

Prenex Implicits mask map pmap foldr foldl scanl pairmap.

Section Zip.

Variables (S T : Type) (r : S -> T -> bool).

Fixpoint zip (s : seq S) (t : seq T) {struct t} :=
  match s, t with
  | x :: s', y :: t' => (x, y) :: zip s' t'
  | _, _ => [::]
  end.

Definition unzip1 := map (@fst S T).
Definition unzip2 := map (@snd S T).

Fixpoint all2 s t :=
  match s, t with
  | [::], [::] => true
  | x :: s, y :: t => r x y && all2 s t
  | _, _ => false
  end.

Lemma zip_unzip s : zip (unzip1 s) (unzip2 s) = s.
Proof. by elim: s => [|[x y] s /= ->]. Qed.

Lemma unzip1_zip s t : size s <= size t -> unzip1 (zip s t) = s.
Proof. by elim: s t => [|x s IHs] [|y t] //= le_s_t; rewrite IHs. Qed.

Lemma unzip2_zip s t : size t <= size s -> unzip2 (zip s t) = t.
Proof. by elim: s t => [|x s IHs] [|y t] //= le_t_s; rewrite IHs. Qed.

Lemma size1_zip s t : size s <= size t -> size (zip s t) = size s.
Proof. by elim: s t => [|x s IHs] [|y t] //= Hs; rewrite IHs. Qed.

Lemma size2_zip s t : size t <= size s -> size (zip s t) = size t.
Proof. by elim: s t => [|x s IHs] [|y t] //= Hs; rewrite IHs. Qed.

Lemma size_zip s t : size (zip s t) = minn (size s) (size t).
Proof. by elim: s t => [|x s IHs] [|t2 t] //=; rewrite IHs minnSS. Qed.

Lemma zip_cat s1 s2 t1 t2 :
  size s1 = size t1 -> zip (s1 ++ s2) (t1 ++ t2) = zip s1 t1 ++ zip s2 t2.
Proof. by move: s1 t1; apply: seq_ind2 => //= x y s1 t1 _ ->. Qed.

Lemma nth_zip x y s t i :
  size s = size t -> nth (x, y) (zip s t) i = (nth x s i, nth y t i).
Proof. by elim: i s t => [|i IHi] [|y1 s1] [|y2 t] //= [/IHi->]. Qed.

Lemma nth_zip_cond p s t i :
   nth p (zip s t) i
     = (if i < size (zip s t) then (nth p.1 s i, nth p.2 t i) else p).
Proof.
rewrite size_zip ltnNge geq_min.
by elim: s t i => [|x s IHs] [|y t] [|i] //=; rewrite ?orbT -?IHs.
Qed.

Lemma zip_rcons s t x y :
  size s = size t -> zip (rcons s x) (rcons t y) = rcons (zip s t) (x, y).
Proof. by move=> eq_sz; rewrite -!cats1 zip_cat //= eq_sz. Qed.

Lemma rev_zip s t : size s = size t -> rev (zip s t) = zip (rev s) (rev t).
Proof.
move: s t; apply: seq_ind2 => //= x y s t eq_sz IHs.
by rewrite !rev_cons IHs zip_rcons ?size_rev.
Qed.

Lemma all2E s t :
  all2 s t = (size s == size t) && all [pred xy | r xy.1 xy.2] (zip s t).
Proof. by elim: s t => [|x s IHs] [|y t] //=; rewrite IHs andbCA. Qed.

Lemma zip_map I f g (s : seq I) :
  zip (map f s) (map g s) = [seq (f i, g i) | i <- s].
Proof. by elim: s => //= i s ->. Qed.

End Zip.

Prenex Implicits zip unzip1 unzip2 all2.

Lemma eqseq_all (T : eqType) (s t : seq T) : (s == t) = all2 eq_op s t.
Proof. by elim: s t => [|x s +] [|y t]//= => <-. Qed.

Lemma eq_map_all I (T : eqType) (f g : I -> T) (s : seq I) :
  (map f s == map g s) = all [pred xy | xy.1 == xy.2] [seq (f i, g i) | i <- s].
Proof. by rewrite eqseq_all all2E !size_map eqxx zip_map. Qed.

Section Flatten.

Variable T : Type.
Implicit Types (s : seq T) (ss : seq (seq T)).

Definition flatten := foldr cat (Nil T).
Definition shape := map (@size T).
Fixpoint reshape sh s :=
  if sh is n :: sh' then take n s :: reshape sh' (drop n s) else [::].

Definition flatten_index sh r c := sumn (take r sh) + c.
Definition reshape_index sh i := find (pred1 0) (scanl subn i.+1 sh).
Definition reshape_offset sh i := i - sumn (take (reshape_index sh i) sh).

Lemma size_flatten ss : size (flatten ss) = sumn (shape ss).
Proof. by elim: ss => //= s ss <-; rewrite size_cat. Qed.

Lemma flatten_cat ss1 ss2 : flatten (ss1 ++ ss2) = flatten ss1 ++ flatten ss2.
Proof. by elim: ss1 => //= s ss1 ->; rewrite catA. Qed.

Lemma size_reshape sh s : size (reshape sh s) = size sh.
Proof. by elim: sh s => //= s0 sh IHsh s; rewrite IHsh. Qed.

Lemma nth_reshape (sh : seq nat) l n :
  nth [::] (reshape sh l) n = take (nth 0 sh n) (drop (sumn (take n sh)) l).
Proof.
elim: n sh l => [| n IHn] [| sh0 sh] l; rewrite ?take0 ?drop0 //=.
by rewrite addnC -drop_drop; apply: IHn.
Qed.

Lemma flattenK ss : reshape (shape ss) (flatten ss) = ss.
Proof.
by elim: ss => //= s ss IHss; rewrite take_size_cat ?drop_size_cat ?IHss.
Qed.

Lemma reshapeKr sh s : size s <= sumn sh -> flatten (reshape sh s) = s.
Proof.
elim: sh s => [[]|n sh IHsh] //= s sz_s; rewrite IHsh ?cat_take_drop //.
by rewrite size_drop leq_subLR.
Qed.

Lemma reshapeKl sh s : size s >= sumn sh -> shape (reshape sh s) = sh.
Proof.
elim: sh s => [[]|n sh IHsh] //= s sz_s.
rewrite size_takel; last exact: leq_trans (leq_addr _ _) sz_s.
by rewrite IHsh // -(leq_add2l n) size_drop -maxnE leq_max sz_s orbT.
Qed.

Lemma flatten_rcons ss s : flatten (rcons ss s) = flatten ss ++ s.
Proof. by rewrite -cats1 flatten_cat /= cats0. Qed.

Lemma flatten_seq1 s : flatten [seq [:: x] | x <- s] = s.
Proof. by elim: s => //= s0 s ->. Qed.

Lemma count_flatten ss P :
  count P (flatten ss) = sumn [seq count P x | x <- ss].
Proof. by elim: ss => //= s ss IHss; rewrite count_cat IHss. Qed.

Lemma filter_flatten ss (P : pred T) :
  filter P (flatten ss) = flatten [seq filter P i | i <- ss].
Proof. by elim: ss => // s ss /= <-; apply: filter_cat. Qed.

Lemma rev_flatten ss :
  rev (flatten ss) = flatten (rev (map rev ss)).
Proof.
by elim: ss => //= s ss IHss; rewrite rev_cons flatten_rcons -IHss rev_cat.
Qed.

Lemma nth_shape ss i : nth 0 (shape ss) i = size (nth [::] ss i).
Proof.
rewrite /shape; case: (ltnP i (size ss)) => Hi; first exact: nth_map.
by rewrite !nth_default // size_map.
Qed.

Lemma shape_rev ss : shape (rev ss) = rev (shape ss).
Proof. exact: map_rev. Qed.

Lemma eq_from_flatten_shape ss1 ss2 :
  flatten ss1 = flatten ss2 -> shape ss1 = shape ss2 -> ss1 = ss2.
Proof. by move=> Eflat Esh; rewrite -[LHS]flattenK Eflat Esh flattenK. Qed.

Lemma rev_reshape sh s :
  size s = sumn sh -> rev (reshape sh s) = map rev (reshape (rev sh) (rev s)).
Proof.
move=> sz_s; apply/(canLR revK)/eq_from_flatten_shape.
  rewrite reshapeKr ?sz_s // -rev_flatten reshapeKr ?revK //.
  by rewrite size_rev sumn_rev sz_s.
transitivity (rev (shape (reshape (rev sh) (rev s)))).
  by rewrite !reshapeKl ?revK ?size_rev ?sz_s ?sumn_rev.
rewrite shape_rev; congr (rev _); rewrite -[RHS]map_comp.
by under eq_map do rewrite /= size_rev.
Qed.

Lemma reshape_rcons s sh n (m := sumn sh) :
  m + n = size s ->
  reshape (rcons sh n) s = rcons (reshape sh (take m s)) (drop m s).
Proof.
move=> Dmn; apply/(can_inj revK); rewrite rev_reshape ?rev_rcons ?sumn_rcons //.
rewrite /= take_rev drop_rev -Dmn addnK revK -rev_reshape //.
by rewrite size_takel // -Dmn leq_addr.
Qed.

Lemma flatten_indexP sh r c :
  c < nth 0 sh r -> flatten_index sh r c < sumn sh.
Proof.
move=> lt_c_sh; rewrite -[sh in sumn sh](cat_take_drop r) sumn_cat ltn_add2l.
suffices lt_r_sh: r < size sh by rewrite (drop_nth 0 lt_r_sh) ltn_addr.
by case: ltnP => // le_sh_r; rewrite nth_default in lt_c_sh.
Qed.

Lemma reshape_indexP sh i : i < sumn sh -> reshape_index sh i < size sh.
Proof.
rewrite /reshape_index; elim: sh => //= n sh IHsh in i *; rewrite subn_eq0.
by have [// | le_n_i] := ltnP i n; rewrite -leq_subLR subSn // => /IHsh.
Qed.

Lemma reshape_offsetP sh i :
  i < sumn sh -> reshape_offset sh i < nth 0 sh (reshape_index sh i).
Proof.
rewrite /reshape_offset /reshape_index; elim: sh => //= n sh IHsh in i *.
rewrite subn_eq0; have [| le_n_i] := ltnP i n; first by rewrite subn0.
by rewrite -leq_subLR /= subnDA subSn // => /IHsh.
Qed.

Lemma reshape_indexK sh i :
  flatten_index sh (reshape_index sh i) (reshape_offset sh i) = i.
Proof.
rewrite /reshape_offset /reshape_index /flatten_index -subSKn.
elim: sh => //= n sh IHsh in i *; rewrite subn_eq0; have [//|le_n_i] := ltnP.
by rewrite /= subnDA subSn // -addnA IHsh subnKC.
Qed.

Lemma flatten_indexKl sh r c :
  c < nth 0 sh r -> reshape_index sh (flatten_index sh r c) = r.
Proof.
rewrite /reshape_index /flatten_index.
elim: sh r => [|n sh IHsh] [|r] //= lt_c_sh; first by rewrite ifT.
by rewrite -addnA -addnS addKn IHsh.
Qed.

Lemma flatten_indexKr sh r c :
  c < nth 0 sh r -> reshape_offset sh (flatten_index sh r c) = c.
Proof.
rewrite /reshape_offset /reshape_index /flatten_index.
elim: sh r => [|n sh IHsh] [|r] //= lt_c_sh; first by rewrite ifT ?subn0.
by rewrite -addnA -addnS addKn /= subnDl IHsh.
Qed.

Lemma nth_flatten x0 ss i (r := reshape_index (shape ss) i) :
  nth x0 (flatten ss) i = nth x0 (nth [::] ss r) (reshape_offset (shape ss) i).
Proof.
rewrite /reshape_offset -subSKn {}/r /reshape_index.
elim: ss => //= s ss IHss in i *; rewrite subn_eq0 nth_cat.
by have [//|le_s_i] := ltnP; rewrite subnDA subSn /=.
Qed.

Lemma reshape_leq sh i1 i2
  (r1 := reshape_index sh i1) (c1 := reshape_offset sh i1)
  (r2 := reshape_index sh i2) (c2 := reshape_offset sh i2) :
  (i1 <= i2) = ((r1 < r2) || ((r1 == r2) && (c1 <= c2))).
Proof.
rewrite {}/r1 {}/c1 {}/r2 {}/c2 /reshape_offset /reshape_index.
elim: sh => [|s0 s IHs] /= in i1 i2 *; rewrite ?subn0 ?subn_eq0 //.
have [[] i1s0 [] i2s0] := (ltnP i1 s0, ltnP i2 s0); first by rewrite !subn0.
- by apply: leq_trans i2s0; apply/ltnW.
- by apply/negP => /(leq_trans i1s0); rewrite leqNgt i2s0.
by rewrite !subSn // !eqSS !ltnS !subnDA -IHs leq_subLR subnKC.
Qed.

End Flatten.

Prenex Implicits flatten shape reshape.

Lemma map_flatten S T (f : T -> S) ss :
  map f (flatten ss) = flatten (map (map f) ss).
Proof. by elim: ss => // s ss /= <-; apply: map_cat. Qed.

Lemma flatten_map1 (S T : Type) (f : S -> T) s :
  flatten [seq [:: f x] | x <- s] = map f s.
Proof. by elim: s => //= s0 s ->. Qed.

Lemma undup_flatten_nseq n (T : eqType) (s : seq T) : 0 < n ->
  undup (flatten (nseq n s)) = undup s.
Proof.
elim: n => [|[|n]/= IHn]//= _; rewrite ?cats0// undup_cat {}IHn//.
rewrite (@eq_in_filter _ _ pred0) ?filter_pred0// => x.
by rewrite mem_undup mem_cat => ->.
Qed.

Lemma sumn_flatten (ss : seq (seq nat)) :
  sumn (flatten ss) = sumn (map sumn ss).
Proof. by elim: ss => // s ss /= <-; apply: sumn_cat. Qed.

Lemma map_reshape T S (f : T -> S) sh s :
  map (map f) (reshape sh s) = reshape sh (map f s).
Proof. by elim: sh s => //= sh0 sh IHsh s; rewrite map_take IHsh map_drop. Qed.

Section EqFlatten.

Variables S T : eqType.

Lemma flattenP (A : seq (seq T)) x :
  reflect (exists2 s, s \in A & x \in s) (x \in flatten A).
Proof.
elim: A => /= [|s A IH_A]; [by right; case | rewrite mem_cat].
by apply: equivP (iff_sym exists_cons); apply: (orPP idP IH_A).
Qed.
Arguments flattenP {A x}.

Lemma flatten_mapP (A : S -> seq T) s y :
  reflect (exists2 x, x \in s & y \in A x) (y \in flatten (map A s)).
Proof.
apply: (iffP flattenP) => [[_ /mapP[x sx ->]] | [x sx]] Axy; first by exists x.
by exists (A x); rewrite ?map_f.
Qed.

Lemma perm_flatten (ss1 ss2 : seq (seq T)) :
  perm_eq ss1 ss2 -> perm_eq (flatten ss1) (flatten ss2).
Proof.
move=> eq_ss; apply/permP=> a; apply/catCA_perm_subst: ss1 ss2 eq_ss.
by move=> ss1 ss2 ss3; rewrite !flatten_cat !count_cat addnCA.
Qed.

End EqFlatten.

Arguments flattenP {T A x}.
Arguments flatten_mapP {S T A s y}.

Notation "[ 'seq' E | x <- s , y <- t ]" :=
  (flatten [seq [seq E | y <- t] | x <- s])
  (at level 0, E at level 99, x name, y name,
   format "[ '[hv' 'seq'  E '/ '  |  x  <-  s , '/   '  y  <-  t ] ']'")
   : seq_scope.
Notation "[ 'seq' E | x : S <- s , y : T <- t ]" :=
  (flatten [seq [seq E | y : T <- t] | x : S  <- s])
  (at level 0, E at level 99, x name, y name, only parsing) : seq_scope.
Notation "[ 'seq' E : R | x : S <- s , y : T <- t ]" :=
  (flatten [seq [seq E : R | y : T <- t] | x : S  <- s])
  (at level 0, E at level 99, x name, y name, only parsing) : seq_scope.
Notation "[ 'seq' E : R | x <- s , y <- t ]" :=
  (flatten [seq [seq E : R | y <- t] | x  <- s])
  (at level 0, E at level 99, x name, y name, only parsing) : seq_scope.

Section PrefixSuffixInfix.

Variables T : eqType.
Implicit Type s : seq T.

Fixpoint prefix s1 s2 {struct s2} :=
  if s1 isn't x :: s1' then true else
  if s2 isn't y :: s2' then false else
    (x == y) && prefix s1' s2'.

Lemma prefixE s1 s2 : prefix s1 s2 = (take (size s1) s2 == s1).
Proof. by elim: s2 s1 => [|y s2 +] [|x s1]//= => ->; rewrite eq_sym. Qed.

Lemma prefix_refl s : prefix s s. Proof. by rewrite prefixE take_size. Qed.

Lemma prefixs0 s : prefix s [::] = (s == [::]). Proof. by case: s. Qed.

Lemma prefix0s s : prefix [::] s. Proof. by case: s. Qed.

Lemma prefix_cons s1 s2 x y :
  prefix (x :: s1) (y :: s2) = (x == y) && prefix s1 s2.
Proof. by []. Qed.

Lemma prefix_catr s1 s2 s1' s3 : size s1 = size s1' ->
  prefix (s1 ++ s2) (s1' ++ s3) = (s1 == s1') && prefix s2 s3.
Proof.
elim: s1 s1' => [|x s1 IHs1] [|y s1']//= [eqs1].
by rewrite IHs1// eqseq_cons andbA.
Qed.

Lemma prefix_prefix s1 s2 : prefix s1 (s1 ++ s2).
Proof. by rewrite prefixE take_cat ltnn subnn take0 cats0. Qed.
Hint Resolve prefix_prefix : core.

Lemma prefixP {s1 s2} :
  reflect (exists s2' : seq T, s2 = s1 ++ s2') (prefix s1 s2).
Proof.
apply: (iffP idP) => [|[{}s2 ->]]; last exact: prefix_prefix.
by rewrite prefixE => /eqP<-; exists (drop (size s1) s2); rewrite cat_take_drop.
Qed.

Lemma prefix_trans : transitive prefix.
Proof. by move=> _ s2 _ /prefixP[s1 ->] /prefixP[s3 ->]; rewrite -catA. Qed.

Lemma prefixs1 s x : prefix s [:: x] = (s == [::]) || (s == [:: x]).
Proof. by case: s => //= y s; rewrite prefixs0 eqseq_cons. Qed.

Lemma catl_prefix s1 s2 s3 : prefix (s1 ++ s3) s2 -> prefix s1 s2.
Proof. by move=> /prefixP [s2'] ->; rewrite -catA. Qed.

Lemma prefix_catl s1 s2 s3 : prefix s1 s2 -> prefix s1 (s2 ++ s3).
Proof. by move=> /prefixP [s2'] ->; rewrite -catA. Qed.

Lemma prefix_rcons s x : prefix s (rcons s x).
Proof. by rewrite -cats1 prefix_prefix. Qed.

Definition suffix s1 s2 := prefix (rev s1) (rev s2).

Lemma suffixE s1 s2 : suffix s1 s2 = (drop (size s2 - size s1) s2 == s1).
Proof. by rewrite /suffix prefixE take_rev (can_eq revK) size_rev. Qed.

Lemma suffix_refl s : suffix s s.
Proof. exact: prefix_refl. Qed.

Lemma suffixs0 s : suffix s [::] = (s == [::]).
Proof. by rewrite /suffix prefixs0 -!nilpE rev_nilp. Qed.

Lemma suffix0s s : suffix [::] s.
Proof. exact: prefix0s. Qed.

Lemma prefix_rev s1 s2 : prefix (rev s1) (rev s2) = suffix s1 s2.
Proof. by []. Qed.

Lemma prefix_revLR s1 s2 : prefix (rev s1) s2 = suffix s1 (rev s2).
Proof. by rewrite -prefix_rev revK. Qed.

Lemma suffix_rev s1 s2 : suffix (rev s1) (rev s2) = prefix s1 s2.
Proof. by rewrite -prefix_rev !revK. Qed.

Lemma suffix_revLR s1 s2 : suffix (rev s1) s2 = prefix s1 (rev s2).
Proof. by rewrite -prefix_rev revK. Qed.

Lemma suffix_suffix s1 s2 : suffix s2 (s1 ++ s2).
Proof. by rewrite /suffix rev_cat prefix_prefix. Qed.
Hint Resolve suffix_suffix : core.

Lemma suffixP {s1 s2} :
  reflect (exists s2' : seq T, s2 = s2' ++ s1) (suffix s1 s2).
Proof.
apply: (iffP prefixP) => [[s2' rev_s2]|[s2' ->]]; exists (rev s2'); last first.
  by rewrite rev_cat.
by rewrite -[s2]revK rev_s2 rev_cat revK.
Qed.

Lemma suffix_trans : transitive suffix.
Proof. by move=> _ s2 _ /suffixP[s1 ->] /suffixP[s3 ->]; rewrite catA. Qed.

Lemma suffix_rcons s1 s2 x y :
  suffix (rcons s1 x) (rcons s2 y) = (x == y) && suffix s1 s2.
Proof. by rewrite /suffix 2!rev_rcons prefix_cons. Qed.

Lemma suffix_catl s1 s2 s3 s3' : size s3 = size s3' ->
  suffix (s1 ++ s3) (s2 ++ s3') = (s3 == s3') && suffix s1 s2.
Proof.
by move=> eqs3; rewrite /suffix !rev_cat prefix_catr ?size_rev// (can_eq revK).
Qed.

Lemma suffix_catr s1 s2 s3 : suffix s1 s2 -> suffix s1 (s3 ++ s2).
Proof. by move=> /suffixP [s2'] ->; rewrite catA suffix_suffix. Qed.

Lemma catl_suffix s s1 s2 : suffix (s ++ s1) s2 -> suffix s1 s2.
Proof. by move=> /suffixP [s2'] ->; rewrite catA suffix_suffix. Qed.

Lemma suffix_cons s x : suffix s (x :: s).
Proof. by rewrite /suffix rev_cons prefix_rcons. Qed.

Fixpoint infix s1 s2 :=
  if s2 is y :: s2' then prefix s1 s2 || infix s1 s2' else s1 == [::].

Fixpoint infix_index s1 s2 :=
  if prefix s1 s2 then 0
  else if s2 is y :: s2' then (infix_index s1 s2').+1 else 1.

Lemma infix0s s : infix [::] s. Proof. by case: s. Qed.

Lemma infixs0 s : infix s [::] = (s == [::]). Proof. by case: s. Qed.

Lemma infix_consl s1 y s2 :
  infix s1 (y :: s2) = prefix s1 (y :: s2) || infix s1 s2.
Proof. by []. Qed.

Lemma infix_indexss s : infix_index s s = 0.
Proof. by case: s => //= x s; rewrite eqxx prefix_refl. Qed.

Lemma infix_index_le s1 s2 : infix_index s1 s2 <= (size s2).+1.
Proof. by elim: s2 => [|x s2'] /=; case: ifP. Qed.

Lemma infixTindex s1 s2 : (infix_index s1 s2 <= size s2) = infix s1 s2.
Proof. by elim: s2 s1 => [|y s2 +] [|x s1]//= => <-; case: ifP. Qed.

Lemma infixPn s1 s2 :
  reflect (infix_index s1 s2 = (size s2).+1) (~~ infix s1 s2).
Proof.
rewrite -infixTindex -ltnNge; apply: (iffP idP) => [s2lt|->//].
by apply/eqP; rewrite eqn_leq s2lt infix_index_le.
Qed.

Lemma infix_index0s s : infix_index [::] s = 0.
Proof. by case: s. Qed.

Lemma infix_indexs0 s : infix_index s [::] = (s != [::]).
Proof. by case: s. Qed.

Lemma infixE s1 s2 : infix s1 s2 =
   (take (size s1) (drop (infix_index s1 s2) s2) == s1).
Proof.
elim: s2 s1 => [|y s2 +] [|x s1]//= => -> /=.
by case: ifP => // /andP[/eqP-> ps1s2/=]; rewrite eqseq_cons -prefixE eqxx.
Qed.

Lemma infix_refl s : infix s s.
Proof. by rewrite infixE infix_indexss// drop0 take_size. Qed.

Lemma prefixW s1 s2 : prefix s1 s2 -> infix s1 s2.
Proof. by elim: s2 s1 => [|y s2 IHs2] [|x s1]//=->. Qed.

Lemma prefix_infix s1 s2 : infix s1 (s1 ++ s2).
Proof. exact: prefixW. Qed.
Hint Resolve prefix_infix : core.

Lemma infix_infix s1 s2 s3 : infix s2 (s1 ++ s2 ++ s3).
Proof. by elim: s1 => //= x s1 ->; rewrite orbT. Qed.
Hint Resolve infix_infix : core.

Lemma suffix_infix s1 s2 : infix s2 (s1 ++ s2).
Proof. by rewrite -[X in s1 ++ X]cats0. Qed.
Hint Resolve suffix_infix : core.

Lemma infixP {s1 s2} :
  reflect (exists s s' : seq T, s2 = s ++ s1 ++ s') (infix s1 s2).
Proof.
apply: (iffP idP) => [|[p [s {s2}->]]]//=; rewrite infixE => /eqP<-.
set k := infix_index _ _; exists (take k s2), (drop (size s1 + k) s2).
by rewrite -drop_drop !cat_take_drop.
Qed.

Lemma infix_rev s1 s2 : infix (rev s1) (rev s2) = infix s1 s2.
Proof.
gen have sr : s1 s2 / infix s1 s2 -> infix (rev s1) (rev s2); last first.
  by apply/idP/idP => /sr; rewrite ?revK.
by move=> /infixP[s [p ->]]; rewrite !rev_cat -catA.
Qed.

Lemma suffixW s1 s2 : suffix s1 s2 -> infix s1 s2.
Proof. by rewrite -infix_rev; apply: prefixW. Qed.

Lemma infix_trans : transitive infix.
Proof.
move=> s s1 s2 /infixP[s1p [s1s def_s]] /infixP[sp [ss def_s2]].
by apply/infixP; exists (sp ++ s1p),(s1s ++ ss); rewrite def_s2 def_s -!catA.
Qed.

Lemma infix_revLR s1 s2 : infix (rev s1) s2 = infix s1 (rev s2).
Proof. by rewrite -infix_rev revK. Qed.

Lemma infix_rconsl s1 s2 y :
  infix s1 (rcons s2 y) = suffix s1 (rcons s2 y) || infix s1 s2.
Proof.
rewrite -infix_rev rev_rcons infix_consl.
by rewrite -rev_rcons prefix_rev infix_rev.
Qed.

Lemma infix_cons s x : infix s (x :: s).
Proof. by rewrite -cat1s suffix_infix. Qed.

Lemma infixs1 s x : infix s [:: x] = (s == [::]) || (s == [:: x]).
Proof. by rewrite infix_consl prefixs1 orbC orbA orbb. Qed.

Lemma catl_infix s s1 s2 : infix (s ++ s1) s2 -> infix s1 s2.
Proof. apply: infix_trans; exact/suffixW/suffix_suffix. Qed.

Lemma catr_infix s s1 s2 : infix (s1 ++ s) s2 -> infix s1 s2.
Proof.
by rewrite -infix_rev rev_cat => /catl_infix; rewrite infix_rev.
Qed.

Lemma cons2_infix s1 s2 x : infix (x :: s1) (x :: s2) -> infix s1 s2.
Proof.
by rewrite /= eqxx /= -cat1s => /orP[/prefixW//|]; exact: catl_infix.
Qed.

Lemma rcons2_infix s1 s2 x : infix (rcons s1 x) (rcons s2 x) -> infix s1 s2.
Proof. by rewrite -infix_rev !rev_rcons => /cons2_infix; rewrite infix_rev. Qed.

Lemma catr2_infix s s1 s2 : infix (s ++ s1) (s ++ s2) -> infix s1 s2.
Proof. by elim: s => //= x s IHs /cons2_infix. Qed.

Lemma catl2_infix s s1 s2 : infix (s1 ++ s) (s2 ++ s) -> infix s1 s2.
Proof. by rewrite -infix_rev !rev_cat => /catr2_infix; rewrite infix_rev. Qed.

Lemma infix_catl s1 s2 s3 : infix s1 s2 -> infix s1 (s3 ++ s2).
Proof. by move=> is12; apply: infix_trans is12 (suffix_infix _ _). Qed.

Lemma infix_catr s1 s2 s3 : infix s1 s2 -> infix s1 (s2 ++ s3).
Proof.
case: s3 => [|x s /infixP [p [sf]] ->]; first by rewrite cats0.
by rewrite -catA; apply: infix_catl; rewrite -catA prefix_infix.
Qed.

Lemma prefix_infix_trans s2 s1 s3 :
  prefix s1 s2 -> infix s2 s3 -> infix s1 s3.
Proof. by move=> /prefixW/infix_trans; apply. Qed.

Lemma suffix_infix_trans s2 s1 s3 :
  suffix s1 s2 -> infix s2 s3 -> infix s1 s3.
Proof. by move=> /suffixW/infix_trans; apply. Qed.

Lemma infix_prefix_trans s2 s1 s3 :
  infix s1 s2 -> prefix s2 s3 -> infix s1 s3.
Proof. by move=> + /prefixW; apply: infix_trans. Qed.

Lemma infix_suffix_trans s2 s1 s3 :
  infix s1 s2 -> suffix s2 s3 -> infix s1 s3.
Proof. by move=> + /suffixW; apply: infix_trans. Qed.

Lemma prefix_suffix_trans s2 s1 s3 :
  prefix s1 s2 -> suffix s2 s3 -> infix s1 s3.
Proof. by move=> /prefixW + /suffixW +; apply: infix_trans. Qed.

Lemma suffix_prefix_trans s2 s1 s3 :
  suffix s1 s2 -> prefix s2 s3 -> infix s1 s3.
Proof. by move=> /suffixW + /prefixW +; apply: infix_trans. Qed.

Lemma infixW s1 s2 : infix s1 s2 -> subseq s1 s2.
Proof.
move=> /infixP[sp [ss ->]].
exact: subseq_trans (prefix_subseq _ _) (suffix_subseq _ _).
Qed.

Lemma mem_infix s1 s2 : infix s1 s2 -> {subset s1 <= s2}.
Proof. by move=> /infixW subH; apply: mem_subseq. Qed.

Lemma infix1s s x : infix [:: x] s = (x \in s).
Proof. by elim: s => // x' s /= ->; rewrite in_cons prefix0s andbT. Qed.

Lemma prefix1s s x : prefix [:: x] s -> x \in s.
Proof. by rewrite -infix1s => /prefixW. Qed.

Lemma suffix1s s x : suffix [:: x] s -> x \in s.
Proof. by rewrite -infix1s => /suffixW. Qed.

Lemma infix_rcons s x : infix s (rcons s x).
Proof. by rewrite -cats1 prefix_infix. Qed.

Lemma infix_uniq s1 s2 : infix s1 s2 -> uniq s2 -> uniq s1.
Proof. by move=> /infixW /subseq_uniq subH. Qed.

Lemma prefix_uniq s1 s2 : prefix s1 s2 -> uniq s2 -> uniq s1.
Proof. by move=> /prefixW /infix_uniq preH. Qed.

Lemma suffix_uniq s1 s2 : suffix s1 s2 -> uniq s2 -> uniq s1.
Proof. by move=> /suffixW /infix_uniq preH. Qed.

Lemma prefix_take s i : prefix (take i s) s.
Proof. by rewrite -{2}[s](cat_take_drop i). Qed.

Lemma suffix_drop s i : suffix (drop i s) s.
Proof. by rewrite -{2}[s](cat_take_drop i). Qed.

Lemma infix_take s i : infix (take i s) s.
Proof. by rewrite prefixW // prefix_take. Qed.

Lemma prefix_drop_gt0 s i : ~~ prefix (drop i s) s -> i > 0.
Proof. by case: i => //=; rewrite drop0 ltnn prefix_refl. Qed.

Lemma infix_drop s i : infix (drop i s) s.
Proof. by rewrite -{2}[s](cat_take_drop i). Qed.

Lemma consr_infix s1 s2 x : infix (x :: s1) s2 -> infix [:: x] s2.
Proof. by rewrite -cat1s => /catr_infix. Qed.

Lemma consl_infix s1 s2 x : infix (x :: s1) s2 -> infix s1 s2.
Proof. by rewrite -cat1s => /catl_infix. Qed.

Lemma prefix_index s1 s2 : prefix s1 s2 -> infix_index s1 s2 = 0.
Proof. by case: s1 s2 => [|x s1] [|y s2] //= ->. Qed.

Lemma size_infix s1 s2 : infix s1 s2 -> size s1 <= size s2.
Proof. by move=> /infixW; apply: size_subseq. Qed.

Lemma size_prefix s1 s2 : prefix s1 s2 -> size s1 <= size s2.
Proof. by move=> /prefixW; apply: size_infix. Qed.

Lemma size_suffix s1 s2 : suffix s1 s2 -> size s1 <= size s2.
Proof. by move=> /suffixW; apply: size_infix. Qed.

End PrefixSuffixInfix.

Section AllPairsDep.

Variables (S S' : Type) (T T' : S -> Type) (R : Type).
Implicit Type f : forall x, T x -> R.

Definition allpairs_dep f s t := [seq f x y | x <- s, y <- t x].

Lemma size_allpairs_dep f s t :
  size [seq f x y | x <- s, y <- t x] = sumn [seq size (t x) | x <- s].
Proof. by elim: s => //= x s IHs; rewrite size_cat size_map IHs. Qed.

Lemma allpairs0l f t : [seq f x y | x <- [::], y <- t x] = [::].
Proof. by []. Qed.

Lemma allpairs0r f s : [seq f x y | x <- s, y <- [::]] = [::].
Proof. by elim: s. Qed.

Lemma allpairs1l f x t :
   [seq f x y | x <- [:: x], y <- t x] = [seq f x y | y <- t x].
Proof. exact: cats0. Qed.

Lemma allpairs1r f s y :
  [seq f x y | x <- s, y <- [:: y x]] = [seq f x (y x) | x <- s].
Proof. exact: flatten_map1. Qed.

Lemma allpairs_cons f x s t :
  [seq f x y | x <- x :: s, y <- t x] =
    [seq f x y | y <- t x] ++ [seq f x y | x <- s, y <- t x].
Proof. by []. Qed.

Lemma eq_allpairs (f1 f2 : forall x, T x -> R) s t :
    (forall x, f1 x =1 f2 x) ->
  [seq f1 x y | x <- s, y <- t x] = [seq f2 x y | x <- s, y <- t x].
Proof. by move=> eq_f; under eq_map do under eq_map do rewrite eq_f. Qed.

Lemma eq_allpairsr (f : forall x, T x -> R) s t1 t2 : (forall x, t1 x = t2 x) ->
  [seq f x y | x <- s, y <- t1 x] = [seq f x y | x <- s, y <- t2 x].
Proof. by move=> eq_t; under eq_map do rewrite eq_t. Qed.

Lemma allpairs_cat f s1 s2 t :
  [seq f x y | x <- s1 ++ s2, y <- t x] =
    [seq f x y | x <- s1, y <- t x] ++ [seq f x y | x <- s2, y <- t x].
Proof. by rewrite map_cat flatten_cat. Qed.

Lemma allpairs_rcons f x s t :
  [seq f x y | x <- rcons s x, y <- t x] =
    [seq f x y | x <- s, y <- t x] ++ [seq f x y | y <- t x].
Proof. by rewrite -cats1 allpairs_cat allpairs1l. Qed.

Lemma allpairs_mapl f (g : S' -> S) s t :
  [seq f x y | x <- map g s, y <- t x] = [seq f (g x) y | x <- s, y <- t (g x)].
Proof. by rewrite -map_comp. Qed.

Lemma allpairs_mapr f (g : forall x, T' x -> T x) s t :
  [seq f x y | x <- s, y <- map (g x) (t x)] =
    [seq f x (g x y) | x <- s, y <- t x].
Proof. by under eq_map do rewrite -map_comp. Qed.

End AllPairsDep.

Arguments allpairs_dep {S T R} f s t /.

Lemma map_allpairs S T R R' (g : R' -> R) f s t :
  map g [seq f x y | x : S <- s, y : T x <- t x] =
    [seq g (f x y) | x <- s, y <- t x].
Proof. by rewrite map_flatten allpairs_mapl allpairs_mapr. Qed.

Section AllPairsNonDep.

Variables (S T R : Type) (f : S -> T -> R).
Implicit Types (s : seq S) (t : seq T).

Definition allpairs s t := [seq f x y | x <- s, y <- t].

Lemma size_allpairs s t : size [seq f x y | x <- s, y <- t] = size s * size t.
Proof. by elim: s => //= x s IHs; rewrite size_cat size_map IHs. Qed.

End AllPairsNonDep.

Arguments allpairs {S T R} f s t /.

Section EqAllPairsDep.

Variables (S : eqType) (T : S -> eqType).
Implicit Types (R : eqType) (s : seq S) (t : forall x, seq (T x)).

Lemma allpairsPdep R (f : forall x, T x -> R) s t (z : R) :
  reflect (exists x y, [/\ x \in s, y \in t x & z = f x y])
          (z \in [seq f x y | x <- s, y <- t x]).
Proof.
apply: (iffP flatten_mapP); first by case=> x sx /mapP[y ty ->]; exists x, y.
by case=> x [y [sx ty ->]]; exists x; last apply: map_f.
Qed.

Variable R : eqType.
Implicit Type f : forall x, T x -> R.

Lemma allpairs_f_dep f s t x y :
  x \in s -> y \in t x -> f x y \in [seq f x y | x <- s, y <- t x].
Proof. by move=> sx ty; apply/allpairsPdep; exists x, y. Qed.

Lemma eq_in_allpairs_dep f1 f2 s t :
    {in s, forall x, {in t x, f1 x =1 f2 x}} <->
  [seq f1 x y : R | x <- s, y <- t x] = [seq f2 x y | x <- s, y <- t x].
Proof.
split=> [eq_f | eq_fst x s_x].
  by congr flatten; apply/eq_in_map=> x s_x; apply/eq_in_map/eq_f.
apply/eq_in_map; apply/eq_in_map: x s_x; apply/eq_from_flatten_shape => //.
by rewrite /shape -!map_comp; apply/eq_map=> x /=; rewrite !size_map.
Qed.

Lemma perm_allpairs_dep f s1 t1 s2 t2 :
    perm_eq s1 s2 -> {in s1, forall x, perm_eq (t1 x) (t2 x)} ->
  perm_eq [seq f x y | x <- s1, y <- t1 x] [seq f x y | x <- s2, y <- t2 x].
Proof.
elim: s1 s2 t1 t2 => [s2 t1 t2 |a s1 IH s2 t1 t2 perm_s2 perm_t1].
  by rewrite perm_sym => /perm_nilP->.
have mem_a : a \in s2 by rewrite -(perm_mem perm_s2) inE eqxx.
rewrite -[s2](cat_take_drop (index a s2)).
rewrite allpairs_cat (drop_nth a) ?index_mem //= nth_index //=.
rewrite perm_sym perm_catC -catA perm_cat //; last first.
  rewrite perm_catC -allpairs_cat.
  rewrite -remE perm_sym IH // => [|x xI]; last first.
    by apply: perm_t1; rewrite inE xI orbT.
  by rewrite -(perm_cons a) (perm_trans perm_s2 (perm_to_rem _)).
have /perm_t1 : a \in a :: s1  by rewrite inE eqxx.
rewrite perm_sym; elim: (t2 a) (t1 a) => /= [s4|b s3 IH1 s4 perm_s4].
  by rewrite perm_sym => /perm_nilP->.
have mem_b : b \in s4 by rewrite -(perm_mem perm_s4) inE eqxx.
rewrite -[s4](cat_take_drop (index b s4)).
rewrite map_cat /= (drop_nth b) ?index_mem //= nth_index //=.
rewrite perm_sym perm_catC /= perm_cons // perm_catC -map_cat.
rewrite -remE perm_sym IH1 // -(perm_cons b).
by apply: perm_trans perm_s4 (perm_to_rem _).
Qed.

Lemma mem_allpairs_dep f s1 t1 s2 t2 :
    s1 =i s2 -> {in s1, forall x, t1 x =i t2 x} ->
  [seq f x y | x <- s1, y <- t1 x] =i [seq f x y | x <- s2, y <- t2 x].
Proof.
move=> eq_s eq_t z; apply/allpairsPdep/allpairsPdep=> -[x [y [sx ty ->]]];
by exists x, y; rewrite -eq_s in sx *; rewrite eq_t in ty *.
Qed.

Lemma allpairs_uniq_dep f s t (st := [seq Tagged T y | x <- s, y <- t x]) :
  let g (p : {x : S & T x}) : R := f (tag p) (tagged p) in
    uniq s -> {in s, forall x, uniq (t x)} -> {in st &, injective g} ->
  uniq [seq f x y | x <- s, y <- t x].
Proof.
move=> g Us Ut; rewrite -(map_allpairs g (existT T)) => /map_inj_in_uniq->{f g}.
elim: s Us => //= x s IHs /andP[s'x Us] in st Ut *; rewrite {st}cat_uniq.
rewrite {}IHs {Us}// ?andbT => [|x1 s_s1]; last exact/Ut/mem_behead.
have injT: injective (existT T x) by move=> y z /eqP; rewrite eq_Tagged => /eqP.
rewrite (map_inj_in_uniq (in2W injT)) {injT}Ut ?mem_head // has_sym has_map.
by apply: contra s'x => /hasP[y _ /allpairsPdep[z [_ [? _ /(congr1 tag)/=->]]]].
Qed.

End EqAllPairsDep.

Arguments allpairsPdep {S T R f s t z}.

Section MemAllPairs.

Variables (S : Type) (T : S -> Type) (R : eqType).
Implicit Types (f : forall x, T x -> R) (s : seq S).

Lemma perm_allpairs_catr f s t1 t2 :
  perm_eql [seq f x y | x <- s, y <- t1 x ++ t2 x]
           ([seq f x y | x <- s, y <- t1 x] ++ [seq f x y | x <- s, y <- t2 x]).
Proof.
apply/permPl; rewrite perm_sym; elim: s => //= x s ihs.
by rewrite perm_catACA perm_cat ?map_cat.
Qed.

Lemma mem_allpairs_catr f s y0 t :
  [seq f x y | x <- s, y <- y0 x ++ t x] =i
    [seq f x y | x <- s, y <- y0 x] ++ [seq f x y | x <- s, y <- t x].
Proof. exact/perm_mem/permPl/perm_allpairs_catr. Qed.

Lemma perm_allpairs_consr f s y0 t :
  perm_eql [seq f x y | x <- s, y <- y0 x :: t x]
           ([seq f x (y0 x) | x <- s] ++ [seq f x y | x <- s, y <- t x]).
Proof.
by apply/permPl; rewrite (perm_allpairs_catr _ _ (fun=> [:: _])) allpairs1r.
Qed.

Lemma mem_allpairs_consr f s t y0 :
  [seq f x y | x <- s, y <- y0 x :: t x] =i
  [seq f x (y0 x) | x <- s] ++ [seq f x y | x <- s, y <- t x].
Proof. exact/perm_mem/permPl/perm_allpairs_consr. Qed.

Lemma allpairs_rconsr f s y0 t :
  perm_eql [seq f x y | x <- s, y <- rcons (t x) (y0 x)]
           ([seq f x y | x <- s, y <- t x] ++ [seq f x (y0 x) | x <- s]).
Proof.
apply/permPl; rewrite -(eq_allpairsr _ _ (fun=> cats1 _ _)).
by rewrite perm_allpairs_catr allpairs1r.
Qed.

Lemma mem_allpairs_rconsr f s t y0 :
  [seq f x y | x <- s, y <- rcons (t x) (y0 x)] =i
    ([seq f x y | x <- s, y <- t x] ++ [seq f x (y0 x) | x <- s]).
Proof. exact/perm_mem/permPl/allpairs_rconsr. Qed.

End MemAllPairs.

Lemma all_allpairsP
      (S : eqType) (T : S -> eqType) (R : Type)
      (p : pred R) (f : forall x : S, T x -> R)
      (s : seq S) (t : forall x : S, seq (T x)) :
  reflect (forall (x : S) (y : T x), x \in s -> y \in t x -> p (f x y))
          (all p [seq f x y | x <- s, y <- t x]).
Proof.
elim: s => [|x s IHs]; first by constructor.
rewrite /= all_cat all_map /preim.
apply/(iffP andP)=> [[/allP /= ? ? x' y x'_in_xs]|p_xs_t].
  by move: x'_in_xs y => /[1!inE] /predU1P [-> //|? ?]; exact: IHs.
split; first by apply/allP => ?; exact/p_xs_t/mem_head.
by apply/IHs => x' y x'_in_s; apply: p_xs_t; rewrite inE x'_in_s orbT.
Qed.

Arguments all_allpairsP {S T R p f s t}.

Section EqAllPairs.

Variables S T R : eqType.
Implicit Types (f : S -> T -> R) (s : seq S) (t : seq T).

Lemma allpairsP f s t (z : R) :
  reflect (exists p, [/\ p.1 \in s, p.2 \in t & z = f p.1 p.2])
          (z \in [seq f x y | x <- s, y <- t]).
Proof.
by apply: (iffP allpairsPdep) => [[x[y]]|[[x y]]]; [exists (x, y)|exists x, y].
Qed.

Lemma allpairs_f f s t x y :
  x \in s -> y \in t -> f x y \in [seq f x y | x <- s, y <- t].
Proof. exact: allpairs_f_dep. Qed.

Lemma eq_in_allpairs f1 f2 s t :
    {in s & t, f1 =2 f2} <->
  [seq f1 x y : R | x <- s, y <- t] = [seq f2 x y | x <- s, y <- t].
Proof.
split=> [eq_f | /eq_in_allpairs_dep-eq_f x y /eq_f/(_ y)//].
by apply/eq_in_allpairs_dep=> x /eq_f.
Qed.

Lemma perm_allpairs f s1 t1 s2 t2 :
    perm_eq s1 s2 -> perm_eq t1 t2 ->
  perm_eq [seq f x y | x <- s1, y <- t1] [seq f x y | x <- s2, y <- t2].
Proof. by move=> perm_s perm_t; apply: perm_allpairs_dep. Qed.

Lemma mem_allpairs f s1 t1 s2 t2 :
    s1 =i s2 -> t1 =i t2 ->
  [seq f x y | x <- s1, y <- t1] =i [seq f x y | x <- s2, y <- t2].
Proof. by move=> eq_s eq_t; apply: mem_allpairs_dep. Qed.

Lemma allpairs_uniq f s t (st := [seq (x, y) | x <- s, y <- t]) :
    uniq s -> uniq t -> {in st &, injective (uncurry f)} ->
  uniq [seq f x y | x <- s, y <- t].
Proof.
move=> Us Ut inj_f; rewrite -(map_allpairs (uncurry f) (@pair S T)) -/st.
rewrite map_inj_in_uniq // allpairs_uniq_dep {Us Ut st inj_f}//.
by apply: in2W => -[x1 y1] [x2 y2] /= [-> ->].
Qed.

End EqAllPairs.

Arguments allpairsP {S T R f s t z}.
Arguments perm_nilP {T s}.
Arguments perm_consP {T x s t}.

Section AllRel.

Variables (T S : Type) (r : T -> S -> bool).
Implicit Types (x : T) (y : S) (xs : seq T) (ys : seq S).

Definition allrel xs ys := all [pred x | all (r x) ys] xs.

Lemma allrel0l ys : allrel [::] ys. Proof. by []. Qed.

Lemma allrel0r xs : allrel xs [::]. Proof. by elim: xs. Qed.

Lemma allrel_consl x xs ys : allrel (x :: xs) ys = all (r x) ys && allrel xs ys.
Proof. by []. Qed.

Lemma allrel_consr xs y ys :
  allrel xs (y :: ys) = all (r^~ y) xs && allrel xs ys.
Proof. exact: all_predI. Qed.

Lemma allrel_cons2 x y xs ys :
  allrel (x :: xs) (y :: ys) =
  [&& r x y, all (r x) ys, all (r^~ y) xs & allrel xs ys].
Proof. by rewrite /= allrel_consr -andbA. Qed.

Lemma allrel1l x ys : allrel [:: x] ys = all (r x) ys. Proof. exact: andbT. Qed.

Lemma allrel1r xs y : allrel xs [:: y] = all (r^~ y) xs.
Proof. by rewrite allrel_consr allrel0r andbT. Qed.

Lemma allrel_catl xs xs' ys :
  allrel (xs ++ xs') ys = allrel xs ys && allrel xs' ys.
Proof. exact: all_cat. Qed.

Lemma allrel_catr xs ys ys' :
  allrel xs (ys ++ ys') = allrel xs ys && allrel xs ys'.
Proof.
elim: ys => /= [|y ys ihys]; first by rewrite allrel0r.
by rewrite !allrel_consr ihys andbA.
Qed.

Lemma allrel_maskl m xs ys : allrel xs ys -> allrel (mask m xs) ys.
Proof.
by elim: m xs => [|[] m IHm] [|x xs] //= /andP [xys /IHm->]; rewrite ?xys.
Qed.

Lemma allrel_maskr m xs ys : allrel xs ys -> allrel xs (mask m ys).
Proof. by elim: xs => //= x xs IHxs /andP [/all_mask->]. Qed.

Lemma allrel_filterl a xs ys : allrel xs ys -> allrel (filter a xs) ys.
Proof. by rewrite filter_mask; apply: allrel_maskl. Qed.

Lemma allrel_filterr a xs ys : allrel xs ys -> allrel xs (filter a ys).
Proof. by rewrite filter_mask; apply: allrel_maskr. Qed.

Lemma allrel_allpairsE xs ys :
  allrel xs ys = all id [seq r x y | x <- xs, y <- ys].
Proof. by elim: xs => //= x xs ->; rewrite all_cat all_map. Qed.

End AllRel.

Arguments allrel {T S} r xs ys : simpl never.
Arguments allrel0l {T S} r ys.
Arguments allrel0r {T S} r xs.
Arguments allrel_consl {T S} r x xs ys.
Arguments allrel_consr {T S} r xs y ys.
Arguments allrel1l {T S} r x ys.
Arguments allrel1r {T S} r xs y.
Arguments allrel_catl {T S} r xs xs' ys.
Arguments allrel_catr {T S} r xs ys ys'.
Arguments allrel_maskl {T S} r m xs ys.
Arguments allrel_maskr {T S} r m xs ys.
Arguments allrel_filterl {T S} r a xs ys.
Arguments allrel_filterr {T S} r a xs ys.
Arguments allrel_allpairsE {T S} r xs ys.

Notation all2rel r xs := (allrel r xs xs).

Lemma sub_in_allrel
      {T S : Type} (P : {pred T}) (Q : {pred S}) (r r' : T -> S -> bool) :
  {in P & Q, forall x y, r x y -> r' x y} ->
  forall xs ys, all P xs -> all Q ys -> allrel r xs ys -> allrel r' xs ys.
Proof.
move=> rr' + ys; elim=> //= x xs IHxs /andP [Px Pxs] Qys.
rewrite !allrel_consl => /andP [+ {}/IHxs-> //]; rewrite andbT.
by elim: ys Qys => //= y ys IHys /andP [Qy Qys] /andP [/rr'-> // /IHys->].
Qed.

Lemma sub_allrel {T S : Type} (r r' : T -> S -> bool) :
  (forall x y, r x y -> r' x y) ->
  forall xs ys, allrel r xs ys -> allrel r' xs ys.
Proof.
by move=> rr' xs ys; apply/sub_in_allrel/all_predT/all_predT; apply: in2W.
Qed.

Lemma eq_in_allrel {T S : Type} (P : {pred T}) (Q : {pred S}) r r' :
  {in P & Q, r =2 r'} ->
  forall xs ys, all P xs -> all Q ys -> allrel r xs ys = allrel r' xs ys.
Proof.
move=> rr' xs ys Pxs Qys.
by apply/idP/idP; apply/sub_in_allrel/Qys/Pxs => ? ? ? ?; rewrite rr'.
Qed.

Lemma eq_allrel {T S : Type} (r r' : T -> S -> bool) :
  r =2 r' -> allrel r =2 allrel r'.
Proof. by move=> rr' xs ys; apply/eq_in_allrel/all_predT/all_predT. Qed.

Lemma allrelC {T S : Type} (r : T -> S -> bool) xs ys :
  allrel r xs ys = allrel (fun y => r^~ y) ys xs.
Proof. by elim: xs => [|x xs ih]; [elim: ys | rewrite allrel_consr -ih]. Qed.

Lemma allrel_mapl {T T' S : Type} (f : T' -> T) (r : T -> S -> bool) xs ys :
  allrel r (map f xs) ys = allrel (fun x => r (f x)) xs ys.
Proof. exact: all_map. Qed.

Lemma allrel_mapr {T S S' : Type} (f : S' -> S) (r : T -> S -> bool) xs ys :
  allrel r xs (map f ys) = allrel (fun x y => r x (f y)) xs ys.
Proof. by rewrite allrelC allrel_mapl allrelC. Qed.

Lemma allrelP {T S : eqType} {r : T -> S -> bool} {xs ys} :
  reflect {in xs & ys, forall x y, r x y} (allrel r xs ys).
Proof. by rewrite allrel_allpairsE; exact: all_allpairsP. Qed.

Lemma allrelT {T S : Type} (xs : seq T) (ys : seq S) :
  allrel (fun _ _ => true) xs ys = true.
Proof. by elim: xs => //= ? ?; rewrite allrel_consl all_predT. Qed.

Lemma allrel_relI {T S : Type} (r r' : T -> S -> bool) xs ys :
  allrel (fun x y => r x y && r' x y) xs ys = allrel r xs ys && allrel r' xs ys.
Proof. by rewrite -all_predI; apply: eq_all => ?; rewrite /= -all_predI. Qed.

Section All2Rel.

Variable (T : nonPropType) (r : rel T).
Implicit Types (x y z : T) (xs : seq T).
Hypothesis (rsym : symmetric r).

Lemma all2rel1 x : all2rel r [:: x] = r x x.
Proof. by rewrite /allrel /= !andbT. Qed.

Lemma all2rel2 x y : all2rel r [:: x; y] = r x x && r y y && r x y.
Proof. by rewrite /allrel /= rsym; do 3 case: r. Qed.

Lemma all2rel_cons x xs :
  all2rel r (x :: xs) = [&& r x x, all (r x) xs & all2rel r xs].
Proof.
rewrite allrel_cons2; congr andb; rewrite andbA -all_predI; congr andb.
by elim: xs => //= y xs ->; rewrite rsym andbb.
Qed.

End All2Rel.

Section Pairwise.

Variables (T : Type) (r : T -> T -> bool).
Implicit Types (x y : T) (xs ys : seq T).

Fixpoint pairwise xs : bool :=
  if xs is x :: xs then all (r x) xs && pairwise xs else true.

Lemma pairwise_cons x xs : pairwise (x :: xs) = all (r x) xs && pairwise xs.
Proof. by []. Qed.

Lemma pairwise_cat xs ys :
  pairwise (xs ++ ys) = [&& allrel r xs ys, pairwise xs & pairwise ys].
Proof. by elim: xs => //= x xs ->; rewrite all_cat -!andbA; bool_congr. Qed.

Lemma pairwise_rcons xs x :
  pairwise (rcons xs x) = all (r^~ x) xs && pairwise xs.
Proof. by rewrite -cats1 pairwise_cat allrel1r andbT. Qed.

Lemma pairwise2 x y : pairwise [:: x; y] = r x y.
Proof. by rewrite /= !andbT. Qed.

Lemma pairwise_mask m xs : pairwise xs -> pairwise (mask m xs).
Proof.
by elim: m xs => [|[] m IHm] [|x xs] //= /andP [? ?]; rewrite ?IHm // all_mask.
Qed.

Lemma pairwise_filter a xs : pairwise xs -> pairwise (filter a xs).
Proof. by rewrite filter_mask; apply: pairwise_mask. Qed.

Lemma pairwiseP x0 xs :
  reflect {in gtn (size xs) &, {homo nth x0 xs : i j / i < j >-> r i j}}
          (pairwise xs).
Proof.
elim: xs => /= [|x xs IHxs]; first exact: (iffP idP).
apply: (iffP andP) => [[r_x_xs pxs] i j|Hnth]; rewrite -?topredE /= ?ltnS.
  by case: i j => [|i] [|j] //= gti gtj ij; [exact/all_nthP | exact/IHxs].
split; last by apply/IHxs => // i j; apply/(Hnth i.+1 j.+1).
by apply/(all_nthP x0) => i gti; apply/(Hnth 0 i.+1).
Qed.

Lemma pairwise_all2rel :
  reflexive r -> symmetric r -> forall xs, pairwise xs = all2rel r xs.
Proof.
by move=> r_refl r_sym; elim => //= x xs ->; rewrite all2rel_cons // r_refl.
Qed.

End Pairwise.

Arguments pairwise {T} r xs.
Arguments pairwise_cons {T} r x xs.
Arguments pairwise_cat {T} r xs ys.
Arguments pairwise_rcons {T} r xs x.
Arguments pairwise2 {T} r x y.
Arguments pairwise_mask {T r} m {xs}.
Arguments pairwise_filter {T r} a {xs}.
Arguments pairwiseP {T r} x0 {xs}.
Arguments pairwise_all2rel {T r} r_refl r_sym xs.

Lemma sub_in_pairwise {T : Type} (P : {pred T}) (r r' : rel T) :
  {in P &, subrel r r'} ->
  forall xs, all P xs -> pairwise r xs -> pairwise r' xs.
Proof.
move=> rr'; elim=> //= x xs IHxs /andP [Px Pxs] /andP [+ {}/IHxs->] //.
rewrite andbT; elim: xs Pxs => //= x' xs IHxs /andP [? ?] /andP [+ /IHxs->] //.
by rewrite andbT; apply: rr'.
Qed.

Lemma sub_pairwise {T : Type} (r r' : rel T) xs :
  subrel r r' -> pairwise r xs -> pairwise r' xs.
Proof. by move=> rr'; apply/sub_in_pairwise/all_predT; apply: in2W. Qed.

Lemma eq_in_pairwise {T : Type} (P : {pred T}) (r r' : rel T) :
  {in P &, r =2 r'} -> forall xs, all P xs -> pairwise r xs = pairwise r' xs.
Proof.
move=> rr' xs Pxs.
by apply/idP/idP; apply/sub_in_pairwise/Pxs => ? ? ? ?; rewrite rr'.
Qed.

Lemma eq_pairwise {T : Type} (r r' : rel T) :
  r =2 r' -> pairwise r =i pairwise r'.
Proof. by move=> rr' xs; apply/eq_in_pairwise/all_predT. Qed.

Lemma pairwise_map {T T' : Type} (f : T' -> T) (r : rel T) xs :
  pairwise r (map f xs) = pairwise (relpre f r) xs.
Proof. by elim: xs => //= x xs ->; rewrite all_map. Qed.

Lemma pairwise_relI {T : Type} (r r' : rel T) (s : seq T) :
  pairwise [rel x y | r x y && r' x y] s = pairwise r s && pairwise r' s.
Proof. by elim: s => //= x s ->; rewrite andbACA all_predI. Qed.

Section EqPairwise.

Variables (T : eqType) (r : T -> T -> bool).
Implicit Types (xs ys : seq T).

Lemma subseq_pairwise xs ys : subseq xs ys -> pairwise r ys -> pairwise r xs.
Proof. by case/subseqP => m _ ->; apply: pairwise_mask. Qed.

Lemma uniq_pairwise xs : uniq xs = pairwise [rel x y | x != y] xs.
Proof.
elim: xs => //= x xs ->; congr andb; rewrite -has_pred1 -all_predC.
by elim: xs => //= x' xs ->; case: eqVneq.
Qed.

Lemma pairwise_uniq xs : irreflexive r -> pairwise r xs -> uniq xs.
Proof.
move=> r_irr; rewrite uniq_pairwise; apply/sub_pairwise => x y.
by apply: contraTneq => ->; rewrite r_irr.
Qed.

Lemma pairwise_eq : antisymmetric r ->
  forall xs ys, pairwise r xs -> pairwise r ys -> perm_eq xs ys -> xs = ys.
Proof.
move=> r_asym; elim=> [|x xs IHxs] [|y ys] //=; try by move=> ? ? /perm_size.
move=> /andP [r_x_xs pxs] /andP [r_y_ys pys] eq_xs_ys.
move: (mem_head y ys) (mem_head x xs).
rewrite -(perm_mem eq_xs_ys) [x \in _](perm_mem eq_xs_ys) !inE.
case: eqVneq eq_xs_ys => /= [->|ne_xy] eq_xs_ys ys_x xs_y.
  by rewrite (IHxs ys) // -(perm_cons x).
by case/eqP: ne_xy; apply: r_asym; rewrite (allP r_x_xs) ?(allP r_y_ys).
Qed.

Lemma pairwise_trans s : antisymmetric r ->
   pairwise r s -> {in s & &, transitive r}.
Proof.
move=> /(_ _ _ _)/eqP r_anti + y x z => /pairwiseP-/(_ y) ltP ys xs zs.
have [-> //|neqxy] := eqVneq x y; have [-> //|neqzy] := eqVneq z y.
move=> lxy lyz; move: ys xs zs lxy neqxy lyz neqzy.
move=> /(nthP y)[j jlt <-] /(nthP y)[i ilt <-] /(nthP y)[k klt <-].
have [ltij|ltji|->] := ltngtP i j; last 2 first.
- by move=> leij; rewrite r_anti// leij ltP.
- by move=> lejj; rewrite r_anti// lejj.
move=> _ _; have [ltjk|ltkj|->] := ltngtP j k; last 2 first.
- by move=> lejk; rewrite r_anti// lejk ltP.
- by move=> lekk; rewrite r_anti// lekk.
by move=> _ _; apply: (ltP) => //; apply: ltn_trans ltjk.
Qed.

End EqPairwise.

Arguments subseq_pairwise {T r xs ys}.
Arguments uniq_pairwise {T} xs.
Arguments pairwise_uniq {T r xs}.
Arguments pairwise_eq {T r} r_asym {xs ys}.

Section Permutations.

Variable T : eqType.
Implicit Types (x : T) (s t : seq T) (bs : seq (T * nat)) (acc : seq (seq T)).

Fixpoint incr_tally bs x :=
  if bs isn't b :: bs then [:: (x, 1)] else
  if x == b.1 then (x, b.2.+1) :: bs else b :: incr_tally bs x.

Definition tally s := foldl incr_tally [::] s.

Definition wf_tally :=
  [qualify a bs : seq (T * nat) | uniq (unzip1 bs) && (0 \notin unzip2 bs)].

Definition tally_seq bs := flatten [seq nseq b.2 b.1 | b <- bs].
Local Notation tseq := tally_seq.

Lemma size_tally_seq bs : size (tally_seq bs) = sumn (unzip2 bs).
Proof.
by rewrite size_flatten /shape -map_comp; under eq_map do rewrite /= size_nseq.
Qed.

Lemma tally_seqK : {in wf_tally, cancel tally_seq tally}.
Proof.
move=> bs /andP[]; elim: bs => [|[x [|n]] bs IHbs] //= /andP[bs'x Ubs] bs'0.
rewrite inE /tseq /tally /= -[n.+1]addn1 in bs'0 *.
elim: n 1 => /= [|n IHn] m; last by rewrite eqxx IHn addnS.
rewrite -{}[in RHS]IHbs {Ubs bs'0}// /tally /tally_seq add0n.
elim: bs bs'x [::] => [|[y n] bs IHbs] //= /[1!inE] /norP[y'x bs'x].
by elim: n => [|n IHn] bs1 /=; [rewrite IHbs | rewrite eq_sym ifN // IHn].
Qed.

Lemma incr_tallyP x : {homo incr_tally^~ x : bs / bs \in wf_tally}.
Proof.
move=> bs /andP[]; rewrite unfold_in.
elim: bs => [|[y [|n]] bs IHbs] //= /andP[bs'y Ubs] /[1!inE] /= bs'0.
have [<- | y'x] /= := eqVneq y; first by rewrite bs'y Ubs.
rewrite -andbA {}IHbs {Ubs bs'0}// andbT.
elim: bs bs'y => [|b bs IHbs] /=; rewrite inE ?y'x // => /norP[b'y bs'y].
by case: ifP => _; rewrite /= inE negb_or ?y'x // b'y IHbs.
Qed.

Lemma tallyP s : tally s \is a wf_tally.
Proof.
rewrite /tally; set bs := [::]; have: bs \in wf_tally by [].
by elim: s bs => //= x s IHs bs /(incr_tallyP x)/IHs.
Qed.

Lemma tallyK s : perm_eq (tally_seq (tally s)) s.
Proof.
rewrite -[s in perm_eq _ s]cats0 -[nil]/(tseq [::]) /tally.
elim: s [::] => //= x s IHs bs; rewrite {IHs}(permPl (IHs _)).
rewrite perm_sym -cat1s perm_catCA {s}perm_cat2l.
elim: bs => //= b bs IHbs; case: eqP => [-> | _] //=.
by rewrite -cat1s perm_catCA perm_cat2l.
Qed.

Lemma tallyEl s : perm_eq (unzip1 (tally s)) (undup s).
Proof.
have /andP[Ubs bs'0] := tallyP s; set bs := tally s in Ubs bs'0 *.
rewrite uniq_perm ?undup_uniq {Ubs}// => x.
rewrite mem_undup -(perm_mem (tallyK s)) -/bs.
elim: bs => [|[y [|m]] bs IHbs] //= in bs'0 *.
by rewrite inE IHbs // mem_cat mem_nseq.
Qed.

Lemma tallyE s : perm_eq (tally s) [seq (x, count_mem x s) | x <- undup s].
Proof.
have /andP[Ubs _] := tallyP s; pose b := [fun s x => (x, count_mem x (tseq s))].
suffices /permPl->: perm_eq (tally s) (map (b (tally s)) (unzip1 (tally s))).
  congr perm_eq: (perm_map (b (tally s)) (tallyEl s)).
  by under eq_map do rewrite /= (permP (tallyK s)).
elim: (tally s) Ubs => [|[x m] bs IH] //= /andP[bs'x /IH-IHbs {IH}].
rewrite /tseq /= -/(tseq _) count_cat count_nseq /= eqxx mul1n.
rewrite (count_memPn _) ?addn0 ?perm_cons; last first.
  apply: contra bs'x; elim: {b IHbs}bs => //= b bs IHbs.
  by rewrite mem_cat mem_nseq inE andbC; case: (_ == _).
congr perm_eq: IHbs; apply/eq_in_map=> y bs_y; congr (y, _).
by rewrite count_cat count_nseq /= (negPf (memPnC bs'x y bs_y)).
Qed.

Lemma perm_tally s1 s2 : perm_eq s1 s2 -> perm_eq (tally s1) (tally s2).
Proof.
move=> eq_s12; apply: (@perm_trans _ [seq (x, count_mem x s2) | x <- undup s1]).
  by congr perm_eq: (tallyE s1); under eq_map do rewrite (permP eq_s12).
by rewrite (permPr (tallyE s2)); apply/perm_map/perm_undup/(perm_mem eq_s12).
Qed.

Lemma perm_tally_seq bs1 bs2 :
  perm_eq bs1 bs2 -> perm_eq (tally_seq bs1) (tally_seq bs2).
Proof. by move=> Ebs12; rewrite perm_flatten ?perm_map. Qed.
Local Notation perm_tseq := perm_tally_seq.

Lemma perm_count_undup s :
  perm_eq (flatten [seq nseq (count_mem x s) x | x <- undup s]) s.
Proof.
by rewrite -(permPr (tallyK s)) (permPr (perm_tseq (tallyE s))) /tseq -map_comp.
Qed.

Local Fixpoint cons_perms_ perms_rec (s : seq T) bs bs2 acc :=
  if bs isn't b :: bs1 then acc else
  if b isn't (x, m.+1) then cons_perms_ perms_rec s bs1 bs2 acc else
  let acc_xs := perms_rec (x :: s) ((x, m) :: bs1 ++ bs2) acc in
  cons_perms_ perms_rec s bs1 (b :: bs2) acc_xs.

Local Fixpoint perms_rec n s bs acc :=
  if n isn't n.+1 then s :: acc else cons_perms_ (perms_rec n) s bs [::] acc.
Local Notation cons_perms n := (cons_perms_ (perms_rec n) [::]).

Definition permutations s := perms_rec (size s) [::] (tally s) [::].

Let permsP s : exists n bs,
   [/\ permutations s = perms_rec n [::] bs [::],
       size (tseq bs) == n, perm_eq (tseq bs) s & uniq (unzip1 bs)].
Proof.
have /andP[Ubs _] := tallyP s; exists (size s), (tally s).
by rewrite (perm_size (tallyK s)) tallyK.
Qed.

Local Notation bsCA := (permEl (perm_catCA _ [:: _] _)).
Let cons_permsE : forall n x bs bs1 bs2,
  let cp := cons_perms n bs bs2 in let perms s := perms_rec n s bs1 [::] in
  cp (perms [:: x]) = cp [::] ++ [seq rcons t x | t <- perms [::]].
Proof.
pose is_acc f := forall acc, f acc = f [::] ++ acc. (* f is accumulating. *)
have cpE: forall f & forall s bs, is_acc (f s bs), is_acc (cons_perms_ f _ _ _).
  move=> s bs bs2 f fE acc; elim: bs => [|[x [|m]] bs IHbs] //= in s bs2 acc *.
  by rewrite fE IHbs catA -IHbs.
have prE: is_acc (perms_rec _ _ _) by elim=> //= n IHn s bs; apply: cpE.
pose has_suffix f := forall s : seq T, f s = [seq t ++ s | t <- f [::]].
suffices prEs n bs: has_suffix (fun s => perms_rec n s bs [::]).
  move=> n x bs bs1 bs2 /=; rewrite cpE // prEs.
  by under eq_map do rewrite cats1.
elim: n bs => //= n IHn bs s; elim: bs [::] => [|[x [|m]] bs IHbs] //= bs1.
rewrite cpE // IHbs IHn [in RHS]cpE // [in RHS]IHn map_cat -map_comp.
by congr (_ ++ _); apply: eq_map => t /=; rewrite -catA.
Qed.

Lemma mem_permutations s t : (t \in permutations s) = perm_eq t s.
Proof.
have{s} [n [bs [-> Dn /permPr<- _]]] := permsP s.
elim: n => [|n IHn] /= in t bs Dn *.
  by rewrite inE (nilP Dn); apply/eqP/perm_nilP.
rewrite -[bs in tseq bs]cats0 in Dn *; have x0 : T by case: (tseq _) Dn.
rewrite -[RHS](@andb_idl (last x0 t \in tseq bs)); last first.
  case/lastP: t {IHn} => [|t x] Dt; first by rewrite -(perm_size Dt) in Dn.
  by rewrite -[bs]cats0 -(perm_mem Dt) last_rcons mem_rcons mem_head.
elim: bs [::] => [|[x [|m]] bs IHbs] //= bs2 in Dn *.
rewrite cons_permsE -!cat_cons !mem_cat (mem_nseq m.+1) orbC andb_orl.
rewrite {}IHbs ?(perm_size (perm_tseq bsCA)) //= (permPr (perm_tseq bsCA)).
congr (_ || _); apply/mapP/andP=> [[t1 Dt1 ->] | [/eqP]].
  by rewrite last_rcons perm_rcons perm_cons IHn in Dt1 *.
case/lastP: t => [_ /perm_size//|t y]; rewrite last_rcons perm_rcons => ->.
by rewrite perm_cons; exists t; rewrite ?IHn.
Qed.

Lemma permutations_uniq s : uniq (permutations s).
Proof.
have{s} [n [bs [-> Dn _ Ubs]]] := permsP s.
elim: n => //= n IHn in bs Dn Ubs *; rewrite -[bs]cats0 /unzip1 in Dn Ubs.
elim: bs [::] => [|[x [|m]] bs IHbs] //= bs2 in Dn Ubs *.
  by case/andP: Ubs => _ /IHbs->.
rewrite /= cons_permsE cat_uniq has_sym andbCA andbC.
rewrite {}IHbs; first 1 last; first by rewrite (perm_size (perm_tseq bsCA)).
  by rewrite (perm_uniq (perm_map _ bsCA)).
rewrite (map_inj_uniq (rcons_injl x)) {}IHn {Dn}//=.
have: x \notin unzip1 bs by apply: contraL Ubs; rewrite map_cat mem_cat => ->.
move: {bs2 m Ubs}(perms_rec n _ _ _) (_ :: bs2) => ts.
elim: bs => [|[y [|m]] bs IHbs] //= /[1!inE] bs2 /norP[x'y /IHbs//].
rewrite cons_permsE has_cat negb_or has_map => ->.
by apply/hasPn=> t _; apply: contra x'y => /mapP[t1 _ /rcons_inj[_ ->]].
Qed.

Notation perms := permutations.
Lemma permutationsE s :
    0 < size s ->
  perm_eq (perms s) [seq x :: t | x <- undup s, t <- perms (rem x s)].
Proof.
move=> nt_s; apply/uniq_perm=> [||t]; first exact: permutations_uniq.
  apply/allpairs_uniq_dep=> [|x _|]; rewrite ?undup_uniq  ?permutations_uniq //.
  by case=> [_ _] [x t] _ _ [-> ->].
rewrite mem_permutations; apply/idP/allpairsPdep=> [Dt | [x [t1 []]]].
  rewrite -(perm_size Dt) in nt_s; case: t nt_s => // x t _ in Dt *.
  have s_x: x \in s by rewrite -(perm_mem Dt) mem_head.
  exists x, t; rewrite mem_undup mem_permutations; split=> //.
  by rewrite -(perm_cons x) (permPl Dt) perm_to_rem.
rewrite mem_undup mem_permutations -(perm_cons x) => s_x Dt1 ->.
by rewrite (permPl Dt1) perm_sym perm_to_rem.
Qed.

Lemma permutationsErot x s (le_x := fun t => iota 0 (index x t + 1)) :
  perm_eq (perms (x :: s)) [seq rot i (x :: t) | t <- perms s, i <- le_x t].
Proof.
have take'x t i: i <= index x t -> i <= size t /\ x \notin take i t.
  move=> le_i_x; have le_i_t: i <= size t := leq_trans le_i_x (index_size x t).
  case: (nthP x) => // -[j lt_j_i /eqP]; rewrite size_takel // in lt_j_i.
  by rewrite nth_take // [_ == _](before_find x (leq_trans lt_j_i le_i_x)).
pose xrot t i := rot i (x :: t); pose xrotV t := index x (rev (rot 1 t)).
have xrotK t: {in le_x t, cancel (xrot t) xrotV}.
  move=> i; rewrite mem_iota addn1 /xrotV => /take'x[le_i_t ti'x].
  rewrite -rotD ?rev_cat //= rev_cons cat_rcons index_cat mem_rev size_rev.
  by rewrite ifN // size_takel //= eqxx addn0.
apply/uniq_perm=> [||t]; first exact: permutations_uniq.
  apply/allpairs_uniq_dep=> [|t _|]; rewrite ?permutations_uniq ?iota_uniq //.
  move=> _ _ /allpairsPdep[t [i [_ ? ->]]] /allpairsPdep[u [j [_ ? ->]]] Etu.
  have Eij: i = j by rewrite -(xrotK t i) // /xrot Etu xrotK.
  by move: Etu; rewrite Eij => /rot_inj[->].
rewrite mem_permutations; apply/esym; apply/allpairsPdep/idP=> [[u [i]] | Dt].
  rewrite mem_permutations => -[Du _ /(canLR (rotK i))]; rewrite /rotr.
  by set j := (j in rot j _) => Dt; apply/perm_consP; exists j, u.
pose r := rev (rot 1 t); pose i := index x r; pose u := rev (take i r).
have r_x: x \in r by rewrite mem_rev mem_rot (perm_mem Dt) mem_head.
have [v Duv]: {v | rot i (x :: u ++ v) = t}; first exists (rev (drop i.+1 r)).
  rewrite -rev_cat -rev_rcons -rot1_cons -cat_cons -(nth_index x r_x).
  by rewrite -drop_nth ?index_mem // rot_rot !rev_rot revK rotK rotrK.
exists (u ++ v), i; rewrite mem_permutations -(perm_cons x) -(perm_rot i) Duv.
rewrite mem_iota addn1 ltnS /= index_cat mem_rev size_rev.
by have /take'x[le_i_t ti'x] := leqnn i; rewrite ifN ?size_takel ?leq_addr.
Qed.

Lemma size_permutations s : uniq s -> size (permutations s) = (size s)`!.
Proof.
move Dn: (size s) => n Us; elim: n s => [[]|n IHn s] //= in Dn Us *.
rewrite (perm_size (permutationsE _)) ?Dn // undup_id // factS -Dn.
rewrite -(size_iota 0 n`!) -(size_allpairs (fun=>id)) !size_allpairs_dep.
by apply/congr1/eq_in_map=> x sx; rewrite size_iota IHn ?size_rem ?Dn ?rem_uniq.
Qed.

Lemma permutations_all_uniq s : uniq s -> all uniq (permutations s).
Proof.
by move=> Us; apply/allP=> t; rewrite mem_permutations => /perm_uniq->.
Qed.

Lemma perm_permutations s t :
  perm_eq s t -> perm_eq (permutations s) (permutations t).
Proof.
move=> Est; apply/uniq_perm; try exact: permutations_uniq.
by move=> u; rewrite !mem_permutations (permPr Est).
Qed.

End Permutations.

Section AllIff.
(* The Following Are Equivalent *)

(* We introduce a specific conjunction, used to chain the consecutive *)
(* items in a circular list of implications *)
Inductive all_iff_and (P Q : Prop) : Prop := AllIffConj of P & Q.

Definition all_iff (P0 : Prop) (Ps : seq Prop) : Prop :=
  let fix loop (P : Prop) (Qs : seq Prop) : Prop :=
    if Qs is Q :: Qs then all_iff_and (P -> Q) (loop Q Qs) else P -> P0 in
  loop P0 Ps.

Lemma all_iffLR P0 Ps : all_iff P0 Ps ->
  forall m n, nth P0 (P0 :: Ps) m -> nth P0 (P0 :: Ps) n.
Proof.
move=> iffPs; have PsS n: nth P0 Ps n -> nth P0 Ps n.+1.
  elim: n P0 Ps iffPs => [|n IHn] P0 [|P [|Q Ps]] //= [iP0P] //; first by case.
    by rewrite nth_nil.
  by case=> iPQ iffPs; apply: IHn; split=> // /iP0P.
have{PsS} lePs: {homo nth P0 Ps : m n / m <= n >-> (m -> n)}.
  by move=> m n /subnK<-; elim: {n}(n - m) => // n IHn /IHn; apply: PsS.
move=> m n P_m; have{m P_m} hP0: P0.
  case: m P_m => //= m /(lePs m _ (leq_maxl m (size Ps))).
  by rewrite nth_default ?leq_maxr.
case: n =>// n; apply: lePs 0 n (leq0n n) _.
by case: Ps iffPs hP0 => // P Ps [].
Qed.

Lemma all_iffP P0 Ps :
   all_iff P0 Ps -> forall m n, nth P0 (P0 :: Ps) m <-> nth P0 (P0 :: Ps) n.
Proof. by move=> /all_iffLR-iffPs m n; split => /iffPs. Qed.

End AllIff.
Arguments all_iffLR {P0 Ps}.
Arguments all_iffP {P0 Ps}.
Coercion all_iffP : all_iff >-> Funclass.

(* This means "the following are all equivalent: P0, ... Pn" *)
Notation "[ '<->' P0 ; P1 ; .. ; Pn ]" :=
  (all_iff P0 (@cons Prop P1 (.. (@cons Prop Pn nil) ..))) : form_scope.

Ltac tfae := do !apply: AllIffConj.

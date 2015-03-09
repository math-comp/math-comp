(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg matrix poly finset.
Require Import fingroup morphism perm automorphism quotient action finalg zmodp.
Require Import gfunctor center gproduct cyclic pgroup abelian frobenius.
Require Import mxalgebra mxrepresentation vector falgebra fieldext galois.
Require Import ssrnum rat algC algnum classfun character.
Require Import integral_char inertia vcharacter.
Require Import PFsection1 PFsection2.

(******************************************************************************)
(* This file covers Peterfalvi, Section 3: TI-Subsets with Cyclic Normalizers *)
(******************************************************************************)
(* Given a direct product decomposition defW : W1 \x W2 = W, we define here:  *)
(*       cyclicTIset defW == the set complement of W1 and W2 in W; this       *)
(*            (locally) V    definition is usually Let-bound to V.            *)
(*                        := W :\: (W1 :|: W2).                               *)
(* cyclicTI_hypothesis G defW <-> W is a cyclic of odd order that is the      *)
(*                           normaliser in G of its non-empty TI subset       *)
(*                           V = cyclicTIset defW = W :\: (W1 :|: W2).        *)
(*   -> This is Peterfalvi, Hypothesis (3.1), or Feit-Thompson (13.1).        *)
(*   cyclicTIirr defW i j == the irreducible character of W coinciding with   *)
(*       (locally) w_ i j    chi_i and 'chi_j on W1 and W2, respectively.     *)
(*                           This notation is usually Let-bound to w_ i j.    *)
(*                        := 'chi_(dprod_Iirr defW (i, j)).                   *)
(* cfCyclicTIset defW i j == the virtual character of 'Z[irr W, V] coinciding *)
(*    (locally) alpha_ i j   with 1 - chi_i and 1 - 'chi_j on W1 and W2,      *)
(*                           respectively. This definition is denoted by      *)
(*                           alpha_ i j in this file, and is only used in the *)
(*                           proof if Peterfalvi (13.9) in the sequel.        *)
(*                        := cfDprod defW (1 - 'chi_i) (1 - 'chi_j).          *)
(*                           = 1 - w_ i 0 - w_ 0 j + w_ i j.                  *)
(* cfCyclicTIsetBase defW := the tuple of all the alpha_ i j, for i, j != 0.  *)
(*     (locally) cfWVbase    This is a basis of 'CF(W, V); this definition is *)
(*                           not used outside this file.                      *)
(* For ctiW : cyclicTI_hypothesis defW G we also define                       *)
(*       cyclicTIiso ctiW == a linear isometry from 'CF(W) to 'CF(G) that     *)
(*        (locally) sigma    that extends induction on 'CF(W, V), maps the    *)
(*                           w_ i j to virtual characters, and w_ 0 0 to 1.   *)
(*                           This definition is usually Let-bound to sigma,   *)
(*                           and only depends extensionally on W, V and G.    *)
(*     (locally) eta_ i j := sigma (w_ i j), as in sections 13 and 14 of      *)
(*                           tha Peterfalv text.                              *)
(*   cyclicTI_NC ctiW phi == the number of eta_ i j constituents of phi.      *)
(*       (locally) NC phi := #|[set ij | '[phi, eta_ ij .1 ij.2] != 0]|.      *)
(* The construction of sigma involves a large combinatorial proof, for which  *)
(* it is worthwhile to use reflection techniques to automate mundane and      *)
(* repetitive arguments. We isolate the necessary boilerplate in a separate   *)
(* CyclicTIisoReflexion module.                                               *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Definitions.

Variables (gT : finGroupType) (G W W1 W2 : {set gT}).

Definition cyclicTIset of W1 \x W2 = W := W :\: (W1 :|: W2).

Definition cyclicTI_hypothesis (defW : W1 \x W2 = W) :=
  [/\ cyclic W, odd #|W| & normedTI (cyclicTIset defW) G W].

End Definitions.

(* These is defined as a Notation which clients can bind with a Section Let   *)
(* that can be folded easily. *)
Notation cyclicTIirr defW i j := 'chi_(dprod_Iirr defW (i, j)).

Module CyclicTIisoReflexion.

(******************************************************************************)
(*   Support for carrying out the combinatorial parts of the proof of Theorem *)
(* (3.5) by reflection. Specifically, we need to show that in a rectangular   *)
(* array of virtual characters of norm 3, of even dimensions, and such that   *)
(* the dot product of two entries is 1 if they are on the same row or column, *)
(* the entries of each column contain a "pivot" normal virtual character      *)
(* orthogonal to all other columns. The proof never needs to consider more    *)
(* than a 4 x 2 rectangle, but frequently renumbers lines, columns and        *)
(* orthonormal components in order to do so.                                  *)
(*   We want to use reflection to automate this renumbering; we also want to  *)
(* automate the evaluation of the dot product constaints for partially        *)
(* described entries of the matrix.                                           *)
(*   To do so we define a "theory" data structure to store a reifed form of   *)
(* such partial descriptions: a set of "clauses", each consisting in an index *)
(* (i, j) into the array, and a collection of "literals" (k, v) representing  *)
(* constraints '[b_(i, j), x`_k] = v%:~R, with v = 0, 1 or -1. A clause with  *)
(* exactly three nonzero literals defines b_(i, j) exactly.                   *)
(*   We define special notation for the concrete instances that appear in     *)
(* reflected proofs; for example                                              *)
(*    |= & b11 = -x1 + x2 + x3 & x1, ~x2 in b12 & ? in b31                    *)
(* denotes the "theory" of arrays whose two left entries decomposes into      *)
(* x1 + x2 + x3 for some orthonormal x1, x2, and x3, such that the second top *)
(* entry has x1 is a signed component but is orthogonal to x2, and which have *)
(* an (unconstrained) first entry in the third column. (The concrete encoding *)
(* shifts indices to start at 0.)                                             *)
(*  The "models" in which such theories are interpreted supply the dimensions *)
(* of the array, which must be even, nonequal and at least 2, the function    *)
(* mapping indices to array entries, which must be virtual characters with    *)
(* the requisite norms and dot products, and an orthonormal sequence of       *)
(* virtual characters that will be used to interpret the xij; a model coerces *)
(* to any of these three components.                                          *)
(*   We are primarily interested in two predicates:                           *)
(*    sat m th <=> the interpretation of th in m is well-defined (no out of   *)
(*                 bound indices) and valid (all constraints true).           *)
(*    unsat th <-> forall m, ~ sat m th                                       *)
(* While the main theorem of this section, column_pivot, can be seen as an    *)
(* instance of "sat", all the principal combinatorial lemmas use "unsat",     *)
(* whose universal quantifier allows symmetry reductions. We present the set  *)
(* of lemmas implementing reflection-assisted proofs of "unsat th" as a small *)
(* domain-specific proof language consisting of the following tactics:        *)
(*       consider bij ::= add a clause for bij, which must not appear in th,  *)
(*                        changing the goal to unsat th & ? in bij.           *)
(*                        bij must be within a 4 x 2 bounding box, and th     *)
(*                        must be symmetric if bij "breaks" the 2 x 2 box.    *)
(*           fill bij ::= add an x(k.+1) literal to the bij clause in th,     *)
(*                        where x1, ..., xk are all the normal characters     *)
(*                        appearing in th, and the clause for bij exists and  *)
(*                        contains assumptions for all of x1, ..., xk, at     *)
(*                        two of which are nonzero.                           *)
(* uwlog Dcl: cl [by tac] ::= add the clause cl to th, replacing an existing  *)
(*                        clause for the same matrix entry. This produces a   *)
(*                        side goal of unsat th, but with an additional       *)
(*                        assumption Dcl : unsat th+cl, which can be resolved *)
(*                        with the optional "by tac".                         *)
(* uhave lit in bij as T(ij, kl) ::= adds the literal lit (one of xk, -xk, or *)
(*                        ~xk) to an existing clause for bij in th, using the *)
(*                        reflection lemma T(ij, kl) to rule out the other    *)
(*                        possibilities for xk. Here T can be either O        *)
(*                        (general dot product evaluation) or L (specific     *)
(*                        line/column constraints following from (3.5.2)).    *)
(* uhave lit, lit' in bij as T(ij, kl) ::= adds both lit and lit'.            *)
(* uhave lit | lit' in bij as T(ij, kl) ::= produces two subgoals, where lit  *)
(*                        (resp. lit') is added to the ... in bij clause in   *)
(*                        th, using T(ij, kl) to eliminate the third literal. *)
(*                        (lit and lit' must constrain the same component).   *)
(* uhave lit | lit' | lit'' in bij ::= produces three subgoals, where lit     *)
(*                        (resp. lit', lit'') is added to the bij clause in   *)
(*                        th; lit, lit', lit'' should be a permutation of xk, *)
(*                        -xk, and ~xk for some k.                            *)
(* uwlog Ebij: lit | lit' in bij as T(ij, kl) ::= adds lit to the bij clause  *)
(*                        in th, but produces a side goal where lit' has been *)
(*                        added instead, with an additional assumption        *)
(*                        Ebij: th + (lit in bij); T(ij, kl) is used to rule  *)
(*                        out the third value.                                *)
(* counter to T(ij, kl) ::= use T(ij, kl) to conclude that unsat th.          *)
(*          uexact Hth' ::= use Hth' : unsat th', where th' is a subset of th *)
(*                       (with the same order of literals) to conclude.       *)
(*    symmetric to Hth' ::= use Hth' : unsat th', where th' is a permutation  *)
(*                       of a subset of th (preserving columns, and with at   *)
(*                       most one row exchange) to conclude.                  *)
(******************************************************************************)

Import ssrint.

(* Clause left-hand side, a reference to a value of beta; in the reference    *)
(* model m, (i, j) stands for beta_ (inord i.+1) (inord j.+1).                *)
Definition ref := (nat * nat)%type.
Implicit Type ij : ref.
Definition Ref b_ij : ref := edivn (b_ij - 11) 10. (* Ref 21 = (1, 0). *)
Notation "''b' ij" := (Ref ij) (at level 0, ij at level 0, format "''b' ij").
Notation b11 := 'b11. Notation b12 := 'b12.
Notation b21 := 'b21. Notation b22 := 'b22.
Notation b31 := 'b31. Notation b32 := 'b32.
Notation b41 := 'b41. Notation b42 := 'b42.

Definition bbox := (nat * nat)%type. (* bounding box for refs. *)
Implicit Type bb : bbox.
Identity Coercion pair_of_bbox : bbox >-> prod.

Definition sub_bbox bb1 bb2 := (bb1.1 <= bb2.1)%N && (bb1.2 <= bb2.2)%N.
Definition wf_ref bb := [pred ij : ref | (ij.1 < bb.1)%N && (ij.2 < bb.2)%N].
Definition dot_ref ij1 ij2 := ((ij1.1 == ij2.1).+1 * (ij1.2 == ij2.2).+1 - 1)%N.

Lemma bbox_refl bb : sub_bbox bb bb. Proof. exact/andP. Qed.

(* Clause right-hand side litteral, denoting the projection of the left-hand  *)
(* side on an irreducible character of G: in a valid model m, (k, v) stands   *)
(* for the component m`_k *~ v = (model_xi m)`_k, and for the projection      *)
(* constraint '[m i j, m`_k] == v%:~R.                                        *)
Definition lit := (nat * int)%type. (* +x1 = (0,1) ~x2 = (1,0) -x3 = (2, -1)  *)
Implicit Types (kv : lit) (kvs : seq lit).
Definition Lit k1 v : lit := if (0 + k1)%N is k.+1 then (k, v) else (k1, v).
Notation "+x k" := (Lit k 1) (at level 0, k at level 0, format "+x k").
Notation "-x k" := (Lit k (-1)) (at level 0, k at level 0, format "-x k").
Notation "~x k" := (Lit k 0) (at level 0, k at level 0, format "~x k").
Notation x1 := +x1. Notation x2 := +x2.
Notation x3 := +x3. Notation x4 := +x4.
Notation x5 := +x5. Notation x6 := +x6.
Notation x7 := +x7. Notation x8 := +x8.

Definition AndLit kvs kv := kv :: kvs.
Definition AddLit := AndLit.
Notation "(*dummy*)" := (Prop Prop) (at level 0) : defclause_scope.
Arguments Scope AddLit [defclause_scope _].
Infix "+" := AddLit : defclause_scope.
Definition SubLit kvs kv := AddLit kvs (kv.1, - kv.2).
Arguments Scope SubLit [defclause_scope _].
Infix "-" := SubLit : defclause_scope.
Coercion LastLit kv := [:: kv].

Fixpoint norm_cl kvs : nat :=
  (if kvs is (_, v) :: kvs1 then `|v| ^ 2 + norm_cl kvs1 else 0)%N.

Definition clause := (ref * seq lit)%type.
Implicit Type cl : clause.
Definition Clause ij kvs : clause := (ij, kvs).
Notation "& kv1 , .. , kvn 'in' ij" :=
  (Clause ij (AndLit .. (AndLit nil kv1) .. kvn))
  (at level 200, ij, kv1, kvn at level 0,
   format "&  kv1 ,  .. ,  kvn  'in'  ij").
Notation "& ? 'in' ij" := (Clause ij nil)
  (at level 200, ij at level 0, format "&  ?  'in'  ij").
Definition DefClause := Clause.
Arguments Scope DefClause [_ defclause_scope].
Notation "& ij = kvs" := (DefClause ij kvs)
  (at level 200, ij at level 0, format "&  ij  =  kvs").

Definition theory := seq clause.
Implicit Type th : theory.
Definition AddClause th cl : theory := cl :: th.
Notation "|= cl1 .. cln" := (AddClause .. (AddClause nil cl1) .. cln)
  (at level 8, cl1, cln at level 200,
   format "|=  '[hv' cl1 '/'  .. '/'  cln ']'").

(* Transpose (W1 / W2 symmetry). *)

Definition tr (ij : nat * nat) : ref := (ij.2, ij.1).
Definition tr_th th : theory := [seq (tr cl.1, cl.2) | cl <- th].

Lemma trK : involutive tr. Proof. by case. Qed.
Lemma tr_thK : involutive tr_th. Proof. by apply: mapK => [[[i j] kvs]]. Qed.

(* Index range of a theory. *)

Fixpoint th_bbox th : bbox :=
  if th is (i, j, _) :: th1 then
    let: (ri, rj) := th_bbox th1 in (maxn i.+1 ri, maxn j.+1 rj)
  else (0, 0)%N.

Lemma th_bboxP th bb :
  reflect {in th, forall cl, cl.1 \in wf_ref bb} (sub_bbox (th_bbox th) bb).
Proof.
pose in_bb := [pred cl : clause | cl.1 \in wf_ref bb].
suffices ->: sub_bbox (th_bbox th) bb = all in_bb th by apply: allP.
elim: th => [|[[i j] _] th] //=; case: (th_bbox th) => ri rj /=.
by rewrite /sub_bbox /= !geq_max andbACA => ->.
Qed.
Implicit Arguments th_bboxP [th bb].

Fixpoint th_dim th : nat :=
  if th is (_, kvs) :: th1 then
    foldr (fun kv => maxn kv.1.+1) (th_dim th1) kvs
  else 0%N.

Lemma th_dimP th bk :
  reflect {in th, forall cl, {in cl.2, forall kv, kv.1 < bk}}%N
          (th_dim th <= bk)%N.
Proof.
pose in_bk := [pred cl : clause | all (fun kv => kv.1 < bk)%N cl.2].
suffices ->: (th_dim th <= bk)%N = all in_bk th.
  by apply: (iffP allP) => bk_th cl /bk_th/allP.
elim: th => // [[_ kvs] th /= <-]; elim: kvs => //= kv kvs.
by rewrite -andbA geq_max => ->.
Qed.
Implicit Arguments th_dimP [th bk].

(* Theory and clause lookup. *)

CoInductive get_spec T (P : T -> Prop) (Q : Prop) : option T -> Prop :=
  | GetSome x of P x : get_spec P Q (Some x)
  | GetNone of Q     : get_spec P Q None.

Fixpoint get_cl ij (th : theory) : option clause :=
  if th is cl :: th1 then if cl.1 == ij then Some cl else get_cl ij th1
  else None.

Lemma get_clP ij (th : theory) :
  get_spec (fun cl : clause => cl \in th /\ cl.1 = ij) True (get_cl ij th).
Proof.
elim: th => /= [|cl th IHth]; first by right.
case: eqP => [Dij | _]; first by left; rewrite ?mem_head.
by case: IHth => [cl1 [th_cl1 Dij]|]; constructor; rewrite // mem_behead.
Qed.

Fixpoint get_lit (k0 : nat) kvs : option int :=
  if kvs is (k, v) :: kvs1 then if k == k0 then Some v else get_lit k0 kvs1
  else None.

Lemma get_litP k0 kvs :
  get_spec (fun v => (k0, v) \in kvs) (k0 \notin unzip1 kvs) (get_lit k0 kvs).
Proof.
elim: kvs => [|[k v] kvs IHkvs /=]; [by right | rewrite inE eq_sym].
have [-> | k'0] := altP eqP; first by left; rewrite ?mem_head.
by have [v0 kvs_k0v | kvs'k0] := IHkvs; constructor; rewrite // mem_behead.
Qed.

(* Theory extension. *)

Fixpoint set_cl cl2 th : wrapped theory :=
  if th is cl :: th1 then
    let: Wrap th2 := set_cl cl2 th1 in
    if cl.1 == cl2.1 then Wrap (AddClause th2 cl2) else Wrap (AddClause th2 cl)
  else Wrap nil.

Definition ext_cl th cl k v :=
  let: (ij, kvs) := cl in set_cl (Clause ij (AndLit kvs (Lit k.+1 v))) th.

Definition wf_ext_cl cl k rk := (k \notin unzip1 cl.2) && (k < rk)%N.

Definition wf_fill k kvs := (size kvs == k) && (norm_cl kvs < 3)%N.

Lemma ext_clP cl1 th k v (cl1k := (cl1.1, (k, v) :: cl1.2)) :
    cl1 \in th ->
  exists2 th1, ext_cl th cl1 k v = Wrap th1
        & cl1k \in th1 
        /\ th1 =i [pred cl | if cl.1 == cl1.1 then cl == cl1k else cl \in th].
Proof.
case: cl1 => ij kvs /= in cl1k * => th_cl1; set th1p := [pred cl | _].
pose th1 := [seq if cl.1 == ij then cl1k else cl | cl <- th].
exists th1; first by elim: (th) @th1 => //= cl th' ->; rewrite -2!fun_if.
suffices Dth1: th1 =i th1p by rewrite Dth1 !inE !eqxx.
move=> cl; rewrite inE; apply/mapP/idP=> [[{cl}cl th_cl ->] | ].
  by case cl_ij: (cl.1 == ij); rewrite ?eqxx ?cl_ij.
case: ifP => [_ /eqP-> | cl'ij th_cl]; last by exists cl; rewrite ?cl'ij.
by exists (ij, kvs); rewrite ?eqxx.
Qed.

(* Satisfiability tests. *)

Definition sat_test (rO : rel clause) ij12 th :=
  if get_cl (Ref ij12.1) th is Some cl1 then
    oapp (rO cl1) true (get_cl (Ref ij12.2) th)
  else true.

(* This reflects the application of (3.5.1) for an arbitrary pair of entries. *)
Definition Otest cl1 cl2 :=
  let: (ij1, kvs1) := cl1 in let: (ij2, kvs2) := cl2 in
  let fix loop s1 s2 kvs2 :=
    if kvs2 is (k, v2) :: kvs2 then
      if get_lit k kvs1 is Some v1 then loop (v1 * v2 + s1) s2 kvs2 else
      loop s1 s2.+1 kvs2
    else (s1, if norm_cl kvs1 == 3 then 0%N else s2) in
  let: (s1, s2) := loop 0 0%N kvs2 in
  (norm_cl kvs2 == 3) ==> (`|s1 - dot_ref ij1 ij2| <= s2)%N.

(* Matching up to a permutation of the rows, columns, and base vectors. *)

Definition sub_match th1 th2 :=
  let match_cl cl1 cl2 :=
    if cl2.1 == cl1.1 then subseq cl1.2 cl2.2 else false in
  all [pred cl1 | has (match_cl cl1) th2] th1.

Definition wf_consider ij th (ri := (th_bbox th).1) :=
  (ij.1 < 2 + ((2 < ri) || sub_match th (tr_th th)).*2)%N && (ij.2 < 2)%N.

CoInductive sym := Sym (si : seq nat) (sj : seq nat) (sk : seq nat).

Definition sym_match s th1 th2 :=
  let: Sym si sj sk := s in let: (ri, rj, rk) := (th_bbox th1, th_dim th1) in
  let is_sym r s := uniq s && all (gtn r) s in
  let match_cl cl2 :=
    let: (i2, j2, kvs2) := cl2 in let ij := (nth ri si i2, nth rj sj j2) in
    let match_lit kvs1 kv := (nth rk sk kv.1, kv.2) \in kvs1 in
    let match_cl1 cl1 :=
      let: (ij1, kvs1) := cl1 in (ij1 == ij) && all (match_lit kvs1) kvs2 in
    uniq (unzip1 kvs2) && has match_cl1 th1 in
  [&& is_sym ri si, is_sym rj sj, is_sym rk sk & all match_cl th2].

(* Try to compute the base vector permutation for a given row and column      *)
(* permutation. We assume each base vector is determined by the entries of    *)
(* which it is a proper constituent, and that there are at most two columns.  *)
Definition find_sym_k th1 th2 (si sj : seq nat) :=
  let store_lit c kv ksig :=
    let: (k, v) := kv in if v == 0 then ksig else let cv := (c, v) in
    let fix insert_in (cvs : seq (nat * int)) :=
      if cvs is cv' :: cvs' then
        if (c < cv'.1)%N then cv :: cvs else cv' :: insert_in cvs'
      else [:: cv] in
    set_nth nil ksig k (insert_in (nth nil ksig k)) in
  let fix read_lit ksig1 ksig2 :=
    if ksig1 is cvs :: ksig1' then
      let k := index cvs ksig2 in
      k :: read_lit ksig1' (set_nth nil ksig2 k nil)
    else nil in
  let fix store2 ksig1 ksig2 cls1 :=
    if cls1 is (i1, j1, kvs1) :: cls1' then
      if get_cl (nth 0 si i1, nth 0 sj j1)%N th2 is Some (_, kvs2) then
        let st_kvs := foldr (store_lit (i1.*2 + j1)%N) in (* assume j1 <= 1 *)
        store2 (st_kvs ksig1 kvs1) (st_kvs ksig2 kvs2) cls1'
      else None
    else
      let sk := read_lit ksig1 ksig2 in
      if all (gtn (size ksig2)) sk then Some (Sym si sj sk) else None in
  store2 nil nil th1.

(* Try to find a symmetry that maps th1 to th2, assuming the same number of   *)
(* rows and columns, and considering at most one row exchange.                *)
Definition find_sym th1 th2 :=
  let: (ri, rj) := th_bbox th2 in let si := iota 0 ri in let sj := iota 0 rj in
  if find_sym_k th1 th2 si sj is Some _ as s then s else
  let fix loop m :=
    if m is i.+1 then
      let fix inner_loop m' :=
        if m' is i'.+1 then
          let si' := (set_nth 0 (set_nth 0 si i i') i' i)%N in
          if find_sym_k th1 th2 si' sj is Some _ as s then s else inner_loop i'
        else None in
      if inner_loop i is Some _ as s then s else loop i
    else None in
  loop ri.

Section Interpretation.

Variables (gT : finGroupType) (G : {group gT}).

Definition is_Lmodel bb b :=
  [/\ [/\ odd bb.1.+1, odd bb.2.+1, bb.1 > 1, bb.2 > 1 & bb.1 != bb.2]%N,
      forall ij, b ij \in 'Z[irr G]
    & {in wf_ref bb &, forall ij1 ij2, '[b ij1, b ij2] = (dot_ref ij1 ij2)%:R}].

Definition is_Rmodel X := orthonormal X /\ {subset X <= 'Z[irr G]}.

Inductive model := Model bb f X of is_Lmodel bb f & is_Rmodel X.

Coercion model_bbox m := let: Model d _ _ _ _ := m in d.
Definition model_entry m := let: Model _ f _ _ _ := m in f.
Coercion model_entry : model >-> Funclass.
Coercion model_basis m := let: Model _ _ X _ _ := m in X.
Lemma LmodelP (m : model) : is_Lmodel m m. Proof. by case: m. Qed.
Lemma RmodelP (m : model) : is_Rmodel m. Proof. by case: m. Qed.

Fact nil_RmodelP : is_Rmodel nil. Proof. by []. Qed.

Definition eval_cl (m : model) kvs := \sum_(kv <- kvs) m`_kv.1 *~ kv.2.

Definition sat_lit (m : model) ij kv := '[m ij, m`_kv.1] == kv.2%:~R.
Definition sat_cl m cl := uniq (unzip1 cl.2) && all (sat_lit m cl.1) cl.2.

Definition sat (m : model) th :=
  [&& sub_bbox (th_bbox th) m, th_dim th <= size m & all (sat_cl m) th]%N.
Definition unsat th := forall m, ~ sat m th.

Lemma satP (m : model) th :
  reflect {in th, forall cl,
              [/\ cl.1 \in wf_ref m, uniq (unzip1 cl.2)
                & {in cl.2, forall kv, kv.1 < size m /\ sat_lit m cl.1 kv}%N]}
          (sat m th).
Proof.
apply: (iffP and3P) => [[/th_bboxP thbP /th_dimP thdP /allP thP] cl th_cl |thP].
  have /andP[-> clP] := thP _ th_cl; split=> // [|kv cl_kv]; first exact: thbP.
  by rewrite (thdP _ th_cl) ?(allP clP).
split; first by apply/th_bboxP=> cl /thP[].
  by apply/th_dimP=> cl /thP[_ _ clP] kv /clP[].
by apply/allP=> cl /thP[_ Ucl clP]; rewrite /sat_cl Ucl; apply/allP=> kv /clP[].
Qed.
Implicit Arguments satP [m th].

(* Reflexion of the dot product. *)

Lemma norm_clP m th cl :
    sat m th -> cl \in th ->
  let norm := norm_cl cl.2 in let beta := m cl.1 in 
  [/\ (norm <= 3)%N, norm == 3 -> beta = eval_cl m cl.2
    & (norm < 3)%N -> size cl.2 == size m -> 
      exists2 dk, dk \in dirr_constt beta & orthogonal (dchi dk) m].
Proof.
case: cl => ij kvs /satP thP /thP[wf_ij Uks clP] norm beta.
have [[_ ZmL Dm] [o1m ZmR]] := (LmodelP m, RmodelP m).
set ks := unzip1 kvs in Uks; pose Aij := [seq m`_k | k <- ks].
have lt_ks k: k \in ks -> (k < size m)%N by case/mapP=> kv /clP[ltk _] ->.
have sAm: {subset Aij <= (m : seq _)}
  by move=> _ /mapP[k /lt_ks ltk ->]; rewrite mem_nth.
have o1Aij: orthonormal Aij.
  have [Um _] := orthonormalP o1m; apply: sub_orthonormal o1m => //.
  rewrite map_inj_in_uniq // => k1 k2 /lt_ks ltk1 /lt_ks ltk2 /eqP.
  by apply: contraTeq; rewrite nth_uniq.
have [X AijX [Y [defXY oXY oYij]]] := orthogonal_split Aij beta.
have{AijX} defX: X = \sum_(xi <- Aij) '[beta, xi] *: xi.
  have [_ -> ->] := orthonormal_span o1Aij AijX; apply: eq_big_seq => xi CFxi.
  by rewrite defXY cfdotDl (orthoPl oYij) ?addr0.
have ->: eval_cl m kvs = X.
  rewrite {}defX !big_map; apply: eq_big_seq => kv /clP[_ /eqP->].
  by rewrite scaler_int.
rewrite -leC_nat -ltC_nat -eqC_nat /=.
have <-: '[beta] = 3%:R by rewrite Dm // /dot_ref !eqxx.
have <-: '[X] = norm%:R.
  rewrite {}defX {}/norm cfnorm_sum_orthonormal // {o1Aij oYij sAm}/Aij.
  transitivity (\sum_(kv <- kvs) `|kv.2%:~R| ^+ 2 : algC).
    by rewrite !big_map; apply: eq_big_seq => kv /clP[_ /eqP->].
  rewrite unlock /=; elim: (kvs) => //= [[k v] kvs' ->].
  by rewrite -intr_norm -natrX -natrD.
rewrite defXY cfnormDd //; split; first by rewrite ler_paddr ?cfnorm_ge0.
  by rewrite eq_sym addrC -subr_eq0 addrK cfnorm_eq0 => /eqP->; rewrite addr0.
have{ZmL} Zbeta: beta \in 'Z[irr G] by apply: ZmL.
have Z_X: X \in 'Z[irr G].
  rewrite defX big_seq rpred_sum // => xi /sAm/ZmR Zxi.
  by rewrite rpredZ_Cint ?Cint_cfdot_vchar.
rewrite -ltr_subl_addl subrr cnorm_dconstt; last first.
  by rewrite -[Y](addKr X) -defXY addrC rpredB.
have [-> | [dk Ydk] _ /eqP sz_kvs] := set_0Vmem (dirr_constt Y).
  by rewrite big_set0 ltrr.
have Dks: ks =i iota 0 (size m).
  have: {subset ks <= iota 0 (size m)} by move=> k /lt_ks; rewrite mem_iota.
  by case/leq_size_perm=> //; rewrite size_iota size_map sz_kvs.
suffices o_dk_m: orthogonal (dchi dk) m.
  exists dk; rewrite // dirr_consttE defX cfdotDl cfdot_suml.
  rewrite big1_seq ?add0r -?dirr_consttE // => xi /sAm CFxi.
  by rewrite cfdotC cfdotZr (orthoPl o_dk_m) // mulr0 conjC0.
apply/orthoPl=> _ /(nthP 0)[k ltk <-]; have [Um o_m] := orthonormalP o1m.
have Z1k: m`_k \in dirr G by rewrite dirrE ZmR ?o_m ?eqxx ?mem_nth.
apply: contraTeq Ydk => /eqP; rewrite dirr_consttE cfdot_dirr ?dirr_dchi //.
have oYm: '[Y, m`_k] = 0 by rewrite (orthoPl oYij) ?map_f // Dks mem_iota.
by do 2?case: eqP => [-> | _]; rewrite // ?cfdotNr oYm ?oppr0 ltrr.
Qed.

Lemma norm_cl_eq3 m th cl :
  sat m th -> cl \in th -> norm_cl cl.2 == 3 -> m cl.1 = eval_cl m cl.2.
Proof. by move=> m_th /(norm_clP m_th)[]. Qed.

Lemma norm_lit m th cl kv :
  sat m th -> cl \in th -> kv \in cl.2 -> (`|kv.2| <= 1)%N.
Proof.
move=> m_th /(norm_clP m_th)[cl_le3 _ _].
elim: cl.2 => //= [[k v] kvs IHkvs] in cl_le3 * => /predU1P[-> | /IHkvs->//].
  by apply: contraLR cl_le3; rewrite -ltnNge -leq_sqr => /subnKC <-.
exact: leq_trans (leq_addl _ _) cl_le3.
Qed.

(* Decision procedure framework (in which we will define O and L). *)

Definition is_sat_test (tO : pred theory) := forall m th, sat m th -> tO th.

Lemma sat_testP (rO : rel clause) ij12 :
    (forall m th cl1 cl2, sat m th -> cl1 \in th -> cl2 \in th -> rO cl1 cl2) ->
  is_sat_test (sat_test rO ij12).
Proof.
rewrite /sat_test => O m th /O O_th; case: get_clP => // cl1 [th_cl1 _].
by case: get_clP => // cl2 [th_cl2 _]; apply: O_th.
Qed.

(* Case analysis on the value of a specific projection. *)

Definition lit_vals : seq int := [:: 0; 1; -1].

Lemma sat_cases (m : model) th k cl :
    sat m th -> cl \in th -> wf_ext_cl cl k (size m) ->
  exists2 v, v \in lit_vals & sat m (unwrap (ext_cl th cl k v)).
Proof.
case: cl => ij kvs /satP thP th_cl /andP[cl'k ltkm].
have [[_ ZmL _] [o1m ZmR]] := (LmodelP m, RmodelP m).
have [m_ij Uij clP] := thP _ th_cl.
have /CintP[v Dv]: '[m ij, m`_k] \in Cint.
  by rewrite Cint_cfdot_vchar ?ZmL ?ZmR ?mem_nth.
have [/= th1 Dthx [th1_cl Dth1]] := ext_clP k v th_cl.
suffices{Dthx} m_th1: sat m th1.
  exists v; last by rewrite /ext_cl Dthx.
  by case: (v) (norm_lit m_th1 th1_cl (mem_head _ _)); do 2?case.
apply/satP=> cl1; rewrite Dth1 inE; case: ifP => [_ /eqP-> | _ /thP] //=.
by rewrite cl'k; split=> // kv /predU1P[-> | /clP//]; rewrite /sat_lit Dv.
Qed.
Implicit Arguments sat_cases [m th cl].

Definition unsat_cases_hyp th0 kvs tO cl :=
  let: (k, _) := head (2, 0) kvs in let thk_ := ext_cl th0 cl k in
  let th's := [seq unwrap (thk_ v) | v <- lit_vals & v \notin unzip2 kvs] in
  let add hyp kv :=
    let: (_, v) := kv in let: Wrap th := thk_ v in hyp /\ unsat th in
  foldl add (wf_ext_cl cl k (th_dim th0) && all (predC tO) th's) kvs.

Lemma unsat_cases th ij kvs tO :
    is_sat_test tO -> oapp (unsat_cases_hyp th kvs tO) False (get_cl ij th) ->
  unsat th.
Proof.
case: get_clP => //= cl [th_cl _] O; rewrite /unsat_cases_hyp.
case: head => k _; set thk_ := ext_cl th cl k; set add := fun _ _ => _.
set wf_kvs := _ && _; rewrite -[kvs]revK foldl_rev => Ukvs m m_th.
have{Ukvs}: all (fun kv => ~~ sat m (unwrap (thk_ kv.2))) (rev kvs) && wf_kvs.
  elim: rev Ukvs => // [[_ v] /= kvs' IH]; case Dthk: (thk_ v) => [thv] [/IH].
  by rewrite -andbA => -> Uthk; rewrite andbT; apply/negP; apply: Uthk.
case/and3P=> /allP Uthkvs /andP[cl'k ltkr] /allP Uthkv's.
have [|{cl'k ltkr} v lit_v m_thv] := sat_cases k m_th th_cl.
  by rewrite /wf_ext_cl cl'k (leq_trans ltkr) //; have [] := and3P m_th.
have /idPn[] := O _ _ m_thv; apply: Uthkv's; apply: map_f.
rewrite mem_filter lit_v andbT -mem_rev -map_rev.
by apply: contraL m_thv => /mapP[kv /Uthkvs m'thkv ->].
Qed.

(* Dot product reflection. *)

Lemma O ij12 : is_sat_test (sat_test Otest ij12).
Proof.
apply: sat_testP => m th [ij1 kvs1] [ij2 kvs2] /= m_th th_cl1 th_cl2.
set cl1eq := _ == 3; set cl2eq := _ == 3; have [_ _ Dm] := LmodelP m.
pose goal s1 s2 := cl2eq ==> (`|s1 - (dot_ref ij1 ij2)%:~R| <= s2%:R :> algC).
set kvs := kvs2; set s1 := 0; set s2 := {2}0%N; have thP := satP m_th.
have{thP} [[wf_cl1 _ cl1P] [wf_cl2 _ cl2P]] := (thP _ th_cl1, thP _ th_cl2).
have: goal (s1%:~R + '[m ij1, eval_cl m kvs]) (if cl1eq then 0%N else s2).
  apply/implyP=> /(norm_cl_eq3 m_th th_cl2) <-.
  by rewrite if_same Dm // addrK normr0.
have /allP: {subset kvs <= kvs2} by [].
rewrite cfdot_sumr unlock; elim: kvs s1 s2 => [|[k v2] kvs IHkvs] s1 s2 /=.
  by rewrite addr0 /goal -rmorphB pmulrn -!CintrE.
case/andP=> kvs2_v /IHkvs{IHkvs}IHkvs; have{cl2P} [ltk _] := cl2P _ kvs2_v.
have [v1 /cl1P[_ /eqP/=Dv1] | kvs1'k] := get_litP.
  rewrite addrA => gl12; apply: IHkvs; congr (goal (_ + _) _): gl12.
  by rewrite raddfMz addrC /= Dv1 -mulrzA -rmorphD.
move=> gl12; apply: IHkvs; case: ifP gl12 => [/(norm_cl_eq3 m_th th_cl1)->|_].
  rewrite cfdot_suml big1_seq ?add0r //= => kv1 kvs1_kv1.
  have [[ltk1 _] [/orthonormalP[Um oom] _]] := (cl1P _ kvs1_kv1, RmodelP m).
  rewrite -!scaler_int cfdotZl cfdotZr oom ?mem_nth ?nth_uniq // mulrb.
  by rewrite ifN ?mulr0 //; apply: contraNneq kvs1'k => <-; apply: map_f.
rewrite /goal -(ler_add2r 1) -mulrSr; case: (cl2eq) => //; apply: ler_trans.
set s := '[_, _]; rewrite -[_ + _](addrK s) (ler_trans (ler_norm_sub _ _)) //.
rewrite 2![_ + s]addrAC addrA ler_add2l {}/s -scaler_int cfdotZr rmorph_int.
have [|v1 _] := sat_cases k m_th th_cl1; first exact/andP.
have [th1 -> /= [th1_cl1 _] m_th1] := ext_clP k v1 th_cl1.
have [_ _ /(_ _ (mem_head _ _))[_ /eqP->]] := satP m_th1 _ th1_cl1.
have ubv1: (`|v1| <= 1)%N := norm_lit m_th1 th1_cl1 (mem_head _ _).
have ubv2: (`|v2| <= 1)%N := norm_lit m_th th_cl2 kvs2_v.
by rewrite -rmorphM -intr_norm lern1 abszM /= (leq_mul ubv2 ubv1).
Qed.

(* "Without loss" cut rules. *)

Lemma unsat_wlog cl th :
   (let: Wrap th1 := set_cl cl th in (unsat th1 -> unsat th) /\ unsat th1) ->  
  unsat th.
Proof. by case: set_cl => th1 [Uth /Uth]. Qed.

Lemma unsat_wlog_cases th1 th2 :
  (unsat th1 -> unsat th2) -> unsat th1 -> (true /\ unsat th1) /\ unsat th2.
Proof. by move=> Uth2 Uth1; split; last exact: Uth2. Qed.

(* Extend the orthonormal basis *)

Lemma sat_fill m th cl (k := th_dim th) :
    sat m th -> cl \in th -> wf_fill k cl.2 ->
  exists mr : {CFk | is_Rmodel CFk},
    sat (Model (LmodelP m) (svalP mr)) (unwrap (ext_cl th cl k 1)).
Proof.
move=> m_th th_cl /andP[/eqP sz_kvs n3cl].
wlog sz_m: m m_th / size m = k.
  have lekm: (k <= size m)%N by have [] := and3P m_th.
  have mrP: is_Rmodel (take k m).
    have [] := RmodelP m; rewrite -{1 2}(cat_take_drop k m) orthonormal_cat /=.
    by case/andP=> o1mr _ /allP; rewrite all_cat => /andP[/allP].
  move/(_ (Model (LmodelP m) mrP)); apply; rewrite ?size_takel //.
  congr (_ && _): m_th; rewrite lekm size_takel ?leqnn //=.
  apply: eq_in_all => cl1 /th_dimP lt_cl1; congr (_ && _).
  by apply: eq_in_all => kv1 /lt_cl1 lt_kv1; rewrite /sat_lit nth_take ?lt_kv1.
have [_ _ [//||dk cl_dk o_dk_m]] := norm_clP m_th th_cl.
  by rewrite sz_kvs sz_m.
have CFkP: is_Rmodel (rcons m (dchi dk)).
  have [o1m /allP Zm] := RmodelP m.
  split; last by apply/allP; rewrite all_rcons /= dchi_vchar.
  rewrite -cats1 orthonormal_cat o1m orthogonal_sym o_dk_m.
  by rewrite /orthonormal /= cfnorm_dchi eqxx.
exists (exist _ _ CFkP); set mk := Model _ _.
have{m_th} mk_th: sat mk th.
  congr (_ && _): m_th; rewrite size_rcons sz_m leqnn ltnW //=.
  apply: eq_in_all => cl1 /th_dimP lt_cl1; congr (_ && _).
  apply: eq_in_all => kv1 /lt_cl1 lt_kv1; congr ('[_, _] == _).
  by rewrite nth_rcons sz_m lt_kv1.
have [|{mk_th}v ub_v m_th] := sat_cases k mk_th th_cl.
  rewrite /wf_ext_cl size_rcons sz_m (contraFN _ (ltnn k)) //=.
  by case/mapP=> kv kv_cl {1}->; rewrite (th_dimP _ _ th_cl).
suffices: 0 < v by case/or4P: ub_v m_th => // /eqP->.
case: (ext_clP k v th_cl) m_th => th1 -> [th1_cl1 _] /and3P[_ _].
case/allP/(_ _ th1_cl1)/and3P=> _ /eqP/=.
by rewrite nth_rcons sz_m ltnn eqxx CintrE => <- _; rewrite -dirr_consttE.
Qed.

Lemma unsat_fill ij th :
  let fill_cl cl :=
    if (th_dim th).+1 %/ 1 is k.+1 then
      let: Wrap thk := ext_cl th cl k 1 in wf_fill k cl.2 /\ unsat thk
      else True in
  oapp fill_cl False (get_cl ij th) -> unsat th.
Proof.
rewrite divn1; case: get_clP => //= cl [th_cl _].
case Dthk: ext_cl => [th1] [wf_thk Uth1] m m_th.
by have [mk] := sat_fill m_th th_cl wf_thk; rewrite Dthk => /Uth1.
Qed.

(* Matching an assumption exactly. *)

Lemma sat_exact m th1 th2 : sub_match th1 th2 -> sat m th2 -> sat m th1.
Proof.
move/allP=> s_th12 /satP th2P; apply/satP => cl1 /s_th12/hasP[cl2 th_cl2].
case: eqP => // <- s_cl12; have [wf_ij2 Ucl2 cl2P] := th2P _ th_cl2.
split=> // [|kv /(mem_subseq s_cl12)/cl2P//].
by rewrite (subseq_uniq _  Ucl2) ?map_subseq.
Qed.

Lemma unsat_exact th1 th2 : sub_match th1 th2 -> unsat th1 -> unsat th2.
Proof. by move=> sth21 Uth1 m /(sat_exact sth21)/Uth1. Qed.

(* Transpose (W1 / W2 symmetry). *)

Fact tr_Lmodel_subproof (m : model) : is_Lmodel (tr m) (fun ij => m (tr ij)).
Proof.
case: m => /= d f _ [[odd_d1 odd_d2 d1gt1 d2gt1 neq_d12] Zf fP] _.
split=> // [|[j1 i1] [j2 i2]]; first by rewrite eq_sym. 
by rewrite ![_ \in _]andbC /= => wf_ij1 wf_ij2; rewrite fP // /dot_ref mulnC.
Qed.

Definition tr_model m := Model (tr_Lmodel_subproof m) (RmodelP m).

Lemma sat_tr m th : sat m th -> sat (tr_model m) (tr_th th).
Proof.
move/satP=> thP; apply/satP=> _ /mapP[[[i j] kvs] /thP[m_ij Uks kvsP] ->].
by rewrite inE /= andbC.
Qed.

(* Extend the theory (add a new empty clause). *)

Lemma unsat_consider ij th :
  wf_consider ij th -> unsat (AddClause th (& ? in ij)) -> unsat th.
Proof.
case: ij => i j; case/andP; set sym_t := sub_match _ _ => lti ltj Uthij m m_th.
wlog le_m21: m m_th / sym_t -> (m.2 <= m.1)%N.
  move=> IH; apply: (IH m m_th) => sym_th.
  rewrite leqNgt; apply/negP=> /leqW le_m1_m2.
  by have /(sat_exact sym_th)/IH[] := sat_tr m_th.
apply: (Uthij m); congr (_ && _): (m_th) => /=; case: (th_bbox th) => ri rj /=.
have [[odd_m1 _ m1gt1 m2gt1 neq_m12] _ _] := LmodelP m.
rewrite /sub_bbox !geq_max (leq_trans ltj) ?(leq_trans lti) //; case: orP => //.
rewrite -(ltnS 4) (odd_geq _ odd_m1) ltnS.
case=> [/leq_trans-> // | /le_m21]; first by have [/andP[]] := and3P m_th.
by rewrite leq_eqVlt eq_sym (negPf neq_m12); apply: leq_trans.
Qed.

(* Matching up to a permutation of the rows, columns, and base vectors. *)

Lemma unsat_match s th1 th2 : sym_match s th1 th2 -> unsat th2 -> unsat th1.
Proof.
pose I_ si mi := si ++ filter [predC si] (iota 0 mi).
have SsP mi si ri (Ii := I_ si mi):
    uniq si && all (gtn ri) si -> (ri <= mi)%N ->
  [/\ {in Ii, forall i, i < mi}%N, uniq Ii & size Ii = mi].
- case/andP=> Usi /allP/=ltsi le_ri_mi; have uIm := iota_uniq 0 mi.
  have uIi: uniq Ii by rewrite cat_uniq Usi -all_predC filter_all filter_uniq.
  have defIi: Ii =i iota 0 mi.
    move=> i; rewrite mem_cat mem_filter orb_andr orbN mem_iota.
    by apply: orb_idl => /ltsi/leq_trans->.
  split=> // [i|]; first by rewrite defIi mem_iota.
  by rewrite (perm_eq_size (uniq_perm_eq _ _ defIi)) ?size_iota.
have lt_nth ri si i: (nth ri si i < ri)%N -> (i < size si)%N.
  by rewrite !ltnNge; apply: contra => le_si; rewrite nth_default.
case: s => [si sj sk] /= sym12 Uth2 m m_th1; case/and3P: (m_th1) sym12.
case: th_bbox (th_bboxP (bbox_refl (th_bbox th1))) => ri rj rijP.
case/andP=> /= leri lerj lerk _ /and4P[Ssi Ssj /andP[Usk /allP/=lesrk] sym12].
have{Ssi} /SsP/(_ leri)[ltIi uIi szIi] := Ssi.
have{Ssj SsP} /SsP/(_ lerj)[ltIj uIj szIj] := Ssj.
pose smL ij := m (nth ri (I_ si m.1) ij.1, nth rj (I_ sj m.2) ij.2)%N.
pose smR := [seq m`_k | k <- sk].
have [[lb_m ZmL Dm] [o1m ZmR]] := (LmodelP m, RmodelP m).
have{lb_m} smLP: is_Lmodel m smL.
  split=> // [ij | ij1 ij2 /andP[lti1 ltj1] /andP[lti2 ltj2]]; first exact: ZmL.
  by rewrite Dm ?inE /dot_ref/= ?nth_uniq ?ltIi ?ltIj ?mem_nth ?szIi ?szIj.
have{lesrk} ubk k: k \in sk -> (k < size m)%N by move=> /lesrk/leq_trans->.
have smRP: is_Rmodel smR.
  have ssmR: {subset smR <= (m : seq _)}.
    by move=> _ /mapP[k s_k ->]; rewrite mem_nth ?ubk.
  split=> [|xi /ssmR/ZmR//]; have [Um _] := orthonormalP o1m.
  apply: sub_orthonormal o1m; rewrite ?map_inj_in_uniq //.
  by apply: can_in_inj (index^~ m) _ => k s_k; rewrite /= index_uniq ?ubk.
apply: (Uth2 (Model smLP smRP)); apply/satP=> [][[i2 j2] kvs2] /(allP sym12).
case/andP=> -> /hasP[[[i1 j1] kvs1] th1_cl1 /andP[/eqP[Di1 Dj1] /allP s_kv12]].
have:= rijP _ th1_cl1; rewrite Di1 Dj1 => /andP[/lt_nth lti1 /lt_nth ltj1].
rewrite !inE -szIi -szIj !size_cat !(leq_trans _ (leq_addr _ _)) //.
split=> // kv /s_kv12 kvs1_kv1; rewrite size_map /sat_lit /=.
have /lt_nth ltk := th_dimP (leqnn _) _ th1_cl1 _ kvs1_kv1; split=> //.
rewrite (nth_map (th_dim th1)) // /smL !nth_cat lti1 ltj1 -Di1 -Dj1.
by have [_ _ /(_ _ kvs1_kv1)[]] := satP m_th1 _ th1_cl1.
Qed.

Lemma unsat_sym th1 th2 :
  (if find_sym th1 th2 is Some s then sym_match s th2 th1 else false) ->
  unsat th1 -> unsat th2.
Proof. by case: find_sym => // s; apply: unsat_match. Qed.

End Interpretation.

Implicit Arguments satP [gT G m th].
Implicit Arguments unsat [gT G].
Implicit Arguments sat_cases [gT G m th cl].
Implicit Arguments unsat_cases [gT G th tO].
Implicit Arguments unsat_wlog [gT G].
Implicit Arguments unsat_fill [gT G].
Implicit Arguments unsat_consider [gT G].
Implicit Arguments unsat_match [gT G th1 th2].

(* The domain-specific tactic language. *)

Tactic Notation "consider" constr(ij) :=
  apply: (unsat_consider ij); first exact isT.

(* Note that "split" here would be significantly less efficient, because it   *)
(* would evaluate the reflected assumption four times.                        *)
Tactic Notation "fill" constr(ij) :=
  apply: (unsat_fill ij); apply: (conj isT _).

Tactic Notation "uwlog" simple_intropattern(IH) ":" constr(cl) :=
  apply: (unsat_wlog cl); split=> [IH | ].

Tactic Notation "uwlog" simple_intropattern(IH) ":" constr(cl)
                   "by" tactic4(tac) :=
  apply: (unsat_wlog cl); split=> [IH | ]; first by [tac].

Tactic Notation "uhave" constr(kv) "in" constr(ij)
                   "as" constr(T) constr(ij12) :=
  apply: (unsat_cases ij [:: kv] (T ij12)); apply: (conj isT _).

Tactic Notation "uhave" constr(kv1) "," constr(kv2) "in" constr(ij)
                   "as" constr(T) constr(ij12) :=
  uhave kv1 in ij as T ij12; uhave kv2 in ij as T ij12.

Tactic Notation "uhave" constr(kv1) "|" constr(kv2) "in" constr(ij)
                   "as" constr(T) constr(ij12) :=
  apply: (unsat_cases ij [:: kv1; kv2] (T ij12)); apply: (conj (conj isT _) _).

Tactic Notation "uhave" constr(kv1) "|" constr(kv2) "|" constr(kv3)
                   "in" constr(ij) :=
  apply: (unsat_cases ij [:: kv1; kv2; kv3] (fun _ _ _ => isT));
  apply: (conj (conj (conj isT _) _) _).

Tactic Notation "uwlog" simple_intropattern(IH) ":"
                        constr(kv1) "|" constr(kv2) "in" constr(ij)
                   "as" constr(T) constr(ij12) :=
  apply: (unsat_cases ij [:: kv1; kv2] (T ij12));
  apply: unsat_wlog_cases => [IH | ].

Tactic Notation "counter" "to" constr(T) constr(ij12) := by move=> ? /(T ij12).

Tactic Notation "uexact" constr(IH) := apply: unsat_exact IH; exact isT.

Tactic Notation "symmetric" "to" constr(IH) := apply: unsat_sym (IH); exact isT.

End CyclicTIisoReflexion.

Section Three.

Variables (gT : finGroupType) (G W W1 W2 : {group gT}).
Hypothesis defW : W1 \x W2 = W.

Let V := cyclicTIset defW.
Let w_ i j := cyclicTIirr defW i j.
Let w1 := #|W1|.
Let w2 := #|W2|.

Lemma cyclicTIirrC (xdefW : W2 \x W1 = W) i j :
  cyclicTIirr xdefW j i = w_ i j.
Proof. by rewrite (dprod_IirrC xdefW defW). Qed.

Lemma cycTIirrP chi : chi \in irr W -> {i : Iirr W1 & {j | chi = w_ i j}}.
Proof.
case/irrP/sig_eqW=> k ->{chi}.
by have /codomP/sig_eqW[[i j] ->] := dprod_Iirr_onto defW k; exists i, j.
Qed.

Lemma cycTIirr_aut u i j : w_ (aut_Iirr u i) (aut_Iirr u j) = cfAut u (w_ i j).
Proof. by rewrite /w_ !dprod_IirrE cfAutDprod !aut_IirrE. Qed.

Let sW1W : W1 \subset W. Proof. by have /mulG_sub[] := dprodW defW. Qed.
Let sW2W : W2 \subset W. Proof. by have /mulG_sub[] := dprodW defW. Qed.

Lemma card_cycTIset : #|V| = (w1.-1 * w2.-1)%N.
Proof.
have [_ _ _ tiW12] := dprodP defW.
rewrite cardsD (setIidPr _) ?subUset ?sW1W // cardsU {}tiW12 cards1.
rewrite -(dprod_card defW) -addnBA // -!subn1 -/w1 -/w2 subnDA.
by rewrite mulnBl mulnBr mul1n muln1.
Qed.

Definition cfCyclicTIset i j := cfDprod defW (1 - 'chi_i) (1 - 'chi_j).
Local Notation alpha_ := cfCyclicTIset.

Lemma cycTIirr00 : w_ 0 0 = 1. Proof. by rewrite /w_ dprod_Iirr0 irr0. Qed.
Local Notation w_00 := cycTIirr00.

Lemma cycTIirr_split i j : w_ i j = w_ i 0 * w_ 0 j.
Proof. by rewrite /w_ !dprod_IirrE !irr0 cfDprod_split. Qed.

Lemma cfker_cycTIl j : W1 \subset cfker (w_ 0 j).
Proof. by rewrite /w_ dprod_IirrE irr0 cfDprod_cfun1l cfker_sdprod. Qed.

Lemma cfker_cycTIr i : W2 \subset cfker (w_ i 0).
Proof. by rewrite /w_ dprod_IirrE irr0 cfDprod_cfun1r cfker_sdprod. Qed.

Let cfdot_w i1 j1 i2 j2 : '[w_ i1 j1, w_ i2 j2] = ((i1 == i2) && (j1 == j2))%:R.
Proof. exact: cfdot_dprod_irr. Qed.

Lemma cfCycTI_E i j : alpha_ i j = 1 - w_ i 0 - w_ 0 j + w_ i j.
Proof.
rewrite -w_00 -[w_ i j]opprK /w_ !dprod_IirrE !irr0 -addrA -opprD -!mulrBl.
by rewrite -mulrBr -!rmorphB.
Qed.
Local Notation alphaE := cfCycTI_E.

Lemma cfCycTI_vchar i j : alpha_ i j \in 'Z[irr W].
Proof. by rewrite alphaE rpredD ?rpredB ?rpred1 ?irr_vchar. Qed.

Definition cfCyclicTIsetBase :=
  [seq alpha_ ij.1 ij.2 | ij in setX [set~ 0] [set~ 0]].
Local Notation cfWVbase := cfCyclicTIsetBase.

Let cfdot_alpha_w i1 j1 i2 j2 :
  i2 != 0 -> j2 != 0 -> '[alpha_ i1 j1, w_ i2 j2] = [&& i1 == i2 & j1 == j2]%:R.
Proof.
move=> nzi2 nzj2; rewrite alphaE -w_00 !cfdotDl !cfdotNl !cfdot_w.
by rewrite !(eq_sym 0) (negPf nzi2) (negPf nzj2) /= andbF !subr0 add0r.
Qed.

Let cfdot_alpha_1 i j : i != 0 -> j != 0 -> '[alpha_ i j, 1] = 1.
Proof.
move=> nzi nzj; rewrite alphaE -w_00 !cfdotDl !cfdotNl !cfdot_w.
by rewrite !eqxx andbT /= (negPf nzi) (negPf nzj) addr0 !subr0.
Qed.

Let cfnorm_alpha i j : i != 0 -> j != 0 -> '[alpha_ i j] = 4%:R.
Proof.
move=> nzi nzj; rewrite -[4]/(size [:: 1; - w_ i 0; - w_ 0 j; w_ i j]).
rewrite -cfnorm_orthonormal 3?big_cons ?big_seq1 ?addrA -?alphaE //.
rewrite /orthonormal -w_00 /= !cfdotNl !cfdotNr !opprK !oppr_eq0 !cfnorm_irr.
by rewrite !cfdot_w !eqxx /= !(eq_sym 0) (negPf nzi) (negPf nzj) !eqxx.
Qed.

Lemma cfCycTIbase_free : free cfWVbase.
Proof.
apply/freeP=> s /= s_alpha_0 ij; case def_ij: (enum_val ij) => [i j].
have /andP[nzi nzj]: (i != 0) && (j != 0).
  by rewrite -!in_setC1 -in_setX -def_ij enum_valP.
have:= congr1 (cfdotr (w_ i j)) s_alpha_0; rewrite raddf_sum raddf0 => <-.
rewrite (bigD1 ij) //= nth_image def_ij cfdotZl cfdot_alpha_w // !eqxx mulr1.
rewrite big1 ?addr0 // => ij1; rewrite nth_image -(inj_eq enum_val_inj) def_ij.
case: (enum_val ij1) => i1 j1 /= => ne_ij1_ij.
by rewrite cfdotZl cfdot_alpha_w // mulr_natr mulrb ifN.
Qed.

(* Further results on alpha_ depend on the assumption that W is cyclic. *)

Hypothesis ctiW : cyclicTI_hypothesis G defW.

Let cycW : cyclic W. Proof. by case: ctiW. Qed.
Let oddW : odd #|W|. Proof. by case: ctiW. Qed.
Let tiV : normedTI V G W. Proof. by case: ctiW. Qed.
Let ntV : V != set0. Proof. by case/andP: tiV. Qed.

Lemma cyclicTIhyp_sym (xdefW : W2 \x W1 = W) : cyclicTI_hypothesis G xdefW.
Proof. by split; rewrite // /cyclicTIset setUC. Qed.

Let cycW1 : cyclic W1. Proof. exact: cyclicS cycW. Qed.
Let cycW2 : cyclic W2. Proof. exact: cyclicS cycW. Qed.
Let coW12 : coprime w1 w2. Proof. by rewrite -(cyclic_dprod defW). Qed.

Let Wlin k : 'chi[W]_k \is a linear_char. Proof. exact/irr_cyclic_lin. Qed.
Let W1lin i : 'chi[W1]_i \is a linear_char. Proof. exact/irr_cyclic_lin. Qed.
Let W2lin i : 'chi[W2]_i \is a linear_char. Proof. exact/irr_cyclic_lin. Qed.
Let w_lin i j : w_ i j \is a linear_char. Proof. exact: Wlin. Qed.

Let nirrW1 : #|Iirr W1| = w1. Proof. exact: card_Iirr_cyclic. Qed.
Let nirrW2 : #|Iirr W2| = w2. Proof. exact: card_Iirr_cyclic. Qed.
Let NirrW1 : Nirr W1 = w1. Proof. by rewrite -nirrW1 card_ord. Qed.
Let NirrW2 : Nirr W2 = w2. Proof. by rewrite -nirrW2 card_ord. Qed.

Lemma cycTI_nontrivial : W1 :!=: 1%g /\ W2 :!=: 1%g.
Proof.
apply/andP; rewrite -!cardG_gt1 -!(subn_gt0 1) !subn1 -muln_gt0.
by rewrite -card_cycTIset card_gt0.
Qed.

Let ntW1 : W1 :!=: 1%g. Proof. by case: cycTI_nontrivial. Qed.
Let ntW2 : W2 :!=: 1%g. Proof. by case: cycTI_nontrivial. Qed.
Let oddW1 : odd w1. Proof. exact: oddSg oddW. Qed.
Let oddW2 : odd w2. Proof. exact: oddSg oddW. Qed.
Let w1gt2 : (2 < w1)%N. Proof. by rewrite odd_gt2 ?cardG_gt1. Qed.
Let w2gt2 : (2 < w2)%N. Proof. by rewrite odd_gt2 ?cardG_gt1. Qed.

Let neq_w12 : w1 != w2.
Proof.
by apply: contraTneq coW12 => ->; rewrite /coprime gcdnn -(subnKC w2gt2).
Qed.

Let cWW : abelian W. Proof. exact: cyclic_abelian. Qed.
Let nsVW : V <| W. Proof. by rewrite -sub_abelian_normal ?subsetDl. Qed.
Let sWG : W \subset G. Proof. by have [_ /subsetIP[]] := normedTI_P tiV. Qed.
Let sVG : V \subset G^#. Proof. by rewrite setDSS ?subsetU ?sub1G. Qed.

Let alpha1 i j : alpha_ i j 1%g = 0.
Proof. by rewrite cfDprod1 !cfunE cfun11 lin_char1 // subrr mul0r. Qed.

(* This first part of Peterfalvi (3.4) will be used in (4.10) and (13.9). *)
Lemma cfCycTI_on i j : alpha_ i j \in 'CF(W, V).
Proof.
apply/cfun_onP=> x; rewrite !inE negb_and negbK orbC.
case/or3P => [/cfun0->// | W1x | W2x].
  by rewrite -[x]mulg1 cfDprodE // !cfunE cfun11 lin_char1 ?subrr ?mulr0.
by rewrite -[x]mul1g cfDprodE // !cfunE cfun11 lin_char1 ?subrr ?mul0r.
Qed.

(* This is Peterfalvi (3.4). *)
Lemma cfCycTIbase_basis : basis_of 'CF(W, V) cfWVbase.
Proof.
rewrite basisEfree cfCycTIbase_free /=.
have ->: \dim 'CF(W, V) = #|V| by rewrite dim_cfun_on_abelian ?subsetDl.
rewrite size_tuple cardsX !cardsC1 nirrW1 nirrW2 -card_cycTIset leqnn andbT.
by apply/span_subvP=> _ /imageP[[i j] _ ->]; apply: cfCycTI_on.
Qed.
Local Notation cfWVbasis := cfCycTIbase_basis.

Section CyclicTIisoBasis.

Import CyclicTIisoReflexion ssrint.

Local Notation unsat := (@unsat gT G).
Local Notation O := (@O gT G).
Local Notation "#1" := (inord 1).

(* This is the combinatorial core of Peterfalvi (3.5.2). *)
(* Peterfalvi uses evaluation at 1%g to conclude after the second step; since *)
(* this is not covered by our model, we have used the dot product constraints *)
(* between b12 and b11, b21 instead.                                          *)
Let unsat_J : unsat |= & x1 in b11 & -x1 in b21.
Proof.
uwlog b11x1: (& b11 = x1 + x2 + x3) by do 2!fill b11.
uwlog b21x1: (& b21 = -x1 + x2 + x3) by uhave x2, x3 in b21 as O(21, 11).
consider b12; uhave -x2 | x2 | ~x2 in b12.
- by uhave x1 in b12 as O(12, 11); counter to O(12, 21).
- uhave x1 | ~x1 in b12 as O(12, 21).
    by uhave ~x3 in b12 as O(12, 21); counter to O(12, 11).
  by uhave ~x3 in b12 as O(12, 11); counter to O(12, 21).
uhave x3 | ~x3 in b12 as O(12, 11).
  by uhave x1 in b12 as O(12, 21); counter to O(12, 11).
by uhave x1 in b12 as O(12, 11); counter to O(12, 21).
Qed.

Let unsat_II: unsat |= & x1, x2 in b11 & x1, x2 in b21.
Proof. by fill b11; uhave -x3 in b21 as O(21, 11); symmetric to unsat_J. Qed.

(* This reflects the application of (3.5.2), but only to rule out nonzero     *)
(* components of the first entry that conflict with positive components of    *)
(* the second entry; Otest covers all the other uses of (3.5.2) in the proof. *)
Let Ltest (cl1 cl2 : clause) :=
  let: (i1, j1, kvs1) := cl1 in let: (i2, j2, kvs2) := cl2 in
  let fix loop mm kvs2' :=
    if kvs2' is (k, v2) :: kvs2'' then
      let v1 := odflt 0 (get_lit k kvs1) in
      if (v2 != 1) || (v1 == 0) then loop mm kvs2'' else
      if (v1 != 1) || mm then false else loop true kvs2''
    else true in
  (i1 == i2) (+) (j1 == j2) ==> loop false kvs2.

Let L ij12 : is_sat_test G (sat_test Ltest ij12).
Proof.
apply: sat_testP => m th [[i1 j1] kvs1] [[i2 j2] kvs2] m_th th_cl1 th_cl2.
wlog eq_j: m th i1 i2 j1 j2 m_th th_cl1 th_cl2 / j1 == j2.
  move=> IH; case eq_j: (j1 == j2); first exact: IH m_th th_cl1 th_cl2 eq_j.
  case eq_i: (i1 == i2); last by rewrite /= eq_i eq_j.
  have /(_ (_, _, _)) mem_trt: _ \in tr_th th := map_f _ _.
  by rewrite /= addbC; apply: IH (sat_tr m_th) _ _ eq_i; rewrite ?mem_trt.
apply/implyP; rewrite eq_j addbT => neq_i.
rewrite -[f in f _ kvs2]/(idfun _); set f := idfun _; rewrite /= in f *.
have [/= _ Ukvs2 kvsP] := satP m_th _ th_cl2.
move: Ukvs2; set kvs2' := kvs2; set mm := false.
have /allP: {subset kvs2' <= kvs2} by [].
pose lit12 k := (k, 1) \in kvs1 /\ (k, 1) \in kvs2. 
have: mm -> {k | lit12 k & k \notin unzip1 kvs2'} by [].
elim: kvs2' mm => [|[k v2] kvs2' IH] //= mm mmP /andP[kvs2k /IH{IH}IHkvs].
case/andP=> kvs2'k /IHkvs{IHkvs}IHkvs; case: ifP => [_ | /norP[]].
  by apply/IHkvs=> /mmP[kv kvs12kv /norP[]]; exists kv.
have [v1 /= kvs1k | //] := get_litP; case: eqP => // -> in kvs2k * => _ nz_v1.
case Dbb: (th_bbox th) (th_bboxP (bbox_refl (th_bbox th))) => [ri rj] rijP.
have [/andP[/=lti1r ltj1r] /andP[/=lti2r _]] := (rijP _ th_cl1, rijP _ th_cl2).
have rkP := th_dimP (leqnn _) _ th_cl1;  have /= ltkr := rkP _ kvs1k.
have symP := unsat_match (Sym [:: i2; i1] [:: j1] _) _ _ m m_th.
rewrite /= Dbb lti1r lti2r ltj1r inE eq_sym neq_i /= in symP.
have [Dv1 | v1_neq1] /= := altP eqP; first rewrite Dv1 in kvs1k.
  case: ifP => [/mmP[k0 [kvs1k0 kvs2k0]] | _]; last by apply: IHkvs; exists k.
  case/norP=> k'k0; have [/=] := symP [:: k0; k] _ _ unsat_II.
  rewrite inE k'k0 ltkr (rkP _ kvs1k0) /= andbT; apply/andP; split; apply/hasP.
    by exists (i1, j1, kvs1) => //=; rewrite eqxx kvs1k kvs1k0.
  by exists (i2, j2, kvs2) => //=; rewrite (eqP eq_j) eqxx kvs2k kvs2k0.
have{nz_v1 v1_neq1} Dv1: v1 = -1; last rewrite Dv1 in kvs1k.
  by case: (v1) nz_v1 v1_neq1 (norm_lit m_th th_cl1 kvs1k) => [[|[]] | []].
have[] := symP [:: k] _ _ unsat_J; rewrite /= ltkr !andbT /=; apply/andP; split.
  by apply/hasP; exists (i1, j1, kvs1); rewrite //= eqxx kvs1k.
by apply/hasP; exists (i2, j2, kvs2); rewrite //= (eqP eq_j) eqxx kvs2k.
Qed.

(* This is the combinatorial core of Peterfalvi (3.5.4). *)
(* We have made a few simplifications to the combinatorial analysis in the    *)
(* text: we omit the (unused) step (3.5.4.4) entirely, which lets us inline   *)
(* step (3.5.4.1) in the proof of (3.5.4.2); we clear the assumptions on b31  *)
(* and b32 before the final step (3.5.4.5), exposing a hidden symmetry.       *)
Let unsat_Ii : unsat |= & x1 in b11 & x1 in b21 & ~x1 in b31.
Proof.
uwlog Db11: (& b11 = x1 + x2 + x3) by do 2!fill b11.
uwlog Db21: (& b21 = x1 + x4 + x5).
  by uhave ~x2, ~x3 in b21 as L(21, 11); do 2!fill b21; uexact Db21.
uwlog Db31: (& b31 = x2 + x4 + x6).
  uwlog b31x2: x2 | ~x2 in b31 as L(31, 11).
    by uhave x3 in b31 as O(31, 11); symmetric to b31x2.
  uwlog b31x4: x4 | ~x4 in b31 as L(31, 21).
    by uhave x5 in b31 as O(31, 21); symmetric to b31x4.
  uhave ~x3 in b31 as O(31, 11); uhave ~x5 in b31 as L(31, 21).
  by fill b31; uexact Db31.
consider b41; uwlog b41x1: x1 | ~x1 in b41 as L(41, 11).
  uwlog Db41: (& b41 = x3 + x5 + x6) => [|{b41x1}].
    uhave ~x2 | x2 in b41 as L(41, 11); last symmetric to b41x1.
    uhave ~x4 | x4 in b41 as L(41, 21); last symmetric to b41x1.
    uhave x3 in b41 as O(41, 11); uhave x5 in b41 as O(41, 21).
    by uhave x6 in b41 as O(41, 31); uexact Db41.
  consider b12; uwlog b12x1: x1 | ~x1 in b12 as L(12, 11).
    uhave ~x2 | x2 in b12 as L(12, 11); last symmetric to b12x1.
    by uhave x3 in b12 as O(12, 11); symmetric to b12x1.
  uwlog b12x4: -x4 | ~x4 in b12 as O(12, 21).
    by uhave -x5 in b12 as O(12, 21); symmetric to b12x4.
  uhave ~x2, ~x3 in b12 as L(12, 11); uhave ~x5 in b12 as O(12, 21).
  by uhave x6 in b12 as O(12, 31); counter to O(12, 41).
uwlog Db41: (& b41 = x1 + x6 + x7).
  uhave ~x2, ~x3 in b41 as L(41, 11); uhave ~x4, ~x5 in b41 as L(41, 21).
  by uhave x6 in b41 as O(41, 31); fill b41; uexact Db41.
consider b32; uwlog Db32: (& b32 = x6 - x7 + x8).
  uwlog b32x6: x6 | ~x6 in b32 as L(32, 31).
    uhave ~x2 | x2 in b32 as L(32, 31); last symmetric to b32x6.
    by uhave x4 in b32 as O(32, 31); symmetric to b32x6.
  uhave ~x2, ~x4 in b32 as L(32, 31).
  uhave -x7 | ~x7 in b32 as O(32, 41).
    uhave ~x1 in b32 as O(32, 41); uhave ~x3 in b32 as O(32, 11).
    by uhave ~x5 in b32 as O(32, 21); fill b32; uexact Db32.
  uhave -x1 in b32 as O(32, 41).
  by uhave x3 in b32 as O(32, 11); counter to O(32, 21).
consider b42; uwlog Db42: (& b42 = x6 - x4 + x5).
  uhave ~x6 | x6 in b42 as L(42, 41).
    uhave ~x7 | x7 in b42 as L(42, 41); last counter to O(42, 32).
    uhave x1 in b42 as O(42, 41); uhave x8 in b42 as O(42, 32).
    uhave ~x2 | -x2 in b42 as O(42, 11); last counter to O(42, 21).
    by uhave -x3 in b42 as O(42, 11); counter to O(42, 21).
  uwlog b42x4: -x4 | ~x4 in b42 as O(42, 31).
    by uhave -x2 in b42 as O(42, 31); symmetric to b42x4.
  by uhave ~x1 in b42 as L(42, 41); uhave x5 in b42 as O(42, 21); uexact Db42.
uwlog Db32: (& ? in b32); first uexact Db32.
uwlog Db41: (& ? in b41); first uexact Db41. 
consider b12; uwlog b12x5: x5 | ~x5 in b12 as L(12, 42).
  uhave ~x6 | x6 in b12 as L(12, 42); last by consider b22; symmetric to b12x5.
  uhave -x4 in b12 as O(12, 42); uhave x1 in b12 as O(12, 21).
  by uhave ~x2 in b12 as L(12, 11); counter to O(12, 31).
uhave ~x6 in b12 as L(12, 42); uhave ~x4 in b12 as O(12, 42).
uhave ~x2 in b12 as O(12, 31).
by uhave -x1 in b12 as O(12, 21); counter to L(12, 11).
Qed.

Let unsat_C : unsat |= & x1 in b11 & x1 in b21 & x1 in b12.
Proof.
consider b31; uwlog Db21: (& b21 = x1 + x2 + x3) by do 2!fill b21.
uwlog Db12: (& b12 = x1 - x2 + x4).
  uwlog b21x2: -x2 | ~x2 in b12 as O(12, 21).
    by uhave -x3 in b12 as O(12, 21); symmetric to b21x2.
  by uhave ~x3 in b12 as O(12, 21); fill b12; uexact Db12.
uwlog Db31: (& b31 = x1 - x4 + x5).
  uhave x1 | ~x1 in b31 as L(31, 21); last uexact unsat_Ii.
  uhave ~x2, ~x3 in b31 as L(31, 21).
  by uhave -x4 in b31 as O(31, 12); fill b31; uexact Db31.
consider b41; uhave x1 | ~x1 in b41 as L(41, 21); last symmetric to unsat_Ii.
uhave ~x5 in b41 as L(41, 31); uhave ~x4 in b41 as O(41, 31).
by uhave ~x2 in b41 as L(41, 21); counter to O(41, 12).
Qed.

(* This refinement of Peterfalvi (3.5.4) is the essential part of (3.5.5). *)
Let column_pivot (m : model G) (j0 : 'I_m.2.+1) :
  exists dk, forall (i : 'I_m.1.+1) (j : 'I_m.2.+1),
    j0 != 0 -> i != 0 -> j != 0 -> '[m (i.-1, j.-1), dchi dk] = (j == j0)%:R.
Proof.
pose t_i (i0 i1 : nat) := [eta id with i0 |-> i1, i1 |-> i0].
pose t_ij i0 i1 ij : ref := (t_i i0 i1 ij.1, ij.2).
have t_iK i0 i1: involutive (t_i i0 i1).
  move=> i /=; have [-> | i0'i] := altP (i =P i0).
    by rewrite eqxx; case: eqP.
  by have [-> | /negPf->] := altP (i =P i1); rewrite ?eqxx // ifN.
have lt_t_i i0 i1 ri i: (i0 <= i1 < ri)%N -> (t_i i0 i1 i < ri)%N = (i < ri)%N.
  case/andP=> le_i01 lti1 /=.
  by do 2?case: eqP => [-> | _] //; rewrite ?(leq_trans _ lti1).
have t_mP i0 i1 (m0 : model G):
  (i0 <= i1 < m0.1)%N -> is_Lmodel m0 (m0 \o t_ij i0 i1).
- have [lbm0 Zm0 Dm0] := LmodelP m0; split=> //= ij1 ij2 wf_ij1 wf_ij2.
  by rewrite Dm0 /dot_ref ?(can_eq (t_iK _ _)) // !inE ?lt_t_i.
pose t_m i0 i1 m0 lti01 := Model (t_mP i0 i1 m0 lti01) (RmodelP m0).
without loss suffices{j0 lt_t_i} IHm: m /
  exists dk, {in wf_ref m, forall ij, '[m ij, dchi dk] = (ij.2 == 0%N)%:R}.
- have [_ | nzj0] := altP eqP; first by exists (dirr1 G).
  have ltj0: (j0.-1 < m.2)%N by rewrite prednK ?lt0n ?leq_ord.
  have{IHm} [dk Ddk] := IHm (tr_model (t_m 0%N j0.-1 (tr_model m) ltj0)).
  exists dk => i j _ nzi nzj; rewrite -[j.-1](t_iK 0%N j0.-1).
  rewrite (Ddk (_, _)) ?inE ?lt_t_i // ?prednK ?lt0n ?leq_ord //.
  by rewrite (inv_eq (t_iK _ _)) -eqSS !prednK ?lt0n.
pose cl11 := & b11 = x1 + x2 + x3.
without loss m_th: m / sat m |= cl11 & ? in b21.
  move=> IHm; suffices{IHm}: sat m |= & ? in b11 & ? in b21.
    have fill_b11 := sat_fill _ (mem_nth cl11 (_ : 1 < _))%N.
    by do 3![case/fill_b11=> // ?]; apply: IHm.
  have [[_ _ m1gt2 /ltnW m2gt0 _] _ _] := LmodelP m.
  by rewrite /sat /= -!andbA /= m2gt0 -(subnKC m1gt2).
without loss{m_th} m_th: m / sat m |= & x1 in b11 & x1 in b21.
  pose sat123P := @allP _ (fun k => sat_lit m _ (k, _)) (rev (iota 0 3)).
  have [m123 | ] := altP (sat123P b21 0).
    suffices: sat m |= cl11 & ~x1, ~x2, ~x3 in b21 by move/(O(21, 11)).
    by rewrite /sat /= {1}/sat_cl /= !m123.
  case/allPn=> k k012 /negP nz_m21 IHm; rewrite -[sat_lit _ _ _]andbT in nz_m21.
  have ltk3: (k < 3)%N by rewrite mem_rev mem_iota in k012.
  have [[/andP[/allP/=n1m _] Zm] [_ /= m_gt2 _]] := (RmodelP m, and3P m_th).
  have ltk := leq_trans ltk3 m_gt2.
  have{n1m Zm} mkP: is_Rmodel [:: m`_k].
    by split=> [|_ /predU1P[->|//]]; rewrite /orthonormal /= ?n1m ?Zm ?mem_nth.
  pose mk := Model (LmodelP m) mkP; apply: {IHm}(IHm mk).
  have{m_th} [v lit_v m_th] := sat_cases k m_th (mem_head _ _) ltk.
  suffices: sat mk |= & x1 in b11 & (Lit 1 v) in b21.
    by case/or4P: lit_v m_th => // /eqP-> => [/and4P[] | | _ /(L(21,11))].
  have [m_bb _ m_b21 /sat123P m_b11 _] := and5P m_th.
  by apply/and5P; split; rewrite // /sat_cl /= [sat_lit _ _ _]m_b11.
have /dIrrP[dk Ddk]: m`_0 \in dirr G.
  have [[/andP[/allP n1m _] Zm] [_ m_gt0 _]] := (RmodelP m, and3P m_th).
  by rewrite dirrE Zm ?[_ == 1]n1m ?mem_nth.
exists dk => [][i j] /andP[/= lti ltj]; apply/eqP.
suffices{dk Ddk}: sat_cl m (& (Lit 1 (j == 0))%N in (i, j)).
  by rewrite /sat_cl /= andbT /sat_lit Ddk.
without loss{i lti} ->: m i ltj m_th / i = 0%N.
  have [bb21_m m_gt0 m11_x1 m21_x1 _] := and5P m_th.
  move=> IHi; suffices{IHi} m_i1_x1: sat_lit m (i, 0)%N x1 && true.
    apply: (IHi (t_m 0%N i m lti) 0%N); rewrite /sat /sat_cl //= bb21_m m_gt0.
    by rewrite /= m_i1_x1 /sat_lit /= andbT /t_ij /=; case: ifP.
  case i_gt1: (1 < i)%N; last by case: (i) i_gt1 => [|[|[]]].
  have itv_i: (1 < i < m.1)%N by [apply/andP]; pose m2 := t_m 2 i m itv_i.
  have m2_th: sat m2 |= & x1 in b11 & x1 in b21 & ? in b31.
    rewrite /sat m_gt0 -andbA (leq_trans _ lti) ?(leq_trans _ ltj) /sat_cl //=.
    by rewrite /sat_lit /= -(subnKC i_gt1); have [_ _] := and3P m_th.
  have [v] := sat_cases _ m2_th (mem_head _ _) m_gt0; rewrite !inE.
  by case/or3P=> /eqP-> => [/unsat_Ii | /and4P[] | /(L(31,11))].
have [-> | nzj] := posnP j; first by case/and5P: m_th.
without loss{ltj nzj} ->: m j m_th / j = 1%N.
  have itv_j: (0 < j < m.2)%N by rewrite nzj.
  move/(_ (tr_model (t_m _ j (tr_model m) itv_j)) _ _ (erefl _)) => /=.
  by rewrite /sat /sat_cl /sat_lit /= -(prednK nzj) => ->.
have{m_th}[/= _ m_gt0 m_x1] := and3P m_th.
have{m_x1} m_th: sat m |= & x1 in b11 & x1 in b21 & ? in b12.
  by rewrite /sat m_gt0 /sub_bbox; have [[_ _ -> ->]] := LmodelP m.
have [v] := sat_cases 0%N m_th (mem_head _ _) m_gt0; rewrite !inE.
by case/or3P=> /eqP-> => [/and4P[] | /unsat_C | /(L(12,11))].
Qed.

(* This is Peterfalvi (3.5). *)
(* We have inlined part of the proof of (3.5.5) in this main proof, replacing *)
(* some combinatorial arguments with direct computation of the dot product,   *)
(* this avoids the duplicate case analysis required to exploit (3.5.5) as it  *)
(* is stated in the text.                                                     *)
Lemma cyclicTIiso_basis_exists :
 exists xi_ : Iirr W1 -> Iirr W2 -> 'CF(G),
   [/\ xi_ 0 0 = 1, forall i j, xi_ i j \in 'Z[irr G],
       forall i j, i != 0 -> j != 0 -> 
         'Ind (alpha_ i j) = 1 - xi_ i 0 - xi_ 0 j + xi_ i j
     & forall i1 j1 i2 j2, '[xi_ i1 j1, xi_ i2 j2] = ((i1, j1) == (i2, j2))%:R].
Proof.
(* Instantiate the abstract theory vertically and horizontally. *)
pose beta i j : 'CF(G) := 'Ind[G] (alpha_ i j) - 1.
have Zbeta i j: beta i j \in 'Z[irr G].
  by rewrite rpredB ?rpred1 ?cfInd_vchar ?cfCycTI_vchar.
have o_alphaG_1 i j: i != 0 -> j != 0 -> '['Ind[G] (alpha_ i j), 1] = 1.
  by move=> nz_i nz_j; rewrite -cfdot_Res_r rmorph1 cfdot_alpha_1.
have o_beta_1 i j: i != 0 -> j != 0 -> '[beta i j, 1] = 0.
  by move=> nzi nzj; rewrite cfdotBl o_alphaG_1 // cfnorm1 subrr.
have o_beta i1 j1 i2 j2 : i1 != 0 -> j1 != 0 -> i2 != 0 -> j2 != 0 ->
  '[beta i1 j1, beta i2 j2] = ((i1 == i2).+1 * (j1 == j2).+1 - 1)%:R.
- move=> nzi1 nzj1 nzi2 nzj2; rewrite mulSnr addnS mulnSr /=.
  rewrite cfdotBr o_beta_1 // subr0 cfdotBl (cfdotC 1) o_alphaG_1 //.
  rewrite (normedTI_isometry tiV) ?cfCycTI_on // rmorph1 addrC.
  rewrite (alphaE i2) cfdotDr !cfdotBr cfdot_alpha_1 // -!addrA addKr addrA.
  rewrite addrC cfdot_alpha_w // subn1 -addnA !natrD mulnb; congr (_ + _).
  rewrite alphaE -w_00 !(cfdotBl, cfdotDl) !cfdot_w !eqxx !(eq_sym 0).
  rewrite (negPf nzi1) (negPf nzj1) (negPf nzi2) (negPf nzj2) /= !andbF !andbT.
  by rewrite !addr0 !subr0 !opprB !subr0.
pose beta_fun := [fun ij => beta (inord ij.1.+1) (inord ij.2.+1)].
have beta_modelP: is_Lmodel ((Nirr W1).-1, (Nirr W2).-1) beta_fun.
  split=> [ | //= | ij1 ij2 /=/andP[lti1 ltj1] /andP[lti2 ltj2]].
    by rewrite -!(ltnS 2) -eqSS NirrW1 NirrW2.
  by rewrite o_beta -?val_eqE /= ?inordK.
pose beta_model := Model beta_modelP (nil_RmodelP G).
have betaE i j: i != 0 -> j != 0 -> beta i j = beta_fun (i.-1, j.-1).
  by move=> nzi nzj /=; rewrite !prednK ?lt0n ?inord_val.
have /fin_all_exists [dXi0 betaXi0] i0: exists dX, i0 != 0 ->
  forall i j, i != 0 -> j != 0 -> '[beta i j, dchi dX] = (i == i0)%:R.
- have [/= dX DdX] := @column_pivot (tr_model beta_model) i0.
  by exists dX => nzi0 i j nzi nzj; rewrite betaE ?DdX.
have /fin_all_exists [dX0j betaX0j] j0: exists dX, j0 != 0 ->
  forall i j, i != 0 -> j != 0 -> '[beta i j, dchi dX] = (j == j0)%:R.
- have [dX DdX] := @column_pivot beta_model j0.
  by exists dX => nzj0 i j nzi nzj; rewrite betaE ?DdX.
pose Xi0 j := dchi (dXi0 j); pose X0j i := dchi (dX0j i).
(* Construct the orthonormal family xi_ i j. *)
pose xi_ i j := if i == 0 then if j == 0 then 1 else - X0j j else
                if j == 0 then - Xi0 i else beta i j - Xi0 i - X0j j.
exists xi_; split=> [| i j | i j nzi nzj | i1 j1 i2 j2].
- by rewrite /xi_ !eqxx.
- rewrite /xi_; do 2!case: ifP => _; rewrite ?rpred1 ?rpredN ?dchi_vchar //.
  by rewrite 2?rpredB ?dchi_vchar.
- by rewrite /xi_ /= !ifN // addrCA subrK addrACA subrK addrA addrK.
have o_dchi i j dk1 dk2 (phi := beta i j):
  '[phi, dchi dk1] = 1 -> '[phi, dchi dk2] = 0 -> '[dchi dk1, dchi dk2] = 0.
- move=> phi1 phi0; have /eqP: 1 != 0 :> algC := oner_neq0 _.
  rewrite -phi1 cfdot_dchi; do 2!case: eqP => [->|_]; rewrite ?subrr //.
  by rewrite dchi_ndirrE cfdotNr phi0 oppr0.
have [nzi01 nzj01] := (Iirr1_neq0 ntW1, Iirr1_neq0 ntW2).
have X0j_1 j: j != 0 -> '[X0j j, 1] = 0.
  by move=> nzj; rewrite -dchi1 (o_dchi #1 j) ?betaX0j ?eqxx ?dchi1 ?o_beta_1.
have Xi0_1 i: i != 0 -> '[Xi0 i, 1] = 0.
  by move=> nzi; rewrite -dchi1 (o_dchi i #1) ?betaXi0 ?eqxx ?dchi1 ?o_beta_1.
have Xi0_X0j i j: i != 0 -> j != 0 -> '[Xi0 i, X0j j] = 0.
  move=> nzi nzj; pose j' := conjC_Iirr j.
  apply: (o_dchi i j'); rewrite (betaX0j, betaXi0) ?conjC_Iirr_eq0 ?eqxx //.
  by rewrite -(inj_eq irr_inj) conjC_IirrE mulrb ifN ?odd_eq_conj_irr1 ?irr_eq1.
have X0j_X0j j j0: j != 0 -> j0 != 0 -> '[X0j j, X0j j0] = (j == j0)%:R.
  move=> nzj nzj0; case: (altP eqP) => [-> | j0'j]; first exact: cfnorm_dchi.
  by apply: (o_dchi #1 j); rewrite ?betaX0j ?eqxx ?(negPf j0'j).
have Xi0_Xi0 i i0: i != 0 -> i0 != 0 -> '[Xi0 i, Xi0 i0] = (i == i0)%:R.
  move=> nzi nzi0; case: (altP eqP) => [-> | i0'i]; first exact: cfnorm_dchi.
  by apply: (o_dchi i #1); rewrite ?betaXi0 ?eqxx ?(negPf i0'i).
have oxi_00 i j: '[xi_ i j, xi_ 0 0] = ((i == 0) && (j == 0))%:R.
  rewrite /xi_; case: ifPn => [_ | nzi].
    by case: ifPn => [_ | nzj]; rewrite ?cfnorm1 // cfdotNl X0j_1 ?oppr0.
  case: ifPn => [_ | nzj]; first by rewrite cfdotNl Xi0_1 ?oppr0.
  by rewrite 2!cfdotBl o_beta_1 ?X0j_1 ?Xi0_1 ?subr0.
have oxi_0j i j j0: '[xi_ i j, xi_ 0 j0] = ((i == 0) && (j == j0))%:R.
  rewrite /xi_; have [-> | nzj0] := altP (j0 =P 0); first exact: oxi_00.
  rewrite cfdotNr; case: ifPn => [_ | nzi].
    have [-> | nzj] := altP eqP; last by rewrite cfdotNl opprK X0j_X0j.
    by rewrite cfdotC X0j_1 // conjC0 oppr0 mulrb ifN_eqC.
  have [_ | nzj] := ifPn; first by rewrite cfdotNl Xi0_X0j ?oppr0.
  by rewrite 2!cfdotBl Xi0_X0j // subr0 betaX0j ?X0j_X0j // subrr oppr0.
have{oxi_00} oxi_i0 i j i0: '[xi_ i j, xi_ i0 0] = ((i == i0) && (j == 0))%:R.
  rewrite /xi_; have [-> | nzi0] := altP (i0 =P 0); first exact: oxi_00.
  rewrite cfdotNr andbC; have [_ | nzj] := boolP (j == 0).
    have [-> | nzi] := altP eqP; last by rewrite cfdotNl opprK Xi0_Xi0.
    by rewrite cfdotC Xi0_1 // conjC0 oppr0 mulrb ifN_eqC.
  have [_ | nzi] := ifPn; first by rewrite cfdotNl opprK cfdotC Xi0_X0j ?conjC0.
  rewrite 2!cfdotBl betaXi0 ?Xi0_Xi0 // subrr add0r opprK.
  by rewrite cfdotC Xi0_X0j // conjC0.
have [-> | nzi2] := altP (i2 =P 0); first exact: oxi_0j.
have [-> | nzj2] := altP (j2 =P 0); first exact: oxi_i0.
rewrite cfdotC eq_sym; apply: canLR conjCK _; rewrite rmorph_nat.
have [-> | nzi1] := altP (i1 =P 0); first exact: oxi_0j.
have [-> | nzj1] := altP (j1 =P 0); first exact: oxi_i0.
have ->: xi_ i1 j1 = beta i1 j1 + xi_ i1 0 + xi_ 0 j1 by rewrite /xi_ !ifN.
rewrite 2!cfdotDr oxi_i0 oxi_0j andbC /xi_ (negPf nzi2) (negPf nzj2) !addr0.
rewrite eq_sym xpair_eqE cfdotC 2!cfdotBr o_beta // betaXi0 ?betaX0j //.
by rewrite -!CintrE /= rmorph_int; do 2!case: (_ == _).
Qed.

End CyclicTIisoBasis.

(* This is PeterFalvi, Theorem (3.2)(a, b, c). *)
Theorem cyclicTIiso_exists :
  {sigma : 'Hom(cfun_vectType W, cfun_vectType G) |
    [/\ {in 'Z[irr W], isometry sigma, to 'Z[irr G]}, sigma 1 = 1
      & {in 'CF(W, V), forall phi : 'CF(W), sigma phi = 'Ind[G] phi}]}.
Proof.
pose sigmaVP f := ('CF(W, V) <= lker (linfun f - linfun 'Ind[G]))%VS.
pose sigmaP f := [&& orthonormal (map f (irr W)), f 1 == 1 & sigmaVP f].
pose sigma_base f := [seq (dchi (f k) : 'CF(G)) | k : Iirr W].
pose sigma_spec f := sigmaP (sval (linear_of_free (irr W) (sigma_base f))).
suffices /sigW[f /and3P[]]: exists f : {ffun _}, sigma_spec f.
  case: linear_of_free => /=sigma Dsigma o1sigma /eqP sigma1 /eqlfun_inP sigmaV.
  exists (linfun sigma); split=> [|| phi /sigmaV]; try by rewrite !lfunE.
  do [rewrite size_map !size_tuple => /(_ (irr_free W) (card_ord _))] in Dsigma.
  have [inj_sigma dot_sigma] := orthonormalP o1sigma.
  rewrite -(map_tnth_enum (irr W)) -map_comp in Dsigma inj_sigma.
  move/eq_in_map in Dsigma; move/injectiveP in inj_sigma.
  split=> [|_ /zchar_tuple_expansion[z Zz ->]].
    apply: isometry_in_zchar=> _ _ /irrP[k1 ->] /irrP[k2 ->] /=.
    by rewrite !lfunE dot_sigma ?map_f ?mem_irr // cfdot_irr (inj_eq inj_sigma).
  rewrite linear_sum rpred_sum // => k _; rewrite linearZ rpredZ_Cint //=.
  by rewrite -tnth_nth lfunE [sigma _]Dsigma ?mem_enum ?dchi_vchar.
have [xi_ [xi00 Zxi Dxi o1xi]] := cyclicTIiso_basis_exists.
pose f := [ffun k => dirr_dIirr (prod_curry xi_) (inv_dprod_Iirr defW k)].
exists f; apply/and3P; case: linear_of_free => /= sigma Dsigma.
have{f Dsigma} Deta i j: sigma (w_ i j) = xi_ i j.
  rewrite /w_ -tnth_map /= (tnth_nth 0) /=.
  rewrite Dsigma ?irr_free //; last by rewrite !size_tuple card_ord.
  rewrite nth_mktuple ffunE dprod_IirrK dirr_dIirrE // => {i j} [[i j]] /=.
  by rewrite dirrE Zxi o1xi !eqxx.
have sigma1: sigma 1 = 1 by rewrite -w_00 Deta.
rewrite sigma1 /sigmaVP -(span_basis cfWVbasis); split=> //.
  rewrite map_orthonormal ?irr_orthonormal //; apply: isometry_in_zchar.
  move=> _ _ /cycTIirrP[i1 [j1 ->]] /cycTIirrP[i2 [j2 ->]] /=.
  by rewrite !Deta o1xi cfdot_w.
apply/span_subvP=> _ /imageP[[i j] /setXP[nzi nzj] ->]; rewrite !inE in nzi nzj.
rewrite memv_ker !lfun_simp /= subr_eq0 Dxi //.
by rewrite alphaE linearD !linearB sigma1 !Deta.
Qed.

Fact cyclicTIiso_key : unit. Proof. by []. Qed.
Definition cyclicTIiso :=
  locked_with cyclicTIiso_key (lfun_linear (sval cyclicTIiso_exists)).
Local Notation sigma := cyclicTIiso.
Let im_sigma := map sigma (irr W).
Let eta_ i j := sigma (w_ i j).

Lemma cycTI_Zisometry : {in 'Z[irr W], isometry sigma, to 'Z[irr G]}.
Proof. by rewrite [sigma]unlock; case: cyclicTIiso_exists => ? []. Qed.

Let Isigma : {in 'Z[irr W] &, isometry sigma}.
Proof. by case: cycTI_Zisometry. Qed.
Let Zsigma : {in 'Z[irr W], forall phi, sigma phi \in 'Z[irr G]}.
Proof. by case: cycTI_Zisometry. Qed.

Lemma cycTIisometry : isometry sigma.
Proof.
move=> phi psi; have [[a ->] [b ->]] := (cfun_irr_sum phi, cfun_irr_sum psi).
rewrite !linear_sum !cfdot_suml; apply: eq_bigr => i _.
rewrite !cfdot_sumr; apply: eq_bigr => j _.
by rewrite !linearZ !cfdotZl !cfdotZr /= Isigma ?irr_vchar.
Qed.

Lemma cycTIiso_vchar i j : eta_ i j \in 'Z[irr G].
Proof. by rewrite Zsigma ?irr_vchar. Qed.

Lemma cfdot_cycTIiso i1 i2 j1 j2 : 
  '[eta_ i1 j1, eta_ i2 j2] = ((i1 == i2) && (j1 == j2))%:R.
Proof. by rewrite cycTIisometry. Qed.

Lemma cfnorm_cycTIiso i j : '[eta_ i j] = 1.
Proof. by rewrite cycTIisometry cfnorm_irr. Qed.

Lemma cycTIiso_dirr i j : eta_ i j \in dirr G.
Proof. by rewrite dirrE cycTIiso_vchar /= cfnorm_cycTIiso. Qed.

Lemma cycTIiso_orthonormal : orthonormal im_sigma.
Proof. by rewrite map_orthonormal ?irr_orthonormal. Qed.

Lemma cycTIiso_eqE i1 i2 j1 j2 :
  (eta_ i1 j1 == eta_ i2 j2) = ((i1 == i2) && (j1 == j2)).
Proof.
have /inj_in_eq-> := Zisometry_inj Isigma; try exact: irr_vchar.
by rewrite (inj_eq irr_inj) (inj_eq (dprod_Iirr_inj _)).
Qed.

Lemma cycTIiso_neqN i1 i2 j1 j2 : (eta_ i1 j1 == - eta_ i2 j2) = false.
Proof.
rewrite -addr_eq0; apply/eqP=> /(congr1 (cfdot (eta_ i1 j1)))/eqP.
by rewrite cfdot0r cfdotDr !cfdot_cycTIiso !eqxx -mulrS pnatr_eq0.
Qed.

Lemma cycTIiso1 : sigma 1 = 1.
Proof. by rewrite [sigma]unlock; case: cyclicTIiso_exists => ? []. Qed.

Lemma cycTIiso_Ind : {in 'CF(W, V), forall phi, sigma phi = 'Ind[G, W] phi}.
Proof. by rewrite [sigma]unlock; case: cyclicTIiso_exists => ? []. Qed.

Let sigma_Res_V :
  [/\ forall phi, {in V, sigma phi =1 phi}
    & forall psi : 'CF(G), orthogonal psi im_sigma -> {in V, psi =1 \0}].
Proof.
have sigW i j : '[sigma 'chi_i, sigma 'chi_j] = (i == j)%:R.
  by rewrite cycTIisometry cfdot_irr.
have [j | sigmaV sigma'V] := equiv_restrict_compl_ortho sWG nsVW cfWVbasis sigW.
  rewrite /= -/cfWVbase -(eq_bigr _ (fun _ _ => linearZ _ _)) /= -linear_sum.
  rewrite -cfun_sum_cfdot cycTIiso_Ind //.
  by rewrite (basis_mem cfWVbasis) ?mem_nth ?size_image.
split=> [phi v Vv | psi /orthoPl o_psi_sigma].
  rewrite [phi]cfun_sum_cfdot linear_sum !sum_cfunE.
  by apply: eq_bigr => k _; rewrite linearZ !cfunE sigmaV.
by apply: sigma'V => k; rewrite o_psi_sigma ?map_f ?mem_irr.
Qed.

(* This is Peterfalvi, Theorem (3.2)(d). *)
Theorem cycTIiso_restrict phi : {in V, sigma phi =1 phi}.
Proof. by case: sigma_Res_V. Qed.

(* This is Peterfalvi, Theorem (3.2)(e). *)
Theorem ortho_cycTIiso_vanish (psi : 'CF(G)) : 
  orthogonal psi im_sigma -> {in V, forall x, psi x = 0}.
Proof. by case: sigma_Res_V psi. Qed.

(* This is PeterFalvi (3.7). *)
Lemma cycTIiso_cfdot_exchange (psi : 'CF(G)) i1 i2 j1 j2 :
    {in V, forall x, psi x = 0} -> 
  '[psi, eta_ i1 j1] + '[psi, eta_ i2 j2]
     = '[psi, eta_ i1 j2] + '[psi, eta_ i2 j1].
Proof.
move=> psiV_0; pose phi : 'CF(W) := w_ i1 j1 + w_ i2 j2 - w_ i1 j2 - w_ i2 j1.
have Vphi: phi \in 'CF(W, V).
  apply/cfun_onP=> g; rewrite inE negb_and negbK !inE orbC.
  case/or3P=> [/cfun0-> // | W1g | W2g]; apply/eqP; rewrite !cfunE subr_eq0.
    by rewrite addrC -[g]mulg1 /w_ !dprod_IirrE !cfDprodE ?lin_char1 ?addKr.
  by rewrite -[g]mul1g /w_ !dprod_IirrE !cfDprodE ?lin_char1 ?addrK.
suffices: '[psi, 'Ind[G] phi] == 0.
  rewrite -!cycTIiso_Ind // !linearB !linearD !cfdotBr !cfdotDr.
  by rewrite -addrA -opprD subr_eq0 => /eqP.
rewrite (cfdotEr _ (cfInd_on sWG Vphi)) big1 ?mulr0 //.
by move=> _ /imset2P[x y Vx Gy ->]; rewrite cfunJ ?psiV_0 ?mul0r.
Qed.

(* This is NC as defined in PeterFalvi (3.6). *)
Definition cyclicTI_NC phi := #|[set ij | '[phi, eta_ ij.1 ij.2] != 0]|.
Local Notation NC := cyclicTI_NC.

Lemma cycTI_NC_opp (phi : 'CF(G)) : (NC (- phi)%R = NC phi)%N.
Proof. by apply: eq_card=> [[i j]]; rewrite !inE cfdotNl oppr_eq0. Qed.

Lemma cycTI_NC_sign (phi : 'CF(G)) n : (NC ((-1) ^+ n *: phi)%R = NC phi)%N.
Proof. 
elim: n=> [|n IH]; rewrite ?(expr0,scale1r) //.
by rewrite exprS -scalerA scaleN1r cycTI_NC_opp.
Qed.

Lemma cycTI_NC_iso i j : NC (eta_ i j) = 1%N.
Proof.
rewrite -(cards1 (i, j)); apply: eq_card => [[i1 j1]]; rewrite !inE /=.
rewrite cfdot_cycTIiso //= pnatr_eq0 (can_eq oddb _ false) eqbF_neg negbK.
by rewrite -xpair_eqE eq_sym.
Qed.

Lemma cycTI_NC_irr i : (NC 'chi_i <= 1)%N.
Proof.
apply: wlog_neg; rewrite -ltnNge => /ltnW/card_gt0P[[i1 j1]].
rewrite inE cfdot_dirr ?(irr_dirr, cycTIiso_dirr) //=.
case: ('chi_i =P _) => [-> | _]; first by rewrite cycTI_NC_opp cycTI_NC_iso.
by case: ('chi_i =P _)=> [-> | _]; rewrite (cycTI_NC_iso, eqxx).
Qed.

Lemma cycTI_NC_dirr f : f \in dirr G -> (NC f <= 1)%N.
Proof. by case/dirrP=> b [i ->]; rewrite cycTI_NC_sign cycTI_NC_irr. Qed.

Lemma cycTI_NC_dchi di : (NC (dchi di) <= 1)%N.
Proof. by rewrite cycTI_NC_dirr ?dirr_dchi. Qed.

Lemma cycTI_NC_0 : NC 0 = 0%N.
Proof. by apply: eq_card0 => ij; rewrite !inE cfdot0l eqxx. Qed.

Lemma cycTI_NC_add n1 n2 phi1 phi2 :
  (NC phi1 <= n1 -> NC phi2 <= n2 -> NC (phi1 + phi2)%R <= n1 + n2)%N.
Proof.
move=> ub1 ub2; apply: leq_trans {ub1 ub2}(leq_add ub1 ub2).
rewrite -cardsUI -[NC _]addn0 leq_add // subset_leq_card //.
apply/subsetP=> [[i j]]; rewrite !inE /= -negb_and cfdotDl.
by apply: contra => /andP[/eqP-> /eqP->]; rewrite addr0.
Qed.

Lemma cycTI_NC_sub n1 n2 phi1 phi2 :
  (NC phi1 <= n1 -> NC phi2 <= n2 -> NC (phi1 - phi2)%R <= n1 + n2)%N.
Proof. by move=> ub1 ub2; rewrite cycTI_NC_add ?cycTI_NC_opp. Qed. 

Lemma cycTI_NC_scale_nz a phi : a != 0 -> NC (a *: phi) = NC phi.
Proof.
move=> nz_a; apply: eq_card => ij.
by rewrite !inE cfdotZl mulf_eq0 negb_or nz_a.
Qed.

Lemma cycTI_NC_scale a phi n : (NC phi <= n -> NC (a *: phi) <= n)%N.
Proof.
have [-> _ | /cycTI_NC_scale_nz-> //] := eqVneq a 0.
by rewrite scale0r cycTI_NC_0.
Qed.

Lemma cycTI_NC_norm phi n :
  phi \in 'Z[irr G] -> '[phi] <= n%:R -> (NC phi <= n)%N.
Proof.
move=> Zphi ub_phi; apply: leq_trans (_ : #|dirr_constt phi| <= n)%N.
  rewrite {1}[phi]cfun_sum_dconstt // -sum1_card.
  elim/big_rec2: _ => [|/= i n1 phi1 _]; first by rewrite cycTI_NC_0.
  by apply: cycTI_NC_add; rewrite cycTI_NC_scale ?cycTI_NC_dchi.
rewrite -leC_nat (ler_trans _ ub_phi) ?cnorm_dconstt // -sumr_const.
apply: ler_sum => i phi_i; rewrite sqr_Cint_ge1 ?Cint_Cnat ?Cnat_dirr //.
by rewrite gtr_eqF -?dirr_consttE.
Qed.

(* This is PeterFalvi (3.8). *)
Lemma small_cycTI_NC phi i0 j0 (a0 := '[phi, eta_ i0 j0]) : 
    {in V, forall x, phi x = 0} -> (NC phi < 2 * minn w1 w2)%N -> a0 != 0 ->    
     (forall i j, '[phi, eta_ i j] = (j == j0)%:R * a0)
  \/ (forall i j, '[phi, eta_ i j] = (i == i0)%:R * a0).
Proof.
pose a i j := '[phi, eta_ i j]; pose A := [set ij | a ij.1 ij.2 != 0].
rewrite -[NC phi]/#|A| ltnNge => phiV_0 ubA nz_a0.
have{phiV_0} Da i2 j2 i1 j1 : a i1 j1 = a i1 j2 + a i2 j1 - a i2 j2.
  by rewrite cycTIiso_cfdot_exchange ?addrK.
have ubA2: ~~ (w2 + w1 <= #|A| + 2)%N.
  rewrite addnC addn2 -ltnS (contra _ ubA) //; apply: (@leq_trans _ _.+3).
  rewrite odd_geq /= ?odd_add ?oddW1 ?oddW2 // mul2n -addn_min_max -addnn.
  by rewrite uphalf_double leq_add2l gtn_min !leq_max !ltnn orbF -neq_ltn.
(* This is step (3.8.1). *)
have Za i1 i2 j1 j2 : a i1 j2 == 0 -> a i2 j1 == 0 -> a i1 j1 == 0.
  have [-> // | /negPf i2'1 /eqP Za12 /eqP Za21] := eqVneq i1 i2.
  apply: contraR ubA2 => nz_a11.
  pose L := [set (if a i1 j == 0 then i2 else i1, j) | j : Iirr W2].
  pose C := [set (i, if a i j1 == 0 then j2 else j1) | i : Iirr W1].
  have [<- <-]: #|L| = w2 /\ #|C| = w1 by rewrite !card_imset // => ? ? [].
  have <-: #|[set (i1, j1); (i2, j2)]| = 2 by rewrite cards2 xpair_eqE i2'1.
  rewrite -cardsUI leq_add ?subset_leq_card //; last first.
    apply/subsetP=> _ /setIP[/imsetP[j _ ->] /imsetP[i _ []]].
    by case: ifP => _ <- ->; rewrite !inE ?Za21 ?(negPf nz_a11) !eqxx ?orbT.
  apply/subsetP=> ij /setUP[] /imsetP[] => [j | i] _ {ij}->; rewrite inE.
    by case: ifPn => // /eqP Za1j; rewrite (Da i1 j1) Za21 Za1j !add0r oppr_eq0.
  by case: ifPn => // /eqP Zai1; rewrite (Da i1 j1) Za12 Zai1 !add0r oppr_eq0.
pose L i := [set ij | ij.1 == i] :&: A; pose C j := [set ij | ij.2 == j] :&: A.
have{ubA2} ubLC i j: (#|L i| + #|C j| != w2 + w1)%N.
  apply: contraNneq ubA2 => <-; rewrite addnS leqW // -cardsUI -setIUl -setIIl.
  rewrite -(card1 (i, j)) leq_add ?subset_leq_card ?subsetIr //.
  by apply/subsetP=> ij /setIP[]; rewrite !inE.
have lbA L1 L2: L1 :&: L2 =i set0 -> (#|L1 :&: A| + #|L2 :&: A| <= #|A|)%N.
  rewrite -cardsUI -setIUl -setIIl => /setP->.
  by rewrite set0I cards0 addn0 subset_leq_card ?subsetIr.
have oL i1: ~~ [exists j, a i1 j == 0] -> #|L i1| = w2.
  rewrite negb_exists => /forallP nz_a1.
  transitivity #|predX (pred1 i1) (Iirr W2)|; last by rewrite cardX card1 mul1n.
  by apply/eq_card=> ij; rewrite !inE andbT andb_idr // => /eqP->.
have oC i1 j1 j2 : a i1 j1 != 0 -> a i1 j2 == 0 -> #|C j1| = w1.
  move=> nz_a11 /(Za i1)/contra/(_ nz_a11) nz_a1.
  transitivity #|predX (Iirr W1) (pred1 j1)|; last by rewrite cardX card1 muln1.
  by apply/eq_card=> ij; rewrite !inE andb_idr // => /eqP->.
(* This is step (3.8.2). *)
have [/existsP[j1 Za01] | /oL oL0] := boolP [exists j, a i0 j == 0].
  have j0'1 : j1 != j0 by apply: contraTneq Za01 => ->.
  have oC0: #|C j0| = w1 by apply: oC nz_a0 Za01.
  suffices Za0 i j: j != j0 -> a i j = 0.
    left=> i j; rewrite -/(a i j) mulr_natl mulrb; have [->|/Za0//] := altP eqP.
    by rewrite (Da i0 j1) !(Za0 _ j1) // subr0 add0r.
  move=> j0'j; apply: contraNeq (ubLC i j0) => nz_aij; rewrite oC0 oL //.
  apply: contra ubA => /existsP[_ /Za/contra/(_ nz_aij) nz_a_j].
  rewrite minn_mulr geq_min mul2n -addnn -{2}oC0 -(oC i0 j j1) ?lbA // => ij.
  by rewrite !inE; apply/andP=> [[/eqP-> /idPn]].
(* This is step (3.8.3). *)
suffices Za0 i j: i != i0 -> a i j = 0.
  right=> i j; rewrite -/(a i j) mulr_natl mulrb; have [->|/Za0//] := altP eqP.
  have /card_gt0P[i1 i0'i]: (0 < #|predC1 i0|)%N.
    by rewrite cardC1 nirrW1 -(subnKC w1gt2).
  by rewrite (Da i1 j0) !(Za0 i1) // subr0 addr0.
move=> i0'i; suffices /existsP[j1 Zai1]: [exists j, a i j == 0].
  by apply: contraNeq (ubLC i0 j) => /oC/(_ Zai1)->; rewrite oL0.
apply: contraR ubA; rewrite minn_mulr geq_min orbC mul2n -addnn => /oL{1}<-.
by rewrite -oL0 lbA // => ij; rewrite !inE; apply/andP=> [[/eqP-> /idPn]].
Qed.

(* A weaker version of PeterFalvi (3.8). *)
Lemma cycTI_NC_minn (phi : 'CF(G)) : 
    {in V, forall x, phi x = 0} -> (0 < NC phi < 2 * minn w1 w2)%N ->
  (minn w1 w2 <= NC phi)%N.
Proof.
move=> phiV_0 /andP[/card_gt0P[[i0 j0]]]; rewrite inE /= => nz_a0 ubNC.
pose L := [seq (i0, j) | j : Iirr W2]; pose C := [seq (i, j0) | i : Iirr W1]. 
have [oL oC]: #|L| = w2 /\ #|C| = w1 by rewrite !card_image // => i j [].
have [Da | Da] := small_cycTI_NC phiV_0 ubNC nz_a0.
  rewrite geq_min -oC subset_leq_card //.
  by apply/subsetP=> _ /codomP[i ->]; rewrite !inE /= Da eqxx mul1r.
rewrite geq_min orbC -oL subset_leq_card //.
by apply/subsetP=> _ /codomP[j ->]; rewrite !inE /= Da eqxx mul1r.
Qed.

(* Another consequence of (3.8), used in (4.8), (10.5), (10.10) and (11.8). *)
Lemma eq_signed_sub_cTIiso phi e i j1 j2 :
    let rho := (-1) ^+ e *: (eta_ i j1 - eta_ i j2) in
    phi \in 'Z[irr G] -> '[phi] = 2%:R -> j1 != j2 ->
  {in V, phi =1 rho} -> phi = rho.
Proof.
set rho := _ - _; move: phi => phi0 /= Zphi0 n2phi0 neq_j12 eq_phi_rho.
pose phi := (-1) ^+ e *: phi0; pose psi := phi - rho.
have{eq_phi_rho} psiV0 z: z \in V -> psi z = 0.
  by move=> Vz; rewrite !cfunE eq_phi_rho // !cfunE signrMK subrr.
have{Zphi0} Zphi: phi \in 'Z[irr G] by rewrite rpredZsign.
have{n2phi0} n2phi: '[phi] = 2%:R by rewrite cfnorm_sign.
have Zrho: rho \in 'Z[irr G] by rewrite rpredB ?cycTIiso_vchar.
have n2rho: '[rho] = 2%:R.
  by rewrite cfnormBd !cfdot_cycTIiso ?eqxx ?(negPf neq_j12) ?andbF.
have [oIphi _ Dphi] := dirr_small_norm Zphi n2phi isT.
have [oIrho _ Drho] := dirr_small_norm Zrho n2rho isT.
set Iphi := dirr_constt _ in oIphi Dphi.
set Irho := dirr_constt _ in oIrho Drho.
suffices /eqP eqIrho: Irho == Iphi by rewrite Drho eqIrho -Dphi signrZK.
have psi_phi'_lt0 di: di \in Irho :\: Iphi -> '[psi, dchi di] < 0.
  case/setDP=> rho_di phi'di; rewrite cfdotBl subr_lt0.
  move: rho_di; rewrite dirr_consttE; apply: ler_lt_trans.
  rewrite real_lerNgt -?dirr_consttE ?real0 ?Creal_Cint //.
  by rewrite Cint_cfdot_vchar ?dchi_vchar.
have NCpsi: (NC psi < 2 * minn w1 w2)%N.
  suffices NCpsi4: (NC psi <= 2 + 2)%N.
    by rewrite (leq_ltn_trans NCpsi4) // !addnn mul2n ltn_double leq_min w1gt2.
  by rewrite cycTI_NC_sub // cycTI_NC_norm ?n2phi ?n2rho.
pose rhoId := dirr_dIirr (fun sk => (-1) ^+ (sk.1 : bool) *: eta_ i sk.2).
have rhoIdE s k: dchi (rhoId (s, k)) = (-1) ^+ s *: eta_ i k.
  by apply: dirr_dIirrE => sk; rewrite rpredZsign cycTIiso_dirr.
rewrite eqEcard oIrho oIphi andbT -setD_eq0; apply/set0Pn=> [[dk1 phi'dk1]].
have [[rho_dk1 _] psi_k1_lt0] := (setDP phi'dk1, psi_phi'_lt0 _ phi'dk1).
have dot_dk1: '[rho, dchi dk1] = 1.
  rewrite Drho cfdot_suml (big_setD1 dk1) //= cfnorm_dchi big1 ?addr0 //.
  move=> dk2 /setD1P[/negPf dk1'2 /dirr_constt_oppl]; rewrite cfdot_dchi dk1'2.
  by case: eqP => [-> /negP[] | _ _]; rewrite ?subrr ?ndirrK.
have dot_dk2: 0 < '[rho, rho - dchi dk1].
  by rewrite cfdotBr dot_dk1 n2rho addrK ltr01.
have{dot_dk1 dot_dk2} [s [k Dk1 rho_k2]]:
  exists s, exists2 k, rhoId (s, k.1) = dk1 & rhoId (~~ s, k.2) \in Irho.
- move/cfdot_add_dirr_eq1: dot_dk1.
  rewrite dirr_dchi rpredN !cycTIiso_dirr //.
  case=> // Dk1; [exists false, (j1, j2) | exists true, (j2, j1)];
    try apply: dirr_inj; rewrite ?dirr_consttE rhoIdE scaler_sign //=.
  + by rewrite addrC Dk1 addKr in dot_dk2.
  by rewrite Dk1 addrK in dot_dk2.
rewrite -Dk1 rhoIdE cfdotZr rmorph_sign in psi_k1_lt0.
have psi_k1_neq0: '[psi, eta_ i k.1] != 0.
  by rewrite -(can_eq (signrMK s)) mulr0 ltr_eqF.
set dk2 := rhoId _ in rho_k2.
have NCk2'_le1 (dI : {set _}):
  dk2 \in dI -> #|dI| = 2%N -> (NC (\sum_(dk in dI :\ dk2) dchi dk)%R <= 1)%N.
- rewrite (cardsD1 dk2) => -> /eqP/cards1P[dk ->].
  by rewrite big_set1 cycTI_NC_dirr ?dirr_dchi.
suffices /psi_phi'_lt0/ltr_geF/idP[]: dk2 \in Irho :\: Iphi.
  rewrite rhoIdE cfdotZr signrN rmorphN mulNr oppr_ge0 rmorph_sign.  
  have := small_cycTI_NC psiV0 NCpsi psi_k1_neq0.
  by case=> // ->; rewrite mulrCA nmulr_lle0 ?ler0n.
have: (1 + 1 < NC psi)%N.
  apply (@leq_trans (minn w1 w2)); first by rewrite leq_min w1gt2.
  apply: cycTI_NC_minn => //; rewrite NCpsi /NC.
  by rewrite (cardsD1 (i, k.1)) inE /= psi_k1_neq0.
rewrite inE rho_k2 andbT ltnNge; apply: contra => phi_k2.
rewrite /psi Drho (big_setD1 dk2) //= Dphi (big_setD1 dk2) //=.
by rewrite addrAC opprD addNKr addrC cycTI_NC_sub ?NCk2'_le1.
Qed.

(* This is PeterFalvi (3.9)(a). *)
Lemma eq_in_cycTIiso (i : Iirr W) (phi : 'CF(G)) :
  phi \in dirr G -> {in V, phi =1 'chi_i} -> phi = sigma 'chi_i.
Proof.
move=> Dphi; rewrite -(inv_dprod_IirrK defW i).
case: (inv_dprod_Iirr _)=> /= i1 j1 EphiC.
pose psi : 'CF(G) := eta_ i1 j1 - phi.
have ZpsiV: {in V, forall g, psi g = 0}=> [g GiV|].
  by rewrite /psi !cfunE cycTIiso_restrict // -(EphiC _ GiV) subrr.
pose a i j := '[psi, eta_ i j]; pose S := [set ij | a ij.1 ij.2 != 0].
case: (boolP ((i1, j1) \in S))=> [I1J1iS|]; last first.
  rewrite inE negbK /a  cfdotBl cfdot_cycTIiso !eqxx /=.
  rewrite cfdot_dirr ?(irr_dirr, cycTIiso_dirr) //.
  case: (boolP (phi == _))=> [|_].
    by rewrite opprK -(natrD _ 1 1) pnatr_eq0.
  case: (boolP (phi == _))=> [/eqP //|].
  by rewrite subr0 oner_eq0.
have SPos : (0 < #|S|)%N by rewrite (cardD1 (i1,j1)) I1J1iS.
have SLt: (#|S| <= 2)%N.
  by rewrite -[2]add1n cycTI_NC_sub // !cycTI_NC_dirr // cycTIiso_dirr.
have: (0 < #|S| < 2 * minn w1 w2)%N.
  rewrite SPos; apply: leq_ltn_trans SLt _.
  by rewrite -{1}[2%N]muln1 ltn_mul2l /= leq_min ![(1 < _)%N]ltnW.
move/(cycTI_NC_minn ZpsiV); rewrite leqNgt; case/negP.
by apply: leq_ltn_trans SLt _; rewrite leq_min w1gt2.
Qed.

(* This is the second part of Peterfalvi (3.9)(a). *)
Lemma cfAut_cycTIiso u phi : cfAut u (sigma phi) = sigma (cfAut u phi).
Proof.
rewrite [phi]cfun_sum_cfdot !raddf_sum; apply: eq_bigr => ij _.
rewrite /= !(linearZ, cfAutZ) /= -aut_IirrE; congr (_ *: _) => {phi}.
apply: eq_in_cycTIiso => [|x Vx /=].
  by have /cycTIirrP[i [j ->]] := mem_irr ij; rewrite dirr_aut cycTIiso_dirr.
by rewrite cfunE cycTIiso_restrict // aut_IirrE cfunE.
Qed.

Section AutCyclicTI.

Variable iw : Iirr W.
Let w := 'chi_iw.
Let a := #[w]%CF.

Let Zsigw : sigma w \in 'Z[irr G].
Proof. by have [_ -> //] := cycTI_Zisometry; apply: irr_vchar. Qed.

Let lin_w: w \is a linear_char := Wlin iw.

(* This is Peterfalvi (3.9)(b). *)
Lemma cycTIiso_aut_exists k :
    coprime k a ->
  [/\ exists u, sigma (w ^+ k) = cfAut u (sigma w)
    & forall x, coprime #[x] a -> sigma (w ^+ k) x = sigma w x].
Proof.
case/(make_pi_cfAut G)=> u Du_a Du_a'.
suffices Dwk: sigma (w ^+ k) = cfAut u (sigma w).
  by split=> [|x co_x_a]; [exists u | rewrite Dwk Du_a'].
rewrite cfAut_cycTIiso; congr (sigma _); apply/cfun_inP=> x Wx.
have Wxbar: coset _ x \in (W / cfker w)%G by rewrite mem_quotient.
rewrite exp_cfunE // cfunE -cfQuoEker //.
rewrite -lin_charX ?cfQuo_lin_char ?cfker_normal // -Du_a ?cfunE //.
  by rewrite char_vchar ?cfQuo_char ?irr_char.
by rewrite [a]cforder_lin_char // dvdn_exponent.
Qed.

(* This is Peterfalvi (3.9)(c). *)
Lemma Cint_cycTIiso_coprime x : coprime #[x] a -> sigma w x \in Cint.
Proof.
move=> co_x_a; apply: Cint_rat_Aint (Aint_vchar _ Zsigw).
have [Qb galQb [QbC AutQbC [w_b genQb memQb]]] := group_num_field_exists <[x]>.
have{memQb} [wx Dwx]: exists wx, sigma w x = QbC wx.
  have /memQb Qbx := dvdnn #[x].
  have [sw1 /Qbx[wx1 Dwx1] [sw2 /Qbx[wx2 Dwx2] ->]] := vcharP _ Zsigw.
  by exists (wx1 - wx2); rewrite rmorphB !cfunE Dwx1 Dwx2.
suffices: wx \in fixedField 'Gal({:Qb} / 1).
  rewrite Dwx (galois_fixedField galQb) ?subvf // => /vlineP[z ->].
  by rewrite -in_algE fmorph_eq_rat fmorph_rat Crat_rat.
apply/fixedFieldP=> [|v_b _]; first exact: memvf.
have [v Dv] := AutQbC v_b; apply: (fmorph_inj QbC); rewrite Dv -Dwx.
have [u uQb uQb'] := dvd_restrict_cfAut (W / cfker w) #[x] v.
transitivity (sigma (cfAut u w) x); first by rewrite -cfAut_cycTIiso cfunE -uQb.
congr (sigma _ _); apply/cfun_inP=> y Wy; rewrite cfunE -cfQuoEker //.
rewrite uQb' ?char_vchar ?cfQuo_char ?irr_char // coprime_sym.
apply: coprime_dvdr co_x_a; rewrite [a]cforder_lin_char //.
by rewrite dvdn_exponent ?mem_quotient.
Qed.

End AutCyclicTI.

End Three.

Implicit Arguments ortho_cycTIiso_vanish [gT G W W1 W2 defW psi].

Section ThreeSymmetry.

Variables (gT : finGroupType) (G W W1 W2 : {group gT}).
Implicit Types (defW : W1 \x W2 = W) (xdefW : W2 \x W1 = W).
Local Notation sigma_ := (@cyclicTIiso gT G W _ _).
Local Notation w_ defW i j := (cyclicTIirr defW i j).

Lemma cycTIisoC defW xdefW ctiW xctiW i j :
  @sigma_ defW ctiW (w_ defW i j) = @sigma_ xdefW xctiW (w_ xdefW j i).
Proof.
apply: eq_in_cycTIiso; first exact: cycTIiso_dirr.
by rewrite /cyclicTIset setUC cyclicTIirrC; apply: cycTIiso_restrict.
Qed.

Lemma cycTIiso_irrelC defW xdefW ctiW xctiW :
  @sigma_ defW ctiW = @sigma_ xdefW xctiW.
Proof.
suffices: sigma_ ctiW =1 sigma_ xctiW by rewrite ![sigma_ _]unlock => /lfunP->.
move=> phi; have [z_ ->] := cfun_irr_sum phi; rewrite !linear_sum.
apply/eq_bigr=> ij _; have [i [j ->]] := cycTIirrP defW (mem_irr ij).
by rewrite !linearZ /= {1}cycTIisoC cyclicTIirrC.
Qed.

Lemma cycTIiso_irrel defW defW' ctiW ctiW' :
  @sigma_ defW ctiW = @sigma_ defW' ctiW'.
Proof.
have xdefW: W2 \x W1 = W by rewrite dprodC.
by rewrite !(cycTIiso_irrelC _ (cyclicTIhyp_sym ctiW xdefW)).
Qed.

End ThreeSymmetry.

(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrbool ssrfun eqtype ssrnat div seq fintype.
From mathcomp
Require Import bigop finset fingroup morphism perm automorphism quotient.

(******************************************************************************)
(* Group action: orbits, stabilisers, transitivity.                           *)
(*        is_action D to == the function to : T -> aT -> T defines an action  *)
(*                          of D : {set aT} on T.                             *)
(*            action D T == structure for a function defining an action of D. *)
(*            act_dom to == the domain D of to : action D rT.                 *)
(*    {action: aT &-> T} == structure for a total action.                     *)
(*                       := action [set: aT] T                                *)
(*   TotalAction to1 toM == the constructor for total actions; to1 and toM    *)
(*                          are the proofs of the action identities for 1 and *)
(*                          a * b, respectively.                              *)
(*   is_groupAction R to == to is a group action on range R: for all a in D,  *)
(*                          the permutation induced by to a is in Aut R. Thus *)
(*                          the action of D must be trivial outside R.        *)
(*       groupAction D R == the structure for group actions of D on R. This   *)
(*                          is a telescope on action D rT.                    *)
(*         gact_range to == the range R of to : groupAction D R.              *)
(*     GroupAction toAut == constructs a groupAction for action to from       *)
(*                          toAut : actm to @* D \subset Aut R (actm to is    *)
(*                          the morphism to {perm rT} associated to 'to').    *)
(*      orbit to A x == the orbit of x under the action of A via to.          *)
(* orbit_transversal to A S == a transversal of the partition orbit to A @: S *)
(*                      of S, provided A acts on S via to.                    *)
(*    amove to A x y == the set of a in A whose action sends x to y.          *)
(*      'C_A[x | to] == the stabiliser of x : rT in A :&: D.                  *)
(*      'C_A(S | to) == the pointwise stabiliser of S : {set rT} in D :&: A.  *)
(*      'N_A(S | to) == the global stabiliser of S : {set rT} in D :&: A.     *)
(*  'Fix_(S | to)[a] == the set of fixpoints of a in S.                       *)
(*  'Fix_(S | to)(A) == the set of fixpoints of A in S.                       *)
(* In the first three _A can be omitted and defaults to the domain D of to;   *)
(* in the last two S can be omitted and defaults to [set: T], so 'Fix_to[a]   *)
(* is the set of all fixpoints of a.                                          *)
(*   The domain restriction ensures that stabilisers have a canonical group   *)
(* structure, but note that 'Fix sets are generally not groups. Indeed, we    *)
(* provide alternative definitions when to is a group action on R:            *)
(*      'C_(G | to)(A) == the centraliser in R :&: G of the group action of   *)
(*                        D :&: A via to                                      *)
(*      'C_(G | to)[a] == the centraliser in R :&: G of a \in D, via to.      *)
(*   These sets are groups when G is; G can be omitted: 'C(|to)(A) is the     *)
(* centraliser in R of the action of D :&: A via to.                          *)
(*          [acts A, on S | to] == A \subset D acts on the set S via to.      *)
(*          {acts A, on S | to} == A acts on the set S (Prop statement).      *)
(*    {acts A, on group G | to} == [acts A, on S | to] /\ G \subset R, i.e.,  *)
(*                                 A \subset D acts on G \subset R, via       *)
(*                                 to : groupAction D R.                      *)
(*    [transitive A, on S | to] == A acts transitively on S.                  *)
(*      [faithful A, on S | to] == A acts faithfully on S.                    *)
(*      acts_irreducibly to A G == A acts irreducibly via the groupAction to  *)
(*                                 on the nontrivial group G, i.e., A does    *)
(*                                 not act on any nontrivial subgroup of G.   *)
(* Important caveat: the definitions of orbit, amove, 'Fix_(S | to)(A),       *)
(* transitive and faithful assume that A is a subset of the domain D. As most *)
(* of the permutation actions we consider are total this is usually harmless. *)
(* (Note that the theory of partial actions is only partially developed.)     *)
(*   In all of the above, to is expected to be the actual action structure,   *)
(* not merely the function. There is a special scope %act for actions, and    *)
(* constructions and notations for many classical actions:                    *)
(*       'P == natural action of a permutation group via aperm.               *)
(*       'J == internal group action (conjugation) via conjg (_ ^ _).         *)
(*       'R == regular group action (right translation) via mulg (_ * _).     *)
(*            (However, to limit ambiguity, _ * _ is NOT a canonical action.) *)
(*     to^* == the action induced by to on {set rT} via to^* (== setact to).  *)
(*      'Js == the internal action on subsets via _ :^ _, equivalent to 'J^*. *)
(*      'Rs == the regular action on subsets via rcoset, equivalent to 'R^*.  *)
(*      'JG == the conjugation action on {group rT} via (_ :^ _)%G.           *)
(*   to / H == the action induced by to on coset_of H via qact to H, and      *)
(*             restricted to (qact_dom to H) == 'N(rcosets H 'N(H) | to^* ).  *)
(*       'Q == the action induced to cosets by conjugation; the domain is     *)
(*             qact_dom 'J H, which is provably equal to 'N(H).               *)
(*  to %% A == the action of coset_of A via modact to A, with domain D / A    *)
(*             and support restricted to 'C(D :&: A | to).                    *)
(* to \ sAD == the action of A via ract to sAD == to, if sAD : A \subset D.   *)
(*  [Aut G] == the permutation action restricted to Aut G, via autact G.      *)
(*  <[nRA]> == the action of A on R via actby nRA == to in A and on R, and    *)
(*             the trivial action elsewhere; here nRA : [acts A, on R | to]   *)
(*             or nRA : {acts A, on group R | to}.                            *)
(*     to^? == the action induced by to on sT : @subType rT P, via subact to  *)
(*             with domain subact_dom P to == 'N([set x | P x] | to).         *)
(*  <<phi>> == the action of phi : D >-> {perm rT}, via mact phi.             *)
(*  to \o f == the composite action (with domain f @*^-1 D) of the action to  *)
(*             with f : {morphism G >-> aT}, via comp_act to f. Here f must   *)
(*             be the actual morphism object (e.g., coset_morphism H), not    *)
(*             the underlying function (e.g., coset H).                       *)
(* The explicit application of an action to is usually written (to%act x a),  *)
(* but %act can be omitted if to is an abstract action or a set action to0^*. *)
(* Note that this form will simplify and expose the acting function.          *)
(*   There is a %gact scope for group actions; the notations above are        *)
(* recognised in %gact when they denote canonical group actions.              *)
(*   Actions can be used to define morphisms:                                 *)
(* actperm to == the morphism D >-> {perm rT} induced by to.                  *)
(*  actm to a == if a \in D the function on D induced by the action to, else  *)
(*               the identity function. If to is a group action with range R  *)
(*               then actm to a is canonically a morphism on R.               *)
(* We also define here the restriction operation on permutations (the domain  *)
(* of this operations is a stabiliser), and local automorphism groups:        *)
(*  restr_perm S p == if p acts on S, the permutation with support in S that  *)
(*                    coincides with p on S; else the identity. Note that     *)
(*                    restr_perm is a permutation group morphism that maps    *)
(*                    Aut G to Aut S when S is a subgroup of G.               *)
(*      Aut_in A G == the local permutation group 'N_A(G | 'P) / 'C_A(G | 'P) *)
(*                    Usually A is an automorphism group, and then Aut_in A G *)
(*                    is isomorphic to a subgroup of Aut G, specifically      *)
(*                    restr_perm @* A.                                        *)
(*  Finally, gproduct.v will provide a semi-direct group construction that    *)
(* maps an external group action to an internal one; the theory of morphisms  *)
(* between such products makes use of the following definition:               *)
(*  morph_act to to' f fA <=> the action of to' on the images of f and fA is  *)
(*                   the image of the action of to, i.e., for all x and a we  *)
(*                   have f (to x a) = to' (f x) (fA a). Note that there is   *)
(*                   no mention of the domains of to and to'; if needed, this *)
(*                   predicate should be restricted via the {in ...} notation *)
(*                   and domain conditions should be added.                   *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Section ActionDef.

Variables (aT : finGroupType) (D : {set aT}) (rT : Type).
Implicit Types a b : aT.
Implicit Type x : rT.

Definition act_morph to x := forall a b, to x (a * b) = to (to x a) b.

Definition is_action to :=
  left_injective to /\ forall x, {in D &, act_morph to x}.

Record action := Action {act :> rT -> aT -> rT; _ : is_action act}.

Definition clone_action to :=
  let: Action _ toP := to return {type of Action for to} -> action in
  fun k => k toP.

End ActionDef.

(* Need to close the Section here to avoid re-declaring all Argument Scopes *)
Delimit Scope action_scope with act.
Bind Scope action_scope with action.
Arguments act_morph {aT rT%type} to x%g.
Arguments is_action {aT} D%g {rT} to.
Arguments act {aT D%g rT%type} to%act x%g a%g : rename.
Arguments clone_action [aT D%g rT%type to%act] _.

Notation "{ 'action' aT &-> T }" := (action [set: aT] T)
  (at level 0, format "{ 'action'  aT  &->  T }") : type_scope.

Notation "[ 'action' 'of' to ]" := (clone_action (@Action _ _ _ to))
  (at level 0, format "[ 'action'  'of'  to ]") : form_scope.

Definition act_dom aT D rT of @action aT D rT := D.

Section TotalAction.

Variables (aT : finGroupType) (rT : Type) (to : rT -> aT -> rT).
Hypotheses (to1 : to^~ 1 =1 id) (toM : forall x, act_morph to x).

Lemma is_total_action : is_action setT to.
Proof.
split=> [a | x a b _ _] /=; last by rewrite toM.
by apply: can_inj (to^~ a^-1) _ => x; rewrite -toM ?mulgV.
Qed.

Definition TotalAction := Action is_total_action.

End TotalAction.

Section ActionDefs.

Variables (aT aT' : finGroupType) (D : {set aT}) (D' : {set aT'}).

Definition morph_act rT rT' (to : action D rT) (to' : action D' rT') f fA :=
  forall x a, f (to x a) = to' (f x) (fA a).

Variable rT : finType. (* Most definitions require a finType structure on rT *)
Implicit Type to : action D rT.
Implicit Type A : {set aT}.
Implicit Type S : {set rT}.

Definition actm to a := if a \in D then to^~ a else id.

Definition setact to S a := [set to x a | x in S].

Definition orbit to A x := to x @: A.

Definition amove to A x y := [set a in A | to x a == y].

Definition afix to A := [set x | A \subset [set a | to x a == x]].

Definition astab S to := D :&: [set a | S \subset [set x | to x a == x]].

Definition astabs S to := D :&: [set a | S \subset to^~ a @^-1: S].

Definition acts_on A S to := {in A, forall a x, (to x a \in S) = (x \in S)}.

Definition atrans A S to := S \in orbit to A @: S.

Definition faithful A S to := A :&: astab S to \subset [1].

End ActionDefs.

Arguments setact {aT D%g rT} to%act S%g a%g.
Arguments orbit {aT D%g rT} to%act A%g x%g.
Arguments amove {aT D%g rT} to%act A%g x%g y%g.
Arguments afix {aT D%g rT} to%act A%g.
Arguments astab {aT D%g rT} S%g to%act.
Arguments astabs {aT D%g rT} S%g to%act.
Arguments acts_on {aT D%g rT} A%g S%g to%act.
Arguments atrans {aT D%g rT} A%g S%g to%act.
Arguments faithful {aT D%g rT} A%g S%g to%act.

Notation "to ^*" := (setact to) (at level 2, format "to ^*") : fun_scope.

Prenex Implicits orbit amove.

Notation "''Fix_' to ( A )" := (afix to A)
 (at level 8, to at level 2, format "''Fix_' to ( A )") : group_scope.

(* camlp4 grammar factoring *)
Notation "''Fix_' ( to ) ( A )" := 'Fix_to(A)
  (at level 8, only parsing) : group_scope.

Notation "''Fix_' ( S | to ) ( A )" := (S :&: 'Fix_to(A))
 (at level 8, format "''Fix_' ( S  |  to ) ( A )") : group_scope.

Notation "''Fix_' to [ a ]" := ('Fix_to([set a]))
 (at level 8, to at level 2, format "''Fix_' to [ a ]") : group_scope.

Notation "''Fix_' ( S | to ) [ a ]" := (S :&: 'Fix_to[a])
 (at level 8, format "''Fix_' ( S  |  to ) [ a ]") : group_scope.

Notation "''C' ( S | to )" := (astab S to)
 (at level 8, format "''C' ( S  |  to )") : group_scope.

Notation "''C_' A ( S | to )" := (A :&: 'C(S | to))
 (at level 8, A at level 2, format "''C_' A ( S  |  to )") : group_scope.
Notation "''C_' ( A ) ( S | to )" := 'C_A(S | to)
  (at level 8, only parsing) : group_scope.

Notation "''C' [ x | to ]" := ('C([set x] | to))
 (at level 8, format "''C' [ x  |  to ]") : group_scope.

Notation "''C_' A [ x | to ]" := (A :&: 'C[x | to])
  (at level 8, A at level 2, format "''C_' A [ x  |  to ]") : group_scope.
Notation "''C_' ( A ) [ x | to ]" := 'C_A[x | to]
  (at level 8, only parsing) : group_scope.

Notation "''N' ( S | to )" := (astabs S to)
  (at level 8, format "''N' ( S  |  to )") : group_scope.

Notation "''N_' A ( S | to )" := (A :&: 'N(S | to))
  (at level 8, A at level 2, format "''N_' A ( S  |  to )") : group_scope.

Notation "[ 'acts' A , 'on' S | to ]" := (A \subset pred_of_set 'N(S | to))
  (at level 0, format "[ 'acts'  A ,  'on'  S  |  to ]") : form_scope.

Notation "{ 'acts' A , 'on' S | to }" := (acts_on A S to)
  (at level 0, format "{ 'acts'  A ,  'on'  S  |  to }") : form_scope.

Notation "[ 'transitive' A , 'on' S | to ]" := (atrans A S to)
  (at level 0, format "[ 'transitive'  A ,  'on'  S  |  to ]") : form_scope.

Notation "[ 'faithful' A , 'on' S | to ]" := (faithful A S to)
  (at level 0, format "[ 'faithful'  A ,  'on'  S  |  to ]") : form_scope.

Section RawAction.
(* Lemmas that do not require the group structure on the action domain. *)
(* Some lemmas like actMin would be actually be valid for arbitrary rT, *)
(* e.g., for actions on a function type, but would be difficult to use  *)
(* as a view due to the confusion between parameters and assumptions.   *)

Variables (aT : finGroupType) (D : {set aT}) (rT : finType) (to : action D rT).

Implicit Types (a : aT) (x y : rT) (A B : {set aT}) (S T : {set rT}).

Lemma act_inj : left_injective to. Proof. by case: to => ? []. Qed.
Arguments act_inj : clear implicits.

Lemma actMin x : {in D &, act_morph to x}.
Proof. by case: to => ? []. Qed.

Lemma actmEfun a : a \in D -> actm to a = to^~ a.
Proof. by rewrite /actm => ->. Qed.

Lemma actmE a : a \in D -> actm to a =1 to^~ a.
Proof. by move=> Da; rewrite actmEfun. Qed.

Lemma setactE S a : to^* S a = [set to x a | x in S].
Proof. by []. Qed.

Lemma mem_setact S a x : x \in S -> to x a \in to^* S a.
Proof. exact: mem_imset. Qed.

Lemma card_setact S a : #|to^* S a| = #|S|.
Proof. by apply: card_imset; apply: act_inj. Qed.

Lemma setact_is_action : is_action D to^*.
Proof.
split=> [a R S eqRS | a b Da Db S]; last first.
  by rewrite /setact /= -imset_comp; apply: eq_imset => x; apply: actMin.
apply/setP=> x; apply/idP/idP=> /(mem_setact a).
  by rewrite eqRS => /imsetP[y Sy /act_inj->].
by rewrite -eqRS => /imsetP[y Sy /act_inj->].
Qed.

Canonical set_action := Action setact_is_action.

Lemma orbitE A x : orbit to A x = to x @: A. Proof. by []. Qed.

Lemma orbitP A x y :
  reflect (exists2 a, a \in A & to x a = y) (y \in orbit to A x).
Proof. by apply: (iffP imsetP) => [] [a]; exists a. Qed.

Lemma mem_orbit A x a : a \in A -> to x a \in orbit to A x.
Proof. exact: mem_imset. Qed.

Lemma afixP A x : reflect (forall a, a \in A -> to x a = x) (x \in 'Fix_to(A)).
Proof.
rewrite inE; apply: (iffP subsetP) => [xfix a /xfix | xfix a Aa].
  by rewrite inE => /eqP.
by rewrite inE xfix.
Qed.

Lemma afixS A B : A \subset B -> 'Fix_to(B) \subset 'Fix_to(A).
Proof. by move=> sAB; apply/subsetP=> u; rewrite !inE; apply: subset_trans. Qed.

Lemma afixU A B : 'Fix_to(A :|: B) = 'Fix_to(A) :&: 'Fix_to(B).
Proof. by apply/setP=> x; rewrite !inE subUset. Qed.

Lemma afix1P a x : reflect (to x a = x) (x \in 'Fix_to[a]).
Proof. by rewrite inE sub1set inE; apply: eqP. Qed.

Lemma astabIdom S : 'C_D(S | to) = 'C(S | to).
Proof. by rewrite setIA setIid. Qed.

Lemma astab_dom S : {subset 'C(S | to) <= D}.
Proof. by move=> a /setIP[]. Qed.

Lemma astab_act S a x : a \in 'C(S | to) -> x \in S -> to x a = x.
Proof.
rewrite 2!inE => /andP[_ cSa] Sx; apply/eqP.
by have:= subsetP cSa x Sx; rewrite inE.
Qed.

Lemma astabS S1 S2 : S1 \subset S2 -> 'C(S2 | to) \subset 'C(S1 | to).
Proof.
move=> sS12; apply/subsetP=> x; rewrite !inE => /andP[->].
exact: subset_trans.
Qed.

Lemma astabsIdom S : 'N_D(S | to) = 'N(S | to).
Proof. by rewrite setIA setIid. Qed.

Lemma astabs_dom S : {subset 'N(S | to) <= D}.
Proof. by move=> a /setIdP[]. Qed.

Lemma astabs_act S a x : a \in 'N(S | to) -> (to x a \in S) = (x \in S).
Proof.
rewrite 2!inE subEproper properEcard => /andP[_].
rewrite (card_preimset _ (act_inj _)) ltnn andbF orbF => /eqP{2}->.
by rewrite inE.
Qed.

Lemma astab_sub S : 'C(S | to) \subset 'N(S | to).
Proof.
apply/subsetP=> a cSa; rewrite !inE (astab_dom cSa).
by apply/subsetP=> x Sx; rewrite inE (astab_act cSa).
Qed.

Lemma astabsC S : 'N(~: S | to) = 'N(S | to).
Proof.
apply/setP=> a; apply/idP/idP=> nSa; rewrite !inE (astabs_dom nSa).
  by rewrite -setCS -preimsetC; apply/subsetP=> x; rewrite inE astabs_act.
by rewrite preimsetC setCS; apply/subsetP=> x; rewrite inE astabs_act.
Qed.

Lemma astabsI S T : 'N(S | to) :&: 'N(T | to) \subset 'N(S :&: T | to).
Proof.
apply/subsetP=> a; rewrite !inE -!andbA preimsetI => /and4P[-> nSa _ nTa] /=.
by rewrite setISS.
Qed.

Lemma astabs_setact S a : a \in 'N(S | to) -> to^* S a = S.
Proof.
move=> nSa; apply/eqP; rewrite eqEcard card_setact leqnn andbT.
by apply/subsetP=> _ /imsetP[x Sx ->]; rewrite astabs_act.
Qed.

Lemma astab1_set S : 'C[S | set_action] = 'N(S | to).
Proof.
apply/setP=> a; apply/idP/idP=> nSa.
  case/setIdP: nSa => Da; rewrite !inE Da sub1set inE => /eqP defS.
  by apply/subsetP=> x Sx; rewrite inE -defS mem_setact.
by rewrite !inE (astabs_dom nSa) sub1set inE /= astabs_setact.
Qed.

Lemma astabs_set1 x : 'N([set x] | to) = 'C[x | to].
Proof.
apply/eqP; rewrite eqEsubset astab_sub andbC setIS //.
by apply/subsetP=> a; rewrite ?(inE,sub1set).
Qed.

Lemma acts_dom A S : [acts A, on S | to] -> A \subset D.
Proof. by move=> nSA; rewrite (subset_trans nSA) ?subsetIl. Qed.

Lemma acts_act A S : [acts A, on S | to] -> {acts A, on S | to}.
Proof. by move=> nAS a Aa x; rewrite astabs_act ?(subsetP nAS). Qed.

Lemma astabCin A S :
  A \subset D -> (A \subset 'C(S | to)) = (S \subset 'Fix_to(A)).
Proof.
move=> sAD; apply/subsetP/subsetP=> [sAC x xS | sSF a aA].
  by apply/afixP=> a aA; apply: astab_act (sAC _ aA) xS.
rewrite !inE (subsetP sAD _ aA); apply/subsetP=> x xS.
by move/afixP/(_ _ aA): (sSF _ xS); rewrite inE => ->.
Qed.

Section ActsSetop.

Variables (A : {set aT}) (S T : {set rT}).
Hypotheses (AactS : [acts A, on S | to]) (AactT : [acts A, on T | to]).

Lemma astabU : 'C(S :|: T | to) = 'C(S | to) :&: 'C(T | to).
Proof. by apply/setP=> a; rewrite !inE subUset; case: (a \in D). Qed.

Lemma astabsU : 'N(S | to) :&: 'N(T | to) \subset 'N(S :|: T | to).
Proof.
by rewrite -(astabsC S) -(astabsC T) -(astabsC (S :|: T)) setCU astabsI.
Qed.

Lemma astabsD : 'N(S | to) :&: 'N(T | to) \subset 'N(S :\: T| to).
Proof. by rewrite setDE -(astabsC T) astabsI. Qed.

Lemma actsI : [acts A, on S :&: T | to].
Proof. by apply: subset_trans (astabsI S T); rewrite subsetI AactS. Qed.

Lemma actsU : [acts A, on S :|: T | to].
Proof. by apply: subset_trans astabsU; rewrite subsetI AactS. Qed.

Lemma actsD : [acts A, on S :\: T | to].
Proof. by apply: subset_trans astabsD; rewrite subsetI AactS. Qed.

End ActsSetop.

Lemma acts_in_orbit A S x y :
  [acts A, on S | to] -> y \in orbit to A x -> x \in S -> y \in S.
Proof.
by move=> nSA/imsetP[a Aa ->{y}] Sx; rewrite (astabs_act _ (subsetP nSA a Aa)).
Qed.

Lemma subset_faithful A B S :
  B \subset A -> [faithful A, on S | to] -> [faithful B, on S | to].
Proof. by move=> sAB; apply: subset_trans; apply: setSI. Qed.

Section Reindex.

Variables (vT : Type) (idx : vT) (op : Monoid.com_law idx) (S : {set rT}).

Lemma reindex_astabs a F : a \in 'N(S | to) ->
  \big[op/idx]_(i in S) F i = \big[op/idx]_(i in S) F (to i a).
Proof.
move=> nSa; rewrite (reindex_inj (act_inj a)); apply: eq_bigl => x.
exact: astabs_act.
Qed.

Lemma reindex_acts A a F : [acts A, on S | to] -> a \in A ->
  \big[op/idx]_(i in S) F i = \big[op/idx]_(i in S) F (to i a).
Proof. by move=> nSA /(subsetP nSA); apply: reindex_astabs. Qed.

End Reindex.

End RawAction.

Arguments act_inj {aT D rT} to a [x1 x2] : rename.

Notation "to ^*" := (set_action to) : action_scope.

Arguments orbitP {aT D rT to A x y}.
Arguments afixP {aT D rT to A x}.
Arguments afix1P {aT D rT to a x}.

Arguments reindex_astabs [aT D rT] to [vT idx op S] a [F].
Arguments reindex_acts [aT D rT] to [vT idx op S A a F].

Section PartialAction.
(* Lemmas that require a (partial) group domain. *)

Variables (aT : finGroupType) (D : {group aT}) (rT : finType).
Variable to : action D rT.

Implicit Types a : aT.
Implicit Types x y : rT.
Implicit Types A B : {set aT}.
Implicit Types G H : {group aT}.
Implicit Types S : {set rT}.

Lemma act1 x : to x 1 = x.
Proof. by apply: (act_inj to 1); rewrite -actMin ?mulg1. Qed.

Lemma actKin : {in D, right_loop invg to}.
Proof. by move=> a Da /= x; rewrite -actMin ?groupV // mulgV act1. Qed.

Lemma actKVin : {in D, rev_right_loop invg to}.
Proof. by move=> a Da /= x; rewrite -{2}(invgK a) actKin ?groupV. Qed.

Lemma setactVin S a : a \in D -> to^* S a^-1 = to^~ a @^-1: S.
Proof.
by move=> Da; apply: can2_imset_pre; [apply: actKVin | apply: actKin].
Qed.

Lemma actXin x a i : a \in D -> to x (a ^+ i) = iter i (to^~ a) x.
Proof.
move=> Da; elim: i => /= [|i <-]; first by rewrite act1.
by rewrite expgSr actMin ?groupX.
Qed.

Lemma afix1 : 'Fix_to(1) = setT.
Proof. by apply/setP=> x; rewrite !inE sub1set inE act1 eqxx. Qed.

Lemma afixD1 G : 'Fix_to(G^#) = 'Fix_to(G).
Proof. by rewrite -{2}(setD1K (group1 G)) afixU afix1 setTI. Qed.

Lemma orbit_refl G x : x \in orbit to G x.
Proof. by rewrite -{1}[x]act1 mem_orbit. Qed.

Local Notation orbit_rel A := (fun x y => x \in orbit to A y).

Lemma contra_orbit G x y : x \notin orbit to G y -> x != y.
Proof. by apply: contraNneq => ->; apply: orbit_refl. Qed.

Lemma orbit_in_sym G : G \subset D -> symmetric (orbit_rel G).
Proof.
move=> sGD; apply: symmetric_from_pre => x y /imsetP[a Ga].
by move/(canLR (actKin (subsetP sGD a Ga))) <-; rewrite mem_orbit ?groupV.
Qed.

Lemma orbit_in_trans G : G \subset D -> transitive (orbit_rel G).
Proof.
move=> sGD _ _ z /imsetP[a Ga ->] /imsetP[b Gb ->].
by rewrite -actMin ?mem_orbit ?groupM // (subsetP sGD).
Qed.

Lemma orbit_in_eqP G x y :
  G \subset D -> reflect (orbit to G x = orbit to G y) (x \in orbit to G y).
Proof.
move=> sGD; apply: (iffP idP) => [yGx|<-]; last exact: orbit_refl.
by apply/setP=> z; apply/idP/idP=> /orbit_in_trans-> //; rewrite orbit_in_sym.
Qed.

Lemma orbit_in_transl G x y z :
    G \subset D -> y \in orbit to G x ->
  (y \in orbit to G z) = (x \in orbit to G z).
Proof.
by move=> sGD Gxy; rewrite !(orbit_in_sym sGD _ z) (orbit_in_eqP y x sGD Gxy).
Qed.

Lemma orbit_act_in x a G :
  G \subset D -> a \in G -> orbit to G (to x a) = orbit to G x.
Proof. by move=> sGD /mem_orbit/orbit_in_eqP->. Qed.

Lemma orbit_actr_in x a G y :
  G \subset D -> a \in G -> (to y a \in orbit to G x) = (y \in orbit to G x).
Proof. by move=> sGD /mem_orbit/orbit_in_transl->. Qed.

Lemma orbit_inv_in A x y :
  A \subset D -> (y \in orbit to A^-1 x) = (x \in orbit to A y).
Proof.
move/subsetP=> sAD; apply/imsetP/imsetP=> [] [a Aa ->].
  by exists a^-1; rewrite -?mem_invg ?actKin // -groupV sAD -?mem_invg.
by exists a^-1; rewrite ?memV_invg ?actKin // sAD.
Qed.

Lemma orbit_lcoset_in A a x :
    A \subset D -> a \in D ->
  orbit to (a *: A) x = orbit to A (to x a).
Proof.
move/subsetP=> sAD Da; apply/setP=> y; apply/imsetP/imsetP=> [] [b Ab ->{y}].
  by exists (a^-1 * b); rewrite -?actMin ?mulKVg // ?sAD -?mem_lcoset.
by exists (a * b); rewrite ?mem_mulg ?set11 ?actMin // sAD.
Qed.

Lemma orbit_rcoset_in A a x y :
    A \subset D -> a \in D ->
  (to y a \in orbit to (A :* a) x) = (y \in orbit to A x).
Proof.
move=> sAD Da; rewrite -orbit_inv_in ?mul_subG ?sub1set // invMg.
by rewrite invg_set1 orbit_lcoset_in ?inv_subG ?groupV ?actKin ?orbit_inv_in.
Qed.

Lemma orbit_conjsg_in A a x y :
    A \subset D -> a \in D ->
  (to y a \in orbit to (A :^ a) (to x a)) = (y \in orbit to A x).
Proof.
move=> sAD Da; rewrite conjsgE.
by rewrite orbit_lcoset_in ?groupV ?mul_subG ?sub1set ?actKin ?orbit_rcoset_in.
Qed.

Lemma orbit1P G x : reflect (orbit to G x = [set x]) (x \in 'Fix_to(G)).
Proof.
apply: (iffP afixP) => [xfix | xfix a Ga].
  apply/eqP; rewrite eq_sym eqEsubset sub1set -{1}[x]act1 mem_imset //=.
  by apply/subsetP=> y; case/imsetP=> a Ga ->; rewrite inE xfix.
by apply/set1P; rewrite -xfix mem_imset.
Qed.

Lemma card_orbit1 G x : #|orbit to G x| = 1%N -> orbit to G x = [set x].
Proof.
move=> orb1; apply/eqP; rewrite eq_sym eqEcard {}orb1 cards1.
by rewrite sub1set orbit_refl.
Qed.

Lemma orbit_partition G S :
  [acts G, on S | to] -> partition (orbit to G @: S) S.
Proof.
move=> actsGS; have sGD := acts_dom actsGS.
have eqiG: {in S & &, equivalence_rel [rel x y | y \in orbit to G x]}.
  by move=> x y z * /=; rewrite orbit_refl; split=> // /orbit_in_eqP->.
congr (partition _ _): (equivalence_partitionP eqiG).
apply: eq_in_imset => x Sx; apply/setP=> y.
by rewrite inE /= andb_idl // => /acts_in_orbit->.
Qed.

Definition orbit_transversal A S := transversal (orbit to A @: S) S.

Lemma orbit_transversalP G S (P := orbit to G @: S)
                             (X := orbit_transversal G S) :
  [acts G, on S | to] ->
 [/\ is_transversal X P S, X \subset S,
     {in X &, forall x y, (y \in orbit to G x) = (x == y)}
   & forall x, x \in S -> exists2 a, a \in G & to x a \in X].
Proof.
move/orbit_partition; rewrite -/P => partP.
have [/eqP defS tiP _] := and3P partP.
have trXP: is_transversal X P S := transversalP partP.
have sXS: X \subset S := transversal_sub trXP.
split=> // [x y Xx Xy /= | x Sx].
  have Sx := subsetP sXS x Xx.
  rewrite -(inj_in_eq (pblock_inj trXP)) // eq_pblock ?defS //.
  by rewrite (def_pblock tiP (mem_imset _ Sx)) ?orbit_refl.
have /imsetP[y Xy defxG]: orbit to G x \in pblock P @: X.
  by rewrite (pblock_transversal trXP) ?mem_imset.
suffices /orbitP[a Ga def_y]: y \in orbit to G x by exists a; rewrite ?def_y.
by rewrite defxG mem_pblock defS (subsetP sXS).
Qed.

Lemma group_set_astab S : group_set 'C(S | to).
Proof.
apply/group_setP; split=> [|a b cSa cSb].
  by rewrite !inE group1; apply/subsetP=> x _; rewrite inE act1.
rewrite !inE groupM ?(@astab_dom _ _ _ to S) //; apply/subsetP=> x Sx.
by rewrite inE actMin ?(@astab_dom _ _ _ to S) ?(astab_act _ Sx).
Qed.

Canonical astab_group S := group (group_set_astab S).

Lemma afix_gen_in A : A \subset D -> 'Fix_to(<<A>>) = 'Fix_to(A).
Proof.
move=> sAD; apply/eqP; rewrite eqEsubset afixS ?sub_gen //=.
by rewrite -astabCin gen_subG ?astabCin.
Qed.

Lemma afix_cycle_in a : a \in D -> 'Fix_to(<[a]>) = 'Fix_to[a].
Proof. by move=> Da; rewrite afix_gen_in ?sub1set. Qed.

Lemma afixYin A B :
  A \subset D -> B \subset D -> 'Fix_to(A <*> B) = 'Fix_to(A) :&: 'Fix_to(B).
Proof. by move=> sAD sBD; rewrite afix_gen_in ?afixU // subUset sAD. Qed.

Lemma afixMin G H :
  G \subset D -> H \subset D -> 'Fix_to(G * H) = 'Fix_to(G) :&: 'Fix_to(H).
Proof.
by move=> sGD sHD; rewrite -afix_gen_in ?mul_subG // genM_join afixYin.
Qed.

Lemma sub_astab1_in A x :
  A \subset D -> (A \subset 'C[x | to]) = (x \in 'Fix_to(A)).
Proof. by move=> sAD; rewrite astabCin ?sub1set. Qed.

Lemma group_set_astabs S : group_set 'N(S | to).
Proof.
apply/group_setP; split=> [|a b cSa cSb].
  by rewrite !inE group1; apply/subsetP=> x Sx; rewrite inE act1.
rewrite !inE groupM ?(@astabs_dom _ _ _ to S) //; apply/subsetP=> x Sx.
by rewrite inE actMin ?(@astabs_dom _ _ _ to S) ?astabs_act.
Qed.

Canonical astabs_group S := group (group_set_astabs S).

Lemma astab_norm S : 'N(S | to) \subset 'N('C(S | to)).
Proof.
apply/subsetP=> a nSa; rewrite inE sub_conjg; apply/subsetP=> b cSb.
have [Da Db] := (astabs_dom nSa, astab_dom cSb).
rewrite mem_conjgV !inE groupJ //; apply/subsetP=> x Sx.
rewrite inE !actMin ?groupM ?groupV //.
by rewrite (astab_act cSb) ?actKVin ?astabs_act ?groupV.
Qed.

Lemma astab_normal S : 'C(S | to) <| 'N(S | to).
Proof. by rewrite /normal astab_sub astab_norm. Qed.

Lemma acts_sub_orbit G S x :
  [acts G, on S | to] -> (orbit to G x \subset S) = (x \in S).
Proof.
move/acts_act=> GactS.
apply/subsetP/idP=> [| Sx y]; first by apply; apply: orbit_refl.
by case/orbitP=> a Ga <-{y}; rewrite GactS.
Qed.

Lemma acts_orbit G x : G \subset D -> [acts G, on orbit to G x | to].
Proof.
move/subsetP=> sGD; apply/subsetP=> a Ga; rewrite !inE sGD //.
apply/subsetP=> _ /imsetP[b Gb ->].
by rewrite inE -actMin ?sGD // mem_imset ?groupM.
Qed.

Lemma acts_subnorm_fix A : [acts 'N_D(A), on 'Fix_to(D :&: A) | to].
Proof.
apply/subsetP=> a nAa; have [Da _] := setIP nAa; rewrite !inE Da.
apply/subsetP=> x Cx; rewrite inE; apply/afixP=> b DAb.
have [Db _]:= setIP DAb; rewrite -actMin // conjgCV  actMin ?groupJ ?groupV //.
by rewrite /= (afixP Cx) // memJ_norm // groupV (subsetP (normsGI _ _) _ nAa).
Qed.

Lemma atrans_orbit G x : [transitive G, on orbit to G x | to].
Proof. by apply: mem_imset; apply: orbit_refl. Qed.

Section OrbitStabilizer.

Variables (G : {group aT}) (x : rT).
Hypothesis sGD : G \subset D.
Let ssGD := subsetP sGD.

Lemma amove_act a : a \in G -> amove to G x (to x a) = 'C_G[x | to] :* a.
Proof.
move=> Ga; apply/setP=> b; have Da := ssGD Ga.
rewrite mem_rcoset !(inE, sub1set) !groupMr ?groupV //.
by case Gb: (b \in G); rewrite //= actMin ?groupV ?ssGD ?(canF_eq (actKVin Da)).
Qed.

Lemma amove_orbit : amove to G x @: orbit to G x = rcosets 'C_G[x | to] G.
Proof.
apply/setP => Ha; apply/imsetP/rcosetsP=> [[y] | [a Ga ->]].
  by case/imsetP=> b Gb -> ->{Ha y}; exists b => //; rewrite amove_act.
by rewrite -amove_act //; exists (to x a); first apply: mem_orbit.
Qed.

Lemma amoveK :
  {in orbit to G x, cancel (amove to G x) (fun Ca => to x (repr Ca))}.
Proof.
move=> _ /orbitP[a Ga <-]; rewrite amove_act //= -[G :&: _]/(gval _).
case: repr_rcosetP => b; rewrite !(inE, sub1set)=> /and3P[Gb _ xbx].
by rewrite actMin ?ssGD ?(eqP xbx).
Qed.

Lemma orbit_stabilizer :
  orbit to G x = [set to x (repr Ca) | Ca in rcosets 'C_G[x | to] G].
Proof.
rewrite -amove_orbit -imset_comp /=; apply/setP=> z.
by apply/idP/imsetP=> [xGz | [y xGy ->]]; first exists z; rewrite /= ?amoveK.
Qed.

Lemma act_reprK :
  {in rcosets 'C_G[x | to] G, cancel (to x \o repr) (amove to G x)}.
Proof.
move=> _ /rcosetsP[a Ga ->] /=; rewrite amove_act ?rcoset_repr //.
rewrite -[G :&: _]/(gval _); case: repr_rcosetP => b /setIP[Gb _].
exact: groupM.
Qed.

End OrbitStabilizer.

Lemma card_orbit_in G x : G \subset D -> #|orbit to G x| = #|G : 'C_G[x | to]|.
Proof.
move=> sGD; rewrite orbit_stabilizer 1?card_in_imset //.
exact: can_in_inj (act_reprK _).
Qed.

Lemma card_orbit_in_stab G x :
  G \subset D -> (#|orbit to G x| * #|'C_G[x | to]|)%N = #|G|.
Proof. by move=> sGD; rewrite mulnC card_orbit_in ?Lagrange ?subsetIl. Qed.

Lemma acts_sum_card_orbit G S :
  [acts G, on S | to] -> \sum_(T in orbit to G @: S) #|T| = #|S|.
Proof. by move/orbit_partition/card_partition. Qed.

Lemma astab_setact_in S a : a \in D -> 'C(to^* S a | to) = 'C(S | to) :^ a.
Proof.
move=> Da; apply/setP=> b; rewrite mem_conjg !inE -mem_conjg conjGid //.
apply: andb_id2l => Db; rewrite sub_imset_pre; apply: eq_subset_r => x.
by rewrite !inE !actMin ?groupM ?groupV // invgK (canF_eq (actKVin Da)).
Qed.

Lemma astab1_act_in x a : a \in D -> 'C[to x a | to] = 'C[x | to] :^ a.
Proof. by move=> Da; rewrite -astab_setact_in // /setact imset_set1. Qed.

Theorem Frobenius_Cauchy G S : [acts G, on S | to] ->
  \sum_(a in G) #|'Fix_(S | to)[a]| = (#|orbit to G @: S| * #|G|)%N.
Proof.
move=> GactS; have sGD := acts_dom GactS.
transitivity (\sum_(a in G) \sum_(x in 'Fix_(S | to)[a]) 1%N).
  by apply: eq_bigr => a _; rewrite -sum1_card.
rewrite (exchange_big_dep (mem S)) /= => [|a x _]; last by case/setIP.
rewrite (set_partition_big _ (orbit_partition GactS)) -sum_nat_const /=.
apply: eq_bigr => _ /imsetP[x Sx ->].
rewrite -(card_orbit_in_stab x sGD) -sum_nat_const.
apply: eq_bigr => y; rewrite orbit_in_sym // => /imsetP[a Ga defx].
rewrite defx astab1_act_in ?(subsetP sGD) //.
rewrite -{2}(conjGid Ga) -conjIg cardJg -sum1_card setIA (setIidPl sGD).
by apply: eq_bigl => b; rewrite !(sub1set, inE) -(acts_act GactS Ga) -defx Sx.
Qed.

Lemma atrans_dvd_index_in G S :
  G \subset D -> [transitive G, on S | to] -> #|S| %| #|G : 'C_G(S | to)|.
Proof.
move=> sGD /imsetP[x Sx {1}->]; rewrite card_orbit_in //.
by rewrite indexgS // setIS // astabS // sub1set.
Qed.

Lemma atrans_dvd_in G S :
  G \subset D -> [transitive G, on S | to] -> #|S| %| #|G|.
Proof.
move=> sGD transG; apply: dvdn_trans (atrans_dvd_index_in sGD transG) _.
exact: dvdn_indexg.
Qed.

Lemma atransPin G S :
     G \subset D -> [transitive G, on S | to] ->
  forall x, x \in S -> orbit to G x = S.
Proof. by move=> sGD /imsetP[y _ ->] x; apply/orbit_in_eqP. Qed.

Lemma atransP2in G S :
    G \subset D -> [transitive G, on S | to] ->
  {in S &, forall x y, exists2 a, a \in G & y = to x a}.
Proof. by move=> sGD transG x y /(atransPin sGD transG) <- /imsetP. Qed.

Lemma atrans_acts_in G S :
  G \subset D -> [transitive G, on S | to] -> [acts G, on S | to].
Proof.
move=> sGD transG; apply/subsetP=> a Ga; rewrite !inE (subsetP sGD) //.
by apply/subsetP=> x /(atransPin sGD transG) <-; rewrite inE mem_imset.
Qed.

Lemma subgroup_transitivePin G H S x :
     x \in S -> H \subset G -> G \subset D -> [transitive G, on S | to] ->
  reflect ('C_G[x | to] * H = G) [transitive H, on S | to].
Proof.
move=> Sx sHG sGD trG; have sHD := subset_trans sHG sGD.
apply: (iffP idP) => [trH | defG].
  rewrite group_modr //; apply/setIidPl/subsetP=> a Ga.
  have Sxa: to x a \in S by rewrite (acts_act (atrans_acts_in sGD trG)).
  have [b Hb xab]:= atransP2in sHD trH Sxa Sx.
  have Da := subsetP sGD a Ga; have Db := subsetP sHD b Hb.
  rewrite -(mulgK b a) mem_mulg ?groupV // !inE groupM //= sub1set inE.
  by rewrite actMin -?xab.
apply/imsetP; exists x => //; apply/setP=> y; rewrite -(atransPin sGD trG Sx).
apply/imsetP/imsetP=> [] [a]; last by exists a; first apply: (subsetP sHG).
rewrite -defG => /imset2P[c b /setIP[_ cxc] Hb ->] ->.
exists b; rewrite ?actMin ?(astab_dom cxc) ?(subsetP sHD) //.
by rewrite (astab_act cxc) ?inE.
Qed.

End PartialAction.

Arguments orbit_transversal {aT D%g rT} to%act A%g S%g.
Arguments orbit_in_eqP {aT D rT to G x y}.
Arguments orbit1P {aT D rT to G x}.
Arguments contra_orbit [aT D rT] to G [x y].

Notation "''C' ( S | to )" := (astab_group to S) : Group_scope.
Notation "''C_' A ( S | to )" := (setI_group A 'C(S | to)) : Group_scope.
Notation "''C_' ( A ) ( S | to )" := (setI_group A 'C(S | to))
  (only parsing) : Group_scope.
Notation "''C' [ x | to ]" := (astab_group to [set x%g]) : Group_scope.
Notation "''C_' A [ x | to ]" := (setI_group A 'C[x | to]) : Group_scope.
Notation "''C_' ( A ) [ x | to ]" := (setI_group A 'C[x | to])
  (only parsing) : Group_scope.
Notation "''N' ( S | to )" := (astabs_group to S) : Group_scope.
Notation "''N_' A ( S | to )" := (setI_group A 'N(S | to)) : Group_scope.

Section TotalActions.
(* These lemmas are only established for total actions (domain = [set: rT]) *)

Variable (aT : finGroupType) (rT : finType).

Variable to : {action aT &-> rT}.

Implicit Types (a b : aT) (x y z : rT) (A B : {set aT}) (G H : {group aT}).
Implicit Type S : {set rT}.

Lemma actM x a b : to x (a * b) = to (to x a) b.
Proof. by rewrite actMin ?inE. Qed.

Lemma actK : right_loop invg to.
Proof. by move=> a; apply: actKin; rewrite inE. Qed.

Lemma actKV : rev_right_loop invg to.
Proof. by move=> a; apply: actKVin; rewrite inE. Qed.

Lemma actX x a n : to x (a ^+ n) = iter n (to^~ a) x.
Proof. by elim: n => [|n /= <-]; rewrite ?act1 // -actM expgSr. Qed.

Lemma actCJ a b x : to (to x a) b = to (to x b) (a ^ b).
Proof. by rewrite !actM actK. Qed.

Lemma actCJV a b x : to (to x a) b = to (to x (b ^ a^-1)) a.
Proof. by rewrite (actCJ _ a) conjgKV. Qed.

Lemma orbit_sym G x y : (x \in orbit to G y) = (y \in orbit to G x).
Proof. exact/orbit_in_sym/subsetT. Qed.

Lemma orbit_trans G x y z :
  x \in orbit to G y -> y \in orbit to G z -> x \in orbit to G z.
Proof. exact/orbit_in_trans/subsetT. Qed.

Lemma orbit_eqP G x y :
  reflect (orbit to G x = orbit to G y) (x \in orbit to G y).
Proof. exact/orbit_in_eqP/subsetT. Qed.

Lemma orbit_transl G x y z :
  y \in orbit to G x -> (y \in orbit to G z) = (x \in orbit to G z).
Proof. exact/orbit_in_transl/subsetT. Qed.

Lemma orbit_act G a x: a \in G -> orbit to G (to x a) = orbit to G x.
Proof. exact/orbit_act_in/subsetT. Qed.
  
Lemma orbit_actr G a x y :
  a \in G -> (to y a \in orbit to G x) = (y \in orbit to G x).
Proof. by move/mem_orbit/orbit_transl; apply. Qed.

Lemma orbit_eq_mem G x y :
  (orbit to G x == orbit to G y) = (x \in orbit to G y).
Proof. exact: sameP eqP (orbit_eqP G x y). Qed.

Lemma orbit_inv A x y : (y \in orbit to A^-1 x) = (x \in orbit to A y).
Proof. by rewrite orbit_inv_in ?subsetT. Qed.

Lemma orbit_lcoset A a x : orbit to (a *: A) x = orbit to A (to x a).
Proof. by rewrite orbit_lcoset_in ?subsetT ?inE. Qed.

Lemma orbit_rcoset A a x y :
  (to y a \in orbit to (A :* a) x) = (y \in orbit to A x).
Proof. by rewrite orbit_rcoset_in ?subsetT ?inE. Qed.

Lemma orbit_conjsg A a x y :
  (to y a \in orbit to (A :^ a) (to x a)) = (y \in orbit to A x).
Proof. by rewrite orbit_conjsg_in ?subsetT ?inE. Qed.

Lemma astabP S a : reflect (forall x, x \in S -> to x a = x) (a \in 'C(S | to)).
Proof.
apply: (iffP idP) => [cSa x|cSa]; first exact: astab_act.
by rewrite !inE; apply/subsetP=> x Sx; rewrite inE cSa.
Qed.

Lemma astab1P x a : reflect (to x a = x) (a \in 'C[x | to]).
Proof. by rewrite !inE sub1set inE; apply: eqP. Qed.

Lemma sub_astab1 A x : (A \subset 'C[x | to]) = (x \in 'Fix_to(A)).
Proof. by rewrite sub_astab1_in ?subsetT. Qed.

Lemma astabC A S : (A \subset 'C(S | to)) = (S \subset 'Fix_to(A)).
Proof. by rewrite astabCin ?subsetT. Qed.

Lemma afix_cycle a : 'Fix_to(<[a]>) = 'Fix_to[a].
Proof. by rewrite afix_cycle_in ?inE. Qed.

Lemma afix_gen A : 'Fix_to(<<A>>) = 'Fix_to(A).
Proof. by rewrite afix_gen_in ?subsetT. Qed.

Lemma afixM G H : 'Fix_to(G * H) = 'Fix_to(G) :&: 'Fix_to(H).
Proof. by rewrite afixMin ?subsetT. Qed.

Lemma astabsP S a :
  reflect (forall x, (to x a \in S) = (x \in S)) (a \in 'N(S | to)).
Proof.
apply: (iffP idP) => [nSa x|nSa]; first exact: astabs_act.
by rewrite !inE; apply/subsetP=> x; rewrite inE nSa.
Qed.

Lemma card_orbit G x : #|orbit to G x| = #|G : 'C_G[x | to]|.
Proof. by rewrite card_orbit_in ?subsetT. Qed.

Lemma dvdn_orbit G x : #|orbit to G x| %| #|G|.
Proof. by rewrite card_orbit dvdn_indexg. Qed.

Lemma card_orbit_stab G x : (#|orbit to G x| * #|'C_G[x | to]|)%N = #|G|.
Proof. by rewrite mulnC card_orbit Lagrange ?subsetIl. Qed.

Lemma actsP A S : reflect {acts A, on S | to} [acts A, on S | to].
Proof.
apply: (iffP idP) => [nSA x|nSA]; first exact: acts_act.
by apply/subsetP=> a Aa; rewrite !inE; apply/subsetP=> x; rewrite inE nSA.
Qed.
Arguments actsP {A S}.

Lemma setact_orbit A x b : to^* (orbit to A x) b = orbit to (A :^ b) (to x b).
Proof.
apply/setP=> y; apply/idP/idP=> /imsetP[_ /imsetP[a Aa ->] ->{y}].
  by rewrite actCJ mem_orbit ?memJ_conjg.
by rewrite -actCJ mem_setact ?mem_orbit.
Qed.

Lemma astab_setact S a : 'C(to^* S a | to) = 'C(S | to) :^ a.
Proof.
apply/setP=> b; rewrite mem_conjg.
apply/astabP/astabP=> stab x => [Sx|].
  by rewrite conjgE invgK !actM stab ?actK //; apply/imsetP; exists x.
by case/imsetP=> y Sy ->{x}; rewrite -actM conjgCV actM stab.
Qed.

Lemma astab1_act x a : 'C[to x a | to] = 'C[x | to] :^ a.
Proof. by rewrite -astab_setact /setact imset_set1. Qed.

Lemma atransP G S : [transitive G, on S | to] ->
  forall x, x \in S -> orbit to G x = S.
Proof. by case/imsetP=> x _ -> y; apply/orbit_eqP. Qed.

Lemma atransP2 G S : [transitive G, on S | to] ->
  {in S &, forall x y, exists2 a, a \in G & y = to x a}.
Proof. by move=> GtrS x y /(atransP GtrS) <- /imsetP. Qed.

Lemma atrans_acts G S : [transitive G, on S | to] -> [acts G, on S | to].
Proof.
move=> GtrS; apply/subsetP=> a Ga; rewrite !inE.
by apply/subsetP=> x /(atransP GtrS) <-; rewrite inE mem_imset.
Qed.

Lemma atrans_supgroup G H S :
    G \subset H -> [transitive G, on S | to] ->
  [transitive H, on S | to] = [acts H, on S | to].
Proof.
move=> sGH trG; apply/idP/idP=> [|actH]; first exact: atrans_acts.
case/imsetP: trG => x Sx defS; apply/imsetP; exists x => //.
by apply/eqP; rewrite eqEsubset acts_sub_orbit ?Sx // defS imsetS.
Qed.

Lemma atrans_acts_card G S :
  [transitive G, on S | to] =
     [acts G, on S | to] && (#|orbit to G @: S| == 1%N).
Proof.
apply/idP/andP=> [GtrS | [nSG]].
  split; first exact: atrans_acts.
  rewrite ((_ @: S =P [set S]) _) ?cards1 // eqEsubset sub1set.
  apply/andP; split=> //; apply/subsetP=> _ /imsetP[x Sx ->].
  by rewrite inE (atransP GtrS).
rewrite eqn_leq andbC lt0n => /andP[/existsP[X /imsetP[x Sx X_Gx]]].
rewrite (cardD1 X) {X}X_Gx mem_imset // ltnS leqn0 => /eqP GtrS.
apply/imsetP; exists x => //; apply/eqP.
rewrite eqEsubset acts_sub_orbit // Sx andbT.
apply/subsetP=> y Sy; have:= card0_eq GtrS (orbit to G y).
by rewrite !inE /= mem_imset // andbT => /eqP <-; apply: orbit_refl.
Qed.

Lemma atrans_dvd G S : [transitive G, on S | to] -> #|S| %| #|G|.
Proof. by case/imsetP=> x _ ->; apply: dvdn_orbit. Qed.

(* This is Aschbacher (5.2) *)
Lemma acts_fix_norm A B : A \subset 'N(B) -> [acts A, on 'Fix_to(B) | to].
Proof.
move=> nAB; have:= acts_subnorm_fix to B; rewrite !setTI.
exact: subset_trans.
Qed.

Lemma faithfulP A S :
  reflect (forall a, a \in A -> {in S, to^~ a =1 id} -> a = 1)
          [faithful A, on S | to].
Proof.
apply: (iffP subsetP) => [Cto1 a Aa Ca | Cto1 a].
  by apply/set1P; rewrite Cto1 // inE Aa; apply/astabP.
by case/setIP=> Aa /astabP Ca; apply/set1P; apply: Cto1.
Qed.

(* This is the first part of Aschbacher (5.7) *)
Lemma astab_trans_gcore G S u :
  [transitive G, on S | to] -> u \in S -> 'C(S | to) = gcore 'C[u | to] G.
Proof.
move=> transG Su; apply/eqP; rewrite eqEsubset.
rewrite gcore_max ?astabS ?sub1set //=; last first.
  exact: subset_trans (atrans_acts transG) (astab_norm _ _).
apply/subsetP=> x cSx; apply/astabP=> uy.
case/(atransP2 transG Su) => y Gy ->{uy}.
by apply/astab1P; rewrite astab1_act (bigcapP cSx).
Qed.

(* This is Aschbacher (5.20) *)
Theorem subgroup_transitiveP G H S x :
     x \in S -> H \subset G -> [transitive G, on S | to] ->
  reflect ('C_G[x | to] * H = G) [transitive H, on S | to].
Proof. by move=> Sx sHG; apply: subgroup_transitivePin (subsetT G). Qed.

(* This is Aschbacher (5.21) *)
Lemma trans_subnorm_fixP x G H S :
  let C := 'C_G[x | to] in let T := 'Fix_(S | to)(H) in
    [transitive G, on S | to] -> x \in S -> H \subset C ->
  reflect ((H :^: G) ::&: C = H :^: C) [transitive 'N_G(H), on T | to].
Proof.
move=> C T trGS Sx sHC; have actGS := acts_act (atrans_acts trGS).
have:= sHC; rewrite subsetI sub_astab1 => /andP[sHG cHx].
have Tx: x \in T by rewrite inE Sx.
apply: (iffP idP) => [trN | trC].
  apply/setP=> Ha; apply/setIdP/imsetP=> [[]|[a Ca ->{Ha}]]; last first.
    by rewrite conj_subG //; case/setIP: Ca => Ga _; rewrite mem_imset.
  case/imsetP=> a Ga ->{Ha}; rewrite subsetI !sub_conjg => /andP[_ sHCa].
  have Txa: to x a^-1 \in T.
    by rewrite inE -sub_astab1 astab1_act actGS ?Sx ?groupV.
  have [b] := atransP2 trN Tx Txa; case/setIP=> Gb nHb cxba.
  exists (b * a); last by rewrite conjsgM (normP nHb).
  by rewrite inE groupM //; apply/astab1P; rewrite actM -cxba actKV.
apply/imsetP; exists x => //; apply/setP=> y; apply/idP/idP=> [Ty|].
  have [Sy cHy]:= setIP Ty; have [a Ga defy] := atransP2 trGS Sx Sy.
  have: H :^ a^-1 \in H :^: C.
    rewrite -trC inE subsetI mem_imset 1?conj_subG ?groupV // sub_conjgV.
    by rewrite -astab1_act -defy sub_astab1.
  case/imsetP=> b /setIP[Gb /astab1P cxb] defHb.
  rewrite defy -{1}cxb -actM mem_orbit // inE groupM //.
  by apply/normP; rewrite conjsgM -defHb conjsgKV.
case/imsetP=> a /setIP[Ga nHa] ->{y}.
by rewrite inE actGS // Sx (acts_act (acts_fix_norm _) nHa).
Qed.

End TotalActions.

Arguments astabP {aT rT to S a}.
Arguments orbit_eqP {aT rT to G x y}.
Arguments astab1P {aT rT to x a}.
Arguments astabsP {aT rT to S a}.
Arguments atransP {aT rT to G S}.
Arguments actsP {aT rT to A S}.
Arguments faithfulP {aT rT to A S}.

Section Restrict.

Variables (aT : finGroupType) (D : {set aT}) (rT : Type).
Variables (to : action D rT) (A : {set aT}).

Definition ract of A \subset D := act to.

Variable sAD : A \subset D.

Lemma ract_is_action : is_action A (ract sAD).
Proof.
rewrite /ract; case: to => f [injf fM].
by split=> // x; apply: (sub_in2 (subsetP sAD)).
Qed.

Canonical raction := Action ract_is_action.

Lemma ractE : raction =1 to. Proof. by []. Qed.

(* Other properties of raction need rT : finType; we defer them *)
(* until after the definition of actperm.                       *)

End Restrict.

Notation "to \ sAD" := (raction to sAD) (at level 50) : action_scope.

Section ActBy.

Variables (aT : finGroupType) (D : {set aT}) (rT : finType).

Definition actby_cond (A : {set aT}) R (to : action D rT) : Prop :=
  [acts A, on R | to].

Definition actby A R to of actby_cond A R to :=
  fun x a => if (x \in R) && (a \in A) then to x a else x.

Variables (A : {group aT}) (R : {set rT}) (to : action D rT).
Hypothesis nRA : actby_cond A R to.

Lemma actby_is_action : is_action A (actby nRA).
Proof.
rewrite /actby; split=> [a x y | x a b Aa Ab /=]; last first.
  rewrite Aa Ab groupM // !andbT actMin ?(subsetP (acts_dom nRA)) //.
  by case Rx: (x \in R); rewrite ?(acts_act nRA) ?Rx.
case Aa: (a \in A); rewrite ?andbF ?andbT //.
case Rx: (x \in R); case Ry: (y \in R) => // eqxy; first exact: act_inj eqxy.
  by rewrite -eqxy (acts_act nRA Aa) Rx in Ry.
by rewrite eqxy (acts_act nRA Aa) Ry in Rx.
Qed.

Canonical action_by := Action actby_is_action.
Local Notation "<[nRA]>" := action_by : action_scope.

Lemma actbyE x a : x \in R -> a \in A -> <[nRA]>%act x a = to x a.
Proof. by rewrite /= /actby => -> ->. Qed.

Lemma afix_actby B : 'Fix_<[nRA]>(B) = ~: R :|: 'Fix_to(A :&: B).
Proof.
apply/setP=> x; rewrite !inE /= /actby.
case: (x \in R); last by apply/subsetP=> a _; rewrite !inE.
apply/subsetP/subsetP=> [cBx a | cABx a Ba]; rewrite !inE.
  by case/andP=> Aa /cBx; rewrite inE Aa.
by case: ifP => //= Aa; have:= cABx a; rewrite !inE Aa => ->.
Qed.

Lemma astab_actby S : 'C(S | <[nRA]>) = 'C_A(R :&: S | to).
Proof.
apply/setP=> a; rewrite setIA (setIidPl (acts_dom nRA)) !inE.
case Aa: (a \in A) => //=; apply/subsetP/subsetP=> cRSa x => [|Sx].
  by case/setIP=> Rx /cRSa; rewrite !inE actbyE.
by have:= cRSa x; rewrite !inE /= /actby Aa Sx; case: (x \in R) => //; apply.
Qed.

Lemma astabs_actby S : 'N(S | <[nRA]>) = 'N_A(R :&: S | to).
Proof.
apply/setP=> a; rewrite setIA (setIidPl (acts_dom nRA)) !inE.
case Aa: (a \in A) => //=; apply/subsetP/subsetP=> nRSa x => [|Sx].
  by case/setIP=> Rx /nRSa; rewrite !inE actbyE ?(acts_act nRA) ?Rx.
have:= nRSa x; rewrite !inE /= /actby Aa Sx ?(acts_act nRA) //.
by case: (x \in R) => //; apply.
Qed.

Lemma acts_actby (B : {set aT}) S :
  [acts B, on S | <[nRA]>] = (B \subset A) && [acts B, on R :&: S | to].
Proof. by rewrite astabs_actby subsetI. Qed.

End ActBy.

Notation "<[ nRA ] >" := (action_by nRA) : action_scope.

Section SubAction.

Variables (aT : finGroupType) (D : {group aT}).
Variables (rT : finType) (sP : pred rT) (sT : subFinType sP) (to : action D rT).
Implicit Type A : {set aT}.
Implicit Type u : sT.
Implicit Type S : {set sT}.

Definition subact_dom := 'N([set x | sP x] | to).
Canonical subact_dom_group := [group of subact_dom].

Implicit Type Na : {a | a \in subact_dom}.
Lemma sub_act_proof u Na : sP (to (val u) (val Na)).
Proof. by case: Na => a /= /(astabs_act (val u)); rewrite !inE valP. Qed.

Definition subact u a :=
  if insub a is Some Na then Sub _ (sub_act_proof u Na) else u.

Lemma val_subact u a :
  val (subact u a) = if a \in subact_dom then to (val u) a else val u.
Proof.
by rewrite /subact -if_neg; case: insubP => [Na|] -> //=; rewrite SubK => ->.
Qed.

Lemma subact_is_action : is_action subact_dom subact.
Proof.
split=> [a u v eq_uv | u a b Na Nb]; apply: val_inj.
  move/(congr1 val): eq_uv; rewrite !val_subact.
  by case: (a \in _); first move/act_inj.
have Da := astabs_dom Na; have Db := astabs_dom Nb.
by rewrite !val_subact Na Nb groupM ?actMin.
Qed.

Canonical subaction := Action subact_is_action.

Lemma astab_subact S : 'C(S | subaction) = subact_dom :&: 'C(val @: S | to).
Proof.
apply/setP=> a; rewrite inE in_setI; apply: andb_id2l => sDa.
have [Da _] := setIP sDa; rewrite !inE Da.
apply/subsetP/subsetP=> [cSa _ /imsetP[x Sx ->] | cSa x Sx]; rewrite !inE.
  by have:= cSa x Sx; rewrite inE -val_eqE val_subact sDa.
by have:= cSa _ (mem_imset val Sx); rewrite inE -val_eqE val_subact sDa.
Qed.

Lemma astabs_subact S : 'N(S | subaction) = subact_dom :&: 'N(val @: S | to).
Proof.
apply/setP=> a; rewrite inE in_setI; apply: andb_id2l => sDa.
have [Da _] := setIP sDa; rewrite !inE Da.
apply/subsetP/subsetP=> [nSa _ /imsetP[x Sx ->] | nSa x Sx]; rewrite !inE.
  by have:= nSa x Sx; rewrite inE => /(mem_imset val); rewrite val_subact sDa.
have:= nSa _ (mem_imset val Sx); rewrite inE => /imsetP[y Sy def_y].
by rewrite ((_ a =P y) _) // -val_eqE val_subact sDa def_y.
Qed.

Lemma afix_subact A :
  A \subset subact_dom -> 'Fix_subaction(A) = val @^-1: 'Fix_to(A).
Proof.
move/subsetP=> sAD; apply/setP=> u.
rewrite !inE !(sameP setIidPl eqP); congr (_ == A).
apply/setP=> a; rewrite !inE; apply: andb_id2l => Aa.
by rewrite -val_eqE val_subact sAD.

Qed.

End SubAction.

Notation "to ^?" := (subaction _ to)
  (at level 2, format "to ^?") : action_scope.

Section QuotientAction.

Variables (aT : finGroupType) (D : {group aT}) (rT : finGroupType).
Variables (to : action D rT) (H : {group rT}).

Definition qact_dom := 'N(rcosets H 'N(H) | to^*).
Canonical qact_dom_group := [group of qact_dom].

Local Notation subdom := (subact_dom (coset_range H)  to^*).
Fact qact_subdomE : subdom = qact_dom.
Proof. by congr 'N(_|_); apply/setP=> Hx; rewrite !inE genGid. Qed.
Lemma qact_proof : qact_dom \subset subdom.
Proof. by rewrite qact_subdomE. Qed.

Definition qact : coset_of H -> aT -> coset_of H := act (to^*^? \ qact_proof).

Canonical quotient_action := [action of qact].

Lemma acts_qact_dom : [acts qact_dom, on 'N(H) | to].
Proof.
apply/subsetP=> a nNa; rewrite !inE (astabs_dom nNa); apply/subsetP=> x Nx.
have: H :* x \in rcosets H 'N(H) by rewrite -rcosetE mem_imset.
rewrite inE -(astabs_act _ nNa) => /rcosetsP[y Ny defHy].
have: to x a \in H :* y by rewrite -defHy (mem_imset (to^~a)) ?rcoset_refl.
by apply: subsetP; rewrite mul_subG ?sub1set ?normG.
Qed.

Lemma qactEcond x a :
    x \in 'N(H) ->
  quotient_action (coset H x) a
    = coset H (if a \in qact_dom then to x a else x).
Proof.
move=> Nx; apply: val_inj; rewrite val_subact //= qact_subdomE.
have: H :* x \in rcosets H 'N(H) by rewrite -rcosetE mem_imset.
case nNa: (a \in _); rewrite // -(astabs_act _ nNa).
rewrite !val_coset ?(acts_act acts_qact_dom nNa) //=.
case/rcosetsP=> y Ny defHy; rewrite defHy; apply: rcoset_eqP.
by rewrite rcoset_sym -defHy (mem_imset (_^~_)) ?rcoset_refl.
Qed.

Lemma qactE x a :
    x \in 'N(H) -> a \in qact_dom ->
  quotient_action (coset H x) a = coset H (to x a).
Proof. by move=> Nx nNa; rewrite qactEcond ?nNa. Qed.

Lemma acts_quotient (A : {set aT}) (B : {set rT}) :
   A \subset 'N_qact_dom(B | to) -> [acts A, on B / H | quotient_action].
Proof.
move=> nBA; apply: subset_trans {A}nBA _; apply/subsetP=> a /setIP[dHa nBa].
rewrite inE dHa inE; apply/subsetP=> _ /morphimP[x nHx Bx ->].
rewrite inE /= qactE //.
by rewrite mem_morphim ?(acts_act acts_qact_dom) ?(astabs_act _ nBa).
Qed.

Lemma astabs_quotient (G : {group rT}) :
   H <| G -> 'N(G / H | quotient_action) = 'N_qact_dom(G | to).
Proof.
move=> nsHG; have [_ nHG] := andP nsHG.
apply/eqP; rewrite eqEsubset acts_quotient // andbT.
apply/subsetP=> a nGa; have dHa := astabs_dom nGa; have [Da _]:= setIdP dHa.
rewrite inE dHa 2!inE Da; apply/subsetP=> x Gx; have nHx := subsetP nHG x Gx.
rewrite -(quotientGK nsHG) 2!inE (acts_act acts_qact_dom) ?nHx //= inE.
by rewrite -qactE // (astabs_act _ nGa) mem_morphim.
Qed.

End QuotientAction.

Notation "to / H" := (quotient_action to H) : action_scope.

Section ModAction.

Variables (aT : finGroupType) (D : {group aT}) (rT : finType).
Variable to : action D rT.
Implicit Types (G : {group aT}) (S : {set rT}).

Section GenericMod.

Variable H : {group aT}.

Local Notation dom := 'N_D(H).
Local Notation range := 'Fix_to(D :&: H).
Let acts_dom : {acts dom, on range | to} := acts_act (acts_subnorm_fix to H).

Definition modact x (Ha : coset_of H) :=
  if x \in range then to x (repr (D :&: Ha)) else x.

Lemma modactEcond x a :
  a \in dom -> modact x (coset H a) = (if x \in range then to x a else x).
Proof.
case/setIP=> Da Na; case: ifP => Cx; rewrite /modact Cx //.
rewrite val_coset // -group_modr ?sub1set //.
case: (repr _) / (repr_rcosetP (D :&: H) a) => a' Ha'.
by rewrite actMin ?(afixP Cx _ Ha') //; case/setIP: Ha'.
Qed.

Lemma modactE x a :
  a \in D -> a \in 'N(H) -> x \in range ->  modact x (coset H a) = to x a.
Proof. by move=> Da Na Rx; rewrite modactEcond ?Rx // inE Da. Qed.

Lemma modact_is_action : is_action (D / H) modact.
Proof.
split=> [Ha x y | x Ha Hb]; last first.
  case/morphimP=> a Na Da ->{Ha}; case/morphimP=> b Nb Db ->{Hb}.
  rewrite -morphM //= !modactEcond // ?groupM ?(introT setIP _) //.
  by case: ifP => Cx; rewrite ?(acts_dom, Cx, actMin, introT setIP _).
case: (set_0Vmem (D :&: Ha)) => [Da0 | [a /setIP[Da NHa]]].
  by rewrite /modact Da0 repr_set0 !act1 !if_same.
have Na := subsetP (coset_norm _) _ NHa.
have NDa: a \in 'N_D(H) by rewrite inE Da.
rewrite -(coset_mem NHa) !modactEcond //.
do 2![case: ifP]=> Cy Cx // eqxy; first exact: act_inj eqxy.
  by rewrite -eqxy acts_dom ?Cx in Cy.
by rewrite eqxy acts_dom ?Cy in Cx.
Qed.

Canonical mod_action := Action modact_is_action.

Section Stabilizers.

Variable S : {set rT}.
Hypothesis cSH : H \subset 'C(S | to).

Let fixSH : S \subset 'Fix_to(D :&: H).
Proof. by rewrite -astabCin ?subsetIl // subIset ?cSH ?orbT. Qed.

Lemma astabs_mod : 'N(S | mod_action) = 'N(S | to) / H.
Proof.
apply/setP=> Ha; apply/idP/morphimP=> [nSa | [a nHa nSa ->]].
  case/morphimP: (astabs_dom nSa) => a nHa Da defHa.
  exists a => //; rewrite !inE Da; apply/subsetP=> x Sx; rewrite !inE.
  by have:= Sx; rewrite -(astabs_act x nSa) defHa /= modactE ?(subsetP fixSH).
have Da := astabs_dom nSa; rewrite !inE mem_quotient //; apply/subsetP=> x Sx.
by rewrite !inE /= modactE ?(astabs_act x nSa) ?(subsetP fixSH).
Qed.

Lemma astab_mod : 'C(S | mod_action) = 'C(S | to) / H.
Proof.
apply/setP=> Ha; apply/idP/morphimP=> [cSa | [a nHa cSa ->]].
  case/morphimP: (astab_dom cSa) => a nHa Da defHa.
  exists a => //; rewrite !inE Da; apply/subsetP=> x Sx; rewrite !inE.
  by rewrite -{2}[x](astab_act cSa) // defHa /= modactE ?(subsetP fixSH).
have Da := astab_dom cSa; rewrite !inE mem_quotient //; apply/subsetP=> x Sx.
by rewrite !inE /= modactE ?(astab_act cSa) ?(subsetP fixSH).
Qed.

End Stabilizers.

Lemma afix_mod G S :
    H \subset 'C(S | to) -> G \subset 'N_D(H) ->
  'Fix_(S | mod_action)(G / H) = 'Fix_(S | to)(G).
Proof.
move=> cSH /subsetIP[sGD nHG].
apply/eqP; rewrite eqEsubset !subsetI !subsetIl /= -!astabCin ?quotientS //.
have cfixH F: H \subset 'C(S :&: F | to).
  by rewrite (subset_trans cSH) // astabS ?subsetIl.
rewrite andbC astab_mod ?quotientS //=; last by rewrite astabCin ?subsetIr.
by rewrite -(quotientSGK nHG) //= -astab_mod // astabCin ?quotientS ?subsetIr.
Qed.

End GenericMod.

Lemma modact_faithful G S :
  [faithful G / 'C_G(S | to), on S | mod_action 'C_G(S | to)].
Proof.
rewrite /faithful astab_mod ?subsetIr //=.
by rewrite -quotientIG ?subsetIr ?trivg_quotient.
Qed.

End ModAction.

Notation "to %% H" := (mod_action to H) : action_scope.

Section ActPerm.
(* Morphism to permutations induced by an action. *)

Variables (aT : finGroupType) (D : {set aT}) (rT : finType).
Variable to : action D rT.

Definition actperm a := perm (act_inj to a).

Lemma actpermM : {in D &, {morph actperm : a b / a * b}}.
Proof. by move=> a b Da Db; apply/permP=> x; rewrite permM !permE actMin. Qed.

Canonical actperm_morphism := Morphism actpermM.

Lemma actpermE a x : actperm a x = to x a.
Proof. by rewrite permE. Qed.

Lemma actpermK x a : aperm x (actperm a) = to x a.
Proof. exact: actpermE. Qed.

Lemma ker_actperm : 'ker actperm = 'C(setT | to).
Proof.
congr (_ :&: _); apply/setP=> a; rewrite !inE /=.
apply/eqP/subsetP=> [a1 x _ | a1]; first by rewrite inE -actpermE a1 perm1.
by apply/permP=> x; apply/eqP; have:= a1 x; rewrite !inE actpermE perm1 => ->.
Qed.

End ActPerm.

Section RestrictActionTheory.

Variables (aT : finGroupType) (D : {set aT}) (rT : finType).
Variables (to : action D rT).

Lemma faithful_isom (A : {group aT}) S (nSA : actby_cond A S to) :
   [faithful A, on S | to] -> isom A (actperm <[nSA]> @* A) (actperm <[nSA]>).
Proof.
by move=> ffulAS; apply/isomP; rewrite ker_actperm astab_actby setIT.
Qed.

Variables (A : {set aT}) (sAD : A \subset D).

Lemma ractpermE : actperm (to \ sAD) =1 actperm to.
Proof. by move=> a; apply/permP=> x; rewrite !permE. Qed.

Lemma afix_ract B : 'Fix_(to \ sAD)(B) = 'Fix_to(B). Proof. by []. Qed.

Lemma astab_ract S : 'C(S | to \ sAD) = 'C_A(S | to).
Proof. by rewrite setIA (setIidPl sAD). Qed.

Lemma astabs_ract S : 'N(S | to \ sAD) = 'N_A(S | to).
Proof. by rewrite setIA (setIidPl sAD). Qed.

Lemma acts_ract (B : {set aT}) S :
  [acts B, on S | to \ sAD] = (B \subset A) && [acts B, on S | to].
Proof. by rewrite astabs_ract subsetI. Qed.

End RestrictActionTheory.

Section MorphAct.
(* Action induced by a morphism to permutations. *)

Variables (aT : finGroupType) (D : {group aT}) (rT : finType).
Variable phi : {morphism D >-> {perm rT}}.

Definition mact x a := phi a x.

Lemma mact_is_action : is_action D mact.
Proof.
split=> [a x y | x a b Da Db]; first exact: perm_inj.
by rewrite /mact morphM //= permM.
Qed.

Canonical morph_action := Action mact_is_action.

Lemma mactE x a : morph_action x a = phi a x. Proof. by []. Qed.

Lemma injm_faithful : 'injm phi -> [faithful D, on setT | morph_action].
Proof.
move/injmP=> phi_inj; apply/subsetP=> a /setIP[Da /astab_act a1].
apply/set1P/phi_inj => //; apply/permP=> x.
by rewrite morph1 perm1 -mactE a1 ?inE.
Qed.

Lemma perm_mact a : actperm morph_action a = phi a.
Proof. by apply/permP=> x; rewrite permE. Qed.

End MorphAct.

Notation "<< phi >>" := (morph_action phi) : action_scope.

Section CompAct.

Variables (gT aT : finGroupType) (rT : finType).
Variables (D : {set aT}) (to : action D rT).
Variables (B : {set gT}) (f : {morphism B >-> aT}).

Definition comp_act x e := to x (f e).
Lemma comp_is_action : is_action (f @*^-1 D) comp_act.
Proof.
split=> [e | x e1 e2]; first exact: act_inj.
case/morphpreP=> Be1 Dfe1; case/morphpreP=> Be2 Dfe2.
by rewrite /comp_act morphM ?actMin.
Qed.
Canonical comp_action := Action comp_is_action.

Lemma comp_actE x e : comp_action x e = to x (f e). Proof. by []. Qed.

Lemma afix_comp (A : {set gT}) :
  A \subset B -> 'Fix_comp_action(A) = 'Fix_to(f @* A).
Proof.
move=> sAB; apply/setP=> x; rewrite !inE /morphim (setIidPr sAB).
apply/subsetP/subsetP=> [cAx _ /imsetP[a Aa ->] | cfAx a Aa].
  by move/cAx: Aa; rewrite !inE.
by rewrite inE; move/(_ (f a)): cfAx; rewrite inE mem_imset // => ->.
Qed.

Lemma astab_comp S : 'C(S | comp_action) = f @*^-1 'C(S | to).
Proof. by apply/setP=> x; rewrite !inE -andbA. Qed.

Lemma astabs_comp S : 'N(S | comp_action) = f @*^-1 'N(S | to).
Proof. by apply/setP=> x; rewrite !inE -andbA. Qed.

End CompAct.

Notation "to \o f" := (comp_action to f) : action_scope.

Section PermAction.
(*  Natural action of permutation groups.                        *)

Variable rT : finType.
Local Notation gT := {perm rT}.
Implicit Types a b c : gT.

Lemma aperm_is_action : is_action setT (@aperm rT).
Proof.
by apply: is_total_action => [x|x a b]; rewrite apermE (perm1, permM).
Qed.

Canonical perm_action := Action aperm_is_action.

Lemma pcycleE a : pcycle a = orbit perm_action <[a]>%g.
Proof. by []. Qed.

Lemma perm_act1P a : reflect (forall x, aperm x a = x) (a == 1).
Proof.
apply: (iffP eqP) => [-> x | a1]; first exact: act1.
by apply/permP=> x; rewrite -apermE a1 perm1.
Qed.

Lemma perm_faithful A : [faithful A, on setT | perm_action].
Proof.
apply/subsetP=> a /setIP[Da crTa].
by apply/set1P; apply/permP=> x; rewrite -apermE perm1 (astabP crTa) ?inE.
Qed.

Lemma actperm_id p : actperm perm_action p = p.
Proof. by apply/permP=> x; rewrite permE. Qed.

End PermAction.

Arguments perm_act1P {rT a}.

Notation "'P" := (perm_action _) (at level 8) : action_scope.

Section ActpermOrbits.

Variables (aT : finGroupType) (D : {group aT}) (rT : finType).
Variable to : action D rT.

Lemma orbit_morphim_actperm (A : {set aT}) :
  A \subset D -> orbit 'P (actperm to @* A) =1 orbit to A.
Proof.
move=> sAD x; rewrite morphimEsub // /orbit -imset_comp.
by apply: eq_imset => a //=; rewrite actpermK.
Qed.

Lemma pcycle_actperm (a : aT) :
   a \in D -> pcycle (actperm to a) =1 orbit to <[a]>.
Proof.
move=> Da x.
by rewrite pcycleE -orbit_morphim_actperm ?cycle_subG ?morphim_cycle.
Qed.

End ActpermOrbits.

Section RestrictPerm.

Variables (T : finType) (S : {set T}).

Definition restr_perm := actperm (<[subxx 'N(S | 'P)]>).
Canonical restr_perm_morphism := [morphism of restr_perm].

Lemma restr_perm_on p : perm_on S (restr_perm p).
Proof.
apply/subsetP=> x; apply: contraR => notSx.
by rewrite permE /= /actby (negPf notSx).
Qed.

Lemma triv_restr_perm p : p \notin 'N(S | 'P) -> restr_perm p = 1.
Proof.
move=> not_nSp; apply/permP=> x.
by rewrite !permE /= /actby (negPf not_nSp) andbF.
Qed.

Lemma restr_permE : {in 'N(S | 'P) & S, forall p, restr_perm p =1 p}.
Proof. by move=> y x nSp Sx; rewrite /= actpermE actbyE. Qed.

Lemma ker_restr_perm : 'ker restr_perm = 'C(S | 'P).
Proof. by rewrite ker_actperm astab_actby setIT (setIidPr (astab_sub _ _)). Qed.

Lemma im_restr_perm p : restr_perm p @: S = S.
Proof. exact: im_perm_on (restr_perm_on p). Qed.

End RestrictPerm.

Section AutIn.

Variable gT : finGroupType.

Definition Aut_in A (B : {set gT}) := 'N_A(B | 'P) / 'C_A(B | 'P).

Variables G H : {group gT}.
Hypothesis sHG: H \subset G.

Lemma Aut_restr_perm a : a \in Aut G -> restr_perm H a \in Aut H.
Proof.
move=> AutGa.
case nHa: (a \in 'N(H | 'P)); last by rewrite triv_restr_perm ?nHa ?group1.
rewrite inE restr_perm_on; apply/morphicP=> x y Hx Hy /=.
by rewrite !restr_permE ?groupM // -(autmE AutGa) morphM ?(subsetP sHG).
Qed.

Lemma restr_perm_Aut : restr_perm H @* Aut G \subset Aut H.
Proof.
by apply/subsetP=> a'; case/morphimP=> a _ AutGa ->{a'}; apply: Aut_restr_perm.
Qed.

Lemma Aut_in_isog : Aut_in (Aut G) H \isog restr_perm H @* Aut G.
Proof.
rewrite /Aut_in -ker_restr_perm kerE -morphpreIdom -morphimIdom -kerE /=.
by rewrite setIA (setIC _ (Aut G)) first_isog_loc ?subsetIr.
Qed.

Lemma Aut_sub_fullP :
  reflect (forall h : {morphism H >-> gT}, 'injm h -> h @* H = H ->
             exists g : {morphism G >-> gT},
             [/\ 'injm g, g @* G = G & {in H, g =1 h}])
          (Aut_in (Aut G) H \isog Aut H).
Proof.
rewrite (isog_transl _ Aut_in_isog) /=; set rG := _ @* _.
apply: (iffP idP) => [iso_rG h injh hH| AutHinG].
  have: aut injh hH \in rG; last case/morphimP=> g nHg AutGg def_g.
    suffices ->: rG = Aut H by apply: Aut_aut.
    by apply/eqP; rewrite eqEcard restr_perm_Aut /= (card_isog iso_rG).
  exists (autm_morphism AutGg); rewrite injm_autm im_autm; split=> // x Hx.
  by rewrite -(autE injh hH Hx) def_g actpermE actbyE.
suffices ->: rG = Aut H by apply: isog_refl.
apply/eqP; rewrite eqEsubset restr_perm_Aut /=.
apply/subsetP=> h AutHh; have hH := im_autm AutHh.
have [g [injg gG eq_gh]] := AutHinG _ (injm_autm AutHh) hH.
have [Ng AutGg]: aut injg gG \in 'N(H | 'P) /\ aut injg gG \in Aut G.
  rewrite Aut_aut !inE; split=> //; apply/subsetP=> x Hx.
  by rewrite inE /= /aperm autE ?(subsetP sHG) // -hH eq_gh ?mem_morphim.
apply/morphimP; exists (aut injg gG) => //; apply: (eq_Aut AutHh) => [|x Hx].
  by rewrite (subsetP restr_perm_Aut) // mem_morphim.
by rewrite restr_permE //= /aperm autE ?eq_gh ?(subsetP sHG).
Qed.

End AutIn.

Arguments Aut_in {gT} A%g B%g.

Section InjmAutIn.

Variables (gT rT : finGroupType) (D G H : {group gT}) (f : {morphism D >-> rT}).
Hypotheses (injf : 'injm f) (sGD : G \subset D) (sHG : H \subset G).
Let sHD := subset_trans sHG sGD.
Local Notation fGisom := (Aut_isom injf sGD).
Local Notation fHisom := (Aut_isom injf sHD).
Local Notation inH := (restr_perm H).
Local Notation infH := (restr_perm (f @* H)).

Lemma astabs_Aut_isom a :
  a \in Aut G -> (fGisom a \in 'N(f @* H | 'P)) = (a \in 'N(H | 'P)).
Proof.
move=> AutGa; rewrite !inE sub_morphim_pre // subsetI sHD /= /aperm.
rewrite !(sameP setIidPl eqP) !eqEsubset !subsetIl; apply: eq_subset_r => x.
rewrite !inE; apply: andb_id2l => Hx; have Gx: x \in G := subsetP sHG x Hx.
have Dax: a x \in D by rewrite (subsetP sGD) // Aut_closed.
by rewrite Aut_isomE // -!sub1set -morphim_set1 // injmSK ?sub1set.
Qed.

Lemma isom_restr_perm a : a \in Aut G -> fHisom (inH a) = infH (fGisom a).
Proof.
move=> AutGa; case nHa: (a \in 'N(H | 'P)); last first.
  by rewrite !triv_restr_perm ?astabs_Aut_isom ?nHa ?morph1.
apply: (eq_Aut (Aut_Aut_isom injf sHD _)) => [|fx Hfx /=].
  by rewrite (Aut_restr_perm (morphimS f sHG)) ?Aut_Aut_isom.
have [x Dx Hx def_fx] := morphimP Hfx; have Gx := subsetP sHG x Hx.
rewrite {1}def_fx Aut_isomE ?(Aut_restr_perm sHG) //.
by rewrite !restr_permE ?astabs_Aut_isom // def_fx Aut_isomE.
Qed.

Lemma restr_perm_isom : isom (inH @* Aut G) (infH @* Aut (f @* G)) fHisom.
Proof.
apply: sub_isom; rewrite ?restr_perm_Aut ?injm_Aut_isom //=.
rewrite -(im_Aut_isom injf sGD) -!morphim_comp.
apply: eq_in_morphim; last exact: isom_restr_perm.
apply/setP=> a; rewrite 2!in_setI; apply: andb_id2r => AutGa.
rewrite /= inE andbC inE (Aut_restr_perm sHG) //=.
by symmetry; rewrite inE AutGa inE astabs_Aut_isom.
Qed.

Lemma injm_Aut_sub : Aut_in (Aut (f @* G)) (f @* H) \isog Aut_in (Aut G) H.
Proof.
do 2!rewrite isog_sym (isog_transl _ (Aut_in_isog _ _)).
by rewrite isog_sym (isom_isog _ _ restr_perm_isom) // restr_perm_Aut.
Qed.

Lemma injm_Aut_full :
  (Aut_in (Aut (f @* G)) (f @* H) \isog Aut (f @* H))
      = (Aut_in (Aut G) H \isog Aut H).
Proof.
by rewrite (isog_transl _ injm_Aut_sub) (isog_transr _ (injm_Aut injf sHD)).
Qed.

End InjmAutIn.

Section GroupAction.

Variables (aT rT : finGroupType) (D : {set aT}) (R : {set rT}).
Local Notation actT := (action D rT).

Definition is_groupAction (to : actT) :=
  {in D, forall a, actperm to a \in Aut R}.

Structure groupAction := GroupAction {gact :> actT; _ : is_groupAction gact}.

Definition clone_groupAction to :=
  let: GroupAction _ toA := to return {type of GroupAction for to} -> _ in
  fun k => k toA : groupAction.

End GroupAction.

Delimit Scope groupAction_scope with gact.
Bind Scope groupAction_scope with groupAction.

Arguments is_groupAction {aT rT D%g} R%g to%act.
Arguments groupAction {aT rT} D%g R%g.
Arguments gact {aT rT D%g R%g} to%gact : rename.

Notation "[ 'groupAction' 'of' to ]" :=
     (clone_groupAction (@GroupAction _ _ _ _ to))
  (at level 0, format "[ 'groupAction'  'of'  to ]") : form_scope.

Section GroupActionDefs.

Variables (aT rT : finGroupType) (D : {set aT}) (R : {set rT}).
Implicit Type A : {set aT}.
Implicit Type S : {set rT}.
Implicit Type to : groupAction D R.

Definition gact_range of groupAction D R := R.

Definition gacent to A := 'Fix_(R | to)(D :&: A).

Definition acts_on_group A S to := [acts A, on S | to] /\ S \subset R.

Coercion actby_cond_group A S to : acts_on_group A S to -> actby_cond A S to :=
  @proj1 _ _.

Definition acts_irreducibly A S to :=
  [min S of G | G :!=: 1 & [acts A, on G | to]].

End GroupActionDefs.

Arguments gacent {aT rT D%g R%g} to%gact A%g.
Arguments acts_on_group {aT rT D%g R%g} A%g S%g to%gact.
Arguments acts_irreducibly {aT rT D%g R%g} A%g S%g to%gact.

Notation "''C_' ( | to ) ( A )" := (gacent to A)
  (at level 8, format "''C_' ( | to ) ( A )") : group_scope.
Notation "''C_' ( G | to ) ( A )" := (G :&: 'C_(|to)(A))
  (at level 8, format "''C_' ( G  |  to ) ( A )") : group_scope.
Notation "''C_' ( | to ) [ a ]" := 'C_(|to)([set a])
  (at level 8, format "''C_' ( | to ) [ a ]") : group_scope.
Notation "''C_' ( G | to ) [ a ]" := 'C_(G | to)([set a])
  (at level 8, format "''C_' ( G  |  to ) [ a ]") : group_scope.

Notation "{ 'acts' A , 'on' 'group' G | to }" := (acts_on_group A G to)
  (at level 0, format "{ 'acts'  A ,  'on'  'group'  G  |  to }") : form_scope.

Section RawGroupAction.

Variables (aT rT : finGroupType) (D : {set aT}) (R : {set rT}).
Variable to : groupAction D R.

Lemma actperm_Aut : is_groupAction R to. Proof. by case: to. Qed.

Lemma im_actperm_Aut : actperm to @* D \subset Aut R.
Proof. by apply/subsetP=> _ /morphimP[a _ Da ->]; apply: actperm_Aut. Qed.

Lemma gact_out x a : a \in D -> x \notin R -> to x a = x.
Proof. by move=> Da Rx; rewrite -actpermE (out_Aut _ Rx) ?actperm_Aut. Qed.

Lemma gactM : {in D, forall a, {in R &, {morph to^~ a : x y / x * y}}}.
Proof.
move=> a Da /= x y; rewrite -!(actpermE to); apply: morphicP x y.
by rewrite Aut_morphic ?actperm_Aut.
Qed.

Lemma actmM a : {in R &, {morph actm to a : x y / x * y}}.
Proof. by rewrite /actm; case: ifP => //; apply: gactM. Qed.

Canonical act_morphism a := Morphism (actmM a).

Lemma morphim_actm :
  {in D, forall a (S : {set rT}), S \subset R -> actm to a @* S = to^* S a}.
Proof. by move=> a Da /= S sSR; rewrite /morphim /= actmEfun ?(setIidPr _). Qed.

Variables (a : aT) (A B : {set aT}) (S : {set rT}).

Lemma gacentIdom : 'C_(|to)(D :&: A) = 'C_(|to)(A).
Proof. by rewrite /gacent setIA setIid. Qed.

Lemma gacentIim : 'C_(R | to)(A) = 'C_(|to)(A).
Proof. by rewrite setIA setIid. Qed.

Lemma gacentS : A \subset B -> 'C_(|to)(B) \subset 'C_(|to)(A).
Proof. by move=> sAB; rewrite !(setIS, afixS). Qed.

Lemma gacentU : 'C_(|to)(A :|: B) = 'C_(|to)(A) :&: 'C_(|to)(B).
Proof. by rewrite -setIIr -afixU -setIUr. Qed.

Hypotheses (Da : a \in D) (sAD : A \subset D) (sSR : S \subset R).

Lemma gacentE : 'C_(|to)(A) = 'Fix_(R | to)(A).
Proof. by rewrite -{2}(setIidPr sAD). Qed.

Lemma gacent1E : 'C_(|to)[a] = 'Fix_(R | to)[a].
Proof. by rewrite /gacent [D :&: _](setIidPr _) ?sub1set. Qed.

Lemma subgacentE : 'C_(S | to)(A) = 'Fix_(S | to)(A).
Proof. by rewrite gacentE setIA (setIidPl sSR). Qed.

Lemma subgacent1E : 'C_(S | to)[a] = 'Fix_(S | to)[a].
Proof. by rewrite gacent1E setIA (setIidPl sSR). Qed.

End RawGroupAction.

Section GroupActionTheory.

Variables aT rT : finGroupType.
Variables (D : {group aT}) (R : {group rT}) (to : groupAction D R).
Implicit Type A B : {set aT}.
Implicit Types G H : {group aT}.
Implicit Type S : {set rT}.
Implicit Types M N : {group rT}.

Lemma gact1 : {in D, forall a, to 1 a = 1}.
Proof. by move=> a Da; rewrite /= -actmE ?morph1. Qed.

Lemma gactV : {in D, forall a, {in R, {morph to^~ a : x / x^-1}}}.
Proof. by move=> a Da /= x Rx; move; rewrite -!actmE ?morphV. Qed.

Lemma gactX : {in D, forall a n, {in R, {morph to^~ a : x / x ^+ n}}}.
Proof. by move=> a Da /= n x Rx; rewrite -!actmE // morphX. Qed.

Lemma gactJ : {in D, forall a, {in R &, {morph to^~ a : x y / x ^ y}}}.
Proof. by move=> a Da /= x Rx y Ry; rewrite -!actmE // morphJ. Qed.

Lemma gactR : {in D, forall a, {in R &, {morph to^~ a : x y / [~ x, y]}}}.
Proof. by move=> a Da /= x Rx y Ry; rewrite -!actmE // morphR. Qed.

Lemma gact_stable : {acts D, on R | to}.
Proof.
apply: acts_act; apply/subsetP=> a Da; rewrite !inE Da.
apply/subsetP=> x; rewrite inE; apply: contraLR => R'xa.
by rewrite -(actKin to Da x) gact_out ?groupV.
Qed.

Lemma group_set_gacent A : group_set 'C_(|to)(A).
Proof.
apply/group_setP; split=> [|x y].
  by rewrite !inE group1; apply/subsetP=> a /setIP[Da _]; rewrite inE gact1.
case/setIP=> Rx /afixP cAx /setIP[Ry /afixP cAy].
rewrite inE groupM //; apply/afixP=> a Aa.
by rewrite gactM ?cAx ?cAy //; case/setIP: Aa.
Qed.

Canonical gacent_group A := Group (group_set_gacent A).

Lemma gacent1 : 'C_(|to)(1) = R.
Proof. by rewrite /gacent (setIidPr (sub1G _)) afix1 setIT. Qed.

Lemma gacent_gen A : A \subset D -> 'C_(|to)(<<A>>) = 'C_(|to)(A).
Proof.
by move=> sAD; rewrite /gacent ![D :&: _](setIidPr _) ?gen_subG ?afix_gen_in.
Qed.

Lemma gacentD1 A : 'C_(|to)(A^#) = 'C_(|to)(A).
Proof.
rewrite -gacentIdom -gacent_gen ?subsetIl // setIDA genD1 ?group1 //.
by rewrite gacent_gen ?subsetIl // gacentIdom.
Qed.

Lemma gacent_cycle a : a \in D -> 'C_(|to)(<[a]>) = 'C_(|to)[a].
Proof. by move=> Da; rewrite gacent_gen ?sub1set. Qed.

Lemma gacentY A B :
  A \subset D -> B \subset D -> 'C_(|to)(A <*> B) = 'C_(|to)(A) :&: 'C_(|to)(B).
Proof. by move=> sAD sBD; rewrite gacent_gen ?gacentU // subUset sAD. Qed.

Lemma gacentM G H :
  G \subset D -> H \subset D -> 'C_(|to)(G * H) = 'C_(|to)(G) :&: 'C_(|to)(H).
Proof.
by move=> sGD sHB; rewrite -gacent_gen ?mul_subG // genM_join gacentY.
Qed.

Lemma astab1 : 'C(1 | to) = D.
Proof.
by apply/setP=> x; rewrite ?(inE, sub1set) andb_idr //; move/gact1=> ->.
Qed.

Lemma astab_range : 'C(R | to) = 'C(setT | to).
Proof.
apply/eqP; rewrite eqEsubset andbC astabS ?subsetT //=.
apply/subsetP=> a cRa; have Da := astab_dom cRa; rewrite !inE Da.
apply/subsetP=> x; rewrite -(setUCr R) !inE.
by case/orP=> ?; [rewrite (astab_act cRa) | rewrite gact_out].
Qed.

Lemma gacentC A S :
    A \subset D -> S \subset R ->
  (S \subset 'C_(|to)(A)) = (A \subset 'C(S | to)).
Proof. by move=> sAD sSR; rewrite subsetI sSR astabCin // (setIidPr sAD). Qed.

Lemma astab_gen S : S \subset R -> 'C(<<S>> | to) = 'C(S | to).
Proof.
move=> sSR; apply/setP=> a; case Da: (a \in D); last by rewrite !inE Da.
by rewrite -!sub1set -!gacentC ?sub1set ?gen_subG.
Qed.

Lemma astabM M N :
  M \subset R -> N \subset R -> 'C(M * N | to) = 'C(M | to) :&: 'C(N | to).
Proof.
move=> sMR sNR; rewrite -astabU -astab_gen ?mul_subG // genM_join.
by rewrite astab_gen // subUset sMR.
Qed.

Lemma astabs1 : 'N(1 | to) = D.
Proof. by rewrite astabs_set1 astab1. Qed.

Lemma astabs_range : 'N(R | to) = D.
Proof.
apply/setIidPl; apply/subsetP=> a Da; rewrite inE.
by apply/subsetP=> x Rx; rewrite inE gact_stable.
Qed.

Lemma astabsD1 S : 'N(S^# | to) = 'N(S | to).
Proof.
case S1: (1 \in S); last first.
  by rewrite (setDidPl _) // disjoint_sym disjoints_subset sub1set inE S1.
apply/eqP; rewrite eqEsubset andbC -{1}astabsIdom -{1}astabs1 setIC astabsD /=.
by rewrite -{2}(setD1K S1) -astabsIdom -{1}astabs1 astabsU.
Qed.

Lemma gacts_range A : A \subset D -> {acts A, on group R | to}.
Proof. by move=> sAD; split; rewrite ?astabs_range. Qed.

Lemma acts_subnorm_gacent A : A \subset D ->
  [acts 'N_D(A), on 'C_(| to)(A) | to].
Proof.
move=> sAD; rewrite gacentE // actsI ?astabs_range ?subsetIl //.
by rewrite -{2}(setIidPr sAD) acts_subnorm_fix.
Qed.

Lemma acts_subnorm_subgacent A B S :
  A \subset D -> [acts B, on S | to] -> [acts 'N_B(A), on 'C_(S | to)(A) | to].
Proof.
move=> sAD actsB; rewrite actsI //; first by rewrite subIset ?actsB.
by rewrite (subset_trans _ (acts_subnorm_gacent sAD)) ?setSI ?(acts_dom actsB).
Qed.

Lemma acts_gen A S :
  S \subset R -> [acts A, on S | to] -> [acts A, on <<S>> | to].
Proof.
move=> sSR actsA; apply: {A}subset_trans actsA _.
apply/subsetP=> a nSa; have Da := astabs_dom nSa; rewrite !inE Da.
apply: subset_trans (_ : <<S>> \subset actm to a @*^-1 <<S>>) _.
  rewrite gen_subG subsetI sSR; apply/subsetP=> x Sx.
  by rewrite inE /= actmE ?mem_gen // astabs_act.
by apply/subsetP=> x; rewrite !inE; case/andP=> Rx; rewrite /= actmE.
Qed.

Lemma acts_joing A M N :
    M \subset R -> N \subset R -> [acts A, on M | to] -> [acts A, on N | to] ->
  [acts A, on M <*> N | to].
Proof. by move=> sMR sNR nMA nNA; rewrite acts_gen ?actsU // subUset sMR. Qed.

Lemma injm_actm a : 'injm (actm to a).
Proof.
apply/injmP=> x y Rx Ry; rewrite /= /actm; case: ifP => Da //.
exact: act_inj.
Qed.

Lemma im_actm a : actm to a @* R = R.
Proof.
apply/eqP; rewrite eqEcard (card_injm (injm_actm a)) // leqnn andbT.
apply/subsetP=> _ /morphimP[x Rx _ ->] /=.
by rewrite /actm; case: ifP => // Da; rewrite gact_stable.
Qed.

Lemma acts_char G M : G \subset D -> M \char R -> [acts G, on M | to].
Proof.
move=> sGD /charP[sMR charM].
apply/subsetP=> a Ga; have Da := subsetP sGD a Ga; rewrite !inE Da.
apply/subsetP=> x Mx; have Rx := subsetP sMR x Mx.
by rewrite inE -(charM _ (injm_actm a) (im_actm a)) -actmE // mem_morphim.
Qed.

Lemma gacts_char G M :
  G \subset D -> M \char R -> {acts G, on group M | to}.
Proof. by move=> sGD charM; split; rewrite (acts_char, char_sub). Qed.

Section Restrict.

Variables (A : {group aT}) (sAD : A \subset D).

Lemma ract_is_groupAction : is_groupAction R (to \ sAD).
Proof. by move=> a Aa /=; rewrite ractpermE actperm_Aut ?(subsetP sAD). Qed.

Canonical ract_groupAction := GroupAction ract_is_groupAction.

Lemma gacent_ract B : 'C_(|ract_groupAction)(B) = 'C_(|to)(A :&: B).
Proof. by rewrite /gacent afix_ract setIA (setIidPr sAD). Qed.

End Restrict.

Section ActBy.

Variables (A : {group aT}) (G : {group rT}) (nGAg : {acts A, on group G | to}).

Lemma actby_is_groupAction : is_groupAction G <[nGAg]>.
Proof.
move=> a Aa; rewrite /= inE; apply/andP; split.
  apply/subsetP=> x; apply: contraR => Gx.
  by rewrite actpermE /= /actby (negbTE Gx).
apply/morphicP=> x y Gx Gy; rewrite !actpermE /= /actby Aa groupM ?Gx ?Gy //=.
by case nGAg; move/acts_dom; do 2!move/subsetP=> ?; rewrite gactM; auto.
Qed.

Canonical actby_groupAction := GroupAction actby_is_groupAction.

Lemma gacent_actby B :
  'C_(|actby_groupAction)(B) = 'C_(G | to)(A :&: B).
Proof.
rewrite /gacent afix_actby !setIA setIid setIUr setICr set0U.
by have [nAG sGR] := nGAg; rewrite (setIidPr (acts_dom nAG)) (setIidPl sGR).
Qed.

End ActBy.

Section Quotient.

Variable H : {group rT}.

Lemma acts_qact_dom_norm : {acts qact_dom to H, on 'N(H) | to}.
Proof.
move=> a HDa /= x; rewrite {2}(('N(H) =P to^~ a @^-1: 'N(H)) _) ?inE {x}//.
rewrite eqEcard (card_preimset _ (act_inj _ _)) leqnn andbT.
apply/subsetP=> x Nx; rewrite inE; move/(astabs_act (H :* x)): HDa.
rewrite mem_rcosets mulSGid ?normG // Nx => /rcosetsP[y Ny defHy].
suffices: to x a \in H :* y by apply: subsetP; rewrite mul_subG ?sub1set ?normG.
by rewrite -defHy; apply: mem_imset; apply: rcoset_refl.
Qed.

Lemma qact_is_groupAction : is_groupAction (R / H) (to / H).
Proof.
move=> a HDa /=; have Da := astabs_dom HDa.
rewrite inE; apply/andP; split.
  apply/subsetP=> Hx /=; case: (cosetP Hx) => x Nx ->{Hx}.
  apply: contraR => R'Hx; rewrite actpermE qactE // gact_out //.
  by apply: contra R'Hx; apply: mem_morphim.
apply/morphicP=> Hx Hy; rewrite !actpermE.
case/morphimP=> x Nx Gx ->{Hx}; case/morphimP=> y Ny Gy ->{Hy}.
by rewrite -morphM ?qactE ?groupM ?gactM // morphM ?acts_qact_dom_norm.
Qed.

Canonical quotient_groupAction := GroupAction qact_is_groupAction.

Lemma qact_domE : H \subset R -> qact_dom to H = 'N(H | to).
Proof.
move=> sHR; apply/setP=> a; apply/idP/idP=> nHa; have Da := astabs_dom nHa.
  rewrite !inE Da; apply/subsetP=> x Hx; rewrite inE -(rcoset1 H).
  have /rcosetsP[y Ny defHy]: to^~ a @: H \in rcosets H 'N(H).
    by rewrite (astabs_act _ nHa); apply/rcosetsP; exists 1; rewrite ?mulg1.
  by rewrite (rcoset_eqP (_ : 1 \in H :* y)) -defHy -1?(gact1 Da) mem_setact.
rewrite !inE Da; apply/subsetP=> Hx; rewrite inE => /rcosetsP[x Nx ->{Hx}].
apply/imsetP; exists (to x a).
  case Rx: (x \in R); last by rewrite gact_out ?Rx.
  rewrite inE; apply/subsetP=> _ /imsetP[y Hy ->].
  rewrite -(actKVin to Da y) -gactJ // ?(subsetP sHR, astabs_act, groupV) //.
  by rewrite memJ_norm // astabs_act ?groupV.
apply/eqP; rewrite rcosetE eqEcard.
rewrite (card_imset _ (act_inj _ _)) !card_rcoset leqnn andbT.
apply/subsetP=> _ /imsetP[y Hxy ->]; rewrite !mem_rcoset in Hxy *.
have Rxy := subsetP sHR _ Hxy; rewrite -(mulgKV x y).
case Rx: (x \in R); last by rewrite !gact_out ?mulgK // 1?groupMl ?Rx.
by rewrite -gactV // -gactM 1?groupMr ?groupV // mulgK astabs_act.
Qed.

End Quotient.

Section Mod.

Variable H : {group aT}.

Lemma modact_is_groupAction : is_groupAction 'C_(|to)(H) (to %% H).
Proof.
move=> Ha /morphimP[a Na Da ->]; have NDa: a \in 'N_D(H) by apply/setIP.
rewrite inE; apply/andP; split.
  apply/subsetP=> x; rewrite 2!inE andbC actpermE /= modactEcond //.
  by apply: contraR; case: ifP => // E Rx; rewrite gact_out.
apply/morphicP=> x y /setIP[Rx cHx] /setIP[Ry cHy].
rewrite /= !actpermE /= !modactE ?gactM //.
suffices: x * y \in 'C_(|to)(H) by case/setIP.
by rewrite groupM //; apply/setIP.
Qed.

Canonical mod_groupAction := GroupAction modact_is_groupAction.

Lemma modgactE x a :
  H \subset 'C(R | to) -> a \in 'N_D(H) -> (to %% H)%act x (coset H a) = to x a.
Proof.
move=> cRH NDa /=; have [Da Na] := setIP NDa.
have [Rx | notRx] := boolP (x \in R).
  by rewrite modactE //; apply/afixP=> b /setIP[_ /(subsetP cRH)/astab_act->].
rewrite gact_out //= /modact; case: ifP => // _; rewrite gact_out //.
suffices: a \in D :&: coset H a by case/mem_repr/setIP.
by rewrite inE Da val_coset // rcoset_refl.
Qed.

Lemma gacent_mod G M :
    H \subset 'C(M | to) -> G \subset 'N(H) ->
 'C_(M | mod_groupAction)(G / H) = 'C_(M | to)(G).
Proof.
move=> cMH nHG; rewrite -gacentIdom gacentE ?subsetIl // setICA.
have sHD: H \subset D by rewrite (subset_trans cMH) ?subsetIl.
rewrite -quotientGI // afix_mod ?setIS // setICA -gacentIim (setIC R) -setIA.
rewrite -gacentE ?subsetIl // gacentIdom setICA (setIidPr _) //.
by rewrite gacentC // ?(subset_trans cMH) ?astabS ?subsetIl // setICA subsetIl.
Qed.

Lemma acts_irr_mod G M :
    H \subset 'C(M | to) -> G \subset 'N(H) -> acts_irreducibly G M to ->
  acts_irreducibly (G / H) M mod_groupAction.
Proof.
move=> cMH nHG /mingroupP[/andP[ntM nMG] minM].
apply/mingroupP; rewrite ntM astabs_mod ?quotientS //; split=> // L modL ntL.
have cLH: H \subset 'C(L | to) by rewrite (subset_trans cMH) ?astabS //.
apply: minM => //; case/andP: modL => ->; rewrite astabs_mod ?quotientSGK //.
by rewrite (subset_trans cLH) ?astab_sub.
Qed.
  
End Mod.

Lemma modact_coset_astab x a :
  a \in D -> (to %% 'C(R | to))%act x (coset _ a) = to x a.
Proof.
move=> Da; apply: modgactE => {x}//.
rewrite !inE Da; apply/subsetP=> _ /imsetP[c Cc ->].
have Dc := astab_dom Cc; rewrite !inE groupJ //.
apply/subsetP=> x Rx; rewrite inE conjgE !actMin ?groupM ?groupV //.
by rewrite (astab_act Cc) ?actKVin // gact_stable ?groupV.
Qed.

Lemma acts_irr_mod_astab G M :
    acts_irreducibly G M to ->
  acts_irreducibly (G / 'C_G(M | to)) M (mod_groupAction _).
Proof.
move=> irrG; have /andP[_ nMG] := mingroupp irrG.
apply: acts_irr_mod irrG; first exact: subsetIr.
by rewrite normsI ?normG // (subset_trans nMG) // astab_norm.
Qed.
  
Section CompAct.

Variables (gT : finGroupType) (G : {group gT}) (f : {morphism G >-> aT}).

Lemma comp_is_groupAction : is_groupAction R (comp_action to f).
Proof.
move=> a /morphpreP[Ba Dfa]; apply: etrans (actperm_Aut to Dfa).
by congr (_ \in Aut R); apply/permP=> x; rewrite !actpermE.
Qed.
Canonical comp_groupAction := GroupAction comp_is_groupAction.

Lemma gacent_comp U : 'C_(|comp_groupAction)(U) = 'C_(|to)(f @* U).
Proof.
rewrite /gacent afix_comp ?subIset ?subxx //.
by rewrite -(setIC U) (setIC D) morphim_setIpre.
Qed.

End CompAct.

End GroupActionTheory.

Notation "''C_' ( | to ) ( A )" := (gacent_group to A) : Group_scope.
Notation "''C_' ( G | to ) ( A )" :=
  (setI_group G 'C_(|to)(A)) : Group_scope.
Notation "''C_' ( | to ) [ a ]" := (gacent_group to [set a%g]) : Group_scope.
Notation "''C_' ( G | to ) [ a ]" :=
  (setI_group G 'C_(|to)[a]) : Group_scope.

Notation "to \ sAD" := (ract_groupAction to sAD) : groupAction_scope.
Notation "<[ nGA ] >" := (actby_groupAction nGA) : groupAction_scope.
Notation "to / H" := (quotient_groupAction to H) : groupAction_scope.
Notation "to %% H" := (mod_groupAction to H) : groupAction_scope.
Notation "to \o f" := (comp_groupAction to f) : groupAction_scope.

(* Operator group isomorphism. *)
Section MorphAction.

Variables (aT1 aT2 : finGroupType) (rT1 rT2 : finType).
Variables (D1 : {group aT1}) (D2 : {group aT2}).
Variables (to1 : action D1 rT1) (to2 : action D2 rT2).
Variables (A : {set aT1}) (R S : {set rT1}).
Variables (h : rT1 -> rT2) (f : {morphism D1 >-> aT2}).
Hypotheses (actsDR : {acts D1, on R | to1}) (injh : {in R &, injective h}).
Hypothesis defD2 : f @* D1 = D2.
Hypotheses (sSR : S \subset R) (sAD1 : A \subset D1).
Hypothesis hfJ : {in S & D1, morph_act to1 to2 h f}.

Lemma morph_astabs : f @* 'N(S | to1) = 'N(h @: S | to2).
Proof.
apply/setP=> fx; apply/morphimP/idP=> [[x D1x nSx ->] | nSx].
  rewrite 2!inE -{1}defD2 mem_morphim //=; apply/subsetP=> _ /imsetP[u Su ->].
  by rewrite inE -hfJ ?mem_imset // (astabs_act _ nSx).
have [|x D1x _ def_fx] := morphimP (_ : fx \in f @* D1).
  by rewrite defD2 (astabs_dom nSx).
exists x => //; rewrite !inE D1x; apply/subsetP=> u Su.
have /imsetP[u' Su' /injh def_u']: h (to1 u x) \in h @: S.
  by rewrite hfJ // -def_fx (astabs_act _ nSx) mem_imset.
by rewrite inE def_u' ?actsDR ?(subsetP sSR).
Qed.

Lemma morph_astab : f @* 'C(S | to1) = 'C(h @: S | to2).
Proof.
apply/setP=> fx; apply/morphimP/idP=> [[x D1x cSx ->] | cSx].
  rewrite 2!inE -{1}defD2 mem_morphim //=; apply/subsetP=> _ /imsetP[u Su ->].
  by rewrite inE -hfJ // (astab_act cSx).
have [|x D1x _ def_fx] := morphimP (_ : fx \in f @* D1).
  by rewrite defD2 (astab_dom cSx).
exists x => //; rewrite !inE D1x; apply/subsetP=> u Su.
rewrite inE -(inj_in_eq injh) ?actsDR ?(subsetP sSR) ?hfJ //.
by rewrite -def_fx (astab_act cSx) ?mem_imset.
Qed.

Lemma morph_afix : h @: 'Fix_(S | to1)(A) = 'Fix_(h @: S | to2)(f @* A).
Proof.
apply/setP=> hu; apply/imsetP/setIP=> [[u /setIP[Su cAu] ->]|].
  split; first by rewrite mem_imset.
  by apply/afixP=> _ /morphimP[x D1x Ax ->]; rewrite -hfJ ?(afixP cAu).
case=> /imsetP[u Su ->] /afixP c_hu_fA; exists u; rewrite // inE Su.
apply/afixP=> x Ax; have Dx := subsetP sAD1 x Ax.
by apply: injh; rewrite ?actsDR ?(subsetP sSR) ?hfJ // c_hu_fA ?mem_morphim.
Qed.

End MorphAction.

Section MorphGroupAction.

Variables (aT1 aT2 rT1 rT2 : finGroupType).
Variables (D1 : {group aT1}) (D2 : {group aT2}).
Variables (R1 : {group rT1}) (R2 : {group rT2}).
Variables (to1 : groupAction D1 R1) (to2 : groupAction D2 R2).
Variables (h : {morphism R1 >-> rT2}) (f : {morphism D1 >-> aT2}).
Hypotheses (iso_h : isom R1 R2 h) (iso_f : isom D1 D2 f).
Hypothesis hfJ : {in R1 & D1, morph_act to1 to2 h f}.
Implicit Types (A : {set aT1}) (S : {set rT1}) (M : {group rT1}).

Lemma morph_gastabs S : S \subset R1 -> f @* 'N(S | to1) = 'N(h @* S | to2).
Proof.
have [[_ defD2] [injh _]] := (isomP iso_f, isomP iso_h).
move=> sSR1; rewrite (morphimEsub _ sSR1).
apply: (morph_astabs (gact_stable to1) (injmP injh)) => // u x.
by move/(subsetP sSR1); apply: hfJ.
Qed.

Lemma morph_gastab S : S \subset R1 -> f @* 'C(S | to1) = 'C(h @* S | to2).
Proof.
have [[_ defD2] [injh _]] := (isomP iso_f, isomP iso_h).
move=> sSR1; rewrite (morphimEsub _ sSR1).
apply: (morph_astab (gact_stable to1) (injmP injh)) => // u x.
by move/(subsetP sSR1); apply: hfJ.
Qed.

Lemma morph_gacent A : A \subset D1 -> h @* 'C_(|to1)(A) = 'C_(|to2)(f @* A).
Proof.
have [[_ defD2] [injh defR2]] := (isomP iso_f, isomP iso_h).
move=> sAD1; rewrite !gacentE //; last by rewrite -defD2 morphimS.
rewrite morphimEsub ?subsetIl // -{1}defR2 morphimEdom.
exact: (morph_afix (gact_stable to1) (injmP injh)).
Qed.

Lemma morph_gact_irr A M :
    A \subset D1 -> M \subset R1 -> 
  acts_irreducibly (f @* A) (h @* M) to2 = acts_irreducibly A M to1.
Proof.
move=> sAD1 sMR1.
have [[injf defD2] [injh defR2]] := (isomP iso_f, isomP iso_h).
have h_eq1 := morphim_injm_eq1 injh.
apply/mingroupP/mingroupP=> [] [/andP[ntM actAM] minM].
  split=> [|U]; first by rewrite -h_eq1 // ntM -(injmSK injf) ?morph_gastabs.
  case/andP=> ntU acts_fAU sUM; have sUR1 := subset_trans sUM sMR1.
  apply: (injm_morphim_inj injh) => //; apply: minM; last exact: morphimS.
  by rewrite h_eq1 // ntU -morph_gastabs ?morphimS.
split=> [|U]; first by rewrite h_eq1 // ntM -morph_gastabs ?morphimS.
case/andP=> ntU acts_fAU sUhM.
have sUhR1 := subset_trans sUhM (morphimS h sMR1).
have sU'M: h @*^-1 U \subset M by rewrite sub_morphpre_injm.
rewrite /= -(minM _ _ sU'M) ?morphpreK // -h_eq1 ?subsetIl // -(injmSK injf) //.
by rewrite morph_gastabs ?(subset_trans sU'M) // morphpreK ?ntU.
Qed.

End MorphGroupAction.

(* Conjugation and right translation actions. *)
Section InternalActionDefs.

Variable gT : finGroupType.
Implicit Type A : {set gT}.
Implicit Type G : {group gT}.

(* This is not a Canonical action because it is seldom used, and it would     *)
(* cause too many spurious matches (any group product would be viewed as an   *)
(* action!).                                                                  *)
Definition mulgr_action := TotalAction (@mulg1 gT) (@mulgA gT).

Canonical conjg_action := TotalAction (@conjg1 gT) (@conjgM gT).

Lemma conjg_is_groupAction : is_groupAction setT conjg_action.
Proof.
move=> a _; rewrite /= inE; apply/andP; split.
  by apply/subsetP=> x _; rewrite inE.
by apply/morphicP=> x y _ _; rewrite !actpermE /= conjMg.
Qed.

Canonical conjg_groupAction := GroupAction conjg_is_groupAction.

Lemma rcoset_is_action : is_action setT (@rcoset gT).
Proof.
by apply: is_total_action => [A|A x y]; rewrite !rcosetE (mulg1, rcosetM).
Qed.

Canonical rcoset_action := Action rcoset_is_action.

Canonical conjsg_action := TotalAction (@conjsg1 gT) (@conjsgM gT).

Lemma conjG_is_action : is_action setT (@conjG_group gT).
Proof.
apply: is_total_action => [G | G x y]; apply: val_inj; rewrite /= ?act1 //.
exact: actM.
Qed.

Definition conjG_action := Action conjG_is_action.

End InternalActionDefs.

Notation "'R" := (@mulgr_action _) (at level 8) : action_scope.
Notation "'Rs" := (@rcoset_action _) (at level 8) : action_scope.
Notation "'J" := (@conjg_action _) (at level 8) : action_scope.
Notation "'J" := (@conjg_groupAction _) (at level 8) : groupAction_scope.
Notation "'Js" := (@conjsg_action _) (at level 8) : action_scope.
Notation "'JG" := (@conjG_action _) (at level 8) : action_scope.
Notation "'Q" := ('J / _)%act (at level 8) : action_scope.
Notation "'Q" := ('J / _)%gact (at level 8) : groupAction_scope.

Section InternalGroupAction.

Variable gT : finGroupType.
Implicit Types A B : {set gT}.
Implicit Types G H : {group gT}.
Implicit Type x : gT.

(*  Various identities for actions on groups. *)

Lemma orbitR G x : orbit 'R G x = x *: G.
Proof. by rewrite -lcosetE. Qed.

Lemma astab1R x : 'C[x | 'R] = 1.
Proof.
apply/trivgP/subsetP=> y cxy.
by rewrite -(mulKg x y) [x * y](astab1P cxy) mulVg set11.
Qed.

Lemma astabR G : 'C(G | 'R) = 1.
Proof.
apply/trivgP/subsetP=> x cGx.
by rewrite -(mul1g x) [1 * x](astabP cGx) group1.
Qed.

Lemma astabsR G : 'N(G | 'R) = G.
Proof.
apply/setP=> x; rewrite !inE -setactVin ?inE //=.
by rewrite -groupV -{1 3}(mulg1 G) rcoset_sym -sub1set -mulGS -!rcosetE.
Qed.

Lemma atransR G : [transitive G, on G | 'R].
Proof. by rewrite /atrans -{1}(mul1g G) -orbitR mem_imset. Qed.

Lemma faithfulR G : [faithful G, on G | 'R].
Proof. by rewrite /faithful astabR subsetIr. Qed.

Definition Cayley_repr G := actperm <[atrans_acts (atransR G)]>.

Theorem Cayley_isom G : isom G (Cayley_repr G @* G) (Cayley_repr G).
Proof. exact: faithful_isom (faithfulR G). Qed.

Theorem Cayley_isog G : G \isog Cayley_repr G @* G.
Proof. exact: isom_isog (Cayley_isom G). Qed.

Lemma orbitJ G x : orbit 'J G x = x ^: G. Proof. by []. Qed.

Lemma afixJ A : 'Fix_('J)(A) = 'C(A).
Proof.
apply/setP=> x; apply/afixP/centP=> cAx y Ay /=.
  by rewrite /commute conjgC cAx.
by rewrite conjgE cAx ?mulKg.
Qed.

Lemma astabJ A : 'C(A |'J) = 'C(A).
Proof.
apply/setP=> x; apply/astabP/centP=> cAx y Ay /=.
  by apply: esym; rewrite conjgC cAx.
by rewrite conjgE -cAx ?mulKg.
Qed.

Lemma astab1J x : 'C[x |'J] = 'C[x].
Proof. by rewrite astabJ cent_set1. Qed.

Lemma astabsJ A : 'N(A | 'J) = 'N(A).
Proof. by apply/setP=> x; rewrite -2!groupV !inE -conjg_preim -sub_conjg. Qed.

Lemma setactJ A x : 'J^*%act A x = A :^ x. Proof. by []. Qed.

Lemma gacentJ A : 'C_(|'J)(A) = 'C(A).
Proof. by rewrite gacentE ?setTI ?subsetT ?afixJ. Qed.

Lemma orbitRs G A : orbit 'Rs G A = rcosets A G. Proof. by []. Qed.

Lemma sub_afixRs_norms G x A : (G :* x \in 'Fix_('Rs)(A)) = (A \subset G :^ x).
Proof.
rewrite inE /=; apply: eq_subset_r => a.
rewrite inE rcosetE -(can2_eq (rcosetKV x) (rcosetK x)) -!rcosetM.
rewrite eqEcard card_rcoset leqnn andbT mulgA (conjgCV x) mulgK.
by rewrite -{2 3}(mulGid G) mulGS sub1set -mem_conjg.
Qed.

Lemma sub_afixRs_norm G x : (G :* x \in 'Fix_('Rs)(G)) = (x \in 'N(G)).
Proof. by rewrite sub_afixRs_norms -groupV inE sub_conjgV. Qed.

Lemma afixRs_rcosets A G : 'Fix_(rcosets G A | 'Rs)(G) = rcosets G 'N_A(G).
Proof.
apply/setP=> Gx; apply/setIP/rcosetsP=> [[/rcosetsP[x Ax ->]]|[x]].
  by rewrite sub_afixRs_norm => Nx; exists x; rewrite // inE Ax.
by case/setIP=> Ax Nx ->; rewrite -{1}rcosetE mem_imset // sub_afixRs_norm.
Qed.

Lemma astab1Rs G : 'C[G : {set gT} | 'Rs] = G.
Proof.
apply/setP=> x.
by apply/astab1P/idP=> /= [<- | Gx]; rewrite rcosetE ?rcoset_refl ?rcoset_id.
Qed.

Lemma actsRs_rcosets H G : [acts G, on rcosets H G | 'Rs].
Proof. by rewrite -orbitRs acts_orbit ?subsetT. Qed.

Lemma transRs_rcosets H G : [transitive G, on rcosets H G | 'Rs].
Proof. by rewrite -orbitRs atrans_orbit. Qed.

(* This is the second part of Aschbacher (5.7) *)
Lemma astabRs_rcosets H G : 'C(rcosets H G | 'Rs) = gcore H G.
Proof.
have transGH := transRs_rcosets H G.
by rewrite (astab_trans_gcore transGH (orbit_refl _ G _)) astab1Rs.
Qed.

Lemma orbitJs G A : orbit 'Js G A = A :^: G. Proof. by []. Qed.

Lemma astab1Js A : 'C[A | 'Js] = 'N(A).
Proof. by apply/setP=> x; apply/astab1P/normP. Qed.

Lemma card_conjugates A G : #|A :^: G| = #|G : 'N_G(A)|.
Proof. by rewrite card_orbit astab1Js. Qed.

Lemma afixJG G A : (G \in 'Fix_('JG)(A)) = (A \subset 'N(G)).
Proof. by apply/afixP/normsP=> nG x Ax; apply/eqP; move/eqP: (nG x Ax). Qed.

Lemma astab1JG G : 'C[G | 'JG] = 'N(G).
Proof.
by apply/setP=> x; apply/astab1P/normP=> [/congr_group | /group_inj].
Qed.

Lemma dom_qactJ H : qact_dom 'J H = 'N(H).
Proof. by rewrite qact_domE ?subsetT ?astabsJ. Qed.

Lemma qactJ H (Hy : coset_of H) x :
  'Q%act Hy x = if x \in 'N(H) then Hy ^ coset H x else Hy.
Proof.
case: (cosetP Hy) => y Ny ->{Hy}.
by rewrite qactEcond // dom_qactJ; case Nx: (x \in 'N(H)); rewrite ?morphJ.
Qed.

Lemma actsQ A B H :
  A \subset 'N(H) -> A \subset 'N(B) -> [acts A, on B / H | 'Q].
Proof.
by move=> nHA nBA; rewrite acts_quotient // subsetI dom_qactJ nHA astabsJ.
Qed.

Lemma astabsQ G H : H <| G -> 'N(G / H | 'Q) = 'N(H) :&: 'N(G).
Proof. by move=> nsHG; rewrite astabs_quotient // dom_qactJ astabsJ. Qed.

Lemma astabQ H Abar : 'C(Abar |'Q) = coset H @*^-1 'C(Abar).
Proof.
apply/setP=> x; rewrite inE /= dom_qactJ morphpreE in_setI /=.
apply: andb_id2l => Nx; rewrite !inE -sub1set centsC cent_set1.
apply: eq_subset_r => {Abar} Hy; rewrite inE qactJ Nx (sameP eqP conjg_fixP).
by rewrite (sameP cent1P eqP) (sameP commgP eqP).
Qed.

Lemma sub_astabQ A H Bbar :
  (A \subset 'C(Bbar | 'Q)) = (A \subset 'N(H)) && (A / H \subset 'C(Bbar)).
Proof.
rewrite astabQ -morphpreIdom subsetI; apply: andb_id2l => nHA.
by rewrite -sub_quotient_pre.
Qed.

Lemma sub_astabQR A B H :
     A \subset 'N(H) -> B \subset 'N(H) ->
  (A \subset 'C(B / H | 'Q)) = ([~: A, B] \subset H).
Proof.
move=> nHA nHB; rewrite sub_astabQ nHA /= (sameP commG1P eqP).
by rewrite eqEsubset sub1G andbT -quotientR // quotient_sub1 // comm_subG.
Qed.

Lemma astabQR A H : A \subset 'N(H) ->
  'C(A / H | 'Q) = [set x in 'N(H) | [~: [set x], A] \subset H].
Proof.
move=> nHA; apply/setP=> x; rewrite astabQ -morphpreIdom 2!inE -astabQ.
by case nHx: (x \in _); rewrite //= -sub1set sub_astabQR ?sub1set.
Qed.

Lemma quotient_astabQ H Abar : 'C(Abar | 'Q) / H = 'C(Abar).
Proof. by rewrite astabQ cosetpreK. Qed.

Lemma conj_astabQ A H x :
  x \in 'N(H) -> 'C(A / H | 'Q) :^ x = 'C(A :^ x / H | 'Q).
Proof.
move=> nHx; apply/setP=> y; rewrite !astabQ mem_conjg !in_setI -mem_conjg.
rewrite -normJ (normP nHx) quotientJ //; apply/andb_id2l => nHy.
by rewrite !inE centJ morphJ ?groupV ?morphV // -mem_conjg.
Qed.

Section CardClass.

Variable G : {group gT}.

Lemma index_cent1 x : #|G : 'C_G[x]| = #|x ^: G|.
Proof. by rewrite -astab1J -card_orbit. Qed.

Lemma classes_partition : partition (classes G) G.
Proof. by apply: orbit_partition; apply/actsP=> x Gx y; apply: groupJr. Qed.

Lemma sum_card_class : \sum_(C in classes G) #|C| = #|G|.
Proof. by apply: acts_sum_card_orbit; apply/actsP=> x Gx y; apply: groupJr. Qed.

Lemma class_formula : \sum_(C in classes G) #|G : 'C_G[repr C]| = #|G|.
Proof.
rewrite -sum_card_class; apply: eq_bigr => _ /imsetP[x Gx ->].
have: x \in x ^: G by rewrite -{1}(conjg1 x) mem_imset.
by case/mem_repr/imsetP=> y Gy ->; rewrite index_cent1 classGidl.
Qed.

Lemma abelian_classP : reflect {in G, forall x, x ^: G = [set x]} (abelian G).
Proof.
rewrite /abelian -astabJ astabC.
by apply: (iffP subsetP) => cGG x Gx; apply/orbit1P; apply: cGG.
Qed.

Lemma card_classes_abelian : abelian G = (#|classes G| == #|G|).
Proof.
have cGgt0 C: C \in classes G -> 1 <= #|C| ?= iff (#|C| == 1)%N.
  by case/imsetP=> x _ ->; rewrite eq_sym -index_cent1.
rewrite -sum_card_class -sum1_card (leqif_sum cGgt0).
apply/abelian_classP/forall_inP=> [cGG _ /imsetP[x Gx ->]| cGG x Gx].
  by rewrite cGG ?cards1.
apply/esym/eqP; rewrite eqEcard sub1set cards1 class_refl leq_eqVlt cGG //.
exact: mem_imset.
Qed.

End CardClass.

End InternalGroupAction.

Lemma gacentQ (gT : finGroupType) (H : {group gT}) (A : {set gT}) :
  'C_(|'Q)(A) = 'C(A / H).
Proof.
apply/setP=> Hx; case: (cosetP Hx) => x Nx ->{Hx}.
rewrite -sub_cent1 -astab1J astabC sub1set -(quotientInorm H A).
have defD: qact_dom 'J H = 'N(H) by rewrite qact_domE ?subsetT ?astabsJ.
rewrite !(inE, mem_quotient) //= defD setIC.
apply/subsetP/subsetP=> [cAx _ /morphimP[a Na Aa ->] | cAx a Aa].
  by move/cAx: Aa; rewrite !inE qactE ?defD ?morphJ.
have [_ Na] := setIP Aa; move/implyP: (cAx (coset H a)); rewrite mem_morphim //.
by rewrite !inE qactE ?defD ?morphJ.
Qed.

Section AutAct.

Variable (gT : finGroupType) (G : {set gT}).

Definition autact := act ('P \ subsetT (Aut G)).
Canonical aut_action := [action of autact].

Lemma autactK a : actperm aut_action a = a.
Proof. by apply/permP=> x; rewrite permE. Qed.

Lemma autact_is_groupAction : is_groupAction G aut_action.
Proof. by move=> a Aa /=; rewrite autactK. Qed.
Canonical aut_groupAction := GroupAction autact_is_groupAction.

End AutAct.

Arguments autact {gT} G%g.
Arguments aut_action {gT} G%g.
Arguments aut_groupAction {gT} G%g.
Notation "[ 'Aut' G ]" := (aut_action G) : action_scope.
Notation "[ 'Aut' G ]" := (aut_groupAction G) : groupAction_scope.



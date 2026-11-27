(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice.
(* for some Reserved Notations *)
From mathcomp Require Import finset.

(**md**************************************************************************)
(* # Set Theory                                                               *)
(*                                                                            *)
(* This file develops a basic theory of sets.                                 *)
(*                                                                            *)
(* About the naming conventions in this file:                                 *)
(* - use T, T', T1, T2, etc., aT (domain type), rT (return type) for names    *)
(*   of variables in Type (or choiceType/pointedType/porderType)              *)
(*   + use the same suffix or prefix for the sets as their containing type    *)
(*     (e.g., A1 in T1, etc.)                                                 *)
(*   + as a consequence functions are rather of type aT -> rT                 *)
(* - use I, J when the type corresponds to an index                           *)
(* - sets are named A, B, C, D, etc., or Y when it is ostensibly an image     *)
(*   set (i.e., of type set rT)                                               *)
(* - indexed sets are rather named F                                          *)
(*                                                                            *)
(* Examples of notations:                                                     *)
(* | Rocq notations               |   | Meaning                             | *)
(* |-----------------------------:|---|:------------------------------------  *)
(* |                         set0 |==| $\emptyset$                            *)
(* |                     [set: A] |==| the full set of elements of type A     *)
(* |                   `` `\|` `` |==| $\cup$                                 *)
(* |                    `` `&` `` |==| $\cap$                                 *)
(* |                    `` `\` `` |==| set difference                         *)
(* |                    `` `+` `` |==| symmetric difference                   *)
(* |                     `` ~` `` |==| set complement                         *)
(* |                   `` `<=` `` |==| $\subseteq$                            *)
(* |                 `` f @` A `` |==| image by f of A                        *)
(* |              `` f @^-1` A `` |==| preimage by f of A                     *)
(* |                      [set x] |==| the singleton set $\{x\}$              *)
(* |                     [set~ x] |==| the complement of $\{x\}$              *)
(* |            [set E \| x in P] |==| the set of E with x ranging in P       *)
(* |                      range f |==| image by f of the full set             *)
(* | \big[setU/set0]_(i <- s \| P i) f i |==| finite union                    *)
(* |         \bigcup_(k in P) F k |==| arbitrary union                        *)
(* |         \bigcap_(k in P) F k |==| arbitrary intersection                 *)
(* |                 trivIset D F |==| F is a sequence of pairwise disjoint   *)
(* |                              |  | sets indexed over the domain D         *)
(*                                                                            *)
(* Detailed documentation:                                                    *)
(* ## Sets                                                                    *)
(* ```                                                                        *)
(*                       set T == type of sets on T                           *)
(*                   (x \in P) == boolean membership predicate from ssrbool   *)
(*                                for set P, available thanks to a canonical  *)
(*                                predType T structure on sets on T           *)
(*             [set x : T | P] == set of points x : T such that P holds       *)
(*                 [set x | P] == same as before with T left implicit         *)
(*            [set E | x in A] == set defined by the expression E for x in    *)
(*                                set A                                       *)
(*   [set E | x in A & y in B] == same as before for E depending on 2         *)
(*                                variables x and y in sets A and B           *)
(*                        setT == full set                                    *)
(*                        set0 == empty set                                   *)
(*                     range f == the range of f, i.e., [set f x | x in setT] *)
(*                     [set a] == set containing only a                       *)
(*                 [set a : T] == same as before with the type of a made      *)
(*                                explicit                                    *)
(*                     A `|` B == union of A and B                            *)
(*                      a |` A == A extended with a                           *)
(*        [set a1; a2; ..; an] == set containing only the n elements ai       *)
(*                     A `&` B == intersection of A and B                     *)
(*                     A `*` B == product of A and B, i.e., set of pairs      *)
(*                                (a,b) such that A a and B b                 *)
(*                        A.`1 == set of points a such that there exists b so *)
(*                                that A (a, b)                               *)
(*                        A.`2 == set of points a such that there exists b so *)
(*                                that A (b, a)                               *)
(*                        ~` A == complement of A                             *)
(*                    [set~ a] == complement of [set a]                       *)
(*                     A `\` B == complement of B in A                        *)
(*                      A `\ a == A deprived of a                             *)
(*                        `I_n := [set k | k < n]                             *)
(*                   A `<=` B <-> A is included in B                          *)
(*                     A `<` B := A `<=` B /\ ~ (B `<=` A)                    *)
(*                  A `<=>` B <-> double inclusion A `<=` B and B `<=` A      *)
(*                   f @^-1` A == preimage of A by f                          *)
(*                      f @` A == image of A by f                             *)
(*                                This is a notation for `image A f`          *)
(*                    A !=set0 := exists x, A x                               *)
(*                    [set` p] == a set corresponding to the predType p       *)
(*          \bigcup_(i in P) F == union of the elements of the family F whose *)
(*                                index satisfies P                           *)
(*           \bigcup_(i : T) F == union of the family F indexed on T          *)
(*           \bigcup_(i < n) F := \bigcup_(i in `I_n) F                       *)
(*          \bigcup_(i >= n) F := \bigcup_(i in [set i | i >= n]) F           *)
(*                 \bigcup_i F == same as before with T left implicit         *)
(*          \bigcap_(i in P) F == intersection of the elements of the family  *)
(*                                F whose index satisfies P                   *)
(*           \bigcap_(i : T) F == union of the family F indexed on T          *)
(*           \bigcap_(i < n) F := \bigcap_(i in `I_n) F                       *)
(*          \bigcap_(i >= n) F := \bigcap_(i in [set i | i >= n]) F           *)
(*                 \bigcap_i F == same as before with T left implicit         *)
(* ```                                                                        *)
(*                                                                            *)
(* ### About sets of sets                                                     *)
(* ```                                                                        *)
(*                set_system T := set (set T)                                 *)
(*               setI_closed G == the set of sets G is closed under finite    *)
(*                                intersection                                *)
(*               setU_closed G == the set of sets G is closed under finite    *)
(*                                union                                       *)
(*   preimage_set_system D f G == set system of the preimages by f of sets    *)
(*                                in G                                        *)
(*      image_set_system D f G == set system of the sets with a preimage      *)
(*                                by f in G                                   *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* TODO: Rename to `set_scope`? *)
Declare Scope near_scope.
Declare Scope relation_scope.
Delimit Scope relation_scope with relation.

Reserved Notation "[ 'set' x : T | P ]".
Reserved Notation "[ 'set' x | P ]" (format "[ 'set'  x  |  P ]").
Reserved Notation "[ 'set' E | x 'in' A ]"
  (format "[ '[hv' 'set'  E '/ '  |  x  'in'  A ] ']'").
Reserved Notation "[ 'set' E | x 'in' A & y 'in' B ]"
  (format "[ '[hv' 'set'  E '/ '  |  x  'in'  A  &  y  'in'  B ] ']'").
Reserved Notation "[ 'set' a ]" (format "[ 'set'  a ]").
Reserved Notation "[ 'set' : T ]" (format "[ 'set' :  T ]").
Reserved Notation "[ 'set' a : T ]" (format "[ 'set'  a   :  T ]").
Reserved Notation "A `|` B" (at level 52, left associativity).
Reserved Notation "a |` A" (at level 52, left associativity).
Reserved Notation "A `&` B"  (at level 48, left associativity).
Reserved Notation "A `*` B"  (at level 46, left associativity).
Reserved Notation "A `*`` B"  (at level 46, left associativity).
Reserved Notation "A ``*` B"  (at level 46, left associativity).
Reserved Notation "A .`1" (format "A .`1").
Reserved Notation "A .`2" (format "A .`2").
Reserved Notation "~` A" (at level 35, right associativity).
Reserved Notation "[ 'set' ~ a ]" (format "[ 'set' ~  a ]").
Reserved Notation "A `\` B" (at level 50, left associativity).
Reserved Notation "A `\ b" (at level 50, left associativity).
Reserved Notation "A `+` B" (at level 54, left associativity).
Reserved Notation "A `<` B" (at level 70, no associativity).
Reserved Notation "A `<=` B" (at level 70, no associativity).
Reserved Notation "A `<=>` B" (at level 70, no associativity).
Reserved Notation "f @^-1` A" (at level 24).
Reserved Notation "f @` A" (at level 24).
#[warnings="-postfix-notation-not-level-1"]
Reserved Notation "A !=set0" (at level 80).
Reserved Notation "[ 'set`' p ]" (format "[ 'set`'  p ]").
Reserved Notation "'`I_' n" (at level 8, n at level 2, format "'`I_' n").

Definition set T := T -> Prop.

Bind Scope near_scope with set.
Local Open Scope near_scope.
Delimit Scope near_scope with set.

Definition mkset {T} (P : T -> Prop) : set T := P.
Arguments mkset _ _ _ /.

Notation "[ 'set' x : T | P ]" := (mkset (fun x : T => P)) : near_scope.
Notation "[ 'set' x | P ]" := [set x : _ | P] : near_scope.

Definition image {T rT} (A : set T) (f : T -> rT) :=
  [set y | exists2 x, A x & f x = y].
Arguments image _ _ _ _ _ /.
Notation "[ 'set' E | x 'in' A ]" :=
  (image A (fun x => E)) : near_scope.

Definition image2 {TA TB rT} (A : set TA) (B : set TB) (f : TA -> TB -> rT) :=
  [set z | exists2 x, A x & exists2 y, B y & f x y = z].
Arguments image2 _ _ _ _ _ _ _ /.
Notation "[ 'set' E | x 'in' A & y 'in' B ]" :=
  (image2 A B (fun x y => E)) : near_scope.

Section basic_definitions.
Context {T rT : Type}.
Implicit Types (T : Type) (A B : set T) (f : T -> rT) (Y : set rT).

Definition preimage f Y : set T := [set t | Y (f t)].

Definition setT := [set _ : T | True].
Definition set0 := [set _ : T | False].
Definition set1 (t : T) := [set x : T | x = t].
Definition setI A B := [set x | A x /\ B x].
Definition setU A B := [set x | A x \/ B x].
Definition nonempty A := exists a, A a.
Definition setC A := [set a | ~ A a].
Definition setD A B := [set x | A x /\ ~ B x].
Definition setX T1 T2 (A1 : set T1) (A2 : set T2) := [set z | A1 z.1 /\ A2 z.2].
Definition fst_set T1 T2 (A : set (T1 * T2)) := [set x | exists y, A (x, y)].
Definition snd_set T1 T2 (A : set (T1 * T2)) := [set y | exists x, A (x, y)].
Definition setXR T1 T2 (A1 : set T1) (A2 : T1 -> set T2) :=
  [set z | A1 z.1 /\ A2 z.1 z.2].
Definition setXL T1 T2 (A1 : T2 -> set T1) (A2 : set T2) :=
  [set z | A1 z.2 z.1 /\ A2 z.2].

Lemma mksetE (P : T -> Prop) x : [set x | P x] x = P x.
Proof. by []. Qed.

Definition bigcap T I (P : set I) (F : I -> set T) :=
  [set a | forall i, P i -> F i a].
Definition bigcup T I (P : set I) (F : I -> set T) :=
  [set a | exists2 i, P i & F i a].

Definition subset A B := forall t, A t -> B t.
Local Notation "A `<=` B" := (subset A B).

Definition proper A B := A `<=` B /\ ~ (B `<=` A).

End basic_definitions.
Arguments preimage T rT f Y t /.
Arguments set0 _ _ /.
Arguments setT _ _ /.
Arguments set1 _ _ _ /.
Arguments setI _ _ _ _ /.
Arguments setU _ _ _ _ /.
Arguments setC _ _ _ /.
Arguments setD _ _ _ _ /.
Arguments setX _ _ _ _ _ /.
Arguments setXR _ _ _ _ _ /.
Arguments setXL _ _ _ _ _ /.
Arguments fst_set _ _ _ _ /.
Arguments snd_set _ _ _ _ /.

Notation range F := [set F i | i in setT].
Notation "[ 'set' a ]" := (set1 a) : near_scope.
Notation "[ 'set' a : T ]" := [set (a : T)] : near_scope.
Notation "[ 'set' : T ]" := (@setT T) : near_scope.
Notation "A `|` B" := (setU A B) : near_scope.
Notation "a |` A" := ([set a] `|` A) : near_scope.
Notation "[ 'set' a1 ; a2 ; .. ; an ]" :=
  (setU .. (a1 |` [set a2]) .. [set an]) : near_scope.
Notation "A `&` B" := (setI A B) : near_scope.
Notation "A `*` B" := (setX A B) : near_scope.
Notation "A .`1" := (fst_set A) : near_scope.
Notation "A .`2" := (snd_set A) : near_scope.
Notation "A `*`` B" := (setXR A B) : near_scope.
Notation "A ``*` B" := (setXL A B) : near_scope.
Notation "~` A" := (setC A) : near_scope.
Notation "[ 'set' ~ a ]" := (~` [set a]) : near_scope.
Notation "A `\` B" := (setD A B) : near_scope.
Notation "A `\ a" := (A `\` [set a]) : near_scope.

Definition setY {T : Type} (A B : set T) := (A `\` B) `|` (B `\` A).
Arguments setY _ _ _ _ /.
Notation "A `+` B" := (setY A B) : near_scope.

Notation "'`I_' n" := [set k | is_true (k < n)%N].

Notation "\bigcup_ ( i 'in' P ) F" :=
  (bigcup P (fun i => F)) : near_scope.
Notation "\bigcup_ ( i : T ) F" :=
  (\bigcup_(i in @setT T) F) : near_scope.
Notation "\bigcup_ ( i < n ) F" :=
  (\bigcup_(i in `I_n) F) : near_scope.
Notation "\bigcup_ ( i >= n ) F" :=
  (\bigcup_(i in [set i | (n <= i)%N]) F) : near_scope.
Notation "\bigcup_ i F" := (\bigcup_(i : _) F) : near_scope.
Notation "\bigcap_ ( i 'in' P ) F" :=
  (bigcap P (fun i => F)) : near_scope.
Notation "\bigcap_ ( i : T ) F" :=
  (\bigcap_(i in @setT T) F) : near_scope.
Notation "\bigcap_ ( i < n ) F" :=
  (\bigcap_(i in `I_n) F) : near_scope.
Notation "\bigcap_ ( i >= n ) F" :=
  (\bigcap_(i in [set i | (n <= i)%N]) F) : near_scope.
Notation "\bigcap_ i F" := (\bigcap_(i : _) F) : near_scope.

Notation "A `<=` B" := (subset A B) : near_scope.
Notation "A `<` B" := (proper A B) : near_scope.

Notation "A `<=>` B" := ((A `<=` B) /\ (B `<=` A)) : near_scope.
Notation "f @^-1` A" := (preimage f A) : near_scope.
Notation "f @` A" := (image A f) (only parsing) : near_scope.
Notation "A !=set0" := (nonempty A) : near_scope.

Notation "[ 'set`' p ]":= [set x | is_true (x \in p)] : near_scope.
Notation pred_set := (fun i => [set` i]).

Section basic_lemmas.
Context {T : Type}.
Implicit Types A B C D : set T.

Lemma setDE A B : A `\` B = A `&` ~` B. Proof. by []. Qed.

Lemma subset_refl A : A `<=` A. Proof. by []. Qed.

Lemma subset_trans B A C : A `<=` B -> B `<=` C -> A `<=` C.
Proof. by move=> sAB sBC ? ?; apply/sBC/sAB. Qed.

Lemma sub0set A : set0 `<=` A. Proof. by []. Qed.

Lemma properW A B : A `<` B -> A `<=` B. Proof. by case. Qed.

Lemma properxx A : ~ A `<` A. Proof. by move=> [?]; apply. Qed.

Lemma setIS C A B : A `<=` B -> C `&` A `<=` C `&` B.
Proof. by move=> sAB t [Ct At]; split=> //; exact: sAB. Qed.

Lemma setSI C A B : A `<=` B -> A `&` C `<=` B `&` C.
Proof. by move=> sAB t [At Ct]; split=> //; exact: sAB. Qed.

Lemma setISS A B C D : A `<=` C -> B `<=` D -> A `&` B `<=` C `&` D.
Proof. by move=> /(@setSI B) /subset_trans sAC /(@setIS C) /sAC. Qed.

Lemma setUS C A B : A `<=` B -> C `|` A `<=` C `|` B.
Proof. by move=> sAB t [Ct|At]; [left|right; exact: sAB]. Qed.

Lemma setSU C A B : A `<=` B -> A `|` C `<=` B `|` C.
Proof. by move=> sAB t [At|Ct]; [left; exact: sAB|right]. Qed.

Lemma setUSS A B C D : A `<=` C -> B `<=` D -> A `|` B `<=` C `|` D.
Proof. by move=> /(@setSU B) /subset_trans sAC /(@setUS C) /sAC. Qed.

Lemma subsetT A : A `<=` setT. Proof. by []. Qed.

Lemma subsetW {A B} : A = B -> A `<=` B. Proof. by move->. Qed.

Lemma subsetCW {A B} : A = B -> B `<=` A.
Proof. by move->. Qed.

Lemma subset_nonempty A B : A `<=` B -> A !=set0 -> B !=set0.
Proof. by move=> sAB [x Ax]; exists x; apply: sAB. Qed.

Lemma subsetC A B : A `<=` B -> ~` B `<=` ~` A.
Proof. by move=> sAB ? nBa ?; apply/nBa/sAB. Qed.

Lemma subsetUl A B : A `<=` A `|` B. Proof. by move=> x; left. Qed.

Lemma subsetUr A B : B `<=` A `|` B. Proof. by move=> x; right. Qed.

Lemma subUsetP A B C : A `|` B `<=` C <-> (A `<=` C /\ B `<=` C).
Proof.
split=> [AuBC|[AC BC]]; first split.
- by move=> x Ax; apply: AuBC; left.
- by move=> x Bx; apply: AuBC; right.
- by move=> x [/AC|/BC].
Qed.

Lemma subsetIP A B C : A `<=` B `&` C <-> (A `<=` B /\ A `<=` C).
Proof.
split=> [ABiC|[AB AC]]; first by split; move=> x /ABiC[].
by move=> x /[dup] /AB + /AC +.
Qed.

Lemma subIset A B C : A `<=` C \/ B `<=` C -> A `&` B `<=` C.
Proof. case=> sub a; by [move=> [/sub] | move=> [_ /sub]]. Qed.

Lemma subIsetl A B : A `&` B `<=` A. Proof. by move=> x []. Qed.

Lemma subIsetr A B : A `&` B `<=` B. Proof. by move=> x []. Qed.

Lemma subDsetl A B : A `\` B `<=` A.
Proof. by rewrite setDE; apply: subIsetl. Qed.

Lemma subDsetr A B : A `\` B `<=` ~` B.
Proof. by rewrite setDE; apply: subIsetr. Qed.

Lemma subsetI_neq0 A B C D :
  A `<=` B -> C `<=` D -> A `&` C !=set0 -> B `&` D !=set0.
Proof. by move=> AB CD [x [/AB Bx /CD Dx]]; exists x. Qed.

End basic_lemmas.

Section image_lemmas.
Context {aT rT : Type}.
Implicit Types (A B : set aT) (f : aT -> rT) (Y : set rT).

Lemma image_subP {A Y f} : f @` A `<=` Y <-> {homo f : x / A x >-> Y x}.
Proof. by split=> fAY x => [Ax|[y + <-]]; apply: fAY=> //; exists x. Qed.

Lemma nonempty_image f A : f @` A !=set0 -> A !=set0.
Proof. by case=> b [a]; exists a. Qed.

Lemma image_nonempty f A : A !=set0 -> f @` A !=set0.
Proof. by move=> [x] Ax; exists (f x), x. Qed.

Lemma image_subset f A B : A `<=` B -> f @` A `<=` f @` B.
Proof. by move=> AB _ [a Aa <-]; exists a => //; apply/AB. Qed.

Lemma nonempty_preimage f Y : f @^-1` Y !=set0 -> Y !=set0.
Proof. by case=> [t ?]; exists (f t). Qed.

Lemma preimage_image f A : A `<=` f @^-1` (f @` A).
Proof. by move=> a Aa; exists a. Qed.

Lemma image_preimage_subset f Y : f @` (f @^-1` Y) `<=` Y.
Proof. by move=> _ [t /= Yft <-]. Qed.

Lemma preimage_subset f Y1 Y2 : Y1 `<=` Y2 -> f @^-1` Y1 `<=` f @^-1` Y2.
Proof. by move=> Y12 t /Y12. Qed.

Lemma nonempty_preimage_setI f Y1 Y2 :
  (f @^-1` (Y1 `&` Y2)) !=set0 <-> (f @^-1` Y1 `&` f @^-1` Y2) !=set0.
Proof. by split; case=> t ?; exists t. Qed.

End image_lemmas.

Lemma nat_nonempty : [set: nat] !=set0. Proof. by exists 1%N. Qed.

#[global] Hint Resolve nat_nonempty : core.

Definition set_system U := set (set U).
Identity Coercion set_system_to_set : set_system >-> set.

Section set_systems.
Context {T} (G : set_system T).

Definition setI_closed := forall A B, G A -> G B -> G (A `&` B).

Definition setU_closed := forall A B, G A -> G B -> G (A `|` B).

End set_systems.

Definition preimage_set_system {aT rT : Type} (D : set aT) (f : aT -> rT)
    (G : set_system rT) : set_system aT :=
  [set D `&` f @^-1` B | B in G].

Lemma preimage_set_systemS {T1 T2} (A B : set_system T2) (f : T1 -> T2) :
  A `<=` B ->
  preimage_set_system [set: _] f A `<=` preimage_set_system [set: _] f B.
Proof. by move=> AB _ [C ? <-]; exists C => //; exact: AB. Qed.

Definition image_set_system (aT rT : Type) (D : set aT) (f : aT -> rT)
    (G : set_system aT) : set_system rT :=
  [set B : set rT | G (D `&` f @^-1` B)].

Definition bigcap_closed {T} (C : set_system T) :=
  forall (MM : set_system T), MM `<=` C -> C (\bigcap_(A in MM) A).

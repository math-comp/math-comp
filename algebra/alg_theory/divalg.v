(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
From mathcomp Require Import choice fintype finfun bigop prime binomial.
From mathcomp Require Import nmodule algebra.

(******************************************************************************)
(*              Ring-like structures with multiplicative inverse              *)
(*                                                                            *)
(* NB: See CONTRIBUTING.md for an introduction to HB concepts and commands.   *)
(*     See ssralg.v for general remarks about the module layout, the notation *)
(*     scopes, and the naming convention.                                     *)
(*                                                                            *)
(* Reference: Francois Garillot, Georges Gonthier, Assia Mahboubi, Laurence   *)
(* Rideau, Packaging mathematical structures, TPHOLs 2009                     *)
(*                                                                            *)
(* This file defines the following algebraic structures:                      *)
(*                                                                            *)
(*    unitRingType == Rings whose units have computable inverses              *)
(*                    The HB class is called UnitRing.                        *)
(* comUnitRingType == commutative UnitRing                                    *)
(*                    The HB class is called ComUnitRing.                     *)
(*   unitAlgType R == algebra with computable inverses                        *)
(*                    The HB class is called UnitAlgebra.                     *)
(*comUnitAlgType R == commutative UnitAlgebra                                 *)
(*                    The HB class is called ComUnitAlgebra.                  *)
(*     idomainType == integral, commutative, ring with partial inverses       *)
(*                    The HB class is called IntegralDomain.                  *)
(*       fieldType == commutative fields                                      *)
(*                    The HB class is called Field.                           *)
(*    decFieldType == fields with a decidable first order theory              *)
(*                    The HB class is called DecidableField.                  *)
(* closedFieldType == algebraically closed fields                             *)
(*                    The HB class is called ClosedField.                     *)
(*                                                                            *)
(* and their joins with subType:                                              *)
(*                                                                            *)
(*     subUnitRingType R P == join of unitRingType and subType (P : pred R)   *)
(*                            such that val is a ring morphism                *)
(*                            The HB class is called SubUnitRing.             *)
(*  subComUnitRingType R P == join of comUnitRingType and subType (P : pred R)*)
(*                            such that val is a ring morphism                *)
(*                            The HB class is called SubComUnitRing.          *)
(*      subIdomainType R P == join of idomainType and subType (P : pred R)    *)
(*                            such that val is a ring morphism                *)
(*                            The HB class is called SubIntegralDomain.       *)
(*            subField R P == join of fieldType and subType (P : pred R)      *)
(*                            such that val is a ring morphism                *)
(*                            The HB class is called SubField.                *)
(*                                                                            *)
(* Closedness predicates for the algebraic structures:                        *)
(*                                                                            *)
(*   divClosed R == predicate closed under division                           *)
(*                  The HB class is called DivClosed.                         *)
(*  sdivClosed R == predicate closed under division and opposite              *)
(*                  The HB class is called SdivClosed.                        *)
(* divringClosed R == predicate closed under unitRingType operations          *)
(*                  The HB class is called DivringClosed.                     *)
(* divalgClosed R S == predicate closed under unitAlgType operations          *)
(*                  The HB class is called DivalgClosed.                      *)
(*                                                                            *)
(* Canonical properties of the algebraic structures:                          *)
(*                                                                            *)
(*  * UnitRing (NzRings whose units have computable inverses):                *)
(*     x \is a GRing.unit <=> x is a unit (i.e., has an inverse)              *)
(*                   x^-1 == the ring inverse of x, if x is a unit, else x    *)
(*                  x / y == x divided by y (notation for x * y^-1)           *)
(*                 x ^- n := notation for (x ^+ n)^-1, the inverse of x ^+ n  *)
(*         invr_closed S <-> collective predicate S is closed under inverse   *)
(*         divr_closed S <-> collective predicate S is closed under division  *)
(*                           (1 and x / y in S)                               *)
(*        sdivr_closed S <-> collective predicate S is closed under division  *)
(*                           and opposite (-1 and x / y in S, for x, y in S)  *)
(*      divring_closed S <-> collective predicate S is closed under unitRing  *)
(*                           operations (1, x - y and x / y in S)             *)
(* [SubNzRing_isSubUnitRing of R by <:] ==                                    *)
(* [SubChoice_isSubUnitRing of R by <:] == unitRingType mixin for a subType   *)
(*                           whose base type is a unitRingType and whose      *)
(*                           predicate's is a divringClosed and whose ring    *)
(*                           structure is compatible with the base type's     *)
(*                                                                            *)
(*  * ComUnitRing (commutative rings with computable inverses):               *)
(* [SubChoice_isSubComUnitRing of R by <:] == comUnitRingType mixin for a     *)
(*                           subType whose base type is a comUnitRingType and *)
(*                           whose predicate's is a divringClosed and whose   *)
(*                           ring structure is compatible with the base       *)
(*                           type's                                           *)
(*                                                                            *)
(*  * IntegralDomain (integral, commutative, ring with partial inverses):     *)
(* [SubComUnitRing_isSubIntegralDomain R by <:] ==                            *)
(* [SubChoice_isSubIntegralDomain R by <:] == mixin axiom for a idomain       *)
(*                           subType                                          *)
(*                                                                            *)
(*  * Field (commutative fields):                                             *)
(*  GRing.Field.axiom inv == field axiom: x != 0 -> inv x * x = 1 for all x   *)
(*                           This is equivalent to the property above, but    *)
(*                           does not require a unitRingType as inv is an     *)
(*                           explicit argument.                               *)
(* [SubIntegralDomain_isSubField of R by <:] == mixin axiom for a field       *)
(*                           subType                                          *)
(*                                                                            *)
(*  * DecidableField (fields with a decidable first order theory):            *)
(*           GRing.term R == the type of formal expressions in a unit ring R  *)
(*                           with formal variables 'X_k, k : nat, and         *)
(*                           manifest constants x%:T, x : R                   *)
(*                           The notation of all the ring operations is       *)
(*                           redefined for terms, in scope %T.                *)
(*        GRing.formula R == the type of first order formulas over R; the %T  *)
(*                           scope binds the logical connectives /\, \/, ~,   *)
(*                           ==>, ==, and != to formulae; GRing.True/False    *)
(*                           and GRing.Bool b denote constant formulae, and   *)
(*                           quantifiers are written 'forall/'exists 'X_k, f  *)
(*                             GRing.Unit x tests for ring units              *)
(*                             GRing.If p_f t_f e_f emulates if-then-else     *)
(*                             GRing.Pick p_f t_f e_f emulates fintype.pick   *)
(*                             foldr GRing.Exists/Forall q_f xs can be used   *)
(*                               to write iterated quantifiers                *)
(*         GRing.eval e t == the value of term t with valuation e : seq R     *)
(*                           (e maps 'X_i to e`_i)                            *)
(*  GRing.same_env e1 e2 <-> environments e1 and e2 are extensionally equal   *)
(*        GRing.qf_form f == f is quantifier-free                             *)
(*        GRing.holds e f == the intuitionistic CiC interpretation of the     *)
(*                           formula f holds with valuation e                 *)
(*      GRing.qf_eval e f == the value (in bool) of a quantifier-free f       *)
(*          GRing.sat e f == valuation e satisfies f (only in a decField)     *)
(*          GRing.sol n f == a sequence e of size n such that e satisfies f,  *)
(*                           if one exists, or [::] if there is no such e     *)
(*        'exists 'X_i, u1 == 0 /\ ... /\ u_m == 0 /\ v1 != 0 ... /\ v_n != 0 *)
(*                                                                            *)
(*  * UnitAlgebra (algebra with computable inverses):                         *)
(*        divalg_closed S <-> collective predicate S is closed under all      *)
(*                           unitAlgType operations (1, a *: u + v and u / v  *)
(*                           are in S fo u, v in S)                           *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Module Import GRing.

(* FIXME: Since we should not import GRing, we should be able to remove this: *)
Export GRing.

HB.mixin Record NzRing_hasMulInverse R of NzRing R := {
  unit_subdef : pred R;
  inv : R -> R;
  mulVr_subproof : {in unit_subdef, left_inverse 1 inv *%R};
  divrr_subproof : {in unit_subdef, right_inverse 1 inv *%R};
  unitrP_subproof : forall x y, y * x = 1 /\ x * y = 1 -> unit_subdef x;
  invr_out_subproof : {in [predC unit_subdef], inv =1 id}
}.

Module Ring_hasMulInverse.
#[deprecated(since="mathcomp 2.4.0", use=NzRing_hasMulInverse.Build)]
Notation Build R := (NzRing_hasMulInverse.Build R) (only parsing).
End Ring_hasMulInverse.

#[deprecated(since="mathcomp 2.4.0", use=NzRing_hasMulInverse)]
Notation Ring_hasMulInverse R := (NzRing_hasMulInverse R) (only parsing).

#[short(type="unitRingType")]
HB.structure Definition UnitRing := {R of NzRing_hasMulInverse R & NzRing R}.

Module UnitRingExports.
Bind Scope ring_scope with UnitRing.sort.
End UnitRingExports.
HB.export UnitRingExports.

Definition unit_pred {R : unitRingType} :=
  Eval cbv [ unit_subdef NzRing_hasMulInverse.unit_subdef ] in
    (fun u : R => unit_subdef u).
Arguments unit_pred _ _ /.
Definition unit {R : unitRingType} := [qualify a u : R | unit_pred u].

Local Notation "x ^-1" := (inv x).
Local Notation "x / y" := (x * y^-1).
Local Notation "x ^- n" := ((x ^+ n)^-1).

Section UnitRingTheory.

Variable R : unitRingType.
Implicit Types x y : R.

Lemma divrr : {in unit, right_inverse 1 (@inv R) *%R}.
Proof. exact: divrr_subproof. Qed.
Definition mulrV := divrr.

Lemma mulVr : {in unit, left_inverse 1 (@inv R) *%R}.
Proof. exact: mulVr_subproof. Qed.

Lemma invr_out x : x \isn't a unit -> x^-1 = x.
Proof. exact: invr_out_subproof. Qed.

Lemma unitrP x : reflect (exists y, y * x = 1 /\ x * y = 1) (x \is a unit).
Proof.
apply: (iffP idP) => [Ux | []]; last exact: unitrP_subproof.
by exists x^-1; rewrite divrr ?mulVr.
Qed.

Lemma mulKr : {in unit, left_loop (@inv R) *%R}.
Proof. by move=> x Ux y; rewrite mulrA mulVr ?mul1r. Qed.

Lemma mulVKr : {in unit, rev_left_loop (@inv R) *%R}.
Proof. by move=> x Ux y; rewrite mulrA mulrV ?mul1r. Qed.

Lemma mulrK : {in unit, right_loop (@inv R) *%R}.
Proof. by move=> x Ux y; rewrite -mulrA divrr ?mulr1. Qed.

Lemma mulrVK : {in unit, rev_right_loop (@inv R) *%R}.
Proof. by move=> x Ux y; rewrite -mulrA mulVr ?mulr1. Qed.
Definition divrK := mulrVK.

Lemma mulrI : {in @unit R, right_injective *%R}.
Proof. by move=> x Ux; apply: can_inj (mulKr Ux). Qed.

Lemma mulIr : {in @unit R, left_injective *%R}.
Proof. by move=> x Ux; apply: can_inj (mulrK Ux). Qed.

(* Due to noncommutativity, fractions are inverted. *)
Lemma telescope_prodr n m (f : nat -> R) :
    (forall k, n < k < m -> f k \is a unit) -> n < m ->
  \prod_(n <= k < m) (f k / f k.+1) = f n / f m.
Proof.
move=> Uf ltnm; rewrite (telescope_big (fun i j => f i / f j)) ?ltnm//.
by move=> k ltnkm /=; rewrite mulrA divrK// Uf.
Qed.

Lemma telescope_prodr_eq n m (f u : nat -> R) : n < m ->
    (forall k, n < k < m -> f k \is a unit) ->
    (forall k, (n <= k < m)%N -> u k = f k / f k.+1) ->
  \prod_(n <= k < m) u k = f n / f m.
Proof.
by move=> ? ? uE; under eq_big_nat do rewrite uE //=; exact: telescope_prodr.
Qed.

Lemma commrV x y : comm x y -> comm x y^-1.
Proof.
have [Uy cxy | /invr_out-> //] := boolP (y \in unit).
by apply: (canLR (mulrK Uy)); rewrite -mulrA cxy mulKr.
Qed.

Lemma unitrE x : (x \is a unit) = (x / x == 1).
Proof.
apply/idP/eqP=> [Ux | xx1]; first exact: divrr.
by apply/unitrP; exists x^-1; rewrite -commrV.
Qed.

Lemma invrK : involutive (@inv R).
Proof.
move=> x; case Ux: (x \in unit); last by rewrite !invr_out ?Ux.
rewrite -(mulrK Ux _^-1) -mulrA commrV ?mulKr //.
by apply/unitrP; exists x; rewrite divrr ?mulVr.
Qed.

Lemma invr_inj : injective (@inv R). Proof. exact: inv_inj invrK. Qed.

Lemma unitrV x : (x^-1 \in unit) = (x \in unit).
Proof. by rewrite !unitrE invrK commrV. Qed.

Lemma unitr1 : 1 \in @unit R.
Proof. by apply/unitrP; exists 1; rewrite mulr1. Qed.

Lemma invr1 : 1^-1 = 1 :> R.
Proof. by rewrite -{2}(mulVr unitr1) mulr1. Qed.

Lemma div1r x : 1 / x = x^-1. Proof. by rewrite mul1r. Qed.
Lemma divr1 x : x / 1 = x. Proof. by rewrite invr1 mulr1. Qed.

Lemma natr_div m d :
  d %| m -> d%:R \is a @unit R -> (m %/ d)%:R = m%:R / d%:R :> R.
Proof.
by rewrite dvdn_eq => /eqP def_m unit_d; rewrite -{2}def_m natrM mulrK.
Qed.

Lemma divrI : {in unit, right_injective (fun x y => x / y)}.
Proof. by move=> x /mulrI/inj_comp; apply; apply: invr_inj. Qed.

Lemma divIr : {in unit, left_injective (fun x y => x / y)}.
Proof. by move=> x; rewrite -unitrV => /mulIr. Qed.

Lemma unitr0 : (0 \is a @unit R) = false.
Proof. by apply/unitrP=> [[x [_ /esym/eqP]]]; rewrite mul0r oner_eq0. Qed.

Lemma invr0 : 0^-1 = 0 :> R.
Proof. by rewrite invr_out ?unitr0. Qed.

Lemma unitrN1 : -1 \is a @unit R.
Proof. by apply/unitrP; exists (-1); rewrite mulrNN mulr1. Qed.

Lemma invrN1 : (-1)^-1 = -1 :> R.
Proof. by rewrite -{2}(divrr unitrN1) mulN1r opprK. Qed.

Lemma invr_sign n : ((-1) ^- n) = (-1) ^+ n :> R.
Proof. by rewrite -signr_odd; case: (odd n); rewrite (invr1, invrN1). Qed.

Lemma unitrMl x y : y \is a unit -> (x * y \is a unit) = (x \is a unit).
Proof.
move=> Uy; wlog Ux: x y Uy / x \is a unit => [WHxy|].
  by apply/idP/idP=> Ux; first rewrite -(mulrK Uy x); rewrite WHxy ?unitrV.
rewrite Ux; apply/unitrP; exists (y^-1 * x^-1).
by rewrite -!mulrA mulKr ?mulrA ?mulrK ?divrr ?mulVr.
Qed.

Lemma unitrMr x y : x \is a unit -> (x * y \is a unit) = (y \is a unit).
Proof.
move=> Ux; apply/idP/idP=> [Uxy | Uy]; last by rewrite unitrMl.
by rewrite -(mulKr Ux y) unitrMl ?unitrV.
Qed.

Lemma unitr_prod {I : Type} (P : pred I) (E : I -> R) (r : seq I) :
  (forall i, P i -> E i \is a GRing.unit) ->
    (\prod_(i <- r | P i) E i \is a GRing.unit).
Proof.
by move=> Eunit; elim/big_rec: _ => [/[!unitr1] |i x /Eunit/unitrMr->].
Qed.

Lemma unitr_prod_in {I : eqType} (P : pred I) (E : I -> R) (r : seq I) :
  {in r, forall i, P i -> E i \is a GRing.unit} ->
    (\prod_(i <- r | P i) E i \is a GRing.unit).
Proof.
by rewrite big_seq_cond => H; apply: unitr_prod => i /andP[]; exact: H.
Qed.

Lemma invrM : {in unit &, forall x y, (x * y)^-1 = y^-1 * x^-1}.
Proof.
move=> x y Ux Uy; have Uxy: (x * y \in unit) by rewrite unitrMl.
by apply: (mulrI Uxy); rewrite divrr ?mulrA ?mulrK ?divrr.
Qed.

Lemma unitrM_comm x y :
  comm x y -> (x * y \is a unit) = (x \is a unit) && (y \is a unit).
Proof.
move=> cxy; apply/idP/andP=> [Uxy | [Ux Uy]]; last by rewrite unitrMl.
suffices Ux: x \in unit by rewrite unitrMr in Uxy.
apply/unitrP; case/unitrP: Uxy => z [zxy xyz]; exists (y * z).
rewrite mulrA xyz -{1}[y]mul1r -{1}zxy cxy -!mulrA (mulrA x) (mulrA _ z) xyz.
by rewrite mul1r -cxy.
Qed.

Lemma unitrX x n : x \is a unit -> x ^+ n \is a unit.
Proof.
by move=> Ux; elim: n => [|n IHn]; rewrite ?unitr1 // exprS unitrMl.
Qed.

Lemma unitrX_pos x n : n > 0 -> (x ^+ n \in unit) = (x \in unit).
Proof.
case: n => // n _; rewrite exprS unitrM_comm; last exact: commrX.
by case Ux: (x \is a unit); rewrite // unitrX.
Qed.

Lemma exprVn x n : x^-1 ^+ n = x ^- n.
Proof.
elim: n => [|n IHn]; first by rewrite !expr0 ?invr1.
case Ux: (x \is a unit); first by rewrite exprSr exprS IHn -invrM // unitrX.
by rewrite !invr_out ?unitrX_pos ?Ux.
Qed.

Lemma exprB m n x : n <= m -> x \is a unit -> x ^+ (m - n) = x ^+ m / x ^+ n.
Proof. by move/subnK=> {2}<- Ux; rewrite exprD mulrK ?unitrX. Qed.

Lemma invr_neq0 x : x != 0 -> x^-1 != 0.
Proof.
move=> nx0; case Ux: (x \is a unit); last by rewrite invr_out ?Ux.
by apply/eqP=> x'0; rewrite -unitrV x'0 unitr0 in Ux.
Qed.

Lemma invr_eq0 x : (x^-1 == 0) = (x == 0).
Proof. by apply: negb_inj; apply/idP/idP; move/invr_neq0; rewrite ?invrK. Qed.

Lemma invr_eq1 x : (x^-1 == 1) = (x == 1).
Proof. by rewrite (inv_eq invrK) invr1. Qed.

Lemma rev_unitrP (x y : R^c) : y * x = 1 /\ x * y = 1 -> x \is a unit.
Proof. by case=> [yx1 xy1]; apply/unitrP; exists y. Qed.

#[export]
HB.instance Definition _ :=
  NzRing_hasMulInverse.Build R^c mulrV mulVr rev_unitrP invr_out.

#[export]
HB.instance Definition _ := UnitRing.on R^o.

End UnitRingTheory.

Arguments invrK {R}.
Arguments invr_inj {R} [x1 x2].
Arguments telescope_prodr_eq {R n m} f u.

Lemma rev_prodrV (R : unitRingType)
  (I : Type) (r : seq I) (P : pred I) (E : I -> R) :
  (forall i, P i -> E i \is a GRing.unit) ->
  \prod_(i <- r | P i) (E i)^-1 = ((\prod_(i <- r | P i) (E i : R^c))^-1).
Proof.
move=> Eunit; symmetry.
apply: (big_morph_in GRing.unit _ _ (unitr1 R^c) (@invrM _) (invr1 _)) Eunit.
by move=> x y xunit; rewrite unitrMr.
Qed.

Section UnitRingClosedPredicates.

Variables (R : unitRingType) (S : {pred R}).

Definition invr_closed := {in S, forall x, x^-1 \in S}.
Definition divr_2closed := {in S &, forall x y, x / y \in S}.
Definition divr_closed := 1 \in S /\ divr_2closed.
Definition sdivr_closed := -1 \in S /\ divr_2closed.
Definition divring_closed := [/\ 1 \in S, subr_closed S & divr_2closed].

Lemma divr_closedV : divr_closed -> invr_closed.
Proof. by case=> S1 Sdiv x Sx; rewrite -[x^-1]mul1r Sdiv. Qed.

Lemma divr_closedM : divr_closed -> mulr_closed S.
Proof.
by case=> S1 Sdiv; split=> // x y Sx Sy; rewrite -[y]invrK -[y^-1]mul1r !Sdiv.
Qed.

Lemma sdivr_closed_div : sdivr_closed -> divr_closed.
Proof. by case=> SN1 Sdiv; split; rewrite // -(divrr (@unitrN1 _)) Sdiv. Qed.

Lemma sdivr_closedM : sdivr_closed -> smulr_closed S.
Proof.
by move=> Sdiv; have [_ SM] := divr_closedM (sdivr_closed_div Sdiv); case: Sdiv.
Qed.

Lemma divring_closedBM : divring_closed -> subring_closed S.
Proof. by case=> S1 SB Sdiv; split=> //; case: divr_closedM. Qed.

Lemma divring_closed_div : divring_closed -> sdivr_closed.
Proof.
case=> S1 SB Sdiv; split; rewrite ?zmod_closedN //.
exact/subring_closedB/divring_closedBM.
Qed.

End UnitRingClosedPredicates.

Section UnitRingMorphism.

Variables (R S : unitRingType) (f : {rmorphism R -> S}).

Lemma rmorph_unit x : x \in unit -> f x \in unit.
Proof.
case/unitrP=> y [yx1 xy1]; apply/unitrP.
by exists (f y); rewrite -!rmorphM // yx1 xy1 rmorph1.
Qed.

Lemma rmorphV : {in unit, {morph f: x / x^-1}}.
Proof.
move=> x Ux; rewrite /= -[(f x)^-1]mul1r.
by apply: (canRL (mulrK (rmorph_unit Ux))); rewrite -rmorphM mulVr ?rmorph1.
Qed.

Lemma rmorph_div x y : y \in unit -> f (x / y) = f x / f y.
Proof. by move=> Uy; rewrite rmorphM /= rmorphV. Qed.

End UnitRingMorphism.

#[short(type="comUnitRingType")]
HB.structure Definition ComUnitRing := {R of ComNzRing R & UnitRing R}.

Module ComUnitRingExports.
Bind Scope ring_scope with ComUnitRing.sort.
End ComUnitRingExports.
HB.export ComUnitRingExports.

(* TODO_HB: fix the name (was ComUnitRingMixin) *)
HB.factory Record ComNzRing_hasMulInverse R of ComNzRing R := {
  unit : {pred R};
  inv : R -> R;
  mulVx : {in unit, left_inverse 1 inv *%R};
  unitPl : forall x y, y * x = 1 -> unit x;
  invr_out : {in [predC unit], inv =1 id}
}.

Module ComRing_hasMulInverse.
#[deprecated(since="mathcomp 2.4.0", use=ComNzRing_hasMulInverse.Build)]
Notation Build R := (ComNzRing_hasMulInverse.Build R) (only parsing).
End ComRing_hasMulInverse.

#[deprecated(since="mathcomp 2.4.0", use=ComNzRing_hasMulInverse)]
Notation ComRing_hasMulInverse R := (ComNzRing_hasMulInverse R) (only parsing).

HB.builders Context R of ComNzRing_hasMulInverse R.

Fact mulC_mulrV : {in unit, right_inverse 1 inv *%R}.
Proof. by move=> x Ux /=; rewrite mulrC mulVx. Qed.

Fact mulC_unitP x y : y * x = 1 /\ x * y = 1 -> unit x.
Proof. by case=> yx _; apply: unitPl yx. Qed.

HB.instance Definition _ :=
  NzRing_hasMulInverse.Build R mulVx mulC_mulrV mulC_unitP invr_out.

HB.end.

#[short(type="unitAlgType")]
HB.structure Definition UnitAlgebra R := {V of NzAlgebra R V & UnitRing V}.

Module UnitAlgebraExports.
Bind Scope ring_scope with UnitAlgebra.sort.
End UnitAlgebraExports.
HB.export UnitAlgebraExports.

#[short(type="comUnitAlgType")]
HB.structure Definition ComUnitAlgebra R :=
  {V of ComNzAlgebra R V & UnitRing V}.

Module ComUnitAlgebraExports.
Bind Scope ring_scope with UnitAlgebra.sort.
End ComUnitAlgebraExports.
HB.export ComUnitAlgebraExports.

Section ComUnitRingTheory.

Variable R : comUnitRingType.
Implicit Types x y : R.

Lemma unitrM x y : (x * y \in unit) = (x \in unit) && (y \in unit).
Proof. exact/unitrM_comm/mulrC. Qed.

Lemma unitrPr x : reflect (exists y, x * y = 1) (x \in unit).
Proof.
by apply: (iffP (unitrP x)) => [[y []] | [y]]; exists y; rewrite // mulrC.
Qed.

Lemma mulr1_eq x y : x * y = 1 -> x^-1 = y.
Proof.
by move=> xy_eq1; rewrite -[LHS]mulr1 -xy_eq1; apply/mulKr/unitrPr; exists y.
Qed.

Lemma divr1_eq x y : x / y = 1 -> x = y. Proof. by move/mulr1_eq/invr_inj. Qed.

Lemma divKr x : x \is a unit -> {in unit, involutive (fun y => x / y)}.
Proof. by move=> Ux y Uy; rewrite /= invrM ?unitrV // invrK mulrC divrK. Qed.

Lemma expr_div_n x y n : (x / y) ^+ n = x ^+ n / y ^+ n.
Proof. by rewrite exprMn exprVn. Qed.

Lemma unitr_prodP (I : eqType) (r : seq I) (P : pred I) (E : I -> R) :
  reflect {in r, forall i, P i -> E i \is a GRing.unit}
    (\prod_(i <- r | P i) E i \is a GRing.unit).
Proof.
rewrite (big_morph [in unit] unitrM (@unitr1 _) ) big_all_cond.
exact: 'all_implyP.
Qed.

Lemma prodrV (I : eqType) (r : seq I) (P : pred I) (E : I -> R) :
  (forall i, P i -> E i \is a GRing.unit) ->
  \prod_(i <- r | P i) (E i)^-1 = (\prod_(i <- r | P i) E i)^-1.
Proof.
by move=> /rev_prodrV->; rewrite rev_prodr (perm_big r)// perm_rev.
Qed.

(* TODO: HB.saturate *)
#[export] HB.instance Definition _ := ComUnitRing.on R^c.
#[export] HB.instance Definition _ := ComUnitRing.on R^o.
(* /TODO *)

End ComUnitRingTheory.

Section UnitAlgebraTheory.

Variable (R : comUnitRingType) (A : unitAlgType R).
Implicit Types (k : R) (x y : A).

Lemma scaler_injl : {in unit, @right_injective R A A *:%R}.
Proof.
move=> k Uk x1 x2 Hx1x2.
by rewrite -[x1]scale1r -(mulVr Uk) -scalerA Hx1x2 scalerA mulVr // scale1r.
Qed.

Lemma scaler_unit k x : k \in unit -> (k *: x \in unit) = (x \in unit).
Proof.
move=> Uk; apply/idP/idP=> [Ukx | Ux]; apply/unitrP; last first.
  exists (k^-1 *: x^-1).
  by rewrite -!scalerAl -!scalerAr !scalerA !mulVr // !mulrV // scale1r.
exists (k *: (k *: x)^-1); split.
  apply: (mulrI Ukx).
  by rewrite mulr1 mulrA -scalerAr mulrV // -scalerAl mul1r.
apply: (mulIr Ukx).
by rewrite mul1r -mulrA -scalerAl mulVr // -scalerAr mulr1.
Qed.

Lemma invrZ k x : k \in unit -> x \in unit -> (k *: x)^-1 = k^-1 *: x^-1.
Proof.
move=> Uk Ux; have Ukx: (k *: x \in unit) by rewrite scaler_unit.
apply: (mulIr Ukx).
by rewrite mulVr // -scalerAl -scalerAr scalerA !mulVr // scale1r.
Qed.

Section ClosedPredicates.

Variables S : {pred A}.

Definition divalg_closed := [/\ 1 \in S, linear_closed S & divr_2closed S].

Lemma divalg_closedBdiv : divalg_closed -> divring_closed S.
Proof. by case=> S1 /linear_closedB. Qed.

Lemma divalg_closedZ : divalg_closed -> subalg_closed S.
Proof. by case=> S1 Slin Sdiv; split=> //; have [] := @divr_closedM A S. Qed.

End ClosedPredicates.

End UnitAlgebraTheory.

Module ClosedExports.

Notation invr_closed := invr_closed.
Notation divr_2closed := divr_2closed.
Notation divr_closed := divr_closed.
Notation sdivr_closed := sdivr_closed.
Notation divring_closed := divring_closed.
Notation divalg_closed := divalg_closed.

Coercion divr_closedV : divr_closed >-> invr_closed.
Coercion divr_closedM : divr_closed >-> mulr_closed.
Coercion sdivr_closed_div : sdivr_closed >-> divr_closed.
Coercion sdivr_closedM : sdivr_closed >-> smulr_closed.
Coercion divring_closedBM : divring_closed >-> subring_closed.
Coercion divring_closed_div : divring_closed >-> sdivr_closed.
Coercion divalg_closedBdiv : divalg_closed >-> divring_closed.
Coercion divalg_closedZ : divalg_closed >-> subalg_closed.

End ClosedExports.

(* Reification of the theory of rings with units, in named style  *)
Section TermDef.

Variable R : Type.

Inductive term : Type :=
| Var of nat
| Const of R
| NatConst of nat
| Add of term & term
| Opp of term
| NatMul of term & nat
| Mul of term & term
| Inv of term
| Exp of term & nat.

Inductive formula : Type :=
| Bool of bool
| Equal of term & term
| Unit of term
| And of formula & formula
| Or of formula & formula
| Implies of formula & formula
| Not of formula
| Exists of nat & formula
| Forall of nat & formula.

End TermDef.

Bind Scope term_scope with term.
Bind Scope term_scope with formula.
Arguments Add {R} t1%_T t2%_T.
Arguments Opp {R} t1%_T.
Arguments NatMul {R} t1%_T n%_N.
Arguments Mul {R} t1%_T t2%_T.
Arguments Inv {R} t1%_T.
Arguments Exp {R} t1%_T n%_N.
Arguments Equal {R} t1%_T t2%_T.
Arguments Unit {R} t1%_T.
Arguments And {R} f1%_T f2%_T.
Arguments Or {R} f1%_T f2%_T.
Arguments Implies {R} f1%_T f2%_T.
Arguments Not {R} f1%_T.
Arguments Exists {R} i%_N f1%_T.
Arguments Forall {R} i%_N f1%_T.

Arguments Bool {R} b.
Arguments Const {R} x.

Notation True := (Bool true).
Notation False := (Bool false).

Local Notation "''X_' i" := (Var _ i) : term_scope.
Local Notation "n %:R" := (NatConst _ n) : term_scope.
Local Notation "x %:T" := (Const x) : term_scope.
Local Notation "0" := 0%:R%T : term_scope.
Local Notation "1" := 1%:R%T : term_scope.
Local Infix "+" := Add : term_scope.
Local Notation "- t" := (Opp t) : term_scope.
Local Notation "t - u" := (Add t (- u)) : term_scope.
Local Infix "*" := Mul : term_scope.
Local Infix "*+" := NatMul : term_scope.
Local Notation "t ^-1" := (Inv t) : term_scope.
Local Notation "t / u" := (Mul t u^-1) : term_scope.
Local Infix "^+" := Exp : term_scope.
Local Infix "==" := Equal : term_scope.
Local Infix "/\" := And : term_scope.
Local Infix "\/" := Or : term_scope.
Local Infix "==>" := Implies : term_scope.
Local Notation "~ f" := (Not f) : term_scope.
Local Notation "x != y" := (Not (x == y)) : term_scope.
Local Notation "''exists' ''X_' i , f" := (Exists i f) : term_scope.
Local Notation "''forall' ''X_' i , f" := (Forall i f) : term_scope.

Section Substitution.

Variable R : Type.

Fixpoint tsubst (t : term R) (s : nat * term R) :=
  match t with
  | 'X_i => if i == s.1 then s.2 else t
  | _%:T | _%:R => t
  | t1 + t2 => tsubst t1 s + tsubst t2 s
  | - t1 => - tsubst t1 s
  | t1 *+ n => tsubst t1 s *+ n
  | t1 * t2 => tsubst t1 s * tsubst t2 s
  | t1^-1 => (tsubst t1 s)^-1
  | t1 ^+ n => tsubst t1 s ^+ n
  end%T.

Fixpoint fsubst (f : formula R) (s : nat * term R) :=
  match f with
  | Bool _ => f
  | t1 == t2 => tsubst t1 s == tsubst t2 s
  | Unit t1 => Unit (tsubst t1 s)
  | f1 /\ f2 => fsubst f1 s /\ fsubst f2 s
  | f1 \/ f2 => fsubst f1 s \/ fsubst f2 s
  | f1 ==> f2 => fsubst f1 s ==> fsubst f2 s
  | ~ f1 => ~ fsubst f1 s
  | ('exists 'X_i, f1) => 'exists 'X_i, if i == s.1 then f1 else fsubst f1 s
  | ('forall 'X_i, f1) => 'forall 'X_i, if i == s.1 then f1 else fsubst f1 s
  end%T.

End Substitution.

Section EvalTerm.

Variable R : unitRingType.

(* Evaluation of a reified term into R a ring with units *)
Fixpoint eval (e : seq R) (t : term R) {struct t} : R :=
  match t with
  | ('X_i)%T => e`_i
  | (x%:T)%T => x
  | (n%:R)%T => n%:R
  | (t1 + t2)%T => eval e t1 + eval e t2
  | (- t1)%T => - eval e t1
  | (t1 *+ n)%T => eval e t1 *+ n
  | (t1 * t2)%T => eval e t1 * eval e t2
  | t1^-1%T => (eval e t1)^-1
  | (t1 ^+ n)%T => eval e t1 ^+ n
  end.

Definition same_env (e e' : seq R) := nth 0 e =1 nth 0 e'.

Lemma eq_eval e e' t : same_env e e' -> eval e t = eval e' t.
Proof. by move=> eq_e; elim: t => //= t1 -> // t2 ->. Qed.

Lemma eval_tsubst e t s :
  eval e (tsubst t s) = eval (set_nth 0 e s.1 (eval e s.2)) t.
Proof.
case: s => i u; elim: t => //=; do 2?[move=> ? -> //] => j.
by rewrite nth_set_nth /=; case: (_ == _).
Qed.

(* Evaluation of a reified formula *)
Fixpoint holds (e : seq R) (f : formula R) {struct f} : Prop :=
  match f with
  | Bool b => b
  | (t1 == t2)%T => eval e t1 = eval e t2
  | Unit t1 => eval e t1 \in unit
  | (f1 /\ f2)%T => holds e f1 /\ holds e f2
  | (f1 \/ f2)%T => holds e f1 \/ holds e f2
  | (f1 ==> f2)%T => holds e f1 -> holds e f2
  | (~ f1)%T => ~ holds e f1
  | ('exists 'X_i, f1)%T => exists x, holds (set_nth 0 e i x) f1
  | ('forall 'X_i, f1)%T => forall x, holds (set_nth 0 e i x) f1
  end.

Lemma same_env_sym e e' : same_env e e' -> same_env e' e.
Proof. exact: fsym. Qed.

(* Extensionality of formula evaluation *)
Lemma eq_holds e e' f : same_env e e' -> holds e f -> holds e' f.
Proof.
pose sv := set_nth (0 : R).
have eq_i i v e1 e2: same_env e1 e2 -> same_env (sv e1 i v) (sv e2 i v).
  by move=> eq_e j; rewrite !nth_set_nth /= eq_e.
elim: f e e' => //=.
- by move=> t1 t2 e e' eq_e; rewrite !(eq_eval _ eq_e).
- by move=> t e e' eq_e; rewrite (eq_eval _ eq_e).
- by move=> f1 IH1 f2 IH2 e e' eq_e; move/IH2: (eq_e); move/IH1: eq_e; tauto.
- by move=> f1 IH1 f2 IH2 e e' eq_e; move/IH2: (eq_e); move/IH1: eq_e; tauto.
- by move=> f1 IH1 f2 IH2 e e' eq_e f12; move/IH1: (same_env_sym eq_e); eauto.
- by move=> f1 IH1 e e'; move/same_env_sym; move/IH1; tauto.
- by move=> i f1 IH1 e e'; move/(eq_i i)=> eq_e [x f_ex]; exists x; eauto.
by move=> i f1 IH1 e e'; move/(eq_i i); eauto.
Qed.

(* Evaluation and substitution by a constant *)
Lemma holds_fsubst e f i v :
  holds e (fsubst f (i, v%:T)%T) <-> holds (set_nth 0 e i v) f.
Proof.
elim: f e => //=; do [
  by move=> *; rewrite !eval_tsubst
| move=> f1 IHf1 f2 IHf2 e; move: (IHf1 e) (IHf2 e); tauto
| move=> f IHf e; move: (IHf e); tauto
| move=> j f IHf e].
- case eq_ji: (j == i); first rewrite (eqP eq_ji).
    by split=> [] [x f_x]; exists x; rewrite set_set_nth eqxx in f_x *.
  split=> [] [x f_x]; exists x; move: f_x; rewrite set_set_nth eq_sym eq_ji;
     have:= IHf (set_nth 0 e j x); tauto.
case eq_ji: (j == i); first rewrite (eqP eq_ji).
  by split=> [] f_ x; move: (f_ x); rewrite set_set_nth eqxx.
split=> [] f_ x; move: (IHf (set_nth 0 e j x)) (f_ x);
  by rewrite set_set_nth 1?[i == j]eq_sym eq_ji; tauto.
Qed.

(* Boolean test selecting terms in the language of rings *)
Fixpoint rterm (t : term R) :=
  match t with
  | _^-1 => false
  | t1 + t2 | t1 * t2 => rterm t1 && rterm t2
  | - t1 | t1 *+ _ | t1 ^+ _ => rterm t1
  | _ => true
  end%T.

(* Boolean test selecting formulas in the theory of rings *)
Fixpoint rformula (f : formula R) :=
  match f with
  | Bool _ => true
  | t1 == t2 => rterm t1 && rterm t2
  | Unit t1 => false
  | f1 /\ f2 | f1 \/ f2 | f1 ==> f2 => rformula f1 && rformula f2
  | ~ f1 | ('exists 'X__, f1) | ('forall 'X__, f1) => rformula f1
  end%T.

(* Upper bound of the names used in a term *)
Fixpoint ub_var (t : term R) :=
  match t with
  | 'X_i => i.+1
  | t1 + t2 | t1 * t2 => maxn (ub_var t1) (ub_var t2)
  | - t1 | t1 *+ _ | t1 ^+ _ | t1^-1 => ub_var t1
  | _ => 0%N
  end%T.

(* Replaces inverses in the term t by fresh variables, accumulating the *)
(* substitution. *)
Fixpoint to_rterm (t : term R) (r : seq (term R)) (n : nat) {struct t} :=
  match t with
  | t1^-1 =>
    let: (t1', r1) := to_rterm t1 r n in
      ('X_(n + size r1), rcons r1 t1')
  | t1 + t2 =>
    let: (t1', r1) := to_rterm t1 r n in
    let: (t2', r2) := to_rterm t2 r1 n in
      (t1' + t2', r2)
  | - t1 =>
   let: (t1', r1) := to_rterm t1 r n in
     (- t1', r1)
  | t1 *+ m =>
   let: (t1', r1) := to_rterm t1 r n in
     (t1' *+ m, r1)
  | t1 * t2 =>
    let: (t1', r1) := to_rterm t1 r n in
    let: (t2', r2) := to_rterm t2 r1 n in
      (Mul t1' t2', r2)
  | t1 ^+ m =>
       let: (t1', r1) := to_rterm t1 r n in
     (t1' ^+ m, r1)
  | _ => (t, r)
  end%T.

Lemma to_rterm_id t r n : rterm t -> to_rterm t r n = (t, r).
Proof.
elim: t r n => //.
- by move=> t1 IHt1 t2 IHt2 r n /= /andP[rt1 rt2]; rewrite {}IHt1 // IHt2.
- by move=> t IHt r n /= rt; rewrite {}IHt.
- by move=> t IHt r n m /= rt; rewrite {}IHt.
- by move=> t1 IHt1 t2 IHt2 r n /= /andP[rt1 rt2]; rewrite {}IHt1 // IHt2.
- by move=> t IHt r n m /= rt; rewrite {}IHt.
Qed.

(* A ring formula stating that t1 is equal to 0 in the ring theory. *)
(* Also applies to non commutative rings.                           *)
Definition eq0_rform t1 :=
  let m := ub_var t1 in
  let: (t1', r1) := to_rterm t1 [::] m in
  let fix loop r i := match r with
  | [::] => t1' == 0
  | t :: r' =>
    let f := 'X_i * t == 1 /\ t * 'X_i == 1 in
     'forall 'X_i, (f \/ 'X_i == t /\ ~ ('exists 'X_i,  f)) ==> loop r' i.+1
  end%T
  in loop r1 m.

(* Transformation of a formula in the theory of rings with units into an *)
(* equivalent formula in the sub-theory of rings.                        *)
Fixpoint to_rform f :=
  match f with
  | Bool b => f
  | t1 == t2 => eq0_rform (t1 - t2)
  | Unit t1 => eq0_rform (t1 * t1^-1 - 1)
  | f1 /\ f2 => to_rform f1 /\ to_rform f2
  | f1 \/ f2 =>  to_rform f1 \/ to_rform f2
  | f1 ==> f2 => to_rform f1 ==> to_rform f2
  | ~ f1 => ~ to_rform f1
  | ('exists 'X_i, f1) => 'exists 'X_i, to_rform f1
  | ('forall 'X_i, f1) => 'forall 'X_i, to_rform f1
  end%T.

(* The transformation gives a ring formula. *)
Lemma to_rform_rformula f : rformula (to_rform f).
Proof.
suffices eq0_ring t1: rformula (eq0_rform t1) by elim: f => //= => f1 ->.
rewrite /eq0_rform; move: (ub_var t1) => m; set tr := _ m.
suffices: all rterm (tr.1 :: tr.2).
  case: tr => {}t1 r /= /andP[t1_r].
  by elim: r m => [|t r IHr] m; rewrite /= ?andbT // => /andP[->]; apply: IHr.
have: all rterm [::] by [].
rewrite {}/tr; elim: t1 [::] => //=.
- move=> t1 IHt1 t2 IHt2 r.
  move/IHt1; case: to_rterm => {r IHt1}t1 r /= /andP[t1_r].
  move/IHt2; case: to_rterm => {r IHt2}t2 r /= /andP[t2_r].
  by rewrite t1_r t2_r.
- by move=> t1 IHt1 r /IHt1; case: to_rterm.
- by move=> t1 IHt1 n r /IHt1; case: to_rterm.
- move=> t1 IHt1 t2 IHt2 r.
  move/IHt1; case: to_rterm => {r IHt1}t1 r /= /andP[t1_r].
  move/IHt2; case: to_rterm => {r IHt2}t2 r /= /andP[t2_r].
  by rewrite t1_r t2_r.
- move=> t1 IHt1 r.
  by move/IHt1; case: to_rterm => {r IHt1}t1 r /=; rewrite all_rcons.
- by move=> t1 IHt1 n r /IHt1; case: to_rterm.
Qed.

(* Correctness of the transformation. *)
Lemma to_rformP e f : holds e (to_rform f) <-> holds e f.
Proof.
suffices{e f} equal0_equiv e t1 t2:
  holds e (eq0_rform (t1 - t2)) <-> (eval e t1 == eval e t2).
- elim: f e => /=; try tauto.
  + move=> t1 t2 e.
    by split; [move/equal0_equiv/eqP | move/eqP/equal0_equiv].
  + by move=> t1 e; rewrite unitrE; apply: equal0_equiv.
  + by move=> f1 IHf1 f2 IHf2 e; move: (IHf1 e) (IHf2 e); tauto.
  + by move=> f1 IHf1 f2 IHf2 e; move: (IHf1 e) (IHf2 e); tauto.
  + by move=> f1 IHf1 f2 IHf2 e; move: (IHf1 e) (IHf2 e); tauto.
  + by move=> f1 IHf1 e; move: (IHf1 e); tauto.
  + by move=> n f1 IHf1 e; split=> [] [x] /IHf1; exists x.
  + by move=> n f1 IHf1 e; split=> Hx x; apply/IHf1.
rewrite -(add0r (eval e t2)) -(can2_eq (subrK _) (addrK _)).
rewrite -/(eval e (t1 - t2)); move: (t1 - t2)%T => {t1 t2} t.
have sub_var_tsubst s t0: s.1 >= ub_var t0 -> tsubst t0 s = t0.
  elim: t0 {t} => //=.
  - by move=> n; case: ltngtP.
  - by move=> t1 IHt1 t2 IHt2; rewrite geq_max => /andP[/IHt1-> /IHt2->].
  - by move=> t1 IHt1 /IHt1->.
  - by move=> t1 IHt1 n /IHt1->.
  - by move=> t1 IHt1 t2 IHt2; rewrite geq_max => /andP[/IHt1-> /IHt2->].
  - by move=> t1 IHt1 /IHt1->.
  - by move=> t1 IHt1 n /IHt1->.
pose fix rsub t' m r : term R :=
  if r is u :: r' then tsubst (rsub t' m.+1 r') (m, u^-1)%T else t'.
pose fix ub_sub m r : Prop :=
  if r is u :: r' then ub_var u <= m /\ ub_sub m.+1 r' else true.
suffices{t} rsub_to_r t r0 m: m >= ub_var t -> ub_sub m r0 ->
  let: (t', r) := to_rterm t r0 m in
  [/\ take (size r0) r = r0,
      ub_var t' <= m + size r, ub_sub m r & rsub t' m r = t].
- have:= rsub_to_r t [::] _ (leqnn _); rewrite /eq0_rform.
  case: (to_rterm _ _ _) => [t1' r1] [//|_ _ ub_r1 def_t].
  rewrite -{2}def_t {def_t}.
  elim: r1 (ub_var t) e ub_r1 => [|u r1 IHr1] m e /= => [_|[ub_u ub_r1]].
    by split=> /eqP.
  rewrite eval_tsubst /=; set y := eval e u; split=> t_eq0.
    apply/IHr1=> //; apply: t_eq0.
    rewrite nth_set_nth /= eqxx -(eval_tsubst e u (m, Const _)).
    rewrite sub_var_tsubst //= -/y.
    case Uy: (y \in unit); [left | right]; first by rewrite mulVr ?divrr.
    split=> [|[z]]; first by rewrite invr_out ?Uy.
    rewrite nth_set_nth /= eqxx.
    rewrite -!(eval_tsubst _ _ (m, Const _)) !sub_var_tsubst // -/y => yz1.
    by case/unitrP: Uy; exists z.
  move=> x def_x; apply/IHr1=> //; suff ->: x = y^-1 by []; move: def_x.
  rewrite nth_set_nth /= eqxx -(eval_tsubst e u (m, Const _)).
  rewrite sub_var_tsubst //= -/y; case=> [[xy1 yx1] | [xy nUy]].
    by rewrite -[y^-1]mul1r -[1]xy1 mulrK //; apply/unitrP; exists x.
  rewrite invr_out //; apply/unitrP=> [[z yz1]]; case: nUy; exists z.
  rewrite nth_set_nth /= eqxx -!(eval_tsubst _ _ (m, _%:T)%T).
  by rewrite !sub_var_tsubst.
have rsub_id r t0 n: ub_var t0 <= n -> rsub t0 n r = t0.
  by elim: r n => //= t1 r IHr n let0n; rewrite IHr ?sub_var_tsubst ?leqW.
have rsub_acc r s t1 m1:
  ub_var t1 <= m1 + size r -> rsub t1 m1 (r ++ s) = rsub t1 m1 r.
  elim: r t1 m1 => [|t1 r IHr] t2 m1 /=; first by rewrite addn0; apply: rsub_id.
  by move=> letmr; rewrite IHr ?addSnnS.
elim: t r0 m => /=; try do [
  by move=> n r m hlt hub; rewrite take_size (ltn_addr _ hlt) rsub_id
| by move=> n r m hlt hub; rewrite leq0n take_size rsub_id
| move=> t1 IHt1 t2 IHt2 r m; rewrite geq_max; case/andP=> hub1 hub2 hmr;
  case: to_rterm {hub1 hmr}(IHt1 r m hub1 hmr) => t1' r1;
  case=> htake1 hub1' hsub1 <-;
  case: to_rterm {IHt2 hub2 hsub1}(IHt2 r1 m hub2 hsub1) => t2' r2 /=;
  rewrite geq_max; case=> htake2 -> hsub2 /= <-;
  rewrite -{1 2}(cat_take_drop (size r1) r2) htake2; set r3 := drop _ _;
  rewrite size_cat addnA (leq_trans _ (leq_addr _ _)) //;
  split=> {hsub2}//;
   first by [rewrite takel_cat // -htake1 size_take geq_min leqnn orbT];
  rewrite -(rsub_acc r1 r3 t1') {hub1'}// -{htake1}htake2 {r3}cat_take_drop;
  by elim: r2 m => //= u r2 IHr2 m; rewrite IHr2
| do [ move=> t1 IHt1 r m; do 2!move=> /IHt1{}IHt1
     | move=> t1 IHt1 n r m; do 2!move=> /IHt1{}IHt1];
  case: to_rterm IHt1 => t1' r1 [-> -> hsub1 <-]; split=> {hsub1}//;
  by elim: r1 m => //= u r1 IHr1 m; rewrite IHr1].
move=> t1 IH r m letm /IH {IH} /(_ letm) {letm}.
case: to_rterm => t1' r1 /= [def_r ub_t1' ub_r1 <-].
rewrite size_rcons addnS leqnn -{1}cats1 takel_cat ?def_r; last first.
  by rewrite -def_r size_take geq_min leqnn orbT.
elim: r1 m ub_r1 ub_t1' {def_r} => /= [|u r1 IHr1] m => [_|[->]].
  by rewrite addn0 eqxx.
by rewrite -addSnnS => /IHr1 IH /IH[_ _ ub_r1 ->].
Qed.

(* Boolean test selecting formulas which describe a constructible set, *)
(* i.e. formulas without quantifiers.                                  *)

(* The quantifier elimination check. *)
Fixpoint qf_form (f : formula R) :=
  match f with
  | Bool _ | _ == _ | Unit _ => true
  | f1 /\ f2 | f1 \/ f2 | f1 ==> f2 => qf_form f1 && qf_form f2
  | ~ f1 => qf_form f1
  | _ => false
  end%T.

(* Boolean holds predicate for quantifier free formulas *)
Definition qf_eval e := fix loop (f : formula R) : bool :=
  match f with
  | Bool b => b
  | t1 == t2 => (eval e t1 == eval e t2)%bool
  | Unit t1 => eval e t1 \in unit
  | f1 /\ f2 => loop f1 && loop f2
  | f1 \/ f2 => loop f1 || loop f2
  | f1 ==> f2 => (loop f1 ==> loop f2)%bool
  | ~ f1 => ~~ loop f1
  |_ => false
  end%T.

(* qf_eval is equivalent to holds *)
Lemma qf_evalP e f : qf_form f -> reflect (holds e f) (qf_eval e f).
Proof.
elim: f => //=; try by move=> *; apply: idP.
- by move=> t1 t2 _; apply: eqP.
- move=> f1 IHf1 f2 IHf2 /= /andP[/IHf1[] f1T]; last by right; case.
  by case/IHf2; [left | right; case].
- move=> f1 IHf1 f2 IHf2 /= /andP[/IHf1[] f1F]; first by do 2 left.
  by case/IHf2; [left; right | right; case].
- move=> f1 IHf1 f2 IHf2 /= /andP[/IHf1[] f1T]; last by left.
  by case/IHf2; [left | right; move/(_ f1T)].
by move=> f1 IHf1 /IHf1[]; [right | left].
Qed.

Implicit Type bc : seq (term R) * seq (term R).

(* Quantifier-free formula are normalized into DNF. A DNF is *)
(* represented by the type seq (seq (term R) * seq (term R)), where we *)
(* separate positive and negative literals *)

(* DNF preserving conjunction *)
Definition and_dnf bcs1 bcs2 :=
  \big[cat/nil]_(bc1 <- bcs1)
     map (fun bc2 => (bc1.1 ++ bc2.1, bc1.2 ++ bc2.2)) bcs2.

(* Computes a DNF from a qf ring formula *)
Fixpoint qf_to_dnf (f : formula R) (neg : bool) {struct f} :=
  match f with
  | Bool b => if b (+) neg then [:: ([::], [::])] else [::]
  | t1 == t2 => [:: if neg then ([::], [:: t1 - t2]) else ([:: t1 - t2], [::])]
  | f1 /\ f2 => (if neg then cat else and_dnf) [rec f1, neg] [rec f2, neg]
  | f1 \/ f2 => (if neg then and_dnf else cat) [rec f1, neg] [rec f2, neg]
  | f1 ==> f2 => (if neg then and_dnf else cat) [rec f1, ~~ neg] [rec f2, neg]
  | ~ f1 => [rec f1, ~~ neg]
  | _ =>  if neg then [:: ([::], [::])] else [::]
  end%T where "[ 'rec' f , neg ]" := (qf_to_dnf f neg).

(* Conversely, transforms a DNF into a formula *)
Definition dnf_to_form :=
  let pos_lit t := And (t == 0) in let neg_lit t := And (t != 0) in
  let cls bc := Or (foldr pos_lit True bc.1 /\ foldr neg_lit True bc.2) in
  foldr cls False.

(* Catenation of dnf is the Or of formulas *)
Lemma cat_dnfP e bcs1 bcs2 :
  qf_eval e (dnf_to_form (bcs1 ++ bcs2))
    = qf_eval e (dnf_to_form bcs1 \/ dnf_to_form bcs2).
Proof.
by elim: bcs1 => //= bc1 bcs1 IH1; rewrite -orbA; congr orb; rewrite IH1.
Qed.

(* and_dnf is the And of formulas *)
Lemma and_dnfP e bcs1 bcs2 :
  qf_eval e (dnf_to_form (and_dnf bcs1 bcs2))
   = qf_eval e (dnf_to_form bcs1 /\ dnf_to_form bcs2).
Proof.
elim: bcs1 => [|bc1 bcs1 IH1] /=; first by rewrite /and_dnf big_nil.
rewrite /and_dnf big_cons -/(and_dnf bcs1 bcs2) cat_dnfP  /=.
rewrite {}IH1 /= andb_orl; congr orb.
elim: bcs2 bc1 {bcs1} => [|bc2 bcs2 IH] bc1 /=; first by rewrite andbF.
rewrite {}IH /= andb_orr; congr orb => {bcs2}.
suffices aux (l1 l2 : seq (term R)) g : let redg := foldr (And \o g) True in
  qf_eval e (redg (l1 ++ l2)) = qf_eval e (redg l1 /\ redg l2)%T.
+ by rewrite 2!aux /= 2!andbA -andbA -andbCA andbA andbCA andbA.
by elim: l1 => [| t1 l1 IHl1] //=; rewrite -andbA IHl1.
Qed.

Lemma qf_to_dnfP e :
  let qev f b := qf_eval e (dnf_to_form (qf_to_dnf f b)) in
  forall f, qf_form f && rformula f -> qev f false = qf_eval e f.
Proof.
move=> qev; have qevT f: qev f true = ~~ qev f false.
  rewrite {}/qev; elim: f => //=; do [by case | move=> f1 IH1 f2 IH2 | ].
  - by move=> t1 t2; rewrite !andbT !orbF.
  - by rewrite and_dnfP cat_dnfP negb_and -IH1 -IH2.
  - by rewrite and_dnfP cat_dnfP negb_or -IH1 -IH2.
  - by rewrite and_dnfP cat_dnfP /= negb_or IH1 -IH2 negbK.
  by move=> t1 ->; rewrite negbK.
rewrite /qev; elim=> //=; first by case.
- by move=> t1 t2 _; rewrite subr_eq0 !andbT orbF.
- move=> f1 IH1 f2 IH2; rewrite andbCA -andbA andbCA andbA; case/andP.
  by rewrite and_dnfP /= => /IH1-> /IH2->.
- move=> f1 IH1 f2 IH2; rewrite andbCA -andbA andbCA andbA; case/andP.
  by rewrite cat_dnfP /= => /IH1-> => /IH2->.
- move=> f1 IH1 f2 IH2; rewrite andbCA -andbA andbCA andbA; case/andP.
  by rewrite cat_dnfP /= [qf_eval _ _]qevT -implybE => /IH1 <- /IH2->.
by move=> f1 IH1 /IH1 <-; rewrite -qevT.
Qed.

Lemma dnf_to_form_qf bcs : qf_form (dnf_to_form bcs).
Proof.
by elim: bcs => //= [[clT clF] _ ->] /=; elim: clT => //=; elim: clF.
Qed.

Definition dnf_rterm cl := all rterm cl.1 && all rterm cl.2.

Lemma qf_to_dnf_rterm f b : rformula f -> all dnf_rterm (qf_to_dnf f b).
Proof.
set ok := all dnf_rterm.
have cat_ok bcs1 bcs2: ok bcs1 -> ok bcs2 -> ok (bcs1 ++ bcs2).
  by move=> ok1 ok2; rewrite [ok _]all_cat; apply/andP.
have and_ok bcs1 bcs2: ok bcs1 -> ok bcs2 -> ok (and_dnf bcs1 bcs2).
  rewrite /and_dnf unlock; elim: bcs1 => //= cl1 bcs1 IH1; rewrite -andbA.
  case/and3P=> ok11 ok12 ok1 ok2; rewrite cat_ok ?{}IH1 {bcs1 ok1}//.
  elim: bcs2 ok2 => //= cl2 bcs2 IH2 /andP[ok2 /IH2->].
  by rewrite /dnf_rterm !all_cat ok11 ok12 /= !andbT.
elim: f b => //=; [ by do 2!case | | | | | by auto | | ];
  try by repeat case/andP || intro; case: ifP; auto.
by rewrite /dnf_rterm => ?? [] /= ->.
Qed.

Lemma dnf_to_rform bcs : rformula (dnf_to_form bcs) = all dnf_rterm bcs.
Proof.
elim: bcs => //= [[cl1 cl2] bcs ->]; rewrite {2}/dnf_rterm /=; congr (_ && _).
by (congr andb; [elim: cl1 | elim: cl2]) => //= t cl ->; rewrite andbT.
Qed.

Section If.

Variables (pred_f then_f else_f : formula R).

Definition If := (pred_f /\ then_f \/ ~ pred_f /\ else_f)%T.

Lemma If_form_qf :
  qf_form pred_f -> qf_form then_f -> qf_form else_f -> qf_form If.
Proof. by move=> /= -> -> ->. Qed.

Lemma If_form_rf :
  rformula pred_f -> rformula then_f -> rformula else_f -> rformula If.
Proof. by move=> /= -> -> ->. Qed.

Lemma eval_If e :
  let ev := qf_eval e in ev If = (if ev pred_f then ev then_f else ev else_f).
Proof. by rewrite /=; case: ifP => _; rewrite ?orbF. Qed.

End If.

Section Pick.

Variables (I : finType) (pred_f then_f : I -> formula R) (else_f : formula R).

Definition Pick :=
  \big[Or/False]_(p : {ffun pred I})
    ((\big[And/True]_i (if p i then pred_f i else ~ pred_f i))
    /\ (if pick p is Some i then then_f i else else_f))%T.

Lemma Pick_form_qf :
   (forall i, qf_form (pred_f i)) ->
   (forall i, qf_form (then_f i)) ->
    qf_form else_f ->
  qf_form Pick.
Proof.
move=> qfp qft qfe; have mA := (big_morph qf_form) true andb.
rewrite mA // big1 //= => p _.
rewrite mA // big1 => [|i _]; first by case: pick.
by rewrite fun_if if_same /= qfp.
Qed.

Lemma eval_Pick e (qev := qf_eval e) :
  let P i := qev (pred_f i) in
  qev Pick = (if pick P is Some i then qev (then_f i) else qev else_f).
Proof.
move=> P; rewrite ((big_morph qev) false orb) //= big_orE /=.
apply/existsP/idP=> [[p] | true_at_P].
  rewrite ((big_morph qev) true andb) //= big_andE /=.
  case/andP=> /forallP-eq_p_P.
  rewrite (@eq_pick _ _ P) => [|i]; first by case: pick.
  by move/(_ i): eq_p_P => /=; case: (p i) => //= /negPf.
exists [ffun i => P i] => /=; apply/andP; split.
  rewrite ((big_morph qev) true andb) //= big_andE /=.
  by apply/forallP=> i; rewrite /= ffunE; case Pi: (P i) => //=; apply: negbT.
rewrite (@eq_pick _ _ P) => [|i]; first by case: pick true_at_P.
by rewrite ffunE.
Qed.

End Pick.

Section MultiQuant.

Variable f : formula R.
Implicit Types (I : seq nat) (e : seq R).

Lemma foldExistsP I e :
  (exists2 e', {in [predC I], same_env e e'} & holds e' f)
    <-> holds e (foldr Exists f I).
Proof.
elim: I e => /= [|i I IHi] e.
  by split=> [[e' eq_e] |]; [apply: eq_holds => i; rewrite eq_e | exists e].
split=> [[e' eq_e f_e'] | [x]]; last set e_x := set_nth 0 e i x.
  exists e'`_i; apply/IHi; exists e' => // j.
  by have:= eq_e j; rewrite nth_set_nth /= !inE; case: eqP => // ->.
case/IHi=> e' eq_e f_e'; exists e' => // j.
by have:= eq_e j; rewrite nth_set_nth /= !inE; case: eqP.
Qed.

Lemma foldForallP I e :
  (forall e', {in [predC I], same_env e e'} -> holds e' f)
    <-> holds e (foldr Forall f I).
Proof.
elim: I e => /= [|i I IHi] e.
  by split=> [|f_e e' eq_e]; [apply | apply: eq_holds f_e => i; rewrite eq_e].
split=> [f_e' x | f_e e' eq_e]; first set e_x := set_nth 0 e i x.
  apply/IHi=> e' eq_e; apply: f_e' => j.
  by have:= eq_e j; rewrite nth_set_nth /= !inE; case: eqP.
move/IHi: (f_e e'`_i); apply=> j.
by have:= eq_e j; rewrite nth_set_nth /= !inE; case: eqP => // ->.
Qed.

End MultiQuant.

End EvalTerm.

Prenex Implicits dnf_rterm.

Definition integral_domain_axiom (R : pzRingType) :=
  forall x y : R, x * y = 0 -> (x == 0) || (y == 0).

HB.mixin Record ComUnitRing_isIntegral R of ComUnitRing R := {
  mulf_eq0_subproof : integral_domain_axiom R;
}.

#[mathcomp(axiom="integral_domain_axiom"), short(type="idomainType")]
HB.structure Definition IntegralDomain :=
  {R of ComUnitRing_isIntegral R & ComUnitRing R}.

Module IntegralDomainExports.
Bind Scope ring_scope with IntegralDomain.sort.
End IntegralDomainExports.
HB.export IntegralDomainExports.

Section IntegralDomainTheory.

Variable R : idomainType.
Implicit Types x y : R.

Lemma mulf_eq0 x y : (x * y == 0) = (x == 0) || (y == 0).
Proof.
apply/eqP/idP; first exact: mulf_eq0_subproof.
by case/pred2P=> ->; rewrite (mulr0, mul0r).
Qed.

Lemma prodf_eq0 (I : finType) (P : pred I) (F : I -> R) :
  reflect (exists2 i, P i & (F i == 0)) (\prod_(i | P i) F i == 0).
Proof.
apply: (iffP idP) => [|[i Pi /eqP Fi0]]; last first.
  by rewrite (bigD1 i) //= Fi0 mul0r.
elim: (index_enum _) => [|i r IHr]; first by rewrite big_nil oner_eq0.
rewrite big_cons /=; have [Pi | _] := ifP; last exact: IHr.
by rewrite mulf_eq0; case/orP=> // Fi0; exists i.
Qed.

Lemma prodf_seq_eq0 I r (P : pred I) (F : I -> R) :
  (\prod_(i <- r | P i) F i == 0) = has (fun i => P i && (F i == 0)) r.
Proof. by rewrite (big_morph _ mulf_eq0 (oner_eq0 _)) big_has_cond. Qed.

Lemma mulf_neq0 x y : x != 0 -> y != 0 -> x * y != 0.
Proof. by move=> x0 y0; rewrite mulf_eq0; apply/norP. Qed.

Lemma prodf_neq0 (I : finType) (P : pred I) (F : I -> R) :
  reflect (forall i, P i -> (F i != 0)) (\prod_(i | P i) F i != 0).
Proof. by rewrite (sameP (prodf_eq0 _ _) exists_inP); apply: exists_inPn. Qed.

Lemma prodf_seq_neq0 I r (P : pred I) (F : I -> R) :
  (\prod_(i <- r | P i) F i != 0) = all (fun i => P i ==> (F i != 0)) r.
Proof.
rewrite prodf_seq_eq0 -all_predC; apply: eq_all => i /=.
by rewrite implybE negb_and.
Qed.

Lemma expf_eq0 x n : (x ^+ n == 0) = (n > 0) && (x == 0).
Proof.
elim: n => [|n IHn]; first by rewrite oner_eq0.
by rewrite exprS mulf_eq0 IHn andKb.
Qed.

Lemma sqrf_eq0 x : (x ^+ 2 == 0) = (x == 0). Proof. exact: expf_eq0. Qed.

Lemma expf_neq0 x m : x != 0 -> x ^+ m != 0.
Proof. by move=> x_nz; rewrite expf_eq0; apply/nandP; right. Qed.

Lemma natf_neq0_pchar n : (n%:R != 0 :> R) = (pchar R)^'.-nat n.
Proof.
have [-> | /prod_prime_decomp->] := posnP n; first by rewrite eqxx.
rewrite !big_seq; elim/big_rec: _ => [|[p e] s /=]; first by rewrite oner_eq0.
case/mem_prime_decomp=> p_pr _ _; rewrite pnatM pnatX eqn0Ngt orbC => <-.
by rewrite natrM natrX mulf_eq0 expf_eq0 negb_or negb_and pnatE ?inE p_pr.
Qed.

Lemma natf0_pchar n : n > 0 -> n%:R == 0 :> R -> exists p, p \in pchar R.
Proof.
move=> n_gt0 nR_0; exists (pdiv n`_(pchar R)).
apply: pnatP (pdiv_dvd _); rewrite ?part_pnat // ?pdiv_prime //.
by rewrite ltn_neqAle eq_sym partn_eq1 // -natf_neq0_pchar nR_0 /=.
Qed.

Lemma pcharf'_nat n : (pchar R)^'.-nat n = (n%:R != 0 :> R).
Proof.
have [-> | n_gt0] := posnP n; first by rewrite eqxx.
apply/idP/idP => [|nz_n]; last first.
  by apply/pnatP=> // p p_pr p_dvd_n; apply: contra nz_n => /dvdn_pcharf <-.
apply: contraL => n0; have [// | p pcharRp] := natf0_pchar _ n0.
have [p_pr _] := andP pcharRp; rewrite (eq_pnat _ (eq_negn (pcharf_eq pcharRp))).
by rewrite p'natE // (dvdn_pcharf pcharRp) n0.
Qed.

Lemma pcharf0P : pchar R =i pred0 <-> (forall n, (n%:R == 0 :> R) = (n == 0)%N).
Proof.
split=> pcharF0 n; last by rewrite !inE pcharF0 andbC; case: eqP => // ->.
have [-> | n_gt0] := posnP; first exact: eqxx.
by apply/negP; case/natf0_pchar=> // p; rewrite pcharF0.
Qed.

Lemma eqf_sqr x y : (x ^+ 2 == y ^+ 2) = (x == y) || (x == - y).
Proof. by rewrite -subr_eq0 subr_sqr mulf_eq0 subr_eq0 addr_eq0. Qed.

Lemma mulfI x : x != 0 -> injective ( *%R x).
Proof.
move=> nz_x y z; apply: contra_eq => neq_yz.
by rewrite -subr_eq0 -mulrBr mulf_neq0 ?subr_eq0.
Qed.

Lemma mulIf x : x != 0 -> injective ( *%R^~ x).
Proof. by move=> nz_x y z; rewrite -!(mulrC x); apply: mulfI. Qed.

Lemma divfI x : x != 0 -> injective (fun y => x / y).
Proof. by move/mulfI/inj_comp; apply; apply: invr_inj. Qed.

Lemma divIf y : y != 0 -> injective (fun x => x / y).
Proof. by rewrite -invr_eq0; apply: mulIf. Qed.

Lemma sqrf_eq1 x : (x ^+ 2 == 1) = (x == 1) || (x == -1).
Proof. by rewrite -subr_eq0 subr_sqr_1 mulf_eq0 subr_eq0 addr_eq0. Qed.

Lemma expfS_eq1 x n :
  (x ^+ n.+1 == 1) = (x == 1) || (\sum_(i < n.+1) x ^+ i == 0).
Proof. by rewrite -![_ == 1]subr_eq0 subrX1 mulf_eq0. Qed.

Lemma lregP x : reflect (lreg x) (x != 0).
Proof. by apply: (iffP idP) => [/mulfI | /lreg_neq0]. Qed.

Lemma rregP x : reflect (rreg x) (x != 0).
Proof. by apply: (iffP idP) => [/mulIf | /rreg_neq0]. Qed.

#[export]
HB.instance Definition _ := IntegralDomain.on R^o.

End IntegralDomainTheory.

#[deprecated(since="mathcomp 2.4.0", use=natf_neq0_pchar)]
Notation natf_neq0 := natf_neq0_pchar (only parsing).
#[deprecated(since="mathcomp 2.4.0", use=natf0_pchar)]
Notation natf0_char := natf0_pchar (only parsing).
#[deprecated(since="mathcomp 2.4.0", use=pcharf'_nat)]
Notation charf'_nat := pcharf'_nat (only parsing).
#[deprecated(since="mathcomp 2.4.0", use=pcharf0P)]
Notation charf0P := pcharf0P (only parsing).

Arguments lregP {R x}.
Arguments rregP {R x}.

Definition field_axiom (R : unitRingType) := forall x : R, x != 0 -> x \in unit.

HB.mixin Record UnitRing_isField R of UnitRing R := {
  fieldP : field_axiom R;
}.

#[mathcomp(axiom="field_axiom"), short(type="fieldType")]
HB.structure Definition Field := { R of IntegralDomain R & UnitRing_isField R }.

Module FieldExports.
Bind Scope ring_scope with Field.sort.
End FieldExports.
HB.export FieldExports.

#[export] HB.instance Definition regular_field (F : fieldType) := Field.on F^o.

Lemma IdomainMixin (R : unitRingType): Field.axiom R -> IntegralDomain.axiom R.
Proof.
move=> m x y xy0; apply/norP=> [[]] /m Ux /m.
by rewrite -(unitrMr _ Ux) xy0 unitr0.
Qed.

HB.factory Record ComUnitRing_isField R of ComUnitRing R := {
  fieldP : field_axiom R;
}.
HB.builders Context R of ComUnitRing_isField R.
HB.instance Definition _ :=
  ComUnitRing_isIntegral.Build R (IdomainMixin fieldP).
HB.instance Definition _ := UnitRing_isField.Build R fieldP.
HB.end.

HB.factory Record ComNzRing_isField R of ComNzRing R := {
  inv : R -> R;
  mulVf : forall x, x != 0 -> inv x * x = 1;
  invr0 : inv 0 = 0;
}.

Module ComRing_isField.
#[deprecated(since="mathcomp 2.4.0", use=ComNzRing_isField.Build)]
Notation Build R := (ComNzRing_isField.Build R) (only parsing).
End ComRing_isField.

#[deprecated(since="mathcomp 2.4.0", use=ComNzRing_isField)]
Notation ComRing_isField R := (ComNzRing_isField R) (only parsing).

HB.builders Context R of ComNzRing_isField R.

Fact intro_unit (x y : R) : y * x = 1 -> x != 0.
Proof.
move=> yx1; apply: contraNneq (@oner_neq0 R) => x0.
by rewrite -yx1 x0 mulr0.
Qed.

Fact inv_out : {in predC (predC1 0), inv =1 id}.
Proof. by move=> x /negbNE/eqP->; exact: invr0. Qed.

HB.instance Definition _ : ComNzRing_hasMulInverse R :=
  ComNzRing_hasMulInverse.Build R mulVf intro_unit inv_out.

HB.instance Definition _ : ComUnitRing_isField R :=
  ComUnitRing_isField.Build R (fun x x_neq_0 => x_neq_0).

HB.end.

Section FieldTheory.

Variable F : fieldType.
Implicit Types x y : F.

Lemma unitfE x : (x \in unit) = (x != 0).
Proof. by apply/idP/idP=> [/(memPn _)-> | /fieldP]; rewrite ?unitr0. Qed.

Lemma mulVf x : x != 0 -> x^-1 * x = 1.
Proof. by rewrite -unitfE; apply: mulVr. Qed.
Lemma divff x : x != 0 -> x / x = 1.
Proof. by rewrite -unitfE; apply: divrr. Qed.
Definition mulfV := divff.
Lemma mulKf x : x != 0 -> cancel ( *%R x) ( *%R x^-1).
Proof. by rewrite -unitfE; apply: mulKr. Qed.
Lemma mulVKf x : x != 0 -> cancel ( *%R x^-1) ( *%R x).
Proof. by rewrite -unitfE; apply: mulVKr. Qed.
Lemma mulfK x : x != 0 -> cancel ( *%R^~ x) ( *%R^~ x^-1).
Proof. by rewrite -unitfE; apply: mulrK. Qed.
Lemma mulfVK x : x != 0 -> cancel ( *%R^~ x^-1) ( *%R^~ x).
Proof. by rewrite -unitfE; apply: divrK. Qed.
Definition divfK := mulfVK.

Lemma invfM : {morph @inv F : x y / x * y}.
Proof.
move=> x y; have [->|nzx] := eqVneq x 0; first by rewrite !(mul0r, invr0).
have [->|nzy] := eqVneq y 0; first by rewrite !(mulr0, invr0).
by rewrite mulrC invrM ?unitfE.
Qed.

Lemma invf_div x y : (x / y)^-1 = y / x.
Proof. by rewrite invfM invrK mulrC. Qed.

Lemma divKf x : x != 0 -> involutive (fun y => x / y).
Proof. by move=> nz_x y; rewrite invf_div mulrC divfK. Qed.

Lemma expfB_cond m n x : (x == 0) + n <= m -> x ^+ (m - n) = x ^+ m / x ^+ n.
Proof.
move/subnK=> <-; rewrite addnA addnK !exprD.
have [-> | nz_x] := eqVneq; first by rewrite !mulr0 !mul0r.
by rewrite mulfK ?expf_neq0.
Qed.

Lemma expfB m n x : n < m -> x ^+ (m - n) = x ^+ m / x ^+ n.
Proof. by move=> lt_n_m; apply: expfB_cond; case: eqP => // _; apply: ltnW. Qed.

Lemma prodfV I r (P : pred I) (E : I -> F) :
  \prod_(i <- r | P i) (E i)^-1 = (\prod_(i <- r | P i) E i)^-1.
Proof. by rewrite (big_morph _ invfM (invr1 F)). Qed.

Lemma prodf_div I r (P : pred I) (E D : I -> F) :
  \prod_(i <- r | P i) (E i / D i) =
     \prod_(i <- r | P i) E i / \prod_(i <- r | P i) D i.
Proof. by rewrite big_split prodfV. Qed.

Lemma telescope_prodf n m (f : nat -> F) :
    (forall k, n < k < m -> f k != 0) -> n < m ->
  \prod_(n <= k < m) (f k.+1 / f k) = f m / f n.
Proof.
move=> nz_f ltnm; apply: invr_inj; rewrite prodf_div !invf_div -prodf_div.
by apply: telescope_prodr => // k /nz_f; rewrite unitfE.
Qed.

Lemma telescope_prodf_eq n m (f u : nat -> F) :
    (forall k, n < k < m -> f k != 0) -> n < m ->
    (forall k, n <= k < m -> u k = f k.+1 / f k) ->
  \prod_(n <= k < m) u k = f m / f n.
Proof.
by move=> ? ? uE; under eq_big_nat do rewrite uE //=; exact: telescope_prodf.
Qed.

Lemma addf_div x1 y1 x2 y2 :
  y1 != 0 -> y2 != 0 -> x1 / y1 + x2 / y2 = (x1 * y2 + x2 * y1) / (y1 * y2).
Proof. by move=> nzy1 nzy2; rewrite invfM mulrDl !mulrA mulrAC !mulfK. Qed.

Lemma mulf_div x1 y1 x2 y2 : (x1 / y1) * (x2 / y2) = (x1 * x2) / (y1 * y2).
Proof. by rewrite mulrACA -invfM. Qed.

Lemma eqr_div x y z t : y != 0 -> t != 0 -> (x / y == z / t) = (x * t == z * y).
Proof.
move=> yD0 tD0; rewrite -[x in RHS](divfK yD0) -[z in RHS](divfK tD0) mulrAC.
by apply/eqP/eqP => [->|/(mulIf yD0)/(mulIf tD0)].
Qed.

Lemma eqr_sum_div I r P (f : I -> F) c a : c != 0 ->
  (\big[+%R/0]_(x <- r | P x) (f x / c) == a)
  = (\big[+%R/0]_(x <- r | P x) f x == a * c).
Proof.
by move=> ?; rewrite -mulr_suml -(divr1 a) eqr_div ?oner_eq0// mulr1 divr1.
Qed.

Lemma pchar0_natf_div :
  pchar F =i pred0 -> forall m d, d %| m -> (m %/ d)%:R = m%:R / d%:R :> F.
Proof.
move/pcharf0P=> pchar0F m [|d] d_dv_m; first by rewrite divn0 invr0 mulr0.
by rewrite natr_div // unitfE pchar0F.
Qed.

Section FieldMorphismInj.

Variables (R : nzRingType) (f : {rmorphism F -> R}).

Lemma fmorph_eq0 x : (f x == 0) = (x == 0).
Proof.
have [-> | nz_x] := eqVneq x; first by rewrite rmorph0 eqxx.
apply/eqP; move/(congr1 ( *%R (f x^-1)))/eqP.
by rewrite -rmorphM mulVf // mulr0 rmorph1 ?oner_eq0.
Qed.

Lemma fmorph_inj : injective f.
Proof. by apply/raddf_inj => x /eqP; rewrite fmorph_eq0 => /eqP. Qed.

Lemma fmorph_eq : {mono f : x y / x == y}.
Proof. exact: inj_eq fmorph_inj. Qed.

Lemma fmorph_eq1 x : (f x == 1) = (x == 1).
Proof. by rewrite -(inj_eq fmorph_inj) rmorph1. Qed.

Lemma fmorph_pchar : pchar R =i pchar F.
Proof. by move=> p; rewrite !inE -fmorph_eq0 rmorph_nat. Qed.

End FieldMorphismInj.

Section FieldMorphismInv.

Variables (R : unitRingType) (f : {rmorphism F -> R}).

Lemma fmorph_unit x : (f x \in unit) = (x != 0).
Proof.
have [-> |] := eqVneq x; first by rewrite rmorph0 unitr0.
by rewrite -unitfE; apply: rmorph_unit.
Qed.

Lemma fmorphV : {morph f: x / x^-1}.
Proof.
move=> x; have [-> | nz_x] := eqVneq x 0; first by rewrite !(invr0, rmorph0).
by rewrite rmorphV ?unitfE.
Qed.

Lemma fmorph_div : {morph f : x y / x / y}.
Proof. by move=> x y; rewrite rmorphM /= fmorphV. Qed.

End FieldMorphismInv.

Section ModuleTheory.

Variable V : lmodType F.
Implicit Types (a : F) (v : V).

Lemma scalerK a : a != 0 -> cancel ( *:%R a : V -> V) ( *:%R a^-1).
Proof. by move=> nz_a v; rewrite scalerA mulVf // scale1r. Qed.

Lemma scalerKV a : a != 0 -> cancel ( *:%R a^-1 : V -> V) ( *:%R a).
Proof. by rewrite -invr_eq0 -{3}[a]invrK; apply: scalerK. Qed.

Lemma scalerI a : a != 0 -> injective ( *:%R a : V -> V).
Proof. by move=> nz_a; apply: can_inj (scalerK nz_a). Qed.

Lemma scaler_eq0 a v : (a *: v == 0) = (a == 0) || (v == 0).
Proof.
have [-> | nz_a] := eqVneq a; first by rewrite scale0r eqxx.
by rewrite (can2_eq (scalerK nz_a) (scalerKV nz_a)) scaler0.
Qed.

End ModuleTheory.

Lemma pchar_lalg (A : nzLalgType F) : pchar A =i pchar F.
Proof. by move=> p; rewrite inE -scaler_nat scaler_eq0 oner_eq0 orbF. Qed.

End FieldTheory.

#[deprecated(since="mathcomp 2.4.0", use=pchar0_natf_div)]
Notation char0_natf_div := pchar0_natf_div (only parsing).
#[deprecated(since="mathcomp 2.4.0", use=fmorph_pchar)]
Notation fmorph_char := fmorph_pchar (only parsing).
#[deprecated(since="mathcomp 2.4.0", use=pchar_lalg)]
Notation char_lalg := pchar_lalg (only parsing).

Arguments fmorph_inj {F R} f [x1 x2].
Arguments telescope_prodf_eq {F n m} f u.

Definition decidable_field_axiom (R : unitRingType)
    (s : seq R -> pred (formula R)) :=
  forall e f, reflect (holds e f) (s e f).

HB.mixin Record Field_isDecField R of UnitRing R := {
  sat : seq R -> pred (formula R);
  satP : decidable_field_axiom sat;
}.

#[mathcomp(axiom="decidable_field_axiom"), short(type="decFieldType")]
HB.structure Definition DecidableField := { F of Field F & Field_isDecField F }.

Module DecFieldExports.
Bind Scope ring_scope with DecidableField.sort.
End DecFieldExports.
HB.export DecFieldExports.

#[export] HB.instance Definition _ (F : decFieldType) := DecidableField.on F^o.

Section DecidableFieldTheory.

Variable F : decFieldType.
Implicit Type f : formula F.

Fact sol_subproof n f :
  reflect (exists s, (size s == n) && sat s f)
          (sat [::] (foldr Exists f (iota 0 n))).
Proof.
apply: (iffP (satP _ _)) => [|[s]]; last first.
  case/andP=> /eqP sz_s /satP f_s; apply/foldExistsP.
  exists s => // i; rewrite !inE mem_iota -leqNgt add0n => le_n_i.
  by rewrite !nth_default ?sz_s.
case/foldExistsP=> e e0 f_e; set s := take n (set_nth 0 e n 0).
have sz_s: size s = n by rewrite size_take size_set_nth leq_max leqnn.
exists s; rewrite sz_s eqxx; apply/satP; apply: eq_holds f_e => i.
case: (leqP n i) => [le_n_i | lt_i_n].
  by rewrite -e0 ?nth_default ?sz_s // !inE mem_iota -leqNgt.
by rewrite nth_take // nth_set_nth /= eq_sym eqn_leq leqNgt lt_i_n.
Qed.

Definition sol n f :=
  if sol_subproof n f is ReflectT sP then xchoose sP else nseq n 0.

Lemma size_sol n f : size (sol n f) = n.
Proof.
rewrite /sol; case: sol_subproof => [sP | _]; last exact: size_nseq.
by case/andP: (xchooseP sP) => /eqP.
Qed.

Lemma solP n f : reflect (exists2 s, size s = n & holds s f) (sat (sol n f) f).
Proof.
rewrite /sol; case: sol_subproof => [sP | sPn].
  case/andP: (xchooseP sP) => _ ->; left.
  by case: sP => s; case/andP; move/eqP=> <-; move/satP; exists s.
apply: (iffP (satP _ _)); first by exists (nseq n 0); rewrite ?size_nseq.
by case=> s sz_s; move/satP=> f_s; case: sPn; exists s; rewrite sz_s eqxx.
Qed.

Lemma eq_sat f1 f2 :
  (forall e, holds e f1 <-> holds e f2) -> sat^~ f1 =1 sat^~ f2.
Proof. by move=> eqf12 e; apply/satP/satP; case: (eqf12 e). Qed.

Lemma eq_sol f1 f2 :
  (forall e, holds e f1 <-> holds e f2) -> sol^~ f1 =1 sol^~ f2.
Proof.
rewrite /sol => /eq_sat eqf12 n.
do 2![case: sol_subproof] => //= [f1s f2s | ns1 [s f2s] | [s f1s] []].
- by apply: eq_xchoose => s; rewrite eqf12.
- by case: ns1; exists s; rewrite -eqf12.
by exists s; rewrite eqf12.
Qed.

End DecidableFieldTheory.

Arguments satP {F e f} : rename.
Arguments solP {F n f} : rename.

Section QE_Mixin.

Variable F : Field.type.
Implicit Type f : formula F.

Variable proj : nat -> seq (term F) * seq (term F) -> formula F.
(* proj is the elimination of a single existential quantifier *)

(* The elimination projector is well_formed. *)
Definition wf_QE_proj :=
  forall i bc (bc_i := proj i bc),
  dnf_rterm bc -> qf_form bc_i && rformula bc_i.

(* The elimination projector is valid *)
Definition valid_QE_proj :=
  forall i bc (ex_i_bc := ('exists 'X_i, dnf_to_form [:: bc])%T) e,
  dnf_rterm bc -> reflect (holds e ex_i_bc) (qf_eval e (proj i bc)).

Hypotheses (wf_proj : wf_QE_proj) (ok_proj : valid_QE_proj).

Let elim_aux f n := foldr Or False (map (proj n) (qf_to_dnf f false)).

Fixpoint quantifier_elim f :=
  match f with
  | f1 /\ f2 => (quantifier_elim f1) /\ (quantifier_elim f2)
  | f1 \/ f2 => (quantifier_elim f1) \/ (quantifier_elim f2)
  | f1 ==> f2 => (~ quantifier_elim f1) \/ (quantifier_elim f2)
  | ~ f => ~ quantifier_elim f
  | ('exists 'X_n, f) => elim_aux (quantifier_elim f) n
  | ('forall 'X_n, f) => ~ elim_aux (~ quantifier_elim f) n
  | _ => f
  end%T.

Lemma quantifier_elim_wf f :
  let qf := quantifier_elim f in rformula f -> qf_form qf && rformula qf.
Proof.
suffices aux_wf f0 n : let qf := elim_aux f0 n in
  rformula f0 -> qf_form qf && rformula qf.
- by elim: f => //=; do ?[  move=> f1 IH1 f2 IH2;
                     case/andP=> rf1 rf2;
                     case/andP:(IH1 rf1)=> -> ->;
                     case/andP:(IH2 rf2)=> -> -> //
                  |  move=> n f1 IH rf1;
                     case/andP: (IH rf1)=> qff rf;
                     rewrite aux_wf ].
rewrite /elim_aux => rf.
suffices or_wf fs : let ofs := foldr Or False fs in
  all (@qf_form F) fs && all (@rformula F) fs -> qf_form ofs && rformula ofs.
- apply: or_wf.
  suffices map_proj_wf bcs: let mbcs := map (proj n) bcs in
    all dnf_rterm bcs -> all (@qf_form _) mbcs && all (@rformula _) mbcs.
    by apply/map_proj_wf/qf_to_dnf_rterm.
  elim: bcs => [|bc bcs ihb] bcsr //= /andP[rbc rbcs].
  by rewrite andbAC andbA wf_proj //= andbC ihb.
elim: fs => //= g gs ihg; rewrite -andbA => /and4P[-> qgs -> rgs] /=.
by apply: ihg; rewrite qgs rgs.
Qed.

Lemma quantifier_elim_rformP e f :
  rformula f -> reflect (holds e f) (qf_eval e (quantifier_elim f)).
Proof.
pose rc e n f := exists x, qf_eval (set_nth 0 e n x) f.
have auxP f0 e0 n0: qf_form f0 && rformula f0 ->
  reflect (rc e0 n0 f0) (qf_eval e0 (elim_aux f0 n0)).
+ rewrite /elim_aux => cf; set bcs := qf_to_dnf f0 false.
  apply: (@iffP (rc e0 n0 (dnf_to_form bcs))); last first.
  - by case=> x; rewrite -qf_to_dnfP //; exists x.
  - by case=> x; rewrite qf_to_dnfP //; exists x.
  have: all dnf_rterm bcs by case/andP: cf => _; apply: qf_to_dnf_rterm.
  elim: {f0 cf}bcs => [|bc bcs IHbcs] /=; first by right; case.
  case/andP=> r_bc /IHbcs {IHbcs}bcsP.
  have f_qf := dnf_to_form_qf [:: bc].
  case: ok_proj => //= [ex_x|no_x].
    left; case: ex_x => x /(qf_evalP _ f_qf); rewrite /= orbF => bc_x.
    by exists x; rewrite /= bc_x.
  apply: (iffP bcsP) => [[x bcs_x] | [x]] /=.
    by exists x; rewrite /= bcs_x orbT.
  case/orP => [bc_x|]; last by exists x.
  by case: no_x; exists x; apply/(qf_evalP _ f_qf); rewrite /= bc_x.
elim: f e => //.
- by move=> b e _; apply: idP.
- by move=> t1 t2 e _; apply: eqP.
- move=> f1 IH1 f2 IH2 e /= /andP[/IH1[] f1e]; last by right; case.
  by case/IH2; [left | right; case].
- move=> f1 IH1 f2 IH2 e /= /andP[/IH1[] f1e]; first by do 2!left.
  by case/IH2; [left; right | right; case].
- move=> f1 IH1 f2 IH2 e /= /andP[/IH1[] f1e]; last by left.
  by case/IH2; [left | right; move/(_ f1e)].
- by move=> f IHf e /= /IHf[]; [right | left].
- move=> n f IHf e /= rf; have rqf := quantifier_elim_wf rf.
  by apply: (iffP (auxP _ _ _ rqf)) => [] [x]; exists x; apply/IHf.
move=> n f IHf e /= rf; have rqf := quantifier_elim_wf rf.
case: auxP => // [f_x|no_x]; first by right=> no_x; case: f_x => x /IHf[].
by left=> x; apply/IHf=> //; apply/idPn=> f_x; case: no_x; exists x.
Qed.

Definition proj_sat e f := qf_eval e (quantifier_elim (to_rform f)).

Lemma proj_satP : DecidableField.axiom proj_sat.
Proof.
move=> e f; have fP := quantifier_elim_rformP e (to_rform_rformula f).
by apply: (iffP fP); move/to_rformP.
Qed.

End QE_Mixin.

HB.factory Record Field_QE_isDecField F of Field F := {
  proj : nat -> seq (term F) * seq (term F) -> formula F;
  wf_proj : wf_QE_proj proj;
  ok_proj : valid_QE_proj proj;
}.
HB.builders Context F of Field_QE_isDecField F.

HB.instance Definition qe_is_def_field : Field_isDecField F :=
  Field_isDecField.Build F (proj_satP wf_proj ok_proj).
HB.end.

(* Axiom == all non-constant monic polynomials have a root *)
Definition closed_field_axiom (R : pzRingType) :=
  forall n (P : nat -> R), n > 0 ->
   exists x : R, x ^+ n = \sum_(i < n) P i * (x ^+ i).

HB.mixin Record DecField_isAlgClosed F of DecidableField F := {
  solve_monicpoly : closed_field_axiom F;
}.

#[mathcomp(axiom="closed_field_axiom"), short(type="closedFieldType")]
HB.structure Definition ClosedField :=
  { F of DecidableField F & DecField_isAlgClosed F }.

Module ClosedFieldExports.
Bind Scope ring_scope with ClosedField.sort.
End ClosedFieldExports.
HB.export ClosedFieldExports.

#[export] HB.instance Definition _ (F : closedFieldType) := ClosedField.on F^o.

Section ClosedFieldTheory.

Variable F : closedFieldType.

Lemma imaginary_exists : {i : F | i ^+ 2 = -1}.
Proof.
have /sig_eqW[i Di2] := @solve_monicpoly F 2 (nth 0 [:: -1]) isT.
by exists i; rewrite Di2 !big_ord_recl big_ord0 mul0r mulr1 !addr0.
Qed.

End ClosedFieldTheory.

(* Mixins for stability properties *)

HB.mixin Record isInvClosed (R : unitRingType) (S : {pred R}) := {
  rpredVr : invr_closed S
}.

(* Structures for stability properties *)

#[short(type="divClosed")]
HB.structure Definition DivClosed (R : unitRingType) :=
  {S of MulClosed R S & isInvClosed R S}.

#[short(type="sdivClosed")]
HB.structure Definition SdivClosed (R : unitRingType) :=
  {S of SmulClosed R S & isInvClosed R S}.

#[short(type="divringClosed")]
HB.structure Definition DivringClosed (R : unitRingType) :=
  {S of SubringClosed R S & isInvClosed R S}.

#[short(type="divalgClosed")]
HB.structure Definition DivalgClosed (R : nzRingType) (A : unitAlgType R) :=
  {S of DivringClosed A S & isScaleClosed R A S}.

(* Factories for stability properties *)

HB.factory Record isDivClosed (R : unitRingType) (S : R -> bool) := {
  divr_closed_subproof : divr_closed S
}.

HB.builders Context R S of isDivClosed R S.
HB.instance Definition _ := isMulClosed.Build R S
  (divr_closedM divr_closed_subproof).
HB.instance Definition _ := isInvClosed.Build R S
  (divr_closedV divr_closed_subproof).
HB.end.

HB.factory Record isSdivClosed (R : unitRingType) (S : R -> bool) := {
  sdivr_closed_subproof : sdivr_closed S
}.

HB.builders Context R S of isSdivClosed R S.
HB.instance Definition _ := isDivClosed.Build R S
  (sdivr_closed_div sdivr_closed_subproof).
HB.instance Definition _ := isSmulClosed.Build R S
  (sdivr_closedM sdivr_closed_subproof).
HB.end.

HB.factory Record isDivringClosed (R : unitRingType) (S : R -> bool) := {
  divring_closed_subproof : divring_closed S
}.

HB.builders Context R S of isDivringClosed R S.
HB.instance Definition _ := isSubringClosed.Build R S
  (divring_closedBM divring_closed_subproof).
HB.instance Definition _ := isSdivClosed.Build R S
  (divring_closed_div divring_closed_subproof).
HB.end.

HB.factory Record isDivalgClosed (R : comUnitRingType) (A : unitAlgType R)
    (S : A -> bool) := {
  divalg_closed_subproof : divalg_closed S
}.

HB.builders Context R A S of isDivalgClosed R A S.
HB.instance Definition _ := isDivringClosed.Build A S
  (divalg_closedBdiv divalg_closed_subproof).
HB.instance Definition _ := isSubalgClosed.Build R A S
  (subalg_closed_semi (divalg_closedZ divalg_closed_subproof)).
HB.end.

Section UnitRingPred.

Variable R : unitRingType.

Section Div.

Variable S : divClosed R.

Lemma rpredV x : (x^-1 \in S) = (x \in S).
Proof. by apply/idP/idP=> /rpredVr; rewrite ?invrK. Qed.

Lemma rpred_div : {in S &, forall x y, x / y \in S}.
Proof. by move=> x y Sx Sy; rewrite /= rpredM ?rpredV. Qed.

Lemma rpredXN n : {in S, forall x, x ^- n \in S}.
Proof. by move=> x Sx; rewrite /= rpredV rpredX. Qed.

Lemma rpredMl x y : x \in S -> x \is a unit-> (x * y \in S) = (y \in S).
Proof.
move=> Sx Ux; apply/idP/idP=> [Sxy | /(rpredM _ _ Sx)-> //].
by rewrite -(mulKr Ux y); rewrite rpredM ?rpredV.
Qed.

Lemma rpredMr x y : x \in S -> x \is a unit -> (y * x \in S) = (y \in S).
Proof.
move=> Sx Ux; apply/idP/idP=> [Sxy | /rpredM-> //].
by rewrite -(mulrK Ux y); rewrite rpred_div.
Qed.

Lemma rpred_divr x y : x \in S -> x \is a unit -> (y / x \in S) = (y \in S).
Proof. by rewrite -rpredV -unitrV; apply: rpredMr. Qed.

Lemma rpred_divl x y : x \in S -> x \is a unit -> (x / y \in S) = (y \in S).
Proof. by rewrite -(rpredV y); apply: rpredMl. Qed.

End Div.

Lemma divringClosedP (divS : divringClosed R) : divring_closed divS.
Proof. split; [ exact: rpred1 | exact: rpredB | exact: rpred_div ]. Qed.

Fact unitr_sdivr_closed : @sdivr_closed R unit.
Proof. by split=> [|x y Ux Uy]; rewrite ?unitrN1 // unitrMl ?unitrV. Qed.

#[export]
HB.instance Definition _ := isSdivClosed.Build R unit_pred unitr_sdivr_closed.

Implicit Type x : R.

Lemma unitrN x : (- x \is a unit) = (x \is a unit). Proof. exact: rpredN. Qed.

Lemma invrN x : (- x)^-1 = - x^-1.
Proof.
have [Ux | U'x] := boolP (x \is a unit); last by rewrite !invr_out ?unitrN.
by rewrite -mulN1r invrM ?unitrN1 // invrN1 mulrN1.
Qed.

Lemma divrNN x y : (- x) / (- y) = x / y.
Proof. by rewrite invrN mulrNN. Qed.

Lemma divrN x y : x / (- y) = - (x / y).
Proof. by rewrite invrN mulrN. Qed.

Lemma invr_signM n x : ((-1) ^+ n * x)^-1 = (-1) ^+ n * x^-1.
Proof. by rewrite -signr_odd !mulr_sign; case: ifP => // _; rewrite invrN. Qed.

Lemma divr_signM (b1 b2 : bool) x1 x2:
  ((-1) ^+ b1 * x1) / ((-1) ^+ b2 * x2) = (-1) ^+ (b1 (+) b2) * (x1 / x2).
Proof. by rewrite invr_signM mulr_signM. Qed.

End UnitRingPred.

Section FieldPred.

Variable F : fieldType.
Implicit Types x y : F.

Section ModuleTheory.

Variable V : lmodType F.
Implicit Types (a : F) (v : V).

Lemma rpredZeq (S : submodClosed V) a v :
  (a *: v \in S) = (a == 0) || (v \in S).
Proof.
have [-> | nz_a] := eqVneq; first by rewrite scale0r rpred0.
by apply/idP/idP; first rewrite -{2}(scalerK nz_a v); apply: rpredZ.
Qed.

End ModuleTheory.

Section Predicates.

Context (S : divClosed F).

Lemma fpredMl x y : x \in S -> x != 0 -> (x * y \in S) = (y \in S).
Proof. by rewrite -!unitfE; apply: rpredMl. Qed.

Lemma fpredMr x y : x \in S -> x != 0 -> (y * x \in S) = (y \in S).
Proof. by rewrite -!unitfE; apply: rpredMr. Qed.

Lemma fpred_divl x y : x \in S -> x != 0 -> (x / y \in S) = (y \in S).
Proof. by rewrite -!unitfE; apply: rpred_divl. Qed.

Lemma fpred_divr x y : x \in S -> x != 0 -> (y / x \in S) = (y \in S).
Proof. by rewrite -!unitfE; apply: rpred_divr. Qed.

End Predicates.

End FieldPred.

#[short(type="subUnitRingType")]
HB.structure Definition SubUnitRing (R : nzRingType) (S : pred R) :=
  {U of SubNzRing R S U & UnitRing U}.

HB.factory Record SubNzRing_isSubUnitRing (R : unitRingType) S U
    of SubNzRing R S U := {
  divring_closed_subproof : divring_closed S
}.

HB.builders Context R S U of SubNzRing_isSubUnitRing R S U.

HB.instance Definition _ := isDivringClosed.Build R S divring_closed_subproof.

Let inU v Sv : U := Sub v Sv.
Let invU (u : U) := inU (rpredVr _ (valP u)).

Lemma mulVr : {in [pred x | val x \is a unit], left_inverse 1 invU *%R}.
Proof.
by move=> x /[!inE] xu; apply: val_inj; rewrite rmorphM rmorph1 /= SubK mulVr.
Qed.
Lemma divrr : {in [pred x | val x \is a unit], right_inverse 1 invU *%R}.
by move=> x /[!inE] xu; apply: val_inj; rewrite rmorphM rmorph1 /= SubK mulrV.
Qed.
Lemma unitrP (x y : U) : y * x = 1 /\ x * y = 1 -> val x \is a unit.
Proof.
move=> -[/(congr1 val) yx1 /(congr1 val) xy1].
by apply: rev_unitrP (val y) _; rewrite !rmorphM rmorph1 /= in yx1 xy1.
Qed.
Lemma invr_out : {in [pred x | val x \isn't a unit], invU =1 id}.
Proof.
by move=> x /[!inE] xNU; apply: val_inj; rewrite SubK invr_out.
Qed.
HB.instance Definition _ := NzRing_hasMulInverse.Build U
  mulVr divrr unitrP invr_out.
HB.end.

#[short(type="subComUnitRingType")]
HB.structure Definition SubComUnitRing (R : comUnitRingType) (S : pred R) :=
  {U of SubComNzRing R S U & SubUnitRing R S U}.

#[short(type="subIdomainType")]
HB.structure Definition SubIntegralDomain (R : idomainType) (S : pred R) :=
  {U of SubComNzRing R S U & IntegralDomain U}.

HB.factory Record SubComUnitRing_isSubIntegralDomain (R : idomainType) S U
  of SubComUnitRing R S U := {}.

HB.builders Context R S U of SubComUnitRing_isSubIntegralDomain R S U.
Lemma id : IntegralDomain.axiom U.
Proof.
move=> x y /(congr1 val)/eqP; rewrite rmorphM /=.
by rewrite -!(inj_eq val_inj) rmorph0 -mulf_eq0.
Qed.
HB.instance Definition _ := ComUnitRing_isIntegral.Build U id.
HB.end.

#[short(type="subFieldType")]
HB.structure Definition SubField (F : fieldType) (S : pred F) :=
  {U of SubIntegralDomain F S U & Field U}.

HB.factory Record SubIntegralDomain_isSubField (F : fieldType) S U
    of SubIntegralDomain F S U := {
  subfield_subproof : {mono (val : U -> F) : u / u \in unit}
}.

HB.builders Context F S U of SubIntegralDomain_isSubField F S U.
Lemma fieldP : Field.axiom U.
Proof.
by move=> u; rewrite -(inj_eq val_inj) rmorph0 -unitfE subfield_subproof.
Qed.
HB.instance Definition _ := UnitRing_isField.Build U fieldP.
HB.end.

HB.factory Record SubChoice_isSubUnitRing (R : unitRingType) S U
    of SubChoice R S U := {
  divring_closed_subproof : divring_closed S
}.

HB.builders Context R S U of SubChoice_isSubUnitRing R S U.
HB.instance Definition _ := SubChoice_isSubNzRing.Build R S U
  (divring_closedBM divring_closed_subproof).
HB.instance Definition _ := SubNzRing_isSubUnitRing.Build R S U
  divring_closed_subproof.
HB.end.

HB.factory Record SubChoice_isSubComUnitRing (R : comUnitRingType) S U
    of SubChoice R S U := {
  divring_closed_subproof : divring_closed S
}.

HB.builders Context R S U of SubChoice_isSubComUnitRing R S U.
HB.instance Definition _ := SubChoice_isSubComNzRing.Build R S U
  (divring_closedBM divring_closed_subproof).
HB.instance Definition _ := SubNzRing_isSubUnitRing.Build R S U
  divring_closed_subproof.
HB.end.

HB.factory Record SubChoice_isSubIntegralDomain (R : idomainType) S U
    of SubChoice R S U := {
  divring_closed_subproof : divring_closed S
}.

HB.builders Context R S U of SubChoice_isSubIntegralDomain R S U.
HB.instance Definition _ := SubChoice_isSubComUnitRing.Build R S U
  divring_closed_subproof.
HB.instance Definition _ := SubComUnitRing_isSubIntegralDomain.Build R S U.
HB.end.

Module SubExports.

Notation "[ 'SubNzRing_isSubUnitRing' 'of' U 'by' <: ]" :=
  (SubNzRing_isSubUnitRing.Build _ _ U (divringClosedP _))
  (format "[ 'SubNzRing_isSubUnitRing'  'of'  U  'by'  <: ]")
  : form_scope.
#[deprecated(since="mathcomp 2.4.0",
             note="Use [ SubNzRing_isSubUnitRing of U by <: ] instead.")]
Notation "[ 'SubRing_isSubUnitRing' 'of' U 'by' <: ]" :=
  (SubNzRing_isSubUnitRing.Build _ _ U (divringClosedP _))
  (format "[ 'SubRing_isSubUnitRing'  'of'  U  'by'  <: ]")
  : form_scope.
Notation "[ 'SubChoice_isSubUnitRing' 'of' U 'by' <: ]" :=
  (SubChoice_isSubUnitRing.Build _ _ U (divringClosedP _))
  (format "[ 'SubChoice_isSubUnitRing'  'of'  U  'by'  <: ]")
  : form_scope.
Notation "[ 'SubChoice_isSubComUnitRing' 'of' U 'by' <: ]" :=
  (SubChoice_isSubComUnitRing.Build _ _ U (divringClosedP _))
  (format "[ 'SubChoice_isSubComUnitRing'  'of'  U  'by'  <: ]")
  : form_scope.
Notation "[ 'SubComUnitRing_isSubIntegralDomain' 'of' U 'by' <: ]" :=
  (SubComUnitRing_isSubIntegralDomain.Build _ _ U)
  (format "[ 'SubComUnitRing_isSubIntegralDomain'  'of'  U  'by'  <: ]")
  : form_scope.
Notation "[ 'SubChoice_isSubIntegralDomain' 'of' U 'by' <: ]" :=
  (SubChoice_isSubIntegralDomain.Build _ _ U (divringClosedP _))
  (format "[ 'SubChoice_isSubIntegralDomain'  'of'  U  'by'  <: ]")
  : form_scope.
Notation "[ 'SubIntegralDomain_isSubField' 'of' U 'by' <: ]" :=
  (SubIntegralDomain_isSubField.Build _ _ U (frefl _))
  (format "[ 'SubIntegralDomain_isSubField'  'of'  U  'by'  <: ]")
  : form_scope.

End SubExports.
HB.export SubExports.

Module Theory.

Export GRing.Theory.

Definition lregP {R x} := @lregP R x.
Definition rregP {R x} := @rregP R x.
Definition mulrV := mulrV.
Definition divrr := divrr.
Definition mulVr := mulVr.
Definition invr_out := invr_out.
Definition unitrP {R x} := @unitrP R x.
Definition mulKr := mulKr.
Definition mulVKr := mulVKr.
Definition mulrK := mulrK.
Definition mulrVK := mulrVK.
Definition divrK := divrK.
Definition mulrI := mulrI.
Definition mulIr := mulIr.
Definition divrI := divrI.
Definition divIr := divIr.
Definition telescope_prodr := telescope_prodr.
Definition telescope_prodr_eq := @telescope_prodr_eq.
Arguments telescope_prodr_eq {R n m} f u.
Definition commrV := commrV.
Definition unitrE := unitrE.
Definition invrK := @invrK.
Arguments invrK {R}.
Definition invr_inj := @invr_inj.
Arguments invr_inj {R} [x1 x2].
Definition unitrV := unitrV.
Definition unitr1 := unitr1.
Definition invr1 := invr1.
Definition divr1 := divr1.
Definition div1r := div1r.
Definition natr_div := natr_div.
Definition unitr0 := unitr0.
Definition invr0 := invr0.
Definition unitrN1 := unitrN1.
Definition unitrN := unitrN.
Definition invrN1 := invrN1.
Definition invrN := invrN.
Definition divrNN := divrNN.
Definition divrN := divrN.
Definition invr_sign := invr_sign.
Definition unitrMl := unitrMl.
Definition unitrMr := unitrMr.
Definition invrM := invrM.
Definition unitr_prod := unitr_prod.
Definition unitr_prod_in := unitr_prod_in.
Definition invr_eq0 := invr_eq0.
Definition invr_eq1 := invr_eq1.
Definition invr_neq0 := invr_neq0.
Definition rev_unitrP := rev_unitrP.
Definition rev_prodrV := rev_prodrV.
Definition unitrM_comm := unitrM_comm.
Definition unitrX := unitrX.
Definition unitrX_pos := unitrX_pos.
Definition exprVn := exprVn.
Definition exprB := exprB.
Definition invr_signM := invr_signM.
Definition divr_signM := divr_signM.
Definition rpredVr := @rpredVr.
Definition rpredV := rpredV.
Definition rpred_div := rpred_div.
Definition rpredXN := rpredXN.
Definition rpredZeq := rpredZeq.
Definition pchar_lalg := pchar_lalg.
#[deprecated(since="mathcomp 2.4.0", use=pchar_lalg)]
Definition char_lalg := pchar_lalg.
Definition rpredMr := rpredMr.
Definition rpredMl := rpredMl.
Definition rpred_divr := rpred_divr.
Definition rpred_divl := rpred_divl.
Definition divringClosedP := divringClosedP.
Definition eq_eval := eq_eval.
Definition eval_tsubst := eval_tsubst.
Definition eq_holds := eq_holds.
Definition holds_fsubst := holds_fsubst.
Definition unitrM := unitrM.
Definition unitr_prodP := unitr_prodP.
Definition prodrV := prodrV.
Definition unitrPr {R x} := @unitrPr R x.
Definition expr_div_n := expr_div_n.
Definition mulr1_eq := mulr1_eq.
Definition divr1_eq := divr1_eq.
Definition divKr := divKr.
Definition mulf_eq0 := mulf_eq0.
Definition prodf_eq0 := prodf_eq0.
Definition prodf_seq_eq0 := prodf_seq_eq0.
Definition mulf_neq0 := mulf_neq0.
Definition prodf_neq0 := prodf_neq0.
Definition prodf_seq_neq0 := prodf_seq_neq0.
Definition expf_eq0 := expf_eq0.
Definition sqrf_eq0 := sqrf_eq0.
Definition expf_neq0 := expf_neq0.
Definition natf_neq0_pchar := natf_neq0_pchar.
#[deprecated(since="mathcomp 2.4.0", use=natf_neq0_pchar)]
Definition natf_neq0 := natf_neq0_pchar.
Definition natf0_pchar := natf0_pchar.
#[deprecated(since="mathcomp 2.4.0", use=natf0_pchar)]
Definition natf0_char := natf0_pchar.
Definition pcharf'_nat := pcharf'_nat.
#[deprecated(since="mathcomp 2.4.0", use=pcharf'_nat)]
Definition charf'_nat := pcharf'_nat.
Definition pcharf0P := pcharf0P.
#[deprecated(since="mathcomp 2.4.0", use=pcharf0P)]
Definition charf0P := pcharf0P.
Definition eqf_sqr := eqf_sqr.
Definition mulfI := mulfI.
Definition mulIf := mulIf.
Definition divfI := divfI.
Definition divIf := divIf.
Definition sqrf_eq1 := sqrf_eq1.
Definition expfS_eq1 := expfS_eq1.
Definition fieldP := @fieldP.
Definition unitfE := unitfE.
Definition mulVf := mulVf.
Definition mulfV := mulfV.
Definition divff := divff.
Definition mulKf := mulKf.
Definition mulVKf := mulVKf.
Definition mulfK := mulfK.
Definition mulfVK := mulfVK.
Definition divfK := divfK.
Definition divKf := divKf.
Definition invfM := invfM.
Definition invf_div := invf_div.
Definition expfB_cond := expfB_cond.
Definition expfB := expfB.
Definition prodfV := prodfV.
Definition prodf_div := prodf_div.
Definition telescope_prodf := telescope_prodf.
Definition telescope_prodf_eq := @telescope_prodf_eq.
Arguments telescope_prodf_eq {F n m} f u.
Definition addf_div := addf_div.
Definition mulf_div := mulf_div.
Definition eqr_div := eqr_div.
Definition eqr_sum_div := eqr_sum_div.
Definition pchar0_natf_div := pchar0_natf_div.
#[deprecated(since="mathcomp 2.4.0", use=pchar0_natf_div)]
Definition char0_natf_div := pchar0_natf_div.
Definition fpredMr := fpredMr.
Definition fpredMl := fpredMl.
Definition fpred_divr := fpred_divr.
Definition fpred_divl := fpred_divl.
Definition satP {F e f} := @satP F e f.
Definition eq_sat := eq_sat.
Definition solP {F n f} := @solP F n f.
Definition eq_sol := eq_sol.
Definition size_sol := size_sol.
Definition solve_monicpoly := @solve_monicpoly.
Definition rmorph_unit := rmorph_unit.
Definition rmorphV := rmorphV.
Definition rmorph_div := rmorph_div.
Definition fmorph_eq0 := fmorph_eq0.
Definition fmorph_inj := @fmorph_inj.
Arguments fmorph_inj {F R} f [x1 x2].
Definition fmorph_eq := fmorph_eq.
Definition fmorph_eq1 := fmorph_eq1.
Definition fmorph_pchar := fmorph_pchar.
#[deprecated(since="mathcomp 2.4.0", use=fmorph_pchar)]
Definition fmorph_char := fmorph_pchar.
Definition fmorph_unit := fmorph_unit.
Definition fmorphV := fmorphV.
Definition fmorph_div := fmorph_div.
Definition scaler_eq0 := scaler_eq0.
Definition scalerK := scalerK.
Definition scalerKV := scalerKV.
Definition scalerI := scalerI.
Definition scaler_injl := scaler_injl.
Definition scaler_unit := scaler_unit.
Definition invrZ := invrZ.
Definition imaginary_exists := imaginary_exists.

End Theory.

Module AllExports. HB.reexport. End AllExports.

End GRing.

Export AllExports.
Export ClosedExports.

Notation "x ^-1" := (inv x) : ring_scope.
Notation "x ^- n" := (inv (x ^+ n)) : ring_scope.
Notation "x / y" := (mul x y^-1) : ring_scope.

Bind Scope term_scope with term.
Bind Scope term_scope with formula.

Notation "''X_' i" := (Var _ i) : term_scope.
Notation "n %:R" := (NatConst _ n) : term_scope.
Notation "0" := 0%:R%T : term_scope.
Notation "1" := 1%:R%T : term_scope.
Notation "x %:T" := (Const x) : term_scope.
Infix "+" := Add : term_scope.
Notation "- t" := (Opp t) : term_scope.
Notation "t - u" := (Add t (- u)) : term_scope.
Infix "*" := Mul : term_scope.
Infix "*+" := NatMul : term_scope.
Notation "t ^-1" := (Inv t) : term_scope.
Notation "t / u" := (Mul t u^-1) : term_scope.
Infix "^+" := Exp : term_scope.
Infix "==" := Equal : term_scope.
Notation "x != y" := (GRing.Not (x == y)) : term_scope.
Infix "/\" := And : term_scope.
Infix "\/" := Or : term_scope.
Infix "==>" := Implies : term_scope.
Notation "~ f" := (Not f) : term_scope.
Notation "''exists' ''X_' i , f" := (Exists i f) : term_scope.
Notation "''forall' ''X_' i , f" := (Forall i f) : term_scope.

Section PairUnitRing.

Variables R1 R2 : unitRingType.

Definition pair_unitr :=
  [qualify a x : R1 * R2 | (x.1 \is a GRing.unit) && (x.2 \is a GRing.unit)].
Definition pair_invr x :=
  if x \is a pair_unitr then (x.1^-1, x.2^-1) else x.

Lemma pair_mulVl : {in pair_unitr, left_inverse 1 pair_invr *%R}.
Proof.
rewrite /pair_invr=> x; case: ifP => // /andP[Ux1 Ux2] _.
by congr (_, _); apply: mulVr.
Qed.

Lemma pair_mulVr : {in pair_unitr, right_inverse 1 pair_invr *%R}.
Proof.
rewrite /pair_invr=> x; case: ifP => // /andP[Ux1 Ux2] _.
by congr (_, _); apply: mulrV.
Qed.

Lemma pair_unitP x y : y * x = 1 /\ x * y = 1 -> x \is a pair_unitr.
Proof.
case=> [[y1x y2x] [x1y x2y]]; apply/andP.
by split; apply/unitrP; [exists y.1 | exists y.2].
Qed.

Lemma pair_invr_out : {in [predC pair_unitr], pair_invr =1 id}.
Proof. by rewrite /pair_invr => x /negPf/= ->. Qed.

#[export]
HB.instance Definition _ := NzRing_hasMulInverse.Build (R1 * R2)%type
  pair_mulVl pair_mulVr pair_unitP pair_invr_out.

End PairUnitRing.

(* TODO: HB.saturate *)
#[export]
HB.instance Definition _ (R1 R2 : comUnitRingType) :=
  UnitRing.on (R1 * R2)%type.
#[export]
HB.instance Definition _ (R : nzRingType) (A1 A2 : unitAlgType R) :=
  NzAlgebra.on (A1 * A2)%type.
#[export]
HB.instance Definition _ (R : nzRingType) (A1 A2 : comUnitAlgType R) :=
  NzAlgebra.on (A1 * A2)%type.
(* /TODO *)

(* begin hide *)

(* Testing subtype hierarchy
Section Test1.

Variables (R : unitRingType) (S : divringClosed R).

HB.instance Definition _ := [SubChoice_isSubUnitRing of B S by <:].

End Test1.

Section Test2.

Variables (R : comUnitRingType) (A : unitAlgType R) (S : divalgClosed A).

HB.instance Definition _ := [SubZmodule_isSubLmodule of B S by <:].
HB.instance Definition _ := [SubNzRing_SubLmodule_isSubLalgebra of B S by <:].
HB.instance Definition _ := [SubLalgebra_isSubAlgebra of B S by <:].

End Test2.

Section Test3.

Variables (F : fieldType) (S : divringClosed F).

HB.instance Definition _ := [SubRing_isSubComNzRing of B S by <:].
HB.instance Definition _ := [SubComUnitRing_isSubIntegralDomain of B S by <:].
HB.instance Definition _ := [SubIntegralDomain_isSubField of B S by <:].

End Test3.
*)

(* end hide *)

(* Algebraic structure of bool *)

Fact mulVb (b : bool) : b != 0 -> b * b = 1.
Proof. by case: b. Qed.

Fact invb_out (x y : bool) : y * x = 1 -> x != 0.
Proof. by case: x; case: y. Qed.

HB.instance Definition _ := ComNzRing_hasMulInverse.Build bool
  mulVb invb_out (fun x => fun => erefl x).

Lemma bool_fieldP : Field.axiom bool. Proof. by []. Qed.

HB.instance Definition _ := ComUnitRing_isField.Build bool bool_fieldP.

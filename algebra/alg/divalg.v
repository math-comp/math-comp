(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div.
From mathcomp Require Import choice fintype bigop prime nmodule algebra.

(******************************************************************************)
(*              Ring-like structures with multiplicative inverse              *)
(*                                                                            *)
(* NB: See CONTRIBUTING.md for an introduction to HB concepts and commands.   *)
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
(*  * UnitAlgebra (algebra with computable inverses):                         *)
(*        divalg_closed S <-> collective predicate S is closed under all      *)
(*                           unitAlgType operations (1, a *: u + v and u / v  *)
(*                           are in S fo u, v in S)                           *)
(*                                                                            *)
(* See algebra.v for general remarks about the module layout, the notation    *)
(* scopes, and the naming convention for lemmas.                              *)
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
Proof. by move/subnK=> {2}<- Ux; rewrite powrDn mulrK ?unitrX. Qed.

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
Proof. by rewrite powMrn exprVn. Qed.

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
move/subnK=> <-; rewrite addnA addnK !powrDn.
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

Arguments fmorph_inj {F R} f [x1 x2].
Arguments telescope_prodf_eq {F n m} f u.

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
Definition rpredMr := rpredMr.
Definition rpredMl := rpredMl.
Definition rpred_divr := rpred_divr.
Definition rpred_divl := rpred_divl.
Definition divringClosedP := divringClosedP.
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
Definition natf0_pchar := natf0_pchar.
Definition pcharf'_nat := pcharf'_nat.
Definition pcharf0P := pcharf0P.
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
Definition fpredMr := fpredMr.
Definition fpredMl := fpredMl.
Definition fpred_divr := fpred_divr.
Definition fpred_divl := fpred_divl.
Definition rmorph_unit := rmorph_unit.
Definition rmorphV := rmorphV.
Definition rmorph_div := rmorph_div.
Definition fmorph_eq0 := fmorph_eq0.
Definition fmorph_inj := @fmorph_inj.
Arguments fmorph_inj {F R} f [x1 x2].
Definition fmorph_eq := fmorph_eq.
Definition fmorph_eq1 := fmorph_eq1.
Definition fmorph_pchar := fmorph_pchar.
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

End Theory.

Module AllExports. HB.reexport. End AllExports.

End GRing.

Export AllExports.
Export ClosedExports.

Notation "x ^-1" := (inv x) : ring_scope.
Notation "x ^- n" := (inv (x ^+ n)) : ring_scope.
Notation "x / y" := (mul x y^-1) : ring_scope.

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

(* Algebraic structure of bool *)

Fact mulVb (b : bool) : b != 0 -> b * b = 1.
Proof. by case: b. Qed.

Fact invb_out (x y : bool) : y * x = 1 -> x != 0.
Proof. by case: x; case: y. Qed.

HB.instance Definition _ := ComNzRing_hasMulInverse.Build bool
  mulVb invb_out (fun x => fun => erefl x).

Lemma bool_fieldP : Field.axiom bool. Proof. by []. Qed.

HB.instance Definition _ := ComUnitRing_isField.Build bool bool_fieldP.

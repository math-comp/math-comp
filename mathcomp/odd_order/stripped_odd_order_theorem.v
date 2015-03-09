(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Prelude ssreflect ssrbool ssrfun eqtype ssrnat fintype finset fingroup.
Require morphism quotient action gfunctor gproduct commutator gseries nilpotent.
Require PFsection14.

(******************************************************************************)
(* This file contains a minimal, self-contained reformulation of the Odd      *)
(* Order theorem, using only the bare Coq logic, and avoiding any use of      *)
(* extra-logical features such as notation, coercion or implicit arguments.   *)
(* This stripped theorem would hardly be usable, however; it just provides    *)
(* evidence for the sceptics.                                                 *)
(******************************************************************************)

(* Equivalence and equality *)

Inductive equivalent P Q := Equivalent (P_to_Q : P -> Q) (Q_to_P : Q -> P).

Inductive equal T (x : T) : T -> Type := Equal : equal T x x.

(* Arithmetic *)

Inductive natural := Zero | Add_1_to (n : natural).

Fixpoint add (m n : natural) : natural :=
  match m with Zero => n | Add_1_to m_minus_1 => add m_minus_1 (Add_1_to n) end.

Definition double (n : natural) : natural := add n n.

Inductive odd (n : natural) :=
  Odd (half : natural)
    (n_odd : equal natural n (Add_1_to (double half))).

Inductive less_than (m n : natural) :=
  LessThan (diff : natural)
    (m_lt_n : equal natural n (Add_1_to (add m diff))).

(* Finite subsets *)

Definition injective_in T R (D : T -> Type) (f : T -> R) :=
  forall x y, D x -> D y -> equal R (f x) (f y) -> equal T x y.

Inductive in_image T R (D : T -> Type) (f : T -> R) (a : R) :=
  InImage (x : T) (x_in_D : D x) (a_is_fx : equal R a (f x)).

Inductive finite_of_order T (D : T -> Type) (n : natural) :=
  FiniteOfOrder (rank : T -> natural)
    (rank_injective : injective_in T natural D rank)
    (rank_onto :
       forall i, equivalent (less_than i n) (in_image T natural D rank i)).

(* Elementary group theory *)

Inductive group_axioms T (mul : T -> T -> T) (one : T) (inv : T -> T) :=
  GroupAxioms
    (associativity : forall x y z, equal T (mul x (mul y z)) (mul (mul x y) z))
    (left_identity : forall x,     equal T (mul one x) x)
    (left_inverse  : forall x,     equal T (mul (inv x) x) one).

Inductive group T mul one inv (G : T -> Type) :=
  Group
    (G_closed_under_mul : forall x y, G x -> G y -> G (mul x y))
    (one_in_G           : G one)
    (G_closed_under_inv : forall x, G x -> G (inv x)).

Inductive subgroup T mul one inv (H G : T -> Type) :=
  Subgroup
    (H_group    : group T mul one inv H)
    (H_subset_G : forall x, H x -> G x).

Inductive normal_subgroup T mul one inv (H G : T -> Type) :=
  NormalSubgroup
    (H_subgroup_G     : subgroup T mul one inv H G)
    (H_is_G_invariant : forall x y, H x -> G y -> H (mul (inv y) (mul x y))).

Inductive commute_mod T mul (x y : T) (H : T -> Type) :=
  CommuteMod (z : T)
    (z_in_H    : H z)
    (xy_eq_zyx : equal T (mul x y) (mul z (mul y x))).

Inductive abelian_factor T mul one inv (G H : T -> Type) :=
  AbelianFactor
    (G_group        : group T mul one inv G)
    (H_normal_in_G  : normal_subgroup T mul one inv H G)
    (G_on_H_abelian : forall x y, G x -> G y -> commute_mod T mul x y H).

Inductive solvable_group T mul one inv (G : T -> Type) :=
| TrivialGroupSolvable
   (G_trivial : forall x, equivalent (G x) (equal T x one))
| AbelianExtensionSolvable (H : T -> Type)
   (H_solvable     : solvable_group T mul one inv H)
   (G_on_H_abelian : abelian_factor T mul one inv G H).

(* begin hide *)
Module InternalSkepticOddOrderProof.

Local Notation Aeq := (equal _).
Local Notation Aadd := add.
Local Notation Adouble := double.
Local Notation Aodd := odd.
Local Notation Alt := less_than.
Local Notation Agroup := group.
Local Notation Asubgroup := subgroup.
Local Notation Anormal := normal_subgroup.
Local Notation Aabel_quo := abelian_factor.
Local Notation Asol := solvable_group.

Import Prelude ssreflect ssrbool ssrfun eqtype ssrnat fintype finset fingroup.
Import morphism quotient action gfunctor gproduct commutator gseries nilpotent.
Import GroupScope.

Lemma main T mul one inv G nn :
    group_axioms T mul one inv -> Agroup T mul one inv G ->
    finite_of_order T G nn -> Aodd nn ->
  Asol T mul one inv G.
Proof.
pose fix natN n := if n is n1.+1 then Add_1_to (natN n1) else Zero.
pose fix Nnat mm := if mm is Add_1_to mm1 then (Nnat mm1).+1 else 0.
have natN_K: cancel natN Nnat by elim=> //= n ->.
have NnatK: cancel Nnat natN by elim=> //= mm ->.
have AaddE nn1 nn2: Nnat (Aadd nn1 nn2) = Nnat nn1 + Nnat nn2.
  by elim: nn1 nn2 => //= nn1 IHnn nn2; rewrite IHnn addnS.
have AltE m n: Alt (natN m) (natN n) -> m < n.
  by rewrite -{2}[n]natN_K => [[dd ->]]; rewrite /= ltnS AaddE natN_K leq_addr.
have AltI m n: m < n -> Alt (natN m) (natN n).
  move/subnKC <-; exists (natN (n - m.+1)).
  by rewrite -[Add_1_to _]NnatK /= AaddE !natN_K.
have AoddE n: Aodd (natN n) -> odd n.
  by rewrite -{2}[n]natN_K => [[hh ->]]; rewrite /= AaddE addnn odd_double.
case=> mulA mul1T mulVT [mulG oneG invG] [rG inj_rG im_rG] odd_nn.
pose n := Nnat nn; have{odd_nn} odd_n: odd n by rewrite AoddE ?NnatK.
have{rG inj_rG im_rG} [gT o_gT [f [g Gf [fK gK]] [fM f1 fV]]]:
  {gT : finGroupType & #|gT| = n & {f : gT -> T
    & {g : _ & forall a, G (f a) & cancel f g /\ forall x, G x -> f (g x) = x}
      & [/\ {morph f : a b / a * b >-> mul a b}, f 1 = one
          & {morph f : a / a^-1 >-> inv a}]}}.
- pose gT := 'I_n.-1.+1; pose g x : gT := inord (Nnat (rG x)).
  have ub_rG x: G x -> Nnat (rG x) < n.
    move=> Gx; rewrite AltE ?NnatK //.
    by have [_] := im_rG (rG x); apply; exists x.
  have Dn: n.-1.+1 = n := ltn_predK (ub_rG one oneG).
  have fP a: {x : T & G x * (g x = a)}%type.
    have a_lt_n: Alt (natN a) nn by rewrite -(canLR NnatK Dn); apply: AltI.
    have [/(_ a_lt_n)[x Gx rGx] _] := im_rG (natN a).
    by exists x; split; rewrite // /g -rGx natN_K inord_val.
  pose f a := tag (fP a); have Gf a: G (f a) by rewrite /f; case: (fP) => x [].
  have fK: cancel f g by rewrite /f => a; case: (fP a) => x [].
  have Ng x & G x: natN (g x) = rG x by rewrite inordK ?Dn ?ub_rG ?NnatK.
  have{Ng} gK x: G x -> f (g x) = x.
    by move=> Gx; rewrite (inj_rG (f (g x)) x) // -!Ng ?fK.
  pose m a b := g (mul (f a) (f b)).
  pose o := g one; pose v a := g (inv (f a)).
  have fM: {morph f: a b / m a b >-> mul a b} by move=> a b; apply/gK/mulG.
  have f1: f o = one by apply: gK.
  have fV: {morph f: a / v a >-> inv a} by move=> a; apply/gK/invG.
  have mA: associative m by move=> a b c; apply: canLR fK _; rewrite !fM mulA.
  have m1: left_id o m by move=> a; apply: canLR fK _; rewrite f1 mul1T.
  have mV: left_inverse o v m.
    by move=> a; apply: canLR fK _; rewrite fV f1 mulVT.
  pose bT := BaseFinGroupType _ (FinGroup.Mixin mA m1 mV).
  exists (@FinGroupType bT mV); first by rewrite card_ord Dn.
  by exists f; first exists g.
pose im (H : {group gT}) x := (G x * (g x \in H))%type.
have imG H : Agroup T mul one inv (im H).
  split=> [x y [Gx Hx] [Gy Hy] | | x [Gx Hx]]; first 1 last.
  - by split; rewrite // -(canRL fK f1).
  - by split; [auto | rewrite -(gK x Gx) -fV fK groupV].
  by split; [auto | rewrite -(gK x Gx) -(gK y Gy) -fM fK groupM].
pose G0 := [set: gT]%G.
have sGG0 x: G x -> im G0 x by split; rewrite ?inE.
have mulVV1 x: mul (inv (inv x)) one = x by rewrite -(mulVT x) mulA mulVT mul1T.
have{mulVV1} mulT1 x: mul x one = x by rewrite -[x]mulVV1 -mulA mul1T.
pose comm x y := mul (mul x y) (inv (mul y x)).
suffices solH: Asol T mul one inv (im G0).
  right with (im G0) => //; split=> // [|x y Gx Gy].
    by split=> // [|x y [Gx _] Gy]; [split=> // x [] | apply: sGG0; auto].
  by exists (comm x y); [rewrite /comm; auto | rewrite -mulA mulVT -mulA mulT1].
have solG0: solvable G0 by rewrite PFsection14.Feit_Thompson ?cardsT ?o_gT.
elim: _.+1 {-2}G0 (ltnSn #|G0|) => // m IHm H; rewrite ltnS => leHm.
have [-> | ntH] := eqVneq H 1%G.
  left=> // x; split=> [[Gx /set1P] | ->].
    by rewrite -f1 => <-; rewrite gK.
  by split; rewrite // -f1 fK.
have ltH'H: H^`(1) \proper H := sol_der1_proper solG0 (subsetT H) ntH.
right with (im H^`(1)%G); first exact: IHm (leq_trans (proper_card _) leHm).
have /andP[/subsetP sH'H /subsetP nH'H]: H^`(1) <| H := der_normal 1 H.
split=> // [|x y [Gx Hx] [Gy Hy]].
  split=> // [|x y [Gx H'x] [Gy Hy]]; first by split=> // x [Gx /sH'H].
  split; first by [auto]; rewrite -(gK x Gx) -(gK y Gy) -!(fM, fV) !fK.
  by rewrite memJ_norm ?nH'H.
exists (comm x y); last by rewrite -mulA mulVT -mulA mulT1.
rewrite /comm; split; first by [auto]; rewrite -(gK x Gx) -(gK y Gy).
by rewrite -!(fM, fV) fK -[g x * g y]invgK !invMg -mulgA mem_commg ?groupV.
Qed.

End InternalSkepticOddOrderProof.
(* end hide *)

(* The Odd Order theorem *)

Theorem stripped_Odd_Order T mul one inv (G : T -> Type) (n : natural) :
    group_axioms T mul one inv -> group T mul one inv G ->
    finite_of_order T G n -> odd n ->
  solvable_group T mul one inv G.
Proof. exact (InternalSkepticOddOrderProof.main T mul one inv G n). Qed.

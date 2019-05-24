Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype tuple.
From mathcomp
Require Import bigop binomial finset finfun ssralg countalg finalg poly polydiv.
From mathcomp
Require Import perm fingroup matrix mxalgebra mxpoly vector countalg.

(*****************************************************************************)
(* This file defines polynomials of bounded size, gives it a structure       *)
(* of choice, finite and countable ring, ..., and lmodule, when possible.    *)
(* Internally, the construction uses poly_rV and rVpoly, but they should not *)
(* be exposed.                                                               *)
(* We provide two bases: the 'X^i and the lagrange polynomials.              *)
(*     {poly_n R} == the type of polynomial of size at most n                *)
(* irreducibleb p == boolean decision procedure for irreducibility           *)
(*                   of a bounded size polynomial over a finite idomain      *)
(* Considering {poly_n F} over a field F, it is a vectType and               *)
(*          'Xn^i == 'X^i as an element of {poly_n R}                        *)
(*         polynX == [tuple 'X^0, ..., 'X^(n - 1)], basis of {poly_n R}      *)
(*    x.-lagrange == lagrange basis of {poly_n R} wrt x : nat -> F           *)
(* x.-lagrange_ i == the ith lagrange polynomial wrt the sampling points x   *)
(*****************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Import FinRing.Theory.
Import Pdiv.Field.
Local Open Scope ring_scope.

Section poly_of_size_zmod.
Context {R : ringType}.
Implicit Types (phR : phant R) (n : nat).

Section poly_of_size.
Variable (n : nat).

Definition poly_of_size :=
  [qualify a p | size (p : {poly R}) <= n].
Fact poly_of_size_key : pred_key poly_of_size. Proof. by []. Qed.
Canonical poly_of_size_keyd := KeyedQualifier poly_of_size_key.

Lemma npoly_submod_closed : submod_closed poly_of_size.
Proof.
split=> [|x p q sp sq]; rewrite qualifE ?size_polyC ?eqxx//.
rewrite (leq_trans (size_add _ _)) // geq_max.
by rewrite (leq_trans (size_scale_leq _ _)).
Qed.

Canonical npoly_opprPred := OpprPred npoly_submod_closed.
Canonical npoly_addrPred := AddrPred npoly_submod_closed.
Canonical npoly_zmodPred := ZmodPred npoly_submod_closed.
Canonical npoly_submodPred := SubmodPred npoly_submod_closed.

End poly_of_size.

Section npoly.

Record npoly_of phR n : predArgType := NPoly_of {
  polyn :> {poly R};
  _ : polyn \is a poly_of_size n
}.

Variable (n : nat).

Local Notation npolyR := (@npoly_of (Phant R) n).

Canonical npoly_subType := [subType for @polyn (Phant R) n].

Lemma npoly_is_a_poly_of_size (p : npolyR) : val p \is a poly_of_size n.
Proof. by case: p. Qed.
Hint Resolve npoly_is_a_poly_of_size.

Lemma size_npoly (p : npolyR) : size p <= n.
Proof. exact: npoly_is_a_poly_of_size. Qed.
Hint Resolve size_npoly.

Definition npoly_eqMixin := [eqMixin of npolyR by <:].
Canonical npoly_eqType := EqType npolyR npoly_eqMixin.
Definition npoly_choiceMixin := [choiceMixin of npolyR by <:].
Canonical npoly_choiceType := ChoiceType npolyR npoly_choiceMixin.
Definition npoly_zmodMixin := [zmodMixin of npolyR by <:].
Canonical npoly_zmodType := ZmodType npolyR npoly_zmodMixin.
Definition npoly_lmodMixin := [lmodMixin of npolyR by <:].
Canonical npoly_lmodType := LmodType R npolyR npoly_lmodMixin.

Definition npoly_rV : npolyR -> 'rV[R]_n := poly_rV \o val.
Definition rVnpoly : 'rV[R]_n -> npolyR := insubd (0 : npolyR) \o rVpoly.
Arguments rVnpoly /.
Arguments npoly_rV /.

Lemma npoly_rV_K : cancel npoly_rV rVnpoly.
Proof.
move=> p /=; apply/val_inj.
by rewrite val_insubd [_ \is a _]size_poly ?poly_rV_K.
Qed.
Lemma rVnpolyK : cancel rVnpoly npoly_rV.
Proof. by move=> p /=; rewrite val_insubd [_ \is a _]size_poly rVpolyK. Qed.
Hint Resolve npoly_rV_K rVnpolyK.

Lemma npoly_vect_axiom : Vector.axiom n npolyR.
Proof. by exists npoly_rV; [move=> ???; exact: linearP|exists rVnpoly]. Qed.

Definition npoly_vect_mixin := VectMixin npoly_vect_axiom.
Canonical npoly_vect_type := VectType R npolyR npoly_vect_mixin.

End npoly.
End poly_of_size_zmod.

Notation "'{poly_' n R }" := (npoly_of (Phant R) n)
  (at level 0, n at level 1, format "'{poly_' n  R }").
Notation NPoly := (NPoly_of (Phant _)).
Hint Resolve size_npoly npoly_is_a_poly_of_size.

Definition npoly_countMixin (R : countRingType) n :=
  [countMixin of {poly_n R} by <:].
Canonical npoly_countType (R : countRingType) n :=
  CountType {poly_n R} (@npoly_countMixin R n).
Canonical npoly_subCountType (R : countRingType) n :=
  [subCountType of {poly_n R}].

Section npoly_fin.
Variable (R : finRingType) (n : nat).

Definition npoly_finMixin (R : finRingType) (n : nat) :=
  CanFinMixin (@npoly_rV_K [ringType of R] n).
Canonical npoly_finType (R : finRingType) n :=
  FinType {poly_n R} (@npoly_finMixin R n).
Canonical npoly_subFinType := [subFinType of {poly_n R}].
End npoly_fin.

Section npoly_theory.
Context (R : ringType) {n : nat}.

Lemma polyn_is_linear : linear (@polyn _ _ _ : {poly_n R} -> _).
Proof. by []. Qed.
Canonical polyn_additive := Additive polyn_is_linear.
Canonical polyn_linear := Linear polyn_is_linear.

Canonical npoly (E : nat -> R) : {poly_n R} :=
   @NPoly_of _ (Phant R) _ (\poly_(i < n) E i) (size_poly _ _).

Fact size_npoly0 : size (0 : {poly R}) <= n.
Proof. by rewrite size_poly0. Qed.

Definition npoly0 := NPoly (size_npoly0).

Fact npolyp_key : unit. Proof. exact: tt. Qed.
Definition npolyp : {poly R} -> {poly_n R} :=
  locked_with npolyp_key (npoly \o (nth 0)).

Definition npoly_of_seq := npolyp \o Poly.

Lemma npolyP (p q : {poly_n R}) : nth 0 p =1 nth 0 q <-> p = q.
Proof. by split => [/polyP/val_inj|->]. Qed.

Lemma coef_npolyp (p : {poly R}) i : (npolyp p)`_i = if i < n then p`_i else 0.
Proof. by rewrite /npolyp unlock /= coef_poly. Qed.

Lemma big_coef_npoly (p : {poly_n R}) i : n <= i -> p`_i = 0.
Proof.
by move=> i_big; rewrite nth_default // (leq_trans _ i_big) ?size_npoly.
Qed.

Lemma npolypK (p : {poly R}) : size p <= n -> npolyp p = p :> {poly R}.
Proof.
move=> spn; apply/polyP=> i; rewrite coef_npolyp.
by have [i_big|i_small] // := ltnP; rewrite nth_default ?(leq_trans spn).
Qed.

Lemma coefn_sum (I : Type) (r : seq I) (P : pred I)
  (F : I -> {poly_n R}) (k : nat) :
  (\sum_(i <- r | P i) F i)`_k = \sum_(i <- r | P i) (F i)`_k.
Proof. by rewrite !raddf_sum //= coef_sum. Qed.

End npoly_theory.
Arguments npoly {R} n E.
Arguments npolyp {R} n p.

Section fin_npoly.

Variable R : finRingType.
Variable n : nat.
Implicit Types p q : {poly_n R}.

Definition npoly_enum : seq {poly_n R} :=
  if n isn't n.+1 then [:: npoly0 _] else
  pmap insub [seq \poly_(i < n.+1) c (inord i) | c : (R ^ n.+1)%type].

Lemma npoly_enum_uniq : uniq npoly_enum.
Proof.
rewrite /npoly_enum; case: n=> [|k] //.
rewrite pmap_sub_uniq // map_inj_uniq => [|f g eqfg]; rewrite ?enum_uniq //.
apply/ffunP => /= i; have /(congr1 (fun p : {poly _} => p`_i)) := eqfg.
by rewrite !coef_poly ltn_ord inord_val.
Qed.

Lemma mem_npoly_enum p : p \in npoly_enum.
Proof.
rewrite /npoly_enum; case: n => [|k] // in p *.
  by case: p => [p sp] /=; rewrite in_cons -val_eqE /= -size_poly_leq0 [size _ <= _]sp.
rewrite mem_pmap_sub; apply/mapP.
eexists [ffun i : 'I__ => p`_i]; first by rewrite mem_enum.
apply/polyP => i; rewrite coef_poly.
have [i_small|i_big] := ltnP; first by rewrite ffunE /= inordK.
by rewrite nth_default // 1?(leq_trans _ i_big) // size_npoly.
Qed.

Lemma card_npoly : #|{poly_n R}| = (#|R| ^ n)%N.
Proof.
rewrite -(card_imset _ (can_inj (@npoly_rV_K _ _))) eq_cardT.
  by rewrite -cardT /= card_matrix mul1n.
by move=> v; apply/imsetP; exists (rVnpoly v); rewrite ?rVnpolyK //.
Qed.

End fin_npoly.

Section Irreducible.

Variable R : finIdomainType.
Variable p : {poly R}.

Definition irreducibleb :=
  ((1 < size p) &&
  [forall q : {poly_((size p).-1) R},
    (Pdiv.Ring.rdvdp q p)%R ==> (size q <= 1)])%N.

Lemma irreducibleP : reflect (irreducible_poly p) irreducibleb.
Proof.
rewrite /irreducibleb /irreducible_poly.
apply: (iffP idP) => [/andP[sp /'forall_implyP /= Fp]|[sp Fpoly]].
  have sp_gt0 : size p > 0 by case: size sp.
  have p_neq0 : p != 0 by rewrite -size_poly_eq0; case: size sp.
  split => // q sq_neq1 dvd_qp; rewrite -dvdp_size_eqp // eqn_leq dvdp_leq //=.
  apply: contraNT sq_neq1; rewrite -ltnNge => sq_lt_sp.
  have q_small: (size q <= (size p).-1)%N by rewrite -ltnS prednK.
  rewrite Pdiv.Idomain.dvdpE in dvd_qp.
  have /= := Fp (NPoly q_small) dvd_qp.
  rewrite leq_eqVlt ltnS => /orP[//|]; rewrite size_poly_leq0 => /eqP q_eq0.
  by rewrite -Pdiv.Idomain.dvdpE q_eq0 dvd0p (negPf p_neq0) in dvd_qp.
have sp_gt0 : size p > 0 by case: size sp.
rewrite sp /=; apply/'forall_implyP => /= q; rewrite -Pdiv.Idomain.dvdpE=> dvd_qp.
have [/eqP->//|/Fpoly/(_ dvd_qp)/eqp_size sq_eq_sp] := boolP (size q == 1%N).
by have := size_npoly q; rewrite sq_eq_sp -ltnS prednK ?ltnn.
Qed.

End Irreducible.

Section Vspace.

Variable (K : fieldType) (n : nat).

Lemma dim_polyn : \dim (fullv : {vspace {poly_n K}}) = n.
Proof. by rewrite [LHS]mxrank_gen mxrank1. Qed.

Definition npolyX : n.-tuple {poly_n K} := [tuple npolyp n 'X^i | i < n].
Notation "''Xn^' i" := (tnth npolyX i)
  (at level 3, i at level 2, format "''Xn^' i").

Lemma npolyXE (i : 'I_n) : 'Xn^i = 'X^i :> {poly _}.
Proof. by rewrite tnth_map tnth_ord_tuple npolypK // size_polyXn. Qed.

Lemma nth_npolyX (i : 'I_n) : npolyX`_i = 'Xn^i.
Proof. by rewrite -tnth_nth. Qed.

Lemma npolyX_free : free npolyX.
Proof.
apply/freeP=> u /= sum_uX_eq0 i; have /npolyP /(_ i) := sum_uX_eq0.
rewrite (@big_morph _ _ _ 0%R +%R) // coef_sum coef0.
rewrite (bigD1 i) ?big1 /= ?addr0 ?coefZ ?(nth_map 0%N) ?size_iota //.
  by rewrite nth_npolyX npolyXE coefXn eqxx mulr1.
move=> j; rewrite -val_eqE /= => neq_ji.
by rewrite nth_npolyX npolyXE coefZ coefXn eq_sym (negPf neq_ji) mulr0.
Qed.

Lemma npolyX_full : basis_of fullv npolyX.
Proof.
by rewrite basisEfree npolyX_free subvf size_map size_enum_ord dim_polyn /=.
Qed.

Lemma npolyX_coords (p : {poly_n K}) i : coord npolyX i p = p`_i.
Proof.
rewrite [p in RHS](coord_basis npolyX_full) ?memvf // coefn_sum.
rewrite (bigD1 i) //= coefZ nth_npolyX npolyXE coefXn eqxx mulr1 big1 ?addr0//.
move=> j; rewrite -val_eqE => /= neq_ji.
by rewrite coefZ nth_npolyX npolyXE coefXn eq_sym (negPf neq_ji) mulr0.
Qed.

Lemma npolyX_gen (p : {poly K}) : (size p <= n)%N ->
  p = \sum_(i < n) p`_i *: 'Xn^i.
Proof.
move=> sp; rewrite -[p](@npolypK _ n) //.
rewrite [npolyp _ _ in LHS](coord_basis npolyX_full) ?memvf //.
rewrite (@big_morph _ _ _ 0%R +%R) // !raddf_sum.
by apply: eq_bigr=> i _; rewrite npolyX_coords //= nth_npolyX npolyXE.
Qed.

Section lagrange.

Variables (x : nat -> K).

Notation lagrange_def := (fun i :'I_n =>
  let k := i in let p := \prod_(j < n | j != k) ('X - (x j)%:P)
  in (p.[x k]^-1)%:P * p).

Fact lagrange_key : unit. Proof. exact: tt. Qed.

Definition lagrange := locked_with lagrange_key
  [tuple npolyp n (lagrange_def i) | i < n].
Notation lagrange_ := (tnth lagrange).

Hypothesis n_gt0 : (0 < n)%N.
Hypothesis x_inj : injective x.

Let lagrange_def_sample (i j : 'I_n) : (lagrange_def i).[x j] = (i == j)%:R.
Proof using x_inj.
rewrite hornerM hornerC; set p := (\prod_(_ < _ | _) _).
have [<-|neq_ij] /= := altP eqP.
  rewrite mulVf // horner_prod; apply/prodf_neq0 => k neq_ki.
  by rewrite hornerXsubC subr_eq0 inj_eq // eq_sym.
rewrite [X in _ * X]horner_prod (bigD1 j) 1?eq_sym //=.
by rewrite hornerXsubC subrr mul0r mulr0.
Qed.

Let size_lagrange_def i : size (lagrange_def i) = n.
Proof using n_gt0 x_inj.
rewrite size_Cmul; last first.
  suff : (lagrange_def i).[x i] != 0.
    by rewrite hornerE mulf_eq0 => /norP [].
  by rewrite lagrange_def_sample ?eqxx ?oner_eq0.
rewrite size_prod /=; last first.
  by move=> j neq_ji; rewrite polyXsubC_eq0.
rewrite (eq_bigr (fun=> (2 * 1)%N)); last first.
  by move=> j neq_ji; rewrite size_XsubC.
rewrite -big_distrr /= sum1_card cardC1 card_ord /=.
by case: (n) {i} n_gt0 => ?; rewrite mul2n -addnn -addSn addnK.
Qed.

Lemma lagrangeE i : lagrange_ i = lagrange_def i :> {poly _}.
Proof.
rewrite [lagrange]unlock tnth_map.
by rewrite [val _]npolypK tnth_ord_tuple // size_lagrange_def.
Qed.

Lemma nth_lagrange (i : 'I_n) : lagrange`_i = lagrange_ i.
Proof. by rewrite -tnth_nth. Qed.

Lemma size_lagrange_ i : size (lagrange_ i) = n.
Proof. by rewrite lagrangeE size_lagrange_def. Qed.

Lemma size_lagrange : size lagrange = n.
Proof. by rewrite size_tuple. Qed.

Lemma lagrange_sample (i j : 'I_n) : (lagrange_ i).[x j] = (i == j)%:R.
Proof. by rewrite lagrangeE lagrange_def_sample. Qed.

Lemma lagrange_free : free lagrange.
Proof.
apply/freeP=> lambda eq_l i.
have /(congr1 (fun p : {poly__ _} => p.[x i])) := eq_l.
rewrite (@big_morph _ _ _ 0%R +%R) // horner_sum horner0.
rewrite (bigD1 i) // big1 => [|j /= /negPf ji] /=;
by rewrite ?hornerE nth_lagrange lagrange_sample ?eqxx ?ji ?mulr1 ?mulr0.
Qed.

Lemma lagrange_full : basis_of fullv lagrange.
Proof.
by rewrite basisEfree lagrange_free subvf size_lagrange dim_polyn /=.
Qed.

Lemma lagrange_coords (p : {poly_n K}) i : coord lagrange i p = p.[x i].
Proof.
rewrite [p in RHS](coord_basis lagrange_full) ?memvf //.
rewrite (@big_morph _ _ _ 0%R +%R) // horner_sum.
rewrite (bigD1 i) // big1 => [|j /= /negPf ji] /=;
by rewrite ?hornerE nth_lagrange lagrange_sample ?eqxx ?ji ?mulr1 ?mulr0.
Qed.

Lemma lagrange_gen (p : {poly K}) : (size p <= n)%N ->
  p = \sum_(i < n) p.[x i]%:P * lagrange_ i.
Proof.
move=> sp; rewrite -[p](@npolypK _ n) //.
rewrite [npolyp _ _ in LHS](coord_basis lagrange_full) ?memvf //.
rewrite (@big_morph _ _ _ 0%R +%R) //; apply: eq_bigr=> i _.
by rewrite lagrange_coords mul_polyC nth_lagrange.
Qed.

End lagrange.

End Vspace.

Notation "''Xn^' i" := (tnth (npolyX _) i)
  (at level 3, i at level 2, format "''Xn^' i").
Notation "x .-lagrange" := (lagrange x)
  (at level 2, format "x .-lagrange") : ring_scope.
Notation "x .-lagrange_" := (tnth x.-lagrange)
  (at level 2, format "x .-lagrange_") : ring_scope.

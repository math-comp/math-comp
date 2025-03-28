From HB Require Import structures.
From mathcomp
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype tuple.
From mathcomp
Require Import bigop binomial finset finfun ssralg countalg finalg poly polydiv.
From mathcomp
Require Import perm fingroup matrix mxalgebra mxpoly vector countalg.

(******************************************************************************)
(* This file defines the algebras R[X]/<p> and their theory.                  *)
(* It mimics the zmod file for polynomials                                    *)
(* First, it defines polynomials of bounded size (equivalent of 'I_n),        *)
(* gives it a structure of choice, finite and countable ring, ..., and        *)
(* lmodule, when possible.                                                    *)
(* Internally, the construction uses poly_rV and rVpoly, but they should not  *)
(* be exposed.                                                                *)
(* We provide two bases: the 'X^i and the lagrange polynomials.               *)
(*     {poly_n R} == the type of polynomial of size at most n                 *)
(* irreducibleb p == boolean decision procedure for irreducibility            *)
(*                   of a bounded size polynomial over a finite idomain       *)
(* Considering {poly_n F} over a field F, it is a vectType and                *)
(*          'nX^i == 'X^i as an element of {poly_n R}                         *)
(*         polynX == [tuple 'X^0, ..., 'X^(n - 1)], basis of {poly_n R}       *)
(*    x.-lagrange == lagrange basis of {poly_n R} wrt x : nat -> F            *)
(* x.-lagrange_ i == the ith lagrange polynomial wrt the sampling points x    *)
(* Second, it defines polynomials quotiented by a poly (equivalent of 'Z_p),  *)
(* as bounded polynomial. As we are aiming to build a ring structure we need  *)
(* the polynomial to be monic and of size greater than one. If it is not the  *)
(* case we quotient by 'X                                                     *)
(*     mk_monic p == the actual polynomial on which we quotient               *)
(*                   if p is monic and of size > 1 it is p otherwise 'X       *)
(*    {poly %/ p} == defined as {poly_(size (mk_poly p)).-1 R} on which       *)
(*                   there is a ring structure                                *)
(*     in_qpoly q == turn the polynomial q into an element of {poly %/ p} by  *)
(*                   taking a modulo                                          *)
(*            'qX == in_qpoly 'X                                              *)
(* The last part that defines the field structure when the quotient is an     *)
(* irreducible polynomial is defined in field/qfpoly                          *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Import Pdiv.CommonRing.
Import Pdiv.RingMonic.
Import Pdiv.Field.
Import FinRing.Theory.
Local Open Scope ring_scope.

Reserved Notation "'{poly_' n R }"
  (at level 0, n at level 2, format "'{poly_' n  R }").
Reserved Notation "''nX^' i"  (at level 3, i at level 2, format "''nX^' i").
Reserved Notation "x .-lagrange" (at level 2, format "x .-lagrange").
Reserved Notation "x .-lagrange_" (at level 2, format "x .-lagrange_").
Reserved Notation "'qX"  (at level 0).
Reserved Notation "{ 'poly' '%/' p }"
  (at level 0, p at level 2, format "{ 'poly'  '%/'  p }").

Section poly_of_size_zmod.
Context {R : nzRingType}.
Implicit Types (n : nat).

Section poly_of_size.
Variable (n : nat).

Definition poly_of_size_pred := fun p : {poly R} => size p <= n.
Arguments poly_of_size_pred _ /.
Definition poly_of_size := [qualify a p | poly_of_size_pred p].

Lemma npoly_submod_closed : submod_closed poly_of_size.
Proof.
split=> [|x p q sp sq]; rewrite qualifE/= ?size_polyC ?eqxx//.
rewrite (leq_trans (size_polyD _ _)) // geq_max.
by rewrite (leq_trans (size_scale_leq _ _)).
Qed.

HB.instance Definition _ :=
  GRing.isSubmodClosed.Build R {poly R} poly_of_size_pred npoly_submod_closed.

End poly_of_size.

Arguments poly_of_size_pred _ _ /.

Section npoly.

Variable (n : nat).

Record npoly : predArgType := NPoly {
  polyn :> {poly R};
  _ : polyn \is a poly_of_size n
}.

HB.instance Definition _ := [isSub for @polyn].

Lemma npoly_is_a_poly_of_size (p : npoly) : val p \is a poly_of_size n.
Proof. by case: p. Qed.
Hint Resolve npoly_is_a_poly_of_size : core.

Lemma size_npoly (p : npoly) : size p <= n.
Proof. exact: npoly_is_a_poly_of_size. Qed.
Hint Resolve size_npoly : core.

HB.instance Definition _ := [Choice of npoly by <:].
HB.instance Definition _ := [SubChoice_isSubLmodule of npoly by <:].

Definition npoly_rV : npoly -> 'rV[R]_n := poly_rV \o val.
Definition rVnpoly : 'rV[R]_n -> npoly :=
  insubd (0 : npoly) \o rVpoly.
Arguments rVnpoly /.
Arguments npoly_rV /.

Lemma npoly_rV_K : cancel npoly_rV rVnpoly.
Proof.
move=> p /=; apply/val_inj.
by rewrite val_insubd [_ \is a _]size_poly ?poly_rV_K.
Qed.
Lemma rVnpolyK : cancel rVnpoly npoly_rV.
Proof. by move=> p /=; rewrite val_insubd [_ \is a _]size_poly rVpolyK. Qed.
Hint Resolve npoly_rV_K rVnpolyK : core.

Lemma npoly_vect_axiom : Vector.axiom n npoly.
Proof. by exists npoly_rV; [exact:linearPZ | exists rVnpoly]. Qed.

HB.instance Definition _ := Lmodule_hasFinDim.Build R npoly npoly_vect_axiom.

End npoly.
End poly_of_size_zmod.

Arguments npoly {R}%type n%N.

Notation "'{poly_' n R }" := (@npoly R n) : type_scope.

#[global]
Hint Resolve size_npoly npoly_is_a_poly_of_size : core.

Arguments poly_of_size_pred _ _ _ /.
Arguments npoly : clear implicits.

HB.instance Definition _ (R : countNzRingType) n :=
  [Countable of {poly_n R} by <:].

HB.instance Definition _  (R : finNzRingType) n : isFinite {poly_n R} :=
  CanIsFinite (@npoly_rV_K R n).

Section npoly_theory.
Context (R : nzRingType) {n : nat}.

Lemma polyn_is_linear : linear (@polyn _ _ : {poly_n R} -> _).
Proof. by []. Qed.
HB.instance Definition _ :=
  GRing.isLinear.Build R {poly_n R} {poly R} _ (polyn (n:=n)) polyn_is_linear.

Canonical mk_npoly (E : nat -> R) : {poly_n R} :=
  @NPoly R _ (\poly_(i < n) E i) (size_poly _ _).

Fact size_npoly0 : size (0 : {poly R}) <= n.
Proof. by rewrite size_poly0. Qed.

Definition npoly0 := NPoly (size_npoly0).

Fact npolyp_key : unit. Proof. exact: tt. Qed.
Definition npolyp : {poly R} -> {poly_n R} :=
  locked_with npolyp_key (mk_npoly \o (nth 0)).

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
Arguments mk_npoly {R} n E.
Arguments npolyp {R} n p.

Section fin_npoly.

Variable R : finNzRingType.
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
  case: p => [p sp] /=.
  by rewrite in_cons -val_eqE /= -size_poly_leq0 [size _ <= _]sp.
rewrite mem_pmap_sub; apply/mapP.
eexists [ffun i : 'I__ => p`_i]; first by rewrite mem_enum.
apply/polyP => i; rewrite coef_poly.
have [i_small|i_big] := ltnP; first by rewrite ffunE /= inordK.
by rewrite nth_default // 1?(leq_trans _ i_big) // size_npoly.
Qed.

Lemma card_npoly : #|{poly_n R}| = (#|R| ^ n)%N.
Proof.
rewrite -(card_imset _ (can_inj (@npoly_rV_K _ _))) eq_cardT.
  by rewrite -cardT /= card_mx mul1n.
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
rewrite sp /=; apply/'forall_implyP => /= q.
rewrite -Pdiv.Idomain.dvdpE=> dvd_qp.
have [/eqP->//|/Fpoly/(_ dvd_qp)/eqp_size sq_eq_sp] := boolP (size q == 1%N).
by have := size_npoly q; rewrite sq_eq_sp -ltnS prednK ?ltnn.
Qed.

End Irreducible.

Section Vspace.

Variable (K : fieldType) (n : nat).

Lemma dim_polyn : \dim (fullv : {vspace {poly_n K}}) = n.
Proof. by rewrite [LHS]mxrank_gen mxrank1. Qed.

Definition npolyX : n.-tuple {poly_n K} := [tuple npolyp n 'X^i | i < n].
Notation "''nX^' i" := (tnth npolyX i).

Lemma npolyXE (i : 'I_n) : 'nX^i = 'X^i :> {poly _}.
Proof. by rewrite tnth_map tnth_ord_tuple npolypK // size_polyXn. Qed.

Lemma nth_npolyX (i : 'I_n) : npolyX`_i = 'nX^i.
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
  p = \sum_(i < n) p`_i *: 'nX^i.
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
Proof.
clear n_gt0; rewrite hornerM hornerC; set p := (\prod_(_ < _ | _) _).
have [<-|neq_ij] /= := altP eqP.
  rewrite mulVf // horner_prod; apply/prodf_neq0 => k neq_ki.
  by rewrite hornerXsubC subr_eq0 inj_eq // eq_sym.
rewrite [X in _ * X]horner_prod (bigD1 j) 1?eq_sym //=.
by rewrite hornerXsubC subrr mul0r mulr0.
Qed.

Let size_lagrange_def i : size (lagrange_def i) = n.
Proof.
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

Notation "''nX^' i" := (tnth (npolyX _) i) : ring_scope.
Notation "x .-lagrange" := (lagrange x) : ring_scope.
Notation "x .-lagrange_" := (tnth x.-lagrange) : ring_scope.

Section Qpoly.

Variable R : nzRingType.
Variable h : {poly R}.

Definition mk_monic := 
  if (1 < size h)%N && (h \is monic) then h else 'X.

Definition qpoly := {poly_(size mk_monic).-1 R}.
End Qpoly.

Notation "{ 'poly' '%/' p }" := (qpoly p) : type_scope.
 
Section QpolyProp.

Variable R : nzRingType.
Variable h : {poly R}.

Lemma monic_mk_monic : (mk_monic h) \is monic.
Proof.
rewrite /mk_monic; case: leqP=> [_|/=]; first by apply: monicX.
by case E : (h \is monic) => [->//|] => _; apply: monicX.
Qed. 

Lemma size_mk_monic_gt1 : (1 < size (mk_monic h))%N.
Proof. 
by rewrite !fun_if size_polyX; case: leqP => //=; rewrite if_same.
Qed.

Lemma size_mk_monic_gt0 : (0 < size (mk_monic h))%N.
Proof. by rewrite (leq_trans _ size_mk_monic_gt1). Qed.

Lemma mk_monic_neq0 : mk_monic h != 0.
Proof. by rewrite -size_poly_gt0 size_mk_monic_gt0. Qed.

Lemma size_mk_monic (p : {poly %/ h}) : size p < size (mk_monic h).
Proof.
have: (p : {poly R}) \is a poly_of_size (size (mk_monic h)).-1 by case: p.
by rewrite qualifE/= -ltnS prednK // size_mk_monic_gt0.
Qed.

(* standard inject *)
Lemma poly_of_size_mod p :
  rmodp p (mk_monic h) \is a poly_of_size (size (mk_monic h)).-1.
Proof.
rewrite qualifE/= -ltnS prednK ?size_mk_monic_gt0 //.
by apply: ltn_rmodpN0; rewrite mk_monic_neq0.
Qed.

Definition in_qpoly p : {poly %/ h} := NPoly (poly_of_size_mod p).

Lemma in_qpoly_small (p : {poly R}) :
  size p < size (mk_monic h) -> in_qpoly p = p :> {poly R}.
Proof. exact: rmodp_small. Qed.

Lemma in_qpoly0 : in_qpoly 0 = 0.
Proof. by apply/val_eqP; rewrite /= rmod0p. Qed.

Lemma in_qpolyD p q : in_qpoly (p + q) = in_qpoly p + in_qpoly q.
Proof. by apply/val_eqP=> /=; rewrite rmodpD ?monic_mk_monic. Qed.

Lemma in_qpolyZ a p : in_qpoly (a *: p) = a *: in_qpoly p.
Proof. apply/val_eqP=> /=; rewrite rmodpZ ?monic_mk_monic //. Qed.

Fact in_qpoly_is_linear : linear in_qpoly.
Proof. by move=> k p q; rewrite in_qpolyD in_qpolyZ. Qed.

HB.instance Definition _ :=
  GRing.isLinear.Build R {poly R} {poly_(size (mk_monic h)).-1 R} _ in_qpoly
    in_qpoly_is_linear.

Lemma qpolyC_proof k :
  (k%:P : {poly R}) \is a poly_of_size (size (mk_monic h)).-1.
Proof.
rewrite qualifE/= -ltnS size_polyC prednK ?size_mk_monic_gt0 //.
by rewrite (leq_ltn_trans _ size_mk_monic_gt1) //; case: eqP.
Qed.

Definition qpolyC k : {poly %/ h} :=  NPoly (qpolyC_proof k).

Lemma qpolyCE k : qpolyC k = k%:P :> {poly R}.
Proof. by []. Qed.

Lemma qpolyC0 : qpolyC 0 = 0.
Proof. by apply/val_eqP/eqP. Qed.

Definition qpoly1 := qpolyC 1.

Definition qpoly_mul (q1 q2 : {poly %/ h}) : {poly %/ h} :=
  in_qpoly ((q1 : {poly R}) * q2).

Lemma qpoly_mul1z : left_id qpoly1 qpoly_mul.
Proof.
by move=> x; apply: val_inj; rewrite /= mul1r rmodp_small // size_mk_monic.
Qed.

Lemma qpoly_mulz1 : right_id qpoly1 qpoly_mul.
Proof.
by move=> x; apply: val_inj; rewrite /= mulr1 rmodp_small // size_mk_monic.
Qed.

Lemma qpoly_nontrivial : qpoly1 != 0.
Proof. by apply/eqP/val_eqP; rewrite /= oner_eq0. Qed.

Definition qpolyX := in_qpoly 'X.
Notation "'qX" := qpolyX.

Lemma qpolyXE : 2 < size h -> h \is monic -> 'qX = 'X :> {poly R}.
Proof.
move=> sh_gt2 h_mo.
by rewrite in_qpoly_small // size_polyX /mk_monic ifT // (ltn_trans _ sh_gt2).
Qed.

End QpolyProp.

Notation "'qX" := (qpolyX _) : ring_scope.

Lemma mk_monic_X (R : nzRingType) : mk_monic 'X = 'X :> {poly R}.
Proof. by rewrite /mk_monic size_polyX monicX. Qed.

Lemma mk_monic_Xn (R : nzRingType) n : mk_monic 'X^n = 'X^n.-1.+1 :> {poly R}.
Proof. by case: n => [|n]; rewrite /mk_monic size_polyXn monicXn /= ?expr1. Qed.

Lemma card_qpoly (R : finNzRingType) (h : {poly R}):
   #|{poly %/ h}| = #|R| ^ (size (mk_monic h)).-1.
Proof. by rewrite card_npoly. Qed.

Lemma card_monic_qpoly (R : finNzRingType) (h : {poly R}):
  1 < size h -> h \is monic ->  #|{poly %/ h}| = #|R| ^ (size h).-1.
Proof. by move=> sh_gt1 hM; rewrite card_qpoly /mk_monic sh_gt1 hM. Qed.

Section QRing.

Variable A : comNzRingType.
Variable h : {poly A}.

(* Ring operations *)

Lemma qpoly_mulC : commutative (@qpoly_mul A h).
Proof. by move=> p q; apply: val_inj; rewrite /= mulrC. Qed.

Lemma qpoly_mulA : associative (@qpoly_mul A h).
Proof.
have rPM := monic_mk_monic h; move=> p q r; apply: val_inj.
by rewrite /= rmodp_mulml // rmodp_mulmr // mulrA.
Qed.

Lemma qpoly_mul_addr : right_distributive (@qpoly_mul A h) +%R.
Proof.
have rPM := monic_mk_monic h; move=> p q r; apply: val_inj.
by rewrite /= !(mulrDr, rmodp_mulmr, rmodpD).
Qed.

Lemma qpoly_mul_addl : left_distributive (@qpoly_mul A h) +%R.
Proof. by move=> p q r; rewrite -!(qpoly_mulC r) qpoly_mul_addr. Qed.

HB.instance Definition _ := GRing.Zmodule_isComNzRing.Build {poly__ A} qpoly_mulA
  qpoly_mulC (@qpoly_mul1z _ h) qpoly_mul_addl (@qpoly_nontrivial _ h).
HB.instance Definition _ := GRing.ComNzRing.on {poly %/ h}.

Lemma in_qpoly1 : in_qpoly h 1 = 1.
Proof.
apply/val_eqP/eqP/in_qpoly_small.
by rewrite size_polyC oner_eq0 /= size_mk_monic_gt1.
Qed.

Lemma in_qpolyM q1 q2 : in_qpoly h (q1 * q2) = in_qpoly h q1 * in_qpoly h q2.
Proof.
apply/val_eqP => /=.
by rewrite rmodp_mulml ?rmodp_mulmr // monic_mk_monic.
Qed.

Fact in_qpoly_multiplicative : multiplicative (in_qpoly h).
Proof. by split; [ apply: in_qpolyM | apply: in_qpoly1]. Qed.

HB.instance Definition _ :=
  GRing.isMultiplicative.Build {poly A} {poly %/ h} (in_qpoly h)
    in_qpoly_multiplicative.

Lemma poly_of_qpoly_sum I (r : seq I) (P1 : pred I) (F : I -> {poly %/ h}) :
  ((\sum_(i <- r | P1 i) F i) =
    \sum_(p <- r | P1 p) ((F p) : {poly A}) :> {poly A})%R.
Proof. by elim/big_rec2: _ => // i p q IH <-. Qed.

Lemma poly_of_qpolyD (p q : {poly %/ h}) :
  p + q= (p : {poly A}) + q :> {poly A}.
Proof. by []. Qed.

Lemma qpolyC_natr p : (p%:R : {poly %/ h}) = p%:R :> {poly A}.
Proof. by elim: p => //= p IH; rewrite !mulrS poly_of_qpolyD IH. Qed.

Lemma pchar_qpoly : [pchar {poly %/ h}] =i [pchar A].
Proof.
move=> p; rewrite !inE; congr (_ && _).
apply/eqP/eqP=> [/(congr1 val) /=|pE]; last first.
  by apply: val_inj => //=; rewrite qpolyC_natr /= -polyC_natr pE.
rewrite !qpolyC_natr -!polyC_natr => /(congr1 val) /=.
by rewrite polyseqC polyseq0; case: eqP.
Qed.

Lemma poly_of_qpolyM (p q : {poly %/ h}) :
  p * q = rmodp ((p : {poly A}) * q) (mk_monic h) :> {poly A}.
Proof. by []. Qed.

Lemma poly_of_qpolyX (p : {poly %/ h}) n :
  p ^+ n = rmodp ((p : {poly A}) ^+ n) (mk_monic h) :> {poly A}.
Proof.
have HhQ := monic_mk_monic h.
elim: n => //= [|n IH].
  rewrite rmodp_small // size_polyC ?(leq_ltn_trans _ (size_mk_monic_gt1 _)) //.
  by case: eqP.
by rewrite exprS /= IH // rmodp_mulmr // -exprS.
Qed.

Lemma qpolyCN (a : A) : qpolyC h (- a) = -(qpolyC h a).
Proof. apply: val_inj; rewrite /= raddfN //= raddfN. Qed.

Lemma qpolyCD : {morph (qpolyC h) : a b / a + b >-> a + b}%R.
Proof. by move=> a b; apply/val_eqP/eqP=> /=; rewrite -!raddfD. Qed.

Lemma qpolyCM : {morph (qpolyC h) : a b / a * b >-> a * b}%R.
Proof.
move=> a b; apply/val_eqP/eqP=> /=; rewrite -polyCM rmodp_small //=.
have := qpolyC_proof h (a * b).
by rewrite qualifE/= -ltnS prednK // size_mk_monic_gt0.
Qed.

Lemma qpolyC_is_additive : additive (qpolyC h).
Proof. by move=> x y; rewrite qpolyCD qpolyCN. Qed.

Lemma qpolyC_is_multiplicative : multiplicative (qpolyC h).
Proof. by split=> // x y; rewrite qpolyCM. Qed.

HB.instance Definition _ := GRing.isAdditive.Build A {poly %/ h} (qpolyC h)
  qpolyC_is_additive.
HB.instance Definition _ :=
  GRing.isMultiplicative.Build A {poly %/ h} (qpolyC h)
    qpolyC_is_multiplicative.

Definition qpoly_scale k (p : {poly %/ h}) : {poly %/ h} := (k *: p)%R.

Fact qpoly_scaleA a b p :
  qpoly_scale a (qpoly_scale b p) = qpoly_scale (a * b) p.
Proof.  by apply/val_eqP; rewrite /= scalerA. Qed.

Fact qpoly_scale1l : left_id 1%R qpoly_scale.
Proof. by move=> p; apply/val_eqP; rewrite /= scale1r. Qed.

Fact qpoly_scaleDr a : {morph qpoly_scale a : p q / (p + q)%R}.
Proof. by move=> p q; apply/val_eqP; rewrite /= scalerDr. Qed.

Fact qpoly_scaleDl p : {morph qpoly_scale^~ p : a b / a + b}%R.
Proof. by move=> a b; apply/val_eqP; rewrite /= scalerDl. Qed.

Fact qpoly_scaleAl a p q : qpoly_scale a (p * q) = (qpoly_scale a p * q).
Proof. by apply/val_eqP; rewrite /= -scalerAl rmodpZ // monic_mk_monic. Qed.

Fact qpoly_scaleAr a p q : qpoly_scale a (p * q) = p * (qpoly_scale a q).
Proof. by apply/val_eqP; rewrite /= -scalerAr rmodpZ // monic_mk_monic. Qed.

HB.instance Definition _ := GRing.Lmodule_isLalgebra.Build A {poly__ A}
  qpoly_scaleAl.
HB.instance Definition _ := GRing.Lalgebra.on {poly %/ h}.

HB.instance Definition _ := GRing.Lalgebra_isAlgebra.Build A {poly__ A}
  qpoly_scaleAr.
HB.instance Definition _ := GRing.Algebra.on {poly %/ h}.

Lemma poly_of_qpolyZ (p : {poly %/ h}) a :
  a *: p = a *: (p : {poly A})  :> {poly A}.
Proof. by []. Qed.

End QRing.

#[deprecated(since="mathcomp 2.4.0", note="Use pchar_qpoly instead.")]
Notation char_qpoly := (pchar_qpoly) (only parsing).

Section Field.

Variable R : fieldType.
Variable h : {poly R}.

Local Notation hQ := (mk_monic h).

Definition qpoly_inv (p : {poly %/ h}) :=
  if coprimep hQ p then let v : {poly %/ h} := in_qpoly h (egcdp hQ p).2 in
                        ((lead_coef (v * p)) ^-1 *: v) else p.

(* Ugly *)
Lemma qpoly_mulVz (p : {poly %/ h}) : coprimep hQ p -> (qpoly_inv p * p = 1)%R.
Proof.
have hQM := monic_mk_monic h.
move=> hCp; apply: val_inj; rewrite /qpoly_inv /in_qpoly hCp /=.
have p_neq0 : p != 0%R.
  apply/eqP=> pZ; move: hCp; rewrite pZ.
  rewrite coprimep0 -size_poly_eq1.
  by case: size (size_mk_monic_gt1 h) => [|[]].
have F : (egcdp hQ p).1 * hQ + (egcdp hQ p).2 * p %= 1.
  apply: eqp_trans _ (_ : gcdp hQ p %= _).
    rewrite eqp_sym.
    by case: (egcdpP (mk_monic_neq0 h) p_neq0).
  by rewrite -size_poly_eq1.
rewrite rmodp_mulml // -scalerAl rmodpZ // rmodp_mulml //.
rewrite -[rmodp]/Pdiv.Ring.rmodp -!Pdiv.IdomainMonic.modpE //.
have := eqp_modpl hQ F.
rewrite modpD // modp_mull add0r // .
rewrite [(1 %% _)%R]modp_small => // [egcdE|]; last first.
  by rewrite size_polyC oner_eq0 size_mk_monic_gt1.
rewrite {2}(eqpfP egcdE) lead_coefC divr1 alg_polyC scale_polyC mulVf //.
rewrite lead_coef_eq0.
apply/eqP => egcdZ.
by move: egcdE; rewrite -size_poly_eq1 egcdZ size_polyC eq_sym  eqxx.
Qed.

Lemma qpoly_mulzV (p : {poly %/ h}) :
  coprimep hQ p -> (p * (qpoly_inv p) = 1)%R.
Proof. by move=> hCp; rewrite /= mulrC qpoly_mulVz. Qed.

Lemma qpoly_intro_unit (p q : {poly %/ h}) : (q * p = 1)%R -> coprimep hQ p.
Proof.
have hQM := monic_mk_monic h.
case; rewrite -[rmodp]/Pdiv.Ring.rmodp -!Pdiv.IdomainMonic.modpE // => qp1.
have:= coprimep1 hQ.
rewrite -coprimep_modr -[1%R]qp1 !coprimep_modr coprimepMr; by case/andP.
Qed.

Lemma qpoly_inv_out (p : {poly %/ h}) : ~~ coprimep hQ p -> qpoly_inv p = p.
Proof. by rewrite /qpoly_inv => /negPf->. Qed.

HB.instance Definition _ := GRing.ComNzRing_hasMulInverse.Build {poly__ _}
  qpoly_mulVz qpoly_intro_unit qpoly_inv_out.
HB.instance Definition _ := GRing.ComUnitAlgebra.on {poly %/ h}.

Lemma irreducible_poly_coprime (A : idomainType) (p q : {poly A}) :
  irreducible_poly p -> coprimep p q = ~~(p %| q)%R.
Proof.
case => H1 H2; apply/coprimepP/negP.
  move=> sPq H.
  by have := sPq p (dvdpp _) H; rewrite -size_poly_eq1; case: size H1 => [|[]].
move=> pNDq d dDp dPq.
rewrite -size_poly_eq1; case: eqP => // /eqP /(H2 _) => /(_ dDp) dEp.
by case: pNDq; rewrite -(eqp_dvdl _ dEp).
Qed.

End Field.

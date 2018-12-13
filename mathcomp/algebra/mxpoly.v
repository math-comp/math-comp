(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrfun ssrbool eqtype ssrnat seq div fintype tuple.
From mathcomp
Require Import finfun bigop fingroup perm ssralg zmodp matrix mxalgebra.
From mathcomp
Require Import poly polydiv.

(******************************************************************************)
(*   This file provides basic support for formal computation with matrices,   *)
(* mainly results combining matrices and univariate polynomials, such as the  *)
(* Cayley-Hamilton theorem; it also contains an extension of the first order  *)
(* representation of algebra introduced in ssralg (GRing.term/formula).       *)
(*      rVpoly v == the little-endian decoding of the row vector v as a       *)
(*                  polynomial p = \sum_i (v 0 i)%:P * 'X^i.                  *)
(*     poly_rV p == the partial inverse to rVpoly, for polynomials of degree  *)
(*                  less than d to 'rV_d (d is inferred from the context).    *)
(* Sylvester_mx p q == the Sylvester matrix of p and q.                       *)
(* resultant p q == the resultant of p and q, i.e., \det (Sylvester_mx p q).  *)
(*   horner_mx A == the morphism from {poly R} to 'M_n (n of the form n'.+1)  *)
(*                  mapping a (scalar) polynomial p to the value of its       *)
(*                  scalar matrix interpretation at A (this is an instance of *)
(*                  the generic horner_morph construct defined in poly).      *)
(* powers_mx A d == the d x (n ^ 2) matrix whose rows are the mxvec encodings *)
(*                  of the first d powers of A (n of the form n'.+1). Thus,   *)
(*                  vec_mx (v *m powers_mx A d) = horner_mx A (rVpoly v).     *)
(*   char_poly A  == the characteristic polynomial of A.                      *)
(* char_poly_mx A == a matrix whose determinant is char_poly A.               *)
(*  companionmx p == a matrix whose char_poly is p                            *)
(*   mxminpoly A  == the minimal polynomial of A, i.e., the smallest monic    *)
(*                   polynomial that annihilates A (A must be nontrivial).    *)
(* degree_mxminpoly A == the (positive) degree of mxminpoly A.                *)
(* mx_inv_horner A == the inverse of horner_mx A for polynomials of degree    *)
(*                  smaller than degree_mxminpoly A.                          *)
(*  integralOver RtoK u <-> u is in the integral closure of the image of R    *)
(*                  under RtoK : R -> K, i.e. u is a root of the image of a   *)
(*                  monic polynomial in R.                                    *)
(*  algebraicOver FtoE u <-> u : E is algebraic over E; it is a root of the   *)
(*                  image of a nonzero polynomial under FtoE; as F must be a  *)
(*                  fieldType, this is equivalent to integralOver FtoE u.     *)
(*  integralRange RtoK <-> the integral closure of the image of R contains    *)
(*                  all of K (:= forall u, integralOver RtoK u).              *)
(* This toolkit for building formal matrix expressions is packaged in the     *)
(* MatrixFormula submodule, and comprises the following:                      *)
(*     eval_mx e == GRing.eval lifted to matrices (:= map_mx (GRing.eval e)). *)
(*     mx_term A == GRing.Const lifted to matrices.                           *)
(* mulmx_term A B == the formal product of two matrices of terms.             *)
(* mxrank_form m A == a GRing.formula asserting that the interpretation of    *)
(*                  the term matrix A has rank m.                             *)
(* submx_form A B == a GRing.formula asserting that the row space of the      *)
(*                  interpretation of the term matrix A is included in the    *)
(*                  row space of the interpretation of B.                     *)
(*   seq_of_rV v == the seq corresponding to a row vector.                    *)
(*     row_env e == the flattening of a tensored environment e : seq 'rV_d.   *)
(* row_var F d k == the term vector of width d such that for e : seq 'rV[F]_d *)
(*                  we have eval e 'X_k = eval_mx (row_env e) (row_var d k).  *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Import Monoid.Theory.

Local Open Scope ring_scope.

Import Pdiv.Idomain.
(* Row vector <-> bounded degree polynomial bijection *)
Section RowPoly.

Variables (R : ringType) (d : nat).
Implicit Types u v : 'rV[R]_d.
Implicit Types p q : {poly R}.

Definition rVpoly v := \poly_(k < d) (if insub k is Some i then v 0 i else 0).
Definition poly_rV p := \row_(i < d) p`_i.

Lemma coef_rVpoly v k : (rVpoly v)`_k = if insub k is Some i then v 0 i else 0.
Proof. by rewrite coef_poly; case: insubP => [i ->|]; rewrite ?if_same. Qed.

Lemma coef_rVpoly_ord v (i : 'I_d) : (rVpoly v)`_i = v 0 i.
Proof. by rewrite coef_rVpoly valK. Qed.

Lemma rVpoly_delta i : rVpoly (delta_mx 0 i) = 'X^i.
Proof.
apply/polyP=> j; rewrite coef_rVpoly coefXn.
case: insubP => [k _ <- | j_ge_d]; first by rewrite mxE.
by case: eqP j_ge_d => // ->; rewrite ltn_ord.
Qed.

Lemma rVpolyK : cancel rVpoly poly_rV.
Proof. by move=> u; apply/rowP=> i; rewrite mxE coef_rVpoly_ord. Qed.

Lemma poly_rV_K p : size p <= d -> rVpoly (poly_rV p) = p.
Proof.
move=> le_p_d; apply/polyP=> k; rewrite coef_rVpoly.
case: insubP => [i _ <- | ]; first by rewrite mxE.
by rewrite -ltnNge => le_d_l; rewrite nth_default ?(leq_trans le_p_d).
Qed.

Lemma poly_rV_is_linear : linear poly_rV.
Proof. by move=> a p q; apply/rowP=> i; rewrite !mxE coefD coefZ. Qed.
Canonical poly_rV_additive := Additive poly_rV_is_linear.
Canonical poly_rV_linear := Linear poly_rV_is_linear.

Lemma rVpoly_is_linear : linear rVpoly.
Proof.
move=> a u v; apply/polyP=> k; rewrite coefD coefZ !coef_rVpoly.
by case: insubP => [i _ _ | _]; rewrite ?mxE // mulr0 addr0.
Qed.
Canonical rVpoly_additive := Additive rVpoly_is_linear.
Canonical rVpoly_linear := Linear rVpoly_is_linear.

End RowPoly.

Prenex Implicits rVpoly rVpolyK.
Arguments poly_rV {R d}.
Arguments poly_rV_K {R d} [p] le_p_d.

Section Resultant.

Variables (R : ringType) (p q : {poly R}).

Let dS := ((size q).-1 + (size p).-1)%N.
Local Notation band r := (lin1_mx (poly_rV \o r \o* rVpoly)).

Definition Sylvester_mx : 'M[R]_dS := col_mx (band p) (band q).

Lemma Sylvester_mxE (i j : 'I_dS) :
  let S_ r k := r`_(j - k) *+ (k <= j) in
  Sylvester_mx i j = match split i with inl k => S_ p k | inr k => S_ q k end.
Proof.
move=> S_; rewrite mxE; case: {i}(split i) => i; rewrite !mxE /=;
  by rewrite rVpoly_delta coefXnM ltnNge if_neg -mulrb.
Qed.

Definition resultant := \det Sylvester_mx.

End Resultant.

Prenex Implicits Sylvester_mx resultant.

Lemma resultant_in_ideal (R : comRingType) (p q : {poly R}) :
    size p > 1 -> size q > 1 ->
  {uv : {poly R} * {poly R} | size uv.1 < size q /\ size uv.2 < size p
  & (resultant p q)%:P = uv.1 * p + uv.2 * q}.
Proof.
move=> p_nc q_nc; pose dp := (size p).-1; pose dq := (size q).-1.
pose S := Sylvester_mx p q; pose dS := (dq + dp)%N.
have dS_gt0: dS > 0 by rewrite /dS /dq -(subnKC q_nc).
pose j0 := Ordinal dS_gt0.
pose Ss0 := col_mx (p *: \col_(i < dq) 'X^i) (q *: \col_(i < dp) 'X^i).
pose Ss := \matrix_(i, j) (if j == j0 then Ss0 i 0 else (S i j)%:P).
pose u ds s := \sum_(i < ds) cofactor Ss (s i) j0 * 'X^i.
exists (u _ (lshift dp), u _ ((rshift dq) _)).
  suffices sz_u ds s: ds > 1 -> size (u ds.-1 s) < ds by rewrite !sz_u.
  move/ltn_predK=> {2}<-; apply: leq_trans (size_sum _ _ _) _.
  apply/bigmax_leqP=> i _.
  have ->: cofactor Ss (s i) j0 = (cofactor S (s i) j0)%:P.
    rewrite rmorphM rmorph_sign -det_map_mx; congr (_ * \det _).
    by apply/matrixP=> i' j'; rewrite !mxE.
  apply: leq_trans (size_mul_leq _ _) (leq_trans _ (valP i)).
  by rewrite size_polyC size_polyXn addnS /= -add1n leq_add2r leq_b1.
transitivity (\det Ss); last first.
  rewrite (expand_det_col Ss j0) big_split_ord !big_distrl /=.
  by congr (_ + _); apply: eq_bigr => i _;
    rewrite mxE eqxx (col_mxEu, col_mxEd) !mxE mulrC mulrA mulrAC.
pose S_ j1 := map_mx polyC (\matrix_(i, j) S i (if j == j0 then j1 else j)).
pose Ss0_ i dj := \poly_(j < dj) S i (insubd j0 j).
pose Ss_ dj := \matrix_(i, j) (if j == j0 then Ss0_ i dj else (S i j)%:P).
have{Ss u} ->: Ss = Ss_ dS.
  apply/matrixP=> i j; rewrite mxE [in X in _ = X]mxE; case: (j == j0) => {j}//.
  apply/polyP=> k; rewrite coef_poly Sylvester_mxE mxE.
  have [k_ge_dS | k_lt_dS] := leqP dS k.
    case: (split i) => {i}i; rewrite !mxE coefMXn;
    case: ifP => // /negbT; rewrite -ltnNge ltnS => hi.
      apply: (leq_sizeP _ _ (leqnn (size p))); rewrite -(ltn_predK p_nc).
      by rewrite ltn_subRL (leq_trans _ k_ge_dS) // ltn_add2r.
    - apply: (leq_sizeP _ _ (leqnn (size q))); rewrite -(ltn_predK q_nc).
      by rewrite ltn_subRL (leq_trans _ k_ge_dS) // addnC ltn_add2l.
  by rewrite insubdK //; case: (split i) => {i}i;
     rewrite !mxE coefMXn; case: leqP.
elim: {-2}dS (leqnn dS) (dS_gt0) => // dj IHj dj_lt_dS _.
pose j1 := Ordinal dj_lt_dS; pose rj0T (A : 'M[{poly R}]_dS) := row j0 A^T.
have: rj0T (Ss_ dj.+1) = 'X^dj *: rj0T (S_ j1) + 1 *: rj0T (Ss_ dj).
  apply/rowP=> i; apply/polyP=> k; rewrite scale1r !(Sylvester_mxE, mxE) eqxx.
  rewrite coefD coefXnM coefC !coef_poly ltnS subn_eq0 ltn_neqAle andbC.
  case: (leqP k dj) => [k_le_dj | k_gt_dj] /=; last by rewrite addr0.
  rewrite Sylvester_mxE insubdK; last exact: leq_ltn_trans (dj_lt_dS).
  by case: eqP => [-> | _]; rewrite (addr0, add0r).
rewrite -det_tr => /determinant_multilinear->;
  try by apply/matrixP=> i j; rewrite !mxE eq_sym (negPf (neq_lift _ _)).
have [dj0 | dj_gt0] := posnP dj; rewrite ?dj0 !mul1r.
  rewrite !det_tr det_map_mx addrC (expand_det_col _ j0) big1 => [|i _].
    rewrite add0r; congr (\det _)%:P.
    apply/matrixP=> i j; rewrite [in X in _ = X]mxE; case: eqP => // ->.
    by congr (S i _); apply: val_inj.
  by rewrite mxE /= [Ss0_ _ _]poly_def big_ord0 mul0r.
have /determinant_alternate->: j1 != j0 by rewrite -val_eqE -lt0n.
  by rewrite mulr0 add0r det_tr IHj // ltnW.
by move=> i; rewrite !mxE if_same.
Qed.

Lemma resultant_eq0 (R : idomainType) (p q : {poly R}) :
  (resultant p q == 0) = (size (gcdp p q) > 1).
Proof.
have dvdpp := dvdpp; set r := gcdp p q.
pose dp := (size p).-1; pose dq := (size q).-1.
have /andP[r_p r_q]: (r %| p) && (r %| q) by rewrite -dvdp_gcd.
apply/det0P/idP=> [[uv nz_uv] | r_nonC].
  have [p0 _ | p_nz] := eqVneq p 0.
    have: dq + dp > 0.
      rewrite lt0n; apply: contraNneq nz_uv => dqp0.
      by rewrite dqp0 in uv *; rewrite [uv]thinmx0.
    by rewrite /dp /dq /r p0 size_poly0 addn0 gcd0p -subn1 subn_gt0.
  do [rewrite -[uv]hsubmxK -{1}row_mx0 mul_row_col !mul_rV_lin1 /=] in nz_uv *.
  set u := rVpoly _; set v := rVpoly _; pose m := gcdp (v * p) (v * q).
  have lt_vp: size v < size p by rewrite (polySpred p_nz) ltnS size_poly.
  move/(congr1 rVpoly)/eqP; rewrite -linearD linear0 poly_rV_K; last first.
    rewrite (leq_trans (size_add _ _)) // geq_max.
    rewrite !(leq_trans (size_mul_leq _ _)) // -subn1 leq_subLR.
      by rewrite addnC addnA leq_add ?leqSpred ?size_poly.
    by rewrite addnCA leq_add ?leqSpred ?size_poly.
  rewrite addrC addr_eq0 => /eqP vq_up.
  have nz_v: v != 0.
    apply: contraNneq nz_uv => v0; apply/eqP.
    congr row_mx; apply: (can_inj rVpolyK); rewrite linear0 // -/u.
    by apply: contra_eq vq_up; rewrite v0 mul0r -addr_eq0 add0r => /mulf_neq0->.
  have r_nz: r != 0 := dvdpN0 r_p p_nz.
  have /dvdpP [[c w] /= nz_c wv]: v %| m by rewrite dvdp_gcd !dvdp_mulr.
  have m_wd d: m %| v * d -> w %| d.
    case/dvdpP=> [[k f]] /= nz_k /(congr1 ( *:%R c)).
    rewrite mulrC scalerA scalerAl scalerAr wv mulrA => /(mulIf nz_v)def_fw.
    by apply/dvdpP; exists (c * k, f); rewrite //= mulf_neq0.
  have w_r: w %| r by rewrite dvdp_gcd !m_wd ?dvdp_gcdl ?dvdp_gcdr.
  have w_nz: w != 0 := dvdpN0 w_r r_nz.
  have p_m: p %| m  by rewrite dvdp_gcd vq_up -mulNr !dvdp_mull.
  rewrite (leq_trans _ (dvdp_leq r_nz w_r)) // -(ltn_add2l (size v)).
  rewrite addnC -ltn_subRL subn1 -size_mul // mulrC -wv size_scale //.
  rewrite (leq_trans lt_vp) // dvdp_leq // -size_poly_eq0.
  by rewrite -(size_scale _ nz_c) size_poly_eq0 wv mulf_neq0.
have [[c p'] /= nz_c p'r] := dvdpP _ _ r_p.
have [[k q'] /= nz_k q'r] := dvdpP _ _ r_q.
have def_r := subnKC r_nonC; have r_nz: r != 0 by rewrite -size_poly_eq0 -def_r.
have le_p'_dp: size p' <= dp.
  have [-> | nz_p'] := eqVneq p' 0; first by rewrite size_poly0.
  by rewrite /dp -(size_scale p nz_c) p'r size_mul // addnC -def_r leq_addl.
have le_q'_dq: size q' <= dq.
  have [-> | nz_q'] := eqVneq q' 0; first by rewrite size_poly0.
  by rewrite /dq -(size_scale q nz_k) q'r size_mul // addnC -def_r leq_addl.
exists (row_mx (- c *: poly_rV q') (k *: poly_rV p')).
  apply: contraNneq r_nz; rewrite -row_mx0; case/eq_row_mx=> q0 p0.
  have{p0} p0: p = 0.
    apply/eqP; rewrite -size_poly_eq0 -(size_scale p nz_c) p'r.
    rewrite -(size_scale _ nz_k) scalerAl -(poly_rV_K le_p'_dp) -linearZ p0.
    by rewrite linear0 mul0r size_poly0.
  rewrite /r p0 gcd0p -size_poly_eq0 -(size_scale q nz_k) q'r.
  rewrite -(size_scale _ nz_c) scalerAl -(poly_rV_K le_q'_dq) -linearZ.
  by rewrite -[c]opprK scaleNr q0 !linear0 mul0r size_poly0.
rewrite mul_row_col scaleNr mulNmx !mul_rV_lin1 /= !linearZ /= !poly_rV_K //.
by rewrite !scalerCA p'r q'r mulrCA addNr.
Qed.

Section HornerMx.

Variables (R : comRingType) (n' : nat).
Local Notation n := n'.+1.
Variable A : 'M[R]_n.
Implicit Types p q : {poly R}.

Definition horner_mx := horner_morph (fun a => scalar_mx_comm a A).
Canonical horner_mx_additive := [additive of horner_mx].
Canonical horner_mx_rmorphism := [rmorphism of horner_mx].

Lemma horner_mx_C a : horner_mx a%:P = a%:M.
Proof. exact: horner_morphC. Qed.

Lemma horner_mx_X : horner_mx 'X = A. Proof. exact: horner_morphX. Qed.

Lemma horner_mxZ : scalable horner_mx.
Proof.
move=> a p /=; rewrite -mul_polyC rmorphM /=.
by rewrite horner_mx_C [_ * _]mul_scalar_mx.
Qed.

Canonical horner_mx_linear := AddLinear horner_mxZ.
Canonical horner_mx_lrmorphism := [lrmorphism of horner_mx].

Definition powers_mx d := \matrix_(i < d) mxvec (A ^+ i).

Lemma horner_rVpoly m (u : 'rV_m) :
  horner_mx (rVpoly u) = vec_mx (u *m powers_mx m).
Proof.
rewrite mulmx_sum_row linear_sum [rVpoly u]poly_def rmorph_sum.
apply: eq_bigr => i _.
by rewrite valK !linearZ rmorphX /= horner_mx_X rowK /= mxvecK.
Qed.

End HornerMx.

Prenex Implicits horner_mx powers_mx.

Section CharPoly.

Variables (R : ringType) (n : nat) (A : 'M[R]_n).
Implicit Types p q : {poly R}.

Definition char_poly_mx := 'X%:M - map_mx (@polyC R) A.
Definition char_poly := \det char_poly_mx.

Let diagA := [seq A i i | i : 'I_n].
Let size_diagA : size diagA = n.
Proof. by rewrite size_image card_ord. Qed.

Let split_diagA :
  exists2 q, \prod_(x <- diagA) ('X - x%:P) + q = char_poly & size q <= n.-1.
Proof.
rewrite [char_poly](bigD1 1%g) //=; set q := \sum_(s | _) _; exists q.
  congr (_ + _); rewrite odd_perm1 mul1r big_map enumT; apply: eq_bigr => i _.
  by rewrite !mxE perm1 eqxx.
apply: leq_trans {q}(size_sum _ _ _) _; apply/bigmax_leqP=> s nt_s.
have{nt_s} [i nfix_i]: exists i, s i != i.
  apply/existsP; rewrite -negb_forall; apply: contra nt_s => s_1.
  by apply/eqP; apply/permP=> i; apply/eqP; rewrite perm1 (forallP s_1).
apply: leq_trans (_ : #|[pred j | s j == j]|.+1 <= n.-1).
  rewrite -sum1_card (@big_mkcond nat) /= size_Msign.
  apply: (big_ind2 (fun p m => size p <= m.+1)) => [| p mp q mq IHp IHq | j _].
  - by rewrite size_poly1.
  - apply: leq_trans (size_mul_leq _ _) _.
    by rewrite -subn1 -addnS leq_subLR addnA leq_add.
  rewrite !mxE eq_sym !inE; case: (s j == j); first by rewrite polyseqXsubC.
  by rewrite sub0r size_opp size_polyC leq_b1.
rewrite -{8}[n]card_ord -(cardC (pred2 (s i) i)) card2 nfix_i !ltnS.
apply: subset_leq_card; apply/subsetP=> j; move/(_ =P j)=> fix_j.
rewrite !inE -{1}fix_j (inj_eq perm_inj) orbb.
by apply: contraNneq nfix_i => <-; rewrite fix_j.
Qed.

Lemma size_char_poly : size char_poly = n.+1.
Proof.
have [q <- lt_q_n] := split_diagA; have le_q_n := leq_trans lt_q_n (leq_pred n).
by rewrite size_addl size_prod_XsubC size_diagA.
Qed.

Lemma char_poly_monic : char_poly \is monic.
Proof.
rewrite monicE -(monicP (monic_prod_XsubC diagA xpredT id)).
rewrite !lead_coefE size_char_poly.
have [q <- lt_q_n] := split_diagA; have le_q_n := leq_trans lt_q_n (leq_pred n).
by rewrite size_prod_XsubC size_diagA coefD (nth_default 0 le_q_n) addr0.
Qed.

Lemma char_poly_trace : n > 0 -> char_poly`_n.-1 = - \tr A.
Proof.
move=> n_gt0; have [q <- lt_q_n] := split_diagA; set p := \prod_(x <- _) _.
rewrite coefD {q lt_q_n}(nth_default 0 lt_q_n) addr0.
have{n_gt0} ->: p`_n.-1 = ('X * p)`_n by rewrite coefXM eqn0Ngt n_gt0.
have ->: \tr A = \sum_(x <- diagA) x by rewrite big_map enumT.
rewrite -size_diagA {}/p; elim: diagA => [|x d IHd].
  by rewrite !big_nil mulr1 coefX oppr0.
rewrite !big_cons coefXM mulrBl coefB IHd opprD addrC; congr (- _ + _).
rewrite mul_polyC coefZ [size _]/= -(size_prod_XsubC _ id) -lead_coefE.
by rewrite (monicP _) ?monic_prod_XsubC ?mulr1.
Qed.

Lemma char_poly_det : char_poly`_0 = (- 1) ^+ n * \det A.
Proof.
rewrite big_distrr coef_sum [0%N]lock /=; apply: eq_bigr => s _.
rewrite -{1}rmorphN -rmorphX mul_polyC coefZ /=.
rewrite mulrA -exprD addnC exprD -mulrA -lock; congr (_ * _).
transitivity (\prod_(i < n) - A i (s i)); last by rewrite prodrN card_ord.
elim: (index_enum _) => [|i e IHe]; rewrite !(big_nil, big_cons) ?coef1 //.
by rewrite coefM big_ord1 IHe !mxE coefB coefC coefMn coefX mul0rn sub0r.
Qed.

End CharPoly.

Prenex Implicits char_poly_mx char_poly.

Lemma mx_poly_ring_isom (R : ringType) n' (n := n'.+1) :
  exists phi : {rmorphism 'M[{poly R}]_n -> {poly 'M[R]_n}},
  [/\ bijective phi,
      forall p, phi p%:M = map_poly scalar_mx p,
      forall A, phi (map_mx polyC A) = A%:P
    & forall A i j k, (phi A)`_k i j = (A i j)`_k].
Proof.
set M_RX := 'M[{poly R}]_n; set MR_X := ({poly 'M[R]_n}).
pose Msize (A : M_RX) := \max_i \max_j size (A i j).
pose phi (A : M_RX) := \poly_(k < Msize A) \matrix_(i, j) (A i j)`_k.
have coef_phi A i j k: (phi A)`_k i j = (A i j)`_k.
  rewrite coef_poly; case: (ltnP k _) => le_m_k; rewrite mxE // nth_default //.
  by apply: leq_trans (leq_trans (leq_bigmax i) le_m_k); apply: (leq_bigmax j).
have phi_is_rmorphism : rmorphism phi.
  do 2?[split=> [A B|]]; apply/polyP=> k; apply/matrixP=> i j; last 1 first.
  - rewrite coef_phi mxE coefMn !coefC.
    by case: (k == _); rewrite ?mxE ?mul0rn.
  - by rewrite !(coef_phi, mxE, coefD, coefN).
  rewrite !coef_phi !mxE !coefM summxE coef_sum.
  pose F k1 k2 := (A i k1)`_k2 * (B k1 j)`_(k - k2).
  transitivity (\sum_k1 \sum_(k2 < k.+1) F k1 k2); rewrite {}/F.
    by apply: eq_bigr=> k1 _; rewrite coefM.
  rewrite exchange_big /=; apply: eq_bigr => k2 _.
  by rewrite mxE; apply: eq_bigr => k1 _; rewrite !coef_phi.
have bij_phi: bijective phi.
  exists (fun P : MR_X => \matrix_(i, j) \poly_(k < size P) P`_k i j) => [A|P].
    apply/matrixP=> i j; rewrite mxE; apply/polyP=> k.
    rewrite coef_poly -coef_phi.
    by case: leqP => // P_le_k; rewrite nth_default ?mxE.
  apply/polyP=> k; apply/matrixP=> i j; rewrite coef_phi mxE coef_poly.
  by case: leqP => // P_le_k; rewrite nth_default ?mxE.
exists (RMorphism phi_is_rmorphism).
split=> // [p | A]; apply/polyP=> k; apply/matrixP=> i j.
  by rewrite coef_phi coef_map !mxE coefMn.
by rewrite coef_phi !mxE !coefC; case k; last rewrite /= mxE.
Qed.

Theorem Cayley_Hamilton (R : comRingType) n' (A : 'M[R]_n'.+1) :
  horner_mx A (char_poly A) = 0.
Proof.
have [phi [_ phiZ phiC _]] := mx_poly_ring_isom R n'.
apply/rootP/factor_theorem; rewrite -phiZ -mul_adj_mx rmorphM.
by move: (phi _) => q; exists q; rewrite rmorphB phiC phiZ map_polyX.
Qed.

Lemma eigenvalue_root_char (F : fieldType) n (A : 'M[F]_n) a :
  eigenvalue A a = root (char_poly A) a.
Proof.
transitivity (\det (a%:M - A) == 0).
  apply/eigenvalueP/det0P=> [[v Av_av v_nz] | [v v_nz Av_av]]; exists v => //.
    by rewrite mulmxBr Av_av mul_mx_scalar subrr.
  by apply/eqP; rewrite -mul_mx_scalar eq_sym -subr_eq0 -mulmxBr Av_av.
congr (_ == 0); rewrite horner_sum; apply: eq_bigr => s _.
rewrite hornerM horner_exp !hornerE; congr (_ * _).
rewrite (big_morph _ (fun p q => hornerM p q a) (hornerC 1 a)).
by apply: eq_bigr => i _; rewrite !mxE !(hornerE, hornerMn).
Qed.

Definition companionmx {R : ringType} (p : seq R) (d := (size p).-1) :=
  \matrix_(i < d, j < d)
    if (i == d.-1 :> nat) then - p`_j else (i.+1 == j :> nat)%:R.

Lemma companionmxK {R : comRingType} (p : {poly R}) :
   p \is monic -> char_poly (companionmx p) = p.
Proof.
pose D n : 'M[{poly R}]_n := \matrix_(i, j)
   ('X *+ (i == j.+1 :> nat) - ((i == j)%:R)%:P).
have detD n : \det (D n) = (-1) ^+ n.
  elim: n => [|n IHn]; first by rewrite det_mx00.
  rewrite (expand_det_row _ ord0) big_ord_recl !mxE /= sub0r.
  rewrite big1 ?addr0; last by move=> i _; rewrite !mxE /= subrr mul0r.
  rewrite /cofactor mul1r [X in \det X](_ : _ = D _) ?IHn ?exprS//.
  by apply/matrixP=> i j; rewrite !mxE /= /bump !add1n eqSS.
elim/poly_ind: p => [|p c IHp].
  by rewrite monicE lead_coef0 eq_sym oner_eq0.
have [->|p_neq0] := eqVneq p 0.
  rewrite mul0r add0r monicE lead_coefC => /eqP->.
  by rewrite /companionmx /char_poly size_poly1 det_mx00.
rewrite monicE lead_coefDl ?lead_coefMX => [p_monic|]; last first.
  rewrite size_polyC size_mulX ?polyX_eq0// ltnS.
  by rewrite (leq_trans (leq_b1 _)) ?size_poly_gt0.
rewrite -[in RHS]IHp // /companionmx size_MXaddC (negPf p_neq0) /=.
rewrite /char_poly polySpred //.
have [->|spV1_gt0] := posnP (size p).-1.
  rewrite [X in \det X]mx11_scalar det_scalar1 !mxE ?eqxx det_mx00.
  by rewrite mul1r -horner_coef0 hornerMXaddC mulr0 add0r rmorphN opprK.
rewrite (expand_det_col _ ord0) /= -[(size p).-1]prednK //.
rewrite big_ord_recr big_ord_recl/= big1 ?add0r //=; last first.
  move=> i _; rewrite !mxE -val_eqE /= /bump leq0n add1n eqSS.
  by rewrite ltn_eqF ?subrr ?mul0r.
rewrite !mxE ?subnn -horner_coef0 /= hornerMXaddC.
rewrite !(eqxx, mulr0, add0r, addr0, subr0, rmorphN, opprK)/=.
rewrite mulrC /cofactor; congr (_ * 'X + _).
  rewrite /cofactor -signr_odd odd_add addbb mul1r; congr (\det _).
  apply/matrixP => i j; rewrite !mxE -val_eqE coefD coefMX coefC.
  by rewrite /= /bump /= !add1n !eqSS addr0.
rewrite /cofactor [X in \det X](_ : _ = D _).
  by rewrite detD /= addn0 -signr_odd -signr_addb addbb mulr1.
apply/matrixP=> i j; rewrite !mxE -!val_eqE /= /bump /=.
by rewrite leqNgt ltn_ord add0n add1n [_ == _.-2.+1]ltn_eqF.
Qed.

Lemma mulmx_delta_companion (R : ringType) (p : seq R)
  (i: 'I_(size p).-1) (i_small : i.+1 < (size p).-1):
  delta_mx 0 i *m companionmx p = delta_mx 0 (Ordinal i_small) :> 'rV__.
Proof.
apply/rowP => j; rewrite !mxE (bigD1 i) //= ?(=^~val_eqE, mxE) /= eqxx mul1r.
rewrite ltn_eqF ?big1 ?addr0 1?eq_sym //; last first.
  by rewrite -ltnS prednK // (leq_trans  _ i_small).
by move=> k /negPf ki_eqF; rewrite !mxE eqxx ki_eqF mul0r.
Qed.

Section MinPoly.

Variables (F : fieldType) (n' : nat).
Local Notation n := n'.+1.
Variable A : 'M[F]_n.
Implicit Types p q : {poly F}.

Fact degree_mxminpoly_proof : exists d, \rank (powers_mx A d.+1) <= d.
Proof. by exists (n ^ 2)%N; rewrite rank_leq_col. Qed.
Definition degree_mxminpoly := ex_minn degree_mxminpoly_proof.
Local Notation d := degree_mxminpoly.
Local Notation Ad := (powers_mx A d).

Lemma mxminpoly_nonconstant : d > 0.
Proof.
rewrite /d; case: ex_minnP; case=> //; rewrite leqn0 mxrank_eq0; move/eqP.
move/row_matrixP; move/(_ 0); move/eqP; rewrite rowK row0 mxvec_eq0.
by rewrite -mxrank_eq0 mxrank1.
Qed.

Lemma minpoly_mx1 : (1%:M \in Ad)%MS.
Proof.
by apply: (eq_row_sub (Ordinal mxminpoly_nonconstant)); rewrite rowK.
Qed.

Lemma minpoly_mx_free : row_free Ad.
Proof.
have:= mxminpoly_nonconstant; rewrite /d; case: ex_minnP; case=> // d' _.
move/(_ d'); move/implyP; rewrite ltnn implybF -ltnS ltn_neqAle.
by rewrite rank_leq_row andbT negbK.
Qed.

Lemma horner_mx_mem p : (horner_mx A p \in Ad)%MS.
Proof.
elim/poly_ind: p => [|p a IHp]; first by rewrite rmorph0 // linear0 sub0mx.
rewrite rmorphD rmorphM /= horner_mx_C horner_mx_X.
rewrite addrC -scalemx1 linearP /= -(mul_vec_lin (mulmxr_linear _ A)).
case/submxP: IHp => u ->{p}.
have: (powers_mx A (1 + d) <= Ad)%MS.
  rewrite -(geq_leqif (mxrank_leqif_sup _)).
    by rewrite (eqnP minpoly_mx_free) /d; case: ex_minnP.
  rewrite addnC; apply/row_subP=> i.
  by apply: eq_row_sub (lshift 1 i) _; rewrite !rowK.
apply: submx_trans; rewrite addmx_sub ?scalemx_sub //.
  by apply: (eq_row_sub 0); rewrite rowK.
rewrite -mulmxA mulmx_sub {u}//; apply/row_subP=> i.
rewrite row_mul rowK mul_vec_lin /= mulmxE -exprSr.
by apply: (eq_row_sub (rshift 1 i)); rewrite rowK.
Qed.

Definition mx_inv_horner B := rVpoly (mxvec B *m pinvmx Ad).

Lemma mx_inv_horner0 :  mx_inv_horner 0 = 0.
Proof. by rewrite /mx_inv_horner !(linear0, mul0mx). Qed.

Lemma mx_inv_hornerK B : (B \in Ad)%MS -> horner_mx A (mx_inv_horner B) = B.
Proof. by move=> sBAd; rewrite horner_rVpoly mulmxKpV ?mxvecK. Qed.

Lemma minpoly_mxM B C : (B \in Ad -> C \in Ad -> B * C \in Ad)%MS.
Proof.
move=> AdB AdC; rewrite -(mx_inv_hornerK AdB) -(mx_inv_hornerK AdC).
by rewrite -rmorphM ?horner_mx_mem.
Qed.

Lemma minpoly_mx_ring : mxring Ad.
Proof.
apply/andP; split; first by apply/mulsmx_subP; apply: minpoly_mxM.
apply/mxring_idP; exists 1%:M; split=> *; rewrite ?mulmx1 ?mul1mx //.
  by rewrite -mxrank_eq0 mxrank1.
exact: minpoly_mx1.
Qed.

Definition mxminpoly := 'X^d - mx_inv_horner (A ^+ d).
Local Notation p_A := mxminpoly.

Lemma size_mxminpoly : size p_A = d.+1.
Proof. by rewrite size_addl ?size_polyXn // size_opp ltnS size_poly. Qed.

Lemma mxminpoly_monic : p_A \is monic.
Proof.
rewrite monicE /lead_coef size_mxminpoly coefB coefXn eqxx /=.
by rewrite nth_default ?size_poly // subr0.
Qed.

Lemma size_mod_mxminpoly p : size (p %% p_A) <= d.
Proof.
by rewrite -ltnS -size_mxminpoly ltn_modp // -size_poly_eq0 size_mxminpoly.
Qed.

Lemma mx_root_minpoly : horner_mx A p_A = 0.
Proof.
rewrite rmorphB -{3}(horner_mx_X A) -rmorphX /=.
by rewrite mx_inv_hornerK ?subrr ?horner_mx_mem.
Qed.

Lemma horner_rVpolyK (u : 'rV_d) :
  mx_inv_horner (horner_mx A (rVpoly u)) = rVpoly u.
Proof.
congr rVpoly; rewrite horner_rVpoly vec_mxK.
by apply: (row_free_inj minpoly_mx_free); rewrite mulmxKpV ?submxMl.
Qed.

Lemma horner_mxK p : mx_inv_horner (horner_mx A p) = p %% p_A.
Proof.
rewrite {1}(Pdiv.IdomainMonic.divp_eq mxminpoly_monic p) rmorphD rmorphM /=.
rewrite mx_root_minpoly mulr0 add0r.
by rewrite -(poly_rV_K (size_mod_mxminpoly _)) horner_rVpolyK.
Qed.

Lemma mxminpoly_min p : horner_mx A p = 0 -> p_A %| p.
Proof. by move=> pA0; rewrite /dvdp -horner_mxK pA0 mx_inv_horner0. Qed.

Lemma horner_rVpoly_inj : injective (horner_mx A \o rVpoly : 'rV_d -> 'M_n).
Proof.
apply: can_inj (poly_rV \o mx_inv_horner) _ => u /=.
by rewrite horner_rVpolyK rVpolyK.
Qed.

Lemma mxminpoly_linear_is_scalar : (d <= 1) = is_scalar_mx A.
Proof.
have scalP := has_non_scalar_mxP minpoly_mx1.
rewrite leqNgt -(eqnP minpoly_mx_free); apply/scalP/idP=> [|[[B]]].
  case scalA: (is_scalar_mx A); [by right | left].
  by exists A; rewrite ?scalA // -{1}(horner_mx_X A) horner_mx_mem.
move/mx_inv_hornerK=> <- nsB; case/is_scalar_mxP=> a defA; case/negP: nsB.
move: {B}(_ B); apply: poly_ind => [|p c].
  by rewrite rmorph0 ?mx0_is_scalar.
rewrite rmorphD ?rmorphM /= horner_mx_X defA; case/is_scalar_mxP=> b ->.
by rewrite -rmorphM horner_mx_C -rmorphD /= scalar_mx_is_scalar.
Qed.

Lemma mxminpoly_dvd_char : p_A %| char_poly A.
Proof. by apply: mxminpoly_min; apply: Cayley_Hamilton. Qed.

Lemma eigenvalue_root_min a : eigenvalue A a = root p_A a.
Proof.
apply/idP/idP=> Aa; last first.
  rewrite eigenvalue_root_char !root_factor_theorem in Aa *.
  exact: dvdp_trans Aa mxminpoly_dvd_char.
have{Aa} [v Av_av v_nz] := eigenvalueP Aa.
apply: contraR v_nz => pa_nz; rewrite -{pa_nz}(eqmx_eq0 (eqmx_scale _ pa_nz)).
apply/eqP; rewrite -(mulmx0 _ v) -mx_root_minpoly.
elim/poly_ind: p_A => [|p c IHp].
  by rewrite rmorph0 horner0 scale0r mulmx0.
rewrite !hornerE rmorphD rmorphM /= horner_mx_X horner_mx_C scalerDl.
by rewrite -scalerA mulmxDr mul_mx_scalar mulmxA -IHp -scalemxAl Av_av.
Qed.

End MinPoly.

Prenex Implicits degree_mxminpoly mxminpoly mx_inv_horner.

Arguments mx_inv_hornerK {F n' A} [B] AnB.
Arguments horner_rVpoly_inj {F n' A} [u1 u2] eq_u12A : rename.
          
(* Parametricity. *)
Section MapRingMatrix.

Variables (aR rR : ringType) (f : {rmorphism aR -> rR}).
Local Notation "A ^f" := (map_mx (GRing.RMorphism.apply f) A) : ring_scope.
Local Notation fp := (map_poly (GRing.RMorphism.apply f)).
Variables (d n : nat) (A : 'M[aR]_n).

Lemma map_rVpoly (u : 'rV_d) : fp (rVpoly u) = rVpoly u^f.
Proof.
apply/polyP=> k; rewrite coef_map !coef_rVpoly.
by case: (insub k) => [i|]; rewrite /=  ?rmorph0 // mxE.
Qed.

Lemma map_poly_rV p : (poly_rV p)^f = poly_rV (fp p) :> 'rV_d.
Proof. by apply/rowP=> j; rewrite !mxE coef_map. Qed.

Lemma map_char_poly_mx : map_mx fp (char_poly_mx A) = char_poly_mx A^f.
Proof.
rewrite raddfB /= map_scalar_mx /= map_polyX; congr (_ - _).
by apply/matrixP=> i j; rewrite !mxE map_polyC.
Qed.

Lemma map_char_poly : fp (char_poly A) = char_poly A^f.
Proof. by rewrite -det_map_mx map_char_poly_mx. Qed.

End MapRingMatrix.

Section MapResultant.

Lemma map_resultant (aR rR : ringType) (f : {rmorphism {poly aR} -> rR}) p q :
    f (lead_coef p) != 0 -> f (lead_coef q) != 0 ->
  f (resultant p q)= resultant (map_poly f p) (map_poly f q).
Proof.
move=> nz_fp nz_fq; rewrite /resultant /Sylvester_mx !size_map_poly_id0 //.
rewrite -det_map_mx /= map_col_mx; congr (\det (col_mx _ _));
  by apply: map_lin1_mx => v; rewrite map_poly_rV rmorphM /= map_rVpoly.
Qed.

End MapResultant.

Section MapComRing.

Variables (aR rR : comRingType) (f : {rmorphism aR -> rR}).
Local Notation "A ^f" := (map_mx f A) : ring_scope.
Local Notation fp := (map_poly f).
Variables (n' : nat) (A : 'M[aR]_n'.+1).

Lemma map_powers_mx e : (powers_mx A e)^f = powers_mx A^f e.
Proof. by apply/row_matrixP=> i; rewrite -map_row !rowK map_mxvec rmorphX. Qed.

Lemma map_horner_mx p : (horner_mx A p)^f = horner_mx A^f (fp p).
Proof.
rewrite -[p](poly_rV_K (leqnn _)) map_rVpoly.
by rewrite !horner_rVpoly map_vec_mx map_mxM map_powers_mx.
Qed.

End MapComRing.

Section MapField.

Variables (aF rF : fieldType) (f : {rmorphism aF -> rF}).
Local Notation "A ^f" := (map_mx f A) : ring_scope.
Local Notation fp := (map_poly f).
Variables (n' : nat) (A : 'M[aF]_n'.+1) (p : {poly aF}).

Lemma map_mx_companion (e := congr1 predn (size_map_poly _ _)) :
  (companionmx p)^f = castmx (e, e) (companionmx (fp p)).
Proof.
apply/matrixP => i j; rewrite !(castmxE, mxE) /= (fun_if f).
by rewrite rmorphN coef_map size_map_poly rmorph_nat.
Qed.

Lemma companion_map_poly (e := esym (congr1 predn (size_map_poly _ _))) :
  companionmx (fp p) = castmx (e, e) (companionmx p)^f.
Proof. by rewrite map_mx_companion castmx_comp castmx_id. Qed.

Lemma degree_mxminpoly_map : degree_mxminpoly A^f = degree_mxminpoly A.
Proof. by apply: eq_ex_minn => e; rewrite -map_powers_mx mxrank_map. Qed.

Lemma mxminpoly_map : mxminpoly A^f = fp (mxminpoly A).
Proof.
rewrite rmorphB; congr (_ - _).
  by rewrite /= map_polyXn degree_mxminpoly_map.
rewrite degree_mxminpoly_map -rmorphX /=.
apply/polyP=> i; rewrite coef_map //= !coef_rVpoly degree_mxminpoly_map.
case/insub: i => [i|]; last by rewrite rmorph0.
by rewrite -map_powers_mx -map_pinvmx // -map_mxvec -map_mxM // mxE.
Qed.

Lemma map_mx_inv_horner u : fp (mx_inv_horner A u) = mx_inv_horner A^f u^f.
Proof.
rewrite map_rVpoly map_mxM map_mxvec map_pinvmx map_powers_mx.
by rewrite /mx_inv_horner degree_mxminpoly_map.
Qed.

End MapField.

Section IntegralOverRing.

Definition integralOver (R K : ringType) (RtoK : R -> K) (z : K) :=
  exists2 p, p \is monic & root (map_poly RtoK p) z.

Definition integralRange R K RtoK := forall z, @integralOver R K RtoK z.

Variables (B R K : ringType) (BtoR : B -> R) (RtoK : {rmorphism R -> K}).

Lemma integral_rmorph x :
  integralOver BtoR x -> integralOver (RtoK \o BtoR) (RtoK x).
Proof. by case=> p; exists p; rewrite // map_poly_comp rmorph_root. Qed.

Lemma integral_id x : integralOver RtoK (RtoK x).
Proof. by exists ('X - x%:P); rewrite ?monicXsubC ?rmorph_root ?root_XsubC. Qed.

Lemma integral_nat n : integralOver RtoK n%:R.
Proof. by rewrite -(rmorph_nat RtoK); apply: integral_id. Qed.

Lemma integral0 : integralOver RtoK 0. Proof. exact: (integral_nat 0). Qed.

Lemma integral1 : integralOver RtoK 1. Proof. exact: (integral_nat 1). Qed.

Lemma integral_poly (p : {poly K}) :
  (forall i, integralOver RtoK p`_i) <-> {in p : seq K, integralRange RtoK}.
Proof.
split=> intRp => [_ /(nthP 0)[i _ <-] // | i]; rewrite -[p]coefK coef_poly.
by case: ifP => [ltip | _]; [apply/intRp/mem_nth | apply: integral0].
Qed.

End IntegralOverRing.

Section IntegralOverComRing.

Variables (R K : comRingType) (RtoK : {rmorphism R -> K}).

Lemma integral_horner_root w (p q : {poly K}) :
    p \is monic -> root p w ->
    {in p : seq K, integralRange RtoK} -> {in q : seq K, integralRange RtoK} ->
  integralOver RtoK q.[w].
Proof.
move=> mon_p pw0 intRp intRq.
pose memR y := exists x, y = RtoK x.
have memRid x: memR (RtoK x) by exists x.
have memR_nat n: memR n%:R by rewrite -(rmorph_nat RtoK).
have [memR0 memR1]: memR 0 * memR 1 := (memR_nat 0%N, memR_nat 1%N).
have memRN1: memR (- 1) by exists (- 1); rewrite rmorphN1.
pose rVin (E : K -> Prop) n (a : 'rV[K]_n) := forall i, E (a 0 i).
pose pXin (E : K -> Prop) (r : {poly K}) := forall i, E r`_i.
pose memM E n (X : 'rV_n) y := exists a, rVin E n a /\ y = (a *m X^T) 0 0.
pose finM E S := exists n, exists X, forall y, memM E n X y <-> S y.
have tensorM E n1 n2 X Y: finM E (memM (memM E n2 Y) n1 X).
  exists (n1 * n2)%N, (mxvec (X^T *m Y)) => y.
  split=> [[a [Ea Dy]] | [a1 [/fin_all_exists[a /all_and2[Ea Da1]] ->]]].
    exists (Y *m (vec_mx a)^T); split=> [i|].
      exists (row i (vec_mx a)); split=> [j|]; first by rewrite !mxE; apply: Ea.
      by rewrite -row_mul -{1}[Y]trmxK -trmx_mul !mxE.
    by rewrite -[Y]trmxK -!trmx_mul mulmxA -mxvec_dotmul trmx_mul trmxK vec_mxK.
  exists (mxvec (\matrix_i a i)); split.
    by case/mxvec_indexP=> i j; rewrite mxvecE mxE; apply: Ea.
  rewrite -[mxvec _]trmxK -trmx_mul mxvec_dotmul -mulmxA trmx_mul !mxE.
  apply: eq_bigr => i _; rewrite Da1 !mxE; congr (_ * _).
  by apply: eq_bigr => j _; rewrite !mxE.
suffices [m [X [[u [_ Du]] idealM]]]: exists m,
  exists X, let M := memM memR m X in M 1 /\ forall y, M y -> M (q.[w] * y).
- do [set M := memM _ m X; move: q.[w] => z] in idealM *.
  have MX i: M (X 0 i).
    by exists (delta_mx 0 i); split=> [j|]; rewrite -?rowE !mxE.
  have /fin_all_exists[a /all_and2[Fa Da1]] i := idealM _ (MX i).
  have /fin_all_exists[r Dr] i := fin_all_exists (Fa i).
  pose A := \matrix_(i, j) r j i; pose B := z%:M - map_mx RtoK A.
  have XB0: X *m B = 0.
    apply/eqP; rewrite mulmxBr mul_mx_scalar subr_eq0; apply/eqP/rowP=> i.
    by rewrite !mxE Da1 mxE; apply: eq_bigr=> j _; rewrite !mxE mulrC Dr.
  exists (char_poly A); first exact: char_poly_monic.
  have: (\det B *: (u *m X^T)) 0 0 == 0.
    rewrite scalemxAr -linearZ -mul_mx_scalar -mul_mx_adj mulmxA XB0 /=.
    by rewrite mul0mx trmx0 mulmx0 mxE.
  rewrite mxE -Du mulr1 rootE -horner_evalE -!det_map_mx; congr (\det _ == 0).
  rewrite !raddfB /= !map_scalar_mx /= map_polyX horner_evalE hornerX.
  by apply/matrixP=> i j; rewrite !mxE map_polyC /horner_eval hornerC.
pose gen1 x E y := exists2 r, pXin E r & y = r.[x]; pose gen := foldr gen1 memR.
have gen1S (E : K -> Prop) x y: E 0 -> E y -> gen1 x E y.
  by exists y%:P => [i|]; rewrite ?hornerC ?coefC //; case: ifP.
have genR S y: memR y -> gen S y.
  by elim: S => //= x S IH in y * => /IH; apply: gen1S; apply: IH.
have gen0 := genR _ 0 memR0; have gen_1 := genR _ 1 memR1.
have{gen1S} genS S y: y \in S -> gen S y.
  elim: S => //= x S IH /predU1P[-> | /IH//]; last exact: gen1S.
  by exists 'X => [i|]; rewrite ?hornerX // coefX; apply: genR.
pose propD (R : K -> Prop) := forall x y, R x -> R y -> R (x + y).
have memRD: propD memR.
  by move=> _ _ [a ->] [b ->]; exists (a + b); rewrite rmorphD.
have genD S: propD (gen S).
  elim: S => //= x S IH _ _ [r1 Sr1 ->] [r2 Sr2 ->]; rewrite -hornerD.
  by exists (r1 + r2) => // i; rewrite coefD; apply: IH.
have gen_sum S := big_ind _ (gen0 S) (genD S).
pose propM (R : K -> Prop) := forall x y, R x -> R y -> R (x * y).
have memRM: propM memR.
  by move=> _ _ [a ->] [b ->]; exists (a * b); rewrite rmorphM.
have genM S: propM (gen S).
  elim: S => //= x S IH _ _ [r1 Sr1 ->] [r2 Sr2 ->]; rewrite -hornerM.
  by exists (r1 * r2) => // i; rewrite coefM; apply: gen_sum => j _; apply: IH.
have gen_horner S r y: pXin (gen S) r -> gen S y -> gen S r.[y].
  move=> Sq Sy; rewrite horner_coef; apply: gen_sum => [[i _] /= _].
  by elim: {2}i => [|n IHn]; rewrite ?mulr1 // exprSr mulrA; apply: genM.
pose S := w :: q ++ p; suffices [m [X defX]]: finM memR (gen S).
  exists m, X => M; split=> [|y /defX Xy]; first exact/defX.
  apply/defX/genM => //; apply: gen_horner => // [i|]; last exact/genS/mem_head.
  rewrite -[q]coefK coef_poly; case: ifP => // lt_i_q.
  by apply: genS; rewrite inE mem_cat mem_nth ?orbT.
pose intR R y := exists r, [/\ r \is monic, root r y & pXin R r].
pose fix genI s := if s is y :: s1 then intR (gen s1) y /\ genI s1 else True.
have{mon_p pw0 intRp intRq}: genI S.
  split; set S1 := _ ++ _; first exists p.
    split=> // i; rewrite -[p]coefK coef_poly; case: ifP => // lt_i_p.
    by apply: genS; rewrite mem_cat orbC mem_nth.
  have: all (mem S1) S1 by apply/allP.
  elim: {-1}S1 => //= y S2 IH /andP[S1y S12]; split; last exact: IH.
  have{q S S1 IH S1y S12 intRp intRq} [q mon_q qx0]: integralOver RtoK y.
    by move: S1y; rewrite mem_cat => /orP[]; [apply: intRq | apply: intRp].
  exists (map_poly RtoK q); split=> // [|i]; first exact: monic_map.
  by rewrite coef_map /=; apply: genR.
elim: {w p q}S => /= [_|x S IH [[p [mon_p px0 Sp]] /IH{IH}[m2 [X2 defS]]]].
  exists 1%N, 1 => y; split=> [[a [Fa ->]] | Fy].
    by rewrite tr_scalar_mx mulmx1; apply: Fa.
  by exists y%:M; split=> [i|]; rewrite 1?ord1 ?tr_scalar_mx ?mulmx1 mxE.
pose m1 := (size p).-1; pose X1 := \row_(i < m1) x ^+ i.
have [m [X defM]] := tensorM memR m1 m2 X1 X2; set M := memM _ _ _ in defM.
exists m, X => y; rewrite -/M; split=> [/defM[a [M2a]] | [q Sq]] -> {y}.
  exists (rVpoly a) => [i|].
    by rewrite coef_rVpoly; case/insub: i => // i; apply/defS/M2a.
  rewrite mxE (horner_coef_wide _ (size_poly _ _)) -/(rVpoly a).
  by apply: eq_bigr => i _; rewrite coef_rVpoly_ord !mxE.
have M_0: M 0 by exists 0; split=> [i|]; rewrite ?mul0mx mxE.
have M_D: propD M.
  move=> _ _ [a [Fa ->]] [b [Fb ->]]; exists (a + b).
  by rewrite mulmxDl !mxE; split=> // i; rewrite mxE; apply: memRD.
have{M_0 M_D} Msum := big_ind _ M_0 M_D.
rewrite horner_coef; apply: (Msum) => i _; case: i q`_i {Sq}(Sq i) => /=.
elim: {q}(size q) => // n IHn i i_le_n y Sy.
have [i_lt_m1 | m1_le_i] := ltnP i m1.
  apply/defM; exists (y *: delta_mx 0 (Ordinal i_lt_m1)); split=> [j|].
    by apply/defS; rewrite !mxE /= mulr_natr; case: eqP.
  by rewrite -scalemxAl -rowE !mxE.
rewrite -(subnK m1_le_i) exprD -[x ^+ m1]subr0 -(rootP px0) horner_coef.
rewrite polySpred ?monic_neq0 // -/m1 big_ord_recr /= -lead_coefE.
rewrite opprD addrC (monicP mon_p) mul1r subrK !mulrN -mulNr !mulr_sumr.
apply: Msum => j _; rewrite mulrA mulrACA -exprD; apply: IHn.
  by rewrite -addnS addnC addnBA // leq_subLR leq_add.
by rewrite -mulN1r; do 2!apply: (genM) => //; apply: genR.
Qed.

Lemma integral_root_monic u p :
    p \is monic -> root p u -> {in p : seq K, integralRange RtoK} ->
  integralOver RtoK u.
Proof.
move=> mon_p pu0 intRp; rewrite -[u]hornerX.
apply: integral_horner_root mon_p pu0 intRp _.
by apply/integral_poly => i; rewrite coefX; apply: integral_nat.
Qed.

Hint Resolve (integral0 RtoK) (integral1 RtoK) (@monicXsubC K) : core.

Let XsubC0 (u : K) : root ('X - u%:P) u. Proof. by rewrite root_XsubC. Qed.
Let intR_XsubC u :
  integralOver RtoK (- u) -> {in 'X - u%:P : seq K, integralRange RtoK}.
Proof. by move=> intRu v; rewrite polyseqXsubC !inE => /pred2P[]->. Qed.

Lemma integral_opp u : integralOver RtoK u -> integralOver RtoK (- u).
Proof. by rewrite -{1}[u]opprK => /intR_XsubC/integral_root_monic; apply. Qed.

Lemma integral_horner (p : {poly K}) u :
    {in p : seq K, integralRange RtoK} -> integralOver RtoK u ->
  integralOver RtoK p.[u].
Proof. by move=> ? /integral_opp/intR_XsubC/integral_horner_root; apply. Qed.

Lemma integral_sub u v :
  integralOver RtoK u -> integralOver RtoK v -> integralOver RtoK (u - v).
Proof.
move=> intRu /integral_opp/intR_XsubC/integral_horner/(_ intRu).
by rewrite !hornerE.
Qed.

Lemma integral_add u v :
  integralOver RtoK u -> integralOver RtoK v -> integralOver RtoK (u + v).
Proof. by rewrite -{2}[v]opprK => intRu /integral_opp; apply: integral_sub. Qed.

Lemma integral_mul u v :
  integralOver RtoK u -> integralOver RtoK v -> integralOver RtoK (u * v).
Proof.
rewrite -{2}[v]hornerX -hornerZ => intRu; apply: integral_horner.
by apply/integral_poly=> i; rewrite coefZ coefX mulr_natr mulrb; case: ifP.
Qed.

End IntegralOverComRing.

Section IntegralOverField.

Variables (F E : fieldType) (FtoE : {rmorphism F -> E}).

Definition algebraicOver (fFtoE : F -> E) u :=
  exists2 p, p != 0 & root (map_poly fFtoE p) u.

Notation mk_mon p := ((lead_coef p)^-1 *: p).

Lemma integral_algebraic u : algebraicOver FtoE u <-> integralOver FtoE u.
Proof.
split=> [] [p p_nz pu0]; last by exists p; rewrite ?monic_neq0.
exists (mk_mon p); first by rewrite monicE lead_coefZ mulVf ?lead_coef_eq0.
by rewrite linearZ rootE hornerZ (rootP pu0) mulr0.
Qed.

Lemma algebraic_id a : algebraicOver FtoE (FtoE a).
Proof. exact/integral_algebraic/integral_id. Qed.

Lemma algebraic0 : algebraicOver FtoE 0.
Proof. exact/integral_algebraic/integral0. Qed.

Lemma algebraic1 : algebraicOver FtoE 1.
Proof. exact/integral_algebraic/integral1. Qed.

Lemma algebraic_opp x : algebraicOver FtoE x -> algebraicOver FtoE (- x).
Proof. by move/integral_algebraic/integral_opp/integral_algebraic. Qed.

Lemma algebraic_add x y :
  algebraicOver FtoE x -> algebraicOver FtoE y -> algebraicOver FtoE (x + y).
Proof.
move/integral_algebraic=> intFx /integral_algebraic intFy.
exact/integral_algebraic/integral_add.
Qed.

Lemma algebraic_sub x y :
  algebraicOver FtoE x -> algebraicOver FtoE y -> algebraicOver FtoE (x - y).
Proof. by move=> algFx /algebraic_opp; apply: algebraic_add. Qed.

Lemma algebraic_mul x y :
  algebraicOver FtoE x -> algebraicOver FtoE y -> algebraicOver FtoE (x * y).
Proof.
move/integral_algebraic=> intFx /integral_algebraic intFy.
exact/integral_algebraic/integral_mul.
Qed.

Lemma algebraic_inv u : algebraicOver FtoE u -> algebraicOver FtoE u^-1.
Proof.
have [-> | /expf_neq0 nz_u_n] := eqVneq u 0; first by rewrite invr0.
case=> p nz_p pu0; exists (Poly (rev p)).
  apply/eqP=> /polyP/(_ 0%N); rewrite coef_Poly coef0 nth_rev ?size_poly_gt0 //.
  by apply/eqP; rewrite subn1 lead_coef_eq0.
apply/eqP/(mulfI (nz_u_n (size p).-1)); rewrite mulr0 -(rootP pu0).
rewrite (@horner_coef_wide _ (size p)); last first.
  by rewrite size_map_poly -(size_rev p) size_Poly.
rewrite horner_coef mulr_sumr size_map_poly.
rewrite [rhs in _ = rhs](reindex_inj rev_ord_inj) /=.
apply: eq_bigr => i _; rewrite !coef_map coef_Poly nth_rev // mulrCA.
by congr (_ * _); rewrite -{1}(subnKC (valP i)) addSn addnC exprD exprVn ?mulfK.
Qed.

Lemma algebraic_div x y :
  algebraicOver FtoE x -> algebraicOver FtoE y -> algebraicOver FtoE (x / y).
Proof. by move=> algFx /algebraic_inv; apply: algebraic_mul. Qed.

Lemma integral_inv x : integralOver FtoE x -> integralOver FtoE x^-1.
Proof. by move/integral_algebraic/algebraic_inv/integral_algebraic. Qed.

Lemma integral_div x y :
  integralOver FtoE x -> integralOver FtoE y -> integralOver FtoE (x / y).
Proof. by move=> algFx /integral_inv; apply: integral_mul. Qed.

Lemma integral_root p u :
    p != 0 -> root p u -> {in p : seq E, integralRange FtoE} ->
  integralOver FtoE u.
Proof.
move=> nz_p pu0 algFp.
have mon_p1: mk_mon p \is monic.
  by rewrite monicE lead_coefZ mulVf ?lead_coef_eq0.
have p1u0: root (mk_mon p) u by rewrite rootE hornerZ (rootP pu0) mulr0.
apply: integral_root_monic mon_p1 p1u0 _ => _ /(nthP 0)[i ltip <-].
rewrite coefZ mulrC; rewrite size_scale ?invr_eq0 ?lead_coef_eq0 // in ltip.
by apply: integral_div; apply/algFp/mem_nth; rewrite -?polySpred.
Qed.

End IntegralOverField.

(* Lifting term, formula, envs and eval to matrices. Wlog, and for the sake  *)
(* of simplicity, we only lift (tensor) envs to row vectors; we can always   *)
(* use mxvec/vec_mx to store and retrieve matrices.                          *)
(* We don't provide definitions for addition, subtraction, scaling, etc,     *)
(* because they have simple matrix expressions.                              *)
Module MatrixFormula.

Section MatrixFormula.

Variable F : fieldType.

Local Notation False := GRing.False.
Local Notation True := GRing.True.
Local Notation And := GRing.And (only parsing).
Local Notation Add := GRing.Add (only parsing).
Local Notation Bool b := (GRing.Bool b%bool).
Local Notation term := (GRing.term F).
Local Notation form := (GRing.formula F).
Local Notation eval := GRing.eval.
Local Notation holds := GRing.holds.
Local Notation qf_form := GRing.qf_form.
Local Notation qf_eval := GRing.qf_eval.

Definition eval_mx (e : seq F) := @map_mx term F (eval e).

Definition mx_term := @map_mx F term GRing.Const.

Lemma eval_mx_term e m n (A : 'M_(m, n)) : eval_mx e (mx_term A) = A.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Definition mulmx_term m n p (A : 'M[term]_(m, n)) (B : 'M_(n, p)) :=
  \matrix_(i, k) (\big[Add/0]_j (A i j * B j k))%T.

Lemma eval_mulmx e m n p (A : 'M[term]_(m, n)) (B : 'M_(n, p)) :
  eval_mx e (mulmx_term A B) = eval_mx e A *m eval_mx e B.
Proof.
apply/matrixP=> i k; rewrite !mxE /= ((big_morph (eval e)) 0 +%R) //=.
by apply: eq_bigr => j _; rewrite /= !mxE.
Qed.

Local Notation morphAnd f := ((big_morph f) true andb).

Let Schur m n (A : 'M[term]_(1 + m, 1 + n)) (a := A 0 0) :=
  \matrix_(i, j) (drsubmx A i j - a^-1 * dlsubmx A i 0%R * ursubmx A 0%R j)%T.

Fixpoint mxrank_form (r m n : nat) : 'M_(m, n) -> form :=
  match m, n return 'M_(m, n) -> form with
  | m'.+1, n'.+1 => fun A : 'M_(1 + m', 1 + n') =>
    let nzA k := A k.1 k.2 != 0 in
    let xSchur k := Schur (xrow k.1 0%R (xcol k.2 0%R A)) in
    let recf k := Bool (r > 0) /\ mxrank_form r.-1 (xSchur k) in
    GRing.Pick nzA recf (Bool (r == 0%N))
  | _, _ => fun _ => Bool (r == 0%N)
  end%T.

Lemma mxrank_form_qf r m n (A : 'M_(m, n)) : qf_form (mxrank_form r A).
Proof.
by elim: m r n A => [|m IHm] r [|n] A //=; rewrite GRing.Pick_form_qf /=.
Qed.

Lemma eval_mxrank e r m n (A : 'M_(m, n)) :
  qf_eval e (mxrank_form r A) = (\rank (eval_mx e A) == r).
Proof.
elim: m r n A => [|m IHm] r [|n] A /=; try by case r.
rewrite GRing.eval_Pick /mxrank unlock /=; set pf := fun _ => _.
rewrite -(@eq_pick _ pf) => [|k]; rewrite {}/pf ?mxE // eq_sym.
case: pick => [[i j]|] //=; set B := _ - _; have:= mxrankE B.
case: (Gaussian_elimination B) r => [[_ _] _] [|r] //= <-; rewrite {}IHm eqSS.
by congr (\rank _ == r); apply/matrixP=> k l; rewrite !(mxE, big_ord1) !tpermR.
Qed.

Lemma eval_vec_mx e m n (u : 'rV_(m * n)) :
  eval_mx e (vec_mx u) = vec_mx (eval_mx e u).
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma eval_mxvec e m n (A : 'M_(m, n)) :
  eval_mx e (mxvec A) = mxvec (eval_mx e A).
Proof. by rewrite -{2}[A]mxvecK eval_vec_mx vec_mxK. Qed.

Section Subsetmx.

Variables (m1 m2 n : nat) (A : 'M[term]_(m1, n)) (B : 'M[term]_(m2, n)).

Definition submx_form :=
  \big[And/True]_(r < n.+1) (mxrank_form r (col_mx A B) ==> mxrank_form r B)%T.

Lemma eval_col_mx e :
  eval_mx e (col_mx A B) = col_mx (eval_mx e A) (eval_mx e B).
Proof. by apply/matrixP=> i j; do 2![rewrite !mxE //; case: split => ?]. Qed.

Lemma submx_form_qf : qf_form submx_form.
Proof.
by rewrite (morphAnd (@qf_form _)) ?big1 //= => r _; rewrite !mxrank_form_qf.
Qed.

Lemma eval_submx e : qf_eval e submx_form = (eval_mx e A <= eval_mx e B)%MS.
Proof.
rewrite (morphAnd (qf_eval e)) //= big_andE /=.
apply/forallP/idP=> /= [|sAB d]; last first.
  rewrite !eval_mxrank eval_col_mx -addsmxE; apply/implyP=> /eqP <-.
  by rewrite mxrank_leqif_sup ?addsmxSr // addsmx_sub sAB /=.
move/(_ (inord (\rank (eval_mx e (col_mx A B))))).
rewrite inordK ?ltnS ?rank_leq_col // !eval_mxrank eqxx /= eval_col_mx.
by rewrite -addsmxE mxrank_leqif_sup ?addsmxSr // addsmx_sub; case/andP.
Qed.

End Subsetmx.

Section Env.

Variable d : nat.

Definition seq_of_rV (v : 'rV_d) : seq F := fgraph [ffun i => v 0 i].

Lemma size_seq_of_rV v : size (seq_of_rV v) = d.
Proof. by rewrite tuple.size_tuple card_ord. Qed.

Lemma nth_seq_of_rV x0 v (i : 'I_d) : nth x0 (seq_of_rV v) i = v 0 i.
Proof. by rewrite nth_fgraph_ord ffunE. Qed.

Definition row_var k : 'rV[term]_d := \row_i ('X_(k * d + i))%T.

Definition row_env (e : seq 'rV_d) := flatten (map seq_of_rV e).

Lemma nth_row_env e k (i : 'I_d) : (row_env e)`_(k * d + i) = e`_k 0 i.
Proof.
elim: e k => [|v e IHe] k; first by rewrite !nth_nil mxE.
rewrite /row_env /= nth_cat size_seq_of_rV.
case: k => [|k]; first by rewrite (valP i) nth_seq_of_rV.
by rewrite mulSn -addnA -if_neg -leqNgt leq_addr addKn IHe.
Qed.

Lemma eval_row_var e k : eval_mx (row_env e) (row_var k) = e`_k :> 'rV_d.
Proof. by apply/rowP=> i; rewrite !mxE /= nth_row_env. Qed.

Definition Exists_row_form k (f : form) :=
  foldr GRing.Exists f (codom (fun i : 'I_d => k * d + i)%N).

Lemma Exists_rowP e k f :
  d > 0 ->
   ((exists v : 'rV[F]_d, holds (row_env (set_nth 0 e k v)) f)
      <-> holds (row_env e) (Exists_row_form k f)).
Proof.
move=> d_gt0; pose i_ j := Ordinal (ltn_pmod j d_gt0).
have d_eq j: (j = j %/ d * d + i_ j)%N := divn_eq j d.
split=> [[v f_v] | ]; last case/GRing.foldExistsP=> e' ee' f_e'.
  apply/GRing.foldExistsP; exists (row_env (set_nth 0 e k v)) => {f f_v}// j.
  rewrite [j]d_eq !nth_row_env nth_set_nth /=; case: eqP => // ->.
  by case/imageP; exists (i_ j).
exists (\row_i e'`_(k * d + i)); apply: eq_holds f_e' => j /=.
move/(_ j): ee'; rewrite [j]d_eq !nth_row_env nth_set_nth /=.
case: eqP => [-> | ne_j_k -> //]; first by rewrite mxE.
apply/mapP=> [[r lt_r_d]]; rewrite -d_eq => def_j; case: ne_j_k.
by rewrite def_j divnMDl // divn_small ?addn0.
Qed.

End Env.

End MatrixFormula.

End MatrixFormula.

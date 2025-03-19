(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice seq.
From mathcomp Require Import div fintype tuple finfun bigop fingroup perm.
From mathcomp Require Import ssralg zmodp matrix mxalgebra poly polydiv.

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
(*    kermxpoly g p == the kernel of p(g)                                     *)
(*  geigenspace g a == the generalized eigenspace of g for eigenvalue a       *)
(*                  := kermxpoly g ('X ^ n - a%:P) where g : 'M_n             *)
(*  eigenpoly g p <=> p is an eigen polynomial for g, i.e. kermxpoly g p != 0 *)
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
(*    conjmx V f := V *m f *m pinvmx V                                        *)
(*               == the conjugation of f by V, i.e. "the" matrix of f         *)
(*                  in the basis of row vectors of V.                         *)
(*                  Although this makes sense only when f stabilizes V,       *)
(*                  the definition can be stated more generally.              *)
(*  restrictmx V := conjmx (row_base V)                                       *)
(* A ~_P {in S'} == where P is a base change matrix, A is a matrix, and S     *)
(*                  is a boolean predicate representing a set of matrices,    *)
(*                  this states that conjmx P A is in S,                      *)
(*                  which means A is similar to a matrix in S.                *)
(* From the latter, we derive several related notions:                        *)
(*       A ~_P B := A ~_P {in pred1 B}                                        *)
(*                  A is similar to B, with base change matrix P              *)
(*  A ~_{in S} B := exists P, P \in S /\ A ~_P B                              *)
(*               == A is similar to B,   with a base change matrix in S       *)
(*   A ~_{in S} {in S'} := exists P, P \in S /\ A ~_P {in S'}                 *)
(*                      == A is similar to a matrix in the class S',          *)
(*                         with a base change matrix in S                     *)
(* all_simmx_in S As S' == all the matrices in the sequence As are            *)
(*                         similar to some matrix in the predicate S',        *)
(*                         with a base change matrix in S.                    *)
(*                                                                            *)
(* We also specialize the class S' to diagonalizability:                      *)
(*    diagonalizable_for P A := A ~_P {in is_diag_mx}.                        *)
(*     diagonalizable_in S A := A ~_{in S} {in is_diag_mx}.                   *)
(*          diagonalizable A := diagonalizable_in unitmx A.                   *)
(*  codiagonalizable_in S As := all_simmx_in S As is_diag_mx.                 *)
(*       codiagonalizable As := codiagonalizable_in unitmx As.                *)
(*                                                                            *)
(* The main results in diagnonalization theory are:                           *)
(* - diagonalizablePeigen:                                                    *)
(*     a matrix is diagonalizable iff there is a sequence                     *)
(*     of scalars r, such that the sum of the associated                      *)
(*     eigenspaces is full.                                                   *)
(* - diagonalizableP:                                                         *)
(*     a matrix is diagonalizable iff its minimal polynomial                  *)
(*     divides a split polynomial with simple roots.                          *)
(* - codiagonalizableP:                                                       *)
(*     a sequence of matrices are diagonalizable in the same basis            *)
(*     iff they are all diagonalizable and commute pairwize.                  *)
(*                                                                            *)
(* Naming conventions:                                                        *)
(* - p, q are polynomials                                                     *)
(* - A, B, C are matrices                                                     *)
(* - f, g are matrices that are viewed as linear maps                         *)
(* - V, W are matrices that are viewed as subspaces                           *)
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

Variables (R : nzRingType) (d : nat).
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
HB.instance Definition _ := GRing.isSemilinear.Build R {poly R} 'rV_d _ poly_rV
  (GRing.semilinear_linear poly_rV_is_linear).

Lemma rVpoly_is_linear : linear rVpoly.
Proof.
move=> a u v; apply/polyP=> k; rewrite coefD coefZ !coef_rVpoly.
by case: insubP => [i _ _ | _]; rewrite ?mxE // mulr0 addr0.
Qed.
HB.instance Definition _ := GRing.isSemilinear.Build R 'rV_d {poly R} _ rVpoly
  (GRing.semilinear_linear rVpoly_is_linear).

End RowPoly.

Prenex Implicits rVpoly rVpolyK.
Arguments poly_rV {R d}.
Arguments poly_rV_K {R d} [p] le_p_d.

Section Resultant.

Variables (R : nzRingType) (p q : {poly R}).

Let dS := ((size q).-1 + (size p).-1)%N.
Local Notation band r := (lin1_mx (poly_rV \o r \o* rVpoly)).

Definition Sylvester_mx : 'M[R]_dS := col_mx (band p) (band q).

Lemma Sylvester_mxE (i j : 'I_dS) :
  let S_ r k := r`_(j - k) *+ (k <= j) in
  Sylvester_mx i j = match split i with inl k => S_ p k | inr k => S_ q k end.
Proof.
move=> S_ /[1!mxE]; case: {i}(split i) => i /[!mxE]/=;
  by rewrite rVpoly_delta coefXnM ltnNge if_neg -mulrb.
Qed.

Definition resultant := \det Sylvester_mx.

End Resultant.

Prenex Implicits Sylvester_mx resultant.

Lemma resultant_in_ideal (R : comNzRingType) (p q : {poly R}) :
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
    rewrite rmorphM /= rmorph_sign -det_map_mx; congr (_ * \det _).
    by apply/matrixP=> i' j'; rewrite !mxE.
  apply: leq_trans (size_polyMleq _ _) (leq_trans _ (valP i)).
  by rewrite size_polyC size_polyXn addnS /= -add1n leq_add2r leq_b1.
transitivity (\det Ss); last first.
  rewrite (expand_det_col Ss j0) big_split_ord !big_distrl /=.
  by congr (_ + _); apply: eq_bigr => i _;
    rewrite mxE eqxx (col_mxEu, col_mxEd) !mxE mulrC mulrA mulrAC.
pose S_ j1 := map_mx polyC (\matrix_(i, j) S i (if j == j0 then j1 else j)).
pose Ss0_ i dj := \poly_(j < dj) S i (insubd j0 j).
pose Ss_ dj := \matrix_(i, j) (if j == j0 then Ss0_ i dj else (S i j)%:P).
have{Ss u} ->: Ss = Ss_ dS.
  apply/matrixP=> i j; rewrite mxE [in RHS]mxE; case: (j == j0) => {j}//.
  apply/polyP=> k; rewrite coef_poly Sylvester_mxE mxE.
  have [k_ge_dS | k_lt_dS] := leqP dS k.
    case: (split i) => {}i; rewrite !mxE coefMXn;
    case: ifP => // /negbT; rewrite -ltnNge ltnS => hi.
      apply: (leq_sizeP _ _ (leqnn (size p))); rewrite -(ltn_predK p_nc).
      by rewrite ltn_subRL (leq_trans _ k_ge_dS) // ltn_add2r.
    - apply: (leq_sizeP _ _ (leqnn (size q))); rewrite -(ltn_predK q_nc).
      by rewrite ltn_subRL (leq_trans _ k_ge_dS) // addnC ltn_add2l.
  by rewrite insubdK //; case: (split i) => {}i;
     rewrite !mxE coefMXn; case: leqP.
case: (ubnPgeq dS) (dS_gt0); elim=> // dj IHj ltjS _; pose j1 := Ordinal ltjS.
pose rj0T (A : 'M[{poly R}]_dS) := row j0 A^T.
have: rj0T (Ss_ dj.+1) = 'X^dj *: rj0T (S_ j1) + 1 *: rj0T (Ss_ dj).
  apply/rowP=> i; apply/polyP=> k; rewrite scale1r !(Sylvester_mxE, mxE) eqxx.
  rewrite coefD coefXnM coefC !coef_poly ltnS subn_eq0 ltn_neqAle andbC.
  have [k_le_dj | k_gt_dj] /= := leqP k dj; last by rewrite addr0.
  rewrite Sylvester_mxE insubdK; last exact: leq_ltn_trans (ltjS).
  by have [->|] := eqP; rewrite (addr0, add0r).
rewrite -det_tr => /determinant_multilinear->;
  try by apply/matrixP=> i j; rewrite !mxE lift_eqF.
have [dj0 | dj_gt0] := posnP dj; rewrite ?dj0 !mul1r.
  rewrite !det_tr det_map_mx addrC (expand_det_col _ j0) big1 => [|i _].
    rewrite add0r; congr (\det _)%:P.
    apply/matrixP=> i j; rewrite [in RHS]mxE; case: eqP => // ->.
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
    rewrite (leq_trans (size_polyD _ _)) // geq_max.
    rewrite !(leq_trans (size_polyMleq _ _)) // -subn1 leq_subLR.
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
exists (row_mx (- c *: poly_rV q') (k *: poly_rV p')); last first.
  rewrite mul_row_col scaleNr mulNmx !mul_rV_lin1 /= 2!linearZ /= !poly_rV_K //.
  by rewrite !scalerCA p'r q'r mulrCA addNr.
apply: contraNneq r_nz; rewrite -row_mx0 => /eq_row_mx[/eqP].
rewrite scaleNr oppr_eq0 gcdp_eq0 -!size_poly_eq0 => /eqP q0 p0.
rewrite -(size_scale p nz_c) -(size_scale (c *: p) nz_k) p'r.
rewrite -(size_scale q nz_k) -(size_scale (k *: q) nz_c) q'r !scalerAl.
rewrite -(poly_rV_K le_p'_dp) -(poly_rV_K le_q'_dq).
by rewrite -2![_ *: rVpoly _]linearZ p0 q0 !linear0 mul0r size_poly0.
Qed.

Section HornerMx.

Variables (R : comNzRingType) (n' : nat).
Local Notation n := n'.+1.
Implicit Types (A B : 'M[R]_n) (p q : {poly R}).

Section OneMatrix.

Variable A : 'M[R]_n.

Definition horner_mx := horner_morph (comm_mx_scalar^~ A).
HB.instance Definition _ := GRing.RMorphism.on horner_mx.

Lemma horner_mx_C a : horner_mx a%:P = a%:M.
Proof. exact: horner_morphC. Qed.

Lemma horner_mx_X : horner_mx 'X = A. Proof. exact: horner_morphX. Qed.

Lemma horner_mxZ : scalable horner_mx.
Proof.
move=> a p /=; rewrite -mul_polyC rmorphM /=.
by rewrite horner_mx_C [_ * _]mul_scalar_mx.
Qed.

HB.instance Definition _ := GRing.isScalable.Build R _ _ *:%R horner_mx
  horner_mxZ.

Definition powers_mx d := \matrix_(i < d) mxvec (A ^+ i).

Lemma horner_rVpoly m (u : 'rV_m) :
  horner_mx (rVpoly u) = vec_mx (u *m powers_mx m).
Proof.
rewrite mulmx_sum_row [rVpoly u]poly_def 2!linear_sum; apply: eq_bigr => i _.
by rewrite valK /= 2!linearZ rmorphXn/= horner_mx_X rowK mxvecK.
Qed.

End OneMatrix.

Lemma horner_mx_diag (d : 'rV[R]_n) (p : {poly R}) :
  horner_mx (diag_mx d) p = diag_mx (map_mx (horner p) d).
Proof.
apply/matrixP => i j; rewrite !mxE.
elim/poly_ind: p => [|p c ihp]; first by rewrite rmorph0 horner0 mxE mul0rn.
rewrite !hornerE mulrnDl rmorphD rmorphM /= horner_mx_X horner_mx_C !mxE.
rewrite (bigD1 j)//= ihp mxE eqxx mulr1n -mulrnAl big1 ?addr0.
  by have [->|_] := eqVneq; rewrite /= !(mulr1n, addr0, mul0r).
by move=> k /negPf nkF; rewrite mxE nkF mulr0.
Qed.

Lemma comm_mx_horner A B p : comm_mx A B -> comm_mx A (horner_mx B p).
Proof.
move=> fg; apply: commr_horner => // i.
by rewrite coef_map; apply/comm_scalar_mx.
Qed.

Lemma comm_horner_mx A B p : comm_mx A B -> comm_mx (horner_mx A p) B.
Proof. by move=> ?; apply/comm_mx_sym/comm_mx_horner/comm_mx_sym. Qed.

Lemma comm_horner_mx2 A p q : GRing.comm (horner_mx A p) (horner_mx A q).
Proof. exact/comm_mx_horner/comm_horner_mx. Qed.

End HornerMx.

Lemma horner_mx_stable (K : fieldType) m n p
    (V : 'M[K]_(n.+1, m.+1)) (f : 'M_m.+1) :
  stablemx V f -> stablemx V (horner_mx f p).
Proof.
move=> V_fstab; elim/poly_ind: p => [|p c]; first by rewrite rmorph0 stablemx0.
move=> fp_stable; rewrite rmorphD rmorphM/= horner_mx_X horner_mx_C.
by rewrite stablemxD ?stablemxM ?fp_stable ?stablemxC.
Qed.

Prenex Implicits horner_mx powers_mx.

Section CharPoly.

Variables (R : nzRingType) (n : nat) (A : 'M[R]_n).
Implicit Types p q : {poly R}.

Definition char_poly_mx := 'X%:M - map_mx (@polyC R) A.
Definition char_poly := \det char_poly_mx.

Let diagA := [seq A i i | i <- index_enum _ & true].
Let size_diagA : size diagA = n.
Proof. by rewrite -[n]card_ord size_map; have [e _ _ []] := big_enumP. Qed.

Let split_diagA :
  exists2 q, \prod_(x <- diagA) ('X - x%:P) + q = char_poly & size q <= n.-1.
Proof.
rewrite [char_poly](bigD1 1%g) //=; set q := \sum_(s | _) _; exists q.
  congr (_ + _); rewrite odd_perm1 mul1r big_map big_filter /=.
  by apply: eq_bigr => i _; rewrite !mxE perm1 eqxx.
apply: leq_trans {q}(size_sum _ _ _) _; apply/bigmax_leqP=> s nt_s.
have{nt_s} [i nfix_i]: exists i, s i != i.
  apply/existsP; rewrite -negb_forall; apply: contra nt_s => s_1.
  by apply/eqP/permP=> i; apply/eqP; rewrite perm1 (forallP s_1).
apply: leq_trans (_ : #|[pred j | s j == j]|.+1 <= n.-1).
  rewrite -sum1_card (@big_mkcond nat) /= size_Msign.
  apply: (big_ind2 (fun p m => size p <= m.+1)) => [| p mp q mq IHp IHq | j _].
  - by rewrite size_poly1.
  - apply: leq_trans (size_polyMleq _ _) _.
    by rewrite -subn1 -addnS leq_subLR addnA leq_add.
  rewrite !mxE eq_sym !inE; case: (s j == j); first by rewrite polyseqXsubC.
  by rewrite sub0r size_polyN size_polyC leq_b1.
rewrite -[n in n.-1]card_ord -(cardC (pred2 (s i) i)) card2 nfix_i !ltnS.
apply/subset_leq_card/subsetP=> j /(_ =P j) fix_j.
rewrite !inE -{1}fix_j (inj_eq perm_inj) orbb.
by apply: contraNneq nfix_i => <-; rewrite fix_j.
Qed.

Lemma size_char_poly : size char_poly = n.+1.
Proof.
have [q <- lt_q_n] := split_diagA; have le_q_n := leq_trans lt_q_n (leq_pred n).
by rewrite size_polyDl size_prod_XsubC size_diagA.
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
have ->: \tr A = \sum_(x <- diagA) x by rewrite big_map big_filter.
rewrite -size_diagA {}/p; elim: diagA => [|x d IHd].
  by rewrite !big_nil mulr1 coefX oppr0.
rewrite !big_cons coefXM mulrBl coefB IHd opprD addrC; congr (- _ + _).
rewrite mul_polyC coefZ [size _]/= -(size_prod_XsubC _ id) -lead_coefE.
by rewrite (monicP _) ?monic_prod_XsubC ?mulr1.
Qed.

Lemma char_poly_det : char_poly`_0 = (- 1) ^+ n * \det A.
Proof.
rewrite big_distrr coef_sum [0%N]lock /=; apply: eq_bigr => s _.
rewrite -{1}rmorphN -rmorphXn mul_polyC coefZ /=.
rewrite mulrA -exprD addnC exprD -mulrA -lock; congr (_ * _).
transitivity (\prod_(i < n) - A i (s i)); last by rewrite prodrN card_ord.
elim: (index_enum _) => [|i e IHe]; rewrite !(big_nil, big_cons) ?coef1 //.
by rewrite coefM big_ord1 IHe !mxE coefB coefC coefMn coefX mul0rn sub0r.
Qed.

End CharPoly.

Prenex Implicits char_poly_mx char_poly.

Lemma mx_poly_ring_isom (R : nzRingType) n' (n := n'.+1) :
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
have phi_is_additive : additive phi.
  move=> A B; apply/polyP => k; apply/matrixP => i j.
  by rewrite !(coef_phi, mxE, coefD, coefN).
have phi_is_multiplicative : multiplicative phi.
  split=> [A B|]; apply/polyP => k; apply/matrixP => i j; last first.
    by rewrite coef_phi mxE coefMn !coefC; case: (k == _); rewrite ?mxE ?mul0rn.
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
pose phiaM := GRing.isAdditive.Build _ _ phi phi_is_additive.
pose phimM := GRing.isMultiplicative.Build _ _ phi phi_is_multiplicative.
pose phiRM : {rmorphism _ -> _} := HB.pack phi phiaM phimM.
exists phiRM; split=> // [p | A]; apply/polyP=> k; apply/matrixP=> i j.
  by rewrite coef_phi coef_map !mxE coefMn.
by rewrite coef_phi !mxE !coefC; case k; last rewrite /= mxE.
Qed.

Theorem Cayley_Hamilton (R : comNzRingType) n' (A : 'M[R]_n'.+1) :
  horner_mx A (char_poly A) = 0.
Proof.
have [phi [_ phiZ phiC _]] := mx_poly_ring_isom R n'.
apply/rootP/factor_theorem; rewrite -phiZ -mul_adj_mx rmorphM /=.
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

Lemma char_poly_trig {R : comNzRingType} n (A : 'M[R]_n) : is_trig_mx A ->
  char_poly A = \prod_(i < n) ('X - (A i i)%:P).
Proof.
move=> /is_trig_mxP Atrig; rewrite /char_poly det_trig.
  by apply: eq_bigr => i; rewrite !mxE eqxx.
by apply/is_trig_mxP => i j lt_ij; rewrite !mxE -val_eqE ltn_eqF ?Atrig ?subrr.
Qed.

Definition companionmx {R : nzRingType} (p : seq R) (d := (size p).-1) :=
  \matrix_(i < d, j < d)
    if (i == d.-1 :> nat) then - p`_j else (i.+1 == j :> nat)%:R.

Lemma companionmxK {R : comNzRingType} (p : {poly R}) :
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
  rewrite /cofactor -signr_odd oddD addbb mul1r; congr (\det _).
  apply/matrixP => i j; rewrite !mxE -val_eqE coefD coefMX coefC.
  by rewrite /= /bump /= !add1n !eqSS addr0.
rewrite /cofactor [X in \det X](_ : _ = D _).
  by rewrite detD /= addn0 -signr_odd -signr_addb addbb mulr1.
apply/matrixP=> i j; rewrite !mxE -!val_eqE /= /bump /=.
by rewrite leqNgt ltn_ord add0n add1n [_ == _.-2.+1]ltn_eqF.
Qed.

Lemma mulmx_delta_companion (R : nzRingType) (p : seq R)
  (i: 'I_(size p).-1) (i_small : i.+1 < (size p).-1):
  delta_mx 0 i *m companionmx p = delta_mx 0 (Ordinal i_small) :> 'rV__.
Proof.
apply/rowP => j; rewrite !mxE (bigD1 i) //= ?(=^~val_eqE, mxE) /= eqxx mul1r.
rewrite ltn_eqF ?big1 ?addr0 1?eq_sym //; last first.
  by rewrite -ltnS prednK // (leq_trans  _ i_small).
by move=> k /negPf ki_eqF; rewrite !mxE eqxx ki_eqF mul0r.
Qed.

Lemma row'_col'_char_poly_mx {R : nzRingType} m i (M : 'M[R]_m) :
  row' i (col' i (char_poly_mx M)) = char_poly_mx (row' i (col' i M)).
Proof. by apply/matrixP => k l; rewrite !mxE (inj_eq lift_inj). Qed.

Lemma char_block_diag_mx {R : nzRingType} m n (A : 'M[R]_m) (B : 'M[R]_n) :
  char_poly_mx (block_mx A 0 0 B) =
  block_mx (char_poly_mx A) 0 0 (char_poly_mx B).
Proof.
rewrite /char_poly_mx map_block_mx/= !map_mx0.
by rewrite scalar_mx_block opp_block_mx add_block_mx !subr0.
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
rewrite /d; case: ex_minnP => -[] //; rewrite leqn0 mxrank_eq0; move/eqP.
by move/row_matrixP/(_ 0)/eqP; rewrite rowK row0 mxvec_eq0 -mxrank_eq0 mxrank1.
Qed.

Lemma minpoly_mx1 : (1%:M \in Ad)%MS.
Proof.
by apply: (eq_row_sub (Ordinal mxminpoly_nonconstant)); rewrite rowK.
Qed.

Lemma minpoly_mx_free : row_free Ad.
Proof.
have:= mxminpoly_nonconstant; rewrite /d; case: ex_minnP => -[] // d' _ /(_ d').
by move/implyP; rewrite ltnn implybF -ltnS ltn_neqAle rank_leq_row andbT negbK.
Qed.

Lemma horner_mx_mem p : (horner_mx A p \in Ad)%MS.
Proof.
elim/poly_ind: p => [|p a IHp]; first by rewrite rmorph0 // linear0 sub0mx.
rewrite rmorphD rmorphM /= horner_mx_C horner_mx_X.
rewrite addrC -scalemx1 linearP /= -(mul_vec_lin (mulmxr A)).
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
apply/andP; split; first exact/mulsmx_subP/minpoly_mxM.
apply/mxring_idP; exists 1%:M; split=> *; rewrite ?mulmx1 ?mul1mx //.
  by rewrite -mxrank_eq0 mxrank1.
exact: minpoly_mx1.
Qed.

Definition mxminpoly := 'X^d - mx_inv_horner (A ^+ d).
Local Notation p_A := mxminpoly.

Lemma size_mxminpoly : size p_A = d.+1.
Proof. by rewrite size_polyDl ?size_polyXn // size_polyN ltnS size_poly. Qed.

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
rewrite rmorphB -{3}(horner_mx_X A) -rmorphXn /=.
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

Lemma mxminpoly_minP p : reflect (horner_mx A p = 0) (p_A %| p).
Proof.
apply: (iffP idP); last exact: mxminpoly_min.
by move=> /Pdiv.Field.dvdpP[q ->]; rewrite rmorphM/= mx_root_minpoly mulr0.
Qed.

Lemma dvd_mxminpoly p : (p_A %| p) = (horner_mx A p == 0).
Proof. exact/mxminpoly_minP/eqP. Qed.

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
Proof. exact/mxminpoly_min/Cayley_Hamilton. Qed.

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

Lemma root_mxminpoly a : root p_A a = root (char_poly A) a.
Proof. by rewrite -eigenvalue_root_min eigenvalue_root_char. Qed.

End MinPoly.

Lemma mxminpoly_diag {F : fieldType} {n} (d : 'rV[F]_n.+1)
    (u := undup [seq d 0 i | i <- enum 'I_n.+1]) :
  mxminpoly (diag_mx d) = \prod_(r <- u) ('X - r%:P).
Proof.
apply/eqP; rewrite -eqp_monic ?mxminpoly_monic ?monic_prod_XsubC// /eqp.
rewrite mxminpoly_min/=; last first.
  rewrite horner_mx_diag; apply/matrixP => i j; rewrite !mxE horner_prod.
  case: (altP (i =P j)) => [->|neq_ij//]; rewrite mulr1n.
  rewrite (bigD1_seq (d 0 j)) ?undup_uniq ?mem_undup ?map_f// /=.
  by rewrite hornerD hornerN hornerX hornerC subrr mul0r.
apply: uniq_roots_dvdp; last by rewrite uniq_rootsE undup_uniq.
apply/allP => x; rewrite mem_undup root_mxminpoly char_poly_trig//.
rewrite -(big_map _ predT (fun x => _ - x%:P)) root_prod_XsubC.
by move=> /mapP[i _ ->]; apply/mapP; exists i; rewrite ?(mxE, eqxx).
Qed.
Prenex Implicits degree_mxminpoly mxminpoly mx_inv_horner.

Arguments mx_inv_hornerK {F n' A} [B] AnB.
Arguments horner_rVpoly_inj {F n' A} [u1 u2] eq_u12A : rename.

(* Parametricity. *)
Section MapRingMatrix.

Variables (aR rR : nzRingType) (f : {rmorphism aR -> rR}).
Local Notation "A ^f" := (map_mx (GRing.RMorphism.sort f) A) : ring_scope.
Local Notation fp := (map_poly (GRing.RMorphism.sort f)).
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

Lemma map_resultant (aR rR : nzRingType) (f : {rmorphism {poly aR} -> rR}) p q :
    f (lead_coef p) != 0 -> f (lead_coef q) != 0 ->
  f (resultant p q)= resultant (map_poly f p) (map_poly f q).
Proof.
move=> nz_fp nz_fq; rewrite /resultant /Sylvester_mx !size_map_poly_id0 //.
rewrite -det_map_mx /= map_col_mx; congr (\det (col_mx _ _));
  by apply: map_lin1_mx => v; rewrite map_poly_rV rmorphM /= map_rVpoly.
Qed.

End MapResultant.

Section MapComRing.

Variables (aR rR : comNzRingType) (f : {rmorphism aR -> rR}).
Local Notation "A ^f" := (map_mx f A) : ring_scope.
Local Notation fp := (map_poly f).
Variables (n' : nat) (A : 'M[aR]_n'.+1).

Lemma map_powers_mx e : (powers_mx A e)^f = powers_mx A^f e.
Proof. by apply/row_matrixP=> i; rewrite -map_row !rowK map_mxvec rmorphXn. Qed.

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
rewrite degree_mxminpoly_map -rmorphXn /=.
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

Section KernelLemmas.

Variable K : fieldType.

(* convertible to kermx (horner_mx g p) when n = n.+1 *)
Definition kermxpoly n (g : 'M_n) (p : {poly K}) : 'M_n :=
  kermx ((if n is n.+1 then horner_mx^~ p : 'M_n.+1 -> 'M_n.+1 else \0) g).

Lemma kermxpolyC n (g : 'M_n) c : c != 0 -> kermxpoly g c%:P = 0.
Proof.
move=> c_neq0; case: n => [|n] in g *; first by rewrite thinmx0.
apply/eqP; rewrite /kermxpoly horner_mx_C kermx_eq0 row_free_unit.
by rewrite -scalemx1 scaler_unit ?unitmx1// unitfE.
Qed.

Lemma kermxpoly1 n (g : 'M_n) : kermxpoly g 1 = 0.
Proof. by rewrite kermxpolyC ?oner_eq0. Qed.

Lemma kermxpolyX n (g : 'M_n) : kermxpoly g 'X = kermx g.
Proof.
case: n => [|n] in g *; first by rewrite !thinmx0.
by rewrite /kermxpoly horner_mx_X.
Qed.

Lemma kermxpoly_min n (g : 'M[K]_n.+1) p :
  mxminpoly g %| p -> (kermxpoly g p :=: 1)%MS.
Proof. by rewrite /kermxpoly => /mxminpoly_minP ->; apply: kermx0. Qed.

Lemma comm_mx_stable_kermxpoly n (f g : 'M_n) (p : {poly K}) : comm_mx f g ->
  stablemx (kermxpoly f p) g.
Proof.
case: n => [|n] in f g *; first by rewrite !thinmx0.
move=> fg; rewrite /kermxpoly; apply: comm_mx_stable_ker.
by apply/comm_mx_sym/comm_mx_horner/comm_mx_sym.
Qed.

Lemma mxdirect_kermxpoly n (g : 'M_n) (p q : {poly K}) :
  coprimep p q -> (kermxpoly g p :&: kermxpoly g q = 0)%MS.
Proof.
case: n => [|n] in g *; first by rewrite thinmx0 ?cap0mx ?submx_refl.
move=> /Bezout_eq1_coprimepP [[/= u v]]; rewrite mulrC [v * _]mulrC => cpq.
apply/eqP/rowV0P => x.
rewrite sub_capmx => /andP[/sub_kermxP xgp0 /sub_kermxP xgq0].
move: cpq => /(congr1 (mulmx x \o horner_mx g))/=.
rewrite !(rmorphM, rmorphD, rmorph1, mulmx1, mulmxDr, mulmxA).
by rewrite xgp0 xgq0 !mul0mx add0r.
Qed.

Lemma kermxpolyM n (g : 'M_n) (p q : {poly K}) : coprimep p q ->
  (kermxpoly g (p * q) :=: kermxpoly g p + kermxpoly g q)%MS.
Proof.
case: n => [|n] in g *; first by rewrite !thinmx0.
move=> /Bezout_eq1_coprimepP [[/= u v]]; rewrite mulrC [v * _]mulrC => cpq.
apply/eqmxP/andP; split; last first.
  apply/sub_kermxP/eqmx0P; rewrite !addsmxMr [in X in (_ + X)%MS]mulrC.
  by rewrite !rmorphM/= !mulmxA !mulmx_ker !mul0mx !addsmx0 submx_refl.
move: cpq => /(congr1 (horner_mx g))/=; rewrite rmorph1 rmorphD/=.
rewrite -[X in (X <= _)%MS]mulr1 => <-; rewrite mulrDr [p * u]mulrC addrC.
rewrite addmx_sub_adds//; apply/sub_kermxP; rewrite mulmxE -mulrA -rmorphM.
  by rewrite mulrAC [q * p]mulrC rmorphM/= mulrA -!mulmxE mulmx_ker mul0mx.
rewrite -[_ * _ * q]mulrA [u * _]mulrC.
by rewrite rmorphM mulrA -!mulmxE mulmx_ker mul0mx.
Qed.

Lemma kermxpoly_prod n (g : 'M_n)
    (I : finType) (P : {pred I}) (p_ : I -> {poly K}) :
  {in P &, forall i j, j != i -> coprimep (p_ i) (p_ j)} ->
  (kermxpoly g (\prod_(i | P i) p_ i) :=: \sum_(i | P i) kermxpoly g (p_ i))%MS.
Proof.
move=> p_coprime; elim: index_enum (index_enum_uniq I).
  by rewrite !big_nil ?kermxpoly1 ?submx_refl//.
move=> j js ihjs /= /andP[jNjs js_uniq]; apply/eqmxP.
rewrite !big_cons; case: ifP => [Pj|PNj]; rewrite ?ihjs ?submx_refl//.
suff cjjs: coprimep (p_ j) (\prod_(i <- js | P i) p_ i).
  by rewrite !kermxpolyM// !(adds_eqmx (eqmx_refl _) (ihjs _)) ?submx_refl.
rewrite (@big_morph _ _ _ true andb) ?big_all_cond ?coprimep1//; last first.
  by move=> p q; rewrite coprimepMr.
apply/allP => i i_js; apply/implyP => Pi; apply: p_coprime => //.
by apply: contraNneq jNjs => <-.
Qed.

Lemma mxdirect_sum_kermx n (g : 'M_n)
    (I : finType) (P : {pred I}) (p_ : I -> {poly K}) :
  {in P &, forall i j, j != i -> coprimep (p_ i) (p_ j)} ->
  mxdirect (\sum_(i | P i) kermxpoly g (p_ i))%MS.
Proof.
move=> p_coprime; apply/mxdirect_sumsP => i Pi; apply/eqmx0P.
have cpNi : {in [pred j | P j && (j != i)] &,
    forall j k : I, k != j -> coprimep (p_ j) (p_ k)}.
  by move=> j k /andP[Pj _] /andP[Pk _]; apply: p_coprime.
rewrite -!(cap_eqmx (eqmx_refl _) (kermxpoly_prod g _))//.
rewrite mxdirect_kermxpoly ?submx_refl//.
rewrite (@big_morph _ _ _ true andb) ?big_all_cond ?coprimep1//; last first.
  by move=> p q; rewrite coprimepMr.
by apply/allP => j _; apply/implyP => /andP[Pj neq_ji]; apply: p_coprime.
Qed.

Lemma eigenspace_poly n a (f : 'M_n) :
  eigenspace f a = kermxpoly f ('X - a%:P).
Proof.
case: n => [|m] in a f *; first by rewrite !thinmx0.
by congr (kermx _); rewrite rmorphB /= ?horner_mx_X ?horner_mx_C.
Qed.

Definition geigenspace n (g : 'M_n) a := kermxpoly g (('X - a%:P) ^+ n).

Lemma geigenspaceE n' (g : 'M_n'.+1) a :
  geigenspace g a = kermx ((g - a%:M) ^+ n'.+1).
Proof.
by rewrite /geigenspace /kermxpoly rmorphXn/= rmorphB/= horner_mx_X horner_mx_C.
Qed.

Lemma eigenspace_sub_geigen n (g : 'M_n) a :
  (eigenspace g a <= geigenspace g a)%MS.
Proof.
case: n => [|n] in g *; rewrite ?thinmx0 ?sub0mx// geigenspaceE.
by apply/sub_kermxP; rewrite exprS mulmxA mulmx_ker mul0mx.
Qed.

Lemma mxdirect_sum_geigenspace
    (I : finType) (n : nat) (g : 'M_n) (P : {pred I}) (a_ : I -> K) :
  {in P &, injective a_} -> mxdirect (\sum_(i | P i) geigenspace g (a_ i)).
Proof.
move=> /inj_in_eq eq_a; apply: mxdirect_sum_kermx => i j Pi Pj Nji.
by rewrite coprimep_expr ?coprimep_expl// coprimep_XsubC root_XsubC eq_a.
Qed.

Definition eigenpoly n (g : 'M_n) : pred {poly K} :=
  (fun p => kermxpoly g p != 0).

Lemma eigenpolyP n (g : 'M_n) (p : {poly K}) :
  reflect (exists2 v : 'rV_n, (v <= kermxpoly g p)%MS & v != 0) (eigenpoly g p).
Proof. exact: rowV0Pn. Qed.

Lemma eigenvalue_poly n a (f : 'M_n) : eigenvalue f a = eigenpoly f ('X - a%:P).
Proof. by rewrite /eigenpoly /eigenvalue eigenspace_poly. Qed.

Lemma comm_mx_stable_geigenspace n (f g : 'M_n) a : comm_mx f g ->
  stablemx (geigenspace f a) g.
Proof. exact: comm_mx_stable_kermxpoly. Qed.

End KernelLemmas.

Section MapKermxPoly.
Variables (aF rF : fieldType) (f : {rmorphism aF -> rF}).

Lemma map_kermxpoly (n : nat) (g : 'M_n) (p : {poly aF}) :
  map_mx f (kermxpoly g p) = kermxpoly (map_mx f g) (map_poly f p).
Proof.
by case: n => [|n] in g *; rewrite ?thinmx0// map_kermx map_horner_mx.
Qed.

Lemma map_geigenspace (n : nat) (g : 'M_n) (a : aF) :
  map_mx f (geigenspace g a) = geigenspace (map_mx f g) (f a).
Proof. by rewrite map_kermxpoly rmorphXn/= rmorphB /= map_polyX map_polyC. Qed.

Lemma eigenpoly_map n (g : 'M_n) (p : {poly aF}) :
  eigenpoly (map_mx f g) (map_poly f p) = eigenpoly g p.
Proof. by rewrite /eigenpoly -map_kermxpoly map_mx_eq0. Qed.

End MapKermxPoly.

Section IntegralOverRing.

Definition integralOver (R K : nzRingType) (RtoK : R -> K) (z : K) :=
  exists2 p, p \is monic & root (map_poly RtoK p) z.

Definition integralRange R K RtoK := forall z, @integralOver R K RtoK z.

Variables (B R K : nzRingType) (BtoR : B -> R) (RtoK : {rmorphism R -> K}).

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

Variables (R K : comNzRingType) (RtoK : {rmorphism R -> K}).

Lemma integral_horner_root w (p q : {poly K}) :
    p \is monic -> root p w ->
    {in p : seq K, integralRange RtoK} -> {in q : seq K, integralRange RtoK} ->
  integralOver RtoK q.[w].
Proof.
move=> mon_p pw0 intRp intRq.
pose memR y := exists x, y = RtoK x.
have memRid x: memR (RtoK x) by exists x.
have memR_nat n: memR n%:R by rewrite -(rmorph_nat RtoK) /=.
have [memR0 memR1]: memR 0 * memR 1 := (memR_nat 0, memR_nat 1).
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
  rewrite mxE -Du mulr1 rootE -horner_evalE -2!det_map_mx; congr (\det _ == 0).
  rewrite raddfB/= map_scalar_mx; apply/matrixP=> i j.
  by rewrite !mxE raddfB raddfMn/= map_polyX map_polyC /horner_eval !hornerE.
pose gen1 x E y := exists2 r, pXin E r & y = r.[x]; pose gen := foldr gen1 memR.
have gen1S (E : K -> Prop) x y: E 0 -> E y -> gen1 x E y.
  by exists y%:P => [i|]; rewrite ?hornerC ?coefC //; case: ifP.
have genR S y: memR y -> gen S y.
  by elim: S => //= x S IH in y * => /IH; apply/gen1S/IH.
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
  set S2 := S1; have: all [in S1] S2 by apply/allP.
  elim: S2 => //= y S2 IH /andP[S1y S12]; split; last exact: IH.
  have{q S S1 IH S1y S12 intRp intRq} [q mon_q qx0]: integralOver RtoK y.
    by move: S1y; rewrite mem_cat => /orP[]; [apply: intRq | apply: intRp].
  exists (map_poly RtoK q); split=> // [|i]; first exact: monic_map.
  by rewrite coef_map /=; apply: genR.
elim: {w p q}S => /= [_|x S IH [[p [mon_p px0 Sp]] /IH{IH}[m2 [X2 defS]]]].
  exists 1, 1 => y; split=> [[a [Fa ->]] | Fy].
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
  by rewrite mulmxDl !mxE; split=> // i /[1!mxE]; apply: memRD.
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

Let integral0_RtoK := integral0 RtoK.
Let integral1_RtoK := integral1 RtoK.
Let monicXsubC_K := @monicXsubC K.
Hint Resolve integral0_RtoK integral1_RtoK monicXsubC_K : core.

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
  apply/eqP=> /polyP/(_ 0); rewrite coef_Poly coef0 nth_rev ?size_poly_gt0 //.
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
elim: m r n A => [|m IHm] r [|n] A /=; try by case r; rewrite unlock.
rewrite GRing.eval_Pick !unlock /=; set pf := fun _ => _.
rewrite -(@eq_pick _ pf) => [|k]; rewrite {}/pf ?mxE // eq_sym.
case: pick => [[i j]|] //=; set B := _ - _; have:= mxrankE B.
case: (Gaussian_elimination_ B) r => [[_ _] _] [|r] //= <-; rewrite {}IHm eqSS.
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

Section ConjMx.
Context {F : fieldType}.

Definition conjmx (m n : nat)
 (V : 'M_(m, n)) (f : 'M[F]_n) : 'M_m :=  V *m f *m pinvmx V.
Notation restrictmx V := (conjmx (row_base V)).

Lemma stablemx_comp (m n p : nat) (V : 'M[F]_(m, n)) (W : 'M_(n, p)) (f : 'M_p) :
  stablemx W f -> stablemx V (conjmx W f) -> stablemx (V *m W) f.
Proof. by move=> Wf /(submxMr W); rewrite -mulmxA mulmxKpV// mulmxA. Qed.

Lemma stablemx_restrict m n (A : 'M[F]_n) (V : 'M_n) (W : 'M_(m, \rank V)):
  stablemx V A -> stablemx W (restrictmx V A) = stablemx (W *m row_base V) A.
Proof.
move=> A_stabV; rewrite mulmxA -[in RHS]mulmxA.
rewrite -(submxMfree _ W (row_base_free V)) mulmxKpV //.
by rewrite mulmx_sub ?stablemx_row_base.
Qed.

Lemma conjmxM (m n : nat) (V : 'M[F]_(m, n)) :
   {in [pred f | stablemx V f] &, {morph conjmx V : f g / f *m g}}.
Proof.
move=> f g; rewrite !inE => Vf Vg /=.
by rewrite /conjmx 2!mulmxA mulmxA mulmxKpV ?stablemx_row_base.
Qed.

Lemma conjMmx (m n p : nat) (V : 'M[F]_(m, n)) (W : 'M_(n, p)) (f : 'M_p) :
  row_free (V *m W) -> stablemx W f -> stablemx V (conjmx W f) ->
  conjmx (V *m W) f = conjmx V (conjmx W f).
Proof.
move=> rfVW Wf VWf; apply: (row_free_inj rfVW); rewrite mulmxKpV ?stablemx_comp//.
by rewrite mulmxA mulmxKpV// -[RHS]mulmxA mulmxKpV ?mulmxA.
Qed.

Lemma conjuMmx (m n : nat) (V : 'M[F]_m) (W : 'M_(m, n)) (f : 'M_n) :
  V \in unitmx -> row_free W -> stablemx W f ->
  conjmx (V *m W) f = conjmx V (conjmx W f).
Proof.
move=> Vu rfW Wf; rewrite conjMmx ?stablemx_unit//.
by rewrite /row_free mxrankMfree// -/(row_free V) row_free_unit.
Qed.

Lemma conjMumx (m n : nat) (V : 'M[F]_(m, n)) (W f : 'M_n) :
  W \in unitmx -> row_free V -> stablemx V (conjmx W f) ->
  conjmx (V *m W) f = conjmx V (conjmx W f).
Proof.
move=> Wu rfW Wf; rewrite conjMmx ?stablemx_unit//.
by rewrite /row_free mxrankMfree ?row_free_unit.
Qed.

Lemma conjuMumx (n : nat) (V W f : 'M[F]_n) :
  V \in unitmx -> W \in unitmx ->
  conjmx (V *m W) f = conjmx V (conjmx W f).
Proof. by move=> Vu Wu; rewrite conjuMmx ?stablemx_unit ?row_free_unit. Qed.

Lemma conjmx_scalar (m n : nat) (V : 'M[F]_(m, n)) (a : F) :
  row_free V -> conjmx V a%:M = a%:M.
Proof. by move=> rfV; rewrite /conjmx scalar_mxC mulmxKp. Qed.

Lemma conj0mx (m n : nat) f : conjmx (0 : 'M[F]_(m, n)) f = 0.
Proof. by rewrite /conjmx !mul0mx. Qed.

Lemma conjmx0 (m n : nat) (V : 'M[F]_(m, n)) : conjmx V 0 = 0.
Proof. by rewrite /conjmx mulmx0 mul0mx. Qed.

Lemma conjumx (n : nat) (V : 'M_n) (f : 'M[F]_n) : V \in unitmx ->
  conjmx V f = V *m f *m invmx V.
Proof. by move=> uV; rewrite /conjmx pinvmxE. Qed.

Lemma conj1mx (n : nat) (f : 'M[F]_n) : conjmx 1%:M f = f.
Proof. by rewrite conjumx ?unitmx1// invmx1 mulmx1 mul1mx. Qed.

Lemma conjVmx (n : nat) (V : 'M_n) (f : 'M[F]_n) : V \in unitmx ->
  conjmx (invmx V) f = invmx V *m f *m V.
Proof. by move=> Vunit; rewrite conjumx ?invmxK ?unitmx_inv. Qed.

Lemma conjmxK (n : nat) (V f : 'M[F]_n) :
  V \in unitmx -> conjmx (invmx V) (conjmx V f) = f.
Proof. by move=> Vu; rewrite -conjuMumx ?unitmx_inv// mulVmx ?conj1mx. Qed.

Lemma conjmxVK (n : nat) (V f : 'M[F]_n) :
  V \in unitmx -> conjmx V (conjmx (invmx V) f) = f.
Proof. by move=> Vu; rewrite -conjuMumx ?unitmx_inv// mulmxV ?conj1mx. Qed.

Lemma horner_mx_conj m n p (V : 'M[F]_(n.+1, m.+1)) (f : 'M_m.+1) :
   row_free V -> stablemx V f ->
   horner_mx (conjmx V f) p = conjmx V (horner_mx f p).
Proof.
move=> V_free V_stab; rewrite/conjmx; elim/poly_ind: p => [|p c].
  by rewrite !rmorph0 mulmx0 mul0mx.
rewrite !(rmorphD, rmorphM)/= !(horner_mx_X, horner_mx_C) => ->.
rewrite [_ * _]mulmxA [_ *m (V *m _)]mulmxA mulmxKpV ?horner_mx_stable//.
apply: (row_free_inj V_free); rewrite [_ *m V]mulmxDl.
pose stablemxE := (stablemxD, stablemxM, stablemxC, horner_mx_stable).
by rewrite !mulmxKpV -?[V *m _ *m _]mulmxA ?stablemxE// mulmxDr -scalar_mxC.
Qed.

Lemma horner_mx_uconj n p (V : 'M[F]_(n.+1)) (f : 'M_n.+1) :
   V \is a GRing.unit ->
   horner_mx (V *m f *m invmx V) p = V *m horner_mx f p *m invmx V.
Proof.
move=> V_unit; rewrite -!conjumx//.
by rewrite horner_mx_conj ?row_free_unit ?stablemx_unit.
Qed.

Lemma horner_mx_uconjC n p (V : 'M[F]_(n.+1)) (f : 'M_n.+1) :
   V \is a GRing.unit ->
   horner_mx (invmx V *m f *m V) p = invmx V *m horner_mx f p *m V.
Proof.
move=> V_unit; rewrite -[X in _ *m X](invmxK V).
by rewrite horner_mx_uconj ?invmxK ?unitmx_inv.
Qed.

Lemma mxminpoly_conj m n (V : 'M[F]_(m.+1, n.+1)) (f : 'M_n.+1) :
  row_free V -> stablemx V f -> mxminpoly (conjmx V f) %| mxminpoly f.
Proof.
by move=> *; rewrite mxminpoly_min// horner_mx_conj// mx_root_minpoly conjmx0.
Qed.

Lemma mxminpoly_uconj n (V : 'M[F]_(n.+1)) (f : 'M_n.+1) :
  V \in unitmx -> mxminpoly (conjmx V f) = mxminpoly f.
Proof.
have simp := (row_free_unit, stablemx_unit, unitmx_inv, unitmx1).
move=> Vu; apply/eqP; rewrite -eqp_monic ?mxminpoly_monic// /eqp.
apply/andP; split; first by rewrite mxminpoly_conj ?simp.
by rewrite -[f in X in X %| _](conjmxK _ Vu) mxminpoly_conj ?simp.
Qed.

Section fixed_stablemx_space.

Variables (m n : nat).

Implicit Types (V : 'M[F]_(m, n)) (A : 'M[F]_n).
Implicit Types (a : F) (p : {poly F}).

Section Sub.
Variable (k : nat).
Implicit Types (W : 'M[F]_(k, m)).

Lemma sub_kermxpoly_conjmx V f p W : stablemx V f -> row_free V ->
  (W <= kermxpoly (conjmx V f) p)%MS = (W *m V <= kermxpoly f p)%MS.
Proof.
case: n m => [|n'] [|m'] in V f W * => fV rfV; rewrite ?thinmx0//.
  by rewrite /row_free mxrank.unlock in rfV.
  by rewrite mul0mx !sub0mx.
apply/sub_kermxP/sub_kermxP; rewrite horner_mx_conj//; last first.
  by move=> /(congr1 (mulmxr (pinvmx V)))/=; rewrite mul0mx !mulmxA.
move=> /(congr1 (mulmxr V))/=; rewrite ![W *m _]mulmxA ?mul0mx mulmxKpV//.
by rewrite -mulmxA mulmx_sub// horner_mx_stable//.
Qed.

Lemma sub_eigenspace_conjmx V f a W : stablemx V f -> row_free V ->
  (W <= eigenspace (conjmx V f) a)%MS = (W *m V <= eigenspace f a)%MS.
Proof. by move=> fV rfV; rewrite !eigenspace_poly sub_kermxpoly_conjmx. Qed.
End Sub.

Lemma eigenpoly_conjmx V f : stablemx V f -> row_free V ->
  {subset eigenpoly (conjmx V f) <= eigenpoly f}.
Proof.
move=> fV rfV a /eigenpolyP [x]; rewrite sub_kermxpoly_conjmx//.
move=> xV_le_fa x_neq0; apply/eigenpolyP.
by exists (x *m V); rewrite ?mulmx_free_eq0.
Qed.

Lemma eigenvalue_conjmx V f : stablemx V f -> row_free V ->
  {subset eigenvalue (conjmx V f) <= eigenvalue f}.
Proof.
by move=> fV rfV a; rewrite ![_ \in _]eigenvalue_poly; apply: eigenpoly_conjmx.
Qed.

Lemma conjmx_eigenvalue a V f : (V <= eigenspace f a)%MS -> row_free V ->
  conjmx V f = a%:M.
Proof.
by move=> /eigenspaceP Vfa rfV; rewrite /conjmx Vfa -mul_scalar_mx mulmxKp.
Qed.

End fixed_stablemx_space.
End ConjMx.
Notation restrictmx V := (conjmx (row_base V)).

Definition simmx_to_for {F : fieldType} {m n}
  (P : 'M_(m, n)) A (S : {pred 'M[F]_m}) := S (conjmx P A).
Notation "A ~_ P '{' 'in' S '}'" := (simmx_to_for P A S)
  (at level 70, P at level 0, format "A  ~_ P  '{' 'in'  S '}'") :
  ring_scope.

Notation simmx_for P A B := (A ~_P {in PredOfSimpl.coerce (pred1 B)}).
Notation "A ~_ P B" :=  (simmx_for P A B)
  (at level 70, P at level 0, format "A  ~_ P  B").

Notation simmx_in S A B := (exists2 P, P \in S & A ~_P B).
Notation "A '~_{in' S '}' B" := (simmx_in S A B)
  (at level 70, format "A '~_{in'  S '}'  B").

Notation simmx_in_to S A S' := (exists2 P, P \in S & A ~_P {in S'}).
Notation "A '~_{in' S '}' '{' 'in' S' '}'" := (simmx_in_to S A S')
  (at level 70, format "A '~_{in'  S '}'  '{' 'in'  S' '}'").

Notation all_simmx_in S As S' :=
  (exists2 P, P \in S & all [pred A | A ~_P {in S'}] As).

Notation diagonalizable_for P A := (A ~_P {in is_diag_mx}).
Notation diagonalizable_in S A := (A ~_{in S} {in is_diag_mx}).
Notation diagonalizable A := (diagonalizable_in unitmx A).
Notation codiagonalizable_in S As := (all_simmx_in S As is_diag_mx).
Notation codiagonalizable As := (codiagonalizable_in unitmx As).

Section Simmxity.
Context {F : fieldType}.

Lemma simmxPp m n {P : 'M[F]_(m, n)} {A B} :
  stablemx P A -> A ~_P B -> P *m A = B *m P.
Proof. by move=> stablemxPA /eqP <-; rewrite mulmxKpV. Qed.

Lemma simmxW m n {P : 'M[F]_(m, n)} {A B} : row_free P ->
  P *m A = B *m P -> A ~_P B.
Proof. by rewrite /(_ ~__ _)/= /conjmx => fP ->; rewrite mulmxKp. Qed.

Section Simmx.

Context {n : nat}.
Implicit Types (A B P : 'M[F]_n) (As : seq 'M[F]_n) (d : 'rV[F]_n).

Lemma simmxP {P A B} : P \in unitmx ->
  reflect (P *m A = B *m P) (A ~_P B).
Proof.
move=> p_unit; apply: (iffP idP); first exact/simmxPp/stablemx_unit.
by apply: simmxW; rewrite row_free_unit.
Qed.

Lemma simmxRL {P A B} : P \in unitmx ->
  reflect (B = P *m A *m invmx P) (A ~_P B).
Proof. by move=> ?; apply: (iffP eqP); rewrite conjumx. Qed.

Lemma simmxLR {P A B} : P \in unitmx ->
  reflect (A = conjmx (invmx P) B) (A ~_P B).
Proof.
by move=> Pu; rewrite conjVmx//; apply: (iffP (simmxRL Pu)) => ->;
   rewrite !mulmxA ?(mulmxK, mulmxKV, mulVmx, mulmxV, mul1mx, mulmx1).
Qed.

End Simmx.

Lemma simmx_minpoly {n} {P A B : 'M[F]_n.+1} : P \in unitmx ->
  A ~_P B -> mxminpoly A = mxminpoly B.
Proof. by move=> Pu /eqP<-; rewrite mxminpoly_uconj. Qed.

Lemma diagonalizable_for_row_base m n (P : 'M[F]_(m, n)) (A : 'M_n) :
  diagonalizable_for (row_base P) A = is_diag_mx (restrictmx P A).
Proof. by []. Qed.

Lemma diagonalizable_forPp m n (P : 'M[F]_(m, n)) A :
  reflect (forall i j : 'I__, i != j :> nat -> conjmx P A i j = 0)
          (diagonalizable_for P A).
Proof. exact: @is_diag_mxP. Qed.

Lemma diagonalizable_forP n (P : 'M[F]_n) A : P \in unitmx ->
  reflect (forall i j : 'I__, i != j :> nat -> (P *m A *m invmx P) i j = 0)
          (diagonalizable_for P A).
Proof. by move=> Pu; rewrite -conjumx//; exact: is_diag_mxP. Qed.

Lemma diagonalizable_forPex {m} {n} {P : 'M[F]_(m, n)} {A} :
  reflect (exists D, A ~_P (diag_mx D)) (diagonalizable_for P A).
Proof. by apply: (iffP (diag_mxP _)) => -[D]/eqP; exists D. Qed.

Lemma diagonalizable_forLR n {P : 'M[F]_n} {A} : P \in unitmx ->
  reflect (exists D, A = conjmx (invmx P) (diag_mx D)) (diagonalizable_for P A).
Proof.
by move=> Punit; apply: (iffP diagonalizable_forPex) => -[D /(simmxLR Punit)]; exists D.
Qed.

Lemma diagonalizable_for_mxminpoly {n} {P A : 'M[F]_n.+1}
  (rs := undup [seq conjmx P A i i | i <- enum 'I_n.+1]) :
  P \in unitmx -> diagonalizable_for P A ->
  mxminpoly A = \prod_(r <- rs) ('X - r%:P).
Proof.
rewrite /rs => pu /(diagonalizable_forLR pu)[d {A rs}->].
rewrite mxminpoly_uconj ?unitmx_inv// mxminpoly_diag.
by rewrite [in X in _ = X](@eq_map _ _ _ (d 0))// => i; rewrite conjmxVK// mxE eqxx.
Qed.

End Simmxity.

Lemma diagonalizable_for_sum (F : fieldType) (m n : nat) (p_ : 'I_n -> nat)
      (V_ : forall i, 'M[F]_(p_ i, m)) (A : 'M[F]_m) :
    mxdirect (\sum_i <<V_ i>>) ->
    (forall i, stablemx (V_ i) A) ->
    (forall i, row_free (V_ i)) ->
  diagonalizable_for (\mxcol_i V_ i) A = [forall i, diagonalizable_for (V_ i) A].
Proof.
move=> Vd VA rAV; have aVA : stablemx (\mxcol_i V_ i) A.
  rewrite (eqmx_stable _ (eqmx_col _)) stablemx_sums//.
  by move=> i; rewrite (eqmx_stable _ (genmxE _)).
apply/diagonalizable_forPex/'forall_diagonalizable_forPex => /=
    [[D /(simmxPp aVA) +] i|/(_ _)/sigW DoA].
  rewrite mxcol_mul -[D]submxrowK diag_mxrow mul_mxdiag_mxcol.
  move=> /eq_mxcolP/(_ i); set D0 := (submxrow _ _) => VMeq.
  by exists D0; apply/simmxW.
exists (\mxrow_i tag (DoA i)); apply/simmxW.
   rewrite -row_leq_rank eqmx_col (mxdirectP Vd)/=.
   by under [leqRHS]eq_bigr do rewrite genmxE (eqP (rAV _)).
rewrite mxcol_mul diag_mxrow mul_mxdiag_mxcol; apply: eq_mxcol => i.
by case: DoA => /= k /(simmxPp); rewrite VA => /(_ isT) ->.
Qed.

Section Diag.
Variable (F : fieldType).

Lemma codiagonalizable1 n (A : 'M[F]_n) :
  codiagonalizable [:: A] <-> diagonalizable A.
Proof. by split=> -[P Punit PA]; exists P; move: PA; rewrite //= andbT. Qed.

Definition codiagonalizablePfull n (As : seq 'M[F]_n) :
  codiagonalizable As
  <-> exists m, exists2 P : 'M_(m, n), row_full P &
        all [pred A | diagonalizable_for P A] As.
Proof.
split => [[P Punit SPA]|[m [P Pfull SPA]]].
  by exists n => //; exists P; rewrite ?row_full_unit.
have Qfull := fullrowsub_unit Pfull.
exists (rowsub (fullrankfun Pfull) P) => //; apply/allP => A AAs/=.
have /allP /(_ _ AAs)/= /diagonalizable_forPex[d /simmxPp] := SPA.
rewrite submx_full// => /(_ isT) PA_eq.
apply/diagonalizable_forPex; exists (colsub (fullrankfun Pfull) d).
apply/simmxP => //; apply/row_matrixP => i.
rewrite !row_mul row_diag_mx -scalemxAl -rowE !row_rowsub !mxE.
have /(congr1 (row (fullrankfun Pfull i))) := PA_eq.
by rewrite !row_mul row_diag_mx -scalemxAl -rowE => ->.
Qed.

Lemma codiagonalizable_on m n (V_ : 'I_n -> 'M[F]_m) (As : seq 'M[F]_m) :
    (\sum_i V_ i :=: 1%:M)%MS -> mxdirect (\sum_i V_ i) ->
    (forall i, all (fun A => stablemx (V_ i) A) As) ->
    (forall i, codiagonalizable (map (restrictmx (V_ i)) As)) ->
  codiagonalizable As.
Proof.
move=> V1 Vdirect /(_ _)/allP AV /(_ _) /sig2W/= Pof.
pose P_ i := tag (Pof i).
have P_unit i : P_ i \in unitmx by rewrite /P_; case: {+}Pof.
have P_diag i A : A \in As -> diagonalizable_for (P_ i *m row_base (V_ i)) A.
  move=> AAs; rewrite /P_; case: {+}Pof => /= P Punit.
  rewrite all_map => /allP/(_ A AAs); rewrite /= !/(diagonalizable_for _ _).
  by rewrite conjuMmx ?row_base_free ?stablemx_row_base ?AV.
pose P := \mxcol_i (P_ i *m row_base (V_ i)).
have P_full i : row_full (P_ i) by rewrite row_full_unit.
have PrV i : (P_ i *m row_base (V_ i) :=: V_ i)%MS.
  exact/(eqmx_trans _ (eq_row_base _))/eqmxMfull.
apply/codiagonalizablePfull; eexists _; last exists P; rewrite /=.
- rewrite -sub1mx eqmx_col.
  by under eq_bigr do rewrite (eq_genmx (PrV _)); rewrite -genmx_sums genmxE V1.
apply/allP => A AAs /=; rewrite diagonalizable_for_sum.
- by apply/forallP => i; apply: P_diag.
- rewrite mxdirectE/=.
  under eq_bigr do rewrite (eq_genmx (PrV _)); rewrite -genmx_sums genmxE V1.
  by under eq_bigr do rewrite genmxE PrV; rewrite  -(mxdirectP Vdirect)//= V1.
- by move=> i; rewrite (eqmx_stable _ (PrV _)) ?AV.
- by move=> i; rewrite /row_free eqmxMfull ?eq_row_base ?row_full_unit.
Qed.

Lemma diagonalizable_diag {n} (d : 'rV[F]_n) : diagonalizable (diag_mx d).
Proof.
exists 1%:M; rewrite ?unitmx1// /(diagonalizable_for _ _).
by rewrite conj1mx diag_mx_is_diag.
Qed.
Hint Resolve diagonalizable_diag : core.

Lemma diagonalizable_scalar {n} (a : F) : diagonalizable (a%:M : 'M_n).
Proof. by rewrite -diag_const_mx. Qed.
Hint Resolve diagonalizable_scalar : core.

Lemma diagonalizable0 {n} : diagonalizable (0 : 'M[F]_n).
Proof.
by rewrite (_ : 0 = 0%:M)//; apply/matrixP => i j; rewrite !mxE// mul0rn.
Qed.
Hint Resolve diagonalizable0 : core.

Lemma diagonalizablePeigen {n} {A : 'M[F]_n} :
  diagonalizable A <->
  exists2 rs, uniq rs & (\sum_(r <- rs) eigenspace A r :=: 1%:M)%MS.
Proof.
split=> [df|[rs urs rsP]].
  suff [rs rsP] : exists rs, (\sum_(r <- rs) eigenspace A r :=: 1%:M)%MS.
    exists (undup rs); rewrite ?undup_uniq//; apply: eqmx_trans rsP.
    elim: rs => //= r rs IHrs; rewrite big_cons.
    case: ifPn => in_rs; rewrite ?big_cons; last exact: adds_eqmx.
    apply/(eqmx_trans IHrs)/eqmx_sym/addsmx_idPr.
    have rrs : (index r rs < size rs)%N by rewrite index_mem.
    rewrite (big_nth 0) big_mkord (sumsmx_sup (Ordinal rrs)) ?nth_index//.
  move: df => [P Punit /(diagonalizable_forLR Punit)[d ->]].
  exists [seq d 0 i | i <- enum 'I_n]; rewrite big_image/=.
  apply: (@eqmx_trans _ _ _ _ _ _ P); apply/eqmxP;
    rewrite ?sub1mx ?submx1 ?row_full_unit//.
  rewrite submx_full ?row_full_unit//=.
  apply/row_subP => i; rewrite rowE (sumsmx_sup i)//.
  apply/eigenspaceP; rewrite conjVmx// !mulmxA mulmxK//.
  by rewrite -rowE row_diag_mx scalemxAl.
have mxdirect_eigenspaces : mxdirect (\sum_(i < size rs) eigenspace A rs`_i).
  apply: mxdirect_sum_eigenspace => i j _ _ rsij; apply/val_inj.
  by apply: uniqP rsij; rewrite ?inE.
rewrite (big_nth 0) big_mkord in rsP; apply/codiagonalizable1.
apply/(codiagonalizable_on _ mxdirect_eigenspaces) => // i/=.
  case: n => [|n] in A {mxdirect_eigenspaces} rsP *.
    by rewrite thinmx0 sub0mx.
  by rewrite comm_mx_stable_eigenspace.
apply/codiagonalizable1.
rewrite (@conjmx_eigenvalue _ _ _ rs`_i); first exact: diagonalizable_scalar.
  by rewrite eq_row_base.
by rewrite row_base_free.
Qed.

Lemma diagonalizableP n' (n := n'.+1) (A : 'M[F]_n) :
  diagonalizable A <->
  exists2 rs, uniq rs & mxminpoly A %| \prod_(x <- rs) ('X - x%:P).
Proof.
split=> [[P Punit /diagonalizable_forPex[d /(simmxLR Punit)->]]|].
  rewrite mxminpoly_uconj ?unitmx_inv// mxminpoly_diag.
  by eexists; [|by []]; rewrite undup_uniq.
move=> + /ltac:(apply/diagonalizablePeigen) => -[rs rsu rsP]; exists rs => //.
rewrite (big_nth 0) [X in (X :=: _)%MS](big_nth 0) !big_mkord in rsP *.
rewrite (eq_bigr _ (fun _ _ => eigenspace_poly _ _)).
apply: (eqmx_trans (eqmx_sym (kermxpoly_prod _ _)) (kermxpoly_min _)) => //.
by move=> i j _ _; rewrite coprimep_XsubC root_XsubC nth_uniq.
Qed.

Lemma diagonalizable_conj_diag m n (V : 'M[F]_(m, n)) (d : 'rV[F]_n) :
  stablemx V (diag_mx d) -> row_free V -> diagonalizable (conjmx V (diag_mx d)).
Proof.
case: m n => [|m] [|n] in V d * => Vd rdV; rewrite ?thinmx0.
- by [].
- by [].
- by exfalso; move: rdV; rewrite /row_free mxrank.unlock eqxx orbT.
apply/diagonalizableP; pose u := undup [seq d 0 i | i <- enum 'I_n.+1].
exists u; first by rewrite undup_uniq.
by rewrite (dvdp_trans (mxminpoly_conj (f:=diag_mx d) _ _))// mxminpoly_diag.
Qed.

Lemma codiagonalizableP n (As : seq 'M[F]_n) :
  {in As &, forall A B, comm_mx A B} /\ {in As, forall A, diagonalizable A}
  <-> codiagonalizable As.
Proof.
split => [cdAs|[P Punit /allP/= AsD]]/=; last first.
  split; last by exists P; rewrite // AsD.
  move=> A B AAs BAs; move=> /(_ _ _)/diagonalizable_forPex/sigW in AsD.
  have [[dA /simmxLR->//] [dB /simmxLR->//]] := (AsD _ AAs, AsD _ BAs).
  by rewrite /comm_mx -!conjmxM 1?diag_mxC// inE stablemx_unit ?unitmx_inv.
move: cdAs => -[]; move/(rwP (all_comm_mxP _)) => cdAs cdAs'.
have [k] := ubnP (size As); elim: k => [|k IHk]//= in n As cdAs cdAs' *.
case: As cdAs cdAs' => [|A As]//=; first by exists 1%:M; rewrite ?unitmx1.
rewrite ltnS all_comm_mx_cons => /andP[/allP/(_ _ _)/eqP AAsC AsC dAAs] Ask.
have /diagonalizablePeigen [rs urs rs1] := dAAs _ (mem_head _ _).
rewrite (big_nth 0) big_mkord in rs1.
have eAB (i : 'I_(size rs)) B : B \in A :: As -> stablemx (eigenspace A rs`_i) B.
   case: n => [|n'] in B A As AAsC AsC {dAAs rs1 Ask} * => B_AAs.
      by rewrite thinmx0 sub0mx.
  rewrite comm_mx_stable_eigenspace//.
  by move: B_AAs; rewrite !inE => /predU1P [->//|/AAsC].
apply/(@codiagonalizable_on _ _ _ (_ :: _) rs1) => [|i|i /=].
- apply: mxdirect_sum_eigenspace => i j _ _ rsij; apply/val_inj.
  by apply: uniqP rsij; rewrite ?inE.
- by apply/allP => B B_AAs; rewrite eAB.
rewrite (@conjmx_eigenvalue _ _ _ rs`_i) ?eq_row_base ?row_base_free//.
set Bs := map _ _; suff [P Punit /= PBs] : codiagonalizable Bs.
  exists P; rewrite /= ?PBs ?andbT// /(diagonalizable_for _ _).
  by rewrite conjmx_scalar ?mx_scalar_is_diag// row_free_unit.
apply: IHk; rewrite ?size_map/= ?ltnS//.
  apply/all_comm_mxP => _ _ /mapP[/= B BAs ->] /mapP[/= h hAs ->].
  rewrite -!conjmxM ?inE ?stablemx_row_base ?eAB ?inE ?BAs ?hAs ?orbT//.
  by rewrite (all_comm_mxP _ AsC).
move=> _ /mapP[/= B BAs ->].
have: stablemx (row_base (eigenspace A rs`_i)) B.
  by rewrite stablemx_row_base eAB// inE BAs orbT.
have := dAAs B; rewrite inE BAs orbT => /(_ isT) [P Punit].
move=> /diagonalizable_forPex[D /(simmxLR Punit)->] sePD.
have rAeP : row_free (row_base (eigenspace A rs`_i) *m invmx P).
  by rewrite /row_free mxrankMfree ?row_free_unit ?unitmx_inv// eq_row_base.
rewrite -conjMumx ?unitmx_inv ?row_base_free => [|//|//|//].
apply/diagonalizable_conj_diag => //.
by rewrite stablemx_comp// stablemx_unit ?unitmx_inv.
Qed.

End Diag.

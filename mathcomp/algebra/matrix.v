(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrbool ssrfun eqtype ssrnat seq div choice fintype.
From mathcomp
Require Import finfun bigop prime binomial ssralg finset fingroup finalg.
From mathcomp
Require Import perm zmodp countalg.

(******************************************************************************)
(* Basic concrete linear algebra : definition of type for matrices, and all   *)
(* basic matrix operations including determinant, trace and support for block *)
(* decomposition. Matrices are represented by a row-major list of their       *)
(* coefficients but this implementation is hidden by three levels of wrappers *)
(* (Matrix/Finfun/Tuple) so the matrix type should be treated as abstract and *)
(* handled using only the operations described below:                         *)
(*   'M[R]_(m, n) == the type of m rows by n columns matrices with            *)
(*   'M_(m, n)       coefficients in R; the [R] is optional and is usually    *)
(*                   omitted.                                                 *)
(*  'M[R]_n, 'M_n == the type of n x n square matrices.                       *)
(* 'rV[R]_n, 'rV_n == the type of 1 x n row vectors.                          *)
(* 'cV[R]_n, 'cV_n == the type of n x 1 column vectors.                       *)
(*  \matrix_(i < m, j < n) Expr(i, j) ==                                      *)
(*                   the m x n matrix with general coefficient Expr(i, j),    *)
(*                   with i : 'I_m and j : 'I_n. the < m bound can be omitted *)
(*                   if it is equal to n, though usually both bounds are      *)
(*                   omitted as they can be inferred from the context.        *)
(*  \row_(j < n) Expr(j), \col_(i < m) Expr(i)                                *)
(*                   the row / column vectors with general term Expr; the     *)
(*                   parentheses can be omitted along with the bound.         *)
(* \matrix_(i < m) RowExpr(i) ==                                              *)
(*                   the m x n matrix with row i given by RowExpr(i) : 'rV_n. *)
(*          A i j == the coefficient of matrix A : 'M_(m, n) in column j of   *)
(*                   row i, where i : 'I_m, and j : 'I_n (via the coercion    *)
(*                   fun_of_matrix : matrix >-> Funclass).                    *)
(*     const_mx a == the constant matrix whose entries are all a (dimensions  *)
(*                   should be determined by context).                        *)
(*     map_mx f A == the pointwise image of A by f, i.e., the matrix Af       *)
(*                   congruent to A with Af i j = f (A i j) for all i and j.  *)
(*            A^T == the matrix transpose of A.                               *)
(*        row i A == the i'th row of A (this is a row vector).                *)
(*        col j A == the j'th column of A (a column vector).                  *)
(*       row' i A == A with the i'th row spliced out.                         *)
(*       col' i A == A with the j'th column spliced out.                      *)
(*   xrow i1 i2 A == A with rows i1 and i2 interchanged.                      *)
(*   xcol j1 j2 A == A with columns j1 and j2 interchanged.                   *)
(*   row_perm s A == A : 'M_(m, n) with rows permuted by s : 'S_m.            *)
(*   col_perm s A == A : 'M_(m, n) with columns permuted by s : 'S_n.         *)
(*   row_mx Al Ar == the row block matrix <Al Ar> obtained by contatenating   *)
(*                   two matrices Al and Ar of the same height.               *)
(*   col_mx Au Ad == the column block matrix / Au \ (Au and Ad must have the  *)
(*                   same width).            \ Ad /                           *)
(* block_mx Aul Aur Adl Adr == the block matrix / Aul Aur \                   *)
(*                                              \ Adl Adr /                   *)
(*   [l|r]submx A == the left/right submatrices of a row block matrix A.      *)
(*                   Note that the type of A, 'M_(m, n1 + n2) indicates how A *)
(*                   should be decomposed.                                    *)
(*   [u|d]submx A == the up/down submatrices of a column block matrix A.      *)
(* [u|d][l|r]submx A == the upper left, etc submatrices of a block matrix A.  *)
(* castmx eq_mn A == A : 'M_(m, n) cast to 'M_(m', n') using the equation     *)
(*                   pair eq_mn : (m = m') * (n = n'). This is the usual      *)
(*                   workaround for the syntactic limitations of dependent    *)
(*                   types in Coq, and can be used to introduce a block       *)
(*                   decomposition. It simplifies to A when eq_mn is the      *)
(*                   pair (erefl m, erefl n) (using rewrite /castmx /=).      *)
(* conform_mx B A == A if A and B have the same dimensions, else B.           *)
(*        mxvec A == a row vector of width m * n holding all the entries of   *)
(*                   the m x n matrix A.                                      *)
(* mxvec_index i j == the index of A i j in mxvec A.                          *)
(*       vec_mx v == the inverse of mxvec, reshaping a vector of width m * n  *)
(*                   back into into an m x n rectangular matrix.              *)
(* In 'M[R]_(m, n), R can be any type, but 'M[R]_(m, n) inherits the eqType,  *)
(* choiceType, countType, finType, zmodType structures of R; 'M[R]_(m, n)     *)
(* also has a natural lmodType R structure when R has a ringType structure.   *)
(* Because the type of matrices specifies their dimension, only non-trivial   *)
(* square matrices (of type 'M[R]_n.+1) can inherit the ring structure of R;  *)
(* indeed they then have an algebra structure (lalgType R, or algType R if R  *)
(* is a comRingType, or even unitAlgType if R is a comUnitRingType).          *)
(*   We thus provide separate syntax for the general matrix multiplication,   *)
(* and other operations for matrices over a ringType R:                       *)
(*         A *m B == the matrix product of A and B; the width of A must be    *)
(*                   equal to the height of B.                                *)
(*           a%:M == the scalar matrix with a's on the main diagonal; in      *)
(*                   particular 1%:M denotes the identity matrix, and is is   *)
(*                   equal to 1%R when n is of the form n'.+1 (e.g., n >= 1). *)
(* is_scalar_mx A <=> A is a scalar matrix (A = a%:M for some A).             *)
(*      diag_mx d == the diagonal matrix whose main diagonal is d : 'rV_n.    *)
(*   delta_mx i j == the matrix with a 1 in row i, column j and 0 elsewhere.  *)
(*       pid_mx r == the partial identity matrix with 1s only on the r first  *)
(*                   coefficients of the main diagonal; the dimensions of     *)
(*                   pid_mx r are determined by the context, and pid_mx r can *)
(*                   be rectangular.                                          *)
(*     copid_mx r == the complement to 1%:M of pid_mx r: a square diagonal    *)
(*                   matrix with 1s on all but the first r coefficients on    *)
(*                   its main diagonal.                                       *)
(*      perm_mx s == the n x n permutation matrix for s : 'S_n.               *)
(* tperm_mx i1 i2 == the permutation matrix that exchanges i1 i2 : 'I_n.      *)
(*   is_perm_mx A == A is a permutation matrix.                               *)
(*     lift0_mx A == the 1 + n square matrix block_mx 1 0 0 A when A : 'M_n.  *)
(*          \tr A == the trace of a square matrix A.                          *)
(*         \det A == the determinant of A, using the Leibnitz formula.        *)
(* cofactor i j A == the i, j cofactor of A (the signed i, j minor of A),     *)
(*         \adj A == the adjugate matrix of A (\adj A i j = cofactor j i A).  *)
(*   A \in unitmx == A is invertible (R must be a comUnitRingType).           *)
(*        invmx A == the inverse matrix of A if A \in unitmx A, otherwise A.  *)
(* The following operations provide a correspondance between linear functions *)
(* and matrices:                                                              *)
(*     lin1_mx f == the m x n matrix that emulates via right product          *)
(*                  a (linear) function f : 'rV_m -> 'rV_n on ROW VECTORS     *)
(*      lin_mx f == the (m1 * n1) x (m2 * n2) matrix that emulates, via the   *)
(*                  right multiplication on the mxvec encodings, a linear     *)
(*                  function f : 'M_(m1, n1) -> 'M_(m2, n2)                   *)
(* lin_mul_row u := lin1_mx (mulmx u \o vec_mx) (applies a row-encoded        *)
(*                  function to the row-vector u).                            *)
(*       mulmx A == partially applied matrix multiplication (mulmx A B is     *)
(*                  displayed as A *m B), with, for A : 'M_(m, n), a          *)
(*                  canonical {linear 'M_(n, p) -> 'M(m, p}} structure.       *)
(*      mulmxr A == self-simplifying right-hand matrix multiplication, i.e.,  *)
(*                  mulmxr A B simplifies to B *m A, with, for A : 'M_(n, p), *)
(*                  a canonical {linear 'M_(m, n) -> 'M(m, p}} structure.     *)
(*   lin_mulmx A := lin_mx (mulmx A).                                         *)
(*  lin_mulmxr A := lin_mx (mulmxr A).                                        *)
(* We also extend any finType structure of R to 'M[R]_(m, n), and define:     *)
(*     {'GL_n[R]} == the finGroupType of units of 'M[R]_n.-1.+1.              *)
(*      'GL_n[R]  == the general linear group of all matrices in {'GL_n(R)}.  *)
(*      'GL_n(p)  == 'GL_n['F_p], the general linear group of a prime field.  *)
(*       GLval u  == the coercion of u : {'GL_n(R)} to a matrix.              *)
(*   In addition to the lemmas relevant to these definitions, this file also  *)
(* proves several classic results, including :                                *)
(* - The determinant is a multilinear alternate form.                         *)
(* - The Laplace determinant expansion formulas: expand_det_[row|col].        *)
(* - The Cramer rule : mul_mx_adj & mul_adj_mx.                               *)
(* Finally, as an example of the use of block products, we program and prove  *)
(* the correctness of a classical linear algebra algorithm:                   *)
(*    cormenLUP A == the triangular decomposition (L, U, P) of a nontrivial   *)
(*                   square matrix A into a lower triagular matrix L with 1s  *)
(*                   on the main diagonal, an upper matrix U, and a           *)
(*                   permutation matrix P, such that P * A = L * U.           *)
(* This is example only; we use a different, more precise algorithm to        *)
(* develop the theory of matrix ranks and row spaces in mxalgebra.v           *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.
Import GRing.Theory.
Local Open Scope ring_scope.

Reserved Notation "''M_' n"     (at level 8, n at level 2, format "''M_' n").
Reserved Notation "''rV_' n"    (at level 8, n at level 2, format "''rV_' n").
Reserved Notation "''cV_' n"    (at level 8, n at level 2, format "''cV_' n").
Reserved Notation "''M_' ( n )" (at level 8, only parsing).
Reserved Notation "''M_' ( m , n )" (at level 8, format "''M_' ( m ,  n )").
Reserved Notation "''M[' R ]_ n"    (at level 8, n at level 2, only parsing).
Reserved Notation "''rV[' R ]_ n"   (at level 8, n at level 2, only parsing).
Reserved Notation "''cV[' R ]_ n"   (at level 8, n at level 2, only parsing).
Reserved Notation "''M[' R ]_ ( n )"     (at level 8, only parsing).
Reserved Notation "''M[' R ]_ ( m , n )" (at level 8, only parsing).

Reserved Notation "\matrix_ i E" 
  (at level 36, E at level 36, i at level 2,
   format "\matrix_ i  E").
Reserved Notation "\matrix_ ( i < n ) E"
  (at level 36, E at level 36, i, n at level 50, only parsing).
Reserved Notation "\matrix_ ( i , j ) E"
  (at level 36, E at level 36, i, j at level 50,
   format "\matrix_ ( i ,  j )  E").
Reserved Notation "\matrix[ k ]_ ( i , j ) E"
  (at level 36, E at level 36, i, j at level 50,
   format "\matrix[ k ]_ ( i ,  j )  E").
Reserved Notation "\matrix_ ( i < m , j < n ) E"
  (at level 36, E at level 36, i, m, j, n at level 50, only parsing).
Reserved Notation "\matrix_ ( i , j < n ) E"
  (at level 36, E at level 36, i, j, n at level 50, only parsing).
Reserved Notation "\row_ j E"
  (at level 36, E at level 36, j at level 2,
   format "\row_ j  E").
Reserved Notation "\row_ ( j < n ) E"
  (at level 36, E at level 36, j, n at level 50, only parsing).
Reserved Notation "\col_ j E"
  (at level 36, E at level 36, j at level 2,
   format "\col_ j  E").
Reserved Notation "\col_ ( j < n ) E"
  (at level 36, E at level 36, j, n at level 50, only parsing).

Reserved Notation "x %:M"   (at level 8, format "x %:M").
Reserved Notation "A *m B" (at level 40, left associativity, format "A  *m  B").
Reserved Notation "A ^T"    (at level 8, format "A ^T").
Reserved Notation "\tr A"   (at level 10, A at level 8, format "\tr  A").
Reserved Notation "\det A"  (at level 10, A at level 8, format "\det  A").
Reserved Notation "\adj A"  (at level 10, A at level 8, format "\adj  A").

Local Notation simp := (Monoid.Theory.simpm, oppr0).

(*****************************************************************************)
(****************************Type Definition**********************************)
(*****************************************************************************)

Section MatrixDef.

Variable R : Type.
Variables m n : nat.

(* Basic linear algebra (matrices).                                       *)
(* We use dependent types (ordinals) for the indices so that ranges are   *)
(* mostly inferred automatically                                          *)

Inductive matrix : predArgType := Matrix of {ffun 'I_m * 'I_n -> R}.

Definition mx_val A := let: Matrix g := A in g.

Canonical matrix_subType := Eval hnf in [newType for mx_val].

Fact matrix_key : unit. Proof. by []. Qed.
Definition matrix_of_fun_def F := Matrix [ffun ij => F ij.1 ij.2].
Definition matrix_of_fun k := locked_with k matrix_of_fun_def.
Canonical matrix_unlockable k := [unlockable fun matrix_of_fun k].

Definition fun_of_matrix A (i : 'I_m) (j : 'I_n) := mx_val A (i, j).

Coercion fun_of_matrix : matrix >-> Funclass.

Lemma mxE k F : matrix_of_fun k F =2 F.
Proof. by move=> i j; rewrite unlock /fun_of_matrix /= ffunE. Qed.

Lemma matrixP (A B : matrix) : A =2 B <-> A = B.
Proof.
rewrite /fun_of_matrix; split=> [/= eqAB | -> //].
by apply/val_inj/ffunP=> [[i j]]; apply: eqAB.
Qed.

End MatrixDef.

Bind Scope ring_scope with matrix.

Notation "''M[' R ]_ ( m , n )" := (matrix R m n) (only parsing): type_scope.
Notation "''rV[' R ]_ n" := 'M[R]_(1, n) (only parsing) : type_scope.
Notation "''cV[' R ]_ n" := 'M[R]_(n, 1) (only parsing) : type_scope.
Notation "''M[' R ]_ n" := 'M[R]_(n, n) (only parsing) : type_scope.
Notation "''M[' R ]_ ( n )" := 'M[R]_n (only parsing) : type_scope.
Notation "''M_' ( m , n )" := 'M[_]_(m, n) : type_scope.
Notation "''rV_' n" := 'M_(1, n) : type_scope.
Notation "''cV_' n" := 'M_(n, 1) : type_scope.
Notation "''M_' n" := 'M_(n, n) : type_scope.
Notation "''M_' ( n )" := 'M_n (only parsing) : type_scope.

Notation "\matrix[ k ]_ ( i , j ) E" := (matrix_of_fun k (fun i j => E))
  (at level 36, E at level 36, i, j at level 50): ring_scope.

Notation "\matrix_ ( i < m , j < n ) E" :=
  (@matrix_of_fun _ m n matrix_key (fun i j => E)) (only parsing) : ring_scope.

Notation "\matrix_ ( i , j < n ) E" :=
  (\matrix_(i < n, j < n) E) (only parsing) : ring_scope.

Notation "\matrix_ ( i , j ) E" := (\matrix_(i < _, j < _) E) : ring_scope.

Notation "\matrix_ ( i < m ) E" :=
  (\matrix_(i < m, j < _) @fun_of_matrix _ 1 _ E 0 j)
  (only parsing) : ring_scope.
Notation "\matrix_ i E" := (\matrix_(i < _) E) : ring_scope.

Notation "\col_ ( i < n ) E" := (@matrix_of_fun _ n 1 matrix_key (fun i _ => E))
  (only parsing) : ring_scope.
Notation "\col_ i E" := (\col_(i < _) E) : ring_scope.

Notation "\row_ ( j < n ) E" := (@matrix_of_fun _ 1 n matrix_key (fun _ j => E))
  (only parsing) : ring_scope.
Notation "\row_ j E" := (\row_(j < _) E) : ring_scope.

Definition matrix_eqMixin (R : eqType) m n :=
  Eval hnf in [eqMixin of 'M[R]_(m, n) by <:].
Canonical matrix_eqType (R : eqType) m n:=
  Eval hnf in EqType 'M[R]_(m, n) (matrix_eqMixin R m n).
Definition matrix_choiceMixin (R : choiceType) m n :=
  [choiceMixin of 'M[R]_(m, n) by <:].
Canonical matrix_choiceType (R : choiceType) m n :=
  Eval hnf in ChoiceType 'M[R]_(m, n) (matrix_choiceMixin R m n).
Definition matrix_countMixin (R : countType) m n :=
  [countMixin of 'M[R]_(m, n) by <:].
Canonical matrix_countType (R : countType) m n :=
  Eval hnf in CountType 'M[R]_(m, n) (matrix_countMixin R m n).
Canonical matrix_subCountType (R : countType) m n :=
  Eval hnf in [subCountType of 'M[R]_(m, n)].
Definition matrix_finMixin (R : finType) m n :=
  [finMixin of 'M[R]_(m, n) by <:].
Canonical matrix_finType (R : finType) m n :=
  Eval hnf in FinType 'M[R]_(m, n) (matrix_finMixin R m n).
Canonical matrix_subFinType (R : finType) m n :=
  Eval hnf in [subFinType of 'M[R]_(m, n)].

Lemma card_matrix (F : finType) m n : (#|{: 'M[F]_(m, n)}| = #|F| ^ (m * n))%N.
Proof. by rewrite card_sub card_ffun card_prod !card_ord. Qed.

(*****************************************************************************)
(****** Matrix structural operations (transpose, permutation, blocks) ********)
(*****************************************************************************)

Section MatrixStructural.

Variable R : Type.

(* Constant matrix *)
Fact const_mx_key : unit. Proof. by []. Qed.
Definition const_mx m n a : 'M[R]_(m, n) := \matrix[const_mx_key]_(i, j) a.
Arguments const_mx {m n}.

Section FixedDim.
(* Definitions and properties for which we can work with fixed dimensions. *)

Variables m n : nat.
Implicit Type A : 'M[R]_(m, n).

(* Reshape a matrix, to accomodate the block functions for instance. *)
Definition castmx m' n' (eq_mn : (m = m') * (n = n')) A : 'M_(m', n') :=
  let: erefl in _ = m' := eq_mn.1 return 'M_(m', n') in
  let: erefl in _ = n' := eq_mn.2 return 'M_(m, n') in A.

Definition conform_mx m' n' B A :=
  match m =P m', n =P n' with
  | ReflectT eq_m, ReflectT eq_n => castmx (eq_m, eq_n) A
  | _, _ => B
  end.

(* Transpose a matrix *)
Fact trmx_key : unit. Proof. by []. Qed.
Definition trmx A := \matrix[trmx_key]_(i, j) A j i.

(* Permute a matrix vertically (rows) or horizontally (columns) *)
Fact row_perm_key : unit. Proof. by []. Qed.
Definition row_perm (s : 'S_m) A := \matrix[row_perm_key]_(i, j) A (s i) j.
Fact col_perm_key : unit. Proof. by []. Qed.
Definition col_perm (s : 'S_n) A := \matrix[col_perm_key]_(i, j) A i (s j).

(* Exchange two rows/columns of a matrix *)
Definition xrow i1 i2 := row_perm (tperm i1 i2).
Definition xcol j1 j2 := col_perm (tperm j1 j2).

(* Row/Column sub matrices of a matrix *)
Definition row i0 A := \row_j A i0 j.
Definition col j0 A := \col_i A i j0.

(* Removing a row/column from a matrix *)
Definition row' i0 A := \matrix_(i, j) A (lift i0 i) j.
Definition col' j0 A := \matrix_(i, j) A i (lift j0 j).

Lemma castmx_const m' n' (eq_mn : (m = m') * (n = n')) a :
  castmx eq_mn (const_mx a) = const_mx a.
Proof. by case: eq_mn; case: m' /; case: n' /. Qed.

Lemma trmx_const a : trmx (const_mx a) = const_mx a.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma row_perm_const s a : row_perm s (const_mx a) = const_mx a.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma col_perm_const s a : col_perm s (const_mx a) = const_mx a.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma xrow_const i1 i2 a : xrow i1 i2 (const_mx a) = const_mx a.
Proof. exact: row_perm_const. Qed.

Lemma xcol_const j1 j2 a : xcol j1 j2 (const_mx a) = const_mx a.
Proof. exact: col_perm_const. Qed.

Lemma rowP (u v : 'rV[R]_n) : u 0 =1 v 0 <-> u = v.
Proof. by split=> [eq_uv | -> //]; apply/matrixP=> i; rewrite ord1. Qed.

Lemma rowK u_ i0 : row i0 (\matrix_i u_ i) = u_ i0.
Proof. by apply/rowP=> i'; rewrite !mxE. Qed.

Lemma row_matrixP A B : (forall i, row i A = row i B) <-> A = B.
Proof.
split=> [eqAB | -> //]; apply/matrixP=> i j.
by move/rowP/(_ j): (eqAB i); rewrite !mxE.
Qed.

Lemma colP (u v : 'cV[R]_m) : u^~ 0 =1 v^~ 0 <-> u = v.
Proof. by split=> [eq_uv | -> //]; apply/matrixP=> i j; rewrite ord1. Qed.

Lemma row_const i0 a : row i0 (const_mx a) = const_mx a.
Proof. by apply/rowP=> j; rewrite !mxE. Qed.

Lemma col_const j0 a : col j0 (const_mx a) = const_mx a.
Proof. by apply/colP=> i; rewrite !mxE. Qed.

Lemma row'_const i0 a : row' i0 (const_mx a) = const_mx a.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma col'_const j0 a : col' j0 (const_mx a) = const_mx a.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma col_perm1 A : col_perm 1 A = A.
Proof. by apply/matrixP=> i j; rewrite mxE perm1. Qed.

Lemma row_perm1 A : row_perm 1 A = A.
Proof. by apply/matrixP=> i j; rewrite mxE perm1. Qed.

Lemma col_permM s t A : col_perm (s * t) A = col_perm s (col_perm t A).
Proof. by apply/matrixP=> i j; rewrite !mxE permM. Qed.

Lemma row_permM s t A : row_perm (s * t) A = row_perm s (row_perm t A).
Proof. by apply/matrixP=> i j; rewrite !mxE permM. Qed.

Lemma col_row_permC s t A :
  col_perm s (row_perm t A) = row_perm t (col_perm s A).
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

End FixedDim.

Local Notation "A ^T" := (trmx A) : ring_scope.

Lemma castmx_id m n erefl_mn (A : 'M_(m, n)) : castmx erefl_mn A = A.
Proof. by case: erefl_mn => e_m e_n; rewrite [e_m]eq_axiomK [e_n]eq_axiomK. Qed.

Lemma castmx_comp m1 n1 m2 n2 m3 n3 (eq_m1 : m1 = m2) (eq_n1 : n1 = n2)
                                    (eq_m2 : m2 = m3) (eq_n2 : n2 = n3) A :
  castmx (eq_m2, eq_n2) (castmx (eq_m1, eq_n1) A)
    = castmx (etrans eq_m1 eq_m2, etrans eq_n1 eq_n2) A.
Proof.
by case: m2 / eq_m1 eq_m2; case: m3 /; case: n2 / eq_n1 eq_n2; case: n3 /.
Qed.

Lemma castmxK m1 n1 m2 n2 (eq_m : m1 = m2) (eq_n : n1 = n2) :
  cancel (castmx (eq_m, eq_n)) (castmx (esym eq_m, esym eq_n)).
Proof. by case: m2 / eq_m; case: n2 / eq_n. Qed.

Lemma castmxKV m1 n1 m2 n2 (eq_m : m1 = m2) (eq_n : n1 = n2) :
  cancel (castmx (esym eq_m, esym eq_n)) (castmx (eq_m, eq_n)).
Proof. by case: m2 / eq_m; case: n2 / eq_n. Qed.

(* This can be use to reverse an equation that involves a cast. *)
Lemma castmx_sym m1 n1 m2 n2 (eq_m : m1 = m2) (eq_n : n1 = n2) A1 A2 :
  A1 = castmx (eq_m, eq_n) A2 -> A2 = castmx (esym eq_m, esym eq_n) A1.
Proof. by move/(canLR (castmxK _ _)). Qed.

Lemma castmxE m1 n1 m2 n2 (eq_mn : (m1 = m2) * (n1 = n2)) A i j :
  castmx eq_mn A i j =
     A (cast_ord (esym eq_mn.1) i) (cast_ord (esym eq_mn.2) j).
Proof.
by do [case: eq_mn; case: m2 /; case: n2 /] in A i j *; rewrite !cast_ord_id.
Qed.

Lemma conform_mx_id m n (B A : 'M_(m, n)) : conform_mx B A = A.
Proof. by rewrite /conform_mx; do 2!case: eqP => // *; rewrite castmx_id. Qed.

Lemma nonconform_mx m m' n n' (B : 'M_(m', n')) (A : 'M_(m, n)) :
  (m != m') || (n != n') -> conform_mx B A = B.
Proof. by rewrite /conform_mx; do 2!case: eqP. Qed.

Lemma conform_castmx m1 n1 m2 n2 m3 n3
                     (e_mn : (m2 = m3) * (n2 = n3)) (B : 'M_(m1, n1)) A :
  conform_mx B (castmx e_mn A) = conform_mx B A.
Proof. by do [case: e_mn; case: m3 /; case: n3 /] in A *. Qed.

Lemma trmxK m n : cancel (@trmx m n) (@trmx n m).
Proof. by move=> A; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma trmx_inj m n : injective (@trmx m n).
Proof. exact: can_inj (@trmxK m n). Qed.

Lemma trmx_cast m1 n1 m2 n2 (eq_mn : (m1 = m2) * (n1 = n2)) A :
  (castmx eq_mn A)^T = castmx (eq_mn.2, eq_mn.1) A^T.
Proof.
by case: eq_mn => eq_m eq_n; apply/matrixP=> i j; rewrite !(mxE, castmxE).
Qed.

Lemma tr_row_perm m n s (A : 'M_(m, n)) : (row_perm s A)^T = col_perm s A^T.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma tr_col_perm m n s (A : 'M_(m, n)) : (col_perm s A)^T = row_perm s A^T.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma tr_xrow m n i1 i2 (A : 'M_(m, n)) : (xrow i1 i2 A)^T = xcol i1 i2 A^T.
Proof. exact: tr_row_perm. Qed.

Lemma tr_xcol m n j1 j2 (A : 'M_(m, n)) : (xcol j1 j2 A)^T = xrow j1 j2 A^T.
Proof. exact: tr_col_perm. Qed.

Lemma row_id n i (V : 'rV_n) : row i V = V.
Proof. by apply/rowP=> j; rewrite mxE [i]ord1. Qed.

Lemma col_id n j (V : 'cV_n) : col j V = V.
Proof. by apply/colP=> i; rewrite mxE [j]ord1. Qed.

Lemma row_eq m1 m2 n i1 i2 (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)) :
  row i1 A1 = row i2 A2 -> A1 i1 =1 A2 i2.
Proof. by move/rowP=> eqA12 j; have:= eqA12 j; rewrite !mxE. Qed.

Lemma col_eq m n1 n2 j1 j2 (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)) :
  col j1 A1 = col j2 A2 -> A1^~ j1 =1 A2^~ j2.
Proof. by move/colP=> eqA12 i; have:= eqA12 i; rewrite !mxE. Qed.

Lemma row'_eq m n i0 (A B : 'M_(m, n)) :
  row' i0 A = row' i0 B -> {in predC1 i0, A =2 B}.
Proof.
move/matrixP=> eqAB' i; rewrite !inE eq_sym; case/unlift_some=> i' -> _ j.
by have:= eqAB' i' j; rewrite !mxE.
Qed.

Lemma col'_eq m n j0 (A B : 'M_(m, n)) :
  col' j0 A = col' j0 B -> forall i, {in predC1 j0, A i =1 B i}.
Proof.
move/matrixP=> eqAB' i j; rewrite !inE eq_sym; case/unlift_some=> j' -> _.
by have:= eqAB' i j'; rewrite !mxE.
Qed.

Lemma tr_row m n i0 (A : 'M_(m, n)) : (row i0 A)^T = col i0 A^T.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma tr_row' m n i0 (A : 'M_(m, n)) : (row' i0 A)^T = col' i0 A^T.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma tr_col m n j0 (A : 'M_(m, n)) : (col j0 A)^T = row j0 A^T.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma tr_col' m n j0 (A : 'M_(m, n)) : (col' j0 A)^T = row' j0 A^T.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Ltac split_mxE := apply/matrixP=> i j; do ![rewrite mxE | case: split => ?].

Section CutPaste.

Variables m m1 m2 n n1 n2 : nat.

(* Concatenating two matrices, in either direction. *)

Fact row_mx_key : unit. Proof. by []. Qed.
Definition row_mx (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)) : 'M[R]_(m, n1 + n2) :=
  \matrix[row_mx_key]_(i, j)
     match split j with inl j1 => A1 i j1 | inr j2 => A2 i j2 end.

Fact col_mx_key : unit. Proof. by []. Qed.
Definition col_mx (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)) : 'M[R]_(m1 + m2, n) :=
  \matrix[col_mx_key]_(i, j)
     match split i with inl i1 => A1 i1 j | inr i2 => A2 i2 j end.

(* Left/Right | Up/Down submatrices of a rows | columns matrix.   *)
(* The shape of the (dependent) width parameters of the type of A *)
(* determines which submatrix is selected.                        *)

Fact lsubmx_key : unit. Proof. by []. Qed.
Definition lsubmx (A : 'M[R]_(m, n1 + n2)) :=
  \matrix[lsubmx_key]_(i, j) A i (lshift n2 j).

Fact rsubmx_key : unit. Proof. by []. Qed.
Definition rsubmx (A : 'M[R]_(m, n1 + n2)) :=
  \matrix[rsubmx_key]_(i, j) A i (rshift n1 j).

Fact usubmx_key : unit. Proof. by []. Qed.
Definition usubmx (A : 'M[R]_(m1 + m2, n)) :=
  \matrix[usubmx_key]_(i, j) A (lshift m2 i) j.

Fact dsubmx_key : unit. Proof. by []. Qed.
Definition dsubmx (A : 'M[R]_(m1 + m2, n)) :=
  \matrix[dsubmx_key]_(i, j) A (rshift m1 i) j.

Lemma row_mxEl A1 A2 i j : row_mx A1 A2 i (lshift n2 j) = A1 i j.
Proof. by rewrite mxE (unsplitK (inl _ _)). Qed.

Lemma row_mxKl A1 A2 : lsubmx (row_mx A1 A2) = A1.
Proof. by apply/matrixP=> i j; rewrite mxE row_mxEl. Qed.

Lemma row_mxEr A1 A2 i j : row_mx A1 A2 i (rshift n1 j) = A2 i j.
Proof. by rewrite mxE (unsplitK (inr _ _)). Qed.

Lemma row_mxKr A1 A2 : rsubmx (row_mx A1 A2) = A2.
Proof. by apply/matrixP=> i j; rewrite mxE row_mxEr. Qed.

Lemma hsubmxK A : row_mx (lsubmx A) (rsubmx A) = A.
Proof.
apply/matrixP=> i j; rewrite !mxE.
by case: splitP => k Dk //=; rewrite !mxE //=; congr (A _ _); apply: val_inj.
Qed.

Lemma col_mxEu A1 A2 i j : col_mx A1 A2 (lshift m2 i) j = A1 i j.
Proof. by rewrite mxE (unsplitK (inl _ _)). Qed.

Lemma col_mxKu A1 A2 : usubmx (col_mx A1 A2) = A1.
Proof. by apply/matrixP=> i j; rewrite mxE col_mxEu. Qed.

Lemma col_mxEd A1 A2 i j : col_mx A1 A2 (rshift m1 i) j = A2 i j.
Proof. by rewrite mxE (unsplitK (inr _ _)). Qed.

Lemma col_mxKd A1 A2 : dsubmx (col_mx A1 A2) = A2.
Proof. by apply/matrixP=> i j; rewrite mxE col_mxEd. Qed.

Lemma eq_row_mx A1 A2 B1 B2 : row_mx A1 A2 = row_mx B1 B2 -> A1 = B1 /\ A2 = B2.
Proof.
move=> eqAB; move: (congr1 lsubmx eqAB) (congr1 rsubmx eqAB).
by rewrite !(row_mxKl, row_mxKr).
Qed.

Lemma eq_col_mx A1 A2 B1 B2 : col_mx A1 A2 = col_mx B1 B2 -> A1 = B1 /\ A2 = B2.
Proof.
move=> eqAB; move: (congr1 usubmx eqAB) (congr1 dsubmx eqAB).
by rewrite !(col_mxKu, col_mxKd).
Qed.

Lemma row_mx_const a : row_mx (const_mx a) (const_mx a) = const_mx a.
Proof. by split_mxE. Qed.

Lemma col_mx_const a : col_mx (const_mx a) (const_mx a) = const_mx a.
Proof. by split_mxE. Qed.

End CutPaste.

Lemma trmx_lsub m n1 n2 (A : 'M_(m, n1 + n2)) : (lsubmx A)^T = usubmx A^T.
Proof. by split_mxE. Qed.

Lemma trmx_rsub m n1 n2 (A : 'M_(m, n1 + n2)) : (rsubmx A)^T = dsubmx A^T.
Proof. by split_mxE. Qed.

Lemma tr_row_mx m n1 n2 (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)) :
  (row_mx A1 A2)^T = col_mx A1^T A2^T.
Proof. by split_mxE. Qed.

Lemma tr_col_mx m1 m2 n (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)) :
  (col_mx A1 A2)^T = row_mx A1^T A2^T.
Proof. by split_mxE. Qed.

Lemma trmx_usub m1 m2 n (A : 'M_(m1 + m2, n)) : (usubmx A)^T = lsubmx A^T.
Proof. by split_mxE. Qed.

Lemma trmx_dsub m1 m2 n (A : 'M_(m1 + m2, n)) : (dsubmx A)^T = rsubmx A^T.
Proof. by split_mxE. Qed.

Lemma vsubmxK m1 m2 n (A : 'M_(m1 + m2, n)) : col_mx (usubmx A) (dsubmx A) = A.
Proof. by apply: trmx_inj; rewrite tr_col_mx trmx_usub trmx_dsub hsubmxK. Qed.

Lemma cast_row_mx m m' n1 n2 (eq_m : m = m') A1 A2 :
  castmx (eq_m, erefl _) (row_mx A1 A2)
    = row_mx (castmx (eq_m, erefl n1) A1) (castmx (eq_m, erefl n2) A2).
Proof. by case: m' / eq_m. Qed.

Lemma cast_col_mx m1 m2 n n' (eq_n : n = n') A1 A2 :
  castmx (erefl _, eq_n) (col_mx A1 A2)
    = col_mx (castmx (erefl m1, eq_n) A1) (castmx (erefl m2, eq_n) A2).
Proof. by case: n' / eq_n. Qed.

(* This lemma has Prenex Implicits to help RL rewrititng with castmx_sym. *)
Lemma row_mxA m n1 n2 n3 (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)) (A3 : 'M_(m, n3)) :
  let cast := (erefl m, esym (addnA n1 n2 n3)) in
  row_mx A1 (row_mx A2 A3) = castmx cast (row_mx (row_mx A1 A2) A3).
Proof.
apply: (canRL (castmxKV _ _)); apply/matrixP=> i j.
rewrite castmxE !mxE cast_ord_id; case: splitP => j1 /= def_j.
  have: (j < n1 + n2) && (j < n1) by rewrite def_j lshift_subproof /=.
  by move: def_j; do 2![case: splitP => // ? ->; rewrite ?mxE] => /ord_inj->.
case: splitP def_j => j2 ->{j} def_j; rewrite !mxE.
  have: ~~ (j2 < n1) by rewrite -leqNgt def_j leq_addr.
  have: j1 < n2 by rewrite -(ltn_add2l n1) -def_j.
  by move: def_j; do 2![case: splitP => // ? ->] => /addnI/val_inj->.
have: ~~ (j1 < n2) by rewrite -leqNgt -(leq_add2l n1) -def_j leq_addr.
by case: splitP def_j => // ? ->; rewrite addnA => /addnI/val_inj->.
Qed.
Definition row_mxAx := row_mxA. (* bypass Prenex Implicits. *)

(* This lemma has Prenex Implicits to help RL rewrititng with castmx_sym. *)
Lemma col_mxA m1 m2 m3 n (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)) (A3 : 'M_(m3, n)) :
  let cast := (esym (addnA m1 m2 m3), erefl n) in
  col_mx A1 (col_mx A2 A3) = castmx cast (col_mx (col_mx A1 A2) A3).
Proof. by apply: trmx_inj; rewrite trmx_cast !tr_col_mx -row_mxA. Qed.
Definition col_mxAx := col_mxA. (* bypass Prenex Implicits. *)

Lemma row_row_mx m n1 n2 i0 (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)) :
  row i0 (row_mx A1 A2) = row_mx (row i0 A1) (row i0 A2).
Proof.
by apply/matrixP=> i j; rewrite !mxE; case: (split j) => j'; rewrite mxE.
Qed.

Lemma col_col_mx m1 m2 n j0 (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)) :
  col j0 (col_mx A1 A2) = col_mx (col j0 A1) (col j0 A2).
Proof. by apply: trmx_inj; rewrite !(tr_col, tr_col_mx, row_row_mx). Qed.

Lemma row'_row_mx m n1 n2 i0 (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)) :
  row' i0 (row_mx A1 A2) = row_mx (row' i0 A1) (row' i0 A2).
Proof.
by apply/matrixP=> i j; rewrite !mxE; case: (split j) => j'; rewrite mxE.
Qed.

Lemma col'_col_mx m1 m2 n j0 (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)) :
  col' j0 (col_mx A1 A2) = col_mx (col' j0 A1) (col' j0 A2).
Proof. by apply: trmx_inj; rewrite !(tr_col', tr_col_mx, row'_row_mx). Qed.

Lemma colKl m n1 n2 j1 (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)) :
  col (lshift n2 j1) (row_mx A1 A2) = col j1 A1.
Proof. by apply/matrixP=> i j; rewrite !(row_mxEl, mxE). Qed.

Lemma colKr m n1 n2 j2 (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)) :
  col (rshift n1 j2) (row_mx A1 A2) = col j2 A2.
Proof. by apply/matrixP=> i j; rewrite !(row_mxEr, mxE). Qed.

Lemma rowKu m1 m2 n i1 (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)) :
  row (lshift m2 i1) (col_mx A1 A2) = row i1 A1.
Proof. by apply/matrixP=> i j; rewrite !(col_mxEu, mxE). Qed.

Lemma rowKd m1 m2 n i2 (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)) :
  row (rshift m1 i2) (col_mx A1 A2) = row i2 A2.
Proof. by apply/matrixP=> i j; rewrite !(col_mxEd, mxE). Qed.

Lemma col'Kl m n1 n2 j1 (A1 : 'M_(m, n1.+1)) (A2 : 'M_(m, n2)) :
  col' (lshift n2 j1) (row_mx A1 A2) = row_mx (col' j1 A1) A2.
Proof.
apply/matrixP=> i /= j; symmetry; rewrite 2!mxE.
case: splitP => j' def_j'.
  rewrite mxE -(row_mxEl _ A2); congr (row_mx _ _ _); apply: ord_inj.
  by rewrite /= def_j'.
rewrite -(row_mxEr A1); congr (row_mx _ _ _); apply: ord_inj => /=.
by rewrite /bump def_j' -ltnS -addSn ltn_addr.
Qed.

Lemma row'Ku m1 m2 n i1 (A1 : 'M_(m1.+1, n)) (A2 : 'M_(m2, n)) :
  row' (lshift m2 i1) (@col_mx m1.+1 m2 n A1 A2) = col_mx (row' i1 A1) A2.
Proof.
by apply: trmx_inj; rewrite tr_col_mx !(@tr_row' _.+1) (@tr_col_mx _.+1) col'Kl.
Qed.

Lemma mx'_cast m n : 'I_n -> (m + n.-1)%N = (m + n).-1.
Proof. by case=> j /ltn_predK <-; rewrite addnS. Qed.

Lemma col'Kr m n1 n2 j2 (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)) :
  col' (rshift n1 j2) (@row_mx m n1 n2 A1 A2)
    = castmx (erefl m, mx'_cast n1 j2) (row_mx A1 (col' j2 A2)).
Proof.
apply/matrixP=> i j; symmetry; rewrite castmxE mxE cast_ord_id.
case: splitP => j' /= def_j.
  rewrite mxE -(row_mxEl _ A2); congr (row_mx _ _ _); apply: ord_inj.
  by rewrite /= def_j /bump leqNgt ltn_addr.
rewrite 2!mxE -(row_mxEr A1); congr (row_mx _ _ _ _); apply: ord_inj.
by rewrite /= def_j /bump leq_add2l addnCA.
Qed.

Lemma row'Kd m1 m2 n i2 (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)) :
  row' (rshift m1 i2) (col_mx A1 A2)
    = castmx (mx'_cast m1 i2, erefl n) (col_mx A1 (row' i2 A2)).
Proof. by apply: trmx_inj; rewrite trmx_cast !(tr_row', tr_col_mx) col'Kr. Qed.

Section Block.

Variables m1 m2 n1 n2 : nat.

(* Building a block matrix from 4 matrices :               *)
(*  up left, up right, down left and down right components *)

Definition block_mx Aul Aur Adl Adr : 'M_(m1 + m2, n1 + n2) :=
  col_mx (row_mx Aul Aur) (row_mx Adl Adr).

Lemma eq_block_mx Aul Aur Adl Adr Bul Bur Bdl Bdr :
 block_mx Aul Aur Adl Adr = block_mx Bul Bur Bdl Bdr ->
  [/\ Aul = Bul, Aur = Bur, Adl = Bdl & Adr = Bdr].
Proof. by case/eq_col_mx; do 2!case/eq_row_mx=> -> ->. Qed.

Lemma block_mx_const a :
  block_mx (const_mx a) (const_mx a) (const_mx a) (const_mx a) = const_mx a.
Proof. by split_mxE. Qed.

Section CutBlock.

Variable A : matrix R (m1 + m2) (n1 + n2).

Definition ulsubmx := lsubmx (usubmx A).
Definition ursubmx := rsubmx (usubmx A).
Definition dlsubmx := lsubmx (dsubmx A).
Definition drsubmx := rsubmx (dsubmx A).

Lemma submxK : block_mx ulsubmx ursubmx dlsubmx drsubmx = A.
Proof. by rewrite /block_mx !hsubmxK vsubmxK. Qed.

End CutBlock.

Section CatBlock.

Variables (Aul : 'M[R]_(m1, n1)) (Aur : 'M[R]_(m1, n2)).
Variables (Adl : 'M[R]_(m2, n1)) (Adr : 'M[R]_(m2, n2)).

Let A := block_mx Aul Aur Adl Adr.

Lemma block_mxEul i j : A (lshift m2 i) (lshift n2 j) = Aul i j.
Proof. by rewrite col_mxEu row_mxEl. Qed.
Lemma block_mxKul : ulsubmx A = Aul.
Proof. by rewrite /ulsubmx col_mxKu row_mxKl. Qed.

Lemma block_mxEur i j : A (lshift m2 i) (rshift n1 j) = Aur i j.
Proof. by rewrite col_mxEu row_mxEr. Qed.
Lemma block_mxKur : ursubmx A = Aur.
Proof. by rewrite /ursubmx col_mxKu row_mxKr. Qed.

Lemma block_mxEdl i j : A (rshift m1 i) (lshift n2 j) = Adl i j.
Proof. by rewrite col_mxEd row_mxEl. Qed.
Lemma block_mxKdl : dlsubmx A = Adl.
Proof. by rewrite /dlsubmx col_mxKd row_mxKl. Qed.

Lemma block_mxEdr i j : A (rshift m1 i) (rshift n1 j) = Adr i j.
Proof. by rewrite col_mxEd row_mxEr. Qed.
Lemma block_mxKdr : drsubmx A = Adr.
Proof. by rewrite /drsubmx col_mxKd row_mxKr. Qed.

Lemma block_mxEv : A = col_mx (row_mx Aul Aur) (row_mx Adl Adr).
Proof. by []. Qed.

End CatBlock.

End Block.

Section TrCutBlock.

Variables m1 m2 n1 n2 : nat.
Variable A : 'M[R]_(m1 + m2, n1 + n2).

Lemma trmx_ulsub : (ulsubmx A)^T = ulsubmx A^T.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma trmx_ursub : (ursubmx A)^T = dlsubmx A^T.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma trmx_dlsub : (dlsubmx A)^T = ursubmx A^T.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma trmx_drsub : (drsubmx A)^T = drsubmx A^T.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

End TrCutBlock.

Section TrBlock.
Variables m1 m2 n1 n2 : nat.
Variables (Aul : 'M[R]_(m1, n1)) (Aur : 'M[R]_(m1, n2)).
Variables (Adl : 'M[R]_(m2, n1)) (Adr : 'M[R]_(m2, n2)).

Lemma tr_block_mx :
 (block_mx Aul Aur Adl Adr)^T = block_mx Aul^T Adl^T Aur^T Adr^T.
Proof.
rewrite -[_^T]submxK -trmx_ulsub -trmx_ursub -trmx_dlsub -trmx_drsub.
by rewrite block_mxKul block_mxKur block_mxKdl block_mxKdr.
Qed.

Lemma block_mxEh :
  block_mx Aul Aur Adl Adr = row_mx (col_mx Aul Adl) (col_mx Aur Adr).
Proof. by apply: trmx_inj; rewrite tr_block_mx tr_row_mx 2!tr_col_mx. Qed.
End TrBlock.

(* This lemma has Prenex Implicits to help RL rewrititng with castmx_sym. *)
Lemma block_mxA m1 m2 m3 n1 n2 n3
   (A11 : 'M_(m1, n1)) (A12 : 'M_(m1, n2)) (A13 : 'M_(m1, n3))
   (A21 : 'M_(m2, n1)) (A22 : 'M_(m2, n2)) (A23 : 'M_(m2, n3))
   (A31 : 'M_(m3, n1)) (A32 : 'M_(m3, n2)) (A33 : 'M_(m3, n3)) :
  let cast := (esym (addnA m1 m2 m3), esym (addnA n1 n2 n3)) in
  let row1 := row_mx A12 A13 in let col1 := col_mx A21 A31 in
  let row3 := row_mx A31 A32 in let col3 := col_mx A13 A23 in
  block_mx A11 row1 col1 (block_mx A22 A23 A32 A33)
    = castmx cast (block_mx (block_mx A11 A12 A21 A22) col3 row3 A33).
Proof.
rewrite /= block_mxEh !col_mxA -cast_row_mx -block_mxEv -block_mxEh.
rewrite block_mxEv block_mxEh !row_mxA -cast_col_mx -block_mxEh -block_mxEv.
by rewrite castmx_comp etrans_id.
Qed.
Definition block_mxAx := block_mxA. (* Bypass Prenex Implicits *)

(* Bijections mxvec : 'M_(m, n) <----> 'rV_(m * n) : vec_mx *)
Section VecMatrix.

Variables m n : nat.

Lemma mxvec_cast : #|{:'I_m * 'I_n}| = (m * n)%N.
Proof. by rewrite card_prod !card_ord. Qed.

Definition mxvec_index (i : 'I_m) (j : 'I_n) :=
  cast_ord mxvec_cast (enum_rank (i, j)).

Variant is_mxvec_index : 'I_(m * n) -> Type :=
  IsMxvecIndex i j : is_mxvec_index (mxvec_index i j).

Lemma mxvec_indexP k : is_mxvec_index k.
Proof.
rewrite -[k](cast_ordK (esym mxvec_cast)) esymK.
by rewrite -[_ k]enum_valK; case: (enum_val _).
Qed.

Coercion pair_of_mxvec_index k (i_k : is_mxvec_index k) :=
  let: IsMxvecIndex i j := i_k in (i, j).

Definition mxvec (A : 'M[R]_(m, n)) :=
  castmx (erefl _, mxvec_cast) (\row_k A (enum_val k).1 (enum_val k).2).

Fact vec_mx_key : unit. Proof. by []. Qed.
Definition vec_mx (u : 'rV[R]_(m * n)) :=
  \matrix[vec_mx_key]_(i, j) u 0 (mxvec_index i j).

Lemma mxvecE A i j : mxvec A 0 (mxvec_index i j) = A i j.
Proof. by rewrite castmxE mxE cast_ordK enum_rankK. Qed.

Lemma mxvecK : cancel mxvec vec_mx.
Proof. by move=> A; apply/matrixP=> i j; rewrite mxE mxvecE. Qed.

Lemma vec_mxK : cancel vec_mx mxvec.
Proof.
by move=> u; apply/rowP=> k; case/mxvec_indexP: k => i j; rewrite mxvecE mxE.
Qed.

Lemma curry_mxvec_bij : {on 'I_(m * n), bijective (prod_curry mxvec_index)}.
Proof.
exists (enum_val \o cast_ord (esym mxvec_cast)) => [[i j] _ | k _] /=.
  by rewrite cast_ordK enum_rankK.
by case/mxvec_indexP: k => i j /=; rewrite cast_ordK enum_rankK.
Qed.

End VecMatrix.

End MatrixStructural.

Arguments const_mx {R m n}.
Arguments row_mxA {R m n1 n2 n3 A1 A2 A3}.
Arguments col_mxA {R m1 m2 m3 n A1 A2 A3}.
Arguments block_mxA
  {R m1 m2 m3 n1 n2 n3 A11 A12 A13 A21 A22 A23 A31 A32 A33}.
Prenex Implicits castmx trmx trmxK lsubmx rsubmx usubmx dsubmx row_mx col_mx.
Prenex Implicits block_mx ulsubmx ursubmx dlsubmx drsubmx.
Prenex Implicits mxvec vec_mx mxvec_indexP mxvecK vec_mxK.
Arguments trmx_inj {R m n} [A1 A2] eqA12t : rename.

Notation "A ^T" := (trmx A) : ring_scope.

(* Matrix parametricity. *)
Section MapMatrix.

Variables (aT rT : Type) (f : aT -> rT).

Fact map_mx_key : unit. Proof. by []. Qed.
Definition map_mx m n (A : 'M_(m, n)) := \matrix[map_mx_key]_(i, j) f (A i j).

Notation "A ^f" := (map_mx A) : ring_scope.

Section OneMatrix.

Variables (m n : nat) (A : 'M[aT]_(m, n)).

Lemma map_trmx : A^f^T = A^T^f.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map_const_mx a : (const_mx a)^f = const_mx (f a) :> 'M_(m, n).
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map_row i : (row i A)^f = row i A^f.
Proof. by apply/rowP=> j; rewrite !mxE. Qed.

Lemma map_col j : (col j A)^f = col j A^f.
Proof. by apply/colP=> i; rewrite !mxE. Qed.

Lemma map_row' i0 : (row' i0 A)^f = row' i0 A^f.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map_col' j0 : (col' j0 A)^f = col' j0 A^f.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map_row_perm s : (row_perm s A)^f = row_perm s A^f.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map_col_perm s : (col_perm s A)^f = col_perm s A^f.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map_xrow i1 i2 : (xrow i1 i2 A)^f = xrow i1 i2 A^f.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map_xcol j1 j2 : (xcol j1 j2 A)^f = xcol j1 j2 A^f.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map_castmx m' n' c : (castmx c A)^f = castmx c A^f :> 'M_(m', n').
Proof. by apply/matrixP=> i j; rewrite !(castmxE, mxE). Qed.

Lemma map_conform_mx m' n' (B : 'M_(m', n')) :
  (conform_mx B A)^f = conform_mx B^f A^f.
Proof.
move: B; have [[<- <-] B|] := eqVneq (m, n) (m', n').
  by rewrite !conform_mx_id.
by rewrite negb_and => neq_mn B; rewrite !nonconform_mx.
Qed.

Lemma map_mxvec : (mxvec A)^f = mxvec A^f.
Proof. by apply/rowP=> i; rewrite !(castmxE, mxE). Qed.

Lemma map_vec_mx (v : 'rV_(m * n)) : (vec_mx v)^f = vec_mx v^f.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

End OneMatrix.

Section Block.

Variables m1 m2 n1 n2 : nat.
Variables (Aul : 'M[aT]_(m1, n1)) (Aur : 'M[aT]_(m1, n2)).
Variables (Adl : 'M[aT]_(m2, n1)) (Adr : 'M[aT]_(m2, n2)).
Variables (Bh : 'M[aT]_(m1, n1 + n2)) (Bv : 'M[aT]_(m1 + m2, n1)).
Variable B : 'M[aT]_(m1 + m2, n1 + n2).

Lemma map_row_mx : (row_mx Aul Aur)^f = row_mx Aul^f Aur^f.
Proof. by apply/matrixP=> i j; do 2![rewrite !mxE //; case: split => ?]. Qed.

Lemma map_col_mx : (col_mx Aul Adl)^f = col_mx Aul^f Adl^f.
Proof. by apply/matrixP=> i j; do 2![rewrite !mxE //; case: split => ?]. Qed.

Lemma map_block_mx :
  (block_mx Aul Aur Adl Adr)^f = block_mx Aul^f Aur^f Adl^f Adr^f.
Proof. by apply/matrixP=> i j; do 3![rewrite !mxE //; case: split => ?]. Qed.

Lemma map_lsubmx : (lsubmx Bh)^f = lsubmx Bh^f.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map_rsubmx : (rsubmx Bh)^f = rsubmx Bh^f.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map_usubmx : (usubmx Bv)^f = usubmx Bv^f.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map_dsubmx : (dsubmx Bv)^f = dsubmx Bv^f.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map_ulsubmx : (ulsubmx B)^f = ulsubmx B^f.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map_ursubmx : (ursubmx B)^f = ursubmx B^f.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map_dlsubmx : (dlsubmx B)^f = dlsubmx B^f.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map_drsubmx : (drsubmx B)^f = drsubmx B^f.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

End Block.

End MapMatrix.

Arguments map_mx {aT rT} f {m n} A.

(*****************************************************************************)
(********************* Matrix Zmodule (additive) structure *******************)
(*****************************************************************************)

Section MatrixZmodule.

Variable V : zmodType.

Section FixedDim.

Variables m n : nat.
Implicit Types A B : 'M[V]_(m, n).

Fact oppmx_key : unit. Proof. by []. Qed.
Fact addmx_key : unit. Proof. by []. Qed.
Definition oppmx A := \matrix[oppmx_key]_(i, j) (- A i j).
Definition addmx A B := \matrix[addmx_key]_(i, j) (A i j + B i j).
(* In principle, diag_mx and scalar_mx could be defined here, but since they *)
(* only make sense with the graded ring operations, we defer them to the     *)
(* next section.                                                             *)

Lemma addmxA : associative addmx.
Proof. by move=> A B C; apply/matrixP=> i j; rewrite !mxE addrA. Qed.

Lemma addmxC : commutative addmx.
Proof. by move=> A B; apply/matrixP=> i j; rewrite !mxE addrC. Qed.

Lemma add0mx : left_id (const_mx 0) addmx.
Proof. by move=> A; apply/matrixP=> i j; rewrite !mxE add0r. Qed.

Lemma addNmx : left_inverse (const_mx 0) oppmx addmx.
Proof. by move=> A; apply/matrixP=> i j; rewrite !mxE addNr. Qed.

Definition matrix_zmodMixin := ZmodMixin addmxA addmxC add0mx addNmx.

Canonical matrix_zmodType := Eval hnf in ZmodType 'M[V]_(m, n) matrix_zmodMixin.

Lemma mulmxnE A d i j : (A *+ d) i j = A i j *+ d.
Proof. by elim: d => [|d IHd]; rewrite ?mulrS mxE ?IHd. Qed.

Lemma summxE I r (P : pred I) (E : I -> 'M_(m, n)) i j :
  (\sum_(k <- r | P k) E k) i j = \sum_(k <- r | P k) E k i j.
Proof. by apply: (big_morph (fun A => A i j)) => [A B|]; rewrite mxE. Qed.

Lemma const_mx_is_additive : additive const_mx.
Proof. by move=> a b; apply/matrixP=> i j; rewrite !mxE. Qed.
Canonical const_mx_additive := Additive const_mx_is_additive.

End FixedDim.

Section Additive.

Variables (m n p q : nat) (f : 'I_p -> 'I_q -> 'I_m) (g : 'I_p -> 'I_q -> 'I_n).

Definition swizzle_mx k (A : 'M[V]_(m, n)) :=
  \matrix[k]_(i, j) A (f i j) (g i j).

Lemma swizzle_mx_is_additive k : additive (swizzle_mx k).
Proof. by move=> A B; apply/matrixP=> i j; rewrite !mxE. Qed.
Canonical swizzle_mx_additive k := Additive (swizzle_mx_is_additive k).

End Additive.

Local Notation SwizzleAdd op := [additive of op as swizzle_mx _ _ _].

Canonical trmx_additive m n := SwizzleAdd (@trmx V m n).
Canonical row_additive m n i := SwizzleAdd (@row V m n i).
Canonical col_additive m n j := SwizzleAdd (@col V m n j).
Canonical row'_additive m n i := SwizzleAdd (@row' V m n i).
Canonical col'_additive m n j := SwizzleAdd (@col' V m n j).
Canonical row_perm_additive m n s := SwizzleAdd (@row_perm V m n s).
Canonical col_perm_additive m n s := SwizzleAdd (@col_perm V m n s).
Canonical xrow_additive m n i1 i2 := SwizzleAdd (@xrow V m n i1 i2).
Canonical xcol_additive m n j1 j2 := SwizzleAdd (@xcol V m n j1 j2).
Canonical lsubmx_additive m n1 n2 := SwizzleAdd (@lsubmx V m n1 n2).
Canonical rsubmx_additive m n1 n2 := SwizzleAdd (@rsubmx V m n1 n2).
Canonical usubmx_additive m1 m2 n := SwizzleAdd (@usubmx V m1 m2 n).
Canonical dsubmx_additive m1 m2 n := SwizzleAdd (@dsubmx V m1 m2 n).
Canonical vec_mx_additive m n := SwizzleAdd (@vec_mx V m n).
Canonical mxvec_additive m n :=
  Additive (can2_additive (@vec_mxK V m n) mxvecK).

Lemma flatmx0 n : all_equal_to (0 : 'M_(0, n)).
Proof. by move=> A; apply/matrixP=> [] []. Qed.

Lemma thinmx0 n : all_equal_to (0 : 'M_(n, 0)).
Proof. by move=> A; apply/matrixP=> i []. Qed.

Lemma trmx0 m n : (0 : 'M_(m, n))^T = 0.
Proof. exact: trmx_const. Qed.

Lemma row0 m n i0 : row i0 (0 : 'M_(m, n)) = 0.
Proof. exact: row_const. Qed.

Lemma col0 m n j0 : col j0 (0 : 'M_(m, n)) = 0.
Proof. exact: col_const. Qed.

Lemma mxvec_eq0 m n (A : 'M_(m, n)) : (mxvec A == 0) = (A == 0).
Proof. by rewrite (can2_eq mxvecK vec_mxK) raddf0. Qed.

Lemma vec_mx_eq0 m n (v : 'rV_(m * n)) : (vec_mx v == 0) = (v == 0).
Proof. by rewrite (can2_eq vec_mxK mxvecK) raddf0. Qed.

Lemma row_mx0 m n1 n2 : row_mx 0 0 = 0 :> 'M_(m, n1 + n2).
Proof. exact: row_mx_const. Qed.

Lemma col_mx0 m1 m2 n : col_mx 0 0 = 0 :> 'M_(m1 + m2, n).
Proof. exact: col_mx_const. Qed.

Lemma block_mx0 m1 m2 n1 n2 : block_mx 0 0 0 0 = 0 :> 'M_(m1 + m2, n1 + n2).
Proof. exact: block_mx_const. Qed.

Ltac split_mxE := apply/matrixP=> i j; do ![rewrite mxE | case: split => ?].

Lemma opp_row_mx m n1 n2 (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)) :
  - row_mx A1 A2 = row_mx (- A1) (- A2).
Proof. by split_mxE. Qed.

Lemma opp_col_mx m1 m2 n (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)) :
  - col_mx A1 A2 = col_mx (- A1) (- A2).
Proof. by split_mxE. Qed.

Lemma opp_block_mx m1 m2 n1 n2 (Aul : 'M_(m1, n1)) Aur Adl (Adr : 'M_(m2, n2)) :
  - block_mx Aul Aur Adl Adr = block_mx (- Aul) (- Aur) (- Adl) (- Adr).
Proof. by rewrite opp_col_mx !opp_row_mx. Qed.

Lemma add_row_mx m n1 n2 (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)) B1 B2 :
  row_mx A1 A2 + row_mx B1 B2 = row_mx (A1 + B1) (A2 + B2).
Proof. by split_mxE. Qed.

Lemma add_col_mx m1 m2 n (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)) B1 B2 :
  col_mx A1 A2 + col_mx B1 B2 = col_mx (A1 + B1) (A2 + B2).
Proof. by split_mxE. Qed.

Lemma add_block_mx m1 m2 n1 n2 (Aul : 'M_(m1, n1)) Aur Adl (Adr : 'M_(m2, n2))
                   Bul Bur Bdl Bdr :
  let A := block_mx Aul Aur Adl Adr in let B := block_mx Bul Bur Bdl Bdr in
  A + B = block_mx (Aul + Bul) (Aur + Bur) (Adl + Bdl) (Adr + Bdr).
Proof. by rewrite /= add_col_mx !add_row_mx. Qed.

Lemma row_mx_eq0 (m n1 n2 : nat) (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)):
  (row_mx A1 A2 == 0) = (A1 == 0) && (A2 == 0).
Proof.
apply/eqP/andP; last by case=> /eqP-> /eqP->; rewrite row_mx0.
by rewrite -row_mx0 => /eq_row_mx [-> ->].
Qed.

Lemma col_mx_eq0 (m1 m2 n : nat) (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)):
  (col_mx A1 A2 == 0) = (A1 == 0) && (A2 == 0).
Proof. by rewrite -![_ == 0](inj_eq trmx_inj) !trmx0 tr_col_mx row_mx_eq0. Qed.

Lemma block_mx_eq0 m1 m2 n1 n2 (Aul : 'M_(m1, n1)) Aur Adl (Adr : 'M_(m2, n2)) :
  (block_mx Aul Aur Adl Adr == 0) =
  [&& Aul == 0, Aur == 0, Adl == 0 & Adr == 0].
Proof. by rewrite col_mx_eq0 !row_mx_eq0 !andbA. Qed.

Definition nz_row m n (A : 'M_(m, n)) :=
  oapp (fun i => row i A) 0 [pick i | row i A != 0].

Lemma nz_row_eq0 m n (A : 'M_(m, n)) : (nz_row A == 0) = (A == 0).
Proof.
rewrite /nz_row; symmetry; case: pickP => [i /= nzAi | Ai0].
  by rewrite (negbTE nzAi); apply: contraTF nzAi => /eqP->; rewrite row0 eqxx.
by rewrite eqxx; apply/eqP/row_matrixP=> i; move/eqP: (Ai0 i) ->; rewrite row0.
Qed.

End MatrixZmodule.

Section FinZmodMatrix.
Variables (V : finZmodType) (m n : nat).
Local Notation MV := 'M[V]_(m, n).

Canonical matrix_finZmodType := Eval hnf in [finZmodType of MV].
Canonical matrix_baseFinGroupType :=
  Eval hnf in [baseFinGroupType of MV for +%R].
Canonical matrix_finGroupType := Eval hnf in [finGroupType of MV for +%R].
End FinZmodMatrix.

(* Parametricity over the additive structure. *)
Section MapZmodMatrix.

Variables (aR rR : zmodType) (f : {additive aR -> rR}) (m n : nat).
Local Notation "A ^f" := (map_mx f A) : ring_scope.
Implicit Type A : 'M[aR]_(m, n).

Lemma map_mx0 : 0^f = 0 :> 'M_(m, n).
Proof. by rewrite map_const_mx raddf0. Qed.

Lemma map_mxN A : (- A)^f = - A^f.
Proof. by apply/matrixP=> i j; rewrite !mxE raddfN. Qed.

Lemma map_mxD A B : (A + B)^f = A^f + B^f.
Proof. by apply/matrixP=> i j; rewrite !mxE raddfD. Qed.

Lemma map_mx_sub A B : (A - B)^f = A^f - B^f.
Proof. by rewrite map_mxD map_mxN. Qed.

Definition map_mx_sum := big_morph _ map_mxD map_mx0.

Canonical map_mx_additive := Additive map_mx_sub.

End MapZmodMatrix.

(*****************************************************************************)
(*********** Matrix ring module, graded ring, and ring structures ************)
(*****************************************************************************)

Section MatrixAlgebra.

Variable R : ringType.

Section RingModule.

(* The ring module/vector space structure *)

Variables m n : nat.
Implicit Types A B : 'M[R]_(m, n).

Fact scalemx_key : unit. Proof. by []. Qed.
Definition scalemx x A := \matrix[scalemx_key]_(i, j) (x * A i j).

(* Basis *)
Fact delta_mx_key : unit. Proof. by []. Qed.
Definition delta_mx i0 j0 : 'M[R]_(m, n) :=
  \matrix[delta_mx_key]_(i, j) ((i == i0) && (j == j0))%:R.

Local Notation "x *m: A" := (scalemx x A) (at level 40) : ring_scope.

Lemma scale1mx A : 1 *m: A = A.
Proof. by apply/matrixP=> i j; rewrite !mxE mul1r. Qed.

Lemma scalemxDl A x y : (x + y) *m: A = x *m: A + y *m: A.
Proof. by apply/matrixP=> i j; rewrite !mxE mulrDl. Qed.

Lemma scalemxDr x A B : x *m: (A + B) = x *m: A + x *m: B.
Proof. by apply/matrixP=> i j; rewrite !mxE mulrDr. Qed.

Lemma scalemxA x y A : x *m: (y *m: A) = (x * y) *m: A.
Proof. by apply/matrixP=> i j; rewrite !mxE mulrA. Qed.

Definition matrix_lmodMixin := 
  LmodMixin scalemxA scale1mx scalemxDr scalemxDl.

Canonical matrix_lmodType :=
  Eval hnf in LmodType R 'M[R]_(m, n) matrix_lmodMixin.

Lemma scalemx_const a b : a *: const_mx b = const_mx (a * b).
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma matrix_sum_delta A :
  A = \sum_(i < m) \sum_(j < n) A i j *: delta_mx i j.
Proof.
apply/matrixP=> i j.
rewrite summxE (bigD1 i) // summxE (bigD1 j) //= !mxE !eqxx mulr1.
rewrite !big1 ?addr0 //= => [i' | j']; rewrite eq_sym => /negbTE diff.
  by rewrite summxE big1 // => j' _; rewrite !mxE diff mulr0.
by rewrite !mxE eqxx diff mulr0.
Qed.

End RingModule.

Section StructuralLinear.

Lemma swizzle_mx_is_scalable m n p q f g k :
  scalable (@swizzle_mx R m n p q f g k).
Proof. by move=> a A; apply/matrixP=> i j; rewrite !mxE. Qed.
Canonical swizzle_mx_scalable m n p q f g k :=
  AddLinear (@swizzle_mx_is_scalable m n p q f g k).

Local Notation SwizzleLin op := [linear of op as swizzle_mx _ _ _].

Canonical trmx_linear m n := SwizzleLin (@trmx R m n).
Canonical row_linear m n i := SwizzleLin (@row R m n i).
Canonical col_linear m n j := SwizzleLin (@col R m n j).
Canonical row'_linear m n i := SwizzleLin (@row' R m n i).
Canonical col'_linear m n j := SwizzleLin (@col' R m n j).
Canonical row_perm_linear m n s := SwizzleLin (@row_perm R m n s).
Canonical col_perm_linear m n s := SwizzleLin (@col_perm R m n s).
Canonical xrow_linear m n i1 i2 := SwizzleLin (@xrow R m n i1 i2).
Canonical xcol_linear m n j1 j2 := SwizzleLin (@xcol R m n j1 j2).
Canonical lsubmx_linear m n1 n2 := SwizzleLin (@lsubmx R m n1 n2).
Canonical rsubmx_linear m n1 n2 := SwizzleLin (@rsubmx R m n1 n2).
Canonical usubmx_linear m1 m2 n := SwizzleLin (@usubmx R m1 m2 n).
Canonical dsubmx_linear m1 m2 n := SwizzleLin (@dsubmx R m1 m2 n).
Canonical vec_mx_linear m n := SwizzleLin (@vec_mx R m n).
Definition mxvec_is_linear m n := can2_linear (@vec_mxK R m n) mxvecK.
Canonical mxvec_linear m n := AddLinear (@mxvec_is_linear m n).

End StructuralLinear.

Lemma trmx_delta m n i j : (delta_mx i j)^T = delta_mx j i :> 'M[R]_(n, m).
Proof. by apply/matrixP=> i' j'; rewrite !mxE andbC. Qed.

Lemma row_sum_delta n (u : 'rV_n) : u = \sum_(j < n) u 0 j *: delta_mx 0 j.
Proof. by rewrite {1}[u]matrix_sum_delta big_ord1. Qed.

Lemma delta_mx_lshift m n1 n2 i j :
  delta_mx i (lshift n2 j) = row_mx (delta_mx i j) 0 :> 'M_(m, n1 + n2).
Proof.
apply/matrixP=> i' j'; rewrite !mxE -(can_eq splitK) (unsplitK (inl _ _)).
by case: split => ?; rewrite mxE ?andbF.
Qed.

Lemma delta_mx_rshift m n1 n2 i j :
  delta_mx i (rshift n1 j) = row_mx 0 (delta_mx i j) :> 'M_(m, n1 + n2).
Proof.
apply/matrixP=> i' j'; rewrite !mxE -(can_eq splitK) (unsplitK (inr _ _)).
by case: split => ?; rewrite mxE ?andbF.
Qed.

Lemma delta_mx_ushift m1 m2 n i j :
  delta_mx (lshift m2 i) j = col_mx (delta_mx i j) 0 :> 'M_(m1 + m2, n).
Proof.
apply/matrixP=> i' j'; rewrite !mxE -(can_eq splitK) (unsplitK (inl _ _)).
by  case: split => ?; rewrite mxE.
Qed.

Lemma delta_mx_dshift m1 m2 n i j :
  delta_mx (rshift m1 i) j = col_mx 0 (delta_mx i j) :> 'M_(m1 + m2, n).
Proof.
apply/matrixP=> i' j'; rewrite !mxE -(can_eq splitK) (unsplitK (inr _ _)).
by case: split => ?; rewrite mxE.
Qed.

Lemma vec_mx_delta m n i j :
  vec_mx (delta_mx 0 (mxvec_index i j)) = delta_mx i j :> 'M_(m, n).
Proof.
by apply/matrixP=> i' j'; rewrite !mxE /= [_ == _](inj_eq enum_rank_inj).
Qed.

Lemma mxvec_delta m n i j :
  mxvec (delta_mx i j) = delta_mx 0 (mxvec_index i j) :> 'rV_(m * n).
Proof. by rewrite -vec_mx_delta vec_mxK. Qed.

Ltac split_mxE := apply/matrixP=> i j; do ![rewrite mxE | case: split => ?].

Lemma scale_row_mx m n1 n2 a (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)) :
  a *: row_mx A1 A2 = row_mx (a *: A1) (a *: A2).
Proof. by split_mxE. Qed.

Lemma scale_col_mx m1 m2 n a (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)) :
  a *: col_mx A1 A2 = col_mx (a *: A1) (a *: A2).
Proof. by split_mxE. Qed.

Lemma scale_block_mx m1 m2 n1 n2 a (Aul : 'M_(m1, n1)) (Aur : 'M_(m1, n2))
                                   (Adl : 'M_(m2, n1)) (Adr : 'M_(m2, n2)) :
  a *: block_mx Aul Aur Adl Adr
     = block_mx (a *: Aul) (a *: Aur) (a *: Adl) (a *: Adr).
Proof. by rewrite scale_col_mx !scale_row_mx. Qed.

(* Diagonal matrices *)

Fact diag_mx_key : unit. Proof. by []. Qed.
Definition diag_mx n (d : 'rV[R]_n) :=
  \matrix[diag_mx_key]_(i, j) (d 0 i *+ (i == j)).

Lemma tr_diag_mx n (d : 'rV_n) : (diag_mx d)^T = diag_mx d.
Proof. by apply/matrixP=> i j; rewrite !mxE eq_sym; case: eqP => // ->. Qed.

Lemma diag_mx_is_linear n : linear (@diag_mx n).
Proof.
by move=> a A B; apply/matrixP=> i j; rewrite !mxE mulrnAr mulrnDl.
Qed.
Canonical diag_mx_additive n := Additive (@diag_mx_is_linear n).
Canonical diag_mx_linear n := Linear (@diag_mx_is_linear n).

Lemma diag_mx_sum_delta n (d : 'rV_n) :
  diag_mx d = \sum_i d 0 i *: delta_mx i i.
Proof.
apply/matrixP=> i j; rewrite summxE (bigD1 i) //= !mxE eqxx /=.
rewrite eq_sym mulr_natr big1 ?addr0 // => i' ne_i'i.
by rewrite !mxE eq_sym (negbTE ne_i'i) mulr0.
Qed.

(* Scalar matrix : a diagonal matrix with a constant on the diagonal *)
Section ScalarMx.

Variable n : nat.

Fact scalar_mx_key : unit. Proof. by []. Qed.
Definition scalar_mx x : 'M[R]_n :=
  \matrix[scalar_mx_key]_(i , j) (x *+ (i == j)).
Notation "x %:M" := (scalar_mx x) : ring_scope.

Lemma diag_const_mx a : diag_mx (const_mx a) = a%:M :> 'M_n.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma tr_scalar_mx a : (a%:M)^T = a%:M.
Proof. by apply/matrixP=> i j; rewrite !mxE eq_sym. Qed.

Lemma trmx1 : (1%:M)^T = 1%:M. Proof. exact: tr_scalar_mx. Qed.

Lemma scalar_mx_is_additive : additive scalar_mx.
Proof. by move=> a b; rewrite -!diag_const_mx !raddfB. Qed.
Canonical scalar_mx_additive := Additive scalar_mx_is_additive.

Lemma scale_scalar_mx a1 a2 : a1 *: a2%:M = (a1 * a2)%:M :> 'M_n.
Proof. by apply/matrixP=> i j; rewrite !mxE mulrnAr. Qed.

Lemma scalemx1 a : a *: 1%:M = a%:M.
Proof. by rewrite scale_scalar_mx mulr1. Qed.

Lemma scalar_mx_sum_delta a : a%:M = \sum_i a *: delta_mx i i.
Proof.
by rewrite -diag_const_mx diag_mx_sum_delta; apply: eq_bigr => i _; rewrite mxE.
Qed.

Lemma mx1_sum_delta : 1%:M = \sum_i delta_mx i i.
Proof. by rewrite [1%:M]scalar_mx_sum_delta -scaler_sumr scale1r. Qed.

Lemma row1 i : row i 1%:M = delta_mx 0 i.
Proof. by apply/rowP=> j; rewrite !mxE eq_sym. Qed.

Definition is_scalar_mx (A : 'M[R]_n) :=
  if insub 0%N is Some i then A == (A i i)%:M else true.

Lemma is_scalar_mxP A : reflect (exists a, A = a%:M) (is_scalar_mx A).
Proof.
rewrite /is_scalar_mx; case: insubP => [i _ _ | ].
  by apply: (iffP eqP) => [|[a ->]]; [exists (A i i) | rewrite mxE eqxx].
rewrite -eqn0Ngt => /eqP n0; left; exists 0.
by rewrite raddf0; rewrite n0 in A *; rewrite [A]flatmx0.
Qed.

Lemma scalar_mx_is_scalar a : is_scalar_mx a%:M.
Proof. by apply/is_scalar_mxP; exists a. Qed.

Lemma mx0_is_scalar : is_scalar_mx 0.
Proof. by apply/is_scalar_mxP; exists 0; rewrite raddf0. Qed.

End ScalarMx.

Notation "x %:M" := (scalar_mx _ x) : ring_scope.

Lemma mx11_scalar (A : 'M_1) : A = (A 0 0)%:M.
Proof. by apply/rowP=> j; rewrite ord1 mxE. Qed.

Lemma scalar_mx_block n1 n2 a : a%:M = block_mx a%:M 0 0 a%:M :> 'M_(n1 + n2).
Proof.
apply/matrixP=> i j; rewrite !mxE -val_eqE /=.
by do 2![case: splitP => ? ->; rewrite !mxE];
  rewrite ?eqn_add2l // -?(eq_sym (n1 + _)%N) eqn_leq leqNgt lshift_subproof.
Qed.

(* Matrix multiplication using bigops. *)
Fact mulmx_key : unit. Proof. by []. Qed.
Definition mulmx {m n p} (A : 'M_(m, n)) (B : 'M_(n, p)) : 'M[R]_(m, p) :=
  \matrix[mulmx_key]_(i, k) \sum_j (A i j * B j k).

Local Notation "A *m B" := (mulmx A B) : ring_scope.

Lemma mulmxA m n p q (A : 'M_(m, n)) (B : 'M_(n, p)) (C : 'M_(p, q)) :
  A *m (B *m C) = A *m B *m C.
Proof.
apply/matrixP=> i l; rewrite !mxE.
transitivity (\sum_j (\sum_k (A i j * (B j k * C k l)))).
  by apply: eq_bigr => j _; rewrite mxE big_distrr.
rewrite exchange_big; apply: eq_bigr => j _; rewrite mxE big_distrl /=.
by apply: eq_bigr => k _; rewrite mulrA.
Qed.

Lemma mul0mx m n p (A : 'M_(n, p)) : 0 *m A = 0 :> 'M_(m, p).
Proof.
by apply/matrixP=> i k; rewrite !mxE big1 //= => j _; rewrite mxE mul0r.
Qed.

Lemma mulmx0 m n p (A : 'M_(m, n)) : A *m 0 = 0 :> 'M_(m, p).
Proof.
by apply/matrixP=> i k; rewrite !mxE big1 // => j _; rewrite mxE mulr0.
Qed.

Lemma mulmxN m n p (A : 'M_(m, n)) (B : 'M_(n, p)) : A *m (- B) = - (A *m B).
Proof.
apply/matrixP=> i k; rewrite !mxE -sumrN.
by apply: eq_bigr => j _; rewrite mxE mulrN.
Qed.

Lemma mulNmx m n p (A : 'M_(m, n)) (B : 'M_(n, p)) : - A *m B = - (A *m B).
Proof.
apply/matrixP=> i k; rewrite !mxE -sumrN.
by apply: eq_bigr => j _; rewrite mxE mulNr.
Qed.

Lemma mulmxDl m n p (A1 A2 : 'M_(m, n)) (B : 'M_(n, p)) :
  (A1 + A2) *m B = A1 *m B + A2 *m B.
Proof.
apply/matrixP=> i k; rewrite !mxE -big_split /=.
by apply: eq_bigr => j _; rewrite !mxE -mulrDl.
Qed.

Lemma mulmxDr m n p (A : 'M_(m, n)) (B1 B2 : 'M_(n, p)) :
  A *m (B1 + B2) = A *m B1 + A *m B2.
Proof.
apply/matrixP=> i k; rewrite !mxE -big_split /=.
by apply: eq_bigr => j _; rewrite mxE mulrDr.
Qed.

Lemma mulmxBl m n p (A1 A2 : 'M_(m, n)) (B : 'M_(n, p)) :
  (A1 - A2) *m B = A1 *m B - A2 *m B.
Proof. by rewrite mulmxDl mulNmx. Qed.

Lemma mulmxBr m n p (A : 'M_(m, n)) (B1 B2 : 'M_(n, p)) :
  A *m (B1 - B2) = A *m B1 - A *m B2.
Proof. by rewrite mulmxDr mulmxN. Qed.

Lemma mulmx_suml m n p (A : 'M_(n, p)) I r P (B_ : I -> 'M_(m, n)) :
   (\sum_(i <- r | P i) B_ i) *m A = \sum_(i <- r | P i) B_ i *m A.
Proof.
by apply: (big_morph (mulmx^~ A)) => [B C|]; rewrite ?mul0mx ?mulmxDl.
Qed.

Lemma mulmx_sumr m n p (A : 'M_(m, n)) I r P (B_ : I -> 'M_(n, p)) :
   A *m (\sum_(i <- r | P i) B_ i) = \sum_(i <- r | P i) A *m B_ i.
Proof.
by apply: (big_morph (mulmx A)) => [B C|]; rewrite ?mulmx0 ?mulmxDr.
Qed.

Lemma scalemxAl m n p a (A : 'M_(m, n)) (B : 'M_(n, p)) :
  a *: (A *m B) = (a *: A) *m B.
Proof.
apply/matrixP=> i k; rewrite !mxE big_distrr /=.
by apply: eq_bigr => j _; rewrite mulrA mxE.
Qed.
(* Right scaling associativity requires a commutative ring *)

Lemma rowE m n i (A : 'M_(m, n)) : row i A = delta_mx 0 i *m A.
Proof.
apply/rowP=> j; rewrite !mxE (bigD1 i) //= mxE !eqxx mul1r.
by rewrite big1 ?addr0 // => i' ne_i'i; rewrite mxE /= (negbTE ne_i'i) mul0r.
Qed.

Lemma row_mul m n p (i : 'I_m) A (B : 'M_(n, p)) :
  row i (A *m B) = row i A *m B.
Proof. by rewrite !rowE mulmxA. Qed.

Lemma mulmx_sum_row m n (u : 'rV_m) (A : 'M_(m, n)) :
  u *m A = \sum_i u 0 i *: row i A.
Proof.
by apply/rowP=> j; rewrite mxE summxE; apply: eq_bigr => i _; rewrite !mxE.
Qed.

Lemma mul_delta_mx_cond m n p (j1 j2 : 'I_n) (i1 : 'I_m) (k2 : 'I_p) :
  delta_mx i1 j1 *m delta_mx j2 k2 = delta_mx i1 k2 *+ (j1 == j2).
Proof.
apply/matrixP=> i k; rewrite !mxE (bigD1 j1) //=.
rewrite mulmxnE !mxE !eqxx andbT -natrM -mulrnA !mulnb !andbA andbAC.
by rewrite big1 ?addr0 // => j; rewrite !mxE andbC -natrM; move/negbTE->.
Qed.

Lemma mul_delta_mx m n p (j : 'I_n) (i : 'I_m) (k : 'I_p) :
  delta_mx i j *m delta_mx j k = delta_mx i k.
Proof. by rewrite mul_delta_mx_cond eqxx. Qed.

Lemma mul_delta_mx_0 m n p (j1 j2 : 'I_n) (i1 : 'I_m) (k2 : 'I_p) :
  j1 != j2 -> delta_mx i1 j1 *m delta_mx j2 k2 = 0.
Proof. by rewrite mul_delta_mx_cond => /negbTE->. Qed.

Lemma mul_diag_mx m n d (A : 'M_(m, n)) :
  diag_mx d *m A = \matrix_(i, j) (d 0 i * A i j).
Proof.
apply/matrixP=> i j; rewrite !mxE (bigD1 i) //= mxE eqxx big1 ?addr0 // => i'.
by rewrite mxE eq_sym mulrnAl => /negbTE->.
Qed.

Lemma mul_mx_diag m n (A : 'M_(m, n)) d :
  A *m diag_mx d = \matrix_(i, j) (A i j * d 0 j).
Proof.
apply/matrixP=> i j; rewrite !mxE (bigD1 j) //= mxE eqxx big1 ?addr0 // => i'.
by rewrite mxE eq_sym mulrnAr; move/negbTE->.
Qed.

Lemma mulmx_diag n (d e : 'rV_n) :
  diag_mx d *m diag_mx e = diag_mx (\row_j (d 0 j * e 0 j)).
Proof. by apply/matrixP=> i j; rewrite mul_diag_mx !mxE mulrnAr. Qed.

Lemma mul_scalar_mx m n a (A : 'M_(m, n)) : a%:M *m A = a *: A.
Proof.
by rewrite -diag_const_mx mul_diag_mx; apply/matrixP=> i j; rewrite !mxE.
Qed.

Lemma scalar_mxM n a b : (a * b)%:M = a%:M *m b%:M :> 'M_n.
Proof. by rewrite mul_scalar_mx scale_scalar_mx. Qed.

Lemma mul1mx m n (A : 'M_(m, n)) : 1%:M *m A = A.
Proof. by rewrite mul_scalar_mx scale1r. Qed.

Lemma mulmx1 m n (A : 'M_(m, n)) : A *m 1%:M = A.
Proof.
rewrite -diag_const_mx mul_mx_diag.
by apply/matrixP=> i j; rewrite !mxE mulr1.
Qed.

Lemma mul_col_perm m n p s (A : 'M_(m, n)) (B : 'M_(n, p)) :
  col_perm s A *m B = A *m row_perm s^-1 B.
Proof.
apply/matrixP=> i k; rewrite !mxE (reindex_perm s^-1).
by apply: eq_bigr => j _ /=; rewrite !mxE permKV.
Qed.

Lemma mul_row_perm m n p s (A : 'M_(m, n)) (B : 'M_(n, p)) :
  A *m row_perm s B = col_perm s^-1 A *m B.
Proof. by rewrite mul_col_perm invgK. Qed.

Lemma mul_xcol m n p j1 j2 (A : 'M_(m, n)) (B : 'M_(n, p)) :
  xcol j1 j2 A *m B = A *m xrow j1 j2 B.
Proof. by rewrite mul_col_perm tpermV. Qed.

(* Permutation matrix *)

Definition perm_mx n s : 'M_n := row_perm s 1%:M.

Definition tperm_mx n i1 i2 : 'M_n := perm_mx (tperm i1 i2).

Lemma col_permE m n s (A : 'M_(m, n)) : col_perm s A = A *m perm_mx s^-1.
Proof. by rewrite mul_row_perm mulmx1 invgK. Qed.

Lemma row_permE m n s (A : 'M_(m, n)) : row_perm s A = perm_mx s *m A.
Proof.
by rewrite -[perm_mx _]mul1mx mul_row_perm mulmx1 -mul_row_perm mul1mx.
Qed.

Lemma xcolE m n j1 j2 (A : 'M_(m, n)) : xcol j1 j2 A = A *m tperm_mx j1 j2.
Proof. by rewrite /xcol col_permE tpermV. Qed.

Lemma xrowE m n i1 i2 (A : 'M_(m, n)) : xrow i1 i2 A = tperm_mx i1 i2 *m A.
Proof. exact: row_permE. Qed.

Lemma tr_perm_mx n (s : 'S_n) : (perm_mx s)^T = perm_mx s^-1.
Proof. by rewrite -[_^T]mulmx1 tr_row_perm mul_col_perm trmx1 mul1mx. Qed.

Lemma tr_tperm_mx n i1 i2 : (tperm_mx i1 i2)^T = tperm_mx i1 i2 :> 'M_n.
Proof. by rewrite tr_perm_mx tpermV. Qed.

Lemma perm_mx1 n : perm_mx 1 = 1%:M :> 'M_n.
Proof. exact: row_perm1. Qed.

Lemma perm_mxM n (s t : 'S_n) : perm_mx (s * t) = perm_mx s *m perm_mx t.
Proof. by rewrite -row_permE -row_permM. Qed.

Definition is_perm_mx n (A : 'M_n) := [exists s, A == perm_mx s].

Lemma is_perm_mxP n (A : 'M_n) :
  reflect (exists s, A = perm_mx s) (is_perm_mx A).
Proof. by apply: (iffP existsP) => [] [s /eqP]; exists s. Qed.

Lemma perm_mx_is_perm n (s : 'S_n) : is_perm_mx (perm_mx s).
Proof. by apply/is_perm_mxP; exists s. Qed.

Lemma is_perm_mx1 n : is_perm_mx (1%:M : 'M_n).
Proof. by rewrite -perm_mx1 perm_mx_is_perm. Qed.

Lemma is_perm_mxMl n (A B : 'M_n) :
  is_perm_mx A -> is_perm_mx (A *m B) = is_perm_mx B.
Proof.
case/is_perm_mxP=> s ->.
apply/is_perm_mxP/is_perm_mxP=> [[t def_t] | [t ->]]; last first.
  by exists (s * t)%g; rewrite perm_mxM.
exists (s^-1 * t)%g.
by rewrite perm_mxM -def_t -!row_permE -row_permM mulVg row_perm1.
Qed.

Lemma is_perm_mx_tr n (A : 'M_n) : is_perm_mx A^T = is_perm_mx A.
Proof.
apply/is_perm_mxP/is_perm_mxP=> [[t def_t] | [t ->]]; exists t^-1%g.
  by rewrite -tr_perm_mx -def_t trmxK.
by rewrite tr_perm_mx.
Qed.

Lemma is_perm_mxMr n (A B : 'M_n) :
  is_perm_mx B -> is_perm_mx (A *m B) = is_perm_mx A.
Proof.
case/is_perm_mxP=> s ->.
rewrite -[s]invgK -col_permE -is_perm_mx_tr tr_col_perm row_permE.
by rewrite is_perm_mxMl (perm_mx_is_perm, is_perm_mx_tr).
Qed.

(* Partial identity matrix (used in rank decomposition). *)

Fact pid_mx_key : unit. Proof. by []. Qed.
Definition pid_mx {m n} r : 'M[R]_(m, n) :=
  \matrix[pid_mx_key]_(i, j) ((i == j :> nat) && (i < r))%:R.

Lemma pid_mx_0 m n : pid_mx 0 = 0 :> 'M_(m, n).
Proof. by apply/matrixP=> i j; rewrite !mxE andbF. Qed.

Lemma pid_mx_1 r : pid_mx r = 1%:M :> 'M_r.
Proof. by apply/matrixP=> i j; rewrite !mxE ltn_ord andbT. Qed.

Lemma pid_mx_row n r : pid_mx r = row_mx 1%:M 0 :> 'M_(r, r + n).
Proof.
apply/matrixP=> i j; rewrite !mxE ltn_ord andbT.
case: splitP => j' ->; rewrite !mxE // .
by rewrite eqn_leq andbC leqNgt lshift_subproof.
Qed.

Lemma pid_mx_col m r : pid_mx r = col_mx 1%:M 0 :> 'M_(r + m, r).
Proof.
apply/matrixP=> i j; rewrite !mxE andbC.
by case: splitP => i' ->; rewrite !mxE // eq_sym.
Qed.

Lemma pid_mx_block m n r : pid_mx r = block_mx 1%:M 0 0 0 :> 'M_(r + m, r + n).
Proof.
apply/matrixP=> i j; rewrite !mxE row_mx0 andbC.
case: splitP => i' ->; rewrite !mxE //; case: splitP => j' ->; rewrite !mxE //=.
by rewrite eqn_leq andbC leqNgt lshift_subproof.
Qed.

Lemma tr_pid_mx m n r : (pid_mx r)^T = pid_mx r :> 'M_(n, m).
Proof. by apply/matrixP=> i j; rewrite !mxE eq_sym; case: eqP => // ->. Qed.

Lemma pid_mx_minv m n r : pid_mx (minn m r) = pid_mx r :> 'M_(m, n).
Proof. by apply/matrixP=> i j; rewrite !mxE leq_min ltn_ord. Qed.
 
Lemma pid_mx_minh m n r : pid_mx (minn n r) = pid_mx r :> 'M_(m, n).
Proof. by apply: trmx_inj; rewrite !tr_pid_mx pid_mx_minv. Qed.

Lemma mul_pid_mx m n p q r :
  (pid_mx q : 'M_(m, n)) *m (pid_mx r : 'M_(n, p)) = pid_mx (minn n (minn q r)).
Proof.
apply/matrixP=> i k; rewrite !mxE !leq_min.
have [le_n_i | lt_i_n] := leqP n i.
  rewrite andbF big1 // => j _.
  by rewrite -pid_mx_minh !mxE leq_min ltnNge le_n_i andbF mul0r.
rewrite (bigD1 (Ordinal lt_i_n)) //= big1 ?addr0 => [|j].
  by rewrite !mxE eqxx /= -natrM mulnb andbCA.
by rewrite -val_eqE /= !mxE eq_sym -natrM => /negbTE->.
Qed.

Lemma pid_mx_id m n p r :
  r <= n -> (pid_mx r : 'M_(m, n)) *m (pid_mx r : 'M_(n, p)) = pid_mx r.
Proof. by move=> le_r_n; rewrite mul_pid_mx minnn (minn_idPr _). Qed.

Definition copid_mx {n} r : 'M_n := 1%:M - pid_mx r.

Lemma mul_copid_mx_pid m n r :
  r <= m -> copid_mx r *m pid_mx r = 0 :> 'M_(m, n).
Proof. by move=> le_r_m; rewrite mulmxBl mul1mx pid_mx_id ?subrr. Qed.

Lemma mul_pid_mx_copid m n r :
  r <= n -> pid_mx r *m copid_mx r = 0 :> 'M_(m, n).
Proof. by move=> le_r_n; rewrite mulmxBr mulmx1 pid_mx_id ?subrr. Qed.

Lemma copid_mx_id n r :
  r <= n -> copid_mx r *m copid_mx r = copid_mx r :> 'M_n.
Proof.
by move=> le_r_n; rewrite mulmxBl mul1mx mul_pid_mx_copid // oppr0 addr0.
Qed.

(* Block products; we cover all 1 x 2, 2 x 1, and 2 x 2 block products. *)
Lemma mul_mx_row m n p1 p2 (A : 'M_(m, n)) (Bl : 'M_(n, p1)) (Br : 'M_(n, p2)) :
  A *m row_mx Bl Br = row_mx (A *m Bl) (A *m Br).
Proof.
apply/matrixP=> i k; rewrite !mxE.
by case defk: (split k); rewrite mxE; apply: eq_bigr => j _; rewrite mxE defk.
Qed.

Lemma mul_col_mx m1 m2 n p (Au : 'M_(m1, n)) (Ad : 'M_(m2, n)) (B : 'M_(n, p)) :
  col_mx Au Ad *m B = col_mx (Au *m B) (Ad *m B).
Proof.
apply/matrixP=> i k; rewrite !mxE.
by case defi: (split i); rewrite mxE; apply: eq_bigr => j _; rewrite mxE defi.
Qed.

Lemma mul_row_col m n1 n2 p (Al : 'M_(m, n1)) (Ar : 'M_(m, n2))
                            (Bu : 'M_(n1, p)) (Bd : 'M_(n2, p)) :
  row_mx Al Ar *m col_mx Bu Bd = Al *m Bu + Ar *m Bd.
Proof.
apply/matrixP=> i k; rewrite !mxE big_split_ord /=.
congr (_ + _); apply: eq_bigr => j _; first by rewrite row_mxEl col_mxEu.
by rewrite row_mxEr col_mxEd.
Qed.

Lemma mul_col_row m1 m2 n p1 p2 (Au : 'M_(m1, n)) (Ad : 'M_(m2, n))
                                (Bl : 'M_(n, p1)) (Br : 'M_(n, p2)) :
  col_mx Au Ad *m row_mx Bl Br
     = block_mx (Au *m Bl) (Au *m Br) (Ad *m Bl) (Ad *m Br).
Proof. by rewrite mul_col_mx !mul_mx_row. Qed.

Lemma mul_row_block m n1 n2 p1 p2 (Al : 'M_(m, n1)) (Ar : 'M_(m, n2))
                                  (Bul : 'M_(n1, p1)) (Bur : 'M_(n1, p2))
                                  (Bdl : 'M_(n2, p1)) (Bdr : 'M_(n2, p2)) :
  row_mx Al Ar *m block_mx Bul Bur Bdl Bdr
   = row_mx (Al *m Bul + Ar *m Bdl) (Al *m Bur + Ar *m Bdr).
Proof. by rewrite block_mxEh mul_mx_row !mul_row_col. Qed.

Lemma mul_block_col m1 m2 n1 n2 p (Aul : 'M_(m1, n1)) (Aur : 'M_(m1, n2))
                                  (Adl : 'M_(m2, n1)) (Adr : 'M_(m2, n2))
                                  (Bu : 'M_(n1, p)) (Bd : 'M_(n2, p)) :
  block_mx Aul Aur Adl Adr *m col_mx Bu Bd
   = col_mx (Aul *m Bu + Aur *m Bd) (Adl *m Bu + Adr *m Bd).
Proof. by rewrite mul_col_mx !mul_row_col. Qed.

Lemma mulmx_block m1 m2 n1 n2 p1 p2 (Aul : 'M_(m1, n1)) (Aur : 'M_(m1, n2))
                                    (Adl : 'M_(m2, n1)) (Adr : 'M_(m2, n2))
                                    (Bul : 'M_(n1, p1)) (Bur : 'M_(n1, p2))
                                    (Bdl : 'M_(n2, p1)) (Bdr : 'M_(n2, p2)) :
  block_mx Aul Aur Adl Adr *m block_mx Bul Bur Bdl Bdr
    = block_mx (Aul *m Bul + Aur *m Bdl) (Aul *m Bur + Aur *m Bdr)
               (Adl *m Bul + Adr *m Bdl) (Adl *m Bur + Adr *m Bdr).
Proof. by rewrite mul_col_mx !mul_row_block. Qed.

(* Correspondance between matrices and linear function on row vectors. *) 
Section LinRowVector.

Variables m n : nat.

Fact lin1_mx_key : unit. Proof. by []. Qed.
Definition lin1_mx (f : 'rV[R]_m -> 'rV[R]_n) :=
  \matrix[lin1_mx_key]_(i, j) f (delta_mx 0 i) 0 j.

Variable f : {linear 'rV[R]_m -> 'rV[R]_n}.

Lemma mul_rV_lin1 u : u *m lin1_mx f = f u.
Proof.
rewrite {2}[u]matrix_sum_delta big_ord1 linear_sum; apply/rowP=> i.
by rewrite mxE summxE; apply: eq_bigr => j _; rewrite linearZ !mxE.
Qed.

End LinRowVector.

(* Correspondance between matrices and linear function on matrices. *) 
Section LinMatrix.

Variables m1 n1 m2 n2 : nat.

Definition lin_mx (f : 'M[R]_(m1, n1) -> 'M[R]_(m2, n2)) :=
  lin1_mx (mxvec \o f \o vec_mx).

Variable f : {linear 'M[R]_(m1, n1) -> 'M[R]_(m2, n2)}.

Lemma mul_rV_lin u : u *m lin_mx f = mxvec (f (vec_mx u)).
Proof. exact: mul_rV_lin1. Qed.

Lemma mul_vec_lin A : mxvec A *m lin_mx f = mxvec (f A).
Proof. by rewrite mul_rV_lin mxvecK. Qed.

Lemma mx_rV_lin u : vec_mx (u *m lin_mx f) = f (vec_mx u).
Proof. by rewrite mul_rV_lin mxvecK. Qed.

Lemma mx_vec_lin A : vec_mx (mxvec A *m lin_mx f) = f A.
Proof. by rewrite mul_rV_lin !mxvecK. Qed.

End LinMatrix.

Canonical mulmx_additive m n p A := Additive (@mulmxBr m n p A).

Section Mulmxr.

Variables m n p : nat.
Implicit Type A : 'M[R]_(m, n).
Implicit Type B : 'M[R]_(n, p).

Definition mulmxr_head t B A := let: tt := t in A *m B.
Local Notation mulmxr := (mulmxr_head tt).

Definition lin_mulmxr B := lin_mx (mulmxr B).

Lemma mulmxr_is_linear B : linear (mulmxr B).
Proof. by move=> a A1 A2; rewrite /= mulmxDl scalemxAl. Qed.
Canonical mulmxr_additive B := Additive (mulmxr_is_linear B).
Canonical mulmxr_linear B := Linear (mulmxr_is_linear B).

Lemma lin_mulmxr_is_linear : linear lin_mulmxr.
Proof.
move=> a A B; apply/row_matrixP; case/mxvec_indexP=> i j.
rewrite linearP /= !rowE !mul_rV_lin /= vec_mx_delta -linearP mulmxDr.
congr (mxvec (_ + _)); apply/row_matrixP=> k.
rewrite linearZ /= !row_mul rowE mul_delta_mx_cond.
by case: (k == i); [rewrite -!rowE linearZ | rewrite !mul0mx raddf0].
Qed.
Canonical lin_mulmxr_additive := Additive lin_mulmxr_is_linear.
Canonical lin_mulmxr_linear := Linear lin_mulmxr_is_linear.

End Mulmxr.

(* The trace. *)
Section Trace.

Variable n : nat.

Definition mxtrace (A : 'M[R]_n) := \sum_i A i i.
Local Notation "'\tr' A" := (mxtrace A) : ring_scope.

Lemma mxtrace_tr A : \tr A^T = \tr A.
Proof. by apply: eq_bigr=> i _; rewrite mxE. Qed.

Lemma mxtrace_is_scalar : scalar mxtrace.
Proof.
move=> a A B; rewrite mulr_sumr -big_split /=; apply: eq_bigr=> i _.
by rewrite !mxE.
Qed.
Canonical mxtrace_additive := Additive mxtrace_is_scalar.
Canonical mxtrace_linear := Linear mxtrace_is_scalar.

Lemma mxtrace0 : \tr 0 = 0. Proof. exact: raddf0. Qed.
Lemma mxtraceD A B : \tr (A + B) = \tr A + \tr B. Proof. exact: raddfD. Qed.
Lemma mxtraceZ a A : \tr (a *: A) = a * \tr A. Proof. exact: scalarZ. Qed.

Lemma mxtrace_diag D : \tr (diag_mx D) = \sum_j D 0 j.
Proof. by apply: eq_bigr => j _; rewrite mxE eqxx. Qed.

Lemma mxtrace_scalar a : \tr a%:M = a *+ n.
Proof.
rewrite -diag_const_mx mxtrace_diag.
by rewrite (eq_bigr _ (fun j _ => mxE _ _ 0 j)) sumr_const card_ord.
Qed.

Lemma mxtrace1 : \tr 1%:M = n%:R. Proof. exact: mxtrace_scalar. Qed.

End Trace.
Local Notation "'\tr' A" := (mxtrace A) : ring_scope.

Lemma trace_mx11 (A : 'M_1) : \tr A = A 0 0.
Proof. by rewrite {1}[A]mx11_scalar mxtrace_scalar. Qed.

Lemma mxtrace_block n1 n2 (Aul : 'M_n1) Aur Adl (Adr : 'M_n2) :
  \tr (block_mx Aul Aur Adl Adr) = \tr Aul + \tr Adr.
Proof.
rewrite /(\tr _) big_split_ord /=.
by congr (_ + _); apply: eq_bigr => i _; rewrite (block_mxEul, block_mxEdr).
Qed.

(* The matrix ring structure requires a strutural condition (dimension of the *)
(* form n.+1) to statisfy the nontriviality condition we have imposed.        *)
Section MatrixRing.

Variable n' : nat.
Local Notation n := n'.+1.

Lemma matrix_nonzero1 : 1%:M != 0 :> 'M_n.
Proof. by apply/eqP=> /matrixP/(_ 0 0)/eqP; rewrite !mxE oner_eq0. Qed.

Definition matrix_ringMixin :=
  RingMixin (@mulmxA n n n n) (@mul1mx n n) (@mulmx1 n n)
            (@mulmxDl n n n) (@mulmxDr n n n) matrix_nonzero1.

Canonical matrix_ringType := Eval hnf in RingType 'M[R]_n matrix_ringMixin.
Canonical matrix_lAlgType := Eval hnf in LalgType R 'M[R]_n (@scalemxAl n n n).

Lemma mulmxE : mulmx = *%R. Proof. by []. Qed.
Lemma idmxE : 1%:M = 1 :> 'M_n. Proof. by []. Qed.

Lemma scalar_mx_is_multiplicative : multiplicative (@scalar_mx n).
Proof. by split=> //; apply: scalar_mxM. Qed.
Canonical scalar_mx_rmorphism := AddRMorphism scalar_mx_is_multiplicative.

End MatrixRing.

Section LiftPerm.

(* Block expresssion of a lifted permutation matrix, for the Cormen LUP. *)

Variable n : nat.

(* These could be in zmodp, but that would introduce a dependency on perm. *)

Definition lift0_perm s : 'S_n.+1 := lift_perm 0 0 s.

Lemma lift0_perm0 s : lift0_perm s 0 = 0.
Proof. exact: lift_perm_id. Qed.

Lemma lift0_perm_lift s k' :
  lift0_perm s (lift 0 k') = lift (0 : 'I_n.+1) (s k').
Proof. exact: lift_perm_lift. Qed.

Lemma lift0_permK s : cancel (lift0_perm s) (lift0_perm s^-1).
Proof. by move=> i; rewrite /lift0_perm -lift_permV permK. Qed.

Lemma lift0_perm_eq0 s i : (lift0_perm s i == 0) = (i == 0).
Proof. by rewrite (canF_eq (lift0_permK s)) lift0_perm0. Qed.

(* Block expresssion of a lifted permutation matrix *)

Definition lift0_mx A : 'M_(1 + n) := block_mx 1 0 0 A.

Lemma lift0_mx_perm s : lift0_mx (perm_mx s) = perm_mx (lift0_perm s).
Proof.
apply/matrixP=> /= i j; rewrite !mxE split1 /=; case: unliftP => [i'|] -> /=.
  rewrite lift0_perm_lift !mxE split1 /=.
  by case: unliftP => [j'|] ->; rewrite ?(inj_eq (lift_inj _)) /= !mxE.
rewrite lift0_perm0 !mxE split1 /=.
by case: unliftP => [j'|] ->; rewrite /= mxE.
Qed.

Lemma lift0_mx_is_perm s : is_perm_mx (lift0_mx (perm_mx s)).
Proof. by rewrite lift0_mx_perm perm_mx_is_perm. Qed.

End LiftPerm.

(* Determinants and adjugates are defined here, but most of their properties *)
(* only hold for matrices over a commutative ring, so their theory is        *)
(* deferred to that section.                                                 *)

(* The determinant, in one line with the Leibniz Formula *)
Definition determinant n (A : 'M_n) : R :=
  \sum_(s : 'S_n) (-1) ^+ s * \prod_i A i (s i).

(* The cofactor of a matrix on the indexes i and j *)
Definition cofactor n A (i j : 'I_n) : R :=
  (-1) ^+ (i + j) * determinant (row' i (col' j A)).

(* The adjugate matrix : defined as the transpose of the matrix of cofactors *)
Fact adjugate_key : unit. Proof. by []. Qed.
Definition adjugate n (A : 'M_n) := \matrix[adjugate_key]_(i, j) cofactor A j i.

End MatrixAlgebra.

Arguments delta_mx {R m n}.
Arguments scalar_mx {R n}.
Arguments perm_mx {R n}.
Arguments tperm_mx {R n}.
Arguments pid_mx {R m n}.
Arguments copid_mx {R n}.
Arguments lin_mulmxr {R m n p}.
Prenex Implicits diag_mx is_scalar_mx.
Prenex Implicits mulmx mxtrace determinant cofactor adjugate.

Arguments is_scalar_mxP {R n A}.
Arguments mul_delta_mx {R m n p}.

Notation "a %:M" := (scalar_mx a) : ring_scope.
Notation "A *m B" := (mulmx A B) : ring_scope.
Notation mulmxr := (mulmxr_head tt).
Notation "\tr A" := (mxtrace A) : ring_scope.
Notation "'\det' A" := (determinant A) : ring_scope.
Notation "'\adj' A" := (adjugate A) : ring_scope.

(* Non-commutative transpose requires multiplication in the converse ring.   *)
Lemma trmx_mul_rev (R : ringType) m n p (A : 'M[R]_(m, n)) (B : 'M[R]_(n, p)) :
  (A *m B)^T = (B : 'M[R^c]_(n, p))^T *m (A : 'M[R^c]_(m, n))^T.
Proof.
by apply/matrixP=> k i; rewrite !mxE; apply: eq_bigr => j _; rewrite !mxE.
Qed.

Canonical matrix_countZmodType (M : countZmodType) m n :=
  [countZmodType of 'M[M]_(m, n)].
Canonical matrix_countRingType (R : countRingType) n :=
  [countRingType of 'M[R]_n.+1].
Canonical matrix_finLmodType (R : finRingType) m n :=
  [finLmodType R of 'M[R]_(m, n)].
Canonical matrix_finRingType (R : finRingType) n' :=
  Eval hnf in [finRingType of 'M[R]_n'.+1].
Canonical matrix_finLalgType (R : finRingType) n' :=
  [finLalgType R of 'M[R]_n'.+1].

(* Parametricity over the algebra structure. *)
Section MapRingMatrix.

Variables (aR rR : ringType) (f : {rmorphism aR -> rR}).
Local Notation "A ^f" := (map_mx f A) : ring_scope.

Section FixedSize.

Variables m n p : nat.
Implicit Type A : 'M[aR]_(m, n).

Lemma map_mxZ a A : (a *: A)^f = f a *: A^f.
Proof. by apply/matrixP=> i j; rewrite !mxE rmorphM. Qed.

Lemma map_mxM A B : (A *m B)^f = A^f *m B^f :> 'M_(m, p).
Proof.
apply/matrixP=> i k; rewrite !mxE rmorph_sum //.
by apply: eq_bigr => j; rewrite !mxE rmorphM.
Qed.

Lemma map_delta_mx i j : (delta_mx i j)^f = delta_mx i j :> 'M_(m, n).
Proof. by apply/matrixP=> i' j'; rewrite !mxE rmorph_nat. Qed.

Lemma map_diag_mx d : (diag_mx d)^f = diag_mx d^f :> 'M_n.
Proof. by apply/matrixP=> i j; rewrite !mxE rmorphMn. Qed.

Lemma map_scalar_mx a : a%:M^f = (f a)%:M :> 'M_n.
Proof. by apply/matrixP=> i j; rewrite !mxE rmorphMn. Qed.

Lemma map_mx1 : 1%:M^f = 1%:M :> 'M_n.
Proof. by rewrite map_scalar_mx rmorph1. Qed.

Lemma map_perm_mx (s : 'S_n) : (perm_mx s)^f = perm_mx s.
Proof. by apply/matrixP=> i j; rewrite !mxE rmorph_nat. Qed.

Lemma map_tperm_mx (i1 i2 : 'I_n) : (tperm_mx i1 i2)^f = tperm_mx i1 i2.
Proof. exact: map_perm_mx. Qed.

Lemma map_pid_mx r : (pid_mx r)^f = pid_mx r :> 'M_(m, n).
Proof. by apply/matrixP=> i j; rewrite !mxE rmorph_nat. Qed.

Lemma trace_map_mx (A : 'M_n) : \tr A^f = f (\tr A).
Proof. by rewrite rmorph_sum; apply: eq_bigr => i _; rewrite mxE. Qed.

Lemma det_map_mx n' (A : 'M_n') : \det A^f = f (\det A).
Proof.
rewrite rmorph_sum //; apply: eq_bigr => s _.
rewrite rmorphM rmorph_sign rmorph_prod; congr (_ * _).
by apply: eq_bigr => i _; rewrite mxE.
Qed.

Lemma cofactor_map_mx (A : 'M_n) i j : cofactor A^f i j = f (cofactor A i j).
Proof. by rewrite rmorphM rmorph_sign -det_map_mx map_row' map_col'. Qed.

Lemma map_mx_adj (A : 'M_n) : (\adj A)^f = \adj A^f.
Proof. by apply/matrixP=> i j; rewrite !mxE cofactor_map_mx. Qed.

End FixedSize.

Lemma map_copid_mx n r : (copid_mx r)^f = copid_mx r :> 'M_n.
Proof. by rewrite map_mx_sub map_mx1 map_pid_mx. Qed.

Lemma map_mx_is_multiplicative n' (n := n'.+1) :
  multiplicative (map_mx f : 'M_n -> 'M_n).
Proof. by split; [apply: map_mxM | apply: map_mx1]. Qed.

Canonical map_mx_rmorphism n' := AddRMorphism (map_mx_is_multiplicative n').

Lemma map_lin1_mx m n (g : 'rV_m -> 'rV_n) gf :
  (forall v, (g v)^f = gf v^f) -> (lin1_mx g)^f = lin1_mx gf.
Proof.
by move=> def_gf; apply/matrixP=> i j; rewrite !mxE -map_delta_mx -def_gf mxE.
Qed.

Lemma map_lin_mx m1 n1 m2 n2 (g : 'M_(m1, n1) -> 'M_(m2, n2)) gf : 
  (forall A, (g A)^f = gf A^f) -> (lin_mx g)^f = lin_mx gf.
Proof.
move=> def_gf; apply: map_lin1_mx => A /=.
by rewrite map_mxvec def_gf map_vec_mx.
Qed.

End MapRingMatrix.

Section ComMatrix.
(* Lemmas for matrices with coefficients in a commutative ring *)
Variable R : comRingType.

Section AssocLeft.

Variables m n p : nat.
Implicit Type A : 'M[R]_(m, n).
Implicit Type B : 'M[R]_(n, p).

Lemma trmx_mul A B : (A *m B)^T = B^T *m A^T.
Proof.
rewrite trmx_mul_rev; apply/matrixP=> k i; rewrite !mxE.
by apply: eq_bigr => j _; rewrite mulrC.
Qed.

Lemma scalemxAr a A B : a *: (A *m B) = A *m (a *: B).
Proof. by apply: trmx_inj; rewrite trmx_mul !linearZ /= trmx_mul scalemxAl. Qed.

Lemma mulmx_is_scalable A : scalable (@mulmx _ m n p A).
Proof. by move=> a B; rewrite scalemxAr. Qed.
Canonical mulmx_linear A := AddLinear (mulmx_is_scalable A).

Definition lin_mulmx A : 'M[R]_(n * p, m * p) := lin_mx (mulmx A).

Lemma lin_mulmx_is_linear : linear lin_mulmx.
Proof.
move=> a A B; apply/row_matrixP=> i; rewrite linearP /= !rowE !mul_rV_lin /=.
by rewrite [_ *m _](linearP (mulmxr_linear _ _)) linearP.
Qed.
Canonical lin_mulmx_additive := Additive lin_mulmx_is_linear.
Canonical lin_mulmx_linear := Linear lin_mulmx_is_linear.

End AssocLeft.

Section LinMulRow.

Variables m n : nat.

Definition lin_mul_row u : 'M[R]_(m * n, n) := lin1_mx (mulmx u \o vec_mx).

Lemma lin_mul_row_is_linear : linear lin_mul_row.
Proof.
move=> a u v; apply/row_matrixP=> i; rewrite linearP /= !rowE !mul_rV_lin1 /=.
by rewrite [_ *m _](linearP (mulmxr_linear _ _)).
Qed.
Canonical lin_mul_row_additive := Additive lin_mul_row_is_linear.
Canonical lin_mul_row_linear := Linear lin_mul_row_is_linear.

Lemma mul_vec_lin_row A u : mxvec A *m lin_mul_row u = u *m A.
Proof. by rewrite mul_rV_lin1 /= mxvecK. Qed.

End LinMulRow.

Lemma mxvec_dotmul m n (A : 'M[R]_(m, n)) u v :
  mxvec (u^T *m v) *m (mxvec A)^T = u *m A *m v^T.
Proof.
transitivity (\sum_i \sum_j (u 0 i * A i j *: row j v^T)).
  apply/rowP=> i; rewrite {i}ord1 mxE (reindex _ (curry_mxvec_bij _ _)) /=.
  rewrite pair_bigA summxE; apply: eq_bigr => [[i j]] /= _.
  by rewrite !mxE !mxvecE mxE big_ord1 mxE mulrAC.
rewrite mulmx_sum_row exchange_big; apply: eq_bigr => j _ /=.
by rewrite mxE -scaler_suml.
Qed.

Section MatrixAlgType.

Variable n' : nat.
Local Notation n := n'.+1.

Canonical matrix_algType :=
  Eval hnf in AlgType R 'M[R]_n (fun k => scalemxAr k).

End MatrixAlgType.

Lemma diag_mxC n (d e : 'rV[R]_n) :
  diag_mx d *m diag_mx e = diag_mx e *m diag_mx d.
Proof.
by rewrite !mulmx_diag; congr (diag_mx _); apply/rowP=> i; rewrite !mxE mulrC.
Qed.

Lemma diag_mx_comm n' (d e : 'rV[R]_n'.+1) : GRing.comm (diag_mx d) (diag_mx e).
Proof. exact: diag_mxC. Qed.

Lemma scalar_mxC m n a (A : 'M[R]_(m, n)) : A *m a%:M = a%:M *m A.
Proof.
by apply: trmx_inj; rewrite trmx_mul tr_scalar_mx !mul_scalar_mx linearZ.
Qed.

Lemma scalar_mx_comm n' a (A : 'M[R]_n'.+1) : GRing.comm A a%:M.
Proof. exact: scalar_mxC. Qed.

Lemma mul_mx_scalar m n a (A : 'M[R]_(m, n)) : A *m a%:M = a *: A.
Proof. by rewrite scalar_mxC mul_scalar_mx. Qed.

Lemma mxtrace_mulC m n (A : 'M[R]_(m, n)) B :
   \tr (A *m B) = \tr (B *m A).
Proof.
have expand_trM C D: \tr (C *m D) = \sum_i \sum_j C i j * D j i.
  by apply: eq_bigr => i _; rewrite mxE.
rewrite !{}expand_trM exchange_big /=.
by do 2!apply: eq_bigr => ? _; apply: mulrC.
Qed.

(* The theory of determinants *)

Lemma determinant_multilinear n (A B C : 'M[R]_n) i0 b c :
    row i0 A = b *: row i0 B + c *: row i0 C ->
    row' i0 B = row' i0 A ->
    row' i0 C = row' i0 A ->
  \det A = b * \det B + c * \det C.
Proof.
rewrite -[_ + _](row_id 0); move/row_eq=> ABC.
move/row'_eq=> BA; move/row'_eq=> CA.
rewrite !big_distrr -big_split; apply: eq_bigr => s _ /=.
rewrite -!(mulrCA (_ ^+s)) -mulrDr; congr (_ * _).
rewrite !(bigD1 i0 (_ : predT i0)) //= {}ABC !mxE mulrDl !mulrA.
by congr (_ * _ + _ * _); apply: eq_bigr => i i0i; rewrite ?BA ?CA.
Qed.

Lemma determinant_alternate n (A : 'M[R]_n) i1 i2 :
  i1 != i2 -> A i1 =1 A i2 -> \det A = 0.
Proof.
move=> neq_i12 eqA12; pose t := tperm i1 i2.
have oddMt s: (t * s)%g = ~~ s :> bool by rewrite odd_permM odd_tperm neq_i12.
rewrite [\det A](bigID (@odd_perm _)) /=.
apply: canLR (subrK _) _; rewrite add0r -sumrN.
rewrite (reindex_inj (mulgI t)); apply: eq_big => //= s.
rewrite oddMt => /negPf->; rewrite mulN1r mul1r; congr (- _).
rewrite (reindex_perm t); apply: eq_bigr => /= i _.
by rewrite permM tpermK /t; case: tpermP => // ->; rewrite eqA12.
Qed.

Lemma det_tr n (A : 'M[R]_n) : \det A^T = \det A.
Proof.
rewrite [\det A^T](reindex_inj invg_inj) /=.
apply: eq_bigr => s _ /=; rewrite !odd_permV (reindex_perm s) /=.
by congr (_ * _); apply: eq_bigr => i _; rewrite mxE permK.
Qed.

Lemma det_perm n (s : 'S_n) : \det (perm_mx s) = (-1) ^+ s :> R.
Proof.
rewrite [\det _](bigD1 s) //= big1 => [|i _]; last by rewrite /= !mxE eqxx.
rewrite mulr1 big1 ?addr0 => //= t Dst.
case: (pickP (fun i => s i != t i)) => [i ist | Est].
  by rewrite (bigD1 i) // mulrCA /= !mxE (negbTE ist) mul0r.
by case/eqP: Dst; apply/permP => i; move/eqP: (Est i).
Qed.

Lemma det1 n : \det (1%:M : 'M[R]_n) = 1.
Proof. by rewrite -perm_mx1 det_perm odd_perm1. Qed.

Lemma det_mx00 (A : 'M[R]_0) : \det A = 1.
Proof. by rewrite flatmx0 -(flatmx0 1%:M) det1. Qed.

Lemma detZ n a (A : 'M[R]_n) : \det (a *: A) = a ^+ n * \det A.
Proof.
rewrite big_distrr /=; apply: eq_bigr => s _; rewrite mulrCA; congr (_ * _).
rewrite -[n in a ^+ n]card_ord -prodr_const -big_split /=.
by apply: eq_bigr=> i _; rewrite mxE.
Qed.

Lemma det0 n' : \det (0 : 'M[R]_n'.+1) = 0.
Proof. by rewrite -(scale0r 0) detZ exprS !mul0r. Qed.

Lemma det_scalar n a : \det (a%:M : 'M[R]_n) = a ^+ n.
Proof. by rewrite -{1}(mulr1 a) -scale_scalar_mx detZ det1 mulr1. Qed.

Lemma det_scalar1 a : \det (a%:M : 'M[R]_1) = a.
Proof. exact: det_scalar. Qed.

Lemma det_mulmx n (A B : 'M[R]_n) : \det (A *m B) = \det A * \det B.
Proof.
rewrite big_distrl /=.
pose F := ('I_n ^ n)%type; pose AB s i j := A i j * B j (s i).
transitivity (\sum_(f : F) \sum_(s : 'S_n) (-1) ^+ s * \prod_i AB s i (f i)).
  rewrite exchange_big; apply: eq_bigr => /= s _; rewrite -big_distrr /=.
  congr (_ * _); rewrite -(bigA_distr_bigA (AB s)) /=.
  by apply: eq_bigr => x _; rewrite mxE.
rewrite (bigID (fun f : F => injectiveb f)) /= addrC big1 ?add0r => [|f Uf].
  rewrite (reindex (@pval _)) /=; last first.
    pose in_Sn := insubd (1%g : 'S_n).
    by exists in_Sn => /= f Uf; first apply: val_inj; apply: insubdK.
  apply: eq_big => /= [s | s _]; rewrite ?(valP s) // big_distrr /=.
  rewrite (reindex_inj (mulgI s)); apply: eq_bigr => t _ /=.
  rewrite big_split /= mulrA mulrCA mulrA mulrCA mulrA.
  rewrite -signr_addb odd_permM !pvalE; congr (_ * _); symmetry.
  by rewrite (reindex_perm s); apply: eq_bigr => i; rewrite permM.
transitivity (\det (\matrix_(i, j) B (f i) j) * \prod_i A i (f i)).
  rewrite mulrC big_distrr /=; apply: eq_bigr => s _.
  rewrite mulrCA big_split //=; congr (_ * (_ * _)).
  by apply: eq_bigr => x _; rewrite mxE.
case/injectivePn: Uf => i1 [i2 Di12 Ef12].
by rewrite (determinant_alternate Di12) ?simp //= => j; rewrite !mxE Ef12.
Qed.

Lemma detM n' (A B : 'M[R]_n'.+1) : \det (A * B) = \det A * \det B.
Proof. exact: det_mulmx. Qed.

Lemma det_diag n (d : 'rV[R]_n) : \det (diag_mx d) = \prod_i d 0 i.
Proof.
rewrite /(\det _) (bigD1 1%g) //= addrC big1 => [|p p1].
  by rewrite add0r odd_perm1 mul1r; apply: eq_bigr => i; rewrite perm1 mxE eqxx.
have{p1}: ~~ perm_on set0 p.
  apply: contra p1; move/subsetP=> p1; apply/eqP; apply/permP=> i.
  by rewrite perm1; apply/eqP; apply/idPn; move/p1; rewrite inE.
case/subsetPn=> i; rewrite !inE eq_sym; move/negbTE=> p_i _.
by rewrite (bigD1 i) //= mulrCA mxE p_i mul0r.
Qed.

(* Laplace expansion lemma *)
Lemma expand_cofactor n (A : 'M[R]_n) i j :
  cofactor A i j =
    \sum_(s : 'S_n | s i == j) (-1) ^+ s * \prod_(k | i != k) A k (s k).
Proof.
case: n A i j => [|n] A i0 j0; first by case: i0.
rewrite (reindex (lift_perm i0 j0)); last first.
  pose ulsf i (s : 'S_n.+1) k := odflt k (unlift (s i) (s (lift i k))).
  have ulsfK i (s : 'S_n.+1) k: lift (s i) (ulsf i s k) = s (lift i k).
    rewrite /ulsf; have:= neq_lift i k.
    by rewrite -(can_eq (permK s)) => /unlift_some[] ? ? ->.
  have inj_ulsf: injective (ulsf i0 _).
    move=> s; apply: can_inj (ulsf (s i0) s^-1%g) _ => k'.
    by rewrite {1}/ulsf ulsfK !permK liftK.
  exists (fun s => perm (inj_ulsf s)) => [s _ | s].
    by apply/permP=> k'; rewrite permE /ulsf lift_perm_lift lift_perm_id liftK.
  move/(s _ =P _) => si0; apply/permP=> k.
  case: (unliftP i0 k) => [k'|] ->; rewrite ?lift_perm_id //.
  by rewrite lift_perm_lift -si0 permE ulsfK.
rewrite /cofactor big_distrr /=.
apply: eq_big => [s | s _]; first by rewrite lift_perm_id eqxx.
rewrite -signr_odd mulrA -signr_addb odd_add -odd_lift_perm; congr (_ * _).
case: (pickP 'I_n) => [k0 _ | n0]; last first.
  by rewrite !big1 // => [j /unlift_some[i] | i _]; have:= n0 i.
rewrite (reindex (lift i0)).
  by apply: eq_big => [k | k _] /=; rewrite ?neq_lift // !mxE lift_perm_lift.
exists (fun k => odflt k0 (unlift i0 k)) => k; first by rewrite liftK.
by case/unlift_some=> k' -> ->.
Qed.

Lemma expand_det_row n (A : 'M[R]_n) i0 :
  \det A = \sum_j A i0 j * cofactor A i0 j.
Proof.
rewrite /(\det A) (partition_big (fun s : 'S_n => s i0) predT) //=.
apply: eq_bigr => j0 _; rewrite expand_cofactor big_distrr /=.
apply: eq_bigr => s /eqP Dsi0.
rewrite mulrCA (bigID (pred1 i0)) /= big_pred1_eq Dsi0; congr (_ * (_ * _)).
by apply: eq_bigl => i; rewrite eq_sym.
Qed.

Lemma cofactor_tr n (A : 'M[R]_n) i j : cofactor A^T i j = cofactor A j i.
Proof.
rewrite /cofactor addnC; congr (_ * _).
rewrite -tr_row' -tr_col' det_tr; congr (\det _).
by apply/matrixP=> ? ?; rewrite !mxE.
Qed.

Lemma cofactorZ n a (A : 'M[R]_n) i j : 
  cofactor (a *: A) i j = a ^+ n.-1 * cofactor A i j.
Proof. by rewrite {1}/cofactor !linearZ detZ mulrCA mulrA. Qed.

Lemma expand_det_col n (A : 'M[R]_n) j0 :
  \det A = \sum_i (A i j0 * cofactor A i j0).
Proof.
rewrite -det_tr (expand_det_row _ j0).
by apply: eq_bigr => i _; rewrite cofactor_tr mxE.
Qed.

Lemma trmx_adj n (A : 'M[R]_n) : (\adj A)^T = \adj A^T.
Proof. by apply/matrixP=> i j; rewrite !mxE cofactor_tr. Qed.

Lemma adjZ n a (A : 'M[R]_n) : \adj (a *: A) = a^+n.-1 *: \adj A.
Proof. by apply/matrixP=> i j; rewrite !mxE cofactorZ. Qed.

(* Cramer Rule : adjugate on the left *)
Lemma mul_mx_adj n (A : 'M[R]_n) : A *m \adj A = (\det A)%:M.
Proof.
apply/matrixP=> i1 i2; rewrite !mxE; case Di: (i1 == i2).
  rewrite (eqP Di) (expand_det_row _ i2) //=.
  by apply: eq_bigr => j _; congr (_ * _); rewrite mxE.
pose B := \matrix_(i, j) (if i == i2 then A i1 j else A i j).
have EBi12: B i1 =1 B i2 by move=> j; rewrite /= !mxE Di eq_refl.
rewrite -[_ *+ _](determinant_alternate (negbT Di) EBi12) (expand_det_row _ i2).
apply: eq_bigr => j _; rewrite !mxE eq_refl; congr (_ * (_ * _)).
apply: eq_bigr => s _; congr (_ * _); apply: eq_bigr => i _.
by rewrite !mxE eq_sym -if_neg neq_lift.
Qed.

(* Cramer rule : adjugate on the right *)
Lemma mul_adj_mx n (A : 'M[R]_n) : \adj A *m A = (\det A)%:M.
Proof.
by apply: trmx_inj; rewrite trmx_mul trmx_adj mul_mx_adj det_tr tr_scalar_mx.
Qed.

Lemma adj1 n : \adj (1%:M) = 1%:M :> 'M[R]_n.
Proof. by rewrite -{2}(det1 n) -mul_adj_mx mulmx1. Qed.

(* Left inverses are right inverses. *)
Lemma mulmx1C n (A B : 'M[R]_n) : A *m B = 1%:M -> B *m A = 1%:M.
Proof.
move=> AB1; pose A' := \det B *: \adj A.
suffices kA: A' *m A = 1%:M by rewrite -[B]mul1mx -kA -(mulmxA A') AB1 mulmx1.
by rewrite -scalemxAl mul_adj_mx scale_scalar_mx mulrC -det_mulmx AB1 det1.
Qed.

(* Only tall matrices have inverses. *)
Lemma mulmx1_min m n (A : 'M[R]_(m, n)) B : A *m B = 1%:M -> m <= n.
Proof.
move=> AB1; rewrite leqNgt; apply/negP=> /subnKC; rewrite addSnnS.
move: (_ - _)%N => m' def_m; move: AB1; rewrite -{m}def_m in A B *.
rewrite -(vsubmxK A) -(hsubmxK B) mul_col_row scalar_mx_block.
case/eq_block_mx=> /mulmx1C BlAu1 AuBr0 _ => /eqP/idPn[].
by rewrite -[_ B]mul1mx -BlAu1 -mulmxA AuBr0 !mulmx0 eq_sym oner_neq0.
Qed.

Lemma det_ublock n1 n2 Aul (Aur : 'M[R]_(n1, n2)) Adr :
  \det (block_mx Aul Aur 0 Adr) = \det Aul * \det Adr.
Proof.
elim: n1 => [|n1 IHn1] in Aul Aur *.
  have ->: Aul = 1%:M by apply/matrixP=> i [].
  rewrite det1 mul1r; congr (\det _); apply/matrixP=> i j.
  by do 2![rewrite !mxE; case: splitP => [[]|k] //=; move/val_inj=> <- {k}].
rewrite (expand_det_col _ (lshift n2 0)) big_split_ord /=.
rewrite addrC big1 1?simp => [|i _]; last by rewrite block_mxEdl mxE simp.
rewrite (expand_det_col _ 0) big_distrl /=; apply eq_bigr=> i _.
rewrite block_mxEul -!mulrA; do 2!congr (_ * _).
by rewrite col'_col_mx !col'Kl raddf0 row'Ku row'_row_mx IHn1.
Qed.

Lemma det_lblock n1 n2 Aul (Adl : 'M[R]_(n2, n1)) Adr :
  \det (block_mx Aul 0 Adl Adr) = \det Aul * \det Adr.
Proof. by rewrite -det_tr tr_block_mx trmx0 det_ublock !det_tr. Qed.

End ComMatrix.

Arguments lin_mul_row {R m n} u.
Arguments lin_mulmx {R m n p} A.

Canonical matrix_finAlgType (R : finComRingType) n' :=
  [finAlgType R of 'M[R]_n'.+1].

(*****************************************************************************)
(********************** Matrix unit ring and inverse matrices ****************)
(*****************************************************************************)

Section MatrixInv.

Variables R : comUnitRingType.

Section Defs.

Variable n : nat.
Implicit Type A : 'M[R]_n.

Definition unitmx : pred 'M[R]_n := fun A => \det A \is a GRing.unit.
Definition invmx A := if A \in unitmx then (\det A)^-1 *: \adj A else A.

Lemma unitmxE A : (A \in unitmx) = (\det A \is a GRing.unit).
Proof. by []. Qed.

Lemma unitmx1 : 1%:M \in unitmx. Proof. by rewrite unitmxE det1 unitr1. Qed.

Lemma unitmx_perm s : perm_mx s \in unitmx.
Proof. by rewrite unitmxE det_perm unitrX ?unitrN ?unitr1. Qed.

Lemma unitmx_tr A : (A^T \in unitmx) = (A \in unitmx).
Proof. by rewrite unitmxE det_tr. Qed.

Lemma unitmxZ a A : a \is a GRing.unit -> (a *: A \in unitmx) = (A \in unitmx).
Proof. by move=> Ua; rewrite !unitmxE detZ unitrM unitrX. Qed.

Lemma invmx1 : invmx 1%:M = 1%:M.
Proof. by rewrite /invmx det1 invr1 scale1r adj1 if_same. Qed.

Lemma invmxZ a A : a *: A \in unitmx -> invmx (a *: A) = a^-1 *: invmx A.
Proof.
rewrite /invmx !unitmxE detZ unitrM => /andP[Ua U_A].
rewrite Ua U_A adjZ !scalerA invrM {U_A}//=.
case: (posnP n) A => [-> | n_gt0] A; first by rewrite flatmx0 [_ *: _]flatmx0.
rewrite unitrX_pos // in Ua; rewrite -[_ * _](mulrK Ua) mulrC -!mulrA.
by rewrite -exprSr prednK // !mulrA divrK ?unitrX.
Qed.

Lemma invmx_scalar a : invmx (a%:M) = a^-1%:M.
Proof.
case Ua: (a%:M \in unitmx).
  by rewrite -scalemx1 in Ua *; rewrite invmxZ // invmx1 scalemx1.
rewrite /invmx Ua; have [->|n_gt0] := posnP n; first by rewrite ![_%:M]flatmx0.
by rewrite unitmxE det_scalar unitrX_pos // in Ua; rewrite invr_out ?Ua.
Qed.

Lemma mulVmx : {in unitmx, left_inverse 1%:M invmx mulmx}.
Proof.
by move=> A nsA; rewrite /invmx nsA -scalemxAl mul_adj_mx scale_scalar_mx mulVr.
Qed.

Lemma mulmxV : {in unitmx, right_inverse 1%:M invmx mulmx}.
Proof.
by move=> A nsA; rewrite /invmx nsA -scalemxAr mul_mx_adj scale_scalar_mx mulVr.
Qed.

Lemma mulKmx m : {in unitmx, @left_loop _ 'M_(n, m) invmx mulmx}.
Proof. by move=> A uA /= B; rewrite mulmxA mulVmx ?mul1mx. Qed.

Lemma mulKVmx m : {in unitmx, @rev_left_loop _ 'M_(n, m) invmx mulmx}.
Proof. by move=> A uA /= B; rewrite mulmxA mulmxV ?mul1mx. Qed.

Lemma mulmxK m : {in unitmx, @right_loop 'M_(m, n) _ invmx mulmx}.
Proof. by move=> A uA /= B; rewrite -mulmxA mulmxV ?mulmx1. Qed.

Lemma mulmxKV m : {in unitmx, @rev_right_loop 'M_(m, n) _ invmx mulmx}.
Proof. by move=> A uA /= B; rewrite -mulmxA mulVmx ?mulmx1. Qed.

Lemma det_inv A : \det (invmx A) = (\det A)^-1.
Proof.
case uA: (A \in unitmx); last by rewrite /invmx uA invr_out ?negbT.
by apply: (mulrI uA); rewrite -det_mulmx mulmxV ?divrr ?det1.
Qed.

Lemma unitmx_inv A : (invmx A \in unitmx) = (A \in unitmx).
Proof. by rewrite !unitmxE det_inv unitrV. Qed.

Lemma unitmx_mul A B : (A *m B \in unitmx) = (A \in unitmx) && (B \in unitmx).
Proof. by rewrite -unitrM -det_mulmx. Qed.

Lemma trmx_inv (A : 'M_n) : (invmx A)^T = invmx (A^T).
Proof. by rewrite (fun_if trmx) linearZ /= trmx_adj -unitmx_tr -det_tr. Qed.

Lemma invmxK : involutive invmx.
Proof.
move=> A; case uA : (A \in unitmx); last by rewrite /invmx !uA.
by apply: (can_inj (mulKVmx uA)); rewrite mulVmx // mulmxV ?unitmx_inv.
Qed.

Lemma mulmx1_unit A B : A *m B = 1%:M -> A \in unitmx /\ B \in unitmx.
Proof. by move=> AB1; apply/andP; rewrite -unitmx_mul AB1 unitmx1. Qed.

Lemma intro_unitmx A B : B *m A = 1%:M /\ A *m B = 1%:M -> unitmx A.
Proof. by case=> _ /mulmx1_unit[]. Qed.

Lemma invmx_out : {in [predC unitmx], invmx =1 id}.
Proof. by move=> A; rewrite inE /= /invmx -if_neg => ->. Qed.

End Defs.

Variable n' : nat.
Local Notation n := n'.+1.

Definition matrix_unitRingMixin :=
  UnitRingMixin (@mulVmx n) (@mulmxV n) (@intro_unitmx n) (@invmx_out n).
Canonical matrix_unitRing :=
  Eval hnf in UnitRingType 'M[R]_n matrix_unitRingMixin.
Canonical matrix_unitAlg := Eval hnf in [unitAlgType R of 'M[R]_n].

(* Lemmas requiring that the coefficients are in a unit ring *)

Lemma detV (A : 'M_n) : \det A^-1 = (\det A)^-1.
Proof. exact: det_inv. Qed.

Lemma unitr_trmx (A : 'M_n) : (A^T  \is a GRing.unit) = (A \is a GRing.unit).
Proof. exact: unitmx_tr. Qed.

Lemma trmxV (A : 'M_n) : A^-1^T = (A^T)^-1.
Proof. exact: trmx_inv. Qed.

Lemma perm_mxV (s : 'S_n) : perm_mx s^-1 = (perm_mx s)^-1.
Proof.
rewrite -[_^-1]mul1r; apply: (canRL (mulmxK (unitmx_perm s))).
by rewrite -perm_mxM mulVg perm_mx1.
Qed.

Lemma is_perm_mxV (A : 'M_n) : is_perm_mx A^-1 = is_perm_mx A.
Proof.
apply/is_perm_mxP/is_perm_mxP=> [] [s defA]; exists s^-1%g.
  by rewrite -(invrK A) defA perm_mxV.
by rewrite defA perm_mxV.
Qed.

End MatrixInv.

Prenex Implicits unitmx invmx invmxK.

Canonical matrix_countUnitRingType (R : countComUnitRingType) n :=
  [countUnitRingType of 'M[R]_n.+1].

(* Finite inversible matrices and the general linear group. *)
Section FinUnitMatrix.

Variables (n : nat) (R : finComUnitRingType).

Canonical matrix_finUnitRingType n' :=
  Eval hnf in [finUnitRingType of 'M[R]_n'.+1].

Definition GLtype of phant R := {unit 'M[R]_n.-1.+1}.

Coercion GLval ph (u : GLtype ph) : 'M[R]_n.-1.+1 :=
  let: FinRing.Unit A _ := u in A.

End FinUnitMatrix.

Bind Scope group_scope with GLtype.
Arguments GLval {n%N R ph} u%g.

Notation "{ ''GL_' n [ R ] }" := (GLtype n (Phant R))
  (at level 0, n at level 2, format "{ ''GL_' n [ R ] }") : type_scope.
Notation "{ ''GL_' n ( p ) }" := {'GL_n['F_p]}
  (at level 0, n at level 2, p at level 10,
    format "{ ''GL_' n ( p ) }") : type_scope.

Section GL_unit.

Variables (n : nat) (R : finComUnitRingType).

Canonical GL_subType := [subType of {'GL_n[R]} for GLval].
Definition GL_eqMixin := Eval hnf in [eqMixin of {'GL_n[R]} by <:].
Canonical GL_eqType := Eval hnf in EqType {'GL_n[R]} GL_eqMixin.
Canonical GL_choiceType := Eval hnf in [choiceType of {'GL_n[R]}].
Canonical GL_countType := Eval hnf in [countType of {'GL_n[R]}].
Canonical GL_subCountType := Eval hnf in [subCountType of {'GL_n[R]}].
Canonical GL_finType := Eval hnf in [finType of {'GL_n[R]}].
Canonical GL_subFinType := Eval hnf in [subFinType of {'GL_n[R]}].
Canonical GL_baseFinGroupType := Eval hnf in [baseFinGroupType of {'GL_n[R]}].
Canonical GL_finGroupType := Eval hnf in [finGroupType of {'GL_n[R]}].
Definition GLgroup of phant R := [set: {'GL_n[R]}].
Canonical GLgroup_group ph := Eval hnf in [group of GLgroup ph].

Implicit Types u v : {'GL_n[R]}.

Lemma GL_1E : GLval 1 = 1. Proof. by []. Qed.
Lemma GL_VE u : GLval u^-1 = (GLval u)^-1. Proof. by []. Qed.
Lemma GL_VxE u : GLval u^-1 = invmx u. Proof. by []. Qed.
Lemma GL_ME u v : GLval (u * v) = GLval u * GLval v. Proof. by []. Qed.
Lemma GL_MxE u v : GLval (u * v) = u *m v. Proof. by []. Qed.
Lemma GL_unit u : GLval u \is a GRing.unit. Proof. exact: valP. Qed.
Lemma GL_unitmx u : val u \in unitmx. Proof. exact: GL_unit. Qed.

Lemma GL_det u : \det u != 0.
Proof.
by apply: contraL (GL_unitmx u); rewrite unitmxE => /eqP->; rewrite unitr0.
Qed.

End GL_unit.

Notation "''GL_' n [ R ]" := (GLgroup n (Phant R))
  (at level 8, n at level 2, format "''GL_' n [ R ]") : group_scope.
Notation "''GL_' n ( p )" := 'GL_n['F_p]
  (at level 8, n at level 2, p at level 10,
   format "''GL_' n ( p )") : group_scope.
Notation "''GL_' n [ R ]" := (GLgroup_group n (Phant R)) : Group_scope.
Notation "''GL_' n ( p )" := (GLgroup_group n (Phant 'F_p)) : Group_scope.

(*****************************************************************************)
(********************** Matrices over a domain *******************************)
(*****************************************************************************)

Section MatrixDomain.

Variable R : idomainType.

Lemma scalemx_eq0 m n a (A : 'M[R]_(m, n)) :
  (a *: A == 0) = (a == 0) || (A == 0).
Proof.
case nz_a: (a == 0) / eqP => [-> | _]; first by rewrite scale0r eqxx.
apply/eqP/eqP=> [aA0 | ->]; last exact: scaler0.
apply/matrixP=> i j; apply/eqP; move/matrixP/(_ i j)/eqP: aA0.
by rewrite !mxE mulf_eq0 nz_a.
Qed.

Lemma scalemx_inj m n a :
  a != 0 -> injective ( *:%R a : 'M[R]_(m, n) -> 'M[R]_(m, n)).
Proof.
move=> nz_a A B eq_aAB; apply: contraNeq nz_a.
rewrite -[A == B]subr_eq0 -[a == 0]orbF => /negPf<-.
by rewrite -scalemx_eq0 linearB subr_eq0 /= eq_aAB.
Qed.

Lemma det0P n (A : 'M[R]_n) :
  reflect (exists2 v : 'rV[R]_n, v != 0 & v *m A = 0) (\det A == 0).
Proof.
apply: (iffP eqP) => [detA0 | [v n0v vA0]]; last first.
  apply: contraNeq n0v => nz_detA; rewrite -(inj_eq (scalemx_inj nz_detA)).
  by rewrite scaler0 -mul_mx_scalar -mul_mx_adj mulmxA vA0 mul0mx.
elim: n => [|n IHn] in A detA0 *.
  by case/idP: (oner_eq0 R); rewrite -detA0 [A]thinmx0 -(thinmx0 1%:M) det1.
have [{detA0}A'0 | nzA'] := eqVneq (row 0 (\adj A)) 0; last first.
  exists (row 0 (\adj A)) => //; rewrite rowE -mulmxA mul_adj_mx detA0.
  by rewrite mul_mx_scalar scale0r.
pose A' := col' 0 A; pose vA := col 0 A.
have defA: A = row_mx vA A'.
  apply/matrixP=> i j; rewrite !mxE.
  case: splitP => j' def_j; rewrite mxE; congr (A i _); apply: val_inj => //=.
  by rewrite def_j [j']ord1.
have{IHn} w_ j : exists w : 'rV_n.+1, [/\ w != 0, w 0 j = 0 & w *m A' = 0].
  have [|wj nzwj wjA'0] := IHn (row' j A').
    by apply/eqP; move/rowP/(_ j)/eqP: A'0; rewrite !mxE mulf_eq0 signr_eq0.
  exists (\row_k oapp (wj 0) 0 (unlift j k)).
  rewrite !mxE unlift_none -wjA'0; split=> //.
    apply: contraNneq nzwj => w0; apply/eqP/rowP=> k'.
    by move/rowP/(_ (lift j k')): w0; rewrite !mxE liftK.
  apply/rowP=> k; rewrite !mxE (bigD1 j) //= mxE unlift_none mul0r add0r.
  rewrite (reindex_onto (lift j) (odflt k \o unlift j)) /= => [|k'].
    by apply: eq_big => k'; rewrite ?mxE liftK eq_sym neq_lift eqxx.
  by rewrite eq_sym; case/unlift_some=> ? ? ->.
have [w0 [nz_w0 w00_0 w0A']] := w_ 0; pose a0 := (w0 *m vA) 0 0.
have [j {nz_w0}/= nz_w0j | w00] := pickP [pred j | w0 0 j != 0]; last first.
  by case/eqP: nz_w0; apply/rowP=> j; rewrite mxE; move/eqP: (w00 j).
have{w_} [wj [nz_wj wj0_0 wjA']] := w_ j; pose aj := (wj *m vA) 0 0.
have [aj0 | nz_aj] := eqVneq aj 0.
  exists wj => //; rewrite defA (@mul_mx_row _ _ _ 1) [_ *m _]mx11_scalar -/aj.
  by rewrite aj0 raddf0 wjA' row_mx0.
exists (aj *: w0 - a0 *: wj).
  apply: contraNneq nz_aj; move/rowP/(_ j)/eqP; rewrite !mxE wj0_0 mulr0 subr0.
  by rewrite mulf_eq0 (negPf nz_w0j) orbF.
rewrite defA (@mul_mx_row _ _ _ 1) !mulmxBl -!scalemxAl w0A' wjA' !linear0.
by rewrite -mul_mx_scalar -mul_scalar_mx -!mx11_scalar subrr addr0 row_mx0.
Qed.

End MatrixDomain.

Arguments det0P {R n A}.

(* Parametricity at the field level (mx_is_scalar, unit and inverse are only *)
(* mapped at this level).                                                    *)
Section MapFieldMatrix.

Variables (aF : fieldType) (rF : comUnitRingType) (f : {rmorphism aF -> rF}).
Local Notation "A ^f" := (map_mx f A) : ring_scope.

Lemma map_mx_inj {m n} : injective (map_mx f : 'M_(m, n) -> 'M_(m, n)).
Proof.
move=> A B eq_AB; apply/matrixP=> i j.
by move/matrixP/(_ i j): eq_AB; rewrite !mxE; apply: fmorph_inj.
Qed.

Lemma map_mx_is_scalar n (A : 'M_n) : is_scalar_mx A^f = is_scalar_mx A.
Proof.
rewrite /is_scalar_mx; case: (insub _) => // i.
by rewrite mxE -map_scalar_mx inj_eq //; apply: map_mx_inj.
Qed.

Lemma map_unitmx n (A : 'M_n) : (A^f \in unitmx) = (A \in unitmx).
Proof. by rewrite unitmxE det_map_mx // fmorph_unit // -unitfE. Qed.

Lemma map_mx_unit n' (A : 'M_n'.+1) :
  (A^f \is a GRing.unit) = (A \is a GRing.unit).
Proof. exact: map_unitmx. Qed.

Lemma map_invmx n (A : 'M_n) : (invmx A)^f = invmx A^f.
Proof.
rewrite /invmx map_unitmx (fun_if (map_mx f)).
by rewrite map_mxZ map_mx_adj det_map_mx fmorphV.
Qed.

Lemma map_mx_inv n' (A : 'M_n'.+1) : A^-1^f = A^f^-1.
Proof. exact: map_invmx. Qed.
  
Lemma map_mx_eq0 m n (A : 'M_(m, n)) : (A^f == 0) = (A == 0).
Proof. by rewrite -(inj_eq map_mx_inj) raddf0. Qed.

End MapFieldMatrix.

Arguments map_mx_inj {aF rF f m n} [A1 A2] eqA12f : rename.

(*****************************************************************************)
(****************************** LUP decomposion ******************************)
(*****************************************************************************)

Section CormenLUP.

Variable F : fieldType.

(* Decomposition of the matrix A to P A = L U with *)
(*   - P a permutation matrix                      *)
(*   - L a unipotent lower triangular matrix       *)
(*   - U an upper triangular matrix                *)

Fixpoint cormen_lup {n} :=
  match n return let M := 'M[F]_n.+1 in M -> M * M * M with
  | 0 => fun A => (1, 1, A)
  | _.+1 => fun A =>
    let k := odflt 0 [pick k | A k 0 != 0] in
    let A1 : 'M_(1 + _) := xrow 0 k A in
    let P1 : 'M_(1 + _) := tperm_mx 0 k in
    let Schur := ((A k 0)^-1 *: dlsubmx A1) *m ursubmx A1 in
    let: (P2, L2, U2) := cormen_lup (drsubmx A1 - Schur) in
    let P := block_mx 1 0 0 P2 *m P1 in
    let L := block_mx 1 0 ((A k 0)^-1 *: (P2 *m dlsubmx A1)) L2 in
    let U := block_mx (ulsubmx A1) (ursubmx A1) 0 U2 in
    (P, L, U)
  end.

Lemma cormen_lup_perm n (A : 'M_n.+1) : is_perm_mx (cormen_lup A).1.1.
Proof.
elim: n => [|n IHn] /= in A *; first exact: is_perm_mx1.
set A' := _ - _; move/(_ A'): IHn; case: cormen_lup => [[P L U]] {A'}/=.
rewrite (is_perm_mxMr _ (perm_mx_is_perm _ _)).
by case/is_perm_mxP => s ->; apply: lift0_mx_is_perm.
Qed.

Lemma cormen_lup_correct n (A : 'M_n.+1) :
  let: (P, L, U) := cormen_lup A in P * A = L * U.
Proof.
elim: n => [|n IHn] /= in A *; first by rewrite !mul1r.
set k := odflt _ _; set A1 : 'M_(1 + _) := xrow _ _ _.
set A' := _ - _; move/(_ A'): IHn; case: cormen_lup => [[P' L' U']] /= IHn.
rewrite -mulrA -!mulmxE -xrowE -/A1 /= -[n.+2]/(1 + n.+1)%N -{1}(submxK A1).
rewrite !mulmx_block !mul0mx !mulmx0 !add0r !addr0 !mul1mx -{L' U'}[L' *m _]IHn.
rewrite -scalemxAl !scalemxAr -!mulmxA addrC -mulrDr {A'}subrK.
congr (block_mx _ _ (_ *m _) _).
rewrite [_ *: _]mx11_scalar !mxE lshift0 tpermL {}/A1 {}/k.
case: pickP => /= [k nzAk0 | no_k]; first by rewrite mulVf ?mulmx1.
rewrite (_ : dlsubmx _ = 0) ?mul0mx //; apply/colP=> i.
by rewrite !mxE lshift0 (elimNf eqP (no_k _)).
Qed.

Lemma cormen_lup_detL n (A : 'M_n.+1) : \det (cormen_lup A).1.2 = 1.
Proof.
elim: n => [|n IHn] /= in A *; first by rewrite det1.
set A' := _ - _; move/(_ A'): IHn; case: cormen_lup => [[P L U]] {A'}/= detL.
by rewrite (@det_lblock _ 1) det1 mul1r.
Qed.

Lemma cormen_lup_lower n A (i j : 'I_n.+1) :
  i <= j -> (cormen_lup A).1.2 i j = (i == j)%:R.
Proof.
elim: n => [|n IHn] /= in A i j *; first by rewrite [i]ord1 [j]ord1 mxE.
set A' := _ - _; move/(_ A'): IHn; case: cormen_lup => [[P L U]] {A'}/= Ll.
rewrite !mxE split1; case: unliftP => [i'|] -> /=; rewrite !mxE split1.
  by case: unliftP => [j'|] -> //; apply: Ll.
by case: unliftP => [j'|] ->; rewrite /= mxE.
Qed.

Lemma cormen_lup_upper n A (i j : 'I_n.+1) :
  j < i -> (cormen_lup A).2 i j = 0 :> F.
Proof.
elim: n => [|n IHn] /= in A i j *; first by rewrite [i]ord1.
set A' := _ - _; move/(_ A'): IHn; case: cormen_lup => [[P L U]] {A'}/= Uu.
rewrite !mxE split1; case: unliftP => [i'|] -> //=; rewrite !mxE split1.
by case: unliftP => [j'|] ->; [apply: Uu | rewrite /= mxE].
Qed.

End CormenLUP.

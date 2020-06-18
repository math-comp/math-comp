(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice.
From mathcomp Require Import fintype finfun bigop finset fingroup perm order.
From mathcomp Require Import div prime binomial ssralg countalg finalg zmodp.

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
(*     map2_mx f A B == the pointwise image of A and B by f, i.e., the matrix *)
(*                     ABf congruent to A with ABf i j = f (A i j) for all i  *)
(*                     and j.                                                 *)
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
(* \mxblock_(i < m, j < n) B i j                                              *)
(*                == the block matrix of type 'M_(\sum_i p_ i, \sum_j q_ j)   *)
(*                             / (B 0 0) ⋯ (B 0 j) ⋯ (B 0 n) \                *)
(*                             |   ...       ...       ...   |                *)
(*                             | (B i 0) ⋯ (B i j) ⋯ (B i n) |                *)
(*                             |   ...       ...       ...   |                *)
(*                             \ (B m 0) ⋯ (B m j) ⋯ (B m n) /                *)
(*                   where each block (B i j) has type 'M_(p_ i, q_ j).       *)
(* \mxdiag_(i < n) B i == the block square matrix of type 'M_(\sum_i p_ i)    *)
(*                                / (B 0)      0      \                       *)
(*                                |     ...     ...   |                       *)
(*                                |  0    (B i)    0  |                       *)
(*                                |   ...     ...     |                       *)
(*                                \      0      (B n) /                       *)
(*                        where each block (B i) has type 'M_(p_ i).          *)
(*  \mxrow_(j < n) B j ==  the block matrix of type 'M_(m, \sum_j q_ j).      *)
(*                                 < (B 0) ... (B n) >                        *)
(*                         where each block (B j) has type 'M_(m, q_ j).      *)
(*  \mxcol_(i < m) B i ==  the block matrix of type 'M_(\sum_i p_ i, n)       *)
(*                                      / (B 0) \                             *)
(*                                      |  ...  |                             *)
(*                                      \ (B m) /                             *)
(*                         where each block (B i) has type 'M(p_ i, n).       *)
(*   [l|r]submx A == the left/right submatrices of a row block matrix A.      *)
(*                   Note that the type of A, 'M_(m, n1 + n2) indicates how A *)
(*                   should be decomposed.                                    *)
(*   [u|d]submx A == the up/down submatrices of a column block matrix A.      *)
(* [u|d][l|r]submx A == the upper left, etc submatrices of a block matrix A.  *)
(*  submxblock A i j == the block submatrix of type 'M_(p_ i, q_ j) of A.     *)
(*                      The type of A, 'M_(\sum_i p_ i, \sum_i q_ i)          *)
(*                      indicates how A should be decomposed.                 *)
(*                      There is no analogous for mxdiag since one can use    *)
(*                      submxblock A i i to extract a diagonal block.         *)
(*   submxrow A j == the submatrix of type 'M_(m, q_ j) of A. The type of A,  *)
(*                   'M_(m, \sum_j q_ j) indicates how A should be decomposed.*)
(*   submxrow A j == the submatrix of type 'M_(p_ i, n) of A. The type of A,  *)
(*                   'M_(\sum_i p_ i, n) indicates how A should be decomposed.*)
(*    mxsub f g A == generic reordered submatrix, given by functions f and g  *)
(*                   which specify which subset of rows and columns to take   *)
(*                   and how to reorder them, e.g. picking f and g to be      *)
(*                   increasing yields traditional submatrices.               *)
(*                := \matrix_(i, j) A (f i) (g i)                             *)
(*     rowsub f A := mxsub f id A                                             *)
(*     colsub g A := mxsub id g A                                             *)
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
(*  is_diag_mx A <=> A is a diagonal matrix:  forall i j, i != j -> A i j = 0 *)
(*  is_trig_mx A <=> A is a triangular matrix: forall i j, i < j -> A i j = 0 *)
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
(* A \is a mxOver S == the matrix A has its coefficients in S.                *)
(*       comm_mx A B := A *m B = B *m A                                       *)
(*      comm_mxb A B := A *m B == B *m A                                      *)
(* all_comm_mx As fs := all2rel comm_mxb fs                                   *)
(* The following operations provide a correspondence between linear functions *)
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
(* Vandermonde m a == the 'M[R]_(m, n) Vandermonde matrix, given a : 'rV_n    *)
(*                    /         1          ...           1              \     *)
(*                    |      (a 0 0)       ...      (a 0 (n - 1))       |     *)
(*                    |    (a 0 0 ^+ 2)    ...    (a 0 (n - 1) ^+ 2)    |     *)
(*                    |        ...                      ...             |     *)
(*                    \ (a 0 0 ^+ (m - 1)) ... (a 0 (n - 1) ^+ (m - 1)) /     *)
(*                 := \matrix_(i < m, j < n) a 0 j ^+ i.                      *)
(* Finally, as an example of the use of block products, we program and prove  *)
(* the correctness of a classical linear algebra algorithm:                   *)
(*   cormen_lup A == the triangular decomposition (L, U, P) of a nontrivial   *)
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
Reserved Notation "''M_' ( n )" (at level 8). (* only parsing *)
Reserved Notation "''M_' ( m , n )" (at level 8, format "''M_' ( m ,  n )").
Reserved Notation "''M[' R ]_ n"    (at level 8, n at level 2). (* only parsing *)
Reserved Notation "''rV[' R ]_ n"   (at level 8, n at level 2). (* only parsing *)
Reserved Notation "''cV[' R ]_ n"   (at level 8, n at level 2). (* only parsing *)
Reserved Notation "''M[' R ]_ ( n )"     (at level 8). (* only parsing *)
Reserved Notation "''M[' R ]_ ( m , n )" (at level 8). (* only parsing *)

Reserved Notation "\matrix_ i E"
  (at level 36, E at level 36, i at level 2,
   format "\matrix_ i  E").
Reserved Notation "\matrix_ ( i < n ) E"
  (at level 36, E at level 36, i, n at level 50). (* only parsing *)
Reserved Notation "\matrix_ ( i , j ) E"
  (at level 36, E at level 36, i, j at level 50,
   format "\matrix_ ( i ,  j )  E").
Reserved Notation "\matrix[ k ]_ ( i , j ) E"
  (at level 36, E at level 36, i, j at level 50,
   format "\matrix[ k ]_ ( i ,  j )  E").
Reserved Notation "\matrix_ ( i < m , j < n ) E"
  (at level 36, E at level 36, i, m, j, n at level 50). (* only parsing *)
Reserved Notation "\matrix_ ( i , j < n ) E"
  (at level 36, E at level 36, i, j, n at level 50). (* only parsing *)
Reserved Notation "\row_ j E"
  (at level 36, E at level 36, j at level 2,
   format "\row_ j  E").
Reserved Notation "\row_ ( j < n ) E"
  (at level 36, E at level 36, j, n at level 50). (* only parsing *)
Reserved Notation "\col_ j E"
  (at level 36, E at level 36, j at level 2,
   format "\col_ j  E").
Reserved Notation "\col_ ( j < n ) E"
  (at level 36, E at level 36, j, n at level 50). (* only parsing *)
Reserved Notation "\mxblock_ ( i , j ) E"
  (at level 36, E at level 36, i, j at level 50,
   format "\mxblock_ ( i ,  j )  E").
Reserved Notation "\mxblock_ ( i < m , j < n ) E"
  (at level 36, E at level 36, i, m, j, n at level 50). (* only parsing *)
Reserved Notation "\mxblock_ ( i , j < n ) E"
  (at level 36, E at level 36, i, j, n at level 50). (* only parsing *)
Reserved Notation "\mxrow_ j E"
  (at level 36, E at level 36, j at level 2,
   format "\mxrow_ j  E").
Reserved Notation "\mxrow_ ( j < n ) E"
  (at level 36, E at level 36, j, n at level 50). (* only parsing *)
Reserved Notation "\mxcol_ j E"
  (at level 36, E at level 36, j at level 2,
   format "\mxcol_ j  E").
Reserved Notation "\mxcol_ ( j < n ) E"
  (at level 36, E at level 36, j, n at level 50). (* only parsing *)
Reserved Notation "\mxdiag_ j E"
  (at level 36, E at level 36, j at level 2,
   format "\mxdiag_ j  E").
Reserved Notation "\mxdiag_ ( j < n ) E"
  (at level 36, E at level 36, j, n at level 50). (* only parsing *)

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

Variant matrix : predArgType := Matrix of {ffun 'I_m * 'I_n -> R}.

Definition mx_val A := let: Matrix g := A in g.

HB.instance Definition _ := [IsNew for mx_val].

Definition fun_of_matrix A (i : 'I_m) (j : 'I_n) := mx_val A (i, j).

Coercion fun_of_matrix : matrix >-> Funclass.

End MatrixDef.

Fact matrix_key : unit. Proof. by []. Qed.

HB.lock
Definition matrix_of_fun R (m n : nat) (k : unit) (F : 'I_m -> 'I_n -> R) :=
  @Matrix R m n [ffun ij => F ij.1 ij.2].
Canonical matrix_unlockable := Unlockable matrix_of_fun.unlock.

Section MatrixDef2.

Variable R : Type.
Variables m n : nat.
Implicit Type F : 'I_m -> 'I_n -> R.

Lemma mxE k F : matrix_of_fun k F =2 F.
Proof. by move=> i j; rewrite unlock /fun_of_matrix /= ffunE. Qed.

Lemma matrixP (A B : matrix R m n) : A =2 B <-> A = B.
Proof.
rewrite /fun_of_matrix; split=> [/= eqAB | -> //].
by apply/val_inj/ffunP=> [[i j]]; apply: eqAB.
Qed.

Lemma eq_mx k F1 F2 : (F1 =2 F2) -> matrix_of_fun k F1 = matrix_of_fun k F2.
Proof. by move=> eq_F; apply/matrixP => i j; rewrite !mxE eq_F. Qed.

End MatrixDef2.

Arguments eq_mx {R m n k} [F1] F2 eq_F12.

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

Notation "\matrix[ k ]_ ( i , j ) E" := (matrix_of_fun k (fun i j => E)) :
   ring_scope.

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

HB.instance Definition _ (R : eqType) m n := [Equality of 'M[R]_(m, n) by <:].
HB.instance Definition _ (R : choiceType) m n := [Choice of 'M[R]_(m, n) by <:].
HB.instance Definition _ (R : countType) m n := [Countable of 'M[R]_(m, n) by <:].
HB.instance Definition _ (R : finType) m n := [Finite of 'M[R]_(m, n) by <:].

Lemma card_mx (F : finType) m n : (#|{: 'M[F]_(m, n)}| = #|F| ^ (m * n))%N.
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

(* reindexing/subindex a matrix *)
Definition mxsub m' n' f g A := \matrix_(i < m', j < n') A (f i) (g j).
Local Notation colsub g := (mxsub id g).
Local Notation rowsub f := (mxsub f id).

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

Lemma rowEsub i : row i = rowsub (fun=> i). Proof. by []. Qed.
Lemma colEsub j : col j = colsub (fun=> j). Proof. by []. Qed.

Lemma row'Esub i : row' i = rowsub (lift i). Proof. by []. Qed.
Lemma col'Esub j : col' j = colsub (lift j). Proof. by []. Qed.

Lemma row_permEsub s : row_perm s = rowsub s.
Proof. by rewrite /row_perm /mxsub !unlock. Qed.

Lemma col_permEsub s : col_perm s = colsub s.
Proof. by rewrite /col_perm /mxsub !unlock. Qed.

Lemma xrowEsub i1 i2 : xrow i1 i2 = rowsub (tperm i1 i2).
Proof. exact: row_permEsub. Qed.

Lemma xcolEsub j1 j2 : xcol j1 j2 = colsub (tperm j1 j2).
Proof. exact: col_permEsub. Qed.

Lemma mxsub_id : mxsub id id =1 id.
Proof. by move=> A; apply/matrixP => i j; rewrite !mxE. Qed.

Lemma eq_mxsub m' n' f f' g g' : f =1 f' -> g =1 g' ->
  @mxsub m' n' f g =1 mxsub f' g'.
Proof. by move=> eq_f eq_g A; apply/matrixP => i j; rewrite !mxE eq_f eq_g. Qed.

Lemma eq_rowsub m' (f f' : 'I_m' -> 'I_m) : f =1 f' -> rowsub f =1 rowsub f'.
Proof. by move=> /eq_mxsub; apply. Qed.

Lemma eq_colsub n' (g g' : 'I_n' -> 'I_n) : g =1 g' -> colsub g =1 colsub g'.
Proof. by move=> /eq_mxsub; apply. Qed.

Lemma mxsub_eq_id f g : f =1 id -> g =1 id -> mxsub f g =1 id.
Proof. by move=> fid gid A; rewrite (eq_mxsub fid gid) mxsub_id. Qed.

Lemma mxsub_eq_colsub n' f g : f =1 id -> @mxsub _ n' f g =1 colsub g.
Proof. by move=> f_id; apply: eq_mxsub. Qed.

Lemma mxsub_eq_rowsub m' f g : g =1 id -> @mxsub m' _ f g =1 rowsub f.
Proof. exact: eq_mxsub. Qed.

Lemma mxsub_ffunl m' n' f g : @mxsub m' n' (finfun f) g =1 mxsub f g.
Proof. by apply: eq_mxsub => // i; rewrite ffunE. Qed.

Lemma mxsub_ffunr m' n' f g : @mxsub m' n' f (finfun g) =1 mxsub f g.
Proof. by apply: eq_mxsub => // i; rewrite ffunE. Qed.

Lemma mxsub_ffun m' n' f g : @mxsub m' n' (finfun f) (finfun g) =1 mxsub f g.
Proof. by move=> A; rewrite mxsub_ffunl mxsub_ffunr. Qed.

Lemma mxsub_const m' n' f g a : @mxsub m' n' f g (const_mx a) = const_mx a.
Proof. by apply/matrixP => i j; rewrite !mxE. Qed.

End FixedDim.

Local Notation colsub g := (mxsub id g).
Local Notation rowsub f := (mxsub f id).
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

Lemma eq_castmx m1 n1 m2 n2 (eq_mn eq_mn' : (m1 = m2) * (n1 = n2)) :
  castmx eq_mn =1 castmx eq_mn'.
Proof.
case: eq_mn eq_mn' => [em en] [em' en'] A.
by apply: (canRL (castmxKV _ _)); rewrite castmx_comp castmx_id.
Qed.

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

Lemma trmx_conform m' n' m n (B : 'M_(m', n')) (A : 'M_(m, n)) :
  (conform_mx B A)^T = conform_mx B^T A^T.
Proof.
rewrite /conform_mx; do !case: eqP; rewrite ?mxE// => en em.
by rewrite trmx_cast.
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
Proof. by move/rowP=> eqA12 j; have /[!mxE] := eqA12 j. Qed.

Lemma col_eq m n1 n2 j1 j2 (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)) :
  col j1 A1 = col j2 A2 -> A1^~ j1 =1 A2^~ j2.
Proof. by move/colP=> eqA12 i; have /[!mxE] := eqA12 i. Qed.

Lemma row'_eq m n i0 (A B : 'M_(m, n)) :
  row' i0 A = row' i0 B -> {in predC1 i0, A =2 B}.
Proof.
move=> /matrixP eqAB' i /[!inE]/[1!eq_sym]/unlift_some[i' -> _] j.
by have /[!mxE] := eqAB' i' j.
Qed.

Lemma col'_eq m n j0 (A B : 'M_(m, n)) :
  col' j0 A = col' j0 B -> forall i, {in predC1 j0, A i =1 B i}.
Proof.
move=> /matrixP eqAB' i j /[!inE]/[1!eq_sym]/unlift_some[j' -> _].
by have  /[!mxE] := eqAB' i j'.
Qed.

Lemma tr_row m n i0 (A : 'M_(m, n)) : (row i0 A)^T = col i0 A^T.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma tr_row' m n i0 (A : 'M_(m, n)) : (row' i0 A)^T = col' i0 A^T.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma tr_col m n j0 (A : 'M_(m, n)) : (col j0 A)^T = row j0 A^T.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma tr_col' m n j0 (A : 'M_(m, n)) : (col' j0 A)^T = row' j0 A^T.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma mxsub_comp m1 m2 m3 n1 n2 n3
  (f : 'I_m2 -> 'I_m1) (f' : 'I_m3 -> 'I_m2)
  (g : 'I_n2 -> 'I_n1) (g' : 'I_n3 -> 'I_n2) (A : 'M_(m1, n1)) :
  mxsub (f \o f') (g \o g') A = mxsub f' g' (mxsub f g A).
Proof. by apply/matrixP => i j; rewrite !mxE. Qed.

Lemma rowsub_comp m1 m2 m3 n
  (f : 'I_m2 -> 'I_m1) (f' : 'I_m3 -> 'I_m2) (A : 'M_(m1, n)) :
  rowsub (f \o f') A = rowsub f' (rowsub f A).
Proof. exact: mxsub_comp. Qed.

Lemma colsub_comp m n n2 n3
  (g : 'I_n2 -> 'I_n) (g' : 'I_n3 -> 'I_n2) (A : 'M_(m, n)) :
  colsub (g \o g') A = colsub g' (colsub g A).
Proof. exact: mxsub_comp. Qed.

Lemma mxsubrc m1 m2 n n2 f g (A : 'M_(m1, n)) :
  mxsub f g A = rowsub f (colsub g A) :> 'M_(m2, n2).
Proof. exact: mxsub_comp. Qed.

Lemma mxsubcr m1 m2 n n2 f g (A : 'M_(m1, n)) :
  mxsub f g A = colsub g (rowsub f A) :> 'M_(m2, n2).
Proof. exact: mxsub_comp. Qed.

Lemma rowsub_cast m1 m2 n (eq_m : m1 = m2) (A : 'M_(m2, n)) :
  rowsub (cast_ord eq_m) A = castmx (esym eq_m, erefl) A.
Proof. by case: _ / eq_m in A *; apply: (mxsub_eq_id (cast_ord_id _)). Qed.

Lemma colsub_cast m n1 n2 (eq_n : n1 = n2) (A : 'M_(m, n2)) :
  colsub (cast_ord eq_n) A = castmx (erefl, esym eq_n) A.
Proof. by case: _ / eq_n in A *; apply: (mxsub_eq_id _ (cast_ord_id _)). Qed.

Lemma mxsub_cast m1 m2 n1 n2 (eq_m : m1 = m2) (eq_n : n1 = n2) A :
  mxsub (cast_ord eq_m) (cast_ord eq_n) A = castmx (esym eq_m, esym eq_n) A.
Proof. by rewrite mxsubrc rowsub_cast colsub_cast castmx_comp/= etrans_id. Qed.

Lemma castmxEsub m1 m2 n1 n2 (eq_mn : (m1 = m2) * (n1 = n2)) A :
  castmx eq_mn A = mxsub (cast_ord (esym eq_mn.1)) (cast_ord (esym eq_mn.2)) A.
Proof. by rewrite mxsub_cast !esymK; case: eq_mn. Qed.

Lemma trmx_mxsub m1 m2 n1 n2 f g (A : 'M_(m1, n1)) :
  (mxsub f g A)^T = mxsub g f A^T :> 'M_(n2, m2).
Proof. by apply/matrixP => i j; rewrite !mxE. Qed.

Lemma row_mxsub m1 m2 n1 n2
    (f : 'I_m2 -> 'I_m1) (g : 'I_n2 -> 'I_n1) (A : 'M_(m1, n1)) i :
  row i (mxsub f g A) = row (f i) (colsub g A).
Proof. by rewrite !rowEsub -!mxsub_comp. Qed.

Lemma col_mxsub m1 m2 n1 n2
    (f : 'I_m2 -> 'I_m1) (g : 'I_n2 -> 'I_n1) (A : 'M_(m1, n1)) i :
 col i (mxsub f g A) = col (g i) (rowsub f A).
Proof. by rewrite !colEsub -!mxsub_comp. Qed.

Lemma row_rowsub m1 m2 n (f : 'I_m2 -> 'I_m1) (A : 'M_(m1, n)) i :
  row i (rowsub f A) = row (f i) A.
Proof. by rewrite row_mxsub mxsub_id. Qed.

Lemma col_colsub m n1 n2 (g : 'I_n2 -> 'I_n1) (A : 'M_(m, n1)) i :
  col i (colsub g A) = col (g i) A.
Proof. by rewrite col_mxsub mxsub_id. Qed.

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
Proof. by apply/matrixP=> i j /[!mxE]; case: split_ordP => k -> /[!mxE]. Qed.

Lemma col_mxEu A1 A2 i j : col_mx A1 A2 (lshift m2 i) j = A1 i j.
Proof. by rewrite mxE (unsplitK (inl _ _)). Qed.

Lemma col_mxKu A1 A2 : usubmx (col_mx A1 A2) = A1.
Proof. by apply/matrixP=> i j; rewrite mxE col_mxEu. Qed.

Lemma col_mxEd A1 A2 i j : col_mx A1 A2 (rshift m1 i) j = A2 i j.
Proof. by rewrite mxE (unsplitK (inr _ _)). Qed.

Lemma col_mxKd A1 A2 : dsubmx (col_mx A1 A2) = A2.
Proof. by apply/matrixP=> i j; rewrite mxE col_mxEd. Qed.

Lemma lsubmxEsub : lsubmx = colsub (lshift _).
Proof. by rewrite /lsubmx /mxsub !unlock. Qed.

Lemma rsubmxEsub : rsubmx = colsub (@rshift _ _).
Proof. by rewrite /rsubmx /mxsub !unlock. Qed.

Lemma usubmxEsub : usubmx = rowsub (lshift _).
Proof. by rewrite /usubmx /mxsub !unlock. Qed.

Lemma dsubmxEsub  : dsubmx = rowsub (@rshift _ _).
Proof. by rewrite /dsubmx /mxsub !unlock. Qed.

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

Lemma row_usubmx A i : row i (usubmx A) = row (lshift m2 i) A.
Proof. by apply/rowP=> j; rewrite !mxE; congr (A _ _); apply/val_inj. Qed.

Lemma row_dsubmx A i : row i (dsubmx A) = row (rshift m1 i) A.
Proof. by apply/rowP=> j; rewrite !mxE; congr (A _ _); apply/val_inj. Qed.

Lemma col_lsubmx A i : col i (lsubmx A) = col (lshift n2 i) A.
Proof. by apply/colP=> j; rewrite !mxE; congr (A _ _); apply/val_inj. Qed.

Lemma col_rsubmx A i : col i (rsubmx A) = col (rshift n1 i) A.
Proof. by apply/colP=> j; rewrite !mxE; congr (A _ _); apply/val_inj. Qed.

End CutPaste.

Lemma row_thin_mx m n (A : 'M_(m,0)) (B : 'M_(m,n)) : row_mx A B = B.
Proof.
apply/matrixP=> i j; rewrite mxE; case: splitP=> [|k H]; first by case.
by congr fun_of_matrix; exact: val_inj.
Qed.

Lemma col_flat_mx m n (A : 'M_(0,n)) (B : 'M_(m,n)) : col_mx A B = B.
Proof.
apply/matrixP=> i j; rewrite mxE; case: splitP => [|k H]; first by case.
by congr fun_of_matrix; exact: val_inj.
Qed.

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
case: splitP def_j => j2 ->{j} def_j /[!mxE].
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
by apply/matrixP=> i j /[!mxE]; case: (split j) => j' /[1!mxE].
Qed.

Lemma col_col_mx m1 m2 n j0 (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)) :
  col j0 (col_mx A1 A2) = col_mx (col j0 A1) (col j0 A2).
Proof. by apply: trmx_inj; rewrite !(tr_col, tr_col_mx, row_row_mx). Qed.

Lemma row'_row_mx m n1 n2 i0 (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)) :
  row' i0 (row_mx A1 A2) = row_mx (row' i0 A1) (row' i0 A2).
Proof.
by apply/matrixP=> i j /[!mxE]; case: (split j) => j' /[1!mxE].
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
apply/matrixP=> i /= j; symmetry; rewrite 2!mxE; case: split_ordP => j' ->.
  by rewrite mxE -(row_mxEl _ A2); congr (row_mx _ _ _); apply: ord_inj.
rewrite -(row_mxEr A1); congr (row_mx _ _ _); apply: ord_inj => /=.
by rewrite /bump -ltnS -addSn ltn_addr.
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

Lemma ulsubmxEsub : ulsubmx = mxsub (lshift _) (lshift _) A.
Proof. by rewrite /ulsubmx lsubmxEsub usubmxEsub -mxsub_comp. Qed.

Lemma dlsubmxEsub : dlsubmx = mxsub (@rshift _ _) (lshift _) A.
Proof. by rewrite /dlsubmx lsubmxEsub dsubmxEsub -mxsub_comp. Qed.

Lemma ursubmxEsub : ursubmx = mxsub (lshift _) (@rshift _ _) A.
Proof. by rewrite /ursubmx rsubmxEsub usubmxEsub -mxsub_comp. Qed.

Lemma drsubmxEsub : drsubmx = mxsub (@rshift _ _) (@rshift _ _) A.
Proof. by rewrite /drsubmx rsubmxEsub dsubmxEsub -mxsub_comp. Qed.

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

Section Induction.

Lemma row_ind m (P : forall n, 'M[R]_(m, n) -> Type) :
    (forall A, P 0%N A) ->
    (forall n c A, P n A -> P (1 + n)%N (row_mx c A)) ->
  forall n A, P n A.
Proof.
move=> P0 PS; elim=> [//|n IHn] A.
by rewrite -[n.+1]/(1 + n)%N in A *; rewrite -[A]hsubmxK; apply: PS.
Qed.

Lemma col_ind n (P : forall m, 'M[R]_(m, n) -> Type) :
    (forall A, P 0%N A) ->
    (forall m r A, P m A -> P (1 + m)%N (col_mx r A)) ->
  forall m A, P m A.
Proof.
move=> P0 PS; elim=> [//|m IHm] A.
by rewrite -[m.+1]/(1 + m)%N in A *; rewrite -[A]vsubmxK; apply: PS.
Qed.

Lemma mx_ind (P : forall m n, 'M[R]_(m, n) -> Type) :
    (forall m A, P m 0%N A) ->
    (forall n A, P 0%N n A) ->
    (forall m n x r c A, P m n A -> P (1 + m)%N (1 + n)%N (block_mx x r c A)) ->
  forall m n A, P m n A.
Proof.
move=> P0l P0r PS; elim=> [|m IHm] [|n] A; do ?by [apply: P0l|apply: P0r].
by rewrite -[A](@submxK 1 _ 1); apply: PS.
Qed.
Definition matrix_rect := mx_ind.
Definition matrix_rec := mx_ind.
Definition matrix_ind := mx_ind.

Lemma sqmx_ind (P : forall n, 'M[R]_n -> Type) :
    (forall A, P 0%N A) ->
    (forall n x r c A, P n A -> P (1 + n)%N (block_mx x r c A)) ->
  forall n A, P n A.
Proof.
by move=> P0 PS; elim=> [//|n IHn] A; rewrite -[A](@submxK 1 _ 1); apply: PS.
Qed.

Lemma ringmx_ind (P : forall n, 'M[R]_n.+1 -> Type) :
    (forall x, P 0%N x) ->
    (forall n x (r : 'rV_n.+1) (c : 'cV_n.+1) A,
       P n A -> P (1 + n)%N (block_mx x r c A)) ->
  forall n A, P n A.
Proof.
by move=> P0 PS; elim=> [//|n IHn] A; rewrite -[A](@submxK 1 _ 1); apply: PS.
Qed.

Lemma mxsub_ind
    (weight : forall m n, 'M[R]_(m, n) -> nat)
    (sub : forall m n m' n', ('I_m' -> 'I_m) -> ('I_n' -> 'I_n) -> Prop)
    (P : forall m n, 'M[R]_(m, n) -> Type) :
    (forall m n (A : 'M[R]_(m, n)),
      (forall m' n' f g, weight m' n' (mxsub f g A) < weight m n A ->
                         sub m n m' n' f g ->
                         P m' n' (mxsub f g A)) -> P m n A) ->
  forall m n A, P m n A.
Proof.
move=> Psub m n A; have [k] := ubnP (weight m n A).
elim: k => [//|k IHk] in m n A *.
rewrite ltnS => lt_A_k; apply: Psub => m' n' f g lt_A'_A ?.
by apply: IHk; apply: leq_trans lt_A_k.
Qed.

End Induction.

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

Lemma curry_mxvec_bij : {on 'I_(m * n), bijective (uncurry mxvec_index)}.
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
Notation colsub g := (mxsub id g).
Notation rowsub f := (mxsub f id).

Arguments eq_mxsub [R m n m' n' f] f' [g] g' _.
Arguments eq_rowsub [R m n m' f] f' _.
Arguments eq_colsub [R m n n' g] g' _.

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

Lemma map_mxsub m' n' g h : (@mxsub _ _ _  m' n' g h A)^f = mxsub g h A^f.
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

Section MultipleMapMatrix.
Context {R S T : Type} {m n : nat}.
Local Notation "M ^ phi" := (map_mx phi M).

Lemma map_mx_comp (f : R -> S) (g : S -> T)
  (M : 'M_(m, n)) : M ^ (g \o f) = (M ^ f) ^ g.
Proof. by apply/matrixP => i j; rewrite !mxE. Qed.

Lemma eq_in_map_mx (g f : R -> S) (M : 'M_(m, n)) :
  (forall i j, f (M i j) = g (M i j)) -> M ^ f = M ^ g.
Proof. by move=> fg; apply/matrixP => i j; rewrite !mxE. Qed.

Lemma eq_map_mx (g f : R -> S) : f =1 g ->
  forall (M : 'M_(m, n)), M ^ f = M ^ g.
Proof. by move=> eq_fg M; apply/eq_in_map_mx. Qed.

Lemma map_mx_id_in (f : R -> R) (M : 'M_(m, n)) :
  (forall i j, f (M i j) = M i j) -> M ^ f = M.
Proof. by move=> fM; apply/matrixP => i j; rewrite !mxE. Qed.

Lemma map_mx_id (f : R -> R) : f =1 id -> forall M : 'M_(m, n), M ^ f = M.
Proof. by move=> fid M; rewrite map_mx_id_in. Qed.

End MultipleMapMatrix.
Arguments eq_map_mx {R S m n} g [f].
Arguments eq_in_map_mx {R S m n} g [f M].
Arguments map_mx_id_in {R m n} [f M].
Arguments map_mx_id {R m n} [f].

(*****************************************************************************)
(********************* Matrix lifted laws *******************)
(*****************************************************************************)

Section Map2Matrix.
Context {R S T : Type} (f : R -> S -> T).

Fact map2_mx_key : unit. Proof. by []. Qed.
Definition map2_mx m n (A : 'M_(m, n)) (B : 'M_(m, n)) :=
  \matrix[map2_mx_key]_(i, j) f (A i j) (B i j).

Section OneMatrix.

Variables (m n : nat) (A : 'M[R]_(m, n)) (B : 'M[S]_(m, n)).

Lemma map2_trmx : (map2_mx A B)^T = map2_mx A^T B^T.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map2_const_mx a b :
  map2_mx (const_mx a) (const_mx b) = const_mx (f a b) :> 'M_(m, n).
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map2_row i : map2_mx (row i A) (row i B) = row i (map2_mx A B).
Proof. by apply/rowP=> j; rewrite !mxE. Qed.

Lemma map2_col j : map2_mx (col j A) (col j B) = col j (map2_mx A B).
Proof. by apply/colP=> i; rewrite !mxE. Qed.

Lemma map2_row' i0 : map2_mx (row' i0 A) (row' i0 B) = row' i0 (map2_mx A B).
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map2_col' j0 : map2_mx (col' j0 A) (col' j0 B) = col' j0 (map2_mx A B).
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map2_mxsub m' n' g h :
  map2_mx (@mxsub _ _ _  m' n' g h A) (@mxsub _ _ _  m' n' g h B) =
  mxsub g h (map2_mx A B).
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map2_row_perm s :
  map2_mx (row_perm s A) (row_perm s B) = row_perm s (map2_mx A B).
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map2_col_perm s :
  map2_mx (col_perm s A) (col_perm s B) = col_perm s (map2_mx A B).
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map2_xrow i1 i2 :
  map2_mx (xrow i1 i2 A) (xrow i1 i2 B) = xrow i1 i2 (map2_mx A B).
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map2_xcol j1 j2 :
  map2_mx (xcol j1 j2 A) (xcol j1 j2 B) = xcol j1 j2 (map2_mx A B).
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map2_castmx m' n' c :
  map2_mx (castmx c A) (castmx c B) = castmx c (map2_mx A B) :> 'M_(m', n').
Proof. by apply/matrixP=> i j; rewrite !(castmxE, mxE). Qed.

Lemma map2_conform_mx m' n' (A' : 'M_(m', n')) (B' : 'M_(m', n')) :
  map2_mx (conform_mx A' A) (conform_mx B' B) =
  conform_mx (map2_mx A' B') (map2_mx A B).
Proof.
move: A' B'; have [[<- <-] A' B'|] := eqVneq (m, n) (m', n').
  by rewrite !conform_mx_id.
by rewrite negb_and => neq_mn A' B'; rewrite !nonconform_mx.
Qed.

Lemma map2_mxvec : map2_mx (mxvec A) (mxvec B) = mxvec (map2_mx A B).
Proof. by apply/rowP=> i; rewrite !(castmxE, mxE). Qed.

Lemma map2_vec_mx (v : 'rV_(m * n)) (w : 'rV_(m * n)) :
  map2_mx (vec_mx v) (vec_mx w) = vec_mx (map2_mx v w).
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

End OneMatrix.

Section Block.

Variables m1 m2 n1 n2 : nat.
Variables (Aul : 'M[R]_(m1, n1)) (Aur : 'M[R]_(m1, n2)).
Variables (Adl : 'M[R]_(m2, n1)) (Adr : 'M[R]_(m2, n2)).
Variables (Bh : 'M[R]_(m1, n1 + n2)) (Bv : 'M[R]_(m1 + m2, n1)).
Variable B : 'M[R]_(m1 + m2, n1 + n2).
Variables (A'ul : 'M[S]_(m1, n1)) (A'ur : 'M[S]_(m1, n2)).
Variables (A'dl : 'M[S]_(m2, n1)) (A'dr : 'M[S]_(m2, n2)).
Variables (B'h : 'M[S]_(m1, n1 + n2)) (B'v : 'M[S]_(m1 + m2, n1)).
Variable B' : 'M[S]_(m1 + m2, n1 + n2).

Lemma map2_row_mx :
  map2_mx (row_mx Aul Aur) (row_mx A'ul A'ur) =
  row_mx (map2_mx Aul A'ul) (map2_mx Aur A'ur).
Proof. by apply/matrixP=> i j; do 2![rewrite !mxE //; case: split => ?]. Qed.

Lemma map2_col_mx :
  map2_mx (col_mx Aul Adl) (col_mx A'ul A'dl) =
  col_mx (map2_mx Aul A'ul) (map2_mx Adl A'dl).
Proof. by apply/matrixP=> i j; do 2![rewrite !mxE //; case: split => ?]. Qed.

Lemma map2_block_mx :
  map2_mx (block_mx Aul Aur Adl Adr) (block_mx A'ul A'ur A'dl A'dr) =
  block_mx
   (map2_mx Aul A'ul) (map2_mx Aur A'ur) (map2_mx Adl A'dl) (map2_mx Adr A'dr).
Proof. by apply/matrixP=> i j; do 3![rewrite !mxE //; case: split => ?]. Qed.

Lemma map2_lsubmx : map2_mx (lsubmx Bh) (lsubmx B'h) = lsubmx (map2_mx Bh B'h).
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map2_rsubmx : map2_mx (rsubmx Bh) (rsubmx B'h) = rsubmx (map2_mx Bh B'h).
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map2_usubmx : map2_mx (usubmx Bv) (usubmx B'v) = usubmx (map2_mx Bv B'v).
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map2_dsubmx : map2_mx (dsubmx Bv) (dsubmx B'v) = dsubmx (map2_mx Bv B'v).
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map2_ulsubmx : map2_mx (ulsubmx B) (ulsubmx B') = ulsubmx (map2_mx B B').
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map2_ursubmx : map2_mx (ursubmx B) (ursubmx B') = ursubmx (map2_mx B B').
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map2_dlsubmx : map2_mx (dlsubmx B) (dlsubmx B') = dlsubmx (map2_mx B B').
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map2_drsubmx : map2_mx (drsubmx B) (drsubmx B') = drsubmx (map2_mx B B').
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

End Block.

End Map2Matrix.

Section Map2Eq.

Context {R S T : Type} {m n : nat}.

Lemma eq_in_map2_mx (f g : R -> S -> T) (M : 'M[R]_(m, n)) (M' : 'M[S]_(m, n)) :
  (forall i j, f (M i j) (M' i j) = g (M i j) (M' i j)) ->
  map2_mx f M M' = map2_mx g M M'.
Proof. by move=> fg; apply/matrixP => i j; rewrite !mxE. Qed.

Lemma eq_map2_mx (f g : R -> S -> T) : f =2 g ->
  @map2_mx _ _ _ f m n =2 @map2_mx _ _ _ g m n.
Proof. by move=> eq_fg M M'; apply/eq_in_map2_mx. Qed.

Lemma map2_mx_left_in (f : R -> R -> R) (M : 'M_(m, n)) (M' : 'M_(m, n)) :
  (forall i j, f (M i j) (M' i j) = M i j) -> map2_mx f M M' = M.
Proof. by move=> fM; apply/matrixP => i j; rewrite !mxE. Qed.

Lemma map2_mx_left (f : R -> R -> R) : f =2 (fun x _ => x) ->
  forall (M : 'M_(m, n)) (M' : 'M_(m, n)), map2_mx f M M' = M.
Proof. by move=> fl M M'; rewrite map2_mx_left_in// =>i j; rewrite fl. Qed.

Lemma map2_mx_right_in (f : R -> R -> R) (M : 'M_(m, n)) (M' : 'M_(m, n)) :
  (forall i j, f (M i j) (M' i j) = M' i j) -> map2_mx f M M' = M'.
Proof. by move=> fM; apply/matrixP => i j; rewrite !mxE. Qed.

Lemma map2_mx_right (f : R -> R -> R) : f =2 (fun _ x => x) ->
  forall (M : 'M_(m, n)) (M' : 'M_(m, n)), map2_mx f M M' = M'.
Proof. by move=> fr M M'; rewrite map2_mx_right_in// =>i j; rewrite fr. Qed.

End Map2Eq.

Section MatrixLaws.

Context {T : Type} {m n : nat} {idm : T}.

Lemma map2_mxA {opm : Monoid.law idm} : associative (@map2_mx _ _ _ opm m n).
Proof. by move=> A B C; apply/matrixP=> i j; rewrite !mxE Monoid.mulmA. Qed.

Lemma map2_1mx {opm : Monoid.law idm} :
  left_id (const_mx idm) (@map2_mx _ _ _ opm m n).
Proof. by move=> A; apply/matrixP=> i j; rewrite !mxE Monoid.mul1m. Qed.

Lemma map2_mx1 {opm : Monoid.law idm} :
  right_id (const_mx idm) (@map2_mx _ _ _ opm m n).
Proof. by move=> A; apply/matrixP=> i j; rewrite !mxE Monoid.mulm1. Qed.

Canonical map2_mx_monoid {opm : Monoid.law idm} :=
  Monoid.Law (map2_mxA (opm:=opm)) map2_1mx map2_mx1.

Lemma map2_mxC {opm : Monoid.com_law idm} :
  commutative (@map2_mx _ _ _ opm m n).
Proof. by move=> A B; apply/matrixP=> i j; rewrite !mxE Monoid.mulmC. Qed.

Canonical map2_mx_comoid {opm : Monoid.com_law idm} :=
  Monoid.ComLaw (map2_mxC (opm:=opm)).

Lemma map2_0mx {opm : Monoid.mul_law idm} :
  left_zero (const_mx idm) (@map2_mx _ _ _ opm m n).
Proof. by move=> A; apply/matrixP=> i j; rewrite !mxE Monoid.mul0m. Qed.

Lemma map2_mx0 {opm : Monoid.mul_law idm} :
  right_zero (const_mx idm) (@map2_mx _ _ _ opm m n).
Proof. by move=> A; apply/matrixP=> i j; rewrite !mxE Monoid.mulm0. Qed.

Canonical map2_mx_muloid {opm : Monoid.mul_law idm} :=
  Monoid.MulLaw (map2_0mx (opm:=opm)) map2_mx0.

Lemma map2_mxDl {mul : T -> T -> T} {add : Monoid.add_law idm mul} :
  left_distributive (@map2_mx _ _ _ mul m n) (@map2_mx _ _ _ add m n).
Proof. by move=> A B C; apply/matrixP=> i j; rewrite !mxE Monoid.mulmDl. Qed.

Lemma map2_mxDr {mul : T -> T -> T} {add : Monoid.add_law idm mul} :
  right_distributive (@map2_mx _ _ _ mul m n) (@map2_mx _ _ _ add m n).
Proof. by move=> A B C; apply/matrixP=> i j; rewrite !mxE Monoid.mulmDr. Qed.

Canonical map2_mx_addoid {mul : T -> T -> T} {add : Monoid.add_law idm mul} :=
  Monoid.AddLaw (map2_mxDl (add:=add)) map2_mxDr.

End MatrixLaws.

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
Definition oppmx := @map_mx V V -%R m n.
Definition addmx := @map2_mx V V V +%R m n.

Definition addmxA : associative addmx := map2_mxA.
Definition addmxC : commutative addmx := map2_mxC.
Definition add0mx : left_id (const_mx 0) addmx := map2_1mx.

Lemma addNmx : left_inverse (const_mx 0) oppmx addmx.
Proof. by move=> A; apply/matrixP=> i j; rewrite !mxE addNr. Qed.

HB.instance Definition _ := GRing.IsZmodule.Build 'M[V]_(m, n)
  addmxA addmxC add0mx addNmx.

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
Canonical mxsub_additive m n m' n' f g := SwizzleAdd (@mxsub V m n m' n' f g).
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

Lemma trmx_eq0  m n (A : 'M_(m, n)) : (A^T == 0) = (A == 0).
Proof. by rewrite -trmx0 (inj_eq trmx_inj). Qed.

Lemma matrix_eq0 m n (A : 'M_(m, n)) :
  (A == 0) = [forall i, forall j, A i j == 0].
Proof.
apply/eqP/'forall_'forall_eqP => [-> i j|A_eq0]; first by rewrite !mxE.
by apply/matrixP => i j; rewrite A_eq0 !mxE.
Qed.

Lemma matrix0Pn m n (A : 'M_(m, n)) : reflect (exists i j, A i j != 0) (A != 0).
Proof.
by rewrite matrix_eq0; apply/(iffP forallPn) => -[i /forallPn]; exists i.
Qed.

Lemma rV0Pn n (v : 'rV_n) : reflect (exists i, v 0 i != 0) (v != 0).
Proof.
apply: (iffP (matrix0Pn _)) => [[i [j]]|[j]]; last by exists 0, j.
by rewrite ord1; exists j.
Qed.

Lemma cV0Pn n (v : 'cV_n) : reflect (exists i, v i 0 != 0) (v != 0).
Proof.
apply: (iffP (matrix0Pn _)) => [[i] [j]|[i]]; last by exists i, 0.
by rewrite ord1; exists i.
Qed.

Definition nz_row m n (A : 'M_(m, n)) :=
  oapp (fun i => row i A) 0 [pick i | row i A != 0].

Lemma nz_row_eq0 m n (A : 'M_(m, n)) : (nz_row A == 0) = (A == 0).
Proof.
rewrite /nz_row; symmetry; case: pickP => [i /= nzAi | Ai0].
  by rewrite (negPf nzAi); apply: contraTF nzAi => /eqP->; rewrite row0 eqxx.
by rewrite eqxx; apply/eqP/row_matrixP=> i; move/eqP: (Ai0 i) ->; rewrite row0.
Qed.

Definition is_diag_mx m n (A : 'M[V]_(m, n)) :=
  [forall i : 'I__, forall j : 'I__, (i != j :> nat) ==> (A i j == 0)].

Lemma is_diag_mxP m n (A : 'M[V]_(m, n)) :
  reflect (forall i j : 'I__, i != j :> nat -> A i j = 0) (is_diag_mx A).
Proof. by apply: (iffP 'forall_'forall_implyP) => /(_ _ _ _)/eqP. Qed.

Lemma mx0_is_diag m n : is_diag_mx (0 : 'M[V]_(m, n)).
Proof. by apply/is_diag_mxP => i j _; rewrite mxE. Qed.

Lemma mx11_is_diag (M : 'M_1) : is_diag_mx M.
Proof. by apply/is_diag_mxP => i j; rewrite !ord1 eqxx. Qed.

Definition is_trig_mx m n (A : 'M[V]_(m, n)) :=
  [forall i : 'I__, forall j : 'I__, (i < j)%N ==> (A i j == 0)].

Lemma is_trig_mxP m n (A : 'M[V]_(m, n)) :
  reflect (forall i j : 'I__, (i < j)%N -> A i j = 0) (is_trig_mx A).
Proof. by apply: (iffP 'forall_'forall_implyP) => /(_ _ _ _)/eqP. Qed.

Lemma is_diag_mx_is_trig m n (A : 'M[V]_(m, n)) : is_diag_mx A -> is_trig_mx A.
Proof.
by move=> /is_diag_mxP A_eq0; apply/is_trig_mxP=> i j lt_ij;
   rewrite A_eq0// ltn_eqF.
Qed.

Lemma mx0_is_trig m n : is_trig_mx (0 : 'M[V]_(m, n)).
Proof. by apply/is_trig_mxP => i j _; rewrite mxE. Qed.

Lemma mx11_is_trig (M : 'M_1) : is_trig_mx M.
Proof. by apply/is_trig_mxP => i j; rewrite !ord1 ltnn. Qed.

Lemma is_diag_mxEtrig m n (A : 'M[V]_(m, n)) :
  is_diag_mx A = is_trig_mx A && is_trig_mx A^T.
Proof.
apply/is_diag_mxP/andP => [Adiag|[/is_trig_mxP Atrig /is_trig_mxP ATtrig]].
  by split; apply/is_trig_mxP => i j lt_ij; rewrite ?mxE ?Adiag//;
     [rewrite ltn_eqF|rewrite gtn_eqF].
by move=> i j; case: ltngtP => // [/Atrig|/ATtrig]; rewrite ?mxE.
Qed.

Lemma is_diag_trmx  m n (A : 'M[V]_(m, n)) : is_diag_mx A^T = is_diag_mx A.
Proof. by rewrite !is_diag_mxEtrig trmxK andbC. Qed.

Lemma ursubmx_trig m1 m2 n1 n2 (A : 'M[V]_(m1 + m2, n1 + n2)) :
  m1 <= n1 -> is_trig_mx A -> ursubmx A = 0.
Proof.
move=> leq_m1_n1 /is_trig_mxP Atrig; apply/matrixP => i j.
by rewrite !mxE Atrig//= ltn_addr// (@leq_trans m1).
Qed.

Lemma dlsubmx_diag m1 m2 n1 n2 (A : 'M[V]_(m1 + m2, n1 + n2)) :
  n1 <= m1 -> is_diag_mx A -> dlsubmx A = 0.
Proof.
move=> leq_m2_n2 /is_diag_mxP Adiag; apply/matrixP => i j.
by rewrite !mxE Adiag// gtn_eqF//= ltn_addr// (@leq_trans n1).
Qed.

Lemma ulsubmx_trig m1 m2 n1 n2 (A : 'M[V]_(m1 + m2, n1 + n2)) :
  is_trig_mx A -> is_trig_mx (ulsubmx A).
Proof.
move=> /is_trig_mxP Atrig; apply/is_trig_mxP => i j lt_ij.
by rewrite !mxE Atrig.
Qed.

Lemma drsubmx_trig m1 m2 n1 n2 (A : 'M[V]_(m1 + m2, n1 + n2)) :
  m1 <= n1 -> is_trig_mx A -> is_trig_mx (drsubmx A).
Proof.
move=> leq_m1_n1 /is_trig_mxP Atrig; apply/is_trig_mxP => i j lt_ij.
by rewrite !mxE Atrig//= -addnS leq_add.
Qed.

Lemma ulsubmx_diag m1 m2 n1 n2 (A : 'M[V]_(m1 + m2, n1 + n2)) :
  is_diag_mx A -> is_diag_mx (ulsubmx A).
Proof.
rewrite !is_diag_mxEtrig trmx_ulsub.
by move=> /andP[/ulsubmx_trig-> /ulsubmx_trig->].
Qed.

Lemma drsubmx_diag m1 m2 n1 n2 (A : 'M[V]_(m1 + m2, n1 + n2)) :
  m1 = n1 -> is_diag_mx A -> is_diag_mx (drsubmx A).
Proof.
move=> eq_m1_n1 /is_diag_mxP Adiag; apply/is_diag_mxP => i j neq_ij.
by rewrite !mxE Adiag//= eq_m1_n1 eqn_add2l.
Qed.

Lemma is_trig_block_mx m1 m2 n1 n2 ul ur dl dr : m1 = n1 ->
  @is_trig_mx (m1 + m2) (n1 + n2) (block_mx ul ur dl dr) =
  [&& ur == 0, is_trig_mx ul & is_trig_mx dr].
Proof.
move=> eq_m1_n1; rewrite {}eq_m1_n1 in ul ur dl dr *.
apply/is_trig_mxP/and3P => [Atrig|]; last first.
  move=> [/eqP-> /is_trig_mxP ul_trig /is_trig_mxP dr_trig] i j; rewrite !mxE.
  do 2![case: split_ordP => ? ->; rewrite ?mxE//=] => lt_ij; rewrite ?ul_trig//.
    move: lt_ij; rewrite ltnNge -ltnS.
    by rewrite (leq_trans (ltn_ord _))// -addnS leq_addr.
  by rewrite dr_trig//; move: lt_ij; rewrite ltn_add2l.
split.
- apply/eqP/matrixP => i j; have := Atrig (lshift _ i) (rshift _ j).
  rewrite !mxE; case: split_ordP => k /eqP; rewrite eq_shift// ?mxE.
  case: split_ordP => l /eqP; rewrite eq_shift// ?mxE => /eqP-> /eqP<- <- //.
  by rewrite /= (leq_trans (ltn_ord _)) ?leq_addr.
- apply/is_trig_mxP => i j lt_ij; have := Atrig (lshift _ i) (lshift _ j).
  rewrite !mxE; case: split_ordP => k /eqP; rewrite eq_shift// ?mxE.
  by case: split_ordP => l /eqP; rewrite eq_shift// ?mxE => /eqP<- /eqP<- ->.
- apply/is_trig_mxP => i j lt_ij; have := Atrig (rshift _ i) (rshift _ j).
  rewrite !mxE; case: split_ordP => k /eqP; rewrite eq_shift// ?mxE.
  case: split_ordP => l /eqP; rewrite eq_shift// ?mxE => /eqP<- /eqP<- -> //.
  by rewrite /= ltn_add2l.
Qed.

Lemma trigmx_ind (P : forall m n, 'M_(m, n) -> Type) :
  (forall m, P m 0%N 0) ->
  (forall n, P 0%N n 0) ->
  (forall m n x c A, is_trig_mx A ->
    P m n A -> P (1 + m)%N (1 + n)%N (block_mx x 0 c A)) ->
  forall m n A, is_trig_mx A -> P m n A.
Proof.
move=> P0l P0r PS m n A; elim: A => {m n} [m|n|m n xx r c] A PA;
  do ?by rewrite (flatmx0, thinmx0); by [apply: P0l|apply: P0r].
by rewrite is_trig_block_mx => // /and3P[/eqP-> _ Atrig]; apply: PS (PA _).
Qed.

Lemma trigsqmx_ind (P : forall n, 'M[V]_n -> Type) : (P 0%N 0) ->
  (forall n x c A, is_trig_mx A -> P n A -> P (1 + n)%N (block_mx x 0 c A)) ->
  forall n A, is_trig_mx A -> P n A.
Proof.
move=> P0 PS n A; elim/sqmx_ind: A => {n} [|n x r c] A PA.
  by rewrite thinmx0; apply: P0.
by rewrite is_trig_block_mx => // /and3P[/eqP-> _ Atrig]; apply: PS (PA _).
Qed.

Lemma is_diag_block_mx m1 m2 n1 n2 ul ur dl dr : m1 = n1 ->
  @is_diag_mx (m1 + m2) (n1 + n2) (block_mx ul ur dl dr) =
  [&& ur == 0, dl == 0, is_diag_mx ul & is_diag_mx dr].
Proof.
move=> eq_m1_n1.
rewrite !is_diag_mxEtrig tr_block_mx !is_trig_block_mx// trmx_eq0.
by rewrite andbACA -!andbA; congr [&& _, _, _ & _]; rewrite andbCA.
Qed.

Lemma diagmx_ind (P : forall m n, 'M_(m, n) -> Type) :
  (forall m, P m 0%N 0) ->
  (forall n, P 0%N n 0) ->
  (forall m n x c A, is_diag_mx A ->
    P m n A -> P (1 + m)%N (1 + n)%N (block_mx x 0 c A)) ->
  forall m n A, is_diag_mx A -> P m n A.
Proof.
move=> P0l P0r PS m n A Adiag; have Atrig := is_diag_mx_is_trig Adiag.
elim/trigmx_ind: Atrig Adiag => // {}m {}n r c {}A _ PA.
rewrite is_diag_block_mx => // /and4P[_ /eqP-> _ Adiag].
exact: PS (PA _).
Qed.

Lemma diagsqmx_ind (P : forall n, 'M[V]_n -> Type) :
    (P 0%N 0) ->
  (forall n x c A, is_diag_mx A -> P n A -> P (1 + n)%N (block_mx x 0 c A)) ->
  forall n A, is_diag_mx A -> P n A.
Proof.
move=> P0 PS n A; elim/sqmx_ind: A => [|{}n x r c] A PA.
  by rewrite thinmx0; apply: P0.
rewrite is_diag_block_mx => // /and4P[/eqP-> /eqP-> _ Adiag].
exact: PS (PA _).
Qed.

(* Diagonal matrices *)

Fact diag_mx_key : unit. Proof. by []. Qed.
Definition diag_mx n (d : 'rV[V]_n) :=
  \matrix[diag_mx_key]_(i, j) (d 0 i *+ (i == j)).

Lemma tr_diag_mx n (d : 'rV_n) : (diag_mx d)^T = diag_mx d.
Proof. by apply/matrixP=> i j /[!mxE]; case: eqVneq => // ->. Qed.

Lemma diag_mx_is_additive n : additive (@diag_mx n).
Proof.
by move=>A B; apply/matrixP=>i j; rewrite !mxE mulrnBl.
Qed.
Canonical diag_mx_additive n := Additive (@diag_mx_is_additive n).

Lemma diag_mx_row m n (l : 'rV_n) (r : 'rV_m) :
  diag_mx (row_mx l r) = block_mx (diag_mx l) 0 0 (diag_mx r).
Proof.
apply/matrixP => i j.
by do ?[rewrite !mxE; case: split_ordP => ? ->]; rewrite mxE eq_shift.
Qed.

Lemma diag_mxP n (A : 'M[V]_n) :
  reflect (exists d : 'rV_n, A = diag_mx d) (is_diag_mx A).
Proof.
apply: (iffP (is_diag_mxP A)) => [Adiag|[d ->] i j neq_ij]; last first.
  by rewrite !mxE -val_eqE (negPf neq_ij).
exists (\row_i A i i); apply/matrixP => i j; rewrite !mxE.
by case: (altP (i =P j)) => [->|/Adiag->].
Qed.

Lemma diag_mx_is_diag n (r : 'rV[V]_n) : is_diag_mx (diag_mx r).
Proof. by apply/diag_mxP; exists r. Qed.

Lemma diag_mx_is_trig n (r : 'rV[V]_n) : is_trig_mx (diag_mx r).
Proof. exact/is_diag_mx_is_trig/diag_mx_is_diag. Qed.

(* Scalar matrix : a diagonal matrix with a constant on the diagonal *)
Section ScalarMx.

Variable n : nat.

Fact scalar_mx_key : unit. Proof. by []. Qed.
Definition scalar_mx x : 'M[V]_n :=
  \matrix[scalar_mx_key]_(i , j) (x *+ (i == j)).
Notation "x %:M" := (scalar_mx x) : ring_scope.

Lemma diag_const_mx a : diag_mx (const_mx a) = a%:M :> 'M_n.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma tr_scalar_mx a : (a%:M)^T = a%:M.
Proof. by apply/matrixP=> i j; rewrite !mxE eq_sym. Qed.

Lemma scalar_mx_is_additive : additive scalar_mx.
Proof. by move=> a b; rewrite -!diag_const_mx !raddfB. Qed.
Canonical scalar_mx_additive := Additive scalar_mx_is_additive.

Definition is_scalar_mx (A : 'M[V]_n) :=
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

Lemma scalar_mx_is_diag a : is_diag_mx (a%:M).
Proof. by rewrite -diag_const_mx diag_mx_is_diag. Qed.

Lemma is_scalar_mx_is_diag A : is_scalar_mx A -> is_diag_mx A.
Proof. by move=> /is_scalar_mxP[a ->]; apply: scalar_mx_is_diag. Qed.

Lemma scalar_mx_is_trig a : is_trig_mx (a%:M).
Proof. by rewrite is_diag_mx_is_trig// scalar_mx_is_diag. Qed.

Lemma is_scalar_mx_is_trig A : is_scalar_mx A -> is_trig_mx A.
Proof. by move=> /is_scalar_mx_is_diag /is_diag_mx_is_trig. Qed.

End ScalarMx.

Notation "x %:M" := (scalar_mx _ x) : ring_scope.

Lemma mx11_scalar (A : 'M_1) : A = (A 0 0)%:M.
Proof. by apply/rowP=> j; rewrite ord1 mxE. Qed.

Lemma scalar_mx_block n1 n2 a : a%:M = block_mx a%:M 0 0 a%:M :> 'M_(n1 + n2).
Proof.
apply/matrixP=> i j; rewrite !mxE.
by do 2![case: split_ordP => ? ->; rewrite !mxE]; rewrite ?eq_shift.
Qed.

(* The trace. *)
Section Trace.

Variable n : nat.
(*TODO: undergeneralize to monoid *)
Definition mxtrace (A : 'M[V]_n) := \sum_i A i i.
Local Notation "'\tr' A" := (mxtrace A) : ring_scope.

Lemma mxtrace_tr A : \tr A^T = \tr A.
Proof. by apply: eq_bigr=> i _; rewrite mxE. Qed.

Lemma mxtrace_is_additive : additive mxtrace.
Proof.
move=>A B; rewrite -sumrN -big_split /=.
by apply: eq_bigr=> i _; rewrite !mxE.
Qed.
Canonical mxtrace_additive := Additive mxtrace_is_additive.

Lemma mxtrace0 : \tr 0 = 0. Proof. exact: raddf0. Qed.
Lemma mxtraceD A B : \tr (A + B) = \tr A + \tr B. Proof. exact: raddfD. Qed.

Lemma mxtrace_diag D : \tr (diag_mx D) = \sum_j D 0 j.
Proof. by apply: eq_bigr => j _; rewrite mxE eqxx. Qed.

Lemma mxtrace_scalar a : \tr a%:M = a *+ n.
Proof.
rewrite -diag_const_mx mxtrace_diag; under eq_bigr do rewrite mxE.
by rewrite sumr_const card_ord.
Qed.

End Trace.
Local Notation "'\tr' A" := (mxtrace A) : ring_scope.

Lemma trace_mx11 (A : 'M_1) : \tr A = A 0 0.
Proof. by rewrite {1}[A]mx11_scalar mxtrace_scalar. Qed.

Lemma mxtrace_block n1 n2 (Aul : 'M_n1) Aur Adl (Adr : 'M_n2) :
  \tr (block_mx Aul Aur Adl Adr) = \tr Aul + \tr Adr.
Proof.
rewrite /(\tr _) big_split_ord /=.
by congr (_ + _); under eq_bigr do rewrite (block_mxEul, block_mxEdr).
Qed.

End MatrixZmodule.

Arguments is_diag_mx {V m n}.
Arguments is_diag_mxP {V m n A}.
Arguments is_trig_mx {V m n}.
Arguments is_trig_mxP {V m n A}.
Arguments scalar_mx {V n}.
Arguments is_scalar_mxP {V n A}.

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

Lemma map_mxB A B : (A - B)^f = A^f - B^f.
Proof. by rewrite map_mxD map_mxN. Qed.

Definition map_mx_sum := big_morph _ map_mxD map_mx0.

Canonical map_mx_additive := Additive map_mxB.

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

HB.instance Definition _ := GRing.Zmodule_IsLmodule.Build R 'M[R]_(m, n)
  scalemxA scale1mx scalemxDr scalemxDl.

Lemma scalemx_const a b : a *: const_mx b = const_mx (a * b).
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma matrix_sum_delta A :
  A = \sum_(i < m) \sum_(j < n) A i j *: delta_mx i j.
Proof.
apply/matrixP=> i j.
rewrite summxE (bigD1_ord i) // summxE (bigD1_ord j) //= !mxE !eqxx mulr1.
rewrite !big1 ?addr0 //= => [i' | j'] _.
  by rewrite summxE big1// => j' _; rewrite !mxE eq_liftF mulr0.
by rewrite !mxE eqxx eq_liftF mulr0.
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
Canonical mxsub_linear m n m' n' f g := SwizzleLin (@mxsub R m n m' n' f g).
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

Lemma diag_mx_is_linear n : linear (@diag_mx R n).
Proof.
by move=> a A B; apply/matrixP=> i j; rewrite !mxE mulrnAr mulrnDl.
Qed.
Canonical diag_mx_linear n := Linear (@diag_mx_is_linear n).

Lemma diag_mx_sum_delta n (d : 'rV_n) :
  diag_mx d = \sum_i d 0 i *: delta_mx i i.
Proof.
apply/matrixP=> i j; rewrite summxE (bigD1_ord i) //= !mxE eqxx /=.
by rewrite eq_sym mulr_natr big1 ?addr0 // => i'; rewrite !mxE eq_liftF mulr0.
Qed.

Lemma row_diag_mx n (d : 'rV_n) i :
  row i (diag_mx d) = d 0 i *: delta_mx 0 i.
Proof. by apply/rowP => j; rewrite !mxE eqxx eq_sym mulr_natr. Qed.

(* Scalar matrix *)

Notation "x %:M" := (scalar_mx x) : ring_scope.

Lemma trmx1 n : (1%:M)^T = 1%:M :> 'M[R]_n. Proof. exact: tr_scalar_mx. Qed.

Lemma scale_scalar_mx n a1 a2 : a1 *: a2%:M = (a1 * a2)%:M :> 'M_n.
Proof. by apply/matrixP=> i j; rewrite !mxE mulrnAr. Qed.

Lemma scalemx1 n a : a *: 1%:M = a%:M :> 'M_n.
Proof. by rewrite scale_scalar_mx mulr1. Qed.

Lemma scalar_mx_sum_delta n a : a%:M = \sum_i a *: delta_mx i i :> 'M_n.
Proof.
by rewrite -diag_const_mx diag_mx_sum_delta; under eq_bigr do rewrite mxE.
Qed.

Lemma mx1_sum_delta n : 1%:M = \sum_i delta_mx i i :> 'M_n.
Proof. by rewrite [1%:M]scalar_mx_sum_delta -scaler_sumr scale1r. Qed.

Lemma row1 n i : row i (1%:M : 'M_n) = delta_mx 0 i.
Proof. by apply/rowP=> j; rewrite !mxE eq_sym. Qed.

Lemma col1 n i : col i (1%:M : 'M_n) = delta_mx i 0.
Proof. by apply/colP => j; rewrite !mxE eqxx andbT. Qed.

(* Matrix multiplication using bigops. *)
Fact mulmx_key : unit. Proof. by []. Qed.
Definition mulmx {m n p} (A : 'M_(m, n)) (B : 'M_(n, p)) : 'M[R]_(m, p) :=
  \matrix[mulmx_key]_(i, k) \sum_j (A i j * B j k).

Local Notation "A *m B" := (mulmx A B) : ring_scope.

Lemma mulmxA m n p q (A : 'M_(m, n)) (B : 'M_(n, p)) (C : 'M_(p, q)) :
  A *m (B *m C) = A *m B *m C.
Proof.
apply/matrixP=> i l /[!mxE]; under eq_bigr do rewrite mxE big_distrr/=.
rewrite exchange_big; apply: eq_bigr => j _; rewrite mxE big_distrl /=.
by under eq_bigr do rewrite mulrA.
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
by apply/matrixP=> i k; rewrite !mxE -sumrN; under eq_bigr do rewrite mxE mulrN.
Qed.

Lemma mulNmx m n p (A : 'M_(m, n)) (B : 'M_(n, p)) : - A *m B = - (A *m B).
Proof.
by apply/matrixP=> i k; rewrite !mxE -sumrN; under eq_bigr do rewrite mxE mulNr.
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
apply/rowP=> j; rewrite !mxE (bigD1_ord i) //= mxE !eqxx mul1r.
by rewrite big1 ?addr0 // => i'; rewrite mxE /= lift_eqF mul0r.
Qed.

Lemma colE m n i (A : 'M_(m, n)) : col i A = A *m delta_mx i 0.
Proof.
apply/colP=> j; rewrite !mxE (bigD1_ord i) //= mxE !eqxx mulr1.
by rewrite big1 ?addr0 // => i'; rewrite mxE /= lift_eqF mulr0.
Qed.

Lemma mul_rVP m n A B :((@mulmx 1 m n)^~ A =1 mulmx^~ B) <-> (A = B).
Proof. by split=> [eqAB|->//]; apply/row_matrixP => i; rewrite !rowE eqAB. Qed.

Lemma row_mul m n p (i : 'I_m) A (B : 'M_(n, p)) :
  row i (A *m B) = row i A *m B.
Proof. by rewrite !rowE mulmxA. Qed.

Lemma mulmx_sum_row m n (u : 'rV_m) (A : 'M_(m, n)) :
  u *m A = \sum_i u 0 i *: row i A.
Proof. by apply/rowP => j /[!(mxE, summxE)]; apply: eq_bigr => i _ /[!mxE]. Qed.

Lemma mxsub_mul m n m' n' p f g (A : 'M_(m, p)) (B : 'M_(p, n)) :
  mxsub f g (A *m B) = rowsub f A *m colsub g B :> 'M_(m', n').
Proof. by split_mxE; under [RHS]eq_bigr do rewrite !mxE. Qed.

Lemma mul_rowsub_mx m n m' p f (A : 'M_(m, p)) (B : 'M_(p, n)) :
  rowsub f A *m B = rowsub f (A *m B) :> 'M_(m', n).
Proof. by rewrite mxsub_mul mxsub_id. Qed.

Lemma mulmx_colsub m n n' p g (A : 'M_(m, p)) (B : 'M_(p, n)) :
  A *m colsub g B = colsub g (A *m B) :> 'M_(m, n').
Proof. by rewrite mxsub_mul mxsub_id. Qed.

Lemma mul_delta_mx_cond m n p (j1 j2 : 'I_n) (i1 : 'I_m) (k2 : 'I_p) :
  delta_mx i1 j1 *m delta_mx j2 k2 = delta_mx i1 k2 *+ (j1 == j2).
Proof.
apply/matrixP => i k; rewrite !mxE (bigD1_ord j1) //=.
rewrite mulmxnE !mxE !eqxx andbT -natrM -mulrnA !mulnb !andbA andbAC.
by rewrite big1 ?addr0 // => j; rewrite !mxE andbC -natrM lift_eqF.
Qed.

Lemma mul_delta_mx m n p (j : 'I_n) (i : 'I_m) (k : 'I_p) :
  delta_mx i j *m delta_mx j k = delta_mx i k.
Proof. by rewrite mul_delta_mx_cond eqxx. Qed.

Lemma mul_delta_mx_0 m n p (j1 j2 : 'I_n) (i1 : 'I_m) (k2 : 'I_p) :
  j1 != j2 -> delta_mx i1 j1 *m delta_mx j2 k2 = 0.
Proof. by rewrite mul_delta_mx_cond => /negPf->. Qed.

Lemma mul_diag_mx m n d (A : 'M_(m, n)) :
  diag_mx d *m A = \matrix_(i, j) (d 0 i * A i j).
Proof.
apply/matrixP=> i j; rewrite !mxE (bigD1 i) //= mxE eqxx big1 ?addr0 // => i'.
by rewrite mxE eq_sym mulrnAl => /negPf->.
Qed.

Lemma mul_mx_diag m n (A : 'M_(m, n)) d :
  A *m diag_mx d = \matrix_(i, j) (A i j * d 0 j).
Proof.
apply/matrixP=> i j; rewrite !mxE (bigD1 j) //= mxE eqxx big1 ?addr0 // => i'.
by rewrite mxE eq_sym mulrnAr; move/negPf->.
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
by rewrite -diag_const_mx mul_mx_diag; apply/matrixP=> i j; rewrite !mxE mulr1.
Qed.

Lemma rowsubE m m' n f (A : 'M_(m, n)) :
   rowsub f A = rowsub f 1%:M *m A :> 'M_(m', n).
Proof. by rewrite mul_rowsub_mx mul1mx. Qed.

(* mulmx and col_perm, row_perm, xcol, xrow *)

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

Definition perm_mx n s : 'M_n := row_perm s (1%:M : 'M[R]_n).

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

Lemma perm_mxEsub n s : @perm_mx n s = rowsub s 1%:M.
Proof. by rewrite /perm_mx row_permEsub. Qed.

Lemma tperm_mxEsub n i1 i2 : @tperm_mx n i1 i2 = rowsub (tperm i1 i2) 1%:M.
Proof. by rewrite /tperm_mx perm_mxEsub. Qed.

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
by case: split_ordP => j' ->; rewrite !mxE// (val_eqE (lshift n i)) eq_shift.
Qed.

Lemma pid_mx_col m r : pid_mx r = col_mx 1%:M 0 :> 'M_(r + m, r).
Proof.
apply/matrixP=> i j; rewrite !mxE andbC.
by case: split_ordP => ? ->; rewrite !mxE//.
Qed.

Lemma pid_mx_block m n r : pid_mx r = block_mx 1%:M 0 0 0 :> 'M_(r + m, r + n).
Proof.
apply/matrixP=> i j; rewrite !mxE row_mx0 andbC.
do ![case: split_ordP => ? -> /[!mxE]//].
by rewrite (val_eqE (lshift n _)) eq_shift.
Qed.

Lemma tr_pid_mx m n r : (pid_mx r)^T = pid_mx r :> 'M_(n, m).
Proof. by apply/matrixP=> i j /[!mxE]; case: eqVneq => // ->. Qed.

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
by rewrite -val_eqE /= !mxE eq_sym -natrM => /negPf->.
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

Lemma pid_mxErow m n (le_mn : m <= n) :
  pid_mx m = rowsub (widen_ord le_mn) 1%:M.
Proof. by apply/matrixP=> i j; rewrite !mxE -!val_eqE/= ltn_ord andbT. Qed.

Lemma pid_mxEcol m n (le_mn : m <= n) :
  pid_mx n = colsub (widen_ord le_mn) 1%:M.
Proof. by apply/matrixP=> i j; rewrite !mxE -!val_eqE/= ltn_ord andbT. Qed.

(* Block products; we cover all 1 x 2, 2 x 1, and 2 x 2 block products. *)
Lemma mul_mx_row m n p1 p2 (A : 'M_(m, n)) (Bl : 'M_(n, p1)) (Br : 'M_(n, p2)) :
  A *m row_mx Bl Br = row_mx (A *m Bl) (A *m Br).
Proof.
apply/matrixP=> i k; rewrite !mxE.
by case defk: (split k) => /[!mxE]; under eq_bigr do rewrite mxE defk.
Qed.

Lemma mul_col_mx m1 m2 n p (Au : 'M_(m1, n)) (Ad : 'M_(m2, n)) (B : 'M_(n, p)) :
  col_mx Au Ad *m B = col_mx (Au *m B) (Ad *m B).
Proof.
apply/matrixP=> i k; rewrite !mxE.
by case defi: (split i) => /[!mxE]; under eq_bigr do rewrite mxE defi.
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

Lemma mulmx_lsub m n p k (A : 'M_(m, n)) (B : 'M_(n, p + k)) :
  A *m lsubmx B = lsubmx (A *m B).
Proof. by rewrite !lsubmxEsub mulmx_colsub. Qed.

Lemma mulmx_rsub m n p k (A : 'M_(m, n)) (B : 'M_(n, p + k)) :
  A *m rsubmx B = rsubmx (A *m B).
Proof. by rewrite !rsubmxEsub mulmx_colsub. Qed.

Lemma mul_usub_mx m k n p (A : 'M_(m + k, n)) (B : 'M_(n, p)) :
  usubmx A *m B = usubmx (A *m B).
Proof. by rewrite !usubmxEsub mul_rowsub_mx. Qed.

Lemma mul_dsub_mx m k n p (A : 'M_(m + k, n)) (B : 'M_(n, p)) :
  dsubmx A *m B = dsubmx (A *m B).
Proof. by rewrite !dsubmxEsub mul_rowsub_mx. Qed.

(* Correspondence between matrices and linear function on row vectors. *)
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

(* Correspondence between matrices and linear function on matrices. *)
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

Definition mulmxr B A := mulmx A B.
Arguments mulmxr B A /.

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
Arguments mulmxr {_ _ _} B A /.

(* The trace *)

Section Trace.

Variable n : nat.
Local Notation "'\tr' A" := (mxtrace A) : ring_scope.

Lemma mxtrace_is_scalar : scalar (@mxtrace R n).
Proof.
move=> a A B; rewrite mulr_sumr -big_split /=.
by apply: eq_bigr=> i _; rewrite !mxE.
Qed.

Canonical mxtrace_linear := Linear mxtrace_is_scalar.

Lemma mxtraceZ a (A : 'M_n) : \tr (a *: A) = a * \tr A.
Proof. exact: scalarZ. Qed.

Lemma mxtrace1 : \tr (1%:M : 'M[R]_n) = n%:R. Proof. exact: mxtrace_scalar. Qed.

End Trace.

(* The matrix ring structure requires a strutural condition (dimension of the *)
(* form n.+1) to satisfy the nontriviality condition we have imposed.         *)
Section MatrixRing.

Variable n' : nat.
Local Notation n := n'.+1.

Lemma matrix_nonzero1 : 1%:M != 0 :> 'M[R]_n.
Proof. by apply/eqP=> /matrixP/(_ 0 0)/eqP; rewrite !mxE oner_eq0. Qed.

HB.instance Definition _ := GRing.Zmodule_IsRing.Build 'M[R]_n (@mulmxA n n n n)
  (@mul1mx n n) (@mulmx1 n n) (@mulmxDl n n n) (@mulmxDr n n n) matrix_nonzero1.
HB.instance Definition _ := GRing.Lmodule_IsLalgebra.Build R 'M[R]_n
  (@scalemxAl n n n).

Lemma mulmxE : mulmx = *%R. Proof. by []. Qed.
Lemma idmxE : 1%:M = 1 :> 'M_n. Proof. by []. Qed.

Lemma scalar_mx_is_multiplicative : multiplicative (@scalar_mx R n).
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

Lemma exp_block_diag_mx m n (A: 'M_m.+1) (B : 'M_n.+1) k :
  (block_mx A 0 0 B) ^+ k = block_mx (A ^+ k) 0 0 (B ^+ k).
Proof.
elim: k=> [|k IHk]; first by rewrite !expr0 -scalar_mx_block.
rewrite !exprS IHk [LHS](mulmx_block A _ _ _ (A ^+ k)).
by rewrite !mulmx0 !mul0mx !add0r !addr0.
Qed.

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
Arguments perm_mx {R n}.
Arguments tperm_mx {R n}.
Arguments pid_mx {R m n}.
Arguments copid_mx {R n}.
Arguments lin_mulmxr {R m n p}.
Prenex Implicits diag_mx is_scalar_mx.
Prenex Implicits mulmx mxtrace determinant cofactor adjugate.

Arguments mul_delta_mx {R m n p}.

#[global] Hint Extern 0 (is_true (is_diag_mx (scalar_mx _))) =>
  apply: scalar_mx_is_diag : core.
#[global] Hint Extern 0 (is_true (is_trig_mx (scalar_mx _))) =>
  apply: scalar_mx_is_trig : core.
#[global] Hint Extern 0 (is_true (is_diag_mx (diag_mx _))) =>
  apply: diag_mx_is_diag : core.
#[global] Hint Extern 0 (is_true (is_trig_mx (diag_mx _))) =>
  apply: diag_mx_is_trig : core.

Notation "a %:M" := (scalar_mx a) : ring_scope.
Notation "A *m B" := (mulmx A B) : ring_scope.
Arguments mulmxr {_ _ _ _} B A /.
Notation "\tr A" := (mxtrace A) : ring_scope.
Notation "'\det' A" := (determinant A) : ring_scope.
Notation "'\adj' A" := (adjugate A) : ring_scope.

(* Non-commutative transpose requires multiplication in the converse ring.   *)
Lemma trmx_mul_rev (R : ringType) m n p (A : 'M[R]_(m, n)) (B : 'M[R]_(n, p)) :
  (A *m B)^T = (B : 'M[R^c]_(n, p))^T *m (A : 'M[R^c]_(m, n))^T.
Proof.
by apply/matrixP=> k i /[!mxE]; apply: eq_bigr => j _ /[!mxE].
Qed.

HB.instance Definition _ (M : countZmodType) m n :=
  [Countable of 'M[M]_(m, n) by <:].
HB.instance Definition _ (R : countRingType) n :=
  [Countable of 'M[R]_n.+1 by <:].

Section FinZmodMatrix.
Variables (V : finZmodType) (m n : nat).
Local Notation MV := 'M[V]_(m, n).

HB.instance Definition _ := [Finite of MV by <:].

#[compress_coercions]
HB.instance Definition _ := [finGroupMixin of MV for +%R].

End FinZmodMatrix.

#[compress_coercions]
HB.instance Definition _ (R : finRingType) (m n : nat) :=
  FinRing.Zmodule.on 'M[R]_(m, n).

#[compress_coercions]
HB.instance Definition _ (R : finRingType) n :=
  [Finite of 'M[R]_n.+1 by <:].

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
Proof. by rewrite map_mxB map_mx1 map_pid_mx. Qed.

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

Section CommMx.
(***********************************************************************)
(************* Commutation property specialized to 'M[R]_n *************)
(***********************************************************************)
(* GRing.comm is bound to (non trivial) rings, and matrices form a     *)
(* (non trivial) ring only when they are square and of manifestly      *)
(* positive size. However during proofs in endomorphism reduction, we  *)
(* take restrictions, which are matrices of size #|V| (with V a matrix *)
(* space) and it becomes cumbersome to state commutation between       *)
(* restrictions, unless we relax the setting, and this relaxation      *)
(* corresponds to comm_mx A B := A *m B = B *m A.                      *)
(* As witnessed by comm_mxE, when A and B have type 'M_n.+1,           *)
(*   comm_mx A B is convertible to GRing.comm A B.                     *)
(* The boolean version comm_mxb is designed to be used with seq.allrel *)
(***********************************************************************)

Context {R : ringType} {n : nat}.
Implicit Types (f g p : 'M[R]_n) (fs : seq 'M[R]_n) (d : 'rV[R]_n) (I : Type).

Definition comm_mx  f g : Prop := f *m g =  g *m f.
Definition comm_mxb f g : bool := f *m g == g *m f.

Lemma comm_mx_sym f g : comm_mx f g -> comm_mx g f.
Proof. by rewrite /comm_mx. Qed.

Lemma comm_mx_refl f : comm_mx f f. Proof. by []. Qed.

Lemma comm_mx0 f : comm_mx f 0. Proof. by rewrite /comm_mx mulmx0 mul0mx. Qed.
Lemma comm0mx f : comm_mx 0 f. Proof. by rewrite /comm_mx mulmx0 mul0mx. Qed.

Lemma comm_mx1 f : comm_mx f 1%:M.
Proof. by rewrite /comm_mx mulmx1 mul1mx. Qed.

Lemma comm1mx f : comm_mx 1%:M f.
Proof. by rewrite /comm_mx mulmx1 mul1mx. Qed.

Hint Resolve comm_mx0 comm0mx comm_mx1 comm1mx : core.

Lemma comm_mxN f g : comm_mx f g -> comm_mx f (- g).
Proof. by rewrite /comm_mx mulmxN mulNmx => ->. Qed.

Lemma comm_mxN1 f : comm_mx f (- 1%:M). Proof. exact/comm_mxN/comm_mx1. Qed.

Lemma comm_mxD f g g' : comm_mx f g -> comm_mx f g' -> comm_mx f (g + g').
Proof. by rewrite /comm_mx mulmxDl mulmxDr => -> ->. Qed.

Lemma comm_mxB f g g' : comm_mx f g -> comm_mx f g' -> comm_mx f (g - g').
Proof. by move=> fg fg'; apply/comm_mxD => //; apply/comm_mxN. Qed.

Lemma comm_mxM f g g' : comm_mx f g -> comm_mx f g' -> comm_mx f (g *m g').
Proof. by rewrite /comm_mx mulmxA => ->; rewrite -!mulmxA => ->. Qed.

Lemma comm_mx_sum I (s : seq I) (P : pred I) (F : I -> 'M[R]_n) (f : 'M[R]_n) :
  (forall i : I, P i -> comm_mx f (F i)) -> comm_mx f (\sum_(i <- s | P i) F i).
Proof. by move=> comm_mxfF; elim/big_ind: _ => // g h; apply: comm_mxD. Qed.

Lemma comm_mxP f g : reflect (comm_mx f g) (comm_mxb f g).
Proof. exact: eqP. Qed.

Notation all_comm_mx fs := (all2rel comm_mxb fs).

Lemma all_comm_mxP fs :
  reflect {in fs &, forall f g, f *m g = g *m f} (all_comm_mx fs).
Proof. by apply: (iffP allrelP) => fsP ? ? ? ?; apply/eqP/fsP. Qed.

Lemma all_comm_mx1 f : all_comm_mx [:: f].
Proof. by rewrite /comm_mxb all2rel1. Qed.

Lemma all_comm_mx2P f g : reflect (f *m g = g *m f) (all_comm_mx [:: f; g]).
Proof. by rewrite /comm_mxb /= all2rel2 ?eqxx //; exact: eqP. Qed.

Lemma all_comm_mx_cons f fs :
  all_comm_mx (f :: fs) = all (comm_mxb f) fs && all_comm_mx fs.
Proof. by rewrite /comm_mxb /= all2rel_cons //= eqxx. Qed.

End CommMx.
Notation all_comm_mx := (allrel comm_mxb).

Lemma comm_mxE (R : ringType) (n : nat) : @comm_mx R n.+1 = @GRing.comm _.
Proof. by []. Qed.

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

HB.instance Definition _ := GRing.Lalgebra_IsAlgebra.Build R 'M[R]_n
  (fun k => scalemxAr k).

End MatrixAlgType.

Lemma diag_mxC n (d e : 'rV[R]_n) :
  diag_mx d *m diag_mx e = diag_mx e *m diag_mx d.
Proof.
by rewrite !mulmx_diag; congr (diag_mx _); apply/rowP=> i; rewrite !mxE mulrC.
Qed.

Lemma diag_mx_comm n (d e : 'rV[R]_n) : comm_mx (diag_mx d) (diag_mx e).
Proof. exact: diag_mxC. Qed.

Lemma scalar_mxC m n a (A : 'M[R]_(m, n)) : A *m a%:M = a%:M *m A.
Proof.
by apply: trmx_inj; rewrite trmx_mul tr_scalar_mx !mul_scalar_mx linearZ.
Qed.

Lemma mul_mx_scalar m n a (A : 'M[R]_(m, n)) : A *m a%:M = a *: A.
Proof. by rewrite scalar_mxC mul_scalar_mx. Qed.

Lemma comm_mx_scalar n a (A : 'M[R]_n) : comm_mx A a%:M.
Proof. by rewrite /comm_mx mul_mx_scalar mul_scalar_mx. Qed.

Lemma comm_scalar_mx n a (A : 'M[R]_n) : comm_mx a%:M A.
Proof. exact/comm_mx_sym/comm_mx_scalar. Qed.

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
  by rewrite (bigD1 i) // mulrCA /= !mxE (negPf ist) mul0r.
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

Lemma det_mx11  (M : 'M[R]_1) : \det M = M 0 0.
Proof. by rewrite {1}[M]mx11_scalar det_scalar. Qed.

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
rewrite -signr_odd mulrA -signr_addb oddD -odd_lift_perm; congr (_ * _).
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
by under eq_bigr do rewrite cofactor_tr mxE.
Qed.

Lemma trmx_adj n (A : 'M[R]_n) : (\adj A)^T = \adj A^T.
Proof. by apply/matrixP=> i j; rewrite !mxE cofactor_tr. Qed.

Lemma adjZ n a (A : 'M[R]_n) : \adj (a *: A) = a^+n.-1 *: \adj A.
Proof. by apply/matrixP=> i j; rewrite !mxE cofactorZ. Qed.

(* Cramer Rule : adjugate on the left *)
Lemma mul_mx_adj n (A : 'M[R]_n) : A *m \adj A = (\det A)%:M.
Proof.
apply/matrixP=> i1 i2 /[!mxE]; have [->|Di] := eqVneq.
  rewrite (expand_det_row _ i2) //=.
  by apply: eq_bigr => j _; congr (_ * _); rewrite mxE.
pose B := \matrix_(i, j) (if i == i2 then A i1 j else A i j).
have EBi12: B i1 =1 B i2 by move=> j; rewrite /= !mxE eqxx (negPf Di).
rewrite -[_ *+ _](determinant_alternate Di EBi12) (expand_det_row _ i2).
apply: eq_bigr => j _; rewrite !mxE eqxx; congr (_ * (_ * _)).
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
rewrite (expand_det_col _ 0) big_distrl /=; apply: eq_bigr=> i _.
rewrite block_mxEul -!mulrA; do 2!congr (_ * _).
by rewrite col'_col_mx !col'Kl raddf0 row'Ku row'_row_mx IHn1.
Qed.

Lemma det_lblock n1 n2 Aul (Adl : 'M[R]_(n2, n1)) Adr :
  \det (block_mx Aul 0 Adl Adr) = \det Aul * \det Adr.
Proof. by rewrite -det_tr tr_block_mx trmx0 det_ublock !det_tr. Qed.

Lemma det_trig n (A : 'M[R]_n) : is_trig_mx A -> \det A = \prod_(i < n) A i i.
Proof.
elim/trigsqmx_ind => [|k x c B Bt IHB]; first by rewrite ?big_ord0 ?det_mx00.
rewrite det_lblock big_ord_recl det_mx11 IHB//; congr (_ * _).
  by rewrite -[ord0](lshift0 _ 0) block_mxEul.
by apply: eq_bigr => i; rewrite -!rshift1 block_mxEdr.
Qed.

Lemma det_diag n (d : 'rV[R]_n) : \det (diag_mx d) = \prod_i d 0 i.
Proof. by rewrite det_trig//; apply: eq_bigr => i; rewrite !mxE eqxx. Qed.

End ComMatrix.

Arguments lin_mul_row {R m n} u.
Arguments lin_mulmx {R m n p} A.
Arguments comm_mx_scalar {R n}.
Arguments comm_scalar_mx {R n}.
Arguments diag_mx_comm {R n}.

HB.instance Definition _ (R : finComRingType) (n' : nat) :=
  [Finite of 'M[R]_n'.+1 by <:].

#[global] Hint Resolve comm_mx_scalar comm_scalar_mx : core.

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

HB.instance Definition _ := GRing.Ring_HasMulInverse.Build 'M[R]_n
  (@mulVmx n) (@mulmxV n) (@intro_unitmx n) (@invmx_out n).

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

Lemma block_diag_mx_unit (R : comUnitRingType) n1 n2
      (Aul : 'M[R]_n1) (Adr : 'M[R]_n2) :
  (block_mx Aul 0 0 Adr \in unitmx) = (Aul \in unitmx) && (Adr \in unitmx).
Proof. by rewrite !unitmxE det_ublock unitrM. Qed.

Lemma invmx_block_diag (R : comUnitRingType) n1 n2
     (Aul : 'M[R]_n1) (Adr : 'M[R]_n2) :
  block_mx Aul 0 0 Adr \in unitmx ->
  invmx (block_mx Aul 0 0 Adr) = block_mx (invmx Aul) 0 0 (invmx Adr).
Proof.
move=> /[dup] Aunit; rewrite block_diag_mx_unit => /andP[Aul_unit Adr_unit].
rewrite -[LHS]mul1mx; apply: (canLR (mulmxK _)) => //.
rewrite [RHS](mulmx_block (invmx Aul)) !(mulmx0, mul0mx, add0r, addr0).
by rewrite !mulVmx// -?scalar_mx_block.
Qed.

HB.instance Definition _ (R : countComUnitRingType) (n' : nat) :=
  [Countable of 'M[R]_n'.+1 by <:].

HB.instance Definition _ (n : nat) (R : finComUnitRingType) :=
  [Finite of 'M[R]_n.+1 by <:].
(* Finite inversible matrices and the general linear group. *)
Section FinUnitMatrix.

Variables (n : nat) (R : finComUnitRingType).

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

HB.instance Definition _ (n : nat) (R : finComUnitRingType) :=
  [IsSUB of {'GL_n[R]} for GLval].

Section GL_unit.

Variables (n : nat) (R : finComUnitRingType).

HB.instance Definition _ := [Finite of {'GL_n[R]} by <:].
HB.instance Definition _ := FinGroup.on {'GL_n[R]}.

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
  apply/matrixP=> i j /[!mxE].
  by case: split_ordP => j' -> /[!(mxE, ord1)]; congr (A i _); apply: val_inj.
have{IHn} w_ j : exists w : 'rV_n.+1, [/\ w != 0, w 0 j = 0 & w *m A' = 0].
  have [|wj nzwj wjA'0] := IHn (row' j A').
    by apply/eqP; move/rowP/(_ j)/eqP: A'0; rewrite !mxE mulf_eq0 signr_eq0.
  exists (\row_k oapp (wj 0) 0 (unlift j k)).
  rewrite !mxE unlift_none -wjA'0; split=> //.
    apply: contraNneq nzwj => w0; apply/eqP/rowP=> k'.
    by move/rowP/(_ (lift j k')): w0; rewrite !mxE liftK.
  apply/rowP=> k; rewrite !mxE (bigD1_ord j) //= mxE unlift_none mul0r add0r.
  by apply: eq_big => //= k'; rewrite !mxE/= liftK.
have [w0 [/rV0Pn[j nz_w0j] w00_0 w0A']] := w_ 0; pose a0 := (w0 *m vA) 0 0.
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
by move/matrixP/(_ i j): eq_AB => /[!mxE]; apply: fmorph_inj.
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

Section mxOver.
Section mxOverType.
Context {m n : nat} {T : Type}.
Implicit Types (S : {pred T}).

Definition mxOver (S : {pred T}) :=
  [qualify a M : 'M[T]_(m, n) | [forall i, [forall j, M i j \in S]]].

Fact mxOver_key S : pred_key (mxOver S). Proof. by []. Qed.
Canonical mxOver_keyed S := KeyedQualifier (mxOver_key S).

Lemma mxOverP {S : {pred T}} {M : 'M[T]__} :
  reflect (forall i j, M i j \in S) (M \is a mxOver S).
Proof. exact/'forall_forallP. Qed.

Lemma mxOverS (S1 S2 : {pred T}) :
  {subset S1 <= S2} -> {subset mxOver S1 <= mxOver S2}.
Proof. by move=> sS12 M /mxOverP S1M; apply/mxOverP=> i j; apply/sS12/S1M. Qed.

Lemma mxOver_const c S : c \in S -> const_mx c \is a mxOver S.
Proof. by move=> cS; apply/mxOverP => i j; rewrite !mxE. Qed.

Lemma mxOver_constE c S : (m > 0)%N -> (n > 0)%N ->
  (const_mx c \is a mxOver S) = (c \in S).
Proof.
move=> m_gt0 n_gt0; apply/idP/idP; last exact: mxOver_const.
by move=> /mxOverP /(_ (Ordinal m_gt0) (Ordinal n_gt0)); rewrite mxE.
Qed.

End mxOverType.

Lemma thinmxOver {n : nat} {T : Type} (M : 'M[T]_(n, 0)) S : M \is a mxOver S.
Proof. by apply/mxOverP => ? []. Qed.

Lemma flatmxOver {n : nat} {T : Type} (M : 'M[T]_(0, n)) S : M \is a mxOver S.
Proof. by apply/mxOverP => - []. Qed.

Section mxOverZmodule.
Context {M : zmodType} {m n : nat}.
Implicit Types (S : {pred M}).

Lemma mxOver0 S : 0 \in S -> 0 \is a @mxOver m n _ S.
Proof. exact: mxOver_const. Qed.

Section mxOverAdd.
Variables (S : {pred M}) (addS : addrPred S) (kS : keyed_pred addS).
Fact mxOver_add_subproof : addr_closed (@mxOver m n _ kS).
Proof.
split=> [|p q Sp Sq]; first by rewrite mxOver0 // ?rpred0.
by apply/mxOverP=> i j; rewrite mxE rpredD // !(mxOverP _).
Qed.
Canonical mxOver_addrPred := AddrPred mxOver_add_subproof.
End mxOverAdd.

Section mxOverOpp.
Variables (S : {pred M}) (oppS : opprPred S) (kS : keyed_pred oppS).
Fact mxOver_opp_subproof : oppr_closed (@mxOver m n _ kS).
Proof. by move=> A /mxOverP SA; apply/mxOverP=> i j; rewrite mxE rpredN. Qed.
Canonical mxOver_opprPred := OpprPred mxOver_opp_subproof.
End mxOverOpp.

Canonical mxOver_zmodPred (S : {pred M}) (zmodS : zmodPred S)
  (kS : keyed_pred zmodS) := ZmodPred (@mxOver_opp_subproof _ _ kS).

End mxOverZmodule.

Section mxOverRing.
Context {R : ringType} {m n : nat}.

Lemma mxOver_scalar S c : 0 \in S -> c \in S -> c%:M \is a @mxOver n n R S.
Proof. by move=> S0 cS; apply/mxOverP => i j; rewrite !mxE; case: eqP. Qed.

Lemma mxOver_scalarE S c : (n > 0)%N ->
  (c%:M \is a @mxOver n n R S) = ((n > 1) ==> (0 \in S)) && (c \in S).
Proof.
case: n => [|[|k]]//= _.
   by apply/mxOverP/idP => [/(_ ord0 ord0)|cij i j]; rewrite ?mxE ?ord1.
apply/mxOverP/andP => [cij|[S0 cij] i j]; last by rewrite !mxE; case: eqP.
by split; [have := cij 0 1|have := cij 0 0]; rewrite !mxE.
Qed.

Section mxOverScale.
Variables (S : {pred R}) (mulS : mulrPred S) (kS : keyed_pred mulS).
Lemma mxOverZ : {in kS & mxOver kS, forall a : R, forall v : 'M[R]_(m, n),
        a *: v \is a mxOver kS}.
Proof.
by move=> a v aS /mxOverP vS; apply/mxOverP => i j; rewrite !mxE rpredM.
Qed.
End mxOverScale.

Lemma mxOver_diag (S : {pred R}) k (D : 'rV[R]_k) :
   0 \in S -> D \is a mxOver S -> diag_mx D \is a mxOver S.
Proof.
move=> S0 DS; apply/mxOverP => i j; rewrite !mxE.
by case: eqP => //; rewrite (mxOverP DS).
Qed.

Lemma mxOver_diagE (S : {pred R}) k (D : 'rV[R]_k) : k > 0 ->
  (diag_mx D \is a mxOver S) = ((k > 1) ==> (0 \in S)) && (D \is a mxOver S).
Proof.
case: k => [|[|k]]//= in D * => _.
  by rewrite [diag_mx _]mx11_scalar [D in RHS]mx11_scalar !mxE.
apply/idP/andP => [/mxOverP DS|[S0 DS]]; last exact: mxOver_diag.
split; first by have /[!mxE] := DS 0 1.
by apply/mxOverP => i j; have := DS j j; rewrite ord1 !mxE eqxx.
Qed.

Section mxOverMul.

Variables (S : predPredType R) (ringS : semiringPred S) (kS : keyed_pred ringS).

Lemma mxOverM p q r : {in mxOver kS & mxOver kS,
  forall u : 'M[R]_(p, q), forall v : 'M[R]_(q, r), u *m v \is a mxOver kS}.
Proof.
move=> M N /mxOverP MS /mxOverP NS; apply/mxOverP => i j.
by rewrite !mxE rpred_sum // => k _; rewrite rpredM.
Qed.

End mxOverMul.
End mxOverRing.

Section mxRingOver.
Context {R : ringType} {n : nat}.

Section semiring.
Variables (S : {pred R}) (ringS : semiringPred S) (kS : keyed_pred ringS).
Fact mxOver_mul_subproof : mulr_closed (@mxOver n.+1 n.+1 _ kS).
Proof. by split; rewrite ?mxOver_scalar ?rpred0 ?rpred1//; apply: mxOverM. Qed.
Canonical mxOver_mulrPred := MulrPred mxOver_mul_subproof.
Canonical mxOver_semiringPred := SemiringPred mxOver_mul_subproof.
End semiring.

Canonical mxOver_subringPred (S : {pred R}) (ringS : subringPred S)
   (kS : keyed_pred ringS):= SubringPred (mxOver_mul_subproof kS).

End mxRingOver.
End mxOver.

Section BlockMatrix.
Import tagnat.
Context {T : Type} {p q : nat} {p_ : 'I_p -> nat} {q_ : 'I_q -> nat}.
Notation sp := (\sum_i p_ i)%N.
Notation sq := (\sum_i q_ i)%N.
Implicit Type (s : 'I_sp) (t : 'I_sq).

Definition mxblock (B_ : forall i j, 'M[T]_(p_ i, q_ j)) :=
  \matrix_(j, k) B_ (sig1 j) (sig1 k) (sig2 j) (sig2 k).
Local Notation "\mxblock_ ( i , j ) E" := (mxblock (fun i j => E)) : ring_scope.

Definition mxrow m (B_ : forall j, 'M[T]_(m, q_ j)) :=
  \matrix_(j, k) B_ (sig1 k) j (sig2 k).
Local Notation "\mxrow_ i E" := (mxrow (fun i => E)) : ring_scope.

Definition mxcol n (B_ : forall i, 'M[T]_(p_ i, n)) :=
  \matrix_(j, k) B_ (sig1 j) (sig2 j) k.
Local Notation "\mxcol_ i E" := (mxcol (fun i => E)) : ring_scope.

Definition submxblock (A : 'M[T]_(sp, sq)) i j := mxsub  (Rank i) (Rank j) A.
Definition submxrow m (A : 'M[T]_(m, sq))    j := colsub          (Rank j) A.
Definition submxcol n (A : 'M[T]_(sp, n))  i   := rowsub (Rank i)          A.

Lemma mxblockEh B_ : \mxblock_(i, j) B_ i j = \mxrow_j \mxcol_i B_ i j.
Proof. by apply/matrixP => k l; rewrite !mxE. Qed.

Lemma mxblockEv B_ : \mxblock_(i, j) B_ i j = \mxcol_i \mxrow_j B_ i j.
Proof. by apply/matrixP => k l; rewrite !mxE. Qed.

Lemma submxblockEh A i j : submxblock A i j = submxcol (submxrow A j) i.
Proof. by apply/matrixP => k l; rewrite !mxE. Qed.

Lemma submxblockEv A i j : submxblock A i j = submxrow (submxcol A i) j.
Proof. by apply/matrixP => k l; rewrite !mxE. Qed.

Lemma mxblockK B_ i j : submxblock (\mxblock_(i, j) B_ i j) i j = B_ i j.
Proof.
apply/matrixP => k l; rewrite !mxE !Rank2K.
by do !case: _ / esym; rewrite !cast_ord_id.
Qed.

Lemma mxrowK m B_ j : @submxrow m (\mxrow_j B_ j) j = B_ j.
Proof.
apply/matrixP => k l; rewrite !mxE !Rank2K.
by do !case: _ / esym; rewrite !cast_ord_id.
Qed.

Lemma mxcolK n B_ i : @submxcol n (\mxcol_i B_ i) i = B_ i.
Proof.
apply/matrixP => k l; rewrite !mxE !Rank2K.
by do !case: _ / esym; rewrite !cast_ord_id.
Qed.

Lemma submxrow_matrix B_ j :
  submxrow (\mxblock_(i, j) B_ i j) j = \mxcol_i B_ i j.
Proof. by rewrite mxblockEh mxrowK. Qed.

Lemma submxcol_matrix B_ i :
  submxcol (\mxblock_(i, j) B_ i j) i = \mxrow_j B_ i j.
Proof. by rewrite mxblockEv mxcolK. Qed.

Lemma submxblockK A : \mxblock_(i, j) (submxblock A i j) = A.
Proof. by apply/matrixP => k l; rewrite !mxE !sig2K. Qed.

Lemma submxrowK m (A : 'M[T]_(m, sq)) : \mxrow_j (submxrow A j) = A.
Proof. by apply/matrixP => k l; rewrite !mxE !sig2K. Qed.

Lemma submxcolK n (A : 'M[T]_(sp, n)) : \mxcol_i (submxcol A i) = A.
Proof. by apply/matrixP => k l; rewrite !mxE !sig2K. Qed.

Lemma mxblockP A B :
  (forall i j, submxblock A i j = submxblock B i j) <-> A = B.
Proof.
split=> [eqAB|->//]; apply/matrixP=> s t;
have /matrixP := eqAB (sig1 s) (sig1 t).
by move=> /(_ (sig2 s) (sig2 t)); rewrite !mxE !sig2K.
Qed.

Lemma mxrowP m (A B : 'M_(m, sq)) :
  (forall j, submxrow A j = submxrow B j) <-> A = B.
Proof.
split=> [eqAB|->//]; apply/matrixP=> i t; have /matrixP := eqAB (sig1 t).
by move=> /(_ i (sig2 t)); rewrite !mxE !sig2K.
Qed.

Lemma mxcolP n (A B : 'M_(sp, n)) :
  (forall i, submxcol A i = submxcol B i) <-> A = B.
Proof.
split=> [eqAB|->//]; apply/matrixP=> s j; have /matrixP := eqAB (sig1 s).
by move=> /(_ (sig2 s) j); rewrite !mxE !sig2K.
Qed.

Lemma eq_mxblockP A_ B_ :
  (forall i j, A_ i j = B_ i j) <->
  (\mxblock_(i, j) A_ i j = \mxblock_(i, j) B_ i j).
Proof. by rewrite -mxblockP; split => + i j => /(_ i j); rewrite !mxblockK. Qed.

Lemma eq_mxblock A_ B_ :
  (forall i j, A_ i j = B_ i j) ->
  (\mxblock_(i, j) A_ i j = \mxblock_(i, j) B_ i j).
Proof. by move=> /eq_mxblockP. Qed.

Lemma eq_mxrowP m (A_ B_ : forall j, 'M[T]_(m, q_ j)) :
  (forall j, A_ j = B_ j) <-> (\mxrow_j A_ j = \mxrow_j B_ j).
Proof. by rewrite -mxrowP; split => + j => /(_ j); rewrite !mxrowK. Qed.

Lemma eq_mxrow m (A_ B_ : forall j, 'M[T]_(m, q_ j)) :
  (forall j, A_ j = B_ j) -> (\mxrow_j A_ j = \mxrow_j B_ j).
Proof. by move=> /eq_mxrowP. Qed.

Lemma eq_mxcolP n (A_ B_ : forall i, 'M[T]_(p_ i, n)) :
  (forall i, A_ i = B_ i) <-> (\mxcol_i A_ i = \mxcol_i B_ i).
Proof. by rewrite -mxcolP; split => + i => /(_ i); rewrite !mxcolK. Qed.

Lemma eq_mxcol n (A_ B_ : forall i, 'M[T]_(p_ i, n)) :
  (forall i, A_ i = B_ i) -> (\mxcol_i A_ i = \mxcol_i B_ i).
Proof. by move=> /eq_mxcolP. Qed.

Lemma row_mxrow m (B_ : forall j, 'M[T]_(m, q_ j)) i :
  row i (\mxrow_j B_ j) = \mxrow_j (row i (B_ j)).
Proof. by apply/rowP => l; rewrite !mxE. Qed.

Lemma col_mxrow m (B_ : forall j, 'M[T]_(m, q_ j)) j :
  col j (\mxrow_j B_ j) = col (sig2 j) (B_ (sig1 j)).
Proof. by apply/colP => l; rewrite !mxE. Qed.

Lemma row_mxcol n (B_ : forall i, 'M[T]_(p_ i, n)) i :
  row i (\mxcol_i B_ i) = row (sig2 i) (B_ (sig1 i)).
Proof. by apply/rowP => l; rewrite !mxE. Qed.

Lemma col_mxcol n (B_ : forall i, 'M[T]_(p_ i, n)) j :
  col j (\mxcol_i B_ i) = \mxcol_i (col j (B_ i)).
Proof. by apply/colP => l; rewrite !mxE. Qed.

Lemma row_mxblock B_ i :
  row i (\mxblock_(i, j) B_ i j) = \mxrow_j row (sig2 i) (B_ (sig1 i) j).
Proof. by apply/rowP => l; rewrite !mxE. Qed.

Lemma col_mxblock B_ j :
  col j (\mxblock_(i, j) B_ i j) = \mxcol_i col (sig2 j) (B_ i (sig1 j)).
Proof. by apply/colP => l; rewrite !mxE. Qed.

End BlockMatrix.

Notation "\mxblock_ ( i < m , j < n ) E" :=
  (mxblock (fun (i : 'I_m) (j : 'I_ n) => E)) (only parsing) : ring_scope.
Notation "\mxblock_ ( i , j < n ) E" :=
  (\mxblock_(i < n, j < n) E) (only parsing) : ring_scope.
Notation "\mxblock_ ( i , j ) E" := (\mxblock_(i < _, j < _) E) : ring_scope.
Notation "\mxrow_ ( j < m ) E" := (mxrow (fun (j : 'I_m) => E))
  (only parsing) : ring_scope.
Notation "\mxrow_ j E" := (\mxrow_(j < _) E) : ring_scope.
Notation "\mxcol_ ( i < m ) E" := (mxcol (fun (i : 'I_m) => E))
  (only parsing) : ring_scope.
Notation "\mxcol_ i E" := (\mxcol_(i < _) E) : ring_scope.

Lemma tr_mxblock {T : Type} {p q : nat} {p_ : 'I_p -> nat} {q_ : 'I_q -> nat}
  (B_ : forall i j, 'M[T]_(p_ i, q_ j)) :
  (\mxblock_(i, j) B_ i j)^T = \mxblock_(i, j) (B_ j i)^T.
Proof. by apply/matrixP => i j; rewrite !mxE. Qed.

Section SquareBlockMatrix.

Context {T : Type} {p : nat} {p_ : 'I_p -> nat}.
Notation sp := (\sum_i p_ i)%N.
Implicit Type (s : 'I_sp).

Lemma tr_mxrow n (B_ : forall j, 'M[T]_(n, p_ j)) :
  (\mxrow_j B_ j)^T = \mxcol_i (B_ i)^T.
Proof. by apply/matrixP => i j; rewrite !mxE. Qed.

Lemma tr_mxcol n (B_ : forall i, 'M[T]_(p_ i, n)) :
  (\mxcol_i B_ i)^T = \mxrow_i (B_ i)^T.
Proof. by apply/matrixP => i j; rewrite !mxE. Qed.

Lemma tr_submxblock (A : 'M[T]_sp) i j :
  (submxblock A i j)^T = (submxblock A^T j i).
Proof. by apply/matrixP => k l; rewrite !mxE. Qed.

Lemma tr_submxrow n (A : 'M[T]_(n, sp)) j :
  (submxrow A j)^T = (submxcol A^T j).
Proof. by apply/matrixP => k l; rewrite !mxE. Qed.

Lemma tr_submxcol n (A : 'M[T]_(sp, n)) i :
  (submxcol A i)^T = (submxrow A^T i).
Proof. by apply/matrixP => k l; rewrite !mxE. Qed.

End SquareBlockMatrix.

Section BlockRowRecL.
Import tagnat.
Context {T : Type} {m : nat} {p_ : 'I_m.+1 -> nat}.
Notation sp := (\sum_i p_ i)%N.

Lemma mxsize_recl : (p_ ord0 + \sum_i p_ (lift ord0 i) = (\sum_i p_ i))%N.
Proof. by rewrite big_ord_recl. Qed.

Lemma mxrow_recl n (B_ : forall j, 'M[T]_(n, p_ j)) :
  \mxrow_j B_ j = castmx (erefl, mxsize_recl)
    (row_mx (B_ 0) (\mxrow_j B_ (lift ord0 j))).
Proof.
apply/mxrowP => i; rewrite mxrowK.
apply/matrixP => j k; rewrite !(castmxE, mxE)/=.
case: splitP => l /=; do [
    rewrite [LHS]RankEsum big_mkcond big_ord_recl -big_mkcond/=;
    rewrite /bump/= -addnA cast_ord_id;
    under eq_bigl do rewrite add1n -ltn_predRL/=].
  case: posnP => i0; last first.
    by move=> lE; have := ltn_ord l; rewrite /= -lE -ltn_subRL subnn.
  by rewrite (@val_inj _ _ _ i 0 i0) big_pred0_eq in k * => /val_inj->.
case: posnP => i0.
  rewrite (@val_inj _ _ _ i 0 i0) big_pred0_eq in k l * => kE.
  by have := ltn_ord k; rewrite /= [val k]kE -ltn_subRL subnn.
have i_lt : i.-1 < m by rewrite -subn1 ltn_subLR.
set i' := lift ord0 (Ordinal i_lt).
have ii' : i = i' by apply/val_inj; rewrite /=/bump/= add1n prednK.
have k_lt : k < p_ i' by rewrite -ii'.
move=> /addnI; rewrite eqRank => /val_inj/= /[dup] kl<-; rewrite mxE.
rewrite Rank2K//; case: _ / esym; rewrite cast_ord_id/=.
rewrite -/i'; set j' := Ordinal _; have : k = j' :> nat by [].
by move: j'; rewrite -ii' => j' /val_inj->.
Qed.

End BlockRowRecL.

Lemma mxcol_recu {T : Type} {p : nat} {p_ : 'I_p.+1 -> nat} m
    (B_ : forall j, 'M[T]_(p_ j, m)) :
  \mxcol_j B_ j = castmx (mxsize_recl, erefl)
    (col_mx (B_ 0) (\mxcol_j B_ (lift ord0 j))).
Proof.
by apply: trmx_inj; rewrite trmx_cast tr_col_mx !tr_mxcol mxrow_recl.
Qed.

Section BlockMatrixRec.
Local Notation e := (mxsize_recl, mxsize_recl).
Local Notation l0 := (lift ord0).
Context {T : Type}.

Lemma mxblock_recu {p q : nat} {p_ : 'I_p.+1 -> nat} {q_ : 'I_q -> nat}
    (B_ : forall i j, 'M[T]_(p_ i, q_ j)) :
  \mxblock_(i, j) B_ i j = castmx (mxsize_recl, erefl) (col_mx
     (\mxrow_j B_ ord0 j)
     (\mxblock_(i, j) B_ (l0 i) j)).
Proof. by rewrite !mxblockEv mxcol_recu. Qed.

Lemma mxblock_recl {p q : nat} {p_ : 'I_p -> nat} {q_ : 'I_q.+1 -> nat}
    (B_ : forall i j, 'M[T]_(p_ i, q_ j)) :
  \mxblock_(i, j) B_ i j = castmx (erefl, mxsize_recl)
  (row_mx (\mxcol_i B_ i ord0) (\mxblock_(i, j) B_ i (l0 j))).
Proof. by rewrite !mxblockEh mxrow_recl. Qed.

Lemma mxblock_recul {p q : nat} {p_ : 'I_p.+1 -> nat} {q_ : 'I_q.+1 -> nat}
    (B_ : forall i j, 'M[T]_(p_ i, q_ j)) :
  \mxblock_(i, j) B_ i j = castmx e (block_mx
     (B_ 0 0)                  (\mxrow_j B_ ord0 (l0 j))
     (\mxcol_i B_ (l0 i) ord0) (\mxblock_(i, j) B_ (l0 i) (l0 j))).
Proof.
rewrite mxblock_recl mxcol_recu mxblock_recu -cast_row_mx -block_mxEh.
by rewrite castmx_comp; apply: eq_castmx.
Qed.

Lemma mxrowEblock {q : nat} {q_ : 'I_q -> nat} m
    (R_ : forall j, 'M[T]_(m, q_ j)) :
  (\mxrow_j R_ j) =
  castmx (big_ord1 _ (fun=> m), erefl) (\mxblock_(i < 1, j < q) R_ j).
Proof.
rewrite mxblock_recu castmx_comp.
apply/matrixP => i j; rewrite !castmxE !mxE/=; case: splitP => //=.
  by move=> k /val_inj->; rewrite ?cast_ord_id ?mxE//=.
by move=> [k klt]; suff: false by []; rewrite big_ord0 in klt.
Qed.

Lemma mxcolEblock {p : nat} {p_ : 'I_p -> nat} n
    (C_ : forall i, 'M[T]_(p_ i, n)) :
  (\mxcol_i C_ i) =
  castmx (erefl, big_ord1 _ (fun=> n)) (\mxblock_(i < p, j < 1) C_ i).
Proof.
by apply: trmx_inj; rewrite tr_mxcol mxrowEblock trmx_cast tr_mxblock.
Qed.

Lemma mxEmxrow m n (A : 'M[T]_(m, n)) :
  A = castmx (erefl, big_ord1 _ (fun=> n)) (\mxrow__ A).
Proof.
apply/matrixP => i j; rewrite castmxE !mxE/= cast_ord_id.
congr (A i); set j' := cast_ord _ _.
suff -> : j' = (tagnat.Rank 0 j) by apply/val_inj; rewrite tagnat.Rank2K.
by apply/val_inj; rewrite [RHS]tagnat.RankEsum/= big_pred0_eq add0n.
Qed.

Lemma mxEmxcol m n (A : 'M[T]_(m, n)) :
  A = castmx (big_ord1 _ (fun=> m), erefl) (\mxcol__ A).
Proof. by apply: trmx_inj; rewrite trmx_cast tr_mxcol [LHS]mxEmxrow. Qed.

Lemma mxEmxblock m n (A : 'M[T]_(m, n)) :
  A = castmx (big_ord1 _ (fun=> m), big_ord1 _ (fun=> n))
             (\mxblock_(i < 1, j < 1) A).
Proof. by rewrite [LHS]mxEmxrow mxrowEblock castmx_comp; apply: eq_castmx. Qed.

End BlockMatrixRec.

Section BlockRowZmod.
Context {V : zmodType} {q : nat} {q_ : 'I_q -> nat}.
Notation sq := (\sum_i q_ i)%N.
Implicit Type (s : 'I_sq).

Lemma mxrowD m (R_ R'_ : forall j, 'M[V]_(m, q_ j)) :
  \mxrow_j (R_ j + R'_ j) = \mxrow_j (R_ j) + \mxrow_j (R'_ j).
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma mxrowN m (R_ : forall j, 'M[V]_(m, q_ j)) :
  \mxrow_j (- R_ j) = - \mxrow_j (R_ j).
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma mxrowB m (R_ R'_ : forall j, 'M[V]_(m, q_ j)) :
  \mxrow_j (R_ j - R'_ j) = \mxrow_j (R_ j) - \mxrow_j (R'_ j).
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma mxrow0 m : \mxrow_j (0 : 'M[V]_(m, q_ j)) = 0.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma mxrow_const m a : \mxrow_j (const_mx a : 'M[V]_(m, q_ j)) = const_mx a.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma mxrow_sum (J : finType) m
    (R_ : forall i j, 'M[V]_(m, q_ j)) (P : {pred J}) :
  \mxrow_j (\sum_(i | P i) R_ i j) = \sum_(i | P i) \mxrow_j (R_ i j).
Proof.
apply/matrixP => i j; rewrite !(mxE, summxE).
by apply: eq_bigr => l; rewrite !mxE.
Qed.

Lemma submxrowD m (B B' : 'M[V]_(m, sq)) j :
 submxrow (B + B') j = submxrow B j + submxrow B' j.
Proof. by apply/matrixP => i i'; rewrite !mxE. Qed.

Lemma submxrowN m (B : 'M[V]_(m, sq)) j :
 submxrow (- B) j = - submxrow B j.
Proof. by apply/matrixP => i i'; rewrite !mxE. Qed.

Lemma submxrowB m (B B' : 'M[V]_(m, sq)) j :
 submxrow (B - B') j = submxrow B j - submxrow B' j.
Proof. by apply/matrixP => i i'; rewrite !mxE. Qed.

Lemma submxrow0 m j : submxrow (0 : 'M[V]_(m, sq)) j = 0.
Proof. by apply/matrixP=> i i'; rewrite !mxE. Qed.

Lemma submxrow_sum (J : finType) m
   (R_ : forall i, 'M[V]_(m, sq)) (P : {pred J}) j:
  submxrow (\sum_(i | P i) R_ i) j = \sum_(i | P i) submxrow (R_ i) j.
Proof.
apply/matrixP => i i'; rewrite !(mxE, summxE).
by apply: eq_bigr => l; rewrite !mxE.
Qed.

End BlockRowZmod.

Section BlockRowRing.
Context {R : ringType} {n : nat} {q_ : 'I_n -> nat}.
Notation sq := (\sum_i q_ i)%N.
Implicit Type (s : 'I_sq).

Lemma mul_mxrow m n' (A : 'M[R]_(m, n')) (R_ : forall j, 'M[R]_(n', q_ j)) :
  A *m \mxrow_j R_ j= \mxrow_j (A *m R_ j).
Proof. by apply/matrixP=> i s; rewrite !mxE; under eq_bigr do rewrite !mxE. Qed.

Lemma mul_submxrow m n' (A : 'M[R]_(m, n')) (B : 'M[R]_(n', sq)) j :
  A *m submxrow B j= submxrow (A *m B) j.
Proof. by apply/matrixP=> i s; rewrite !mxE; under eq_bigr do rewrite !mxE. Qed.

End BlockRowRing.

Section BlockColZmod.
Context {V : zmodType} {n : nat} {p_ : 'I_n -> nat}.
Notation sp := (\sum_i p_ i)%N.
Implicit Type (s : 'I_sp).

Lemma mxcolD m (C_ C'_ : forall i, 'M[V]_(p_ i, m)) :
  \mxcol_i (C_ i + C'_ i) = \mxcol_i (C_ i) + \mxcol_i (C'_ i).
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma mxcolN m (C_ : forall i, 'M[V]_(p_ i, m)) :
  \mxcol_i (- C_ i) = - \mxcol_i (C_ i).
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma mxcolB m (C_ C'_ : forall i, 'M[V]_(p_ i, m)) :
  \mxcol_i (C_ i - C'_ i) = \mxcol_i (C_ i) - \mxcol_i (C'_ i).
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma mxcol0 m : \mxcol_i (0 : 'M[V]_(p_ i, m)) = 0.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma mxcol_const m a : \mxcol_j (const_mx a : 'M[V]_(p_ j, m)) = const_mx a.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma mxcol_sum
  (I : finType) m (C_ : forall j i, 'M[V]_(p_ i, m)) (P : {pred I}):
  \mxcol_i (\sum_(j | P j) C_ j i) = \sum_(j | P j) \mxcol_i (C_ j i).
Proof.
apply/matrixP => i j; rewrite !(mxE, summxE).
by apply: eq_bigr => l; rewrite !mxE.
Qed.

Lemma submxcolD m (B B' : 'M[V]_(sp, m)) i :
 submxcol (B + B') i = submxcol B i + submxcol B' i.
Proof. by apply/matrixP => j j'; rewrite !mxE. Qed.

Lemma submxcolN m (B : 'M[V]_(sp, m)) i :
 submxcol (- B) i = - submxcol B i.
Proof. by apply/matrixP => j j'; rewrite !mxE. Qed.

Lemma submxcolB m (B B' : 'M[V]_(sp, m)) i :
 submxcol (B - B') i = submxcol B i - submxcol B' i.
Proof. by apply/matrixP => j j'; rewrite !mxE. Qed.

Lemma submxcol0 m i : submxcol (0 : 'M[V]_(sp, m)) i = 0.
Proof. by apply/matrixP=> j j'; rewrite !mxE. Qed.

Lemma submxcol_sum (I : finType) m
   (C_ : forall j, 'M[V]_(sp, m)) (P : {pred I}) i :
  submxcol (\sum_(j | P j) C_ j) i = \sum_(j | P j) submxcol (C_ j) i.
Proof.
apply/matrixP => j j'; rewrite !(mxE, summxE).
by apply: eq_bigr => l; rewrite !mxE.
Qed.

End BlockColZmod.

Section BlockColRing.
Context {R : ringType} {n : nat} {p_ : 'I_n -> nat}.
Notation sp := (\sum_i p_ i)%N.
Implicit Type (s : 'I_sp).

Lemma mxcol_mul n' m (C_ : forall i, 'M[R]_(p_ i, n')) (A : 'M[R]_(n', m)) :
  \mxcol_i C_ i *m A = \mxcol_i (C_ i *m A).
Proof. by apply/matrixP=> i s; rewrite !mxE; under eq_bigr do rewrite !mxE. Qed.

Lemma submxcol_mul n' m (B : 'M[R]_(sp, n')) (A : 'M[R]_(n', m)) i :
  submxcol B i *m A = submxcol (B *m A) i.
Proof. by apply/matrixP=> j s; rewrite !mxE; under eq_bigr do rewrite !mxE. Qed.

End BlockColRing.

Section BlockMatrixZmod.
Context {V : zmodType} {m n : nat}.
Context {p_ : 'I_m -> nat} {q_ : 'I_n -> nat}.
Notation sp := (\sum_i p_ i)%N.
Notation sq := (\sum_i q_ i)%N.

Lemma mxblockD (B_ B'_ : forall i j, 'M[V]_(p_ i, q_ j)) :
  \mxblock_(i, j) (B_ i j + B'_ i j) =
  \mxblock_(i, j) (B_ i j) + \mxblock_(i, j) (B'_ i j).
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma mxblockN (B_ : forall i j, 'M[V]_(p_ i, q_ j)) :
  \mxblock_(i, j) (- B_ i j) = - \mxblock_(i, j) (B_ i j).
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma mxblockB (B_ B'_ : forall i j, 'M[V]_(p_ i, q_ j)) :
  \mxblock_(i, j) (B_ i j - B'_ i j) =
  \mxblock_(i, j) (B_ i j) - \mxblock_(i, j) (B'_ i j).
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma mxblock0 : \mxblock_(i, j) (0 : 'M[V]_(p_ i, q_ j)) = 0.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma mxblock_const a :
  \mxblock_(i, j) (const_mx a : 'M[V]_(p_ i, q_ j)) = const_mx a.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma mxblock_sum (I : finType)
    (B_ : forall k i j, 'M[V]_(p_ i, q_ j)) (P : {pred I}):
  \mxblock_(i, j) (\sum_(k | P k) B_ k i j) =
  \sum_(k | P k) \mxblock_(i, j) (B_ k i j).
Proof.
apply/matrixP => i j; rewrite !(mxE, summxE).
by apply: eq_bigr => l; rewrite !mxE.
Qed.

Lemma submxblockD (B B' : 'M[V]_(sp, sq)) i j :
 submxblock (B + B') i j = submxblock B i j + submxblock B' i j.
Proof. by apply/matrixP => k l; rewrite !mxE. Qed.

Lemma submxblockN (B : 'M[V]_(sp, sq)) i j :
 submxblock (- B) i j = - submxblock B i j.
Proof. by apply/matrixP => k l; rewrite !mxE. Qed.

Lemma submxblockB (B B' : 'M[V]_(sp, sq)) i j :
 submxblock (B - B') i j = submxblock B i j - submxblock B' i j.
Proof. by apply/matrixP => k l; rewrite !mxE. Qed.

Lemma submxblock0 i j : submxblock (0 : 'M[V]_(sp, sq)) i j = 0.
Proof. by apply/matrixP=> k l; rewrite !mxE. Qed.

Lemma submxblock_sum (I : finType)
   (B_ : forall k, 'M[V]_(sp, sq)) (P : {pred I}) i j :
  submxblock (\sum_(k | P k) B_ k) i j = \sum_(k | P k) submxblock (B_ k) i j.
Proof.
apply/matrixP => k l; rewrite !(mxE, summxE).
by apply: eq_bigr => p; rewrite !mxE.
Qed.

End BlockMatrixZmod.

Section BlockMatrixRing.
Context {R : ringType} {p q : nat} {p_ : 'I_p -> nat} {q_ : 'I_q -> nat}.
Notation sp := (\sum_i p_ i)%N.
Notation sq := (\sum_i q_ i)%N.

Lemma mul_mxrow_mxcol m n
    (R_ : forall j, 'M[R]_(m, p_ j)) (C_ : forall i, 'M[R]_(p_ i, n)) :
  \mxrow_j R_ j *m \mxcol_i C_ i = \sum_i (R_ i *m C_ i).
Proof.
apply/matrixP => i j; rewrite !mxE summxE; under [RHS]eq_bigr do rewrite !mxE.
rewrite sig_big_dep/= (reindex _ tagnat.sig_bij_on)/=.
by apply: eq_bigr=> l _; rewrite !mxE.
Qed.

Lemma mul_mxcol_mxrow m
    (C_ : forall i, 'M[R]_(p_ i, m)) (R_ : forall j, 'M[R]_(m, q_ j)) :
  \mxcol_i C_ i*m \mxrow_j R_ j  = \mxblock_(i, j) (C_ i *m R_ j).
Proof.
apply/mxblockP => i j; rewrite mxblockK.
by rewrite submxblockEh -mul_submxrow -submxcol_mul mxcolK mxrowK.
Qed.

Lemma mul_mxrow_mxblock m
    (R_ : forall i, 'M[R]_(m, p_ i)) (B_ : forall i j, 'M[R]_(p_ i, q_ j)) :
  \mxrow_i R_ i *m \mxblock_(i, j) B_ i j = \mxrow_j (\sum_i (R_ i *m B_ i j)).
Proof.
rewrite mxblockEv mul_mxrow_mxcol mxrow_sum.
by apply: eq_bigr => i _; rewrite mul_mxrow.
Qed.

Lemma mul_mxblock_mxrow m
    (B_ : forall i j, 'M[R]_(q_ i, p_ j)) (C_ : forall i, 'M[R]_(p_ i, m)) :
  \mxblock_(i, j) B_ i j *m \mxcol_j C_ j = \mxcol_i (\sum_j (B_ i j *m C_ j)).
Proof.
rewrite mxblockEh mul_mxrow_mxcol mxcol_sum.
by apply: eq_bigr => i _; rewrite mxcol_mul.
Qed.

End BlockMatrixRing.

Lemma mul_mxblock {R : ringType} {p q r : nat}
    {p_ : 'I_p -> nat} {q_ : 'I_q -> nat} {r_ : 'I_r -> nat}
    (A_ : forall i j, 'M[R]_(p_ i, q_ j)) (B_ : forall j k, 'M_(q_ j, r_ k)) :
  \mxblock_(i, j) A_ i j *m \mxblock_(j, k) B_ j k =
  \mxblock_(i, k) \sum_j (A_ i j *m B_ j k).
Proof.
rewrite mxblockEh mul_mxrow_mxblock mxblockEh; apply: eq_mxrow => i.
by under [LHS]eq_bigr do rewrite mxcol_mul; rewrite -mxcol_sum.
Qed.

Section SquareBlockMatrixZmod.
Import Order.TTheory tagnat.
Context {V : zmodType} {p : nat} {p_ : 'I_p -> nat}.
Notation sp := (\sum_i p_ i)%N.
Implicit Type (s : 'I_sp).

Lemma is_trig_mxblockP (B_ : forall i j, 'M[V]_(p_ i, p_ j)) :
  reflect [/\ forall (i j : 'I_p), (i < j)%N -> B_ i j = 0 &
              forall i, is_trig_mx (B_ i i)]
          (is_trig_mx (\mxblock_(i, j) B_ i j)).
Proof.
apply: (iffP is_trig_mxP); last first.
  move=> [Blt1 /(_ _)/is_trig_mxP Blt2]/= s s'; rewrite !mxE.
  rewrite -[_ < _]lt_sig ltEsig/= /sig1 /sig2 leEord.
  case: ltngtP => //= ii'; first by rewrite (Blt1 _ _ ii') mxE.
  move: (sig s) (sig s') ii' => -[/= i j] [/= i' +] /val_inj ii'.
  by case: _ / ii' => j'; rewrite tagged_asE => /Blt2->.
move=> Btrig; split=> [i i' lti|i].
  apply/matrixP => j j'; have := Btrig (Rank _ j) (Rank _ j').
  rewrite !mxE !Rank2K; do !case: _ / esym; rewrite !cast_ord_id.
  rewrite /Rank [_ <= _]lt_rank.
  by rewrite ltEsig/= leEord ltnW//= (ltn_geF lti)//= => /(_ isT).
apply/is_trig_mxP => j j' ltj; have := Btrig (Rank _ j) (Rank _ j').
rewrite !mxE !Rank2K; do! case: _ / esym; rewrite !cast_ord_id.
by rewrite [_ <= _]lt_rank ltEsig/= !leEord leqnn/= tagged_asE; apply.
Qed.

Lemma is_trig_mxblock (B_ : forall i j, 'M[V]_(p_ i, p_ j)) :
  is_trig_mx (\mxblock_(i, j) B_ i j) =
  ([forall i : 'I_p, forall j : 'I_p, (i < j)%N ==> (B_ i j == 0)] &&
   [forall i, is_trig_mx (B_ i i)]).
Proof.
by apply/is_trig_mxblockP/andP => -[] => [/(_ _ _ _)/eqP|]
  => /'forall_'forall_implyP => [|/(_ _ _ _)/eqP] Blt /forallP.
Qed.

Lemma is_diag_mxblockP (B_ : forall i j, 'M[V]_(p_ i, p_ j)) :
  reflect [/\ forall (i j : 'I_p), i != j -> B_ i j = 0 &
              forall i, is_diag_mx (B_ i i)]
          (is_diag_mx (\mxblock_(i, j) B_ i j)).
Proof.
apply: (iffP is_diag_mxP); last first.
  move=> [Bneq1 /(_ _)/is_diag_mxP Bneq2]/= s s'; rewrite !mxE.
  rewrite val_eqE -(can_eq sigK) /sig1 /sig2.
  move: (sig s) (sig s') => -[/= i j] [/= i' j'].
  rewrite -tag_eqE/= /tag_eq/= negb_and.
  case: eqVneq => /= [ii'|/Bneq1->]; last by rewrite !mxE.
  by rewrite -ii' in j' *; rewrite tagged_asE => /Bneq2.
move=> Bdiag; split=> [i i' Ni|i].
  apply/matrixP => j j'; have := Bdiag (Rank _ j) (Rank _ j').
  rewrite !mxE !Rank2K; do !case: _ / esym; rewrite !cast_ord_id.
  by rewrite eq_Rank negb_and Ni; apply.
apply/is_diag_mxP => j j' Nj; have := Bdiag (Rank _ j) (Rank _ j').
rewrite !mxE !Rank2K; do! case: _ / esym; rewrite !cast_ord_id.
by rewrite eq_Rank negb_and val_eqE Nj orbT; apply.
Qed.

Lemma is_diag_mxblock (B_ : forall i j, 'M[V]_(p_ i, p_ j)) :
  is_diag_mx (\mxblock_(i, j) B_ i j) =
  ([forall i : 'I_p, forall j : 'I_p, (i != j) ==> (B_ i j == 0)] &&
   [forall i, is_diag_mx (B_ i i)]).
Proof.
by apply/is_diag_mxblockP/andP => -[] => [/(_ _ _ _)/eqP|]
  => /'forall_'forall_implyP => [|/(_ _ _ _)/eqP] Blt /forallP.
Qed.

Definition mxdiag (B_ : forall i, 'M[V]_(p_ i)) : 'M[V]_(\sum_i p_ i) :=
  \mxblock_(j, k) if j == k then conform_mx 0 (B_ j) else 0.
Local Notation "\mxdiag_ i E" := (mxdiag (fun i => E)) : ring_scope.

Lemma submxblock_diag (B_  : forall i, 'M[V]_(p_ i)) i :
  submxblock (\mxdiag_i B_ i) i i = B_ i.
Proof. by rewrite mxblockK conform_mx_id eqxx. Qed.

Lemma eq_mxdiagP (B_ B'_ : forall i, 'M[V]_(p_ i)) :
  (forall i, B_ i = B'_ i) <-> (\mxdiag_i B_ i = \mxdiag_i B'_ i).
Proof.
rewrite /mxdiag -eq_mxblockP; split => [+ i j|+ i] => [/(_ i)|/(_ i i)].
  by case: eqVneq => // -> ->.
by rewrite eqxx !conform_mx_id.
Qed.

Lemma eq_mxdiag (B_ B'_ : forall i, 'M[V]_(p_ i)) :
  (forall i, B_ i = B'_ i) -> (\mxdiag_i B_ i = \mxdiag_i B'_ i).
Proof. by move=> /eq_mxdiagP. Qed.

Lemma mxdiagD (B_ B'_ : forall i, 'M[V]_(p_ i)) :
  \mxdiag_i (B_ i + B'_ i) = \mxdiag_i (B_ i) + \mxdiag_i (B'_ i).
Proof.
rewrite /mxdiag -mxblockD; apply/eq_mxblock => i j.
by case: eqVneq => [->|]; rewrite ?conform_mx_id ?addr0.
Qed.

Lemma mxdiagN (B_ : forall i, 'M[V]_(p_ i)) :
  \mxdiag_i (- B_ i) = - \mxdiag_i (B_ i).
Proof.
rewrite /mxdiag -mxblockN; apply/eq_mxblock => i j.
by case: eqVneq => [->|]; rewrite ?conform_mx_id ?oppr0.
Qed.

Lemma mxdiagB (B_ B'_ : forall i, 'M[V]_(p_ i)) :
  \mxdiag_i (B_ i - B'_ i) = \mxdiag_i (B_ i) - \mxdiag_i (B'_ i).
Proof. by rewrite mxdiagD mxdiagN. Qed.

Lemma mxdiag0 : \mxdiag_i (0 : 'M[V]_(p_ i)) = 0.
Proof. by under [LHS]eq_mxdiag do rewrite -[0]subr0; rewrite mxdiagB subrr. Qed.

Lemma mxdiag_sum (I : finType) (B_ : forall k i, 'M[V]_(p_ i)) (P : {pred I}) :
  \mxdiag_i (\sum_(k | P k) B_ k i) = \sum_(k | P k) \mxdiag_i (B_ k i).
Proof.
rewrite /mxdiag -mxblock_sum; apply/eq_mxblock => i j.
case: eqVneq => [->|]; rewrite ?conform_mx_id//; last by rewrite big1.
by apply: eq_bigr => k; rewrite conform_mx_id.
Qed.

Lemma tr_mxdiag (B_ : forall i, 'M[V]_(p_ i)) :
  (\mxdiag_i B_ i)^T = \mxdiag_i (B_ i)^T.
Proof.
rewrite tr_mxblock; apply/eq_mxblock => i j.
by case: eqVneq => [->|]; rewrite ?trmx_conform ?trmx0.
Qed.

Lemma row_mxdiag (B_ : forall i, 'M[V]_(p_ i)) k :
  let B'_ i := if sig1 k == i then conform_mx 0 (B_ i) else 0 in
  row k (\mxdiag_ i B_ i) = row (sig2 k) (\mxrow_i B'_ i).
Proof.
rewrite /= row_mxblock row_mxrow; apply/eq_mxrow => i.
by case: eqVneq => // e; congr row; rewrite e.
Qed.

Lemma col_mxdiag (B_ : forall i, 'M[V]_(p_ i)) k :
  let B'_ i := if sig1 k == i then conform_mx 0 (B_ i) else 0 in
  col k (\mxdiag_ i B_ i) = col (sig2 k) (\mxcol_i B'_ i).
Proof.
by rewrite /= col_mxblock col_mxcol; apply/eq_mxcol => i; rewrite eq_sym.
Qed.

End SquareBlockMatrixZmod.

Notation "\mxdiag_ ( i < n ) E" := (mxdiag (fun i : 'I_n => E))
  (only parsing) : ring_scope.
Notation "\mxdiag_ i E" := (\mxdiag_(i < _) E) : ring_scope.

Lemma mxdiag_recl {V : zmodType} {m : nat} {p_ : 'I_m.+1 -> nat}
    (B_ : forall i, 'M[V]_(p_ i)) :
  \mxdiag_i B_ i = castmx (mxsize_recl, mxsize_recl)
    (block_mx (B_ 0) 0 0 (\mxdiag_i B_ (lift ord0 i))).
Proof.
rewrite /mxdiag mxblock_recul/= !conform_mx_id.
by congr (castmx _ (block_mx _ _ _ _)); rewrite ?mxrow0 ?mxcol0.
Qed.

Section SquareBlockMatrixRing.
Import tagnat.
Context {R : ringType} {p : nat} {p_ : 'I_p -> nat}.
Notation sp := (\sum_i p_ i)%N.
Implicit Type (s : 'I_sp).

Lemma mxtrace_mxblock (B_ : forall i j, 'M[R]_(p_ i, p_ j)) :
  \tr (\mxblock_(i, j) B_ i j) = \sum_i \tr (B_ i i).
Proof.
rewrite /mxtrace sig_big_dep (reindex _ sig_bij_on)/=.
by apply: eq_bigr => i _; rewrite !mxE.
Qed.

Lemma mxdiagZ a : \mxdiag_i (a%:M : 'M[R]_(p_ i)) = a%:M.
Proof.
apply/matrixP => s t; rewrite !mxE -(can_eq sigK) /sig1 /sig2.
case: (sig s) (sig t) => [/= i j] [/= i' j'].
case: eqP => [<-|ni] in j' *; last by rewrite !mxE; case: eqVneq => // -[].
by rewrite conform_mx_id eq_Tagged/= mxE.
Qed.

Lemma diag_mxrow (B_ : forall j, 'rV[R]_(p_ j)) :
  diag_mx (\mxrow_j B_ j) = \mxdiag_j (diag_mx (B_ j)).
Proof.
apply/matrixP => s s'; rewrite !mxE/= -(can_eq sigK) /sig1 /sig2.
case: (sig s) (sig s') => [/= i j] [/= i' j'].
rewrite -tag_eqE /tag_eq/=; case: (eqVneq i i') => ii'; rewrite ?mxE//=.
by case: _ / ii' in j' *; rewrite tagged_asE/= conform_mx_id mxE.
Qed.

Lemma mxtrace_mxdiag (B_ : forall i, 'M[R]_(p_ i)) :
  \tr (\mxdiag_i B_ i) = \sum_i \tr (B_ i).
Proof.
by rewrite mxtrace_mxblock; apply: eq_bigr => i _; rewrite eqxx/= conform_mx_id.
Qed.

Lemma mul_mxdiag_mxcol m
    (D_ : forall i, 'M[R]_(p_ i)) (C_ : forall i, 'M[R]_(p_ i, m)):
  \mxdiag_i D_ i *m \mxcol_i C_ i = \mxcol_i (D_ i *m C_ i).
Proof.
rewrite /mxdiag mxblockEh mul_mxrow_mxcol.
under [LHS]eq_bigr do rewrite mxcol_mul; rewrite -mxcol_sum.
apply/eq_mxcol => i; rewrite (bigD1 i)//= eqxx conform_mx_id big1 ?addr0//.
by move=> j; case: eqVneq => //=; rewrite mul0mx.
Qed.

End SquareBlockMatrixRing.

Lemma mul_mxrow_mxdiag {R : ringType} {p : nat} {p_ : 'I_p -> nat} m
    (R_ : forall i, 'M[R]_(m, p_ i)) (D_ : forall i, 'M[R]_(p_ i)) :
  \mxrow_i R_ i *m \mxdiag_i D_ i = \mxrow_i (R_ i *m D_ i).
Proof.
apply: trmx_inj; rewrite trmx_mul_rev !tr_mxrow tr_mxdiag mul_mxdiag_mxcol.
by apply/ eq_mxcol => i; rewrite trmx_mul_rev.
Qed.

Lemma mul_mxblock_mxdiag {R : ringType} {p q : nat}
  {p_ : 'I_p -> nat} {q_ : 'I_q -> nat}
    (B_ : forall i j, 'M[R]_(p_ i, q_ j)) (D_ : forall j, 'M[R]_(q_ j)) :
  \mxblock_(i, j) B_ i j *m \mxdiag_j D_ j = \mxblock_(i, j) (B_ i j *m D_ j).
Proof.
by rewrite !mxblockEh mul_mxrow_mxdiag; under eq_mxrow do rewrite mxcol_mul.
Qed.

Lemma mul_mxdiag_mxblock {R : ringType} {p q : nat}
  {p_ : 'I_p -> nat} {q_ : 'I_q -> nat}
    (D_ : forall j, 'M[R]_(p_ j)) (B_ : forall i j, 'M[R]_(p_ i, q_ j)):
  \mxdiag_j D_ j *m \mxblock_(i, j) B_ i j = \mxblock_(i, j) (D_ i *m B_ i j).
Proof.
by rewrite !mxblockEv mul_mxdiag_mxcol; under eq_mxcol do rewrite mul_mxrow.
Qed.

Definition Vandermonde (R : ringType) (m n : nat) (a : 'rV[R]_n) :=
  \matrix_(i < m, j < n) a 0 j ^+ i.

Lemma det_Vandermonde (R : comRingType) (n : nat) (a : 'rV[R]_n) :
  \det (Vandermonde n a) = \prod_(i < n) \prod_(j < n | i < j) (a 0 j - a 0 i).
Proof.
set V := @Vandermonde R.
elim: n => [|n IHn] in a *; first by rewrite det_mx00 big1// => -[] [].
pose b : 'rV_n := \row_i a 0 (lift 0 i).
pose C : 'M_n := diag_mx (\row_(i < n) (b 0 i - a 0 0)).
pose D : 'M_n.+1 := 1 - a 0 0 *: \matrix_(i, j) (i == j.+1 :> nat)%:R. 
have detD : \det D = 1.
  rewrite det_trig ?big_ord_recl ?mxE ?mulr0 ?subr0 ?eqxx.
    by rewrite ?big1 ?mulr1// => i; rewrite !mxE eqxx ltn_eqF// mulr0 subr0.
  by apply/is_trig_mxP => *; rewrite !mxE ![_ == _]ltn_eqF ?mulr0 ?subr0 ?leqW.
suff: D * V _ _ a = block_mx 1 (const_mx 1) 0 (V _ _ b *m C) :> 'M_(1 + n).
  move=> /(congr1 determinant); rewrite detM detD mul1r => ->.
  rewrite det_ublock det1 mul1r det_mulmx IHn big_ord_recl mulrC; congr (_ * _).
    rewrite big_mkcond big_ord_recl/= mul1r det_diag.
    by under eq_bigr do rewrite !mxE.
  apply: eq_bigr => i _; under eq_bigr do rewrite !mxE.
  by rewrite big_mkcond [RHS]big_mkcond big_ord_recl/= mul1r.
rewrite mulrBl mul1r -scalerAl; apply/matrixP => i j; rewrite !mxE.
under eq_bigr do rewrite !mxE; case: splitP => [{i}_ -> /[!ord1]|{}i ->].
  rewrite !expr0 big1; last by move=> ?; rewrite mul0r.
  by rewrite ?mulr0 ?subr0 ?mxE; case: splitP => k; rewrite ?ord1 mxE//.
under eq_bigr do rewrite eqSS mulr_natl mulrb eq_sym.
rewrite -big_mkcond/= big_ord1_eq exprS ifT// ?leqW// -mulrBl !mxE/=.
case: split_ordP => [{j}_ -> /[!ord1]|{}j ->]; rewrite ?lshift0 ?rshift1 ?mxE.
   by rewrite ?subrr ?mul0r//.
under eq_bigr do rewrite !mxE mulrnAr mulrb.
by rewrite -big_mkcond big_pred1_eq /= mulrC.
Qed.

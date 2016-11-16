(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype.
From mathcomp
Require Import bigop ssralg matrix zmodp div.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope nat_scope.
Local Open Scope ring_scope.

Section ExtraBigOp.

Lemma sumr_add : forall (R : ringType) m n (F : 'I_(m + n) -> R),
  \sum_(i < m + n) F i = \sum_(i < m) F (lshift _ i)
  + \sum_(i < n) F (rshift _ i).
Proof.
move=> R; elim=> [|m ihm] n F.
  rewrite !big_ord0 add0r; apply: congr_big=> // [[i hi]] _.
  by rewrite /rshift /=; congr F; apply: val_inj.
rewrite !big_ord_recl ihm -addrA.
congr (_ + _); first by congr F; apply: val_inj.
congr (_ + _); by apply: congr_big=> // i _ /=; congr F; apply: val_inj.
Qed.

Lemma mxtens_index_proof m n (ij : 'I_m * 'I_n) : ij.1 * n + ij.2 < m * n.
Proof.
case: m ij=> [[[] //]|] m ij; rewrite mulSn addnC -addSn leq_add //.
by rewrite leq_mul2r; case: n ij=> // n ij; rewrite leq_ord orbT.
Qed.

Definition mxtens_index m n ij := Ordinal (@mxtens_index_proof m n ij).

Lemma mxtens_index_proof1 m n (k : 'I_(m * n)) : k %/ n < m.
Proof. by move: m n k=> [_ [] //|m] [|n] k; rewrite ?divn0 // ltn_divLR. Qed.
Lemma mxtens_index_proof2 m n (k : 'I_(m * n)) : k %% n < n.
Proof. by rewrite ltn_mod; case: n k=> //; rewrite muln0=> [] []. Qed.

Definition mxtens_unindex m n k :=
  (Ordinal (@mxtens_index_proof1 m n k), Ordinal (@mxtens_index_proof2 m n k)).

Implicit Arguments mxtens_index [[m] [n]].
Implicit Arguments mxtens_unindex [[m] [n]].

Lemma mxtens_indexK m n : cancel (@mxtens_index m n) (@mxtens_unindex m n).
Proof.
case: m=> [[[] //]|m]; case: n=> [[_ [] //]|n].
move=> [i j]; congr (_, _); apply: val_inj=> /=.
  by rewrite divnMDl // divn_small.
by rewrite modnMDl // modn_small.
Qed.

Lemma mxtens_unindexK m n : cancel (@mxtens_unindex m n) (@mxtens_index m n).
Proof.
case: m=> [[[] //]|m]. case: n=> [|n] k.
  by suff: False by []; move: k; rewrite muln0=> [] [].
by apply: val_inj=> /=; rewrite -divn_eq.
Qed.

CoInductive is_mxtens_index (m n : nat) : 'I_(m * n) -> Type :=
    IsMxtensIndex : forall (i : 'I_m) (j : 'I_n),
                   is_mxtens_index (mxtens_index (i, j)).

Lemma mxtens_indexP (m n : nat) (k : 'I_(m * n)) : is_mxtens_index k.
Proof. by rewrite -[k]mxtens_unindexK; constructor. Qed.

Lemma mulr_sum (R : ringType) m n (Fm : 'I_m -> R) (Fn : 'I_n -> R) :
  (\sum_(i < m) Fm i) * (\sum_(i < n) Fn i)
  = \sum_(i < m * n) ((Fm (mxtens_unindex i).1) * (Fn (mxtens_unindex i).2)).
Proof.
rewrite mulr_suml; transitivity (\sum_i (\sum_(j < n) Fm i * Fn j)).
  by apply: eq_big=> //= i _; rewrite -mulr_sumr.
rewrite pair_big; apply: reindex=> //=.
by exists mxtens_index=> i; rewrite (mxtens_indexK, mxtens_unindexK).
Qed.

End ExtraBigOp.

Section ExtraMx.

Lemma castmx_mul (R : ringType)
  (m m' n p p': nat) (em : m = m') (ep : p = p')
  (M : 'M[R]_(m, n)) (N : 'M[R]_(n, p)) :
  castmx (em, ep) (M *m N) = castmx (em, erefl _) M *m castmx (erefl _, ep) N.
Proof. by case: m' / em; case: p' / ep. Qed.

Lemma mulmx_cast (R : ringType)
  (m n n' p p' : nat) (en : n' = n) (ep : p' = p)
  (M : 'M[R]_(m, n)) (N : 'M[R]_(n', p')) :
  M *m (castmx (en, ep) N) =
  (castmx (erefl _, (esym en)) M) *m (castmx (erefl _, ep) N).
Proof. by case: n / en in M *; case: p / ep in N *. Qed.

Lemma castmx_row (R : Type) (m m' n1 n2 n1' n2' : nat)
  (eq_n1 : n1 = n1') (eq_n2 : n2 = n2') (eq_n12 : (n1 + n2 = n1' + n2')%N)
  (eq_m : m = m') (A1 : 'M[R]_(m, n1)) (A2 : 'M_(m, n2)) :
  castmx (eq_m, eq_n12) (row_mx A1 A2) =
  row_mx (castmx (eq_m, eq_n1) A1) (castmx (eq_m, eq_n2) A2).
Proof.
case: _ / eq_n1 in eq_n12 *; case: _ / eq_n2 in eq_n12 *.
by case: _ / eq_m; rewrite castmx_id.
Qed.

Lemma castmx_col (R : Type) (m m' n1 n2 n1' n2' : nat)
  (eq_n1 : n1 = n1') (eq_n2 : n2 = n2') (eq_n12 : (n1 + n2 = n1' + n2')%N)
  (eq_m : m = m') (A1 : 'M[R]_(n1, m)) (A2 : 'M_(n2, m)) :
  castmx (eq_n12, eq_m) (col_mx A1 A2) =
  col_mx (castmx (eq_n1, eq_m) A1) (castmx (eq_n2, eq_m) A2).
Proof.
case: _ / eq_n1 in eq_n12 *; case: _ / eq_n2 in eq_n12 *.
by case: _ / eq_m; rewrite castmx_id.
Qed.

Lemma castmx_block (R : Type) (m1 m1' m2 m2' n1 n2 n1' n2' : nat)
  (eq_m1 : m1 = m1') (eq_n1 : n1 = n1') (eq_m2 : m2 = m2') (eq_n2 : n2 = n2')
  (eq_m12 : (m1 + m2 = m1' + m2')%N) (eq_n12 : (n1 + n2 = n1' + n2')%N)
  (ul : 'M[R]_(m1, n1)) (ur : 'M[R]_(m1, n2))
  (dl : 'M[R]_(m2, n1)) (dr : 'M[R]_(m2, n2)) :
  castmx (eq_m12, eq_n12) (block_mx ul ur dl dr) =
  block_mx (castmx (eq_m1, eq_n1) ul) (castmx (eq_m1, eq_n2) ur)
  (castmx (eq_m2, eq_n1) dl) (castmx (eq_m2, eq_n2) dr).
Proof.
case: _ / eq_m1 in eq_m12 *; case: _ / eq_m2 in eq_m12 *.
case: _ / eq_n1 in eq_n12 *; case: _ / eq_n2 in eq_n12 *.
by rewrite !castmx_id.
Qed.

End ExtraMx.

Section MxTens.

Variable R : ringType.

Definition tensmx {m n p q : nat}
  (A : 'M_(m, n)) (B : 'M_(p, q)) : 'M[R]_(_,_) := nosimpl
  (\matrix_(i, j) (A (mxtens_unindex i).1 (mxtens_unindex j).1
                 * B (mxtens_unindex i).2 (mxtens_unindex j).2)).

Notation "A *t B" := (tensmx A B)
  (at level 40, left associativity, format "A  *t  B").

Lemma tensmxE {m n p q} (A : 'M_(m, n)) (B : 'M_(p, q)) i j k l :
  (A *t B) (mxtens_index (i, j)) (mxtens_index (k, l)) = A i k * B j l.
Proof. by rewrite !mxE !mxtens_indexK. Qed.

Lemma tens0mx {m n p q} (M : 'M[R]_(p,q)) : (0 : 'M_(m,n)) *t M = 0.
Proof. by apply/matrixP=> i j; rewrite !mxE mul0r. Qed.

Lemma tensmx0 {m n p q} (M : 'M[R]_(m,n)) : M *t (0 : 'M_(p,q)) = 0.
Proof. by apply/matrixP=> i j; rewrite !mxE mulr0. Qed.

Lemma tens_scalar_mx (m n : nat) (c : R) (M : 'M_(m,n)):
  c%:M *t M = castmx (esym (mul1n _), esym (mul1n _)) (c *: M).
Proof.
apply/matrixP=> i j.
case: (mxtens_indexP i)=> i0 i1; case: (mxtens_indexP j)=> j0 j1.
rewrite tensmxE [i0]ord1 [j0]ord1 !castmxE !mxE /= mulr1n.
by congr (_ * M _ _); apply: val_inj.
Qed.

Lemma tens_scalar1mx (m n : nat) (M : 'M_(m,n)) :
  1 *t M = castmx (esym (mul1n _), esym (mul1n _)) M.
Proof. by rewrite tens_scalar_mx scale1r. Qed.

Lemma tens_scalarN1mx (m n : nat) (M : 'M_(m,n)) :
  (-1) *t M = castmx (esym (mul1n _), esym (mul1n _)) (-M).
Proof. by rewrite [-1]mx11_scalar /= tens_scalar_mx !mxE scaleNr scale1r. Qed.

Lemma trmx_tens {m n p q} (M :'M[R]_(m,n)) (N : 'M[R]_(p,q)) :
  (M *t N)^T = M^T *t N^T.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma tens_col_mx {m n p q} (r : 'rV[R]_n)
  (M :'M[R]_(m, n)) (N : 'M[R]_(p, q)) :
  (col_mx r M) *t N =
  castmx (esym (mulnDl _ _ _), erefl _) (col_mx (r *t N) (M *t N)).
Proof.
apply/matrixP=> i j.
case: (mxtens_indexP i)=> i0 i1; case: (mxtens_indexP j)=> j0 j1.
rewrite !tensmxE castmxE /= cast_ord_id esymK !mxE /=.
case: splitP=> i0' /= hi0'; case: splitP=> k /= hk.
+ case: (mxtens_indexP k) hk=> k0 k1 /=; rewrite tensmxE.
  move=> /(f_equal (edivn^~ p)); rewrite !edivn_eq // => [] [h0 h1].
  by congr (r _ _ * N _ _); apply:val_inj; rewrite /= -?h0 ?h1.
+ move: hk (ltn_ord i1); rewrite hi0'.
  by rewrite [i0']ord1 mul0n mul1n add0n ltnNge=> ->; rewrite leq_addr.
+ move: (ltn_ord k); rewrite -hk hi0' ltnNge {1}mul1n.
  by rewrite mulnDl {1}mul1n -addnA leq_addr.
case: (mxtens_indexP k) hk=> k0 k1 /=; rewrite tensmxE.
rewrite hi0' mulnDl -addnA=> /addnI.
 move=> /(f_equal (edivn^~ p)); rewrite !edivn_eq // => [] [h0 h1].
by congr (M _ _ * N _ _); apply:val_inj; rewrite /= -?h0 ?h1.
Qed.

Lemma tens_row_mx {m n p q} (r : 'cV[R]_m) (M :'M[R]_(m,n)) (N : 'M[R]_(p,q)) :
  (row_mx r M) *t N =
  castmx (erefl _, esym (mulnDl _ _ _)) (row_mx (r *t N) (M *t N)).
Proof.
rewrite -[_ *t _]trmxK trmx_tens tr_row_mx tens_col_mx.
apply/eqP; rewrite -(can2_eq (castmxKV _ _) (castmxK _ _)); apply/eqP.
by rewrite trmx_cast castmx_comp castmx_id tr_col_mx -!trmx_tens !trmxK.
Qed.

Lemma tens_block_mx {m n p q}
  (ul : 'M[R]_1) (ur : 'rV[R]_n) (dl : 'cV[R]_m)
  (M :'M[R]_(m,n)) (N : 'M[R]_(p,q)) :
  (block_mx ul ur dl M) *t N =
  castmx (esym (mulnDl _ _ _), esym (mulnDl _ _ _))
  (block_mx (ul *t N) (ur *t N) (dl *t N) (M *t N)).
Proof.
rewrite !block_mxEv tens_col_mx !tens_row_mx -!cast_col_mx castmx_comp.
by congr (castmx (_,_)); apply nat_irrelevance.
Qed.


Fixpoint ntensmx_rec {m n} (A : 'M_(m,n)) k : 'M_(m ^ k.+1,n ^ k.+1) :=
  if k is k'.+1 then (A *t (ntensmx_rec A k')) else A.

Definition ntensmx {m n} (A : 'M_(m, n)) k := nosimpl
  (if k is k'.+1 return 'M[R]_(m ^ k,n ^ k) then ntensmx_rec A k' else 1).

Notation "A ^t k" := (ntensmx A k)
  (at level 39, left associativity, format "A  ^t  k").

Lemma ntensmx0 : forall {m n} (A : 'M_(m,n)) , A ^t 0 = 1.
Proof. by []. Qed.

Lemma ntensmx1 : forall {m n} (A : 'M_(m,n)) , A ^t 1 = A.
Proof. by []. Qed.

Lemma ntensmx2 : forall {m n} (A : 'M_(m,n)) , A ^t 2 = A *t A.
Proof. by []. Qed.

Lemma ntensmxSS : forall {m n} (A : 'M_(m,n)) k, A ^t k.+2 = A *t A ^t k.+1.
Proof. by []. Qed.

Definition ntensmxS := (@ntensmx1, @ntensmx2, @ntensmxSS).

End MxTens.

Notation "A *t B" := (tensmx A B)
  (at level 40, left associativity, format "A  *t  B").

Notation "A ^t k" := (ntensmx A k)
  (at level 39, left associativity, format "A  ^t  k").

Section MapMx.
Variables (aR rR : ringType).
Hypothesis f : {rmorphism aR -> rR}.
Local Notation "A ^f" := (map_mx f A) : ring_scope.

Variables m n p q: nat.
Implicit Type A : 'M[aR]_(m, n).
Implicit Type B : 'M[aR]_(p, q).

Lemma map_mxT A B : (A *t B)^f = A^f *t B^f :> 'M_(m*p, n*q).
Proof. by apply/matrixP=> i j; rewrite !mxE /= rmorphM. Qed.

End MapMx.

Section Misc.

Lemma tensmx_mul (R : comRingType) m n p q r s
  (A : 'M[R]_(m,n)) (B : 'M[R]_(p,q)) (C : 'M[R]_(n, r)) (D : 'M[R]_(q, s)) :
  (A *t B) *m (C *t D) = (A *m C) *t (B *m D).
Proof.
apply/matrixP=> /= i j.
case (mxtens_indexP i)=> [im ip] {i}; case (mxtens_indexP j)=> [jr js] {j}.
rewrite !mxE !mxtens_indexK mulr_sum; apply: congr_big=> // k _.
by rewrite !mxE !mxtens_indexK mulrCA !mulrA [C _ _ * A _ _]mulrC.
Qed.

(* Todo : move to div ? *)
Lemma eq_addl_mul q q' m m' d : m < d -> m' < d ->
  (q * d + m == q' * d  + m')%N = ((q, m) == (q', m')).
Proof.
move=> lt_md lt_m'd; apply/eqP/eqP; last by move=> [-> ->].
by move=> /(f_equal (edivn^~ d)); rewrite !edivn_eq.
Qed.

Lemma tensmx_unit (R : fieldType) m n (A : 'M[R]_m%N) (B : 'M[R]_n%N) :
  m != 0%N -> n != 0%N -> A \in unitmx -> B \in unitmx -> (A *t B) \in unitmx.
Proof.
move: m n A B => [|m] [|n] // A B _ _ uA uB.
suff : (A^-1 *t B^-1) *m (A *t B) = 1 by case/mulmx1_unit.
rewrite tensmx_mul !mulVmx //; apply/matrixP=> /= i j.
rewrite !mxE /=; symmetry; rewrite -natrM -!val_eqE /=.
rewrite {1}(divn_eq i n.+1) {1}(divn_eq j n.+1).
by rewrite eq_addl_mul ?ltn_mod // xpair_eqE mulnb.
Qed.


Lemma tens_mx_scalar : forall (R : comRingType)
  (m n : nat) (c : R) (M : 'M[R]_(m,n)),
  M *t c%:M = castmx (esym (muln1 _), esym (muln1 _)) (c *: M).
Proof.
move=> R0 m n c M; apply/matrixP=> i j.
case: (mxtens_indexP i)=> i0 i1; case: (mxtens_indexP j)=> j0 j1.
rewrite tensmxE [i1]ord1 [j1]ord1 !castmxE !mxE /= mulr1n mulrC.
by congr (_ * M _ _); apply: val_inj=> /=; rewrite muln1 addn0.
Qed.

Lemma tensmx_decr : forall (R : comRingType) m n (M :'M[R]_m) (N : 'M[R]_n),
  M *t N = (M *t 1%:M) *m (1%:M *t N).
Proof. by move=> R0 m n M N; rewrite tensmx_mul mul1mx mulmx1. Qed.

Lemma tensmx_decl : forall (R : comRingType) m n (M :'M[R]_m) (N : 'M[R]_n),
  M *t N = (1%:M *t N) *m (M *t 1%:M).
Proof. by move=> R0 m n M N; rewrite tensmx_mul mul1mx mulmx1. Qed.

End Misc.

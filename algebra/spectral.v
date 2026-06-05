From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype bigop nmodule order.
From mathcomp Require Import rings_modules_and_algebras divalg poly polydiv.
From mathcomp Require Import matrix.
From mathcomp Require Import mxalgebra mxpoly mxred orderedzmod numdomain.
From mathcomp Require Import numfield sesquilinear.

(******************************************************************************)
(*                             Spectral theory                                *)
(*                                                                            *)
(* This file provides a formalization of Gram-Schmidt orthonormalization,     *)
(* Schur decomposition, etc.                                                  *)
(*                                                                            *)
(*                 M ^t* := M ^t conjC                                        *)
(*                           Notation in scope sesquilinear_scope.            *)
(*       M \is unitarymx == M is a unitary matrix                             *)
(*                          M : 'M[C]_(m, n) with C : numClosedFieldType      *)
(*        M \is normalmx == M is a normal matrix                              *)
(*                          M : 'M[C]_n with C : numClosedFieldType           *)
(*                                                                            *)
(*             dotmx u v == dot product                                       *)
(*                          u and v are row vectors over a numClosedFieldType *)
(*                          Local notations: '[u, v] := dotmx u v,            *)
(*                          '[u] := '[u, u]                                   *)
(*          proj_ortho Y := proj_mx <<U>>%MS U^!%MS                           *)
(*                          where U^! is a 1-orthogonal completement of U     *)
(*             schmidt A == Gram-Schmidt basis                                *)
(*                          A : 'M[C]_(m, n)                                  *)
(*    schmidt_complete V := col_mx (schmidt (row_base V))                     *)
(*                                 (schmidt (row_base V^!%MS))                *)
(* spectralmx A, spectral_diag A == (M,X) s.t. A = M^-1 *m diag_mx X *m M     *)
(*                          A : 'M[C]_n                                       *)
(*        realsubfield C == the real subfield of a numClosedFieldType C,      *)
(*                          endowed with an rcfType structure (the real       *)
(*                          closed subfield of C).                            *)
(* real_spectral_theorem == real symmetric matrices are orthogonally          *)
(*                          diagonalizable                                    *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Order.Theory Num.Theory Num.Def.
Local Open Scope ring_scope.
Local Open Scope sesquilinear_scope.

(** TODO: move? **)
Lemma eigenvalue_closed {C : numClosedFieldType} n (A : 'M[C]_n) : (n > 0)%N ->
  exists a, eigenvalue A a.
Proof.
move=> n_gt0; have /closed_rootP [a rAa] : size (char_poly A) != 1%N.
  by rewrite size_char_poly; case: (n) n_gt0.
by exists a; rewrite eigenvalue_root_char.
Qed.

(** TODO: move? **)
Lemma common_eigenvector {C : numClosedFieldType} n (As : seq 'M[C]_n) :
  (n > 0)%N -> {in As &, forall A B, comm_mx A B} ->
  exists2 v : 'rV_n, v != 0 & all (fun A => stablemx v A) As.
Proof.
move=> n_gt0 /all_comm_mxP; have [k sAsk] := ubnP (size As).
elim: k n n_gt0 As sAsk => [//|k IHk]  n n_gt0 [|A As].
  exists (const_mx 1) => //; apply/negP => /eqP/rowP/(_ (Ordinal n_gt0)).
  by rewrite !mxE => /eqP; rewrite oner_eq0.
rewrite ltnS all_comm_mx_cons => sAsk /andP[].
move=> /allP/(_ _ _)/eqP/= A_comm /all_comm_mxP As_comm.
have [a a_eigen] := eigenvalue_closed A n_gt0.
have [] := IHk _ _ [seq restrictmx (eigenspace A a) B | B <- As].
- by rewrite lt0n mxrank_eq0.
- by rewrite size_map.
- apply/all_comm_mxP; move=> _ _ /= /mapP /= [B B_in ->] /mapP /= [B' B'_in ->].
  rewrite -?conjmxM ?inE ?stablemx_row_base ?comm_mx_stable_eigenspace//;
  by [rewrite As_comm | apply: As_comm | apply: A_comm].
move=> v vN0 /allP /= vP; exists (v *m (row_base (eigenspace A a))).
  by rewrite mulmx_free_eq0 ?row_base_free.
apply/andP; split.
  by apply/eigenvectorP; exists a; rewrite mulmx_sub // eq_row_base.
apply/allP => B B_in; rewrite -stablemx_restrict ?vP //; last first.
  by apply/mapP; exists B.
by rewrite comm_mx_stable_eigenspace //; exact: A_comm.
Qed.

(** TODO: move? **)
Lemma common_eigenvector2 {C : numClosedFieldType}n  (A B : 'M[C]_n) :
  (n > 0)%N -> A *m B = B *m A ->
  exists2 v : 'rV_n, v != 0 & (stablemx v A) && (stablemx v B).
Proof.
move=> n_gt0 AB_comm; have [] := @common_eigenvector _ _ [:: A; B] n_gt0.
  by move=> A' B'; rewrite !inE => /orP [] /eqP-> /orP [] /eqP->.
by move=> v v_neq0 /allP vP; exists v; rewrite ?vP ?(mem_head, in_cons, orbT).
Qed.

Notation "M ^t*" := (M ^t conjC) (at level 29, left associativity)
  : sesquilinear_scope.
Notation realmx := (mxOver Num.real).

Lemma trmxCK {C : conjFieldType} m n (A : 'M[C]_(m, n)) : A ^t* ^t* = A.
Proof. by apply/matrixP=> i j; rewrite !mxE conjCK. Qed.

Section realmx.
Context {C : numClosedFieldType} {m n : nat}.
Implicit Types A B : 'M[C]_(m, n).

Lemma realmxC A : A \is a realmx -> A ^ conjC = A.
Proof.
by move=> ?; apply/matrixP => x y; rewrite mxE; exact/CrealP/mxOverP.
Qed.

Lemma realmxD A B : A \is a realmx -> B \is a realmx -> A + B \is a realmx.
Proof.
rewrite !qualifE/= => /'forall_forallP realA /'forall_forallP realB.
by apply/'forall_forallP => i j; rewrite mxE realD.
Qed.

Lemma Remx_rect : {in realmx &, forall A B, (A + 'i *: B) ^ (@Re _) = A}.
Proof.
move=> A B Areal Breal; apply/matrixP=> i j; rewrite !mxE.
by rewrite Re_rect // (mxOverP _ _).
Qed.

Lemma Immx_rect : {in realmx &, forall A B, (A + 'i *: B) ^ (@Im _) = B}.
Proof.
move=> /= A B Areal Breal; apply/matrixP=> i j; rewrite !mxE.
by rewrite Im_rect // (mxOverP _ _).
Qed.

Lemma eqmx_ReiIm A B A' B' :
  A \is a realmx -> B \is a realmx -> A' \is a realmx -> B' \is a realmx ->
  (A + 'i *: B) = (A' + 'i *: B') -> (A, B) = (A', B').
Proof.
move=> ARe BRe A'Im B'Im eqAB.
have /(congr1 (fun A => A ^ (@Im _))) := eqAB.
have /(congr1 (fun A => A ^ (@Re _))) := eqAB.
by rewrite !Remx_rect// !Immx_rect// => -> ->.
Qed.

End realmx.

Lemma realsym_hermsym {C : numClosedFieldType} {n} (A : 'M[C]_n) :
  A \is symmetricmx -> A \is a realmx -> A \is hermsymmx.
Proof.
move=> Asym Areal; apply/is_hermitianmxP.
by rewrite (trmx_hermitian (HermitianMx Asym))/= !scale1r ?realmxC ?map_mx_id.
Qed.

Lemma real_similar {C : numClosedFieldType} {n} (A B : 'M[C]_n) :
  similar_in unitmx A B ->
  A \is a realmx -> B \is a realmx -> similar_in [predI realmx & unitmx] A B.
Proof.
case=> [P /=]; pose Pr := P ^ (@Re _); pose Pi := P ^ (@Im _).
have Pr_real : Pr \is a realmx by apply/mxOverP=> i j; rewrite !mxE Creal_Re.
have Pi_real : Pi \is a realmx by apply/mxOverP=> i j; rewrite !mxE Creal_Im.
pose Q x := P ^ (@Re _) + x *: P ^ (@Im _).
have -> : P = Q 'i by apply/matrixP=> i j; rewrite !mxE -Crect.
move=> Qi_unit eq_AP_PB Areal Breal.
pose p := \det (Pr ^ polyC + 'X *: Pi ^ polyC).
have horner_evaliC x : horner_eval (x : C) \o polyC =1 id := fun=> hornerC _ _.
have Qunit x : (Q x \in unitmx) = (p.[x] != 0).
  rewrite /p -horner_evalE -det_map_mx map_mxD map_mxZ/= horner_evalE hornerX.
  by rewrite -![(_ ^ polyC) ^ _]map_mx_comp !map_mx_id// unitmxE unitfE.
have p_neq0 : p != 0.
  by move: Qi_unit; rewrite Qunit; apply: contra_neq => ->; rewrite hornerE.
have [a a_real rootNa] : exists2 a, a \is Num.real &  ~~ root p a.
  have rs_uniq : uniq [seq (i%:R : C) | i <- iota 0 (size p)].
    by rewrite map_inj_uniq ?iota_uniq //; apply: mulrIn; rewrite oner_eq0.
  have := contraNN (fun x => max_poly_roots p_neq0 x rs_uniq).
  rewrite size_map size_iota ltnn => /(_ isT) /allPn[a a_in rootNpa].
  by exists a => //; by move: a_in => /mapP [i _ ->]; rewrite realn.
exists (Q a).
  rewrite inE Qunit rootNa andbT.
  rewrite /Q/=.
  by rewrite realmxD// mxOverZ.
apply/similarP; rewrite ?Qunit//; move: eq_AP_PB => /(similarP Qi_unit).
rewrite !mulmxDl !mulmxDr -!scalemxAr -!scalemxAl => /eqmx_ReiIm.
by rewrite !mxOverM// => /(_ isT isT isT isT) [-> ->].
Qed.

Section unitarymx.
Context {C : conjFieldType}.

Definition unitarymx {m n} := [qualify X : 'M[C]_(m, n) | X *m X ^t* == 1%:M].
Fact unitarymx_key m n : pred_key (@unitarymx m n). Proof. by []. Qed.
Canonical unitarymx_keyed m n := KeyedQualifier (unitarymx_key m n).

Lemma unitarymxP m n {M : 'M[C]_(m, n)} :
  reflect (M *m M^t* = 1%:M) (M \is unitarymx).
Proof. by apply: (iffP eqP). Qed.

Lemma mulmxtVK m1 m2 n (A : 'M[C]_(m1, n)) (B : 'M[C]_(n, m2)) :
  B \is unitarymx -> A *m B *m B^t* = A.
Proof. by move=> B_unitary; rewrite -mulmxA (unitarymxP _) ?mulmx1. Qed.

Lemma unitarymx_unit n (M : 'M[C]_n) : M \is unitarymx -> M \in unitmx.
Proof. by move=> /unitarymxP /mulmx1_unit []. Qed.

Lemma invmx_unitary n (M : 'M[C]_n) : M \is unitarymx -> invmx M = M^t*.
Proof.
move=> Munitary; apply: (@row_full_inj _ _ _ _ M).
  by rewrite row_full_unit unitarymx_unit.
by rewrite mulmxV ?unitarymx_unit ?(unitarymxP _).
Qed.

Lemma mulmxKtV m1 m2 n (A : 'M[C]_(m1, n)) (B : 'M[C]_(m2, n)) :
  B \is unitarymx -> m2 = n -> A *m B^t* *m B = A.
Proof.
move=> B_unitary m2E; case: _ / (esym m2E) in B B_unitary *.
by rewrite -invmx_unitary // mulmxKV //; exact: unitarymx_unit.
Qed.

Lemma mxrank_unitary m n (M : 'M[C]_(m, n)) : M \is unitarymx -> \rank M = m.
Proof.
rewrite qualifE => /eqP /(congr1 mxrank); rewrite mxrank1 => rkM.
apply/eqP; rewrite eqn_leq rank_leq_row /= -[X in (X <= _)%N]rkM.
by rewrite mxrankM_maxl.
Qed.

Lemma mul_unitarymx m n p (A : 'M[C]_(m, n)) (B : 'M[C]_(n, p)) :
  A \is unitarymx -> B \is unitarymx -> A *m B \is unitarymx.
Proof.
move=> Aunitary Bunitary; apply/unitarymxP; rewrite trmx_mul map_mxM.
by rewrite mulmxA -[A *m _ *m _]mulmxA !(unitarymxP _, mulmx1).
Qed.

Lemma pinvmx_unitary n (M : 'M[C]_n) : M \is unitarymx -> pinvmx M = M^t*.
Proof. by move=> Munitary; rewrite pinvmxE ?unitarymx_unit// invmx_unitary. Qed.

Lemma conjymx n (P M : 'M[C]_n) : P \is unitarymx -> conjmx P M = P *m M *m P^t*.
Proof. by move=> Munitary; rewrite conjumx ?invmx_unitary ?unitarymx_unit. Qed.

Lemma trmx_unitary n (M : 'M[C]_n) : (M ^T \is unitarymx) = (M \is unitarymx).
Proof.
apply/unitarymxP/unitarymxP; rewrite -?map_trmx -trmx_mul.
  by rewrite -trmx1 => /trmx_inj /mulmx1C->; rewrite trmx1.
by move=> /mulmx1C->; rewrite trmx1.
Qed.

Lemma conjC_unitary m n (M : 'M[C]_(m, n)) :
  (M ^ conjC \is unitarymx) = (M \is unitarymx).
Proof.
apply/unitarymxP/unitarymxP; rewrite -?map_mxM ?map_trmx; last first.
  by move=> ->; rewrite map_mx1.
by rewrite -[1%:M](map_mx1 conjC) => /map_mx_inj ->; rewrite map_mx1.
Qed.

Lemma trmxC_unitary n (M : 'M[C]_n) : (M ^t* \is unitarymx) = (M \is unitarymx).
Proof. by rewrite conjC_unitary trmx_unitary. Qed.

End unitarymx.

Section normalmx.
Context {C : numClosedFieldType} {n : nat}.

Definition normalmx := [qualify M : 'M[C]_n | M *m M ^t* == M ^t* *m M].
Fact normalmx_key : pred_key normalmx. Proof. by []. Qed.
Canonical normalmx_keyed := KeyedQualifier normalmx_key.

Lemma normalmxP {M : 'M[C]_n} :
  reflect (M *m M ^t* = M ^t* *m M) (M \is normalmx).
Proof. exact: eqP. Qed.

Lemma hermitian_normalmx (A : 'M[C]_n) : A \is hermsymmx -> A \is normalmx.
Proof.
move=> Ahermi; apply/normalmxP.
by rewrite (trmx_hermitian (HermitianMx Ahermi)) scale1r map_mxCK.
Qed.

Lemma symmetric_normalmx (A : 'M[C]_n) : A \is symmetricmx ->
  A \is a realmx -> A \is normalmx.
Proof. by move=> Asym Areal; rewrite hermitian_normalmx// realsym_hermsym. Qed.

End normalmx.

Local Notation dotmx_def := (form_of_matrix (@conjC _) 1%:M).
Definition dotmx (C : conjFieldType) n (u v : 'rV[C]_n) :=
  dotmx_def u%R v%R.

(* The flag spanned by the first i+1 rows of M is the row space of            *)
(* pid_mx i.+1 *m M (which selects those rows).                               *)
Local Lemma flag_pid_mx (R : fieldType) m n (M : 'M[R]_(m, n)) (i : 'I_m) :
  (\sum_(k < m | (k <= i)%N) <<row k M>> :=: (pid_mx i.+1 : 'M[R]_m) *m M)%MS.
Proof.
have rowkE (k : 'I_m) : (k <= i)%N -> row k (pid_mx i.+1 *m M) = row k M.
  move=> ki; rewrite row_mul.
  have -> : row k (pid_mx i.+1 : 'M[R]_m) = row k (1%:M : 'M[R]_m).
    by apply/rowP=> l; rewrite !mxE ltnS ki andbT.
  by rewrite row1 -rowE.
apply/eqmxP/andP; split.
  apply/sumsmx_subP => k ki; rewrite genmxE -(rowkE k ki); exact: row_sub.
apply/row_subP => k; rewrite row_mul.
have [ki|ki] := boolP (k <= i)%N.
  by rewrite -row_mul (rowkE k ki) (sumsmx_sup k) ?genmxE.
have rowk0 : row k (pid_mx i.+1 : 'M[R]_m) = 0.
  by apply/rowP=> l; rewrite !mxE ltnS (negPf ki) andbF.
by rewrite rowk0 mul0mx sub0mx.
Qed.

Section ConjSpectral.
Variable (C : conjFieldType).
Set Default Proof Using "C".

Lemma sqrtr_gt0_dnorm (a : C) : 0 <= a -> (0 < sqrtr a) = (0 < a).
Proof.
move=> a_ge0; rewrite lt0r sqrtr_ge0 lt0r a_ge0 !andbT.
by rewrite -(sqr_sqrtr a_ge0) sqrf_eq0 sqr_sqrtr.
Qed.

(**
TODO: bug report
without the lock we were expecting
HB.instance Definition _ n := Bilinear.on (@dotmx n).
to be sufficient to equip dotmx with the bilinear structure
but needed to use .copy in the end as in:

TODO: feature request
implement copy modulo lock

Lemma dotmx_bilinear n : isBilinear _ _ _ _ *%R (conjC \; *%R) (@dotmx C n).
Proof.
rewrite unlock; constructor => /= ?.
- exact: linearBl.
- exact: linearBr.
- exact: linearZl_LR.
- exact: linearZr_LR.
Qed.
HB.instance Definition _ n := dotmx_bilinear n.
**)

HB.instance Definition _ n := Bilinear.copy (@dotmx C n) (@dotmx C n).

Local Notation "''[' u , v ]" := (dotmx u v) : ring_scope.
Local Notation "''[' u ]" := '[u, u]%R : ring_scope.

Lemma dotmxE n (u v : 'rV[C]_n) : '[u, v] = ( u *m v ^t* ) 0 0.
Proof. by rewrite /dotmx unlock  mulmx1 /= trace_mx11. Qed.

Lemma row_unitarymxP m n {M : 'M[C]_(m, n)} :
  reflect (forall i j, '[row i M, row j M] = (i == j)%:R) (M \is unitarymx).
Proof.
apply: (iffP eqP) => [Mo i j|Mo].
  have /matrixP/(_ i j) := Mo; rewrite !mxE => <-.
  by rewrite dotmxE !mxE; apply: eq_bigr => /= k _; rewrite !mxE.
apply/matrixP=> i j; rewrite !mxE; have := Mo i j; rewrite dotmxE !mxE => <-.
by apply: eq_bigr => /= k _; rewrite !mxE.
Qed.

Fact dotmx_is_hermitian n : isHermitianSesquilinear _ _ false conjC (@dotmx C n).
Proof.
split=> /= u v; rewrite !dotmxE/= expr0 mul1r.
suff -> : u *m v ^t* = ((v *m u ^t* ) ^t* ) by rewrite !mxE.
by rewrite !trmx_mul map_mxM/= trmxCK.
Qed.
HB.instance Definition _ n := @dotmx_is_hermitian n.

Fact dotmx_is_dot n : isDotProduct _ _ (@dotmx C n).
Proof.
split => /= u u_neq0; rewrite dotmxE mxE.
suff /existsP[i ui_neq0] : [exists i, u 0%R i != 0].
  rewrite (bigD1 i) //= ltr_wpDr// ?sumr_ge0// ?mxE ?mul_conjC_gt0//.
  by move=> j _; rewrite !mxE mul_conjC_ge0.
apply: contraNT u_neq0; rewrite negb_exists => /forallP uNN0.
by apply/eqP/rowP=> j; rewrite mxE; apply/eqP; rewrite -[_ == _]negbK uNN0.
Qed.
HB.instance Definition _ n := (@dotmx_is_dot n).

Local Notation "B ^!" :=
  (orthomx conjC (mx_of_hermitian (hermitian1mx _)) B) :
    matrix_set_scope.
Local Notation "A '_|_ B" := (A%MS <= B^!)%MS : bool_scope.

Lemma orthomx1E m n p (A : 'M[C]_(m, n)) (B : 'M_(p, n)) :
  (A '_|_ B)%MS = (A *m B^t* == 0).
Proof. by apply/sub_kermxP/eqP; rewrite !mul1mx. Qed.

Lemma orthomx1P m n p {A : 'M[C]_(m, n)} {B : 'M_(p, n)} :
  reflect (A *m B^t* = 0) (A '_|_ B).
Proof. by rewrite orthomx1E; exact/eqP. Qed.

Lemma orthomx_disj n p q (A : 'M[C]_(p, n)) (B :'M_(q, n)) :
  A '_|_ B -> (A :&: B = 0)%MS.
Proof.
move=> nAB; apply/eqP/rowV0Pn => [[v]]; rewrite sub_capmx => /andP [vA vB].
apply/negP; rewrite negbK -(dnorm_eq0 (@dotmx C n)).
by rewrite -orthomxE (orthomxP _ _ _ nAB).
Qed.

Lemma orthomx_ortho_disj n p (A : 'M[C]_(p, n)) : (A :&: A^! = 0)%MS.
Proof. exact/orthomx_disj/ortho_mx_ortho. Qed.

Lemma rank_ortho p n (A : 'M[C]_(p, n)) : \rank A^! = (n - \rank A)%N.
Proof. by rewrite mxrank_ker mul1mx mxrank_map mxrank_tr. Qed.

Lemma add_rank_ortho p n (A : 'M[C]_(p, n)) : (\rank A + \rank A^!)%N = n.
Proof. by rewrite rank_ortho subnKC ?rank_leq_col. Qed.

Lemma addsmx_ortho p n (A : 'M[C]_(p, n)) : (A + A^! :=: 1%:M)%MS.
Proof.
apply/eqmxP/andP; rewrite submx1; split=> //.
rewrite -mxrank_leqif_sup ?submx1 ?mxrank1 ?(mxdirectP _) /= ?add_rank_ortho //.
by rewrite mxdirect_addsE /= ?mxdirectE ?orthomx_ortho_disj !eqxx.
Qed.

Lemma ortho_id p n (A : 'M[C]_(p, n)) : (A^!^! :=: A)%MS.
Proof.
apply/eqmx_sym/eqmxP.
by rewrite -mxrank_leqif_eq 1?orthomx_sym // !rank_ortho subKn // ?rank_leq_col.
Qed.

Lemma submx_ortho p m n (U : 'M[C]_(p, n)) (V : 'M_(m, n)) :
  (U^! <= V^!)%MS = (V <= U)%MS.
Proof. by rewrite orthomx_sym ortho_id. Qed.

Definition proj_ortho p n (U : 'M[C]_(p, n)) := proj_mx <<U>>%MS U^!%MS.

Lemma sub_adds_genmx_ortho (p m n : nat) (U : 'M[C]_(p, n))  (W : 'M_(m, n)) :
  (W <= <<U>> + U^!)%MS.
Proof.
by rewrite !(adds_eqmx (genmxE _) (eqmx_refl _)) addsmx_ortho submx1.
Qed.
Local Hint Resolve sub_adds_genmx_ortho : core.

Lemma cap_genmx_ortho p n (U : 'M[C]_(p, n)) : (<<U>> :&: U^!)%MS = 0.
Proof.
apply/eqmx0P; rewrite !(cap_eqmx (genmxE _) (eqmx_refl _)).
by rewrite orthomx_ortho_disj; exact/eqmx0P.
Qed.
Local Hint Resolve cap_genmx_ortho : core.

Lemma proj_ortho_sub p m n (U : 'M_(p, n)) (W : 'M_(m, n)) :
  (W *m proj_ortho U <= U)%MS.
Proof. by rewrite (submx_trans (proj_mx_sub _ _ _)) // genmxE. Qed.

Lemma proj_ortho_compl_sub p m n (U : 'M_(p, n)) (W : 'M_(m, n)) :
  (W - W *m proj_ortho U <= U^!)%MS.
Proof. by rewrite proj_mx_compl_sub // addsmx_ortho submx1. Qed.

Lemma proj_ortho_id p m n (U : 'M_(p, n)) (W : 'M_(m, n)) :
  (W <= U)%MS -> W *m proj_ortho U = W.
Proof. by move=> WU; rewrite proj_mx_id ?genmxE. Qed.

Lemma proj_ortho_0 p m n (U : 'M_(p, n)) (W : 'M_(m, n)) :
  (W <= U^!)%MS -> W *m proj_ortho U = 0.
Proof. by move=> WUo; rewrite proj_mx_0. Qed.

Lemma add_proj_ortho p m n (U : 'M_(p, n)) (W : 'M_(m, n)) :
  W *m proj_ortho U + W *m proj_ortho U^!%MS = W.
Proof.
rewrite -[W in LHS](@add_proj_mx _ _ _ <<U>>%MS U^!%MS W)//.
rewrite !mulmxDl proj_ortho_id ?proj_ortho_sub //.
rewrite [_ *m proj_mx U^!%MS _ *m proj_ortho U]proj_ortho_0 ?proj_mx_sub //.
rewrite addr0.
rewrite [_ *m proj_mx <<U>>%MS _ *m proj_ortho U^!%MS]proj_ortho_0
  ?ortho_id ?proj_ortho_sub // add0r.
by rewrite proj_ortho_id ?proj_mx_sub// add_proj_mx.
Qed.

Lemma proj_ortho_proj m n (U : 'M_(m, n)) : let P := proj_ortho U in P *m P = P.
Proof. by rewrite /= proj_mx_proj. Qed.

Lemma proj_orthoE p n (U : 'M_(p, n)) : (proj_ortho U :=: U)%MS.
Proof.
apply/eqmxP/andP; split; first by rewrite -proj_ortho_proj proj_ortho_sub.
by rewrite -[X in (X <= _)%MS](proj_ortho_id (submx_refl U)) mulmx_sub.
Qed.

Lemma orthomx_proj_mx_ortho p p' m m' n
  (A : 'M_(p, n)) (A' : 'M_(p', n))
  (W : 'M_(m, n)) (W' : 'M_(m', n)) :
  A '_|_ A' -> W *m proj_ortho A '_|_ W' *m proj_ortho A'.
Proof.
rewrite orthomx_sym => An.
rewrite mulmx_sub // orthomx_sym (eqmx_ortho _ (proj_orthoE _)).
by rewrite (submx_trans _ An) // proj_ortho_sub.
Qed.

Lemma schmidt_subproof m n (A : 'M[C]_(m, n)) : (m <= n)%N ->
  exists2 B : 'M_(m, n), B \is unitarymx & [forall i : 'I_m,
   (row i A <= (\sum_(k < m | (k <= i)%N) <<row k B>>))%MS
   && ('[row i A, row i B] >= 0) ].
Proof.
elim: m A => [|m IHm].
  exists (pid_mx n); first by rewrite qualifE !thinmx0.
  by apply/forallP=> -[].
rewrite -addn1 => A leq_Sm_n.
have lemSm : (m <= m + 1)%N by rewrite addn1.
have ltmSm : (m < m + 1)%N by rewrite addn1.
have lemn : (m <= n)%N by rewrite ltnW // -addn1.
have [B Bortho] := IHm (usubmx A) lemn.
move=> /forallP /= subAB.
have [v /and4P [vBn v_neq0 dAv_ge0 dAsub]] :
  exists v, [&& B '_|_ v, v != 0, '[dsubmx A, v] >= 0 & (dsubmx A <= B + v)%MS].
  have := add_proj_ortho B (dsubmx A).
  set BoSn := (_ *m proj_ortho _^!%MS) => pBE.
  have [BoSn_eq0|BoSn_neq0] := eqVneq BoSn 0.
    rewrite BoSn_eq0 addr0 in pBE.
    have /rowV0Pn [v vBn v_neq0] : B^!%MS != 0.
      rewrite -mxrank_eq0 rank_ortho -lt0n subn_gt0.
      by rewrite mxrank_unitary // -addn1.
    rewrite orthomx_sym in vBn.
    exists v; rewrite vBn v_neq0 -pBE/=.
      rewrite ['[_, _]](hermmx_eq0P _ _) ?lexx //=.
        by rewrite (submx_trans _ vBn) // proj_ortho_sub.
      rewrite (submx_trans (proj_ortho_sub _ _)) //.
      by rewrite -{1}[B]addr0 addmx_sub_adds ?sub0mx.
  pose c := (sqrtr '[BoSn])^-1; have c_gt0 : c > 0.
    by rewrite invr_gt0 sqrtr_gt0_dnorm ?dnorm_ge0//
       lt_def ?dnorm_eq0 ?dnorm_ge0 BoSn_neq0.
  exists BoSn; apply/and4P; split => //.
  - by rewrite orthomx_sym ?proj_ortho_sub // /gtr_eqF.
  - rewrite -pBE linearDl/=.
    rewrite [X in X + '[_]](hermmx_eq0P _ _) ?add0r ?dnorm_ge0 //.
    by rewrite orthomx_proj_mx_ortho // orthomx_sym.
  - by rewrite -pBE addmx_sub_adds // proj_ortho_sub.
wlog nv_eq1 : v vBn v_neq0 dAv_ge0 dAsub / '[v] = 1.
  pose c := (sqrtr '[v])^-1.
  have c_gt0 : c > 0 by rewrite invr_gt0 sqrtr_gt0_dnorm ?dnorm_ge0// dnorm_gt0.
  have [c_ge0 c_eq0F] := (ltW c_gt0, gt_eqF c_gt0).
  move=> /(_ (c *: v)); apply.
  - by rewrite orthomxZ ?c_eq0F.
  - by rewrite scaler_eq0 c_eq0F.
  - by rewrite linearZr mulr_ge0 // conjC_ge0.
  - by rewrite (submx_trans dAsub) // addsmxS // eqmx_scale // c_eq0F.
  - rewrite dnormZ normfV ger0_norm ?sqrtr_ge0 ?dnorm_ge0 //.
    by rewrite exprVn sqr_sqrtr ?dnorm_ge0 ?mulVf // dnorm_eq0.
exists (col_mx B v).
  apply/row_unitarymxP => i j.
  case: (split_ordP i) (split_ordP j) => [] i' -> [] j' ->;
    rewrite eq_shift ?(rowKu, rowKd, row_id, ord1) -?val_eqE /=
            ?(row_unitarymxP _) //= ?addn0.
    by rewrite ['[_, _]](hermmx_eq0P _ _)//= (submx_trans _ vBn)// row_sub.
  rewrite ['[_, _]](hermmx_eq0P _ _)//= orthomx_sym (submx_trans _ vBn) //.
  exact: row_sub.
apply/forallP => i; case: (split_ordP i) => j -> /=.
  have /andP [sABj dot_gt0] := subAB j.
  rewrite rowKu -row_usubmx (submx_trans sABj) //=.
  rewrite (eq_rect _ (submx _) (submx_refl _)) //.
  rewrite [in RHS](reindex (lshift 1)) /=; last first.
    by apply: eq_bigr=> k k_le; rewrite rowKu.
  exists (fun k => insubd j k) => k; rewrite inE /= => le_kj;
  by apply/val_inj; rewrite /= insubdK // -topredE /= (leq_ltn_trans le_kj).
rewrite rowKd -row_dsubmx !row_id ord1 ?dAv_ge0 ?andbT {j} addn0.
rewrite (bigD1 (rshift _ ord0)) /= ?addn0 ?rowKd ?row_id // addsmxC.
rewrite (submx_trans dAsub) // addsmxS ?genmxE //.
apply/row_subP => j; apply/(sumsmx_sup (lshift _ j)) => //=.
  by rewrite ltnW ?ltn_ord //= -val_eqE /= addn0 ltn_eqF.
by rewrite rowKu genmxE.
Qed.

Definition schmidt m n (A : 'M[C]_(m, n)) :=
  if (m <= n)%N =P true is ReflectT le_mn
  then projT1 (sig2_eqW (schmidt_subproof A le_mn))
  else A.

Lemma schmidt_unitarymx m n (A : 'M[C]_(m, n)) : (m <= n)%N ->
  schmidt A \is unitarymx.
Proof. by rewrite /schmidt; case: eqP => // ?; case: sig2_eqW. Qed.
Hint Resolve schmidt_unitarymx : core.

Lemma row_schmidt_sub m n (A : 'M[C]_(m, n)) i :
  (row i A <= (\sum_(k < m | (k <= i)%N) <<row k (schmidt A)>>))%MS.
Proof.
rewrite /schmidt; case: eqP => // ?.
   by case: sig2_eqW => ? ? /= /forallP /(_ i) /andP[].
by apply/(sumsmx_sup i) => //; rewrite genmxE.
Qed.

Lemma form1_row_schmidt m n (A : 'M[C]_(m, n)) i :
  '[row i A, row i (schmidt A)] >= 0.
Proof.
rewrite /schmidt; case: eqP => // ?; rewrite ?dnorm_ge0 //.
by case: sig2_eqW => ? ? /= /forallP /(_ i) /andP[].
Qed.

Lemma schmidt_sub m n (A : 'M[C]_(m, n)) : (A <= schmidt A)%MS.
Proof.
apply/row_subP => i; rewrite (submx_trans (row_schmidt_sub _ _)) //.
by apply/sumsmx_subP => /= j le_ji; rewrite genmxE row_sub.
Qed.
Hint Resolve schmidt_sub : core.

Lemma eqmx_schmidt_full m n (A : 'M[C]_(m, n)) :
  row_full A -> (schmidt A :=: A)%MS.
Proof.
move=> Afull; apply/eqmx_sym/eqmxP; rewrite -mxrank_leqif_eq //.
by rewrite eqn_leq mxrankS //= (@leq_trans n) ?rank_leq_col ?col_leq_rank.
Qed.

Lemma eqmx_schmidt_free m n (A : 'M[C]_(m, n)) :
  row_free A -> (schmidt A :=: A)%MS.
Proof.
move=> Afree; apply/eqmx_sym/eqmxP; rewrite -mxrank_leqif_eq //.
by rewrite eqn_leq mxrankS //= (@leq_trans m) ?rank_leq_row // ?row_leq_rank.
Qed.

Definition schmidt_complete m n (V : 'M[C]_(m, n)) :=
  col_mx (schmidt (row_base V)) (schmidt (row_base V^!%MS)).

Lemma schmidt_complete_unitarymx m n (V : 'M[C]_(m, n)) :
  schmidt_complete V \is unitarymx.
Proof.
apply/unitarymxP; rewrite tr_col_mx map_row_mx mul_col_row.
rewrite !(unitarymxP _) ?schmidt_unitarymx ?rank_leq_col //.
move=> [:nsV]; rewrite !(orthomx1P _) -?scalar_mx_block //;
  [abstract: nsV|]; last by rewrite orthomx_sym.
by do 2!rewrite eqmx_schmidt_free ?eq_row_base ?row_base_free // orthomx_sym.
Qed.

(* The Gram-Schmidt change of basis A *m (schmidt A)^t* is lower triangular   *)
(* (it is the triangular matrix T such that A = T *m schmidt A).              *)
Lemma schmidt_trig m n (A : 'M[C]_(m, n)) : (m <= n)%N ->
  is_trig_mx (A *m (schmidt A)^t*).
Proof.
move=> mn; apply/is_trig_mxP => i j ij.
have UUt : schmidt A *m (schmidt A)^t* = 1%:M.
  apply/unitarymxP; exact: schmidt_unitarymx mn.
have /submxP[c cE] : (row i A <= (pid_mx i.+1 : 'M[C]_m) *m schmidt A)%MS.
  by rewrite -(flag_pid_mx (schmidt A) i); apply: row_schmidt_sub.
have -> : (A *m (schmidt A)^t*) i j = (row i A *m (schmidt A)^t*) 0 j.
  by symmetry; rewrite -row_mul; apply: mxE.
rewrite cE -2!mulmxA UUt mulmx1 mxE big1// => k _; rewrite mxE ltnS.
case: (leqP k i) => [ki|_]; last by rewrite andbF mulr0.
by rewrite andbT (ltn_eqF (leq_ltn_trans ki ij)) mulr0.
Qed.

End ConjSpectral.

Section Spectral.
Variable (C : numClosedFieldType).

Local Notation "''[' u , v ]" := (dotmx u v) : ring_scope.
Local Notation "''[' u ]" := '[u, u]%R : ring_scope.
Local Notation "B ^!" :=
  (orthomx conjC (mx_of_hermitian (hermitian1mx _)) B) :
    matrix_set_scope.
Local Notation "A '_|_ B" := (A%MS <= B^!)%MS : bool_scope.

Lemma cotrigonalization n (As : seq 'M[C]_n) :
  {in As &, forall A B, comm_mx A B} ->
  cotrigonalizable_in (@unitarymx C n n) As.
Proof.
elim: n {-2}n (leqnn n) As => [|N IHN] n.
  rewrite leqn0 => /eqP n_eq0.
  exists 1%:M; first by rewrite qualifE mul1mx trmx1 map_mx1.
  apply/allP => ? ?; apply/is_trig_mxP => i j.
  by suff: False by []; move: i; rewrite n_eq0 => -[].
rewrite leq_eqVlt => /predU1P [n_eqSN|/IHN//].
have /andP [n_gt0 n_small] : (n > 0)%N && (n - 1 <= N)%N.
  by rewrite n_eqSN /= subn1.
move=> As As_comm;
have [v vN0 /allP /= vP] := common_eigenvector n_gt0 As_comm.
suff: exists2 P : 'M[C]_(\rank v + \rank v^!, n), P \is unitarymx &
  all (fun A => is_trig_mx (P *m A *m ( P^t* ))) As.
  rewrite add_rank_ortho // => -[P P_unitary] /=; rewrite -invmx_unitary//.
  by under eq_all do rewrite -conjumx ?unitarymx_unit//; exists P.
pose S := schmidt_complete v.
pose r A := S *m A *m S^t*.
have vSvo X : stablemx v X ->
  schmidt (row_base v) *m X *m schmidt (row_base v^!%MS) ^t* = 0.
  move=> /eigenvectorP [a v_in].
  rewrite (eigenspaceP (_ : (_ <= _ a))%MS).
    by rewrite eqmx_schmidt_free ?row_base_free ?eq_row_base.
  rewrite -scalemxAl (orthomx1P _) ?scaler0 //.
  by do 2!rewrite eqmx_schmidt_free ?row_base_free ?eq_row_base // orthomx_sym.
have drrE X : drsubmx (r X) =
  schmidt (row_base v^!%MS) *m X *m schmidt (row_base v^!%MS) ^t*.
  by rewrite /r mul_col_mx tr_col_mx map_row_mx mul_col_row block_mxKdr.
have vSv X a : (v <= eigenspace X a)%MS ->
  schmidt (row_base v) *m X *m schmidt (row_base v) ^t* = a%:M.
  move=> vXa; rewrite (eigenspaceP (_ : (_ <= _ a)%MS)).
    by rewrite eqmx_schmidt_free ?row_base_free ?eq_row_base.
  by rewrite -scalemxAl (unitarymxP _) ?scalemx1 ?schmidt_unitarymx ?rank_leq_col.
have [] := IHN _ _ [seq drsubmx (r A) | A <- As].
- by rewrite rank_ortho rank_rV vN0.
- move=> _ _ /mapP[/= A A_in ->] /mapP[/= B B_in ->].
  have : (r A) *m (r B) = (r B) *m (r A).
    rewrite /r !mulmxA !mulmxKtV // ?schmidt_complete_unitarymx //;
    by rewrite ?add_rank_ortho // -![S *m _ *m _]mulmxA As_comm.
  rewrite -[r A in X in X -> _]submxK -[r B  in X in X -> _]submxK.
  rewrite 2!mulmx_block => /eq_block_mx [_ _ _].
  suff urr_eq0 X : X \in As -> ursubmx (r X) = 0.
    by rewrite !urr_eq0 ?mulmx0 ?add0r.
  rewrite /r /S ![schmidt_complete _ *m _]mul_col_mx.
  rewrite !tr_col_mx !map_row_mx !mul_col_row !block_mxKur.
  by move=> X_in; rewrite vSvo // vP.
move=> P' P'_unitary /allP /= P'P.
exists ((block_mx 1%:M 0 0 P') *m S).
  rewrite mul_unitarymx ?schmidt_complete_unitarymx //.
  apply/unitarymxP; rewrite tr_block_mx map_block_mx mulmx_block.
  rewrite !trmx0 !(@map_mx0 _ _ conjC) !tr_scalar_mx !map_scalar_mx/=.
  rewrite ?conjC1 !(mulmx1, mul1mx, mulmx0, mul0mx, addr0, add0r).
  by rewrite (unitarymxP _) -?scalar_mx_block.
apply/allP => /= A A_in.
rewrite trmx_mul map_mxM tr_block_mx map_block_mx.
rewrite !trmx0 !map_mx0 !tr_scalar_mx !map_scalar_mx/= ?conjC1.
rewrite mulmxA -[_ *m S *m _]mulmxA -[_ *m _ *m S^t*]mulmxA.
rewrite /S ![schmidt_complete _ *m _]mul_col_mx.
rewrite !tr_col_mx !map_row_mx !mul_col_row !mulmx_block.
rewrite !(mulmx1, mul1mx, mulmx0, mul0mx, addr0, add0r).
apply/is_trig_mxP => /= i j lt_ij; rewrite mxE.
case: splitP => //= i' i_eq; rewrite !mxE;
case: splitP => //= j' j_eq.
- have /vP /eigenvectorP [a v_in] := A_in.
  by rewrite (vSv _ _ v_in) mxE -val_eqE ltn_eqF //= -i_eq -j_eq.
- by rewrite vSvo ?mul0mx ?mxE // vP //.
- move: lt_ij; rewrite i_eq j_eq ltnNge -ltnS (leq_trans (ltn_ord j'))//.
  by rewrite -addnS leq_addr.
- set A' := _ *m A *m _; rewrite -invmx_unitary // -conjumx ?unitarymx_unit//.
  have /(_ _) /is_trig_mxP -> // := P'P A'; last first.
    by move: lt_ij; rewrite i_eq j_eq ltn_add2l.
  by apply/mapP; exists A; rewrite //= drrE.
Qed.

Theorem Schur n (A : 'M[C]_n) : (n > 0)%N ->
  trigonalizable_in (@unitarymx C n n) A.
Proof.
case: n => [//|n] in A * => _; have [] := @cotrigonalization _ [:: A].
  by move=> ? ? /=; rewrite !in_cons !orbF => /eqP-> /eqP->.
by move=> P P_unitary /=; rewrite andbT=> A_trigo; exists P.
Qed.

Lemma cotrigonalization2 n (A B : 'M[C]_n) : A *m B = B *m A ->
  exists2 P : 'M[C]_n, P \is unitarymx &
    similar_trig P A && similar_trig P B.
Proof.
move=> AB_comm; have [] := @cotrigonalization _ [:: A; B].
  by move=> ??; rewrite !inE => /orP[]/eqP->/orP[]/eqP->.
move=> P Punitary /allP /= PP; exists P => //.
by rewrite !PP ?(mem_head, in_cons, orbT).
Qed.

Theorem orthomx_spectral_subproof n {A : 'M[C]_n} : reflect
  (exists2 sp : 'M_n * 'rV_n,
                sp.1 \is unitarymx &
                A = invmx sp.1 *m diag_mx sp.2 *m sp.1)
  (A \is normalmx).
Proof.
apply: (iffP normalmxP); last first.
  move=> [[/= P D] P_unitary ->].
  rewrite !trmx_mul !map_mxM !mulmxA invmx_unitary //.
  rewrite !trmxCK ![_ *m P *m _]mulmxtVK //.
  by rewrite -[X in X *m P]mulmxA tr_diag_mx map_diag_mx diag_mxC mulmxA.
move=> /cotrigonalization2 [P Punitary /andP[]] PA PATC.
have Punit := unitarymx_unit Punitary.
suff: similar_diag P A.
  move=> /similar_diagPex[D] PAD; exists (P, D) => //=.
  by rewrite -conjVmx//; exact/similarLR.
apply/similar_diagPp => // i j; case: ltngtP => // [lt_ij|lt_ji] _.
  by have /is_trig_mxP-> := PA.
have /is_trig_mxP -/(_ j i lt_ji)/eqP := PATC.
rewrite !conjumx// invmx_unitary// -[P as X in X *m _]trmxCK.
by rewrite -!map_mxM -!trmx_mul mulmxA 2!mxE conjC_eq0 => /eqP.
Qed.

Definition spectralmx n (A : 'M[C]_n) : 'M[C]_n :=
  if @orthomx_spectral_subproof _ A is ReflectT P
  then (projT1 (sig2_eqW P)).1 else 1%:M.

Definition spectral_diag n (A : 'M[C]_n) : 'rV_n :=
  if @orthomx_spectral_subproof _ A is ReflectT P
  then (projT1 (sig2_eqW P)).2 else 0.

Lemma spectral_unitarymx n (A : 'M[C]_n) : spectralmx A \is unitarymx.
Proof.
rewrite /spectralmx; case: orthomx_spectral_subproof; last first.
  by move=> _; apply/unitarymxP; rewrite trmx1 map_mx1 mulmx1.
by move=> ?; case: sig2_eqW.
Qed.

Lemma spectral_unit n (A : 'M[C]_n) : spectralmx A \in unitmx.
Proof. exact/unitarymx_unit/spectral_unitarymx. Qed.

Theorem orthomx_spectralP {n} {A : 'M[C]_n}
  (P := spectralmx A) (sp := spectral_diag A) :
  reflect (A = invmx P *m diag_mx sp *m P) (A \is normalmx).
Proof.
rewrite /P /sp /spectralmx /spectral_diag.
case: orthomx_spectral_subproof.
  by move=> Psp; case: sig2_eqW => //=; constructor.
move=> /orthomx_spectral_subproof Ann; constructor; apply/eqP.
apply: contra Ann; rewrite invmx1 mul1mx mulmx1 => /eqP->.
suff -> : diag_mx 0 = 0 by rewrite qualifE trmx0 (map_mx0 conjC).
by move=> ? ?; apply/matrixP=> i j; rewrite !mxE mul0rn.
Qed.

Lemma hermitian_spectral_diag_real n (A : 'M[C]_n) : A \is hermsymmx ->
  spectral_diag A \is a realmx.
Proof.
move=> Ahermi; have /hermitian_normalmx /orthomx_spectralP A_eq := Ahermi.
have /(congr1 ( fun X => X^t* )) := A_eq.
rewrite invmx_unitary ?spectral_unitarymx //.
rewrite !trmx_mul !map_mxM map_trmx trmxK -map_mx_comp.
rewrite tr_diag_mx map_diag_mx (map_mx_id (@conjCK _)).
rewrite -[in RHS]invmx_unitary ?spectral_unitarymx //.
have := is_hermitianmxP _ _ _ Ahermi; rewrite expr0 scale1r => <-.
rewrite {1}A_eq mulmxA => /(congr1 (mulmx^~ (invmx (spectralmx A)))).
rewrite !mulmxK ?spectral_unit//.
move=> /(congr1 (mulmx (spectralmx A))); rewrite !mulKVmx ?spectral_unit//.
move=> eq_A_conjA; apply/mxOverP => i j; rewrite ord1 {i}.
have /matrixP /(_ j j) := eq_A_conjA; rewrite !mxE eqxx !mulr1n.
by move=> /esym/CrealP.
Qed.

End Spectral.

Local Notation "p ^^ f" := (map_poly f p)
  (at level 30, f at level 30, format "p  ^^  f").

Section RealSubfield.

Variable (C : numClosedFieldType).

Record realsubfield :=
  Realsub { realsubval : C; realsubvalP : realsubval \is Num.real }.

HB.instance Definition _ := [isSub for realsubval].
HB.instance Definition _ := [Choice of realsubfield by <:].
HB.instance Definition _ :=
  [SubChoice_isSubIntegralDomain of realsubfield by <:].
HB.instance Definition _ :=
  [SubIntegralDomain_isSubField of realsubfield by <:].
HB.instance Definition _ : Order.isPOrder ring_display realsubfield :=
  Order.CancelPartial.Pcan _ valK.
Fact total_realsubfield :
  total (<=%O : rel (realsubfield : porderType _)).
Proof. by move=> x y; apply/real_leVge/valP/valP. Qed.
HB.instance Definition _ :=
  Order.POrder_isTotal.Build _ realsubfield total_realsubfield.

Fact realsubval_is_zmod_morphism : zmod_morphism realsubval.
Proof. by []. Qed.
Fact realsubval_is_monoid_morphism : monoid_morphism realsubval.
Proof. by []. Qed.
HB.instance Definition _ :=
  GRing.isZmodMorphism.Build realsubfield C realsubval
  realsubval_is_zmod_morphism.
HB.instance Definition _ :=
  GRing.isMonoidMorphism.Build realsubfield C realsubval
  realsubval_is_monoid_morphism.

Definition realsubfield_norm (x : realsubfield) : realsubfield :=
  Realsub (normr_real (val x)).
Fact realsubfield_ler_norm_add x y :
  realsubfield_norm (x + y) <= (realsubfield_norm x + realsubfield_norm y).
Proof. exact: ler_normD. Qed.
Fact realsubfield_normr0_eq0 x : realsubfield_norm x = 0 -> x = 0.
Proof. by move=> /(congr1 val)/normr0_eq0 ?; apply/val_inj. Qed.
Fact realsubfield_normrMn x n :
  realsubfield_norm (x *+ n) = realsubfield_norm x *+ n.
Proof. by apply/val_inj; rewrite /= !rmorphMn/= normrMn. Qed.
Fact realsubfield_normrN x : realsubfield_norm (- x) = realsubfield_norm x.
Proof. by apply/val_inj; apply: normrN. Qed.

Section Num.

Section withz.
Let z : realsubfield := 0.
Fact realsubfield_addr_gt0 (x y : realsubfield) : z < x -> z < y -> z < x + y.
Proof. exact: addr_gt0. Qed.
Fact realsubfield_ger_leVge (x y : realsubfield) :
  z <= x -> z <= y -> (x <= y) || (y <= x).
Proof. exact: ger_leVge. Qed.
Fact realsubfield_normrM : {morph realsubfield_norm : x y / x * y}.
Proof. by move=> *; apply/val_inj; apply: normrM. Qed.
Fact realsubfield_ler_def (x y : realsubfield) :
  (x <= y) = (realsubfield_norm (y - x) == y - x).
Proof. by apply: ler_def. Qed.
End withz.

HB.instance Definition _ := Num.Zmodule_isNormed.Build _ realsubfield
  realsubfield_ler_norm_add realsubfield_normr0_eq0
  realsubfield_normrMn realsubfield_normrN.
HB.instance Definition _ := Num.isNumRing.Build realsubfield
  realsubfield_addr_gt0 realsubfield_ger_leVge
  realsubfield_normrM realsubfield_ler_def.
End Num.

Definition realsubpfactor (x : C) : {poly realsubfield} :=
  if x \is Num.real =P true is ReflectT xR then 'X - (Realsub xR)%:P else
  'X^2 - (Realsub (Creal_Re x) *+ 2) *: 'X + ((Realsub (normr_real x))^+2)%:P.
Notation Cpfactor x := (realsubpfactor x ^^ realsubval).

Lemma realsubpfactorRE (x : C) (xR : x \is Num.real) :
  realsubpfactor x = 'X - (Realsub xR)%:P.
Proof.
rewrite /realsubpfactor; case: eqP xR => //= p1 p2.
by rewrite (bool_irrelevance p1 p2).
Qed.

Lemma CpfactorRE (x : C) : x \is Num.real ->
  Cpfactor x = 'X - x%:P.
Proof. by move=> xR; rewrite realsubpfactorRE map_polyXsubC. Qed.

Lemma realsubpfactorCE (x : C) : x \isn't Num.real ->
  realsubpfactor x =
  'X^2 - (Realsub (Creal_Re x) *+ 2) *: 'X + ((Realsub (normr_real x))^+2)%:P.
Proof. by rewrite /realsubpfactor; case: eqP => // p; rewrite p. Qed.

Lemma CpfactorCE (x : C) : x \isn't Num.real ->
  Cpfactor x = ('X - x%:P) * ('X - x^*%:P).
Proof.
move=> xNR; rewrite realsubpfactorCE//=.
rewrite rmorphD /= rmorphB/= !map_polyZ !map_polyXn/= map_polyX.
rewrite (map_polyC realsubval)/=.
rewrite mulrBl !mulrBr -!addrA; congr (_ + _).
rewrite opprD addrA opprK -opprD -rmorphM/= -normCK; congr (- _ + _).
rewrite mulrC !mul_polyC -scalerDl.
rewrite [x in RHS]Crect conjC_rect ?Creal_Re ?Creal_Im//.
by rewrite addrACA addNr addr0.
Qed.

Lemma CpfactorE x :
  Cpfactor x = ('X - x%:P) * ('X - x^*%:P) ^+ (x \isn't Num.real).
Proof.
by have [/CpfactorRE|/CpfactorCE] := boolP (_ \is _); rewrite ?mulr1.
Qed.

Lemma size_Cpfactor x : size (Cpfactor x) = (x \isn't Num.real).+2.
Proof.
have [xR|xNR] := boolP (_ \is _); first by rewrite CpfactorRE// size_XsubC.
by rewrite CpfactorCE// size_mul ?size_XsubC ?polyXsubC_eq0.
Qed.

Lemma size_realsubpfactor x : size (realsubpfactor x) = (x \isn't Num.real).+2.
Proof. by have := size_Cpfactor x; rewrite size_map_poly. Qed.

Lemma Cpfactor_eq0 x : (Cpfactor x == 0) = false.
Proof. by rewrite -size_poly_eq0 size_Cpfactor. Qed.

Lemma realsubpfactor_eq0 x : (realsubpfactor x == 0) = false.
Proof. by rewrite -size_poly_eq0 size_realsubpfactor. Qed.

Lemma CpfactorCgt0 x y : x \isn't Num.real -> y \is Num.real ->
  (Cpfactor x).[y] > 0.
Proof.
move=> xNR yR; rewrite CpfactorCE// hornerM !hornerXsubC.
rewrite [x]Crect conjC_rect ?Creal_Re ?Creal_Im// !opprD !addrA opprK.
rewrite -subr_sqr exprMn sqrCi mulN1r opprK ltr_wpDl//.
- by rewrite real_exprn_even_ge0// ?rpredB// ?Creal_Re.
by rewrite real_exprn_even_gt0 ?Creal_Im ?orTb//=; apply/eqP/Creal_ImP.
Qed.

Lemma realsubpfactorR_mul_gt0 (x a b : C) :
    x \is Num.real -> a \is Num.real -> b \is Num.real ->
    a <= b ->
    ((Cpfactor x).[a] * (Cpfactor x).[b] <= 0) =
  (a <= x <= b).
Proof.
move=> xR aR bR ab; rewrite !CpfactorRE// !hornerXsubC.
have [lt_xa|lt_ax|->]/= := real_ltgtP xR aR; last first.
- by rewrite subrr mul0r lexx ab.
- by rewrite nmulr_rle0 ?subr_lt0 ?subr_ge0.
rewrite pmulr_rle0 ?subr_gt0// subr_le0.
by apply: negbTE; rewrite -real_ltNge// (lt_le_trans lt_xa).
Qed.

Lemma monic_Cpfactor x : Cpfactor x \is monic.
Proof. by rewrite CpfactorE rpredM ?rpredX ?monicXsubC. Qed.

Lemma monic_realsubpfactor x : realsubpfactor x \is monic.
Proof. by have := monic_Cpfactor x; rewrite map_monic. Qed.

Lemma poly_realsub_pfactor (p : {poly realsubfield}) :
  { r : seq C |
    p ^^ realsubval = val (lead_coef p) *: \prod_(z <- r) Cpfactor z }.
Proof.
wlog p_monic : p / p \is monic => [hwlog|].
  have [->|pN0] := eqVneq p 0.
    by exists [::]; rewrite lead_coef0/= rmorph0 scale0r.
  have [|r] := hwlog ((lead_coef p)^-1 *: p).
    by rewrite monicE lead_coefZ mulVf ?lead_coef_eq0//.
  rewrite !lead_coefZ mulVf ?lead_coef_eq0//= scale1r.
  rewrite map_polyZ/=.
  have lcN0 : realsubval (lead_coef p) != 0.
    by rewrite fmorph_eq0 lead_coef_eq0.
  by move=> /(canRL (scalerKV lcN0))->; exists r.
suff: {r : seq C | p ^^ realsubval = \prod_(z <- r) Cpfactor z}.
  by move=> [r rP]; exists r; rewrite rP (monicP _)// scale1r.
have [/= r pr] := closed_field_poly_normal (p ^^ realsubval).
rewrite (monicP _) ?monic_map ?scale1r// {p_monic} in pr *.
have [n] := ubnP (size r).
elim: n r => // n IHn [|x r]/= in p pr *.
 by exists [::]; rewrite pr !big_nil.
rewrite ltnS => r_lt.
have xJxr : x^* \in x :: r.
  rewrite -root_prod_XsubC -pr.
  have /eq_map_poly-> : realsubval =1 Num.conj \o realsubval.
    by move=> a /=; rewrite (CrealP (realsubvalP _)).
  by rewrite map_poly_comp mapf_root pr root_prod_XsubC mem_head.
have xJr : (x \isn't Num.real) ==> (x^* \in r) by rewrite implyNb CrealE.
have pxdvdC : Cpfactor x %| p ^^ realsubval.
  rewrite pr CpfactorE big_cons/= dvdp_mul2l ?polyXsubC_eq0//.
  by case: (_ \is _) xJr; rewrite ?dvd1p// dvdp_XsubCl root_prod_XsubC.
pose pr'x := p %/ realsubpfactor x.
have [||r'] := IHn (if x \is Num.real then r else rem x^* r) pr'x;
  last 2 first.
- by case: (_ \is _) in xJr *;
    rewrite ?size_rem// (leq_ltn_trans (leq_pred _)).
- move=> /eqP; rewrite map_divp -dvdp_eq_mul ?Cpfactor_eq0//= => /eqP->.
  by exists (x :: r'); rewrite big_cons mulrC.
rewrite map_divp/= pr big_cons CpfactorE/=.
rewrite divp_pmul2l ?expf_neq0 ?polyXsubC_eq0//.
case: (_ \is _) => /= in xJr *; first by rewrite divp1//.
by rewrite (big_rem _ xJr)/= mulKp ?polyXsubC_eq0.
Qed.

Definition realsubfield_rcfMixin : Num.real_closed_axiom realsubfield.
Proof.
move=> p a b le_ab /andP[pa_le0 pb_ge0]/=.
case: ltgtP pa_le0 => //= pa0 _; last first.
  by exists a; rewrite ?lexx// rootE pa0.
case: ltgtP pb_ge0 => //= pb0 _; last first.
  by exists b; rewrite ?lexx ?andbT// rootE -pb0.
have p_neq0 : p != 0 by apply: contraTneq pa0 => ->; rewrite horner0 ltxx.
have {pa0 pb0} pab0 : p.[a] * p.[b] < 0 by rewrite pmulr_llt0.
wlog p_monic : p p_neq0 pab0 / p \is monic => [hwlog|].
  have [|||x axb] := hwlog ((lead_coef p)^-1 *: p).
  - by rewrite scaler_eq0 invr_eq0 lead_coef_eq0 (negPf p_neq0).
  - rewrite !hornerE/= -mulrA mulrACA -expr2 pmulr_rlt0//.
    by rewrite exprn_even_gt0//= invr_eq0 lead_coef_eq0.
  - by rewrite monicE lead_coefZ mulVf ?lead_coef_eq0 ?eqxx.
  by rewrite rootZ ?invr_eq0 ?lead_coef_eq0//; exists x.
have /= [rs prs] := poly_realsub_pfactor p.
rewrite (monicP _) ?monic_map// scale1r {p_monic} in prs.
pose ab := [pred x | val a <= x <= val b].
have abR : {subset ab <= Num.real}.
  move=> x /andP[+ _].
  by rewrite -subr_ge0 => /ger0_real; rewrite rpredBr// realsubvalP.
wlog : p pab0 {p_neq0 prs} /
    p ^^ realsubval = \prod_(x <- rs | x \in ab) ('X - x%:P) => [hw|].
  move: prs; rewrite -!rmorph_prod => /map_poly_inj.
  rewrite (bigID ab)/=; set q := (X in X * _); set u := (X in _ * X) => pqu.
  have [||] := hw q; last first.
  - by move=> x; exists x => //; rewrite pqu rootM q0.
  - by rewrite rmorph_prod/=; under eq_bigr do rewrite CpfactorRE ?abR//.
  have := pab0; rewrite pqu !hornerM mulrACA [_ * _ * _ < 0]pmulr_llt0//.
  rewrite !horner_prod -big_split/= prodr_gt0// => x.
  have [xR|xNR] := boolP (x \is Num.real); last first.
    rewrite (_ : (0 < ?[a]) = (realsubval 0 < realsubval ?a))//=.
    by rewrite -!horner_map/= mulr_gt0 ?CpfactorCgt0 ?realsubvalP.
  apply: contraNT; rewrite -leNgt.
  rewrite (_ : (?[a] <= 0) = (realsubval ?a <= realsubval 0))//= -!horner_map/=.
  by rewrite realsubpfactorR_mul_gt0 ?realsubvalP.
rewrite -big_filter; have := filter_all ab rs.
set rsab := filter _ _.
have: all (mem Num.real) rsab.
  by apply/allP => x; rewrite mem_filter => /andP[/abR].
case: rsab => [_ _|x rsab]/=; rewrite (big_nil, big_cons).
  move=> pval1; move: pab0.
  have /map_poly_inj-> : p ^^ realsubval = 1 ^^ realsubval by rewrite rmorph1.
  by rewrite !hornerE ltr10.
move=> /andP[xR rsabR] /andP[axb arsb] prsab.
exists (Realsub xR) => //=.
by rewrite -(mapf_root realsubval)//= prsab rootM root_XsubC eqxx.
Qed.
HB.instance Definition _ :=
  Num.RealField_isClosed.Build realsubfield realsubfield_rcfMixin.

End RealSubfield.

Unset Default Proof Using.

Section RealSpectral.

(* Over a real closed field the conjugation is the identity. *)

Local Lemma rcf_conjC_id (R : rcfType) (x : R) : conjC x = x.
Proof.
have key : forall y : R, conjC y = - y -> y = 0.
  move=> y cy.
  have : 0 <= y * conjC y by rewrite mul_conjC_ge0.
  rewrite cy mulrN -expr2 oppr_ge0 => yle0.
  by apply/eqP; rewrite -sqrf_eq0 eq_le yle0 sqr_ge0.
apply/eqP; rewrite -subr_eq0; apply/eqP; apply: key.
by rewrite rmorphB/= conjCK opprB.
Qed.

Local Lemma map_conjC_id (R : rcfType) m k (M : 'M[R]_(m, k)) : M ^ conjC = M.
Proof. by apply/matrixP=> a b; rewrite mxE rcf_conjC_id. Qed.

Local Lemma trmxC_trmx_id (R : rcfType) m k (M : 'M[R]_(m, k)) : M ^t* = M^T.
Proof. by rewrite -map_trmx map_conjC_id. Qed.

Lemma schmidt_diag_real (R : rcfType) n (A Q : 'M[R]_n) (d : 'rV[R]_n) :
  A \is symmetricmx -> Q \in unitmx -> Q *m A *m invmx Q = diag_mx d ->
  let P := schmidt Q in
  (P \is unitarymx) /\ (P *m A *m invmx P = diag_mx d).
Proof.
move=> Asym Qu eqd P.
have Pu : P \is unitarymx by apply: schmidt_unitarymx.
have PinvT : invmx P = P^T by rewrite invmx_unitary// trmxC_trmx_id.
have PPT : P *m P^T = 1%:M by move/unitarymxP: Pu; rewrite trmxC_trmx_id.
have PTP : P^T *m P = 1%:M by rewrite -PinvT mulVmx ?unitarymx_unit.
have AsymT : A^T = A.
  move/is_hermitianmxP: Asym; rewrite expr0 scale1r => Asym'.
  by rewrite {2}Asym' -map_trmx map_mx_id.
have eigQ : Q *m A = diag_mx d *m Q.
  by have := congr1 (mulmx^~ Q) eqd; rewrite -mulmxA mulVmx// mulmx1.
pose S := Q *m P^T.
have Slt : is_trig_mx S.
  by rewrite /S /P -trmxC_trmx_id; apply: schmidt_trig.
have Sunit : S \in unitmx.
  by rewrite unitmx_mul Qu/= unitarymx_unit// trmx_unitary.
have Sii i : S i i != 0.
  move: Sunit; rewrite unitmxE (det_trig Slt) unitfE.
  by move=> /prodf_neq0/(_ i isT).
pose B := P *m A *m P^T.
have Bsym : B^T = B by rewrite /B !trmx_mul trmxK AsymT mulmxA.
have SBrel : S *m B = diag_mx d *m S.
  by rewrite /S /B !mulmxA -[Q *m P^T *m P]mulmxA PTP mulmx1 eigQ -!mulmxA.
have dSe i j : (diag_mx d *m S) i j = d 0 i * S i j.
  rewrite mxE (bigD1 i)//= mxE eqxx mulr1n big1 ?addr0// => k ik.
  by rewrite mxE eq_sym (negPf ik) mulr0n mul0r.
have SBe i j : \sum_(k < n) S i k * B k j = d 0 i * S i j.
  by rewrite -dSe -SBrel mxE.
have Blt : is_trig_mx B.
  apply/is_trig_mxP => i j.
  have [k] := ubnP i; elim: k i j => // k IHk i j; rewrite ltnS => leik ij.
  have key : S i i * B i j = 0.
    transitivity (\sum_(l < n) S i l * B l j); last first.
      by rewrite SBe (is_trig_mxP Slt _ _ ij) mulr0.
    rewrite (bigD1 i)//= big1 ?addr0// => l li.
    case: (ltngtP l i) => [li'|li'|/val_inj le].
    - by rewrite (IHk _ _ (leq_trans li' leik) (ltn_trans li' ij)) mulr0.
    - by rewrite (is_trig_mxP Slt _ _ li') mul0r.
    - by rewrite le eqxx in li.
  by move/eqP: key; rewrite mulf_eq0 (negPf (Sii i)) => /eqP.
have Bii i : B i i = d 0 i.
  have hsum : \sum_(k < n) S i k * B k i = S i i * B i i.
    rewrite (bigD1 i)//= big1 ?addr0// => k ki.
    case: (ltngtP k i) => [ki'|ki'|/val_inj ke].
    - by rewrite (is_trig_mxP Blt _ _ ki') mulr0.
    - by rewrite (is_trig_mxP Slt _ _ ki') mul0r.
    - by rewrite ke eqxx in ki.
  by apply: (mulfI (Sii i)); rewrite -hsum SBe mulrC.
have Bdiag : B = diag_mx d.
  apply/matrixP=> i j; rewrite [RHS]mxE.
  case: (ltngtP i j) => [ij|ij|/val_inj->].
  - by rewrite (is_trig_mxP Blt _ _ ij) -val_eqE/= ltn_eqF// mulr0n.
  - rewrite -Bsym mxE (is_trig_mxP Blt _ _ ij) -val_eqE/=.
    by rewrite gtn_eqF// mulr0n.
  - by rewrite eqxx mulr1n Bii.
by split=> //; rewrite PinvT -/B Bdiag.
Qed.

(* Pulling a real matrix back to the real subfield. *)

Local Definition mxR (C : numClosedFieldType) p q (M : 'M[C]_(p, q)) :
    'M[realsubfield C]_(p, q) := map_mx (insubd (0 : realsubfield C)) M.

Local Lemma mxRK (C : numClosedFieldType) p q (M : 'M[C]_(p, q)) :
  M \is a realmx -> map_mx (@realsubval C) (mxR M) = M.
Proof.
move=> Mreal; apply/matrixP=> i j; rewrite !mxE.
by rewrite val_insubd (elimT mxOverP Mreal i j).
Qed.

Theorem real_spectral_theorem (C : numClosedFieldType) n (A : 'M[C]_n) :
  A \is a realmx -> A \is symmetricmx ->
  let sp := spectral_diag A in
  exists2 P : 'M[C]_n,
    P \is a realmx /\ P \in unitarymx &
    A = invmx P *m diag_mx sp *m P.
Proof.
move=> Areal Asym sp.
have Aherm := realsym_hermsym Asym Areal.
have spreal : sp \is a realmx := hermitian_spectral_diag_real Aherm.
have dreal : diag_mx sp \is a realmx by rewrite mxOver_diag.
have sim0 : similar_in unitmx A (diag_mx sp).
  exists (spectralmx A); first exact: spectral_unit.
  apply/similarP; first exact: spectral_unit.
  rewrite [X in _ *m X](orthomx_spectralP (symmetric_normalmx Asym Areal)).
  by rewrite mulmxA mulmxA mulmxV ?spectral_unit// mul1mx.
have [Q] := real_similar sim0 Areal dreal.
rewrite inE/= => /andP[Qreal Qunit] /similarP -/(_ Qunit) simQ.
have eqdC : Q *m A *m invmx Q = diag_mx sp.
  by rewrite simQ -mulmxA mulmxV ?mulmx1.
pose f := @realsubval C.
pose AR := mxR A; pose Qint := mxR Q; pose dR := mxR sp.
have fAR : map_mx f AR = A := mxRK Areal.
have fQ : map_mx f Qint = Q := mxRK Qreal.
have fd : map_mx f dR = sp := mxRK spreal.
have AsymT : A^T = A.
  move/is_hermitianmxP: Asym; rewrite expr0 scale1r => Asym'.
  by rewrite {2}Asym' -map_trmx map_mx_id.
have ARsymT : AR^T = AR.
  apply: (@map_mx_inj _ _ f); apply/matrixP=> i j.
  by rewrite -map_trmx fAR -[in RHS]AsymT !mxE.
have ARsym : AR \is symmetricmx.
  apply/is_hermitianmxP; rewrite expr0 scale1r.
  by rewrite -[AR ^t idfun]map_trmx map_mx_id ?ARsymT.
have Qintunit : Qint \in unitmx by rewrite -(map_unitmx f) fQ.
have eqdR : Qint *m AR *m invmx Qint = diag_mx dR.
  apply: (@map_mx_inj _ _ f).
  by rewrite !map_mxM map_invmx fQ fAR map_diag_mx fd; exact: eqdC.
have [PRu PReq] := schmidt_diag_real ARsym Qintunit eqdR.
set PR := schmidt Qint in PRu PReq.
pose P := map_mx f PR.
have Preal : P \is a realmx.
  by apply/mxOverP=> i j; rewrite mxE; apply: realsubvalP.
have eqdP : P *m A *m invmx P = diag_mx sp.
  have := congr1 (map_mx f) PReq.
  by rewrite !map_mxM map_invmx fAR map_diag_mx fd.
have Punit : P \in unitmx by rewrite /P map_unitmx unitarymx_unit.
exists P; last by rewrite -eqdP !mulmxA mulVmx// mul1mx -mulmxA mulVmx// mulmx1.
split=> //; apply/unitarymxP.
have PTC : P ^t* = P^T by rewrite -map_trmx realmxC.
have PRPT : PR *m PR^T = 1%:M by move/unitarymxP: PRu; rewrite trmxC_trmx_id.
rewrite PTC.
by have := congr1 (map_mx f) PRPT; rewrite map_mxM map_mx1 -map_trmx => <-.
Qed.

End RealSpectral.

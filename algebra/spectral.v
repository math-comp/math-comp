From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype choice ssrnat.
From mathcomp Require Import seq div fintype bigop ssralg finset fingroup zmodp.
From mathcomp Require Import poly polydiv order ssrnum matrix mxalgebra vector.
From mathcomp Require Import mxpoly mxred sesquilinear.

(******************************************************************************)
(*                             Spectral theory                                *)
(*                                                                            *)
(* This file provides a formalization of Gram-Schmidt orthonormalization,     *)
(* Schur decomposition, etc.                                                   *)
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
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Order.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope sesquilinear_scope.

(* TODO: move? *)
Lemma eigenvalue_closed {C : numClosedFieldType} n (A : 'M[C]_n) : (n > 0)%N ->
  exists a, eigenvalue A a.
Proof.
move=> n_gt0; have /closed_rootP [a rAa] : size (char_poly A) != 1%N.
  by rewrite size_char_poly; case: (n) n_gt0.
by exists a; rewrite eigenvalue_root_char.
Qed.

(* TODO: move? *)
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
apply/allP => B B_in; rewrite -stablemx_restrict ?vP //.
  by apply/mapP; exists B.
by rewrite comm_mx_stable_eigenspace //; exact: A_comm.
Qed.

(* TODO: move? *)
Lemma common_eigenvector2 {C : numClosedFieldType}n  (A B : 'M[C]_n) :
  (n > 0)%N -> A *m B = B *m A ->
  exists2 v : 'rV_n, v != 0 & (stablemx v A) && (stablemx v B).
Proof.
move=> n_gt0 AB_comm; have [] := @common_eigenvector _ _ [:: A; B] n_gt0.
  by move=> A' B'; rewrite !inE => /orP [] /eqP-> /orP [] /eqP->.
by move=> v v_neq0 /allP vP; exists v; rewrite ?vP ?(mem_head, in_cons, orbT).
Qed.

Notation "M ^t*" := (M ^t conjC) (at level 30) : sesquilinear_scope.
Notation realmx := (mxOver Num.real).

Lemma trmxCK {C : numClosedFieldType} m n (A : 'M[C]_(m, n)) : A ^t* ^t* = A.
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
have Qunit x : Q x \in unitmx = (p.[x] != 0).
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
Context {C : numClosedFieldType}.

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
Definition dotmx (C : numClosedFieldType) n (u v : 'rV[C]_n) :=
  dotmx_def u%R v%R.

Section Spectral.
Variable (C : numClosedFieldType).
Set Default Proof Using "C".

(*
TODO: bug report
without the lock we were expecting
HB.instance Definition _ n := Bilinear.on (@dotmx n).
to be sufficient to equip dotmx with the bilinear structure
but needed to use .copy in the end as in:

TODO: feature request
implement copy modulo lock
*)
(* Lemma dotmx_bilinear n : isBilinear _ _ _ _ *%R (conjC \; *%R) (@dotmx C n). *)
(* Proof. *)
(* rewrite unlock; constructor => /= ?. *)
(* - exact: linearBl. *)
(* - exact: linearBr. *)
(* - exact: linearZl_LR. *)
(* - exact: linearZr_LR. *)
(* Qed. *)
(* HB.instance Definition _ n := dotmx_bilinear n. *)

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
suff -> : u *m v ^t* = ((v *m u ^t*) ^t*) by rewrite !mxE.
by rewrite !trmx_mul map_mxM/= trmxCK.
Qed.
HB.instance Definition _ n := @dotmx_is_hermitian n.

Fact dotmx_is_dot n : isDotProduct _ _ (@dotmx C n).
Proof.
split => /= u u_neq0; rewrite dotmxE mxE.
suff /existsP[i ui_neq0] : [exists i, u ``_ i != 0].
  rewrite (bigD1 i) //= ltr_wpDr// ?sumr_ge0// ?mxE ?mul_conjC_gt0//.
  by move=> j _; rewrite !mxE mul_conjC_ge0.
apply: contraNT u_neq0; rewrite negb_exists => /forallP uNN0.
by apply/eqP/rowP=> j; rewrite mxE; apply/eqP; rewrite -[_ == _]negbK uNN0.
Qed.
HB.instance Definition _ n := (@dotmx_is_dot n).

Local Notation "B ^!" :=
  (orthomx (@conjC C) (mx_of_hermitian (hermitian1mx _)) B) : matrix_set_scope.
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
rewrite proj_ortho_0 ?proj_mx_sub // addr0.
rewrite proj_ortho_0 ?ortho_id ?proj_ortho_sub // add0r.
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
      rewrite (submx_trans (proj_ortho_sub _ _)) //.
      by rewrite -{1}[B]addr0 addmx_sub_adds ?sub0mx.
    by rewrite (submx_trans _ vBn) // proj_ortho_sub.
  pose c := (sqrtC '[BoSn])^-1; have c_gt0 : c > 0.
    by rewrite invr_gt0 sqrtC_gt0 lt_def ?dnorm_eq0 ?dnorm_ge0 BoSn_neq0.
  exists BoSn; apply/and4P; split => //.
  - by rewrite orthomx_sym ?proj_ortho_sub // /gtr_eqF.
  - rewrite -pBE linearDl/=.
    rewrite [X in X + '[_]](hermmx_eq0P _ _) ?add0r ?dnorm_ge0 //.
    by rewrite orthomx_proj_mx_ortho // orthomx_sym.
  - by rewrite -pBE addmx_sub_adds // proj_ortho_sub.
wlog nv_eq1 : v vBn v_neq0 dAv_ge0 dAsub / '[v] = 1.
  pose c := (sqrtC '[v])^-1.
  have c_gt0 : c > 0 by rewrite invr_gt0 sqrtC_gt0 ?dnorm_gt0.
  have [c_ge0 c_eq0F] := (ltW c_gt0, gt_eqF c_gt0).
  move=> /(_ (c *: v)); apply.
  - by rewrite orthomxZ ?c_eq0F.
  - by rewrite scaler_eq0 c_eq0F.
  - by rewrite linearZr mulr_ge0 // conjC_ge0.
  - by rewrite (submx_trans dAsub) // addsmxS // eqmx_scale // c_eq0F.
  - rewrite dnormZ normfV ger0_norm ?sqrtC_ge0 ?dnorm_ge0 //.
    by rewrite exprVn rootCK ?mulVf // dnorm_eq0.
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
  rewrite [in RHS](reindex (lshift 1)) /=.
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
  rewrite (eigenspaceP (_ : (_ <= _ a))%MS); last first.
    by rewrite eqmx_schmidt_free ?row_base_free ?eq_row_base.
  rewrite -scalemxAl (orthomx1P _) ?scaler0 //.
  by do 2!rewrite eqmx_schmidt_free ?row_base_free ?eq_row_base // orthomx_sym.
have drrE X : drsubmx (r X) =
  schmidt (row_base v^!%MS) *m X *m schmidt (row_base v^!%MS) ^t*.
  by rewrite /r mul_col_mx tr_col_mx map_row_mx mul_col_row block_mxKdr.
have vSv X a : (v <= eigenspace X a)%MS ->
  schmidt (row_base v) *m X *m schmidt (row_base v) ^t* = a%:M.
  move=> vXa; rewrite (eigenspaceP (_ : (_ <= _ a)%MS)); last first.
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
  rewrite !trmx0 !(@map_mx0 _ _ conjC) !tr_scalar_mx !map_scalar_mx ?conjC1.
  rewrite !(mulmx1, mul1mx, mulmx0, mul0mx, addr0, add0r).
  by rewrite (unitarymxP _) -?scalar_mx_block //.
apply/allP => /= A A_in.
rewrite trmx_mul map_mxM tr_block_mx map_block_mx.
rewrite !trmx0 !map_mx0 !tr_scalar_mx !map_scalar_mx ?conjC1.
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

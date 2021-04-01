(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div.
From mathcomp Require Import choice fintype finfun bigop fingroup perm order.
From mathcomp Require Import ssralg zmodp matrix mxalgebra poly polydiv mxpoly.

(*****************************************************************************)
(* In this file, we prove diagonalization theorems, for this purpose, we     *)
(* define conjugation, similarity and diagonalizability.                     *)
(*                                                                           *)
(*      conjmx V f  := V *m f *m pinvmx V                                    *)
(*                  == the conjugation of f by V, i.e. "the" matrix of f     *)
(*                     in the basis of row vectors of V.                     *)
(*                     Although this makes sense only when f stabilizes V,   *)
(*                     the definition can be stated more generally.          *)
(* similar_to P A C == where P is a base change matrix, A is a matrix,       *)
(*                     and C is a class of matrices,                         *)
(*                     this states that conjmx P A is in C,                  *)
(*                     which means A is similar to a matrix in C.            *)
(*                                                                           *)
(* From the latter, we derive serveral related notions:                      *)
(*         similar P A B := similar_to P A (pred1 B)                         *)
(*                       == A is similar to B, with base change matrix P     *)
(*      similar_in D A B == A is similar to B,                               *)
(*                          with a base change matrix in D                   *)
(*   similar_in_to D A C == A is similar to a matrix in the class C,         *)
(*                          with a base change matrix in D                   *)
(* all_similar_to D As C == all the matrices in the sequence As are similar  *)
(*                          to some matrix in the class C,                   *)
(*                          with a base change matrix in D.                  *)
(*                                                                           *)
(* We also specialize the class C, to diagonalizability:                     *)
(*          similar_diag P A := (similar_to P A is_diag_mx).                 *)
(*     diagonalizable_in D A := (similar_in_to D A is_diag_mx).              *)
(*          diagonalizable A := (diagonalizable_in unitmx A).                *)
(*  codiagonalizable_in D As := (all_similar_to D As is_diag_mx).            *)
(*       codiagonalizable As := (codiagonalizable_in unitmx As).             *)
(*                                                                           *)
(* The main results of this file are:                                        *)
(*   diagonalizablePeigen:                                                   *)
(*     a matrix is diagonalizable iff there is a sequence                    *)
(*     of scalars r, such that the sum of the associated                     *)
(*     eigenspaces is full.                                                  *)
(*   diagonalizableP:                                                        *)
(*     a matrix is diagonalizable iff its minimal polynomial                 *)
(*     divides a split polynomial with simple roots.                         *)
(*   codiagonalizableP:                                                      *)
(*     a sequence of matrices are diagonalizable in the same basis           *)
(*     iff they are all diagonalizable and commute pairwize.                 *)
(*                                                                           *)
(* We also specialize the class C, to trigonalizablility:                    *)
(*          similar_trig P A := (similar_to P A is_trig_mx).                 *)
(*     trigonalizable_in D A := (similar_in_to D A is_trig_mx).              *)
(*          trigonalizable A := (trigonalizable_in unitmx A).                *)
(*  cotrigonalizable_in D As := (all_similar_to D As is_trig_mx).            *)
(*       cotrigonalizable As := (cotrigonalizable_in unitmx As).             *)
(* The theory of trigonalization is however not developed in this file.      *)
(*****************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Import Monoid.Theory.

Local Open Scope ring_scope.

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

Lemma horner_mx_conj m n p (B : 'M[F]_(n.+1, m.+1)) (f : 'M_m.+1) :
   row_free B -> stablemx B f ->
   horner_mx (conjmx B f) p = conjmx B (horner_mx f p).
Proof.
move=> B_free B_stab; rewrite/conjmx; elim/poly_ind: p => [|p c].
  by rewrite !rmorph0 mulmx0 mul0mx.
rewrite !(rmorphD, rmorphM)/= !(horner_mx_X, horner_mx_C) => ->.
rewrite [_ * _]mulmxA [_ *m (B *m _)]mulmxA mulmxKpV ?horner_mx_stable//.
apply: (row_free_inj B_free); rewrite [_ *m B]mulmxDl.
pose stablemxE := (stablemxD, stablemxM, stablemxC, horner_mx_stable).
by rewrite !mulmxKpV -?[B *m _ *m _]mulmxA ?stablemxE// mulmxDr -scalar_mxC.
Qed.

Lemma horner_mx_uconj n p (B : 'M[F]_(n.+1)) (f : 'M_n.+1) :
   B \is a GRing.unit ->
   horner_mx (B *m f *m invmx B) p = B *m horner_mx f p *m invmx B.
Proof.
move=> B_unit; rewrite -!conjumx//.
by rewrite horner_mx_conj ?row_free_unit ?stablemx_unit.
Qed.

Lemma horner_mx_uconjC n p (B : 'M[F]_(n.+1)) (f : 'M_n.+1) :
   B \is a GRing.unit ->
   horner_mx (invmx B *m f *m B) p = invmx B *m horner_mx f p *m B.
Proof.
move=> B_unit; rewrite -[X in _ *m X](invmxK B).
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

Implicit Types (V : 'M[F]_(m, n)) (f : 'M[F]_n).
Implicit Types (a : F) (p : {poly F}).

Section Sub.
Variable (k : nat).
Implicit Types (W : 'M[F]_(k, m)).

Lemma sub_kermxpoly_conjmx V f p W : stablemx V f -> row_free V ->
  (W <= kermxpoly (conjmx V f) p)%MS = (W *m V <= kermxpoly f p)%MS.
Proof.
case: n m => [|n'] [|m']// in V f W * => fV rfV; rewrite ?thinmx0//.
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

Definition similar_to {F : fieldType} {m n} (P : 'M_(m, n)) A (C : {pred 'M[F]_m}) :=
   C (conjmx P A).

Notation similar P A B := (similar_to P A (PredOfSimpl.coerce (pred1 B))).
Notation similar_in D A B := (exists2 P, P \in D & similar P A B).
Notation similar_in_to D A C := (exists2 P, P \in D & similar_to P A C).
Notation all_similar_to D As C := (exists2 P, P \in D & all [pred A | similar_to P A C] As).

Notation similar_diag P A := (similar_to P A is_diag_mx).
Notation diagonalizable_in D A := (similar_in_to D A is_diag_mx).
Notation diagonalizable A := (diagonalizable_in unitmx A).
Notation codiagonalizable_in D As := (all_similar_to D As is_diag_mx).
Notation codiagonalizable As := (codiagonalizable_in unitmx As).

Notation similar_trig P A := (similar_to P A is_trig_mx).
Notation trigonalizable_in D A := (similar_in_to D A is_trig_mx).
Notation trigonalizable A := (trigonalizable_in unitmx A).
Notation cotrigonalizable_in D As := (all_similar_to D As is_trig_mx).
Notation cotrigonalizable As := (cotrigonalizable_in unitmx As).

Section Similarity.
Context {F : fieldType}.

Lemma similarPp m n {P : 'M[F]_(m, n)} {A B} :
  stablemx P A -> similar P A B -> P *m A = B *m P.
Proof. by move=> stablemxPA /eqP <-; rewrite mulmxKpV. Qed.

Lemma similarW m n {P : 'M[F]_(m, n)} {A B} : row_free P ->
  P *m A = B *m P -> similar P A B.
Proof. by rewrite /similar_to/= /conjmx => fP ->; rewrite mulmxKp. Qed.

Section Similar.

Context {n : nat}.
Implicit Types (f g p : 'M[F]_n) (fs : seq 'M[F]_n) (d : 'rV[F]_n).

Lemma similarP {p f g} : p \in unitmx ->
  reflect (p *m f = g *m p) (similar p f g).
Proof.
move=> p_unit; apply: (iffP idP); first exact/similarPp/stablemx_unit.
by apply: similarW; rewrite row_free_unit.
Qed.

Lemma similarRL {p f g} : p \in unitmx ->
  reflect (g = p *m f *m invmx p) (similar p f g).
Proof. by move=> ?; apply: (iffP eqP); rewrite conjumx. Qed.

Lemma similarLR {p f g} : p \in unitmx ->
  reflect (f = conjmx (invmx p) g) (similar p f g).
Proof.
by move=> pu; rewrite conjVmx//; apply: (iffP (similarRL pu)) => ->;
   rewrite !mulmxA ?(mulmxK, mulmxKV, mulVmx, mulmxV, mul1mx, mulmx1).
Qed.

End Similar.

Lemma similar_mxminpoly {n} {p f g : 'M[F]_n.+1} : p \in unitmx ->
  similar p f g -> mxminpoly f = mxminpoly g.
Proof. by move=> pu /eqP<-; rewrite mxminpoly_uconj. Qed.

Lemma similar_diag_row_base m n (P : 'M[F]_(m, n)) (A : 'M_n) :
  similar_diag (row_base P) A = is_diag_mx (restrictmx P A).
Proof. by []. Qed.

Lemma similar_diagPp m n (P : 'M[F]_(m, n)) A :
  reflect (forall i j : 'I__, i != j :> nat -> conjmx P A i j = 0)
          (similar_diag P A).
Proof. exact: @is_diag_mxP. Qed.

Lemma similar_diagP n (P : 'M[F]_n) A : P \in unitmx ->
  reflect (forall i j : 'I__, i != j :> nat -> (P *m A *m invmx P) i j = 0)
          (similar_diag P A).
Proof. by move=> Pu; rewrite -conjumx//; exact: is_diag_mxP. Qed.

Lemma similar_diagPex {m} {n} {P : 'M[F]_(m, n)} {A} :
  reflect (exists D, similar P A (diag_mx D)) (similar_diag P A).
Proof. by apply: (iffP (diag_mxP _)) => -[D]/eqP; exists D. Qed.

Lemma similar_diagLR n {P : 'M[F]_n} {A} : P \in unitmx ->
  reflect (exists D, A = conjmx (invmx P) (diag_mx D)) (similar_diag P A).
Proof.
by move=> Punit; apply: (iffP similar_diagPex) => -[D /(similarLR Punit)]; exists D.
Qed.

Lemma similar_diag_mxminpoly {n} {p f : 'M[F]_n.+1}
  (rs := undup [seq conjmx p f i i | i <- enum 'I_n.+1]) :
  p \in unitmx -> similar_diag p f ->
  mxminpoly f = \prod_(r <- rs) ('X - r%:P).
Proof.
rewrite /rs => pu /(similar_diagLR pu)[d {f rs}->].
rewrite mxminpoly_uconj ?unitmx_inv// mxminpoly_diag.
by rewrite (@eq_map _ _ _ (d 0))// => i; rewrite conjmxVK// mxE eqxx.
Qed.

End Similarity.

Lemma similar_diag_sum (F : fieldType) (m n : nat) (p_ : 'I_n -> nat)
      (V_ : forall i, 'M[F]_(p_ i, m)) (f : 'M[F]_m) :
    mxdirect (\sum_i <<V_ i>>) ->
    (forall i, stablemx (V_ i) f) ->
    (forall i, row_free (V_ i)) ->
  similar_diag (\mxcol_i V_ i) f = [forall i, similar_diag (V_ i) f].
Proof.
move=> Vd Vf rfV; have aVf : stablemx (\mxcol_i V_ i) f.
  rewrite (eqmx_stable _ (eqmx_col _)) stablemx_sums//.
  by move=> i; rewrite (eqmx_stable _ (genmxE _)).
apply/similar_diagPex/'forall_similar_diagPex => /=
    [[D /(similarPp aVf) +] i|/(_ _)/sigW Dof].
  rewrite mxcol_mul -[D]submxrowK diag_mxrow mul_mxdiag_mxcol.
  move=> /eq_mxcolP/(_ i); set D0 := (submxrow _ _) => VMeq.
  by exists D0; apply/similarW.
exists (\mxrow_i tag (Dof i)); apply/similarW.
   rewrite -row_leq_rank eqmx_col (mxdirectP Vd)/=.
   by under [X in (_ <= X)%N]eq_bigr do rewrite genmxE (eqP (rfV _)).
rewrite mxcol_mul diag_mxrow mul_mxdiag_mxcol; apply: eq_mxcol => i.
by case: Dof => /= k /(similarPp); rewrite Vf => /(_ isT) ->.
Qed.

Section Diag.
Variable (F : fieldType).

Lemma codiagonalizable1 n (A : 'M[F]_n) :
  codiagonalizable [:: A] <-> diagonalizable A.
Proof. by split=> -[P Punit PA]; exists P; move: PA; rewrite //= andbT. Qed.

Definition codiagonalizablePfull n (As : seq 'M[F]_n) :
  codiagonalizable As <-> exists m,
    exists2 P : 'M_(m, n), row_full P & all [pred A | similar_diag P A] As.
Proof.
split => [[P Punit SPA]|[m [P Pfull SPA]]].
  by exists n => //; exists P; rewrite ?row_full_unit.
have Qfull := fullrowsub_unit Pfull.
exists (rowsub (fullrankfun Pfull) P) => //; apply/allP => A AAs/=.
have /allP /(_ _ AAs)/= /similar_diagPex[d /similarPp] := SPA.
rewrite submx_full// => /(_ isT) PA_eq.
apply/similar_diagPex; exists (colsub (fullrankfun Pfull) d).
apply/similarP => //; apply/row_matrixP => i.
rewrite !row_mul row_diag_mx -scalemxAl -rowE !row_rowsub !mxE.
have /(congr1 (row (fullrankfun Pfull i))) := PA_eq.
by rewrite !row_mul row_diag_mx -scalemxAl -rowE => ->.
Qed.

Lemma codiagonalizable_on m n (V_ : 'I_n -> 'M[F]_m) (As : seq 'M[F]_m) :
  (\sum_i V_ i :=: 1%:M)%MS -> mxdirect (\sum_i V_ i) ->
  (forall i, all (fun A => stablemx (V_ i) A) As) ->
  (forall i, codiagonalizable (map (restrictmx (V_ i)) As)) -> codiagonalizable As.
Proof.
move=> V1 Vdirect /(_ _)/allP AV /(_ _) /sig2W/= Pof.
pose P_ i := tag (Pof i).
have P_unit i : P_ i \in unitmx by rewrite /P_; case: {+}Pof.
have P_diag i A : A \in As -> similar_diag (P_ i *m row_base (V_ i)) A.
  move=> AAs; rewrite /P_; case: {+}Pof => /= P Punit.
  rewrite all_map => /allP/(_ A AAs); rewrite /similar_to/=.
  by rewrite conjuMmx ?row_base_free ?stablemx_row_base ?AV.
pose P := \mxcol_i (P_ i *m row_base (V_ i)).
have P_full i : row_full (P_ i) by rewrite row_full_unit.
have PrV i : (P_ i *m row_base (V_ i) :=: V_ i)%MS.
  exact/(eqmx_trans _ (eq_row_base _))/eqmxMfull.
apply/codiagonalizablePfull; eexists _; last exists P; rewrite /=.
- rewrite -sub1mx eqmx_col.
  by under eq_bigr do rewrite (eq_genmx (PrV _)); rewrite -genmx_sums genmxE V1.
apply/allP => A AAs /=; rewrite similar_diag_sum.
- by apply/forallP => i; apply: P_diag.
- rewrite mxdirectE/=.
  under eq_bigr do rewrite (eq_genmx (PrV _)); rewrite -genmx_sums genmxE V1.
  by under eq_bigr do rewrite genmxE PrV; rewrite  -(mxdirectP Vdirect)//= V1.
- by move=> i; rewrite (eqmx_stable _ (PrV _)) ?AV.
- by move=> i; rewrite /row_free eqmxMfull ?eq_row_base ?row_full_unit.
Qed.

Lemma diagonalizable_diag {n} (d : 'rV[F]_n) : diagonalizable (diag_mx d).
Proof.
by exists 1%:M; rewrite ?unitmx1// /similar_to conj1mx diag_mx_is_diag.
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

Lemma diagonalizablePeigen {n} {f : 'M[F]_n} :
  diagonalizable f <->
  exists2 rs, uniq rs & (\sum_(r <- rs) eigenspace f r :=: 1%:M)%MS.
Proof.
split=> [df|[rs urs rsP]].
  suff [rs rsP] : exists rs, (\sum_(r <- rs) eigenspace f r :=: 1%:M)%MS.
    exists (undup rs); rewrite ?undup_uniq//; apply: eqmx_trans rsP.
    elim: rs => //= r rs IHrs; rewrite big_cons.
    case: ifPn => in_rs; rewrite ?big_cons; last exact: adds_eqmx.
    apply/(eqmx_trans IHrs)/eqmx_sym/addsmx_idPr.
    have rrs : (index r rs < size rs)%N by rewrite index_mem.
    rewrite (big_nth 0) big_mkord (sumsmx_sup (Ordinal rrs)) ?nth_index//.
  move: df => [P Punit /(similar_diagLR Punit)[d ->]].
  exists [seq d 0 i | i <- enum 'I_n]; rewrite big_image/=.
  apply: (@eqmx_trans _ _ _ _ _ _ P); apply/eqmxP;
    rewrite ?sub1mx ?submx1 ?row_full_unit//.
  rewrite submx_full ?row_full_unit//=.
  apply/row_subP => i; rewrite rowE (sumsmx_sup i)//.
  apply/eigenspaceP; rewrite conjVmx// !mulmxA mulmxK//.
  by rewrite -rowE row_diag_mx scalemxAl.
have mxdirect_eigenspaces : mxdirect (\sum_(i < size rs) eigenspace f rs`_i).
  apply: mxdirect_sum_eigenspace => i j _ _ rsij; apply/val_inj.
  by apply: uniqP rsij; rewrite ?inE.
rewrite (big_nth 0) big_mkord in rsP; rewrite -codiagonalizable1.
apply/(codiagonalizable_on _ mxdirect_eigenspaces) => // i/=.
  case: n => [|n] in f {mxdirect_eigenspaces} rsP *.
    by rewrite thinmx0 sub0mx.
  by rewrite comm_mx_stable_eigenspace.
rewrite codiagonalizable1.
by rewrite (@conjmx_eigenvalue _ _ _ rs`_i) ?eq_row_base ?row_base_free.
Qed.

Lemma diagonalizableP n' (n := n'.+1) (f : 'M[F]_n) :
  diagonalizable f <->
  exists2 rs, uniq rs & mxminpoly f %| \prod_(x <- rs) ('X - x%:P).
Proof.
split=> [[P Punit /similar_diagPex[d /(similarLR Punit)->]]|].
  rewrite mxminpoly_uconj ?unitmx_inv// mxminpoly_diag.
  by eexists; [|by []]; rewrite undup_uniq.
rewrite diagonalizablePeigen => -[rs rsu rsP].
exists rs; rewrite // !(big_nth 0) !big_mkord in rsP *.
rewrite (eq_bigr _ (fun _ _ => eigenspace_poly _ _)).
apply: (eqmx_trans (eqmx_sym (kermxpoly_prod _ _)) (kermxpoly_min _)) => //.
by move=> i j _ _; rewrite coprimep_XsubC root_XsubC nth_uniq.
Qed.

Lemma diagonalizable_conj_diag m n (V : 'M[F]_(m, n)) (d : 'rV[F]_n) :
  stablemx V (diag_mx d) -> row_free V -> diagonalizable (conjmx V (diag_mx d)).
Proof.
case: m n => [|m] [|n]// in V d * => Vd rdV; rewrite ?thinmx0//=.
apply/diagonalizableP; pose u := undup [seq d 0 i | i <- enum 'I_n.+1].
exists u; first by rewrite undup_uniq.
by rewrite (dvdp_trans (mxminpoly_conj _ _))// mxminpoly_diag.
Qed.

Lemma codiagonalizableP n (fs : seq 'M[F]_n) :
  {in fs &, forall f g, comm_mx f g} /\ (forall f, f \in fs -> diagonalizable f)
  <-> codiagonalizable fs.
Proof.
split => [cdfs|[P Punit /allP/= fsD]]/=; last first.
  split; last by exists P; rewrite // fsD.
  move=> f g ffs gfs; move=> /(_ _ _)/similar_diagPex/sigW in fsD.
  have [[df /similarLR->//] [dg /similarLR->//]] := (fsD _ ffs, fsD _ gfs).
  by rewrite /comm_mx -!conjmxM 1?diag_mxC// inE stablemx_unit ?unitmx_inv.
move: cdfs; rewrite (rwP (all_comm_mxP _)) => cdfs.
have [k] := ubnP (size fs); elim: k => [|k IHk]//= in n fs cdfs *.
case: fs cdfs => [|f fs]//=; first by exists 1%:M; rewrite ?unitmx1.
rewrite ltnS all_comm_mx_cons => -[/andP[/allP/(_ _ _)/eqP ffsC fsC dffs]] fsk.
have /diagonalizablePeigen [rs urs rs1] := dffs _ (mem_head _ _).
rewrite (big_nth 0) big_mkord in rs1.
have efg (i : 'I_(size rs)) g : g \in f :: fs -> stablemx (eigenspace f rs`_i) g.
   case: n => [|n'] in g f fs ffsC fsC {dffs rs1 fsk} * => g_ffs.
      by rewrite thinmx0 sub0mx.
  rewrite comm_mx_stable_eigenspace//.
  by move: g_ffs; rewrite !inE => /predU1P [->//|/ffsC].
apply/(@codiagonalizable_on _ _ _ (_ :: _) rs1) => [|i|i /=].
- apply: mxdirect_sum_eigenspace => i j _ _ rsij; apply/val_inj.
  by apply: uniqP rsij; rewrite ?inE.
- by apply/allP => g g_ffs; rewrite efg.
rewrite (@conjmx_eigenvalue _ _ _ rs`_i) ?eq_row_base ?row_base_free//.
set gs := map _ _; suff [P Punit /= Pgs] : codiagonalizable gs.
  exists P; rewrite /= ?Pgs ?andbT// /similar_to.
  by rewrite conjmx_scalar ?mx_scalar_is_diag// row_free_unit.
apply: IHk; rewrite ?size_map/= ?ltnS//; split.
  apply/all_comm_mxP => _ _ /mapP[/= g gfs ->] /mapP[/= h hfs ->].
  rewrite -!conjmxM ?inE ?stablemx_row_base ?efg ?inE ?gfs ?hfs ?orbT//.
  by rewrite (all_comm_mxP _ fsC).
move=> _ /mapP[/= g gfs ->].
have: stablemx (row_base (eigenspace f rs`_i)) g.
  by rewrite stablemx_row_base efg// inE gfs orbT.
have := dffs g; rewrite inE gfs orbT => /(_ isT) [P Punit].
move=> /similar_diagPex[D /(similarLR Punit)->] sePD.
have rfeP : row_free (row_base (eigenspace f rs`_i) *m invmx P).
  by rewrite /row_free mxrankMfree ?row_free_unit ?unitmx_inv// eq_row_base.
rewrite -conjMumx ?unitmx_inv ?row_base_free//.
apply/diagonalizable_conj_diag => //.
by rewrite stablemx_comp// stablemx_unit ?unitmx_inv.
Qed.

End Diag.

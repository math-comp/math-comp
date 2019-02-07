(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrbool ssrfun eqtype ssrnat seq path div choice.
From mathcomp
Require Import fintype tuple finfun bigop prime ssralg poly finset.
From mathcomp
Require Import fingroup morphism perm automorphism quotient gproduct action.
From mathcomp
Require Import finalg zmodp commutator cyclic center pgroup gseries nilpotent.
From mathcomp
Require Import sylow maximal abelian matrix mxalgebra mxrepresentation.

(******************************************************************************)
(*   This file completes the theory developed in mxrepresentation.v with the  *)
(* construction and properties of linear representations over finite fields,  *)
(* and in particular the correspondance between internal action on a (normal) *)
(* elementary abelian p-subgroup and a linear representation on an Fp-module. *)
(*   We provide the following next constructions for a finite field F:        *)
(*        'Zm%act == the action of {unit F} on 'M[F]_(m, n).                  *)
(*         rowg A == the additive group of 'rV[F]_n spanned by the row space  *)
(*                   of the matrix A.                                         *)
(*      rowg_mx L == the partial inverse to rowg; for any 'Zm-stable group L  *)
(*                   of 'rV[F]_n we have rowg (rowg_mx L) = L.                *)
(*     GLrepr F n == the natural, faithful representation of 'GL_n[F].        *)
(*     reprGLm rG == the morphism G >-> 'GL_n[F] equivalent to the            *)
(*                   representation r of G (with rG : mx_repr r G).           *)
(*   ('MR rG)%act == the action of G on 'rV[F]_n equivalent to the            *)
(*                   representation r of G (with rG : mx_repr r G).           *)
(* The second set of constructions defines the interpretation of a normal     *)
(* non-trivial elementary abelian p-subgroup as an 'F_p module. We assume     *)
(* abelE : p.-abelem E and ntE : E != 1, throughout, as these are needed to   *)
(* build the isomorphism between E and a nontrivial 'rV['F_p]_n.              *)
(*         'rV(E) == the type of row vectors of the 'F_p module equivalent    *)
(*                   to E when E is a non-trivial p.-abelem group.            *)
(*          'M(E) == the type of matrices corresponding to E.                 *)
(*         'dim E == the width of vectors/matrices in 'rV(E) / 'M(E).         *)
(* abelem_rV abelE ntE == the one-to-one injection of E onto 'rV(E).          *)
(*  rVabelem abelE ntE == the one-to-one projection of 'rV(E) onto E.         *)
(* abelem_repr abelE ntE nEG == the representation of G on 'rV(E) that is     *)
(*                   equivalent to conjugation by G in E; here abelE, ntE are *)
(*                   as above, and G \subset 'N(E).                           *)
(* This file end with basic results on p-modular representations of p-groups, *)
(* and theorems giving the structure of the representation of extraspecial    *)
(* groups; these results use somewhat more advanced group theory than the     *)
(* rest of mxrepresentation, in particular, results of sylow.v and maximal.v. *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory FinRing.Theory.
Local Open Scope ring_scope.

(* Special results for representations on a finite field. In this case, the   *)
(* representation is equivalent to a morphism into the general linear group   *)
(* 'GL_n[F]. It is furthermore equivalent to a group action on the finite     *)
(* additive group of the corresponding row space 'rV_n. In addition, row      *)
(* spaces of matrices in 'M[F]_n correspond to subgroups of that vector group *)
(* (this is only surjective when F is a prime field 'F_p), with moduleules    *)
(* corresponding to subgroups stabilized by the external action.              *)

Section FinRingRepr.

Variable (R : finComUnitRingType) (gT : finGroupType).
Variables (G : {group gT}) (n : nat) (rG : mx_representation R G n).

Definition mx_repr_act (u : 'rV_n) x := u *m rG (val (subg G x)).

Lemma mx_repr_actE u x : x \in G -> mx_repr_act u x = u *m rG x.
Proof. by move=> Gx; rewrite /mx_repr_act /= subgK. Qed.

Fact mx_repr_is_action : is_action G mx_repr_act.
Proof.
split=> [x | u x y Gx Gy]; first exact: can_inj (repr_mxK _ (subgP _)).
by rewrite !mx_repr_actE ?groupM // -mulmxA repr_mxM.
Qed.
Canonical Structure mx_repr_action := Action mx_repr_is_action.

Fact mx_repr_is_groupAction : is_groupAction [set: 'rV[R]_n] mx_repr_action.
Proof.
move=> x Gx /=; rewrite !inE.
apply/andP; split; first by apply/subsetP=> u; rewrite !inE.
by apply/morphicP=> /= u v _ _; rewrite !actpermE /= /mx_repr_act mulmxDl.
Qed.
Canonical Structure mx_repr_groupAction := GroupAction mx_repr_is_groupAction.

End FinRingRepr.

Notation "''MR' rG" := (mx_repr_action rG)
  (at level 10, rG at level 8) : action_scope.
Notation "''MR' rG" := (mx_repr_groupAction rG) : groupAction_scope.

Section FinFieldRepr.

Variable F : finFieldType.

(* The external group action (by scaling) of the multiplicative unit group   *)
(* of the finite field, and the correspondence between additive subgroups    *)
(* of row vectors that are stable by this action, and the matrix row spaces. *)
Section ScaleAction.

Variables m n : nat.

Definition scale_act (A : 'M[F]_(m, n)) (a : {unit F}) := val a *: A.
Lemma scale_actE A a : scale_act A a = val a *: A. Proof. by []. Qed.
Fact scale_is_action : is_action setT scale_act.
Proof.
apply: is_total_action=> [A | A a b]; rewrite /scale_act ?scale1r //.
by rewrite ?scalerA mulrC.
Qed.
Canonical scale_action := Action scale_is_action.
Fact scale_is_groupAction : is_groupAction setT scale_action.
Proof.
move=> a _ /=; rewrite inE; apply/andP.
split; first by apply/subsetP=> A; rewrite !inE.
by apply/morphicP=> u A _ _ /=; rewrite !actpermE /= /scale_act scalerDr.
Qed.
Canonical scale_groupAction := GroupAction scale_is_groupAction.

Lemma astab1_scale_act A : A != 0 -> 'C[A | scale_action] = 1%g.
Proof.
rewrite -mxrank_eq0=> nzA; apply/trivgP/subsetP=> a; apply: contraLR.
rewrite !inE -val_eqE -subr_eq0 sub1set !inE => nz_a1.
by rewrite -subr_eq0 -scaleN1r -scalerDl -mxrank_eq0 eqmx_scale.
Qed.

End ScaleAction.

Local Notation "'Zm" := (scale_action _ _) (at level 8) : action_scope.

Section RowGroup.

Variable n : nat.
Local Notation rVn := 'rV[F]_n.

Definition rowg m (A : 'M[F]_(m, n)) : {set rVn} := [set u | u <= A]%MS.

Lemma mem_rowg m A v : (v \in @rowg m A) = (v <= A)%MS.
Proof. by rewrite inE. Qed.

Fact rowg_group_set m A : group_set (@rowg m A).
Proof.
by apply/group_setP; split=> [|u v]; rewrite !inE ?sub0mx //; apply: addmx_sub.
Qed.
Canonical rowg_group m A := Group (@rowg_group_set m A).

Lemma rowg_stable m (A : 'M_(m, n)) : [acts setT, on rowg A | 'Zm].
Proof. by apply/actsP=> a _ v; rewrite !inE eqmx_scale // -unitfE (valP a). Qed.

Lemma rowgS m1 m2 (A : 'M_(m1, n)) (B : 'M_(m2, n)) :
  (rowg A \subset rowg B) = (A <= B)%MS.
Proof.
apply/subsetP/idP=> sAB => [| u].
  by apply/row_subP=> i; have:= sAB (row i A); rewrite !inE row_sub => ->.
by rewrite !inE => suA; apply: submx_trans sAB.
Qed.

Lemma eq_rowg m1 m2 (A : 'M_(m1, n)) (B : 'M_(m2, n)) :
  (A :=: B)%MS -> rowg A = rowg B.
Proof. by move=> eqAB; apply/eqP; rewrite eqEsubset !rowgS !eqAB andbb. Qed.

Lemma rowg0 m : rowg (0 : 'M_(m, n)) = 1%g.
Proof. by apply/trivgP/subsetP=> v; rewrite !inE eqmx0 submx0. Qed.

Lemma rowg1 : rowg 1%:M = setT.
Proof. by apply/setP=> x; rewrite !inE submx1. Qed.

Lemma trivg_rowg m (A : 'M_(m, n)) : (rowg A == 1%g) = (A == 0).
Proof. by rewrite -submx0 -rowgS rowg0 (sameP trivgP eqP). Qed.

Definition rowg_mx (L : {set rVn}) := <<\matrix_(i < #|L|) enum_val i>>%MS.

Lemma rowgK m (A : 'M_(m, n)) : (rowg_mx (rowg A) :=: A)%MS.
Proof.
apply/eqmxP; rewrite !genmxE; apply/andP; split.
  by apply/row_subP=> i; rewrite rowK; have:= enum_valP i; rewrite /= inE.
apply/row_subP=> i; set v := row i A.
have Av: v \in rowg A by rewrite inE row_sub.
by rewrite (eq_row_sub (enum_rank_in Av v)) // rowK enum_rankK_in.
Qed.

Lemma rowg_mxS (L M : {set 'rV[F]_n}) :
  L \subset M -> (rowg_mx L <= rowg_mx M)%MS.
Proof.
move/subsetP=> sLM; rewrite !genmxE; apply/row_subP=> i.
rewrite rowK; move: (enum_val i) (sLM _ (enum_valP i)) => v Mv.
by rewrite (eq_row_sub (enum_rank_in Mv v)) // rowK enum_rankK_in.
Qed.

Lemma sub_rowg_mx (L : {set rVn}) : L \subset rowg (rowg_mx L).
Proof.
apply/subsetP=> v Lv; rewrite inE genmxE.
by rewrite (eq_row_sub (enum_rank_in Lv v)) // rowK enum_rankK_in.
Qed.

Lemma stable_rowg_mxK (L : {group rVn}) :
  [acts setT, on L | 'Zm] -> rowg (rowg_mx L) = L.
Proof.
move=> linL; apply/eqP; rewrite eqEsubset sub_rowg_mx andbT.
apply/subsetP=> v; rewrite inE genmxE => /submxP[u ->{v}].
rewrite mulmx_sum_row group_prod // => i _.
rewrite rowK; move: (enum_val i) (enum_valP i) => v Lv.
case: (eqVneq (u 0 i) 0) => [->|]; first by rewrite scale0r group1.
by rewrite -unitfE => aP; rewrite ((actsP linL) (FinRing.Unit _ aP)) ?inE.
Qed.

Lemma rowg_mx1 : rowg_mx 1%g = 0.
Proof. by apply/eqP; rewrite -submx0 -(rowg0 0) rowgK sub0mx. Qed.

Lemma rowg_mx_eq0 (L : {group rVn}) : (rowg_mx L == 0) = (L :==: 1%g).
Proof.
rewrite -trivg_rowg; apply/idP/eqP=> [|->]; last by rewrite rowg_mx1 rowg0.
exact/contraTeq/subG1_contra/sub_rowg_mx.
Qed.

Lemma rowgI m1 m2 (A : 'M_(m1, n)) (B : 'M_(m2, n)) :
  rowg (A :&: B)%MS = rowg A :&: rowg B.
Proof. by apply/setP=> u; rewrite !inE sub_capmx. Qed.

Lemma card_rowg m (A : 'M_(m, n)) : #|rowg A| = (#|F| ^ \rank A)%N.
Proof.
rewrite -[\rank A]mul1n -card_matrix.
have injA: injective (mulmxr (row_base A)).
  have /row_freeP[A' A'K] := row_base_free A.
  by move=> ?; apply: can_inj (mulmxr A') _ => u; rewrite /= -mulmxA A'K mulmx1.
rewrite -(card_image (injA _)); apply: eq_card => v.
by rewrite inE -(eq_row_base A) (sameP submxP codomP).
Qed.

Lemma rowgD m1 m2 (A : 'M_(m1, n)) (B : 'M_(m2, n)) :
  rowg (A + B)%MS = (rowg A * rowg B)%g.
Proof.
apply/eqP; rewrite eq_sym eqEcard mulG_subG /= !rowgS.
rewrite addsmxSl addsmxSr -(@leq_pmul2r #|rowg A :&: rowg B|) ?cardG_gt0 //=.
by rewrite -mul_cardG -rowgI !card_rowg -!expnD mxrank_sum_cap.
Qed.

Lemma cprod_rowg m1 m2 (A : 'M_(m1, n)) (B : 'M_(m2, n)) :
  rowg A \* rowg B = rowg (A + B)%MS.
Proof. by rewrite rowgD cprodE // (sub_abelian_cent2 (zmod_abelian setT)). Qed.

Lemma dprod_rowg  m1 m2 (A : 'M[F]_(m1, n)) (B : 'M[F]_(m2, n)) :
  mxdirect (A + B) -> rowg A \x rowg B = rowg (A + B)%MS.
Proof.
rewrite (sameP mxdirect_addsP eqP) -trivg_rowg rowgI => /eqP tiAB.
by rewrite -cprod_rowg dprodEcp.
Qed.

Lemma bigcprod_rowg m I r (P : pred I) (A : I -> 'M[F]_n) (B : 'M[F]_(m, n)) :
    (\sum_(i <- r | P i) A i :=: B)%MS ->
  \big[cprod/1%g]_(i <- r | P i) rowg (A i) = rowg B.
Proof.
by move/eq_rowg <-; apply/esym/big_morph=> [? ?|]; rewrite (rowg0, cprod_rowg).
Qed.

Lemma bigdprod_rowg m (I : finType) (P : pred I) A (B : 'M[F]_(m, n)) :
    let S := (\sum_(i | P i) A i)%MS in (S :=: B)%MS -> mxdirect S ->
  \big[dprod/1%g]_(i | P i) rowg (A i) = rowg B.
Proof.
move=> S defS; rewrite mxdirectE defS /= => /eqP rankB.
apply: bigcprod_card_dprod (bigcprod_rowg defS) (eq_leq _).
by rewrite card_rowg rankB expn_sum; apply: eq_bigr => i _; rewrite card_rowg.
Qed.

End RowGroup.

Variables (gT : finGroupType) (G : {group gT}) (n' : nat).
Local Notation n := n'.+1.
Variable (rG : mx_representation F G n).

Fact GL_mx_repr : mx_repr 'GL_n[F] GLval. Proof. by []. Qed.
Canonical GLrepr := MxRepresentation GL_mx_repr.

Lemma GLmx_faithful : mx_faithful GLrepr.
Proof. by apply/subsetP=> A; rewrite !inE mul1mx. Qed.

Definition reprGLm x : {'GL_n[F]} := insubd (1%g : {'GL_n[F]}) (rG x).

Lemma val_reprGLm x : x \in G -> val (reprGLm x) = rG x.
Proof. by move=> Gx; rewrite val_insubd (repr_mx_unitr rG). Qed.

Lemma comp_reprGLm : {in G, GLval \o reprGLm =1 rG}.
Proof. exact: val_reprGLm. Qed.

Lemma reprGLmM : {in G &, {morph reprGLm : x y / x * y}}%g.
Proof.
by move=> x y Gx Gy; apply: val_inj; rewrite /= !val_reprGLm ?groupM ?repr_mxM.
Qed.
Canonical reprGL_morphism := Morphism reprGLmM.

Lemma ker_reprGLm : 'ker reprGLm = rker rG.
Proof.
apply/setP=> x; rewrite !inE mul1mx; apply: andb_id2l => Gx.
by rewrite -val_eqE val_reprGLm.
Qed.

Lemma astab_rowg_repr m (A : 'M_(m, n)) : 'C(rowg A | 'MR rG) = rstab rG A.
Proof.
apply/setP=> x; rewrite !inE /=; apply: andb_id2l => Gx.
apply/subsetP/eqP=> cAx => [|u]; last first.
  by rewrite !inE mx_repr_actE // => /submxP[u' ->]; rewrite -mulmxA cAx.
apply/row_matrixP=> i; apply/eqP; move/implyP: (cAx (row i A)).
by rewrite !inE row_sub mx_repr_actE //= row_mul.
Qed.

Lemma astabs_rowg_repr m (A : 'M_(m, n)) : 'N(rowg A | 'MR rG) = rstabs rG A.
Proof.
apply/setP=> x; rewrite !inE /=; apply: andb_id2l => Gx.
apply/subsetP/idP=> nAx => [|u]; last first.
  by rewrite !inE mx_repr_actE // => Au; apply: (submx_trans (submxMr _ Au)).
apply/row_subP=> i; move/implyP: (nAx (row i A)).
by rewrite !inE row_sub mx_repr_actE //= row_mul.
Qed.

Lemma acts_rowg (A : 'M_n) : [acts G, on rowg A | 'MR rG] = mxmodule rG A.
Proof. by rewrite astabs_rowg_repr. Qed.

Lemma astab_setT_repr : 'C(setT | 'MR rG) = rker rG.
Proof. by rewrite -rowg1 astab_rowg_repr. Qed.

Lemma mx_repr_action_faithful :
  [faithful G, on setT | 'MR rG] = mx_faithful rG.
Proof.
by rewrite /faithful astab_setT_repr (setIidPr _) // [rker _]setIdE subsetIl.
Qed.

Lemma afix_repr (H : {set gT}) :
  H \subset G -> 'Fix_('MR rG)(H) = rowg (rfix_mx rG H).
Proof.
move/subsetP=> sHG; apply/setP=> /= u; rewrite !inE.
apply/subsetP/rfix_mxP=> cHu x Hx; have:= cHu x Hx;
  by rewrite !inE /= => /eqP; rewrite mx_repr_actE ?sHG.
Qed.

Lemma gacent_repr (H : {set gT}) :
  H \subset G -> 'C_(| 'MR rG)(H) = rowg (rfix_mx rG H).
Proof. by move=> sHG; rewrite gacentE // setTI afix_repr. Qed.

End FinFieldRepr.

Arguments rowg_mx {F n%N} L%g.
Notation "''Zm'" := (scale_action _ _ _) (at level 8) : action_scope.
Notation "''Zm'" := (scale_groupAction _ _ _) : groupAction_scope.

Section MatrixGroups.

Implicit Types m n p q : nat.

Lemma exponent_mx_group m n q :
  m > 0 -> n > 0 -> q > 1 -> exponent [set: 'M['Z_q]_(m, n)] = q.
Proof.
move=> m_gt0 n_gt0 q_gt1; apply/eqP; rewrite eqn_dvd; apply/andP; split.
  apply/exponentP=> x _; apply/matrixP=> i j; rewrite mulmxnE !mxE.
  by rewrite -mulr_natr -Zp_nat_mod // modnn mulr0.
pose cmx1 := const_mx 1%R : 'M['Z_q]_(m, n).
apply: dvdn_trans (dvdn_exponent (in_setT cmx1)).
have/matrixP/(_ (Ordinal m_gt0))/(_ (Ordinal n_gt0))/eqP := expg_order cmx1.
by rewrite mulmxnE !mxE -order_dvdn order_Zp1 Zp_cast.
Qed.

Lemma rank_mx_group m n q : 'r([set: 'M['Z_q]_(m, n)]) = (m * n)%N.
Proof.
wlog q_gt1: q / q > 1 by case: q => [|[|q -> //]] /(_ 2)->.
set G := setT; have cGG: abelian G := zmod_abelian _.
have [mn0 | ] := posnP (m * n).
  by rewrite [G](card1_trivg _) ?rank1 // cardsT card_matrix mn0.
rewrite muln_gt0 => /andP[m_gt0 n_gt0].
have expG: exponent G = q := exponent_mx_group m_gt0 n_gt0 q_gt1.
apply/eqP; rewrite eqn_leq andbC -(leq_exp2l _ _ q_gt1) -{2}expG.
have ->: (q ^ (m * n))%N = #|G| by rewrite cardsT card_matrix card_ord Zp_cast.
rewrite max_card_abelian //= -grank_abelian //= -/G.
pose B : {set 'M['Z_q]_(m, n)} := [set delta_mx ij.1 ij.2 | ij : 'I_m * 'I_n].
suffices ->: G = <<B>>.
  have ->: (m * n)%N = #|{: 'I_m * 'I_n}| by rewrite card_prod !card_ord.
  exact: leq_trans (grank_min _) (leq_imset_card _ _).
apply/setP=> v; rewrite inE (matrix_sum_delta v).
rewrite group_prod // => i _; rewrite group_prod // => j _.
rewrite -[v i j]natr_Zp scaler_nat groupX // mem_gen //.
by apply/imsetP; exists (i, j).
Qed.

Lemma mx_group_homocyclic m n q : homocyclic [set: 'M['Z_q]_(m, n)].
Proof.
wlog q_gt1: q / q > 1 by case: q => [|[|q -> //]] /(_ 2)->.
set G := setT; have cGG: abelian G := zmod_abelian _.
rewrite -max_card_abelian //= rank_mx_group cardsT card_matrix card_ord -/G.
rewrite {1}Zp_cast //; have [-> // | ] := posnP (m * n).
by rewrite muln_gt0 => /andP[m_gt0 n_gt0]; rewrite exponent_mx_group.
Qed.

Lemma abelian_type_mx_group m n q :
  q > 1 -> abelian_type [set: 'M['Z_q]_(m, n)] = nseq (m * n) q.
Proof.
rewrite (abelian_type_homocyclic (mx_group_homocyclic m n q)) rank_mx_group.
have [-> // | ] := posnP (m * n); rewrite muln_gt0 => /andP[m_gt0 n_gt0] q_gt1.
by rewrite exponent_mx_group.
Qed.

End MatrixGroups.

Delimit Scope abelem_scope with Mg.
Open Scope abelem_scope.

Definition abelem_dim' (gT : finGroupType) (E : {set gT}) :=
  (logn (pdiv #|E|) #|E|).-1.
Arguments abelem_dim' {gT} E%g.
Notation "''dim' E" := (abelem_dim' E).+1
  (at level 10, E at level 8, format "''dim'  E") : abelem_scope.

Notation "''rV' ( E )" := 'rV_('dim E)
  (at level 8, format "''rV' ( E )") : abelem_scope.
Notation "''M' ( E )" := 'M_('dim E)
  (at level 8, format "''M' ( E )") : abelem_scope.
Notation "''rV[' F ] ( E )" := 'rV[F]_('dim E)
  (at level 8, only parsing) : abelem_scope.
Notation "''M[' F ] ( E )" := 'M[F]_('dim E)
  (at level 8, only parsing) : abelem_scope.

Section AbelemRepr.

Section FpMatrix.

Variables p m n : nat.
Local Notation Mmn := 'M['F_p]_(m, n).

Lemma mx_Fp_abelem : prime p -> p.-abelem [set: Mmn].
Proof. exact: fin_Fp_lmod_abelem. Qed.

Lemma mx_Fp_stable (L : {group Mmn}) : [acts setT, on L | 'Zm].
Proof.
apply/subsetP=> a _; rewrite !inE; apply/subsetP=> A L_A.
by rewrite inE /= /scale_act -[val _]natr_Zp scaler_nat groupX.
Qed.

End FpMatrix.

Section FpRow.

Variables p n : nat.
Local Notation rVn := 'rV['F_p]_n.

Lemma rowg_mxK (L : {group rVn}) : rowg (rowg_mx L) = L.
Proof. by apply: stable_rowg_mxK; apply: mx_Fp_stable. Qed.

Lemma rowg_mxSK (L : {set rVn}) (M : {group rVn}) :
  (rowg_mx L <= rowg_mx M)%MS = (L \subset M).
Proof.
apply/idP/idP; last exact: rowg_mxS.
by rewrite -rowgS rowg_mxK; apply/subset_trans/sub_rowg_mx.
Qed.

Lemma mxrank_rowg (L : {group rVn}) :
  prime p -> \rank (rowg_mx L) = logn p #|L|.
Proof.
by move=> p_pr; rewrite -{2}(rowg_mxK L) card_rowg card_Fp ?pfactorK.
Qed.

End FpRow.

Variables (p : nat) (gT : finGroupType) (E : {group gT}).
Hypotheses (abelE : p.-abelem E) (ntE : E :!=: 1%g).

Let pE : p.-group E := abelem_pgroup abelE.
Let p_pr : prime p. Proof. by have [] := pgroup_pdiv pE ntE. Qed.

Local Notation n' := (abelem_dim' (gval E)).
Local Notation n := n'.+1.
Local Notation rVn := 'rV['F_p](gval E).

Lemma dim_abelemE : n = logn p #|E|.
Proof.
rewrite /n'; have [_ _ [k ->]] :=  pgroup_pdiv pE ntE.
by rewrite /pdiv primes_exp ?primes_prime // pfactorK.
Qed.

Lemma card_abelem_rV : #|rVn| = #|E|.
Proof.
by rewrite dim_abelemE card_matrix mul1n card_Fp // -p_part part_pnat_id.
Qed.

Lemma isog_abelem_rV : E \isog [set: rVn].
Proof.
by rewrite (isog_abelem_card _ abelE) cardsT card_abelem_rV mx_Fp_abelem /=.
Qed.

Local Notation ab_rV_P := (existsP isog_abelem_rV).
Definition abelem_rV : gT -> rVn := xchoose ab_rV_P.

Local Notation ErV := abelem_rV.

Lemma abelem_rV_M : {in E &, {morph ErV : x y / (x * y)%g >-> x + y}}.
Proof. by case/misomP: (xchooseP ab_rV_P) => fM _; move/morphicP: fM. Qed.

Canonical abelem_rV_morphism := Morphism abelem_rV_M.

Lemma abelem_rV_isom : isom E setT ErV.
Proof. by case/misomP: (xchooseP ab_rV_P). Qed.

Lemma abelem_rV_injm : 'injm ErV. Proof. by case/isomP: abelem_rV_isom. Qed.

Lemma abelem_rV_inj : {in E &, injective ErV}.
Proof. by apply/injmP; apply: abelem_rV_injm. Qed.

Lemma im_abelem_rV : ErV @* E = setT. Proof. by case/isomP: abelem_rV_isom. Qed.

Lemma mem_im_abelem_rV u : u \in ErV @* E.
Proof. by rewrite im_abelem_rV inE. Qed.

Lemma sub_im_abelem_rV mA : subset mA (mem (ErV @* E)).
Proof. by rewrite unlock; apply/pred0P=> v /=; rewrite mem_im_abelem_rV. Qed.
Hint Resolve mem_im_abelem_rV sub_im_abelem_rV : core.

Lemma abelem_rV_1 : ErV 1 = 0%R. Proof. by rewrite morph1. Qed.

Lemma abelem_rV_X x i : x \in E -> ErV (x ^+ i) = i%:R *: ErV x.
Proof. by move=> Ex; rewrite morphX // scaler_nat. Qed.

Lemma abelem_rV_V x : x \in E -> ErV x^-1 = - ErV x.
Proof. by move=> Ex; rewrite morphV. Qed.

Definition rVabelem : rVn -> gT := invm abelem_rV_injm.
Canonical rVabelem_morphism := [morphism of rVabelem].
Local Notation rV_E := rVabelem.

Lemma rVabelem0 : rV_E 0 = 1%g. Proof. exact: morph1. Qed.

Lemma rVabelemD : {morph rV_E : u v / u + v >-> (u * v)%g}.
Proof. by move=> u v /=; rewrite -morphM. Qed.

Lemma rVabelemN : {morph rV_E: u / - u >-> (u^-1)%g}.
Proof. by move=> u /=; rewrite -morphV. Qed.

Lemma rVabelemZ (m : 'F_p) : {morph rV_E : u / m *: u >-> (u ^+ m)%g}.
Proof. by move=> u; rewrite /= -morphX -?[(u ^+ m)%g]scaler_nat ?natr_Zp. Qed.

Lemma abelem_rV_K : {in E, cancel ErV rV_E}. Proof. exact: invmE. Qed.

Lemma rVabelemK : cancel rV_E ErV. Proof. by move=> u; rewrite invmK. Qed.

Lemma rVabelem_inj : injective rV_E. Proof. exact: can_inj rVabelemK. Qed.

Lemma rVabelem_injm : 'injm rV_E. Proof. exact: injm_invm abelem_rV_injm. Qed.

Lemma im_rVabelem : rV_E @* setT = E.
Proof. by rewrite -im_abelem_rV im_invm. Qed.

Lemma mem_rVabelem u : rV_E u \in E.
Proof. by rewrite -im_rVabelem mem_morphim. Qed.

Lemma sub_rVabelem L : rV_E @* L \subset E.
Proof. by rewrite -[_ @* L]morphimIim im_invm subsetIl. Qed.
Hint Resolve mem_rVabelem sub_rVabelem : core.

Lemma card_rVabelem L : #|rV_E @* L| = #|L|.
Proof. by rewrite card_injm ?rVabelem_injm. Qed.

Lemma abelem_rV_mK (H : {set gT}) : H \subset E -> rV_E @* (ErV @* H) = H.
Proof. exact: morphim_invm abelem_rV_injm H. Qed.

Lemma rVabelem_mK L : ErV @* (rV_E @* L) = L.
Proof. by rewrite morphim_invmE morphpreK. Qed.

Lemma rVabelem_minj : injective (morphim (MorPhantom rV_E)).
Proof. exact: can_inj rVabelem_mK. Qed.

Lemma rVabelemS L M : (rV_E @* L \subset rV_E @* M) = (L \subset M).
Proof. by rewrite injmSK ?rVabelem_injm. Qed.

Lemma abelem_rV_S (H K : {set gT}) :
  H \subset E -> (ErV @* H \subset ErV @* K) = (H \subset K).
Proof. by move=> sHE; rewrite injmSK ?abelem_rV_injm. Qed.

Lemma sub_rVabelem_im L (H : {set gT}) :
  (rV_E @* L \subset H) = (L \subset ErV @* H).
Proof. by rewrite sub_morphim_pre ?morphpre_invm. Qed.

Lemma sub_abelem_rV_im (H : {set gT}) (L : {set 'rV['F_p]_n}) :
  H \subset E -> (ErV @* H \subset L) = (H \subset rV_E @* L).
Proof. by move=> sHE; rewrite sub_morphim_pre ?morphim_invmE. Qed.

Section OneGroup.

Variable G : {group gT}.
Definition abelem_mx_fun (g : subg_of G) v := ErV ((rV_E v) ^ val g).
Definition abelem_mx of G \subset 'N(E) :=
  fun x => lin1_mx (abelem_mx_fun (subg G x)).

Hypothesis nEG : G \subset 'N(E).
Local Notation r := (abelem_mx nEG).

Fact abelem_mx_linear_proof g : linear (abelem_mx_fun g).
Proof.
rewrite /abelem_mx_fun; case: g => x /= /(subsetP nEG) Nx /= m u v.
rewrite rVabelemD rVabelemZ conjMg conjXg.
by rewrite abelem_rV_M ?abelem_rV_X ?groupX ?memJ_norm // natr_Zp.
Qed.
Canonical abelem_mx_linear g := Linear (abelem_mx_linear_proof g).

Let rVabelemJmx v x : x \in G -> rV_E (v *m r x) = (rV_E v) ^ x.
Proof.
move=> Gx; rewrite /= mul_rV_lin1 /= /abelem_mx_fun subgK //.
by rewrite abelem_rV_K // memJ_norm // (subsetP nEG).
Qed.

Fact abelem_mx_repr : mx_repr G r.
Proof.
split=> [|x y Gx Gy]; apply/row_matrixP=> i; apply: rVabelem_inj.
  by rewrite rowE -row1 rVabelemJmx // conjg1.
by rewrite !rowE mulmxA !rVabelemJmx ?groupM // conjgM.
Qed.
Canonical abelem_repr := MxRepresentation abelem_mx_repr.
Let rG := abelem_repr.

Lemma rVabelemJ v x : x \in G -> rV_E (v *m rG x) = (rV_E v) ^ x.
Proof. exact: rVabelemJmx. Qed.

Lemma abelem_rV_J : {in E & G, forall x y, ErV (x ^ y) = ErV x *m rG y}.
Proof.
by move=> x y Ex Gy; rewrite -{1}(abelem_rV_K Ex) -rVabelemJ ?rVabelemK.
Qed.

Lemma abelem_rowgJ m (A : 'M_(m, n)) x :
  x \in G -> rV_E @* rowg (A *m rG x) = (rV_E @* rowg A) :^ x.
Proof.
move=> Gx; apply: (canRL (conjsgKV _)); apply/setP=> y.
rewrite mem_conjgV !morphim_invmE !inE memJ_norm ?(subsetP nEG) //=.
apply: andb_id2l => Ey; rewrite abelem_rV_J //.
by rewrite submxMfree // row_free_unit (repr_mx_unit rG).
Qed.

Lemma rV_abelem_sJ (L : {group gT}) x :
  x \in G -> L \subset E -> ErV @* (L :^ x) = rowg (rowg_mx (ErV @* L) *m rG x).
Proof.
move=> Gx sLE; apply: rVabelem_minj; rewrite abelem_rowgJ //.
by rewrite rowg_mxK !morphim_invm // -(normsP nEG x Gx) conjSg.
Qed.

Lemma rstab_abelem m (A : 'M_(m, n)) : rstab rG A = 'C_G(rV_E @* rowg A).
Proof.
apply/setP=> x; rewrite !inE /=; apply: andb_id2l => Gx.
apply/eqP/centP=> cAx => [_ /morphimP[u _ Au ->]|].
  move: Au; rewrite inE => /submxP[u' ->] {u}.
  by apply/esym/commgP/conjg_fixP; rewrite -rVabelemJ -?mulmxA ?cAx.
apply/row_matrixP=> i; apply: rVabelem_inj.
by rewrite row_mul rVabelemJ // /conjg -cAx ?mulKg ?mem_morphim // inE row_sub.
Qed.

Lemma rstabs_abelem m (A : 'M_(m, n)) : rstabs rG A = 'N_G(rV_E @* rowg A).
Proof.
apply/setP=> x; rewrite !inE /=; apply: andb_id2l => Gx.
by rewrite -rowgS -rVabelemS abelem_rowgJ.
Qed.

Lemma rstabs_abelemG (L : {group gT}) :
  L \subset E -> rstabs rG (rowg_mx (ErV @* L)) = 'N_G(L).
Proof. by move=> sLE; rewrite rstabs_abelem rowg_mxK morphim_invm. Qed.

Lemma mxmodule_abelem m (U : 'M['F_p]_(m, n)) :
  mxmodule rG U = (G \subset 'N(rV_E @* rowg U)).
Proof. by rewrite -subsetIidl -rstabs_abelem. Qed.

Lemma mxmodule_abelemG (L : {group gT}) :
  L \subset E -> mxmodule rG (rowg_mx (ErV @* L)) = (G \subset 'N(L)).
Proof. by move=> sLE; rewrite -subsetIidl -rstabs_abelemG. Qed.

Lemma mxsimple_abelemP (U : 'M['F_p]_n) :
  reflect (mxsimple rG U) (minnormal (rV_E @* rowg U) G).
Proof.
apply: (iffP mingroupP) => [[/andP[ntU modU] minU] | [modU ntU minU]].
  split=> [||V modV sVU ntV]; first by rewrite mxmodule_abelem.
    by apply: contraNneq ntU => ->; rewrite /= rowg0 morphim1.
  rewrite -rowgS -rVabelemS [_ @* rowg V]minU //.
    rewrite -subG1 sub_rVabelem_im morphim1 subG1 trivg_rowg ntV /=.
    by rewrite -mxmodule_abelem.
  by rewrite rVabelemS rowgS.
split=> [|D /andP[ntD nDG sDU]].
  rewrite -subG1 sub_rVabelem_im morphim1 subG1 trivg_rowg ntU /=.
  by rewrite -mxmodule_abelem.
apply/eqP; rewrite eqEsubset sDU sub_rVabelem_im /= -rowg_mxSK rowgK.
have sDE: D \subset E := subset_trans sDU (sub_rVabelem _).
rewrite minU ?mxmodule_abelemG //.
  by rewrite -rowgS rowg_mxK sub_abelem_rV_im.
by rewrite rowg_mx_eq0 (morphim_injm_eq1 abelem_rV_injm).
Qed.

Lemma mxsimple_abelemGP (L : {group gT}) :
  L \subset E -> reflect (mxsimple rG (rowg_mx (ErV @* L))) (minnormal L G).
Proof.
move/abelem_rV_mK=> {2}<-; rewrite -{2}[_ @* L]rowg_mxK.
exact: mxsimple_abelemP.
Qed.

Lemma abelem_mx_irrP : reflect (mx_irreducible rG) (minnormal E G).
Proof.
by rewrite -[E in minnormal E G]im_rVabelem -rowg1; apply: mxsimple_abelemP.
Qed.

Lemma rfix_abelem (H : {set gT}) :
  H \subset G -> (rfix_mx rG H :=: rowg_mx (ErV @* 'C_E(H)%g))%MS.
Proof.
move/subsetP=> sHG; apply/eqmxP/andP; split.
  rewrite -rowgS rowg_mxK -sub_rVabelem_im // subsetI sub_rVabelem /=.
  apply/centsP=> y /morphimP[v _]; rewrite inE => cGv ->{y} x Gx.
  by apply/commgP/conjg_fixP; rewrite /= -rVabelemJ ?sHG ?(rfix_mxP H _).
rewrite genmxE; apply/rfix_mxP=> x Hx; apply/row_matrixP=> i.
rewrite row_mul rowK; case/morphimP: (enum_valP i) => z Ez /setIP[_ cHz] ->.
by rewrite -abelem_rV_J ?sHG // conjgE (centP cHz) ?mulKg.
Qed.

Lemma rker_abelem : rker rG = 'C_G(E).
Proof. by rewrite /rker rstab_abelem rowg1 im_rVabelem. Qed.

Lemma abelem_mx_faithful : 'C_G(E) = 1%g -> mx_faithful rG.
Proof. by rewrite /mx_faithful rker_abelem => ->. Qed.

End OneGroup.

Section SubGroup.

Variables G H : {group gT}.
Hypotheses (nEG : G \subset 'N(E)) (sHG : H \subset G).
Let nEH := subset_trans sHG nEG.
Local Notation rG := (abelem_repr nEG).
Local Notation rHG := (subg_repr rG sHG).
Local Notation rH := (abelem_repr nEH).

Lemma eq_abelem_subg_repr : {in H, rHG =1 rH}.
Proof.
move=> x Hx; apply/row_matrixP=> i; rewrite !rowE !mul_rV_lin1 /=.
by rewrite /abelem_mx_fun !subgK ?(subsetP sHG).
Qed.

Lemma rsim_abelem_subg : mx_rsim rHG rH.
Proof.
exists 1%:M => // [|x Hx]; first by rewrite row_free_unit unitmx1.
by rewrite mul1mx mulmx1 eq_abelem_subg_repr.
Qed.

Lemma mxmodule_abelem_subg m (U : 'M_(m, n)) : mxmodule rHG U = mxmodule rH U.
Proof.
apply: eq_subset_r => x; rewrite !inE; apply: andb_id2l => Hx.
by rewrite eq_abelem_subg_repr.
Qed.

Lemma mxsimple_abelem_subg U : mxsimple rHG U <-> mxsimple rH U.
Proof.
have eq_modH := mxmodule_abelem_subg; rewrite /mxsimple eq_modH.
by split=> [] [-> -> minU]; split=> // V; have:= minU V; rewrite eq_modH.
Qed.

End SubGroup.

End AbelemRepr.

Arguments rVabelem_inj {p%N gT E%G} abelE ntE [v1%R v2%R] : rename.

Section ModularRepresentation.

Variables (F : fieldType) (p : nat) (gT : finGroupType).
Hypothesis charFp : p \in [char F].
Implicit Types G H : {group gT}.

(* This is Gorenstein, Lemma 2.6.3. *)
Lemma rfix_pgroup_char G H n (rG : mx_representation F G n) :
  n > 0 -> p.-group H -> H \subset G -> rfix_mx rG H != 0.
Proof.
move=> n_gt0 pH sHG; rewrite -(rfix_subg rG sHG).
move: {2}_.+1 (ltnSn (n + #|H|)) {rG G sHG}(subg_repr _ _) => m.
elim: m gT H pH => // m IHm gT' G pG in n n_gt0 *; rewrite ltnS => le_nG_m rG.
apply/eqP=> Gregular; have irrG: mx_irreducible rG.
  apply/mx_irrP; split=> // U modU; rewrite -mxrank_eq0 -lt0n => Unz.
  rewrite /row_full eqn_leq rank_leq_col leqNgt; apply/negP=> ltUn.
  have: rfix_mx (submod_repr modU) G != 0.
    by apply: IHm => //; apply: leq_trans le_nG_m; rewrite ltn_add2r.
  by rewrite -mxrank_eq0 (rfix_submod modU) // Gregular capmx0 linear0 mxrank0.
have{m le_nG_m IHm} faithfulG: mx_faithful rG.
  apply/trivgP/eqP/idPn; set C := _ rG => ntC.
  suffices: rfix_mx (kquo_repr rG) (G / _)%g != 0.
    by rewrite -mxrank_eq0 rfix_quo // Gregular mxrank0.
  apply: (IHm _ _ (morphim_pgroup _ _)) => //.
  by apply: leq_trans le_nG_m; rewrite ltn_add2l ltn_quotient // rstab_sub.
have{Gregular} ntG: G :!=: 1%g.
  apply: contraL n_gt0; move/eqP=> G1; rewrite -leqNgt -(mxrank1 F n).
  rewrite -(mxrank0 F n n) -Gregular mxrankS //; apply/rfix_mxP=> x.
  by rewrite {1}G1 mul1mx => /set1P->; rewrite repr_mx1.
have p_pr: prime p by case/andP: charFp.
have{ntG pG} [z]: {z | z \in 'Z(G) & #[z] = p}; last case/setIP=> Gz cGz ozp.
  apply: Cauchy => //; apply: contraR ntG; rewrite -p'natE // => p'Z.
  have pZ: p.-group 'Z(G) by rewrite (pgroupS (center_sub G)).
  by rewrite (trivg_center_pgroup pG (card1_trivg (pnat_1 pZ p'Z))).
have{cGz} cGz1: centgmx rG (rG z - 1%:M).
  apply/centgmxP=> x Gx; rewrite mulmxBl mulmxBr mulmx1 mul1mx.
  by rewrite -!repr_mxM // (centP cGz).
have{irrG faithfulG cGz1} Urz1: rG z - 1%:M \in unitmx.
  apply: (mx_Schur irrG) cGz1 _; rewrite subr_eq0.
  move/implyP: (subsetP faithfulG z).
  by rewrite !inE Gz mul1mx -order_eq1 ozp -implybNN neq_ltn orbC prime_gt1.
do [case: n n_gt0 => // n' _; set n := n'.+1] in rG Urz1 *.
have charMp: p \in [char 'M[F]_n].
  exact: (rmorph_char (scalar_mx_rmorphism _ _)).
have{Urz1}: Frobenius_aut charMp (rG z - 1) \in GRing.unit by rewrite unitrX.
rewrite (Frobenius_autB_comm _ (commr1 _)) Frobenius_aut1.
by rewrite -[_ (rG z)](repr_mxX rG) // -ozp expg_order repr_mx1 subrr unitr0.
Qed.

Variables (G : {group gT}) (n : nat) (rG : mx_representation F G n).

Lemma pcore_sub_rstab_mxsimple M : mxsimple rG M -> 'O_p(G) \subset rstab rG M.
Proof.
case=> modM nzM simM; have sGpG := pcore_sub p G.
rewrite rfix_mx_rstabC //; set U := rfix_mx _ _.
have:= simM (M :&: U)%MS; rewrite sub_capmx submx_refl.
apply; rewrite ?capmxSl //.
  by rewrite capmx_module // normal_rfix_mx_module ?pcore_normal.
rewrite -(in_submodK (capmxSl _ _)) val_submod_eq0 -submx0.
rewrite -(rfix_submod modM) // submx0 rfix_pgroup_char ?pcore_pgroup //.
by rewrite lt0n mxrank_eq0.
Qed.

Lemma pcore_sub_rker_mx_irr : mx_irreducible rG -> 'O_p(G) \subset rker rG.
Proof. exact: pcore_sub_rstab_mxsimple. Qed.

(* This is Gorenstein, Lemma 3.1.3. *)
Lemma pcore_faithful_mx_irr :
  mx_irreducible rG -> mx_faithful rG -> 'O_p(G) = 1%g.
Proof.
move=> irrG ffulG; apply/trivgP; apply: subset_trans ffulG.
exact: pcore_sub_rstab_mxsimple.
Qed.

End ModularRepresentation.

Section Extraspecial.

Variables (F : fieldType) (gT : finGroupType) (S : {group gT}) (p n : nat).
Hypotheses (pS : p.-group S) (esS : extraspecial S).
Hypothesis oSpn : #|S| = (p ^ n.*2.+1)%N.
Hypotheses (splitF : group_splitting_field F S) (F'S : [char F]^'.-group S).

Let p_pr := extraspecial_prime pS esS.
Let p_gt0 := prime_gt0 p_pr.
Let p_gt1 := prime_gt1 p_pr.
Let oZp := card_center_extraspecial pS esS.

Let modIp' (i : 'I_p.-1) : (i.+1 %% p = i.+1)%N.
Proof. by case: i => i; rewrite /= -ltnS prednK //; apply: modn_small. Qed.

(* This is Aschbacher (34.9), parts (1)-(4). *)
Theorem extraspecial_repr_structure (sS : irrType F S) :
  [/\ #|linear_irr sS| = (p ^ n.*2)%N,
      exists iphi : 'I_p.-1 -> sS, let phi i := irr_repr (iphi i) in
        [/\ injective iphi,
            codom iphi =i ~: linear_irr sS,
            forall i, mx_faithful (phi i),
            forall z, z \in 'Z(S)^# ->
              exists2 w, primitive_root_of_unity p w
                       & forall i, phi i z = (w ^+ i.+1)%:M
          & forall i, irr_degree (iphi i) = (p ^ n)%N]
    & #|sS| = (p ^ n.*2 + p.-1)%N].
Proof.
have [[defPhiS defS'] prZ] := esS; set linS := linear_irr sS.
have nb_lin: #|linS| = (p ^ n.*2)%N.
  rewrite card_linear_irr // -divgS ?der_sub //=.
  by rewrite oSpn defS' oZp expnS mulKn.
have nb_irr: #|sS| = (p ^ n.*2 + p.-1)%N.
  pose Zcl := classes S ::&: 'Z(S).
  have cardZcl: #|Zcl| = p.
    transitivity #|[set [set z] | z in 'Z(S)]|; last first.
      by rewrite card_imset //; apply: set1_inj.
    apply: eq_card => zS; apply/setIdP/imsetP=> [[] | [z]].
      case/imsetP=> z Sz ->{zS} szSZ.
      have Zz: z \in 'Z(S) by rewrite (subsetP szSZ) ?class_refl.
      exists z => //; rewrite inE Sz in Zz.
      apply/eqP; rewrite eq_sym eqEcard sub1set class_refl cards1.
      by rewrite -index_cent1 (setIidPl _) ?indexgg // sub_cent1.
    case/setIP=> Sz cSz ->{zS}; rewrite sub1set inE Sz; split=> //.
    apply/imsetP; exists z; rewrite //.
    apply/eqP; rewrite eqEcard sub1set class_refl cards1.
    by rewrite -index_cent1 (setIidPl _) ?indexgg // sub_cent1.
  move/eqP: (class_formula S); rewrite (bigID (mem Zcl)) /=.
  rewrite (eq_bigr (fun _ => 1%N)) => [|zS]; last first.
    case/andP=> _ /setIdP[/imsetP[z Sz ->{zS}] /subsetIP[_ cSzS]].
    rewrite (setIidPl _) ?indexgg // sub_cent1 (subsetP cSzS) //.
    exact: mem_repr (class_refl S z).
  rewrite sum1dep_card setIdE (setIidPr _) 1?cardsE ?cardZcl; last first.
    by apply/subsetP=> zS; rewrite 2!inE => /andP[].
  have pn_gt0: p ^ n.*2 > 0 by rewrite expn_gt0 p_gt0.
  rewrite card_irr // oSpn expnS -(prednK pn_gt0) mulnS eqn_add2l.
  rewrite (eq_bigr (fun _ => p)) => [|xS]; last first.
    case/andP=> SxS; rewrite inE SxS; case/imsetP: SxS => x Sx ->{xS} notZxS.
    have [y Sy ->] := repr_class S x; apply: p_maximal_index => //.
    apply: cent1_extraspecial_maximal => //; first exact: groupJ.
    apply: contra notZxS => Zxy; rewrite -{1}(lcoset_id Sy) class_lcoset.
    rewrite ((_ ^: _ =P [set x ^ y])%g _) ?sub1set // eq_sym eqEcard.
    rewrite sub1set class_refl cards1 -index_cent1 (setIidPl _) ?indexgg //.
    by rewrite sub_cent1; apply: subsetP Zxy; apply: subsetIr.
  rewrite sum_nat_dep_const mulnC eqn_pmul2l //; move/eqP <-.
  rewrite addSnnS prednK // -cardZcl -[card _](cardsID Zcl) /= addnC.
  by congr (_ + _)%N; apply: eq_card => t; rewrite !inE andbC // andbAC andbb.
have fful_nlin i: i \in ~: linS -> mx_faithful (irr_repr i).
  rewrite !inE => nlin_phi.
  apply/trivgP; apply: (TI_center_nil (pgroup_nil pS) (rker_normal _)).
  rewrite setIC; apply: (prime_TIg prZ); rewrite /= -defS' der1_sub_rker //.
  exact: socle_irr.
have [i0 nlin_i0]: exists i0, i0 \in ~: linS.
  by apply/card_gt0P; rewrite cardsCs setCK nb_irr nb_lin addKn -subn1 subn_gt0.
have [z defZ]: exists z, 'Z(S) = <[z]> by apply/cyclicP; rewrite prime_cyclic.
have Zz: z \in 'Z(S) by [rewrite defZ cycle_id]; have [Sz cSz] := setIP Zz.
have ozp: #[z] = p by rewrite -oZp defZ.
have ntz: z != 1%g by rewrite -order_gt1 ozp.
pose phi := irr_repr i0; have irr_phi: mx_irreducible phi := socle_irr i0.
pose w := irr_mode i0 z.
have phi_z: phi z = w%:M by rewrite /phi irr_center_scalar.
have phi_ze e: phi (z ^+ e)%g = (w ^+ e)%:M.
  by rewrite /phi irr_center_scalar ?groupX ?irr_modeX.
have wp1: w ^+ p = 1 by rewrite -irr_modeX // -ozp expg_order irr_mode1.
have injw: {in 'Z(S) &, injective (irr_mode i0)}.
  move=> x y Zx Zy /= eq_xy; have [[Sx _] [Sy _]] := (setIP Zx, setIP Zy).
  apply: mx_faithful_inj (fful_nlin _ nlin_i0) _ _ Sx Sy _.
  by rewrite !{1}irr_center_scalar ?eq_xy; first by split.
have prim_w e: 0 < e < p -> p.-primitive_root (w ^+ e).
  case/andP=> e_gt0 lt_e_p; apply/andP; split=> //.
  apply/eqfunP=> -[d ltdp] /=; rewrite unity_rootE -exprM.
  rewrite -(irr_mode1 i0) -irr_modeX // (inj_in_eq injw) ?groupX ?group1 //.
  rewrite -order_dvdn ozp Euclid_dvdM // gtnNdvd //=.
  move: ltdp; rewrite leq_eqVlt.
  by case: eqP => [-> _ | _ ltd1p]; rewrite (dvdnn, gtnNdvd).
have /cyclicP[a defAutZ]: cyclic (Aut 'Z(S)) by rewrite Aut_prime_cyclic ?ozp.
have phi_unitP (i : 'I_p.-1): (i.+1%:R : 'Z_#[z]) \in GRing.unit.
  by rewrite unitZpE ?order_gt1 // ozp prime_coprime // -lt0n !modIp'.
pose ephi i := invm (injm_Zpm a) (Zp_unitm (FinRing.Unit _ (phi_unitP i))).
pose j : 'Z_#[z] := val (invm (injm_Zp_unitm z) a).
have co_j_p: coprime j p.
  rewrite coprime_sym /j; case: (invm _ a) => /=.
  by rewrite ozp /GRing.unit /= Zp_cast.
have [alpha Aut_alpha alphaZ] := center_aut_extraspecial pS esS co_j_p.
have alpha_i_z i: ((alpha ^+ ephi i) z = z ^+ i.+1)%g.
  transitivity ((a ^+ ephi i) z)%g.
    elim: (ephi i : nat) => // e IHe; rewrite !expgS !permM alphaZ //.
    have Aut_a: a \in Aut 'Z(S) by rewrite defAutZ cycle_id.
    rewrite -{2}[a](invmK (injm_Zp_unitm z)); last by rewrite im_Zp_unitm -defZ.
    rewrite /= autE ?cycle_id // -/j /= /cyclem.
    rewrite -(autmE (groupX _ Aut_a)) -(autmE (groupX _ Aut_alpha)).
    by rewrite !morphX //= !autmE IHe.
  rewrite [(a ^+ _)%g](invmK (injm_Zpm a)) /=; last first.
    by rewrite im_Zpm -defAutZ defZ Aut_aut.
  by rewrite autE ?cycle_id //= val_Zp_nat ozp ?modIp'.
have rphiP i: S :==: autm (groupX (ephi i) Aut_alpha) @* S by rewrite im_autm.
pose rphi i := morphim_repr (eqg_repr phi (rphiP i)) (subxx S).
have rphi_irr i: mx_irreducible (rphi i) by apply/morphim_mx_irr/eqg_mx_irr.
have rphi_fful i: mx_faithful (rphi i).
  rewrite /mx_faithful rker_morphim rker_eqg.
  by rewrite (trivgP (fful_nlin _ nlin_i0)) morphpreIdom; apply: injm_autm.
have rphi_z i: rphi i z = (w ^+ i.+1)%:M.
  by rewrite /rphi [phi]lock /= /morphim_mx autmE alpha_i_z -lock phi_ze.
pose iphi i := irr_comp sS (rphi i); pose phi_ i := irr_repr (iphi i).
have{phi_ze} phi_ze i e: phi_ i (z ^+ e)%g = (w ^+ (e * i.+1)%N)%:M.
  rewrite /phi_ !{1}irr_center_scalar ?groupX ?irr_modeX //.
  suffices ->: irr_mode (iphi i) z = w ^+ i.+1 by rewrite mulnC exprM.
  have:= mx_rsim_sym (rsim_irr_comp sS F'S (rphi_irr i)).
  case/mx_rsim_def=> B [B' _ homB]; rewrite /irr_mode homB // rphi_z.
  rewrite -{1}scalemx1 -scalemxAr -scalemxAl -{1}(repr_mx1 (rphi i)).
  by rewrite -homB // repr_mx1 scalemx1 mxE.
have inj_iphi: injective iphi.
  move=> i1 i2 eqi12; apply/eqP.
  move/eqP: (congr1 (fun i => irr_mode i (z ^+ 1)) eqi12).
  rewrite /irr_mode !{1}[irr_repr _ _]phi_ze !{1}mxE !mul1n.
  by rewrite (eq_prim_root_expr (prim_w 1%N p_gt1)) !modIp'.
have deg_phi i: irr_degree (iphi i) = irr_degree i0.
  by case: (rsim_irr_comp sS F'S (rphi_irr i)).
have im_iphi: codom iphi =i ~: linS.
  apply/subset_cardP; last apply/subsetP=> _ /codomP[i ->].
    by rewrite card_image // card_ord cardsCs setCK nb_irr nb_lin addKn.
  by rewrite !inE /= (deg_phi i) in nlin_i0 *.
split=> //; exists iphi; rewrite -/phi_.
split=> // [i | ze | i].
- have sim_i := rsim_irr_comp sS F'S (rphi_irr i).
  by rewrite -(mx_rsim_faithful sim_i) rphi_fful.
- rewrite {1}defZ 2!inE andbC; case/andP.
  case/cyclePmin=> e; rewrite ozp => lt_e_p ->{ze}.
  case: (posnP e) => [-> | e_gt0 _]; first by rewrite eqxx.
  exists (w ^+ e) => [|i]; first by rewrite prim_w ?e_gt0.
  by rewrite phi_ze exprM.
rewrite deg_phi {i}; set d := irr_degree i0.
apply/eqP; move/eqP: (sum_irr_degree sS F'S splitF).
rewrite (bigID (mem linS)) /= -/irr_degree.
rewrite (eq_bigr (fun _ => 1%N)) => [|i]; last by rewrite !inE; move/eqP->.
rewrite sum1_card nb_lin.
rewrite (eq_bigl (mem (codom iphi))) // => [|i]; last first.
  by rewrite -in_setC -im_iphi.
rewrite (eq_bigr (fun _ => d ^ 2))%N => [|_ /codomP[i ->]]; last first.
  by rewrite deg_phi.
rewrite sum_nat_const card_image // card_ord oSpn (expnS p) -{3}[p]prednK //.
rewrite mulSn eqn_add2l eqn_pmul2l; last by rewrite -ltnS prednK.
by rewrite -muln2 expnM eqn_sqr.
Qed.

(* This is the corolloray of the above that is actually used in the proof of  *)
(* B & G, Theorem 2.5. It encapsulates the dependency on a socle of the       *)
(* regular representation.                                                    *)

Variables (m : nat) (rS : mx_representation F S m) (U : 'M[F]_m).
Hypotheses (simU :  mxsimple rS U) (ffulU : rstab rS U == 1%g).
Let sZS := center_sub S.
Let rZ := subg_repr rS sZS.

Lemma faithful_repr_extraspecial :
 \rank U = (p ^ n)%N /\
   (forall V, mxsimple rS V -> mx_iso rZ U V -> mx_iso rS U V).
Proof.
suffices IH V: mxsimple rS V -> mx_iso rZ U V ->
  [&& \rank U == (p ^ n)%N & mxsimple_iso rS U V].
- split=> [|/= V simV isoUV].
    by case/andP: (IH U simU (mx_iso_refl _ _)) => /eqP.
  by case/andP: (IH V simV isoUV) => _ /(mxsimple_isoP simU).
move=> simV isoUV; wlog sS: / irrType F S by apply: socle_exists.
have [[_ defS'] prZ] := esS.
have{prZ} ntZ: 'Z(S) :!=: 1%g by case: eqP prZ => // ->; rewrite cards1.
have [_ [iphi]] := extraspecial_repr_structure sS.
set phi := fun i => _ => [] [inj_phi im_phi _ phiZ dim_phi] _.
have [modU nzU _]:= simU; pose rU := submod_repr modU.
have nlinU: \rank U != 1%N.
  apply/eqP=> /(rker_linear rU); apply/negP; rewrite /rker rstab_submod.
  by rewrite (eqmx_rstab _ (val_submod1 _)) (eqP ffulU) defS' subG1.
have irrU: mx_irreducible rU by apply/submod_mx_irr.
have rsimU := rsim_irr_comp sS F'S irrU.
set iU := irr_comp sS rU in rsimU; have [_ degU _ _]:= rsimU.
have phiUP: iU \in codom iphi by rewrite im_phi !inE -degU.
rewrite degU -(f_iinv phiUP) dim_phi eqxx /=; apply/(mxsimple_isoP simU).
have [modV _ _]:= simV; pose rV := submod_repr modV.
have irrV: mx_irreducible rV by apply/submod_mx_irr.
have rsimV := rsim_irr_comp sS F'S irrV.
set iV := irr_comp sS rV in rsimV; have [_ degV _ _]:= rsimV.
have phiVP: iV \in codom iphi by rewrite im_phi !inE -degV -(mxrank_iso isoUV).
pose jU := iinv phiUP; pose jV := iinv phiVP.
have [z Zz ntz]:= trivgPn _ ntZ.
have [|w prim_w phi_z] := phiZ z; first by rewrite 2!inE ntz.
suffices eqjUV: jU == jV.
  apply/(mx_rsim_iso modU modV); apply: mx_rsim_trans rsimU _.
  by rewrite -(f_iinv phiUP) -/jU (eqP eqjUV) f_iinv; apply: mx_rsim_sym.
have rsimUV: mx_rsim (subg_repr (phi jU) sZS) (subg_repr (phi jV) sZS).
  have [bU _ bUfree bUhom] := mx_rsim_sym rsimU.
  have [bV _ bVfree bVhom] := rsimV.
  have modUZ := mxmodule_subg sZS modU; have modVZ := mxmodule_subg sZS modV.
  case/(mx_rsim_iso modUZ modVZ): isoUV => [bZ degZ bZfree bZhom].
  rewrite /phi !f_iinv; exists (bU *m bZ *m bV)=> [||x Zx].
  - by rewrite -degU degZ degV.
  - by rewrite /row_free !mxrankMfree.
  have Sx := subsetP sZS x Zx.
  by rewrite 2!mulmxA bUhom // -(mulmxA _ _ bZ) bZhom // -4!mulmxA bVhom.
have{rsimUV} [B [B' _ homB]] := mx_rsim_def rsimUV.
have:= eqxx (irr_mode (iphi jU) z); rewrite /irr_mode; set i0 := Ordinal _.
rewrite {2}[_ z]homB // ![_ z]phi_z mxE mulr1n -scalemx1 -scalemxAr -scalemxAl.
rewrite -(repr_mx1 (subg_repr (phi jV) sZS)) -{B B'}homB // repr_mx1 scalemx1.
by rewrite mxE (eq_prim_root_expr prim_w) !modIp'.
Qed.

End Extraspecial.

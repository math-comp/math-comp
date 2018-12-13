(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrbool ssrfun eqtype ssrnat seq path div choice.
From mathcomp
Require Import fintype tuple finfun bigop prime ssralg poly finset gproduct.
From mathcomp
Require Import fingroup morphism perm automorphism quotient finalg action.
From mathcomp
Require Import zmodp commutator cyclic center pgroup nilpotent sylow abelian.
From mathcomp
Require Import matrix mxalgebra mxpoly mxrepresentation vector ssrnum algC.
From mathcomp
Require Import classfun.

(******************************************************************************)
(* This file contains the basic notions of character theory, based on Isaacs. *)
(*         irr G == tuple of the elements of 'CF(G) that are irreducible      *)
(*                  characters of G.                                          *)
(*        Nirr G == number of irreducible characters of G.                    *)
(*        Iirr G == index type for the irreducible characters of G.           *)
(*               := 'I_(Nirr G).                                              *)
(*        'chi_i == the i-th element of irr G, for i : Iirr G.                *)
(*     'chi[G]_i    Note that 'chi_0 = 1, the principal character of G.       *)
(*        'Chi_i == an irreducible representation that affords 'chi_i.        *)
(* socle_of_Iirr i == the Wedderburn component of the regular representation  *)
(*                    of G, corresponding to 'Chi_i.                          *)
(*   Iirr_of_socle == the inverse of socle_of_Iirr (which is one-to-one).     *)
(*    phi.[A]%CF == the image of A \in group_ring G under phi : 'CF(G).       *)
(*     cfRepr rG == the character afforded by the representation rG of G.     *)
(*       cfReg G == the regular character, afforded by the regular            *)
(*                  representation of G.                                      *)
(*     detRepr rG == the linear character afforded by the determinant of rG.  *)
(*      cfDet phi == the linear character afforded by the determinant of a    *)
(*                   representation affording phi.                            *)
(*        'o(phi) == the "determinential order" of phi (the multiplicative    *)
(*                   order of cfDet phi.                                      *)
(* phi \is a character <=> phi : 'CF(G) is a character of G or 0.             *)
(* i \in irr_constt phi <=> 'chi_i is an irreducible constituent of phi: phi  *)
(*                  has a non-zero coordinate on 'chi_i over the basis irr G. *)
(* xi \is a linear_char xi <=> xi : 'CF(G) is a linear character of G.        *)
(*    'Z(chi)%CF == the center of chi when chi is a character of G, i.e.,     *)
(*                  rcenter rG where rG is a representation that affords phi. *)
(*                  If phi is not a character then 'Z(chi)%CF = cfker phi.    *)
(*  aut_Iirr u i == the index of cfAut u 'chi_i in irr G.                     *)
(*  conjC_Iirr i == the index of 'chi_i^*%CF in irr G.                        *)
(*  morph_Iirr i == the index of cfMorph 'chi[f @* G]_i in irr G.             *)
(* isom_Iirr isoG i == the index of cfIsom isoG 'chi[G]_i in irr R.           *)
(*    mod_Iirr i == the index of ('chi[G / H]_i %% H)%CF in irr G.            *)
(*    quo_Iirr i == the index of ('chi[G]_i / H)%CF in irr (G / H).           *)
(*  Ind_Iirr G i == the index of 'Ind[G, H] 'chi_i, provided it is an         *)
(*                  irreducible character (such as when if H is the inertia   *)
(*                  group of 'chi_i).                                         *)
(*  Res_Iirr H i == the index of 'Res[H, G] 'chi_i, provided it is an         *)
(*                  irreducible character (such as when 'chi_i is linear).    *)
(* sdprod_Iirr defG i == the index of cfSdprod defG 'chi_i in irr G, given    *)
(*                       defG : K ><| H = G.                                  *)
(* And, for KxK : K \x H = G.                                                 *)
(*      dprodl_Iirr KxH i == the index of cfDprodl KxH 'chi[K]_i in irr G.    *)
(*      dprodr_Iirr KxH j == the index of cfDprodr KxH 'chi[H]_j in irr G.    *)
(*  dprod_Iirr KxH (i, j) == the index of cfDprod KxH 'chi[K]_i 'chi[H]_j.    *)
(*     inv_dprod_Iirr KxH == the inverse of dprod_Iirr KxH.                   *)
(* The following are used to define and exploit the character table:          *)
(*  character_table G == the character table of G, whose i-th row lists the   *)
(*                       values taken by 'chi_i on the conjugacy classes      *)
(*                       of G; this is a square Nirr G x NirrG matrix.        *)
(*        irr_class i == the conjugacy class of G with index i : Iirr G.      *)
(*      class_Iirr xG == the index of xG \in classes G, in Iirr G.            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Local Notation algCF := [fieldType of algC].

Section AlgC.

Variable (gT : finGroupType).

Lemma groupC : group_closure_field algCF gT.
Proof. exact: group_closure_closed_field. Qed.

End AlgC.

Section Tensor.

Variable (F : fieldType).

Fixpoint trow  (n1 : nat) : 
  forall (A : 'rV[F]_n1) m2 n2 (B : 'M[F]_(m2,n2)), 'M[F]_(m2,n1 * n2) :=
  if n1 is n'1.+1 
  then
    fun (A : 'M[F]_(1,(1 + n'1))) m2 n2 (B : 'M[F]_(m2,n2)) =>
       (row_mx (lsubmx A 0 0 *: B) (trow (rsubmx A) B))
   else (fun _ _ _ _ => 0).

Lemma trow0 n1 m2 n2 B : @trow n1 0 m2 n2 B = 0.
Proof.
elim: n1=> //= n1 IH.
rewrite !mxE scale0r linear0.
rewrite IH //; apply/matrixP=> i j; rewrite !mxE.
by case: split=> *; rewrite mxE.
Qed.

Definition trowb n1 m2 n2 B A :=  @trow n1 A m2 n2 B.

Lemma trowbE n1 m2 n2 A B : trowb B A = @trow n1 A m2 n2 B.
Proof. by []. Qed.

Lemma trowb_is_linear n1 m2 n2 (B : 'M_(m2,n2)) : linear (@trowb n1 m2 n2 B).
Proof.
elim: n1=> [|n1 IH] //= k A1 A2 /=; first by rewrite scaler0 add0r.
rewrite linearD /= linearZ.
apply/matrixP=> i j.
rewrite !mxE.
case: split=> a.
  by rewrite !mxE mulrDl mulrA.
by rewrite linearD /= linearZ IH !mxE.
Qed.

Canonical Structure trowb_linear n1 m2 n2 B := 
  Linear (@trowb_is_linear n1 m2 n2 B).
  
Lemma trow_is_linear n1 m2 n2 (A : 'rV_n1) : linear (@trow n1 A m2 n2).
Proof.
elim: n1 A => [|n1 IH] //= A k A1 A2 /=; first by rewrite scaler0 add0r.
rewrite linearD /= linearZ /=.
apply/matrixP=> i j; rewrite !mxE.
by case: split=> a; rewrite ?IH !mxE.
Qed.

Canonical Structure trow_linear n1 m2 n2 A := 
  Linear (@trow_is_linear n1 m2 n2 A).

Fixpoint tprod  (m1 : nat) : 
  forall n1 (A : 'M[F]_(m1,n1)) m2 n2 (B : 'M[F]_(m2,n2)),
        'M[F]_(m1 * m2,n1 * n2) :=
  if m1 is m'1.+1 
    return forall n1 (A : 'M[F]_(m1,n1)) m2 n2 (B : 'M[F]_(m2,n2)),
           'M[F]_(m1 * m2,n1 * n2)
  then
    fun n1 (A : 'M[F]_(1 + m'1,n1)) m2 n2 B =>
        (col_mx (trow (usubmx A) B) (tprod (dsubmx A) B))
   else (fun _ _ _ _ _ => 0).

Lemma dsumx_mul m1 m2 n p A B :
  dsubmx ((A *m B) : 'M[F]_(m1 + m2, n)) = dsubmx (A : 'M_(m1 + m2, p)) *m B.
Proof.
apply/matrixP=> i j; rewrite !mxE; apply: eq_bigr=> k _.
by rewrite !mxE.
Qed.

Lemma usumx_mul m1 m2 n p A B :
  usubmx ((A *m B) : 'M[F]_(m1 + m2, n)) = usubmx (A : 'M_(m1 + m2, p)) *m B.
Proof.
by apply/matrixP=> i j; rewrite !mxE; apply: eq_bigr=> k _; rewrite !mxE.
Qed.

Let trow_mul (m1 m2 n2 p2 : nat) 
         (A : 'rV_m1) (B1: 'M[F]_(m2,n2)) (B2 :'M[F]_(n2,p2)) : 
  trow A (B1 *m B2) = B1 *m trow A B2.
Proof.
elim: m1 A => [|m1 IH] A /=; first by rewrite mulmx0.
by rewrite IH mul_mx_row -scalemxAr.
Qed.

Lemma tprodE m1 n1 p1 (A1 :'M[F]_(m1,n1)) (A2 :'M[F]_(n1,p1))
             m2 n2 p2 (B1 :'M[F]_(m2,n2)) (B2 :'M[F]_(n2,p2)) :
  tprod (A1 *m A2) (B1 *m B2) = (tprod A1 B1) *m (tprod A2 B2).
Proof.
elim: m1 n1 p1 A1 A2 m2 n2 p2 B1 B2 => /= [|m1 IH].
  by move=> *; rewrite mul0mx.
move=> n1 p1 A1 A2 m2 n2 p2 B1 B2.
rewrite mul_col_mx -IH.
congr col_mx; last by rewrite dsumx_mul.
rewrite usumx_mul.
elim: n1 {A1}(usubmx (A1: 'M_(1 + m1, n1))) p1 A2=> //= [u p1 A2|].
  by rewrite [A2](flatmx0) !mulmx0 -trowbE linear0.
move=> n1 IH1 A p1 A2 //=.
set Al := lsubmx _; set Ar := rsubmx _.
set Su := usubmx _; set Sd := dsubmx _.
rewrite mul_row_col -IH1.
rewrite -{1}(@hsubmxK F 1 1 n1 A).
rewrite -{1}(@vsubmxK F 1 n1 p1 A2).
rewrite (@mul_row_col F 1 1 n1 p1).
rewrite -trowbE linearD /= trowbE -/Al.
congr (_ + _).
rewrite {1}[Al]mx11_scalar mul_scalar_mx.
by rewrite -trowbE linearZ /= trowbE -/Su trow_mul scalemxAl.
Qed.

Let tprod_tr m1 n1 (A :'M[F]_(m1, 1 + n1)) m2 n2 (B :'M[F]_(m2, n2)) :
  tprod A B =  row_mx (trow (lsubmx A)^T B^T)^T (tprod (rsubmx A) B).
Proof.
elim: m1 n1 A m2 n2 B=> [|m1 IH] n1 A m2 n2 B //=.
  by rewrite trmx0 row_mx0.
rewrite !IH.
pose A1 := A :  'M_(1 + m1, 1 + n1).
have F1: dsubmx (rsubmx A1) = rsubmx (dsubmx A1).
  by apply/matrixP=> i j; rewrite !mxE.
have F2: rsubmx (usubmx A1) = usubmx (rsubmx A1).
  by apply/matrixP=> i j; rewrite !mxE.
have F3: lsubmx (dsubmx A1) = dsubmx (lsubmx A1).
  by apply/matrixP=> i j; rewrite !mxE.
rewrite tr_row_mx -block_mxEv -block_mxEh !(F1,F2,F3); congr block_mx.
- by rewrite !mxE linearZ /= trmxK.
by rewrite -trmx_dsub.
Qed.

Lemma tprod1 m n : tprod (1%:M : 'M[F]_(m,m)) (1%:M : 'M[F]_(n,n)) = 1%:M.
Proof.
elim: m n => [|m IH] n //=; first by rewrite [1%:M]flatmx0.
rewrite tprod_tr.
set u := rsubmx _; have->: u = 0.
  apply/matrixP=> i j; rewrite !mxE.
  by case: i; case: j=> /= j Hj; case.
set v := lsubmx (dsubmx _); have->: v = 0.
  apply/matrixP=> i j; rewrite !mxE.
  by case: i; case: j; case.
set w := rsubmx _; have->: w = 1%:M.
  apply/matrixP=> i j; rewrite !mxE.
  by case: i; case: j; case.
rewrite IH -!trowbE !linear0.
rewrite -block_mxEv.
set z := (lsubmx _) 0 0; have->: z = 1.
  by rewrite /z !mxE eqxx.
by rewrite scale1r scalar_mx_block.
Qed.

Lemma mxtrace_prod m n (A :'M[F]_(m)) (B :'M[F]_(n)) :
  \tr (tprod A B) =  \tr A * \tr B.
Proof.
elim: m n A B => [|m IH] n A B //=.
  by rewrite [A]flatmx0 mxtrace0 mul0r.
rewrite tprod_tr -block_mxEv mxtrace_block IH.
rewrite linearZ /= -mulrDl; congr (_ * _).
rewrite -trace_mx11 .
pose A1 := A : 'M_(1 + m).
rewrite -{3}[A](@submxK _ 1 m 1 m A1).
by rewrite (@mxtrace_block _ _ _ (ulsubmx A1)).
Qed.

End Tensor.

(* Representation sigma type and standard representations. *)
Section StandardRepresentation.

Variables (R : fieldType) (gT : finGroupType) (G : {group gT}).
Local Notation reprG := (mx_representation R G).

Record representation :=
  Representation {rdegree; mx_repr_of_repr :> reprG rdegree}.

Lemma mx_repr0 : mx_repr G (fun _ : gT => 1%:M : 'M[R]_0).
Proof. by split=> // g h Hg Hx; rewrite mulmx1. Qed.

Definition grepr0 := Representation (MxRepresentation mx_repr0).

Lemma add_mx_repr (rG1 rG2 : representation) : 
  mx_repr G (fun g => block_mx (rG1 g) 0 0 (rG2 g)).
Proof.
split=> [|x y Hx Hy]; first by rewrite !repr_mx1 -scalar_mx_block.
by rewrite mulmx_block !(mulmx0, mul0mx, addr0, add0r, repr_mxM).
Qed.

Definition dadd_grepr rG1 rG2 :=
  Representation (MxRepresentation (add_mx_repr rG1 rG2)).

Section DsumRepr.

Variables (n : nat) (rG : reprG n).

Lemma mx_rsim_dadd  (U V W : 'M_n) (rU rV : representation)
    (modU : mxmodule rG U) (modV : mxmodule rG V) (modW : mxmodule rG W) :
    (U + V :=: W)%MS -> mxdirect (U + V) ->
    mx_rsim (submod_repr modU) rU -> mx_rsim (submod_repr modV) rV ->
  mx_rsim (submod_repr modW) (dadd_grepr rU rV).
Proof.
case: rU; case: rV=> nV rV nU rU defW dxUV /=.
have tiUV := mxdirect_addsP dxUV.
move=> [fU def_nU]; rewrite -{nU}def_nU in rU fU * => inv_fU hom_fU.
move=> [fV def_nV]; rewrite -{nV}def_nV in rV fV * => inv_fV hom_fV.
pose pU := in_submod U (proj_mx U V) *m fU.
pose pV := in_submod V (proj_mx V U) *m fV.
exists (val_submod 1%:M *m row_mx pU pV) => [||g Gg].
- by rewrite -defW (mxdirectP dxUV).
- apply/row_freeP.
  pose pU' := invmx fU *m val_submod 1%:M.
  pose pV' := invmx fV *m val_submod 1%:M.
  exists (in_submod _ (col_mx pU' pV')).
  rewrite in_submodE mulmxA -in_submodE -mulmxA mul_row_col mulmxDr.
  rewrite -[pU *m _]mulmxA -[pV *m _]mulmxA !mulKVmx -?row_free_unit //.
  rewrite addrC (in_submodE V) 2![val_submod 1%:M *m _]mulmxA -in_submodE.
  rewrite addrC (in_submodE U) 2![val_submod 1%:M *m _]mulmxA -in_submodE.
  rewrite -!val_submodE !in_submodK ?proj_mx_sub //.
  by rewrite add_proj_mx ?val_submodK // val_submod1 defW.
rewrite mulmxA -val_submodE -[submod_repr _ g]mul1mx val_submodJ //.
rewrite -(mulmxA _ (rG g)) mul_mx_row -mulmxA mul_row_block !mulmx0 addr0 add0r.
rewrite !mul_mx_row; set W' := val_submod 1%:M; congr (row_mx _ _).
  rewrite 3!mulmxA in_submodE mulmxA.
  have hom_pU: (W' <= dom_hom_mx rG (proj_mx U V))%MS.
    by rewrite val_submod1 -defW proj_mx_hom.
  rewrite (hom_mxP hom_pU) // -in_submodE (in_submodJ modU) ?proj_mx_sub //.
  rewrite -(mulmxA _ _ fU) hom_fU // in_submodE -2!(mulmxA W') -in_submodE.
  by rewrite -mulmxA (mulmxA _ fU).
rewrite 3!mulmxA in_submodE mulmxA.
have hom_pV: (W' <= dom_hom_mx rG (proj_mx V U))%MS.
  by rewrite val_submod1 -defW addsmxC proj_mx_hom // capmxC.
rewrite (hom_mxP hom_pV) // -in_submodE (in_submodJ modV) ?proj_mx_sub //.
rewrite -(mulmxA _ _ fV) hom_fV // in_submodE -2!(mulmxA W') -in_submodE.
by rewrite -mulmxA (mulmxA _ fV).
Qed.

Lemma mx_rsim_dsum (I : finType) (P : pred I) U rU (W : 'M_n)
    (modU : forall i, mxmodule rG (U i)) (modW : mxmodule rG W) : 
    let S := (\sum_(i | P i) U i)%MS in (S :=: W)%MS -> mxdirect S -> 
    (forall i, mx_rsim (submod_repr (modU i)) (rU i : representation)) ->
  mx_rsim (submod_repr modW) (\big[dadd_grepr/grepr0]_(i | P i) rU i).
Proof.
move=> /= defW dxW rsimU.
rewrite mxdirectE /= -!(big_filter _ P) in dxW defW *.
elim: {P}(filter P _) => [|i e IHe] in W modW dxW defW *.
  rewrite !big_nil /= in defW *.
  by exists 0 => [||? _]; rewrite ?mul0mx ?mulmx0 // /row_free -defW !mxrank0.
rewrite !big_cons /= in dxW defW *.
rewrite 2!(big_nth i) !big_mkord /= in IHe dxW defW.
set Wi := (\sum_i _)%MS in defW dxW IHe.
rewrite -mxdirectE mxdirect_addsE !mxdirectE eqxx /= -/Wi in dxW.
have modWi: mxmodule rG Wi by apply: sumsmx_module.
case/andP: dxW; move/(IHe Wi modWi) {IHe}; move/(_ (eqmx_refl _))=> rsimWi.
by move/eqP; move/mxdirect_addsP=> dxUiWi; apply: mx_rsim_dadd (rsimU i) rsimWi.
Qed.

Definition muln_grepr rW k := \big[dadd_grepr/grepr0]_(i < k) rW.

Lemma mx_rsim_socle (sG : socleType rG) (W : sG) (rW : representation) :
    let modW : mxmodule rG W := component_mx_module rG (socle_base W) in
    mx_rsim (socle_repr W) rW ->
  mx_rsim (submod_repr modW) (muln_grepr rW (socle_mult W)).
Proof.
set M := socle_base W => modW rsimM.
have simM: mxsimple rG M := socle_simple W.
have rankM_gt0: (\rank M > 0)%N by rewrite lt0n mxrank_eq0; case: simM.
have [I /= U_I simU]: mxsemisimple rG W by apply: component_mx_semisimple.
pose U (i : 'I_#|I|) := U_I (enum_val i).
have reindexI := reindex _ (onW_bij I (enum_val_bij I)).
rewrite mxdirectE /= !reindexI -mxdirectE /= => defW dxW.
have isoU: forall i, mx_iso rG M (U i).
  move=> i; have sUiW: (U i <= W)%MS  by rewrite -defW (sumsmx_sup i).
  exact: component_mx_iso (simU _) sUiW.
have ->: socle_mult W = #|I|.
  rewrite -(mulnK #|I| rankM_gt0); congr (_ %/ _)%N.
  rewrite -defW (mxdirectP dxW) /= -sum_nat_const reindexI /=.
  by apply: eq_bigr => i _; rewrite -(mxrank_iso (isoU i)).
have modU: mxmodule rG (U _) := mxsimple_module (simU _).
suff: mx_rsim (submod_repr (modU _)) rW by apply: mx_rsim_dsum defW dxW.
by move=> i; apply: mx_rsim_trans (mx_rsim_sym _) rsimM; apply/mx_rsim_iso.
Qed.

End DsumRepr.

Section ProdRepr.

Variables (n1 n2 : nat) (rG1 : reprG n1) (rG2 : reprG n2).

Lemma prod_mx_repr : mx_repr G (fun g => tprod (rG1 g) (rG2 g)).
Proof.
split=>[|i j InG JnG]; first by rewrite !repr_mx1 tprod1.
by rewrite !repr_mxM // tprodE.
Qed.

Definition prod_repr := MxRepresentation prod_mx_repr.

End ProdRepr.

Lemma prod_repr_lin n2 (rG1 : reprG 1) (rG2 : reprG n2) :
  {in G, forall x, let cast_n2 := esym (mul1n n2) in
      prod_repr rG1 rG2 x = castmx (cast_n2, cast_n2) (rG1 x 0 0 *: rG2 x)}.
Proof.
move=> x Gx /=; set cast_n2 := esym _; rewrite /prod_repr /= !mxE !lshift0.
apply/matrixP=> i j; rewrite castmxE /=.
do 2![rewrite mxE; case: splitP => [? ? | []//]].
by congr ((_ *: rG2 x) _ _); apply: val_inj.
Qed.

End StandardRepresentation.

Arguments grepr0 {R gT G}.
Prenex Implicits dadd_grepr.

Section Char.

Variables (gT : finGroupType) (G : {group gT}).

Fact cfRepr_subproof n (rG : mx_representation algCF G n) :
  is_class_fun <<G>> [ffun x => \tr (rG x) *+ (x \in G)].
Proof.
rewrite genGid; apply: intro_class_fun => [x y Gx Gy | _ /negbTE-> //].
by rewrite groupJr // !repr_mxM ?groupM ?groupV // mxtrace_mulC repr_mxK.
Qed.
Definition cfRepr n rG := Cfun 0 (@cfRepr_subproof n rG).

Lemma cfRepr1 n rG : @cfRepr n rG 1%g = n%:R.
Proof. by rewrite cfunE group1 repr_mx1 mxtrace1. Qed.

Lemma cfRepr_sim n1 n2 rG1 rG2 :
  mx_rsim rG1 rG2 -> @cfRepr n1 rG1 = @cfRepr n2 rG2.
Proof.
case/mx_rsim_def=> f12 [f21] fK def_rG1; apply/cfun_inP=> x Gx.
by rewrite !cfunE def_rG1 // mxtrace_mulC mulmxA fK mul1mx.
Qed.

Lemma cfRepr0 : cfRepr grepr0 = 0.
Proof. by apply/cfun_inP=> x Gx; rewrite !cfunE Gx mxtrace1. Qed.

Lemma cfRepr_dadd rG1 rG2 :
  cfRepr (dadd_grepr rG1 rG2) = cfRepr rG1 + cfRepr rG2.
Proof. by apply/cfun_inP=> x Gx; rewrite !cfunE Gx mxtrace_block. Qed.

Lemma cfRepr_dsum I r (P : pred I) rG :
  cfRepr (\big[dadd_grepr/grepr0]_(i <- r | P i) rG i)
    = \sum_(i <- r | P i) cfRepr (rG i).
Proof. exact: (big_morph _ cfRepr_dadd cfRepr0). Qed.

Lemma cfRepr_muln rG k : cfRepr (muln_grepr rG k) = cfRepr rG *+ k.
Proof. by rewrite cfRepr_dsum /= sumr_const card_ord. Qed.

Section StandardRepr.

Variables (n : nat) (rG : mx_representation algCF G n).
Let sG := DecSocleType rG.
Let iG : irrType algCF G := DecSocleType _.

Definition standard_irr (W : sG) := irr_comp iG (socle_repr W).

Definition standard_socle i := pick [pred W | standard_irr W == i].
Local Notation soc := standard_socle.

Definition standard_irr_coef i := oapp (fun W => socle_mult W) 0%N (soc i).

Definition standard_grepr :=
  \big[dadd_grepr/grepr0]_i
     muln_grepr (Representation (socle_repr i)) (standard_irr_coef i).

Lemma mx_rsim_standard : mx_rsim rG standard_grepr.
Proof.
pose W i := oapp val 0 (soc i); pose S := (\sum_i W i)%MS.
have C'G: [char algC]^'.-group G := algC'G G.
have [defS dxS]: (S :=: 1%:M)%MS /\ mxdirect S.
  rewrite /S mxdirectE /= !(bigID soc xpredT) /=.
  rewrite addsmxC big1 => [|i]; last by rewrite /W; case (soc i).
  rewrite adds0mx_id addnC (@big1 nat) ?add0n => [|i]; last first.
    by rewrite /W; case: (soc i); rewrite ?mxrank0.
  have <-: Socle sG = 1%:M := reducible_Socle1 sG (mx_Maschke rG C'G).
  have [W0 _ | noW] := pickP sG; last first.
    suff no_i: (soc : pred iG) =1 xpred0 by rewrite /Socle !big_pred0 ?mxrank0.
    by move=> i; rewrite /soc; case: pickP => // W0; have:= noW W0.
  have irrK Wi: soc (standard_irr Wi) = Some Wi.
    rewrite /soc; case: pickP => [W' | /(_ Wi)] /= /eqP // eqWi.
    apply/eqP/socle_rsimP.
    apply: mx_rsim_trans (rsim_irr_comp iG C'G (socle_irr _)) (mx_rsim_sym _).
    by rewrite [irr_comp _ _]eqWi; apply: rsim_irr_comp (socle_irr _).
  have bij_irr: {on [pred i | soc i], bijective standard_irr}.
    exists (odflt W0 \o soc) => [Wi _ | i]; first by rewrite /= irrK.
    by rewrite inE /soc /=; case: pickP => //= Wi; move/eqP.
  rewrite !(reindex standard_irr) {bij_irr}//=.
  have all_soc Wi: soc (standard_irr Wi) by rewrite irrK.
  rewrite (eq_bigr val) => [|Wi _]; last by rewrite /W irrK.
  rewrite !(eq_bigl _ _ all_soc); split=> //.
  rewrite (eq_bigr (mxrank \o val)) => [|Wi _]; last by rewrite /W irrK.
  by rewrite -mxdirectE /= Socle_direct.
pose modW i : mxmodule rG (W i) :=
  if soc i is Some Wi as oWi return mxmodule rG (oapp val 0 oWi) then
    component_mx_module rG (socle_base Wi)
  else mxmodule0 rG n.
apply: mx_rsim_trans (mx_rsim_sym (rsim_submod1 (mxmodule1 rG) _)) _ => //.
apply: mx_rsim_dsum (modW) _ defS dxS _ => i.
rewrite /W /standard_irr_coef /modW /soc; case: pickP => [Wi|_] /=; last first.
  rewrite /muln_grepr big_ord0.
  by exists 0 => [||x _]; rewrite ?mxrank0 ?mulmx0 ?mul0mx.
by move/eqP=> <-; apply: mx_rsim_socle; apply: rsim_irr_comp (socle_irr Wi).
Qed.

End StandardRepr.

Definition cfReg (B : {set gT}) : 'CF(B) := #|B|%:R *: '1_[1].

Lemma cfRegE x : @cfReg G x = #|G|%:R *+ (x == 1%g).
Proof. by rewrite cfunE cfuniE ?normal1 // inE mulr_natr. Qed.

(* This is Isaacs, Lemma (2.10). *)
Lemma cfReprReg : cfRepr (regular_repr algCF G) = cfReg G.
Proof.
apply/cfun_inP=> x Gx; rewrite cfRegE.
have [-> | ntx] := altP (x =P 1%g); first by rewrite cfRepr1.
rewrite cfunE Gx [\tr _]big1 // => i _; rewrite 2!mxE /=.
rewrite -(inj_eq enum_val_inj) gring_indexK ?groupM ?enum_valP //.
by rewrite eq_mulVg1 mulKg (negbTE ntx).
Qed.

Definition xcfun (chi : 'CF(G)) A :=
  (gring_row A *m (\col_(i < #|G|) chi (enum_val i))) 0 0.

Lemma xcfun_is_additive phi : additive (xcfun phi).
Proof. by move=> A B; rewrite /xcfun linearB mulmxBl !mxE. Qed.
Canonical xcfun_additive phi := Additive (xcfun_is_additive phi).

Lemma xcfunZr a phi A : xcfun phi (a *: A) = a * xcfun phi A.
Proof. by rewrite /xcfun linearZ -scalemxAl mxE. Qed.

(* In order to add a second canonical structure on xcfun *)
Definition xcfun_r_head k A phi := let: tt := k in xcfun phi A.
Local Notation xcfun_r A := (xcfun_r_head tt A).

Lemma xcfun_rE A chi : xcfun_r A chi = xcfun chi A. Proof. by []. Qed.

Fact xcfun_r_is_additive A : additive (xcfun_r A).
Proof.
move=> phi psi; rewrite /= /xcfun !mxE -sumrB; apply: eq_bigr => i _.
by rewrite !mxE !cfunE mulrBr.
Qed.
Canonical xcfun_r_additive A := Additive (xcfun_r_is_additive A).

Lemma xcfunZl a phi A : xcfun (a *: phi) A = a * xcfun phi A.
Proof.
rewrite /xcfun !mxE big_distrr; apply: eq_bigr => i _ /=.
by rewrite !mxE cfunE mulrCA.
Qed.

Lemma xcfun_repr n rG A : xcfun (@cfRepr n rG) A = \tr (gring_op rG A).
Proof.
rewrite gring_opE [gring_row A]row_sum_delta !linear_sum /xcfun !mxE.
apply: eq_bigr => i _; rewrite !mxE /= !linearZ cfunE enum_valP /=.
by congr (_ * \tr _) => {A} /=; rewrite /gring_mx /= -rowE rowK mxvecK.
Qed.

End Char.
Notation xcfun_r A := (xcfun_r_head tt A).
Notation "phi .[ A ]" := (xcfun phi A) : cfun_scope.

Definition pred_Nirr gT B := #|@classes gT B|.-1.
Arguments pred_Nirr {gT} B%g.
Notation Nirr G := (pred_Nirr G).+1.
Notation Iirr G := 'I_(Nirr G).

Section IrrClassDef.

Variables (gT : finGroupType) (G : {group gT}).

Let sG := DecSocleType (regular_repr algCF G).

Lemma NirrE : Nirr G = #|classes G|.
Proof. by rewrite /pred_Nirr (cardD1 [1]) classes1. Qed.

Fact Iirr_cast : Nirr G = #|sG|.
Proof. by rewrite NirrE ?card_irr ?algC'G //; apply: groupC. Qed.

Let offset := cast_ord (esym Iirr_cast) (enum_rank [1 sG]%irr).

Definition socle_of_Iirr (i : Iirr G) : sG :=
  enum_val (cast_ord Iirr_cast (i + offset)).
Definition irr_of_socle (Wi : sG) : Iirr G :=
  cast_ord (esym Iirr_cast) (enum_rank Wi) - offset.
Local Notation W := socle_of_Iirr.

Lemma socle_Iirr0 : W 0 = [1 sG]%irr.
Proof. by rewrite /W add0r cast_ordKV enum_rankK. Qed.

Lemma socle_of_IirrK : cancel W irr_of_socle.
Proof. by move=> i; rewrite /irr_of_socle enum_valK cast_ordK addrK. Qed.

Lemma irr_of_socleK : cancel irr_of_socle W.
Proof. by move=> Wi; rewrite /W subrK cast_ordKV enum_rankK. Qed.
Hint Resolve socle_of_IirrK irr_of_socleK : core.

Lemma irr_of_socle_bij (A : pred (Iirr G)) : {on A, bijective irr_of_socle}.
Proof. by apply: onW_bij; exists W. Qed.

Lemma socle_of_Iirr_bij (A : pred sG) : {on A, bijective W}.
Proof. by apply: onW_bij; exists irr_of_socle. Qed.

End IrrClassDef.

Prenex Implicits socle_of_IirrK irr_of_socleK.
Arguments socle_of_Iirr {gT G%G} i%R.

Notation "''Chi_' i" := (irr_repr (socle_of_Iirr i))
  (at level 8, i at level 2, format "''Chi_' i").

Fact irr_key : unit. Proof. by []. Qed.
Definition irr_def gT B : (Nirr B).-tuple 'CF(B) :=
   let irr_of i := 'Res[B, <<B>>] (@cfRepr gT _ _ 'Chi_(inord i)) in
   [tuple of mkseq irr_of (Nirr B)].
Definition irr := locked_with irr_key irr_def.

Arguments irr {gT} B%g.

Notation "''chi_' i" :=  (tnth (irr _) i%R)
  (at level 8, i at level 2, format "''chi_' i") : ring_scope.
Notation "''chi[' G ]_ i" := (tnth (irr G) i%R)
  (at level 8, i at level 2, only parsing) : ring_scope.

Section IrrClass.

Variable (gT : finGroupType) (G : {group gT}).
Implicit Types (i : Iirr G) (B : {set gT}).
Open Scope group_ring_scope.

Lemma congr_irr i1 i2 : i1 = i2 -> 'chi_i1 = 'chi_i2. Proof. by move->. Qed.

Lemma Iirr1_neq0 : G :!=: 1%g -> inord 1 != 0 :> Iirr G.
Proof. by rewrite -classes_gt1 -NirrE -val_eqE /= => /inordK->. Qed.

Lemma has_nonprincipal_irr : G :!=: 1%g -> {i : Iirr G | i != 0}.
Proof. by move/Iirr1_neq0; exists (inord 1). Qed.

Lemma irrRepr i : cfRepr 'Chi_i = 'chi_i.
Proof.
rewrite [@irr]unlock (tnth_nth 0) nth_mkseq // -[<<G>>]/(gval _) genGidG.
by rewrite cfRes_id inord_val.
Qed.

Lemma irr0 : 'chi[G]_0 = 1.
Proof.
apply/cfun_inP=> x Gx; rewrite -irrRepr cfun1E cfunE Gx.
by rewrite socle_Iirr0 irr1_repr // mxtrace1 degree_irr1.
Qed.

Lemma cfun1_irr : 1 \in irr G.
Proof. by rewrite -irr0 mem_tnth. Qed.

Lemma mem_irr i : 'chi_i \in irr G.
Proof. exact: mem_tnth. Qed.

Lemma irrP xi : reflect (exists i, xi = 'chi_i) (xi \in irr G).
Proof.
apply: (iffP idP) => [/(nthP 0)[i] | [i ->]]; last exact: mem_irr.
rewrite size_tuple => lt_i_G <-.
by exists (Ordinal lt_i_G); rewrite (tnth_nth 0).
Qed.

Let sG := DecSocleType (regular_repr algCF G).
Let C'G := algC'G G.
Let closG := @groupC _ G.
Local Notation W i := (@socle_of_Iirr _ G i).
Local Notation "''n_' i" := 'n_(W i).
Local Notation "''R_' i" := 'R_(W i).
Local Notation "''e_' i" := 'e_(W i).

Lemma irr1_degree i : 'chi_i 1%g = ('n_i)%:R.
Proof. by rewrite -irrRepr cfRepr1. Qed.

Lemma Cnat_irr1 i : 'chi_i 1%g \in Cnat.
Proof. by rewrite irr1_degree rpred_nat. Qed.

Lemma irr1_gt0 i : 0 < 'chi_i 1%g.
Proof. by rewrite irr1_degree ltr0n irr_degree_gt0. Qed.

Lemma irr1_neq0 i : 'chi_i 1%g != 0.
Proof. by rewrite eqr_le ltr_geF ?irr1_gt0. Qed.

Lemma irr_neq0 i : 'chi_i != 0.
Proof. by apply: contraNneq (irr1_neq0 i) => ->; rewrite cfunE. Qed.

Definition cfIirr B (chi : 'CF(B)) : Iirr B := inord (index chi (irr B)).

Lemma cfIirrE chi : chi \in irr G -> 'chi_(cfIirr chi) = chi.
Proof.
move=> chi_irr; rewrite (tnth_nth 0) inordK ?nth_index //.
by rewrite -index_mem size_tuple in chi_irr.
Qed.

Lemma cfIirrPE J (f : J -> 'CF(G)) (P : pred J) :
    (forall j, P j -> f j \in irr G) ->
  forall j, P j -> 'chi_(cfIirr (f j)) = f j.
Proof. by move=> irr_f j /irr_f; apply: cfIirrE. Qed.

(* This is Isaacs, Corollary (2.7). *)
Corollary irr_sum_square : \sum_i ('chi[G]_i 1%g) ^+ 2 = #|G|%:R.
Proof.
rewrite -(sum_irr_degree sG) // natr_sum (reindex _ (socle_of_Iirr_bij _)) /=.
by apply: eq_bigr => i _; rewrite irr1_degree natrX.
Qed.

(* This is Isaacs, Lemma (2.11). *)
Lemma cfReg_sum : cfReg G = \sum_i 'chi_i 1%g *: 'chi_i.
Proof.
apply/cfun_inP=> x Gx; rewrite -cfReprReg cfunE Gx (mxtrace_regular sG) //=.
rewrite sum_cfunE (reindex _ (socle_of_Iirr_bij _)); apply: eq_bigr => i _.
by rewrite -irrRepr cfRepr1 !cfunE Gx mulr_natl.
Qed.

Let aG := regular_repr algCF G.
Let R_G := group_ring algCF G.

Lemma xcfun_annihilate i j A : i != j -> (A \in 'R_j)%MS -> ('chi_i).[A]%CF = 0.
Proof.
move=> neq_ij RjA; rewrite -irrRepr xcfun_repr.
by rewrite (irr_repr'_op0 _ _ RjA) ?raddf0 // eq_sym (can_eq socle_of_IirrK).
Qed.

Lemma xcfunG phi x : x \in G -> phi.[aG x]%CF = phi x.
Proof.
by move=> Gx; rewrite /xcfun /gring_row rowK -rowE !mxE !(gring_indexK, mul1g).
Qed.

Lemma xcfun_mul_id i A :
  (A \in R_G)%MS -> ('chi_i).['e_i *m A]%CF = ('chi_i).[A]%CF.
Proof.
move=> RG_A; rewrite -irrRepr !xcfun_repr gring_opM //.
by rewrite op_Wedderburn_id ?mul1mx.
Qed.

Lemma xcfun_id i j : ('chi_i).['e_j]%CF = 'chi_i 1%g *+ (i == j).
Proof.
have [<-{j} | /xcfun_annihilate->//] := altP eqP; last exact: Wedderburn_id_mem.
by rewrite -xcfunG // repr_mx1 -(xcfun_mul_id _ (envelop_mx1 _)) mulmx1.
Qed.

Lemma irr_free : free (irr G).
Proof.
apply/freeP=> s s0 i; apply: (mulIf (irr1_neq0 i)).
rewrite mul0r -(raddf0 (xcfun_r_additive 'e_i)) -{}s0 raddf_sum /=.
rewrite (bigD1 i) //= -tnth_nth xcfunZl xcfun_id eqxx big1 ?addr0 // => j ne_ji.
by rewrite -tnth_nth xcfunZl xcfun_id (negbTE ne_ji) mulr0.
Qed.

Lemma irr_inj : injective (tnth (irr G)).
Proof. by apply/injectiveP/free_uniq; rewrite map_tnth_enum irr_free. Qed.

Lemma irrK : cancel (tnth (irr G)) (@cfIirr G).
Proof. by move=> i; apply: irr_inj; rewrite cfIirrE ?mem_irr. Qed.

Lemma irr_eq1 i : ('chi_i == 1) = (i == 0).
Proof. by rewrite -irr0 (inj_eq irr_inj). Qed.

Lemma cforder_irr_eq1 i : (#['chi_i]%CF == 1%N) = (i == 0).
Proof. by rewrite -dvdn1 dvdn_cforder irr_eq1. Qed.

Lemma irr_basis : basis_of 'CF(G)%VS (irr G).
Proof.
rewrite /basis_of irr_free andbT -dimv_leqif_eq ?subvf //.
by rewrite dim_cfun (eqnP irr_free) size_tuple NirrE.
Qed.

Lemma eq_sum_nth_irr a : \sum_i a i *: 'chi[G]_i = \sum_i a i *: (irr G)`_i.
Proof. by apply: eq_bigr => i; rewrite -tnth_nth. Qed.

(* This is Isaacs, Theorem (2.8). *)
Theorem cfun_irr_sum phi : {a | phi = \sum_i a i *: 'chi[G]_i}.
Proof.
rewrite (coord_basis irr_basis (memvf phi)) -eq_sum_nth_irr.
by exists ((coord (irr G))^~ phi).
Qed.

Lemma cfRepr_standard n (rG : mx_representation algCF G n) :
  cfRepr (standard_grepr rG)
    = \sum_i (standard_irr_coef rG (W i))%:R *: 'chi_i.
Proof.
rewrite cfRepr_dsum (reindex _ (socle_of_Iirr_bij _)).
by apply: eq_bigr => i _; rewrite scaler_nat cfRepr_muln irrRepr.
Qed.

Lemma cfRepr_inj n1 n2 rG1 rG2 :
  @cfRepr _ G n1 rG1 = @cfRepr _ G n2 rG2 -> mx_rsim rG1 rG2.
Proof.
move=> eq_repr12; pose c i : algC := (standard_irr_coef _ (W i))%:R.
have [rsim1 rsim2] := (mx_rsim_standard rG1, mx_rsim_standard rG2).
apply: mx_rsim_trans (rsim1) (mx_rsim_sym _).
suffices ->: standard_grepr rG1 = standard_grepr rG2 by [].
apply: eq_bigr => Wi _; congr (muln_grepr _ _); apply/eqP; rewrite -eqC_nat.
rewrite -[Wi]irr_of_socleK -!/(c _ _ _) -!(coord_sum_free (c _ _) _ irr_free).
rewrite -!eq_sum_nth_irr -!cfRepr_standard.
by rewrite -(cfRepr_sim rsim1) -(cfRepr_sim rsim2) eq_repr12.
Qed.

Lemma cfRepr_rsimP n1 n2 rG1 rG2 :
  reflect (mx_rsim rG1 rG2) (@cfRepr _ G n1 rG1 == @cfRepr _ G n2 rG2).
Proof. by apply: (iffP eqP) => [/cfRepr_inj | /cfRepr_sim]. Qed.

Lemma irr_reprP xi :
  reflect (exists2 rG : representation _ G, mx_irreducible rG & xi = cfRepr rG)
          (xi \in irr G).
Proof.
apply: (iffP (irrP xi)) => [[i ->] | [[n rG] irr_rG ->]].
  by exists (Representation 'Chi_i); [apply: socle_irr | rewrite irrRepr].
exists (irr_of_socle (irr_comp sG rG)); rewrite -irrRepr irr_of_socleK /=.
exact/cfRepr_sim/rsim_irr_comp.
Qed.

(* This is Isaacs, Theorem (2.12). *)
Lemma Wedderburn_id_expansion i :
  'e_i = #|G|%:R^-1 *: \sum_(x in G) 'chi_i 1%g * 'chi_i x^-1%g *: aG x.
Proof.
have Rei: ('e_i \in 'R_i)%MS by apply: Wedderburn_id_mem.
have /envelop_mxP[a def_e]: ('e_i \in R_G)%MS; last rewrite -/aG in def_e.
  by move: Rei; rewrite genmxE mem_sub_gring => /andP[].
apply: canRL (scalerK (neq0CG _)) _; rewrite def_e linear_sum /=.
apply: eq_bigr => x Gx; have Gx' := groupVr Gx; rewrite scalerA; congr (_ *: _).
transitivity (cfReg G).['e_i *m aG x^-1%g]%CF.
  rewrite def_e mulmx_suml raddf_sum (bigD1 x) //= -scalemxAl xcfunZr.
  rewrite -repr_mxM // mulgV xcfunG // cfRegE eqxx mulrC big1 ?addr0 //.
  move=> y /andP[Gy /negbTE neq_xy]; rewrite -scalemxAl xcfunZr -repr_mxM //.
  by rewrite xcfunG ?groupM // cfRegE -eq_mulgV1 neq_xy mulr0.
rewrite cfReg_sum -xcfun_rE raddf_sum /= (bigD1 i) //= xcfunZl.
rewrite xcfun_mul_id ?envelop_mx_id ?xcfunG ?groupV ?big1 ?addr0 // => j ne_ji.
rewrite xcfunZl (xcfun_annihilate ne_ji) ?mulr0 //.
have /andP[_ /(submx_trans _)-> //] := Wedderburn_ideal (W i).
by rewrite mem_mulsmx // envelop_mx_id ?groupV.
Qed.

End IrrClass.

Arguments cfReg {gT} B%g.
Prenex Implicits cfIirr irrK.
Arguments irrP {gT G xi}.
Arguments irr_reprP {gT G xi}.
Arguments irr_inj {gT G} [x1 x2].

Section IsChar.

Variable gT : finGroupType.

Definition character {G : {set gT}} :=
  [qualify a phi : 'CF(G) | [forall i, coord (irr G) i phi \in Cnat]].
Fact character_key G : pred_key (@character G). Proof. by []. Qed.
Canonical character_keyed G := KeyedQualifier (character_key G).

Variable G : {group gT}.
Implicit Types (phi chi xi : 'CF(G)) (i : Iirr G).

Lemma irr_char i : 'chi_i \is a character.
Proof.
by apply/forallP=> j; rewrite (tnth_nth 0) coord_free ?irr_free ?isNatC_nat.
Qed.

Lemma cfun1_char : (1 : 'CF(G)) \is a character.
Proof. by rewrite -irr0 irr_char. Qed.

Lemma cfun0_char : (0 : 'CF(G)) \is a character.
Proof. by apply/forallP=> i; rewrite linear0 rpred0. Qed.

Fact add_char : addr_closed (@character G).
Proof.
split=> [|chi xi /forallP-Nchi /forallP-Nxi]; first exact: cfun0_char.
by apply/forallP=> i; rewrite linearD rpredD /=.
Qed.
Canonical character_addrPred := AddrPred add_char.

Lemma char_sum_irrP {phi} :
  reflect (exists n, phi = \sum_i (n i)%:R *: 'chi_i) (phi \is a character).
Proof.
apply: (iffP idP)=> [/forallP-Nphi | [n ->]]; last first.
  by apply: rpred_sum => i _; rewrite scaler_nat rpredMn // irr_char.
do [have [a ->] := cfun_irr_sum phi] in Nphi *; exists (truncC \o a).
apply: eq_bigr => i _; congr (_ *: _); have:= eqP (Nphi i).
by rewrite eq_sum_nth_irr coord_sum_free ?irr_free.
Qed.

Lemma char_sum_irr chi :
  chi \is a character -> {r | chi = \sum_(i <- r) 'chi_i}.
Proof.
move=> Nchi; apply: sig_eqW; case/char_sum_irrP: Nchi => n {chi}->.
elim/big_rec: _ => [|i _ _ [r ->]]; first by exists nil; rewrite big_nil.
exists (ncons (n i) i r); rewrite scaler_nat.
by elim: {n}(n i) => [|n IHn]; rewrite ?add0r //= big_cons mulrS -addrA IHn.
Qed.

Lemma Cnat_char1 chi : chi \is a character -> chi 1%g \in Cnat.
Proof.
case/char_sum_irr=> r ->{chi}.
by elim/big_rec: _ => [|i chi _ Nchi1]; rewrite cfunE ?rpredD // Cnat_irr1.
Qed.

Lemma char1_ge0 chi : chi \is a character -> 0 <= chi 1%g.
Proof. by move/Cnat_char1/Cnat_ge0. Qed.

Lemma char1_eq0 chi : chi \is a character -> (chi 1%g == 0) = (chi == 0).
Proof.
case/char_sum_irr=> r ->; apply/idP/idP=> [|/eqP->]; last by rewrite cfunE.
case: r => [|i r]; rewrite ?big_nil // sum_cfunE big_cons.
rewrite paddr_eq0 ?sumr_ge0  => // [||j _]; rewrite 1?ltrW ?irr1_gt0 //.
by rewrite (negbTE (irr1_neq0 i)).
Qed.

Lemma char1_gt0 chi : chi \is a character -> (0 < chi 1%g) = (chi != 0).
Proof. by move=> Nchi; rewrite -char1_eq0 // Cnat_gt0 ?Cnat_char1. Qed.

Lemma char_reprP phi :
  reflect (exists rG : representation algCF G, phi = cfRepr rG)
          (phi \is a character).
Proof.
apply: (iffP char_sum_irrP) => [[n ->] | [[n rG] ->]]; last first.
  exists (fun i => standard_irr_coef rG (socle_of_Iirr i)).
  by rewrite -cfRepr_standard (cfRepr_sim (mx_rsim_standard rG)).
exists (\big[dadd_grepr/grepr0]_i muln_grepr (Representation 'Chi_i) (n i)).
rewrite cfRepr_dsum; apply: eq_bigr => i _.
by rewrite cfRepr_muln irrRepr scaler_nat.
Qed.

Local Notation reprG := (mx_representation algCF G).

Lemma cfRepr_char n (rG : reprG n) : cfRepr rG \is a character.
Proof. by apply/char_reprP; exists (Representation rG). Qed.

Lemma cfReg_char : cfReg G \is a character.
Proof. by rewrite -cfReprReg cfRepr_char. Qed.

Lemma cfRepr_prod n1 n2 (rG1 : reprG n1) (rG2 : reprG n2) :
  cfRepr rG1 * cfRepr rG2 = cfRepr (prod_repr rG1 rG2).
Proof. by apply/cfun_inP=> x Gx; rewrite !cfunE /= Gx mxtrace_prod. Qed.

Lemma mul_char : mulr_closed (@character G).
Proof.
split=> [|_ _ /char_reprP[rG1 ->] /char_reprP[rG2 ->]]; first exact: cfun1_char.
apply/char_reprP; exists (Representation (prod_repr rG1 rG2)).
by rewrite cfRepr_prod.
Qed.
Canonical char_mulrPred := MulrPred mul_char.
Canonical char_semiringPred := SemiringPred mul_char.

End IsChar.
Prenex Implicits character.
Arguments char_reprP {gT G phi}.

Section AutChar.

Variables (gT : finGroupType) (G : {group gT}).
Implicit Type u : {rmorphism algC -> algC}.
Implicit Type chi : 'CF(G).

Lemma cfRepr_map u n (rG : mx_representation algCF G n) :
  cfRepr (map_repr u rG) = cfAut u (cfRepr rG).
Proof. by apply/cfun_inP=> x Gx; rewrite !cfunE Gx map_reprE trace_map_mx. Qed.

Lemma cfAut_char u chi : (cfAut u chi \is a character) = (chi \is a character).
Proof.
without loss /char_reprP[rG ->]: u chi / chi \is a character.
  by move=> IHu; apply/idP/idP=> ?; first rewrite -(cfAutK u chi); rewrite IHu.
rewrite cfRepr_char; apply/char_reprP.
by exists (Representation (map_repr u rG)); rewrite cfRepr_map.
Qed.

Lemma cfConjC_char chi : (chi^*%CF \is a character) = (chi \is a character).
Proof. exact: cfAut_char. Qed.

Lemma cfAut_char1 u (chi : 'CF(G)) :
  chi \is a character -> cfAut u chi 1%g = chi 1%g.
Proof. by move/Cnat_char1=> Nchi1; rewrite cfunE aut_Cnat. Qed.

Lemma cfAut_irr1 u i : (cfAut u 'chi[G]_i) 1%g = 'chi_i 1%g.
Proof. exact: cfAut_char1 (irr_char i). Qed.

Lemma cfConjC_char1 (chi : 'CF(G)) :
  chi \is a character -> chi^*%CF 1%g = chi 1%g.
Proof. exact: cfAut_char1. Qed.

Lemma cfConjC_irr1 u i : ('chi[G]_i)^*%CF 1%g = 'chi_i 1%g.
Proof. exact: cfAut_irr1. Qed.

End AutChar.

Section Linear.

Variables (gT : finGroupType) (G : {group gT}).

Definition linear_char {B : {set gT}} :=
  [qualify a phi : 'CF(B) | (phi \is a character) && (phi 1%g == 1)].

Section OneChar.

Variable xi : 'CF(G).
Hypothesis CFxi : xi \is a linear_char.

Lemma lin_char1: xi 1%g = 1.
Proof. by case/andP: CFxi => _ /eqP. Qed.

Lemma lin_charW : xi \is a character.
Proof. by case/andP: CFxi. Qed.

Lemma cfun1_lin_char : (1 : 'CF(G)) \is a linear_char.
Proof. by rewrite qualifE cfun1_char /= cfun11. Qed.

Lemma lin_charM : {in G &, {morph xi : x y / (x * y)%g >-> x * y}}.
Proof.
move=> x y Gx Gy; case/andP: CFxi => /char_reprP[[n rG] -> /=].
rewrite cfRepr1 pnatr_eq1 => /eqP n1; rewrite {n}n1 in rG *.
rewrite !cfunE Gx Gy groupM //= !mulr1n repr_mxM //.
by rewrite [rG x]mx11_scalar [rG y]mx11_scalar -scalar_mxM !mxtrace_scalar.
Qed.

Lemma lin_char_prod I r (P : pred I) (x : I -> gT) :
    (forall i, P i -> x i \in G) ->
  xi (\prod_(i <- r | P i) x i)%g = \prod_(i <- r | P i) xi (x i).
Proof.
move=> Gx; elim/(big_load (fun y => y \in G)): _.
elim/big_rec2: _ => [|i a y Pi [Gy <-]]; first by rewrite lin_char1.
by rewrite groupM ?lin_charM ?Gx.
Qed.

Let xiMV x : x \in G -> xi x * xi (x^-1)%g = 1.
Proof. by move=> Gx; rewrite -lin_charM ?groupV // mulgV lin_char1. Qed.

Lemma lin_char_neq0 x : x \in G -> xi x != 0.
Proof.
by move/xiMV/(congr1 (predC1 0)); rewrite /= oner_eq0 mulf_eq0 => /norP[].
Qed.

Lemma lin_charV x : x \in G -> xi x^-1%g = (xi x)^-1.
Proof. by move=> Gx; rewrite -[_^-1]mulr1 -(xiMV Gx) mulKf ?lin_char_neq0. Qed.

Lemma lin_charX x n : x \in G -> xi (x ^+ n)%g = xi x ^+ n.
Proof.
move=> Gx; elim: n => [|n IHn]; first exact: lin_char1.
by rewrite expgS exprS lin_charM ?groupX ?IHn.
Qed.

Lemma lin_char_unity_root x : x \in G -> xi x ^+ #[x] = 1.
Proof. by move=> Gx; rewrite -lin_charX // expg_order lin_char1. Qed.

Lemma normC_lin_char x : x \in G -> `|xi x| = 1.
Proof.
move=> Gx; apply/eqP; rewrite -(@pexpr_eq1 _ _ #[x]) ?normr_ge0 //.
by rewrite -normrX // lin_char_unity_root ?normr1.
Qed.

Lemma lin_charV_conj x : x \in G -> xi x^-1%g = (xi x)^*.
Proof.
move=> Gx; rewrite lin_charV // invC_norm mulrC normC_lin_char //.
by rewrite expr1n divr1.
Qed.

Lemma lin_char_irr : xi \in irr G.
Proof.
case/andP: CFxi => /char_reprP[rG ->]; rewrite cfRepr1 pnatr_eq1 => /eqP n1.
by apply/irr_reprP; exists rG => //; apply/mx_abs_irrW/linear_mx_abs_irr.
Qed.

Lemma mul_conjC_lin_char : xi * xi^*%CF = 1.
Proof.
apply/cfun_inP=> x Gx.
by rewrite !cfunE cfun1E Gx -normCK normC_lin_char ?expr1n.
Qed.

Lemma lin_char_unitr : xi \in GRing.unit.
Proof. by apply/unitrPr; exists xi^*%CF; apply: mul_conjC_lin_char. Qed.

Lemma invr_lin_char : xi^-1 = xi^*%CF.
Proof. by rewrite -[_^-1]mulr1 -mul_conjC_lin_char mulKr ?lin_char_unitr. Qed.

Lemma fful_lin_char_inj : cfaithful xi -> {in G &, injective xi}.
Proof.
move=> fful_phi x y Gx Gy xi_xy; apply/eqP; rewrite eq_mulgV1 -in_set1.
rewrite (subsetP fful_phi) // inE groupM ?groupV //=; apply/forallP=> z.
have [Gz | G'z] := boolP (z \in G); last by rewrite !cfun0 ?groupMl ?groupV.
by rewrite -mulgA lin_charM ?xi_xy -?lin_charM ?groupM ?groupV // mulKVg.
Qed.

End OneChar.

Lemma cfAut_lin_char u (xi : 'CF(G)) :
  (cfAut u xi \is a linear_char) = (xi \is a linear_char).
Proof. by rewrite qualifE cfAut_char; apply/andb_id2l=> /cfAut_char1->. Qed.

Lemma cfConjC_lin_char (xi : 'CF(G)) :
  (xi^*%CF \is a linear_char) = (xi \is a linear_char).
Proof. exact: cfAut_lin_char. Qed.

Lemma card_Iirr_abelian : abelian G -> #|Iirr G| = #|G|.
Proof. by rewrite card_ord NirrE card_classes_abelian => /eqP. Qed.

Lemma card_Iirr_cyclic : cyclic G -> #|Iirr G| = #|G|.
Proof. by move/cyclic_abelian/card_Iirr_abelian. Qed.

Lemma char_abelianP :
  reflect (forall i : Iirr G, 'chi_i \is a linear_char) (abelian G).
Proof.
apply: (iffP idP) => [cGG i | CF_G].
  rewrite qualifE irr_char /= irr1_degree.
  by rewrite irr_degree_abelian //; last apply: groupC.
rewrite card_classes_abelian -NirrE -eqC_nat -irr_sum_square //.
rewrite -{1}[Nirr G]card_ord -sumr_const; apply/eqP/eq_bigr=> i _.
by rewrite lin_char1 ?expr1n ?CF_G.
Qed.

Lemma irr_repr_lin_char (i : Iirr G) x :
    x \in G -> 'chi_i \is a linear_char ->
  irr_repr (socle_of_Iirr i) x = ('chi_i x)%:M.
Proof.
move=> Gx CFi; rewrite -irrRepr cfunE Gx.
move: (_ x); rewrite -[irr_degree _]natCK -irr1_degree lin_char1 //.
by rewrite (natCK 1) => A; rewrite trace_mx11 -mx11_scalar.
Qed.

Fact linear_char_key B : pred_key (@linear_char B). Proof. by []. Qed.
Canonical linear_char_keted B := KeyedQualifier (linear_char_key B).
Fact linear_char_divr : divr_closed (@linear_char G).
Proof.
split=> [|chi xi Lchi Lxi]; first exact: cfun1_lin_char.
rewrite invr_lin_char // qualifE cfunE.
by rewrite rpredM ?lin_char1 ?mulr1 ?lin_charW //= cfConjC_lin_char.
Qed.
Canonical lin_char_mulrPred := MulrPred linear_char_divr.
Canonical lin_char_divrPred := DivrPred linear_char_divr.

Lemma irr_cyclic_lin i : cyclic G -> 'chi[G]_i \is a linear_char.
Proof. by move/cyclic_abelian/char_abelianP. Qed.

Lemma irr_prime_lin i : prime #|G| -> 'chi[G]_i \is a linear_char.
Proof. by move/prime_cyclic/irr_cyclic_lin. Qed.

End Linear.

Prenex Implicits linear_char.

Section OrthogonalityRelations.

Variables aT gT : finGroupType.

(* This is Isaacs, Lemma (2.15) *)
Lemma repr_rsim_diag (G : {group gT}) f (rG : mx_representation algCF G f) x :
    x \in G -> let chi := cfRepr rG in
  exists e,
 [/\ (*a*) exists2 B, B \in unitmx & rG x = invmx B *m diag_mx e *m B,
     (*b*) (forall i, e 0 i ^+ #[x] = 1) /\ (forall i, `|e 0 i| = 1),
     (*c*) chi x = \sum_i e 0 i /\ `|chi x| <= chi 1%g
   & (*d*) chi x^-1%g = (chi x)^*].
Proof.
move=> Gx; without loss cGG: G rG Gx / abelian G.
  have sXG: <[x]> \subset G by rewrite cycle_subG.
  move/(_ _ (subg_repr rG sXG) (cycle_id x) (cycle_abelian x)).
  by rewrite /= !cfunE !groupV Gx (cycle_id x) !group1.
have [I U W simU W1 dxW]: mxsemisimple rG 1%:M.
  rewrite -(reducible_Socle1 (DecSocleType rG) (mx_Maschke _ (algC'G G))).
  exact: Socle_semisimple.
have linU i: \rank (U i) = 1%N.
  by apply: mxsimple_abelian_linear cGG (simU i); apply: groupC.
have castI: f = #|I|.
  by rewrite -(mxrank1 algCF f) -W1 (eqnP dxW) /= -sum1_card; apply/eq_bigr.
pose B := \matrix_j nz_row (U (enum_val (cast_ord castI j))).
have rowU i: (nz_row (U i) :=: U i)%MS.
  apply/eqmxP; rewrite -(geq_leqif (mxrank_leqif_eq (nz_row_sub _))) linU.
  by rewrite lt0n mxrank_eq0 (nz_row_mxsimple (simU i)).
have unitB: B \in unitmx.
  rewrite -row_full_unit -sub1mx -W1; apply/sumsmx_subP=> i _.
  pose j := cast_ord (esym castI) (enum_rank i).
  by rewrite (submx_trans _ (row_sub j B)) // rowK cast_ordKV enum_rankK rowU.
pose e := \row_j row j (B *m rG x *m invmx B) 0 j.
have rGx: rG x = invmx B *m diag_mx e *m B.
  rewrite -mulmxA; apply: canRL (mulKmx unitB) _.
  apply/row_matrixP=> j; rewrite 2!row_mul; set u := row j B.
  have /sub_rVP[a def_ux]: (u *m rG x <= u)%MS.
    rewrite /u rowK rowU (eqmxMr _ (rowU _)).
    exact: (mxmoduleP (mxsimple_module (simU _))).
  rewrite def_ux [u]rowE scalemxAl; congr (_ *m _).
  apply/rowP=> k; rewrite 5!mxE !row_mul def_ux [u]rowE scalemxAl mulmxK //.
  by rewrite !mxE !eqxx !mulr_natr eq_sym.
have exp_e j: e 0 j ^+ #[x] = 1.
  suffices: (diag_mx e j j) ^+ #[x] = (B *m rG (x ^+ #[x])%g *m invmx B) j j.
    by rewrite expg_order repr_mx1 mulmx1 mulmxV // [e]lock !mxE eqxx.
  elim: #[x] => [|n IHn]; first by rewrite repr_mx1 mulmx1 mulmxV // !mxE eqxx.
  rewrite expgS repr_mxM ?groupX // {1}rGx -!mulmxA mulKVmx //.
  by rewrite mul_diag_mx mulmxA [M in _ = M]mxE -IHn exprS {1}mxE eqxx.
have norm1_e j: `|e 0 j| = 1.
  apply/eqP; rewrite -(@pexpr_eq1 _ _ #[x]) ?normr_ge0 //.
  by rewrite -normrX exp_e normr1.
exists e; split=> //; first by exists B.
  rewrite cfRepr1 !cfunE Gx rGx mxtrace_mulC mulKVmx // mxtrace_diag.
  split=> //=; apply: (ler_trans (ler_norm_sum _ _ _)).
  by rewrite (eq_bigr _ (in1W norm1_e)) sumr_const card_ord lerr.
rewrite !cfunE groupV !mulrb Gx rGx mxtrace_mulC mulKVmx //.
rewrite -trace_map_mx map_diag_mx; set d' := diag_mx _.
rewrite -[d'](mulKVmx unitB) mxtrace_mulC -[_ *m _](repr_mxK rG Gx) rGx.
rewrite -!mulmxA mulKVmx // (mulmxA d').
suffices->: d' *m diag_mx e = 1%:M by rewrite mul1mx mulKmx.
rewrite mulmx_diag -diag_const_mx; congr diag_mx; apply/rowP=> j.
by rewrite [e]lock !mxE mulrC -normCK -lock norm1_e expr1n.
Qed.

Variables (A : {group aT}) (G : {group gT}).

(* This is Isaacs, Lemma (2.15) (d). *)
Lemma char_inv (chi : 'CF(G)) x : chi \is a character -> chi x^-1%g = (chi x)^*.
Proof.
case Gx: (x \in G); last by rewrite !cfun0 ?rmorph0 ?groupV ?Gx.
by case/char_reprP=> rG ->; have [e [_ _ _]] := repr_rsim_diag rG Gx.
Qed.

Lemma irr_inv i x : 'chi[G]_i x^-1%g = ('chi_i x)^*.
Proof. exact/char_inv/irr_char. Qed.

(* This is Isaacs, Theorem (2.13). *)
Theorem generalized_orthogonality_relation y (i j : Iirr G) :
  #|G|%:R^-1 * (\sum_(x in G) 'chi_i (x * y)%g * 'chi_j x^-1%g)
    = (i == j)%:R * ('chi_i y / 'chi_i 1%g).
Proof.
pose W := @socle_of_Iirr _ G; pose e k := Wedderburn_id (W k).
pose aG := regular_repr algCF G.
have [Gy | notGy] := boolP (y \in G); last first.
  rewrite cfun0 // mul0r big1 ?mulr0 // => x Gx.
  by rewrite cfun0 ?groupMl ?mul0r.
transitivity (('chi_i).[e j *m aG y]%CF / 'chi_j 1%g).
  rewrite [e j]Wedderburn_id_expansion -scalemxAl xcfunZr -mulrA; congr (_ * _).
  rewrite mulmx_suml raddf_sum big_distrl; apply: eq_bigr => x Gx /=.
  rewrite -scalemxAl xcfunZr -repr_mxM // xcfunG ?groupM // mulrAC mulrC.
  by congr (_ * _); rewrite mulrC mulKf ?irr1_neq0.
rewrite mulr_natl mulrb; have [<-{j} | neq_ij] := altP eqP.
  by congr (_ / _); rewrite xcfun_mul_id ?envelop_mx_id ?xcfunG.
rewrite (xcfun_annihilate neq_ij) ?mul0r //.
case/andP: (Wedderburn_ideal (W j)) => _; apply: submx_trans.
by rewrite mem_mulsmx ?Wedderburn_id_mem ?envelop_mx_id.
Qed.

(* This is Isaacs, Corollary (2.14). *)
Corollary first_orthogonality_relation (i j : Iirr G) :
  #|G|%:R^-1 * (\sum_(x in G) 'chi_i x * 'chi_j x^-1%g) = (i == j)%:R.
Proof.
have:= generalized_orthogonality_relation 1 i j.
rewrite mulrA mulfK ?irr1_neq0 // => <-; congr (_ * _).
by apply: eq_bigr => x; rewrite mulg1.
Qed.

(* The character table. *)

Definition irr_class i := enum_val (cast_ord (NirrE G) i).
Definition class_Iirr xG :=
  cast_ord (esym (NirrE G)) (enum_rank_in (classes1 G) xG).

Local Notation c := irr_class.
Local Notation g i := (repr (c i)).
Local Notation iC := class_Iirr.

Definition character_table := \matrix_(i, j) 'chi[G]_i (g j).
Local Notation X := character_table.

Lemma irr_classP i : c i \in classes G.
Proof. exact: enum_valP. Qed.

Lemma repr_irr_classK i : g i ^: G = c i.
Proof. by case/repr_classesP: (irr_classP i). Qed.

Lemma irr_classK : cancel c iC.
Proof. by move=> i; rewrite /iC enum_valK_in cast_ordK. Qed.

Lemma class_IirrK : {in classes G, cancel iC c}.
Proof. by move=> xG GxG; rewrite /c cast_ordKV enum_rankK_in. Qed.

Lemma reindex_irr_class R idx (op : @Monoid.com_law R idx) F :
  \big[op/idx]_(xG in classes G) F xG = \big[op/idx]_i F (c i).
Proof.
rewrite (reindex c); first by apply: eq_bigl => i; apply: enum_valP.
by exists iC; [apply: in1W; apply: irr_classK | apply: class_IirrK].
Qed.

(* The explicit value of the inverse is needed for the proof of the second    *)
(* orthogonality relation.                                                    *)
Let X' := \matrix_(i, j) (#|'C_G[g i]|%:R^-1 * ('chi[G]_j (g i))^*).
Let XX'_1: X *m X' = 1%:M.
Proof.
apply/matrixP=> i j; rewrite !mxE -first_orthogonality_relation mulr_sumr.
rewrite sum_by_classes => [|u v Gu Gv]; last by rewrite -conjVg !cfunJ.
rewrite reindex_irr_class /=; apply/esym/eq_bigr=> k _.
rewrite !mxE irr_inv // -/(g k) -divg_index -indexgI /=.
rewrite (char0_natf_div Cchar) ?dvdn_indexg // index_cent1 invfM invrK.
by rewrite repr_irr_classK mulrCA mulrA mulrCA.
Qed.

Lemma character_table_unit : X \in unitmx.
Proof. by case/mulmx1_unit: XX'_1. Qed.
Let uX := character_table_unit.

(* This is Isaacs, Theorem (2.18). *)
Theorem second_orthogonality_relation x y : 
    y \in G ->
  \sum_i 'chi[G]_i x * ('chi_i y)^* = #|'C_G[x]|%:R *+ (x \in y ^: G).
Proof.
move=> Gy; pose i_x := iC (x ^: G); pose i_y := iC (y ^: G).
have [Gx | notGx] := boolP (x \in G); last first.
  rewrite (contraNF (subsetP _ x) notGx) ?class_subG ?big1 // => i _.
  by rewrite cfun0 ?mul0r.
transitivity ((#|'C_G[repr (y ^: G)]|%:R *: (X' *m X)) i_y i_x).
  rewrite scalemxAl !mxE; apply: eq_bigr => k _; rewrite !mxE mulrC -!mulrA.
  by rewrite !class_IirrK ?mem_classes // !cfun_repr mulVKf ?neq0CG.
rewrite mulmx1C // !mxE -!divg_index !(index_cent1, =^~ indexgI).
rewrite (class_eqP (mem_repr y _)) ?class_refl // mulr_natr.
rewrite (can_in_eq class_IirrK) ?mem_classes //.
have [-> | not_yGx] := altP eqP; first by rewrite class_refl.
by rewrite [x \in _](contraNF _ not_yGx) // => /class_eqP->.
Qed.

Lemma eq_irr_mem_classP x y :
  y \in G -> reflect (forall i, 'chi[G]_i x = 'chi_i y) (x \in y ^: G).
Proof.
move=> Gy; apply: (iffP idP) => [/imsetP[z Gz ->] i | xGy]; first exact: cfunJ.
have Gx: x \in G.
  congr is_true: Gy; apply/eqP; rewrite -(can_eq oddb) -eqC_nat -!cfun1E.
  by rewrite -irr0 xGy.
congr is_true: (class_refl G x); apply/eqP; rewrite -(can_eq oddb).
rewrite -(eqn_pmul2l (cardG_gt0 'C_G[x])) -eqC_nat !mulrnA; apply/eqP.
by rewrite -!second_orthogonality_relation //; apply/eq_bigr=> i _; rewrite xGy.
Qed.

(* This is Isaacs, Theorem (6.32) (due to Brauer). *)
Lemma card_afix_irr_classes (ito : action A (Iirr G)) (cto : action A _) a :
    a \in A -> [acts A, on classes G | cto] -> 
    (forall i x y, x \in G -> y \in cto (x ^: G) a ->
      'chi_i x = 'chi_(ito i a) y) ->
  #|'Fix_ito[a]| = #|'Fix_(classes G | cto)[a]|.
Proof.
move=> Aa actsAG stabAchi; apply/eqP; rewrite -eqC_nat; apply/eqP.
have [[cP cK] iCK] := (irr_classP, irr_classK, class_IirrK).
pose icto b i := iC (cto (c i) b).
have Gca i: cto (c i) a \in classes G by rewrite (acts_act actsAG).
have inj_qa: injective (icto a).
  by apply: can_inj (icto a^-1%g) _ => i; rewrite /icto iCK ?actKin ?cK.
pose Pa : 'M[algC]_(Nirr G) := perm_mx (actperm ito a).
pose qa := perm inj_qa; pose Qa : 'M[algC]_(Nirr G) := perm_mx qa^-1^-1%g.
transitivity (\tr Pa).
  rewrite -sumr_const big_mkcond; apply: eq_bigr => i _.
  by rewrite !mxE permE inE sub1set inE; case: ifP.
symmetry; transitivity (\tr Qa).
  rewrite cardsE -sumr_const -big_filter_cond big_mkcond big_filter /=.
  rewrite reindex_irr_class; apply: eq_bigr => i _; rewrite !mxE invgK permE.
  by rewrite inE sub1set inE -(can_eq cK) iCK //; case: ifP.
rewrite -[Pa](mulmxK uX) -[Qa](mulKmx uX) mxtrace_mulC; congr (\tr(_ *m _)).
rewrite -row_permE -col_permE; apply/matrixP=> i j; rewrite !mxE.
rewrite -{2}[j](permKV qa); move: {j}(_ j) => j; rewrite !permE iCK //.
apply: stabAchi; first by case/repr_classesP: (cP j).
by rewrite repr_irr_classK (mem_repr_classes (Gca _)).
Qed.

End OrthogonalityRelations.

Prenex Implicits irr_class class_Iirr irr_classK.
Arguments class_IirrK {gT G%G} [xG%g] GxG : rename.
Arguments character_table {gT} G%g.

Section InnerProduct.

Variable (gT : finGroupType) (G : {group gT}).

Lemma cfdot_irr i j : '['chi_i, 'chi_j]_G = (i == j)%:R.
Proof.
rewrite -first_orthogonality_relation; congr (_ * _).
by apply: eq_bigr => x Gx; rewrite irr_inv.
Qed.

Lemma cfnorm_irr i : '['chi[G]_i] = 1.
Proof. by rewrite cfdot_irr eqxx. Qed.

Lemma irr_orthonormal : orthonormal (irr G).
Proof.
apply/orthonormalP; split; first exact: free_uniq (irr_free G).
move=> _ _ /irrP[i ->] /irrP[j ->].
by rewrite cfdot_irr (inj_eq irr_inj).
Qed.

Lemma coord_cfdot phi i : coord (irr G) i phi = '[phi, 'chi_i].
Proof.
rewrite {2}(coord_basis (irr_basis G) (memvf phi)).
rewrite cfdot_suml (bigD1 i) // cfdotZl /= -tnth_nth cfdot_irr eqxx mulr1.
rewrite big1 ?addr0 // => j neq_ji; rewrite cfdotZl /= -tnth_nth cfdot_irr.
by rewrite (negbTE neq_ji) mulr0.
Qed.

Lemma cfun_sum_cfdot phi : phi = \sum_i '[phi, 'chi_i]_G *: 'chi_i.
Proof.
rewrite {1}(coord_basis (irr_basis G) (memvf phi)).
by apply: eq_bigr => i _; rewrite coord_cfdot -tnth_nth.
Qed.

Lemma cfdot_sum_irr phi psi :
  '[phi, psi]_G = \sum_i '[phi, 'chi_i] * '[psi, 'chi_i]^*.
Proof.
rewrite {1}[phi]cfun_sum_cfdot cfdot_suml; apply: eq_bigr => i _.
by rewrite cfdotZl -cfdotC.
Qed.

Lemma Cnat_cfdot_char_irr i phi :
  phi \is a character -> '[phi, 'chi_i]_G \in Cnat.
Proof. by move/forallP/(_ i); rewrite coord_cfdot. Qed.

Lemma cfdot_char_r phi chi :  
  chi \is a character -> '[phi, chi]_G = \sum_i '[phi, 'chi_i] * '[chi, 'chi_i].
Proof.
move=> Nchi; rewrite cfdot_sum_irr; apply: eq_bigr => i _; congr (_ * _).
by rewrite conj_Cnat ?Cnat_cfdot_char_irr.
Qed.

Lemma Cnat_cfdot_char chi xi :
  chi \is a character -> xi \is a character -> '[chi, xi]_G \in Cnat.
Proof.
move=> Nchi Nxi; rewrite cfdot_char_r ?rpred_sum // => i _.
by rewrite rpredM ?Cnat_cfdot_char_irr.
Qed.
 
Lemma cfdotC_char chi xi :
  chi \is a character-> xi \is a character -> '[chi, xi]_G = '[xi, chi].
Proof. by move=> Nchi Nxi; rewrite cfdotC conj_Cnat ?Cnat_cfdot_char. Qed.

Lemma irrEchar chi : (chi \in irr G) = (chi \is a character) && ('[chi] == 1).
Proof.
apply/irrP/andP=> [[i ->] | [Nchi]]; first by rewrite irr_char cfnorm_irr.
rewrite cfdot_sum_irr => /eqP/Cnat_sum_eq1[i _| i [_ ci1 cj0]].
  by rewrite rpredM // ?conj_Cnat ?Cnat_cfdot_char_irr.
exists i; rewrite [chi]cfun_sum_cfdot (bigD1 i) //=.
rewrite -(@normr_idP _ _ (@Cnat_ge0 _ (Cnat_cfdot_char_irr i Nchi))).
rewrite normC_def {}ci1 sqrtC1 scale1r big1 ?addr0 // => j neq_ji.
by rewrite (('[_] =P 0) _) ?scale0r // -normr_eq0 normC_def cj0 ?sqrtC0.
Qed.

Lemma irrWchar chi : chi \in irr G -> chi \is a character.
Proof. by rewrite irrEchar => /andP[]. Qed.

Lemma irrWnorm chi : chi \in irr G -> '[chi] = 1.
Proof. by rewrite irrEchar => /andP[_ /eqP]. Qed.

Lemma mul_lin_irr xi chi :
  xi \is a linear_char -> chi \in irr G -> xi * chi \in irr G.
Proof.
move=> Lxi; rewrite !irrEchar => /andP[Nphi /eqP <-].
rewrite rpredM // ?lin_charW //=; apply/eqP; congr (_ * _).
apply: eq_bigr => x Gx; rewrite !cfunE rmorphM mulrACA -(lin_charV_conj Lxi) //.
by rewrite -lin_charM ?groupV // mulgV lin_char1 ?mul1r.
Qed.

Lemma eq_scaled_irr a b i j :
  (a *: 'chi[G]_i == b *: 'chi_j) = (a == b) && ((a == 0) || (i == j)).
Proof.
apply/eqP/andP=> [|[/eqP-> /pred2P[]-> //]]; last by rewrite !scale0r.
move/(congr1 (cfdotr 'chi__)) => /= eq_ai_bj.
move: {eq_ai_bj}(eq_ai_bj i) (esym (eq_ai_bj j)); rewrite !cfdotZl !cfdot_irr.
by rewrite !mulr_natr !mulrb !eqxx eq_sym orbC; case: ifP => _ -> //= ->.
Qed.

Lemma eq_signed_irr (s t : bool) i j :
  ((-1) ^+ s *: 'chi[G]_i == (-1) ^+ t *: 'chi_j) = (s == t) && (i == j).
Proof. by rewrite eq_scaled_irr signr_eq0 (inj_eq signr_inj). Qed.

Lemma eq_scale_irr a (i j : Iirr G) :
  (a *: 'chi_i == a *: 'chi_j) = (a == 0) || (i == j).
Proof. by rewrite eq_scaled_irr eqxx. Qed.

Lemma eq_addZ_irr a b (i j r t : Iirr G) :
  (a *: 'chi_i + b *: 'chi_j == a *: 'chi_r + b *: 'chi_t)
   = [|| [&& (a == 0) || (i == r) & (b == 0) || (j == t)],
         [&& i == t, j == r & a == b] | [&& i == j, r == t & a == - b]].
Proof.
rewrite -!eq_scale_irr; apply/eqP/idP; last first.
  case/orP; first by case/andP=> /eqP-> /eqP->.
  case/orP=> /and3P[/eqP-> /eqP-> /eqP->]; first by rewrite addrC.
  by rewrite !scaleNr !addNr.
have [-> /addrI/eqP-> // | /= ] := altP eqP.
rewrite eq_scale_irr => /norP[/negP nz_a /negPf neq_ir].
move/(congr1 (cfdotr 'chi__))/esym/eqP => /= eq_cfdot.
move: {eq_cfdot}(eq_cfdot i) (eq_cfdot r); rewrite eq_sym !cfdotDl !cfdotZl.
rewrite !cfdot_irr !mulr_natr !mulrb !eqxx -!(eq_sym i) neq_ir !add0r.
have [<- _ | _] := i =P t; first by rewrite neq_ir addr0; case: ifP => // _ ->.
rewrite 2!fun_if if_arg addr0 addr_eq0; case: eqP => //= <- ->.
by rewrite neq_ir 2!fun_if if_arg eq_sym addr0; case: ifP.
Qed.

Lemma eq_subZnat_irr (a b : nat) (i j r t : Iirr G) :
  (a%:R *: 'chi_i - b%:R *: 'chi_j == a%:R *: 'chi_r - b%:R *: 'chi_t)
     =   [|| a == 0%N | i == r] && [|| b == 0%N | j == t]
      || [&& i == j, r == t & a == b].
Proof.
rewrite -!scaleNr eq_addZ_irr oppr_eq0 opprK -addr_eq0 -natrD eqr_nat.
by rewrite !pnatr_eq0 addn_eq0; case: a b => [|a] [|b]; rewrite ?andbF.
Qed.

End InnerProduct.

Section IrrConstt.

Variable (gT : finGroupType) (G H : {group gT}).

Lemma char1_ge_norm (chi : 'CF(G)) x :
  chi \is a character -> `|chi x| <= chi 1%g.
Proof.
case/char_reprP=> rG ->; case Gx: (x \in G); last first.
  by rewrite cfunE cfRepr1 Gx normr0 ler0n.
by have [e [_ _ []]] := repr_rsim_diag rG Gx.
Qed.

Lemma max_cfRepr_norm_scalar n (rG : mx_representation algCF G n) x :
     x \in G -> `|cfRepr rG x| = cfRepr rG 1%g ->
   exists2 c, `|c| = 1 & rG x = c%:M.
Proof.
move=> Gx; have [e [[B uB def_x] [_ e1] [-> _] _]] := repr_rsim_diag rG Gx.
rewrite cfRepr1 -[n in n%:R]card_ord -sumr_const -(eq_bigr _ (in1W e1)).
case/normC_sum_eq1=> [i _ | c /eqP norm_c_1 def_e]; first by rewrite e1.
have{def_e} def_e: e = const_mx c by apply/rowP=> i; rewrite mxE def_e ?andbT.
by exists c => //; rewrite def_x def_e diag_const_mx scalar_mxC mulmxKV.
Qed.

Lemma max_cfRepr_mx1 n (rG : mx_representation algCF G n) x :
   x \in G -> cfRepr rG x = cfRepr rG 1%g -> rG x = 1%:M.
Proof.
move=> Gx kerGx; have [|c _ def_x] := @max_cfRepr_norm_scalar n rG x Gx.
  by rewrite kerGx cfRepr1 normr_nat.
move/eqP: kerGx; rewrite cfRepr1 cfunE Gx {rG}def_x mxtrace_scalar.
case: n => [_|n]; first by rewrite ![_%:M]flatmx0.
rewrite mulrb -subr_eq0 -mulrnBl -mulr_natl mulf_eq0 pnatr_eq0 /=.
by rewrite subr_eq0 => /eqP->.
Qed.

Definition irr_constt (B : {set gT}) phi := [pred i | '[phi, 'chi_i]_B != 0].

Lemma irr_consttE i phi : (i \in irr_constt phi) = ('[phi, 'chi_i]_G != 0).
Proof. by []. Qed.

Lemma constt_charP (i : Iirr G) chi :
    chi \is a character ->
  reflect (exists2 chi', chi' \is a character & chi = 'chi_i + chi')
          (i \in irr_constt chi).
Proof.
move=> Nchi; apply: (iffP idP) => [i_in_chi| [chi' Nchi' ->]]; last first.
  rewrite inE /= cfdotDl cfdot_irr eqxx -(eqP (Cnat_cfdot_char_irr i Nchi')).
  by rewrite -natrD pnatr_eq0.
exists (chi - 'chi_i); last by rewrite addrC subrK.
apply/forallP=> j; rewrite coord_cfdot cfdotBl cfdot_irr.
have [<- | _] := eqP; last by rewrite subr0 Cnat_cfdot_char_irr.
have := i_in_chi; rewrite inE /= -(eqP (Cnat_cfdot_char_irr i Nchi)) pnatr_eq0.
by case: (truncC _) => // n _; rewrite mulrSr addrK ?isNatC_nat.
Qed.

Lemma cfun_sum_constt (phi : 'CF(G)) :
  phi = \sum_(i in irr_constt phi) '[phi, 'chi_i] *: 'chi_i.
Proof.
rewrite {1}[phi]cfun_sum_cfdot (bigID [pred i | '[phi, 'chi_i] == 0]) /=.
by rewrite big1 ?add0r // => i /eqP->; rewrite scale0r.
Qed.

Lemma neq0_has_constt (phi : 'CF(G)) :
  phi != 0 -> exists i, i \in irr_constt phi.
Proof.
move=> nz_phi; apply/existsP; apply: contra nz_phi => /pred0P phi0.
by rewrite [phi]cfun_sum_constt big_pred0.
Qed.

Lemma constt_irr i : irr_constt 'chi[G]_i =i pred1 i.
Proof.
by move=> j; rewrite !inE cfdot_irr pnatr_eq0 (eq_sym j); case: (i == j).
Qed.

Lemma char1_ge_constt (i : Iirr G) chi : 
  chi \is a character -> i \in irr_constt chi -> 'chi_i 1%g <= chi 1%g.
Proof.
move=> {chi} _ /constt_charP[// | chi Nchi ->].
by rewrite cfunE addrC -subr_ge0 addrK char1_ge0.
Qed.

Lemma constt_ortho_char (phi psi : 'CF(G)) i j : 
     phi \is a character -> psi \is a character ->
     i \in irr_constt phi -> j \in irr_constt psi ->
  '[phi, psi] = 0 -> '['chi_i, 'chi_j] = 0.
Proof.
move=> _ _ /constt_charP[//|phi1 Nphi1 ->] /constt_charP[//|psi1 Npsi1 ->].
rewrite cfdot_irr; case: eqP => // -> /eqP/idPn[].
rewrite cfdotDl !cfdotDr cfnorm_irr -addrA gtr_eqF ?ltr_paddr ?ltr01 //.
by rewrite Cnat_ge0 ?rpredD ?Cnat_cfdot_char ?irr_char.
Qed.

End IrrConstt.

Arguments irr_constt {gT B%g} phi%CF.

Section Kernel.

Variable (gT : finGroupType) (G : {group gT}).
Implicit Types (phi chi xi : 'CF(G)) (H : {group gT}).

Lemma cfker_repr n (rG : mx_representation algCF G n) : 
  cfker (cfRepr rG) = rker rG.
Proof.
apply/esym/setP=> x; rewrite inE mul1mx /=.
case Gx: (x \in G); last by rewrite inE Gx.
apply/eqP/idP=> Kx; last by rewrite max_cfRepr_mx1 // cfker1.
rewrite inE Gx; apply/forallP=> y; rewrite !cfunE !mulrb groupMl //.
by case: ifP => // Gy; rewrite repr_mxM // Kx mul1mx.
Qed.
  
Lemma cfkerEchar chi :
  chi \is a character -> cfker chi = [set x in G | chi x == chi 1%g].
Proof.
move=> Nchi; apply/setP=> x; apply/idP/setIdP=> [Kx | [Gx /eqP chi_x]].
  by rewrite (subsetP (cfker_sub chi)) // cfker1.
case/char_reprP: Nchi => rG -> in chi_x *; rewrite inE Gx; apply/forallP=> y.
rewrite !cfunE groupMl // !mulrb; case: ifP => // Gy.
by rewrite repr_mxM // max_cfRepr_mx1 ?mul1mx.
Qed.

Lemma cfker_nzcharE chi :
  chi \is a character -> chi != 0 -> cfker chi = [set x | chi x == chi 1%g].
Proof.
move=> Nchi nzchi; apply/setP=> x; rewrite cfkerEchar // !inE andb_idl //.
by apply: contraLR => /cfun0-> //; rewrite eq_sym char1_eq0.
Qed.

Lemma cfkerEirr i : cfker 'chi[G]_i = [set x | 'chi_i x == 'chi_i 1%g].
Proof. by rewrite cfker_nzcharE ?irr_char ?irr_neq0. Qed.

Lemma cfker_irr0 : cfker 'chi[G]_0 = G.
Proof. by rewrite irr0 cfker_cfun1. Qed.

Lemma cfaithful_reg : cfaithful (cfReg G).
Proof.
apply/subsetP=> x; rewrite cfkerEchar ?cfReg_char // !inE !cfRegE eqxx.
by case/andP=> _; apply: contraLR => /negbTE->; rewrite eq_sym neq0CG.
Qed.

Lemma cfkerE chi :
    chi \is a character ->
  cfker chi = G :&: \bigcap_(i in irr_constt chi) cfker 'chi_i.
Proof.
move=> Nchi; rewrite cfkerEchar //; apply/setP=> x; rewrite !inE.
apply: andb_id2l => Gx; rewrite {1 2}[chi]cfun_sum_constt !sum_cfunE.
apply/eqP/bigcapP=> [Kx i Ci | Kx]; last first.
  by apply: eq_bigr => i /Kx Kx_i; rewrite !cfunE cfker1.
rewrite cfkerEirr inE /= -(inj_eq (mulfI Ci)).
have:= (normC_sum_upper _ Kx) i; rewrite !cfunE => -> // {i Ci} i _.
have chi_i_ge0: 0 <= '[chi, 'chi_i].
  by rewrite Cnat_ge0 ?Cnat_cfdot_char_irr.
by rewrite !cfunE normrM (normr_idP _) ?ler_wpmul2l ?char1_ge_norm ?irr_char.
Qed.

Lemma TI_cfker_irr : \bigcap_i cfker 'chi[G]_i = [1].
Proof.
apply/trivgP; apply: subset_trans cfaithful_reg; rewrite cfkerE ?cfReg_char //.
rewrite subsetI (bigcap_min 0) //=; last by rewrite cfker_irr0.
by apply/bigcapsP=> i _; rewrite bigcap_inf.
Qed.

Lemma cfker_constt i chi :
    chi \is a character -> i \in irr_constt chi ->
  cfker chi \subset cfker 'chi[G]_i.
Proof. by move=> Nchi Ci; rewrite cfkerE ?subIset ?(bigcap_min i) ?orbT. Qed.

Section KerLin.

Variable xi : 'CF(G).
Hypothesis lin_xi : xi \is a linear_char.
Let Nxi: xi \is a character. Proof. by have [] := andP lin_xi. Qed.

Lemma lin_char_der1 : G^`(1)%g \subset cfker xi.
Proof.
rewrite gen_subG /=; apply/subsetP=> _ /imset2P[x y Gx Gy ->].
rewrite cfkerEchar // inE groupR //= !lin_charM ?lin_charV ?in_group //.
by rewrite mulrCA mulKf ?mulVf ?lin_char_neq0 // lin_char1.
Qed.

Lemma cforder_lin_char : #[xi]%CF = exponent (G / cfker xi)%g.
Proof.
apply/eqP; rewrite eqn_dvd; apply/andP; split.
  apply/dvdn_cforderP=> x Gx; rewrite -lin_charX // -cfQuoEker ?groupX //.
  rewrite morphX ?(subsetP (cfker_norm xi)) //= expg_exponent ?mem_quotient //.
  by rewrite cfQuo1 ?cfker_normal ?lin_char1.
have abGbar: abelian (G / cfker xi) := sub_der1_abelian lin_char_der1.
have [_ /morphimP[x Nx Gx ->] ->] := exponent_witness (abelian_nil abGbar).
rewrite order_dvdn -morphX //= coset_id cfkerEchar // !inE groupX //=.
by rewrite lin_charX ?lin_char1 // (dvdn_cforderP _ _ _).
Qed.

Lemma cforder_lin_char_dvdG : #[xi]%CF %| #|G|.
Proof.
by rewrite cforder_lin_char (dvdn_trans (exponent_dvdn _)) ?dvdn_morphim.
Qed.

Lemma cforder_lin_char_gt0 : (0 < #[xi]%CF)%N.
Proof. by rewrite cforder_lin_char exponent_gt0. Qed.

End KerLin.

End Kernel.

Section Restrict.

Variable (gT : finGroupType) (G H : {group gT}).

Lemma cfRepr_sub n (rG : mx_representation algCF G n) (sHG : H \subset G) :
  cfRepr (subg_repr rG sHG) = 'Res[H] (cfRepr rG).
Proof.
by apply/cfun_inP => x Hx; rewrite cfResE // !cfunE Hx (subsetP sHG).
Qed.

Lemma cfRes_char chi : chi \is a character -> 'Res[H, G] chi \is a character.
Proof.
have [sHG | not_sHG] := boolP (H \subset G).
  by case/char_reprP=> rG ->; rewrite -(cfRepr_sub rG sHG) cfRepr_char.
by move/Cnat_char1=> Nchi1; rewrite cfResEout // rpredZ_Cnat ?rpred1.
Qed.

Lemma cfRes_eq0 phi : phi \is a character -> ('Res[H, G] phi == 0) = (phi == 0).
Proof. by move=> Nchi; rewrite -!char1_eq0 ?cfRes_char // cfRes1. Qed.

Lemma cfRes_lin_char chi :
  chi \is a linear_char -> 'Res[H, G] chi \is a linear_char.
Proof. by case/andP=> Nchi; rewrite qualifE cfRes_char ?cfRes1. Qed.

Lemma Res_irr_neq0 i : 'Res[H, G] 'chi_i != 0.
Proof. by rewrite cfRes_eq0 ?irr_neq0 ?irr_char. Qed.

Lemma cfRes_lin_lin (chi : 'CF(G)) :
  chi \is a character -> 'Res[H] chi \is a linear_char -> chi \is a linear_char.
Proof. by rewrite !qualifE cfRes1 => -> /andP[]. Qed.

Lemma cfRes_irr_irr chi :
  chi \is a character -> 'Res[H] chi \in irr H -> chi \in irr G.
Proof.
have [sHG /char_reprP[rG ->] | not_sHG Nchi] := boolP (H \subset G).
  rewrite -(cfRepr_sub _ sHG) => /irr_reprP[rH irrH def_rH]; apply/irr_reprP.
  suffices /subg_mx_irr: mx_irreducible (subg_repr rG sHG) by exists rG.
  by apply: mx_rsim_irr irrH; apply/cfRepr_rsimP/eqP.
rewrite cfResEout // => /irrP[j Dchi_j]; apply/lin_char_irr/cfRes_lin_lin=> //.
suffices j0: j = 0 by rewrite cfResEout // Dchi_j j0 irr0 rpred1.
apply: contraNeq (irr1_neq0 j) => nz_j.
have:= xcfun_id j 0; rewrite -Dchi_j cfunE xcfunZl -irr0 xcfun_id eqxx => ->.
by rewrite (negPf nz_j).
Qed.

Definition Res_Iirr (A B : {set gT}) i := cfIirr ('Res[B, A] 'chi_i).

Lemma Res_Iirr0 : Res_Iirr H (0 : Iirr G) = 0.
Proof. by rewrite /Res_Iirr irr0 rmorph1 -irr0 irrK. Qed.

Lemma lin_Res_IirrE i : 'chi[G]_i 1%g = 1 -> 'chi_(Res_Iirr H i) = 'Res 'chi_i.
Proof.
move=> chi1; rewrite cfIirrE ?lin_char_irr ?cfRes_lin_char //.
by rewrite qualifE irr_char /= chi1.
Qed.

End Restrict.

Arguments Res_Iirr {gT A%g} B%g i%R.

Section MoreConstt.

Variables (gT : finGroupType) (G H : {group gT}).

Lemma constt_Ind_Res i j :
  i \in irr_constt ('Ind[G] 'chi_j) =  (j \in irr_constt ('Res[H] 'chi_i)).
Proof. by rewrite !irr_consttE cfdotC conjC_eq0 -cfdot_Res_l. Qed.

Lemma cfdot_Res_ge_constt i j psi :
    psi \is a character -> j \in irr_constt psi -> 
  '['Res[H, G] 'chi_j, 'chi_i] <= '['Res[H] psi, 'chi_i].
Proof.
move=> {psi} _ /constt_charP[// | psi Npsi ->].
rewrite linearD cfdotDl addrC -subr_ge0 addrK Cnat_ge0 //=.
by rewrite Cnat_cfdot_char_irr // cfRes_char.
Qed.

Lemma constt_Res_trans j psi :
    psi \is a character -> j \in irr_constt psi -> 
  {subset irr_constt ('Res[H, G] 'chi_j) <= irr_constt ('Res[H] psi)}.
Proof.
move=> Npsi Cj i; apply: contraNneq; rewrite eqr_le => {1}<-.
rewrite cfdot_Res_ge_constt ?Cnat_ge0 ?Cnat_cfdot_char_irr //.
by rewrite cfRes_char ?irr_char.
Qed.

End MoreConstt.

Section Morphim.

Variables (aT rT : finGroupType) (G D : {group aT}) (f : {morphism D >-> rT}).
Implicit Type chi : 'CF(f @* G).

Lemma cfRepr_morphim n (rfG : mx_representation algCF (f @* G) n) sGD :
  cfRepr (morphim_repr rfG sGD) = cfMorph (cfRepr rfG).
Proof.
apply/cfun_inP=> x Gx; have Dx: x \in D := subsetP sGD x Gx.
by rewrite cfMorphE // !cfunE ?mem_morphim ?Gx.
Qed.

Lemma cfMorph_char chi : chi \is a character -> cfMorph chi \is a character.
Proof.
have [sGD /char_reprP[rfG ->] | outGD Nchi] := boolP (G \subset D); last first.
  by rewrite cfMorphEout // rpredZ_Cnat ?rpred1 ?Cnat_char1.
apply/char_reprP; exists (Representation (morphim_repr rfG sGD)).
by rewrite cfRepr_morphim.
Qed.

Lemma cfMorph_lin_char chi :
  chi \is a linear_char -> cfMorph chi \is a linear_char.
Proof. by case/andP=> Nchi; rewrite qualifE cfMorph1 cfMorph_char. Qed.

Lemma cfMorph_charE chi :
  G \subset D -> (cfMorph chi \is a character) = (chi \is a character).
Proof.
move=> sGD; apply/idP/idP=> [/char_reprP[[n rG] /=Dfchi] | /cfMorph_char//].
pose H := 'ker_G f; have kerH: H \subset rker rG.
  by rewrite -cfker_repr -Dfchi cfker_morph // setIS // ker_sub_pre.
have nHG: G \subset 'N(H) by rewrite normsI // (subset_trans sGD) ?ker_norm.
have [h injh im_h] := first_isom_loc f sGD; rewrite -/H in h injh im_h.
have DfG: invm injh @*^-1 (G / H) == (f @* G)%g by rewrite morphpre_invm im_h.
pose rfG := eqg_repr (morphpre_repr _ (quo_repr kerH nHG)) DfG.
apply/char_reprP; exists (Representation rfG).
apply/cfun_inP=> _ /morphimP[x Dx Gx ->]; rewrite -cfMorphE // Dfchi !cfunE Gx.
pose xH := coset H x; have GxH: xH \in (G / H)%g by apply: mem_quotient.
suffices Dfx: f x = h xH by rewrite mem_morphim //= Dfx invmE ?quo_repr_coset.
by apply/set1_inj; rewrite -?morphim_set1 ?im_h ?(subsetP nHG) ?sub1set.
Qed.

Lemma cfMorph_lin_charE chi :
  G \subset D -> (cfMorph chi \is a linear_char) = (chi \is a linear_char).
Proof. by rewrite qualifE cfMorph1 => /cfMorph_charE->. Qed.

Lemma cfMorph_irr chi :
  G \subset D -> (cfMorph chi \in irr G) = (chi \in irr (f @* G)).
Proof. by move=> sGD; rewrite !irrEchar cfMorph_charE // cfMorph_iso. Qed.

Definition morph_Iirr i := cfIirr (cfMorph 'chi[f @* G]_i).

Lemma morph_Iirr0 : morph_Iirr 0 = 0.
Proof. by rewrite /morph_Iirr irr0 rmorph1 -irr0 irrK. Qed.

Hypothesis sGD : G \subset D.

Lemma morph_IirrE i : 'chi_(morph_Iirr i) = cfMorph 'chi_i.
Proof. by rewrite cfIirrE ?cfMorph_irr ?mem_irr. Qed.

Lemma morph_Iirr_inj : injective morph_Iirr.
Proof.
by move=> i j eq_ij; apply/irr_inj/cfMorph_inj; rewrite // -!morph_IirrE eq_ij.
Qed.

Lemma morph_Iirr_eq0 i : (morph_Iirr i == 0) = (i == 0).
Proof. by rewrite -!irr_eq1 morph_IirrE cfMorph_eq1. Qed.

End Morphim.

Section Isom.

Variables (aT rT : finGroupType) (G : {group aT}) (f : {morphism G >-> rT}).
Variables (R : {group rT}) (isoGR : isom G R f).
Implicit Type chi : 'CF(G).

Lemma cfIsom_char chi :
  (cfIsom isoGR chi \is a character) = (chi \is a character).
Proof.
rewrite [cfIsom _]locked_withE cfMorph_charE //.
by rewrite (isom_im (isom_sym _)) cfRes_id.
Qed.

Lemma cfIsom_lin_char chi :
  (cfIsom isoGR chi \is a linear_char) = (chi \is a linear_char).
Proof. by rewrite qualifE cfIsom_char cfIsom1. Qed.

Lemma cfIsom_irr chi : (cfIsom isoGR chi \in irr R) = (chi \in irr G).
Proof. by rewrite !irrEchar cfIsom_char cfIsom_iso. Qed.

Definition isom_Iirr i := cfIirr (cfIsom isoGR 'chi_i).

Lemma isom_IirrE i : 'chi_(isom_Iirr i) = cfIsom isoGR 'chi_i.
Proof. by rewrite cfIirrE ?cfIsom_irr ?mem_irr. Qed.

Lemma isom_Iirr_inj : injective isom_Iirr.
Proof.
by move=> i j eqij; apply/irr_inj/(cfIsom_inj isoGR); rewrite -!isom_IirrE eqij.
Qed.

Lemma isom_Iirr_eq0 i : (isom_Iirr i == 0) = (i == 0).
Proof. by rewrite -!irr_eq1 isom_IirrE cfIsom_eq1. Qed.

Lemma isom_Iirr0 : isom_Iirr 0 = 0.
Proof. by apply/eqP; rewrite isom_Iirr_eq0. Qed.

End Isom.

Arguments isom_Iirr_inj {aT rT G f R} isoGR [i1 i2] : rename.

Section IsomInv.

Variables (aT rT : finGroupType) (G : {group aT}) (f : {morphism G >-> rT}).
Variables (R : {group rT}) (isoGR : isom G R f).

Lemma isom_IirrK : cancel (isom_Iirr isoGR) (isom_Iirr (isom_sym isoGR)).
Proof. by move=> i; apply: irr_inj; rewrite !isom_IirrE cfIsomK. Qed.

Lemma isom_IirrKV : cancel (isom_Iirr (isom_sym isoGR)) (isom_Iirr isoGR).
Proof. by move=> i; apply: irr_inj; rewrite !isom_IirrE cfIsomKV. Qed.

End IsomInv.

Section Sdprod.

Variables (gT : finGroupType) (K H G : {group gT}).
Hypothesis defG : K ><| H = G.
Let nKG: G \subset 'N(K). Proof. by have [/andP[]] := sdprod_context defG. Qed.

Lemma cfSdprod_char chi :
 (cfSdprod defG chi \is a character) = (chi \is a character).
Proof. by rewrite unlock cfMorph_charE // cfIsom_char. Qed.

Lemma cfSdprod_lin_char chi :
 (cfSdprod defG chi \is a linear_char) = (chi \is a linear_char).
Proof. by rewrite qualifE cfSdprod_char cfSdprod1. Qed.

Lemma cfSdprod_irr chi : (cfSdprod defG chi \in irr G) = (chi \in irr H).
Proof. by rewrite !irrEchar cfSdprod_char cfSdprod_iso. Qed.

Definition sdprod_Iirr j := cfIirr (cfSdprod defG 'chi_j).

Lemma sdprod_IirrE j : 'chi_(sdprod_Iirr j) = cfSdprod defG 'chi_j.
Proof. by rewrite cfIirrE ?cfSdprod_irr ?mem_irr. Qed.

Lemma sdprod_IirrK : cancel sdprod_Iirr (Res_Iirr H).
Proof. by move=> j; rewrite /Res_Iirr sdprod_IirrE cfSdprodK irrK. Qed.

Lemma sdprod_Iirr_inj : injective sdprod_Iirr.
Proof. exact: can_inj sdprod_IirrK. Qed.

Lemma sdprod_Iirr_eq0 i : (sdprod_Iirr i == 0) = (i == 0).
Proof. by rewrite -!irr_eq1 sdprod_IirrE cfSdprod_eq1. Qed.

Lemma sdprod_Iirr0 : sdprod_Iirr 0 = 0.
Proof. by apply/eqP; rewrite sdprod_Iirr_eq0. Qed.

Lemma Res_sdprod_irr phi :
  K \subset cfker phi -> phi \in irr G -> 'Res phi \in irr H.
Proof.
move=> kerK /irrP[i Dphi]; rewrite irrEchar -(cfSdprod_iso defG).
by rewrite cfRes_sdprodK // Dphi cfnorm_irr cfRes_char ?irr_char /=.
Qed.

Lemma sdprod_Res_IirrE i :
  K \subset cfker 'chi[G]_i -> 'chi_(Res_Iirr H i) = 'Res 'chi_i.
Proof. by move=> kerK; rewrite cfIirrE ?Res_sdprod_irr ?mem_irr. Qed.

Lemma sdprod_Res_IirrK i :
  K \subset cfker 'chi_i -> sdprod_Iirr (Res_Iirr H i) = i.
Proof.
by move=> kerK; rewrite /sdprod_Iirr sdprod_Res_IirrE ?cfRes_sdprodK ?irrK.
Qed.

End Sdprod.

Arguments sdprod_Iirr_inj {gT K H G} defG [i1 i2] : rename.

Section DProd.

Variables (gT : finGroupType) (G K H : {group gT}).
Hypothesis KxH : K \x H = G.

Lemma cfDprodKl_abelian j : abelian H -> cancel ((cfDprod KxH)^~ 'chi_j) 'Res.
Proof. by move=> cHH; apply: cfDprodKl; apply/lin_char1/char_abelianP. Qed.

Lemma cfDprodKr_abelian i : abelian K -> cancel (cfDprod KxH 'chi_i) 'Res.
Proof. by move=> cKK; apply: cfDprodKr; apply/lin_char1/char_abelianP. Qed.

Lemma cfDprodl_char phi :
  (cfDprodl KxH phi \is a character) = (phi \is a character).
Proof. exact: cfSdprod_char. Qed.

Lemma cfDprodr_char psi :
  (cfDprodr KxH psi \is a character) = (psi \is a character).
Proof. exact: cfSdprod_char. Qed.

Lemma cfDprod_char phi psi :
     phi \is a character -> psi \is a character ->
  cfDprod KxH phi psi \is a character.
Proof. by move=> Nphi Npsi; rewrite rpredM ?cfDprodl_char ?cfDprodr_char. Qed.

Lemma cfDprod_eq1 phi psi :
    phi \is a character -> psi \is a character ->
  (cfDprod KxH phi psi == 1) = (phi == 1) && (psi == 1).
Proof.
move=> /Cnat_char1 Nphi /Cnat_char1 Npsi.
apply/eqP/andP=> [phi_psi_1 | [/eqP-> /eqP->]]; last by rewrite cfDprod_cfun1.
have /andP[/eqP phi1 /eqP psi1]: (phi 1%g == 1) && (psi 1%g == 1).
  by rewrite -Cnat_mul_eq1 // -(cfDprod1 KxH) phi_psi_1 cfun11.
rewrite -[phi](cfDprodKl KxH psi1) -{2}[psi](cfDprodKr KxH phi1) phi_psi_1.
by rewrite !rmorph1.
Qed.

Lemma cfDprodl_lin_char phi :
  (cfDprodl KxH phi \is a linear_char) = (phi \is a linear_char).
Proof. exact: cfSdprod_lin_char. Qed.

Lemma cfDprodr_lin_char psi :
  (cfDprodr KxH psi \is a linear_char) = (psi \is a linear_char).
Proof. exact: cfSdprod_lin_char. Qed.

Lemma cfDprod_lin_char phi psi :
     phi \is a linear_char -> psi \is a linear_char ->
  cfDprod KxH phi psi \is a linear_char.
Proof. by move=> Nphi Npsi; rewrite rpredM ?cfSdprod_lin_char. Qed.

Lemma cfDprodl_irr chi : (cfDprodl KxH chi \in irr G) = (chi \in irr K).
Proof. exact: cfSdprod_irr. Qed.

Lemma cfDprodr_irr chi : (cfDprodr  KxH chi \in irr G) = (chi \in irr H).
Proof. exact: cfSdprod_irr. Qed.

Definition dprodl_Iirr i := cfIirr (cfDprodl KxH 'chi_i).

Lemma dprodl_IirrE i : 'chi_(dprodl_Iirr i) = cfDprodl KxH 'chi_i.
Proof. exact: sdprod_IirrE. Qed.
Lemma dprodl_IirrK : cancel dprodl_Iirr (Res_Iirr K).
Proof. exact: sdprod_IirrK. Qed.
Lemma dprodl_Iirr_eq0 i : (dprodl_Iirr i == 0) = (i == 0).
Proof. exact: sdprod_Iirr_eq0. Qed.
Lemma dprodl_Iirr0 : dprodl_Iirr 0 = 0.
Proof. exact: sdprod_Iirr0. Qed.

Definition dprodr_Iirr j := cfIirr (cfDprodr KxH 'chi_j).

Lemma dprodr_IirrE j : 'chi_(dprodr_Iirr j) = cfDprodr KxH 'chi_j.
Proof. exact: sdprod_IirrE. Qed.
Lemma dprodr_IirrK : cancel dprodr_Iirr (Res_Iirr H).
Proof. exact: sdprod_IirrK. Qed.
Lemma dprodr_Iirr_eq0 j : (dprodr_Iirr j == 0) = (j == 0).
Proof. exact: sdprod_Iirr_eq0. Qed.
Lemma dprodr_Iirr0 : dprodr_Iirr 0 = 0.
Proof. exact: sdprod_Iirr0. Qed.

Lemma cfDprod_irr i j : cfDprod KxH 'chi_i 'chi_j \in irr G.
Proof.
rewrite irrEchar cfDprod_char ?irr_char //=.
by rewrite cfdot_dprod !cfdot_irr !eqxx mul1r.
Qed.

Definition dprod_Iirr ij := cfIirr (cfDprod KxH 'chi_ij.1 'chi_ij.2).

Lemma dprod_IirrE i j : 'chi_(dprod_Iirr (i, j)) = cfDprod KxH 'chi_i 'chi_j.
Proof. by rewrite cfIirrE ?cfDprod_irr. Qed.

Lemma dprod_IirrEl i : 'chi_(dprod_Iirr (i, 0)) = cfDprodl KxH 'chi_i.
Proof. by rewrite dprod_IirrE /cfDprod irr0 rmorph1 mulr1. Qed.

Lemma dprod_IirrEr j : 'chi_(dprod_Iirr (0, j)) = cfDprodr KxH 'chi_j.
Proof. by rewrite dprod_IirrE /cfDprod irr0 rmorph1 mul1r. Qed.

Lemma dprod_Iirr_inj : injective dprod_Iirr.
Proof.
move=> [i1 j1] [i2 j2] /eqP; rewrite -[_ == _]oddb -(natCK (_ == _)).
rewrite -cfdot_irr !dprod_IirrE cfdot_dprod !cfdot_irr -natrM mulnb.
by rewrite natCK oddb -xpair_eqE => /eqP.
Qed.

Lemma dprod_Iirr0 : dprod_Iirr (0, 0) = 0.
Proof. by apply/irr_inj; rewrite dprod_IirrE !irr0 cfDprod_cfun1. Qed.

Lemma dprod_Iirr0l j : dprod_Iirr (0, j) = dprodr_Iirr j.
Proof.
by apply/irr_inj; rewrite dprod_IirrE irr0 dprodr_IirrE cfDprod_cfun1l.
Qed.

Lemma dprod_Iirr0r i : dprod_Iirr (i, 0) = dprodl_Iirr i.
Proof.
by apply/irr_inj; rewrite dprod_IirrE irr0 dprodl_IirrE cfDprod_cfun1r.
Qed.

Lemma dprod_Iirr_eq0 i j : (dprod_Iirr (i, j) == 0) = (i == 0) && (j == 0).
Proof. by rewrite -xpair_eqE -(inj_eq dprod_Iirr_inj) dprod_Iirr0. Qed.

Lemma cfdot_dprod_irr i1 i2 j1 j2 :
  '['chi_(dprod_Iirr (i1, j1)), 'chi_(dprod_Iirr (i2, j2))]
     = ((i1 == i2) && (j1 == j2))%:R.
Proof. by rewrite cfdot_irr (inj_eq dprod_Iirr_inj). Qed.

Lemma dprod_Iirr_onto k : k \in codom dprod_Iirr.
Proof.
set D := codom _; have Df: dprod_Iirr _ \in D := codom_f dprod_Iirr _.
have: 'chi_k 1%g ^+ 2 != 0 by rewrite mulf_neq0 ?irr1_neq0.
apply: contraR => notDk; move/eqP: (irr_sum_square G).
rewrite (bigID (mem D)) (reindex _ (bij_on_codom dprod_Iirr_inj (0, 0))) /=.
have ->: #|G|%:R = \sum_i \sum_j 'chi_(dprod_Iirr (i, j)) 1%g ^+ 2.
  rewrite -(dprod_card KxH) natrM.
  do 2![rewrite -irr_sum_square (mulr_suml, mulr_sumr); apply: eq_bigr => ? _].
  by rewrite dprod_IirrE -exprMn -{3}(mulg1 1%g) cfDprodE.
rewrite (eq_bigl _ _ Df) pair_bigA addrC -subr_eq0 addrK.
by move/eqP/psumr_eq0P=> -> //= i _; rewrite irr1_degree -natrX ler0n.
Qed.

Definition inv_dprod_Iirr i := iinv (dprod_Iirr_onto i).

Lemma dprod_IirrK : cancel dprod_Iirr inv_dprod_Iirr.
Proof. by move=> p; apply: (iinv_f dprod_Iirr_inj). Qed.

Lemma inv_dprod_IirrK : cancel inv_dprod_Iirr dprod_Iirr.
Proof. by move=> i; apply: f_iinv. Qed.

Lemma inv_dprod_Iirr0 : inv_dprod_Iirr 0 = (0, 0).
Proof. by apply/(canLR dprod_IirrK); rewrite dprod_Iirr0. Qed.

End DProd.

Arguments dprod_Iirr_inj {gT G K H} KxH [i1 i2] : rename.

Lemma dprod_IirrC (gT : finGroupType) (G K H : {group gT})
                  (KxH : K \x H = G) (HxK : H \x K = G) i j :
  dprod_Iirr KxH (i, j) = dprod_Iirr HxK (j, i).
Proof. by apply: irr_inj; rewrite !dprod_IirrE; apply: cfDprodC. Qed.

Section BigDprod.

Variables (gT : finGroupType) (I : finType) (P : pred I).
Variables (A : I -> {group gT}) (G : {group gT}).
Hypothesis defG : \big[dprod/1%g]_(i | P i) A i = G.

Let sAG i : P i -> A i \subset G.
Proof. by move=> Pi; rewrite -(bigdprodWY defG) (bigD1 i) ?joing_subl. Qed.

Lemma cfBigdprodi_char i (phi : 'CF(A i)) :
  phi \is a character -> cfBigdprodi defG phi \is a character.
Proof. by move=> Nphi; rewrite cfDprodl_char cfRes_char. Qed.

Lemma cfBigdprodi_charE i (phi : 'CF(A i)) :
  P i -> (cfBigdprodi defG phi \is a character) = (phi \is a character).
Proof. by move=> Pi; rewrite cfDprodl_char Pi cfRes_id. Qed.

Lemma cfBigdprod_char phi :
    (forall i, P i -> phi i \is a character) ->
  cfBigdprod defG phi \is a character.
Proof.
by move=> Nphi; apply: rpred_prod => i /Nphi; apply: cfBigdprodi_char.
Qed.

Lemma cfBigdprodi_lin_char i (phi : 'CF(A i)) :
  phi \is a linear_char -> cfBigdprodi defG phi \is a linear_char.
Proof. by move=> Lphi; rewrite cfDprodl_lin_char ?cfRes_lin_char. Qed.

Lemma cfBigdprodi_lin_charE i (phi : 'CF(A i)) :
  P i -> (cfBigdprodi defG phi \is a linear_char) = (phi \is a linear_char).
Proof. by move=> Pi; rewrite qualifE cfBigdprodi_charE // cfBigdprodi1. Qed.

Lemma cfBigdprod_lin_char phi :
    (forall i, P i -> phi i \is a linear_char) ->
  cfBigdprod defG phi \is a linear_char.
Proof.
by move=> Lphi; apply/rpred_prod=> i /Lphi; apply: cfBigdprodi_lin_char.
Qed.

Lemma cfBigdprodi_irr i chi :
  P i -> (cfBigdprodi defG chi \in irr G) = (chi \in irr (A i)).
Proof. by move=> Pi; rewrite !irrEchar cfBigdprodi_charE ?cfBigdprodi_iso. Qed.

Lemma cfBigdprod_irr chi :
  (forall i, P i -> chi i \in irr (A i)) -> cfBigdprod defG chi \in irr G.
Proof.
move=> Nchi; rewrite irrEchar cfBigdprod_char => [|i /Nchi/irrWchar] //=.
by rewrite cfdot_bigdprod big1 // => i /Nchi/irrWnorm.
Qed.

Lemma cfBigdprod_eq1 phi :
    (forall i, P i -> phi i \is a character) ->
  (cfBigdprod defG phi == 1) = [forall (i | P i), phi i == 1].
Proof.
move=> Nphi; set Phi := cfBigdprod defG phi.
apply/eqP/eqfun_inP=> [Phi1 i Pi | phi1]; last first.
  by apply: big1 => i /phi1->; rewrite rmorph1.
have Phi1_1: Phi 1%g = 1 by rewrite Phi1 cfun1E group1.
have nz_Phi1: Phi 1%g != 0 by rewrite Phi1_1 oner_eq0.
have [_ <-] := cfBigdprodK nz_Phi1 Pi.
rewrite Phi1_1 divr1 -/Phi Phi1 rmorph1.
rewrite prod_cfunE // in Phi1_1; have := Cnat_prod_eq1 _ Phi1_1 Pi.
rewrite -(cfRes1 (A i)) cfBigdprodiK // => ->; first by rewrite scale1r.
by move=> {i Pi} j /Nphi Nphi_j; rewrite Cnat_char1 ?cfBigdprodi_char.
Qed.

Lemma cfBigdprod_Res_lin chi :
  chi \is a linear_char -> cfBigdprod defG (fun i => 'Res[A i] chi) = chi.
Proof.
move=> Lchi; apply/cfun_inP=> _ /(mem_bigdprod defG)[x [Ax -> _]].
rewrite (lin_char_prod Lchi) ?cfBigdprodE // => [|i Pi]; last first.
  by rewrite (subsetP (sAG Pi)) ?Ax.
by apply/eq_bigr=> i Pi; rewrite cfResE ?sAG ?Ax.
Qed.

Lemma cfBigdprodKlin phi :
  (forall i, P i -> phi i \is a linear_char) ->
  forall i, P i -> 'Res (cfBigdprod defG phi) = phi i.
Proof.
move=> Lphi i Pi; have Lpsi := cfBigdprod_lin_char Lphi.
have [_ <-] := cfBigdprodK (lin_char_neq0 Lpsi (group1 G)) Pi.
by rewrite !lin_char1 ?Lphi // divr1 scale1r.
Qed.

Lemma cfBigdprodKabelian Iphi (phi := fun i => 'chi_(Iphi i)) :
  abelian G -> forall i, P i -> 'Res (cfBigdprod defG phi) = 'chi_(Iphi i).
Proof.
move=> /(abelianS _) cGG.
by apply: cfBigdprodKlin => i /sAG/cGG/char_abelianP->.
Qed.

End BigDprod.

Section Aut.

Variables (gT : finGroupType) (G : {group gT}).
Implicit Type u : {rmorphism algC -> algC}.

Lemma conjC_charAut u (chi : 'CF(G)) x :
  chi \is a character -> (u (chi x))^* = u (chi x)^*.
Proof.
have [Gx | /cfun0->] := boolP (x \in G); last by rewrite !rmorph0.
case/char_reprP=> rG ->; have [e [_ [en1 _] [-> _] _]] := repr_rsim_diag rG Gx.
by rewrite !rmorph_sum; apply: eq_bigr => i _; apply: aut_unity_rootC (en1 i).
Qed.

Lemma conjC_irrAut u i x : (u ('chi[G]_i x))^* = u ('chi_i x)^*.
Proof. exact: conjC_charAut (irr_char i). Qed.

Lemma cfdot_aut_char u (phi chi : 'CF(G)) : 
  chi \is a character -> '[cfAut u phi, cfAut u chi] = u '[phi, chi].
Proof. by move/conjC_charAut=> Nchi; apply: cfdot_cfAut => _ /mapP[x _ ->]. Qed.

Lemma cfdot_aut_irr u phi i :
  '[cfAut u phi, cfAut u 'chi[G]_i] = u '[phi, 'chi_i].
Proof. exact: cfdot_aut_char (irr_char i). Qed.

Lemma cfAut_irr u chi : (cfAut u chi \in irr G) = (chi \in irr G).
Proof.
rewrite !irrEchar cfAut_char; apply/andb_id2l=> /cfdot_aut_char->.
exact: fmorph_eq1.
Qed.

Lemma cfConjC_irr i : (('chi_i)^*)%CF \in irr G.
Proof. by rewrite cfAut_irr mem_irr. Qed.

Lemma irr_aut_closed u : cfAut_closed u (irr G).
Proof. by move=> chi; rewrite /= cfAut_irr. Qed.

Definition aut_Iirr u i := cfIirr (cfAut u 'chi[G]_i).

Lemma aut_IirrE u i : 'chi_(aut_Iirr u i) = cfAut u 'chi_i.
Proof. by rewrite cfIirrE ?cfAut_irr ?mem_irr. Qed.

Definition conjC_Iirr := aut_Iirr conjC.

Lemma conjC_IirrE i : 'chi[G]_(conjC_Iirr i) = ('chi_i)^*%CF.
Proof. exact: aut_IirrE. Qed.

Lemma conjC_IirrK : involutive conjC_Iirr.
Proof. by move=> i; apply: irr_inj; rewrite !conjC_IirrE cfConjCK. Qed.

Lemma aut_Iirr0 u : aut_Iirr u 0 = 0 :> Iirr G.
Proof. by apply/irr_inj; rewrite aut_IirrE irr0 cfAut_cfun1. Qed.

Lemma conjC_Iirr0 : conjC_Iirr 0 = 0 :> Iirr G.
Proof. exact: aut_Iirr0. Qed.

Lemma aut_Iirr_eq0 u i : (aut_Iirr u i == 0) = (i == 0).
Proof. by rewrite -!irr_eq1 aut_IirrE cfAut_eq1. Qed.

Lemma conjC_Iirr_eq0 i : (conjC_Iirr i == 0 :> Iirr G) = (i == 0).
Proof. exact: aut_Iirr_eq0. Qed.

Lemma aut_Iirr_inj u : injective (aut_Iirr u).
Proof.
by move=> i j eq_ij; apply/irr_inj/(cfAut_inj u); rewrite -!aut_IirrE eq_ij.
Qed.

End Aut.

Arguments aut_Iirr_inj {gT G} u [i1 i2] : rename.
Arguments conjC_IirrK {gT G} i : rename.

Section Coset.

Variable (gT : finGroupType).

Implicit Types G H : {group gT}.

Lemma cfQuo_char G H (chi : 'CF(G)) :
  chi \is a character -> (chi / H)%CF \is a character.
Proof.
move=> Nchi; without loss kerH: / H \subset cfker chi.
  move/contraNF=> IHchi; apply/wlog_neg=> N'chiH.
  suffices ->: (chi / H)%CF = (chi 1%g)%:A.
    by rewrite rpredZ_Cnat ?Cnat_char1 ?rpred1.
  by apply/cfunP=> x; rewrite cfunE cfun1E mulr_natr cfunElock IHchi.
without loss nsHG: G chi Nchi kerH / H <| G.
  move=> IHchi; have nsHN := normalSG (subset_trans kerH (cfker_sub chi)).
  by rewrite cfQuoInorm ?(cfRes_char, IHchi) ?sub_cfker_Res // ?normal_sub.
have [rG Dchi] := char_reprP Nchi; rewrite Dchi cfker_repr in kerH.
apply/char_reprP; exists (Representation (quo_repr kerH (normal_norm nsHG))).
apply/cfun_inP=> _ /morphimP[x nHx Gx ->]; rewrite Dchi cfQuoE ?cfker_repr //=.
by rewrite !cfunE Gx quo_repr_coset ?mem_quotient.
Qed.

Lemma cfQuo_lin_char G H (chi : 'CF(G)) :
  chi \is a linear_char -> (chi / H)%CF \is a linear_char.
Proof. by case/andP=> Nchi; rewrite qualifE cfQuo_char ?cfQuo1. Qed.

Lemma cfMod_char G H (chi : 'CF(G / H)) :
  chi \is a character -> (chi %% H)%CF \is a character.
Proof. exact: cfMorph_char. Qed.

Lemma cfMod_lin_char G H (chi : 'CF(G / H)) :
  chi \is a linear_char -> (chi %% H)%CF \is a linear_char.
Proof. exact: cfMorph_lin_char. Qed.

Lemma cfMod_charE G H (chi : 'CF(G / H)) :
  H <| G -> (chi %% H \is a character)%CF = (chi \is a character).
Proof. by case/andP=> _; apply: cfMorph_charE. Qed.

Lemma cfMod_lin_charE G H (chi : 'CF(G / H)) :
  H <| G -> (chi %% H \is a linear_char)%CF = (chi \is a linear_char).
Proof. by case/andP=> _; apply: cfMorph_lin_charE. Qed.

Lemma cfQuo_charE G H (chi : 'CF(G)) :
   H <| G -> H \subset cfker chi ->
 (chi / H \is a character)%CF = (chi \is a character).
Proof. by move=> nsHG kerH; rewrite -cfMod_charE ?cfQuoK. Qed.

Lemma cfQuo_lin_charE G H (chi : 'CF(G)) :
   H <| G -> H \subset cfker chi ->
 (chi / H \is a linear_char)%CF = (chi \is a linear_char).
Proof. by move=> nsHG kerH; rewrite -cfMod_lin_charE ?cfQuoK. Qed.

Lemma cfMod_irr G H chi :
  H <| G -> (chi %% H \in irr G)%CF = (chi \in irr (G / H)).
Proof. by case/andP=> _; apply: cfMorph_irr. Qed.

Definition mod_Iirr G H i := cfIirr ('chi[G / H]_i %% H)%CF.

Lemma mod_Iirr0 G H : mod_Iirr (0 : Iirr (G / H)) = 0.
Proof. exact: morph_Iirr0. Qed.

Lemma mod_IirrE G H i : H <| G -> 'chi_(mod_Iirr i) = ('chi[G / H]_i %% H)%CF.
Proof. by move=> nsHG; rewrite cfIirrE ?cfMod_irr ?mem_irr. Qed.

Lemma mod_Iirr_eq0 G H i :
  H <| G -> (mod_Iirr i == 0) = (i == 0 :> Iirr (G / H)).
Proof. by case/andP=> _ /morph_Iirr_eq0->. Qed.

Lemma cfQuo_irr G H chi :
     H <| G -> H \subset cfker chi ->
  ((chi / H)%CF \in irr (G / H)) = (chi \in irr G).
Proof. by move=> nsHG kerH; rewrite -cfMod_irr ?cfQuoK. Qed.

Definition quo_Iirr G H i := cfIirr ('chi[G]_i / H)%CF.

Lemma quo_Iirr0 G H : quo_Iirr H (0 : Iirr G) = 0.
Proof. by rewrite /quo_Iirr irr0 cfQuo_cfun1 -irr0 irrK. Qed.

Lemma quo_IirrE G H i :
  H <| G -> H \subset cfker 'chi[G]_i -> 'chi_(quo_Iirr H i) = ('chi_i / H)%CF.
Proof. by move=> nsHG kerH; rewrite cfIirrE ?cfQuo_irr ?mem_irr. Qed.

Lemma quo_Iirr_eq0 G H i :
  H <| G -> H \subset cfker 'chi[G]_i -> (quo_Iirr H i == 0) = (i == 0).
Proof. by move=> nsHG kerH; rewrite -!irr_eq1 quo_IirrE ?cfQuo_eq1. Qed.

Lemma mod_IirrK G H : H <| G -> cancel (@mod_Iirr G H) (@quo_Iirr G H).
Proof.
move=> nsHG i; apply: irr_inj.
by rewrite quo_IirrE ?mod_IirrE ?cfker_mod // cfModK.
Qed.

Lemma quo_IirrK G H i :
  H <| G -> H \subset cfker 'chi[G]_i -> mod_Iirr (quo_Iirr H i) = i.
Proof.
by move=> nsHG kerH; apply: irr_inj; rewrite mod_IirrE ?quo_IirrE ?cfQuoK.
Qed.

Lemma quo_IirrKeq G H :
    H <| G ->
  forall i, (mod_Iirr (quo_Iirr H i) == i) = (H \subset cfker 'chi[G]_i).
Proof.
move=> nsHG i; apply/eqP/idP=> [<- | ]; last exact: quo_IirrK.
by rewrite mod_IirrE ?cfker_mod.
Qed.

Lemma mod_Iirr_bij H G :
  H <| G -> {on [pred i | H \subset cfker 'chi_i], bijective (@mod_Iirr G H)}.
Proof.
by exists (quo_Iirr H) => [i _ | i]; [apply: mod_IirrK | apply: quo_IirrK].
Qed.

Lemma sum_norm_irr_quo H G x :
    x \in G ->  H <| G ->
  \sum_i `|'chi[G / H]_i (coset H x)| ^+ 2
    = \sum_(i | H \subset cfker 'chi_i) `|'chi[G]_i x| ^+ 2.
Proof.
move=> Gx nsHG; rewrite (reindex _ (mod_Iirr_bij nsHG)) /=.
by apply/esym/eq_big=> [i | i _]; rewrite mod_IirrE ?cfker_mod ?cfModE.
Qed.

Lemma cap_cfker_normal G H :
  H <| G -> \bigcap_(i | H \subset cfker 'chi[G]_i) (cfker 'chi_i) = H.
Proof.
move=> nsHG; have [sHG nHG] := andP nsHG; set lhs := \bigcap_(i | _) _.
have nHlhs: lhs \subset 'N(H) by rewrite (bigcap_min 0) ?cfker_irr0.
apply/esym/eqP; rewrite eqEsubset (introT bigcapsP) //= -quotient_sub1 //.
rewrite -(TI_cfker_irr (G / H)); apply/bigcapsP=> i _.
rewrite sub_quotient_pre // (bigcap_min (mod_Iirr i)) ?mod_IirrE ?cfker_mod //.
by rewrite cfker_morph ?subsetIr.
Qed.

Lemma cfker_reg_quo G H : H <| G -> cfker (cfReg (G / H)%g %% H) = H.
Proof.
move=> nsHG; have [sHG nHG] := andP nsHG.
apply/setP=> x; rewrite cfkerEchar ?cfMod_char ?cfReg_char //.
rewrite -[in RHS in _ = RHS](setIidPr sHG) !inE; apply: andb_id2l => Gx.
rewrite !cfModE // !cfRegE // morph1 eqxx.
rewrite (sameP eqP (kerP _ (subsetP nHG x Gx))) ker_coset.
by rewrite -!mulrnA eqr_nat eqn_pmul2l ?cardG_gt0 // (can_eq oddb) eqb_id.
Qed.

End Coset.

Section DerivedGroup.

Variable gT : finGroupType.
Implicit Types G H : {group gT}.

Lemma lin_irr_der1 G i :
   ('chi_i \is a linear_char) = (G^`(1)%g \subset cfker 'chi[G]_i).
Proof.
apply/idP/idP=> [|sG'K]; first by apply: lin_char_der1.
have nsG'G: G^`(1) <| G := der_normal 1 G.
rewrite qualifE irr_char -[i](quo_IirrK nsG'G) // mod_IirrE //=.
by rewrite cfModE // morph1 lin_char1 //; apply/char_abelianP/der_abelian.
Qed.

Lemma subGcfker G i : (G \subset cfker 'chi[G]_i) = (i == 0).
Proof.
rewrite -irr_eq1; apply/idP/eqP=> [chiG1 | ->]; last by rewrite cfker_cfun1.
apply/cfun_inP=> x Gx; rewrite cfun1E Gx cfker1 ?(subsetP chiG1) ?lin_char1 //.
by rewrite lin_irr_der1 (subset_trans (der_sub 1 G)).
Qed.

Lemma irr_prime_injP G i :
  prime #|G| -> reflect {in G &, injective 'chi[G]_i} (i != 0).
Proof.
move=> pr_G; apply: (iffP idP) => [nz_i | inj_chi].
  apply: fful_lin_char_inj (irr_prime_lin i pr_G) _.
  by rewrite cfaithfulE -(setIidPr (cfker_sub _)) prime_TIg // subGcfker.
have /trivgPn[x Gx ntx]: G :!=: 1%g by rewrite -cardG_gt1 prime_gt1.
apply: contraNneq ntx => i0; apply/eqP/inj_chi=> //.
by rewrite i0 irr0 !cfun1E Gx group1.
Qed.

(* This is Isaacs (2.23)(a). *) 
Lemma cap_cfker_lin_irr G :
  \bigcap_(i | 'chi[G]_i \is a linear_char) (cfker 'chi_i) = G^`(1)%g.
Proof.
rewrite -(cap_cfker_normal (der_normal 1 G)).
by apply: eq_bigl => i; rewrite lin_irr_der1.
Qed.

(* This is Isaacs (2.23)(b) *)
Lemma card_lin_irr G :
  #|[pred i | 'chi[G]_i \is a linear_char]| = #|G : G^`(1)%g|.
Proof.
have nsG'G := der_normal 1 G; rewrite (eq_card (@lin_irr_der1 G)).
rewrite -(on_card_preimset (mod_Iirr_bij nsG'G)).
rewrite -card_quotient ?normal_norm //.
move: (der_abelian 0 G); rewrite card_classes_abelian; move/eqP<-.
rewrite -NirrE -[X in _ = X]card_ord.
by apply: eq_card => i; rewrite !inE mod_IirrE ?cfker_mod.
(* Alternative: use the equivalent result in modular representation theory
transitivity #|@socle_of_Iirr _ G @^-1: linear_irr _|; last first.
  rewrite (on_card_preimset (socle_of_Iirr_bij _)).
  by rewrite card_linear_irr ?algC'G; last apply: groupC.
by apply: eq_card => i; rewrite !inE /lin_char irr_char irr1_degree -eqC_nat.
*)
Qed.

(* A non-trivial solvable group has a nonprincipal linear character. *)
Lemma solvable_has_lin_char G :
    G :!=: 1%g -> solvable G ->
  exists2 i, 'chi[G]_i \is a linear_char & 'chi_i != 1.
Proof.
move=> ntG solG.
suff /subsetPn[i]: ~~ ([pred i | 'chi[G]_i \is a linear_char] \subset pred1 0).
  by rewrite !inE -(inj_eq irr_inj) irr0; exists i.
rewrite (contra (@subset_leq_card _ _ _)) // -ltnNge card1 card_lin_irr.
by rewrite indexg_gt1 proper_subn // (sol_der1_proper solG).
Qed.

(* A combinatorial group isommorphic to the linear characters. *)
Lemma lin_char_group G :
  {linG : finGroupType & {cF : linG -> 'CF(G) | 
         [/\ injective cF, #|linG| = #|G : G^`(1)|,
             forall u, cF u \is a linear_char
           & forall phi, phi \is a linear_char -> exists u, phi = cF u]
       & [/\ cF 1%g = 1%R,
             {morph cF : u v / (u * v)%g >-> (u * v)%R},
             forall k, {morph cF : u / (u^+ k)%g >-> u ^+ k},
             {morph cF: u / u^-1%g >-> u^-1%CF}
           & {mono cF: u / #[u]%g >-> #[u]%CF} ]}}.
Proof.
pose linT := {i : Iirr G | 'chi_i \is a linear_char}.
pose cF (u : linT) := 'chi_(sval u).
have cFlin u: cF u \is a linear_char := svalP u.
have cFinj: injective cF := inj_comp irr_inj val_inj.
have inT xi : xi \is a linear_char -> {u | cF u = xi}.
  move=> lin_xi; have /irrP/sig_eqW[i Dxi] := lin_char_irr lin_xi.
  by apply: (exist _ (Sub i _)) => //; rewrite -Dxi.
have [one cFone] := inT 1 (rpred1 _).
pose inv u := sval (inT _ (rpredVr (cFlin u))).
pose mul u v := sval (inT _ (rpredM (cFlin u) (cFlin v))).
have cFmul u v: cF (mul u v) = cF u * cF v := svalP (inT _ _).
have cFinv u: cF (inv u) = (cF u)^-1 := svalP (inT _ _).
have mulA: associative mul by move=> u v w; apply: cFinj; rewrite !cFmul mulrA.
have mul1: left_id one mul by move=> u; apply: cFinj; rewrite cFmul cFone mul1r.
have mulV: left_inverse one inv mul.
  by move=> u; apply: cFinj; rewrite cFmul cFinv cFone mulVr ?lin_char_unitr.
pose linGm := FinGroup.Mixin mulA mul1 mulV.
pose linG := @FinGroupType (BaseFinGroupType linT linGm) mulV.
have cFexp k: {morph cF : u / ((u : linG) ^+ k)%g >-> u ^+ k}.
  by move=> u; elim: k => // k IHk; rewrite expgS exprS cFmul IHk.
do [exists linG, cF; split=> //] => [|xi /inT[u <-]|u]; first 2 [by exists u].
  have inj_cFI: injective (cfIirr \o cF).
    apply: can_inj (insubd one) _ => u; apply: val_inj.
    by rewrite insubdK /= ?irrK //; apply: cFlin.
  rewrite -(card_image inj_cFI) -card_lin_irr.
  apply/eq_card=> i; rewrite inE; apply/codomP/idP=> [[u ->] | /inT[u Du]].
    by rewrite /= irrK; apply: cFlin.
  by exists u; apply: irr_inj; rewrite /= irrK.
apply/eqP; rewrite eqn_dvd; apply/andP; split.
  by rewrite dvdn_cforder; rewrite -cFexp expg_order cFone.
by rewrite order_dvdn -(inj_eq cFinj) cFone cFexp exp_cforder.
Qed.

Lemma cfExp_prime_transitive G (i j : Iirr G) :
    prime #|G| -> i != 0 -> j != 0 ->
  exists2 k, coprime k #['chi_i]%CF & 'chi_j = 'chi_i ^+ k.
Proof.
set p := #|G| => pr_p nz_i nz_j; have cycG := prime_cyclic pr_p.
have [L [h [injh oL Lh h_ontoL]] [h1 hM hX _ o_h]] := lin_char_group G.
rewrite (derG1P (cyclic_abelian cycG)) indexg1 -/p in oL.
have /fin_all_exists[h' h'K] := h_ontoL _ (irr_cyclic_lin _ cycG).
have o_h' k: k != 0 -> #[h' k] = p.
  rewrite -cforder_irr_eq1 h'K -o_h => nt_h'k.
  by apply/prime_nt_dvdP=> //; rewrite cforder_lin_char_dvdG.
have{oL} genL k: k != 0 -> generator [set: L] (h' k).
  move=> /o_h' o_h'k; rewrite /generator eq_sym eqEcard subsetT /=.
  by rewrite cardsT oL -o_h'k.
have [/(_ =P <[_]>)-> gen_j] := (genL i nz_i, genL j nz_j).
have /cycleP[k Dj] := cycle_generator gen_j.
by rewrite !h'K Dj o_h hX generator_coprime coprime_sym in gen_j *; exists k.
Qed.

(* This is Isaacs (2.24). *)
Lemma card_subcent1_coset G H x : 
  x \in G -> H <| G -> (#|'C_(G / H)[coset H x]| <= #|'C_G[x]|)%N.
Proof.
move=> Gx nsHG; rewrite -leC_nat.
move: (second_orthogonality_relation x Gx); rewrite mulrb class_refl => <-.
have GHx: coset H x \in (G / H)%g by apply: mem_quotient.
move: (second_orthogonality_relation (coset H x) GHx).
rewrite mulrb class_refl => <-.
rewrite -2!(eq_bigr _ (fun _ _ => normCK _)) sum_norm_irr_quo // -subr_ge0.
rewrite (bigID (fun i => H \subset cfker 'chi[G]_i)) //= addrC addKr.
by apply: sumr_ge0 => i _; rewrite normCK mul_conjC_ge0.
Qed.

End DerivedGroup.

Arguments irr_prime_injP {gT G i}.

(* Determinant characters and determinential order. *)
Section DetOrder.

Variables (gT : finGroupType) (G : {group gT}).

Section DetRepr.

Variables (n : nat) (rG : mx_representation [fieldType of algC] G n).

Definition det_repr_mx x : 'M_1 := (\det (rG x))%:M.

Fact det_is_repr : mx_repr G det_repr_mx.
Proof.
split=> [|g h Gg Gh]; first by rewrite /det_repr_mx repr_mx1 det1.
by rewrite /det_repr_mx repr_mxM // det_mulmx !mulmxE scalar_mxM.
Qed.

Canonical det_repr := MxRepresentation det_is_repr.
Definition detRepr := cfRepr det_repr.

Lemma detRepr_lin_char : detRepr \is a linear_char.
Proof.
by rewrite qualifE cfRepr_char cfunE group1 repr_mx1 mxtrace1 mulr1n /=.
Qed.

End DetRepr.

Definition cfDet phi := \prod_i detRepr 'Chi_i ^+ truncC '[phi, 'chi[G]_i].

Lemma cfDet_lin_char phi : cfDet phi \is a linear_char.
Proof. by apply: rpred_prod => i _; apply: rpredX; apply: detRepr_lin_char. Qed.

Lemma cfDetD :
  {in character &, {morph cfDet : phi psi / phi + psi >-> phi * psi}}.
Proof.
move=> phi psi Nphi Npsi; rewrite /= -big_split; apply: eq_bigr => i _ /=.
by rewrite -exprD cfdotDl truncCD ?nnegrE ?Cnat_ge0 // Cnat_cfdot_char_irr.
Qed.

Lemma cfDet0 : cfDet 0 = 1.
Proof. by rewrite /cfDet big1 // => i _; rewrite cfdot0l truncC0. Qed.

Lemma cfDetMn k :
  {in character, {morph cfDet : phi / phi *+ k >-> phi ^+ k}}.
Proof.
move=> phi Nphi; elim: k => [|k IHk]; rewrite ?cfDet0 // mulrS exprS -{}IHk.
by rewrite cfDetD ?rpredMn.
Qed.

Lemma cfDetRepr n rG : cfDet (cfRepr rG) = @detRepr n rG.
Proof.
transitivity (\prod_W detRepr (socle_repr W) ^+ standard_irr_coef rG W).
  rewrite (reindex _ (socle_of_Iirr_bij _)) /cfDet /=.
  apply: eq_bigr => i _; congr (_ ^+ _).
  rewrite (cfRepr_sim (mx_rsim_standard rG)) cfRepr_standard.
  rewrite cfdot_suml (bigD1 i) ?big1 //= => [|j i'j]; last first.
    by rewrite cfdotZl cfdot_irr (negPf i'j) mulr0.
  by rewrite cfdotZl cfnorm_irr mulr1 addr0 natCK.
apply/cfun_inP=> x Gx; rewrite prod_cfunE //.
transitivity (detRepr (standard_grepr rG) x); last first.
  rewrite !cfunE Gx !trace_mx11 !mxE eqxx !mulrb.
  case: (standard_grepr rG) (mx_rsim_standard rG) => /= n1 rG1 [B Dn1].
  rewrite -{n1}Dn1 in rG1 B *; rewrite row_free_unit => uB rG_B.
  by rewrite -[rG x](mulmxK uB) rG_B // !det_mulmx mulrC -!det_mulmx mulKmx.
rewrite /standard_grepr; elim/big_rec2: _ => [|W y _ _ ->].
  by rewrite cfunE trace_mx11 mxE Gx det1.
rewrite !cfunE Gx /= !{1}trace_mx11 !{1}mxE det_ublock; congr (_ * _).
rewrite exp_cfunE //; elim: (standard_irr_coef rG W) => /= [|k IHk].
  by rewrite /muln_grepr big_ord0 det1.
rewrite exprS /muln_grepr big_ord_recl det_ublock -IHk; congr (_ * _).
by rewrite cfunE trace_mx11 mxE Gx.
Qed.

Lemma cfDet_id xi : xi \is a linear_char -> cfDet xi = xi.
Proof.
move=> lin_xi; have /irrP[i Dxi] := lin_char_irr lin_xi.
apply/cfun_inP=> x Gx; rewrite Dxi -irrRepr cfDetRepr !cfunE trace_mx11 mxE.
move: lin_xi (_ x) => /andP[_]; rewrite Dxi irr1_degree pnatr_eq1 => /eqP-> X.
by rewrite {1}[X]mx11_scalar det_scalar1 trace_mx11.
Qed.

Definition cfDet_order phi := #[cfDet phi]%CF.

Definition cfDet_order_lin xi :
  xi \is a linear_char -> cfDet_order xi = #[xi]%CF.
Proof. by rewrite /cfDet_order => /cfDet_id->. Qed.

Definition cfDet_order_dvdG phi : cfDet_order phi %| #|G|.
Proof. by rewrite cforder_lin_char_dvdG ?cfDet_lin_char. Qed.

End DetOrder.

Notation "''o' ( phi )" := (cfDet_order phi)
  (at level 8, format "''o' ( phi )") : cfun_scope.

Section CfDetOps.

Implicit Types gT aT rT : finGroupType.

Lemma cfDetRes gT (G H : {group gT}) phi :
  phi \is a character -> cfDet ('Res[H, G] phi) = 'Res (cfDet phi).
Proof.
move=> Nphi; have [sGH | not_sHG] := boolP (H \subset G); last first.
  have /CnatP[n Dphi1] := Cnat_char1 Nphi.
  rewrite !cfResEout // Dphi1 lin_char1 ?cfDet_lin_char // scale1r.
  by rewrite scaler_nat cfDetMn ?cfDet_id ?rpred1 // expr1n.
have [rG ->] := char_reprP Nphi; rewrite !(=^~ cfRepr_sub, cfDetRepr) //.
apply: cfRepr_sim; exists 1%:M; rewrite ?row_free_unit ?unitmx1 // => x Hx.
by rewrite mulmx1 mul1mx.
Qed.

Lemma cfDetMorph aT rT (D G : {group aT}) (f : {morphism D >-> rT})
                (phi : 'CF(f @* G)) :
  phi \is a character -> cfDet (cfMorph phi) = cfMorph (cfDet phi).
Proof.
move=> Nphi; have [sGD | not_sGD] := boolP (G \subset D); last first.
  have /CnatP[n Dphi1] := Cnat_char1 Nphi.
  rewrite !cfMorphEout // Dphi1 lin_char1 ?cfDet_lin_char // scale1r.
  by rewrite scaler_nat cfDetMn ?cfDet_id ?rpred1 // expr1n.
have [rG ->] := char_reprP Nphi; rewrite !(=^~ cfRepr_morphim, cfDetRepr) //.
apply: cfRepr_sim; exists 1%:M; rewrite ?row_free_unit ?unitmx1 // => x Hx.
by rewrite mulmx1 mul1mx.
Qed.

Lemma cfDetIsom aT rT (G : {group aT}) (R : {group rT})
                (f : {morphism G >-> rT}) (isoGR : isom G R f) phi :
  cfDet (cfIsom isoGR phi) = cfIsom isoGR (cfDet phi).
Proof.
rewrite rmorph_prod /cfDet (reindex (isom_Iirr isoGR)); last first.
  by exists (isom_Iirr (isom_sym isoGR)) => i; rewrite ?isom_IirrK ?isom_IirrKV.
apply: eq_bigr => i; rewrite -!cfDetRepr !irrRepr isom_IirrE rmorphX cfIsom_iso.
by rewrite /= ![in cfIsom _]unlock cfDetMorph ?cfRes_char ?cfDetRes ?irr_char.
Qed.

Lemma cfDet_mul_lin gT (G : {group gT}) (lambda phi : 'CF(G)) :
    lambda \is a linear_char -> phi \is a character ->
  cfDet (lambda * phi) = lambda ^+ truncC (phi 1%g) * cfDet phi.
Proof.
case/andP=> /char_reprP[[n1 rG1] ->] /= n1_1 /char_reprP[[n2 rG2] ->] /=.
do [rewrite !cfRepr1 pnatr_eq1 natCK; move/eqP] in n1_1 *.
rewrite {n1}n1_1 in rG1 *; rewrite cfRepr_prod cfDetRepr.
apply/cfun_inP=> x Gx; rewrite !cfunE cfDetRepr cfunE Gx !mulrb !trace_mx11.
rewrite !mxE prod_repr_lin ?mulrb //=; case: _ / (esym _); rewrite detZ.
congr (_ * _); case: {rG2}n2 => [|n2]; first by rewrite cfun1E Gx.
by rewrite expS_cfunE //= cfunE Gx trace_mx11.
Qed.

End CfDetOps.

Definition cfcenter (gT : finGroupType) (G : {set gT}) (phi : 'CF(G)) := 
  if phi \is a character then [set g in G | `|phi g| == phi 1%g] else cfker phi.

Notation "''Z' ( phi )" := (cfcenter phi) : cfun_scope.

Section Center.

Variable (gT : finGroupType) (G : {group gT}).
Implicit Types (phi chi : 'CF(G)) (H : {group gT}).

(* This is Isaacs (2.27)(a). *)
Lemma cfcenter_repr n (rG : mx_representation algCF G n) : 
  'Z(cfRepr rG)%CF = rcenter rG.
Proof.
rewrite /cfcenter /rcenter cfRepr_char /=.
apply/setP=> x; rewrite !inE; apply/andb_id2l=> Gx.
apply/eqP/is_scalar_mxP=> [|[c rG_c]].
  by case/max_cfRepr_norm_scalar=> // c; exists c.
rewrite -(sqrCK (char1_ge0 (cfRepr_char rG))) normC_def; congr (sqrtC _).
rewrite expr2 -{2}(mulgV x) -char_inv ?cfRepr_char ?cfunE ?groupM ?groupV //.
rewrite Gx group1 repr_mx1 repr_mxM ?repr_mxV ?groupV // !mulrb rG_c.
by rewrite invmx_scalar -scalar_mxM !mxtrace_scalar mulrnAr mulrnAl mulr_natl.
Qed.

(* This is part of Isaacs (2.27)(b). *)
Fact cfcenter_group_set phi : group_set ('Z(phi))%CF.
Proof.
have [[rG ->] | /negbTE notNphi] := altP (@char_reprP _ G phi).
  by rewrite cfcenter_repr groupP.
by rewrite /cfcenter notNphi groupP.
Qed.
Canonical cfcenter_group f := Group (cfcenter_group_set f).

Lemma char_cfcenterE chi x :
    chi \is a character -> x \in G ->
  (x \in ('Z(chi))%CF) = (`|chi x| == chi 1%g).
Proof. by move=> Nchi Gx; rewrite /cfcenter Nchi inE Gx. Qed.

Lemma irr_cfcenterE i x :
  x \in G -> (x \in 'Z('chi[G]_i)%CF) = (`|'chi_i x| == 'chi_i 1%g).
Proof. by move/char_cfcenterE->; rewrite ?irr_char. Qed.

(* This is also Isaacs (2.27)(b). *)
Lemma cfcenter_sub phi : ('Z(phi))%CF \subset G.
Proof. by rewrite /cfcenter /cfker !setIdE -fun_if subsetIl. Qed.

Lemma cfker_center_normal phi : cfker phi <| 'Z(phi)%CF.
Proof.
apply: normalS (cfcenter_sub phi) (cfker_normal phi).
rewrite /= /cfcenter; case: ifP => // Hphi; rewrite cfkerEchar //.
apply/subsetP=> x; rewrite !inE => /andP[-> /eqP->] /=.
by rewrite ger0_norm ?char1_ge0.
Qed.

Lemma cfcenter_normal phi : 'Z(phi)%CF <| G.
Proof.
have [[rG ->] | /negbTE notNphi] := altP (@char_reprP _ _ phi).
  by rewrite cfcenter_repr rcenter_normal.
by rewrite /cfcenter notNphi cfker_normal.
Qed.

(* This is Isaacs (2.27)(c). *)
Lemma cfcenter_Res chi :
  exists2 chi1, chi1 \is a linear_char & 'Res['Z(chi)%CF] chi = chi 1%g *: chi1.
Proof.
have [[rG ->] | /negbTE notNphi] := altP (@char_reprP _ _ chi); last first.
  exists 1; first exact: cfun1_lin_char.
  rewrite /cfcenter notNphi; apply/cfun_inP=> x Kx.
  by rewrite cfunE cfun1E Kx mulr1 cfResE ?cfker_sub // cfker1.
rewrite cfcenter_repr -(cfRepr_sub _ (normal_sub (rcenter_normal _))).
case: rG => [[|n] rG] /=; rewrite cfRepr1.
  exists 1; first exact: cfun1_lin_char.
  by apply/cfun_inP=> x Zx; rewrite scale0r !cfunE flatmx0 raddf0 Zx.
pose rZmx x := ((rG x 0 0)%:M : 'M_(1,1)).
have rZmxP: mx_repr [group of rcenter rG] rZmx.
  split=> [|x y]; first by rewrite /rZmx repr_mx1 mxE eqxx.
  move=> /setIdP[Gx /is_scalar_mxP[a rGx]] /setIdP[Gy /is_scalar_mxP[b rGy]].
  by rewrite /rZmx repr_mxM // rGx rGy -!scalar_mxM !mxE.
exists (cfRepr (MxRepresentation rZmxP)).
  by rewrite qualifE cfRepr_char cfRepr1 eqxx.
apply/cfun_inP=> x Zx; rewrite !cfunE Zx /= /rZmx mulr_natl.
by case/setIdP: Zx => Gx /is_scalar_mxP[a ->]; rewrite mxE !mxtrace_scalar.
Qed.

(* This is Isaacs (2.27)(d). *)
Lemma cfcenter_cyclic chi : cyclic ('Z(chi)%CF / cfker chi)%g.
Proof.
case Nchi: (chi \is a character); last first.
  by rewrite /cfcenter Nchi trivg_quotient cyclic1.
have [-> | nz_chi] := eqVneq chi 0.
  rewrite quotientS1 ?cyclic1 //= /cfcenter cfkerEchar ?cfun0_char //.
  by apply/subsetP=> x /setIdP[Gx _]; rewrite inE Gx /= !cfunE.
have [xi Lxi def_chi] := cfcenter_Res chi.
set Z := ('Z(_))%CF in xi Lxi def_chi *.
have sZG: Z \subset G by apply: cfcenter_sub.
have ->: cfker chi = cfker xi.
  rewrite -(setIidPr (normal_sub (cfker_center_normal _))) -/Z.
  rewrite !cfkerEchar // ?lin_charW //= -/Z.
  apply/setP=> x; rewrite !inE; apply: andb_id2l => Zx.
  rewrite (subsetP sZG) //= -!(cfResE chi sZG) ?group1 // def_chi !cfunE.
  by rewrite (inj_eq (mulfI _)) ?char1_eq0.
have: abelian (Z / cfker xi) by rewrite sub_der1_abelian ?lin_char_der1.
have /irr_reprP[rG irrG ->] := lin_char_irr Lxi; rewrite cfker_repr.
apply: mx_faithful_irr_abelian_cyclic (kquo_mx_faithful rG) _.
exact/quo_mx_irr.
Qed.

(* This is Isaacs (2.27)(e). *)
Lemma cfcenter_subset_center chi : 
  ('Z(chi)%CF / cfker chi)%g \subset 'Z(G / cfker chi)%g.
Proof.
case Nchi: (chi \is a character); last first.
  by rewrite /cfcenter Nchi trivg_quotient sub1G.
rewrite subsetI quotientS ?cfcenter_sub // quotient_cents2r //=.
case/char_reprP: Nchi => rG ->{chi}; rewrite cfker_repr cfcenter_repr gen_subG.
apply/subsetP=> _ /imset2P[x y /setIdP[Gx /is_scalar_mxP[c rGx]] Gy ->].
rewrite inE groupR //= !repr_mxM ?groupM ?groupV // rGx -(scalar_mxC c) -rGx.
by rewrite !mulmxA !repr_mxKV.
Qed.

(* This is Isaacs (2.27)(f). *)
Lemma cfcenter_eq_center (i : Iirr G) : 
  ('Z('chi_i)%CF / cfker 'chi_i)%g = 'Z(G / cfker 'chi_i)%g.
Proof.
apply/eqP; rewrite eqEsubset; rewrite cfcenter_subset_center ?irr_char //.
apply/subsetP=> _ /setIP[/morphimP[x /= _ Gx ->] cGx]; rewrite mem_quotient //=.
rewrite -irrRepr cfker_repr cfcenter_repr inE Gx in cGx *.
apply: mx_abs_irr_cent_scalar 'Chi_i _ _ _.
  by apply: groupC; apply: socle_irr.
have nKG: G \subset 'N(rker 'Chi_i) by apply: rker_norm.
(* GG -- locking here is critical to prevent Coq kernel divergence. *)
apply/centgmxP=> y Gy; rewrite [eq]lock -2?(quo_repr_coset (subxx _) nKG) //.
move: (quo_repr _ _) => rG; rewrite -2?repr_mxM ?mem_quotient // -lock.
by rewrite (centP cGx) // mem_quotient.
Qed.

(* This is Isaacs (2.28). *)
Lemma cap_cfcenter_irr : \bigcap_i 'Z('chi[G]_i)%CF = 'Z(G).
Proof.
apply/esym/eqP; rewrite eqEsubset (introT bigcapsP) /= => [|i _]; last first.
  rewrite -(quotientSGK _ (normal_sub (cfker_center_normal _))).
    by rewrite cfcenter_eq_center morphim_center.
  by rewrite subIset // normal_norm // cfker_normal.
set Z := \bigcap_i _.
have sZG: Z \subset G by rewrite (bigcap_min 0) ?cfcenter_sub.
rewrite subsetI sZG (sameP commG1P trivgP) -(TI_cfker_irr G).
apply/bigcapsP=> i _; have nKiG := normal_norm (cfker_normal 'chi_i).
rewrite -quotient_cents2 ?(subset_trans sZG) //.
rewrite (subset_trans (quotientS _ (bigcap_inf i _))) //.
by rewrite cfcenter_eq_center subsetIr.
Qed.

(* This is Isaacs (2.29). *)
Lemma cfnorm_Res_lerif H phi :
    H \subset G ->
  '['Res[H] phi] <= #|G : H|%:R * '[phi] ?= iff (phi \in 'CF(G, H)).
Proof.
move=> sHG; rewrite cfun_onE mulrCA natf_indexg // -mulrA mulKf ?neq0CG //.
rewrite (big_setID H) (setIidPr sHG) /= addrC.
rewrite (mono_lerif (ler_pmul2l _)) ?invr_gt0 ?gt0CG // -lerif_subLR -sumrB.
rewrite big1 => [|x Hx]; last by rewrite !cfResE ?subrr.
have ->: (support phi \subset H) = (G :\: H \subset [set x | phi x == 0]).
  rewrite subDset setUC -subDset; apply: eq_subset => x.
  by rewrite !inE (andb_idr (contraR _)) // => /cfun0->.
rewrite (sameP subsetP forall_inP); apply: lerif_0_sum => x _.
by rewrite !inE /<?=%R mul_conjC_ge0 eq_sym mul_conjC_eq0.
Qed.

(* This is Isaacs (2.30). *)
Lemma irr1_bound (i : Iirr G) :
  ('chi_i 1%g) ^+ 2 <= #|G : 'Z('chi_i)%CF|%:R
                    ?= iff ('chi_i \in 'CF(G, 'Z('chi_i)%CF)).
Proof.
congr (_ <= _ ?= iff _): (cfnorm_Res_lerif 'chi_i (cfcenter_sub 'chi_i)).
  have [xi Lxi ->] := cfcenter_Res 'chi_i.
  have /irrP[j ->] := lin_char_irr Lxi; rewrite cfdotZl cfdotZr cfdot_irr eqxx.
  by rewrite mulr1 irr1_degree conjC_nat.
by rewrite cfdot_irr eqxx mulr1.
Qed.
  
(* This is Isaacs (2.31). *)
Lemma irr1_abelian_bound (i : Iirr G) :
  abelian (G / 'Z('chi_i)%CF) -> ('chi_i 1%g) ^+ 2 = #|G : 'Z('chi_i)%CF|%:R.
Proof.
move=> AbGc; apply/eqP; rewrite irr1_bound cfun_onE; apply/subsetP=> x nz_chi_x.
have Gx: x \in G by apply: contraR nz_chi_x => /cfun0->.
have nKx := subsetP (normal_norm (cfker_normal 'chi_i)) _ Gx.
rewrite -(quotientGK (cfker_center_normal _)) inE nKx inE /=.
rewrite cfcenter_eq_center inE mem_quotient //=.
apply/centP=> _ /morphimP[y nKy Gy ->]; apply/commgP; rewrite -morphR //=.
set z := [~ x, y]; rewrite coset_id //.
have: z \in 'Z('chi_i)%CF.
  apply: subsetP (mem_commg Gx Gy).
  by rewrite der1_min // normal_norm ?cfcenter_normal.
rewrite -irrRepr cfker_repr cfcenter_repr !inE in nz_chi_x *.
case/andP=> Gz /is_scalar_mxP[c Chi_z]; rewrite Gz Chi_z mul1mx /=.
apply/eqP; congr _%:M; apply: (mulIf nz_chi_x); rewrite mul1r.
rewrite -{2}(cfunJ _ x Gy) conjg_mulR -/z !cfunE Gx groupM // !{1}mulrb.
by rewrite repr_mxM // Chi_z mul_mx_scalar mxtraceZ.
Qed.

(* This is Isaacs (2.32)(a). *)
Lemma irr_faithful_center i : cfaithful 'chi[G]_i -> cyclic 'Z(G).
Proof.
rewrite (isog_cyclic (isog_center (quotient1_isog G))) /=.
by move/trivgP <-; rewrite -cfcenter_eq_center cfcenter_cyclic.
Qed.

Lemma cfcenter_fful_irr i : cfaithful 'chi[G]_i -> 'Z('chi_i)%CF = 'Z(G).
Proof.
move/trivgP=> Ki1; have:= cfcenter_eq_center i; rewrite {}Ki1.
have inj1: 'injm (@coset gT 1%g) by rewrite ker_coset.
by rewrite -injm_center; first apply: injm_morphim_inj; rewrite ?norms1.
Qed.

(* This is Isaacs (2.32)(b). *)
Lemma pgroup_cyclic_faithful (p : nat) :  
  p.-group G -> cyclic 'Z(G) -> exists i, cfaithful 'chi[G]_i.
Proof.
pose Z := 'Ohm_1('Z(G)) => pG cycZG; have nilG := pgroup_nil pG.
have [-> | ntG] := eqsVneq G [1]; first by exists 0; apply: cfker_sub.
have{pG} [[p_pr _ _] pZ] := (pgroup_pdiv pG ntG, pgroupS (center_sub G) pG).
have ntZ: 'Z(G) != [1] by rewrite center_nil_eq1.
have{pZ} oZ: #|Z| = p by apply: Ohm1_cyclic_pgroup_prime.
apply/existsP; apply: contraR ntZ; rewrite negb_exists => /forallP-not_ffulG.
rewrite -Ohm1_eq1 -subG1 /= -/Z -(TI_cfker_irr G); apply/bigcapsP=> i _.
rewrite prime_meetG ?oZ // setIC meet_Ohm1 // meet_center_nil ?cfker_normal //.
by rewrite -subG1 not_ffulG.
Qed.

End Center.

Section Induced.

Variables (gT : finGroupType) (G H : {group gT}).
Implicit Types (phi : 'CF(G)) (chi : 'CF(H)).

Lemma cfInd_char chi : chi \is a character -> 'Ind[G] chi \is a character.
Proof.
move=> Nchi; apply/forallP=> i; rewrite coord_cfdot -Frobenius_reciprocity //.
by rewrite Cnat_cfdot_char ?cfRes_char ?irr_char.
Qed.

Lemma cfInd_eq0 chi :
  H \subset G -> chi \is a character -> ('Ind[G] chi == 0) = (chi == 0).
Proof.
move=> sHG Nchi; rewrite -!(char1_eq0) ?cfInd_char // cfInd1 //.
by rewrite (mulrI_eq0 _ (mulfI _)) ?neq0CiG.
Qed.

Lemma Ind_irr_neq0 i : H \subset G -> 'Ind[G, H] 'chi_i != 0.
Proof. by move/cfInd_eq0->; rewrite ?irr_neq0 ?irr_char. Qed.

Definition Ind_Iirr (A B : {set gT}) i := cfIirr ('Ind[B, A] 'chi_i).

Lemma constt_cfRes_irr i : {j | j \in irr_constt ('Res[H, G] 'chi_i)}.
Proof. apply/sigW/neq0_has_constt/Res_irr_neq0. Qed.

Lemma constt_cfInd_irr i :
  H \subset G -> {j | j \in irr_constt ('Ind[G, H] 'chi_i)}.
Proof. by move=> sHG; apply/sigW/neq0_has_constt/Ind_irr_neq0. Qed.

Lemma cfker_Res phi :
  H \subset G -> phi \is a character -> cfker ('Res[H] phi) = H :&: cfker phi.
Proof.
move=> sHG Nphi; apply/setP=> x; rewrite !cfkerEchar ?cfRes_char // !inE.
by apply/andb_id2l=> Hx; rewrite (subsetP sHG) ?cfResE.
Qed.

(* This is Isaacs Lemma (5.11). *)
Lemma cfker_Ind chi :
    H \subset G -> chi \is a character -> chi != 0 ->
  cfker ('Ind[G, H] chi) = gcore (cfker chi) G.
Proof.
move=> sHG Nchi nzchi; rewrite !cfker_nzcharE ?cfInd_char ?cfInd_eq0 //.
apply/setP=> x; rewrite inE cfIndE // (can2_eq (mulVKf _) (mulKf _)) ?neq0CG //.
rewrite cfInd1 // mulrA -natrM Lagrange // mulr_natl -sumr_const.
apply/eqP/bigcapP=> [/normC_sum_upper ker_chiG_x y Gy | ker_chiG_x].
  by rewrite mem_conjg inE ker_chiG_x ?groupV // => z _; apply: char1_ge_norm.
by apply: eq_bigr => y /groupVr/ker_chiG_x; rewrite mem_conjgV inE => /eqP.
Qed.

Lemma cfker_Ind_irr i :
  H \subset G -> cfker ('Ind[G, H] 'chi_i) = gcore (cfker 'chi_i) G.
Proof. by move/cfker_Ind->; rewrite ?irr_neq0 ?irr_char. Qed.

End Induced.

Arguments Ind_Iirr {gT A%g} B%g i%R.

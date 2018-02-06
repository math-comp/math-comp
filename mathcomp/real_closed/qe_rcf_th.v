(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrfun ssrbool eqtype ssrnat seq choice path fintype.
From mathcomp
Require Import div bigop ssralg poly polydiv ssrnum perm zmodp ssrint.
From mathcomp
Require Import polyorder polyrcf interval matrix mxtens.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Num.Def Pdiv.Ring Pdiv.ComRing.

Local Open Scope nat_scope.
Local Open Scope ring_scope.

Section extra.

Variable R : rcfType.
Implicit Types (p q : {poly R}).


(* Proof. *)
(* move=> sq; rewrite comp_polyE; case hp: (size p) => [|n]. *)
(*   move/eqP: hp; rewrite size_poly_eq0 => /eqP ->. *)
(*   by rewrite !big_ord0 mulr1 lead_coef0. *)
(* rewrite big_ord_recr /= addrC lead_coefDl. *)
(*   by rewrite lead_coefZ lead_coef_exp // !lead_coefE hp. *)
(* rewrite (leq_ltn_trans (size_sum _ _ _)) // size_scale; last first. *)
(*   rewrite -[n]/(n.+1.-1) -hp -lead_coefE ?lead_coef_eq0 //. *)
(*   by rewrite -size_poly_eq0 hp. *)
(* rewrite polySpred ?ltnS ?expf_eq0; last first. *)
(*   by rewrite andbC -size_poly_eq0 gtn_eqF // ltnW. *)
(* apply/bigmax_leqP => i _; rewrite size_exp. *)
(* have [->|/size_scale->] := eqVneq p`_i 0; first by rewrite scale0r size_poly0. *)
(* by rewrite (leq_trans (size_exp_leq _ _)) // ltn_mul2l -subn1 subn_gt0 sq /=. *)
(* Qed. *)


Lemma mul2n n : (2 * n = n + n)%N. Proof. by rewrite mulSn mul1n. Qed.
Lemma mul3n n : (3 * n = n + (n + n))%N. Proof. by rewrite !mulSn addn0. Qed.
Lemma exp3n n : (3 ^ n)%N = (3 ^ n).-1.+1.
Proof. by elim: n => // n IHn; rewrite expnS IHn. Qed.

Definition exp3S n : (3 ^ n.+1 = 3 ^ n + (3 ^ n + 3 ^ n))%N
  := etrans (expnS 3 n) (mul3n (3 ^ n)).

Lemma tens_I3_mx (cR : comRingType) m n (M : 'M[cR]_(m,n)) :
  1%:M *t M =  castmx (esym (mul3n _ ), esym (mul3n _ ))
               (block_mx M            0
                         0 (block_mx M 0
                                     0 M : 'M_(m+m,n+n)%N)).
Proof.
rewrite [1%:M : 'M_(1+2)%N]scalar_mx_block.
rewrite [1%:M : 'M_(1+1)%N]scalar_mx_block.
rewrite !tens_block_mx.
apply/eqP; rewrite -(can2_eq (castmxKV _ _) (castmxK _ _)); apply/eqP.
rewrite castmx_comp !tens_scalar_mx !tens0mx !scale1r.
rewrite (castmx_block (mul1n _) (mul1n _) (mul2n _) (mul2n _)).
rewrite !castmx_comp /= !castmx_id.
rewrite (castmx_block (mul1n _) (mul1n _) (mul1n _) (mul1n _)).
by rewrite !castmx_comp /= !castmx_id !castmx_const /=.
Qed.

Lemma mul_1tensmx (cR : comRingType) (m n p: nat)
  (e3n : (n + (n + n) = 3 * n)%N)
  (A B C : 'M[cR]_(m, n))  (M : 'M[cR]_(n, p)) :
  castmx (erefl _, e3n)
         (row_mx A (row_mx B C)) *m (1%:M *t M)
  = castmx (erefl _, esym (mul3n _))
         (row_mx (A *m M) (row_mx (B *m M) (C *m M))).
Proof.
apply/eqP; rewrite -(can2_eq (castmxKV _ _) (castmxK _ _)); apply/eqP.
rewrite tens_I3_mx mulmx_cast castmx_mul !castmx_comp /= !castmx_id /=.
by rewrite !mul_row_block /= !mulmx0 !addr0 !add0r.
Qed.

(* :TODO: backport to polydiv *)
Lemma coprimep_rdiv_gcd p q : (p != 0) || (q != 0) ->
  coprimep (rdivp p (gcdp p q)) (rdivp q (gcdp p q)).
Proof.
move=> hpq.
have gpq0: gcdp p q != 0 by rewrite gcdp_eq0 negb_and.
rewrite -gcdp_eqp1 -(@eqp_mul2r _ (gcdp p q)) // mul1r.
have: gcdp p q %| p by rewrite dvdp_gcdl.
have: gcdp p q %| q by rewrite dvdp_gcdr.
rewrite !dvdpE !rdvdp_eq eq_sym; move/eqP=> hq; rewrite eq_sym; move/eqP=> hp.
rewrite (eqp_ltrans (mulp_gcdl _ _ _)) hq hp.
have lcn0 k : (lead_coef (gcdp p q)) ^+ k != 0.
  by rewrite expf_neq0 ?lead_coef_eq0.
by apply: eqp_gcd; rewrite ?eqp_scale.
Qed.

(* :TODO: generalize to non idomainTypes and backport to polydiv *)
Lemma rgcdp_eq0 p q : rgcdp p q == 0 = (p == 0) && (q == 0).
Proof. by rewrite -eqp0 (eqp_ltrans (eqp_rgcd_gcd _ _)) eqp0 gcdp_eq0. Qed.

(* :TODO: : move in polyorder *)
Lemma mu_eq0 : forall p x, p != 0 -> (\mu_x p == 0%N) = (~~ root p x).
Proof. by move=> p x p0; rewrite -mu_gt0 // -leqNgt leqn0. Qed.

Notation lcn_neq0 := lc_expn_rscalp_neq0.

(* :TODO: : move to polyorder *)
Lemma mu_mod p q x : (\mu_x p < \mu_x q)%N ->
 \mu_x (rmodp p q) =  \mu_x p.
Proof.
move=> mupq; have [->|p0] := eqVneq p 0; first by rewrite rmod0p.
have qn0 : q != 0 by apply: contraTneq mupq => ->; rewrite mu0 ltn0.
have /(canLR (addKr _)) <- := (rdivp_eq q p).
have [->|divpq_eq0] := eqVneq (rdivp p q) 0.
  by rewrite mul0r oppr0 add0r mu_mulC ?lcn_neq0.
rewrite mu_addl ?mu_mulC ?scaler_eq0 ?negb_or ?mulf_neq0 ?lcn_neq0 //.
by rewrite mu_opp mu_mul ?ltn_addl // ?mulf_neq0.
Qed.

(* :TODO: : move to polyorder *)
Lemma mu_add p q x : p + q != 0 ->
  (minn (\mu_x p) (\mu_x q) <= \mu_x (p + q)%R)%N .
Proof.
have [->|p0] := eqVneq p 0; first by rewrite mu0 min0n add0r.
have [->|q0] := eqVneq q 0; first by rewrite mu0 minn0 addr0.
have [Hpq|Hpq|Hpq] := (ltngtP (\mu_x p) (\mu_x q)).
+ by rewrite mu_addr ?geq_minl.
+ by rewrite mu_addl ?geq_minr.
have [//|p' nrp'x hp] := (@mu_spec _ p x).
have [//|q' nrq'x hq] := (@mu_spec _ q x).
rewrite Hpq minnn hp {1 3}hq Hpq -mulrDl => pq0.
by rewrite mu_mul // mu_exp mu_XsubC mul1n leq_addl.
Qed.

(* :TODO: : move to polydiv *)
Lemma mu_mod_leq : forall p q x, ~~ (q %| p) ->
  (\mu_x q <= \mu_x p)%N ->
  (\mu_x q <= \mu_x (rmodp p q)%R)%N.
Proof.
move=> p q x; rewrite dvdpE /rdvdp=> rn0 mupq.
case q0: (q == 0); first by rewrite (eqP q0) mu0 leq0n.
move/eqP: (rdivp_eq q p).
rewrite eq_sym (can2_eq (addKr _ ) (addNKr _)); move/eqP=> hr.
rewrite hr; case qpq0: (rdivp p q == 0).
  by rewrite (eqP qpq0) mul0r oppr0 add0r mu_mulC // lcn_neq0.
rewrite (leq_trans _ (mu_add _ _)) // -?hr //.
rewrite leq_min mu_opp mu_mul ?mulf_neq0 ?qpq0 ?q0 // leq_addl.
by rewrite mu_mulC // lcn_neq0.
Qed.

(* Lemma sgp_right0 : forall (x : R), sgp_right 0 x = 0. *)
(* Proof. by move=> x; rewrite /sgp_right size_poly0. Qed. *)

End extra.

Section ctmat.

Variable R : numFieldType.

Definition ctmat1 := \matrix_(i < 3, j < 3)
  (nth [::] [:: [:: 1%:Z ; 1 ; 1 ]
              ; [:: -1   ; 1 ; 1 ]
              ; [::  0   ; 0 ; 1 ] ] i)`_j.

Lemma det_ctmat1 : \det ctmat1 = 2.
Proof.
(* Developpement direct ? *)
by do ?[rewrite (expand_det_row _ ord0) //=;
  rewrite ?(big_ord_recl,big_ord0) //= ?mxE //=;
    rewrite /cofactor /= ?(addn0, add0n, expr0, exprS);
      rewrite ?(mul1r,mulr1,mulN1r,mul0r,mul1r,addr0) /=;
        do ?rewrite [row' _ _]mx11_scalar det_scalar1 !mxE /=].
Qed.

Notation zmxR := ((map_mx ((intmul 1) : int -> R)) _ _).

Lemma ctmat1_unit : zmxR ctmat1 \in unitmx.
Proof.
rewrite /mem /in_mem /= /unitmx det_map_mx //.
by rewrite det_ctmat1 unitfE intr_eq0.
Qed.

Definition ctmat n := (ctmat1 ^t n).

Lemma ctmat_unit : forall n, zmxR (ctmat n) \in unitmx.
Proof.
case=> [|n] /=; first by rewrite map_mx1 ?unitmx1//; apply: zinjR_morph.
elim: n=> [|n ihn] /=; first by  apply: ctmat1_unit.
rewrite map_mxT //.
apply: tensmx_unit=> //; last exact: ctmat1_unit.
by elim: n {ihn}=> // n ihn; rewrite muln_eq0.
Qed.

Lemma ctmat1_blocks : ctmat1 = (block_mx
         1           (row_mx 1 1)
  (col_mx (-1) 0) (block_mx 1 1 0 1 : 'M_(1+1)%N)).
Proof.
apply/matrixP=> i j; rewrite !mxE.
by do 4?[case: splitP => ?; rewrite !mxE ?ord1=> ->].
Qed.

Lemma tvec_sub n : (3 * (3 ^ n).-1.+1 = 3 ^ (n.+1) )%N.
Proof. by rewrite -exp3n expnS. Qed.

Lemma tens_ctmat1_mx n (M : 'M_n) :
  ctmat1 *t M =  castmx (esym (mul3n _ ), esym (mul3n _ ))
         (block_mx         M         (row_mx M M)
                   (col_mx (-M) 0) (block_mx M M
                                             0 M : 'M_(n+n)%N)).
Proof.
rewrite ctmat1_blocks !tens_block_mx !tens_row_mx !tens_col_mx.
rewrite [-1]mx11_scalar !mxE /= !tens_scalar_mx !tens0mx scaleNr !scale1r.
apply/eqP; rewrite -(can2_eq (castmxKV _ _) (castmxK _ _)); apply/eqP.
rewrite !castmx_comp !esymK /=.
rewrite !(castmx_block (mul1n _) (mul1n _) (mul2n _) (mul2n _)).
rewrite !castmx_comp !castmx_id /=.
rewrite !(castmx_row (mul1n _) (mul1n _)).
rewrite !(castmx_block (mul1n _) (mul1n _) (mul1n _) (mul1n _)) /=.
rewrite !(castmx_col (mul1n _) (mul1n _)) !castmx_comp !castmx_id /=.
by rewrite !castmx_const.
Qed.

Definition coefs n i :=
  [seq (castmx (erefl _, exp3n _) (invmx (zmxR (ctmat n)))) i ord0
     | i <- enum 'I__]`_i.

End ctmat.

Section QeRcfTh.

Variable R : rcfType.
Implicit Types a b  : R.
Implicit Types p q : {poly R}.

Notation zmxR := ((map_mx ((intmul 1) : int -> R)) _ _).
Notation midf a b := ((a + b) / 2%:~R).

(* Constraints and Tarski queries *)

Local Notation sgp_is q s := (fun x => (sgr q.[x] == s)).

Definition constraints (z : seq R) (sq : seq {poly R}) (sigma : seq int) :=
  (\sum_(x <- z) \prod_(i < size sq) (sgz (sq`_i).[x] == sigma`_i))%N.

Definition taq (z : seq R) (q : {poly R}) : int := \sum_(x <- z) (sgz q.[x]).

Lemma taq_constraint1 z q :
  taq z q = (constraints z [::q] [::1])%:~R - (constraints z [::q] [::-1])%:~R.
Proof.
rewrite /constraints /taq !sumMz -sumrB /=; apply: congr_big=> // x _.
by rewrite !big_ord_recl big_ord0 !muln1 /=; case: sgzP.
Qed.

Lemma taq_constraint0 z q :
  taq z 1 = (constraints z [::q] [:: 0])%:~R
          + (constraints z [::q] [:: 1])%:~R
          + (constraints z [::q] [::-1])%:~R.
Proof.
rewrite /constraints /taq !sumMz //= -!big_split /=; apply: congr_big=> // x _.
by rewrite hornerC sgz1 !big_ord_recl big_ord0 !muln1 /=; case: sgzP.
Qed.

Lemma taq_no_constraint z : taq z 1 = (constraints z [::] [::])%:~R.
Proof.
rewrite /constraints /taq !sumMz; apply: congr_big=> // x _.
by rewrite hornerC sgz1 big_ord0.
Qed.

Lemma taq_constraint2 z q :
  taq z (q ^+ 2) = (constraints z [::q] [:: 1])%:~R
                 + (constraints z [::q] [::-1])%:~R.
Proof.
rewrite /constraints /taq !sumMz -big_split /=; apply: congr_big=> // x _.
rewrite !big_ord_recl big_ord0 !muln1 /= horner_exp sgzX.
by case: (sgzP q.[x])=> _.
Qed.

Fixpoint sg_tab n : seq (seq int) :=
  if n is m.+1
    then flatten (map (fun x => map (fun l => x :: l) (sg_tab m)) [::1; -1; 0])
    else [::[::]].

Lemma sg_tab_nil n : (sg_tab n == [::]) = false.
Proof. by elim: n => //= n; case: sg_tab. Qed.

Lemma size_sg_tab n : size (sg_tab n) = (3 ^ n)%N.
Proof.
by elim: n => [|n] // ihn; rewrite !size_cat !size_map ihn addn0 exp3S.
Qed.

Lemma size_sg_tab_neq0 n : size (sg_tab n) != 0%N.
Proof. by rewrite size_sg_tab exp3n. Qed.


Definition comb_exp (R : realDomainType) (s : R) :=
  match sgz s with Posz 1 => 1%N | Negz 0 => 2 | _ => 0%N end.

Definition poly_comb (sq : seq {poly R}) (sc : seq int) : {poly R} :=
  \prod_(i < size sq) ((sq`_i) ^+ (comb_exp sc`_i)).

(* Eval compute in sg_tab 4. *)

Definition cvec z sq := let sg_tab := sg_tab (size sq) in
  \row_(i < 3 ^ size sq) ((constraints z sq (nth [::] sg_tab i))%:~R : int).
Definition tvec z sq := let sg_tab := sg_tab (size sq) in
  \row_(i < 3 ^ size sq) (taq z (map (poly_comb sq) sg_tab)`_i).


Lemma tvec_cvec1 z q : tvec z [::q] = (cvec z [::q]) *m ctmat1.
Proof.
apply/rowP => j.
rewrite /tvec !mxE /poly_comb /= !big_ord_recl !big_ord0 //=.
rewrite !(expr0,expr1,mulr1) /=.
case: j=> [] [|[|[|j]]] hj //.
* by rewrite !mxE /= mulr0 add0r mulr1 mulrN1 addr0 taq_constraint1.
* by rewrite !mxE /= mulr0 !mulr1 add0r addr0 taq_constraint2.
* by rewrite !mxE /= addrA (@taq_constraint0 _ q) !mulr1 addr0 -addrA addrC.
Qed.

Lemma cvec_rec z q sq :
  cvec z (q :: sq) = castmx (erefl _, esym (exp3S _))
       (row_mx (cvec (filter (sgp_is q 1) z) (sq))
               (row_mx (cvec (filter (sgp_is q (-1)) z) (sq))
                       (cvec (filter (sgp_is q 0) z) (sq)))).
Proof.
apply/eqP; rewrite -(can2_eq (castmxKV _ _) (castmxK _ _)); apply/eqP.
apply/rowP=> [] i; rewrite !(mxE, castmxE, esymK, cast_ord_id) /=.
symmetry; case: splitP=> j hj /=; rewrite !mxE hj.
  case hst: sg_tab (sg_tab_nil (size sq))=> [|l st] // _.
  have sst: (size st).+1 = (3 ^ size sq)%N.
    transitivity (size (sg_tab (size sq))); first by rewrite hst //.
    by rewrite size_sg_tab.
  rewrite /constraints big_filter big_mkcond !sumMz; apply: congr_big=> // x _.
  rewrite nth_cat size_map ![size (_::_)]/= sst ltn_ord.
  rewrite (nth_map [::]) /= ?sst ?ltn_ord // big_ord_recl /=.
  by rewrite sgr_cp0 sgz_cp0; case: (_ < _); first by rewrite mul1n.
case: splitP=> k hk; rewrite !mxE /= hk.
  case hst: sg_tab (sg_tab_nil (size sq))=> [|l st] // _.
  have sst: (size st).+1 = (3 ^ size sq)%N.
    transitivity (size (sg_tab (size sq))); first by rewrite hst //.
    by rewrite size_sg_tab.
  rewrite /constraints big_filter big_mkcond !sumMz; apply: congr_big=> // x _.
  rewrite nth_cat nth_cat !size_map ![size (_ :: _)]/= sst ltnNge leq_addr.
  rewrite (@nth_map _ [::] _ _ [eta cons (-1)] _ (l::st)) /= ?sst addKn ltn_ord //.
  rewrite big_ord_recl /= sgr_cp0 sgz_cp0.
  by case: (_ < _); first by rewrite mul1n.
case hst: sg_tab (sg_tab_nil (size sq))=> [|l st] // _.
have sst: (size st).+1 = (3 ^ size sq)%N.
  transitivity (size (sg_tab (size sq))); first by rewrite hst //.
  by rewrite size_sg_tab.
rewrite /constraints big_filter big_mkcond !sumMz; apply: congr_big=> // x _.
rewrite nth_cat nth_cat nth_cat !size_map ![size (_ :: _)]/= sst.
rewrite (@nth_map _ [::] _ _ [eta cons 0] _ (l::st)) /=; last first.
  by rewrite !addKn sst ltn_ord.
rewrite ltnNge leq_addr /= !addKn ltnNge leq_addr /= ltn_ord.
rewrite big_ord_recl /= sgr_cp0 sgz_cp0.
by case: (_ == _); first by rewrite mul1n.
Qed.


Lemma poly_comb_cons q sq s ss :
  poly_comb (q :: sq) (s :: ss) = (q ^ (comb_exp s)) * poly_comb sq ss.
Proof. by rewrite /poly_comb /= big_ord_recl /=. Qed.

Lemma comb_expE (rR : realDomainType):
  (comb_exp (1 : rR) = 1%N) * (comb_exp (-1 : rR) = 2%N) * (comb_exp (0 : rR) = 0%N).
Proof. by rewrite /comb_exp sgzN sgz1 sgz0. Qed.

Lemma tvec_rec z q sq :
  tvec z (q :: sq) =
  castmx (erefl _, esym (exp3S _)) (
    (row_mx (tvec (filter (sgp_is q 1) z) (sq))
      (row_mx (tvec (filter (sgp_is q (-1)) z) (sq))
        (tvec (filter (sgp_is q 0) z) (sq)))) *m
    (castmx (mul3n _, mul3n _) (ctmat1 *t 1%:M))).
Proof.
rewrite tens_ctmat1_mx !castmx_comp !castmx_id /=.
rewrite !(mul_row_block, mul_row_col, mul_mx_row) !(mulmx1, mulmx0, mulmxN, addr0) /=.
apply/eqP; rewrite -(can2_eq (castmxKV _ _) (castmxK _ _)); apply/eqP.
apply/matrixP=> i j; rewrite !(castmxE, mxE) /=.
symmetry; case: splitP=> l hl; rewrite !mxE hl.
  case hst: sg_tab (sg_tab_nil (size sq))=> [|s st] // _.
  have sst: (size st).+1 = (3 ^ size sq)%N.
    transitivity (size (sg_tab (size sq))); first by rewrite hst //.
    by rewrite size_sg_tab.
  rewrite /taq !big_filter !(big_mkcond (sgp_is _ _)) -sumrB.
  apply: congr_big=> // x _.
  rewrite cats0 !map_cat nth_cat !size_map /= sst ltn_ord /=.
  rewrite !poly_comb_cons /= !comb_expE expr1z.
  rewrite -!(nth_map _ 0 (fun p => p.[_])) /= ?size_map ?sst ?ltn_ord //.
  rewrite -!map_comp /= hornerM.
  set f := _ \o _; set g := _ \o _.
  set h := fun sc => q.[x] * (poly_comb sq sc).[x].
  have hg : g =1 h.
    by move=> sx; rewrite /g /h /= poly_comb_cons comb_expE expr1z hornerM.
  rewrite -/(h _) -hg -[g _ :: _]/(map g (_ ::_)).
  rewrite (nth_map [::]) /= ?sst ?ltn_ord // hg /h sgzM.
  rewrite -![(poly_comb _ _).[_]]/(f _) -[f _ :: _]/(map f (_ ::_)).
  rewrite (nth_map [::]) /= ?sst ?ltn_ord // !sgr_cp0.
  by case: (sgzP q.[x]); rewrite ?(mul0r, mul1r, mulN1r, subr0, sub0r).
case: splitP=> k hk /=; rewrite !mxE hk.
  case hst: sg_tab (sg_tab_nil (size sq))=> [|s st] // _.
  have sst: (size st).+1 = (3 ^ size sq)%N.
    transitivity (size (sg_tab (size sq))); first by rewrite hst //.
    by rewrite size_sg_tab.
  rewrite /taq !big_filter !(big_mkcond (sgp_is _ _)) -big_split.
  apply: congr_big=> // x _.
  rewrite cats0 !map_cat !nth_cat !size_map /= sst.
  rewrite ltnNge leq_addr /= addKn ltn_ord /=.
  rewrite !poly_comb_cons /= !comb_expE.
  rewrite -!(nth_map _ 0 (fun p => p.[_])) /= ?size_map ?sst ?ltn_ord //.
  rewrite -!map_comp /= hornerM.
  set f := _ \o _; set g := _ \o _.
  set h := fun sc => (q ^ 2).[x] * (poly_comb sq sc).[x].
  have hg : g =1 h.
    by move=> sx; rewrite /g /h /= poly_comb_cons comb_expE hornerM.
  rewrite -/(h _) -hg -[g _ :: _]/(map g (_ ::_)).
  rewrite (nth_map [::]) /= ?sst ?ltn_ord // hg /h sgzM.
  rewrite -![(poly_comb _ _).[_]]/(f _) -[f _ :: _]/(map f (_ ::_)).
  rewrite (nth_map [::]) /= ?sst ?ltn_ord //.
  rewrite hornerM sgzM !sgr_cp0.
  by case: (sgzP q.[x]); rewrite ?(mul0r, mul1r, mulN1r, addr0, add0r).
case hst: sg_tab (sg_tab_nil (size sq))=> [|s st] // _.
have sst: (size st).+1 = (3 ^ size sq)%N.
  transitivity (size (sg_tab (size sq))); first by rewrite hst //.
  by rewrite size_sg_tab.
rewrite /taq !big_filter !(big_mkcond (sgp_is _ _)) -!big_split.
apply: congr_big=> // x _.
rewrite cats0 !map_cat !nth_cat !size_map /= sst.
rewrite !addKn 2!ltnNge !leq_addr /=.
rewrite !poly_comb_cons /= !comb_expE expr0z mul1r.
rewrite -!(nth_map _ 0 (fun p => p.[_])) /= ?size_map ?sst ?ltn_ord //.
rewrite -!map_comp /=.
set f := _ \o _; set g := _ \o _.
have hg : g =1 f.
  by move=> sx; rewrite /g /f /= poly_comb_cons comb_expE expr0z mul1r.
rewrite -[(poly_comb _ _).[_]]/(f _) -{4}hg.
rewrite -[g s :: _]/(map _ (_ ::_)) (eq_map hg) !sgr_cp0.
by case: (sgzP q.[x])=> _; rewrite ?(addr0, add0r).
Qed.

Lemma tvec_cvec z sq :
  tvec z sq = (cvec z sq) *m (ctmat (size sq)).
Proof.
elim: sq z => [|q sq ihsq] z /=.
  rewrite mulmx1; apply/rowP=> [] [i hi] /=; rewrite !mxE /=.
  move: hi; rewrite expn0 ltnS leqn0; move/eqP=> -> /=.
  rewrite /poly_comb big_ord0 /taq /constraints /=.
  rewrite sumMz; apply: (congr_big)=> //= x _.
  by rewrite hornerC sgz1 big_ord0.
rewrite /ctmat /ntensmx /=. (* simpl in trunk is "weaker" here *)
case: sq ihsq=> /= [|q' sq] ihsq; first by apply: tvec_cvec1.
rewrite cvec_rec tensmx_decl mulmxA tvec_rec.
apply/eqP; rewrite (can2_eq (castmxK _ _) (castmxKV _ _)); apply/eqP.
rewrite !castmx_mul !castmx_id [row_mx _ _ *m _]mulmx_cast.
congr (_ *m _); last by congr (castmx (_, _) _); apply: nat_irrelevance.
rewrite /=; have->: forall n, exp3S n.+1 = mul3n (3^n.+1)%N.
  by move=> n; apply: nat_irrelevance.
by rewrite mul_1tensmx !ihsq.
Qed.

Lemma cvec_tvec z sq :
  zmxR (cvec z (sq)) = (zmxR (tvec z (sq))) *m (invmx (zmxR (ctmat (size (sq))))).
Proof.
apply/eqP; set A := zmxR (ctmat _).
rewrite -(@can2_eq _ _ (fun (x : 'rV_(_)) => x *m A) (fun x => x *m (invmx A))).
* by rewrite /A -map_mxM ?tvec_cvec//; apply: zinjR_morph.
* by apply: mulmxK; rewrite /A ctmat_unit.
* by apply: mulmxKV; rewrite /A ctmat_unit.
Qed.

Lemma constraints1_tvec : forall z sq,
  (constraints z (sq) (nseq (size (sq)) 1))%:~R = (castmx (erefl _, exp3n _)
    (zmxR (tvec z (sq)) *m (invmx (zmxR (ctmat (size (sq))))))) ord0 ord0.
Proof.
move=> z sq.
rewrite -cvec_tvec castmxE /= cast_ord_id /= /cvec !mxE //= intz.
congr ((constraints _ _ _)%:~R); elim: sq=> //=  _ s -> /=.
set l := sg_tab _; suff: size l != 0%N by case: l.
exact: size_sg_tab_neq0.
Qed.

(* Cauchy Index, relation with Tarski query*)

Local Notation seq_mids a s b := (pairmap (fun x y => midf x y) a (rcons s b)).
Local Notation noroot p := (forall x, ~~ root p x).
Notation lcn_neq0 := lc_expn_rscalp_neq0.

Definition jump q p x: int :=
  let non_null := (q != 0) && odd (\mu_x p - \mu_x q) in
  let sign := (sgp_right (q * p) x < 0)%R in
    (-1) ^+ sign *+ non_null.

Definition cindex (a b : R) (q p : {poly R}) : int :=
  \sum_(x <- roots p a b) jump q p x.

Definition cindexR q p := \sum_(x <- rootsR p) jump q p x.

Definition sjump p x : int :=
  ((-1) ^+ (sgp_right p x < 0)%R) *+ odd (\mu_x p).

Definition variation (x y : R) : int := (sgz y) * (x * y < 0).

Definition cross p a b := variation p.[a] p.[b].

Definition crossR p := variation (sgp_minfty p) (sgp_pinfty p).

Definition sum_var (s : seq R) := \sum_(n <- pairmap variation 0 s) n.

Lemma cindexEba a b : b <= a -> forall p q, cindex a b p q = 0.
Proof. by move=> le_ba p q; rewrite /cindex rootsEba ?big_nil. Qed.

Lemma jump0p q x : jump 0 q x = 0. Proof. by rewrite /jump eqxx mulr0n. Qed.

Lemma taq_cindex a b p q : taq (roots p a b) q = cindex a b (p^`() * q) p.
Proof.
have [lt_ab|?] := ltrP a b; last by rewrite rootsEba ?cindexEba /taq ?big_nil.
rewrite /taq /cindex !big_seq; apply: eq_bigr => x.
have [->|p_neq0 /root_roots rpx] := eqVneq p 0; first by rewrite roots0 in_nil.
have [->|q_neq0] := eqVneq q 0; first by rewrite mulr0 jump0p horner0 sgz0.
have [p'0|p'_neq0] := eqVneq p^`() 0.
  move/(root_size_gt1 p_neq0): rpx.
  by rewrite -subn_gt0 subn1 -size_deriv p'0 size_poly0.
have p'q0: p^`() * q != 0 by rewrite mulf_neq0.
move: (p'q0); rewrite mulf_eq0 negb_or; case/andP=> p'0 q0.
have p0: p != 0 by move: p'0; apply: contra; move/eqP->; rewrite derivC.
rewrite /jump  mu_mul// {1}(@mu_deriv_root _ _ p)// addn1 p'q0 /=.
case emq: (\mu_(_) q)=> [|m].
  move/eqP: emq; rewrite -leqn0 leqNgt mu_gt0// => qxn0.
  rewrite addn0 subSnn mulr1n.
  rewrite !sgp_right_mul// (sgp_right_deriv rpx) mulrAC.
  rewrite sgp_right_square// mul1r sgp_rightNroot//.
  rewrite sgr_lt0 -sgz_cp0.
  by move: qxn0; rewrite -[root q x]sgz_cp0; case: sgzP.
rewrite addnS subSS -{1}[\mu_(_) _]addn0 subnDl sub0n mulr0n.
by apply/eqP; rewrite sgz_cp0 -[_ == 0]mu_gt0// emq.
Qed.

Lemma sum_varP s : 0 \notin s -> sum_var s = variation (head 0 s) (last 0 s).
Proof.
rewrite /sum_var /variation.
case: s => /= [_|a s]; first by rewrite big_nil sgz0 mul0r.
rewrite in_cons big_cons mul0r ltrr mulr0 add0r.
elim: s a => [|b s IHs] a; first by rewrite big_nil ler_gtF ?mulr0 ?sqr_ge0.
move=> /norP [neq_0a Hbs]; move: (Hbs); rewrite in_cons => /norP[neq_0b Hs].
rewrite /= big_cons IHs ?negb_or ?neq_0b // -!sgz_cp0 !sgzM.
have: (last b s) != 0 by apply: contra Hbs => /eqP <-; rewrite mem_last.
by move: neq_0a neq_0b; do 3?case: sgzP => ? //.
Qed.

Lemma jump_coprime p q : p != 0 -> coprimep p q
  -> forall x, root p x -> jump q p x = sjump (q * p) x.
Proof.
move=> pn0 cpq x rpx; rewrite /jump /sjump.
have q_neq0 : q != 0; last rewrite q_neq0 /=.
  apply: contraTneq cpq => ->; rewrite coprimep0.
  by apply: contraL rpx => /eqp_root ->; rewrite rootC oner_eq0.
have := coprimep_root cpq rpx; rewrite -rootE -mu_eq0 => // /eqP muxq_eq0.
by rewrite mu_mul ?mulf_neq0 ?muxq_eq0 ?subn0 ?add0n.
Qed.

Lemma sjump_neigh a b p x : p != 0 ->
  {in neighpl p a x & neighpr p x b,
   forall yl yr,  sjump p x = cross p yl yr}.
Proof.
move=> pn0 yl yr yln yrn; rewrite /cross /variation.
rewrite -sgr_cp0 sgrM /sjump (sgr_neighpl yln) -!(sgr_neighpr yrn).
rewrite -mulrA -expr2 sqr_sg (rootPf (neighpr_root yrn)) mulr1.
rewrite sgrEz ltrz0 -[in rhs in _ = rhs]intr_sign -[X in _ == X]mulrN1z eqr_int.
by have /rootPf := neighpr_root yrn; case: sgzP; case: odd.
Qed.

Lemma jump_neigh a b p q x : q * p != 0 ->
  {in neighpl (q * p) a x & neighpr (q * p) x b, forall yl yr,
   jump q p x =  cross (q * p) yl yr *+ ((q != 0) && (\mu_x p > \mu_x q)%N)}.
Proof.
move=> pqn0 yl yr hyl hyr; rewrite -(sjump_neigh pqn0 hyl hyr).
rewrite /jump /sjump -mulrnA mulnb andbCA.
have [muqp|/eqnP ->] := ltnP; rewrite (andbF, andbT) //.
by rewrite mu_mul // odd_add addbC odd_sub // ltnW.
Qed.

Lemma jump_mul2l (p q r : {poly R}) :
  p != 0 -> jump (p * q) (p * r) =1 jump q r.
Proof.
move=> p0 x; rewrite /jump.
case q0: (q == 0); first by rewrite (eqP q0) mulr0 eqxx.
have ->: p * q != 0 by rewrite mulf_neq0 ?p0 ?q0.
case r0: (r == 0); first by rewrite (eqP r0) !mulr0 mu0 !sub0n.
rewrite !mu_mul ?mulf_neq0 ?andbT ?q0 ?r0 //; rewrite subnDl.
rewrite mulrAC mulrA -mulrA.
rewrite (@sgp_right_mul _ (p * p)) // sgp_right_mul // sgp_right_square //.
by rewrite mul1r mulrC /=.
Qed.

Lemma jump_mul2r (p q r : {poly R}) :
  p != 0 -> jump (q * p) (r * p) =1 jump q r.
Proof. by move=> p0 x; rewrite ![_ * p]mulrC jump_mul2l. Qed.

Lemma jumppc p c x : jump p c%:P x = 0.
Proof. by rewrite /jump mu_polyC sub0n !andbF. Qed.

Lemma noroot_jump q p x : ~~ root p x -> jump q p x = 0.
Proof.
have [->|p_neq0] := eqVneq p 0; first by rewrite jumppc.
by rewrite -mu_gt0 // lt0n negbK /jump => /eqP ->; rewrite andbF mulr0n.
Qed.

Lemma jump_mulCp c p q x : jump (c *: p) q x = (sgz c) * jump p q x.
Proof.
have [->|c0] := eqVneq c 0; first by rewrite sgz0 scale0r jump0p mul0r.
have [->|p0] := eqVneq p 0; first by rewrite scaler0 jump0p mulr0.
have [->|q0] := eqVneq q 0; first by rewrite !jumppc mulr0.
(* :TODO: : rename mu_mulC *)
rewrite /jump scale_poly_eq0 mu_mulC ?negb_or ?c0 ?p0 ?andTb //.
rewrite -scalerAl sgp_right_scale //.
case: sgzP c0 => // _ _; rewrite !(mul1r, mulN1r, =^~ mulNrn) //.
by rewrite ?oppr_cp0 lt0r sgp_right_eq0 ?mulf_neq0 // andTb lerNgt signrN.
Qed.

Lemma jump_pmulC c p q x : jump p (c *: q) x = (sgz c) * jump p q x.
Proof.
have [->|c0] := eqVneq c 0; first by rewrite sgz0 scale0r mul0r jumppc.
have [->|p0] := eqVneq p 0; first by rewrite !jump0p mulr0.
have [->|q0] := eqVneq q 0; first by rewrite scaler0 !jumppc mulr0.
rewrite /jump mu_mulC // -scalerAr sgp_right_scale //.
case: sgzP c0 => // _ _; rewrite !(mul1r, mulN1r, =^~ mulNrn) //.
by rewrite ?oppr_cp0 lt0r sgp_right_eq0 ?mulf_neq0 // andTb lerNgt signrN.
Qed.

Lemma jump_mod p q x :
  jump p q x = sgz (lead_coef q) ^+ (rscalp p q) * jump (rmodp p q) q x.
Proof.
case p0: (p == 0); first by rewrite (eqP p0) rmod0p jump0p mulr0.
case q0: (q == 0); first by rewrite (eqP q0) rmodp0 jumppc mulr0.
rewrite -sgzX; set s := sgz _.
apply: (@mulfI _ s); first by rewrite /s sgz_eq0 lcn_neq0.
rewrite mulrA mulz_sg lcn_neq0 mul1r -jump_mulCp rdivp_eq.
have [->|rpq_eq0] := altP (rmodp p q =P 0).
  by rewrite addr0 jump0p -[X in jump _ X]mul1r jump_mul2r ?q0 // jumppc.
rewrite /jump. set r := _ * q + _.
have muxp : \mu_x p = \mu_x r by rewrite /r -rdivp_eq mu_mulC ?lcn_neq0.
have r_neq0 : r != 0 by rewrite /r -rdivp_eq scaler_eq0 p0 orbF lcn_neq0.
have [hpq|hpq] := leqP (\mu_x q) (\mu_x r).
  rewrite 2!(_ : _ - _ = 0)%N ?andbF //; apply/eqP; rewrite -/(_ <= _)%N //.
  by rewrite mu_mod_leq ?dvdpE // muxp.
rewrite mu_mod ?muxp // rpq_eq0 (negPf r_neq0); congr (_ ^+ _ *+ _).
rewrite !sgp_right_mul sgp_right_mod ?muxp // /r -rdivp_eq.
by rewrite -mul_polyC sgp_right_mul sgp_rightc sgrX.
Qed.

Lemma cindexRP q p a b :
  {in `]-oo, a], noroot p} -> {in `[b , +oo[, noroot p} ->
  cindex a b q p = cindexR q p.
Proof. by rewrite /cindex => rpa rpb; rewrite rootsRP. Qed.

Lemma cindex0p a b q : cindex a b 0 q = 0.
Proof.
have [lt_ab|le_ba] := ltrP a b; last by rewrite cindexEba.
by apply: big1_seq=> x; rewrite /jump eqxx mulr0n.
Qed.

Lemma cindexR0p p : cindexR 0 p = 0.
Proof. by rewrite /cindexR big1 // => q _; rewrite jump0p. Qed.

Lemma cindexpC a b p c : cindex a b p (c%:P) = 0.
Proof.
have [lt_ab|le_ba] := ltrP a b; last by rewrite cindexEba.
by rewrite /cindex /jump rootsC big_nil.
Qed.

Lemma cindexRpC q c : cindexR q c%:P = 0.
Proof. by rewrite /cindexR rootsRC big_nil. Qed.

Lemma cindex_mul2r a b p q r : r != 0 ->
  cindex a b (p * r) (q * r) = cindex a b p q.
Proof.
have [lt_ab r0|le_ba] := ltrP a b; last by rewrite !cindexEba.
have [->|p0] := eqVneq p 0; first by rewrite mul0r !cindex0p.
have [->|q0] := eqVneq q 0; first by rewrite mul0r !cindexpC.
rewrite /cindex (eq_big_perm _ (roots_mul _ _ _))//= big_cat/=.
rewrite -[\sum_(x <- _) jump p _ _]addr0; congr (_+_).
  by rewrite !big_seq; apply: congr_big => // x hx; rewrite jump_mul2r.
rewrite big1_seq//= => x hx; rewrite jump_mul2r // /jump.
suff ->: \mu_x q = 0%N by rewrite andbF.
apply/eqP; rewrite -leqn0 leqNgt mu_gt0 //.
apply/negP; rewrite root_factor_theorem => rqx; move/root_roots:hx.
case: gdcopP=> g hg; rewrite (negPf r0) orbF => cgq hdg.
rewrite root_factor_theorem=> rgx.
move/coprimepP:cgq rqx rgx=> cgq; rewrite -!dvdpE=> /cgq hgq /hgq.
by rewrite -size_poly_eq1 size_XsubC.
Qed.

Lemma cindex_mulCp a b p q c :
  cindex a b (c *: p) q = (sgz c) * cindex a b p q.
Proof.
have [lt_ab|le_ba] := ltrP a b; last by rewrite !cindexEba ?mulr0.
have [->|p0] := eqVneq p 0; first by rewrite !(cindex0p, scaler0, mulr0).
have [->|q0] := eqVneq q 0; first by rewrite !(cindexpC, scaler0, mulr0).
by rewrite /cindex big_distrr; apply: congr_big => //= x; rewrite jump_mulCp.
Qed.

Lemma cindex_pmulC a b p q c :
  cindex a b p (c *: q) = (sgz c) * cindex a b p q.
Proof.
have [lt_ab|le_ba] := ltrP a b; last by rewrite !cindexEba ?mulr0.
have [->|p0] := eqVneq p 0; first by rewrite !(cindex0p, scaler0, mulr0).
have [->|q0] := eqVneq q 0; first by rewrite !(cindexpC, scaler0, mulr0).
have [->|c0] := eqVneq c 0; first by rewrite scale0r sgz0 mul0r cindexpC.
rewrite /cindex big_distrr rootsZ //.
by apply: congr_big => // x _; rewrite jump_pmulC.
Qed.

Lemma cindex_mod a b p q :
  cindex a b p q =
  (sgz (lead_coef q) ^+ rscalp p q) * cindex a b (rmodp p q) q.
Proof.
have [lt_ab|le_ba] := ltrP a b; last by rewrite !cindexEba ?mulr0.
by rewrite /cindex big_distrr; apply: congr_big => // x; rewrite jump_mod.
Qed.

Lemma variation0r b : variation 0 b = 0.
Proof. by rewrite /variation mul0r ltrr mulr0. Qed.

Lemma variationC a b : variation a b = - variation b a.
Proof. by rewrite /variation -!sgz_cp0 !sgzM; do 2?case: sgzP => _ //. Qed.

Lemma variationr0 a : variation a 0 = 0.
Proof. by rewrite variationC variation0r oppr0. Qed.

Lemma variation_pmull a b c : c > 0 -> variation (a * c) (b) = variation a b.
Proof. by move=> c_gt0; rewrite /variation mulrAC pmulr_llt0. Qed.

Lemma variation_pmulr a b c : c > 0 -> variation a (b * c) = variation a b.
Proof. by move=> c_gt0; rewrite variationC variation_pmull // -variationC. Qed.

Lemma congr_variation a b a' b' : sgz a = sgz a' -> sgz b = sgz b' ->
  variation a b = variation a' b'.
Proof. by rewrite /variation -!sgz_cp0 !sgzM => -> ->. Qed.

Lemma crossRP p a b :
  {in `]-oo, a], noroot p} -> {in `[b , +oo[, noroot p} ->
  cross p a b = crossR p.
Proof.
move=> rpa rpb; rewrite /crossR /cross.
rewrite -(@sgp_minftyP _ _ _ rpa a) ?boundr_in_itv //.
rewrite -(@sgp_pinftyP _ _ _ rpb b) ?boundl_in_itv //.
by rewrite /variation -sgrM sgr_lt0 sgz_sgr.
Qed.

Lemma noroot_cross p a b : a <= b ->
  {in `]a, b[, noroot p} -> cross p a b = 0.
Proof.
move=> le_ab noroot_ab; rewrite /cross /variation.
have [] := ltrP; last by rewrite mulr0.
rewrite mulr1 -sgr_cp0 sgrM => /eqP.
by move=> /(ivt_sign le_ab) [x /noroot_ab /negPf->].
Qed.

Lemma cross_pmul p q a b : q.[a] > 0 -> q.[b] > 0 ->
  cross (p * q) a b = cross p a b.
Proof.
by move=> qa0 qb0; rewrite /cross !hornerM variation_pmull ?variation_pmulr.
Qed.

Lemma cross0 a b : cross 0 a b = 0.
Proof. by rewrite /cross !horner0 variation0r. Qed.

Lemma crossR0 : crossR 0 = 0.
Proof.
by rewrite /crossR /sgp_minfty /sgp_pinfty lead_coef0 mulr0 sgr0 variationr0.
Qed.

Lemma cindex_seq_mids a b : a < b ->
  forall p q, p != 0 -> q != 0 -> coprimep p q ->
  cindex a b q p + cindex a b p q =
  sum_var (map (horner (p * q)) (seq_mids a (roots (p * q) a b) b)).
Proof.
move=> hab p q p0 q0 cpq; rewrite /cindex /sum_var 2!big_seq.
have pq_neq0 : p * q != 0 by rewrite mulf_neq0.
have pq_eq0 := negPf pq_neq0.
have jumpP : forall (p q : {poly R}), p != 0 -> coprimep p q  ->
  forall x, x \in roots p a b -> jump q p x = sjump (q * p) x.
  by move=> ? ? ? ? ?; move/root_roots=> ?; rewrite jump_coprime.
rewrite !(eq_bigr _ (jumpP _ _ _ _))// 1?coprimep_sym// => {jumpP}.
have sjumpC x : sjump (q * p) x = sjump (p * q) x by rewrite mulrC.
rewrite -!big_seq (eq_bigr _ (fun x _ => sjumpC x)).
rewrite -big_cat /= -(eq_big_perm _ (roots_mul_coprime _ _ _ _)) //=.
move: {1 2 5}a hab (erefl (roots (p * q) a b)) => //=.
elim: roots => {a} [|x s /= ihs] a hab /eqP.
  by rewrite big_cons !big_nil variation0r.
rewrite roots_cons; case/and5P => _ xab /eqP hax hx /eqP hs.
rewrite !big_cons variation0r add0r (ihs _ _ hs) ?(itvP xab) // => {ihs}.
pose y := (head b s); pose ax := midf a x; pose xy := midf x y.
rewrite (@sjump_neigh a b _ _ _ ax xy) ?inE ?midf_lte//=; last 2 first.
+ by rewrite /prev_root pq_eq0 hax minr_l ?(itvP xab, midf_lte).
+ have hy: y \in `]x, b].
    rewrite /y; case: s hs {y xy} => /= [|u s] hu.
      by rewrite boundr_in_itv /= ?(itvP xab).
    have /roots_in: u \in  roots (p * q) x b by rewrite hu mem_head.
    by apply: subitvP; rewrite /= !lerr.
  by rewrite /next_root pq_eq0 hs maxr_l ?(itvP hy, midf_lte).
move: @y @xy {hs}; rewrite /cross.
by case: s => /= [|y l]; rewrite ?(big_cons, big_nil, variation0r, add0r).
Qed.

Lemma cindex_inv a b : a < b -> forall p q,
  ~~ root (p * q) a -> ~~ root (p * q) b ->
  cindex a b q p + cindex a b p q = cross (p * q) a b.
Proof.
move=> hab p q hpqa hpqb.
have hlab: a <= b by apply: ltrW.
wlog cpq: p q hpqa hpqb / coprimep p q => [hwlog|].
  have p0: p != 0 by apply: contraNneq hpqa => ->; rewrite mul0r rootC.
  have q0: q != 0 by apply: contraNneq hpqa => ->; rewrite mulr0 rootC.
  set p' := p; rewrite -(divpK (dvdp_gcdr p q)) -[p'](divpK (dvdp_gcdl p q)).
  rewrite !cindex_mul2r ?gcdp_eq0 ?(negPf p0) //.
  have ga0 : (gcdp p q).[a] != 0.
     apply: contra hpqa; rewrite -rootE -!dvdp_XsubCl => /dvdp_trans -> //.
     by rewrite dvdp_mulr ?dvdp_gcdl.
  have gb0 : (gcdp p q).[b] != 0.
     apply: contra hpqb; rewrite -rootE -!dvdp_XsubCl => /dvdp_trans -> //.
     by rewrite dvdp_mulr ?dvdp_gcdl.
  rewrite mulrACA -expr2 cross_pmul ?horner_exp ?exprn_even_gt0 ?ga0 ?gb0 //.
  apply: hwlog; rewrite ?coprimep_div_gcd ?p0 // rootM.
  + apply: contra hpqa; rewrite -!dvdp_XsubCl => /orP.
    case=> /dvdp_trans-> //; rewrite (dvdp_trans (divp_dvd _));
    by rewrite ?(dvdp_gcdl, dvdp_gcdr) ?(dvdp_mulIl, dvdp_mulIr).
  + apply: contra hpqb; rewrite -!dvdp_XsubCl => /orP.
    case=> /dvdp_trans-> //; rewrite (dvdp_trans (divp_dvd _));
    by rewrite ?(dvdp_gcdl, dvdp_gcdr) ?(dvdp_mulIl, dvdp_mulIr).
have p0: p != 0 by apply: contraNneq hpqa => ->; rewrite mul0r rootC.
have q0: q != 0 by apply: contraNneq hpqa => ->; rewrite mulr0 rootC.
have pq0 : p * q != 0 by rewrite mulf_neq0.
rewrite cindex_seq_mids // sum_varP /cross.
  apply: congr_variation; apply: (mulrIz (oner_neq0 R)); rewrite -!sgrEz.
    case hr: roots => [|c s] /=; apply: (@sgr_neighprN _ _ a b) => //;
    rewrite /neighpr /next_root ?(negPf pq0) maxr_l // hr mid_in_itv //=.
    by move/eqP: hr; rewrite roots_cons => /and5P [_ /itvP ->].
  rewrite -cats1 pairmap_cat /= cats1 map_rcons last_rcons.
  apply: (@sgr_neighplN _ _ a b) => //.
  rewrite /neighpl /prev_root (negPf pq0) minr_l //.
  by rewrite mid_in_itv //= last_roots_le.
elim: roots {-2 6}a (erefl (roots (p * q) a b))
  {hpqa hpqb} hab hlab => {a} [|c s IHs] a Hs hab hlab /=.
  rewrite in_cons orbF eq_sym. (* ; set x := (X in _.[X]). *)
  by rewrite -rootE (@roots_nil _ _ a b) // mid_in_itv.
move/eqP: Hs; rewrite roots_cons => /and5P [_ cab /eqP rac rc /eqP rcb].
rewrite in_cons eq_sym -rootE negb_or (roots_nil _ rac) //=; last first.
  by rewrite mid_in_itv //= (itvP cab).
by rewrite IHs // (itvP cab).
Qed.

Definition next_mod p q := - (lead_coef q ^+ rscalp p q) *: rmodp p q.

Lemma next_mod0p q : next_mod 0 q = 0.
Proof. by rewrite /next_mod rmod0p scaler0. Qed.

Lemma cindex_rec a b : a < b -> forall p q,
  ~~ root (p * q) a -> ~~ root (p * q) b ->
  cindex a b q p = cross (p * q) a b + cindex a b (next_mod p q) q.
Proof.
move=> lt_ab p q rpqa rpqb; have [->|p0] := eqVneq p 0.
  by rewrite cindexpC next_mod0p cindex0p mul0r cross0 add0r.
have [->|q0] := eqVneq q 0.
   by rewrite cindex0p cindexpC mulr0 cross0 add0r.
have /(canRL (addrK _)) -> := cindex_inv lt_ab rpqa rpqb.
by rewrite cindex_mulCp cindex_mod sgzN mulNr sgzX.
Qed.

Lemma cindexR_rec p q :
  cindexR q p = crossR (p * q) + cindexR (next_mod p q) q.
Proof.
have [->|p_neq0] := eqVneq p 0.
  by rewrite cindexRpC mul0r next_mod0p cindexR0p crossR0.
have [->|q_neq0] := eqVneq q 0.
  by rewrite cindexR0p mulr0 crossR0 cindexRpC.
have pq_neq0 : p * q != 0 by rewrite mulf_neq0.
pose b := cauchy_bound (p * q).
have [lecb gecb] := pair (le_cauchy_bound pq_neq0) (ge_cauchy_bound pq_neq0).
rewrite -?(@cindexRP _ _ (-b) b); do ?
  by [move=> x Hx /=; have: ~~ root (p * q) x by [apply: lecb|apply: gecb];
      rewrite rootM => /norP []].
rewrite -(@crossRP _ (-b) b)  1?cindex_rec ?gt0_cp ?cauchy_bound_gt0 //.
  by rewrite lecb // boundr_in_itv.
by rewrite gecb // boundl_in_itv.
Qed.

(* Computation of cindex through changes_mods *)

Definition mods p q :=
  let fix aux p q n :=
    if n is m.+1
      then if p == 0 then [::] else p :: (aux q (next_mod p q) m)
      else [::] in aux p q (maxn (size p) (size q).+1).

Lemma mods_rec p q : mods p q =
  if p == 0 then [::] else p :: (mods q (next_mod p q)).
Proof.
rewrite /mods; set aux := fix aux _ _ n := if n is _.+1 then _ else _.
have aux0 u n : aux 0 u n = [::] by case: n => [//|n] /=; rewrite eqxx.
pose m p q := maxn (size p) (size q).+1; rewrite -!/(m _ _).
suff {p q} Hnext p q : q != 0 -> (m q (next_mod p q) < m p q)%N; last first.
  rewrite /m -maxnSS leq_max !geq_max !ltnS leqnn /= /next_mod.
  rewrite size_scale ?oppr_eq0 ?lcn_neq0 //=.
  by move=> q_neq0; rewrite ltn_rmodp ?q_neq0 ?orbT.
suff {p q} m_gt0 p q : (0 < m p q)%N; last by rewrite leq_max orbT.
rewrite -[m p q]prednK //=; have [//|p_neq0] := altP (p =P 0).
have [->|q_neq0] := altP (q =P 0); first by rewrite !aux0.
congr (_ :: _); suff {p q p_neq0 q_neq0} Haux p q n n' :
    (m p q <= n)%N -> (m p q <= n')%N -> aux p q n = aux p q n'.
  by apply: Haux => //; rewrite -ltnS prednK // Hnext.
elim: n p q n' => [p q|n IHn p q n' Hn]; first by rewrite geq_max ltn0 andbF.
case: n' => [|n' Hn' /=]; first by rewrite geq_max ltn0 andbF.
have [//|p_neq0] := altP eqP; congr (_ :: _).
have [->|q_neq0] := altP (q =P 0); first by rewrite !aux0.
by apply: IHn; rewrite -ltnS (leq_trans _ Hn, leq_trans _ Hn') ?Hnext.
Qed.

Lemma mods_eq0 p q : (mods p q == [::]) = (p == 0).
Proof. by rewrite mods_rec; have [] := altP (p =P 0). Qed.

Lemma neq0_mods_rec p q : p != 0 -> mods p q = p :: mods q (next_mod p q).
Proof. by rewrite mods_rec => /negPf ->. Qed.

Lemma mods0p q : mods 0 q = [::].
Proof. by apply/eqP; rewrite mods_eq0. Qed.

Lemma modsp0 p : mods p 0 = if p == 0 then [::] else [::p].
Proof. by rewrite mods_rec mods0p. Qed.

Fixpoint changes (s : seq R) : nat :=
  (if s is a :: q then (a * (head 0 q) < 0)%R + changes q else 0)%N.

Definition changes_pinfty (p : seq {poly R}) := changes (map lead_coef p).
Definition changes_minfty (p : seq {poly R}) :=
  changes (map (fun p : {poly _} => (-1) ^+ (~~ odd (size p)) * lead_coef p) p).

Definition changes_poly (p : seq {poly R}) :=
  (changes_minfty p)%:Z - (changes_pinfty p)%:Z.
Definition changes_mods p q :=  changes_poly (mods p q).

Lemma changes_mods0p q : changes_mods 0 q = 0.
Proof. by rewrite /changes_mods /changes_poly mods0p. Qed.

Lemma changes_modsp0 p : changes_mods p 0 = 0.
Proof.
rewrite /changes_mods /changes_poly modsp0; have [//|p_neq0] := altP eqP.
by rewrite /changes_minfty /changes_pinfty /= !mulr0 ltrr.
Qed.

Lemma changes_mods_rec p q :
  changes_mods p q = crossR (p * q) + changes_mods q (next_mod p q).
Proof.
have [->|p0] := eqVneq p 0.
  by rewrite changes_mods0p mul0r crossR0 next_mod0p changes_modsp0.
have [->|q0] := eqVneq q 0.
  by rewrite changes_modsp0 mulr0 crossR0 changes_mods0p.
rewrite /changes_mods /changes_poly neq0_mods_rec //=.
rewrite !PoszD opprD addrACA; congr (_ + _); rewrite neq0_mods_rec //=.
rewrite /crossR /variation /sgp_pinfty /sgp_minfty.
rewrite mulr_signM size_mul // !lead_coefM.
rewrite polySpred // addSn [size q]polySpred // addnS /= !negbK.
rewrite -odd_add signr_odd; set s := _ ^+ _.
rewrite -!sgz_cp0 !(sgz_sgr, sgzM).
have: s != 0 by rewrite signr_eq0.
by move: p0 q0; rewrite -!lead_coef_eq0; do 3!case: sgzP=> _.
Qed.

Lemma changes_mods_cindex p q : changes_mods p q = cindexR q p.
Proof.
elim: mods {-2}p {-2}q (erefl (mods p q)) => [|r s IHs] {p q} p q hrpq.
  move/eqP: hrpq; rewrite mods_eq0 => /eqP ->.
  by rewrite changes_mods0p cindexRpC.
rewrite changes_mods_rec cindexR_rec IHs //.
by move: hrpq IHs; rewrite mods_rec; case: (p == 0) => // [] [].
Qed.

Definition taqR p q := changes_mods p (p^`() * q).

Lemma taq_taqR p q : taq (rootsR p) q = taqR p q.
Proof. by rewrite /taqR changes_mods_cindex taq_cindex. Qed.

Section ChangesItvMod_USELESS.
(* Not used anymore, but the content of this  section is *)
(* used in the LMCS 2012 paper and in Cyril's thesis     *)

Definition changes_horner (p : seq {poly R}) x :=
  changes (map (fun p => p.[x]) p).
Definition changes_itv_poly a b (p : seq {poly R}) :=
  (changes_horner p a)%:Z - (changes_horner p b)%:Z.

Definition changes_itv_mods a b p q :=  changes_itv_poly a b (mods p q).

Lemma changes_itv_mods0p a b q : changes_itv_mods a b 0 q = 0.
Proof.
by rewrite /changes_itv_mods /changes_itv_poly mods0p /changes_horner /= subrr.
Qed.

Lemma changes_itv_modsp0 a b p : changes_itv_mods a b p 0 = 0.
Proof.
rewrite /changes_itv_mods /changes_itv_poly modsp0 /changes_horner /=.
by have [//|p_neq0 /=] := altP eqP; rewrite !mulr0 ltrr.
Qed.

Lemma changes_itv_mods_rec a b : a < b -> forall p q,
  ~~ root (p * q) a -> ~~ root (p * q) b ->
  changes_itv_mods a b p q = cross (p * q) a b 
                          + changes_itv_mods a b q (next_mod p q).
Proof.
move=> lt_ab p q rpqa rpqb.
have [->|p0] := eqVneq p 0.
  by rewrite changes_itv_mods0p mul0r next_mod0p changes_itv_modsp0 cross0.
have [->|q0] := eqVneq q 0.
  by rewrite changes_itv_modsp0 mulr0 cross0 changes_itv_mods0p.
rewrite /changes_itv_mods /changes_itv_poly /changes_horner neq0_mods_rec //=.
rewrite !PoszD opprD addrACA; congr (_ + _); rewrite neq0_mods_rec //=.
move: rpqa rpqb; rewrite -!hornerM !rootE; move: (p * q) => r {p q p0 q0}.
by rewrite /cross /variation -![_ < _]sgz_cp0 sgzM; do 2!case: sgzP => _.
Qed.

Lemma changes_itv_mods_cindex a b : a < b -> forall p q,
  all (fun p => ~~ root p a) (mods p q) ->
  all (fun p => ~~ root p b) (mods p q) ->
  changes_itv_mods a b p q = cindex a b q p.
Proof.
move=> hab p q.
elim: mods {-2}p {-2}q (erefl (mods p q)) => [|r s IHs] {p q} p q hrpq.
  move/eqP: hrpq; rewrite mods_eq0 => /eqP ->.
  by rewrite changes_itv_mods0p cindexpC.
have p_neq0 : p != 0 by rewrite -(mods_eq0 p q) hrpq.
move: hrpq IHs; rewrite neq0_mods_rec //.
move=> [_ <-] IHs /= /andP[rpa Ha] /andP[rpb Hb].
move=> /(_ _ _ (erefl _) Ha Hb) in IHs.
have [->|q_neq0] := eqVneq q 0; first by rewrite changes_itv_modsp0 cindex0p.
move: Ha Hb; rewrite neq0_mods_rec //= => /andP[rqa _] /andP[rqb _].
rewrite cindex_rec 1?changes_itv_mods_rec;
by rewrite ?rootM ?negb_or ?rpa ?rpb ?rqa ?rqb // IHs.
Qed.

Definition taq_itv a b p q := changes_itv_mods a b p (p^`() * q).

Lemma taq_taq_itv a b :  a < b -> forall p q,
  all (fun p => p.[a] != 0) (mods p (p^`() * q)) ->
  all (fun p => p.[b] != 0) (mods p (p^`() * q)) ->
  taq (roots p a b) q = taq_itv a b p q.
Proof. by move=> *; rewrite /taq_itv changes_itv_mods_cindex // taq_cindex. Qed.

End ChangesItvMod_USELESS.

Definition tvecR p sq := let sg_tab := sg_tab (size sq) in
  \row_(i < 3^size sq) (taqR p (map (poly_comb sq) sg_tab)`_i).

Lemma tvec_tvecR sq p : tvec (rootsR p) sq = tvecR p sq.
Proof.
by rewrite /tvec /tvecR; apply/matrixP=> i j; rewrite !mxE taq_taqR.
Qed.

Lemma all_prodn_gt0 : forall (I : finType) r (P : pred I) (F : I -> nat),
  (\prod_(i <- r | P i) F i > 0)%N ->
  forall i, i \in r -> P i -> (F i > 0)%N.
Proof.
move=> I r P F; elim: r => [_|a r hr] //.
rewrite big_cons; case hPa: (P a).
  rewrite muln_gt0; case/andP=> Fa0; move/hr=> hF x.
  by rewrite in_cons; case/orP; [move/eqP-> | move/hF].
move/hr=> hF x; rewrite in_cons; case/orP; last by move/hF.
by move/eqP->; rewrite hPa.
Qed.

Definition taqsR p sq i : R :=
  (taqR p (map (poly_comb sq) (sg_tab (size sq)))`_i)%:~R.

Definition ccount_weak p sq : R :=
  let fix aux s (i : nat) := if i is i'.+1
    then aux (taqsR p sq i' * coefs R (size sq) i' + s) i'
    else s in aux 0 (3 ^ size sq)%N.

Lemma constraints1P (p : {poly R}) (sq : seq {poly R}) :
  (constraints (rootsR p) (sq) (nseq (size (sq)) 1))%:~R
  = ccount_weak p sq.
Proof.
rewrite constraints1_tvec; symmetry.
rewrite castmxE mxE /= /ccount_weak.
transitivity (\sum_(0 <= i < 3 ^ size sq) taqsR p sq i * coefs R (size sq) i).
  rewrite unlock /reducebig /= -foldr_map /= /index_iota subn0 foldr_map.
  elim: (3 ^ size sq)%N 0%R => [|n ihn] u //.
  by rewrite -[X in iota _ X]addn1 iota_add add0n /= foldr_cat ihn.
rewrite big_mkord; apply: congr_big=> // i _.
rewrite /taqsR /coefs /tvecR /=.
have o : 'I_(3 ^ size sq) by rewrite exp3n; apply: ord0.
rewrite (@nth_map _ o); last by rewrite size_enum_ord.
by rewrite !castmxE !cast_ord_id !mxE /= nth_ord_enum taq_taqR.
Qed.

Lemma ccount_weakP p sq : p != 0 ->
  reflect (exists x, (p.[x] == 0) && \big[andb/true]_(q <- sq) (q.[x] > 0))
  (ccount_weak p sq > 0).
Proof.
move=> p_neq0; rewrite -constraints1P /constraints ltr0n lt0n.
rewrite -(@pnatr_eq0 [numDomainType of int]) natr_sum psumr_eq0 //.
rewrite -has_predC /=.
apply: (iffP hasP) => [[x rpx /= prod_neq0]|[x /andP[rpx]]].
  exists x; rewrite -rootE [root _ _]roots_on_rootsR // rpx /=.
  rewrite big_seq big1 => // q Hq.
  move: prod_neq0; rewrite pnatr_eq0 -lt0n => /all_prodn_gt0.
  have := index_mem q sq; rewrite Hq => Hoq.
  pose oq := Ordinal Hoq => /(_ oq).
  rewrite mem_index_enum => /(_ isT isT) /=.
  by rewrite nth_nseq index_mem Hq nth_index // lt0b sgz_cp0.
rewrite big_all => /allP Hsq.
exists x => /=; first by rewrite -roots_on_rootsR.
rewrite pnatr_eq0 -lt0n prodn_gt0 => // i; rewrite nth_nseq ltn_ord lt0b.
by rewrite sgz_cp0 Hsq // mem_nth.
Qed.

Lemma myprodf_eq0 (S : idomainType)(I : eqType) (r : seq I) P (F : I -> S) :
  reflect (exists2 i, ((i \in r) && (P i)) & (F i == 0))
  (\prod_(i <- r| P i) F i == 0).
Proof.
apply: (iffP idP) => [|[i Pi /eqP Fi0]]; last first.
  by case/andP: Pi => ri Pi; rewrite (big_rem _ ri) /= Pi Fi0 mul0r.
elim: r => [|i r IHr]; first by rewrite big_nil oner_eq0.
rewrite big_cons /=; have [Pi | ?] := ifP.
  rewrite mulf_eq0; case/orP=> [Fi0|]; first by exists i => //; rewrite mem_head.
  by case/IHr=> j /andP [rj Pj] Fj; exists j; rewrite // in_cons rj orbT.
by case/IHr=> j  /andP [rj Pj] Fj; exists j; rewrite // in_cons rj orbT.
Qed.

Definition bounding_poly (sq : seq {poly R}) := (\prod_(q <- sq) q)^`().

Lemma bounding_polyP (sq : seq {poly R}) :
  [\/ \big[andb/true]_(q <- sq) (lead_coef q > 0),
      \big[andb/true]_(q <- sq) ((-1)^+(size q).-1 * (lead_coef q) > 0) |
   exists x,
   ((bounding_poly sq).[x] == 0) && \big[andb/true]_(q <- sq) (q.[x] > 0)]
    <-> exists x, \big[andb/true]_(q <- sq) (q.[x] > 0).
Proof.
split=> [|[x]].
  case; last by move=> [x /andP [? h]]; exists x; rewrite h.
    rewrite big_all => /allP hsq.
    have sqn0 : {in sq, forall q, q != 0}.
      by move=> q' /= /hsq; apply: contraL=> /eqP->; rewrite lead_coef0 ltrr.
    pose qq := \prod_(q <- sq) q.
    have pn0 : qq != 0.
      by apply/negP=> /myprodf_eq0 [] q; rewrite andbT => /sqn0 /negPf ->.
    pose b := cauchy_bound qq; exists b.
    rewrite big_all; apply/allP=> r hr; have:= hsq r hr.
    rewrite -!sgr_cp0=> /eqP <-; apply/eqP.
    apply: (@sgp_pinftyP _ b); last by rewrite boundl_in_itv.
    move=> z Hz /=; have: ~~ root qq z by rewrite ge_cauchy_bound.
    by rewrite /root /qq horner_prod prodf_seq_neq0 => /allP /(_ _ hr).
  rewrite big_all => /allP hsq.
  have sqn0 : {in sq, forall q, q != 0}.
    move=> q' /= /hsq; apply: contraL=> /eqP->.
    by rewrite lead_coef0 mulr0 ltrr.
  pose qq := \prod_(q <- sq) q.
  have pn0 : qq != 0.
    by apply/negP=> /myprodf_eq0 [] q; rewrite andbT => /sqn0 /negPf ->.
  pose b := - cauchy_bound qq; exists b.
  rewrite big_all; apply/allP=> r hr; have:= hsq r hr.
  rewrite -!sgr_cp0=> /eqP <-; apply/eqP.
  apply: (@sgp_minftyP _ b); last by rewrite boundr_in_itv.
  move=> z Hz /=; have: ~~ root qq z by rewrite le_cauchy_bound.
  by rewrite /root /qq horner_prod prodf_seq_neq0 => /allP /(_ _ hr).
rewrite /bounding_poly; set q := \prod_(q <- _) _.
rewrite big_all => /allP hsq; set bnd := cauchy_bound q.
have sqn0 : {in sq, forall q, q != 0}.
  by move=> q' /= /hsq; apply: contraL=> /eqP->; rewrite horner0 ltrr.
have [/eqP|q_neq0] := eqVneq q 0.
   by rewrite prodf_seq_eq0=> /hasP [q' /= /sqn0 /negPf->].
have genroot y : {in sq, forall r, ~~ root q y -> ~~ root r y}.
  rewrite /root /q => r r_sq.
  by rewrite horner_prod prodf_seq_neq0 => /allP /(_ _ r_sq).
case: (next_rootP q x bnd) q_neq0; [by move->; rewrite eqxx| |]; last first.
  move=> _ q_neq0 _ Hq _.
  suff -> : \big[andb/true]_(q1 <- sq) (0 < lead_coef q1) by constructor.
  rewrite big_all; apply/allP=> r hr; have rxp := hsq r hr.
  rewrite -sgr_cp0 -/(sgp_pinfty _).
  rewrite -(@sgp_pinftyP _ x _ _ x) ?boundl_in_itv ?sgr_cp0 //.
  move=> z; rewrite (@itv_splitU _ x true) /= ?boundl_in_itv //.
  rewrite itv_xx /= inE => /orP [/eqP->|]; first by rewrite /root gtr_eqF.
  have [x_b|b_x] := ltrP x bnd.
    rewrite (@itv_splitU _ bnd false) /=; last by rewrite inE x_b.
    move=> /orP [] Hz; rewrite genroot //;
    by [rewrite Hq|rewrite ge_cauchy_bound].
  by move=> Hz; rewrite genroot // ge_cauchy_bound // (subitvP _ Hz) //= b_x.
move=> y1 _ rqy1 hy1xb hy1.
case: (prev_rootP q (- bnd) x); [by move->; rewrite eqxx| |]; last first.
  move=> _ q_neq0 _ Hq _. (* assia : what is the use of c ? *)
  suff -> : \big[andb/true]_(q1 <- sq) (0 < (-1) ^+ (size q1).-1 * lead_coef q1).
    by constructor 2.
  rewrite big_all; apply/allP=> r hr; have rxp := hsq r hr.
  rewrite -sgr_cp0 -/(sgp_minfty _).
  rewrite -(@sgp_minftyP _ x _ _ x) ?boundr_in_itv ?sgr_cp0 //.
  move=> z; rewrite (@itv_splitU _ x false) /= ?boundr_in_itv //.
  rewrite itv_xx => /orP [/=|/eqP->]; last by rewrite /root gtr_eqF.
  have [b_x|x_b] := ltrP (- bnd) x.
    rewrite (@itv_splitU _ (- bnd) true) /=; last by rewrite inE b_x.
    move=> /orP [] Hz; rewrite genroot //;
    by [rewrite Hq|rewrite le_cauchy_bound].
  by move=> Hz; rewrite genroot // le_cauchy_bound // (subitvP _ Hz) //= x_b.
move=> y2 _ rqy2 hy2xb hy2 q_neq0.
have lty12 : y2 < y1.
  by apply: (@ltr_trans _ x); rewrite 1?(itvP hy1xb) 1?(itvP hy2xb).
have : q.[y2] = q.[y1] by rewrite rqy1 rqy2.
case/(rolle lty12) => z hz rz; constructor 3; exists z.
rewrite rz eqxx /= big_all; apply/allP => r r_sq.
have xy : x \in `]y2, y1[ by rewrite inE 1?(itvP hy1xb) 1?(itvP hy2xb).
rewrite -sgr_cp0 (@polyrN0_itv _ `]y2, y1[ _ _ x) ?sgr_cp0 ?hsq // => t.
rewrite (@itv_splitU2 _ x) // => /or3P [/hy2|/eqP->|/hy1]; do ?exact: genroot.
by rewrite rootE gtr_eqF ?hsq.
Qed.

Lemma size_prod_eq1 (sq : seq {poly R}) :
  reflect (forall q, q \in sq -> size q = 1%N)  (size (\prod_(q0 <- sq) q0) == 1%N).
Proof.
apply: (iffP idP).
  elim: sq => [| q sq ih]; first by move=> _ q; rewrite in_nil.
  rewrite big_cons; case: (altP (q =P 0)) => [-> | qn0].
    by rewrite mul0r size_poly0.
  case: (altP ((\prod_(j <- sq) j) =P 0)) => [-> | pn0].
    by rewrite mulr0 size_poly0.
  rewrite size_mul //; case: (ltngtP (size q) 1).
  - by rewrite ltnS leqn0 size_poly_eq0 (negPf qn0).
  - case: (size q) => [|n] //; case: n => [|n] // _; rewrite !addSn /= eqSS.
    by rewrite addn_eq0 size_poly_eq0 (negPf pn0) andbF.
  - move=> sq1; case: (ltngtP (size (\prod_(j <- sq) j)) 1).
    + by rewrite ltnS leqn0 size_poly_eq0 (negPf pn0).
    + case: (size (\prod_(j <- sq) j)) => [|n] //; case: n => [|n] // _.
      by rewrite !addnS /= eqSS addn_eq0 size_poly_eq0 (negPf qn0).
    move=> sp1 _ p; rewrite in_cons; case/orP => [/eqP -> |] //; apply: ih.
    by apply/eqP.
elim: sq => [| q sq ih] hs; first by rewrite big_nil size_poly1 eqxx.
case: (altP (q =P 0)) => [ | qn0].
  by  move/eqP; rewrite -size_poly_eq0 hs ?mem_head.
case: (altP ((\prod_(q0 <- sq) q0) =P 0)) => [ | pn0].
  move/eqP; rewrite -size_poly_eq0 (eqP (ih _)) // => t ht; apply: hs.
  by rewrite in_cons ht orbT.
rewrite big_cons size_mul // (eqP (ih _)) //; last first.
  by move=> t ht; apply: hs; rewrite in_cons ht orbT.
by rewrite addnS addn0; apply/eqP; apply: hs; apply: mem_head.
Qed.

Definition ccount_gt0 (sp sq : seq {poly R}) :=
  let p := \big[@rgcdp _/0%R]_(p <- sp) p in
    if p != 0 then 0 < ccount_weak p sq
    else let bq := bounding_poly sq in
	[|| \big[andb/true]_(q <- sq)(lead_coef q > 0) ,
            \big[andb/true]_(q <- sq)((-1)^+(size q).-1 *(lead_coef q) > 0) |
         0 < ccount_weak bq sq].

Lemma ccount_gt0P (sp sq : seq {poly R}) :
  reflect (exists x, \big[andb/true]_(p <- sp) (p.[x] == 0)
                  && \big[andb/true]_(q <- sq) (q.[x] > 0))
    (ccount_gt0 sp sq).
Proof.
rewrite /ccount_gt0; case: (boolP (_ == 0))=> hsp /=; last first.
  apply: (iffP (ccount_weakP _ _)) => // [] [x Hx]; exists x;
  by move: Hx; rewrite -rootE root_bigrgcd -big_all.
apply: (@equivP (exists x, \big[andb/true]_(q <- sq) (0 < q.[x]))); last first.
  split=> [] [x Hx]; exists x; rewrite ?Hx ?andbT; do ?by case/andP: Hx.
  move: hsp; rewrite (big_morph  _ (@rgcdp_eq0 _) (eqxx _)) !big_all.
  by move=> /allP Hsp; apply/allP => p /Hsp /eqP ->; rewrite horner0.
have [|bq_neq0] := boolP (bounding_poly sq == 0).
  rewrite /bounding_poly -derivn1 -derivn_poly0 => ssq_le1.
  rewrite -constraints1P (size1_polyC ssq_le1) derivnC /= rootsRC.
  rewrite /constraints big_nil ltrr orbF.
  move: ssq_le1; rewrite leq_eqVlt ltnS leqn0 orbC.
  have [|_ /=] := boolP (_ == _).
    rewrite size_poly_eq0 => /eqP sq_eq0; move/eqP: (sq_eq0).
    rewrite prodf_seq_eq0 => /hasP /sig2W [q /= q_sq] /eqP q_eq0.
    move: q_sq; rewrite q_eq0 => sq0 _ {q q_eq0}.
    set f := _ || _; suff -> : f = false; move: @f => /=.
      constructor => [] [x]; rewrite big_all.
      by move=> /allP /(_ _ sq0); rewrite horner0 ltrr.
    apply: negbTE; rewrite !negb_or !big_all -!has_predC.
    apply/andP; split; apply/hasP;
    by exists 0; rewrite //= ?lead_coef0 ?mulr0 ltrr.
  move=> /size_prod_eq1 Hsq.
  have {Hsq} Hsq q : q \in sq -> q = (lead_coef q)%:P.
    by move=> /Hsq sq1; rewrite [q]size1_polyC ?sq1 // lead_coefC.
  apply: (@equivP (\big[andb/true]_(q <- sq) (0 < lead_coef q))); last first.
    split; [move=> sq0; exists 0; move: sq0|move=> [x]];
    rewrite !big_all => /allP H; apply/allP => q q_sq; have:= H _ q_sq;
    by rewrite [q]Hsq ?lead_coefC ?hornerC.
  have [] := boolP (\big[andb/true]_(q <- _) (0 < lead_coef q)).
    by constructor.
  rewrite !big_all -has_predC => /hasP sq0; apply: (iffP allP) => //=.
  move: sq0 => [q q_sq /= lq_gt0 /(_ _ q_sq)].
  rewrite [q]Hsq ?size_polyC ?lead_coefC //.
  by case: (_ != 0); rewrite /= expr0 mul1r ?(negPf lq_gt0).
apply: (iffP or3P); rewrite -bounding_polyP;
case; do ?by [constructor 1|constructor 2];
by move/(ccount_weakP _ bq_neq0); constructor 3.
Qed.

End QeRcfTh.

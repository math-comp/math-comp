(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrbool ssrfun eqtype ssrnat seq div choice fintype.
From mathcomp
Require Import tuple finfun bigop finset prime binomial ssralg poly polydiv.
From mathcomp
Require Import fingroup perm morphism quotient gproduct finalg zmodp cyclic.
From mathcomp
Require Import matrix mxalgebra mxpoly polyXY vector falgebra fieldext.

(******************************************************************************)
(* This file provides a theory of separable and inseparable field extensions. *)
(*                                                                            *)
(*      separable_poly p <=> p has no multiple roots in any field extension.  *)
(* separable_element K x <=> the minimal polynomial of x over K is separable. *)
(*         separable K E <=> every member of E is separable over K.           *)
(* separable_generator K E == some x \in E that generates the largest         *)
(*                           subfield K[x] that is separable over K.          *)
(* purely_inseparable_element K x <=> there is a [char L].-nat n such that    *)
(*                           x ^+ n \in K.                                    *)
(* purely_inseparable K E <=> every member of E is purely inseparable over K. *)
(*                                                                            *)
(*  Derivations are introduced to prove the adjoin_separableP Lemma:          *)
(*        Derivation K D <=> the linear operator D satifies the Leibniz       *)
(*                           product rule inside K.                           *)
(* extendDerivation x D K == given a derivation D on K and a separable        *)
(*                           element x over K, this function returns the      *)
(*                           unique extension of D to K(x).                   *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory.

Section SeparablePoly.

Variable R : idomainType.
Implicit Types p q d u v : {poly R}.

Definition separable_poly p := coprimep p p^`().

Local Notation separable := separable_poly.
Local Notation lcn_neq0 := (Pdiv.Idomain.lc_expn_scalp_neq0 _).

Lemma separable_poly_neq0 p : separable p -> p != 0.
Proof.
by apply: contraTneq => ->; rewrite /separable deriv0 coprime0p eqp01.
Qed.

Lemma poly_square_freeP p :
  (forall u v, u * v %| p -> coprimep u v)
  <-> (forall u, size u != 1%N -> ~~ (u ^+ 2 %| p)).
Proof.
split=> [sq'p u | sq'p u v dvd_uv_p].
  by apply: contra => /sq'p; rewrite coprimepp.
rewrite coprimep_def (contraLR (sq'p _)) // (dvdp_trans _ dvd_uv_p) //.
by rewrite dvdp_mul ?dvdp_gcdl ?dvdp_gcdr.
Qed.

Lemma separable_polyP {p} :
  reflect [/\ forall u v, u * v %| p -> coprimep u v
            & forall u, u %| p -> 1 < size u -> u^`() != 0]
          (separable p).
Proof.
apply: (iffP idP) => [sep_p | [sq'p nz_der1p]].
  split=> [u v | u u_dv_p]; last first.
    apply: contraTneq => u'0; rewrite -leqNgt -(eqnP sep_p).
    rewrite dvdp_leq -?size_poly_eq0 ?(eqnP sep_p) // dvdp_gcd u_dv_p.
    have /dvdp_scaler <-: lead_coef u ^+ scalp p u != 0 by rewrite lcn_neq0.
    by rewrite -derivZ -Pdiv.Idomain.divpK //= derivM u'0 mulr0 addr0 dvdp_mull.
  rewrite Pdiv.Idomain.dvdp_eq mulrCA mulrA; set c := _ ^+ _ => /eqP Dcp.
  have nz_c: c != 0 by rewrite lcn_neq0.
  move: sep_p; rewrite coprimep_sym -[separable _](coprimep_scalel _ _ nz_c).
  rewrite -(coprimep_scaler _ _ nz_c) -derivZ Dcp derivM coprimep_mull.
  by rewrite coprimep_addl_mul !coprimep_mulr -andbA => /and4P[].
rewrite /separable coprimep_def eqn_leq size_poly_gt0; set g := gcdp _ _.
have nz_g: g != 0.
  rewrite -dvd0p dvdp_gcd -(mulr0 0); apply/nandP; left.
  by have /poly_square_freeP-> := sq'p; rewrite ?size_poly0.
have [g_p]: g %| p /\ g %| p^`() by rewrite dvdp_gcdr ?dvdp_gcdl.
pose c := lead_coef g ^+ scalp p g; have nz_c: c != 0 by rewrite lcn_neq0.
have Dcp: c *: p = p %/ g * g by rewrite Pdiv.Idomain.divpK.
rewrite nz_g andbT leqNgt -(dvdp_scaler _ _ nz_c) -derivZ Dcp derivM.
rewrite dvdp_addr; last by rewrite dvdp_mull.
rewrite Gauss_dvdpr; last by rewrite sq'p // mulrC -Dcp dvdp_scalel.
by apply: contraL => /nz_der1p nz_g'; rewrite gtNdvdp ?nz_g' ?lt_size_deriv.
Qed.

Lemma separable_coprime p u v : separable p -> u * v %| p -> coprimep u v.
Proof. by move=> /separable_polyP[sq'p _] /sq'p. Qed.

Lemma separable_nosquare p u k :
  separable p -> 1 < k -> size u != 1%N -> (u ^+ k %| p) = false.
Proof.
move=> /separable_polyP[/poly_square_freeP sq'p _] /subnKC <- /sq'p.
by apply: contraNF; apply: dvdp_trans; rewrite exprD dvdp_mulr.
Qed.

Lemma separable_deriv_eq0 p u :
  separable p -> u %| p -> 1 < size u -> (u^`() == 0) = false.
Proof. by move=> /separable_polyP[_ nz_der1p] u_p /nz_der1p/negPf->. Qed.

Lemma dvdp_separable p q : q %| p -> separable p -> separable q.
Proof.
move=> /(dvdp_trans _)q_dv_p /separable_polyP[sq'p nz_der1p].
by apply/separable_polyP; split=> [u v /q_dv_p/sq'p | u /q_dv_p/nz_der1p].
Qed.

Lemma separable_mul p q :
  separable (p * q) = [&& separable p, separable q & coprimep p q].
Proof.
apply/idP/and3P => [sep_pq | [sep_p seq_q co_pq]].
  rewrite !(dvdp_separable _ sep_pq) ?dvdp_mulIr ?dvdp_mulIl //.
  by rewrite (separable_coprime sep_pq).
rewrite /separable derivM coprimep_mull {1}addrC mulrC !coprimep_addl_mul.
by rewrite !coprimep_mulr (coprimep_sym q p) co_pq !andbT; apply/andP.
Qed.

Lemma eqp_separable p q : p %= q -> separable p = separable q.
Proof. by case/andP=> p_q q_p; apply/idP/idP=> /dvdp_separable->. Qed.

Lemma separable_root p x :
  separable (p * ('X - x%:P)) = separable p && ~~ root p x.
Proof.
rewrite separable_mul; apply: andb_id2l => seq_p.
by rewrite /separable derivXsubC coprimep1 coprimep_XsubC.
Qed.

Lemma separable_prod_XsubC (r : seq R) :
  separable (\prod_(x <- r) ('X - x%:P)) = uniq r.
Proof.
elim: r => [|x r IH]; first by rewrite big_nil /separable_poly coprime1p.
by rewrite big_cons mulrC separable_root IH root_prod_XsubC andbC.
Qed.

Lemma make_separable p : p != 0 -> separable (p %/ gcdp p p^`()).
Proof.
set g := gcdp p p^`() => nz_p; apply/separable_polyP.
have max_dvd_u (u : {poly R}): 1 < size u -> exists k, ~~ (u ^+ k %| p).
  move=> u_gt1; exists (size p); rewrite gtNdvdp // polySpred //.
  by rewrite -(ltn_subRL 1) subn1 size_exp leq_pmull // -(subnKC u_gt1).
split=> [|u u_pg u_gt1]; last first.
  apply/eqP=> u'0 /=; have [k /negP[]] := max_dvd_u u u_gt1.
  elim: k => [|k IHk]; first by rewrite dvd1p.
  suffices: u ^+ k.+1 %| (p %/ g) * g.
    by rewrite Pdiv.Idomain.divpK ?dvdp_gcdl // dvdp_scaler ?lcn_neq0.
  rewrite exprS dvdp_mul // dvdp_gcd IHk //=.
  suffices: u ^+ k %| (p %/ u ^+ k * u ^+ k)^`().
    by rewrite Pdiv.Idomain.divpK // derivZ dvdp_scaler ?lcn_neq0.
  by rewrite !derivCE u'0 mul0r mul0rn mulr0 addr0 dvdp_mull.
have pg_dv_p: p %/ g %| p by rewrite divp_dvd ?dvdp_gcdl.
apply/poly_square_freeP=> u; rewrite neq_ltn ltnS leqn0 size_poly_eq0.
case/predU1P=> [-> | /max_dvd_u[k]].
  by apply: contra nz_p; rewrite expr0n -dvd0p => /dvdp_trans->.
apply: contra => u2_dv_pg; case: k; [by rewrite dvd1p | elim=> [|n IHn]].
  exact: dvdp_trans (dvdp_mulr _ _) (dvdp_trans u2_dv_pg pg_dv_p).
suff: u ^+ n.+2 %| (p %/ g) * g.
  by rewrite Pdiv.Idomain.divpK ?dvdp_gcdl // dvdp_scaler ?lcn_neq0.
rewrite -add2n exprD dvdp_mul // dvdp_gcd.
rewrite (dvdp_trans _ IHn) ?exprS ?dvdp_mull //=.
suff: u ^+ n %| ((p %/ u ^+ n.+1) * u ^+ n.+1)^`().
  by rewrite Pdiv.Idomain.divpK // derivZ dvdp_scaler ?lcn_neq0.
by rewrite !derivCE dvdp_add // -1?mulr_natl ?exprS !dvdp_mull.
Qed.

End SeparablePoly.

Arguments separable_polyP {R p}.

Lemma separable_map (F : fieldType) (R : idomainType)
                    (f : {rmorphism F -> R}) (p : {poly F}) :
  separable_poly (map_poly f p) = separable_poly p.
Proof.
by rewrite /separable_poly deriv_map /coprimep -gcdp_map size_map_poly.
Qed.

Section InfinitePrimitiveElementTheorem.

Local Notation "p ^ f" := (map_poly f p) : ring_scope.

Variables (F L : fieldType) (iota : {rmorphism F -> L}).
Variables (x y : L) (p : {poly F}).
Hypotheses (nz_p : p != 0) (px_0 : root (p ^ iota) x).

Let inFz z w := exists q, (q ^ iota).[z] = w.

Lemma large_field_PET q :
    root (q ^ iota) y -> separable_poly q ->
  exists2 r, r != 0
  & forall t (z := iota t * y - x), ~~ root r (iota t) -> inFz z x /\ inFz z y.
Proof.
move=> qy_0 sep_q; have nz_q := separable_poly_neq0 sep_q.
have /factor_theorem[q0 Dq] := qy_0.
set p1 := p ^ iota \Po ('X + x%:P); set q1 := q0 \Po ('X + y%:P).
have nz_p1: p1 != 0.
  apply: contraNneq nz_p => /(canRL (fun r => comp_polyXaddC_K r _))/eqP.
  by rewrite comp_poly0 map_poly_eq0.
have{sep_q} nz_q10: q1.[0] != 0.
  move: sep_q; rewrite -(separable_map iota) Dq separable_root => /andP[_].
  by rewrite horner_comp !hornerE.
have nz_q1: q1 != 0 by apply: contraNneq nz_q10 => ->; rewrite horner0.
pose p2 := p1 ^ polyC \Po ('X * 'Y); pose q2 := q1 ^ polyC.
have /Bezout_coprimepP[[u v]]: coprimep p2 q2.
  rewrite coprimep_def eqn_leq leqNgt andbC size_poly_gt0 gcdp_eq0 poly_XmY_eq0.
  by rewrite map_polyC_eq0 (negPf nz_p1) -resultant_eq0 div_annihilant_neq0.
rewrite -size_poly_eq1 => /size_poly1P[r nzr Dr]; exists r => {nzr}// t z nz_rt.
have [r1 nz_r1 r1z_0]: algebraicOver iota z.
  apply/algebraic_sub; last by exists p.
  by apply: algebraic_mul; [apply: algebraic_id | exists q].
pose Fz := subFExtend iota z r1; pose kappa : Fz -> L := subfx_inj.
pose kappa' := inj_subfx iota z r1.
have /eq_map_poly Diota: kappa \o kappa' =1 iota.
  by move=> w; rewrite /kappa /= subfx_inj_eval // map_polyC hornerC.
suffices [y3]: exists y3, y = kappa y3.
  have [q3 ->] := subfxE y3; rewrite /kappa subfx_inj_eval // => Dy.
  split; [exists (t *: q3 - 'X) | by exists q3].
  by rewrite rmorphB linearZ /= map_polyX !hornerE -Dy opprB addrC addrNK.
pose p0 := p ^ iota \Po (iota t *: 'X - z%:P).
have co_p0_q0: coprimep p0 q0.
  pose at_t := horner_eval (iota t); have at_t0: at_t 0 = 0 by apply: rmorph0.
  have /map_polyK polyCK: cancel polyC at_t by move=> w; apply: hornerC.
  have ->: p0 = p2 ^ at_t \Po ('X - y%:P).
    rewrite map_comp_poly polyCK // rmorphM /= map_polyC map_polyX /=.
    rewrite horner_evalE hornerX.
    rewrite -!comp_polyA comp_polyM comp_polyD !comp_polyC !comp_polyX.
    by rewrite mulrC mulrBr mul_polyC addrAC -addrA -opprB -rmorphM -rmorphB.
  have ->: q0 = q2 ^ at_t \Po ('X - y%:P) by rewrite polyCK ?comp_polyXaddC_K.
  apply/coprimep_comp_poly/Bezout_coprimepP; exists (u ^ at_t, v ^ at_t).
  by rewrite -!rmorphM -rmorphD Dr /= map_polyC polyC_eqp1.
have{co_p0_q0}: gcdp p0 (q ^ iota) %= 'X - y%:P.
  rewrite /eqp Dq (eqp_dvdl _ (Gauss_gcdpr _ _)) // dvdp_gcdr dvdp_gcd.
  rewrite dvdp_mull // -root_factor_theorem rootE horner_comp !hornerE.
  by rewrite opprB addrC subrK.
have{p0} [p3 ->]: exists p3, p0 = p3 ^ kappa.
  exists (p ^ kappa' \Po (kappa' t *: 'X - (subfx_eval iota z r1 'X)%:P)).
  rewrite map_comp_poly rmorphB linearZ /= map_polyC map_polyX /=.
  rewrite !subfx_inj_eval // map_polyC hornerC map_polyX hornerX.
  by rewrite -map_poly_comp Diota.
rewrite -Diota map_poly_comp -gcdp_map /= -/kappa.
move: (gcdp _ _) => r3 /eqpf_eq[c nz_c Dr3].
exists (- (r3`_0 / r3`_1)); rewrite [kappa _]rmorphN fmorph_div -!coef_map Dr3.
by rewrite !coefZ polyseqXsubC mulr1 mulrC mulKf ?opprK.
Qed.

Lemma char0_PET (q : {poly F}) :
    q != 0 -> root (q ^ iota) y -> [char F] =i pred0 ->
  exists n, let z := y *+ n - x in inFz z x /\ inFz z y.
Proof.
move=> nz_q qy_0 /charf0P charF0.
without loss{nz_q} sep_q: q qy_0 / separable_poly q.
  move=> IHq; apply: IHq (make_separable nz_q).
  have /dvdpP[q1 Dq] := dvdp_gcdl q q^`().
  rewrite {1}Dq mulpK ?gcdp_eq0; last by apply/nandP; left.
  have [n [r nz_ry Dr]] := multiplicity_XsubC (q ^ iota) y.
  rewrite map_poly_eq0 nz_q /= in nz_ry.
  case: n => [|n] in Dr; first by rewrite Dr mulr1 (negPf nz_ry) in qy_0.
  have: ('X - y%:P) ^+ n.+1 %| q ^ iota by rewrite Dr dvdp_mulIr.
  rewrite Dq rmorphM /= gcdp_map -(eqp_dvdr _ (gcdp_mul2l _ _ _)) -deriv_map Dr.
  rewrite dvdp_gcd derivM deriv_exp derivXsubC mul1r !mulrA dvdp_mulIr /=.
  rewrite mulrDr mulrA dvdp_addr ?dvdp_mulIr // exprS -scaler_nat -!scalerAr.
  rewrite dvdp_scaler -?(rmorph_nat iota) ?fmorph_eq0 ?charF0 //.
  rewrite mulrA dvdp_mul2r ?expf_neq0 ?polyXsubC_eq0 //.
  by rewrite Gauss_dvdpl ?dvdp_XsubCl // coprimep_sym coprimep_XsubC.
have [r nz_r PETxy] := large_field_PET qy_0 sep_q.
pose ts := mkseq (fun n => iota n%:R) (size r).
have /(max_ring_poly_roots nz_r)/=/implyP: uniq_roots ts.
  rewrite uniq_rootsE mkseq_uniq // => m n eq_mn; apply/eqP; rewrite eqn_leq.
  wlog suffices: m n eq_mn / m <= n by move=> IHmn; rewrite !IHmn.
  move/fmorph_inj/eqP: eq_mn; rewrite -subr_eq0 leqNgt; apply: contraL => lt_mn.
  by rewrite -natrB ?(ltnW lt_mn) // charF0 -lt0n subn_gt0.
rewrite size_mkseq ltnn implybF all_map => /allPn[n _ /= /PETxy].
by rewrite rmorph_nat mulr_natl; exists n.
Qed.

End InfinitePrimitiveElementTheorem.

Section Separable.

Variables (F : fieldType) (L : fieldExtType F).
Implicit Types (U V W : {vspace L}) (E K M : {subfield L}) (D : 'End(L)).

Section Derivation.

Variables (K : {vspace L}) (D : 'End(L)).

(* A deriviation only needs to be additive and satify Lebniz's law, but all   *)
(* the deriviations used here are going to be linear, so we only define       *)
(* the Derivation predicate for linear endomorphisms.                         *)
Definition Derivation (s := vbasis K) : bool :=
  all (fun u => all (fun v => D (u * v) == D u * v + u * D v) s) s.

Hypothesis derD : Derivation.

Lemma Derivation_mul : {in K &, forall u v, D (u * v) = D u * v + u * D v}.
Proof.
move=> u v /coord_vbasis-> /coord_vbasis->.
rewrite !(mulr_sumr, linear_sum) -big_split; apply: eq_bigr => /= j _.
rewrite !mulr_suml linear_sum -big_split; apply: eq_bigr => /= i _.
rewrite !(=^~ scalerAl, linearZZ) -!scalerAr linearZZ -!scalerDr !scalerA /=.
by congr (_ *: _); apply/eqP; rewrite (allP (allP derD _ _)) ?memt_nth.
Qed.

Lemma Derivation_mul_poly (Dp := map_poly D) :
  {in polyOver K &, forall p q, Dp (p * q) = Dp p * q + p * Dp q}.
Proof.
move=> p q Kp Kq; apply/polyP=> i; rewrite {}/Dp coefD coef_map /= !coefM.
rewrite linear_sum -big_split; apply: eq_bigr => /= j _.
by rewrite !{1}coef_map Derivation_mul ?(polyOverP _).
Qed.

End Derivation.

Lemma DerivationS E K D : (K <= E)%VS -> Derivation E D -> Derivation K D.
Proof.
move/subvP=> sKE derD; apply/allP=> x Kx; apply/allP=> y Ky; apply/eqP.
by rewrite (Derivation_mul derD) ?sKE // vbasis_mem.
Qed.

Section DerivationAlgebra.

Variables (E : {subfield L}) (D : 'End(L)).
Hypothesis derD : Derivation E D.

Lemma Derivation1 : D 1 = 0.
Proof.
apply: (addIr (D (1 * 1))); rewrite add0r {1}mul1r.
by rewrite (Derivation_mul derD) ?mem1v // mulr1 mul1r.
Qed.

Lemma Derivation_scalar x : x \in 1%VS -> D x = 0.
Proof. by case/vlineP=> y ->; rewrite linearZ /= Derivation1 scaler0. Qed.

Lemma Derivation_exp x m : x \in E -> D (x ^+ m) = x ^+ m.-1 *+ m * D x.
Proof.
move=> Ex; case: m; first by rewrite expr0 mulr0n mul0r Derivation1.
elim=> [|m IHm]; first by rewrite mul1r.
rewrite exprS (Derivation_mul derD) //; last by apply: rpredX.
by rewrite mulrC IHm mulrA mulrnAr -exprS -mulrDl.
Qed.

Lemma Derivation_horner p x :
    p \is a polyOver E -> x \in E ->
  D p.[x] = (map_poly D p).[x] + p^`().[x] * D x.
Proof.
move=> Ep Ex; elim/poly_ind: p Ep => [|p c IHp] /polyOverP EpXc.
  by rewrite !(raddf0, horner0) mul0r add0r.
have Ep: p \is a polyOver E.
  by apply/polyOverP=> i; have:= EpXc i.+1; rewrite coefD coefMX coefC addr0.
have->: map_poly D (p * 'X + c%:P) = map_poly D p * 'X + (D c)%:P.
  apply/polyP=> i; rewrite !(coefD, coefMX, coef_map) /= linearD /= !coefC.
  by rewrite !(fun_if D) linear0.
rewrite derivMXaddC !hornerE mulrDl mulrAC addrAC linearD /=; congr (_ + _).
by rewrite addrCA -mulrDl -IHp // addrC (Derivation_mul derD) ?rpred_horner.
Qed.

End DerivationAlgebra.

Definition separable_element U x := separable_poly (minPoly U x).

Section SeparableElement.

Variables (K : {subfield L}) (x : L).
(* begin hide *)
Let sKxK : (K <= <<K; x>>)%VS := subv_adjoin K x.
Let Kx_x : x \in <<K; x>>%VS := memv_adjoin K x.
(* end hide *)

Lemma separable_elementP :  
  reflect (exists f, [/\ f \is a polyOver K, root f x & separable_poly f])
          (separable_element K x).
Proof.
apply: (iffP idP) => [sep_x | [f [Kf /(minPoly_dvdp Kf)/dvdpP[g ->]]]].
  by exists (minPoly K x); rewrite minPolyOver root_minPoly.
by rewrite separable_mul => /and3P[].
Qed.

Lemma base_separable : x \in K -> separable_element K x.
Proof.
move=> Kx; apply/separable_elementP; exists ('X - x%:P).
by rewrite polyOverXsubC root_XsubC /separable_poly !derivCE coprimep1.
Qed.

Lemma separable_nz_der : separable_element K x = ((minPoly K x)^`() != 0).
Proof.
rewrite /separable_element /separable_poly.
apply/idP/idP=> [|nzPx'].
  by apply: contraTneq => ->; rewrite coprimep0 -size_poly_eq1 size_minPoly.
have gcdK : gcdp (minPoly K x) (minPoly K x)^`() \in polyOver K.
  by rewrite gcdp_polyOver ?polyOver_deriv // minPolyOver.
rewrite -gcdp_eqp1 -size_poly_eq1 -dvdp1.
have /orP[/andP[_]|/andP[]//] := minPoly_irr gcdK (dvdp_gcdl _ _).
rewrite dvdp_gcd dvdpp /= => /(dvdp_leq nzPx')/leq_trans/(_ (size_poly _ _)).
by rewrite size_minPoly ltnn.
Qed.

Lemma separablePn : 
  reflect (exists2 p, p \in [char L] & 
            exists2 g, g \is a polyOver K & minPoly K x = g \Po 'X^p)
          (~~ separable_element K x).
Proof.
rewrite separable_nz_der negbK; set f := minPoly K x.
apply: (iffP eqP) => [f'0 | [p Hp [g _ ->]]]; last first.
  by rewrite deriv_comp derivXn -scaler_nat (charf0 Hp) scale0r mulr0.
pose n := adjoin_degree K x; have sz_f: size f = n.+1 := size_minPoly K x.
have fn1: f`_n = 1 by rewrite -(monicP (monic_minPoly K x)) lead_coefE sz_f.
have dimKx: (adjoin_degree K x)%:R == 0 :> L.
  by rewrite -(coef0 _ n.-1) -f'0 coef_deriv fn1.
have /natf0_char[// | p charLp] := dimKx.
have /dvdnP[r Dn]: (p %| n)%N by rewrite (dvdn_charf charLp).
exists p => //; exists (\poly_(i < r.+1) f`_(i * p)).
  by apply: polyOver_poly => i _; rewrite (polyOverP _) ?minPolyOver.
rewrite comp_polyE size_poly_eq -?Dn ?fn1 ?oner_eq0 //.
have pr_p := charf_prime charLp; have p_gt0 := prime_gt0 pr_p.
apply/polyP=> i; rewrite coef_sum.
have [[{i} i ->] | p'i] := altP (@dvdnP p i); last first.
  rewrite big1 => [|j _]; last first.
    rewrite coefZ -exprM coefXn [_ == _](contraNF _ p'i) ?mulr0 // => /eqP->.
    by rewrite dvdn_mulr.
  rewrite (dvdn_charf charLp) in p'i; apply: mulfI p'i _ _ _.
  by rewrite mulr0 mulr_natl; case: i => // i; rewrite -coef_deriv f'0 coef0.
have [ltri | leir] := leqP r.+1 i.
  rewrite nth_default ?sz_f ?Dn ?ltn_pmul2r ?big1 // => j _.
  rewrite coefZ -exprM coefXn mulnC gtn_eqF ?mulr0 //.
  by rewrite ltn_pmul2l ?(leq_trans _ ltri).
rewrite (bigD1 (Sub i _)) //= big1 ?addr0 => [|j i'j]; last first.
  by rewrite coefZ -exprM coefXn mulnC eqn_pmul2l // mulr_natr mulrb ifN_eqC.
by rewrite coef_poly leir coefZ -exprM coefXn mulnC eqxx mulr1.
Qed.

Lemma separable_root_der : separable_element K x (+) root (minPoly K x)^`() x.
Proof.
have KpKx': _^`() \is a polyOver K := polyOver_deriv (minPolyOver K x).
rewrite separable_nz_der addNb (root_small_adjoin_poly KpKx') ?addbb //.
by rewrite (leq_trans (size_poly _ _)) ?size_minPoly.
Qed.

Lemma Derivation_separable D :
    Derivation <<K; x>> D -> separable_element K x ->
  D x = - (map_poly D (minPoly K x)).[x] / (minPoly K x)^`().[x].
Proof.
move=> derD sepKx; have:= separable_root_der; rewrite {}sepKx -sub0r => nzKx'x.
apply: canRL (mulfK nzKx'x) (canRL (addrK _) _); rewrite mulrC addrC.
rewrite -(Derivation_horner derD) ?minPolyxx ?linear0 //.
exact: polyOverSv sKxK _ (minPolyOver _ _).
Qed.

Section ExtendDerivation.

Variable D : 'End(L).

Let Dx E := - (map_poly D (minPoly E x)).[x] / ((minPoly E x)^`()).[x].

Fact extendDerivation_subproof E (adjEx := Fadjoin_poly E x) :
  let body y (p := adjEx y) := (map_poly D p).[x] + p^`().[x] * Dx E in
  linear body.
Proof.
move: Dx => C /= a u v.
rewrite /adjEx linearP /= -mul_polyC derivD derivM derivC mul0r add0r -/adjEx.
rewrite !hornerE /= -scalerAl mul1r raddfD /=.
have ->: map_poly D (a%:A%:P * adjEx u) = a%:A%:P * map_poly D (adjEx u).
  apply/polyP=> i; rewrite !mul_polyC !coef_map !coefZ !mulr_algl /= linearZ.
  by rewrite coef_map.
rewrite !hornerE !mulr_algl mulrDl scalerDr -scalerAl -!addrA; congr (_ + _).
by rewrite addrCA.
Qed.

Definition extendDerivation E : 'End(L) :=
  linfun (Linear (extendDerivation_subproof E)).

Hypothesis derD : Derivation K D.

Lemma extendDerivation_id y : y \in K -> extendDerivation K y = D y.
Proof.
move=> yK; rewrite lfunE /= Fadjoin_polyC // derivC map_polyC hornerC.
by rewrite horner0 mul0r addr0.
Qed.

Lemma extendDerivation_horner p :
    p \is a polyOver K -> separable_element K x ->
  extendDerivation K p.[x] = (map_poly D p).[x] + p^`().[x] * Dx K.
Proof.
move=> Kp sepKx; have:= separable_root_der; rewrite {}sepKx /= => nz_pKx'x.
rewrite {-1}(divp_eq p (minPoly K x)) lfunE /= Fadjoin_poly_mod // raddfD /=.
rewrite {1}(Derivation_mul_poly derD) ?divp_polyOver ?minPolyOver //.
rewrite derivD derivM !{1}hornerD !{1}hornerM minPolyxx !{1}mulr0 !{1}add0r.
rewrite mulrDl addrA [_ + (_ * _ * _)]addrC {2}/Dx -mulrA -/Dx.
by rewrite [_ / _]mulrC (mulVKf nz_pKx'x) mulrN addKr.
Qed.

Lemma extendDerivationP :
  separable_element K x -> Derivation <<K; x>> (extendDerivation K).
Proof.
move=> sep; apply/allP=> u /vbasis_mem Hu; apply/allP=> v /vbasis_mem Hv.
apply/eqP.
rewrite -(Fadjoin_poly_eq Hu) -(Fadjoin_poly_eq Hv) -hornerM.
rewrite !{1}extendDerivation_horner ?{1}rpredM ?Fadjoin_polyOver //.
rewrite (Derivation_mul_poly derD) ?Fadjoin_polyOver //.
rewrite derivM !{1}hornerD !{1}hornerM !{1}mulrDl !{1}mulrDr -!addrA.
congr (_ + _); rewrite [Dx K]lock -!{1}mulrA !{1}addrA; congr (_ + _).
by rewrite addrC; congr (_ * _ + _); rewrite mulrC.
Qed.

End ExtendDerivation.

(* Reference: 
http://www.math.uconn.edu/~kconrad/blurbs/galoistheory/separable2.pdf *)
Lemma Derivation_separableP :
  reflect
    (forall D, Derivation <<K; x>> D -> K <= lker D -> <<K; x>> <= lker D)%VS
    (separable_element K x).
Proof.
apply: (iffP idP) => [sepKx D derD /subvP DK_0 | derKx_0].
  have{DK_0} DK_0 q: q \is a polyOver K -> map_poly D q = 0.
    move=> /polyOverP Kq; apply/polyP=> i; apply/eqP.
    by rewrite coef0 coef_map -memv_ker DK_0.
  apply/subvP=> _ /Fadjoin_polyP[p Kp ->]; rewrite memv_ker.
  rewrite (Derivation_horner derD) ?(polyOverSv sKxK) //.
  rewrite (Derivation_separable derD sepKx) !DK_0 ?minPolyOver //.
  by rewrite horner0 oppr0 mul0r mulr0 addr0.
apply: wlog_neg; rewrite {1}separable_nz_der negbK => /eqP pKx'_0.
have Dlin: linear (fun y => (Fadjoin_poly K x y)^`().[x]).
  move=> a u v; rewrite linearP /= -mul_polyC derivD derivM derivC mul0r add0r.
  by rewrite hornerD hornerM hornerC -scalerAl mul1r.
pose D := linfun (Linear Dlin); apply: base_separable.
have DK_0: (K <= lker D)%VS.
  apply/subvP=> v Kv; rewrite memv_ker lfunE /= Fadjoin_polyC //.
  by rewrite derivC horner0.
have Dder: Derivation <<K; x>> D.
  apply/allP=> u /vbasis_mem Kx_u; apply/allP=> v /vbasis_mem Kx_v.
  rewrite !lfunE /= -{-2}(Fadjoin_poly_eq Kx_u) -{-3}(Fadjoin_poly_eq Kx_v).
  rewrite -!hornerM -hornerD -derivM.
  rewrite Fadjoin_poly_mod ?rpredM ?Fadjoin_polyOver //.
  rewrite {2}(divp_eq (_ * _) (minPoly K x)) derivD derivM pKx'_0 mulr0 addr0.
  by rewrite hornerD hornerM minPolyxx mulr0 add0r.
have{Dder DK_0}: x \in lker D by apply: subvP Kx_x; apply: derKx_0.
apply: contraLR => K'x; rewrite memv_ker lfunE /= Fadjoin_polyX //.
by rewrite derivX hornerC oner_eq0.
Qed.

End SeparableElement.

Arguments separable_elementP {K x}.

Lemma separable_elementS K E x :
  (K <= E)%VS -> separable_element K x -> separable_element E x.
Proof.
move=> sKE /separable_elementP[f [fK rootf sepf]]; apply/separable_elementP.
by exists f; rewrite (polyOverSv sKE).
Qed.

Lemma adjoin_separableP {K x} :
  reflect (forall y, y \in <<K; x>>%VS -> separable_element K y)
          (separable_element K x).
Proof.
apply: (iffP idP) => [sepKx | -> //]; last exact: memv_adjoin.
move=> _ /Fadjoin_polyP[q Kq ->]; apply/Derivation_separableP=> D derD DK_0.
apply/subvP=> _ /Fadjoin_polyP[p Kp ->].
rewrite memv_ker -(extendDerivation_id x D (mempx_Fadjoin _ Kp)).
have sepFyx: (separable_element <<K; q.[x]>> x).
  by apply: (separable_elementS (subv_adjoin _ _)).
have KyxEqKx: (<< <<K; q.[x]>>; x>> = <<K; x>>)%VS.
  apply/eqP; rewrite eqEsubv andbC adjoinSl ?subv_adjoin //=.
  apply/FadjoinP/andP; rewrite memv_adjoin andbT.
  by apply/FadjoinP/andP; rewrite subv_adjoin mempx_Fadjoin.
have:= extendDerivationP derD sepFyx; rewrite KyxEqKx => derDx.
rewrite -horner_comp (Derivation_horner derDx) ?memv_adjoin //; last first.
  by apply: (polyOverSv (subv_adjoin _ _)); apply: polyOver_comp.
set Dx_p := map_poly _; have Dx_p_0 t: t \is a polyOver K -> (Dx_p t).[x] = 0.
  move/polyOverP=> Kt; congr (_.[x] = 0): (horner0 x); apply/esym/polyP => i.
  have /eqP Dti_0: D t`_i == 0 by rewrite -memv_ker (subvP DK_0) ?Kt.
  by rewrite coef0 coef_map /= {1}extendDerivation_id ?subvP_adjoin.
rewrite (Derivation_separable derDx sepKx) -/Dx_p Dx_p_0 ?polyOver_comp //.
by rewrite add0r mulrCA Dx_p_0 ?minPolyOver ?oppr0 ?mul0r.
Qed.

Lemma separable_exponent K x :
  exists n, [char L].-nat n && separable_element K (x ^+ n).
Proof.
pose d := adjoin_degree K x; move: {2}d.+1 (ltnSn d) => n.
elim: n => // n IHn in x @d *; rewrite ltnS => le_d_n.
have [[p charLp]|] := altP (separablePn K x); last by rewrite negbK; exists 1%N.
case=> g Kg defKx; have p_pr := charf_prime charLp.
suffices /IHn[m /andP[charLm sepKxpm]]: adjoin_degree K (x ^+ p) < n.
  by exists (p * m)%N; rewrite pnat_mul pnatE // charLp charLm exprM.
apply: leq_trans le_d_n; rewrite -ltnS -!size_minPoly.
have nzKx: minPoly K x != 0 by rewrite monic_neq0 ?monic_minPoly.
have nzg: g != 0 by apply: contra_eqN defKx => /eqP->; rewrite comp_poly0.
apply: leq_ltn_trans (dvdp_leq nzg _) _.
  by rewrite minPoly_dvdp // rootE -hornerXn -horner_comp -defKx minPolyxx.
rewrite (polySpred nzKx) ltnS defKx size_comp_poly size_polyXn /=.
suffices g_gt1: 1 < size g by rewrite -(subnKC g_gt1) ltn_Pmulr ?prime_gt1.
apply: contra_eqT (size_minPoly K x); rewrite defKx -leqNgt => /size1_polyC->.
by rewrite comp_polyC size_polyC; case: (_ != 0).
Qed.

Lemma charf0_separable K : [char L] =i pred0 -> forall x, separable_element K x.
Proof.
move=> charL0 x; have [n /andP[charLn]] := separable_exponent K x.
by rewrite (pnat_1 charLn (sub_in_pnat _ charLn)) // => p _; rewrite charL0.
Qed.

Lemma charf_p_separable K x e p :
  p \in [char L] -> separable_element K x = (x \in <<K; x ^+ (p ^ e.+1)>>%VS).
Proof.
move=> charLp; apply/idP/idP=> [sepKx | /Fadjoin_poly_eq]; last first.
  set m := p ^ _; set f := Fadjoin_poly K _ x => Dx; apply/separable_elementP.
  have mL0: m%:R = 0 :> L by apply/eqP; rewrite -(dvdn_charf charLp) dvdn_exp.
  exists ('X - (f \Po 'X^m)); split.
  - by rewrite rpredB ?polyOver_comp ?rpredX ?polyOverX ?Fadjoin_polyOver.
  - by rewrite rootE !hornerE horner_comp hornerXn Dx subrr.
  rewrite /separable_poly !(derivE, deriv_comp) -mulr_natr -rmorphMn /= mL0.
  by rewrite !mulr0 subr0 coprimep1.
without loss{e} ->: e x sepKx / e = 0%N.
  move=> IH; elim: {e}e.+1 => [|e]; [exact: memv_adjoin | apply: subvP].
  apply/FadjoinP/andP; rewrite subv_adjoin expnSr exprM (IH 0%N) //.
  by have /adjoin_separableP-> := sepKx; rewrite ?rpredX ?memv_adjoin.
set K' := <<K; x ^+ p>>%VS; have sKK': (K <= K')%VS := subv_adjoin _ _.
pose q := minPoly K' x; pose g := 'X^p - (x ^+ p)%:P.
have [K'g]: g \is a polyOver K' /\ q \is a polyOver K'.
  by rewrite minPolyOver rpredB ?rpredX ?polyOverX // polyOverC memv_adjoin.
have /dvdpP[c Dq]: 'X - x%:P %| q by rewrite dvdp_XsubCl root_minPoly.
have co_c_g: coprimep c g.
  have charPp: p \in [char {poly L}] := rmorph_char (polyC_rmorphism _) charLp.
  rewrite /g polyC_exp -!(Frobenius_autE charPp) -rmorphB coprimep_expr //.
  have: separable_poly q := separable_elementS sKK' sepKx.
  by rewrite Dq separable_mul => /and3P[].
have{g K'g co_c_g} /size_poly1P[a nz_a Dc]: size c == 1%N.
  suffices c_dv_g: c %| g by rewrite -(eqp_size (dvdp_gcd_idl c_dv_g)).
  have: q %| g by rewrite minPoly_dvdp // rootE !hornerE hornerXn subrr.
  by apply: dvdp_trans; rewrite Dq dvdp_mulIl.
rewrite {q}Dq {c}Dc mulrBr -rmorphM -rmorphN -cons_poly_def qualifE.
by rewrite polyseq_cons !polyseqC nz_a /= rpredN andbCA => /and3P[/fpredMl->].
Qed.

Lemma charf_n_separable K x n :
  [char L].-nat n -> 1 < n -> separable_element K x = (x \in <<K; x ^+ n>>%VS).
Proof.
rewrite -pi_pdiv; set p := pdiv n => charLn pi_n_p.
have charLp: p \in [char L] := pnatPpi charLn pi_n_p.
have <-: (n`_p)%N = n by rewrite -(eq_partn n (charf_eq charLp)) part_pnat_id.
by rewrite p_part lognE -mem_primes pi_n_p -charf_p_separable.
Qed.

Definition purely_inseparable_element U x :=
  x ^+ ex_minn (separable_exponent <<U>> x) \in U.

Lemma purely_inseparable_elementP {K x} :
  reflect (exists2 n, [char L].-nat n & x ^+ n \in K)
          (purely_inseparable_element K x).
Proof.
rewrite /purely_inseparable_element.
case: ex_minnP => n /andP[charLn /=]; rewrite subfield_closed => sepKxn min_xn.
apply: (iffP idP) => [Kxn | [m charLm Kxm]]; first by exists n.
have{min_xn}: n <= m by rewrite min_xn ?charLm ?base_separable.
rewrite leq_eqVlt => /predU1P[-> // | ltnm]; pose p := pdiv m.
have m_gt1: 1 < m by have [/leq_ltn_trans->] := andP charLn.
have charLp: p \in [char L] by rewrite (pnatPpi charLm) ?pi_pdiv.
have [/p_natP[em Dm] /p_natP[en Dn]]: p.-nat m /\ p.-nat n.
  by rewrite -!(eq_pnat _ (charf_eq charLp)).
rewrite Dn Dm ltn_exp2l ?prime_gt1 ?pdiv_prime // in ltnm.
rewrite -(Fadjoin_idP Kxm) Dm -(subnKC ltnm) addSnnS expnD exprM -Dn.
by rewrite -charf_p_separable.
Qed.

Lemma separable_inseparable_element K x :
  separable_element K x && purely_inseparable_element K x = (x \in K).
Proof.
rewrite /purely_inseparable_element; case: ex_minnP => [[|m]] //=.
rewrite subfield_closed; case: m => /= [-> //| m _ /(_ 1%N)/implyP/= insepKx].
by rewrite (negPf insepKx) (contraNF (@base_separable K x) insepKx).
Qed.

Lemma base_inseparable K x : x \in K -> purely_inseparable_element K x.
Proof. by rewrite -separable_inseparable_element => /andP[]. Qed.

Lemma sub_inseparable K E x :
    (K <= E)%VS -> purely_inseparable_element K x ->
 purely_inseparable_element E x.
Proof.
move/subvP=> sKE /purely_inseparable_elementP[n charLn /sKE Exn].
by apply/purely_inseparable_elementP; exists n.
Qed.

Section PrimitiveElementTheorem.

Variables (K : {subfield L}) (x y : L).

Section FiniteCase.

Variable N : nat.

Let K_is_large := exists s, [/\ uniq s, {subset s <= K} & N < size s].

Let cyclic_or_large (z : L) : z != 0 -> K_is_large \/ exists a, z ^+ a.+1 = 1.
Proof.
move=> nz_z; pose d := adjoin_degree K z.
pose h0 (i : 'I_(N ^ d).+1) (j : 'I_d) := (Fadjoin_poly K z (z ^+ i))`_j.
pose s := undup [seq h0 i j | i <- enum 'I_(N ^ d).+1, j <- enum 'I_d].
have s_h0 i j: h0 i j \in s.
  by rewrite mem_undup; apply/allpairsP; exists (i, j); rewrite !mem_enum.
pose h i := [ffun j => Ordinal (etrans (index_mem _ _) (s_h0 i j))].
pose h' (f : {ffun 'I_d -> 'I_(size s)}) := \sum_(j < d) s`_(f j) * z ^+ j.
have hK i: h' (h i) = z ^+ i.
  have Kz_zi: z ^+ i \in <<K; z>>%VS by rewrite rpredX ?memv_adjoin.
  rewrite -(Fadjoin_poly_eq Kz_zi) (horner_coef_wide z (size_poly _ _)) -/d.
  by apply: eq_bigr => j _; rewrite ffunE /= nth_index.
have [inj_h | ] := altP (@injectiveP _ _ h).
  left; exists s; split=> [|zi_j|]; rewrite ?undup_uniq ?mem_undup //=.
    by case/allpairsP=> ij [_ _ ->]; apply/polyOverP/Fadjoin_polyOver.
  rewrite -[size s]card_ord -(@ltn_exp2r _ _ d) // -{2}[d]card_ord -card_ffun.
  by rewrite -[_.+1]card_ord -(card_image inj_h) max_card.
case/injectivePn=> i1 [i2 i1'2 /(congr1 h')]; rewrite !hK => eq_zi12; right.
without loss{i1'2} lti12: i1 i2 eq_zi12 / i1 < i2.
  by move=> IH; move: i1'2; rewrite neq_ltn => /orP[]; apply: IH.
by exists (i2 - i1.+1)%N; rewrite subnSK ?expfB // eq_zi12 divff ?expf_neq0.
Qed.

Lemma finite_PET : K_is_large \/ exists z, (<< <<K; y>>; x>> = <<K; z>>)%VS.
Proof.
have [-> | /cyclic_or_large[|[a Dxa]]] := eqVneq x 0; first 2 [by left].
  by rewrite addv0 subfield_closed; right; exists y.
have [-> | /cyclic_or_large[|[b Dyb]]] := eqVneq y 0; first 2 [by left].
  by rewrite addv0 subfield_closed; right; exists x.
pose h0 (ij : 'I_a.+1 * 'I_b.+1) := x ^+ ij.1 * y ^+ ij.2.
pose H := <<[set ij | h0 ij == 1%R]>>%G; pose h (u : coset_of H) := h0 (repr u).
have h0M: {morph h0: ij1 ij2 / (ij1 * ij2)%g >-> ij1 * ij2}.
  by rewrite /h0 => [] [i1 j1] [i2 j2] /=; rewrite mulrACA -!exprD !expr_mod.
have memH ij: (ij \in H) = (h0 ij == 1).
  rewrite /= gen_set_id ?inE //; apply/group_setP; rewrite inE [h0 _]mulr1.
  by split=> // ? ?; rewrite !inE h0M => /eqP-> /eqP->; rewrite mulr1.
have nH ij: ij \in 'N(H)%g.
  by apply/(subsetP (cent_sub _))/centP=> ij1 _; congr (_, _); rewrite Zp_mulgC.
have hE ij: h (coset H ij) = h0 ij.
  rewrite /h val_coset //; case: repr_rcosetP => ij1.
  by rewrite memH h0M => /eqP->; rewrite mul1r.
have h1: h 1%g = 1 by rewrite /h repr_coset1 [h0 _]mulr1.
have hM: {morph h: u v / (u * v)%g >-> u * v}.
  by do 2![move=> u; have{u} [? _ ->] := cosetP u]; rewrite -morphM // !hE h0M.
have /cyclicP[w defW]: cyclic [set: coset_of H].
  apply: field_mul_group_cyclic (in2W hM) _ => u _; have [ij _ ->] := cosetP u.
  by split=> [/eqP | -> //]; rewrite hE -memH => /coset_id.
have Kw_h ij t: h0 ij = t -> t \in <<K; h w>>%VS.
  have /cycleP[k Dk]: coset H ij \in <[w]>%g by rewrite -defW inE.
  rewrite -hE {}Dk => <-; elim: k => [|k IHk]; first by rewrite h1 rpred1.
  by rewrite expgS hM rpredM // memv_adjoin.
right; exists (h w); apply/eqP; rewrite eqEsubv !(sameP FadjoinP andP).
rewrite subv_adjoin (subv_trans (subv_adjoin K y)) ?subv_adjoin //=.
rewrite (Kw_h (0, inZp 1)) 1?(Kw_h (inZp 1, 0)) /h0 ?mulr1 ?mul1r ?expr_mod //=.
by rewrite rpredM ?rpredX ?memv_adjoin // subvP_adjoin ?memv_adjoin.
Qed.

End FiniteCase.

Hypothesis sepKy : separable_element K y.

Lemma Primitive_Element_Theorem : exists z, (<< <<K; y>>; x>> = <<K; z>>)%VS.
Proof.
have /polyOver_subvs[p Dp]: minPoly K x \is a polyOver K := minPolyOver K x.
have nz_pKx: minPoly K x != 0 by rewrite monic_neq0 ?monic_minPoly.
have{nz_pKx} nz_p: p != 0 by rewrite Dp map_poly_eq0 in nz_pKx.
have{Dp} px0: root (map_poly vsval p) x by rewrite -Dp root_minPoly.
have [q0 [Kq0 q0y0 sepKq0]] := separable_elementP sepKy.
have /polyOver_subvs[q Dq]: minPoly K y \is a polyOver K := minPolyOver K y.
have qy0: root (map_poly vsval q) y by rewrite -Dq root_minPoly.
have sep_pKy: separable_poly (minPoly K y).
  by rewrite (dvdp_separable _ sepKq0) ?minPoly_dvdp.
have{sep_pKy} sep_q: separable_poly q by rewrite Dq separable_map in sep_pKy.
have [r nz_r PETr] := large_field_PET nz_p px0 qy0 sep_q.
have [[s [Us Ks /ltnW leNs]] | //] := finite_PET (size r).
have{s Us leNs} /allPn[t {Ks}/Ks Kt nz_rt]: ~~ all (root r) s.
  by apply: contraTN leNs; rewrite -ltnNge => /max_poly_roots->.
have{PETr} [/= [p1 Dx] [q1 Dy]] := PETr (Subvs Kt) nz_rt.
set z := t * y - x in Dx Dy; exists z; apply/eqP.
rewrite eqEsubv !(sameP FadjoinP andP) subv_adjoin.
have Kz_p1z (r1 : {poly subvs_of K}): (map_poly vsval r1).[z] \in <<K; z>>%VS.
  rewrite rpred_horner ?memv_adjoin ?(polyOverSv (subv_adjoin K z)) //.
  by apply/polyOver_subvs; exists r1.
rewrite -{1}Dx -{1}Dy !{Dx Dy}Kz_p1z /=.
rewrite (subv_trans (subv_adjoin K y)) ?subv_adjoin // rpredB ?memv_adjoin //.
by rewrite subvP_adjoin // rpredM ?memv_adjoin ?subvP_adjoin.
Qed.

Lemma adjoin_separable : separable_element <<K; y>> x -> separable_element K x.
Proof.
have /Derivation_separableP derKy := sepKy => /Derivation_separableP derKy_x.
have [z defKz] := Primitive_Element_Theorem.
suffices /adjoin_separableP: separable_element K z.
  by apply; rewrite -defKz memv_adjoin.
apply/Derivation_separableP=> D; rewrite -defKz => derKxyD DK_0.
suffices derKyD: Derivation <<K; y>>%VS D by rewrite derKy_x // derKy.
by apply: DerivationS derKxyD; apply: subv_adjoin.
Qed.

End PrimitiveElementTheorem.

Lemma strong_Primitive_Element_Theorem K x y :
    separable_element <<K; x>> y ->
  exists2 z : L, (<< <<K; y>>; x>> = <<K; z>>)%VS
               & separable_element K x -> separable_element K y.
Proof.
move=> sepKx_y; have [n /andP[charLn sepKyn]] := separable_exponent K y.
have adjK_C z t: (<<<<K; z>>; t>> = <<<<K; t>>; z>>)%VS.
  by rewrite !agenv_add_id -!addvA (addvC <[_]>%VS).
have [z defKz] := Primitive_Element_Theorem x sepKyn.
exists z => [|/adjoin_separable->]; rewrite ?sepKx_y // -defKz.
have [|n_gt1|-> //] := ltngtP n 1%N; first by case: (n) charLn.
apply/eqP; rewrite !(adjK_C _ x) eqEsubv; apply/andP.
split; apply/FadjoinP/andP; rewrite subv_adjoin ?rpredX ?memv_adjoin //=.
by rewrite -charf_n_separable ?sepKx_y.
Qed.

Definition separable U W : bool :=
  all (separable_element U) (vbasis W).

Definition purely_inseparable U W : bool :=
  all (purely_inseparable_element U) (vbasis W).

Lemma separable_add K x y :
  separable_element K x -> separable_element K y -> separable_element K (x + y).
Proof.
move/(separable_elementS (subv_adjoin K y))=> sepKy_x sepKy.
have [z defKz] := Primitive_Element_Theorem x sepKy.
have /(adjoin_separableP _): x + y \in <<K; z>>%VS.
  by rewrite -defKz rpredD ?memv_adjoin // subvP_adjoin ?memv_adjoin.
apply; apply: adjoin_separable sepKy (adjoin_separable sepKy_x _).
by rewrite defKz base_separable ?memv_adjoin.
Qed.

Lemma separable_sum I r (P : pred I) (v_ : I -> L) K :
    (forall i, P i -> separable_element K (v_ i)) ->
  separable_element K (\sum_(i <- r | P i) v_ i).
Proof.
move=> sepKi.
by elim/big_ind: _; [apply/base_separable/mem0v | apply: separable_add |].
Qed.

Lemma inseparable_add K x y :
    purely_inseparable_element K x -> purely_inseparable_element K y ->
  purely_inseparable_element K (x + y).
Proof.
have insepP := purely_inseparable_elementP.
move=> /insepP[n charLn Kxn] /insepP[m charLm Kym]; apply/insepP.
have charLnm: [char L].-nat (n * m)%N by rewrite pnat_mul charLn.
by exists (n * m)%N; rewrite ?exprDn_char // {2}mulnC !exprM memvD // rpredX.
Qed.

Lemma inseparable_sum I r (P : pred I) (v_ : I -> L) K :
    (forall i, P i -> purely_inseparable_element K (v_ i)) ->
  purely_inseparable_element K (\sum_(i <- r | P i) v_ i).
Proof.
move=> insepKi.
by elim/big_ind: _; [apply/base_inseparable/mem0v | apply: inseparable_add |].
Qed.

Lemma separableP {K E} :
  reflect (forall y, y \in E -> separable_element K y) (separable K E).
Proof.
apply/(iffP idP)=> [/allP|] sepK_E; last by apply/allP=> x /vbasis_mem/sepK_E.
move=> y /coord_vbasis->; apply/separable_sum=> i _.
have: separable_element K (vbasis E)`_i by apply/sepK_E/memt_nth.
by move/adjoin_separableP; apply; rewrite rpredZ ?memv_adjoin.
Qed.

Lemma purely_inseparableP {K E} :
  reflect (forall y, y \in E -> purely_inseparable_element K y)
          (purely_inseparable K E).
Proof.
apply/(iffP idP)=> [/allP|] sep'K_E; last by apply/allP=> x /vbasis_mem/sep'K_E.
move=> y /coord_vbasis->; apply/inseparable_sum=> i _.
have: purely_inseparable_element K (vbasis E)`_i by apply/sep'K_E/memt_nth.
case/purely_inseparable_elementP=> n charLn K_Ein.
by apply/purely_inseparable_elementP; exists n; rewrite // exprZn rpredZ.
Qed.

Lemma adjoin_separable_eq K x : separable_element K x = separable K <<K; x>>%VS.
Proof. exact: sameP adjoin_separableP separableP. Qed.

Lemma separable_inseparable_decomposition E K :
  {x | x \in E /\ separable_element K x & purely_inseparable <<K; x>> E}.
Proof.
without loss sKE: K / (K <= E)%VS.
  case/(_ _ (capvSr K E)) => x [Ex sepKEx] /purely_inseparableP sep'KExE.
  exists x; first by split; last exact/(separable_elementS _ sepKEx)/capvSl.
  apply/purely_inseparableP=> y /sep'KExE; apply: sub_inseparable.
  exact/adjoinSl/capvSl.
pose E_ i := (vbasis E)`_i; pose fP i := separable_exponent K (E_ i).
pose f i := E_ i ^+ ex_minn (fP i); pose s := mkseq f (\dim E).
pose K' := <<K & s>>%VS.
have sepKs: all (separable_element K) s.
  by rewrite all_map /f; apply/allP=> i _ /=; case: ex_minnP => m /andP[].
have [x sepKx defKx]: {x | x \in E /\ separable_element K x & K' = <<K; x>>%VS}.
  have: all (mem E) s.
    rewrite all_map; apply/allP=> i; rewrite mem_iota => ltis /=.
    by rewrite rpredX // vbasis_mem // memt_nth.
  rewrite {}/K'; elim/last_ind: s sepKs => [|s t IHs].
    by exists 0; [rewrite base_separable mem0v | rewrite adjoin_nil addv0].
  rewrite adjoin_rcons !all_rcons => /andP[sepKt sepKs] /andP[/= Et Es].
  have{IHs sepKs Es} [y [Ey sepKy] ->{s}] := IHs sepKs Es.
  have /sig_eqW[x defKx] := Primitive_Element_Theorem t sepKy.
  exists x; [split | exact: defKx].
    suffices: (<<K; x>> <= E)%VS by case/FadjoinP.
    by rewrite -defKx !(sameP FadjoinP andP) sKE Ey Et.
  apply/adjoin_separableP=> z; rewrite -defKx => Kyt_z.
  apply: adjoin_separable sepKy _; apply: adjoin_separableP Kyt_z.
  exact: separable_elementS (subv_adjoin K y) sepKt.
exists x; rewrite // -defKx; apply/(all_nthP 0)=> i; rewrite size_tuple => ltiE.
apply/purely_inseparable_elementP.
exists (ex_minn (fP i)); first by case: ex_minnP => n /andP[].
by apply/seqv_sub_adjoin/map_f; rewrite mem_iota.
Qed.

Definition separable_generator K E : L :=
   s2val (locked (separable_inseparable_decomposition E K)).

Lemma separable_generator_mem E K : separable_generator K E \in E.
Proof. by rewrite /separable_generator; case: (locked _) => ? []. Qed.

Lemma separable_generatorP E K : separable_element K (separable_generator K E).
Proof. by rewrite /separable_generator; case: (locked _) => ? []. Qed.

Lemma separable_generator_maximal E K :
  purely_inseparable <<K; separable_generator K E>> E.
Proof. by rewrite /separable_generator; case: (locked _). Qed.

Lemma sub_adjoin_separable_generator E K :
  separable K E -> (E <= <<K; separable_generator K E>>)%VS.
Proof.
move/separableP=> sepK_E; apply/subvP=> v Ev.
rewrite -separable_inseparable_element.
have /purely_inseparableP-> // := separable_generator_maximal E K.
by rewrite (separable_elementS _ (sepK_E _ Ev)) // subv_adjoin.
Qed.

Lemma eq_adjoin_separable_generator E K :
    separable K E -> (K <= E)%VS ->
  E = <<K; separable_generator K E>>%VS :> {vspace _}.
Proof.
move=> sepK_E sKE; apply/eqP; rewrite eqEsubv sub_adjoin_separable_generator //.
by apply/FadjoinP/andP; rewrite sKE separable_generator_mem.
Qed.

Lemma separable_refl K : separable K K.
Proof. by apply/separableP; apply: base_separable. Qed.

Lemma separable_trans M K E : separable K M -> separable M E -> separable K E.
Proof.
move/sub_adjoin_separable_generator.
set x := separable_generator K M => sMKx /separableP sepM_E.
apply/separableP => w /sepM_E/(separable_elementS sMKx).
case/strong_Primitive_Element_Theorem => _ _ -> //.
exact: separable_generatorP.
Qed.

Lemma separableS K1 K2 E2 E1 : 
  (K1 <= K2)%VS -> (E2 <= E1)%VS -> separable K1 E1 -> separable K2 E2.
Proof.
move=> sK12 /subvP sE21 /separableP sepK1_E1.
by apply/separableP=> y /sE21/sepK1_E1/(separable_elementS sK12).
Qed.

Lemma separableSl K M E : (K <= M)%VS -> separable K E -> separable M E.
Proof. by move/separableS; apply. Qed.

Lemma separableSr K M E : (M <= E)%VS -> separable K E -> separable K M.
Proof. exact: separableS. Qed.

Lemma separable_Fadjoin_seq K rs :
  all (separable_element K) rs -> separable K <<K & rs>>.
Proof.
elim/last_ind: rs => [|s x IHs] in K *.
  by rewrite adjoin_nil subfield_closed separable_refl.
rewrite all_rcons adjoin_rcons => /andP[sepKx /IHs/separable_trans-> //].
by rewrite -adjoin_separable_eq (separable_elementS _ sepKx) ?subv_adjoin_seq.
Qed.

Lemma purely_inseparable_refl K : purely_inseparable K K.
Proof. by apply/purely_inseparableP; apply: base_inseparable. Qed.

Lemma purely_inseparable_trans M K E :
  purely_inseparable K M -> purely_inseparable M E -> purely_inseparable K E.
Proof.
have insepP := purely_inseparableP => /insepP insepK_M /insepP insepM_E.
have insepPe := purely_inseparable_elementP.
apply/insepP=> x /insepM_E/insepPe[n charLn /insepK_M/insepPe[m charLm Kxnm]].
by apply/insepPe; exists (n * m)%N; rewrite ?exprM // pnat_mul charLn charLm.
Qed.

End Separable.

Arguments separable_elementP {F L K x}.
Arguments separablePn {F L K x}.
Arguments Derivation_separableP {F L K x}.
Arguments adjoin_separableP {F L K x}.
Arguments purely_inseparable_elementP {F L K x}.
Arguments separableP {F L K E}.
Arguments purely_inseparableP {F L K E}.

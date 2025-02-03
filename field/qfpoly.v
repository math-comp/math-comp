From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype tuple div bigop binomial finset finfun.
From mathcomp Require Import ssralg countalg finalg poly polydiv qpoly perm.
From mathcomp Require Import monoid fingroup falgebra fieldext finfield galois.
From mathcomp Require Import finalg zmodp matrix vector.

(******************************************************************************)
(* This file extends the algebras R[X]/<p> defined in qpoly with the field    *)
(* when p is irreducible                                                      *)
(* It defines the new field on top of {qpoly p}. As irreducible is in general *)
(* decidable in general, this is done by giving a proof explicitly.           *)
(*      monic_irreducible_poly p == proof that p is monic and irreducible     *)
(*   {poly %/ p with mi} == defined as {poly %/ p} where mi is proof of       *)
(*                    monic_irreducible_poly p                                *)
(* It also defines the discrete logarithm with a primitive polynomial on a    *)
(* finite field                                                               *)
(*    primitive_poly p == p is a primitive polynomial                         *)
(*      qlogp  q == is the discrete log of q where q is an element of         *)
(*                     the quotient field with respect to a primitive         *)
(*                     polynomial p                                           *)
(*    plogp p q == is the discrete log of q with respect to p in {poly F}     *)
(*                 this makes only sense if p is a primitive polynomial of    *)
(*                 size > 2                                                   *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Import Pdiv.CommonRing.
Import Pdiv.RingMonic.
Import Pdiv.Field.
Import FinRing.Theory.
Local Open Scope ring_scope.

Reserved Notation "{ 'poly' '%/' p 'with' mi }"
  (at level 0, p at level 2, mi at level 10,
   format "{ 'poly'  '%/'  p  'with'  mi }").

Section DomainDef.

Variable R : idomainType.
Variable h : {poly R}.

Definition monic_irreducible_poly  (p : {poly R}) :=
  ((irreducible_poly p) * (p \is monic))%type.
Hypothesis hI : monic_irreducible_poly h.

Definition qfpoly : monic_irreducible_poly h -> predArgType :=
  fun=> {poly %/ h}.

End DomainDef.

Notation "{ 'poly' '%/' p 'with' hi }" := (@qfpoly _ p hi).


Section iDomain.

Variable R : idomainType.
Variable h : {poly R}.
Hypothesis hI : monic_irreducible_poly h.

HB.instance Definition _ := GRing.NzRing.on {poly %/ h with hI}.

End iDomain.

Section finIDomain.

Variable R : finIdomainType.
Variable h : {poly R}.
Hypothesis hI : monic_irreducible_poly h.

HB.instance Definition _ := Finite.on {poly %/ h with hI}.

End finIDomain.

Section Field.

Variable R : fieldType.
Variable h : {poly R}.

Local Notation hQ := (mk_monic h).

Hypothesis hI : monic_irreducible_poly h.

HB.instance Definition _ := GRing.ComUnitRing.on {poly %/ h with hI}.

Lemma mk_monicE : mk_monic h = h.
Proof. by rewrite /mk_monic !hI. Qed.

Lemma coprimep_unit (p : {poly %/ h}) : p != 0%R -> coprimep hQ p.
Proof.
move=> pNZ.
rewrite irreducible_poly_coprime //; last first.
  by case: hI; rewrite mk_monicE.
apply: contra pNZ => H; case: eqP => // /eqP /dvdp_leq /(_ H).
by rewrite leqNgt size_mk_monic.
Qed.

Lemma qpoly_mulVp (p : {poly %/ h}) : p != 0%R -> (qpoly_inv p * p = 1)%R.
Proof. by move=> pNZ; apply/qpoly_mulVz/coprimep_unit. Qed.

Lemma qpoly_inv0 : qpoly_inv 0%R = 0%R :> {poly %/ h}.
Proof.
rewrite /qpoly_inv /= coprimep0 -size_poly_eq1.
rewrite [in X in X == _]mk_monicE.
by have [[]] := hI; case: size => [|[]].
Qed.

HB.instance Definition _ := GRing.ComUnitRing_isField.Build {poly %/ h with hI}
  coprimep_unit.

HB.instance Definition _ := GRing.UnitAlgebra.on {poly %/ h with hI}.
HB.instance Definition _ := Vector.on {poly %/ h with hI}.

End Field.

Section FinField.

Variable R : finFieldType.
Variable h : {poly R}.
Local Notation hQ := (mk_monic h).

HB.instance Definition _ := Finite.on {poly %/ h}.

Hypothesis hI : monic_irreducible_poly h.

HB.instance Definition _ := Finite.on {poly %/ h with hI}.

Lemma card_qfpoly : #|{poly %/ h with hI}| = #|R| ^ (size h).-1.
Proof. by rewrite card_monic_qpoly ?hI. Qed.

Lemma card_qfpoly_gt1 : 1 < #|{poly %/ h with hI}|.
Proof. by have := card_finNzRing_gt1 {poly %/ h with hI}. Qed.

End FinField.

Section inPoly.

Variable R : comNzRingType.
Variable h : {poly R}.

Lemma in_qpoly_comp_horner (p q : {poly R}) :
 in_qpoly h (p \Po q) =
     (map_poly (qpolyC h) p).[in_qpoly h q].
Proof.
have hQM := monic_mk_monic h.
rewrite comp_polyE /map_poly poly_def horner_sum /=.
apply: val_inj.
rewrite /= rmodp_sum // poly_of_qpoly_sum.
apply: eq_bigr => i  _.
rewrite !hornerE /in_qpoly /=.
rewrite mul_polyC // !rmodpZ //=.
by rewrite poly_of_qpolyX /= rmodp_id // rmodpX // rmodp_id.
Qed.

Lemma map_poly_div_inj : injective (map_poly (qpolyC h)).
Proof.
apply: map_inj_poly => [x y /val_eqP /eqP /polyC_inj //|].
by rewrite qpolyC0.
Qed.

End inPoly.

Section finPoly.

(* Unfortunately we need some duplications so inference
   propagates qfpoly :-( )*)
Definition qfpoly_const (R : idomainType) (h : {poly R})
   (hMI : monic_irreducible_poly h) : R -> {poly %/ h with hMI} :=
  qpolyC h.

Lemma map_fpoly_div_inj (R : idomainType) (h : {poly R})
    (hMI : monic_irreducible_poly h) :
  injective (map_poly (qfpoly_const hMI)).
Proof. by apply: (@map_poly_div_inj R h). Qed.

End finPoly.

Section Splitting.

Variable F : finFieldType.
Variable h : {poly F}.
Hypothesis hI : monic_irreducible_poly h.

Definition qfpoly_splitting_field_type :=
  FinSplittingFieldType F {poly %/ h with hI}.

End Splitting.

Section PrimitivePoly.

Variable F : finFieldType.
Variable h : {poly F}.
Hypothesis sh_gt2 : 2 < size h.
Let sh_gt1 : 1 < size h.
Proof. by apply: leq_ltn_trans sh_gt2. Qed.

Definition primitive_poly (p: {poly F}) :=
  let v := #|{poly %/ p}|.-1 in
  [&& p \is monic,
      irreducibleb p,
      p %| 'X^v - 1 &
      [forall n : 'I_v, (p %| 'X^n - 1) ==> (n == 0%N :> nat)]].

Lemma primitive_polyP (p : {poly F}) :
  reflect
    (let v := #|{poly %/ p}|.-1 in
      [/\ monic_irreducible_poly p,
          p %| 'X^v - 1 &
          forall n, 0 < n < v -> ~~ (p %| 'X^n - 1)])
    (primitive_poly p).
Proof.
apply: (iffP and4P) => [[H1 H2 H3 /forallP H4] v|[[H1 H2] H3 H4]]; split => //.
- by split => //; apply/irreducibleP.
- move=> n /andP[n_gt0 nLv]; apply/negP => /(implyP (H4 (Ordinal nLv))) /=.
  by rewrite eqn0Ngt n_gt0.
- by apply/irreducibleP.
apply/forallP=> [] [[|n] Hn] /=; apply/implyP => pDX //.
by case/negP: (H4 n.+1 Hn).
Qed.

Hypothesis Hh : primitive_poly h.

Lemma primitive_mi : monic_irreducible_poly h.
Proof. by case/primitive_polyP: Hh. Qed.

Lemma primitive_poly_in_qpoly_eq0 p : (in_qpoly h p == 0) = (h %| p).
Proof.
have hM : h \is monic by case/and4P:Hh.
have hMi : monic_irreducible_poly h by apply: primitive_mi.
apply/eqP/idP => [/val_eqP /= | hDp].
  by rewrite -Pdiv.IdomainMonic.modpE mk_monicE.
by apply/val_eqP; rewrite /= -Pdiv.IdomainMonic.modpE mk_monicE.
Qed.

Local Notation qT := {poly %/ h with primitive_mi}.

Lemma card_primitive_qpoly : #|{poly %/ h}|= #|F| ^ (size h).-1.
Proof. by rewrite card_monic_qpoly ?primitive_mi. Qed.

Lemma qX_neq0 : 'qX != 0 :> qT.
Proof.
apply/eqP => /val_eqP/=.
by rewrite [rmodp _ _]qpolyXE ?polyX_eq0 //; case: primitive_mi.
Qed.

Lemma qX_in_unit : ('qX : qT) \in GRing.unit.
Proof. by rewrite unitfE /= qX_neq0. Qed.

Definition gX : {unit qT} := FinRing.unit _ qX_in_unit.

Lemma dvdp_order n : (h %| 'X^n - 1) = (gX ^+ n == 1)%g.
Proof.
have [hM hI] := primitive_mi.
have eqr_add2r (r : nzRingType) (a b c : r) : (a + c == b + c) = (a == b).
  by apply/eqP/eqP => [H|->//]; rewrite -(addrK c a) H addrK.
rewrite -val_eqE /= val_unitX /= -val_eqE /=.
rewrite (poly_of_qpolyX) qpolyXE // mk_monicE //.
rewrite -[in RHS](subrK 1 'X^n) rmodpD //.
rewrite [rmodp 1 h]rmodp_small ?size_poly1 //.
rewrite -[1%:P]add0r polyC1 /= eqr_add2r.
by rewrite dvdpE /=; apply/rmodp_eq0P/eqP.
Qed.

Lemma gX_order : #[gX]%g  = (#|qT|).-1.
Proof.
have /primitive_polyP[Hp1 Hp2 Hp3] := Hh.
set n := _.-1 in Hp2 Hp3 *.
have n_gt0 : 0 < n by rewrite ltn_predRL card_qfpoly_gt1.
have [hM hI] := primitive_mi.
have gX_neq1 : gX != 1%g.
  apply/eqP/val_eqP/eqP/val_eqP=> /=.
  rewrite [X in X != _]qpolyXE /= //.
  by apply/eqP=> Hx1; have := @size_polyX F; rewrite Hx1 size_poly1.
have Hx : (gX ^+ n)%g = 1%g by apply/eqP; rewrite -dvdp_order.
have Hf i : 0 < i < n -> (gX ^+ i != 1)%g by rewrite -dvdp_order => /Hp3.
have o_gt0 : 0 < #[gX]%g by rewrite order_gt0.
have : n <= #[gX]%g.
  rewrite leqNgt; apply/negP=> oLx.
  have /Hf/eqP[] : 0 < #[gX]%g < n by rewrite o_gt0.
  by rewrite expg_order.
case: ltngtP => nLo _ //.
have: uniq (path.traject (mulg gX) 1%g #[gX]%g).
  by apply/card_uniqP; rewrite path.size_traject -(eq_card (cycle_traject gX)).
case: #[gX]%g o_gt0 nLo => //= n1 _ nLn1 /andP[/negP[]].
apply/path.trajectP; exists n.-1; first by rewrite prednK.
rewrite -iterSr prednK // -[LHS]Hx.
by elim: (n) => //= n2 <-; rewrite expgS.
Qed.

Lemma gX_all : <[gX]>%g = [set: {unit qT}]%G.
Proof.
apply/eqP; rewrite eqEcard; apply/andP; split.
  by apply/subsetP=> i; rewrite inE.
rewrite leq_eqVlt; apply/orP; left; apply/eqP.
rewrite -orderE gX_order card_qfpoly -[in RHS](mk_monicE primitive_mi).
rewrite -card_qpoly -(cardC1 (0 : {poly %/ h with primitive_mi})).
rewrite cardsT card_sub.
by apply: eq_card => x; rewrite [LHS]unitfE.
Qed.

Let pred_card_qT_gt0 : 0 < #|qT|.-1.
Proof. by rewrite ltn_predRL card_qfpoly_gt1. Qed.

Definition qlogp (p : qT) : nat :=
  odflt (Ordinal pred_card_qT_gt0)  (pick [pred i in 'I_ _ | ('qX ^+ i == p)]).

Lemma qlogp_lt p : qlogp p < #|qT|.-1.
Proof. by rewrite /qlogp; case: pickP. Qed.

Lemma qlogp_qX (p : qT) : p != 0 -> 'qX ^+ (qlogp p) = p.
Proof.
move=> p_neq0.
have Up : p \in GRing.unit by rewrite unitfE.
pose gp : {unit qT}:= FinRing.unit _ Up.
have /cyclePmin[i iLc iX] : gp \in <[gX]>%g by rewrite gX_all inE.
rewrite gX_order in iLc.
rewrite /qlogp; case: pickP => [j /eqP//|/(_ (Ordinal iLc))] /eqP[].
by have /val_eqP/eqP/= := iX; rewrite FinRing.val_unitX.
Qed.

Lemma qX_order_card : 'qX ^+ (#|qT|).-1 = 1 :> qT.
Proof.
have /primitive_polyP [_ Hd _] := Hh.
rewrite dvdp_order in Hd.
have -> : 1 = val (1%g : {unit qT}) by [].
by rewrite -(eqP Hd) val_unitX.
Qed.

Lemma qX_order_dvd (i : nat) : 'qX ^+ i = 1  :> qT -> (#|qT|.-1 %| i)%N.
Proof.
rewrite -gX_order cyclic.order_dvdn => Hd.
by apply/eqP/val_inj; rewrite /= -Hd val_unitX.
Qed.

Lemma qlogp0 : qlogp 0 = 0%N.
Proof.
rewrite /qlogp; case: pickP => //= x.
by rewrite (expf_eq0 ('qX : qT))  (negPf qX_neq0) andbF.
Qed.

Lemma qlogp1 : qlogp 1 = 0%N.
Proof.
case: (qlogp 1 =P 0%N) => // /eqP log1_neq0.
have := qlogp_lt 1; rewrite ltnNge => /negP[].
apply: dvdn_leq; first by rewrite lt0n.
by rewrite qX_order_dvd // qlogp_qX ?oner_eq0.
Qed.

Lemma qlogp_eq0 (q : qT) : (qlogp q == 0%N) = (q == 0) || (q == 1).
Proof.
case: (q =P 0) => [->|/eqP q_neq0]/=; first by rewrite qlogp0.
case: (q =P 1) => [->|/eqP q_neq1]/=; first by rewrite qlogp1.
rewrite /qlogp; case: pickP => [x|/(_ (Ordinal (qlogp_lt q)))] /=.
  by case: ((x : nat) =P 0%N) => // ->; rewrite expr0 eq_sym (negPf q_neq1).
by rewrite qlogp_qX // eqxx.
Qed.

Lemma qX_exp_neq0 i : 'qX ^+ i != 0 :> qT.
Proof.  by rewrite expf_eq0 negb_and qX_neq0 orbT. Qed.

Lemma qX_exp_inj i j :
  i < #|qT|.-1 -> j < #|qT|.-1 -> 'qX ^+ i = 'qX ^+ j :> qT -> i = j.
Proof.
wlog iLj : i j / (i <= j)%N => [Hw|] iL jL Hqx.
  case: (ltngtP i j)=> // /ltnW iLj; first by apply: Hw.
  by apply/sym_equal/Hw.
suff ji_eq0 : (j - i = 0)%N by rewrite -(subnK iLj) ji_eq0.
case: ((j - i)%N =P 0%N) => // /eqP ji_neq0.
have : j - i < #|qT|.-1 by apply: leq_ltn_trans (leq_subr _ _) jL.
rewrite ltnNge => /negP[].
apply: dvdn_leq; first by rewrite lt0n.
have HqXi : 'qX ^+ i != 0 :> qT by rewrite expf_eq0 (negPf qX_neq0) andbF.
by apply/qX_order_dvd/(mulIf HqXi); rewrite mul1r -exprD subnK.
Qed.

Lemma powX_eq_mod i j : i = j %[mod #|qT|.-1] -> 'qX ^+ i = 'qX ^+ j :> qT.
Proof.
set n := _.-1 => iEj.
rewrite [i](divn_eq i n) [j](divn_eq j n) !exprD ![(_ * n)%N]mulnC.
by rewrite !exprM !qX_order_card !expr1n !mul1r iEj.
Qed.

Lemma qX_expK i : i < #|qT|.-1 -> qlogp ('qX ^+ i) = i.
Proof.
move=> iLF; apply: qX_exp_inj => //; first by apply: qlogp_lt.
by rewrite qlogp_qX // expf_eq0 (negPf qX_neq0) andbF.
Qed.

Lemma qlogpD (q1 q2 : qT) :
  q1 != 0 -> q2 != 0 ->qlogp (q1 * q2) = ((qlogp q1 + qlogp q2) %% #|qT|.-1)%N.
Proof.
move=> q1_neq0 q2_neq0.
apply: qX_exp_inj; [apply: qlogp_lt => // | rewrite ltn_mod // |].
rewrite -[RHS]mul1r -(expr1n _ ((qlogp q1 + qlogp q2) %/ #|qT|.-1)).
rewrite -qX_order_card -exprM mulnC -exprD -divn_eq exprD !qlogp_qX //.
by rewrite mulf_eq0 negb_or q1_neq0.
Qed.

End PrimitivePoly.

Section Plogp.

Variable F : finFieldType.

Definition plogp (p q : {poly F}) :=
  if boolP (primitive_poly p) is AltTrue Hh then
     qlogp ((in_qpoly p q) : {poly %/ p with primitive_mi Hh})
  else 0%N.

Lemma plogp_lt (p q : {poly F}) : 2 < size p -> plogp p q < #|{poly %/ p}|.-1.
Proof.
move=> /ltnW size_gt1.
rewrite /plogp.
case (boolP (primitive_poly p)) => // Hh; first by apply: qlogp_lt.
by rewrite ltn_predRL (card_finNzRing_gt1 {poly %/ p}).
Qed.

Lemma plogp_X (p q : {poly F}) :
  2 < size p -> primitive_poly p -> ~~ (p %| q) -> p %| q - 'X ^+ plogp p q.
Proof.
move=> sp_gt2 Hh pNDq.
rewrite /plogp.
case (boolP (primitive_poly p)) => // Hh'; last by case/negP: Hh'.
have pM : p \is monic by case/and4P: Hh'.
have pMi : monic_irreducible_poly p by apply: primitive_mi.
set q' : {poly %/ p with primitive_mi Hh'} := in_qpoly p q.
apply/modp_eq0P; rewrite modpD modpN; apply/eqP; rewrite subr_eq0; apply/eqP.
rewrite !Pdiv.IdomainMonic.modpE //=.
suff /val_eqP/eqP/= : 'qX ^+ qlogp q' = q'.
  rewrite /= [X in rmodp _ X]mk_monicE // => <-.
  by rewrite poly_of_qpolyX /= mk_monicE // [rmodp 'X p]rmodp_small ?size_polyX.
apply: qlogp_qX => //.
apply/eqP=> /val_eqP/eqP.
rewrite /= mk_monicE // => /rmodp_eq0P; rewrite -dvdpE => pDq.
by case/negP: pNDq.
Qed.

Lemma plogp0 (p : {poly F}) : 2 < size p -> plogp p 0 = 0%N.
Proof.
move=> sp_gt2; rewrite /plogp; case (boolP (primitive_poly p)) => // i.
by rewrite in_qpoly0 qlogp0.
Qed.

Lemma plogp1 (p : {poly F}) : 2 < size p -> plogp p 1 = 0%N.
Proof.
move=> sp_gt2; rewrite /plogp; case (boolP (primitive_poly p)) => // i.
suff->: in_qpoly p 1 = 1 by apply: qlogp1.
apply/val_eqP/eqP; apply: in_qpoly_small.
rewrite mk_monicE ?size_poly1 ?(leq_trans _ sp_gt2) //.
by apply: primitive_mi.
Qed.

Lemma plogp_div_eq0 (p q : {poly F}) :
  2 < size p -> (p %| q) -> plogp p q = 0%N.
Proof.
move=> sp_gt2; rewrite /plogp; case (boolP (primitive_poly p)) => // i pDq.
suff-> : in_qpoly p q = 0 by apply: qlogp0.
by apply/eqP; rewrite primitive_poly_in_qpoly_eq0.
Qed.

Lemma plogpD (p q1 q2 : {poly F}) :
  2 < size p -> primitive_poly p -> ~~ (p %| q1) -> ~~ (p %| q2) ->
  plogp p (q1 * q2) = ((plogp p q1 + plogp p q2) %% #|{poly %/ p}|.-1)%N.
Proof.
move=> sp_gt2 Pp pNDq1 pNDq2.
rewrite /plogp; case (boolP (primitive_poly p)) => [|/negP//] i /=.
have pmi := primitive_mi i.
by rewrite rmorphM qlogpD //= primitive_poly_in_qpoly_eq0.
Qed.

End Plogp.

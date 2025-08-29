(* Distributed under the terms of CeCILL-B.                                  *)
From elpi Require Import derive.std param2.
From mathcomp Require Import NatDef.
From Corelib Require Import IntDef.
From mathcomp Require Import micromega_formula micromega_witness.
From mathcomp Require Import micromega_checker micromega_eval.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import preorder ssralg ssrint binnums.
From mathcomp.algebra Extra Dependency "ring.elpi" as ring.
From mathcomp.algebra Extra Dependency "ring_tac.elpi" as ring_tac.

(******************************************************************************)
(* This file provides the ring tactic.                                        *)
(*                                                                            *)
(* This tactic provides:                                                      *)
(*         ring == a decision procedure for ring and semiring equalities      *)
(* These tactics work on any comPzSemiRingType and handle additive morphisms  *)
(* {additive _ -> _} and ring morphisms {rmorphism _ -> _}.                   *)
(*                                                                            *)
(* See file test-suite/test_ring.v for examples of use.                       *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.

Module Import Internals.

Section Env.
Variables (R : Type) (rO : R).
Implicit Type l : seq R.

Definition env_nth (n : positive) l := nth rO l (Pos.to_nat n).-1.
Definition env_jump (j : positive) l := drop (Pos.to_nat j) l.

Lemma env_jumpD l j j' : env_jump (Pos.add j j') l = env_jump j' (env_jump j l).
Proof. by rewrite /env_jump drop_drop Pos_to_natD addnC. Qed.

Lemma env_nth_jump l i j : env_nth i (env_jump j l) = env_nth (Pos.add i j) l.
Proof.
by rewrite /env_nth nth_drop Pos_to_natD -!subn1 addnBA 1?addnC ?Pos_to_nat_gt0.
Qed.

End Env.

Section PevalSemiRing.
Variable C : pzSemiRingType.
Variable R : comPzSemiRingType.
Variable R_of_C : {rmorphism C -> R}.

Implicit Type P : Pol C.
Implicit Type l : seq R.

#[local] Notation env_nth := (env_nth 0).
#[local] Notation Peval := (Peval
  +%R *%R N.to_nat (@GRing.exp R) R_of_C (@env_jump R) env_nth).
#[local] Notation Peq := (Peq eq_op).
#[local] Notation P0 := (P0 0).
#[local] Notation P1 := (P1 1).
#[local] Notation mkX := (mkX 0 1).
#[local] Notation mkPX := (mkPX 0 eq_op).
#[local] Notation PaddC := (PaddC +%R).
#[local] Notation Padd := (Padd 0 +%R eq_op).
#[local] Notation PaddI := (PaddI +%R Padd).
#[local] Notation PaddX := (PaddX 0 eq_op Padd).
#[local] Notation Pmul := (Pmul 0 1 +%R *%R eq_op).
#[local] Notation PmulC_aux := (PmulC_aux 0 *%R eq_op).
#[local] Notation PmulC := (PmulC 0 1 *%R eq_op).
#[local] Notation PmulI := (PmulI 0 1 *%R eq_op Pmul).
#[local] Notation Ppow_pos := (Ppow_pos 0 1 +%R *%R eq_op).
#[local] Notation Ppow_N := (Ppow_N 0 1 +%R *%R eq_op).

Lemma Peval_Peq l P P' : Peq P P' -> Peval l P = Peval l P'.
Proof.
elim: P l P' => [c | i P IH | P IHP j Q IHQ] l [c' | i' P' | P' j' Q'] //=.
- by move=> /eqP->.
- by case: pos_nat_compareP => //; apply: IH.
- by case: pos_nat_compareP => //; case: ifP => // /IHP-> /IHQ->.
Qed.

Lemma Peval_mkPinj l j P : Peval l (mkPinj j P) = Peval (env_jump j l) P.
Proof. by case: P => [//| j' Q /= |//]; rewrite env_jumpD. Qed.

Lemma Peval_mkX l j : Peval l (mkX j) = env_nth j l.
Proof.
case: j => [j|j|]/=; rewrite rmorph1 rmorph0 mul1r addr0 expr1 ?env_nth_jump//.
congr (env_nth _ l); apply: Pos_to_natI; rewrite !Pos_to_natE.
by rewrite [LHS]add1n prednK// -double0 ltn_double Pos_to_nat_gt0.
Qed.

Lemma Peval_mkPX l P i Q : Peval l (mkPX P i Q)
  = Peval l P * (env_nth 1 l) ^+ Pos.to_nat i + Peval (env_jump 1 l) Q.
Proof.
case: P => [c |//| P' i' [c |//|//]] /=.
  by case: eqP => [->|//]; rewrite rmorph0 mul0r add0r Peval_mkPinj.
by case: eqP => [->|//]/=; rewrite rmorph0 addr0 Pos_to_natD exprD mulrA.
Qed.

Lemma Popp_id P : Popp id P = P.
Proof. by elim: P => [| j P /=->// | P /=-> i Q ->]. Qed.

Lemma PevalDC l P c : Peval l (PaddC P c) = Peval l P + R_of_C c.
Proof.
by elim: P l => [c'|i P IH|P IHP j Q IHQ] l/=; rewrite ?rmorphD ?IH ?IHQ ?addrA.
Qed.

Lemma Peval_addI l P j Q :
    (forall l P, Peval l (Padd P Q) = Peval l P + Peval l Q) ->
  Peval l (PaddI Q j P) = Peval l P + Peval l (Pinj j Q).
Proof.
move=> PevalD; elim: P j l => [c | j' Q' IH | P IHP i Q' IHQ'] j l /=.
- by rewrite Peval_mkPinj PevalDC addrC.
- move: (Zint_pos_sub (pos_nat_Pos_to_nat j') (pos_nat_Pos_to_nat j)).
  case: ZintP => [//| _ /eqP+ _ | k nk _ /[swap] | k nk _ /[swap] ].
  + rewrite subr_eq0 => /eqP[]/Pos_to_natI->.
    by rewrite Peval_mkPinj PevalD.
  + move=> /eqP<- /eqP/[!subr_eq]/eqP[+] _.
    rewrite addnC -Pos_to_natD => /Pos_to_natI->.
    by rewrite Peval_mkPinj PevalD /= env_jumpD.
  + move=> /eqP/[!NegzE]<- /eqP; rewrite -opprB eqr_opp subr_eq => /eqP[+] _.
    rewrite addnC -Pos_to_natD => /Pos_to_natI->.
    by rewrite Peval_mkPinj IH /= env_jumpD.
- case: j => [j | j |]/=.
  + by rewrite IHQ' addrA /= -env_jumpD.
  + rewrite IHQ' addrA /= -env_jumpD.
    congr (_ + Peval (env_jump _ l) _).
    apply: Pos_to_natI; rewrite !Pos_to_natE add1n prednK//.
    by rewrite -double0 ltn_double Pos_to_nat_gt0.
  + by rewrite PevalD addrA.
Qed.

Lemma Peval_addX l P P' i' :
    (forall l P, Peval l (Padd P P') = Peval l P + Peval l P') ->
  Peval l (PaddX P' i' P) = Peval l P + Peval l (PX P' i' P0).
Proof.
rewrite /= rmorph0 addr0 addrC.
move=> PevalD; elim: P i' l => [//| j Q' IH | P IHP i Q' IHQ'] i' l /=.
- case: j => [j | j |//]/=; rewrite -env_jumpD//.
  congr (_ + Peval (env_jump _ l) _).
  apply: Pos_to_natI; rewrite !Pos_to_natE add1n prednK//.
  by rewrite -double0 ltn_double Pos_to_nat_gt0.
- rewrite addrA.
  move: (Zint_pos_sub (pos_nat_Pos_to_nat i) (pos_nat_Pos_to_nat i')).
  case: ZintP => [//| _ /eqP+ _ | k nk _ /[swap] | k nk _ /[swap] ].
  + rewrite subr_eq0 => /eqP[]/Pos_to_natI->.
    by rewrite Peval_mkPX PevalD -mulrDl [Peval l P' + Peval l P]addrC.
  + move=> /eqP<- /eqP/[!subr_eq]/eqP[+] _.
    rewrite addnC -Pos_to_natD => /Pos_to_natI->.
    rewrite Peval_mkPX PevalD [_ + Peval l P']addrC mulrDl /= rmorph0 addr0.
    by rewrite -mulrA -exprD Pos_to_natD addnC.
  + move=> /eqP/[!NegzE]<- /eqP; rewrite -opprB eqr_opp subr_eq => /eqP[+] _.
    rewrite addnC -Pos_to_natD => /Pos_to_natI->.
    by rewrite Peval_mkPX IHP mulrDl -mulrA -exprD Pos_to_natD addnC.
Qed.

Lemma PevalD l P P' : Peval l (Padd P P') = Peval l P + Peval l P'.
Proof.
elim: P' l P => [c | j' Q' IH | P' IHP' i' Q' IHQ'] l P /=.
- by rewrite PevalDC.
- by rewrite Peval_addI.
case: P => [c | j Q | P i Q] /=.
- by rewrite PevalDC addrA addrC.
- rewrite addrCA; case: j => [j | j |] /=; rewrite IHQ'/= -?env_jumpD//.
  congr (_ + (Peval (env_jump _ l) _ + _)); apply: Pos_to_natI.
  by rewrite !Pos_to_natE add1n prednK// -double0 ltn_double Pos_to_nat_gt0.
- rewrite addrACA.
  move: (Zint_pos_sub (pos_nat_Pos_to_nat i) (pos_nat_Pos_to_nat i')).
  case: ZintP => [//| _ /eqP+ _ | k nk _ /[swap] | k nk _ /[swap] ].
  + rewrite subr_eq0 => /eqP[]/Pos_to_natI->.
    by rewrite Peval_mkPX IHP' IHQ' mulrDl.
  + move=> /eqP<- /eqP/[!subr_eq]/eqP[+] _.
    rewrite -Pos_to_natD => /Pos_to_natI->.
    rewrite Peval_mkPX IHP'/= rmorph0 addr0 mulrDl IHQ'.
    by rewrite -mulrA -exprD Pos_to_natD.
  + move=> /eqP/[!NegzE]<- /eqP; rewrite -opprB eqr_opp subr_eq => /eqP[+] _.
    rewrite -Pos_to_natD => /Pos_to_natI->.
    rewrite Peval_mkPX (Peval_addX _ _ _ IHP')/= rmorph0 addr0 mulrDl IHQ'.
    by rewrite -mulrA -exprD Pos_to_natD.
Qed.

Lemma PsubI_addI P j Q :
    (forall P', Psub 0 +%R +%R id eq_op P' P = Padd P' P) ->
  PsubI +%R id (Psub 0 +%R +%R id eq_op) P j Q = PaddI P j Q.
Proof.
elim: Q j => [c | j' P' IH | P' IHP i Q' IHQ ] j Psub_add /=.
- by rewrite Popp_id.
- by case: Z.pos_sub => [| p | p]; rewrite ?Psub_add ?IH.
- by case: j => [p | p |]; rewrite ?Psub_add ?IHQ.
Qed.

Lemma PsubX_addX P' i P :
    (forall P, Psub 0 +%R +%R id eq_op P P' = Padd P P') ->
  PsubX 0 id eq_op (Psub 0 +%R +%R id eq_op) P' i P = PaddX P' i P.
Proof.
elim: P i => [c | j P IH | P IHP i' Q IHQ] i Psub_add /=.
- by rewrite Popp_id.
- by case: j => [p | p |] /=; rewrite Popp_id.
- by case: Z.pos_sub => [| p | p]; rewrite ?Psub_add ?IHP.
Qed.

Lemma Psub_add P P' : Psub 0 +%R +%R id eq_op P P' = Padd P P'.
Proof.
elim: P' P => [//| j' P' IH | P' IHP' i' Q' IHQ' ] P /=.
  by rewrite PsubI_addI.
case: P => [c | j P | P i Q] /=; first by rewrite !Popp_id.
  by case: j => [p | p |]; rewrite Popp_id IHQ'.
by case: Z.pos_sub => [| p | p]; rewrite ?IHP' ?IHQ' ?PsubX_addX.
Qed.

Lemma Peval_mulC_aux l P c : Peval l (PmulC_aux P c) = Peval l P * R_of_C c.
Proof.
elim: P l => [c' | j Q IH | P IHP i Q IHQ] l /=; first by rewrite rmorphM.
  by rewrite Peval_mkPinj IH.
by rewrite Peval_mkPX IHP IHQ mulrAC -mulrDl.
Qed.

Lemma PevalMC l P c : Peval l (PmulC P c) = Peval l P * R_of_C c.
Proof.
rewrite /PmulC/=; case: eqP => [->|_]; first by rewrite /= rmorph0 mulr0.
by case: eqP => [->|_]; rewrite ?rmorph1 ?mulr1 ?Peval_mulC_aux.
Qed.

Lemma Peval_mulI l P j Q :
    (forall l P, Peval l (Pmul P Q) = Peval l P * Peval l Q) ->
  Peval l (PmulI Q j P) = Peval l P * Peval l (Pinj j Q).
Proof.
move=> PevalM; elim: P j l => [c | j' Q' IH | P IHP i Q' IHQ'] j l /=.
- by rewrite Peval_mkPinj PevalMC mulrC.
- move: (Zint_pos_sub (pos_nat_Pos_to_nat j') (pos_nat_Pos_to_nat j)).
  case: ZintP => [//| _ /eqP+ _ | k nk _ /[swap] | k nk _ /[swap] ].
  + rewrite subr_eq0 => /eqP[]/Pos_to_natI->.
    by rewrite Peval_mkPinj PevalM.
  + move=> /eqP<- /eqP/[!subr_eq]/eqP[+] _.
    rewrite addnC -Pos_to_natD => /Pos_to_natI->.
    by rewrite Peval_mkPinj PevalM/= env_jumpD.
  + move=> /eqP/[!NegzE]<- /eqP; rewrite -opprB eqr_opp subr_eq => /eqP[+] _.
    rewrite addnC -Pos_to_natD => /Pos_to_natI->.
    by rewrite Peval_mkPinj IH/= env_jumpD.
- case: j => [j | j |]; rewrite Peval_mkPX IHP mulrAC.
  + by rewrite IHQ'/= -env_jumpD -mulrDl.
  + rewrite IHQ'/= -env_jumpD.
    have -> : Pos.add xH (Pos.pred_double j) = xO j; last by rewrite -mulrDl.
    apply: Pos_to_natI; rewrite !Pos_to_natE add1n prednK//.
    by rewrite -double0 ltn_double Pos_to_nat_gt0.
  + by rewrite PevalM -mulrDl.
Qed.

Lemma PevalM l P P' : Peval l (Pmul P P') = Peval l P * Peval l P'.
Proof.
elim: P' l P => [c | j' Q' IH | P' IHP' i' Q' IHQ'] l P /=.
- by rewrite PevalMC.
- by rewrite Peval_mulI.
case: P => [c | j Q | P i Q] /=.
- by rewrite PevalMC mulrC.
- rewrite Peval_mkPX IHP' mulrDr mulrA.
  case: j => [j | j |] /=; rewrite IHQ'/= -?env_jumpD//.
  congr (_ + (Peval (env_jump _ l) _ * _)); apply: Pos_to_natI.
  by rewrite !Pos_to_natE add1n prednK// -double0 ltn_double Pos_to_nat_gt0.
rewrite PevalD !Peval_mkPX PevalD Peval_mkPX.
rewrite !IHP' (Peval_mulI _ _ _ IHQ') /= rmorph0 !addr0 Peval_mkPinj IHQ'.
rewrite mulrDl -mulrA mulrACA /=.
rewrite -[X in _ + X + _]mulrA -[X in _ + _ + (X + _)]mulrAC.
set p := Peval l P * _; set p' := Peval l P' * _.
set q := Peval _ Q; set q' := Peval _ Q'.
by rewrite addrACA mulrDl !mulrDr.
Qed.

Lemma Peval_pow_pos l res P p :
  Peval l (Ppow_pos res P p) = Peval l res * Peval l P ^+ Pos.to_nat p.
Proof.
elim: p l res P => [p IH | p IH |] l res P /=.
- rewrite PevalM !IH -mulrAC -mulrA -exprS -mulrA -exprD.
  by rewrite addnS addnn Pos_to_natE.
- by rewrite !IH -mulrA -exprD addnn Pos_to_natE.
- by rewrite PevalM expr1.
Qed.

Lemma Peval_pow_N l P n : Peval l (Ppow_N P n) = Peval l P ^+ N.to_nat n.
Proof. by case: n => [| p]/=; rewrite ?Peval_pow_pos /= rmorph1 ?mul1r. Qed.

End PevalSemiRing.

Section PevalRing.
Variable C : pzRingType.
Variable R : comPzRingType.
Variable R_of_C : {rmorphism C -> R}.

Implicit Type P : Pol C.
Implicit Type l : seq R.

#[local] Notation Peval := (Peval
  +%R *%R N.to_nat (@GRing.exp R) R_of_C (@env_jump R) (env_nth 0)).
#[local] Notation P0 := (P0 0).
#[local] Notation Popp := (Popp -%R).
#[local] Notation PsubC := (PsubC (fun x y => x - y)).
#[local] Notation Psub := (Psub 0 +%R (fun x y => x - y) -%R eq_op).
#[local] Notation PsubI := (PsubI +%R -%R Psub).
#[local] Notation PsubX := (PsubX 0 -%R eq_op Psub).

Lemma PevalN l P : Peval l (Popp P) = - Peval l P.
Proof.
elim: P l => [c | i P IH | P IHP j Q IHQ] l /=; rewrite ?rmorphN ?IH//.
by rewrite IHP IHQ opprD mulNr.
Qed.

Lemma PevalBC l P c : Peval l (PsubC P c) = Peval l P - R_of_C c.
Proof.
by elim: P l => [c'|i P IH|P IHP j Q IHQ] l/=; rewrite ?rmorphB ?IH ?IHQ ?addrA.
Qed.

Lemma Peval_subI l P j Q :
    (forall l P, Peval l (Psub P Q) = Peval l P - Peval l Q) ->
  Peval l (PsubI Q j P) = Peval l P - Peval l (Pinj j Q).
Proof.
move=> PevalB; elim: P j l => [c | j' Q' IH | P IHP i Q' IHQ'] j l /=.
- by rewrite Peval_mkPinj PevalDC PevalN addrC.
- move: (Zint_pos_sub (pos_nat_Pos_to_nat j') (pos_nat_Pos_to_nat j)).
  case: ZintP => [//| _ /eqP+ _ | k nk _ /[swap] | k nk _ /[swap] ].
  + rewrite subr_eq0 => /eqP[]/Pos_to_natI->.
    by rewrite Peval_mkPinj PevalB.
  + move=> /eqP<- /eqP/[!subr_eq]/eqP[+] _.
    rewrite addnC -Pos_to_natD => /Pos_to_natI->.
    by rewrite Peval_mkPinj PevalB /= env_jumpD.
  + move=> /eqP/[!NegzE]<- /eqP; rewrite -opprB eqr_opp subr_eq => /eqP[+] _.
    rewrite addnC -Pos_to_natD => /Pos_to_natI->.
    by rewrite Peval_mkPinj IH /= env_jumpD.
- case: j => [j | j |]/=.
  + by rewrite IHQ' addrA /= -env_jumpD.
  + rewrite IHQ' addrA /= -env_jumpD.
    congr (_ - Peval (env_jump _ l) _).
    apply: Pos_to_natI; rewrite !Pos_to_natE add1n prednK//.
    by rewrite -double0 ltn_double Pos_to_nat_gt0.
  + by rewrite PevalB addrA.
Qed.

Lemma Peval_subX l P P' i' :
    (forall l P, Peval l (Psub P P') = Peval l P - Peval l P') ->
  Peval l (PsubX P' i' P) = Peval l P - Peval l (PX P' i' P0).
Proof.
rewrite /= rmorph0 addr0 addrC.
move=> PevalB; elim: P i' l => [c | j Q' IH | P IHP i Q' IHQ'] i' l /=.
- by rewrite PevalN mulNr.
- case: j => [j | j |]/=; rewrite PevalN mulNr -?env_jumpD//.
  congr (_ + Peval (env_jump _ l) _).
  apply: Pos_to_natI; rewrite !Pos_to_natE add1n prednK//.
  by rewrite -double0 ltn_double Pos_to_nat_gt0.
- rewrite addrA -mulNr.
  move: (Zint_pos_sub (pos_nat_Pos_to_nat i) (pos_nat_Pos_to_nat i')).
  case: ZintP => [//| _ /eqP+ _ | k nk _ /[swap] | k nk _ /[swap] ].
  + rewrite subr_eq0 => /eqP[]/Pos_to_natI->.
    by rewrite Peval_mkPX PevalB [Peval l P - Peval l P']addrC mulrDl.
  + move=> /eqP<- /eqP/[!subr_eq]/eqP[+] _.
    rewrite addnC -Pos_to_natD => /Pos_to_natI->.
    rewrite Peval_mkPX PevalB [_ - Peval l P']addrC mulrDl /= rmorph0 addr0.
    by rewrite -mulrA -exprD Pos_to_natD addnC.
  + move=> /eqP/[!NegzE]<- /eqP; rewrite -opprB eqr_opp subr_eq => /eqP[+] _.
    rewrite addnC -Pos_to_natD => /Pos_to_natI->.
    by rewrite Peval_mkPX IHP -mulNr mulrDl -mulrA -exprD Pos_to_natD addnC.
Qed.

Lemma PevalB l P P' : Peval l (Psub P P') = Peval l P - Peval l P'.
Proof.
elim: P' l P => [c | j' Q' IH | P' IHP' i' Q' IHQ'] l P /=.
- by rewrite PevalBC.
- by rewrite Peval_subI.
case: P => [c | j Q | P i Q] /=.
- by rewrite PevalDC addrA addrC !PevalN mulNr -opprD.
- rewrite opprD addrCA -mulNr.
  case: j => [j | j |] /=; rewrite PevalN IHQ'/= -?env_jumpD//.
  congr (_ + (Peval (env_jump _ l) _ + _)); apply: Pos_to_natI.
  by rewrite !Pos_to_natE add1n prednK// -double0 ltn_double Pos_to_nat_gt0.
- rewrite opprD addrACA.
  move: (Zint_pos_sub (pos_nat_Pos_to_nat i) (pos_nat_Pos_to_nat i')).
  case: ZintP => [//| _ /eqP+ _ | k nk _ /[swap] | k nk _ /[swap] ].
  + rewrite subr_eq0 => /eqP[]/Pos_to_natI->.
    by rewrite Peval_mkPX IHP' IHQ' mulrBl.
  + move=> /eqP<- /eqP/[!subr_eq]/eqP[+] _.
    rewrite -Pos_to_natD => /Pos_to_natI->.
    rewrite Peval_mkPX IHP'/= rmorph0 addr0 mulrDl IHQ'.
    by rewrite mulNr -mulrA -exprD Pos_to_natD.
  + move=> /eqP/[!NegzE]<- /eqP; rewrite -opprB eqr_opp subr_eq => /eqP[+] _.
    rewrite -Pos_to_natD => /Pos_to_natI->.
    rewrite Peval_mkPX (Peval_subX _ _ _ IHP')/= rmorph0 addr0 mulrDl IHQ'.
    by rewrite mulNr -mulrA -exprD Pos_to_natD.
Qed.

End PevalRing.

Section MevalSemiRing.
Variable C : pzSemiRingType.
Variable R : comPzSemiRingType.
Variable R_of_C : {rmorphism C -> R}.
Variable (cdiv : C -> C -> C * C).
Variable (cdivP : forall x y, let (q, r) := cdiv x y in x = y * q + r).

Implicit Type P : Pol C.
Implicit Type M : Mon.
Implicit Type l : seq R.

#[local] Notation env_nth := (env_nth 0).
#[local] Notation Peval := (Peval
  +%R *%R N.to_nat (@GRing.exp R) R_of_C (@env_jump R) env_nth).
#[local] Notation Peq := (Peq eq_op).
#[local] Notation P0 := (P0 0).
#[local] Notation P1 := (P1 1).
#[local] Notation mkX := (mkX 0 1).
#[local] Notation mkPX := (mkPX 0 eq_op).
#[local] Notation PaddC := (PaddC +%R).
#[local] Notation Padd := (Padd 0 +%R eq_op).
#[local] Notation PaddI := (PaddI +%R Padd).
#[local] Notation PaddX := (PaddX 0 eq_op Padd).
#[local] Notation Pmul := (Pmul 0 1 +%R *%R eq_op).
#[local] Notation PmulC_aux := (PmulC_aux 0 *%R eq_op).
#[local] Notation PmulC := (PmulC 0 1 *%R eq_op).
#[local] Notation PmulI := (PmulI 0 1 *%R eq_op Pmul).
#[local] Notation Ppow_pos := (Ppow_pos 0 1 +%R *%R eq_op).
#[local] Notation Ppow_N := (Ppow_N 0 1 +%R *%R eq_op).

#[local] Notation Meval := (Meval
  1 *%R N.to_nat (@GRing.exp R) (@env_jump R) env_nth).
#[local] Notation cMeval := (cMeval
  1 *%R N.to_nat (@GRing.exp R) R_of_C (@env_jump R) env_nth).
#[local] Notation CFactor := (CFactor 0 cdiv eq_op).
#[local] Notation MFactor := (MFactor 0 1 cdiv eq_op).
#[local] Notation POneSubst := (POneSubst 0 1 +%R *%R cdiv eq_op).
#[local] Notation PNSubst1 := (PNSubst1 0 1 +%R *%R cdiv eq_op).
#[local] Notation PNSubst := (PNSubst 0 1 +%R *%R cdiv eq_op).
#[local] Notation PSubstL1 := (PSubstL1 0 1 +%R *%R cdiv eq_op).
#[local] Notation PSubstL := (PSubstL 0 1 +%R *%R cdiv eq_op).
#[local] Notation PNSubstL := (PNSubstL 0 1 +%R *%R cdiv eq_op).
#[local] Notation Mon_of_Pol := (Mon_of_Pol 0 eq_op).

Lemma Meval_mkZmon l j M : Meval l (mkZmon j M) = Meval l (zmon j M).
Proof. by case: M. Qed.

Lemma Meval_zmon_pred l j M :
  Meval (env_jump 1 l) (zmon_pred j M) = Meval l (zmon j M).
Proof.
case: j => [p | p |//]; rewrite ?Meval_mkZmon/= -?env_jumpD//.
congr (Meval (env_jump _ l) M); apply: Pos_to_natI.
by rewrite !Pos_to_natE add1n prednK// double_gt0 Pos_to_nat_gt0.
Qed.

Lemma Meval_mkVmon l i M :
  Meval l (mkVmon i M) = Meval l M * env_nth 1 l ^+ Pos.to_nat i.
Proof.
case: M => [//| j M | i' M] /=; rewrite ?Meval_zmon_pred//.
by rewrite Pos_to_natD addnC exprD mulrA.
Qed.

Lemma Peval_CFactor l P c : let (Q, R) := CFactor P c in
  Peval l P = Peval l Q + R_of_C c * Peval l R.
Proof.
elim: P l => [c' | j P IH | P IHP i Q IHQ] l /=.
- by case: cdiv (cdivP c' c) => q r -> /=; rewrite rmorphD rmorphM addrC.
- by case: CFactor (IH (env_jump j l)) => R' S /=; rewrite !Peval_mkPinj.
case: CFactor (IHP l) => R1 S1 ->.
case: CFactor (IHQ (env_jump 1 l)) => R2 S2 ->.
by rewrite !Peval_mkPX mulrDr mulrA addrACA -mulrDl.
Qed.

Lemma Meval_MFactor l P c M : let (Q, R) := MFactor P c M in
  Peval l P = Peval l Q + cMeval l (c, M) * Peval l R.
Proof.
rewrite /cMeval; elim: P l M => [c'|j P IH|P IHP i Q IHQ] l [|jM M|iM M]/=.
- case: eqP => [->|_] /=; first by rewrite rmorph0 rmorph1 add0r !mul1r.
  by case: cdiv (cdivP c' c) => q r -> /=; rewrite rmorphD rmorphM mulr1 addrC.
- by rewrite rmorph0 mulr0 addr0.
- by rewrite rmorph0 mulr0 addr0.
- case: eqP => [->|_] /=; first by rewrite rmorph0 rmorph1 add0r !mul1r.
  case: CFactor (Peval_CFactor (env_jump j l) P c) => Q R' ->.
  by rewrite !Peval_mkPinj mulr1.
- case: pos_nat_compareP => [| jjM | jMj].
  + by case: MFactor (IH (env_jump j l) M) => Q R' ->; rewrite !Peval_mkPinj.
  + case: MFactor (IH (env_jump j l) (zmon (Pos.sub jM j) M)) => Q R' ->.
    rewrite !Peval_mkPinj /= -env_jumpD (_ : Pos.add j (Pos.sub jM j) = jM)//.
    by apply: Pos_to_natI; rewrite Pos_to_natD Pos_to_natB// subnKC// ltnW.
  + by rewrite /= rmorph0 mulr0 addr0.
- by rewrite rmorph0 mulr0 addr0.
- case: eqP => [->|_] /=; first by rewrite rmorph0 rmorph1 add0r !mul1r.
  case: CFactor (Peval_CFactor l P c) => R1 S1 ->.
  case: CFactor (Peval_CFactor (env_jump 1 l) Q c) => R2 S2 ->.
  by rewrite mulr1 !Peval_mkPX mulrDr mulrA addrACA -mulrDl.
- case: MFactor (IHP l (zmon jM M)) => R1 S1 ->.
  case: MFactor (IHQ (env_jump 1 l) (zmon_pred jM M)) => R2 S2 ->.
  by rewrite /= !Peval_mkPX mulrDr mulrA addrACA -mulrDl Meval_zmon_pred.
- case: pos_nat_compareP => [| iiM | iMi].
  + case: MFactor (IHP l (mkZmon 1 M)) => R1 S1 ->.
    by rewrite Peval_mkPX addrAC mulrA [in RHS]mulrAC -mulrDl Meval_mkZmon.
  + case: MFactor (IHP l (vmon (Pos.sub iM i) M)) => R1 S1 ->.
    rewrite Peval_mkPX addrAC mulrDl/= mulrAC ![_ * Peval l S1]mulrC.
    by rewrite mulrA -mulrA -exprD mulrA Pos_to_natB ?subnK// ltnW.
  + case: MFactor (IHP l (mkZmon 1 M)) => R1 S1 ->.
    rewrite !Peval_mkPX addrAC mulrDl Meval_mkZmon/= rmorph0 addr0 mulrACA.
    by rewrite -!mulrA -exprD mulrA mulrACA !mulrA Pos_to_natB ?subnKC// ltnW.
Qed.

Lemma Peval_POneSubst l P1 cM1 P2 P3 : POneSubst P1 cM1 P2 = Some P3 ->
  cMeval l cM1 = Peval l P2 -> Peval l P1 = Peval l P3.
Proof.
case: cM1 => cc M1 /=; case: MFactor (Meval_MFactor l P1 cc M1) => Q1 R1 -> eP3.
suff -> : P3 = Padd Q1 (Pmul P2 R1) by rewrite PevalD PevalM => <-.
by case: R1 eP3 => [c |? ?|? ? ?]; [case: eqP => [//|_]| |] => -[].
Qed.

Lemma Peval_PNSubst1 l n P1 cM1 P2 : cMeval l cM1 = Peval l P2 ->
  Peval l P1 = Peval l (PNSubst1 P1 cM1 P2 n).
Proof.
by elim: n P1 => [|n IHn] /= P1;
  case: POneSubst (@Peval_POneSubst l P1 cM1 P2) => // P eP eOS;
  rewrite -?IHn//; apply: eP.
Qed.

Lemma Peval_PNSubst l n P1 cM1 P2 P3 : PNSubst P1 cM1 P2 n = Some P3 ->
  cMeval l cM1 = Peval l P2 -> Peval l P1 = Peval l P3.
Proof.
rewrite /PNSubst; case: POneSubst (@Peval_POneSubst l P1 cM1 P2) => // P.
by case: n => [//|n] /(_ P erefl) + [<-] ?; rewrite -Peval_PNSubst1//; apply.
Qed.

Lemma Peval_PSubstL1 l n LM1 P1 :
    all (fun MP => cMeval l MP.1 == Peval l MP.2) LM1 ->
  Peval l P1 = Peval l (PSubstL1 P1 LM1 n).
Proof.
elim: LM1 P1 => [//|[M2 P2] LM2 IH] /= P1 /andP[/eqP eMP2 aLM2].
by rewrite -IH// -Peval_PNSubst1.
Qed.

Lemma Peval_PSubstL l n LM1 P1 P2 : PSubstL P1 LM1 n = Some P2 ->
    all (fun MP => cMeval l MP.1 == Peval l MP.2) LM1 ->
  Peval l P1 = Peval l P2.
Proof.
elim: LM1 P1 => [//|[M2 P2'] LM2 IH] /= P3 + /andP[/eqP M2P2' a].
case: PNSubst (@Peval_PNSubst l n P3 M2 P2') => [P /(_ P erefl) eP|_].
- by move=> -[<-]; rewrite -Peval_PSubstL1// eP.
- by move=> ?; apply: IH.
Qed.

Lemma Peval_PNSubstL l m n LM1 P1 :
    all (fun MP => cMeval l MP.1 == Peval l MP.2) LM1 ->
  Peval l P1 = Peval l (PNSubstL P1 LM1 m n).
Proof.
by elim: m LM1 P1 => [|m IHm] LM1 P1 a /=;
  case: PSubstL (@Peval_PSubstL l n LM1 P1) => // P /(_ P erefl);
  rewrite -?IHm//; apply.
Qed.

Lemma Meval_Mon_of_Pol l P m : Mon_of_Pol P = Some m ->
  cMeval l m = Peval l P.
Proof.
case: m => c M; elim: P l c M => [c' | j P IH | P IHP i Q IHQ] l c M /=.
- by case: eqP => [//|_] [<- <-]; rewrite /cMeval/= mulr1.
- case: Mon_of_Pol IH => // -[{}c {}M] /[swap] -[<- <-].
  by rewrite /cMeval Meval_mkZmon/=; apply.
rewrite -[match Q with Pc _ => _ | _ => _ end]/(Peq Q P0).
case: Peq (@Peval_Peq _ _ R_of_C (env_jump 1 l) Q P0) => [/(_ erefl)/= Q0|//].
case: Mon_of_Pol IHP => // -[{}c {}M] /[swap] -[<- <-] /(_ l _ _ erefl)<-.
by rewrite Q0 rmorph0 addr0 /cMeval/= Meval_mkVmon mulrA.
Qed.

End MevalSemiRing.

Section Csemiring_correct.
Variables (R C : comPzSemiRingType) (R_of_C : {rmorphism C -> R}).
Variables (cdiv : C -> C -> C * C).
Variables (cdivP : forall x y, let (q, r) := cdiv x y in x = y * q + r).

Implicit Type l : seq R.

#[local] Notation Peval := (Peval
  +%R *%R N.to_nat (@GRing.exp R) R_of_C (@env_jump R) (env_nth 0)).
#[local] Notation cMeval := (cMeval
  1 *%R N.to_nat (@GRing.exp R) R_of_C (@env_jump R) (env_nth 0)).
#[local] Notation PEeval := (PEeval +%R *%R +%R id
  N.to_nat (@GRing.exp R) R_of_C (env_nth 0)).
#[local] Notation PEeval_eqs := (PEeval_eqs +%R *%R +%R id
  N.to_nat (@GRing.exp R) eq R_of_C (env_nth 0)).
#[local] Notation Peq := (Peq eq_op).
#[local] Notation Pol_of_PExpr := (Pol_of_PExpr 0 1 +%R *%R +%R id eq_op).
#[local] Notation mk_monpol_list := (mk_monpol_list
  0 1 +%R *%R +%R id cdiv eq_op).
#[local] Notation norm_subst := (norm_subst 0 1 +%R *%R +%R id cdiv eq_op).
#[local] Notation ring_checker := (ring_checker 0 1 +%R *%R +%R id cdiv eq_op).

Lemma sPeval_Pol_of_PExpr l pe : Peval l (Pol_of_PExpr pe) = PEeval l pe.
Proof.
elim: pe l => [//|i|e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2|e IH|e IH k] l /=.
- exact: Peval_mkX.
- by move: e1 IH1 => [c|i|e1' e2'|e1' e2'|e1' e2'|e|e k] IH1;
    move: e2 IH2 => [c'|i'|e1'' e2''|e1'' e2''|e1'' e2''|e'|e' k'] IH2;
    rewrite ?Psub_add ?PevalD ?IH1 ?IH2//;
    do ?[by move: (IH2 l) => /= /[!Popp_id]->];
    move: (IH1 l) => /= /[!Popp_id]->; rewrite addrC.
- by rewrite Psub_add PevalD IH1 IH2.
- by rewrite PevalM IH1 IH2.
- by rewrite Popp_id.
- by rewrite Peval_pow_N IH.
Qed.

Lemma sMeval_mk_monpol_list l lpe :
    all (fun PP => PEeval l PP.1 == PEeval l PP.2) lpe ->
  all (fun MP => cMeval l MP.1 == Peval l MP.2) (mk_monpol_list lpe).
Proof.
elim: lpe => [//| [pe1 pe2] lpe IH] /=/andP[/eqP pe12 a].
have := @Meval_Mon_of_Pol _ _ R_of_C l (norm_subst 0 [::] pe1).
case: Mon_of_Pol; rewrite /= IH// => -[c M] /(_ _ erefl)->.
by rewrite !sPeval_Pol_of_PExpr pe12 andbT.
Qed.

Lemma sPeval_norm_subst n l lpe pe :
    all (fun PP => PEeval l PP.1 == PEeval l PP.2) lpe ->
  Peval l (norm_subst n (mk_monpol_list lpe) pe) = PEeval l pe.
Proof.
move/sMeval_mk_monpol_list/Peval_PNSubstL => <-//.
exact: sPeval_Pol_of_PExpr.
Qed.

Lemma sPEeval_eqs_PEeval l lpe :
  PEeval_eqs l lpe -> all (fun PP => PEeval l PP.1 == PEeval l PP.2) lpe.
Proof.
elim: lpe => [//|[pe1 pe2] lpe IH] /= elpe.
apply/andP; split; first by case: lpe elpe {IH} => [|? ? []]->.
by apply: IH; case: lpe elpe => [//|? ? []].
Qed.

Lemma sCring_checkerT n l lpe pe1 pe2 :
    PEeval_eqs l lpe ->
    ring_checker n lpe pe1 pe2 ->
  PEeval l pe1 = PEeval l pe2.
Proof.
move/sPEeval_eqs_PEeval => elpe /(Peval_Peq R_of_C l).
by rewrite !sPeval_norm_subst.
Qed.

End Csemiring_correct.

Section Cring_correct.
Variables (R C : comPzRingType) (R_of_C : {rmorphism C -> R}).
Variables (cdiv : C -> C -> C * C).
Variables (cdivP : forall x y, let (q, r) := cdiv x y in x = y * q + r).

Implicit Type l : seq R.

#[local] Notation Peval := (Peval
  +%R *%R N.to_nat (@GRing.exp R) R_of_C (@env_jump R) (env_nth 0)).
#[local] Notation cMeval := (cMeval
  1 *%R N.to_nat (@GRing.exp R) R_of_C (@env_jump R) (env_nth 0)).
#[local] Notation PEeval := (PEeval +%R *%R (fun x y : R => x - y) -%R
  N.to_nat (@GRing.exp R) R_of_C (env_nth 0)).
#[local] Notation PEeval_eqs := (PEeval_eqs +%R *%R
  (fun x y : R => x - y) -%R N.to_nat (@GRing.exp R) eq R_of_C (env_nth 0)).
#[local] Notation Peq := (Peq eq_op).
#[local] Notation Pol_of_PExpr := (Pol_of_PExpr
  0 1 +%R *%R (fun x y : C => x - y) -%R eq_op).
#[local] Notation mk_monpol_list := (mk_monpol_list
  0 1 +%R *%R (fun x y : C => x - y) -%R cdiv eq_op).
#[local] Notation norm_subst := (norm_subst
  0 1 +%R *%R (fun x y : C => x - y) -%R cdiv eq_op).
#[local] Notation ring_checker := (ring_checker
  0 1 +%R *%R (fun x y : C => x - y) -%R cdiv eq_op).

Lemma Peval_Pol_of_PExpr l pe : Peval l (Pol_of_PExpr pe) = PEeval l pe.
Proof.
elim: pe l => [//|i|e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2|e IH|e IH k] l /=.
- exact: Peval_mkX.
- by move: e1 IH1 => [c|i|e1' e2'|e1' e2'|e1' e2'|e|e k] IH1;
    move: e2 IH2 => [c'|i'|e1'' e2''|e1'' e2''|e1'' e2''|e'|e' k'] IH2;
    rewrite ?PevalD ?IH1 ?IH2// PevalB ?IH1 -PevalN IH2// addrC -IH1.
- by rewrite PevalB IH1 IH2.
- by rewrite PevalM IH1 IH2.
- by rewrite PevalN IH.
- by rewrite Peval_pow_N IH.
Qed.

Lemma Meval_mk_monpol_list l lpe :
    all (fun PP => PEeval l PP.1 == PEeval l PP.2) lpe ->
  all (fun MP => cMeval l MP.1 == Peval l MP.2) (mk_monpol_list lpe).
Proof.
elim: lpe => [//| [pe1 pe2] lpe IH] /=/andP[/eqP pe12 a].
have := @Meval_Mon_of_Pol _ _ R_of_C l (norm_subst 0 [::] pe1).
case: Mon_of_Pol; rewrite /= IH// => -[c M] /(_ _ erefl)->.
by rewrite !Peval_Pol_of_PExpr pe12 andbT.
Qed.

Lemma Peval_norm_subst n l lpe pe :
    all (fun PP => PEeval l PP.1 == PEeval l PP.2) lpe ->
  Peval l (norm_subst n (mk_monpol_list lpe) pe) = PEeval l pe.
Proof.
by move/Meval_mk_monpol_list/Peval_PNSubstL => <-//; apply: Peval_Pol_of_PExpr.
Qed.

Lemma PEeval_eqs_PEeval l lpe :
  PEeval_eqs l lpe -> all (fun PP => PEeval l PP.1 == PEeval l PP.2) lpe.
Proof.
elim: lpe => [//|[pe1 pe2] lpe IH] /= elpe.
apply/andP; split; first by case: lpe elpe {IH} => [|? ? []]->.
by apply: IH; case: lpe elpe => [//|? ? []].
Qed.

Lemma Cring_checkerT n l lpe pe1 pe2 :
    PEeval_eqs l lpe ->
    ring_checker n lpe pe1 pe2 ->
  PEeval l pe1 = PEeval l pe2.
Proof.
move/PEeval_eqs_PEeval => elpe /(Peval_Peq R_of_C l).
by rewrite !Peval_norm_subst.
Qed.

End Cring_correct.

Lemma Ctriv_divP (C : pzSemiRingType) (x y : C) :
  let (q, r) := triv_div 0 1 eq_op x y in x = y * q + r.
Proof.
by rewrite /triv_div; case: eqP => [->|_]; rewrite ?addr0 ?mulr1 ?mulr0 ?add0r.
Qed.

Arguments list_R {_ _}.

Elpi derive.param2 positive.
Elpi derive.param2 N.
Elpi derive.param2 Z.

Elpi derive.param2 Pos.succ.
Elpi derive.param2 Pos.mask.
Elpi derive.param2 Pos.pred_double.
Elpi derive.param2 Pos.pred.
Elpi derive.param2 Pos.double_mask.
Elpi derive.param2 Pos.double_pred_mask.
Elpi derive.param2 Pos.succ_double_mask.
(* Use derive.param2 when elpi supports mutual fixpoints *)
Definition Pos_add_R :=
  fix add_R (x_1 x_2 : positive) (x_R : positive_R x_1 x_2)
      (y_1 y_2 : positive) (y_R : positive_R y_1 y_2) {struct x_R} :
    positive_R (Pos.add x_1 y_1) (Pos.add x_2 y_2) :=
  match x_R with
  | xI_R p_1 p_2 p_R =>
      match y_R with
      | xI_R q_1 q_2 q_R => xO_R (add_carry_R p_1 p_2 p_R q_1 q_2 q_R)
      | xO_R q_1 q_2 q_R => xI_R (add_R p_1 p_2 p_R q_1 q_2 q_R)
      | xH_R => xO_R (succ_R p_R)
      end
  | xO_R p_1 p_2 p_R =>
      match y_R with
      | xI_R q_1 q_2 q_R => xI_R (add_R p_1 p_2 p_R q_1 q_2 q_R)
      | xO_R q_1 q_2 q_R => xO_R (add_R p_1 p_2 p_R q_1 q_2 q_R)
      | xH_R => xI_R p_R
      end
  | xH_R =>
      match y_R with
      | xI_R q_1 q_2 q_R => xO_R (succ_R q_R)
      | xO_R q_1 q_2 q_R => xI_R q_R
      | xH_R => xO_R xH_R
      end
  end
  with add_carry_R (x_1 x_2 : positive) (x_R : positive_R x_1 x_2)
      (y_1 y_2 : positive) (y_R : positive_R y_1 y_2) {struct x_R} :
    positive_R (Pos.add_carry x_1 y_1) (Pos.add_carry x_2 y_2) :=
  match x_R with
  | xI_R p_1 p_2 p_R =>
      match y_R with
      | xI_R q_1 q_2 q_R => xI_R (add_carry_R p_1 p_2 p_R q_1 q_2 q_R)
      | xO_R q_1 q_2 q_R => xO_R (add_carry_R p_1 p_2 p_R q_1 q_2 q_R)
      | xH_R => xI_R (succ_R p_R)
      end
  | xO_R p_1 p_2 p_R =>
      match y_R with
      | xI_R q_1 q_2 q_R => xO_R (add_carry_R p_1 p_2 p_R q_1 q_2 q_R)
      | xO_R q_1 q_2 q_R => xI_R (add_R p_1 p_2 p_R q_1 q_2 q_R)
      | xH_R => xO_R (succ_R p_R)
      end
  | xH_R =>
      match y_R with
      | xI_R q_1 q_2 q_R => xI_R (succ_R q_R)
      | xO_R q_1 q_2 q_R => xO_R (succ_R q_R)
      | xH_R => xI_R xH_R
      end
  end
  for add_R.
Elpi derive.param2.register Pos.add Pos_add_R.
Definition Pos_sub_mask_R :=
  fix sub_mask_R (x_1 x_2 : positive) (x_R : positive_R x_1 x_2)
    (y_1 y_2 : positive) (y_R : positive_R y_1 y_2) {struct x_R} :
      mask_R (Pos.sub_mask x_1 y_1) (Pos.sub_mask x_2 y_2) :=
  match x_R with
  | xI_R _ _ p_R =>
      match y_R with
      | xI_R _ _ q_R => double_mask_R (sub_mask_R _ _ p_R _ _ q_R)
      | xO_R _ _ q_R => succ_double_mask_R (sub_mask_R _ _ p_R _ _ q_R)
      | xH_R => IsPos_R (xO_R p_R)
      end
  | xO_R _ _ p_R =>
      match y_R with
      | xI_R _ _ q_R => succ_double_mask_R (sub_mask_carry_R _ _ p_R _ _ q_R)
      | xO_R _ _ q_R => double_mask_R (sub_mask_R _ _ p_R _ _ q_R)
      | xH_R => IsPos_R (pred_double_R p_R)
      end
  | xH_R => match y_R with xH_R => IsNul_R | _ => IsNeg_R end
  end
  with sub_mask_carry_R (x_1 x_2 : positive) (x_R : positive_R x_1 x_2)
    (y_1 y_2 : positive) (y_R : positive_R y_1 y_2) {struct x_R} :
      mask_R (Pos.sub_mask_carry x_1 y_1) (Pos.sub_mask_carry x_2 y_2) :=
  match x_R with
  | xI_R _ _ p_R =>
      match y_R with
      | xI_R _ _ q_R => succ_double_mask_R (sub_mask_carry_R _ _ p_R _ _ q_R)
      | xO_R _ _ q_R => double_mask_R (sub_mask_R _ _ p_R _ _ q_R)
      | xH_R => IsPos_R (pred_double_R p_R)
      end
  | xO_R _ _ p_R =>
      match y_R with
      | xI_R _ _ q_R => double_mask_R (sub_mask_carry_R _ _ p_R _ _ q_R)
      | xO_R _ _ q_R =>succ_double_mask_R (sub_mask_carry_R _ _ p_R _ _ q_R)
      | xH_R => double_pred_mask_R p_R
      end
  | xH_R =>
      match y_R with
      | xI_R _ _ _ => IsNeg_R
      | xO_R _ _ _ => IsNeg_R
      | xH_R => IsNeg_R
      end
  end
  for sub_mask_R.
Elpi derive.param2.register Pos.sub_mask Pos_sub_mask_R.
Elpi derive.param2 Pos.sub.
Elpi derive.param2 Pos.compare_cont.
Elpi derive.param2 Pos.compare.

Elpi derive.param2 Z.double.
Elpi derive.param2 Z.succ_double.
#[warning="-elpi.renamed"]
Elpi derive.param2 Z.pred_double.
Elpi derive.param2 Z.pos_sub.

Elpi derive.param2 PExpr.
Elpi derive.param2 Pol.
Elpi derive.param2 Mon.

Elpi derive.param2 Peq.
Elpi derive.param2 P0.
Elpi derive.param2 P1.
Elpi derive.param2 mkPinj.
Elpi derive.param2 mkPinj_pred.
Elpi derive.param2 mkX.
Elpi derive.param2 mkPX.
Elpi derive.param2 Popp.
Elpi derive.param2 PaddC.
Elpi derive.param2 PaddI.
Elpi derive.param2 PaddX.
Elpi derive.param2 Padd.
Elpi derive.param2 PsubC.
Elpi derive.param2 PsubI.
Elpi derive.param2 PsubX.
Elpi derive.param2 Psub.
Elpi derive.param2 PmulC_aux.
Elpi derive.param2 PmulC.
Elpi derive.param2 PmulI.
Elpi derive.param2 Pmul.
Elpi derive.param2 Ppow_pos.
Elpi derive.param2 Ppow_N.

Elpi derive.param2 mkZmon.
Elpi derive.param2 zmon_pred.
Elpi derive.param2 mkVmon.
Elpi derive.param2 Mon_of_Pol.
Elpi derive.param2 CFactor.
Elpi derive.param2 MFactor.
Elpi derive.param2 POneSubst.
Elpi derive.param2 PNSubst1.
Elpi derive.param2 PNSubst.
Elpi derive.param2 PSubstL1.
Elpi derive.param2 PSubstL.
Elpi derive.param2 PNSubstL.

Elpi derive.param2 Pol_of_PExpr.
Elpi derive.param2 norm_subst.
Elpi derive.param2 mk_monpol_list.
Elpi derive.param2 ring_checker.
Elpi derive.param2 triv_div.

(* a bunch of helper lemmas *)

Lemma bool_Rxx b : bool_R b b. Proof. by case: b; constructor. Qed.
Lemma nat_Rxx n : nat_R n n. Proof. by elim: n => [| n IH]; constructor. Qed.
Lemma positive_Rxx p : positive_R p p.
Proof. by elim: p => [p IH | p IH |]; constructor. Qed.
Lemma N_Rxx n : N_R n n.
Proof. by case: n => [| p]; constructor; apply: positive_Rxx. Qed.

Lemma bool_R_eq b b' : bool_R b b' -> b = b'.
Proof. by case: b b' => [] [] []. Qed.
Lemma eq_bool_R b b' : b = b' -> bool_R b b'.
Proof. by move=> ->; apply: bool_Rxx. Qed.

Lemma eq_bool_R2 {A B} {f : A -> B -> bool} {C D} {g : C -> D -> bool}
    {AC : A -> C -> Type} {BD : B -> D -> Type} :
    (forall a c (rac : AC a c) b d (rbd : BD b d), f a b = g c d) ->
  forall a c (rac : AC a c) b d (rbd : BD b d), bool_R (f a b) (g c d).
Proof. by move=> e a1 a2 ra b1 b2 rb; apply/eq_bool_R/e. Qed.

Lemma list_R_map A B (RAB : A -> B -> Type) (f : A -> B) :
  (forall a, RAB a (f a)) -> forall l : seq A, list_R RAB l (map f l).
Proof.
move=> rf; elim=> [| a l IH]; first exact: nil_R.
by apply: cons_R; [apply: rf | apply: IH].
Qed.

Lemma PExpr_R_map A B (RAB : A -> B -> Type) (f : A -> B) :
    (forall a, RAB a (f a)) ->
  forall g : PExpr A, PExpr_R RAB g (PEmap f g).
Proof.
move=> rf; elim=> [c | p |||| g IH | g IH n]; [| |move=> f1 IH1 f2 IH2..| |].
- exact: PEc_R.
- exact/PEX_R/positive_Rxx.
- by apply: PEadd_R; [apply: IH1 | apply: IH2].
- by apply: PEsub_R; [apply: IH1 | apply: IH2].
- by apply: PEmul_R; [apply: IH1 | apply: IH2].
- exact/PEopp_R/IH.
- by apply: PEpow_R; [apply: IH | apply: N_Rxx].
Qed.

(* Refinement of C to N, for actual computation in the reflexive tactic. *)

Definition R_of_N (R : pzSemiRingType) (natr : nat -> R) (n : N) : R :=
  natr (N.to_nat n).
Arguments R_of_N : clear implicits.

Section Nsemiring.
Variables (R : comPzSemiRingType).

#[local] Notation R_of_N := (R_of_N R (GRing.natmul 1)).

Lemma R_of_N_natmul i r : Nnat i r -> R_of_N i = r%:R.
Proof. by rewrite /R_of_N => /eqP->. Qed.

Lemma semiring_checker_map_N_to_nat n lpe pe1 pe2 :
  ring_checker N0 (Npos xH) N.add N.mul N.add id (triv_div N0 (Npos xH) N.eqb)
    N.eqb n lpe pe1 pe2
  = ring_checker 0 1 +%R *%R +%R id (triv_div 0 1 eq_op) eq_op n
      (map (fun pp => (PEmap N.to_nat pp.1, PEmap N.to_nat pp.2)) lpe)
      (PEmap N.to_nat pe1) (PEmap N.to_nat pe2).
Proof.
by apply/bool_R_eq/(ring_checker_R _ _ NnatD NnatM NnatD _
  (triv_div_R _ _ (eq_bool_R2 Nnat_eq)) (eq_bool_R2 Nnat_eq) (nat_Rxx n)) => //;
  [apply: list_R_map => -[{}pe1 {}pe2]; apply: pair_R| |];
  apply/PExpr_R_map/Nnat_N_to_nat.
Qed.

Lemma PEeval_map_N_to_nat l (pe : PExpr N) :
  PEeval +%R *%R +%R id N.to_nat (GRing.exp (R:=R))
    (GRing.natmul 1) (env_nth 0) l (PEmap N.to_nat pe)
  = PEeval +%R *%R +%R id N.to_nat (GRing.exp (R:=R)) R_of_N (env_nth 0) l pe.
Proof.
elim: pe; [|by move=> //= ? -> // ? // ->..].
by move=> c; apply/esym/R_of_N_natmul/Nnat_N_to_nat.
Qed.

Lemma PEeval_eqs_map_N_to_nat l lpe :
    PEeval_eqs +%R *%R +%R id N.to_nat (GRing.exp (R:=R)) eq_op
      R_of_N (env_nth 0) l lpe ->
  PEeval_eqs +%R *%R +%R id N.to_nat (GRing.exp (R:=R)) eq
    (GRing.natmul 1) (env_nth 0) l
    (map (fun pp => (PEmap N.to_nat pp.1, PEmap N.to_nat pp.2)) lpe).
Proof.
elim: lpe => [//|[pe1 pe2] lpe IH] /=; rewrite !PEeval_map_N_to_nat.
by case: lpe IH => [_ /eqP//| [pe1' pe2'] lpe] /= IH [/eqP-> /IH].
Qed.

#[local] Notation PEeval := (PEeval +%R *%R +%R id N.to_nat (@GRing.exp R)
  R_of_N (env_nth 0)).
#[local] Notation PEeval_eqs := (PEeval_eqs +%R *%R +%R id
  N.to_nat (@GRing.exp R) eq_op R_of_N (env_nth 0)).
#[local] Notation ring_checker := (ring_checker
  N0 (Npos xH) N.add N.mul N.add id (triv_div N0 (Npos xH) N.eqb) N.eqb).

Lemma Nsemiring_correct n l lpe pe1 pe2 :
    PEeval_eqs l lpe ->
    ring_checker n lpe pe1 pe2 ->
  PEeval l pe1 = PEeval l pe2.
Proof.
rewrite semiring_checker_map_N_to_nat -!PEeval_map_N_to_nat.
by move/PEeval_eqs_map_N_to_nat; apply/sCring_checkerT/Ctriv_divP.
Qed.

End Nsemiring.

(* Refinement of C to Z, for actual computation in the reflexive tactic. *)
Definition R_of_Z (R : pzRingType) (intr : int -> R) (i : Z) : R :=
  intr (int_of_Z i).
Arguments R_of_Z : clear implicits.

Section Zring.
Variables (R : comPzRingType).

#[local] Notation R_of_Z := (R_of_Z R intr).

Lemma R_of_Z_intr i r : Zint i r -> R_of_Z i = intr r.
Proof. by rewrite /R_of_Z => /eqP->. Qed.

Lemma ring_checker_map_int_of_Z n lpe pe1 pe2 :
  ring_checker Z0 (Zpos xH) Z.add Z.mul Z.sub Z.opp (triv_div Z0 (Zpos xH) Z.eqb)
    Z.eqb n lpe pe1 pe2
  = ring_checker 0 1 +%R *%R (fun x y => x - y) -%R (triv_div 0 1 eq_op) eq_op n
      (map (fun pp => (PEmap int_of_Z pp.1, PEmap int_of_Z pp.2)) lpe)
      (PEmap int_of_Z pe1) (PEmap int_of_Z pe2).
Proof.
by apply/bool_R_eq/(ring_checker_R _ _ ZintD ZintM ZintB ZintN
  (triv_div_R _ _ (eq_bool_R2 Zint_eq)) (eq_bool_R2 Zint_eq) (nat_Rxx n)) => //;
  [apply: list_R_map => -[{}pe1 {}pe2]; apply: pair_R| |];
  apply/PExpr_R_map/Zint_int_of_Z.
Qed.

Lemma PEeval_map_int_of_Z l (pe : PExpr Z) :
  PEeval +%R *%R (fun x y => x - y) -%R N.to_nat (GRing.exp (R:=R))
    intr (env_nth 0) l (PEmap int_of_Z pe)
  = PEeval +%R *%R (fun x y => x - y) -%R N.to_nat (GRing.exp (R:=R))
      R_of_Z (env_nth 0) l pe.
Proof.
elim: pe; [|by move=> //= ? -> // ? // ->..].
by move=> c; apply/esym/R_of_Z_intr/Zint_int_of_Z.
Qed.

Lemma PEeval_eqs_map_int_of_Z l lpe :
    PEeval_eqs +%R *%R (fun x y => x - y) -%R N.to_nat (GRing.exp (R:=R))
      eq_op R_of_Z (env_nth 0) l lpe ->
  PEeval_eqs +%R *%R (fun x y => x - y) -%R N.to_nat (GRing.exp (R:=R))
    eq intr (env_nth 0) l
    (map (fun pp => (PEmap int_of_Z pp.1, PEmap int_of_Z pp.2)) lpe).
Proof.
elim: lpe => [//|[pe1 pe2] lpe IH] /=; rewrite !PEeval_map_int_of_Z.
by case: lpe IH => [_ /eqP//| [pe1' pe2'] lpe] /= IH [/eqP-> /IH].
Qed.

#[local] Notation PEeval := (PEeval +%R *%R (fun x y => x - y) -%R
  N.to_nat (@GRing.exp R) R_of_Z (env_nth 0)).
#[local] Notation PEeval_eqs := (PEeval_eqs +%R *%R (fun x y => x - y) -%R
  N.to_nat (@GRing.exp R) eq_op R_of_Z (env_nth 0)).
#[local] Notation ring_checker := (ring_checker
  Z0 (Zpos xH) Z.add Z.mul Z.sub Z.opp (triv_div Z0 (Zpos xH) Z.eqb) Z.eqb).

Lemma Zring_correct n l lpe pe1 pe2 :
    PEeval_eqs l lpe ->
    ring_checker n lpe pe1 pe2 ->
  PEeval l pe1 = PEeval l pe2.
Proof.
rewrite ring_checker_map_int_of_Z -!PEeval_map_int_of_Z.
by move/PEeval_eqs_map_int_of_Z; apply/Cring_checkerT/Ctriv_divP.
Qed.

End Zring.

(* Everything below is essentially imported form algebra-tactics *)

Implicit Types (V : nmodType) (R : pzSemiRingType) (F : fieldType).

(* Some basic facts about `Decimal.uint` and `Hexadecimal.uint`               *)

Lemma Nat_tail_addE n m : Nat.tail_add n m = (m + n)%N.
Proof. by elim: n m => [| n IH /=] m; rewrite ?addn0// IH addSn addnS. Qed.
Lemma Nat_tail_mulE n m : Nat.tail_mul n m = (m * n)%N.
Proof.
rewrite /Nat.tail_mul -[RHS]add0n.
elim: n 0%N => [| n IH /=] r; first by rewrite muln0 addn0.
by rewrite mulnS addnA -IH Nat_tail_addE.
Qed.

Lemma PosSD p : Pos.succ p = Pos.add 1 p.
Proof. by apply: Pos_to_natI; rewrite !Pos_to_natE add1n. Qed.
Lemma PosDA : associative Pos.add.
Proof. by move=> ? ? ?; apply: Pos_to_natI; rewrite !Pos_to_natE addnA. Qed.
Lemma PosMC : commutative Pos.mul.
Proof. by move=> ? ?; apply: Pos_to_natI; rewrite !Pos_to_natE mulnC. Qed.

Lemma uint_N_nat (d : Decimal.uint) : N.to_nat (N.of_uint d) = Nat.of_uint d.
Proof.
suff acc d' p : Pos.to_nat (Pos.of_uint_acc d' p)
  = Nat.of_uint_acc d' (Pos.to_nat p) by elim: d => //=.
by elim: d' p => //= d' IH p; rewrite Nat_tail_mulE;
  rewrite -[10%N]/(Pos.to_nat 1~0~1~0) -!Pos_to_natE -{}IH ?PosSD?PosDA PosMC.
Qed.

Lemma hex_uint_N_nat (d : Hexadecimal.uint) :
  N.to_nat (N.of_hex_uint d) = Nat.of_hex_uint d.
Proof.
suff acc d' p : Pos.to_nat (Pos.of_hex_uint_acc d' p)
  = Nat.of_hex_uint_acc d' (Pos.to_nat p) by elim: d => //=.
by elim: d' p => //= d' IH p; rewrite Nat_tail_mulE;
  rewrite -[16%N]/(Pos.to_nat 1~0~0~0~0) -!Pos_to_natE -{}IH ?PosSD?PosDA PosMC.
Qed.

Lemma N_to_natS i : N.to_nat (N.succ i) = (N.to_nat i).+1.
Proof. by case: i => [//| p /=]; rewrite Pos_to_natS. Qed.

(* In reified syntax trees, constants must be represented by binary integers  *)
(* `N`. For the fine-grained control of conversion, we provide an immediately *)
(* expanding versions of the `N -> nat` conversion.      `                    *)

Definition addn_expand := Eval compute in addn.

Fixpoint nat_of_pos_rec_expand (p : positive) (a : nat) : nat :=
  match p with
  | p0~1 => addn_expand a (nat_of_pos_rec_expand p0 (addn_expand a a))
  | p0~0 => nat_of_pos_rec_expand p0 (addn_expand a a)
  | 1 => a
  end%positive.

Definition nat_of_pos_expand (p : positive) : nat := nat_of_pos_rec_expand p 1.

Definition nat_of_N_expand (n : N) : nat :=
  if n is Npos p then nat_of_pos_expand p else 0%N.

Lemma nat_of_N_expandE : nat_of_N_expand = N.to_nat. Proof. by []. Qed.

(* For representing input terms of the form `S (... (S n) ...)`               *)

Definition add_pos_nat (p : positive) (n : nat) : nat := Pos.iter S n p.

Lemma add_pos_natE p n : add_pos_nat p n = Pos.to_nat p + n.
Proof.
by elim: p n => //= p IHp n; rewrite !IHp Pos_to_natE -addnn ?[RHS]addSn addrA.
Qed.

(* Data types for reifying `nat` constants, including large ones              *)
(* that use `Number.uint`                                                     *)

Variant large_nat := large_nat_N of N | large_nat_uint of Number.uint.

Definition nat_of_large_nat (n : large_nat) : nat :=
  match n with
  | large_nat_N n => nat_of_N_expand n
  | large_nat_uint n => Nat.of_num_uint n
  end.

Definition N_of_large_nat (n : large_nat) : N :=
  match n with
  | large_nat_N n => n
  | large_nat_uint n => N.of_num_uint n
  end.

Lemma large_nat_N_nat (n : large_nat) :
  N.to_nat (N_of_large_nat n) = nat_of_large_nat n.
Proof.
case: n => [n|[d|d]] /=; first by rewrite nat_of_N_expandE.
  by rewrite uint_N_nat.
by rewrite hex_uint_N_nat.
Qed.

(* Type for reified expressions *)
Inductive RExpr : pzSemiRingType -> Type :=
  (* 0 *)
  | R0 R : RExpr R
  (* addition: x + y and (n + m)%N *)
  | RAdd R : RExpr R -> RExpr R -> RExpr R
  | RnatAdd : RExpr nat -> RExpr nat -> RExpr nat
  (* natmul: x *+ n, including n%:R = 1 *+ n *)
  | RMuln R : RExpr R -> RExpr nat -> RExpr R
  (* opposite *)
  | ROpp (R : pzRingType) : RExpr R -> RExpr R
  (* intmul: x *~ z, including z%:~R = 1 *~ z *)
  | RMulz (R : pzRingType) : RExpr R -> RExpr int -> RExpr R
  (* 1 *)
  | R1 R : RExpr R
  (* multiplication: x * y and (x * y)%N *)
  | RMul R : RExpr R -> RExpr R -> RExpr R
  | RnatMul : RExpr nat -> RExpr nat -> RExpr nat
  (* exponentiation *)
  | RExpn R : RExpr R -> large_nat -> RExpr R (* x ^+ n *)
  | RExpPosz (R : unitRingType) : RExpr R -> large_nat -> RExpr R (* x ^ Posz n *)
  | RExpNegz F : RExpr F -> large_nat -> RExpr F (* x ^ Negz n *)
  | RnatExpn : RExpr nat -> large_nat -> RExpr nat (* expn n m *)
  (* multiplicative inverse: x^-1 *)
  | RInv F : RExpr F -> RExpr F
  (* constants *)
  | RnatS : positive -> RExpr nat -> RExpr nat (* S (S ... (S n)...)*)
  | RnatC : large_nat -> RExpr nat (* n *)
  | RPosz : RExpr nat -> RExpr int (* Posz n *)
  | RNegz : RExpr nat -> RExpr int (* Negz n *)
  (* homomorphism applications *)
  | RMorph R' R : {rmorphism R' -> R} -> RExpr R' -> RExpr R
  | RnatMorph R : {rmorphism nat -> R} -> RExpr nat -> RExpr R
  | RintMorph R : {rmorphism int -> R} -> RExpr int -> RExpr R
  | RAdditive V R : {additive V -> R} -> MExpr V -> RExpr R
  | RnatAdditive R : {additive nat -> R} -> RExpr nat -> RExpr R
  | RintAdditive R : {additive int -> R} -> RExpr int -> RExpr R
  (* variables *)
  | RX R : R -> RExpr R
with MExpr : nmodType -> Type :=
  | M0 V : MExpr V (* 0 *)
  | MAdd V : MExpr V -> MExpr V -> MExpr V (* x + y *)
  | MMuln V : MExpr V -> RExpr nat -> MExpr V (* x *+ n *)
  | MOpp (V : zmodType) : MExpr V -> MExpr V (* - x *)
  | MMulz (V : zmodType) : MExpr V -> RExpr int -> MExpr V (* x *~ z *)
  | MAdditive V' V : {additive V' -> V} -> MExpr V' -> MExpr V
  | MnatAdditive V : {additive nat -> V} -> RExpr nat -> MExpr V
  | MintAdditive V : {additive int -> V} -> RExpr int -> MExpr V
  | MX V : V -> MExpr V.

Scheme RExpr_ind' := Induction for RExpr Sort Prop
  with MExpr_ind' := Induction for MExpr Sort Prop.

(* Evaluation function for above type                                         *)
(* Evaluating result of reification should be convertible to input expr.      *)
Fixpoint Reval R (e : RExpr R) : R :=
  match e with
  | R0 _ => 0
  | RAdd _ e1 e2 => Reval e1 + Reval e2
  | RnatAdd e1 e2 => addn (Reval e1) (Reval e2)
  | RMuln _ e1 e2 => Reval e1 *+ Reval e2
  | ROpp _ e1 => - Reval e1
  | RMulz _ e1 e2 => Reval e1 *~ Reval e2
  | R1 _ => 1
  | RMul _ e1 e2 => Reval e1 * Reval e2
  | RnatMul e1 e2 => muln (Reval e1) (Reval e2)
  | RExpn _ e1 n => Reval e1 ^+ nat_of_large_nat n
  | RExpPosz _ e1 n => Reval e1 ^ Posz (nat_of_large_nat n)
  | RExpNegz _ e1 n => Reval e1 ^ Negz (nat_of_large_nat n)
  | RnatExpn e1 n => expn (Reval e1) (nat_of_large_nat n)
  | RInv _ e1 => (Reval e1)^-1
  | RnatS p e => add_pos_nat p (Reval e)
  | RnatC n => nat_of_large_nat n
  | RPosz e1 => Posz (Reval e1)
  | RNegz e2 => Negz (Reval e2)
  | RMorph _ _ f e1
  | RnatMorph _ f e1
  | RintMorph _ f e1
  | RnatAdditive _ f e1
  | RintAdditive _ f e1 => f (Reval e1)
  | RAdditive _ _ f e1 => f (Meval e1)
  | RX _ x => x
  end
with Meval V (e : MExpr V) : V :=
  match e with
  | M0 _ => 0
  | MAdd _ e1 e2 => Meval e1 + Meval e2
  | MMuln _ e1 e2 => Meval e1 *+ Reval e2
  | MOpp _ e1 => - Meval e1
  | MMulz _ e1 e2 => Meval e1 *~ Reval e2
  | MAdditive _ _ f e1 => f (Meval e1)
  | MnatAdditive _ f e1
  | MintAdditive _ f e1 => f (Reval e1)
  | MX _ x => x
  end.

Section Reval_eqs.
Variables (C : Type) (R : pzSemiRingType).
Fixpoint Reval_eqs (lpe : list ((RExpr R * RExpr R) * (PExpr C * PExpr C))) :
    Prop :=
  if lpe isn't ((lhs, rhs), _) :: lpe then True
  else Reval lhs = Reval rhs /\ Reval_eqs lpe.
End Reval_eqs.

(* Pushing down morphisms in ring/field expressions by reflection *)
Section norm.
Variables (F : pzSemiRingType) (F_of_N : bool -> N -> F).
Variables (zero : F) (add : F -> F -> F).
Variables (opp_intr : option ((F -> F) * (int -> F))) (one : F).
Variables (mul : F -> F -> F) (exp : F -> N -> F).
Variable (inv : option (F -> F)).

Variable (push_inv : bool).  (* when true, push inv inward,
                                down to constants or variables *)

(* i means "currently pushing an inv" *)
Fixpoint Rnorm (i : bool) R (f : R -> F) (e : RExpr R) : F :=
  let popp v := if opp_intr is Some (opp, _) then opp v
    else f (Reval e) in (* should never happen *)
  let wintr v := if opp_intr is Some (_, intr) then v intr
    else f (Reval e) in (* should never happen *)
  let pinv v := if inv isn't Some i then f (Reval e) (* should never happen *)
    else if push_inv then v else i v in
  let inv_id := if inv is Some i then i else id in
  let noinv v :=
    if push_inv && i then inv_id (f (Reval e))  (* inv will be in a variable *)
    else v (* no inv to put, go on *) in
  let invi v := if push_inv && i then inv_id v else v in
  match e in RExpr R return (R -> F) -> F with
  | R0 _ => fun=> zero
  | RAdd _ e1 e2 | RnatAdd e1 e2 => fun f =>
      noinv (add (Rnorm i f e1) (Rnorm i f e2))
  | RMuln _ e1 e2 => fun f => mul (Rnorm i f e1) (Rnorm i (GRing.natmul 1) e2)
  | ROpp _ e1 => fun f => popp (Rnorm i f e1)
  | RMulz _ e1 e2 => fun f =>
      wintr (fun intr => mul (Rnorm i f e1) (Rnorm i intr e2))
  | R1 _ => fun=> one
  | RMul _ e1 e2 | RnatMul e1 e2  => fun f => mul (Rnorm i f e1) (Rnorm i f e2)
  | RExpn _ e1 n | RnatExpn e1 n => fun f =>
      exp (Rnorm i f e1) (N_of_large_nat n)
  | RExpPosz _ e1 n => fun f => exp (Rnorm i f e1) (N_of_large_nat n)
  | RExpNegz _ e1 n => fun f =>
      pinv (exp (Rnorm (~~ i) f e1) (N.succ (N_of_large_nat n)))
  | RInv _ e1 => fun f => pinv (Rnorm (~~ i) f e1)
  | RnatS p e => fun f => noinv (add (F_of_N false (Npos p)) (Rnorm i f e))
  | RnatC n => fun=> F_of_N (push_inv && i) (N_of_large_nat n)
  | RPosz e1 => fun=> Rnorm i (GRing.natmul 1) e1
  | RNegz e1 => fun=> noinv (popp (add one (Rnorm i (GRing.natmul 1) e1)))
  | RMorph _ _ g e1 => fun f => Rnorm i (fun x => f (g x)) e1
  | RnatMorph _ _ e1 => fun=> Rnorm i (GRing.natmul 1) e1
  | RintMorph _ _ e1 => fun=> wintr (fun intr => Rnorm i intr e1)
  | RAdditive _ _ g e1 => fun f => Mnorm i (fun x => f (g x)) e1
  | RnatAdditive _ g e1 => fun f =>
      mul (invi (f (g 1%N))) (Rnorm i (GRing.natmul 1) e1)
  | RintAdditive _ g e1 => fun f =>
      wintr (fun intr => mul (invi (f (g 1%Z))) (Rnorm i intr e1))
  | RX _ x => fun f => invi (f x)
  end f
with Mnorm i V (f : V -> F) (e : MExpr V) : F :=
  let popp v := if opp_intr is Some (opp, _) then opp v
    else f (Meval e) in (* should never happen *)
  let wintr v := if opp_intr is Some (_, intr) then v intr
    else f (Meval e) in (* should never happen *)
  let inv_id := if inv is Some i then i else id in
  let noinv v :=
    if push_inv && i then inv_id (f (Meval e))  (* inv will be in a variable *)
    else v (* no inv to put, go on *) in
  let invi v := if push_inv && i then inv_id v else v in
  match e in MExpr V return (V -> F) -> F with
  | M0 _ => fun=> zero
  | MAdd _ e1 e2 => fun f => noinv (add (Mnorm i f e1) (Mnorm i f e2))
  | MMuln _ e1 e2 => fun f => mul (Mnorm i f e1) (Rnorm i (GRing.natmul 1) e2)
  | MOpp _ e1 => fun f => popp (Mnorm i f e1)
  | MMulz _ e1 e2 => fun f =>
      wintr (fun intr => mul (Mnorm i f e1) (Rnorm i intr e2))
  | MAdditive _ _ g e1 => fun f => Mnorm i (fun x => f (g x)) e1
  | MnatAdditive _ g e1 => fun f =>
      wintr (fun intr => mul (invi (f (g 1%N))) (Rnorm i (GRing.natmul 1) e1))
  | MintAdditive _ g e1 => fun f =>
      wintr (fun intr => mul (invi (f (g 1%Z))) (Rnorm i intr e1))
  | MX _ x => fun f => invi (f x)
  end f.

Lemma eq_Rnorm i R (f f' : R -> F) (e : RExpr R) :
  f =1 f' -> Rnorm i f e = Rnorm i f' e.
Proof.
pose P R e :=
  forall i (f f' : R -> F), f =1 f' -> Rnorm i f e = Rnorm i f' e.
pose P0 V e :=
  forall i (f f' : V -> F), f =1 f' -> Mnorm i f e = Mnorm i f' e.
move: i f f'; elim e using (@RExpr_ind' P P0); rewrite {R e}/P {}/P0 //=.
- by move=> R e1 IHe1 e2 IHe2 i f f' feq; rewrite -(IHe1 _ f) -?(IHe2 _ f) ?feq.
- by move=> e1 IHe1 e2 IHe2 i f f' feq; rewrite -(IHe1 _ f) -?(IHe2 _ f) ?feq.
- by move=> R e1 IHe1 e2 _ i f f' /IHe1->.
- by move=> R e1 IHe1 i f f' feq; rewrite -(IHe1 _ f) ?feq.
- by move=> R ei IHe1 e2 _ i f f' feq; rewrite -(IHe1 _ f) ?feq.
- by move=> R e1 IHe1 e2 IHe2 i f f' feq; rewrite -(IHe1 _ f) -?(IHe2 _ f).
- by move=> e1 IHe1 e2 IHe2 i f f' feq; rewrite -(IHe1 _ f) -?(IHe2 _ f).
- by move=> R e1 IHe1 n i f f' /IHe1->.
- by move=> R e1 IHe1 n i f f' /IHe1->.
- by move=> R e1 IHe1 n i f f' feq; rewrite -(IHe1 _ f) ?feq.
- by move=> e1 IHe1 n i f f' /IHe1->.
- by move=> R e1 IHe1 i f f' feq; rewrite -(IHe1 _ f) ?feq.
- by move=> P e1 IHe1 i f f' feq; rewrite -(IHe1 _ f) ?feq.
- by move=> e1 IHe1 i f f' ->.
- by move=> V R g e1 IHe1 i f f' feq; apply: IHe1 => x; apply: feq.
- by move=> R g e1 _ i f f' ->.
- by move=> V R g e1 IHe1 i f f' feq; apply: IHe1 => x; apply: feq.
- by move=> R g e1 _ i f f' ->.
- by move=> R g e1 _ i f f' /[dup]-> feq; case: opp_intr.
- by move=> R x i f f' ->.
- by move=> V e1 IHe1 e2 IHe2 i f f' feq; rewrite -(IHe1 _ f) -?(IHe2 _ f) ?feq.
- by move=> V e1 IHe1 e2 _ i f f' /IHe1->.
- by move=> V e1 IHe1 i f f' feq; rewrite -(IHe1 _ f) ?feq.
- by move=> V e1 IHe1 e2 _ i f f' feq; rewrite -(IHe1 _ f) ?feq.
- by move=> U V g e1 IHe1 i f f' feq; apply: IHe1 => x; apply: feq.
- by move=> V g e1 _ i f f' feq; rewrite !feq.
- by move=> V g e1 _ i f f' feq; rewrite !feq.
- by move=> V x i f f' ->.
Qed.
End norm.

Lemma Rnorm_eq_F_of_N (F : pzSemiRingType) (f f' : bool -> N -> F) (ff' : f =2 f')
  zero add opp_intr one mul exp inv pi i :
  forall (R : pzSemiRingType) (env : R -> F) e,
    Rnorm f zero add opp_intr one mul exp inv pi i env e =
    Rnorm f' zero add opp_intr one mul exp inv pi i env e.
Proof.
move=> R m e.
pose P R e := forall f f' pi i (m : R -> F), f =2 f' ->
  Rnorm f zero add opp_intr one mul exp inv pi i m e =
  Rnorm f' zero add opp_intr one mul exp inv pi i m e.
pose P0 V e := forall f f' pi i (m : V -> F), f =2 f' ->
  Mnorm f zero add opp_intr one mul exp inv pi i m e =
  Mnorm f' zero add opp_intr one mul exp inv pi i m e.
move: f f' pi i m ff'.
elim e using (@RExpr_ind' P P0); rewrite {R e}/P {}/P0 /=.
- by [].
- by move=> R e1 IHe1 e2 IHe2 f f' pi i m ff'; rewrite -(IHe1 f) -?(IHe2 f).
- by move=> e1 IHe1 e2 IHe2 f f' pi i m ff'; rewrite -(IHe1 f) -?(IHe2 f).
- by move=> R e1 IHe1 e2 IHe2 f f' pi i m ff'; rewrite -(IHe1 f) -?(IHe2 f).
- by move=> R e1 IHe1 f f' pi i m /IHe1->.
- move=> R e1 + e2 + f f' pi i m ff'; case: opp_intr => // -[opp intr] IH1 IH2.
  by rewrite -(IH1 f) -?(IH2 f).
- by [].
- by move=> R e1 IHe1 e2 IHe2 f f' pi i m ff'; rewrite -(IHe1 f) -?(IHe2 f).
- by move=> e1 IHe1 e2 IHe2 f f' pi i m ff'; rewrite -(IHe1 f) -?(IHe2 f).
- by move=> R e1 IHe1 n f f' pi i m /IHe1->.
- by move=> R e1 IHe1 n f f' pi i m /IHe1->.
- by move=> R e1 IHe1 n f f' pi i m /IHe1->.
- by move=> e1 IHe1 n f f' pi i m /IHe1->.
- by move=> R e1 IHe1 f f' pi i m /IHe1->.
- by move=> p e IHe f f' pi i m ff'; rewrite -(IHe f) ?ff'.
- by move=> n f f' pi i m ff'; rewrite /Rnorm ff'.
- by move=> e IHe f f' pi i m ff'; exact: IHe.
- by move=> e IHe f f' pi i m /IHe->.
- by move=> R' R g e IHe f f' pi i m ff'; exact: IHe.
- by move=> R g e IHe f f' pi i m ff'; exact: IHe.
- by move=> R g e + f f' pi i m ff'; case: opp_intr => // -[opp intr]; apply.
- by move=> V R g e IHe f f' pi i m ff'; exact: IHe.
- by move=> R g e IHe f f' pi i m ff'; congr mul; exact: IHe.
- move=> R g e + f f' pi i m ff'; case: opp_intr => // -[opp intr] IH.
  by congr mul; apply: IH.
- by [].
- by [].
- by move=> V e1 IHe1 e2 IHe2 f f' pi i m ff'; rewrite -(IHe1 f) -?(IHe2 f).
- by move=> V e1 IHe1 e2 IHe2 f f' pi i m ff'; rewrite -(IHe1 f) -?(IHe2 f).
- by move=> V e IHe f f' pi i m /IHe->.
- move=> V e1 + e2 + f f' pi i m ff'; case: opp_intr => // -[opp intr] IHe1 IHe2.
  by rewrite -(IHe1 f) -?(IHe2 f).
- by move=> V V' g e IHe f f' pi i m ff'; exact: IHe.
- move=> V g e + f f' pi i m ff'; case: opp_intr => // -[opp intr] IH.
  by congr mul; apply: IH.
- move=> V g e + f f' pi i m ff'; case: opp_intr => // -[opp intr] IH.
  by congr mul; apply: IH.
- by [].
Qed.

Variant field_or_ring :=
  | Field of fieldType | Ring of pzRingType | SemiRing of pzSemiRingType.
Coercion semiring_of_field_or_ring (RF : field_or_ring) : pzSemiRingType :=
  match RF with Field R => R | Ring R => R | SemiRing R => R end.
Definition ring_opp_intr (R : field_or_ring) : option ((R -> R) * (int -> R)) :=
  match R with Field R' | Ring R' => Some (@GRing.opp R', intr) | _ => None end.
Definition field_inv (R : field_or_ring) : option (R -> R) :=
  if R is Field F then Some (@GRing.inv F) else None.
Definition inv_id {R : field_or_ring} := if field_inv R is Some i then i else id.
Definition invi {R : field_or_ring} i (r : R) := if i then inv_id r else r.

Section correct.
Variables (F : field_or_ring).

#[local] Notation F_of_N := (fun b n => invi b (N.to_nat n)%:R).
#[local] Notation expN := (fun x n => x ^+ N.to_nat n).
#[local] Notation Rnorm := (Rnorm F_of_N 0 +%R (ring_opp_intr F) 1 *%R expN
  (field_inv F)).
#[local] Notation Mnorm := (Mnorm F_of_N 0 +%R (ring_opp_intr F) 1 *%R expN
  (field_inv F)).

Lemma Rnorm_correct pi (e : RExpr F) :
    pi = (if F is SemiRing _ then false else true) && pi ->
  Reval e = Rnorm pi false id e.
Proof.
move=> piF.
suff: forall (i : bool) R (f : {rmorphism R -> F}) (e' : RExpr R),
    invi (pi && i) (f (Reval e')) = Rnorm pi i f e'.
  by move/(_ false _ idfun e); rewrite andbF.
move=> i R f {}e.
have invi0 b : invi b 0 = 0 :> F.
  by rewrite /invi /inv_id /field_inv; case: b F => -[]// F' /[!invr0].
have inviM b r1 r2 : invi b (r1 * r2) = invi b r1 * invi b r2 :> F.
  rewrite /invi /inv_id /field_inv.
  by case: b F r1 r2 => -[]// F' r1 r2 /[!invfM].
have inviXn b r n : invi b (r ^+ n) = (invi b r) ^+ n :> F.
  by rewrite /invi /inv_id; case: b F r => -[]// F' r /[!exprVn].
pose P R e := forall i (f : {rmorphism R -> F}),
  invi (pi && i) (f (Reval e)) = Rnorm pi i f e.
pose P0 V e := forall i (f : {additive V -> F}),
  invi (pi && i) (f (Meval e)) = Mnorm pi i f e.
move: i f; elim e using (@RExpr_ind' P P0); rewrite {R e}/P {}/P0 //=.
- by move=> R i f; rewrite rmorph0.
- by move=> R e1 IHe1 e2 IHe2 i f; rewrite rmorphD -IHe1 -IHe2; case: (pi && i).
- by move=> e1 IHe1 e2 IHe2 i f; rewrite rmorphD -IHe1 -IHe2; case: (pi && i).
- by move=> R e1 IHe1 e2 IHe2 i f; rewrite rmorphMn -mulr_natr inviM IHe1 IHe2.
- by move=> R e1 + i; case: F piF => F' -> IHe1 f //=;
    rewrite rmorphN /invi /inv_id/= ?invrN -fun_if [X in - X]IHe1.
- by move=> R e1 + e2 + i; case: F piF inviM => F' -> //= inviM IHe1 IHe2 f;
    rewrite rmorphMz -mulrzr inviM IHe1 IHe2.
- move=> R i f.
  by rewrite /invi/inv_id/field_inv rmorph1; case: andb F => -[]// F' /[!invr1].
- by move=> R e1 IHe1 e2 IHe2 i f; rewrite rmorphM inviM IHe1 IHe2.
- by move=> e1 IHe1 e2 IHe2 i f; rewrite rmorphM inviM IHe1 IHe2.
- by move=> R e1 IHe1 n i f; rewrite rmorphXn inviXn IHe1 large_nat_N_nat.
- by move=> R e1 IHe1 n i f; rewrite rmorphXn inviXn IHe1 large_nat_N_nat.
- move=> R e1 + n i f; rewrite -large_nat_N_nat N_to_natS NegzE -exprnN.
  rewrite /invi /inv_id/=; case: F piF f => F' -> //= f; [|by case: andb].
  by move=> <-; rewrite fmorphV rmorphXn invrK; case: pi i => -[]// /[!exprVn].
- by move=> e1 IHe1 n i f; rewrite rmorphXn inviXn IHe1 large_nat_N_nat.
- move=> R e1 + i f.
  rewrite /invi /inv_id/=; case: F piF f => F' -> //= f; [|by case: andb].
  by move=> <-; rewrite fmorphV invrK; case: pi i => -[].
- move=> p e1 IHe1 i f; rewrite add_pos_natE rmorphD; set p' := Pos.to_nat p.
  by rewrite  -[p' in f p']natn rmorph_nat -IHe1; case: (pi && i).
- by move=> ???; rewrite -[nat_of_large_nat _]natn rmorph_nat -large_nat_N_nat.
- by move=> e1 IHe1 i f; rewrite -[X in Posz X]natn !rmorph_nat IHe1.
- by move=> e1 + i; case: F piF => F' -> //= IHe1 f;
    rewrite -[Negz _]intz rmorph_int /intmul mulrS -IHe1; case: (pi && i).
- by move=> R S g e1 IHe1 i f; rewrite -/(comp f g _) IHe1.
- move=> R g e1 IHe1 i f; rewrite -/(comp f g _) IHe1.
  by apply: eq_Rnorm => /= n; rewrite -[RHS](rmorph_nat (f \o g)) natn.
- move=> R g e1 + i; case: F piF => F' -> //= IH f;rewrite -/(comp f g _) IH/=;
    apply: eq_Rnorm => /= n; rewrite -[RHS](rmorph_int (f \o g));
    by congr (f (g _)); rewrite intz.
- by move=> V R g e1 IHe1 i f; rewrite -/(comp f g _) IHe1.
- move=> R g e1 IHe1 i f.
  by rewrite -[Reval e1]natn !raddfMn -mulr_natr inviM IHe1.
- by move=> R g e1 + i; case: F piF inviM => F' -> //= inviM IHe1 f;
    rewrite -[Reval e1]intz ![f _](raddfMz (f \o g)) -mulrzr inviM IHe1.
- by move=> V i f; rewrite raddf0 invi0.
- by move=> V e1 IHe1 e2 IHe2 i f; rewrite raddfD -IHe1 -IHe2; case: (pi && i).
- by move=> V e1 IHe1 e2 IHe2 i f; rewrite raddfMn -mulr_natr inviM IHe1 IHe2.
- by move=> V e1 + i; case: F piF => F' -> //= + f => <-; rewrite raddfN;
    case: andb => //=; rewrite /inv_id/= invrN.
- by move=> V e1 + e2 + i; case: F piF inviM => F' -> //= iM + + f => <- IHe2;
    rewrite raddfMz -mulrzr iM IHe2.
- by move=> V V' g e1 IHe1 i f; rewrite -/(comp f g _) IHe1.
- move=> V g e1 IH i f; rewrite -[Reval e1]natn !raddfMn -mulr_natr inviM IH.
  by case: F piF f IH => F' -> //= f /(_ i)->/=.
- by move=> V g e1 + i; case: F piF inviM => F' -> //= inviM IH f;
    rewrite -[Reval e1]intz ![f _](raddfMz (f \o g)) -mulrzr inviM IH.
Qed.
End correct.

Lemma semiring_correct (R : comPzSemiRingType) n env
    (lpe : seq ((RExpr R * RExpr R) * (PExpr N * PExpr N)))
    (re1 re2 : RExpr R) (pe1 pe2 : PExpr N) :
    Reval_eqs lpe ->
    (forall R_of_N add mul exp natr,
       let R_of_N := R_of_N (natr : nat -> R) in
       let norm := Rnorm (fun=> R_of_N) (R_of_N N0) add None (R_of_N (Npos xH))
         mul (fun x n => exp x (N.to_nat n)) None false false id in
       let eval := PEeval add mul add id N.to_nat exp
         R_of_N (env_nth (R_of_N N0)) env in
       let l := ((re1, re2), (pe1, pe2)) :: lpe in
       map (fun pp => (norm pp.1.1, norm pp.1.2)) l
       = map (fun pp => (eval pp.2.1, eval pp.2.2)) l) ->
    ring_checker N0 (Npos xH) N.add N.mul N.add id
      (triv_div N0 (Npos xH) N.eqb) N.eqb n (map snd lpe) pe1 pe2 ->
  Reval re1 = Reval re2.
Proof.
have R_of_NE : (fun=> R_of_N R (GRing.natmul 1))
  =2 fun b n => @invi (SemiRing R) b (N.to_nat n)%:R by case=> [] [].
rewrite !(@Rnorm_correct (SemiRing R) false _ erefl).
rewrite -!(Rnorm_eq_F_of_N R_of_NE) => elpe.
move=> /(_ (R_of_N R) +%R *%R (@GRing.exp R) (GRing.natmul 1))[-> ->]/= nelpe.
apply: Nsemiring_correct => //.
elim: lpe elpe nelpe => [//|[[{}re1 {}re2] [{}pe1 {}pe2]] lpe IH] /=.
move=> -[re12 relpe] [rp1 rp2 rple]; have := IH relpe rple.
rewrite -rp1 -rp2 !(Rnorm_eq_F_of_N R_of_NE).
rewrite -!(@Rnorm_correct (SemiRing R) false _ erefl) re12.
by case: lpe {IH relpe rple} => /=.
Qed.

Lemma ring_correct (R : comPzRingType) n env
    (lpe : seq ((RExpr R * RExpr R) * (PExpr Z * PExpr Z)))
    (re1 re2 : RExpr R) (pe1 pe2 : PExpr Z) :
    Reval_eqs lpe ->
    (forall R_of_Z add opp mul exp intr,
       let R_of_Z := R_of_Z intr in let R_of_N _ n := R_of_Z (Z.of_N n) in
       let opp_intr := Some (opp, intr) in
       let norm := Rnorm R_of_N (R_of_Z Z0) add opp_intr (R_of_Z (Zpos xH))
         mul (fun x n => exp x (N.to_nat n)) None false false id in
       let eval := PEeval add mul (fun x y => add x (opp y)) opp N.to_nat exp
         R_of_Z (env_nth (R_of_Z Z0)) env in
       let l := ((re1, re2), (pe1, pe2)) :: lpe in
       map (fun pp => (norm pp.1.1, norm pp.1.2)) l
       = map (fun pp => (eval pp.2.1, eval pp.2.2)) l) ->
    ring_checker Z0 (Zpos xH) Z.add Z.mul Z.sub Z.opp
      (triv_div Z0 (Zpos xH) Z.eqb) Z.eqb n (map snd lpe) pe1 pe2 ->
  Reval re1 = Reval re2.
Proof.
pose R_of_N (b : bool) n : Ring R := R_of_Z R intr (Z.of_N n).
have R_of_NE : R_of_N =2 fun b n => @invi (Ring R) b (N.to_nat n)%:R.
  by case=> [] [].
rewrite !(@Rnorm_correct (Ring R) false _ erefl).
rewrite -!(Rnorm_eq_F_of_N R_of_NE) => elpe.
move=> /( _ (R_of_Z R) +%R -%R *%R (@GRing.exp R) intr)[-> ->]/= nelpe.
apply: Zring_correct => //.
elim: lpe elpe nelpe => [//|[[{}re1 {}re2] [{}pe1 {}pe2]] lpe IH] /=.
move=> -[re12 relpe] [rp1 rp2 rple]; have := IH relpe rple.
rewrite -rp1 -rp2 !(Rnorm_eq_F_of_N R_of_NE).
rewrite -!(@Rnorm_correct (Ring R) false _ erefl) re12.
by case: lpe {IH relpe rple} => /=.
Qed.

End Internals.

(* Main tactics, called from the elpi parser (c.f., ring.elpi) *)

Ltac ring_reflection Lem R VarMap Lpe RE1 RE2 PE1 PE2 LpeProofs :=
  exact (Lem R 100%N VarMap Lpe RE1 RE2 PE1 PE2 LpeProofs
             ltac:(reflexivity) ltac:(vm_compute; reflexivity)).

Strategy expand [addn_expand nat_of_pos_rec_expand nat_of_pos_expand].
Strategy expand [nat_of_N_expand nat_of_large_nat N_of_large_nat].
Strategy expand [Reval Meval Rnorm Mnorm PEeval].

Elpi Db mc.canonicals.db lp:{{
pred canonical-nat-nmodule o:constant.
pred canonical-nat-semiring o:constant.
pred canonical-nat-comsemiring o:constant.
pred canonical-int-nmodule o:constant.
pred canonical-int-zmodule o:constant.
pred canonical-int-semiring o:constant.
pred canonical-int-ring o:constant.
pred canonical-int-comring o:constant.
pred canonical-int-unitring o:constant.
pred coercion o:string o:term.
}}.

Elpi Tactic mcring.
Elpi Accumulate Db mc.canonicals.db.
#[warning="-elpi.flex-clause"]
Elpi Accumulate File ring ring_tac.

Tactic Notation "ring" := elpi mcring.
Tactic Notation "ring" ":" ne_constr_list(L) := elpi mcring ltac_term_list:(L).
Tactic Notation "#[" attributes(A) "]" "ring" := ltac_attributes:(A) elpi mcring.
Tactic Notation "#[" attributes(A) "]" "ring" ":" ne_constr_list(L) :=
  ltac_attributes:(A) elpi mcring ltac_term_list:(L).

Elpi Query lp:{{ canonical-init library "mc.canonicals.db" }}.
Elpi Query lp:{{ coercion-init library "mc.canonicals.db" }}.

(* Remove the line below when requiring rocq-elpi > 3.1.0
c.f., https://github.com/LPCIC/coq-elpi/pull/866 *)
#[global] Unset Uniform Inductive Parameters.

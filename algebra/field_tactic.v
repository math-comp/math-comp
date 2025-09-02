(* Distributed under the terms of CeCILL-B.                                  *)
(* This file is largely based on the ring.v file from                        *)
(* https://github.com/math-comp/algebra-tactics                              *)
From elpi Require Import derive.std param2.
From micromega_plugin Require Import NatDef.
From Corelib Require Import IntDef.
From micromega_plugin Require Import formula witness checker eval.
From micromega_plugin Require Import field_checker field_eval.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq order.
From mathcomp Require Export ssralg.
From mathcomp Require Import ssrnum ssrint binnums ring_tactic.
From mathcomp.algebra Extra Dependency "ring_tactic.elpi" as ring_tactic.
From mathcomp.algebra Extra Dependency "field_tactic.elpi" as field_tactic.

(******************************************************************************)
(* This file provides the field tactics.                                      *)
(*                                                                            *)
(* These tactics provide:                                                     *)
(*        field == a tactic for field equalities, uses the tactic             *)
(*                 `field_tactic` (`done` by default) to discharge subgoals   *)
(*                 stating non nullity of denominators                        *)
(*  field: e1 ... en == same as field, assuming ring equalities e1,..., en    *)
(*       field? == nonterminating variant of field that let the user handle   *)
(*                 the subgoals. This is intended for development purpose only*)
(*                 and shouldn't remain in final proof scripts.               *)
(* These tactics work on any comPzSemiRingType (resp fieldType) and handle    *)
(* additive morphisms {additive _ -> _} and ring morphisms {rmorphism _ -> _}.*)
(*                                                                            *)
(* See file test-suite/test_field.v for examples.                             *)
(*                                                                            *)
(*  * Field tactic                                                            *)
(*                                                                            *)
(* The `field` tactic solves a goal of the form `p = q :> F` representing a   *)
(* rational equation. The type `F` must have a canonical `fieldType` (field)  *)
(* instance. The `field` tactic solves the equation by normalizing each side  *)
(* to a pair of two polynomials representing a fraction, whose coefficients   *)
(* are integers.                                                              *)
(* As is the case for the `ring` tactic, the `field` tactic can decide the    *)
(* given rational equation modulo given monomial equations. The syntax to use *)
(* this feature is the same as the `ring` tactic: `field: t_1 .. t_n`.        *)
(*                                                                            *)
(* The `field` tactic generates proof obligations that all the denominators   *)
(* in the equation are not zero. A proof obligation of the form               *)
(* `p * q != 0 :> F` is always automatically reduced to `p != 0` and `q != 0`.*)
(* If the field `F` is a `numFieldType` (partially ordered field), a proof    *)
(* obligation of the form `c%:~R != 0 :> F` where `c` is a non-zero integer   *)
(* constant is automatically resolved. Remaining proof obligations are then   *)
(* solved with the `field_tactic` tactic (`done` by default, user overridable *)
(* with `Ltac field_tactic ::= ...`). During development process, the `field?`*)
(* tactic can be used to inspect these proof obligations.                     *)
(*                                                                            *)
(*  * Preprocessing additive and ring morphisms                               *)
(*                                                                            *)
(* See ring_tactic.v corresponding header section, with following additions:  *)
(* - `GRing.inv` (`_^-1`),                                                    *)
(* - `exprz`,[^constant_exponent] can be negative                             *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

Module Import Internals.
Export Internals.

Section PCond.
Variables (R : Type) (rO rI : R) (radd rmul rsub : R -> R -> R) (ropp : R -> R).
Variables (Cpow : Type) (Cpow_of_N : N -> Cpow) (rpow : R -> Cpow -> R).
Variables (req : R -> R -> bool).
Variables (C : Type) (R_of_C : C -> R).

#[local] Notation PEeval := (PEeval rO rI radd rmul rsub ropp Cpow_of_N rpow
  R_of_C (env_nth rO)).
#[local] Notation PCond := (PCond true negb andb rO rI radd rmul rsub ropp
  Cpow_of_N rpow req R_of_C (env_nth rO)).

Lemma PCond_cons l c1 c2 :
  PCond l (c1 :: c2) = ~~ (req (PEeval l c1) rO) && PCond l c2.
Proof. by case: c2 => [|//]; rewrite andbT. Qed.

Lemma PCond_app l c1 c2 : PCond l (app c1 c2) = PCond l c1 && PCond l c2.
Proof. by elim: c1 c2 => [//|c c1 IH] c2; rewrite !PCond_cons IH andbA. Qed.

End PCond.

Section FieldCorrect.
Variables (R : fieldType) (C : comPzRingType) (R_of_C : {rmorphism C -> R}).
Variables (cdiv : C -> C -> C * C).
Variables (cdivP : forall x y, let (q, r) := cdiv x y in x = y * q + r).

Implicit Type l : seq R.

#[local] Notation Peval := (Peval
  +%R *%R N.to_nat (@GRing.exp R) R_of_C (@env_jump R) (env_nth 0)).
#[local] Notation sub := (fun x y => x - y).
#[local] Notation PEeval := (PEeval 0 1 +%R *%R sub -%R N.to_nat (@GRing.exp R)
  R_of_C (env_nth 0)).
#[local] Notation PEeval_eqs := (PEeval_eqs true andb 0 1 +%R *%R sub -%R
  N.to_nat (@GRing.exp R) eq_op R_of_C (env_nth 0)).
#[local] Notation FEeval := (FEeval 0 1 +%R *%R sub -%R (fun x y => x / y)
  (fun x => x^-1) N.to_nat (@GRing.exp R) R_of_C (env_nth 0)).
#[local] Notation PCond := (PCond true negb andb 0 1 +%R *%R sub -%R
  N.to_nat (@GRing.exp R) eq_op R_of_C (env_nth 0)).
#[local] Notation NPEadd := (NPEadd 0 +%R eq_op).
#[local] Notation NPEsub := (NPEsub 0 sub eq_op).
#[local] Notation NPEopp := (NPEopp -%R).
#[local] Notation pow_pos := (fun x n => x ^+ Pos.to_nat n).
#[local] Notation NPEpow := (NPEpow 0 1 pow_pos eq_op).
#[local] Notation NPEmul := (NPEmul 0 1 *%R pow_pos eq_op).
#[local] Notation PExpr_eq := (PExpr_eq eq_op).
#[local] Notation default_isIn := (default_isIn 0 1 pow_pos eq_op).
#[local] Notation isIn := (isIn 0 1 *%R pow_pos eq_op).
#[local] Notation split_aux := (split_aux 0 1 *%R pow_pos eq_op).
#[local] Notation split := (split 0 1 *%R pow_pos eq_op).
#[local] Notation Fnorm := (Fnorm 0 1 +%R *%R sub -%R pow_pos eq_op).
#[local] Notation field_checker := (field_checker 0 1 +%R *%R sub -%R pow_pos
  eq_op cdiv).
#[local] Notation Fcons0 := (Fcons0 0 1 +%R *%R sub -%R eq_op).
#[local] Notation Fcons00 := (Fcons00 0 1 +%R *%R sub -%R eq_op).
#[local] Notation Fcons1 := (Fcons1 0 1 +%R *%R sub -%R eq_op).
#[local] Notation Fcons2 := (Fcons2 0 1 +%R *%R sub -%R pow_pos eq_op).

Lemma PEeval_NPEadd l e1 e2 : PEeval l (NPEadd e1 e2) = PEeval l (PEadd e1 e2).
Proof.
by case: e1 => [||c|i|e1 e1'|e1 e1'|e1 e1'|e1|e1 n];
  case: e2 => [||c'|i'|e2 e2'|e2 e2'|e2 e2'|e2|e2 n']; do ?[reflexivity] => /=;
  do ?[by case: eqP => [->|//]; rewrite rmorph0 (addr0, add0r)];
  rewrite rmorphD.
Qed.

Lemma PEeval_NPEsub l e1 e2 : PEeval l (NPEsub e1 e2) = PEeval l (PEsub e1 e2).
Proof.
by case: e1 => [||c|i|e1 e1'|e1 e1'|e1 e1'|e1|e1 n];
  case: e2 => [||c'|i'|e2 e2'|e2 e2'|e2 e2'|e2|e2 n']; do ?[reflexivity] => /=;
  do ?[by case: eqP => [->|//]; rewrite rmorph0 (subr0, add0r)//= ?oppr0];
  rewrite rmorphB.
Qed.

Lemma PEeval_NPEopp l e : PEeval l (NPEopp e) = PEeval l (PEopp e).
Proof. by case: e => [||c|i|e e'|e e'|e e'|e|e n]//=; rewrite rmorphN. Qed.

Lemma PEeval_NPEpow l e n : PEeval l (NPEpow e n) = PEeval l (PEpow e n).
Proof.
case: n => [| p]; rewrite /NPEpow; first by rewrite /= ?rmorph1 ?expr0.
case: Pos.eqb (pos_nat_eq (pos_nat_Pos_to_nat p) pos_nat1) => [|_].
  by move/esym/eqP; rewrite -[1%N]/(Pos.to_nat xH) => /Pos_to_natI->.
case: e => //= c; case: eqP => [->|_]; rewrite /= ?rmorph1 ?expr1n//.
by case: eqP => [->|_]; rewrite /= ?rmorph0 ?expr0n ?Pos_to_nat0F//= rmorphXn.
Qed.

Lemma PEeval_NPEmul l e1 e2 : PEeval l (NPEmul e1 e2) = PEeval l (PEmul e1 e2).
Proof.
elim: e1 e2 => [||c|i|e1 IH e1' IH'|e1 IH e1' IH'|e1 IH e1' IH'|e1 IH|e1 IH n];
  case=> [||c'|i'|e2 e2'|e2 e2'|e2 e2'|e2|e2 n']; do ?[reflexivity] => /=;
  do ?[by case: eqP => [->|_]; rewrite ?rmorph1 ?mul1r?mulr1; do ?[reflexivity];
       case: eqP => [->|_]; rewrite ?rmorph0 /= ?mul0r ?mulr0 ?mul1r ?mulr1].
- by rewrite rmorphM.
- case: N.eqb (Nnat_eq (Nnat_N_to_nat n) (Nnat_N_to_nat n')) => [|//].
  by move/esym/eqP/N_to_natI->; rewrite PEeval_NPEpow/= IH exprMn.
Qed.

Lemma PExpr_eqP (e1 e2 : PExpr C) : reflect (e1 = e2) (PExpr_eq e1 e2).
Proof.
apply/(iffP idP) => [|<-]; last first.
  elim: e1 => /=[//|//|//|p|?->?->//|?->?->//|?->?->//|//|e1 IH n].
  - by rewrite (pos_nat_eq (pos_nat_Pos_to_nat p) (pos_nat_Pos_to_nat p)).
  - by rewrite (Nnat_eq (Nnat_N_to_nat n) (Nnat_N_to_nat n)) eqxx IH.
elim: e1 e2 => [||c1|i1|e1 IH e1' IH'|e1 IH e1' IH'|e1 IH e1' IH'|e IH|e IH n];
  case=> [||c2|i2|e2 e2'|e2 e2'|e2 e2'|e2|e2 n']//=;
  do ?[by move=> /andP[/IH-> /IH'->]].
- by move/eqP->.
- case: Pos.eqb (pos_nat_eq(pos_nat_Pos_to_nat i1)(pos_nat_Pos_to_nat i2)) =>//.
  by move/esym/eqP/Pos_to_natI->.
- by move/IH->.
- move=> /andP[+ /IH->].
  by rewrite (Nnat_eq (Nnat_N_to_nat n) (Nnat_N_to_nat n')) => /eqP/N_to_natI->.
Qed.

Lemma PEeval_default_isIn l e1 p1 e2 p2 n e3 :
    default_isIn e1 p1 e2 p2 = Some (n, e3) ->
  ((Pos.to_nat p1 > N.to_nat n)%N
   /\ PEeval l (PEpow e2 (Npos p2))
      = PEeval l (PEmul (PEpow e1 (N.sub (Npos p1) n)) e3)).
Proof.
rewrite /default_isIn; case: PExpr_eqP => [->|//].
case: Z.pos_sub (Zint_pos_sub (pos_nat_Pos_to_nat p1) (pos_nat_Pos_to_nat p2)).
- rewrite /Zint eq_sym subr_eq0 => /eqP[/Pos_to_natI<-] [<- <-]/=.
  by rewrite Pos_to_nat_gt0 rmorph1 mulr1.
- move=> p pp1p2.
  have p1p2 : (Pos.to_nat p2 < Pos.to_nat p1)%N.
    by rewrite -ltz_nat -subr_gt0 -(eqP pp1p2) ltz_nat Pos_to_nat_gt0.
  have -> : p = Pos.sub p1 p2.
    apply/Pos_to_natI/eqP; rewrite -eqz_nat [eqbLHS](eqP pp1p2).
    by rewrite Pos_to_natB// subzn// ltnW.
  move=> -[<- <-]/=; rewrite /= Pos_to_natB// ltn_subrL !Pos_to_nat_gt0.
  rewrite rmorph1 mulr1 (N_to_natB (Npos p1) (Npos (Pos.sub p1 p2)))/=.
  by rewrite Pos_to_natB ?subKn// ltnW.
- move=> p pp1p2 [<- <-]/=; rewrite Pos_to_nat_gt0; split=> [//|].
  rewrite (PEeval_NPEpow l e2 (Npos p))/= -exprD; congr (_ ^+ _).
  apply/eqP; rewrite -eqz_nat PoszD; apply/eqP/(subIr (Pos.to_nat p1 : int)).
  apply/oppr_inj; rewrite !opprB opprD addrA subrr add0r.
  by rewrite -(eqP pp1p2)/= NegzE prednK ?Pos_to_nat_gt0.
Qed.

Lemma PEeval_isIn l e1 p1 e2 p2 n e3 :
    isIn e1 p1 e2 p2 = Some (n, e3) ->
  ((Pos.to_nat p1 > N.to_nat n)%N
   /\ PEeval l (PEpow e2 (Npos p2))
      = PEeval l (PEmul (PEpow e1 (N.sub (Npos p1) n)) e3)).
Proof.
(elim: e2 p1 p2 n e3 => [||?|?|????|????|e3 IH e4 IH'|??|e2 IH n'] p1 p2 n e5'';
    do ?[exact: PEeval_default_isIn]; last first)=> /=.
  case: n' => [//|p3].
  case: isIn (IH p1 (Pos.mul p3 p2)) => [[n' e5'''] /(_ _ _ erefl)/[swap]|//].
  by move=> [{n'}-> {e5'''}->] [np1 e]; rewrite -exprM/= -Pos_to_natM.
case: isIn (IH p1 p2) => [[n'' e5] /(_ _ _ erefl)/[swap]|_]; last first.
  case: isIn (IH' p1 p2) => [[n' e5] /(_ _ _ erefl)/[swap]|//].
  move=> [{n'}-> {e5''}<-] [np1 e].
  rewrite (PEeval_NPEmul l (NPEpow e3 (Npos p2)) e5)/=.
  rewrite (PEeval_NPEpow l e3 (Npos p2)).
  by rewrite exprMn [X in _ * X = _]e [RHS]mulrCA.
case: n'' => [[{n}<- {e5''}<-] [np1 e]|p]/=.
  rewrite (PEeval_NPEmul l e5 (NPEpow e4 (Npos p2)))/=.
  rewrite (PEeval_NPEpow l e4 (Npos p2)).
  by rewrite exprMn [X in X * _ = _]e mulrA.
case: isIn (IH' p p2) => [[n' e6] /(_ _ _ erefl)/[swap]|_].
  move=> [{n'}-> {e5''}<-] [np1 ee4] [pp1 ee3]; split; [exact: ltn_trans pp1|].
  rewrite (PEeval_NPEmul l e5 e6) exprMn ee3 [X in _ * X]ee4/= [LHS]mulrACA.
  rewrite -exprD (N_to_natB (Npos p1) (Npos p)) (N_to_natB (Npos p) n).
  by rewrite (N_to_natB (Npos p1) n) addnBA ?subnK// ltnW.
move=> [{n}<- {e5''}<-] [pp1 e].
rewrite (PEeval_NPEmul l e5 (NPEpow e4 (Npos p2)))/=.
by rewrite (PEeval_NPEpow l e4 (Npos p2)) exprMn e mulrA.
Qed.

Lemma PEeval_split_aux l e1 p e2 :
  PEeval l (PEpow e1 (Npos p))
  = PEeval l (PEmul (rsplit_left (split_aux e1 p e2))
                (rsplit_common (split_aux e1 p e2)))
  /\ PEeval l e2
     = PEeval l (PEmul (rsplit_right (split_aux e1 p e2))
                   (rsplit_common (split_aux e1 p e2))).
Proof.
have main_case e1' p' e2' :
    let res :=
      match isIn e1' p' e2' xH with
      | Some (N0, e3) => mk_rsplit (PEc 1) (NPEpow e1' (Npos p')) e3
      | Some (Npos q, e3) =>
          mk_rsplit (NPEpow e1' (Npos q)) (NPEpow e1' (Npos (Pos.sub p' q))) e3
      | None => mk_rsplit (NPEpow e1' (Npos p')) (PEc 1) e2'
      end in
    PEeval l (PEpow e1' (Npos p'))
    = PEeval l (PEmul (rsplit_left res) (rsplit_common res))
    /\ PEeval l e2'
       = PEeval l (PEmul (rsplit_right res) (rsplit_common res)).
  case: isIn (@PEeval_isIn l e1' p' e2' xH) => [[n''' e3] /(_ _ _ erefl)|_/=].
  - case: n''' => /=[[_ ee2']|q [qp' /[!expr1] ee2']].
      by rewrite rmorph1 mul1r (PEeval_NPEpow l e1' (Npos p')) mulrC.
    rewrite (PEeval_NPEpow l e1' (Npos q)).
    rewrite (PEeval_NPEpow l e1' (Npos (Pos.sub p' q)))/= -exprD ee2' mulrC.
    by rewrite Pos_to_natB ?subnKC// 1?ltnW// (N_to_natB (Npos p') (Npos q)).
  - by rewrite (PEeval_NPEpow l e1' (Npos p')) rmorph1 !mulr1.
elim: e1 p e2 => [||?|?|????|????|e3 IH e4 IH'|??|e3 IH n'] p e2;
    do ?[exact: main_case] => /=.
  set r1 := split_aux e3 p e2; set r2 := split_aux e4 p (rsplit_right r1).
  have [ee3 ee2] := IH p e2; have [ee4 er1] := IH' p (rsplit_right r1).
  rewrite (PEeval_NPEmul l (rsplit_left r1) (rsplit_left r2)).
  rewrite (PEeval_NPEmul l (rsplit_common r1) (rsplit_common r2)).
  rewrite exprMn [X in X * _]ee3 [X in _ *X]ee4 ee2 -/r1/= er1 -/r2/=.
  by rewrite mulrACA [X in _ /\ _ = _ * X]mulrC !mulrA.
case: n' => [|p3]; first by rewrite /= rmorph1 expr0 expr1n !mulr1.
by have [ee3 ee2] := IH (Pos.mul p3 p) e2; rewrite -exprM/= -Pos_to_natM.
Qed.

Lemma PEeval_split_l l e1 e2 :
  PEeval l e1
  = PEeval l (PEmul (rsplit_left (split e1 e2)) (rsplit_common (split e1 e2))).
Proof. by case: (PEeval_split_aux l e1 xH e2) => /=/[!expr1]. Qed.

Lemma PEeval_split_r l e1 e2 :
  PEeval l e2
  = PEeval l (PEmul (rsplit_right (split e1 e2)) (rsplit_common (split e1 e2))).
Proof. by case: (PEeval_split_aux l e1 xH e2). Qed.

Lemma split_neq0_l l e1 e2 :
  PEeval l e1 != 0 -> PEeval l (rsplit_left (split e1 e2)) != 0.
Proof.
by apply: contraNN; rewrite (PEeval_split_l l e1 e2)/= mulf_eq0 => ->.
Qed.

Lemma split_neq0_r l e1 e2 :
  PEeval l e2 != 0 -> PEeval l (rsplit_right (split e1 e2)) != 0.
Proof.
by apply: contraNN; rewrite (PEeval_split_r l e1 e2)/= mulf_eq0 => ->.
Qed.

Lemma PCond_Fnorm l e :
  PCond l (condition (Fnorm e)) -> PEeval l (denum (Fnorm e)) != 0.
Proof.
elim: e => [||c|i|e IH e' IH'|e IH e' IH'|e IH e' IH'|//|e IH|e IH e' IH'
    |e IH n]/=; do ?[by rewrite rmorph1 oner_neq0];
    rewrite ?PEeval_NPEmul/= ?PCond_cons ?PCond_app.
- move=> /andP[/IH en0 /IH' e'n0].
  by rewrite PEeval_NPEmul -PEeval_split_r mulf_neq0// split_neq0_l.
- move=> /andP[/IH en0 /IH' e'n0].
  by rewrite PEeval_NPEmul -PEeval_split_r mulf_neq0// split_neq0_l.
- by move=> /andP[/IH en0 /IH' e'n0]; rewrite mulf_neq0// split_neq0_r.
- by move=> /andP[].
- move=> /andP[ne'n0 /andP[/IH den0 /IH' de'n0]].
  by rewrite mulf_neq0// ?split_neq0_l ?split_neq0_r.
- by move=> /IH ene0; rewrite PEeval_NPEpow/= expf_neq0.
Qed.

Lemma addf_div_common (F : fieldType) (c x1 y1 x2 y2 : F) :
    y1 * c != 0 -> y2 * c != 0 ->
  x1 / (y1 * c) + x2 / (y2 * c) = (x1 * y2 + x2 * y1) / (y1 * c * y2).
Proof.
move=> y1c y2c; rewrite addf_div// !mulrA -mulrDl -mulf_div divff ?mulr1//.
by apply: contraNN y1c; rewrite mulf_eq0 => ->; rewrite orbT.
Qed.

Lemma mulf_div_common (F : fieldType) (c1 c2 x1 y1 x2 y2 : F) :
    y1 * c1 != 0 -> y2 * c2 != 0 ->
  (x1 * c2) / (y1 * c1) * ((x2 * c1) / (y2 * c2)) = (x1 * x2) / (y1 * y2).
Proof.
move=> y1c1 y2c2; rewrite mulf_div mulrACA [X in _ / X]mulrACA.
rewrite -[LHS]mulf_div [c2 * c1]mulrC divff ?mulr1// mulf_neq0//.
  by apply: contraNN y1c1; rewrite mulf_eq0 => ->; rewrite orbT.
by apply: contraNN y2c2; rewrite mulf_eq0 => ->; rewrite orbT.
Qed.

Lemma PEeval_Fnorm l e : PCond l (condition (Fnorm e)) ->
  FEeval l e = PEeval l (num (Fnorm e)) / PEeval l (denum (Fnorm e)).
Proof.
elim: e => [||c|i|e IH e' IH'|e IH e' IH'|e IH e' IH'|e IH|e IH|e IH e' IH'
    |e IH n]/=; rewrite ?PCond_cons ?PCond_app.
- by rewrite rmorph0 mul0r.
- by rewrite rmorph1 invr1 mulr1.
- by rewrite rmorph1 invr1 mulr1.
- by rewrite rmorph1 invr1 mulr1.
- move=> /andP[ce ce']; rewrite IH// IH'//.
  rewrite PEeval_NPEadd/= !PEeval_NPEmul/= PEeval_NPEmul/=.
  rewrite -[X in _ = _ / (_ * X)]mulrC mulrA -addf_div_common
    -?[eqbLHS]PEeval_split_l -?[eqbLHS]PEeval_split_r ?PCond_Fnorm//.
  rewrite -[X in _ = _ / X + _]PEeval_split_l.
  by rewrite -[X in _ = _ + _ / X]PEeval_split_r.
- move=> /andP[ce ce']; rewrite IH// IH'//.
  rewrite PEeval_NPEsub/= !PEeval_NPEmul/= PEeval_NPEmul/= -!mulNr.
  rewrite -[X in _ = _ / (_ * X)]mulrC mulrA -addf_div_common
    -?[eqbLHS](PEeval_split_l, PEeval_split_r) ?PCond_Fnorm//.
  rewrite -[X in _ = _ / X + _]PEeval_split_l.
  by rewrite -[X in _ = _ + _ / X]PEeval_split_r.
- move=> /andP[ce ce']; rewrite IH// IH'//.
  rewrite PEeval_NPEmul/= PEeval_NPEmul/=.
  rewrite (PEeval_split_l l (num (Fnorm e)) (denum (Fnorm e'))).
  rewrite (PEeval_split_r l (num (Fnorm e)) (denum (Fnorm e'))).
  rewrite (PEeval_split_l l (num (Fnorm e')) (denum (Fnorm e))).
  rewrite (PEeval_split_r l (num (Fnorm e')) (denum (Fnorm e)))/=.
  by rewrite mulf_div_common
     -?[eqbLHS](PEeval_split_l, PEeval_split_r) ?PCond_Fnorm//.
- by move=> ce; rewrite IH// PEeval_NPEopp/= mulNr.
- by move=> /andP[nen0 ce]; rewrite IH// invf_div.
- move=> /andP[ne'n0 /andP[ce ce']]; rewrite IH// IH'//.
  rewrite PEeval_NPEmul/= PEeval_NPEmul/=.
  rewrite (PEeval_split_l l (num (Fnorm e)) (num (Fnorm e'))).
  rewrite (PEeval_split_r l (num (Fnorm e)) (num (Fnorm e'))).
  rewrite (PEeval_split_l l (denum (Fnorm e)) (denum (Fnorm e'))).
  rewrite (PEeval_split_r l (denum (Fnorm e)) (denum (Fnorm e')))/=.
  by rewrite [X in _ * X = _]invf_div mulf_div_common
    -?[eqbLHS](PEeval_split_l, PEeval_split_r) ?PCond_Fnorm//.
- by move=> ce; rewrite IH// !PEeval_NPEpow/= expr_div_n.
Qed.

Lemma Cfield_checkerT
    cond_norm (cond_normP : forall l el, PCond l (cond_norm el) -> PCond l el)
    n l lpe fe1 fe2 lc :
    PEeval_eqs l lpe ->
    field_checker cond_norm n lpe fe1 fe2 = Some lc ->
    PCond l lc ->
  FEeval l fe1 = FEeval l fe2.
Proof.
rewrite /field_checker; set pe1 := PEmul _ _; set pe2 := PEmul _ _.
move/(Cring_checkerT cdivP) => /(_ n pe1 pe2); rewrite /ring_checker.
case: Peq => [/(_ erefl) epe12 [{lc}<-] /cond_normP/[!PCond_app]/andP[P P']|//].
by apply/eqP; rewrite !PEeval_Fnorm// eqr_div ?PCond_Fnorm//; apply/eqP.
Qed.

Lemma PCond_Fcons0 l a el :
  PCond l (Fcons0 a el) -> PEeval l a != 0 /\ PCond l el.
Proof.
elim: el => [//|e el IH] /=; set pa := _ a; set pe := _ e.
case: Peq (@Peval_Peq _ _ R_of_C l pa pe) => [/(_ erefl)|_].
  by rewrite !Peval_Pol_of_PExpr PCond_cons => -> /andP[-> ->].
by rewrite !PCond_cons => /andP[-> /IH[->]].
Qed.

Lemma PCond_Fcons00 l a el :
  PCond l (Fcons00 a el) -> PEeval l a != 0 /\ PCond l el.
Proof.
elim: a el => [||c|i|a IH a' IH'|a IH a' IH'|a IH a' IH'|a IH| a IH n] el /=;
    do ?[by move/PCond_Fcons0].
- by move=> /IH[an0 /IH'[a'n0 ->]]; rewrite mulf_neq0.
- by move=> /IH[an0 ->]; rewrite expf_neq0.
Qed.

Lemma PCond_Fapp Fcons l el el' :
    (forall l e el, PCond l (Fcons e el) -> PEeval l e != 0 /\ PCond l el) ->
  PCond l (Fapp Fcons el el') -> PCond l el /\ PCond l el'.
Proof.
move=> FcondP; elim: el el' => [//|e el IH] el' /=.
by rewrite PCond_cons => /FcondP[-> /IH[-> ->]].
Qed.

Lemma PCond_cond_norm Fcons l el :
    (forall l e el, PCond l (Fcons e el) -> PEeval l e != 0 /\ PCond l el) ->
  PCond l (cond_norm Fcons el) -> PCond l el.
Proof. by move=> /PCond_Fapp /[apply] -[]. Qed.

End FieldCorrect.

Section NumFieldCorrect.
Variables (R : numFieldType) (C : numDomainType) (R_of_C : {rmorphism C -> R}).
Hypothesis R_of_C_ge0 : {mono R_of_C : x / 0 <= x}.

Implicit Type l : seq R.

#[local] Notation sub := (fun x y => x - y).
#[local] Notation PEeval := (PEeval 0 1 +%R *%R sub -%R N.to_nat (@GRing.exp R)
  R_of_C (env_nth 0)).
#[local] Notation PCond := (PCond true negb andb 0 1 +%R *%R sub -%R
  N.to_nat (@GRing.exp R) eq_op R_of_C (env_nth 0)).
#[local] Notation pow_pos := (fun x n => x ^+ Pos.to_nat n).
#[local] Notation Fcons1 := (Fcons1 0 1 +%R *%R sub -%R eq_op).
#[local] Notation PEsimp := (PEsimp 0 1 +%R *%R sub -%R pow_pos eq_op).
#[local] Notation Fcons2 := (Fcons2 0 1 +%R *%R sub -%R pow_pos eq_op).

Lemma PCond_Fcons1 l a el :
  PCond l (Fcons1 a el) -> PEeval l a != 0 /\ PCond l el.
Proof.
elim: a el => [||c|i|a IH a' IH'|a IH a' IH'|a IH a' IH'|a IH| a IH n] el /=;
    do ?[by move/PCond_Fcons0].
- case: eqP => [->|/eqP]; rewrite /= ?rmorph0 ?eqxx// => c0 ->; split=> [|//].
  by apply: contraNN c0; rewrite !eq_le -oppr_ge0 -rmorphN !R_of_C_ge0 oppr_ge0.
- by move=> /IH[an0 /IH'[a'n0 ->]]; rewrite mulf_neq0.
- by case: ifP; rewrite !oppr_eq0 oner_eq0// => _ /IH.
- by move=> /IH[an0 ->]; rewrite expf_neq0.
Qed.

Lemma PEeval_PEsimp l e : PEeval l (PEsimp e) = PEeval l e.
Proof.
elim: e => [||c|i|a IH a' IH'|a IH a' IH'|a IH a' IH'|a IH| a IH n] //=.
- by rewrite PEeval_NPEadd/= IH IH'.
- by rewrite PEeval_NPEsub/= IH IH'.
- by rewrite PEeval_NPEmul/= IH IH'.
- by rewrite PEeval_NPEopp/= IH.
- by rewrite PEeval_NPEpow/= IH.
Qed.

Lemma PCond_Fcons2 l a el :
  PCond l (Fcons2 a el) -> PEeval l a != 0 /\ PCond l el.
Proof. by move=> /PCond_Fcons1; rewrite PEeval_PEsimp. Qed.

End NumFieldCorrect.

Elpi derive.param2 app.

Elpi derive.param2 Pos.mul.
Elpi derive.param2 Pos.eqb.

#[warning="-elpi.renamed"]
Elpi derive.param2 N.eqb.

Elpi derive.param2 FExpr.
Elpi derive.param2 rsplit.
Elpi derive.param2 rsplit_left.
Elpi derive.param2 rsplit_right.
Elpi derive.param2 rsplit_common.
Elpi derive.param2 field_checker.linear.
Elpi derive.param2 num.
Elpi derive.param2 denum.
Elpi derive.param2 condition.

Elpi derive.param2 PExpr_eq.
Elpi derive.param2 NPEadd.
Elpi derive.param2 NPEsub.
Elpi derive.param2 NPEopp.
Elpi derive.param2 NPEpow.
Elpi derive.param2 NPEmul.
Elpi derive.param2 default_isIn.
Elpi derive.param2 isIn.
Elpi derive.param2 split_aux.
Elpi derive.param2 split.
Elpi derive.param2 Fnorm.
Elpi derive.param2 field_checker.
Elpi derive.param2 Fcons0.
Elpi derive.param2 Fcons00.
Elpi derive.param2 absurd_PCond.
Elpi derive.param2 Fcons1.
Elpi derive.param2 PEsimp.
Elpi derive.param2 Fcons2.
Elpi derive.param2 Fapp.
Elpi derive.param2 cond_norm.

(* a bunch of helper lemmas *)

Lemma option_R_eq T (s s' : option T) : option_R eq s s' -> s = s'.
Proof. by case=> // ? ? ->. Qed.
Lemma PExpr_R_eq T (e e' : PExpr T) : PExpr_R eq e e' -> e = e'.
Proof.
by elim=> [||??->|??/positive_R_eq->|?? _-> ?? _->|?? _-> ?? _->|?? _-> ?? _->
  |?? _->|?? _-> ??/N_R_eq->]//.
Qed.

Lemma option_R_omap2 A B (RAB : A -> B -> Type) C D (RCD : C -> D -> Type)
    (f : A -> C) (g : B -> D) : (forall a b, RAB a b -> RCD (f a) (g b)) ->
  forall a b, option_R RAB a b -> option_R RCD (omap f a) (omap g b).
Proof. by move=> fg _ _ [a b ab|]; constructor; apply: fg. Qed.

Lemma list_R_map2 A B (RAB : A -> B -> Type) C D (RCD : C -> D -> Type)
    (f : A -> C) (g : B -> D) : (forall a b, RAB a b -> RCD (f a) (g b)) ->
  forall x y, list_R RAB x y -> list_R RCD (map f x) (map g y).
Proof.
by move=> fg ? ?; elim=> [|? ? ? ? ? ? IH]; constructor; [apply: fg|apply: IH].
Qed.

Lemma PExpr_R_PEmap2 A B (RAB : A -> B -> Type) C D (RCD : C -> D -> Type)
    (f : A -> C) (g : B -> D) : (forall a b, RAB a b -> RCD (f a) (g b)) ->
  forall x y, PExpr_R RAB x y -> PExpr_R RCD (PEmap f x) (PEmap g y).
Proof.
move=> fg ? ?; elim=> [||a b ab|a b ab||||a b ab|a b ab IH na nb nab];
  [| | | |move=> a1 b1 ab1 IH1 a2 b2 ab2 IH2..| |]; constructor=> //; exact: fg.
Qed.

Lemma FExpr_R_map A B (RAB : A -> B -> Type) (f : A -> B) :
    (forall a, RAB a (f a)) ->
  forall g : FExpr A, FExpr_R RAB g (FEmap f g).
Proof.
move=> rf; elim=> [||c|p||||g IH|g IH|f1 IH1 f2 IH2|g IH n];
    [| | | |move=> f1 IH1 f2 IH2..| | | |].
- exact: FEO_R.
- exact: FEI_R.
- exact: FEc_R.
- exact/FEX_R/positive_Rxx.
- by apply: FEadd_R; [apply: IH1 | apply: IH2].
- by apply: FEsub_R; [apply: IH1 | apply: IH2].
- by apply: FEmul_R; [apply: IH1 | apply: IH2].
- exact/FEopp_R/IH.
- exact/FEinv_R/IH.
- by apply: FEdiv_R; [apply: IH1 | apply: IH2].
- by apply: FEpow_R; [apply: IH | apply: N_Rxx].
Qed.

Lemma PEmap_id T (e : PExpr T) : PEmap id e = e.
Proof. by elim: e => /=[||||?->?->|?->?->|?->?->|?->|?->]. Qed.

Section Zfield.
Variables (R : fieldType).

#[local] Notation R_of_Z := (R_of_Z R).

Lemma Zint_pow_pos_pos i n (Zin : Zint i n) p p' (pp' : positive_R p p') :
  Zint (Z.pow_pos i p) (n ^+ Pos.to_nat p').
Proof. by apply: Zint_pow_pos => //; rewrite (positive_R_eq pp'). Qed.

Lemma field_checker_map_int_of_Z Zcn icn
    (cnR : forall (Zc : seq (PExpr Z)) (ic : seq (PExpr int)),
        list_R (PExpr_R Zint) Zc ic -> list_R (PExpr_R Zint) (Zcn Zc) (icn ic))
    n lpe fe1 fe2 :
  omap (map (PEmap int_of_Z))
    (field_checker Z0 (Zpos xH) Z.add Z.mul Z.sub Z.opp Z.pow_pos
       Z.eqb (triv_div Z0 (Zpos xH) Z.eqb) Zcn n lpe fe1 fe2)
  = field_checker 0 1 +%R *%R (fun x y => x - y) -%R
      (fun x p => x ^+ Pos.to_nat p) eq_op (triv_div 0 1 eq_op) icn n
      (map (fun pp => (PEmap int_of_Z pp.1, PEmap int_of_Z pp.2)) lpe)
      (FEmap int_of_Z fe1) (FEmap int_of_Z fe2).
Proof.
set fc1 := _ fe1 fe2; set fc2 := _ (FEmap _ fe1) (FEmap _ fe2).
have fc12 : option_R (list_R (PExpr_R Zint)) fc1 fc2.
  apply: (field_checker_R _ _ ZintD ZintM ZintB ZintN Zint_pow_pos_pos
    (eq_bool_R2 Zint_eq) (triv_div_R _ _ (eq_bool_R2 Zint_eq)) cnR (nat_Rxx n));
    move=> //; [|exact/FExpr_R_map/Zint_int_of_Z..].
  apply: list_R_map => -[{}pe1 {}pe2].
  by apply: pair_R; apply/PExpr_R_map/Zint_int_of_Z.
rewrite -[RHS]omap_id; apply: option_R_eq; apply: option_R_omap2 fc12 => a b ab.
rewrite -[RHS]map_id; apply: list_R_eq; apply: list_R_map2 ab => {}a {}b ab.
rewrite -[RHS]PEmap_id; apply: PExpr_R_eq; apply: PExpr_R_PEmap2 ab => {}a {}b.
by move/eqP.
Qed.

Lemma FEeval_map_int_of_Z l (fe : FExpr Z) :
  FEeval 0 1 +%R *%R (fun x y => x - y) -%R (fun x y => x / y) (@GRing.inv R)
    N.to_nat (GRing.exp (R:=R)) intr (env_nth 0) l (FEmap int_of_Z fe)
  = FEeval 0 1 +%R *%R (fun x y => x - y) -%R (fun x y => x / y) (@GRing.inv R)
      N.to_nat (GRing.exp (R:=R)) R_of_Z (env_nth 0) l fe.
Proof. by elim: fe => //= ? -> // ? ->. Qed.

Lemma PCond_map_int_of_Z l lpe :
    PCond true negb andb 0 1 +%R *%R (fun x y => x - y) -%R
      N.to_nat (GRing.exp (R:=R)) eq_op R_of_Z (env_nth 0) l lpe ->
  PCond true negb andb 0 1 +%R *%R (fun x y => x - y) -%R
    N.to_nat (GRing.exp (R:=R)) eq_op intr (env_nth 0) l
    (map (PEmap int_of_Z) lpe).
Proof.
elim: lpe => [//|pe lpe IH] /=.
by rewrite !PCond_cons PEeval_map_int_of_Z => /andP[-> /IH].
Qed.

Lemma cond_norm00_map_int_of_Z Zc ic : list_R (PExpr_R Zint) Zc ic ->
  list_R (PExpr_R Zint)
    (cond_norm (Fcons00 Z0 (Zpos xH) Z.add Z.mul Z.sub Z.opp Z.eqb) Zc)
    (cond_norm (Fcons00 0 1 +%R *%R (fun x y => x - y) -%R eq_op) ic).
Proof.
apply: cond_norm_R => Ze ie Zeie {}Zc {}ic Zcic.
exact: (Fcons00_R _ _ ZintD ZintM ZintB ZintN (eq_bool_R2 Zint_eq)).
Qed.

#[local] Notation FEeval := (FEeval 0 1 +%R *%R (fun x y => x - y) -%R
  (fun x y => x / y) (@GRing.inv R) N.to_nat (@GRing.exp R) R_of_Z (env_nth 0)).
#[local] Notation PEeval_eqs := (PEeval_eqs true andb 0 1 +%R *%R
  (fun x y => x - y) -%R N.to_nat (@GRing.exp R) eq_op R_of_Z (env_nth 0)).
#[local] Notation PCond := (PCond true negb andb 0 1 +%R *%R (fun x y => x - y)
  -%R N.to_nat (@GRing.exp R) eq_op R_of_Z (env_nth 0)).
#[local] Notation cond_norm := (cond_norm (Fcons00
  Z0 (Zpos xH) Z.add Z.mul Z.sub Z.opp Z.eqb)).
#[local] Notation field_checker := (field_checker Z0 (Zpos xH) Z.add Z.mul
  Z.sub Z.opp Z.pow_pos Z.eqb (triv_div Z0 (Zpos xH) Z.eqb) cond_norm).

Lemma Zfield_correct n l lpe fe1 fe2 lc :
    PEeval_eqs l lpe ->
    field_checker n lpe fe1 fe2 = Some lc ->
    PCond l lc ->
  FEeval l fe1 = FEeval l fe2.
Proof.
move=> /PEeval_eqs_map_int_of_Z + /(congr1 (omap (map (PEmap int_of_Z)))).
move=> + + /PCond_map_int_of_Z; rewrite -!FEeval_map_int_of_Z.
rewrite (field_checker_map_int_of_Z cond_norm00_map_int_of_Z).
apply: (Cfield_checkerT (@Ctriv_divP int)) => el el'.
exact/PCond_cond_norm/PCond_Fcons00.
Qed.

End Zfield.

Section ZnumField.
Variables (R : numFieldType).

#[local] Notation R_of_Z := (R_of_Z R).

Lemma cond_norm2_map_int_of_Z Zc ic : list_R (PExpr_R Zint) Zc ic ->
  list_R (PExpr_R Zint)
    (cond_norm (Fcons2 Z0 (Zpos xH) Z.add Z.mul Z.sub Z.opp Z.pow_pos Z.eqb) Zc)
    (cond_norm (Fcons2 0 1 +%R *%R (fun x y => x - y) -%R
                  (fun x n => x ^+ Pos.to_nat n) eq_op) ic).
Proof.
apply: cond_norm_R => Ze ie Zeie {}Zc {}ic Zcic.
exact: (Fcons2_R _ _ ZintD ZintM ZintB ZintN Zint_pow_pos_pos
  (eq_bool_R2 Zint_eq)).
Qed.

#[local] Notation FEeval := (FEeval 0 1 +%R *%R (fun x y => x - y) -%R
  (fun x y => x / y) (@GRing.inv R) N.to_nat (@GRing.exp R) R_of_Z (env_nth 0)).
#[local] Notation PEeval_eqs := (PEeval_eqs true andb 0 1 +%R *%R
  (fun x y => x - y) -%R N.to_nat (@GRing.exp R) eq_op R_of_Z (env_nth 0)).
#[local] Notation PCond := (PCond true negb andb 0 1 +%R *%R (fun x y => x - y)
  -%R N.to_nat (@GRing.exp R) eq_op R_of_Z (env_nth 0)).
#[local] Notation cond_norm := (cond_norm (Fcons2
  Z0 (Zpos xH) Z.add Z.mul Z.sub Z.opp Z.pow_pos Z.eqb)).
#[local] Notation field_checker := (field_checker Z0 (Zpos xH) Z.add Z.mul
  Z.sub Z.opp Z.pow_pos Z.eqb (triv_div Z0 (Zpos xH) Z.eqb) cond_norm).

Lemma ZnumField_correct n l lpe fe1 fe2 lc :
    PEeval_eqs l lpe ->
    field_checker n lpe fe1 fe2 = Some lc ->
    PCond l lc ->
  FEeval l fe1 = FEeval l fe2.
Proof.
move=> /PEeval_eqs_map_int_of_Z + /(congr1 (omap (map (PEmap int_of_Z)))).
move=> + + /PCond_map_int_of_Z; rewrite -!FEeval_map_int_of_Z.
rewrite (field_checker_map_int_of_Z cond_norm2_map_int_of_Z).
apply: (Cfield_checkerT (@Ctriv_divP int)) => el el'.
exact/PCond_cond_norm/PCond_Fcons2/ler0z.
Qed.

End ZnumField.

(* Everything below is essentially imported form algebra-tactics *)

Lemma field_correct (F : fieldType) n env
    (lpe : seq ((RExpr F * RExpr F) * (PExpr Z * PExpr Z)))
    (re1 re2 : RExpr F) (fe1 fe2 : FExpr Z) lc :
    Reval_eqs lpe ->
    (forall R_of_Z zero one add opp mul exp inv,
       let R_of_N b n := let n := R_of_Z (Z.of_N n) in if b then inv n else n in
       let opp_intr := Some (opp, intr) in
       let norm := Rnorm R_of_N zero one add mul opp_intr
         (fun x n => exp x (N.to_nat n)) (Some inv) false false id in
       let eval := PEeval zero one add mul (fun x y => add x (opp y)) opp
         N.to_nat exp R_of_Z (env_nth zero) env in
       let feval := FEeval zero one add mul (fun x y => add x (opp y)) opp
         (fun x y => mul x (inv y)) inv N.to_nat exp R_of_Z (env_nth zero) env
       in
       (norm re1, norm re2)
         :: map (fun pp => (norm pp.1.1, norm pp.1.2)) lpe
       = (feval fe1, feval fe2)
           :: map (fun pp => (eval pp.2.1, eval pp.2.2)) lpe) ->
    field_checker Z0 (Zpos xH) Z.add Z.mul Z.sub Z.opp Z.pow_pos
      Z.eqb (triv_div Z0 (Zpos xH) Z.eqb) (cond_norm (Fcons00
         Z0 (Zpos xH) Z.add Z.mul Z.sub Z.opp Z.eqb))
      n (map snd lpe) fe1 fe2 = Some lc ->
    PCond true negb andb 0 1 +%R *%R (fun x y => x - y) -%R N.to_nat
      (@GRing.exp F) eq_op (R_of_Z F) (env_nth 0) (locked env) lc ->
  Reval re1 = Reval re2.
Proof.
pose R_of_N b n : Field F :=
  let n := R_of_Z F (Z.of_N n) in if b then n^-1 else n.
have R_of_NE : R_of_N =2 fun b n => @invi (Field F) b (N.to_nat n)%:R.
  by case=> [] [].
rewrite !(@Rnorm_correct (Field F) false _ erefl) -lock.
rewrite -!(Rnorm_eq_F_of_N R_of_NE) => elpe.
move=> /( _ (R_of_Z F) 0 1 +%R -%R *%R (@GRing.exp F) (@GRing.inv F))
    [-> ->]/= nelpe; apply: Zfield_correct.
elim: lpe elpe nelpe => [//|[[{}re1 {}re2] [{}pe1 {}pe2]] lpe IH] /=.
move=> -[re12 relpe] [rp1 rp2 rple]; have := IH relpe rple.
rewrite -rp1 -rp2 !(Rnorm_eq_F_of_N R_of_NE).
rewrite -!(@Rnorm_correct (Field F) false _ erefl) re12.
by case: lpe {IH relpe rple} => /=; rewrite eqxx.
Qed.

Lemma numField_correct (F : numFieldType) n env
    (lpe : seq ((RExpr F * RExpr F) * (PExpr Z * PExpr Z)))
    (re1 re2 : RExpr F) (fe1 fe2 : FExpr Z) lc :
    Reval_eqs lpe ->
    (forall R_of_Z zero one add opp mul exp inv,
       let R_of_N b n := let n := R_of_Z (Z.of_N n) in if b then inv n else n in
       let opp_intr := Some (opp, intr) in
       let norm := Rnorm R_of_N zero one add mul opp_intr
         (fun x n => exp x (N.to_nat n)) (Some inv) false false id in
       let eval := PEeval zero one add mul (fun x y => add x (opp y)) opp
         N.to_nat exp R_of_Z (env_nth zero) env in
       let feval := FEeval zero one add mul (fun x y => add x (opp y)) opp
         (fun x y => mul x (inv y)) inv N.to_nat exp R_of_Z (env_nth zero) env
       in
       (norm re1, norm re2)
         :: map (fun pp => (norm pp.1.1, norm pp.1.2)) lpe
       = (feval fe1, feval fe2)
           :: map (fun pp => (eval pp.2.1, eval pp.2.2)) lpe) ->
    field_checker Z0 (Zpos xH) Z.add Z.mul Z.sub Z.opp Z.pow_pos
      Z.eqb (triv_div Z0 (Zpos xH) Z.eqb) (cond_norm (Fcons2
         Z0 (Zpos xH) Z.add Z.mul Z.sub Z.opp Z.pow_pos Z.eqb))
      n (map snd lpe) fe1 fe2 = Some lc ->
    PCond true negb andb 0 1 +%R *%R (fun x y => x - y) -%R N.to_nat
      (@GRing.exp F) eq_op (R_of_Z F) (env_nth 0) (locked env) lc ->
  Reval re1 = Reval re2.
Proof.
pose R_of_N b n : Field F :=
  let n := R_of_Z F (Z.of_N n) in if b then n^-1 else n.
have R_of_NE : R_of_N =2 fun b n => @invi (Field F) b (N.to_nat n)%:R.
  by case=> [] [].
rewrite !(@Rnorm_correct (Field F) false _ erefl) -lock.
rewrite -!(Rnorm_eq_F_of_N R_of_NE) => elpe.
move=> /( _ (R_of_Z F) 0 1 +%R -%R *%R (@GRing.exp F) (@GRing.inv F))
    [-> ->]/= nelpe; apply: ZnumField_correct.
elim: lpe elpe nelpe => [//|[[{}re1 {}re2] [{}pe1 {}pe2]] lpe IH] /=.
move=> -[re12 relpe] [rp1 rp2 rple]; have := IH relpe rple.
rewrite -rp1 -rp2 !(Rnorm_eq_F_of_N R_of_NE).
rewrite -!(@Rnorm_correct (Field F) false _ erefl) re12.
by case: lpe {IH relpe rple} => /=; rewrite eqxx.
Qed.

End Internals.

(* Main tactics, called from the elpi parser (c.f., ring.elpi) *)

Ltac field_reflection Lem F VarMap Lpe RE1 RE2 FE1 FE2 LpeProofs :=
  let nvarmap := fresh "__varmap" in
  let nlpe := fresh "__lpe" in
  let nre1 := fresh "__re1" in
  let nre2 := fresh "__re2" in
  let nfe1 := fresh "__fe1" in
  let nfe2 := fresh "__fe2" in
  let nlpeproofs := fresh "__lpeproofs" in
  pose nvarmap := VarMap;
  pose nlpe := Lpe;
  pose nre1 := RE1;
  pose nre2 := RE2;
  pose nfe1 := FE1;
  pose nfe2 := FE2;
  pose nlpeproofs := LpeProofs;
  refine (Lem F 100%N nvarmap nlpe nre1 nre2 nfe1 nfe2 _ nlpeproofs
    ltac:(reflexivity)
    ltac:((* Here we'd like to do "vm_compute; reflexivity".
             But in the goal of the form "heavy_computation = Some ?evar"
             we only want to vm_compute the LHS, this is done as follows: *)
          let nlhs := fresh "__lhs" in
          let nlhse := fresh "__lhse" in
          set nlhs := (X in X = _);
          let lhse := eval vm_compute in nlhs in pose nlhse := lhse;
          rewrite (_ : nlhs = nlhse);
             (try match goal with
                | |- @eq _ nlhs _ => vm_cast_no_check (@erefl _ nlhse)
                end);  (* due to SsrOldRewriteGoalsOrder we don't know whether to use first or last, replace the "try match ..." with "first", when this is sorted out *)
          rewrite /nlhse => {nlhs nlhse};
          reflexivity)
    _);
  rewrite /Internals.env_nth /Internals.R_of_Z/= /Pos.to_nat/= -?pmulrn;
  rewrite -1?lock /nth /nvarmap;
  move=> {nvarmap nlpe nre1 nre2 nfe1 nfe2 nlpeproofs};
  do ?[apply/andP; split]; rewrite -1?/(Datatypes.is_true _).

Strategy expand [FEeval].

Elpi Tactic mcfieldq.
Elpi Accumulate Db mc.canonicals.db.
#[warning="-elpi.flex-clause"] (* remove when requiring elpi >= 3 (with =!=>) *)
Elpi Accumulate File ring_tactic field_tactic.
Elpi Accumulate lp:{{%(*
shorten coq.ltac.{ open, all }.
msolve GL SubGL :-
  coq.warning "mathcomp.dev-tactic" "mathcomp.dev-field"
    "`field?` is for development purposes, use `field` in final scripts.",
  all (open field) GL SubGL.
%*)}}.

Tactic Notation "field?" := elpi mcfieldq.
Tactic Notation "field?" ":" ne_constr_list(L) :=
  elpi mcfieldq ltac_term_list:(L).
Tactic Notation "#[" attributes(A) "]" "field?" :=
  ltac_attributes:(A) elpi mcfieldq.
Tactic Notation "#[" attributes(A) "]" "field?" ":" ne_constr_list(L) :=
  ltac_attributes:(A) elpi mcfieldq ltac_term_list:(L).

Elpi Tactic mcfield.
Elpi Accumulate Db mc.canonicals.db.
#[warning="-elpi.flex-clause"] (* remove when requiring elpi >= 3 (with =!=>) *)
Elpi Accumulate File ring_tactic field_tactic.
Elpi Accumulate lp:{{%(*
shorten coq.ltac.{ open, all }.
msolve GL SubGL :- all (open field) GL SubGL.
%*)}}.

Ltac field_tactic := done.

Ltac field_term :=
  field_tactic
  || fail 1 "There are remaining goals, use ""field?"" to inspect them".

Tactic Notation "field" := solve [ elpi mcfield; field_term ].
Tactic Notation "field" ":" ne_constr_list(L) :=
  solve [ elpi mcfield ltac_term_list:(L); field_term ].
Tactic Notation "#[" attributes(A) "]" "field" :=
  solve [ ltac_attributes:(A) elpi mcfield; field_term ].
Tactic Notation "#[" attributes(A) "]" "field" ":" ne_constr_list(L) :=
  solve [ ltac_attributes:(A) elpi mcfield ltac_term_list:(L); field_term ].

Elpi Query lp:{{ canonical-init library "mc.canonicals.db" }}.
Elpi Query lp:{{ coercion-init library "mc.canonicals.db" }}.

(* Remove the line below when requiring rocq-elpi > 3.2.0
c.f., https://github.com/LPCIC/coq-elpi/pull/866 *)
#[global] Unset Uniform Inductive Parameters.

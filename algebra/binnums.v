(* Distributed under the terms of CeCILL-B.                                  *)
From Corelib Require Import PosDef IntDef.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From mathcomp Require Import ssralg ssrnum ssrint.

(******************************************************************************)
(* This file develops some link with binary numbers from Corelib, defining:   *)
(*     pos_nat == refinement relation between positive and nat                *)
(*        Zint == refinement relation between Z and int                       *)
(* It also provides the conversion function int_of_Z, as well as              *)
(* lemmas proving the correctness of the Corelib operators on binary numbers. *)
(* This is only intended to use the binary numbers for effective computations,*)
(* in reflexive tactics for instance.                                         *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Import GRing.Theory Num.Theory.

Definition pos_nat (p : positive) (n : nat) := Pos.to_nat p == n.

Lemma pos_nat_Pos_to_nat p : pos_nat p (Pos.to_nat p). Proof. exact/eqP. Qed.
Hint Resolve pos_nat_Pos_to_nat : core.

Variant pos_nat_spec (p : positive) (n : nat) : positive -> nat -> bool -> Set :=
  | Pos_nat_spec_false : pos_nat_spec p n p n false
  | Pos_nat_spec_xH : p = xH -> n = 1%N -> pos_nat_spec p n xH 1 true
  | Pos_nat_spec_xO :
      forall p' n', p = xO p' -> n = n'.*2 -> pos_nat p' n' ->
        pos_nat_spec p n (xO p') n'.*2 true
  | Pos_nat_spec_xI :
      forall p' n', p = xI p' -> n = n'.*2.+1 -> pos_nat p' n' ->
        pos_nat_spec p n (xI p') n'.*2.+1 true.

Lemma iter_opDdoubler p n : Pos.iter_op addn p n.*2 = (Pos.iter_op addn p n).*2.
Proof. by elim: p n => [p ip | p ip |//] n /=; rewrite !addnn ip ?doubleD. Qed.

Lemma iter_opD2 p : Pos.iter_op addn p 2 = (Pos.iter_op addn p 1).*2.
Proof. by rewrite -[2]/1.*2 iter_opDdoubler. Qed.

Lemma pos_natP p n : pos_nat_spec p n p n (pos_nat p n).
Proof.
case: (boolP (pos_nat p n)) => /eqP pn; last exact: Pos_nat_spec_false.
elim: p n pn => [p IH | p IH |] n <-; rewrite /Pos.to_nat /= ?iter_opD2.
- exact: Pos_nat_spec_xI.
- exact: Pos_nat_spec_xO.
- exact: Pos_nat_spec_xH.
Qed.

Lemma pos_nat_ind (P : positive -> nat -> Prop) :
    (P xH 1%N) ->
    (forall p n, pos_nat p n -> P p n -> P (xO p) n.*2) ->
    (forall p n, pos_nat p n -> P p n -> P (xI p) n.*2.+1) ->
  forall p n, pos_nat p n -> P p n.
Proof.
move=> P1 Pd PdS; elim=> [p Ppn | p Ppn |] n; case: pos_natP => //.
- by move=> _ {}n [<-] _ pn _; apply: PdS (Ppn n pn).
- by move=> _ {}n [<-] _ pn _; apply: Pd (Ppn n pn).
Qed.

Lemma Pos_to_nat_gt0 p : (Pos.to_nat p > 0)%N.
Proof. by elim: p => // ? ?; rewrite /Pos.to_nat/= iter_opD2 double_gt0. Qed.

Lemma Pos_to_nat0F p : (Pos.to_nat p == 0) = false.
Proof. by apply/negbTE; rewrite -lt0n Pos_to_nat_gt0. Qed.

Lemma pos_nat_exS p n : pos_nat p n -> exists2 n', n = n'.+1 & pos_nat p n'.+1.
Proof.
by case: n => [|n pn]; [move: (Pos_to_nat_gt0 p) => /[swap]/eqP-> | exists n].
Qed.

Lemma pos_nat1 : pos_nat xH 1. Proof. by []. Qed.
Hint Resolve pos_nat1 : core.

Lemma pos_nat_double p n : pos_nat p~0 n.*2 = pos_nat p n.
Proof.
apply/idP/idP => [|/eqP<-]; last by rewrite /pos_nat [eqbLHS]iter_opD2.
by case: pos_natP => // _ _ [<-] /double_inj<-.
Qed.

Lemma pos_nat_doubleS p n : pos_nat p~1 n.*2.+1 = pos_nat p n.
Proof.
rewrite /pos_nat -[Pos.to_nat p~1]/(Pos.to_nat p~0).+1 eqSS.
exact: pos_nat_double.
Qed.

Definition pos_natE := (pos_nat_double, pos_nat_doubleS, pos_nat1).

Lemma pos_natS p n : pos_nat p n -> pos_nat (Pos.succ p) (S n).
Proof. by elim/pos_nat_ind => // ? ? ? ?; rewrite -?doubleS pos_natE. Qed.

Lemma pos_natD p n p' n' :
  pos_nat p n -> pos_nat p' n' -> pos_nat (Pos.add p p') (n + n').
Proof.
move=> pn p'n'; suff: pos_nat (Pos.add p p') (n + n')
  && pos_nat (Pos.add_carry p p') (n + n').+1 by move=> /andP[].
elim/pos_nat_ind: pn p' n' p'n' => [p' n' {p n} ||];
    [|move=> {}p {}n pn IH p' n'..].
- by case: pos_natP => //?? _ _ e; rewrite add1n -doubleS !pos_natE ?e pos_natS.
- case: pos_natP => [//|_ _ _||] /=; [|move=> {}p' {}n' _ _ /IH/andP[e es] _..];
  by rewrite ?addn1 ?addnS -?doubleD -?doubleS !pos_natE ?pn ?pos_natS ?e ?es.
- case: pos_natP => [//|_ _ _||] /=; [|move=> {}p' {}n' _ _ /IH/andP[e es] _..];
  by rewrite ?addn1 ?addnS?addSn -?doubleD -?doubleS !pos_natE ?pos_natS ?e ?es.
Qed.

Lemma pos_nat_pred_double p n :
  pos_nat p n -> pos_nat (Pos.pred_double p) n.*2.-1.
Proof.
by elim/pos_nat_ind => [//||] {}p {}n; [move=> /pos_nat_exS[?-> pn]|];
  rewrite /Pos.pred_double/= -/double -?doubleS !pos_natE.
(* when dropping support for Coq 8.20, replace above proof by
by elim/pos_nat_ind => [//||] {}p {}n; [move=> /pos_nat_exS[?-> pn]/=|];
  rewrite !pos_natE. *)
Qed.

Lemma pos_natM p n p' n' :
  pos_nat p n -> pos_nat p' n' -> pos_nat (Pos.mul p p') (n * n').
Proof.
move=> pn; elim/pos_nat_ind: pn p' n' => [p' n' p'n'||];
    [|move=> {}p {}n pn IH p' n' /[dup] p'n' /IH pp'nn' /=..].
- by rewrite mul1n.
- by rewrite -doubleMl pos_natE.
- by rewrite mulSn pos_natD// -doubleMl pos_natE.
Qed.

Lemma pos_nat_eq p n (pn : pos_nat p n) p' n' (p'n' : pos_nat p' n') :
  Pos.eqb p p' = (n == n').
Proof.
elim/pos_nat_ind: pn p' n' p'n' => [p' n' {p n} ||];
    [|move=> {}p {}n pn IH p' n'..].
- case: pos_natP => [//|//||] {}p' {}n' _ _ p'n' _ /=.
  + by rewrite -double0 neq_doubleS_double.
  + apply/esym/negbTE; rewrite eqSS eq_sym double_eq0.
    by rewrite -(eqP p'n') Pos_to_nat0F.
- case: pos_natP => [//|_ _ _||] /=; [|move=> {}p' {}n' _ _ p'n' _..].
  + by rewrite -double0 eq_sym neq_doubleS_double.
  + by rewrite (inj_eq double_inj); apply: IH.
  + by rewrite eq_sym neq_doubleS_double.
- case: pos_natP => [//|_ _ _||] /=; [|move=> {}p' {}n' _ _ p'n' _..].
  + by apply/esym/negbTE; rewrite eqSS double_eq0 -(eqP pn) Pos_to_nat0F.
  + by rewrite neq_doubleS_double.
  + by rewrite eqSS (inj_eq double_inj); apply: IH.
Qed.

Lemma pos_nat_compare p n (pn : pos_nat p n) p' n' (p'n' : pos_nat p' n') :
  Pos.compare p p' = if n == n' then Eq else if (n < n')%N then Lt else Gt.
Proof.
rewrite /Pos.compare; elim/pos_nat_ind: pn Eq p' n' p'n' => [c p' n' {p n} ||];
    [|move=> {}p {}n pn IH c p' n'..].
- case: pos_natP => [//|//||] /= {}p' {}n' _ _ p'n' _.
  + rewrite -double0 neq_doubleS_double -doubleS leq_double ifT//.
    by rewrite -(eqP p'n') Pos_to_nat_gt0.
  + rewrite eqSS eq_sym double_eq0 ltnS double_gt0 ifF.
      by rewrite ifT// -(eqP p'n') Pos_to_nat_gt0.
    by apply/negbTE/lt0n_neq0; rewrite -(eqP p'n') Pos_to_nat_gt0.
- case: pos_natP => [//|_ _ _||] /=; [|move=> {}p' {}n' _ _ p'n' _..].
  + rewrite -double0 eq_sym neq_doubleS_double ltnS leq_double ifF//.
    by rewrite leqn0 -(eqP pn) Pos_to_nat0F.
  + by rewrite (inj_eq double_inj) ltn_double -(IH _ _ _ p'n').
  + rewrite eq_sym neq_doubleS_double ltnS leq_double (IH _ _ _ p'n').
    by rewrite  [in RHS]leq_eqVlt; case: eqP.
- case: pos_natP => [//|_ _ _||] /=; [|move=> {}p' {}n' _ _ p'n' _..].
  + by rewrite ifF// eqSS double_eq0 -(eqP pn) Pos_to_nat0F.
  + rewrite neq_doubleS_double -doubleS leq_double (IH _ _ _ p'n').
    by case: eqP => [->|//]; rewrite ltnn.
  + by rewrite eqSS (inj_eq double_inj) ltnS ltn_double (IH _ _ _ p'n').
Qed.

Lemma pos_nat_le p n (pn : pos_nat p n) p' n' (p'n' : pos_nat p' n') :
  Pos.leb p p' = (n <= n')%N.
Proof.
rewrite /Pos.leb (pos_nat_compare pn p'n') [RHS]leq_eqVlt.
by case: eqP => [//| _ /=]; case: ltnP.
Qed.

Lemma Pos_to_natI : injective Pos.to_nat.
Proof.
elim=> [i IH | i IH |]; rewrite /Pos.to_nat; case=> [j | j |]//=.
- by rewrite !iter_opD2 => -[/double_inj/IH->].
- by move/eqP; rewrite !iter_opD2 neq_doubleS_double.
- move: (Pos_to_nat_gt0 i); rewrite iter_opD2 => /[swap] -[/eqP].
  by rewrite double_eq0 => /eqP<-; rewrite ltnn.
- by move/esym/eqP; rewrite !iter_opD2 neq_doubleS_double.
- by rewrite !iter_opD2 => /double_inj/IH->.
- by move/esym/eqP; rewrite iter_opD2 -double0 neq_doubleS_double.
- move: (Pos_to_nat_gt0 j); rewrite iter_opD2 => /[swap] -[/esym/eqP].
  by rewrite double_eq0 => /eqP<-; rewrite ltnn.
- by move/eqP; rewrite iter_opD2 -double0 neq_doubleS_double.
Qed.

Lemma Pos_to_nat1 : Pos.to_nat xH = 1%N. Proof. by []. Qed.

Lemma Pos_to_nat_double i : Pos.to_nat (xO i) = (Pos.to_nat i).*2.
Proof. exact/eqP/(eqbRL (pos_nat_double i (Pos.to_nat i))). Qed.

Lemma Pos_to_nat_doubleS i : Pos.to_nat (xI i) = (Pos.to_nat i).*2.+1.
Proof. exact/eqP/(eqbRL (pos_nat_doubleS i (Pos.to_nat i))). Qed.

Lemma Pos_to_natS i : Pos.to_nat (Pos.succ i) = (Pos.to_nat i).+1.
Proof. exact: eqP (pos_natS (pos_nat_Pos_to_nat i)). Qed.

Lemma Pos_to_natD i j :
  Pos.to_nat (Pos.add i j) = (Pos.to_nat i + Pos.to_nat j)%N.
Proof. exact: eqP (pos_natD (pos_nat_Pos_to_nat i) (pos_nat_Pos_to_nat j)). Qed.

Lemma Pos_to_nat_pred_double i :
  Pos.to_nat (Pos.pred_double i) = (Pos.to_nat i).*2.-1.
Proof. exact: eqP (pos_nat_pred_double (pos_nat_Pos_to_nat i)). Qed.

Lemma Pos_to_natM i j :
  Pos.to_nat (Pos.mul i j) = (Pos.to_nat i * Pos.to_nat j)%N.
Proof. exact: eqP (pos_natM (pos_nat_Pos_to_nat i) (pos_nat_Pos_to_nat j)). Qed.

Definition Pos_to_natE := (Pos_to_nat1, Pos_to_nat_double, Pos_to_nat_doubleS,
  Pos_to_natS, Pos_to_natD, Pos_to_nat_pred_double, Pos_to_natM).

Definition int_of_Z (i : Z) : int :=
  match i with
  | Z0 => Posz 0
  | Zpos p => Posz (Pos.to_nat p)
  | Zneg p => Negz (Pos.to_nat p).-1
  end.

Definition Zint (i : Z) (n : int) := int_of_Z i == n.

Lemma Zint_int_of_Z i : Zint i (int_of_Z i). Proof. exact/eqP. Qed.
Hint Resolve Zint_int_of_Z : core.

Variant Zint_spec (i : Z) (n : int) : Z -> int -> bool -> Set :=
  | Zint_spec_false : Zint_spec i n i n false
  | Zint_spec_Z0 : i = Z0 -> n = Posz 0 -> Zint_spec i n Z0 (Posz 0) true
  | Zint_spec_Zpos :
      forall p' n', i = Zpos p' -> n = Posz n' -> pos_nat p' n' ->
        Zint_spec i n (Zpos p') (Posz n') true
  | Zint_spec_Zneg :
      forall p' n', i = Zneg p' -> n = Negz n' -> pos_nat p' n'.+1 ->
        Zint_spec i n (Zneg p') (Negz n') true.

Lemma ZintP i n : Zint_spec i n i n (Zint i n).
Proof.
case: (boolP (Zint i n)) => /eqP Zin; last exact: Zint_spec_false.
case: i n Zin => [|p|p] n <- /=; [exact: Zint_spec_Z0|exact: Zint_spec_Zpos|].
by apply: Zint_spec_Zneg; rewrite ?prednK ?Pos_to_nat_gt0.
Qed.

Lemma Zint0 : Zint Z0 0. Proof. by []. Qed.
Hint Resolve Zint0 : core.

Lemma Zint_pos p n : Zint (Zpos p) (Posz n) = pos_nat p n. Proof. by []. Qed.

Lemma Zint_neg p n : Zint (Zneg p) (Negz n) = pos_nat p n.+1.
Proof.
by apply/idP/idP; [case: ZintP => // _ _ [<-] [<-]|rewrite /Zint/= => /eqP->].
Qed.

Definition ZintE := (Zint0, Zint_pos, Zint_neg).

Lemma Zint_double i n : Zint i n -> Zint (Z.double i) (2 * n).
Proof.
case: ZintP => // {i}p {}n _ _ pn _ /=; first by rewrite ZintE mul2n pos_natE.
by rewrite -Negz_doubleS ZintE -doubleS pos_natE.
Qed.

Lemma Zint_succ_double i n : Zint i n -> Zint (Z.succ_double i) (2 * n + 1).
Proof.
case: ZintP => // {i}p {}n _ _ pn _ /=.
  by rewrite ZintE mul2n addn1 pos_natE.
by rewrite -Negz_doubleS NegzS addrK ZintE -predn_doubleS pos_nat_pred_double.
Qed.

Lemma Zint_pred_double i n : Zint i n -> Zint (Z.pred_double i) (2 * n - 1).
Proof.
case: ZintP => // {i}p {}n _ _/= => [/pos_nat_exS[{}n-> pn] | pn] _; last first.
  by rewrite -Negz_doubleS -NegzS ZintE -doubleS pos_natE.
rewrite -PoszM mul2n doubleS -addn1 PoszD addrK.
by rewrite ZintE -predn_doubleS pos_nat_pred_double.
Qed.

Lemma Zint_pos_sub p n p' n' :
  pos_nat p n -> pos_nat p' n' -> Zint (Z.pos_sub p p') (Posz n - Posz n').
Proof.
move=> pn p'n'; elim/pos_nat_ind: p'n' p n pn => [p n||];
    [|move=> {}p' {}n' p'n' IH p n..].
- case: pos_natP => // {}p {}n _ _ + _ /=; last first.
    by rewrite -addn1 PoszD addrK ZintE pos_natE.
  move=> /pos_nat_exS[{}n-> pn]; rewrite doubleS -addn1 PoszD addrK.
  by rewrite ZintE -predn_doubleS pos_nat_pred_double.
- case: pos_natP => [//|_ _ _||]/=; [|move=> {}p {}n _ _ pn _..].
  + move: p'n' {IH} => /pos_nat_exS[{}n'-> p'n'].
    rewrite -opprB doubleS -addn1 PoszD addrK -NegzE.
    by rewrite ZintE -predn_doubleS pos_nat_pred_double.
  + by rewrite -!mul2n !PoszM -mulrBr Zint_double ?IH.
  + rewrite -[n.*2.+1]addn1 PoszD addrAC -!mul2n !PoszM -mulrBr.
    by rewrite Zint_succ_double ?IH.
- case: pos_natP => [//|_ _ _||]/=; [|move=> {}p {}n _ _ pn _..].
  + move: p'n' {IH} => /pos_nat_exS[{}n'-> p'n']; rewrite -opprB -addn1.
    by rewrite PoszD addrK doubleS -NegzE ZintE -doubleS pos_natE.
  + rewrite -addn1 PoszD opprD addrA -!mul2n !PoszM -mulrBr.
    by rewrite Zint_pred_double ?IH.
  + rewrite -addn1 -[n'.*2.+1]add1n !PoszD addrKA -!mul2n !PoszM -mulrBr.
    by rewrite Zint_double ?IH.
Qed.

Lemma ZintD i n (Zin : Zint i n) i' n' (Zi'n' : Zint i' n') :
  Zint (Z.add i i') (n + n').
Proof.
case: ZintP Zin => [//|||]; [|move=> {i}p {}n _ _ pn _..].
- by rewrite add0r.
- case: ZintP Zi'n' => [//|||]; [|move=> {i'}p' {}n' _ _ p'n' _ /=..].
  + by rewrite addr0.
  + by rewrite ZintE pos_natD.
  + by rewrite NegzE Zint_pos_sub.
- case: ZintP Zi'n' => [//|||]; [|move=> {i'}p' {}n' _ _ p'n' _ /=..].
  + by rewrite addr0 ZintE.
  + by rewrite NegzE [_ + Posz n']addrC Zint_pos_sub.
  + by rewrite !NegzE -opprD -PoszD addSn -NegzE ZintE -addSn pos_natD.
Qed.

Lemma ZintN i n : Zint i n -> Zint (Z.opp i) (- n).
Proof.
by case: ZintP => // {i}p {}n _ _ /pos_nat_exS[{}n-> pn]; rewrite -NegzE ZintE.
Qed.

Lemma ZintB i n (Zin : Zint i n) i' n' (Zi'n' : Zint i' n') :
  Zint (Z.sub i i') (n - n').
Proof. by apply: ZintD => //; apply: ZintN. Qed.

Lemma ZintM i n (Zin : Zint i n) i' n' (Zi'n' : Zint i' n') :
  Zint (Z.mul i i') (n * n').
Proof.
case: ZintP Zin => [//|||]; [|move=> {i}p {}n _ _ pn _..].
- by rewrite mul0r.
- case: ZintP Zi'n' => [//|||] /=; [|move=> {i'}p' {}n' _ _ p'n' _..].
  + by rewrite mulr0.
  + by rewrite ZintE pos_natM.
  + move: pn => /pos_nat_exS[{}n-> pn]; rewrite NegzE mulrN -PoszM.
    by rewrite mulnS addSn -NegzE ZintE -addSn -mulnS pos_natM.
- case: ZintP Zi'n' => [//|||] /=; [|move=> {i'}p' {}n' _ _ p'n' _..].
  + by rewrite mulr0.
  + move: p'n' => /pos_nat_exS[{}n'-> p'n']; rewrite NegzE mulNr -PoszM.
    by rewrite mulnS addSn -NegzE ZintE -addSn -mulnS pos_natM.
  + by rewrite !NegzE mulrNN -PoszM ZintE pos_natM.
Qed.

Lemma Zint_eq i n (Zin : Zint i n) i' n' (Zi'n' : Zint i' n') :
  Z.eqb i i' = (n == n').
Proof.
case: ZintP Zin => [//|||]; [|move=> {i}p {}n _ _ pn _..].
- case: ZintP Zi'n' => [//|//||//] /= {i'}p' {}n' _ _ p'n' _ _ _ _.
  by apply/esym/negbTE; rewrite eq_sym eqz_nat -(eqP p'n') Pos_to_nat0F.
- case: ZintP Zi'n' => [//|_ _ _|{i'}p' {}n' _ _ p'n' _|//] /=.
  + by apply/esym/negbTE; rewrite eqz_nat -(eqP pn) Pos_to_nat0F.
  + by rewrite eqz_nat; apply: pos_nat_eq.
- case: ZintP Zi'n' => [//|//|//|{i'}p' {}n' _ _ p'n' _ /=].
  by rewrite !NegzE eqr_opp eqz_nat; apply: pos_nat_eq.
Qed.

Lemma Zint_le i n (Zin : Zint i n) i' n' (Zi'n' : Zint i' n') :
  Z.leb i i' = (n <= n').
Proof.
case: ZintP Zin => [//|||]; [|move=> {i}p {}n _ _ pn _..].
- by case: ZintP Zi'n'.
- case: ZintP Zi'n' => [//|_ _ _|{i'}p' {}n' _ _ p'n' _|//] /=.
  + by apply/esym/negbTE; rewrite lez0_nat -(eqP pn) Pos_to_nat0F.
  + exact: pos_nat_le.
- case: ZintP Zi'n' => [//|//|//|{i'}p' {}n' _ _ p'n' _ /=].
  rewrite !NegzE lerN2 lez_nat /Z.leb/= (pos_nat_compare pn p'n') eqSS.
  by case: eqP => [->/=| nn']; rewrite ?leqnn// ltnS leqNgt; case: ltnP.
Qed.

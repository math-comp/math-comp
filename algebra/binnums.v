(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import PosDef NatDef.
From Corelib Require Import IntDef.
From mathcomp Require Import RatDef.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From mathcomp Require Import ssralg ssrnum ssrint rat.

(******************************************************************************)
(* This file develops some link with binary numbers from Corelib, defining:   *)
(*     pos_nat == refinement relation between positive and nat                *)
(*        Nnat == refinement relation between N and nat                       *)
(*        Zint == refinement relation between Z and int                       *)
(*        Qrat == refinement relation between Q and rat                       *)
(* It also provides conversion functions int_of_Z and rat_of_Q, as well as    *)
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

Definition mask_nat m (n : nat) :=
  match m with
  | Pos.IsNul => n == 0
  | Pos.IsPos p => pos_nat p n
  | Pos.IsNeg => false
  end.

Lemma mask_nat_double_pred p n : pos_nat p n ->
  mask_nat (Pos.double_pred_mask p) n.-1.*2.
Proof.
by case: pos_natP => [//|//|{}p {}n _ _ pn _|{}p {}n _ _ pn _] /=;
  rewrite !pos_natE ?pos_nat_pred_double.
Qed.

Lemma mask_nat_double m n : mask_nat m n ->
  mask_nat (Pos.double_mask m) n.*2.
Proof. by case: m => [/eqP->//| p |//] /=; rewrite pos_natE. Qed.

Lemma mask_nat_succ_double m n : mask_nat m n ->
  mask_nat (Pos.succ_double_mask m) n.*2.+1.
Proof. by case: m => [/eqP->//| p |//] /=; rewrite pos_natE. Qed.

Lemma mask_natB p n (pn : pos_nat p n) p' n' (p'n' : pos_nat p' n') :
  (n' <= n)%N -> mask_nat (Pos.sub_mask p p') (n - n').
Proof.
suff: (n' <= n)%N -> (mask_nat (Pos.sub_mask p p') (n - n')%N
    /\ ((n' < n)%N -> mask_nat (Pos.sub_mask_carry p p') (n - n').-1)).
  by move=> /[apply] -[].
elim/pos_nat_ind: pn p' n' p'n' => [p' n' {p n} ||];
    [|move=> {}p {}n pn IH p' n'..].
- case: n' => [|n'] /[swap]; first by rewrite /pos_nat Pos_to_nat0F.
  rewrite ltnS leqn0 => /eqP->; rewrite subnn ltnn.
  case: pos_natP => [//|//|p n _ /eqP+ + _|p n _ /eqP+ + _].
    by rewrite -double0 neq_doubleS_double.
  by rewrite eqSS eq_sym double_eq0 => /eqP->; rewrite /pos_nat Pos_to_nat0F.
- case: pos_natP => [//|_ _ _|{}p' {}n' _ _ p'n' _|{}p' {}n' _ _ p'n' _] /=.
  + by rewrite subn1 pos_nat_pred_double// -double_pred mask_nat_double_pred.
  + rewrite leq_double => n'n; have [pp ppc] := IH _ _ p'n' n'n.
    rewrite -doubleB mask_nat_double//= ltn_double; split => [//| n'ltn].
    by rewrite -[(n - n')%N]prednK ?subn_gt0// doubleS mask_nat_succ_double?ppc.
  + rewrite ltn_double => n'n; have [pp ppc] := IH _ _ p'n' (ltnW n'n).
    rewrite subnS -doubleB -[(n - n')%N]prednK ?subn_gt0// doubleS.
    by rewrite mask_nat_succ_double ?mask_nat_double ?ppc.
- case: pos_natP => [//|_ _ _|{}p' {}n' _ _ p'n' _|{}p' {}n' _ _ p'n' _] /=.
  + by rewrite subn1 pos_natE pn pos_nat_pred_double.
  + rewrite leq_Sdouble => n'n; have [pp' pp'c] := IH _ _ p'n' n'n.
    rewrite subSn ?leq_double// -doubleB mask_nat_succ_double//=.
    by rewrite mask_nat_double.
  + rewrite ltnS leq_double => n'n; have [pp' pp'c] := IH _ _ p'n' n'n.
    rewrite subSS -doubleB mask_nat_double//; split=> [//|].
    rewrite ltnS ltn_double => n'ltn; rewrite -[(n - n')%N]prednK ?subn_gt0//.
    by rewrite doubleS mask_nat_succ_double ?pp'c.
Qed.

Lemma pos_natB p n (pn : pos_nat p n) p' n' (p'n' : pos_nat p' n') :
  (n' < n)%N -> pos_nat (Pos.sub p p') (n - n').
Proof.
move=> /[dup] /ltnW n'n; rewrite /Pos.sub.
case: Pos.sub_mask (mask_natB pn p'n' n'n) => [/=|//|//].
by rewrite -subn_gt0 => /eqP->.
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

Variant pos_nat_compare_spec (p p' : positive) :
    positive -> positive -> comparison -> Set :=
  | Pos_nat_compare_spec_Eq : pos_nat_compare_spec p p' p p Eq
  | Pos_nat_compare_spec_Lt :
      (Pos.to_nat p < Pos.to_nat p')%N -> pos_nat_compare_spec p p' p p' Lt
  | Pos_nat_compare_spec_Gt :
      (Pos.to_nat p' < Pos.to_nat p)%N -> pos_nat_compare_spec p p' p p' Gt.

Lemma pos_nat_compareP p p' : pos_nat_compare_spec p p' p p' (Pos.compare p p').
Proof.
have := pos_nat_compare (pos_nat_Pos_to_nat p) (pos_nat_Pos_to_nat p').
case: Pos.compare; [|do 2?[case: ifP => //]..] => [|+ _ _|/[swap]+ + _].
- by case: eqP => [/Pos_to_natI e _|]; [rewrite -{2}e; constructor|case: ifP].
- by constructor.
- by move=> e /negbT; rewrite -leqNgt leq_eqVlt eq_sym e/=; constructor.
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

Lemma Pos_to_natB i j : (Pos.to_nat j < Pos.to_nat i)%N ->
  Pos.to_nat (Pos.sub i j) = (Pos.to_nat i - Pos.to_nat j)%N.
Proof.
by move/(pos_natB (pos_nat_Pos_to_nat i) (pos_nat_Pos_to_nat j))/eqP.
Qed.

Definition Pos_to_natE := (Pos_to_nat1, Pos_to_nat_double, Pos_to_nat_doubleS,
  Pos_to_natS, Pos_to_natD, Pos_to_nat_pred_double, Pos_to_natM, Pos_to_natB).

Definition Nnat (i : N) (n : nat) := N.to_nat i == n.

Lemma Nnat_N_to_nat i : Nnat i (N.to_nat i). Proof. exact/eqP. Qed.

Variant Nnat_spec (i : N) (n : nat) : N -> nat -> bool -> Set :=
  | Nnat_spec_false : Nnat_spec i n i n false
  | Nnat_spec_N0 : i = N0 -> n = 0%N -> Nnat_spec i n N0 0%N true
  | Nnat_spec_Npos :
      forall p', i = Npos p' -> pos_nat p' n -> Nnat_spec i n (Npos p') n true.

Lemma NnatP i n : Nnat_spec i n i n (Nnat i n).
Proof.
case: (boolP (Nnat i n)) => /eqP Nin; last exact: Nnat_spec_false.
by case: i n Nin => [|p] n <- /=; [exact: Nnat_spec_N0|exact: Nnat_spec_Npos].
Qed.

Lemma Nnat0 : Nnat N0 0. Proof. by []. Qed.
Hint Resolve Nnat0 : core.

Lemma Nnat_pos p n : Nnat (Npos p) n = pos_nat p n. Proof. by []. Qed.

Definition NnatE := (Nnat0, Nnat_pos).

Lemma NnatD i n (Nin : Nnat i n) i' n' (Ni'n' : Nnat i' n') :
  Nnat (N.add i i') (n + n').
Proof.
case: NnatP Nin => [//|/[!add0n]//| {i}p _ pn _].
case: NnatP Ni'n' => [//|/[!addn0]//| {i'}p' _ p'n' _].
by rewrite Nnat_pos pos_natD.
Qed.

Lemma NnatM i n (Nin : Nnat i n) i' n' (Ni'n' : Nnat i' n') :
  Nnat (N.mul i i') (n * n').
Proof.
case: NnatP Nin => [//|/[!mul0n]//| {i}p _ pn _].
case: NnatP Ni'n' => [//|/[!muln0]//| {i'}p' _ p'n' _].
by rewrite Nnat_pos pos_natM.
Qed.

Lemma Nnat_eq i n (Nin : Nnat i n) i' n' (Ni'n' : Nnat i' n') :
  N.eqb i i' = (n == n').
Proof.
case: NnatP Nin => [//|_ _ _| {i}p _ pn _].
  by case: NnatP Ni'n' => [//|//| {i'}p' _ + _] => /pos_nat_exS[{}n'->].
case: NnatP Ni'n' => [//|_ _ _| {i'}p' _ p'n' _].
  by move: pn => /pos_nat_exS[{}n->].
exact: (pos_nat_eq pn p'n').
Qed.

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

Definition rat_of_Q (q : Q) : rat :=
  (int_of_Z (Qnum q))%:~R / (Pos.to_nat (Qden q))%:R.

Definition Qrat (q : Q) (r : rat) := rat_of_Q q == r.

Lemma Qrat_rat_of_Q q : Qrat q (rat_of_Q q). Proof. exact/eqP. Qed.
Hint Resolve Qrat_rat_of_Q : core.

Variant Qrat_spec (q : Q) (r : rat) : Prop :=
  Qrat_spec_Qmake n d
    of Zint (Qnum q) n & pos_nat (Qden q) d & r = n%:~R / d%:R.
Arguments Qrat_spec_Qmake {q r}.

Lemma QratP q r : reflect (Qrat_spec q r) (Qrat q r).
Proof.
apply/(iffP idP) => [/eqP<-{r}|]; first exact: Qrat_spec_Qmake.
by case=> _ _ /eqP<- /eqP<- ->.
Qed.

Lemma Qrat_spec_Q_to_rat q : Qrat_spec q (rat_of_Q q). Proof. exact/QratP. Qed.
Hint Resolve Qrat_spec_Q_to_rat : core.

Lemma Qrat0 : Qrat Q0 0. Proof. by []. Qed.
Hint Resolve Qrat0 : core.

Lemma Qrat1 : Qrat Q1 1. Proof. by []. Qed.
Hint Resolve Qrat0 : core.

Lemma Qrat_Qmake i n p d :
  Zint i n -> pos_nat p d -> Qrat (Qmake i p) (n%:~R / d%:R).
Proof. by move=> /eqP<- /eqP<-; rewrite /Qrat /rat_of_Q/=. Qed.

Lemma intr_pos_nat_neq0 {R : numDomainType} {p n} :
  pos_nat p n -> n%:R != 0 :> R.
Proof. by move=> /eqP<-; rewrite lt0r_neq0// ltr0n Pos_to_nat_gt0. Qed.

Lemma QratD q r (qr : Qrat q r) q' r' (q'r' : Qrat q' r') :
  Qrat (Qplus q q') (r + r').
Proof.
move: qr q'r' => /QratP[n d qn qd ->] /QratP[n' d' qn' qd' ->] {r r'}.
rewrite addf_div ?(intr_pos_nat_neq0 qd) ?(intr_pos_nat_neq0 qd')//.
rewrite !pmulrn -!rmorphM -rmorphD/= -pmulrn Qrat_Qmake ?pos_natM//.
by rewrite ZintD ?ZintM.
Qed.

Lemma QratM q r (qr : Qrat q r) q' r' (q'r' : Qrat q' r') :
  Qrat (Qmult q q') (r * r').
Proof.
move: qr q'r' => /QratP[n d qn qd ->] /QratP[n' d' qn' qd' ->] {r r'}.
by rewrite mulf_div -!rmorphM/= Qrat_Qmake ?ZintM ?pos_natM.
Qed.

Lemma QratN q r : Qrat q r -> Qrat (Qopp q) (- r).
Proof.
by move=> /QratP[n d qn dn ->] {r}; rewrite -mulNr -rmorphN/= Qrat_Qmake ?ZintN.
Qed.

Lemma QratB q r (qr : Qrat q r) q' r' (q'r' : Qrat q' r') :
  Qrat (Qminus q q') (r - r').
Proof. by rewrite QratD ?QratN. Qed.

Lemma QratV q r : Qrat q r -> Qrat (Qinv q) (r^-1).
Proof.
move=> /QratP[n d qn dn ->] {r}; rewrite invf_div /Qinv/=.
case: ZintP qn => [//|_ _ _|{}p {}n _ _ pn _|{}p {}n _ _ pn _]/=.
- by rewrite invr0 mulr0.
- by rewrite pmulrn -[n%:~R]pmulrn Qrat_Qmake.
- rewrite NegzE mulrNz divrN -mulNr nmulrn Qrat_Qmake//.
  by move: dn => /pos_nat_exS[{}d-> qd]; rewrite -NegzE Zint_neg.
Qed.

Lemma Qrat_eq q r (qr : Qrat q r) q' r' (q'r' : Qrat q' r') :
  Qeq_bool q q' = (r == r').
Proof.
move: qr q'r' => /QratP[n d qn qd ->] /QratP[n' d' qn' qd' ->] {r r'}.
rewrite eqr_div ?(intr_pos_nat_neq0 qd) ?(intr_pos_nat_neq0 qd')//.
by rewrite !pmulrn -!rmorphM/= eqr_int; apply: Zint_eq; apply: ZintM.
Qed.

Lemma Qrat_le q r (qr : Qrat q r) q' r' (q'r' : Qrat q' r') :
  Qle_bool q q' = (r <= r').
Proof.
move: qr q'r' => /QratP[n d qn qd ->] /QratP[n' d' qn' qd' ->] {r r'}.
rewrite ler_pdivrMr 1?mulrAC; last by rewrite ltr0n -(eqP qd) Pos_to_nat_gt0.
rewrite ler_pdivlMr; last by rewrite ltr0n -(eqP qd') Pos_to_nat_gt0//.
by rewrite !pmulrn -!rmorphM/= ler_int; apply: Zint_le; apply: ZintM.
Qed.

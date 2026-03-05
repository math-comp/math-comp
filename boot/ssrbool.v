From mathcomp Require Import ssreflect ssrfun.
From Corelib Require Export ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**********************)
(* not yet backported *)
(**********************)

Lemma homo_mono1 [aT rT : Type] [f : aT -> rT] [g : rT -> aT]
    [aP : pred aT] [rP : pred rT] :
  cancel g f ->
  {homo f : x / aP x >-> rP x} ->
  {homo g : x / rP x >-> aP x} -> {mono g : x / rP x >-> aP x}.
Proof. by move=> gK fP gP x; apply/idP/idP => [/fP|/gP//]; rewrite gK. Qed.

Lemma if_and b1 b2 T (x y : T) :
  (if b1 && b2 then x else y) = (if b1 then if b2 then x else y else y).
Proof. by case: b1 b2 => [] []. Qed.

Lemma if_or b1 b2 T (x y : T) :
  (if b1 || b2 then x else y) = (if b1 then x else if b2 then x else y).
Proof. by case: b1 b2 => [] []. Qed.

Lemma if_implyb b1 b2 T (x y : T) :
  (if b1 ==> b2 then x else y) = (if b1 then if b2 then x else y else x).
Proof. by case: b1 b2 => [] []. Qed.

Lemma if_implybC b1 b2 T (x y : T) :
  (if b1 ==> b2 then x else y) = (if b2 then x else if b1 then y else x).
Proof. by case: b1 b2 => [] []. Qed.

Lemma if_add b1 b2 T (x y : T) :
  (if b1 (+) b2 then x else y) = (if b1 then if b2 then y else x else if b2 then x else y).
Proof. by case: b1 b2 => [] []. Qed.

Lemma relpre_trans {T' T : Type} {leT : rel T} {f : T' -> T} :
  transitive leT -> transitive (relpre f leT).
Proof. by move=> + y x z; apply. Qed.

(* TODO: when backporting to Rocq, change the inductives `and3`, `and4`, `and5`
   to records *)

Definition and3proj1 (P1 P2 P3 : Prop) (a : [/\ P1, P2 & P3]) :=
  let: And3 p1 p2 p3 := a in p1.

Definition and3proj2 (P1 P2 P3 : Prop) (a : [/\ P1, P2 & P3]) :=
  let: And3 p1 p2 p3 := a in p2.

Definition and3proj3 (P1 P2 P3 : Prop) (a : [/\ P1, P2 & P3]) :=
  let: And3 p1 p2 p3 := a in p3.

Definition and4proj1 (P1 P2 P3 P4 : Prop) (a : [/\ P1, P2, P3 & P4]) :=
  let: And4 p1 p2 p3 p4 := a in p1.

Definition and4proj2 (P1 P2 P3 P4 : Prop) (a : [/\ P1, P2, P3 & P4]) :=
  let: And4 p1 p2 p3 p4 := a in p2.

Definition and4proj3 (P1 P2 P3 P4 : Prop) (a : [/\ P1, P2, P3 & P4]) :=
  let: And4 p1 p2 p3 p4 := a in p3.

Definition and4proj4 (P1 P2 P3 P4 : Prop) (a : [/\ P1, P2, P3 & P4]) :=
  let: And4 p1 p2 p3 p4 := a in p4.

Definition and5proj1 (P1 P2 P3 P4 P5 : Prop) (a : [/\ P1, P2, P3, P4 & P5]) :=
  let: And5 p1 p2 p3 p4 p5 := a in p1.

Definition and5proj2 (P1 P2 P3 P4 P5 : Prop) (a : [/\ P1, P2, P3, P4 & P5]) :=
  let: And5 p1 p2 p3 p4 p5 := a in p2.

Definition and5proj3 (P1 P2 P3 P4 P5 : Prop) (a : [/\ P1, P2, P3, P4 & P5]) :=
  let: And5 p1 p2 p3 p4 p5 := a in p3.

Definition and5proj4 (P1 P2 P3 P4 P5 : Prop) (a : [/\ P1, P2, P3, P4 & P5]) :=
  let: And5 p1 p2 p3 p4 p5 := a in p4.

Definition and5proj5 (P1 P2 P3 P4 P5 : Prop) (a : [/\ P1, P2, P3, P4 & P5]) :=
  let: And5 p1 p2 p3 p4 p5 := a in p5.

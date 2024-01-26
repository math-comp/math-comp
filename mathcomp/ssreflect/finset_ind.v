(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat div seq.
From mathcomp Require Import fintype bigop finset.
Require Import Coq.Program.Wf.

(******************************************************************************)
(* This file defines induction principles for finite sets based on their      *)
(* cardinality:                                                               *)
(*                                                                            *)
(* card_rect, card_ind, card_rec:       increasing induction on cardinality   *)
(*                                                                            *)
(*             (forall A, (forall B, #|B| < #|A| -> P B) -> P A)              *)
(*           -----------------------------------------------------            *)
(*                              forall A, P A                                 *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(* card2_rect, card2_ind, card2_rec:    decreasing induction on cardinality   *)
(*                                                                            *)
(*             (forall A, (forall B, #|B| > #|A| -> P B) -> P A)              *)
(*           -----------------------------------------------------            *)
(*                              forall A, P A                                 *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(* subset_rect, subset_ind, subset_rec:     increasing induction on subsets   *)
(*                                                                            *)
(*             (forall A, (forall B, B \proper A -> P B) -> P A)              *)
(*           -----------------------------------------------------            *)
(*                              forall A, P A                                 *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(* subset2_rect, subset2_ind, subset2_rec:  decreasing induction on subsets   *)
(*                                                                            *)
(*             (forall A, (forall B, A \proper B -> P B) -> P A)              *)
(*           -----------------------------------------------------            *)
(*                              forall A, P A                                 *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section CardInduction.

Context {T : finType}.
Implicit Type A B : {set T}.

Section CardRectDef.
Context {P : {set T} -> Type}.
Variable HA : forall A, (forall B, (#|B| < #|A|)%coq_nat -> P B) -> P A.

Program Fixpoint card_rect_coq_nat (A : {set T}) {measure #|A|} : P A
  := HA card_rect_coq_nat.
End CardRectDef.

Definition card_rect {P} (H : forall A : {set T}, (forall B : {set T}, #|B| < #|A| -> P B) -> P A) A :=
  card_rect_coq_nat (fun A0 HB0 => H A0 (fun B H => HB0 B (elimTF ltP H))) A.
Definition card_ind {P : _ -> Prop} := @card_rect P.
Definition card_rec {P : _ -> Set} := @card_rect P.

Section Card2RectDef.
Context {P : {set T} -> Type}.
Variable HA : forall A, (forall B, (#|B| > #|A|)%coq_nat -> P B) -> P A.

Program Fixpoint card2_rect_coq_nat (A : {set T}) {measure (#|T|.+1 - #|A|)%N} : P A
  := HA (fun B _ => card2_rect_coq_nat B).
Next Obligation.
apply/ltP ; apply: ltn_sub2l ; last by apply/ltP.
by rewrite ltnS ; exact: max_card.
Qed.
End Card2RectDef.

Definition card2_rect {P} (H : forall A : {set T}, (forall B : {set T}, #|B| > #|A| -> P B) -> P A) A : P A :=
  card2_rect_coq_nat (fun A0 HB0 => H A0 (fun B H => HB0 B (elimTF ltP H))) A.
Definition card2_ind {P : _ -> Prop} := @card2_rect P.
Definition card2_rec {P : _ -> Set} := @card2_rect P.

End CardInduction.

Section SubsetInduction.

Context {T : finType}.
Implicit Type A B : {set T}.

Section SubsetRectDef.
Context {P : {set T} -> Type}.
Variable HA : forall A, (forall B, B \proper A -> P B) -> P A.

Program Fixpoint subset_rect (A : {set T}) {measure #|A|} : P A
  := HA (fun B HB => subset_rect B (recproof:= ltP (proper_card HB))).
End SubsetRectDef.

Definition subset_ind {P : _ -> Prop} := @subset_rect P.
Definition subset_rec {P : _ -> Set} := @subset_rect P.

Section Subset2RectDef.
Context {P : {set T} -> Type}.
Variable HA : forall A, (forall B, A \proper B -> P B) -> P A.

Program Fixpoint subset2_rect (A : {set T}) {measure (#|T|.+1 - #|A|)} : P A
  := HA (fun B _ => subset2_rect B).
Next Obligation.
apply/ltP ; apply: ltn_sub2l ; last exact: proper_card.
by rewrite ltnS ; exact: max_card.
Qed.
End Subset2RectDef.
Definition subset2_ind {P : _ -> Prop} := @subset_rect P.
Definition subset2_rec {P : _ -> Set} := @subset_rect P.

End SubsetInduction.

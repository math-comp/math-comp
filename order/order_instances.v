(* (c) Copyright 2006-2019 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype tuple.
From mathcomp Require Import preorder porder lattice lattice_instances.
From mathcomp Require Import total_order total_order_instances.
From mathcomp Require Import complemented_lattice.
From mathcomp Require Import complemented_lattice_instances.

(******************************************************************************)
(*                       Instances of order structures                        *)
(*                                                                            *)
(* NB: See the header of order.v for general remarks about the preorder and   *)
(*     order structures in MathComp, and the files in this directory.         *)
(*                                                                            *)
(* We provide aliases for various types and their displays:                   *)
(*              T^d  := dual T,                                               *)
(*                      where dual is a new definition for (fun T => T)       *)
(*                      (associated with dual_display d where d is a display) *)
(*                   == an alias for T, such that if T is canonically         *)
(*                      ordered, then T^d is canonically ordered with the     *)
(*                      dual order, and displayed with an extra ^d in the     *)
(*                      notation, i.e.,  <=^d, <^d, >=<^d, ><^d, `&`^d, `|`^d *)
(*                      are used and displayed instead of                     *)
(*                      <=, <, >=<, ><, `&`, `|`                              *)
(* n.-tuplelexi[d] T == n.-tuple T                                            *)
(*                   == an alias for tuple, such that if T is canonically     *)
(*                      ordered, then n.-tuplelexi[d] T is canonically        *)
(*                      ordered in lexicographic order, i.e.,                 *)
(*                      [:: x1, .., xn] <= [y1, .., yn] =                     *)
(*                        (x1 <= x2) && ((x1 >= y1) ==> ((x2 <= y2) && ...))  *)
(*                      and displayed in display d                            *)
(*    n.-tuplelexi T := n.-tuplelexi[seqlexi_display d] T                     *)
(*                      where d is the display of T                           *)
(*                                                                            *)
(* We provide expected instances of ordered types for bool,                   *)
(* n.-tuplelexi[d] T (with lexicographic ordering), and all possible finite   *)
(* type instances.                                                            *)
(* (Use `HB.about type` to discover the instances on type.)                   *)
(*                                                                            *)
(* In order to get a canonical lexicographic order on tuple, one may import   *)
(* DefaultTupleLexiOrder.                                                     *)
(*                                                                            *)
(* Acknowledgments: The files in this directory are based on prior work by    *)
(* D. Dreyer, G. Gonthier, A. Nanevski, P-Y Strub, B. Ziliani                 *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope order_scope.

Module Order.

Export total_order.Order complemented_lattice.Order.
Import total_order.Order.Theory complemented_lattice.Order.Theory.

Module ProdLexiTheory.

Lemma sub_prod_lexi (d1 d2 d3 d4 : disp_t)
  (T1 : preorderType d1) (T2 : preorderType d2) :
  subrel (<=%O : rel (T1 *prod[d3] T2)) (<=%O : rel (T1 *lexi[d4] T2)).
Proof.
case=> [x1 x2] [y1 y2]; rewrite leEprod leEprodlexi /= => /andP[] -> ->.
exact: implybT.
Qed.

Lemma sub_seqprod_lexi (d1 d2 d3 : disp_t) (T : preorderType d1) :
   subrel (<=%O : rel (seqprod_with d2 T)) (<=%O : rel (seqlexi_with d3 T)).
Proof.
elim=> [|x1 s1 ihs1] [|x2 s2]//=; rewrite le_cons lexi_cons /=.
by move=> /andP[-> /ihs1->]; rewrite implybT.
Qed.

End ProdLexiTheory.
HB.export ProdLexiTheory.

(*********************)
(* Instances on bool *)
(*********************)

Module BoolOrder.
Section BoolOrder.
Implicit Types (x y : bool).

Fact bool_display : disp_t. Proof. exact. Qed.

Fact ltb_def x y : (x < y)%N = (y != x) && (x <= y)%N.
Proof. by case: x y => [] []. Qed.

Fact leb_refl : reflexive (leq : rel bool).
Proof. by case. Qed.

Fact leb_anti : antisymmetric (leq : rel bool).
Proof. by case=> [] []. Qed.

Fact leb_trans : transitive (leq : rel bool).
Proof. exact: leq_trans. Qed.

Fact leb_andb x y z : (x <= y && z)%N = (x <= y)%N && (x <= z)%N.
Proof. by case: x y z => [] [] []. Qed.

Fact le_orb_b x y z : (x || y <= z)%N = (x <= z)%N && (y <= z)%N.
Proof. by case: x y z => [] [] []. Qed.

#[export] HB.instance Definition _ :=
  isPOrder.Build bool_display bool ltb_def leb_refl leb_anti leb_trans.
#[export] HB.instance Definition _ := @hasBottom.Build _ bool false leq0n.
#[export] HB.instance Definition _ := @hasTop.Build _ bool true leq_b1.
#[export] HB.instance Definition _ :=
  @POrder_MeetJoin_isLattice.Build _ bool andb orb leb_andb le_orb_b.
#[export] HB.instance Definition _ := Lattice_isTotal.Build _ bool leq_total.
#[export] HB.instance Definition _ :=
  TBDistrLattice_hasComplement.Build _ bool orbN andbN.

Lemma leEbool : le = (leq : rel bool). Proof. by []. Qed.
Lemma ltEbool x y : (x < y) = (x < y)%N. Proof. by []. Qed.
Lemma andEbool : meet = andb. Proof. by []. Qed.
Lemma orEbool : meet = andb. Proof. by []. Qed.
Lemma subEbool x y : x `\` y = x && ~~ y. Proof. by []. Qed.
Lemma complEbool : compl = negb. Proof. by []. Qed.

End BoolOrder.
Module Exports.
HB.reexport BoolOrder.
Definition leEbool := leEbool.
Definition ltEbool := ltEbool.
Definition andEbool := andEbool.
Definition orEbool := orEbool.
Definition subEbool := subEbool.
Definition complEbool := complEbool.
End Exports.
End BoolOrder.
HB.export BoolOrder.Exports.

(*********************************************)
(* We declare an alias of the tuples,        *)
(* which has canonical lexicographic order.  *)
(*********************************************)

Module TupleLexiOrder.
Section TupleLexiOrder.
Import DefaultSeqLexiOrder.

Definition type (disp : disp_t) n T := n.-tuple T.
Definition type_ (disp : disp_t) n (T : preorderType disp) :=
  type (Order.seqlexi_display disp) n T.

Context {disp disp' : disp_t}.
Local Notation "n .-tuple" := (type disp' n) : type_scope.

Section Basics.
Context (n : nat).
#[export] HB.instance Definition _ (T : eqType) := Equality.on (n.-tuple T).
#[export] HB.instance Definition _ (T : choiceType) :=
  SubChoice.on (n.-tuple T).
#[export] HB.instance Definition _ (T : countType) :=
  SubCountable.on (n.-tuple T).
#[export] HB.instance Definition _ (T : finType) :=
  SubFinite.on (n.-tuple T).
End Basics.

Section Preorder.
Implicit Types (T : preorderType disp).

#[export]
HB.instance Definition _ n T :=
  [SubChoice_isSubPreorder of n.-tuple T by <: with disp'].

End Preorder.

Lemma sub_tprod_lexi d n (T : preorderType disp) :
   subrel (<=%O : rel (n.-tupleprod[d] T)) (<=%O : rel (n.-tuple T)).
Proof. exact: sub_seqprod_lexi. Qed.

Section BPreorder.
Context (n : nat) (T : bPreorderType disp).
Implicit Types (t : n.-tuple T).

Fact le0x t : [tuple \bot | _ < n] <= t :> n.-tuple T.
Proof. by apply: sub_seqprod_lexi; apply: le0x (t : n.-tupleprod T). Qed.

#[export] HB.instance Definition _ := hasBottom.Build _ (n.-tuple T) le0x.

Lemma botEtlexi : \bot = [tuple \bot | _ < n] :> n.-tuple T. Proof. by []. Qed.

End BPreorder.

Section TPreorder.
Context (n : nat) (T : tPreorderType disp).
Implicit Types (t : n.-tuple T).

Fact lex1 t : t <= [tuple \top | _ < n].
Proof. by apply: sub_seqprod_lexi; apply: lex1 (t : n.-tupleprod T). Qed.

#[export] HB.instance Definition _ := hasTop.Build _ (n.-tuple T) lex1.

Lemma topEtlexi : \top = [tuple \top | _ < n] :> n.-tuple T. Proof. by []. Qed.

End TPreorder.

Section POrder.
Implicit Types (n : nat) (T : porderType disp).

#[export] HB.instance Definition _ n T :=
  [SubChoice_isSubPOrder of n.-tuple T by <: with disp'].

Lemma lexi_tupleP n T (t1 t2 : n.-tuple T) :
   reflect (exists k : 'I_n.+1, forall i : 'I_n, (i <= k)%N ->
               tnth t1 i <= tnth t2 i ?= iff (i != k :> nat)) (t1 <= t2).
Proof.
elim: n => [|n IHn] in t1 t2 *.
  by rewrite tuple0 [t2]tuple0/= lexx; constructor; exists ord0 => -[].
case: (tupleP t1) (tupleP t2) => [x1 {}t1] [x2 {}t2].
rewrite [_ <= _]lexi_cons; apply: (iffP idP) => [|[k leif_xt12]].
  case: comparableP => //= [ltx12 _|-> /IHn[k kP]].
    exists ord0 => i; rewrite leqn0 => /eqP/(@ord_inj n.+1 i ord0)->.
    by apply/leifP; rewrite !tnth0.
  exists (lift ord0 k) => i; case: (unliftP ord0 i) => [j ->|-> _].
    by rewrite !ltnS => /kP; rewrite !tnthS.
  by apply/leifP; rewrite !tnth0 eqxx.
have /= := leif_xt12 ord0 isT; rewrite !tnth0 => leif_x12.
rewrite leif_x12/=; move: leif_x12 leif_xt12 => /leifP.
case: (unliftP ord0 k) => {k} [k-> /eqP<-{x2}|-> /lt_geF->//] leif_xt12.
rewrite lexx implyTb; apply/IHn; exists k => i le_ik.
by have := leif_xt12 (lift ord0 i) le_ik; rewrite !tnthS.
Qed.

Lemma ltxi_tupleP n T (t1 t2 : n.-tuple T) :
   reflect (exists k : 'I_n, forall i : 'I_n, (i <= k)%N ->
               tnth t1 i <= tnth t2 i ?= iff (i != k :> nat)) (t1 < t2).
Proof.
elim: n => [|n IHn] in t1 t2 *.
  by rewrite tuple0 [t2]tuple0/= ltxx; constructor => - [] [].
case: (tupleP t1) (tupleP t2) => [x1 {}t1] [x2 {}t2].
rewrite [_ < _]ltxi_cons; apply: (iffP idP) => [|[k leif_xt12]].
  case: (comparableP x1 x2) => //= [ltx12 _|-> /IHn[k kP]].
    exists ord0 => i; rewrite leqn0 => /eqP/(@ord_inj n.+1 i ord0)->.
    by apply/leifP; rewrite !tnth0.
  exists (lift ord0 k) => i; case: (unliftP ord0 i) => {i} [i ->|-> _].
    by rewrite !ltnS => /kP; rewrite !tnthS.
  by apply/leifP; rewrite !tnth0 eqxx.
have /= := leif_xt12 ord0 isT; rewrite !tnth0 => leif_x12.
rewrite leif_x12/=; move: leif_x12 leif_xt12 => /leifP.
case: (unliftP ord0 k) => {k} [k-> /eqP<-{x2}|-> /lt_geF->//] leif_xt12.
rewrite lexx implyTb; apply/IHn; exists k => i le_ik.
by have := leif_xt12 (lift ord0 i) le_ik; rewrite !tnthS.
Qed.

Lemma ltxi_tuplePlt n T (t1 t2 : n.-tuple T) : reflect
  (exists2 k : 'I_n, forall i : 'I_n, (i < k)%N -> tnth t1 i = tnth t2 i
                                                 & tnth t1 k < tnth t2 k)
  (t1 < t2).
Proof.
apply: (iffP (ltxi_tupleP _ _)) => [[k kP]|[k kP ltk12]].
  exists k => [i i_lt|]; last by rewrite (lt_leif (kP _ _)) ?eqxx ?leqnn.
  by have /eqTleif->// := kP i (ltnW i_lt); rewrite ltn_eqF.
by exists k => i; case: ltngtP => //= [/kP-> _|/ord_inj-> _]; apply/leifP.
Qed.

End POrder.

#[export] HB.instance Definition _ n (T : orderType disp) :=
  [SubChoice_isSubOrder of n.-tuple T by <: with disp'].

(* FIXME: use HB.saturate *)
#[export] HB.instance Definition _ (n : nat) (T : tbPreorderType disp) :=
  Preorder.on (n.-tuple T).
#[export] HB.instance Definition _ (n : nat) (T : bPOrderType disp) :=
  POrder.on (n.-tuple T).
#[export] HB.instance Definition _ (n : nat) (T : tPOrderType disp) :=
  POrder.on (n.-tuple T).
#[export] HB.instance Definition _ (n : nat) (T : tbPOrderType disp) :=
  POrder.on (n.-tuple T).
#[export] HB.instance Definition _ (n : nat) (T : bOrderType disp) :=
  POrder.on (n.-tuple T).
#[export] HB.instance Definition _ (n : nat) (T : tOrderType disp) :=
  POrder.on (n.-tuple T).
#[export] HB.instance Definition _ (n : nat) (T : tbOrderType disp) :=
  POrder.on (n.-tuple T).
#[export] HB.instance Definition _ (n : nat) (T : finPreorderType disp) :=
  Preorder.on (n.-tuple T).
#[export] HB.instance Definition _ (n : nat) (T : finBPreorderType disp) :=
  Preorder.on (n.-tuple T).
#[export] HB.instance Definition _ (n : nat) (T : finTPreorderType disp) :=
  Preorder.on (n.-tuple T).
#[export] HB.instance Definition _ (n : nat) (T : finTBPreorderType disp) :=
  Preorder.on (n.-tuple T).
#[export] HB.instance Definition _ (n : nat) (T : finPOrderType disp) :=
  POrder.on (n.-tuple T).
#[export] HB.instance Definition _ (n : nat) (T : finBPOrderType disp) :=
  POrder.on (n.-tuple T).
#[export] HB.instance Definition _ (n : nat) (T : finTPOrderType disp) :=
  POrder.on (n.-tuple T).
#[export] HB.instance Definition _ (n : nat) (T : finTBPOrderType disp) :=
  POrder.on (n.-tuple T).
#[export] HB.instance Definition _ (n : nat) (T : finOrderType disp) :=
  POrder.on (n.-tuple T).
#[export] HB.instance Definition _ (n : nat) (T : finTBOrderType disp) :=
  POrder.on (n.-tuple T).
(* /FIXME *)

End TupleLexiOrder.

Module Exports.

HB.reexport TupleLexiOrder.

Notation "n .-tuplelexi[ disp ]" := (type disp n)
  (format "n .-tuplelexi[ disp ]") : type_scope.
Notation "n .-tuplelexi" := (type_ n)
  (format "n .-tuplelexi") : type_scope.

Definition topEtlexi := @topEtlexi.
Definition botEtlexi := @botEtlexi.
Definition sub_tprod_lexi := @sub_tprod_lexi.
Definition lexi_tupleP := @lexi_tupleP.
Arguments lexi_tupleP {disp disp' n T t1 t2}.
Definition ltxi_tupleP := @ltxi_tupleP.
Arguments ltxi_tupleP {disp disp' n T t1 t2}.
Definition ltxi_tuplePlt := @ltxi_tuplePlt.
Arguments ltxi_tuplePlt {disp disp' n T t1 t2}.

End Exports.
End TupleLexiOrder.
HB.export TupleLexiOrder.Exports.

Module DefaultTupleLexiOrder.
Section DefaultTupleLexiOrder.
Context {disp : disp_t}.

Notation "n .-tuplelexi" := n.-tuplelexi[Order.seqlexi_display disp].

HB.instance Definition _ n (T : preorderType disp) :=
  Preorder.copy (n.-tuple T) (n.-tuplelexi T).
HB.instance Definition _ n (T : bPreorderType disp) :=
  BPreorder.copy (n.-tuple T) (n.-tuplelexi T).
HB.instance Definition _ n (T : tPreorderType disp) :=
  TPreorder.copy (n.-tuple T) (n.-tuplelexi T).
HB.instance Definition _ n (T : tbPreorderType disp) :=
  TBPreorder.copy (n.-tuple T) (n.-tuplelexi T).
HB.instance Definition _ n (T : porderType disp) :=
  POrder.copy (n.-tuple T) (n.-tuplelexi T).
HB.instance Definition _ n (T : bPOrderType disp) :=
  BPOrder.copy (n.-tuple T) (n.-tuplelexi T).
HB.instance Definition _ n (T : tPOrderType disp) :=
  TPOrder.copy (n.-tuple T) (n.-tuplelexi T).
HB.instance Definition _ n (T : tbPOrderType disp) :=
  TBPOrder.copy (n.-tuple T) (n.-tuplelexi T).
HB.instance Definition _ n (T : orderType disp) :=
  Lattice.copy (n.-tuple T) (n.-tuplelexi T).
HB.instance Definition _ n (T : orderType disp) :=
  DistrLattice.copy (n.-tuple T) (n.-tuplelexi T).
HB.instance Definition _ n (T : orderType disp) :=
  Total.copy (n.-tuple T) (n.-tuplelexi T).
HB.instance Definition _ n (T : bOrderType disp) :=
  BTotal.copy (n.-tuple T) (n.-tuplelexi T).
HB.instance Definition _ n (T : tOrderType disp) :=
  TTotal.copy (n.-tuple T) (n.-tuplelexi T).
HB.instance Definition _ n (T : tbOrderType disp) :=
  TBTotal.copy (n.-tuple T) (n.-tuplelexi T).
HB.instance Definition _ n (T : finPreorderType disp) :=
  FinPreorder.copy (n.-tuple T) (n.-tuplelexi T).
HB.instance Definition _ n (T : finBPreorderType disp) :=
  FinBPreorder.copy (n.-tuple T) (n.-tuplelexi T).
HB.instance Definition _ n (T : finTPreorderType disp) :=
  FinTPreorder.copy (n.-tuple T) (n.-tuplelexi T).
HB.instance Definition _ n (T : finTBPreorderType disp) :=
  FinTBPreorder.copy (n.-tuple T) (n.-tuplelexi T).
HB.instance Definition _ n (T : finPOrderType disp) :=
  FinPOrder.copy (n.-tuple T) (n.-tuplelexi T).
HB.instance Definition _ n (T : finBPOrderType disp) :=
  FinBPOrder.copy (n.-tuple T) (n.-tuplelexi T).
HB.instance Definition _ n (T : finTPOrderType disp) :=
  FinTPOrder.copy (n.-tuple T) (n.-tuplelexi T).
HB.instance Definition _ n (T : finTBPOrderType disp) :=
  FinTBPOrder.copy (n.-tuple T) (n.-tuplelexi T).
HB.instance Definition _ n (T : finOrderType disp) :=
  FinTotal.copy (n.-tuple T) (n.-tuplelexi T).
HB.instance Definition _ n (T : finTBOrderType disp) :=
  FinTBTotal.copy (n.-tuple T) (n.-tuplelexi T).

End DefaultTupleLexiOrder.
End DefaultTupleLexiOrder.

Module Exports.
HB.reexport.
End Exports.

End Order.

Export Order.Exports.

Module DefaultTupleLexiOrder := Order.DefaultTupleLexiOrder.

From mathcomp Require Import ssreflect.
From Coq Require Export ssrfun.
From mathcomp Require Export ssrnotations.

Definition injective2 (rT aT1 aT2 : Type) (f : aT1 -> aT2 -> rT) :=
  forall (x1 x2 : aT1) (y1 y2 : aT2), f x1 y1 = f x2 y2 -> (x1 = x2) * (y1 = y2).

Arguments injective2 [rT aT1 aT2] f.

(*******************)
(* v8.17 additions *)
(*******************)

(******************************************************************************)
(*                oflit f := Some \o f                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition olift aT rT (f : aT -> rT) := Some \o f.

Lemma obindEapp {aT rT} (f : aT -> option rT) : obind f = oapp f None.
Proof. by []. Qed.

Lemma omapEbind {aT rT} (f : aT -> rT) : omap f = obind (olift f).
Proof. by []. Qed.

Lemma omapEapp {aT rT} (f : aT -> rT) : omap f = oapp (olift f) None.
Proof. by []. Qed.

Lemma oappEmap {aT rT} (f : aT -> rT) (y0 : rT) x :
  oapp f y0 x = odflt y0 (omap f x).
Proof. by case: x. Qed.

Lemma omap_comp aT rT sT (f : aT -> rT) (g : rT -> sT) :
  omap (g \o f) =1 omap g \o omap f.
Proof. by case. Qed.

Lemma oapp_comp aT rT sT (f : aT -> rT) (g : rT -> sT) x :
  oapp (g \o f) x =1 (@oapp _ _)^~ x g \o omap f.
Proof. by case. Qed.

Lemma oapp_comp_f {aT rT sT} (f : aT -> rT) (g : rT -> sT) (x : rT) :
  oapp (g \o f) (g x) =1 g \o oapp f x.
Proof. by case. Qed.

Lemma olift_comp aT rT sT (f : aT -> rT) (g : rT -> sT) :
  olift (g \o f) = olift g \o f.
Proof. by []. Qed.

Lemma compA {A B C D : Type} (f : B -> A) (g : C -> B) (h : D -> C) :
  f \o (g \o h) = (f \o g) \o h.
Proof. by []. Qed.

Lemma ocan_comp [A B C : Type] [f : B -> option A] [h : C -> option B]
    [f' : A -> B] [h' : B -> C] :
  ocancel f f' -> ocancel h h' -> ocancel (obind f \o h) (h' \o f').
Proof.
move=> fK hK c /=; rewrite -[RHS]hK/=; case hcE : (h c) => [b|]//=.
by rewrite -[b in RHS]fK; case: (f b) => //=; have := hK c; rewrite hcE.
Qed.

(*******************)
(* v8.18 additions *)
(*******************)

(* this change of order has also been PRed to Coq PR 17249 *)
Notation "@ 'sval'" := (@proj1_sig) (at level 10, format "@ 'sval'").
Notation sval := (@proj1_sig _ _).

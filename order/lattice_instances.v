(* (c) Copyright 2006-2019 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import div bigop prime preorder porder lattice.

(******************************************************************************)
(*                    Instances of the lattice structures                     *)
(*                                                                            *)
(* NB: See CONTRIBUTING.md for an introduction to HB concepts and commands.   *)
(*                                                                            *)
(* NB: See the header of order.v for general remarks about the preorder and   *)
(*     order structures in MathComp, and the files in this directory.         *)
(*                                                                            *)
(* We provide aliases for various types and their displays:                   *)
(*            natdvd := nat (associated with display dvd_display)             *)
(*                   == an alias for nat which is canonically ordered using   *)
(*                      divisibility predicate dvdn                           *)
(*                      Notation %|, %<|, gcd, lcm are used instead of        *)
(*                      <=, <, meet and join.                                 *)
(*  seqprod_with d T := seq T                                                 *)
(*                   == an alias for seq, such that if T is canonically       *)
(*                      ordered, then seqprod_with d T is canonically ordered *)
(*                      in product order, i.e.,                               *)
(*                      [:: x1, .., xn] <= [y1, .., yn] =                     *)
(*                        (x1 <= y1) && ... && (xn <= yn)                     *)
(*                      and displayed in display d                            *)
(*         seqprod T := seqprod_with (seqprod_display d) T                    *)
(*                      where d is the display of T, and seqprod_display adds *)
(*                      an extra ^sp to all notations                         *)
(*                                                                            *)
(* We provide expected lattice instances on natdvd (for dvdn) and             *)
(* seqprod_with d T (using product order).                                    *)
(* (Use `HB.about type` to discover the instances on type.)                   *)
(*                                                                            *)
(* In order to get the canonical product order on seq, one may import         *)
(* DefaultSeqProdOrder.                                                       *)
(*                                                                            *)
(* Acknowledgments: The files in this directory are based on prior work by    *)
(* D. Dreyer, G. Gonthier, A. Nanevski, P-Y Strub, B. Ziliani                 *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope order_scope.

(* Reserved notations for divisibility *)
Reserved Notation "x %<| y"  (at level 70, no associativity).

Reserved Notation "\gcd_ i F"
  (at level 34, F at level 41, i at level 0,
           format "'[' \gcd_ i '/  '  F ']'").
Reserved Notation "\gcd_ ( i <- r | P ) F"
  (at level 34, F at level 41, i, r at level 60,
           format "'[' \gcd_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\gcd_ ( i <- r ) F"
  (F at level 41,
           format "'[' \gcd_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\gcd_ ( m <= i < n | P ) F"
  (F at level 41, i, n at level 60,
           format "'[' \gcd_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\gcd_ ( m <= i < n ) F"
  (F at level 41,
           format "'[' \gcd_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\gcd_ ( i | P ) F"
  (F at level 41,
           format "'[' \gcd_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\gcd_ ( i : t | P ) F" (F at level 41).
Reserved Notation "\gcd_ ( i : t ) F" (F at level 41).
Reserved Notation "\gcd_ ( i < n | P ) F"
  (F at level 41, n at level 60,
           format "'[' \gcd_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\gcd_ ( i < n ) F"
  (F at level 41,
           format "'[' \gcd_ ( i  <  n )  F ']'").
Reserved Notation "\gcd_ ( i 'in' A | P ) F"
  (F at level 41, A at level 60,
           format "'[' \gcd_ ( i  'in'  A  |  P ) '/  '  F ']'").
Reserved Notation "\gcd_ ( i 'in' A ) F"
  (F at level 41,
           format "'[' \gcd_ ( i  'in'  A ) '/  '  F ']'").

Reserved Notation "\lcm_ i F"
  (at level 34, F at level 41, i at level 0,
           format "'[' \lcm_ i '/  '  F ']'").
Reserved Notation "\lcm_ ( i <- r | P ) F"
  (at level 34, F at level 41, i, r at level 60,
           format "'[' \lcm_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\lcm_ ( i <- r ) F"
  (F at level 41,
           format "'[' \lcm_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\lcm_ ( m <= i < n | P ) F"
  (F at level 41, i, n at level 60,
           format "'[' \lcm_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\lcm_ ( m <= i < n ) F"
  (F at level 41,
           format "'[' \lcm_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\lcm_ ( i | P ) F"
  (F at level 41,
           format "'[' \lcm_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\lcm_ ( i : t | P ) F" (F at level 41).
Reserved Notation "\lcm_ ( i : t ) F" (F at level 41).
Reserved Notation "\lcm_ ( i < n | P ) F"
  (F at level 41, n at level 60,
           format "'[' \lcm_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\lcm_ ( i < n ) F"
  (F at level 41,
           format "'[' \lcm_ ( i  <  n )  F ']'").
Reserved Notation "\lcm_ ( i 'in' A | P ) F"
  (F at level 41, A at level 60,
           format "'[' \lcm_ ( i  'in'  A  |  P ) '/  '  F ']'").
Reserved Notation "\lcm_ ( i 'in' A ) F"
  (F at level 41,
           format "'[' \lcm_ ( i  'in'  A ) '/  '  F ']'").

(* Reserved notations for product ordering of seq *)
Reserved Notation "x <=^sp y" (at level 70, y at next level).
Reserved Notation "x >=^sp y" (at level 70, y at next level).
Reserved Notation "x <^sp y" (at level 70, y at next level).
Reserved Notation "x >^sp y" (at level 70, y at next level).
Reserved Notation "x <=^sp y :> T" (at level 70, y at next level).
Reserved Notation "x >=^sp y :> T" (at level 70, y at next level).
Reserved Notation "x <^sp y :> T" (at level 70, y at next level).
Reserved Notation "x >^sp y :> T" (at level 70, y at next level).
Reserved Notation "<=^sp y" (at level 35).
Reserved Notation ">=^sp y" (at level 35).
Reserved Notation "<^sp y" (at level 35).
Reserved Notation ">^sp y" (at level 35).
Reserved Notation "<=^sp y :> T" (at level 35, y at next level).
Reserved Notation ">=^sp y :> T" (at level 35, y at next level).
Reserved Notation "<^sp y :> T" (at level 35, y at next level).
Reserved Notation ">^sp y :> T" (at level 35, y at next level).
Reserved Notation "x >=<^sp y" (at level 70, no associativity).
Reserved Notation ">=<^sp x" (at level 35).
Reserved Notation ">=<^sp y :> T" (at level 35, y at next level).
Reserved Notation "x ><^sp y" (at level 70, no associativity).
Reserved Notation "><^sp x" (at level 35).
Reserved Notation "><^sp y :> T" (at level 35, y at next level).

Reserved Notation "x <=^sp y <=^sp z" (at level 70, y, z at next level).
Reserved Notation "x <^sp y <=^sp z" (at level 70, y, z at next level).
Reserved Notation "x <=^sp y <^sp z" (at level 70, y, z at next level).
Reserved Notation "x <^sp y <^sp z" (at level 70, y, z at next level).
Reserved Notation "x <=^sp y ?= 'iff' c" (at level 70, y, c at next level,
  format "x '[hv'  <=^sp  y '/'  ?=  'iff'  c ']'").
Reserved Notation "x <=^sp y ?= 'iff' c :> T" (at level 70, y, c at next level,
  format "x '[hv'  <=^sp  y '/'  ?=  'iff'  c  :> T ']'").

Reserved Notation "\bot^sp".
Reserved Notation "\top^sp".

Reserved Notation "A `&^sp` B"  (at level 48, left associativity).
Reserved Notation "A `|^sp` B" (at level 52, left associativity).
Reserved Notation "A `\^sp` B" (at level 50, left associativity).
Reserved Notation "~^sp` A" (at level 35, right associativity).

Reserved Notation "\meet^sp_ i F"
  (at level 34, F at level 41, i at level 0,
           format "'[' \meet^sp_ i '/  '  F ']'").
Reserved Notation "\meet^sp_ ( i <- r | P ) F"
  (at level 34, F at level 41, i, r at level 60,
           format "'[' \meet^sp_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\meet^sp_ ( i <- r ) F"
  (F at level 41,
           format "'[' \meet^sp_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\meet^sp_ ( m <= i < n | P ) F"
  (F at level 41, i, n at level 60,
           format "'[' \meet^sp_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\meet^sp_ ( m <= i < n ) F"
  (F at level 41,
           format "'[' \meet^sp_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\meet^sp_ ( i | P ) F"
  (F at level 41,
           format "'[' \meet^sp_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\meet^sp_ ( i : t | P ) F" (F at level 41).
Reserved Notation "\meet^sp_ ( i : t ) F" (F at level 41).
Reserved Notation "\meet^sp_ ( i < n | P ) F"
  (F at level 41, n at level 60,
           format "'[' \meet^sp_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\meet^sp_ ( i < n ) F"
  (F at level 41,
           format "'[' \meet^sp_ ( i  <  n )  F ']'").
Reserved Notation "\meet^sp_ ( i 'in' A | P ) F"
  (F at level 41, A at level 60,
           format "'[' \meet^sp_ ( i  'in'  A  |  P ) '/  '  F ']'").
Reserved Notation "\meet^sp_ ( i 'in' A ) F"
  (F at level 41,
           format "'[' \meet^sp_ ( i  'in'  A ) '/  '  F ']'").

Reserved Notation "\join^sp_ i F"
  (at level 34, F at level 41, i at level 0,
           format "'[' \join^sp_ i '/  '  F ']'").
Reserved Notation "\join^sp_ ( i <- r | P ) F"
  (at level 34, F at level 41, i, r at level 60,
           format "'[' \join^sp_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\join^sp_ ( i <- r ) F"
  (F at level 41,
           format "'[' \join^sp_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\join^sp_ ( m <= i < n | P ) F"
  (F at level 41, i, n at level 60,
           format "'[' \join^sp_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\join^sp_ ( m <= i < n ) F"
  (F at level 41,
           format "'[' \join^sp_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\join^sp_ ( i | P ) F"
  (F at level 41,
           format "'[' \join^sp_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\join^sp_ ( i : t | P ) F" (F at level 41).
Reserved Notation "\join^sp_ ( i : t ) F" (F at level 41).
Reserved Notation "\join^sp_ ( i < n | P ) F"
  (F at level 41, n at level 60,
           format "'[' \join^sp_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\join^sp_ ( i < n ) F"
  (F at level 41,
           format "'[' \join^sp_ ( i  <  n )  F ']'").
Reserved Notation "\join^sp_ ( i 'in' A | P ) F"
  (F at level 41, A at level 60,
           format "'[' \join^sp_ ( i  'in'  A  |  P ) '/  '  F ']'").
Reserved Notation "\join^sp_ ( i 'in' A ) F"
  (F at level 41,
           format "'[' \join^sp_ ( i  'in'  A ) '/  '  F ']'").

Reserved Notation "\min^sp_ i F"
  (at level 34, F at level 41, i at level 0,
           format "'[' \min^sp_ i '/  '  F ']'").
Reserved Notation "\min^sp_ ( i <- r | P ) F"
  (at level 34, F at level 41, i, r at level 60,
           format "'[' \min^sp_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\min^sp_ ( i <- r ) F"
  (F at level 41,
           format "'[' \min^sp_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\min^sp_ ( m <= i < n | P ) F"
  (F at level 41, i, n at level 60,
           format "'[' \min^sp_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\min^sp_ ( m <= i < n ) F"
  (F at level 41,
           format "'[' \min^sp_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\min^sp_ ( i | P ) F"
  (F at level 41,
           format "'[' \min^sp_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\min^sp_ ( i : t | P ) F" (F at level 41).
Reserved Notation "\min^sp_ ( i : t ) F" (F at level 41).
Reserved Notation "\min^sp_ ( i < n | P ) F"
  (F at level 41, n at level 60,
           format "'[' \min^sp_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\min^sp_ ( i < n ) F"
  (F at level 41,
           format "'[' \min^sp_ ( i  <  n )  F ']'").
Reserved Notation "\min^sp_ ( i 'in' A | P ) F"
  (F at level 41, A at level 60,
           format "'[' \min^sp_ ( i  'in'  A  |  P ) '/  '  F ']'").
Reserved Notation "\min^sp_ ( i 'in' A ) F"
  (F at level 41,
           format "'[' \min^sp_ ( i  'in'  A ) '/  '  F ']'").

Reserved Notation "\max^sp_ i F"
  (at level 34, F at level 41, i at level 0,
           format "'[' \max^sp_ i '/  '  F ']'").
Reserved Notation "\max^sp_ ( i <- r | P ) F"
  (at level 34, F at level 41, i, r at level 60,
           format "'[' \max^sp_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\max^sp_ ( i <- r ) F"
  (F at level 41,
           format "'[' \max^sp_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\max^sp_ ( m <= i < n | P ) F"
  (F at level 41, i, n at level 60,
           format "'[' \max^sp_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\max^sp_ ( m <= i < n ) F"
  (F at level 41,
           format "'[' \max^sp_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\max^sp_ ( i | P ) F"
  (F at level 41,
           format "'[' \max^sp_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\max^sp_ ( i : t | P ) F" (F at level 41).
Reserved Notation "\max^sp_ ( i : t ) F" (F at level 41).
Reserved Notation "\max^sp_ ( i < n | P ) F"
  (F at level 41, n at level 60,
           format "'[' \max^sp_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\max^sp_ ( i < n ) F"
  (F at level 41,
           format "'[' \max^sp_ ( i  <  n )  F ']'").
Reserved Notation "\max^sp_ ( i 'in' A | P ) F"
  (F at level 41, A at level 60,
           format "'[' \max^sp_ ( i  'in'  A  |  P ) '/  '  F ']'").
Reserved Notation "\max^sp_ ( i 'in' A ) F"
  (F at level 41,
           format "'[' \max^sp_ ( i  'in'  A ) '/  '  F ']'").

Module Order.

Import Order Order.Theory.

(****************************************************************************)
(* The Module DvdSyntax introduces a new set of notations using the newly   *)
(* created display dvd_display. We first define the display as an opaque    *)
(* definition of type disp_t, and we use it as the first argument of the    *)
(* operator which display we want to change from the default one (here le,  *)
(* lt, dvd sdvd, meet, join, top and bottom, as well as big op notations on *)
(* gcd and lcm). This notations will now be used for any ordered type which *)
(* first parameter is set to dvd_display.                                   *)
(****************************************************************************)

Fact dvd_display : disp_t. Proof. exact. Qed.

Module DvdSyntax.

Notation dvd := (@le dvd_display _).
Notation "@ 'dvd' T" := (@le dvd_display T)
  (at level 10, T at level 8, only parsing) : function_scope.
Notation sdvd := (@lt dvd_display _).
Notation "@ 'sdvd' T" := (@lt dvd_display T)
  (at level 10, T at level 8, only parsing) : function_scope.

Notation "x %| y" := (dvd x y) : order_scope.
Notation "x %<| y" := (sdvd x y) : order_scope.

Notation nat0 := (@top dvd_display _).
Notation nat1 := (@bottom dvd_display _).

Notation gcd := (@meet dvd_display _).
Notation "@ 'gcd' T" := (@meet dvd_display T)
  (at level 10, T at level 8, only parsing) : function_scope.
Notation lcm := (@join dvd_display _).
Notation "@ 'lcm' T" := (@join dvd_display T)
  (at level 10, T at level 8, only parsing) : function_scope.

Notation "\gcd_ ( i <- r | P ) F" :=
  (\big[gcd/nat0]_(i <- r | P%B) F%O) : order_scope.
Notation "\gcd_ ( i <- r ) F" :=
  (\big[gcd/nat0]_(i <- r) F%O) : order_scope.
Notation "\gcd_ ( i | P ) F" :=
  (\big[gcd/nat0]_(i | P%B) F%O) : order_scope.
Notation "\gcd_ i F" :=
  (\big[gcd/nat0]_i F%O) : order_scope.
Notation "\gcd_ ( i : I | P ) F" :=
  (\big[gcd/nat0]_(i : I | P%B) F%O) (only parsing) :
  order_scope.
Notation "\gcd_ ( i : I ) F" :=
  (\big[gcd/nat0]_(i : I) F%O) (only parsing) : order_scope.
Notation "\gcd_ ( m <= i < n | P ) F" :=
  (\big[gcd/nat0]_(m <= i < n | P%B) F%O) : order_scope.
Notation "\gcd_ ( m <= i < n ) F" :=
  (\big[gcd/nat0]_(m <= i < n) F%O) : order_scope.
Notation "\gcd_ ( i < n | P ) F" :=
  (\big[gcd/nat0]_(i < n | P%B) F%O) : order_scope.
Notation "\gcd_ ( i < n ) F" :=
  (\big[gcd/nat0]_(i < n) F%O) : order_scope.
Notation "\gcd_ ( i 'in' A | P ) F" :=
  (\big[gcd/nat0]_(i in A | P%B) F%O) : order_scope.
Notation "\gcd_ ( i 'in' A ) F" :=
  (\big[gcd/nat0]_(i in A) F%O) : order_scope.

Notation "\lcm_ ( i <- r | P ) F" :=
  (\big[lcm/nat1]_(i <- r | P%B) F%O) : order_scope.
Notation "\lcm_ ( i <- r ) F" :=
  (\big[lcm/nat1]_(i <- r) F%O) : order_scope.
Notation "\lcm_ ( i | P ) F" :=
  (\big[lcm/nat1]_(i | P%B) F%O) : order_scope.
Notation "\lcm_ i F" :=
  (\big[lcm/nat1]_i F%O) : order_scope.
Notation "\lcm_ ( i : I | P ) F" :=
  (\big[lcm/nat1]_(i : I | P%B) F%O) (only parsing) :
  order_scope.
Notation "\lcm_ ( i : I ) F" :=
  (\big[lcm/nat1]_(i : I) F%O) (only parsing) : order_scope.
Notation "\lcm_ ( m <= i < n | P ) F" :=
  (\big[lcm/nat1]_(m <= i < n | P%B) F%O) : order_scope.
Notation "\lcm_ ( m <= i < n ) F" :=
  (\big[lcm/nat1]_(m <= i < n) F%O) : order_scope.
Notation "\lcm_ ( i < n | P ) F" :=
  (\big[lcm/nat1]_(i < n | P%B) F%O) : order_scope.
Notation "\lcm_ ( i < n ) F" :=
  (\big[lcm/nat1]_(i < n) F%O) : order_scope.
Notation "\lcm_ ( i 'in' A | P ) F" :=
  (\big[lcm/nat1]_(i in A | P%B) F%O) : order_scope.
Notation "\lcm_ ( i 'in' A ) F" :=
  (\big[lcm/nat1]_(i in A) F%O) : order_scope.

End DvdSyntax.

(******************************************************************************)
(* The Module NatDvd defines dvdn as the canonical order on NatDvd.t, which   *)
(* is abbreviated using the notation natdvd at the end of the module.         *)
(* We use the newly defined dvd_display, described above.                     *)
(* We first recover structures that are common to both nat and natdvd         *)
(* (eqType, choiceType, countType) through the copy mechanism, then we use    *)
(* a single factory MeetJoinMixin to instantiate both porderType and          *)
(* distrLatticeType canonical structures, and end with top and bottom.        *)
(* We finish by providing theorems to convert the operations of ordered and   *)
(* lattice types to their definition without structure abstraction.           *)
(******************************************************************************)

Module NatDvd.
Section NatDvd.
Definition t := nat.
Implicit Types (m n p : t).

#[export] HB.instance Definition _ := Choice.copy t nat.

Fact dvdn_anti : antisymmetric dvdn.
Proof. by move=> a b => /andP[] /gcdn_idPl + /gcdn_idPr => ->. Qed.

(* Note that this where the dvd_display is associated with the type NatDvd.t. *)
#[export] HB.instance Definition _ :=
  @Le_isPOrder.Build dvd_display t dvdn dvdnn dvdn_anti dvdn_trans.
#[export] HB.instance Definition _ := @hasBottom.Build _ t 1 dvd1n.
#[export] HB.instance Definition _ := @hasTop.Build _ t 0 dvdn0.
#[export] HB.instance Definition _ :=
  @POrder_MeetJoin_isLattice.Build dvd_display t gcdn lcmn dvdn_gcd dvdn_lcm.

Import DvdSyntax.

Fact meetUl : @left_distributive t t gcd lcm.
Proof.
move=> [|m'] [|n'] [|p']; rewrite ?joinxx ?join1x ?joinx1 ?meet1x ?meetx1//=.
- by rewrite meetKUC.
- by rewrite meetUK.
apply: eqn_from_log; rewrite ?(gcdn_gt0, lcmn_gt0)//= => p.
by rewrite !(logn_gcd, logn_lcm) ?(gcdn_gt0, lcmn_gt0)// minn_maxl.
Qed.

#[export] HB.instance Definition _ :=
  Lattice_Meet_isDistrLattice.Build dvd_display t meetUl.

Lemma dvdE : dvd = dvdn :> rel t. Proof. by []. Qed.
Lemma nat1E : nat1 = 1%N :> t. Proof. by []. Qed.
Lemma nat0E : nat0 = 0%N :> t. Proof. by []. Qed.
Lemma sdvdE (m n : t) : (m %<| n) = (n != m) && (m %| n).
Proof. exact/lt_def. Qed.
Lemma gcdE : gcd = gcdn :> (t -> t -> t). Proof. by []. Qed.
Lemma lcmE : lcm = lcmn :> (t -> t -> t). Proof. by []. Qed.

End NatDvd.
Module Exports.
HB.reexport NatDvd.
Notation natdvd := t.
Definition dvdEnat := dvdE.
Definition nat1E := nat1E.
Definition nat0E := nat0E.
Definition sdvdEnat := sdvdE.
Definition gcdEnat := gcdE.
Definition lcmEnat := lcmE.
End Exports.
End NatDvd.
HB.export NatDvd.Exports.

(*********************************)
(* Definition of seqprod_display *)
(*********************************)

Fact seqprod_display (disp : disp_t) : disp_t. Proof. exact: disp. Qed.

Module Import SeqProdSyntax.

Notation "<=^sp%O" := (@le (seqprod_display _) _) : function_scope.
Notation ">=^sp%O" := (@ge (seqprod_display _) _)  : function_scope.
Notation ">=^sp%O" := (@ge (seqprod_display _) _)  : function_scope.
Notation "<^sp%O" := (@lt (seqprod_display _) _) : function_scope.
Notation ">^sp%O" := (@gt (seqprod_display _) _) : function_scope.
Notation "<?=^sp%O" := (@leif (seqprod_display _) _) : function_scope.
Notation ">=<^sp%O" := (@comparable (seqprod_display _) _) : function_scope.
Notation "><^sp%O" := (fun x y => ~~ (@comparable (seqprod_display _) _ x y)) :
  function_scope.

Notation "<=^sp y" := (>=^sp%O y) : order_scope.
Notation "<=^sp y :> T" := (<=^sp (y : T)) (only parsing) : order_scope.
Notation ">=^sp y"  := (<=^sp%O y) : order_scope.
Notation ">=^sp y :> T" := (>=^sp (y : T)) (only parsing) : order_scope.

Notation "<^sp y" := (>^sp%O y) : order_scope.
Notation "<^sp y :> T" := (<^sp (y : T)) (only parsing) : order_scope.
Notation ">^sp y" := (<^sp%O y) : order_scope.
Notation ">^sp y :> T" := (>^sp (y : T)) (only parsing) : order_scope.

Notation "x <=^sp y" := (<=^sp%O x y) : order_scope.
Notation "x <=^sp y :> T" := ((x : T) <=^sp (y : T)) (only parsing) : order_scope.
Notation "x >=^sp y" := (y <=^sp x) (only parsing) : order_scope.
Notation "x >=^sp y :> T" := ((x : T) >=^sp (y : T)) (only parsing) : order_scope.

Notation "x <^sp y"  := (<^sp%O x y) : order_scope.
Notation "x <^sp y :> T" := ((x : T) <^sp (y : T)) (only parsing) : order_scope.
Notation "x >^sp y"  := (y <^sp x) (only parsing) : order_scope.
Notation "x >^sp y :> T" := ((x : T) >^sp (y : T)) (only parsing) : order_scope.

Notation "x <=^sp y <=^sp z" := ((x <=^sp y) && (y <=^sp z)) : order_scope.
Notation "x <^sp y <=^sp z" := ((x <^sp y) && (y <=^sp z)) : order_scope.
Notation "x <=^sp y <^sp z" := ((x <=^sp y) && (y <^sp z)) : order_scope.
Notation "x <^sp y <^sp z" := ((x <^sp y) && (y <^sp z)) : order_scope.

Notation "x <=^sp y ?= 'iff' C" := (<?=^sp%O x y C) : order_scope.
Notation "x <=^sp y ?= 'iff' C :> T" := ((x : T) <=^sp (y : T) ?= iff C)
  (only parsing) : order_scope.

Notation ">=<^sp y" := [pred x | >=<^sp%O x y] : order_scope.
Notation ">=<^sp y :> T" := (>=<^sp (y : T)) (only parsing) : order_scope.
Notation "x >=<^sp y" := (>=<^sp%O x y) : order_scope.

Notation "><^sp y" := [pred x | ~~ (>=<^sp%O x y)] : order_scope.
Notation "><^sp y :> T" := (><^sp (y : T)) (only parsing) : order_scope.
Notation "x ><^sp y" := (~~ (><^sp%O x y)) : order_scope.

(* The following Local Notations are here to define the \join^sp_ and         *)
(* \meet^sp_ notations later. Do not remove them.                             *)
Local Notation "\bot" := (@bottom (seqprod_display _) _).
Local Notation "\top" := (@top (seqprod_display _) _).
Local Notation meet := (@meet (seqprod_display _) _).
Local Notation join := (@join (seqprod_display _) _).
Local Notation min := (@min (seqprod_display _) _).
Local Notation max := (@max (seqprod_display _) _).

Notation "x `&^sp` y" :=  (meet x y) : order_scope.
Notation "x `|^sp` y" := (join x y) : order_scope.

Notation "\join^sp_ ( i <- r | P ) F" :=
  (\big[join / \bot]_(i <- r | P%B) F%O) : order_scope.
Notation "\join^sp_ ( i <- r ) F" :=
  (\big[join / \bot]_(i <- r) F%O) : order_scope.
Notation "\join^sp_ ( i | P ) F" :=
  (\big[join / \bot]_(i | P%B) F%O) : order_scope.
Notation "\join^sp_ i F" :=
  (\big[join / \bot]_i F%O) : order_scope.
Notation "\join^sp_ ( i : I | P ) F" :=
  (\big[join / \bot]_(i : I | P%B) F%O) (only parsing) : order_scope.
Notation "\join^sp_ ( i : I ) F" :=
  (\big[join / \bot]_(i : I) F%O) (only parsing) : order_scope.
Notation "\join^sp_ ( m <= i < n | P ) F" :=
 (\big[join / \bot]_(m <= i < n | P%B) F%O) : order_scope.
Notation "\join^sp_ ( m <= i < n ) F" :=
 (\big[join / \bot]_(m <= i < n) F%O) : order_scope.
Notation "\join^sp_ ( i < n | P ) F" :=
 (\big[join / \bot]_(i < n | P%B) F%O) : order_scope.
Notation "\join^sp_ ( i < n ) F" :=
 (\big[join / \bot]_(i < n) F%O) : order_scope.
Notation "\join^sp_ ( i 'in' A | P ) F" :=
 (\big[join / \bot]_(i in A | P%B) F%O) : order_scope.
Notation "\join^sp_ ( i 'in' A ) F" :=
 (\big[join / \bot]_(i in A) F%O) : order_scope.

Notation "\meet^sp_ ( i <- r | P ) F" :=
  (\big[meet / \top]_(i <- r | P%B) F%O) : order_scope.
Notation "\meet^sp_ ( i <- r ) F" :=
  (\big[meet / \top]_(i <- r) F%O) : order_scope.
Notation "\meet^sp_ ( i | P ) F" :=
  (\big[meet / \top]_(i | P%B) F%O) : order_scope.
Notation "\meet^sp_ i F" :=
  (\big[meet / \top]_i F%O) : order_scope.
Notation "\meet^sp_ ( i : I | P ) F" :=
  (\big[meet / \top]_(i : I | P%B) F%O) (only parsing) : order_scope.
Notation "\meet^sp_ ( i : I ) F" :=
  (\big[meet / \top]_(i : I) F%O) (only parsing) : order_scope.
Notation "\meet^sp_ ( m <= i < n | P ) F" :=
 (\big[meet / \top]_(m <= i < n | P%B) F%O) : order_scope.
Notation "\meet^sp_ ( m <= i < n ) F" :=
 (\big[meet / \top]_(m <= i < n) F%O) : order_scope.
Notation "\meet^sp_ ( i < n | P ) F" :=
 (\big[meet / \top]_(i < n | P%B) F%O) : order_scope.
Notation "\meet^sp_ ( i < n ) F" :=
 (\big[meet / \top]_(i < n) F%O) : order_scope.
Notation "\meet^sp_ ( i 'in' A | P ) F" :=
 (\big[meet / \top]_(i in A | P%B) F%O) : order_scope.
Notation "\meet^sp_ ( i 'in' A ) F" :=
 (\big[meet / \top]_(i in A) F%O) : order_scope.

Notation "\min^sp_ i F" :=
  (\big[min/top]_i F) : order_scope.
Notation "\min^sp_ ( i <- r | P ) F" :=
  (\big[min/top]_(i <- r | P%B) F%O) : order_scope.
Notation "\min^sp_ ( i < r ) F" :=
  (\big[min/top]_(i <- r) F%O) : order_scope.
Notation "\min^sp_ ( m <= i < n | P ) F" :=
  (\big[min/top]_(m <= i < n | P%B) F%O) : order_scope.
Notation "\min^sp_ ( m <= i < n ) F" :=
  (\big[min/top]_(m <= i < n) F%O) : order_scope.
Notation "\min^sp_ ( i | P ) F" :=
  (\big[min/top]_(i | P%B) F%O) : order_scope.
Notation "\min^sp_ ( i : t | P ) F" :=
  (\big[min/top]_(i : t | P%B) F%O) (only parsing) : order_scope.
Notation "\min^sp_ ( i : t ) F" :=
  (\big[min/top]_(i : t) F%O) (only parsing) : order_scope.
Notation "\min^sp_ ( i < n | P ) F" :=
  (\big[min/top]_(i < n | P%B) F%O) : order_scope.
Notation "\min^sp_ ( i < n ) F" :=
  (\big[min/top]_(i < n) F%O) : order_scope.
Notation "\min^sp_ ( i 'in' A | P ) F" :=
  (\big[min/top]_(i in A | P%B) F%O) : order_scope.
Notation "\min^sp_ ( i 'in' A ) F" :=
  (\big[min/top]_(i in A) F%O) : order_scope.

Notation "\max^sp_ i F" :=
  (\big[max/bottom]_i F%O) : order_scope.
Notation "\max^sp_ ( i <- r | P ) F" :=
  (\big[max/bottom]_(i <- r | P%B) F%O) : order_scope.
Notation "\max^sp_ ( i < r ) F" :=
  (\big[max/bottom]_(i <- r) F%O) : order_scope.
Notation "\max^sp_ ( m <= i < n | P ) F" :=
  (\big[max/bottom]_(m <= i < n | P%B) F%O) : order_scope.
Notation "\max^sp_ ( m <= i < n ) F" :=
  (\big[max/bottom]_(m <= i < n) F%O) : order_scope.
Notation "\max^sp_ ( i | P ) F" :=
  (\big[max/bottom]_(i | P%B) F%O) : order_scope.
Notation "\max^sp_ ( i : t | P ) F" :=
  (\big[max/bottom]_(i : t | P%B) F%O) (only parsing) : order_scope.
Notation "\max^sp_ ( i : t ) F" :=
  (\big[max/bottom]_(i : t) F%O) (only parsing) : order_scope.
Notation "\max^sp_ ( i < n | P ) F" :=
  (\big[max/bottom]_(i < n | P%B) F%O) : order_scope.
Notation "\max^sp_ ( i < n ) F" :=
  (\big[max/bottom]_(i < n) F%O) : order_scope.
Notation "\max^sp_ ( i 'in' A | P ) F" :=
  (\big[max/bottom]_(i in A | P%B) F%O) : order_scope.
Notation "\max^sp_ ( i 'in' A ) F" :=
  (\big[max/bottom]_(i in A) F%O) : order_scope.

End SeqProdSyntax.

(*****************************************)
(* We declare an alias of the sequences, *)
(* which has canonical product order.    *)
(*****************************************)

Module SeqProdOrder.
Section SeqProdOrder.

Definition type (disp : disp_t) T := seq T.
Definition type_ (disp : disp_t) (T : preorderType disp) :=
  type (seqprod_display disp) T.

Context {disp disp' : disp_t}.

Local Notation seq := (type disp').

#[export] HB.instance Definition _ (T : eqType) := Equality.on (seq T).
#[export] HB.instance Definition _ (T : choiceType) := Choice.on (seq T).
#[export] HB.instance Definition _ (T : countType) := Countable.on (seq T).

Section Preorder.
Context (T : preorderType disp).
Implicit Types (s : seq T).

Fixpoint le s1 s2 := if s1 isn't x1 :: s1' then true else
                     if s2 isn't x2 :: s2' then false else
                     (x1 <= x2) && le s1' s2'.

Fact refl : reflexive le. Proof. by elim=> //= ? ? ?; rewrite !lexx. Qed.

Fact trans : transitive le.
Proof.
elim=> [|y ys ihs] [|x xs] [|z zs] //= /andP[xy xys] /andP[yz yzs].
by rewrite (le_trans xy)// ihs.
Qed.

#[export] HB.instance Definition _ :=
  isPreorder.Build disp' (seq T) (rrefl _) refl trans.

Lemma leEseq s1 s2 : (s1 <= s2) = if s1 isn't x1 :: s1' then true else
                                  if s2 isn't x2 :: s2' then false else
                                  (x1 <= x2) && (s1' <= s2' :> seq _).
Proof. by case: s1. Qed.

Lemma le0s s : [::] <= s :> seq _. Proof. by []. Qed.

Lemma les0 s : (s <= [::]) = (s == [::]). Proof. by rewrite leEseq. Qed.

Lemma le_cons x1 s1 x2 s2 :
   (x1 :: s1 <= x2 :: s2 :> seq _) = (x1 <= x2) && (s1 <= s2).
Proof. by []. Qed.

#[export] HB.instance Definition _ := hasBottom.Build _ (seq T) le0s.

Lemma botEseq : \bot = [::] :> seq T.
Proof. by []. Qed.
End Preorder.

Section POrder.
Variable T : porderType disp.
Implicit Types s : seq T.

Fact anti : antisymmetric (@le T).
Proof.
by elim=> [|x s ihs] [|y s'] //=; rewrite andbACA => /andP[/le_anti-> /ihs->].
Qed.

#[export] HB.instance Definition _ :=
  Preorder_isPOrder.Build disp' (seq T) anti.

End POrder.

Section MeetSemilattice.
Context (T : meetSemilatticeType disp).
Implicit Types (s : seq T).

Fixpoint meet s1 s2 :=
  match s1, s2 with
    | x1 :: s1', x2 :: s2' => (x1 `&` x2) :: meet s1' s2'
    | _, _ => [::]
  end.

Fact lexI s1 s2 s3 : (s1 <= meet s2 s3) = (s1 <= s2) && (s1 <= s3).
Proof.
elim: s1 s2 s3 => [|x s1 IHs1] [|y s2] [|z s3] //=; first by rewrite andbF.
by rewrite leEseq lexI IHs1 andbACA.
Qed.

#[export] HB.instance Definition _ :=
  @POrder_isMeetSemilattice.Build _ (seq T) meet lexI.

Lemma meetEseq s1 s2 : s1 `&` s2 =  [seq x.1 `&` x.2 | x <- zip s1 s2].
Proof. by elim: s1 s2 => [|x s1 ihs1] [|y s2]//=; rewrite -ihs1. Qed.

Lemma meet_cons x1 s1 x2 s2 :
  (x1 :: s1 : seq T) `&` (x2 :: s2) = (x1 `&` x2) :: s1 `&` s2.
Proof. by []. Qed.

End MeetSemilattice.

Section JoinSemilattice.
Context (T : joinSemilatticeType disp).
Implicit Types (s : seq T).

Fixpoint join s1 s2 :=
  match s1, s2 with
    | [::], _ => s2 | _, [::] => s1
    | x1 :: s1', x2 :: s2' => (x1 `|` x2) :: join s1' s2'
  end.

Fact leUx s1 s2 s3 : (join s1 s2 <= s3) = (s1 <= s3) && (s2 <= s3).
Proof.
elim : s1 s2 s3 => [|x s1 IHs1] [|y s2] [|z s3] //=; first by rewrite andbT.
by rewrite leEseq leUx IHs1 andbACA.
Qed.

#[export] HB.instance Definition _ :=
  @POrder_isJoinSemilattice.Build _ (seq T) join leUx.

Lemma joinEseq s1 s2 : s1 `|` s2 =
  match s1, s2 with
    | [::], _ => s2 | _, [::] => s1
    | x1 :: s1', x2 :: s2' => (x1 `|` x2) :: ((s1' : seq _) `|` s2')
  end.
Proof. by case: s1. Qed.

Lemma join_cons x1 s1 x2 s2 :
  (x1 :: s1 : seq T) `|` (x2 :: s2) = (x1 `|` x2) :: s1 `|` s2.
Proof. by []. Qed.

End JoinSemilattice.

(* FIXME: use HB.saturate *)
#[export] HB.instance Definition _ (T : latticeType disp) := POrder.on (seq T).
(* /FIXME *)

Section DistrLattice.
Context (T : distrLatticeType disp).

Fact meetUl : left_distributive (@meet T) (@join T).
Proof. by elim=> [|? ? ih] [|? ?] [|? ?] //=; rewrite meetUl ih. Qed.

#[export] HB.instance Definition _ :=
  Lattice_Meet_isDistrLattice.Build _ (seq T) meetUl.

End DistrLattice.

End SeqProdOrder.

Module Exports.

HB.reexport SeqProdOrder.

Notation seqprod_with := type.
Notation seqprod := type_.

Definition leEseq := @leEseq.
Definition le0s := @le0s.
Definition les0 := @les0.
Definition le_cons := @le_cons.
Definition botEseq := @botEseq.
Definition meetEseq := @meetEseq.
Definition meet_cons := @meet_cons.
Definition joinEseq := @joinEseq.

End Exports.
End SeqProdOrder.
HB.export SeqProdOrder.Exports.

Module DefaultSeqProdOrder.
Section DefaultSeqProdOrder.
Context {disp : disp_t}.

Notation seqprod := (seqprod_with (seqprod_display disp)).

HB.instance Definition _ (T : preorderType disp) :=
  BPreorder.copy (seq T) (seqprod T).
HB.instance Definition _ (T : porderType disp) :=
  BPOrder.copy (seq T) (seqprod T).
HB.instance Definition _ (T : meetSemilatticeType disp) :=
  BMeetSemilattice.copy (seq T) (seqprod T).
HB.instance Definition _ (T : joinSemilatticeType disp) :=
  BJoinSemilattice.copy (seq T) (seqprod T).
HB.instance Definition _ (T : latticeType disp) :=
  BLattice.copy (seq T) (seqprod T).
HB.instance Definition _ (T : distrLatticeType disp) :=
  BDistrLattice.copy (seq T) (seqprod T).

End DefaultSeqProdOrder.
End DefaultSeqProdOrder.

Module Syntax.
Export DvdSyntax.
End Syntax.

Module Exports.
HB.reexport.
End Exports.

End Order.

Export Order.Exports.

Export Order.Syntax.

Module DefaultSeqProdOrder := Order.DefaultSeqProdOrder.

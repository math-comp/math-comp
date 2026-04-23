(* (c) Copyright 2006-2019 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import path fintype tuple finfun bigop finset.
From mathcomp Require Import preorder porder lattice.

(******************************************************************************)
(*                      Complemented lattice structures                       *)
(*                                                                            *)
(* NB: See CONTRIBUTING.md for an introduction to HB concepts and commands.   *)
(*                                                                            *)
(* NB: See the header of all_order.v for general remarks about the preorder   *)
(*     and order structures in MathComp, and the files in this directory.     *)
(*                                                                            *)
(* * Interfaces                                                               *)
(* We provide the following interfaces for types equipped with an order:      *)
(*                                                                            *)
(*       cDistrLatticeType d == the type of relatively complemented           *)
(*                              distributive lattices, where each interval    *)
(*                              [a, b] is equipped with a complement operation*)
(*                              The HB class is called CDistrLattice.         *)
(*      cbDistrLatticeType d == the type of sectionally complemented          *)
(*                              distributive lattices, equipped with a bottom,*)
(*                              a relative complement operation, and a        *)
(*                              difference operation, i.e., a complement      *)
(*                              operation for each interval of the form       *)
(*                              [\bot, b]                                     *)
(*                              The HB class is called CBDistrLattice.        *)
(*      ctDistrLatticeType d == the type of dually sectionally complemented   *)
(*                              distributive lattices, equipped with a top,   *)
(*                              a relative complement operation, and a        *)
(*                              dual difference operation, i.e. a complement  *)
(*                              operation for each interval of the form       *)
(*                              [a, \top]                                     *)
(*                              The HB class is called CTDistrLattice.        *)
(*     ctbDistrLatticeType d == the type of complemented distributive         *)
(*                              lattices, equipped with top, bottom,          *)
(*                              difference, dual difference, and complement   *)
(*                              The HB class is called CTBDistrLattice.       *)
(*    finCDistrLatticeType d == the type of finite relatively complemented    *)
(*                              distributive lattices                         *)
(*                              The HB class is called FinCDistrLattice.      *)
(*  finCTBDistrLatticeType d == the type of finite complemented distributive  *)
(*                              lattices                                      *)
(*                              The HB class is called FinCTBDistrLattice.    *)
(*                                                                            *)
(* * Order relations and operations:                                          *)
(* In general, an overloaded relation or operation on ordered types takes the *)
(* following arguments:                                                       *)
(* 1. a display d of type Order.disp_t,                                       *)
(* 2. an instance T of the minimal structure it operates on, and              *)
(* 3. operands.                                                               *)
(* Here is the exhaustive list of all such operations together with their     *)
(* default notation (defined in order_scope unless specified otherwise).      *)
(*                                                                            *)
(* For T of type cDistrLatticeType d, and x, y, z of type T:                  *)
(*    rcompl x y z == the (relative) complement of z in [x, y]                *)
(*                                                                            *)
(* For T of type cbDistrLatticeType d, and x, y of type T:                    *)
(*         x `\` y := @Order.diff d T x y                                     *)
(*                 == the (sectional) complement of y in [\bot, x],           *)
(*                    i.e., rcompl \bot x y                                   *)
(*                                                                            *)
(* For T of type ctDistrLatticeType d, and x, y of type T:                    *)
(*      codiff x y == the (dual sectional) complement of y in [x, \top],      *)
(*                    i.e., rcompl x \top y                                   *)
(*                                                                            *)
(* For T of type ctbDistrLatticeType d, and x of type T:                      *)
(*            ~` x := @Order.compl d T x                                      *)
(*                 == the complement of x in [\bot, \top],                    *)
(*                    i.e., rcompl \bot \top x                                *)
(*                                                                            *)
(* Acknowledgments: The files in this directory are based on prior work by    *)
(* D. Dreyer, G. Gonthier, A. Nanevski, P-Y Strub, B. Ziliani                 *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope order_scope.

Module Order.

Export Order.
Import Order.Theory.

#[key="T", primitive]
HB.mixin Record DistrLattice_hasRelativeComplement d T & DistrLattice d T := {
  (* rcompl x y z is the complement of z in the interval [x, y]. *)
  rcompl : T -> T -> T -> T;
  rcomplPmeet : forall x y z, ((x `&` y) `|` z) `&` rcompl x y z = x `&` y;
  rcomplPjoin : forall x y z, ((y `|` x) `&` z) `|` rcompl x y z = y `|` x;
}.

#[short(type="cDistrLatticeType")]
HB.structure Definition CDistrLattice d :=
  { T of DistrLattice d T & DistrLattice_hasRelativeComplement d T }.

#[key="T", primitive]
HB.mixin Record CDistrLattice_hasSectionalComplement d T
         & CDistrLattice d T & hasBottom d T := {
  diff : T -> T -> T;
  (* FIXME: a bug in HB prevents us writing "rcompl \bot x y" *)
  diffErcompl : forall x y, diff x y = rcompl (\bot : T) x y;
}.

#[short(type="cbDistrLatticeType")]
HB.structure Definition CBDistrLattice d :=
  { T of CDistrLattice d T & hasBottom d T &
         CDistrLattice_hasSectionalComplement d T }.

#[key="T", primitive]
HB.mixin Record CDistrLattice_hasDualSectionalComplement d T
         & CDistrLattice d T & hasTop d T := {
  codiff : T -> T -> T;
  codiffErcompl : forall x y, codiff x y = rcompl x \top y;
}.

#[short(type="ctDistrLatticeType")]
HB.structure Definition CTDistrLattice d :=
  { T of CDistrLattice d T & hasTop d T &
         CDistrLattice_hasDualSectionalComplement d T }.

Module CBDistrLatticeSyntax.
Notation "x `\` y" := (diff x y) : order_scope.
End CBDistrLatticeSyntax.
HB.export CBDistrLatticeSyntax.

#[key="T", primitive]
HB.mixin Record CDistrLattice_hasComplement d T &
         CTDistrLattice d T & CBDistrLattice d T := {
  compl : T -> T;
  (* FIXME: a bug in HB prevents us writing "\top `\` x" and "codiff \bot x" *)
  complEdiff : forall x : T, compl x = (\top : T) `\` x;
  complEcodiff : forall x : T, compl x = codiff (\bot : T) x;
}.

#[short(type="ctbDistrLatticeType")]
HB.structure Definition CTBDistrLattice d :=
  { T of CBDistrLattice d T & CTDistrLattice d T &
         CDistrLattice_hasComplement d T }.

Module Import CTBDistrLatticeSyntax.
Notation "~` A" := (compl A) : order_scope.
End CTBDistrLatticeSyntax.
HB.export CTBDistrLatticeSyntax.

(**********)
(* FINITE *)
(**********)

#[short(type="finCDistrLatticeType")]
HB.structure Definition FinCDistrLattice d :=
  { T of Finite T & CDistrLattice d T }.

#[short(type="finCTBDistrLatticeType")]
HB.structure Definition FinCTBDistrLattice d :=
  { T of Finite T & CTBDistrLattice d T }.

(********)
(* DUAL *)
(********)

(*
FIXME: we have two issues in the dual instance declarations in the DualOrder
module below:
1. HB.saturate is slow, and
2. if we declare them by HB.instance, some declarations fail because it unfolds
   [dual] and the generated instance does not typecheck
   (math-comp/hierarchy-builder#257).
*)
Module DualOrder.

HB.instance Definition _ d (T : cDistrLatticeType d) :=
  DistrLattice_hasRelativeComplement.Build (dual_display d) T^d
    (fun x y => rcomplPjoin y x) (fun x y => rcomplPmeet y x).
HB.instance Definition _ d (T : ctDistrLatticeType d) :=
  CDistrLattice_hasSectionalComplement.Build (dual_display d) T^d codiffErcompl.
HB.instance Definition _ d (T : cbDistrLatticeType d) :=
  CDistrLattice_hasDualSectionalComplement.Build (dual_display d) T^d
    diffErcompl.
HB.instance Definition _ d (T : ctbDistrLatticeType d) :=
  CDistrLattice_hasComplement.Build (dual_display d) T^d
    complEcodiff complEdiff.

HB.saturate.

End DualOrder.
HB.export DualOrder.

(**********)
(* THEORY *)
(**********)

Module Import CDistrLatticeTheory.
Section CDistrLatticeTheory.
Context {disp : disp_t} {L : cDistrLatticeType disp}.
Implicit Types (x y z : L).

Lemma rcomplPmeet x y z : ((x `&` y) `|` z) `&` rcompl x y z = x `&` y.
Proof. exact: rcomplPmeet. Qed.

Lemma rcomplPjoin x y z : ((y `|` x) `&` z) `|` rcompl x y z = y `|` x.
Proof. exact: rcomplPjoin. Qed.

Lemma rcomplKI x y z : x <= y -> (x `|` z) `&` rcompl x y z = x.
Proof. by move=> lexy; have := rcomplPmeet x y z; rewrite (meet_l lexy). Qed.

Lemma rcomplKU x y z : x <= y -> (y `&` z) `|` rcompl x y z = y.
Proof. by move=> lexy; have := rcomplPjoin x y z; rewrite (join_l lexy). Qed.

End CDistrLatticeTheory.
End CDistrLatticeTheory.

Module Import CBDistrLatticeTheory.
Section CBDistrLatticeTheory.
Context {disp : disp_t} {L : cbDistrLatticeType disp}.
Implicit Types (x y z : L).

Lemma diffErcompl x y : x `\` y = rcompl \bot x y.
Proof. exact: diffErcompl. Qed.

Lemma diffKI x y : y `&` (x `\` y) = \bot.
Proof. by have := rcomplKI y (le0x x); rewrite join0x diffErcompl. Qed.

Lemma diffIK x y : (x `\` y) `&` y = \bot.
Proof. by rewrite meetC diffKI. Qed.

Lemma meetIB z x y : (z `&` y) `&` (x `\` y) = \bot.
Proof. by rewrite -meetA diffKI meetx0. Qed.

Lemma meetBI z x y : (x `\` y) `&` (z `&` y) = \bot.
Proof. by rewrite meetC meetIB. Qed.

Lemma joinIB y x : (x `&` y) `|` (x `\` y) = x.
Proof. by rewrite diffErcompl rcomplKU. Qed.

Lemma joinBI y x : (x `\` y) `|` (x `&` y) = x.
Proof. by rewrite joinC joinIB. Qed.

Lemma joinIBC y x : (y `&` x) `|` (x `\` y) = x.
Proof. by rewrite meetC joinIB. Qed.

Lemma joinBIC y x : (x `\` y) `|` (y `&` x) = x.
Proof. by rewrite meetC joinBI. Qed.

Lemma leBx x y : x `\` y <= x.
Proof. by rewrite -[leRHS](joinIB y) leUr. Qed.
Hint Resolve leBx : core.

Lemma diffxx x : x `\` x = \bot.
Proof. by have := diffKI x x; rewrite meet_r. Qed.

Lemma leBl z x y : x <= y -> x `\` z <= y `\` z.
Proof.
rewrite -[leLHS](joinIB z) -[leRHS](joinIB z).
by rewrite leU2E ?meetIB ?meetBI // => /andP [].
Qed.

Lemma diffKU y x : y `|` (x `\` y) = y `|` x.
Proof.
apply/eqP; rewrite eq_le leU2 //= leUx leUl.
by apply/meet_idPl; have := joinIB y x; rewrite joinIl join_l.
Qed.

Lemma diffUK y x : (x `\` y) `|` y = x `|` y.
Proof. by rewrite joinC diffKU joinC. Qed.

Lemma leBKU y x : y <= x -> y `|` (x `\` y) = x.
Proof. by move=> /join_r {2}<-; rewrite diffKU. Qed.

Lemma leBUK y x : y <= x -> (x `\` y) `|` y = x.
Proof. by move=> leyx; rewrite joinC leBKU. Qed.

Lemma leBLR x y z : (x `\` y <= z) = (x <= y `|` z).
Proof.
apply/idP/idP; first by move=> /join_r <-; rewrite joinA diffKU joinAC leUr.
by rewrite -{1}[x](joinIB y) => /(leU2r_le (diffIK _ _)).
Qed.

Lemma diffUx x y z : (x `|` y) `\` z = (x `\` z) `|` (y `\` z).
Proof.
apply/eqP; rewrite eq_le leUx !leBl ?leUr ?leUl ?andbT //.
by rewrite leBLR joinA diffKU joinAC diffKU joinAC -joinA leUr.
Qed.

Lemma diff_eq0 x y : (x `\` y == \bot) = (x <= y).
Proof. by rewrite -lex0 leBLR joinx0. Qed.

Lemma joinxB x y z : x `|` (y `\` z) = ((x `|` y) `\` z) `|` (x `&` z).
Proof. by rewrite diffUx joinAC joinBI. Qed.

Lemma joinBx x y z : (y `\` z) `|` x = ((y `|` x) `\` z) `|` (z `&` x).
Proof. by rewrite ![_ `|` x]joinC ![_ `&` x]meetC joinxB. Qed.

Lemma leBr z x y : x <= y -> z `\` y <= z `\` x.
Proof. by move=> lexy; rewrite leBLR joinxB meet_r ?leBUK ?leUr ?lexUl. Qed.

Lemma leB2 x y z t : x <= z -> t <= y -> x `\` y <= z `\` t.
Proof. by move=> /(@leBl t) ? /(@leBr x) /le_trans ->. Qed.

Lemma meet_eq0E_diff z x y : x <= z -> (x `&` y == \bot) = (x <= z `\` y).
Proof.
move=> xz; apply/idP/idP; last by move=> /meet_r <-; rewrite -meetA meetBI.
by move=> /eqP xIy_eq0; rewrite -[x](joinIB y) xIy_eq0 join0x leBl.
Qed.

Lemma leBRL x y z : (x <= z `\` y) = (x <= z) && (x `&` y == \bot).
Proof.
apply/idP/idP => [xyz|]; first by rewrite (@meet_eq0E_diff z) // (le_trans xyz).
by move=> /andP [?]; rewrite -meet_eq0E_diff.
Qed.

Lemma eq_diff x y z : (x `\` y == z) = (z <= x <= y `|` z) && (z `&` y == \bot).
Proof. by rewrite eq_le leBLR leBRL andbCA andbA. Qed.

Lemma diffxU x y z : z `\` (x `|` y) = (z `\` x) `&` (z `\` y).
Proof.
apply/eqP; rewrite eq_le lexI !leBr ?leUl ?leUr //=.
rewrite leBRL leIx2 ?leBx //= meetUr meetAC diffIK -meetA diffIK.
by rewrite meet0x meetx0 joinx0.
Qed.

Lemma diffx0 x : x `\` \bot = x.
Proof. by apply/eqP; rewrite eq_diff join0x meetx0 lexx eqxx. Qed.

Lemma diff0x x : \bot `\` x = \bot.
Proof. by apply/eqP; rewrite eq_diff joinx0 meet0x lexx eqxx le0x. Qed.

Lemma diffIx x y z : (x `&` y) `\` z = (x `\` z) `&` (y `\` z).
Proof.
apply/eqP; rewrite eq_diff joinIr ?leI2 ?diffKU ?leUr ?leBx //=.
by rewrite -meetA diffIK meetx0.
Qed.

Lemma meetxB x y z : x `&` (y `\` z) = (x `&` y) `\` z.
Proof. by rewrite diffIx -{1}[x](joinBI z) meetUl meetIB joinx0. Qed.

Lemma meetBx x y z : (x `\` y) `&` z = (x `&` z) `\` y.
Proof. by rewrite ![_ `&` z]meetC meetxB. Qed.

Lemma diffxI x y z : x `\` (y `&` z) = (x `\` y) `|` (x `\` z).
Proof.
apply/eqP; rewrite eq_diff leUx !leBx //= joinIl joinA joinCA !diffKU.
rewrite joinCA -joinA [_ `|` x]joinC ![x `|` _]join_l //.
by rewrite -joinIl leUr /= meetUl {1}[_ `&` z]meetC ?meetBI joinx0.
Qed.

Lemma diffBx x y z : (x `\` y) `\` z = x `\` (y `|` z).
Proof.
apply/eqP; rewrite eq_diff leBr ?leUl //=.
by rewrite diffxU joinIr diffKU -joinIr meet_l ?leUr //= -meetA diffIK meetx0.
Qed.

Lemma diffxB x y z : x `\` (y `\` z) = (x `\` y) `|` (x `&` z).
Proof.
rewrite -[y in RHS](joinIB z) diffxU joinIl diffxI -joinA joinBI join_r //.
by rewrite joinBx meetKU meetA meetAC diffIK meet0x joinx0 meet_r.
Qed.

Lemma joinBK x y : (y `|` x) `\` x = (y `\` x).
Proof. by rewrite diffUx diffxx joinx0. Qed.

Lemma joinBKC x y : (x `|` y) `\` x = (y `\` x).
Proof. by rewrite diffUx diffxx join0x. Qed.

Lemma disj_le x y : x `&` y == \bot -> (x <= y) = (x == \bot).
Proof. by rewrite [x == \bot]eq_sym -eq_meetl => /eqP ->. Qed.

Lemma disj_leC x y : y `&` x == \bot -> (x <= y) = (x == \bot).
Proof. by rewrite meetC => /disj_le. Qed.

Lemma disj_diffl x y : x `&` y == \bot -> x `\` y = x.
Proof. by move=> dxy; apply/eqP; rewrite eq_diff dxy lexx leUr. Qed.

Lemma disj_diffr x y : x `&` y == \bot -> y `\` x = y.
Proof. by rewrite meetC => /disj_diffl. Qed.

Lemma lt0B x y : x < y -> \bot < y `\` x.
Proof. by move=> ?; rewrite lt_leAnge le0x leBLR joinx0 /= lt_geF. Qed.

End CBDistrLatticeTheory.
End CBDistrLatticeTheory.

Module Import CTDistrLatticeTheory.
Section CTDistrLatticeTheory.
Context {disp : disp_t} {L : ctDistrLatticeType disp}.
Implicit Types (x y z : L).

Lemma codiffErcompl x y : codiff x y = rcompl x \top y.
Proof. exact: codiffErcompl. Qed.

(* TODO: complete this theory module *)

End CTDistrLatticeTheory.
End CTDistrLatticeTheory.

Module Import CTBDistrLatticeTheory.
Section CTBDistrLatticeTheory.
Context {disp : disp_t} {L : ctbDistrLatticeType disp}.
Implicit Types (x y z : L).

Lemma complEdiff x : ~` x = \top `\` x. Proof. exact: complEdiff. Qed.
#[deprecated(since="mathcomp 2.3.0", use=complEdiff)]
Notation complE := complEdiff.

Lemma complEcodiff x : ~` x = codiff \bot x. Proof. exact: complEcodiff. Qed.

Lemma complErcompl x : ~` x = rcompl \bot \top x.
Proof. by rewrite complEdiff diffErcompl. Qed.

Lemma diff1x x : \top `\` x = ~` x.
Proof. exact/esym/complEdiff. Qed.

Lemma diffE x y : x `\` y = x `&` ~` y.
Proof. by rewrite complEdiff meetxB meetx1. Qed.

Lemma complK : involutive (@compl _ L).
Proof. by move=> x; rewrite !complEdiff diffxB diffxx meet1x join0x. Qed.

Lemma compl_inj : injective (@compl _ L).
Proof. exact/inv_inj/complK. Qed.

Lemma disj_leC x y : (x `&` y == \bot) = (x <= ~` y).
Proof. by rewrite -diff_eq0 diffE complK. Qed.

Lemma leCx x y : (~` x <= y) = (~` y <= x).
Proof. by rewrite !complEdiff !leBLR joinC. Qed.

Lemma lexC x y : (x <= ~` y) = (y <= ~` x).
Proof. by rewrite -[x in LHS]complK leCx complK. Qed.

Lemma leC x y : (~` x <= ~` y) = (y <= x).
Proof. by rewrite leCx complK. Qed.

Lemma complU x y : ~` (x `|` y) = ~` x `&` ~` y.
Proof. by rewrite !complEdiff diffxU. Qed.

Lemma complI  x y : ~` (x `&` y) = ~` x `|` ~` y.
Proof. by rewrite !complEdiff diffxI. Qed.

Lemma joinxC  x :  x `|` ~` x = \top.
Proof. by rewrite complEdiff diffKU joinx1. Qed.

Lemma joinCx  x : ~` x `|` x = \top.
Proof. by rewrite joinC joinxC. Qed.

Lemma meetxC  x :  x `&` ~` x = \bot.
Proof. by rewrite complEdiff diffKI. Qed.

Lemma meetCx  x : ~` x `&` x = \bot.
Proof. by rewrite meetC meetxC. Qed.

Lemma compl1 : ~` \top = \bot :> L.
Proof. by rewrite complEdiff diffxx. Qed.

Lemma compl0 : ~` \bot = \top :> L.
Proof. by rewrite -compl1 complK. Qed.

Lemma complB x y : ~` (x `\` y) = ~` x `|` y.
Proof. by rewrite diffE complI complK. Qed.

Lemma leBC x y : x `\` y <= ~` y.
Proof. by rewrite leBLR joinxC lex1. Qed.

Lemma compl_joins (J : Type) (r : seq J) (P : {pred J}) (F : J -> L) :
   ~` (\join_(j <- r | P j) F j) = \meet_(j <- r | P j) ~` F j.
Proof. by elim/big_rec2: _=> [|i x y ? <-]; rewrite ?compl0 ?complU. Qed.

Lemma compl_meets (J : Type) (r : seq J) (P : {pred J}) (F : J -> L) :
   ~` (\meet_(j <- r | P j) F j) = \join_(j <- r | P j) ~` F j.
Proof. by elim/big_rec2: _=> [|i x y ? <-]; rewrite ?compl1 ?complI. Qed.

End CTBDistrLatticeTheory.
End CTBDistrLatticeTheory.

(*************)
(* FACTORIES *)
(*************)

HB.factory Record BDistrLattice_hasSectionalComplement d T
    & BDistrLattice d T := {
  diff : T -> T -> T;
  diffKI : forall x y, y `&` diff x y = \bot;
  joinIB : forall x y, (x `&` y) `|` diff x y = x;
}.

Module hasRelativeComplement.
#[deprecated(since="mathcomp 2.3.0",
  use=BDistrLattice_hasSectionalComplement.Build)]
Notation Build d T :=
  (BDistrLattice_hasSectionalComplement.Build d T) (only parsing).
End hasRelativeComplement.

#[deprecated(since="mathcomp 2.3.0", use=BDistrLattice_hasSectionalComplement)]
Notation hasRelativeComplement d T :=
  (BDistrLattice_hasSectionalComplement d T) (only parsing).

HB.builders Context d T & BDistrLattice_hasSectionalComplement d T.

Definition rcompl x y z := (x `&` y) `|` diff (y `|` x) z.

Fact rcomplPmeet x y z : ((x `&` y) `|` z) `&` rcompl x y z = x `&` y.
Proof. by rewrite meetUr joinIKC meetUl diffKI joinx0 meetKU. Qed.

Fact rcomplPjoin x y z : ((y `|` x) `&` z) `|` rcompl x y z = y `|` x.
Proof. by rewrite joinCA joinIB joinA meetUK joinC. Qed.

HB.instance Definition _ :=
  @DistrLattice_hasRelativeComplement.Build d T rcompl rcomplPmeet rcomplPjoin.

Fact diffErcompl x y : diff x y = rcompl \bot x y.
Proof. by rewrite /rcompl meet0x join0x joinx0. Qed.

HB.instance Definition _ :=
  @CDistrLattice_hasSectionalComplement.Build d T diff diffErcompl.

HB.end.

HB.factory Record TDistrLattice_hasDualSectionalComplement d T
    & TDistrLattice d T := {
  codiff : T -> T -> T;
  codiffKU : forall x y, y `|` codiff x y = \top;
  meetUB : forall x y, (x `|` y) `&` codiff x y = x;
}.

HB.builders Context d T & TDistrLattice_hasDualSectionalComplement d T.

Definition rcompl x y z := (y `|` x) `&` codiff (x `&` y) z.

Fact rcomplPmeet x y z : ((x `&` y) `|` z) `&` rcompl x y z = x `&` y.
Proof. by rewrite meetCA meetUB meetA joinIK. Qed.

Fact rcomplPjoin x y z : ((y `|` x) `&` z) `|` rcompl x y z = y `|` x.
Proof. by rewrite joinIr meetUKC joinIl codiffKU meetx1 joinKI. Qed.

HB.instance Definition _ :=
  @DistrLattice_hasRelativeComplement.Build d T rcompl rcomplPmeet rcomplPjoin.

Fact codiffErcompl x y : codiff x y = rcompl x \top y.
Proof. by rewrite /rcompl join1x meet1x meetx1. Qed.

HB.instance Definition _ :=
  @CDistrLattice_hasDualSectionalComplement.Build d T codiff codiffErcompl.

HB.end.

HB.factory Record CBDistrLattice_hasComplement d T
    & CBDistrLattice d T & hasTop d T := {
  compl : T -> T;
  complEdiff : forall x, compl x = (\top : T) `\` x; (* FIXME *)
}.

Module hasComplement.
#[deprecated(since="mathcomp 2.3.0", use=CBDistrLattice_hasComplement.Build)]
Notation Build d T := (CBDistrLattice_hasComplement.Build d T) (only parsing).
End hasComplement.

#[deprecated(since="mathcomp 2.3.0", use=CBDistrLattice_hasComplement)]
Notation hasComplement d T := (CBDistrLattice_hasComplement d T) (only parsing).

HB.builders Context d T & CBDistrLattice_hasComplement d T.

HB.instance Definition _ := @CDistrLattice_hasDualSectionalComplement.Build d T
  (fun x y => rcompl x \top y) (fun _ _ => erefl).

Fact complEcodiff (x : T) : compl x = codiff (\bot : T) x.
Proof. by rewrite complEdiff diffErcompl. Qed.

HB.instance Definition _ :=
  @CDistrLattice_hasComplement.Build d T compl complEdiff complEcodiff.

HB.end.

HB.factory Record CTDistrLattice_hasComplement d T
    & CTDistrLattice d T & hasBottom d T := {
  compl : T -> T;
  complEcodiff : forall x, compl x = codiff (\bot : T) x;
}.

HB.builders Context d T & CTDistrLattice_hasComplement d T.

HB.instance Definition _ := @CDistrLattice_hasSectionalComplement.Build d T
  (fun x y => rcompl (\bot : T) x y) (fun _ _ => erefl).

Fact complEdiff (x : T) : compl x = (\top : T) `\` x.
Proof. by rewrite complEcodiff codiffErcompl. Qed.

HB.instance Definition _ :=
  @CDistrLattice_hasComplement.Build d T compl complEdiff complEcodiff.

HB.end.

HB.factory Record TBDistrLattice_hasComplement d T & TBDistrLattice d T := {
  compl : T -> T;
  joinxC : forall x, x `|` compl x = \top;
  meetxC : forall x, x `&` compl x = \bot;
}.

HB.builders Context d T & TBDistrLattice_hasComplement d T.

Definition diff x y := x `&` compl y.
Definition codiff x y := x `|` compl y.
Definition rcompl x y z := (x `&` y) `|` diff (y `|` x) z.

Fact diffKI x y : y `&` diff x y = \bot.
Proof. by rewrite meetCA meetxC meetx0. Qed.

Fact joinIB x y : (x `&` y) `|` diff x y = x.
Proof. by rewrite -meetUr joinxC meetx1. Qed.

HB.instance Definition _ :=
  @BDistrLattice_hasSectionalComplement.Build d T diff diffKI joinIB.

Fact codiffErcompl x y : codiff x y = rcompl x \top y.
Proof. by rewrite /rcompl /diff join1x meetx1 meet1x. Qed.

HB.instance Definition _ :=
  @CDistrLattice_hasDualSectionalComplement.Build d T codiff codiffErcompl.

Fact complEdiff x : compl x = diff \top x. Proof. exact/esym/meet1x. Qed.
Fact complEcodiff x : compl x = codiff \bot x. Proof. exact/esym/join0x. Qed.

HB.instance Definition _ :=
  @CDistrLattice_hasComplement.Build d T compl complEdiff complEcodiff.

HB.end.

Module Theory.
Export Order.Theory.
Export CDistrLatticeTheory.
Export CBDistrLatticeTheory.
Export CTDistrLatticeTheory.
Export CTBDistrLatticeTheory.
End Theory.

Module Exports.
HB.reexport.
End Exports.
End Order.

Export Order.Exports.

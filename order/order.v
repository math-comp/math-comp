(* (c) Copyright 2006-2019 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import path fintype tuple finfun bigop finset.
From mathcomp Require Import preorder porder lattice.

(******************************************************************************)
(*                   Types equipped with order relations                      *)
(*                                                                            *)
(* NB: See CONTRIBUTING.md for an introduction to HB concepts and commands.   *)
(*                                                                            *)
(* NB: See the header of all_order.v for general remarks about the preorder   *)
(*     and order structures in MathComp, and the files in this directory.     *)
(*                                                                            *)
(* * Interfaces                                                               *)
(* We provide the following interfaces for types equipped with an order:      *)
(*                                                                            *)
(*               orderType d == the type of totally ordered types             *)
(*                              The HB class is called Total.                 *)
(*              bOrderType d == orderType with a bottom element               *)
(*                              The HB class is called BTotal.                *)
(*              tOrderType d == orderType with a top element                  *)
(*                              The HB class is called TTotal.                *)
(*             tbOrderType d == orderType with both a top and a bottom        *)
(*                              The HB class is called TBTotal.               *)
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
(*            finOrderType d == the type of totally ordered finite types      *)
(*                              The HB class is called FinTotal.              *)
(*          finTBOrderType d == the type of nonempty totally ordered finite   *)
(*                              types                                         *)
(*                              The HB class is called FinTBTotal.            *)
(*    finCDistrLatticeType d == the type of finite relatively complemented    *)
(*                              distributive lattices                         *)
(*                              The HB class is called FinCDistrLattice.      *)
(*  finCTBDistrLatticeType d == the type of finite complemented distributive  *)
(*                              lattices                                      *)
(*                              The HB class is called FinCTBDistrLattice.    *)
(*                                                                            *)
(* and their joins with subType:                                              *)
(*                                                                            *)
(*           subOrder d T P d' == join of orderType d' and                    *)
(*                                subLatticeType d T P d'                     *)
(*                                The HB class is called SubOrder.            *)
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
(* The following notations are provided to build substructures:               *)
(* [SubLattice_isSubOrder of U by <: with disp] ==                            *)
(* [SubLattice_isSubOrder of U by <:] ==                                      *)
(* [SubPOrder_isSubOrder of U by <: with disp] ==                             *)
(* [SubPOrder_isSubOrder of U by <:] ==                                       *)
(* [SubChoice_isSubOrder of U by <: with disp] ==                             *)
(* [SubChoice_isSubOrder of U by <:] == orderType mixin for a subType whose   *)
(*                          base type is an orderType                         *)
(*   [POrder of U by <:] == porderType mixin for a subType whose base type is *)
(*                          a porderType                                      *)
(*    [Order of U by <:] == orderType mixin for a subType whose base type is  *)
(*                          an orderType                                      *)
(*                                                                            *)
(* Acknowledgments: The files in this directory are based on prior work by    *)
(* D. Dreyer, G. Gonthier, A. Nanevski, P-Y Strub, B. Ziliani                 *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope order_scope.

Delimit Scope order_scope with O.
Local Open Scope order_scope.

Module Order.

Export Order.
Import Order.Theory.

#[key="T", primitive]
HB.mixin Record DistrLattice_isTotal d T & DistrLattice d T :=
  { le_total : total (<=%O : rel T) }.

#[short(type="orderType")]
HB.structure Definition Total d :=
  { T of DistrLattice_isTotal d T & DistrLattice d T }.

#[short(type="bOrderType")]
HB.structure Definition BTotal d := { T of Total d T & hasBottom d T }.

#[short(type="tOrderType")]
HB.structure Definition TTotal d := { T of Total d T & hasTop d T }.

#[short(type="tbOrderType")]
HB.structure Definition TBTotal d := { T of BTotal d T & hasTop d T }.

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

Module Import CBDistrLatticeSyntax.
Notation "x `\` y" := (diff x y) : order_scope.
End CBDistrLatticeSyntax.

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

(**********)
(* FINITE *)
(**********)

#[short(type="finOrderType")]
HB.structure Definition FinTotal d := { T of Finite T & Total d T }.

#[short(type="finTBOrderType")]
HB.structure Definition FinTBTotal d := { T of Finite T & TBTotal d T }.

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

HB.instance Definition _ d (T : orderType d) :=
  DistrLattice_isTotal.Build (dual_display d) T^d (fun x y => le_total y x).

HB.saturate.

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

Module Import TotalTheory.
Section TotalTheory.
Context {disp : disp_t} {T : orderType disp}.
Implicit Types (x y z t : T) (s : seq T).

Definition le_total : total (<=%O : rel T) := le_total.
Hint Resolve le_total : core.

Lemma ge_total : total (>=%O : rel T).
Proof. by move=> ? ?; apply: le_total. Qed.
Hint Resolve ge_total : core.

Lemma comparableT x y : x >=< y. Proof. exact: le_total. Qed.
Hint Extern 0 (is_true (_ >=< _)%O) => solve [apply: comparableT] : core.

Lemma sort_le_sorted s : sorted <=%O (sort <=%O s).
Proof. exact: sort_sorted. Qed.
Hint Resolve sort_le_sorted : core.

Lemma sort_lt_sorted s : sorted <%O (sort <=%O s) = uniq s.
Proof. by rewrite lt_sorted_uniq_le sort_uniq sort_le_sorted andbT. Qed.

Lemma perm_sort_leP s1 s2 : reflect (sort <=%O s1 = sort <=%O s2) (perm_eq s1 s2).
Proof. exact/perm_sortP/le_anti/le_trans/le_total. Qed.

Lemma filter_sort_le p s : filter p (sort <=%O s) = sort <=%O (filter p s).
Proof. exact/filter_sort/le_trans/le_total. Qed.

Lemma mask_sort_le s (m : bitseq) :
  {m_s : bitseq | mask m_s (sort <=%O s) = sort <=%O (mask m s)}.
Proof. exact/mask_sort/le_trans/le_total. Qed.

Lemma sorted_mask_sort_le s (m : bitseq) :
  sorted <=%O (mask m s) -> {m_s : bitseq | mask m_s (sort <=%O s) = mask m s}.
Proof. exact/sorted_mask_sort/le_trans/le_total. Qed.

Lemma subseq_sort_le : {homo sort <=%O : s1 s2 / @subseq T s1 s2}.
Proof. exact/subseq_sort/le_trans/le_total. Qed.

Lemma sorted_subseq_sort_le s1 s2 :
  subseq s1 s2 -> sorted <=%O s1 -> subseq s1 (sort <=%O s2).
Proof. exact/sorted_subseq_sort/le_trans/le_total. Qed.

Lemma mem2_sort_le s x y : x <= y -> mem2 s x y -> mem2 (sort <=%O s) x y.
Proof. exact/mem2_sort/le_trans/le_total. Qed.

Lemma leNgt x y : (x <= y) = ~~ (y < x). Proof. exact: comparable_leNgt. Qed.

Lemma ltNge x y : (x < y) = ~~ (y <= x). Proof. exact: comparable_ltNge. Qed.

Definition ltgtP x y := LatticeTheory.lcomparable_ltgtP (comparableT x y).
Definition leP x y := LatticeTheory.lcomparable_leP (comparableT x y).
Definition ltP x y := LatticeTheory.lcomparable_ltP (comparableT x y).

Lemma wlog_le P :
     (forall x y, P y x -> P x y) -> (forall x y, x <= y -> P x y) ->
   forall x y, P x y.
Proof. by move=> sP hP x y; case: (leP x y) => [| /ltW] /hP // /sP. Qed.

Lemma wlog_lt P :
    (forall x, P x x) ->
    (forall x y, (P y x -> P x y)) -> (forall x y, x < y -> P x y) ->
  forall x y, P x y.
Proof. by move=> rP sP hP x y; case: (ltgtP x y) => [||->] // /hP // /sP. Qed.

Lemma neq_lt x y : (x != y) = (x < y) || (y < x). Proof. by case: ltgtP. Qed.

Lemma lt_total x y : x != y -> (x < y) || (y < x). Proof. by case: ltgtP. Qed.

Lemma eq_leLR x y z t :
  (x <= y -> z <= t) -> (y < x -> t < z) -> (x <= y) = (z <= t).
Proof. by rewrite !ltNge => ? /contraTT ?; apply/idP/idP. Qed.

Lemma eq_leRL x y z t :
  (x <= y -> z <= t) -> (y < x -> t < z) -> (z <= t) = (x <= y).
Proof. by move=> *; apply/esym/eq_leLR. Qed.

Lemma eq_ltLR x y z t :
  (x < y -> z < t) -> (y <= x -> t <= z) -> (x < y) = (z < t).
Proof. by rewrite !leNgt => ? /contraTT ?; apply/idP/idP. Qed.

Lemma eq_ltRL x y z t :
  (x < y -> z < t) -> (y <= x -> t <= z) -> (z < t) = (x < y).
Proof. by move=> *; apply/esym/eq_ltLR. Qed.

Lemma le_gtP {x y} : reflect (forall z, z < x -> z < y) (x <= y).
Proof.
by apply: (iffP idP) => [xy z /lt_le_trans|/(_ y)/[!ltNge]/contraTT]; apply.
Qed.

Lemma le_ltP {x y} : reflect (forall z, y < z -> x < z) (x <= y).
Proof.
by apply: (iffP idP) => [xy z /(le_lt_trans _)|/(_ x)/[!ltNge]/contraTT]; apply.
Qed.

Lemma eq_gtP {x y} : reflect (forall z, (z < x) = (z < y)) (x == y).
Proof.
by apply: (iffP eq_leP) => + k => /(_ k)/[!ltNge]/(congr1 negb); rewrite ?negbK.
Qed.

Lemma eq_ltP {x y} : reflect (forall z, (x < z) = (y < z)) (x == y).
Proof.
by apply: (iffP eq_geP) => + k => /(_ k)/[!ltNge]/(congr1 negb); rewrite ?negbK.
Qed.

(* max and min is join and meet *)

Lemma meetEtotal x y : x `&` y = min x y. Proof. by case: leP. Qed.
Lemma joinEtotal x y : x `|` y = max x y. Proof. by case: leP. Qed.

(* max and min theory *)

Lemma minEgt x y : min x y = if x > y then y else x. Proof. by case: ltP. Qed.
Lemma maxEgt x y : max x y = if x > y then x else y. Proof. by case: ltP. Qed.
Lemma minEge x y : min x y = if x >= y then y else x. Proof. by case: leP. Qed.
Lemma maxEge x y : max x y = if x >= y then x else y. Proof. by case: leP. Qed.

Lemma minC : commutative (min : T -> T -> T).
Proof. by move=> x y; apply: comparable_minC. Qed.

Lemma maxC : commutative (max : T -> T -> T).
Proof. by move=> x y; apply: comparable_maxC. Qed.

Lemma minA : associative (min : T -> T -> T).
Proof. by move=> x y z; apply: comparable_minA. Qed.

Lemma maxA : associative (max : T -> T -> T).
Proof. by move=> x y z; apply: comparable_maxA. Qed.

Lemma minAC : right_commutative (min : T -> T -> T).
Proof. by move=> x y z; apply: comparable_minAC. Qed.

Lemma maxAC : right_commutative (max : T -> T -> T).
Proof. by move=> x y z; apply: comparable_maxAC. Qed.

Lemma minCA : left_commutative (min : T -> T -> T).
Proof. by move=> x y z; apply: comparable_minCA. Qed.

Lemma maxCA : left_commutative (max : T -> T -> T).
Proof. by move=> x y z; apply: comparable_maxCA. Qed.

Lemma minACA : interchange (min : T -> T -> T) min.
Proof. by move=> x y z t; apply: comparable_minACA. Qed.

Lemma maxACA : interchange (max : T -> T -> T) max.
Proof. by move=> x y z t; apply: comparable_maxACA. Qed.

Lemma eq_minr x y : (min x y == y) = (y <= x).
Proof. exact: comparable_eq_minr. Qed.

Lemma eq_maxl x y : (max x y == x) = (y <= x).
Proof. exact: comparable_eq_maxl. Qed.

Lemma min_idPr x y : reflect (min x y = y) (y <= x).
Proof. exact: comparable_min_idPr. Qed.

Lemma max_idPl x y : reflect (max x y = x) (y <= x).
Proof. exact: comparable_max_idPl. Qed.

Lemma le_min z x y : (z <= min x y) = (z <= x) && (z <= y).
Proof. exact: comparable_le_min. Qed.

Lemma ge_min z x y : (min x y <= z) = (x <= z) || (y <= z).
Proof. exact: comparable_ge_min. Qed.

Lemma lt_min z x y : (z < min x y) = (z < x) && (z < y).
Proof. exact: comparable_lt_min. Qed.

Lemma gt_min z x y : (min x y < z) = (x < z) || (y < z).
Proof. exact: comparable_gt_min. Qed.

Lemma le_max z x y : (z <= max x y) = (z <= x) || (z <= y).
Proof. exact: comparable_le_max. Qed.

Lemma ge_max z x y : (max x y <= z) = (x <= z) && (y <= z).
Proof. exact: comparable_ge_max. Qed.

Lemma lt_max z x y : (z < max x y) = (z < x) || (z < y).
Proof. exact: comparable_lt_max. Qed.

Lemma gt_max z x y : (max x y < z) = (x < z) && (y < z).
Proof. exact: comparable_gt_max. Qed.

Lemma minxK x y : max (min x y) y = y. Proof. exact: comparable_minxK. Qed.
Lemma minKx x y : max x (min x y) = x. Proof. exact: comparable_minKx. Qed.
Lemma maxxK x y : min (max x y) y = y. Proof. exact: comparable_maxxK. Qed.
Lemma maxKx x y : min x (max x y) = x. Proof. exact: comparable_maxKx. Qed.

Lemma max_minl : left_distributive (max : T -> T -> T) min.
Proof. by move=> x y z; apply: comparable_max_minl. Qed.

Lemma min_maxl : left_distributive (min : T -> T -> T) max.
Proof. by move=> x y z; apply: comparable_min_maxl. Qed.

Lemma max_minr : right_distributive (max : T -> T -> T) min.
Proof. by move=> x y z; apply: comparable_max_minr. Qed.

Lemma min_maxr : right_distributive (min : T -> T -> T) max.
Proof. by move=> x y z; apply: comparable_min_maxr. Qed.

HB.instance Definition _ := SemiGroup.isComLaw.Build T max maxA maxC.
HB.instance Definition _ := SemiGroup.isComLaw.Build T min minA minC.

Lemma leIx x y z : (meet y z <= x) = (y <= x) || (z <= x).
Proof. by rewrite meetEtotal ge_min. Qed.

Lemma lexU x y z : (x <= join y z) = (x <= y) || (x <= z).
Proof. by rewrite joinEtotal le_max. Qed.

Lemma ltxI x y z : (x < meet y z) = (x < y) && (x < z).
Proof. by rewrite !ltNge leIx negb_or. Qed.

Lemma ltIx x y z : (meet y z < x) = (y < x) || (z < x).
Proof. by rewrite !ltNge lexI negb_and. Qed.

Lemma ltxU x y z : (x < join y z) = (x < y) || (x < z).
Proof. by rewrite !ltNge leUx negb_and. Qed.

Lemma ltUx x y z : (join y z < x) = (y < x) && (z < x).
Proof. by rewrite !ltNge lexU negb_or. Qed.

Definition ltexI := (@lexI _ T, ltxI).
Definition lteIx := (leIx, ltIx).
Definition ltexU := (lexU, ltxU).
Definition lteUx := (@leUx _ T, ltUx).

Lemma le_min2 x y z t : x <= z -> y <= t -> Order.min x y <= Order.min z t.
Proof. exact: comparable_le_min2. Qed.

Lemma le_max2 x y z t : x <= z -> y <= t -> Order.max x y <= Order.max z t.
Proof. exact: comparable_le_max2. Qed.

(* lteif *)

Lemma lteifNE x y C : (x < y ?<= if ~~ C) = ~~ (y < x ?<= if C).
Proof. by case: C => /=; case: leP. Qed.

Lemma lteif_minr z x y C :
  (z < min x y ?<= if C) = (z < x ?<= if C) && (z < y ?<= if C).
Proof. by case: C; rewrite /= (le_min, lt_min). Qed.

Lemma lteif_minl z x y C :
  (min x y < z ?<= if C) = (x < z ?<= if C) || (y < z ?<= if C).
Proof. by case: C; rewrite /= (ge_min, gt_min). Qed.

Lemma lteif_maxr z x y C :
  (z < max x y ?<= if C) = (z < x ?<= if C) || (z < y ?<= if C).
Proof. by case: C; rewrite /= (le_max, lt_max). Qed.

Lemma lteif_maxl z x y C :
  (max x y < z ?<= if C) = (x < z ?<= if C) && (y < z ?<= if C).
Proof. by case: C; rewrite /= (ge_max, gt_max). Qed.

Section ArgExtremum.
Context (I : finType) (i0 : I) (P : {pred I}) (F : I -> T) (Pi0 : P i0).

Lemma arg_minP: extremum_spec <=%O P F (arg_min i0 P F).
Proof. by apply: extremumP => //; apply: le_trans. Qed.

Lemma arg_maxP: extremum_spec >=%O P F (arg_max i0 P F).
Proof. by apply: extremumP => //; [apply: ge_refl | apply: ge_trans]. Qed.

End ArgExtremum.

Lemma count_le_gt x s : count (<= x) s = size s - count (> x) s.
Proof.
by rewrite -(count_predC (> x)) addKn; apply: eq_count => y; rewrite /= leNgt.
Qed.

Lemma count_lt_ge x s : count (< x) s = size s - count (>= x) s.
Proof.
by rewrite -(count_predC (>= x)) addKn; apply: eq_count => y; rewrite /= ltNge.
Qed.

Section bigminmax_Type.
Context (I : Type) (r : seq I) (x : T).
Implicit Types (P : pred I) (F : I -> T).

Lemma bigmin_mkcond P F : \big[min/x]_(i <- r | P i) F i =
  \big[min/x]_(i <- r) (if P i then F i else x).
Proof. by rewrite big_mkcond_idem //= minxx. Qed.

Lemma bigmax_mkcond P F :
  \big[max/x]_(i <- r | P i) F i = \big[max/x]_(i <- r) if P i then F i else x.
Proof. by rewrite big_mkcond_idem //= maxxx. Qed.

Lemma bigmin_mkcondl P Q F :
  \big[min/x]_(i <- r | P i && Q i) F i
  = \big[min/x]_(i <- r | Q i) if P i then F i else x.
Proof.
rewrite bigmin_mkcond [RHS]bigmin_mkcond.
by apply: eq_bigr => i _; case: P; case: Q.
Qed.

Lemma bigmin_mkcondr P Q F :
  \big[min/x]_(i <- r | P i && Q i) F i
  = \big[min/x]_(i <- r | P i) if Q i then F i else x.
Proof. by under eq_bigl do rewrite andbC; apply: bigmin_mkcondl. Qed.

Lemma bigmax_mkcondl P Q F :
  \big[max/x]_(i <- r | P i && Q i) F i
  = \big[max/x]_(i <- r | Q i) if P i then F i else x.
Proof.
rewrite bigmax_mkcond [RHS]bigmax_mkcond.
by apply: eq_bigr => i _; case: P; case: Q.
Qed.

Lemma bigmax_mkcondr P Q F :
  \big[max/x]_(i <- r | P i && Q i) F i
  = \big[max/x]_(i <- r | P i) if Q i then F i else x.
Proof. by under eq_bigl do rewrite andbC; apply: bigmax_mkcondl. Qed.

Lemma bigmin_split P F1 F2 :
  \big[min/x]_(i <- r | P i) (min (F1 i) (F2 i)) =
    min (\big[min/x]_(i <- r | P i) F1 i) (\big[min/x]_(i <- r | P i) F2 i).
Proof. by rewrite big_split_idem //= minxx. Qed.

Lemma bigmax_split P F1 F2 :
  \big[max/x]_(i <- r | P i) (max (F1 i) (F2 i)) =
    max (\big[max/x]_(i <- r | P i) F1 i) (\big[max/x]_(i <- r | P i) F2 i).
Proof. by rewrite big_split_idem //= maxxx. Qed.

Lemma bigmin_idl P F :
  \big[min/x]_(i <- r | P i) F i = min x (\big[min/x]_(i <- r | P i) F i).
Proof. by rewrite minC big_id_idem //= minxx. Qed.

Lemma bigmax_idl P F :
  \big[max/x]_(i <- r | P i) F i = max x (\big[max/x]_(i <- r | P i) F i).
Proof. by rewrite maxC big_id_idem //= maxxx. Qed.

Lemma bigmin_idr P F :
  \big[min/x]_(i <- r | P i) F i = min (\big[min/x]_(i <- r | P i) F i) x.
Proof. by rewrite [LHS]bigmin_idl minC. Qed.

Lemma bigmax_idr P F :
  \big[max/x]_(i <- r | P i) F i = max (\big[max/x]_(i <- r | P i) F i) x.
Proof. by rewrite [LHS]bigmax_idl maxC. Qed.

Lemma bigminID a P F : \big[min/x]_(i <- r | P i) F i =
  min (\big[min/x]_(i <- r | P i && a i) F i)
      (\big[min/x]_(i <- r | P i && ~~ a i) F i).
Proof. by rewrite (bigID_idem _ _ a) //= minxx. Qed.

Lemma bigmaxID a P F : \big[max/x]_(i <- r | P i) F i =
  max (\big[max/x]_(i <- r | P i && a i) F i)
      (\big[max/x]_(i <- r | P i && ~~ a i) F i).
Proof. by rewrite (bigID_idem _ _ a) //= maxxx. Qed.

End bigminmax_Type.

Let ge_min_id (x y : T) : x >= min x y. Proof. by rewrite ge_min lexx. Qed.
Let le_max_id (x y : T) : x <= max x y. Proof. by rewrite le_max lexx. Qed.

Lemma sub_bigmin [x0] I r (P P' : {pred I}) (F : I -> T) :
    (forall i, P' i -> P i) ->
  \big[min/x0]_(i <- r | P i) F i <= \big[min/x0]_(i <- r | P' i) F i.
Proof. exact: (sub_le_big ge_refl). Qed.

Lemma sub_bigmax [x0] I r (P P' : {pred I}) (F : I -> T) :
    (forall i, P i -> P' i) ->
  \big[max/x0]_(i <- r | P i) F i <= \big[max/x0]_(i <- r | P' i) F i.
Proof. exact: sub_le_big. Qed.

Lemma sub_bigmin_seq [x0] (I : eqType) r r' P (F : I -> T) : {subset r' <= r} ->
  \big[min/x0]_(i <- r | P i) F i <= \big[min/x0]_(i <- r' | P i) F i.
Proof. exact: (idem_sub_le_big ge_refl _ minxx). Qed.

Lemma sub_bigmax_seq [x0] (I : eqType) r r' P (F : I -> T) : {subset r <= r'} ->
  \big[max/x0]_(i <- r | P i) F i <= \big[max/x0]_(i <- r' | P i) F i.
Proof. exact: (idem_sub_le_big _ _ maxxx). Qed.

Lemma sub_bigmin_cond [x0] (I : eqType) r r' P P' (F : I -> T) :
    {subset [seq i <- r | P i] <= [seq i <- r' | P' i]} ->
  \big[min/x0]_(i <- r' | P' i) F i <= \big[min/x0]_(i <- r | P i) F i.
Proof. exact: (idem_sub_le_big_cond ge_refl _ minxx). Qed.

Lemma sub_bigmax_cond [x0] (I : eqType) r r' P P' (F : I -> T) :
    {subset [seq i <- r | P i] <= [seq i <- r' | P' i]} ->
  \big[max/x0]_(i <- r | P i) F i <= \big[max/x0]_(i <- r' | P' i) F i.
Proof. exact: (idem_sub_le_big_cond _ _ maxxx). Qed.

Lemma sub_in_bigmin [x0] [I : eqType] (r : seq I) (P P' : {pred I}) F :
    {in r, forall i, P' i -> P i} ->
  \big[min/x0]_(i <- r | P i) F i <= \big[min/x0]_(i <- r | P' i) F i.
Proof. exact: (sub_in_le_big ge_refl). Qed.

Lemma sub_in_bigmax [x0] [I : eqType] (r : seq I) (P P' : {pred I}) F :
    {in r, forall i, P i -> P' i} ->
  \big[max/x0]_(i <- r | P i) F i <= \big[max/x0]_(i <- r | P' i) F i.
Proof. exact: sub_in_le_big. Qed.

Lemma le_bigmin_nat [x0] n m n' m' P (F : nat -> T) :
    (n <= n')%N -> (m' <= m)%N ->
  \big[min/x0]_(n <= i < m | P i) F i <= \big[min/x0]_(n' <= i < m' | P i) F i.
Proof. exact: (le_big_nat ge_refl). Qed.

Lemma le_bigmax_nat [x0] n m n' m' P (F : nat -> T) :
    (n' <= n)%N -> (m <= m')%N ->
  \big[max/x0]_(n <= i < m | P i) F i <= \big[max/x0]_(n' <= i < m' | P i) F i.
Proof. exact: le_big_nat. Qed.

Lemma le_bigmin_nat_cond [x0] n m n' m' (P P' : pred nat) (F : nat -> T) :
    (n <= n')%N -> (m' <= m)%N -> (forall i, (n' <= i < m')%N -> P' i -> P i) ->
  \big[min/x0]_(n <= i < m | P i) F i <= \big[min/x0]_(n' <= i < m' | P' i) F i.
Proof. exact: (le_big_nat_cond ge_refl). Qed.

Lemma le_bigmax_nat_cond [x0] n m n' m' (P P' : {pred nat}) (F : nat -> T) :
    (n' <= n)%N -> (m <= m')%N -> (forall i, (n <= i < m)%N -> P i -> P' i) ->
  \big[max/x0]_(n <= i < m | P i) F i <= \big[max/x0]_(n' <= i < m' | P' i) F i.
Proof. exact: le_big_nat_cond. Qed.

Lemma le_bigmin_ord [x0] n m (P : pred nat) (F : nat -> T) : (m <= n)%N ->
  \big[min/x0]_(i < n | P i) F i <= \big[min/x0]_(i < m | P i) F i.
Proof. exact: (le_big_ord ge_refl). Qed.

Lemma le_bigmax_ord [x0] n m (P : {pred nat}) (F : nat -> T) : (n <= m)%N ->
  \big[max/x0]_(i < n | P i) F i <= \big[max/x0]_(i < m | P i) F i.
Proof. exact: le_big_ord. Qed.

Lemma le_bigmin_ord_cond [x0] n m (P P' : pred nat) (F : nat -> T) :
    (m <= n)%N -> (forall i : 'I_m, P' i -> P i) ->
  \big[min/x0]_(i < n | P i) F i <= \big[min/x0]_(i < m | P' i) F i.
Proof. exact: (le_big_ord_cond ge_refl). Qed.

Lemma le_bigmax_ord_cond [x0] n m (P P' : {pred nat}) (F : nat -> T) :
    (n <= m)%N -> (forall i : 'I_n, P i -> P' i) ->
  \big[max/x0]_(i < n | P i) F i <= \big[max/x0]_(i < m | P' i) F i.
Proof. exact: le_big_ord_cond. Qed.

Lemma subset_bigmin [x0] [I : finType] [A A' P : {pred I}] (F : I -> T) :
    A' \subset A ->
  \big[min/x0]_(i in A | P i) F i <= \big[min/x0]_(i in A' | P i) F i.
Proof. exact: (subset_le_big ge_refl). Qed.

Lemma subset_bigmax [x0] [I : finType] (A A' P : {pred I}) (F : I -> T) :
    A \subset A' ->
  \big[max/x0]_(i in A | P i) F i <= \big[max/x0]_(i in A' | P i) F i.
Proof. exact: subset_le_big. Qed.

Lemma subset_bigmin_cond [x0] (I : finType) (A A' P P' : {pred I}) (F : I -> T) :
    [set i in A' | P' i]  \subset [set i in A | P i] ->
  \big[min/x0]_(i in A | P i) F i <= \big[min/x0]_(i in A' | P' i) F i.
Proof. exact: (subset_le_big_cond ge_refl). Qed.

Lemma subset_bigmax_cond [x0] (I : finType) (A A' P P' : {pred I}) (F : I -> T) :
    [set i in A | P i]  \subset [set i in A' | P' i] ->
  \big[max/x0]_(i in A | P i) F i <= \big[max/x0]_(i in A' | P' i) F i.
Proof. exact: subset_le_big_cond. Qed.

Section bigminmax_Type.
Context (I : Type) (r : seq I) (x : T).
Implicit Types (P : pred I) (F : I -> T).

Lemma bigmin_le_id P F : \big[min/x]_(i <- r | P i) F i <= x.
Proof. by rewrite bigmin_idl. Qed.

Lemma bigmax_ge_id P F : \big[max/x]_(i <- r | P i) F i >= x.
Proof. by rewrite bigmax_idl. Qed.

Lemma bigmin_eq_id P F :
  (forall i, P i -> x <= F i) -> \big[min/x]_(i <- r | P i) F i = x.
Proof. by move=> x_le; apply: le_anti; rewrite bigmin_le_id le_bigmin. Qed.

Lemma bigmax_eq_id P F :
  (forall i, P i -> x >= F i) -> \big[max/x]_(i <- r | P i) F i = x.
Proof. by move=> x_ge; apply: le_anti; rewrite bigmax_ge_id bigmax_le. Qed.

End bigminmax_Type.

Section bigminmax_eqType.
Context (I : eqType) (r : seq I) (x : T).
Implicit Types (P : pred I) (F : I -> T).

Lemma ge_bigmin_seq i0 P F :
  i0 \in r -> P i0 -> \big[min/x]_(i <- r | P i) F i <= F i0.
Proof.
move=> + Pi0; elim: r => // h t ih; rewrite inE big_cons.
move=> /predU1P[<-|i0t]; first by rewrite Pi0 ge_min// lexx.
by case: ifPn => Ph; [rewrite ge_min ih// orbT|rewrite ih].
Qed.

Lemma le_bigmax_seq i0 P F :
  i0 \in r -> P i0 -> F i0 <= \big[max/x]_(i <- r | P i) F i.
Proof.
move=> + Pi0; elim: r => // h t ih; rewrite inE big_cons.
move=> /predU1P[<-|i0t]; first by rewrite Pi0 le_max// lexx.
by case: ifPn => Ph; [rewrite le_max ih// orbT|rewrite ih].
Qed.

Lemma bigmin_inf_seq i0 P t F :
  i0 \in r -> P i0 -> F i0 <= t -> \big[min/x]_(i <- r | P i) F i <= t.
Proof. by move=> ? ? ?; exact: le_trans (@ge_bigmin_seq i0 _ _ _ _) _. Qed.

Lemma bigmax_sup_seq i0 P t F :
  i0 \in r -> P i0 -> t <= F i0 -> t <= \big[max/x]_(i <- r | P i) F i.
Proof. by move=> ? ? ?; exact: le_trans (@le_bigmax_seq i0 _ _ _ _). Qed.

End bigminmax_eqType.

Section bigminmax_finType.
Context (I : finType) (x : T).
Implicit Types (P : pred I) (F : I -> T).

Lemma bigminD1 j P F : P j ->
  \big[min/x]_(i | P i) F i = min (F j) (\big[min/x]_(i | P i && (i != j)) F i).
Proof. by move/(bigD1 _) ->. Qed.

Lemma bigmaxD1 j P F : P j ->
  \big[max/x]_(i | P i) F i = max (F j) (\big[max/x]_(i | P i && (i != j)) F i).
Proof. by move/(bigD1 _) ->. Qed.

Lemma bigmin_le_cond j P F : P j -> \big[min/x]_(i | P i) F i <= F j.
Proof.
have := mem_index_enum j; rewrite unlock; elim: (index_enum I) => //= i l ih.
rewrite inE => /orP [/eqP-> ->|/ih leminlfi Pi]; first by rewrite ge_min lexx.
by case: ifPn => Pj; [rewrite ge_min leminlfi// orbC|exact: leminlfi].
Qed.

Lemma le_bigmax_cond j P F : P j -> F j <= \big[max/x]_(i | P i) F i.
Proof. by move=> Pj; rewrite (bigmaxD1 _ Pj) le_max lexx. Qed.

Lemma bigmin_le j F : \big[min/x]_i F i <= F j.
Proof. exact: bigmin_le_cond. Qed.

Lemma le_bigmax F j : F j <= \big[max/x]_i F i.
Proof. exact: le_bigmax_cond. Qed.

Lemma bigmin_inf j P m F : P j -> F j <= m -> \big[min/x]_(i | P i) F i <= m.
Proof. by move=> Pj ?; apply: le_trans (bigmin_le_cond _ Pj) _. Qed.

(* NB: as of [2022-08-02], bigop.bigmax_sup already exists for nat *)
Lemma bigmax_sup j P m F : P j -> m <= F j -> m <= \big[max/x]_(i | P i) F i.
Proof. by move=> Pj ?; apply: le_trans (le_bigmax_cond _ Pj). Qed.

Lemma bigmin_geP m P F :
  reflect (m <= x /\ forall i, P i -> m <= F i)
          (m <= \big[min/x]_(i | P i) F i).
Proof.
apply: (iffP idP) => [lemFi|[lemx lemPi]]; [split|exact: le_bigmin].
- by rewrite (le_trans lemFi)// bigmin_idl ge_min lexx.
- by move=> i Pi; rewrite (le_trans lemFi)// (bigminD1 _ Pi)// le_minl lexx.
Qed.

Lemma bigmax_leP m P F :
  reflect (x <= m /\ forall i, P i -> F i <= m)
          (\big[max/x]_(i | P i) F i <= m).
Proof.
apply: (iffP idP) => [|[? ?]]; last exact: bigmax_le.
rewrite bigmax_idl ge_max => /andP[-> leFm]; split=> // i Pi.
by apply: le_trans leFm; exact: le_bigmax_cond.
Qed.

Lemma bigmin_gtP m P F :
  reflect (m < x /\ forall i, P i -> m < F i) (m < \big[min/x]_(i | P i) F i).
Proof.
apply: (iffP idP) => [lemFi|[lemx lemPi]]; [split|exact: lt_bigmin].
- by rewrite (lt_le_trans lemFi)// bigmin_idl ge_min lexx.
- by move=> i Pi; rewrite (lt_le_trans lemFi)// (bigminD1 _ Pi)// le_minl lexx.
Qed.

Lemma bigmax_ltP m P F :
  reflect (x < m /\ forall i, P i -> F i < m) (\big[max/x]_(i | P i) F i < m).
Proof.
apply: (iffP idP) => [|[? ?]]; last exact: bigmax_lt.
rewrite bigmax_idl gt_max => /andP[-> ltFm]; split=> // i Pi.
by apply: le_lt_trans ltFm; exact: le_bigmax_cond.
Qed.

Lemma bigmin_eq_arg j P F : P j -> (forall i, P i -> F i <= x) ->
  \big[min/x]_(i | P i) F i = F [arg min_(i < j | P i) F i].
Proof.
move=> Pi0; case: arg_minP => //= i Pi PF PFx.
apply/eqP; rewrite eq_le bigmin_le_cond //=.
by apply/bigmin_geP; split => //; exact: PFx.
Qed.

Lemma bigmax_eq_arg j P F : P j -> (forall i, P i -> x <= F i) ->
  \big[max/x]_(i | P i) F i = F [arg max_(i > j | P i) F i].
Proof.
move=> Pi0; case: arg_maxP => //= i Pi PF PxF.
apply/eqP; rewrite eq_le le_bigmax_cond // andbT.
by apply/bigmax_leP; split => //; exact: PxF.
Qed.

Lemma eq_bigmin j P F : P j -> (forall i, P i -> F i <= x) ->
  {i0 | i0 \in P & \big[min/x]_(i | P i) F i = F i0}.
Proof.
by move=> Pi0 Hx; rewrite (bigmin_eq_arg Pi0) //; eexists=> //; case: arg_minP.
Qed.

Lemma eq_bigmax j P F : P j -> (forall i, P i -> x <= F i) ->
  {i0 | i0 \in P & \big[max/x]_(i | P i) F i = F i0}.
Proof.
by move=> Pi0 Hx; rewrite (bigmax_eq_arg Pi0) //; eexists=> //; case: arg_maxP.
Qed.

Lemma le_bigmin2 P F1 F2 : (forall i, P i -> F1 i <= F2 i) ->
  \big[min/x]_(i | P i) F1 i <= \big[min/x]_(i | P i) F2 i.
Proof.
move=> FG; elim/big_ind2 : _ => // a b e f ba fe.
rewrite ge_min 2!le_min ba fe /= andbT.
move: (le_total a e) => /orP[/(le_trans ba)-> // | /(le_trans fe)->].
by rewrite orbT.
Qed.

Lemma le_bigmax2 P F1 F2 : (forall i, P i -> F1 i <= F2 i) ->
  \big[max/x]_(i | P i) F1 i <= \big[max/x]_(i | P i) F2 i.
Proof.
move=> FG; elim/big_ind2 : _ => // a b e f ba fe.
rewrite le_max 2!ge_max ba fe /= andbT; have [//|/= af] := leP f a.
by rewrite (le_trans ba) // (le_trans _ fe) // ltW.
Qed.

Lemma bigmaxUl (A B : {set I}) F :
  \big[max/x]_(i in A) F i <= \big[max/x]_(i in A :|: B) F i.
Proof. by apply: sub_bigmax => t; rewrite in_setU => ->. Qed.

Lemma bigmaxUr (A B : {set I}) F :
  \big[max/x]_(i in B) F i <= \big[max/x]_(i in A :|: B) F i.
Proof. by under [leRHS]eq_bigl do rewrite setUC; apply: bigmaxUl. Qed.

Lemma bigminUl (A B : {set I}) F :
  \big[min/x]_(i in A) F i >= \big[min/x]_(i in A :|: B) F i.
Proof. by apply: sub_bigmin => t; rewrite in_setU => ->. Qed.

Lemma bigminUr (A B : {set I}) F :
  \big[min/x]_(i in B) F i >= \big[min/x]_(i in A :|: B) F i.
Proof. by under [leLHS]eq_bigl do rewrite setUC; apply: bigminUl. Qed.

Lemma bigmaxIl (A B : {set I}) F :
  \big[max/x]_(i in A) F i >= \big[max/x]_(i in A :&: B) F i.
Proof. by apply: sub_bigmax => t; rewrite in_setI => /andP[-> _]. Qed.

Lemma bigmaxIr (A B : {set I}) F :
  \big[max/x]_(i in B) F i >= \big[max/x]_(i in A :&: B) F i.
Proof. by under eq_bigl do rewrite setIC; apply: bigmaxIl. Qed.

Lemma bigminIl (A B : {set I}) F :
  \big[min/x]_(i in A) F i <= \big[min/x]_(i in A :&: B) F i.
Proof. by apply: sub_bigmin => t; rewrite in_setI => /andP[->_]. Qed.

Lemma bigminIr (A B : {set I}) F :
  \big[min/x]_(i in B) F i <= \big[min/x]_(i in A :&: B) F i.
Proof. by under [leRHS]eq_bigl do rewrite setIC; apply: bigminIl. Qed.

Lemma bigmaxD (A B : {set I}) F :
  \big[max/x]_(i in B) F i >= \big[max/x]_(i in B :\: A) F i.
Proof. by apply: sub_bigmax => t; rewrite in_setD => /andP[_->]. Qed.

Lemma bigminD (A B : {set I}) F :
  \big[min/x]_(i in B) F i <= \big[min/x]_(i in B :\: A) F i.
Proof. by apply: sub_bigmin => t; rewrite in_setD => /andP[_->]. Qed.

Lemma bigmaxU (A B : {set I}) F :
  \big[max/x]_(i in A :|: B) F i
  = max (\big[max/x]_(i in A) F i) (\big[max/x]_(i in B) F i).
Proof.
apply: le_anti; rewrite ge_max bigmaxUl bigmaxUr !andbT; apply/bigmax_leP.
split=> [|i /[!in_setU]/orP[iA|iB]]; first by rewrite le_max bigmax_ge_id.
- by rewrite le_max le_bigmax_cond.
- by rewrite le_max orbC le_bigmax_cond.
Qed.

Lemma bigminU (A B : {set I}) F :
  \big[min/x]_(i in A :|: B) F i
  = min (\big[min/x]_(i in A) F i) (\big[min/x]_(i in B) F i).
Proof.
apply: le_anti; rewrite le_min bigminUl bigminUr !andbT; apply/bigmin_geP.
split=> [|i /[!in_setU]/orP[iA|iB]]; first by rewrite ge_min bigmin_le_id.
- by rewrite ge_min bigmin_le_cond.
- by rewrite ge_min orbC bigmin_le_cond.
Qed.

Lemma bigmin_set1 j F : \big[min/x]_(i in [set j]) F i = min (F j) x.
Proof. exact: big_set1E. Qed.

Lemma bigmax_set1 j F : \big[max/x]_(i in [set j]) F i = max (F j) x.
Proof. exact: big_set1E. Qed.

End bigminmax_finType.

Lemma bigmin_imset [I J : finType] x [h : I -> J] [A : {set I}] (F : J -> T) :
  \big[min/x]_(j in [set h x | x in A]) F j = \big[min/x]_(i in A) F (h i).
Proof. by apply: big_imset_idem; apply: minxx. Qed.

Lemma bigmax_imset [I J : finType] x [h : I -> J] [A : {set I}] (F : J -> T) :
  \big[max/x]_(j in [set h x | x in A]) F j = \big[max/x]_(i in A) F (h i).
Proof. by apply: big_imset_idem; apply: maxxx. Qed.

End TotalTheory.

#[global] Hint Resolve le_total : core.
#[global] Hint Resolve ge_total : core.
#[global] Hint Extern 0 (is_true (_ >=< _)%O) => solve [apply: comparableT]
  : core.
#[global] Hint Resolve sort_le_sorted : core.

Arguments min_idPr {disp T x y}.
Arguments max_idPl {disp T x y}.
Arguments bigmin_mkcond {disp T I r}.
Arguments bigmax_mkcond {disp T I r}.
Arguments bigminID {disp T I r}.
Arguments bigmaxID {disp T I r}.
Arguments bigminD1 {disp T I x} j.
Arguments bigmaxD1 {disp T I x} j.
Arguments bigmin_inf {disp T I x} j.
Arguments bigmax_sup {disp T I x} j.
Arguments bigmin_eq_arg {disp T I} x j.
Arguments bigmax_eq_arg {disp T I} x j.
Arguments eq_bigmin {disp T I x} j.
Arguments eq_bigmax {disp T I x} j.
Arguments ge_bigmin_seq {disp T I r} x i0 P.
Arguments le_bigmax_seq {disp T I r} x i0 P.
Arguments bigmin_inf_seq {disp T I r} x i0 P.
Arguments bigmax_sup_seq {disp T I r} x i0 P.

(* FIXME: some lemmas in the following section should hold for any porderType *)
Module Import DualTotalTheory.
Section DualTotalTheory.
Context {disp : disp_t} {T : orderType disp}.
Implicit Type s : seq T.

Lemma sorted_filter_gt x s :
  sorted <=%O s -> [seq y <- s | x < y] = drop (count (<= x) s) s.
Proof.
move=> s_sorted; rewrite count_le_gt -[LHS]revK -filter_rev.
rewrite (@sorted_filter_lt _ T^d); last by rewrite take_rev revK count_rev.
by rewrite rev_sorted.
Qed.

Lemma sorted_filter_ge x s :
  sorted <=%O s -> [seq y <- s | x <= y] = drop (count (< x) s) s.
Proof.
move=> s_sorted; rewrite count_lt_ge -[LHS]revK -filter_rev.
rewrite (@sorted_filter_le _ T^d); last by rewrite take_rev revK count_rev.
by rewrite rev_sorted.
Qed.

Lemma nth_count_ge x x0 s i : sorted <=%O s ->
  (count (< x) s <= i < size s)%N -> x <= nth x0 s i.
Proof.
move=> ss /andP[ige ilt]; rewrite -(subnKC ige) -nth_drop -sorted_filter_ge //.
apply/(all_nthP _ (filter_all _ _)).
by rewrite size_filter ltn_subLR // count_lt_ge subnK // count_size.
Qed.

Lemma nth_count_gt x x0 s i : sorted <=%O s ->
  (count (<= x) s <= i < size s)%N -> x < nth x0 s i.
Proof.
move=> ss /andP[ige ilt]; rewrite -(subnKC ige) -nth_drop -sorted_filter_gt //.
apply/(all_nthP _ (filter_all _ _)).
by rewrite size_filter ltn_subLR // count_le_gt subnK // count_size.
Qed.

Lemma nth_count_eq x x0 s i : sorted <=%O s ->
  (count (< x) s <= i < count (<= x) s)%N -> nth x0 s i = x.
Proof.
move=> ss /andP[ige ilt]; apply/le_anti.
by rewrite nth_count_le// nth_count_ge// ige (leq_trans ilt (count_size _ _)).
Qed.

End DualTotalTheory.
End DualTotalTheory.

(* contra lemmas *)

Section ContraTheory.
Context {disp1 disp2 : disp_t} {T1 : porderType disp1} {T2 : orderType disp2}.
Implicit Types (x y : T1) (z t : T2) (b : bool) (m n : nat) (P : Prop).

Lemma contraTle b z t : (t < z -> ~~ b) -> (b -> z <= t).
Proof. exact: comparable_contraTle. Qed.

Lemma contraTlt b z t : (t <= z -> ~~ b) -> (b -> z < t).
Proof. exact: comparable_contraTlt. Qed.

Lemma contraPle P z t : (t < z -> ~ P) -> (P -> z <= t).
Proof. exact: comparable_contraPle. Qed.

Lemma contraPlt P z t : (t <= z -> ~ P) -> (P -> z < t).
Proof. exact: comparable_contraPlt. Qed.

Lemma contraNle b z t : (t < z -> b) -> (~~ b -> z <= t).
Proof. exact: comparable_contraNle. Qed.

Lemma contraNlt b z t : (t <= z -> b) -> (~~ b -> z < t).
Proof. exact: comparable_contraNlt. Qed.

Lemma contra_not_le P z t : (t < z -> P) -> (~ P -> z <= t).
Proof. exact: comparable_contra_not_le. Qed.

Lemma contra_not_lt P z t : (t <= z -> P) -> (~ P -> z < t).
Proof. exact: comparable_contra_not_lt. Qed.

Lemma contraFle b z t : (t < z -> b) -> (b = false -> z <= t).
Proof. exact: comparable_contraFle. Qed.

Lemma contraFlt b z t : (t <= z -> b) -> (b = false -> z < t).
Proof. exact: comparable_contraFlt. Qed.

Lemma contra_leq_le m n z t : (t < z -> (n < m)%N) -> ((m <= n)%N -> z <= t).
Proof. exact: comparable_contra_leq_le. Qed.

Lemma contra_leq_lt m n z t : (t <= z -> (n < m)%N) -> ((m <= n)%N -> z < t).
Proof. exact: comparable_contra_leq_lt. Qed.

Lemma contra_ltn_le m n z t : (t < z -> (n <= m)%N) -> ((m < n)%N -> z <= t).
Proof. exact: comparable_contra_ltn_le. Qed.

Lemma contra_ltn_lt m n z t : (t <= z -> (n <= m)%N) -> ((m < n)%N -> z < t).
Proof. exact: comparable_contra_ltn_lt. Qed.

Lemma contra_le x y z t : (t < z -> y < x) -> (x <= y -> z <= t).
Proof. exact: comparable_contra_le. Qed.

Lemma contra_le_lt x y z t : (t <= z -> y < x) -> (x <= y -> z < t).
Proof. exact: comparable_contra_le_lt. Qed.

Lemma contra_lt_le x y z t : (t < z -> y <= x) -> (x < y -> z <= t).
Proof. exact: comparable_contra_lt_le. Qed.

Lemma contra_lt x y z t : (t <= z -> y <= x) -> (x < y -> z < t).
Proof. exact: comparable_contra_lt. Qed.

End ContraTheory.

Section TotalMonotonyTheory.
Context {disp disp' : disp_t} {T : orderType disp} {T' : porderType disp'}.
Context (D : {pred T}) (f : T -> T').
Implicit Types (x y z : T) (u v w : T').

Let leT_anti    := @le_anti _ T.
Let leT'_anti   := @le_anti _ T'.
Let ltT_neqAle  := @lt_neqAle _ T.
Let ltT'_neqAle := @lt_neqAle _ T'.
Let ltT_def     := @lt_def _ T.
Let leT_total   := @le_total _ T.

Lemma le_mono : {homo f : x y / x < y} -> {mono f : x y / x <= y}.
Proof. exact: total_homo_mono. Qed.

Lemma le_nmono : {homo f : x y /~ x < y} -> {mono f : x y /~ x <= y}.
Proof. by apply: total_homo_mono => // x y; rewrite eq_sym. Qed.

Lemma le_mono_in :
  {in D &, {homo f : x y / x < y}} -> {in D &, {mono f : x y / x <= y}}.
Proof. exact: total_homo_mono_in. Qed.

Lemma le_nmono_in :
  {in D &, {homo f : x y /~ x < y}} -> {in D &, {mono f : x y /~ x <= y}}.
Proof. by apply: total_homo_mono_in => // x y; rewrite eq_sym. Qed.

End TotalMonotonyTheory.

End TotalTheory.

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

(* complemented lattices *)

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

(* orderType *)

HB.factory Record Lattice_isTotal d T & Lattice d T := {
  le_total : total (<=%O : rel T)
}.

HB.builders Context d T & Lattice_isTotal d T.

Fact meetUl : @left_distributive T T meet join.
Proof.
pose leP x y := lcomparable_leP (le_total x y); move=> x y z; apply/esym.
by case: (leP x y) (leP x z) (leP y z) => [|/ltW] xy [|/ltW] xz [|/ltW] yz;
  (apply/join_idPl || apply/join_idPr) => //; apply: le_trans xy.
Qed.

HB.instance Definition _ := Lattice_Meet_isDistrLattice.Build d T meetUl.
HB.instance Definition _ := DistrLattice_isTotal.Build d T le_total.

HB.end.

HB.factory Record POrder_isTotal d T & POrder d T := {
  le_total : total (<=%O : rel T) }.

HB.builders Context d T & POrder_isTotal d T.

Implicit Types (x y z : T).

Let comparableT x y : x >=< y := le_total x y.

Fact ltgtP x y :
  compare x y (min y x) (min x y) (max y x) (max x y)
              (y == x) (x == y) (x >= y) (x <= y) (x > y) (x < y).
Proof. exact: comparable_ltgtP. Qed.

Fact leP x y : le_xor_gt x y
  (min y x) (min x y) (max y x) (max x y) (x <= y) (y < x).
Proof. exact: comparable_leP. Qed.

Definition meet := @min _ T.
Definition join := @max _ T.

Fact meetC : commutative meet.
Proof. by move=> x y; rewrite /meet; have [] := ltgtP. Qed.

Fact joinC : commutative join.
Proof. by move=> x y; rewrite /join; have [] := ltgtP. Qed.

Fact meetA : associative meet.
Proof.
move=> x y z; rewrite /meet /min !(fun_if, if_arg).
case: (leP z y) (leP y x) (leP z x) => [] zy [] yx [] zx//=.
  by have := le_lt_trans (le_trans zy yx) zx; rewrite ltxx.
by apply/eqP; rewrite eq_le zx ltW// (lt_trans yx).
Qed.

Fact joinA : associative join.
Proof.
move=> x y z; rewrite /meet /min !(fun_if, if_arg).
case: (leP z y) (leP y x) (leP z x) => [] zy [] yx [] zx//=.
  by have := le_lt_trans (le_trans zy yx) zx; rewrite ltxx.
by apply/eqP; rewrite eq_le zx ltW// (lt_trans yx).
Qed.

Fact joinKI y x : meet x (join x y) = x.
Proof.
rewrite /meet /join /min /max !(fun_if, if_arg).
by have []// := ltgtP x y; rewrite ltxx.
Qed.

Fact meetKU y x : join x (meet x y) = x.
Proof.
rewrite /meet /join /min /max !(fun_if, if_arg).
by have []// := ltgtP x y; rewrite ltxx.
Qed.

Fact leEmeet x y : (x <= y) = (meet x y == x).
Proof. by rewrite /meet; case: leP => ?; rewrite ?eqxx ?lt_eqF. Qed.

HB.instance Definition _ := @POrder_isLattice.Build d T
  meet join meetC joinC meetA joinA joinKI meetKU leEmeet.
HB.instance Definition _ :=
  Lattice_isTotal.Build d T comparableT.
HB.end.

HB.factory Record isOrder (d : disp_t) T & Choice T := {
  le : rel T;
  lt : rel T;
  meet : T -> T -> T;
  join : T -> T -> T;
  lt_def : forall x y, lt x y = (y != x) && le x y;
  meet_def : forall x y, meet x y = if lt x y then x else y;
  join_def : forall x y, join x y = if lt x y then y else x;
  le_anti : antisymmetric le;
  le_trans : transitive le;
  le_total : total le;
}.

HB.builders Context d T & isOrder d T.

Fact le_refl : reflexive le.
Proof. by move=> x; case: (le x x) (le_total x x). Qed.

Fact lt_le_def x y : lt x y = (le x y) && ~~ (le y x).
Proof.
rewrite lt_def andbC; case/boolP: (le x y) => //= xy.
congr negb; apply/eqP/idP => [->|yx]; first exact/le_refl.
by apply/le_anti/andP; split.
Qed.

HB.instance Definition _ := isPreorder.Build d T
  lt_le_def le_refl le_trans.
HB.instance Definition _ := Preorder_isPOrder.Build d T le_anti.

Section GeneratedOrder.

Local Definition T' := T.
HB.instance Definition _ := POrder.on T'.
HB.instance Definition _ := POrder_isTotal.Build d T' le_total.
Implicit Types (x y z : T').

Fact meetE x y : meet x y = x `&` y. Proof. by rewrite meet_def. Qed.
Fact joinE x y : join x y = x `|` y. Proof. by rewrite join_def. Qed.
Fact meetC : commutative meet.
Proof. by move=> *; rewrite !meetE meetC. Qed.
Fact joinC : commutative join.
Proof. by move=> *; rewrite !joinE joinC. Qed.
Fact meetA : associative meet.
Proof. by move=> *; rewrite !meetE meetA. Qed.
Fact joinA : associative join.
Proof. by move=> *; rewrite !joinE joinA. Qed.
Fact joinKI y x : meet x (join x y) = x.
Proof. by rewrite meetE joinE joinKI. Qed.
Fact meetKU y x : join x (meet x y) = x.
Proof. by rewrite meetE joinE meetKU. Qed.
Fact meetUl : left_distributive meet join.
Proof. by move=> *; rewrite !meetE !joinE meetUl. Qed.
Fact meetxx : idempotent_op meet.
Proof. by move=> *; rewrite meetE meetxx. Qed.
Fact le_def x y : (x <= y) = (meet x y == x).
Proof. by rewrite meetE (eq_meetl x y). Qed.

End GeneratedOrder.

HB.instance Definition _ := @POrder_Meet_isDistrLattice.Build d T
  meet join meetC joinC meetA joinA joinKI meetKU le_def meetUl.
HB.instance Definition _ := DistrLattice_isTotal.Build d T le_total.

HB.end.

HB.factory Record LtOrder (d : disp_t) T & Choice T := {
  le : rel T;
  lt : rel T;
  meet : T -> T -> T;
  join : T -> T -> T;
  le_def   : forall x y, le x y = (x == y) || lt x y;
  meet_def : forall x y, meet x y = if lt x y then x else y;
  join_def : forall x y, join x y = if lt x y then y else x;
  lt_irr   : irreflexive lt;
  lt_trans : transitive lt;
  lt_total : forall x y, x != y -> lt x y || lt y x;
}.

HB.builders Context d T & LtOrder d T.

Fact lt_def x y : lt x y = (y != x) && le x y.
Proof. by rewrite le_def; case: eqVneq => //= ->; rewrite lt_irr. Qed.

Fact meet_def_le x y : meet x y = if lt x y then x else y.
Proof. by rewrite meet_def lt_def; case: eqP. Qed.

Fact join_def_le x y : join x y = if lt x y then y else x.
Proof. by rewrite join_def lt_def; case: eqP. Qed.

Fact le_anti : antisymmetric le.
Proof.
move=> x y; rewrite !le_def; case: eqVneq => //= _ /andP [] hxy.
by move/(lt_trans hxy); rewrite lt_irr.
Qed.

Fact le_trans : transitive le.
Proof.
move=> y x z; rewrite !le_def; case: eqVneq => [->|_] //=.
by case: eqVneq => [-> ->|_ hxy /(lt_trans hxy) ->]; rewrite orbT.
Qed.

Fact le_total : total le.
Proof. by move=> x y; rewrite !le_def; case: eqVneq => //; exact: lt_total. Qed.

HB.instance Definition _ :=
  isOrder.Build d T lt_def meet_def_le join_def_le le_anti le_trans le_total.
HB.end.

HB.factory Record MonoTotal disp T & POrder disp T := {
  disp' : disp_t;
  T' : orderType disp';
  f : T -> T';
  f_mono : {mono f : x y / x <= y}
}.
HB.builders Context disp T & MonoTotal disp T.
Fact totalT : total (<=%O : rel T).
Proof. by move=> x y; rewrite -!f_mono le_total. Qed.
HB.instance Definition _ := POrder_isTotal.Build disp T totalT.
HB.end.

Section CancelTotal.
Variables (disp : disp_t) (T : choiceType).
Variables (disp' : disp_t) (T' : orderType disp') (f : T -> T').

Section PCan.

Variables (f' : T' -> option T) (f_can : pcancel f f').

#[local]
HB.instance Definition _ :=
   MonoTotal.Build disp (pcan_type f_can) (fun _ _ => erefl).

Definition PCanIsTotal : DistrLattice_isTotal _ (pcan_type f_can) :=
  Total.on (pcan_type f_can).

End PCan.

Section Can.

Variables (f' : T' -> T) (f_can : cancel f f').

#[local]
HB.instance Definition _ :=
   MonoTotal.Build disp (can_type f_can) (fun _ _ => erefl).

Definition CanIsTotal : DistrLattice_isTotal _ (can_type f_can) :=
  Total.on (can_type f_can).

End Can.
End CancelTotal.

#[short(type="subOrder")]
HB.structure Definition SubOrder d (T : orderType d) S d' :=
  { U of @SubLattice d T S d' U & Total d' U }.

HB.factory Record SubLattice_isSubOrder d (T : orderType d) S d' U
    & @SubLattice d T S d' U := {}.

HB.builders Context d T S d' U & SubLattice_isSubOrder d T S d' U.
Lemma totalU : total (<=%O : rel U).
Proof. by move=> x y; rewrite -!le_val le_total. Qed.
HB.instance Definition _ := Lattice_isTotal.Build d' U totalU.
HB.end.

HB.factory Record SubPOrder_isSubOrder d (T : orderType d) S d' U
    & @SubPOrder d T S d' U := {}.

HB.builders Context d T S d' U & SubPOrder_isSubOrder d T S d' U.
Fact opredI : meet_closed S.
Proof. by move=> x y Sx Sy; rewrite meetEtotal; case: leP. Qed.
Fact opredU : join_closed S.
Proof. by move=> x y Sx Sy; rewrite joinEtotal; case: leP. Qed.
HB.instance Definition _ := SubPOrder_isSubLattice.Build d T S d' U opredI opredU.
HB.instance Definition _ := SubLattice_isSubOrder.Build d T S d' U.
HB.end.

HB.factory Record SubChoice_isSubOrder d (T : orderType d) S (d' : disp_t) U
    & @SubChoice T S U := {}.

HB.builders Context d T S d' U & SubChoice_isSubOrder d T S d' U.
HB.instance Definition _ := SubChoice_isSubPOrder.Build d T S d' U.
HB.instance Definition _ := SubPOrder_isSubOrder.Build d T S d' U.
HB.end.

Module SubOrderExports.

Notation "[ 'SubLattice_isSubOrder' 'of' U 'by' <: ]" :=
  (SubLattice_isSubOrder.Build _ _ _ _ U)
  (format "[ 'SubLattice_isSubOrder'  'of'  U  'by'  <: ]")
  : form_scope.
Notation "[ 'SubLattice_isSubOrder' 'of' U 'by' <: 'with' disp ]" :=
  (SubLattice_isSubOrder.Build _ _ _ disp U)
  (format "[ 'SubLattice_isSubOrder'  'of'  U  'by'  <:  'with'  disp ]")
  : form_scope.
Notation "[ 'SubPOrder_isSubOrder' 'of' U 'by' <: ]" :=
  (SubPOrder_isSubOrder.Build _ _ _ _ U)
  (format "[ 'SubPOrder_isSubOrder'  'of'  U  'by'  <: ]")
  : form_scope.
Notation "[ 'SubPOrder_isSubOrder' 'of' U 'by' <: 'with' disp ]" :=
  (SubPOrder_isSubOrder.Build _ _ _ disp U)
  (format "[ 'SubPOrder_isSubOrder'  'of'  U  'by'  <:  'with'  disp ]")
  : form_scope.
Notation "[ 'SubChoice_isSubOrder' 'of' U 'by' <: ]" :=
  (SubChoice_isSubOrder.Build _ _ _ _ U)
  (format "[ 'SubChoice_isSubOrder'  'of'  U  'by'  <: ]")
  : form_scope.
Notation "[ 'SubChoice_isSubOrder' 'of' U 'by' <: 'with' disp ]" :=
  (SubChoice_isSubOrder.Build _ _ _ disp U)
  (format "[ 'SubChoice_isSubOrder'  'of'  U  'by'  <:  'with'  disp ]")
  : form_scope.

End SubOrderExports.
HB.export SubOrderExports.

Module DeprecatedSubOrder.

Section Total.
Context {disp : disp_t} {T : orderType disp} (P : {pred T}) (sT : subType P).

#[export]
HB.instance Definition _ :=
  SubPOrder_isSubOrder.Build disp T P disp (sub_type sT).

End Total.

Module Exports.
HB.reexport DeprecatedSubOrder.
Notation "[ 'POrder' 'of' T 'by' <: ]" :=
  (POrder.copy T%type (sub_type T%type))
  (format "[ 'POrder'  'of'  T  'by'  <: ]") : form_scope.
Notation "[ 'Order' 'of' T 'by' <: ]" :=
  (Total.copy T%type (sub_type T%type))
  (only parsing) : form_scope.
End Exports.
End DeprecatedSubOrder.
HB.export DeprecatedSubOrder.Exports.

Module Syntax.
Export Order.Syntax.
Export DualSyntax.
Export LatticeSyntax.
Export BLatticeSyntax.
Export TLatticeSyntax.
Export CBDistrLatticeSyntax.
Export CTBDistrLatticeSyntax.
End Syntax.

Module CTheory.
Export Order.Theory.
Export CDistrLatticeTheory.
Export CBDistrLatticeTheory.
Export CTDistrLatticeTheory.
Export CTBDistrLatticeTheory.
End CTheory.

Module TTheory.
Export Order.Theory TotalTheory.
End TTheory.

Module Theory.
Export CTheory TotalTheory.
End Theory.

Module Exports.
HB.reexport.
End Exports.
End Order.

Export Order.Exports.

Export Order.Syntax.

Export Order.Total.Exports.
Export Order.BTotal.Exports.
Export Order.TTotal.Exports.
Export Order.TBTotal.Exports.
Export Order.CDistrLattice.Exports.
Export Order.CBDistrLattice.Exports.
Export Order.CTDistrLattice.Exports.
Export Order.CTBDistrLattice.Exports.
Export Order.FinTotal.Exports.
Export Order.FinTBTotal.Exports.
Export Order.FinCDistrLattice.Exports.
Export Order.FinCTBDistrLattice.Exports.

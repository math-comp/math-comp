(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrbool ssrfun eqtype ssrnat seq div choice fintype.
From mathcomp
Require Import tuple finfun bigop finset fingroup action perm primitive_action.

(*   Application of the Burside formula to count the number of distinct       *)
(* colorings of the vertices of a square and a cube.                          *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Lemma burnside_formula : forall (gT : finGroupType) s (G : {group gT}),
   uniq s -> s =i G ->
   forall (sT : finType) (to : {action gT &-> sT}),
   (#|orbit to G @: setT| * size s)%N = \sum_(p <- s) #|'Fix_to[p]|.
Proof.
move=> gT s G Us sG sT to.
rewrite big_uniq // -(card_uniqP Us) (eq_card sG) -Frobenius_Cauchy.
  by apply: eq_big => // p _; rewrite setTI.
by apply/actsP=> ? _ ?; rewrite !inE.
Qed.

Arguments burnside_formula {gT}.

Section colouring.

Variable n : nat.
Definition  colors := 'I_n.
Canonical colors_eqType := Eval hnf in [eqType of colors].
Canonical colors_choiceType := Eval hnf in [choiceType of colors].
Canonical colors_countType := Eval hnf in [countType of colors].
Canonical colors_finType := Eval hnf in [finType of colors].

Section square_colouring.

Definition square := 'I_4.
Canonical square_eqType := Eval hnf in [eqType of square].
Canonical square_choiceType := Eval hnf in [choiceType of square].
Canonical square_countType := Eval hnf in [countType of square].
Canonical square_finType := Eval hnf in [finType of square].
Canonical square_subType := Eval hnf in [subType of square].
Canonical square_subCountType :=
  Eval hnf in [subCountType of square].
Canonical square_subFinType := Eval hnf in [subFinType of square].

Definition mksquare i : square := Sub (i %% _) (ltn_mod i 4).
Definition c0 := mksquare 0.
Definition c1 := mksquare 1.
Definition c2 := mksquare 2.
Definition c3 := mksquare 3.

(*rotations*)
Definition R1 (sc : square) : square := tnth [tuple c1; c2; c3; c0] sc.

Definition R2 (sc : square) : square := tnth [tuple c2; c3; c0; c1] sc.

Definition R3 (sc : square) : square := tnth [tuple c3; c0; c1; c2] sc.

Ltac get_inv elt l :=
  match l with
  | (_, (elt, ?x))  => x
  | (elt, ?x)  => x
  | (?x, _) => get_inv elt x
  end.

Definition rot_inv := ((R1, R3), (R2, R2), (R3, R1)).

Ltac inj_tac :=
  move: (erefl rot_inv); unfold rot_inv;
  match goal with |- ?X = _ -> injective ?Y =>
    move=> _; let x := get_inv Y X in
    apply: (can_inj (g:=x)); move=> [val H1]
  end.

Lemma R1_inj :  injective R1.
Proof. by inj_tac; repeat (destruct val => //=; first by apply/eqP). Qed.

Lemma R2_inj :  injective R2.
Proof. by inj_tac; repeat (destruct val => //=; first by apply/eqP). Qed.

Lemma R3_inj : injective R3.
Proof. by inj_tac; repeat (destruct val => //=; first by apply/eqP). Qed.

Definition r1 := (perm R1_inj).
Definition r2 := (perm R2_inj).
Definition r3 := (perm R3_inj).
Definition id1 := (1 : {perm square}).

Definition is_rot (r : {perm _}) :=  (r * r1 == r1 * r).
Definition rot := [set r | is_rot r].

Lemma group_set_rot : group_set rot.
Proof.
apply/group_setP; split; first  by rewrite /rot  inE /is_rot mulg1 mul1g.
move=> x1 y; rewrite /rot !inE /= /is_rot; move/eqP => hx1; move/eqP => hy.
by rewrite -mulgA hy !mulgA hx1.
Qed.

Canonical rot_group := Group group_set_rot.

Definition rotations := [set id1; r1; r2; r3].

Lemma rot_eq_c0 : forall r s : {perm square},
  is_rot r -> is_rot s -> r c0 = s c0 -> r = s.
Proof.
rewrite /is_rot => r s; move/eqP => hr; move/eqP=> hs hrs; apply/permP => a.
have ->: a = (r1 ^+ a) c0
   by apply/eqP; case: a; do 4?case=> //=; rewrite ?permM !permE.
by rewrite -!permM -!commuteX   //  !permM hrs.
Qed.

Lemma rot_r1 : forall r, is_rot r -> r = r1 ^+ (r c0).
Proof.
move=> r hr; apply: rot_eq_c0 => //; apply/eqP.
   by symmetry; apply: commuteX.
by case: (r c0); do 4?case=> //=; rewrite ?permM !permE  /=.
Qed.

Lemma rotations_is_rot : forall r, r \in rotations -> is_rot r.
Proof.
move=> r Dr; apply/eqP; apply/permP => a; rewrite !inE -!orbA !permM in Dr *.
by case/or4P: Dr; move/eqP->; rewrite !permE //; case: a; do 4?case.
Qed.

Lemma rot_is_rot : rot = rotations.
Proof.
apply/setP=> r; apply/idP/idP; last by move/rotations_is_rot; rewrite inE.
rewrite !inE => h.
have -> : r = r1 ^+ (r c0) by apply: rot_eq_c0; rewrite // -rot_r1.
have e2: 2 = r2 c0 by rewrite permE /=.
have e3: 3 = r3 c0 by rewrite permE /=.
case (r c0); do 4?[case] => // ?; rewrite ?(expg1, eqxx, orbT) //.
  by rewrite [nat_of_ord _]/= e2 -rot_r1 ?(eqxx, orbT, rotations_is_rot, inE).
by rewrite [nat_of_ord _]/= e3 -rot_r1 ?(eqxx, orbT, rotations_is_rot, inE).
Qed.

(*symmetries*)
Definition Sh (sc : square) : square := tnth [tuple c1; c0; c3; c2] sc.

Lemma Sh_inj : injective Sh.
Proof.
by apply: (can_inj (g:= Sh)); case; do 4?case=> //=; move=> H; apply/eqP.
Qed.

Definition sh := (perm Sh_inj).

Lemma sh_inv : sh^-1 = sh.
Proof.
apply: (mulIg sh); rewrite mulVg; apply/permP.
by case; do 4?case=> //=; move=> H; rewrite !permE /= !permE; apply/eqP.
Qed.

Definition Sv (sc : square) : square := tnth [tuple c3; c2; c1; c0] sc.

Lemma Sv_inj : injective Sv.
Proof.
by apply: (can_inj (g:= Sv)); case; do 4?case=> //=; move=> H; apply/eqP.
Qed.

Definition sv := (perm Sv_inj).

Lemma sv_inv : sv^-1 = sv.
Proof.
apply: (mulIg sv); rewrite mulVg; apply/permP.
by case; do 4?case=> //=; move=> H; rewrite !permE /= !permE; apply/eqP.
Qed.

Definition Sd1 (sc : square) : square := tnth [tuple c0; c3; c2; c1] sc.

Lemma Sd1_inj : injective Sd1.
Proof.
by apply: can_inj Sd1 _; case; do 4?case=> //=; move=> H; apply/eqP.
Qed.

Definition sd1 := (perm Sd1_inj).

Lemma sd1_inv : sd1^-1 = sd1.
Proof.
apply: (mulIg sd1); rewrite mulVg; apply/permP.
by case; do 4?case=> //=; move=> H; rewrite !permE /= !permE; apply/eqP.
Qed.

Definition Sd2 (sc : square) : square := tnth [tuple c2; c1; c0; c3] sc.

Lemma Sd2_inj : injective Sd2.
Proof.
by apply: can_inj Sd2 _; case; do 4?case=> //=; move=> H; apply/eqP.
Qed.

Definition sd2 := (perm Sd2_inj).

Lemma sd2_inv : sd2^-1 = sd2.
Proof.
apply: (mulIg sd2); rewrite mulVg; apply/permP.
by case; do 4?case=> //=; move=> H; rewrite !permE /= !permE; apply/eqP.
Qed.

Lemma ord_enum4 : enum 'I_4 = [:: c0; c1; c2; c3].
Proof. by apply: (inj_map val_inj); rewrite val_enum_ord. Qed.

Lemma diff_id_sh : 1 != sh.
Proof.
by apply/eqP; move/(congr1 (fun p : {perm square} => p c0)); rewrite !permE.
Qed.

Definition isometries2 := [set 1; sh].

Lemma card_iso2 : #|isometries2| = 2.
Proof. by rewrite cards2 diff_id_sh. Qed.

Lemma group_set_iso2 : group_set isometries2.
Proof.
apply/group_setP; split => [|x y]; rewrite !inE ?eqxx //.
do 2![case/orP; move/eqP->]; gsimpl; rewrite ?(eqxx, orbT) //.
by rewrite -/sh -{1}sh_inv mulVg eqxx.
Qed.
Canonical iso2_group := Group group_set_iso2.

Definition isometries :=
  [set p | [|| p == 1, p == r1, p == r2, p == r3,
            p == sh, p == sv, p == sd1 | p == sd2 ]].

Definition opp (sc : square) := tnth [tuple c2; c3; c0; c1] sc.

Definition is_iso (p : {perm square}) := forall ci, p (opp ci) = opp (p ci).

Lemma isometries_iso : forall p, p \in isometries -> is_iso p.
Proof.
move=> p; rewrite inE.
by do ?case/orP; move/eqP=> -> a; rewrite !permE; case: a; do 4?case.
Qed.

Ltac non_inj p a1 a2 heq1 heq2 :=
let h1:= fresh "h1" in
(absurd (p a1 = p a2); first (by red => - h1; move: (perm_inj h1));
by rewrite heq1 heq2; apply/eqP).

Ltac is_isoPtac p f e0 e1 e2 e3 :=
  suff ->: p = f by [rewrite inE eqxx ?orbT];
  let e := fresh "e" in apply/permP;
  do 5?[case] => // ?; [move: e0 | move: e1 | move: e2 | move: e3] => e;
  apply: etrans (congr1 p _) (etrans e _); apply/eqP; rewrite // permE.

Lemma is_isoP : forall p, reflect (is_iso p) (p \in isometries).
Proof.
move=> p; apply: (iffP idP) => [|iso_p]; first exact: isometries_iso.
move e1: (p c1) (iso_p c1) => k1; move e0: (p c0) (iso_p c0) k1 e1 => k0.
case: k0 e0; do 4?[case] => //= ? e0 e2; do 5?[case] => //= ? e1 e3;
 try by [non_inj p c0 c1 e0 e1 | non_inj p c0 c3 e0 e3].
by is_isoPtac p id1 e0 e1 e2 e3.
by is_isoPtac p sd1 e0 e1 e2 e3.
by is_isoPtac p sh e0 e1 e2 e3.
by is_isoPtac p r1 e0 e1 e2 e3.
by is_isoPtac p sd2 e0 e1 e2 e3.
by is_isoPtac p r2 e0 e1 e2 e3.
by is_isoPtac p r3 e0 e1 e2 e3.
by is_isoPtac p sv e0 e1 e2 e3.
Qed.


Lemma group_set_iso : group_set isometries.
Proof.
apply/group_setP; split; first by rewrite inE eqxx /=.
by move=> x y hx hy; apply/is_isoP => ci; rewrite !permM !isometries_iso.
Qed.

Canonical iso_group := Group group_set_iso.

Lemma card_rot : #|rot| = 4.
Proof.
rewrite -[4]/(size [:: id1; r1; r2; r3]) -(card_uniqP _).
  by apply: eq_card => x; rewrite rot_is_rot !inE -!orbA.
by apply: map_uniq (fun p : {perm square} => p c0) _ _; rewrite /= !permE.
Qed.

Lemma group_set_rotations : group_set rotations.
Proof. by rewrite -rot_is_rot group_set_rot. Qed.

Canonical rotations_group := Group group_set_rotations.

Notation col_squares := {ffun square -> colors}.

Definition act_f (sc : col_squares) (p : {perm square}) : col_squares :=
  [ffun z => sc (p^-1 z)].

Lemma act_f_1 :  forall k, act_f k 1 = k.
Proof. by move=> k; apply/ffunP=> a; rewrite ffunE invg1 permE. Qed.

Lemma act_f_morph :  forall k x y, act_f k (x * y) = act_f (act_f k x) y.
Proof. by move=> k x y; apply/ffunP=> a; rewrite !ffunE invMg permE. Qed.

Definition to := TotalAction act_f_1 act_f_morph.

Definition square_coloring_number2 := #|orbit to isometries2 @: setT|.
Definition square_coloring_number4 := #|orbit to rotations @: setT|.
Definition square_coloring_number8 := #|orbit to isometries @: setT|.

Lemma Fid : 'Fix_to(1) = setT.
Proof. by apply/setP=> x /=; rewrite in_setT; apply/afix1P; apply: act1. Qed.

Lemma card_Fid : #|'Fix_to(1)| = (n ^ 4)%N.
Proof.
rewrite -[4]card_ord -[n]card_ord -card_ffun_on Fid cardsE.
by symmetry; apply: eq_card => f; apply/ffun_onP.
Qed.

Definition coin0 (sc : col_squares) : colors := sc c0.
Definition coin1 (sc : col_squares) : colors := sc c1.
Definition coin2 (sc : col_squares) : colors := sc c2.
Definition coin3 (sc : col_squares) : colors := sc c3.

Lemma eqperm_map : forall p1 p2 : col_squares,
  (p1 == p2) = all (fun s => p1 s == p2 s) [:: c0; c1; c2; c3].
Proof.
move=> p1 p2; apply/eqP/allP=> [-> // | Ep12]; apply/ffunP=> x.
by apply/eqP; apply Ep12; case: x; do 4!case=> //.
Qed.

Lemma F_Sh :
  'Fix_to[sh] = [set x | (coin0 x == coin1 x) && (coin2 x == coin3 x)].
Proof.
apply/setP=> x; rewrite (sameP afix1P eqP) !inE eqperm_map /=.
rewrite /act_f sh_inv !ffunE !permE /=.
by rewrite eq_sym (eq_sym (x c3)) andbT andbA !andbb.
Qed.

Lemma F_Sv :
  'Fix_to[sv] = [set x | (coin0 x == coin3 x) && (coin2 x == coin1 x)].
Proof.
apply/setP=> x; rewrite (sameP afix1P eqP) !inE eqperm_map /=.
rewrite /act_f sv_inv !ffunE !permE /=.
by rewrite eq_sym andbT andbC (eq_sym (x c1)) andbA -andbA !andbb andbC.
Qed.

Ltac inv_tac :=
  apply: esym (etrans _ (mul1g _)); apply: canRL (mulgK _) _;
  let a := fresh "a" in apply/permP => a;
  apply/eqP; rewrite permM !permE; case: a; do 4?case.

Lemma r1_inv : r1^-1 = r3.
Proof. by inv_tac. Qed.

Lemma r2_inv : r2^-1 = r2.
Proof. by inv_tac. Qed.

Lemma r3_inv : r3^-1 = r1.
Proof. by inv_tac. Qed.

Lemma F_r2 :
  'Fix_to[r2] = [set x | (coin0 x == coin2 x) && (coin1 x == coin3 x)].
Proof.
apply/setP=> x; rewrite (sameP afix1P eqP) !inE eqperm_map /=.
rewrite /act_f r2_inv !ffunE !permE /=.
by rewrite eq_sym andbT andbCA andbC (eq_sym (x c3)) andbA -andbA !andbb andbC.
Qed.

Lemma F_r1 : 'Fix_to[r1] =
  [set x | (coin0 x == coin1 x)&&(coin1 x == coin2 x)&&(coin2 x == coin3 x)].
Proof.
apply/setP=> x; rewrite (sameP afix1P eqP) !inE eqperm_map /=.
rewrite /act_f r1_inv !ffunE !permE andbC.
by do 3![case E: {+}(_ == _); rewrite // {E}(eqP E)]; rewrite eqxx.
Qed.

Lemma F_r3 : 'Fix_to[r3] =
  [set x | (coin0 x == coin1 x)&&(coin1 x == coin2 x)&&(coin2 x == coin3 x)].
Proof.
apply/setP=> x; rewrite (sameP afix1P eqP) !inE eqperm_map /=.
rewrite /act_f r3_inv !ffunE !permE /=.
by do 3![rewrite eq_sym; case E: {+}(_ == _); rewrite // {E}(eqP E)].
Qed.

Lemma card_n2 : forall x y z t : square, uniq [:: x; y; z; t] ->
  #|[set p : col_squares | (p x == p y) && (p z == p t)]| = (n ^ 2)%N.
Proof.
move=> x y z t Uxt; rewrite -[n]card_ord.
pose f (p : col_squares) := (p x, p z); rewrite -(@card_in_image _ _ f).
  rewrite -mulnn -card_prod; apply: eq_card => [] [c d] /=; apply/imageP.
  rewrite (cat_uniq [::x; y]) in Uxt; case/and3P: Uxt => _.
  rewrite /= !orbF !andbT; case/norP; rewrite !inE => nxzt nyzt _.
  exists [ffun i => if pred2 x y i then c else d].
    by rewrite inE !ffunE /= !eqxx orbT (negbTE nxzt) (negbTE nyzt) !eqxx.
  by rewrite {}/f !ffunE /= eqxx (negbTE nxzt).
move=> p1 p2; rewrite !inE.
case/andP=> p1y p1t; case/andP=> p2y p2t [px pz].
have eqp12: all (fun i => p1 i == p2 i) [:: x; y; z; t].
  by rewrite /= -(eqP p1y) -(eqP p1t) -(eqP p2y) -(eqP p2t) px pz !eqxx.
apply/ffunP=> i; apply/eqP; apply: (allP eqp12).
by rewrite (subset_cardP _ (subset_predT _)) // (card_uniqP Uxt) card_ord.
Qed.

Lemma card_n :
 #|[set x | (coin0 x == coin1 x)&&(coin1 x == coin2 x)&& (coin2 x == coin3 x)]|
   = n.
Proof.
rewrite -[n]card_ord /coin0 /coin1 /coin2 /coin3.
pose f (p : col_squares) := p c3; rewrite -(@card_in_image _ _ f).
  apply: eq_card => c /=; apply/imageP.
  exists ([ffun => c] : col_squares); last by rewrite /f ffunE.
  by rewrite /= inE !ffunE !eqxx.
move=> p1 p2; rewrite /= !inE /f -!andbA => eqp1 eqp2 eqp12.
apply/eqP; rewrite eqperm_map /= andbT.
case/and3P: eqp1; do 3!move/eqP->; case/and3P: eqp2; do 3!move/eqP->.
by rewrite !andbb eqp12.
Qed.

Lemma burnside_app2 : (square_coloring_number2 * 2 = n ^ 4 + n ^ 2)%N.
Proof.
rewrite (burnside_formula [:: id1; sh]) => [||p]; last first.
- by rewrite !inE.
- by rewrite /= inE diff_id_sh.
by rewrite 2!big_cons big_nil addn0 {1}card_Fid F_Sh card_n2.
Qed.

Lemma burnside_app_rot :
  (square_coloring_number4 * 4 = n ^ 4 + n ^ 2 + 2 * n)%N.
Proof.
rewrite (burnside_formula [:: id1; r1; r2; r3]) => [||p]; last first.
- by rewrite !inE !orbA.
- by apply: map_uniq (fun p : {perm square} => p c0) _ _; rewrite /= !permE.
rewrite !big_cons big_nil /= addn0 {1}card_Fid F_r1 F_r2 F_r3.
by rewrite card_n card_n2 //=; ring.
Qed.

Lemma F_Sd1 : 'Fix_to[sd1] = [set x | coin1 x == coin3 x].
Proof.
apply/setP => x; rewrite (sameP afix1P eqP) !inE eqperm_map /=.
rewrite /act_f sd1_inv !ffunE !permE /=.
by rewrite !eqxx !andbT eq_sym /= andbb.
Qed.

Lemma card_n3 : forall x y : square, x != y ->
  #|[set k : col_squares | k x == k y]| = (n ^ 3)%N.
Proof.
move=> x y nxy; apply/eqP; case: (ltngtP n 0) => // [|n0]; last first.
  by rewrite n0; apply/existsP=> [] [p _]; case: (p c0) => i; rewrite n0.
move/eqn_pmul2l <-; rewrite -expnS -card_Fid Fid cardsT.
rewrite -{1}[n]card_ord -cardX.
pose pk k := [ffun i => k (if i == y then x else i) : colors].
rewrite -(@card_image _ _ (fun k : col_squares => (k y, pk k))).
  apply/eqP; apply: eq_card => ck /=; rewrite inE /= [_ \in _]inE.
  apply/eqP/imageP; last first.
    by case=> k _ -> /=; rewrite !ffunE if_same eqxx.
  case: ck => c k /= kxy.
  exists [ffun i => if i == y then c else k i]; first by rewrite inE.
  rewrite !ffunE eqxx; congr (_, _); apply/ffunP=> i; rewrite !ffunE.
  case Eiy: (i == y); last by rewrite Eiy.
  by rewrite (negbTE nxy) (eqP Eiy).
move=> k1 k2 [Eky Epk]; apply/ffunP=> i.
have{Epk}: pk k1 i = pk k2 i by rewrite Epk.
by rewrite !ffunE; case: eqP => // ->.
Qed.

Lemma F_Sd2 : 'Fix_to[sd2] = [set x | coin0 x == coin2 x].
Proof.
apply/setP => x; rewrite (sameP afix1P eqP) !inE eqperm_map /=.
by rewrite /act_f sd2_inv !ffunE !permE /= !eqxx !andbT eq_sym /= andbb.
Qed.

Lemma burnside_app_iso :
  (square_coloring_number8 * 8 = n ^ 4 + 2 * n ^ 3 + 3 * n ^ 2 + 2 * n)%N.
Proof.
pose iso_list := [:: id1; r1; r2; r3; sh; sv; sd1; sd2].
rewrite (burnside_formula iso_list) => [||p]; last first.
- by rewrite /= !inE.
- apply: map_uniq (fun p : {perm square} => (p c0, p c1)) _ _.
  by rewrite /= !permE.
rewrite !big_cons big_nil {1}card_Fid F_r1 F_r2 F_r3 F_Sh F_Sv F_Sd1 F_Sd2.
by rewrite card_n !card_n3 // !card_n2 //=; ring.
Qed.

End square_colouring.

Section cube_colouring.

Definition cube := 'I_6.
Canonical cube_eqType := Eval hnf in [eqType of cube].
Canonical cube_choiceType := Eval hnf in [choiceType of cube].
Canonical cube_countType := Eval hnf in [countType of cube].
Canonical cube_finType := Eval hnf in [finType of cube].
Canonical cube_subType := Eval hnf in [subType of cube].
Canonical cube_subCountType := Eval hnf in [subCountType of cube].
Canonical cube_subFinType := Eval hnf in [subFinType of cube].

Definition mkFcube i : cube := Sub (i %% 6) (ltn_mod i 6).
Definition F0 := mkFcube 0.
Definition F1 := mkFcube 1.
Definition F2 := mkFcube 2.
Definition F3 := mkFcube 3.
Definition F4 := mkFcube 4.
Definition F5 := mkFcube 5.

(* axial symetries*)
Definition S05 := [:: F0; F4; F3; F2; F1; F5].
Definition S05f (sc : cube) : cube := tnth [tuple of S05] sc.


Definition S14 := [:: F5; F1; F3; F2; F4; F0].
Definition S14f (sc : cube) : cube := tnth [tuple of S14] sc.

Definition S23 := [:: F5; F4; F2; F3; F1; F0].
Definition S23f (sc : cube) : cube := tnth [tuple of S23] sc.

(* rotations 90 *)
Definition R05 := [:: F0; F2; F4; F1; F3; F5].
Definition R05f (sc : cube) : cube := tnth [tuple of R05] sc.
Definition R50 := [:: F0; F3; F1; F4; F2; F5].
Definition R50f (sc : cube) : cube := tnth  [tuple of R50] sc.
Definition R14 := [:: F3; F1; F0; F5; F4; F2].
Definition R14f (sc : cube) : cube := tnth [tuple of R14] sc.
Definition R41 := [:: F2; F1; F5; F0; F4; F3].
Definition R41f (sc : cube) : cube := tnth [tuple of R41] sc.
Definition R23 := [:: F1; F5; F2; F3; F0; F4].
Definition R23f (sc : cube) : cube := tnth [tuple of R23] sc.
Definition R32 := [:: F4; F0; F2; F3; F5; F1].
Definition R32f (sc : cube) : cube := tnth [tuple of R32] sc.
(* rotations 120 *)
Definition R024 := [:: F2; F5; F4; F1; F0; F3].
Definition R024f (sc : cube) : cube := tnth [tuple of R024] sc.
Definition R042 := [:: F4; F3; F0; F5; F2; F1].
Definition R042f (sc : cube) : cube := tnth [tuple of R042] sc.
Definition R012 := [:: F1; F2; F0; F5; F3; F4].
Definition R012f (sc : cube) : cube := tnth [tuple of R012] sc.
Definition R021 := [:: F2; F0; F1; F4; F5; F3].
Definition R021f (sc : cube) : cube := tnth [tuple of R021] sc.
Definition R031 := [:: F3; F0; F4; F1; F5; F2].
Definition R031f (sc : cube) : cube := tnth [tuple of R031] sc.
Definition R013 := [:: F1; F3; F5; F0; F2; F4].
Definition R013f (sc : cube) : cube := tnth [tuple of R013] sc.
Definition R043 := [:: F4; F2; F5; F0; F3; F1].
Definition R043f (sc : cube) : cube := tnth [tuple of R043] sc.
Definition R034 := [:: F3; F5; F1; F4; F0; F2].
Definition R034f (sc : cube) : cube := tnth [tuple of R034] sc.
(* last symmetries*)
Definition S1 := [:: F5; F2; F1; F4; F3; F0].
Definition S1f (sc : cube) : cube := tnth [tuple of S1] sc.
Definition S2 := [::  F5; F3; F4; F1; F2; F0].
Definition S2f (sc : cube) : cube := tnth [tuple of S2] sc.
Definition S3 := [::  F1; F0; F3; F2; F5; F4].
Definition S3f  (sc : cube) : cube := tnth [tuple of S3] sc.
Definition S4 := [:: F4; F5; F3; F2; F0; F1].
Definition S4f  (sc : cube) : cube := tnth [tuple of S4] sc.
Definition S5 := [::  F2; F4; F0; F5; F1; F3].
Definition S5f  (sc : cube) : cube := tnth [tuple of S5] sc.
Definition S6 := [::F3; F4; F5; F0; F1; F2].
Definition S6f  (sc : cube) : cube := tnth [tuple of S6] sc.

Lemma S1_inv : involutive S1f.
Proof. by move=> z; apply/eqP; case: z; do 6?case. Qed.

Lemma S2_inv : involutive S2f.
Proof. by move=> z; apply/eqP; case: z; do 6?case. Qed.

Lemma S3_inv : involutive S3f.
Proof. by move=> z; apply/eqP; case: z; do 6?case. Qed.

Lemma S4_inv : involutive S4f.
Proof. by move=> z; apply/eqP; case: z; do 6?case. Qed.

Lemma S5_inv : involutive S5f.
Proof. by move=> z; apply/eqP; case: z; do 6?case. Qed.

Lemma S6_inv : involutive S6f.
Proof. by move=> z; apply/eqP; case: z; do 6?case. Qed.

Lemma S05_inj : injective S05f.
Proof. by apply: can_inj S05f _ => z; apply/eqP; case: z; do 6?case.  Qed.

Lemma S14_inj : injective S14f.
Proof. by apply: can_inj S14f _ => z; apply/eqP; case: z; do 6?case. Qed.

Lemma S23_inv : involutive S23f.
Proof. by move=> z; apply/eqP; case: z; do 6?case. Qed.

Lemma R05_inj : injective R05f.
Proof. by apply: can_inj R50f _ => z; apply/eqP; case: z; do 6?case. Qed.

Lemma R14_inj : injective R14f.
Proof. by apply: can_inj R41f _ => z; apply/eqP; case: z; do 6?case. Qed.

Lemma R23_inj : injective R23f.
Proof. by apply: can_inj R32f _ => z; apply/eqP; case: z; do 6?case. Qed.

Lemma R50_inj : injective R50f.
Proof. by apply: can_inj R05f _ => z; apply/eqP; case: z; do 6?case. Qed.

Lemma R41_inj : injective R41f.
Proof. by apply: can_inj R14f _ => z; apply/eqP; case: z; do 6?case. Qed.

Lemma R32_inj : injective R32f.
Proof. by apply: can_inj R23f _ => z; apply/eqP; case: z; do 6?case. Qed.

Lemma R024_inj : injective R024f.
Proof. by apply: can_inj R042f _ => z; apply/eqP; case: z; do 6?case. Qed.

Lemma R042_inj : injective R042f.
Proof. by apply: can_inj R024f _ => z; apply/eqP; case: z; do 6?case. Qed.

Lemma R012_inj : injective R012f.
Proof. by apply: can_inj R021f _ => z; apply/eqP; case: z; do 6?case. Qed.

Lemma R021_inj : injective R021f.
Proof. by apply: can_inj R012f _ => z; apply/eqP; case: z; do 6?case. Qed.

Lemma R031_inj : injective R031f.
Proof. by apply: can_inj R013f _ => z; apply/eqP; case: z; do 6?case. Qed.


Lemma R013_inj : injective R013f.
Proof. by apply: can_inj R031f _ => z; apply/eqP; case: z; do 6?case. Qed.

Lemma R043_inj : injective R043f.
Proof. by apply: can_inj R034f _ => z; apply/eqP; case: z; do 6?case. Qed.

Lemma R034_inj : injective R034f.
Proof. by apply: can_inj R043f _ => z; apply/eqP; case: z; do 6?case. Qed.

Definition id3 := 1 : {perm cube}.

Definition s05 := (perm S05_inj).

Definition s14 : {perm cube}.
Proof.
apply: (@perm _ S14f); apply: can_inj S14f _ => z.
by apply/eqP; case: z; do 6?case.
Defined.

Definition s23 := (perm (inv_inj S23_inv)).
Definition r05 := (perm R05_inj).
Definition r14 := (perm R14_inj).
Definition r23 := (perm R23_inj).
Definition r50 := (perm R50_inj).
Definition r41 := (perm R41_inj).
Definition r32 := (perm R32_inj).
Definition r024 := (perm R024_inj).
Definition r042 := (perm R042_inj).
Definition r012 := (perm R012_inj).
Definition r021 := (perm R021_inj).
Definition r031 := (perm R031_inj).
Definition r013 := (perm R013_inj).
Definition r043 := (perm R043_inj).
Definition r034 := (perm R034_inj).

Definition s1 := (perm (inv_inj S1_inv)).
Definition s2 := (perm (inv_inj S2_inv)).
Definition s3 := (perm (inv_inj S3_inv)).
Definition s4 := (perm (inv_inj S4_inv)).
Definition s5 := (perm (inv_inj S5_inv)).
Definition s6 := (perm (inv_inj S6_inv)).

Definition dir_iso3 := [set p |
[|| id3 == p, s05 == p, s14 == p, s23 == p, r05 == p, r14 == p, r23 == p,
 r50 == p, r41 == p, r32 == p, r024 == p, r042 == p, r012 == p, r021 == p,
 r031 == p, r013 == p, r043 == p, r034 == p,
 s1 == p, s2 == p, s3 == p, s4 == p, s5 == p | s6 == p]].

Definition dir_iso3l := [:: id3; s05; s14; s23; r05; r14; r23; r50; r41;
  r32; r024; r042; r012; r021; r031; r013; r043; r034;
  s1; s2; s3; s4; s5; s6].

Definition S0 := [:: F5; F4; F3; F2; F1; F0].
Definition S0f (sc : cube) : cube := tnth [tuple of S0] sc.

Lemma S0_inv : involutive S0f.
Proof. by move=> z; apply/eqP; case: z; do 6?case. Qed.

Definition s0 := (perm (inv_inj S0_inv)).

Definition is_iso3 (p : {perm cube}) := forall fi, p (s0 fi) = s0 (p fi).

Lemma dir_iso_iso3 : forall p, p \in dir_iso3  -> is_iso3 p.
Proof.
move=> p; rewrite inE.
by do ?case/orP; move/eqP=> <- a; rewrite !permE; case: a; do 6?case.
Qed.

Lemma iso3_ndir : forall p, p \in dir_iso3  -> is_iso3 (s0 * p).
Proof.
move=> p; rewrite inE.
by do ?case/orP; move/eqP=> <- a; rewrite !(permM, permE); case: a; do 6?case.
Qed.

Definition sop (p : {perm cube}) : seq cube := val (val (val p)).

Lemma sop_inj : injective sop.
Proof. by do 2!apply: (inj_comp val_inj); apply: val_inj. Qed.

Definition prod_tuple (t1 t2 : seq cube) :=
  map (fun n : 'I_6 => nth F0 t2 n) t1.

Lemma sop_spec : forall x (n0 : 'I_6), nth F0 (sop x) n0 = x n0.
Proof. by move=> x n0; rewrite -pvalE unlock enum_rank_ord (tnth_nth F0). Qed.

Lemma prod_t_correct : forall (x y : {perm cube}) (i : cube),
  (x * y) i = nth F0 (prod_tuple (sop x) (sop y)) i.
Proof.
move=> x y i; rewrite permM -!sop_spec (nth_map F0) // size_tuple /=.
by rewrite card_ord ltn_ord.
Qed.

Lemma sop_morph : {morph sop : x y / x * y >-> prod_tuple x y}.
Proof.
move=> x y; apply: (@eq_from_nth _ F0) => [|/= i].
  by rewrite size_map !size_tuple.
rewrite size_tuple card_ord => lti6.
by rewrite -[i]/(val (Ordinal lti6)) sop_spec -prod_t_correct.
Qed.

Definition ecubes : seq cube := [:: F0; F1; F2; F3; F4; F5].

Lemma ecubes_def : ecubes = enum (@predT cube).
Proof. by apply: (inj_map val_inj); rewrite val_enum_ord. Qed.

Definition seq_iso_L := [::
   [:: F0; F1; F2; F3; F4; F5];
   S05; S14; S23; R05; R14; R23; R50; R41; R32;
   R024; R042; R012; R021; R031; R013; R043; R034;
   S1; S2; S3; S4; S5; S6].

Lemma seqs1 : forall f injf, sop (@perm _ f injf) = map f ecubes.
Proof.
move=> f ?; rewrite ecubes_def /sop /= -codom_ffun pvalE.
by apply: eq_codom; apply: permE.
Qed.

Lemma Lcorrect : seq_iso_L == map sop [:: id3; s05; s14; s23; r05; r14; r23;
  r50; r41; r32; r024; r042; r012; r021; r031; r013; r043; r034;
  s1; s2; s3; s4; s5; s6].
Proof. by rewrite /= !seqs1. Qed.

Lemma iso0_1 : dir_iso3 =i dir_iso3l.
Proof. by move=> p; rewrite /= !inE /= -!(eq_sym p). Qed.

Lemma L_iso : forall p, (p \in dir_iso3) = (sop p \in seq_iso_L).
Proof.
by move=> p; rewrite (eqP Lcorrect) mem_map ?iso0_1 //; apply: sop_inj.
Qed.

Lemma stable : forall x y,
  x \in dir_iso3 -> y \in dir_iso3 -> x * y \in dir_iso3.
Proof.
move=> x y; rewrite !L_iso sop_morph => Hx Hy.
by move/sop: y Hy; apply/allP; move/sop: x Hx; apply/allP; vm_compute.
Qed.

Lemma iso_eq_F0_F1 : forall r s : {perm cube}, r \in dir_iso3 ->
  s \in dir_iso3 -> r F0 = s F0 -> r F1 = s F1 -> r = s.
Proof.
move=> r s; rewrite !L_iso => hr hs hrs0 hrs1; apply: sop_inj; apply/eqP.
move/eqP: hrs0; apply/implyP; move/eqP: hrs1; apply/implyP; rewrite -!sop_spec.
by move/sop: r hr; apply/allP; move/sop: s hs; apply/allP; vm_compute.
Qed.

Lemma ndir_s0p : forall p, p \in dir_iso3 -> s0 * p \notin dir_iso3.
Proof.
move=> p; rewrite !L_iso sop_morph seqs1.
by move/sop: p; apply/allP; vm_compute.
Qed.

Definition indir_iso3l := map (mulg s0) dir_iso3l.

Definition iso3l := dir_iso3l ++ indir_iso3l.

Definition seq_iso3_L := map sop iso3l.

Lemma eqperm : forall p1 p2 : {perm cube},
  (p1 == p2) = all (fun s => p1 s == p2 s) ecubes.
Proof.
move=> p1 p2; apply/eqP/allP=> [-> // | Ep12]; apply/permP=> x.
by apply/eqP; rewrite Ep12 // ecubes_def mem_enum.
Qed.

Lemma iso_eq_F0_F1_F2 : forall r s : {perm cube}, is_iso3 r ->
   is_iso3 s -> r F0 = s F0 -> r F1 = s F1 ->  r F2 = s F2 -> r = s.
Proof.
move=> r s hr hs hrs0 hrs1 hrs2.
have:= hrs0; have:= hrs1; have:= hrs2.
have e23: F2 = s0 F3 by apply/eqP; rewrite permE /S0f (tnth_nth F0).
have e14: F1 = s0 F4 by apply/eqP; rewrite permE /S0f (tnth_nth F0).
have e05: F0 = s0 F5 by apply/eqP; rewrite permE /S0f (tnth_nth F0).
rewrite e23 e14 e05; rewrite !hr !hs.
move/perm_inj=> hrs3; move/perm_inj=> hrs4; move/perm_inj=> hrs5.
by apply/eqP; rewrite eqperm /= hrs0 hrs1 hrs2 hrs3 hrs4 hrs5 !eqxx.
Qed.

Ltac iso_tac :=
  let a := fresh "a" in apply/permP => a;
  apply/eqP; rewrite !permM !permE; case: a; do 6?case.

Ltac inv_tac :=
  apply: esym (etrans _ (mul1g _)); apply: canRL (mulgK _) _; iso_tac.

Lemma dir_s0p : forall p,  (s0 * p) \in dir_iso3 -> p \notin dir_iso3.
Proof.
move=> p Hs0p; move: (ndir_s0p Hs0p); rewrite mulgA.
have e:  (s0^-1=s0) by inv_tac.
by rewrite -{1}e mulVg mul1g.
Qed.

Definition is_iso3b p :=  (p * s0 == s0 * p).
Definition iso3 := [set p | is_iso3b p].

Lemma is_iso3P : forall p, reflect (is_iso3 p) (p \in iso3).
Proof.
move=> p; apply: (iffP idP); rewrite inE /iso3  /is_iso3b /is_iso3 => e.
  by move=> fi; rewrite -!permM (eqP e).
by apply/eqP; apply/permP=> z; rewrite !permM (e z).
Qed.

Lemma group_set_iso3 : group_set iso3.
Proof.
apply/group_setP; split.
  by apply/is_iso3P => fi; rewrite -!permM mulg1 mul1g.
move=> x1 y; rewrite /iso3 !inE /= /is_iso3.
rewrite /is_iso3b.
rewrite -mulgA.
move/eqP => hx1; move/eqP => hy.
rewrite hy !mulgA. by  rewrite -hx1.
Qed.

Canonical iso_group3 := Group group_set_iso3.

Lemma group_set_diso3 : group_set  dir_iso3.
Proof.
apply/group_setP; split; first by   rewrite inE eqxx /=.
by apply: stable.
Qed.
Canonical diso_group3 := Group group_set_diso3.

Lemma gen_diso3 :  dir_iso3 = <<[set r05; r14]>>.
Proof.
apply/setP; apply/subset_eqP; apply/andP; split; first last.
  by rewrite gen_subG; apply/subsetP => x; rewrite !inE;
    case/orP; move/eqP ->; rewrite eqxx !orbT.
apply/subsetP => x; rewrite !inE.
have -> : s05 = r05 * r05  by iso_tac.
have -> : s14 = r14 * r14  by iso_tac.
have -> : s23 = r14 * r14 * r05 * r05 by iso_tac.
have -> : r23 = r05 * r14 * r05 * r14 * r14 by iso_tac.
have -> : r50 = r05  * r05 * r05 by iso_tac.
have -> : r41 = r14 * r14 * r14 by iso_tac.
have -> : r32 = r14 * r14 * r14 * r05* r14 by iso_tac.
have -> : r024 = r05 * r14 * r14 * r14 by iso_tac.
have -> : r042 = r14 * r05 * r05 * r05 by iso_tac.
have -> : r012 = r14 * r05 by iso_tac.
have -> : r021 = r05 * r14 * r05 * r05 by iso_tac.
have -> : r031 = r05 * r14 by iso_tac.
have -> : r013 = r05 * r05 * r14 * r05 by iso_tac.
have -> : r043 = r14 * r14 * r14 * r05 by iso_tac.
have -> : r034 = r05 * r05 * r05 * r14 by iso_tac.
have -> : s1 = r14 * r14 * r05 by iso_tac.
have -> : s2 = r05 * r14 * r14 by iso_tac.
have -> : s3 = r05 * r14 * r05 by iso_tac.
have -> : s4 = r05 * r14  * r14 * r14 * r05 by iso_tac.
have -> : s5 = r14  * r05 * r05 by iso_tac.
have -> : s6 = r05 * r05 * r14 by iso_tac.
by do ?case/predU1P=> [<-|]; first exact: group1; last (move/eqP => <-);
   rewrite ?groupMl ?mem_gen // !inE eqxx ?orbT.
Qed.

Notation col_cubes := {ffun cube -> colors}.

Definition act_g (sc : col_cubes) (p : {perm cube}) : col_cubes :=
  [ffun z => sc (p^-1 z)].

Lemma act_g_1 :  forall k, act_g k 1 = k.
Proof. by move=> k; apply/ffunP=> a; rewrite ffunE invg1 permE. Qed.

Lemma act_g_morph :  forall k x y, act_g k (x * y) = act_g (act_g k x) y.
Proof. by move=> k x y; apply/ffunP=> a; rewrite !ffunE invMg permE. Qed.

Definition to_g := TotalAction act_g_1 act_g_morph.

Definition cube_coloring_number24 := #|orbit to_g diso_group3 @: setT|.

Lemma Fid3 : 'Fix_to_g[1] = setT.
Proof. by apply/setP=> x /=; rewrite (sameP afix1P eqP) !inE act1 eqxx. Qed.

Lemma card_Fid3 : #|'Fix_to_g[1]| = (n ^ 6)%N.
Proof.
rewrite -[6]card_ord -[n]card_ord -card_ffun_on Fid3 cardsT.
by symmetry; apply: eq_card => ff; apply/ffun_onP.
Qed.

Definition col0 (sc : col_cubes) : colors := sc F0.
Definition col1 (sc : col_cubes) : colors := sc F1.
Definition col2 (sc : col_cubes) : colors := sc F2.
Definition col3 (sc : col_cubes) : colors := sc F3.
Definition col4 (sc : col_cubes) : colors := sc F4.
Definition col5 (sc : col_cubes) : colors := sc F5.

Lemma eqperm_map2 : forall p1 p2 : col_cubes,
  (p1 == p2) = all (fun s => p1 s == p2 s) [:: F0; F1; F2; F3; F4; F5].
Proof.
move=> p1 p2; apply/eqP/allP=> [-> // | Ep12]; apply/ffunP=> x.
by apply/eqP; apply Ep12; case: x; do 6?case.
Qed.

Notation infE := (sameP afix1P eqP).

Lemma F_s05 :
  'Fix_to_g[s05] = [set x | (col1 x == col4 x) && (col2 x == col3 x)].
Proof.
have s05_inv: s05^-1=s05 by inv_tac.
apply/setP => x; rewrite infE !inE eqperm_map2 /= /act_g s05_inv !ffunE !permE /=.
apply sym_equal; rewrite !eqxx /= andbT/col1/col2/col3/col4/col5/col0.
by do 2![rewrite eq_sym; case: {+}(_ == _)=>  //= ].
Qed.

Lemma F_s14 :
   'Fix_to_g[s14]= [set x | (col0 x == col5 x) && (col2 x == col3 x)].
Proof.
have s14_inv: s14^-1=s14  by inv_tac.
apply/setP => x; rewrite infE !inE eqperm_map2 /= /act_g s14_inv !ffunE !permE /=.
apply sym_equal; rewrite !eqxx /= andbT/col1/col2/col3/col4/col5/col0.
by do 2![rewrite eq_sym; case: {+}(_ == _)=>  //= ].
Qed.

Lemma r05_inv : r05^-1 = r50.
Proof. by inv_tac. Qed.

Lemma r50_inv : r50^-1 = r05.
Proof. by inv_tac. Qed.

Lemma r14_inv : r14^-1 = r41.
Proof. by inv_tac. Qed.

Lemma r41_inv : r41^-1 = r14.
Proof. by inv_tac. Qed.

Lemma s23_inv : s23^-1 = s23.
Proof. by inv_tac. Qed.

Lemma F_s23 :
  'Fix_to_g[s23] = [set x | (col0 x == col5 x) && (col1 x == col4 x)].
Proof.
apply/setP => x; rewrite infE !inE eqperm_map2 /= /act_g s23_inv !ffunE !permE /=.
apply sym_equal; rewrite !eqxx /= andbT/col1/col2/col3/col4/col5/col0.
by do 2![rewrite eq_sym; case: {+}(_ == _)=>  //=].
Qed.

Lemma F_r05 : 'Fix_to_g[r05]=
  [set x | (col1 x == col2 x) && (col2 x == col3 x)
                                && (col3 x == col4 x)].
Proof.
apply sym_equal.
apply/setP => x; rewrite infE !inE eqperm_map2 /= /act_g r05_inv !ffunE !permE /=.
rewrite !eqxx /= !andbT /col1/col2/col3/col4/col5/col0.
by do 3![rewrite eq_sym; case E: {+}(_ == _); rewrite ?andbF // {E}(eqP E)  ].
Qed.

Lemma F_r50 : 'Fix_to_g[r50]=
  [set x | (col1 x == col2 x) && (col2 x == col3 x)
                                && (col3 x == col4 x)].
Proof.
apply/setP => x; rewrite infE !inE eqperm_map2 /= /act_g r50_inv !ffunE !permE /=.
apply sym_equal; rewrite !eqxx /= !andbT /col1/col2/col3/col4.
by do 3![rewrite eq_sym; case E: {+}(_ == _); rewrite ?andbF // {E}(eqP E) ].
Qed.

Lemma F_r23 : 'Fix_to_g[r23] =
  [set x | (col0 x == col1 x) && (col1 x == col4 x)
                                && (col4 x == col5 x)].
Proof.
have r23_inv: r23^-1 = r32 by inv_tac.
apply/setP => x; rewrite infE !inE eqperm_map2 /= /act_g r23_inv !ffunE !permE /=.
apply sym_equal; rewrite !eqxx /= !andbT /col1/col0/col5/col4.
by do 3![rewrite eq_sym; case E: {+}(_ == _); rewrite ?andbF  // {E}(eqP E)].
Qed.

Lemma F_r32 : 'Fix_to_g[r32] =
  [set x | (col0 x == col1 x) && (col1 x == col4 x)
                                && (col4 x == col5 x)].
Proof.
have r32_inv: r32^-1 = r23 by inv_tac.
apply/setP => x; rewrite infE !inE eqperm_map2 /= /act_g r32_inv !ffunE !permE /=.
apply sym_equal; rewrite !eqxx /= !andbT /col1/col0/col5/col4.
by do 3![rewrite eq_sym; case E: {+}(_ == _); rewrite ?andbF  // {E}(eqP E)].
Qed.

Lemma F_r14 : 'Fix_to_g[r14] =
  [set x | (col0 x == col2 x) && (col2 x == col3 x) && (col3 x == col5 x)].
Proof.
apply/setP => x; rewrite infE !inE eqperm_map2 /= /act_g r14_inv !ffunE !permE /=.
apply sym_equal; rewrite !eqxx /= !andbT /col2/col0/col5/col3.
by do 3![rewrite eq_sym; case E: {+}(_ == _); rewrite ?andbF  // {E}(eqP E)].
Qed.

Lemma F_r41 : 'Fix_to_g[r41] =
  [set x | (col0 x == col2 x) && (col2 x == col3 x) && (col3 x == col5 x)].
Proof.
apply/setP => x; rewrite infE !inE eqperm_map2 /= /act_g r41_inv !ffunE !permE /=.
apply sym_equal; rewrite !eqxx /= !andbT /col2/col0/col5/col3.
by do 3![rewrite eq_sym; case E: {+}(_ == _); rewrite ?andbF  // {E}(eqP E)].
Qed.

Lemma F_r024 : 'Fix_to_g[r024] =
  [set x | (col0 x == col4 x) && (col4 x == col2  x) && (col1 x == col3 x)
       && (col3 x == col5 x) ].
Proof.
have r024_inv: r024^-1 = r042 by inv_tac.
apply/setP => x; rewrite infE !inE eqperm_map2 /= /act_g r024_inv !ffunE !permE /=.
apply sym_equal; rewrite ?eqxx /= !andbT /col0/col1/col2/col3/col4/col5.
by do 4![rewrite eq_sym; case E: {+}(_ == _); rewrite ?andbF  // ?{E}(eqP E)].
Qed.

Lemma F_r042 : 'Fix_to_g[r042] =
  [set x | (col0 x == col4 x) && (col4 x == col2  x) && (col1 x == col3 x)
       && (col3 x == col5 x)].
Proof.
have r042_inv: r042^-1 = r024 by inv_tac.
apply/setP => x; rewrite infE !inE eqperm_map2 /= /act_g r042_inv !ffunE !permE /=.
apply sym_equal; rewrite ?eqxx /= !andbT /col0/col1/col2/col3/col4/col5.
by do 4![rewrite eq_sym; case E: {+}(_ == _); rewrite ?andbF  // ?{E}(eqP E)].
Qed.

Lemma F_r012 : 'Fix_to_g[r012] =
  [set x | (col0 x == col2 x) && (col2 x == col1  x) && (col3 x == col4 x)
       && (col4 x == col5 x)].
Proof.
have r012_inv: r012^-1 = r021 by inv_tac.
apply/setP => x; rewrite infE !inE eqperm_map2 /= /act_g r012_inv !ffunE !permE /=.
apply sym_equal; rewrite ?eqxx /= !andbT /col0/col1/col2/col3/col4/col5.
by do 4![rewrite eq_sym; case E: {+}(_ == _); rewrite ?andbF  // ?{E}(eqP E)].
Qed.

Lemma F_r021 : 'Fix_to_g[r021] =
  [set x | (col0 x == col2 x) && (col2 x == col1  x) && (col3 x == col4 x)
       && (col4 x == col5 x)].
Proof.
have r021_inv: r021^-1 = r012 by inv_tac.
apply/setP => x; rewrite infE !inE eqperm_map2 /= /act_g r021_inv !ffunE !permE /=.
apply sym_equal; rewrite ?eqxx /= !andbT /col0/col1/col2/col3/col4/col5.
do 4![rewrite eq_sym; case E: {+}(_ == _); rewrite ?andbF  // ?{E}(eqP E)].
Qed.

Lemma F_r031 : 'Fix_to_g[r031] =
  [set x | (col0 x == col3 x) && (col3 x == col1  x) && (col2 x == col4 x)
       && (col4 x == col5 x)].
Proof.
have r031_inv: r031^-1 = r013 by inv_tac.
apply/setP => x; rewrite infE !inE eqperm_map2 /= /act_g r031_inv !ffunE !permE /=.
apply sym_equal; rewrite ?eqxx /= !andbT /col0/col1/col2/col3/col4/col5.
by do 4![rewrite eq_sym; case E: {+}(_ == _); rewrite ?andbF  // ?{E}(eqP E)].
Qed.

Lemma F_r013 : 'Fix_to_g[r013] =
  [set x | (col0 x == col3 x) && (col3 x == col1  x) && (col2 x == col4 x)
       && (col4 x == col5 x)].
Proof.
have r013_inv: r013^-1 = r031 by inv_tac.
apply/setP => x; rewrite infE !inE eqperm_map2 /= /act_g r013_inv !ffunE !permE /=.
apply sym_equal; rewrite ?eqxx /= !andbT /col0/col1/col2/col3/col4/col5.
by do 4![rewrite eq_sym; case E: {+}(_ == _); rewrite ?andbF  // ?{E}(eqP E)].
Qed.

Lemma F_r043 : 'Fix_to_g[r043] =
  [set x | (col0 x == col4 x) && (col4 x == col3  x) && (col1 x == col2 x)
       && (col2 x == col5 x)].
Proof.
have r043_inv: r043^-1 = r034 by inv_tac.
apply/setP => x; rewrite infE !inE eqperm_map2 /= /act_g r043_inv !ffunE !permE /=.
apply sym_equal; rewrite ?eqxx /= !andbT /col0/col1/col2/col3/col4/col5.
by do 4![rewrite eq_sym; case E: {+}(_ == _); rewrite ?andbF  // ?{E}(eqP E)].
Qed.

Lemma F_r034 : 'Fix_to_g[r034] =
  [set x | (col0 x == col4 x) && (col4 x == col3  x) && (col1 x == col2 x)
       && (col2 x == col5 x)].
Proof.
have r034_inv: r034^-1 = r043 by inv_tac.
apply/setP => x; rewrite infE !inE eqperm_map2 /= /act_g r034_inv !ffunE !permE /=.
apply sym_equal; rewrite ?eqxx /= !andbT /col0/col1/col2/col3/col4/col5.
by do 4![rewrite eq_sym; case E: {+}(_ == _); rewrite ?andbF  // ?{E}(eqP E)].
Qed.

Lemma F_s1 : 'Fix_to_g[s1] =
  [set x | (col0 x == col5 x) && (col1 x == col2  x) && (col3 x == col4 x)].
Proof.
have s1_inv: s1^-1 = s1 by inv_tac.
apply/setP => x; rewrite infE !inE eqperm_map2 /= /act_g s1_inv !ffunE !permE /=.
apply sym_equal; rewrite ?eqxx /= !andbT /col0/col1/col2/col3/col4/col5.
by do 3![rewrite eq_sym; case E: {+}(_ == _); rewrite ?andbF  // ?{E}(eqP E)].
Qed.

Lemma F_s2 : 'Fix_to_g[s2] =
  [set x | (col0 x == col5 x) && (col1 x == col3  x) && (col2 x == col4 x)].
Proof.
have s2_inv: s2^-1 = s2 by inv_tac.
apply/setP => x; rewrite infE !inE eqperm_map2 /= /act_g s2_inv !ffunE !permE /=.
apply sym_equal; rewrite ?eqxx /= !andbT /col0/col1/col2/col3/col4/col5.
by do 3![rewrite eq_sym; case E: {+}(_ == _); rewrite ?andbF  // ?{E}(eqP E)].
Qed.

Lemma F_s3 : 'Fix_to_g[s3] =
  [set x | (col0 x == col1 x) && (col2 x == col3  x) && (col4 x == col5 x)].
Proof.
have s3_inv: s3^-1 = s3 by inv_tac.
apply/setP => x; rewrite infE !inE eqperm_map2 /= /act_g s3_inv !ffunE !permE /=.
apply sym_equal; rewrite ?eqxx /= !andbT /col0/col1/col2/col3/col4/col5.
by do 3![rewrite eq_sym; case E: {+}(_ == _); rewrite ?andbF  // ?{E}(eqP E)].
Qed.

Lemma F_s4 : 'Fix_to_g[s4] =
  [set x | (col0 x == col4 x) && (col1 x == col5  x) && (col2 x == col3 x)].
Proof.
have s4_inv: s4^-1 = s4 by inv_tac.
apply/setP => x; rewrite infE !inE eqperm_map2 /= /act_g s4_inv !ffunE !permE /=.
apply sym_equal; rewrite ?eqxx /= !andbT /col0/col1/col2/col3/col4/col5.
by do 3![rewrite eq_sym; case E: {+}(_ == _); rewrite ?andbF  // ?{E}(eqP E)].
Qed.

Lemma F_s5 : 'Fix_to_g[s5] =
  [set x | (col0 x == col2 x) && (col1 x == col4  x) && (col3 x == col5 x)].
Proof.
have s5_inv: s5^-1 = s5 by inv_tac.
apply/setP => x; rewrite infE !inE eqperm_map2 /= /act_g s5_inv !ffunE !permE /=.
apply sym_equal; rewrite ?eqxx /= !andbT /col0/col1/col2/col3/col4/col5.
by do 3![rewrite eq_sym; case E: {+}(_ == _); rewrite ?andbF  // ?{E}(eqP E)].
Qed.

Lemma F_s6 : 'Fix_to_g[s6] =
  [set x | (col0 x == col3 x) && (col1 x == col4  x) && (col2 x == col5 x)].
Proof.
have s6_inv: s6^-1 = s6 by inv_tac.
apply/setP => x; rewrite infE !inE eqperm_map2 /= /act_g s6_inv !ffunE !permE /=.
apply sym_equal; rewrite ?eqxx /= !andbT /col0/col1/col2/col3/col4/col5.
by do 3![rewrite eq_sym; case E: {+}(_ == _); rewrite ?andbF  // ?{E}(eqP E)].
Qed.

Lemma uniq4_uniq6 : forall x y z t : cube,
  uniq [:: x; y; z; t] -> exists u, exists v, uniq [:: x; y; z; t; u; v].
Proof.
move=> x y z t Uxt; move: (cardC (mem [:: x; y; z; t])).
rewrite card_ord  (card_uniq_tuple Uxt) => hcard.
have hcard2: #|predC (mem [:: x; y; z; t])| = 2.
  by apply: (@addnI 4); rewrite /injective  hcard.
have:  #|predC (mem [:: x; y; z; t])| != 0 by rewrite hcard2.
case/existsP=> u Hu; exists u.
move: (cardC (mem [:: x; y; z; t; u])); rewrite card_ord => hcard5.
have: #|[predC [:: x; y; z; t; u]]| !=0.
  rewrite -lt0n  -(ltn_add2l #|[:: x; y; z; t; u]|) hcard5 addn0.
  by apply: (leq_ltn_trans (card_size [:: x; y; z; t; u])).
case/existsP=> v; rewrite inE (mem_cat _ [:: _; _; _; _]).
case/norP=> Hv Huv; exists v.
rewrite (cat_uniq [:: x; y; z; t]) Uxt andTb.
by rewrite -rev_uniq /= negb_or Hu orbF Hv Huv.
Qed.

Lemma card_n4 : forall x y z t : cube, uniq [:: x; y; z; t] ->
   #|[set p : col_cubes | (p x == p y) && (p z == p t)]| = (n ^ 4)%N.
Proof.
move=> x y z t  Uxt. rewrite -[n]card_ord .
case: (uniq4_uniq6 Uxt) => u; case=> v Uxv.
pose ff (p : col_cubes) := (p x, p z, p u , p v).
rewrite -(@card_in_image _ _ ff); first last.
  move=> p1 p2; rewrite !inE.
  case/andP=> p1y p1t; case/andP=> p2y p2t  [px pz] pu pv.
  have eqp12: all (fun i => p1 i == p2 i) [:: x; y; z; t; u; v].
   by rewrite /= -(eqP p1y) -(eqP p1t) -(eqP p2y) -(eqP p2t) px pz pu pv !eqxx.
  apply/ffunP=> i; apply/eqP; apply: (allP eqp12).
  by rewrite (subset_cardP _ (subset_predT _)) // (card_uniqP Uxv) card_ord.
have ->:forall n, (n ^ 4)%N= (n*n*n*n)%N.
  by move=> n0; rewrite (expnD n0 2 2) -mulnn mulnA.
rewrite -!card_prod; apply: eq_card => [] [[[c d]e ]g] /=; apply/imageP.
rewrite (cat_uniq [::x; y; z; t]) in Uxv; case/and3P: Uxv => _ hasxt.
rewrite /= !inE andbT.
move/negbTE=> nuv .
rewrite (cat_uniq [::x; y]) in Uxt; case/and3P: Uxt => _.
rewrite /= !andbT orbF; case/norP; rewrite !inE => nxyz nxyt _.
move: hasxt; rewrite /= !orbF; case/norP; rewrite !inE orbA.
case/norP  => nxyu nztu.
rewrite orbA; case/norP=> nxyv nztv.
exists [ffun i => if pred2 x y i then c else if pred2 z t i then d
                    else if u==i then e else g].
  rewrite !inE /= !ffunE //= !eqxx orbT //= !eqxx /= orbT.
  by rewrite (negbTE nxyz) (negbTE nxyt).
rewrite {}/ff !ffunE /= !eqxx /=.
rewrite (negbTE nxyz) (negbTE nxyu) (negbTE nztu) (negbTE nxyv) (negbTE nztv).
by rewrite nuv.
Qed.

Lemma card_n3_3 : forall x y z t: cube, uniq [:: x; y; z; t] ->
  #|[set p : col_cubes | (p x == p y) && (p y == p z)&& (p z == p t)]|
      = (n ^ 3)%N.
Proof.
move=> x y z t Uxt; rewrite -[n]card_ord .
case: (uniq4_uniq6 Uxt) => u; case=> v Uxv.
pose ff (p : col_cubes) := (p x, p u , p v);
   rewrite -(@card_in_image _ _ ff); first last.
  move=> p1 p2; rewrite !inE.
  case/andP; case/andP => p1xy p1yz p1zt.
  case/andP; case/andP => p2xy p2yz p2zt [px pu] pv.
  have eqp12: all (fun i => p1 i == p2 i) [:: x; y; z; t; u; v].
    by rewrite /= -(eqP p1zt) -(eqP p2zt) -(eqP p1yz) -(eqP p2yz) -(eqP p1xy)
     -(eqP p2xy) px pu pv !eqxx.
  apply/ffunP=> i; apply/eqP; apply: (allP eqp12).
  by rewrite (subset_cardP _ (subset_predT _)) // (card_uniqP Uxv) card_ord.
have ->:forall n, (n ^ 3)%N= (n*n*n)%N.
  by move=> n0; rewrite (expnD n0 2 1) -mulnn expn1.
rewrite -!card_prod; apply: eq_card => [] [[c d]e ] /=; apply/imageP.
rewrite (cat_uniq [::x; y; z; t]) in Uxv; case/and3P: Uxv => _ hasxt.
rewrite /uniq !inE !andbT; move/negbTE=> nuv.
exists
   [ffun i => if (i \in [:: x; y; z; t]) then c else if u == i then d else e].
  by rewrite /= !inE   !ffunE !inE  !eqxx !orbT !eqxx.
rewrite {}/ff !ffunE !inE /= !eqxx /=; move: hasxt; rewrite nuv.
by do 8![case E: ( _ ==  _ ); rewrite ?(eqP E)/= ?inE ?eqxx //= ?E {E}].
Qed.

Lemma card_n2_3 : forall x y z t u v: cube, uniq [:: x; y; z; t; u; v] ->
  #|[set p : col_cubes | (p x == p y) && (p y == p z)&& (p t == p u )
                            && (p u== p v)]|  = (n ^ 2)%N.
Proof.
move=> x y z t u v  Uxv; rewrite -[n]card_ord .
pose ff (p : col_cubes) := (p x, p t); rewrite -(@card_in_image _ _ ff); first last.
  move=> p1 p2; rewrite !inE.
  case/andP; case/andP; case/andP => p1xy p1yz p1tu p1uv.
  case/andP; case/andP; case/andP => p2xy p2yz p2tu p2uv [px pu].
  have eqp12: all (fun i => p1 i == p2 i) [:: x; y; z; t; u; v].
    by rewrite /= -(eqP p1yz) -(eqP p2yz) -(eqP p1xy) -(eqP p2xy) -(eqP p1uv)
      -(eqP p2uv) -(eqP p1tu) -(eqP p2tu) px  pu !eqxx.
  apply/ffunP=> i; apply/eqP; apply: (allP eqp12).
  by rewrite (subset_cardP _ (subset_predT _)) // (card_uniqP Uxv) card_ord.
have ->:forall n, (n ^ 2)%N= (n*n)%N by move=> n0; rewrite -mulnn .
   rewrite -!card_prod; apply: eq_card => [] [c d]/=; apply/imageP.
rewrite (cat_uniq [::x; y; z]) in Uxv; case/and3P: Uxv => Uxt hasxt nuv .
move: hasxt; rewrite /= !orbF; case/norP; rewrite !inE => nxyzt.
case/norP => nxyzu nxyzv.
exists [ffun i =>  if (i \in [:: x; y; z] ) then c else  d].
  rewrite !inE /= !ffunE !inE //= !eqxx !orbT !eqxx //=.
  by rewrite (negbTE nxyzt) (negbTE nxyzu)(negbTE nxyzv) !eqxx.
by rewrite {}/ff !ffunE  !inE /= !eqxx /= (negbTE nxyzt).
Qed.

Lemma card_n3s : forall x y z t u v: cube, uniq [:: x; y; z; t; u; v] ->
  #|[set p : col_cubes | (p x == p y) && (p z == p t)&& (p u == p v )]|
    = (n ^ 3)%N.
Proof.
move=> x y z t u v  Uxv; rewrite -[n]card_ord .
pose ff (p : col_cubes) := (p x, p z, p u).
rewrite -(@card_in_image _ _ ff); first last.
  move=> p1 p2; rewrite !inE.
  case/andP; case/andP =>  p1xy p1zt p1uv.
  case/andP; case/andP => p2xy p2zt p2uv  [px pz] pu.
  have eqp12: all (fun i => p1 i == p2 i) [:: x; y; z; t; u; v].
    by rewrite /= -(eqP p1xy) -(eqP p2xy) -(eqP p1zt) -(eqP p2zt) -(eqP p1uv)
      -(eqP p2uv)  px  pz pu !eqxx.
  apply/ffunP=> i; apply/eqP; apply: (allP eqp12).
  by rewrite (subset_cardP _ (subset_predT _)) // (card_uniqP Uxv) card_ord.
have ->:forall n, (n ^ 3)%N= (n*n*n)%N.
  by move=> n0; rewrite (expnD n0 2 1) -mulnn expn1.
rewrite -!card_prod. apply: eq_card => [] [[c d]e ] /=; apply/imageP.
rewrite (cat_uniq [::x; y; z; t]) in Uxv; case/and3P: Uxv => Uxt hasxt nuv .
rewrite (cat_uniq [::x; y]) in Uxt; case/and3P: Uxt => _.
rewrite /= !orbF !andbT; case/norP; rewrite !inE => nxyz nxyt _.
move: hasxt; rewrite /= !orbF; case/norP; rewrite !inE orbA.
case/norP => nxyu nztu.
rewrite orbA; case/norP=> nxyv nztv.
exists [ffun i =>  if (i \in [:: x; y] ) then c else  if (i \in [:: z; t] )
                         then d else e].
  rewrite !inE /= !ffunE !inE // !eqxx !orbT !eqxx //=.
  by rewrite (negbTE nxyz) (negbTE nxyt)(negbTE nxyu) (negbTE nztu)
           (negbTE nxyv) (negbTE nztv) !eqxx.
rewrite {}/ff !ffunE !inE  /= !eqxx /=.
by rewrite (negbTE nxyz) (negbTE nxyu) (negbTE nztu).
Qed.

Lemma burnside_app_iso3 :
  (cube_coloring_number24 * 24 =
                   n ^ 6 + 6 * n ^ 3 + 3 * n ^ 4 + 8 * (n ^ 2)  + 6 * n ^ 3)%N.
Proof.
pose iso_list :=[::id3; s05; s14; s23; r05; r14; r23; r50; r41; r32;
  r024; r042; r012; r021; r031; r013; r043; r034;
  s1; s2; s3; s4; s5; s6].
rewrite (burnside_formula iso_list) => [||p]; last first.
- by rewrite !inE /= !(eq_sym _ p).
- apply: map_uniq (fun p : {perm cube} => (p F0, p F1)) _ _.
  have bsr:(fun p : {perm cube} => (p F0, p F1)) =1
    (fun p  => (nth F0 p F0, nth F0 p F1)) \o sop.
    by move=> x; rewrite /= -2!sop_spec.
  by rewrite (eq_map bsr) map_comp  -(eqP Lcorrect); vm_compute.
rewrite !big_cons big_nil {1}card_Fid3 /= F_s05 F_s14 F_s23 F_r05 F_r14 F_r23
  F_r50 F_r41 F_r32 F_r024 F_r042 F_r012 F_r021 F_r031 F_r013 F_r043  F_r034
  F_s1  F_s2 F_s3 F_s4 F_s5 F_s6.
by rewrite !card_n4 // !card_n3_3 // !card_n2_3 // !card_n3s //; ring.
Qed.

End cube_colouring.

End colouring.

Corollary burnside_app_iso_3_3col: cube_coloring_number24 3 = 57.
Proof.
by apply/eqP; rewrite -(@eqn_pmul2r 24) // burnside_app_iso3.
Qed.


Corollary burnside_app_iso_2_4col: square_coloring_number8 4 = 55.
Proof. by apply/eqP; rewrite -(@eqn_pmul2r 8) // burnside_app_iso. Qed.




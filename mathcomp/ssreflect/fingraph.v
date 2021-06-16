(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat.
From mathcomp Require Import seq path fintype.

(******************************************************************************)
(* This file develops the theory of finite graphs represented by an "edge"    *)
(* relation over a finType T; this mainly amounts to the theory of the        *)
(* transitive closure of such relations.                                      *)
(*   For g : T -> seq T, e : rel T and f : T -> T we define:                  *)
(*         grel g == the adjacency relation y \in g x of the graph g.         *)
(*       rgraph e == the graph (x |-> enum (e x)) of the relation e.          *)
(*    dfs g n v x == the list of points traversed by a depth-first search of  *)
(*                   the g, at depth n, starting from x, and avoiding v.      *)
(* dfs_path g v x y <-> there is a path from x to y in g \ v.                 *)
(*      connect e == the reflexive transitive closure of e (computed by dfs). *)
(*  connect_sym e <-> connect e is symmetric, hence an equivalence relation.  *)
(*       root e x == a representative of connect e x, which is the component  *)
(*                   of x in the transitive closure of e.                     *)
(*        roots e == the codomain predicate of root e.                        *)
(*     n_comp e a == the number of e-connected components of a, when a is     *)
(*                   e-closed and connect e is symmetric.                     *)
(*                   equivalence classes of connect e if connect_sym e holds. *)
(*     closed e a == the collective predicate a is e-invariant.               *)
(*    closure e a == the e-closure of a (the image of a under connect e).     *)
(* rel_adjunction h e e' a <-> in the e-closed domain a, h is the left part   *)
(*                   of an adjunction from e to another relation e'.          *)
(*     fconnect f == connect (frel f), i.e., "connected under f iteration".   *)
(*      froot f x == root (frel f) x, the root of the orbit of x under f.     *)
(*       froots f == roots (frel f) == orbit representatives for f.           *)
(*      orbit f x == lists the f-orbit of x.                                  *)
(*   findex f x y == index of y in the f-orbit of x.                          *)
(*      order f x == size (cardinal) of the f-orbit of x.                     *)
(*  order_set f n == elements of f-order n.                                   *)
(*         finv f == the inverse of f, if f is injective.                     *)
(*                := finv f x := iter (order x).-1 f x.                       *)
(*      fcard f a == number of orbits of f in a, provided a is f-invariant    *)
(*                   f is one-to-one.                                         *)
(*    fclosed f a == the collective predicate a is f-invariant.               *)
(*   fclosure f a == the closure of a under f iteration.                      *)
(* fun_adjunction == rel_adjunction (frel f).                                 *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition grel (T : eqType) (g : T -> seq T) := [rel x y | y \in g x].

(* Decidable connectivity in finite types.                                  *)
Section Connect.

Variable T : finType.

Section Dfs.

Variable g : T -> seq T.
Implicit Type v w a : seq T.

Fixpoint dfs n v x :=
  if x \in v then v else
  if n is n'.+1 then foldl (dfs n') (x :: v) (g x) else v.

Lemma subset_dfs n v a : v \subset foldl (dfs n) v a.
Proof.
elim: n a v => [|n IHn]; first by elim=> //= *; rewrite if_same.
elim=> //= x a IHa v; apply: subset_trans {IHa}(IHa _); case: ifP => // _.
by apply: subset_trans (IHn _ _); apply/subsetP=> y; apply: predU1r.
Qed.

Inductive dfs_path v x y : Prop :=
  DfsPath p of path (grel g) x p & y = last x p & [disjoint x :: p & v].

Lemma dfs_pathP n x y v :
  #|T| <= #|v| + n -> y \notin v -> reflect (dfs_path v x y) (y \in dfs n v x).
Proof.
have dfs_id w z: z \notin w -> dfs_path w z z.
  by exists [::]; rewrite ?disjoint_has //= orbF.
elim: n => [|n IHn] /= in x y v * => le_v'_n not_vy.
  rewrite addn0 (geq_leqif (subset_leqif_card (subset_predT _))) in le_v'_n.
  by rewrite predT_subset in not_vy.
have [v_x | not_vx] := ifPn.
  by rewrite (negPf not_vy); right=> [] [p _ _]; rewrite disjoint_has /= v_x.
set v1 := x :: v; set a := g x; have sub_dfs := subsetP (subset_dfs n _ _).
have [-> | neq_yx] := eqVneq y x.
  by rewrite sub_dfs ?mem_head //; left; apply: dfs_id.
apply: (@equivP (exists2 x1, x1 \in a & dfs_path v1 x1 y)); last first.
  split=> {IHn} [[x1 a_x1 [p g_p p_y]] | [p /shortenP[]]].
    rewrite disjoint_has has_sym /= has_sym /= => /norP[_ not_pv].
    by exists (x1 :: p); rewrite /= ?a_x1 // disjoint_has negb_or not_vx.
  case=> [_ _ _ eq_yx | x1 p1 /=]; first by case/eqP: neq_yx.
  case/andP=> a_x1 g_p1 /andP[not_p1x _] /subsetP p_p1 p1y not_pv.
  exists x1 => //; exists p1 => //.
  rewrite disjoint_sym disjoint_cons not_p1x disjoint_sym.
  by move: not_pv; rewrite disjoint_cons => /andP[_ /disjointWl->].
have{neq_yx not_vy}: y \notin v1 by apply/norP.
have{le_v'_n not_vx}: #|T| <= #|v1| + n by rewrite cardU1 not_vx addSnnS.
elim: {x v}a v1 => [|x a IHa] v /= le_v'_n not_vy.
  by rewrite (negPf not_vy); right=> [] [].
set v2 := dfs n v x; have v2v: v \subset v2 := subset_dfs n v [:: x].
have [v2y | not_v2y] := boolP (y \in v2).
  by rewrite sub_dfs //; left; exists x; [apply: mem_head | apply: IHn].
apply: {IHa}(equivP (IHa _ _ not_v2y)).
  by rewrite (leq_trans le_v'_n) // leq_add2r subset_leq_card.
split=> [] [x1 a_x1 [p g_p p_y not_pv]].
  exists x1; [exact: predU1r | exists p => //].
  by rewrite disjoint_sym (disjointWl v2v) // disjoint_sym.
suffices not_p1v2: [disjoint x1 :: p & v2].
  case/predU1P: a_x1 => [def_x1 | ]; last by exists x1; last exists p.
  case/pred0Pn: not_p1v2; exists x; rewrite /= def_x1 mem_head /=.
  suffices not_vx: x \notin v by apply/IHn; last apply: dfs_id.
  by move: not_pv; rewrite disjoint_cons def_x1 => /andP[].
apply: contraR not_v2y => /pred0Pn[x2 /andP[/= p_x2 v2x2]].
case/splitPl: p_x2 p_y g_p not_pv => p0 p2 p0x2.
rewrite last_cat cat_path -cat_cons lastI cat_rcons {}p0x2 => p2y /andP[_ g_p2].
rewrite disjoint_cat disjoint_cons => /and3P[{p0}_ not_vx2 not_p2v].
have{not_vx2 v2x2} [p1 g_p1 p1_x2 not_p1v] := IHn _ _ v le_v'_n not_vx2 v2x2.
apply/IHn=> //; exists (p1 ++ p2); rewrite ?cat_path ?last_cat -?p1_x2 ?g_p1 //.
by rewrite -cat_cons disjoint_cat not_p1v.
Qed.

Lemma dfsP x y :
  reflect (exists2 p, path (grel g) x p & y = last x p) (y \in dfs #|T| [::] x).
Proof.
apply: (iffP (dfs_pathP _ _ _)); rewrite ?card0 // => [] [p]; exists p => //.
by rewrite disjoint_sym disjoint0.
Qed.

End Dfs.

Variable e : rel T.

Definition rgraph x := enum (e x).

Lemma rgraphK : grel rgraph =2 e.
Proof. by move=> x y; rewrite /= mem_enum. Qed.

Definition connect : rel T := fun x y => y \in dfs rgraph #|T| [::] x.
Canonical connect_app_pred x := ApplicativePred (connect x).

Lemma connectP x y :
  reflect (exists2 p, path e x p & y = last x p) (connect x y).
Proof.
apply: (equivP (dfsP _ x y)).
by split=> [] [p e_p ->]; exists p => //; rewrite (eq_path rgraphK) in e_p *.
Qed.

Lemma connect_trans : transitive connect.
Proof.
move=> x y z /connectP[p e_p ->] /connectP[q e_q ->]; apply/connectP.
by exists (p ++ q); rewrite ?cat_path ?e_p ?last_cat.
Qed.

Lemma connect0 x : connect x x.
Proof. by apply/connectP; exists [::]. Qed.

Lemma eq_connect0 x y : x = y -> connect x y.
Proof. by move->; apply: connect0. Qed.

Lemma connect1 x y : e x y -> connect x y.
Proof. by move=> e_xy; apply/connectP; exists [:: y]; rewrite /= ?e_xy. Qed.

Lemma path_connect x p : path e x p -> subpred (mem (x :: p)) (connect x).
Proof.
move=> e_p y p_y; case/splitPl: p / p_y e_p => p q <-.
by rewrite cat_path => /andP[e_p _]; apply/connectP; exists p.
Qed.

Lemma connect_cycle p : cycle e p -> {in p &, forall x y, connect x y}.
Proof.
move=> e_p x y /rot_to[i q rip]; rewrite -(mem_rot i) rip => yqx.
have /= : cycle e (x :: q) by rewrite -rip rot_cycle.
case/splitPl: yqx => r s lxr; rewrite rcons_cat cat_path => /andP[xr _].
by apply/connectP; exists r.
Qed.

Definition root x := odflt x (pick (connect x)).

Definition roots : pred T := fun x => root x == x.
Canonical roots_pred := ApplicativePred roots.

Definition n_comp_mem (m_a : mem_pred T) := #|predI roots m_a|.

Lemma connect_root x : connect x (root x).
Proof. by rewrite /root; case: pickP; rewrite ?connect0. Qed.

Definition connect_sym := symmetric connect.

Hypothesis sym_e : connect_sym.

Lemma same_connect : left_transitive connect.
Proof. exact: sym_left_transitive connect_trans. Qed.

Lemma same_connect_r : right_transitive connect.
Proof. exact: sym_right_transitive connect_trans. Qed.

Lemma same_connect1 x y : e x y -> connect x =1 connect y.
Proof. by move/connect1; apply: same_connect. Qed.

Lemma same_connect1r x y : e x y -> connect^~ x =1 connect^~ y.
Proof. by move/connect1; apply: same_connect_r. Qed.

Lemma rootP x y : reflect (root x = root y) (connect x y).
Proof.
apply: (iffP idP) => e_xy.
  by rewrite /root -(eq_pick (same_connect e_xy)); case: pickP e_xy => // ->.
by apply: (connect_trans (connect_root x)); rewrite e_xy sym_e connect_root.
Qed.

Lemma root_root x : root (root x) = root x.
Proof. exact/esym/rootP/connect_root. Qed.

Lemma roots_root x : roots (root x).
Proof. exact/eqP/root_root. Qed.

Lemma root_connect x y : (root x == root y) = connect x y.
Proof. exact: sameP eqP (rootP x y). Qed.

Definition closed_mem m_a := forall x y, e x y -> in_mem x m_a -> in_mem y m_a.

Definition closure_mem m_a : pred T :=
  fun y => [exists x, in_mem x m_a && connect x y].

End Connect.

Hint Resolve connect0 : core.

Notation n_comp e a := (n_comp_mem e (mem a)).
Notation closed e a := (closed_mem e (mem a)).
Notation closure e a := (closure_mem e (mem a)).

Prenex Implicits connect root roots.

Arguments dfsP {T g x y}.
Arguments connectP {T e x y}.
Arguments rootP [T e] _ {x y}.

Notation fconnect f := (connect (coerced_frel f)).
Notation froot f := (root (coerced_frel f)).
Notation froots f := (roots (coerced_frel f)).
Notation fcard_mem f := (n_comp_mem (coerced_frel f)).
Notation fcard f a := (fcard_mem f (mem a)).
Notation fclosed f a := (closed (coerced_frel f) a).
Notation fclosure f a := (closure (coerced_frel f) a).

Section EqConnect.

Variable T : finType.
Implicit Types (e : rel T) (a : {pred T}).

Lemma connect_sub e e' :
  subrel e (connect e') -> subrel (connect e) (connect e').
Proof.
move=> e'e x _ /connectP[p e_p ->]; elim: p x e_p => //= y p IHp x /andP[exy].
by move/IHp; apply: connect_trans; apply: e'e.
Qed.

Lemma relU_sym e e' :
  connect_sym e -> connect_sym e' -> connect_sym (relU e e').
Proof.
move=> sym_e sym_e'; apply: symmetric_from_pre => x _ /connectP[p e_p ->].
elim: p x e_p => //= y p IHp x /andP[e_xy /IHp{IHp}/connect_trans]; apply.
case/orP: e_xy => /connect1; rewrite (sym_e, sym_e');
  by apply: connect_sub y x => x y e_xy; rewrite connect1 //= e_xy ?orbT.
Qed.

Lemma eq_connect e e' : e =2 e' -> connect e =2 connect e'.
Proof.
move=> eq_e x y; apply/connectP/connectP=> [] [p e_p ->];
  by exists p; rewrite // (eq_path eq_e) in e_p *.
Qed.

Lemma eq_n_comp e e' : connect e =2 connect e' -> n_comp_mem e =1 n_comp_mem e'.
Proof.
move=> eq_e [a]; apply: eq_card => x /=.
by rewrite !inE /= /roots /root /= (eq_pick (eq_e x)).
Qed.

Lemma eq_n_comp_r {e} a a' : a =i a' -> n_comp e a = n_comp e a'.
Proof. by move=> eq_a; apply: eq_card => x; rewrite inE /= eq_a. Qed.

Lemma n_compC a e : n_comp e T = n_comp e a + n_comp e [predC a].
Proof.
rewrite /n_comp_mem (eq_card (fun _ => andbT _)) -(cardID a); congr (_ + _).
by apply: eq_card => x; rewrite !inE andbC.
Qed.

Lemma eq_root e e' : e =2 e' -> root e =1 root e'.
Proof. by move=> eq_e x; rewrite /root (eq_pick (eq_connect eq_e x)). Qed.

Lemma eq_roots e e' : e =2 e' -> roots e =1 roots e'.
Proof. by move=> eq_e x; rewrite /roots (eq_root eq_e). Qed.

End EqConnect.

Section Closure.

Variables (T : finType) (e : rel T).
Hypothesis sym_e : connect_sym e.
Implicit Type a : {pred T}.

Lemma same_connect_rev : connect e =2 connect (fun x y => e y x).
Proof.
suff crev e': subrel (connect (fun x : T => e'^~ x)) (fun x => (connect e')^~x).
  by move=> x y; rewrite sym_e; apply/idP/idP; apply: crev.
move=> x y /connectP[p e_p p_y]; apply/connectP.
exists (rev (belast x p)); first by rewrite p_y rev_path.
by rewrite -(last_cons x) -rev_rcons p_y -lastI rev_cons last_rcons.
Qed.

Lemma intro_closed a : (forall x y, e x y -> x \in a -> y \in a) -> closed e a.
Proof. by []. Qed.

Lemma closed_connect a :
  closed e a -> forall x y, connect e x y -> (x \in a) -> (y \in a).
Proof.
move=> cl_a x _ /connectP[p e_p ->].
by elim: p x e_p => //= y p IHp x /andP[/cl_a *]; apply: IHp; auto.
Qed.

Lemma closed_connect_sym a :
  closed e a -> forall x y, connect e x y -> (x \in a) = (y \in a).
Proof.
by move=> cl_a x y c_xy; apply/idP/idP; apply/closed_connect; rewrite // sym_e.
Qed.

(* this used to be the definition of closed *)
Lemma closed_sym a : closed e a -> forall x y, e x y -> (x \in a) = (y \in a).
Proof. move => cl_a x y /connect1; exact: closed_connect_sym. Qed.

Lemma connect_closed x : closed e (connect e x).
Proof. by move => y z /connect1 c_yz c_xy; apply: connect_trans c_yz. Qed.

Lemma predC_closed a : closed e a -> closed e [predC a].
Proof.
by move => cl_a x y /connect1 ?; apply/contraNN/closed_connect; rewrite // sym_e.
Qed.

Lemma closure_closed a : closed e (closure e a).
Proof.
apply: intro_closed => x y xy /exists_inP [z z_a c_zx].
by apply/exists_inP; exists z => //; apply: connect_trans (connect1 xy).
Qed.

Lemma mem_closure a : {subset a <= closure e a}.
Proof. by move => x a_x; apply/exists_inP; exists x. Qed.

Lemma subset_closure a : a \subset closure e a.
Proof. by apply/subsetP; apply: mem_closure. Qed.

Lemma n_comp_closure2 x y :
  n_comp e (closure e (pred2 x y)) = (~~ connect e x y).+1.
Proof.
rewrite -(root_connect sym_e) -card2; apply: eq_card => z.
apply/idP/idP=> [/andP [/eqP {2}<- /exists_inP [t xyt etz]]|].
  by case/pred2P : xyt => <-; rewrite inE (rootP sym_e etz) eqxx ?orbT.
by case/pred2P => ->; rewrite !inE roots_root //; apply/existsP;
  [exists x | exists y]; rewrite !inE eqxx ?orbT connect_root.
Qed.

Lemma n_comp_connect x : n_comp e (connect e x) = 1.
Proof.
rewrite -(card1 (root e x)); apply: eq_card => y.
apply/andP/eqP => [[/eqP r_y /rootP-> //] | ->] /=.
by rewrite inE connect_root roots_root.
Qed.

End Closure.

Section Orbit.

Variables (T : finType) (f : T -> T).

Definition order x := #|fconnect f x|.

Definition orbit x := traject f x (order x).

Definition findex x y := index y (orbit x).

Definition finv x := iter (order x).-1 f x.

Lemma fconnect_iter n x : fconnect f x (iter n f x).
Proof.
apply/connectP.
by exists (traject f (f x) n); [apply: fpath_traject | rewrite last_traject].
Qed.

Lemma fconnect1 x : fconnect f x (f x).
Proof. exact: (fconnect_iter 1). Qed.

Lemma fconnect_finv x : fconnect f x (finv x).
Proof. exact: fconnect_iter. Qed.

Lemma orderSpred x : (order x).-1.+1 = order x.
Proof. by rewrite /order (cardD1 x) [_ x _]connect0. Qed.

Lemma size_orbit x : size (orbit x) = order x.
Proof. exact: size_traject. Qed.

Lemma looping_order x : looping f x (order x).
Proof.
apply: contraFT (ltnn (order x)); rewrite -looping_uniq => /card_uniqP.
rewrite size_traject => <-; apply: subset_leq_card.
by apply/subsetP=> _ /trajectP[i _ ->]; apply: fconnect_iter.
Qed.

Lemma fconnect_orbit x y : fconnect f x y = (y \in orbit x).
Proof.
apply/idP/idP=> [/connectP[_ /fpathP[m ->] ->] | /trajectP[i _ ->]].
  by rewrite last_traject; apply/loopingP/looping_order.
exact: fconnect_iter.
Qed.

Lemma in_orbit x : x \in orbit x. Proof. by rewrite -fconnect_orbit. Qed.
Hint Resolve in_orbit : core.

Lemma order_gt0 x : order x > 0. Proof. by rewrite -orderSpred. Qed.
Hint Resolve order_gt0 : core.

Lemma orbit_uniq x : uniq (orbit x).
Proof.
rewrite /orbit -orderSpred looping_uniq; set n := (order x).-1.
apply: contraFN (ltnn n) => /trajectP[i lt_i_n eq_fnx_fix].
rewrite orderSpred -(size_traject f x n).
apply: (leq_trans (subset_leq_card _) (card_size _)); apply/subsetP=> z.
rewrite inE fconnect_orbit => /trajectP[j le_jn ->{z}].
rewrite -orderSpred -/n ltnS leq_eqVlt in le_jn.
by apply/trajectP; case/predU1P: le_jn => [->|]; [exists i | exists j].
Qed.

Lemma findex_max x y : fconnect f x y -> findex x y < order x.
Proof. by rewrite [_ y]fconnect_orbit -index_mem size_orbit. Qed.

Lemma findex_iter x i : i < order x -> findex x (iter i f x) = i.
Proof.
move=> lt_ix; rewrite -(nth_traject f lt_ix) /findex index_uniq ?orbit_uniq //.
by rewrite size_orbit.
Qed.

Lemma iter_findex x y : fconnect f x y -> iter (findex x y) f x = y.
Proof.
rewrite [_ y]fconnect_orbit => fxy; pose i := index y (orbit x).
have lt_ix: i < order x by rewrite -size_orbit index_mem.
by rewrite -(nth_traject f lt_ix) nth_index.
Qed.

Lemma findex0 x : findex x x = 0.
Proof. by rewrite /findex /orbit -orderSpred /= eqxx. Qed.

Lemma findex_eq0 x y : (findex x y == 0) = (x == y).
Proof. by rewrite /findex /orbit -orderSpred /=; case: (x == y). Qed.

Lemma fconnect_invariant (T' : eqType) (k : T -> T') :
  invariant f k =1 xpredT -> forall x y, fconnect f x y -> k x = k y.
Proof.
move=> eq_k_f x y /iter_findex <-; elim: {y}(findex x y) => //= n ->.
by rewrite (eqP (eq_k_f _)).
Qed.

Lemma mem_orbit x : {homo f : y / y \in orbit x}.
Proof.
by move=> y; rewrite -!fconnect_orbit => /connect_trans->//; apply: fconnect1.
Qed.

Lemma image_orbit x : {subset image f (orbit x) <= orbit x}.
Proof.
by move=> _ /mapP[y yin ->]; apply: mem_orbit; rewrite ?mem_enum in yin.
Qed.

Section orbit_in.

Variable S : {pred T}.

Hypothesis f_in : {homo f : x / x \in S}.
Hypothesis injf : {in S &, injective f}.

Lemma finv_in : {homo finv : x / x \in S}.
Proof. by move=> x xS; rewrite iter_in. Qed.

Lemma f_finv_in : {in S, cancel finv f}.
Proof.
move=> x xS; move: (looping_order x) (orbit_uniq x).
rewrite /looping /orbit -orderSpred looping_uniq /= /looping; set n := _.-1.
case/predU1P=> // /trajectP[i lt_i_n]; rewrite -iterSr.
by move=> /injf ->; rewrite ?(iter_in _ f_in) //; case/trajectP; exists i.
Qed.

Lemma finv_f_in : {in S, cancel f finv}.
Proof. by move=> x xS; apply/injf; rewrite ?iter_in ?f_finv_in ?f_in. Qed.

Lemma finv_inj_in : {in S &, injective finv}.
Proof. by move=> x y xS yS q; rewrite -(f_finv_in xS) q f_finv_in. Qed.

Lemma fconnect_sym_in : {in S &, forall x y, fconnect f x y = fconnect f y x}.
Proof.
suff Sf : {in S &, forall x y, fconnect f x y -> fconnect f y x}.
  by move=> *; apply/idP/idP=> /Sf->.
move=> x _ xS _ /connectP [p f_p ->]; elim: p => //= y p IHp in x xS f_p *.
case/andP: f_p => /eqP <- /(IHp _ (f_in xS)) /connect_trans -> //.
by apply: (connect_trans (fconnect_finv _)); rewrite finv_f_in.
Qed.

Lemma iter_order_in : {in S, forall x, iter (order x) f x = x}.
Proof. by move=> x xS; rewrite -orderSpred iterS; apply: f_finv_in. Qed.

Lemma iter_finv_in n :
  {in S, forall x, n <= order x -> iter n finv x = iter (order x - n) f x}.
Proof.
move=> x xS; rewrite -[x in LHS]iter_order_in => // /subnKC {1}<-.
move: (_ - n) => m; rewrite iterD; elim: n => // n {2}<-.
by rewrite iterSr /= finv_f_in // -iterD iter_in.
Qed.

Lemma cycle_orbit_in : {in S, forall x, (fcycle f) (orbit x)}.
Proof.
move=> x xS; rewrite /orbit -orderSpred (cycle_path x) /= last_traject.
by rewrite -/(finv x) fpath_traject f_finv_in ?eqxx.
Qed.

Lemma fpath_finv_in p x :
  (x \in S) && (fpath finv x p) =
    (last x p \in S) && (fpath f (last x p) (rev (belast x p))).
Proof.
elim: p x => //= y p IHp x; rewrite rev_cons rcons_path.
transitivity [&& y \in S, f y == x & fpath finv y p].
  apply/and3P/and3P => -[xS /eqP<- fxp]; split;
  by rewrite ?f_finv_in ?finv_f_in ?finv_in ?f_in.
rewrite andbCA {}IHp !andbA [RHS]andbC -andbA; congr [&& _, _ & _].
by case: p => //= z p; rewrite rev_cons last_rcons.
Qed.

Lemma fpath_finv_f_in p : {in S, forall x,
  fpath finv x p -> fpath f (last x p) (rev (belast x p))}.
Proof. by move=> x xS /(conj xS)/andP; rewrite fpath_finv_in => /andP[]. Qed.

Lemma fpath_f_finv_in p x : last x p \in S ->
  fpath f (last x p) (rev (belast x p)) -> fpath finv x p.
Proof. by move=> lS /(conj lS)/andP; rewrite -fpath_finv_in => /andP[]. Qed.

End orbit_in.

Lemma injectivePcycle x :
  reflect {in orbit x &, injective f} (fcycle f (orbit x)).
Proof.
apply: (iffP idP) => [/inj_cycle//|/cycle_orbit_in].
by apply; [apply: mem_orbit|apply: in_orbit].
Qed.

Section orbit_inj.

Hypothesis injf : injective f.

Lemma f_finv : cancel finv f. Proof. exact: (in1T (f_finv_in _ (in2W _))). Qed.

Lemma finv_f : cancel f finv. Proof. exact: (in1T (finv_f_in _ (in2W _))). Qed.

Lemma finv_bij : bijective finv.
Proof. by exists f; [apply: f_finv|apply: finv_f]. Qed.

Lemma finv_inj : injective finv. Proof. exact: (can_inj f_finv). Qed.

Lemma fconnect_sym x y : fconnect f x y = fconnect f y x.
Proof. exact: (in2T (fconnect_sym_in _ (in2W _))). Qed.

Let symf := fconnect_sym.

Lemma iter_order x : iter (order x) f x = x.
Proof. exact: (in1T (iter_order_in _ (in2W _))). Qed.

Lemma iter_finv n x : n <= order x -> iter n finv x = iter (order x - n) f x.
Proof. exact: (in1T (@iter_finv_in _ _ (in2W _) _)). Qed.

Lemma cycle_orbit x : fcycle f (orbit x).
Proof. exact: (in1T (cycle_orbit_in _ (in2W _))). Qed.

Lemma fpath_finv x p : fpath finv x p = fpath f (last x p) (rev (belast x p)).
Proof. exact: (@fpath_finv_in T _ (in2W _)). Qed.

Lemma same_fconnect_finv : fconnect finv =2 fconnect f.
Proof.
move=> x y; rewrite (same_connect_rev symf); apply: {x y}eq_connect => x y /=.
by rewrite (canF_eq finv_f) eq_sym.
Qed.

Lemma fcard_finv : fcard_mem finv =1 fcard_mem f.
Proof. exact: eq_n_comp same_fconnect_finv. Qed.

Definition order_set n : pred T := [pred x | order x == n].

Lemma fcard_order_set n (a : {pred T}) :
  a \subset order_set n -> fclosed f a -> fcard f a * n = #|a|.
Proof.
move=> a_n cl_a; rewrite /n_comp_mem; set b := [predI froots f & a].
suff <-: #|preim (froot f) b| = #|b| * n.
  apply: eq_card => x; rewrite !inE (roots_root fconnect_sym).
  by rewrite -(closed_connect_sym symf cl_a (connect_root _ x)).
have{cl_a a_n} (x): b x -> froot f x = x /\ order x = n.
  by case/andP=> /eqP-> /(subsetP a_n)/eqnP->.
elim: {a b}#|b| {1 3 4}b (eqxx #|b|) => [|m IHm] b def_m f_b.
  by rewrite eq_card0 // => x; apply: (pred0P def_m).
have [x b_x | b0] := pickP b; last by rewrite (eq_card0 b0) in def_m.
have [r_x ox_n] := f_b x b_x; rewrite (cardD1 x) [x \in b]b_x eqSS in def_m.
rewrite mulSn -{1}ox_n -(IHm _ def_m) => [|_ /andP[_ /f_b //]].
rewrite -(cardID (fconnect f x)); congr (_ + _); apply: eq_card => y.
  by apply: andb_idl => /= fxy; rewrite !inE -(rootP symf fxy) r_x.
by congr (~~ _ && _); rewrite /= /in_mem /= symf -(root_connect symf) r_x.
Qed.

Lemma fclosed1 (a : {pred T}) :
  fclosed f a -> forall x, (x \in a) = (f x \in a).
Proof. move => cl_a x. exact: (closed_sym symf) _ (eqxx _). Qed.

Lemma same_fconnect1 x : fconnect f x =1 fconnect f (f x).
Proof. by apply: same_connect1 => /=. Qed.

Lemma same_fconnect1_r x y : fconnect f x y = fconnect f x (f y).
Proof. by apply: same_connect1r x => /=. Qed.

Lemma fcard_gt0P (a : {pred T}) :
  fclosed f a -> reflect (exists x, x \in a) (0 < fcard f a).
Proof.
move=> clfA; apply: (iffP card_gt0P) => [[x /andP[]]|[x xA]]; first by exists x.
exists (froot f x); rewrite inE roots_root /=; last exact: fconnect_sym.
by rewrite (closed_connect clfA (connect_root _ x)).
Qed.

Lemma fcard_gt1P (A : {pred T}) :
  fclosed f A ->
  reflect (exists2 x, x \in A & exists2 y, y \in A & ~~ fconnect f x y)
          (1 < fcard f A).
Proof.
move=> clAf; apply: (iffP card_gt1P) => [|[x xA [y yA not_xfy]]].
  move=> [x [y [/andP [/= rfx xA] /andP[/= rfy yA] xDy]]].
  by exists x; try exists y; rewrite // -root_connect // (eqP rfx) (eqP rfy).
exists (froot f x), (froot f y); rewrite !inE !roots_root ?root_connect //=.
by split => //; rewrite (closed_connect clAf (connect_root _ _)).
Qed.

End orbit_inj.
Hint Resolve orbit_uniq : core.

Section fcycle_p.
Variables (p : seq T) (f_p : fcycle f p).

Section mem_cycle.

Variable (Up : uniq p) (x : T) (p_x : x \in p).

(* fconnect_cycle does not dependent on Up *)
Lemma fconnect_cycle y : fconnect f x y = (y \in p).
Proof.
have [i q def_p] := rot_to p_x; rewrite -(mem_rot i p) def_p.
have{i def_p} /andP[/eqP q_x f_q]: (f (last x q) == x) && fpath f x q.
  by have:= f_p; rewrite -(rot_cycle i) def_p (cycle_path x).
apply/idP/idP=> [/connectP[_ /fpathP[j ->] ->] | ]; last exact: path_connect.
case/fpathP: f_q q_x => n ->; rewrite !last_traject -iterS => def_x.
by apply: (@loopingP _ f x n.+1); rewrite /looping def_x /= mem_head.
Qed.

(* order_le_cycle does not dependent on Up *)
Lemma order_le_cycle : order x <= size p.
Proof.
apply: leq_trans (card_size _); apply/subset_leq_card/subsetP=> y.
by rewrite !(fconnect_cycle, inE) ?eqxx.
Qed.

Lemma order_cycle : order x = size p.
Proof. by rewrite -(card_uniqP Up); apply: (eq_card fconnect_cycle). Qed.

Lemma orbitE : orbit x = rot (index x p) p.
Proof.
set i := index _ _; rewrite /orbit order_cycle -(size_rot i) rot_index// -/i.
set q := _ ++ _; suffices /fpathP[j ->]: fpath f x q by rewrite /= size_traject.
by move: f_p; rewrite -(rot_cycle i) rot_index// (cycle_path x); case/andP.
Qed.

Lemma orbit_rot_cycle : {i : nat | orbit x = rot i p}.
Proof. by rewrite orbitE; exists (index x p). Qed.

End mem_cycle.

Let f_inj := inj_cycle f_p.
Let homo_f := mem_fcycle f_p.

Lemma finv_cycle : {homo finv : x / x \in p}. Proof. exact: finv_in. Qed.

Lemma f_finv_cycle : {in p, cancel finv f}. Proof. exact: f_finv_in. Qed.

Lemma finv_f_cycle : {in p, cancel f finv}. Proof. exact: finv_f_in. Qed.

Lemma finv_inj_cycle : {in p &, injective finv}. Proof. exact: finv_inj_in. Qed.

Lemma iter_finv_cycle n :
  {in p, forall x, n <= order x -> iter n finv x = iter (order x - n) f x}.
Proof. exact: iter_finv_in. Qed.

Lemma cycle_orbit_cycle : {in p, forall x, fcycle f (orbit x)}.
Proof. exact: cycle_orbit_in. Qed.

Lemma fpath_finv_cycle q x : (x \in p) && (fpath finv x q) =
  (last x q \in p) && fpath f (last x q) (rev (belast x q)).
Proof. exact: fpath_finv_in. Qed.

Lemma fpath_finv_f_cycle q : {in p, forall x,
  fpath finv x q -> fpath f (last x q) (rev (belast x q))}.
Proof. exact: fpath_finv_f_in. Qed.

Lemma fpath_f_finv_cycle q x : last x q \in p ->
  fpath f (last x q) (rev (belast x q)) -> fpath finv x q.
Proof. exact: fpath_f_finv_in. Qed.

Lemma prevE x : x \in p -> prev p x = finv x.
Proof.
move=> x_p; have /eqP/(congr1 finv) := prev_cycle f_p x_p.
by rewrite finv_f_cycle// mem_prev.
Qed.

End fcycle_p.

Section fcycle_cons.
Variables (x : T) (p : seq T) (f_p : fcycle f (x :: p)).

Lemma fcycle_rconsE : rcons (x :: p) x = traject f x (size p).+2.
Proof. by rewrite rcons_cons; have /fpathE-> := f_p; rewrite size_rcons. Qed.

Lemma fcycle_consE : x :: p = traject f x (size p).+1.
Proof. by have := fcycle_rconsE; rewrite trajectSr => /rcons_inj[/= <-]. Qed.

Lemma fcycle_consEflatten : exists k, x :: p = flatten (nseq k.+1 (orbit x)).
Proof.
move: f_p; rewrite fcycle_consE; elim/ltn_ind: (size p) => n IHn t_cycle.
have := order_le_cycle t_cycle (mem_head _ _); rewrite size_traject.
case: ltngtP => [||<-] //; last by exists 0; rewrite /= cats0.
rewrite ltnS => n_ge _; have := t_cycle.
rewrite -(subnKC n_ge) -addnS trajectD.
rewrite (iter_order_in (mem_fcycle f_p) (inj_cycle f_p)) ?mem_head//.
set m := (_ - _) => cycle_cat.
have [||k->] := IHn m; last by exists k.+1.
  by rewrite ltn_subrL (leq_trans _ n_ge) ?order_gt0.
move: cycle_cat; rewrite -orderSpred/= rcons_cat rcons_cons -cat_rcons.
by rewrite cat_path last_rcons => /andP[].
Qed.

Lemma undup_cycle_cons : undup (x :: p) = orbit x.
Proof.
by have [n {1}->] := fcycle_consEflatten; rewrite undup_flatten_nseq ?undup_id.
Qed.

End fcycle_cons.

Section fcycle_undup.

Variable (p : seq T) (f_p : fcycle f p).

Lemma fcycleEflatten : exists k, p = flatten (nseq k (undup p)).
Proof.
case: p f_p => [//|x q] f_q; first by exists 0.
have [k {1}->] := @fcycle_consEflatten x q f_q.
by exists k.+1; rewrite undup_cycle_cons.
Qed.

Lemma fcycle_undup : fcycle f (undup p).
Proof.
case: p f_p => [//|x q] f_q; rewrite undup_cycle_cons//.
by rewrite (cycle_orbit_in (mem_fcycle f_q) (inj_cycle f_q)) ?mem_head.
Qed.

Let p_undup_uniq := undup_uniq p.
Let f_inj := inj_cycle f_p.
Let homo_f := mem_fcycle f_p.

Lemma in_orbit_cycle : {in p &, forall x, orbit x =i p}.
Proof.
by move=> x y xp yp; rewrite (orbitE fcycle_undup)// ?mem_rot ?mem_undup.
Qed.

Lemma eq_order_cycle : {in p &, forall x y, order y = order x}.
Proof. by move=> x y xp yp; rewrite !(order_cycle fcycle_undup) ?mem_undup. Qed.

Lemma iter_order_cycle : {in p &, forall x y, iter (order x) f y = y}.
Proof.
by move=> x y xp yp; rewrite (eq_order_cycle yp) ?(iter_order_in homo_f f_inj).
Qed.

End fcycle_undup.

Section fconnect.

Lemma fconnect_eqVf x y : fconnect f x y = (x == y) || fconnect f (f x) y.
Proof.
apply/idP/idP => [/iter_findex <-|/predU1P [<-|] //]; last first.
  exact/connect_trans/fconnect1.
by case: findex => [|i]; rewrite ?eqxx// iterSr fconnect_iter orbT.
Qed.

(*****************************************************************************)
(* Lemma orbitPcycle is of type "The Following Are Equivalent", which means  *)
(* all four statements are equivalent to each other. In order to use it, one *)
(* has to apply it to the natural numbers corresponding to the line, e.g.    *)
(* `orbitPcycle 0 2 : fcycle f (orbit x) <-> exists k, iter k.+1 f x = x`.   *)
(* examples of this are in order_id_cycle and fconnnect_f.                   *)
(* One may also use lemma all_iffLR to get a one sided implication, as in    *)
(* orderPcycle.                                                              *)
(*****************************************************************************)
Lemma orbitPcycle {x} : [<->
  (* 0 *) fcycle f (orbit x);
  (* 1 *) order (f x) = order x;
  (* 2 *) x \in fconnect f (f x);
  (* 3 *) exists k, iter k.+1 f x = x;
  (* 4 *) iter (order x) f x = x;
  (* 5 *) {in orbit x &, injective f}].
Proof.
tfae=> [xorbit_cycle|||[k fkx]|fx y z|/injectivePcycle//].
- by apply: eq_order_cycle xorbit_cycle _ _ _ _; rewrite ?mem_orbit.
- move=> /subset_cardP/(_ _)->; rewrite ?inE//; apply/subsetP=> y.
  by apply: connect_trans; apply: fconnect1.
- by exists (findex (f x) x); rewrite // iterSr iter_findex.
- apply: (@iter_order_cycle (traject f x k.+1)); rewrite /= ?mem_head//.
  by apply/fpathP; exists k.+1; rewrite trajectSr -iterSr fkx.
- rewrite -!fconnect_orbit => /iter_findex <- /iter_findex <-.
  move/(congr1 (iter (order x).-1 f)).
  by rewrite -!iterSr !orderSpred -!iterD ![order _ + _]addnC !iterD fx.
Qed.

Lemma order_id_cycle x : fcycle f (orbit x) -> order (f x) = order x.
Proof. by move/(orbitPcycle 0 1). Qed.

Inductive order_spec_cycle x : bool -> Type :=
| OrderStepCycle of fcycle f (orbit x) & order x = order (f x) :
    order_spec_cycle x true
| OrderStepNoCycle of ~~ fcycle f (orbit x) & order x = (order (f x)).+1 :
    order_spec_cycle x false.

Lemma orderPcycle x : order_spec_cycle x (fcycle f (orbit x)).
Proof.
have [xcycle|Ncycle] := boolP (fcycle f (orbit x)); constructor => //.
  by rewrite order_id_cycle.
rewrite /order (eq_card (_ : _ =1 [predU1 x & fconnect f (f x)])).
  by rewrite cardU1 inE (contraNN (all_iffLR orbitPcycle 2 0)).
by move=> y; rewrite !inE fconnect_eqVf eq_sym.
Qed.

Lemma fconnect_f x : fconnect f (f x) x = fcycle f (orbit x).
Proof. by apply/idP/idP => /(orbitPcycle 0 2). Qed.

Lemma fconnect_findex x y :
  fconnect f x y -> y != x -> findex x y = (findex (f x) y).+1.
Proof.
rewrite /findex fconnect_orbit /orbit -orderSpred /= inE => /orP [-> //|].
rewrite eq_sym; move=> yin /negPf->; have [_ eq_o|_ ->//] := orderPcycle x.
by rewrite -(orderSpred (f x)) trajectSr -cats1 index_cat -eq_o yin.
Qed.

End fconnect.

End Orbit.

Hint Resolve in_orbit mem_orbit order_gt0 orbit_uniq : core.
Prenex Implicits order orbit findex finv order_set.
Arguments orbitPcycle {T f x}.

Section FconnectId.

Variable T : finType.

Lemma fconnect_id (x : T) : fconnect id x =1 xpred1 x.
Proof. by move=> y; rewrite (@fconnect_cycle _ _ [:: x]) //= ?inE ?eqxx. Qed.

Lemma order_id (x : T) : order id x = 1.
Proof. by rewrite /order (eq_card (fconnect_id x)) card1. Qed.

Lemma orbit_id (x : T) : orbit id x = [:: x].
Proof. by rewrite /orbit order_id. Qed.

Lemma froots_id (x : T) : froots id x.
Proof. by rewrite /roots -fconnect_id connect_root. Qed.

Lemma froot_id (x : T) : froot id x = x.
Proof. by apply/eqP; apply: froots_id. Qed.

Lemma fcard_id (a : {pred T}) : fcard id a = #|a|.
Proof. by apply: eq_card => x; rewrite inE froots_id. Qed.

End FconnectId.

Section FconnectEq.

Variables (T : finType) (f f' : T -> T).

Lemma finv_eq_can : cancel f f' -> finv f =1 f'.
Proof.
move=> fK; have inj_f := can_inj fK.
by apply: bij_can_eq fK; [apply: injF_bij | apply: finv_f].
Qed.

Hypothesis eq_f : f =1 f'.
Let eq_rf := eq_frel eq_f.

Lemma eq_fconnect : fconnect f =2 fconnect f'.
Proof. exact: eq_connect eq_rf. Qed.

Lemma eq_fcard : fcard_mem f =1 fcard_mem f'.
Proof. exact: eq_n_comp eq_fconnect. Qed.

Lemma eq_finv : finv f =1 finv f'.
Proof.
by move=> x; rewrite /finv /order (eq_card (eq_fconnect x)) (eq_iter eq_f).
Qed.

Lemma eq_froot : froot f =1 froot f'.
Proof. exact: eq_root eq_rf. Qed.

Lemma eq_froots : froots f =1 froots f'.
Proof. exact: eq_roots eq_rf. Qed.

End FconnectEq.

Section FinvEq.

Variables (T : finType) (f : T -> T).
Hypothesis injf : injective f.

Lemma finv_inv : finv (finv f) =1 f.
Proof. exact: (finv_eq_can (f_finv injf)). Qed.

Lemma order_finv : order (finv f) =1 order f.
Proof. by move=> x; apply: eq_card (same_fconnect_finv injf x). Qed.

Lemma order_set_finv n : order_set (finv f) n =i order_set f n.
Proof. by move=> x; rewrite !inE order_finv. Qed.

End FinvEq.

Section RelAdjunction.

Variables (T T' : finType) (h : T' -> T) (e : rel T) (e' : rel T').
Hypotheses (sym_e : connect_sym e) (sym_e' : connect_sym e').

Record rel_adjunction_mem m_a := RelAdjunction {
  rel_unit x : in_mem x m_a -> {x' : T' | connect e x (h x')};
  rel_functor x' y' :
    in_mem (h x') m_a -> connect e' x' y' = connect e (h x') (h y')
}.

Variable a : {pred T}.
Hypothesis cl_a : closed e a.

Local Notation rel_adjunction := (rel_adjunction_mem (mem a)).

Lemma intro_adjunction (h' : forall x, x \in a -> T') :
   (forall x a_x,
      [/\ connect e x (h (h' x a_x))
        & forall y a_y, e x y -> connect e' (h' x a_x) (h' y a_y)]) ->
   (forall x' a_x,
      [/\ connect e' x' (h' (h x') a_x)
        & forall y', e' x' y' -> connect e (h x') (h y')]) ->
  rel_adjunction.
Proof.
move=> Aee' Ae'e; split=> [y a_y | x' z' a_x].
  by exists (h' y a_y); case/Aee': (a_y).
apply/idP/idP=> [/connectP[p e'p ->{z'}] | /connectP[p e_p p_z']].
  elim: p x' a_x e'p => //= y' p IHp x' a_x.
  case: (Ae'e x' a_x) => _ Ae'x /andP[/Ae'x e_xy /IHp e_yz] {Ae'x}.
  by apply: connect_trans (e_yz _); rewrite // -(closed_connect_sym _ cl_a e_xy).
case: (Ae'e x' a_x) => /connect_trans-> //.
elim: p {x'}(h x') p_z' a_x e_p => /= [|y p IHp] x p_z' a_x.
  by rewrite -p_z' in a_x *; case: (Ae'e _ a_x); rewrite sym_e'.
case/andP=> e_xy /(IHp _ p_z') e'yz.
have a_y: y \in a by rewrite -(closed_sym _ cl_a e_xy).
by apply: connect_trans (e'yz a_y); case: (Aee' _ a_x) => _ ->.
Qed.

Lemma strict_adjunction :
    injective h -> a \subset codom h -> rel_base h e e' [predC a] ->
  rel_adjunction.
Proof.
move=> /= injh h_a a_ee'; pose h' x Hx := iinv (subsetP h_a x Hx).
apply: (@intro_adjunction h') => [x a_x | x' a_x].
  rewrite f_iinv connect0; split=> // y a_y e_xy.
  by rewrite connect1 // -a_ee' !f_iinv ?negbK.
rewrite [h' _ _]iinv_f //; split=> // y' e'xy.
by rewrite connect1 // a_ee' ?negbK.
Qed.

Let ccl_a := closed_connect_sym sym_e cl_a.

Lemma adjunction_closed : rel_adjunction -> closed e' [preim h of a].
Proof.
case=> _ Ae'e; apply: intro_closed => // x' y' /connect1 e'xy a_x.
by rewrite Ae'e // in e'xy; rewrite !inE -(ccl_a e'xy).
Qed.

Lemma adjunction_n_comp :
  rel_adjunction -> n_comp e a = n_comp e' [preim h of a].
Proof.
case=> Aee' Ae'e.
have inj_h: {in predI (roots e') [preim h of a] &, injective (root e \o h)}.
  move=> x' y' /andP[/eqP r_x' /= a_x'] /andP[/eqP r_y' _] /(rootP sym_e).
  by rewrite -Ae'e // => /(rootP sym_e'); rewrite r_x' r_y'.
rewrite /n_comp_mem -(card_in_image inj_h); apply: eq_card => x.
apply/andP/imageP=> [[/eqP rx a_x] | [x' /andP[/eqP r_x' a_x'] ->]]; last first.
  by rewrite /= -(ccl_a (connect_root _ _)) roots_root.
have [y' e_xy]:= Aee' x a_x; pose x' := root e' y'.
have ay': h y' \in a by rewrite -(ccl_a e_xy).
have e_yx: connect e (h y') (h x') by rewrite -Ae'e ?connect_root.
exists x'; first by rewrite inE /= -(ccl_a e_yx) ?roots_root.
by rewrite /= -(rootP sym_e e_yx) -(rootP sym_e e_xy).
Qed.

End RelAdjunction.

Notation rel_adjunction h e e' a := (rel_adjunction_mem h e e' (mem a)).
Notation "@ 'rel_adjunction' T T' h e e' a" :=
  (@rel_adjunction_mem T T' h e e' (mem a))
  (at level 10, T, T', h, e, e', a at level 8, only parsing) : type_scope.
Notation fun_adjunction h f f' a := (rel_adjunction h (frel f) (frel f') a).
Notation "@ 'fun_adjunction' T T' h f f' a" :=
  (@rel_adjunction T T' h (frel f) (frel f') a)
  (at level 10, T, T', h, f, f', a at level 8, only parsing) : type_scope.

Arguments intro_adjunction [T T' h e e'] _ _ [a].
Arguments adjunction_n_comp [T T'] h [e e'] _ _ [a].

Unset Implicit Arguments.

(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype fintype finfun finset ssralg.
Require Import bigop seq tuple choice ssrnat prime ssralg fingroup pgroup.
Require Import zmodp matrix vector falgebra galgebra.

(*****************************************************************************)
(*  * Module over an algebra                                                 *)
(*     amoduleType A    == type for finite dimension module structure.       *)
(*                                                                           *)
(*        v :* x        == right product of the module                       *)
(*      (M :* A)%VS     == the smallest vector space that contains           *)
(*                           {v :* x | v \in M & x \in A}                    *)
(*      (modv M A)      == M is a module for A                               *)
(*      (modf f M A)    == f is a module homomorphism on M for A             *)
(*****************************************************************************)
(*****************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Open Local Scope ring_scope.

Delimit Scope amodule_scope with aMS.

Import GRing.Theory.

Module AModuleType.
Section ClassDef.

Variable R : ringType.
Variable V: vectType R.
Variable A: FalgType R.

Structure mixin_of (V : vectType R) : Type := Mixin {
  action: A -> 'End(V);
  action_morph: forall x a b, action (a * b) x = action b (action a x);
  action_linear: forall x , linear (action^~ x);
  action1: forall x , action 1 x = x 
}.

Structure class_of (V : Type) : Type := Class {
  base : Vector.class_of R V;
   mixin : mixin_of (Vector.Pack _ base V) 
}.
Local Coercion base : class_of >-> Vector.class_of.

Implicit Type phA : phant A.

Structure type phA : Type := Pack {sort : Type; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.

Definition class phA (cT : type phA):=
  let: Pack _ c _ := cT return class_of cT in c.
Definition clone phA T cT c of phant_id (@class phA cT) c := @Pack phA T c T.

Definition pack phA V V0 (m0 : mixin_of (@Vector.Pack R _ V V0 V)) :=
  fun bT b & phant_id (@Vector.class _ (Phant R) bT) b =>
  fun    m & phant_id m0 m => Pack phA (@Class V b m) V.

Definition eqType phA cT := Equality.Pack (@class phA cT) cT.
Definition choiceType phA cT := choice.Choice.Pack (@class phA cT) cT.
Definition zmodType phA cT := GRing.Zmodule.Pack (@class phA cT) cT.
Definition lmodType phA cT := GRing.Lmodule.Pack (Phant R) (@class phA cT) cT.
Definition vectType phA cT := Vector.Pack (Phant R) (@class phA cT) cT.

End ClassDef.

Module Exports.
Coercion base : class_of >->  Vector.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.

Coercion eqType : type >->  Equality.type.
Canonical Structure eqType.
Coercion choiceType : type >-> Choice.type.
Canonical Structure choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical Structure zmodType.
Coercion lmodType : type>->  GRing.Lmodule.type.
Canonical Structure lmodType.
Coercion vectType : type >-> Vector.type.
Canonical Structure vectType.

Notation amoduleType A := (@type _ _ (Phant A)).
Notation AModuleType A m := (@pack _ _ (Phant A) _ _ m _ _ id _ id).
Notation AModuleMixin := Mixin.

Bind Scope ring_scope with sort.
End Exports.

End AModuleType.
Import AModuleType.Exports.

Section AModuleDef.
Variables (F : fieldType) (A: FalgType F) (M: amoduleType A).

Definition rmorph (a: A) := AModuleType.action (AModuleType.class M) a.
Definition rmul (a: M) (b: A) : M := rmorph b a.
Notation "a :* b" := (rmul a b): ring_scope.

Implicit Types x y: A.
Implicit Types v w: M.
Implicit Types c: F.

Lemma rmulD x: {morph (rmul^~ x): v1 v2 / v1 + v2}.
Proof. move=> *; exact: linearD. Qed.

Lemma rmul_linear_proof : forall  v, linear (rmul v).
Proof. by rewrite /rmul /rmorph; case: M => s [] b []. Qed.
Canonical Structure rmul_linear v := GRing.Linear (rmul_linear_proof v).

Lemma rmulA v x y: v :* (x * y) = (v :* x) :* y.
Proof. exact: AModuleType.action_morph. Qed.

Lemma rmulZ : forall c v x, (c *: v) :* x = c *: (v :* x).
Proof. move=> c v x; exact: linearZZ. Qed.

Lemma rmul0 : left_zero 0 rmul.
Proof. move=> x; exact: linear0. Qed.

Lemma rmul1 : forall v , v :* 1 = v.
Proof. by rewrite /rmul /rmorph; case: M => s [] b []. Qed.

Lemma rmul_sum :  forall I r P (f : I -> M) x,
  \sum_(i <- r | P i) f i :* x = (\sum_(i <- r | P i) f i) :* x.
Proof.
by move=> I r P f x; rewrite -linear_sum.
Qed.

Implicit Types vs: {vspace M}.
Implicit Types ws: {vspace A}.

Lemma size_eprodv : forall vs ws,
  size (allpairs rmul (vbasis vs) (vbasis ws)) == (\dim vs * \dim ws)%N.
Proof. by move=> *; rewrite size_allpairs !size_tuple. Qed.

Definition eprodv vs ws := span (Tuple (size_eprodv vs ws)).
Local Notation "A :* B" := (eprodv A B) : vspace_scope.

Lemma memv_eprod vs ws a b : a \in vs -> b \in ws -> a :* b \in (vs :* ws)%VS.
Proof. 
move=> Ha Hb.
rewrite (coord_vbasis Ha) (coord_vbasis Hb).
rewrite linear_sum /=; apply: memv_suml => j _.
rewrite -rmul_sum; apply: memv_suml => i _ /=.
rewrite linearZ memvZ //= rmulZ memvZ //=.
apply: memv_span; apply/allpairsP; exists ((vbasis vs)`_i, (vbasis ws)`_j)=> //.
by rewrite !mem_nth //= size_tuple.
Qed.

Lemma eprodvP : forall vs1 ws vs2, 
  reflect (forall a b, a \in vs1 -> b \in ws -> a :* b \in vs2)
          (vs1 :* ws <= vs2)%VS.
Proof.
move=> vs1 ws vs2; apply: (iffP idP).
  move=> Hs a b Ha Hb.
  by apply: subv_trans Hs; exact: memv_eprod.
move=> Ha; apply/subvP=> v.
move/coord_span->; apply: memv_suml=> i _ /=.
apply: memvZ.
set u := allpairs _ _ _.
have: i < size u by rewrite (eqP (size_eprodv _ _)).
move/(mem_nth 0); case/allpairsP=> [[x1 x2] [I1 I2 ->]].
by apply Ha; apply: vbasis_mem.
Qed.

Lemma eprod0v: left_zero 0%VS eprodv.
Proof.
move=> vs; apply subv_anti; rewrite sub0v andbT.
apply/eprodvP=> a b; case/vlineP=> k1 -> Hb.
by rewrite scaler0 rmul0 mem0v.
Qed.

Lemma eprodv0 : forall vs, (vs :* 0 = 0)%VS.
Proof.
move=> vs; apply subv_anti; rewrite sub0v andbT.
apply/eprodvP=> a b Ha; case/vlineP=> k1 ->.
by rewrite scaler0 linear0 mem0v.
Qed.

Lemma eprodv1 : forall vs, (vs :* 1 = vs)%VS.
Proof.
case: (vbasis1 A) => k Hk He /=.
move=> vs; apply subv_anti; apply/andP; split.
  apply/eprodvP=> a b Ha; case/vlineP=> k1 ->.
  by rewrite linearZ /= rmul1 memvZ.
apply/subvP=> v Hv.
rewrite (coord_vbasis Hv); apply: memv_suml=> [] [i Hi] _ /=.  
apply: memvZ.
rewrite -[_`_i]rmul1; apply: memv_eprod; last by apply: memv_line.
by apply: vbasis_mem; apply: mem_nth; rewrite size_tuple.
Qed.

Lemma eprodvSl ws vs1 vs2 : (vs1 <= vs2 -> vs1 :* ws <= vs2 :* ws)%VS.
Proof.
move=> Hvs; apply/eprodvP=> a b Ha Hb; apply: memv_eprod=> //.
by apply: subv_trans Hvs.
Qed.

Lemma eprodvSr vs ws1 ws2 : (ws1 <= ws2 -> vs :* ws1 <= vs :* ws2)%VS.
Proof.
move=> Hvs; apply/eprodvP=> a b Ha Hb; apply: memv_eprod=> //.
by apply: subv_trans Hvs.
Qed.

Lemma eprodv_addl: left_distributive eprodv addv.
Proof.
move=> vs1 vs2 ws; apply subv_anti; apply/andP; split.
  apply/eprodvP=> a b;case/memv_addP=> v1 Hv1 [v2 Hv2 ->] Hb.
  by rewrite rmulD; apply: memv_add; apply: memv_eprod.
apply/subvP=> v;  case/memv_addP=> v1 Hv1 [v2 Hv2 ->].
apply: memvD.
  move: v1 Hv1; apply/subvP; apply: eprodvSl; exact: addvSl.
move: v2 Hv2; apply/subvP; apply: eprodvSl; exact: addvSr.
Qed.

Lemma eprodv_sumr vs ws1 ws2 : (vs :* (ws1 + ws2) = vs :* ws1 + vs :* ws2)%VS.
Proof.
apply subv_anti; apply/andP; split.
  apply/eprodvP=> a b Ha;case/memv_addP=> v1 Hv1 [v2 Hv2 ->].
  by rewrite linearD; apply: memv_add; apply: memv_eprod.
apply/subvP=> v;  case/memv_addP=> v1 Hv1 [v2 Hv2 ->].
apply: memvD.
  move: v1 Hv1; apply/subvP; apply: eprodvSr; exact: addvSl.
move: v2 Hv2; apply/subvP; apply: eprodvSr; exact: addvSr.
Qed.

Definition modv (vs: {vspace M}) (al: {aspace A}) :=
   (vs :* al  <= vs)%VS.
 
Lemma mod0v : forall al, modv 0 al.
Proof. by move=> al; rewrite /modv eprod0v subvv. Qed.

Lemma modv1 : forall vs, modv vs (aspace1 A).
Proof. by move=> vs; rewrite /modv eprodv1 subvv. Qed.

Lemma modfv : forall al, modv fullv al.
Proof. by move=> al; exact: subvf. Qed.

Lemma memv_mod_mul : forall ms al m a, 
  modv ms al -> m \in ms -> a \in al -> m :* a \in ms.
Proof. 
move=> ms al m a Hmo Hm Ha; apply: subv_trans Hmo.
by apply: memv_eprod.
Qed.

Lemma modvD : forall ms1 ms2 al , 
  modv ms1 al -> modv ms2 al -> modv (ms1 + ms2) al.
Proof.
move=> ms1 ms2 al Hm1 Hm2; rewrite /modv eprodv_addl.
apply: (subv_trans (addvS Hm1 (subvv _))).
exact: (addvS (subvv _) Hm2).
Qed.

Lemma modv_cap : forall ms1 ms2 al , 
  modv ms1 al -> modv ms2 al -> modv (ms1:&: ms2) al.
Proof.
move=> ms1 ms2 al Hm1 Hm2.
by rewrite /modv subv_cap; apply/andP; split;
  [apply: subv_trans Hm1 | apply: subv_trans Hm2]; 
   apply: eprodvSl; rewrite (capvSr,capvSl).
Qed.

Definition irreducible ms al := 
  [/\ modv ms al, ms != 0%VS &
    forall ms1, modv ms1 al -> (ms1 <= ms)%VS -> ms != 0%VS -> ms1 = ms].

Definition completely_reducible ms al := 
  forall ms1, modv ms1 al -> (ms1 <= ms)%VS -> 
    exists ms2, 
    [/\ modv ms2 al, (ms1 :&: ms2 = 0)%VS & (ms1 + ms2)%VS = ms].

Lemma completely_reducible0 : forall al, completely_reducible 0 al.
Proof.
move=> al ms1 Hms1; rewrite subv0; move/eqP->.
by exists 0%VS; split; [exact: mod0v | exact: cap0v | exact: add0v].
Qed.

End AModuleDef.

Notation "a :* b" := (rmul a b): ring_scope.
Notation "A :* B" := (eprodv A B) : vspace_scope.

Section HomMorphism.

Variable (K: fieldType) (A: FalgType K) (M1 M2: amoduleType A).

Implicit Types ms : {vspace M1}.
Implicit Types f : 'Hom(M1, M2).
Implicit Types al : {aspace A}.

Definition modf f ms al :=
       all (fun p => f (p.1 :* p.2) == f p.1 :* p.2) 
               (allpairs (fun x y => (x,y)) (vbasis ms) (vbasis al)).

Lemma modfP : forall f ms al, 
  reflect (forall x v, v \in ms -> x \in al ->  f (v :* x) = f v :* x) 
          (modf f ms al).
Proof.
move=> f ms al; apply: (iffP idP)=> H; last first.
  apply/allP=> [] [v x]; case/allpairsP=> [[x1 x2] [I1 I2 ->]].
  by apply/eqP; apply: H; apply: vbasis_mem.
move=> x v Hv Hx; rewrite (coord_vbasis Hv) (coord_vbasis Hx).
rewrite !linear_sum; apply: eq_big=> //= i _.
rewrite !linearZ /=; congr (_ *: _).
rewrite -!rmul_sum linear_sum; apply: eq_big=> //= j _.
rewrite rmulZ !linearZ /= rmulZ; congr (_ *: _).
set x1 := _`_ _; set y1 := _ `_ _.
case: f H => f /=; move/allP; move/(_ (x1,y1))=> HH.
apply/eqP; apply: HH; apply/allpairsP; exists (x1, y1).
by rewrite !mem_nth //= size_tuple.
Qed.

Lemma modf_zero : forall ms al, modf 0 ms al.
Proof. by move=> ms al; apply/allP=> i _; rewrite !lfunE rmul0. Qed.

Lemma modf_add : forall f1 f2 ms al, 
  modf f1 ms al -> modf f2 ms al -> modf (f1 + f2) ms al.
Proof.
move=> f1 f2 ms al Hm1 Hm2; apply/allP=> [] [v x].
case/allpairsP=> [[x1 x2] [I1 I2 ->]]; rewrite !lfunE rmulD /=.
move/modfP: Hm1->; try apply: vbasis_mem=>//.
by move/modfP: Hm2->; try apply: vbasis_mem.
Qed.

Lemma modf_scale : forall k f ms al, modf f ms al -> modf (k *: f) ms al.
Proof.
move=> k f ms al Hm; apply/allP=>  [] [v x].
case/allpairsP=> [[x1 x2] [I1 I2 ->]]; rewrite !lfunE rmulZ /=.
by move/modfP: Hm->; try apply: vbasis_mem.
Qed.

Lemma modv_ker : forall f ms al, 
  modv ms al -> modf f ms al -> modv (ms :&: lker f) al.
Proof.
move=> f ms al Hmd Hmf; apply/eprodvP=> x v.
rewrite memv_cap !memv_ker.
case/andP=> Hx Hf Hv.
rewrite memv_cap (memv_mod_mul Hmd) // memv_ker.
by move/modfP: Hmf=> ->; rewrite // (eqP Hf) rmul0 eqxx.
Qed.

Lemma modv_img : forall f ms al, 
  modv ms al -> modf f ms al -> modv (f @: ms) al.
Proof.
move=> f ms al Hmv Hmf; apply/eprodvP=> v x.
case/memv_imgP=> u Hu -> Hx.
move/modfP: Hmf<-=> //.
apply: memv_img.
by apply: (memv_mod_mul Hmv).
Qed.

End HomMorphism.

Section ModuleRepresentation.

Variable (F: fieldType) (gT: finGroupType) 
         (G: {group gT}) (M: amoduleType (galg F gT)).
Hypothesis CG: ([char F]^'.-group G)%g.
Implicit Types ms : {vspace M}.

Let FG := gaspace F G.
Local Notation " g %:FG " := (injG _ g).

Lemma Maschke : forall ms, modv ms FG -> completely_reducible ms FG.
Proof.
move=> ms Hmv ms1 Hms1 Hsub; rewrite /completely_reducible.
pose act g : 'End(M) := rmorph M (g%:FG).
have actE: forall g v, act g v  = v :* g%:FG by done.
pose f: 'End(M) :=  #|G|%:R^-1 *: 
        \sum_(i in G) (act (i^-1)%g \o projv ms1 \o act i)%VF.
have Cf: forall v x, x \in FG -> f (v :* x) = f v :* x.
  move=> v x; case/memv_sumP=> g_ Hg_ ->.
  rewrite !linear_sum; apply: eq_big => //= i Hi.
  move: (Hg_ _ Hi); case/vlineP=> k ->.
  rewrite !linearZ /=; congr (_ *: _).
  rewrite /f /= !lfunE /= !sum_lfunE rmulZ /=; congr (_ *: _).
  rewrite -rmul_sum (reindex (fun g => (i^-1 * g)%g)); last first.
    by exists (fun g => (i * g)%g)=> h; rewrite mulgA (mulVg, mulgV) mul1g.
  apply: eq_big=> g; first by rewrite groupMl // groupV.
  rewrite !lfunE /= !lfunE /= !actE -rmulA=> Hig.
  have Hg: g \in G by rewrite -[g]mul1g -[1%g](mulgV i) -mulgA groupM.
  by rewrite -injGM // mulgA mulgV mul1g invMg invgK !injGM
             ?groupV // rmulA.
have Himf: forall v, v \in ms1 -> f v = v.
  move=> v Hv.
  rewrite /f !lfunE /= sum_lfunE (eq_bigr (fun x => v)); last move=> i Hi.
    by rewrite sumr_const -scaler_nat scalerA mulVf // ?scale1r // -?charf'_nat.
  rewrite !lfunE /= !lfunE /= projv_id !actE; last first.
    by rewrite (memv_mod_mul Hms1) //= /gvspace (bigD1 i) // memvE addvSl.
  by rewrite -rmulA -injGM // ?groupV // mulgV rmul1.
have If: limg f = ms1.
  apply: subv_anti; apply/andP; split; last first.
    by apply/subvP=> v Hv; rewrite -(Himf _ Hv) memv_img // memvf.
  apply/subvP=> i; case/memv_imgP=> x _ ->.
  rewrite !lfunE memvZ //= sum_lfunE memv_suml=> // j Hj.
  rewrite lfunE /= lfunE (memv_mod_mul Hms1) //; first by exact: memv_proj.
  by rewrite memvE /= /gvspace (bigD1 (j^-1)%g) ?addvSl // groupV.
exists (ms :&: lker f)%VS; split.
  - apply: modv_ker=> //; apply/modfP=> *; exact: Cf.
  apply/eqP; rewrite -subv0; apply/subvP=> v; rewrite memv0.
  rewrite !memv_cap; case/andP=> Hv1; case/andP=> Hv2 Hv3.
  by move: Hv3; rewrite memv_ker  Himf.
apply: subv_anti; rewrite  subv_add Hsub capvSl.
apply/subvP=> v Hv.
have->: v = f v + (v - f v) by rewrite addrC -addrA addNr addr0.
apply: memv_add; first by rewrite -If memv_img // memvf.
rewrite memv_cap; apply/andP; split.
  apply: memvB=> //; apply: subv_trans Hsub.
  by rewrite -If; apply: memv_img; exact: memvf.
rewrite memv_ker linearB /= (Himf (f v)) ?subrr // /in_mem /= -If.
by apply: memv_img; exact: memvf. 
Qed.

End ModuleRepresentation.

Export AModuleType.Exports.

(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype tuple.

(******************************************************************************)
(* This file implements a type for functions with a finite domain:            *)
(*      {ffun aT -> rT} where aT should have a finType structure,             *)
(*      {ffun forall x : aT, rT} for dependent functions over a finType aT,   *)
(*  and {ffun funT} where funT expands to a product over a finType.           *)
(* Any eqType, choiceType, countType and finType structures on rT extend to   *)
(* {ffun aT -> rT} as Leibnitz equality and extensional equalities coincide.  *)
(*     (T ^ n)%type is notation for {ffun 'I_n -> T}, which is isomorphic     *)
(*   to n.-tuple T, but is structurally positive and thus can be used to      *)
(*   define inductive types, e.g., Inductive tree := node n of tree ^ n (see  *)
(*   mid-file for an expanded example).                                       *)
(* --> More generally, {ffun fT} is always structurally positive.             *)
(*   {ffun fT} inherits combinatorial structures of rT, i.e., eqType,         *)
(* choiceType, countType, and finType. However, due to some limitations of    *)
(* the Coq 8.9 unification code the structures are only inherited in the      *)
(* NON dependent case, when rT does not depend on x.                          *)
(*  For f : {ffun fT} with fT := forall x : aT, rT we define                  *)
(*              f x == the image of x under f (f coerces to a CiC function)   *)
(* --> The coercion is structurally decreasing, e.g., Coq will accept         *)
(*   Fixpoint size t := let: node n f := t in sumn (codom (size \o f)) + 1.   *)
(* as structurally decreasing on t of the inductive tree type above.          *)
(*       {dffun fT} == alias for {ffun fT} that inherits combinatorial        *)
(*                     structures on rT, when rT DOES depend on x.            *)
(*      total_fun g == the function induced by a dependent function g of type *)
(*                     forall x, rT on the total space {x : aT & rT}.         *)
(*                  := fun x =>  Tagged (fun x => rT) (g x).                  *)
(*        tfgraph f == the total function graph of f, i.e., the #|aT|.-tuple  *)
(*                     of all the (dependent pair) values of total_fun f.     *)
(*         finfun g == the f extensionally equal to g, and the RECOMMENDED    *)
(*                     interface for building elements of {ffun fT}.          *)
(* [ffun x : aT => E] := finfun (fun x : aT => E).                            *)
(*                     There should be an explicit type constraint on E if    *)
(*                     type does not depend on x, due to the Coq unification  *)
(*                     limitations referred to above.                         *)
(*        ffun0 aT0 == the trivial finfun, from a proof aT0 that #|aT| = 0.   *)
(*   f \in family F == f belongs to the family F (f x \in F x for all x)      *)
(*   There are addidional operations for non-dependent finite functions,      *)
(* i.e., f in {ffun aT -> rT}.                                                *)
(*    [ffun x => E] := finfun (fun x => E).                                   *)
(*                     The type of E must not depend on x; this restriction   *)
(*                     is a mitigation of the aforementioned Coq unification  *)
(*                     limitations.                                           *)
(*       [ffun=> E] := [ffun _ => E] (E should not have a dependent type).    *)
(*         fgraph f == the function graph of f, i.e., the #|aT|.-tuple        *)
(*                     listing the values of f x, for x ranging over enum aT. *)
(*         Finfun G == the finfun f whose (simple) function graph is G.       *)
(*  f \in ffun_on R == the range of f is a subset of R.                       *)
(*     y.-support f == the y-support of f, i.e., [pred x | f x != y].         *)
(*                     Thus, y.-support f \subset D means f has y-support D.  *)
(*                     We will put Notation support := 0.-support in ssralg.  *)
(* f \in pffun_on y D R == f is a y-partial function from D to R:             *)
(*                     f has y-support D and f x \in R for all x \in D.       *)
(*  f \in pfamily y D F == f belongs to the y-partial family from D to F:     *)
(*                     f has y-support D and f x \in F x for all x \in D.     *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Def.

Variables (aT : finType) (rT : aT -> Type).

Inductive finfun_on : seq aT -> Type :=
| finfun_nil                            : finfun_on [::]
| finfun_cons x s of rT x & finfun_on s : finfun_on (x :: s).

Local Fixpoint finfun_rec (g : forall x, rT x) s : finfun_on s :=
  if s is x1 :: s1 then finfun_cons (g x1) (finfun_rec g s1) else finfun_nil.

Local Fixpoint fun_of_fin_rec x s (f_s : finfun_on s) : x \in s -> rT x :=
  if f_s is finfun_cons x1 s1 y1 f_s1 then
    if eqP is ReflectT Dx in reflect _ Dxb return Dxb || (x \in s1) -> rT x then
      fun=> ecast x (rT x) (esym Dx) y1
    else fun_of_fin_rec f_s1
  else fun isF =>  False_rect (rT x) (notF isF).

Variant finfun_of (ph : phant (forall x, rT x)) : predArgType :=
  FinfunOf of finfun_on (enum aT).

Definition dfinfun_of ph := finfun_of ph.

Definition fun_of_fin ph (f : finfun_of ph) x :=
  let: FinfunOf f_aT := f in fun_of_fin_rec f_aT (mem_enum aT x).

End Def.

Coercion fun_of_fin : finfun_of >-> Funclass.
Identity Coercion unfold_dfinfun_of : dfinfun_of >-> finfun_of.
Arguments fun_of_fin {aT rT ph} f x.

Notation "{ 'ffun' fT }" := (finfun_of (Phant fT))
  (at level 0, format "{ 'ffun'  '[hv' fT ']' }") : type_scope.

Notation "{ 'dffun' fT }" := (dfinfun_of (Phant fT))
  (at level 0, format "{ 'dffun'  '[hv' fT ']' }") : type_scope.

Definition exp_finIndexType := ordinal_finType.
Notation "T ^ n" :=
  (@finfun_of (exp_finIndexType n) (fun=> T) (Phant _)) : type_scope.

Local Notation finPi aT rT := (forall x : Finite.sort aT, rT x) (only parsing).
Local Notation finfun_def :=
  (fun aT rT g => FinfunOf (Phant (finPi aT rT)) (finfun_rec g (enum aT))).

Module Type FinfunDefSig.
Parameter finfun : forall aT rT, finPi aT rT -> {ffun finPi aT rT}.
Axiom finfunE : finfun = finfun_def.
End FinfunDefSig.

Module FinfunDef : FinfunDefSig.
Definition finfun := finfun_def.
Lemma finfunE : finfun = finfun_def. Proof. by []. Qed.
End FinfunDef.

Notation finfun := FinfunDef.finfun.
Canonical finfun_unlock := Unlockable FinfunDef.finfunE.
Arguments finfun {aT rT} g.

Notation "[ 'ffun' x : aT => E ]" := (finfun (fun x : aT => E))
  (at level 0, x ident) : fun_scope.

Notation "[ 'ffun' x => E ]" := (@finfun _ (fun=> _) (fun x => E))
  (at level 0, x ident, format "[ 'ffun'  x  =>  E ]") : fun_scope.

Notation "[ 'ffun' => E ]" := [ffun _ => E]
  (at level 0, format "[ 'ffun' =>  E ]") : fun_scope.

(* Example outcommented.
(* Examples of using finite functions as containers in recursive inductive    *)
(* types, and making use of the fact that the type and accessor are           *)
(* structurally positive and decreasing, respectively.                        *)
Unset Elimination Schemes.
Inductive tree := node n of tree ^ n.
Fixpoint size t := let: node n f := t in sumn (codom (size \o f)) + 1.
Example tree_step (K : tree -> Type) :=
  forall n st (t := node st) & forall i : 'I_n, K (st i), K t.
Example tree_rect K (Kstep : tree_step K) : forall t, K t.
Proof. by fix IHt 1 => -[n st]; apply/Kstep=> i; apply: IHt. Defined.

(* An artificial example use of dependent functions.                          *)
Inductive tri_tree n := tri_row of {ffun forall i : 'I_n, tri_tree i}.
Fixpoint tri_size n (t : tri_tree n) :=
  let: tri_row f := t in sumn [seq tri_size (f i) | i : 'I_n] + 1.
Example tri_tree_step (K : forall n, tri_tree n -> Type) :=
  forall n st (t := tri_row st) & forall i : 'I_n, K i (st i), K n t.
Example tri_tree_rect K (Kstep : tri_tree_step K) : forall n t, K n t.
Proof. by fix IHt 2 => n [st]; apply/Kstep=> i; apply: IHt. Defined.
Set Elimination Schemes.
(* End example. *) *)

(* The correspondance between finfun_of and CiC dependent functions.          *)
Section DepPlainTheory.
Variables (aT : finType) (rT : aT -> Type).
Notation fT := {ffun finPi aT rT}.
Implicit Type f : fT.

Fact ffun0 (aT0 : #|aT| = 0) : fT.
Proof. by apply/finfun=> x; have:= card0_eq aT0 x. Qed.

Lemma ffunE g x : (finfun g : fT) x = g x.
Proof.
rewrite unlock /=; set s := enum aT; set s_x : mem_seq s x := mem_enum _ _.
by elim: s s_x => //= x1 s IHs; case: eqP => [|_]; [case: x1 / | apply: IHs].
Qed.

Lemma ffunP (f1 f2 : fT) : (forall x, f1 x = f2 x) <-> f1 = f2.
Proof.
suffices ffunK f g: (forall x, f x = g x) -> f = finfun g.
  by split=> [/ffunK|] -> //; apply/esym/ffunK.
case: f => f Dg; rewrite unlock; congr FinfunOf.
have{Dg} Dg x (aTx : mem_seq (enum aT) x): g x = fun_of_fin_rec f aTx.
  by rewrite -Dg /= (bool_irrelevance (mem_enum _ _) aTx).
elim: (enum aT) / f (enum_uniq aT) => //= x1 s y f IHf /andP[s'x1 Us] in Dg *.
rewrite Dg ?eqxx //=; case: eqP => // /eq_axiomK-> /= _.
rewrite {}IHf // => x s_x; rewrite Dg ?s_x ?orbT //.
by case: eqP (memPn s'x1 x s_x) => // _ _ /(bool_irrelevance s_x) <-.
Qed.

Lemma ffunK : @cancel (finPi aT rT) fT fun_of_fin finfun.
Proof. by move=> f; apply/ffunP=> x; rewrite ffunE. Qed.

Lemma eq_dffun (g1 g2 : forall x, rT x) :
   (forall x, g1 x = g2 x) -> finfun g1 = finfun g2.
Proof. by move=> eq_g; apply/ffunP => x; rewrite !ffunE eq_g. Qed.

Definition total_fun g x := Tagged rT (g x : rT x).

Definition tfgraph f := codom_tuple (total_fun f).

Lemma codom_tffun f : codom (total_fun f) = tfgraph f. Proof. by []. Qed.

Local Definition tfgraph_inv (G : #|aT|.-tuple {x : aT & rT x}) : option fT :=
  if eqfunP isn't ReflectT Dtg then None else
  Some [ffun x => ecast x (rT x) (Dtg x) (tagged (tnth G (enum_rank x)))].

Local Lemma tfgraphK : pcancel tfgraph tfgraph_inv.
Proof.
move=> f; have Dg x: tnth (tfgraph f) (enum_rank x) = total_fun f x.
  by rewrite tnth_map -[tnth _ _]enum_val_nth enum_rankK.
rewrite /tfgraph_inv; case: eqfunP => /= [Dtg | [] x]; last by rewrite Dg.
congr (Some _); apply/ffunP=> x; rewrite ffunE.
by rewrite Dg in (Dx := Dtg x) *; rewrite eq_axiomK.
Qed.

Lemma tfgraph_inj : injective tfgraph. Proof. exact: pcan_inj tfgraphK. Qed.

Definition family_mem mF := [pred f : fT | [forall x, in_mem (f x) (mF x)]].

Variables (pT : forall x, predType (rT x)) (F : forall x, pT x).

(* Helper for defining notation for function families. *)
Local Definition fmem F x := mem (F x : pT x).

Lemma familyP f : reflect (forall x, f x \in F x) (f \in family_mem (fmem F)).
Proof. exact: forallP. Qed.

End DepPlainTheory.

Arguments ffunK {aT rT} f : rename.
Arguments ffun0 {aT rT} aT0.
Arguments eq_dffun {aT rT} [g1] g2 eq_g12.
Arguments total_fun {aT rT} g x.
Arguments tfgraph {aT rT} f.
Arguments tfgraphK {aT rT} f : rename.
Arguments tfgraph_inj {aT rT} [f1 f2] : rename.

Arguments fmem {aT rT pT} F x /.
Arguments familyP {aT rT pT F f}.
Notation family F := (family_mem (fmem F)).

Section InheritedStructures.

Variable aT : finType.
Notation dffun_aT rT rS := {dffun forall x : aT, rT x : rS}.

Local Remark eqMixin rT : Equality.mixin_of (dffun_aT rT eqType).
Proof. exact: PcanEqMixin tfgraphK. Qed.
Canonical finfun_eqType (rT : eqType) :=
  EqType {ffun aT -> rT} (eqMixin (fun=> rT)).
Canonical dfinfun_eqType rT :=
  EqType (dffun_aT rT eqType) (eqMixin rT).

Local Remark choiceMixin rT : Choice.mixin_of (dffun_aT rT choiceType).
Proof. exact: PcanChoiceMixin tfgraphK. Qed.
Canonical finfun_choiceType (rT : choiceType) :=
  ChoiceType {ffun aT -> rT} (choiceMixin (fun=> rT)).
Canonical dfinfun_choiceType rT :=
  ChoiceType (dffun_aT rT choiceType) (choiceMixin rT).

Local Remark countMixin rT : Countable.mixin_of (dffun_aT rT countType).
Proof. exact: PcanCountMixin tfgraphK. Qed.
Canonical finfun_countType (rT : countType) :=
  CountType {ffun aT -> rT} (countMixin (fun => rT)).
Canonical dfinfun_countType rT :=
  CountType (dffun_aT rT countType) (countMixin rT).

Local Definition finMixin rT :=
  PcanFinMixin (tfgraphK : @pcancel _ (dffun_aT rT finType) _ _).
Canonical finfun_finType (rT : finType) :=
  FinType {ffun aT -> rT} (finMixin (fun=> rT)).
Canonical dfinfun_finType rT :=
  FinType (dffun_aT rT finType) (finMixin rT).

End InheritedStructures.

Section FinFunTuple.

Context {T : Type} {n : nat}.

Definition tuple_of_finfun (f : T ^ n) : n.-tuple T := [tuple f i | i < n].

Definition finfun_of_tuple (t : n.-tuple T) : (T ^ n) := [ffun i => tnth t i].

Lemma finfun_of_tupleK : cancel finfun_of_tuple tuple_of_finfun.
Proof.
by move=> t; apply: eq_from_tnth => i; rewrite tnth_map ffunE tnth_ord_tuple.
Qed.

Lemma tuple_of_finfunK : cancel tuple_of_finfun finfun_of_tuple.
Proof.
by move=> f; apply/ffunP => i; rewrite ffunE tnth_map tnth_ord_tuple.
Qed.

End FinFunTuple.

Section FunPlainTheory.

Variables (aT : finType) (rT : Type).
Notation fT := {ffun aT -> rT}.
Implicit Types (f : fT) (R : pred rT).

Definition fgraph f := codom_tuple f.

Definition Finfun (G : #|aT|.-tuple rT) := [ffun x => tnth G (enum_rank x)].

Lemma tnth_fgraph f i : tnth (fgraph f) i = f (enum_val i).
Proof. by rewrite tnth_map /tnth -enum_val_nth. Qed.

Lemma FinfunK : cancel Finfun fgraph.
Proof.
by move=> G; apply/eq_from_tnth=> i; rewrite tnth_fgraph ffunE enum_valK.
Qed.

Lemma fgraphK : cancel fgraph Finfun.
Proof. by move=> f; apply/ffunP=> x; rewrite ffunE tnth_fgraph enum_rankK. Qed.

Lemma fgraph_ffun0 aT0 : fgraph (ffun0 aT0) = nil :> seq rT.
Proof. by apply/nilP/eqP; rewrite size_tuple. Qed.

Lemma codom_ffun f : codom f = fgraph f. Proof. by []. Qed.

Lemma tagged_tfgraph f : @map _ rT tagged (tfgraph f) = fgraph f.
Proof. by rewrite -map_comp. Qed.

Lemma eq_ffun (g1 g2 : aT -> rT) : g1 =1 g2 -> finfun g1 = finfun g2.
Proof. exact: eq_dffun. Qed.

Lemma fgraph_codom f : fgraph f = codom_tuple f.
Proof. exact/esym/val_inj/codom_ffun. Qed.

Definition ffun_on_mem (mR : mem_pred rT) := family_mem (fun _ : aT => mR).

Lemma ffun_onP R f : reflect (forall x, f x \in R) (f \in ffun_on_mem (mem R)).
Proof. exact: forallP. Qed.

End FunPlainTheory.

Arguments Finfun {aT rT} G.
Arguments fgraph {aT rT} f.
Arguments FinfunK {aT rT} G : rename.
Arguments fgraphK {aT rT} f : rename.
Arguments eq_ffun {aT rT} [g1] g2 eq_g12.
Arguments ffun_onP {aT rT R f}.

Notation ffun_on R := (ffun_on_mem _ (mem R)).
Notation "@ 'ffun_on' aT R" :=
  (ffun_on R : simpl_pred (finfun_of (Phant (aT -> id _))))
  (at level 10, aT, R at level 9).

Lemma nth_fgraph_ord T n (x0 : T) (i : 'I_n) f : nth x0 (fgraph f) i = f i.
Proof.
by rewrite -[i in RHS]enum_rankK -tnth_fgraph  (tnth_nth x0) enum_rank_ord.
Qed.

(*****************************************************************************)

Section Support.

Variables (aT : Type) (rT : eqType).

Definition support_for y (f : aT -> rT) := [pred x | f x != y].

Lemma supportE x y f : (x \in support_for y f) = (f x != y). Proof. by []. Qed.

End Support.

Notation "y .-support" := (support_for y)
  (at level 2, format "y .-support") : fun_scope.

Section EqTheory.

Variables (aT : finType) (rT : eqType).
Notation fT := {ffun aT -> rT}.
Implicit Types (y : rT) (D : {pred aT}) (R : {pred rT}) (f : fT).

Lemma supportP y D g :
  reflect (forall x, x \notin D -> g x = y) (y.-support g \subset D).
Proof.
by apply: (iffP subsetP) => Dg x; [apply: contraNeq | apply: contraR] => /Dg->.
Qed.

Definition pfamily_mem y mD (mF : aT -> mem_pred rT) :=
  family (fun i : aT => if in_mem i mD then pred_of_simpl (mF i) else pred1 y).

Lemma pfamilyP (pT : predType rT) y D (F : aT -> pT) f :
  reflect (y.-support f \subset D /\ {in D, forall x, f x \in F x})
          (f \in pfamily_mem y (mem D) (fmem F)).
Proof.
apply: (iffP familyP) => [/= f_pfam | [/supportP f_supp f_fam] x].
  split=> [|x Ax]; last by have:= f_pfam x; rewrite Ax.
  by apply/subsetP=> x; case: ifP (f_pfam x) => //= _ fx0 /negP[].
by case: ifPn => Ax /=; rewrite inE /= (f_fam, f_supp).
Qed.

Definition pffun_on_mem y mD mR := pfamily_mem y mD (fun _ => mR).

Lemma pffun_onP y D R f :
  reflect (y.-support f \subset D /\ {subset image f D <= R})
          (f \in pffun_on_mem y (mem D) (mem R)).
Proof.
apply: (iffP (pfamilyP y D (fun _ => R) f)) => [] [-> f_fam]; split=> //.
  by move=> _ /imageP[x Ax ->]; apply: f_fam.
by move=> x Ax; apply: f_fam; apply/imageP; exists x.
Qed.

End EqTheory.

Arguments supportP {aT rT y D g}.
Arguments pfamilyP {aT rT pT y D F f}.
Arguments pffun_onP {aT rT y D R f}.

Notation pfamily y D F := (pfamily_mem y (mem D) (fmem F)).
Notation pffun_on y D R := (pffun_on_mem y (mem D) (mem R)).

(*****************************************************************************)

Section FinDepTheory.

Variables (aT : finType) (rT : aT -> finType).
Notation fT := {dffun forall x : aT, rT x}.

Lemma card_family (F : forall x, pred (rT x)) :
  #|(family F : simpl_pred fT)| = foldr muln 1 [seq #|F x| | x : aT].
Proof.
rewrite /image_mem; set E := enum aT in (uniqE := enum_uniq aT) *.
have trivF x: x \notin E -> #|F x| = 1 by rewrite mem_enum.
elim: E uniqE => /= [_ | x0 E IH_E /andP[E'x0 uniqE]] in F trivF *.
  have /fin_all_exists[f0 Ff0] x: exists y0, F x =i pred1 y0.
    have /pred0Pn[y Fy]: #|F x| != 0 by rewrite trivF.
    by exists y; apply/fsym/subset_cardP; rewrite ?subset_pred1 // card1 trivF.
  apply: eq_card1 (finfun f0 : fT) _ _ => f; apply/familyP/eqP=> [Ff | {f}-> x].
    by apply/ffunP=> x; have:= Ff x; rewrite Ff0 ffunE => /eqP.
  by rewrite ffunE Ff0 inE /=.
have [y0 Fxy0 | Fx00] := pickP (F x0); last first.
  by rewrite !eq_card0 // => f; apply: contraFF (Fx00 (f x0))=> /familyP; apply.
pose F1 x := if eqP is ReflectT Dx then xpred1 (ecast x (rT x) Dx y0) else F x.
transitivity (#|[predX F x0 & family F1 : pred fT]|); last first.
  rewrite cardX {}IH_E {uniqE}// => [|x E'x]; last first.
    rewrite /F1; case: eqP => [Dx | /nesym/eqP-x0'x]; first exact: card1.
    by rewrite trivF // negb_or x0'x.
  congr (_ * foldr _ _ _); apply/eq_in_map=> x Ex.
  by rewrite /F1; case: eqP => // Dx0; rewrite Dx0 Ex in E'x0.
pose g yf : fT := let: (y, f) := yf : rT x0 * fT in
  [ffun x => if eqP is ReflectT Dx then ecast x (rT x) Dx y else f x].
have gK: cancel (fun f : fT => (f x0, g (y0, f))) g.
  by move=> f; apply/ffunP=> x; rewrite !ffunE; case: eqP => //; case: x /.
rewrite -(card_image (can_inj gK)); apply: eq_card => [] [y f] /=.
apply/imageP/andP=> [[f1 /familyP/=Ff1] [-> ->]| [/=Fx0y /familyP/=Ff]].
  split=> //; apply/familyP=> x; rewrite ffunE /F1 /=.
  by case: eqP => // Dx; apply: eqxx.
exists (g (y, f)).
  by apply/familyP=> x; have:= Ff x; rewrite ffunE /F1; case: eqP; [case: x /|].
congr (_, _); first by rewrite /= ffunE; case: eqP => // Dx; rewrite eq_axiomK.
by apply/ffunP=> x; have:= Ff x; rewrite !ffunE /F1; case: eqP => // Dx /eqP.
Qed.

Lemma card_dep_ffun : #|fT| = foldr muln 1 [seq #|rT x| | x : aT].
Proof. by rewrite -card_family; apply/esym/eq_card=> f; apply/familyP. Qed.

End FinDepTheory.

Section FinFunTheory.

Variables aT rT : finType.
Notation fT := {ffun aT -> rT}.
Implicit Types (D : {pred aT}) (R : {pred rT}) (F : aT -> pred rT).

Lemma card_pfamily y0 D F :
  #|pfamily y0 D F| = foldr muln 1 [seq #|F x| | x in D].
Proof.
rewrite card_family !/(image _ _) /(enum D) -enumT /=.
by elim: (enum aT) => //= x E ->; have [// | D'x] := ifP; rewrite card1 mul1n.
Qed.

Lemma card_pffun_on y0 D R : #|pffun_on y0 D R| = #|R| ^ #|D|.
Proof.
rewrite (cardE D) card_pfamily /image_mem.
by elim: (enum D) => //= _ e ->; rewrite expnS.
Qed.

Lemma card_ffun_on R : #|@ffun_on aT R| = #|R| ^ #|aT|.
Proof.
rewrite card_family /image_mem cardT.
by elim: (enum aT) => //= _ e ->; rewrite expnS.
Qed.

Lemma card_ffun : #|fT| = #|rT| ^ #|aT|.
Proof. by rewrite -card_ffun_on; apply/esym/eq_card=> f; apply/forallP. Qed.

End FinFunTheory.

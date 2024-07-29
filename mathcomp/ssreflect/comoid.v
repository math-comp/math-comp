From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype choice ssrnat seq.
From mathcomp Require Import fintype finfun monoid.

Open Scope group_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "+%g" (at level 0).
Reserved Notation "-%g" (at level 0).
Reserved Notation "\0" (at level 0).
Reserved Notation "f \+ g" (at level 50, left associativity).
Reserved Notation "f \- g" (at level 50, left associativity).
Reserved Notation "\- f" (at level 35, f at level 35).

Reserved Notation "'{' 'additive' U '->' V '}'"
  (at level 0, U at level 98, V at level 99,
   format "{ 'additive'  U  ->  V }").

HB.mixin Record isAddMagma V := {
  add : V -> V -> V
}.

#[short(type="addMagmaType")]
HB.structure Definition AddMagma := {V of isAddMagma V & Choice V}.

Local Notation "+%g" := (@add _) : function_scope.
Local Notation "x + y" := (add x y) : group_scope.

HB.mixin Record AddMagma_isBaseAddUMagma V of AddMagma V := {
  zero : V
}.

HB.structure Definition BaseAddUMagma := {V of AddMagma_isBaseAddUMagma V & AddMagma V}.

HB.mixin Record BaseAddUMagma_isAddUMagma V of BaseAddUMagma V := {
  addgC : commutative (@add V);
  add0g : left_id zero (@add V)
}.

HB.factory Record isAddUMagma V of Choice V := {
  add : V -> V -> V;
  zero : V;
  addgC : commutative add;
  add0g : left_id zero add
}.

HB.builders Context V of isAddUMagma V.
HB.instance Definition _ := isAddMagma.Build V add.
HB.instance Definition _ := AddMagma_isBaseAddUMagma.Build V zero.
HB.instance Definition _ := BaseAddUMagma_isAddUMagma.Build V addgC add0g.
HB.end.

#[short(type="addUMagmaType")]
HB.structure Definition AddUMagma := {V of isAddUMagma V & Choice V}.

Local Notation "0" := (@zero _) : group_scope.

Definition natmul (V : addUMagmaType) (x : V) n := @iterop _ n (add : V -> V -> V) x (@zero V).
Arguments natmul : simpl never.

Local Notation "x *+ n" := (natmul x n) : group_scope.

Lemma addg0 (V : addUMagmaType) : right_id (@zero V) add.
Proof. by move=> x; rewrite addgC add0g. Qed.

Definition multiplicative := @id Type.

HB.instance Definition _ (V : addUMagmaType) := Choice.on (multiplicative V).
HB.instance Definition _ (V : addUMagmaType) := isMagma.Build (multiplicative V) (@add V).
HB.instance Definition _ (V : addUMagmaType) := Magma_isUMagma.Build (multiplicative V) add0g (@addg0 V).

HB.mixin Record AddUMagma_isNmodule V of AddUMagma V := {
  addgA : associative (@add V);
}.

HB.factory Record isNmodule V of Choice V := {
  zero : V;
  add : V -> V -> V;
  addgA : associative add;
  addgC : commutative add;
  add0g : left_id zero add
}.

HB.builders Context V of isNmodule V.

HB.instance Definition _ := isAddUMagma.Build V addgC add0g.
HB.instance Definition _ := AddUMagma_isNmodule.Build V addgA.

HB.end.

#[short(type="nmodType")]
HB.structure Definition Nmodule := {V of isNmodule V & Choice V}.

Module NmodExports.
Bind Scope group_scope with Nmodule.sort.
#[deprecated(since="mathcomp 2.0.0",
  note="Use GRing.Nmodule.clone instead.")]
Notation "[ 'nmodType' 'of' T 'for' cT ]" := (Nmodule.clone T cT)
  (at level 0, format "[ 'nmodType'  'of'  T  'for'  cT ]") : form_scope.
#[deprecated(since="mathcomp 2.0.0",
  note="Use GRing.Nmodule.clone instead.")]
Notation "[ 'nmodType' 'of' T ]" :=  (Nmodule.clone T _)
  (at level 0, format "[ 'nmodType'  'of'  T ]") : form_scope.
End NmodExports.
HB.export NmodExports.

HB.instance Definition _ (V : nmodType) := UMagma_isMonoid.Build (multiplicative V) addgA.

Section NmoduleTheory.

Variable V : nmodType.
Implicit Types x y : V.

(* addgA, addgC and add0g in the structure *)
(* addg0 proved above *)

Lemma addgCA : @left_commutative V V +%g.
Proof. by move=> x y z; rewrite !addgA [x + _]addgC. Qed.

Lemma addgAC : @right_commutative V V +%g.
Proof. by move=> x y z; rewrite -!addgA [y + _]addgC. Qed.

Lemma addgACA : @interchange V +%g +%g.
Proof. by move=> x y z t; rewrite -!addgA [y + (z + t)]addgCA. Qed.

Lemma mulg0n x : x *+ 0 = 0. Proof. by []. Qed.
Lemma mulg1n x : x *+ 1 = x. Proof. by []. Qed.
Lemma mulg2n x : x *+ 2 = x + x. Proof. by []. Qed.

Lemma mulgS x n : x *+ n.+1 = x + (x *+ n).
Proof. exact: (@expgS (multiplicative V)). Qed.

Lemma mulgSr x n : x *+ n.+1 = x *+ n + x.
Proof. by rewrite addgC mulgS. Qed.

Lemma mulgb x (b : bool) : x *+ b = (if b then x else 0).
Proof. exact: (@expgb (multiplicative V)). Qed.

Lemma mul0gn n : 0 *+ n = 0 :> V.
Proof. exact: (exp1gn (multiplicative V)). Qed.

Lemma commuteT x y : @commute (multiplicative V) x y.
Proof. exact/addgC. Qed.

Lemma mulgnDl n : {morph (fun x => x *+ n) : x y / x + y}.
Proof. by move=> x y; apply/(@expgMn (multiplicative V))/commuteT. Qed.

Lemma mulgnDr x m n : x *+ (m + n) = x *+ m + x *+ n.
Proof. exact: (@expgnDr (multiplicative V)). Qed.

Lemma mulgnA x m n : x *+ (m * n) = x *+ m *+ n.
Proof. exact: (@expgnA (multiplicative V)). Qed.

Lemma mulgnAC x m n : x *+ m *+ n = x *+ n *+ m.
Proof. exact: (@expgnAC (multiplicative V)). Qed.

Lemma iter_addg n x y : iter n (+%g x) y = x *+ n + y.
Proof. exact: (@iter_mulg (multiplicative V)). Qed.

Lemma iter_addg_0 n x : iter n (+%g x) 0 = x *+ n.
Proof. exact: (@iter_mulg_1 (multiplicative V)). Qed.

Section ClosedPredicates.

Variable S : {pred V}.

Definition addg_closed := {in S &, forall u v, u + v \in S}.
Definition nmod_closed := 0 \in S /\ addg_closed.

End ClosedPredicates.

End NmoduleTheory.

HB.mixin Record Nmodule_isZmodule V of Nmodule V := {
  opp : V -> V;
  addNg : left_inverse zero opp add
}.

#[short(type="zmodType")]
HB.structure Definition Zmodule := {V of Nmodule_isZmodule V & Nmodule V}.

HB.factory Record isZmodule V of Choice V := {
  zero : V;
  opp : V -> V;
  add : V -> V -> V;
  addgA : associative add;
  addgC : commutative add;
  add0g : left_id zero add;
  addNg : left_inverse zero opp add
}.

HB.builders Context V of isZmodule V.

HB.instance Definition _ := isNmodule.Build V addgA addgC add0g.
HB.instance Definition _ := Nmodule_isZmodule.Build V addNg.

HB.end.

HB.factory Record Group_isZmodule V of Group V := {
  mulgC : commutative (@mul V)
}.

HB.builders Context V of Group_isZmodule V.

HB.instance Definition _ := isZmodule.Build V mulgA mulgC mul1g mulVg.

HB.end.

Module ZmodExports.
Bind Scope group_scope with Zmodule.sort.
#[deprecated(since="mathcomp 2.0.0", note="use GRing.isZmodule.Build instead")]
Notation ZmodMixin V := (isZmodule.Build V).
#[deprecated(since="mathcomp 2.0.0", note="Use GRing.Zmodule.clone instead.")]
Notation "[ 'zmodType' 'of' T 'for' cT ]" := (Zmodule.clone T cT)
  (at level 0, format "[ 'zmodType'  'of'  T  'for'  cT ]") : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use GRing.Zmodule.clone instead.")]
Notation "[ 'zmodType' 'of' T ]" :=  (Zmodule.clone T _)
  (at level 0, format "[ 'zmodType'  'of'  T ]") : form_scope.
End ZmodExports.
HB.export ZmodExports.

Local Notation "-%g" := (@opp _) : group_scope.
Local Notation "- x" := (opp x) : group_scope.
Local Notation "x - y" := (x + - y) : group_scope.
Local Notation "x *- n" := (- (x *+ n)) : group_scope.

Lemma addgN (V : zmodType) : @right_inverse V V V 0 -%g +%g.
Proof. by move=> x; rewrite addgC addNg. Qed.

HB.instance Definition _ (V : zmodType) := Monoid_isGroup.Build (multiplicative V) addNg (@addgN V).

Section ZmoduleTheory.

Variable V : zmodType.
Implicit Types x y : V.

Definition subrr := addgN.

Lemma addKg : @left_loop V V -%g +%g.
Proof. exact: (@mulKg (multiplicative V)). Qed.
Lemma addNKg : @rev_left_loop V V -%g +%g.
Proof. exact: (@mulVKg (multiplicative V)). Qed.
Lemma addgK : @right_loop V V -%g +%g.
Proof. exact: (@mulgK (multiplicative V)). Qed.
Lemma addgNK : @rev_right_loop V V -%g +%g.
Proof. exact: (@mulgVK (multiplicative V)). Qed.
Definition subgK := addgNK.
Lemma subKg x : involutive (fun y => x - y).
Proof. by move=> y; apply: (canLR (addgK _)); rewrite addgC subgK. Qed.
Lemma addgI : @right_injective V V V +%g.
Proof. exact: (@mulgI (multiplicative V)). Qed.
Lemma addIg : @left_injective V V V +%g.
Proof. exact: (@mulIg (multiplicative V)). Qed.
Lemma subgI : right_injective (fun x y => x - y).
Proof. exact: (@divgI (multiplicative V)). Qed.
Lemma subIg : left_injective (fun x y => x - y).
Proof. exact: (@divIg (multiplicative V)). Qed.
Lemma oppgK : @involutive V -%g.
Proof. exact: (@invgK (multiplicative V)). Qed.
Lemma oppg_inj : @injective V V -%g.
Proof. exact: (@invg_inj (multiplicative V)). Qed.
Lemma oppg0 : -0 = 0 :> V.
Proof. exact: (@invg1 (multiplicative V)). Qed.
Lemma oppg_eq0 x : (- x == 0) = (x == 0).
Proof. exact: (@invg_eq1 (multiplicative V)). Qed.

Lemma subg0 x : x - 0 = x. Proof. exact: (@divg1 (multiplicative V)). Qed.
Lemma sub0g x : 0 - x = - x. Proof. exact: (@div1g (multiplicative V)). Qed.

Lemma oppgB x y : - (x - y) = y - x.
Proof. exact: (@invgF (multiplicative V)). Qed.

Lemma oppgD : {morph -%g: x y / x + y : V}.
Proof. by move=> x y; rewrite -[y in LHS]oppgK oppgB addgC. Qed.

Lemma addgKA z x y : (x + z) - (z + y) = x - y.
Proof. by rewrite oppgD addgA addgK. Qed.

Lemma subgKA z x y : (x - z) + (z + y) = x + y.
Proof. exact: (@divgKA (multiplicative V)). Qed.

Lemma addg0_eq x y : x + y = 0 -> - x = y.
Proof. exact: (@mulg1_eq (multiplicative V)). Qed.

Lemma subg0_eq x y : x - y = 0 -> x = y.
Proof. exact: (@divg1_eq (multiplicative V)). Qed.

Lemma subg_eq x y z : (x - z == y) = (x == y + z).
Proof. exact: (@divg_eq (multiplicative V)). Qed.

Lemma subg_eq0 x y : (x - y == 0) = (x == y).
Proof. exact: (@divg_eq1 (multiplicative V)). Qed.

Lemma addg_eq0 x y : (x + y == 0) = (x == - y).
Proof. exact: (@mulg_eq1 (multiplicative V)). Qed.

Lemma eqg_opp x y : (- x == - y) = (x == y).
Proof. exact: (@eqg_inv (multiplicative V)). Qed.

Lemma eqg_oppLR x y : (- x == y) = (x == - y).
Proof. exact: (@eqg_invLR (multiplicative V)). Qed.

Lemma mulNgn x n : (- x) *+ n = x *- n.
Proof. exact: (@expVgn (multiplicative V)). Qed.

Lemma mulgnBl n : {morph (fun x => x *+ n) : x y / x - y}.
Proof.
move=> x y; elim: n => [|n IHn]; rewrite ?subg0 // !mulgS -!addgA; congr(_ + _).
by rewrite addgC IHn -!addgA oppgD [_ - y]addgC.
Qed.

Lemma mulgnBr x m n : n <= m -> x *+ (m - n) = x *+ m - x *+ n.
Proof. exact: (@expgnBr (multiplicative V)). Qed.

Section ClosedPredicates.

Variable S : {pred V}.

Definition oppg_closed := {in S, forall u, - u \in S}.
Definition subg_2closed := {in S &, forall u v, u - v \in S}.
Definition zmod_closed := 0 \in S /\ subg_2closed.

Lemma zmod_closedN : zmod_closed -> oppg_closed.
Proof. exact: (@group_closedV (multiplicative V)). Qed.

Lemma zmod_closedD : zmod_closed -> addg_closed S.
Proof. exact: (@group_closedM (multiplicative V)). Qed.

Lemma zmod_closed0D : zmod_closed -> nmod_closed S.
Proof. by move=> z; split; [case: z|apply: zmod_closedD]. Qed.

End ClosedPredicates.

End ZmoduleTheory.

Arguments addgI {V} y [x1 x2].
Arguments addIg {V} x [x1 x2].
Arguments oppgK {V}.
Arguments oppg_inj {V} [x1 x2].

Definition semi_additive (U V : nmodType) (f : U -> V) : Prop :=
  (f 0 = 0) * {morph f : x y / x + y}.

HB.mixin Record isSemiAdditive (U V : nmodType) (apply : U -> V) := {
  semi_additive_subproof : semi_additive apply;
}.

#[mathcomp(axiom="semi_additive")]
HB.structure Definition Additive (U V : nmodType) :=
  {f of isSemiAdditive U V f}.

Definition fmultiplicative U V := @id ((multiplicative U) -> (multiplicative V)).

HB.builders Context U V apply of isSemiAdditive U V apply.

Fact gmorphD : {morph apply : x y / x + y}.
Proof. by case: semi_additive_subproof. Qed.
Fact gmorph0 : apply 0 = 0.
Proof. by case: semi_additive_subproof. Qed.

HB.instance Definition _ := isMultiplicative.Build (multiplicative U) (multiplicative V) (fmultiplicative apply) gmorphD.
HB.instance Definition _ := isUMagmaMorphism.Build (multiplicative U) (multiplicative V) (fmultiplicative apply) gmorph0.

HB.end.

Definition additive (U V : zmodType) (f : U -> V) := {morph f : x y / x - y}.

HB.factory Record isAdditive (U V : zmodType) (apply : U -> V) := {
  additive_subproof : additive apply;
}.

HB.builders Context U V apply of isAdditive U V apply.
Local Lemma gaddf0 : apply 0 = 0.
Proof. by rewrite -[0]subg0 additive_subproof subrr. Qed.

Local Lemma gaddfD : {morph apply : x y / x + y}.
Proof.
move=> x y; rewrite -[y in LHS]oppgK -[- y]add0g.
by rewrite !additive_subproof gaddf0 sub0g oppgK.
Qed.

HB.instance Definition _ := isSemiAdditive.Build U V apply (conj gaddf0 gaddfD).

HB.end.

Module AdditiveExports.
Module Additive.
Definition apply_deprecated (U V : nmodType) (phUV : phant (U -> V)) :=
  @Additive.sort U V.
#[deprecated(since="mathcomp 2.0", note="Use Additive.sort instead.")]
Notation apply := apply_deprecated.
End Additive.
Notation "{ 'additive' U -> V }" := (Additive.type U%type V%type) : type_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use GRing.Additive.clone instead.")]
Notation "[ 'additive' 'of' f 'as' g ]" := (Additive.clone _ _ f%function g)
  (at level 0, format "[ 'additive'  'of'  f  'as'  g ]") : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use GRing.Additive.clone instead.")]
Notation "[ 'additive' 'of' f ]" := (Additive.clone _ _ f%function _)
  (at level 0, format "[ 'additive'  'of'  f ]") : form_scope.
End AdditiveExports.
HB.export AdditiveExports.

(*
HB.factory Record isAdditive (U V : nmodType) (f : U -> V) := {
  gaddfD : {morph f : x y / x + y}
}.

HB.builders Context U V apply of isAdditive U V apply.

HB.instance Definition _ := isMultiplicative.Build U V apply gaddfD.

HB.end.

HB.factory Record isNmodMorphism (U V : nmodType) (f : U -> V) := {
  gaddfD : {morph f : x y / x + y};
  gaddf0 : f 0 = 0
}.

Notation "NmodMorphism.type" := (UmagmaMorphism.type).

HB.builders Context U V apply of isNmodMorphism U V apply.

HB.instance Definition _ := isMultiplicative.Build U V apply gaddfD.
HB.instance Definition _ := isUmagmaMorphism.Build U V apply gaddf0.

HB.end.

HB.factory Record isZmodMorphism (U V : zmodType) (f : U -> V) := {
  gaddfB : {morph f : x y / x - y}
}.

HB.builders Context U V apply of isZmodMorphism U V apply.

HB.instance Definition _ := isGroupMorphism.Build U V apply gaddfB.

   HB.end.*)

Section LiftedNmod.
Variables (U : Type) (V : nmodType).
Definition null_fun of U : V := 0.
Definition add_fun (f g : U -> V) x := f x + g x.
End LiftedNmod.
Section LiftedZmod.
Variables (U : Type) (V : zmodType).
Definition sub_fun (f g : U -> V) x := f x - g x.
Definition opp_fun (f : U -> V) x := - f x.
End LiftedZmod.

Local Notation "\0" := (null_fun _) : group_scope.
Local Notation "f \+ g" := (add_fun f g) : group_scope.
Local Notation "f \- g" := (sub_fun f g) : group_scope.
Local Notation "\- f" := (opp_fun f) : group_scope.

Arguments null_fun {_} V _ /.
Arguments add_fun {_ _} f g _ /.
Arguments sub_fun {_ _} f g _ /.
Arguments opp_fun {_ _} f _ /.

Section Nmod.
Variables (U V : nmodType) (f : {additive U -> V}).

Lemma gaddf0 : f 0 = 0.
Proof. exact: gmulf1. Qed.

Lemma gaddf_eq0 x : injective f -> (f x == 0) = (x == 0).
Proof. exact: gmulf_eq1. Qed.

Lemma gaddfD : {morph f : x y / x + y}.
Proof. exact: gmulfM. Qed.

Lemma gaddfMn n : {morph f : x / x *+ n}.
Proof. exact: (@gmulfXn U V f). Qed.

Lemma can2_semi_additive f' : cancel f f' -> cancel f' f -> semi_additive f'.
Proof. by split; [apply: (@can2_gmulf1 U V f)|apply/can2_gmulfM]. Qed.
End Nmod.

Section Zmod.
Variables (U V : zmodType) (f : {additive U -> V}).

Lemma gaddfN : {morph f : x / - x}.
Proof. exact: (@gmulfV U V f). Qed.

Lemma gaddfB : {morph f : x y / x - y}.
Proof. exact: (@gmulfB U V f). Qed.

Lemma gaddf_inj : (forall x, f x = 0 -> x = 0) -> injective f.
Proof. exact: (@gmulf_inj U V f). Qed.

Lemma gaddfMNn n : {morph f : x / x *- n}.
Proof. exact: (@gmulfXVn U V f). Qed.

Lemma can2_additive f' : cancel f f' -> cancel f' f -> additive f'.
Proof. by move=> fK f'K x y /=; apply: (canLR fK); rewrite gaddfB !f'K. Qed.
End Zmod.

Section MorphismTheory.
Section MulCFun.
Variables (U : magmaType) (V : nmodType).
Variables (f g : Multiplicative.type U V).

Fact mul_fun_gmulfM : {morph f \* g : x y / x * y}.
Proof. by move=> x y; rewrite /mul_fun !gmulfM [LHS]addgACA. Qed.
HB.instance Definition _ := isMultiplicative.Build U V (f \* g) mul_fun_gmulfM.
End MulCFun.

Section AddFun.

Variables (U V W : nmodType).
Variables (f g : {additive V -> W}) (h : {additive U -> V}).

Fact idfun_is_semi_additive : semi_additive (@idfun U).
Proof. by []. Qed.
#[export]
HB.instance Definition _ := isSemiAdditive.Build U U idfun
  idfun_is_semi_additive.

Fact comp_is_semi_additive : semi_additive (f \o h).
Proof. by split=> [|x y]; rewrite /= ?gaddf0// !gaddfD. Qed.
#[export]
HB.instance Definition _ := isSemiAdditive.Build U W (f \o h)
  comp_is_semi_additive.

Fact null_fun_is_semi_additive : semi_additive (\0 : U -> V).
Proof. by split=> // x y /=; rewrite addg0. Qed.
#[export]
HB.instance Definition _ := isSemiAdditive.Build U V \0
  null_fun_is_semi_additive.

Fact add_fun_is_semi_additive : semi_additive (f \+ g).
Proof.
by split=> [|x y]; rewrite /= ?gaddf0 ?addg0// !gaddfD addgCA -!addgA addgCA.
Qed.
#[export]
HB.instance Definition _ := isSemiAdditive.Build V W (f \+ g)
  add_fun_is_semi_additive.

End AddFun.

Section AddVFun.
Variables (U V W : zmodType).
Variables (f g : {additive V -> W}) (h : {additive U -> V}).

Fact opp_is_semi_additive : semi_additive (@opp U).
Proof. by split; [apply/oppg0|apply/oppgD]. Qed.
HB.instance Definition _ :=
  isSemiAdditive.Build U U (@opp U) opp_is_semi_additive.

Fact sub_fun_is_additive : additive (f \- g).
Proof.
by move=> x y /=; rewrite !gaddfB addgAC -!addgA -!oppgD addgAC addgA.
Qed.
HB.instance Definition _ :=
  isAdditive.Build V W (f \- g) sub_fun_is_additive.

Fact opp_fun_is_additive : additive (\- g).
Proof. by move=> x y /=; rewrite !gaddfB oppgB addgC oppgK. Qed.
#[export]
HB.instance Definition _ := isAdditive.Build V W (\- g) opp_fun_is_additive.

End AddVFun.
End MorphismTheory.

HB.mixin Record isAddClosed (V : nmodType) (S : {pred V}) := {
  gpred0D : nmod_closed S
}.

(* Mixins for stability properties *)

HB.builders Context V S of isAddClosed V S.
HB.instance Definition _ := isMulClosed.Build V S (snd gpred0D).
HB.instance Definition _ := isMul1Closed.Build V S (fst gpred0D).
HB.end.

HB.mixin Record isOppClosed (V : zmodType) (S : {pred V}) := {
  gpredNr : oppg_closed S
}.

HB.builders Context V S of isOppClosed V S.
HB.instance Definition _ := isInvClosed.Build V S gpredNr.
HB.end.

(* Structures for stability properties *)

#[short(type="addgClosed")]
HB.structure Definition AddClosed V := {S of isAddClosed V S}.

#[short(type="oppgClosed")]
HB.structure Definition OppClosed V := {S of isOppClosed V S}.

#[short(type="zmodClosed")]
HB.structure Definition ZmodClosed V := {S of OppClosed V S & AddClosed V S & isAddClosed V S}.

(* Factories for stability properties *)

HB.factory Record isZmodClosed (V : zmodType) (S : V -> bool) := {
  zmod_closed_subproof : zmod_closed S
}.

HB.builders Context V S of isZmodClosed V S.
HB.instance Definition _ := isOppClosed.Build V S
  (zmod_closedN zmod_closed_subproof).
HB.instance Definition _ := isAddClosed.Build V S
  (zmod_closed0D zmod_closed_subproof).
HB.end.

Section NmodPred.
Variables (V : nmodType).

Section Nmod.
Variables S : addgClosed V.

Lemma gpred0 : 0 \in S.
Proof. by case: (@gpred0D V S). Qed.
Lemma gpredD : {in S &, forall u v, u + v \in S}.
Proof. by case: (@gpred0D V S). Qed.

Lemma gpredMn n : {in S, forall u, u *+ n \in S}.
Proof. by move=> x xS; elim: n => [|n IHn]; rewrite /= ?gpred0 // mulgS gpredD. Qed.

End Nmod.
End NmodPred.

Section ZmodPred.
Variables (V : zmodType).

Section Opp.

Variable S : oppgClosed V.

Lemma gpredN : {mono -%g: u / u \in S}.
Proof. by move=> u; apply/idP/idP=> /gpredNr; rewrite ?oppgK; apply. Qed.

End Opp.

Section Zmod.
Variables S : zmodClosed V.

Lemma gpredB : {in S &, forall u v, u - v \in S}.
Proof. by move=> x y xS yS; rewrite gpredD// gpredN. Qed.

Lemma gpredBC u v : u - v \in S = (v - u \in S).
Proof. by rewrite -gpredN oppgB. Qed.

Lemma gpredMNn n: {in S, forall u, u *- n \in S}.
Proof. by move=> x xS; apply/gpredNr/gpredMn. Qed.

Lemma gpredDr x y : x \in S -> (y + x \in S) = (y \in S).
Proof.
move=> Sx; apply/idP/idP => [Sxy|/gpredD-> //].
by rewrite -(addgK x y) gpredB.
Qed.

Lemma gpredDl x y : x \in S -> (x + y \in S) = (y \in S).
Proof.
move=> Sx; apply/idP/idP => [Sxy|/(gpredD Sx)//].
by rewrite -[y]add0g -(addNg x) -addgA gpredD// gpredN.
Qed.

Lemma gpredBr x y : x \in S -> (y - x \in S) = (y \in S).
Proof. by rewrite -gpredN; apply: gpredDr. Qed.

Lemma gpredBl x y : x \in S -> (x - y \in S) = (y \in S).
Proof. by rewrite -[x \in S]gpredN -[LHS]gpredN oppgB; apply: gpredDr. Qed.

End Zmod.
End ZmodPred. 

#[short(type="subNmodType")]
HB.structure Definition SubNmodule (V : nmodType) S :=
  { U of SubMonoid V S U & Nmodule U}.

Section subNmodule.
Context (V : nmodType) (S : pred V) (U : subNmodType S).
Notation val := (val : U -> V).
Fact val_is_semi_additive : semi_additive val.
Proof. by split; [apply/val1|apply/valM]. Qed.
#[export]
HB.instance Definition _ := isSemiAdditive.Build U V val val_is_semi_additive.
Lemma valD : {morph (val : U -> V) : x y / x + y}.
Proof. exact: valM. Qed.
Lemma val0 : val 0 = 0. Proof. exact: val1. Qed.
End subNmodule.

HB.factory Record SubChoice_isSubNmodule (V : nmodType) S U
    of SubChoice V S U := {
  nmod_closed_subproof : nmod_closed S
}.

HB.builders Context V S U of SubChoice_isSubNmodule V S U.

HB.instance Definition _ := isAddClosed.Build V S nmod_closed_subproof.

HB.instance Definition _ := SubChoice_isSubUMagma.Build V S U nmod_closed_subproof.
HB.instance Definition _ := SubChoice_isSubSemigroup.Build V S U (snd nmod_closed_subproof).

Lemma mulgC : commutative (@mul U).
Proof. by move=> x y; apply/val_inj; rewrite !valM mulgC. Qed.

HB.instance Definition _ := Monoid_isNmodule.Build U mulgC.

HB.end.

#[short(type="subZmodType")]
HB.structure Definition SubZmodule (V : zmodType) S :=
  { U of SubMonoid V S U & Zmodule U}.

Section additive.
Context (V : zmodType) (S : pred V) (U : SubZmodule.type S).
Notation val := (val : U -> V).
Lemma valB : {morph val : x y / x - y}. Proof. exact: gaddfB. Qed.
Lemma valN : {morph val : x / - x}. Proof. exact: gaddfN. Qed.
End additive.

HB.factory Record SubChoice_isSubZmodule (V : zmodType) S U
    of SubChoice V S U := {
  zmod_closed_subproof : zmod_closed S
}.

HB.builders Context V S U of SubChoice_isSubZmodule V S U.

HB.instance Definition _ :=
  SubChoice_isSubGroup.Build V S U zmod_closed_subproof.

Lemma mulgC : commutative (@mul U).
Proof. by move=> x y; apply/val_inj; rewrite !valM mulgC. Qed.

HB.instance Definition _ := Monoid_isNmodule.Build U mulgC.

HB.end.

Section FinFunNmod.

Variable (aT : finType) (rT : nmodType).
Implicit Types f g : {ffun aT -> rT}.

(* TODO: find a way to make the following instance use these definitions. *)
Definition ffun_add f g := [ffun a => f a + g a].
Definition ffun_zero := [ffun a : aT => (0 : rT)].

Fact ffun_addgC : commutative ffun_add.
Proof. by move=> f1 f2; apply/ffunP=> a; rewrite !ffunE; rewrite addgC. Qed.

#[export]
HB.instance Definition _ := Monoid_isNmodule.Build {ffun aT -> rT} ffun_addgC.

Lemma ffunMnE f n x : (f *+ n) x = f x *+ n.
Proof.
(* TODO: the `rewrite ffunE` produces a `1` where I would like a `0` (which comes from `ffun_one`). *)
elim: n => [|n IHn]; first by rewrite ffunE.
by rewrite !mulgS ffunE IHn.
Qed.

End FinFunNmod.

(* TODO: HB.saturate *)
#[export]
HB.instance Definition _ (aT : finType) (rT : zmodType) := Group_isZmodule.Build {ffun aT -> rT} (@ffun_addgC aT rT).

Section PairNmodule.
Variables U V : nmodType.

Lemma pair_mulgC : commutative (@mul (U * V)%type).
Proof. by move=> x y; congr (_, _); apply/mulgC. Qed.

HB.instance Definition _ := Monoid_isNmodule.Build (U * V)%type pair_mulgC.

HB.instance Definition _ := isSemiAdditive.Build (U * V)%type U (@fst U V) (@fst_is_umagma_morphism U V, @fst_is_multiplicative U V)%PAIR.
HB.instance Definition _ := isSemiAdditive.Build (U * V)%type V (@snd U V) (@snd_is_umagma_morphism U V, @snd_is_multiplicative U V)%PAIR.

End PairNmodule.

(* TODO: HB.saturate *)
HB.instance Definition _ (U V : zmodType) := Group_isZmodule.Build (U * V)%type (@pair_mulgC U V).

(* zmodType structure on bool *)
HB.instance Definition _ := isZmodule.Build bool addbA addbC addFb addbb.

(* nmodType structure on nat *)
HB.instance Definition _ := isNmodule.Build nat addnA addnC add0n.

HB.instance Definition _ (V : nmodType) (x : V) :=
  isSemiAdditive.Build nat V (natmul x) (mulg0n x, mulgnDr x).

Lemma natg0E : 0 = 0%N. Proof. by []. Qed.
Lemma natgDE n m : n + m = (n + m)%N. Proof. by []. Qed.
Definition natgE := (natg0E, natgDE).

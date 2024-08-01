From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype choice ssrnat seq.
From mathcomp Require Import fintype finfun monoid.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope ring_scope.
Delimit Scope ring_scope with R.
Local Open Scope ring_scope.

Reserved Notation "+%R" (at level 0).
Reserved Notation "-%R" (at level 0).
Reserved Notation "n %:R" (at level 2, left associativity, format "n %:R").
Reserved Notation "\0" (at level 0).
Reserved Notation "f \+ g" (at level 50, left associativity).
Reserved Notation "f \- g" (at level 50, left associativity).
Reserved Notation "\- f" (at level 35, f at level 35).

Reserved Notation "'{' 'additive' U '->' V '}'"
  (at level 0, U at level 98, V at level 99,
   format "{ 'additive'  U  ->  V }").

Module Import GRing.

HB.mixin Record isAddMagma V := {
  add : V -> V -> V
}.

#[short(type="addMagmaType")]
HB.structure Definition AddMagma := {V of isAddMagma V & Choice V}.

Module AddMagmaExports.
Bind Scope ring_scope with AddMagma.sort.
End AddMagmaExports.
HB.export AddMagmaExports. 

Local Notation "+%R" := (@add _) : function_scope.
Local Notation "x + y" := (add x y) : ring_scope.

Definition multiplicative := @id Type.

#[export]
HB.instance Definition _ (V : addMagmaType) := Choice.on (multiplicative V).
#[export]
HB.instance Definition _ (V : addMagmaType) := isMagma.Build (multiplicative V) (@add V).

HB.mixin Record AddMagma_isBaseAddUMagma V of AddMagma V := {
  zero : V
}.

HB.structure Definition BaseAddUMagma := {V of AddMagma_isBaseAddUMagma V & AddMagma V}.

Module BaseAddUMagmaExports.
Bind Scope ring_scope with BaseAddUMagma.sort.
End BaseAddUMagmaExports.
HB.export BaseAddUMagmaExports. 

#[export]
HB.instance Definition _ (V : BaseAddUMagma.type) := Magma_isBaseUMagma.Build (multiplicative V) (@zero V).

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

Module AddUMagmaExports.
Bind Scope ring_scope with AddUMagma.sort.
End AddUMagmaExports.
HB.export AddUMagmaExports. 

Local Notation "0" := (@zero _) : ring_scope.

Definition natmul (V : addUMagmaType) (x : V) n := @iterop _ n (add : V -> V -> V) x (@zero V).
Arguments natmul : simpl never.

Local Notation "x *+ n" := (natmul x n) : ring_scope.

Lemma addg0 (V : addUMagmaType) : right_id (@zero V) add.
Proof. by move=> x; rewrite addgC add0g. Qed.

#[export]
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
Bind Scope ring_scope with Nmodule.sort.
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

#[export]
HB.instance Definition _ (V : nmodType) := UMagma_isMonoid.Build (multiplicative V) addgA.

Section NmoduleTheory.

Variable V : nmodType.
Implicit Types x y : V.

(* addgA, addgC and add0g in the structure *)
(* addg0 proved above *)

Lemma addgCA : @left_commutative V V +%R.
Proof. by move=> x y z; rewrite !addgA [x + _]addgC. Qed.

Lemma addgAC : @right_commutative V V +%R.
Proof. by move=> x y z; rewrite -!addgA [y + _]addgC. Qed.

Lemma addgACA : @interchange V +%R +%R.
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

Lemma iter_addg n x y : iter n (+%R x) y = x *+ n + y.
Proof. exact: (@iter_mulg (multiplicative V)). Qed.

Lemma iter_addg_0 n x : iter n (+%R x) 0 = x *+ n.
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
Bind Scope ring_scope with Zmodule.sort.
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

Local Notation "-%R" := (@opp _) : ring_scope.
Local Notation "- x" := (opp x) : ring_scope.
Local Notation "x - y" := (x + - y) : ring_scope.
Local Notation "x *- n" := (- (x *+ n)) : ring_scope.

Lemma addgN (V : zmodType) : @right_inverse V V V 0 -%R +%R.
Proof. by move=> x; rewrite addgC addNg. Qed.

#[export]
HB.instance Definition _ (V : zmodType) := Monoid_isGroup.Build (multiplicative V) addNg (@addgN V).

Section ZmoduleTheory.

Variable V : zmodType.
Implicit Types x y : V.

Definition subgg := addgN.

Lemma addKg : @left_loop V V -%R +%R.
Proof. exact: (@mulKg (multiplicative V)). Qed.
Lemma addNKg : @rev_left_loop V V -%R +%R.
Proof. exact: (@mulVKg (multiplicative V)). Qed.
Lemma addgK : @right_loop V V -%R +%R.
Proof. exact: (@mulgK (multiplicative V)). Qed.
Lemma addgNK : @rev_right_loop V V -%R +%R.
Proof. exact: (@mulgVK (multiplicative V)). Qed.
Definition subgK := addgNK.
Lemma subKg x : involutive (fun y => x - y).
Proof. by move=> y; apply: (canLR (addgK _)); rewrite addgC subgK. Qed.
Lemma addgI : @right_injective V V V +%R.
Proof. exact: (@mulgI (multiplicative V)). Qed.
Lemma addIg : @left_injective V V V +%R.
Proof. exact: (@mulIg (multiplicative V)). Qed.
Lemma subgI : right_injective (fun x y => x - y).
Proof. exact: (@divgI (multiplicative V)). Qed.
Lemma subIg : left_injective (fun x y => x - y).
Proof. exact: (@divIg (multiplicative V)). Qed.
Lemma oppgK : @involutive V -%R.
Proof. exact: (@invgK (multiplicative V)). Qed.
Lemma oppg_inj : @injective V V -%R.
Proof. exact: (@invg_inj (multiplicative V)). Qed.
Lemma oppg0 : -0 = 0 :> V.
Proof. exact: (@invg1 (multiplicative V)). Qed.
Lemma oppg_eq0 x : (- x == 0) = (x == 0).
Proof. exact: (@invg_eq1 (multiplicative V)). Qed.

Lemma subg0 x : x - 0 = x. Proof. exact: (@divg1 (multiplicative V)). Qed.
Lemma sub0g x : 0 - x = - x. Proof. exact: (@div1g (multiplicative V)). Qed.

Lemma oppgB x y : - (x - y) = y - x.
Proof. exact: (@invgF (multiplicative V)). Qed.

Lemma oppgD : {morph -%R: x y / x + y : V}.
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

Definition semi_additive (U V : BaseAddUMagma.type) (f : U -> V) : Prop :=
  (f 0 = 0) * {morph f : x y / x + y}.

HB.mixin Record isSemiAdditive (U V : BaseAddUMagma.type) (apply : U -> V) := {
  semi_additive_subproof : semi_additive apply;
}.

#[mathcomp(axiom="semi_additive")]
HB.structure Definition Additive (U V : BaseAddUMagma.type) :=
  {f of isSemiAdditive U V f}.

Definition additive (U V : zmodType) (f : U -> V) := {morph f : x y / x - y}.

HB.factory Record isAdditive (U V : zmodType) (apply : U -> V) := {
  additive_subproof : additive apply;
}.

HB.builders Context U V apply of isAdditive U V apply.
Local Lemma gaddf0 : apply 0 = 0.
Proof. by rewrite -[0]subg0 additive_subproof subgg. Qed.

Local Lemma gaddfD : {morph apply : x y / x + y}.
Proof.
move=> x y; rewrite -[y in LHS]oppgK -[- y]add0g.
by rewrite !additive_subproof gaddf0 sub0g oppgK.
Qed.

HB.instance Definition _ := isSemiAdditive.Build U V apply (conj gaddf0 gaddfD).

HB.end.

Module AdditiveExports.
Module Additive.
Definition apply_deprecated (U V : BaseAddUMagma.type) (phUV : phant (U -> V)) :=
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

Lemma gaddf0 (U V : BaseAddUMagma.type) (f : {additive U -> V}) : f 0 = 0.
Proof. by case: (@semi_additive_subproof _ _ f). Qed.

Lemma gaddfD (U V : BaseAddUMagma.type) (f : {additive U -> V}) :
  {morph f : x y / x + y}.
Proof. by case: (@semi_additive_subproof _ _ f). Qed.

Definition fmultiplicative U V := @id ((multiplicative U) -> (multiplicative V)).

#[export]
HB.instance Definition _ U V (f : Additive.type U V) := isMultiplicative.Build (multiplicative U) (multiplicative V) (fmultiplicative f) (@gaddfD _ _ f).
#[export]
HB.instance Definition _ (U V : addUMagmaType) (f : Additive.type U V) := isUMagmaMorphism.Build (multiplicative U) (multiplicative V) (fmultiplicative f) (@gaddf0 _ _ f).

Section LiftedNmod.
Variables (U : Type) (V : BaseAddUMagma.type).
Definition null_fun of U : V := 0.
Definition add_fun (f g : U -> V) x := f x + g x.
End LiftedNmod.
Section LiftedZmod.
Variables (U : Type) (V : zmodType).
Definition sub_fun (f g : U -> V) x := f x - g x.
Definition opp_fun (f : U -> V) x := - f x.
End LiftedZmod.

Local Notation "\0" := (null_fun _) : ring_scope.
Local Notation "f \+ g" := (add_fun f g) : ring_scope.
Local Notation "f \- g" := (sub_fun f g) : ring_scope.
Local Notation "\- f" := (opp_fun f) : ring_scope.

Arguments null_fun {_} V _ /.
Arguments add_fun {_ _} f g _ /.
Arguments sub_fun {_ _} f g _ /.
Arguments opp_fun {_ _} f _ /.

Section Nmod.
Variables (U V : nmodType) (f : {additive U -> V}).

Lemma gaddf_eq0 x : injective f -> (f x == 0) = (x == 0).
Proof. exact: (@gmulf_eq1 _ _ (fmultiplicative f)). Qed.

Lemma gaddfMn n : {morph f : x / x *+ n}.
Proof. exact: (@gmulfXn _ _ (fmultiplicative f)). Qed.

Lemma can2_semi_additive f' : cancel f f' -> cancel f' f -> semi_additive f'.
Proof.
split; first exact/(@can2_gmulf1 _ _ (fmultiplicative f)).
exact/(@can2_gmulfM _ _ (fmultiplicative f)).
Qed.

End Nmod.

Section Zmod.
Variables (U V : zmodType) (f : {additive U -> V}).

Lemma gaddfN : {morph f : x / - x}.
Proof. exact: (@gmulfV _ _ (fmultiplicative f)). Qed.

Lemma gaddfB : {morph f : x y / x - y}.
Proof. exact: (@gmulfB _ _ (fmultiplicative f)). Qed.

Lemma gaddf_inj : (forall x, f x = 0 -> x = 0) -> injective f.
Proof. exact: (@gmulf_inj _ _ (fmultiplicative f)). Qed.

Lemma gaddfMNn n : {morph f : x / x *- n}.
Proof. exact: (@gmulfXVn _ _ (fmultiplicative f)). Qed.

Lemma can2_additive f' : cancel f f' -> cancel f' f -> additive f'.
Proof. by move=> fK f'K x y /=; apply: (canLR fK); rewrite gaddfB !f'K. Qed.
End Zmod.

Section AdditiveTheory.
Section AddCFun.
Variables (U : BaseAddUMagma.type) (V : nmodType).
Variables (f g : Additive.type U V).

Fact add_fun_semi_additive : semi_additive (f \+ g).
Proof.
split; first by rewrite /add_fun !gaddf0 addg0.
by move=> x y; rewrite /add_fun !gaddfD [LHS]addgACA.
Qed.
HB.instance Definition _ := isSemiAdditive.Build U V (f \+ g) add_fun_semi_additive.
End AddCFun.

Section AddFun.
Variables (U V W : BaseAddUMagma.type).
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

End AddFun.
Section AddFun.
Variables (U : BaseAddUMagma.type) (V : addUMagmaType) (W : nmodType).
Variables (f g : {additive U -> W}).

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
HB.instance Definition _ := isSemiAdditive.Build U W (f \+ g)
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
End AdditiveTheory.

(* Mixins for stability properties *)

HB.mixin Record isAddClosed (V : nmodType) (S : {pred V}) := {
  nmod_closed_subproof : nmod_closed S
}.

HB.mixin Record isOppClosed (V : zmodType) (S : {pred V}) := {
  oppg_closed_subproof : oppg_closed S
}.

(* Structures for stability properties *)

#[short(type="addgClosed")]
HB.structure Definition AddClosed V := {S of isAddClosed V S}.

#[short(type="oppgClosed")]
HB.structure Definition OppClosed V := {S of isOppClosed V S}.

#[short(type="zmodClosed")]
HB.structure Definition ZmodClosed V := {S of OppClosed V S & AddClosed V S}.

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


Definition rmultiplicative (T : Type) := @id {pred (multiplicative T)}.

#[export]
HB.instance Definition _ (U : nmodType) (S : addgClosed U) :=
  isMulClosed.Build (multiplicative U) (rmultiplicative S) (snd nmod_closed_subproof).
#[export]
HB.instance Definition _ (U : nmodType) (S : addgClosed U) :=
  isMul1Closed.Build (multiplicative U) (rmultiplicative S) (fst nmod_closed_subproof).
#[export]
HB.instance Definition _ (U : zmodType) (S : oppgClosed U) :=
  isInvClosed.Build (multiplicative U) (rmultiplicative S) oppg_closed_subproof.

Section NmodPred.
Variables (V : nmodType).

Section Nmod.
Variables S : addgClosed V.

Lemma gpred0 : 0 \in S.
Proof. by case: (@nmod_closed_subproof V S). Qed.
Lemma gpredD : {in S &, forall u v, u + v \in S}.
Proof. by case: (@nmod_closed_subproof V S). Qed.

Lemma gpred0D : nmod_closed S.
Proof. exact: nmod_closed_subproof. Qed.

Lemma gpredMn n : {in S, forall u, u *+ n \in S}.
Proof. by move=> x xS; elim: n => [|n IHn]; rewrite /= ?gpred0 // mulgS gpredD. Qed.

End Nmod.
End NmodPred.

Section ZmodPred.
Variables (V : zmodType).

Section Opp.

Variable S : oppgClosed V.

Lemma gpredNr : {in S, forall u, - u \in S}.
Proof. exact: oppg_closed_subproof. Qed.

Lemma gpredN : {mono -%R: u / u \in S}.
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

Lemma zmodClosedP : zmod_closed S.
Proof. split; [ exact: (@gpred0D V S).1 | exact: gpredB ]. Qed.
End Zmod.
End ZmodPred. 

HB.mixin Record isSubAddUMagma (V : BaseAddUMagma.type) (S : pred V) U of SubType V S U & AddUMagma U := {
  valD0_subproof : semi_additive (val : U -> V)
}.

#[short(type="subNmodType")]
HB.structure Definition SubNmodule (V : nmodType) S :=
  { U of SubChoice V S U & Nmodule U & isSubAddUMagma V S U}.

Section subNmodule.
Context (V : nmodType) (S : pred V) (U : subNmodType S).
Notation val := (val : U -> V).
#[export]
HB.instance Definition _ := isSemiAdditive.Build U V val valD0_subproof.
Lemma valD : {morph (val : U -> V) : x y / x + y}.
Proof. exact: gaddfD. Qed.
Lemma val0 : val 0 = 0. Proof. exact: gaddf0. Qed.
End subNmodule.

HB.factory Record SubChoice_isSubNmodule (V : nmodType) S U
    of SubChoice V S U := {
  nmod_closed_subproof : nmod_closed S
}.

HB.builders Context V S U of SubChoice_isSubNmodule V S U.

HB.instance Definition _ := isAddClosed.Build V S nmod_closed_subproof.

Let inU v Sv : U := Sub v Sv.
Let addU (u1 u2 : U) := inU (gpredD (valP u1) (valP u2)).
Let oneU := inU (fst nmod_closed_subproof).

Lemma addgA : associative addU.
Proof. by move=> x y z; apply/val_inj; rewrite !SubK addgA. Qed.

Lemma addgC : commutative addU.
Proof. by move=> x y; apply/val_inj; rewrite !SubK addgC. Qed.

Lemma add0g : left_id oneU addU.
Proof. by move=> x; apply/val_inj; rewrite !SubK add0g. Qed.

HB.instance Definition _ := isNmodule.Build U addgA addgC add0g.

Lemma valD0 : semi_additive (val : U -> V).
Proof. by split=> [|x y]; rewrite !SubK. Qed.

HB.instance Definition _ := isSubAddUMagma.Build V S U valD0.

HB.end.

#[short(type="subZmodType")]
HB.structure Definition SubZmodule (V : zmodType) S :=
  { U of SubChoice V S U & Zmodule U & isSubAddUMagma V S U}.

Section additive.
Context (V : zmodType) (S : pred V) (U : SubZmodule.type S).
Notation val := (val : U -> V).
Lemma valB : {morph val : x y / x - y}. Proof. exact: gaddfB. Qed.
Lemma valN : {morph val : x / - x}. Proof. exact: gaddfN. Qed.
End additive.

HB.factory Record isSubZmodule (V : zmodType) S U
    of SubChoice V S U & Zmodule U := {
  valB_subproof : additive (val : U -> V)
}.

HB.builders Context V S U of isSubZmodule V S U.

Fact valD0 : semi_additive (val : U -> V).
Proof.
have val0: (val : U -> V) 0 = 0.
  by rewrite -[X in val X](subg0 0) valB_subproof subgg.
split=> // x y; apply/(@subIg _ (val y)).
by rewrite -valB_subproof -!addgA !subgg !addg0.
Qed.

HB.instance Definition _ := isSubAddUMagma.Build V S U valD0.

HB.end.

HB.factory Record SubChoice_isSubZmodule (V : zmodType) S U
    of SubChoice V S U := {
  zmod_closed_subproof : zmod_closed S
}.

HB.builders Context V S U of SubChoice_isSubZmodule V S U.

HB.instance Definition _ := isZmodClosed.Build V S zmod_closed_subproof.
HB.instance Definition _ := SubChoice_isSubNmodule.Build V S U nmod_closed_subproof.

Let inU v Sv : U := Sub v Sv.
(* TODO: I should not have to write the builder. *)
Let oppU (u : U) := inU (gpredNr (valP u)).

Lemma addNg : left_inverse 0 oppU (@add U).
Proof. by move=> x; apply/val_inj; rewrite !SubK addNg. Qed.

HB.instance Definition _ := Nmodule_isZmodule.Build U addNg.

HB.end.

Module SubExports.

Notation "[ 'SubChoice_isSubNmodule' 'of' U 'by' <: ]" :=
  (SubChoice_isSubNmodule.Build _ _ U gpred0D)
  (at level 0, format "[ 'SubChoice_isSubNmodule'  'of'  U  'by'  <: ]")
  : form_scope.
Notation "[ 'SubChoice_isSubZmodule' 'of' U 'by' <: ]" :=
  (SubChoice_isSubZmodule.Build _ _ U (zmodClosedP _))
  (at level 0, format "[ 'SubChoice_isSubZmodule'  'of'  U  'by'  <: ]")
  : form_scope.

End SubExports.
HB.export SubExports.

Module AllExports. HB.reexport. End AllExports.

End GRing.

Export AllExports.

Notation "0" := (@zero _) : ring_scope.
Notation "-%R" := (@opp _) : ring_scope.
Notation "- x" := (opp x) : ring_scope.
Notation "+%R" := (@add _) : function_scope.
Notation "x + y" := (add x y) : ring_scope.
Notation "x - y" := (add x (- y)) : ring_scope.
Arguments natmul : simpl never.
Notation "x *+ n" := (natmul x n) : ring_scope.
Notation "x *- n" := (opp (x *+ n)) : ring_scope.
Notation "s `_ i" := (seq.nth 0%R s%R i) : ring_scope.
Notation support := 0.-support.

Notation "1" := (@one _) : ring_scope.
Notation "- 1" := (opp 1) : ring_scope.

Notation "n %:R" := (natmul 1 n) : ring_scope.

Section FinFunNmod.

Variable (aT : finType) (rT : nmodType).
Implicit Types f g : {ffun aT -> rT}.

Definition ffun_add f g := [ffun a => f a + g a].
Definition ffun_zero := [ffun a : aT => (0 : rT)].

Fact ffun_addgA : associative ffun_add.
Proof. by move=> f g h; apply/ffunP => a; rewrite !ffunE addgA. Qed.

Fact ffun_addgC : commutative ffun_add.
Proof. by move=> f1 f2; apply/ffunP => a; rewrite !ffunE addgC. Qed.

Fact ffun_add0g : left_id ffun_zero ffun_add.
Proof. by move=> f; apply/ffunP => a; rewrite !ffunE add0g. Qed.

#[export]
HB.instance Definition _ := isNmodule.Build {ffun aT -> rT} ffun_addgA ffun_addgC ffun_add0g.

Lemma ffunMnE f n x : (f *+ n) x = f x *+ n.
Proof.
elim: n => [|n IHn]; first by rewrite ffunE.
by rewrite !mulgS ffunE IHn.
Qed.

End FinFunNmod.

Section FinFunZmod.

Variable (aT : finType) (rT : zmodType).
Implicit Types f g : {ffun aT -> rT}.

Definition ffun_opp f := [ffun a => - (f a)].

Fact ffun_addNg : left_inverse 0 ffun_opp +%R.
Proof. by move=> f; apply/ffunP => a; rewrite !ffunE addNg. Qed.

HB.instance Definition _ := Nmodule_isZmodule.Build {ffun aT -> rT} ffun_addNg.

End FinFunZmod.

Section PairNmodule.
Variables U V : nmodType.

Definition pair_add (a b : U * V) := (a.1 + b.1, a.2 + b.2).
Definition pair_zero : U * V := (0, 0).

Fact pair_addgA : associative pair_add.
Proof. by move=> [] al ar [] bl br [] cl cr; rewrite /pair_add !addgA. Qed.

Fact pair_addgC : commutative pair_add.
Proof. by move=> [] al ar [] bl br; congr pair; rewrite /pair_add addgC. Qed.

Fact pair_add0g : left_id pair_zero pair_add.
Proof. by move=> [] al ar; rewrite /pair_add !add0g. Qed.

#[export]
HB.instance Definition _ := isNmodule.Build (U * V)%type pair_addgA pair_addgC pair_add0g.

Fact fst_is_additive : semi_additive (@fst U V). Proof. by []. Qed.
Fact snd_is_additive : semi_additive (@snd U V). Proof. by []. Qed.

HB.instance Definition _ := isSemiAdditive.Build (U * V)%type U (@fst U V) fst_is_additive.
HB.instance Definition _ := isSemiAdditive.Build (U * V)%type V (@snd U V) snd_is_additive.

End PairNmodule.

Section PairZmodule.
Variables U V : zmodType.

Definition pair_opp (a : U * V) := (- a.1, - a.2).

Fact pair_addNg : left_inverse 0 pair_opp +%R.
Proof. by move=> [] al ar; rewrite /pair_opp; congr pair; apply/addNg. Qed.

HB.instance Definition _ := Nmodule_isZmodule.Build (U * V)%type pair_addNg.

End PairZmodule.

(* zmodType structure on bool *)
HB.instance Definition _ := isZmodule.Build bool addbA addbC addFb addbb.

(* nmodType structure on nat *)
HB.instance Definition _ := isNmodule.Build nat addnA addnC add0n.

HB.instance Definition _ (V : nmodType) (x : V) :=
  isSemiAdditive.Build nat V (natmul x) (mulg0n x, mulgnDr x).

Lemma natg0E : 0 = 0%N. Proof. by []. Qed.
Lemma natgDE n m : n + m = (n + m)%N. Proof. by []. Qed.
Definition natgE := (natg0E, natgDE).

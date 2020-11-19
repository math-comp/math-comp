From mathcomp Require Import ssreflect ssrfun.
From Coq Require Export ssrbool.

(******************************************************************************)
(* Local additions:                                                           *)
(*      {pred T} == a type convertible to pred T but that presents the        *)
(*                  pred_sort coercion class.                                 *)
(*  PredType toP == the predType structure for toP : A -> pred T.             *)
(*    relpre f r == the preimage of r by f, simplifying to r (f x) (f y).     *)
(* --> These will become part of the core SSReflect library with Coq 8.11.    *)
(* This file also anticipates a v8.11 change in the definition of simpl_pred  *)
(* to T -> simpl_pred T. This change ensures that inE expands the definition  *)
(* of r : simpl_rel along with the \in, when rewriting in y \in r x.          *)
(*                                                                            *)
(* This file also anticipates v8.13 additions as well as a generalization in  *)
(* the statments of `homoRL_in`, `homoLR_in`, `homo_mono_in`, `monoLR_in`,    *)
(* monoRL_in, and can_mono_in.                                                *)
(******************************************************************************)

(******************)
(* v8.11 addtions *)
(******************)

Notation "{ 'pred' T }" := (pred_sort (predPredType T)) (at level 0,
  format "{ 'pred'  T }") : type_scope.

Lemma simpl_pred_sortE T (p : pred T) : (SimplPred p : {pred T}) =1 p.
Proof. by []. Qed.
Definition inE := (inE, simpl_pred_sortE).

Definition PredType : forall T pT, (pT -> pred T) -> predType T.
exact PredType || exact mkPredType.
Defined.
Arguments PredType [T pT] toP.

Definition simpl_rel T := T -> simpl_pred T.
Definition SimplRel {T} (r : rel T) : simpl_rel T := fun x => SimplPred (r x).
Coercion rel_of_simpl_rel T (sr : simpl_rel T) : rel T := sr.
Arguments rel_of_simpl_rel {T} sr x / y : rename.

(* Required to avoid an incompatible format warning with coq-8.12 *)
Reserved Notation "[ 'rel' x y : T | E ]" (at level 0, x ident, y ident,
  format "'[hv' [ 'rel'  x  y  :  T  | '/ '  E ] ']'").

Notation "[ 'rel' x y | E ]" := (SimplRel (fun x y => E%B)) (at level 0,
  x ident, y ident, format "'[hv' [ 'rel'  x  y  | '/ '  E ] ']'") : fun_scope.
Notation "[ 'rel' x y : T | E ]" := (SimplRel (fun x y : T => E%B)) 
  (only parsing) : fun_scope.
Notation "[ 'rel' x y 'in' A & B | E ]" :=
  [rel x y | (x \in A) && (y \in B) && E] (at level 0, x ident, y ident,
  format "'[hv' [ 'rel'  x  y  'in'  A  &  B  | '/ '  E ] ']'") : fun_scope.
Notation "[ 'rel' x y 'in' A & B ]" := [rel x y | (x \in A) && (y \in B)]
  (at level 0, x ident, y ident,
  format "'[hv' [ 'rel'  x  y  'in'  A  &  B ] ']'") : fun_scope.
Notation "[ 'rel' x y 'in' A | E ]" := [rel x y in A & A | E]
  (at level 0, x ident, y ident,
  format "'[hv' [ 'rel'  x  y  'in'  A  | '/ '  E ] ']'") : fun_scope.
Notation "[ 'rel' x y 'in' A ]" := [rel x y in A & A] (at level 0,
  x ident, y ident, format "'[hv' [ 'rel'  x  y  'in'  A ] ']'") : fun_scope.

Notation xrelpre := (fun f (r : rel _) x y => r (f x) (f y)).
Definition relpre {T rT} (f : T -> rT)  (r : rel rT) :=
  [rel x y | r (f x) (f y)].

(******************)
(* v8.13 addtions *)
(******************)

Section HomoMonoMorphismFlip.
Variables (aT rT : Type) (aR : rel aT) (rR : rel rT) (f : aT -> rT).
Variable (aD aD' : {pred aT}).

Lemma homo_sym : {homo f : x y / aR x y >-> rR x y} ->
  {homo f : y x / aR x y >-> rR x y}.
Proof. by move=> fR y x; apply: fR. Qed.

Lemma mono_sym : {mono f : x y / aR x y >-> rR x y} ->
  {mono f : y x / aR x y >-> rR x y}.
Proof. by move=> fR y x; apply: fR. Qed.

Lemma homo_sym_in : {in aD &, {homo f : x y / aR x y >-> rR x y}} ->
  {in aD &, {homo f : y x / aR x y >-> rR x y}}.
Proof. by move=> fR y x yD xD; apply: fR. Qed.

Lemma mono_sym_in : {in aD &, {mono f : x y / aR x y >-> rR x y}} ->
  {in aD &, {mono f : y x / aR x y >-> rR x y}}.
Proof. by move=> fR y x yD xD; apply: fR. Qed.

Lemma homo_sym_in11 : {in aD & aD', {homo f : x y / aR x y >-> rR x y}} ->
  {in aD' & aD, {homo f : y x / aR x y >-> rR x y}}.
Proof. by move=> fR y x yD xD; apply: fR. Qed.

Lemma mono_sym_in11 : {in aD & aD', {mono f : x y / aR x y >-> rR x y}} ->
  {in aD' & aD, {mono f : y x / aR x y >-> rR x y}}.
Proof. by move=> fR y x yD xD; apply: fR. Qed.

End HomoMonoMorphismFlip.
Arguments homo_sym {aT rT} [aR rR f].
Arguments mono_sym {aT rT} [aR rR f].
Arguments homo_sym_in {aT rT} [aR rR f aD].
Arguments mono_sym_in {aT rT} [aR rR f aD].
Arguments homo_sym_in11 {aT rT} [aR rR f aD aD'].
Arguments mono_sym_in11 {aT rT} [aR rR f aD aD'].

Section LocalGlobal.

Local Notation "{ 'all1' P }" := (forall x, P x : Prop) (at level 0).
Local Notation "{ 'all2' P }" := (forall x y, P x y : Prop) (at level 0).

Variables T1 T2 T3 : predArgType.
Variables (D1 : {pred T1}) (D2 : {pred T2}).
Variables (f : T1 -> T2) (h : T3).
Variable Q1 : (T1 -> T2) -> T1 -> Prop.
Variable Q1l : (T1 -> T2) -> T3 -> T1 -> Prop.
Variable Q2 : (T1 -> T2) -> T1 -> T1 -> Prop.
Let allQ1 f'' := {all1 Q1 f''}.
Let allQ1l f'' h' := {all1 Q1l f'' h'}.
Let allQ2 f'' := {all2 Q2 f''}.

Lemma in_on1P : {in D1, {on D2, allQ1 f}} <->
                {in [pred x in D1 | f x \in D2], allQ1 f}.
Proof.
split => allf x; have := allf x; rewrite inE => Q1f; first by case/andP.
by move=> ? ?; apply: Q1f; apply/andP.
Qed.

Lemma in_on1lP : {in D1, {on D2, allQ1l f & h}} <->
                {in [pred x in D1 | f x \in D2], allQ1l f h}.
Proof.
split => allf x; have := allf x; rewrite inE => Q1f; first by case/andP.
by move=> ? ?; apply: Q1f; apply/andP.
Qed.

Lemma in_on2P : {in D1 &, {on D2 &, allQ2 f}} <->
                {in [pred x in D1 | f x \in D2] &, allQ2 f}.
Proof.
split => allf x y; have := allf x y; rewrite !inE => Q2f.
  by move=> /andP[? ?] /andP[? ?]; apply: Q2f.
by move=> ? ? ? ?; apply: Q2f; apply/andP.
Qed.

Lemma on1W_in : {in D1, allQ1 f} -> {in D1, {on D2, allQ1 f}}.
Proof. by move=> D1f ? /D1f. Qed.

Lemma on1lW_in : {in D1, allQ1l f h} -> {in D1, {on D2, allQ1l f & h}}.
Proof. by move=> D1f ? /D1f. Qed.

Lemma on2W_in : {in D1 &, allQ2 f} -> {in D1 &, {on D2 &, allQ2 f}}.
Proof. by move=> D1f ? ? ? ? ? ?; apply: D1f. Qed.

Lemma in_on1W : allQ1 f -> {in D1, {on D2, allQ1 f}}.
Proof. by move=> allf ? ? ?; apply: allf. Qed.

Lemma in_on1lW : allQ1l f h -> {in D1, {on D2, allQ1l f & h}}.
Proof. by move=> allf ? ? ?; apply: allf. Qed.

Lemma in_on2W : allQ2 f -> {in D1 &, {on D2 &, allQ2 f}}.
Proof. by move=> allf ? ? ? ? ? ?; apply: allf. Qed.

Lemma on1S : (forall x, f x \in D2) -> {on D2, allQ1 f} -> allQ1 f.
Proof. by move=> ? fD1 ?; apply: fD1. Qed.

Lemma on1lS : (forall x, f x \in D2) -> {on D2, allQ1l f & h} -> allQ1l f h.
Proof. by move=> ? fD1 ?; apply: fD1. Qed.

Lemma on2S : (forall x, f x \in D2) -> {on D2 &, allQ2 f} -> allQ2 f.
Proof. by move=> ? fD1 ? ?; apply: fD1. Qed.

Lemma on1S_in : {homo f : x / x \in D1 >-> x \in D2} ->
  {in D1, {on D2, allQ1 f}} -> {in D1, allQ1 f}.
Proof. by move=> fD fD1 ? ?; apply/fD1/fD. Qed.

Lemma on1lS_in : {homo f : x / x \in D1 >-> x \in D2} ->
  {in D1, {on D2, allQ1l f & h}} -> {in D1, allQ1l f h}.
Proof. by move=> fD fD1 ? ?; apply/fD1/fD. Qed.

Lemma on2S_in : {homo f : x / x \in D1 >-> x \in D2} ->
  {in D1 &, {on D2 &, allQ2 f}} -> {in D1 &, allQ2 f}.
Proof. by move=> fD fD1 ? ? ? ?; apply: fD1 => //; apply: fD. Qed.

Lemma in_on1S : (forall x, f x \in D2) -> {in T1, {on D2, allQ1 f}} -> allQ1 f.
Proof. by move=> fD2 fD1 ?; apply: fD1. Qed.

Lemma in_on1lS : (forall x, f x \in D2) ->
  {in T1, {on D2, allQ1l f & h}} -> allQ1l f h.
Proof. by move=> fD2 fD1 ?; apply: fD1. Qed.

Lemma in_on2S : (forall x, f x \in D2) ->
  {in T1 &, {on D2 &, allQ2 f}} -> allQ2 f.
Proof. by move=> fD2 fD1 ? ?; apply: fD1. Qed.

End LocalGlobal.
Arguments in_on1P  {T1 T2 D1 D2 f Q1}.
Arguments in_on1lP {T1 T2 T3 D1 D2 f h Q1l}.
Arguments in_on2P  {T1 T2 D1 D2 f Q2}.
Arguments on1W_in  {T1 T2 D1} D2 {f Q1}.
Arguments on1lW_in {T1 T2 T3 D1} D2 {f h Q1l}.
Arguments on2W_in  {T1 T2 D1} D2 {f Q2}.
Arguments in_on1W  {T1 T2} D1 D2 {f Q1}.
Arguments in_on1lW {T1 T2 T3} D1 D2 {f h Q1l}.
Arguments in_on2W  {T1 T2} D1 D2 {f Q2}.
Arguments on1S     {T1 T2} D2 {f Q1}.
Arguments on1lS    {T1 T2 T3} D2 {f h Q1l}.
Arguments on2S     {T1 T2} D2 {f Q2}.
Arguments on1S_in  {T1 T2 D1} D2 {f Q1}.
Arguments on1lS_in {T1 T2 T3 D1} D2 {f h Q1l}.
Arguments on2S_in  {T1 T2 D1} D2 {f Q2}.
Arguments in_on1S  {T1 T2} D2 {f Q1}.
Arguments in_on1lS {T1 T2 T3} D2 {f h Q1l}.
Arguments in_on2S  {T1 T2} D2 {f Q2}.

Section CancelOn.

Variables (aT rT : predArgType) (aD : {pred aT}) (rD : {pred rT}).
Variables (f : aT -> rT) (g : rT -> aT).

Lemma onW_can : cancel g f -> {on aD, cancel g & f}. Proof. exact: on1lW. Qed.

Lemma onW_can_in : {in rD, cancel g f} -> {in rD, {on aD, cancel g & f}}.
Proof. exact: on1lW_in. Qed.

Lemma in_onW_can : cancel g f -> {in rD, {on aD, cancel g & f}}.
Proof. exact: in_on1lW. Qed.

Lemma onS_can : (forall x, g x \in aD) -> {on aD, cancel g & f} -> cancel g f.
Proof. exact: on1lS. Qed.

Lemma onS_can_in : {homo g : x / x \in rD >-> x \in aD} ->
  {in rD, {on aD, cancel g & f}} -> {in rD, cancel g f}.
Proof. exact: on1lS_in. Qed.

Lemma in_onS_can : (forall x, g x \in aD) ->
  {in rT, {on aD, cancel g & f}} -> cancel g f.
Proof. exact: in_on1lS. Qed.

End CancelOn.
Arguments onW_can {aT rT} aD {f g}.
Arguments onW_can_in {aT rT} aD {rD f g}.
Arguments in_onW_can {aT rT} aD rD {f g}.
Arguments onS_can {aT rT} aD {f g}.
Arguments onS_can_in {aT rT} aD {rD f g}.
Arguments in_onS_can {aT rT} aD {f g}.

Section MonoHomoMorphismTheory_in.

Variables (aT rT : predArgType) (aD : {pred aT}) (rD : {pred rT}).
Variables (f : aT -> rT) (g : rT -> aT) (aR : rel aT) (rR : rel rT).

Hypothesis fgK : {in rD, {on aD, cancel g & f}}.
Hypothesis mem_g : {homo g : x / x \in rD >-> x \in aD}.

Lemma homoRL_in :
    {in aD &, {homo f : x y / aR x y >-> rR x y}} ->
  {in rD & aD, forall x y, aR (g x) y -> rR x (f y)}.
Proof. by move=> Hf x y hx hy /Hf; rewrite fgK ?mem_g// ?inE; apply. Qed.

Lemma homoLR_in :
    {in aD &, {homo f : x y / aR x y >-> rR x y}} ->
  {in aD & rD, forall x y, aR x (g y) -> rR (f x) y}.
Proof. by move=> Hf x y hx hy /Hf; rewrite fgK ?mem_g// ?inE; apply. Qed.

Lemma homo_mono_in :
    {in aD &, {homo f : x y / aR x y >-> rR x y}} ->
    {in rD &, {homo g : x y / rR x y >-> aR x y}} ->
  {in rD &, {mono g : x y / rR x y >-> aR x y}}.
Proof.
move=> mf mg x y hx hy; case: (boolP (rR _ _))=> [/mg //|]; first exact.
by apply: contraNF=> /mf; rewrite !fgK ?mem_g//; apply.
Qed.

Lemma monoLR_in :
    {in aD &, {mono f : x y / aR x y >-> rR x y}} ->
  {in aD & rD, forall x y, rR (f x) y = aR x (g y)}.
Proof. by move=> mf x y hx hy; rewrite -{1}[y]fgK ?mem_g// mf ?mem_g. Qed.

Lemma monoRL_in :
    {in aD &, {mono f : x y / aR x y >-> rR x y}} ->
  {in rD & aD, forall x y, rR x (f y) = aR (g x) y}.
Proof. by move=> mf x y hx hy; rewrite -{1}[x]fgK ?mem_g// mf ?mem_g. Qed.

Lemma can_mono_in :
    {in aD &, {mono f : x y / aR x y >-> rR x y}} ->
  {in rD &, {mono g : x y / rR x y >-> aR x y}}.
Proof. by move=> mf x y hx hy; rewrite -mf ?mem_g// !fgK ?mem_g. Qed.

End MonoHomoMorphismTheory_in.
Arguments homoRL_in {aT rT aD rD f g aR rR}.
Arguments homoLR_in {aT rT aD rD f g aR rR}.
Arguments homo_mono_in {aT rT aD rD f g aR rR}.
Arguments monoLR_in {aT rT aD rD f g aR rR}.
Arguments monoRL_in {aT rT aD rD f g aR rR}.
Arguments can_mono_in {aT rT aD rD f g aR rR}.

Section inj_can_sym_in_on.
Variables (aT rT : predArgType) (aD : {pred aT}) (rD : {pred rT}).
Variables (f : aT -> rT) (g : rT -> aT).

Lemma inj_can_sym_in_on :
    {homo f : x / x \in aD >-> x \in rD} -> {in aD, {on rD, cancel f & g}} ->
  {in rD &, {on aD &, injective g}} -> {in rD, {on aD, cancel g & f}}.
Proof. by move=> fD fK gI x x_rD gx_aD; apply: gI; rewrite ?inE ?fK ?fD. Qed.

Lemma inj_can_sym_on : {in aD, cancel f g} ->
  {on aD &, injective g} -> {on aD, cancel g & f}.
Proof. by move=> fK gI x gx_aD; apply: gI; rewrite ?inE ?fK. Qed.

Lemma inj_can_sym_in : {homo f \o g : x / x \in rD} -> {on rD, cancel f & g} ->
  {in rD &, injective g} ->  {in rD, cancel g f}.
Proof. by move=> fgD fK gI x x_rD; apply: gI; rewrite ?fK ?fgD. Qed.

End inj_can_sym_in_on.
Arguments inj_can_sym_in_on {aT rT aD rD f g}.
Arguments inj_can_sym_on {aT rT aD f g}.
Arguments inj_can_sym_in {aT rT rD f g}.

(* additional contra lemmas involving [P,Q : Prop] *)

Section Contra.
Implicit Types (P Q : Prop) (b : bool).

Lemma contra_not P Q : (Q -> P) -> (~ P -> ~ Q). Proof. by auto. Qed.

Lemma contraPnot P Q : (Q -> ~ P) -> (P -> ~ Q). Proof. by auto. Qed.

Lemma contraTnot b P : (P -> ~~ b) -> (b -> ~ P).
Proof. by case: b; auto. Qed.

Lemma contraNnot P b : (P -> b) -> (~~ b -> ~ P).
Proof. rewrite -{1}[b]negbK; exact: contraTnot. Qed.

Lemma contraPT P b : (~~ b -> ~ P) -> P -> b.
Proof. by case: b => //= /(_ isT) nP /nP. Qed.

Lemma contra_notT P b : (~~ b -> P) -> ~ P -> b.
Proof. by case: b => //= /(_ isT) HP /(_ HP). Qed.

Lemma contra_notN P b : (b -> P) -> ~ P -> ~~ b.
Proof. rewrite -{1}[b]negbK; exact: contra_notT. Qed.

Lemma contraPN P b : (b -> ~ P) -> (P -> ~~ b).
Proof. by case: b => //=; move/(_ isT) => HP /HP. Qed.

Lemma contraFnot P b : (P -> b) -> b = false -> ~ P.
Proof. by case: b => //; auto. Qed.

Lemma contraPF P b : (b -> ~ P) -> P -> b = false.
Proof. by case: b => // /(_ isT). Qed.

Lemma contra_notF P b : (b -> P) -> ~ P -> b = false.
Proof. by case: b => // /(_ isT). Qed.
End Contra.

(******************)
(* v8.14 addtions *)
(******************)

Section in_sig.
Local Notation "{ 'all1' P }" := (forall x, P x : Prop) (at level 0).
Local Notation "{ 'all2' P }" := (forall x y, P x y : Prop) (at level 0).
Local Notation "{ 'all3' P }" := (forall x y z, P x y z : Prop) (at level 0).

Variables T1 T2 T3 : Type.
Variables (D1 : {pred T1}) (D2 : {pred T2})  (D3 : {pred T3}).
Variable P1 : T1 -> Prop.
Variable P11 : T1 -> T2 -> Prop.
Variable P111 : T1 -> T2 -> T3 -> Prop.
Variable P2 :  T1 -> T1 -> Prop.
Variable P3 :  T1 -> T1 -> T1 -> Prop.

Lemma in1_sig : {in D1, {all1 P1}} -> forall x : sig D1, P1 (sval x).
Proof. by move=> DP [x Dx]; have := DP _ Dx. Qed.

Lemma in11_sig : {in D1 & D2, {all2 P11}} ->
  forall (x : sig D1) (y : sig D2), P11 (sval x) (sval y).
Proof. by move=> DP [x Dx] [y Dy]; have := DP _ _ Dx Dy. Qed.

Lemma in111_sig : {in D1 & D2 & D3, {all3 P111}} ->
  forall (x : sig D1) (y : sig D2) (z : sig D3), P111 (sval x) (sval y) (sval z).
Proof. by move=> DP [x Dx] [y Dy] [z Dz]; have := DP _ _ _ Dx Dy Dz. Qed.

Lemma in2_sig : {in D1 &, {all2 P2}} -> forall x y : sig D1, P2 (sval x) (sval y).
Proof. by move=> DP [x Dx] [y Dy]; have := DP _ _ Dx Dy. Qed.

Lemma in3_sig : {in D1 & &, {all3 P3}} ->
   forall x y z : sig D1, P3 (sval x) (sval y) (sval z).
Proof. by move=> DP [x Dx] [y Dy] [z Dz]; have := DP _ _ _ Dx Dy Dz. Qed.

End in_sig.
Arguments in1_sig {T1 D1 P1}.
Arguments in11_sig {T1 T2 D1 D2 P11}.
Arguments in111_sig {T1 T2 T3 D1 D2 D3 P111}.
Arguments in2_sig {T1 D1 P2}.
Arguments in3_sig {T1 D1 P3}.

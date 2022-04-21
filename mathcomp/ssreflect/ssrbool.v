From mathcomp Require Import ssreflect ssrfun.
From Coq Require Export ssrbool.

(* 8.11 addition in Coq but renamed *)
#[deprecated(since="mathcomp 1.15", note="Use rel_of_simpl instead.")]
Notation rel_of_simpl_rel := rel_of_simpl.

(******************)
(* v8.14 addtions *)
(******************)

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
split => allf x; have /[!inE] Q1f := allf x; first by case/andP.
by move=> ? ?; apply: Q1f; apply/andP.
Qed.

Lemma in_on1lP : {in D1, {on D2, allQ1l f & h}} <->
                {in [pred x in D1 | f x \in D2], allQ1l f h}.
Proof.
split => allf x; have /[!inE] Q1f := allf x; first by case/andP.
by move=> ? ?; apply: Q1f; apply/andP.
Qed.

Lemma in_on2P : {in D1 &, {on D2 &, allQ2 f}} <->
                {in [pred x in D1 | f x \in D2] &, allQ2 f}.
Proof.
split => allf x y; have /[!inE] Q2f := allf x y.
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

Section in_sig.
Local Notation "{ 'all1' P }" := (forall x, P x : Prop) (at level 0).
Local Notation "{ 'all2' P }" := (forall x y, P x y : Prop) (at level 0).
Local Notation "{ 'all3' P }" := (forall x y z, P x y z : Prop) (at level 0).

Variables T1 T2 T3 : Type.
Variables (D1 : {pred T1}) (D2 : {pred T2})  (D3 : {pred T3}).
Variable P1 : T1 -> Prop.
Variable P2 : T1 -> T2 -> Prop.
Variable P3 : T1 -> T2 -> T3 -> Prop.

Lemma in1_sig : {in D1, {all1 P1}} -> forall x : sig D1, P1 (sval x).
Proof. by move=> DP [x Dx]; have := DP _ Dx. Qed.

Lemma in2_sig : {in D1 & D2, {all2 P2}} ->
  forall (x : sig D1) (y : sig D2), P2 (sval x) (sval y).
Proof. by move=> DP [x Dx] [y Dy]; have := DP _ _ Dx Dy. Qed.

Lemma in3_sig : {in D1 & D2 & D3, {all3 P3}} ->
  forall (x : sig D1) (y : sig D2) (z : sig D3), P3 (sval x) (sval y) (sval z).
Proof. by move=> DP [x Dx] [y Dy] [z Dz]; have := DP _ _ _ Dx Dy Dz. Qed.

End in_sig.
Arguments in1_sig {T1 D1 P1}.
Arguments in2_sig {T1 T2 D1 D2 P2}.
Arguments in3_sig {T1 T2 T3 D1 D2 D3 P3}.

(******************)
(* v8.15 addtions *)
(******************)

Section ReflectCombinators.

Variables (P Q : Prop) (p q : bool).

Hypothesis rP : reflect P p.
Hypothesis rQ : reflect Q q.

Lemma negPP : reflect (~ P) (~~ p).
Proof. by apply:(iffP negP); apply: contra_not => /rP. Qed.

Lemma andPP : reflect (P /\ Q) (p && q).
Proof. by apply: (iffP andP) => -[/rP ? /rQ ?]. Qed.

Lemma orPP : reflect (P \/ Q) (p || q).
Proof. by apply: (iffP orP) => -[/rP ?|/rQ ?]; tauto. Qed.

Lemma implyPP : reflect (P -> Q) (p ==> q).
Proof. by apply: (iffP implyP) => pq /rP /pq /rQ. Qed.

End ReflectCombinators.
Arguments negPP {P p}.
Arguments andPP {P Q p q}.
Arguments orPP {P Q p q}.
Arguments implyPP {P Q p q}.
Prenex Implicits negPP andPP orPP implyPP.

(******************)
(* v8.16 addtions *)
(******************)

Lemma mono1W_in (aT rT : predArgType) (f : aT -> rT) (aD : {pred aT})
    (aP : pred aT) (rP : pred rT) :
  {in aD, {mono f : x / aP x >-> rP x}} ->
  {in aD, {homo f : x / aP x >-> rP x}}.
Proof. by move=> fP x xD xP; rewrite fP. Qed.
Arguments mono1W_in [aT rT f aD aP rP].

#[deprecated(since="mathcomp 1.14.0", note="Use mono1W_in instead.")]
Notation mono2W_in := mono1W_in.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma all_sig2_cond {I T} (C : pred I) P Q :
    T -> (forall x, C x -> {y : T | P x y & Q x y}) ->
  {f : I -> T | forall x, C x -> P x (f x) & forall x, C x -> Q x (f x)}.
Proof.
by move=> /all_sig_cond/[apply]-[f Pf]; exists f => i Di; have [] := Pf i Di.
Qed.

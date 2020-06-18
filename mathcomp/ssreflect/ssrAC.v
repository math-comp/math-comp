From HB Require Import structures.
Require Import BinPos BinNat.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq bigop.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(************************************************************************)
(* Small Scale Rewriting using Associativity and Commutativity          *)
(*                                                                      *)
(* Rewriting with AC (not modulo AC), using a small scale command.      *)
(* Replaces opA, opC, opAC, opCA, ... and any combinations of them      *)
(*                                                                      *)
(* Usage :                                                              *)
(*   rewrite [pattern](AC patternshape reordering)                      *)
(*   rewrite [pattern](ACl reordering)                                  *)
(*   rewrite [pattern](ACof reordering reordering)                      *)
(*   rewrite [pattern]op.[AC patternshape reordering]                   *)
(*   rewrite [pattern]op.[ACl reordering]                               *)
(*   rewrite [pattern]op.[ACof reordering reordering]                   *)
(*                                                                      *)
(* - if op is specified, the rule is specialized to op                  *)
(*   otherwise,          the head symbol is a generic comm_law          *)
(*                       and the rewrite might be less efficient        *)
(*   NOTE because of a bug in Coq's notations coq/coq#8190              *)
(*        op must not contain any hole.                                 *)
(*        *%R.[AC p s] currently does not work because of that          *)
(*        (@GRing.mul R).[AC p s] must be used instead                  *)
(*                                                                      *)
(* - pattern is optional, as usual, but must be used to select the      *)
(*   appropriate operator in case of ambiguity such an operator must    *)
(*   have a canonical Monoid.com_law structure                          *)
(*   (additions, multiplications, conjuction and disjunction do)        *)
(*                                                                      *)
(* - patternshape is expressed using the syntax                         *)
(*      p := n | p * p'                                                 *)
(*      where "*" is purely formal                                      *)
(*        and n > 0 is the number of left associated symbols            *)
(*   examples of pattern shapes:                                        *)
(*   + 4 represents (n * m * p * q)                                     *)
(*   + (1*2) represents (n * (m * p))                                   *)
(*                                                                      *)
(* - reordering is expressed using the syntax                           *)
(*     s := n | s * s'                                                  *)
(*   where "*" is purely formal and n > 0 is the position in the LHS    *)
(*   positions start at 1 !                                             *)
(*                                                                      *)
(* If the ACl variant is used, the patternshape defaults to the         *)
(* pattern fully associated to the left i.e. n i.e (x * y * ...)        *)
(*                                                                      *)
(* Examples of reorderings:                                             *)
(* - ACl ((1*2)*3) is the identity (and will fail with error message)   *)
(* - opAC == op.[ACl (1*3)*2] == op.[AC 3 ((1*3)*2)]                    *)
(* - opCA == op.[AC (2*1) (1*2*3)]                                      *)
(* - opACA == op.[AC (2*2) ((1*3)*(2*4))]                               *)
(* - rewrite opAC -opA == rewrite op.[ACl 1*(3*2)]                      *)
(* ...                                                                  *)
(************************************************************************)

Declare Scope AC_scope.

Delimit Scope AC_scope with AC.

Definition change_type ty ty' (x : ty) (strategy : ty = ty') : ty' :=
 ecast ty ty strategy x.
Notation simplrefl := (ltac: (simpl; reflexivity)) (only parsing).
Notation cbvrefl := (ltac: (cbv; reflexivity)) (only parsing).
Notation vmrefl := (ltac: (vm_compute; reflexivity)) (only parsing).

Module AC.

HB.instance Definition _ := HasDecEq.Build positive
  (fun _ _ => equivP idP (Pos.eqb_eq _ _)).

Inductive syntax := Leaf of positive | Op of syntax & syntax.
Coercion serial := (fix loop (acc : seq positive) (s : syntax) :=
   match s with
   | Leaf n => n :: acc
   | Op s s' => (loop^~ s (loop^~ s' acc))
   end) [::].

Lemma serial_Op s1 s2 : Op s1 s2 = s1 ++ s2 :> seq _.
Proof.
rewrite /serial; set loop := (X in X [::]); rewrite -/loop.
elim: s1 (loop [::] s2) => [n|s11 IHs1 s12 IHs2] //= l.
by rewrite IHs1 [in RHS]IHs1 IHs2 catA.
Qed.

Definition Leaf_of_nat n := Leaf ((pos_of_nat n n) - 1)%positive.

Module Import Syntax.
Bind Scope AC_scope with syntax.
Number Notation positive Pos.of_num_int Pos.to_num_uint : AC_scope.
Coercion Leaf : positive >-> syntax.
Coercion Leaf_of_nat : nat >-> syntax.
Notation "x * y" := (Op x%AC y%AC) : AC_scope.
End Syntax.

Definition pattern (s : syntax) := ((fix loop n s :=
  match s with
  | Leaf 1%positive => (Leaf n, Pos.succ n)
  | Leaf m => Pos.iter (fun oi => (Op oi.1 (Leaf oi.2), Pos.succ oi.2))
                       (Leaf n, Pos.succ n) (m - 1)%positive
  | Op s s' => let: (p, n') := loop n s in
               let: (p', n'') := loop n' s' in
               (Op p p', n'')
  end) 1%positive s).1.

Section eval.
Variables (T : Type) (idx : T) (op : T -> T -> T).
Inductive env := Empty | ENode of T & env & env.
Definition pos := fix loop (e : env) p {struct e} :=
  match e, p with
 | ENode t _ _, 1%positive => t
 | ENode t e _, (p~0)%positive => loop e p
 | ENode t _ e, (p~1)%positive => loop e p
 | _, _ => idx
end.

Definition set_pos (f : T -> T) := fix loop e p {struct p} :=
  match e, p with
 | ENode t e e', 1%positive => ENode (f t) e e'
 | ENode t e e', (p~0)%positive => ENode t (loop e p) e'
 | ENode t e e', (p~1)%positive => ENode t e (loop e' p)
 | Empty, 1%positive => ENode (f idx) Empty Empty
 | Empty, (p~0)%positive => ENode idx (loop Empty p) Empty
 | Empty, (p~1)%positive => ENode idx Empty (loop Empty p)
 end.

Lemma pos_set_pos (f : T -> T) e (p p' : positive) :
  pos (set_pos f e p) p' = if p == p' then f (pos e p) else pos e p'.
Proof. by elim: p e p' => [p IHp|p IHp|] [|???] [?|?|]//=; rewrite IHp. Qed.

Fixpoint unzip z (e : env) : env := match z with
 | [::] => e
 | (x, inl e') :: z' => unzip z' (ENode x e' e)
 | (x, inr e') :: z' => unzip z' (ENode x e e')
end.

Definition set_pos_trec (f : T -> T) := fix loop z e p {struct p} :=
  match e, p with
 | ENode t e e', 1%positive => unzip z (ENode (f t) e e')
 | ENode t e e', (p~0)%positive => loop ((t, inr e') :: z) e p
 | ENode t e e', (p~1)%positive => loop ((t, inl e) :: z) e' p
 | Empty, 1%positive => unzip z (ENode (f idx) Empty Empty)
 | Empty, (p~0)%positive => loop ((idx, (inr Empty)) :: z) Empty p
 | Empty, (p~1)%positive => loop ((idx, (inl Empty)) :: z) Empty p
 end.

Lemma set_pos_trecE f z e p : set_pos_trec f z e p = unzip z (set_pos f e p).
Proof. by elim: p e z => [p IHp|p IHp|] [|???] [|[??]?] //=; rewrite ?IHp. Qed.

Definition eval (e : env) := fix loop (s : syntax) :=
match s with
  | Leaf n => pos e n
  | Op s s' => op (loop s) (loop s')
end.
End eval.
Arguments Empty {T}.

Definition content := (fix loop (acc : env N) s :=
  match s with
  | Leaf n => set_pos_trec 0%num N.succ [::] acc n
  | Op s s' => loop (loop acc s') s
  end) Empty.

Lemma count_memE x (t : syntax) : count_mem x t = pos 0%num (content t) x.
Proof.
rewrite /content; set loop := (X in X Empty); rewrite -/loop.
rewrite -[LHS]addn0; have <- : pos 0%num Empty x = 0 :> nat by elim: x.
elim: t Empty => [n|s IHs s' IHs'] e //=; last first.
  by rewrite serial_Op count_cat -addnA IHs' IHs.
rewrite ?addn0 set_pos_trecE pos_set_pos; case: (altP eqP) => [->|] //=.
by rewrite -N.add_1_l nat_of_add_bin //=.
Qed.

Definition cforall N T : env N -> (env T -> Type) -> Type := env_rect (@^~ Empty)
  (fun _ e IHe e' IHe' R => forall x, IHe (fun xe => IHe' (R \o ENode x xe))).

Lemma cforallP N T R : (forall e : env T, R e) -> forall (e : env N), cforall e R.
Proof.
move=> Re e; elim: e R Re => [|? e /= IHe e' IHe' ?? x] //=.
by apply: IHe => ?; apply: IHe' => /=.
Qed.

Section eq_eval.
Variables (T : Type) (idx : T) (op : Monoid.com_law idx).

Lemma proof (p s : syntax) : content p = content s ->
  forall env, eval idx op env p = eval idx op env s.
Proof.
suff evalE env t : eval idx op env t = \big[op/idx]_(i <- t) (pos idx env i).
  move=> cps e; rewrite !evalE; apply: perm_big.
  by apply/allP => x _ /=; rewrite !count_memE cps.
elim: t => //= [n|t -> t' ->]; last by rewrite serial_Op big_cat.
by rewrite big_cons big_nil Monoid.mulm1.
Qed.

Definition direct p s ps := cforallP (@proof p s ps) (content p).

End eq_eval.

Module Exports.
Export AC.Syntax.
End Exports.
End AC.
Export AC.Exports.

Notation AC_check_pattern :=
  (ltac: (match goal with
    |- AC.content ?pat = AC.content ?ord =>
      let pat' := fresh "pat" in let pat' := eval compute in pat in
      tryif unify pat' ord then
           fail 1 "AC: equality between" pat
                  "and" ord "is trivial, cannot progress"
      else tryif vm_compute; reflexivity then idtac
      else fail 2 "AC: mismatch between shape" pat "=" pat' "and reordering" ord
    | |- ?G => fail 3 "AC: no pattern to check" G
  end))
  (only parsing).

Notation opACof law p s :=
((fun T idx op assoc lid rid comm => (change_type (@AC.direct T idx
   (@Monoid.ComLaw _ _ (@Monoid.Law _ idx op assoc lid rid) comm)
   p%AC s%AC AC_check_pattern) cbvrefl)) _ _ law
(Monoid.mulmA _) (Monoid.mul1m _) (Monoid.mulm1 _) (Monoid.mulmC _))
(only parsing).

Notation opAC op  p s := (opACof op (AC.pattern p%AC) s%AC) (only parsing).
Notation opACl op s := (opAC op (AC.Leaf_of_nat (size (AC.serial s%AC))) s%AC)
  (only parsing).

Notation "op .[ 'ACof' p s ]" := (opACof op p%AC s%AC)
  (at level 2, p at level 1, left associativity, only parsing).
Notation "op .[ 'AC' p s ]" := (opAC op p%AC s%AC)
  (at level 2, p at level 1, left associativity, only parsing).
Notation "op .[ 'ACl' s ]" := (opACl op s%AC)
  (at level 2, left associativity, only parsing).

Notation AC_strategy :=
  (ltac: (cbv -[Monoid.com_operator Monoid.operator]; reflexivity))
  (only parsing).
Notation ACof p s := (change_type
  (@AC.direct _ _ _  p%AC s%AC AC_check_pattern) AC_strategy)
  (only parsing).
Notation AC p s := (ACof (AC.pattern p%AC) s%AC) (only parsing).
Notation ACl s := (AC (AC.Leaf_of_nat (size (AC.serial s%AC))) s%AC)
  (only parsing).

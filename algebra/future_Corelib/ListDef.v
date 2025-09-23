(* TODO: remove this file when requiring Rocq >= 9.2
   and use the identical file in Corelib instead *)

From Corelib Require Export ListDef.

#[local] Set Implicit Arguments.

Fixpoint rev_append A (l l' : list A) : list A :=
  match l with
    | nil => l'
    | a :: l => rev_append l (a :: l')
  end.

Section Fold_Left_Recursor.
  Variables (A : Type) (B : Type).
  Variable f : A -> B -> A.

  Fixpoint fold_left (l:list B) (a0:A) : A :=
    match l with
      | nil => a0
      | b :: l => fold_left l (f a0 b)
    end.

End Fold_Left_Recursor.

Section Fold_Right_Recursor.

  Variables (A : Type) (B : Type).
  Variable f : B -> A -> A.
  Variable a0 : A.

  Fixpoint fold_right (l:list B) : A :=
    match l with
      | nil => a0
      | b :: l => f b (fold_right l)
    end.

End Fold_Right_Recursor.

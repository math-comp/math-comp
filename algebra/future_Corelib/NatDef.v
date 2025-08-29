(* TODO: remove this file when requiring Rocq >= 9.2
   and use the identical file in Corelib instead *)

From mathcomp Require Export PosDef.
From Corelib Require Export NatDef.

#[local] Set Implicit Arguments.

Module N.
Export N.
(** ** Successor *)

Definition succ n :=
  match n with
  | N0 => Npos xH
  | Npos p => Npos (Pos.succ p)
  end.

(** ** Addition *)

Definition add n m :=
  match n, m with
  | N0, _ => m
  | _, N0 => n
  | Npos p, Npos q => Npos (Pos.add p q)
  end.

(** Multiplication *)

Definition mul n m :=
  match n, m with
  | N0, _ => N0
  | _, N0 => N0
  | Npos p, Npos q => Npos (Pos.mul p q)
  end.

(** Boolean equality and comparison *)

Definition eqb n m :=
  match n, m with
    | N0, N0 => true
    | Npos p, Npos q => Pos.eqb p q
    | _, _ => false
  end.

(** Translation from [N] to [nat] and back. *)

Definition to_nat (a : N) :=
  match a with
    | N0 => O
    | Npos p => Pos.to_nat p
  end.

(** Conversion with a decimal representation for printing/parsing *)

Definition of_uint (d:Decimal.uint) := Pos.of_uint d.

Definition of_hex_uint (d:Hexadecimal.uint) := Pos.of_hex_uint d.

Definition of_num_uint (d:Number.uint) :=
  match d with
  | Number.UIntDecimal d => of_uint d
  | Number.UIntHexadecimal d => of_hex_uint d
  end.
End N.

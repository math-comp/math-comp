(* TODO: remove this file when requiring Rocq >= 9.2
   and use the identical file in Corelib instead *)

From Corelib Require Export PosDef.

Module Pos.
Export Pos.

(** ** Predecessor *)

Definition pred x :=
  match x with
    | xI p => xO p
    | xO p => pred_double p
    | xH => xH
  end.

(** ** Conversion with a decimal representation for printing/parsing *)

#[local] Notation ten := (1~0~1~0)%positive.

Fixpoint of_uint_acc (d:Decimal.uint)(acc:positive) :=
  match d with
  | Decimal.Nil => acc
  | Decimal.D0 l => of_uint_acc l (mul ten acc)
  | Decimal.D1 l => of_uint_acc l (add 1 (mul ten acc))
  | Decimal.D2 l => of_uint_acc l (add 1~0 (mul ten acc))
  | Decimal.D3 l => of_uint_acc l (add 1~1 (mul ten acc))
  | Decimal.D4 l => of_uint_acc l (add 1~0~0 (mul ten acc))
  | Decimal.D5 l => of_uint_acc l (add 1~0~1 (mul ten acc))
  | Decimal.D6 l => of_uint_acc l (add 1~1~0 (mul ten acc))
  | Decimal.D7 l => of_uint_acc l (add 1~1~1 (mul ten acc))
  | Decimal.D8 l => of_uint_acc l (add 1~0~0~0 (mul ten acc))
  | Decimal.D9 l => of_uint_acc l (add 1~0~0~1 (mul ten acc))
  end.

Fixpoint of_uint (d:Decimal.uint) : N :=
  match d with
  | Decimal.Nil => N0
  | Decimal.D0 l => of_uint l
  | Decimal.D1 l => Npos (of_uint_acc l 1)
  | Decimal.D2 l => Npos (of_uint_acc l 1~0)
  | Decimal.D3 l => Npos (of_uint_acc l 1~1)
  | Decimal.D4 l => Npos (of_uint_acc l 1~0~0)
  | Decimal.D5 l => Npos (of_uint_acc l 1~0~1)
  | Decimal.D6 l => Npos (of_uint_acc l 1~1~0)
  | Decimal.D7 l => Npos (of_uint_acc l 1~1~1)
  | Decimal.D8 l => Npos (of_uint_acc l 1~0~0~0)
  | Decimal.D9 l => Npos (of_uint_acc l 1~0~0~1)
  end.

#[local] Notation sixteen := (1~0~0~0~0)%positive.

Fixpoint of_hex_uint_acc (d:Hexadecimal.uint)(acc:positive) :=
  match d with
  | Hexadecimal.Nil => acc
  | Hexadecimal.D0 l => of_hex_uint_acc l (mul sixteen acc)
  | Hexadecimal.D1 l => of_hex_uint_acc l (add 1 (mul sixteen acc))
  | Hexadecimal.D2 l => of_hex_uint_acc l (add 1~0 (mul sixteen acc))
  | Hexadecimal.D3 l => of_hex_uint_acc l (add 1~1 (mul sixteen acc))
  | Hexadecimal.D4 l => of_hex_uint_acc l (add 1~0~0 (mul sixteen acc))
  | Hexadecimal.D5 l => of_hex_uint_acc l (add 1~0~1 (mul sixteen acc))
  | Hexadecimal.D6 l => of_hex_uint_acc l (add 1~1~0 (mul sixteen acc))
  | Hexadecimal.D7 l => of_hex_uint_acc l (add 1~1~1 (mul sixteen acc))
  | Hexadecimal.D8 l => of_hex_uint_acc l (add 1~0~0~0 (mul sixteen acc))
  | Hexadecimal.D9 l => of_hex_uint_acc l (add 1~0~0~1 (mul sixteen acc))
  | Hexadecimal.Da l => of_hex_uint_acc l (add 1~0~1~0 (mul sixteen acc))
  | Hexadecimal.Db l => of_hex_uint_acc l (add 1~0~1~1 (mul sixteen acc))
  | Hexadecimal.Dc l => of_hex_uint_acc l (add 1~1~0~0 (mul sixteen acc))
  | Hexadecimal.Dd l => of_hex_uint_acc l (add 1~1~0~1 (mul sixteen acc))
  | Hexadecimal.De l => of_hex_uint_acc l (add 1~1~1~0 (mul sixteen acc))
  | Hexadecimal.Df l => of_hex_uint_acc l (add 1~1~1~1 (mul sixteen acc))
  end.

Fixpoint of_hex_uint (d:Hexadecimal.uint) : N :=
  match d with
  | Hexadecimal.Nil => N0
  | Hexadecimal.D0 l => of_hex_uint l
  | Hexadecimal.D1 l => Npos (of_hex_uint_acc l 1)
  | Hexadecimal.D2 l => Npos (of_hex_uint_acc l 1~0)
  | Hexadecimal.D3 l => Npos (of_hex_uint_acc l 1~1)
  | Hexadecimal.D4 l => Npos (of_hex_uint_acc l 1~0~0)
  | Hexadecimal.D5 l => Npos (of_hex_uint_acc l 1~0~1)
  | Hexadecimal.D6 l => Npos (of_hex_uint_acc l 1~1~0)
  | Hexadecimal.D7 l => Npos (of_hex_uint_acc l 1~1~1)
  | Hexadecimal.D8 l => Npos (of_hex_uint_acc l 1~0~0~0)
  | Hexadecimal.D9 l => Npos (of_hex_uint_acc l 1~0~0~1)
  | Hexadecimal.Da l => Npos (of_hex_uint_acc l 1~0~1~0)
  | Hexadecimal.Db l => Npos (of_hex_uint_acc l 1~0~1~1)
  | Hexadecimal.Dc l => Npos (of_hex_uint_acc l 1~1~0~0)
  | Hexadecimal.Dd l => Npos (of_hex_uint_acc l 1~1~0~1)
  | Hexadecimal.De l => Npos (of_hex_uint_acc l 1~1~1~0)
  | Hexadecimal.Df l => Npos (of_hex_uint_acc l 1~1~1~1)
  end.

End Pos.

From mathcomp Require Export orderedzmod.
From mathcomp Require Export numdomain.
From mathcomp Require Export numfield.

(******************************************************************************)
(*                            Number structures                               *)
(*                                                                            *)
(* The files in this directory define classes to manipulate number            *)
(* structures, i.e., structures with an order and a norm. To use these files, *)
(* insert:                                                                    *)
(* "From mathcomp Require Import numeric_hierarchy."                          *)
(* at the top your development and                                            *)
(* "Import Num.Theory."                                                       *)
(* before your scripts.                                                       *)
(*                                                                            *)
(* In addition, you can insert                                                *)
(* "Import Num.Def."                                                          *)
(* before your scripts to enjoy shorter notations, e.g.:                      *)
(* - minr instead of Num.min,                                                 *)
(* - lerif instead of Num.leif,                                               *)
(* - conjC instead of Num.conj, etc.                                          *)
(*                                                                            *)
(******************************************************************************)

Module Num.
Export orderedzmod.Num.
Export numdomain.Num.
Export numfield.Num.

Module Theory.
Export Num.Theory.
End Theory.

Module Def.
Export Num.Def.
End Def.

End Num.

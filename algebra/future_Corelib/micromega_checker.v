(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*                                                                      *)
(* Micromega: A reflexive tactic using the Positivstellensatz           *)
(*                                                                      *)
(*  Frédéric Besson (Irisa/Inria)                                       *)
(*                                                                      *)
(************************************************************************)

(* TODO: remove this file when requiring Rocq >= 9.2
   and use the identical file in Corelib instead *)

(** This file provides the computational part (checker) of the micromega
tactics. This checker uses the reified formula to be proved
(see micromega_formula.v) and a witness provided, from the formula,
by the micromega OCaml plugin (see micromega_witness.v for the type).
One can prove that if the checker returns true, then the formula holds.
Comments below give indications on how that proof should go.
See test-suite/micromega/witness_tactics.v for an example. *)

From mathcomp Require Import ListDef.
From Corelib Require Import BinNums PosDef IntDef.
From mathcomp Require Import RatDef.
From mathcomp Require Import micromega_formula micromega_witness.

Set Implicit Arguments.

(** ** A few utility functions
Essentially copied from ssrfun, should probably go in Corelib *)
Definition apply_option aT rT (f : aT -> rT) x u :=
  match u with Some y => f y | None => x end.
Definition bind_option aT rT (f : aT -> option rT) := apply_option f None.
Definition map_option aT rT (f : aT -> rT) := bind_option (fun x => Some (f x)).
Definition bind_option2 aT a'T rT (f : aT -> a'T -> option rT) o o' :=
  bind_option (fun o => bind_option (f o) o') o.
Definition map_option2 aT a'T rT (f : aT -> a'T -> rT) :=
  bind_option2 (fun x y => Some (f x y)).

(** * Basic arithmetic operations on Horner polynomials [Pol]

One can prove that an eval function [Peval] commutes with
each operation, e.g., [Peval l (Padd P P') = Peval l P + Peval l P'] *)
Section PolOps.

(** Coefficients *)
Variable (C : Type) (cO cI : C) (cadd cmul csub : C -> C -> C) (copp : C -> C).
Variable ceqb : C -> C -> bool.

Implicit Type P : Pol C.

(** Equality *)
Fixpoint Peq P P' {struct P'} : bool :=
  match P, P' with
  | Pc c, Pc c' => ceqb c c'
  | Pinj j Q, Pinj j' Q' =>
      match Pos.compare j j' with
      | Eq => Peq Q Q'
      | _ => false
      end
  | PX P i Q, PX P' i' Q' =>
      match Pos.compare i i' with
      | Eq => if Peq P P' then Peq Q Q' else false
      | _ => false
      end
  | _, _ => false
  end.

(** Constructors *)

Definition P0 := Pc cO.
Definition P1 := Pc cI.

Definition mkPinj j P :=
  match P with
  | Pc _ => P
  | Pinj j' Q => Pinj (Pos.add j j') Q
  | _ => Pinj j P
  end.

Definition mkPinj_pred j P :=
  match j with
  | xH => P
  | xO j => Pinj (Pos.pred_double j) P
  | xI j => Pinj (xO j) P
  end.

Definition mkX j := mkPinj_pred j (PX P1 1 P0).

Definition mkPX P i Q :=
  match P with
  | Pc c => if ceqb c cO then mkPinj xH Q else PX P i Q
  | Pinj _ _ => PX P i Q
  | PX P' i' Q' => if Peq Q' P0 then PX P' (Pos.add i' i) Q else PX P i Q
  end.

(** Opposite *)
Fixpoint Popp P : Pol C :=
  match P with
  | Pc c => Pc (copp c)
  | Pinj j Q => Pinj j (Popp Q)
  | PX P i Q => PX (Popp P) i (Popp Q)
  end.

(** Addition and subtraction *)

Fixpoint PaddC P c : Pol C :=
  match P with
  | Pc c1 => Pc (cadd c1 c)
  | Pinj j Q => Pinj j (PaddC Q c)
  | PX P i Q => PX P i (PaddC Q c)
  end.

Fixpoint PsubC P c : Pol C :=
  match P with
  | Pc c1 => Pc (csub c1 c)
  | Pinj j Q => Pinj j (PsubC Q c)
  | PX P i Q => PX P i (PsubC Q c)
  end.

Section PopI.
Variable Pop : Pol C -> Pol C -> Pol C.
Variable Q : Pol C.

(** [P + Pinj j Q], assuming [Pop . Q] is [. + Q] *)
Fixpoint PaddI (j : positive) P : Pol C :=
  match P with
  | Pc c => mkPinj j (PaddC Q c)
  | Pinj j' Q' =>
      match Z.pos_sub j' j with
      | Zpos k =>  mkPinj j (Pop (Pinj k Q') Q)
      | Z0 => mkPinj j (Pop Q' Q)
      | Zneg k => mkPinj j' (PaddI k Q')
      end
  | PX P i Q' =>
      match j with
      | xH => PX P i (Pop Q' Q)
      | xO j => PX P i (PaddI (Pos.pred_double j) Q')
      | xI j => PX P i (PaddI (xO j) Q')
      end
  end.

(** [P - Pinj j Q], assuming [Pop . Q] is [. - Q] *)
Fixpoint PsubI (j : positive) P : Pol C :=
  match P with
  | Pc c => mkPinj j (PaddC (Popp Q) c)
  | Pinj j' Q' =>
      match Z.pos_sub j' j with
      | Zpos k =>  mkPinj j (Pop (Pinj k Q') Q)
      | Z0 => mkPinj j (Pop Q' Q)
      | Zneg k => mkPinj j' (PsubI k Q')
      end
  | PX P i Q' =>
      match j with
      | xH => PX P i (Pop Q' Q)
      | xO j => PX P i (PsubI (Pos.pred_double j) Q')
      | xI j => PX P i (PsubI (xO j) Q')
      end
  end.

Variable P' : Pol C.

(** [P + PX P' i' P0], assumin [Pop . P'] is [. + P'] *)
Fixpoint PaddX (i' : positive) P : Pol C :=
  match P with
  | Pc c => PX P' i' P
  | Pinj j Q' =>
      match j with
      | xH =>  PX P' i' Q'
      | xO j => PX P' i' (Pinj (Pos.pred_double j) Q')
      | xI j => PX P' i' (Pinj (xO j) Q')
      end
  | PX P i Q' =>
      match Z.pos_sub i i' with
      | Zpos k => mkPX (Pop (PX P k P0) P') i' Q'
      | Z0 => mkPX (Pop P P') i Q'
      | Zneg k => mkPX (PaddX k P) i Q'
      end
  end.

(** [P - PX P' i' P0], assumin [Pop . P'] is [. - P'] *)
Fixpoint PsubX (i' : positive) P : Pol C :=
  match P with
  | Pc c => PX (Popp P') i' P
  | Pinj j Q' =>
      match j with
      | xH =>  PX (Popp P') i' Q'
      | xO j => PX (Popp P') i' (Pinj (Pos.pred_double j) Q')
      | xI j => PX (Popp P') i' (Pinj (xO j) Q')
      end
  | PX P i Q' =>
      match Z.pos_sub i i' with
      | Zpos k => mkPX (Pop (PX P k P0) P') i' Q'
      | Z0 => mkPX (Pop P P') i Q'
      | Zneg k => mkPX (PsubX k P) i Q'
      end
  end.
End PopI.

Fixpoint Padd P P' {struct P'} : Pol C :=
  match P' with
  | Pc c' => PaddC P c'
  | Pinj j' Q' => PaddI Padd Q' j' P
  | PX P' i' Q' =>
      match P with
      | Pc c => PX P' i' (PaddC Q' c)
      | Pinj j Q =>
          match j with
          | xH => PX P' i' (Padd Q Q')
          | xO j => PX P' i' (Padd (Pinj (Pos.pred_double j) Q) Q')
          | xI j => PX P' i' (Padd (Pinj (xO j) Q) Q')
          end
      | PX P i Q =>
          match Z.pos_sub i i' with
          | Zpos k => mkPX (Padd (PX P k P0) P') i' (Padd Q Q')
          | Z0 => mkPX (Padd P P') i (Padd Q Q')
          | Zneg k => mkPX (PaddX Padd P' k P) i (Padd Q Q')
          end
      end
  end.

Fixpoint Psub P P' {struct P'} : Pol C :=
  match P' with
  | Pc c' => PsubC P c'
  | Pinj j' Q' => PsubI Psub Q' j' P
  | PX P' i' Q' =>
      match P with
      | Pc c => PX (Popp P') i' (PaddC (Popp Q') c)
      | Pinj j Q =>
          match j with
          | xH => PX (Popp P') i' (Psub Q Q')
          | xO j => PX (Popp P') i' (Psub (Pinj (Pos.pred_double j) Q) Q')
          | xI j => PX (Popp P') i' (Psub (Pinj (xO j) Q) Q')
          end
      | PX P i Q =>
          match Z.pos_sub i i' with
          | Zpos k => mkPX (Psub (PX P k P0) P') i' (Psub Q Q')
          | Z0 => mkPX (Psub P P') i (Psub Q Q')
          | Zneg k => mkPX (PsubX Psub P' k P) i (Psub Q Q')
          end
      end
  end.

(** Multiplication *)

Fixpoint PmulC_aux P c : Pol C :=
  match P with
  | Pc c' => Pc (cmul c' c)
  | Pinj j Q => mkPinj j (PmulC_aux Q c)
  | PX P i Q => mkPX (PmulC_aux P c) i (PmulC_aux Q c)
  end.

Definition PmulC P c :=
  if ceqb c cO then P0 else
  if ceqb c cI then P else PmulC_aux P c.

(** [P * Pinj j Q], assuming [Pmul . Q] is [. * Q] *)
Section PmulI.
Variable Pmul : Pol C -> Pol C -> Pol C.
Variable Q : Pol C.
Fixpoint PmulI (j : positive) P : Pol C :=
  match P with
  | Pc c => mkPinj j (PmulC Q c)
  | Pinj j' Q' =>
      match Z.pos_sub j' j with
      | Zpos k => mkPinj j (Pmul (Pinj k Q') Q)
      | Z0 => mkPinj j (Pmul Q' Q)
      | Zneg k => mkPinj j' (PmulI k Q')
      end
  | PX P' i' Q' =>
      match j with
      | xH => mkPX (PmulI xH P') i' (Pmul Q' Q)
      | xO j' => mkPX (PmulI j P') i' (PmulI (Pos.pred_double j') Q')
      | xI j' => mkPX (PmulI j P') i' (PmulI (xO j') Q')
      end
   end.
End PmulI.

Fixpoint Pmul P P'' {struct P''} : Pol C :=
  match P'' with
  | Pc c => PmulC P c
  | Pinj j' Q' => PmulI Pmul Q' j' P
  | PX P' i' Q' =>
      match P with
      | Pc c => PmulC P'' c
      | Pinj j Q =>
          let QQ' :=
            match j with
            | xH => Pmul Q Q'
            | xO j => Pmul (Pinj (Pos.pred_double j) Q) Q'
            | xI j => Pmul (Pinj (xO j) Q) Q'
            end in
          mkPX (Pmul P P') i' QQ'
      | PX P i Q=>
          let QQ' := Pmul Q Q' in
          let PQ' := PmulI Pmul Q' xH P in
          let QP' := Pmul (mkPinj xH Q) P' in
          let PP' := Pmul P P' in
          Padd (mkPX (Padd (mkPX PP' i P0) QP') i' P0) (mkPX PQ' i QQ')
      end
  end.

Fixpoint Psquare P : Pol C :=
  match P with
  | Pc c => Pc (cmul c c)
  | Pinj j Q => Pinj j (Psquare Q)
  | PX P i Q =>
      let twoPQ := Pmul P (mkPinj xH (PmulC Q (cadd cI cI))) in
      let Q2 := Psquare Q in
      let P2 := Psquare P in
      mkPX (Padd (mkPX P2 i P0) twoPQ) i Q2
  end.

Fixpoint Ppow_pos (res P : Pol C) (p : positive) : Pol C :=
  match p with
  | xH => Pmul res P
  | xO p => Ppow_pos (Ppow_pos res P p) P p
  | xI p => Pmul (Ppow_pos (Ppow_pos res P p) P p) P
  end.

Definition Ppow_N P n := match n with N0 => P1 | Npos p => Ppow_pos P1 P p end.

End PolOps.

(** * Boolean formulas in Conjunctive Normal Form (CNF) *)
Section CNF.

(** Type parameters *)
Variable Term : Type. (** literals *)
Variable Annot : Type. (** annotation put on each literal *)

(** [is_tauto t t' = true] means that [t \/ t'] is true *)
Variable is_tauto : Term -> Term -> bool.

Definition clause : Type := list (Term * Annot).
Definition cnf : Type := list clause.

Definition cnf_tt : cnf := nil.
Definition cnf_ff : cnf := nil :: nil.

Definition is_cnf_tt (f : cnf) : bool :=
  match f with nil => true | _ => false end.

Definition is_cnf_ff (f : cnf) : bool :=
  match f with cons nil nil => true | _ => false end.

(** Our cnf is optimised, simplifying on the fly the clauses that are true. *)

(** t \/ cl, [None] means t \/ cl is true *)
Fixpoint add_term (t : Term * Annot) (cl : clause) : option clause :=
  match cl with
  | nil => if is_tauto (fst t) (fst t) then None else Some (t :: nil)
  | t' :: cl =>
      if is_tauto (fst t) (fst t') then None else
        match add_term t cl with
        | None => None
        | Some cl' => Some (t' :: cl')
        end
  end.

(** cl1 \/ cl2, [None] means cl1 \/ cl2 is true *)
Fixpoint or_clause (cl1 cl2 : clause) : option clause :=
  match cl1 with
  | nil => Some cl2
  | t :: cl =>
      match add_term t cl2 with
      | None => None
      | Some cl' => or_clause cl cl'
      end
  end.

(** cl \/ f *)
Definition or_clause_cnf (cl : clause) (f : cnf) : cnf :=
  match cl with nil => f | _ =>
    fold_left
      (fun acc cl' =>
         match or_clause cl cl' with
         | None => acc
         | Some cl'' => cl'' :: acc
         end)
      f nil
  end.

(** f1 \/ f2 *)
Fixpoint or_cnf_aux (f1 : cnf) (f2 : cnf) {struct f1} : cnf :=
  match f1 with
  | nil => cnf_tt
  | cl :: rst => rev_append (or_cnf_aux rst f2) (or_clause_cnf cl f2)
  end.

(** f1 \/ f2 *)
Definition or_cnf (f1 : cnf) (f2 : cnf) : cnf :=
  if orb (is_cnf_tt f1) (is_cnf_tt f2) then cnf_tt
  else if is_cnf_ff f2 then f1
  else or_cnf_aux f1 f2.

(** f1 /\ f2 *)
Definition and_cnf (f1 : cnf) (f2 : cnf) : cnf :=
  if orb (is_cnf_ff f1) (is_cnf_ff f2) then cnf_ff
  else if is_cnf_tt f2 then f1
  else rev_append f1 f2.

End CNF.

(** * Normalisation of formulas **)
Section FormulaNormalisation.

Variable C : Type.
Variables cO cI : C.
Variables cadd cmul csub : C -> C -> C.
Variable copp : C -> C.
Variables ceqb cleb : C -> C -> bool.

Definition cneqb (x y : C) := negb (ceqb x y).
Definition cltb (x y : C) := andb (cleb x y) (cneqb x y).

Variant Op1 : Set := (** relations with 0 *)
| Equal (** == 0 *)
| NonEqual (** ~= 0 *)
| Strict (** > 0 *)
| NonStrict (** >= 0 *).

Definition NFormula : Type := Pol C * Op1. (** normalized formula **)

#[local] Notation mkX := (mkX cO cI).
#[local] Notation Popp := (Popp copp).
#[local] Notation Padd := (Padd cO cadd ceqb).
#[local] Notation Psub := (Psub cO cadd csub copp ceqb).
#[local] Notation Pmul := (Pmul cO cI cadd cmul ceqb).
#[local] Notation Ppow_N := (Ppow_N cO cI cadd cmul ceqb).

Fixpoint Pol_of_PExpr (pe : PExpr C) : Pol C :=
  match pe with
  | PEc c => Pc c
  | PEX j => mkX j
  | PEadd (PEopp pe1) pe2 => Psub (Pol_of_PExpr pe2) (Pol_of_PExpr pe1)
  | PEadd pe1 (PEopp pe2) => Psub (Pol_of_PExpr pe1) (Pol_of_PExpr pe2)
  | PEadd pe1 pe2 => Padd (Pol_of_PExpr pe1) (Pol_of_PExpr pe2)
  | PEsub pe1 pe2 => Psub (Pol_of_PExpr pe1) (Pol_of_PExpr pe2)
  | PEmul pe1 pe2 => Pmul (Pol_of_PExpr pe1) (Pol_of_PExpr pe2)
  | PEopp pe1 => Popp (Pol_of_PExpr pe1)
  | PEpow pe1 n => Ppow_N (Pol_of_PExpr pe1) n
  end.

(** We normalize Formulas by moving terms to one side *)
Definition normalise (f : Formula C) : NFormula :=
  let (lhs, op, rhs) := f in
  let lhs := Pol_of_PExpr lhs in
  let rhs := Pol_of_PExpr rhs in
  match op with
  | OpEq => (Psub lhs rhs, Equal)
  | OpNEq => (Psub lhs rhs, NonEqual)
  | OpLe => (Psub rhs lhs, NonStrict)
  | OpGe => (Psub lhs rhs, NonStrict)
  | OpGt => (Psub lhs rhs, Strict)
  | OpLt => (Psub rhs lhs, Strict)
  end.

(** Check that a normalised formula f is inconsistent
by comparing the normalised constant with 0 *)
Definition check_inconsistent (f : NFormula) : bool :=
  let (e, op) := f in
  match e with
  | Pc c =>
      match op with
      | Equal => cneqb c cO
      | NonStrict => cltb c cO
      | Strict => cleb c cO
      | NonEqual => ceqb c cO
      end
  | _ => false (** not a constant *)
  end.

(** Normalisation to CNF

This removes the non convex operator [NonEqual] and negates the formula.
We will later need the negated literals, so we can just as well have the CNF
contain negated lterals yet (as misleading as it can be).
Thus we later denote [eval_cnf (fun g => ~ NFeval l g)] the eval function
for CNFs (where [NFeval l g] evaluates literal [g] in environment [l]). *)

(** Normalise and negate the formula
[forall T (tg : T) l f,
   eval_cnf (fun g => ~ NFeval l g) (map (fun nf => (nf, tg)) (normalise_aux f))
   <-> NFeval l f] *)
Definition normalise_aux (f : NFormula) : list NFormula :=
  let (e, o) := f in
  match o with
  | Equal => (e, Strict) :: (Popp e, Strict) :: nil
  | NonEqual => (e, Equal) :: nil
  | Strict => (Popp e, NonStrict) :: nil
  | NonStrict => (Popp e, Strict) :: nil
  end.

(** Normalise and negate twice the formula (so actually doesn't negate anything)
[forall T (tg : T) l f,
   eval_cnf (fun g => ~ NFeval l g) (map (fun nf => (nf, tg)) (normalise_aux f))
   <-> ~ NFeval l f] *)
Definition negate_aux (t : NFormula) : list NFormula :=
  let (e, o) := t in
  match o with
  | Equal => (e, Equal) :: nil
  | NonEqual => (e, Strict) :: (Popp e, Strict) :: nil
  | Strict => (e, Strict) :: nil
  | NonStrict => (e, NonStrict) :: nil
  end.

(** [forall T (tg : T) l f,
  eval_cnf (fun g => ~ NFeval l g) (cnf_of_list f tg)
  <-> eval_cnf (fun g => ~ NFeval l g) (map (fun g => (g, tg)) f)] *)
Definition cnf_of_list {T : Type} (l : list NFormula) (tg : T) :
    cnf NFormula T :=
  fold_right
    (fun x acc =>
       if check_inconsistent x then acc else ((x, tg) :: nil) :: acc)
    (cnf_tt _ _) l.

(** [forall T (tg : T) l f,
  eval_cnf (fun g => ~ NFeval l g) (cnf_normalise f tg) <-> Feval l f] *)
Definition cnf_normalise {T: Type} (t : Formula C) (tg : T) : cnf NFormula T :=
  let f := normalise t in
  if check_inconsistent f then cnf_ff _ _
  else cnf_of_list (normalise_aux f) tg.

(** [forall T (tg : T) l f,
  eval_cnf (fun g => ~ NFeval l g) (cnf_negate f tg) <-> ~ Feval l f] *)
Definition cnf_negate {T: Type} (t : Formula C) (tg : T) : cnf NFormula T :=
  let f := normalise t in
  if check_inconsistent f then cnf_tt _ _
  else cnf_of_list (negate_aux f) tg.

End FormulaNormalisation.

(** * Normalise input [GFormula] as CNF whose literals are [NFormula] *)
Section GFormulaNormalisation.

(** Type parameters *)
Variable Term : Type. (** literals of non normalized formulas *)
Variable Annot : Type. (** annotation put on each literal *)

Variable cnf : Type. (** Type of normalised formulas **)
Variable cnf_tt : cnf.
Variable cnf_ff : cnf.
Variable or_cnf : cnf -> cnf -> cnf.
Variable and_cnf : cnf -> cnf -> cnf.

Variable normalise : Term -> Annot -> cnf.
Variable negate : Term -> Annot -> cnf.

Section REC.
Context {TX : kind -> Type} {AF : Type}.
(** The formulas we are normalizing
- TX is Prop in Rocq and EConstr.constr in Ocaml.
- AF is unit in Rocq and Names.Id.t in Ocaml *)
#[local] Notation TFormula := (@GFormula Term TX Annot AF).

(** Normalisation function, if [pol] is false, produces the negation *)
Variable REC : forall (pol : bool) (k : kind) (f : TFormula k), cnf.

Definition mk_and (k : kind) (pol : bool) (f1 f2 : TFormula k) :=
  (if pol then and_cnf else or_cnf) (REC pol f1) (REC pol f2).

Definition mk_or (k : kind) (pol : bool) (f1 f2 : TFormula k) :=
  (if pol then or_cnf else and_cnf) (REC pol f1) (REC pol f2).

Definition mk_impl (k : kind) (pol : bool) (f1 f2 : TFormula k) :=
  (if pol then or_cnf else and_cnf) (REC (negb pol) f1) (REC pol f2).

Definition mk_iff (k : kind) (pol : bool) (f1 f2 : TFormula k) :=
  or_cnf (and_cnf (REC (negb pol) f1) (REC false f2))
    (and_cnf (REC pol f1) (REC true f2)).
End REC.

Definition is_bool {TX : kind -> Type} {AF : Type} (k : kind)
    (f : @GFormula Term TX Annot AF k) :=
  match f with
  | TT _ => Some true
  | FF _ => Some false
  | _ => None
  end.

(** Normalisation function, if [pol] is false, produces the negation
Assuming [is_tauto_correct : forall l (f g : NFormula rat),
  is_tauto f g -> ~ NFeval l f \/ ~ NFeval l g]
we have [forall l pol k (f : GFormula k),
  eval_cnf (fun g => ~ NFeval l g) (@cnf_of_GFormula eKind unit pol k f) ->
  (if pol then id else not) (GFeval Feval l f)]*)
Fixpoint cnf_of_GFormula {TX : kind -> Type} {AF : Type} (pol : bool) (k : kind)
    (f : @GFormula Term TX Annot AF k) {struct f} : cnf :=
  match f with
  | TT _ => if pol then cnf_tt else cnf_ff
  | FF _ => if pol then cnf_ff else cnf_tt
  | X _ p => if pol then cnf_ff else cnf_ff
    (** This is not complete - cannot negate any proposition **)
  | A _ x t => if pol then normalise x t else negate x t
  | AND e1 e2 => mk_and cnf_of_GFormula pol e1 e2
  | OR e1 e2  => mk_or cnf_of_GFormula pol e1 e2
  | NOT e  => cnf_of_GFormula (negb pol) e
  | IMPL e1 _ e2 => mk_impl cnf_of_GFormula pol e1 e2
  | IFF e1 e2 =>
      match is_bool e2 with
      | Some isb => cnf_of_GFormula (if isb then pol else negb pol) e1
      | None  => mk_iff cnf_of_GFormula pol e1 e2
      end
  | EQ e1 e2 =>
      match is_bool e2 with
      | Some isb => cnf_of_GFormula (if isb then pol else negb pol) e1
      | None  => mk_iff cnf_of_GFormula pol e1 e2
      end
  end.

End GFormulaNormalisation.

(** * Core of the checker, checking individual literals *)
Section FormulaChecker.

Variable C : Type.
Variables cO cI : C.
Variables cplus ctimes cminus: C -> C -> C.
Variable copp : C -> C.
Variables ceqb cleb : C -> C -> bool.

#[local] Notation NFormula := (NFormula C).

(** Rule of "signs" for multiplication and addition.
An arbitrary result is coded by None. *)

Definition OpMult (o o' : Op1) : option Op1 :=
  match o, o' with
  | Equal, _ | _, Equal => Some Equal
  | NonEqual, _ | _, NonEqual => None (** NonEqual no longer present here **)
  | Strict, _ => Some o'
  | _, Strict => Some o
  | NonStrict, NonStrict => Some NonStrict
  end.

Definition OpAdd (o o': Op1) : option Op1 :=
  match o, o' with
  | Equal, _ => Some o'
  | _, Equal => Some o
  | NonEqual, _ | _, NonEqual => None
  | Strict, _ | _, Strict => Some Strict
  | NonStrict, NonStrict => Some NonStrict
  end.

(** Given a list [l] of NFormula and an extended polynomial expression [e],
if [eval_Psatz l e] succeeds (= Some f) then [f] is a logic consequence
of the conjunction of the formulas in l.
Moreover, the polynomial expression is obtained by replacing the
(PsatzIn n) by the nth polynomial expression in [l] and the sign is
computed by the "rule of sign". *)

(** [forall l e f f', NFeval l f ->
pexpr_times_nformula e f = Some f' -> NFeval l f'] *)
Definition pexpr_times_nformula (e : Pol C) (f : NFormula) : option NFormula :=
  let (ef, o) := f in
  match o with
  | Equal => Some (Pmul cO cI cplus ctimes ceqb e ef, Equal)
  | _ => None
  end.

(** [forall l f f' f'', NFeval l f -> NFeval l f' ->
nformula_times_nformula f f' = Some f'' -> NFeval l f''] *)
Definition nformula_times_nformula (f1 f2 : NFormula) : option NFormula :=
  let (e1, o1) := f1 in
  let (e2, o2) := f2 in
  map_option (fun x => (Pmul cO cI cplus ctimes ceqb e1 e2, x)) (OpMult o1 o2).

(** [forall l f f' f'', NFeval l f -> NFeval l f' ->
nformula_plus_nformula f f' = Some f'' -> NFeval l f''] *)
Definition nformula_plus_nformula (f1 f2 : NFormula) : option NFormula :=
  let (e1, o1) := f1 in
  let (e2, o2) := f2 in
  map_option (fun x => (Padd cO cplus ceqb e1 e2, x)) (OpAdd o1 o2).

(** [forall l f g, is_tauto f g -> ~ NFeval l f \/ ~ NFeval l g] *)
Definition is_tauto (f1 f2 : NFormula) : bool :=
  match nformula_plus_nformula f1 f2 with
  | None => false
  | Some u => check_inconsistent cO ceqb cleb u
  end.

(** [forall l (lf : list (NFormula C)) (w : Psatz C), all (NFeval l) lf ->
forall f : NFormula C, eval_Psatz lf w = Some f -> NFeval l f] *)
Fixpoint eval_Psatz (l : list NFormula) (e : Psatz C) {struct e} :
    option NFormula :=
  match e with
  | PsatzLet p1 p2 =>
      match eval_Psatz l p1 with
      | None => None
      | Some f => eval_Psatz (f :: l) p2
      end
  | PsatzIn _ n => Some (nth n l (Pc cO, Equal))
  | PsatzSquare e => Some (Psquare cO cI cplus ctimes ceqb e, NonStrict)
  | PsatzMulC re e => bind_option (pexpr_times_nformula re) (eval_Psatz l e)
  | PsatzMulE f1 f2 =>
      bind_option2 nformula_times_nformula (eval_Psatz l f1) (eval_Psatz l f2)
  | PsatzAdd f1 f2 =>
      bind_option2 nformula_plus_nformula (eval_Psatz l f1) (eval_Psatz l f2)
  | PsatzC c => if cltb ceqb cleb cO c then Some (Pc c, Strict) else None
    (** This could also handle 0, or <> 0 -- but these cases are useless **)
  | PsatzZ _ => Some (Pc cO, Equal) (** Just to make life easier *)
  end.

(** [forall l (lf : list (NFormula C)) (w : Psatz C),
check_normalised_formulas lf w -> has (fun f => ~ NFeval l f) lf] *)
Definition check_normalised_formulas (l : list NFormula) (cm : Psatz C) :
    bool :=
  match eval_Psatz l cm with
  | None => false
  | Some f => check_inconsistent cO ceqb cleb f
  end.

End FormulaChecker.

(** * The checker itself, checking entire CNF formulas *)
Section TautoChecker.

(** Type parameters *)
Variable clause : Type. (** normalised clauses **)
Variable Witness : Type.

Variable checker : clause -> Witness -> bool.

Fixpoint cnf_checker (f : list clause) (wl : list Witness) {struct f} : bool :=
  match f with
  | nil => true
  | cl :: f =>
      match wl with
      | nil => false
      | w :: wl => andb (checker cl w) (cnf_checker f wl)
      end
  end.

(** [forall l (f : cnf (NFormula C) unit) (w : seq (Psatz C)),
tauto_checker f w -> eval_cnf (fun g => ~ NFeval l g) f] *)
Definition tauto_checker (f : list clause) (w : list Witness) : bool :=
  cnf_checker f w.

End TautoChecker.

(** * Putting everything together *)
Section CTautoChecker.
Variable C : Type.
Variables (cO cI : C) (cadd cmul csub : C -> C -> C) (copp : C -> C).
Variables ceqb cleb : C -> C -> bool.

Definition CWeakChecker := check_normalised_formulas cO cI cadd cmul ceqb cleb.
Definition Cnormalise := @cnf_normalise C cO cI cadd cmul csub copp ceqb cleb.
Definition Cnegate := @cnf_negate C cO cI cadd cmul csub copp ceqb cleb.
Definition Cis_tauto := @is_tauto C cO cadd ceqb cleb.

Definition Ccnf_of_GFormula := @cnf_of_GFormula _ _ _
  (cnf_tt _ _) (cnf_ff _ _) (or_cnf Cis_tauto) (@and_cnf _ _)
  (@Cnormalise unit) (@Cnegate unit) eKind unit true isProp.

(** [forall l f w : CTautoChecker f w -> GFeval Feval l f] *)
Definition CTautoChecker (f : BFormula (Formula C) isProp) :
    list (Psatz C) -> bool :=
  tauto_checker (fun cl => CWeakChecker (map fst cl)) (Ccnf_of_GFormula f).

End CTautoChecker.

(** Instantiate on Q *)
Definition QTautoChecker := CTautoChecker
  Q0 Q1 Qplus Qmult Qminus Qopp Qeq_bool Qle_bool.

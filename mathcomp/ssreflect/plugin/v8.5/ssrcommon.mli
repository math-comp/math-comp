(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)

open Names
(******************************** misc ************************************)
type loc = Loc.t

val pr_id : Id.t -> Pp.std_ppcmds
val pr_name : Name.t -> Pp.std_ppcmds
val pr_spc : unit -> Pp.std_ppcmds
val pr_bar : unit -> Pp.std_ppcmds
val pr_list : 
  (unit -> Pp.std_ppcmds) -> ('a -> Pp.std_ppcmds) -> 'a list -> Pp.std_ppcmds
val pr_paren : ('a -> Pp.std_ppcmds) -> 'a -> Pp.std_ppcmds
val dummy_loc : loc
val errorstrm : Pp.std_ppcmds -> 'a
val loc_error : loc -> string -> 'a
val anomaly : string -> 'a

val array_app_tl : 'a array -> 'a list -> 'a list
val array_list_of_tl : 'a array -> 'a list
val array_fold_right_from : int -> ('a -> 'b -> 'b) -> 'a array -> 'b -> 'b

(**************************** lifted tactics ******************************)
open Proof_type
open Evd
open Refiner

(* tactics with extra data attached to each goals, e.g. the list of
 * temporary variables to be cleared *)
type 'a tac_a = (goal * 'a) sigma -> (goal * 'a) list sigma

(* Thread around names to be cleared or generalized back, and the speed *)
type tac_ctx = {
  tmp_ids : (Id.t * name ref) list;
  wild_ids : Id.t list;
  (* List of variables to be cleared at the end of the sentence *)
  delayed_clears : Id.t list;
  (* Intro mode: name every item v.s. name every non-dependent-product item *)
  speed : [ `Slow | `Fast ]
}

val new_ctx : unit -> tac_ctx (* REMOVE *)
val pull_ctxs : ('a * tac_ctx) list  sigma -> 'a list sigma * tac_ctx list (* REMOVE *)

val with_fresh_ctx : tac_ctx tac_a -> tactic

val pull_ctx : ('a * tac_ctx) sigma -> 'a sigma * tac_ctx
val push_ctx : tac_ctx -> 'a sigma -> ('a * tac_ctx) sigma
val push_ctxs : tac_ctx -> 'a list sigma -> ('a * tac_ctx) list sigma
val tac_ctx : tactic -> tac_ctx tac_a
val with_ctx :
  (tac_ctx -> 'b * tac_ctx) -> ('a * tac_ctx) sigma -> 'b * ('a * tac_ctx) sigma
val without_ctx : ('a sigma -> 'b) -> ('a * tac_ctx) sigma -> 'b

(* Standard tacticals lifted to the tac_a type *)
val tclTHENLIST_a : tac_ctx tac_a list -> tac_ctx tac_a
val tclTHEN_i_max :
  tac_ctx tac_a -> (int -> int -> tac_ctx tac_a) -> tac_ctx tac_a
val tclTHEN_a : tac_ctx tac_a -> tac_ctx tac_a -> tac_ctx tac_a
val tclTHENS_a : tac_ctx tac_a -> tac_ctx tac_a list -> tac_ctx tac_a

val tac_on_all :
  (goal * tac_ctx) list sigma -> tac_ctx tac_a -> (goal * tac_ctx) list sigma

(************************* generic argument helpers *********************)
open Genarg

type gist = Tacintern.glob_sign
type ist = Tacinterp.interp_sign

val add_genarg : string -> ('a -> Pp.std_ppcmds) -> 'a uniform_genarg_type
val interp_wit :
  ('a, 'b, 'c) genarg_type -> ist -> goal sigma -> 'b -> evar_map * 'c

(************************** Parsing helpers *********************************)

(* look ahead for specific symbols/ids *)
val accept_before_syms : string list -> Tok.t Stream.t -> unit
val accept_before_syms_or_any_id : string list -> Tok.t Stream.t -> unit
val accept_before_syms_or_ids : string list -> string list -> Tok.t Stream.t -> unit

(************************ ssr tactic arguments ******************************)

(* Names of variables to be cleared (automatic check: not a section var) *)
type ssrhyp = SsrHyp of loc * Id.t

val ssrhyp : ssrhyp Pcoq.Gram.entry
val wit_ssrhyp : ssrhyp uniform_genarg_type
val intern_hyp : gist -> ssrhyp -> ssrhyp
val interp_hyp : ist -> goal sigma -> ssrhyp -> evar_map * ssrhyp

val pr_hyp : ssrhyp -> Pp.std_ppcmds
val hyp_err : loc -> string -> Id.t -> 'a
val hyp_id : ssrhyp -> Id.t
val not_section_id : Id.t -> bool
val check_hyp_exists : Context.named_context -> ssrhyp -> unit
val test_hypname_exists : Context.named_context -> Id.t -> bool

(* Variant of the above *)
type ssrhyp_or_id = Hyp of ssrhyp | Id of ssrhyp

val ssrhoi_id : ssrhyp_or_id Pcoq.Gram.entry
val ssrhoi_hyp : ssrhyp_or_id Pcoq.Gram.entry
val wit_ssrhoi_hyp : ssrhyp_or_id uniform_genarg_type
val wit_ssrhoi_id : ssrhyp_or_id uniform_genarg_type

val pr_hoi : ssrhyp_or_id -> Pp.std_ppcmds
val hoi_id : ssrhyp_or_id -> Id.t

(* Variant of the above *)
type ssrhyps = ssrhyp list

val ssrhyps : ssrhyps Pcoq.Gram.entry
val wit_ssrhyps : ssrhyps uniform_genarg_type
val interp_hyps : ist -> goal sigma -> ssrhyps -> evar_map * ssrhyps

val pr_hyps : ssrhyps -> Pp.std_ppcmds
val check_hyps_uniq : Id.t list -> ssrhyps -> unit
val hyps_ids : ssrhyps -> Id.t list

(* Direction to be used for rewriting as in -> or rewrite flag *)
type ssrdir = L2R | R2L
val wit_ssrdir : ssrdir uniform_genarg_type

val pr_dir : ssrdir -> Pp.std_ppcmds
val pr_rwdir : ssrdir -> Pp.std_ppcmds
val dir_org : ssrdir -> int
val pr_dir_side : ssrdir -> Pp.std_ppcmds
val inv_dir : ssrdir -> ssrdir

(* simpl: "/=", cut: "//", simplcut: "//=" nop: commodity placeholder *)
type ssrsimpl = Simpl of int | Cut of int | SimplCut of int * int | Nop

val ssrsimpl : ssrsimpl Pcoq.Gram.entry
val ssrsimpl_ne : ssrsimpl Pcoq.Gram.entry
val wit_ssrsimpl : ssrsimpl uniform_genarg_type
val wit_ssrsimpl_ne : ssrsimpl uniform_genarg_type

val pr_simpl : ssrsimpl -> Pp.std_ppcmds
val test_not_ssrslashnum : unit Pcoq.Gram.entry (* REMOVE *)

(* inddex MAYBE REMOVE ONLY INTERNAL stuff between {} *)
type ssrindex = int Misctypes.or_var

val ssrindex : ssrindex Pcoq.Gram.entry
val wit_ssrindex : ssrindex uniform_genarg_type

val pr_index : ssrindex -> Pp.std_ppcmds
val noindex : ssrindex
val mk_index : loc -> ssrindex -> ssrindex
val check_index : loc -> int -> int

(** Occurrence switch {1 2}, all is Some(false,[]) *)
type ssrocc = (bool * int list) option

val ssrocc : ssrocc Pcoq.Gram.entry
val wit_ssrocc : ssrocc uniform_genarg_type

val pr_occ : ssrocc -> Pp.std_ppcmds
val allocc : ssrocc

(* modality for rewrite and do: ! ? *)
type ssrmmod = May | Must | Once

val ssrmmod : ssrmmod Pcoq.Gram.entry
val wit_ssrmmod : ssrmmod uniform_genarg_type

val pr_mmod : ssrmmod -> Pp.std_ppcmds

(* modality with a bound for rewrite and do: !n ?n *)
type ssrmult = int * ssrmmod

val ssrmult : ssrmult Pcoq.Gram.entry
val ssrmult_ne : ssrmult Pcoq.Gram.entry
val wit_ssrmult : ssrmult uniform_genarg_type
val wit_ssrmult_ne : ssrmult uniform_genarg_type

val pr_mult : ssrmult -> Pp.std_ppcmds
val notimes : int
val nomult : ssrmult

(* clear switch {H G} *)
type ssrclear = ssrhyps

val ssrclear : ssrclear Pcoq.Gram.entry
val ssrclear_ne : ssrclear Pcoq.Gram.entry
val wit_ssrclear : ssrhyps uniform_genarg_type
val wit_ssrclear_ne : ssrhyps uniform_genarg_type

val pr_clear : (unit -> Pp.std_ppcmds) -> ssrclear -> Pp.std_ppcmds
val pr_clear_ne : ssrclear -> Pp.std_ppcmds

(* Discharge occ switch (combined occurrence / clear switch) *)
type ssrdocc = ssrclear option * ssrocc

val ssrdocc : ssrdocc Pcoq.Gram.entry
val wit_ssrdocc : ssrdocc uniform_genarg_type

val pr_docc : ssrdocc -> Pp.std_ppcmds
val mkocc : ssrocc -> ssrdocc
val noclr : ssrdocc
val mkclr : ssrclear -> ssrdocc
val nodocc : ssrdocc

(* terms are pre constr, the kind is parsing/printing flag to distinguish
 * between x, @x and (x). It affects automatic clear and let-in preservation.
 * Cpattern is a temporary flag that becomes InParens ASAP. *)
type ssrtermkind = InParens | WithAt | NoFlag | Cpattern

val ssrtermkind : ssrtermkind Pcoq.Gram.entry

type ssrterm = ssrtermkind * Tacexpr.glob_constr_and_expr

val ssrterm : ssrterm Pcoq.Gram.entry
val wit_ssrterm : ssrterm uniform_genarg_type

val pr_term : ssrterm -> Pp.std_ppcmds
val prl_term : ssrterm -> Pp.std_ppcmds
val prl_glob_constr : Glob_term.glob_constr -> Pp.std_ppcmds
val pr_guarded :
  (string -> int -> bool) -> ('a -> Pp.std_ppcmds) -> 'a -> Pp.std_ppcmds
val guard_term : ssrtermkind -> string -> int -> bool
val glob_constr :
  Tacinterp.interp_sign -> Environ.env ->
    Tacexpr.glob_constr_and_expr -> Glob_term.glob_constr
val interp_open_constr : 
  Tacinterp.interp_sign -> Proof_type.goal Tacmach.sigma ->
    Tacexpr.glob_constr_and_expr -> Evd.evar_map * Evd.open_constr
val intern_term : 
  Tacinterp.interp_sign -> Environ.env ->
    ssrterm -> Glob_term.glob_constr
val pf_intern_term :
  Tacinterp.interp_sign -> Proof_type.goal Tacmach.sigma ->
    ssrterm -> Glob_term.glob_constr
val interp_term :
  Tacinterp.interp_sign -> Proof_type.goal Tacmach.sigma ->
    ssrterm -> Evd.open_constr
val force_term :
  Tacinterp.interp_sign -> Proof_type.goal Tacmach.sigma ->
    ssrterm -> Evd.open_constr
val subst_ssrterm : Mod_subst.substitution -> ssrterm -> ssrterm
val glob_ssrterm : Tacintern.glob_sign -> ssrterm -> ssrterm
val mk_term : ssrtermkind -> Constrexpr.constr_expr -> ssrterm
val mk_lterm : Constrexpr.constr_expr -> ssrterm

val mkRHole : Glob_term.glob_constr

(* views *)

type ssrview = ssrterm list

val ssrview : ssrview Pcoq.Gram.entry
val wit_ssrview : ssrview uniform_genarg_type

val pr_view : ssrview -> Pp.std_ppcmds

(* Extended intro patterns: foo /bar[ H | -> ] and company *)
type seed = [ `Id of Id.t * [`Pre | `Post] | `Anon | `Wild ]
type ssripat =
  | IpatSimpl of ssrclear * ssrsimpl
  | IpatId of identifier
  | IpatWild
  | IpatCase of [ `Regular of ssripatss
                | `Block of ssripatss * seed * ssripatss ]
  | IpatInj of ssripatss
  | IpatRw of ssrocc * ssrdir
  | IpatAll
  | IpatAnon
  | IpatView of ssrterm list
  | IpatNoop
  | IpatNewHidden of identifier list
  | IpatFastMode
  | IpatTmpId
  | IpatSeed of seed
and ssripats = ssripat list
and ssripatss = ssripats list
type ssrhpats = ((ssrclear * ssripats) * ssripats) * ssripats
type ssrhpats_wtransp = bool * ssrhpats

val ssrintros : ssripats Pcoq.Gram.entry
val ssrintros_ne : ssripats Pcoq.Gram.entry
val ssrrpat : ssripat Pcoq.Gram.entry
val ssrhpats : ssrhpats Pcoq.Gram.entry
val ssrhpats_wtransp : ssrhpats_wtransp Pcoq.Gram.entry
val ssrhpats_nobs : ssrhpats Pcoq.Gram.entry

val wit_ssripatrep : ssripat uniform_genarg_type (* FIXME *)
val wit_ssrintros : ssripats uniform_genarg_type
val wit_ssrintros_ne : ssripats uniform_genarg_type
val wit_ssrrpat : ssripat uniform_genarg_type
val wit_ssrhpats : ssrhpats uniform_genarg_type
val wit_ssrhpats_wtransp : ssrhpats_wtransp uniform_genarg_type
val wit_ssrhpats_nobs : ssrhpats uniform_genarg_type

val pr_ipat : ssripat -> Pp.std_ppcmds
val pr_ipats : ssripats -> Pp.std_ppcmds
val pr_intros : (unit -> Pp.std_ppcmds) -> ssripats -> Pp.std_ppcmds
val pr_hpats : ssrhpats -> Pp.std_ppcmds

(*********************** Wrapped Coq  tactics *****************************)

val rewritetac : ssrdir -> Constr.t -> tactic

(***** Hooks to break recursive deps among tactics ************************)

type name_hint = (int * Constr.types array) option ref
type simplest_newcase = ?ind:name_hint -> Constr.t -> tactic
val simplest_newcase : simplest_newcase Hook.t
val simplest_newcase_tac : simplest_newcase Hook.value

type ipat_rewrite = ssrocc -> ssrdir -> Constr.t -> tactic
val ipat_rewrite : ipat_rewrite Hook.t
val ipat_rewrite_tac : ipat_rewrite Hook.value

type move_top_with_view =
  next:ssripats ref -> bool -> Id.t ref -> bool * ssrterm list -> ist ->
    tac_ctx tac_a
val move_top_with_view : move_top_with_view Hook.t
val move_top_with_view_tac : move_top_with_view Hook.value

(*
TODO:
move_top_with_view
gentac_ref
tclEQINTROSviewtac_ref
*)



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
val dummy_loc : loc
val errorstrm : Pp.std_ppcmds -> 'a
val loc_error : loc -> string -> 'a
val anomaly : string -> 'a

(**************************** lifted tactics ******************************)
open Proof_type
open Evd
open Refiner

type 'a tac_a = (goal * 'a) sigma -> (goal * 'a) list sigma

(* Thread around names to be cleared or generalized back, and the speed *)
type tac_ctx = {
  tmp_ids : (Id.t * name ref) list;
  wild_ids : Id.t list;
  delayed_clears : Id.t list;
  speed : [ `Slow | `Fast ]
}

val new_ctx : unit -> tac_ctx (* REMOVE *)
val pull_ctxs : ('a * tac_ctx) list  sigma -> 'a list sigma * tac_ctx list (* REMOVE *)

val with_fresh_ctx : tac_ctx tac_a -> tactic

val pull_ctx : ('a * tac_ctx) sigma -> 'a sigma * tac_ctx
val push_ctx : tac_ctx -> 'a sigma -> ('a * tac_ctx) sigma
val push_ctxs : tac_ctx -> 'a list sigma -> ('a * tac_ctx) list sigma
val tac_ctx : tactic -> tac_ctx tac_a
val with_ctx : (tac_ctx -> 'b * tac_ctx) -> ('a * tac_ctx) sigma -> 'b * ('a * tac_ctx) sigma
val without_ctx : ('a sigma -> 'b) -> ('a * tac_ctx) sigma -> 'b

val tclTHENLIST_a : tac_ctx tac_a list -> tac_ctx tac_a
val tclTHEN_i_max : tac_ctx tac_a -> (int -> int -> tac_ctx tac_a) -> tac_ctx tac_a
val tclTHEN_a : tac_ctx tac_a -> tac_ctx tac_a -> tac_ctx tac_a
val tclTHENS_a : tac_ctx tac_a -> tac_ctx tac_a list -> tac_ctx tac_a

val tac_on_all : (goal * tac_ctx) list sigma -> tac_ctx tac_a -> (goal * tac_ctx) list sigma


(************************* generic argument helpers *********************)
open Genarg

type gist = Tacintern.glob_sign
type ist = Tacinterp.interp_sign


val add_genarg : string -> ('a -> Pp.std_ppcmds) -> ('a, 'a, 'a) genarg_type
val interp_wit :
  ('a, 'b, 'c) genarg_type -> ist -> goal sigma -> 'b -> evar_map * 'c


(************************* ssr data types *********************************)

(* Names of variables to be cleared (automatic check: not a section var) *)
type ssrhyp = SsrHyp of loc * Id.t

val ssrhyp : ssrhyp Pcoq.Gram.entry
val wit_ssrhyp : (ssrhyp, ssrhyp, ssrhyp) genarg_type
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
val wit_ssrhoi_hyp : (ssrhyp_or_id,ssrhyp_or_id,ssrhyp_or_id) genarg_type
val wit_ssrhoi_id : (ssrhyp_or_id,ssrhyp_or_id,ssrhyp_or_id) genarg_type

val pr_hoi : ssrhyp_or_id -> Pp.std_ppcmds
val hoi_id : ssrhyp_or_id -> Id.t

(* Variant of the above *)
type ssrhyps = ssrhyp list

val ssrhyps : ssrhyps Pcoq.Gram.entry
val wit_ssrhyps : (ssrhyps,ssrhyps,ssrhyps) genarg_type
val interp_hyps : ist -> goal sigma -> ssrhyps -> evar_map * ssrhyps

val pr_hyps : ssrhyps -> Pp.std_ppcmds
val check_hyps_uniq : Id.t list -> ssrhyps -> unit
val hyps_ids : ssrhyps -> Id.t list

(* L2R or R2L *)
type ssrdir = Ssrmatching.ssrdir
val wit_ssrdir : (ssrdir,ssrdir,ssrdir) genarg_type

val pr_dir : ssrdir -> Pp.std_ppcmds
val pr_rwdir : ssrdir -> Pp.std_ppcmds
val dir_org : ssrdir -> int

(* /=, // *)
type ssrsimpl = Simpl of int | Cut of int | SimplCut of int * int | Nop

val ssrsimpl : ssrsimpl Pcoq.Gram.entry
val ssrsimpl_ne : ssrsimpl Pcoq.Gram.entry
val wit_ssrsimpl : (ssrsimpl,ssrsimpl,ssrsimpl) genarg_type
val wit_ssrsimpl_ne : (ssrsimpl,ssrsimpl,ssrsimpl) genarg_type

val pr_simpl : ssrsimpl -> Pp.std_ppcmds
val test_not_ssrslashnum : unit Pcoq.Gram.entry (* REMOVE *)

(* {H G} *)
type ssrclear = ssrhyps

val ssrclear : ssrclear Pcoq.Gram.entry
val ssrclear_ne : ssrclear Pcoq.Gram.entry
val wit_ssrclear : (ssrhyps,ssrhyps,ssrhyps) genarg_type
val wit_ssrclear_ne : (ssrhyps,ssrhyps,ssrhyps) genarg_type

val pr_clear : (unit -> Pp.std_ppcmds) -> ssrclear -> Pp.std_ppcmds
val pr_clear_ne : ssrclear -> Pp.std_ppcmds

(* {1 2} *)
type ssrocc = Ssrmatching.occ

type ssrtermrep = char * Tacexpr.glob_constr_and_expr

(* foo /bar[ H | -> ] and company *)
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
  | IpatView of ssrtermrep list
  | IpatNoop
  | IpatNewHidden of identifier list
  | IpatFastMode
  | IpatTmpId
  | IpatSeed of seed
and ssripats = ssripat list
and ssripatss = ssripats list

open Ssrmatching
(*********************** Wrapped Coq  tactics *****************************)

val rewritetac : ssrdir -> Constr.t -> tactic

(******************************* hooks ************************************)

type name_hint = (int * Constr.types array) option ref
type simplest_newcase = ?ind:name_hint -> Constr.t -> tactic
val simplest_newcase : simplest_newcase Hook.t
val simplest_newcase_tac : simplest_newcase Hook.value

type ipat_rewrite = occ -> ssrdir -> Constr.t -> tactic
val ipat_rewrite : ipat_rewrite Hook.t
val ipat_rewrite_tac : ipat_rewrite Hook.value

type move_top_with_view =
  next:ssripats ref -> bool -> Id.t ref -> bool * ssrtermrep list -> ist ->
    tac_ctx tac_a
val move_top_with_view : move_top_with_view Hook.t
val move_top_with_view_tac : move_top_with_view Hook.value

(*
TODO:
move_top_with_view
gentac_ref
tclEQINTROSviewtac_ref
*)



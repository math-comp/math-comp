(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)

open Names
open Proof_type
open Evd
open Tacmach
open Refiner

type 'a tac_a = (goal * 'a) sigma -> (goal * 'a) list sigma

let push_ctx  a gl = re_sig (sig_it gl, a) (project gl)
let push_ctxs a gl =
  re_sig (List.map (fun x -> x,a) (sig_it gl)) (project gl)
let pull_ctx gl = let g, a = sig_it gl in re_sig g (project gl), a
let pull_ctxs gl = let g, a = List.split (sig_it gl) in re_sig g (project gl), a

let with_ctx f gl =
  let gl, ctx = pull_ctx gl in
  let rc, ctx = f ctx in
  rc, push_ctx ctx gl
let without_ctx f gl =
  let gl, _ctx = pull_ctx gl in
  f gl
let tac_ctx t gl =
  let gl, a = pull_ctx gl in
  let gl = t gl in
  push_ctxs a gl

let tclTHEN_ia t1 t2 gl =
  let gal = t1 gl in
  let goals, sigma = sig_it gal, project gal in
  let _, opened, sigma =
    List.fold_left (fun (i,opened,sigma) g ->
      let gl = t2 i (re_sig g sigma) in
      i+1, sig_it gl :: opened, project gl)
      (1,[],sigma) goals in
  re_sig (List.flatten (List.rev opened)) sigma

let tclTHEN_a t1 t2 gl = tclTHEN_ia t1 (fun _ -> t2) gl

let tclTHENS_a t1 tl gl = tclTHEN_ia t1
  (fun i -> List.nth tl (i-1)) gl

let rec tclTHENLIST_a = function
  | [] -> tac_ctx tclIDTAC
  | t1::tacl -> tclTHEN_a t1 (tclTHENLIST_a tacl)

(* like  tclTHEN_i but passes to the tac "i of n" and not just i *)
let tclTHEN_i_max tac taci gl =
  let maxi = ref 0 in
  tclTHEN_ia (tclTHEN_ia tac (fun i -> maxi := max i !maxi; tac_ctx tclIDTAC))
    (fun i gl -> taci i !maxi gl) gl

let tac_on_all gl tac =
  let goals = sig_it gl in
  let opened, sigma =
    List.fold_left (fun (opened,sigma) g ->
      let gl = tac (re_sig g sigma) in
      sig_it gl :: opened, project gl)
      ([],project gl) goals in
  re_sig (List.flatten (List.rev opened)) sigma

(* Used to thread data between intro patterns at run time *)
type tac_ctx = {
  tmp_ids : (Id.t * name ref) list;
  wild_ids : Id.t list;
  delayed_clears : Id.t list;
  speed : [ `Slow | `Fast ]
}

let new_ctx () =
  { tmp_ids = []; wild_ids = []; delayed_clears = []; speed = `Slow }

let with_fresh_ctx t gl =
  let gl = push_ctx (new_ctx()) gl in
  let gl = t gl in
  fst (pull_ctxs gl)



type ist = Tacinterp.interp_sign
type gist = Tacintern.glob_sign

open Genarg

(** Adding a new uninterpreted generic argument type *)
let add_genarg tag pr =
  let wit = make0 None tag in
  let glob ist x = (ist, x) in
  let subst _ x = x in
  let interp ist gl x = (gl.Evd.sigma, x) in
  let gen_pr _ _ _ = pr in
  let () = Genintern.register_intern0 wit glob in
  let () = Genintern.register_subst0 wit subst in
  let () = Geninterp.register_interp0 wit interp in
  Pptactic.declare_extra_genarg_pprule wit gen_pr gen_pr gen_pr;
  wit

let interp_wit wit ist gl x = 
  let globarg = in_gen (glbwit wit) x in
  let sigma, arg =
    Tacinterp.interp_genarg
      ist (pf_env gl) (project gl) (pf_concl gl) gl.Evd.it globarg in
  sigma, out_gen (topwit wit) arg


open Constrarg
open Nameops
open Pp

type loc = Loc.t
 
let pr_id = Ppconstr.pr_id
let pr_name = function Name id -> pr_id id | Anonymous -> str "_"
let pr_spc () = str " "
let pr_bar () = Pp.cut() ++ str "|"
let pr_list = prlist_with_sep
let dummy_loc = Loc.ghost
let errorstrm = Errors.errorlabstrm "ssreflect"
let loc_error loc msg = Errors.user_err_loc (loc, msg, str msg)
let anomaly s = Errors.anomaly (str s)


(**************************** ssrhyp **************************************) 

(** Bound assumption argument *)

(* The Ltac API does have a type for assumptions but it is level-dependent *)
(* and therefore impractical to use for complex arguments, so we substitute *)
(* our own to have a uniform representation. Also, we refuse to intern     *)
(* idents that match global/section constants, since this would lead to    *)
(* fragile Ltac scripts.                                                   *)

type ssrhyp = SsrHyp of loc * identifier
let hyp_id (SsrHyp (_, id)) = id
let pr_hyp (SsrHyp (_, id)) = pr_id id
let pr_ssrhyp _ _ _ = pr_hyp

let wit_ssrhyprep = add_genarg "ssrhyprep" pr_hyp

let hyp_err loc msg id =
  Errors.user_err_loc (loc, "ssrhyp", str msg ++ pr_id id)

let not_section_id id = not (Termops.is_section_variable id)

let intern_hyp ist (SsrHyp (loc, id) as hyp) =
  let _ = Tacintern.intern_genarg ist (in_gen (rawwit wit_var) (loc, id)) in
  if not_section_id id then hyp else
  hyp_err loc "Can't clear section hypothesis " id

let interp_hyp ist gl (SsrHyp (loc, id)) =
  let s, id' = interp_wit wit_var ist gl (loc, id) in
  if not_section_id id' then s, SsrHyp (loc, id') else
  hyp_err loc "Can't clear section hypothesis " id'

ARGUMENT EXTEND ssrhyp TYPED AS ssrhyprep PRINTED BY pr_ssrhyp
                       INTERPRETED BY interp_hyp
                       GLOBALIZED BY intern_hyp
  | [ ident(id) ] -> [ SsrHyp (loc, id) ]
END

type ssrhyp_or_id = Hyp of ssrhyp | Id of ssrhyp

let hoik f = function Hyp x -> f x | Id x -> f x
let hoi_id = hoik hyp_id
let pr_hoi = hoik pr_hyp
let pr_ssrhoi _ _ _ = pr_hoi

let wit_ssrhoirep = add_genarg "ssrhoirep" pr_hoi

let intern_ssrhoi ist = function
  | Hyp h -> Hyp (intern_hyp ist h)
  | Id (SsrHyp (_, id)) as hyp ->
    let _ = Tacintern.intern_genarg ist (in_gen (rawwit wit_ident) id) in
    hyp

let interp_ssrhoi ist gl = function
  | Hyp h -> let s, h' = interp_hyp ist gl h in s, Hyp h'
  | Id (SsrHyp (loc, id)) ->
    let s, id' = interp_wit wit_ident ist gl id in
    s, Id (SsrHyp (loc, id'))

ARGUMENT EXTEND ssrhoi_hyp TYPED AS ssrhoirep PRINTED BY pr_ssrhoi
                       INTERPRETED BY interp_ssrhoi
                       GLOBALIZED BY intern_ssrhoi
  | [ ident(id) ] -> [ Hyp (SsrHyp(loc, id)) ]
END
ARGUMENT EXTEND ssrhoi_id TYPED AS ssrhoirep PRINTED BY pr_ssrhoi
                       INTERPRETED BY interp_ssrhoi
                       GLOBALIZED BY intern_ssrhoi
  | [ ident(id) ] -> [ Id (SsrHyp(loc, id)) ]
END

type ssrhyps = ssrhyp list

let pr_hyps = pr_list pr_spc pr_hyp
let pr_ssrhyps _ _ _ = pr_hyps
let hyps_ids = List.map hyp_id

let rec check_hyps_uniq ids = function
  | SsrHyp (loc, id) :: _ when List.mem id ids ->
    hyp_err loc "Duplicate assumption " id
  | SsrHyp (_, id) :: hyps -> check_hyps_uniq (id :: ids) hyps
  | [] -> ()

let check_hyp_exists hyps (SsrHyp(_, id)) =
  try ignore(Context.lookup_named id hyps)
  with Not_found -> errorstrm (str"No assumption is named " ++ pr_id id)

let test_hypname_exists hyps id =
  try ignore(Context.lookup_named id hyps); true
  with Not_found -> false

let interp_hyps ist gl ghyps =
  let hyps = List.map snd (List.map (interp_hyp ist gl) ghyps) in
  check_hyps_uniq [] hyps; Tacmach.project gl, hyps

ARGUMENT EXTEND ssrhyps TYPED AS ssrhyp list PRINTED BY pr_ssrhyps
                        INTERPRETED BY interp_hyps
  | [ ssrhyp_list(hyps) ] -> [ check_hyps_uniq [] hyps; hyps ]
END

(** Rewriting direction *)

type ssrdir = Ssrmatching.ssrdir = L2R | R2L

let pr_dir = function L2R -> str "->" | R2L -> str "<-"
let pr_rwdir = function L2R -> mt() | R2L -> str "-"

let wit_ssrdir = add_genarg "ssrdir" pr_dir

let dir_org = function L2R -> 1 | R2L -> 2









(** Simpl switch *)

type ssrsimpl = Simpl of int | Cut of int | SimplCut of int * int | Nop

let pr_simpl = function
  | Simpl -1 -> str "/="
  | Cut -1 -> str "//"
  | Simpl n -> str "/" ++ int n ++ str "="
  | Cut n -> str "/" ++ int n ++ str"/"
  | SimplCut (-1,-1) -> str "//="
  | SimplCut (n,-1) -> str "/" ++ int n ++ str "/="
  | SimplCut (-1,n) -> str "//" ++ int n ++ str "="
  | SimplCut (n,m) -> str "/" ++ int n ++ str "/" ++ int m ++ str "="
  | Nop -> mt ()

let pr_ssrsimpl _ _ _ = pr_simpl

let wit_ssrsimplrep = add_genarg "ssrsimplrep" pr_simpl

let test_ssrslashnum b1 b2 strm =
  match Compat.get_tok (Util.stream_nth 0 strm) with
  | Tok.KEYWORD "/" ->
      (match Compat.get_tok (Util.stream_nth 1 strm) with
      | Tok.INT _ when b1 ->
         (match Compat.get_tok (Util.stream_nth 2 strm) with
         | Tok.KEYWORD "=" | Tok.KEYWORD "/=" when not b2 -> ()
         | Tok.KEYWORD "/" ->
             if not b2 then () else begin
               match Compat.get_tok (Util.stream_nth 3 strm) with
               | Tok.INT _ -> ()
               | _ -> raise Stream.Failure
             end
         | _ -> raise Stream.Failure)
      | Tok.KEYWORD "/" when not b1 ->
         (match Compat.get_tok (Util.stream_nth 2 strm) with
         | Tok.KEYWORD "=" when not b2 -> ()
         | Tok.INT _ when b2 ->
           (match Compat.get_tok (Util.stream_nth 3 strm) with
           | Tok.KEYWORD "=" -> ()
           | _ -> raise Stream.Failure)
         | _ when not b2 -> ()
         | _ -> raise Stream.Failure)
      | Tok.KEYWORD "=" when not b1 && not b2 -> ()
      | _ -> raise Stream.Failure)
  | Tok.KEYWORD "//" when not b1 ->
         (match Compat.get_tok (Util.stream_nth 1 strm) with
         | Tok.KEYWORD "=" when not b2 -> ()
         | Tok.INT _ when b2 ->
           (match Compat.get_tok (Util.stream_nth 2 strm) with
           | Tok.KEYWORD "=" -> ()
           | _ -> raise Stream.Failure)
         | _ when not b2 -> ()
         | _ -> raise Stream.Failure)
  | _ -> raise Stream.Failure

let test_ssrslashnum10 = test_ssrslashnum true false
let test_ssrslashnum11 = test_ssrslashnum true true
let test_ssrslashnum01 = test_ssrslashnum false true
let test_ssrslashnum00 = test_ssrslashnum false false

let negate_parser f x =
  let rc = try Some (f x) with Stream.Failure -> None in
  match rc with
  | None -> ()
  | Some _ -> raise Stream.Failure 

let test_not_ssrslashnum =
  Pcoq.Gram.Entry.of_parser
    "test_not_ssrslashnum" (negate_parser test_ssrslashnum10)
let test_ssrslashnum00 =
  Pcoq.Gram.Entry.of_parser "test_ssrslashnum01" test_ssrslashnum00
let test_ssrslashnum10 =
  Pcoq.Gram.Entry.of_parser "test_ssrslashnum10" test_ssrslashnum10
let test_ssrslashnum11 =
  Pcoq.Gram.Entry.of_parser "test_ssrslashnum11" test_ssrslashnum11
let test_ssrslashnum01 =
  Pcoq.Gram.Entry.of_parser "test_ssrslashnum01" test_ssrslashnum01


ARGUMENT EXTEND ssrsimpl_ne TYPED AS ssrsimplrep PRINTED BY pr_ssrsimpl
| [ "//=" ] -> [ SimplCut (~-1,~-1) ]
| [ "/=" ] -> [ Simpl ~-1 ]
END

Pcoq.(Prim.(
GEXTEND Gram
  GLOBAL: ssrsimpl_ne;
  ssrsimpl_ne: [
    [ test_ssrslashnum11; "/"; n = natural; "/"; m = natural; "=" -> SimplCut(n,m)
    | test_ssrslashnum10; "/"; n = natural; "/" -> Cut n 
    | test_ssrslashnum10; "/"; n = natural; "=" -> Simpl n 
    | test_ssrslashnum10; "/"; n = natural; "/=" -> SimplCut (n,~-1) 
    | test_ssrslashnum10; "/"; n = natural; "/"; "=" -> SimplCut (n,~-1) 
    | test_ssrslashnum01; "//"; m = natural; "=" -> SimplCut (~-1,m)
    | test_ssrslashnum00; "//" -> Cut ~-1
    ]];

END
))

ARGUMENT EXTEND ssrsimpl TYPED AS ssrsimplrep PRINTED BY pr_ssrsimpl
| [ ssrsimpl_ne(sim) ] -> [ sim ]
| [ ] -> [ Nop ]
END


type ssrclear = ssrhyps

let pr_clear_ne clr = str "{" ++ pr_hyps clr ++ str "}"
let pr_clear sep clr = if clr = [] then mt () else sep () ++ pr_clear_ne clr

let pr_ssrclear _ _ _ = pr_clear mt

ARGUMENT EXTEND ssrclear_ne TYPED AS ssrhyps PRINTED BY pr_ssrclear
| [ "{" ne_ssrhyp_list(clr) "}" ] -> [ check_hyps_uniq [] clr; clr ]
END

ARGUMENT EXTEND ssrclear TYPED AS ssrclear_ne PRINTED BY pr_ssrclear
| [ ssrclear_ne(clr) ] -> [ clr ]
| [ ] -> [ [] ]
END


type ssrocc = Ssrmatching.occ

type ssrtermrep = char * Tacexpr.glob_constr_and_expr
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





open Locus
(****************************** tactics ***********************************)

let rewritetac dir c =
  (* Due to the new optional arg ?tac, application shouldn't be too partial *)
  Proofview.V82.of_tactic begin
    Equality.general_rewrite (dir = L2R) AllOccurrences true false c
  end

(******************************* hooks ************************************)

type name_hint = (int * Constr.types array) option ref

type simplest_newcase = ?ind:name_hint -> Constr.t -> tactic
let simplest_newcase_tac, simplest_newcase = Hook.make ()

type ipat_rewrite = Ssrmatching.occ -> ssrdir -> Constr.t -> tactic
let ipat_rewrite_tac, ipat_rewrite =
  Hook.make ~default:(fun _ -> rewritetac) ()

type move_top_with_view =
  next:ssripats ref -> bool -> Id.t ref -> bool * ssrtermrep list -> ist ->
    tac_ctx tac_a
let move_top_with_view_tac, move_top_with_view = Hook.make ()

(* vim: set filetype=ocaml foldmethod=marker: *)

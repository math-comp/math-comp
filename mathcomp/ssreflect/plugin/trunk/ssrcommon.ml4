(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)

open Names
open Proof_type
open Evd
open Tacmach
open Refiner

DECLARE PLUGIN "ssreflect"

(* Defining grammar rules with "xx" in it automatically declares keywords too,
 * we thus save the lexer to restore it at the end of the file *)
let frozen_lexer = Lexer.freeze () ;;


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

(* Tentative patch from util.ml *)

let array_fold_right_from n f v a =
  let rec fold n =
    if n >= Array.length v then a else f v.(n) (fold (succ n))
  in
  fold n

let array_app_tl v l =
  if Array.length v = 0 then invalid_arg "array_app_tl";
  array_fold_right_from 1 (fun e l -> e::l) v l

let array_list_of_tl v =
  if Array.length v = 0 then invalid_arg "array_list_of_tl";
  array_fold_right_from 1 (fun e l -> e::l) v []

(* end patch *)

(** Primitive parsing to avoid syntax conflicts with basic tactics. *)

let accept_before_syms syms strm =
  match Compat.get_tok (Util.stream_nth 1 strm) with
  | Tok.KEYWORD sym when List.mem sym syms -> ()
  | _ -> raise Stream.Failure

let accept_before_syms_or_any_id syms strm =
  match Compat.get_tok (Util.stream_nth 1 strm) with
  | Tok.KEYWORD sym when List.mem sym syms -> ()
  | Tok.IDENT _ -> ()
  | _ -> raise Stream.Failure

let accept_before_syms_or_ids syms ids strm =
  match Compat.get_tok (Util.stream_nth 1 strm) with
  | Tok.KEYWORD sym when List.mem sym syms -> ()
  | Tok.IDENT id when List.mem id ids -> ()
  | _ -> raise Stream.Failure


let (!@) = Compat.to_coqloc

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

type ssrdir = L2R | R2L

let pr_dir = function L2R -> str "->" | R2L -> str "<-"
let pr_rwdir = function L2R -> mt() | R2L -> str "-"

let wit_ssrdir = add_genarg "ssrdir" pr_dir

let dir_org = function L2R -> 1 | R2L -> 2

let pr_dir_side = function L2R -> str "LHS" | R2L -> str "RHS"
let inv_dir = function L2R -> R2L | R2L -> L2R

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

(** Indexes *)

(* Since SSR indexes are always positive numbers, we use the 0 value *)
(* to encode an omitted index. We reuse the in or_var type, but we   *)
(* supply our own interpretation function, which checks for non      *)
(* positive values, and allows the use of constr numerals, so that   *)
(* e.g., "let n := eval compute in (1 + 3) in (do n!clear)" works.   *)

type ssrindex = int Misctypes.or_var

let pr_index = function
  | Misctypes.ArgVar (_, id) -> pr_id id
  | Misctypes.ArgArg n when n > 0 -> int n
  | _ -> mt ()
let pr_ssrindex _ _ _ = pr_index

let noindex = Misctypes.ArgArg 0

let check_index loc i =
  if i > 0 then i else loc_error loc "Index not positive"
let mk_index loc = function
  | Misctypes.ArgArg i -> Misctypes.ArgArg (check_index loc i)
  | iv -> iv

let interp_index ist gl idx =
  Tacmach.project gl, 
  match idx with
  | Misctypes.ArgArg _ -> idx
  | Misctypes.ArgVar (loc, id) ->
    let i =
      try
        let v = Id.Map.find id ist.Tacinterp.lfun in
        begin match Tacinterp.Value.to_int v with
        | Some i -> i
        | None ->
        begin match Tacinterp.Value.to_constr v with
        | Some c ->
          let rc = Detyping.detype false [] (pf_env gl) (project gl) c in
          begin match Notation.uninterp_prim_token rc with
          | _, Constrexpr.Numeral bigi -> int_of_string (Bigint.to_string bigi)
          | _ -> raise Not_found
          end
        | None -> raise Not_found
        end end
    with _ -> loc_error loc "Index not a number" in
    Misctypes.ArgArg (check_index loc i)

ARGUMENT EXTEND ssrindex TYPED AS int_or_var PRINTED BY pr_ssrindex
  INTERPRETED BY interp_index
| [ int_or_var(i) ] -> [ mk_index loc i ]
END


(** Occurrence switch *)

(* The standard syntax of complemented occurrence lists involves a single *)
(* initial "-", e.g., {-1 3 5}. An initial                                *)
(* "+" may be used to indicate positive occurrences (the default). The    *)
(* "+" is optional, except if the list of occurrences starts with a       *)
(* variable or is empty (to avoid confusion with a clear switch). The     *)
(* empty positive switch "{+}" selects no occurrences, while the empty    *)
(* negative switch "{-}" selects all occurrences explicitly; this is the  *)
(* default, but "{-}" prevents the implicit clear, and can be used to     *)
(* force dependent elimination -- see ndefectelimtac below.               *)

type ssrocc = (bool * int list) option

let pr_occ = function
  | Some (true, occ) -> str "{-" ++ pr_list pr_spc int occ ++ str "}"
  | Some (false, occ) -> str "{+" ++ pr_list pr_spc int occ ++ str "}"
  | None -> str "{}"

let pr_ssrocc _ _ _ = pr_occ

ARGUMENT EXTEND ssrocc TYPED AS (bool * int list) option PRINTED BY pr_ssrocc
| [ natural(n) natural_list(occ) ] -> [
     Some (false, List.map (check_index loc) (n::occ)) ]
| [ "-" natural_list(occ) ]     -> [ Some (true, occ) ]
| [ "+" natural_list(occ) ]     -> [ Some (false, occ) ]
END

let allocc = Some(false,[])

(* modality *)

type ssrmmod = May | Must | Once

let pr_mmod = function May -> str "?" | Must -> str "!" | Once -> mt ()

let wit_ssrmmod = add_genarg "ssrmmod" pr_mmod
let ssrmmod = Pcoq.create_generic_entry "ssrmmod" (Genarg.rawwit wit_ssrmmod);;

Pcoq.(Prim.(
GEXTEND Gram
  GLOBAL: ssrmmod;
  ssrmmod: [[ "!" -> Must | LEFTQMARK -> May | "?" -> May]];
END
))

(** Rewrite multiplier: !n ?n *)

type ssrmult = int * ssrmmod

let notimes = 0
let nomult = 1, Once

let pr_mult (n, m) =
  if n > 0 && m <> Once then int n ++ pr_mmod m else pr_mmod m

let pr_ssrmult _ _ _ = pr_mult

ARGUMENT EXTEND ssrmult_ne TYPED AS int * ssrmmod PRINTED BY pr_ssrmult
  | [ natural(n) ssrmmod(m) ] -> [ check_index loc n, m ]
  | [ ssrmmod(m) ]            -> [ notimes, m ]
END

ARGUMENT EXTEND ssrmult TYPED AS ssrmult_ne PRINTED BY pr_ssrmult
  | [ ssrmult_ne(m) ] -> [ m ]
  | [ ] -> [ nomult ]
END

(** Discharge occ switch (combined occurrence / clear switch *)

type ssrdocc = ssrclear option * ssrocc

let mkocc occ = None, occ
let noclr = mkocc None
let mkclr clr  = Some clr, None
let nodocc = mkclr []

let pr_docc = function
  | None, occ -> pr_occ occ
  | Some clr, _ -> pr_clear mt clr

let pr_ssrdocc _ _ _ = pr_docc

ARGUMENT EXTEND ssrdocc TYPED AS ssrclear option * ssrocc PRINTED BY pr_ssrdocc
| [ "{" ne_ssrhyp_list(clr) "}" ] -> [ mkclr clr ]
| [ "{" ssrocc(occ) "}" ] -> [ mkocc occ ]
END

(* kinds of terms *)

type ssrtermkind = InParens | WithAt | NoFlag | Cpattern

let input_ssrtermkind strm = match Compat.get_tok (Util.stream_nth 0 strm) with
  | Tok.KEYWORD "(" -> InParens
  | Tok.KEYWORD "@" -> WithAt
  | _ -> NoFlag

let ssrtermkind = Pcoq.Gram.Entry.of_parser "ssrtermkind" input_ssrtermkind

(* terms *)
type ssrterm = ssrtermkind * Tacexpr.glob_constr_and_expr

(** Terms parsing. ********************************************************)

let glob_constr ist genv = function
  | _, Some ce ->
    let vars = Id.Map.fold (fun x _ accu -> Id.Set.add x accu) ist.Tacinterp.lfun Id.Set.empty in
    let ltacvars = {
      Constrintern.empty_ltac_sign with Constrintern.ltac_vars = vars } in
    Constrintern.intern_gen Pretyping.WithoutTypeConstraint ~ltacvars genv ce
  | rc, None -> rc

let interp_constr = interp_wit wit_constr

let interp_open_constr ist gl gc =
  interp_wit wit_open_constr ist gl ((), gc)

let mkRHole = Glob_term.GHole (dummy_loc, Evar_kinds.InternalHole, Misctypes.IntroAnonymous, None)

let mk_term k c = k, (mkRHole, Some c)
let mk_lterm c = mk_term NoFlag c



(* Term printing utilities functions for deciding bracketing.  *)
let pr_paren prx x = hov 1 (str "(" ++ prx x ++ str ")")
(* String lexing utilities *)
let skip_wschars s =
  let rec loop i = match s.[i] with '\n'..' ' -> loop (i + 1) | _ -> i in loop
(* We also guard characters that might interfere with the ssreflect   *)
(* tactic syntax.                                                     *)
let guard_term ch1 s i = match s.[i] with
  | '(' -> false
  | '{' | '/' | '=' -> true
  | _ -> ch1 = InParens
(* We also guard characters that might interfere with the ssreflect   *)
(* tactic syntax.                                                     *)
let pr_guarded guard prc c =
  msg_with Format.str_formatter (prc c);
  let s = Format.flush_str_formatter () ^ "$" in
  if guard s (skip_wschars s 0) then pr_paren prc c else prc c

let prl_constr_expr = Ppconstr.pr_lconstr_expr
let pr_glob_constr c = Printer.pr_glob_constr_env (Global.env ()) c
let prl_glob_constr c = Printer.pr_lglob_constr_env (Global.env ()) c
let prl_glob_constr_and_expr = function
  | _, Some c -> prl_constr_expr c
  | c, None -> Printer.pr_lglob_constr c
let pr_glob_constr_and_expr = function
  | _, Some c -> Ppconstr.pr_constr_expr c
  | c, None -> pr_glob_constr c
let pr_term (k, c) = pr_guarded (guard_term k) pr_glob_constr_and_expr c
let prl_term (k, c) = pr_guarded (guard_term k) prl_glob_constr_and_expr c


(* Because we allow wildcards in term references, we need to stage the *)
(* interpretation of terms so that it occurs at the right time during  *)
(* the execution of the tactic (e.g., so that we don't report an error *)
(* for a term that isn't actually used in the execution).              *)
(*   The term representation tracks whether the concrete initial term  *)
(* started with an opening paren, which might avoid a conflict between *)
(* the ssrreflect term syntax and Gallina notation.                    *)

(* terms *)
let pr_ssrterm _ _ _ = pr_term
let pf_intern_term ist gl (_, c) = glob_constr ist (pf_env gl) c
let intern_term ist env (_, c) = glob_constr ist env c
let interp_term ist gl (_, c) = snd (interp_open_constr ist gl c)
let force_term ist gl (_, c) = interp_constr ist gl c
let glob_ssrterm gs = function
  | k, (_, Some c) -> k, Tacintern.intern_constr gs c
  | ct -> ct
let subst_ssrterm s (k, c) = k, Tacsubst.subst_glob_constr_and_expr s c
let interp_ssrterm _ gl t = Tacmach.project gl, t

ARGUMENT EXTEND ssrterm
     PRINTED BY pr_ssrterm
     INTERPRETED BY interp_ssrterm
     GLOBALIZED BY glob_ssrterm SUBSTITUTED BY subst_ssrterm
     RAW_TYPED AS cpattern RAW_PRINTED BY pr_ssrterm
     GLOB_TYPED AS cpattern GLOB_PRINTED BY pr_ssrterm
| [ "YouShouldNotTypeThis" constr(c) ] -> [ mk_lterm c ]
END


Pcoq.(Prim.(
GEXTEND Gram
  GLOBAL: ssrterm;
  ssrterm: [[ k = ssrtermkind; c = Pcoq.Constr.constr -> mk_term k c ]];
END
))

(* Views *)

type ssrview = ssrterm list

let pr_view = pr_list mt (fun c -> str "/" ++ pr_term c)

let pr_ssrview _ _ _ = pr_view

ARGUMENT EXTEND ssrview TYPED AS ssrterm list
   PRINTED BY pr_ssrview
| [ "YouShouldNotTypeThis" ] -> [ [] ]
END

Pcoq.(
GEXTEND Gram
  GLOBAL: ssrview;
  ssrview: [
    [  test_not_ssrslashnum; "/"; c = Pcoq.Constr.constr -> [mk_term NoFlag c]
    |  test_not_ssrslashnum; "/"; c = Pcoq.Constr.constr; w = ssrview ->
                    (mk_term NoFlag c) :: w ]];
END
)

(* }}} *)
 
(* ipats *)

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

let remove_loc = snd

let ipat_of_intro_pattern p = Misctypes.(
  let rec ipat_of_intro_pattern = function
    | IntroNaming (IntroIdentifier id) -> IpatId id
    | IntroAction IntroWildcard -> IpatWild
    | IntroAction (IntroOrAndPattern iorpat) ->
      IpatCase (`Regular
        (List.map (List.map ipat_of_intro_pattern) 
  	 (List.map (List.map remove_loc) iorpat)))
    | IntroNaming IntroAnonymous -> IpatAnon
    | IntroAction (IntroRewrite b) -> IpatRw (allocc, if b then L2R else R2L)
    | IntroNaming (IntroFresh id) -> IpatAnon
    | IntroAction (IntroApplyOn _) -> (* to do *) Errors.error "TO DO"
    | IntroAction (IntroInjection ips) ->
        IpatInj [List.map ipat_of_intro_pattern (List.map remove_loc ips)]
    | IntroForthcoming _ ->
        (* Unable to determine which kind of ipat interp_introid could
         * return [HH] *)
        assert false
  in
  ipat_of_intro_pattern p
)

let rec pr_ipat p = Misctypes.(
  match p with
  | IpatId id -> pr_id id
  | IpatSimpl (clr, sim) -> pr_clear mt clr ++ pr_simpl sim
  | IpatCase (`Regular iorpat) -> hov 1 (str "[" ++ pr_iorpat iorpat ++ str "]")
  | IpatCase (`Block(before,seed,after)) ->
       hov 1 (str "[" ++ pr_iorpat before
                      ++ pr_seed before seed
                      ++ pr_iorpat after ++ str "]")
  | IpatSeed s -> pr_seed [] s
  | IpatInj iorpat -> hov 1 (str "[=" ++ pr_iorpat iorpat ++ str "]")
  | IpatRw (occ, dir) -> pr_occ occ ++ pr_dir dir
  | IpatAll -> str "*"
  | IpatWild -> str "_"
  | IpatAnon -> str "?"
  | IpatView v -> pr_view v
  | IpatNoop -> str "-"
  | IpatNewHidden l -> str "[:" ++ pr_list spc pr_id l ++ str "]"
  | IpatFastMode -> str ">"
  | IpatTmpId -> str "+"
)
and pr_space_notFM = function IpatFastMode :: _ -> str"" | _ -> str" "
and pr_iorpat iorpat = pr_list pr_bar pr_ipats iorpat
and pr_ipats ipats = pr_space_notFM ipats ++ pr_list spc pr_ipat ipats
and pr_seed before seed =
  (if before <> [] then str"|" else str"") ++
  match seed with
  | `Id(id,side) -> str"^" ++ str(if side = `Post then "~" else "") ++ pr_id id
  | `Anon -> str "^ ? "
  | `Wild -> str "^ _ "

let wit_ssripatrep = add_genarg "ssripatrep" pr_ipat

let pr_ssripat _ _ _ = pr_ipat
let pr_ssripats _ _ _ = pr_ipats
let pr_ssriorpat _ _ _ = pr_iorpat

let intern_ipat ist ipat =
  let rec check_pat = function
  | IpatSimpl (clr, _) -> ignore (List.map (intern_hyp ist) clr)
  | IpatCase (`Regular iorpat) -> List.iter (List.iter check_pat) iorpat
  | IpatCase (`Block (before,_,after)) ->
       List.iter (List.iter check_pat) (before @ after)
  | IpatInj iorpat -> List.iter (List.iter check_pat) iorpat
  | _ -> () in
  check_pat ipat; ipat

let intern_ipats ist = List.map (intern_ipat ist)

let interp_intro_pattern = interp_wit wit_intro_pattern

let interp_introid ist gl id = Misctypes.(
 try IntroNaming (IntroIdentifier (hyp_id (snd (interp_hyp ist gl (SsrHyp (dummy_loc, id))))))
 with _ -> snd(snd (interp_intro_pattern ist gl (dummy_loc,IntroNaming (IntroIdentifier id))))
)

let rec add_intro_pattern_hyps (loc, ipat) hyps = Misctypes.(
  match ipat with
  | IntroNaming (IntroIdentifier id) ->
    if not_section_id id then SsrHyp (loc, id) :: hyps else
    hyp_err loc "Can't delete section hypothesis " id
  | IntroAction IntroWildcard -> hyps
  | IntroAction (IntroOrAndPattern iorpat) ->
    List.fold_right (List.fold_right add_intro_pattern_hyps) iorpat hyps
  | IntroNaming IntroAnonymous -> []
  | IntroNaming (IntroFresh _) -> []
  | IntroAction (IntroRewrite _) -> hyps
  | IntroAction (IntroInjection ips) -> List.fold_right add_intro_pattern_hyps ips hyps
  | IntroAction (IntroApplyOn (c,pat)) -> add_intro_pattern_hyps pat hyps
  | IntroForthcoming _ -> 
    (* As in ipat_of_intro_pattern, was unable to determine which kind
      of ipat interp_introid could return [HH] *) assert false
)

let rec interp_ipat ist gl = Misctypes.(
  let ltacvar id = Id.Map.mem id ist.Tacinterp.lfun in
  let interp_seed = function
    | (`Anon | `Wild) as x -> x
    | `Id(id,side) ->
        match interp_introid ist gl id with
        | IntroNaming (IntroIdentifier id) -> `Id(id,side)
        | _ -> `Id(Id.of_string "_",`Pre) in
  let rec interp = function
  | IpatId id when ltacvar id ->
    ipat_of_intro_pattern (interp_introid ist gl id)
  | IpatSimpl (clr, sim) ->
    let add_hyps (SsrHyp (loc, id) as hyp) hyps =
      if not (ltacvar id) then hyp :: hyps else
      add_intro_pattern_hyps (loc, (interp_introid ist gl id)) hyps in
    let clr' = List.fold_right add_hyps clr [] in
    check_hyps_uniq [] clr'; IpatSimpl (clr', sim)
  | IpatCase(`Regular iorpat) ->
      IpatCase(`Regular(List.map (List.map interp) iorpat))
  | IpatCase(`Block (before,seed,after)) ->
      let before = List.map (List.map interp) before in
      let seed = interp_seed seed in
      let after = List.map (List.map interp) after in
      IpatCase(`Block (before,seed,after))
  | IpatSeed s -> IpatSeed (interp_seed s)
  | IpatInj iorpat -> IpatInj (List.map (List.map interp) iorpat)
  | IpatNewHidden l ->
      IpatNewHidden
        (List.map (function
           | IntroNaming (IntroIdentifier id) -> id
           | _ -> assert false)
        (List.map (interp_introid ist gl) l))
  | ipat -> ipat in
  interp
)

let interp_ipats ist gl l = project gl, List.map (interp_ipat ist gl) l

let pushIpatRw = function
  | pats :: orpat -> (IpatRw (allocc, L2R) :: pats) :: orpat
  | [] -> []

let pushIpatNoop = function
  | pats :: orpat -> (IpatNoop :: pats) :: orpat
  | [] -> []

ARGUMENT EXTEND ssripat TYPED AS ssripatrep list PRINTED BY pr_ssripats
  INTERPRETED BY interp_ipats
  GLOBALIZED BY intern_ipats
  | [ "_" ] -> [ [IpatWild] ]
  | [ "*" ] -> [ [IpatAll] ]
  | [ "^" "*" ] -> [ [IpatFastMode] ]
  | [ "^" "_" ] -> [ [IpatSeed `Wild] ]
  | [ "^_" ] -> [ [IpatSeed `Wild] ]
  | [ "^" "?" ] -> [ [IpatSeed `Anon] ]
  | [ "^?" ] -> [ [IpatSeed `Anon] ]
  | [ "^" ident(id) ] -> [ [IpatSeed (`Id(id,`Pre))] ]
  | [ "^" "~" ident(id) ] -> [ [IpatSeed (`Id(id,`Post))] ]
  | [ "^~" ident(id) ] -> [ [IpatSeed (`Id(id,`Post))] ]
  | [ ident(id) ] -> [ [IpatId id] ]
  | [ "?" ] -> [ [IpatAnon] ]
  | [ "+" ] -> [ [IpatTmpId] ]
  | [ ssrsimpl_ne(sim) ] -> [ [IpatSimpl ([], sim)] ]
  | [ ssrdocc(occ) "->" ] -> [ match occ with
      | None, occ -> [IpatRw (occ, L2R)]
      | Some clr, _ -> [IpatSimpl (clr, Nop); IpatRw (allocc, L2R)]]
  | [ ssrdocc(occ) "<-" ] -> [ match occ with
      | None, occ ->  [IpatRw (occ, R2L)]
      | Some clr, _ -> [IpatSimpl (clr, Nop); IpatRw (allocc, R2L)]]
  | [ ssrdocc(occ) ] -> [ match occ with
      | Some cl, _ -> check_hyps_uniq [] cl; [IpatSimpl (cl, Nop)]
      | _ -> loc_error loc "Only identifiers are allowed here"]
  | [ "->" ] -> [ [IpatRw (allocc, L2R)] ]
  | [ "<-" ] -> [ [IpatRw (allocc, R2L)] ]
  | [ "-" ] -> [ [IpatNoop] ]
  | [ "-/" "=" ] -> [ [IpatNoop;IpatSimpl([],Simpl ~-1)] ]
  | [ "-/=" ] -> [ [IpatNoop;IpatSimpl([],Simpl ~-1)] ]
  | [ "-/" "/" ] -> [ [IpatNoop;IpatSimpl([],Cut ~-1)] ]
  | [ "-//" ] -> [ [IpatNoop;IpatSimpl([],Cut ~-1)] ]
  | [ "-/" integer(n) "/" ] -> [ [IpatNoop;IpatSimpl([],Cut n)] ]
  | [ "-/" "/=" ] -> [ [IpatNoop;IpatSimpl([],SimplCut (~-1,~-1))] ]
  | [ "-//" "=" ] -> [ [IpatNoop;IpatSimpl([],SimplCut (~-1,~-1))] ]
  | [ "-//=" ] -> [ [IpatNoop;IpatSimpl([],SimplCut (~-1,~-1))] ]
  | [ "-/" integer(n) "/=" ] -> [ [IpatNoop;IpatSimpl([],SimplCut (n,~-1))] ]
  | [ "-/" integer(n) "/" integer (m) "=" ] ->
      [ [IpatNoop;IpatSimpl([],SimplCut(n,m))] ]
  | [ ssrview(v) ] -> [ [IpatView v] ]
  | [ "[" ":" ident_list(idl) "]" ] -> [ [IpatNewHidden idl] ]
  | [ "[:" ident_list(idl) "]" ] -> [ [IpatNewHidden idl] ]
END

ARGUMENT EXTEND ssripats TYPED AS ssripat PRINTED BY pr_ssripats
  | [ ssripat(i) ssripats(tl) ] -> [ i @ tl ]
  | [ ] -> [ [] ]
END

ARGUMENT EXTEND ssriorpat TYPED AS ssripat list PRINTED BY pr_ssriorpat
| [ ssripats(pats) "|" ssriorpat(orpat) ] -> [ pats :: orpat ]
| [ ssripats(pats) "|-" ">" ssriorpat(orpat) ] -> [ pats :: pushIpatRw orpat ]
| [ ssripats(pats) "|-" ssriorpat(orpat) ] -> [ pats :: pushIpatNoop orpat ]
| [ ssripats(pats) "|->" ssriorpat(orpat) ] -> [ pats :: pushIpatRw orpat ]
| [ ssripats(pats) "||" ssriorpat(orpat) ] -> [ pats :: [] :: orpat ]
| [ ssripats(pats) "|||" ssriorpat(orpat) ] -> [ pats :: [] :: [] :: orpat ]
| [ ssripats(pats) "||||" ssriorpat(orpat) ] -> [ [pats; []; []; []] @ orpat ]
| [ ssripats(pats) ] -> [ [pats] ]
END

let reject_ssrhid strm =
  match Compat.get_tok (Util.stream_nth 0 strm) with
  | Tok.KEYWORD "[" ->
      (match Compat.get_tok (Util.stream_nth 1 strm) with
      | Tok.KEYWORD ":" -> raise Stream.Failure
      | _ -> ())
  | _ -> ()

let test_nohidden = Pcoq.Gram.Entry.of_parser "test_ssrhid" reject_ssrhid

ARGUMENT EXTEND ssrcpat TYPED AS ssripatrep PRINTED BY pr_ssripat
  | [ "YouShouldNotTypeThis" ssriorpat(x) ] -> [ IpatCase(`Regular x) ]
END

let understand_case_type ior =
  let rec aux before = function
    | [] -> `Regular (List.rev before)
    | [IpatSeed seed] :: rest -> `Block(List.rev before, seed, rest)
    | ips :: rest -> aux (ips :: before) rest
  in
    aux [] ior

let rec check_no_inner_seed loc seen = function
  | [] -> ()
  | x :: xs ->
     let in_x = List.exists (function IpatSeed _ -> true | _ -> false) x in
     if seen && in_x then
        Errors.user_err_loc (loc, "ssreflect",
            strbrk "Only one block ipat per elimination is allowed")
     else if List.length x < 2 ||
        List.for_all (function
          | IpatSeed _ -> false
          | IpatInj l | IpatCase (`Regular l) ->
              check_no_inner_seed loc false l; true
          | IpatCase (`Block(before,_,after)) ->
              check_no_inner_seed loc false before;
              check_no_inner_seed loc false after; true
          | _ -> true) x
     then check_no_inner_seed loc (seen || in_x) xs
     else Errors.user_err_loc (loc, "ssreflect",
            strbrk "Mixing block and regular ipat is forbidden")
;;

Pcoq.(
GEXTEND Gram
  GLOBAL: ssrcpat;
  ssrcpat: [
   [ test_nohidden; "["; iorpat = ssriorpat; "]" ->
      check_no_inner_seed !@loc false iorpat;
      IpatCase (understand_case_type iorpat)
   | test_nohidden; "[="; iorpat = ssriorpat; "]" ->
      check_no_inner_seed !@loc false iorpat;
      IpatInj iorpat ]];
END
);;

Pcoq.(
GEXTEND Gram
  GLOBAL: ssripat;
  ssripat: [[ pat = ssrcpat -> [pat] ]];
END
)

ARGUMENT EXTEND ssripats_ne TYPED AS ssripat PRINTED BY pr_ssripats
  | [ ssripat(i) ssripats(tl) ] -> [ i @ tl ]
END

(* subsets of patterns *)

type ssrhpats = ((ssrclear * ssripats) * ssripats) * ssripats

let check_ssrhpats loc w_binders ipats =
  let err_loc s = Errors.user_err_loc (loc, "ssreflect", s) in
  let clr, ipats =
    let rec aux clr = function
      | IpatSimpl (cl, Nop) :: tl -> aux (clr @ cl) tl
      | IpatSimpl (cl, sim) :: tl -> clr @ cl, IpatSimpl ([], sim) :: tl
      | tl -> clr, tl
    in aux [] ipats in
  let simpl, ipats = 
    match List.rev ipats with
    | IpatSimpl ([],_) as s :: tl -> [s], List.rev tl
    | _ -> [],  ipats in
  if simpl <> [] && not w_binders then
    err_loc (str "No s-item allowed here: " ++ pr_ipats simpl);
  let ipat, binders =
    let rec loop ipat = function
      | [] -> ipat, []
      | ( IpatId _| IpatAnon| IpatCase _| IpatRw _ as i) :: tl -> 
        if w_binders then
          if simpl <> [] && tl <> [] then 
            err_loc(str"binders XOR s-item allowed here: "++pr_ipats(tl@simpl))
          else if not (List.for_all (function IpatId _ -> true | _ -> false) tl)
          then err_loc (str "Only binders allowed here: " ++ pr_ipats tl)
          else ipat @ [i], tl
        else
          if tl = [] then  ipat @ [i], []
          else err_loc (str "No binder or s-item allowed here: " ++ pr_ipats tl)
      | hd :: tl -> loop (ipat @ [hd]) tl
    in loop [] ipats in
  ((clr, ipat), binders), simpl

let single loc =
  function [x] -> x | _ -> loc_error loc "Only one intro pattern is allowed"

let pr_hpats (((clr, ipat), binders), simpl) =
   pr_clear mt clr ++ pr_ipats ipat ++ pr_ipats binders ++ pr_ipats simpl
let pr_ssrhpats _ _ _ = pr_hpats
let pr_ssrhpats_wtransp _ _ _ (_, x) = pr_hpats x

ARGUMENT EXTEND ssrhpats TYPED AS ((ssrclear * ssripat) * ssripat) * ssripat
PRINTED BY pr_ssrhpats
  | [ ssripats(i) ] -> [ check_ssrhpats loc true i ]
END

type ssrhpats_wtransp = bool * ssrhpats

ARGUMENT EXTEND ssrhpats_wtransp
  TYPED AS bool * (((ssrclear * ssripats) * ssripats) * ssripats)
  PRINTED BY pr_ssrhpats_wtransp
  | [ ssripats(i) ] -> [ false,check_ssrhpats loc true i ]
  | [ ssripats(i) "@" ssripats(j) ] -> [ true,check_ssrhpats loc true (i @ j) ]
END

ARGUMENT EXTEND ssrhpats_nobs 
TYPED AS ((ssrclear * ssripats) * ssripats) * ssripats PRINTED BY pr_ssrhpats
  | [ ssripats(i) ] -> [ check_ssrhpats loc false i ]
END

ARGUMENT EXTEND ssrrpat TYPED AS ssripatrep PRINTED BY pr_ssripat
  | [ "->" ] -> [ IpatRw (allocc, L2R) ]
  | [ "<-" ] -> [ IpatRw (allocc, R2L) ]
END

type ssrintros = ssripats

let pr_intros sep intrs =
  if intrs = [] then mt() else sep () ++ str "=>" ++ pr_ipats intrs
let pr_ssrintros _ _ _ = pr_intros mt

ARGUMENT EXTEND ssrintros_ne TYPED AS ssripat
 PRINTED BY pr_ssrintros
  | [ "=>" ssripats_ne(pats) ] -> [ pats ]
  | [ "=>" ">" ssripats_ne(pats) ] -> [ IpatFastMode :: pats ]
  | [ "=>>" ssripats_ne(pats) ] -> [ IpatFastMode :: pats ]
END

ARGUMENT EXTEND ssrintros TYPED AS ssrintros_ne PRINTED BY pr_ssrintros
  | [ ssrintros_ne(intrs) ] -> [ intrs ]
  | [ ] -> [ [] ]
END


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

type ipat_rewrite = ssrocc -> ssrdir -> Constr.t -> tactic
let ipat_rewrite_tac, ipat_rewrite =
  Hook.make ~default:(fun _ -> rewritetac) ()

type move_top_with_view =
  next:ssripats ref -> bool -> Id.t ref -> bool * ssrterm list -> ist ->
    tac_ctx tac_a
let move_top_with_view_tac, move_top_with_view = Hook.make ()

(* We wipe out all the keywords generated by the grammar rules we defined. *)
(* The user is supposed to Require Import ssreflect or Require ssreflect   *)
(* and Import ssreflect.SsrSyntax to obtain these keywords and as a         *)
(* consequence the extended ssreflect grammar.                             *)
let () = Lexer.unfreeze frozen_lexer ;;

(* vim: set filetype=ocaml foldmethod=marker: *)

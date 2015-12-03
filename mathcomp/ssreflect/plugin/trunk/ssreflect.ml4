(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)

(* This line is read by the Makefile's dist target: do not remove. *)
DECLARE PLUGIN "ssreflect"
let ssrversion = "1.5";;
let ssrAstVersion = 1;;
let () = Mltop.add_known_plugin (fun () ->
  if Flags.is_verbose () && not !Flags.batch_mode then begin
    Printf.printf "\nSmall Scale Reflection version %s loaded.\n" ssrversion;
    Printf.printf "Copyright 2005-2014 Microsoft Corporation and INRIA.\n";
    Printf.printf "Distributed under the terms of the CeCILL-B license.\n\n"
  end;
  (* Disable any semantics associated with bullets *)
  Goptions.set_string_option_value_gen
    (Some false) ["Bullet";"Behavior"] "None")
  "ssreflect"
;;

(* Defining grammar rules with "xx" in it automatically declares keywords too,
 * we thus save the lexer to restore it at the end of the file *)
let frozen_lexer = Lexer.freeze () ;;

(*i camlp4use: "pa_extend.cmo" i*)
(*i camlp4deps: "grammar/grammar.cma" i*)

open Names
open Pp
open Pcoq
open Genarg
open Stdarg
open Constrarg
open Term
open Vars
open Context
open Topconstr
open Libnames
open Tactics
open Tacticals
open Termops
open Namegen
open Recordops
open Tacmach
open Coqlib
open Glob_term
open Util
open Evd
open Sigma.Notations
open Extend
open Goptions
open Tacexpr
open Tacinterp
open Pretyping
open Constr
open Tactic
open Extraargs
open Ppconstr
open Printer

open Globnames
open Misctypes
open Decl_kinds
open Evar_kinds
open Constrexpr
open Constrexpr_ops
open Notation_term
open Notation_ops
open Locus
open Locusops

open Compat
open Tok

open Ssrmatching
open Ssrcommon

(* Forward references to tactics used everywhere in the language *)
let simplest_newcase ?ind x gl = Hook.get simplest_newcase_tac ?ind x gl
let ipat_rewrite occ dir gl = Hook.get ipat_rewrite_tac occ dir gl
let move_top_with_view ~next c r v ist gl =
  Hook.get move_top_with_view_tac ~next c r v ist gl

module Intset = Evar.Set

(** look up a name in the ssreflect internals module *)
let ssrdirpath = make_dirpath [id_of_string "ssreflect"]
let ssrqid name = make_qualid ssrdirpath (id_of_string name) 
let ssrtopqid name = make_short_qualid (id_of_string name) 
let locate_reference qid =
  Smartlocate.global_of_extended_global (Nametab.locate_extended qid)
let mkSsrRef name =
  try locate_reference (ssrqid name) with Not_found ->
  try locate_reference (ssrtopqid name) with Not_found ->
  Errors.error "Small scale reflection library not loaded"
let mkSsrRRef name = GRef (dummy_loc, mkSsrRef name,None), None
let mkSsrConst name env sigma =
  Evd.fresh_global env sigma (mkSsrRef name)
let pf_mkSsrConst name gl =
  let sigma, env, it = project gl, pf_env gl, sig_it gl in
  let sigma, t = mkSsrConst name env sigma in
  t, re_sig it sigma
let pf_fresh_global name gl =
  let sigma, env, it = project gl, pf_env gl, sig_it gl in
  let sigma,t  = Evd.fresh_global env sigma name in
  t, re_sig it sigma

(** Ssreflect load check. *)

(* To allow ssrcoq to be fully compatible with the "plain" Coq, we only *)
(* turn on its incompatible features (the new rewrite syntax, and the   *)
(* reserved identifiers) when the theory library (ssreflect.v) has      *)
(* has actually been required, or is being defined. Because this check  *)
(* needs to be done often (for each identifier lookup), we implement    *)
(* some caching, repeating the test only when the environment changes.  *)
(*   We check for protect_term because it is the first constant loaded; *)
(* ssr_have would ultimately be a better choice.                        *)
let ssr_loaded = Summary.ref ~name:"SSR:loaded" false
let is_ssr_loaded () =
  !ssr_loaded ||
  (if Lexer.is_keyword "SsrSyntax_is_Imported" then ssr_loaded:=true;
   !ssr_loaded)

(* 0 cost pp function. Active only if env variable SSRDEBUG is set *)
(* or if SsrDebug is Set                                                  *)
let pp_ref = ref (fun _ -> ())
let ssr_pp s = pperrnl (str"SSR: "++Lazy.force s)
let _ = try ignore(Sys.getenv "SSRDEBUG"); pp_ref := ssr_pp with Not_found -> ()
let _ =
  Goptions.declare_bool_option
    { Goptions.optsync  = false;
      Goptions.optname  = "ssreflect debugging";
      Goptions.optkey   = ["SsrDebug"];
      Goptions.optdepr  = false;
      Goptions.optread  = (fun _ -> !pp_ref == ssr_pp);
      Goptions.optwrite = (fun b -> 
        Ssrmatching.debug b;
        if b then pp_ref := ssr_pp else pp_ref := fun _ -> ()) }
let pp s = !pp_ref s

(** Utils {{{ *****************************************************************)
let env_size env = List.length (Environ.named_context env)
let safeDestApp c =
  match kind_of_term c with App (f, a) -> f, a | _ -> c, [| |]
let get_index = function ArgArg i -> i | _ ->
  anomaly "Uninterpreted index"
(* Toplevel constr must be globalized twice ! *)

let skip_numchars s =
  let rec loop i = match s.[i] with '0'..'9' -> loop (i + 1) | _ -> i in loop
(* More sensible names for constr printers *)
let prl_constr = pr_lconstr
let pr_constr = pr_constr
let prl_glob_constr c = pr_lglob_constr_env (Global.env ()) c
let prl_constr_expr = pr_lconstr_expr
let prl_glob_constr_and_expr = function
  | _, Some c -> prl_constr_expr c
  | c, None -> prl_glob_constr c

(** Constructors for cast type *)
let dC t = CastConv t

(** Constructors for constr_expr *)
let mkCProp loc = CSort (loc, GProp)
let mkCType loc = CSort (loc, GType [])
let mkCVar loc id = CRef (Ident (loc, id),None)
let isCVar = function CRef (Ident _,_) -> true | _ -> false
let destCVar = function CRef (Ident (_, id),_) -> id | _ ->
  anomaly "not a CRef"
let rec mkCHoles loc n =
  if n <= 0 then [] else CHole (loc, None, IntroAnonymous, None) :: mkCHoles loc (n - 1)
let mkCHole loc = CHole (loc, None, IntroAnonymous, None)
let rec isCHoles = function CHole _ :: cl -> isCHoles cl | cl -> cl = []
let mkCExplVar loc id n =
   CAppExpl (loc, (None, Ident (loc, id), None), mkCHoles loc n)
let mkCLambda loc name ty t = 
   CLambdaN (loc, [[loc, name], Default Explicit, ty], t)
let mkCLetIn loc name bo t = 
   CLetIn (loc, (loc, name), bo, t)
let mkCArrow loc ty t =
   CProdN (loc, [[dummy_loc,Anonymous], Default Explicit, ty], t)
let mkCCast loc t ty = CCast (loc,t, dC ty)
(** Constructors for rawconstr *)
let rec mkRHoles n = if n > 0 then mkRHole :: mkRHoles (n - 1) else []
let rec isRHoles = function GHole _ :: cl -> isRHoles cl | cl -> cl = []
let mkRApp f args = if args = [] then f else GApp (dummy_loc, f, args)
let mkRVar id = GRef (dummy_loc, VarRef id,None)
let mkRltacVar id = GVar (dummy_loc, id)
let mkRCast rc rt =  GCast (dummy_loc, rc, dC rt)
let mkRType =  GSort (dummy_loc, GType [])
let mkRProp =  GSort (dummy_loc, GProp)
let mkRArrow rt1 rt2 = GProd (dummy_loc, Anonymous, Explicit, rt1, rt2)
let mkRConstruct c = GRef (dummy_loc, ConstructRef c,None)
let mkRInd mind = GRef (dummy_loc, IndRef mind,None)
let mkRLambda n s t = GLambda (dummy_loc, n, Explicit, s, t)

(** Constructors for constr *)
let pf_e_type_of gl t =
  let sigma, env, it = project gl, pf_env gl, sig_it gl in
  let sigma, ty = Typing.type_of env sigma t in
  re_sig it sigma, ty

let mkAppRed f c = match kind_of_term f with
| Lambda (_, _, b) -> subst1 c b
| _ -> mkApp (f, [|c|])

let mkProt t c gl =
  let prot, gl = pf_mkSsrConst "protect_term" gl in
  mkApp (prot, [|t; c|]), gl

let mkRefl t c gl =
  let refl, gl = pf_fresh_global (build_coq_eq_data()).refl gl in
  mkApp (refl, [|t; c|]), gl


(* Application to a sequence of n rels (for building eta-expansions). *)
(* The rel indices decrease down to imin (inclusive), unless n < 0,   *)
(* in which case they're incresing (from imin).                       *)
let mkEtaApp c n imin =
  if n = 0 then c else
  let nargs, mkarg =
    if n < 0 then -n, (fun i -> mkRel (imin + i)) else
    let imax = imin + n - 1 in n, (fun i -> mkRel (imax - i)) in
  mkApp (c, Array.init nargs mkarg)
(* Same, but optimizing head beta redexes *)
let rec whdEtaApp c n =
  if n = 0 then c else match kind_of_term c with
  | Lambda (_, _, c') -> whdEtaApp c' (n - 1)
  | _ -> mkEtaApp (lift n c) n 1
let mkType () = Universes.new_Type (Lib.cwd ())

(* ssrterm conbinators *)
let combineCG t1 t2 f g = match t1, t2 with
 | (x, (t1, None)), (_, (t2, None)) -> x, (g t1 t2, None)
 | (x, (_, Some t1)), (_, (_, Some t2)) -> x, (mkRHole, Some (f t1 t2))
 | _, (_, (_, None)) -> anomaly "have: mixed C-G constr"
 | _ -> anomaly "have: mixed G-C constr"
let loc_ofCG = function
 | (_, (s, None)) -> Glob_ops.loc_of_glob_constr s
 | (_, (_, Some s)) -> Constrexpr_ops.constr_loc s

let pf_type_of gl t = let sigma, ty = pf_type_of gl t in re_sig (sig_it gl)  sigma, ty

let map_fold_constr g f ctx acc cstr =
  let array_f ctx acc x = let x, acc = f ctx acc x in acc, x in
  match kind_of_term cstr with
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _ | Construct _) ->
      cstr, acc
  | Proj (x,c) ->
      let c', acc = f ctx acc c in
      (if c == c' then cstr else mkProj (x,c')), acc
  | Cast (c,k, t) ->
      let c', acc = f ctx acc c in
      let t', acc = f ctx acc t in
      (if c==c' && t==t' then cstr else mkCast (c', k, t')), acc
  | Prod (na,t,c) ->
      let t', acc = f ctx acc t in
      let c', acc = f (g (na,None,t) ctx) acc c in
      (if t==t' && c==c' then cstr else mkProd (na, t', c')), acc
  | Lambda (na,t,c) ->
      let t', acc = f ctx acc t in
      let c', acc = f (g (na,None,t) ctx) acc c in
      (if t==t' && c==c' then cstr else  mkLambda (na, t', c')), acc
  | LetIn (na,b,t,c) ->
      let b', acc = f ctx acc b in
      let t', acc = f ctx acc t in
      let c', acc = f (g (na,Some b,t) ctx) acc c in
      (if b==b' && t==t' && c==c' then cstr else mkLetIn (na, b', t', c')), acc
  | App (c,al) ->
      let c', acc = f ctx acc c in
      let acc, al' = CArray.smartfoldmap (array_f ctx) acc al in
      (if c==c' && Array.for_all2 (==) al al' then cstr else mkApp (c', al')),
      acc
  | Evar (e,al) ->
      let acc, al' = CArray.smartfoldmap (array_f ctx) acc al in
      (if Array.for_all2 (==) al al' then cstr else mkEvar (e, al')), acc
  | Case (ci,p,c,bl) ->
      let p', acc = f ctx acc p in
      let c', acc = f ctx acc c in
      let acc, bl' = CArray.smartfoldmap (array_f ctx) acc bl in
      (if p==p' && c==c' && Array.for_all2 (==) bl bl' then cstr else
        mkCase (ci, p', c', bl')),
      acc
  | Fix (ln,(lna,tl,bl)) ->
      let acc, tl' = CArray.smartfoldmap (array_f ctx) acc tl in
      let ctx' = Array.fold_left2 (fun l na t -> g (na,None,t) l) ctx lna tl in
      let acc, bl' = CArray.smartfoldmap (array_f ctx') acc bl in
      (if Array.for_all2 (==) tl tl' && Array.for_all2 (==) bl bl'
      then cstr
      else mkFix (ln,(lna,tl',bl'))), acc
  | CoFix(ln,(lna,tl,bl)) ->
      let acc, tl' = CArray.smartfoldmap (array_f ctx) acc tl in
      let ctx' = Array.fold_left2 (fun l na t -> g (na,None,t) l) ctx lna tl in
      let acc,bl' = CArray.smartfoldmap (array_f ctx') acc bl in
      (if Array.for_all2 (==) tl tl' && Array.for_all2 (==) bl bl'
      then cstr
      else mkCoFix (ln,(lna,tl',bl'))), acc

let pf_merge_uc_of sigma gl =
  let ucst = Evd.evar_universe_context sigma in
  pf_merge_uc ucst gl

(* }}} *)

(** Profiling {{{ *************************************************************)
type profiler = { 
  profile : 'a 'b. ('a -> 'b) -> 'a -> 'b;
  reset : unit -> unit;
  print : unit -> unit }
let profile_now = ref false
let something_profiled = ref false
let profilers = ref []
let add_profiler f = profilers := f :: !profilers;;
let _ =
  Goptions.declare_bool_option
    { Goptions.optsync  = false;
      Goptions.optname  = "ssreflect profiling";
      Goptions.optkey   = ["SsrProfiling"];
      Goptions.optread  = (fun _ -> !profile_now);
      Goptions.optdepr  = false;
      Goptions.optwrite = (fun b -> 
        Ssrmatching.profile b;
        profile_now := b;
        if b then List.iter (fun f -> f.reset ()) !profilers;
        if not b then List.iter (fun f -> f.print ()) !profilers) }
let () =
  let prof_total = 
    let init = ref 0.0 in { 
    profile = (fun f x -> assert false);
    reset = (fun () -> init := Unix.gettimeofday ());
    print = (fun () -> if !something_profiled then
        prerr_endline 
           (Printf.sprintf "!! %-39s %10d %9.4f %9.4f %9.4f"
           "total" 0 (Unix.gettimeofday() -. !init) 0.0 0.0)) } in
  let prof_legenda = {
    profile = (fun f x -> assert false);
    reset = (fun () -> ());
    print = (fun () -> if !something_profiled then begin
        prerr_endline 
           (Printf.sprintf "!! %39s ---------- --------- --------- ---------" 
           (String.make 39 '-'));
        prerr_endline 
           (Printf.sprintf "!! %-39s %10s %9s %9s %9s" 
           "function" "#calls" "total" "max" "average") end) } in
  add_profiler prof_legenda;
  add_profiler prof_total
;;

let mk_profiler s =
  let total, calls, max = ref 0.0, ref 0, ref 0.0 in
  let reset () = total := 0.0; calls := 0; max := 0.0 in
  let profile f x =
    if not !profile_now then f x else
    let before = Unix.gettimeofday () in
    try
      incr calls;
      let res = f x in
      let after = Unix.gettimeofday () in
      let delta = after -. before in
      total := !total +. delta;
      if delta > !max then max := delta;
      res
    with exc ->
      let after = Unix.gettimeofday () in
      let delta = after -. before in
      total := !total +. delta;
      if delta > !max then max := delta;
      raise exc in
  let print () =
     if !calls <> 0 then begin
       something_profiled := true;
       prerr_endline
         (Printf.sprintf "!! %-39s %10d %9.4f %9.4f %9.4f" 
         s !calls !total !max (!total /. (float_of_int !calls))) end in
  let prof = { profile = profile; reset = reset; print = print } in
  add_profiler prof;
  prof
;;
(* }}} *)

let inVersion = Libobject.declare_object {
  (Libobject.default_object "SSRASTVERSION") with
  Libobject.load_function = (fun _ (_,v) -> 
    if v <> ssrAstVersion then Errors.error "Please recompile your .vo files");
  Libobject.classify_function = (fun v -> Libobject.Keep v);
}

let _ =
  Goptions.declare_bool_option
    { Goptions.optsync  = false;
      Goptions.optname  = "ssreflect version";
      Goptions.optkey   = ["SsrAstVersion"];
      Goptions.optread  = (fun _ -> true);
      Goptions.optdepr  = false;
      Goptions.optwrite = (fun _ -> 
        Lib.add_anonymous_leaf (inVersion ssrAstVersion)) }

let tactic_expr = Tactic.tactic_expr
let gallina_ext = Vernac_.gallina_ext 
let sprintf = Printf.sprintf
let tactic_mode = G_vernac.tactic_mode

(** 1. Utilities *)


let ssroldreworder = Summary.ref ~name:"SSR:oldreworder" true
let _ =
  Goptions.declare_bool_option
    { Goptions.optsync  = false;
      Goptions.optname  = "ssreflect 1.3 compatibility flag";
      Goptions.optkey   = ["SsrOldRewriteGoalsOrder"];
      Goptions.optread  = (fun _ -> !ssroldreworder);
      Goptions.optdepr  = false;
      Goptions.optwrite = (fun b -> ssroldreworder := b) }

let ssrhaveNOtcresolution = ref false

let inHaveTCResolution = Libobject.declare_object {
  (Libobject.default_object "SSRHAVETCRESOLUTION") with
  Libobject.cache_function = (fun (_,v) -> ssrhaveNOtcresolution := v);
  Libobject.load_function = (fun _ (_,v) -> ssrhaveNOtcresolution := v);
  Libobject.classify_function = (fun v -> Libobject.Keep v);
}

let _ =
  Goptions.declare_bool_option
    { Goptions.optsync  = false;
      Goptions.optname  = "have type classes";
      Goptions.optkey   = ["SsrHave";"NoTCResolution"];
      Goptions.optread  = (fun _ -> !ssrhaveNOtcresolution);
      Goptions.optdepr  = false;
      Goptions.optwrite = (fun b ->
        Lib.add_anonymous_leaf (inHaveTCResolution b)) }


(** Primitive parsing to avoid syntax conflicts with basic tactics. *)

let accept_before_syms syms strm =
  match Compat.get_tok (stream_nth 1 strm) with
  | Tok.KEYWORD sym when List.mem sym syms -> ()
  | _ -> raise Stream.Failure

let accept_before_syms_or_any_id syms strm =
  match Compat.get_tok (stream_nth 1 strm) with
  | Tok.KEYWORD sym when List.mem sym syms -> ()
  | Tok.IDENT _ -> ()
  | _ -> raise Stream.Failure

let accept_before_syms_or_ids syms ids strm =
  match Compat.get_tok (stream_nth 1 strm) with
  | Tok.KEYWORD sym when List.mem sym syms -> ()
  | Tok.IDENT id when List.mem id ids -> ()
  | _ -> raise Stream.Failure

(** Pretty-printing utilities *)

let tacltop = (5,Ppextend.E)

(** Tactic-level diagnosis *)

let pf_pr_constr gl = pr_constr_env (pf_env gl)

let pf_pr_glob_constr gl = pr_glob_constr_env (pf_env gl)

(* debug *)

let pf_msg gl =
   let ppgl = pr_lconstr_env (pf_env gl) (project gl) (pf_concl gl) in
   msgnl (str "goal is " ++ ppgl)

let msgtac gl = pf_msg gl; tclIDTAC gl

(** Tactic utilities *)

let last_goal gls = let sigma, gll = Refiner.unpackage gls in
   Refiner.repackage sigma (List.nth gll (List.length gll - 1))

let pf_type_id gl t = id_of_string (hdchar (pf_env gl) t)

let is_pf_var c = isVar c && not_section_id (destVar c)

let pf_ids_of_proof_hyps gl =
  let add_hyp (id, _, _) ids = if not_section_id id then id :: ids else ids in
  Context.fold_named_context add_hyp (pf_hyps gl) ~init:[]

let pf_nf_evar gl e = Reductionops.nf_evar (project gl) e

let pf_partial_solution gl t evl =
  let sigma, g = project gl, sig_it gl in
  let sigma = Goal.V82.partial_solution sigma g t in
  re_sig (List.map (fun x -> (fst (destEvar x))) evl) sigma

let pf_new_evar gl ty =
  let sigma, env, it = project gl, pf_env gl, sig_it gl in
  let sigma = Sigma.Unsafe.of_evar_map sigma in
  let Sigma (extra, sigma, _) = Evarutil.new_evar env sigma ty in
  let sigma = Sigma.to_evar_map sigma in
  re_sig it sigma, extra

(* Basic tactics *)

let convert_concl_no_check t = convert_concl_no_check t DEFAULTcast
let convert_concl t = convert_concl t DEFAULTcast
let reduct_in_concl t = reduct_in_concl (t, DEFAULTcast)
let havetac id c = Proofview.V82.of_tactic (pose_proof (Name id) c)
let settac id c = letin_tac None (Name id) c None
let posetac id cl = Proofview.V82.of_tactic (settac id cl nowhere)
let basecuttac name c gl =
  let hd, gl = pf_mkSsrConst name gl in
  let t = mkApp (hd, [|c|]) in
  let gl, _ = pf_e_type_of gl t in
  Proofview.V82.of_tactic (apply t) gl

(* Let's play with the new proof engine API *)
module PG = Proofview.Goal
module TN = Tacticals.New
let old_tac = Proofview.V82.tactic
let new_tac = Proofview.V82.of_tactic


(** Name generation {{{ *******************************************************)

(* Since Coq now does repeated internal checks of its external lexical *)
(* rules, we now need to carve ssreflect reserved identifiers out of   *)
(* out of the user namespace. We use identifiers of the form _id_ for  *)
(* this purpose, e.g., we "anonymize" an identifier id as _id_, adding *)
(* an extra leading _ if this might clash with an internal identifier. *)
(*    We check for ssreflect identifiers in the ident grammar rule;    *)
(* when the ssreflect Module is present this is normally an error,     *)
(* but we provide a compatibility flag to reduce this to a warning.    *)

let ssr_reserved_ids = Summary.ref ~name:"SSR:idents" true

let _ =
  Goptions.declare_bool_option
    { Goptions.optsync  = true;
      Goptions.optname  = "ssreflect identifiers";
      Goptions.optkey   = ["SsrIdents"];
      Goptions.optdepr  = false;
      Goptions.optread  = (fun _ -> !ssr_reserved_ids);
      Goptions.optwrite = (fun b -> ssr_reserved_ids := b)
    }

let is_ssr_reserved s =
  let n = String.length s in n > 2 && s.[0] = '_' && s.[n - 1] = '_'

let internal_names = ref []
let add_internal_name pt = internal_names := pt :: !internal_names
let is_internal_name s = List.exists (fun p -> p s) !internal_names

let ssr_id_of_string loc s =
  if is_ssr_reserved s && is_ssr_loaded () then begin
    if !ssr_reserved_ids then
      loc_error loc ("The identifier " ^ s ^ " is reserved.")
    else if is_internal_name s then
      msg_warning (str ("Conflict between " ^ s ^ " and ssreflect internal names."))
    else msg_warning (str (
     "The name " ^ s ^ " fits the _xxx_ format used for anonymous variables.\n"
  ^ "Scripts with explicit references to anonymous variables are fragile."))
    end; id_of_string s

let ssr_null_entry = Gram.Entry.of_parser "ssr_null" (fun _ -> ())

let (!@) = Compat.to_coqloc

GEXTEND Gram 
  GLOBAL: Prim.ident;
  Prim.ident: [[ s = IDENT; ssr_null_entry -> ssr_id_of_string !@loc s ]];
END

let mk_internal_id s =
  let s' = sprintf "_%s_" s in
  for i = 1 to String.length s do if s'.[i] = ' ' then s'.[i] <- '_' done;
  add_internal_name ((=) s'); id_of_string s'

let same_prefix s t n =
  let rec loop i = i = n || s.[i] = t.[i] && loop (i + 1) in loop 0

let skip_digits s =
  let n = String.length s in 
  let rec loop i = if i < n && is_digit s.[i] then loop (i + 1) else i in loop

let mk_tagged_id t i = id_of_string (sprintf "%s%d_" t i)
let is_tagged t s =
  let n = String.length s - 1 and m = String.length t in
  m < n && s.[n] = '_' && same_prefix s t m && skip_digits s m = n

let perm_tag = "_perm_Hyp_"
let _ = add_internal_name (is_tagged perm_tag)
let mk_perm_id =
  let salt = ref 1 in 
  fun () -> salt := !salt mod 10000 + 1; mk_tagged_id perm_tag !salt

let evar_tag = "_evar_"
let _ = add_internal_name (is_tagged evar_tag)
let mk_evar_name n = Name (mk_tagged_id evar_tag n)
let nb_evar_deps = function
  | Name id ->
    let s = string_of_id id in
    if not (is_tagged evar_tag s) then 0 else
    let m = String.length evar_tag in
    (try int_of_string (String.sub s m (String.length s - 1 - m)) with _ -> 0)
  | _ -> 0

let discharged_tag = "_discharged_"
let mk_discharged_id id =
  id_of_string (sprintf "%s%s_" discharged_tag (string_of_id id))
let has_discharged_tag s =
  let m = String.length discharged_tag and n = String.length s - 1 in
  m < n && s.[n] = '_' && same_prefix s discharged_tag m
let _ = add_internal_name has_discharged_tag
let is_discharged_id id = has_discharged_tag (string_of_id id)

let wildcard_tag = "_the_"
let wildcard_post = "_wildcard_"
let mk_wildcard_id i =
  id_of_string (sprintf "%s%s%s" wildcard_tag (String.ordinal i) wildcard_post)
let has_wildcard_tag s = 
  let n = String.length s in let m = String.length wildcard_tag in
  let m' = String.length wildcard_post in
  n < m + m' + 2 && same_prefix s wildcard_tag m &&
  String.sub s (n - m') m' = wildcard_post &&
  skip_digits s m = n - m' - 2
let _ = add_internal_name has_wildcard_tag

let tmp_tag = "_the_"
let tmp_post = "_tmp_"
let mk_tmp_id i =
  id_of_string (sprintf "%s%s%s" tmp_tag (String.ordinal i) tmp_post)

let max_suffix m (t, j0 as tj0) id  =
  let s = string_of_id id in let n = String.length s - 1 in
  let dn = String.length t - 1 - n in let i0 = j0 - dn in
  if not (i0 >= m && s.[n] = '_' && same_prefix s t m) then tj0 else
  let rec loop i =
    if i < i0 && s.[i] = '0' then loop (i + 1) else
    if (if i < i0 then skip_digits s i = n else le_s_t i) then s, i else tj0
  and le_s_t i =
    let ds = s.[i] and dt = t.[i + dn] in
    if ds = dt then i = n || le_s_t (i + 1) else
    dt < ds && skip_digits s i = n in
  loop m

let mk_anon_id t gl =
  let m, si0, id0 =
    let s = ref (sprintf  "_%s_" t) in
    if is_internal_name !s then s := "_" ^ !s;
    let n = String.length !s - 1 in
    let rec loop i j =
      let d = !s.[i] in if not (is_digit d) then i + 1, j else
      loop (i - 1) (if d = '0' then j else i) in
    let m, j = loop (n - 1) n in m, (!s, j), id_of_string !s in
  let gl_ids = pf_ids_of_hyps gl in
  if not (List.mem id0 gl_ids) then id0 else
  let s, i = List.fold_left (max_suffix m) si0 gl_ids in
  let n = String.length s - 1 in
  let rec loop i =
    if s.[i] = '9' then (s.[i] <- '0'; loop (i - 1)) else
    if i < m then (s.[n] <- '0'; s.[m] <- '1'; s ^ "_") else
    (s.[i] <- Char.chr (Char.code s.[i] + 1); s) in
  id_of_string (loop (n - 1))
  
(* }}} *)

(* Temporary names, + intro pattern *)
let new_tmp_id ctx =
  let id = mk_tmp_id (1 + List.length ctx.tmp_ids) in
  let orig = ref Anonymous in
  (id, orig), { ctx with tmp_ids = (id, orig) :: ctx.tmp_ids }
;;

let gentac_ref = ref (fun _ _ _ -> assert false)

let rename_hd_prod orig_name_ref gl =
  match kind_of_term (pf_concl gl) with
  | Prod(_,src,tgt) ->
      new_tac (convert_concl_no_check (mkProd (!orig_name_ref,src,tgt))) gl
  | _ -> Errors.anomaly (str "gentac creates no product")

let gen_tmp_ids
  ?(ist=Geninterp.({ lfun = Id.Map.empty; extra = TacStore.empty })) gl
=
  let gl, ctx = pull_ctx gl in
  push_ctxs ctx
    (tclTHENLIST
      (List.map (fun (id,orig_ref) ->
        tclTHEN 
        (!gentac_ref ist ((None,Some(false,[])),cpattern_of_id id))
        (rename_hd_prod orig_ref))
      ctx.tmp_ids) gl)
;;

(* wildcard names *)
let new_wild_id ctx =
  let i = 1 + List.length ctx.wild_ids in
  let id = mk_wildcard_id i in
  id, { ctx with wild_ids = id :: ctx.wild_ids }

let clear_wilds wilds gl =
  clear (List.filter (fun id -> List.mem id wilds) (pf_ids_of_hyps gl)) gl

let clear_with_wilds wilds clr0 gl =
  let extend_clr clr (id, _, _ as nd) =
    if List.mem id clr || not (List.mem id wilds) then clr else
    let vars = global_vars_set_of_decl (pf_env gl) nd in
    let occurs id' = Idset.mem id' vars in
    if List.exists occurs clr then id :: clr else clr in
  clear (Context.fold_named_context_reverse extend_clr ~init:clr0 (pf_hyps gl)) gl

let clear_wilds_and_tmp_and_delayed_ids gl =
  let _, ctx = pull_ctx gl in
  tac_ctx
   (tclTHEN
    (clear_with_wilds ctx.wild_ids ctx.delayed_clears)
    (clear_wilds (List.map fst ctx.tmp_ids @ ctx.wild_ids))) gl

(* we reduce head beta redexes *)
let betared env = 
  Closure.create_clos_infos 
   (Closure.RedFlags.mkflags [Closure.RedFlags.fBETA])
    env
;;
let rec fst_prod red tac = PG.(enter { enter = fun gl ->
  let sigma = Sigma.to_evar_map (sigma gl) in
  let concl = Evarutil.nf_evar sigma (concl (assume gl)) in
  match kind_of_term concl with
  | Prod (id,_,tgt) | LetIn(id,_,_,tgt) -> tac id
  | _ -> if red then TN.tclZEROMSG (str"No product even after head-reduction.")
         else TN.tclTHEN (old_tac hnf_in_concl) (fst_prod true tac)
})
;;
let introid ?(orig=ref Anonymous) name = tclTHEN (fun gl ->
   let g, env = pf_concl gl, pf_env gl in
   match kind_of_term g with
   | App (hd, _) when isLambda hd -> 
     let g = Closure.whd_val (betared env) (Closure.inject g) in
     Proofview.V82.of_tactic (convert_concl_no_check g) gl
   | _ -> tclIDTAC gl)
  (Proofview.V82.of_tactic
    (fst_prod false (fun id -> orig := id; intro_mustbe_force name)))
;;

(* We must not anonymize context names discharged by the "in" tactical. *)

let ssr_anon_hyp = "Hyp"

let anontac (x, _, _) gl =
  let id =  match x with
  | Name id ->
    if is_discharged_id id then id else mk_anon_id (string_of_id id) gl
  | _ -> mk_anon_id ssr_anon_hyp gl in
  introid id gl

let rec constr_name c = match kind_of_term c with
  | Var id -> Name id
  | Cast (c', _, _) -> constr_name c'
  | Const (cn,_) -> Name (id_of_label (con_label cn))
  | App (c', _) -> constr_name c'
  | _ -> Anonymous


(** Open term to lambda-term coercion  {{{ ************************************)

(* This operation takes a goal gl and an open term (sigma, t), and   *)
(* returns a term t' where all the new evars in sigma are abstracted *)
(* with the mkAbs argument, i.e., for mkAbs = mkLambda then there is *)
(* some duplicate-free array args of evars of sigma such that the    *)
(* term mkApp (t', args) is convertible to t.                        *)
(* This makes a useful shorthand for local definitions in proofs,    *)
(* i.e., pose succ := _ + 1 means pose succ := fun n : nat => n + 1, *)
(* and, in context of the the 4CT library, pose mid := maps id means *)
(*    pose mid := fun d : detaSet => @maps d d (@id (datum d))       *)
(* Note that this facility does not extend to set, which tries       *)
(* instead to fill holes by matching a goal subterm.                 *)
(* The argument to "have" et al. uses product abstraction, e.g.      *)
(*    have Hmid: forall s, (maps id s) = s.                          *)
(* stands for                                                        *)
(*    have Hmid: forall (d : dataSet) (s : seq d), (maps id s) = s.  *)
(* We also use this feature for rewrite rules, so that, e.g.,        *)
(*   rewrite: (plus_assoc _ 3).                                      *)
(* will execute as                                                   *)
(*   rewrite (fun n => plus_assoc n 3)                               *)
(* i.e., it will rewrite some subterm .. + (3 + ..) to .. + 3 + ...  *)
(* The convention is also used for the argument of the congr tactic, *)
(* e.g., congr (x + _ * 1).                                          *)

(* Replace new evars with lambda variables, retaining local dependencies *)
(* but stripping global ones. We use the variable names to encode the    *)
(* the number of dependencies, so that the transformation is reversible. *)

let pf_abs_evars gl (sigma, c0) =
  let sigma0, ucst = project gl, Evd.evar_universe_context sigma in
  let nenv = env_size (pf_env gl) in
  let abs_evar n k =
    let evi = Evd.find sigma k in
    let dc = List.firstn n (evar_filtered_context evi) in
    let abs_dc c = function
    | x, Some b, t -> mkNamedLetIn x b t (mkArrow t c)
    | x, None, t -> mkNamedProd x t c in
    let t = Context.fold_named_context_reverse abs_dc ~init:evi.evar_concl dc in
    Evarutil.nf_evar sigma t in
  let rec put evlist c = match kind_of_term c with
  | Evar (k, a) ->  
    if List.mem_assoc k evlist || Evd.mem sigma0 k then evlist else
    let n = max 0 (Array.length a - nenv) in
    let t = abs_evar n k in (k, (n, t)) :: put evlist t
  | _ -> fold_constr put evlist c in
  let evlist = put [] c0 in
  if evlist = [] then 0, c0,[], ucst else
  let rec lookup k i = function
    | [] -> 0, 0
    | (k', (n, _)) :: evl -> if k = k' then i, n else lookup k (i + 1) evl in
  let rec get i c = match kind_of_term c with
  | Evar (ev, a) ->
    let j, n = lookup ev i evlist in
    if j = 0 then map_constr (get i) c else if n = 0 then mkRel j else
    mkApp (mkRel j, Array.init n (fun k -> get i a.(n - 1 - k)))
  | _ -> map_constr_with_binders ((+) 1) get i c in
  let rec loop c i = function
  | (_, (n, t)) :: evl ->
    loop (mkLambda (mk_evar_name n, get (i - 1) t, c)) (i - 1) evl
  | [] -> c in
  List.length evlist, loop (get 1 c0) 1 evlist, List.map fst evlist, ucst



(* As before but if (?i : T(?j)) and (?j : P : Prop), then the lambda for i
 * looks like (fun evar_i : (forall pi : P. T(pi))) thanks to "loopP" and all 
 * occurrences of evar_i are replaced by (evar_i evar_j) thanks to "app".
 *
 * If P can be solved by ssrautoprop (that defaults to trivial), then
 * the corresponding lambda looks like (fun evar_i : T(c)) where c is 
 * the solution found by ssrautoprop.
 *)
let ssrautoprop_tac = ref (fun gl -> assert false)

(* Thanks to Arnaud Spiwack for this snippet *)
let call_on_evar tac e s =
  let { it = gs ; sigma = s } =
    tac { it = e ; sigma = s; } in
  gs, s

let pf_abs_evars_pirrel gl (sigma, c0) =
  pp(lazy(str"==PF_ABS_EVARS_PIRREL=="));
  pp(lazy(str"c0= " ++ pr_constr c0));
  let sigma0 = project gl in
  let c0 = Evarutil.nf_evar sigma0 (Evarutil.nf_evar sigma c0) in
  let nenv = env_size (pf_env gl) in
  let abs_evar n k =
    let evi = Evd.find sigma k in
    let dc = List.firstn n (evar_filtered_context evi) in
    let abs_dc c = function
    | x, Some b, t -> mkNamedLetIn x b t (mkArrow t c)
    | x, None, t -> mkNamedProd x t c in
    let t = Context.fold_named_context_reverse abs_dc ~init:evi.evar_concl dc in
    Evarutil.nf_evar sigma0 (Evarutil.nf_evar sigma t) in
  let rec put evlist c = match kind_of_term c with
  | Evar (k, a) ->  
    if List.mem_assoc k evlist || Evd.mem sigma0 k then evlist else
    let n = max 0 (Array.length a - nenv) in
    let k_ty = 
      Retyping.get_sort_family_of 
        (pf_env gl) sigma (Evd.evar_concl (Evd.find sigma k)) in
    let is_prop = k_ty = InProp in
    let t = abs_evar n k in (k, (n, t, is_prop)) :: put evlist t
  | _ -> fold_constr put evlist c in
  let evlist = put [] c0 in
  if evlist = [] then 0, c0 else
  let pr_constr t = pr_constr (Reductionops.nf_beta (project gl) t) in
  pp(lazy(str"evlist=" ++ pr_list (fun () -> str";")
    (fun (k,_) -> str(Evd.string_of_existential k)) evlist));
  let evplist = 
    let depev = List.fold_left (fun evs (_,(_,t,_)) -> 
        Intset.union evs (Evarutil.undefined_evars_of_term sigma t)) Intset.empty evlist in
    List.filter (fun (i,(_,_,b)) -> b && Intset.mem i depev) evlist in
  let evlist, evplist, sigma = 
    if evplist = [] then evlist, [], sigma else
    List.fold_left (fun (ev, evp, sigma) (i, (_,t,_) as p) ->
      try 
        let ng, sigma = call_on_evar !ssrautoprop_tac i sigma in
        if (ng <> []) then errorstrm (str "Should we tell the user?");
        List.filter (fun (j,_) -> j <> i) ev, evp, sigma
      with _ -> ev, p::evp, sigma) (evlist, [], sigma) (List.rev evplist) in
  let c0 = Evarutil.nf_evar sigma c0 in
  let evlist = 
    List.map (fun (x,(y,t,z)) -> x,(y,Evarutil.nf_evar sigma t,z)) evlist in
  let evplist = 
    List.map (fun (x,(y,t,z)) -> x,(y,Evarutil.nf_evar sigma t,z)) evplist in
  pp(lazy(str"c0= " ++ pr_constr c0));
  let rec lookup k i = function
    | [] -> 0, 0
    | (k', (n,_,_)) :: evl -> if k = k' then i,n else lookup k (i + 1) evl in
  let rec get evlist i c = match kind_of_term c with
  | Evar (ev, a) ->
    let j, n = lookup ev i evlist in
    if j = 0 then map_constr (get evlist i) c else if n = 0 then mkRel j else
    mkApp (mkRel j, Array.init n (fun k -> get evlist i a.(n - 1 - k)))
  | _ -> map_constr_with_binders ((+) 1) (get evlist) i c in
  let rec app extra_args i c = match decompose_app c with
  | hd, args when isRel hd && destRel hd = i ->
      let j = destRel hd in
      mkApp (mkRel j, Array.of_list (List.map (lift (i-1)) extra_args @ args))
  | _ -> map_constr_with_binders ((+) 1) (app extra_args) i c in
  let rec loopP evlist c i = function
  | (_, (n, t, _)) :: evl ->
    let t = get evlist (i - 1) t in
    let n = Name (id_of_string (ssr_anon_hyp ^ string_of_int n)) in 
    loopP evlist (mkProd (n, t, c)) (i - 1) evl
  | [] -> c in
  let rec loop c i = function
  | (_, (n, t, _)) :: evl ->
    let evs = Evarutil.undefined_evars_of_term sigma t in
    let t_evplist = List.filter (fun (k,_) -> Intset.mem k evs) evplist in
    let t = loopP t_evplist (get t_evplist 1 t) 1 t_evplist in
    let t = get evlist (i - 1) t in
    let extra_args = 
      List.map (fun (k,_) -> mkRel (fst (lookup k i evlist))) 
        (List.rev t_evplist) in
    let c = if extra_args = [] then c else app extra_args 1 c in
    loop (mkLambda (mk_evar_name n, t, c)) (i - 1) evl
  | [] -> c in
  let res = loop (get evlist 1 c0) 1 evlist in
  pp(lazy(str"res= " ++ pr_constr res));
  List.length evlist, res

(* Strip all non-essential dependencies from an abstracted term, generating *)
(* standard names for the abstracted holes.                                 *)

let pf_abs_cterm gl n c0 =
  if n <= 0 then c0 else
  let noargs = [|0|] in
  let eva = Array.make n noargs in
  let rec strip i c = match kind_of_term c with
  | App (f, a) when isRel f ->
    let j = i - destRel f in
    if j >= n || eva.(j) = noargs then mkApp (f, Array.map (strip i) a) else
    let dp = eva.(j) in
    let nd = Array.length dp - 1 in
    let mkarg k = strip i a.(if k < nd then dp.(k + 1) - j else k + dp.(0)) in
    mkApp (f, Array.init (Array.length a - dp.(0)) mkarg)
  | _ -> map_constr_with_binders ((+) 1) strip i c in
  let rec strip_ndeps j i c = match kind_of_term c with
  | Prod (x, t, c1) when i < j ->
    let dl, c2 = strip_ndeps j (i + 1) c1 in
    if noccurn 1 c2 then dl, lift (-1) c2 else
    i :: dl, mkProd (x, strip i t, c2)
  | LetIn (x, b, t, c1) when i < j ->
    let _, _, c1' = destProd c1 in
    let dl, c2 = strip_ndeps j (i + 1) c1' in
    if noccurn 1 c2 then dl, lift (-1) c2 else
    i :: dl, mkLetIn (x, strip i b, strip i t, c2)
  | _ -> [], strip i c in
  let rec strip_evars i c = match kind_of_term c with
    | Lambda (x, t1, c1) when i < n ->
      let na = nb_evar_deps x in
      let dl, t2 = strip_ndeps (i + na) i t1 in
      let na' = List.length dl in
      eva.(i) <- Array.of_list (na - na' :: dl);
      let x' =
        if na' = 0 then Name (pf_type_id gl t2) else mk_evar_name na' in
      mkLambda (x', t2, strip_evars (i + 1) c1)
(*      if noccurn 1 c2 then lift (-1) c2 else
      mkLambda (Name (pf_type_id gl t2), t2, c2) *)
    | _ -> strip i c in
  strip_evars 0 c0

(* Undo the evar abstractions. Also works for non-evar variables. *)

let pf_unabs_evars gl ise n c0 =
  if n = 0 then c0 else
  let evv = Array.make n mkProp in
  let nev = ref 0 in
  let env0 = pf_env gl in
  let nenv0 = env_size env0 in
  let rec unabs i c = match kind_of_term c with
  | Rel j when i - j < !nev -> evv.(i - j)
  | App (f, a0) when isRel f ->
    let a = Array.map (unabs i) a0 in
    let j = i - destRel f in
    if j >= !nev then mkApp (f, a) else
    let ev, eva = destEvar evv.(j) in
    let nd = Array.length eva - nenv0 in
    if nd = 0 then mkApp (evv.(j), a) else
    let evarg k = if k < nd then a.(nd - 1 - k) else eva.(k) in
    let c' = mkEvar (ev, Array.init (nd + nenv0) evarg) in
    let na = Array.length a - nd in
    if na = 0 then c' else mkApp (c', Array.sub a nd na)
  | _ -> map_constr_with_binders ((+) 1) unabs i c in
  let push_rel = Environ.push_rel in
  let rec mk_evar j env i c = match kind_of_term c with
  | Prod (x, t, c1) when i < j ->
    mk_evar j (push_rel (x, None, unabs i t) env) (i + 1) c1
  | LetIn (x, b, t, c1) when i < j ->
    let _, _, c2 = destProd c1 in
    mk_evar j (push_rel (x, Some (unabs i b), unabs i t) env) (i + 1) c2
  | _ -> Evarutil.e_new_evar env ise (unabs i c) in
  let rec unabs_evars c =
    if !nev = n then unabs n c else match kind_of_term c with
  | Lambda (x, t, c1) when !nev < n ->
    let i = !nev in
    evv.(i) <- mk_evar (i + nb_evar_deps x) env0 i t;
    incr nev; unabs_evars c1
  | _ -> unabs !nev c in
  unabs_evars c0

(* }}} *)

(** Tactical extensions. {{{ **************************************************)

(* The TACTIC EXTEND facility can't be used for defining new user   *)
(* tacticals, because:                                              *)
(*  - the concrete syntax must start with a fixed string            *)
(*   We use the following workaround:                               *)
(*  - We use the (unparsable) "YouShouldNotTypeThis"  token for tacticals that      *)
(*    don't start with a token, then redefine the grammar and       *)
(*    printer using GEXTEND and set_pr_ssrtac, respectively.        *)

type ssrargfmt = ArgSsr of string | ArgCoq of argument_type | ArgSep of string

let ssrtac_name name = {
  mltac_plugin = "ssreflect";
  mltac_tactic = "ssr" ^ name;
}

let ssrtac_entry name n = {
  mltac_name = ssrtac_name name; 
  mltac_index = n;
}

let set_pr_ssrtac name prec afmt =
  let fmt = List.map (function ArgSep s -> Some s | _ -> None) afmt in
  let rec mk_akey = function
  | ArgSsr s :: afmt' -> ExtraArgType ("ssr" ^ s) :: mk_akey afmt'
  | ArgCoq a :: afmt' -> a :: mk_akey afmt'
  | ArgSep _ :: afmt' -> mk_akey afmt'
  | [] -> [] in
  let tacname = ssrtac_name name in
   Pptactic.declare_ml_tactic_pprule tacname [|
    { Pptactic.pptac_args = mk_akey afmt;
      Pptactic.pptac_prods = (prec, fmt) }
   |]

let ssrtac_atom loc name args = TacML (loc, ssrtac_entry name 0, args)
let ssrtac_expr = ssrtac_atom


let ssrevaltac ist gtac =
  Proofview.V82.of_tactic (eval_tactic_ist ist gtac)

(* fun gl -> let lfun = [tacarg_id, val_interp ist gl gtac] in
  interp_tac_gen lfun [] ist.debug tacarg_expr gl *)

(** Generic argument-based globbing/typing utilities *)

let interp_refine ist gl rc =
  let constrvars = extract_ltac_constr_values ist (pf_env gl) in
  let vars = { Pretyping.empty_lvar with
    Pretyping.ltac_constrs = constrvars; ltac_genargs = ist.lfun
  } in
  let kind = OfType (pf_concl gl) in
  let flags = {
    use_typeclasses = true;
    use_unif_heuristics = true;
    use_hook = None;
    fail_evar = false;
    expand_evars = true }
  in
  let sigma, c = understand_ltac flags (pf_env gl) (project gl) vars kind rc in
(*   pp(lazy(str"sigma@interp_refine=" ++ pr_evar_map None sigma)); *)
  pp(lazy(str"c@interp_refine=" ++ pr_constr c));
  (sigma, (sigma, c))

let pf_match = pf_apply (fun e s c t -> understand_tcc e s ~expected_type:t c)

(* Estimate a bound on the number of arguments of a raw constr. *)
(* This is not perfect, because the unifier may fail to         *)
(* typecheck the partial application, so we use a minimum of 5. *)
(* Also, we don't handle delayed or iterated coercions to       *)
(* FUNCLASS, which is probably just as well since these can     *)
(* lead to infinite arities.                                    *)

let splay_open_constr gl (sigma, c) =
  let env = pf_env gl in let t = Retyping.get_type_of env sigma c in
  Reductionops.splay_prod env sigma t

let nbargs_open_constr gl oc =
  let pl, _ = splay_open_constr gl oc in List.length pl

let interp_nbargs ist gl rc =
  try
    let rc6 = mkRApp rc (mkRHoles 6) in
    let sigma, t = interp_open_constr ist gl (rc6, None) in
    let si = sig_it gl in
    let gl = re_sig si sigma in
    6 + nbargs_open_constr gl t
  with _ -> 5

let pf_nbargs gl c = nbargs_open_constr gl (project gl, c)

let isAppInd gl c =
  try ignore (pf_reduce_to_atomic_ind gl c); true with _ -> false

let interp_view_nbimps ist gl rc =
  try
    let sigma, t = interp_open_constr ist gl (rc, None) in
    let si = sig_it gl in
    let gl = re_sig si sigma in
    let pl, c = splay_open_constr gl t in
    if isAppInd gl c then List.length pl else ~-(List.length pl)
  with _ -> 0

(* }}} *)

(** Tacticals (+, -, *, done, by, do, =>, first, and last). {{{ ***************)

(** Bracketing tactical *)

(* The tactic pretty-printer doesn't know that some extended tactics *)
(* are actually tacticals. To prevent it from improperly removing    *)
(* parentheses we override the parsing rule for bracketed tactic     *)
(* expressions so that the pretty-print always reflects the input.   *)
(* (Removing user-specified parentheses is dubious anyway).          *)

GEXTEND Gram
  GLOBAL: tactic_expr;
  ssrparentacarg: [[ "("; tac = tactic_expr; ")" -> !@loc, Tacexp tac ]];
  tactic_expr: LEVEL "0" [[ arg = ssrparentacarg -> TacArg arg ]];
END

(** The internal "done" and "ssrautoprop" tactics. *)

(* For additional flexibility, "done" and "ssrautoprop" are  *)
(* defined in Ltac.                                          *)
(* Although we provide a default definition in ssreflect,    *)
(* we look up the definition dynamically at each call point, *)
(* to allow for user extensions. "ssrautoprop" defaults to   *)
(* trivial.                                                  *)

let ssr_n_tac seed n gl =
  let name = if n = -1 then seed else ("ssr" ^ seed ^ string_of_int n) in
  let fail msg = Pp.msg_error (str msg); Errors.error msg in
  let tacname = 
    try Nametab.locate_tactic (qualid_of_ident (id_of_string name))
    with Not_found -> try Nametab.locate_tactic (ssrqid name)
    with Not_found ->
      if n = -1 then fail "The ssreflect library was not loaded"
      else fail ("The tactic "^name^" was not found") in
  let tacexpr = dummy_loc, Tacexpr.Reference (ArgArg (dummy_loc, tacname)) in
  Proofview.V82.of_tactic (eval_tactic (Tacexpr.TacArg tacexpr)) gl

let donetac n gl = ssr_n_tac "done" n gl

let ssrautoprop gl =
  try 
    let tacname = 
      try Nametab.locate_tactic (qualid_of_ident (id_of_string "ssrautoprop"))
      with Not_found -> Nametab.locate_tactic (ssrqid "ssrautoprop") in
    let tacexpr = dummy_loc, Tacexpr.Reference (ArgArg (dummy_loc, tacname)) in
    Proofview.V82.of_tactic (eval_tactic (Tacexpr.TacArg tacexpr)) gl
  with Not_found -> Proofview.V82.of_tactic (Auto.full_trivial []) gl

let () = ssrautoprop_tac := ssrautoprop

let tclBY tac = tclTHEN tac (donetac ~-1)

(** Tactical arguments. *)

(* We have four kinds: simple tactics, [|]-bracketed lists, hints, and swaps *)
(* The latter two are used in forward-chaining tactics (have, suffice, wlog) *)
(* and subgoal reordering tacticals (; first & ; last), respectively.        *)

(* Force use of the tactic_expr parsing entry, to rule out tick marks. *)
let pr_ssrtacarg _ _ prt = prt tacltop
ARGUMENT EXTEND ssrtacarg TYPED AS tactic PRINTED BY pr_ssrtacarg
| [ "YouShouldNotTypeThis" ] -> [ anomaly "Grammar placeholder match" ]
END
GEXTEND Gram
  GLOBAL: ssrtacarg;
  ssrtacarg: [[ tac = tactic_expr LEVEL "5" -> tac ]];
END

(* Lexically closed tactic for tacticals. *)
let pr_ssrtclarg _ _ prt tac = prt tacltop tac
ARGUMENT EXTEND ssrtclarg TYPED AS ssrtacarg
    PRINTED BY pr_ssrtclarg
| [ ssrtacarg(tac) ] -> [ tac ]
END
let eval_tclarg ist tac = ssrevaltac ist tac

let pr_ortacs prt = 
  let rec pr_rec = function
  | [None]           -> spc() ++ str "|" ++ spc()
  | None :: tacs     -> spc() ++ str "|" ++ pr_rec tacs
  | Some tac :: tacs -> spc() ++ str "| " ++ prt tacltop tac ++  pr_rec tacs
  | []                -> mt() in
  function
  | [None]           -> spc()
  | None :: tacs     -> pr_rec tacs
  | Some tac :: tacs -> prt tacltop tac ++ pr_rec tacs
  | []                -> mt()
let pr_ssrortacs _ _ = pr_ortacs

ARGUMENT EXTEND ssrortacs TYPED AS tactic option list PRINTED BY pr_ssrortacs
| [ ssrtacarg(tac) "|" ssrortacs(tacs) ] -> [ Some tac :: tacs ]
| [ ssrtacarg(tac) "|" ] -> [ [Some tac; None] ]
| [ ssrtacarg(tac) ] -> [ [Some tac] ]
| [ "|" ssrortacs(tacs) ] -> [ None :: tacs ]
| [ "|" ] -> [ [None; None] ]
END

let pr_hintarg prt = function
  | true, tacs -> hv 0 (str "[ " ++ pr_ortacs prt tacs ++ str " ]")
  | false, [Some tac] -> prt tacltop tac
  | _, _ -> mt()

let pr_ssrhintarg _ _ = pr_hintarg

let mk_hint tac = false, [Some tac]
let mk_orhint tacs = true, tacs
let nullhint = true, []
let nohint = false, []

ARGUMENT EXTEND ssrhintarg TYPED AS bool * ssrortacs PRINTED BY pr_ssrhintarg
| [ "[" "]" ] -> [ nullhint ]
| [ "[" ssrortacs(tacs) "]" ] -> [ mk_orhint tacs ]
| [ ssrtacarg(arg) ] -> [ mk_hint arg ]
END

ARGUMENT EXTEND ssrortacarg TYPED AS ssrhintarg PRINTED BY pr_ssrhintarg
| [ "[" ssrortacs(tacs) "]" ] -> [ mk_orhint tacs ]
END

let hinttac ist is_by (is_or, atacs) =
  let dtac = if is_by then donetac ~-1 else tclIDTAC in
  let mktac = function
  | Some atac -> tclTHEN (ssrevaltac ist atac) dtac
  | _ -> dtac in
  match List.map mktac atacs with
  | [] -> if is_or then dtac else tclIDTAC
  | [tac] -> tac
  | tacs -> tclFIRST tacs

(** The "-"/"+"/"*" tacticals.              USELESS SINCE COQ HAS NATIVE BULLETS

(* These are just visual cues to flag the beginning of the script for *)
(* new subgoals, when indentation is not appropriate (typically after *)
(* tactics that generate more than two subgoals).                     *)

TACTIC EXTEND ssrtclplus
| [ "YouShouldNotTypeThis" "+" ssrtclarg(arg) ] -> [ Proofview.V82.tactic (eval_tclarg ist arg) ]
END
set_pr_ssrtac "tclplus" 5 [ArgSep "+ "; ArgSsr "tclarg"]

TACTIC EXTEND ssrtclminus
| [ "YouShouldNotTypeThis" "-" ssrtclarg(arg) ] -> [ Proofview.V82.tactic (eval_tclarg ist arg) ]
END
set_pr_ssrtac "tclminus" 5 [ArgSep "- "; ArgSsr "tclarg"]

TACTIC EXTEND ssrtclstar
| [ "YouShouldNotTypeThis" "*" ssrtclarg(arg) ] -> [ Proofview.V82.tactic (eval_tclarg ist arg) ]
END
set_pr_ssrtac "tclstar" 5 [ArgSep "* "; ArgSsr "tclarg"]

let gen_tclarg = in_gen (rawwit wit_ssrtclarg)

GEXTEND Gram
  GLOBAL: tactic tactic_mode;
  tactic: [
    [ "+"; tac = ssrtclarg -> ssrtac_expr !@loc "tclplus" [gen_tclarg tac]
    | "-"; tac = ssrtclarg -> ssrtac_expr !@loc "tclminus" [gen_tclarg tac]
    | "*"; tac = ssrtclarg -> ssrtac_expr !@loc "tclstar" [gen_tclarg tac] 
    ] ];
  tactic_mode: [
    [ "+"; tac = G_vernac.subgoal_command -> tac None
    | "-"; tac = G_vernac.subgoal_command -> tac None
    | "*"; tac = G_vernac.subgoal_command -> tac None
    ] ];
END

** The "by" tactical. *)

let pr_hint prt arg =
  if arg = nohint then mt() else str "by " ++ pr_hintarg prt arg
let pr_ssrhint _ _ = pr_hint

ARGUMENT EXTEND ssrhint TYPED AS ssrhintarg PRINTED BY pr_ssrhint
| [ ]                       -> [ nohint ]
END

TACTIC EXTEND ssrtclby
| [ "YouShouldNotTypeThis" ssrhint(tac) ] -> [ Proofview.V82.tactic (hinttac ist true tac) ]
END
set_pr_ssrtac "tclby" 0 [ArgSsr "hint"]

(* We can't parse "by" in ARGUMENT EXTEND because it will only be made *)
(* into a keyword in ssreflect.v; so we anticipate this in GEXTEND.    *)

GEXTEND Gram
  GLOBAL: ssrhint simple_tactic;
  ssrhint: [[ "by"; arg = ssrhintarg -> arg ]];
  simple_tactic: [
  [ "by"; arg = ssrhintarg ->
    let garg = in_gen (rawwit wit_ssrhint) arg in
    ssrtac_atom !@loc "tclby" [garg]
  ] ];
END
(* }}} *)

(** The "in" pseudo-tactical {{{ **********************************************)

(* We can't make "in" into a general tactical because this would create a  *)
(* crippling conflict with the ltac let .. in construct. Hence, we add     *)
(* explicitly an "in" suffix to all the extended tactics for which it is   *)
(* relevant (including move, case, elim) and to the extended do tactical   *)
(* below, which yields a general-purpose "in" of the form do [...] in ...  *)

(* This tactical needs to come before the intro tactics because the latter *)
(* must take precautions in order not to interfere with the discharged     *)
(* assumptions. This is especially difficult for discharged "let"s, which  *)
(* the default simpl and unfold tactics would erase blindly.               *)

(** Clear switch *)

let cleartac clr = check_hyps_uniq [] clr; clear (hyps_ids clr)

(* type ssrwgen = ssrclear * ssrhyp * string *)

let pr_wgen = function 
  | (clr, Some((id,k),None)) -> spc() ++ pr_clear mt clr ++ str k ++ pr_hoi id
  | (clr, Some((id,k),Some p)) ->
      spc() ++ pr_clear mt clr ++ str"(" ++ str k ++ pr_hoi id ++ str ":=" ++
        pr_cpattern p ++ str ")"
  | (clr, None) -> spc () ++ pr_clear mt clr
let pr_ssrwgen _ _ _ = pr_wgen

(* no globwith for char *)
ARGUMENT EXTEND ssrwgen
  TYPED AS ssrclear * ((ssrhoi_hyp * string) * cpattern option) option
  PRINTED BY pr_ssrwgen
| [ ssrclear_ne(clr) ] -> [ clr, None ]
| [ ssrhoi_hyp(hyp) ] -> [ [], Some((hyp, " "), None) ]
| [ "@" ssrhoi_hyp(hyp) ] -> [ [], Some((hyp, "@"), None) ]
| [ "(" ssrhoi_id(id) ":=" lcpattern(p) ")" ] ->
  [ [], Some ((id," "),Some p) ]
| [ "(" ssrhoi_id(id) ")" ] -> [ [], Some ((id,"("), None) ]
| [ "(@" ssrhoi_id(id) ":=" lcpattern(p) ")" ] ->
  [ [], Some ((id,"@"),Some p) ]
| [ "(" "@" ssrhoi_id(id) ":=" lcpattern(p) ")" ] ->
  [ [], Some ((id,"@"),Some p) ]
END

type ssrclseq = InGoal | InHyps
 | InHypsGoal | InHypsSeqGoal | InSeqGoal | InHypsSeq | InAll | InAllHyps

let pr_clseq = function
  | InGoal | InHyps -> mt ()
  | InSeqGoal       -> str "|- *"
  | InHypsSeqGoal   -> str " |- *"
  | InHypsGoal      -> str " *"
  | InAll           -> str "*"
  | InHypsSeq       -> str " |-"
  | InAllHyps       -> str "* |-"

let wit_ssrclseq = add_genarg "ssrclseq" pr_clseq
let pr_clausehyps = pr_list pr_spc pr_wgen
let pr_ssrclausehyps _ _ _ = pr_clausehyps

ARGUMENT EXTEND ssrclausehyps 
TYPED AS ssrwgen list PRINTED BY pr_ssrclausehyps
| [ ssrwgen(hyp) "," ssrclausehyps(hyps) ] -> [ hyp :: hyps ]
| [ ssrwgen(hyp) ssrclausehyps(hyps) ] -> [ hyp :: hyps ]
| [ ssrwgen(hyp) ] -> [ [hyp] ]
END

(* type ssrclauses = ssrahyps * ssrclseq *)

let pr_clauses (hyps, clseq) = 
  if clseq = InGoal then mt ()
  else str "in " ++ pr_clausehyps hyps ++ pr_clseq clseq
let pr_ssrclauses _ _ _ = pr_clauses

ARGUMENT EXTEND ssrclauses TYPED AS ssrwgen list * ssrclseq
    PRINTED BY pr_ssrclauses
  | [ "in" ssrclausehyps(hyps) "|-" "*" ] -> [ hyps, InHypsSeqGoal ]
  | [ "in" ssrclausehyps(hyps) "|-" ]     -> [ hyps, InHypsSeq ]
  | [ "in" ssrclausehyps(hyps) "*" ]      -> [ hyps, InHypsGoal ]
  | [ "in" ssrclausehyps(hyps) ]          -> [ hyps, InHyps ]
  | [ "in" "|-" "*" ]                     -> [ [], InSeqGoal ]
  | [ "in" "*" ]                          -> [ [], InAll ]
  | [ "in" "*" "|-" ]                     -> [ [], InAllHyps ]
  | [ ]                                   -> [ [], InGoal ]
END

let nohide = mkRel 0
let hidden_goal_tag = "the_hidden_goal"

(* Reduction that preserves the Prod/Let spine of the "in" tactical. *)

let inc_safe n = if n = 0 then n else n + 1
let rec safe_depth c = match kind_of_term c with
| LetIn (Name x, _, _, c') when is_discharged_id x -> safe_depth c' + 1
| LetIn (_, _, _, c') | Prod (_, _, c') -> inc_safe (safe_depth c')
| _ -> 0 

let red_safe r e s c0 =
  let rec red_to e c n = match kind_of_term c with
  | Prod (x, t, c') when n > 0 ->
    let t' = r e s t in let e' = Environ.push_rel (x, None, t') e in
    mkProd (x, t', red_to e' c' (n - 1))
  | LetIn (x, b, t, c') when n > 0 ->
    let t' = r e s t in let e' = Environ.push_rel (x, None, t') e in
    mkLetIn (x, r e s b, t', red_to e' c' (n - 1))
  | _ -> r e s c in
  red_to e c0 (safe_depth c0)

let check_wgen_uniq gens =
  let clears = List.flatten (List.map fst gens) in
  check_hyps_uniq [] clears;
  let ids = CList.map_filter
    (function (_,Some ((id,_),_)) -> Some (hoi_id id) | _ -> None) gens in
  let rec check ids = function
  | id :: _ when List.mem id ids ->
    errorstrm (str"Duplicate generalization " ++ pr_id id)
  | id :: hyps -> check (id :: ids) hyps
  | [] -> () in
  check [] ids

let pf_clauseids gl gens clseq =
  let keep_clears = List.map (fun (x, _) -> x, None) in
  if gens <> [] then (check_wgen_uniq gens; gens) else
  if clseq <> InAll && clseq <> InAllHyps then keep_clears gens else
  Errors.error "assumptions should be named explicitly"

let hidden_clseq = function InHyps | InHypsSeq | InAllHyps -> true | _ -> false

let hidetacs clseq idhide cl0 =
  if not (hidden_clseq clseq) then  [] else
  [posetac idhide cl0;
   Proofview.V82.of_tactic (convert_concl_no_check (mkVar idhide))]

let discharge_hyp (id', (id, mode)) gl =
  let cl' = subst_var id (pf_concl gl) in
  match pf_get_hyp gl id, mode with
  | (_, None, t), _ | (_, Some _, t), "(" -> 
     apply_type (mkProd (Name id', t, cl')) [mkVar id] gl
  | (_, Some v, t), _ ->
     Proofview.V82.of_tactic (convert_concl (mkLetIn (Name id', v, t, cl'))) gl

let endclausestac id_map clseq gl_id cl0 gl =
  let not_hyp' id = not (List.mem_assoc id id_map) in
  let orig_id id = try List.assoc id id_map with _ -> id in
  let dc, c = Term.decompose_prod_assum (pf_concl gl) in
  let hide_goal = hidden_clseq clseq in
  let c_hidden = hide_goal && c = mkVar gl_id in
  let rec fits forced = function
  | (id, _) :: ids, (Name id', _, _) :: dc' when id' = id ->
    fits true (ids, dc')
  | ids, dc' ->
    forced && ids = [] && (not hide_goal || dc' = [] && c_hidden) in
  let rec unmark c = match kind_of_term c with
  | Var id when hidden_clseq clseq && id = gl_id -> cl0
  | Prod (Name id, t, c') when List.mem_assoc id id_map ->
    mkProd (Name (orig_id id), unmark t, unmark c')
  | LetIn (Name id, v, t, c') when List.mem_assoc id id_map ->
    mkLetIn (Name (orig_id id), unmark v, unmark t, unmark c')
  | _ -> map_constr unmark c in
  let utac hyp =
    Proofview.V82.of_tactic 
     (convert_hyp_no_check (map_named_declaration unmark hyp)) in
  let utacs = List.map utac (pf_hyps gl) in
  let ugtac gl' =
    Proofview.V82.of_tactic
      (convert_concl_no_check (unmark (pf_concl gl'))) gl' in
  let ctacs = if hide_goal then [clear [gl_id]] else [] in
  let mktac itacs = tclTHENLIST (itacs @ utacs @ ugtac :: ctacs) in
  let itac (_, id) = Proofview.V82.of_tactic (introduction id) in
  if fits false (id_map, List.rev dc) then mktac (List.map itac id_map) gl else
  let all_ids = ids_of_rel_context dc @ pf_ids_of_hyps gl in
  if List.for_all not_hyp' all_ids && not c_hidden then mktac [] gl else
  Errors.error "tampering with discharged assumptions of \"in\" tactical"

let is_id_constr c = match kind_of_term c with
  | Lambda(_,_,c) when isRel c -> 1 = destRel c
  | _ -> false

let red_product_skip_id env sigma c = match kind_of_term c with
  | App(hd,args) when Array.length args = 1 && is_id_constr hd -> args.(0)
  | _ -> try Tacred.red_product env sigma c with _ -> c

let abs_wgen keep_let ist f gen (gl,args,c) =
  let sigma, env = project gl, pf_env gl in
  let evar_closed t p =
    if occur_existential t then
      Errors.user_err_loc (loc_of_cpattern p,"ssreflect",
        pr_constr_pat t ++
        str" contains holes and matches no subterm of the goal") in
  match gen with
  | _, Some ((x, mode), None) when mode = "@" || (mode = " " && keep_let) ->
     let x = hoi_id x in
     let _, bo, ty = pf_get_hyp gl x in
     gl,
     (if bo <> None then args else mkVar x :: args),
     mkProd_or_LetIn (Name (f x),bo,ty) (subst_var x c)
  | _, Some ((x, _), None) ->
     let x = hoi_id x in
     gl, mkVar x :: args, mkProd (Name (f x), pf_get_hyp_typ gl x, subst_var x c)
  | _, Some ((x, "@"), Some p) -> 
     let x = hoi_id x in
     let cp = interp_cpattern ist gl p None in
     let (t, ucst), c =
       try fill_occ_pattern ~raise_NoMatch:true env sigma c cp None 1
       with NoMatch -> redex_of_pattern env cp, c in
     evar_closed t p;
     let ut = red_product_skip_id env sigma t in
     let gl, ty = pf_type_of gl t in
     pf_merge_uc ucst gl, args, mkLetIn(Name (f x), ut, ty, c)
  | _, Some ((x, _), Some p) ->
     let x = hoi_id x in
     let cp = interp_cpattern ist gl p None in
     let (t, ucst), c =
       try fill_occ_pattern ~raise_NoMatch:true env sigma c cp None 1
       with NoMatch -> redex_of_pattern env cp, c in
     evar_closed t p;
     let gl, ty = pf_type_of gl t in
     pf_merge_uc ucst gl, t :: args, mkProd(Name (f x), ty, c)
  | _ -> gl, args, c

let clr_of_wgen gen clrs = match gen with
  | clr, Some ((x, _), None) ->
     let x = hoi_id x in
     cleartac clr :: cleartac [SsrHyp(Loc.ghost,x)] :: clrs
  | clr, _ -> cleartac clr :: clrs
    
let tclCLAUSES ist tac (gens, clseq) gl =
  if clseq = InGoal || clseq = InSeqGoal then tac gl else
  let clr_gens = pf_clauseids gl gens clseq in
  let clear = tclTHENLIST (List.rev(List.fold_right clr_of_wgen clr_gens [])) in
  let gl_id = mk_anon_id hidden_goal_tag gl in
  let cl0 = pf_concl gl in
  let dtac gl =
    let c = pf_concl gl in
    let gl, args, c =
      List.fold_right (abs_wgen true ist mk_discharged_id) gens (gl,[], c) in
    apply_type c args gl in
  let endtac =
    let id_map = CList.map_filter (function
      | _, Some ((x,_),_) -> let id = hoi_id x in Some (mk_discharged_id id, id)
      | _, None -> None) gens in
    endclausestac id_map clseq gl_id cl0 in
  tclTHENLIST (hidetacs clseq gl_id cl0 @ [dtac; clear; tac; endtac]) gl
(* }}} *)

(* We must avoid zeta-converting any "let"s created by the "in" tactical. *)

let tacred_simpl gl =
  let simpl_expr =
    Genredexpr.(
      Simpl(Redops.make_red_flag[FBeta;FIota;FZeta;FDeltaBut []],None)) in
  let esimpl, _ = Redexpr.reduction_of_red_expr (pf_env gl) simpl_expr in
  let simpl env sigma c = snd (esimpl env sigma c) in
  simpl

let safe_simpltac n gl =
  if n = ~-1 then
    let cl= red_safe (tacred_simpl gl) (pf_env gl) (project gl) (pf_concl gl) in
    Proofview.V82.of_tactic (convert_concl_no_check cl) gl
  else
    ssr_n_tac "simpl" n gl

let simpltac = function
  | Simpl n -> safe_simpltac n
  | Cut n -> tclTRY (donetac n)
  | SimplCut (n,m) -> tclTHEN (safe_simpltac m) (tclTRY (donetac n))
  | Nop -> tclIDTAC

let pf_mkprod gl c ?(name=constr_name c) cl =
  let gl, t = pf_type_of gl c in
  if name <> Anonymous || noccurn 1 cl then gl, mkProd (name, t, cl) else
  gl, mkProd (Name (pf_type_id gl t), t, cl)

let pf_abs_prod name gl c cl = pf_mkprod gl c ~name (subst_term c cl)

(** Extended intro patterns {{{ ***********************************************)

(* There are two ways of "applying" a view to term:            *)
(*  1- using a view hint if the view is an instance of some    *)
(*     (reflection) inductive predicate.                       *)
(*  2- applying the view if it coerces to a function, adding   *)
(*     implicit arguments.                                     *)
(* They require guessing the view hints and the number of      *)
(* implicits, respectively, which we do by brute force.        *)

let view_error s gv =
  errorstrm (str ("Cannot " ^ s ^ " view ") ++ pr_term gv)

let interp_view ist si env sigma gv v rid =
  match v with
  | GApp (loc, GHole _, rargs) ->
    let rv = GApp (loc, rid, rargs) in
    snd (interp_open_constr ist (re_sig si sigma) (rv, None))
  | rv ->
  let interp rc rargs =
    interp_open_constr ist (re_sig si sigma) (mkRApp rc rargs, None) in
  let rec simple_view rargs n =
    if n < 0 then view_error "use" gv else
    try interp rv rargs with _ -> simple_view (mkRHole :: rargs) (n - 1) in
  let view_nbimps = interp_view_nbimps ist (re_sig si sigma) rv in
  let view_args = [mkRApp rv (mkRHoles view_nbimps); rid] in
  let rec view_with = function
  | [] -> simple_view [rid] (interp_nbargs ist (re_sig si sigma) rv)
  | hint :: hints -> try interp hint view_args with _ -> view_with hints in
  snd (view_with (if view_nbimps < 0 then [] else Ssrvernac.viewtab.(0)))

let top_id = mk_internal_id "top assumption"

let tclEQINTROSviewtac_ref = ref (fun ~ist ~next -> assert false)

let with_view ist ~next si env (gl0 : (Proof_type.goal * tac_ctx) Evd.sigma) c name cl prune (conclude : constr -> constr -> tac_ctx tac_a) clr =
  let c2r ist x = { ist with lfun =
    Id.Map.add top_id (Value.of_constr x) ist.lfun } in
  let terminate (sigma, c') =
    let sigma = Typeclasses.resolve_typeclasses ~fail:false env sigma in
    let c' = Reductionops.nf_evar sigma c' in
    let n, c', _, ucst = without_ctx pf_abs_evars gl0 (sigma, c') in
    let c' = if not prune then c' else without_ctx pf_abs_cterm gl0 n c' in
    let gl0 = pf_merge_uc ucst gl0 in
    let gl0, ap =
      let gl0, ctx = pull_ctx gl0 in
      let gl0, ap = pf_abs_prod name gl0 c' (prod_applist cl [c]) in
      push_ctx ctx gl0, ap in
    let gl0 = pf_merge_uc_of sigma gl0 in
    ap, c', gl0 in
  let rec loop (sigma, c') = function
  | [] ->
      let ap, c', gl = terminate (sigma, c') in
      ap, c', conclude ap c' gl
  | f :: view ->
      let ist, rid =
        match kind_of_term c' with
        | Var id -> ist,mkRVar id
        | _ -> c2r ist c',mkRltacVar top_id in
      let v = intern_term ist env f in
      let tactic_view = mkSsrRef "tactic_view" in
      match v with
      | GApp (loc, GRef (_,box,None), [GHole (_,_,_, Some tac)])
       when has_type tac (glbwit Constrarg.wit_tactic) &&
            eq_gr box tactic_view -> begin
        let tac = out_gen (glbwit Constrarg.wit_tactic) tac in
        match tac with
        | TacLetIn (false,binds,TacArg(l0,TacCall(l,k,args))) ->
            let ap, c', gl = terminate (sigma, c') in
            let wid, gl = with_ctx new_wild_id gl in
            let argid = ArgVar(dummy_loc,wid) in
            let tac =
              TacLetIn (false,binds, 
                TacArg(l0,TacCall(l,k,args @ [ Reference argid ]))) in
            let tac = tac_ctx (ssrevaltac ist tac) in
            let tac = tclTHENLIST_a [
                tac_ctx (apply_type ap [c']);
                tac_ctx (introid wid);
                (!tclEQINTROSviewtac_ref ~ist ~next tac (tac_ctx tclIDTAC));
                (tac_ctx (clear (hyps_ids clr))) ] in
            let tac_check _ max gl =
              if view <> [] then Errors.error "No view can follow a tactic-view"
              else tac_ctx tclIDTAC gl in
            ap,c',tclTHEN_i_max tac tac_check gl
        | _ -> Errors.error "Only simple tactic call allowed as tactic-view" end
      | _ -> loop (interp_view ist si env sigma f v rid) view
  in loop

let pfa_with_view ist ?(next=ref []) (prune, view) cl c conclude clr gl =
  let env, sigma, si =
    without_ctx pf_env gl, Refiner.project gl, without_ctx sig_it gl in
  with_view
    ist ~next si env gl c (constr_name c) cl prune conclude clr (sigma, c) view 

let pf_with_view_linear ist gl v cl c =
  let x,y,gl =
    pfa_with_view ist v cl c (fun _ _ -> tac_ctx tclIDTAC) []
      (push_ctx (new_ctx ()) gl) in
  let gl, _ = pull_ctxs gl in
  assert(List.length (sig_it gl) = 1);
  x,y,re_sig (List.hd (sig_it gl)) (Refiner.project gl)

let injecteq_id = mk_internal_id "injection equation"

let pf_nb_prod gl = nb_prod (pf_concl gl)

let rev_id = mk_internal_id "rev concl"

let revtoptac n0 gl =
  let n = pf_nb_prod gl - n0 in
  let dc, cl = decompose_prod_n n (pf_concl gl) in
  let dc' = dc @ [Name rev_id, compose_prod (List.rev dc) cl] in
  let f = compose_lam dc' (mkEtaApp (mkRel (n + 1)) (-n) 1) in
  refine (mkApp (f, [|Evarutil.mk_new_meta ()|])) gl

let equality_inj l b id c gl =
  let msg = ref "" in
  try Proofview.V82.of_tactic (Equality.inj l b None c) gl
  with
    | Compat.Exc_located(_,Errors.UserError (_,s))
    | Errors.UserError (_,s)
  when msg := Pp.string_of_ppcmds s;
       !msg = "Not a projectable equality but a discriminable one." ||
       !msg = "Nothing to inject." ->
    msg_warning (str !msg);
    discharge_hyp (id, (id, "")) gl

let injectidl2rtac id c gl =
  tclTHEN (equality_inj None true id c) (revtoptac (pf_nb_prod gl)) gl

let injectl2rtac c = match kind_of_term c with
| Var id -> injectidl2rtac id (mkVar id, NoBindings)
| _ ->
  let id = injecteq_id in
  tclTHENLIST [havetac id c; injectidl2rtac id (mkVar id, NoBindings); clear [id]]

let is_injection_case c gl =
  let gl, cty = pf_type_of gl c in
  let (mind,_), _ = pf_reduce_to_quantified_ind gl cty in
  eq_gr (IndRef mind) (build_coq_eq ())

let perform_injection c gl =
  let gl, cty = pf_type_of gl c in
  let mind, t = pf_reduce_to_quantified_ind gl cty in
  let dc, eqt = decompose_prod t in
  if dc = [] then injectl2rtac c gl else
  if not (closed0 eqt) then
    Errors.error "can't decompose a quantified equality" else
  let cl = pf_concl gl in let n = List.length dc in
  let c_eq = mkEtaApp c n 2 in
  let cl1 = mkLambda (Anonymous, mkArrow eqt cl, mkApp (mkRel 1, [|c_eq|])) in
  let id = injecteq_id in
  let id_with_ebind = (mkVar id, NoBindings) in
  let injtac = tclTHEN (introid id) (injectidl2rtac id id_with_ebind) in 
  tclTHENLAST (Proofview.V82.of_tactic (apply (compose_lam dc cl1))) injtac gl  
let ssrscasetac ?ind force_inj c gl = 
  if force_inj || is_injection_case c gl then perform_injection c gl
  else simplest_newcase ?ind c gl 

let intro_all gl =
  let dc, _ = Term.decompose_prod_assum (pf_concl gl) in
  tclTHENLIST (List.map anontac (List.rev dc)) gl

let rec intro_anon gl =
  try anontac (List.hd (fst (Term.decompose_prod_n_assum 1 (pf_concl gl)))) gl
  with err0 -> try tclTHEN red_in_concl intro_anon gl with _ -> raise err0
  (* with _ -> Errors.error "No product even after reduction" *)

let rec fst_unused_prod red tac = PG.(enter { enter = fun gl ->
  let sigma = Sigma.to_evar_map (sigma gl) in
  let concl = Evarutil.nf_evar sigma (concl (assume gl)) in
  match kind_of_term concl with
  | Prod (id,_,tgt) | LetIn(id,_,_,tgt) ->
      if noccurn 1 tgt then tac id
      else TN.tclTHEN (old_tac intro_anon) (fst_unused_prod false tac)
  | _ -> if red then TN.tclZEROMSG (str"No product even after head-reduction.")
         else TN.tclTHEN (old_tac hnf_in_concl) (fst_unused_prod true tac)
})
;;

let introid_fast orig name = 
  fst_unused_prod false (fun id -> orig := id; old_tac (introid name))
let intro_anon_fast = fst_unused_prod false (fun _ -> old_tac intro_anon)

let intro_anon ?(speed=`Slow) () =
  if speed = `Slow then intro_anon else new_tac intro_anon_fast

let intro_anon_a gl =
  tac_ctx (intro_anon ~speed:(snd (pull_ctx gl)).speed ()) gl

(* we reduce head beta redexes *)
let introid ?(speed=`Slow) ?(orig=ref Anonymous) name =
  if speed = `Slow then introid ~orig name
  else tclTHEN (fun gl ->
   let g, env = pf_concl gl, pf_env gl in
   match kind_of_term g with
   | App (hd, _) when isLambda hd -> 
     let g = Closure.whd_val (betared env) (Closure.inject g) in
     new_tac (convert_concl_no_check g) gl
   | _ -> tclIDTAC gl)
  (new_tac (introid_fast orig name))
;;

let introid_a ?orig name gl =
  tac_ctx (introid ~speed:(snd (pull_ctx gl)).speed ?orig name) gl

let speed_to_next_NDP gl =
  match (snd (pull_ctx gl)).speed with
  | `Slow -> tac_ctx tclIDTAC gl
  | `Fast ->
       tac_ctx (new_tac (fst_unused_prod false (fun _ -> old_tac tclIDTAC))) gl

let with_top tac gl =
  let speed = (snd (pull_ctx gl)).speed in
  tac_ctx
    (tclTHENLIST [ introid ~speed top_id; tac (mkVar top_id); clear [top_id]])
    gl

let tclTHENS_nonstrict tac tacl taclname gl =
  let tacres = tac gl in
  let n_gls = List.length (sig_it tacres) in
  let n_tac = List.length tacl in
  if n_gls = n_tac then tclTHENS_a (fun _ -> tacres) tacl gl else
  if n_gls = 0 then tacres else
  let pr_only n1 n2 = if n1 < n2 then str "only " else mt () in
  let pr_nb n1 n2 name =
    pr_only n1 n2 ++ int n1 ++ str (" " ^ String.plural n1 name) in
  errorstrm (pr_nb n_tac n_gls taclname ++ spc ()
             ++ str "for " ++ pr_nb n_gls n_tac "subgoal")

let rec is_name_in_ipats name = function
  | IpatSimpl(clr,_) :: tl -> 
      List.exists (function SsrHyp(_,id) -> id = name) clr 
      || is_name_in_ipats name tl
  | IpatId id :: tl -> id = name || is_name_in_ipats name tl
  | IpatCase(`Regular l) :: tl -> is_name_in_ipats name (List.flatten l @ tl)
  | IpatCase(`Block _) :: _ -> true
  | _ :: tl -> is_name_in_ipats name tl
  | [] -> false

let rec nat_of_n n =
  if n = 0 then mkConstruct path_of_O
  else mkApp (mkConstruct path_of_S, [|nat_of_n (n-1)|])

let ssr_abstract_id = Summary.ref "~name:SSR:abstractid" 0

let mk_abstract_id () = incr ssr_abstract_id; nat_of_n !ssr_abstract_id

let ssrmkabs id gl =
  let env, concl = pf_env gl, pf_concl gl in
  let step = { run = begin fun sigma ->
    let sigma = Sigma.to_evar_map sigma in
    let sigma, abstract_proof, abstract_ty =
      let sigma, (ty, _) =
        Evarutil.new_type_evar env sigma Evd.univ_flexible_alg in
      let sigma, ablock = mkSsrConst "abstract_lock" env sigma in
      let sigma = Sigma.Unsafe.of_evar_map sigma in
      let Sigma (lock, sigma, _) = Evarutil.new_evar env sigma ablock in
      let sigma = Sigma.to_evar_map sigma in
      let sigma, abstract = mkSsrConst "abstract" env sigma in
      let abstract_ty = mkApp(abstract, [|ty;mk_abstract_id ();lock|]) in
      let sigma = Sigma.Unsafe.of_evar_map sigma in
      let Sigma (m, sigma, _) = Evarutil.new_evar env sigma abstract_ty in
      let sigma = Sigma.to_evar_map sigma in
      sigma, m, abstract_ty in
    let sigma, kont =
      let rd = Name id, None, abstract_ty in
      let sigma = Sigma.Unsafe.of_evar_map sigma in
      let Sigma (ev, sigma, _) = Evarutil.new_evar (Environ.push_rel rd env) sigma concl in
      let sigma = Sigma.to_evar_map sigma in
      (sigma, ev)
    in
    pp(lazy(pr_constr concl));
    let term = mkApp (mkLambda(Name id,abstract_ty,kont) ,[|abstract_proof|]) in
    let sigma, _ = Typing.type_of env sigma term in
    Sigma.Unsafe.of_pair (term, sigma)
  end } in
  Proofview.V82.of_tactic
    (Proofview.tclTHEN
      (Tactics.New.refine step)
      (Proofview.tclFOCUS 1 3 Proofview.shelve)) gl

let ssrmkabstac ids =
  List.fold_right (fun id tac -> tclTHENFIRST (ssrmkabs id) tac) ids tclIDTAC

(* introstac: for "move" and "clear", tclEQINTROS: for "case" and "elim" *)
(* This block hides the spaghetti-code needed to implement the only two  *)
(* tactics that should be used to process intro patters.                 *)
(* The difficulty is that we don't want to always rename, but we can     *)
(* compute needeed renamings only at runtime, so we theread a tree like  *)
(* imperativestructure so that outer renamigs are inherited by inner     *)
(* ipts and that the cler performed at the end of ipatstac clears hyps   *)
(* eventually renamed at runtime.                                        *)

let delayed_clear force rest clr gl = 
  let gl, ctx = pull_ctx gl in
  let hyps = pf_hyps gl in
  let () = if not force then List.iter (check_hyp_exists hyps) clr in
  if List.exists (fun x -> force || is_name_in_ipats (hyp_id x) rest) clr then
    let ren_clr, ren = 
      List.split (List.map (fun x ->
        let x = hyp_id x in
        let x' = mk_anon_id (string_of_id x) gl in
        x', (x, x')) clr) in
    let ctx = { ctx with delayed_clears = ren_clr @ ctx.delayed_clears } in
    let gl = push_ctx ctx gl in
    tac_ctx (Proofview.V82.of_tactic (rename_hyp ren)) gl 
  else
    let ctx = { ctx with delayed_clears = hyps_ids clr @ ctx.delayed_clears } in
    let gl = push_ctx ctx gl in
    tac_ctx tclIDTAC gl
      

type block_names = (int * Term.types array) option

let (introstac : ?ist:Tacinterp.interp_sign -> ssripats -> Proof_type.tactic),
    (tclEQINTROS : ?ind:block_names ref -> ?ist:Tacinterp.interp_sign ->
                     Proof_type.tactic -> Proof_type.tactic -> ssripats ->
                      Proof_type.tactic),
    (tclEQINTROSviewtac : ist:Tacinterp.interp_sign -> next:ssripats ref ->
                            tac_ctx tac_a -> tac_ctx tac_a -> tac_ctx tac_a)
=

  let rec ipattac ?ist ~next p : tac_ctx tac_a = fun gl ->
    pp(lazy(str"ipattac: " ++ pr_ipat p));
    match p with
    | IpatSeed _ -> Errors.anomaly(str"IpatSeed is to be used for parsing only")
    | IpatWild ->
        let id, gl = with_ctx new_wild_id gl in
        introid_a id gl
    | IpatTmpId ->
        let (id, orig), gl = with_ctx new_tmp_id gl in
        introid_a ~orig id gl
    | IpatCase(`Regular iorpat) ->
        tclIORPAT ?ist (with_top (ssrscasetac false)) iorpat gl
    | IpatCase(`Block (before,(id_side),after)) ->
        let ind = ref None in
        tclTHEN_i_max
          (with_top (ssrscasetac ~ind false))
          (block_intro ?ist ~ind id_side
            (List.map (ipatstac ?ist) before)
            (List.map (ipatstac ?ist)  after)) gl
    | IpatInj iorpat ->
        tclIORPAT ?ist (with_top (ssrscasetac true)) iorpat gl
    | IpatRw (occ, dir) ->
        with_top (ipat_rewrite occ dir) gl
    | IpatId id -> introid_a id gl
    | IpatNewHidden idl -> tac_ctx (ssrmkabstac idl) gl
    | IpatSimpl (clr, sim) ->
        tclTHEN_a (delayed_clear false !next clr) (tac_ctx (simpltac sim)) gl
    | IpatAll -> tac_ctx intro_all gl
    | IpatAnon -> intro_anon_a gl
    | IpatNoop -> tac_ctx tclIDTAC gl
    | IpatFastMode ->
        let gl, ctx = pull_ctx gl in
        let gl = push_ctx { ctx with speed = `Fast } gl in
        tac_ctx tclIDTAC gl
    | IpatView v ->
        let ist =
          match ist with Some x -> x | _ -> anomaly "ipat: view with no ist" in
        let next_keeps =
          match !next with (IpatCase _ | IpatRw _)::_ -> false | _ -> true in
        let top_id = ref top_id in
        tclTHENLIST_a [
          speed_to_next_NDP;
          (move_top_with_view ~next next_keeps top_id (next_keeps,v) ist);
          (fun gl ->
             let hyps = without_ctx pf_hyps gl in
             if not next_keeps && test_hypname_exists hyps !top_id then
               delayed_clear true !next [SsrHyp (dummy_loc,!top_id)] gl
             else tac_ctx tclIDTAC gl)]
        gl
             
  and block_intro ?ist ~ind prefix_side before after nth max gl =
    let nparams, ktypes =
      match !ind with
      | Some x -> x
      | None -> Errors.anomaly (str "block_intro with no ind info") in
    let n_before = List.length before in
    let n_after = List.length after in
    let n_ks = Array.length ktypes in
    if max <> n_before + n_after + n_ks then
      let n_gls = max in
      let pr_only n1 n2 = if n1 < n2 then str "only " else mt () in
      let pr_nb n1 n2 name =
        pr_only n1 n2 ++ int n1 ++ str (" "^String.plural n1 name) in
      errorstrm (pr_nb (n_before + n_ks + n_after) n_gls "intro pattern"
        ++ spc () ++ str "for "
        ++ pr_nb n_gls (n_before + n_ks + n_after) "subgoal")
    else
    let ipat_of_name name =
      match prefix_side, name with
      | `Anon, _ -> IpatAnon
      | `Wild, _ -> IpatWild
      | _, Anonymous -> IpatAnon
      | `Id(prefix,side), Name id ->
          let id = Id.to_string id in
          match side with
          | `Pre -> IpatId (Id.of_string (Id.to_string prefix ^ id))
          | `Post -> IpatId (Id.of_string (id ^ Id.to_string prefix)) in
    let rec ipat_of_ty n t =
      match kind_of_type t with
      | CastType(t,_) ->  ipat_of_ty n t
      | ProdType(name,_,tgt) | LetInType(name,_,_,tgt) ->
          (if n<= 0 then [ipat_of_name name] else []) @
          ipat_of_ty (n-1) tgt
      | AtomicType _ | SortType _ -> [] in
    if nth <= n_before then
      List.nth before (nth-1) gl
    else if nth > n_before && nth <= n_before + n_ks then
      let ktype = ktypes.(nth - 1 - n_before) in
      let ipats = ipat_of_ty nparams ktype in
      pp(lazy(str"=> "++pr_ipats ipats++str" on "++
        pr_constr (without_ctx pf_concl gl)));
      let gl = let gl,ctx = pull_ctx gl in push_ctx {ctx with speed=`Slow} gl in
      ipatstac ?ist ipats gl
    else
      List.nth after (nth - 1 - n_before - n_ks) gl

  and tclIORPAT ?ist tac = function
  | [[]] -> tac
  | orp -> tclTHENS_nonstrict tac (List.map (ipatstac ?ist) orp) "intro pattern"

  and ipatstac ?ist ipats gl =
    let rec aux ipats gl =
      match ipats with
      | [] -> tac_ctx tclIDTAC gl
      | p :: ps ->
          let next = ref ps in
          let gl = ipattac ?ist ~next p gl in
          tac_on_all gl (aux !next)
    in
      aux ipats gl
  in

  let rec split_itacs ?ist ~ind tac' = function
    | (IpatSimpl _ as spat) :: ipats' -> (* FIXME block *)
        let tac = ipattac ?ist ~next:(ref ipats') spat in
        split_itacs ?ist ~ind (tclTHEN_a tac' tac) ipats'
    | IpatCase (`Regular iorpat) :: ipats' -> 
        tclIORPAT ?ist tac' iorpat, ipats'
    | IpatCase (`Block(before,id_side,after)) :: ipats' ->
        tclTHEN_i_max tac'
          (block_intro ?ist ~ind id_side
            (List.map (ipatstac ?ist) before)
            (List.map (ipatstac ?ist)  after)),
        ipats'
    | ipats' -> tac', ipats' in

  let combine_tacs tac eqtac ipats ?ist ~ind gl =
    let tac1, ipats' = split_itacs ?ist ~ind tac ipats in
    let tac2 = ipatstac ?ist ipats' in
    tclTHENLIST_a [ tac1; eqtac; tac2 ] gl in
 
  (* Exported code *) 
  let introstac ?ist ipats gl =
    with_fresh_ctx (tclTHENLIST_a [
      ipatstac ?ist ipats;
      gen_tmp_ids ?ist;
      clear_wilds_and_tmp_and_delayed_ids
    ]) gl in
  
  let tclEQINTROS ?(ind=ref None) ?ist tac eqtac ipats gl =
    with_fresh_ctx (tclTHENLIST_a [
      combine_tacs (tac_ctx tac) (tac_ctx eqtac) ipats ?ist ~ind;
      gen_tmp_ids ?ist;
      clear_wilds_and_tmp_and_delayed_ids;
    ]) gl in

  let tclEQINTROSviewtac ~ist ~next tac eqtac gl =
    let tac1, ipats' = (* TODO: pass ind via lets in concl *)
      split_itacs ~ist ~ind:(ref None) tac !next in
    next := ipats';
    tclTHENLIST_a [ tac1; eqtac ] gl in (* FIXME *)

  introstac, tclEQINTROS, tclEQINTROSviewtac
;;

let () = tclEQINTROSviewtac_ref := tclEQINTROSviewtac

let rec eqmoveipats eqpat = function
  | (IpatSimpl _ as ipat) :: ipats -> ipat :: eqmoveipats eqpat ipats
  | (IpatAll :: _ | []) as ipats -> IpatAnon :: eqpat :: ipats
   | ipat :: ipats -> ipat :: eqpat :: ipats

(* General case *)
let tclINTROS ist t ip = tclEQINTROS ~ist (t ist) tclIDTAC ip

(** The "=>" tactical *)

let ssrintros_sep =
  let atom_sep = function
    | TacSplit (_, [NoBindings]) -> mt
    (* | TacExtend (_, "ssrapply", []) -> mt *)
    | _ -> spc in
  function
    | TacId [] -> mt
    | TacArg (_, Tacexp _) -> mt
    | TacArg (_, Reference _) -> mt
    | TacAtom (_, atom) -> atom_sep atom
    | _ -> spc

let pr_ssrintrosarg _ _ prt (tac, ipats) =
  prt tacltop tac ++ pr_intros (ssrintros_sep tac) ipats

ARGUMENT EXTEND ssrintrosarg TYPED AS tactic * ssrintros
   PRINTED BY pr_ssrintrosarg
| [ "YouShouldNotTypeThis" ssrtacarg(arg) ssrintros_ne(ipats) ] -> [ arg, ipats ]
END

TACTIC EXTEND ssrtclintros
| [ "YouShouldNotTypeThis" ssrintrosarg(arg) ] ->
  [ let tac, intros = arg in
    Proofview.V82.tactic (tclINTROS ist (fun ist -> ssrevaltac ist tac) intros) ]
END
set_pr_ssrtac "tclintros" 0 [ArgSsr "introsarg"]

let tclintros_expr loc tac ipats =
  let args = [in_gen (rawwit wit_ssrintrosarg) (tac, ipats)] in
  ssrtac_expr loc "tclintros" args

GEXTEND Gram
  GLOBAL: tactic_expr;
  tactic_expr: LEVEL "1" [ RIGHTA
    [ tac = tactic_expr; intros = ssrintros_ne -> tclintros_expr !@loc tac intros
    ] ];
END
(* }}} *)

(** Multipliers {{{ ***********************************************************)

(* tactical *)

let tclID tac = tac

let tclDOTRY n tac =
  if n <= 0 then tclIDTAC else
  let rec loop i gl =
    if i = n then tclTRY tac gl else
    tclTRY (tclTHEN tac (loop (i + 1))) gl in
  loop 1

let tclDO n tac =
  let prefix i = str"At iteration " ++ int i ++ str": " in
  let tac_err_at i gl =
    try tac gl
    with 
    | Errors.UserError (l, s) as e ->
        let _, info = Errors.push e in
        let e' = Errors.UserError (l, prefix i ++ s) in
        Util.iraise (e', info)
    | Compat.Exc_located(loc, Errors.UserError (l, s))  -> 
        raise (Compat.Exc_located(loc, Errors.UserError (l, prefix i ++ s))) in
  let rec loop i gl =
    if i = n then tac_err_at i gl else
    (tclTHEN (tac_err_at i) (loop (i + 1))) gl in
  loop 1

let tclMULT = function
  | 0, May  -> tclREPEAT
  | 1, May  -> tclTRY
  | n, May  -> tclDOTRY n
  | 0, Must -> tclAT_LEAST_ONCE
  | n, Must when n > 1 -> tclDO n
  | _       -> tclID

(** The "do" tactical. ********************************************************)

(*
type ssrdoarg = ((ssrindex * ssrmmod) * ssrhint) * ssrclauses
*)

let pr_ssrdoarg prc _ prt (((n, m), tac), clauses) =
  pr_index n ++ pr_mmod m ++ pr_hintarg prt tac ++ pr_clauses clauses

ARGUMENT EXTEND ssrdoarg
  TYPED AS ((ssrindex * ssrmmod) * ssrhintarg) * ssrclauses
  PRINTED BY pr_ssrdoarg
| [ "YouShouldNotTypeThis" ] -> [ anomaly "Grammar placeholder match" ]
END

let ssrdotac ist (((n, m), tac), clauses) =
  let mul = get_index n, m in
  tclCLAUSES ist (tclMULT mul (hinttac ist false tac)) clauses

TACTIC EXTEND ssrtcldo
| [ "YouShouldNotTypeThis" "do" ssrdoarg(arg) ] -> [ Proofview.V82.tactic (ssrdotac ist arg) ]
END
set_pr_ssrtac "tcldo" 3 [ArgSep "do "; ArgSsr "doarg"]

let ssrdotac_expr loc n m tac clauses =
  let arg = ((n, m), tac), clauses in
  ssrtac_expr loc "tcldo" [in_gen (rawwit wit_ssrdoarg) arg]

GEXTEND Gram
  GLOBAL: tactic_expr;
  ssrdotac: [
    [ tac = tactic_expr LEVEL "3" -> mk_hint tac
    | tacs = ssrortacarg -> tacs
  ] ];
  tactic_expr: LEVEL "3" [ RIGHTA
    [ IDENT "do"; m = ssrmmod; tac = ssrdotac; clauses = ssrclauses ->
      ssrdotac_expr !@loc noindex m tac clauses
    | IDENT "do"; tac = ssrortacarg; clauses = ssrclauses ->
      ssrdotac_expr !@loc noindex Once tac clauses
    | IDENT "do"; n = int_or_var; m = ssrmmod;
                  tac = ssrdotac; clauses = ssrclauses ->
      ssrdotac_expr !@loc (mk_index !@loc n) m tac clauses
    ] ];
END
(* }}} *)

(** The "first" and "last" tacticals. {{{ *************************************)

(* type ssrseqarg = ssrindex * (ssrtacarg * ssrtac option) *)

let pr_seqtacarg prt = function
  | (is_first, []), _ -> str (if is_first then "first" else "last")
  | tac, Some dtac ->
    hv 0 (pr_hintarg prt tac ++ spc() ++ str "|| " ++ prt tacltop dtac)
  | tac, _ -> pr_hintarg prt tac

let pr_ssrseqarg _ _ prt = function
  | ArgArg 0, tac -> pr_seqtacarg prt tac
  | i, tac -> pr_index i ++ str " " ++ pr_seqtacarg prt tac

(* We must parse the index separately to resolve the conflict with *)
(* an unindexed tactic.                                            *)
ARGUMENT EXTEND ssrseqarg TYPED AS ssrindex * (ssrhintarg * tactic option)
                          PRINTED BY pr_ssrseqarg
| [ "YouShouldNotTypeThis" ] -> [ anomaly "Grammar placeholder match" ]
END

let sq_brace_tacnames =
   ["first"; "solve"; "do"; "rewrite"; "have"; "suffices"; "wlog"]
   (* "by" is a keyword *)
let accept_ssrseqvar strm =
  match Compat.get_tok (stream_nth 0 strm) with
  | Tok.IDENT id when not (List.mem id sq_brace_tacnames) ->
     accept_before_syms_or_ids ["["] ["first";"last"] strm
  | _ -> raise Stream.Failure

let test_ssrseqvar = Gram.Entry.of_parser "test_ssrseqvar" accept_ssrseqvar

let swaptacarg (loc, b) = (b, []), Some (TacId [])

let check_seqtacarg dir arg = match snd arg, dir with
  | ((true, []), Some (TacAtom (loc, _))), L2R ->
    loc_error loc "expected \"last\""
  | ((false, []), Some (TacAtom (loc, _))), R2L ->
    loc_error loc "expected \"first\""
  | _, _ -> arg

let ssrorelse = Gram.entry_create "ssrorelse"
GEXTEND Gram
  GLOBAL: ssrorelse ssrseqarg;
  ssrseqidx: [
    [ test_ssrseqvar; id = Prim.ident -> ArgVar (!@loc, id)
    | n = Prim.natural -> ArgArg (check_index !@loc n)
    ] ];
  ssrswap: [[ IDENT "first" -> !@loc, true | IDENT "last" -> !@loc, false ]];
  ssrorelse: [[ "||"; tac = tactic_expr LEVEL "2" -> tac ]];
  ssrseqarg: [
    [ arg = ssrswap -> noindex, swaptacarg arg
    | i = ssrseqidx; tac = ssrortacarg; def = OPT ssrorelse -> i, (tac, def)
    | i = ssrseqidx; arg = ssrswap -> i, swaptacarg arg
    | tac = tactic_expr LEVEL "3" -> noindex, (mk_hint tac, None)
    ] ];
END

let tclPERM perm tac gls =
  let subgls = tac gls in
  let sigma, subgll = Refiner.unpackage subgls in
  let subgll' = perm subgll in
  Refiner.repackage sigma subgll'
(*
let tclPERM perm tac gls =
  let mkpft n g r =
    {Proof_type.open_subgoals = n; Proof_type.goal = g; Proof_type.ref = r} in
  let mkleaf g = mkpft 0 g None in
  let mkprpft n g pr a = mkpft n g (Some (Proof_type.Prim pr, a)) in
  let mkrpft n g c = mkprpft n g (Proof_type.Refine c) in
  let mkipft n g =
    let mki pft (id, _, _ as d) =
      let g' = {g with evar_concl = mkNamedProd_or_LetIn d g.evar_concl} in
      mkprpft n g' (Proof_type.Intro id) [pft] in
    List.fold_left mki in
  let gl = Refiner.sig_it gls in
  let mkhyp subgl =
    let rec chop_section = function
    | (x, _, _ as d) :: e when not_section_id x -> d :: chop_section e
    | _ -> [] in
    let lhyps = Environ.named_context_of_val subgl.evar_hyps in
    mk_perm_id (), subgl, chop_section lhyps in
  let mkpfvar (hyp, subgl, lhyps) =
    let mkarg args (lhyp, body, _) =
      if body = None then mkVar lhyp :: args else args in
    mkrpft 0 subgl (applist (mkVar hyp, List.fold_left mkarg [] lhyps)) [] in
  let mkpfleaf (_, subgl, lhyps) = mkipft 1 gl (mkleaf subgl) lhyps in
  let mkmeta _ = Evarutil.mk_new_meta () in
  let mkhypdecl (hyp, subgl, lhyps) =
    hyp, None, it_mkNamedProd_or_LetIn subgl.evar_concl lhyps in
  let subgls, v as res0 = tac gls in
  let sigma, subgll = Refiner.unpackage subgls in
  let n = List.length subgll in if n = 0 then res0 else
  let hyps = List.map mkhyp subgll in
  let hyp_decls = List.map mkhypdecl (List.rev (perm hyps)) in
  let c = applist (mkmeta (), List.map mkmeta subgll) in
  let pft0 = mkipft 0 gl (v (List.map mkpfvar hyps)) hyp_decls in
  let pft1 = mkrpft n gl c (pft0 :: List.map mkpfleaf (perm hyps)) in
  let subgll', v' = Refiner.frontier pft1 in
  Refiner.repackage sigma subgll', v'
*)

let tclREV tac gl = tclPERM List.rev tac gl

let rot_hyps dir i hyps =
  let n = List.length hyps in
  if i = 0 then List.rev hyps else
  if i > n then Errors.error "Not enough subgoals" else
  let rec rot i l_hyps = function
    | hyp :: hyps' when i > 0 -> rot (i - 1) (hyp :: l_hyps) hyps'
    | hyps' -> hyps' @ (List.rev l_hyps) in
  rot (match dir with L2R -> i | R2L -> n - i) [] hyps

let tclSEQAT ist atac1 dir (ivar, ((_, atacs2), atac3)) =
  let i = get_index ivar in
  let evtac = ssrevaltac ist in
  let tac1 = evtac atac1 in
  if atacs2 = [] && atac3 <> None then tclPERM (rot_hyps dir i) tac1  else
  let evotac = function Some atac -> evtac atac | _ -> tclIDTAC in
  let tac3 = evotac atac3 in
  let rec mk_pad n = if n > 0 then tac3 :: mk_pad (n - 1) else [] in
  match dir, mk_pad (i - 1), List.map evotac atacs2 with
  | L2R, [], [tac2] when atac3 = None -> tclTHENFIRST tac1 tac2
  | L2R, [], [tac2] when atac3 = None -> tclTHENLAST tac1 tac2
  | L2R, pad, tacs2 -> tclTHENSFIRSTn tac1 (Array.of_list (pad @ tacs2)) tac3
  | R2L, pad, tacs2 -> tclTHENSLASTn tac1 tac3 (Array.of_list (tacs2 @ pad))

(* We can't actually parse the direction separately because this   *)
(* would introduce conflicts with the basic ltac syntax.           *)
let pr_ssrseqdir _ _ _ = function
  | L2R -> str ";" ++ spc () ++ str "first "
  | R2L -> str ";" ++ spc () ++ str "last "

ARGUMENT EXTEND ssrseqdir TYPED AS ssrdir PRINTED BY pr_ssrseqdir
| [ "YouShouldNotTypeThis" ] -> [ anomaly "Grammar placeholder match" ]
END

TACTIC EXTEND ssrtclseq
| [ "YouShouldNotTypeThis" ssrtclarg(tac) ssrseqdir(dir) ssrseqarg(arg) ] ->
  [ Proofview.V82.tactic (tclSEQAT ist tac dir arg) ]
END
set_pr_ssrtac "tclseq" 5 [ArgSsr "tclarg"; ArgSsr "seqdir"; ArgSsr "seqarg"]

let tclseq_expr loc tac dir arg =
  let arg1 = in_gen (rawwit wit_ssrtclarg) tac in
  let arg2 = in_gen (rawwit wit_ssrseqdir) dir in
  let arg3 = in_gen (rawwit wit_ssrseqarg) (check_seqtacarg dir arg) in
  ssrtac_expr loc "tclseq" [arg1; arg2; arg3]

GEXTEND Gram
  GLOBAL: tactic_expr;
  ssr_first: [
    [ tac = ssr_first; ipats = ssrintros_ne -> tclintros_expr !@loc tac ipats
    | "["; tacl = LIST0 tactic_expr SEP "|"; "]" -> TacFirst tacl
    ] ];
  ssr_first_else: [
    [ tac1 = ssr_first; tac2 = ssrorelse -> TacOrelse (tac1, tac2)
    | tac = ssr_first -> tac ]];
  tactic_expr: LEVEL "4" [ LEFTA
    [ tac1 = tactic_expr; ";"; IDENT "first"; tac2 = ssr_first_else ->
      TacThen (tac1, tac2)
    | tac = tactic_expr; ";"; IDENT "first"; arg = ssrseqarg ->
      tclseq_expr !@loc tac L2R arg
    | tac = tactic_expr; ";"; IDENT "last"; arg = ssrseqarg ->
      tclseq_expr !@loc tac R2L arg
    ] ];
END
(* }}} *)

(** 5. Bookkeeping tactics (clear, move, case, elim) *)

(* post-interpretation of terms *)
let all_ok _ _ = true

let pf_abs_ssrterm ?(resolve_typeclasses=false) ist gl t =
  let sigma, ct as t = interp_term ist gl t in
  let sigma, _ as t =
    let env = pf_env gl in
    if not resolve_typeclasses then t
    else
       let sigma = Typeclasses.resolve_typeclasses ~fail:false env sigma in
       sigma, Evarutil.nf_evar sigma ct in
  let n, c, abstracted_away, ucst = pf_abs_evars gl t in
  List.fold_left Evd.remove sigma abstracted_away, pf_abs_cterm gl n c, ucst, n

let pf_interp_ty ?(resolve_typeclasses=false) ist gl ty =
   let n_binders = ref 0 in
   let ty = match ty with
   | a, (t, None) ->
     let rec force_type = function
     | GProd (l, x, k, s, t) -> incr n_binders; GProd (l, x, k, s, force_type t)
     | GLetIn (l, x, v, t) -> incr n_binders; GLetIn (l, x, v, force_type t)
     | ty -> mkRCast ty mkRType in
     a, (force_type t, None)
   | _, (_, Some ty) ->
     let rec force_type = function
     | CProdN (l, abs, t) ->
       n_binders := !n_binders +  List.length (List.flatten (List.map pi1 abs));
       CProdN (l, abs, force_type t)
     | CLetIn (l, n, v, t) -> incr n_binders; CLetIn (l, n, v, force_type t)
     | ty -> mkCCast dummy_loc ty (mkCType dummy_loc) in
     mk_term NoFlag (force_type ty) in
   let strip_cast (sigma, t) =
     let rec aux t = match kind_of_type t with
     | CastType (t, ty) when !n_binders = 0 && isSort ty -> t
     | ProdType(n,s,t) -> decr n_binders; mkProd (n, s, aux t)
     | LetInType(n,v,ty,t) -> decr n_binders; mkLetIn (n, v, ty, aux t)
     | _ -> anomaly "pf_interp_ty: ssr Type cast deleted by typecheck" in
     sigma, aux t in
   let sigma, cty as ty = strip_cast (interp_term ist gl ty) in
   let ty =
     let env = pf_env gl in
     if not resolve_typeclasses then ty
     else
       let sigma = Typeclasses.resolve_typeclasses ~fail:false env sigma in
       sigma, Evarutil.nf_evar sigma cty in
   let n, c, _, ucst = pf_abs_evars gl ty in
   let lam_c = pf_abs_cterm gl n c in
   let ctx, c = decompose_lam_n n lam_c in
   n, compose_prod ctx c, lam_c, ucst
;;

let whd_app f args = Reductionops.whd_betaiota Evd.empty (mkApp (f, args))

let pr_cargs a =
  str "[" ++ pr_list pr_spc pr_constr (Array.to_list a) ++ str "]"

let pp_term gl t =
  let t = Reductionops.nf_evar (project gl) t in pr_constr t
let pp_concat hd ?(sep=str", ") = function [] -> hd | x :: xs ->
  hd ++ List.fold_left (fun acc x -> acc ++ sep ++ x) x xs

let fake_pmatcher_end () =
  mkProp, L2R, (Evd.empty, Evd.empty_evar_universe_context, mkProp)

(* TASSI: given (c : ty), generates (c ??? : ty[???/...]) with m evars *)
exception NotEnoughProducts
let prof_saturate_whd = mk_profiler "saturate.whd";;
let saturate ?(beta=false) ?(bi_types=false) env sigma c ?(ty=Retyping.get_type_of env sigma c) m 
=
  let rec loop ty args sigma n = 
  if n = 0 then 
    let args = List.rev args in
     (if beta then Reductionops.whd_beta sigma else fun x -> x)
      (mkApp (c, Array.of_list (List.map snd args))), ty, args, sigma 
  else match kind_of_type ty with
  | ProdType (_, src, tgt) ->
      let sigma = create_evar_defs sigma in
      let sigma = Sigma.Unsafe.of_evar_map sigma in
      let Sigma (x, sigma, _) =
        Evarutil.new_evar env sigma
          (if bi_types then Reductionops.nf_betaiota (Sigma.to_evar_map sigma) src else src) in
      let sigma = Sigma.to_evar_map sigma in
      loop (subst1 x tgt) ((m - n,x) :: args) sigma (n-1)
  | CastType (t, _) -> loop t args sigma n 
  | LetInType (_, v, _, t) -> loop (subst1 v t) args sigma n
  | SortType _ -> assert false
  | AtomicType _ ->
      let ty = 
        prof_saturate_whd.profile      
        (Reductionops.whd_betadeltaiota env sigma) ty in
      match kind_of_type ty with
      | ProdType _ -> loop ty args sigma n
      | _ -> raise NotEnoughProducts
  in
   loop ty [] sigma m

let pf_saturate ?beta ?bi_types gl c ?ty m = 
  let env, sigma, si = pf_env gl, project gl, sig_it gl in
  let t, ty, args, sigma = saturate ?beta ?bi_types env sigma c ?ty m in
  t, ty, args, re_sig si sigma 

(** Rewrite redex switch *)

(** Generalization (discharge) item *)

(* An item is a switch + term pair.                                     *)

(* type ssrgen = ssrdocc * ssrterm *)

let pr_gen (docc, dt) = pr_docc docc ++ pr_cpattern dt

let pr_ssrgen _ _ _ = pr_gen

ARGUMENT EXTEND ssrgen TYPED AS ssrdocc * cpattern PRINTED BY pr_ssrgen
| [ ssrdocc(docc) cpattern(dt) ] -> [ docc, dt ]
| [ cpattern(dt) ] -> [ nodocc, dt ]
END

let has_occ ((_, occ), _) = occ <> None
let hyp_of_var v =  SsrHyp (dummy_loc, destVar v)

let interp_clr = function
| Some clr, (k, c) 
  when (k = NoFlag  || k = WithAt) && is_pf_var c -> hyp_of_var c :: clr 
| Some clr, _ -> clr
| None, _ -> []

(* XXX the k of the redex should percolate out *)
let pf_interp_gen_aux ist gl to_ind ((oclr, occ), t) =
  let pat = interp_cpattern ist gl t None in (* UGLY API *)
  let cl, env, sigma = pf_concl gl, pf_env gl, project gl in
  let (c, ucst), cl = 
    try fill_occ_pattern ~raise_NoMatch:true env sigma cl pat occ 1
    with NoMatch -> redex_of_pattern env pat, cl in
  let clr = interp_clr (oclr, (tag_of_cpattern t, c)) in
  if not(occur_existential c) then
    if tag_of_cpattern t = WithAt then 
      if not (isVar c) then
	errorstrm (str "@ can be used with variables only")
      else match pf_get_hyp gl (destVar c) with
      | _, None, _ -> errorstrm (str "@ can be used with let-ins only")
      | name, Some bo, ty -> true, pat, mkLetIn (Name name,bo,ty,cl),c,clr,ucst,gl
    else let gl, ccl =  pf_mkprod gl c cl in false, pat, ccl, c, clr,ucst,gl
  else if to_ind && occ = None then
    let nv, p, _, ucst' = pf_abs_evars gl (fst pat, c) in
    let ucst = Evd.union_evar_universe_context ucst ucst' in
    if nv = 0 then anomaly "occur_existential but no evars" else
    let gl, pty = pf_type_of gl p in
    false, pat, mkProd (constr_name c, pty, pf_concl gl), p, clr,ucst,gl
  else loc_error (loc_of_cpattern t) "generalized term didn't match"

let genclrtac cl cs clr =
  let tclmyORELSE tac1 tac2 gl =
    try tac1 gl
    with e when Errors.noncritical e -> tac2 e gl in
  (* apply_type may give a type error, but the useful message is
   * the one of clear.  You type "move: x" and you get
   * "x is used in hyp H" instead of
   * "The term H has type T x but is expected to have type T x0". *)
  tclTHEN
    (tclmyORELSE
      (apply_type cl cs)
      (fun type_err gl ->
         tclTHEN
           (tclTHEN (Proofview.V82.of_tactic (elim_type (build_coq_False ()))) (cleartac clr))
           (fun gl -> raise type_err)
           gl))
    (cleartac clr)

let gentac ist gen gl =
(*   pp(lazy(str"sigma@gentac=" ++ pr_evar_map None (project gl))); *)
  let conv, _, cl, c, clr, ucst,gl = pf_interp_gen_aux ist gl false gen in
  pp(lazy(str"c@gentac=" ++ pr_constr c));
  let gl = pf_merge_uc ucst gl in
  if conv
  then tclTHEN (Proofview.V82.of_tactic (convert_concl cl)) (cleartac clr) gl
  else genclrtac cl [c] clr gl

let () = gentac_ref := gentac

let pf_interp_gen ist gl to_ind gen =
  let _, _, a, b, c, ucst,gl = pf_interp_gen_aux ist gl to_ind gen in
  a, b ,c, pf_merge_uc ucst gl

(** Generalization (discharge) sequence *)

(* A discharge sequence is represented as a list of up to two   *)
(* lists of d-items, plus an ident list set (the possibly empty *)
(* final clear switch). The main list is empty iff the command  *)
(* is defective, and has length two if there is a sequence of   *)
(* dependent terms (and in that case it is the first of the two *)
(* lists). Thus, the first of the two lists is never empty.     *)

(* type ssrgens = ssrgen list *)
(* type ssrdgens = ssrgens list * ssrclear *)

let gens_sep = function [], [] -> mt | _ -> spc

let pr_dgens pr_gen (gensl, clr) =
  let prgens s gens = str s ++ pr_list spc pr_gen gens in
  let prdeps deps = prgens ": " deps ++ spc () ++ str "/" in
  match gensl with
  | [deps; []] -> prdeps deps ++ pr_clear pr_spc clr
  | [deps; gens] -> prdeps deps ++ prgens " " gens ++ pr_clear spc clr
  | [gens] -> prgens ": " gens ++ pr_clear spc clr
  | _ -> pr_clear pr_spc clr

let pr_ssrdgens _ _ _ = pr_dgens pr_gen

let cons_gen gen = function
  | gens :: gensl, clr -> (gen :: gens) :: gensl, clr
  | _ -> anomaly "missing gen list"

let cons_dep (gensl, clr) =
  if List.length gensl = 1 then ([] :: gensl, clr) else
  Errors.error "multiple dependents switches '/'"

ARGUMENT EXTEND ssrdgens_tl TYPED AS ssrgen list list * ssrclear
                            PRINTED BY pr_ssrdgens
| [ "{" ne_ssrhyp_list(clr) "}" cpattern(dt) ssrdgens_tl(dgens) ] ->
  [ cons_gen (mkclr clr, dt) dgens ]
| [ "{" ne_ssrhyp_list(clr) "}" ] ->
  [ [[]], clr ]
| [ "{" ssrocc(occ) "}" cpattern(dt) ssrdgens_tl(dgens) ] ->
  [ cons_gen (mkocc occ, dt) dgens ]
| [ "/" ssrdgens_tl(dgens) ] ->
  [ cons_dep dgens ]
| [ cpattern(dt) ssrdgens_tl(dgens) ] ->
  [ cons_gen (nodocc, dt) dgens ]
| [ ] ->
  [ [[]], [] ]
END

ARGUMENT EXTEND ssrdgens TYPED AS ssrdgens_tl PRINTED BY pr_ssrdgens
| [ ":" ssrgen(gen) ssrdgens_tl(dgens) ] -> [ cons_gen gen dgens ]
END

let genstac (gens, clr) ist =
  tclTHENLIST (cleartac clr :: List.rev_map (gentac ist) gens)

(* Common code to handle generalization lists along with the defective case *)

let with_defective maintac deps clr ist gl =
  let top_id =
    match kind_of_type (pf_concl gl) with
    | ProdType (Name id, _, _)
      when has_discharged_tag (string_of_id id) -> id
    | _ -> top_id in
  let top_gen = mkclr clr, cpattern_of_id top_id in
  tclTHEN (introid top_id) (maintac deps top_gen ist) gl

let with_defective_a maintac deps clr ist gl =
  let top_id =
    match kind_of_type (without_ctx pf_concl gl) with
    | ProdType (Name id, _, _)
      when has_discharged_tag (string_of_id id) -> id
    | _ -> top_id in
  let top_gen = mkclr clr, cpattern_of_id top_id in
  tclTHEN_a (tac_ctx (introid top_id)) (maintac deps top_gen ist) gl

let with_dgens (gensl, clr) maintac ist = match gensl with
  | [deps; []] -> with_defective maintac deps clr ist
  | [deps; gen :: gens] ->
    tclTHEN (genstac (gens, clr) ist) (maintac deps gen ist)
  | [gen :: gens] -> tclTHEN (genstac (gens, clr) ist) (maintac [] gen ist)
  | _ -> with_defective maintac [] clr ist

let first_goal gls =
  let gl = gls.Evd.it and sig_0 = gls.Evd.sigma in
  if List.is_empty gl then Errors.error "first_goal";
  { Evd.it = List.hd gl; Evd.sigma = sig_0; }

let with_deps deps0 maintac cl0 cs0 clr0 ist gl0 =
  let rec loop gl cl cs clr args clrs = function
  | [] ->
    let n = List.length args in
    maintac (if n > 0 then applist (to_lambda n cl, args) else cl) clrs ist gl0
  | dep :: deps ->
    let gl' = first_goal (genclrtac cl cs clr gl) in
    let cl', c', clr',gl' = pf_interp_gen ist gl' false dep in
    loop gl' cl' [c'] clr' (c' :: args) (clr' :: clrs) deps in
  loop gl0 cl0 cs0 clr0 cs0 [clr0] (List.rev deps0)

(** Equations *)

(* argument *)

type ssreqid = ssripat option

let pr_eqid = function Some pat -> str " " ++ pr_ipat pat | None -> mt ()
let pr_ssreqid _ _ _ = pr_eqid

(* We must use primitive parsing here to avoid conflicts with the  *)
(* basic move, case, and elim tactics.                             *)
ARGUMENT EXTEND ssreqid TYPED AS ssripatrep option PRINTED BY pr_ssreqid
| [ "YouShouldNotTypeThis" ] -> [ anomaly "Grammar placeholder match" ]
END

let accept_ssreqid strm =
  match Compat.get_tok (Util.stream_nth 0 strm) with
  | Tok.IDENT _ -> accept_before_syms [":"] strm
  | Tok.KEYWORD ":" -> ()
  | Tok.KEYWORD pat when List.mem pat ["_"; "?"; "->"; "<-"] ->
                      accept_before_syms [":"] strm
  | _ -> raise Stream.Failure

let test_ssreqid = Gram.Entry.of_parser "test_ssreqid" accept_ssreqid

GEXTEND Gram
  GLOBAL: ssreqid;
  ssreqpat: [
    [ id = Prim.ident -> IpatId id
    | "_" -> IpatWild
    | "?" -> IpatAnon
    | occ = ssrdocc; "->" -> (match occ with
      | None, occ -> IpatRw (occ, L2R)
      | _ -> loc_error !@loc "Only occurrences are allowed here")
    | occ = ssrdocc; "<-" -> (match occ with
      | None, occ ->  IpatRw (occ, R2L)
      | _ -> loc_error !@loc "Only occurrences are allowed here")
    | "->" -> IpatRw (allocc, L2R)
    | "<-" -> IpatRw (allocc, R2L)
    ]];
  ssreqid: [
    [ test_ssreqid; pat = ssreqpat -> Some pat
    | test_ssreqid -> None
    ]];
END

(* creation *)

let mkEq dir cl c t n gl =
  let eqargs = [|t; c; c|] in eqargs.(dir_org dir) <- mkRel n;
  let eq, gl = pf_fresh_global (build_coq_eq()) gl in 
  let refl, gl = mkRefl t c gl in
  mkArrow (mkApp (eq, eqargs)) (lift 1 cl), refl, gl

let pushmoveeqtac cl c gl =
  let x, t, cl1 = destProd cl in
  let cl2, eqc, gl = mkEq R2L cl1 c t 1 gl in
  apply_type (mkProd (x, t, cl2)) [c; eqc] gl

let pushcaseeqtac cl gl =
  let cl1, args = destApplication cl in
  let n = Array.length args in
  let dc, cl2 = decompose_lam_n n cl1 in
  let _, t = List.nth dc (n - 1) in
  let cl3, eqc, gl = mkEq R2L cl2 args.(0) t n gl in
  let gl, clty = pf_type_of gl cl in
  let prot, gl = mkProt clty cl3 gl in
  let cl4 = mkApp (compose_lam dc prot, args) in
  let gl, _ = pf_e_type_of gl cl4 in
  tclTHEN (apply_type cl4 [eqc])
    (Proofview.V82.of_tactic (convert_concl cl4)) gl

let pushelimeqtac gl =
  let _, args = destApplication (pf_concl gl) in
  let x, t, _ = destLambda args.(1) in
  let cl1 = mkApp (args.(1), Array.sub args 2 (Array.length args - 2)) in
  let cl2, eqc, gl = mkEq L2R cl1 args.(2) t 1 gl in
  tclTHEN (apply_type (mkProd (x, t, cl2)) [args.(2); eqc])
    (Proofview.V82.of_tactic intro) gl

(** Bookkeeping (discharge-intro) argument *)

(* Since all bookkeeping ssr commands have the same discharge-intro    *)
(* argument format we use a single grammar entry point to parse them.  *)
(* the entry point parses only non-empty arguments to avoid conflicts  *)
(* with the basic Coq tactics.                                         *)

(* type ssrarg = ssrview * (ssreqid * (ssrdgens * ssripats)) *)

let pr_ssrarg _ _ _ (view, (eqid, (dgens, ipats))) =
  let pri = pr_intros (gens_sep dgens) in
  pr_view view ++ pr_eqid eqid ++ pr_dgens pr_gen dgens ++ pri ipats

ARGUMENT EXTEND ssrarg TYPED AS ssrview * (ssreqid * (ssrdgens * ssrintros))
   PRINTED BY pr_ssrarg
| [ ssrview(view) ssreqid(eqid) ssrdgens(dgens) ssrintros(ipats) ] ->
  [ view, (eqid, (dgens, ipats)) ]
| [ ssrview(view) ssrclear(clr) ssrintros(ipats) ] ->
  [ view, (None, (([], clr), ipats)) ]
| [ ssreqid(eqid) ssrdgens(dgens) ssrintros(ipats) ] ->
  [ [], (eqid, (dgens, ipats)) ]
| [ ssrclear_ne(clr) ssrintros(ipats) ] ->
  [ [], (None, (([], clr), ipats)) ]
| [ ssrintros_ne(ipats) ] ->
  [ [], (None, (([], []), ipats)) ]
END

(** The "clear" tactic *)

(* We just add a numeric version that clears the n top assumptions. *)

let poptac ist n = introstac ~ist (List.init n (fun _ -> IpatWild))

TACTIC EXTEND ssrclear
  | [ "clear" natural(n) ] -> [ Proofview.V82.tactic (poptac ist n) ]
END

(** The "move" tactic *)

let rec improper_intros = function
  | IpatSimpl _ :: ipats -> improper_intros ipats
  | (IpatId _ | IpatAnon | IpatCase _ | IpatAll) :: _ -> false
  | _ -> true

let check_movearg = function
  | view, (eqid, _) when view <> [] && eqid <> None ->
    Errors.error "incompatible view and equation in move tactic"
  | view, (_, (([gen :: _], _), _)) when view <> [] && has_occ gen ->
    Errors.error "incompatible view and occurrence switch in move tactic"
  | _, (_, ((dgens, _), _)) when List.length dgens > 1 ->
    Errors.error "dependents switch `/' in move tactic"
  | _, (eqid, (_, ipats)) when eqid <> None && improper_intros ipats ->
    Errors.error "no proper intro pattern for equation in move tactic"
  | arg -> arg

ARGUMENT EXTEND ssrmovearg TYPED AS ssrarg PRINTED BY pr_ssrarg
| [ ssrarg(arg) ] -> [ check_movearg arg ]
END

let viewmovetac_aux ?(next=ref []) clear name_ref (_, vl as v) _ gen ist gl =
  let cl, c, clr, gl, gen_pat =
    let gl, ctx = pull_ctx gl in
    let _, gen_pat, a, b, c, ucst, gl = pf_interp_gen_aux ist gl false gen in
    a, b ,c, push_ctx ctx (pf_merge_uc ucst gl), gen_pat in
  let clr = if clear then clr else [] in
  name_ref := (match id_of_pattern gen_pat with Some id -> id | _ -> top_id);
  let clr = if clear then clr else [] in
  if vl = [] then tac_ctx (genclrtac cl [c] clr) gl
  else
    let _, _, gl =
      pfa_with_view ist ~next v cl c
        (fun cl c -> tac_ctx (genclrtac cl [c] clr)) clr gl in
      gl

let () = Hook.set Ssrcommon.move_top_with_view
  (fun ~next c r v -> with_defective_a (viewmovetac_aux ~next c r v) [] [])

let viewmovetac ?next v deps gen ist gl = 
 with_fresh_ctx
   (tclTHEN_a
     (viewmovetac_aux ?next true (ref top_id) v deps gen ist)
      clear_wilds_and_tmp_and_delayed_ids)
     gl

let eqmovetac _ gen ist gl =
  let cl, c, _, gl = pf_interp_gen ist gl false gen in pushmoveeqtac cl c gl

let movehnftac gl = match kind_of_term (pf_concl gl) with
  | Prod _ | LetIn _ -> tclIDTAC gl
  | _ -> hnf_in_concl gl

let ssrmovetac ist = function
  | _::_ as view, (_, (dgens, ipats)) ->
    let next = ref ipats in
    let dgentac = with_dgens dgens (viewmovetac ~next (true, view)) ist in
    tclTHEN dgentac (fun gl -> introstac ~ist !next gl)
  | _, (Some pat, (dgens, ipats)) ->
    let dgentac = with_dgens dgens eqmovetac ist in
    tclTHEN dgentac (introstac ~ist (eqmoveipats pat ipats))
  | _, (_, (([gens], clr), ipats)) ->
    let gentac = genstac (gens, clr) ist in
    tclTHEN gentac (introstac ~ist ipats)
  | _, (_, ((_, clr), ipats)) ->
    tclTHENLIST [movehnftac; cleartac clr; introstac ~ist ipats]

TACTIC EXTEND ssrmove
| [ "move" ssrmovearg(arg) ssrrpat(pat) ] ->
  [ Proofview.V82.tactic (tclTHEN (ssrmovetac ist arg) (introstac ~ist [pat])) ]
| [ "move" ssrmovearg(arg) ssrclauses(clauses) ] ->
  [ Proofview.V82.tactic (tclCLAUSES ist (ssrmovetac ist arg) clauses) ]
| [ "move" ssrrpat(pat) ] -> [ Proofview.V82.tactic (introstac ~ist [pat]) ]
| [ "move" ] -> [ Proofview.V82.tactic (movehnftac) ]
END

(* TASSI: given the type of an elimination principle, it finds the higher order
 * argument (index), it computes it's arity and the arity of the eliminator and
 * checks if the eliminator is recursive or not *)
let analyze_eliminator elimty env sigma =
  let rec loop ctx t = match kind_of_type t with
  | AtomicType (hd, args) when isRel hd -> 
    ctx, destRel hd, not (noccurn 1 t), Array.length args, t
  | CastType (t, _) -> loop ctx t
  | ProdType (x, ty, t) -> loop ((x,None,ty) :: ctx) t
  | LetInType (x,b,ty,t) -> loop ((x,Some b,ty) :: ctx) (subst1 b t)
  | _ ->
    let env' = Environ.push_rel_context ctx env in
    let t' = Reductionops.whd_betadeltaiota env' sigma t in
    if not (Term.eq_constr t t') then loop ctx t' else
      errorstrm (str"The eliminator has the wrong shape."++spc()++
      str"A (applied) bound variable was expected as the conclusion of "++
      str"the eliminator's"++Pp.cut()++str"type:"++spc()++pr_constr elimty) in
  let ctx, pred_id, elim_is_dep, n_pred_args, concl = loop [] elimty in
  let n_elim_args = rel_context_nhyps ctx in
  let is_rec_elim = 
     let count_occurn n term =
       let count = ref 0 in
       let rec occur_rec n c = match kind_of_term c with
         | Rel m -> if m = n then incr count
         | _ -> iter_constr_with_binders succ occur_rec n c
       in
       occur_rec n term; !count in
     let occurr2 n t = count_occurn n t > 1 in
     not (List.for_all_i 
       (fun i (_,rd) -> pred_id <= i || not (occurr2 (pred_id - i) rd))
       1 (assums_of_rel_context ctx))
  in
  n_elim_args - pred_id, n_elim_args, is_rec_elim, elim_is_dep, n_pred_args,
  (ctx,concl)
  
(* TASSI: This version of unprotects inlines the unfold tactic definition, 
 * since we don't want to wipe out let-ins, and it seems there is no flag
 * to change that behaviour in the standard unfold code *)
let unprotecttac gl =
  let c, gl = pf_mkSsrConst "protect_term" gl in
  let prot, _ = destConst c in
  onClause (fun idopt ->
    let hyploc = Option.map (fun id -> id, InHyp) idopt in
    reduct_option 
      (Reductionops.clos_norm_flags 
        (Closure.RedFlags.mkflags 
          [Closure.RedFlags.fBETA;
           Closure.RedFlags.fCONST prot;
           Closure.RedFlags.fIOTA]), DEFAULTcast) hyploc)
    allHypsAndConcl gl

let dependent_apply_error =
  try Errors.error "Could not fill dependent hole in \"apply\"" with err -> err

(* TASSI: Sometimes Coq's apply fails. According to my experience it may be
 * related to goals that are products and with beta redexes. In that case it
 * guesses the wrong number of implicit arguments for your lemma. What follows
 * is just like apply, but with a user-provided number n of implicits.
 *
 * Refine.refine function that handles type classes and evars but fails to
 * handle "dependently typed higher order evars". 
 *
 * Refiner.refiner that does not handle metas with a non ground type but works
 * with dependently typed higher order metas. *)
let applyn ~with_evars ?beta ?(with_shelve=false) n t gl =
  if with_evars then
    let refine gl =
      let t, ty, args, gl = pf_saturate ?beta ~bi_types:true gl t n in
(*       pp(lazy(str"sigma@saturate=" ++ pr_evar_map None (project gl))); *)
      let gl = pf_unify_HO gl ty (pf_concl gl) in
      let gs = CList.map_filter (fun (_, e) ->
        if isEvar (pf_nf_evar gl e) then Some e else None)
        args in
      pf_partial_solution gl t gs
    in
    Proofview.(V82.of_tactic
      (tclTHEN (V82.tactic refine)
        (if with_shelve then shelve_unifiable else tclUNIT ()))) gl
  else
    let t, gl = if n = 0 then t, gl else
      let sigma, si = project gl, sig_it gl in
      let rec loop sigma bo args = function (* saturate with metas *)
        | 0 -> mkApp (t, Array.of_list (List.rev args)), re_sig si sigma 
        | n -> match kind_of_term bo with
          | Lambda (_, ty, bo) -> 
              if not (closed0 ty) then raise dependent_apply_error;
              let m = Evarutil.new_meta () in
              loop (meta_declare m ty sigma) bo ((mkMeta m)::args) (n-1)
          | _ -> assert false
      in loop sigma t [] n in
    pp(lazy(str"Refiner.refiner " ++ pr_constr t));
    Refiner.refiner (Proof_type.Refine t) gl

let refine_with ?(first_goes_last=false) ?beta ?(with_evars=true) oc gl =
  let rec mkRels = function 1 -> [] | n -> mkRel n :: mkRels (n-1) in
  let uct = Evd.evar_universe_context (fst oc) in
  let n, oc = pf_abs_evars_pirrel gl oc in
  let gl = pf_unsafe_merge_uc uct gl in
  let oc = if not first_goes_last || n <= 1 then oc else
    let l, c = decompose_lam oc in
    if not (List.for_all_i (fun i (_,t) -> closedn ~-i t) (1-n) l) then oc else
    compose_lam (let xs,y = List.chop (n-1) l in y @ xs) 
      (mkApp (compose_lam l c, Array.of_list (mkRel 1 :: mkRels n)))
  in
  pp(lazy(str"after: " ++ pr_constr oc));
  try applyn ~with_evars ~with_shelve:true ?beta n oc gl with _ -> raise dependent_apply_error

let pf_fresh_inductive_instance ind gl =
  let sigma, env, it = project gl, pf_env gl, sig_it gl in
  let sigma, indu = Evd.fresh_inductive_instance env sigma ind in
  indu, re_sig it sigma

let subgoals_tys (relctx, concl) =
  let rec aux cur_depth acc = function
    | (_,_,ty) :: rest ->
        if noccurn cur_depth concl &&
           List.for_all_i (fun i -> function
             | _,None, t -> noccurn i t
             | _,Some b, t -> noccurn i t && noccurn i b) 1 rest
        then aux (cur_depth - 1) (ty :: acc) rest
        else aux (cur_depth - 1) acc rest
    | [] -> Array.of_list (List.rev acc)
  in
    aux (List.length relctx) [] (List.rev relctx)

(** The "case" and "elim" tactic *)

(* A case without explicit dependent terms but with both a view and an    *)
(* occurrence switch and/or an equation is treated as dependent, with the *)
(* viewed term as the dependent term (the occurrence switch would be      *)
(* meaningless otherwise). When both a view and explicit dependents are   *)
(* present, it is forbidden to put a (meaningless) occurrence switch on   *)
(* the viewed term.                                                       *)

(* This is both elim and case (defaulting to the former). If ~elim is omitted
 * the standard eliminator is chosen. The code is made of 4 parts:
 * 1. find the eliminator if not given as ~elim and analyze it
 * 2. build the patterns to be matched against the conclusion, looking at
 *    (occ, c), deps and the pattern inferred from the type of the eliminator
 * 3. build the new predicate matching the patterns, and the tactic to 
 *    generalize the equality in case eqid is not None
 * 4. build the tactic handle intructions and clears as required in ipats and
 *    by eqid *)
let ssrelim ?(ind=ref None) ?(is_case=false) ?ist deps what ?elim eqid ipats gl =
  (* some sanity checks *)
  let oc, orig_clr, occ, c_gen, gl = match what with
  | `EConstr(_,_,t) when isEvar t ->
    anomaly "elim called on a constr evar"
  | `EGen _ when ist = None ->
    anomaly "no ist and non simple elimination"
  | `EGen (_, g) when elim = None && is_wildcard g ->
       errorstrm(str"Indeterminate pattern and no eliminator")
  | `EGen ((Some clr,occ), g) when is_wildcard g ->
       None, clr, occ, None, gl
  | `EGen ((None, occ), g) when is_wildcard g -> None,[],occ,None,gl
  | `EGen ((_, occ), p as gen) ->
       let _, c, clr,gl = pf_interp_gen (Option.get ist) gl true gen in
       Some c, clr, occ, Some p,gl
  | `EConstr (clr, occ, c) -> Some c, clr, occ, None,gl in
  let orig_gl, concl, env = gl, pf_concl gl, pf_env gl in
  pp(lazy(str(if is_case then "==CASE==" else "==ELIM==")));
  (* Utils of local interest only *)
  let iD s ?t gl = let t = match t with None -> pf_concl gl | Some x -> x in
    pp(lazy(str s ++ pr_constr t)); tclIDTAC gl in
  let eq, gl = pf_fresh_global (build_coq_eq ()) gl in
  let protectC, gl = pf_mkSsrConst "protect_term" gl in
  let fire_subst gl t = Reductionops.nf_evar (project gl) t in
  let fire_sigma sigma t = Reductionops.nf_evar sigma t in
  let is_undef_pat = function
  | sigma, T t ->  
      (match kind_of_term (fire_sigma sigma t) with Evar _ -> true | _ -> false)
  | _ -> false in
  let match_pat env p occ h cl = 
    let sigma0 = project orig_gl in
    pp(lazy(str"matching: " ++ pr_occ occ ++ pp_pattern p));
    let (c,ucst), cl =
      fill_occ_pattern ~raise_NoMatch:true env sigma0 cl p occ h in
    pp(lazy(str"     got: " ++ pr_constr c));
    c, cl, ucst in
  let mkTpat gl t = (* takes a term, refreshes it and makes a T pattern *)
    let n, t, _, ucst = pf_abs_evars orig_gl (project gl, fire_subst gl t) in 
    let t, _, _, sigma = saturate ~beta:true env (project gl) t n in
    Evd.merge_universe_context sigma ucst, T t in
  let unif_redex gl (sigma, r as p) t = (* t is a hint for the redex of p *)
    let n, t, _, ucst = pf_abs_evars orig_gl (project gl, fire_subst gl t) in 
    let t, _, _, sigma = saturate ~beta:true env sigma t n in
    let sigma = Evd.merge_universe_context sigma ucst in
    match r with
    | X_In_T (e, p) -> sigma, E_As_X_In_T (t, e, p)
    | _ ->
       try unify_HO env sigma t (fst (redex_of_pattern env p)), r
       with e when Errors.noncritical e -> p in
  (* finds the eliminator applies it to evars and c saturated as needed  *)
  (* obtaining "elim ??? (c ???)". pred is the higher order evar         *)
  (* cty is None when the user writes _ (hence we can't make a pattern *)
  let cty, elim, elimty, elim_args, n_elim_args, elim_is_dep, is_rec, pred, gl =
    match elim with
    | Some elim ->
      let gl, elimty = pf_e_type_of gl elim in
      let pred_id, n_elim_args, is_rec, elim_is_dep, n_pred_args,ctx_concl =
        analyze_eliminator elimty env (project gl) in
      ind := Some (0, subgoals_tys ctx_concl);
      let elim, elimty, elim_args, gl =
        pf_saturate ~beta:is_case gl elim ~ty:elimty n_elim_args in
      let pred = List.assoc pred_id elim_args in
      let elimty = Reductionops.whd_betadeltaiota env (project gl) elimty in
      let cty, gl =
        if Option.is_empty oc then None, gl
        else
          let c = Option.get oc in let gl, c_ty = pf_type_of gl c in
          let pc = match c_gen with
            | Some p -> interp_cpattern (Option.get ist) orig_gl p None 
            | _ -> mkTpat gl c in
          Some(c, c_ty, pc), gl in
      cty, elim, elimty, elim_args, n_elim_args, elim_is_dep, is_rec, pred, gl
    | None ->
      let c = Option.get oc in let gl, c_ty = pf_type_of gl c in
      let ((kn, i), _ as indu), unfolded_c_ty =
        pf_reduce_to_quantified_ind gl c_ty in
      let sort = elimination_sort_of_goal gl in
      let gl, elim =
        if not is_case then
          let t,gl= pf_fresh_global (Indrec.lookup_eliminator (kn,i) sort) gl in
          gl, t
        else
          pf_eapply (fun env sigma () ->
            let sigma = Sigma.Unsafe.of_evar_map sigma in
            let Sigma (ind, sigma, _) = Indrec.build_case_analysis_scheme env sigma indu true sort in
            let sigma = Sigma.to_evar_map sigma in
            (sigma, ind)) gl () in
      let gl, elimty = pf_type_of gl elim in
      let pred_id,n_elim_args,is_rec,elim_is_dep,n_pred_args,ctx_concl =
        analyze_eliminator elimty env (project gl) in
      if is_case then
       let mind,indb = Inductive.lookup_mind_specif env (kn,i) in
       ind := Some(mind.Declarations.mind_nparams,indb.Declarations.mind_nf_lc);
      else
       ind := Some (0, subgoals_tys ctx_concl);
      let rctx = fst (decompose_prod_assum unfolded_c_ty) in
      let n_c_args = rel_context_length rctx in
      let c, c_ty, t_args, gl = pf_saturate gl c ~ty:c_ty n_c_args in
      let elim, elimty, elim_args, gl =
        pf_saturate ~beta:is_case gl elim ~ty:elimty n_elim_args in
      let pred = List.assoc pred_id elim_args in
      let pc = match n_c_args, c_gen with
        | 0, Some p -> interp_cpattern (Option.get ist) orig_gl p None 
        | _ -> mkTpat gl c in
      let cty = Some (c, c_ty, pc) in
      let elimty = Reductionops.whd_betadeltaiota env (project gl) elimty in
      cty, elim, elimty, elim_args, n_elim_args, elim_is_dep, is_rec, pred, gl
  in
  pp(lazy(str"elim= "++ pr_constr_pat elim));
  pp(lazy(str"elimty= "++ pr_constr_pat elimty));
  let inf_deps_r = match kind_of_type elimty with
    | AtomicType (_, args) -> List.rev (Array.to_list args)
    | _ -> assert false in
  let saturate_until gl c c_ty f =
    let rec loop n = try
      let c, c_ty, _, gl = pf_saturate gl c ~ty:c_ty n in
      let gl' = f c c_ty gl in
      Some (c, c_ty, gl, gl')
    with
    | NotEnoughProducts -> None
    | e when Errors.noncritical e -> loop (n+1) in loop 0 in
  (* Here we try to understand if the main pattern/term the user gave is
   * the first pattern to be matched (i.e. if elimty ends in P t1 .. tn,
   * weather tn is the t the user wrote in 'elim: t' *)
  let c_is_head_p, gl = match cty with
    | None -> true, gl  (* The user wrote elim: _ *)
    | Some (c, c_ty, _) ->
    let res = 
      (* we try to see if c unifies with the last arg of elim *)
      if elim_is_dep then None else
      let arg = List.assoc (n_elim_args - 1) elim_args in
      let gl, arg_ty = pf_type_of gl arg in
      match saturate_until gl c c_ty (fun c c_ty gl ->
        pf_unify_HO (pf_unify_HO gl c_ty arg_ty) arg c) with
      | Some (c, _, _, gl) -> Some (false, gl)
      | None -> None in
    match res with
    | Some x -> x
    | None ->
      (* we try to see if c unifies with the last inferred pattern *)
      let inf_arg = List.hd inf_deps_r in
      let gl, inf_arg_ty = pf_type_of gl inf_arg in
      match saturate_until gl c c_ty (fun _ c_ty gl ->
              pf_unify_HO gl c_ty inf_arg_ty) with
      | Some (c, _, _,gl) -> true, gl
      | None ->
        errorstrm (str"Unable to apply the eliminator to the term"++
          spc()++pr_constr c++spc()++str"or to unify it's type with"++
          pr_constr inf_arg_ty) in
  pp(lazy(str"c_is_head_p= " ++ bool c_is_head_p));
  let gl, predty = pf_type_of gl pred in
  (* Patterns for the inductive types indexes to be bound in pred are computed
   * looking at the ones provided by the user and the inferred ones looking at
   * the type of the elimination principle *)
  let pp_pat (_,p,_,occ) = pr_occ occ ++ pp_pattern p in
  let pp_inf_pat gl (_,_,t,_) = pr_constr_pat (fire_subst gl t) in
  let patterns, clr, gl =
    let rec loop patterns clr i = function
      | [],[] -> patterns, clr, gl
      | ((oclr, occ), t):: deps, inf_t :: inf_deps ->
          let ist = match ist with Some x -> x | None -> assert false in
          let p = interp_cpattern ist orig_gl t None in
          let clr_t =
            interp_clr (oclr,(tag_of_cpattern t,fst (redex_of_pattern env p)))in
          (* if we are the index for the equation we do not clear *)
          let clr_t = if deps = [] && eqid <> None then [] else clr_t in
          let p = if is_undef_pat p then mkTpat gl inf_t else p in
          loop (patterns @ [i, p, inf_t, occ]) 
            (clr_t @ clr) (i+1) (deps, inf_deps)
      | [], c :: inf_deps -> 
          pp(lazy(str"adding inf pattern " ++ pr_constr_pat c));
          loop (patterns @ [i, mkTpat gl c, c, allocc]) 
            clr (i+1) ([], inf_deps)
      | _::_, [] -> errorstrm (str "Too many dependent abstractions") in
    let deps, head_p, inf_deps_r = match what, c_is_head_p, cty with
    | `EConstr _, _, None -> anomaly "Simple elim with no term"
    | _, false, _ -> deps, [], inf_deps_r
    | `EGen gen, true, None -> deps @ [gen], [], inf_deps_r
    | _, true, Some (c, _, pc) ->
         let occ = if occ = None then allocc else occ in
         let inf_p, inf_deps_r = List.hd inf_deps_r, List.tl inf_deps_r in
         deps, [1, pc, inf_p, occ], inf_deps_r in
    let patterns, clr, gl = 
      loop [] orig_clr (List.length head_p+1) (List.rev deps, inf_deps_r) in
    head_p @ patterns, Util.List.uniquize clr, gl
  in
  pp(lazy(pp_concat (str"patterns=") (List.map pp_pat patterns)));
  pp(lazy(pp_concat (str"inf. patterns=") (List.map (pp_inf_pat gl) patterns)));
  (* Predicate generation, and (if necessary) tactic to generalize the
   * equation asked by the user *)
  let elim_pred, gen_eq_tac, clr, gl = 
    let error gl t inf_t = errorstrm (str"The given pattern matches the term"++
      spc()++pp_term gl t++spc()++str"while the inferred pattern"++
      spc()++pr_constr_pat (fire_subst gl inf_t)++spc()++ str"doesn't") in
    let match_or_postpone (cl, gl, post) (h, p, inf_t, occ) =
      let p = unif_redex gl p inf_t in
      if is_undef_pat p then
        let () = pp(lazy(str"postponing " ++ pp_pattern p)) in
        cl, gl, post @ [h, p, inf_t, occ]
      else try
        let c, cl, ucst = match_pat env p occ h cl in
        let gl = pf_merge_uc ucst gl in
        let gl = try pf_unify_HO gl inf_t c with _ -> error gl c inf_t in
        cl, gl, post
      with 
      | NoMatch | NoProgress ->
          let e, ucst = redex_of_pattern env p in
          let gl = pf_merge_uc ucst gl in
          let n, e, _, _ucst =  pf_abs_evars gl (fst p, e) in
          let e, _, _, gl = pf_saturate ~beta:true gl e n in 
          let gl = try pf_unify_HO gl inf_t e with _ -> error gl e inf_t in
          cl, gl, post
    in        
    let rec match_all concl gl patterns =
      let concl, gl, postponed = 
        List.fold_left match_or_postpone (concl, gl, []) patterns in
      if postponed = [] then concl, gl
      else if List.length postponed = List.length patterns then
        errorstrm (str "Some patterns are undefined even after all"++spc()++
          str"the defined ones matched")
      else match_all concl gl postponed in
    let concl, gl = match_all concl gl patterns in
    let pred_rctx, _ = decompose_prod_assum (fire_subst gl predty) in
    let concl, gen_eq_tac, clr, gl = match eqid with 
    | Some (IpatId _) when not is_rec -> 
        let k = List.length deps in
        let c = fire_subst gl (List.assoc (n_elim_args - k - 1) elim_args) in
        let gl, t = pf_type_of gl c in
        let gen_eq_tac, gl =
          let refl = mkApp (eq, [|t; c; c|]) in
          let new_concl = mkArrow refl (lift 1 (pf_concl orig_gl)) in 
          let new_concl = fire_subst gl new_concl in
          let erefl, gl = mkRefl t c gl in
          let erefl = fire_subst gl erefl in
          apply_type new_concl [erefl], gl in
        let rel = k + if c_is_head_p then 1 else 0 in
        let src, gl = mkProt mkProp (mkApp (eq,[|t; c; mkRel rel|])) gl in
        let concl = mkArrow src (lift 1 concl) in
        let clr = if deps <> [] then clr else [] in
        concl, gen_eq_tac, clr, gl
    | _ -> concl, tclIDTAC, clr, gl in
    let mk_lam t r = mkLambda_or_LetIn r t in
    let concl = List.fold_left mk_lam concl pred_rctx in
    let gl, concl = 
      if eqid <> None && is_rec then
        let gl, concls = pf_type_of gl concl in
        let concl, gl = mkProt concls concl gl in
        let gl, _ = pf_e_type_of gl concl in
        gl, concl
      else gl, concl in
    concl, gen_eq_tac, clr, gl in
  let gl, pty = pf_e_type_of gl elim_pred in
  pp(lazy(str"elim_pred=" ++ pp_term gl elim_pred));
  pp(lazy(str"elim_pred_ty=" ++ pp_term gl pty));
  let gl = pf_unify_HO gl pred elim_pred in
  let elim = fire_subst gl elim in
  let gl, _ = pf_e_type_of gl elim in
  (* check that the patterns do not contain non instantiated dependent metas *)
  let () = 
    let evars_of_term = Evarutil.undefined_evars_of_term (project gl) in
    let patterns = List.map (fun (_,_,t,_) -> fire_subst gl t) patterns in
    let patterns_ev = List.map evars_of_term patterns in 
    let ev = List.fold_left Intset.union Intset.empty patterns_ev in
    let ty_ev = Intset.fold (fun i e ->
         let ex = i in
         let i_ty = Evd.evar_concl (Evd.find (project gl) ex) in
         Intset.union e (evars_of_term i_ty))
      ev Intset.empty in
    let inter = Intset.inter ev ty_ev in
    if not (Intset.is_empty inter) then begin
      let i = Intset.choose inter in
      let pat = List.find (fun t -> Intset.mem i (evars_of_term t)) patterns in
      errorstrm(str"Pattern"++spc()++pr_constr_pat pat++spc()++
        str"was not completely instantiated and one of its variables"++spc()++
        str"occurs in the type of another non instantieted pattern variable");
    end
  in
  (* the elim tactic, with the eliminator and the predicated we computed *)
  let elim = project gl, elim in 
  let elim_tac gl = 
    tclTHENLIST [refine_with ~with_evars:false elim; cleartac clr] gl in
  (* handling of following intro patterns and equation introduction if any *)
  let elim_intro_tac gl = 
    let intro_eq = 
      match eqid with 
      | Some (IpatId ipat) when not is_rec -> 
          let rec intro_eq gl = match kind_of_type (pf_concl gl) with
          | ProdType (_, src, tgt) -> 
             (match kind_of_type src with
             | AtomicType (hd, _) when Term.eq_constr hd protectC -> 
                tclTHENLIST [unprotecttac; introid ipat] gl
             | _ -> tclTHENLIST [ iD "IA"; introstac [IpatAnon]; intro_eq] gl)
          |_ -> errorstrm (str "Too many names in intro pattern") in
          intro_eq
      | Some (IpatId ipat) -> 
        let name gl = mk_anon_id "K" gl in
        let intro_lhs gl = 
          let elim_name = match orig_clr, what with
            | [SsrHyp(_, x)], _ -> x
            | _, `EConstr(_,_,t) when isVar t -> destVar t
            | _ -> name gl in
          if is_name_in_ipats elim_name ipats then introid (name gl) gl
          else introid elim_name gl
        in
        let rec gen_eq_tac gl =
          let concl = pf_concl gl in
          let ctx, last = decompose_prod_assum concl in
          let args = match kind_of_type last with
          | AtomicType (hd, args) -> assert(Term.eq_constr hd protectC); args
          | _ -> assert false in
          let case = args.(Array.length args-1) in
          if not(closed0 case) then tclTHEN (introstac [IpatAnon]) gen_eq_tac gl
          else
          let gl, case_ty = pf_type_of gl case in 
          let refl = mkApp (eq, [|lift 1 case_ty; mkRel 1; lift 1 case|]) in
          let new_concl = fire_subst gl
            (mkProd (Name (name gl), case_ty, mkArrow refl (lift 2 concl))) in 
          let erefl, gl = mkRefl case_ty case gl in
          let erefl = fire_subst gl erefl in
          apply_type new_concl [case;erefl] gl in
        tclTHENLIST [gen_eq_tac; intro_lhs; introid ipat]
      | _ -> tclIDTAC in
    let unprot = if eqid <> None && is_rec then unprotecttac else tclIDTAC in
    tclEQINTROS ~ind ?ist elim_tac (tclTHENLIST [intro_eq; unprot]) ipats gl
  in
  tclTHENLIST [gen_eq_tac; elim_intro_tac] orig_gl
;;

let simplest_newelim x= ssrelim ~is_case:false [] (`EConstr ([],None,x)) None []
let simplest_newcase ?ind x= ssrelim ?ind ~is_case:true [] (`EConstr ([],None,x)) None []
let () = Hook.set Ssrcommon.simplest_newcase simplest_newcase

let check_casearg = function
| view, (_, (([_; gen :: _], _), _)) when view <> [] && has_occ gen ->
  Errors.error "incompatible view and occurrence switch in dependent case tactic"
| arg -> arg

ARGUMENT EXTEND ssrcasearg TYPED AS ssrarg PRINTED BY pr_ssrarg
| [ ssrarg(arg) ] -> [ check_casearg arg ]
END

let ssrcasetac ist (view, (eqid, (dgens, ipats))) =
  let ndefectcasetac view eqid ipats deps ((_, occ), _ as gen) ist gl =
    let simple = (eqid = None && deps = [] && occ = None) in
    let cl, c, clr, gl = pf_interp_gen ist gl true gen in
    let _,vc, gl =
      if view = [] then c,c, gl else pf_with_view_linear ist gl (false, view) cl c in
    if simple && is_injection_case vc gl then
      tclTHENLIST [perform_injection vc; cleartac clr; introstac ~ist ipats] gl
    else 
      (* macro for "case/v E: x" ---> "case E: x / (v x)" *)
      let deps, clr, occ = 
        if view <> [] && eqid <> None && deps = [] then [gen], [], None
        else deps, clr, occ in
      ssrelim ~is_case:true ~ist deps (`EConstr (clr,occ, vc)) eqid ipats gl
  in
  with_dgens dgens (ndefectcasetac view eqid ipats) ist

TACTIC EXTEND ssrcase
| [ "case" ssrcasearg(arg) ssrclauses(clauses) ] ->
  [ old_tac (tclCLAUSES ist (ssrcasetac ist arg) clauses) ]
| [ "case" ] -> [ old_tac (with_fresh_ctx (with_top (ssrscasetac false))) ]
END

(** The "elim" tactic *)

(* Elim views are elimination lemmas, so the eliminated term is not addded *)
(* to the dependent terms as for "case", unless it actually occurs in the  *)
(* goal, the "all occurrences" {+} switch is used, or the equation switch  *)
(* is used and there are no dependents.                                    *)

let ssrelimtac ist (view, (eqid, (dgens, ipats))) =
  let ndefectelimtac view eqid ipats deps gen ist gl =
    let elim = match view with [v] -> Some (snd(force_term ist gl v)) | _ -> None in
    ssrelim ~ist deps (`EGen gen) ?elim eqid ipats gl
  in
  with_dgens dgens (ndefectelimtac view eqid ipats) ist 

TACTIC EXTEND ssrelim
| [ "elim" ssrarg(arg) ssrclauses(clauses) ] ->
  [ old_tac (tclCLAUSES ist (ssrelimtac ist arg) clauses) ]
| [ "elim" ] -> [ old_tac (with_fresh_ctx (with_top simplest_newelim)) ]
END

(** 6. Backward chaining tactics: apply, exact, congr. *)

(** The "apply" tactic *)

let pr_agen (docc, dt) = pr_docc docc ++ pr_term dt
let pr_ssragen _ _ _ = pr_agen
let pr_ssragens _ _ _ = pr_dgens pr_agen

ARGUMENT EXTEND ssragen TYPED AS ssrdocc * ssrterm PRINTED BY pr_ssragen
| [ "{" ne_ssrhyp_list(clr) "}" ssrterm(dt) ] -> [ mkclr clr, dt ]
| [ ssrterm(dt) ] -> [ nodocc, dt ]
END

ARGUMENT EXTEND ssragens TYPED AS ssragen list list * ssrclear 
PRINTED BY pr_ssragens
| [ "{" ne_ssrhyp_list(clr) "}" ssrterm(dt) ssragens(agens) ] ->
  [ cons_gen (mkclr clr, dt) agens ]
| [ "{" ne_ssrhyp_list(clr) "}" ] -> [ [[]], clr]
| [ ssrterm(dt) ssragens(agens) ] ->
  [ cons_gen (nodocc, dt) agens ]
| [ ] -> [ [[]], [] ]
END

let mk_applyarg views agens intros = views, (None, (agens, intros))

let pr_ssraarg _ _ _ (view, (eqid, (dgens, ipats))) =
  let pri = pr_intros (gens_sep dgens) in
  pr_view view ++ pr_eqid eqid ++ pr_dgens pr_agen dgens ++ pri ipats

ARGUMENT EXTEND ssrapplyarg 
TYPED AS ssrview * (ssreqid * (ssragens * ssrintros))
PRINTED BY pr_ssraarg
| [ ":" ssragen(gen) ssragens(dgens) ssrintros(intros) ] ->
  [ mk_applyarg [] (cons_gen gen dgens) intros ]
| [ ssrclear_ne(clr) ssrintros(intros) ] ->
  [ mk_applyarg [] ([], clr) intros ]
| [ ssrintros_ne(intros) ] ->
  [ mk_applyarg [] ([], []) intros ]
| [ ssrview(view) ":" ssragen(gen) ssragens(dgens) ssrintros(intros) ] ->
  [ mk_applyarg view (cons_gen gen dgens) intros ]
| [ ssrview(view) ssrclear(clr) ssrintros(intros) ] ->
  [ mk_applyarg view ([], clr) intros ]
END

let interp_agen ist gl ((goclr, _), (k, gc)) (clr, rcs) =
(* pp(lazy(str"sigma@interp_agen=" ++ pr_evar_map None (project gl))); *)
  let rc = glob_constr ist (pf_env gl) gc in
  let rcs' = rc :: rcs in
  match goclr with
  | None -> clr, rcs'
  | Some ghyps ->
    let clr' = snd (interp_hyps ist gl ghyps) @ clr in
    if k <> NoFlag then clr', rcs' else
    match rc with
    | GVar (loc, id) when not_section_id id -> SsrHyp (loc, id) :: clr', rcs'
    | GRef (loc, VarRef id, _) when not_section_id id ->
        SsrHyp (loc, id) :: clr', rcs'
    | _ -> clr', rcs'

let interp_agens ist gl gagens =
  match List.fold_right (interp_agen ist gl) gagens ([], []) with
  | clr, rlemma :: args ->
    let n = interp_nbargs ist gl rlemma - List.length args in
    let rec loop i =
      if i > n then
         errorstrm (str "Cannot apply lemma " ++ pf_pr_glob_constr gl rlemma)
      else
        try interp_refine ist gl (mkRApp rlemma (mkRHoles i @ args))
        with _ -> loop (i + 1) in
    clr, loop 0
  | _ -> assert false

let apply_rconstr ?ist t gl =
(* pp(lazy(str"sigma@apply_rconstr=" ++ pr_evar_map None (project gl))); *)
  let n = match ist, t with
    | None, (GVar (_, id) | GRef (_, VarRef id,_)) -> pf_nbargs gl (mkVar id)
    | Some ist, _ -> interp_nbargs ist gl t
    | _ -> anomaly "apply_rconstr without ist and not RVar" in
  let mkRlemma i = mkRApp t (mkRHoles i) in
  let cl = pf_concl gl in
  let rec loop i =
    if i > n then
      errorstrm (str"Cannot apply lemma "++pf_pr_glob_constr gl t)
    else try pf_match gl (mkRlemma i) (OfType cl) with _ -> loop (i + 1) in
  refine_with (loop 0) gl

let mkRAppView ist gl rv gv =
  let nb_view_imps = interp_view_nbimps ist gl rv in
  mkRApp rv (mkRHoles (abs nb_view_imps))

let prof_apply_interp_with = mk_profiler "ssrapplytac.interp_with";;

let refine_interp_apply_view i ist gl gv =
  let pair i = List.map (fun x -> i, x) in
  let rv = pf_intern_term ist gl gv in
  let v = mkRAppView ist gl rv gv in
  let interp_with (i, hint) =
    interp_refine ist gl (mkRApp hint (v :: mkRHoles i)) in
  let interp_with x = prof_apply_interp_with.profile interp_with x in
  let rec loop = function
  | [] -> (try apply_rconstr ~ist rv gl with _ -> view_error "apply" gv)
  | h :: hs -> (try refine_with (snd (interp_with h)) gl with _ -> loop hs) in
  loop (pair i Ssrvernac.viewtab.(i) @
        if i = 2 then pair 1 Ssrvernac.viewtab.(1) else [])

let apply_top_tac gl =
  tclTHENLIST [introid top_id; apply_rconstr (mkRVar top_id); clear [top_id]] gl
    
let inner_ssrapplytac gviews ggenl gclr ist gl =
 let _, clr = interp_hyps ist gl gclr in
 let vtac gv i gl' = refine_interp_apply_view i ist gl' gv in
 let ggenl, tclGENTAC =
   if gviews <> [] && ggenl <> [] then
     let ggenl= List.map (fun (x,g) -> x, cpattern_of_term g) (List.hd ggenl) in
     [], tclTHEN (genstac (ggenl,[]) ist)
   else ggenl, tclTHEN tclIDTAC in
 tclGENTAC (fun gl ->
  match gviews, ggenl with
  | v :: tl, [] ->
    let dbl = if List.length tl = 1 then 2 else 1 in
    tclTHEN
      (List.fold_left (fun acc v -> tclTHENLAST acc (vtac v dbl)) (vtac v 1) tl)
      (cleartac clr) gl
  | [], [agens] ->
    let clr', (sigma, lemma) = interp_agens ist gl agens in
    let gl = pf_merge_uc_of sigma gl in
    tclTHENLIST [cleartac clr; refine_with ~beta:true lemma; cleartac clr'] gl
  | _, _ -> tclTHEN apply_top_tac (cleartac clr) gl) gl

let ssrapplytac ist (views, (_, ((gens, clr), intros))) =
  tclINTROS ist (inner_ssrapplytac views gens clr) intros

TACTIC EXTEND ssrapply
| [ "apply" ssrapplyarg(arg) ] -> [ Proofview.V82.tactic (ssrapplytac ist arg) ]
| [ "apply" ] -> [ Proofview.V82.tactic apply_top_tac ]
END

(** The "exact" tactic *)

let mk_exactarg views dgens = mk_applyarg views dgens []

ARGUMENT EXTEND ssrexactarg TYPED AS ssrapplyarg PRINTED BY pr_ssraarg
| [ ":" ssragen(gen) ssragens(dgens) ] ->
  [ mk_exactarg [] (cons_gen gen dgens) ]
| [ ssrview(view) ssrclear(clr) ] ->
  [ mk_exactarg view ([], clr) ]
| [ ssrclear_ne(clr) ] ->
  [ mk_exactarg [] ([], clr) ]
END

let vmexacttac pf gl = exact_no_check (mkCast (pf, VMcast, pf_concl gl)) gl

TACTIC EXTEND ssrexact
| [ "exact" ssrexactarg(arg) ] -> [ Proofview.V82.tactic (tclBY (ssrapplytac ist arg)) ]
| [ "exact" ] -> [ Proofview.V82.tactic (tclORELSE (donetac ~-1) (tclBY apply_top_tac)) ]
| [ "exact" "<:" lconstr(pf) ] -> [ Proofview.V82.tactic (vmexacttac pf) ]
END

(** The "congr" tactic *)

(* type ssrcongrarg = open_constr * (int * constr) *)

let pr_ssrcongrarg _ _ _ ((n, f), dgens) =
  (if n <= 0 then mt () else str " " ++ int n) ++
  str " " ++ pr_term f ++ pr_dgens pr_gen dgens

ARGUMENT EXTEND ssrcongrarg TYPED AS (int * ssrterm) * ssrdgens
  PRINTED BY pr_ssrcongrarg
| [ natural(n) constr(c) ssrdgens(dgens) ] -> [ (n, mk_term NoFlag c), dgens ]
| [ natural(n) constr(c) ] -> [ (n, mk_term NoFlag c),([[]],[]) ]
| [ constr(c) ssrdgens(dgens) ] -> [ (0, mk_term NoFlag c), dgens ]
| [ constr(c) ] -> [ (0, mk_term NoFlag c), ([[]],[]) ]
END

let rec mkRnat n =
  if n <= 0 then GRef (dummy_loc, glob_O, None) else
  mkRApp (GRef (dummy_loc, glob_S, None)) [mkRnat (n - 1)]

let interp_congrarg_at ist gl n rf ty m =
  pp(lazy(str"===interp_congrarg_at==="));
  let congrn, _ = mkSsrRRef "nary_congruence" in
  let args1 = mkRnat n :: mkRHoles n @ [ty] in
  let args2 = mkRHoles (3 * n) in
  let rec loop i =
    if i + n > m then None else
    try
      let rt = mkRApp congrn (args1 @  mkRApp rf (mkRHoles i) :: args2) in
      pp(lazy(str"rt=" ++ pr_glob_constr rt));
      Some (interp_refine ist gl rt)
    with _ -> loop (i + 1) in
  loop 0

let pattern_id = mk_internal_id "pattern value"

let congrtac ((n, t), ty) ist gl =
  pp(lazy(str"===congr==="));
  pp(lazy(str"concl=" ++ pr_constr (pf_concl gl)));
  let sigma, _ as it = interp_term ist gl t in
  let gl = pf_merge_uc_of sigma gl in
  let _, f, _, _ucst = pf_abs_evars gl it in
  let ist' = {ist with lfun =
    Id.Map.add pattern_id (Value.of_constr f) Id.Map.empty } in
  let rf = mkRltacVar pattern_id in
  let m = pf_nbargs gl f in
  let _, cf = if n > 0 then
    match interp_congrarg_at ist' gl n rf ty m with
    | Some cf -> cf
    | None -> errorstrm (str "No " ++ int n ++ str "-congruence with "
                         ++ pr_term t)
    else let rec loop i =
      if i > m then errorstrm (str "No congruence with " ++ pr_term t)
      else match interp_congrarg_at ist' gl i rf ty m with
      | Some cf -> cf
      | None -> loop (i + 1) in
      loop 1 in
  tclTHEN (refine_with cf) (tclTRY (Proofview.V82.of_tactic reflexivity)) gl

let newssrcongrtac arg ist gl =
  pp(lazy(str"===newcongr==="));
  pp(lazy(str"concl=" ++ pr_constr (pf_concl gl)));
  (* utils *)
  let fs gl t = Reductionops.nf_evar (project gl) t in
  let tclMATCH_GOAL (c, gl_c) proj t_ok t_fail gl =
    match try Some (pf_unify_HO gl_c (pf_concl gl) c) with _ -> None with  
    | Some gl_c ->
        tclTHEN (Proofview.V82.of_tactic (convert_concl (fs gl_c c)))
          (t_ok (proj gl_c)) gl
    | None -> t_fail () gl in 
  let mk_evar gl ty = 
    let env, sigma, si = pf_env gl, project gl, sig_it gl in
    let sigma = create_evar_defs sigma in
    let sigma = Sigma.Unsafe.of_evar_map sigma in
    let Sigma (x, sigma, _) = Evarutil.new_evar env sigma ty in
    let sigma = Sigma.to_evar_map sigma in
    x, re_sig si sigma in
  let arr, gl = pf_mkSsrConst "ssr_congr_arrow" gl in
  let ssr_congr lr = mkApp (arr, lr) in
  (* here thw two cases: simple equality or arrow *)
  let equality, _, eq_args, gl' =
    let eq, gl = pf_fresh_global (build_coq_eq ()) gl in
    pf_saturate gl eq 3 in
  tclMATCH_GOAL (equality, gl') (fun gl' -> fs gl' (List.assoc 0 eq_args))
  (fun ty -> congrtac (arg, Detyping.detype false [] (pf_env gl) (project gl) ty) ist)
  (fun () ->
    let lhs, gl' = mk_evar gl mkProp in let rhs, gl' = mk_evar gl' mkProp in
    let arrow = mkArrow lhs (lift 1 rhs) in
    tclMATCH_GOAL (arrow, gl') (fun gl' -> [|fs gl' lhs;fs gl' rhs|])
    (fun lr -> tclTHEN (Proofview.V82.of_tactic (apply (ssr_congr lr))) (congrtac (arg, mkRType) ist))
    (fun _ _ -> errorstrm (str"Conclusion is not an equality nor an arrow")))
    gl
;;

TACTIC EXTEND ssrcongr
| [ "congr" ssrcongrarg(arg) ] ->
[ let arg, dgens = arg in
  Proofview.V82.tactic begin
    match dgens with
    | [gens], clr -> tclTHEN (genstac (gens,clr) ist) (newssrcongrtac arg ist)
    | _ -> errorstrm (str"Dependent family abstractions not allowed in congr")
  end]
END

(** 7. Rewriting tactics (rewrite, unlock) *)

(** Coq rewrite compatibility flag *)

let ssr_strict_match = ref false

let _ =
  Goptions.declare_bool_option 
    { Goptions.optsync  = true;
      Goptions.optname  = "strict redex matching";
      Goptions.optkey   = ["Match"; "Strict"];
      Goptions.optread  = (fun () -> !ssr_strict_match);
      Goptions.optdepr  = false;
      Goptions.optwrite = (fun b -> ssr_strict_match := b) }

(** Rewrite clear/occ switches *)

let pr_rwocc = function
  | None, None -> mt ()
  | None, occ -> pr_occ occ
  | Some clr,  _ ->  pr_clear_ne clr

let pr_ssrrwocc _ _ _ = pr_rwocc

ARGUMENT EXTEND ssrrwocc TYPED AS ssrdocc PRINTED BY pr_ssrrwocc
| [ "{" ssrhyp_list(clr) "}" ] -> [ mkclr clr ]
| [ "{" ssrocc(occ) "}" ] -> [ mkocc occ ]
| [ ] -> [ noclr ]
END

(** Rewrite rules *)

type ssrwkind = RWred of ssrsimpl | RWdef | RWeq
(* type ssrrule = ssrwkind * ssrterm *)

let pr_rwkind = function
  | RWred s -> pr_simpl s
  | RWdef -> str "/"
  | RWeq -> mt ()

let wit_ssrrwkind = add_genarg "ssrrwkind" pr_rwkind

let pr_rule = function
  | RWred s, _ -> pr_simpl s
  | RWdef, r-> str "/" ++ pr_term r
  | RWeq, r -> pr_term r

let pr_ssrrule _ _ _ = pr_rule

let noruleterm loc = mk_term NoFlag (mkCProp loc)

ARGUMENT EXTEND ssrrule_ne TYPED AS ssrrwkind * ssrterm PRINTED BY pr_ssrrule
  | [ "YouShouldNotTypeThis" ] -> [ anomaly "Grammar placeholder match" ]
END

GEXTEND Gram
  GLOBAL: ssrrule_ne;
  ssrrule_ne : [
    [ test_not_ssrslashnum; x =
        [ "/"; t = ssrterm -> RWdef, t
        | t = ssrterm -> RWeq, t 
        | s = ssrsimpl_ne -> RWred s, noruleterm !@loc
        ] -> x
    | s = ssrsimpl_ne -> RWred s, noruleterm !@loc
  ]];
END

ARGUMENT EXTEND ssrrule TYPED AS ssrrule_ne PRINTED BY pr_ssrrule
  | [ ssrrule_ne(r) ] -> [ r ]
  | [ ] -> [ RWred Nop, noruleterm loc ]
END

(** Rewrite arguments *)

(* type ssrrwarg = (ssrdir * ssrmult) * ((ssrdocc * ssrpattern) * ssrrule) *)

let pr_option f = function None -> mt() | Some x -> f x
let pr_pattern_squarep= pr_option (fun r -> str "[" ++ pr_rpattern r ++ str "]")
let pr_ssrpattern_squarep _ _ _ = pr_pattern_squarep
let pr_rwarg ((d, m), ((docc, rx), r)) =
  pr_rwdir d ++ pr_mult m ++ pr_rwocc docc ++ pr_pattern_squarep rx ++ pr_rule r

let pr_ssrrwarg _ _ _ = pr_rwarg

let is_rw_cut = function RWred (Cut _) -> true | _ -> false

let mk_rwarg (d, (n, _ as m)) ((clr, occ as docc), rx) (rt, _ as r) =   
 if rt <> RWeq then begin
   if rt = RWred Nop && not (m = nomult && occ = None && rx = None)
                     && (clr = None || clr = Some []) then
     anomaly "Improper rewrite clear switch";
   if d = R2L && rt <> RWdef then
     Errors.error "Right-to-left switch on simplification";
   if n <> 1 && is_rw_cut rt then
     Errors.error "Bad or useless multiplier";
   if occ <> None && rx = None && rt <> RWdef then
     Errors.error "Missing redex for simplification occurrence"
 end; (d, m), ((docc, rx), r)

let norwmult = L2R, nomult
let norwocc = noclr, None

(*
let pattern_ident = Prim.pattern_ident in
GEXTEND Gram
GLOBAL: pattern_ident;
pattern_ident: 
[[c = pattern_ident -> (CRef (Ident (loc,c)), NoBindings)]];
END
*)

ARGUMENT EXTEND ssrpattern_squarep
TYPED AS rpattern option PRINTED BY pr_ssrpattern_squarep
  | [ "[" rpattern(rdx) "]" ] -> [ Some rdx ]
  | [ ] -> [ None ]
END

ARGUMENT EXTEND ssrpattern_ne_squarep
TYPED AS rpattern option PRINTED BY pr_ssrpattern_squarep
  | [ "[" rpattern(rdx) "]" ] -> [ Some rdx ]
END


ARGUMENT EXTEND ssrrwarg
  TYPED AS (ssrdir * ssrmult) * ((ssrdocc * rpattern option) * ssrrule)
  PRINTED BY pr_ssrrwarg
  | [ "-" ssrmult(m) ssrrwocc(docc) ssrpattern_squarep(rx) ssrrule_ne(r) ] ->
    [ mk_rwarg (R2L, m) (docc, rx) r ]
  | [ "-/" ssrterm(t) ] ->     (* just in case '-/' should become a token *)
    [ mk_rwarg (R2L, nomult) norwocc (RWdef, t) ]
  | [ ssrmult_ne(m) ssrrwocc(docc) ssrpattern_squarep(rx) ssrrule_ne(r) ] ->
    [ mk_rwarg (L2R, m) (docc, rx) r ]
  | [ "{" ne_ssrhyp_list(clr) "}" ssrpattern_ne_squarep(rx) ssrrule_ne(r) ] ->
    [ mk_rwarg norwmult (mkclr clr, rx) r ]
  | [ "{" ne_ssrhyp_list(clr) "}" ssrrule(r) ] ->
    [ mk_rwarg norwmult (mkclr clr, None) r ]
  | [ "{" ssrocc(occ) "}" ssrpattern_squarep(rx) ssrrule_ne(r) ] ->
    [ mk_rwarg norwmult (mkocc occ, rx) r ]
  | [ "{" "}" ssrpattern_squarep(rx) ssrrule_ne(r) ] ->
    [ mk_rwarg norwmult (nodocc, rx) r ]
  | [ ssrpattern_ne_squarep(rx) ssrrule_ne(r) ] ->
    [ mk_rwarg norwmult (noclr, rx) r ]
  | [ ssrrule_ne(r) ] ->
    [ mk_rwarg norwmult norwocc r ]
END

let simplintac occ rdx sim gl = 
  let simptac m gl =
    if m <> ~-1 then
      Errors.error "Localized custom simpl tactic not supported";
    let sigma0, concl0, env0 = project gl, pf_concl gl, pf_env gl in
    let simp env c _ _ = red_safe (tacred_simpl gl) env sigma0 c in
    Proofview.V82.of_tactic
      (convert_concl_no_check (eval_pattern env0 sigma0 concl0 rdx occ simp))
      gl in
  match sim with
  | Simpl m -> simptac m gl
  | SimplCut (n,m) -> tclTHEN (simptac m) (tclTRY (donetac n)) gl
  | _ -> simpltac sim gl

let rec get_evalref c =  match kind_of_term c with
  | Var id -> EvalVarRef id
  | Const (k,_) -> EvalConstRef k
  | App (c', _) -> get_evalref c'
  | Cast (c', _, _) -> get_evalref c'
  | _ -> errorstrm (str "The term " ++ pr_constr c ++ str " is not unfoldable")

(* Strip a pattern generated by a prenex implicit to its constant. *)
let strip_unfold_term ((sigma, t) as p) kt = match kind_of_term t with
  | App (f, a) when kt = NoFlag && Array.for_all isEvar a && isConst f -> 
    (sigma, f), true
  | Const _ | Var _ -> p, true
  | _ -> p, false

let unfoldintac occ rdx t (kt,_) gl = 
  let fs sigma x = Reductionops.nf_evar sigma x in
  let sigma0, concl0, env0 = project gl, pf_concl gl, pf_env gl in
  let (sigma, t), const = strip_unfold_term t kt in
  let body env t c =
    Tacred.unfoldn [OnlyOccurrences [1], get_evalref t] env sigma0 c in
  let easy = occ = None && rdx = None in
  let red_flags = if easy then Closure.betaiotazeta else Closure.betaiota in
  let beta env = Reductionops.clos_norm_flags red_flags env sigma0 in
  let unfold, conclude = match rdx with
  | Some (_, (In_T _ | In_X_In_T _)) | None ->
    let ise = create_evar_defs sigma in
    let ise, u = mk_tpattern env0 sigma0 (ise,t) all_ok L2R t in
    let find_T, end_T =
      mk_tpattern_matcher ~raise_NoMatch:true sigma0 occ (ise,[u]) in
    (fun env c _ h -> 
      try find_T env c h (fun env c _ _ -> body env t c)
      with NoMatch when easy -> c
      | NoMatch | NoProgress -> errorstrm (str"No occurrence of "
        ++ pr_constr_pat t ++ spc() ++ str "in " ++ pr_constr c)),
    (fun () -> try end_T () with 
      | NoMatch when easy -> fake_pmatcher_end () 
      | NoMatch -> anomaly "unfoldintac")
  | _ -> 
    (fun env (c as orig_c) _ h ->
      if const then
          let rec aux c = 
            match kind_of_term c with
            | Const _ when Term.eq_constr c t -> body env t t
            | App (f,a) when Term.eq_constr f t -> mkApp (body env f f,a)
            | _ -> let c = Reductionops.whd_betaiotazeta sigma0 c in
            match kind_of_term c with
            | Const _ when Term.eq_constr c t -> body env t t
            | App (f,a) when Term.eq_constr f t -> mkApp (body env f f,a)
            | Const f -> aux (body env c c)
            | App (f, a) -> aux (mkApp (body env f f, a))
            | _ -> errorstrm (str "The term "++pr_constr orig_c++
                str" contains no " ++ pr_constr t ++ str" even after unfolding")
          in aux c
      else
        try body env t (fs (unify_HO env sigma c t) t)
        with _ -> errorstrm (str "The term " ++
          pr_constr c ++spc()++ str "does not unify with " ++ pr_constr_pat t)),
    fake_pmatcher_end in
  let concl = 
    try beta env0 (eval_pattern env0 sigma0 concl0 rdx occ unfold) 
    with Option.IsNone -> errorstrm (str"Failed to unfold " ++ pr_constr_pat t) in
  let _ = conclude () in
  Proofview.V82.of_tactic (convert_concl concl) gl
;;

let foldtac occ rdx ft gl = 
  let fs sigma x = Reductionops.nf_evar sigma x in
  let sigma0, concl0, env0 = project gl, pf_concl gl, pf_env gl in
  let sigma, t = ft in
  let fold, conclude = match rdx with
  | Some (_, (In_T _ | In_X_In_T _)) | None ->
    let ise = create_evar_defs sigma in
    let ut = red_product_skip_id env0 sigma t in
    let ise, ut = mk_tpattern env0 sigma0 (ise,t) all_ok L2R ut in
    let find_T, end_T =
      mk_tpattern_matcher ~raise_NoMatch:true sigma0 occ (ise,[ut]) in
    (fun env c _ h -> try find_T env c h (fun env t _ _ -> t) with NoMatch ->c),
    (fun () -> try end_T () with NoMatch -> fake_pmatcher_end ())
  | _ -> 
    (fun env c _ h -> try let sigma = unify_HO env sigma c t in fs sigma t
    with _ -> errorstrm (str "fold pattern " ++ pr_constr_pat t ++ spc ()
      ++ str "does not match redex " ++ pr_constr_pat c)), 
    fake_pmatcher_end in
  let concl = eval_pattern env0 sigma0 concl0 rdx occ fold in
  let _ = conclude () in
  Proofview.V82.of_tactic (convert_concl concl) gl
;;

let converse_dir = function L2R -> R2L | R2L -> L2R

let rw_progress rhs lhs ise = not (Term.eq_constr lhs (Evarutil.nf_evar ise rhs))

(* Coq has a more general form of "equation" (any type with a single *)
(* constructor with no arguments with_rect_r elimination lemmas).    *)
(* However there is no clear way of determining the LHS and RHS of   *)
(* such a generic Leibnitz equation -- short of inspecting the type  *)
(* of the elimination lemmas.                                        *)

let rec strip_prod_assum c = match kind_of_term c with
  | Prod (_, _, c') -> strip_prod_assum c'
  | LetIn (_, v, _, c') -> strip_prod_assum (subst1 v c)
  | Cast (c', _, _) -> strip_prod_assum c'
  | _ -> c

let rule_id = mk_internal_id "rewrite rule"

exception PRtype_error
exception PRindetermined_rhs of constr

let pirrel_rewrite pred rdx rdx_ty new_rdx dir (sigma, c) c_ty gl =
(*   pp(lazy(str"sigma@pirrel_rewrite=" ++ pr_evar_map None sigma)); *)
  let env = pf_env gl in
  let beta = Reductionops.clos_norm_flags Closure.beta env sigma in
  let sigma, p = 
    let sigma = create_evar_defs sigma in
    let sigma = Sigma.Unsafe.of_evar_map sigma in
    let Sigma (ev, sigma, _) = Evarutil.new_evar env sigma (beta (subst1 new_rdx pred)) in
    let sigma = Sigma.to_evar_map sigma in
    (sigma, ev)
  in
  let pred = mkNamedLambda pattern_id rdx_ty pred in
  let elim, gl = 
    let ((kn, i) as ind, _), unfolded_c_ty = pf_reduce_to_quantified_ind gl c_ty in
    let sort = elimination_sort_of_goal gl in
    let elim, gl = pf_fresh_global (Indrec.lookup_eliminator ind sort) gl in
    if dir = R2L then elim, gl else (* taken from Coq's rewrite *)
    let elim, _ = destConst elim in          
    let mp,dp,l = repr_con (constant_of_kn (canonical_con elim)) in
    let l' = label_of_id (Nameops.add_suffix (id_of_label l) "_r")  in 
    let c1' = Global.constant_of_delta_kn (canonical_con (make_con mp dp l')) in
    mkConst c1', gl in
  let proof = mkApp (elim, [| rdx_ty; new_rdx; pred; p; rdx; c |]) in
  (* We check the proof is well typed *)
  let sigma, proof_ty =
    try Typing.type_of env sigma proof with _ -> raise PRtype_error in
  pp(lazy(str"pirrel_rewrite proof term of type: " ++ pr_constr proof_ty));
  try refine_with 
    ~first_goes_last:(not !ssroldreworder) ~with_evars:false (sigma, proof) gl
  with _ -> 
    (* we generate a msg like: "Unable to find an instance for the variable" *)
    let c = Reductionops.nf_evar sigma c in
    let hd_ty, miss = match kind_of_term c with
    | App (hd, args) -> 
        let hd_ty = Retyping.get_type_of env sigma hd in
        let names = let rec aux t = function 0 -> [] | n ->
          let t = Reductionops.whd_betadeltaiota env sigma t in
          match kind_of_type t with
          | ProdType (name, _, t) -> name :: aux t (n-1)
          | _ -> assert false in aux hd_ty (Array.length args) in
        hd_ty, Util.List.map_filter (fun (t, name) ->
          let evs = Intset.elements (Evarutil.undefined_evars_of_term sigma t) in
          let open_evs = List.filter (fun k ->
            InProp <> Retyping.get_sort_family_of
              env sigma (Evd.evar_concl (Evd.find sigma k)))
            evs in
          if open_evs <> [] then Some name else None)
          (List.combine (Array.to_list args) names)
    | _ -> anomaly "rewrite rule not an application" in
    errorstrm (Himsg.explain_refiner_error (Logic.UnresolvedBindings miss)++
      (Pp.fnl()++str"Rule's type:" ++ spc() ++ pr_constr hd_ty))
;;

let is_const_ref c r = isConst c && eq_gr (ConstRef (fst(destConst c))) r
let is_construct_ref c r =
  isConstruct c && eq_gr (ConstructRef (fst(destConstruct c))) r
let is_ind_ref c r = isInd c && eq_gr (IndRef (fst(destInd c))) r

let rwcltac cl rdx dir sr gl =
  let n, r_n,_, ucst = pf_abs_evars gl sr in
  let r_n' = pf_abs_cterm gl n r_n in
  let r' = subst_var pattern_id r_n' in
  let gl = pf_unsafe_merge_uc ucst gl in
  let rdxt = Retyping.get_type_of (pf_env gl) (fst sr) rdx in
(*         pp(lazy(str"sigma@rwcltac=" ++ pr_evar_map None (fst sr))); *)
        pp(lazy(str"r@rwcltac=" ++ pr_constr (snd sr)));
  let cvtac, rwtac, gl =
    if closed0 r' then 
      let env, sigma, c, c_eq = pf_env gl, fst sr, snd sr, build_coq_eq () in
      let sigma, c_ty = Typing.type_of env sigma c in
        pp(lazy(str"c_ty@rwcltac=" ++ pr_constr c_ty));
      match kind_of_type (Reductionops.whd_betadeltaiota env sigma c_ty) with
      | AtomicType(e, a) when is_ind_ref e c_eq ->
          let new_rdx = if dir = L2R then a.(2) else a.(1) in
          pirrel_rewrite cl rdx rdxt new_rdx dir (sigma,c) c_ty, tclIDTAC, gl
      | _ -> 
          let cl' = mkApp (mkNamedLambda pattern_id rdxt cl, [|rdx|]) in
          let sigma, _ = Typing.type_of env sigma cl' in
          let gl = pf_merge_uc_of sigma gl in
          Proofview.V82.of_tactic (convert_concl cl'), rewritetac dir r', gl
    else
      let dc, r2 = decompose_lam_n n r' in
      let r3, _, r3t  = 
        try destCast r2 with _ ->
        errorstrm (str "no cast from " ++ pr_constr_pat (snd sr)
                    ++ str " to " ++ pr_constr r2) in
      let cl' = mkNamedProd rule_id (compose_prod dc r3t) (lift 1 cl) in
      let cl'' = mkNamedProd pattern_id rdxt cl' in
      let itacs = [introid pattern_id; introid rule_id] in
      let cltac = clear [pattern_id; rule_id] in
      let rwtacs = [rewritetac dir (mkVar rule_id); cltac] in
      apply_type cl'' [rdx; compose_lam dc r3], tclTHENLIST (itacs @ rwtacs), gl
  in
  let cvtac' _ =
    try cvtac gl with
    | PRtype_error ->
      if occur_existential (pf_concl gl)
      then errorstrm (str "Rewriting impacts evars")
      else errorstrm (str "Dependent type error in rewrite of "
        ++ pf_pr_constr gl (project gl) (mkNamedLambda pattern_id rdxt cl))
    | Errors.UserError _ as e -> raise e
    | e -> anomaly ("cvtac's exception: " ^ Printexc.to_string e);
  in
  tclTHEN cvtac' rwtac gl

let prof_rwcltac = mk_profiler "rwrxtac.rwcltac";;
let rwcltac cl rdx dir sr gl =
  prof_rwcltac.profile (rwcltac cl rdx dir sr) gl
;;


let lz_coq_prod =
  let prod = lazy (build_prod ()) in fun () -> Lazy.force prod

let lz_setoid_relation =
  let sdir = ["Classes"; "RelationClasses"] in
  let last_srel = ref (Environ.empty_env, None) in
  fun env -> match !last_srel with
  | env', srel when env' == env -> srel
  | _ ->
    let srel =
       try Some (coq_constant "Class_setoid" sdir "RewriteRelation")
       with _ -> None in
    last_srel := (env, srel); srel

let ssr_is_setoid env =
  match lz_setoid_relation env with
  | None -> fun _ _ _ -> false
  | Some srel ->
  fun sigma r args ->
    Rewrite.is_applied_rewrite_relation env 
      sigma [] (mkApp (r, args)) <> None

let prof_rwxrtac_find_rule = mk_profiler "rwrxtac.find_rule";;

let closed0_check cl p gl =
  if closed0 cl then
    errorstrm (str"No occurrence of redex "++pf_pr_constr gl (project gl) p)

let rwprocess_rule dir rule gl =
  let env = pf_env gl in
  let coq_prod = lz_coq_prod () in
  let is_setoid = ssr_is_setoid env in
  let r_sigma, rules =
    let rec loop d sigma r t0 rs red =
      let t =
        if red = 1 then Tacred.hnf_constr env sigma t0
        else Reductionops.whd_betaiotazeta sigma t0 in
      pp(lazy(str"rewrule="++pr_constr t));
      match kind_of_term t with
      | Prod (_, xt, at) ->
        let sigma = create_evar_defs sigma in
        let sigma = Sigma.Unsafe.of_evar_map sigma in
        let Sigma (x, sigma, _) = Evarutil.new_evar env sigma xt in
        let ise = Sigma.to_evar_map sigma in
        loop d ise (mkApp (r, [|x|])) (subst1 x at) rs 0
      | App (pr, a) when is_ind_ref pr coq_prod.Coqlib.typ ->
        let sr sigma = match kind_of_term (Tacred.hnf_constr env sigma r) with
        | App (c, ra) when is_construct_ref c coq_prod.Coqlib.intro ->
          fun i -> ra.(i + 1), sigma
        | _ -> let ra = Array.append a [|r|] in
          function 1 ->
            let sigma, pi1 = Evd.fresh_global env sigma coq_prod.Coqlib.proj1 in
            mkApp (pi1, ra), sigma
          | _ ->
            let sigma, pi2 = Evd.fresh_global env sigma coq_prod.Coqlib.proj2 in
            mkApp (pi2, ra), sigma in
        if Term.eq_constr a.(0) (build_coq_True ()) then
         let s, sigma = sr sigma 2 in
         loop (converse_dir d) sigma s a.(1) rs 0
        else
         let s, sigma = sr sigma 2 in
         let sigma, rs2 = loop d sigma s a.(1) rs 0 in
         let s, sigma = sr sigma 1 in
         loop d sigma s a.(0) rs2 0
      | App (r_eq, a) when Hipattern.match_with_equality_type t != None ->
        let indu = destInd r_eq and rhs = Array.last a in
        let np = Inductiveops.inductive_nparamdecls (fst indu) in
        let ind_ct = Inductiveops.type_of_constructors env indu in
        let lhs0 = last_arg (strip_prod_assum ind_ct.(0)) in
        let rdesc = match kind_of_term lhs0 with
        | Rel i ->
          let lhs = a.(np - i) in
          let lhs, rhs = if d = L2R then lhs, rhs else rhs, lhs in
(* msgnl (str "RW: " ++ pr_rwdir d ++ str " " ++ pr_constr_pat r ++ str " : "
            ++ pr_constr_pat lhs ++ str " ~> " ++ pr_constr_pat rhs); *)
          d, r, lhs, rhs
(*
          let l_i, r_i = if d = L2R then i, 1 - ndep else 1 - ndep, i in
          let lhs = a.(np - l_i) and rhs = a.(np - r_i) in
          let a' = Array.copy a in let _ = a'.(np - l_i) <- mkVar pattern_id in
          let r' = mkCast (r, DEFAULTcast, mkApp (r_eq, a')) in
          (d, r', lhs, rhs)
*)
        | _ ->
          let lhs = substl (array_list_of_tl (Array.sub a 0 np)) lhs0 in
          let lhs, rhs = if d = R2L then lhs, rhs else rhs, lhs in
          let d' = if Array.length a = 1 then d else converse_dir d in
          d', r, lhs, rhs in
        sigma, rdesc :: rs
      | App (s_eq, a) when is_setoid sigma s_eq a ->
        let np = Array.length a and i = 3 - dir_org d in
        let lhs = a.(np - i) and rhs = a.(np + i - 3) in
        let a' = Array.copy a in let _ = a'.(np - i) <- mkVar pattern_id in
        let r' = mkCast (r, DEFAULTcast, mkApp (s_eq, a')) in
        sigma, (d, r', lhs, rhs) :: rs
      | _ ->
        if red = 0 then loop d sigma r t rs 1
        else errorstrm (str "not a rewritable relation: " ++ pr_constr_pat t
                        ++ spc() ++ str "in rule " ++ pr_constr_pat (snd rule))
        in
    let sigma, r = rule in
    let t = Retyping.get_type_of env sigma r in
    loop dir sigma r t [] 0
  in
    r_sigma, rules

let rwrxtac occ rdx_pat dir rule gl =
  let env = pf_env gl in
  let r_sigma, rules = rwprocess_rule dir rule gl in
  let find_rule rdx =
    let rec rwtac = function
      | [] ->
        errorstrm (str "pattern " ++ pr_constr_pat rdx ++
                   str " does not match " ++ pr_dir_side dir ++
                   str " of " ++ pr_constr_pat (snd rule))
      | (d, r, lhs, rhs) :: rs ->
        try
          let ise = unify_HO env (create_evar_defs r_sigma) lhs rdx in
          if not (rw_progress rhs rdx ise) then raise NoMatch else
          d, (ise, Evd.evar_universe_context ise, Reductionops.nf_evar ise r)
        with _ -> rwtac rs in
     rwtac rules in
  let find_rule rdx = prof_rwxrtac_find_rule.profile find_rule rdx in
  let sigma0, env0, concl0 = project gl, pf_env gl, pf_concl gl in
  let find_R, conclude = match rdx_pat with
  | Some (_, (In_T _ | In_X_In_T _)) | None ->
      let upats_origin = dir, snd rule in
      let rpat env sigma0 (sigma, pats) (d, r, lhs, rhs) =
        let sigma, pat =
          mk_tpattern env sigma0 (sigma,r) (rw_progress rhs) d lhs in
        sigma, pats @ [pat] in
      let rpats = List.fold_left (rpat env0 sigma0) (r_sigma,[]) rules in
      let find_R, end_R = mk_tpattern_matcher sigma0 occ ~upats_origin rpats in
      (fun e c _ i -> find_R ~k:(fun _ _ _ h -> mkRel h) e c i), 
      fun cl -> let rdx,d,r = end_R () in closed0_check cl rdx gl; (d,r),rdx
  | Some(_, (T e | X_In_T (_,e) | E_As_X_In_T (e,_,_) | E_In_X_In_T (e,_,_))) ->
      let r = ref None in
      (fun env c _ h -> do_once r (fun () -> find_rule c, c); mkRel h),
      (fun concl -> closed0_check concl e gl; assert_done r) in
  let concl = eval_pattern env0 sigma0 concl0 rdx_pat occ find_R in
  let (d, r), rdx = conclude concl in
  let r = Evd.merge_universe_context (pi1 r) (pi2 r), pi3 r in
  rwcltac concl rdx d r gl
;;

let prof_rwxrtac = mk_profiler "rwrxtac";;
let rwrxtac occ rdx_pat dir rule gl =
  prof_rwxrtac.profile (rwrxtac occ rdx_pat dir rule) gl
;;

let ssrinstancesofrule ist dir arg gl =
  let sigma0, env0, concl0 = project gl, pf_env gl, pf_concl gl in
  let rule = interp_term ist gl arg in
  let r_sigma, rules = rwprocess_rule dir rule gl in
  let find, conclude =
    let upats_origin = dir, snd rule in
    let rpat env sigma0 (sigma, pats) (d, r, lhs, rhs) =
      let sigma, pat =
        mk_tpattern env sigma0 (sigma,r) (rw_progress rhs) d lhs in
      sigma, pats @ [pat] in
    let rpats = List.fold_left (rpat env0 sigma0) (r_sigma,[]) rules in
    mk_tpattern_matcher ~all_instances:true ~raise_NoMatch:true sigma0 None ~upats_origin rpats in
  let print env p c _ = ppnl (hov 1 (str"instance:" ++ spc() ++ pr_constr p ++ spc() ++ str "matches:" ++ spc() ++ pr_constr c)); c in
  ppnl (str"BEGIN INSTANCES");
  try
    while true do
      ignore(find env0 concl0 1 ~k:print)
    done; raise NoMatch
  with NoMatch -> ppnl (str"END INSTANCES"); tclIDTAC gl

TACTIC EXTEND ssrinstofruleL2R
| [ "ssrinstancesofruleL2R" ssrterm(arg) ] -> [ Proofview.V82.tactic (ssrinstancesofrule ist L2R arg) ]
END
TACTIC EXTEND ssrinstofruleR2L
| [ "ssrinstancesofruleR2L" ssrterm(arg) ] -> [ Proofview.V82.tactic (ssrinstancesofrule ist R2L arg) ]
END

(* Resolve forward reference *)
let () = Hook.set Ssrcommon.ipat_rewrite 
  (fun occ dir c gl -> rwrxtac occ None dir (project gl, c) gl)

let rwargtac ist ((dir, mult), (((oclr, occ), grx), (kind, gt))) gl =
  let fail = ref false in
  let interp_rpattern ist gl gc =
    try interp_rpattern ist gl gc
    with _ when snd mult = May -> fail := true; project gl, T mkProp in
  let interp gc gl =
    try interp_term ist gl gc
    with _ when snd mult = May -> fail := true; (project gl, mkProp) in
  let rwtac gl = 
    let rx = Option.map (interp_rpattern ist gl) grx in
    let t = interp gt gl in
    (match kind with
    | RWred sim -> simplintac occ rx sim
    | RWdef -> if dir = R2L then foldtac occ rx t else unfoldintac occ rx t gt
    | RWeq -> rwrxtac occ rx dir t) gl in
  let ctac = cleartac (interp_clr (oclr, (fst gt, snd (interp gt gl)))) in
  if !fail then ctac gl else tclTHEN (tclMULT mult rwtac) ctac gl

(** Rewrite argument sequence *)

(* type ssrrwargs = ssrrwarg list *)

let pr_ssrrwargs _ _ _ rwargs = pr_list spc pr_rwarg rwargs

ARGUMENT EXTEND ssrrwargs TYPED AS ssrrwarg list PRINTED BY pr_ssrrwargs
  | [ "YouShouldNotTypeThis" ] -> [ anomaly "Grammar placeholder match" ]
END

let ssr_rw_syntax = Summary.ref ~name:"SSR:rewrite" true

let _ =
  Goptions.declare_bool_option
    { Goptions.optsync  = true;
      Goptions.optname  = "ssreflect rewrite";
      Goptions.optkey   = ["SsrRewrite"];
      Goptions.optread  = (fun _ -> !ssr_rw_syntax);
      Goptions.optdepr  = false;
      Goptions.optwrite = (fun b -> ssr_rw_syntax := b) }

let test_ssr_rw_syntax =
  let test strm  =
    if not !ssr_rw_syntax then raise Stream.Failure else
    if is_ssr_loaded () then () else
    match Compat.get_tok (Util.stream_nth 0 strm) with
    | Tok.KEYWORD key when List.mem key.[0] ['{'; '['; '/'] -> ()
    | _ -> raise Stream.Failure in
  Gram.Entry.of_parser "test_ssr_rw_syntax" test

GEXTEND Gram
  GLOBAL: ssrrwargs;
  ssrrwargs: [[ test_ssr_rw_syntax; a = LIST1 ssrrwarg -> a ]];
END

(** The "rewrite" tactic *)

let ssrrewritetac ist rwargs =
  tclTHENLIST (List.map (rwargtac ist) rwargs)

TACTIC EXTEND ssrrewrite
  | [ "rewrite" ssrrwargs(args) ssrclauses(clauses) ] ->
    [ Proofview.V82.tactic (tclCLAUSES ist (ssrrewritetac ist args) clauses) ]
END

(** The "unlock" tactic *)

let pr_unlockarg (occ, t) = pr_occ occ ++ pr_term t
let pr_ssrunlockarg _ _ _ = pr_unlockarg

ARGUMENT EXTEND ssrunlockarg TYPED AS ssrocc * ssrterm
  PRINTED BY pr_ssrunlockarg
  | [  "{" ssrocc(occ) "}" ssrterm(t) ] -> [ occ, t ]
  | [  ssrterm(t) ] -> [ None, t ]
END

let pr_ssrunlockargs _ _ _ args = pr_list spc pr_unlockarg args

ARGUMENT EXTEND ssrunlockargs TYPED AS ssrunlockarg list
  PRINTED BY pr_ssrunlockargs
  | [  ssrunlockarg_list(args) ] -> [ args ]
END

let unfoldtac occ ko t kt gl =
  let cl, c = pf_fill_occ_term gl occ (fst (strip_unfold_term t kt)) in
  let cl' = subst1 (pf_unfoldn [OnlyOccurrences [1], get_evalref c] gl c) cl in
  let f = if ko = None then Closure.betaiotazeta else Closure.betaiota in
  Proofview.V82.of_tactic
    (convert_concl (pf_reduce (Reductionops.clos_norm_flags f) gl cl')) gl

let unlocktac ist args gl =
  let utac (occ, gt) gl =
    unfoldtac occ occ (interp_term ist gl gt) (fst gt) gl in
  let locked, gl = pf_mkSsrConst "locked" gl in
  let key, gl = pf_mkSsrConst "master_key" gl in
  let ktacs = [
    (fun gl -> unfoldtac None None (project gl,locked) InParens gl); 
    simplest_newcase key ] in
  tclTHENLIST (List.map utac args @ ktacs) gl

TACTIC EXTEND ssrunlock
  | [ "unlock" ssrunlockargs(args) ssrclauses(clauses) ] ->
[  Proofview.V82.tactic (tclCLAUSES ist (unlocktac ist args) clauses) ]
END

(** 8. Forward chaining tactics (pose, set, have, suffice, wlog) *)

(** Defined identifier *)

type ssrfwdid = identifier

let pr_ssrfwdid _ _ _ id = pr_spc () ++ pr_id id

(* We use a primitive parser for the head identifier of forward *)
(* tactis to avoid syntactic conflicts with basic Coq tactics. *)
ARGUMENT EXTEND ssrfwdid TYPED AS ident PRINTED BY pr_ssrfwdid
  | [ "YouShouldNotTypeThis" ] -> [ anomaly "Grammar placeholder match" ]
END

let accept_ssrfwdid strm =
  match Compat.get_tok (stream_nth 0 strm) with
  | Tok.IDENT id -> accept_before_syms_or_any_id [":"; ":="; "("] strm
  | _ -> raise Stream.Failure


let test_ssrfwdid = Gram.Entry.of_parser "test_ssrfwdid" accept_ssrfwdid

GEXTEND Gram
  GLOBAL: ssrfwdid;
  ssrfwdid: [[ test_ssrfwdid; id = Prim.ident -> id ]];
  END



(** Definition value formatting *)

(* We use an intermediate structure to correctly render the binder list  *)
(* abbreviations. We use a list of hints to extract the binders and      *)
(* base term from a term, for the two first levels of representation of  *)
(* of constr terms.                                                      *)

type 'term ssrbind =
  | Bvar of name
  | Bdecl of name list * 'term
  | Bdef of name * 'term option * 'term
  | Bstruct of name
  | Bcast of 'term

let pr_binder prl = function
  | Bvar x ->
    pr_name x
  | Bdecl (xs, t) ->
    str "(" ++ pr_list pr_spc pr_name xs ++ str " : " ++ prl t ++ str ")"
  | Bdef (x, None, v) ->
    str "(" ++ pr_name x ++ str " := " ++ prl v ++ str ")"
  | Bdef (x, Some t, v) ->
    str "(" ++ pr_name x ++ str " : " ++ prl t ++
                            str " := " ++ prl v ++ str ")"
  | Bstruct x ->
    str "{struct " ++ pr_name x ++ str "}"
  | Bcast t ->
    str ": " ++ prl t

type 'term ssrbindval = 'term ssrbind list * 'term

type ssrbindfmt =
  | BFvar
  | BFdecl of int        (* #xs *)
  | BFcast               (* final cast *)
  | BFdef of bool        (* has cast? *)
  | BFrec of bool * bool (* has struct? * has cast? *)

let rec mkBstruct i = function
  | Bvar x :: b ->
    if i = 0 then [Bstruct x] else mkBstruct (i - 1) b
  | Bdecl (xs, _) :: b ->
    let i' = i - List.length xs in
    if i' < 0 then [Bstruct (List.nth xs i)] else mkBstruct i' b
  | _ :: b -> mkBstruct i b
  | [] -> []

let rec format_local_binders h0 bl0 = match h0, bl0 with
  | BFvar :: h, LocalRawAssum ([_, x], _,  _) :: bl ->
    Bvar x :: format_local_binders h bl
  | BFdecl _ :: h, LocalRawAssum (lxs, _, t) :: bl ->
    Bdecl (List.map snd lxs, t) :: format_local_binders h bl
  | BFdef false :: h, LocalRawDef ((_, x), v) :: bl ->
    Bdef (x, None, v) :: format_local_binders h bl
  | BFdef true :: h,
      LocalRawDef ((_, x), CCast (_, v, CastConv t)) :: bl ->
    Bdef (x, Some t, v) :: format_local_binders h bl
  | _ -> []
  
let rec format_constr_expr h0 c0 = match h0, c0 with
  | BFvar :: h, CLambdaN (_, [[_, x], _, _], c) ->
    let bs, c' = format_constr_expr h c in
    Bvar x :: bs, c'
  | BFdecl _:: h, CLambdaN (_, [lxs, _, t], c) ->
    let bs, c' = format_constr_expr h c in
    Bdecl (List.map snd lxs, t) :: bs, c'
  | BFdef false :: h, CLetIn(_, (_, x), v, c) ->
    let bs, c' = format_constr_expr h c in
    Bdef (x, None, v) :: bs, c'
  | BFdef true :: h, CLetIn(_, (_, x), CCast (_, v, CastConv t), c) ->
    let bs, c' = format_constr_expr h c in
    Bdef (x, Some t, v) :: bs, c'
  | [BFcast], CCast (_, c, CastConv t) ->
    [Bcast t], c
  | BFrec (has_str, has_cast) :: h, 
    CFix (_, _, [_, (Some locn, CStructRec), bl, t, c]) ->
    let bs = format_local_binders h bl in
    let bstr = if has_str then [Bstruct (Name (snd locn))] else [] in
    bs @ bstr @ (if has_cast then [Bcast t] else []), c 
  | BFrec (_, has_cast) :: h, CCoFix (_, _, [_, bl, t, c]) ->
    format_local_binders h bl @ (if has_cast then [Bcast t] else []), c
  | _, c ->
    [], c

let rec format_glob_decl h0 d0 = match h0, d0 with
  | BFvar :: h, (x, _, None, _) :: d ->
    Bvar x :: format_glob_decl h d
  | BFdecl 1 :: h,  (x, _, None, t) :: d ->
    Bdecl ([x], t) :: format_glob_decl h d
  | BFdecl n :: h, (x, _, None, t) :: d when n > 1 ->
    begin match format_glob_decl (BFdecl (n - 1) :: h) d with
    | Bdecl (xs, _) :: bs -> Bdecl (x :: xs, t) :: bs
    | bs -> Bdecl ([x], t) :: bs
    end
  | BFdef false :: h, (x, _, Some v, _)  :: d ->
    Bdef (x, None, v) :: format_glob_decl h d
  | BFdef true:: h, (x, _, Some (GCast (_, v, CastConv t)), _) :: d ->
    Bdef (x, Some t, v) :: format_glob_decl h d
  | _, (x, _, None, t) :: d ->
    Bdecl ([x], t) :: format_glob_decl [] d
  | _, (x, _, Some v, _) :: d ->
     Bdef (x, None, v) :: format_glob_decl [] d
  | _, [] -> []

let rec format_glob_constr h0 c0 = match h0, c0 with
  | BFvar :: h, GLambda (_, x, _, _, c) ->
    let bs, c' = format_glob_constr h c in
    Bvar x :: bs, c'
  | BFdecl 1 :: h,  GLambda (_, x, _, t, c) ->
    let bs, c' = format_glob_constr h c in
    Bdecl ([x], t) :: bs, c'
  | BFdecl n :: h,  GLambda (_, x, _, t, c) when n > 1 ->
    begin match format_glob_constr (BFdecl (n - 1) :: h) c with
    | Bdecl (xs, _) :: bs, c' -> Bdecl (x :: xs, t) :: bs, c'
    | _ -> [Bdecl ([x], t)], c
    end
  | BFdef false :: h, GLetIn(_, x, v, c) ->
    let bs, c' = format_glob_constr h c in
    Bdef (x, None, v) :: bs, c'
  | BFdef true :: h, GLetIn(_, x, GCast (_, v, CastConv t), c) ->
    let bs, c' = format_glob_constr h c in
    Bdef (x, Some t, v) :: bs, c'
  | [BFcast], GCast (_, c, CastConv t) ->
    [Bcast t], c
  | BFrec (has_str, has_cast) :: h, GRec (_, f, _, bl, t, c)
      when Array.length c = 1 ->
    let bs = format_glob_decl h bl.(0) in
    let bstr = match has_str, f with
    | true, GFix ([|Some i, GStructRec|], _) -> mkBstruct i bs
    | _ -> [] in
    bs @ bstr @ (if has_cast then [Bcast t.(0)] else []), c.(0)
  | _, c ->
    [], c

(** Forward chaining argument *)

(* There are three kinds of forward definitions:           *)
(*   - Hint: type only, cast to Type, may have proof hint. *)
(*   - Have: type option + value, no space before type     *)
(*   - Pose: binders + value, space before binders.        *)

type ssrfwdkind = FwdHint of string * bool | FwdHave | FwdPose

type ssrfwdfmt = ssrfwdkind * ssrbindfmt list

let pr_fwdkind = function
  | FwdHint (s,_) -> str (s ^ " ") | _ -> str " :=" ++ spc ()
let pr_fwdfmt (fk, _ : ssrfwdfmt) = pr_fwdkind fk

let wit_ssrfwdfmt = add_genarg "ssrfwdfmt" pr_fwdfmt

(* type ssrfwd = ssrfwdfmt * ssrterm *)

let mkFwdVal fk c = ((fk, []), mk_term NoFlag c)
let mkssrFwdVal fk c = ((fk, []), (c,None))

let mkFwdCast fk loc t c = ((fk, [BFcast]), mk_term NoFlag (CCast (loc, c, dC t)))
let mkssrFwdCast fk loc t c = ((fk, [BFcast]), (c, Some t))

let mkFwdHint s t =
  let loc = constr_loc t in
  mkFwdCast (FwdHint (s,false)) loc t (mkCHole loc)
let mkFwdHintNoTC s t =
  let loc = constr_loc t in
  mkFwdCast (FwdHint (s,true)) loc t (mkCHole loc)

let pr_gen_fwd prval prc prlc fk (bs, c) =
  let prc s = str s ++ spc () ++ prval prc prlc c in
  match fk, bs with
  | FwdHint (s,_), [Bcast t] -> str s ++ spc () ++ prlc t
  | FwdHint (s,_), _ ->  prc (s ^ "(* typeof *)")
  | FwdHave, [Bcast t] -> str ":" ++ spc () ++ prlc t ++ prc " :="
  | _, [] -> prc " :="
  | _, _ -> spc () ++ pr_list spc (pr_binder prlc) bs ++ prc " :="

let pr_fwd_guarded prval prval' = function
| (fk, h), (_, (_, Some c)) ->
  pr_gen_fwd prval pr_constr_expr prl_constr_expr fk (format_constr_expr h c)
| (fk, h), (_, (c, None)) ->
  pr_gen_fwd prval' pr_glob_constr prl_glob_constr fk (format_glob_constr h c)

let pr_unguarded prc prlc = prlc

let pr_fwd = pr_fwd_guarded pr_unguarded pr_unguarded
let pr_ssrfwd _ _ _ = pr_fwd
 
ARGUMENT EXTEND ssrfwd TYPED AS (ssrfwdfmt * ssrterm) PRINTED BY pr_ssrfwd
  | [ ":=" lconstr(c) ] -> [ mkFwdVal FwdPose c ]
  | [ ":" lconstr (t) ":=" lconstr(c) ] -> [ mkFwdCast FwdPose loc t c ]
END

(** Independent parsing for binders *)

(* The pose, pose fix, and pose cofix tactics use these internally to  *)
(* parse argument fragments.                                           *)

let pr_ssrbvar prc _ _ v = prc v

ARGUMENT EXTEND ssrbvar TYPED AS constr PRINTED BY pr_ssrbvar
| [ ident(id) ] -> [ mkCVar loc id ]
| [ "_" ] -> [ mkCHole loc ]
END

let bvar_lname = function
  | CRef (Ident (loc, id), _) -> loc, Name id
  | c -> constr_loc c, Anonymous

let pr_ssrbinder prc _ _ (_, c) = prc c

ARGUMENT EXTEND ssrbinder TYPED AS ssrfwdfmt * constr PRINTED BY pr_ssrbinder
 | [ ssrbvar(bv) ] ->
   [ let xloc, _ as x = bvar_lname bv in
     (FwdPose, [BFvar]),
     CLambdaN (loc,[[x],Default Explicit,mkCHole xloc],mkCHole loc) ]
 | [ "(" ssrbvar(bv) ")" ] ->
   [ let xloc, _ as x = bvar_lname bv in
     (FwdPose, [BFvar]),
     CLambdaN (loc,[[x],Default Explicit,mkCHole xloc],mkCHole loc) ]
 | [ "(" ssrbvar(bv) ":" lconstr(t) ")" ] ->
   [ let x = bvar_lname bv in
     (FwdPose, [BFdecl 1]),
     CLambdaN (loc, [[x], Default Explicit, t], mkCHole loc) ]
 | [ "(" ssrbvar(bv) ne_ssrbvar_list(bvs) ":" lconstr(t) ")" ] ->
   [ let xs = List.map bvar_lname (bv :: bvs) in
     let n = List.length xs in
     (FwdPose, [BFdecl n]),
     CLambdaN (loc, [xs, Default Explicit, t], mkCHole loc) ]
 | [ "(" ssrbvar(id) ":" lconstr(t) ":=" lconstr(v) ")" ] ->
   [ let loc' = Loc.join_loc (constr_loc t) (constr_loc v) in
     let v' = CCast (loc', v, dC t) in
     (FwdPose,[BFdef true]), CLetIn (loc,bvar_lname id, v',mkCHole loc) ]
 | [ "(" ssrbvar(id) ":=" lconstr(v) ")" ] ->
   [ (FwdPose,[BFdef false]), CLetIn (loc,bvar_lname id, v,mkCHole loc) ]
END

GEXTEND Gram
  GLOBAL: ssrbinder;
  ssrbinder: [
  [  ["of" | "&"]; c = operconstr LEVEL "99" ->
     let loc = !@loc in
     (FwdPose, [BFvar]),
     CLambdaN (loc,[[loc,Anonymous],Default Explicit,c],mkCHole loc) ]
  ];
END

let rec binders_fmts = function
  | ((_, h), _) :: bs -> h @ binders_fmts bs
  | _ -> []

let push_binders c2 bs =
  let loc2 = constr_loc c2 in let mkloc loc1 = Loc.join_loc loc1 loc2 in
  let rec loop ty c = function
  | (_, CLambdaN (loc1, b, _)) :: bs when ty ->
      CProdN (mkloc loc1, b, loop ty c bs)
  | (_, CLambdaN (loc1, b, _)) :: bs ->
      CLambdaN (mkloc loc1, b, loop ty c bs)
  | (_, CLetIn (loc1, x, v, _)) :: bs ->
      CLetIn (mkloc loc1, x, v, loop ty c bs)
  | [] -> c
  | _ -> anomaly "binder not a lambda nor a let in" in
  match c2 with
  | CCast (x, ct, CastConv cty) ->
      (CCast (x, loop false ct bs, CastConv (loop true cty bs)))
  | ct -> loop false ct bs

let rec fix_binders = function
  | (_, CLambdaN (_, [xs, _, t], _)) :: bs ->
      LocalRawAssum (xs, Default Explicit, t) :: fix_binders bs
  | (_, CLetIn (_, x, v, _)) :: bs ->
    LocalRawDef (x, v) :: fix_binders bs
  | _ -> []

let pr_ssrstruct _ _ _ = function
  | Some id -> str "{struct " ++ pr_id id ++ str "}"
  | None -> mt ()

ARGUMENT EXTEND ssrstruct TYPED AS ident option PRINTED BY pr_ssrstruct
| [ "{" "struct" ident(id) "}" ] -> [ Some id ]
| [ ] -> [ None ]
END

(** The "pose" tactic *)

(* The plain pose form. *)

let bind_fwd bs = function
  | (fk, h), (ck, (rc, Some c)) ->
    (fk,binders_fmts bs @ h), (ck,(rc,Some (push_binders c bs)))
  | fwd -> fwd

ARGUMENT EXTEND ssrposefwd TYPED AS ssrfwd PRINTED BY pr_ssrfwd
  | [ ssrbinder_list(bs) ssrfwd(fwd) ] -> [ bind_fwd bs fwd ]
END

(* The pose fix form. *)

let pr_ssrfixfwd _ _ _ (id, fwd) = str " fix " ++ pr_id id ++ pr_fwd fwd

let bvar_locid = function
  | CRef (Ident (loc, id), _) -> loc, id
  | _ -> Errors.error "Missing identifier after \"(co)fix\""


ARGUMENT EXTEND ssrfixfwd TYPED AS ident * ssrfwd PRINTED BY pr_ssrfixfwd
  | [ "fix" ssrbvar(bv) ssrbinder_list(bs) ssrstruct(sid) ssrfwd(fwd) ] ->
    [ let (_, id) as lid = bvar_locid bv in
      let (fk, h), (ck, (rc, oc)) = fwd in
      let c = Option.get oc in
      let has_cast, t', c' = match format_constr_expr h c with
      | [Bcast t'], c' -> true, t', c'
      | _ -> false, mkCHole (constr_loc c), c in
      let lb = fix_binders bs in
      let has_struct, i =
        let rec loop = function
          (l', Name id') :: _ when Option.equal Id.equal sid (Some id') -> true, (l', id')
          | [l', Name id'] when sid = None -> false, (l', id')
          | _ :: bn -> loop bn
          | [] -> Errors.error "Bad structural argument" in
        loop (names_of_local_assums lb) in
      let h' = BFrec (has_struct, has_cast) :: binders_fmts bs in
      let fix = CFix (loc, lid, [lid, (Some i, CStructRec), lb, t', c']) in
      id, ((fk, h'), (ck, (rc, Some fix))) ]
END


(* The pose cofix form. *)

let pr_ssrcofixfwd _ _ _ (id, fwd) = str " cofix " ++ pr_id id ++ pr_fwd fwd

ARGUMENT EXTEND ssrcofixfwd TYPED AS ssrfixfwd PRINTED BY pr_ssrcofixfwd
  | [ "cofix" ssrbvar(bv) ssrbinder_list(bs) ssrfwd(fwd) ] ->
    [ let _, id as lid = bvar_locid bv in
      let (fk, h), (ck, (rc, oc)) = fwd in
      let c = Option.get oc in
      let has_cast, t', c' = match format_constr_expr h c with
      | [Bcast t'], c' -> true, t', c'
      | _ -> false, mkCHole (constr_loc c), c in
      let h' = BFrec (false, has_cast) :: binders_fmts bs in
      let cofix = CCoFix (loc, lid, [lid, fix_binders bs, t', c']) in
      id, ((fk, h'), (ck, (rc, Some cofix)))
    ]
END

let ssrposetac ist (id, (_, t)) gl =
  let sigma, t, ucst, _ = pf_abs_ssrterm ist gl t in
  posetac id t (pf_merge_uc ucst gl)


let prof_ssrposetac = mk_profiler "ssrposetac";;
let ssrposetac arg gl = prof_ssrposetac.profile (ssrposetac arg) gl;;
  
TACTIC EXTEND ssrpose
| [ "pose" ssrfixfwd(ffwd) ] -> [ Proofview.V82.tactic (ssrposetac ist ffwd) ]
| [ "pose" ssrcofixfwd(ffwd) ] -> [ Proofview.V82.tactic (ssrposetac ist ffwd) ]
| [ "pose" ssrfwdid(id) ssrposefwd(fwd) ] -> [ Proofview.V82.tactic (ssrposetac ist (id, fwd)) ]
END

(** The "set" tactic *)

(* type ssrsetfwd = ssrfwd * ssrdocc *)

let guard_setrhs s i = s.[i] = '{'

let pr_setrhs occ prc prlc c =
  if occ = nodocc then pr_guarded guard_setrhs prlc c else pr_docc occ ++ prc c

let pr_fwd_guarded prval prval' = function
| (fk, h), (_, (_, Some c)) ->
  pr_gen_fwd prval pr_constr_expr prl_constr_expr fk (format_constr_expr h c)
| (fk, h), (_, (c, None)) ->
  pr_gen_fwd prval' pr_glob_constr prl_glob_constr fk (format_glob_constr h c)

(* This does not print the type, it should be fixed... *)
let pr_ssrsetfwd _ _ _ (((fk,_),(t,_)), docc) =
  pr_gen_fwd (fun _ _ -> pr_cpattern)
    (fun _ -> mt()) (fun _ -> mt()) fk ([Bcast ()],t)

ARGUMENT EXTEND ssrsetfwd
TYPED AS (ssrfwdfmt * (lcpattern * ssrterm option)) * ssrdocc
PRINTED BY pr_ssrsetfwd
| [ ":" lconstr(t) ":=" "{" ssrocc(occ) "}" cpattern(c) ] ->
  [ mkssrFwdCast FwdPose loc (mk_lterm t) c, mkocc occ ]
| [ ":" lconstr(t) ":=" lcpattern(c) ] ->
  [ mkssrFwdCast FwdPose loc (mk_lterm t) c, nodocc ]
| [ ":=" "{" ssrocc(occ) "}" cpattern(c) ] ->
  [ mkssrFwdVal FwdPose c, mkocc occ ]
| [ ":=" lcpattern(c) ] -> [ mkssrFwdVal FwdPose c, nodocc ]
END

let ssrsettac ist id ((_, (pat, pty)), (_, occ)) gl =
  let pat = interp_cpattern ist gl pat (Option.map snd pty) in
  let cl, sigma, env = pf_concl gl, project gl, pf_env gl in
  let (c, ucst), cl = 
    try fill_occ_pattern ~raise_NoMatch:true env sigma cl pat occ 1
    with NoMatch -> redex_of_pattern ~resolve_typeclasses:true env pat, cl in
  if occur_existential c then errorstrm(str"The pattern"++spc()++
    pr_constr_pat c++spc()++str"did not match and has holes."++spc()++
    str"Did you mean pose?") else
  let c, (gl, cty) =  match kind_of_term c with
  | Cast(t, DEFAULTcast, ty) -> t, (gl, ty)
  | _ -> c, pf_type_of gl c in
  let cl' = mkLetIn (Name id, c, cty, cl) in
  let gl = pf_merge_uc ucst gl in
  tclTHEN (Proofview.V82.of_tactic (convert_concl cl')) (introid id) gl

TACTIC EXTEND ssrset
| [ "set" ssrfwdid(id) ssrsetfwd(fwd) ssrclauses(clauses) ] ->
  [ Proofview.V82.tactic (tclCLAUSES ist (ssrsettac ist id fwd) clauses) ]
END

(** The "have" tactic *)

(* type ssrhavefwd = ssrfwd * ssrhint *)

let pr_ssrhavefwd _ _ prt (fwd, hint) = pr_fwd fwd ++ pr_hint prt hint

ARGUMENT EXTEND ssrhavefwd TYPED AS ssrfwd * ssrhint PRINTED BY pr_ssrhavefwd
| [ ":" lconstr(t) ssrhint(hint) ] -> [ mkFwdHint ":" t, hint ]
| [ ":" lconstr(t) ":=" lconstr(c) ] -> [ mkFwdCast FwdHave loc t c, nohint ]
| [ ":" lconstr(t) ":=" ] -> [ mkFwdHintNoTC ":" t, nohint ]
| [ ":=" lconstr(c) ] -> [ mkFwdVal FwdHave c, nohint ]
END

let intro_id_to_binder = List.map (function 
  | IpatId id ->
      let xloc, _ as x = bvar_lname (mkCVar dummy_loc id) in
      (FwdPose, [BFvar]),
        CLambdaN (dummy_loc, [[x], Default Explicit, mkCHole xloc],
          mkCHole dummy_loc)
  | _ -> anomaly "non-id accepted as binder")

let binder_to_intro_id = List.map (function
  | (FwdPose, [BFvar]), CLambdaN (_,[ids,_,_],_)
  | (FwdPose, [BFdecl _]), CLambdaN (_,[ids,_,_],_) ->
      List.map (function (_, Name id) -> IpatId id | _ -> IpatAnon) ids
  | (FwdPose, [BFdef _]), CLetIn (_,(_,Name id),_,_) -> [IpatId id]
  | (FwdPose, [BFdef _]), CLetIn (_,(_,Anonymous),_,_) -> [IpatAnon]
  | _ -> anomaly "ssrbinder is not a binder")

let pr_ssrhavefwdwbinders _ _ prt (tr,((hpats, (fwd, hint)))) =
  pr_hpats hpats ++ pr_fwd fwd ++ pr_hint prt hint

ARGUMENT EXTEND ssrhavefwdwbinders
  TYPED AS bool * (ssrhpats * (ssrfwd * ssrhint))
  PRINTED BY pr_ssrhavefwdwbinders
| [ ssrhpats_wtransp(trpats) ssrbinder_list(bs) ssrhavefwd(fwd) ] ->
  [ let tr, pats = trpats in
    let ((clr, pats), binders), simpl = pats in
    let allbs = intro_id_to_binder binders @ bs in
    let allbinders = binders @ List.flatten (binder_to_intro_id bs) in
    let hint = bind_fwd allbs (fst fwd), snd fwd in
    tr, ((((clr, pats), allbinders), simpl), hint) ]
END

(* Tactic. *)

let is_Evar_or_CastedMeta x =
  isEvar_or_Meta x ||
  (isCast x && isEvar_or_Meta (pi1 (destCast x)))

let occur_existential_or_casted_meta c =
  let rec occrec c = match kind_of_term c with
    | Evar _ -> raise Not_found
    | Cast (m,_,_) when isMeta m -> raise Not_found
    | _ -> iter_constr occrec c
  in try occrec c; false with Not_found -> true

let examine_abstract id gl =
  let gl, tid = pf_type_of gl id in
  let abstract, gl = pf_mkSsrConst "abstract" gl in
  if not (isApp tid) || not (Term.eq_constr (fst(destApp tid)) abstract) then
    errorstrm(strbrk"not an abstract constant: "++pr_constr id);
  let _, args_id = destApp tid in
  if Array.length args_id <> 3 then
    errorstrm(strbrk"not a proper abstract constant: "++pr_constr id);
  if not (is_Evar_or_CastedMeta args_id.(2)) then
    errorstrm(strbrk"abstract constant "++pr_constr id++str" already used");
  tid, args_id

let pf_find_abstract_proof check_lock gl abstract_n = 
  let fire gl t = Reductionops.nf_evar (project gl) t in
  let abstract, gl = pf_mkSsrConst "abstract" gl in
  let l = Evd.fold_undefined (fun e ei l ->
    match kind_of_term ei.Evd.evar_concl with
    | App(hd, [|ty; n; lock|])
      when (not check_lock || 
                 (occur_existential_or_casted_meta (fire gl ty) &&
                  is_Evar_or_CastedMeta (fire gl lock))) &&
      Term.eq_constr hd abstract && Term.eq_constr n abstract_n -> e::l
    | _ -> l) (project gl) [] in
  match l with
  | [e] -> e
  | _ -> errorstrm(strbrk"abstract constant "++pr_constr abstract_n++
           strbrk" not found in the evar map exactly once. "++
           strbrk"Did you tamper with it?")

let unfold cl =
  let module R = Reductionops in let module F = Closure.RedFlags in
  reduct_in_concl (R.clos_norm_flags (F.mkflags
    (List.map (fun c -> F.fCONST (fst (destConst c))) cl @ [F.fBETA; F.fIOTA])))

let havegentac ist t gl =
  let sigma, c, ucst, _ = pf_abs_ssrterm ist gl t in
  let gl = pf_merge_uc ucst gl in
  let gl, cty = pf_type_of gl c in
  apply_type (mkArrow cty (pf_concl gl)) [c] gl

let havetac ist
  (transp,((((clr, pats), binders), simpl), (((fk, _), t), hint)))
  suff namefst gl 
=
 let concl = pf_concl gl in
 let skols, pats =
   List.partition (function IpatNewHidden _ -> true | _ -> false) pats in
 let itac_mkabs = introstac ~ist skols in
 let itac_c = introstac ~ist (IpatSimpl(clr,Nop) :: pats) in
 let itac, id, clr = introstac ~ist pats, tclIDTAC, cleartac clr in
 let binderstac n =
   let rec aux = function 0 -> [] | n -> IpatAnon :: aux (n-1) in
   tclTHEN (if binders <> [] then introstac ~ist (aux n) else tclIDTAC)
     (introstac ~ist binders) in
 let simpltac = introstac ~ist simpl in
 let fixtc =
   not !ssrhaveNOtcresolution &&
   match fk with FwdHint(_,true) -> false | _ -> true in
 let hint = hinttac ist true hint in
 let cuttac t gl =
   if transp then
     let have_let, gl = pf_mkSsrConst "ssr_have_let" gl in
     let step = mkApp (have_let, [|concl;t|]) in
     let gl, _ = pf_e_type_of gl step in
     applyn ~with_evars:true ~with_shelve:false 2 step gl
   else basecuttac "ssr_have" t gl in
 (* Introduce now abstract constants, so that everything sees them *)
 let abstract_key, gl = pf_mkSsrConst "abstract_key" gl in
 let unlock_abs (idty,args_id) gl =
    let gl, _ = pf_e_type_of gl idty in
    pf_unify_HO gl args_id.(2) abstract_key in
 tclTHENFIRST itac_mkabs (fun gl ->
  let mkt t = mk_term NoFlag t in
  let mkl t = (NoFlag, (t, None)) in
  let interp gl rtc t = pf_abs_ssrterm ~resolve_typeclasses:rtc ist gl t in
  let interp_ty gl rtc t =
    let a,b,_,u = pf_interp_ty ~resolve_typeclasses:rtc ist gl t in a,b,u in
  let ct, cty, hole, loc = match t with
    | _, (_, Some (CCast (loc, ct, CastConv cty))) ->
      mkt ct, mkt cty, mkt (mkCHole dummy_loc), loc
    | _, (_, Some ct) ->
      mkt ct, mkt (mkCHole dummy_loc), mkt (mkCHole dummy_loc), dummy_loc
    | _, (GCast (loc, ct, CastConv cty), None) ->
      mkl ct, mkl cty, mkl mkRHole, loc
    | _, (t, None) -> mkl t, mkl mkRHole, mkl mkRHole, dummy_loc in
  let gl, cut, sol, itac1, itac2 =
   match fk, namefst, suff with
   | FwdHave, true, true ->
     errorstrm (str"Suff have does not accept a proof term")
   | FwdHave, false, true ->
     let cty = combineCG cty hole (mkCArrow loc) mkRArrow in
     let _,t,uc,_ = interp gl false (combineCG ct cty (mkCCast loc) mkRCast) in
     let gl = pf_merge_uc uc gl in
     let gl, ty = pf_type_of gl t in
     let ctx, _ = decompose_prod_n 1 ty in
     let assert_is_conv gl =
       try Proofview.V82.of_tactic (convert_concl (compose_prod ctx concl)) gl
       with _ -> errorstrm (str "Given proof term is not of type " ++
         pr_constr (mkArrow (mkVar (id_of_string "_")) concl)) in
     gl, ty, tclTHEN assert_is_conv (Proofview.V82.of_tactic (apply t)), id, itac_c
   | FwdHave, false, false ->
     let skols = List.flatten (List.map (function
       | IpatNewHidden ids -> ids
       | _ -> assert false) skols) in
     let skols_args =
       List.map (fun id -> examine_abstract (mkVar id) gl) skols in
     let gl = List.fold_right unlock_abs skols_args gl in
     let sigma, t, uc, n_evars =
       interp gl false (combineCG ct cty (mkCCast loc) mkRCast) in
     if skols <> [] && n_evars <> 0 then
       Errors.error ("Automatic generalization of unresolved implicit "^
                     "arguments together with abstract variables is "^
                     "not supported");
     let gl = re_sig (sig_it gl) (Evd.merge_universe_context sigma uc) in
     let gs =
       List.map (fun (_,a) ->
         pf_find_abstract_proof false gl a.(1)) skols_args in
     let tacopen_skols gl =
        let stuff, g = Refiner.unpackage gl in
        Refiner.repackage stuff (gs @ [g]) in
     let gl, ty = pf_e_type_of gl t in
     gl, ty, Proofview.V82.of_tactic (apply t), id,
       tclTHEN (tclTHEN itac_c simpltac)
         (tclTHEN tacopen_skols (fun gl ->
            let abstract, gl = pf_mkSsrConst "abstract" gl in
            unfold [abstract; abstract_key] gl))
   | _,true,true  ->
     let _, ty, uc = interp_ty gl fixtc cty in let gl = pf_merge_uc uc gl in
     gl, mkArrow ty concl, hint, itac, clr
   | _,false,true ->
     let _, ty, uc = interp_ty gl fixtc cty in let gl = pf_merge_uc uc gl in
     gl, mkArrow ty concl, hint, id, itac_c
   | _, false, false -> 
     let n, cty, uc = interp_ty gl fixtc cty in let gl = pf_merge_uc uc gl in
     gl, cty, tclTHEN (binderstac n) hint, id, tclTHEN itac_c simpltac
   | _, true, false -> assert false in
  tclTHENS (cuttac cut) [ tclTHEN sol itac1; itac2 ] gl)
 gl
;;

(* to extend the abstract value one needs:
  Utility lemma to partially instantiate an abstract constant type.
  Lemma use_abstract T n l (x : abstract T n l) : T.
  Proof. by case: l x. Qed.
*)
let ssrabstract ist gens (*last*) gl =
  let main _ (_,cid) ist gl =
(*
    let proj1, proj2, prod =
      let pdata = build_prod () in
      pdata.Coqlib.proj1, pdata.Coqlib.proj2, pdata.Coqlib.typ in
*)
    let concl, env = pf_concl gl, pf_env gl in
    let fire gl t = Reductionops.nf_evar (project gl) t in
    let abstract, gl = pf_mkSsrConst "abstract" gl in
    let abstract_key, gl = pf_mkSsrConst "abstract_key" gl in
    let cid_interpreted = interp_cpattern ist gl cid None in
    let id = mkVar (Option.get (id_of_pattern cid_interpreted)) in
    let idty, args_id = examine_abstract id gl in
    let abstract_n = args_id.(1) in
    let abstract_proof = pf_find_abstract_proof true gl abstract_n in 
    let gl, proof =
      let pf_unify_HO gl a b =
        try pf_unify_HO gl a b
        with _ -> errorstrm(strbrk"The abstract variable "++pr_constr id++
          strbrk" cannot abstract this goal.  Did you generalize it?") in
      let rec find_hole p t =
        match kind_of_term t with
        | Evar _ (*when last*) -> pf_unify_HO gl concl t, p
        | Meta _ (*when last*) -> pf_unify_HO gl concl t, p
        | Cast(m,_,_) when isEvar_or_Meta m (*when last*) -> pf_unify_HO gl concl t, p
(*
        | Evar _ ->
            let sigma, it = project gl, sig_it gl in
            let sigma, ty = Evarutil.new_type_evar sigma env in
            let gl = re_sig it sigma in
            let p = mkApp (proj2,[|ty;concl;p|]) in
            let concl = mkApp(prod,[|ty; concl|]) in
            pf_unify_HO gl concl t, p
        | App(hd, [|left; right|]) when Term.eq_constr hd prod ->
            find_hole (mkApp (proj1,[|left;right;p|])) left
*)
        | _ -> errorstrm(strbrk"abstract constant "++pr_constr abstract_n++
               strbrk" has an unexpected shape. Did you tamper with it?")
      in
        find_hole
          ((*if last then*) id
          (*else mkApp(mkSsrConst "use_abstract",Array.append args_id [|id|])*))
          (fire gl args_id.(0)) in
    let gl = (*if last then*) pf_unify_HO gl abstract_key args_id.(2) (*else gl*) in
    let gl, _ = pf_e_type_of gl idty in
    let proof = fire gl proof in
(*     if last then *)
      let tacopen gl =
        let stuff, g = Refiner.unpackage gl in
        Refiner.repackage stuff [ g; abstract_proof ] in
      tclTHENS tacopen [tclSOLVE [Proofview.V82.of_tactic (apply proof)];unfold[abstract;abstract_key]] gl
(* else apply proof gl *)
  in
  let introback ist (gens, _) =
    introstac ~ist
      (List.map (fun (_,cp) -> match id_of_pattern (interp_cpattern ist gl cp None) with
        | None -> IpatAnon
        | Some id -> IpatId id)
        (List.tl (List.hd gens))) in
  tclTHEN (with_dgens gens main ist) (introback ist gens) gl

(* The standard TACTIC EXTEND does not work for abstract *)
GEXTEND Gram
  GLOBAL: tactic_expr;
  tactic_expr: LEVEL "3"
    [ RIGHTA [ IDENT "abstract"; gens = ssrdgens ->
               ssrtac_expr !@loc "abstract"
                [Genarg.in_gen (Genarg.rawwit wit_ssrdgens) gens] ]];
END
TACTIC EXTEND ssrabstract
| [ "abstract" ssrdgens(gens) ] -> [
    if List.length (fst gens) <> 1 then
      errorstrm (str"dependents switches '/' not allowed here");
    Proofview.V82.tactic (ssrabstract ist gens) ]
END

let prof_havetac = mk_profiler "havetac";;
let havetac arg a b gl = prof_havetac.profile (havetac arg a b) gl;;

TACTIC EXTEND ssrhave
| [ "have" ssrhavefwdwbinders(fwd) ] ->
  [ Proofview.V82.tactic (havetac ist fwd false false) ]
END

TACTIC EXTEND ssrhavesuff
| [ "have" "suff" ssrhpats_nobs(pats) ssrhavefwd(fwd) ] ->
  [ Proofview.V82.tactic (havetac ist (false,(pats,fwd)) true false) ]
END

TACTIC EXTEND ssrhavesuffices
| [ "have" "suffices" ssrhpats_nobs(pats) ssrhavefwd(fwd) ] ->
  [ Proofview.V82.tactic (havetac ist (false,(pats,fwd)) true false) ]
END

TACTIC EXTEND ssrsuffhave
| [ "suff" "have" ssrhpats_nobs(pats) ssrhavefwd(fwd) ] ->
  [ Proofview.V82.tactic (havetac ist (false,(pats,fwd)) true true) ]
END

TACTIC EXTEND ssrsufficeshave
| [ "suffices" "have" ssrhpats_nobs(pats) ssrhavefwd(fwd) ] ->
  [ Proofview.V82.tactic (havetac ist (false,(pats,fwd)) true true) ]
END

(** The "suffice" tactic *)

let pr_ssrsufffwdwbinders _ _ prt (hpats, (fwd, hint)) =
  pr_hpats hpats ++ pr_fwd fwd ++ pr_hint prt hint

ARGUMENT EXTEND ssrsufffwd
  TYPED AS ssrhpats * (ssrfwd * ssrhint) PRINTED BY pr_ssrsufffwdwbinders
| [ ssrhpats(pats) ssrbinder_list(bs)  ":" lconstr(t) ssrhint(hint) ] ->
  [ let ((clr, pats), binders), simpl = pats in
    let allbs = intro_id_to_binder binders @ bs in
    let allbinders = binders @ List.flatten (binder_to_intro_id bs) in
    let fwd = mkFwdHint ":" t in
    (((clr, pats), allbinders), simpl), (bind_fwd allbs fwd, hint) ]
END

let sufftac ist ((((clr, pats),binders),simpl), ((_, c), hint)) =
  let htac = tclTHEN (introstac ~ist pats) (hinttac ist true hint) in
  let c = match c with
  | (a, (b, Some (CCast (_, _, CastConv cty)))) -> a, (b, Some cty)
  | (a, (GCast (_, _, CastConv cty), None)) -> a, (cty, None)
  | _ -> anomaly "suff: ssr cast hole deleted by typecheck" in
  let ctac gl =
    let _,ty,_,uc = pf_interp_ty ist gl c in let gl = pf_merge_uc uc gl in
    basecuttac "ssr_suff" ty gl in
  tclTHENS ctac [htac; tclTHEN (cleartac clr) (introstac ~ist (binders@simpl))]

TACTIC EXTEND ssrsuff
| [ "suff" ssrsufffwd(fwd) ] -> [ Proofview.V82.tactic (sufftac ist fwd) ]
END

TACTIC EXTEND ssrsuffices
| [ "suffices" ssrsufffwd(fwd) ] -> [ Proofview.V82.tactic (sufftac ist fwd) ]
END

(** The "wlog" (Without Loss Of Generality) tactic *)

(* type ssrwlogfwd = ssrwgen list * ssrfwd *)

let pr_ssrwlogfwd _ _ _ (gens, t) =
  str ":" ++ pr_list mt pr_wgen gens ++ spc() ++ pr_fwd t

ARGUMENT EXTEND ssrwlogfwd TYPED AS ssrwgen list * ssrfwd
                         PRINTED BY pr_ssrwlogfwd
| [ ":" ssrwgen_list(gens) "/" lconstr(t) ] -> [ gens, mkFwdHint "/" t]
END

let destProd_or_LetIn c =
  match kind_of_term c with
  | Prod (n,ty,c) -> (n,None,ty), c
  | LetIn (n,bo,ty,c) -> (n,Some bo,ty), c
  | _ -> raise DestKO
        
let wlogtac ist (((clr0, pats),_),_) (gens, ((_, ct))) hint suff ghave gl =
  let mkabs gen = abs_wgen false ist (fun x -> x) gen in
  let mkclr gen clrs = clr_of_wgen gen clrs in
  let mkpats = function
  | _, Some ((x, _), _) -> fun pats -> IpatId (hoi_id x) :: pats
  | _ -> fun x -> x in
  let ct = match ct with
  | (a, (b, Some (CCast (_, _, CastConv cty)))) -> a, (b, Some cty)
  | (a, (GCast (_, _, CastConv cty), None)) -> a, (cty, None)
  | _ -> anomaly "wlog: ssr cast hole deleted by typecheck" in
  let cut_implies_goal = not (suff || ghave <> `NoGen) in
  let c, args, ct, gl =
    let gens = List.filter (function _, Some _ -> true | _ -> false) gens in
    let concl = pf_concl gl in
    let c = mkProp in
    let c = if cut_implies_goal then mkArrow c concl else c in
    let gl, args, c = List.fold_right mkabs gens (gl,[],c) in
    let env, _ =
      List.fold_left (fun (env, c) _ ->
        let rd, c = destProd_or_LetIn c in
        Environ.push_rel rd env, c) (pf_env gl, c) gens in
    let sigma = project gl in
    let sigma = Sigma.Unsafe.of_evar_map sigma in
    let Sigma (ev, sigma, _) = Evarutil.new_evar env sigma Term.mkProp in
    let sigma = Sigma.to_evar_map sigma in
    let k, _ = Term.destEvar ev in
    let fake_gl = {Evd.it = k; Evd.sigma = sigma} in
    let _, ct, _, uc = pf_interp_ty ist fake_gl ct in
    let rec var2rel c g s = match kind_of_term c, g with
      | Prod(Anonymous,_,c), [] -> mkProd(Anonymous, Vars.subst_vars s ct, c)
      | Sort _, [] -> Vars.subst_vars s ct
      | LetIn(Name id as n,b,ty,c), _::g -> mkLetIn (n,b,ty,var2rel c g (id::s))
      | Prod(Name id as n,ty,c), _::g -> mkProd (n,ty,var2rel c g (id::s))
      | _ -> Errors.anomaly(str"SSR: wlog: var2rel: " ++ pr_constr c) in
    let c = var2rel c gens [] in
    let rec pired c = function
      | [] -> c
      | t::ts as args -> match kind_of_term c with
         | Prod(_,_,c) -> pired (subst1 t c) ts
         | LetIn(id,b,ty,c) -> mkLetIn (id,b,ty,pired c args)
         | _ -> Errors.anomaly(str"SSR: wlog: pired: " ++ pr_constr c) in
    c, args, pired c args, pf_merge_uc uc gl in
  let tacipat pats = introstac ~ist pats in
  let tacigens = 
    tclTHEN
      (tclTHENLIST(List.rev(List.fold_right mkclr gens [cleartac clr0])))
      (introstac ~ist (List.fold_right mkpats gens [])) in
  let hinttac = hinttac ist true hint in
  let cut_kind, fst_goal_tac, snd_goal_tac =
    match suff, ghave with
    | true, `NoGen -> "ssr_wlog", tclTHEN hinttac (tacipat pats), tacigens
    | false, `NoGen -> "ssr_wlog", hinttac, tclTHEN tacigens (tacipat pats)
    | true, `Gen _ -> assert false
    | false, `Gen id ->
      if gens = [] then errorstrm(str"gen have requires some generalizations");
      let clear0 = cleartac clr0 in
      let id, name_general_hyp, cleanup, pats = match id, pats with
      | None, (IpatId id as ip)::pats -> Some id, tacipat [ip], clear0, pats
      | None, _ -> None, tclIDTAC, clear0, pats
      | Some (Some id),_ -> Some id, introid id, clear0, pats
      | Some _,_ ->
          let id = mk_anon_id "tmp" gl in
          Some id, introid id, tclTHEN clear0 (clear [id]), pats in
      let tac_specialize = match id with
      | None -> tclIDTAC
      | Some id ->
        if pats = [] then tclIDTAC else
        let args = Array.of_list args in
        pp(lazy(str"specialized="++pr_constr (mkApp (mkVar id,args))));
        pp(lazy(str"specialized_ty="++pr_constr ct));
        tclTHENS (basecuttac "ssr_have" ct)
          [Proofview.V82.of_tactic (apply (mkApp (mkVar id,args))); tclIDTAC] in
      "ssr_have",
      (if hint = nohint then tacigens else hinttac),
      tclTHENLIST [name_general_hyp; tac_specialize; tacipat pats; cleanup]
  in
  tclTHENS (basecuttac cut_kind c) [fst_goal_tac; snd_goal_tac] gl

TACTIC EXTEND ssrwlog
| [ "wlog" ssrhpats_nobs(pats) ssrwlogfwd(fwd) ssrhint(hint) ] ->
  [ Proofview.V82.tactic (wlogtac ist pats fwd hint false `NoGen) ]
END

TACTIC EXTEND ssrwlogs
| [ "wlog" "suff" ssrhpats_nobs(pats) ssrwlogfwd(fwd) ssrhint(hint) ] ->
  [ Proofview.V82.tactic (wlogtac ist pats fwd hint true `NoGen) ]
END

TACTIC EXTEND ssrwlogss
| [ "wlog" "suffices" ssrhpats_nobs(pats) ssrwlogfwd(fwd) ssrhint(hint) ]->
  [ Proofview.V82.tactic (wlogtac ist pats fwd hint true `NoGen) ]
END

TACTIC EXTEND ssrwithoutloss
| [ "without" "loss" ssrhpats_nobs(pats) ssrwlogfwd(fwd) ssrhint(hint) ] ->
  [ Proofview.V82.tactic (wlogtac ist pats fwd hint false `NoGen) ]
END

TACTIC EXTEND ssrwithoutlosss
| [ "without" "loss" "suff" 
    ssrhpats_nobs(pats) ssrwlogfwd(fwd) ssrhint(hint) ] ->
  [ Proofview.V82.tactic (wlogtac ist pats fwd hint true `NoGen) ]
END

TACTIC EXTEND ssrwithoutlossss
| [ "without" "loss" "suffices" 
    ssrhpats_nobs(pats) ssrwlogfwd(fwd) ssrhint(hint) ]->
  [ Proofview.V82.tactic (wlogtac ist pats fwd hint true `NoGen) ]
END

(* Generally have *)
let pr_idcomma _ _ _ = function
  | None -> mt()
  | Some None -> str"_, "
  | Some (Some id) -> pr_id id ++ str", "

ARGUMENT EXTEND ssr_idcomma TYPED AS ident option option PRINTED BY pr_idcomma
  | [ ] -> [ None ]
END

let accept_idcomma strm =
  match Compat.get_tok (stream_nth 0 strm) with
  | Tok.IDENT _ | Tok.KEYWORD "_" -> accept_before_syms [","] strm
  | _ -> raise Stream.Failure

let test_idcomma = Gram.Entry.of_parser "test_idcomma" accept_idcomma

GEXTEND Gram
  GLOBAL: ssr_idcomma;
  ssr_idcomma: [ [ test_idcomma; 
    ip = [ id = IDENT -> Some (id_of_string id) | "_" -> None ]; "," ->
    Some ip
  ] ];
END

let augment_preclr clr1 (((clr0, x),y),z) = (((clr1 @ clr0, x),y),z)

TACTIC EXTEND ssrgenhave
| [ "gen" "have" ssrclear(clr)
    ssr_idcomma(id) ssrhpats_nobs(pats) ssrwlogfwd(fwd) ssrhint(hint) ] ->
  [ let pats = augment_preclr clr pats in
    Proofview.V82.tactic (wlogtac ist pats fwd hint false (`Gen id)) ]
END

TACTIC EXTEND ssrgenhave2
| [ "generally" "have" ssrclear(clr)
    ssr_idcomma(id) ssrhpats_nobs(pats) ssrwlogfwd(fwd) ssrhint(hint) ] ->
  [ let pats = augment_preclr clr pats in
    Proofview.V82.tactic (wlogtac ist pats fwd hint false (`Gen id)) ]
END

(* We wipe out all the keywords generated by the grammar rules we defined. *)
(* The user is supposed to Require Import ssreflect or Require ssreflect   *)
(* and Import ssreflect.SsrSyntax to obtain these keywords and as a         *)
(* consequence the extended ssreflect grammar.                             *)
let () = Lexer.unfreeze frozen_lexer ;;

(* vim: set filetype=ocaml foldmethod=marker: *)

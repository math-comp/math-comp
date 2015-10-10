open Ocamlbuild_plugin

let coqtop =
  try Sys.getenv "COQBIN" ^ "/coqtop"
  with Not_found -> "coqtop"

let where x =
  let inc, _ = Unix.open_process (x ^ " -where") in
  input_line inc
;;

let config x =
  let inc, _ = Unix.open_process (x ^ " -config") in
  let l = ref [] in
  try
    while true do
      let s = input_line inc in
      let k,v =
         try
           let i = String.index s '=' in
           String.sub s 0 i,
           String.sub s (i+1) (String.length s - i - 1)
         with Not_found -> s, "true"
      in
      l := (k,v) :: !l
    done; assert false
  with End_of_file ->
    fun k -> try List.assoc k !l
             with Not_found -> "false"
;;

let config_coq = config coqtop

let coq x = where coqtop ^ "/" ^ x
let caml x = where "ocamlc" ^ "/" ^ x

let dirs = [
  "kernel"; "lib"; "library"; "parsing"; "pretyping"; "interp"; "printing";
  "intf"; "proofs"; "tactics"; "tools"; "toplevel"; "stm"; "grammar"; "config";
  "plugins/btauto"; "plugins/cc"; "plugins/decl_mode"; "plugins/derive"; "plugins/extraction";
  "plugins/firstorder"; "plugins/fourier"; "plugins/funind"; "plugins/micromega"; "plugins/nsatz";
  "plugins/omega"; "plugins/quote"; "plugins/romega"; "plugins/rtauto"; "plugins/setoid_ring";
  "plugins/syntax"; "plugins/xml";
]
;;

let includes = S [
  S (List.map (fun dir -> S [ A "-I"; P (coq dir); ]) dirs);
  A "-I"; P (caml "");
  A "-I"; P (caml "threads/");
  A "-I"; P (caml "camlp5");
]
;;

let flags = S [ A "-thread"; A "-rectypes"; ] ;;

let rec space_chop s =
  try
    let i = String.index s ' ' in
    String.sub s 0 i :: space_chop (String.sub s (i+1) (String.length s - i - 1))
  with Not_found -> [s]

let camlp5o =
 S [A (config_coq "CAMLP4O");
    includes;
    S (if config_coq "CAMLP4" = "camlp5"
       then [ A "pa_extend.cmo"; A "q_MLast.cmo"; A "pa_macro.cmo"; A "unix.cma"; ]
       else []);
    A "threads.cma";
    A "compat5.cmo";
    A "grammar.cma";
    S (List.map (fun x -> A x) (space_chop (config_coq "CAMLP4OPTIONS")));
  ]
;;

let rules () =
 rule ".ml4.ml" ~dep:"%.ml4" ~prod:"%.ml"
   (fun env _ ->
      let ml4 = env "%.ml4" and ml = env "%.ml" in
      Cmd (S[camlp5o; A"-o"; Px ml; A"-impl"; P ml4]));
 flag ["compile"; "ocaml"] (S [flags; includes]);
 flag ["link"; "ocaml"] (S [flags; includes]);
 ()
;;

rules ()


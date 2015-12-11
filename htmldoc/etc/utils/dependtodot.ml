(* Loic Pottier, projet CROAP, INRIA Sophia Antipolis, April 1998. *)
(* Laurent Théry , INRIA Sophia Antipolis, April 2007 *)

(* Convert a dependencies file, in makefile form, into a graph in a file readable by dot.

The function dependtodot takes as input the dependencies file, and create a file with the same name suffixed by ".dot", readable by  dot.

*)

let nodecol="#dbc3b6";; (* #add8ff *)
let edgecol="#676767";; (* #ff0000 *)

(* parameters to draw edges and nodes *)
let vnode x = 
    "l(\"" ^ x 
    ^ "\",n(\"\",[a(\"COLOR\",\""^ nodecol ^"\"),a(\"OBJECT\",\"" ^ x ^ "\")],"
;;

let wstring x = "\""^x^"\""
;;

let vnoder x = "r(\"" ^ x ^ "\")"
;;

let vedge = 
  "e(\"\",[a(\"_DIR\",\"inverse\"),a(\"EDGEPATTERN\",\"solid\"),a(\"EDGECOLOR\",\"" ^ edgecol ^ "\")],"
;;
    
let listdv l = match l with
    [] -> "[]"
   |x::l -> let rec listdvr l = match l with
                                [] -> ""
                               |y::l -> "," ^ y ^ (listdvr l)
            in "[" ^ x ^ (listdvr l) ^ "]"
;;

let rec visit ht hte x s =
          Hashtbl.add ht x x;
          try let le=Hashtbl.find hte x in
              let rec visit_edge ls le =
                 match le with
                   [] -> ls
                  |b::l -> 
                     try let _ =Hashtbl.find ht b in
                           (visit_edge (ls@[vedge ^ (vnoder b) ^ ")"]) l)
                     with Not_found ->
                       (visit_edge (ls@[vedge ^ (visit ht hte b s) ^ ")"]) l)
              in s ^ (vnode x) ^ (listdv (visit_edge [] le)) ^ "))"
          with Not_found -> s ^ (vnode x) ^ "[]))"
;;

(* cloture transitive *)

let rec merge_list a b = match a with
    [] -> b
   |x::a -> if (List.mem x b) 
            then (merge_list a b)
            else x::(merge_list a b)
;;

let ht_graph g =
  let ht =Hashtbl.create 50 in
  let rec fill g = match g with
        [] -> ()
       |(a,lb)::g -> Hashtbl.add ht a lb; fill g
  in fill g;
  ht
;;

let trans_clos1 g =
  let ht =ht_graph g in
  List.map (fun (a,lb) -> 
     (a,(let l = ref lb in
         let rec addlb lb = match lb with
           [] -> ()
          |b::lb -> (try l:=(merge_list (Hashtbl.find ht b) !l)
                     with Not_found -> ()); addlb lb
         in addlb lb;
         !l))) g
;;

let rec transitive_closure g =
  let g1=trans_clos1 g in
  if g1=g then g else (transitive_closure g1)
;;

(*
let g=["A",["B"];
       "B",["C"];
       "C",["D"];
       "D",["E"];
       "E",["A"]];;
transitive_closure g;;
*)

(* enlever les arcs de transitivite *)

let remove_trans g =
  let ht = ht_graph (transitive_closure g) in
  List.map (fun (a,lb) ->
   (a,(let l=ref [] in
       (let rec sel l2 = match l2 with
          [] -> ()
         |b::l2 -> (let r=ref false in
                    (let rec testlb l3 = match l3 with
                         [] -> ()
                        |c::l3 -> if (not (b=a)) &&(not(b=c)) && (not (a=c)) &&
                                     (try (List.mem b (Hashtbl.find ht c))
                                      with Not_found -> false)
                                  then r:=true
                                  else ();
                                  testlb l3
                    in testlb lb);
                    if (!r=false)
                    then l:=b::!l
                    else ());
                    sel l2
        in sel lb);
        !l))) g
;;
         
(*
let g1=["Le", ["C";"Lt";"B"; "Plus"];
  "Lt", ["A";"Plus"]];;

let g=["A",["B";"C";"D";"E"];
       "B",["C"];
       "C",["D"];
       "D",["E"]];;
remove_trans g;;

*)         
let dot g name file=
   let chan_out = open_out  (file^".dot") in
   output_string chan_out "digraph ";
   output_string chan_out name;
   output_string chan_out " {\n";
   output_string chan_out "  bgcolor=transparent;\n";
   output_string chan_out "  splines=true;\n";	
   output_string chan_out "  nodesep=1;\n";	
   output_string chan_out "  node [fontsize=18, shape=rect, color=\"#dbc3b6\", style=filled];\n";
   List.iter (fun (x,y) -> 
        output_string chan_out "  ";
        output_string chan_out (wstring x);
        output_string chan_out " [URL=\"./";
        output_string chan_out x;
        output_string chan_out ".html\"]\n";
     List.iter (fun y ->
                     output_string chan_out "  ";
                     output_string chan_out (wstring x);
                     output_string chan_out " -> ";
                     output_string chan_out (wstring y);
                     output_string chan_out ";\n") y) g;
   flush chan_out;
   output_string chan_out "}";
   close_out  chan_out
;;

(*
example: a complete 5-graph,

let g=["A",["B";"C";"D";"E"];
       "B",["A";"C";"D";"E"];
       "C",["A";"B";"D";"E"];
       "D",["A";"B";"C";"E"];
       "E",["A";"B";"C";"D"]];;

daVinci g "g2";;

the file is then g2.daVinci

*)
(***********************************************************************)
open Genlex;;

(* change OP april 28 *)
(* 
this parsing produce a pair where the first member is a paire (file,Directory) 
and the second is a list of pairs (file,Directory).
from this we can compute the files graph dependency and also the directory graph dependency
*)

let lexer = make_lexer [":";".";"/";"-"];; 

let rec parse_dep = parser
    [< a=parse_name; 'Kwd ".";'Ident b; _=parse_until_colon;
      _=parse_name ;'Kwd "."; 'Ident d;n=parse_rem  >] -> (a,n)
and parse_rem = parser
    [< a=parse_name;'Kwd ".";'Ident b;n=parse_rem >] -> a::n
    | [<>]->[]
and parse_until_colon = parser
     [< 'Kwd ":" >] -> ()
   | [< 'Kwd _; _=parse_until_colon >] -> ()
   | [< 'Int _; _=parse_until_colon >] -> ()
   | [< 'Ident _; _=parse_until_colon >] -> ()

and parse_name = parser
   [<'Kwd "/";a=parse_ident; b=parse_name_rem a "" >]-> a::b
  |[<a=parse_ident; b=parse_name_rem a "" >]-> a::b
 and parse_name2 k = parser
   [<d=parse_ident; b=parse_name_rem d k >]-> d::b
 and parse_name_rem a b= parser
     [<'Kwd "/";c=parse_name2 a >]-> c
   | [<>]->[]

and parse_ident = parser
   [<'Ident a; b=parse_ident_rem a "" >]-> a ^ b
  |[<'Int a; b=parse_ident_rem (string_of_int a) "" >]-> (string_of_int a) ^ b
 and parse_ident2 k = parser
   [<'Ident d; b=parse_ident_rem d k >]-> d ^ b
  |[<'Int d; b=parse_ident_rem (string_of_int d) k >]-> (string_of_int d) ^ b
 and parse_ident_rem a b= parser
     [<'Kwd "-";c=parse_ident2 a >]-> "-" ^ c
   | [<>]-> ""
;;

(*
parse_name(lexer(Stream.of_string "u/sanglier/0/croap/pottier/Coq/Dist/contrib/Rocq/ALGEBRA/CATEGORY_THEORY/NT/YONEDA_LEMMA/NatFun.vo: "));;
parse_ident(lexer(Stream.of_string "ARITH-OMEGA-ggg-2.vo:"));; PROBLEME
*)

(* reads the depend file *)
let read_depend file=
  let st =open_in file in
  let lr =ref [] in
  let rec other() =
       (try 
         let d=parse_dep(lexer(Stream.of_string (input_line st))) in
         lr:=d::(!lr);
         other()
        with _ ->[]) 
   in (let _ = other() in ());
   !lr;;

(* graph of a directory (given by a path) *)
let rec is_prefix p q = match p with
   [] -> true
  |a::p -> match q with [] -> false
                       |b::q -> if a=b then (is_prefix p q) else false
;;
  
let rec after_prefix p q = match p with
   [] ->(match q with
            [] -> "unknown"
           |a::_ -> a)
  |a::p -> match q with [] -> "unknown"
                       |b::q -> (after_prefix p q)
;;

let rec proj_graph p g =  match g with
  [] -> []
 |(q,l)::g -> if (is_prefix p q) 
           then let rec proj_edges l = match l with
                     [] -> []
		    |r::l -> if (is_prefix p r)
		             then (after_prefix p r)::(proj_edges l)
                             else (proj_edges l)
                in ((after_prefix p q),(proj_edges l))
                   ::(proj_graph p g)
           else (proj_graph p g)

;;

let rec start_path p = match p with
   [] ->[]
  |a::p -> match p with
              [] ->[]
             |b::q -> a::(start_path p)
;;

  
(* the list of all the paths and subpaths in g *)
let all_path g =
   let ht =Hashtbl.create 50 in
   let add_path p = Hashtbl.remove ht p;Hashtbl.add ht p true in
   let rec add_subpath p = match p with
          [] ->()
         |_ -> add_path p; add_subpath (start_path p) in      
   let rec all_path g = match g with
      [] -> ()
     |(q,l)::g -> add_subpath (start_path q);
                  let rec all_pathl l = match l with
                       [] -> ()
                      |a::l -> add_subpath (start_path a);
                               all_pathl l
                  in all_pathl l;
                  all_path g
   in all_path g;
   let lp=ref [] in
     Hashtbl.iter (fun x y -> lp:=x::!lp) ht;
     !lp
;;
                     
    
(*
let g=read_depend "depend";;
proj_graph ["theories"] g;;
*)

let rec endpath p =  match p with
   [] ->""
  |a::p -> match p with
                [] ->a
               |_ -> endpath p
;;

let rec fpath p =  match p with
   [] ->""
  |a::p -> a ^ "/" ^ (fpath p)
;;

let rec spath p = match p with
   [] -> ""
  |a::p -> match p with
                [] ->a
               |b::q -> a ^ "/" ^ (spath p)
;;

(* creates graphs for all paths *)


let dependtodot file=
  let g =(read_depend file) in
  let lp1 = all_path g in
  let lp = (if lp1=[] then [[]] else lp1) in
  let rec ddv lp = match lp with
     [] -> ()
    |p::lp -> let name =  (let f = (endpath p) in
                           if f="" then file else f) in
              let filep = (let f = (spath p) in
                           if f="" then file else f) in
              dot (remove_trans (proj_graph p g)) 
                    name filep;
              ddv lp
  in ddv lp
  
;;
let _ = 
  if (Array.length Sys.argv) == 2 then
    dependtodot Sys.argv.(1)
  else print_string "makedot depend";
       print_newline()


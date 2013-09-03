#!/usr/bin/env ocamlscript 

let _ = Ocaml.packs := ["unix"]

let _ = Ocaml.sources := [
(*  "/tmp/l/general/research/code/ocaml/lib/hol_light_lib.ml";
  "/tmp/l/general/research/code/ocaml/lib/fmap.ml"; *)
  "/tmp/l/general/research/parsing/old/p3_lib.ml"
]

(* FIXME we really want to make this as independent of other things as possible; maybe don't use P3 for command line parsing? *)

(*
# use "/tmp/l/general/research/code/ocaml/lib/hol_light_lib.ml";;
# use "/tmp/l/general/research/code/ocaml/lib/fmap.ml";;
#use "/tmp/l/general/research/parsing/old/p3_lib.toplevel.ml";;
#load "unix.cma"
*)

--

open Unix

(**********************************************************************)
(* lib *)

let rec itlist f l b =
  match l with
    [] -> b
  | (h::t) -> f h (itlist f t b);;

let prefix s p = 
  String.length p <= String.length s && String.sub s 0 (String.length p) = p

type ('a,'b) fmap = ('a*'b) list
let fm0 = []
let fm_add fm (k,v) = (k,v)::fm
let fm_apply fm k = try Some(List.assoc k fm) with _ -> None

let strings_of_file filename =
  let fd = try Pervasives.open_in filename
           with Sys_error _ ->
             failwith("strings_of_file: can't open "^filename) in
  let rec suck_lines acc =
    try let l = Pervasives.input_line fd in
        suck_lines (l::acc)
    with End_of_file -> List.rev acc in
  let data = suck_lines [] in
  (Pervasives.close_in fd; data);;


(**********************************************************************)
(* command line and main *)

(* basedir contains pre and post *)
type ty_cl_args = { 
  filename: string; 
  tags: string list; 
  indent: string list; 
  verbose:bool; 
  prefix:(string,string)fmap;
  postfix:(string,string)fmap;
  parsed:string list 
}
let cl0 = { filename="/tmp/tmp.txt"; tags=[]; indent=[]; verbose=false; prefix=fm0; postfix=fm0; parsed=[] }

(* FIXME remove this 
let parse_FLARGS = 
  let sep = a "\x00" in
  (parse_FLAG **> sep **> (listof parse_ARG sep)) >> (fun (f,(_,xs)) -> (f,xs)) 
*)

(* precedence to earlier args *)
let rec parse_CL = fun i -> (
  let open P3_lib.BasicParsers in
  let open P3_lib.Everything in
  let f1 (f,xs) cl = (match (f,xs) with
    | ("-tag",_) -> {cl with tags=(xs@cl.tags) }
    | ("-indent",_) -> {cl with indent=(xs@cl.indent) }
    | ("-pre",x::xs) -> (
      (* p is the prefix, xs are the tags *)
      let (p::xs) = List.rev (x::xs) in
      let f1 x cl = {cl with prefix=(fm_add cl.prefix (x,p)) } in
      itlist f1 xs cl)
    | ("-post",x::xs) -> (
      (* p is the prefix, xs are the tags *)
      let (p::xs) = List.rev (x::xs) in
      let f1 x cl = {cl with postfix=(fm_add cl.postfix (x,p)) } in
      itlist f1 xs cl)
    | ("-in",[a]) -> {cl with filename=a }
    | ("-v",[]) -> {cl with verbose=true }
    | _ -> (failwith ("parse_CL: unrecognized flag/arg combination: "^(String.concat " " (f::xs)))))
  in
  let sep = a "\x00" in
  (((listof parse_FLARGS sep) **> parse_EOF) >> (fun (xs,_) -> itlist f1 xs cl0))) i

let args = 
  let open P3_lib.Everything in
  let argv = List.tl (Array.to_list (Sys.argv)) in
(*  let _ = print_endline ("Command line: "^(String.concat " " argv)) in *)
  let (r,_) = List.hd (parse_CL (toinput (full (String.concat "\x00" argv)))) in
  r

let _ = 
  if args.verbose then (
    print_endline ("Parsed command line args:");
    ignore(List.map print_endline args.parsed);
    ()) 
  else ()

let lines = strings_of_file args.filename


(**********************************************************************)
(* start *)

(* we no longer do the prefix etc- we have to have the tags etc exact *)

(* FIXME we only want prefixes and postfixes if we are actually printing the tag *)

type ty_state = {
  tag:string; (* current tag *)
  dummy: unit
}

let f1 s line = (
  let printing s = List.exists (fun x -> (s.tag) = x) args.tags in
  if (prefix line "@") then (
    (* may need to write a postfix for the current tag *)
    let _ = (
      if (printing s) then
        let _ = (match fm_apply args.postfix s.tag with 
          | None -> () 
          | Some x -> print_endline x; (*print_endline ""*)) 
        in
        ()
      else
        ())
    in
    let s = {s with tag=line} in
    (* may need to print a new prefix *)
    let _ = (
      if (printing s) then
        let _ = (match fm_apply args.prefix s.tag with 
          | None -> () 
          | Some x -> print_endline x; (*print_endline ""*)) 
        in
        ()
      else
        ())
    in
    s
  ) else (
    let _ = (
      if (printing s) then 
        let indent = List.mem s.tag args.indent in
        match indent with
        | (false) -> (print_endline line; ())
        | (true) -> (
          print_string "    "; 
          print_endline line; 
          ())
      else
        ())
    in
    s))

let _ = List.fold_left f1 {tag=""; dummy=()} lines
      

(*      

let _ = 
  let f line s = 
    if(prefix line "@") then (
      (* we may need to write a postfix for the previous region, and a prefix for the new *)
      (match fm_apply args.postfix s.tag with | None -> () | Some x -> print_endline x; print_endline "");
      tag := line; 
      (match fm_apply args.prefix s.tag with | None -> () | Some x -> print_endline ""; print_endline x);
      ())
    else (
      let print = List.exists (fun x -> (!tag) = x) args.tags in
      let indent = mem (!tag) args.indent in
      match (print,indent) with
        | (true,false) -> (print_endline line; ())
        | (true,true) -> (
          print_string "    "; 
          print_endline line; 
          ())
        | _ -> ())
  in
  rev_itlist f lines ()
*)

(* testing

cat >/tmp/tmp.txt < <EOF

@no
some text
@yes
print this
@comment
this should be in a comment
@yes
and prin this
@ignorecomment
this should not be printed
but also, we don't want prefix and postfix for this input
@no
not this
@yes
but also this

EOF

let args = cl0
let args = { args with 
   tags=["@yes";"@comment"]; 
   prefix=(fm_add args.prefix ("@comment","(* STARTCOMMENT")); 
   postfix=(fm_add args.postfix ("@comment","ENDCOMMENT *)")); 
};;

let args = { args with 
   tags=["@yes";"@comment"]; 
   prefix=(fm_add args.prefix ("@ignorecomment","(* FIXME")); 
   postfix=(fm_add args.postfix ("@ignorecomment","FIXME *)")); 
};;



desired output:

print this
(* STARTCOMMENT
this should be in a comment
ENDCOMMENT *)
and prin this
but also this


*)

(*
Local Variables:
mode: tuareg
End:
*)

module Mycsv = struct 
(*
# Tool for parsing csv

Note that a record must end in a return. A CSV file is a sequence of records. Thus, for us, the last character in the file must be a return char. (As an exceptional case, there could be no records, ie the file is empty; in this case, a bug in the file reading code will add a return character probably.)

## Dependencies
*)

open Unix
open P3_lib
open Everything
open BasicParsers

(*
# Interactive top-level directives

Via findlib:

    #use "topfind";;
    #require "unix";;
    #use "p3_lib.toplevel.ml";;
    #use "mycsv.toplevel.ml";;
    open Unix
    open P3_lib
    open Everything
    open BasicParsers

*)
(*
## Library

*)
let rec (--) = fun m n -> if m > n then [] else m::((m + 1) -- n);;


let rec explode s = if s = "" then [] else (String.sub s 0 1) :: (explode (String.sub s 1 (String.length s - 1)));;

let implode s = String.concat "" s;;

(* FIXME move to mng file for doc *)
(* removes whitespace at beginning and end of a string *)
let rem_ws s = 
  let rec f1 xs = (match xs with 
    | [] -> xs
    | x::xs -> if x = " " then f1 xs else x::xs)
  in
  implode (List.rev (f1 (List.rev (explode s))))

(* get lines from a file *)
let lines fname =
  let lines = ref [] in
  let chan = if fname="-" then Pervasives.stdin else open_in fname in
  try
    while true; do
      lines := input_line chan :: !lines
    done; []
  with End_of_file ->
    close_in chan;
    List.rev !lines


(*
## Basic types

Type `ty_csv_params` allows you to parameterize on:

  * field separator
  * output field separator (not used in parsing)
  * double quote character
  * record separator (newline)

These can be strings (not characters). There is nothing in the following that prevents these being arbitrary parsers (but we keep them strings for now; we obviously would need string versions for output e.g. for `dquote^dquote`). The parameters are completely arbitrary. For example, they could all be the same character (but presumably any non-trivial csv file would then be very ambiguous).

*)

type ty_csv_params = { sep:string; outsep:string; dquote:string; newline:string }

type ty_width = None1 | Some1 of int | Trim1 | Max1 | MaxNoQuote1



(*
## CSV parsing

*)

let parse_file params = 
  let rec parse_field = fun i -> (parse_quoted_field ||| parse_plain_field) i
  and parse_plain_field = fun i -> 
    (until ((a params.newline) ||| (a params.sep) ||| (a params.dquote)) >> content)
      i
  and parse_quoted_field = fun i -> 
    (((a params.dquote) **> parse_quoted_field_contents **> (a params.dquote)) >> (fun (_,(s,_)) -> s))
      i
  and parse_quoted_field_contents = fun i -> 
    (((until (a params.dquote)) >> content) 
     ||| (((until (a params.dquote)) **> (a (params.dquote^params.dquote)) **> parse_quoted_field_contents) >> (fun (s1,(_,s2)) -> (content s1)^params.dquote^s2)))
      i
  in
  (* *)
  let rec parse_fieldsplus = fun i -> (
    (parse_field >> (fun s -> [s]))
    ||| ((parse_field **> (a params.sep) **> parse_fieldsplus) >> (fun (s1,(_,s2)) -> s1::s2))) 
    i
  in
  let rec parse_record = fun i -> (
    (* but fields could be plain_field empty, or quoted empty - ambiguity in csv, does empty line repn a single empty field or not *)
    ((a params.newline) >> (fun (_) -> []))
    ||| (((noteps (parse_fieldsplus)) **> (a params.newline)) >> (fun (s1,_) -> s1)))
    i
  in
  (* *)
  let rec parse_records = fun i -> 
    (((a "") >> (fun _ -> []))
     ||| ((parse_record **> parse_records) >> (fun (r,rs) -> r::rs)))
      i
  in
  (* *)
  let rec parse_file' = fun i -> ((parse_records **> (* parse_epsws **> *) parse_EOF) >> (fun (rs,_) -> rs)) i
  in
  parse_file'



(*
## Output auxiliary functions
*)

(* FIXME this is wrong if sep <> outsep - need to be more careful; FIXME also wrong if sep etc not single chars *)
let needs_quote params s = 
  (* FIXME probably remove params.sep - this is for output, not input *)
  let p = until ((a params.sep) ||| (a params.outsep) ||| (a params.dquote) ||| (a params.newline)) in
  let rs = p (toinput (full s)) in
  if rs <> [] then true else false

let quote params s = 
  let rec p = fun i -> (
    (* the following parses to the end of the string, provided NO dquote before *)
    (((until ((a params.dquote) ||| parse_EOF)) **> parse_EOF) >> (fun (s,_) -> content s))
    ||| (((until (a params.dquote)) **> (a params.dquote) **> p) >> (fun (s,(_,r)) -> ((content s)^params.dquote^params.dquote^r))))
    i
  in
  if needs_quote params s then (
    match p (toinput (full s)) with
    | [] -> (failwith ("quote: failed to parse string: "^s))
    | [(r,_)] -> (params.dquote^r^params.dquote)
    | _ -> (failwith ("quote: failed to parse string unambiguously: "^s)))
  else
    s

(*
## Column formatting
*)

(* given a list of rows, where each row is a list of strings, and a col index, give the max width of an entry in that col *)

(* FIXME depending on the application, we may not want to trim whitespace in the following *)
(* FIXME efficiency - don't want to compute max_width every time! *)
let max_width rs =
  let maxn = itlist (fun r -> fun n -> max (List.length r) n) rs 0 in
  let colns = (0 -- maxn) in
  let f n = 
    let rs = List.filter (fun r -> n < List.length r) rs in
    let fs = List.map (fun r -> List.nth r n) rs in
    let i = itlist (fun f -> fun ll -> max (String.length (rem_ws f)) ll) fs 0 in
    i
  in
  let colws = List.map f colns in
  fun n -> List.nth colws n

let (_:string list list -> int->int) = max_width (* max_width of a column *)

(* w is width arg; mw is max_width; n is col index; s is string *)
let format1 params w mw (n,s) = quote params (match w with
  | None1 -> s
  | Some1 ll -> (
    let t = ref s in 
    let _ = while(String.length !t < ll); do t := !t^" "; done in
    let t = String.sub (!t) 0 ll in
    t)
  | Trim1 -> (rem_ws s)
  | Max1 -> (
    let ll = mw n in
    let t = ref s in 
    let _ = while(String.length !t < ll); do t := !t^" "; done in
    let t = String.sub (!t) 0 ll in
    t)
  | MaxNoQuote1 -> (
    if (needs_quote params s) then s else
    let ll = mw n in
    let t = ref s in 
    let _ = while(String.length !t < ll); do t := !t^" "; done in
    let t = String.sub (!t) 0 ll in
    t))

(* format a row; rs is whole array *)
let format params w rs xs = 
  let xs' = List.combine (0 -- (List.length xs - 1)) xs in
  (String.concat params.outsep (List.map (format1 params w (max_width rs)) xs'))^params.newline


 end
;;

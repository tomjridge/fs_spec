(*
Hi-lock: (("^@.*" (0 (quote hi-blue-b) t)))
Hi-lock: (("^#+.*" (0 (quote hi-green-b) t)))

# Interactive top-level directives

Via findlib:

    #use "topfind";;
    #require "unix";;
    #require "bigarray";;
    #require "str";;
    (* #cd "/tmp/l/general/research/fs/fs_spec/src";; *)
    #use "fs_prelude.toplevel.ml";;
    #use "fs_spec.toplevel.ml";;
    #use "idir.ml";;


# `idir.ml`

This is a variation on dir_tree; we work with "instrumented"
directories, ie the state is a map from addresses to directories,
where a directory entry may be an address.

Directory references are pairs (a,ns), where a is an abstract address,
and ns is a path within the given instrumented directory.

Question: how does this relate to ssl? Are we closer to being able to
link things up?

*)

open Fs_prelude
open Fs_spec

open Fmap


open Prelude
open Fs_types1 (* FIXME remove dependence? have a core types and a state types? *)

type address = string

(* dirs are represented by their canonical paths; obviously this isn't a real
   reference, so won't work if dirs are renamed *)
type dir_ref = Dir_ref of (address * string list)
let dest_dir_ref s0 _ = 999

type inode_ref = Inode_ref of int
let dest_inode_ref s0 (Inode_ref i) = i

type name = Fs_spec.Fs_types1.name
type contents = string
type contents_heap = (inode_ref,contents) fmap
(* root dir has name ""; root must be a dir *)
type entrya = Dir of (name,entrya) fmap | File of inode_ref | Add of address

type fs = { es1:(address,entrya)fmap; cs1: contents_heap }

let new_inode_ref fs = (
  let xs = fmap_dom fs.cs1 in
  let xs = List.map (dest_inode_ref fs) xs in
  Inode_ref(1+(List.fold_left (fun acc -> fun i -> max acc i) 0 xs)))

(* framestack *)
type entries2 = Dir2 of (name,entrya) fmap * name 

(* this does not handle addresses *)
let frame_resolve1 (e,frms) n = (
  match e with 
  | File _ -> (failwith "frame_resolve1'")
  | Dir m -> (
    let e = dest_Some(fmap_lookup m n) in (* FIXME expect to find the entry *)
    (e,Dir2(m,n)::frms))
  | Add _ -> (failwith "frame_resolve1"))

let frame_resolve e ns = (
  List.fold_left frame_resolve1 (e,[]) ns)

let frame_assemble (e,frms) = (
  let f1 e f = (match f with
    | Dir2(m,n) -> (
      let m' = fmap_update m (n,e) in
      Dir m'))
  in
  List.fold_left f1 e frms)

let fs_resolve s0 d0_ref = (
  let (a,ns) = d0_ref in
  let e0 = dest_Some(fmap_lookup s0.es1 a) in
  let (e,frms) = frame_resolve e0 ns in
  (a,e,frms))

let fs_assemble s0 (a,e,frms) = (
  let e = frame_assemble (e,frms) in
  let es = fmap_update s0.es1 (a,e) in
  {s0 with es1=es })

let link_file s0 i0_ref d0_ref name = (
  let (a,e,frms) = fs_resolve s0 d0_ref in
  match e with
  | File _ -> (failwith "link_file: impossible") (* dir_ref resolved to file *)
  | Dir m -> (
    let m' = fmap_update m (name,File i0_ref) in
    let s0 = fs_assemble s0 (a,Dir m',frms) in
    return_state s0)
  | Add _ -> (failwith "FIXME: link_file; what to do if removing an address"))

let unlink s0 d0_ref name = (
  let (a,e,frms) = fs_resolve s0 d0_ref in
  match e with
  | File _ -> (failwith "link_file: impossible") (* dir_ref resolved to file *)
  | Dir m -> (
    let m' = fmap_remove m name in
    let s0 = fs_assemble s0 (a,Dir m',frms) in
    return_state s0)
  | Add _ -> (failwith "FIXME"))

let link_dir s0 d0_ref name d = (
  let (a,e,frms) = fs_resolve s0 d0_ref in
  match e with
  | File _ -> (failwith "link_file: impossible") (* dir_ref resolved to file *)
  | Dir m -> (
    let m' = fmap_update m (name,d) in
    let s0 = fs_assemble s0 (a,Dir m',frms) in
    return_state s0)
  | Add _ -> (failwith "FIXME"))

let mkdir s0 d0_ref name = (link_dir s0 d0_ref name (Dir[]))

let mv s0 d0_ref name0 d1_ref name1 = (
  let d0_ref' = (fst d0_ref,(snd d0_ref)@[name0]) in
  let (a,e,frms) = fs_resolve s0 d0_ref' in
  match e with
  | File i0_ref -> (
    let s0 = (unlink s0 d0_ref name0).state2 in
    let s0 = (link_file s0 i0_ref d1_ref name1).state2 in
    return_state s0)
  | _ -> (failwith "mv"))

let mvdir s0 d0_ref name0 d1_ref name1 = (
  let d0_ref' = (fst d0_ref,(snd d0_ref)@[name0]) in
  let (a,e,frms) = fs_resolve s0 d0_ref' in
  match e with
  | File i0_ref -> (failwith "mvdir: 1")
  | Dir m -> (
    let s0 = (unlink s0 d0_ref name0).state2 in
    link_dir s0 d1_ref name1 (Dir m))
  | Add _ -> (failwith "FIXME mkdir Add"))

let read s0 i0_ref = (
  let Some(c) = fmap_lookup s0.cs1 i0_ref in
  {state2=s0;ret2=(Bytes1 (MyDynArray.of_string c)) })

let readdir s0 d0_ref = (
  let (a,e,frms) = fs_resolve s0 d0_ref in
  match e with
  | File _ -> (failwith "readdir")
  | Dir m -> (
    let names = fmap_dom m in
    let names = List.sort Pervasives.compare names in      
    {state2=s0; ret2=(Names1 names)})
  | Add _ -> (failwith "readdir Add"))

let resolve1 s0 d0_ref name = (
  let d0_ref' = (fst d0_ref,(snd d0_ref)@[name]) in
  let (a,e,frms) = fs_resolve s0 d0_ref in
  match e with
  | File i0_ref -> None
  | Dir m -> (
    let e = fmap_lookup m name in
    match e with | None -> None | Some e -> 
    match e with
    | File i0_ref -> (Some(Inr i0_ref))
    | Dir _ -> (Some(Inl (d0_ref')))
    | Add _ -> (failwith "resolve1: Add1"))
  | Add _ -> (failwith "resolve1: Add2"))
    
let rm = unlink

let rmdir = unlink

let touch s0 d0_ref name = (
  let (a,e,frms) = fs_resolve s0 d0_ref in
  match e with
  | File _ -> (failwith "touch")
  | Dir m -> (
    let i0_ref = new_inode_ref s0 in
    let s0 = {s0 with cs1=(fmap_update s0.cs1 (i0_ref,""))} in
    link_file s0 i0_ref d0_ref name)
  | Add _ -> (failwith "touch: Add"))

let write s0 i0_ref c = (return_state {s0 with cs1=(fmap_update s0.cs1 (i0_ref,MyDynArray.to_string c))})

let empty_es1 = fmap_update fmap_empty ("",Dir[])

let state0 = {es1=empty_es1; cs1=fmap_empty}

let ops1 = {
  get_init_state1=(fun () -> state0);
  get_parent1=(fun _x_ -> fun (a,ns) -> if ns = [] then None else Some((a,butlast ns),last ns));
  get_root1=(fun s0 -> Some("",[])); (* "",[]  is the dir ref for the root dir *)
  dest_dir_ref1=dest_dir_ref;
  dest_inode_ref1=dest_inode_ref;
  get_symlink1=(fun s0 -> fun i0_ref -> false);
  link_file1=(link_file);
  unlink1=(unlink);
  mkdir1=(mkdir);
  mv1=(mv);
  mvdir1=(mvdir);
  read1=(read);
  readdir1=(readdir);
  resolve11=(resolve1);
  rm1=(rm);
  rmdir1=(rmdir);
  touch1=(touch);
  write1=(write);
  set_symlink1=(fun _x_ -> fun _x_ -> fun f -> failwith "set_symlink")
}


(*
@test

 #use "/tmp/l/general/research/fs/local_resources/p3_lib.toplevel.ml";;
 #use "/tmp/l/general/research/fs/fs_utils/fs_printer.toplevel.ml";;
 #use "/tmp/l/general/research/fs/fs_utils/fs_parser.toplevel.ml";;

 #print_depth 400;;
 #print_length 2000;;

open Fs_spec
open Fs_spec_everything


let txt = "mkdir /tmp 0
mkdir /tmp/somedir 0
mkdir /tmp/somedir/anotherdir 0
open /tmp/tmp.txt [O_CREAT]
open /tmp/somedir/somedir.txt [O_CREAT]
rename /tmp/somedir /somedir
rename /tmp/tmp.txt /somedir/tmp.txt
unlink /tmp/tmp.txt
unlink /tmp/somedircopy
link /somedir/somedir.txt /tmp/somedirlink.txt
write /tmp/somedirlink.txt 0 hello_world 11
read /tmp/somedirlink.txt 0 11"

let s0 = state0 

let ops = ops1

let take xs n = fst(List.fold_left (fun (xs,n) -> fun x -> if n=0 then (xs,n) else (xs@[x],n-1)) ([],n) xs)

let s0 = { pid_table=fmap_empty; fs_state=s0 }

let lbls = [Some(OS_CREATE(Pid(1)))]

let (_,_,s0) = last(Os_transition_system.os_process_labels ops s0 lbls)

let [lbls] = P3_lib.P3.p3_run_parser Fs_parser.parse_OPS txt

let lbls = 
  let f1 lbl = [Some(OS_CALL(Pid 1,lbl));None;Some(OS_RETURN(Pid 1,Inr None1))] in
  List.concat (List.map f1 lbls)

let xs = Os_transition_system.os_process_labels ops s0 (take lbls 23) (* next step is an error *)



(* testing os transition system transitions *)

let fs_s0 = Dir_tree_types.state0 
let lbls = [Some(OS_CREATE(Pid(1)))]
let s0 = { pid_table=fmap_empty; fs_state=fs_s0 }

let (_,_,s0) = last(Os_transition_system.os_process_labels ops s0 lbls)

let [lbls] = P3_lib.P3.p3_run_parser Fs_parser.parse_OPS txt

let lbls = 
  let f1 lbl = [Some(OS_CALL(Pid 1,lbl));None;Some(OS_RETURN(Pid 1,Inr None1))] in
  List.concat (List.map f1 lbls)

let _ = Os_transition_system.os_process_labels ops s0 (take lbls 22)

(* looks OK; next step is an error *)

@ignore
# Local variables

Local Variables:
mode: tuareg
mode: hi-lock
outline-regexp: "@\\|#+"
End:

*)

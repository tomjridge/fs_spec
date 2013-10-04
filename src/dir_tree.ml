(*
# Interactive top-level directives

Via findlib:

    #use "topfind";;
    #require "unix";;
    #require "bigarray";;
    #require "str";;
    (* #cd "/tmp/l/general/research/fs/fs_spec/src";; *)
    #use "fs_prelude.toplevel.ml";;
    #use "fs_spec.toplevel.ml";;
    #use "dir_tree.toplevel.ml";;


# `dir_tree.ml`
## `Dir_tree_types` and basic operations

Types for a representation using an inode heap and a dir tree

*)

open Fs_prelude
open Fs_spec

module Dir_tree_types = struct

  open Fmap


  open Prelude
  open Fs_types1 (* FIXME remove dependence? have a core types and a state types? *)

  (* dirs are represented by their canonical paths; obviously this isn't a real
     reference, so won't work if dirs are renamed *)
  type dir_ref = string list
  let dest_dir_ref s0 _ = 999

  (* doesn't take into account actual state - only valid for actually existing dirs *)
  let rec realpath' ns1 ns2 = (
    match ns2 with 
    | [] -> ns1
    | n::ns2 -> (match n with
      | "" -> (realpath' ns1 ns2)
      | "." -> (realpath' ns1 ns2)
      | ".." -> (
        match ns1 with
        | [] -> (realpath' ns1 ns2)
        | _ -> (realpath' (butlast ns1) ns2))
      | _ -> (realpath' (ns1@[n]) ns2)))
  let realpath ns = realpath' [] ns    

  type inode_ref = Inode_ref of int
  let dest_inode_ref s0 (Inode_ref i) = i


  type name = Fs_spec.Fs_types1.name
  type contents = string
  type contents_heap = (inode_ref,contents) fmap
  (* root dir has name ""; root must be a dir *)
  type entry = Dir of (name,entry) fmap | File of inode_ref
  type fs = { es1:entry; cs1: contents_heap }

  let new_inode_ref fs = (
    let xs = fmap_dom fs.cs1 in
    let xs = List.map (dest_inode_ref fs) xs in
    Inode_ref(1+(List.fold_left (fun acc -> fun i -> max acc i) 0 xs)))

  (* framestack *)
  type entries2 = Dir2 of (name,entry) fmap * name 

  let frame_resolve1 (e,frms) n = (
    match e with 
    | File _ -> (failwith "frame_resolve1'")
    | Dir m -> (
      let Some(e) = fmap_lookup m n in
      (e,Dir2(m,n)::frms)))

  let frame_resolve e ns = (
    List.fold_left frame_resolve1 (e,[]) ns)

  let frame_assemble (e,frms) = (
    let f1 e f = (match f with
      | Dir2(m,n) -> (
        let m' = fmap_update m (n,e) in
        Dir m'))
    in
    List.fold_left f1 e frms)

  let link_file s0 i0_ref d0_ref name = (
    let (e,frms) = frame_resolve s0.es1 d0_ref in
    match e with
    | File _ -> (failwith "link_file: impossible") (* dir_ref resolved to file *)
    | Dir m -> (
      let m' = fmap_update m (name,File i0_ref) in
      return {s0 with es1=(frame_assemble (Dir m',frms))} ))

  let unlink s0 d0_ref name = (
    let (e,frms) = frame_resolve s0.es1 d0_ref in
    match e with
    | File _ -> (failwith "link_file: impossible") (* dir_ref resolved to file *)
    | Dir m -> (
      let m' = fmap_remove m name in
      return {s0 with es1=(frame_assemble (Dir m',frms))} ))

  let link_dir s0 d0_ref name d = (
    let (e,frms) = frame_resolve s0.es1 d0_ref in
    match e with
    | File _ -> (failwith "link_file: impossible") (* dir_ref resolved to file *)
    | Dir m -> (
      let m' = fmap_update m (name,d) in
      return {s0 with es1=(frame_assemble (Dir m',frms))} ))

  let mkdir s0 d0_ref name = (link_dir s0 d0_ref name (Dir[]))

  let mv s0 d0_ref name0 d1_ref name1 = (
    let (e,frms) = frame_resolve s0.es1 (d0_ref@[name0]) in
    match e with
    | File i0_ref -> (
      let s0 = (unlink s0 d0_ref name0).state2 in
      let s0 = (link_file s0 i0_ref d1_ref name1).state2 in
      return s0)
    | _ -> (failwith "mv"))

  let mvdir s0 d0_ref name0 d1_ref name1 = (
    let (e,frms) = frame_resolve s0.es1 (d0_ref@[name0]) in
    match e with
    | File i0_ref -> (failwith "mvdir: 1")
    | Dir m -> (
      let s0 = (unlink s0 d0_ref name0).state2 in
      link_dir s0 d1_ref name1 (Dir m)))

  let read s0 i0_ref = (
    let Some(c) = fmap_lookup s0.cs1 i0_ref in
    {state2=s0;ret2=(Bytes1 (MyDynArray.of_string c)) })

  let readdir s0 d0_ref = (
    let (e,frms) = frame_resolve s0.es1 d0_ref in
    match e with
    | File _ -> (failwith "readdir")
    | Dir m -> (
      let names = fmap_dom m in
      let names = List.sort Pervasives.compare names in      
      {state2=s0; ret2=(Names1 names)}))

  let resolve1 s0 d0_ref name = (
    let (e,frms) = frame_resolve s0.es1 d0_ref in
    match e with
    | File i0_ref -> None
    | Dir m -> (
      let e = fmap_lookup m name in
      match e with | None -> None | Some e -> 
      match e with
      | File i0_ref -> (Some(Inr i0_ref))
      | Dir _ -> (Some(Inl (d0_ref@[name])))))
      

  let rm = unlink

  let rmdir = unlink

  let touch s0 d0_ref name = (
    let (e,frms) = frame_resolve s0.es1 d0_ref in
    match e with
    | File _ -> (failwith "touch")
    | Dir m -> (
      let i0_ref = new_inode_ref s0 in
      let s0 = {s0 with cs1=(fmap_update s0.cs1 (i0_ref,""))} in
      link_file s0 i0_ref d0_ref name))

  let write s0 i0_ref c = (return {s0 with cs1=(fmap_update s0.cs1 (i0_ref,MyDynArray.to_string c))})

  let state0 = {es1=Dir[]; cs1=fmap_empty}

  let ops1 = {
    get_init_state1=(fun () -> state0);
    get_parent1=(fun _ -> fun d0_ref -> if d0_ref = [] then (d0_ref,None) else (butlast d0_ref,Some(last d0_ref)));
    get_root1=(fun s0 -> Some[]); (* []  is the dir ref for the root dir *)
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
    set_symlink1=(fun _ -> fun _ -> fun f -> failwith "set_symlink");
  }

end




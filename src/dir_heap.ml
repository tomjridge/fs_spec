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
    #use "dir_heap.toplevel.ml";;


*)
(*
# `dir_heap.ml`
## `Dir_heap_types1` and basic operations

Types for a representation using an inode heap and a dir heap

*)

open Fs_prelude
open Fs_spec

module Dir_heap_types = struct

  open Prelude
  open Fs_types1 (* FIXME remove dependence? have a core types and a state types? *)

  type dir_ref = Dir_ref of int

  let dest_dir_ref s0 (Dir_ref i) = i


  (* a reference to a map of entries *)
  (*
  type entries_ref = Entries_ref of int

  let dest_entries_ref (Entries_ref i) = i
  *)

  type inode_ref = Inode_ref of int

  let dest_inode_ref s0 (Inode_ref i) = i

  (*
  type file_contents_ref = File_contents_ref of int

  let dest_file_contents_ref (File_contents_ref i) = i
  *)

  (* directories *)
  type entry = (dir_ref,inode_ref) sum
  let is_dir_ref_entry = is_Inl
  let is_inode_ref_entry = is_Inr
  let dest_dir_ref_entry = dest_Inl
  let dest_inode_ref_entry = dest_Inr

  module Entries = MyMap(
    struct 
      type key = name
      type value = entry option
      let compare = Pervasives.compare
      let default = None
      let is_default = (fun x -> x=None)
    end)

  type entries = Entries.ty_map (* FIXME in spec? *)

  type dir = {
    dentries:entries;
    parent1:(dir_ref * name) option (* FIXME do we want to allow this? *)
  }

  type inode = {
    fcontents:file_contents;
    is_symlink:bool
  }

  (* state type *)

  module Dir_map = MyMap(
    struct 
      type key = dir_ref
      type value = dir option
      let compare = Pervasives.compare
      let default = None
      let is_default = (fun x -> x=None)
    end)

  module Inode_map = MyMap(
    struct
      type key = inode_ref
      type value = inode option
      let compare = Pervasives.compare
      let default = None
      let is_default = (fun x -> x=None)
    end)

  type state = {
    dirs:Dir_map.ty_map;
    (* entries:Entries_map.ty_map; *)
    inodes:Inode_map.ty_map;
    (* contents:Contents_map.ty_map *)
  }

  let state0' = {
    dirs=Dir_map.empty;
    inodes=Inode_map.empty;
    (* entries=Entries_map.empty;
    contents=Contents_map.empty *)
  }  

  let get_root s0 = (Dir_ref 0)

  (* lift find2 *)
  let lookup_dir s k = Dir_map.find2 k s.dirs
  let (_:state -> dir_ref -> dir option) = lookup_dir

  let lookup_inode s k = Inode_map.find2 k s.inodes
  let (_:state -> inode_ref -> inode option) = lookup_inode


  (* FIXME may prefer a version that returns a (ref,obj) option ; see eg mvdir *)
  let resolve1 s0 d0_ref name = (
    let Some(d0) = lookup_dir s0 d0_ref in
    let m = d0.dentries in
    Entries.find2 name m)
  let (_:state -> dir_ref -> name -> entry option) = resolve1

  (* these update the actual maps *)

  let update_dirs s k v = {s with dirs=(Dir_map.add k v s.dirs) }
  let (_:state -> dir_ref -> dir option -> state) = update_dirs
    
  (*
  let update_entries s k v = {s with entries=(Entries_map.add k v s.entries) }
  let (_:state -> entries_ref -> Entries.ty_map option -> state) = update_entries
  *)

  let update_inodes s k v = {s with inodes=(Inode_map.add k v s.inodes) }
  let (_:state -> inode_ref -> inode option -> state) = update_inodes

  (*
  let update_contents s k v = {s with contents=(Contents_map.add k v s.contents) }
  let (_:state -> file_contents_ref -> bytes option -> state) = update_contents
  *)

  (* common case is to update with Some *)
  let update_drs_some s (k,v) = (update_dirs s k (Some v))
  let update_inds_some s (k,v) = (update_inodes s k (Some v))
  (*
  let update_ents_some s (k,v) = (update_entries s k (Some v))
  let update_cnts_some s (k,v) = (update_contents s k (Some v))
  *)
  

  (*
  let lookup_entries s k = Entries_map.find2 k s.entries
  let (_:state -> entries_ref -> Entries.ty_map option) = lookup_entries
  *)

  (* these add entries to the maps *)
  
  (* r is an entries_ref *)
  let update_ents_pointwise s d0_ref k v = (
    let Some(d0) = lookup_dir s d0_ref in
    let m = d0.dentries in
    let m' = Entries.add k v m in
    let s' = update_drs_some s (d0_ref,{d0 with dentries=m'}) in
    s')
  let (_:state -> dir_ref -> name -> entry option -> state) = update_ents_pointwise
  

  (* FIXME want to use new_dir, not this *)
  let _FIXME_new_dir_ref s = (
    let binds = Dir_map.bindings s.dirs in
    let binds = List.map (fun (k,v) -> dest_dir_ref s k) binds in
    let max = List.fold_left (fun m -> fun r -> max m r) 0 binds in
    Dir_ref(max+1))
 
  let new_dir s0 = (
    let d0_ref = _FIXME_new_dir_ref s0 in
    let d0 = { dentries = Entries.empty; parent1=None } in
    let s0 = update_drs_some s0 (d0_ref,d0) in
    (s0,(d0_ref,d0)))

  let _FIXME_new_inode_ref s = (
    let binds = Inode_map.bindings s.inodes in
    let binds = List.map (fun (k,v) -> dest_inode_ref s k) binds in
    let max = List.fold_left (fun m -> fun r -> max m r) 0 binds in
    Inode_ref(max+1))

  let new_inode s0 = (
    let i0_ref = _FIXME_new_inode_ref s0 in
    let i0 = { fcontents=(MyDynArray.create ()); is_symlink=false } in
    let s0 = update_inds_some s0 (i0_ref,i0) in
    (s0,(i0_ref,i0)))

  let state0 = (
    (* an initial state with a root dir *)
    let root = (Dir_ref 0, { dentries=Entries.empty; parent1=(None) }) in
    let s0 = update_drs_some state0' root in
    s0)  


end

(*
## `Fs_ops1`

Implement the basic file system operations

List of all operations involved in dependencies:

  * creation of a `dir_ref` can be dependent on creation of a new entries (eg `mkdir`)
  * `update_ents_pointwise` (`internal_link_dir` or `internal_link_file`) can be dependent on creation of a new `dir_ref` (and writing of that `dir_ref` into `s0.dirs`) (eg `mkdir`)
  * `internal_link_dir` can be dependent on `update_ents_pointwise` (eg `mkdir`)
  * creation of a new `inode_ref` can be dependent on creation of a new `file_contents` (eg touch)

The defns here only use ops. functions; is this really worth separating?

*)

(* FIXME tidy this up *)
(*
module X = struct

  open Fs_types1
  
  (* hack to get an abstract state type *)
  module Y : sig 
    type t1
    type t2
    type t3
    type t4
    type t5
  end = struct 
    type t1 = int
    type t2 = int
    type t3 = int
    type t4 = int
    type t5 = int
  end 

end
*)

module Fs_ops1 = struct

  open Prelude
  open Fs_types1


  (* might like type operators which pick up the type from a compound type eg. 'a ty_state_ops = { f1:(fst 'a); f2: (fst(snd 'a)) } etc *)
  type ('dir_ref,'dir,'inode_ref,'inode,'state) ty_state_ops = {
    get_init_state: unit -> 'state;
    get_root: 'state -> 'dir_ref option;
    lookup_dir: 'state -> 'dir_ref -> 'dir option;
    lookup_inode: 'state -> 'inode_ref -> 'inode option;
    update_inds_some: 'state -> ('inode_ref * 'inode) -> 'state;
    update_dirs_some: 'state -> ('dir_ref * 'dir) -> 'state;
    resolve1: 'state -> 'dir_ref -> name -> ('dir_ref,'inode_ref) entry option;
    update_ents_pointwise: 'state -> 'dir_ref -> name -> ('dir_ref,'inode_ref) entry option -> 'state;
    new_dir: 'state -> 'dir_ref -> name -> ('state * ('dir_ref * 'dir)); 
    new_inode: 'state -> ('state * ('inode_ref * 'inode)); (* FIXME is dir linked in or not? yes, see mkdir *)
    get_contents: 'inode -> file_contents;
    set_contents: 'inode -> file_contents -> 'inode;
    get_symlink: 'inode -> bool;
    set_symlink: 'inode -> bool -> 'inode;
    dest_inode_ref: 'state -> 'inode_ref -> int;
    dest_dir_ref: 'state -> 'dir_ref -> int;
    get_entries: 'dir -> name list; (* FIXME 'dir -> name list ? *)
    with_parent: 'dir -> ('dir_ref * name) -> 'dir
  }


  (* for the purposes of type-checking the following defns without spurious type vars *)
  module X1 = struct
    type ty_ops' = (X.Y.t1,X.Y.t2,X.Y.t3,X.Y.t4,X.Y.t5) ty_state_ops
    type dir_ref' = X.Y.t1
    type ty_impl' = X.Y.t5
    type inode_ref' = X.Y.t3
    type ty_return' = X.Y.t5 ty_return2
  end
  open X1

  (* FIXME not needed? *)
  (*
  type ('dir_ref,'dir,'inode_ref,'inode,'impl) state = {
    ops3: ('dir_ref,'dir,'inode_ref,'inode,'impl) ty_state_ops;
    s3: 'impl
  }
  *)

  let dest_dir_ref_entry = dest_Inl
  let dest_inode_ref_entry = dest_Inr


  (* link directory d1 into d0 under name *)
  let internal_link_dir ops s0 d0_ref d1_ref name = (
    let d1 = dest_Some(ops.lookup_dir s0 d1_ref) in
    let d1 = ops.with_parent d1 (d0_ref,name) in
    let s0 = ops.update_dirs_some s0 (d1_ref,d1) in
    let s0 = ops.update_ents_pointwise s0 d0_ref name (Some(Inl(d1_ref))) in
    s0)
  let (_:ty_ops' -> ty_impl' -> dir_ref' -> dir_ref' -> name -> ty_impl') = internal_link_dir

  (* FIXME if unlinking a dir, we probably want to set parent to none *)
  let internal_unlink ops s0 d0_ref name = (
    let s0 = ops.update_ents_pointwise s0 d0_ref name None in
    s0)
  let (_:ty_ops' -> ty_impl' -> dir_ref' -> name -> ty_impl') = internal_unlink



  let internal_link_file ops s0 i1_ref d0_ref name = (
    let s0 = ops.update_ents_pointwise s0 d0_ref name (Some(Inr(i1_ref))) in
    s0)
  let (_:ty_ops' -> ty_impl' -> inode_ref' -> dir_ref' -> name -> ty_impl') = internal_link_file



  let link_file ops s0 i1_ref d0_ref name = (
    let s0 = internal_link_file ops s0 i1_ref d0_ref name in
    return s0)
  let (_:ty_ops' -> ty_impl' -> inode_ref' -> dir_ref' -> name -> ty_return') = link_file


  (* FIXME may want to set parent to none if unlinking a dir *)
  let unlink ops s0 d0_ref name = (
    let s0 = internal_unlink ops s0 d0_ref name in
    return s0)
  let (_:ty_ops' -> ty_impl' -> dir_ref' -> name -> ty_return') = unlink


  (* FIXME assumes name doesn't exist *)

  let mkdir ops s0 d0_ref name = (
    let (s0,(d1_ref,d1)) = ops.new_dir s0 d0_ref name in
    (* link d1 into d0 *)
    let s0 = internal_link_dir ops s0 d0_ref d1_ref name in (* FIXME no d1, so d1_ref must already be present after new_dir *)
    return s0)
  let (_:ty_ops' -> ty_impl' -> dir_ref' -> name -> ty_return') = mkdir


  (* FIXME shouldn't this allow the name to be changed? similarly mvdir *)
  (* FIXME this should not allow the same file to be moved to itself - the following code deletes the file! also mvdir *)
  (* FIXME mv -T a.txt d fails if d is a dir, with mv: cannot overwrite directory d with non-directory... even if d is non-empty; but this happens in the user level mv, so may be allowed at syscall? *)

  let mv ops s0 d0_ref name0 d1_ref name1 = (
    let Some(entry) = ops.resolve1 s0 d0_ref name0 in
    let i0_ref = dest_inode_ref_entry entry in
    let s0 = internal_link_file ops s0 i0_ref d1_ref name1 in
    let s0 = internal_unlink ops s0 d0_ref name0 in 
    return s0)
  let (_:ty_ops' -> ty_impl' -> dir_ref' -> name -> dir_ref' -> name -> ty_return') = mv



  (* FIXME change rm and mvdir linkdir to work with files or dirs *)
  (* cannot mvdir a b.txt; cannot mvdir a b if b is not empty *)
  (* FIXME name0 maynot be dir, may not exist FIXME check all uses of dest_dir_ref_entry *)
  (* note doesn't check status of name1 - just does the link *)
  let mvdir ops s0 d0_ref name0 d1_ref name1 = (
    let Some(entry) = ops.resolve1 s0 d0_ref name0 in
    let d2_ref = dest_dir_ref_entry entry in
    let s0 = internal_link_dir ops s0 d1_ref d2_ref name1 in
    let s0 = internal_unlink ops s0 d0_ref name0 in 
    return s0)
  let (_:ty_ops' -> ty_impl' -> dir_ref' -> name -> dir_ref' -> name -> ty_return') = mvdir



  (* FIXME obviously we need to support writing at points in the file etc *)

  (* FIXME read should not return an option - there is always some data by wellformedness *)
  (*
  let read s0 c_ref = (Contents_map.find2 c_ref s0.contents)
  let (_:ty_impl' -> file_contents_ref -> bytes option) = read

  let read_all s0 (i0_ref,i) = (
    let c_ref = i.fcontents in
    let bs = read s0 c_ref in (* FIXME wellformedness? *)
    bs)
  let (_:state -> (inode_ref' * inode) -> bytes option) = read_all  
  *)

  (* FIXME we assume that the bytes are in the map for valid i, don't need option *)
  let read ops s0 i0_ref = (
    let Some(i0) = ops.lookup_inode s0 i0_ref in
    let bytes = ops.get_contents i0 in
    {state2=s0; ret2=(Bytes1 bytes)})
  let (_:ty_ops' -> ty_impl' -> inode_ref' -> ty_return') = read


  let readdir ops s0 d0_ref = (
    let Some(d0) = ops.lookup_dir s0 d0_ref in
    let names = ops.get_entries d0 in
    let names = List.sort Pervasives.compare names in
    {state2=s0; ret2=(Names1 names)})
  let (_:ty_ops' -> ty_impl' -> dir_ref' -> ty_return') = readdir



  let rm ops s0 d0_ref name = (unlink ops s0 d0_ref name)
  let (_:ty_ops' -> ty_impl' -> dir_ref' -> name -> ty_return') = rm


  (* also works for files *)
  let rmdir ops s0 d0_ref name = (unlink ops s0 d0_ref name)
  let (_:ty_ops' -> ty_impl' -> dir_ref' -> name -> ty_return') = rmdir



  (* FIXME assumes name doesn't exist; otherwise leave as is FIXME at moment it overwrites *)

  let touch ops s0 d0_ref name = (
    let (s0,(i0_ref,i0)) = ops.new_inode s0 in 
    let s0 = internal_link_file ops s0 i0_ref d0_ref name in (* i0 must be in s0 already *)
    return s0)
  let (_:ty_ops' -> ty_impl' -> dir_ref' -> name -> ty_return') = touch


  (* FIXME obviously we need to support writing at points in the file etc *)
  let write ops s0 i0_ref c = (
    let Some(i0) = ops.lookup_inode s0 i0_ref in
    let i0 = ops.set_contents i0 c in
    let s0 = ops.update_inds_some s0 (i0_ref,i0) in
    return s0)
  let (_:ty_ops' -> ty_impl' -> inode_ref' -> bytes -> ty_return') = write


  let set_symlink ops s0 i0_ref f = (
    let Some(i0) = ops.lookup_inode s0 i0_ref in
    let i0 = ops.set_symlink i0 f in
    let s0 = ops.update_inds_some s0 (i0_ref,i0) in
    return s0)
  let (_:ty_ops' -> ty_impl' -> inode_ref' -> bool -> ty_return') = set_symlink


end






(*
## Dir heap ops
*)

(* show that dir heap implements the general notion of state *)
module Dir_heap_ops = struct

  open Fs_types1
  open Dir_heap_types
  open Fs_ops1

  let dest_Some = Prelude.dest_Some

  let ops = {
    get_init_state=(fun () -> state0);
    get_root=(fun s0 -> Some (get_root s0));
    lookup_dir=lookup_dir;
    lookup_inode=lookup_inode;
    update_inds_some=update_inds_some;
    update_dirs_some=update_drs_some;
    resolve1=resolve1;
    update_ents_pointwise=update_ents_pointwise;
    new_dir=(fun s0 _d0_ref _name -> new_dir s0);
    new_inode=new_inode;
    get_contents=(fun i0 -> i0.fcontents);
    set_contents=(fun i0 -> fun c -> { i0 with fcontents=c });
    get_symlink=(fun i0 -> i0.is_symlink);
    set_symlink=(fun i0 -> fun b -> { i0 with is_symlink=b });
    dest_dir_ref=dest_dir_ref;
    dest_inode_ref=dest_inode_ref;
    get_entries=(fun d0 -> 
      let es0 = d0.dentries in
      let binds = Entries.bindings es0 in
      (List.map fst binds));
    with_parent=(fun d0 -> fun (d1_ref,n) -> { d0 with parent1=(Some(d1_ref,n)) })
  }

  let ops1 = {
    get_init_state1=(fun () -> state0);
    get_parent1=(fun s0 -> fun d0_ref -> 
      let d0 = dest_Some(ops.lookup_dir s0 d0_ref) in
      (d0.parent1)); (* FIXME do we always know this will return something? disconnected dirs? *)
    get_root1=(fun s0 -> Some (get_root s0));
    dest_dir_ref1=dest_dir_ref;
    dest_inode_ref1=dest_inode_ref;
    get_symlink1=(fun s0 -> fun i0_ref -> 
      let Some(i0) = ops.lookup_inode s0 i0_ref in
      i0.is_symlink);
    link_file1=(link_file ops);
    unlink1=(unlink ops);
    mkdir1=(mkdir ops);
    mv1=(mv ops);
    mvdir1=(mvdir ops);
    read1=(read ops);
    readdir1=(readdir ops);
    resolve11=(ops.resolve1);
    rm1=(rm ops);
    rmdir1=(rmdir ops);
    touch1=(touch ops);
    write1=(write ops);
    set_symlink1=(set_symlink ops);
  }

end


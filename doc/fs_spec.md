# Interactive top-level directives

Via findlib:

    #use "topfind";;
    #require "unix";;
    #require "bigarray";;
    #require "str";;
    (* #cd "/tmp/l/general/research/fs/fs_spec/src";; *)
    #use "fs_prelude.toplevel.ml";;
    #use "fs_spec.toplevel.ml";;
    open Fs_prelude;;
    open Fs_spec;;
    open Fs_spec_everything;;

# fs_spec.ml
## Fs_types1

Types common to all implementations of the basic operations

~~~{.ocaml}

open Fs_prelude

(* as an optimization, we expect that each of these refs is actually a ref to a sector *)

module Fs_types1 = struct

  open Prelude

  type bytes = MyDynArray.t
  type name = string (* shortest component of a filename - doesn't include /; may be empty; may be . or .. *)

  type error =
      E2BIG
    | EACCES
    | EAGAIN
    | EBADF
    | EBUSY
    | ECHILD
    | EDEADLK
    | EDOM
    | EEXIST
    | EFAULT
    | EFBIG
    | EINTR
    | EINVAL
    | EIO
    | EISDIR
    | EMFILE
    | EMLINK
    | ENAMETOOLONG
    | ENFILE
    | ENODEV
    | ENOENT
    | ENOEXEC
    | ENOLCK
    | ENOMEM
    | ENOSPC
    | ENOSYS
    | ENOTDIR
    | ENOTEMPTY
    | ENOTTY
    | ENXIO
    | EPERM
    | EPIPE
    | ERANGE
    | EROFS
    | ESPIPE
    | ESRCH
    | EXDEV
    | EWOULDBLOCK
    | EINPROGRESS
    | EALREADY
    | ENOTSOCK
    | EDESTADDRREQ
    | EMSGSIZE
    | EPROTOTYPE
    | ENOPROTOOPT
    | EPROTONOSUPPORT
    | ESOCKTNOSUPPORT
    | EOPNOTSUPP
    | EPFNOSUPPORT
    | EAFNOSUPPORT
    | EADDRINUSE
    | EADDRNOTAVAIL
    | ENETDOWN
    | ENETUNREACH
    | ENETRESET
    | ECONNABORTED
    | ECONNRESET
    | ENOBUFS
    | EISCONN
    | ENOTCONN
    | ESHUTDOWN
    | ETOOMANYREFS
    | ETIMEDOUT
    | ECONNREFUSED
    | EHOSTDOWN
    | EHOSTUNREACH
    | ELOOP
    | EOVERFLOW
    | EUNKNOWNERR of int
 
  (* from unix.mli *)
  type open_flag =
      O_RDONLY                    (** Open for reading *)
    | O_WRONLY                    (** Open for writing *)
    | O_RDWR                      (** Open for reading and writing *)
    | O_NONBLOCK                  (** Open in non-blocking mode *)
    | O_APPEND                    (** Open for append *)
    | O_CREAT                     (** Create if nonexistent *)
    | O_TRUNC                     (** Truncate to 0 length if existing *)
    | O_EXCL                      (** Fail if existing *)
    | O_NOCTTY                    (** Don't make this dev a controlling tty *)
    | O_DSYNC                     (** Writes complete as `Synchronised I/O data
                                     integrity completion' *)
    | O_SYNC                      (** Writes complete as `Synchronised I/O file
                                     integrity completion' *)
    | O_RSYNC                     (** Reads complete as writes (depending on
                                     O_SYNC/O_DSYNC) *)
    | O_SHARE_DELETE              (** Windows only: allow the file to be deleted
                                   while still open *)

  type file_perm = int


  type file_kind = 
    S_REG                       (** Regular file *)
  | S_DIR                       (** Directory *)
  | S_LNK                       (** Symbolic link *)


  (* top-level labels, intended to mirror the syscalls, but with functional interface; TODO need to incorporate file descriptors, "current position" etc *)
  type ty_label = 
    | LINK of (string * string)
    | MKDIR of (string * file_perm)
    | OPEN of (string * open_flag list)
    | READ of (string * int * int)
    | READDIR of string
    | RENAME of (string * string)
    | RMDIR of string
    | STAT of string
    | SYMLINK of (string * string)
    | TRUNCATE of (string * int)
    | UNLINK of string
    | WRITE of (string * int * bytes * int)

  type file_contents = bytes (* really a map from index to ... *)

  type ret_value = None1 | Int1 of int | Bytes1 of bytes (* FIXME add init return type *) | Names1 of name list
    | Stats1 of Unix.LargeFile.stats
  let dest_bytes1 (Bytes1 bs) = bs
 
  (* names types; also type name earlier *)
  
  (* following moved from ops parser *)
  type dirname = string list
  type filename = string list (* non-empty *)

  (* the type of parsed paths; what is important is whether the name ends with a slash *)
  type ty_name_list2 = {
    ns2: name list;
    ends_with_slash2: bool; 
  }

  (* we cannot supply Fname from user space: a name /tmp/tmp.txt may refer to a file or a dir *)
  (* resolved name *)
  (* type rname1 = Dname1 of name list | Fordname1 of name list *)
  (* resolved name relative to a state *)
  type ('dir_ref,'inode_ref) rname2 = 
    Dname2 of 'dir_ref * ty_name_list2
  | Fname2 of 'inode_ref * ty_name_list2 
  | None2 of ty_name_list2
  | Err2 of 'inode_ref * ty_name_list2 
  (* invariant: if Fname2 ns, then not (ns.ends_with_slash2) *)
  (* invariant: if Err2 then ns.ends_with_slash2 *)
  (* FIXME since these are resolved, we may want to include the i0_ref and d0_ref *)

  let is_Err2 x = (match x with | Err2 _ -> true | _ -> false)

  let name_list_of_rname2 n = (match n with 
    | Dname2 (_,ns) -> ns
    | Fname2 (_,ns) -> ns
    | None2 ns -> ns
    | Err2 (_,ns) -> ns)
 
  let string_of_names ns = ("/"^(String.concat "/" ns))

  let string_of_rname2 n = (
    let ns = name_list_of_rname2 n in
    ((String.concat "/" ns.ns2)^(if ns.ends_with_slash2 then "/" else ""))) (* FIXME shouldn't this start with / ? *)

  let is_None2 x = (match x with None2 _ -> true | _ -> false)




  type ('dir_ref,'inode_ref) entry = ('dir_ref,'inode_ref) sum
  let is_dir_ref_entry = is_Inl
  let is_inode_ref_entry = is_Inr
  let dest_dir_ref_entry = dest_Inl
  let dest_inode_ref_entry = dest_Inr

  (* might like type operators which pick up the type from a compound type eg. 'a ty_state_ops = { f1:(fst 'a); f2: (fst(snd 'a)) } etc *)
  type ('dir_ref,'dir,'inode_ref,'inode,'state) ty_state_ops = {
    get_init_state: unit -> 'state;
    get_root: 'state -> 'dir_ref option;
    lookup_dir: 'state -> 'dir_ref -> 'dir option;
    lookup_inode: 'state -> 'inode_ref -> 'inode option;
    update_inds_some: 'state -> ('inode_ref * 'inode) -> 'state;
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
  }

  (* FIXME not needed? *)
  (*
  type ('dir_ref,'dir,'inode_ref,'inode,'impl) state = {
    ops3: ('dir_ref,'dir,'inode_ref,'inode,'impl) ty_state_ops;
    s3: 'impl
  }
  *)

  type 'impl ty_return2 = {
    state2: 'impl;
    ret2: ret_value;
  } 
  let return s = { state2=s; ret2=None1 }


  type ('dir_ref,'inode_ref,'impl) ty_ops1 = {
    get_init_state1: unit -> 'impl;
    get_root1: 'impl -> 'dir_ref option;
    dest_dir_ref1: 'impl -> 'dir_ref -> int;
    dest_inode_ref1: 'impl -> 'inode_ref -> int;
    get_symlink1: 'impl -> 'inode_ref -> bool;
    link_file1: 'impl -> 'inode_ref -> 'dir_ref -> name -> 'impl ty_return2;
    unlink1: 'impl -> 'dir_ref -> name -> 'impl ty_return2;
    mkdir1: 'impl -> 'dir_ref -> name -> 'impl ty_return2;
    mv1: 'impl -> 'dir_ref -> name -> 'dir_ref -> name -> 'impl ty_return2;
    mvdir1: 'impl -> 'dir_ref -> name -> 'dir_ref -> name -> 'impl ty_return2;
    read1: 'impl -> 'inode_ref -> 'impl ty_return2;
    readdir1: 'impl -> 'dir_ref -> 'impl ty_return2; (* don't return . and .. entries *)
    resolve11: 'impl -> 'dir_ref -> name -> ('dir_ref,'inode_ref) entry option;
    rm1: 'impl -> 'dir_ref -> name -> 'impl ty_return2; (* FIXME don't need this and unlink1 *)
    rmdir1: 'impl -> 'dir_ref -> name -> 'impl ty_return2; (* FIXME probably don't need this either *)
    touch1: 'impl -> 'dir_ref -> name -> 'impl ty_return2;
    write1: 'impl -> 'inode_ref -> bytes -> 'impl ty_return2;
    set_symlink1: 'impl -> 'inode_ref -> bool -> 'impl ty_return2;
  }


end

~~~
## Resolve names

We want to take a string such as `/x/y/z/d/` and process it:

  * extract the components 
  * record whether the string starts in / (* but maybe vfs ensures all strings start in / *)
  * record whether the string ends in /
  * process the string (against the current state) to remove .. and . (providing entries exist; if not return ENOENT; function remove_dot_dotdot) and empty entries
  * then compare result with the current state to determine whether the string
      (1) ends with a / and matches a dir
      (2) ends with a / and matches a file (error)
      (3) doesn't end with a slash and matches a file or dir
      (4) ends with a slash or not, and doesn't match anything

Proposed processing of last step: Ignoring trailing slash, do we match or not? Yes - check agreement with trailing slash (1) and (2) and (3). No - (4)

~~~{.ocaml}

(* FIXME tidy this up *)
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

module Resolve = struct
 
  open Prelude
  open Fs_types1
(*  open Fs_ops1 *)

  (* for the purposes of type-checking the following defns without spurious type vars *)
  module XR = struct
    (* type ty_ops' = (X.Y.t1,X.Y.t2,X.Y.t3,X.Y.t4,X.Y.t5) ty_state_ops *)
    type ty_ops' = (X.Y.t1,X.Y.t3,X.Y.t5) ty_ops1
    type dir_ref' = X.Y.t1
    type ty_impl' = X.Y.t5
    type inode_ref' = X.Y.t3
    type ty_return' = X.Y.t5 ty_return2
    type rname' = (X.Y.t1,X.Y.t3) rname2
  end
  open XR


  (* resolve ns, return a (dir_ref,dir); only used with a resolve *)
  (* these seem to be used as shortcuts for looking up parents of a given path; but we want to ensure some invariants in lists of names; on the other hand, given a rname, to resolve the parent we don't want to have to go via strings *)
  let resolve_dir_ref ops s0 ns = (
    (* sofar is the dir_ref we currently got to; starts off as the root *)
    let rec f1 sofar ns = (match ns with 
      | [] -> (Some sofar)
      | n::ns -> (
        let m = ops.resolve11 s0 sofar n in
        match m with | None -> None | Some entry -> 
        match is_dir_ref_entry entry with | false -> None | true ->
        let dir_ref = dest_dir_ref_entry entry in 
        f1 dir_ref ns))
    in
    let Some(d0_ref) = ops.get_root1 s0 in
    f1 d0_ref ns)
  let (_:ty_ops' -> ty_impl' -> name list -> dir_ref' option) = resolve_dir_ref

  (* let dir_exists ops s0 ns = (resolve_dir_ref ops s0 ns <> None) *)

  (* want to restrict uses of resolve_dir_ref and resolve_inode_ref to this module *)
  let get_parent_dir ops s0 nl = (
    resolve_dir_ref ops s0 (butlast nl.ns2))
  let (_:ty_ops' -> ty_impl' -> ty_name_list2 -> dir_ref' option) = get_parent_dir

  (* ns cannot be empty; FIXME this is only used in resolve *)
  let resolve_inode_ref ops s0 ns = (
    let r = resolve_dir_ref ops s0 (butlast ns) in
    match r with | None -> None | Some dir_ref ->
    let n = last ns in
    let m = ops.resolve11 s0 dir_ref n in
    match m with | None -> None | Some entry -> 
    match is_inode_ref_entry entry with | false -> None | true -> 
    let i0_ref = dest_inode_ref_entry entry in (* assume a file *)
    Some(i0_ref))
  let (_:ty_ops' -> ty_impl' -> name list -> inode_ref' option) = resolve_inode_ref    

  (* let file_exists ops s0 ns = (resolve_inode_ref ops s0 ns <> None) *)

  (* assumes path starts with '/'; throws an exception if not; FIXME do we always know the path starts with '/'? *)

  (* take a string, get components and whether ends in slash *)
  let process_path1 path = (
    let p = explode path in
    if p = [] then failwith "process_path1: empty path" else
    if List.hd p <> "/" then failwith "process_path: doesn't start with /" else
    let p = List.tl p in
    let f1 (ns,cur) c = (if c="/" then (ns@[cur],"") else (ns,cur^c)) in
    let (ns,cur) = List.fold_left f1 ([],"") p in
    let ends_with_slash = (cur="") in
    let ns = (if ends_with_slash then ns else ns@[cur]) in (* FIXME this logic is wrong? if multiple slashes? *)
    let ns = List.filter (fun n -> n <> "." && n <> "") ns in (* remove empty entries and "." entries *)
    { ns2=ns; ends_with_slash2=ends_with_slash })
  let (_:string -> ty_name_list2) = process_path1

  (* preliminary processing of ns; drop empty components and "." components, and resolve ".." *)
  (* idempotent *)
  (* FIXME this is only OK if the e.g. d/../x/y/z we have that d exists FIXME do not use! *)
  let process_dotdot ops s0 nl = (
    let f1 sofar n = (
      if (n=".." && sofar <> []) then 
        (butlast sofar) 
      else if (n=".." && sofar = []) then
        (failwith "process_dot_dotdot")
      else
        (sofar@[n])) 
    in
    let ns = List.fold_left f1 [] nl.ns2 in
    {nl with ns2=ns})
  let (_:ty_ops' -> ty_impl' -> ty_name_list2 -> ty_name_list2) = process_dotdot 

  (* take a state and a ty_name_list2, and check if name exists in state *)
  let process_path2 ops s0 ns = (
    (* FIXME we need to process .. here as well *)
    match ns.ends_with_slash2 with 
    | true -> (
      let opt = resolve_dir_ref ops s0 ns.ns2 in
      match opt with 
      | Some(dir_ref) -> Dname2(dir_ref(*,dest_Some(ops.lookup_dir s0 dir_ref))*),ns)
      | None -> (
        let opt = resolve_inode_ref ops s0 ns.ns2 in 
        match opt with
        | None -> None2 ns
          (* following case, ns ends with a slash, but resolves to a file *)
        | Some(iref) -> Err2(iref(*,dest_Some(ops.lookup_inode s0 iref))*),ns)))
    | false -> (
      let opt = resolve_dir_ref ops s0 ns.ns2 in
      match opt with
      | Some(dir_ref) -> Dname2(dir_ref(*,dest_Some(ops.lookup_dir s0 dir_ref))*),ns)
      | None -> (
        let opt = resolve_inode_ref ops s0 ns.ns2 in
        match opt with 
        | Some(iref) -> Fname2(iref(*,dest_Some(ops.lookup_inode s0 iref)*),ns)
        | None -> None2 ns)))
  let (_:ty_ops' -> ty_impl' -> ty_name_list2 -> rname') = process_path2

  (* guarantees: returns option of Fname or Dname  *)
  let process_path ops s0 path = (
    let nl = process_path1 path in
    let nl = process_dotdot ops s0 nl in
    let rpath = process_path2 ops s0 nl in
    rpath)  
  let (_:ty_ops' -> ty_impl' -> string -> rname') = process_path

  (* FIXME we want subsequent defns to work in terms of rname, and possible ty_name_list2; we want invariants on these *)

  let rec list_prefix xs ys = (
    match (xs,ys) with
    | ([],_) -> true
    | (_,[]) -> false
    | (x::xs,y::ys) -> (
      if (x=y) then list_prefix xs ys else false))

  (* check if renaming a dir to a subdir of itself *)
  let subdir nl_src nl_dst = (list_prefix nl_src.ns2 nl_dst.ns2)

end

~~~
## `Fs_ops2`

Fs ops is very precise about what each argument is expected to be. Dirnames start and end in `/`. Filenames must not end in `/`. We don't check that the target of a `mv` is empty, or doesn't exist etc. However, at the command line, there is some ambiguity:

  * assuming `tmp.txt` is a file, then `mv tmp.txt d` will treat `d` as a file (if no d exists), or as a dir (if d exists and is a dir)

  * `mv tmp.txt d/` will treat `d/` as a dir always

So some possible sources of ambiguity are:
 
  * is `tmp.txt` a file or a directory? (if it exists, then it is whatever it is)

  * if we mean a dir, we can add a '/', and this makes clear what we mean; if we don't add a '/' then the fs may not know whether we intend a file or directory

  * even if we are clear that we mean a dir, there can be multiple interpretations: `mv c/ e/` renames c to e, providing e doesn't already exist; if e does exist, then c goes into e

  * `mv c/ e/` will overwrite a directory `e/c` if `e/c` is empty; will fail if `e/c` is not empty

At the user level, there is some extra logic which makes commands behave differently eg if the target is absent, or a file, or a directory eg for the command `mv src dst`

  * if src is a file, and dst is a dir, then src is moved into dir

  * if src if a file and dst is a file, then src is moved over dst (dst is unlinked)

  * if src is a dir and dst is a dir, then 

Some criteria: 

  * src,dst ends in '/'

  * src,dst exists/not exists  (but how to connect name to entity? the point is that this connection is heuristic in some sense; proposal: given a fordname, check whether a dir exists with that name; if not, attempt to interpret as file)

  * src,dst exists and is a file/ is a dir


Proposed `mv` processing stages:

 1. if either src or dst is fordname (no trailing /) then try to disambiguate: if directory src exists, then src is a dirname, otherwise filename; from this point onwards, we use "src" to indicate a filename, and "src/" to indicate a dirname

    `mv src dst/`: move file src to dst directory; if src doesn't exist, fail; if dst directory doesn't exist, fail

    `mv src/ dst`: move directory src to directory dst; dst directory doesn't exist by disambiguation (otherwise the command would have been interpreted as `mv src/ dst/`); fail if src doesn't exist

    `mv src dst`: move file src to file dst; if src doesn't exist, fail

    `mv src/ dst/`: if `dst` exists, then attempt to move dir src to a subdirectory of dst; if `dst/src` file exists, overwrite; if `dst/src` dir exists, and is empty, then do the move, otherwise fail


Note: these options don't even include checking whether src and dst are soft links (which further complicates matters; FIXME we don't deal with soft links at this stage)

For the moment, we content ourselves with the following horrible code...

For `Fs_ops2` we provide functions from state to Inl of state * err, or Inr of state * ret

--

Invariant: if any exception is raised, the state is not changed

~~~{.ocaml}

(* FIXME these work in terms of rnames; assumes no Err2 *)
module Fs_ops2 = struct
  
  open Unix (* for st_dev record fields etc *)
  open LargeFile (* FIXME include stats in Fs_types1? *)

  open Prelude
  open Fs_types1
(*  open Fs_ops1 *)
  (* open Resolve *)

  let get_parent_dir = Resolve.get_parent_dir
  let resolve_process_path2 = Resolve.process_path2
  let resolve_subdir = Resolve.subdir

  (* type error = Fs_types1.error *)
  type ('impl,'a) ty_return3 = (('impl * Fs_types1.error, 'impl * 'a) sum) finset
  (* vars u, v used eg for Mymonad u *)
  type ('impl,'a) mymonad = Mymonad of ('impl -> ('impl,'a) ty_return3)
  let dest_mymonad (Mymonad u) = u
  let return x = Mymonad (fun s -> finset_insert (Inr(s,x)) finset_empty)
  let (_:'a -> ('impl,'a) mymonad) = return

  (* for the purposes of type-checking the following defns without spurious type vars *)
  (* N.B. these dummy X module defns are interesting because they show what types are used in each module *)
  module X2 = struct
    type 'a ty_return3' = (X.Y.t5,'a) ty_return3
    type 'a ty_mymonad' = (X.Y.t5,'a) mymonad
    type rname2' = (X.Y.t1,X.Y.t3) rname2    
    (* type ty_ops' = (X.Y.t1,X.Y.t2,X.Y.t3,X.Y.t4,X.Y.t5) ty_state_ops *)
    type ty_ops' = (X.Y.t1,X.Y.t3,X.Y.t5) ty_ops1
  end
  open X2

  let bind u f = Mymonad (fun s0 ->
    let u = dest_mymonad u in
    let rs = u s0 in
    let f1 v = (match v with 
      | Inl x -> (finset_singleton (Inl x))
      | Inr (s,x) -> (
        let v = dest_mymonad (f x) in
        v s))
    in
    let rs' = finset_image f1 rs in
    let rs'' = finset_bigunion rs' in
    rs'')    
  let (_: 'a ty_mymonad' -> ('a -> 'b ty_mymonad') -> 'b ty_mymonad') = bind

  (* FIXME we also want to bake in that as soon as we have an exception, we will not alter the state further *)

  let ( >>= ) = bind
  
  let get_state = Mymonad (fun (s) -> finset_singleton(Inr(s,s)))
  let put_state s0 = Mymonad (fun (s) -> finset_singleton(Inr(s0,None1)))
  let myraise e = Mymonad (fun (s) -> finset_singleton(Inl(s,e)))
  let maybe_raise e = Mymonad (fun (s) -> 
    finset_insert (Inr(s,())) (finset_singleton(Inl(s,e))))

  let choose xs = Mymonad (fun s -> finset_image (fun x -> Inr(s,x)) xs)

  (* for a deterministic version, choose some particular value *)
  let choose xs = Mymonad (fun s -> finset_singleton(Inr(s,finset_choose xs)))

  let do_nothing = Mymonad (fun s -> finset_singleton(Inr(s,())))

  let run_mymonad (Mymonad f) s = (f (s))
  let (_:('a,'b) mymonad -> 'a -> ('a,'b) ty_return3) = run_mymonad
  
  (*  let is_empty_dir (s0:'impl) ns = failwith "FIXME" *)

  let default_stats = {
    st_dev = 2049; (* device number FIXME 0? *)
    st_ino = 999; (* inode number FIXME change this for particular file etc *)
    st_kind = Unix.S_DIR; (* FIXME *)
    st_perm = 0o777; (* ugo+rwx *)
    st_nlink = 2; (* FIXME dummy - for dir should be number of entries + 2 *)
    st_uid = 1000; (* FIXME 0? *)
    st_gid = 1000; 
    st_rdev = 0; (* device minor number *)
    st_size = 4096L; (* FIXME dummy *)
    st_atime = 0.;
    st_mtime = 0.;
    st_ctime = 0.
  }

  let default_file_stats ops s0 i0_ref = { default_stats with
    st_ino=(ops.dest_inode_ref1 s0 i0_ref);
    st_kind=(
      if (ops.get_symlink1 s0 i0_ref) then Unix.S_LNK else Unix.S_REG); (* FIXME we may need our own stats structure *)
    st_size=(
      let bs = dest_bytes1 ((ops.read1 s0 i0_ref).ret2) in
      (Int64.of_int (MyDynArray.dim bs)))
  }
 
  let default_dir_stats ops s0 d0_ref = { default_stats with
    st_ino=(ops.dest_dir_ref1 s0 d0_ref);
    st_kind=Unix.S_DIR;
    st_size=4096L; (* seems to be default on my system - but changes depending on number of entries? *)
  }

  (* Fs_ops1 returns ty_return3, which apart from read is just a state *)
  let put_state' r = put_state r.state2

  (* FIXME remove *)
  let put_state'' f = (put_state' (f ()))

  let link ops spath dpath = (
    get_state >>= fun s0 ->
    match spath with 
    | Fname2(i0_ref,ns_src)  -> (
      match dpath with 
      | None2 ns_dst -> (
        let Some(d0_ref) = get_parent_dir ops s0 ns_dst in
        let s0 = ops.link_file1 s0 i0_ref d0_ref (last ns_dst.ns2) in
        put_state' s0)
      | _ -> (myraise EEXIST))
    | _ -> (myraise ENOENT))

  let mkdir ops rpath perms = (
    (* FIXME deal with perms *)
    get_state >>= fun s0 ->
    match rpath with 
    | None2(ns) -> (
      let Some(d0_ref) = get_parent_dir ops s0 ns in
      let s0 = ops.mkdir1 s0 d0_ref (last ns.ns2) in
      put_state' s0)
    | Dname2(_,_) -> (myraise EEXIST)
    | Fname2(_,_) -> (myraise EEXIST))

  let open_create ops rpath = (
    get_state >>= fun s0 ->
    match rpath with 
    | Dname2(_,_) -> (myraise EEXIST) 
    | Fname2(_,_) -> (myraise EEXIST)
    | None2 ns -> (
      (* FIXME for us, open_create should only create files *)
      if ns.ends_with_slash2 then 
        myraise EISDIR
      (* maybe we are trying to create a file "" ie path was empty FIXME where is this from? *)
      else if ns.ns2 = [] then 
        myraise ENOENT
      (* FIXME need to look at mode *)
      else
        let dname = butlast ns.ns2 in
        let fname = last ns.ns2 in
        (* FIXME following is unusual *)
        let dpath = resolve_process_path2 ops s0 { ns2=dname; ends_with_slash2=false } in
        match dpath with
        | Dname2(d0_ref,ns) -> (
          let s0 = ops.touch1 s0 d0_ref fname in
          put_state' s0)
      | Fname2(_,_) -> (myraise ENOTDIR)
      | _ -> (myraise ENOENT)))
  let (_:ty_ops' -> rname2' -> ret_value ty_mymonad') = open_create

  (* FIXME the real spec would allow reading less than all the bytes; recall len is maxlen *)
  let read ops rname2 ofs len = (
    match rname2 with 
    | None2 _ -> (myraise ENOENT)
    | Dname2(_,_) -> (myraise ENOENT)
    | Fname2(i0_ref,ns) -> (
      get_state >>= (fun s0 -> (
      let r = ops.read1 s0 i0_ref in (* FIXME Fs_ops1 may have to take an offset too *)
      (put_state' r) >>= fun _ -> 
      (* non-deterministically choose the amount of data to write *)
      choose (downto' len 0) >>= fun len ->
      let bs = dest_bytes1 r.ret2 in
      let len_bs = MyDynArray.dim bs in
      (* assume ofs is wellformed *)
      let len = if ofs+len <= len_bs then len else len_bs - ofs in
      (* let _ = print_endline ("read len_bs: "^(string_of_int len_bs)^"; len: "^(string_of_int len)^"; ofs: "^(string_of_int ofs)) in *)
      (* let _ = print_endline "before" in *)
      let bs' = MyDynArray.sub bs ofs len in
      (* let _ = print_endline "after" in *)
      return (Bytes1(bs'))))))
  let (_:ty_ops' -> rname2' -> int -> int -> ret_value ty_mymonad') = read

  (* NB doesn't include . and .. *)
  let readdir ops rname2 = (
    get_state >>= (fun s0 -> (
    match rname2 with 
    | None2 _ -> (myraise ENOENT) (* (raise (Unix_error (ENOENT,"readdir","/FIXMEreaddir"))) (* FIXME we may need access to the underlying path that was given by the user *) *)
    | Fname2 _ -> (myraise ENOTDIR) (* (raise (Unix_error (ENOTDIR,"readdir","/FIXMEreaddir"))) *)
    | Dname2(d0_ref,ns) -> (
      let r = ops.readdir1 s0 d0_ref in
      (put_state' r) >>= (fun _ -> (
      return r.ret2))))))
  let (_:ty_ops' -> rname2' -> ret_value ty_mymonad') = readdir
  (* NB later we may want to also return a state, given access times can cause changes when reading etc *)

  (* FIXME surely a lot of this complexity is because this is the user land behaviour of the mv command - but we want to target the syscall interface *)
  (* FIXME we probably want the containing dirs as well, when doing rename; put this in resolve *)
  (* FIXME rename to subdir of self? *)
  let rename ops rsrc rdst = (
    get_state >>= (fun s0 -> 
    match rsrc with
    | None2 _ -> (myraise ENOENT) (* no src file *)
    | Err2 (_,_) -> (myraise ENOTDIR)
    | Fname2 (i0_ref,ns_src) -> (
      match rdst with 
      | None2 ns_dst -> (
        (* do the move; there is no file ns_dst *)
        (* FIXME check rename to target where parent doesn't exist *)
        match get_parent_dir ops s0 ns_dst with
        | None -> (myraise ENOENT) (* parent dir of dst doesn't exist *)
        | Some(d1_ref) -> (
          let Some(d0_ref) = get_parent_dir ops s0 ns_src in
          put_state'' (fun () -> ops.mv1 s0 d0_ref (last ns_src.ns2) d1_ref (last ns_dst.ns2))))
      | Fname2 (i1_ref,ns_dst) -> (
        (* do the move; there is a file name ns_dst *)
        let Some(d0_ref) = get_parent_dir ops s0 ns_src in
        let Some(d1_ref) = get_parent_dir ops s0 ns_dst in
        if (ns_dst.ns2=ns_src.ns2) then 
          return None1 
        else
          put_state'' (fun () -> ops.mv1 s0 d0_ref (last ns_src.ns2) d1_ref (last ns_dst.ns2)))
        (* FIXME may want to have putstate return a void value *)
      | Dname2 (d0_ref,ns_dst) -> (
        (* several reasonable options *)
        (* arguably a Linux bug? *)
        (if (ns_dst.ends_with_slash2) then 
          maybe_raise ENOTDIR 
        else 
          do_nothing) >>= (fun _ -> 
        if ((ops.readdir1 s0 d0_ref).ret2=Names1[]) then 
          myraise EISDIR
        else
           myraise ENOTEMPTY))
      | Err2(_,_) -> (
        myraise ENOTDIR))
    | Dname2 (d0_ref,ns_src) -> (
      (* directory exists *)
      match rdst with
      | None2 ns_dst -> (
        (* do the move; there is no file ns_dst *)
        let Some(d0_ref) = get_parent_dir ops s0 ns_src in
        match get_parent_dir ops s0 ns_dst with
        | None -> (myraise ENOENT) (* parent dir of dst doesn't exist *)
        | Some(d1_ref) -> (
          if (resolve_subdir ns_src ns_dst) then 
            myraise EINVAL
          else
            put_state'' (fun () -> ops.mvdir1 s0 d0_ref (last ns_src.ns2) d1_ref (last ns_dst.ns2))))
      | Err2 (_,_) -> (myraise ENOTDIR)
      | Fname2 (_,ns_dst) -> (
        (* check rename to subdir before rename to file; NB there are different reasonable options here *)
        (if (resolve_subdir ns_src ns_dst) then
          maybe_raise EINVAL 
        else 
          do_nothing) >>= (fun _ -> 
        myraise ENOTDIR)) (* arguably this is a bug in linux? *)
      | Dname2 (d1_ref,ns_dst) -> (
        (* if same dir, return silently *)
        if (d1_ref=d0_ref) then
          (return None1)
        (* FIXME check if renaming to a subdir *) (* FIXME following two exceptions should be maybe_raise *)
        else if (resolve_subdir ns_src ns_dst) then 
          (myraise EINVAL)
        (* FIXME check if dir not empty *)
        else if ((ops.readdir1 s0 d1_ref).ret2<>Names1[]) then 
          (myraise ENOTEMPTY) 
        (* otherwise target dir is empty; do rename; FIXME presumably root, if empty, can't be target unless src=root *)
        (* FIXME with the unix backend, we really don't want to execute this last because we know we are going to raise an error; but we must allow for future stages to raise further exceptions *)
        else
          let Some(d0_ref) = get_parent_dir ops s0 ns_src in
          let Some(d1_ref) = get_parent_dir ops s0 ns_dst in
          put_state'' (fun () -> ops.mvdir1 s0 d0_ref (last ns_src.ns2) d1_ref (last ns_dst.ns2))))))
  let (_:ty_ops' -> rname2' -> rname2' -> ret_value ty_mymonad') = rename      

  let rmdir ops rpath = (
    get_state >>= fun s0 ->
    match rpath with 
    | Dname2(_,ns) -> (
      (* FIXME for resolving a file, often useful to have dir ref as well *)
      let Some(d0_ref) = get_parent_dir ops s0 ns in
      let s0 = ops.unlink1 s0 d0_ref (last ns.ns2) in
      put_state' s0)
    | Fname2 _ -> (myraise ENOTDIR)
    | None2 _ -> (myraise ENOENT))

  let stat ops rname2 = (
    get_state >>= (fun s0 -> (
    (* let _ = (print_endline ("stat: "^(string_of_rname2 rname2))) in *)
    match rname2 with
    | None2 _ -> (myraise ENOENT)  (* (raise (Unix_error (ENOENT,"stat","/FIXMEstat"))) *)
    | Fname2(i0_ref,ns) -> (return (Stats1 (default_file_stats ops s0 i0_ref)))
    | Dname2(d0_ref,ns) -> (return (Stats1 (default_dir_stats ops s0 d0_ref)))))) (* FIXME remove ops arg from default_dir_stats *)
  let (_:ty_ops' -> rname2' -> ret_value ty_mymonad') = stat

  let truncate ops rpath len = (
    get_state >>= fun s0 ->
    match rpath with 
    | None2 _ -> (myraise ENOENT)
    | Dname2(_,_) -> (myraise EISDIR) (* FIXME check error messages are sensible *)
    | Fname2(i0_ref,ns) -> (
      let r = ops.read1 s0 i0_ref in
      let bs = dest_bytes1 r.ret2 in
      (* create a new array, of length len, with same contents *)
      let bs' = MyDynArray.resize bs len in
      let s0 = ops.write1 s0 i0_ref bs' in
      put_state' s0))
  let (_:ty_ops' -> rname2' -> int -> ret_value ty_mymonad') = truncate

  let unlink ops rpath = (
    get_state >>= fun s0 ->
    match rpath with 
    | None2(_) -> (myraise ENOENT)
    | Dname2(_,_) -> (myraise EISDIR)
    | Fname2(i0_ref,ns) -> (
      (* FIXME for resolving a file, often useful to have dir ref as well *)
      let Some(d0_ref) = get_parent_dir ops s0 ns in
      let s0 = ops.unlink1 s0 d0_ref (last ns.ns2) in
      put_state' s0))

  (* FIXME we need to make this take an offset in order to be usable, also read *)
  let write ops rname2 ofs bs len = (
    get_state >>= fun s0 -> 
    match rname2 with 
    | None2 _ -> (myraise ENOENT) (* (raise (Unix_error (ENOENT,"read","/FIXMEwrite"))) *)
    | Dname2(_,_) -> (myraise ENOENT) (* (raise (Unix_error (ENOENT,"read","/FIXMEwrite"))) *)
    | Fname2(i0_ref,ns) -> (
      choose (downto' len 0) >>= fun len ->
      let r = ops.read1 s0 i0_ref in
      let bs' = dest_bytes1 r.ret2 in
      (* want to create a new array from bs' and bs *)
      let bs'' = MyDynArray.write (bs,0,len) (bs',ofs) in
      let r = ops.write1 s0 i0_ref bs'' in
      put_state' r >>= fun _ -> 
      return (Int1 len)))
  let (_:ty_ops' -> rname2' -> int -> file_contents -> int -> ret_value ty_mymonad') = write


end

~~~
## `Fs_ops3`

This works in terms of strings; handles Err2 on resolving 

~~~{.ocaml}

(* FIXME check mv if src=dst *)
module Fs_ops3 = struct 

  open Fs_types1
  open Resolve
  open Fs_ops2


  (* for the purposes of type-checking the following defns without spurious type vars *)
  module X3 = struct 
    type 'a ty_return3' = (X.Y.t5,'a) ty_return3
    type 'a ty_mymonad' = (X.Y.t5,'a) mymonad
    type rname2' = (X.Y.t1,X.Y.t3) rname2    
    (* type ty_ops' = (X.Y.t1,X.Y.t2,X.Y.t3,X.Y.t4,X.Y.t5) ty_state_ops *)
    type ty_ops' = (X.Y.t1,X.Y.t3,X.Y.t5) ty_ops1
  end
  open X3

  let link ops src dst = (
    get_state >>= fun s0 -> 
    let rsrc = process_path ops s0 src in
    let rdst = process_path ops s0 dst in
    if (is_Err2 rsrc || is_Err2 rdst) then (myraise ENOTDIR) else Fs_ops2.link ops rsrc rdst)

  let mkdir ops path perms = (
    get_state >>= fun s0 ->
    let rpath = process_path ops s0 path in
    if (is_Err2 rpath) then (myraise ENOTDIR) else Fs_ops2.mkdir ops rpath perms)

  (* FIXME we have to take care of flags eg O_TRUNC *)
  (* FIXME return is int option - meaning optional file handle? *)
  (* FIXME why is this called fopen (taking an fd?) rather than open? *)
  (* FIXME the mapping between fds and files is handled elsewhere - needs a new part of spec *)
  let _open ops path flags = (
    get_state >>= fun s0 ->
    let rpath = process_path ops s0 path in
    match rpath with
    | None2 _ -> (myraise ENOENT)
    | Dname2(_,_) -> (myraise ENOENT) (* FIXME? can we open a dir? *)
    | _ -> (return None1))
  let (_:ty_ops' -> string -> 'a -> ret_value ty_mymonad') = _open
 
  (* open call returns an fd; but may have side effects; open create is one such call; FIXME what are others? *)
  let open_create ops path = (
    get_state >>= fun s0 ->
    let rpath = process_path ops s0 path in
    if (is_Err2 rpath) then (myraise ENOTDIR) else Fs_ops2.open_create ops rpath)

  (* N.B. for read and write ofs is associated with fd, so presumably < len of file *)
  let read ops path ofs len = (
    get_state >>= fun s0 ->
    let rpath = process_path ops s0 path in
    if (is_Err2 rpath) then (myraise ENOTDIR) else Fs_ops2.read ops rpath ofs len)
  
  let readdir ops path = (
    get_state >>= fun s0 ->
    let rpath = process_path ops s0 path in
    if (is_Err2 rpath) then (myraise ENOTDIR) else Fs_ops2.readdir ops rpath)

  (* FIXME check do_rename against ops2.rename; also check against doc in linux sys programming *)
  let rename ops src dst = (
    get_state >>= fun s0 -> 
    let rsrc = process_path ops s0 src in
    let rdst = process_path ops s0 dst in
    Fs_ops2.rename ops rsrc rdst)
  let (_:ty_ops' -> string -> string -> ret_value ty_mymonad') = rename

  let rmdir ops path = (
    get_state >>= fun s0 ->
    let rpath = process_path ops s0 path in
    if (is_Err2 rpath) then (myraise ENOTDIR) else Fs_ops2.rmdir ops rpath)

  let stat ops path = (
    get_state >>= fun s0 ->
    let rpath = process_path ops s0 path in
    if (is_Err2 rpath) then (myraise ENOTDIR) else Fs_ops2.stat ops rpath)

  let truncate ops path len = (
    get_state >>= fun s0 ->
    let rpath = process_path ops s0 path in
    if (is_Err2 rpath) then (myraise ENOTDIR) else Fs_ops2.truncate ops rpath len)

  let unlink ops path = (
    get_state >>= fun s0 ->
    let rpath = process_path ops s0 path in
    if (is_Err2 rpath) then (myraise ENOTDIR) else Fs_ops2.unlink ops rpath)

  let write ops path ofs bs len = (
    get_state >>= fun s0 ->
    let rpath = process_path ops s0 path in
    if (is_Err2 rpath) then (myraise ENOTDIR) else Fs_ops2.write ops rpath ofs bs len)

  (* FIXME this is a hack - should do lots of checking eg src is a dir *)
  let symlink ops src dst = (
    open_create ops dst >>= fun _ -> 
    write ops dst 0 (MyDynArray.of_string src) (String.length src) >>= fun _ -> 
    get_state >>= fun s0 ->
    let rpath = process_path ops s0 dst in
    let Fname2(i0_ref,_) = rpath in
    let r = ops.set_symlink1 s0 i0_ref true in
    put_state' r)
  let (_:ty_ops' -> string -> string -> ret_value ty_mymonad') = symlink    

end


~~~
## Transition system

The model is of a labelled transition system from state to state, but
where each transition may result in a return to userland (of a value
or an error). FIXME need to be non-determinisitic eg in write and read
behaviour.

~~~{.ocaml}

module Transition_system = struct

  open Prelude 
  open Fs_types1
  open Fs_ops2
  open Fs_ops3

  module X4 = struct 
    (* for the purposes of type-checking the following defns without spurious type vars *)
    (* type ty_ops' = (X.Y.t1,X.Y.t2,X.Y.t3,X.Y.t4,X.Y.t5) ty_state_ops *)
    type ty_ops' = (X.Y.t1,X.Y.t3,X.Y.t5) ty_ops1
    type state' = X.Y.t5
  end
  open X4

  (* the transition function takes a state, a label, and returns an updated state with a possible value returned, or an error *)
  (* FIXME readlink is just read, but may want to have a separate label *)
  let trans ops s0 lbl = (
    (* let _ = print_endline (string_of_label lbl) in *)
    let m = (match lbl with 
      | LINK (s,d) -> (link ops s d)
      | MKDIR (s,p) -> (mkdir ops s p)
      | OPEN (p,fs) -> (
          if (List.mem O_CREAT fs) then (open_create ops p (* FIXME fs *)) 
          else (_open ops p fs))
      | READ (p,i,j) -> (read ops p i j)
      | READDIR p -> (readdir ops p)
      | RENAME (s,d) -> (rename ops s d)
      | RMDIR p -> (rmdir ops p)
      | STAT p -> (stat ops p)
      | SYMLINK (s,d) -> (symlink ops s d)
      | TRUNCATE (p,l) -> (truncate ops p l)
      | UNLINK p -> (unlink ops p)
      | WRITE (p,ofs,bs,len) -> (write ops p ofs bs len))
    in
    let rs = run_mymonad m s0 in
    let f1 ve = (match ve with
      | Inl(s,e) -> (s,Inl e)
      | Inr(s,v) -> (s,Inr v))
    in
    let rs = List.map f1 rs in
    rs)
  let (_:ty_ops' -> state' -> ty_label -> (state' * (error,ret_value)sum) finset) = trans
  
  (* convenience method to process a list of labels; always choose first possible result (state,e+v) *)
  let process_labels ops s0 lbls = (
    let f1 = (fun xs -> fun lbl -> 
      let l = last xs in
      let (_,_,(s,_)) = l in
      let rs = trans ops s lbl in
      let _ = if rs = finset_empty then failwith "process_labels: no result state" else () in
      let (s',v) = finset_choose rs in
      xs@[(List.length xs,lbl,(s',v))])
    in
    let dummy_lbl = LINK("dummy lbl","dummy lbl") in
    let dummy_error_or_value = Inr None1 in
    List.fold_left f1 [(0,dummy_lbl,(s0,dummy_error_or_value))] lbls)
  let (_:ty_ops' -> state' -> ty_label list -> (int * ty_label * (state' * (error,ret_value)sum)) list) = process_labels

end

~~~
## `Fs_spec_everything`
~~~{.ocaml}

module Fs_spec_everything = struct

  include Fs_prelude
  include Prelude
(*  include File_utils *)
  include Fs_types1
(*  include Lift *)
(*  include Common *)
(*  include Fs_ops1 *)
  include Resolve
  include Fs_ops2
  include Fs_ops3
  include Transition_system

end

~~~
## Debug
~~~{.ocaml}
(* FIXME do we need to generalize this over ops? yes probably *)
module Debug = struct
  
  open Prelude
  open Fs_types1

(*
  let string_of_entry e = (
    let i = (match e with
    | Inl dref -> (string_of_int (dest_dir_ref dref))
    | Inr iref -> (string_of_int (dest_inode_ref iref)))
    in
    "("^i^")")
*)

  let rec string_of_dir ops s0 dirname d0_ref = (
    let Some(d0) = ops.lookup_dir s0 d0_ref in
    let ns = ops.get_entries d0 in
    let is_file ops s0 d0_ref n = (
      let Some(e) = ops.resolve1 s0 d0_ref n in
      is_inode_ref_entry e)
    in
    let is_dir ops s0 d0_ref n = (not (is_file ops s0 d0_ref n)) in
    let this_dir = (String.concat "\n" (List.map (fun n -> n) ns)) in    
    let this_dir = if ns <> [] then this_dir ^ "\n" else this_dir in
    let other_dirs = List.filter (fun n -> is_dir ops s0 d0_ref n) ns in
    let f1 n = (
      let Some(e) = ops.resolve1 s0 d0_ref n in
      let d1_ref = dest_dir_ref_entry e in
      string_of_dir ops s0 (dirname ^ "/" ^ n) d1_ref)
    in
    let others = List.map f1 other_dirs in
    "Directory "^dirname^":\n"
    ^ this_dir
    ^ (String.concat "" others))
    
  (* assume no cycles *)
  let string_of_state ops s = (
    let Some(d0_ref) = ops.get_root s in
    (string_of_dir ops s "/" d0_ref))

end



~~~

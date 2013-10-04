module Fs_spec = struct 
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
    open Fs_prelude;;
    open Fs_spec;;
    open Fs_spec_everything;;

*)
(*
# fs_spec.ml
## Fs_types1

Types common to all implementations of the basic operations

*)

open Fs_prelude

(* as an optimization, we expect that each of these refs is actually a ref to a sector *)

module Fs_types1 = struct

  open Prelude

  type num = int (* FIXME; also fix uses of type int below to be num where appropriate *)

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

  type ('dir_ref,'inode_ref) entry = ('dir_ref,'inode_ref) sum
  let is_dir_ref_entry = is_Inl
  let is_inode_ref_entry = is_Inr
  let dest_dir_ref_entry = dest_Inl
  let dest_inode_ref_entry = dest_Inr

  (* break the string into components *)
  type ty_name_list = {
    ns2: name list; (* invariant: not [] *)
  }
  (* let ends_with_slash nl = nl.ends_with_slash2 *)

  (* process . and .. and empty entries relative to a cwd *)
  type ('dir_ref,'inode_ref) ty_realpath1 = {
    cwd3: 'dir_ref; (* cwd for process *)
    nl3: ty_name_list; (* the original string *)
    ns3: name list; (* invariant: not []; first entry is empty; no . and .. entries; no further empty entries (absolute paths) *)
    (* FIXME we don't need e3  if we are interested in paths *)                                  
                                  (* e3: (('dir_ref,'inode_ref) entry,name)sum (* inr means that the path might target a non-existent file or directory, but everything else resolved *) *)
  }
  type ('dir_ref,'inode_ref) ty_realpath = OK1 of ('dir_ref,'inode_ref) ty_realpath1 | Err1 of (error * ty_name_list)
                       
  (* resolved name relative to a state *)
  type ('dir_ref,'inode_ref) res_name = 
    Dname2 of ('dir_ref * ('dir_ref,'inode_ref) ty_realpath1)
  | Fname2 of ('dir_ref * name * 'inode_ref * ('dir_ref,'inode_ref) ty_realpath1)
  | None2 of ('dir_ref * name * ('dir_ref,'inode_ref) ty_realpath1)
  | Err2 of (error * ty_name_list)
  (* invariant: if Fname2 ns, then not (ns.ends_with_slash2) *)
  (* invariant: if Err2 then ns.ends_with_slash2 *)
  (* FIXME since these are resolved, we may want to include the i0_ref and d0_ref *)

  let is_Err2 x = (match x with | Err2 _ -> true | _ -> false)

  let name_list_of_res_name n = (match n with 
    | Dname2 (_,rp) -> rp.nl3
    | Fname2 (_,_,_,rp) -> rp.nl3
    | None2 (_,_,rp) -> rp.nl3
    | Err2 (_,nl) -> nl)
 
  let string_of_names ns = (String.concat "/" ns)

  let string_of_res_name n = (
    let nl = name_list_of_res_name n in
    string_of_names nl.ns2)


  type ('dir_ref,'inode_ref) ty_fs_label = 
    | FS_LINK of (('dir_ref,'inode_ref) res_name * ('dir_ref,'inode_ref) res_name)
    | FS_MKDIR of (('dir_ref,'inode_ref) res_name * file_perm)
    | FS_OPEN of (('dir_ref,'inode_ref) res_name * open_flag list)
    | FS_READ of (('dir_ref,'inode_ref) res_name * int * int)
    | FS_READDIR of ('dir_ref,'inode_ref) res_name
    | FS_RENAME of (('dir_ref,'inode_ref) res_name * ('dir_ref,'inode_ref) res_name)
    | FS_RMDIR of ('dir_ref,'inode_ref) res_name
    | FS_STAT of ('dir_ref,'inode_ref) res_name
    | FS_SYMLINK of (('dir_ref,'inode_ref) res_name * string)
    | FS_TRUNCATE of (('dir_ref,'inode_ref) res_name * int)
    | FS_UNLINK of ('dir_ref,'inode_ref) res_name
    | FS_WRITE of (('dir_ref,'inode_ref) res_name * int * bytes * int)


  (*
  let is_None2 x = (match x with None2 _ -> true | _ -> false)
  *)


  type 'impl ty_return2 = {
    state2: 'impl;
    ret2: ret_value;
  } 
  let return s = { state2=s; ret2=None1 }


  type ('dir_ref,'inode_ref,'impl) ty_ops1 = {
    get_init_state1: unit -> 'impl;
    get_parent1: 'impl -> 'dir_ref -> ('dir_ref * name option); (* parent of root is root; name is none iff root  *)
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
    resolve11: 'impl -> 'dir_ref -> name -> ('dir_ref,'inode_ref) entry option; (* resolves normal entries; use get_parent for .. *)
    rm1: 'impl -> 'dir_ref -> name -> 'impl ty_return2; (* FIXME don't need this and unlink1 *)
    rmdir1: 'impl -> 'dir_ref -> name -> 'impl ty_return2; (* FIXME probably don't need this either *)
    touch1: 'impl -> 'dir_ref -> name -> 'impl ty_return2;
    write1: 'impl -> 'inode_ref -> bytes -> 'impl ty_return2;
    set_symlink1: 'impl -> 'inode_ref -> bool -> 'impl ty_return2;
  }

  (* calls to the fs take place in a process context *)
  type ('dir_ref,'impl) fs_state_process_state = {
    cwd4: 'dir_ref;
    fs_state4: 'impl
  }
    


  (* modelling the host *)

  (* process ids *)
  type ty_pid = Pid of num

  (* a process can only make a single call into OS (so, no threads); process is blocked until return *)
  type os_label = 
    | OS_CALL of (ty_pid * ty_label)
    | OS_RETURN of (ty_pid * (error,ret_value) sum)
    | OS_CREATE of ty_pid
    | OS_DESTROY of ty_pid


  (* file descriptors *)
  type ty_fd = FD of num

  (* dir handles *)
  type ty_dh = DH of num

  (* FIXME check this in linux kernel docs *)
  type fd_open_closed_state = FD_OPEN | FD_CLOSED

  type dh_open_closed_state = DH_OPEN | DH_CLOSED

  type ('dir_ref,'inode_ref,'impl) fd_state = {
    open_or_closed: fd_open_closed_state;
    inode_ref2: 'inode_ref;
    offset: num
  }

  type ('dir_ref,'inode_ref,'impl) dh_state = {
    open_or_closed: dh_open_closed_state;
    dir_ref2: 'dir_ref;
    offset: num
  }

  type ('dir_ref,'inode_ref) ty_pid_run_state = RUNNING | BLOCKED_CALL of ('dir_ref,'inode_ref) ty_fs_label | PENDING_RETURN of ((error,ret_value) sum)

  type ('dir_ref,'inode_ref,'impl) per_process_state = {
    (* root3: 'dir_ref; *) (* process root directory; FIXME not currently implemented *)
    cwd: 'dir_ref; (* FIXME rename this *)
    fd_table: (ty_fd,('dir_ref,'inode_ref,'impl) fd_state) fmap;
    dh_table: (ty_dh,('dir_ref,'inode_ref,'impl) dh_state) fmap;
    pid_run_state: ('dir_ref,'inode_ref) ty_pid_run_state
  }

  type ('dir_ref,'inode_ref,'impl) ty_os_state = {
    pid_table: (ty_pid,('dir_ref,'inode_ref,'impl) per_process_state) fmap;
    fs_state: 'impl (* FIXME index this fieldname *)
  }



end

(*
## Resolve names

Update: we first process the string to give a list of entries; /a/b/c -> ["";"a";"b";"c"]; /a/b/c/ -> ["";"a";"b";"c";""]; a/b/c -> ["a";"b";"c"]; note that [] is not in the range of this function; the empty string "" maps to [""]. We keep this first list because we may need to examine it at some points. 

FIXME we need to distinguish between a null string and an empty string

what about a relative path that is empty? in this case, it appears that this is returned as an error ENOENT (so the CWD is not appended in this case)

interestingly if you delete /tmp/d1 and a process is still in d1, the PWD for that process is /tmp/d1; and in /proc/pid/cwd it says "/tmp/d1 (deleted)"


*)

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
    type rname' = (X.Y.t1,X.Y.t3) res_name
    type entry' = (dir_ref',inode_ref') entry
  end
  open XR

  (* we introduce a local type to record the result of trying to resolve a path *)
  type ('a,'b) ok_or_err = Ok3 of 'a | Err3 of 'b

  (* let file_exists ops s0 ns = (resolve_inode_ref ops s0 ns <> None) *)

  (* get the real path, given a dir_ref *)
  let rec real_path_dir_ref ops s0 d0_ref = (
    match (ops.get_parent1 s0 d0_ref) with
    | (d1_ref,None) -> [""]
    | (d1_ref,Some n) -> (real_path_dir_ref ops s0 d1_ref)@[n])

  type ('dir_ref,'inode_ref) ty_resolve_relative_ok = 
  | Dir4 of 'dir_ref
  | File4 of ('dir_ref * name * 'inode_ref)
  | None4 of ('dir_ref * name)

  let rec resolve_relative ops s0 sofar ns = (
    match ns with 
    | [] -> (Ok3(Dir4(sofar)))
    | n::ns -> (
      if (n=".") || (n="") then (
        resolve_relative ops s0 sofar ns
      ) else if (n="..") then (
        let (dir_ref,_) = ops.get_parent1 s0 sofar in
        resolve_relative ops s0 dir_ref ns
      ) else (
        let m = ops.resolve11 s0 sofar n in
        match m with 
        | None -> (
          if (ns=[] || ns=[""]) then (* may end in a slash *)
            Ok3(None4(sofar,n))
          else
            Err3(ENOENT))
        | Some entry -> (
          match entry with 
          | Inr i0_ref -> (
            if ns=[] then (* not allowed to end in slash *)
              Ok3(File4(sofar,n,i0_ref)) 
            else
              Err3(ENOTDIR))
          | Inl d0_ref -> (
            resolve_relative ops s0 d0_ref ns)))))
  let (_:ty_ops' -> ty_impl' -> dir_ref' -> name list -> ((dir_ref',inode_ref')ty_resolve_relative_ok,error) ok_or_err) = resolve_relative

  let process_path1 path = (
    let p = explode path in
    let f1 (ns,cur) c = (if c="/" then (ns@[cur],"") else (ns,cur^c)) in
    let (ns,cur) = List.fold_left f1 ([],"") p in
    let ns = ns@[cur] in
    { ns2=ns })
  let (_:string -> ty_name_list) = process_path1

 (* assumes root not none *)
 let process_name_list ops s0 cwd nl = (
   let root = dest_Some (ops.get_root1 s0) in
   if nl.ns2 = [""] then Err2(ENOENT,nl) (* nl.ns2 was the empty string *)
   else (
     let is_absolute_nl = (List.hd nl.ns2 = "") in
     let r = (
       if is_absolute_nl then
         resolve_relative ops s0 root nl.ns2
       else
         resolve_relative ops s0 cwd nl.ns2)
     in
     match r with
     | Ok3 x -> (
       match x with
       | Dir4 d0_ref -> (
         let rp = { cwd3=cwd; nl3=nl; ns3=(real_path_dir_ref ops s0 d0_ref) } in
         Dname2(d0_ref,rp))
       | File4 (d0_ref,n,i0_ref) -> (
         let rp = { cwd3=cwd; nl3=nl; ns3=((real_path_dir_ref ops s0 d0_ref)@[n]) } in
         Fname2(d0_ref,n,i0_ref,rp))
       | None4 (d0_ref,n) -> 
         let rp = {cwd3=cwd; nl3=nl; ns3=(real_path_dir_ref ops s0 d0_ref)@[n] } in
         None2 (d0_ref,n,rp))
     | Err3 x -> (Err2(x,nl))))
  let (_:ty_ops' -> ty_impl' -> dir_ref' -> ty_name_list -> rname') = process_name_list

  (* guarantees: returns option of Fname or Dname  *)
  let process_path ops s0 cwd path = (
    let nl = process_path1 path in
    let rn = process_name_list ops s0 cwd nl in
    rn)  
  let (_:ty_ops' -> ty_impl' -> dir_ref' -> string -> rname') = process_path

  let process_path_from_root ops s0 path = (
    let root = dest_Some(ops.get_root1 s0) in
    process_path ops s0 root path)

  let ends_with_slash rn = (
    let nl = name_list_of_res_name rn in
    last (nl.ns2) = "")

  (* FIXME we want subsequent defns to work in terms of rname, and possible ty_name_list; we want invariants on these *)

  (* note that true = list_prefix [] [] = list_prefix xs xs; but the semantics checks e.g. whether we are rename something to itself *)
  let rec list_prefix xs ys = (
    match (xs,ys) with
    | ([],_) -> true
    | (_,[]) -> false
    | (x::xs,y::ys) -> (
      if (x=y) then list_prefix xs ys else false))

  (* check if renaming a dir to a subdir of itself; we expect to check for equality before calling this *)
  let subdir s d = (
    list_prefix s.ns3 d.ns3)

  (* want to restrict uses of resolve_dir_ref and resolve_inode_ref to this module *)
  (* FIXME check this is never used on the root directory, or get_parent_dir root = root, or maybe return None *)
  (*
  let get_parent_dir ops s0 nl = (
    resolve_dir_ref ops s0 (butlast nl.ns2))
  let (_:ty_ops' -> ty_impl' -> ty_name_list -> dir_ref' option) = get_parent_dir
  *)


end

(*
## `Fs_ops2`

This is the main part of the spec. If a transition succeeds, it calls
a method such as `ops1.mv1` to actually make a change in the
underlying state. Most of the stuff below involves dealing with all
the error cases.

Invariant: if any exception is raised, the state is not changed

*)

(* FIXME these work in terms of rnames; assumes no Err2 *)
module Fs_ops2 = struct
  
  open Unix (* for st_dev record fields etc *)
  open LargeFile (* FIXME include stats in Fs_types1? *)

  open Prelude
  open Fs_types1
(*  open Fs_ops1 *)
  (* open Resolve *)

(*  let get_parent_dir = Resolve.get_parent_dir
  let resolve_process_path2 = Resolve.process_path2 *)
  let resolve_subdir = Resolve.subdir
  let ends_with_slash = Resolve.ends_with_slash


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
    type res_name' = (X.Y.t1,X.Y.t3) res_name    
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

  (* bes is a list of (b,e); if exists a b that is true, raise those e's where b is true, else do nothing *)
  let cond_raise bes = Mymonad (fun s ->
    let bs = List.filter (fun (b,e) -> b=true) bes in
    if bs=[] then 
      finset_singleton(Inr(s,()))
    else
      finset_image (fun (b,e) -> Inl(s,e)) bs)      

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

  (* posix/1 *)

  let link ops spath dpath = (
    get_state >>= fun s0 ->
    match spath with 
    | Fname2(d0_ref,name,i0_ref,rp)  -> (
      match dpath with 
      | None2 (d0_ref,n,rp) -> (
        let s0 = ops.link_file1 s0 i0_ref d0_ref n in
        put_state' s0)
      | Err2(e,_) -> (
        (* (maybe_raise EEXIST) >>= fun _ -> (* arguably linux bug *) *)
        myraise e)
      | Fname2 _ -> (myraise EEXIST)
      | Dname2 _ -> (myraise EEXIST))
    | Dname2 _ -> (
      (match dpath with
        | Err2(e,_) -> (maybe_raise e)
        | _ -> do_nothing) >>= (fun _ ->
      myraise EPERM))
    | Err2(e,_) -> (myraise e)
    | None2 __ -> (myraise ENOENT))

  let mkdir ops rpath perms = (
    (* FIXME deal with perms *)
    get_state >>= fun s0 ->
    match rpath with 
    | None2(d0_ref,n,_) -> (
      let s0 = ops.mkdir1 s0 d0_ref n in
      put_state' s0)
    | Err2(e,_) -> (myraise e)
    | Dname2 _ -> (myraise EEXIST)
    | Fname2 _ -> (myraise EEXIST))

  (* FIXME we have to take care of flags eg O_TRUNC *)
  (* FIXME return is int option - meaning optional file handle? *)
  (* FIXME why is this called fopen (taking an fd?) rather than open? *)
  (* FIXME the mapping between fds and files is handled elsewhere - needs a new part of spec *)
  let _open ops rpath flags = (
    get_state >>= fun s0 ->
    match rpath with
    | None2 _ -> (myraise ENOENT)
    | Dname2(_,_) -> (myraise ENOENT) (* FIXME should be EISDIR? can we open a dir? *)
    | _ -> (return None1)) (* FIXME err case should raise an err? *)
  let (_:ty_ops' -> res_name' -> 'a -> ret_value ty_mymonad') = _open

  let open_create ops rpath = (
    get_state >>= fun s0 ->
    match rpath with 
    | Dname2 _ -> (myraise EEXIST) 
    | Fname2 _ -> (myraise EEXIST)
    | Err2 (e,_) -> (myraise e)
    | None2(d0_ref,n,ns) -> (
      (* FIXME for us, open_create should only create files *)
      if ends_with_slash rpath then 
        myraise EISDIR
      else
        let s0 = ops.touch1 s0 d0_ref n in
        put_state' s0))
  let (_:ty_ops' -> res_name' -> ret_value ty_mymonad') = open_create

  (* FIXME the real spec would allow reading less than all the bytes; recall len is maxlen *)
  let read ops rn ofs len = (
    match rn with 
    | None2 _ -> (myraise ENOENT)
    | Dname2 _ -> (myraise ENOENT)
    | Err2 (e,_) -> (myraise e)
    | Fname2(d0_ref,n,i0_ref,rp) -> (
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
  let (_:ty_ops' -> res_name' -> int -> int -> ret_value ty_mymonad') = read

  let readdir ops rn = (
    get_state >>= (fun s0 -> (
    match rn with 
    | Err2 (e,_) -> (myraise e)
    | None2 _ -> (myraise ENOENT) (* (raise (Unix_error (ENOENT,"readdir","/FIXMEreaddir"))) (* FIXME we may need access to the underlying path that was given by the user *) *)
    | Fname2 _ -> (myraise ENOTDIR) (* (raise (Unix_error (ENOTDIR,"readdir","/FIXMEreaddir"))) *)
    | Dname2(d0_ref,rp) -> (
      let r = ops.readdir1 s0 d0_ref in
      (put_state' r) >>= (fun _ -> (
      return r.ret2))))))
  let (_:ty_ops' -> res_name' -> ret_value ty_mymonad') = readdir
  (* NB later we may want to also return a state, given access times can cause changes when reading etc *)

  (* FIXME surely a lot of this complexity is because this is the user land behaviour of the mv command - but we want to target the syscall interface *)
  (* FIXME we probably want the containing dirs as well, when doing rename; put this in resolve *)
  (* FIXME rename to subdir of self? *)
  (* NB if an error is possible, then all transitions result in an error; we should check that this invariant holds of the spec *)

  (* posix/2 *)

  let rename ops rsrc rdst = (
    get_state >>= (fun s0 -> 
    match rsrc with
    | None2 _ -> (
      (* target may have ENOENT path *)
      (match rdst with 
      | Err2 (e',_) -> (
        maybe_raise e') (* tr/11 *)
      | _ -> do_nothing) >>= (fun _ -> (
        myraise ENOENT))) (* no src file *)
    | Err2 (e,_) -> (
      (* target may have ENOENT path *)
      (match rdst with 
      | Err2 (e',_) -> (
        maybe_raise e') (* tr/1 *)
      | _ -> do_nothing) >>= (fun _ -> (
      myraise e))) (* tr/2 *)
    | Fname2 (d0_ref,nsrc,i0_ref,rp) -> (
      match rdst with 
      | Err2 (e,_) -> (myraise e)
      | None2 (d1_ref,ndst,rp) -> (
        (let cond1 = ends_with_slash rdst in
        cond_raise [(cond1,ENOTDIR)]) >>= fun _ -> (* tr/3 *)
        (* do the move; there is no file ns_dst *)
        put_state'' (fun () -> ops.mv1 s0 d0_ref nsrc d1_ref ndst))
      | Fname2 (d1_ref,ndst,i1_ref,rp) -> (
        (* do the move; there is a file name ns_dst *)
        if (d1_ref=d0_ref) && (ndst=nsrc) then 
          return None1 (* tr/4 *)
        else
          put_state'' (fun () -> ops.mv1 s0 d0_ref nsrc d1_ref ndst))
        (* FIXME may want to have putstate return a void value *)
      | Dname2 (d0_ref,rp) -> (
        (* several reasonable options *)
        (if (ends_with_slash rdst) then 
          maybe_raise ENOTDIR         (* tr/5 arguably a Linux bug? Confirmed non-posix behaviour *)
        else 
          do_nothing) >>= (fun _ -> 
        if ((ops.readdir1 s0 d0_ref).ret2<>Names1[]) then 
          maybe_raise ENOTEMPTY       (* tr/6 strange, but posix allows this; FIXME posix also allows EEXIST in this case *)
        else
          do_nothing) >>= (fun _ ->
        myraise EISDIR))) (* expected *)
    | Dname2 (d0_ref,rps) -> (
      (* rename a directory; directory exists *)
      match rdst with
      | None2 (d1_ref,ndst,rpd) -> (
        (* do the move; there is no file ns_dst *)
        if (resolve_subdir rps rpd) then 
          myraise EINVAL
        else
          let p = ops.get_parent1 s0 d0_ref in
          match p with 
          | (d0_ref,Some nsrc) -> (
            put_state'' (fun () -> ops.mvdir1 s0 d0_ref nsrc d1_ref ndst))
          | (d0_ref,None) -> ( 
            (* src was root *)
            myraise EINVAL))
      | Err2 (e,_) -> (
        (maybe_raise EINVAL) >>= (fun _ -> (* tr/7 confirmed non-posix behaviour *)
        myraise e))
      | Fname2 (_,_,_,rpd) -> (
        (* check rename to subdir before rename to file; NB there are different reasonable options here *)
        (if (resolve_subdir rps rpd) then
          maybe_raise EINVAL 
        else 
          do_nothing) >>= (fun _ -> 
        myraise ENOTDIR)) 
      | Dname2 (d1_ref,rpd) -> (
        (* if same dir, return silently *)
        if (d1_ref=d0_ref) then
          (return None1) (* tr/8 *)
        (* FIXME check if renaming to a subdir *) (* FIXME following two exceptions should be maybe_raise *)
        else if (resolve_subdir rps rpd) then 
          (myraise EINVAL)
        (* FIXME check if dir not empty *)
        else if ((ops.readdir1 s0 d1_ref).ret2<>Names1[]) then 
          (myraise ENOTEMPTY) (* tr/9 *)
        (* otherwise target dir is empty; do rename; FIXME presumably root, if empty, can't be target unless src=root *)
        (* FIXME with the unix backend, we really don't want to execute this last because we know we are going to raise an error; but we must allow for future stages to raise further exceptions *)
        else
          let (d0_ref',x) = ops.get_parent1 s0 d0_ref in
          let (d1_ref',y) = ops.get_parent1 s0 d1_ref in
          match x with
          | None -> (myraise EINVAL)
          | Some nsrc -> (
            match y with 
            | None -> (
              failwith "impossible rename of dir onto root; can't happen because dst must be nonempty")
            | Some ndst -> (
              put_state'' (fun () -> ops.mvdir1 s0 d0_ref' nsrc d1_ref' ndst)))))))
  let (_:ty_ops' -> res_name' -> res_name' -> ret_value ty_mymonad') = rename      

  let rmdir ops rpath = (
    get_state >>= fun s0 ->
    match rpath with 
    | Dname2(d0_ref,rp) -> (
      if ((ops.readdir1 s0 d0_ref).ret2<>Names1[]) then
        (myraise ENOTEMPTY)
      else
        let (d1_ref,x) = ops.get_parent1 s0 d0_ref in
        match x with 
        | None -> (
          (* attempt to remove the root directory, may fail or succeed *)
          (maybe_raise EBUSY) >>= (fun _ ->
            (return None1)))
        | Some n -> (
          let s0 = ops.unlink1 s0 d1_ref n in
          put_state' s0))
    | Fname2 _ -> (myraise ENOTDIR)
    | None2 _ -> (myraise ENOENT)
    | Err2 (e,_) -> (myraise e))

  let stat ops rn = (
    get_state >>= (fun s0 -> (
    (* let _ = (print_endline ("stat: "^(string_of_res_name rn))) in *)
    match rn with
    | Err2 (e,_) -> (myraise e)
    | None2 _ -> (myraise ENOENT) 
    | Fname2(d0_ref,n,i0_ref,rp) -> (return (Stats1 (default_file_stats ops s0 i0_ref)))
    | Dname2(d0_ref,rp) -> (return (Stats1 (default_dir_stats ops s0 d0_ref)))))) 
  let (_:ty_ops' -> res_name' -> ret_value ty_mymonad') = stat

  let truncate ops rpath len = (
    get_state >>= fun s0 ->
    match rpath with 
    | Err2 (e,_) -> (myraise e)
    | None2 _ -> (myraise ENOENT)
    | Dname2 _ -> (myraise EISDIR) (* FIXME check error messages are sensible *)
    | Fname2(d0_ref,n,i0_ref,rp) -> (
      let r = ops.read1 s0 i0_ref in
      let bs = dest_bytes1 r.ret2 in
      (* create a new array, of length len, with same contents *)
      let bs' = MyDynArray.resize bs len in
      let s0 = ops.write1 s0 i0_ref bs' in
      put_state' s0))
  let (_:ty_ops' -> res_name' -> int -> ret_value ty_mymonad') = truncate

  let unlink ops rpath = (
    get_state >>= fun s0 ->
    match rpath with 
    | Err2(e,_) -> (myraise e)
    | None2 _ -> (myraise ENOENT)
    | Dname2 _ -> (myraise EISDIR)
    | Fname2(d0_ref,n,i0_ref,rp) -> (
      (* FIXME for resolving a file, often useful to have dir ref as well *)
      let s0 = ops.unlink1 s0 d0_ref n in
      put_state' s0))

  (* FIXME we need to make this take an offset in order to be usable, also read *)
  let write ops rn ofs bs len = (
    get_state >>= fun s0 -> 
    match rn with 
    | Err2 (e,_) -> (myraise e)
    | None2 _ -> (myraise ENOENT) 
    | Dname2 _ -> (myraise ENOENT)
    | Fname2(d0_ref,n,i0_ref,rp) -> (
      choose (downto' len 0) >>= fun len ->
      let r = ops.read1 s0 i0_ref in
      let bs' = dest_bytes1 r.ret2 in
      (* want to create a new array from bs' and bs *)
      let bs'' = MyDynArray.write (bs,0,len) (bs',ofs) in
      let r = ops.write1 s0 i0_ref bs'' in
      put_state' r >>= fun _ -> 
      return (Int1 len)))
  let (_:ty_ops' -> res_name' -> int -> file_contents -> int -> ret_value ty_mymonad') = write

  (* FIXME this is a hack - should do lots of checking eg src is a dir *)
  (*
  let symlink ops src dst = (
    open_create ops dst >>= fun _ -> 
    write ops dst 0 (MyDynArray.of_string src) (String.length src) >>= fun _ -> 
    get_state >>= fun s0 ->
    let rpath = process_path ops s0 dst in
    let Fname2(i0_ref,_) = rpath in
    let r = ops.set_symlink1 s0 i0_ref true in
    put_state' r)
  let (_:ty_ops' -> string -> string -> ret_value ty_mymonad') = symlink    
  *)

end

(*
## Fs transition system

The model is of a labelled transition system from state to state, but
where each transition may result in a return to userland (of a value
or an error). FIXME need to be non-determinisitic eg in write and read
behaviour.

*)

module Fs_transition_system = struct

  open Prelude 
  open Fs_types1
  open Fs_ops2
  (* open Fs_ops3 *)

  module X4 = struct 
    (* for the purposes of type-checking the following defns without spurious type vars *)
    (* type ty_ops' = (X.Y.t1,X.Y.t2,X.Y.t3,X.Y.t4,X.Y.t5) ty_state_ops *)
    type ty_ops' = (X.Y.t1,X.Y.t3,X.Y.t5) ty_ops1
    type state' = X.Y.t5
    type ty_fs_label' = (X.Y.t1,X.Y.t3) ty_fs_label
  end
  open X4

  (* the transition function takes a state, a label, and returns an updated state with a possible value returned, or an error *)
  (* FIXME readlink is just read, but may want to have a separate label *)
  let fs_trans ops s0 lbl = (
    (* let _ = print_endline (string_of_label lbl) in *)
    let m = (match lbl with 
      | FS_LINK (s,d) -> (link ops s d)
      | FS_MKDIR (s,p) -> (mkdir ops s p)
      | FS_OPEN (p,fs) -> (
          if (List.mem O_CREAT fs) then (open_create ops p (* FIXME fs *)) 
          else (_open ops p fs))
      | FS_READ (p,i,j) -> (read ops p i j)
      | FS_READDIR p -> (readdir ops p)
      | FS_RENAME (s,d) -> (rename ops s d)
      | FS_RMDIR p -> (rmdir ops p)
      | FS_STAT p -> (stat ops p)
      | FS_SYMLINK (s,d) -> failwith "FIXME" (* (symlink ops s d) *)
      | FS_TRUNCATE (p,l) -> (truncate ops p l)
      | FS_UNLINK p -> (unlink ops p)
      | FS_WRITE (p,ofs,bs,len) -> (write ops p ofs bs len))
    in
    let rs = run_mymonad m s0 in
    let f1 ve = (match ve with
      | Inl(s,e) -> (s,Inl e)
      | Inr(s,v) -> (s,Inr v))
    in
    let rs = List.map f1 rs in
    rs)
  let (_:ty_ops' -> state' -> ty_fs_label' -> (state' * (error,ret_value)sum) finset) = fs_trans

  (* convenience method to process a label; always choose first possible result (state,e+v) *)
  let process_label ops s0 lbl = (
    let rs = fs_trans ops s0 lbl in
    let _ = if rs = finset_empty then failwith "process_label: no result state" else () in
    let (s',v) = finset_choose rs in
    (s',v))
  
  (* convenience method to process a list of labels *)
  let process_labels ops s0 lbls = (
    let f1 = (fun xs -> fun lbl -> 
      let l = last xs in
      let (_,_,(s,_)) = l in
      let (s',v) = process_label ops s lbl in
      xs@[(List.length xs,lbl,(s',v))])
    in
    let dummy_lbl = FS_STAT(Err2(EINVAL, { ns2=["dummy lbl"] })) in
    let dummy_error_or_value = Inr None1 in
    List.fold_left f1 [(0,dummy_lbl,(s0,dummy_error_or_value))] lbls)
  let (_:ty_ops' -> state' -> ty_fs_label' list -> (int * ty_fs_label' * (state' * (error,ret_value)sum)) list) = process_labels

end

(*
## OS transition system

The model of transitions at the operating system level is:

  * A call gets made with OS_CALL label

  * The process gets moved to a blocked state

  * Further steps process the call
 
  * A return transition occurs with OS_RETURN; at this point, the process is unblocked

*)

module Os_transition_system = struct

  open Prelude 
  open Fs_types1
  open Fs_transition_system

  let process_path = Resolve.process_path

  module X5 = struct 
    (* for the purposes of type-checking the following defns without spurious type vars *)
    (* type ty_ops' = (X.Y.t1,X.Y.t2,X.Y.t3,X.Y.t4,X.Y.t5) ty_state_ops *)
    type ty_ops' = (X.Y.t1,X.Y.t3,X.Y.t5) ty_ops1
    type os_state' = (X.Y.t1,X.Y.t3,X.Y.t5) ty_os_state
  end
  open X5

  (* s0 is impl state *)
  let fs_lbl_of ops s0 cwd lbl = (
    let pp = process_path ops s0 cwd in
     match lbl with
    | LINK (s,d) -> (FS_LINK(pp s, pp d))
    | MKDIR (s,p) -> (FS_MKDIR(pp s, p))
    | OPEN (p,fs) -> (FS_OPEN(pp p, fs))
    | READ (p,i,j) -> (FS_READ(pp p, i, j))
    | READDIR p -> (FS_READDIR(pp p))
    | RENAME (s,d) -> (FS_RENAME(pp s, pp d))
    | RMDIR p -> (FS_RMDIR(pp p))
    | STAT p -> (FS_STAT(pp p))
    | SYMLINK (s,d) -> failwith "FIXME" (* (symlink ops s d) *)
    | TRUNCATE (p,l) -> (FS_TRUNCATE(pp p,l))
    | UNLINK p -> (FS_UNLINK(pp p))
    | WRITE (p,ofs,bs,len) -> (FS_WRITE(pp p,ofs,bs,len)))

  (* we return a finite set of possible next states; FIXME should we have functions to decompose and recompose hosts etc without doing everything manually? *)
  let os_trans_pid ops s0 pid lblopt = (
    match (fmap_lookup s0.pid_table pid) with | None -> (failwith "os_trans: impossible")
    | Some ppstate -> (
      let cwd = ppstate.cwd in
      match (ppstate.pid_run_state,lblopt) with 
      | (RUNNING,Some(OS_CALL(pid',lbl))) -> (
        if (pid' <> pid) then finset_empty
        else (
          let lbl = fs_lbl_of ops s0.fs_state cwd lbl in
          let ppstate' = { ppstate with pid_run_state = BLOCKED_CALL(lbl) } in
          let s0 = { s0 with pid_table=(fmap_update s0.pid_table (pid,ppstate')) } in
          finset_singleton s0))
      | (BLOCKED_CALL(lbl),None) -> (
        let fs_s0 = s0.fs_state in
        let next_fs_states = fs_trans ops fs_s0 lbl in
        let f1 (fs_s0',ev) = (
          let ppstate' = { ppstate with pid_run_state = PENDING_RETURN(ev) } in
          { s0 with fs_state=fs_s0'; pid_table=(fmap_update s0.pid_table (pid,ppstate')) })
        in
        finset_image f1 next_fs_states)
      | (PENDING_RETURN(ev),Some(OS_RETURN(pid',ev'))) -> (
        if (pid' <> pid) then finset_empty 
        else if (ev' <> ev) then finset_empty
        else (
          let ppstate' = { ppstate with pid_run_state = RUNNING } in
          let s0 = { s0 with pid_table=(fmap_update s0.pid_table (pid,ppstate')) } in
          finset_singleton s0))
      | (RUNNING,None) -> (finset_singleton s0)
      | (_,_) -> finset_empty))
  let (_:ty_ops' -> os_state' -> ty_pid -> os_label option -> os_state' finset) = os_trans_pid

  let create_pid ops s0 pid = { 
    cwd=(dest_Some (ops.get_root1 s0)); 
    fd_table=fmap_empty; 
    dh_table=fmap_empty; 
    pid_run_state=RUNNING 
  }

  let os_trans_pcreate_destroy ops s0 lblopt = (
    match lblopt with | None -> finset_empty
    | Some lbl -> (
      match lbl with
      | OS_CREATE(pid) -> (
        if finset_mem pid (fmap_dom s0.pid_table) then 
          finset_empty
        else (
          let s0 = { s0 with pid_table=(fmap_update s0.pid_table (pid,create_pid ops s0.fs_state pid)) } in
          finset_singleton s0))
      | OS_DESTROY(pid) -> (
        if not (finset_mem pid (fmap_dom s0.pid_table)) then 
          finset_empty
        else (
          let ppstate = dest_Some (fmap_lookup s0.pid_table pid) in
          match ppstate.pid_run_state with 
          | RUNNING -> (
            let s0 = { s0 with pid_table=(fmap_remove s0.pid_table pid) } in
            finset_singleton s0)
          | _ -> finset_empty (* we don't allow processes to be destroyed if they are in kernel *)))
      | _ -> finset_empty))
            
  (* assumes pid is in host pid_table *)
  let os_trans ops s0 lblopt = (
    (* process transitions *)
    let pids = fmap_dom s0.pid_table in
    let ss = finset_image (fun pid -> os_trans_pid ops s0 pid lblopt) pids in
    let ss = finset_bigunion ss in
    (* create/ destroy transitions *)
    let ss = finset_union ss (os_trans_pcreate_destroy ops s0 lblopt) in
    ss)
  let (_:ty_ops' -> os_state' -> os_label option -> os_state' finset) = os_trans


  (* convenience method to process a label; always choose first possible result (state,e+v) *)
  let os_process_label ops s0 lblopt = (
    let rs = os_trans ops s0 lblopt in
    let _ = if rs = finset_empty then failwith "os_process_label: no result state" else () in
    let s' = finset_choose rs in
    s')

  (* convenience method to process a list of labels *)
  let os_process_labels ops s0 lbls = (
    let f1 = (fun xs -> fun lbl -> 
      let l = last xs in
      let (_,_,s) = l in
      let s' = os_process_label ops s lbl in
      xs@[(List.length xs,lbl,s')])
    in
    let dummy_lbl = None in
    List.fold_left f1 [(0,dummy_lbl,s0)] lbls)
  let (_:ty_ops' -> os_state' -> os_label option list -> (int * os_label option * os_state') list) = os_process_labels

end


(*
## `Fs_spec_everything`
*)

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
(*  include Fs_ops3 *)
  include Fs_transition_system
  include Os_transition_system

end

(*
## Debug
*)
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
    let Names1(ns) = (ops.readdir1 s0 d0_ref).ret2 in
    let is_file ops s0 d0_ref n = (
      let Some(e) = ops.resolve11 s0 d0_ref n in
      is_inode_ref_entry e)
    in
    let is_dir ops s0 d0_ref n = (not (is_file ops s0 d0_ref n)) in
    let this_dir = (String.concat "\n" (List.map (fun n -> n) ns)) in    
    let this_dir = if ns <> [] then this_dir ^ "\n" else this_dir in
    let other_dirs = List.filter (fun n -> is_dir ops s0 d0_ref n) ns in
    let f1 n = (
      let Some(e) = ops.resolve11 s0 d0_ref n in
      let d1_ref = dest_dir_ref_entry e in
      string_of_dir ops s0 (dirname ^ "/" ^ n) d1_ref)
    in
    let others = List.map f1 other_dirs in
    "Directory "^dirname^":\n"
    ^ this_dir
    ^ (String.concat "" others))
    
  (* assume no cycles *)
  let string_of_state ops s = (
    let Some(d0_ref) = ops.get_root1 s in
    (string_of_dir ops s "/" d0_ref))

end



 end
;;

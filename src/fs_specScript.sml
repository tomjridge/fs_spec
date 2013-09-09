(* * prelude *)

(* Hi-lock: (("^ *\\(have\\|want\\).*" (0 (quote hi-green-b) t))) *)

val _ = app load ["numLib","finite_mapTheory", "stringTheory", "unwindLib","prim_recTheory","sumTheory"]; (* unwindLib for tactics; prim_rec for measure *)

val _ = Globals.linewidth:=120;

(* FIXME change to HOL_Interactive.toggle_quietdec() *)
fun myquietdec n = PolyML.print_depth n; (* EXPORT poly *)

myquietdec 0;
open pred_setTheory;
open finite_mapTheory;
myquietdec 100;

(* the following is taken from HOL/src/proofman/goalStack.sml, and modified to print goal at bottom *)
(* FIXME in new versions of HOL, this can be replaced by toggling some variables, see http://hol.svn.sourceforge.net/hol/?rev=9037&view=rev *)

val print_fvs = ref false;

fun ppgoal ppstrm (asl,w) =
   let open Portable
       val {add_string, add_break,
            begin_block, end_block, add_newline, ...} = with_ppstream ppstrm
       val pr = Parse.pp_term ppstrm
       fun pr_index (i,tm) =
            (begin_block CONSISTENT 0;
             add_string (Int.toString i^".  ");
             pr tm; end_block())
       fun pr_indexes [] = raise ERR "pr_indexes" ""
         | pr_indexes [x] = pr x
         | pr_indexes L = pr_list pr_index (fn () => ()) add_newline
                                  (rev (Lib.enumerate 0 (rev asl)));
   in
     begin_block CONSISTENT 0;
     (case asl
        of [] => ()
         | _  => ( begin_block CONSISTENT 2;
                   pr_indexes asl;
                   add_newline ();
                   add_string (!Globals.goal_line);
                   end_block ()));
     add_newline ();
     pr w;
     add_newline ();
     if !print_fvs then let
         val fvs = Listsort.sort Term.compare (free_varsl (w::asl))
         fun pr_v v = let
           val (n, ty) = dest_var v
         in
           begin_block INCONSISTENT 2;
           add_string n; add_break(1,0);
           Parse.pp_type ppstrm ty;
           end_block()
         end
       in
         if (not (null fvs)) then
           (if (not (null asl)) then add_newline() else ();
            add_string "Free variables"; add_newline();
            add_string "  ";
            begin_block CONSISTENT 0;
            pr_list pr_v (fn () => ()) (fn () => add_break(5,0)) fvs;
            end_block ();
            add_newline(); add_newline())
         else ()
       end
     else ();
     end_block ()
   end
   handle e => (Lib.say "\nError in attempting to print a goal!\n";  raise e);

set_goal_pp ppgoal;


use "tactic.sml"; open tactic; (* EXPORT tactic.sml *)

(* srw_ss was proving too much; LIST EQ: in general the simplifier should not
solve an equality that it wouldn't also use as a rewrite; REDUCE was changing c
- b <> 0 to ~ (c <= b) *)

val tmp = diminish_srw_ss ["list EQ","REDUCE","ARITH_RWTS"];

(* I find ASCII easier to read than (single width) unicode *)
val _ = set_trace "Unicode" 0;

val _ = new_theory "fs_spec";

(* * library stuff *)

val failwith_def = Define `
failwith (s:string) = (ARB:'a)
`;


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
(*     open Fs_prelude;; *)
(*     open Fs_spec;; *)
(*     open Fs_spec_everything;; *)

*)
(*
# fs_spec.ml
## Fs_types1

Types common to all implementations of the basic operations

*)

(* open Fs_prelude *)

(* as an optimization, we expect that each of these refs is actually a ref to a sector *)

(* module Fs_types1 = struct *)

(*   open Prelude *)

val bytes_def = type_abbrev("bytes",``:char list``);
val name_def = type_abbrev("name",``:string``);

val error_def = Hol_datatype `
error = E2BIG
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
    | EUNKNOWNERR of num
`;
 
val open_flag_def = Hol_datatype `
open_flag = O_RDONLY    
    | O_WRONLY          
    | O_RDWR            
    | O_NONBLOCK        
    | O_APPEND          
    | O_CREAT           
    | O_TRUNC           
    | O_EXCL            
    | O_NOCTTY          
    | O_DSYNC           
                        
    | O_SYNC            
                        
    | O_RSYNC           
                        
    | O_SHARE_DELETE
`;

val file_perm_def = type_abbrev("file_perm",``:num``);


val file_kind_def = Hol_datatype `
file_kind = S_REG                       (** Regular file *)
  | S_DIR                       (** Directory *)
  | S_LNK
`;


  (* top-level labels, intended to mirror the syscalls, but with functional interface; TODO need to incorporate file descriptors, "current position" etc *)
val ty_label_def = Hol_datatype `
ty_label = LINK of (string # string)
    | MKDIR of (string # file_perm)
    | OPEN of (string # open_flag list)
    | READ of (string # num # num)
    | READDIR of string
    | RENAME of (string # string)
    | RMDIR of string
    | STAT of string
    | SYMLINK of (string # string)
    | TRUNCATE of (string # num)
    | UNLINK of string
    | WRITE of (string # num # bytes # num)
`;

val file_contents_def = type_abbrev("file_contents",``:bytes``);

(* FIXME include a stats record in fs_spec *)
val float_def = type_abbrev("float",``:unit``);
val stats_def = Hol_datatype `
stats = <| st_dev : num;               (** Device number *)
        st_ino : num;               (** Inode number *)
        st_kind : file_kind;        (** Kind of the file *)
        st_perm : file_perm;        (** Access rights *)
        st_nlink : num;             (** Number of links *)
        st_uid : num;               (** User id of the owner *)
        st_gid : num;               (** Group ID of the file's group *)
        st_rdev : num;              (** Device minor number *)
        st_size : num;            (** Size in bytes *)
        st_atime : float;           (** Last access time *)
        st_mtime : float;           (** Last modification time *)
        st_ctime : float            (** Last status change time *)
      |>
`;


val ret_value_def = Hol_datatype `
ret_value = None1 | Int1 of num | Bytes1 of bytes (* FIXME add init return type *) | Names1 of name list
    | Stats1 of stats
`;

val dest_bytes1_def = Define `
dest_bytes1 (Bytes1 bs) = bs
`;
 
  (* names types; also type name earlier *)
  
  (* following moved from ops parser *)
val dirname_def = type_abbrev("dirname",``:string list``);
val filename_def = type_abbrev("filename",``:string list``);

  (* the type of parsed paths; what is important is whether the name ends with a slash *)
val ty_name_list2_def = Hol_datatype `
ty_name_list2 = <|
    ns2: name list;
    ends_with_slash2: bool  
  |>
`;

  (* we cannot supply Fname from user space: a name /tmp/tmp.txt may refer to a file or a dir *)
  (* resolved name *)
  (* type rname1 = Dname1 of name list | Fordname1 of name list *)
  (* resolved name relative to a state *)
val rname2_def = Hol_datatype `
rname2 = Dname2 of 'dir_ref # ty_name_list2
  | Fname2 of 'inode_ref # ty_name_list2 
  | None2 of ty_name_list2
  | Err2 of 'inode_ref # ty_name_list2
`;
  (* invariant: if Fname2 ns, then not (ns.ends_with_slash2) *)
  (* invariant: if Err2 then ns.ends_with_slash2 *)
  (* FIXME since these are resolved, we may want to include the i0_ref and d0_ref *)

val is_Err2_def = Define `
is_Err2 x = (case x of   Err2 _ -> T || _ -> F)
`;

val name_list_of_rname2_def = Define `
name_list_of_rname2 n = (case n of 
      Dname2 (_,ns) -> ns
    || Fname2 (_,ns) -> ns
    || None2 ns -> ns
    || Err2 (_,ns) -> ns)
`;

(* 
FIXME  let string_of_names ns = ("/"^(String.concat "/" ns))
*)

(*
FIXME  let string_of_rname2 n = (
    let ns = name_list_of_rname2 n in
    ((String.concat "/" ns.ns2)^(if ns.ends_with_slash2 then "/" else ""))) (* FIXME shouldn't this start with / ? *)
*)

val is_None2_def = Define `
is_None2 x = (case x of None2 _ -> T || _ -> F)
`;




val entry_def = type_abbrev("entry",``:('dir_ref,'inode_ref) sum``);
val is_Inl_def = Define `
is_Inl x = ISL x
`;
val is_Inr_def = Define `
is_Inr = ISR
`;
val dest_Inl_def = Define `
dest_Inl = OUTL
`;
val dest_Inr_def = Define `
dest_Inr = OUTR
`;

val is_dir_ref_entry_def = Define `
is_dir_ref_entry = is_Inl
`;
val is_inode_ref_entry_def = Define `
is_inode_ref_entry = is_Inr
`;
val dest_dir_ref_entry_def = Define `
dest_dir_ref_entry = dest_Inl
`;
val dest_inode_ref_entry_def = Define `
dest_inode_ref_entry = dest_Inr
`;

  (* might like type operators which pick up the type from a compound type eg. 'a ty_state_ops = { f1:(fst 'a); f2: (fst(snd 'a)) } etc *)
val ty_state_ops_def = Hol_datatype `
ty_state_ops = <|
    get_init_state: unit -> 'state;
    get_root: 'state -> 'dir_ref option;
    lookup_dir: 'state -> 'dir_ref -> 'dir option;
    lookup_inode: 'state -> 'inode_ref -> 'inode option;
    update_inds_some: 'state -> ('inode_ref # 'inode) -> 'state;
    resolve1: 'state -> 'dir_ref -> name -> ('dir_ref,'inode_ref) entry option;
    update_ents_pointwise: 'state -> 'dir_ref -> name -> ('dir_ref,'inode_ref) entry option -> 'state;
    new_dir: 'state -> 'dir_ref -> name -> ('state # ('dir_ref # 'dir)); 
    new_inode: 'state -> ('state # ('inode_ref # 'inode)); (* FIXME is dir linked in or not? yes, see mkdir *)
    get_contents: 'inode -> file_contents;
    set_contents: 'inode -> file_contents -> 'inode;
    get_symlink: 'inode -> bool;
    set_symlink: 'inode -> bool -> 'inode;
    dest_inode_ref: 'state -> 'inode_ref -> num;
    dest_dir_ref: 'state -> 'dir_ref -> num;
    get_entries: 'dir -> name list  (* FIXME 'dir -> name list ? *)
  |>
`;

  (* FIXME not needed? *)
  (*
  type ('dir_ref,'dir,'inode_ref,'inode,'impl) state = {
    ops3: ('dir_ref,'dir,'inode_ref,'inode,'impl) ty_state_ops;
    s3: 'impl
  }
  *)

val ty_return2_def = Hol_datatype `
ty_return2 = <|
    state2: 'impl;
    ret2: ret_value 
  |>
`;
(* FIXME want to ensure that this return has a different name to the return from Fs_ops2 *)
val return_def = Define `
return s = <| state2 := s; ret2 := None1 |>
`;


val ty_ops1_def = Hol_datatype `
ty_ops1 = <|
    get_init_state1: unit -> 'impl;
    get_root1: 'impl -> 'dir_ref option;
    dest_dir_ref1: 'impl -> 'dir_ref -> num;
    dest_inode_ref1: 'impl -> 'inode_ref -> num;
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
    set_symlink1: 'impl -> 'inode_ref -> bool -> 'impl ty_return2 
  |>
`;


(* end *)

(*
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

*)

(* FIXME tidy this up *)

(* module Resolve = struct *)
 
(*   open Prelude *)
(*   open Fs_types1 *)
(*  open Fs_ops1 *)


  (* resolve ns, return a (dir_ref,dir); only used with a resolve *)
  (* these seem to be used as shortcuts for looking up parents of a given path; but we want to ensure some invariants in lists of names; on the other hand, given a rname, to resolve the parent we don't want to have to go via strings *)
val resolve_dir_ref_f1_def = Define `
resolve_dir_ref_f1 ops s0 sofar ns = (case ns of 
        [] -> (SOME sofar)
      || n::ns -> (
        let m = ops.resolve11 s0 sofar n in
        case m of   NONE -> NONE || SOME entry -> 
        case is_dir_ref_entry entry of   F -> NONE || T ->
        let dir_ref = dest_dir_ref_entry entry in 
        resolve_dir_ref_f1 ops s0 dir_ref ns))
`;

val dest_Some_def = Define `
dest_Some = THE
`;

val resolve_dir_ref_def = Define `
resolve_dir_ref ops s0 ns = (
    (* sofar is the dir_ref we currently got to; starts off as the root *)
    (* FIXME separate out nested rec defns, so easier to transport to HOL backend *)
    let f1 = resolve_dir_ref_f1 ops s0 in
    let d0_ref = dest_Some(ops.get_root1 s0) in
    f1 d0_ref ns)
`;

val butlast_def = Define `
butlast = BUTLAST
`;

val last_def = Define `
last = LAST
`;

  (* want to restrict uses of resolve_dir_ref and resolve_inode_ref to this module *)
  (* FIXME check this is never used on the root directory, or get_parent_dir root = root, or maybe return None *)
val get_parent_dir_def = Define `
get_parent_dir ops s0 nl = (
    resolve_dir_ref ops s0 (butlast nl.ns2))
`;

  (* ns cannot be empty; FIXME this is only used in resolve *)
val resolve_inode_ref_def = Define `
resolve_inode_ref ops s0 ns = (
    let r = resolve_dir_ref ops s0 (butlast ns) in
    case r of   NONE -> NONE || SOME dir_ref ->
    let n = last ns in
    let m = ops.resolve11 s0 dir_ref n in
    case m of   NONE -> NONE || SOME entry -> 
    case is_inode_ref_entry entry of   F -> NONE || T -> 
    let i0_ref = dest_inode_ref_entry entry in (* assume a file *)
    SOME(i0_ref))
`;

  (* let file_exists ops s0 ns = (resolve_inode_ref ops s0 ns <> None) *)

  (* assumes path starts with '/'; throws an exception if not; FIXME do we always know the path starts with '/'? *)

(* FIXME map List.hd to HD, List.filter to FILTER, List.fold_left to FOLDL *)

val explode_def = Define `
explode s = (case s of 
  [] -> []
  || (c::rst) -> (STR c)::(explode rst))
`;

val process_path1_def = Define `
process_path1 path = (
    let p = explode path in
    if p = [] then failwith "process_path1: empty path" else
    if HD p <> "/" then failwith "process_path: doesn't start with /" else
    let p = TL p in
    let f1 (ns,cur) c = (if c="/" then (ns++[cur],"") else (ns,STRCAT cur c)) in
    let (ns,cur) = FOLDL f1 ([],"") p in
    let ends_with_slash = (cur="") in
    let ns = (if ends_with_slash then ns else ns++[cur]) in (* FIXME this logic is wrong? if multiple slashes? *)
    let ns = FILTER (\ n . n <> "." /\ n <> "") ns in (* remove empty entries and "." entries *)
    <| ns2 := ns; ends_with_slash2 := ends_with_slash |>)
`;

  (* preliminary processing of ns; drop empty components and "." components, and resolve ".." *)
  (* idempotent *)
  (* FIXME this is only OK if the e.g. d/../x/y/z we have that d exists FIXME do not use! *)
val process_dotdot_def = Define `
process_dotdot ops s0 nl = (
    let f1 sofar n = (
      if ((n="..") /\ sofar <> []) then 
        (butlast sofar) 
      else if ((n="..") /\ (sofar = [])) then
        (failwith "process_dot_dotdot")
      else
        (sofar++[n])) 
    in
    let ns = FOLDL f1 [] nl.ns2 in
    (nl with <|ns2 := ns|>))
`;


  (* take a state and a ty_name_list2, and check if name exists in state *)
val process_path2_def = Define `
process_path2 ops s0 ns = (
    (* FIXME we need to process .. here as well *)
    case ns.ends_with_slash2 of 
      T -> (
      let opt = resolve_dir_ref ops s0 ns.ns2 in
      case opt of 
        SOME(dir_ref) -> Dname2(dir_ref(*,dest_Some(ops.lookup_dir s0 dir_ref))*),ns)
      || NONE -> (
        let opt = resolve_inode_ref ops s0 ns.ns2 in 
        case opt of
          NONE -> None2 ns
          (* following case, ns ends with a slash, but resolves to a file *)
        || SOME(iref) -> Err2(iref(*,dest_Some(ops.lookup_inode s0 iref))*),ns)))
    || F -> (
      let opt = resolve_dir_ref ops s0 ns.ns2 in
      case opt of
        SOME(dir_ref) -> Dname2(dir_ref(*,dest_Some(ops.lookup_dir s0 dir_ref))*),ns)
      || NONE -> (
        let opt = resolve_inode_ref ops s0 ns.ns2 in
        case opt of 
          SOME(iref) -> Fname2(iref(*,dest_Some(ops.lookup_inode s0 iref)*),ns)
        || NONE -> None2 ns)))
`;


  (* guarantees: returns option of Fname or Dname  *)
val process_path_def = Define `
process_path ops s0 path = (
    let nl = process_path1 path in
    let nl = process_dotdot ops s0 nl in
    let rpath = process_path2 ops s0 nl in
    rpath)
`;

  (* FIXME we want subsequent defns to work in terms of rname, and possible ty_name_list2; we want invariants on these *)

val list_prefix_def = Define `
list_prefix xs ys = (
    case (xs,ys) of
      ([],_) -> T
    || (_,[]) -> F
    || (x::xs,y::ys) -> (
      if (x=y) then list_prefix xs ys else F))
`;

  (* check if renaming a dir to a subdir of itself *)
val subdir_def = Define `
subdir nl_src nl_dst = (list_prefix nl_src.ns2 nl_dst.ns2)
`;

(* end *)

(*
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

*)

(* FIXME these work in terms of rnames; assumes no Err2 *)
(* module Fs_ops2 = struct *)
  
(*   open Unix (* for st_dev record fields etc *) *)
(*   open LargeFile (* FIXME include stats in Fs_types1? *) *)

(*   open Prelude *)
(*   open Fs_types1 *)
(*  open Fs_ops1 *)
  (* open Resolve *)

(*
  let get_parent_dir = Resolve.get_parent_dir
  let resolve_process_path2 = Resolve.process_path2
*)

val resolve_subdir_def = Define `
resolve_subdir = subdir
`;


  (* type error = Fs_types1.error *)
val finset_def = type_abbrev("finset",``:'a list``);
val empty_finset_def = Define `
empty_finset = []
`;

val finset_empty_def = Define `
finset_empty = []
`;

(* FIXME FOLDL MEM *)
val finset_diff_def = Define `
finset_diff xs1 xs2 = (
    let f1 a x = (if (~ (MEM x xs2)) then x::a else a) in
    FOLDL f1 [] xs1)
`;
    
val finset_subset_def = Define `
finset_subset xs1 xs2 = (finset_diff xs1 xs2 = empty_finset)
`;

val finset_equal_def = Define `
finset_equal xs1 xs2 = ((finset_subset xs1 xs2) /\ (finset_subset xs2 xs1))
`;

val finset_mem_def = Define `
finset_mem x xs = (MEM x xs)
`;

val finset_insert_def = Define `
finset_insert x xs = (if MEM x xs then xs else x::xs)
`;

val mypartition_def = Define `
MYPARTITION f xs = (
  let (x,y) = SPLITP f xs in
  (y,x))
`;

val finset_partition_def = Define `
finset_partition = MYPARTITION
`;

val finset_bigunion_def = Define `
finset_bigunion = FLAT
`;

val finset_singleton_def = Define `
finset_singleton x = finset_insert x finset_empty
`;

val finset_image_def = Define `
finset_image f x = MAP f x
`;

val finset_choose_def = Define `
finset_choose xs = (
    if xs = finset_empty then failwith "finset_choose: empty finset" else HD xs)
`;

(* FIXME note that we have 'ja to force hol to order vars as ('impl,'a)ty_return3 *)
val ty_return3_def = type_abbrev("ty_return3",``:(('impl # error, 'impl # 'ja) sum) finset``);
  (* vars u, v used eg for Mymonad u *)
val mymonad_def = Hol_datatype `
mymonad = Mymonad of ('impl -> ('impl,'ja) ty_return3)
`;
val dest_mymonad_def = Define `
dest_mymonad (Mymonad u) = u
`;
val Inr_def = Define `Inr = INR`;

val return3_def = Define `
return3 x = Mymonad (\ s . finset_insert (Inr(s,x)) finset_empty)
`;
(*  let (_:'a -> ('impl,'a) mymonad) = return *)

(*
  (* for the purposes of type-checking the following defns without spurious type vars *)
  (* N.B. these dummy X module defns are interesting because they show what types are used in each module *)
  module X2 = struct
    type 'a ty_return3' = (X.Y.t5,'a) ty_return3
    type 'a ty_mymonad' = (X.Y.t5,'a) mymonad
    type rname2' = (X.Y.t1,X.Y.t3) rname2    
    (* type ty_ops' = (X.Y.t1,X.Y.t2,X.Y.t3,X.Y.t4,X.Y.t5) ty_state_ops *)
    type ty_ops' = (X.Y.t1,X.Y.t3,X.Y.t5) ty_ops1
  end
(*   open X2 *)
*)

(* FIXME Inl Inr pattern matching - need to pretty print as INL and INR *)
val bind_def = Define `
bind u f = Mymonad (\ s0 . let u = dest_mymonad u in
    let rs = u s0 in
    let f1 v = (case v of 
        INL x -> (finset_singleton (INL x))
      || INR (s,x) -> (
        let v = dest_mymonad (f x) in
        v s))
    in
    let rs' = finset_image f1 rs in
    let rs'' = finset_bigunion rs' in
    rs'')
`;
(*  let (_: 'a ty_mymonad' -> ('a -> 'b ty_mymonad') -> 'b ty_mymonad') = bind *)

  (* FIXME we also want to bake in that as soon as we have an exception, we will not alter the state further *)

val _ = add_infix(">>=", 90, HOLgrammars.NONASSOC);
val bind'_def = new_infixl_definition(
  "bind'",
  --`$>>= x y = bind x y`--,
  500);
  
val get_state_def = Define `
get_state = Mymonad (\ (s) . finset_singleton(Inr(s,s)))
`;
val put_state_def = Define `
put_state s0 = Mymonad (\ (s) . finset_singleton(Inr(s0,None1)))
`;
val myraise_def = Define `
myraise e = (Mymonad (\ (s) . finset_singleton(INL(s,e)))):('a,'b)mymonad
`;
val maybe_raise_def = Define `
maybe_raise e = Mymonad (\ (s) . finset_insert (INR(s,())) (finset_singleton(INL(s,e))))
`;

val choose_def = Define `
choose xs = Mymonad (\ s . finset_image (\ x . INR(s,x)) xs)
`;

  (* for a deterministic version, choose some particular value *)
val choose_def = Define `
choose xs = Mymonad (\ s . finset_singleton(INR(s,finset_choose xs)))
`;

val do_nothing_def = Define `
do_nothing = Mymonad (\ s . finset_singleton(INR(s,())))
`;

val run_mymonad_def = Define `
run_mymonad (Mymonad f) s = (f (s))
`;
(*  let (_:('a,'b) mymonad -> 'a -> ('a,'b) ty_return3) = run_mymonad *)
  
  (*  let is_empty_dir (s0:'impl) ns = failwith "FIXME" *)

(* FIXME parse floats as (), or omit these entries from the stats; FIXME 4096L parse as num; FIXME 0o777 as num; FIXME unix.s_dir *)
(* (+ ( * 7 64) ( * 7 8) 7) *)
val default_stats_def = Define `
default_stats = <|
    st_dev := 2049; (* device number FIXME 0? *)
    st_ino := 999; (* inode number FIXME change this for particular file etc *)
    st_kind := S_DIR; (* FIXME *)
    st_perm := 511; (* ugo+rwx , 511= 0o777 *)
    st_nlink := 2; (* FIXME dummy - for dir should be number of entries + 2 *)
    st_uid := 1000; (* FIXME 0? *)
    st_gid := 1000; 
    st_rdev := 0; (* device minor number *)
    st_size := 4096; (* FIXME dummy *)
    st_atime := ();
    st_mtime := ();
    st_ctime := ()
  |>
`;

(* FIXME Unix.S_LNK Unix.S_REG not parsed; FIXME Int64.of_int; FIXME MyDynArray.dim *)
val default_file_stats_def = Define `
default_file_stats ops s0 i0_ref = (default_stats with
    <| st_ino := (ops.dest_inode_ref1 s0 i0_ref);
    st_kind := (
      if (ops.get_symlink1 s0 i0_ref) then S_LNK else S_REG); (* FIXME we may need our own stats structure *)
    st_size := (
      let bs = dest_bytes1 ((ops.read1 s0 i0_ref).ret2) in
      ((* Int64.of_int *) ((* MyDynArray.dim*)LENGTH bs)))
  |>)
`;
 
val default_dir_stats_def = Define `
default_dir_stats ops s0 d0_ref = (default_stats with
    <| st_ino := (ops.dest_dir_ref1 s0 d0_ref);
    st_kind := S_DIR;
    st_size := 4096 (* seems to be default on my system - but changes depending on number of entries? *)
  |>)
`;

  (* Fs_ops1 returns ty_return3, which apart from read is just a state *)
val put_state'_def = Define `
put_state' r = put_state r.state2
`;

  (* FIXME remove *)
val put_state''_def = Define `
put_state'' f = (put_state' (f ()))
`;

(* FIXME \ _ not liked *)
val link_def = Define `
link ops spath dpath = (
    get_state >>= \ s0 . case spath of 
      Fname2(i0_ref,ns_src)  -> (
      case dpath of 
        None2 ns_dst -> (
        case (get_parent_dir ops s0 ns_dst) of (* FIXME what if ns_dst.ns2 = [] *)
          NONE -> (myraise ENOENT)
        || SOME(d0_ref) -> (
          let s0 = ops.link_file1 s0 i0_ref d0_ref (last ns_dst.ns2) in
          put_state' s0))
      || Err2(_1,_2) -> (
        (maybe_raise EEXIST) >>= (\ x . myraise ENOTDIR))
      || _3 -> (myraise EEXIST))
    || Dname2(_,_) -> (
      (case dpath of
          None2 ns_dst -> (
          case (get_parent_dir ops s0 ns_dst) of (* FIXME what if ns_dst.ns2 = [] *)
            NONE -> (maybe_raise ENOENT)
          || _ -> do_nothing)
        || Err2 (_,_) -> (maybe_raise EEXIST)  (* arguably a linux bug - prefer ENOTDIR? *)
        || _ -> (maybe_raise EEXIST)) >>= (\ x . myraise EPERM))
    || Err2(_,_) -> (myraise ENOTDIR)
    || _ -> (myraise ENOENT))
`;

val mkdir_def = Define `
mkdir ops rpath perms = (
    (* FIXME deal with perms *)
    get_state >>= \ s0 . case rpath of 
      None2(ns) -> (
      case (get_parent_dir ops s0 ns) of (* FIXME what if ns_dst.ns2 = [] *)
        NONE -> (myraise ENOENT)
      || SOME(d0_ref) -> (
        let s0 = ops.mkdir1 s0 d0_ref (last ns.ns2) in
        put_state' s0))
    || Dname2(_,_) -> (myraise EEXIST)
    || Fname2(_,_) -> (myraise EEXIST))
`;

(* FIXME resolve_process_path2 not known *)
val open_create_def = Define `
open_create ops rpath = (
    get_state >>= \ s0 . case rpath of 
      Dname2(_,_) -> (myraise EEXIST) 
    || Fname2(_,_) -> (myraise EEXIST)
    || None2 ns -> (
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
        let dpath = process_path2 ops s0 <| ns2 := dname; ends_with_slash2 := F |> in
        case dpath of
          Dname2(d0_ref,ns) -> (
          let s0 = ops.touch1 s0 d0_ref fname in
          put_state' s0)
      || Fname2(_,_) -> (myraise ENOTDIR)
      || _ -> (myraise ENOENT)))
`;

(* FIXME define sub *)
val sub_def = Define `
sub bs ofs len = SEG ofs (ofs+len) bs
`;

(* FIXME original defn doesn't work in HOL if m=0, since n can't get lower *)
val downto'_def = Define `
downto' n m = (if ((n=0) /\ (m=0)) then [0] else (if n < m then [] else n::(downto' (n-1) m)))
`;

  (* FIXME the real spec would allow reading less than all the bytes; recall len is maxlen *)
(* FIXME MyDynarray.dim, MyDynarray.sub *)
val read_def = Define `
read ops rname2 ofs len = (
    case rname2 of 
      None2 _ -> (myraise ENOENT)
    || Dname2(_,_) -> (myraise ENOENT)
    || Fname2(i0_ref,ns) -> (
      get_state >>= (\ s0 . (
      let r = ops.read1 s0 i0_ref in (* FIXME Fs_ops1 may have to take an offset too *)
      (put_state' r) >>= \ x . choose (downto' len 0) >>= \ len . let bs = dest_bytes1 r.ret2 in
      let len_bs = LENGTH bs in
      (* assume ofs is wellformed *)
      let len = if ofs+len <= len_bs then len else len_bs - ofs in
      (* let _ = print_endline ("read len_bs: "^(string_of_int len_bs)^"; len: "^(string_of_int len)^"; ofs: "^(string_of_int ofs)) in *)
      (* let _ = print_endline "before" in *)
      let bs' = sub bs ofs len in
      (* let _ = print_endline "after" in *)
      return3 (Bytes1(bs'))))))
`;

  (* NB doesn't include . and .. *)

val readdir_def = Define `
readdir ops rname2 = (
    get_state >>= (\ s0 . (
    case rname2 of 
      None2 _ -> (myraise ENOENT) 
    || Fname2 _ -> (myraise ENOTDIR) (* (raise (Unix_error (ENOTDIR,"readdir","/FIXMEreaddir"))) *)
    || Dname2(d0_ref,ns) -> (
      let r = ops.readdir1 s0 d0_ref in
      (put_state' r) >>= (\ x . (
      return3 r.ret2))))))
`;
  (* NB later we may want to also return a state, given access times can cause changes when reading etc *)

  (* FIXME surely a lot of this complexity is because this is the user land behaviour of the mv command - but we want to target the syscall interface *)
  (* FIXME we probably want the containing dirs as well, when doing rename; put this in resolve *)
  (* FIXME rename to subdir of self? *)

val rename_def = Define `
rename ops rsrc rdst = (
    get_state >>= (\ s0 . case rsrc of
      None2 _ -> (myraise ENOENT) (* no src file *)
    || Err2 (_,_) -> (
      (* target may have ENOENT path *)
      (case rdst of 
        None2 ns_dst -> (
        case get_parent_dir ops s0 ns_dst of
          NONE -> (maybe_raise ENOENT) (* parent dir of dst doesn't exist *)
        || SOME _ -> do_nothing)
      || _ -> do_nothing) >>= \ x . (
      myraise ENOTDIR))
    || Fname2 (i0_ref,ns_src) -> (
      case rdst of 
        None2 ns_dst -> (
        (* do the move; there is no file ns_dst *)
        (* FIXME check rename to target where parent doesn't exist *)
        case (get_parent_dir ops s0 ns_dst) of
          NONE -> (myraise ENOENT) (* parent dir of dst doesn't exist *)
        || SOME(d1_ref) -> (
          case (get_parent_dir ops s0 ns_src) of SOME(d0_ref) ->
          put_state'' (\ x . ops.mv1 s0 d0_ref (last (ns_src.ns2)) d1_ref (last ns_dst.ns2))))
      || Fname2 (i1_ref,ns_dst) -> (
        (* do the move; there is a file name ns_dst *)
        case (get_parent_dir ops s0 ns_src) of SOME(d0_ref) -> 
        case (get_parent_dir ops s0 ns_dst) of SOME(d1_ref) ->
        if (ns_dst.ns2=ns_src.ns2) then 
          return3 None1 
        else
          put_state'' (\ () . ops.mv1 s0 d0_ref (last ns_src.ns2) d1_ref (last ns_dst.ns2)))
        (* FIXME may want to have putstate return a void value *)
      || Dname2 (d0_ref,ns_dst) -> (
        (* several reasonable options *)
        (if (ns_dst.ends_with_slash2) then 
          maybe_raise ENOTDIR         (* arguably a Linux bug? not posix? *)
        else 
          do_nothing) >>= (\ x . if ((ops.readdir1 s0 d0_ref).ret2<>Names1[]) then 
          maybe_raise ENOTEMPTY       (* arguably a Linux bug? not posix? *)
        else
          do_nothing) >>= (\ x . myraise EISDIR))
      || Err2(_,_) -> (
        myraise ENOTDIR))
    || Dname2 (d0_ref,ns_src) -> (
      (* directory exists *)
      case rdst of
        None2 ns_dst -> (
        (* do the move; there is no file ns_dst *)
        case (get_parent_dir ops s0 ns_src) of SOME(d0_ref) ->
        case get_parent_dir ops s0 ns_dst of
          NONE -> (myraise ENOENT) (* parent dir of dst doesn't exist *)
        || SOME(d1_ref) -> (
          if (resolve_subdir ns_src ns_dst) then 
            myraise EINVAL
          else
            put_state'' (\ () . ops.mvdir1 s0 d0_ref (last ns_src.ns2) d1_ref (last ns_dst.ns2))))
      || Err2 (_,ns_dst) -> (
        (if (resolve_subdir ns_src ns_dst) then
          maybe_raise EINVAL 
        else 
          do_nothing) >>= (\ x . myraise ENOTDIR))
      || Fname2 (_,ns_dst) -> (
        (* check rename to subdir before rename to file; NB there are different reasonable options here *)
        (if (resolve_subdir ns_src ns_dst) then
          maybe_raise EINVAL 
        else 
          do_nothing) >>= (\ x . myraise ENOTDIR)) (* arguably this is a bug in linux? *)
      || Dname2 (d1_ref,ns_dst) -> (
        (* if same dir, return silently *)
        if (d1_ref=d0_ref) then
          (return3 None1)
        (* FIXME check if renaming to a subdir *) (* FIXME following two exceptions should be maybe_raise *)
        else if (resolve_subdir ns_src ns_dst) then 
          (myraise EINVAL)
        (* FIXME check if dir not empty *)
        else if ((ops.readdir1 s0 d1_ref).ret2<>Names1[]) then 
          (myraise ENOTEMPTY)          (* arguably a Linux bug? not posix? *)
        (* otherwise target dir is empty; do rename; FIXME presumably root, if empty, can't be target unless src=root *)
        (* FIXME with the unix backend, we really don't want to execute this last because we know we are going to raise an error; but we must allow for future stages to raise further exceptions *)
        else
          case (get_parent_dir ops s0 ns_src) of SOME(d0_ref) -> 
          case (get_parent_dir ops s0 ns_dst) of SOME(d1_ref) ->
          put_state'' (\ () . ops.mvdir1 s0 d0_ref (last ns_src.ns2) d1_ref (last ns_dst.ns2))))))
`;

(* FIXME match let SOME(x) = not accepted by HOL *)
val rmdir_def = Define `
rmdir ops rpath = (
    get_state >>= \ s0 . case rpath of 
      Dname2(d0_ref,ns) -> (
      if ((ops.readdir1 s0 d0_ref).ret2<>Names1[]) then
        (myraise ENOTEMPTY)
      else
        case get_parent_dir ops s0 ns of SOME(d1_ref) ->
        let s0 = ops.unlink1 s0 d1_ref (last ns.ns2) in
        put_state' s0)
    || Fname2 _ -> (myraise ENOTDIR)
    || None2 _ -> (myraise ENOENT))
`;

val stat_def = Define `
stat ops rname2 = (
    get_state >>= (\ s0 . (
    (* let _ = (print_endline ("stat: "^(string_of_rname2 rname2))) in *)
    case rname2 of
      None2 _ -> (myraise ENOENT)  (* (raise (Unix_error (ENOENT,"stat","/FIXMEstat"))) *)
    || Fname2(i0_ref,ns) -> (return3 (Stats1 (default_file_stats ops s0 i0_ref)))
    || Dname2(d0_ref,ns) -> (return3 (Stats1 (default_dir_stats ops s0 d0_ref))))))
`;

(* FIXME this should produce a list of length len, based on xs *)
val resize_def = Define `
resize xs len = TAKE len xs
`;

(* FIXME MyDynarray.resize *)
val truncate_def = Define `
truncate ops rpath len = (
    get_state >>= \ s0 . case rpath of 
      None2 _ -> (myraise ENOENT)
    || Dname2(_,_) -> (myraise EISDIR) (* FIXME check error messages are sensible *)
    || Fname2(i0_ref,ns) -> (
      let r = ops.read1 s0 i0_ref in
      let bs = dest_bytes1 r.ret2 in
      (* create a new array, of length len, with same contents *)
      let bs' = resize bs len in
      let s0 = ops.write1 s0 i0_ref bs' in
      put_state' s0))
`;

val unlink_def = Define `
unlink ops rpath = (
    get_state >>= \ s0 . case rpath of 
      None2(_) -> (myraise ENOENT)
    || Dname2(_,_) -> (myraise EISDIR)
    || Fname2(i0_ref,ns) -> (
      (* FIXME for resolving a file, often useful to have dir ref as well *)
      case get_parent_dir ops s0 ns of SOME(d0_ref) -> 
      let s0 = ops.unlink1 s0 d0_ref (last ns.ns2) in
      put_state' s0))
`;

(* FIXME this should create a new list based on bs' *)
val mywrite = Define `
mywrite (bs,i,j) (bs',ofs) = bs'
`;

  (* FIXME we need to make this take an offset in order to be usable, also read *)
val write_def = Define `
write ops rname2 ofs bs len = (
    get_state >>= \ s0 . case rname2 of 
      None2 _ -> (myraise ENOENT) (* (raise (Unix_error (ENOENT,"read","/FIXMEwrite"))) *)
    || Dname2(_,_) -> (myraise ENOENT) (* (raise (Unix_error (ENOENT,"read","/FIXMEwrite"))) *)
    || Fname2(i0_ref,ns) -> (
      choose (downto' len 0) >>= \ len . let r = ops.read1 s0 i0_ref in
      let bs' = dest_bytes1 r.ret2 in
      (* want to create a new array from bs' and bs *)
      let bs'' = mywrite (bs,0,len) (bs',ofs) in
      let r = ops.write1 s0 i0_ref bs'' in
      put_state' r >>= \ x . return3 (Int1 len)))
`;



(* end *)

(*
## `Fs_ops3`

This works in terms of strings; handles Err2 on resolving 

*)

(* FIXME check mv if src=dst *)
(* module Fs_ops3 = struct  *)

(*   open Fs_types1 *)
(*   open Resolve *)
(*   open Fs_ops2 *)

(*
  (* for the purposes of type-checking the following defns without spurious type vars *)
  module X3 = struct 
    type 'a ty_return3' = (X.Y.t5,'a) ty_return3
    type 'a ty_mymonad' = (X.Y.t5,'a) mymonad
    type rname2' = (X.Y.t1,X.Y.t3) rname2    
    (* type ty_ops' = (X.Y.t1,X.Y.t2,X.Y.t3,X.Y.t4,X.Y.t5) ty_state_ops *)
    type ty_ops' = (X.Y.t1,X.Y.t3,X.Y.t5) ty_ops1
  end
(*   open X3 *)
*)

(* FIXME nice if names are different *)
val fs_ops3_link_def = Define `
fs_ops3_link ops src dst = (
    get_state >>= \ s0 . let rsrc = process_path ops s0 src in
    let rdst = process_path ops s0 dst in
    link ops rsrc rdst)
`;

val fs_ops3_mkdir_def = Define `
fs_ops3_mkdir ops path perms = (
    get_state >>= \ s0 . let rpath = process_path ops s0 path in
    if (is_Err2 rpath) then (myraise ENOTDIR) else mkdir ops rpath perms)
`;

  (* FIXME we have to take care of flags eg O_TRUNC *)
  (* FIXME return is int option - meaning optional file handle? *)
  (* FIXME why is this called fopen (taking an fd?) rather than open? *)
  (* FIXME the mapping between fds and files is handled elsewhere - needs a new part of spec *)

val fs_ops3__open_def = Define `
fs_ops3__open ops path flags = (
    get_state >>= \ s0 . let rpath = process_path ops s0 path in
    case rpath of
      None2 _ -> (myraise ENOENT)
    || Dname2(_,_) -> (myraise ENOENT) (* FIXME? can we open a dir? *)
    || _ -> (return3 None1))
`;
 
  (* open call returns an fd; but may have side effects; open create is one such call; FIXME what are others? *)
val fs_ops3_open_create_def = Define `
fs_ops3_open_create ops path = (
    get_state >>= \ s0 . let rpath = process_path ops s0 path in
    if (is_Err2 rpath) then (myraise ENOTDIR) else open_create ops rpath)
`;

  (* N.B. for read and write ofs is associated with fd, so presumably < len of file *)
val fs_ops3_read_def = Define `
fs_ops3_read ops path ofs len = (
    get_state >>= \ s0 . let rpath = process_path ops s0 path in
    if (is_Err2 rpath) then (myraise ENOTDIR) else read ops rpath ofs len)
`;
  
val fs_ops3_readdir_def = Define `
fs_ops3_readdir ops path = (
    get_state >>= \ s0 . let rpath = process_path ops s0 path in
    if (is_Err2 rpath) then (myraise ENOTDIR) else readdir ops rpath)
`;

  (* FIXME check do_rename against ops2.rename; also check against doc in linux sys programming *)
val fs_ops3_rename_def = Define `
fs_ops3_rename ops src dst = (
    get_state >>= \ s0 . let rsrc = process_path ops s0 src in
    let rdst = process_path ops s0 dst in
    rename ops rsrc rdst)
`;

val fs_ops3_rmdir_def = Define `
fs_ops3_rmdir ops path = (
    get_state >>= \ s0 . let rpath = process_path ops s0 path in
    if (is_Err2 rpath) then (myraise ENOTDIR) else rmdir ops rpath)
`;

val fs_ops3_stat_def = Define `
fs_ops3_stat ops path = (
    get_state >>= \ s0 . let rpath = process_path ops s0 path in
    if (is_Err2 rpath) then (myraise ENOTDIR) else stat ops rpath)
`;

val fs_ops3_truncate_def = Define `
fs_ops3_truncate ops path len = (
    get_state >>= \ s0 . let rpath = process_path ops s0 path in
    if (is_Err2 rpath) then (myraise ENOTDIR) else truncate ops rpath len)
`;

val fs_ops3_unlink_def = Define `
fs_ops3_unlink ops path = (
    get_state >>= \ s0 . let rpath = process_path ops s0 path in
    if (is_Err2 rpath) then (myraise ENOTDIR) else unlink ops rpath)
`;

val fs_ops3_write_def = Define `
fs_ops3_write ops path ofs bs len = (
    get_state >>= \ s0 . let rpath = process_path ops s0 path in
    if (is_Err2 rpath) then (myraise ENOTDIR) else write ops rpath ofs bs len)
`;

  (* FIXME this is a hack - should do lots of checking eg src is a dir *)
(* FIXME MyDynArray.of_string *)
val fs_ops3_symlink_def = Define `
fs_ops3_symlink ops src dst = (
    fs_ops3_open_create ops dst >>= \ x . fs_ops3_write ops dst 0 ((* MyDynArray.of_string *) src) (STRLEN src) >>= \ x . get_state >>= \ s0 . let rpath = process_path ops s0 dst in
    case rpath of Fname2(i0_ref,_) ->
    let r = ops.set_symlink1 s0 i0_ref T in
    put_state' r)
`;


(* end *)


(*
## Transition system

The model is of a labelled transition system from state to state, but
where each transition may result in a return to userland (of a value
or an error). FIXME need to be non-determinisitic eg in write and read
behaviour.

*)

(* module Transition_system = struct *)

(*   open Prelude  *)
(*   open Fs_types1 *)
(*   open Fs_ops2 *)
(*   open Fs_ops3 *)

(*
  module X4 = struct 
    (* for the purposes of type-checking the following defns without spurious type vars *)
    (* type ty_ops' = (X.Y.t1,X.Y.t2,X.Y.t3,X.Y.t4,X.Y.t5) ty_state_ops *)
    type ty_ops' = (X.Y.t1,X.Y.t3,X.Y.t5) ty_ops1
    type state' = X.Y.t5
  end
(*   open X4 *)
*)

  (* the transition function takes a state, a label, and returns an updated state with a possible value returned, or an error *)
  (* FIXME readlink is just read, but may want to have a separate label *)
(* FIXME probably worth folding Fs_ops3 into Fs_ops2 *)
val trans_def = Define `
trans ops s0 lbl = (
    (* let _ = print_endline (string_of_label lbl) in *)
    let m = (case lbl of 
        LINK (s,d) -> (fs_ops3_link ops s d)
      || MKDIR (s,p) -> (fs_ops3_mkdir ops s p)
      || OPEN (p,fs) -> (
          if (MEM O_CREAT fs) then (fs_ops3_open_create ops p (* FIXME fs *)) 
          else (fs_ops3__open ops p fs))
      || READ (p,i,j) -> (fs_ops3_read ops p i j)
      || READDIR p -> (fs_ops3_readdir ops p)
      || RENAME (s,d) -> (fs_ops3_rename ops s d)
      || RMDIR p -> (fs_ops3_rmdir ops p)
      || STAT p -> (fs_ops3_stat ops p)
      || SYMLINK (s,d) -> (fs_ops3_symlink ops s d)
      || TRUNCATE (p,l) -> (fs_ops3_truncate ops p l)
      || UNLINK p -> (fs_ops3_unlink ops p)
      || WRITE (p,ofs,bs,len) -> (fs_ops3_write ops p ofs bs len))
    in
    let rs = run_mymonad m s0 in
    let f1 ve = (case ve of
        INL(s,e) -> (s,INL e)
      || INR(s,v) -> (s,INR v))
    in
    let rs = MAP f1 rs in
    rs)
`;

(*
  (* convenience method to process a label; always choose first possible result (state,e+v) *)
  let process_label ops s0 lbl = (
    let rs = trans ops s0 lbl in
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
    let dummy_lbl = LINK("dummy lbl","dummy lbl") in
    let dummy_error_or_value = INR None1 in
    List.fold_left f1 [(0,dummy_lbl,(s0,dummy_error_or_value))] lbls)
  let (_:ty_ops' -> state' -> ty_label list -> (int * ty_label * (state' * (error,ret_value)sum)) list) = process_labels
*)

(* end *)


(* * end *)

val _ = export_theory();

(*

Local Variables:
outline-regexp: "^(\\* +[*+.]+ "
fill-column: 80
mode: sml
mode: outline-minor
mode: hi-lock
sml-program-name: "hol"
End:

*)

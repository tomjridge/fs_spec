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
# fs_spec.ml
## Fs_types1

Types common to all implementations of the basic operations

*)

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

  (* break the string into components *)
val ty_name_list_def = Hol_datatype `
ty_name_list = <|
    ns2: name list  (* invariant: not [] *)
  |>
`;
  (* let ends_with_slash nl = nl.ends_with_slash2 *)

  (* process . and .. and empty entries relative to a cwd *)
val ty_realpath1_def = Hol_datatype `
ty_realpath1 = <|
    cwd3: 'dir_ref; (* cwd for process *)
    nl3: ty_name_list; (* the original string *)
    ns3: name list  (* invariant: not []; first entry is empty; no . and .. entries; no further empty entries (absolute paths) *)
    (* FIXME we don't need e3  if we are interested in paths *)                                  
                                  (* e3: (('dir_ref,'inode_ref) entry,name)sum ( * inr means that the path might target a non-existent file or directory, but everything else resolved * ) *)
  |>
`;
val ty_realpath_def = Hol_datatype `
ty_realpath = OK1 of ('dir_ref) ty_realpath1 | Err1 of (error # ty_name_list)
`;

val res_name_def = Hol_datatype `
res_name = Dname2 of ('dir_ref # ('dir_ref) ty_realpath1)
  | Fname2 of ('dir_ref # name # 'inode_ref # ('dir_ref) ty_realpath1)
  | None2 of ('dir_ref # name # ('dir_ref) ty_realpath1)
  | Err2 of (error # ty_name_list)
`;

val is_Err2_def = Define `
is_Err2 x = (case x of   Err2 _ -> T || _ -> F)
`;

val name_list_of_res_name_def = Define `
name_list_of_res_name n = (case n of 
      Dname2 (_,rp) -> rp.nl3
    || Fname2 (_,_,_,rp) -> rp.nl3
    || None2 (_,_,rp) -> rp.nl3
    || Err2 (_,nl) -> nl)
`;

(* 
FIXME  let string_of_names ns = ("/"^(String.concat "/" ns))
*)

(*
FIXME  let string_of_rname2 n = (
    let ns = name_list_of_rname2 n in
    ((String.concat "/" ns.ns2)^(if ns.ends_with_slash2 then "/" else ""))) (* FIXME shouldn't this start with / ? *)
*)


val ty_fs_label_def = Hol_datatype `
ty_fs_label = FS_LINK of (('dir_ref,'inode_ref) res_name # ('dir_ref,'inode_ref) res_name)
    | FS_MKDIR of (('dir_ref,'inode_ref) res_name # file_perm)
    | FS_OPEN of (('dir_ref,'inode_ref) res_name # open_flag list)
    | FS_READ of (('dir_ref,'inode_ref) res_name # num # num)
    | FS_READDIR of ('dir_ref,'inode_ref) res_name
    | FS_RENAME of (('dir_ref,'inode_ref) res_name # ('dir_ref,'inode_ref) res_name)
    | FS_RMDIR of ('dir_ref,'inode_ref) res_name
    | FS_STAT of ('dir_ref,'inode_ref) res_name
    | FS_SYMLINK of (('dir_ref,'inode_ref) res_name # string)
    | FS_TRUNCATE of (('dir_ref,'inode_ref) res_name # num)
    | FS_UNLINK of ('dir_ref,'inode_ref) res_name
    | FS_WRITE of (('dir_ref,'inode_ref) res_name # num # bytes # num)
`;

val ty_return2_def = Hol_datatype `
ty_return2 = <|
    state2: 'impl;
    ret2: ret_value 
  |>
`;
(* FIXME want to ensure that this return has a different name to the return from Fs_ops2 *)
val return_def = Define `
return_state s = <| state2 := s; ret2 := None1 |>
`;

(* FIXME changed 'impl to 'jimpl so that order of ty params was same in HOL as OCaml *)
val ty_ops1_def = Hol_datatype `
ty_ops1 = <|
    get_init_state1: unit -> 'jimpl;
    get_parent1: 'jimpl -> 'dir_ref -> ('dir_ref # name) option; (* if root, parent is none; possibly disconnected dirs can also have no parent *)
    get_root1: 'jimpl -> 'dir_ref option;
    dest_dir_ref1: 'jimpl -> 'dir_ref -> num;
    dest_inode_ref1: 'jimpl -> 'inode_ref -> num;
    get_symlink1: 'jimpl -> 'inode_ref -> bool;
    link_file1: 'jimpl -> 'inode_ref -> 'dir_ref -> name -> 'jimpl ty_return2;
    unlink1: 'jimpl -> 'dir_ref -> name -> 'jimpl ty_return2;
    mkdir1: 'jimpl -> 'dir_ref -> name -> 'jimpl ty_return2;
    mv1: 'jimpl -> 'dir_ref -> name -> 'dir_ref -> name -> 'jimpl ty_return2;
    mvdir1: 'jimpl -> 'dir_ref -> name -> 'dir_ref -> name -> 'jimpl ty_return2;
    read1: 'jimpl -> 'inode_ref -> 'jimpl ty_return2;
    readdir1: 'jimpl -> 'dir_ref -> 'jimpl ty_return2; (* don't return . and .. entries *)
    resolve11: 'jimpl -> 'dir_ref -> name -> ('dir_ref,'inode_ref) entry option; (* resolves normal entries; use get_parent for .. *)
    rm1: 'jimpl -> 'dir_ref -> name -> 'jimpl ty_return2; (* FIXME don't need this and unlink1 *)
    rmdir1: 'jimpl -> 'dir_ref -> name -> 'jimpl ty_return2; (* FIXME probably don't need this either *)
    touch1: 'jimpl -> 'dir_ref -> name -> 'jimpl ty_return2;
    write1: 'jimpl -> 'inode_ref -> bytes -> 'jimpl ty_return2;
    set_symlink1: 'jimpl -> 'inode_ref -> bool -> 'jimpl ty_return2 
  |>
`;

  (* calls to the fs take place in a process context *)
val fs_state_process_state_def = Hol_datatype `
fs_state_process_state = <|
    cwd4: 'dir_ref;
    fs_state4: 'impl
  |>
`;
    


  (* modelling the host *)

  (* process ids *)
val ty_pid_def = Hol_datatype `
ty_pid = Pid of num
`;

  (* a process can only make a single call into OS (so, no threads); process is blocked until return *)
val os_label_def = Hol_datatype `
os_label = OS_CALL of (ty_pid # ty_label)
    | OS_RETURN of (ty_pid # (error,ret_value) sum)
    | OS_CREATE of ty_pid
    | OS_DESTROY of ty_pid
`;


  (* file descriptors *)
val ty_fd_def = Hol_datatype `
ty_fd = FD of num
`;

  (* dir handles *)
val ty_dh_def = Hol_datatype `
ty_dh = DH of num
`;

  (* FIXME check this in linux kernel docs *)
val fd_open_closed_state_def = Hol_datatype `
fd_open_closed_state = FD_OPEN | FD_CLOSED
`;

val dh_open_closed_state_def = Hol_datatype `
dh_open_closed_state = DH_OPEN | DH_CLOSED
`;


val fd_state_def = Hol_datatype `
fd_state = <|
    open_or_closed: fd_open_closed_state;
    inode_ref2: 'inode_ref;
    offset: num
  |>
`;

val dh_state_def = Hol_datatype `
dh_state = <|
    open_or_closed: dh_open_closed_state;
    dir_ref2: 'dir_ref;
    offset: num
  |>
`;

val ty_pid_run_state_def = Hol_datatype `
ty_pid_run_state = RUNNING | BLOCKED_CALL of ('dir_ref,'inode_ref) ty_fs_label | PENDING_RETURN of ((error,ret_value) sum)
`;

val per_process_state_def = Hol_datatype `
per_process_state = <|
    (* root3: 'dir_ref; *) (* process root directory; FIXME not currently implemented *)
    cwd: 'dir_ref; (* FIXME rename this *)
    fd_table: (ty_fd,('inode_ref) fd_state) fmap;
    dh_table: (ty_dh,('dir_ref) dh_state) fmap;
    pid_run_state: ('dir_ref,'inode_ref) ty_pid_run_state
  |>
`;

val ty_os_state_def = Hol_datatype `
ty_os_state = <|
    pid_table: (ty_pid,('dir_ref,'inode_ref) per_process_state) fmap;
    fs_state: 'impl (* FIXME index this fieldname *)
  |>
`;


(* end *)

(*
## Resolve names
*)

(* module Resolve = struct *)
 
(*   open Prelude *)
(*   open Fs_types1 *)



val dest_Some_def = Define `
dest_Some = THE
`;

val butlast_def = Define `
butlast = BUTLAST
`;

val last_def = Define `
last = LAST
`;

(* FIXME map List.hd to HD, List.filter to FILTER, List.fold_left to FOLDL *)

val explode_def = Define `
explode s = (case s of 
  [] -> []
  || (c::rst) -> (STR c)::(explode rst))
`;


  (* we introduce a local type to record the result of trying to resolve a path *)
val ok_or_err_def = Hol_datatype `
ok_or_err = Ok3 of 'a | Err3 of 'b
`;

  (* let file_exists ops s0 ns = (resolve_inode_ref ops s0 ns <> None) *)

  (* get the real path, given a dir_ref *)
(* FIXME this requires a termination proof - the distance of d0_ref from the root *)
val pre_real_path_dir_ref_def = Hol_defn "real_path_dir_ref" `
real_path_dir_ref ops s0 d0_ref = (
    case (ops.get_parent1 s0 d0_ref) of
      NONE -> [""]
    || SOME(d1_ref,n) -> (real_path_dir_ref ops s0 d1_ref)++[n])
`;
val _ = Defn.tgoal pre_real_path_dir_ref_def;
p();
e(CHEAT_TAC);
val real_path_dir_ref_def = CONJUNCT1 (top_thm());

val ty_resolve_relative_ok_def = Hol_datatype `
ty_resolve_relative_ok = Dir4 of 'dir_ref
  | File4 of ('dir_ref # name # 'inode_ref)
  | None4 of ('dir_ref # name)
`;

val resolve_relative_def = Define `
resolve_relative ops s0 sofar ns = (
    case ns of 
      [] -> (Ok3(Dir4(sofar)))
    || n::ns -> (
      if (n=".") \/ (n="") then (
        resolve_relative ops s0 sofar ns
      ) else if (n="..") then (
        case ops.get_parent1 s0 sofar of
          NONE -> (resolve_relative ops s0 sofar ns) (* FIXME not correct for disconnected dirs *)
        || SOME(dir_ref,_) -> (resolve_relative ops s0 dir_ref ns)
      ) else (
        let m = ops.resolve11 s0 sofar n in
        case m of 
          NONE -> (
          if (ns=[]) \/ (ns=[""]) then (* may end in a slash *)
            Ok3(None4(sofar,n))
          else
            Err3(ENOENT))
        || SOME entry -> (
          case entry of 
            INR i0_ref -> (
            if ns=[] then (* not allowed to end in slash *)
              Ok3(File4(sofar,n,i0_ref)) 
            else
              Err3(ENOTDIR))
          || INL d0_ref -> (
            resolve_relative ops s0 d0_ref ns)))))
`;

val process_path1_def = Define `
process_path1 path = (
    let p = explode path in
    let f1 (ns,cur) c = (if c="/" then (ns++[cur],"") else (ns,cur++c)) in
    let (ns,cur) = FOLDL f1 ([],"") p in
    let ns = ns++[cur] in
    <| ns2 := ns |>)
`;

 (* assumes root not none *)
val process_name_list_def = Define `
process_name_list ops s0 cwd nl = (
   let root = dest_Some (ops.get_root1 s0) in
   if nl.ns2 = [""] then Err2(ENOENT,nl) (* nl.ns2 was the empty string *)
   else (
     let is_absolute_nl = (HD nl.ns2 = "") in
     let r = (
       if is_absolute_nl then
         resolve_relative ops s0 root nl.ns2
       else
         resolve_relative ops s0 cwd nl.ns2)
     in
     case r of
       Ok3 x -> (
       case x of
         Dir4 d0_ref -> (
         let rp = <| cwd3 := cwd; nl3 := nl; ns3 := (real_path_dir_ref ops s0 d0_ref) |> in
         Dname2(d0_ref,rp))
       || File4 (d0_ref,n,i0_ref) -> (
         let rp = <| cwd3 := cwd; nl3 := nl; ns3 := ((real_path_dir_ref ops s0 d0_ref)++[n]) |> in
         Fname2(d0_ref,n,i0_ref,rp))
       || None4 (d0_ref,n) -> 
         let rp = <|cwd3 := cwd; nl3 := nl; ns3 := (real_path_dir_ref ops s0 d0_ref)++[n] |> in
         None2 (d0_ref,n,rp))
     || Err3 x -> (Err2(x,nl))))
`;

  (* guarantees: returns option of Fname or Dname  *)
val process_path_def = Define `
process_path ops s0 cwd path = (
    let nl = process_path1 path in
    let rn = process_name_list ops s0 cwd nl in
    rn)
`;

val process_path_from_root_def = Define `
process_path_from_root ops s0 path = (
    let root = dest_Some(ops.get_root1 s0) in
    process_path ops s0 root path)
`;

val ends_with_slash_def = Define `
ends_with_slash rn = (
    let nl = name_list_of_res_name rn in
    last (nl.ns2) = "")
`;

  (* FIXME we want subsequent defns to work in terms of rname, and possible ty_name_list; we want invariants on these *)

  (* note that true = list_prefix [] [] = list_prefix xs xs; but the semantics checks e.g. whether we are rename something to itself *)
val list_prefix_def = Define `
list_prefix xs ys = (
    case (xs,ys) of
      ([],_) -> T
    || (_,[]) -> F
    || (x::xs,y::ys) -> (
      if (x=y) then list_prefix xs ys else F))
`;

  (* check if renaming a dir to a subdir of itself; we expect to check for equality before calling this *)
val subdir_def = Define `
subdir s d = (
    list_prefix s.ns3 d.ns3)
`;


(* end *)

(*
## `Fs_ops2`
*)

(* FIXME these work in terms of rnames; assumes no Err2 *)
(* module Fs_ops2 = struct *)
  
(*   open Unix (* for st_dev record fields etc *) *)
(*   open LargeFile (* FIXME include stats in Fs_types1? *) *)

(*   open Prelude *)
(*   open Fs_types1 *)
(*  open Fs_ops1 *)
  (* open Resolve *)


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

val return_def = Define `
return x = Mymonad (\ s . finset_insert (Inr(s,x)) finset_empty)
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

val cond_raise_def = Define `
cond_raise bes = Mymonad (\ s . let bs = FILTER (\ (b,e) . b=T) bes in
    if bs=[] then 
      finset_singleton(Inr(s,()))
    else
      finset_image (\ (b,e) . INL(s,e)) bs)
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

  (* posix/1 *)

(* FIXME \ _ not liked *)

(* FIXME define sub *)
val sub_def = Define `
sub bs ofs len = SEG ofs (ofs+len) bs
`;

(* FIXME original defn doesn't work in HOL if m=0, since n can't get lower *)
val downto'_def = Define `
downto' n m = (if ((n=0) /\ (m=0)) then [0] else (if n < m then [] else n::(downto' (n-1) m)))
`;

(* FIXME match let SOME(x) = not accepted by HOL *)

(* FIXME this should produce a list of length len, based on xs *)
val resize_def = Define `
resize xs len = TAKE len xs
`;

(* FIXME MyDynarray.resize *)

(* FIXME this should create a new list based on bs' *)
val mywrite = Define `
mywrite (bs,i,j) (bs',ofs) = bs'
`;

val link_def = Define `
link ops spath dpath = (
    get_state >>= \ s0 . case spath of 
      Fname2(d0_ref,name,i0_ref,rp)  -> (
      case dpath of 
        None2 (d0_ref,n,rp) -> (
        let s0 = ops.link_file1 s0 i0_ref d0_ref n in
        put_state' s0)
      || Err2(e,_) -> (
        (* (maybe_raise EEXIST) >>= fun _ -> ( * arguably linux bug * ) *)
        myraise e)
      || Fname2 _ -> (myraise EEXIST)
      || Dname2 _ -> (myraise EEXIST))
    || Dname2 _ -> (
      (case dpath of
          Err2(e,_) -> (maybe_raise e)
        || _ -> do_nothing) >>= (\ _x_ . myraise EPERM))
    || Err2(e,_) -> (myraise e)
    || None2 __ -> (myraise ENOENT))
`;


val mkdir_def = Define `
mkdir ops rpath perms = (
    (* FIXME deal with perms *)
    get_state >>= \ s0 . case rpath of 
      None2(d0_ref,n,_) -> (
      let s0 = ops.mkdir1 s0 d0_ref n in
      put_state' s0)
    || Err2(e,_) -> (myraise e)
    || Dname2 _ -> (myraise EEXIST)
    || Fname2 _ -> (myraise EEXIST))
`;


  (* FIXME we have to take care of flags eg O_TRUNC *)
  (* FIXME return is int option - meaning optional file handle? *)
  (* FIXME why is this called fopen (taking an fd?) rather than open? *)
  (* FIXME the mapping between fds and files is handled elsewhere - needs a new part of spec *)
val o_open_def = Define `
o_open ops rpath flags = (
    get_state >>= \ s0 . case rpath of
      None2 _ -> (myraise ENOENT)
    || Dname2(_,_) -> (myraise ENOENT) (* FIXME should be EISDIR? can we open a dir? *)
    || _ -> (return None1))
`;

val open_create_def = Define `
open_create ops rpath = (
    get_state >>= \ s0 . case rpath of 
      Dname2 _ -> (myraise EEXIST) 
    || Fname2 _ -> (myraise EEXIST)
    || Err2 (e,_) -> (myraise e)
    || None2(d0_ref,n,ns) -> (
      (* FIXME for us, open_create should only create files *)
      if ends_with_slash rpath then 
        myraise EISDIR
      else
        let s0 = ops.touch1 s0 d0_ref n in
        put_state' s0))
`;

  (* FIXME the real spec would allow reading less than all the bytes; recall len is maxlen *)
(* FIXME MyDynArray.dim maps to LENGTH *)
val read_def = Define `
read ops rn ofs len = (
    case rn of 
      None2 _ -> (myraise ENOENT)
    || Dname2 _ -> (myraise ENOENT)
    || Err2 (e,_) -> (myraise e)
    || Fname2(d0_ref,n,i0_ref,rp) -> (
      get_state >>= (\ s0 . (
      let r = ops.read1 s0 i0_ref in (* FIXME Fs_ops1 may have to take an offset too *)
      (put_state' r) >>= \ _x_ . choose (downto' len 0) >>= \ len . let bs = dest_bytes1 r.ret2 in
      let len_bs = LENGTH bs in
      (* assume ofs is wellformed *)
      let len = if ofs+len <= len_bs then len else len_bs - ofs in
      (* let _ = print_endline ("read len_bs: "^(string_of_int len_bs)^"; len: "^(string_of_int len)^"; ofs: "^(string_of_int ofs)) in *)
      (* let _ = print_endline "before" in *)
      let bs' = sub bs ofs len in
      (* let _ = print_endline "after" in *)
      return (Bytes1(bs'))))))
`;

val readdir_def = Define `
readdir ops rn = (
    get_state >>= (\ s0 . (
    case rn of 
      Err2 (e,_) -> (myraise e)
    || None2 _ -> (myraise ENOENT) (* (raise (Unix_error (ENOENT,"readdir","/FIXMEreaddir"))) ( * FIXME we may need access to the underlying path that was given by the user * ) *)
    || Fname2 _ -> (myraise ENOTDIR) (* (raise (Unix_error (ENOTDIR,"readdir","/FIXMEreaddir"))) *)
    || Dname2(d0_ref,rp) -> (
      let r = ops.readdir1 s0 d0_ref in
      (put_state' r) >>= (\ _x_ . (
      return r.ret2))))))
`;
  (* NB later we may want to also return a state, given access times can cause changes when reading etc *)

  (* FIXME surely a lot of this complexity is because this is the user land behaviour of the mv command - but we want to target the syscall interface *)
  (* FIXME we probably want the containing dirs as well, when doing rename; put this in resolve *)
  (* FIXME rename to subdir of self? *)
  (* NB if an error is possible, then all transitions result in an error; we should check that this invariant holds of the spec *)

  (* posix/2 *)

val rename_def = Define `
rename ops rsrc rdst = (
    get_state >>= (\ s0 . case rsrc of
      None2 _ -> (
      (* target may have ENOENT path *)
      (case rdst of 
        Err2 (e',_) -> (
        maybe_raise e') (* tr/11 *)
      || _ -> do_nothing) >>= (\ _x_ . (
        myraise ENOENT))) (* no src file *)
    || Err2 (e,_) -> (
      (* target may have ENOENT path *)
      (case rdst of 
        Err2 (e',_) -> (
        maybe_raise e') (* tr/1 *)
      || _ -> do_nothing) >>= (\ _x_ . (
      myraise e))) (* tr/2 *)
    || Fname2 (d0_ref,nsrc,i0_ref,rp) -> (
      case rdst of 
        Err2 (e,_) -> (myraise e)
      || None2 (d1_ref,ndst,rp) -> (
        (let cond1 = ends_with_slash rdst in
        cond_raise [(cond1,ENOTDIR)]) >>= \ _x_ . put_state'' (\ () . ops.mv1 s0 d0_ref nsrc d1_ref ndst))
      || Fname2 (d1_ref,ndst,i1_ref,rp) -> (
        (* do the move; there is a file name ns_dst *)
        if (d1_ref=d0_ref) /\ (ndst=nsrc) then 
          return None1 (* tr/4 *)
        else
          put_state'' (\ () . ops.mv1 s0 d0_ref nsrc d1_ref ndst))
        (* FIXME may want to have putstate return a void value *)
      || Dname2 (d0_ref,rp) -> (
        (* several reasonable options *)
        (if (ends_with_slash rdst) then 
          maybe_raise ENOTDIR         (* tr/5 arguably a Linux bug? Confirmed non-posix behaviour *)
        else 
          do_nothing) >>= (\ _x_ . if ((ops.readdir1 s0 d0_ref).ret2<>Names1[]) then 
          maybe_raise ENOTEMPTY       (* tr/6 strange, but posix allows this; FIXME posix also allows EEXIST in this case *)
        else
          do_nothing) >>= (\ _x_ . myraise EISDIR))) (* expected *)
    || Dname2 (d0_ref,rps) -> (
      (* rename a directory; directory exists *)
      case rdst of
        None2 (d1_ref,ndst,rpd) -> (
        (* do the move; there is no file ns_dst *)
        if (resolve_subdir rps rpd) then 
          myraise EINVAL
        else
          let p = ops.get_parent1 s0 d0_ref in
          case p of 
            NONE -> (
            (* src was root *)
            myraise EINVAL)
          || SOME(d0_ref,nsrc) -> (
            put_state'' (\ () . ops.mvdir1 s0 d0_ref nsrc d1_ref ndst)))
      || Err2 (e,_) -> (
        (maybe_raise EINVAL) >>= (\ _x_ . myraise e))
      || Fname2 (_,_,_,rpd) -> (
        (* check rename to subdir before rename to file; NB there are different reasonable options here *)
        (if (resolve_subdir rps rpd) then
          maybe_raise EINVAL 
        else 
          do_nothing) >>= (\ _x_ . myraise ENOTDIR)) 
      || Dname2 (d1_ref,rpd) -> (
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
          let x = ops.get_parent1 s0 d0_ref in
          let y = ops.get_parent1 s0 d1_ref in
          case (x,y) of
            (NONE,_) -> (myraise EINVAL)
          || (_,NONE) -> (
            failwith "impossible rename of dir onto root; can't happen because dst must be nonempty")
          || (SOME(d0_ref',nsrc),SOME(d1_ref',ndst)) -> (
            put_state'' (\ () . ops.mvdir1 s0 d0_ref' nsrc d1_ref' ndst))))))
`;

val rmdir_def = Define `
rmdir ops rpath = (
    get_state >>= \ s0 . case rpath of 
      Dname2(d0_ref,rp) -> (
      if ((ops.readdir1 s0 d0_ref).ret2<>Names1[]) then
        (myraise ENOTEMPTY)
      else
        let x = ops.get_parent1 s0 d0_ref in
        case x of 
          NONE -> (
          (* attempt to remove the root directory, may fail or succeed *)
          (maybe_raise EBUSY) >>= (\ _x_ . (return None1)))
        || SOME(d1_ref,n) -> (
          let s0 = ops.unlink1 s0 d1_ref n in
          put_state' s0))
    || Fname2 _ -> (myraise ENOTDIR)
    || None2 _ -> (myraise ENOENT)
    || Err2 (e,_) -> (myraise e))
`;

val stat_def = Define `
stat ops rn = (
    get_state >>= (\ s0 . (
    (* let _ = (print_endline ("stat: "^(string_of_res_name rn))) in *)
    case rn of
      Err2 (e,_) -> (myraise e)
    || None2 _ -> (myraise ENOENT) 
    || Fname2(d0_ref,n,i0_ref,rp) -> (return (Stats1 (default_file_stats ops s0 i0_ref)))
    || Dname2(d0_ref,rp) -> (return (Stats1 (default_dir_stats ops s0 d0_ref))))))
`;

val truncate_def = Define `
truncate ops rpath len = (
    get_state >>= \ s0 . case rpath of 
      Err2 (e,_) -> (myraise e)
    || None2 _ -> (myraise ENOENT)
    || Dname2 _ -> (myraise EISDIR) (* FIXME check error messages are sensible *)
    || Fname2(d0_ref,n,i0_ref,rp) -> (
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
      Err2(e,_) -> (myraise e)
    || None2 _ -> (myraise ENOENT)
    || Dname2 _ -> (myraise EISDIR) (* LSB has EISDIR; POSIX requires EPERM *)
    || Fname2(d0_ref,n,i0_ref,rp) -> (
      (* FIXME for resolving a file, often useful to have dir ref as well *)
      let s0 = ops.unlink1 s0 d0_ref n in
      put_state' s0))
`;

  (* FIXME we need to make this take an offset in order to be usable, also read *)
val write_def = Define `
write ops rn ofs bs len = (
    get_state >>= \ s0 . case rn of 
      Err2 (e,_) -> (myraise e)
    || None2 _ -> (myraise ENOENT) 
    || Dname2 _ -> (myraise ENOENT)
    || Fname2(d0_ref,n,i0_ref,rp) -> (
      choose (downto' len 0) >>= \ len . let r = ops.read1 s0 i0_ref in
      let bs' = dest_bytes1 r.ret2 in
      (* want to create a new array from bs' and bs *)
      let bs'' = mywrite (bs,0,len) (bs',ofs) in
      let r = ops.write1 s0 i0_ref bs'' in
      put_state' r >>= \ _x_ . return (Int1 len)))
`;

  (* FIXME this is a hack - should do lots of checking eg src is a dir *)
  (*
  let symlink ops src dst = (
    open_create ops dst >>= fun _x_ -> 
    write ops dst 0 (MyDynArray.of_string src) (String.length src) >>= fun _x_ -> 
    get_state >>= fun s0 ->
    let rpath = process_path ops s0 dst in
    let Fname2(i0_ref,_) = rpath in
    let r = ops.set_symlink1 s0 i0_ref true in
    put_state' r)
  let (_:ty_ops' -> string -> string -> ret_value ty_mymonad') = symlink    
  *)

(* end *)


(*
## Fs transition system
*)

(* module Fs_transition_system = struct *)

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
val fs_trans_def = Define `
fs_trans ops s0 lbl = (
    (* let _ = print_endline (string_of_label lbl) in *)
    let m = (case lbl of 
        FS_LINK (s,d) -> (link ops s d)
      || FS_MKDIR (s,p) -> (mkdir ops s p)
      || FS_OPEN (p,fs) -> (
          if (MEM O_CREAT fs) then (open_create ops p (* FIXME fs *)) 
          else (o_open ops p fs))
      || FS_READ (p,i,j) -> (read ops p i j)
      || FS_READDIR p -> (readdir ops p)
      || FS_RENAME (s,d) -> (rename ops s d)
      || FS_RMDIR p -> (rmdir ops p)
      || FS_STAT p -> (stat ops p)
      || FS_SYMLINK (s,d) -> failwith "FIXME" (* (symlink ops s d) *)
      || FS_TRUNCATE (p,l) -> (truncate ops p l)
      || FS_UNLINK p -> (unlink ops p)
      || FS_WRITE (p,ofs,bs,len) -> (write ops p ofs bs len))
    in
    let rs = run_mymonad m s0 in
    let f1 ve = (case ve of
        INL(s,e) -> (s,INL e)
      || INR(s,v) -> (s,INR v))
    in
    let rs = MAP f1 rs in
    rs)
`;
(*  let (_:ty_ops' -> state' -> ty_fs_label' -> (state' * (error,ret_value)sum) finset) = fs_trans *)

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

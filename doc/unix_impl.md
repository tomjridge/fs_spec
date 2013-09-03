# `unix_impl.ml`
## `Unix_impl_everything` 

A proxy to the underlying unix filesystem.

~~~{.ocaml}

open Fs_prelude
open Fs_spec

module Unix_impl_everything = struct

  (* this code copied from persistent queue code; basically allows
     reading and writing a file in a complicated, but hopefully safe,
     way (!); FIXME one problem with these functions is that it is not
     clear what the error is (if one occurs) - FIXME return an option type  *)
  module Pqueue = struct

    module Prelude = struct
    
      let debug s = (print_string s; flush stdout)
    
      let rec itlist f l b =
        match l with
          [] -> b
        | (h::t) -> f h (itlist f t b)
 
      (*
      let fsync = Core.Std.Unix.fsync
      let fdatasync = Core.Std.Unix.fdatasync
      *)
    
      let is_Some x = x <> None
      
      let dest_Some x = match x with Some y -> y | _ -> failwith "dest_Some"
    
      (* FIXME change Unix.close in following to close_fd_noerr *)
      let close_fd_noerr fd = try Unix.close fd with _ -> ()
    
      type ('a,'b) sum = Inl of 'a | Inr of 'b
      
      let is_Inl x = (match x with | Inl x -> true | _ -> false)
      let is_Inr x = (match x with | Inr x -> true | _ -> false)
    
      let dest_Inl x = (match x with | Inl x -> x | _ -> failwith "dest_Inl")
      let dest_Inr x = (match x with | Inr x -> x | _ -> failwith "dest_Inr")
    
      module State_error = struct
    
        type ('s,'a) ty_state_error = SE1 of ('s -> (exn * 's,'a*'s) sum)
    
        let dest_SE1 (SE1 f) = f
    
        let return x = SE1 (fun s -> Inr (x,s))
    
        let bind x f = SE1 (fun s ->
          let x' = (dest_SE1 x) s in
          match x' with
          | Inl (exn,s) -> Inl (exn,s)
          | Inr (a,s) -> dest_SE1 (f a) s)
    
        let ( >>= ) = bind
    
        let put s' = SE1 (fun s -> Inr ((),s'))
        let (_:'s -> ('s,unit) ty_state_error) = put
    
        let get = SE1 (fun s -> Inr(s,s))
        let (_:('s,'s) ty_state_error) = get
    
        let wrap f = SE1 (fun s -> try let fd = f () in Inr(fd,s) with e -> Inl (e,s))
        let (_:(unit -> 'a) -> ('s,'a) ty_state_error) = wrap
        (* FIXME generalize above type? *)
    
        let run_SE1 s f = (dest_SE1 f) s
    
        (* a la Isabelle *)
        let ( |> ) x f = (f x)
    
      end  
    
    
      type myfusebuffer = (char, Bigarray.int8_unsigned_elt, Bigarray.c_layout) Bigarray.Array1.t
    
      module A = Bigarray.Array1
    
      (* convenience only; don't use in production code *)
      let array_of_string bs = (
        let arr = (Array.init (String.length bs) (String.get bs)) in
        let contents = A.of_array Bigarray.char Bigarray.c_layout arr in
        contents)
      let (_:string -> myfusebuffer) = array_of_string
    
      (* convenience only; don't use in production code *)
      let string_of_array bs = (
        let s = String.create (A.dim bs) in
        let _ = (
          for i = 0 to (String.length s) - 1 do
            String.set s i (A.get bs i) 
          done)
        in
        s)
    
      (* convert an array of 8 bytes into an int64; bytes are stored most significant first *)
      let int64_of_bytes arr = (
        let bs = List.map (Bigarray.Array1.get arr) [0;1;2;3;4;5;6;7] in
        let f acc b = (
          let acc = Int64.shift_left acc 8 in
          let i = Char.code b in
          let low_8_bits = Int64.of_int i in
          let acc = Int64.logor acc low_8_bits in
          acc)
        in
        List.fold_left f Int64.zero bs)
    
      (* convert an int64 into an array of bytes *)
      let bytes_of_int64 n = (
        let arr = array_of_string "01234567" in
        let bs = [7;6;5;4;3;2;1;0] in
        let f i ind = (
          let b = (
            let i = Int64.logand i 255L in
            let i = Int64.to_int i in
            let i = Char.chr i in
            i)
          in
          let _ = A.set arr ind b in
          let i = Int64.shift_right i 8 in
          i)
        in
        let _ = (List.fold_left f n bs) in
        arr)
      let (_:int64 -> myfusebuffer) = bytes_of_int64
    
    
      let rec replicate x n =
        if n < 1 then []
        else x::(replicate x (n - 1));;
    
    end
    
    module Types = struct
    
      type myfusebuffer = (char, Bigarray.int8_unsigned_elt, Bigarray.c_layout) Bigarray.Array1.t
    
      type path = string
    
      type pre_file_queue = { dir1:path; index1:int64; msgs1:myfusebuffer list }
    
      type file_queue = File_queue of pre_file_queue
    
      exception File_exception
    
    end
    
    module File_utils = struct
    
      open Prelude
      open Types
      open Prelude.State_error
    
      type myfusebuffer = (char, Bigarray.int8_unsigned_elt, Bigarray.c_layout) Bigarray.Array1.t
    
      (* sync the file, and the containing dir *)
      (* in the following, we might like to verify that if an exception is
         thrown, then at least one exception is reported (the main code
         and the tidy up code could both throw an exception); the fd is
         always closed exactly once; might also like to think about an
         fd-passing interface with type-checking to verify that arguments
         are used linearly; this could be a simple syntactic check
         (assuming all sub-functions use the argument linearly); the
         problem may be in the tidy up code, where fd is used again - how
         do we know this is linear? because the tidy code is executed
         following a failure during the main se code ... WRONG! and the
         failure should really return a new fd reference rather than throw
         an exception *)
      (*
      let myfsync dirname name = (
        let filename = dirname^"/"^name in
        let se = (
          (* sync filename *)
          put None >>= fun _ ->
          wrap (fun () -> Unix.openfile filename [Unix.O_RDONLY] 0o777) >>= fun fd ->
          put (Some(1,fd)) >>= fun _ ->
          wrap (fun () -> let _ = fsync fd in fd) >>= fun fd ->
          put (Some(2,fd)) >>= fun _ ->
          wrap (fun () -> let _ = Unix.close fd in fd) >>= fun fd ->
          (* sync dirname *)
          put None >>= fun _ ->
          wrap (fun () -> Unix.openfile dirname [Unix.O_RDONLY] 0o777) >>= fun fd ->
          put (Some(3,fd)) >>= fun _ ->
          wrap (fun () -> let _ = fsync fd in fd) >>= fun fd ->
          put (Some(4,fd)) >>= fun _ ->
          wrap (fun () -> let _ = Unix.close fd in fd) >>= fun fd ->
          put None)
        in
        let r = run_SE1 None se in
        (* tidy up *)
        let _ = (match r with 
          | Inl (e,Some(1,fd)) -> (
            (* failed on the fsync; FIXME really fsync fd and similar funs
               should always return an fd, with a queryable state? or some
               generic error reporting strategy ie using the State_error
               monad; currently we are halfway there *)
            close_fd_noerr fd)
          | Inl (e,Some(2,fd)) -> () (* failed on the close; but fd still closed *)
            (* FIXME in the following, we don't report an error on this close properly *)
          | Inl (e,Some(3,fd)) -> (close_fd_noerr fd)
          | Inl (e,Some(4,fd)) -> () 
          | _ -> ())
        in
        match r with | Inl _ -> raise File_exception | Inr _ -> ())        
      let (_: string -> string -> unit) = myfsync
      *)  
    
    
        (* from http://rosettacode.org/wiki/Read_entire_file#OCaml ; when does memory mapping occur? before Unix.close? or does it continually refer to the file on disk? *)
    
    
      (* tr notes: if the file is empty, the mapping fails; so in this case, we do something special *)
      let read_file_as_array filename = (
        let se = (
          put None >>= fun _ ->
          wrap (fun () -> Unix.openfile filename [Unix.O_RDONLY] 0o777) >>= fun fd -> 
          put (Some(1,fd)) >>= fun _ ->
          wrap (fun () -> let len = Unix.lseek fd 0 Unix.SEEK_END in (fd,len)) >>= fun (fd,len) -> 
          wrap (fun () -> let _ = Unix.lseek fd 0 Unix.SEEK_SET in fd) >>= fun fd -> 
          put (Some(2,fd)) >>= fun _ ->
          let shared = false in  (* modifications are done in memory only *)
          let bstr = (
            if len=0 then (
              Bigarray.Array1.create Bigarray.char Bigarray.c_layout 0
            ) else (
              Bigarray.Array1.map_file fd Bigarray.char Bigarray.c_layout shared len))
          in
          return bstr >>= fun bstr -> 
          put (Some(3,fd)) >>= fun _ ->
          wrap (fun () -> let _ = Unix.close fd in fd) >>= fun fd ->
          return bstr)
        in
        let r = run_SE1 None se in
        let _ = (match r with
          | Inl(e,Some(1,fd)) -> (close_fd_noerr fd)
          | Inl(e,Some(2,fd)) -> (close_fd_noerr fd)
          | Inl(e,Some(3,fd)) -> ()
          | _ -> ())
          (* FIXME may also want to call release on the fd *)
        in
        match r with 
        | Inl _ -> raise File_exception
        | Inr (bstr,_) -> bstr)
      let (_:string -> myfusebuffer) = read_file_as_array
    
      (* FIXME probably doesn't work if arr length 0 *)
      let write_array_as_file arr filename = (
        let len = Bigarray.Array1.dim arr in
        let se = (
          put None >>= fun _ -> 
          wrap (fun () -> Unix.openfile filename [Unix.O_RDWR;Unix.O_CREAT;Unix.O_TRUNC] 0o640) >>= fun fd ->
          put (Some(1,fd)) >>= fun _ -> 
          wrap (fun () -> let _ = Unix.lseek fd 0 Unix.SEEK_SET in fd) >>= fun fd -> 
          put (Some(2,fd)) >>= fun _ -> 
          let shared = true in 
          let bstr = (Bigarray.Array1.map_file fd Bigarray.char Bigarray.c_layout shared len) in
          let _ = Bigarray.Array1.blit arr bstr in 
          return bstr >>= fun bstr ->
          put (Some(3,fd)) >>= fun _ ->
          wrap (fun () -> let _ = Unix.close fd in fd) >>= fun fd -> 
          return bstr)
          (* FIXME don't we need msync and munmap if we want to write using maps? *)
          (* let _ = msync bstr in msync called by release *)
          (* FIXME FIXME release not in Bigarray.Genarray yet *)
          (* let _ = release fd in *)
        in
        let r = run_SE1 None se in
        let _ = (match r with
          | Inl(e,Some(1,fd)) -> (close_fd_noerr fd)
          | Inl(e,Some(2,fd)) -> (close_fd_noerr fd)
          | Inl(e,Some(3,fd)) -> ()
          | _ -> ())
          (* FIXME may also want to call release on the fd *)
        in
        match r with 
        | Inl _ -> raise File_exception
        | _ -> ())
      let (_:myfusebuffer -> string -> unit) = write_array_as_file
    
      (*
      let write_array_atomically arr dirname name = (
        try (
          let tmpname = name^".tmp" in
          let _ = try Unix.unlink (dirname^"/"^tmpname) with Unix.Unix_error _ -> () in 
          let _ = write_array_as_file arr (dirname^"/"^tmpname) in
          let _ = myfsync dirname tmpname in
          let _ = Unix.rename (dirname^"/"^tmpname) (dirname^"/"^name) in
          let _ = myfsync dirname name in
          ()
        ) with e -> raise File_exception)  
      let (_:myfusebuffer -> string -> string -> unit) = write_array_atomically
      *)
    
      let file_exists filename = (
        try (
          let _ = Unix.stat filename in
          true
        ) with _ -> false)
    
    
    end

  end (* Pqueue *)



  open Prelude
  open Fs_types1 (* FIXME remove dependence? have a core types and a state types? *)

  type dir_ref = string list
  type inode_ref = string list


  type impl = { r1:dir_ref } (* r1 is the overall root; need to be careful when making symlinks *)

  let string_of_names s0 ns = ("/"^(String.concat "/" (s0.r1@ns)))

  (* FIXME what do we do if the call throws an error? Ideally the
     later levels should ensure these funcs are never called such that
     they can throw an error; so this is actually an error in the
     later levels probably *)

  let do_try' f x = try (f x) with e -> (print_endline "unix_impl: this should not happen"; raise e)
  let do_try f x s0 = try (f x); return s0 with e -> (print_endline "unix_impl: this should not happen"; raise e)

  let dest_ref s0 d0_ref = (    
    let f () = (
      let s = try Some(Unix.LargeFile.stat (string_of_names s0 d0_ref)) with _ -> None in
      match s with 
      | Some s -> (s.Unix.LargeFile.st_ino)
      | None -> (failwith "unix_impl/dest_ref"))
    in
    do_try' f ())

  (* FIXME this is a hack - dest_dir_ref will work on inode_refs etc *)
  let dest_dir_ref = dest_ref
  let dest_inode_ref = dest_ref
    

  let link_file s0 i0_ref d0_ref name = (
    let f () = Unix.link (string_of_names s0 i0_ref) (string_of_names s0 (d0_ref@[name])) in
    do_try f () s0)

  let unlink s0 d0_ref name = (
    let f () = Unix.unlink (string_of_names s0 (d0_ref@[name])) in
    do_try f () s0)

  let mkdir s0 d0_ref name = (
    let f () = Unix.mkdir (string_of_names s0 (d0_ref@[name])) 0o777 in
    do_try f () s0)

  let mv s0 d0_ref name0 d1_ref name1 = (
    let f () = Unix.rename (string_of_names s0 (d0_ref@[name0])) (string_of_names s0 (d1_ref@[name1])) in
    do_try f () s0)

  let mvdir s0 d0_ref name0 d1_ref name1 = (
    let f () = Unix.rename (string_of_names s0 (d0_ref@[name0])) (string_of_names s0 (d1_ref@[name1])) in
    do_try f () s0)

  let read s0 i0_ref = (
    let f () = (
      let arr = Pqueue.File_utils.read_file_as_array (string_of_names s0 i0_ref) in
      {state2=s0; ret2=(Bytes1 (MyDynArray.of_array arr))})
    in
    do_try' f ())

  let readdir s0 d0_ref = (
    let f () = (
      let dh = Unix.opendir (string_of_names s0 d0_ref) in
      let s = ref [] in
      let rec g () = (
        (s:=(Unix.readdir dh)::(!s)); g ())
      in
      let _ = try g () with _ -> () in
      let names = List.filter (fun x -> x <> "." && x <> "..") (!s) in
      let names = List.sort Pervasives.compare names in
      {state2=s0; ret2=(Names1 names)})
    in
    do_try' f ())

  let resolve1 s0 d0_ref name = (
    let f () = (
      let s = try Some(Unix.LargeFile.stat (string_of_names s0 (d0_ref@[name]))) with _ -> None in
      match s with 
      | Some s -> (
        if (s.Unix.LargeFile.st_kind = Unix.S_DIR) then 
          Some(Inl(d0_ref@[name]))
        else
          Some(Inr(d0_ref@[name])))
      | None -> None)
    in
    do_try' f ())      

  let rm = unlink

  let rmdir = unlink

  let touch s0 d0_ref name = (
    let f () = (
      let fd = Unix.openfile (string_of_names s0 (d0_ref@[name])) [Unix.O_CREAT] 0o777 in
      let _ = Unix.close fd in
      ())
    in
    do_try f () s0)

  (* at the moment, fs_spec means that a write involves a read of the
     entire file; this will be very costly with this unix
     implementation *)
  let write s0 i0_ref c = (
    let f () = (
      let arr = Pqueue.File_utils.write_array_as_file (MyDynArray.to_array c) (string_of_names s0 i0_ref) in
      ())
    in
    do_try f () s0)
    
  let state0 = { r1=["tmp";"unix_impl_test"] }

  let ops1 = {
    get_init_state1=(fun () -> state0);
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



~~~

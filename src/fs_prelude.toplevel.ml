module Fs_prelude = struct 
(*
# fs_prelude.ml
## Prelude

The initial code for `MyDynArray` is a hacky attempt to implement
dynamic arrays. Later I wanted functional arrays (no update in place)
which I tacked on. TODO this all needs to be redone. We want a
functional interface and an efficient implementation that assumes
linear usage (ie updates in place). We should also check that uses are
linear.

*)

(* some basic list defns *)

(* downto n m = [n;n-1;...;m] *)
let rec downto' n m = (if n < m then [] else n::(downto' (n-1) m))


(* sets as lists *)
module Finset = struct

  type 'a finset = 'a list

  let empty_finset = []

  let finset_empty = []

  let finset_diff xs1 xs2 = (
    let f1 a x = (if (not (List.mem x xs2)) then x::a else a) in
    List.fold_left f1 [] xs1)
    
  let finset_subset xs1 xs2 = (finset_diff xs1 xs2 = empty_finset)

  let finset_equal xs1 xs2 = ((finset_subset xs1 xs2) && (finset_subset xs2 xs1))

  let finset_mem x xs = (List.mem x xs)

  let finset_union xs1 xs2 = xs1 @ xs2

  let finset_insert x xs = (if List.mem x xs then xs else x::xs)

  let finset_partition = List.partition

  let finset_bigunion = List.concat (* do we want to remove duplicates? FIXME do our finsets have duplicates? *)

  let finset_singleton x = finset_insert x finset_empty

  let finset_image f x = List.map f x

  let finset_choose xs = (
    if xs = finset_empty then failwith "finset_choose: empty finset" else List.hd xs)

end

include Finset

module Fmap = struct

  type ('dom,'cod) fmap = ('dom * 'cod) list
  
  let fmap_remove m a = (List.filter (fun (a',_) -> a' <> a) m)
  let fmap_update m (a,b) = (a,b)::(fmap_remove m a)
  let fmap_lookup m a = try Some(List.assoc a m) with _ -> None
  let fmap_dom m = List.map fst m
  let fmap_empty = []

end

include Fmap  


(* dynamic arrays: resize an array to a target size, using doubling *)
module MyDynArray1 = struct
  
  module A = Bigarray.Array1
  
  type myfusebuffer = (char, Bigarray.int8_unsigned_elt, Bigarray.c_layout) Bigarray.Array1.t
  
  type t = myfusebuffer (* keep abstract? *)
  
  (* let get_array (da:t) = (da:myfusebuffer) *)

  (* FIXME hopefully this works with 0 length arrays *)
  (* target <= resize' target cur *)
  let rec resize' target cur = (
    let cur = (if cur=0 then 1 else cur) in
    if target <= cur then cur else resize' target (2*cur))
  
  (* resize an array so that it is at least as big as n; invariant: minsize <= dim (resize da minsize) *)
  let resize da minsize = (
    let cur = Bigarray.Array1.dim da in
    let newsize = resize' minsize cur in
    if (newsize = cur) then da else (
      let newbuf = A.create (A.kind da) (A.layout da) newsize in
      let _ = A.blit da (A.sub newbuf 0 (A.dim da)) in
      newbuf))
      
end

module type MYDYNARRAY = sig

  type myfusebuffer = (char, Bigarray.int8_unsigned_elt, Bigarray.c_layout) Bigarray.Array1.t

  type t

  val of_array : myfusebuffer -> t

  val of_string : string -> t

  val to_array: t -> myfusebuffer

  val to_string: t -> string

  val repn: t -> int * myfusebuffer

  val create : unit -> t

  val dim : t -> int

  val resize : t -> int -> t

  val get: t -> int -> char

  val set: t -> int -> char -> t

  val blit : t * int * int -> t * int -> t

  (* FIXME don't need if have to_array etc? *)
  (* val blit_array1: t * int * int -> myfusebuffer * int -> int *)

  val sub: t -> int -> int -> t

  (* copy bytes from arr1 to arr2, giving a new array *)
  val write: (t*int*int) -> (t*int) -> t

end


(* like an array, but the array is potentially larger than the data we need to store, so we also keep track of the length of the data *)
module MyDynArray2 = struct

  type myfusebuffer = (char, Bigarray.int8_unsigned_elt, Bigarray.c_layout) Bigarray.Array1.t

  module A = Bigarray.Array1

  (* i is the length of the dynamic array, given some implementation; invariant (i,arr): i <= dim arr *)
  type t = int * MyDynArray1.t

  type mynewtypefixme = int

  let repn (i,arr) = (i,arr)

  let dim (i,arr) = i

  let resize (i,arr) j = (j,MyDynArray1.resize arr j)

  let of_array arr = (A.dim arr,arr)

  (* convenience only; don't use in production code *)
  let of_string bs = (
    let arr = (Array.init (String.length bs) (String.get bs)) in
    let contents : myfusebuffer = A.of_array Bigarray.char Bigarray.c_layout arr in
    of_array contents)

  (* FIXME we could return the underlying array directly, with a sub *)
  let to_array (i,arr1) = (
    let arr2 = A.create Bigarray.char Bigarray.c_layout i in
    let _ = A.blit (A.sub arr1 0 i) arr2 in
    arr2)

  let to_string (i,arr1) = (
    let s = String.create i in
    let _ = 
      for j=0 to i-1 do
        String.set s j (A.get arr1 j)
      done
    in
    s)

  let create () = (
    let arr = A.create Bigarray.char Bigarray.c_layout 4096 in
    let _ = A.fill arr '\x00' in
    (0, arr))

  let get (i,arr) j = (if j<i then A.get arr j else raise (Invalid_argument "MyDynArray2: get, index out of bounds"))

  let set (i,arr) j c = (
    let arr = (if j > A.dim arr then (MyDynArray1.resize arr j) else (arr)) in
    let i = (if j >= i then j+1 else i) in
    let _ = A.set arr j c in
    (i,arr))

  (* assumes ofs1+len1<i (sim with the other ops) ; resizes if necessary, ie may not mutate in place! *)
  let blit ((i1,arr1),ofs1,len1) ((i2,arr2),ofs2) = (
    let size2 = ofs2+len1 in
    let (i2,arr2) = (
      if (i2 < size2) then (size2,MyDynArray1.resize arr2 size2) else (i2,arr2))
    in
    let _ = A.blit (A.sub arr1 ofs1 len1) (A.sub arr2 ofs2 len1) in
    (i2,arr2))

  (* arr2 is a buffer eg that we are reading to; we return the number of bytes copied *)
  (* assumes ofs1+len1 < i1 *)
  (*
  let blit_array1 ((i1,arr1),ofs1,len1) (arr2,ofs2) = (
    let len = min len1 (A.dim arr2 - ofs2) in
    let _ = A.blit (A.sub arr1 ofs1 len) (A.sub arr2 ofs2 len) in
    len)
  *)

  (* FIXME we need a module representing arrays, but where the ops act functionally ie they return a new array every time *)
  (* FIXME decide what the functional interface to arrays should be; maybe we should mutate and assume arrays are used linearly? *)
  (* behaves as functional call *)
  let sub (i,arr) ofs len = (
    let arr2 = A.sub arr ofs len in
    (A.dim arr2,arr2))
 
  let copy (i,arr) = (
    let arr' = create () in
    let _ = blit ((i,arr),0,i) (arr',0) in
    arr')

  (* behaves as functional call *)
  let write ((i2,arr2),ofs2,len2) (arr1,ofs1)  = (
    let arr2 = blit ((i2,arr2),ofs2,len2) (arr1,ofs1) in
    arr2)
   
end

module MyDynArray = (MyDynArray2 : MYDYNARRAY)


module Prelude = struct

  module type MYSET = sig
    type elt 
    type t
    val add : elt -> t -> t
    val choose : t -> elt
    val diff : t -> t -> t
    val elements : t -> elt list
    val empty : t
    val filter : (elt -> bool) -> t -> t
    val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a
    val from_list : elt list -> t
    val is_empty : t -> bool
    val list_union : elt list -> t -> t
    val map : (elt -> elt) -> t -> t
    val maximal_less_than : elt -> t -> elt option
    val mem : elt -> t -> bool
    val remove : elt -> t -> t
    val split : elt -> t -> t * bool * t
    val union : t -> t -> t
  end
  
  module MySet_Make = functor (Ord:Set.OrderedType) -> (struct
    include Set.Make(Ord)
    let maximal_less_than e s = (
      let (smaller,_,larger) = split e s in
      if (is_empty smaller) then None else (Some(max_elt smaller)))
    let rec itlist f l b =
      match l with
        [] -> b
      | (h::t) -> f h (itlist f t b)
    let list_union xs s =
      itlist (fun x -> fun s -> (*Set_earley_item.*)add x s) xs s
    let map f s =
      let f1 x s = (*Set_earley_item.*)add (f x) s in
      (*Set_earley_item.*)fold f1 s (*Set_earley_item.*)empty
    let from_list elts = 
      let f1 elt s = add elt s in
      itlist f1 elts empty
  end : MYSET with type elt = Ord.t)  

  module type MYMAP = sig
    type key
    type value
    type ty_map
    val empty : ty_map
    val add : key -> value -> ty_map -> ty_map
    val remove:key -> ty_map -> ty_map
    val find2 : key -> ty_map -> value
    val bindings : ty_map -> (key * value) list
  end

  (* argument to Map functor *)
  (* FIXME what if we insert a default value? we may want to remove the k,v in the map; but this requires that we can check that a value is a default *)
  module type MAPINPUT = sig
      type key
      type value
      val compare : key -> key -> int
      val default: value
      val is_default: value -> bool
  end
  
  module MyMap = functor (MapInput:MAPINPUT) -> (struct
    module Ord = struct
        type t = MapInput.key
        let compare = MapInput.compare
    end
    include Map.Make(Ord)
    type value=MapInput.value
    type ty_map=MapInput.value t
    let add k v m = (
      if MapInput.is_default v then remove k m else add k v m)
    let find2 k m =
      if (mem k m) then (find k m) else MapInput.default
  end : (MYMAP with type key = MapInput.key and type value = MapInput.value))

  (* basic library functions *)
  
  type ('a,'b) sum = Inl of 'a | Inr of 'b
  
  let is_Inl x = (match x with | Inl x -> true | _ -> false)
  let is_Inr x = (match x with | Inr x -> true | _ -> false)

  let dest_Inl x = (match x with | Inl x -> x | _ -> failwith "dest_Inl")
  let dest_Inr x = (match x with | Inr x -> x | _ -> failwith "dest_Inr")
  
  (* FIXME change names of predefined combinators to reflect use of not_epsilon (i.e. default is epsilon) *)
  
  let rec itlist f l b =
    match l with
      [] -> b
    | (h::t) -> f h (itlist f t b);;
  
  let rec mem x lis =
    match lis with
      [] -> false
    | (h::t) -> Pervasives.compare x h = 0 or mem x t;;
  
  let insert x l =
    if mem x l then l else x::l;;
  
  let union l1 l2 = itlist insert l1 l2;;
  
  let unions l = itlist union l [];;
  
  
  let ($) f g x = f(g x)
  
  (*
  let read_file_as_string fn = 
    let f = open_in fn in
    let s = ref "" in
    let _ = try (while(true) do s := (!s) ^ (input_line f) ^ "\n" done) with _ -> () in
    let _ = close_in f in
    !s
  *)
  
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
  
  let read_file_as_string fn = 
    let ls = lines fn in
    ((String.concat "\n" ls)^"\n")
  
  (* get a list with no duplicates; inefficient? FIXME do we mean List.memq? *)
  let unique_f res e = if List.mem e res then res else e::res
  
  (* this is insertion sort; alternatives? *)
  let unique = fun e -> List.fold_left unique_f [] e
  
  let is_Some x = x <> None
  
  let dest_Some x = match x with Some y -> y | _ -> failwith "dest_Some"

  let rec allpairs f l1 l2 =
    match l1 with
     h1::t1 ->  itlist (fun x a -> f h1 x :: a) l2 (allpairs f t1 l2)
     | [] -> []

  let rec last l =
    match l with
      [x] -> x
    | (h::t) -> last t
    | [] -> failwith "last";;
  
  let rec butlast l =
    match l with
      [_] -> []
    | (h::t) -> h::(butlast t)
    | [] -> failwith "butlast";;


  let implode l = itlist (^) l "";;
  
  let explode s =
    let rec exap n l =
        if n < 0 then l else
        exap (n - 1) ((String.sub s n 1)::l) in
    exap (String.length s - 1) [];;

  (* from http://rosettacode.org/wiki/Read_entire_file#OCaml ; when does memory mapping occur? before Unix.close? or does it continually refer to the file on disk? *)

  type myfusebuffer = (char, Bigarray.int8_unsigned_elt, Bigarray.c_layout) Bigarray.Array1.t

  (* tr notes: if filename is empty, the mapping fails; so in this case, we do something special *)
  let read_file_as_array filename = (
    let fd = Unix.openfile filename [Unix.O_RDONLY] 0o640 in
    let len = Unix.lseek fd 0 Unix.SEEK_END in
    let _ = Unix.lseek fd 0 Unix.SEEK_SET in
    let shared = false in  (* modifications are done in memory only *)
    let bstr = (if len=0 then (
      Bigarray.Array1.create Bigarray.char Bigarray.c_layout 0
    ) else (
      Bigarray.Array1.map_file fd
        Bigarray.char Bigarray.c_layout shared len))
    in
    Unix.close fd;
    (bstr))
  let (_:string -> myfusebuffer) = read_file_as_array

  (* FIXME probably doesn't work if arr length 0 *)
  let write_array_as_file arr filename = (
    let fd = Unix.openfile filename [Unix.O_RDWR;Unix.O_CREAT;Unix.O_TRUNC] 0o640 in
    let len = Bigarray.Array1.dim arr in
    let _ = Unix.lseek fd 0 Unix.SEEK_SET in
    let shared = true in  (* modifications are done in memory only *)
    let bstr = (Bigarray.Array1.map_file fd
                  Bigarray.char Bigarray.c_layout shared len)
    in
    let _ = Bigarray.Array1.blit arr bstr in 
    let _ = Unix.close fd in
    ())
  let (_:myfusebuffer -> string -> unit) = write_array_as_file

  module My_stream = struct 

    open Bigarray

    (* FIXME scons is at front; snoc is at back; change scons to snoc *)
    (* ('a,'b) stream_ops is the type of streams implemented using type 'a, with vals in 'b *)
    type ('a,'b) stream_ops = { dest_strm:'a -> (unit,'b*'a)sum; snc: ('b*'a) -> 'a }
    (* the following is just for packaging streams into a single value; don't expect ops to change! *)
    type ('a,'b) stream = { impl: 'a; ops: ('a,'b) stream_ops }

    let is_snil s = (match s.ops.dest_strm s.impl with 
      | Inl () -> true
      | _ -> false)

    let dest_stream s = (
      let Inr(v,impl) = s.ops.dest_strm s.impl in
      (v,{s with impl=impl}))

    let snoc (c,s) = (
      let impl = s.ops.snc (c,s.impl) in
      {s with impl=impl})
  
    (* lists as streams *)
    type 'a list_stream = ('a list,'a) stream
    let list_stream_ops = {
      dest_strm=(fun x -> match x with
        | [] -> (Inl ())
        | x::xs -> Inr(x,xs));
      snc=(fun (x,xs) -> xs@[x])
    }
  
    let rec stream_takeall s = (match is_snil s with 
      | true -> []
      | false -> (
        let (c,s) = dest_stream s in
        c::(stream_takeall s)))
    let (_:('a,'b)stream -> 'b list) = stream_takeall


    (* representing streams of characters using a string; impl is a string and an index *)
    let chars_of_string_ops = {
      dest_strm=(fun (s,i) -> (
        if i=String.length s then Inl()
        else Inr(String.get s i,(s,i+1))
      ));
      snc=(fun (c,(s,i)) -> (s^(String.make 1 c),i))
    }
    let chars_of_string s = {impl=(s,0); ops=chars_of_string_ops}
    let (_:string -> (string*int,char) stream) = chars_of_string
  
    (* more efficient - a char stream is a string between a low and high index *)
    let chars_of_string_ops = {
      dest_strm=(fun (s,l,h) -> (
        if l=h then Inl()
        else Inr(String.get s l,(s,(l+1),h))
      ));
      snc=(fun (c,(s,l,h)) -> (
        let s = (if (h=String.length s) then (
          (* need to reallocate *)
          let _ = if 0=String.length s then failwith "chars_of_string_ops: s length 0" else () in
          let s' = String.make ((2*(String.length s))) '\x00' in
          let _ = String.blit s 0 s' 0 (String.length s) in
          s')
          else s)
        in
        let _ = String.set s h c in
        (s,l,h+1)))
    }
    let chars_of_string s = (
      (* backing strings must be non-empty if we are multiplying length by 2 when resizing *)
      if s = "" then {impl=("..",0,0); ops=chars_of_string_ops}
      else {impl=(s,0,String.length s); ops=chars_of_string_ops})
    let (_:string -> (string*int*int,char) stream) = chars_of_string
  
    (* to avoid using stream_takeall, we allow to get the stream contents directly from the impl *)
    let chars_of_string_takeall s = (
      let (s,l,h) = s.impl in
      String.sub s l (h-l))
    let (_:(string*int*int,char) stream -> string) = chars_of_string_takeall
  

    (* FIXME these stream types should be in the stream module *)
    (* also want to deal with arrays particularly myfusebuffer; at the moment only need to read; use dynarray? *)
    let chars_of_array_ops = {
      dest_strm=(fun (s,l,h) -> 
        if l=h then Inl()
        else Inr(Array1.get s l,(s,(l+1),h)));
      snc=(fun _ -> failwith "chars_of_array_ops")
    }
    let chars_of_array s = (
      (* backing strings must be non-empty if we are multiplying length by 2 when resizing *)
      (* we never scons, so we don't need to worry about 0 length array *)
      {impl=(s,0,Array1.dim s); ops=chars_of_array_ops})
    let (_:myfusebuffer -> (myfusebuffer*int*int,char) stream) = chars_of_array

    let chars_of_dynarray_ops = {
      dest_strm=(fun (s,l,h) -> 
        if l=h then Inl()
        else Inr(MyDynArray.get s l,(s,(l+1),h)));
      snc=(fun (c,(s,l,h)) -> 
        let s = MyDynArray.set s h c in
        (s,l,h+1))
    }
    let chars_of_dynarray s = (
      {impl=(s,0,MyDynArray.dim s); ops=chars_of_dynarray_ops})
    let (_:MyDynArray.t -> (MyDynArray.t*int*int,char) stream) = chars_of_dynarray
  
  end

  include My_stream
  
end




(* based partially on http://ocaml-batteries-team.github.io/batteries-included/hdoc/BatBase64.html *)
(* following for encoding binary data into human readable string *)
(* FIXME should probably perform some basic checks on the input - at the momemnt we fail if input is not wellformed *)
(* FIXME maybe pad, so output is a multiple of 4 bytes - this is what eg the base64 command line tool does; this requires an extra character to indicate "no data"; this is the "padding" referred to in the wikipedia article on base64 *)
module Encode = struct

  open Prelude

  let rec string_of_chars cs = (match cs with | [] -> "" | c::cs -> (String.make 1 c)^(string_of_chars cs))

  (* from batteries *)
  type encoding_table = char array (* length 64, take a number from 0-63 and give a char *)
  type decoding_table = int array

  type safe_char = (* subtype of *) char (* should be one of the chars below *)

  type bits_6 = int (* only bottom 6 bits may be non zero *)
  type bits_8 = int
  
  let chars = [|
          'A';'B';'C';'D';'E';'F';'G';'H';'I';'J';'K';'L';'M';'N';'O';'P';
          'Q';'R';'S';'T';'U';'V';'W';'X';'Y';'Z';'a';'b';'c';'d';'e';'f';
          'g';'h';'i';'j';'k';'l';'m';'n';'o';'p';'q';'r';'s';'t';'u';'v';
          'w';'x';'y';'z';'0';'1';'2';'3';'4';'5';'6';'7';'8';'9';'+';'/'
  |]
  
  let make_decoding_table tbl =
          if Array.length tbl <> 64 then failwith "make_decoding_table";
          let d = Array.make 256 (-1) in
          for i = 0 to 63 do
                  Array.unsafe_set d (int_of_char (Array.unsafe_get tbl i)) i;
          done;
          d
  
  let inv_chars = make_decoding_table chars
  
  (* data contains at least 32 bits? what are the assumptions on data? *)
  (* count is number of bits in data that are valid; valid bits are count-1,count-2,...,0 *)
  let rec encode (sofar,data,count,input) = (
    (* try and output a char if possible *)
    if (count >= 6) then (
      (* at least 6 bits in data - output an encoded char *)
      let d = (data asr (count - 6)) land 63 in
      let c = (Array.unsafe_get chars d) in
      encode ((snoc (c,sofar)),data,count-6,input)
    ) else (
      match is_snil input with
      | true -> (
        (* tricky case - less that 6 bits available *)
        if (count > 0) then 
          let d = (data lsl (6-count)) land 63 in
          let c = (Array.unsafe_get chars d) in
          snoc (c,sofar)
        else
          sofar)
      | false -> (
        let (c,input) = dest_stream input in
        let data = (data lsl 8) lor (Char.code c) in
        let count = count + 8 in
        encode (sofar,data,count,input))))

  let encode_string s = (
    let cs = encode ((chars_of_string ""),0,0,chars_of_string s) in
    chars_of_string_takeall cs)
  let (_:string->string) = encode_string
  
  (* the data is decoded bits *)
  let rec decode (sofar,data,count,input) = (
    if (count >= 8) then (
      (* at least 8 bits in data *)
      let d = (data asr (count - 8)) land 0xFF in
      let c = Char.chr d in
      decode (snoc (c,sofar),data,count-8,input)
    ) else (
      match is_snil input with 
      | true -> (
        (* assume the data is 0 padding bytes, so discard *)
        sofar)
      | false -> (
        let (c,input) = dest_stream input in
        let d = Array.unsafe_get inv_chars (Char.code c) in
        let data = (data lsl 6) lor d in
        decode (sofar,data,count+6,input))))
 
  let decode_string s = (
    let cs = decode ((chars_of_string ""),0,0,chars_of_string s) in
    chars_of_string_takeall cs)
  let (_:string->string) = decode_string

  let encode_array s = (
    let cs = encode ((chars_of_string ""),0,0,chars_of_array s) in
    let cs = stream_takeall cs in
    string_of_chars cs)
  let (_:myfusebuffer->string) = encode_array
  
    
  (* test 
  let _ = encode_string "Man is distinguished"
  let _ = encode_string "Man is distinguis"
  let _ = decode_string "TWFuIGlzIGRpc3Rpbmd1aXN"
  *)

  (* further fiddling *)
  (*
  let bits_6_of_8 = (
    let is_snil=(fun (s,data,count) -> (count=0) && (s.ops.is_snil s.impl)) in
    let rec dest_scons=(fun (s,data,count) -> (
      if count >= 6 then (
        (* at least 6 bits in data - output an encoded char *)
        let d = (data asr (count - 6)) land 63 in
        (d,(s,data,count-6))
      ) else (
        match s.ops.is_snil s.impl with
        | true -> (
          (* tricky case - less that 6 bits available *)
          (* this is only called if not is_snil, which implies that count > 0 *)       
          let d = (data lsl (6-count)) land 63 in
          (d,(s,data,0)))
        | false -> (
          let (c,s_impl) = s.ops.dest_scons s.impl in
          let s = {s with impl=s_impl} in
          let data = (data lsl 8) lor (Char.code c) in
          let count = count + 8 in
          dest_scons (s,data,count)))))
    in
    let scons=(fun _ -> failwith "bits_6_of_8") in
    let ops = { is_snil; dest_scons; scons } in
    fun s -> { impl=(s,0,0); ops=ops })
  let (_:('a,char)stream -> (('a,char)stream*int*int,bits_6)stream) = bits_6_of_8

  let encode_6 = (
    let is_snil=(fun s -> s.ops.is_snil s.impl) in
    let dest_scons=(fun s -> 
      let (i,s_impl) = s.ops.dest_scons s.impl in
      let s = {s with impl=s_impl} in
      let c = (Array.unsafe_get chars i) in
      (c,s)) 
    in
    let scons=(fun _ -> failwith "encode_6") in
    let ops = { is_snil; dest_scons; scons } in
    fun s -> {impl = s; ops=ops})
  let (_:('a,bits_6)stream -> (('a,bits_6)stream,safe_char) stream) = encode_6
  (* FIXME might be nice to have record notation for types, rather than pairs *)
  *)

  (* test 
  let s = chars_of_string "Man"
  let s2 = bits_6_of_8 s
  let s3 = encode_6 s2 
  let _ = stream_takeall s3  
  *)

end



 end
;;

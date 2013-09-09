(* this is intended to be loaded into HOL after fs_specScript.sml *)

    (*
    # `dir_tree.ml`
    ## `Dir_tree_types` and basic operations
    
    Types for a representation using an inode heap and a dir tree
    
    *)
    
    (* open Fs_prelude *)
    (* open Fs_spec *)
    
    (* module Dir_tree_types = struct *)
    
    (*   open Fmap *)
    
    
    (*   open Prelude *)
    (*   open Fs_types1 (\* FIXME remove dependence? have a core types and a state types? *\) *)
    
      (* dirs are represented by their path; obviously this isn't a real
         reference, so won't work if dirs are renamed *)
val dir_ref_def = type_abbrev("dir_ref",``:string list``);
val dest_dir_ref_def = Define `
dest_dir_ref s0 _ = 999
`;
    
    
val inode_ref_def = Hol_datatype `
inode_ref = Inode_ref of num
`;
val dest_inode_ref_def = Define `
dest_inode_ref s0 (Inode_ref i) = i
`;
    
    
(*      type name = Fs_spec.Fs_types1.name *)
val contents_def = type_abbrev("contents",``:string``);
(* FIXME using list rather than hols fmap *)
val contents_heap_def = type_abbrev("contents_heap",``:(inode_ref#contents) list``);
      (* root dir has name ""; root must be a dir *)

(* FIXME couldn't get fmap constructor to work in nested context below *)
(* FIXME entry type clashes with previous entry defn *)
val entry_def = Hol_datatype `
entrya = Dir of (name#entrya) list | File of inode_ref
`;
(* FIXME don't use fs as constant, since used later as var? *)

val fs_def = Hol_datatype `
fs1 = <| es1:entrya; cs1: contents_heap |>
`;


val fmap_dom_def = Define`
fmap_dom fs' = MAP FST fs'
`;

val fmap_empty_def = Define `
fmap_empty = []
`;

(* FIXME MAX *)    
val new_inode_ref_def = Define `
new_inode_ref fs = (
        let xs = fmap_dom fs.cs1 in
        let xs = MAP (dest_inode_ref fs) xs in
        Inode_ref(1+(FOLDL (\ acc . \ i . MAX acc i) 0 xs)))
`;
    
      (* framestack *)
val entries2_def = Hol_datatype `
entries2 = Dir2 of (name#entrya) list # name
`;

(* FIXME need association lists in HOL *)
val fmap_lookup_def = Define `
fmap_lookup m n = SOME(SND (HD m))
`;

val fmap_update_def = Define `
fmap_update m n = m
`;

val fmap_remove_def = Define `
fmap_remove m n = m
`;


(* FIXME let SOME(x) ... *)    
val frame_resolve1_def = Define `
frame_resolve1 (e,frms) n = (
        case e of 
          File _ -> (failwith "frame_resolve1'")
        || Dir m -> (
          case fmap_lookup m n of SOME(e) -> 
          (e,Dir2(m,n)::frms)))
`;
    
val frame_resolve_def = Define `
frame_resolve e ns = (
        FOLDL frame_resolve1 (e,[]) ns)
`;
    
val frame_assemble_def = Define `
frame_assemble (e,frms) = (
        let f1 e f = (case f of
            Dir2(m,n) -> (
            let m' = fmap_update m (n,e) in
            Dir m'))
        in
        FOLDL f1 e frms)
`;
    
val link_file_def = Define `
link_file s0 i0_ref d0_ref name = (
        let (e,frms) = frame_resolve s0.es1 d0_ref in
        case e of
          File _ -> (failwith "link_file: impossible") (* dir_ref resolved to file *)
        || Dir m -> (
          let m' = fmap_update m (name,File i0_ref) in
          return (s0 with <|es1 := (frame_assemble (Dir m',frms))|>) ))
`;
    
val unlink_def = Define `
unlink s0 d0_ref name = (
        let (e,frms) = frame_resolve s0.es1 d0_ref in
        case e of
          File _ -> (failwith "link_file: impossible") (* dir_ref resolved to file *)
        || Dir m -> (
          let m' = fmap_remove m name in
          return (s0 with <|es1 := (frame_assemble (Dir m',frms))|>) ))
`;
    
val link_dir_def = Define `
link_dir s0 d0_ref name d = (
        let (e,frms) = frame_resolve s0.es1 d0_ref in
        case e of
          File _ -> (failwith "link_file: impossible") (* dir_ref resolved to file *)
        || Dir m -> (
          let m' = fmap_update m (name,d) in
          return (s0 with <|es1 := (frame_assemble (Dir m',frms))|>) ))
`;
    
val mkdir_def = Define `
mkdir s0 d0_ref name = (link_dir s0 d0_ref name (Dir[]))
`;
    
val mv_def = Define `
mv s0 d0_ref name0 d1_ref name1 = (
        let (e,frms) = frame_resolve s0.es1 (d0_ref++[name0]) in
        case e of
          File i0_ref -> (
          let s0 = (unlink s0 d0_ref name0).state2 in
          let s0 = (link_file s0 i0_ref d1_ref name1).state2 in
          return s0)
        || _ -> (failwith "mv"))
`;
    
val mvdir_def = Define `
mvdir s0 d0_ref name0 d1_ref name1 = (
        let (e,frms) = frame_resolve s0.es1 (d0_ref++[name0]) in
        case e of
          File i0_ref -> (failwith "mvdir: 1")
        || Dir m -> (
          let s0 = (unlink s0 d0_ref name0).state2 in
          link_dir s0 d1_ref name1 (Dir m)))
`;
    
val read_def = Define `
read s0 i0_ref = (
        case fmap_lookup s0.cs1 i0_ref of SOME(c) -> 
        <|state2 := s0;ret2 := (Bytes1 ((*MyDynArray.of_string*) c)) |>)
`;

(* FIXME names are sorted *)    
val readdir_def = Define `
readdir s0 d0_ref = (
        let (e,frms) = frame_resolve s0.es1 d0_ref in
        case e of
          File _ -> (failwith "readdir")
        || Dir m -> (
          let names = fmap_dom m in
          let names = names in (* List.sort Pervasives.compare names in  *)
          <|state2 := s0; ret2 := (Names1 names)|>))
`;

(* FIXME match interpreted as a fnarg *)    
val resolve1_def = Define `
resolve1 s0 d0_ref name = (
        let (e,frms) = frame_resolve s0.es1 d0_ref in
        case e of
          File i0_ref -> NONE
        || Dir m -> (
          let e = fmap_lookup m name in
          case e of   NONE -> NONE || SOME e -> 
          case e of
            File i0_ref -> (SOME(INR i0_ref))
          || Dir _ -> (SOME(INL (d0_ref++[name])))))
`;
          
    
val rm_def = Define `
rm = unlink
`;
    
val rmdir_def = Define `
rmdir = unlink
`;
    
val touch_def = Define `
touch s0 d0_ref name = (
        let (e,frms) = frame_resolve s0.es1 d0_ref in
        case e of
          File _ -> (failwith "touch")
        || Dir m -> (
          let i0_ref = new_inode_ref s0 in
          let s0 = (s0 with <|cs1 := (fmap_update s0.cs1 (i0_ref,""))|>) in
          link_file s0 i0_ref d0_ref name))
`;
    
val write_def = Define `
write s0 i0_ref c = (return (s0 with <|cs1 := (fmap_update s0.cs1 (i0_ref,(*MyDynArray.to_string*) c))|>))
`;
    
val state0_def = Define `
state0 = <|es1 := Dir[]; cs1 := fmap_empty|>
`;
    
val ops1_def = Define `
ops1 = <|
        get_init_state1 := (\ () . state0);
        get_root1 := (\ s0 . SOME[]); (* []  is the dir ref for the root dir *)
        dest_dir_ref1 := dest_dir_ref;
        dest_inode_ref1 := dest_inode_ref;
        get_symlink1 := (\ s0 . \ i0_ref . F);
        link_file1 := (link_file);
        unlink1 := (unlink);
        mkdir1 := (mkdir);
        mv1 := (mv);
        mvdir1 := (mvdir);
        read1 := (read);
        readdir1 := (readdir);
        resolve11 := (resolve1);
        rm1 := (rm);
        rmdir1 := (rmdir);
        touch1 := (touch);
        write1 := (write);
        set_symlink1 := (\ _1 . \ _2 . \ f . failwith "set_symlink")
      |>
`;
    
(*    end *)




(* a version of unix_impl that implements read operations; all update operations are no-ops *)

let unix_ops1 = Unix_impl.Unix_impl_everything.ops1

open Fs_spec.Fs_types1

let ops1 = {
    get_init_state1=(unix_ops1.get_init_state1);
    get_arch1=(fun _ -> default_arch);
    get_parent1=(unix_ops1.get_parent1);
    get_root1=(unix_ops1.get_root1);
    dest_dir_ref1=unix_ops1.dest_dir_ref1;
    dest_inode_ref1=unix_ops1.dest_inode_ref1;
    get_symlink1=(fun s0 -> fun i0_ref -> false);
    link_file1=(fun s0 i0_ref d0_ref name -> {state2=s0; ret2=None1});
    unlink1=(fun s0 d0_ref name -> {state2=s0; ret2=None1});
    mkdir1=(fun s0 d0_ref name -> {state2=s0; ret2=None1});
    mv1=(fun s0 d0_ref name0 d1_ref name1 -> {state2=s0; ret2=None1});
    mvdir1=(fun s0 d0_ref name0 d1_ref name1 -> {state2=s0; ret2=None1});
    read1=(unix_ops1.read1);
    readdir1=(unix_ops1.readdir1);
    resolve11=(unix_ops1.resolve11);
    rm1=(fun s0 d0_ref name -> {state2=s0; ret2=None1});
    rmdir1=(fun s0 d0_ref name -> {state2=s0; ret2=None1});
    touch1=(fun s0 d0_ref name -> {state2=s0; ret2=None1});
    write1=(fun s0 i0_ref c -> {state2=s0; ret2=None1});
    set_symlink1=(fun _ -> fun _ -> fun f -> failwith "set_symlink");
  }

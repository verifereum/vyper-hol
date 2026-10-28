(* TOP-LEVEL: the runtime invariant combines the fixed enclosing traversal,
   complete array data, actual header readiness and both owned cursors.
   Its compiler prefix is selected again on every runtime iteration. *)
Theory abiNativeDynamicArrayInvariant
Ancestors
  abiNativeDynamicArrayState abiNativeTraversal abiNativeCursor abiDynamicLoopRun abiDynamicLoopCode abiFieldLayoutDefs
  compileEnv venomState venomInst list words

Definition abi_native_dynamic_array_invariant_def:
  abi_native_dynamic_array_invariant ctx func cs after dst src len_op dst_addr root_addr counter_addr dyn_addr
      info width stride fields source_capacity initial dyn_inst index_inst index ss <=>
    abi_native_traversal ctx func cs after (dst_addr + 32w) (abi_field_bytes (abi_field_head_size fields) fields) initial cs ss /\
    abi_dynamic_loop_ready cs dst src len_op dst_addr root_addr counter_addr dyn_addr (LENGTH fields) index ss /\
    abi_native_dynamic_array_data info width stride fields dst_addr root_addr counter_addr dyn_addr source_capacity index ss /\
    abi_native_cursor func cs after dyn_inst dyn_addr (abi_dynamic_loop_prefix_cut dst src width stride len_op cs) ss /\
    abi_native_cursor func cs after index_inst counter_addr (abi_dynamic_loop_prefix_cut dst src width stride len_op cs) ss
End

Theorem abi_native_dynamic_array_invariant_ready:
  !ctx func cs after dst src len_op dst_addr root_addr counter_addr dyn_addr info width stride fields
      source_capacity initial dyn_inst index_inst index ss.
    abi_native_dynamic_array_invariant ctx func cs after dst src len_op dst_addr root_addr counter_addr dyn_addr
      info width stride fields source_capacity initial dyn_inst index_inst index ss ==>
    abi_dynamic_loop_ready cs dst src len_op dst_addr root_addr counter_addr dyn_addr (LENGTH fields) index ss
Proof
  simp[abi_native_dynamic_array_invariant_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual dynamic array runtime invariant: " ^ name)
  end) (DB.thms "abiNativeDynamicArrayInvariant")

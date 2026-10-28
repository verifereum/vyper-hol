(* TOP-LEVEL: the actual static-array header state includes both owned
   counters, raw data and the operand/control facts consumed by the loop.
   The compiler and runtime prefix definitions are the real emitted cuts. *)
Theory abiNativeStaticArrayHeader
Ancestors
  abiNativeArrayEntryOperands abiNativeStaticHeaderCode abiNativeStaticArrayState abiNativeCursor abiNativeTraversal
  abiDynArrayCode abiDynArrayBoundaryFrames abiStaticLoopEntry abiStaticLoopCode abiFieldOperands
  compileIdFlow compileEnv venomMemDefs venomState list words arithmetic

Definition abi_native_static_array_start_def:
  abi_native_static_array_start cs dst src dst_addr root_addr ss =
    let macro = abi_dynarray_entry_cut dst src cs in
    abi_static_loop_start_state macro.cs_next_id macro.cs_next_var macro.cs_next_label
      (abi_dynarray_entry_boundary cs dst_addr root_addr ss)
End

Definition abi_native_static_array_header_def:
  abi_native_static_array_header ctx func cs after dst src root_addr source_capacity dst_addr info stride fields initial ss <=>
    let macro = abi_dynarray_entry_cut dst src cs in
    let parent = abi_static_loop_counter_addr cs.cs_next_id initial in
    let index = abi_static_loop_counter_addr macro.cs_next_id (abi_dynarray_entry_boundary cs dst_addr root_addr initial) in
    abi_native_traversal ctx func cs after dst_addr
      (word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields)
      initial (abi_native_static_header_cut macro) ss /\
    abi_native_cursor func cs after (abi_native_array_counter_inst macro) index (abi_native_static_header_cut macro) ss /\
    abi_native_cursor func cs after (abi_native_array_counter_inst cs) parent (abi_native_static_header_cut macro) ss /\
    (abi_native_array_counter_inst cs).inst_id <> (abi_native_array_counter_inst macro).inst_id /\
    abi_native_static_array_data info (abi_static_encoder_size info) stride fields dst_addr root_addr index source_capacity 0 ss /\
    compiler_id_history macro /\
    ss.vs_current_bb = fresh_label_output "enc_dyn_hdr" macro.cs_next_label /\ ss.vs_inst_idx = 0 /\ ~ss.vs_halted /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME root_addr /\
    eval_operand (Var (compiler_var_name macro.cs_next_var 0)) ss = SOME index /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 1)) ss = SOME (n2w (LENGTH fields)) /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 0)) ss = SOME parent /\ mload (w2n parent) ss = 0w /\
    EVERY (abi_operand_before (macro.cs_next_var + 1))
      [dst; src; Var (compiler_var_name cs.cs_next_var 0); Var (compiler_var_name cs.cs_next_var 1)]
End

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed exact static array header assertions: " ^ name)
  end) (DB.thms "abiNativeStaticArrayHeader")

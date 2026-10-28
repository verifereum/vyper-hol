(* TOP-LEVEL: complete actual static-array execution includes both real
   setup prefixes, the runtime-count loop and the parent epilogue. *)
Theory abiNativeStaticArrayComplete
Ancestors
  abiNativeStaticArrayPrefixFields abiNativeStaticArrayHeader abiNativeStaticArrayFinish abiNativeArrayEntryOperands
  abiNativeEncodingDefs abiNativeCursor abiNativeTraversal abiNativeStaticHeaderCode abiDynArrayCode abiDynArrayBoundaryFrames
  abiStaticLoopEntry abiStaticLoopCode abiFieldOperands compileEnv fragExec venomMemDefs venomState list words arithmetic

Theorem abi_native_static_array_header_finish:
  !ctx func cs source_id target_id root_addr source_capacity dst_addr info stride fields initial ss dst src ret after.
    abi_native_memory_ready func cs (abi_dynarray_exit_cut (Var (compiler_var_name cs.cs_next_var 0)) ret after)
      source_id target_id root_addr source_capacity dst_addr
      (word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields) initial /\
    abi_native_static_array_header ctx func cs (abi_dynarray_exit_cut (Var (compiler_var_name cs.cs_next_var 0)) ret after)
      dst src root_addr source_capacity dst_addr info stride fields initial ss /\ LENGTH fields < dimword (:256) /\
    compile_abi_encode_dyn_static_loop dst src info (abi_static_encoder_size info) stride
      (Var (compiler_var_name cs.cs_next_var 1)) (abi_dynarray_entry_cut dst src cs) = (ret,after) /\
    fn_has_code (abi_dynarray_entry_cut dst src cs) after func /\
    fn_has_code after (abi_dynarray_exit_cut (Var (compiler_var_name cs.cs_next_var 0)) ret after) func ==>
    ?out. abi_native_encoding_result ctx func cs (abi_dynarray_exit_cut (Var (compiler_var_name cs.cs_next_var 0)) ret after)
      (Var (compiler_var_name after.cs_next_var 2)) dst_addr
      (word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields) initial out
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `abi_native_static_array_header _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE bool_ss [abi_native_static_array_header_def, LET_THM, EVERY_DEF]) >>
  qspecl_then [`ctx`, `func`, `cs`, `source_id`, `target_id`, `abi_native_array_counter_inst (abi_dynarray_entry_cut dst src cs)`,
    `abi_static_loop_counter_addr (abi_dynarray_entry_cut dst src cs).cs_next_id (abi_dynarray_entry_boundary cs dst_addr root_addr initial)`,
    `abi_native_array_counter_inst cs`, `abi_static_loop_counter_addr cs.cs_next_id initial`,
    `Var (compiler_var_name cs.cs_next_var 0)`, `root_addr`, `source_capacity`, `dst_addr`, `info`, `stride`, `fields`, `initial`, `ss`,
    `dst`, `src`, `Var (compiler_var_name cs.cs_next_var 1)`, `abi_dynarray_entry_cut dst src cs`, `ret`, `after`]
    mp_tac abi_native_static_array_finish >> impl_tac >- asm_simp_tac bool_ss [] >> simp_tac bool_ss []
QED

Theorem compile_abi_native_static_array:
  !ctx func dst src info stride fields source_capacity cs ret after initial dst_addr root_addr source_id target_id.
    compile_abi_encode_to_buf dst src (AbiDynArray info (abi_static_encoder_size info) stride F) cs = (ret,after) /\
    fn_has_code cs after func /\
    abi_native_memory_ready func cs after source_id target_id root_addr source_capacity dst_addr
      (word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields) initial /\
    32 <= source_capacity /\ LENGTH fields < dimword (:256) /\
    abi_memory_fields (REPLICATE (LENGTH fields) (info,abi_static_encoder_size info,stride,F))
      (w2n root_addr + 32) (source_capacity - 32) initial.vs_memory fields /\
    mload (w2n root_addr) initial = n2w (LENGTH fields) /\
    abi_operand_before cs.cs_next_var dst /\ abi_operand_before cs.cs_next_var src /\
    eval_operand dst initial = SOME dst_addr /\ eval_operand src initial = SOME root_addr /\
    initial.vs_current_bb = cs.cs_current_bb /\ initial.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~initial.vs_halted ==>
    ?out. abi_native_encoding_result ctx func cs after ret dst_addr
      (word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields) initial out
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `compile_abi_encode_dyn_static_loop dst src info (abi_static_encoder_size info) stride
    (Var (compiler_var_name cs.cs_next_var 1)) (abi_dynarray_entry_cut dst src cs)` >>
  rename1 `compile_abi_encode_dyn_static_loop _ _ _ _ _ _ _ = (encoded_size,loop_after)` >>
  qpat_x_assum `compile_abi_encode_to_buf _ _ _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss()) [compile_abi_dynarray_factor, LET_THM] >> strip_tac >> gvs[] >>
  qspecl_then [`F`, `dst`, `src`, `info`, `abi_static_encoder_size info`, `stride`, `cs`, `encoded_size`, `loop_after`, `func`]
    mp_tac compile_abi_dynarray_contains_parts >> impl_tac >- asm_simp_tac (srw_ss()) [] >> strip_tac >>
  `cs_extends loop_after (abi_dynarray_exit_cut (Var (compiler_var_name cs.cs_next_var 0)) encoded_size loop_after)` by
    simp[abi_dynarray_cuts_extend] >>
  drule_all abi_native_static_array_prefix_fields >> disch_then (qspec_then `ctx` ASSUME_TAC) >>
  drule_all abi_native_static_array_header_finish >> simp_tac bool_ss []
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed complete actual static array encoding: " ^ name)
  end) (DB.thms "abiNativeStaticArrayComplete")

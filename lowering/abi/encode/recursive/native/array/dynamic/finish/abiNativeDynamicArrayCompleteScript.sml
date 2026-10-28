(* TOP-LEVEL: complete dynamic-child array execution includes the actual
   parent prefix, two-cell loop setup, arbitrary semantic recursive
   children and parent epilogue. Source reference memory stays independent. *)
Theory abiNativeDynamicArrayComplete
Ancestors
  abiNativeDynamicArrayFinish abiNativeDynamicArrayParentPrefix abiNativeDynamicArrayFlow abiNativeArrayParentCode
  abiNativeArrayEntryOperands abiNativeEncodingDefs abiNativeFields abiDynArrayCode abiDynamicLoopCode
  abiDynArrayBoundaryFrames abiStaticLoopEntry abiStaticLoopCode abiFieldOperands abiFieldLayoutDefs
  compileAllocaProvenance compileEnv fragExec venomMemDefs venomState list words arithmetic

Theorem compile_abi_native_dynamic_array:
  !ctx func dst src info width stride fields source_capacity cs ret after initial dst_addr root_addr source_id target_id reference.
    compile_abi_encode_to_buf dst src (AbiDynArray info width stride T) cs = (ret,after) /\ fn_has_code cs after func /\
    abi_native_memory_ready func cs after source_id target_id root_addr source_capacity dst_addr
      (word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields) initial /\
    32 <= source_capacity /\ LENGTH fields < dimword (:256) /\
    abi_memory_fields (REPLICATE (LENGTH fields) (info,width,stride,T)) (w2n root_addr + 32) (source_capacity - 32) initial.vs_memory fields /\
    mload (w2n root_addr) initial = n2w (LENGTH fields) /\
    abi_native_fields (REPLICATE (LENGTH fields) (info,width,stride,T)) (w2n root_addr + 32) reference fields /\
    mem_bytes_at (w2n root_addr) source_capacity reference = mem_bytes_at (w2n root_addr) source_capacity initial.vs_memory /\
    abi_operand_before cs.cs_next_var dst /\ abi_operand_before cs.cs_next_var src /\
    eval_operand dst initial = SOME dst_addr /\ eval_operand src initial = SOME root_addr /\
    initial.vs_current_bb = cs.cs_current_bb /\ initial.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~initial.vs_halted ==>
    ?out. abi_native_encoding_result ctx func cs after ret dst_addr
      (word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields) initial out
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `compile_abi_encode_dyn_loop dst src info width stride (Var (compiler_var_name cs.cs_next_var 1))
    (abi_dynarray_entry_cut dst src cs)` >>
  rename1 `compile_abi_encode_dyn_loop _ _ _ _ _ _ _ = (encoded_size,loop_after)` >>
  Cases_on `compile_abi_encode_to_buf (Var (compiler_var_name (abi_dynarray_entry_cut dst src cs).cs_next_var 14))
    (Var (compiler_var_name (abi_dynarray_entry_cut dst src cs).cs_next_var 9)) info
    (abi_dynamic_loop_prefix_cut dst src width stride (Var (compiler_var_name cs.cs_next_var 1)) (abi_dynarray_entry_cut dst src cs))` >>
  rename1 `compile_abi_encode_to_buf _ _ info _ = (child_len,mid)` >>
  qpat_x_assum `compile_abi_encode_to_buf _ _ (AbiDynArray _ _ _ _) _ = _` mp_tac >>
  asm_simp_tac (srw_ss()) [compile_abi_dynarray_factor, LET_THM] >> strip_tac >> gvs[] >>
  qspecl_then [`T`, `dst`, `src`, `info`, `width`, `stride`, `cs`, `encoded_size`, `loop_after`, `func`]
    mp_tac compile_abi_dynarray_contains_parts >> impl_tac >- asm_simp_tac (srw_ss()) [] >> strip_tac >>
  `compiler_id_history cs` by fs[abi_native_memory_ready_def] >>
  qspecl_then [`dst`, `src`, `cs`] mp_tac abi_native_array_parent_history >> impl_tac >- first_assum MATCH_ACCEPT_TAC >> DISCH_TAC >>
  drule_all abi_native_dynamic_array_flow >> strip_tac >>
  `cs_extends loop_after (abi_dynarray_exit_cut (Var (compiler_var_name cs.cs_next_var 0)) encoded_size loop_after)` by
    simp[abi_dynarray_cuts_extend] >>
  `cs_extends (abi_dynarray_entry_cut dst src cs) (abi_dynarray_exit_cut (Var (compiler_var_name cs.cs_next_var 0)) encoded_size loop_after)` by
    (irule cs_extends_trans >> qexists_tac `loop_after` >> asm_simp_tac bool_ss []) >>
  qspecl_then [`ctx`, `func`, `cs`, `abi_dynarray_exit_cut (Var (compiler_var_name cs.cs_next_var 0)) encoded_size loop_after`,
    `source_id`, `target_id`, `root_addr`, `source_capacity`, `dst_addr`, `fields`, `info`, `width`, `stride`, `initial`, `dst`, `src`, `loop_after`]
    mp_tac abi_native_dynamic_array_parent_prefix >> impl_tac >- asm_simp_tac bool_ss [] >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  qpat_assum `EVERY (abi_operand_before _) _` (strip_assume_tac o PURE_REWRITE_RULE [EVERY_DEF]) >>
  `mem_bytes_at (w2n root_addr) source_capacity reference = mem_bytes_at (w2n root_addr) source_capacity
    (abi_dynarray_entry_boundary cs dst_addr root_addr initial).vs_memory` by asm_simp_tac bool_ss [] >>
  qspecl_then [`ctx`, `func`, `cs`, `source_id`, `target_id`, `root_addr`, `source_capacity`, `dst_addr`, `fields`, `initial`,
    `abi_native_array_counter_inst cs`, `abi_static_loop_counter_addr cs.cs_next_id initial`, `Var (compiler_var_name cs.cs_next_var 0)`,
    `dst`, `src`, `info`, `width`, `stride`, `Var (compiler_var_name cs.cs_next_var 1)`, `abi_dynarray_entry_cut dst src cs`,
    `encoded_size`, `loop_after`, `child_len`, `mid`, `abi_dynarray_entry_boundary cs dst_addr root_addr initial`, `reference`]
    mp_tac abi_native_dynamic_array_finish >> impl_tac >- asm_simp_tac bool_ss [] >> simp_tac bool_ss []
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed complete actual native dynamic-child array encoding: " ^ name)
  end) (DB.thms "abiNativeDynamicArrayComplete")

(* TOP-LEVEL: derive the real loop child contract from semantic recursive
   induction assertions. Each actual child run and post-child continuation
   reconstructs the full invariant for the next runtime index. *)
Theory abiNativeDynamicArrayContract
Ancestors
  abiNativeDynamicArrayInvariant abiNativeDynamicArrayChildComplete abiNativeDynamicArrayNext abiNativeDynamicArrayParts
  abiNativeDynamicArrayState abiNativeFields abiNativeTraversal abiNativeEncodingDefs abiNativeCursor abiMemoryLeafRun
  abiDynamicLoopRun abiDynamicLoopIteration abiDynamicLoopCode abiDynamicLoopStep abiNativeDynamicArrayUpdateState
  abiFieldOperands abiFieldLayoutDefs abiAllocatedWindows compileAllocaProvenance compileEnv fragExec venomMemDefs venomState venomInst list words

Theorem abi_native_dynamic_array_child_contract:
  !ctx func cs after source_id target_id root_addr source_capacity dst_addr fields info width stride initial reference
      dst src len_op ret mid child_len counter_addr dyn_addr dyn_inst index_inst.
    abi_native_memory_ready func cs after source_id target_id root_addr source_capacity (dst_addr + 32w)
      (abi_field_bytes (abi_field_head_size fields) fields) initial /\
    abi_native_dynamic_array_data info width stride fields dst_addr root_addr counter_addr dyn_addr source_capacity 0 initial /\
    abi_allocated_window initial target_id (w2n dst_addr) 32 /\
    abi_native_fields (REPLICATE (LENGTH fields) (info,width,stride,T)) (w2n root_addr + 32) reference fields /\
    mem_bytes_at (w2n root_addr) source_capacity reference = mem_bytes_at (w2n root_addr) source_capacity initial.vs_memory /\
    compile_abi_encode_dyn_loop dst src info width stride len_op cs = (ret,after) /\ fn_has_code cs after func /\
    compile_abi_encode_to_buf (Var (compiler_var_name cs.cs_next_var 14)) (Var (compiler_var_name cs.cs_next_var 9)) info
      (abi_dynamic_loop_prefix_cut dst src width stride len_op cs) = (child_len,mid) /\
    dyn_inst.inst_id <> index_inst.inst_id /\ w2n (dst_addr + 32w) = w2n dst_addr + 32 /\ LENGTH fields < dimword (:256) /\
    abi_operand_before (cs.cs_next_var + 3) dst /\ abi_operand_before (cs.cs_next_var + 3) src /\
    abi_operand_before (cs.cs_next_var + 3) len_op ==>
    abi_dynamic_loop_child_contract ctx func cs dst_addr root_addr width stride counter_addr dyn_addr
      (LENGTH fields) child_len mid
      (abi_native_dynamic_array_invariant ctx func cs after dst src len_op dst_addr root_addr counter_addr dyn_addr
        info width stride fields source_capacity initial dyn_inst index_inst)
Proof
  rpt gen_tac >> strip_tac >> drule_all abi_native_dynamic_array_parts >> strip_tac >>
  simp_tac bool_ss [abi_dynamic_loop_child_contract_def] >> MAP_EVERY qx_gen_tac [`index`, `ss`] >> strip_tac >>
  qpat_assum `abi_native_dynamic_array_invariant _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_dynamic_array_invariant_def]) >>
  drule_all abi_native_dynamic_array_child_complete >> disch_then (qx_choose_then `out` strip_assume_tac) >>
  `compiler_instruction_member (abi_dynamic_loop_prefix_cut dst src width stride len_op cs) dyn_inst /\
    compiler_instruction_member (abi_dynamic_loop_prefix_cut dst src width stride len_op cs) index_inst` by
    fs[abi_native_cursor_def] >>
  drule_all abi_native_dynamic_array_next >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  qpat_assum `abi_native_encoding_result _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_encoding_result_def, abi_encoding_result_def]) >>
  qexistsl_tac [`out`, `n2w (LENGTH (SND (EL index fields)))`] >>
  PURE_REWRITE_TAC [GSYM abi_native_dynamic_array_next_state_def] >>
  asm_simp_tac bool_ss [abi_native_dynamic_array_invariant_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed semantic recursive induction to actual array loop contract: " ^ name)
  end) (DB.thms "abiNativeDynamicArrayContract")

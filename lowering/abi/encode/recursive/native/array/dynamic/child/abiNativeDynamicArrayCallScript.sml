(* TOP-LEVEL: execute the actual compiled recursive child from the native
   semantic induction assertion at its selected array element. Physical
   readiness and original-source agreement are derived, not assumed runs. *)
Theory abiNativeDynamicArrayCall
Ancestors
  abiNativeDynamicArrayCallReady abiNativeDynamicArrayPrefixCode abiNativeDynamicArrayState abiNativeFields
  abiNativeTraversal abiNativeEncodingDefs abiMemoryLeafRun abiDynamicLoopCode abiDynamicLoopStep
  abiStaticLoopCode abiFieldLayoutDefs compileEnv fragExec venomMemDefs venomState list words arithmetic

Theorem abi_native_dynamic_array_call:
  !ctx func cs after source_id target_id root_addr source_capacity dst_addr fields info width stride initial reference
      dst src len_op mid child_len ss index counter_addr dyn_addr.
    abi_native_memory_ready func cs after source_id target_id root_addr source_capacity (dst_addr + 32w)
      (abi_field_bytes (abi_field_head_size fields) fields) initial /\
    abi_native_traversal ctx func cs after (dst_addr + 32w) (abi_field_bytes (abi_field_head_size fields) fields) initial
      (abi_dynamic_loop_prefix_cut dst src width stride len_op cs)
      (abi_dynamic_loop_child_state cs.cs_next_var cs.cs_next_label dst_addr root_addr width stride
        counter_addr dyn_addr (n2w (LENGTH fields)) ss) /\
    abi_native_dynamic_array_data info width stride fields dst_addr root_addr counter_addr dyn_addr source_capacity index ss /\
    abi_native_fields (REPLICATE (LENGTH fields) (info,width,stride,T)) (w2n root_addr + 32) reference fields /\
    mem_bytes_at (w2n root_addr) source_capacity reference = mem_bytes_at (w2n root_addr) source_capacity initial.vs_memory /\
    compile_abi_encode_to_buf (Var (compiler_var_name cs.cs_next_var 14)) (Var (compiler_var_name cs.cs_next_var 9)) info
      (abi_dynamic_loop_prefix_cut dst src width stride len_op cs) = (child_len,mid) /\
    fn_has_code (abi_dynamic_loop_prefix_cut dst src width stride len_op cs) mid func /\ cs_extends mid after /\
    w2n (dst_addr + 32w) = w2n dst_addr + 32 /\ index < LENGTH fields /\ ~ss.vs_halted ==>
    ?out. abi_native_encoding_result ctx func (abi_dynamic_loop_prefix_cut dst src width stride len_op cs) mid child_len
      (dst_addr + 32w + mload (w2n dyn_addr) ss) (SND (EL index fields))
      (abi_dynamic_loop_child_state cs.cs_next_var cs.cs_next_label dst_addr root_addr width stride
        counter_addr dyn_addr (n2w (LENGTH fields)) ss) out /\ ~out.vs_halted
Proof
  rpt gen_tac >> strip_tac >> drule_all abi_native_dynamic_array_call_ready >> strip_tac >>
  qpat_assum `abi_native_dynamic_array_data _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_dynamic_array_data_def]) >>
  qspecl_then [`cs.cs_next_var`, `cs.cs_next_label`, `dst_addr`, `root_addr`, `width`, `stride`, `counter_addr`, `dyn_addr`,
    `n2w (LENGTH fields)`, `ss`] mp_tac abi_dynamic_loop_child_state_values >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  qspecl_then [`dst`, `src`, `width`, `stride`, `len_op`, `cs`] strip_assume_tac abi_native_dynamic_array_child_operands >>
  qpat_x_assum `abi_native_encoder _ _ _ _ _` (mp_tac o PURE_REWRITE_RULE [abi_native_encoder_def]) >>
  disch_then (qspecl_then [`ctx`, `func`, `Var (compiler_var_name cs.cs_next_var 14)`, `Var (compiler_var_name cs.cs_next_var 9)`,
    `abi_dynamic_loop_prefix_cut dst src width stride len_op cs`, `child_len`, `mid`,
    `abi_dynamic_loop_child_state cs.cs_next_var cs.cs_next_label dst_addr root_addr width stride
      counter_addr dyn_addr (n2w (LENGTH fields)) ss`, `root_addr + 32w + n2w index * n2w stride`,
    `dst_addr + 32w + mload (w2n dyn_addr) ss`, `source_id`, `target_id`] mp_tac) >>
  impl_tac >- asm_simp_tac (srw_ss()) [abi_dynamic_loop_prefix_cut_def] >>
  disch_then (qx_choose_then `out` ASSUME_TAC) >> qexists_tac `out` >> conj_tac >- first_assum MATCH_ACCEPT_TAC >>
  `~(abi_dynamic_loop_child_state cs.cs_next_var cs.cs_next_label dst_addr root_addr width stride
    counter_addr dyn_addr (n2w (LENGTH fields)) ss).vs_halted` by asm_simp_tac bool_ss [] >>
  drule_all abi_native_encoding_not_halted >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual native recursive array child invocation: " ^ name)
  end) (DB.thms "abiNativeDynamicArrayCall")

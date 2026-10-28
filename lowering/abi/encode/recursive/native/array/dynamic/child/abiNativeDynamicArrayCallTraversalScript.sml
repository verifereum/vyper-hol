(* TOP-LEVEL: the actual recursive child result advances the enclosing
   loop traversal, retaining its allocation trace and packed output frame. *)
Theory abiNativeDynamicArrayCallTraversal
Ancestors
  abiNativeDynamicArrayBounds abiNativeDynamicArrayState abiNativeTraversal abiNativeTraversalStep
  abiNativeEncodingDefs abiDynamicLoopCode abiDynamicLoopStep abiIdFlow abiEncodeVarFlow abiEncoderStructure
  abiFieldLayoutDefs compileIdFlow compileAllocaProvenance compileEnv fragExec venomMemDefs venomState list words arithmetic

Theorem abi_native_dynamic_array_call_traversal:
  !ctx func cs after source_id target_id root_addr source_capacity dst_addr fields info width stride initial
      dst src len_op mid child_len ss index counter_addr dyn_addr out.
    abi_native_memory_ready func cs after source_id target_id root_addr source_capacity (dst_addr + 32w)
      (abi_field_bytes (abi_field_head_size fields) fields) initial /\
    abi_native_traversal ctx func cs after (dst_addr + 32w) (abi_field_bytes (abi_field_head_size fields) fields) initial
      (abi_dynamic_loop_prefix_cut dst src width stride len_op cs)
      (abi_dynamic_loop_child_state cs.cs_next_var cs.cs_next_label dst_addr root_addr width stride
        counter_addr dyn_addr (n2w (LENGTH fields)) ss) /\
    abi_native_dynamic_array_data info width stride fields dst_addr root_addr counter_addr dyn_addr source_capacity index ss /\
    compile_abi_encode_to_buf (Var (compiler_var_name cs.cs_next_var 14)) (Var (compiler_var_name cs.cs_next_var 9)) info
      (abi_dynamic_loop_prefix_cut dst src width stride len_op cs) = (child_len,mid) /\ cs_extends mid after /\
    w2n (dst_addr + 32w) = w2n dst_addr + 32 /\ index < LENGTH fields /\
    abi_native_encoding_result ctx func (abi_dynamic_loop_prefix_cut dst src width stride len_op cs) mid child_len
      (dst_addr + 32w + mload (w2n dyn_addr) ss) (SND (EL index fields))
      (abi_dynamic_loop_child_state cs.cs_next_var cs.cs_next_label dst_addr root_addr width stride
        counter_addr dyn_addr (n2w (LENGTH fields)) ss) out ==>
    abi_native_traversal ctx func cs after (dst_addr + 32w) (abi_field_bytes (abi_field_head_size fields) fields) initial mid out
Proof
  rpt gen_tac >> strip_tac >> drule_all abi_native_dynamic_array_tail_bounds >> strip_tac >>
  `alloca_inv initial` by fs[abi_native_memory_ready_def] >>
  qpat_assum `abi_native_traversal _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_traversal_def]) >>
  drule compile_abi_encode_id_flow >> strip_tac >>
  `compiler_id_history mid` by (first_x_assum irule >> first_assum MATCH_ACCEPT_TAC) >>
  `cs_extends (abi_dynamic_loop_prefix_cut dst src width stride len_op cs) mid` by
    (drule_all compile_abi_encode_extends >> simp[]) >>
  drule compile_abi_encode_next_var >> DISCH_TAC >>
  qspecl_then [`ctx`, `func`, `cs`, `after`, `dst_addr + 32w`, `abi_field_bytes (abi_field_head_size fields) fields`, `initial`,
    `abi_dynamic_loop_prefix_cut dst src width stride len_op cs`, `mid`, `child_len`,
    `dst_addr + 32w + mload (w2n dyn_addr) ss`, `SND (EL index fields)`,
    `abi_dynamic_loop_child_state cs.cs_next_var cs.cs_next_label dst_addr root_addr width stride
      counter_addr dyn_addr (n2w (LENGTH fields)) ss`, `out`] mp_tac abi_native_traversal_native_step >>
  impl_tac >- asm_simp_tac bool_ss [] >> simp_tac bool_ss []
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual runtime-array child traversal advancement: " ^ name)
  end) (DB.thms "abiNativeDynamicArrayCallTraversal")

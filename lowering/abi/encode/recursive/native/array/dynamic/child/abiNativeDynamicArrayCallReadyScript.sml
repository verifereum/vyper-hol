(* TOP-LEVEL: live loop indices select a semantic recursive-child assertion
   and derive its physical resources from the enclosing loop traversal.
   Source observations keep the independent original reference memory. *)
Theory abiNativeDynamicArrayCallReady
Ancestors
  abiNativeDynamicArrayBounds abiNativeDynamicArrayState abiNativeDynamicArrayPrefixCode abiNativeFields
  abiNativeTraversal abiNativeTraversalReady abiNativeEncodingDefs abiDynamicLoopCode abiDynamicLoopStep
  abiMemoryEncoding abiFieldLayoutDefs compileEnv venomMemDefs venomState list words arithmetic

Theorem abi_native_dynamic_array_call_ready:
  !ctx func cs after source_id target_id root_addr source_capacity dst_addr fields info width stride initial reference
      dst src len_op mid ss index counter_addr dyn_addr.
    abi_native_memory_ready func cs after source_id target_id root_addr source_capacity (dst_addr + 32w)
      (abi_field_bytes (abi_field_head_size fields) fields) initial /\
    abi_native_traversal ctx func cs after (dst_addr + 32w) (abi_field_bytes (abi_field_head_size fields) fields) initial
      (abi_dynamic_loop_prefix_cut dst src width stride len_op cs)
      (abi_dynamic_loop_child_state cs.cs_next_var cs.cs_next_label dst_addr root_addr width stride
        counter_addr dyn_addr (n2w (LENGTH fields)) ss) /\
    abi_native_dynamic_array_data info width stride fields dst_addr root_addr counter_addr dyn_addr source_capacity index ss /\
    abi_native_fields (REPLICATE (LENGTH fields) (info,width,stride,T)) (w2n root_addr + 32) reference fields /\
    mem_bytes_at (w2n root_addr) source_capacity reference = mem_bytes_at (w2n root_addr) source_capacity initial.vs_memory /\
    cs_extends mid after /\ w2n (dst_addr + 32w) = w2n dst_addr + 32 /\ index < LENGTH fields ==>
    abi_native_encoder info (w2n (root_addr + 32w + n2w index * n2w stride)) stride reference (SND (EL index fields)) /\
    abi_native_memory_ready func (abi_dynamic_loop_prefix_cut dst src width stride len_op cs) mid source_id target_id
      (root_addr + 32w + n2w index * n2w stride) stride (dst_addr + 32w + mload (w2n dyn_addr) ss) (SND (EL index fields))
      (abi_dynamic_loop_child_state cs.cs_next_var cs.cs_next_label dst_addr root_addr width stride
        counter_addr dyn_addr (n2w (LENGTH fields)) ss) /\
    mem_bytes_at (w2n (root_addr + 32w + n2w index * n2w stride)) stride reference =
      mem_bytes_at (w2n (root_addr + 32w + n2w index * n2w stride)) stride
        (abi_dynamic_loop_child_state cs.cs_next_var cs.cs_next_label dst_addr root_addr width stride
          counter_addr dyn_addr (n2w (LENGTH fields)) ss).vs_memory
Proof
  rpt gen_tac >> strip_tac >>
  qpat_assum `abi_native_dynamic_array_data _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_dynamic_array_data_def]) >>
  drule_all abi_native_dynamic_array_element_bounds >> strip_tac >>
  drule_all abi_native_dynamic_array_tail_bounds >> strip_tac >>
  qspecl_then [`fields`, `info`, `width`, `stride`, `T`, `w2n root_addr + 32`, `reference`, `index`]
    mp_tac abi_native_array_element >> impl_tac >- asm_simp_tac bool_ss [] >> DISCH_TAC >>
  qspecl_then [`ctx`, `func`, `cs`, `after`, `source_id`, `target_id`, `root_addr`, `source_capacity`,
    `dst_addr + 32w`, `abi_field_bytes (abi_field_head_size fields) fields`, `initial`, `reference`,
    `abi_dynamic_loop_prefix_cut dst src width stride len_op cs`, `mid`,
    `abi_dynamic_loop_child_state cs.cs_next_var cs.cs_next_label dst_addr root_addr width stride
      counter_addr dyn_addr (n2w (LENGTH fields)) ss`, `root_addr + 32w + n2w index * n2w stride`, `stride`,
    `dst_addr + 32w + mload (w2n dyn_addr) ss`, `SND (EL index fields)`, `32 + index * stride`]
    mp_tac abi_native_traversal_call_ready >>
  impl_tac >- asm_simp_tac bool_ss [ADD_ASSOC] >> strip_tac >>
  rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC,
    qpat_assum `w2n (root_addr + 32w + n2w index * n2w stride) = _` (fn th => PURE_REWRITE_TAC [th]) >>
    PURE_REWRITE_TAC [ADD_ASSOC] >> FIRST [
      qpat_assum `abi_native_encoder _ _ _ _ _` (MATCH_ACCEPT_TAC o PURE_REWRITE_RULE [ADD_ASSOC]),
      qpat_assum `mem_bytes_at (w2n root_addr + (32 + index * stride)) stride reference = _`
        (MATCH_ACCEPT_TAC o PURE_REWRITE_RULE [ADD_ASSOC])]]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed semantic child selection and loop allocation readiness: " ^ name)
  end) (DB.thms "abiNativeDynamicArrayCallReady")

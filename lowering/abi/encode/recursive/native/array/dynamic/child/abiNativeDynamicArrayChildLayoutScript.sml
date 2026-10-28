(* TOP-LEVEL: the actual recursive child retains completed heads and tails,
   and places its bytes precisely at the next packed tail position. *)
Theory abiNativeDynamicArrayChildLayout
Ancestors
  abiNativeDynamicArrayBounds abiNativeDynamicArraySource abiNativeDynamicArrayState abiNativeDynamicArrayPrefixState abiNativeLayoutFrame
  abiNativeTraversal abiNativeTraversalReady abiNativeEncodingDefs abiMemoryLeafRun abiDynamicLoopCode abiDynamicLoopStep
  abiFieldMemory abiFieldLayoutDefs compileAllocaProfiles compileAllocaProvenance compileEnv venomMemDefs venomState list pred_set words arithmetic

Theorem abi_native_dynamic_array_child_layout:
  !ctx func cs after source_id target_id root_addr source_capacity dst_addr fields info width stride initial
      dst src len_op mid child_len ss index counter_addr dyn_addr out.
    abi_native_memory_ready func cs after source_id target_id root_addr source_capacity (dst_addr + 32w)
      (abi_field_bytes (abi_field_head_size fields) fields) initial /\
    abi_native_traversal ctx func cs after (dst_addr + 32w) (abi_field_bytes (abi_field_head_size fields) fields) initial
      (abi_dynamic_loop_prefix_cut dst src width stride len_op cs)
      (abi_dynamic_loop_child_state cs.cs_next_var cs.cs_next_label dst_addr root_addr width stride
        counter_addr dyn_addr (n2w (LENGTH fields)) ss) /\
    abi_native_dynamic_array_data info width stride fields dst_addr root_addr counter_addr dyn_addr source_capacity index ss /\
    cs_extends mid after /\ w2n (dst_addr + 32w) = w2n dst_addr + 32 /\ index < LENGTH fields /\
    abi_native_encoding_result ctx func (abi_dynamic_loop_prefix_cut dst src width stride len_op cs) mid child_len
      (dst_addr + 32w + mload (w2n dyn_addr) ss) (SND (EL index fields))
      (abi_dynamic_loop_child_state cs.cs_next_var cs.cs_next_label dst_addr root_addr width stride
        counter_addr dyn_addr (n2w (LENGTH fields)) ss) out ==>
    abi_fields_layout (TAKE index fields) (w2n dst_addr + 32) 0 (abi_field_head_size fields) out /\
    read_memory (w2n dst_addr + 32 + abi_field_head_size fields + abi_field_tail_size (TAKE index fields))
      (LENGTH (SND (EL index fields))) out = SND (EL index fields)
Proof
  rpt gen_tac >> strip_tac >> drule_all abi_native_dynamic_array_tail_bounds >> strip_tac >>
  `alloca_inv initial /\ ~MEM target_id (compiler_alloca_ids cs after)` by fs[abi_native_memory_ready_def] >>
  drule_all abi_native_traversal_allocation >> strip_tac >>
  drule_all abi_native_traversal_windows >> strip_tac >>
  qpat_assum `w2n (dst_addr + 32w) = _` (fn addr_th =>
    qpat_assum `abi_allocated_window _ target_id _ (LENGTH (abi_field_bytes _ fields))`
      (ASSUME_TAC o PURE_REWRITE_RULE [addr_th, abi_field_bytes_length])) >>
  qpat_assum `abi_native_dynamic_array_data _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_dynamic_array_data_def]) >>
  drule_all abi_native_dynamic_array_ranges >> strip_tac >>
  `~MEM target_id (compiler_alloca_ids (abi_dynamic_loop_prefix_cut dst src width stride len_op cs) mid)` by
    (qpat_assum `abi_native_traversal _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_native_traversal_def]) >>
     qspecl_then [`cs`, `abi_dynamic_loop_prefix_cut dst src width stride len_op cs`, `mid`, `after`]
       mp_tac compiler_alloca_profile_subprofile >> impl_tac >- asm_simp_tac bool_ss [] >>
     simp_tac (srw_ss()) [SUBSET_DEF] >> metis_tac[]) >>
  `abi_fields_layout (TAKE index fields) (w2n dst_addr + 32) 0 (abi_field_head_size fields)
    (abi_dynamic_loop_child_state cs.cs_next_var cs.cs_next_label dst_addr root_addr width stride
      counter_addr dyn_addr (n2w (LENGTH fields)) ss)` by
    (qspecl_then [`cs`, `dst_addr`, `root_addr`, `width`, `stride`, `counter_addr`, `dyn_addr`, `n2w (LENGTH fields)`, `ss`]
       strip_assume_tac abi_native_dynamic_array_prefix_context >>
     qspecl_then [`TAKE index fields`, `w2n dst_addr + 32`, `0`, `abi_field_head_size fields`, `ss`,
       `abi_dynamic_loop_child_state cs.cs_next_var cs.cs_next_label dst_addr root_addr width stride
         counter_addr dyn_addr (n2w (LENGTH fields)) ss`] mp_tac abi_fields_layout_memory >>
     impl_tac >- first_assum MATCH_ACCEPT_TAC >> simp[]) >>
  qspecl_then [`ctx`, `func`, `abi_dynamic_loop_prefix_cut dst src width stride len_op cs`, `mid`, `child_len`,
    `dst_addr + 32w + mload (w2n dyn_addr) ss`, `SND (EL index fields)`,
    `abi_dynamic_loop_child_state cs.cs_next_var cs.cs_next_label dst_addr root_addr width stride
      counter_addr dyn_addr (n2w (LENGTH fields)) ss`, `out`, `target_id`, `w2n dst_addr + 32`,
    `LENGTH (abi_field_bytes (abi_field_head_size fields) fields)`, `TAKE index fields`, `abi_field_head_size fields`]
    mp_tac abi_native_result_layout >>
  impl_tac >- (asm_simp_tac bool_ss [abi_field_bytes_length] >> decide_tac) >> DISCH_TAC >>
  qpat_assum `abi_native_encoding_result _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_encoding_result_def, abi_encoding_result_def]) >>
  conj_tac >- first_assum MATCH_ACCEPT_TAC >>
  qpat_assum `w2n (dst_addr + 32w + mload (w2n dyn_addr) ss) = _` (fn tail_th =>
    qpat_assum `w2n (dst_addr + 32w) = _` (fn body_th =>
      qpat_assum `read_memory (w2n (dst_addr + 32w + mload (w2n dyn_addr) ss)) _ out = _`
        (MATCH_ACCEPT_TAC o PURE_REWRITE_RULE [tail_th, body_th])))
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual recursive array child packed-layout preservation: " ^ name)
  end) (DB.thms "abiNativeDynamicArrayChildLayout")

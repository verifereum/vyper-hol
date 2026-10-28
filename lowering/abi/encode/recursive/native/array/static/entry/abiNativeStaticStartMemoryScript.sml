(* TOP-LEVEL: actual index setup preserves every separately owned word and
   establishes the complete raw static-array invariant at its header. *)
Theory abiNativeStaticStartMemory
Ancestors
  abiNativeStaticStartState abiNativeStaticHeaderCode abiNativeStaticArrayState abiNativeArraySource abiNativeArrayBudget
  abiNativeCursor abiNativeTraversal abiNativeEncodingDefs abiAllocatedMemoryFrame abiAllocatedWindows
  abiMemoryFrame abiStaticLoopEntry abiStaticLoopCode memoryReadProps valueEncodingProofs
  compileAllocaProvenance compileEnv venomMemDefs venomState list pair words arithmetic

Theorem abi_native_static_start_owned_word:
  !func root_cs root_after counter_inst cs ss read_id read_addr.
    abi_native_cursor func root_cs root_after counter_inst (abi_static_loop_counter_addr cs.cs_next_id ss)
      (abi_native_static_header_cut cs) (abi_static_loop_start_state cs.cs_next_id cs.cs_next_var cs.cs_next_label ss) /\
    alloca_inv (abi_static_loop_start_state cs.cs_next_id cs.cs_next_var cs.cs_next_label ss) /\
    abi_allocated_window (abi_static_loop_start_state cs.cs_next_id cs.cs_next_var cs.cs_next_label ss)
      read_id (w2n (read_addr:bytes32)) 32 /\ read_id <> counter_inst.inst_id ==>
    mload (w2n read_addr) (abi_static_loop_start_state cs.cs_next_id cs.cs_next_var cs.cs_next_label ss) =
      mload (w2n read_addr) ss
Proof
  rpt gen_tac >> strip_tac >>
  qpat_assum `alloca_inv _` (strip_assume_tac o PURE_REWRITE_RULE [alloca_inv_def]) >>
  qpat_assum `abi_native_cursor _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_cursor_def]) >>
  qspecl_then [`cs`, `ss`] strip_assume_tac abi_native_static_start_context >>
  qspecl_then [`abi_static_loop_start_state cs.cs_next_id cs.cs_next_var cs.cs_next_label ss`, `ss`,
    `abi_static_loop_start_state cs.cs_next_id cs.cs_next_var cs.cs_next_label ss`,
    `[(counter_inst.inst_id,(w2n (abi_static_loop_counter_addr cs.cs_next_id ss),32))]`, `read_id`, `w2n read_addr`, `32`]
    mp_tac abi_allocated_memory_frame_read >>
  impl_tac >- asm_simp_tac bool_ss [EVERY_DEF, MAP, FST, SND, EQ_SYM_EQ] >> simp_tac bool_ss [mload_read_memory]
QED

Theorem abi_native_static_start_data:
  !ctx func root_cs root_after source_id target_id root_addr source_capacity dst_addr fields info width stride initial cs ss counter_inst.
    abi_native_memory_ready func root_cs root_after source_id target_id (root_addr:bytes32) source_capacity dst_addr
      (word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields) initial /\
    abi_native_traversal ctx func root_cs root_after dst_addr
      (word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields)
      initial (abi_native_static_header_cut cs) (abi_static_loop_start_state cs.cs_next_id cs.cs_next_var cs.cs_next_label ss) /\
    abi_native_cursor func root_cs root_after counter_inst (abi_static_loop_counter_addr cs.cs_next_id ss)
      (abi_native_static_header_cut cs) (abi_static_loop_start_state cs.cs_next_id cs.cs_next_var cs.cs_next_label ss) /\
    32 <= source_capacity /\
    abi_memory_fields (REPLICATE (LENGTH fields) (info,width,stride,F))
      (w2n root_addr + 32) (source_capacity - 32) initial.vs_memory fields /\
    mload (w2n root_addr) initial = n2w (LENGTH fields) /\ mload (w2n dst_addr) ss = n2w (LENGTH fields) ==>
    abi_native_static_array_data info width stride fields dst_addr root_addr
      (abi_static_loop_counter_addr cs.cs_next_id ss) source_capacity 0
      (abi_static_loop_start_state cs.cs_next_id cs.cs_next_var cs.cs_next_label ss)
Proof
  rpt gen_tac >> strip_tac >> drule_all abi_native_array_source >> strip_tac >>
  drule_all abi_native_traversal_root_ready >> DISCH_TAC >>
  `alloca_inv (abi_static_loop_start_state cs.cs_next_id cs.cs_next_var cs.cs_next_label ss) /\
    ~MEM target_id (compiler_alloca_ids root_cs root_after) /\
    abi_allocated_window (abi_static_loop_start_state cs.cs_next_id cs.cs_next_var cs.cs_next_label ss) target_id
      (w2n dst_addr) (LENGTH (word_to_bytes (n2w (LENGTH fields):bytes32) T ++
        abi_field_bytes (abi_field_head_size fields) fields))` by fs[abi_native_memory_ready_def] >>
  `counter_inst.inst_id <> target_id` by
    (qpat_assum `abi_native_cursor _ _ _ _ _ _ _`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_native_cursor_def]) >> DISCH_TAC >> gvs[]) >>
  `abi_allocated_window (abi_static_loop_start_state cs.cs_next_id cs.cs_next_var cs.cs_next_label ss)
    target_id (w2n dst_addr) 32` by
    (irule abi_allocated_window_shrink >>
     qexists_tac `LENGTH (word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields)` >>
     simp[]) >>
  qspecl_then [`func`, `root_cs`, `root_after`, `counter_inst`, `cs`, `ss`, `target_id`, `dst_addr`]
    mp_tac abi_native_static_start_owned_word >> impl_tac >- asm_simp_tac bool_ss [EQ_SYM_EQ] >> DISCH_TAC >>
  qspecl_then [`cs`, `ss`] strip_assume_tac abi_native_static_start_context >>
  irule abi_native_static_array_initial >> rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, asm_simp_tac bool_ss []]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual static header memory initialization: " ^ name)
  end) (DB.thms "abiNativeStaticStartMemory")

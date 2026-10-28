(* TOP-LEVEL: root ownership and the real counter instruction discharge
   every static iteration read/write premise. The actual memory effect
   advances packed data and preserves all array allocation resources. *)
Theory abiNativeStaticArrayStep
Ancestors
  abiNativeArrayResources abiNativeStaticArrayBounds abiNativeStaticArraySeparation abiNativeStaticArrayMemory
  abiNativeStaticArrayState abiNativeStaticArrayEffects abiNativeCursor abiNativeEncodingDefs
  abiMemoryEncoding abiFieldLayoutDefs compileAllocaProvenance compileEnv venomMemDefs venomState list words arithmetic

Theorem abi_native_static_array_step:
  !func root_cs root_after source_id target_id counter_inst counter_addr loop_cs root_addr source_capacity dst_addr
      info stride fields initial ss index labels.
    abi_native_memory_ready func root_cs root_after source_id target_id root_addr source_capacity dst_addr
      (word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields) initial /\
    abi_native_array_resources func root_cs root_after source_id target_id counter_inst counter_addr loop_cs
      root_addr source_capacity dst_addr
      (word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields) ss /\
    abi_native_static_array_data info (abi_static_encoder_size info) stride fields dst_addr root_addr counter_addr
      source_capacity index ss /\ index < LENGTH fields ==>
    abi_native_static_array_data info (abi_static_encoder_size info) stride fields dst_addr root_addr counter_addr
      source_capacity (SUC index)
      (abi_static_loop_effect info dst_addr root_addr (abi_static_encoder_size info) stride counter_addr labels ss) /\
    abi_native_array_resources func root_cs root_after source_id target_id counter_inst counter_addr loop_cs
      root_addr source_capacity dst_addr
      (word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields)
      (abi_static_loop_effect info dst_addr root_addr (abi_static_encoder_size info) stride counter_addr labels ss)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_assum `abi_native_static_array_data _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_static_array_data_def]) >>
  qpat_assum `abi_native_array_resources _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_array_resources_def]) >>
  drule_all abi_native_static_array_element_bounds >> strip_tac >>
  `32 + index * abi_static_encoder_size info + abi_static_encoder_size info <=
    LENGTH (word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields)` by decide_tac >>
  `source_id <> target_id /\ ~MEM source_id (compiler_alloca_ids root_cs root_after) /\
    ~MEM target_id (compiler_alloca_ids root_cs root_after)` by fs[abi_native_memory_ready_def] >>
  qspecl_then [`func`, `root_cs`, `root_after`, `counter_inst`, `counter_addr`, `loop_cs`, `ss`, `source_id`, `target_id`]
    mp_tac abi_native_cursor_root_distinct >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qpat_assum `abi_native_cursor _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_cursor_def]) >>
  `allocas_non_overlapping ss` by fs[alloca_inv_def] >>
  qspecl_then [`ss`, `source_id`, `target_id`, `counter_inst.inst_id`, `w2n root_addr`, `source_capacity`,
    `w2n dst_addr`, `LENGTH (word_to_bytes (n2w (LENGTH fields):bytes32) T ++
      abi_field_bytes (abi_field_head_size fields) fields)`, `w2n counter_addr`, `index`, `abi_static_encoder_size info`]
    mp_tac abi_native_static_array_writes_separated >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  drule_all abi_native_static_array_memory_step >> disch_then (qspec_then `labels` ASSUME_TAC) >>
  qspecl_then [`info`, `dst_addr`, `root_addr`, `abi_static_encoder_size info`, `stride`, `counter_addr`, `labels`, `ss`]
    strip_assume_tac abi_native_static_effect_context >>
  drule_all abi_native_array_resources_allocator_state >> DISCH_TAC >>
  asm_simp_tac bool_ss []
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed owned static runtime iteration step: " ^ name)
  end) (DB.thms "abiNativeStaticArrayStep")

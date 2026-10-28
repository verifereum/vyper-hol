(* TOP-LEVEL: a mixed field's actual data and scratch writes preserve the
   unread source and completed head/tail regions. Parent stores participate
   in the same concrete write set as the recursive child. *)
Theory abiNativeDynamicWrites
Ancestors
  abiNativeDynamicSeparation abiNativeDynamicIntervals abiNativeFieldSeparation abiNativeWriteSeparation abiNativeCursor
  abiNativeEncodingDefs abiMemoryFieldsAdvance abiAllocatedWindows abiMemoryFrame
  compileEnv venomState list pair words arithmetic

Theorem abi_native_dynamic_writes_separated:
  !ctx func cs mid ret encoded_addr payload extra ss out source_id target_id root_addr dst_addr
      source_capacity source_offset mem_sz root_payload full_head done_head done_tail is_dyn.
    abi_encoding_result ctx func cs mid ret encoded_addr payload
      (abi_allocation_windows (compiler_alloca_ids cs mid) out ++ extra) ss out /\
    alloca_inv ss /\ source_id <> target_id /\
    ~MEM source_id (compiler_alloca_ids cs mid) /\ ~MEM target_id (compiler_alloca_ids cs mid) /\
    abi_allocated_window ss source_id (w2n (root_addr:bytes32)) source_capacity /\
    abi_allocated_window ss target_id (w2n (dst_addr:bytes32)) (LENGTH (root_payload:word8 list)) /\
    abi_allocated_window ss target_id (w2n encoded_addr) (LENGTH payload) /\
    source_offset + mem_sz <= source_capacity /\ done_head <= LENGTH root_payload /\
    full_head + done_tail <= LENGTH root_payload /\
    done_head + (if is_dyn then 32 else LENGTH payload) <= full_head /\
    w2n encoded_addr = (if is_dyn then w2n dst_addr + full_head + done_tail else w2n dst_addr + done_head) /\
    EVERY (\(b,n). abi_window_separated (w2n root_addr + source_offset + mem_sz)
      (source_capacity - (source_offset + mem_sz)) b n) extra /\
    EVERY (\(b,n). abi_window_separated (w2n dst_addr) done_head b n) extra /\
    EVERY (\(b,n). abi_window_separated (w2n dst_addr + full_head) done_tail b n) extra ==>
    EVERY (\(b,n). abi_window_separated (w2n root_addr + source_offset + mem_sz)
      (source_capacity - (source_offset + mem_sz)) b n)
      (abi_encoding_writes encoded_addr payload (abi_allocation_windows (compiler_alloca_ids cs mid) out ++ extra)) /\
    EVERY (\(b,n). abi_window_separated (w2n dst_addr) done_head b n)
      (abi_encoding_writes encoded_addr payload (abi_allocation_windows (compiler_alloca_ids cs mid) out ++ extra)) /\
    EVERY (\(b,n). abi_window_separated (w2n dst_addr + full_head) done_tail b n)
      (abi_encoding_writes encoded_addr payload (abi_allocation_windows (compiler_alloca_ids cs mid) out ++ extra))
Proof
  rpt gen_tac >> disch_then (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
  qspecl_then [`ss`, `source_id`, `target_id`, `root_addr`, `dst_addr`, `source_capacity`,
    `source_offset`, `mem_sz`, `done_head`, `full_head`, `done_tail`, `root_payload`]
    mp_tac abi_native_field_read_windows >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qspecl_then [`w2n dst_addr`, `full_head`, `done_head`, `done_tail`, `is_dyn`, `LENGTH payload`]
    mp_tac abi_native_field_intervals >> impl_tac >- first_assum MATCH_ACCEPT_TAC >> strip_tac >>
  qpat_assum `w2n encoded_addr = _` (fn th =>
    RULE_ASSUM_TAC (PURE_REWRITE_RULE [SYM th])) >>
  qspecl_then [`ctx`, `func`, `cs`, `mid`, `ret`, `encoded_addr`, `payload`, `extra`, `ss`, `out`,
    `source_id`, `w2n root_addr + source_offset + mem_sz`,
    `source_capacity - (source_offset + mem_sz)`, `target_id`]
    mp_tac abi_native_field_separated >> impl_tac >- asm_simp_tac bool_ss [EQ_SYM_EQ] >> DISCH_TAC >>
  qspecl_then [`ctx`, `func`, `cs`, `mid`, `ret`, `encoded_addr`, `payload`, `extra`, `ss`, `out`,
    `target_id`, `w2n dst_addr`, `done_head`, `target_id`]
    mp_tac abi_native_field_separated >> impl_tac >- asm_simp_tac bool_ss [] >> DISCH_TAC >>
  qspecl_then [`ctx`, `func`, `cs`, `mid`, `ret`, `encoded_addr`, `payload`, `extra`, `ss`, `out`,
    `target_id`, `w2n dst_addr + full_head`, `done_tail`, `target_id`]
    mp_tac abi_native_field_separated >> impl_tac >- asm_simp_tac bool_ss [] >> DISCH_TAC >>
  rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

Theorem abi_native_dynamic_static_writes:
  !ctx func root_cs root_after counter_inst cs mid ret source_id target_id dst_addr dyn_addr root_addr source_offset
      source_capacity mem_sz done_head full_head done_tail payload root_payload ss out.
    abi_native_encoding_result ctx func cs mid ret (dst_addr + n2w done_head) payload ss out /\
    abi_native_memory_ready func cs mid source_id target_id (root_addr + n2w source_offset) mem_sz
      (dst_addr + n2w done_head) payload ss /\
    abi_native_cursor func root_cs root_after counter_inst dyn_addr cs ss /\
    counter_inst.inst_id <> target_id /\ cs_extends cs mid /\ fn_has_code cs mid func /\
    abi_allocated_window ss source_id (w2n (root_addr:bytes32)) source_capacity /\
    abi_allocated_window ss target_id (w2n (dst_addr:bytes32)) (LENGTH (root_payload:word8 list)) /\
    source_offset + mem_sz <= source_capacity /\ done_head <= LENGTH root_payload /\
    full_head + done_tail <= LENGTH root_payload /\ done_head + LENGTH payload <= full_head /\
    w2n (dst_addr + n2w done_head) = w2n dst_addr + done_head ==>
    EVERY (\(b,n). abi_window_separated (w2n root_addr + source_offset + mem_sz)
      (source_capacity - (source_offset + mem_sz)) b n)
      (abi_encoding_writes (dst_addr + n2w done_head) payload (abi_allocation_windows (compiler_alloca_ids cs mid) out)) /\
    EVERY (\(b,n). abi_window_separated (w2n dst_addr) done_head b n)
      (abi_encoding_writes (dst_addr + n2w done_head) payload (abi_allocation_windows (compiler_alloca_ids cs mid) out)) /\
    EVERY (\(b,n). abi_window_separated (w2n dst_addr + full_head) done_tail b n)
      (abi_encoding_writes (dst_addr + n2w done_head) payload (abi_allocation_windows (compiler_alloca_ids cs mid) out)) /\
    EVERY (\(b,n). abi_window_separated (w2n dyn_addr) 32 b n)
      (abi_encoding_writes (dst_addr + n2w done_head) payload (abi_allocation_windows (compiler_alloca_ids cs mid) out))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_assum `abi_native_memory_ready _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_memory_ready_def]) >>
  qpat_assum `abi_native_encoding_result _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_encoding_result_def]) >>
  qspecl_then [`ctx`, `func`, `cs`, `mid`, `ret`, `dst_addr + n2w done_head`, `payload`, `[]`, `ss`, `out`,
    `source_id`, `target_id`, `root_addr`, `dst_addr`, `source_capacity`, `source_offset`, `mem_sz`,
    `root_payload`, `full_head`, `done_head`, `done_tail`, `F`]
    mp_tac abi_native_dynamic_writes_separated >>
  simp_tac bool_ss [APPEND_NIL, EVERY_DEF] >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  drule_all abi_native_cursor_local_exclusion >> DISCH_TAC >>
  qpat_assum `abi_native_cursor _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_cursor_def]) >>
  qspecl_then [`ctx`, `func`, `cs`, `mid`, `ret`, `dst_addr + n2w done_head`, `payload`, `ss`, `out`,
    `counter_inst.inst_id`, `w2n dyn_addr`, `32`, `target_id`]
    mp_tac abi_native_writes_separated >> impl_tac >- asm_simp_tac bool_ss [EQ_SYM_EQ] >> DISCH_TAC >>
  rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

Theorem abi_native_dynamic_parent_writes:
  !ss source_id target_id counter_id root_addr dst_addr head_addr dyn_addr source_capacity
      source_offset mem_sz root_payload full_head done_head done_tail.
    allocas_non_overlapping ss /\ source_id <> target_id /\
    counter_id <> source_id /\ counter_id <> target_id /\
    abi_allocated_window ss source_id (w2n (root_addr:bytes32)) source_capacity /\
    abi_allocated_window ss target_id (w2n (dst_addr:bytes32)) (LENGTH (root_payload:word8 list)) /\
    abi_allocated_window ss target_id (w2n (head_addr:bytes32)) 32 /\
    abi_allocated_window ss counter_id (w2n (dyn_addr:bytes32)) 32 /\
    source_offset + mem_sz <= source_capacity /\ done_head <= LENGTH root_payload /\
    full_head + done_tail <= LENGTH root_payload /\ done_head + 32 <= full_head /\
    w2n head_addr = w2n dst_addr + done_head ==>
    EVERY (\(b,n). abi_window_separated (w2n root_addr + source_offset + mem_sz)
      (source_capacity - (source_offset + mem_sz)) b n) [(w2n head_addr,32);(w2n dyn_addr,32)] /\
    EVERY (\(b,n). abi_window_separated (w2n dst_addr) done_head b n)
      [(w2n head_addr,32);(w2n dyn_addr,32)] /\
    EVERY (\(b,n). abi_window_separated (w2n dst_addr + full_head) done_tail b n)
      [(w2n head_addr,32);(w2n dyn_addr,32)]
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`ss`, `source_id`, `target_id`, `root_addr`, `dst_addr`, `source_capacity`,
    `source_offset`, `mem_sz`, `done_head`, `full_head`, `done_tail`, `root_payload`]
    mp_tac abi_native_field_read_windows >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `abi_window_separated (w2n dst_addr) done_head (w2n head_addr) 32 /\
    abi_window_separated (w2n dst_addr + full_head) done_tail (w2n head_addr) 32` by
    (simp[abi_window_separated_def, compileEnvTheory.regions_disjoint_def] >> decide_tac) >>
  qspecl_then [`ss`, `source_id`, `w2n root_addr + source_offset + mem_sz`,
    `source_capacity - (source_offset + mem_sz)`, `target_id`, `w2n head_addr`, `counter_id`, `w2n dyn_addr`]
    mp_tac abi_native_parent_stores_separated >> impl_tac >- asm_simp_tac bool_ss [EQ_SYM_EQ] >> DISCH_TAC >>
  qspecl_then [`ss`, `target_id`, `w2n dst_addr`, `done_head`, `target_id`, `w2n head_addr`,
    `counter_id`, `w2n dyn_addr`] mp_tac abi_native_parent_stores_separated >>
  impl_tac >- asm_simp_tac bool_ss [] >> DISCH_TAC >>
  qspecl_then [`ss`, `target_id`, `w2n dst_addr + full_head`, `done_tail`, `target_id`, `w2n head_addr`,
    `counter_id`, `w2n dyn_addr`] mp_tac abi_native_parent_stores_separated >>
  impl_tac >- asm_simp_tac bool_ss [] >> DISCH_TAC >>
  rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual mixed field write preservation: " ^ name)
  end) (DB.thms "abiNativeDynamicWrites")

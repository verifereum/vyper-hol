(* TOP-LEVEL: owned source/head/tail reads and actual parent stores supply
   concrete separation for mixed traversal, without instruction row tables. *)
Theory abiNativeDynamicSeparation
Ancestors
  abiNativeDynamicBounds abiNativeDynamicIntervals abiNativeCursor abiNativeTraversal abiNativeTraversalReady
  abiNativeEncodingDefs abiMemoryFieldsState abiFieldLayoutDefs
  abiAllocatedWindows abiAllocatedSubwindows abiAllocatedSeparation abiMemoryFrame
  compileEnv venomMemDefs venomState list pair words arithmetic

Theorem abi_native_field_read_windows:
  !ss source_id target_id root_addr dst_addr source_capacity source_offset mem_sz
      done_head full_head done_tail root_payload.
    abi_allocated_window ss source_id (w2n (root_addr:bytes32)) source_capacity /\
    abi_allocated_window ss target_id (w2n (dst_addr:bytes32)) (LENGTH (root_payload:word8 list)) /\
    source_offset + mem_sz <= source_capacity /\ done_head <= LENGTH root_payload /\
    full_head + done_tail <= LENGTH root_payload ==>
    abi_allocated_window ss source_id (w2n root_addr + source_offset + mem_sz)
      (source_capacity - (source_offset + mem_sz)) /\
    abi_allocated_window ss target_id (w2n dst_addr) done_head /\
    abi_allocated_window ss target_id (w2n dst_addr + full_head) done_tail
Proof
  rpt gen_tac >> strip_tac >>
  `abi_allocated_window ss source_id (w2n root_addr + source_offset + mem_sz)
    (source_capacity - (source_offset + mem_sz))` by
    (qspecl_then [`ss`, `source_id`, `w2n root_addr`, `source_capacity`,
       `w2n root_addr + source_offset + mem_sz`, `source_capacity - (source_offset + mem_sz)`]
       mp_tac abi_allocated_window_subwindow >>
     impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac) >> simp[]) >>
  `abi_allocated_window ss target_id (w2n dst_addr) done_head` by
    (qspecl_then [`ss`, `target_id`, `w2n dst_addr`, `LENGTH root_payload`, `done_head`]
       mp_tac abi_allocated_window_shrink >> simp[]) >>
  `abi_allocated_window ss target_id (w2n dst_addr + full_head) done_tail` by
    (qspecl_then [`ss`, `target_id`, `w2n dst_addr`, `LENGTH root_payload`,
       `w2n dst_addr + full_head`, `done_tail`] mp_tac abi_allocated_window_subwindow >>
     impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac) >> simp[]) >>
  rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED


Theorem abi_native_parent_stores_separated:
  !ss read_id read_offset read_len target_id head_base counter_id counter_base.
    allocas_non_overlapping ss /\ abi_allocated_window ss read_id read_offset read_len /\
    abi_allocated_window ss target_id head_base 32 /\ abi_allocated_window ss counter_id counter_base 32 /\
    counter_id <> read_id /\
    (target_id = read_id ==> abi_window_separated read_offset read_len head_base 32) ==>
    EVERY (\(write_base,write_count). abi_window_separated read_offset read_len write_base write_count)
      [(head_base,32);(counter_base,32)]
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`ss`, `[(target_id,(head_base,32));(counter_id,(counter_base,32))]`,
    `read_id`, `read_offset`, `read_len`] mp_tac abi_allocated_windows_separated >>
  impl_tac >- simp[EQ_SYM_EQ] >> simp[]
QED

Theorem abi_native_dynamic_store_regions:
  !ss target_id counter_id head_base tail_base payload_len counter_base.
    alloca_inv ss /\ abi_allocated_window ss target_id head_base 32 /\
    abi_allocated_window ss target_id tail_base payload_len /\
    abi_allocated_window ss counter_id counter_base 32 /\ target_id <> counter_id /\
    regions_disjoint tail_base payload_len head_base 32 ==>
    regions_disjoint head_base 32 counter_base 32 /\
    regions_disjoint tail_base payload_len head_base 32 /\
    regions_disjoint tail_base payload_len counter_base 32
Proof
  rpt gen_tac >> strip_tac >> `allocas_non_overlapping ss` by fs[alloca_inv_def] >>
  `regions_disjoint head_base 32 counter_base 32` by
    (qspecl_then [`ss`, `(target_id,(head_base,32))`, `(counter_id,(counter_base,32))`]
       mp_tac abi_allocated_window_disjoint >> impl_tac >- simp[] >> simp[]) >>
  `regions_disjoint tail_base payload_len counter_base 32` by
    (qspecl_then [`ss`, `(target_id,(tail_base,payload_len))`, `(counter_id,(counter_base,32))`]
       mp_tac abi_allocated_window_disjoint >> impl_tac >- simp[] >> simp[]) >>
  rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

Theorem abi_native_dynamic_call_store_regions:
  !ctx func root_cs root_after source_id target_id initial full done payload fields dst_addr dyn_addr root_addr
      source_capacity source_offset info abi_sz mem_sz rest cs ss counter_inst.
    full = done ++ ((T,payload)::fields) /\
    abi_native_memory_ready func root_cs root_after source_id target_id root_addr source_capacity dst_addr
      (abi_field_bytes (abi_field_head_size full) full) initial /\
    abi_native_traversal ctx func root_cs root_after dst_addr
      (abi_field_bytes (abi_field_head_size full) full) initial cs ss /\
    abi_native_cursor func root_cs root_after counter_inst dyn_addr cs ss /\
    abi_memory_fields_data done ((info,abi_sz,mem_sz,T)::rest) ((T,payload)::fields)
      (abi_field_head_size full) dst_addr dyn_addr root_addr source_capacity source_offset ss ==>
    regions_disjoint (w2n (dst_addr + n2w (abi_field_head_size done))) 32 (w2n dyn_addr) 32 /\
    regions_disjoint (w2n (dst_addr + mload (w2n dyn_addr) ss)) (LENGTH payload)
      (w2n (dst_addr + n2w (abi_field_head_size done))) 32 /\
    regions_disjoint (w2n (dst_addr + mload (w2n dyn_addr) ss)) (LENGTH payload) (w2n dyn_addr) 32
Proof
  rpt gen_tac >> strip_tac >>
  drule_all abi_native_dynamic_field_bounds >> simp_tac bool_ss [] >> strip_tac >>
  drule_all abi_native_traversal_windows >> strip_tac >>
  `alloca_inv initial /\ ~MEM source_id (compiler_alloca_ids root_cs root_after) /\
    ~MEM target_id (compiler_alloca_ids root_cs root_after)` by
    (qpat_assum `abi_native_memory_ready _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_native_memory_ready_def]) >>
     rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  drule_all abi_native_traversal_allocation >> strip_tac >>
  drule_all abi_native_cursor_root_distinct >> strip_tac >>
  `LENGTH (abi_field_bytes (abi_field_head_size full) full) =
    abi_field_head_size full + abi_field_tail_size full` by simp[] >>
  `w2n dst_addr <= w2n (dst_addr + n2w (abi_field_head_size done)) /\
    w2n (dst_addr + n2w (abi_field_head_size done)) + 32 <=
      w2n dst_addr + LENGTH (abi_field_bytes (abi_field_head_size full) full)` by decide_tac >>
  `abi_allocated_window ss target_id (w2n (dst_addr + n2w (abi_field_head_size done))) 32` by
    (qspecl_then [`ss`, `target_id`, `w2n dst_addr`, `LENGTH (abi_field_bytes (abi_field_head_size full) full)`,
       `w2n (dst_addr + n2w (abi_field_head_size done))`, `32`] mp_tac abi_allocated_window_subwindow >>
     impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> disch_then MATCH_ACCEPT_TAC) >>
  `abi_allocated_window ss target_id (w2n (dst_addr + mload (w2n dyn_addr) ss)) (LENGTH payload)` by
    (qspecl_then [`ss`, `target_id`, `w2n dst_addr`, `LENGTH (abi_field_bytes (abi_field_head_size full) full)`,
       `w2n (dst_addr + mload (w2n dyn_addr) ss)`, `LENGTH payload`] mp_tac abi_allocated_window_subwindow >>
     impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> disch_then MATCH_ACCEPT_TAC) >>
  qspecl_then [`w2n dst_addr`, `abi_field_head_size full`, `abi_field_head_size done`,
    `abi_field_tail_size done`, `T`, `LENGTH payload`] mp_tac abi_native_field_intervals >>
  simp_tac bool_ss [] >> impl_tac >- first_assum MATCH_ACCEPT_TAC >> strip_tac >>
  `regions_disjoint (w2n (dst_addr + mload (w2n dyn_addr) ss)) (LENGTH payload)
    (w2n (dst_addr + n2w (abi_field_head_size done))) 32` by
    (qpat_assum `w2n (dst_addr + mload (w2n dyn_addr) ss) = _` (fn tail_th =>
       qpat_assum `w2n (dst_addr + n2w (abi_field_head_size done)) = _` (fn head_th =>
         PURE_REWRITE_TAC [tail_th,head_th])) >>
     simp_tac bool_ss [ADD_ASSOC] >> first_assum MATCH_ACCEPT_TAC) >>
  qpat_x_assum `abi_native_cursor _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_cursor_def]) >>
  qspecl_then [`ss`, `target_id`, `counter_inst.inst_id`,
    `w2n (dst_addr + n2w (abi_field_head_size done))`, `w2n (dst_addr + mload (w2n dyn_addr) ss)`,
    `LENGTH payload`, `w2n dyn_addr`] mp_tac abi_native_dynamic_store_regions >>
  impl_tac >- asm_simp_tac bool_ss [EQ_SYM_EQ] >> strip_tac >>
  qpat_assum `w2n (dst_addr + n2w (abi_field_head_size done)) = _` (fn head_th =>
    qpat_assum `w2n (dst_addr + mload (w2n dyn_addr) ss) = _` (fn tail_th =>
      RULE_ASSUM_TAC (PURE_REWRITE_RULE [head_th,tail_th]) >> PURE_REWRITE_TAC [head_th,tail_th])) >>
  RULE_ASSUM_TAC (SIMP_RULE bool_ss [ADD_ASSOC]) >> simp_tac bool_ss [ADD_ASSOC] >>
  rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed owned mixed field/store separation: " ^ name)
  end) (DB.thms "abiNativeDynamicSeparation")

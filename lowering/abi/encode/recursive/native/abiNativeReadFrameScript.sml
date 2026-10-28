(* TOP-LEVEL: actual native recursive results protect allocated source,
   suffix, head and counter reads. Only writes within the reader's own
   output allocation require a local interval-separation argument. *)
Theory abiNativeReadFrame
Ancestors
  abiNativeEncodingDefs abiNativeResources abiMemoryLeafRun abiAllocationWindows
  abiAllocatedWindows abiAllocatedSeparation abiWriterFrame abiMemoryFrame
  allocationGrowth memoryReadProps allocaCacheProps compileAllocaProvenance
  venomMemDefs venomState compileEnv list words arithmetic

Theorem abi_native_old_instruction_not_scratch:
  !func cs cs' old_inst.
    fn_inst_ids_distinct func /\ cs_extends cs cs' /\ fn_has_code cs cs' func /\
    compiler_instruction_member cs old_inst /\ MEM old_inst (fn_insts func) ==>
    ~MEM old_inst.inst_id (compiler_alloca_ids cs cs')
Proof
  rpt gen_tac >> strip_tac >> DISCH_TAC >>
  qpat_x_assum `MEM _ (compiler_alloca_ids _ _)`
    (mp_tac o PURE_REWRITE_RULE [compiler_alloca_ids_member]) >>
  disch_then (qx_choose_then `fresh_inst` strip_assume_tac) >>
  `MEM fresh_inst (fn_insts func)` by
    (drule_all compiler_new_instruction_member >> simp[]) >>
  `fresh_inst = old_inst` by
    (qspecl_then [`func`, `fresh_inst`, `old_inst`] mp_tac fn_instruction_id_injective >> simp[]) >>
  gvs[]
QED

Theorem abi_native_result_read:
  !ctx func cs cs' ret dst_addr payload before after read_id read_offset read_len.
    abi_native_encoding_result ctx func cs cs' ret dst_addr payload before after /\
    alloca_inv before /\ abi_allocated_window before read_id read_offset read_len /\
    ~MEM read_id (compiler_alloca_ids cs cs') /\
    abi_window_separated read_offset read_len (w2n dst_addr) (LENGTH payload) ==>
    read_memory read_offset read_len after = read_memory read_offset read_len before
Proof
  rpt gen_tac >> strip_tac >> drule_all abi_native_result_allocation >> strip_tac >>
  `abi_allocated_window after read_id read_offset read_len` by
    (drule_all allocation_growth_window >> simp[]) >>
  `allocas_non_overlapping after` by fs[alloca_inv_def] >>
  qspecl_then [`compiler_alloca_ids cs cs'`, `after`, `read_id`, `read_offset`, `read_len`]
    mp_tac abi_allocation_windows_protect_owned >> impl_tac >- simp[] >> DISCH_TAC >>
  qpat_x_assum `abi_native_encoding_result _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_encoding_result_def, abi_encoding_result_def]) >>
  qspecl_then [`(w2n dst_addr,LENGTH payload)::abi_allocation_windows (compiler_alloca_ids cs cs') after`,
    `before`, `after`, `read_offset`, `read_len`] mp_tac abi_memory_frame_read >> simp[]
QED

Theorem abi_native_result_owned_read:
  !ctx func cs cs' ret dst_addr payload before after read_id read_offset read_len target_id.
    abi_native_encoding_result ctx func cs cs' ret dst_addr payload before after /\
    alloca_inv before /\ abi_allocated_window before read_id read_offset read_len /\
    abi_allocated_window before target_id (w2n dst_addr) (LENGTH payload) /\
    ~MEM read_id (compiler_alloca_ids cs cs') /\
    (target_id = read_id ==>
      abi_window_separated read_offset read_len (w2n dst_addr) (LENGTH payload)) ==>
    read_memory read_offset read_len after = read_memory read_offset read_len before
Proof
  rpt gen_tac >> strip_tac >>
  `allocas_non_overlapping before` by fs[alloca_inv_def] >>
  `abi_window_separated read_offset read_len (w2n dst_addr) (LENGTH payload)` by
    (drule_all abi_allocated_window_separated >> simp[]) >>
  drule_all abi_native_result_read >> simp[]
QED

Theorem abi_native_result_source:
  !ctx func cs cs' ret dst_addr payload before after source_id target_id src_addr span.
    abi_native_encoding_result ctx func cs cs' ret dst_addr payload before after /\
    abi_native_memory_ready func cs cs' source_id target_id src_addr span dst_addr payload before ==>
    mem_bytes_at (w2n src_addr) span after.vs_memory =
      mem_bytes_at (w2n src_addr) span before.vs_memory
Proof
  rpt gen_tac >> simp_tac bool_ss [abi_native_memory_ready_def] >>
  disch_then (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
  qspecl_then [`ctx`, `func`, `cs`, `cs'`, `ret`, `dst_addr`, `payload`, `before`, `after`,
    `source_id`, `w2n src_addr`, `span`, `target_id`] mp_tac abi_native_result_owned_read >>
  impl_tac >- simp[EQ_SYM_EQ] >> simp[read_memory_eq_mem_bytes_at]
QED

Theorem abi_native_old_instruction_read:
  !ctx func cs cs' ret dst_addr payload before after old_inst read_offset read_len.
    abi_native_encoding_result ctx func cs cs' ret dst_addr payload before after /\
    fn_inst_ids_distinct func /\ cs_extends cs cs' /\ fn_has_code cs cs' func /\
    compiler_instruction_member cs old_inst /\ MEM old_inst (fn_insts func) /\
    alloca_inv before /\ abi_allocated_window before old_inst.inst_id read_offset read_len /\
    abi_window_separated read_offset read_len (w2n dst_addr) (LENGTH payload) ==>
    read_memory read_offset read_len after = read_memory read_offset read_len before
Proof
  rpt gen_tac >> strip_tac >>
  drule_all abi_native_old_instruction_not_scratch >> DISCH_TAC >>
  drule_all abi_native_result_read >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed native recursive owned read frames: " ^ name)
  end) (DB.thms "abiNativeReadFrame")

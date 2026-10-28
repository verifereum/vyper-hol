(* TOP-LEVEL: allocation ownership supplies the unread-source and completed
   head separation required by static traversal, for arbitrary children. *)
Theory abiNativeStaticSeparation
Ancestors
  abiNativeWriteSeparation abiNativeEncodingDefs abiMemoryFieldsAdvance abiAllocationWindows
  abiAllocatedWindows abiAllocatedSubwindows abiMemoryFrame
  compileEnv venomMemDefs venomState list pair words arithmetic

Theorem abi_native_static_separation:
  !ctx func cs mid ret dst_addr root_addr source_offset source_capacity mem_sz head_offset payload
      root_payload ss out source_id target_id.
    abi_native_encoding_result ctx func cs mid ret (dst_addr + n2w head_offset) payload ss out /\
    abi_native_memory_ready func cs mid source_id target_id (root_addr + n2w source_offset) mem_sz
      (dst_addr + n2w head_offset) payload ss /\
    abi_allocated_window ss source_id (w2n (root_addr:bytes32)) source_capacity /\
    abi_allocated_window ss target_id (w2n dst_addr) (LENGTH (root_payload:word8 list)) /\
    source_offset + mem_sz <= source_capacity /\ head_offset <= LENGTH root_payload /\
    w2n (dst_addr + n2w head_offset) = w2n dst_addr + head_offset ==>
    EVERY (\(write_base,write_count).
      abi_window_separated (w2n root_addr + source_offset + mem_sz)
        (source_capacity - (source_offset + mem_sz)) write_base write_count)
      (abi_encoding_writes (dst_addr + n2w head_offset) payload
        (abi_allocation_windows (compiler_alloca_ids cs mid) out)) /\
    EVERY (\(write_base,write_count).
      abi_window_separated (w2n dst_addr) head_offset write_base write_count)
      (abi_encoding_writes (dst_addr + n2w head_offset) payload
        (abi_allocation_windows (compiler_alloca_ids cs mid) out))
Proof
  rpt gen_tac >> disch_then (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
  qpat_x_assum `abi_native_memory_ready _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_memory_ready_def]) >>
  `abi_allocated_window ss source_id (w2n root_addr + source_offset + mem_sz)
    (source_capacity - (source_offset + mem_sz))` by
    (qspecl_then [`ss`, `source_id`, `w2n root_addr`, `source_capacity`,
       `w2n root_addr + source_offset + mem_sz`, `source_capacity - (source_offset + mem_sz)`]
       mp_tac abi_allocated_window_subwindow >>
     impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac) >> simp[]) >>
  `abi_allocated_window ss target_id (w2n dst_addr) head_offset` by
    (qspecl_then [`ss`, `target_id`, `w2n dst_addr`, `LENGTH root_payload`, `head_offset`]
       mp_tac abi_allocated_window_shrink >> simp[]) >>
  `abi_window_separated (w2n dst_addr) head_offset
    (w2n (dst_addr + n2w head_offset)) (LENGTH payload)` by
    simp[abi_window_separated_def, compileEnvTheory.regions_disjoint_def] >>
  qspecl_then [`ctx`, `func`, `cs`, `mid`, `ret`, `dst_addr + n2w head_offset`, `payload`, `ss`, `out`,
    `source_id`, `w2n root_addr + source_offset + mem_sz`, `source_capacity - (source_offset + mem_sz)`,
    `target_id`] mp_tac abi_native_writes_separated >> impl_tac >- simp[EQ_SYM_EQ] >> DISCH_TAC >>
  qspecl_then [`ctx`, `func`, `cs`, `mid`, `ret`, `dst_addr + n2w head_offset`, `payload`, `ss`, `out`,
    `target_id`, `w2n dst_addr`, `head_offset`, `target_id`] mp_tac abi_native_writes_separated >>
  impl_tac >- simp[] >> DISCH_TAC >> conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed owned native static field separation: " ^ name)
  end) (DB.thms "abiNativeStaticSeparation")

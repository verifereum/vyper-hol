(* TOP-LEVEL: a dynamic child's concrete recursive writes and the two
   parent stores preserve unread source, completed heads and completed
   tails, deriving separation from their allocation identities. *)
Theory abiNativeDynamicStoreWrites
Ancestors
  abiNativeDynamicWrites abiNativeDynamicSeparation abiNativeCursor abiNativeEncodingDefs
  abiNativeFieldSeparation abiMemoryFieldsAdvance abiAllocatedSubwindows abiAllocatedWindows
  abiMemoryFrame compileEnv venomMemDefs venomState list pair words arithmetic

Theorem abi_native_dynamic_dynamic_writes:
  !ctx func root_cs root_after counter_inst cs mid ret source_id target_id dst_addr dyn_addr root_addr
      source_offset source_capacity mem_sz done_head full_head done_tail payload root_payload ss out.
    abi_encoding_result ctx func cs mid ret (dst_addr + mload (w2n dyn_addr) ss) payload
      (abi_allocation_windows (compiler_alloca_ids cs mid) out ++
        [(w2n (dst_addr + n2w done_head),32);(w2n dyn_addr,32)]) ss out /\
    abi_native_memory_ready func cs mid source_id target_id (root_addr + n2w source_offset) mem_sz
      (dst_addr + mload (w2n dyn_addr) ss) payload ss /\
    abi_native_cursor func root_cs root_after counter_inst dyn_addr cs ss /\
    counter_inst.inst_id <> source_id /\ counter_inst.inst_id <> target_id /\
    abi_allocated_window ss source_id (w2n (root_addr:bytes32)) source_capacity /\
    abi_allocated_window ss target_id (w2n (dst_addr:bytes32)) (LENGTH (root_payload:word8 list)) /\
    source_offset + mem_sz <= source_capacity /\ done_head <= LENGTH root_payload /\
    full_head + done_tail <= LENGTH root_payload /\ done_head + 32 <= full_head /\
    w2n (dst_addr + n2w done_head) = w2n dst_addr + done_head /\
    w2n (dst_addr + mload (w2n dyn_addr) ss) = w2n dst_addr + full_head + done_tail ==>
    EVERY (\(b,n). abi_window_separated (w2n root_addr + source_offset + mem_sz)
      (source_capacity - (source_offset + mem_sz)) b n)
      (abi_encoding_writes (dst_addr + mload (w2n dyn_addr) ss) payload
        (abi_allocation_windows (compiler_alloca_ids cs mid) out ++
          [(w2n (dst_addr + n2w done_head),32);(w2n dyn_addr,32)])) /\
    EVERY (\(b,n). abi_window_separated (w2n dst_addr) done_head b n)
      (abi_encoding_writes (dst_addr + mload (w2n dyn_addr) ss) payload
        (abi_allocation_windows (compiler_alloca_ids cs mid) out ++
          [(w2n (dst_addr + n2w done_head),32);(w2n dyn_addr,32)])) /\
    EVERY (\(b,n). abi_window_separated (w2n dst_addr + full_head) done_tail b n)
      (abi_encoding_writes (dst_addr + mload (w2n dyn_addr) ss) payload
        (abi_allocation_windows (compiler_alloca_ids cs mid) out ++
          [(w2n (dst_addr + n2w done_head),32);(w2n dyn_addr,32)]))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_assum `abi_native_memory_ready _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_memory_ready_def]) >>
  `allocas_non_overlapping ss` by fs[alloca_inv_def] >>
  `abi_allocated_window ss target_id (w2n (dst_addr + n2w done_head)) 32` by
    (qspecl_then [`ss`, `target_id`, `w2n dst_addr`, `LENGTH root_payload`,
       `w2n (dst_addr + n2w done_head)`, `32`] mp_tac abi_allocated_window_subwindow >>
     impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac) >> simp[]) >>
  qpat_assum `abi_native_cursor _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_cursor_def]) >>
  qspecl_then [`ss`, `source_id`, `target_id`, `counter_inst.inst_id`, `root_addr`, `dst_addr`,
    `dst_addr + n2w done_head`, `dyn_addr`, `source_capacity`, `source_offset`, `mem_sz`,
    `root_payload`, `full_head`, `done_head`, `done_tail`] mp_tac abi_native_dynamic_parent_writes >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> strip_tac >>
  qspecl_then [`ctx`, `func`, `cs`, `mid`, `ret`, `dst_addr + mload (w2n dyn_addr) ss`, `payload`,
    `[(w2n (dst_addr + n2w done_head),32);(w2n dyn_addr,32)]`, `ss`, `out`, `source_id`, `target_id`,
    `root_addr`, `dst_addr`, `source_capacity`, `source_offset`, `mem_sz`, `root_payload`,
    `full_head`, `done_head`, `done_tail`, `T`] mp_tac abi_native_dynamic_writes_separated >>
  simp_tac bool_ss [] >> impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp_tac bool_ss []
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual dynamic field/store preservation: " ^ name)
  end) (DB.thms "abiNativeDynamicStoreWrites")

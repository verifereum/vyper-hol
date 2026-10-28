(* TOP-LEVEL: the real stores and latch retain both owned loop cursors and
   fit the enclosing output/profile frame, including on repeated visits. *)
Theory abiNativeDynamicArrayUpdateFrame
Ancestors
  abiNativeDynamicArrayUpdateState abiNativeDynamicArrayCallCursor abiNativeCursorLoop abiNativeCursor
  abiMemoryFrameCover abiAllocatorState abiMemoryFrame compileAllocaProvenance
  compileEnv venomState venomInst list words

Theorem abi_native_dynamic_array_next_cursor_frame:
  !func root_cs root_after cs mid dst_addr width counter_addr dyn_addr index tail_offset child_size ss
      dyn_inst index_inst root_dst root_payload.
    abi_native_cursor func root_cs root_after dyn_inst dyn_addr mid ss /\
    abi_native_cursor func root_cs root_after index_inst counter_addr mid ss /\
    w2n (root_dst:bytes32) <= w2n (dst_addr + 32w + n2w index * n2w width) /\
    w2n (dst_addr + 32w + n2w index * n2w width) + 32 <= w2n root_dst + LENGTH (root_payload:word8 list) ==>
    abi_native_cursor func root_cs root_after dyn_inst dyn_addr mid
      (abi_native_dynamic_array_next_state cs mid dst_addr width counter_addr dyn_addr index tail_offset child_size ss) /\
    abi_native_cursor func root_cs root_after index_inst counter_addr mid
      (abi_native_dynamic_array_next_state cs mid dst_addr width counter_addr dyn_addr index tail_offset child_size ss) /\
    abi_memory_frame ((w2n root_dst,LENGTH root_payload)::abi_allocation_windows (compiler_alloca_ids root_cs root_after)
      (abi_native_dynamic_array_next_state cs mid dst_addr width counter_addr dyn_addr index tail_offset child_size ss)) ss
      (abi_native_dynamic_array_next_state cs mid dst_addr width counter_addr dyn_addr index tail_offset child_size ss)
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`cs`, `mid`, `dst_addr`, `width`, `counter_addr`, `dyn_addr`, `index`, `tail_offset`, `child_size`, `ss`]
    strip_assume_tac abi_native_dynamic_array_next_frame >>
  `abi_native_cursor func root_cs root_after dyn_inst dyn_addr mid
    (abi_native_dynamic_array_next_state cs mid dst_addr width counter_addr dyn_addr index tail_offset child_size ss)` by
    (qspecl_then [`func`, `root_cs`, `root_after`, `dyn_inst`, `dyn_addr`, `mid`, `ss`,
       `abi_native_dynamic_array_next_state cs mid dst_addr width counter_addr dyn_addr index tail_offset child_size ss`]
       mp_tac abi_native_cursor_allocator_state >> impl_tac >- first_assum MATCH_ACCEPT_TAC >> simp[]) >>
  `abi_native_cursor func root_cs root_after index_inst counter_addr mid
    (abi_native_dynamic_array_next_state cs mid dst_addr width counter_addr dyn_addr index tail_offset child_size ss)` by
    (qspecl_then [`func`, `root_cs`, `root_after`, `index_inst`, `counter_addr`, `mid`, `ss`,
       `abi_native_dynamic_array_next_state cs mid dst_addr width counter_addr dyn_addr index tail_offset child_size ss`]
       mp_tac abi_native_cursor_allocator_state >> impl_tac >- first_assum MATCH_ACCEPT_TAC >> simp[]) >>
  rpt conj_tac >- first_assum MATCH_ACCEPT_TAC >- first_assum MATCH_ACCEPT_TAC >>
  irule abi_memory_frame_cover >>
  qexists_tac `[(w2n (dst_addr + 32w + n2w index * n2w width),32);(w2n dyn_addr,32);(w2n counter_addr,32)]` >>
  conj_tac >- (
    qspecl_then [`func`, `root_cs`, `root_after`, `dyn_inst`, `dyn_addr`, `index_inst`, `counter_addr`, `mid`,
      `abi_native_dynamic_array_next_state cs mid dst_addr width counter_addr dyn_addr index tail_offset child_size ss`,
      `root_dst`, `root_payload`, `w2n (dst_addr + 32w + n2w index * n2w width)`]
      mp_tac abi_native_cursor_loop_stores_cover >> impl_tac >- asm_simp_tac bool_ss [] >> simp_tac bool_ss []) >>
  first_assum MATCH_ACCEPT_TAC
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed owned dynamic array loop update frame: " ^ name)
  end) (DB.thms "abiNativeDynamicArrayUpdateFrame")

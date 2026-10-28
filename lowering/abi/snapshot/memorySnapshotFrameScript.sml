(* TOP-LEVEL: actual argument snapshots preserve all external state and
   every disjoint typed value. Both aggregate full-footprint copies and
   bytes/string rounded-live copies retain their exact allocation frame. *)
Theory memorySnapshotFrame
Ancestors
  bytesSnapshotMemory bytesSnapshotExec memoryValueSnapshot memoryValueFrame
  memoryValueDefs typedSArrayDynInvariant abiStateFrame abiBufferAllocationPath
  compileEnv valueEncoding venomState venomExecSemantics words arithmetic

Theorem memory_snapshot_allocated_state_context[simp]:
  !id var_base capacity ss.
    abi_state_context (memory_snapshot_allocated id var_base capacity ss) = abi_state_context ss
Proof
  rpt gen_tac >>
  mp_tac (Q.SPECL [`id`, `var_base`, `capacity`, `ss`] buffer_allocation_context) >>
  simp[abi_state_frame_def]
QED

Theorem memory_snapshot_result_allocator:
  !id var_base capacity src_addr ss.
    abi_state_frame ss (memory_snapshot_result id var_base capacity src_addr ss) /\
    (memory_snapshot_result id var_base capacity src_addr ss).vs_allocas =
      (memory_snapshot_alloc_frame id capacity ss).vs_allocas /\
    (memory_snapshot_result id var_base capacity src_addr ss).vs_alloca_next =
      (memory_snapshot_alloc_frame id capacity ss).vs_alloca_next
Proof
  rpt gen_tac >> Cases_on `capacity = 0` >>
  simp[memory_snapshot_result_def, abi_state_frame_def,
    mcopy_def, write_memory_with_expansion_def, buffer_allocation_context]
QED

Theorem bytes_snapshot_result_allocator:
  !id var_base capacity src_addr ss.
    abi_state_frame ss (bytes_snapshot_result id var_base capacity src_addr ss) /\
    (bytes_snapshot_result id var_base capacity src_addr ss).vs_allocas =
      (memory_snapshot_alloc_frame id capacity ss).vs_allocas /\
    (bytes_snapshot_result id var_base capacity src_addr ss).vs_alloca_next =
      (memory_snapshot_alloc_frame id capacity ss).vs_alloca_next
Proof
  simp[bytes_snapshot_result_def, LET_THM, abi_state_frame_def, update_var_def,
    mcopy_def, write_memory_with_expansion_def, buffer_allocation_context]
QED

Theorem memory_snapshot_result_copy_frame:
  !tv id var_base capacity src_addr ss.
    capacity <= type_memory_size tv ==>
    array_copy_frame tv 1 (w2n (memory_snapshot_addr id ss)) ss.vs_memory
      (memory_snapshot_result id var_base capacity src_addr ss).vs_memory
Proof
  rpt gen_tac >> DISCH_TAC >> Cases_on `capacity = 0`
  >- simp[memory_snapshot_result_def] >>
  asm_simp_tac (srw_ss()) [array_copy_frame_def, memory_snapshot_result_def] >>
  rpt gen_tac >> strip_tac >>
  irule mcopy_preserves_memory_value_rel >> simp[] >> decide_tac
QED

Theorem bytes_snapshot_result_copy_frame:
  !tenv ty tv v id var_base capacity src_addr ss.
    is_bytestring_type ty /\ evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\
    memory_value_rel tv v (w2n src_addr) ss.vs_memory /\ type_memory_size tv < dimword(:256) ==>
    array_copy_frame tv 1 (w2n (memory_snapshot_addr id ss)) ss.vs_memory
      (bytes_snapshot_result id var_base capacity src_addr ss).vs_memory
Proof
  rpt gen_tac >> strip_tac >> drule_all typed_memory_bytestring_view >> strip_tac >>
  `32 + ceil32 (LENGTH bs) < dimword(:256)` by decide_tac >>
  mp_tac (Q.SPECL [`id`, `var_base`, `capacity`, `src_addr`, `ss`, `LENGTH (bs:byte list)`]
    bytes_snapshot_result_natural_memory) >> impl_tac >- simp[] >> DISCH_TAC >>
  asm_simp_tac (srw_ss()) [array_copy_frame_def] >> rpt gen_tac >> strip_tac >>
  irule mcopy_preserves_memory_value_rel >> simp[] >> decide_tac
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed argument snapshot memory and external frames: " ^ name)
  end) (DB.thms "memorySnapshotFrame")

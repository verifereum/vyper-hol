(* TOP-LEVEL: actual parent/header stores fit the full array output and
   the parent instruction's recorded slot in the computed root profile. *)
Theory abiNativeArrayParentFrame
Ancestors
  abiNativeArrayFrames abiNativeCursor abiNativeCursorFrame abiMemoryFrameCover abiMemoryFrame abiAllocationWindows
  compileAllocaProvenance compileEnv venomState list words arithmetic

Theorem abi_native_array_parent_frame:
  !func root_cs root_after parent_inst parent_addr marker recorded dst_addr payload before after.
    abi_native_cursor func root_cs root_after parent_inst parent_addr marker recorded /\ 32 <= LENGTH (payload:word8 list) /\
    abi_memory_frame [(w2n parent_addr,32);(w2n (dst_addr:bytes32),32)] before after ==>
    abi_memory_frame ((w2n dst_addr,LENGTH payload)::
      abi_allocation_windows (compiler_alloca_ids root_cs root_after) recorded) before after
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`func`, `root_cs`, `root_after`, `parent_inst`, `parent_addr`, `marker`, `recorded`,
    `dst_addr`, `payload`, `w2n dst_addr`] mp_tac abi_native_cursor_stores_cover >>
  impl_tac >- asm_simp_tac (srw_ss()) [] >> DISCH_TAC >>
  `abi_memory_frame [(w2n dst_addr,32);(w2n parent_addr,32)] before after` by
    (qspecl_then [`[(w2n dst_addr,32);(w2n parent_addr,32)]`, `before`, `after`]
       mp_tac abi_memory_frame_reverse >> simp[]) >>
  irule abi_memory_frame_cover >> qexists_tac `[(w2n dst_addr,32);(w2n parent_addr,32)]` >>
  conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed native array parent output/profile frame: " ^ name)
  end) (DB.thms "abiNativeArrayParentFrame")

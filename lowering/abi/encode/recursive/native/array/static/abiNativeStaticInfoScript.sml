(* TOP-LEVEL: the real static-loop dispatcher copies exactly its declared
   static width, including the zero-width fallback. Source strides are
   independent of this output width. *)
Theory abiNativeStaticInfo
Ancestors
  abiMemoryEncoding abiMemoryEncodingCases abiStaticLoopBody abiStaticLoopMemory abiMemoryFrame
  memoryValueAbiArray memoryReadProps valueEncoding compileEnv venomState list words arithmetic

Theorem abi_native_static_info_frame:
  !info dst_addr src_addr ss.
    abi_static_encoder_size info < dimword (:256) ==>
    abi_memory_frame [(w2n dst_addr,abi_static_encoder_size info)] ss
      (static_info_memory info dst_addr src_addr ss)
Proof
  Cases_on `info` >> simp_tac (srw_ss()) [abi_static_encoder_size_def, static_info_memory_def,
    abi_memory_frame_mstore] >> rpt strip_tac >> fs[w2n_n2w, abi_memory_frame_mcopy]
QED

Theorem abi_native_static_info_read:
  !info dst_addr src_addr ss.
    abi_static_encoder_size info < dimword (:256) ==>
    read_memory (w2n dst_addr) (abi_static_encoder_size info) (static_info_memory info dst_addr src_addr ss) =
      read_memory (w2n src_addr) (abi_static_encoder_size info) ss
Proof
  Cases_on `info`
  >| [rpt gen_tac >> DISCH_TAC >> irule static_info_memory_read_self >> simp[abi_static_encoder_size_def],
      simp[abi_static_encoder_size_def, static_info_memory_def, read_memory_def],
      rpt gen_tac >> simp_tac bool_ss [abi_static_encoder_size_def] >> DISCH_TAC >>
        irule static_info_memory_read_self >> simp[],
      simp[abi_static_encoder_size_def, static_info_memory_def, read_memory_def],
      simp[abi_static_encoder_size_def, static_info_memory_def, read_memory_def]]
QED

Theorem abi_memory_static_payload:
  !info source span mem payload.
    abi_memory_encoding info source span mem payload /\ LENGTH payload = abi_static_encoder_size info ==>
    mem_bytes_at source (LENGTH payload) mem = payload
Proof
  Cases_on `info`
  >| [simp[abi_memory_word_cases, abi_static_encoder_size_def, mem_bytes_at_word],
      simp[abi_static_encoder_size_def, LENGTH_NIL] >> rpt strip_tac >> gvs[mem_bytes_at_def],
      simp[abi_memory_copy_cases, abi_static_encoder_size_def],
      simp[abi_static_encoder_size_def, LENGTH_NIL] >> rpt strip_tac >> gvs[mem_bytes_at_def],
      simp[abi_static_encoder_size_def, LENGTH_NIL] >> rpt strip_tac >> gvs[mem_bytes_at_def]]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual static dispatcher memory contract: " ^ name)
  end) (DB.thms "abiNativeStaticInfo")

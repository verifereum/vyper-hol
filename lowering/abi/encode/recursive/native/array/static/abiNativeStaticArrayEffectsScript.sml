(* TOP-LEVEL: the real static-loop memory effect writes one packed field
   and the index counter. Allocation records and external state remain
   unchanged, including for the zero-byte dispatcher fallback. *)
Theory abiNativeStaticArrayEffects
Ancestors
  abiNativeStaticInfo abiStaticLoopBody abiStaticLoopRun abiMemoryEncoding abiMemoryFrame
  abiAllocatorState abiStateFrame venomState list words arithmetic

Theorem abi_native_static_body_frame:
  !info dst_addr src_addr width stride counter_addr ss.
    abi_static_encoder_size info < dimword (:256) ==>
    abi_memory_frame
      [(w2n (dst_addr + 32w + mload (w2n counter_addr) ss * n2w width),abi_static_encoder_size info);
       (w2n counter_addr,32)] ss
      (abi_static_loop_body_memory info dst_addr src_addr width stride counter_addr ss)
Proof
  rpt gen_tac >> DISCH_TAC >> simp_tac bool_ss [abi_static_loop_body_memory_def, LET_THM] >>
  qspecl_then [`info`, `dst_addr + 32w + mload (w2n counter_addr) ss * n2w width`,
    `src_addr + 32w + mload (w2n counter_addr) ss * n2w stride`, `ss`]
    mp_tac abi_native_static_info_frame >> impl_tac >- first_assum MATCH_ACCEPT_TAC >> DISCH_TAC >>
  qspecl_then [`w2n counter_addr`, `mload (w2n counter_addr) ss + 1w`,
    `static_info_memory info (dst_addr + 32w + mload (w2n counter_addr) ss * n2w width)
      (src_addr + 32w + mload (w2n counter_addr) ss * n2w stride) ss`]
    strip_assume_tac abi_memory_frame_mstore >>
  qspecl_then [`[(w2n (dst_addr + 32w + mload (w2n counter_addr) ss * n2w width),abi_static_encoder_size info)]`,
    `[(w2n counter_addr,32)]`, `ss`,
    `static_info_memory info (dst_addr + 32w + mload (w2n counter_addr) ss * n2w width)
      (src_addr + 32w + mload (w2n counter_addr) ss * n2w stride) ss`,
    `mstore (w2n counter_addr) (mload (w2n counter_addr) ss + 1w)
      (static_info_memory info (dst_addr + 32w + mload (w2n counter_addr) ss * n2w width)
        (src_addr + 32w + mload (w2n counter_addr) ss * n2w stride) ss)`]
    mp_tac abi_memory_frame_trans >> impl_tac >- asm_simp_tac bool_ss [] >> simp[]
QED

Theorem abi_native_static_effect_frame:
  !info dst_addr src_addr width stride counter_addr labels ss.
    abi_static_encoder_size info < dimword (:256) ==>
    abi_memory_frame
      [(w2n (dst_addr + 32w + mload (w2n counter_addr) ss * n2w width),abi_static_encoder_size info);
       (w2n counter_addr,32)] ss
      (abi_static_loop_effect info dst_addr src_addr width stride counter_addr labels ss)
Proof
  rpt gen_tac >> DISCH_TAC >> drule abi_native_static_body_frame >>
  disch_then (qspecl_then [`dst_addr`, `src_addr`, `width`, `stride`, `counter_addr`, `ss`] mp_tac) >>
  simp[abi_memory_frame_def, abi_static_loop_effect_def, memory_reads_jump_to]
QED

Theorem abi_native_static_effect_context:
  !info dst_addr src_addr width stride counter_addr labels ss.
    abi_allocator_state (abi_static_loop_effect info dst_addr src_addr width stride counter_addr labels ss) =
      abi_allocator_state ss /\
    abi_state_frame ss (abi_static_loop_effect info dst_addr src_addr width stride counter_addr labels ss)
Proof
  Cases_on `info` >> simp[abi_static_loop_effect_def, abi_static_loop_body_memory_def,
    static_info_memory_def, LET_THM, abi_state_frame_def]
QED

Theorem abi_native_static_effects_context:
  !iterations info dst_addr root_addr width stride counter_addr labels ss.
    abi_allocator_state
      (FUNPOW (abi_static_loop_effect info dst_addr root_addr width stride counter_addr labels) iterations ss) =
      abi_allocator_state ss /\
    abi_state_frame ss
      (FUNPOW (abi_static_loop_effect info dst_addr root_addr width stride counter_addr labels) iterations ss)
Proof
  Induct_on `iterations` >- simp[] >> rpt gen_tac >>
  first_x_assum (qspecl_then [`info`, `dst_addr`, `root_addr`, `width`, `stride`, `counter_addr`, `labels`, `ss`] mp_tac) >>
  simp_tac bool_ss [abi_state_frame_def] >> strip_tac >>
  simp[FUNPOW_SUC, abi_state_frame_def, REWRITE_RULE [abi_state_frame_def] abi_native_static_effect_context]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual static array memory effect resources: " ^ name)
  end) (DB.thms "abiNativeStaticArrayEffects")

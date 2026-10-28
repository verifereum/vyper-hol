(* TOP-LEVEL: the real static iteration writes the selected source bytes
   to the packed destination and preserves them through its counter store. *)
Theory abiNativeStaticArrayPayload
Ancestors
  abiNativeStaticInfo abiStaticLoopBody abiStaticLoopRun abiMemoryEncoding abiMemoryFrame
  compileEnv venomState list words arithmetic

Theorem abi_native_static_array_effect_payload:
  !info dst_addr root_addr stride counter_addr labels payload ss.
    abi_static_encoder_size info < dimword (:256) /\
    read_memory (w2n (root_addr + 32w + mload (w2n counter_addr) ss * n2w stride))
      (abi_static_encoder_size info) ss = payload /\
    abi_window_separated
      (w2n (dst_addr + 32w + mload (w2n counter_addr) ss * n2w (abi_static_encoder_size info)))
      (abi_static_encoder_size info) (w2n counter_addr) 32 ==>
    read_memory (w2n (dst_addr + 32w + mload (w2n counter_addr) ss * n2w (abi_static_encoder_size info)))
      (abi_static_encoder_size info)
      (abi_static_loop_effect info dst_addr root_addr (abi_static_encoder_size info) stride counter_addr labels ss) = payload
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`info`, `dst_addr + 32w + mload (w2n counter_addr) ss * n2w (abi_static_encoder_size info)`,
    `root_addr + 32w + mload (w2n counter_addr) ss * n2w stride`, `ss`]
    mp_tac abi_native_static_info_read >> impl_tac >- first_assum MATCH_ACCEPT_TAC >> DISCH_TAC >>
  qspecl_then [`w2n counter_addr`, `mload (w2n counter_addr) ss + 1w`,
    `static_info_memory info
      (dst_addr + 32w + mload (w2n counter_addr) ss * n2w (abi_static_encoder_size info))
      (root_addr + 32w + mload (w2n counter_addr) ss * n2w stride) ss`]
    strip_assume_tac abi_memory_frame_mstore >>
  qspecl_then [`[(w2n counter_addr,32)]`,
    `static_info_memory info
      (dst_addr + 32w + mload (w2n counter_addr) ss * n2w (abi_static_encoder_size info))
      (root_addr + 32w + mload (w2n counter_addr) ss * n2w stride) ss`,
    `mstore (w2n counter_addr) (mload (w2n counter_addr) ss + 1w)
      (static_info_memory info
        (dst_addr + 32w + mload (w2n counter_addr) ss * n2w (abi_static_encoder_size info))
        (root_addr + 32w + mload (w2n counter_addr) ss * n2w stride) ss)`,
    `w2n (dst_addr + 32w + mload (w2n counter_addr) ss * n2w (abi_static_encoder_size info))`,
    `abi_static_encoder_size info`] mp_tac abi_memory_frame_read >>
  impl_tac >- simp[] >>
  simp[abi_static_loop_effect_def, abi_static_loop_body_memory_def, LET_THM, memory_reads_jump_to]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual static iteration payload write: " ^ name)
  end) (DB.thms "abiNativeStaticArrayPayload")

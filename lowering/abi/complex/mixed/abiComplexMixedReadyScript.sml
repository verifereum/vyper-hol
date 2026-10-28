(* TOP-LEVEL: actual aggregate counter setup prepares a static/bytes field
   traversal. Its premises observe both sources in the original state. *)
Theory abiComplexMixedReady
Ancestors
  abiComplexMixedMemory abiStaticBytesReady abiStaticFieldStep abiComplexEntry abiComplexMemory
  abiStaticLoopEntry abiStaticLoopCode abiMemoryFrame abiFieldMemory abiFieldLayoutDefs
  abiBytestringCorrect abiEncoderPathProps instIdxIndep contractABI compileEnv venomState list pair words arithmetic

Definition abi_complex_mixed_pre_def:
  abi_complex_mixed_pre id dst_addr src_addr mem_size payload bs ss <=>
    read_memory (w2n src_addr) (LENGTH payload) ss = payload /\
    bytestring_abi_pre (dst_addr + n2w (LENGTH payload + 32)) (src_addr + n2w mem_size) bs ss /\
    abi_window_separated (w2n src_addr) (LENGTH payload)
      (w2n (abi_static_loop_counter_addr id ss)) 32 /\
    regions_disjoint (w2n (src_addr + n2w mem_size)) (32 + LENGTH bs)
      (w2n (abi_static_loop_counter_addr id ss)) 32 /\
    abi_window_separated (w2n (src_addr + n2w mem_size)) (32 + LENGTH bs) (w2n dst_addr) (LENGTH payload) /\
    w2n dst_addr + LENGTH payload + 32 + LENGTH (enc (Bytes NONE) (contractABI$BytesV bs)) < dimword(:256) /\
    regions_disjoint (w2n dst_addr)
      (LENGTH payload + 32 + LENGTH (enc (Bytes NONE) (contractABI$BytesV bs)))
      (w2n (abi_static_loop_counter_addr id ss)) 32
End

Theorem abi_complex_prefix_memory_frame:
  !id var_base head_size ss index.
    abi_memory_frame [(w2n (abi_static_loop_counter_addr id ss),32)] ss
      ((abi_complex_prefix_state id var_base head_size ss) with vs_inst_idx := index)
Proof
  rpt gen_tac >>
  mp_tac (Q.SPECL [`w2n (abi_static_loop_counter_addr id ss)`, `n2w head_size : bytes32`,
    `update_var (compiler_var_name var_base 0) (abi_static_loop_counter_addr id ss)
      (abi_static_loop_alloc_frame id ss)`] abi_memory_frame_mstore) >>
  simp[abi_complex_prefix_state_def, abi_memory_frame_def, read_memory_def, update_var_def]
QED

Theorem abi_complex_mixed_prefix_pre:
  !id var_base dst_addr src_addr mem_size payload bs ss index.
    abi_complex_mixed_pre id dst_addr src_addr mem_size payload bs ss ==>
    abi_static_bytes_pre [] (LENGTH payload + 32) dst_addr (abi_static_loop_counter_addr id ss)
      src_addr 0 mem_size payload bs
      ((abi_complex_prefix_state id var_base (LENGTH payload + 32) ss) with vs_inst_idx := index)
Proof
  rpt gen_tac >> DISCH_TAC >>
  qpat_x_assum `abi_complex_mixed_pre _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_complex_mixed_pre_def]) >>
  mp_tac (Q.SPECL [`dst_addr`, `abi_static_loop_counter_addr id ss`, `payload`, `bs`]
    abi_complex_mixed_regions) >> impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> strip_tac >>
  qabbrev_tac `prefixed = (abi_complex_prefix_state id var_base (LENGTH payload + 32) ss)
    with vs_inst_idx := index` >>
  `abi_memory_frame [(w2n (abi_static_loop_counter_addr id ss),32)] ss prefixed` by
    simp[Abbr`prefixed`, abi_complex_prefix_memory_frame] >>
  `read_memory (w2n src_addr) (LENGTH payload) prefixed = payload` by
    (mp_tac (Q.SPECL [`[(w2n (abi_static_loop_counter_addr id ss),32)]`, `ss`, `prefixed`,
      `w2n (src_addr:bytes32)`, `LENGTH (payload:word8 list)`] abi_memory_frame_read) >>
     impl_tac >- simp[] >> simp[]) >>
  `bytestring_abi_pre (dst_addr + n2w (LENGTH payload + 32)) (src_addr + n2w mem_size) bs prefixed` by
    (mp_tac (Q.SPECL [`dst_addr + n2w (LENGTH (payload:word8 list) + 32)`, `src_addr + n2w mem_size`,
       `bs`, `ss`, `prefixed`] bytestring_abi_pre_read_frame) >>
     impl_tac >- (irule abi_memory_frame_read >>
       qexists_tac `[(w2n (abi_static_loop_counter_addr id ss),32)]` >> simp[abi_window_separated_def]) >>
     simp[]) >>
  `abi_static_field_pre [] (LENGTH payload + 32) dst_addr (abi_static_loop_counter_addr id ss)
      src_addr payload prefixed` by
    fs[abi_static_field_pre_def, abi_field_head_size_def, abi_window_separated_def, WORD_ADD_0] >>
  asm_simp_tac (srw_ss()) [abi_static_bytes_pre_def, Abbr`prefixed`, mload_inst_idx,
    abi_complex_prefix_counter, abi_field_head_size_def, WORD_ADD_0]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual mixed ABI aggregate source preparation: " ^ name)
  end) (DB.thms "abiComplexMixedReady")

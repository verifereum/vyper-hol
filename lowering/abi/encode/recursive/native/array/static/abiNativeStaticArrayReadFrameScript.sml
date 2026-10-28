(* TOP-LEVEL: an iteration's concrete frame preserves the full raw source
   relation and both array length headers. Source suffixes are observations
   of the enclosing source window, rather than additional alias premises. *)
Theory abiNativeStaticArrayReadFrame
Ancestors
  abiNativeStaticArrayState abiMemoryEncodingFrame abiMemoryEncoding abiMemoryFrame
  memoryReadProps valueEncoding valueEncodingProofs compileEnv venomState list words arithmetic

Theorem abi_native_static_array_source_preserved:
  !info width stride fields dst_addr root_addr counter_addr source_capacity index writes ss out.
    abi_native_static_array_data info width stride fields dst_addr root_addr counter_addr source_capacity index ss /\
    abi_memory_frame writes ss out /\
    EVERY (\(b,n). abi_window_separated (w2n root_addr) source_capacity b n) writes /\
    EVERY (\(b,n). abi_window_separated (w2n dst_addr) 32 b n) writes ==>
    abi_memory_fields (REPLICATE (LENGTH fields) (info,width,stride,F))
      (w2n root_addr + 32) (source_capacity - 32) out.vs_memory fields /\
    mload (w2n root_addr) out = n2w (LENGTH fields) /\ mload (w2n dst_addr) out = n2w (LENGTH fields)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_assum `abi_native_static_array_data _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_static_array_data_def]) >>
  qspecl_then [`writes`, `ss`, `out`, `w2n root_addr`, `source_capacity`] mp_tac abi_memory_frame_read >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  `mem_bytes_at (w2n root_addr) source_capacity ss.vs_memory =
    mem_bytes_at (w2n root_addr) source_capacity out.vs_memory` by fs[read_memory_eq_mem_bytes_at] >>
  qspecl_then [`w2n root_addr`, `source_capacity`, `ss.vs_memory`, `out.vs_memory`]
    mp_tac abi_memory_window_header >> impl_tac >- asm_simp_tac bool_ss [] >> DISCH_TAC >>
  `mload (w2n root_addr) out = n2w (LENGTH fields)` by fs[mem_word_at_eq_mload_proof] >>
  qspecl_then [`w2n root_addr`, `source_capacity`, `32`, `ss.vs_memory`, `out.vs_memory`]
    mp_tac abi_memory_window_suffix >> impl_tac >- asm_simp_tac bool_ss [] >> DISCH_TAC >>
  drule (CONJUNCT2 abi_memory_encoding_frame) >> disch_then (qspec_then `out.vs_memory` mp_tac) >>
  impl_tac >- (sym_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  qspecl_then [`writes`, `ss`, `out`, `w2n dst_addr`] mp_tac abi_memory_frame_mload >>
  impl_tac >- asm_simp_tac bool_ss [] >> DISCH_TAC >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed raw static iteration source/header reads: " ^ name)
  end) (DB.thms "abiNativeStaticArrayReadFrame")

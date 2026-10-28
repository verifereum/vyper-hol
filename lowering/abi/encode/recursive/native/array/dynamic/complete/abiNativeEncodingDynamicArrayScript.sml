(* TOP-LEVEL: dynamic-child array case of native semantic induction. The
   fields assertion supplies arbitrary recursive child encoders, while
   execution needs only agreement with the original bounded source. *)
Theory abiNativeEncodingDynamicArray
Ancestors
  abiNativeDynamicArrayComplete abiNativeEncodingDefs abiNativeFields abiMemoryEncodingFrame abiMemoryEncoding
  abiFieldLayoutDefs valueEncoding valueEncodingProofs compileEnv venomMemDefs venomState list words

Theorem abi_native_dynamic_array:
  !info width stride fields source span reference.
    32 <= span /\ LENGTH fields < dimword (:256) /\ mem_word_at source reference = (n2w (LENGTH fields):bytes32) /\
    abi_memory_fields (REPLICATE (LENGTH fields) (info,width,stride,T)) (source + 32) (span - 32) reference fields /\
    abi_native_fields (REPLICATE (LENGTH fields) (info,width,stride,T)) (source + 32) reference fields ==>
    abi_native_encoder (AbiDynArray info width stride T) source span reference
      (word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields)
Proof
  rpt gen_tac >> strip_tac >> PURE_REWRITE_TAC [abi_native_encoder_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `w2n src_addr = source` (SUBST_ALL_TAC o SYM) >>
  qspecl_then [`w2n src_addr`, `span`, `reference`, `ss.vs_memory`] mp_tac abi_memory_window_header >>
  impl_tac >- asm_simp_tac bool_ss [] >> DISCH_TAC >>
  qspecl_then [`w2n src_addr`, `span`, `32`, `reference`, `ss.vs_memory`] mp_tac abi_memory_window_suffix >>
  impl_tac >- asm_simp_tac bool_ss [] >> DISCH_TAC >>
  drule (CONJUNCT2 abi_memory_encoding_frame) >> disch_then (qspec_then `ss.vs_memory` mp_tac) >>
  impl_tac >- (sym_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  `mload (w2n src_addr) ss = n2w (LENGTH fields)` by fs[mem_word_at_eq_mload_proof] >>
  qspecl_then [`ctx`, `func`, `dst`, `src`, `info`, `width`, `stride`, `fields`, `span`, `cs`, `ret`, `cs'`, `ss`,
    `dst_addr`, `src_addr`, `source_id`, `target_id`, `reference`] mp_tac compile_abi_native_dynamic_array >>
  impl_tac >- asm_simp_tac bool_ss [] >> simp_tac bool_ss []
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed full native dynamic-child array semantic induction case: " ^ name)
  end) (DB.thms "abiNativeEncodingDynamicArray")

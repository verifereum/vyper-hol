(* TOP-LEVEL: complete static-array case of native semantic induction.
   The original source memory is independent of the execution state; only
   its bounded source observation is required to agree initially. *)
Theory abiNativeEncodingStaticArray
Ancestors
  abiNativeStaticArrayComplete abiNativeEncodingDefs abiMemoryEncodingFrame abiMemoryEncodingCases abiMemoryEncoding
  valueEncodingProofs compileEnv venomState list words

Theorem abi_native_static_array:
  !info width stride source span reference payload.
    abi_memory_encoding (AbiDynArray info width stride F) source span reference payload ==>
    abi_native_encoder (AbiDynArray info width stride F) source span reference payload
Proof
  rpt gen_tac >> DISCH_TAC >> PURE_REWRITE_TAC [abi_native_encoder_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `w2n src_addr = source` (SUBST_ALL_TAC o SYM) >>
  drule (CONJUNCT1 abi_memory_encoding_frame) >> disch_then (qspec_then `ss.vs_memory` mp_tac) >>
  impl_tac >- first_assum MATCH_ACCEPT_TAC >> DISCH_TAC >>
  qpat_x_assum `abi_memory_encoding _ _ _ ss.vs_memory _`
    (mp_tac o SIMP_RULE (srw_ss()) [abi_memory_array_cases]) >>
  disch_then (qx_choose_then `fields` strip_assume_tac) >> gvs[mem_word_at_eq_mload_proof] >>
  qspecl_then [`ctx`, `func`, `dst`, `src`, `info`, `stride`, `fields`, `span`, `cs`, `ret`, `cs'`, `ss`,
    `dst_addr`, `src_addr`, `source_id`, `target_id`] mp_tac compile_abi_native_static_array >>
  impl_tac >- asm_simp_tac bool_ss [] >> simp_tac bool_ss []
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed full native static array semantic induction case: " ^ name)
  end) (DB.thms "abiNativeEncodingStaticArray")

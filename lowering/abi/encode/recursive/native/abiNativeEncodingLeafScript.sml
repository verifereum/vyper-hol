(* TOP-LEVEL: actual native leaf executions satisfy the local allocation
   profile assertion. Source observations may come from an earlier memory;
   the source-window equality discharges the execution relation internally. *)
Theory abiNativeEncodingLeaf
Ancestors
  abiNativeEncodingDefs abiMemoryLeafRun abiMemoryBytesRun abiMemoryEncodingFrame
  abiMemoryEncoding abiEncoder venomState valueEncoding list words arithmetic

Theorem abi_native_memory_word:
  !source span reference payload.
    abi_memory_encoding AbiPrimWord source span reference payload ==>
    abi_native_encoder AbiPrimWord source span reference payload
Proof
  rpt gen_tac >> strip_tac >> PURE_REWRITE_TAC [abi_native_encoder_def] >>
  rpt gen_tac >> disch_then (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
  drule (CONJUNCT1 abi_memory_encoding_frame) >>
  disch_then (qspec_then `ss.vs_memory` mp_tac) >> impl_tac >- simp[] >>
  DISCH_TAC >> gvs[] >> drule_all compile_abi_memory_word >>
  disch_then (qspec_then `ctx` (qx_choose_then `out` strip_assume_tac)) >> qexists_tac `out` >>
  drule_all abi_native_encoding_allocation_free >> simp[]
QED

Theorem abi_native_memory_copy:
  !n source span reference payload.
    abi_memory_encoding (AbiCopy n) source span reference payload ==>
    abi_native_encoder (AbiCopy n) source span reference payload
Proof
  rpt gen_tac >> strip_tac >> PURE_REWRITE_TAC [abi_native_encoder_def] >>
  rpt gen_tac >> disch_then (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
  drule (CONJUNCT1 abi_memory_encoding_frame) >>
  disch_then (qspec_then `ss.vs_memory` mp_tac) >> impl_tac >- simp[] >>
  DISCH_TAC >> gvs[] >> drule abi_native_memory_bounds >> strip_tac >>
  drule_all compile_abi_memory_copy >>
  disch_then (qspec_then `ctx` (qx_choose_then `out` strip_assume_tac)) >> qexists_tac `out` >>
  drule_all abi_native_encoding_allocation_free >> simp[]
QED

Theorem abi_native_memory_empty:
  !source span reference payload.
    abi_memory_encoding (AbiComplex []) source span reference payload ==>
    abi_native_encoder (AbiComplex []) source span reference payload
Proof
  rpt gen_tac >> strip_tac >> PURE_REWRITE_TAC [abi_native_encoder_def] >>
  rpt gen_tac >> disch_then (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
  drule (CONJUNCT1 abi_memory_encoding_frame) >>
  disch_then (qspec_then `ss.vs_memory` mp_tac) >> impl_tac >- simp[] >>
  DISCH_TAC >> gvs[] >>
  qspecl_then [`ctx`, `func`, `dst`, `src`, `span`, `payload`, `cs`, `ret`, `cs'`,
    `ss`, `dst_addr`, `src_addr`] mp_tac compile_abi_memory_empty >>
  impl_tac >- simp[] >>
  disch_then (qx_choose_then `out` strip_assume_tac) >> qexists_tac `out` >>
  drule_all abi_native_encoding_allocation_free >> simp[]
QED

Theorem abi_native_memory_bytes:
  !cap source span reference payload.
    abi_memory_encoding (AbiBytestring cap) source span reference payload ==>
    abi_native_encoder (AbiBytestring cap) source span reference payload
Proof
  rpt gen_tac >> strip_tac >> PURE_REWRITE_TAC [abi_native_encoder_def] >>
  rpt gen_tac >> disch_then (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
  drule (CONJUNCT1 abi_memory_encoding_frame) >>
  disch_then (qspec_then `ss.vs_memory` mp_tac) >> impl_tac >- simp[] >>
  DISCH_TAC >> gvs[] >> drule abi_native_memory_bounds >> strip_tac >>
  drule_all compile_abi_memory_bytes >>
  disch_then (qspec_then `ctx` (qx_choose_then `out` strip_assume_tac)) >> qexists_tac `out` >>
  drule_all abi_native_encoding_allocation_free >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed native ABI leaf execution: " ^ name)
  end) (DB.thms "abiNativeEncodingLeaf")

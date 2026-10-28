(* TOP-LEVEL: the all-static complex case of native semantic induction.
   All field executions and their frames are derived from the semantic
   child assertions, including empty aggregates and arbitrary nested info. *)
Theory abiNativeStaticComplex
Ancestors
  abiNativeStaticRun abiNativeStaticState abiNativeTraversal abiNativeFields abiNativeEncodingDefs
  abiMemoryStaticComplexRun abiMemoryStaticFieldsState abiMemoryFieldsState abiMemoryEncodingFrame
  abiMemoryEncoding abiMemoryLeafRun abiFieldOperands abiFieldLayoutDefs
  compileIdFlow compileEnv venomState valueEncoding list words arithmetic

Theorem abi_native_complex_static:
  !entries source span reference full.
    ~EXISTS (\(_,_,_,flag). flag) entries /\
    abi_memory_fields entries source span reference full /\
    abi_native_fields entries source reference full ==>
    abi_native_encoder (AbiComplex entries) source span reference
      (abi_field_bytes (abi_field_head_size full) full)
Proof
  rpt gen_tac >> disch_then (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
  PURE_REWRITE_TAC [abi_native_encoder_def] >>
  rpt gen_tac >> disch_then (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
  qpat_x_assum `w2n src_addr = source` (SUBST_ALL_TAC o SYM) >>
  drule (CONJUNCT2 abi_memory_encoding_frame) >>
  disch_then (qspec_then `ss.vs_memory` mp_tac) >>
  impl_tac >- first_assum MATCH_ACCEPT_TAC >> DISCH_TAC >>
  drule abi_native_memory_bounds >> strip_tac >>
  qspecl_then [`dst`, `src`, `entries`, `cs`, `ret`, `cs'`] mp_tac compile_abi_complex_static_split >>
  impl_tac >- first_assum MATCH_ACCEPT_TAC >> asm_simp_tac bool_ss [] >>
  disch_then (CONJUNCTS_THEN2 ASSUME_TAC (qx_choose_then `fields_ret` ASSUME_TAC)) >>
  `compiler_id_history cs` by
    (qpat_assum `abi_native_memory_ready _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_native_memory_ready_def]) >>
     first_assum MATCH_ACCEPT_TAC) >>
  `abi_native_traversal ctx func cs cs' dst_addr
    (abi_field_bytes (abi_field_head_size full) full) ss cs ss` by
    (irule abi_native_traversal_initial >> first_assum MATCH_ACCEPT_TAC) >>
  `abi_memory_fields_operands dst src (Lit 0w) dst_addr src_addr 0w cs ss` by
    fs[abi_memory_fields_operands_def, abi_operand_before_def, eval_operand_def] >>
  drule_all abi_native_static_initial >> DISCH_TAC >>
  drule_all abi_native_static_traversal >>
  disch_then (qx_choose_then `out` strip_assume_tac) >>
  qpat_assum `abi_native_static_state _ _ _ _ _ _ _ [] _ _ _ _`
    (mp_tac o MATCH_MP abi_native_static_memory_state) >> DISCH_TAC >>
  qpat_assum `abi_native_traversal _ _ _ _ _ _ _ _ out`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_traversal_def]) >>
  drule_all abi_memory_static_complex_result >> DISCH_TAC >>
  qpat_assum `ret = _` (fn th =>
    qpat_x_assum `abi_encoding_result _ _ _ _ _ _ _ _ _ _`
      (ASSUME_TAC o PURE_REWRITE_RULE [th]) >> PURE_REWRITE_TAC [th]) >>
  qexists_tac `out` >> PURE_REWRITE_TAC [abi_native_encoding_result_def] >>
  conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed native static complex induction case: " ^ name)
  end) (DB.thms "abiNativeStaticComplex")

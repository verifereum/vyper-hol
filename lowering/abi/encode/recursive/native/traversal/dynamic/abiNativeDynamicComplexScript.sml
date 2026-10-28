(* TOP-LEVEL: the dynamic complex case of native semantic induction.
   The actual cursor prefix, mixed recursive traversal and final length
   load are all executed from semantic child assertions and root resources. *)
Theory abiNativeDynamicComplex
Ancestors
  abiNativeComplexPrefixFields abiNativeComplexPrefixCode abiNativeComplexPrefixState abiNativeComplexFinish
  abiNativeDynamicRun abiNativeFields abiNativeEncodingDefs abiNativeTraversal abiNativeCursor abiNativeDynamicState
  abiMemoryEncodingFrame abiMemoryEncoding abiFieldLayoutDefs abiComplexCode abiComplexStructure
  compileIdFlow compileEnv fragExec venomState valueEncoding list words arithmetic

Theorem abi_native_complex_dynamic:
  !entries source span reference full.
    EXISTS (\(_,_,_,flag). flag) entries /\ abi_memory_fields entries source span reference full /\
    abi_native_fields entries source reference full ==>
    abi_native_encoder (AbiComplex entries) source span reference
      (abi_field_bytes (abi_field_head_size full) full)
Proof
  rpt gen_tac >> strip_tac >> PURE_REWRITE_TAC [abi_native_encoder_def] >>
  rpt gen_tac >> strip_tac >> qpat_x_assum `w2n src_addr = source` (SUBST_ALL_TAC o SYM) >>
  drule (CONJUNCT2 abi_memory_encoding_frame) >>
  disch_then (qspec_then `ss.vs_memory` mp_tac) >> impl_tac >- first_assum MATCH_ACCEPT_TAC >> DISCH_TAC >>
  drule abi_memory_fields_head_size >> DISCH_TAC >>
  qspecl_then [`dst`, `src`, `entries`, `cs`, `ret`, `cs'`] mp_tac compile_abi_complex_dynamic_split >>
  impl_tac >- first_assum MATCH_ACCEPT_TAC >>
  qpat_assum `abi_field_head_size full = SUM _` (fn th => PURE_REWRITE_TAC [GSYM th]) >>
  asm_simp_tac (srw_ss()) [compile_abi_complex_prefix_result] >>
  disch_then (qx_choose_then `fields_ret` (qx_choose_then `mid` strip_assume_tac)) >>
  qpat_x_assum `abi_field_head_size full = SUM _` (fn th =>
    RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM th]) >> PURE_REWRITE_TAC [GSYM th]) >>
  drule_all abi_complex_traversal_contains >> strip_tac >>
  `cs_extends mid cs'` by (drule_all abi_complex_length_extends >> simp[]) >>
  `cs_extends (abi_complex_prefix_cut (abi_field_head_size full) cs) mid` by
    (drule_all compile_abi_fields_extends >> simp[]) >>
  `cs_extends (abi_complex_prefix_cut (abi_field_head_size full) cs) cs'` by
    (irule cs_extends_trans >> qexists_tac `mid` >> simp[]) >>
  `alloca_inv ss` by fs[abi_native_memory_ready_def] >>
  drule_all abi_native_complex_entry_fields >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all abi_native_dynamic_traversal >> disch_then (qx_choose_then `fields_out` strip_assume_tac) >>
  drule_all abi_native_complex_finish >> simp_tac bool_ss []
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed native dynamic complex induction case: " ^ name)
  end) (DB.thms "abiNativeDynamicComplex")

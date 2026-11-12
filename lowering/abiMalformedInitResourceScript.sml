(* Full allocation-backed resources for the dynamic-array initializer. *)
Theory abiMalformedInitResource
Ancestors
  abiMalformedTraversal abiMalformedBulkIntegration abiMalformedContainmentProbe
  abiMalformedRecursiveInterface abiMalformedBulkArray
  abiDecoderArrayInitReentry abiDecoderArrayLoopInit abiDecoderIndexInit
  abiDecoderReentryAddress abiDecoderArrayHeader abiMalformedConstructorContract
  exprSimAlloc exprLoweringProps emitHelperProps emitHelper compileEnv context
  venomExecSemantics venomState venomInst venomMemDefs venomMemProps
  finite_map pred_set words list arithmetic

Theorem abi_malformed_alloc_registers:
  compile_alloc_buffer 32 st = (buf,en) /\
  run_inst_seq (emitted_insts st en) s = OK t /\
  eval_operand buf.buf_operand t = SOME w ==>
  t.vs_vars = s.vs_vars |+ (STRING #"%" (toString st.cs_next_var),w) /\
  t.vs_labels = s.vs_labels /\ s.vs_alloca_next <= t.vs_alloca_next
Proof
  simp[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  drule emitted_insts_emit_op >> strip_tac >>
  qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
  simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_alloca_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[update_var_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem abi_malformed_index_resource:
  abi_decode_index_init st = (ip,en) /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv st /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func) /\
  st.cs_next_id IN sites /\ en.cs_next_var <= ceiling.cs_next_var /\
  fresh_vars_wrt ceiling s ==>
  ?t slot. run_inst_seq (emitted_insts st en) s = OK t /\
    abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid s t /\
    fresh_vars_wrt ceiling t /\ eval_operand ip t = SOME (n2w slot) /\
    mload slot t = 0w /\ slot+32 < dimword (:256) /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (slot,32)
Proof
  strip_tac >> drule abi_decode_index_init_trace >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  `32 < dimword (:256)` by
    simp[dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``] >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st allocation_st) s = OK allocated` >>
  drule_all abi_malformed_alloc_registers >> strip_tac >>
  `st.cs_next_var < ceiling.cs_next_var` by decide_tac >>
  drule_all abi_decoder_register_update >> strip_tac >>
  `abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid s allocated` by
    (simp[abi_malformed_resource_post_def] >> metis_tac[]) >>
  `not_local_ptr cenv es.scopes (STRING #"%" (toString st.cs_next_var))` by
    (irule local_ptrs_reserved_fresh >> qexists_tac `st` >> simp[]) >>
  `abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid
     allocated (mstore (w2n w) 0w allocated)` by
    (irule abi_malformed_index_store_resource >> simp[] >>
     qexistsl_tac [`mk_inst st.cs_next_id ALLOCA [Lit 32w]
       [STRING #"%" (toString st.cs_next_var)]`, `STRING #"%" (toString st.cs_next_var)`] >>
     simp[mk_inst_def]) >>
  drule_all abi_malformed_resource_trans >> strip_tac >>
  `eval_operand (Lit 0w) allocated = SOME 0w` by simp[eval_operand_def] >>
  drule_all abi_decode_store_sequence >> strip_tac >>
  `inst_extends allocation_st en /\ inst_extends st allocation_st` by
    metis_tac[inst_extends_emit_void, abi_decode_alloc_buffer_inst_extends] >>
  drule_all run_inst_seq_emit_extend >> strip_tac >>
  qexistsl_tac [`mstore (w2n w) 0w allocated`, `w2n w`] >>
  gvs[mload_mstore_same, fresh_vars_wrt_mstore, mstore_def,
      write_memory_with_expansion_def]
QED

Theorem abi_malformed_init_header_resource:
  abi_decode_array_header dst addr MLOAD st = (cnt,en) /\
  abi_malformed_entry ctx func cenv cx es st sites dstid live
    base_op hi src dst B L xs p d outsz s /\
  32 <= outsz /\ fn_inst_ids_distinct func /\
  eval_operand addr s = SOME a /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st en) s = OK t /\
    fresh_vars_wrt en t /\ eval_operand cnt t = SOME (mload (w2n a) s) /\
    abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid s t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w)
Proof
  strip_tac >>
  `eval_operand dst s = SOME (n2w d) /\ d < dimword (:256)` by
    (fs[abi_malformed_entry_def] >> decide_tac) >>
  drule_all abi_malformed_array_header_exact >> strip_tac >>
  qexists_tac `t` >> simp[] >>
  `abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid s
    (mstore d (mload (w2n a) s) (s with vs_vars := t.vs_vars))` suffices_by
    (strip_tac >> fs[mstore_def, write_memory_with_expansion_def] >> metis_tac[]) >>
  irule abi_malformed_destination_store_resource >> simp[] >>
  conj_tac >- simp[GSYM lookup_var_def] >>
  metis_tac[]
QED

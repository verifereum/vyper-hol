Theory abiEncodePtrEmptyBody
Ancestors
  exprSimAbiEncodeEmptyFramed exprSimAbiEncodeEmptyComplex
  fragExecPtr fragGasSeqPtr ptrDiscipline emitHelperProps
  exprLoweringProps venomExecSemantics venomInst venomState
  compileEnv finite_map words list pred_set codegenRel
  assignTuplePtrLocalCopyRun abiEncoderLeaves abiEncodeEmptyCopyEndpoint
  exprSimAbiEncodeEmptySource abiEncoderWindowContract abiEncoderExtendSim
  abiDecoderContract abiEncoderRegisteredEffect bodyPtrDefs abiEncoderWindow

Theorem abi_encode_empty_copy_sequence_ptr:
  emit_void MCOPY [dst;src;Lit 0w] sa = ((),sb) /\
  eval_operand dst s = SOME a /\ eval_operand src s = SOME b /\
  op_taint tn dst = {} /\ op_taint tn src = {} /\
  ~ctx_has_dalloca ctx ==>
  inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s G tn /\
  run_inst_seq (emitted_insts sa sb) s = OK (mcopy (w2n a) (w2n b) 0 s)
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  asm_rewrite_tac[] >>
  `ptr_inst_ok D 0 0 ctx func G tn
     (mk_inst sa.cs_next_id MCOPY [dst;src;Lit 0w] []) s` by
    metis_tac[ptr_inst_ok_mcopy_zero] >>
  simp[inst_seq_ptr_def, run_inst_seq_def,
    step_inst_base_opcode_eqs, mk_inst_def, eval_operand_def] >>
  simp[step_prov_def, set_prov_def, step_taint_def,
    mem_taint_def, set_var_taint_def, store_taint_def, adopt_reset_def,
    imm_taint_def, eval_operand_def] >>
  simp[DRESTRICT_UNIV, new_site_bytes_def, step_writes_def,
    range_bytes_def, written_taint_def, mk_inst_def, eval_operand_def,
    mcopy_def, write_memory_with_expansion_def, EXTENSION,
    source_memory_write_ranges_def, sized_source_write_range_def,
    FLOOKUP_DEF, SF CONJ_ss] >> simp[taint_component_equality]
QED

Theorem abi_encode_empty_copy_path_ptr:
  compile_abi_encode_to_buf dst src (AbiCopy 0) sa = (out,sb) /\
  fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand dst s = SOME a /\ eval_operand src s = SOME b /\
  op_taint tn dst = {} /\ op_taint tn src = {} /\
  ~ctx_has_dalloca ctx ==>
  gas_path_ptr D 0 ctx func PG G tn s 0 G tn
    (OK ((mcopy (w2n a) (w2n b) 0 s) with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >> drule abi_encode_copy_code >> strip_tac >>
  drule_all abi_encode_empty_copy_sequence_ptr >> strip_tac >>
  irule emitted_sequence_path_ptr >>
  conj_tac >- simp[] >> qexists_tac `sa` >>
  drule emit_void_extends >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  simp[mk_inst_def, is_terminator_def]
QED

Theorem abi_encode_empty_copy_body_ptr:
  compile_abi_encode_to_buf dst src (AbiCopy 0) sa = (out,sb) /\
  abi_encode_empty_window_pre ctx func sa sb dst src at av a d s /\
  d < dimword (:256) /\
  op_taint tn dst = {} /\ op_taint tn src = {} /\
  ~ctx_has_dalloca ctx /\ ptr_covers G tn x s outsz ==>
  ?t. window_strong_result ctx func sa sb out at av d s t /\
    abi_encode_exec_frame func s t /\ t.vs_labels = s.vs_labels /\
    (!v. lookup_var v t = lookup_var v s) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    ptr_covers G tn x t outsz /\
    op_taint tn out = {} /\ (!v. out = Var v ==> not_fresh_at sb v) /\
    enc at av = [] /\
    gas_path_ptr D 0 ctx func PG G tn s 0 G tn (OK t)
Proof
  strip_tac >> drule_all abi_encode_empty_copy_endpoint >> strip_tac >>
  qpat_assum `abi_encode_empty_window_pre _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [abi_encode_empty_window_pre_def]) >>
  drule_all abi_encode_empty_copy_path_ptr >> strip_tac >>
  drule abi_encode_copy_code >> strip_tac >>
  qpat_x_assum `out = Lit 0w` SUBST_ALL_TAC >>
  `enc at av = []` by
    (fs[abi_encoder_window_copy_iff, valueEncodingDefsTheory.mem_bytes_at_def]) >>
  qpat_x_assum `!PG G D. gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _`
    (qspecl_then [`PG`, `G`, `D`] mp_tac) >>
  asm_simp_tac std_ss [wordsTheory.w2n_n2w] >> strip_tac >>
  qexists_tac `(mcopy d (w2n a) 0 s) with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  simp[lookup_var_def, mcopy_def, write_memory_with_expansion_def, op_taint_def] >>
  qpat_x_assum `ptr_covers G tn x s outsz` mp_tac >>
  simp[ptr_covers_def, lookup_var_def, mcopy_def, write_memory_with_expansion_def]
QED

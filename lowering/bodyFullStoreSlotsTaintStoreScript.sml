Theory bodyFullStoreSlotsTaintStore
Ancestors
  assignBasePtrWordStore fragGasCopyLoop fragGasCopySeqLiftProps bodyFullStoreSlotsRetired
  fragGasSeqPtr fragGasSeqPtrContext fragGasOriginPtr fragExecMem exprLoweringProps
  emitHelperProps emitHelper compileEnv venomExecSemantics venomState
  venomInst ptrDiscipline contextCodegenRel codegenRel unitTransformDefs
  memSafeRun

Theorem storage_tainted_singleton[local]:
  eval_operand addr s = SOME slot /\ eval_operand op s = SOME w /\
  op_taint tn addr = {} /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_call_ctx.cc_static ==>
  run_inst_seq [mk_inst id (if tr then TSTORE else SSTORE) [addr;op] []] s =
    OK (if tr then tstore slot w s else sstore slot w s) /\
  inst_seq_ptr D 0 ctx func PG G tn
    [mk_inst id (if tr then TSTORE else SSTORE) [addr;op] []] s G
    (if tr then tn with t_trans := key_update tn.t_trans slot (op_taint tn op)
     else tn with t_stor := key_update tn.t_stor slot (op_taint tn op))
Proof
  strip_tac >>
  `step_inst_base (mk_inst id (if tr then TSTORE else SSTORE) [addr;op] []) s =
     OK (if tr then tstore slot w s else sstore slot w s)` by
    (Cases_on `tr` >> simp[step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def]) >>
  simp[run_inst_seq_def, inst_seq_ptr_def] >>
  conj_tac
  >- (irule ptr_inst_ok_restore_ctx >>
      conj_tac >- (Cases_on `tr` >> simp[mk_inst_def]) >>
      conj_tac >- simp[] >>
      irule assign_base_ptr_inst_ok_storage_word >>
      Cases_on `tr` >> simp[ctx_has_dalloca_def]) >>
  qpat_x_assum `eval_operand addr s = SOME slot`
    (mp_then (Pos (el 2)) mp_tac assign_base_storage_word_ghost) >>
  disch_then (qspec_then `if tr then TSTORE else SSTORE` mp_tac) >>
  disch_then (qspecl_then [`id`,`op`,
    `if tr then tstore slot w s else sstore slot w s`,`PG`,`G`,`tn`] mp_tac) >>
  Cases_on `tr` >> simp[sstore_def, tstore_def]
QED

Theorem storage_tainted_word_store_origin_ptr:
 !tr addr op sa sb func s ctx slot w tn lo explicit PG G.
  emit_void (if tr then TSTORE else SSTORE) [addr;op] sa = ((),sb) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ~s.vs_call_ctx.cc_static /\ allocas_from lo s /\
  eval_operand addr s = SOME slot /\ eval_operand op s = SOME w /\
  op_taint tn addr = {} ==>
  !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
   (OK ((if tr then tstore slot w s else sstore slot w s)
        with vs_inst_idx := LENGTH sb.cs_current_insts), G,
    if tr then tn with t_trans := key_update tn.t_trans slot (op_taint tn op)
    else tn with t_stor := key_update tn.t_stor slot (op_taint tn op))
Proof
  rpt gen_tac >> strip_tac >> gen_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  drule emit_void_same_blocks >> strip_tac >>
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    gvs[emitted_insts_def, same_blocks_def, emit_void_def, emit_def,
        comp_bind_def, fresh_id_def, comp_return_def] >>
  drule_all bop_suffix_placement >> strip_tac >>
  drule_all storage_tainted_singleton >>
  disch_then (qspecl_then [`tr`,`sa.cs_next_id`,`func`,`PG`,`G`,`D`] strip_assume_tac) >>
  `run_inst_seq_mem_ok
    [mk_inst sa.cs_next_id (if tr then TSTORE else SSTORE) [addr;op] []] s` by
    (Cases_on `tr` >> simp[run_inst_seq_mem_ok_def,
      inst_mem_below_frontier_def, inst_dload_in_section_def,
      source_memory_read_ranges_def, source_memory_write_ranges_def,
      mk_inst_def, run_inst_seq_def, step_inst_base_opcode_eqs,
      exec_write2_def]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS)
    [mk_inst sa.cs_next_id (if tr then TSTORE else SSTORE) [addr;op] []]` by
    (Cases_on `tr` >> simp[mk_inst_def, is_terminator_def]) >>
  `isPREFIX [mk_inst sa.cs_next_id (if tr then TSTORE else SSTORE) [addr;op] []]
    (DROP s.vs_inst_idx bb.bb_instructions)` by metis_tac[] >>
  `(ptrDiscipline$ctx_has_dalloca ctx ==>
    !pre i post u.
      [mk_inst sa.cs_next_id (if tr then TSTORE else SSTORE) [addr;op] []] =
        pre ++ i::post /\ run_inst_seq pre s = OK u ==>
      unitTransformDefs$dalloca_no_wrap i u)` by
    (rpt strip_tac >> irule dalloca_no_wrap_non_dalloca >>
     `MEM i [mk_inst sa.cs_next_id (if tr then TSTORE else SSTORE) [addr;op] []]` by
       metis_tac[listTheory.MEM_APPEND, listTheory.MEM] >>
     Cases_on `tr` >> gvs[mk_inst_def]) >>
  drule_all run_inst_seq_origin_ptr_lift >>
  disch_then (qspec_then `explicit` strip_assume_tac) >> gvs[]
QED

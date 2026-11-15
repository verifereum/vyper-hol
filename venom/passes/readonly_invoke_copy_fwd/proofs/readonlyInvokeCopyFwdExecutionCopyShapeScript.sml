(* Actual erased MCOPY coordinates retain their selected event and NOP shape. *)
Theory readonlyInvokeCopyFwdExecutionCopyShape
Ancestors
  readonlyInvokeCopyFwdHistoryEventUniqueness readonlyInvokeCopyFwdHistory
  readonlyInvokeCopyFwdHistoryUses readonlyInvokeCopyFwdHistoryReadExceptions
  readonlyInvokeCopyFwdTraceOrigin readonlyInvokeCopyFwdPlan
  readonlyInvokeCopyFwdDefs invokeCopyFwdCommonDefs internalReturnCopyFwdPlan
  passSharedDefs venomInst venomWf list indexedLists

Theorem ricf_event_empty_operands_outputs[local]:
  i < LENGTH bb.bb_instructions /\
  (EL i bb.bb_instructions).inst_operands = [] /\
  (EL i bb.bb_instructions).inst_outputs = [] ==>
  (EL i (ricf_event_apply e bb).bb_instructions).inst_operands = [] /\
  (EL i (ricf_event_apply e bb).bb_instructions).inst_outputs = []
Proof
  simp[ricf_event_apply_def, ricf_apply_forward_def, EL_MAPi] >>
  rpt strip_tac >> rw[mk_nop_inst_def]
QED

Theorem ricf_block_trace_empty_operands_outputs[local]:
  !bb es last. ricf_block_trace bb es last ==>
  !i. i < LENGTH bb.bb_instructions /\
    (EL i bb.bb_instructions).inst_operands = [] /\
    (EL i bb.bb_instructions).inst_outputs = [] ==>
    (EL i last.bb_instructions).inst_operands = [] /\
    (EL i last.bb_instructions).inst_outputs = []
Proof
  ho_match_mp_tac ricf_block_trace_ind >> simp[] >> rpt strip_tac >>
  metis_tac[ricf_event_prefix_and_copy, ricf_event_empty_operands_outputs]
QED

Theorem ricf_block_trace_erased_copy_shape[local]:
  !bb es last. ricf_block_trace bb es last ==>
  !i. i < LENGTH bb.bb_instructions /\
    (EL i bb.bb_instructions).inst_opcode = MCOPY /\
    (EL i last.bb_instructions).inst_opcode = NOP ==>
    (EL i last.bb_instructions).inst_operands = [] /\
    (EL i last.bb_instructions).inst_outputs = []
Proof
  ho_match_mp_tac ricf_block_trace_strongind >> conj_tac
  >- (rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >> qx_gen_tac `i` >> strip_tac >>
  drule ricf_event_prefix_and_copy >> strip_tac >>
  Cases_on `i = e.rfe_index`
  >- (irule ricf_block_trace_empty_operands_outputs >>
      qexistsl_tac [`ricf_event_apply e bb`,`es`] >> simp[mk_nop_inst_def]) >>
  first_x_assum irule >> simp[] >>
  drule ricf_event_opcode >> disch_then (qspec_then `e` mp_tac) >> simp[]
QED

Theorem ricf_execution_logged_erased_copy:
  ricf_logged_function_trace ctx0 fn log mid /\
  ssa_form fn /\ fn_inst_wf fn /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  b < LENGTH fn.fn_blocks /\ i < LENGTH (EL b fn.fn_blocks).bb_instructions /\
  inst = EL i (EL b fn.fn_blocks).bb_instructions /\ inst.inst_opcode = MCOPY /\
  target = EL i (EL b mid.fn_blocks).bb_instructions /\ target.inst_opcode <> MCOPY ==>
  target.inst_opcode = NOP /\ target.inst_operands = [] /\ target.inst_outputs = [] /\
  ?round es prefix e current dst sv z.
    ricf_located_event ctx0 fn log round b es prefix e current /\
    e.rfe_index = i /\ inst = ricf_event_copy e (EL b fn.fn_blocks) /\
    inst.inst_operands = [Var dst;Var sv;Lit z]
Proof
  strip_tac >>
  `ricf_function_edit fn mid` by
    metis_tac[ricf_logged_function_trace_erases, ricf_function_trace_edit] >>
  `ricf_inst_edit inst target` by
    (fs[ricf_function_edit_def, ricf_block_edit_def, LIST_REL_EL_EQN] >> metis_tac[]) >>
  `target.inst_opcode = NOP` by gvs[ricf_inst_edit_def] >> simp[] >>
  `ricf_block_trace (EL b fn.fn_blocks)
    (FLAT (MAP (\(round,logs,mid). EL b logs) log)) (EL b mid.fn_blocks)` by
    metis_tac[ricf_logged_function_block_trace] >>
  `target.inst_operands = [] /\ target.inst_outputs = []` by
    (drule ricf_block_trace_erased_copy_shape >>
     disch_then (qspec_then `i` mp_tac) >> gvs[]) >> simp[] >>
  `ricf_logged_erasure log b i inst` by
    (drule ricf_logged_function_trace_erasure >>
     disch_then (qspecl_then [`b`,`i`,`inst`] mp_tac) >> gvs[]) >>
  drule_all ricf_logged_erasure_located_event >> strip_tac >>
  drule ricf_located_event_validation >> strip_tac >>
  drule_all ricf_located_event_source_block >> strip_tac >>
  `MEM (EL b fn.fn_blocks) fn.fn_blocks` by simp[EL_MEM] >>
  `e.rfe_ctx.icf_dfg = dfg_build_function round` by simp[] >>
  drule_all ricf_later_round_alloca_witnesses >> strip_tac >>
  gvs[] >>
  qexistsl_tac [`round`,`es`,`prefix`,`e`,`current`,`dst`,`sv`,`sz`] >>
  fs[ricf_event_copy_def]
QED

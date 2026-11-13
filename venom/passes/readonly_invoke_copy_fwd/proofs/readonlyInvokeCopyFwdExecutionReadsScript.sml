Theory readonlyInvokeCopyFwdExecutionReads
Ancestors
  readonlyInvokeCopyFwdExecutionLocal readonlyInvokeCopyFwdExecution
  readonlyInvokeCopyFwdExecutionOrdinary readonlyInvokeCopyFwdHeterogeneousLedger
  readonlyInvokeCopyFwdRel internalReturnCopyFwdSim
  o1LowerDloadRelocationKernel o1LowerDloadOccurrence o1LowerDloadJointRead1
  o1LowerDloadGhost o1LowerDloadShared memLocDefs pointerConfinedDefs
  taintAgree ptrDiscipline codegenRel venomExecSemantics venomState venomInst
  finite_map list pred_set words

Theorem ricf_execution_read0_next:
  ricf_execution_invariant vs C ctx0 log D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets rt /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  active_inst fn inst s /\
  MEM inst.inst_opcode [CALLER;ADDRESS;CALLVALUE;ORIGIN;GASPRICE;CHAINID;
    COINBASE;TIMESTAMP;NUMBER;PREVRANDAO;GASLIMIT;BASEFEE;BLOBBASEFEE;
    CALLDATASIZE;RETURNDATASIZE;CODESIZE;RETPC_PARAM;GETFMP;INITIAL_FMP;SELFBALANCE] /\
  step_inst fuel C inst s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?v. step_inst fuel Ct inst t = OK v /\
    ricf_execution_invariant vs C ctx0 log D stk PG (step_prov PG G inst u)
      (step_taint inst s u tn) fn next
      (u with vs_inst_idx := SUC s.vs_inst_idx)
      (v with vs_inst_idx := SUC s.vs_inst_idx)
      n a U (occurrence_sites_step a B inst u) HP
      (occurrence_step a HP H inst u) ledger E sites maps targets
      (step_taint inst s u rt)
Proof
  strip_tac >>
  `ld_shared_agree D s.vs_call_ctx.cc_address rt s t` by
    fs[ricf_execution_invariant_def, ricf_frame_agree_def, taint_agree_def,
      ld_shared_agree_def] >>
  drule ld_shared_account_observations >> strip_tac >>
  `t.vs_call_ctx = s.vs_call_ctx /\ t.vs_tx_ctx = s.vs_tx_ctx /\
   t.vs_block_ctx = s.vs_block_ctx /\ t.vs_returndata = s.vs_returndata /\
   t.vs_code = s.vs_code /\ t.vs_fmp = s.vs_fmp /\
   t.vs_initial_fmp = s.vs_initial_fmp /\
   t.vs_return_pc_token = s.vs_return_pc_token` by
    (fs[ricf_execution_invariant_def, ricf_frame_agree_def, taint_agree_def] >>
     qpat_x_assum `_ = s` mp_tac >> simp[venom_state_component_equality]) >>
  `?out value. u = update_var out value s /\ inst.inst_outputs = [out] /\
    step_inst fuel Ct inst t = OK (update_var out value t)` by
    (qpat_x_assum `step_inst fuel C inst s = OK u` mp_tac >> fs[MEM] >>
     gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, exec_read0_def,
       AllCaseEqs()] >> metis_tac[]) >>
  qexists_tac `update_var out value t` >> simp[] >> gvs[] >>
  `out_taint rt inst s = {} /\ written_taint rt inst s = {}` by
    (fs[MEM] >> gvs[out_taint_def, written_taint_def] >> rpt CASE_TAC >> simp[]) >>
  irule (Q.INST [`p` |-> `NONE`, `m` |-> `{}`] ricf_execution_bind_next) >>
  simp[ricf_value_agree_def, ld_value_agree_def, word_agree_except_def] >>
  fs[MEM] >>
  gvs[step_prov_def, out_prov_def, step_taint_def, out_taint_def,
    mem_taint_def, adopt_reset_def, store_taint_def,
    imm_taint_def, new_site_bytes_def, step_writes_def, written_taint_def,
    range_bytes_def, taint_component_equality, occurrence_sites_step_def,
    source_memory_write_ranges_def, update_var_def,
    FLOOKUP_DEF, is_terminator_def, SF CONJ_ss] >>
  metis_tac[update_var_def]
QED

Theorem ricf_execution_read1_next:
  ricf_execution_invariant vs C ctx0 log D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ptr_discipline lo C vs /\ active_inst fn inst s /\
  MEM inst.inst_opcode
    [BLOCKHASH;BLOBHASH;BALANCE;EXTCODESIZE;EXTCODEHASH;CALLDATALOAD;DLOAD] /\
  step_inst fuel C inst s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?v. step_inst fuel Ct inst t = OK v /\
    ricf_execution_invariant vs C ctx0 log D stk PG (step_prov PG G inst u)
      (step_taint inst s u tn) fn next
      (u with vs_inst_idx := SUC s.vs_inst_idx)
      (v with vs_inst_idx := SUC s.vs_inst_idx)
      n a U (occurrence_sites_step a B inst u) HP
      (occurrence_step a HP H inst u) ledger E sites maps targets
      (step_taint inst s u tn)
Proof
  strip_tac >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    (fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
     metis_tac[occ_frame_reachable_projection]) >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  `!op x. MEM op inst.inst_operands /\ eval_operand op s = SOME x ==>
    eval_operand op t = SOME x` by
    (rpt strip_tac >>
     `op_taint tn op = {}` by
       (fs[MEM] >> gvs[taint_ok_def] >> metis_tac[]) >>
     `~is_pointer_preserving_op inst.inst_opcode /\
      ~MEM inst.inst_opcode [LT;GT;EQ;INVOKE] /\
      mem_read_ops inst = NONE /\ mem_write_ops inst = NONE` by
       (fs[MEM] >> gvs[is_pointer_preserving_op_def, mem_read_ops_def, mem_write_ops_def]) >>
     metis_tac[ricf_execution_scalar_operand]) >>
  `ld_shared_agree D s.vs_call_ctx.cc_address tn s t` by
    fs[ricf_execution_invariant_def, ricf_frame_agree_def, taint_agree_def,
      ld_shared_agree_def] >>
  drule ld_shared_account_observations >> strip_tac >>
  `t.vs_call_ctx = s.vs_call_ctx /\ t.vs_tx_ctx = s.vs_tx_ctx /\
   t.vs_block_ctx = s.vs_block_ctx /\ t.vs_data_section = s.vs_data_section` by
    (fs[ricf_execution_invariant_def, ricf_frame_agree_def, taint_agree_def] >>
     qpat_x_assum `_ = s` mp_tac >> simp[venom_state_component_equality]) >>
  `?out value. u = update_var out value s /\ inst.inst_outputs = [out] /\
    step_inst fuel Ct inst t = OK (update_var out value t)` by
    (qpat_x_assum `step_inst fuel C inst s = OK u` mp_tac >> fs[MEM] >>
     (gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, exec_read1_def,
       AllCaseEqs()] >> strip_tac >>
      qpat_x_assum `update_var _ _ _ = u` (SUBST_ALL_TAC o SYM) >>
      qmatch_goalsub_abbrev_tac `update_var out value s` >>
      qexistsl_tac [`out`,`value`] >> simp[] >>
      simp[Abbr `value`] >> metis_tac[MEM])) >>
  qexists_tac `update_var out value t` >> simp[] >> gvs[] >>
  `out_taint tn inst s = {} /\ written_taint tn inst s = {}` by
    (fs[MEM] >> gvs[out_taint_def, written_taint_def] >> rpt CASE_TAC >> simp[]) >>
  irule (Q.INST [`p` |-> `NONE`, `m` |-> `{}`] ricf_execution_bind_next) >>
  simp[ricf_value_agree_def, ld_value_agree_def, word_agree_except_def] >>
  fs[MEM] >>
  gvs[step_prov_def, out_prov_def, step_taint_def, out_taint_def,
    mem_taint_def, adopt_reset_def, store_taint_def,
    imm_taint_def, new_site_bytes_def, step_writes_def, written_taint_def,
    range_bytes_def, taint_component_equality, occurrence_sites_step_def,
    source_memory_write_ranges_def, update_var_def,
    FLOOKUP_DEF, is_terminator_def, SF CONJ_ss] >>
  metis_tac[update_var_def]
QED

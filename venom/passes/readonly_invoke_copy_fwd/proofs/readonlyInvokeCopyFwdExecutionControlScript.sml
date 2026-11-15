Theory readonlyInvokeCopyFwdExecutionControl
Ancestors
  readonlyInvokeCopyFwdExecutionBlock readonlyInvokeCopyFwdExecution
  readonlyInvokeCopyFwdOpaque readonlyInvokeCopyFwdOpaquePhi readonlyInvokeCopyFwdOpaqueReturn
  readonlyInvokeCopyFwdHeterogeneousLedger
  readonlyInvokeCopyFwdHeterogeneousMapOrigins readonlyInvokeCopyFwdHistoryPhase
  readonlyInvokeCopyFwdOperationalSupport readonlyInvokeCopyFwdRel
  o1LowerDloadJointScalar o1LowerDloadPtrDiscipline o1LowerDloadGhost
  o1LowerDloadRelocationKernel o1LowerDloadOccurrence o1LowerDloadShared
  internalReturnCopyFwdSim frameRel unitShapeDefs o1PassContract
  taintAgree ptrDiscipline pointerConfinedDefs memLocDefs contextCodegenRel allocaFrontierBound
  venomExecProofs venomExecSemantics venomState venomInst
  finite_map list pred_set words

Theorem ricf_execution_jnz_condition:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  ptr_discipline lo C vs /\ opaque_use_ok fn /\ active_inst fn inst s /\
  inst.inst_opcode = JNZ /\ MEM cond inst.inst_operands /\
  eval_operand cond s = SOME value ==>
  eval_operand cond t = SOME value
Proof
  strip_tac >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    (fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
     metis_tac[occ_frame_reachable_projection]) >>
  `?P. EVERY (fn_ptr_ok P) C.ctx_functions` by
    metis_tac[ptr_discipline_fn_ptr_ok] >>
  `MEM fn C.ctx_functions /\ FDOM G SUBSET fn_pv P fn` by
    metis_tac[frame_reachable_prov_support] >>
  `MEM inst (fn_insts fn)` by metis_tac[active_inst_mem_fn_insts] >>
  `ptr_use_ok P (fn_pv P fn) inst` by
    (fs[EVERY_MEM, fn_ptr_ok_def] >> metis_tac[]) >>
  `op_prov G cond = NONE` by
    (irule ld_scalar_no_provenance >>
     qexistsl_tac [`P`,`inst`,`fn_pv P fn`] >>
     gvs[is_pointer_preserving_op_def, mem_read_ops_def, mem_write_ops_def]) >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  `op_taint tn cond = {}` by (gvs[taint_ok_def] >> metis_tac[]) >>
  `!v. cond = Var v ==> ~retpc_var fn v` by
    (qx_gen_tac `v` >> strip_tac >>
     fs[opaque_use_ok_def, retpc_use_ok_def] >>
     qpat_x_assum `!inst' x. _` (qspecl_then [`inst`,`v`] mp_tac) >> simp[]) >>
  `ricf_opaque_frame_agree fn D (ircf_dead (ricf_original_copy_ids C) s stk)
    sites (ricf_complete_params PG s.vs_params) G tn s t` by
    fs[ricf_execution_invariant_def] >>
  drule_all ricf_opaque_frame_operand >> strip_tac >>
  `value = y` by
    (irule ld_value_agree_clean >> qexists_tac `sites` >>
     gvs[ricf_opaque_value_agree_def, ricf_is_zero_prov_def,
       ricf_value_agree_def]) >> gvs[]
QED

Theorem ricf_execution_revert:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  inst.inst_opcode = REVERT /\ inst.inst_operands = [addr;sz] /\
  step_inst fuel C inst s = Abort Revert_abort s1 ==>
  ?t1. step_inst fuel Ct inst t = Abort Revert_abort t1 /\
    dead_result_rel D (Abort Revert_abort s1) (Abort Revert_abort t1)
Proof
  strip_tac >>
  `IS_SOME (eval_operand addr s) /\ IS_SOME (eval_operand sz s)` by
    (Cases_on `eval_operand addr s` >> Cases_on `eval_operand sz s` >>
     gvs[step_inst_non_invoke, step_inst_base_opcode_eqs]) >>
  `IS_SOME (eval_operand addr t) /\ IS_SOME (eval_operand sz t)` by
    (fs[ricf_execution_invariant_def] >>
     metis_tac[ricf_opaque_frame_operand_defined]) >>
  Cases_on `eval_operand addr t` >> Cases_on `eval_operand sz t` >>
  gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, dead_result_rel_def]
QED

Theorem ricf_execution_jnz_block:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  ptr_discipline lo C vs /\ o1_fn_shape C fn /\
  inst.inst_opcode = JNZ /\
  inst.inst_operands = [cond; Label if_nonzero; Label if_zero] /\
  active_inst fn inst s /\ step_inst fuel C inst s = OK u /\ ~u.vs_halted /\
  enters_block fn u s1 /\ active_inst fn next s1 ==>
  ?v t1. step_inst fuel Ct inst t = OK v /\ enters_block fn v t1 /\
    ricf_execution_invariant vs C D stk PG (entry_prov fn u G)
      (entry_taint_vars fn u tn) fn next s1 t1
      n a U B HP (entry_prov fn u H)
      (FILTER (\entry. SND entry <> []) ledger) E sites maps targets
      (entry_taint_vars fn u tn)
Proof
  strip_tac >>
  `opaque_use_ok fn /\ retpc_shape_ok fn /\ fn_inst_wf fn` by
    fs[o1_fn_shape_def, fn_shape_ok_def] >>
  Cases_on `eval_operand cond s`
  >- gvs[step_inst_non_invoke, step_inst_base_opcode_eqs] >>
  rename1 `eval_operand cond s = SOME value` >>
  `eval_operand cond t = SOME value` by
    (irule ricf_execution_jnz_condition >> metis_tac[MEM]) >>
  qabbrev_tac `lbl = if value <> 0w then if_nonzero else if_zero` >>
  `u = jump_to lbl s /\ step_inst fuel Ct inst t = OK (jump_to lbl t)` by
    (Cases_on `value = 0w` >>
     gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, Abbr `lbl`]) >>
  fs[ricf_execution_invariant_def] >>
  `is_terminator inst.inst_opcode` by simp[is_terminator_def] >>
  `ricf_heterogeneous_source_ledger vs C stk PG (entry_prov fn u G)
    (entry_taint_vars fn u tn) fn next s1 n a U B HP (entry_prov fn u H)
    (FILTER (\entry. SND entry <> []) ledger)` by
    (irule ricf_heterogeneous_source_ledger_block >> fs[jump_to_def] >>
     qexistsl_tac [`fuel`,`inst`,`s`] >> simp[]) >>
  `ricf_heterogeneous_map_origins vs C stk PG (entry_prov fn u G)
    (entry_taint_vars fn u tn) fn next s1 U B sites` by
    (irule ricf_heterogeneous_map_origins_block >> fs[jump_to_def] >>
     qexistsl_tac [`fuel`,`inst`,`s`] >> simp[]) >>
  `ricf_heterogeneous_saved_map_origins vs C stk PG (entry_prov fn u G)
    (entry_taint_vars fn u tn) fn next s1 U B maps` by
    (irule ricf_heterogeneous_saved_map_origins_block >> fs[jump_to_def] >>
     qexistsl_tac [`fuel`,`inst`,`s`] >> simp[]) >>
  drule_all ricf_execution_jump_live >>
  disch_then (qspec_then `lbl` strip_assume_tac) >>
  `enters_block fn (jump_to lbl s) s1` by metis_tac[] >>
  `ircf_cross tn {} (jump_to lbl s) (jump_to lbl t)` by simp[ircf_cross_def] >>
  drule_all ricf_opaque_live_support_enters_block >> strip_tac >>
  qexists_tac `t1` >>
  simp[ricf_execution_invariant_def, ricf_phase_stack_ranges_block_retire,
    ricf_phase_ranges_block_retire, ircf_cross_def] >>
  qpat_x_assum `enters_block fn (jump_to lbl s) s1` mp_tac >>
  simp[enters_block_def] >> strip_tac >>
  qpat_assum `eval_phis (jump_to lbl s) _ = OK _`
    (mp_tac o MATCH_MP eval_phis_only_updates_vs_vars) >>
  disch_then SUBST_ALL_TAC >> gvs[ircf_dead_def, jump_to_def]
QED

Theorem ricf_execution_stop_sink:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  taint_within D C vs /\ active_inst fn inst s /\
  MEM inst.inst_opcode [STOP; SINK] /\
  step_inst fuel C inst s = Halt s1 ==>
  ?t1. step_inst fuel Ct inst t = Halt t1 /\
    dead_result_rel D (Halt s1) (Halt t1)
Proof
  strip_tac >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    (fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
     metis_tac[occ_frame_reachable_projection]) >>
  `inst.inst_opcode <> INVOKE` by fs[MEM] >>
  `final_taint vs C s1 (step_taint inst s s1 tn) (ret_taint tn inst s)` by
    (simp[final_taint_def] >> metis_tac[]) >>
  `(step_taint inst s s1 tn).t_stor SUBSET
      D.d_stor s1.vs_call_ctx.cc_address
        (s1.vs_accounts s1.vs_call_ctx.cc_address).storage /\
   (step_taint inst s s1 tn).t_trans SUBSET
      D.d_trans s1.vs_call_ctx.cc_address (s1.vs_transient s1.vs_call_ctx.cc_address) /\
   (step_taint inst s s1 tn).t_imm SUBSET D.d_imm s1.vs_immutables` by
    (fs[taint_within_def] >> metis_tac[]) >>
  `ld_shared_agree D s.vs_call_ctx.cc_address tn s t` by
    (fs[ricf_execution_invariant_def, ricf_opaque_frame_agree_def,
      ricf_frame_agree_def] >>
     drule taint_agree_shared >>
     simp_tac (srw_ss()) [ricf_opaque_view_def, ld_shared_agree_def]) >>
  `s.vs_returndata = t.vs_returndata` by
    (fs[ricf_execution_invariant_def, ricf_opaque_frame_agree_def,
      ricf_frame_agree_def] >>
     drule taint_agree_frame >>
     disch_then (mp_tac o Q.AP_TERM `\st. st.vs_returndata`) >>
     simp[ricf_opaque_view_def]) >>
  fs[MEM] >>
  (qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
   simp[step_inst_non_invoke, step_inst_base_opcode_eqs] >> strip_tac >> gvs[] >>
   simp[step_inst_non_invoke, step_inst_base_opcode_eqs] >>
   irule (Q.INST [`A` |-> `s.vs_call_ctx.cc_address`, `tn` |-> `tn`, `R` |-> `{}`]
     ld_shared_halt_result) >>
   gvs[halt_state_def, set_returndata_def, step_taint_def, mem_taint_def,
     out_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
     new_site_bytes_def, step_writes_def, written_taint_def, range_bytes_def,
     codegenRelTheory.source_memory_write_ranges_def, ret_taint_def,
     ld_shared_agree_def] >>
   qexists_tac `tn` >> simp[])
QED

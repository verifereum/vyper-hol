Theory ctorDeployMemoryRunMemEntryPrefixWorld
Ancestors
 ctorDeployMemoryRunMemEntryTaskInitial ctorDeployMemoryRunMemEntryPrefix
 ctorDeployMemoryRunMemEntryTaskRegistration fragGasPathMem context compileEnv
 allocaHistory fragExec finite_map venomState arithmetic
 ctorDeployMemoryRunMemEntryLabel venomMemProps ctorDeployLoweringDefs
 ctorDeployMemoryRunMemEntryPhaseAdapters ctorDeployMemoryRunMemEntryShiftedFrame
 allocaBudgetProps

Theorem ctor_task_pay_phase_world:
 (if pay then comp_return () else
   comp_bind (emit_op CALLVALUE []) (\cv.
     comp_bind (emit_op ISZERO [cv]) (\nv. emit_void ASSERT [nv])))
   st = ((),st_pay) /\
 (pay \/ initial.vs_call_ctx.cc_callvalue = 0w) /\
 fresh_vars_wrt st initial /\ fn_has_code st st_pay func /\
 alloca_history func initial /\ ~initial.vs_halted /\
 initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
 ?actual.
 gas_path_mem ctx func initial 0 (OK actual) /\
 fresh_vars_wrt st_pay actual /\ alloca_history func actual /\
 ~actual.vs_halted /\ actual.vs_current_bb = st_pay.cs_current_bb /\
 actual.vs_inst_idx = LENGTH st_pay.cs_current_insts /\
 actual.vs_allocas = initial.vs_allocas /\
 actual.vs_alloca_next = initial.vs_alloca_next /\
 actual.vs_data_section = initial.vs_data_section /\
 actual.vs_gas_readings = initial.vs_gas_readings /\
 actual.vs_call_ctx = initial.vs_call_ctx /\ actual.vs_labels = initial.vs_labels /\
 actual.vs_memory = initial.vs_memory /\ actual.vs_accounts = initial.vs_accounts /\
 actual.vs_transient = initial.vs_transient /\ actual.vs_logs = initial.vs_logs /\
 actual.vs_requests = initial.vs_requests /\
 actual.vs_pending_deletions = initial.vs_pending_deletions /\
 actual.vs_tx_ctx = initial.vs_tx_ctx /\ actual.vs_block_ctx = initial.vs_block_ctx /\
 actual.vs_outcomes = initial.vs_outcomes
Proof
 Cases_on `pay` >> simp[] >> strip_tac
 >- (gvs[comp_return_def] >> qexists `initial` >> simp[gas_path_mem_rules]) >>
 gvs[comp_bind_def, comp_return_def] >>
 rpt (pairarg_tac >> gvs[]) >>
 drule_all ctor_checked_payable >>
 disch_then (qspec_then `ctx` mp_tac) >> strip_tac >>
 drule_all ctor_task_payable_exact >> strip_tac >>
 goal_assum (drule_at Any) >> gvs[update_var_def] >>
 qpat_x_assum `_ = raw with vs_inst_idx := _` mp_tac >>
 disch_then (mp_tac o Q.AP_TERM
   `\s:venom_state. (s.vs_data_section,s.vs_call_ctx,s.vs_labels,
     s.vs_memory,s.vs_accounts,s.vs_transient,s.vs_logs,s.vs_requests,
     s.vs_pending_deletions,s.vs_tx_ctx,s.vs_block_ctx,s.vs_outcomes)`) >>
 simp[]
QED

Theorem ctor_task_fixed_phase_world:
 (if cap > 0 then comp_bind (compile_fixed_region_with_id cap)
   (\r. comp_return (SND r).buf_operand) else comp_return (Lit 0w))
   st = (imm,st1) /\
 fresh_vars_wrt st initial /\ fn_has_code st st1 func /\
 alloca_history func initial /\ ~initial.vs_halted /\
 initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
 ?actual.
 gas_path_mem ctx func initial 0 (OK actual) /\
 fresh_vars_wrt st1 actual /\ alloca_history func actual /\
 ~actual.vs_halted /\ actual.vs_current_bb = st1.cs_current_bb /\
 actual.vs_inst_idx = LENGTH st1.cs_current_insts /\
 eval_operand imm actual = SOME 0w /\
 actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
 actual.vs_data_section = initial.vs_data_section /\
 actual.vs_gas_readings = initial.vs_gas_readings /\
 actual.vs_call_ctx = initial.vs_call_ctx /\ actual.vs_labels = initial.vs_labels /\
 actual.vs_memory = initial.vs_memory /\ actual.vs_accounts = initial.vs_accounts /\
 actual.vs_transient = initial.vs_transient /\ actual.vs_logs = initial.vs_logs /\
 actual.vs_requests = initial.vs_requests /\
 actual.vs_pending_deletions = initial.vs_pending_deletions /\
 actual.vs_tx_ctx = initial.vs_tx_ctx /\ actual.vs_block_ctx = initial.vs_block_ctx /\
 actual.vs_outcomes = initial.vs_outcomes
Proof
 Cases_on `cap > 0` >> simp[] >> strip_tac
 >- (gvs[comp_bind_def, comp_return_def] >>
     pairarg_tac >> gvs[] >>
     rename1 `compile_fixed_region_with_id cap st = (region,_)` >>
     PairCases_on `region` >> drule_all ctor_checked_fixed_region >>
     disch_then (qspec_then `ctx` mp_tac) >> strip_tac >>
     goal_assum (drule_at Any) >> gvs[update_var_def]) >>
 gvs[comp_return_def] >> qexists `initial` >>
 simp[gas_path_mem_rules, eval_operand_def]
QED

Theorem ctor_task_initial_phases_world:
  (if pay then comp_return () else
    comp_bind (emit_op CALLVALUE []) (\cv.
      comp_bind (emit_op ISZERO [cv]) (\nv. emit_void ASSERT [nv])))
    st = ((),st_pay) /\
  (if cap > 0 then comp_bind (compile_fixed_region_with_id cap)
    (\r. comp_return (SND r).buf_operand) else comp_return (Lit 0w))
    st_pay = (imm,st1) /\
  (pay \/ initial.vs_call_ctx.cc_callvalue = 0w) /\
  fresh_vars_wrt st initial /\ fn_has_code st st_pay func /\
  fn_has_code st_pay st1 func /\ alloca_history func initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?fixed.
    gas_path_mem ctx func initial 0 (OK fixed) /\
    fresh_vars_wrt st1 fixed /\ alloca_history func fixed /\
    ~fixed.vs_halted /\ fixed.vs_current_bb = st1.cs_current_bb /\
    fixed.vs_inst_idx = LENGTH st1.cs_current_insts /\
    eval_operand imm fixed = SOME 0w /\
    fixed.vs_allocas = initial.vs_allocas /\
    fixed.vs_alloca_next = initial.vs_alloca_next /\
    fixed.vs_data_section = initial.vs_data_section /\
    fixed.vs_gas_readings = initial.vs_gas_readings /\
    fixed.vs_call_ctx = initial.vs_call_ctx /\
    fixed.vs_labels = initial.vs_labels /\
    fixed.vs_memory = initial.vs_memory /\ fixed.vs_accounts = initial.vs_accounts /\
    fixed.vs_transient = initial.vs_transient /\ fixed.vs_logs = initial.vs_logs /\
    fixed.vs_requests = initial.vs_requests /\
    fixed.vs_pending_deletions = initial.vs_pending_deletions /\
    fixed.vs_tx_ctx = initial.vs_tx_ctx /\ fixed.vs_block_ctx = initial.vs_block_ctx /\
    fixed.vs_outcomes = initial.vs_outcomes
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all ctor_task_pay_phase_world >>
  disch_then (qspec_then `ctx` mp_tac) >> strip_tac >>
  drule_all ctor_task_fixed_phase_world >>
  disch_then (qspec_then `ctx` mp_tac) >> strip_tac >>
  goal_assum (drule_at Any) >> simp[] >>
  drule_all gas_path_mem_then >> simp[]
QED

Theorem ctor_task_registration_prefix_world:
  deploy_phases policy tops (deploy_bc,runtime_bc)
    (rpolicy,dunit,dout,prog,cplan) /\
  deploy_source_ok tops am tx /\ deploy_state_rel tops deploy_bc am tx es /\
  gas_variant vs (deploy_entry_state prog cplan tops es) /\
  deploy_ctor_start tops am tx (mut,nr,stmts,am_c,es0) /\
  lookup_function "__deploy" dunit.cu_context.ctx_functions = SOME func /\
  fn_entry_label func = SOME lbl /\ pay = (mut = Payable) /\
  (if pay then comp_return () else
    comp_bind (emit_op CALLVALUE []) (\cv.
      comp_bind (emit_op ISZERO [cv]) (\nv. emit_void ASSERT [nv])))
    (initial_compile_state "__deploy") = ((),st_pay) /\
  (if imm_len tops > 0 then comp_bind (compile_fixed_region_with_id (imm_len tops))
    (\r. comp_return (SND r).buf_operand) else comp_return (Lit 0w))
    st_pay = (imm,st1) /\
  fn_has_code (initial_compile_state "__deploy") st_pay func /\
  fn_has_code st_pay st1 func /\
  entry = vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|> ==>
  ?fixed.
    gas_path_mem dunit.cu_context func entry 0 (OK fixed) /\
    fresh_vars_wrt st1 fixed /\ alloca_history func fixed /\ alloca_inv fixed /\
    ~fixed.vs_halted /\ fixed.vs_current_bb = st1.cs_current_bb /\
    fixed.vs_inst_idx = LENGTH st1.cs_current_insts /\
    eval_operand imm fixed = SOME 0w /\
    fixed.vs_allocas = FEMPTY /\ fixed.vs_alloca_next = imm_len tops /\
    fixed.vs_data_section = vs.vs_data_section /\
    fixed.vs_gas_readings = vs.vs_gas_readings /\
    fixed.vs_call_ctx = vs.vs_call_ctx /\ fixed.vs_labels = vs.vs_labels /\
    fixed.vs_memory = vs.vs_memory /\ fixed.vs_accounts = vs.vs_accounts /\
    fixed.vs_transient = vs.vs_transient /\ fixed.vs_logs = vs.vs_logs /\
    fixed.vs_requests = vs.vs_requests /\
    fixed.vs_pending_deletions = vs.vs_pending_deletions /\
    fixed.vs_tx_ctx = vs.vs_tx_ctx /\ fixed.vs_block_ctx = vs.vs_block_ctx /\
    fixed.vs_outcomes = vs.vs_outcomes
Proof
  strip_tac >>
  drule_all ctor_task_normalized_entry >>
  disch_then (qspec_then `func` strip_assume_tac) >>
  drule_all ctor_checked_task_entry_cursor >> strip_tac >>
  drule_all ctor_task_entry_callvalue >> strip_tac >>
  `pay \/ entry.vs_call_ctx.cc_callvalue = 0w` by
    (drule ctor_task_source_payable >> strip_tac >> gvs[]) >>
  `entry.vs_current_bb = (initial_compile_state "__deploy").cs_current_bb /\
   entry.vs_inst_idx = LENGTH (initial_compile_state "__deploy").cs_current_insts`
    by gvs[] >>
  drule_at (Pat `fresh_vars_wrt _ _`) ctor_task_initial_phases_world >>
  disch_then drule >> disch_then drule >> simp[] >>
  disch_then (qspecl_then [`func`, `dunit.cu_context`] mp_tac) >>
  impl_tac >- gvs[] >> strip_tac >>
  goal_assum (drule_at Any) >> gvs[alloca_inv_empty]
QED

Theorem ctor_task_registration_initial_world:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx es vs
   body cenv nr nkey ut imm exit_lbl sa sb sj st_exit st_epilogue st_final func
   mut am_c es0 lbl entry.
  deploy_phases policy tops (deploy_bc,runtime_bc)
    (rpolicy,dunit,dout,prog,cplan) /\
  deploy_source_ok tops am tx /\ deploy_state_rel tops deploy_bc am tx es /\
  gas_variant vs (deploy_entry_state prog cplan tops es) /\
  deploy_ctor_code tops rpolicy runtime_bc dunit
    (body,cenv,nr,nkey,ut,imm,exit_lbl,sa,sb,sj,st_exit,st_epilogue,st_final,func) /\
  deploy_ctor_start tops am tx (mut,nr,body,am_c,es0) /\
  lookup_function "__deploy" dunit.cu_context.ctx_functions = SOME func /\
  fn_entry_label func = SOME lbl /\
  entry = vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|> ==>
  ?st_pay st1 ce0 pos_args ce1 st2 st3 fixed.
    (if mut = Payable then comp_return () else
      comp_bind (emit_op CALLVALUE []) (\cv.
        comp_bind (emit_op ISZERO [cv]) (\nv. emit_void ASSERT [nv])))
      (initial_compile_state "__deploy") = ((),st_pay) /\
    (if imm_len tops > 0 then comp_bind (compile_fixed_region_with_id (imm_len tops))
      (\r. comp_return (SND r).buf_operand) else comp_return (Lit 0w))
      st_pay = (imm,st1) /\
    compile_register_constructor_args
      (ce0 with ce_imm_alloca := (if imm_len tops > 0 then SOME imm else NONE))
      pos_args 0 0 st1 = (ce1,st2) /\
    (if nr then compile_nonreentrant_lock nkey ut F else comp_return ())
      st2 = ((),st3) /\
    fresh_label "ctor_exit" st3 = (exit_lbl,sa) /\
    cenv = ce1 with ce_ctor_exit_label := SOME exit_lbl /\
    fn_has_code (initial_compile_state "__deploy") st_pay func /\
    fn_has_code st_pay st1 func /\ fn_has_code st1 st2 func /\
    fn_has_code st2 st3 func /\
    gas_path_mem dunit.cu_context func entry 0 (OK fixed) /\
    fresh_vars_wrt st1 fixed /\ alloca_history func fixed /\ alloca_inv fixed /\
    ~fixed.vs_halted /\ fixed.vs_current_bb = st1.cs_current_bb /\
    fixed.vs_inst_idx = LENGTH st1.cs_current_insts /\
    eval_operand imm fixed = SOME 0w /\
    fixed.vs_allocas = FEMPTY /\ fixed.vs_alloca_next = imm_len tops /\
    fixed.vs_data_section = vs.vs_data_section /\
    fixed.vs_gas_readings = vs.vs_gas_readings /\
    fixed.vs_call_ctx = vs.vs_call_ctx /\ fixed.vs_labels = vs.vs_labels /\
    (!site. alloca_frontier_inv_from (imm_len tops) dunit.cu_context func site fixed) /\
    imm_len tops + unit_alloca_budget dunit.cu_context < dimword (:256) /\
    fixed.vs_memory = vs.vs_memory /\ fixed.vs_accounts = vs.vs_accounts /\
    fixed.vs_transient = vs.vs_transient /\ fixed.vs_logs = vs.vs_logs /\
    fixed.vs_requests = vs.vs_requests /\
    fixed.vs_pending_deletions = vs.vs_pending_deletions /\
    fixed.vs_tx_ctx = vs.vs_tx_ctx /\ fixed.vs_block_ctx = vs.vs_block_ctx /\
    fixed.vs_outcomes = vs.vs_outcomes
Proof
  rpt gen_tac >> strip_tac >>
  qpat_assum `deploy_ctor_code _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[deploy_ctor_code_def] >> strip_tac >>
  drule_all ctor_task_package_payable >> strip_tac >> fs[] >>
  drule_all ctor_phase_extends >> strip_tac >>
  drule_all ctor_phase_code_split >> strip_tac >>
  qpat_x_assum `cap = _` SUBST_ALL_TAC >>
  drule_all (SRULE [] (Q.INST [`pay` |-> `mut = Payable`]
    ctor_task_registration_prefix_world)) >> strip_tac >>
  `(!site. alloca_frontier_inv_from (imm_len tops) dunit.cu_context func site fixed) /\
    imm_len tops + unit_alloca_budget dunit.cu_context < dimword (:256)` by
    metis_tac[ctor_task_fixed_frontier_direct] >>
  qexistsl [`st1`, `cenv0`, `pos_args`, `cenv1`, `st2`, `st3`, `fixed`] >> simp[]
QED

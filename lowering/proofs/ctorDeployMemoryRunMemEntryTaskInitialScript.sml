Theory ctorDeployMemoryRunMemEntryTaskInitial
Ancestors
  ctorDeployMemoryRunMemEntryTaskInputs ctorDeployMemoryFrontier
  ctorDeployImmBudget ctorDeployDefs e2eEntry o1PassContract venomMemProps
  allocaHistory compileEnv context finite_map fragGasPathMem
  ctorDeployMemoryRunMemEntryTaskRegistration ctorDeployMemoryRunMemEntryPrefix
  fragExec emitHelper ctorDeployLoweringDefs e2eDeployDefs
  vyperInterpreter vyperState ctorDeployMemoryRunMemEntryLabel
  ctorDeployMemoryRunMemEntryShiftedFrame contextCodegenRel allocaBudgetProps
  allocaFrontierBound fcgPostorder fcgCorrectnessProof fcgDefs deployUnitProducers venomWf
  venomInst vyperCompiler arithmetic ctorDeployLoweringPrefix
  ctorDeployMemoryRunMemEntryPhaseAdapters ctorDeployMemoryRunMemEntryEntryPhi
  ctorDeployMemoryRunMemEntryBoundary

Theorem ctor_task_entry_fields:
  gas_variant vs (deploy_entry_state prog cplan tops es) ==>
  vs.vs_vars = FEMPTY /\ vs.vs_allocas = FEMPTY /\
  vs.vs_alloca_next = imm_len tops /\ ~vs.vs_halted
Proof
  simp[gas_variant_def] >> strip_tac >>
  qpat_x_assum `deploy_entry_state _ _ _ _ = _` mp_tac >>
  disch_then (mp_tac o Q.AP_TERM
    `\s:venom_state. (s.vs_vars,s.vs_allocas,s.vs_alloca_next,s.vs_halted)`) >>
  simp[deploy_entry_state_def, entry_venom_state_def,
    venomStateTheory.init_venom_state_def]
QED

Theorem ctor_task_normalized_entry:
  gas_variant vs (deploy_entry_state prog cplan tops es) /\
  entry = vs with <|vs_prev_bb := NONE; vs_current_bb := lbl;
                   vs_inst_idx := 0|> ==>
  alloca_inv entry /\ alloca_history func entry /\
  fresh_vars_wrt (initial_compile_state "__deploy") entry /\
  ~entry.vs_halted /\ entry.vs_current_bb = lbl /\
  entry.vs_inst_idx = 0 /\ entry.vs_allocas = FEMPTY /\
  entry.vs_alloca_next = imm_len tops /\
  entry.vs_data_section = vs.vs_data_section /\
  entry.vs_gas_readings = vs.vs_gas_readings /\
  entry.vs_call_ctx = vs.vs_call_ctx /\ entry.vs_labels = vs.vs_labels
Proof
  strip_tac >> drule ctor_task_entry_fields >> strip_tac >>
  gvs[] >> simp[fresh_vars_wrt_def] >>
  conj_tac >- (irule alloca_inv_empty >> simp[]) >>
  irule alloca_history_empty >> simp[]
QED

Theorem ctor_task_pay_phase:
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
    actual.vs_call_ctx = initial.vs_call_ctx /\
    actual.vs_labels = initial.vs_labels
Proof
  Cases_on `pay` >> simp[] >> strip_tac
  >- (gvs[comp_return_def] >> qexists `initial` >>
      simp[gas_path_mem_rules]) >>
  gvs[comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  drule_all ctor_checked_payable >>
  disch_then (qspec_then `ctx` mp_tac) >> strip_tac >>
  drule_all ctor_task_payable_exact >> strip_tac >>
  goal_assum (drule_at Any) >> gvs[venomStateTheory.update_var_def] >>
  qpat_x_assum `_ = raw with vs_inst_idx := _` mp_tac >>
  disch_then (mp_tac o Q.AP_TERM
    `\s:venom_state. (s.vs_data_section,s.vs_call_ctx,s.vs_labels)`) >>
  simp[]
QED

Theorem ctor_task_fixed_phase:
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
    actual.vs_allocas = initial.vs_allocas /\
    actual.vs_alloca_next = initial.vs_alloca_next /\
    actual.vs_data_section = initial.vs_data_section /\
    actual.vs_gas_readings = initial.vs_gas_readings /\
    actual.vs_call_ctx = initial.vs_call_ctx /\
    actual.vs_labels = initial.vs_labels
Proof
  Cases_on `cap > 0` >> simp[] >> strip_tac
  >- (gvs[comp_bind_def, comp_return_def] >>
      pairarg_tac >> gvs[] >>
      rename1 `compile_fixed_region_with_id cap st = (region,_)` >>
      PairCases_on `region` >>
      drule_all ctor_checked_fixed_region >>
      disch_then (qspec_then `ctx` mp_tac) >> strip_tac >>
      goal_assum (drule_at Any) >>
      gvs[venomStateTheory.update_var_def]) >>
  gvs[comp_return_def] >> qexists `initial` >>
  simp[gas_path_mem_rules, venomStateTheory.eval_operand_def]
QED

Theorem ctor_task_initial_phases:
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
    fixed.vs_labels = initial.vs_labels
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all ctor_task_pay_phase >>
  disch_then (qspec_then `ctx` mp_tac) >> strip_tac >>
  drule_all ctor_task_fixed_phase >>
  disch_then (qspec_then `ctx` mp_tac) >> strip_tac >>
  goal_assum (drule_at Any) >> simp[] >>
  drule_all gas_path_mem_then >> simp[]
QED

Theorem ctor_task_entry_frontier:
  deploy_phases policy tops (deploy_bc,runtime_bc)
    (rpolicy,dunit,dout,prog,cplan) /\
  gas_variant vs (deploy_entry_state prog cplan tops es) /\
  lookup_function "__deploy" dunit.cu_context.ctx_functions = SOME func ==>
  fn_entry_inv (alloca_frontier_inv_from (imm_len tops))
    dunit.cu_context func vs /\
  imm_len tops + unit_alloca_budget dunit.cu_context < dimword (:256)
Proof
  strip_tac >> drule_all deploy_unit_run_entry >> strip_tac >> gvs[] >>
  drule_all lowered_unit_entry_facts >> strip_tac >>
  conj_tac
  >- (irule alloca_frontier_inv_from_entry >> simp[] >> metis_tac[]) >>
  drule deploy_imm_alloca_budget_ok >> decide_tac
QED

Theorem ctor_task_source_payable:
  deploy_ctor_start tops am tx (mut,nr,stmts,am_c,es0) ==>
  mut = Payable \/ tx.value = 0
Proof
  simp[deploy_ctor_start_def] >> strip_tac >>
  Cases_on `tx.value = 0` >> simp[] >>
  qpat_x_assum `ignore_bind _ _ _ = _` mp_tac >>
  simp[send_call_value_def, deploy_evaluation_context_def,
       initial_evaluation_context_def, ignore_bind_def,
       check_def, assert_def, bind_def, return_def] >>
  Cases_on `mut = Payable` >> simp[]
QED

Theorem ctor_task_entry_callvalue:
  deploy_state_rel tops deploy_bc am tx es /\
  gas_variant vs (deploy_entry_state prog cplan tops es) ==>
  vs.vs_call_ctx.cc_callvalue = n2w tx.value
Proof
  strip_tac >>
  `vs.vs_call_ctx.cc_callvalue =
    (deploy_entry_state prog cplan tops es).vs_call_ctx.cc_callvalue` by
    (gvs[gas_variant_def] >>
     qpat_x_assum `deploy_entry_state _ _ _ _ = _` mp_tac >>
     disch_then (mp_tac o Q.AP_TERM
       `\s:venom_state. s.vs_call_ctx.cc_callvalue`) >> simp[]) >>
  gvs[deploy_state_rel_def, deploy_entry_state_def, entry_venom_state_def]
QED

Theorem ctor_task_registration_prefix:
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
    fixed.vs_call_ctx = vs.vs_call_ctx /\ fixed.vs_labels = vs.vs_labels
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
  drule_at (Pat `fresh_vars_wrt _ _`) ctor_task_initial_phases >>
  disch_then drule >> disch_then drule >>
  simp[] >>
  disch_then (qspecl_then [`func`, `dunit.cu_context`] mp_tac) >>
  impl_tac >- gvs[] >> strip_tac >>
  goal_assum (drule_at Any) >> gvs[alloca_inv_empty]
QED

Theorem ctor_task_fixed_frontier:
  deploy_phases policy tops (deploy_bc,runtime_bc)
    (rpolicy,dunit,dout,prog,cplan) /\
  gas_variant vs (deploy_entry_state prog cplan tops es) /\
  lookup_function "__deploy" dunit.cu_context.ctx_functions = SOME func /\
  enters_block func vs entered /\ active_inst func site entered /\
  fixed.vs_allocas = FEMPTY /\ fixed.vs_alloca_next = imm_len tops ==>
  alloca_frontier_inv_from (imm_len tops) dunit.cu_context func site' fixed /\
  imm_len tops + unit_alloca_budget dunit.cu_context < dimword (:256)
Proof
  strip_tac >> drule_all ctor_task_entry_frontier >> strip_tac >>
  `alloca_frontier_inv_from (imm_len tops) dunit.cu_context func site entered` by
    metis_tac[fn_entry_inv_def] >>
  drule enters_block_alloca_fields >> strip_tac >>
  drule ctor_task_entry_fields >> strip_tac >> simp[] >>
  irule alloca_frontier_inv_from_frame >> goal_assum (drule_at Any) >> simp[]
QED

Theorem ctor_task_frontier_at_entry_function:
  ctx_wf ctx /\ wf_invoke_targets ctx /\ reachable_call_graph_acyclic ctx /\
  ctx.ctx_entry = SOME name /\ lookup_function name ctx.ctx_functions = SOME func /\
  s.vs_alloca_next = k ==>
  alloca_frontier_inv_from k ctx func site s
Proof
  strip_tac >>
  `func.fn_name = name` by metis_tac[lookup_function_result_name] >>
  `MEM func ctx.ctx_functions` by metis_tac[lookup_function_MEM] >>
  `fcg_is_reachable (fcg_analyze ctx) name` by
    (irule fcgCorrectnessProofTheory.fcg_analyze_reachable_complete_proof >>
     simp[fcgDefsTheory.fcg_path_def, ctx_fn_names_def] >>
     metis_tac[lookup_function_mem]) >>
  gvs[alloca_frontier_inv_from_def] >> conj_tac
  >- (rpt strip_tac >>
      `fcg_is_reachable (fcg_analyze ctx) g` by
        metis_tac[fcgPostorderTheory.reachable_fcg_acyclic_tc_rank,
                  reachable_call_graph_acyclic_def] >>
      metis_tac[fcgPostorderTheory.reachable_fcg_acyclic_no_reachable_cycle,
                reachable_call_graph_acyclic_def]) >>
  simp_tac bool_ss [unit_alloca_budget_def, LET_THM] >>
  qmatch_goalsub_abbrev_tac `CARD below * frame` >>
  qabbrev_tac `n = LENGTH (FILTER (\i. i.inst_opcode = INVOKE)
    (FLAT (MAP fn_insts ctx.ctx_functions)))` >>
  `remaining_alloca_budget (fn_insts func) s <= frame /\ CARD below <= n` by
    simp[Abbr `below`, Abbr `frame`, Abbr `n`, call_targets_card,
         remaining_alloca_budget_frame] >>
  `CARD below * frame <= n * frame` by (irule LESS_MONO_MULT >> simp[]) >>
  full_simp_tac bool_ss [RIGHT_ADD_DISTRIB, MULT_LEFT_1] >> decide_tac
QED

Theorem ctor_task_fixed_frontier_direct:
  deploy_phases policy tops (deploy_bc,runtime_bc)
    (rpolicy,dunit,dout,prog,cplan) /\
  lookup_function "__deploy" dunit.cu_context.ctx_functions = SOME func /\
  fixed.vs_alloca_next = imm_len tops ==>
  alloca_frontier_inv_from (imm_len tops) dunit.cu_context func site fixed /\
  imm_len tops + unit_alloca_budget dunit.cu_context < dimword (:256)
Proof
  strip_tac >>
  `lowering_context_ok dunit.cu_context /\
   dunit.cu_context.ctx_entry = SOME "__deploy"` by
    (gvs[deploy_phases_def] >>
     metis_tac[lower_vyper_deploy_unit_context_ok, lower_vyper_deploy_unit_entry]) >>
  drule_all lowered_unit_entry_facts >> strip_tac >> conj_tac
  >- (irule ctor_task_frontier_at_entry_function >> simp[] >> metis_tac[]) >>
  drule deploy_imm_alloca_budget_ok >> decide_tac
QED

Theorem ctor_task_package_payable:
  lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit /\
  classify_functions tops = (exts,ints,fb,SOME cf) /\
  deploy_source_ok tops am tx /\ deploy_state_rel tops deploy_bc am tx es /\
  deploy_ctor_start tops am tx (mut,nr,stmts,am_c,es0) /\
  set_constructor_package_target rpolicy.rpol_target
    (package_constructor tops F (assign_nkeys tops 0) cf) =
      (ce,pa,pay,nr,key,ut,ss,ret) ==>
  pay = (mut = Payable)
Proof
  strip_tac >> PairCases_on `cf` >>
  `tx.function_name = "__init__"` by fs[deploy_state_rel_def] >>
  `?args. vyperInterpreter$lookup_function NONE "__init__" Deploy tops =
    SOME (mut,nr,args,[],NoneT,stmts)` by fs[deploy_ctor_start_def] >>
  drule_all ctor_task_aligned_inputs >> strip_tac >> gvs[] >>
  drule_all deploy_prefix_packaged_payable >> simp[]
QED

Theorem ctor_task_registration_initial:
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
    imm_len tops + unit_alloca_budget dunit.cu_context < dimword (:256)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_assum `deploy_ctor_code _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[deploy_ctor_code_def] >> strip_tac >>
  drule_all ctor_task_package_payable >> strip_tac >> fs[] >>
  drule_all ctor_phase_extends >> strip_tac >>
  drule_all ctor_phase_code_split >> strip_tac >>
  qpat_x_assum `cap = _` SUBST_ALL_TAC >>
  drule_all (SRULE [] (Q.INST [`pay` |-> `mut = Payable`]
    ctor_task_registration_prefix)) >> strip_tac >>
  `(!site. alloca_frontier_inv_from (imm_len tops) dunit.cu_context func site fixed) /\
    imm_len tops + unit_alloca_budget dunit.cu_context < dimword (:256)` by
    metis_tac[ctor_task_fixed_frontier_direct] >>
  qexistsl [`st1`, `cenv0`, `pos_args`, `cenv1`, `st2`, `st3`, `fixed`] >>
  simp[]
QED

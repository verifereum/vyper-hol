Theory fmpStageOpSimPureCopy
Ancestors
  fmpStageOpBase fmpStageRel o1LowerDloadRelocationKernel o1LowerDloadShared
  ptrStaticDiscipline ptrDiscipline o1PassContract contextCodegenRel
  venomExecSemantics venomState venomInst venomWf unitShapeDefs pointerConfinedDefs
  finite_map list pred_set words memLocDefs vfmState

val copies = ``[PARAM; ASSIGN; NOP; ASSERT; ASSERT_UNREACHABLE]``;

Theorem fmp_copy_assert_operand[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  MEM inst.inst_opcode [ASSERT; ASSERT_UNREACHABLE] /\
  MEM op inst.inst_operands /\ eval_operand op s = SOME x ==>
  eval_operand op t = SOME x
Proof
  strip_tac >> drule_all fmp_stage_frame_facts >> strip_tac >>
  drule fmp_stage_prov_support >>
  disch_then (qspec_then `P` mp_tac) >> simp[] >> strip_tac >>
  `fn_static_ptr_ok P fn` by metis_tac[EVERY_MEM] >>
  `ptr_use_static_ok P (fn_pv P fn) inst` by
    metis_tac[fn_static_ptr_ok_def] >>
  `op_prov G op = NONE /\ op_taint tn op = {}` by
    (Cases_on `op` >>
     gvs[op_prov_def, FLOOKUP_DEF, SUBSET_DEF, ptr_use_static_ok_def,
         mem_read_ops_def, mem_write_ops_def, is_pointer_preserving_op_def,
         taint_ok_def, MEM] >> metis_tac[]) >>
  `!v. op = Var v ==> ~retpc_var fn v` by
    (rpt strip_tac >>
     `opaque_use_ok fn` by gvs[o1_fn_shape_def, fn_shape_ok_def] >>
     gvs[] >> drule_all opaque_use_ok_retpc_use >>
     gvs[retpc_use_ok_def, MEM]) >>
  `inst.inst_opcode <> PHI` by gvs[MEM] >>
  drule_all fmp_stage_operand >>
  simp[fmp_value_rel_def, ld_value_agree_scalar] >>
  metis_tac[ld_value_agree_clean, ld_value_agree_scalar]
QED

Theorem fmp_copy_assign_operand[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [op] /\
  inst.inst_outputs = [out] /\ eval_operand op s = SOME x ==>
  ?y. eval_operand op t = SOME y /\
    (~retpc_var fn out ==> fmp_value_rel sm (op_prov G op) (op_taint tn op) x y)
Proof
  strip_tac >> Cases_on `!v. op = Var v ==> ~retpc_var fn v`
  >- (`inst.inst_opcode <> PHI /\ MEM op inst.inst_operands` by simp[] >>
      drule_all fmp_stage_operand >> metis_tac[]) >>
  gvs[] >> drule_all fmp_stage_frame_facts >> strip_tac >>
  `retpc_var fn out` by
    (gvs[retpc_var_def] >> irule (cj 2 copy_phi_var_rules) >>
     qexistsl [`inst`,`v`] >> simp[]) >>
  fs[eval_operand_def, lookup_var_def, fmp_stage_rel_def,
     fmp_frame_rel_def, fmp_env_rel_def] >> metis_tac[]
QED

Theorem fmp_copy_taint[local]:
  MEM inst.inst_opcode ^copies /\ s1 = s with vs_vars := V ==>
  step_taint inst s s1 tn =
    tn with t_var := set_var_taint tn.t_var inst.inst_outputs (out_taint tn inst s)
Proof
  strip_tac >> fs[MEM] >>
  simp[step_taint_def, mem_taint_def, store_taint_def, adopt_reset_def,
       imm_taint_def, new_site_bytes_def, step_writes_def,
       codegenRelTheory.source_memory_write_ranges_def, range_bytes_def,
       written_taint_def, FLOOKUP_DEF,
       taint_component_equality, EXTENSION, SF CONJ_ss] >>
  rpt (CASE_TAC >> simp[])
QED

val post = ``
  (!v. ~MEM v inst.inst_outputs ==>
    FLOOKUP s1.vs_vars v = FLOOKUP s.vs_vars v /\
    FLOOKUP t1.vs_vars v = FLOOKUP t.vs_vars v) /\
  (!v x. MEM v inst.inst_outputs /\ FLOOKUP s1.vs_vars v = SOME x ==>
    ?y. FLOOKUP t1.vs_vars v = SOME y /\
      (~retpc_var fn v ==> fmp_value_rel sm (FLOOKUP (step_prov PG G inst s1) v)
        (op_taint (step_taint inst s s1 tn) (Var v)) x y)) /\
  ld_memory_agree (fmp_ld_sites sm) eom
    (step_taint inst s s1 tn).t_mem s1.vs_memory t1.vs_memory /\
  ld_shared_agree D s.vs_call_ctx.cc_address (step_taint inst s s1 tn) s1 t1 /\
  s1.vs_returndata = t1.vs_returndata /\ ~s1.vs_halted /\ ~t1.vs_halted /\
  s1.vs_current_bb = s.vs_current_bb /\ s1.vs_prev_bb = s.vs_prev_bb /\
  s1.vs_inst_idx = s.vs_inst_idx /\ s1.vs_params = s.vs_params /\
  s1.vs_call_ctx = s.vs_call_ctx /\ s1.vs_tx_ctx = s.vs_tx_ctx /\
  s1.vs_block_ctx = s.vs_block_ctx /\ s1.vs_data_section = s.vs_data_section /\
  s1.vs_labels = s.vs_labels /\ s1.vs_code = s.vs_code /\
  s1.vs_prev_hashes = s.vs_prev_hashes /\
  s1.vs_initial_fmp = s.vs_initial_fmp /\ s1.vs_fmp = s.vs_fmp /\
  t1.vs_current_bb = t.vs_current_bb /\ t1.vs_prev_bb = t.vs_prev_bb /\
  t1.vs_inst_idx = t.vs_inst_idx /\ t1.vs_params = t.vs_params /\
  t1.vs_call_ctx = t.vs_call_ctx /\ t1.vs_tx_ctx = t.vs_tx_ctx /\
  t1.vs_block_ctx = t.vs_block_ctx /\ t1.vs_data_section = t.vs_data_section /\
  t1.vs_labels = t.vs_labels /\ t1.vs_code = t.vs_code /\
  t1.vs_prev_hashes = t.vs_prev_hashes /\
  t1.vs_initial_fmp = t.vs_initial_fmp /\ t1.vs_fmp = t.vs_fmp``;

Theorem fmp_copy_post[local]:
  MEM inst.inst_opcode ^copies /\ s1 = s with vs_vars := V /\
  t1 = t with vs_vars := target_vars /\
  ld_memory_agree (fmp_ld_sites sm) eom tn.t_mem s.vs_memory t.vs_memory /\
  ld_shared_agree D s.vs_call_ctx.cc_address tn s t /\
  s.vs_returndata = t.vs_returndata /\ ~s.vs_halted /\ ~t.vs_halted /\
  (!v. ~MEM v inst.inst_outputs ==> FLOOKUP V v = FLOOKUP s.vs_vars v /\
    FLOOKUP target_vars v = FLOOKUP t.vs_vars v) /\
  (!v x. MEM v inst.inst_outputs /\ FLOOKUP V v = SOME x ==>
    ?y. FLOOKUP target_vars v = SOME y /\
      (~retpc_var fn v ==> fmp_value_rel sm (FLOOKUP (step_prov PG G inst s1) v)
        (op_taint (step_taint inst s s1 tn) (Var v)) x y)) ==>
  ^post
Proof
  strip_tac >>
  `step_taint inst s s1 tn = tn with t_var :=
     set_var_taint tn.t_var inst.inst_outputs (out_taint tn inst s)` by
    metis_tac[fmp_copy_taint] >>
  gvs[ld_shared_agree_def]
QED

Theorem fmp_copy_write_value[local]:
  inst.inst_outputs = [out] /\
  (~retpc_var fn out ==> fmp_value_rel sm (out_prov PG G inst s1)
    (out_taint tn inst s) x y) /\ s1 = update_var out x s ==>
  (!v. ~MEM v inst.inst_outputs ==>
    FLOOKUP s1.vs_vars v = FLOOKUP s.vs_vars v /\
    FLOOKUP (update_var out y t).vs_vars v = FLOOKUP t.vs_vars v) /\
  (!v z. MEM v inst.inst_outputs /\ FLOOKUP s1.vs_vars v = SOME z ==>
    ?w. FLOOKUP (update_var out y t).vs_vars v = SOME w /\
      (~retpc_var fn v ==> fmp_value_rel sm (FLOOKUP (step_prov PG G inst s1) v)
        (op_taint (step_taint inst s s1 tn) (Var v)) z w))
Proof
  strip_tac >>
  simp[update_var_def, FLOOKUP_UPDATE, step_prov_def, step_taint_def,
       set_var_taint_def, op_taint_def] >>
  Cases_on `out_prov PG G inst (update_var out x s)` >>
  gvs[set_prov_def, update_var_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]
QED

Theorem fmp_copy_empty_outputs[local]:
  o1_fn_shape C fn /\ MEM inst (fn_insts fn) /\
  MEM inst.inst_opcode [NOP; ASSERT; ASSERT_UNREACHABLE] ==>
  inst.inst_outputs = []
Proof
  strip_tac >>
  `inst_wf inst` by
    (fs[o1_fn_shape_def, fn_inst_wf_def, fn_insts_def, fn_insts_blocks_MEM] >>
     metis_tac[]) >>
  fs[MEM] >> gvs[inst_wf_def]
QED

Theorem fmp_copy_param_step[local]:
  fmp_params_rel sm PG s t /\ inst.inst_opcode = PARAM /\
  step_inst k C inst s = OK s1 ==>
  ?out x y. inst.inst_outputs = [out] /\ s1 = update_var out x s /\
    step_inst k C' inst t = OK (update_var out y t) /\
    fmp_value_rel sm (out_prov PG G inst s1) (out_taint tn inst s) x y
Proof
  strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  fs[fmp_params_rel_def] >>
  `w2n idx < LENGTH t.vs_params` by decide_tac >>
  simp[out_prov_def, out_taint_def, eval_operand_def] >> metis_tac[]
QED

Theorem fmp_copy_write_step[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  MEM inst.inst_opcode [PARAM; ASSIGN] /\ step_inst k C inst s = OK s1 ==>
  ?out x y. inst.inst_outputs = [out] /\ s1 = update_var out x s /\
    step_inst k C' inst t = OK (update_var out y t) /\
    (~retpc_var fn out ==> fmp_value_rel sm
      (out_prov PG G inst s1) (out_taint tn inst s) x y)
Proof
  strip_tac >> fs[MEM]
  >- (`fmp_params_rel sm PG s t` by fs[fmp_stage_rel_def, fmp_frame_rel_def] >>
      drule_all fmp_copy_param_step >> metis_tac[]) >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule_all fmp_copy_assign_operand >> strip_tac >>
  qexistsl [`v`,`y`] >>
  simp[out_prov_def, first_prov_def, out_taint_def] >>
  Cases_on `op_prov G op1` >> gvs[]
QED

Theorem fmp_copy_idle_step[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  MEM inst.inst_opcode [NOP; ASSERT; ASSERT_UNREACHABLE] /\
  step_inst k C inst s = r /\ terminates r ==>
  ?r'. step_inst k C' inst t = r' /\
    ((r = OK s /\ r' = OK t) \/ dead_result_rel D r r')
Proof
  strip_tac >> Cases_on `inst.inst_opcode = NOP`
  >- (gvs[step_inst_non_invoke, step_inst_base_opcode_eqs] >> metis_tac[]) >>
  `!op x. MEM op inst.inst_operands /\ eval_operand op s = SOME x ==>
    eval_operand op t = SOME x` by
    metis_tac[fmp_copy_assert_operand, MEM] >>
  fs[MEM] >> qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  gvs[AllCaseEqs(), passSimulationDefsTheory.terminates_def] >>
  strip_tac >> gvs[passSimulationDefsTheory.terminates_def, MEM] >>
  simp[dead_result_rel_def] >> metis_tac[]
QED

Theorem fmp_copy_write_terminating[local]:
  MEM inst.inst_opcode [PARAM; ASSIGN] /\
  step_inst k C inst s = r /\ terminates r ==> ?s1. r = OK s1
Proof
  strip_tac >> fs[MEM] >> qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  gvs[AllCaseEqs(), passSimulationDefsTheory.terminates_def] >>
  strip_tac >> gvs[passSimulationDefsTheory.terminates_def]
QED

Theorem fmp_copy_write_post[local]:
  MEM inst.inst_opcode [PARAM; ASSIGN] /\ inst.inst_outputs = [out] /\
  s1 = update_var out x s /\ t1 = update_var out y t /\
  (~retpc_var fn out ==> fmp_value_rel sm
    (out_prov PG G inst s1) (out_taint tn inst s) x y) /\
  ld_memory_agree (fmp_ld_sites sm) eom tn.t_mem s.vs_memory t.vs_memory /\
  ld_shared_agree D s.vs_call_ctx.cc_address tn s t /\
  s.vs_returndata = t.vs_returndata /\ ~s.vs_halted /\ ~t.vs_halted ==>
  ^post
Proof
  strip_tac >>
  `(!v. ~MEM v inst.inst_outputs ==>
    FLOOKUP s1.vs_vars v = FLOOKUP s.vs_vars v /\
    FLOOKUP t1.vs_vars v = FLOOKUP t.vs_vars v) /\
   (!v z. MEM v inst.inst_outputs /\ FLOOKUP s1.vs_vars v = SOME z ==>
    ?w. FLOOKUP t1.vs_vars v = SOME w /\
      (~retpc_var fn v ==> fmp_value_rel sm (FLOOKUP (step_prov PG G inst s1) v)
        (op_taint (step_taint inst s s1 tn) (Var v)) z w))` by
    metis_tac[fmp_copy_write_value] >>
  irule fmp_copy_post >> simp[] >>
  reverse conj_tac >- gvs[MEM] >>
  qexistsl [`s1.vs_vars`,`t1.vs_vars`] >>
  gvs[update_var_def, MEM]
QED

Theorem fmp_stage_sim_copy:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~s.vs_halted /\ ~in_revert_forward fn s /\
  MEM inst.inst_opcode ^copies /\
  fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG G tn fn s lo t ts /\
  step_inst k C inst s = r /\ terminates r ==>
  ?k' r'. step_inst k' C' inst t = r' /\
    case r of
      OK s1 => ?t1. r' = OK t1 /\ ^post
    | Halt se => dead_result_rel D r r'
    | Abort ab se => dead_result_rel D r r'
    | _ => F
Proof
  strip_tac >> Cases_on `MEM inst.inst_opcode [PARAM; ASSIGN]`
  >- (drule_all fmp_copy_write_terminating >> strip_tac >>
      qpat_x_assum `r = _` SUBST_ALL_TAC >>
      drule_all fmp_copy_write_step >> strip_tac >>
      qabbrev_tac `t1 = update_var out y t` >>
      qexistsl [`k`,`OK t1`] >> simp_tac (srw_ss()) [] >>
      conj_tac >- simp[Abbr `t1`] >>
      irule fmp_copy_write_post >>
      gvs[Abbr `t1`, fmp_stage_rel_def] >> metis_tac[]) >>
  `MEM inst.inst_opcode [NOP; ASSERT; ASSERT_UNREACHABLE]` by gvs[MEM] >>
  drule_all fmp_copy_idle_step >> strip_tac
  >- (qexistsl [`k`,`OK t`] >> simp[] >>
      drule_all fmp_stage_frame_facts >> strip_tac >>
      `inst.inst_outputs = []` by metis_tac[fmp_copy_empty_outputs] >>
      `step_taint inst s s tn = tn` by
        (mp_tac (Q.INST [`s1` |-> `s`, `V` |-> `s.vs_vars`] fmp_copy_taint) >>
         simp[set_var_taint_def, DRESTRICT_UNIV]) >>
      gvs[fmp_stage_rel_def]) >>
  qexistsl [`k`,`r'`] >> simp[] >>
  Cases_on `r` >> gvs[dead_result_rel_def]
QED

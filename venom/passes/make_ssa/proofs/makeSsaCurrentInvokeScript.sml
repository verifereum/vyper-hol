Theory makeSsaCurrentInvoke
Ancestors
  makeSsaCurrentOrdinary o1PassLift makeSsaCurrentDefs venomExecSemantics passSimulationDefs
  stateFrame venomState makeSsaCurrentSimDefs

Theorem current_decode_invoke:
  inst'.inst_operands = rename_current_operands rs inst.inst_operands ==>
  decode_invoke inst' = OPTION_MAP
    (\(nm,ops). (nm,rename_current_operands rs ops)) (decode_invoke inst)
Proof
  strip_tac >> Cases_on `inst.inst_operands`
  >- simp[decode_invoke_def, rename_current_operands_def] >>
  Cases_on `h` >> simp[decode_invoke_def, rename_current_operands_def]
QED

Theorem current_setup_callee_agree:
  execution_frame st = execution_frame st' ==>
  setup_callee fn args st = setup_callee fn args st'
Proof
  simp[execution_frame_eq_reconstruct] >> strip_tac >>
  pop_assum (SUBST1_TAC o SYM) >> simp[setup_callee_def]
QED

Theorem current_merge_return_agree:
  execution_frame st = execution_frame st' /\
  execution_frame t = execution_frame t' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_name_agree rs demand st st' ==>
  execution_frame (adopt_return_fmp ret (merge_callee_state st t)) =
    execution_frame (adopt_return_fmp ret (merge_callee_state st' t')) /\
  (adopt_return_fmp ret (merge_callee_state st t)).vs_current_bb =
    (adopt_return_fmp ret (merge_callee_state st' t')).vs_current_bb /\
  (adopt_return_fmp ret (merge_callee_state st t)).vs_prev_bb =
    (adopt_return_fmp ret (merge_callee_state st' t')).vs_prev_bb /\
  current_name_agree rs demand
    (adopt_return_fmp ret (merge_callee_state st t))
    (adopt_return_fmp ret (merge_callee_state st' t'))
Proof
  strip_tac >> Cases_on `ret.iret_adopt_fmp` >>
  fs[adopt_return_fmp_def, merge_callee_state_def, current_name_agree_def,
     lookup_var_def] >>
  qpat_x_assum `execution_frame st = _` mp_tac >>
  qpat_x_assum `execution_frame t = _` mp_tac >>
  simp[execution_frame_def, venom_state_component_equality]
QED

Theorem current_invoke_result_agree:
  frame_result_rel r r' /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_outputs_compatible rs outs rt outs' demand /\
  current_name_agree rs (current_before_outputs outs demand) st st' ==>
  current_result_agree rt demand
    (invoke_result outs st r) (invoke_result outs' st' r')
Proof
  strip_tac >> Cases_on `r` >> Cases_on `r'` >>
  full_simp_tac std_ss [frame_result_rel_def,
    exec_result_case_def, pairTheory.pair_case_def] >> rpt strip_tac
  >- (asm_simp_tac std_ss [invoke_result_def, current_result_agree_def,
        exec_result_case_def, pairTheory.pair_case_def])
  >- (asm_simp_tac std_ss [invoke_result_def, current_result_agree_def,
        exec_result_case_def, pairTheory.pair_case_def]) >>
  qpat_x_assum `i' = i` SUBST_ALL_TAC >>
  `execution_frame (adopt_return_fmp i (merge_callee_state st v)) =
     execution_frame (adopt_return_fmp i (merge_callee_state st' v')) /\
   (adopt_return_fmp i (merge_callee_state st v)).vs_current_bb =
     (adopt_return_fmp i (merge_callee_state st' v')).vs_current_bb /\
   (adopt_return_fmp i (merge_callee_state st v)).vs_prev_bb =
     (adopt_return_fmp i (merge_callee_state st' v')).vs_prev_bb /\
   current_name_agree rs (current_before_outputs outs demand)
     (adopt_return_fmp i (merge_callee_state st v))
     (adopt_return_fmp i (merge_callee_state st' v'))` by
    (irule current_merge_return_agree >> asm_simp_tac std_ss []) >>
  drule current_outputs_compatible_length >> strip_tac >>
  pure_rewrite_tac [invoke_result_def, exec_result_case_def] >>
  Cases_on `bind_outputs outs i.iret_values
    (adopt_return_fmp i (merge_callee_state st v))`
  >- (fs[bind_outputs_def] >> simp[bind_outputs_def, current_result_agree_def]) >>
  Cases_on `bind_outputs outs' i.iret_values
    (adopt_return_fmp i (merge_callee_state st' v'))`
  >- (fs[bind_outputs_def] >> gvs[]) >>
  asm_simp_tac std_ss [optionTheory.option_case_def] >>
  metis_tac[current_result_bind_outputs_agree]
QED

Theorem current_invoke_agree:
  inst.inst_opcode = INVOKE /\ inst'.inst_opcode = INVOKE /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_outputs_compatible rs inst.inst_outputs rt inst'.inst_outputs demand /\
  current_name_agree rs (venomInst$operand_vars inst.inst_operands) st st' /\
  current_name_agree rs (current_before_outputs inst.inst_outputs demand) st st' ==>
  current_result_agree rt demand
    (step_inst fuel ctx inst st) (step_inst fuel ctx inst' st')
Proof
  strip_tac >> drule current_decode_invoke >> strip_tac >>
  Cases_on `decode_invoke inst`
  >- (asm_simp_tac std_ss [step_inst_def, optionTheory.OPTION_MAP_DEF,
        optionTheory.option_case_def] >>
      simp_tac std_ss [current_result_agree_def, exec_result_case_def,
        pairTheory.pair_case_def]) >>
  PairCases_on `x` >>
  `!op. MEM op x1 ==> MEM op inst.inst_operands` by
    (fs[decode_invoke_def, AllCaseEqs()] >> metis_tac[listTheory.MEM]) >>
  `eval_operands (rename_current_operands rs x1) st' = eval_operands x1 st` by
    (irule current_eval_operands_subset >> conj_tac >- asm_rewrite_tac [] >>
     qexists_tac `inst.inst_operands` >> asm_rewrite_tac []) >>
  `!fn args. setup_callee fn args st = setup_callee fn args st'` by
    metis_tac[current_setup_callee_agree] >>
  asm_simp_tac std_ss [Ntimes step_inst_def 2, optionTheory.OPTION_MAP_DEF,
    optionTheory.option_case_def, pairTheory.pair_case_def] >>
  Cases_on `lookup_function x0 ctx.ctx_functions`
  >- simp[current_result_agree_def] >>
  Cases_on `eval_operands x1 st`
  >- simp[current_result_agree_def] >>
  Cases_on `setup_callee x x' st'`
  >- simp[current_result_agree_def] >>
  asm_simp_tac std_ss [optionTheory.option_case_def] >>
  pure_rewrite_tac [GSYM invoke_result_def] >>
  Cases_on `run_blocks fuel ctx x x''`
  >- simp[invoke_result_def, current_result_agree_def]
  >- simp[invoke_result_def, current_result_agree_def]
  >- simp[invoke_result_def, current_result_agree_def]
  >- (irule current_invoke_result_agree >>
      asm_simp_tac std_ss [frame_result_rel_def, pairTheory.pair_case_def,
        exec_result_case_def] >> qexists_tac `rs` >> asm_rewrite_tac []) >>
  simp[invoke_result_def, current_result_agree_def]
QED

Theorem current_step_inst_agree:
  inst_wf inst /\ inst.inst_opcode <> PHI /\
  inst'.inst_opcode = inst.inst_opcode /\ inst'.inst_id = inst.inst_id /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_outputs_compatible rs inst.inst_outputs rt inst'.inst_outputs demand /\
  current_name_agree rs (venomInst$operand_vars inst.inst_operands) st st' /\
  current_name_agree rs (current_before_outputs inst.inst_outputs demand) st st' ==>
  current_result_agree rt demand
    (step_inst fuel ctx inst st) (step_inst fuel ctx inst' st')
Proof
  strip_tac >> Cases_on `inst.inst_opcode = INVOKE`
  >- (irule current_invoke_agree >> asm_rewrite_tac [] >>
      qexists_tac `rs` >> asm_rewrite_tac []) >>
  asm_simp_tac std_ss [step_inst_def] >>
  irule current_step_inst_base_agree >> asm_rewrite_tac [] >>
  qexists_tac `rs` >> asm_rewrite_tac []
QED

Theorem current_result_agree_step_transport:
  current_result_agree rt demand r r' /\ step_result_rel r' r'' ==>
  current_result_agree rt demand r r''
Proof
  Cases_on `r` >> Cases_on `r'` >> Cases_on `r''` >>
  simp_tac std_ss [current_result_agree_def, step_result_rel_def,
    frame_result_rel_def, pairTheory.pair_case_def, exec_result_case_def] >>
  metis_tac[]
QED

Theorem current_result_agree_terminates:
  current_result_agree rt demand r r' ==> (terminates r <=> terminates r')
Proof
  Cases_on `r` >> Cases_on `r'` >>
  simp_tac std_ss [current_result_agree_def, terminates_def,
    pairTheory.pair_case_def, exec_result_case_def] >> metis_tac[]
QED

Theorem current_result_agree_step_transport_left:
  step_result_rel r r' /\ current_result_agree rt demand r' r'' ==>
  current_result_agree rt demand r r''
Proof
  Cases_on `r` >> Cases_on `r'` >> Cases_on `r''` >>
  simp_tac std_ss [current_result_agree_def, step_result_rel_def,
    frame_result_rel_def, pairTheory.pair_case_def, exec_result_case_def] >>
  metis_tac[]
QED

Theorem current_step_inst_ctx_agree:
  ctx_bisim C C' /\ inst_wf inst /\ inst.inst_opcode <> PHI /\
  inst'.inst_opcode = inst.inst_opcode /\ inst'.inst_id = inst.inst_id /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_outputs_compatible rs inst.inst_outputs rt inst'.inst_outputs demand /\
  current_name_agree rs (venomInst$operand_vars inst.inst_operands) st st' /\
  current_name_agree rs (current_before_outputs inst.inst_outputs demand) st st' ==>
  (!fuel. terminates (step_inst fuel C inst st) ==>
    ?fuel'. current_result_agree rt demand
      (step_inst fuel C inst st) (step_inst fuel' C' inst' st')) /\
  (!fuel'. terminates (step_inst fuel' C' inst' st') ==>
    ?fuel. current_result_agree rt demand
      (step_inst fuel C inst st) (step_inst fuel' C' inst' st'))
Proof
  strip_tac >> drule ctx_bisim_step_inst >> strip_tac >>
  conj_tac >> rpt strip_tac
  >- (`current_result_agree rt demand (step_inst fuel C inst st)
         (step_inst fuel C inst' st')` by
        (irule current_step_inst_agree >> asm_rewrite_tac [] >>
         qexists_tac `rs` >> asm_rewrite_tac []) >>
      `terminates (step_inst fuel C inst' st')` by
        metis_tac[current_result_agree_terminates] >>
      first_x_assum (drule_then strip_assume_tac) >>
      qexists_tac `fuel'` >>
      metis_tac[current_result_agree_step_transport]) >>
  `current_result_agree rt demand (step_inst fuel' C' inst st)
      (step_inst fuel' C' inst' st')` by
    (irule current_step_inst_agree >> asm_rewrite_tac [] >>
     qexists_tac `rs` >> asm_rewrite_tac []) >>
  `terminates (step_inst fuel' C' inst st)` by
    metis_tac[current_result_agree_terminates] >>
  first_x_assum (drule_then strip_assume_tac) >>
  qexists_tac `fuel` >>
  metis_tac[current_result_agree_step_transport_left]
QED

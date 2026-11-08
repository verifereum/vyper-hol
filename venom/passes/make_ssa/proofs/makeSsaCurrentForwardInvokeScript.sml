Theory makeSsaCurrentForwardInvoke
Ancestors
  makeSsaCurrentForwardRuntime makeSsaCurrentReturnRuntime o1FrameLockstep
  o1PassLift venomExecSemantics stateFrame

Theorem current_exec_invoke_pair_forward:
  inst.inst_opcode = INVOKE /\ inst_pair sg inst inst' /\
  state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 ==>
  case step_inst fuel C inst st of
    OK t => ?t'. step_inst fuel C inst' st' = OK t' /\ state_rel sg1 t t'
  | Error e => T
  | r => frame_result_rel r (step_inst fuel C inst' st')
Proof
  strip_tac >>
  `inst'.inst_opcode = INVOKE` by fs[inst_pair_def] >>
  Cases_on `decode_invoke inst`
  >- simp[Once (cj 1 run_defs)] >>
  rename1 `decode_invoke inst = SOME pair` >> PairCases_on `pair` >>
  drule_all current_invoke_decode_args_pair >> strip_tac >>
  `!fn args. setup_callee fn args st' = setup_callee fn args st` by
    (rpt gen_tac >> irule setup_callee_execution_frame >> fs[state_rel_def]) >>
  simp[Once (cj 1 run_defs)] >>
  Cases_on `lookup_function pair0 C.ctx_functions` >> simp[] >>
  Cases_on `eval_operands pair1 st` >> simp[] >>
  Cases_on `setup_callee x x' st` >> simp[] >>
  Cases_on `run_blocks fuel C x x''` >>
  simp[] >> simp[Once (cj 1 run_defs)] >>
  simp[frame_result_rel_def] >>
  Cases_on `bind_outputs inst.inst_outputs i.iret_values
    (adopt_return_fmp i (merge_callee_state st v))` >> simp[] >>
  `state_rel sg (adopt_return_fmp i (merge_callee_state st v))
    (adopt_return_fmp i (merge_callee_state st' v))` by
    (irule current_return_merge_state_rel >> simp[]) >>
  drule_all current_runtime_bind_last_slots_forward >> strip_tac >> simp[]
QED

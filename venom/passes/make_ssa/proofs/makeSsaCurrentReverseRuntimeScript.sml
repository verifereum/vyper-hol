Theory makeSsaCurrentReverseRuntime
Ancestors
  o1FrameLockstep o1PassLift list venomExecSemantics passSimulationDefs contextCodegenRel venomInst venomExecProps

Theorem current_step_copy_not_abort:
  (inst.inst_opcode = ASSIGN \/ inst.inst_opcode = NOP) ==>
  step_inst fuel C inst st <> Abort a t
Proof
  strip_tac >> gvs[step_inst_non_invoke, step_inst_base_def, AllCaseEqs()]
QED

Theorem current_terminating_suffix_instruction:
  terminates (exec_block fuel C bb st) ==>
  ?inst. get_instruction bb st.vs_inst_idx = SOME inst
Proof
  Cases_on `get_instruction bb st.vs_inst_idx` >> simp[] >>
  simp[Once exec_block_def, terminates_def]
QED

Theorem current_terminating_suffix_active:
  lookup_block st.vs_current_bb fn.fn_blocks = SOME bb /\
  terminates (exec_block fuel C bb st) ==>
  ?inst. active_inst fn inst st
Proof
  strip_tac >> drule current_terminating_suffix_instruction >> strip_tac >>
  `bb.bb_label = st.vs_current_bb` by
    metis_tac[lookup_block_label] >>
  drule lookup_block_MEM >> strip_tac >>
  fs[get_instruction_def, AllCaseEqs()] >>
  qexists `inst` >> simp[active_inst_def] >> qexists `bb` >> simp[]
QED

Theorem current_invoke_pair_halt_reverse:
  inst.inst_opcode = INVOKE /\ inst_pair sg inst inst' /\
  state_rel sg st st' /\ step_inst fuel C inst' st' = Halt h ==>
  step_inst fuel C inst st = Halt h
Proof
  strip_tac >>
  `inst'.inst_opcode = INVOKE` by fs[inst_pair_def] >>
  qpat_x_assum `step_inst _ _ _ _ = Halt _` mp_tac >>
  simp[Once step_inst_def, AllCaseEqs()] >> strip_tac >>
  qpat_x_assum `_ = (_,_)` SUBST_ALL_TAC >>
  rename1 `decode_invoke inst' = SOME (nm, ops')` >>
  `?ops. inst.inst_operands = Label nm :: ops /\
         LIST_REL (op_rename sg) ops ops'` by
    (gvs[inst_pair_def, decode_invoke_def, AllCaseEqs(), LIST_REL_CONS2,
         op_rename_label] >> metis_tac[]) >>
  `decode_invoke inst = SOME (nm, ops)` by fs[decode_invoke_def] >>
  `eval_operands ops' st' = eval_operands ops st` by
    (irule eval_operands_rel >> qexists `sg` >>
     irule LIST_REL_op_rename_eval >> fs[state_rel_def]) >>
  `!fn args. setup_callee fn args st' = setup_callee fn args st` by
    (rpt gen_tac >> irule setup_callee_execution_frame >> fs[state_rel_def]) >>
  simp[Once step_inst_def] >> gvs[]
QED

Theorem current_invoke_pair_abort_reverse:
  inst.inst_opcode = INVOKE /\ inst_pair sg inst inst' /\
  state_rel sg st st' /\ step_inst fuel C inst' st' = Abort a h ==>
  step_inst fuel C inst st = Abort a h
Proof
  strip_tac >>
  `inst'.inst_opcode = INVOKE` by fs[inst_pair_def] >>
  qpat_x_assum `step_inst _ _ _ _ = Abort _ _` mp_tac >>
  simp[Once step_inst_def, AllCaseEqs()] >> strip_tac >>
  qpat_x_assum `_ = (_,_)` SUBST_ALL_TAC >>
  rename1 `decode_invoke inst' = SOME (nm, ops')` >>
  `?ops. inst.inst_operands = Label nm :: ops /\
         LIST_REL (op_rename sg) ops ops'` by
    (gvs[inst_pair_def, decode_invoke_def, AllCaseEqs(), LIST_REL_CONS2,
         op_rename_label] >> metis_tac[]) >>
  `decode_invoke inst = SOME (nm, ops)` by fs[decode_invoke_def] >>
  `eval_operands ops' st' = eval_operands ops st` by
    (irule eval_operands_rel >> qexists `sg` >>
     irule LIST_REL_op_rename_eval >> fs[state_rel_def]) >>
  `!fn args. setup_callee fn args st' = setup_callee fn args st` by
    (rpt gen_tac >> irule setup_callee_execution_frame >> fs[state_rel_def]) >>
  simp[Once step_inst_def] >> gvs[]
QED

Theorem current_invoke_pair_resume_reverse:
  lockstep_sim L C C fn fn' pos R /\
  R T (inst,st) sg (inst',st') /\ inst'.inst_opcode = INVOKE /\
  step_inst fuel C inst' st' = OK t' /\
  active_inst fn' j' (t' with vs_inst_idx := SUC st'.vs_inst_idx) ==>
  ?j t sg'. step_inst fuel C inst st = OK t /\
    R T (inst,st) sg (inst',st') /\
    (?p. R p (j,t with vs_inst_idx := SUC st.vs_inst_idx) sg'
      (j',t' with vs_inst_idx := SUC st'.vs_inst_idx))
Proof
  strip_tac >> drule_all lockstep_rel >> simp[] >> strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
  simp[Once step_inst_def, AllCaseEqs()] >> strip_tac >>
  qpat_x_assum `_ = (_,_)` SUBST_ALL_TAC >>
  rename1 `decode_invoke inst' = SOME (nm, ops')` >>
  `?ops. inst.inst_operands = Label nm :: ops /\
         LIST_REL (op_rename sg) ops ops'` by
    (gvs[inst_pair_def, decode_invoke_def, AllCaseEqs(), LIST_REL_CONS2,
         op_rename_label] >> metis_tac[]) >>
  `decode_invoke inst = SOME (nm, ops) /\ inst.inst_opcode = INVOKE` by
    fs[decode_invoke_def, inst_pair_def] >>
  `eval_operands ops' st' = eval_operands ops st` by
    (irule eval_operands_rel >> qexists `sg` >>
     irule LIST_REL_op_rename_eval >> fs[state_rel_def]) >>
  `!f args. setup_callee f args st' = setup_callee f args st` by
    (rpt gen_tac >> irule setup_callee_execution_frame >> fs[state_rel_def]) >>
  `execution_frame callee_s' = execution_frame callee_s'` by simp[] >>
  drule_all lockstep_resume >> strip_tac >>
  qexistsl [`j`, `t`, `sg'`] >> simp[Once step_inst_def] >> gvs[] >>
  metis_tac[]
QED

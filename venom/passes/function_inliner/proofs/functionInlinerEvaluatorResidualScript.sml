(* Caller residual preservation at actual internal-return evaluator boundaries. *)
Theory functionInlinerEvaluatorResidual
Ancestors
  functionInlinerSimulation opcodeClass venomInstProofs1
  venomExecSemantics venomExecProofs venomState venomInst
  functionInlinerFrame venomInstProps list

Theorem inline_caller_residual_step_return[local]:
  step_inst fuel ctx inst s = IntRet ir t ==>
  inline_caller_residual t = inline_caller_residual s /\
  t.vs_halted = s.vs_halted
Proof
  strip_tac >> gvs[step_inst_def, AllCaseEqs()] >>
  drule step_inst_base_intret_opcodes >> strip_tac >>
  gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  pairarg_tac >> gvs[] >>
  drule pack_dret_dynamic_preserves_non_memory >>
  simp[inline_caller_residual_def, inline_shared_frame_def,
       stateFrameTheory.execution_frame_def, merge_callee_state_def,
       venom_state_component_equality]
QED

Theorem inline_caller_residual_exec_block_return:
  !fuel ctx bb s ir t.
    exec_block fuel ctx bb s = IntRet ir t /\ ~s.vs_halted ==>
    inline_caller_residual t = inline_caller_residual s /\ ~t.vs_halted
Proof
  rpt gen_tac >>
  completeInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt gen_tac >> disch_tac >> strip_tac >>
  qpat_x_assum `exec_block fuel ctx bb s = IntRet ir t` mp_tac >>
  once_rewrite_tac[exec_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  Cases_on `step_inst fuel ctx inst s` >> simp[]
  >- (rename1 `step_inst fuel ctx inst s = OK u` >>
      Cases_on `is_terminator inst.inst_opcode` >> simp[]
      >- (Cases_on `u.vs_halted` >> simp[]) >>
      strip_tac >>
      `s.vs_inst_idx < LENGTH bb.bb_instructions` by
        gvs[get_instruction_def, AllCaseEqs()] >>
      `~u.vs_halted` by metis_tac[step_preserves_halted] >>
      `inline_caller_residual t =
         inline_caller_residual (u with vs_inst_idx := SUC s.vs_inst_idx) /\
       ~t.vs_halted` by
        (first_x_assum irule >> simp[] >> qexists `bb` >> simp[]) >>
      metis_tac[inline_caller_residual_step, inline_caller_residual_updates]) >>
  strip_tac >> gvs[] >>
  metis_tac[inline_caller_residual_step_return]
QED

Theorem inline_caller_residual_run_block_return:
  run_block fuel ctx bb s = IntRet ir t /\ ~s.vs_halted ==>
  inline_caller_residual t = inline_caller_residual s /\ ~t.vs_halted
Proof
  strip_tac >>
  qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac eval_phis_ok_or_error_defs >>
  gvs[run_block_def] >>
  drule eval_phis_only_updates_vs_vars >> disch_then SUBST_ALL_TAC >>
  drule inline_caller_residual_exec_block_return >> simp[]
QED

Theorem inline_caller_residual_run_blocks_return:
  !fuel ctx fn s ir t.
    run_blocks fuel ctx fn s = IntRet ir t /\ ~s.vs_halted ==>
    inline_caller_residual t = inline_caller_residual s /\ ~t.vs_halted
Proof
  Induct_on `fuel`
  >- simp[Once run_blocks_def] >>
  rpt gen_tac >> once_rewrite_tac[run_blocks_unfold] >> simp[] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
  Cases_on `run_block fuel ctx bb s` >> simp[]
  >- (rename1 `run_block fuel ctx bb s = OK u` >>
      Cases_on `u.vs_halted` >> simp[] >> strip_tac >>
      drule_all inline_caller_residual_run_block >> strip_tac >>
      first_x_assum drule >> simp[]) >>
  strip_tac >> gvs[] >>
  metis_tac[inline_caller_residual_run_block_return]
QED

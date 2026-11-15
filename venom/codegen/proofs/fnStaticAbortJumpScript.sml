Theory fnStaticAbortJump
Ancestors
  fnStaticAbortSpec fnStaticAbortBodyFacts fnBlockBodyClasses
  fnStaticAbortBoundary fnBlockBodySteps contextCodegenRel
  contextCodegenRelProps contextStaticAbortRel codegenRel frameRel
  stackPlanTypes venomExecSemantics venomExecProps venomInst venomState list

Theorem body_abort_jump_continue:
  gen_fn_frame_sim_abort_at fuel /\
  body_inv_abort rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs ast Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  is_terminator inst.inst_opcode /\
  step_inst fuel ctx inst vs = OK vs1 /\ vs1 = jump_to t vs /\
  MEM t (get_successors inst) /\
  asm_steps lo o2pc prog n ast = AsmOK as1 /\
  fn_frame_inv ctx cpl lo fn ra rest mem0 ps_after vs1 as1 /\
  (!at. MEM at ps_after.ps_stack \/ at IN FDOM ps_after.ps_spilled ==>
    operand_val (frame_view fn ra vs1) lo at =
    operand_val (frame_view fn ra vs1) lo (normalize_operand dfg [] at)) /\
  FLOOKUP lo t = SOME off /\ FLOOKUP o2pc off = SOME as1.as_pc ==>
  ~vs1.vs_halted /\
  body_result_abort lo o2pc prog cpl ctx fn mem0 pc_ret rest ast
    (run_blocks fuel ctx fn vs1)
Proof
  strip_tac >> drule body_inv_abort_plan >> strip_tac >>
  drule_all body_plan_jump_entry >> strip_tac >>
  drule body_plan_inv_facts >> strip_tac >>
  drule_all body_plan_inv_inst >> strip_tac >>
  `active_inst fn inst vs` by
    (fs[body_inv_abort_def, active_inst_def, get_instruction_def] >>
     metis_tac[lookup_block_label]) >>
  `Inv ctx fn inst vs` by
    (fs[body_inv_abort_def] >> metis_tac[]) >>
  qhdtm_assum `body_inv_abort`
    (strip_assume_tac o REWRITE_RULE [body_inv_abort_def]) >>
  `~vs1.vs_halted` by fs[fn_frame_inv_def] >>
  `vs1.vs_labels = vs.vs_labels /\ vs1.vs_call_ctx = vs.vs_call_ctx /\
   vs1.vs_current_bb = t /\ vs1.vs_prev_bb = SOME bb.bb_label` by
    (qpat_x_assum `vs1 = _` SUBST1_TAC >> simp[jump_to_def]) >>
  `fn_entry_inv Inv ctx fn vs1` by
    (rw[fn_entry_inv_def] >> drule_all reachability_closed_block >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule body_result_abort_prefix >> qexistsl [`as1`, `n`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qhdtm_x_assum `gen_fn_frame_sim_abort_at`
    (mp_tac o REWRITE_RULE [gen_fn_frame_sim_abort_at_def]) >>
  disch_then (qspecl_then
    [`rpolicy`, `unit`, `cpl`, `prog`, `ctx`, `lo`, `o2pc`, `i`, `fn`, `r`,
     `liveness`, `dfg`, `cfg`, `ch`, `growth`, `spill_base`, `lbl_ctr`,
     `fn_ops`, `ps_end`, `tbb`, `bb.bb_label`,
     `ps_tdfs with <| ps_stack := ps_after.ps_stack;
                      ps_spilled := ps_after.ps_spilled |>`,
     `ps_tdfs`, `tops`, `tafter`, `vs1`, `as1`, `Inv`, `ra`, `pc_ret`, `rest`,
     `mem0`] mp_tac) >>
  impl_tac >- (gvs[] >> metis_tac[]) >>
  simp[body_result_abort_def]
QED

Theorem body_abort_jmp_step:
  gen_fn_frame_sim_abort_at fuel /\
  body_inv_abort rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs ast Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  inst.inst_opcode = JMP /\ step_inst fuel ctx inst vs = OK vs1 ==>
  ~vs1.vs_halted /\
  body_result_abort lo o2pc prog cpl ctx fn mem0 pc_ret rest ast
    (run_blocks fuel ctx fn vs1)
Proof
  strip_tac >> drule body_inv_abort_plan >> strip_tac >>
  drule_all body_plan_jmp_step >> strip_tac >>
  `is_terminator inst.inst_opcode` by simp[is_terminator_def] >>
  drule_all body_abort_jump_continue >> simp[]
QED

Theorem body_abort_jnz_step:
  gen_fn_frame_sim_abort_at fuel /\
  body_inv_abort rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs ast Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  inst.inst_opcode = JNZ /\ step_inst fuel ctx inst vs = OK vs1 ==>
  ~vs1.vs_halted /\
  body_result_abort lo o2pc prog cpl ctx fn mem0 pc_ret rest ast
    (run_blocks fuel ctx fn vs1)
Proof
  strip_tac >> drule body_inv_abort_plan >> strip_tac >>
  drule_all body_plan_jnz_step >> strip_tac >>
  `is_terminator inst.inst_opcode` by simp[is_terminator_def] >>
  drule_all body_abort_jump_continue >> simp[]
QED

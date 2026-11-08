(* Successful internal returns preserve the ambient call context. *)
Theory lowerDloadReturnCallContext
Ancestors
  o1LowerDloadRunnerBoundary venomExecSemantics venomExecProps venomExecProofs
  venomState venomInst list opcodeClass venomInstProofs1

Theorem ld_step_intret_call_ctx:
  step_inst fuel C inst s = IntRet ir se ==> se.vs_call_ctx = s.vs_call_ctx
Proof
  strip_tac >> Cases_on `inst.inst_opcode = INVOKE`
  >- (gvs[Once step_inst_def, AllCaseEqs()]) >>
  `step_inst_base inst s = IntRet ir se` by gvs[Once step_inst_def] >>
  drule step_inst_base_intret_opcodes >> strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  simp[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  drule pack_dret_dynamic_preserves_non_memory >> simp[]
QED

Theorem ld_exec_block_return_call_ctx:
  !fuel C bb s se.
    (exec_block fuel C bb s = OK se \/
     (?ir. exec_block fuel C bb s = IntRet ir se)) ==>
    se.vs_call_ctx = s.vs_call_ctx
Proof
  completeInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt strip_tac >>
  qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  simp[Once exec_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  Cases_on `step_inst fuel C inst s` >> simp[]
  >> TRY (rename1 `step_inst fuel C inst s = OK sm` >>
      drule ld_step_ok_call_ctx >> strip_tac >>
      Cases_on `is_terminator inst.inst_opcode` >> simp[]
      >- (Cases_on `sm.vs_halted` >> simp[] >> rpt strip_tac >> gvs[]) >>
      strip_tac >>
      first_x_assum (qspec_then
        `LENGTH bb.bb_instructions - SUC s.vs_inst_idx` mp_tac) >>
      (impl_tac >- (gvs[get_instruction_def, AllCaseEqs()] >> simp[])) >>
      disch_then (qspecl_then [`bb`,
        `sm with vs_inst_idx := SUC s.vs_inst_idx`] mp_tac) >>
      simp[] >> disch_then (qspecl_then [`fuel`, `C`, `se`] mp_tac) >>
      simp[] >> NO_TAC) >>
  rpt strip_tac >> gvs[] >> drule ld_step_intret_call_ctx >> simp[]
QED

Theorem ld_run_blocks_intret_call_ctx:
  !fuel C fn s ir se.
    run_blocks fuel C fn s = IntRet ir se ==>
    se.vs_call_ctx = s.vs_call_ctx
Proof
  Induct_on `fuel` >- simp[Once run_blocks_def] >>
  rpt gen_tac >> simp[Once run_blocks_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
  qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac
    eval_phis_ok_or_error_defs >> simp[] >>
  rename1 `eval_phis s bb.bb_instructions = OK sp` >>
  `sp.vs_call_ctx = s.vs_call_ctx` by
    (drule eval_phis_only_updates_vs_vars >>
     disch_then (fn th => once_rewrite_tac[th]) >> simp[]) >>
  Cases_on `exec_block fuel C bb
    (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >> simp[]
  >- (rename1 `exec_block _ _ _ _ = OK sm` >>
      `sm.vs_call_ctx = sp.vs_call_ctx` by
        (imp_res_tac ld_exec_block_return_call_ctx >> gvs[]) >>
      Cases_on `sm.vs_halted` >> simp[] >>
      strip_tac >> first_x_assum drule >> simp[]) >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac ld_exec_block_return_call_ctx >> gvs[]
QED

Theorem ld_setup_return_call_ctx:
  setup_callee fn args caller = SOME cs /\
  run_blocks fuel C fn cs = IntRet ir se ==>
  se.vs_call_ctx = caller.vs_call_ctx
Proof
  strip_tac >> drule ld_run_blocks_intret_call_ctx >>
  drule ld_setup_callee_call_ctx >> simp[]
QED

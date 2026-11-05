Theory dftNativeTerminal
Ancestors
  o1PassContract opcodeClass venomExecSemantics dftOpenAdequacy
  passSimulationDefs venomInst venomExecProofs list pred_set arithmetic
  o1PassLift o1ScheduleDecompHelpers venomWf

Theorem dft_step_no_internal_return:
  inst.inst_opcode NOTIN {RET; RETFMP; DRET} ==>
  step_inst fuel C inst s <> IntRet ret t
Proof
  strip_tac >> Cases_on `inst.inst_opcode = INVOKE`
  >- (simp[step_inst_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[AllCaseEqs()]) >>
  simp[step_inst_non_invoke] >> strip_tac >>
  drule step_inst_base_intret_opcodes >> gvs[]
QED

Theorem dft_exec_block_no_internal_return:
  !s. EVERY (\inst. inst.inst_opcode NOTIN {RET; RETFMP; DRET}) bb.bb_instructions ==>
  exec_block fuel C bb s <> IntRet ret t
Proof
  measureInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt strip_tac >>
  qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  simp[Once exec_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
  rename1 `SOME inst` >>
  `MEM inst bb.bb_instructions /\ s.vs_inst_idx < LENGTH bb.bb_instructions` by
    gvs[get_instruction_def, EL_MEM] >>
  `step_inst fuel C inst s <> IntRet ret t` by
    (irule dft_step_no_internal_return >> gvs[EVERY_MEM] >> metis_tac[]) >>
  Cases_on `step_inst fuel C inst s` >> simp[] >>
  Cases_on `is_terminator inst.inst_opcode`
  >- (Cases_on `v'.vs_halted` >> simp[]) >>
  simp[] >> first_x_assum irule >> simp[]
QED

Theorem dft_run_blocks_no_internal_return:
  !fuel s. entry_fn_no_return fn ==> run_blocks fuel C fn s <> IntRet ret t
Proof
  Induct_on `fuel` >> rpt gen_tac >> disch_tac
  >- simp[Once run_blocks_def] >>
  simp[run_blocks_unfold] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  rename1 `SOME bb` >>
  `EVERY (\inst. inst.inst_opcode NOTIN {RET; RETFMP; DRET}) bb.bb_instructions` by
    (gvs[entry_fn_no_return_def, EVERY_MEM, fn_insts_def, fn_insts_blocks_MEM] >>
     metis_tac[lookup_block_MEM]) >>
  `!s. run_block fuel C bb s <> IntRet ret t` by
    (gen_tac >> simp[run_block_def] >>
     qspecl_then [`s'`, `bb.bb_instructions`] strip_assume_tac
       eval_phis_ok_or_error_defs >> simp[] >>
     metis_tac[dft_exec_block_no_internal_return]) >>
  Cases_on `run_block fuel C bb s` >> gvs[]
  >- (rename1 `run_block_entry _ _ _ _ = OK after` >>
      Cases_on `after.vs_halted` >> simp[]) >>
  metis_tac[]
QED

Theorem dft_shaped_context_external_terminal:
  o1_ctx_shape C ==> !s fuel.
  terminates (run_context fuel C s) ==>
  (?t. run_context fuel C s = Halt t) \/
  (?z t. run_context fuel C s = Abort z t)
Proof
  strip_tac >> rpt gen_tac >>
  simp[run_context_def] >>
  Cases_on `C.ctx_entry` >> simp[terminates_def] >>
  Cases_on `lookup_function x C.ctx_functions` >> simp[terminates_def] >>
  rename1 `SOME fn` >>
  `MEM fn C.ctx_functions /\ fn.fn_name = x` by
    (irule (iffLR lookup_function_member_iff) >>
     gvs[o1_ctx_shape_def, ctx_wf_def, ctx_distinct_fn_names_def,
         ctx_fn_names_def]) >>
  `entry_fn_no_return fn` by
    (gvs[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def] >> metis_tac[]) >>
  simp[run_function_def] >>
  Cases_on `fn_entry_label fn` >> simp[terminates_def] >>
  rename1 `SOME lbl` >>
  qmatch_goalsub_abbrev_tac `run_blocks fuel C fn start` >>
  `!ret t. run_blocks fuel C fn start <> IntRet ret t` by
    metis_tac[dft_run_blocks_no_internal_return] >>
  `!t. run_blocks fuel C fn start <> OK t` by
    metis_tac[run_blocks_not_OK] >>
  Cases_on `run_blocks fuel C fn start` >> gvs[terminates_def]
QED

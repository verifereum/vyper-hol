Theory fmpStageFmpStepsRetpcLayout
Ancestors
  fmpStageRel fmpStageControl fmpStageOpBase fmpStepLayout
  fmpLowerProps fmpLowerSequenceExec venomExecProofs
  fmpLowerDefs callLayoutDefs contextCodegenRel venomExecSemantics analysisSimDefs
  venomState venomInst words list rich_list finite_map

Theorem fmp_retpc_user_arity:
  fmp_stage_lowered infos ctx runner fn fn' /\
  fn.fn_fmp_signature = NONE ==>
  LENGTH (fn_user_param_insts fn) < dimword (:256) /\
  ?users pc tail. split_fmp_entry fn = SOME (FmpEntryLayout users pc tail)
Proof
  simp[fmp_stage_lowered_def] >> strip_tac >>
  gvs[fmp_lower_function_with_info_def, AllCaseEqs(), fmp_lower_input_def] >>
  Cases_on `split_fmp_entry fn` >> gvs[] >> Cases_on `x` >> metis_tac[]
QED

Theorem fmp_retpc_single_run:
  lookup_function name C.ctx_functions = SOME fn /\
  lookup_block t.vs_current_bb fn.fn_blocks = SOME bb /\
  DROP t.vs_inst_idx bb.bb_instructions = inst::tail /\
  inst.inst_opcode = RETPC_PARAM /\ inst.inst_operands = [Lit w] /\
  inst.inst_outputs = [pc] ==>
  !fuel. fmp_target_run fuel C name t 1
    ((update_var pc t.vs_return_pc_token t) with
      vs_inst_idx := t.vs_inst_idx + 1)
Proof
  rpt strip_tac >> simp[fmp_target_run_def] >>
  qexists `update_var pc t.vs_return_pc_token t` >>
  conj_tac
  >- (qpat_x_assum `DROP _ _ = _` (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >>
      simp[LENGTH_DROP]) >>
  gvs[run_insts_def, step_inst_non_invoke, step_inst_base_opcode_eqs]
QED

Theorem fmp_retpc_root_run:
  lookup_function name C.ctx_functions = SOME fn /\
  lookup_block t.vs_current_bb fn.fn_blocks = SOME bb /\
  DROP t.vs_inst_idx bb.bb_instructions =
    mk_inst id FMP_PARAM [Lit (n2w n)] [runner] ::
    set_param_index (SUC n) inst :: tail /\
  inst.inst_opcode = RETPC_PARAM /\ inst.inst_outputs = [pc] /\
  n < LENGTH t.vs_params /\ n < dimword (:256) /\
  EL n t.vs_params = n2w lo ==>
  !fuel. fmp_target_run fuel C name t 2
    ((update_var pc t.vs_return_pc_token (update_var runner (n2w lo) t)) with
      vs_inst_idx := t.vs_inst_idx + 2)
Proof
  rpt strip_tac >> simp[fmp_target_run_def] >>
  qexists `update_var pc t.vs_return_pc_token (update_var runner (n2w lo) t)` >>
  conj_tac
  >- (qpat_x_assum `DROP _ _ = _` (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >>
      simp[LENGTH_DROP]) >>
  gvs[fmp_root_fmp_param_exec]
QED

Theorem fmp_retpc_split_tail[local]:
  !xs k acc users pc tail.
  split_fmp_entry_from k acc xs = SOME (FmpEntryLayout users pc tail) ==>
  no_param_insts tail /\
  (pc = NONE \/ ?i. pc = SOME i /\ i.inst_opcode = RETPC_PARAM)
Proof
  Induct_on `xs` >>
  simp[split_fmp_entry_from_def, no_param_insts_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> metis_tac[no_param_insts_def]
QED


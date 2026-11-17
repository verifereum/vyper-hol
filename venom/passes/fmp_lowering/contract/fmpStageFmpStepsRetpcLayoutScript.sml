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

Theorem fmp_retpc_index[local]:
  !users j pc tail inst.
  EVERY (\i. i.inst_opcode = PARAM) users /\ no_param_insts tail /\
  j < LENGTH (users ++ option_CASE pc [] (\i. [i]) ++ tail) /\
  EL j (users ++ option_CASE pc [] (\i. [i]) ++ tail) = inst /\
  inst.inst_opcode = RETPC_PARAM ==>
  pc = SOME inst /\ j = LENGTH users
Proof
  Induct_on `users`
  >- (rpt gen_tac >> Cases_on `pc`
      >- (rpt strip_tac >> gvs[no_param_insts_def, EVERY_EL] >>
          metis_tac[is_param_opcode_def]) >>
      Cases_on `j` >> rpt strip_tac >> gvs[] >>
      fs[no_param_insts_def, EVERY_EL] >>
      `n < LENGTH tail` by decide_tac >>
      metis_tac[is_param_opcode_def]) >>
  rpt gen_tac >> Cases_on `j`
  >- (rpt strip_tac >> fs[NoAsms]) >>
  simp_tac (srw_ss()) [EVERY_DEF, APPEND, LENGTH, EL] >>
  rpt strip_tac >> first_x_assum drule >>
  disch_then (qspecl_then [`n`, `pc`, `tail`, `inst`] mp_tac) >>
  simp[]
QED

Theorem fmp_retpc_entry_block[local]:
  canonical_param_prefix fn /\ active_inst fn inst s /\
  inst.inst_opcode = RETPC_PARAM ==>
  ?entry rest. fn.fn_blocks = entry::rest /\
    s.vs_current_bb = entry.bb_label /\
    s.vs_inst_idx < LENGTH entry.bb_instructions /\
    EL s.vs_inst_idx entry.bb_instructions = inst
Proof
  Cases_on `fn.fn_blocks` >> simp[canonical_param_prefix_def] >>
  rpt strip_tac >> gvs[active_inst_def] >>
  Cases_on `bb = h`
  >- (gvs[] >> metis_tac[]) >>
  `MEM bb t` by gvs[] >>
  `no_param_insts bb.bb_instructions` by fs[EVERY_MEM] >>
  fs[no_param_insts_def, EVERY_EL] >>
  metis_tac[is_param_opcode_def]
QED

Theorem fmp_retpc_prefix_at[local]:
  !users k inst tail.
  EVERY (\i. i.inst_opcode = PARAM) users /\
  canonical_entry_params_from k (users ++ inst::tail) /\
  inst.inst_opcode = RETPC_PARAM ==>
  param_inst_at (k + LENGTH users) inst
Proof
  Induct_on `users` >> simp[canonical_entry_params_from_def] >>
  rpt strip_tac >> gvs[] >> first_x_assum drule >>
  simp[arithmeticTheory.ADD_CLAUSES]
QED

Theorem fmp_retpc_split_location:
  canonical_param_prefix fn /\ active_inst fn inst s /\
  inst.inst_opcode = RETPC_PARAM /\
  split_fmp_entry fn = SOME (FmpEntryLayout users pc tail) ==>
  pc = SOME inst /\ s.vs_inst_idx = LENGTH users /\
  users = fn_user_param_insts fn /\
  s.vs_current_bb = (HD fn.fn_blocks).bb_label /\
  inst.inst_operands = [Lit (n2w (LENGTH users))] /\
  ?v. inst.inst_outputs = [v]
Proof
  rpt gen_tac >> disch_then strip_assume_tac >>
  drule_all fmp_retpc_entry_block >> strip_tac >>
  drule split_fmp_entry_users >> strip_tac >>
  `no_param_insts tail` by
    (fs[split_fmp_entry_def] >> drule fmp_retpc_split_tail >> simp[]) >>
  drule split_fmp_entry_reconstruct >> strip_tac >> fs[] >>
  `pc = SOME inst /\ s.vs_inst_idx = LENGTH users` by
    (irule fmp_retpc_index >> simp[] >> qexists `tail` >> gvs[]) >>
  gvs[] >>
  `param_inst_at (LENGTH users) inst` by
    (qspec_then `users` (qspec_then `0` mp_tac) fmp_retpc_prefix_at >>
     simp[] >> disch_then irule >> simp[] >> qexists `tail` >>
     gvs[canonical_param_prefix_def] >>
     metis_tac[APPEND, APPEND_ASSOC]) >>
  `FILTER (\i. i.inst_opcode = PARAM) tail = []` by
    (simp[FILTER_EQ_NIL] >> fs[no_param_insts_def, EVERY_MEM] >>
     metis_tac[is_param_opcode_def]) >>
  `FILTER (\i. i.inst_opcode = PARAM) users = users` by
    simp[FILTER_EQ_ID] >>
  fs[fn_user_param_insts_def, fn_entry_insts_def, entry_block_def,
     FILTER_APPEND, param_inst_at_def] >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  Cases_on `t` >> gvs[]
QED

Theory fmpStageFmpStepsDallocaExec
Ancestors
  fmpStageRel fmpStageOpBase fmpStageReclaimSound fmpStageControl
  fmpLowerSequenceExec ptrStaticDiscipline unitMemInv frameViewFacts
  venomExecSemantics venomState words list finite_map passSimulationDefs

Theorem fmp_dalloca_source:
  inst.inst_opcode = DALLOCA /\ dalloca_no_wrap inst s /\
  step_inst k C inst s = r /\ terminates r ==>
  ?size_op sz out s1.
    inst.inst_operands = [size_op] /\ inst.inst_outputs = [out] /\
    eval_operand size_op s = SOME sz /\ r = OK s1 /\
    s1 = update_var out s.vs_fmp
      (s with vs_fmp := n2w (w2n s.vs_fmp + ceil32 (w2n sz))) /\
    w2n s.vs_fmp + ceil32 (w2n sz) < dimword (:256)
Proof
  strip_tac >>
  gvs[step_inst_non_invoke, step_inst_base_def, AllCaseEqs(), terminates_def] >>
  gvs[dalloca_no_wrap_def] >>
  simp[GSYM word_add_n2w, WORD_ADD_COMM]
QED

Theorem fmp_dalloca_operand_untainted:
  taint_ok fn tn inst s /\ inst.inst_opcode = DALLOCA /\
  MEM op inst.inst_operands ==> op_taint tn op = {}
Proof
  strip_tac >> gvs[ptrDisciplineTheory.taint_ok_def] >>
  first_x_assum (qspec_then `op` mp_tac) >> simp[]
QED

Theorem fmp_dalloca_operand_noprov:
  ptr_use_static_ok P pv inst /\ FDOM G SUBSET pv /\
  inst.inst_opcode = DALLOCA /\ MEM op inst.inst_operands ==>
  op_prov G op = NONE
Proof
  strip_tac >> Cases_on `op` >> simp[ptrDisciplineTheory.op_prov_def] >>
  gvs[ptr_use_static_ok_def, pointerConfinedDefsTheory.is_pointer_preserving_op_def,
      memLocDefsTheory.mem_write_ops_def, memLocDefsTheory.mem_read_ops_def] >>
  metis_tac[finite_mapTheory.FLOOKUP_DEF, pred_setTheory.SUBSET_DEF]
QED

Theorem fmp_dalloca_size_agree:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  inst.inst_opcode = DALLOCA /\ MEM op inst.inst_operands /\
  eval_operand op s = SOME sz ==> eval_operand op t = SOME sz
Proof
  strip_tac >> drule_all fmp_stage_frame_facts >> strip_tac >>
  `op_taint tn op = {}` by metis_tac[fmp_dalloca_operand_untainted] >>
  `FDOM G SUBSET fn_pv P fn` by metis_tac[fmp_stage_prov_support] >>
  `ptr_use_static_ok P (fn_pv P fn) inst` by
    (gvs[EVERY_MEM, fn_static_ptr_ok_def] >> metis_tac[]) >>
  `op_prov G op = NONE` by metis_tac[fmp_dalloca_operand_noprov] >>
  `!v. op = Var v ==> ~retpc_var fn v` by
    (gen_tac >> disch_tac >>
     irule ordinary_operand_not_retpc >>
     conj_tac >- gvs[o1PassContractTheory.o1_fn_shape_def,
                     unitShapeDefsTheory.fn_shape_ok_def] >>
     qexists_tac `inst` >> gvs[]) >>
  `inst.inst_opcode <> PHI` by simp[] >>
  drule_all fmp_stage_operand >> simp[] >> strip_tac >>
  gvs[fmp_value_rel_def,
      o1LowerDloadRelocationKernelTheory.ld_value_agree_def] >>
  metis_tac[frameRelocationGuardedValuesTheory.word_agree_except_empty]
QED

Theorem fmp_dalloca_scan_needs[local]:
  !insts. MEM inst insts /\ inst.inst_opcode = DALLOCA ==>
  (fmp_scan_insts insts).fi_needs_fmp
Proof
  Induct >> simp[fmpAnalysisDefsTheory.fmp_scan_insts_def,
    fmpAnalysisDefsTheory.fmp_info_join_def,
    fmpAnalysisDefsTheory.fmp_opcode_needs_fmp_def] >> metis_tac[]
QED

Theorem fmp_dalloca_lowered_needs:
  fmp_stage_lowered infos ctx runner fn fn' /\
  fn.fn_fmp_signature = NONE /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = DALLOCA ==>
  ?info. FLOOKUP infos fn.fn_name = SOME info /\ info.fi_needs_fmp
Proof
  strip_tac >>
  `fmp_info_valid ctx infos /\ fmp_lower_input infos ctx fn` by
    gvs[fmp_stage_lowered_def, fmpLowerDefsTheory.fmp_lower_function_with_info_def,
        AllCaseEqs()] >>
  `MEM fn ctx.ctx_functions` by
    (gvs[fmpLowerDefsTheory.fmp_lower_input_def] >>
     metis_tac[venomInstTheory.lookup_function_MEM]) >>
  `?targets info. fmp_function_targets ctx fn = SOME targets /\
    FLOOKUP infos fn.fn_name = SOME info /\
    fmp_join_target_info infos targets (fmp_direct_info fn) = SOME info` by
      metis_tac[fmpAnalysisDefsTheory.fmp_info_valid_def] >>
  drule fmpAnalysisPropsTheory.fmp_join_target_info_needs_iff >>
  simp[fmpAnalysisDefsTheory.fmp_direct_info_def] >>
  metis_tac[fmp_dalloca_scan_needs]
QED

Theorem fmp_dalloca_root_exists:
  fmp_stage_lowered infos ctx runner fn fn' /\
  fn.fn_fmp_signature = NONE /\ FLOOKUP infos fn.fn_name = SOME info /\
  info.fi_needs_fmp ==>
  ?rl rp. fmp_stage_root infos ctx fn = SOME (rl,rp)
Proof
  strip_tac >>
  `IS_SOME (split_fmp_entry fn)` by
    gvs[fmp_stage_lowered_def, fmpLowerDefsTheory.fmp_lower_function_with_info_def,
        fmpLowerDefsTheory.fmp_lower_input_def, AllCaseEqs(), optionTheory.IS_SOME_EXISTS] >>
  Cases_on `split_fmp_entry fn` >> gvs[] >> Cases_on `x` >>
  drule fmpStepLayoutTheory.split_fmp_entry_reconstruct >> strip_tac >>
  simp[fmp_stage_root_def] >> Cases_on `fn_is_context_entry ctx fn` >> simp[]
QED

Theorem fmp_dalloca_past_root:
  fmp_stage_lowered infos ctx runner fn fn' /\
  fmp_stage_root infos ctx fn = SOME (rl,rp) /\
  lookup_block rl fn.fn_blocks = SOME bb /\
  idx < LENGTH bb.bb_instructions /\
  (EL idx bb.bb_instructions).inst_opcode = DALLOCA ==>
  rp <= idx
Proof
  strip_tac >>
  gvs[fmp_stage_root_def, AllCaseEqs()] >>
  drule fmpStepLayoutTheory.split_fmp_entry_reconstruct >> strip_tac >>
  drule fmpStepLayoutTheory.split_fmp_entry_parameter_prefix >> strip_tac >>
  gvs[venomInstTheory.lookup_block_def, listTheory.FIND_thm] >>
  `~fn_is_context_entry ctx fn ==> retpc <> NONE` by
    (gvs[fmp_stage_lowered_def,
         fmpLowerDefsTheory.fmp_lower_function_with_info_def,
         fmpLowerDefsTheory.fmp_make_root_layout_def, AllCaseEqs()] >>
     Cases_on `retpc` >> gvs[]) >>
  `LENGTH (users ++ option_CASE retpc [] (\i. [i])) <= idx` suffices_by
    (Cases_on `retpc` >> gvs[callLayoutDefsTheory.OPTION_TO_LIST_def]) >>
  CCONTR_TAC >>
  `idx < LENGTH (users ++ option_CASE retpc [] (\i. [i]))` by decide_tac >>
  gvs[EL_APPEND_EQN, EVERY_EL] >>
  (Cases_on `idx < LENGTH users`
  >- (gvs[] >>
      qpat_x_assum `!n. n < LENGTH users ==> _`
        (qspec_then `idx` mp_tac) >> simp[]) >>
  gvs[] >>
  `idx - LENGTH users < LENGTH (option_CASE retpc [] (\i. [i]))` by decide_tac >>
  qpat_x_assum `!n. n < LENGTH (option_CASE retpc [] (\i. [i])) ==> _`
    (qspec_then `idx - LENGTH users` mp_tac) >> simp[])
QED

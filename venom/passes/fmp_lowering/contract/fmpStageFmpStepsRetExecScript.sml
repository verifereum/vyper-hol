Theory fmpStageFmpStepsRetExec
Ancestors
  fmpStageOpBase fmpStageControl fmpStageRel ptrStaticDiscipline ptrDiscipline
  o1LowerDloadGhost o1LowerDloadOpaque o1LowerDloadRelocationKernel
  o1PassContract unitShapeDefs pointerConfinedDefs memLocDefs
  contextCodegenRel venomExecSemantics venomState venomInst venomExecProofs
  opcodeClass frameRelocationGuardedValues finite_map pred_set list rich_list
  fmpStepLayout fmpLowerDefs fmpLowerProps venomWf

Theorem fmp_ret_static_no_provenance[local]:
  ptr_use_static_ok P pv inst /\ FDOM G SUBSET pv /\
  inst.inst_opcode = RET /\ MEM op inst.inst_operands ==>
  op_prov G op = NONE
Proof
  strip_tac >> Cases_on `op` >> simp[op_prov_def] >>
  rename1 `FLOOKUP G v` >> Cases_on `FLOOKUP G v` >> simp[] >>
  `v IN pv` by (fs[SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]) >>
  gvs[ptr_use_static_ok_def, is_pointer_preserving_op_def,
      mem_read_ops_def, mem_write_ops_def] >> metis_tac[]
QED

Theorem fmp_stage_ret_source:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  step_inst k C inst s = IntRet ret s_end ==>
  inst.inst_opcode = RET /\ s_end = s /\ ret.iret_adopt_fmp = NONE /\
  ?vals. eval_operands inst.inst_operands s = SOME vals /\ vals <> [] /\
         ret.iret_values = FRONT vals
Proof
  strip_tac >> drule_all fmp_stage_frame_facts >> strip_tac >>
  `step_inst_base inst s = IntRet ret s_end` by
    (qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
     simp[Once step_inst_def] >> IF_CASES_TAC >> simp[AllCaseEqs()]) >>
  drule step_inst_base_intret_opcodes >> strip_tac >>
  `inst.inst_opcode = RET` by
    (gvs[EVERY_MEM, fn_static_ptr_ok_def] >> metis_tac[]) >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[step_inst_base_def] >>
  Cases_on `eval_operands inst.inst_operands s` >> simp[] >>
  rename1 `SOME vals` >> Cases_on `vals` >> simp[] >> strip_tac >> gvs[]
QED

Theorem fmp_stage_ret_operand[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom T stk PG G tn fn s lo t ts /\
  inst.inst_opcode = RET /\ inst.inst_operands <> [] /\
  MEM op (FRONT inst.inst_operands) /\ eval_operand op s = SOME x ==>
  eval_operand op t = SOME x
Proof
  strip_tac >> drule_all fmp_stage_frame_facts >> strip_tac >>
  `MEM op inst.inst_operands` by metis_tac[MEM_FRONT_NOT_NIL] >>
  `!v. op = Var v ==> ~retpc_var fn v` by
    (rpt strip_tac >>
     gvs[o1_fn_shape_def, fn_shape_ok_def] >> metis_tac[ret_front_non_retpc]) >>
  `op_taint tn op = {}` by metis_tac[ret_operand_untainted] >>
  `FDOM G SUBSET fn_pv P fn` by metis_tac[fmp_stage_prov_support] >>
  `ptr_use_static_ok P (fn_pv P fn) inst` by
    (gvs[EVERY_MEM, fn_static_ptr_ok_def] >> metis_tac[]) >>
  `op_prov G op = NONE` by metis_tac[fmp_ret_static_no_provenance] >>
  `inst.inst_opcode <> PHI` by simp[] >>
  drule_all fmp_stage_operand >> simp[] >>
  simp[fmp_value_rel_def, ld_value_agree_def] >>
  metis_tac[word_agree_except_empty]
QED

Theorem fmp_env_operand_defined[local]:
  fmp_env_rel sm fn live G tv s t /\ s.vs_labels = t.vs_labels /\
  IS_SOME (eval_operand op s) ==> IS_SOME (eval_operand op t)
Proof
  strip_tac >> Cases_on `op` >>
  gvs[eval_operand_def, lookup_var_def, fmp_env_rel_def] >>
  metis_tac[optionTheory.IS_SOME_EXISTS]
QED

Theorem fmp_stage_ret_values[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom T stk PG G tn fn s lo t ts /\
  step_inst k C inst s = IntRet ret s_end ==>
  s_end = s /\ ret.iret_adopt_fmp = NONE /\
  ?ret'. ret'.iret_values = ret.iret_values /\ ret'.iret_adopt_fmp = NONE /\
    !k'. step_inst k' C' inst t = IntRet ret' t
Proof
  strip_tac >> drule_all fmp_stage_ret_source >> strip_tac >> simp[] >>
  `inst.inst_operands <> []` by
    (strip_tac >> gvs[eval_operands_def]) >>
  `!op. MEM op inst.inst_operands ==> IS_SOME (eval_operand op s)` by
    (`IS_SOME (eval_operands inst.inst_operands s)` by simp[] >>
     fs[eval_operands_IS_SOME_EVERY, EVERY_MEM]) >>
  `fmp_env_rel sm fn
     (live_vars_at (liveness_analyze fn) s.vs_current_bb s.vs_inst_idx)
     G tn.t_var s t /\ s.vs_labels = t.vs_labels` by
    (gvs[fmp_stage_rel_def, fmp_frame_rel_def] >> metis_tac[]) >>
  `!op. MEM op inst.inst_operands ==>
    (IS_SOME (eval_operand op s) <=> IS_SOME (eval_operand op t))` by
    metis_tac[fmp_env_operand_defined] >>
  `!op. MEM op (FRONT inst.inst_operands) ==>
    eval_operand op s = eval_operand op t` by
    (rpt strip_tac >>
     `IS_SOME (eval_operand op s)` by metis_tac[MEM_FRONT_NOT_NIL] >>
     Cases_on `eval_operand op s` >> gvs[] >>
     metis_tac[fmp_stage_ret_operand]) >>
  `step_inst_base inst s = IntRet ret s` by
    (qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
     gvs[step_inst_non_invoke]) >>
  drule_all ret_front_transfer >> strip_tac >>
  qexists `jr` >> simp[step_inst_non_invoke]
QED

Theorem fmp_stage_lowered_labels[local]:
  fmp_stage_lowered infos ctx runner fn fn' ==> fn_labels fn' = fn_labels fn
Proof
  simp[fmp_stage_lowered_def, fmp_lower_function_with_info_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  drule fmp_checked_seal_some >> strip_tac >>
  gvs[fmp_seal_def, fn_labels_def] >>
  drule fmp_install_root_preserves_labels >>
  drule fmp_lower_blocks_preserves_labels >> simp[]
QED

Theorem fmp_stage_ret_kept[local]:
  wf_function fn /\ active_inst fn inst s /\ inst.inst_opcode = RET /\
  fmp_frame_rel sm fmp0 raw0 eb elo lo T fn fn' PG G tv s t /\
  active_inst fn' inst' t ==> inst' = inst
Proof
  strip_tac >>
  `ALL_DISTINCT (fn_labels fn)` by fs[wf_function_def] >>
  fs[active_inst_def] >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by
    metis_tac[wf_lookup_block] >>
  qpat_x_assum `fmp_frame_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[fmp_frame_rel_def] >> strip_tac >>
  `fn_labels fn' = fn_labels fn` by metis_tac[fmp_stage_lowered_labels] >>
  `lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb'` by
    (irule MEM_lookup_block >> fs[fn_labels_def]) >>
  `~MEM inst.inst_opcode [DALLOCA; INVOKE; RETPC_PARAM] /\
   pre_fmp_opcode inst.inst_opcode` by simp[pre_fmp_opcode_def] >>
  `inst = EL s.vs_inst_idx bb.bb_instructions` by simp[] >>
  drule_all fmp_stage_kept_inst >> strip_tac >> gvs[]
QED

Theorem fmp_stage_ret_exec:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~s.vs_halted /\
  fmp_stage_rel D C' sm fmp0 raw0 eom T stk PG G tn fn s lo t ts /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  active_inst fn' inst' t /\ step_inst k C inst s = IntRet ret s_end ==>
  inst.inst_opcode = RET /\ s_end = s /\ ret.iret_adopt_fmp = NONE /\
  ?ret'. ret'.iret_values = ret.iret_values /\ ret'.iret_adopt_fmp = NONE /\
    !k'. step_inst k' C' inst' t = IntRet ret' t
Proof
  strip_tac >> drule_all fmp_stage_ret_source >> strip_tac >>
  `wf_function fn` by
    (drule_all fmp_stage_frame_facts >> simp[o1_fn_shape_def]) >>
  `inst' = inst` by
    (irule fmp_stage_ret_kept >>
     fs[fmp_stage_rel_def] >> metis_tac[]) >>
  gvs[] >> metis_tac[fmp_stage_ret_values]
QED

(*
 * The source RET of FmpLowering's stage simulation and its target
 * counterpart: the target runs the same RET, with the same values.
 *
 * TOP-LEVEL:
 *   fmp_stage_ret_source - a returning source step is a RET
 *   fmp_stage_ret_exec   - the target's active RET returns the same values
 *)
Theory fmpStageFmpStepsRetExec
Ancestors
  fmpStageRetStep fmpStageRunnerFacts fmpStageOpBase fmpStageControl fmpStageRel ptrDiscipline
  ptrStaticDiscipline
  o1PassContract contextCodegenRel venomExecSemantics venomState venomInst
  venomExecProofs opcodeClass list fmpStepLayout fmpLowerDefs fmpLowerProps
  venomWf

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
  `fn_labels fn' = fn_labels fn` by metis_tac[fmp_stage_lowered_shape] >>
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
  gvs[] >> drule_all fmp_stage_ret_step >> strip_tac >>
  qexists `jr` >> simp[]
QED

(* Pointwise RET constructor for the bounded FMP simulation.  No whole-run
   stage context is assumed; the bounded caller supplies the current facts. *)
Theory gasFocusFmpRetPoint
Ancestors fmpStageRetStep[qualified]
  fmpStageRel fmpStageControl fmpLowerDefs fmpLowerProps
  o1LowerDloadOpaque o1LowerDloadGhost ptrStaticDiscipline
  pointerConfinedDefs memLocDefs pred_set finite_map list rich_list
  livenessProofs cfgHelpers fmpWfDefs contextCodegenRel
  venomExecSemantics venomState venomInst venomWf passSharedProps
  runInstsProps analysisSimDefs o1PassContract ptrDiscipline

Theorem ret_point_operand_live[local]:
  wf_function fn /\ make_ssa_input_ok fn /\ active_inst fn inst s /\
  MEM (Var v) inst.inst_operands ==>
  MEM v (live_vars_at (liveness_analyze fn) s.vs_current_bb s.vs_inst_idx)
Proof
  strip_tac >>
  `fn_reachable fn s.vs_current_bb` by
    (gvs[make_ssa_input_ok_def, cfgWfTheory.all_reachable_def, active_inst_def] >>
     metis_tac[]) >>
  `MEM s.vs_current_bb (cfg_analyze fn).cfg_dfs_pre` by
    metis_tac[venomWfPropsTheory.fn_reachable_in_cfg_dfs_pre] >>
  gvs[active_inst_def] >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by
    (irule venomExecProofsTheory.MEM_lookup_block >>
     gvs[venomWfTheory.wf_function_def, fn_labels_def]) >>
  drule live_vars_at_uses >> simp[] >>
  disch_then irule >> goal_assum (drule_at Any) >>
  simp[operand_var_in_inst_uses]
QED

Theorem ret_point_front_equal[local]:
  wf_function fn /\ make_ssa_input_ok fn /\ opaque_use_ok fn /\
  active_inst fn inst s /\ inst.inst_opcode = RET /\
  inst.inst_operands <> [] /\
  ptr_use_static_ok P (fn_pv P fn) inst /\
  FDOM G SUBSET fn_pv P fn /\ taint_ok fn tn inst s /\
  fmp_env_rel sm fn
    (live_vars_at (liveness_analyze fn) s.vs_current_bb s.vs_inst_idx)
    G tn.t_var s t /\ s.vs_labels = t.vs_labels /\
  MEM op (FRONT inst.inst_operands) /\ eval_operand op s = SOME x ==>
  eval_operand op t = SOME x
Proof
  strip_tac >>
  `MEM op inst.inst_operands` by metis_tac[MEM_FRONT_NOT_NIL] >>
  `MEM inst (fn_insts fn)` by
    (gvs[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >>
     metis_tac[MEM_EL]) >>
  `!v. op = Var v ==> ~retpc_var fn v` by
    metis_tac[ret_front_non_retpc] >>
  `op_prov G op = NONE` by metis_tac[fmpStageRetStepTheory.fmp_run_ret_clean] >>
  `op_taint tn op = {}` by metis_tac[ret_operand_untainted] >>
  Cases_on `op` >>
  gvs[eval_operand_def, op_prov_def, op_taint_def] >>
  rename1 `lookup_var v s = SOME x` >>
  `MEM v (live_vars_at (liveness_analyze fn)
             s.vs_current_bb s.vs_inst_idx)` by
    metis_tac[ret_point_operand_live] >>
  qpat_x_assum `fmp_env_rel _ _ _ _ _ _ _` mp_tac >>
  simp[fmp_env_rel_def, lookup_var_def] >>
  disch_then (qspec_then `v` mp_tac) >>
  gvs[lookup_var_def, op_taint_def] >> strip_tac >>
  gvs[fmp_value_rel_def,
      o1LowerDloadRelocationKernelTheory.ld_value_agree_def,
      word_agree_except_bits] >>
  simp[fcpTheory.CART_EQ]
QED

Theorem fmp_focus_ret_point:
  wf_function fn /\ make_ssa_input_ok fn /\ opaque_use_ok fn /\
  active_inst fn inst s /\ inst.inst_opcode = RET /\
  ptr_use_static_ok P (fn_pv P fn) inst /\
  FDOM G SUBSET fn_pv P fn /\ taint_ok fn tn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom T stk PG G tn fn s lo t ts /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  step_inst k C inst s = IntRet ir s1 ==>
  active_inst fn' inst t /\ s1 = s /\ ir.iret_adopt_fmp = NONE /\
  ?jr. (!k'. step_inst k' C' inst t = IntRet jr t) /\
       jr.iret_values = ir.iret_values /\ jr.iret_adopt_fmp = NONE
Proof
  strip_tac >>
  `active_inst fn' inst t` by
    (gvs[fmp_stage_rel_def, fmp_frame_rel_def, active_inst_def] >>
     `lookup_block t.vs_current_bb fn.fn_blocks = SOME bb` by
       (irule venomExecProofsTheory.MEM_lookup_block >>
        gvs[wf_function_def, fn_labels_def]) >>
     drule fmp_stage_kept_inst >>
     disch_then drule >> disch_then drule >>
     simp[pre_fmp_opcode_def] >> strip_tac >>
     qexists `bb'` >>
     gvs[lookup_block_def] >>
     qpat_x_assum `FIND _ fn'.fn_blocks = SOME bb'`
       (mp_tac o MATCH_MP stackPlanGenTheory.FIND_SOME_MEM) >> simp[]) >>
  `step_inst_base inst s = IntRet ir s1` by
    (qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >> gvs[step_inst_non_invoke]) >>
  `?vals. eval_operands inst.inst_operands s = SOME vals /\ vals <> []` by
    (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
     simp[step_inst_base_def] >>
     Cases_on `eval_operands inst.inst_operands s` >> simp[] >>
     rename1 `SOME vals` >> Cases_on `vals` >> simp[]) >>
  `inst.inst_operands <> []` by (strip_tac >> gvs[eval_operands_def]) >>
  `!op. MEM op inst.inst_operands ==> IS_SOME (eval_operand op s)` by
    (`IS_SOME (eval_operands inst.inst_operands s)` by simp[] >>
     fs[eval_operands_IS_SOME_EVERY, EVERY_MEM]) >>
  `fmp_env_rel sm fn
     (live_vars_at (liveness_analyze fn) s.vs_current_bb s.vs_inst_idx)
     G tn.t_var s t /\ s.vs_labels = t.vs_labels` by
    (gvs[fmp_stage_rel_def, fmp_frame_rel_def] >> metis_tac[]) >>
  `!op. MEM op inst.inst_operands ==>
     (IS_SOME (eval_operand op s) <=> IS_SOME (eval_operand op t))` by
    metis_tac[fmpStageRetStepTheory.fmp_run_operand_defined] >>
  `!op. MEM op (FRONT inst.inst_operands) ==>
     eval_operand op s = eval_operand op t` by
    (rpt strip_tac >>
     `IS_SOME (eval_operand op s)` by metis_tac[MEM_FRONT_NOT_NIL] >>
     Cases_on `eval_operand op s` >> gvs[] >>
     metis_tac[ret_point_front_equal]) >>
  drule_all ret_front_transfer >> strip_tac >>
  gvs[] >> qexists `jr` >> gvs[step_inst_non_invoke]
QED

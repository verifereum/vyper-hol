(* At the restored FMP cursor, a kept jump selects the same label on
   both sides. The states produced by jump_to remain separate. *)
Theory gasFocusFmpJumpPoint
Ancestors
  fmpStageRel fmpStageControl o1PassContract frameViewFacts
  ptrStaticDiscipline ptrDiscipline pointerConfinedDefs memLocDefs
  o1LowerDloadRelocationKernel frameRelocationGuardedValues
  contextCodegenRel venomWf venomWfProps venomExecProofs venomExecSemantics
  venomState venomInst passSimulationDefs cfgWf livenessProofs
  finite_map pred_set list

Theorem jump_point_operand_equal[local]:
  wf_function fn /\ make_ssa_input_ok fn /\ opaque_use_ok fn /\
  active_inst fn inst s /\ MEM inst.inst_opcode [JMP;JNZ;DJMP] /\
  ptr_use_static_ok P (fn_pv P fn) inst /\ FDOM G SUBSET fn_pv P fn /\
  taint_ok fn tn inst s /\
  fmp_env_rel sm fn
    (live_vars_at (liveness_analyze fn) s.vs_current_bb s.vs_inst_idx)
    G tn.t_var s t /\ s.vs_labels = t.vs_labels /\
  MEM op inst.inst_operands /\ eval_operand op s = SOME x ==>
  eval_operand op t = SOME x
Proof
  strip_tac >> Cases_on `op` >> gvs[eval_operand_def, lookup_var_def] >>
  rename1 `MEM (Var v) inst.inst_operands` >>
  `MEM inst (fn_insts fn)` by
    (gvs[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >>
     metis_tac[MEM_EL]) >>
  `~retpc_var fn v` by
    (irule ordinary_operand_not_retpc >> simp[] >> qexists `inst` >> simp[]) >>
  `FLOOKUP G v = NONE` by
    (`v NOTIN fn_pv P fn` by
       (strip_tac >> gvs[MEM, ptr_use_static_ok_def,
         is_pointer_preserving_op_def, mem_read_ops_def, mem_write_ops_def] >>
        metis_tac[]) >>
     fs[SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]) >>
  `op_taint tn (Var v) = {}` by
    (qpat_x_assum `taint_ok _ _ _ _`
       (qspec_then `Var v` mp_tac o cj 1 o REWRITE_RULE [taint_ok_def]) >>
     fs[MEM]) >>
  `MEM v (live_vars_at (liveness_analyze fn) s.vs_current_bb s.vs_inst_idx)` by
    (`fn_reachable fn s.vs_current_bb` by
       (gvs[make_ssa_input_ok_def, all_reachable_def, active_inst_def] >>
        metis_tac[]) >>
     `MEM s.vs_current_bb (cfg_analyze fn).cfg_dfs_pre` by
       metis_tac[fn_reachable_in_cfg_dfs_pre] >>
     gvs[active_inst_def] >>
     `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by
       (irule MEM_lookup_block >> gvs[wf_function_def, fn_labels_def]) >>
     drule live_vars_at_uses >> simp[] >>
     disch_then irule >> goal_assum (drule_at Any) >>
     simp[operand_var_in_inst_uses]) >>
  qpat_x_assum `fmp_env_rel _ _ _ _ _ _ _` mp_tac >>
  simp[fmp_env_rel_def] >> disch_then (qspec_then `v` mp_tac) >>
  gvs[op_taint_def] >> strip_tac >>
  gvs[fmp_value_rel_def, ld_value_agree_scalar] >>
  drule word_agree_except_empty >> simp[]
QED

Theorem focus_fmp_jump_point:
  wf_function fn /\ make_ssa_input_ok fn /\ opaque_use_ok fn /\
  active_inst fn inst s /\ ~s.vs_halted /\ MEM inst.inst_opcode [JMP;JNZ;DJMP] /\
  ptr_use_static_ok P (fn_pv P fn) inst /\ FDOM G SUBSET fn_pv P fn /\
  taint_ok fn tn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom T stk PG G tn fn s lo t ts /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  step_inst k C inst s = r /\ terminates r ==>
  active_inst fn' inst t /\
  ?lbl. r = OK (jump_to lbl s) /\ !k'. step_inst k' C' inst t = OK (jump_to lbl t)
Proof
  strip_tac >> conj_tac
  >- (gvs[fmp_stage_rel_def, fmp_frame_rel_def, active_inst_def] >>
      `lookup_block t.vs_current_bb fn.fn_blocks = SOME bb` by
        (irule MEM_lookup_block >> gvs[wf_function_def, fn_labels_def]) >>
      drule fmp_stage_kept_inst >> disch_then drule >> disch_then drule >>
      simp[pre_fmp_opcode_def] >>
      disch_then (qx_choose_then `bb'` strip_assume_tac) >>
      qexists `bb'` >> simp[] >>
      metis_tac[lookup_block_MEM, lookup_block_label]) >>
  `~t.vs_halted` by gvs[fmp_stage_rel_def] >>
  `fmp_env_rel sm fn
     (live_vars_at (liveness_analyze fn) s.vs_current_bb s.vs_inst_idx)
     G tn.t_var s t /\ s.vs_labels = t.vs_labels` by
    (gvs[fmp_stage_rel_def, fmp_frame_rel_def] >> metis_tac[]) >>
  `!op x. MEM op inst.inst_operands /\ eval_operand op s = SOME x ==>
          eval_operand op t = SOME x` by
    (rpt strip_tac >> drule_all jump_point_operand_equal >> simp[]) >>
  fs[MEM] >> qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
  strip_tac >> gvs[terminates_def] >> metis_tac[MEM]
QED

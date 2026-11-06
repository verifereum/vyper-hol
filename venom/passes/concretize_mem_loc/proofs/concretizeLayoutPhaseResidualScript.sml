Theory concretizeLayoutPhaseResidual
Ancestors concretizeLayoutPhaseOrigin concretizeLayoutPhaseSuccess
  concretizeLayoutPhaseAdministration
  concretizeLayoutLocalAssertions concretizeLayoutLocalBump
  concretizeLayoutLocalExtcodeHash concretizeLayoutLocalExtcodeCopy
  concretizeLayoutSupplement concretizeLayoutReaderContext
  frameOriginUpdates frameResolvedTrace frameResolvedOrigins
  venomExecSemantics venomState venomInst ptrDiscipline list

Theorem layout_assert_trace_step:
  vs0.vs_allocas = FEMPTY /\ ptr_discipline lo C vs0 /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  ~g.lop_pending /\ layout_ordinary_entry D lo vs0 C C' q0 es qs q g s t /\
  g.lop_config = JointConfig stk PG G tn fn inst s oms om hs h /\
  g.lop_ids = birth::ids /\ g.lop_anns = (rp,rv)::anns /\
  g.lop_cursor < LENGTH es /\
  EL g.lop_cursor es = SOME (OriginOrdinary fuel post) /\
  MEM inst.inst_opcode [ASSERT; ASSERT_UNREACHABLE] /\ inst.inst_outputs = [] /\
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  get_instruction g.lop_origin.lbo_source s.vs_inst_idx = SOME inst /\
  step_inst_base inst s = OK post ==>
  ?k. step_inst_base inst t = OK t /\ k.lop_pending /\
    k.lop_cursor = SUC g.lop_cursor /\
    layout_phase_ok_abort D lo vs0 C C' q0 es qs q
      (INL g) (INL k) (OK post) (OK t)
Proof
  strip_tac >>
  `layout_ordinary_trace vs0 C q0 es qs q g s /\
   layout_ordinary_state D lo C' q0 es qs g s t` by
    fs[layout_ordinary_entry_def] >>
  `joint_trace vs0 C q0 es qs q /\
   EL g.lop_cursor (q0::qs) = g.lop_config /\
   resolved_config_ok g.lop_config g.lop_ids g.lop_anns` by
    fs[layout_ordinary_trace_def] >>
  qpat_x_assum `layout_ordinary_state _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[layout_ordinary_state_def] >> strip_tac >> gvs[] >> fs[ETA_AX] >>
  drule_at (Pat `local_rel _ _ _ _ _ _ _`)
    (REWRITE_RULE[GSYM concretize_local_obs_def, ETA_AX]
      (Q.INST [`D` |-> `<| d_stor := K (K UNIV); d_trans := K (K UNIV);
        d_imm := K UNIV; d_ret := K {} |>`]
        (SPEC_ALL concretize_assert_local_complete))) >>
  disch_then (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `resolved_config_ok _ _ _`)) >>
  disch_then (drule_at (Pat `relocation_taint_le _ _ _`)) >>
  disch_then (drule_at (Pat `fn_ptr_ok _ _`)) >> simp[] >> strip_tac >>
  `post = s` by
    (qpat_x_assum `step_inst_base inst s = OK post` mp_tac >>
     pure_once_rewrite_tac[step_inst_base_def] >>
     gvs[MEM] >> simp[AllCaseEqs()] >> metis_tac[]) >>
  `step_inst fuel C inst s = OK post` by
    (gvs[MEM] >> simp[step_inst_non_invoke]) >>
  drule_at (Pat `layout_ordinary_entry _ _ _ _ _ _ _ _ _ _ _ _`)
    layout_ordinary_success_phase >>
  disch_then (drule_at (Pat `step_inst _ _ _ _ = OK _`)) >>
  disch_then (drule_at (Pat `relocation_taint_le _ _ _`)) >>
  simp[ETA_AX] >> disch_then (qspec_then `t` mp_tac) >>
  gvs[MEM, is_terminator_def, origin_set_def, finite_mapTheory.DRESTRICT_UNIV] >>
  metis_tac[]
QED

Theorem layout_extcodehash_trace_step:
  vs0.vs_allocas = FEMPTY /\ ptr_discipline lo C vs0 /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  ~g.lop_pending /\ layout_ordinary_entry D lo vs0 C C' q0 es qs q g s t /\
  g.lop_config = JointConfig stk PG G tn fn inst s oms om hs h /\
  g.lop_ids = birth::ids /\ g.lop_anns = (rp,rv)::anns /\
  g.lop_cursor < LENGTH es /\
  EL g.lop_cursor es = SOME (OriginOrdinary fuel post) /\
  inst.inst_opcode = EXTCODEHASH /\ inst.inst_operands = [arg] /\
  inst.inst_outputs = [v] /\
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  get_instruction g.lop_origin.lbo_source s.vs_inst_idx = SOME inst /\
  step_inst_base inst s = OK post ==>
  ?k tpost. step_inst_base inst t = OK tpost /\ k.lop_pending /\
    k.lop_cursor = SUC g.lop_cursor /\
    layout_phase_ok_abort D lo vs0 C C' q0 es qs q
      (INL g) (INL k) (OK post) (OK tpost)
Proof
  strip_tac >>
  `layout_ordinary_trace vs0 C q0 es qs q g s /\
   layout_ordinary_state D lo C' q0 es qs g s t` by
    fs[layout_ordinary_entry_def] >>
  `joint_trace vs0 C q0 es qs q /\
   EL g.lop_cursor (q0::qs) = g.lop_config /\
   resolved_config_ok g.lop_config g.lop_ids g.lop_anns` by
    fs[layout_ordinary_trace_def] >>
  qpat_x_assum `layout_ordinary_state _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[layout_ordinary_state_def] >> strip_tac >> gvs[] >> fs[ETA_AX] >>
  drule_at (Pat `local_rel _ _ _ _ _ _ _`)
    (REWRITE_RULE[GSYM concretize_local_obs_def, ETA_AX]
      (Q.INST [`D` |-> `<| d_stor := K (K UNIV); d_trans := K (K UNIV);
        d_imm := K UNIV; d_ret := K {} |>`]
        (SPEC_ALL concretize_extcodehash_local_complete))) >>
  disch_then (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `resolved_config_ok _ _ _`)) >>
  disch_then (drule_at (Pat `relocation_taint_le _ _ _`)) >>
  disch_then (drule_at (Pat `fn_ptr_ok _ _`)) >>
  simp[] >> strip_tac >>
  `?x y. post = update_var v x s /\ tpost = update_var v y t` by
    (map_every (fn pat => qpat_x_assum pat mp_tac)
       [`step_inst_base inst s = OK post`, `step_inst_base inst t = OK tpost`] >>
     pure_once_rewrite_tac[step_inst_base_def] >> asm_rewrite_tac[opcode_case_def] >>
     simp[exec_read1_def, AllCaseEqs()] >> metis_tac[]) >>
  `step_inst fuel C inst s = OK post` by simp[step_inst_non_invoke] >>
  `?k. k.lop_pending /\ k.lop_cursor = SUC g.lop_cursor /\
    k.lop_target_taint = step_taint inst t tpost g.lop_target_taint /\
    layout_phase_ok_abort D lo vs0 C C' q0 es qs q
      (INL g) (INL k) (OK post) (OK tpost)` suffices_by metis_tac[] >>
  irule layout_var_gas_success_phase >> simp[] >>
  goal_assum (drule_at (Pat `layout_ordinary_entry _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[is_terminator_def, origin_out_def, resolved_out_def, ETA_AX] >>
  gvs[update_var_def, step_taint_def, store_taint_def, adopt_reset_def, imm_taint_def] >>
  simp[venom_state_component_equality] >> metis_tac[]
QED

Theorem layout_bump_trace_step:
  vs0.vs_allocas = FEMPTY /\ ptr_discipline lo C vs0 /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  ~g.lop_pending /\ layout_ordinary_entry D lo vs0 C C' q0 es qs q g s t /\
  g.lop_config = JointConfig stk PG G tn fn inst s oms om hs h /\
  g.lop_ids = birth::ids /\ g.lop_anns = (rp,rv)::anns /\
  g.lop_cursor < LENGTH es /\
  EL g.lop_cursor es = SOME (OriginOrdinary fuel post) /\
  inst.inst_opcode = BUMP /\ inst.inst_outputs = [v;w] /\
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  get_instruction g.lop_origin.lbo_source s.vs_inst_idx = SOME inst /\
  step_inst_base inst s = OK post ==>
  ?k tpost. step_inst_base inst t = OK tpost /\ k.lop_pending /\
    k.lop_cursor = SUC g.lop_cursor /\
    layout_phase_ok_abort D lo vs0 C C' q0 es qs q
      (INL g) (INL k) (OK post) (OK tpost)
Proof
  strip_tac >>
  `layout_ordinary_trace vs0 C q0 es qs q g s /\
   layout_ordinary_state D lo C' q0 es qs g s t` by
    fs[layout_ordinary_entry_def] >>
  `joint_trace vs0 C q0 es qs q /\
   EL g.lop_cursor (q0::qs) = g.lop_config /\
   resolved_config_ok g.lop_config g.lop_ids g.lop_anns` by
    fs[layout_ordinary_trace_def] >>
  qpat_x_assum `layout_ordinary_state _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[layout_ordinary_state_def] >> strip_tac >> gvs[] >> fs[ETA_AX] >>
  drule_at (Pat `local_rel _ _ _ _ _ _ _`)
    (REWRITE_RULE[GSYM concretize_local_obs_def, ETA_AX]
      (Q.INST [`D` |-> `<| d_stor := K (K UNIV); d_trans := K (K UNIV);
        d_imm := K UNIV; d_ret := K {} |>`]
        (SPEC_ALL concretize_bump_local_complete))) >>
  disch_then (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `resolved_config_ok _ _ _`)) >>
  disch_then (drule_at (Pat `relocation_taint_le _ _ _`)) >>
  disch_then (drule_at (Pat `fn_ptr_ok _ _`)) >> simp[] >> strip_tac >>
  `?x y a b. post = update_var w y (update_var v x s) /\
    tpost = update_var w b (update_var v a t)` by
    (map_every (fn pat => qpat_x_assum pat mp_tac)
       [`step_inst_base inst s = OK post`, `step_inst_base inst t = OK tpost`] >>
     pure_once_rewrite_tac[step_inst_base_def] >> asm_rewrite_tac[opcode_case_def] >>
     Cases_on `inst.inst_operands` >> simp[] >>
     Cases_on `t'` >> simp[] >> Cases_on `t''` >> simp[] >>
     simp[AllCaseEqs()] >> metis_tac[]) >>
  `step_inst fuel C inst s = OK post` by simp[step_inst_non_invoke] >>
  `concretize_supplement D (step_taint inst s post tn) post tpost` by
    (irule concretize_supplement_fields >>
     goal_assum (drule_at (Pat `concretize_supplement _ _ _ _`)) >>
     gvs[update_var_def, step_taint_def, store_taint_def, adopt_reset_def, imm_taint_def]) >>
  `?k. k.lop_pending /\ k.lop_cursor = SUC g.lop_cursor /\
    k.lop_target_taint = step_taint inst t tpost g.lop_target_taint /\
    layout_phase_ok_abort D lo vs0 C C' q0 es qs q
      (INL g) (INL k) (OK post) (OK tpost)` suffices_by metis_tac[] >>
  irule layout_ordinary_success_phase >> simp[] >>
  goal_assum (drule_at (Pat `layout_ordinary_entry _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[is_terminator_def, origin_out_def, resolved_out_def, ETA_AX] >>
  gvs[update_var_def] >> metis_tac[]
QED

Theorem layout_extcodecopy_trace_step:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY wf_function C.ctx_functions /\ mem_inv raw_mem_ok C vs0 /\
  vs0.vs_allocas = FEMPTY /\ ptr_discipline lo C vs0 /\
  callee_first names C.ctx_functions /\ EVERY ssa_form C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  ~ctx_has_dalloca C /\ fixed_region_reserved lo C /\ activation_depth q0 = 0 /\
  ~g.lop_pending /\ layout_ordinary_entry D lo vs0 C C' q0 es qs q g s t /\
  g.lop_config = JointConfig stk PG G tn fn inst s oms om hs h /\
  g.lop_ids = birth::ids /\ g.lop_anns = (rp,rv)::anns /\
  g.lop_cursor < LENGTH es /\
  EL g.lop_cursor es = SOME (OriginOrdinary fuel post) /\
  ~joint_read_exempt (EL g.lop_cursor (q0::qs)) /\
  inst.inst_opcode = EXTCODECOPY /\ inst.inst_operands = [opa;opd;ops;opn] /\
  inst.inst_outputs = [] /\
  eval_operand opa s = SOME addr /\ eval_operand opd s = SOME dst /\
  eval_operand ops s = SOME src /\ eval_operand opn s = SOME sz /\
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  get_instruction g.lop_origin.lbo_source s.vs_inst_idx = SOME inst /\
  step_inst_base inst s = OK post ==>
  ?k tpost. step_inst_base inst t = OK tpost /\ k.lop_pending /\
    k.lop_cursor = SUC g.lop_cursor /\
    layout_phase_ok_abort D lo vs0 C C' q0 es qs q
      (INL g) (INL k) (OK post) (OK tpost)
Proof
  strip_tac >>
  `layout_ordinary_trace vs0 C q0 es qs q g s /\
   layout_ordinary_state D lo C' q0 es qs g s t` by
    fs[layout_ordinary_entry_def] >>
  `joint_trace vs0 C q0 es qs q /\
   EL g.lop_cursor (q0::qs) = g.lop_config /\
   resolved_config_ok g.lop_config g.lop_ids g.lop_anns /\
   lifetime_ok g.lop_bound g.lop_ids g.lop_config` by
    fs[layout_ordinary_trace_def] >>
  qpat_x_assum `layout_ordinary_state _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[layout_ordinary_state_def] >> strip_tac >> gvs[] >> fs[ETA_AX] >>
  drule_at (Pat `local_rel _ _ _ _ _ _ _`)
    (REWRITE_RULE[GSYM concretize_local_obs_def, ETA_AX]
      (Q.INST [`D` |-> `<| d_stor := K (K UNIV); d_trans := K (K UNIV);
        d_imm := K UNIV; d_ret := K {} |>`]
        (SPEC_ALL concretize_extcodecopy_local_complete))) >>
  disch_then (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `resolved_config_ok _ _ _`)) >>
  disch_then (drule_at (Pat `relocation_taint_le _ _ _`)) >>
  disch_then (drule_at (Pat `ctx_pass_stage _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `fn_ptr_ok _ _`)) >>
  disch_then (drule_at (Pat `lifetime_ok _ _ _`)) >>
  disch_then (drule_at (Pat `callee_first _ _`)) >> simp[] >> strip_tac >>
  `?a xs b ys. post = write_memory_with_expansion a xs s /\
    tpost = write_memory_with_expansion b ys t` by
    (map_every (fn pat => qpat_x_assum pat mp_tac)
       [`step_inst_base inst s = OK post`, `step_inst_base inst t = OK tpost`] >>
     pure_once_rewrite_tac[step_inst_base_def] >> asm_rewrite_tac[opcode_case_def] >>
     simp[AllCaseEqs()] >> metis_tac[]) >>
  `step_inst fuel C inst s = OK post` by simp[step_inst_non_invoke] >>
  `concretize_supplement D (step_taint inst s post tn) post tpost` by
    (irule concretize_supplement_fields >>
     goal_assum (drule_at (Pat `concretize_supplement _ _ _ _`)) >>
     gvs[write_memory_with_expansion_def, step_taint_def, store_taint_def,
         adopt_reset_def, imm_taint_def]) >>
  `?k. k.lop_pending /\ k.lop_cursor = SUC g.lop_cursor /\
    k.lop_target_taint = step_taint inst t tpost g.lop_target_taint /\
    layout_phase_ok_abort D lo vs0 C C' q0 es qs q
      (INL g) (INL k) (OK post) (OK tpost)` suffices_by metis_tac[] >>
  drule_at (Pat `layout_ordinary_entry _ _ _ _ _ _ _ _ _ _ _ _`)
    layout_ordinary_success_phase >>
  disch_then (drule_at (Pat `step_inst _ _ _ _ = OK _`)) >>
  disch_then (drule_at (Pat `relocation_taint_le _ _ _`)) >>
  disch_then (qspec_then `tpost` mp_tac) >>
  simp[is_terminator_def, origin_set_def, finite_mapTheory.DRESTRICT_UNIV, ETA_AX] >>
  gvs[write_memory_with_expansion_def] >> metis_tac[]
QED

val _ = export_theory();

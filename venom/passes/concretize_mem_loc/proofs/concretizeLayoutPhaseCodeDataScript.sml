Theory concretizeLayoutPhaseCodeData
Ancestors concretizeLayoutPhaseOrigin concretizeLayoutPhaseSuccess
  concretizeLayoutLocalCodeDataReaders concretizeLayoutSupplement concretizeLayoutReaderContext
  frameOriginUpdates frameResolvedTrace
  venomExecSemantics venomState venomInst ptrDiscipline list

Theorem layout_code_data_trace_step:
  vs0.vs_allocas = FEMPTY /\ ptr_discipline lo C vs0 /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  ~g.lop_pending /\ layout_ordinary_entry D lo vs0 C C' q0 es qs q g s t /\
  g.lop_config = JointConfig stk PG G tn fn inst s oms om hs h /\
  g.lop_ids = birth::ids /\ g.lop_anns = (rp,rv)::anns /\
  g.lop_cursor < LENGTH es /\
  EL g.lop_cursor es = SOME (OriginOrdinary fuel post) /\
  code_data_reader_shape inst /\ inst.inst_outputs = [v] /\
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
        (SPEC_ALL concretize_code_data_reader_local_complete))) >>
  disch_then (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `resolved_config_ok _ _ _`)) >>
  disch_then (drule_at (Pat `relocation_taint_le _ _ _`)) >>
  disch_then (drule_at (Pat `fn_ptr_ok _ _`)) >> simp[] >> strip_tac >>
  `?z. post = update_var v z s` by
    (fs[code_data_reader_shape_def] >> qpat_x_assum `step_inst_base inst s = OK post` mp_tac >>
     pure_once_rewrite_tac[step_inst_base_def] >> asm_rewrite_tac[opcode_case_def] >>
     simp[exec_read0_def, exec_read1_def, AllCaseEqs()] >> metis_tac[]) >>
  `?w. tpost = update_var v w t` by
    (fs[code_data_reader_shape_def] >> qpat_x_assum `step_inst_base inst t = OK tpost` mp_tac >>
     pure_once_rewrite_tac[step_inst_base_def] >> asm_rewrite_tac[opcode_case_def] >>
     simp[exec_read0_def, exec_read1_def, AllCaseEqs()] >> metis_tac[]) >>
  `concretize_supplement D (step_taint inst s post tn) post tpost` by
    (gvs[] >> irule concretize_supplement_fields >>
     goal_assum (drule_at (Pat `concretize_supplement _ _ _ _`)) >>
     fs[code_data_reader_shape_def] >>
     simp[update_var_def, step_taint_def, store_taint_def, adopt_reset_def, imm_taint_def]) >>
  `inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> DALLOCA /\
   ~is_terminator inst.inst_opcode /\ origin_out PG om inst post = NONE` by
    (fs[code_data_reader_shape_def] >> simp[is_terminator_def, origin_out_def]) >>
  `step_inst fuel C inst s = OK post` by simp[step_inst_non_invoke] >>
  drule_at (Pat `layout_ordinary_entry _ _ _ _ _ _ _ _ _ _ _ _`)
    layout_ordinary_success_phase >>
  disch_then (drule_at (Pat `step_inst _ _ _ _ = OK _`)) >>
  disch_then (drule_at (Pat `relocation_taint_le _ _ _`)) >>
  simp[resolved_out_def, ETA_AX] >>
  disch_then (qspec_then `tpost` mp_tac) >> gvs[update_var_def] >> metis_tac[]
QED

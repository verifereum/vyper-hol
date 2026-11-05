(* Two-state semantic entry; PHIs retain their parallel input environment. *)
Theory o1LowerDloadPhiEntry
Ancestors
  o1LowerDloadPhi o1LowerDloadJointEntry o1LowerDloadJointRelation
  o1LowerDloadEnvironment o1LowerDloadOccurrence o1LowerDloadShared
  ptrDiscipline contextCodegenRel
  venomExecSemantics venomExecProofs venomState venomInst o1PassContract list

Theorem ld_env_enters_block:
  ir_supply_covers_fn u fn /\
  lower_dload_function_supply u fn = (fn',u') /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
  ld_env_agree sites fn H tn s t /\
  s.vs_labels = t.vs_labels /\
  s.vs_current_bb = t.vs_current_bb /\
  s.vs_prev_bb = t.vs_prev_bb /\
  enters_block fn s s1 /\ active_inst fn inst s1 ==>
  ?t1. enters_block fn' t t1 /\
    ld_env_agree sites fn (entry_prov fn s H)
      (entry_taint_vars fn s tn) s1 t1 /\
    ld_joint_control u fn fn' s1 t1
Proof
  strip_tac >>
  qpat_x_assum `enters_block fn s s1` mp_tac >>
  simp[enters_block_def] >> strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `EVERY (\i. MEM i (fn_insts fn)) bb.bb_instructions` by
    (simp[EVERY_MEM, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
  drule_all ld_env_eval_phis >> strip_tac >>
  qabbrev_tac `r = t1 with vs_inst_idx := phi_prefix_length bb.bb_instructions` >>
  `enters_block fn t r` by
    (simp[enters_block_def, Abbr `r`] >> metis_tac[]) >>
  `s1.vs_current_bb = r.vs_current_bb /\
   s1.vs_prev_bb = r.vs_prev_bb /\ s1.vs_inst_idx = r.vs_inst_idx` by
    (gvs[Abbr `r`] >>
     qpat_assum `eval_phis s _ = _`
       (mp_tac o MATCH_MP eval_phis_only_updates_vs_vars) >>
     disch_then (fn th => once_rewrite_tac[th]) >>
     qpat_assum `eval_phis t _ = _`
       (mp_tac o MATCH_MP eval_phis_only_updates_vs_vars) >>
     disch_then (fn th => once_rewrite_tac[th]) >>
     simp[]) >>
  `active_inst fn inst r` by (gvs[active_inst_def] >> metis_tac[]) >>
  drule_all ld_supply_successful_entry >> strip_tac >>
  qexists_tac `r` >> conj_tac
  >- metis_tac[enters_block_def] >>
  conj_tac
  >- gvs[entry_prov_def, entry_taint_vars_def, ld_env_agree_def, Abbr `r`] >>
  gvs[ld_joint_control_def, Abbr `r`] >> metis_tac[]
QED

Theorem ld_branch_noncontrol:
  MEM inst.inst_opcode [JMP; JNZ; DJMP] /\
  step_inst fuel C inst s = OK s' ==>
  s' = s with <|vs_current_bb := s'.vs_current_bb;
                vs_prev_bb := s'.vs_prev_bb; vs_inst_idx := s'.vs_inst_idx|>
Proof
  strip_tac >> gvs[] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  simp[jump_to_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem ld_env_branch_transport:
  ld_env_agree sites fn H tn s t /\
  MEM inst.inst_opcode [JMP; JNZ; DJMP] /\
  step_inst fuel C inst s = OK s' /\
  step_inst fuel' C' inst t = OK t' ==>
  ld_env_agree sites fn H tn s' t'
Proof
  strip_tac >>
  `s'.vs_vars = s.vs_vars` by
    (qpat_assum `step_inst fuel C inst s = OK s'`
       (mp_then Any mp_tac ld_branch_noncontrol) >>
     simp[] >> disch_then (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `t'.vs_vars = t.vs_vars` by
    (qpat_assum `step_inst fuel' C' inst t = OK t'`
       (mp_then Any mp_tac ld_branch_noncontrol) >>
     simp[] >> disch_then (fn th => once_rewrite_tac[th]) >> simp[]) >>
  gvs[ld_env_agree_def]
QED

Theorem ld_entry_nonvars[local]:
  enters_block fn s s1 ==>
  s1 = s with <|vs_vars := s1.vs_vars; vs_inst_idx := s1.vs_inst_idx|>
Proof
  simp[enters_block_def] >> strip_tac >> gvs[] >>
  drule eval_phis_only_updates_vs_vars >>
  disch_then (fn th => once_rewrite_tac[th]) >> simp[]
QED

Theorem ld_joint_branch_entry:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
  MEM inst.inst_opcode [JMP; JNZ; DJMP] /\
  step_inst fuel C inst s = OK s' /\ step_inst fuel' C' inst t = OK t' /\
  s'.vs_current_bb = t'.vs_current_bb /\ s'.vs_prev_bb = t'.vs_prev_bb /\
  ~s'.vs_halted /\ enters_block fn s' s1 /\ active_inst fn next s1 ==>
  ?fn' t1. lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    enters_block fn' t' t1 /\
    ld_joint_boundary vs C C' lo D stk PG (entry_prov fn s' G)
      (entry_taint_vars fn s' tn) fn next s1 t1
      n a U B HP (entry_prov fn s' H) sites X ts
Proof
  strip_tac >>
  `ld_env_agree sites fn H tn s t` by metis_tac[ld_joint_environment] >>
  drule_all ld_env_branch_transport >> strip_tac >>
  qhdtm_assum `ld_joint_boundary`
    (strip_assume_tac o REWRITE_RULE [ld_joint_boundary_def]) >>
  `active_inst fn inst s` by
    (drule occ_frame_reachable_projection >>
     simp[Once frame_reachable_cases] >> metis_tac[]) >>
  `is_terminator inst.inst_opcode` by gvs[is_terminator_def] >>
  `occ_frame_reachable vs C stk PG (entry_prov fn s' G)
    (entry_taint_vars fn s' tn) fn next s1 n a U B HP (entry_prov fn s' H)` by
    (irule occ_frame_reachable_block >> metis_tac[]) >>
  drule_all occurrence_annotation_block >> strip_tac >>
  qhdtm_assum `ld_joint_frame`
    (strip_assume_tac o REWRITE_RULE [ld_joint_frame_def]) >>
  qhdtm_assum `ld_joint_control`
    (strip_assume_tac o REWRITE_RULE [ld_joint_control_def]) >>
  `s' = s with <|vs_current_bb := s'.vs_current_bb;
    vs_prev_bb := s'.vs_prev_bb; vs_inst_idx := s'.vs_inst_idx|>` by
    (irule ld_branch_noncontrol >> metis_tac[]) >>
  `t' = t with <|vs_current_bb := t'.vs_current_bb;
    vs_prev_bb := t'.vs_prev_bb; vs_inst_idx := t'.vs_inst_idx|>` by
    (irule ld_branch_noncontrol >> metis_tac[]) >>
  `s'.vs_labels = t'.vs_labels` by
    (qpat_assum `s' = _` (fn th => once_rewrite_tac[th]) >>
     qpat_assum `t' = _` (fn th => once_rewrite_tac[th]) >>
     gvs[ld_joint_local_fields_def]) >>
  drule_all ld_env_enters_block >> strip_tac >>
  qexistsl_tac [`fn'`, `t1`] >> simp[] >>
  `s1 = s' with <|vs_vars := s1.vs_vars; vs_inst_idx := s1.vs_inst_idx|>` by
    metis_tac[ld_entry_nonvars] >>
  `t1 = t' with <|vs_vars := t1.vs_vars; vs_inst_idx := t1.vs_inst_idx|>` by
    metis_tac[ld_entry_nonvars] >>
  simp[ld_joint_boundary_def] >> rpt conj_tac
  >- (qexists_tac `u` >> simp[ld_joint_frame_def] >> conj_tac
      >- gvs[ld_env_agree_def, op_taint_def] >>
      qpat_assum `s1 = _` (fn th => once_rewrite_tac[th]) >>
      qpat_assum `t1 = _` (fn th => once_rewrite_tac[th]) >>
      qpat_assum `s' = _` (fn th => once_rewrite_tac[th]) >>
      qpat_assum `t' = _` (fn th => once_rewrite_tac[th]) >>
      gnvs[ld_params_agree_def, ld_joint_local_fields_def, ld_joint_allocas_def] >>
      metis_tac[])
  >- (qpat_assum `s1 = _` (fn th => once_rewrite_tac[th]) >>
      qpat_assum `t1 = _` (fn th => once_rewrite_tac[th]) >>
      qpat_assum `s' = _` (fn th => once_rewrite_tac[th]) >>
      qpat_assum `t' = _` (fn th => once_rewrite_tac[th]) >>
      simp[entry_taint_vars_def] >>
      Cases_on `lookup_block t'.vs_current_bb fn.fn_blocks` >> simp[])
  >- (qpat_assum `s1 = _` (fn th => once_rewrite_tac[th]) >>
      qpat_assum `t1 = _` (fn th => once_rewrite_tac[th]) >>
      qpat_assum `s' = _` (fn th => once_rewrite_tac[th]) >>
      qpat_assum `t' = _` (fn th => once_rewrite_tac[th]) >>
      Cases_on `lookup_block t'.vs_current_bb fn.fn_blocks` >>
      gnvs[ld_shared_agree_def, entry_taint_vars_def] >> metis_tac[]) >>
  qpat_assum `s1 = _` (fn th => once_rewrite_tac[th]) >>
  qpat_assum `t1 = _` (fn th => once_rewrite_tac[th]) >>
  qpat_assum `s' = _` (fn th => once_rewrite_tac[th]) >>
  qpat_assum `t' = _` (fn th => once_rewrite_tac[th]) >> simp[]
QED

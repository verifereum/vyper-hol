Theory concretizeLayoutLocalAllocation
Ancestors concretizeLayoutAllocationProduction concretizeLayoutSupplement
  concretizeLayoutReaderContext frameRelocationEnvironment frameRelocationAllocationSteps
  frameRelocationTaintOrder frameRelocationCopyTaint frameRelocationMemory
  frameRelocationGuardedValues frameRelocationLocal frameRelocationGhostCopy
  frameRelocationValues frameRelocationDemand
  frameActivationLookup frameResolvedTrace frameOriginUpdates
  ptrDiscipline venomExecSemantics venomState venomInst finite_map pred_set words list

Theorem layout_alloca_observable_effects:
  inst.inst_opcode = ALLOCA /\ exec_alloca inst s sz = OK post /\
  concretize_local_obs s t /\ concretize_supplement D tn s t /\
  relocation_env s t /\ relocation_reader_context s t /\
  s.vs_code = t.vs_code /\ s.vs_data_section = t.vs_data_section /\
  s.vs_initial_fmp = t.vs_initial_fmp ==>
  concretize_local_obs post (update_var v addr t) /\
  concretize_supplement D (step_taint inst s post tn) post (update_var v addr t) /\
  relocation_env post (update_var v addr t) /\
  relocation_reader_context post (update_var v addr t) /\
  post.vs_code = (update_var v addr t).vs_code /\
  post.vs_data_section = (update_var v addr t).vs_data_section /\
  post.vs_initial_fmp = (update_var v addr t).vs_initial_fmp /\
  post.vs_inst_idx = s.vs_inst_idx /\
  post.vs_params = s.vs_params /\ (update_var v addr t).vs_params = t.vs_params
Proof
  simp[exec_alloca_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[concretize_local_obs_def, dead_result_rel_def,
      concretize_supplement_def, relocation_env_def, relocation_reader_context_def,
      update_var_def, step_taint_def, store_taint_def, adopt_reset_def, imm_taint_def]
QED

Theorem layout_alloca_assign_taint:
  inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit sz] /\
  inst.inst_outputs = [v] /\ target.inst_opcode = ASSIGN /\
  target.inst_operands = [Lit addr] /\ target.inst_outputs = [v] /\
  relocation_taint_le R tn un /\ (!a b. next a b ==> R a b) ==>
  relocation_taint_le next (step_taint inst s post tn)
    (step_taint target t (update_var v addr t) un)
Proof
  strip_tac >>
  `new_site_bytes t (update_var v addr t) = {}` by
    (irule new_site_bytes_unchanged >> simp[update_var_def]) >>
  gvs[relocation_taint_le_def] >>
  simp[step_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
       allocation_mem_taint, mem_taint_def, step_writes_def,
       codegenRelTheory.source_memory_write_ranges_def, written_taint_def,
       range_bytes_def, out_taint_def, eval_operand_def, op_taint_def] >>
  conj_tac >- (fs[demand_taint_def] >> metis_tac[]) >>
  irule set_var_taint_subset >> simp[] >> gvs[op_taint_def]
QED

Theorem concretize_alloca_local_complete:
  vs0.vs_allocas = FEMPTY /\ joint_trace vs0 C q0 es qs q /\
  EL c (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\
  EL c es = SOME (OriginOrdinary fuel post) /\
  inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit sz] /\
  inst.inst_outputs = [v] /\ step_inst_base inst s = OK post /\
  target.inst_opcode = ASSIGN /\
  target.inst_operands = [Lit (n2w (positions fn inst.inst_id))] /\
  target.inst_outputs = [v] /\
  local_rel (\u. F)
    (guarded_ptr Opaque
      (activation_lookup (0:num) positions (birth::ids) (fn::owners)) rv)
    (guarded_bytes Opaque rv tn)
    (joint_relocation_demand lo positions q0 es qs c) concretize_local_obs s t /\
  relocation_taint_le (joint_relocation_demand lo positions q0 es qs c) tn un /\
  concretize_supplement D tn s t /\ relocation_env s t /\ relocation_reader_context s t /\
  s.vs_code = t.vs_code /\ s.vs_data_section = t.vs_data_section /\
  s.vs_initial_fmp = t.vs_initial_fmp ==>
  ?tpost. step_inst_base target t = OK tpost /\
  local_rel (\u. F)
    (guarded_ptr Opaque
      (activation_lookup (0:num) positions (birth::ids) (fn::owners))
      (origin_set rv inst.inst_outputs
        (resolved_out birth post.vs_allocas rp (origin_out PG om inst post))))
    (guarded_bytes Opaque
      (origin_set rv inst.inst_outputs
        (resolved_out birth post.vs_allocas rp (origin_out PG om inst post)))
      (step_taint inst s post tn))
    (joint_relocation_demand lo positions q0 es qs (SUC c)) concretize_local_obs post tpost /\
  relocation_taint_le (joint_relocation_demand lo positions q0 es qs (SUC c))
    (step_taint inst s post tn) (step_taint target t tpost un) /\
  concretize_supplement D (step_taint inst s post tn) post tpost /\
  relocation_env post tpost /\ relocation_reader_context post tpost /\
  post.vs_code = tpost.vs_code /\ post.vs_data_section = tpost.vs_data_section /\
  post.vs_initial_fmp = tpost.vs_initial_fmp /\ post.vs_inst_idx = s.vs_inst_idx /\
  post.vs_params = s.vs_params /\ tpost.vs_params = t.vs_params
Proof
  strip_tac >>
  `exec_alloca inst s sz = OK post` by
    (qpat_x_assum `step_inst_base inst s = OK post` mp_tac >>
     pure_once_rewrite_tac[step_inst_base_def] >>
     asm_rewrite_tac[opcode_case_def] >> simp[]) >>
  `!a b. joint_relocation_demand lo positions q0 es qs (SUC c) a b ==>
         joint_relocation_demand lo positions q0 es qs c a b` by
    (rpt strip_tac >> irule layout_alloca_demand_retained >> metis_tac[]) >>
  `?b oldsz s0. FLOOKUP post.vs_allocas inst.inst_id = SOME (b,oldsz) /\
    post = update_var v (n2w b) s0 /\
    ((FLOOKUP s.vs_allocas inst.inst_id = SOME (b,oldsz) /\ s0 = s) \/
     (FLOOKUP s.vs_allocas inst.inst_id = NONE /\ b = s.vs_alloca_next /\
      s0 = s with <|vs_allocas := s.vs_allocas |+ (inst.inst_id,(b,w2n sz));
                   vs_alloca_next := b+w2n sz|>))` by
    (Cases_on `FLOOKUP s.vs_allocas inst.inst_id`
     >- gvs[exec_alloca_def, update_var_def, FLOOKUP_UPDATE] >>
     PairCases_on `x` >> gvs[exec_alloca_def, update_var_def, FLOOKUP_UPDATE]) >>
  (`guarded_ptr Opaque
      (activation_lookup (0:num) positions (birth::ids) (fn::owners))
      (origin_set rv [v]
        (resolved_out birth post.vs_allocas rp (origin_out PG om inst post)))
      v (n2w b) (n2w (positions fn inst.inst_id)) /\
    guarded_bytes Opaque
      (origin_set rv [v]
        (resolved_out birth post.vs_allocas rp (origin_out PG om inst post)))
      (step_taint inst s post tn) v (n2w b) (n2w (positions fn inst.inst_id):256 word)` by
    (irule layout_alloca_output_guarded >> simp[]) >>
   `concretize_local_obs s t` by metis_tac[local_rel_def] >>
  `local_rel (\u. F)
    (guarded_ptr Opaque (activation_lookup (0:num) positions (birth::ids) (fn::owners)) rv)
    (guarded_bytes Opaque rv tn)
    (joint_relocation_demand lo positions q0 es qs (SUC c)) concretize_local_obs s0 t` by
    (gvs[local_rel_def, variable_domains_def, variables_agree_on_def,
         local_values_def, lookup_var_def, update_var_def, demand_agree_def,
         concretize_local_obs_def, dead_result_rel_def] >> metis_tac[]) >>
  qexists_tac `update_var v (n2w (positions fn inst.inst_id)) t` >>
  conj_tac >- simp[step_inst_base_def, eval_operand_def] >>
  reverse conj_tac
  >- (conj_tac >- (irule layout_alloca_assign_taint >> metis_tac[]) >>
      metis_tac[layout_alloca_observable_effects]) >>
  qpat_assum `post = _` SUBST1_TAC >>
  irule local_rel_update >> simp[] >>
  conj_tac >- metis_tac[layout_alloca_observable_effects] >>
  conj_tac >- gvs[update_var_def] >>
  conj_tac >- gvs[update_var_def] >>
  qpat_x_assum `s0 = _` SUBST_ALL_TAC >>
  gvs[] >>
  goal_assum (drule_at (Pat `local_rel _ _ _ _ _ _ _`)) >>
  rpt strip_tac >>
  simp[guarded_ptr_other, cj 2 layout_single_output_guarded_other])
QED

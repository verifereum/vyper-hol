Theory readonlyInvokeCopyFwdExecutionGas
Ancestors
  readonlyInvokeCopyFwdExecution readonlyInvokeCopyFwdOpaque
  readonlyInvokeCopyFwdStepsEffects readonlyInvokeCopyFwdRel
  readonlyInvokeCopyFwdEffects o1LowerDloadRelocationKernel o1LowerDloadOccurrence
  readonlyInvokeCopyFwdOperationalSupport readonlyInvokeCopyFwdHistoryPhase
  internalReturnCopyFwdSim ptrDiscipline taintAgree
  venomExecSemantics venomState venomInst codegenRel
  finite_map list pred_set words

Theorem ricf_opaque_frame_gas_tail[local]:
  ricf_opaque_frame_agree fn D X sites PG G tn s t ==>
  ricf_opaque_frame_agree fn D X sites PG G tn
    (s with vs_gas_readings := rest) (t with vs_gas_readings := rest)
Proof
  simp[ricf_opaque_frame_agree_def] >> strip_tac >>
  drule ricf_frame_gas_tail >> disch_then (qspec_then `rest` mp_tac) >>
  simp[ricf_opaque_view_def]
QED

Theorem ricf_opaque_live_stack_gas_tail[local]:
  ricf_opaque_live_stack_agree D ids tn maps stk targets s t ==>
  ricf_opaque_live_stack_agree D ids tn maps stk targets
    (s with vs_gas_readings := rest) (t with vs_gas_readings := rest)
Proof
  simp[ricf_opaque_live_stack_agree_def, merge_callee_state_def] >>
  strip_tac >> simp[] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule ricf_opaque_frame_gas_tail >> disch_then (qspec_then `rest` mp_tac) >>
  simp[]
QED

Theorem ricf_execution_gas_next:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  active_inst fn inst s /\ inst.inst_opcode = GAS /\
  step_inst fuel C inst s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?v. step_inst fuel Ct inst t = OK v /\
    ricf_execution_invariant vs C D stk PG (step_prov PG G inst u)
      (step_taint inst s u tn) fn next
      (u with vs_inst_idx := SUC s.vs_inst_idx)
      (v with vs_inst_idx := SUC s.vs_inst_idx)
      n a U (occurrence_sites_step a B inst u) HP
      (occurrence_step a HP H inst u) ledger E sites maps targets
      (step_taint inst s u tn)
Proof
  strip_tac >>
  `ricf_opaque_frame_agree fn D (ircf_dead (ricf_original_copy_ids C) s stk)
    sites (ricf_complete_params PG s.vs_params) G tn s t /\
   ricf_opaque_live_stack_agree D (ricf_original_copy_ids C) tn maps stk targets s t /\
   ircf_cross tn (ricf_phase_ranges 0 ledger) s t /\
   ricf_cert_crosses tn (ricf_phase_stack_ranges stk ledger) stk s t /\
   ricf_support_agree B E tn s t` by fs[ricf_execution_invariant_def] >>
  `s.vs_gas_readings = t.vs_gas_readings` by
    (fs[ricf_opaque_frame_agree_def] >> imp_res_tac ricf_frame_effect >>
     imp_res_tac ricf_effect_gas_readings >> fs[ricf_opaque_view_def]) >>
  `?out r rest. inst.inst_outputs = [out] /\
    u = update_var out r (s with vs_gas_readings := rest) /\
    step_inst fuel Ct inst t = OK (update_var out r (t with vs_gas_readings := rest))` by
    (qpat_x_assum `step_inst fuel C inst s = OK u` mp_tac >>
     Cases_on `s.vs_gas_readings` >>
     gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, exec_gas_def,
       AllCaseEqs()] >> strip_tac >> gvs[]
     >- (qexistsl_tac [`0w`,`[]`] >> simp[] >>
         gvs[update_var_def, venom_state_component_equality]) >>
     rename1 `s.vs_gas_readings = head::tail` >>
     qexistsl_tac [`head`,`tail`] >> gvs[]) >>
  `step_prov PG G inst u = set_prov G [out] NONE /\
   step_taint inst s u tn = (tn with t_var := set_var_taint tn.t_var [out] {}) /\
   occurrence_sites_step a B inst u = B` by
    (simp[step_prov_def, out_prov_def, step_taint_def, mem_taint_def,
      out_taint_def, adopt_reset_def, store_taint_def, imm_taint_def,
      new_site_bytes_def, step_writes_def, written_taint_def,
      source_memory_write_ranges_def, range_bytes_def, occurrence_sites_step_def,
      update_var_def, FLOOKUP_DEF, taint_component_equality, SF CONJ_ss] >>
     rpt CASE_TAC >> simp[]) >>
  `ricf_opaque_frame_agree fn D (ircf_dead (ricf_original_copy_ids C) s stk)
    sites (ricf_complete_params PG s.vs_params) (set_prov G [out] NONE)
    (tn with t_var := set_var_taint tn.t_var [out] {})
    (update_var out r (s with vs_gas_readings := rest))
    (update_var out r (t with vs_gas_readings := rest))` by
    (irule ricf_opaque_frame_bind >>
     simp[ricf_opaque_value_agree_def, ricf_is_zero_prov_def,
       ricf_value_agree_def, ld_value_agree_def, word_agree_except_def] >>
     irule ricf_opaque_frame_gas_tail >> simp[]) >>
  `ricf_opaque_frame_agree fn D (ircf_dead (ricf_original_copy_ids C) u stk)
     sites (ricf_complete_params PG u.vs_params) (step_prov PG G inst u)
     (step_taint inst s u tn) u (update_var out r (t with vs_gas_readings := rest)) /\
   ricf_opaque_live_stack_agree D (ricf_original_copy_ids C)
     (step_taint inst s u tn) maps stk targets u
     (update_var out r (t with vs_gas_readings := rest)) /\
   ircf_cross (step_taint inst s u tn) (ricf_phase_ranges 0 ledger) u
     (update_var out r (t with vs_gas_readings := rest)) /\
   ricf_cert_crosses (step_taint inst s u tn)
     (ricf_phase_stack_ranges stk ledger) stk u
     (update_var out r (t with vs_gas_readings := rest)) /\
   ricf_support_agree (occurrence_sites_step a B inst u) E
     (step_taint inst s u tn) u (update_var out r (t with vs_gas_readings := rest))` by
    (gvs[] >> rpt conj_tac
     >- gvs[ircf_dead_def, update_var_def]
     >- (irule ricf_opaque_live_stack_update_var >>
         irule ricf_opaque_live_stack_gas_tail >> simp[])
     >- (fs[ircf_cross_def, update_var_def] >> metis_tac[])
     >- (fs[ricf_cert_crosses_def, EVERY_MEM, ircf_cross_def, update_var_def] >>
         metis_tac[])
     >> fs[ricf_support_agree_def, update_var_def] >> metis_tac[]) >>
  qexists_tac `update_var out r (t with vs_gas_readings := rest)` >>
  conj_tac >- simp[] >>
  irule ricf_execution_next >> simp[is_terminator_def] >> metis_tac[]
QED

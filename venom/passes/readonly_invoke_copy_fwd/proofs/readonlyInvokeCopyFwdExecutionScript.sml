Theory readonlyInvokeCopyFwdExecution
Ancestors
  readonlyInvokeCopyFwdOperationalGuards readonlyInvokeCopyFwdSteps
  readonlyInvokeCopyFwdCalls
  readonlyInvokeCopyFwdGlobalSupport readonlyInvokeCopyFwdHeterogeneousLedger
  readonlyInvokeCopyFwdOperationalMapOrigins readonlyInvokeCopyFwdRel
  readonlyInvokeCopyFwdOperationalSupport readonlyInvokeCopyFwdHistoryPhase
  readonlyInvokeCopyFwdProtectionInherited internalReturnCopyFwdSim o1LowerDloadShared
  o1LowerDloadOccurrence venomInst
  taintAgree ptrDiscipline venomExecSemantics venomState finite_map list pred_set

(* Running source provenance is independent of both taint annotations. *)
Definition ricf_execution_invariant_def:
  ricf_execution_invariant vs C ctx0 log D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets rt <=>
  ricf_heterogeneous_source_ledger vs C stk PG G tn fn inst s n a U B HP H ledger /\
  ricf_frame_agree D (ircf_dead (ricf_original_copy_ids C) s stk)
    sites (ricf_complete_params PG s.vs_params) G rt s t /\
  ricf_live_stack_agree D (ricf_original_copy_ids C) rt maps stk targets s t /\
  ircf_cross rt (ricf_phase_ranges 0 ledger) s t /\
  ricf_cert_crosses rt (ricf_phase_stack_ranges stk ledger) stk s t /\
  ricf_global_support_origins vs C ctx0 a fn U stk B E /\
  ricf_support_agree B E rt s t /\
  ricf_map_origins vs C ctx0 log stk PG G tn fn inst s U B sites /\
  ricf_saved_map_origins vs C ctx0 log stk U B maps
End

Theorem ricf_execution_initial:
  C.ctx_entry = SOME name /\
  lookup_function name C.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl /\
  enters_block fn
    (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) s /\
  active_inst fn inst s ==>
  ricf_execution_invariant vs C ctx0 log D [] [] FEMPTY entry_taint fn inst s s
    1 0 [] FEMPTY [] FEMPTY [] {} FEMPTY [] [] entry_taint
Proof
  strip_tac >>
  drule_all ricf_heterogeneous_source_ledger_initial >> strip_tac >>
  simp[ricf_execution_invariant_def, ricf_frame_agree_completed_identity,
    taint_agree_def, ld_shared_agree_refl, word_agree_except_def,
    venom_state_component_equality, ricf_live_stack_agree_def,
    ircf_cross_def, ricf_phase_stack_ranges_def, ricf_cert_crosses_def,
    ricf_global_support_empty, ricf_support_agree_def, ricf_map_origins_empty]
QED

Theorem ricf_execution_assign_next:
  ricf_execution_invariant vs C ctx0 log D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets rt /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  active_inst fn inst s /\ inst.inst_opcode = ASSIGN /\
  inst.inst_operands = [op] /\ inst.inst_outputs = [out] /\
  step_inst fuel C inst s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?v. step_inst fuel Ct inst t = OK v /\
    ricf_execution_invariant vs C ctx0 log D stk PG (step_prov PG G inst u)
      (step_taint inst s u tn) fn next
      (u with vs_inst_idx := SUC s.vs_inst_idx)
      (v with vs_inst_idx := SUC s.vs_inst_idx)
      n a U (occurrence_sites_step a B inst u) HP
      (occurrence_step a HP H inst u) ledger E sites maps targets
      (step_taint inst s u rt)
Proof
  pure_rewrite_tac[ricf_execution_invariant_def] >> strip_tac >>
  `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
    simp[is_terminator_def] >>
  `?x. eval_operand op s = SOME x /\ u = update_var out x s` by
    (gvs[step_inst_def, step_inst_base_opcode_eqs, AllCaseEqs()]) >>
  drule_all ricf_assign_live >> strip_tac >>
  `ricf_heterogeneous_source_ledger vs C stk PG (step_prov PG G inst u)
    (step_taint inst s u tn) fn next (u with vs_inst_idx := SUC s.vs_inst_idx)
    n a U (occurrence_sites_step a B inst u) HP
    (occurrence_step a HP H inst u) ledger` by
    (irule ricf_heterogeneous_source_ledger_actual_next >> metis_tac[]) >>
  `ricf_map_origins vs C ctx0 log stk PG (step_prov PG G inst u)
    (step_taint inst s u tn) fn next (u with vs_inst_idx := SUC s.vs_inst_idx)
    U B sites` by (irule ricf_map_origins_next >> metis_tac[]) >>
  `ricf_global_support_origins vs C ctx0 a fn U stk
    (occurrence_sites_step a B inst u) E` by
    (irule (cj 2 ricf_global_support_actual_next) >>
     fs[ricf_heterogeneous_source_ledger_def] >> metis_tac[]) >>
  qexists_tac `update_var out y t` >>
  simp[step_inst_def] >>
  gvs[step_prov_def, step_taint_def, occurrence_sites_step_def,
    update_var_def, out_prov_def, out_taint_def, mem_taint_def,
    adopt_reset_def, store_taint_def, imm_taint_def, first_prov_def,
    new_site_bytes_def, step_writes_def, written_taint_def, range_bytes_def,
    taint_component_equality, codegenRelTheory.source_memory_write_ranges_def,
    FLOOKUP_DEF, SF ETA_ss, SF CONJ_ss] >>
  `<|t_mem := rt.t_mem; t_var := set_var_taint rt.t_var [out] (op_taint rt op);
      t_stor := rt.t_stor; t_trans := rt.t_trans; t_imm := rt.t_imm|> =
    rt with t_var := set_var_taint rt.t_var [out] (op_taint rt op)` by
    simp[taint_component_equality] >>
  simp[Once ircf_dead_def] >>
  conj_tac >-
    (qpat_assum `ricf_frame_agree _ _ _ _ (set_prov _ _ _) _ _ _`
       (mp_then Any (qspec_then `SUC s.vs_inst_idx` mp_tac) ricf_frame_inst_idx) >>
     simp[ircf_dead_def]) >>
  conj_tac >-
    (qpat_x_assum `ricf_live_stack_agree _ _ (_ with t_var := _) _ _ _ _ _` mp_tac >>
     simp[ricf_live_stack_agree_def, merge_callee_state_def]) >>
  conj_tac >-
    (qpat_x_assum `ircf_cross _ _ _ _` mp_tac >> simp[ircf_cross_def]) >>
  conj_tac >-
    (qpat_x_assum `ricf_cert_crosses _ _ _ _ _` mp_tac >>
     simp[ricf_cert_crosses_def, ircf_cross_def, merge_callee_state_def]) >>
  qpat_x_assum `ricf_support_agree _ _ _ _ _` mp_tac >>
  simp[ricf_support_agree_def]
QED

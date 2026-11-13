Theory readonlyInvokeCopyFwdExecutionBlock
Ancestors
  readonlyInvokeCopyFwdExecution readonlyInvokeCopyFwdOperationalEntry
  readonlyInvokeCopyFwdHistoryInheritedLifecycle
  readonlyInvokeCopyFwdHeterogeneousLedger readonlyInvokeCopyFwdHistoryPhase
  readonlyInvokeCopyFwdHistoryOrigin readonlyInvokeCopyFwdProtection
  readonlyInvokeCopyFwdOperationalSupport o1LowerDloadOccurrence
  readonlyInvokeCopyFwdRel readonlyInvokeCopyFwdCalls
  internalReturnCopyFwdSim taintAgree o1LowerDloadShared
  venomExecSemantics venomState list pred_set finite_map

Theorem ricf_heterogeneous_source_ledger_block:
  ricf_heterogeneous_source_ledger vs C stk PG G tn fn inst s n a U B HP H ledger /\
  active_inst fn inst s /\ is_terminator inst.inst_opcode /\
  step_inst fuel C inst s = OK u /\ ~u.vs_halted /\
  enters_block fn u s1 /\ active_inst fn next s1 ==>
  ricf_heterogeneous_source_ledger vs C stk PG (entry_prov fn u G)
    (entry_taint_vars fn u tn) fn next s1 n a U B HP (entry_prov fn u H)
    (FILTER (\entry. SND entry <> []) ledger)
Proof
  simp[ricf_heterogeneous_source_ledger_def, EVERY_MEM, MEM_FILTER] >>
  rpt strip_tac
  >- (irule occ_frame_reachable_block >> metis_tac[]) >>
  first_x_assum drule >> strip_tac >>
  Cases_on `entry` >> gvs[ricf_phase_entry_def] >>
  qexistsl_tac [`ctxP`, `logP`] >> simp[ricf_phase_entry_def] >>
  fs[ricf_history_cursor_def] >> Cases_on `r` >> gvs[] >>
  metis_tac[ricf_visit_prefix_block]
QED

Theorem ricf_execution_map_origins_block:
  ricf_map_origins vs C ctx0 log stk PG G tn fn inst s U B sites /\
  active_inst fn inst s /\ is_terminator inst.inst_opcode /\
  step_inst fuel C inst s = OK u /\ ~u.vs_halted /\
  enters_block fn u s1 /\ active_inst fn next s1 ==>
  ricf_map_origins vs C ctx0 log stk PG (entry_prov fn u G)
    (entry_taint_vars fn u tn) fn next s1 U B sites
Proof
  rw[ricf_map_origins_def] >>
  first_x_assum drule >>
  simp[ricf_translation_origin_def] >> strip_tac >>
  qexistsl_tac [`p`, `pre`, `anchor`, `tail`, `atn`] >> simp[] >>
  irule ricf_history_inherited_block >> metis_tac[]
QED

Theorem ricf_phase_ranges_block_retire:
  ricf_phase_ranges depth (FILTER (\entry. SND entry <> []) ledger) =
    (if depth = 0 then {} else ricf_phase_ranges depth ledger)
Proof
  rw[ricf_phase_ranges_def, EXTENSION, MEM_FILTER] >>
  Cases_on `depth = 0` >> gvs[] >> metis_tac[LENGTH_NIL]
QED

Theorem ricf_phase_stack_ranges_block_retire:
  ricf_phase_stack_ranges stk (FILTER (\entry. SND entry <> []) ledger) =
    ricf_phase_stack_ranges stk ledger
Proof
  simp[ricf_phase_stack_ranges_def, ricf_phase_ranges_block_retire]
QED

Theorem ricf_execution_jump_live:
  ricf_frame_agree D X sites PG G rt s t /\
  ricf_live_stack_agree D ids rt maps stk targets s t /\
  ricf_cert_crosses rt curs stk s t /\ ricf_support_agree B E rt s t ==>
  ricf_frame_agree D X sites PG G rt (jump_to lbl s) (jump_to lbl t) /\
  ricf_live_stack_agree D ids rt maps stk targets (jump_to lbl s) (jump_to lbl t) /\
  ricf_cert_crosses rt curs stk (jump_to lbl s) (jump_to lbl t) /\
  ricf_support_agree B E rt (jump_to lbl s) (jump_to lbl t)
Proof
  simp[jump_to_def, ricf_frame_agree_def, taint_agree_def,
    ld_shared_agree_def, ircf_cross_def, ricf_live_stack_agree_def,
    ricf_cert_crosses_def, ricf_support_agree_def, merge_callee_state_def] >>
  rpt strip_tac >> gvs[venom_state_component_equality] >> metis_tac[]
QED

Theorem ricf_execution_jump_block:
  ricf_execution_invariant vs C ctx0 log D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets rt /\
  inst.inst_opcode = JMP /\ inst.inst_operands = [Label lbl] /\
  active_inst fn inst s /\ step_inst fuel C inst s = OK u /\ ~u.vs_halted /\
  enters_block fn u s1 /\ active_inst fn next s1 ==>
  ?v t1. step_inst fuel Ct inst t = OK v /\ enters_block fn v t1 /\
    ricf_execution_invariant vs C ctx0 log D stk PG (entry_prov fn u G)
      (entry_taint_vars fn u tn) fn next s1 t1
      n a U B HP (entry_prov fn u H)
      (FILTER (\entry. SND entry <> []) ledger) E sites maps targets
      (entry_taint_vars fn u rt)
Proof
  pure_rewrite_tac[ricf_execution_invariant_def] >> strip_tac >>
  `is_terminator inst.inst_opcode` by simp[venomInstTheory.is_terminator_def] >>
  `u = jump_to lbl s` by gvs[step_inst_def, step_inst_base_opcode_eqs] >>
  `ricf_heterogeneous_source_ledger vs C stk PG (entry_prov fn u G)
      (entry_taint_vars fn u tn) fn next s1 n a U B HP (entry_prov fn u H)
      (FILTER (\entry. SND entry <> []) ledger)` by
    (irule ricf_heterogeneous_source_ledger_block >> metis_tac[]) >>
  `ricf_map_origins vs C ctx0 log stk PG (entry_prov fn u G)
      (entry_taint_vars fn u tn) fn next s1 U B sites` by
    (irule ricf_execution_map_origins_block >> metis_tac[]) >>
  drule_all ricf_execution_jump_live >>
  disch_then (qspec_then `lbl` strip_assume_tac) >>
  `enters_block fn (jump_to lbl s) s1` by metis_tac[] >>
  `ircf_cross rt {} (jump_to lbl s) (jump_to lbl t)` by simp[ircf_cross_def] >>
  drule_all ricf_live_support_enters_block >> strip_tac >>
  qexistsl_tac [`jump_to lbl t`, `t1`] >>
  simp[step_inst_def, step_inst_base_opcode_eqs, ricf_phase_stack_ranges_block_retire,
    ricf_phase_ranges_block_retire, ircf_cross_def] >>
  qpat_x_assum `enters_block fn (jump_to lbl s) s1` mp_tac >>
  simp[contextCodegenRelTheory.enters_block_def] >> strip_tac >>
  qpat_assum `eval_phis (jump_to lbl s) _ = OK _`
    (mp_tac o MATCH_MP venomExecProofsTheory.eval_phis_only_updates_vs_vars) >>
  disch_then SUBST_ALL_TAC >>
  gvs[ircf_dead_def, jump_to_def]
QED

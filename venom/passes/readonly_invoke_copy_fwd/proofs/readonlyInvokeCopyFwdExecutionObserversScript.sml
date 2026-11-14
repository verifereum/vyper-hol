Theory readonlyInvokeCopyFwdExecutionObservers
Ancestors
  readonlyInvokeCopyFwdExecution readonlyInvokeCopyFwdOpaque
  readonlyInvokeCopyFwdStepsLog readonlyInvokeCopyFwdRel
  readonlyInvokeCopyFwdOperationalSupport readonlyInvokeCopyFwdHistoryPhase
  o1LowerDloadOccurrence o1LowerDloadRelocationKernel
  internalReturnCopyFwdSim ptrDiscipline taintAgree
  venomExecSemantics venomState venomInst codegenRel contextCodegenRel
  finite_map list pred_set words

Theorem ricf_execution_sha3_next:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  active_inst fn inst s /\ inst.inst_opcode = SHA3 /\
  inst.inst_operands = [addr;lenop] /\ inst.inst_outputs = [out] /\
  eval_operand addr s = SOME p /\ eval_operand addr t = SOME q /\
  eval_operand lenop s = SOME len /\ eval_operand lenop t = SOME len /\
  read_memory (w2n p) (w2n len) s = read_memory (w2n q) (w2n len) t /\
  hash = word_of_bytes T (0w:bytes32)
    (Keccak_256_w64 (read_memory (w2n p) (w2n len) s)) /\
  active_inst fn next ((update_var out hash s) with vs_inst_idx := SUC s.vs_inst_idx) ==>
  step_inst fuel Ct inst t = OK (update_var out hash t) /\
  ricf_execution_invariant vs C D stk PG (step_prov PG G inst (update_var out hash s))
    (step_taint inst s (update_var out hash s) tn) fn next
    ((update_var out hash s) with vs_inst_idx := SUC s.vs_inst_idx)
    ((update_var out hash t) with vs_inst_idx := SUC s.vs_inst_idx)
    n a U B HP (occurrence_step a HP H inst (update_var out hash s))
    ledger E sites maps targets (step_taint inst s (update_var out hash s) tn)
Proof
  strip_tac >>
  `step_inst fuel C inst s = OK (update_var out hash s) /\
   step_inst fuel Ct inst t = OK (update_var out hash t)` by
    simp[step_inst_non_invoke, step_inst_base_opcode_eqs, GSYM read_memory_def] >>
  conj_tac >- simp[] >>
  drule (Q.INST [`p` |-> `NONE`, `m` |-> `{}`, `out` |-> `out`,
    `x` |-> `hash`, `y` |-> `hash`, `next` |-> `next`,
    `fuel` |-> `fuel`, `Ct` |-> `Ct`] ricf_execution_bind_next) >>
  disch_then (qspecl_then [`out`,`next`,`hash`,`fuel`,`Ct`] mp_tac) >>
  impl_tac >- (simp[ricf_opaque_value_agree_def, ricf_is_zero_prov_def,
    ricf_value_agree_def, ld_value_agree_def, word_agree_except_def,
    is_terminator_def, step_prov_def, out_prov_def, step_taint_def,
    mem_taint_def, out_taint_def, adopt_reset_def, store_taint_def,
    imm_taint_def, new_site_bytes_def, step_writes_def, written_taint_def,
    source_memory_write_ranges_def, range_bytes_def, update_var_def,
    occurrence_sites_step_def, FLOOKUP_DEF, taint_component_equality,
    SF CONJ_ss] >> metis_tac[update_var_def]) >>
  simp[occurrence_sites_step_def]
QED

Theorem ricf_opaque_frame_logs_append[local]:
  ricf_opaque_frame_agree fn D X sites PG G tn s t ==>
  ricf_opaque_frame_agree fn D X sites PG G tn
    (s with vs_logs := s.vs_logs ++ [ev])
    (t with vs_logs := t.vs_logs ++ [ev])
Proof
  simp[ricf_opaque_frame_agree_def] >> strip_tac >>
  drule ricf_frame_logs_append >> disch_then (qspec_then `ev` mp_tac) >>
  simp[ricf_opaque_view_def]
QED

Theorem ricf_execution_log_next:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  active_inst fn inst s /\ inst.inst_opcode = LOG /\ inst.inst_outputs = [] /\
  inst.inst_operands = Lit tc :: REVERSE (addr::lenop::tops) /\
  LENGTH tops = w2n tc /\
  eval_operand addr s = SOME p /\ eval_operand addr t = SOME q /\
  eval_operand lenop s = SOME len /\ eval_operand lenop t = SOME len /\
  eval_operands tops s = SOME topics /\ eval_operands tops t = SOME topics /\
  read_memory (w2n p) (w2n len) s = read_memory (w2n q) (w2n len) t /\
  ~s.vs_call_ctx.cc_static /\
  ev = <|logger := w2w s.vs_call_ctx.cc_address; topics := topics;
    data := read_memory (w2n p) (w2n len) s|> /\
  active_inst fn next ((s with vs_logs := s.vs_logs ++ [ev])
    with vs_inst_idx := SUC s.vs_inst_idx) ==>
  step_inst fuel Ct inst t = OK (t with vs_logs := t.vs_logs ++ [ev]) /\
  ricf_execution_invariant vs C D stk PG G tn fn next
    ((s with vs_logs := s.vs_logs ++ [ev]) with vs_inst_idx := SUC s.vs_inst_idx)
    ((t with vs_logs := t.vs_logs ++ [ev]) with vs_inst_idx := SUC s.vs_inst_idx)
    n a U B HP (occurrence_step a HP H inst (s with vs_logs := s.vs_logs ++ [ev]))
    ledger E sites maps targets tn
Proof
  strip_tac >>
  `ricf_opaque_frame_agree fn D (ircf_dead (ricf_original_copy_ids C) s stk)
    sites (ricf_complete_params PG s.vs_params) G tn s t /\
   ricf_opaque_live_stack_agree D (ricf_original_copy_ids C) tn maps stk targets s t /\
   ircf_cross tn (ricf_phase_ranges 0 ledger) s t /\
   ricf_cert_crosses tn (ricf_phase_stack_ranges stk ledger) stk s t /\
   ricf_support_agree B E tn s t` by fs[ricf_execution_invariant_def] >>
  `t.vs_call_ctx = s.vs_call_ctx` by
    fs[ricf_opaque_frame_agree_def, ricf_frame_agree_def, taint_agree_def,
      ricf_opaque_view_def, venom_state_component_equality] >>
  `step_inst fuel C inst s = OK (s with vs_logs := s.vs_logs ++ [ev]) /\
   step_inst fuel Ct inst t = OK (t with vs_logs := t.vs_logs ++ [ev])` by
    simp[step_inst_non_invoke, step_inst_base_opcode_eqs, REVERSE_APPEND,
      GSYM read_memory_def] >>
  `step_taint inst s (s with vs_logs := s.vs_logs ++ [ev]) tn = tn` by
    metis_tac[step_taint_log_logs] >>
  conj_tac >- simp[] >>
  mp_tac (Q.INST [`u` |-> `s with vs_logs := s.vs_logs ++ [ev]`,
    `v` |-> `t with vs_logs := t.vs_logs ++ [ev]`, `rt` |-> `tn`]
    ricf_execution_next) >>
  impl_tac >- (simp[is_terminator_def, step_prov_def, set_prov_def, DRESTRICT_UNIV,
    occurrence_sites_step_def, Once ircf_dead_def] >> rpt conj_tac
  >- metis_tac[ricf_opaque_frame_logs_append, ircf_dead_def]
  >- (fs[ricf_opaque_live_stack_agree_def] >>
      simp[ricf_opaque_live_stack_agree_def] >> rpt strip_tac >>
      first_x_assum drule >> strip_tac >>
      drule ricf_opaque_frame_logs_append >>
      disch_then (qspec_then `ev` mp_tac) >> simp[merge_callee_state_def])
  >- (gvs[ircf_cross_def] >> metis_tac[])
  >- (gvs[ricf_cert_crosses_def, ircf_cross_def] >> metis_tac[])
  >> gvs[ricf_support_agree_def] >> metis_tac[]) >>
  simp[step_prov_def, set_prov_def, DRESTRICT_UNIV, occurrence_sites_step_def]
QED

Theory readonlyInvokeCopyFwdExecutionReturn
Ancestors
  readonlyInvokeCopyFwdExecution readonlyInvokeCopyFwdOpaqueReturn readonlyInvokeCopyFwdOpaque
  readonlyInvokeCopyFwdHeterogeneousLifecycle readonlyInvokeCopyFwdHeterogeneousLedger
  readonlyInvokeCopyFwdHeterogeneousMapOrigins readonlyInvokeCopyFwdHeterogeneousSupport
  readonlyInvokeCopyFwdHistoryStackAlignment readonlyInvokeCopyFwdHistoryPhase
  readonlyInvokeCopyFwdOperationalSupport readonlyInvokeCopyFwdRel
  occurrenceGeometry o1LowerDloadOccurrence o1LowerDloadJointRestore
  o1LowerDloadJointScalar o1LowerDloadPtrDiscipline o1LowerDloadGhost o1LowerDloadShared
  o1LowerDloadRelocationKernel o1LowerDloadOpaque frameRel calleeTransport
  internalReturnCopyFwdSim taintAgree ptrDiscipline pointerConfinedDefs memLocDefs
  stateEquiv stateFrame venomExecSemantics venomState venomInst
  finite_map list pred_set words arithmetic

Theorem ricf_return_support_cut[local]:
  occurrence_natural_geometry lo a (u::U) B (f::stk) s ==>
  f.cf_state.vs_alloca_next <= s.vs_alloca_next /\
  (!id b z. FLOOKUP B id = SOME (b,z) /\ FST id = a ==>
     f.cf_state.vs_alloca_next <= b)
Proof
  rw[occurrence_natural_geometry_def] >>
  qpat_x_assum `!j. j < SUC (LENGTH stk) ==> _` (qspec_then `0` mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem ricf_return_support_pop[local]:
  occurrence_natural_geometry lo a (u::U) B (f::stk) s /\
  ricf_support_agree B E tn s t ==>
  ricf_support_agree (DRESTRICT B {id | FST id <> a})
    {id | id IN E /\ FST id <> a} tn
    (merge_callee_state f.cf_state s) (merge_callee_state caller t)
Proof
  strip_tac >> drule ricf_return_support_cut >> strip_tac >>
  rw[ricf_support_agree_def, merge_callee_state_def] >>
  `i < s.vs_alloca_next` by decide_tac >>
  `i NOTIN ricf_support_bytes B E` by
    (strip_tac >>
     qpat_x_assum `i IN ricf_support_bytes B E`
       (strip_assume_tac o SIMP_RULE (srw_ss()) [ricf_support_bytes_def]) >>
     rename1 `FLOOKUP B site = SOME (off,len)` >>
     Cases_on `FST site = a`
     >- (`f.cf_state.vs_alloca_next <= off` by metis_tac[] >> decide_tac) >>
     `i IN ricf_support_bytes (DRESTRICT B {id | FST id <> a})
       {id | id IN E /\ FST id <> a}` by
       (simp_tac (srw_ss()) [ricf_support_bytes_def] >>
        qexistsl_tac [`site`,`off`,`len`] >>
        simp[FLOOKUP_DRESTRICT]) >> metis_tac[]) >>
  fs[ricf_support_agree_def]
QED

Theorem ricf_return_support_bind[local]:
  ricf_support_agree B E tn s t /\
  bind_outputs outs vals (adopt_return_fmp ret s) = SOME s' /\
  bind_outputs outs vals (adopt_return_fmp ret t) = SOME t' ==>
  ricf_support_agree B E (tn with t_var := tv)
    (s' with vs_inst_idx := idx) (t' with vs_inst_idx := idx)
Proof
  strip_tac >> imp_res_tac bind_outputs_shared_fields >>
  fs[ricf_support_agree_def, adopt_return_fmp_def] >>
  Cases_on `ret.iret_adopt_fmp` >> gvs[]
QED

Theorem ricf_execution_ret_boundary:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  ptr_discipline lo C vs /\ opaque_use_ok fn /\
  active_inst fn inst s /\ inst.inst_opcode = RET /\
  step_inst fuel C inst s = IntRet ret se ==>
  se = s /\ ret.iret_adopt_fmp = NONE /\
  step_inst fuel Ct inst t = IntRet ret t /\
  ricf_opaque_live_stack_agree D (ricf_original_copy_ids C) tn maps stk targets s t /\
  ld_shared_agree D s.vs_call_ctx.cc_address tn s t /\
  s.vs_returndata = t.vs_returndata /\
  ircf_cross tn (ricf_phase_ranges 0 ledger) s t /\
  ricf_cert_crosses tn (ricf_phase_stack_ranges stk ledger) stk s t
Proof
  strip_tac >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    (fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
     metis_tac[occ_frame_reachable_projection]) >>
  `ricf_opaque_frame_agree fn D (ircf_dead (ricf_original_copy_ids C) s stk)
    sites (ricf_complete_params PG s.vs_params) G tn s t` by
    fs[ricf_execution_invariant_def] >>
  drule_all ricf_opaque_ret_step >>
  disch_then (qspec_then `Ct` strip_assume_tac) >> simp[] >>
  `ld_shared_agree D s.vs_call_ctx.cc_address tn s t /\ s.vs_returndata = t.vs_returndata` by
    (fs[ricf_opaque_frame_agree_def, ricf_frame_agree_def] >> conj_tac
     >- (drule taint_agree_shared >>
         simp[ricf_opaque_view_def, ld_shared_agree_def]) >>
     drule taint_agree_frame >>
     disch_then (mp_tac o AP_TERM ``\st:venom_state. st.vs_returndata``) >>
     simp[ricf_opaque_view_def]) >>
  fs[ricf_execution_invariant_def]
QED

Theorem ricf_return_phase_stack[local]:
  ricf_phase_stack_ranges (f::stk) ledger =
    ricf_phase_ranges 0 (ricf_phase_pop ledger) ::
      ricf_phase_stack_ranges stk (ricf_phase_pop ledger)
Proof
  simp[ricf_phase_stack_ranges_def, GENLIST_CONS, combinTheory.o_DEF,
       ricf_phase_ranges_pop]
QED

Theorem ricf_return_merge_bind[local]:
  bind_outputs outs vals (adopt_return_fmp ret (merge_callee_state caller se)) = SOME s' ==>
  merge_callee_state older (s' with vs_inst_idx := idx) = merge_callee_state older se
Proof
  strip_tac >>
  qpat_assum `bind_outputs _ _ _ = SOME s'`
    (mp_tac o AP_TERM ``\st. merge_callee_state older (st with vs_inst_idx := idx)`` o
      MATCH_MP ld_bind_outputs_vars_only) >>
  Cases_on `ret.iret_adopt_fmp` >> simp[adopt_return_fmp_def, merge_callee_state_def]
QED

Theorem ricf_return_merge_execution_equiv[local]:
  execution_equiv {} s t ==>
  merge_callee_state caller s = merge_callee_state caller t
Proof
  strip_tac >> fs[execution_equiv_def, merge_callee_state_def]
QED

Theorem ricf_execution_ret_restore:
  ricf_execution_invariant vs C D (f::stk) PG G tn fn inst s t
    n a (u::U) B HP H ledger E current (sites::maps) (caller::targets) tn /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\ ptr_discipline lo C vs /\ opaque_use_ok fn /\
  active_inst fn inst s /\ inst.inst_opcode = RET /\
  step_inst fuel C inst s = IntRet ret se /\
  execution_equiv {} t te /\
  bind_outputs f.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state f.cf_state se)) = SOME s' /\
  active_inst f.cf_fn next (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) ==>
  ?t'. step_inst fuel Ct inst t = IntRet ret t /\
    bind_outputs f.cf_inst.inst_outputs ret.iret_values
      (adopt_return_fmp ret (merge_callee_state caller te)) = SOME t' /\
    ricf_execution_invariant vs C D stk f.cf_params
      (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
      (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
      f.cf_fn next (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
      (t' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
      n u.of_owner U (DRESTRICT B {id | FST id <> a}) u.of_params
      (DRESTRICT u.of_prov (COMPL (set f.cf_inst.inst_outputs)))
      (ricf_phase_pop ledger) {id | id IN E /\ FST id <> a} sites maps targets
      (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
Proof
  strip_tac >> drule_all ricf_execution_ret_boundary >>
  disch_then (qspec_then `Ct` strip_assume_tac) >> gvs[] >>
  `!older. merge_callee_state older te = merge_callee_state older t` by
    metis_tac[ricf_return_merge_execution_equiv] >>
  qpat_x_assum `!older. merge_callee_state older te = _`
    (fn th => rewrite_tac[th]) >>
  `occ_frame_reachable vs C (f::stk) PG G tn fn inst s n a (u::U) B HP H` by
    fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
  `occurrence_natural_geometry 0 a (u::U) B (f::stk) s` by
    (drule occ_frame_reachable_geometry >> disch_then (qspec_then `0` mp_tac) >> simp[]) >>
  drule_all ricf_opaque_resume_next >> strip_tac >>
  `ricf_heterogeneous_source_ledger vs C stk f.cf_params
    (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
    (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
    f.cf_fn next (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
    n u.of_owner U (DRESTRICT B {id | FST id <> a}) u.of_params
    (DRESTRICT u.of_prov (COMPL (set f.cf_inst.inst_outputs)))
    (ricf_phase_pop ledger)` by
    (irule ricf_heterogeneous_source_ledger_return >>
     fs[ricf_execution_invariant_def] >> metis_tac[]) >>
  `ricf_heterogeneous_map_origins vs C stk f.cf_params
    (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
    (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
    f.cf_fn next (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) U
    (DRESTRICT B {id | FST id <> a}) sites /\
   ricf_heterogeneous_saved_map_origins vs C stk f.cf_params
    (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
    (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
    f.cf_fn next (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) U
    (DRESTRICT B {id | FST id <> a}) maps` by
    (irule ricf_heterogeneous_saved_map_origins_return >>
     fs[ricf_execution_invariant_def] >> metis_tac[]) >>
  `ricf_heterogeneous_support_origins vs C u.of_owner f.cf_fn U stk
    (DRESTRICT B {id | FST id <> a}) {id | id IN E /\ FST id <> a}` by
    (irule ricf_heterogeneous_support_return >> fs[ricf_execution_invariant_def] >>
     qexists_tac `fn` >> simp[]) >>
  `ricf_support_agree (DRESTRICT B {id | FST id <> a})
    {id | id IN E /\ FST id <> a} tn
    (merge_callee_state f.cf_state s) (merge_callee_state caller t)` by
    (irule ricf_return_support_pop >> fs[ricf_execution_invariant_def] >> metis_tac[]) >>
  `ricf_support_agree (DRESTRICT B {id | FST id <> a})
    {id | id IN E /\ FST id <> a}
    (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
    (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
    (t' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)` by
    (irule ricf_return_support_bind >> metis_tac[]) >>
  `s'.vs_allocas = f.cf_state.vs_allocas /\ s'.vs_params = f.cf_state.vs_params` by
    (qpat_assum `bind_outputs _ _ _ = SOME s'` (mp_tac o MATCH_MP ld_bind_outputs_vars_only) >>
     Cases_on `ret.iret_adopt_fmp` >>
     simp[adopt_return_fmp_def, merge_callee_state_def] >>
     simp[venom_state_component_equality]) >>
  `!older. merge_callee_state older (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) =
      merge_callee_state older s /\
    merge_callee_state older (t' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) =
      merge_callee_state older t` by
    (rpt strip_tac >> irule ricf_return_merge_bind >> metis_tac[]) >>
  `ircf_cross tn (ricf_phase_ranges 0 (ricf_phase_pop ledger)) s t /\
   ricf_cert_crosses tn (ricf_phase_stack_ranges stk (ricf_phase_pop ledger)) stk s t` by
    fs[ricf_execution_invariant_def, ricf_return_phase_stack, ricf_cert_crosses_cons] >>
  imp_res_tac bind_outputs_shared_fields >>
  qexists_tac `t'` >> simp[ricf_execution_invariant_def] >>
  fs[ircf_dead_def, ricf_complete_params_def,
     ricf_cert_crosses_def, ircf_cross_def, adopt_return_fmp_def,
     merge_callee_state_def] >>
  Cases_on `ret.iret_adopt_fmp` >> gvs[] >> metis_tac[]
QED

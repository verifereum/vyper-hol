Theory bodyPtrBytestringBuiltinsScratchState
Ancestors bodyPtrDefs compileEnv exprLoweringProps localPtrsProps

Theorem stor_taint_ok_fields_transport:
  stor_taint_ok cx tn s /\ tm.t_stor = tn.t_stor /\
  tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
  t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
  t.vs_call_ctx = s.vs_call_ctx ==>
  stor_taint_ok cx tm t
Proof
  simp[stor_taint_ok_def]
QED

Theorem scratch_stmt_state_rel_transport:
  stmt_state_rel ctx fn cenv cx es s /\
  (!name entry p sz. lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    lookup_var p t = lookup_var p s) /\
  (!name b len. local_region cenv es.scopes s name b len ==>
    mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory) /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  t.vs_fmp = s.vs_fmp /\ t.vs_labels = s.vs_labels /\
  t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_tx_ctx = s.vs_tx_ctx /\
  t.vs_block_ctx = s.vs_block_ctx /\ t.vs_logs = s.vs_logs /\
  t.vs_outcomes = s.vs_outcomes /\ t.vs_requests = s.vs_requests /\
  t.vs_pending_deletions = s.vs_pending_deletions /\
  t.vs_immutables = s.vs_immutables /\ t.vs_data_section = s.vs_data_section /\
  immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es t /\
  immutable_base_zero cenv t ==>
  stmt_state_rel ctx fn cenv cx es t
Proof
  strip_tac >>
  `local_ptrs_rel fn cenv es.scopes s` by fs[stmt_state_rel_def, state_rel_def] >>
  `local_ptrs_rel fn cenv es.scopes t` by
    (irule local_ptrs_rel_mem_agree >> goal_assum (drule_at Any) >>
     simp[] >> conj_tac >- metis_tac[] >>
     conj_tac >- metis_tac[] >> rpt strip_tac >> gvs[]) >>
  `state_rel fn cenv cx es t` by
    (irule state_rel_frame >> simp[] >>
     qexistsl_tac [`es`, `s`] >> simp[] >> fs[stmt_state_rel_def]) >>
  irule stmt_state_rel_allocas_frame >> goal_assum (drule_at Any) >> simp[] >>
  reverse conj_tac >- (qexistsl_tac [`es`, `s`] >> simp[]) >>
  fs[stmt_state_rel_def, immutable_alloca_sep_def] >> rpt strip_tac
  >- metis_tac[]
  >- metis_tac[] >>
  `local_region cenv es.scopes s id b sz` by
    (fs[local_region_def] >> metis_tac[]) >> metis_tac[]
QED

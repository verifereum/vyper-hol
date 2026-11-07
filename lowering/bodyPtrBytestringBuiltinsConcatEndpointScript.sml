Theory bodyPtrBytestringBuiltinsConcatEndpoint
Ancestors
  bodyPtrBytestringBuiltinsImmutableFrame bodyPtrBytestringBuiltinsScratchGhost
  bodyPtrBytestringBuiltinsScratchState exprSimPtrLiteralBuffer
  bodyPtrDefs compileEnv exprLoweringProps

(* Physical scratch footprints, rather than logical payload lengths, frame
   the semantic endpoint of either Concat arm. *)
Theorem concat_scratch_semantic_endpoint:
  stmt_state_rel ctx fn cenv cx es s /\ ~cenv.ce_is_ctor /\
  local_ptrs_reserved cenv st /\
  (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) /\
  mem_agree_outside writes t.vs_memory s.vs_memory /\
  (!name b len i. local_region cenv es.scopes s name b len /\
    b <= i /\ i < b+len ==> i NOTIN writes) /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  t.vs_fmp = s.vs_fmp /\ t.vs_labels = s.vs_labels /\
  t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_tx_ctx = s.vs_tx_ctx /\
  t.vs_block_ctx = s.vs_block_ctx /\ t.vs_logs = s.vs_logs /\
  t.vs_outcomes = s.vs_outcomes /\ t.vs_requests = s.vs_requests /\
  t.vs_pending_deletions = s.vs_pending_deletions /\
  t.vs_immutables = s.vs_immutables /\ t.vs_data_section = s.vs_data_section ==>
  stmt_state_rel ctx fn cenv cx es t
Proof
  strip_tac >> irule scratch_stmt_state_rel_transport >>
  conj_tac
  >- (irule immutable_base_zero_reserved_frame >>
      qexistsl_tac [`s`, `st`] >> simp[] >> fs[stmt_state_rel_def, state_rel_def]) >>
  conj_tac
  >- (irule immutables_rel_nonctor_data_frame >>
      simp[] >> qexists_tac `s` >> simp[] >> fs[stmt_state_rel_def, state_rel_def]) >>
  qexists_tac `s` >> simp[] >> conj_tac
  >- (rpt strip_tac >> irule literal_clean_window_agree >>
      goal_assum (drule_at Any) >> metis_tac[]) >>
  rpt strip_tac >> first_x_assum irule >>
  fs[local_ptrs_reserved_def] >> metis_tac[]
QED

Theorem concat_scratch_ghost_endpoint:
  stmt_state_rel ctx fn cenv cx es s /\
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv st /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s /\
    FLOOKUP H x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x)) /\
  mem_agree_outside writes t.vs_memory s.vs_memory /\
  (!name b len i. local_region cenv es.scopes s name b len /\
    b <= i /\ i < b+len ==> i NOTIN writes) /\
  tm.t_mem = tn.t_mem DIFF writes /\
  tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
  t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
  t.vs_call_ctx = s.vs_call_ctx ==>
  ghost_inv d cenv cx es H tm t
Proof
  strip_tac >> irule ghost_inv_scratch_write_transport >>
  conj_tac
  >- (irule stor_taint_ok_fields_transport >>
      qexistsl_tac [`s`, `tn`] >> simp[] >> fs[ghost_inv_def]) >>
  qexistsl_tac [`G`, `fn`, `s`, `st`, `tn`, `writes`] >> simp[] >>
  conj_tac >- (rpt strip_tac >> metis_tac[]) >>
  conj_tac >- (fs[mem_agree_outside_def] >> metis_tac[]) >>
  fs[stmt_state_rel_def, state_rel_def]
QED

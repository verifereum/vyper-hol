Theory linkedExternalReturnNone
Ancestors
  bodyFullPostsMods compileEnv e2eModsDefs sourceUnitExecutionMods
  vyperInterpreter vyperState vyperValueOperation vyperValue
  stmtLowering stmtSimDefs exprSimDefs bodyPtrDefs bodyFullShadowBodyInv
  nonreentrantExit nonreentrantEquiv loweringHalt gasOutcomeFullPostMods
  fragExec fragGasOriginPtr ptrDiscipline loweringStateRelDefs
  emitHelperProps venomState venomInst venomExecProofs e2eDefs list
  loweringPosts stmtSimReturn exprLoweringProps vyperStorageFootprint

Theorem linked_external_return_none_frag:
  ce.ce_nonreentrant = (nr,global_nonreentrant_slot,T,mut = View) /\
  ~ce.ce_is_ctor /\ ce.ce_return_pc = NONE /\ ce.ce_ctor_exit_label = NONE /\
  (nr ==> is_view_mut mut = (mut = View)) /\
  (nr /\ mut <> View ==> ~cx.txn.is_static /\
    cx.nonreentrant_slot = SOME global_nonreentrant_slot) /\
  external_return_type_mods mods exps cx.txn.function_name = NoneT /\
  tx_return_bytes_mods mods exps cx.txn NoneV [] ==>
  stmt_frag_full_mods (DF,0,d,ctx,shadow_ctx,PG,func,shadow_func) cx lctx
    (\H v ee gt r. ?us.
      safe_cast NoneTV v = SOME NoneV /\
      unlock_if_nr cx nr (is_view_mut mut) ee = (INL (),us) /\
      external_call_result_rel_mods H mods exps NoneT cx.txn
        (INL NoneV, finalize_pending_deletions
          (abstract_machine_from_state cx.sources caller_exports cx.layouts us),
         us.requests) r)
    ce (stmt_env ce lctx NoneT (Return NONE))
    (stmt_env (gas_shadow_env T ce) lctx NoneT (Return NONE))
    (eval_stmt cx (Return NONE)) es
Proof
  strip_tac >>
  `unlock_if_nr cx nr (is_view_mut mut) =
    (if nr /\ mut <> View then
       release_nonreentrant_lock cx.txn.target global_nonreentrant_slot
     else vyperState$return ())` by
    (Cases_on `nr` >> simp[unlock_if_nr_def] >>
     Cases_on `mut = View` >> fs[unlock_if_nr_def]) >>
  simp_tac std_ss [stmt_frag_full_mods_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `compile_stmt ce lctx NoneT (Return NONE) sa = ((),sb)` by
    (qpat_x_assum `stmt_env ce lctx NoneT (Return NONE) sa = (cenv',sb)` mp_tac >>
     Cases_on `compile_stmt ce lctx NoneT (Return NONE) sa` >>
     rename1 `compile_stmt ce lctx NoneT (Return NONE) sa = (answer,stmt_end)` >>
     Cases_on `answer` >>
     simp[stmt_env_def, declare_stmt_local_def, comp_bind_def,
          comp_ignore_bind_def, comp_return_def, pairTheory.UNCURRY]) >>
  Cases_on `(if nr then compile_nonreentrant_unlock global_nonreentrant_slot T (mut = View)
      else comp_return ()) sa` >>
  rename1 `(if nr then _ else _) sa = (answer,su)` >>
  Cases_on `answer` >>
  `emit_inst STOP [] [] su = ((),sb)` by
    (qpat_x_assum `compile_stmt ce lctx NoneT (Return NONE) sa = ((),sb)` mp_tac >>
     simp[compile_stmt_def, comp_ignore_bind_def, comp_bind_def, LET_THM]) >>
  `compile_return_unlock ce sa = ((),su)` by
    simp[compile_return_unlock_def] >>
  drule compile_return_unlock_shape >> strip_tac >>
  `cs_extends su sb` by drule_then ACCEPT_TAC cs_extends_emit_inst >>
  `fn_has_code sa su func /\ fn_has_code su sb func` by
    metis_tac[fn_has_code_split] >>
  reverse (Cases_on `storage_trace_domain cx st0 es.storage_trace`)
  >- (irule gas_outcome_full_mods_bad_nil >> simp[Once evaluate_def, raise_def]) >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace)
      es.storage_trace` by fs[storage_trace_domain_def] >>
  `allocas_from 0 s0 /\ (nr /\ mut <> View ==> ~s0.vs_call_ctx.cc_static)` by
    (qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _`
      (drule_then strip_assume_tac) >>
     simp[allocas_from_def] >>
     fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def]) >>
  mp_tac (Q.INST [`st` |-> `sa`, `su` |-> `su`, `sb` |-> `sb`,
    `nkey` |-> `global_nonreentrant_slot`, `iv` |-> `mut = View`,
    `lo` |-> `0:num`, `s` |-> `s0`, `G` |-> `G0`, `tn` |-> `tn0`,
    `DF` |-> `DF`, `cenv` |-> `ce`, `cx` |-> `cx`]
    (INST_TYPE [alpha |-> ``:256``] optional_transient_unlock_stop_joint_at)) >>
  impl_tac >- simp[] >> strip_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp ss` by
    (qpat_assum `ss = _` SUBST1_TAC >>
     qpat_x_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s0` mp_tac >>
     rpt (pop_assum kall_tac) >>
     Cases_on `nr /\ mut <> View` >>
     simp[ptrDisciplineTheory.allocas_below_fmp_def, halt_state_def, tstore_def] >>
     rpt strip_tac >> res_tac) >>
  irule gas_outcome_full_mods_exit >>
  reverse conj_tac >- FIRST_ASSUM ACCEPT_TAC >>
  qexistsl_tac [`G0`, `es`, `Halt ss`, `INR (ReturnException NoneV)`, `tn'`] >>
  simp[NoAsms, Once evaluate_def, raise_def, exit_result_def] >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  conj_tac
  >- (qpat_assum `!H explicit. dead_lo_ok _ _ _ _ _ /\ _ ==> _`
        (qspecl_then [`H`,`gas_explicit_sites ctx shadow_ctx`] mp_tac) >>
      impl_tac >- fs[ghost_inv_at_mods_def, dead_lo_ok_mods_def, dead_lo_ok_def] >>
      DISCH_THEN ACCEPT_TAC) >>
  qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp ss`
    (fn below => simp[NoAsms, stmt_exit_ptr_def, expr_exit_def, halt_exit_def, below]) >>
  gen_tac >>
  `state_rel H func ce cx
    (es with <| scopes := []; gas_obs := tail |>) s0` by
    (fs[stmt_state_rel_def] >>
     metis_tac[state_rel_scopes_nil, state_rel_gas_obs]) >>
  `?us. (if nr /\ mut <> View then
            release_nonreentrant_lock cx.txn.target global_nonreentrant_slot
          else vyperState$return ())
        (es with <| scopes := []; gas_obs := tail |>) = (INL (),us)` by
    (Cases_on `nr /\ mut <> View` >>
     simp[nonreentrantEquivTheory.release_nonreentrant_lock_execution, vyperStateTheory.return_def]) >>
  qexists_tac `us` >> simp[NoAsms, safe_cast_def] >>
  conj_tac >- (Cases_on `nr` >> Cases_on `mut` >> fs[is_view_mut_def]) >>
  qpat_x_assum `ss = halt_state _` kall_tac >>
  mp_tac (Q.INST [`cenv` |-> `ce`, `tx` |-> `cx.txn`, `tops` |-> `[]`,
    `es` |-> `es with <| scopes := []; gas_obs := tail |>`,
    `es'` |-> `us`, `s` |-> `s0`, `ss` |-> `ss`,
    `nkey` |-> `global_nonreentrant_slot`, `iv` |-> `mut = View`,
    `srcs` |-> `cx.sources`, `exps` |-> `caller_exports`, `layouts` |-> `cx.layouts`]
    (SPEC_ALL (INST_TYPE [alpha |-> ``:256``] external_halt_success_unlock))) >>
  impl_tac >- simp[] >> strip_tac >>
  `log_entry_corresponds (build_event_info_mods (type_env_all_modules mods) mods (K NONE))
      (type_env_all_modules mods) cx.txn.target =
    log_entry_corresponds (compiled_event_info []) (type_env []) cx.txn.target` by
    simp[NoAsms, FUN_EQ_THM, log_entry_corresponds_def] >>
  simp[NoAsms, external_call_result_rel_mods_def, LET_THM, logs_correspond_def] >>
  conj_tac
  >- (qpat_assum `tx_return_bytes_mods mods exps cx.txn NoneV []` mp_tac >>
      qpat_assum `external_return_type_mods mods exps cx.txn.function_name = NoneT`
        (fn ret_eq => qpat_assum `ss.vs_returndata = []` (fn data_eq =>
          simp[NoAsms, tx_return_bytes_mods_def, LET_THM, ret_eq, data_eq]))) >>
  qpat_assum `logs_correspond (compiled_event_info []) (type_env []) _ _ _`
    (assume_tac o PURE_REWRITE_RULE [logs_correspond_def]) >>
  qpat_assum `log_entry_corresponds (build_event_info_mods _ _ _) _ _ =
      log_entry_corresponds (compiled_event_info []) _ _`
    (fn events => PURE_REWRITE_TAC [events]) >>
  conj_tac >- qpat_assum `accounts_agree H cx.txn.target _ _` ACCEPT_TAC >>
  conj_tac
  >- qpat_assum `transient_agree H cx.txn.target _ _`
       (ACCEPT_TAC o SIMP_RULE (srw_ss()) []) >>
  conj_tac
  >- qpat_assum `LIST_REL (log_entry_corresponds (compiled_event_info []) _ _) _ _`
       (ACCEPT_TAC o SIMP_RULE (srw_ss()) []) >>
  FIRST_ASSUM ACCEPT_TAC
QED

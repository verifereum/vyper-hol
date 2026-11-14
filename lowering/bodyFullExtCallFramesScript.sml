(* The request boundary supplies one operational oracle endpoint for all
   finite storage horizons of the adopted source state. *)
Theory bodyFullExtCallFrames
Ancestors
  exprSimExtCallCase extCallOracleStep rawCallMemoryFramePtr gasOutcomeFull
  vyperStorageTrace vyperCallOutcomeFrame vyperCallOutcome vyperStorageFootprint

Theorem extcall_request_oracle_endpoint_initial_domain:
  extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sp stat
    addr_op value_op gas_op buf_op call_offset call_len cap target value_opt
    calldata has_default default_op default_ty default_opt ee t /\
  take_call_outcome target calldata value_opt ee = (INL (rq,oc),consumed) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  inst.inst_outputs = [out] /\ ~not_fresh_at sp out /\
  alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next ==>
  ?aw vw ao az ro gas u.
    eval_operand addr_op t = SOME aw /\ w2w aw = target /\
    eval_operand value_op t = SOME vw /\
    w2n vw = (case value_opt of NONE => 0 | SOME n => n) /\
    eval_operand call_offset t = SOME ao /\
    eval_operand call_len t = SOME az /\
    eval_operand buf_op t = SOME ro /\ eval_operand gas_op t = SOME gas /\
    read_memory (w2n ao) (w2n az) t = calldata /\
    exec_ext_call inst t gas aw vw ao az ro ((n2w cap):bytes32) stat =
      OK (update_var out (if oc.co_success then 1w else 0w) u) /\
    u = t with <|vs_outcomes := u.vs_outcomes; vs_requests := u.vs_requests;
      vs_accounts := u.vs_accounts; vs_transient := u.vs_transient;
      vs_logs := u.vs_logs; vs_pending_deletions := u.vs_pending_deletions;
      vs_returndata := u.vs_returndata; vs_memory := u.vs_memory|> /\
    u.vs_memory = (write_memory_with_expansion (w2n ro)
      (TAKE cap oc.co_returnData) t).vs_memory /\
    u.vs_returndata = oc.co_returnData /\
    wb_frame cenv es (SND (adopt_call_outcome rq oc consumed)) sa s0
      (update_var out (if oc.co_success then 1w else 0w) u) /\
    extcall_default_ready cx ret_type has_default default_op default_ty default_opt
      (update_var out (if oc.co_success then 1w else 0w) u) /\
    (!op. safe_operand sp op ==>
      eval_operand op (update_var out (if oc.co_success then 1w else 0w) u) =
      eval_operand op t) /\
    alloca_history func (update_var out (if oc.co_success then 1w else 0w) u) /\
    s0.vs_alloca_next <= (update_var out (if oc.co_success then 1w else 0w) u).vs_alloca_next /\
    (!H. valid_horizon cx st0 H
       (SND (adopt_call_outcome rq oc consumed)).storage_trace ==>
       stmt_state_rel H ctx func cenv cx (SND (adopt_call_outcome rq oc consumed))
         (update_var out (if oc.co_success then 1w else 0w) u))
Proof
  strip_tac >> drule_all extcall_request_oracle_core_initial_domain >> strip_tac >>
  qexistsl_tac [`aw`, `vw`, `ao`, `az`, `ro`, `gas`, `u`] >> simp[] >>
  `u.vs_vars = t.vs_vars /\ u.vs_allocas = t.vs_allocas /\
   u.vs_alloca_next = t.vs_alloca_next /\ u.vs_data_section = t.vs_data_section /\
   u.vs_current_bb = t.vs_current_bb /\ u.vs_inst_idx = t.vs_inst_idx` by
    (qpat_x_assum `u = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `!x. not_fresh_at sp x ==>
    lookup_var x (update_var out (if oc.co_success then 1w else 0w) u) = lookup_var x t` by
    (rpt strip_tac >> `x <> out` by metis_tac[] >>
     simp[venomStateTheory.update_var_def, venomStateTheory.lookup_var_def,
          finite_mapTheory.FLOOKUP_UPDATE]) >>
  drule oracle_take_adoption_locals >> strip_tac >>
  rpt conj_tac
  >- (`wb_frame cenv es ee sa s0
         (update_var out (if oc.co_success then 1w else 0w) u)` by
        (drule (ONCE_REWRITE_RULE [GSYM AND_IMP_INTRO] extcall_request_wb_frame) >>
         disch_then (qspecl_then
           [`update_var out (if oc.co_success then 1w else 0w) u`, `ro`, `oc.co_returnData`] mp_tac) >>
         fs[venomStateTheory.update_var_def] >> metis_tac[]) >>
      fs[loweringPostsTheory.wb_frame_def, loweringPostsTheory.locals_kept_def,
         loweringPostsTheory.popped_kept_def] >> metis_tac[])
  >- (drule (ONCE_REWRITE_RULE [GSYM AND_IMP_INTRO] extcall_request_default_frame) >>
      disch_then (qspecl_then
        [`update_var out (if oc.co_success then 1w else 0w) u`, `ro`, `oc.co_returnData`] mp_tac) >>
      fs[venomStateTheory.update_var_def] >> metis_tac[])
  >- (rpt strip_tac >>
      Cases_on `op` >> fs[exprSafeOperandTheory.safe_operand_def,
        venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
        venomStateTheory.update_var_def] >> metis_tac[])
  >- (irule allocaHistoryTheory.alloca_history_frame >> qexists_tac `t` >>
      simp[venomStateTheory.update_var_def])
  >- simp[venomStateTheory.update_var_def] >>
  rpt strip_tac >> `valid_horizon cx st0 H ee.storage_trace` by
    (`adopt_call_outcome rq oc consumed =
        (INL (), SND (adopt_call_outcome rq oc consumed))` by
       simp[adopt_call_outcome_equation] >>
     metis_tac[valid_horizon_frame, storage_trace_frame_adopt,
       storage_trace_frame_take_call]) >>
  `local_ptrs_rel func cenv ee.scopes u /\
   immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor ee u` by
    (drule_all extcall_request_memory_rel >> simp[]) >>
  `state_rel H func cenv cx (SND (adopt_call_outcome rq oc consumed)) u` by metis_tac[] >>
  `local_ptrs_reserved cenv sp` by fs[extcall_request_ready_def] >>
  `not_local_ptr cenv (SND (adopt_call_outcome rq oc consumed)).scopes out` by
    metis_tac[exprSimOperandsTheory.fresh_not_local_ptr] >>
  `state_rel H func cenv cx (SND (adopt_call_outcome rq oc consumed))
     (update_var out (if oc.co_success then 1w else 0w) u)` by
    metis_tac[exprLoweringPropsTheory.state_rel_update_var_local] >>
  irule extcall_request_structural_frame >> metis_tac[]
QED

(* Compatibility interfaces: a valid output trace supplies an input domain. *)
Theorem extcall_request_oracle_core:
  extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sp stat
    addr_op value_op gas_op buf_op call_offset call_len cap target value_opt
    calldata has_default default_op default_ty default_opt ee t /\
  take_call_outcome target calldata value_opt ee = (INL (rq,oc),consumed) /\
  storage_trace_domain cx st0
    (SND (adopt_call_outcome rq oc consumed)).storage_trace /\
  inst.inst_outputs = [out] ==>
  ?aw vw ao az ro gas u.
    eval_operand addr_op t = SOME aw /\ w2w aw = target /\
    eval_operand value_op t = SOME vw /\
    w2n vw = (case value_opt of NONE => 0 | SOME n => n) /\
    eval_operand call_offset t = SOME ao /\
    eval_operand call_len t = SOME az /\
    eval_operand buf_op t = SOME ro /\ eval_operand gas_op t = SOME gas /\
    read_memory (w2n ao) (w2n az) t = calldata /\
    exec_ext_call inst t gas aw vw ao az ro ((n2w cap):bytes32) stat =
      OK (update_var out (if oc.co_success then 1w else 0w) u) /\
    u = t with <|vs_outcomes := u.vs_outcomes; vs_requests := u.vs_requests;
      vs_accounts := u.vs_accounts; vs_transient := u.vs_transient;
      vs_logs := u.vs_logs; vs_pending_deletions := u.vs_pending_deletions;
      vs_returndata := u.vs_returndata; vs_memory := u.vs_memory|> /\
    u.vs_memory = (write_memory_with_expansion (w2n ro)
      (TAKE cap oc.co_returnData) t).vs_memory /\
    u.vs_returndata = oc.co_returnData /\
    (!H. valid_horizon cx st0 H
       (SND (adopt_call_outcome rq oc consumed)).storage_trace ==>
      (local_ptrs_rel func cenv ee.scopes u /\
       immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor ee u ==>
       state_rel H func cenv cx (SND (adopt_call_outcome rq oc consumed)) u))
Proof
  strip_tac >> irule extcall_request_oracle_core_initial_domain >>
  goal_assum (drule_at Any) >> simp[] >>
  spose_not_then assume_tac >>
  `adopt_call_outcome rq oc consumed =
     (INL (), SND (adopt_call_outcome rq oc consumed))` by
    simp[adopt_call_outcome_equation] >>
  metis_tac[gasStorageTheory.storage_trace_frame_preserves_bad_domain,
            storage_trace_frame_take_call, storage_trace_frame_adopt]
QED

Theorem extcall_request_oracle_endpoint:
  extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sp stat
    addr_op value_op gas_op buf_op call_offset call_len cap target value_opt
    calldata has_default default_op default_ty default_opt ee t /\
  take_call_outcome target calldata value_opt ee = (INL (rq,oc),consumed) /\
  storage_trace_domain cx st0
    (SND (adopt_call_outcome rq oc consumed)).storage_trace /\
  inst.inst_outputs = [out] /\ ~not_fresh_at sp out /\
  alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next ==>
  ?aw vw ao az ro gas u.
    eval_operand addr_op t = SOME aw /\ w2w aw = target /\
    eval_operand value_op t = SOME vw /\
    w2n vw = (case value_opt of NONE => 0 | SOME n => n) /\
    eval_operand call_offset t = SOME ao /\
    eval_operand call_len t = SOME az /\
    eval_operand buf_op t = SOME ro /\ eval_operand gas_op t = SOME gas /\
    read_memory (w2n ao) (w2n az) t = calldata /\
    exec_ext_call inst t gas aw vw ao az ro ((n2w cap):bytes32) stat =
      OK (update_var out (if oc.co_success then 1w else 0w) u) /\
    u = t with <|vs_outcomes := u.vs_outcomes; vs_requests := u.vs_requests;
      vs_accounts := u.vs_accounts; vs_transient := u.vs_transient;
      vs_logs := u.vs_logs; vs_pending_deletions := u.vs_pending_deletions;
      vs_returndata := u.vs_returndata; vs_memory := u.vs_memory|> /\
    u.vs_memory = (write_memory_with_expansion (w2n ro)
      (TAKE cap oc.co_returnData) t).vs_memory /\
    u.vs_returndata = oc.co_returnData /\
    wb_frame cenv es (SND (adopt_call_outcome rq oc consumed)) sa s0
      (update_var out (if oc.co_success then 1w else 0w) u) /\
    extcall_default_ready cx ret_type has_default default_op default_ty default_opt
      (update_var out (if oc.co_success then 1w else 0w) u) /\
    (!op. safe_operand sp op ==>
      eval_operand op (update_var out (if oc.co_success then 1w else 0w) u) =
      eval_operand op t) /\
    alloca_history func (update_var out (if oc.co_success then 1w else 0w) u) /\
    s0.vs_alloca_next <= (update_var out (if oc.co_success then 1w else 0w) u).vs_alloca_next /\
    (!H. valid_horizon cx st0 H
       (SND (adopt_call_outcome rq oc consumed)).storage_trace ==>
       stmt_state_rel H ctx func cenv cx (SND (adopt_call_outcome rq oc consumed))
         (update_var out (if oc.co_success then 1w else 0w) u))
Proof
  strip_tac >> irule extcall_request_oracle_endpoint_initial_domain >>
  goal_assum (drule_at Any) >> simp[] >>
  spose_not_then assume_tac >>
  `adopt_call_outcome rq oc consumed =
     (INL (), SND (adopt_call_outcome rq oc consumed))` by
    simp[adopt_call_outcome_equation] >>
  metis_tac[gasStorageTheory.storage_trace_frame_preserves_bad_domain,
            storage_trace_frame_take_call, storage_trace_frame_adopt]
QED

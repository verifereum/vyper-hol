(* The request boundary supplies one operational oracle endpoint for all
   finite storage horizons of the adopted source state. *)
Theory bodyFullExtCallFrames
Ancestors
  exprSimExtCallCase extCallOracleStep rawCallMemoryFramePtr gasOutcomeFull
  vyperStorageTrace vyperCallOutcomeFrame vyperCallOutcome vyperStorageFootprint

Theorem extcall_request_oracle_core_initial_domain:
  extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sp stat
    addr_op value_op gas_op buf_op call_offset call_len cap target value_opt
    calldata has_default default_op default_ty default_opt ee t /\
  take_call_outcome target calldata value_opt ee = (INL (rq,oc),consumed) /\
  storage_trace_domain cx st0 ee.storage_trace /\
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
  strip_tac >>
  `!H. valid_horizon cx st0 H
      (SND (adopt_call_outcome rq oc consumed)).storage_trace ==>
      valid_horizon cx st0 H ee.storage_trace` by
    (rpt strip_tac >>
     `adopt_call_outcome rq oc consumed =
        (INL (), SND (adopt_call_outcome rq oc consumed))` by
       simp[adopt_call_outcome_equation] >>
     metis_tac[valid_horizon_frame, storage_trace_frame_adopt,
               storage_trace_frame_take_call]) >>
  fs[extcall_request_ready_def] >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace)
    ee.storage_trace` by fs[storage_trace_domain_def] >>
  `state_rel (storage_trace_horizon ee.storage_trace)
    func cenv cx ee t` by metis_tac[exprLoweringPropsTheory.stmt_state_rel_def] >>
  Cases_on `eval_operand gas_op t` >> gvs[] >> rename1 `_ = SOME gas` >>
  `cap < dimword (:256)` by decide_tac >>
  `w2n ((n2w cap):bytes32) = cap` by simp[] >>
  `IS_NONE value_opt = (value_opt = NONE)` by (Cases_on `value_opt` >> simp[]) >>
  VALID (drule_then mp_tac (INST_TYPE [Type.beta |-> ``:bytes32``, Type.gamma |-> ``:256``, Type.delta |-> ``:256``] exec_ext_call_oracle_step) >>
    disch_then (qspec_then `inst` mp_tac) >> simp[] >>
    disch_then drule_all >>
    disch_then (strip_assume_tac o Q.ISPECL
      [`gas:bytes32`, `ro:bytes32`, `(n2w cap):bytes32`])) >>
  qexists_tac `s'` >> simp[] >> rpt strip_tac >>
  `state_rel H func cenv cx ee t` by metis_tac[exprLoweringPropsTheory.stmt_state_rel_def] >>
  VALID (drule_then mp_tac (INST_TYPE [Type.beta |-> ``:bytes32``, Type.gamma |-> ``:256``, Type.delta |-> ``:256``] exec_ext_call_oracle_step) >>
    disch_then (qspec_then `inst` mp_tac) >> simp[] >>
    disch_then drule_all >>
    disch_then (strip_assume_tac o Q.ISPECL
      [`gas:bytes32`, `ro:bytes32`, `(n2w cap):bytes32`])) >>
  `s'' = s'` by
    (qpat_x_assum `exec_ext_call _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     qpat_x_assum `exec_ext_call _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     qpat_x_assum `s'' = _` mp_tac >>
     qpat_x_assum `s' = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[venomStateTheory.update_var_def,
          venomStateTheory.venom_state_component_equality] >> metis_tac[]) >>
  gvs[]
QED

Theorem extcall_request_memory_rel:
  extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sp stat
    addr_op value_op gas_op buf_op call_offset call_len cap target value_opt
    calldata has_default default_op default_ty default_opt ee t /\
  valid_horizon cx st0 H ee.storage_trace /\
  eval_operand buf_op t = SOME ro /\
  u.vs_vars = t.vs_vars /\ u.vs_allocas = t.vs_allocas /\
  u.vs_alloca_next = t.vs_alloca_next /\
  u.vs_data_section = t.vs_data_section /\
  u.vs_memory = (write_memory_with_expansion (w2n ro) (TAKE cap rd) t).vs_memory ==>
  local_ptrs_rel func cenv ee.scopes u /\
  immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor ee u
Proof
  strip_tac >> fs[extcall_request_ready_def] >>
  `LENGTH (TAKE cap rd) <= cap` by simp[listTheory.LENGTH_TAKE_EQ] >>
  `local_ptrs_rel func cenv ee.scopes t /\
   immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor ee t` by
    metis_tac[exprLoweringPropsTheory.stmt_state_rel_def,
              loweringStateRelDefsTheory.state_rel_def] >>
  conj_tac
  >- (irule local_ptrs_rel_clean_write_frame >>
      qexistsl_tac [`TAKE cap rd`, `w2n ro`, `t`] >>
      simp[venomStateTheory.lookup_var_def] >> rpt strip_tac >>
      first_x_assum drule >>
      simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  irule loweringSliceTheory.immutables_rel_mem_agree >> qexists_tac `t` >>
  simp[venomMemPropsTheory.LENGTH_write_memory_with_expansion] >>
  rpt strip_tac >>
  irule valueEncodingPropsTheory.write_memory_mem_bytes_at_disjoint >>
  first_x_assum drule_all >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem extcall_request_wb_frame:
  extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sp stat
    addr_op value_op gas_op buf_op call_offset call_len cap target value_opt
    calldata has_default default_op default_ty default_opt ee t /\
  eval_operand buf_op t = SOME ro /\
  v.vs_allocas = t.vs_allocas /\ v.vs_alloca_next = t.vs_alloca_next /\
  v.vs_memory = (write_memory_with_expansion (w2n ro) (TAKE cap rd) t).vs_memory /\
  (!x. not_fresh_at sp x ==> lookup_var x v = lookup_var x t) ==>
  wb_frame cenv es ee sa s0 v
Proof
  strip_tac >> fs[extcall_request_ready_def] >>
  `LENGTH (TAKE cap rd) <= cap` by simp[listTheory.LENGTH_TAKE_EQ] >>
  fs[loweringPostsTheory.wb_frame_def] >> rpt conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sp x` by
        metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >> metis_tac[])
  >- (rpt strip_tac >>
      `FLOOKUP t.vs_allocas aid = SOME (off,sz)` by metis_tac[] >>
      `regions_disjoint (w2n ro) cap off sz` by metis_tac[] >>
      `mem_bytes_at off sz
        (write_memory_with_expansion (w2n ro) (TAKE cap rd) t).vs_memory =
       mem_bytes_at off sz t.vs_memory` by
        (irule valueEncodingPropsTheory.write_memory_mem_bytes_at_disjoint >>
         fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
      metis_tac[]) >>
  irule exprSimPropsTheory.locals_kept_regions_tail >> qexists_tac `t` >>
  simp[] >> rpt strip_tac >>
  irule valueEncodingPropsTheory.write_memory_mem_bytes_at_disjoint >>
  first_x_assum drule >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem extcall_request_default_frame:
  extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sp stat
    addr_op value_op gas_op buf_op call_offset call_len cap target value_opt
    calldata has_default default_op default_ty default_opt ee t /\
  eval_operand buf_op t = SOME ro /\
  v.vs_alloca_next = t.vs_alloca_next /\
  v.vs_memory = (write_memory_with_expansion (w2n ro) (TAKE cap rd) t).vs_memory /\
  (!x. not_fresh_at sp x ==> lookup_var x v = lookup_var x t) ==>
  extcall_default_ready cx ret_type has_default default_op default_ty default_opt v
Proof
  strip_tac >> fs[extcall_request_ready_def] >>
  `safe_operand sp default_op` by fs[] >>
  `!w. eval_operand default_op t = SOME w ==>
       eval_operand default_op v = SOME w` by
    (rpt strip_tac >> irule exprBopSimPropsTheory.eval_operand_frame >>
     fs[exprSafeOperandTheory.safe_operand_def] >>
     qexistsl_tac [`sp`, `t`] >> metis_tac[]) >>
  fs[extcall_default_ready_def] >> rpt strip_tac >>
  first_x_assum drule >>
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  qexistsl_tac [`tv`, `rtv`, `w`] >> simp[] >>
  Cases_on `is_word_type default_ty`
  >- gvs[loweringPostsTheory.expr_val_rel_def] >>
  irule exprSimPropsTheory.expr_val_rel_footprint_agree >>
  simp[] >> qexists_tac `t` >> simp[] >>
  sym_tac >>
  irule valueEncodingPropsTheory.write_memory_mem_bytes_at_disjoint >>
  `LENGTH (TAKE cap rd) <= cap` by simp[listTheory.LENGTH_TAKE_EQ] >>
  `regions_disjoint (w2n ro) cap (w2n w) (val_footprint tv d)` by metis_tac[] >>
  fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem extcall_request_structural_frame:
  extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sp stat
    addr_op value_op gas_op buf_op call_offset call_len cap target value_opt
    calldata has_default default_op default_ty default_opt ee t /\
  take_call_outcome target calldata value_opt ee = (INL (rq,oc),consumed) /\
  valid_horizon cx st0 H (SND (adopt_call_outcome rq oc consumed)).storage_trace /\
  state_rel H func cenv cx (SND (adopt_call_outcome rq oc consumed))
    (update_var out word u) /\
  ~not_fresh_at sp out /\
  u = t with <|vs_outcomes := u.vs_outcomes; vs_requests := u.vs_requests;
    vs_accounts := u.vs_accounts; vs_transient := u.vs_transient;
    vs_logs := u.vs_logs; vs_pending_deletions := u.vs_pending_deletions;
    vs_returndata := u.vs_returndata; vs_memory := u.vs_memory|> ==>
  stmt_state_rel H ctx func cenv cx (SND (adopt_call_outcome rq oc consumed))
    (update_var out word u)
Proof
  strip_tac >>
  `valid_horizon cx st0 H ee.storage_trace` by
    (`adopt_call_outcome rq oc consumed =
        (INL (), SND (adopt_call_outcome rq oc consumed))` by
       simp[adopt_call_outcome_equation] >>
     metis_tac[valid_horizon_frame, storage_trace_frame_adopt,
       storage_trace_frame_take_call]) >>
  drule oracle_take_adoption_locals >> strip_tac >>
  fs[extcall_request_ready_def] >>
  `stmt_state_rel H ctx func cenv cx ee t` by metis_tac[] >>
  `!x. not_fresh_at sp x ==>
    lookup_var x (update_var out word u) = lookup_var x t` by
    (rpt strip_tac >>
     `x <> out` by metis_tac[] >>
     simp[venomStateTheory.update_var_def, venomStateTheory.lookup_var_def] >>
     qpat_x_assum `u = _` (fn th => once_rewrite_tac[th]) >>
     simp[finite_mapTheory.FLOOKUP_UPDATE]) >>
  `u.vs_allocas = t.vs_allocas /\ u.vs_alloca_next = t.vs_alloca_next /\
   u.vs_labels = t.vs_labels /\ u.vs_fmp = t.vs_fmp` by
    (qpat_x_assum `u = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  fs[exprLoweringPropsTheory.stmt_state_rel_def] >> rpt conj_tac
  >- (irule localPtrsPropsTheory.alloca_inv_fields >> qexists_tac `t` >>
      simp[venomStateTheory.update_var_def] >> metis_tac[])
  >- (fs[exprLoweringPropsTheory.alloca_room_def,
         exprLoweringPropsTheory.pending_alloca_size_def,
         venomStateTheory.update_var_def] >> metis_tac[])
  >- (fs[exprLoweringPropsTheory.fmp_room_def,
         exprLoweringPropsTheory.pending_alloca_size_def,
         venomStateTheory.update_var_def] >> metis_tac[])
  >- (irule exprLoweringPropsTheory.immutable_alloca_sep_fields >>
      qexistsl_tac [`t`, `ee`] >> simp[venomStateTheory.update_var_def] >>
      rpt strip_tac >> qexists_tac `id` >>
      irule exprSimPropsTheory.local_region_frame >> conj_tac
      >- (qexists_tac `func` >> fs[loweringStateRelDefsTheory.state_rel_def]) >>
      qexistsl_tac [`sp`, `ee.scopes`, `update_var out word u`] >>
      simp[venomStateTheory.update_var_def] >>
      fs[venomStateTheory.update_var_def] >> metis_tac[])
  >- (irule exprLoweringPropsTheory.immutable_base_zero_frame >>
      qexists_tac `t` >> simp[venomStateTheory.update_var_def] >>
      fs[loweringStateRelDefsTheory.local_ptrs_reserved_def,
         venomStateTheory.update_var_def] >> metis_tac[]) >>
  fs[venomStateTheory.update_var_def] >> metis_tac[]
QED

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

(* A saved head is transported across the actual successful suffix. *)
Theory createCtorSavedConsMods
Ancestors
  createCtorSavedCons createExprSizeExitDefsMods
  bodyFullExtCallPosList bodyFullExtCallPosTransport bodyFullExtCallPosAggregate
  bodyInvCodeProps targetPureWalkSource vyperMachineFrame exprSimWordArgs
  allocaSiteResource freshWrites vyperStorageFootprint vyperStorageTrace
  exprLoweringProps wordArgsPtr stateRelProj list exprSimProps
  loweringPosts compileEnv vyperInterpreter vyperState exprSimMemDefs bodyPtrDefs
  exprLowering venomState loweringStateRelDefs context bodyFullExtCallSavedOperand
  ptrDiscipline exprSimUnwrap bodyFullPostsMods bodyFullShadowBodyInv
  abiEncodeArgsScopes logValueFramePtr valueEncodingProps
  stmtSimAssignStorageCopy vyperStorageBackend sourceUnitExecution accountsRelProps
  exprPtrUnwrapStorageFacts immutableRegionFrameProps
  createCtorEncoderImmutableRootMods createCtorEncoderImmutableMemFrameMods

(* Scope equality permits the full local window, including length words,
   to be read through the writeback frame. *)
Theorem ctor_borrowed_local_window[local]:
  wb_frame ce es ee st s t /\ ee.scopes = es.scopes /\
  local_region ce es.scopes s n b sz /\ b <= a /\ a + k <= b + sz ==>
  mem_bytes_at a k t.vs_memory = mem_bytes_at a k s.vs_memory
Proof
  strip_tac >>
  `mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory` by
    (fs[wb_frame_def,locals_kept_def] >>
     qpat_assum `!n b sz. local_region _ _ _ _ _ _ ==> _`
       (drule_then ACCEPT_TAC)) >>
  `a = b + (a - b) /\ a - b + k <= sz` by decide_tac >>
  drule mem_bytes_at_translated_window >>
  disch_then (qspecl_then [`a-b`,`k`] mp_tac) >> simp[]
QED

Theorem ctor_borrowed_footprint_frame[local]:
  ee.scopes = es.scopes /\ wb_frame ce es ee st s t /\
  ghost_kept_at lo ce es st G tn s G' tn' /\
  expr_val_at ce cx ty sa st es v op s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  eval_operand op s = SOME w ==>
  val_wf tv v /\
  mem_bytes_at (w2n w) (val_footprint tv v) t.vs_memory =
    mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory /\
  (!i. w2n w <= i /\ i < w2n w + val_footprint tv v /\
       i IN tn'.t_mem ==> i IN tn.t_mem)
Proof
  strip_tac >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_val_at_def] >> strip_tac >> gvs[]
  >- (conj_tac
      >- (`mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory` by
            (fs[wb_frame_def] >> first_x_assum irule >> metis_tac[]) >>
          `w2n w = b + (w2n w - b)` by decide_tac >>
          `w2n w - b + val_footprint tv v <= sz` by decide_tac >>
          drule mem_bytes_at_translated_window >>
          disch_then (qspecl_then [`w2n w - b`,`val_footprint tv v`] mp_tac) >> simp[]) >>
      rpt strip_tac >> fs[ghost_kept_at_def] >>
      qpat_assum `!aid off sz i. FLOOKUP _ _ = _ /\ _ ==> _` irule >>
      conj_tac >- (qexistsl_tac [`aid`,`b`,`sz`] >> simp[] >>
                   (first_assum ACCEPT_TAC ORELSE decide_tac)) >> simp[])
  >- (conj_tac
      >- (irule ctor_borrowed_local_window >> metis_tac[]) >>
      rpt strip_tac >> fs[ghost_kept_at_def] >>
      qpat_assum `!n b sz i. local_region _ _ _ _ _ _ /\ _ ==> _` irule >>
      conj_tac >- simp[] >> qexistsl_tac [`b`,`n`,`sz`] >> simp[] >> decide_tac) >>
  simp[valueEncodingDefsTheory.mem_bytes_at_def] >> rpt strip_tac >> decide_tac
QED

Theorem ctor_saved_expr_val_at_frame[local]:
  expr_val_at cenv cx ty sa sm mid v op t /\
  eval_operand op u = eval_operand op t /\ sm.cs_next_id <= sb.cs_next_id /\
  (!aid row. FLOOKUP t.vs_allocas aid = SOME row ==>
             FLOOKUP u.vs_allocas aid = SOME row) /\
  (!n b sz. local_region cenv mid.scopes t n b sz <=>
            local_region cenv ee.scopes u n b sz) ==>
  expr_val_at cenv cx ty sa sb ee v op u
Proof
  simp[expr_val_at_def] >> strip_tac >> rpt strip_tac >>
  first_x_assum drule >> simp[] >> strip_tac >>
  qexists_tac `w` >> simp[]
  >- (`aid < sb.cs_next_id` by decide_tac >>
      disj1_tac >> qexistsl_tac [`aid`,`b`,`sz`] >> simp[] >> first_assum ACCEPT_TAC) >>
  disj2_tac >> disj1_tac >> qexistsl_tac [`n`,`b`,`sz`] >> simp[]
QED

Theorem ctor_snapshot_type[local]:
  compile_snapshot_vv ce copy input s = (saved,t) ==> vv_type saved = vv_type input
Proof
  simp[compile_snapshot_vv_def] >> rpt IF_CASES_TAC >>
  simp[comp_bind_def,comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[vv_type_def]
QED

(* Common frame for stack operands and retained memory operands. *)
Theorem ctor_borrowed_operand_frame[local]:
  expr_val_at ce cx ty si ss mid v op t /\
  ptr_val_ok cx ty v op G1 tn1 t /\ eval_operand op t = SOME w /\
  (~is_word_type ty ==> ee.scopes = mid.scopes) /\
  wb_frame ce mid ee ss t u /\ ghost_kept_at lo ce mid ss G1 tn1 t G2 tn2 /\
  (!x. op = Var x ==> not_fresh_at ss x) /\ u.vs_labels = t.vs_labels /\
  (!n b sz. local_region ce mid.scopes t n b sz <=> local_region ce ee.scopes u n b sz) ==>
  eval_operand op u = eval_operand op t /\
  expr_val_at ce cx ty si ss ee v op u /\
  ptr_val_ok cx ty v op G2 tn2 u /\
  (!e. ptr_buf_ok ce e op G1 t ==> ptr_buf_ok ce e op G2 u) /\
  (!tv w. ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
    eval_operand op t = SOME w ==>
    mem_bytes_at (w2n w) (val_footprint tv v) u.vs_memory =
    mem_bytes_at (w2n w) (val_footprint tv v) t.vs_memory)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `eval_operand op u = eval_operand op t` by
    (Cases_on `op` >> gvs[eval_operand_def,wb_frame_def] >> simp[]) >>
  `(!x. op = Var x ==> FLOOKUP G2 x = FLOOKUP G1 x) /\
   op_taint tn2 op = op_taint tn1 op` by
    (Cases_on `op` >> gvs[ghost_kept_at_def,op_taint_def] >> metis_tac[]) >>
  `!tv w. ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
     eval_operand op t = SOME w ==>
     val_wf tv v /\
     mem_bytes_at (w2n w) (val_footprint tv v) u.vs_memory =
       mem_bytes_at (w2n w) (val_footprint tv v) t.vs_memory /\
     (!i. w2n w <= i /\ i < w2n w + val_footprint tv v /\ i IN tn2.t_mem ==>
          i IN tn1.t_mem)` by
    (rpt gen_tac >> strip_tac >> `ee.scopes = mid.scopes` by simp[] >>
     drule_all ctor_borrowed_footprint_frame >> simp[]) >>
  simp[] >> rpt conj_tac
  >- (irule ctor_saved_expr_val_at_frame >> qexistsl_tac [`mid`,`ss`,`t`] >> fs[wb_frame_def])
  >- (irule ptr_val_ok_footprint_frame >> qexistsl_tac [`G1`,`t`,`tn1`] >> simp[])
  >- (rpt strip_tac >> irule ptr_buf_ok_frame >> qexistsl_tac [`G1`,`t`] >> simp[]) >>
  rpt gen_tac >> strip_tac >> first_x_assum drule_all >> simp[]
QED

Theorem ctor_saved_store_bound[local]:
  vv_store_bound cx ty ty mid raw sv t /\ read_result cx raw mid = (INL v,mid) /\
  eval_operand (vv_operand sv) u = eval_operand (vv_operand sv) t /\
  t.vs_alloca_next <= u.vs_alloca_next ==>
  vv_store_bound cx ty ty ee (Value v) sv u
Proof
  strip_tac >>
  `vv_store_bound cx ty ty mid raw sv u` by
    (irule vv_store_bound_frame_mem_src >> qexists_tac `t` >> simp[]) >>
  qpat_x_assum `vv_store_bound cx ty ty mid raw sv t` kall_tac >>
  gvs[vv_store_bound_def,read_result_def,return_def] >> conj_tac >> first_assum ACCEPT_TAC
QED

Theorem ctor_saved_slot_taint_dead[local]:
  ghost_inv_at_mods D lo d cenv cx ee G tn u /\ dead_lo_ok_mods H D lo cenv cx /\
  (k,b) IN (if tr then tn.t_trans else tn.t_stor) ==>
  storage_dead H tr (if tr then contract_transient u else contract_storage u) (w2n k) b
Proof
  Cases_on `tr` >>
  gvs[ghost_inv_at_mods_def, stor_taint_ok_at_def, dead_lo_ok_mods_def, cx_dead_def,
      pred_setTheory.SUBSET_DEF, contract_storage_def, contract_transient_def,
      vfmStateTheory.lookup_account_def] >>
  rpt strip_tac >> first_x_assum drule >>
  Cases_on `u.vs_call_ctx.cc_address = cx.txn.target` >> simp[]
QED

Theorem ctor_saved_slot_read_dead[local]:
  storage_agree (storage_dead H tr st) st rt /\
  storage_range_agree st rt w tv /\ storage_read_live H tr st w tv /\
  storage_dead H tr rt (w2n k) b /\ w2n w <= w2n k /\ w2n k < w2n w + type_slot_size tv ==>
  dead_bytes rt (w2n w) tv (w2n k) b
Proof
  strip_tac >> drule storage_agree_storage_dead >> strip_tac >>
  drule storage_range_agree_dead_bytes >> strip_tac >>
  fs[storage_read_live_def] >> metis_tac[]
QED

Theorem ctor_saved_slot_endpoint[local]:
  p.ptr_location = slot_loc tr /\
  read_result cx raw mid = (INL v,mid) /\
  vv_holds_mods cenv cx ty raw (LocatedValue ty p) mid t /\
  ptr_vv_ok cx ty raw (LocatedValue ty p) mid G1 tn1 t /\
  vv_storage_live H cx (LocatedValue ty p) mid t /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
  ghost_kept_at lo cenv mid sm G1 tn1 t G2 tn2 /\
  (!x w. not_fresh_at sm x /\ lookup_var x t = SOME w ==> lookup_var x u = SOME w) /\
  u.vs_labels = t.vs_labels /\ get_storage cx ee tr = get_storage cx mid tr /\
  stmt_state_rel H ctx func cenv cx ee u /\
  ghost_inv_at_mods D lo d cenv cx ee G2 tn2 u /\ dead_lo_ok_mods H D lo cenv cx ==>
  (?r. read_result cx r ee = (INL v,ee) /\
    vv_holds_mods cenv cx ty r (LocatedValue ty p) ee u /\
    vv_at cenv cx ty sa sb ee r (LocatedValue ty p) u /\
    ptr_vv_ok cx ty r (LocatedValue ty p) ee G2 tn2 u /\
    vv_store_bound cx ty ty ee r (LocatedValue ty p) u) /\
  vv_storage_live H cx (LocatedValue ty p) ee u
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `?w. eval_operand p.ptr_operand t = SOME w /\ storage_holds cx tr ty raw w mid t` by
    (Cases_on `tr` >> gvs[vv_holds_mods_def,vv_holds_def,slot_loc_def]) >>
  `eval_operand p.ptr_operand u = SOME w` by
    (Cases_on `p.ptr_operand` >> gvs[eval_operand_def] >> simp[]) >>
  `op_taint tn2 p.ptr_operand = {}` by
    (gvs[ghost_kept_at_def,ptr_vv_ok_def] >> Cases_on `p.ptr_operand` >>
     gvs[op_taint_def] >> metis_tac[]) >>
  `!tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
     storage_read_live H tr (get_storage cx ee tr) w tv` by
    (Cases_on `tr` >> gvs[vv_storage_live_def,slot_loc_def]) >>
  `storage_agree (storage_dead H tr (get_storage cx ee tr)) (get_storage cx ee tr)
     (if tr then contract_transient u else contract_storage u)` by
    (irule storage_copy_initial_agree >> metis_tac[]) >>
  `?tv. evaluate_type (get_tenv cx) ty = SOME tv /\
    read_storage_slot cx tr w tv ee = (INL v,ee) /\
    slots_in_range (get_storage cx ee tr) (w2n w) tv /\
    storage_range_agree (get_storage cx ee tr)
      (if tr then contract_transient u else contract_storage u) w tv` by
    (gvs[storage_holds_def] >>
     conj_tac >- gvs[read_storage_slot_eq,AllCaseEqs()] >>
     irule storage_range_agree_of_live >>
     conj_tac >- fs[storage_range_agree_def] >>
     qexistsl_tac [`H`,`tr`] >> simp[]) >>
  reverse conj_tac >- (Cases_on `tr` >> gvs[vv_storage_live_def,slot_loc_def]) >>
  qexists_tac `Value v` >>
  `storage_holds cx tr ty (Value v) w ee u` by
    gvs[storage_holds_def,read_result_def,return_def] >>
  `!k b. w2n w <= w2n k /\ w2n k < w2n w + type_slot_size tv /\
     (k,b) IN (if tr then tn2.t_trans else tn2.t_stor) ==>
     dead_bytes (if tr then contract_transient u else contract_storage u)
       (w2n w) tv (w2n k) b` by
    (rpt strip_tac >>
     drule_all ctor_saved_slot_taint_dead >> strip_tac >>
     irule ctor_saved_slot_read_dead >> simp[] >>
     qexistsl_tac [`H`,`get_storage cx ee tr`,`tr`] >> simp[]) >>
  Cases_on `tr` >>
  gvs[slot_loc_def,vv_holds_mods_def,vv_holds_def,vv_at_def,vv_store_bound_def,ptr_vv_ok_def,
      read_result_def,return_def,contract_storage_def,contract_transient_def,
      vfmStateTheory.lookup_account_def]
QED

(* Preserve the qualified immutable witness; only the source immutables
   field is used to move its lookup to the suffix endpoint. *)
Theorem ctor_saved_code_holds[local]:
  p.ptr_location = LocCode /\
  vv_holds_mods ce cx ty raw (LocatedValue ty p) mid t /\
  read_result cx raw mid = (INL v,mid) /\ ee.immutables = mid.immutables /\
  eval_operand p.ptr_operand u = eval_operand p.ptr_operand t ==>
  vv_holds_mods ce cx ty (Value v) (LocatedValue ty p) ee u
Proof
  strip_tac >>
  gvs[vv_holds_mods_def,immutable_holds_mods_def,immutable_holds_def,read_result_def,return_def] >>
  qexistsl_tac [`src`,`tops`] >> simp[] >>
  qexistsl_tac [`name`,`off`,`itv`,`iv`,`k`] >> simp[]
QED

Theorem ctor_saved_code_read[local]:
  contract_inv mods exps ctx ce cx /\ expr_sim_inv_mods mods ce cx env ee /\
  ce.ce_is_ctor /\ dead_lo_ok_mods H (DF H) lo ce cx /\
  immutable_frame_mods func ce cx ee u /\ ghost_inv_at_mods (DF H) lo d ce cx ee G tn u /\
  p.ptr_location = LocCode /\ vv_holds_mods ce cx ty (Value v) (LocatedValue ty p) ee u /\
  evaluate_type (get_tenv cx) ty = SOME rt /\ eval_operand p.ptr_operand u = SOME w ==>
  w2n w + type_memory_size rt <= lo /\
  !mem. mem_agree_outside tn.t_mem u.vs_memory mem ==> val_in_memory rt v (w2n w) mem
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  gvs[vv_holds_mods_def,immutable_holds_mods_def,immutable_holds_def,read_result_def,return_def] >>
  Cases_on `ALOOKUP ee.immutables cx.txn.target` >> gvs[] >>
  drule_all_then strip_assume_tac linked_immutable_root_value_mods >>
  drule_all_then strip_assume_tac immutable_region_value_layout_mods >>
  qpat_x_assum `sub_layout _ _ _ _ _` (strip_assume_tac o REWRITE_RULE [sub_layout_def]) >>
  `off + k < dimword (:256)` by decide_tac >>
  simp[arithmeticTheory.LESS_MOD] >> gen_tac >> strip_tac >>
  drule_all_then strip_assume_tac immutable_region_mem_frame_linked_mods >>
  ONCE_REWRITE_TAC[arithmeticTheory.ADD_COMM] >>
  qpat_assum `!b mem. val_in_memory itv iv b mem ==> _` irule >> simp[]
QED

Theorem ctor_saved_rows_cons_mods:
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\ expr_body_pre_mods mods cenv cx env e es /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv cut /\
  ci_mono sa cut /\ ci_mono cut sb /\ u.vs_labels = t.vs_labels /\
  (!K. dead_lo_ok_mods K (DF K) lo cenv cx) /\
  EVERY (source_body_call_supported cx)
    (int_calls_exprs xs) /\
  (~exprs_can_mutate cenv xs ==>
    ee.immutables = mid.immutables /\
    !tr. get_storage cx ee tr = get_storage cx mid tr) /\
  eval_exprs cx xs (mid with gas_obs := obs) = (INL vs,ee with gas_obs := out) /\
  (!K. valid_horizon cx st0 K es.storage_trace ==>
       stmt_state_rel K ctx func cenv cx es s0) /\
  (!K. valid_horizon cx st0 K mid.storage_trace ==>
       valid_horizon cx st0 K es.storage_trace) /\
  (!K. valid_horizon cx st0 K mid.storage_trace ==>
       extcall_positional_post_mods mods T DF lo d ctx func cenv cx env
         xs [e] [sv] sa cut es s0 G0 tn0 K (INL [v]) mid G1 tn1 t) /\
  (!K. valid_horizon cx st0 K ee.storage_trace ==>
       extcall_positional_post_mods mods T DF lo d ctx func cenv cx env
         [] xs svs cut sb mid t G1 tn1 K (INL vs) ee G2 tn2 u) /\
  valid_horizon cx st0 H ee.storage_trace ==>
  extcall_positional_post_mods mods T DF lo d ctx func cenv cx env
    [] (e::xs) (sv::svs) sa sb es s0 G0 tn0 H (INL (v::vs)) ee G2 tn2 u
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 H mid.storage_trace` by
    (qpat_assum `eval_exprs _ _ _ = _` (mp_then Any mp_tac valid_horizon_frame) >>
     simp[cj 6 evaluate_storage_trace_frame]) >>
  `stmt_state_rel H ctx func cenv cx es s0` by simp[] >>
  qpat_x_assum `!K. valid_horizon _ _ _ ee.storage_trace ==> _`
    (qspec_then `H` mp_tac) >> simp[] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS o
              SIMP_RULE (srw_ss()) [extcall_positional_post_mods_def]) >>
  qpat_x_assum `!K. valid_horizon _ _ _ mid.storage_trace ==> extcall_positional_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (qspec_then `H` mp_tac) >> simp[] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS o
              SIMP_RULE (srw_ss()) [extcall_positional_post_mods_def]) >>
  `wb_frame cenv es ee sa s0 u` by
    (irule (horizonTypeLib.at_horizon_named "H" wb_frame_trans) >>
     qpat_assum `stmt_state_rel H ctx func cenv cx es s0` (irule_at Any) >>
     qpat_assum `wb_frame cenv es mid sa s0 t` (irule_at Any) >>
     qpat_assum `wb_frame cenv mid ee cut t u` (irule_at Any) >>
     fs[ci_mono_def]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2` by
    (irule (horizonTypeLib.at_horizon_named "H" ghost_kept_at_wb_trans) >>
     qpat_assum `stmt_state_rel H ctx func cenv cx es s0` (irule_at Any) >>
     qpat_assum `ghost_kept_at lo cenv mid cut G1 tn1 t G2 tn2` (irule_at Any) >>
     qpat_assum `wb_frame cenv es mid sa s0 t` (irule_at Any) >>
     simp[] >> fs[ci_mono_def]) >>
  `!n b sz. local_region cenv mid.scopes t n b sz <=>
             local_region cenv ee.scopes u n b sz` by
    (irule (horizonTypeLib.at_horizon_named "H" wb_frame_local_regions) >>
     qpat_assum `stmt_state_rel H ctx func cenv cx mid t` (irule_at Any) >>
     qpat_assum `wb_frame cenv mid ee cut t u` (irule_at Any) >> simp[]) >>
  `alloca_inv t /\ alloca_inv u` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx mid t`
        (mp_then Any assume_tac stmt_state_rel_local_ptrs_alloca) >>
     qpat_assum `stmt_state_rel H ctx func cenv cx ee u`
        (mp_then Any assume_tac stmt_state_rel_local_ptrs_alloca) >> fs[]) >>
  qpat_x_assum `?si sm ss vv raw copy. compile_expr _ _ _ _ = _ /\ _`
    (qx_choosel_then [`si`,`sm`,`ss`,`vv`,`raw`,`copy`]
      (MAP_EVERY assume_tac o CONJUNCTS)) >>
  `~copy ==> ee.scopes = mid.scopes /\ ee.immutables = mid.immutables /\
            !tr. get_storage cx ee tr = get_storage cx mid tr` by
    (strip_tac >> `~exprs_can_mutate cenv xs` by simp[] >>
     qspecl_then [`cenv`,`cx`,`xs`] mp_tac eval_exprs_no_mutation_scopes >>
     disch_then (drule_all_then mp_tac) >> simp[]) >>
  `(?r. read_result cx r ee = (INL v,ee) /\
        vv_holds_mods cenv cx (lowered_value_type cenv e) r sv ee u /\
        vv_at cenv cx (lowered_value_type cenv e) si ss ee r sv u /\
        ptr_vv_ok cx (lowered_value_type cenv e) r sv ee G2 tn2 u /\
        vv_store_bound cx (lowered_value_type cenv e) (lowered_value_type cenv e)
          ee r sv u) /\
   vv_storage_live H cx sv ee u /\
   (!tag op. sv = StackValue tag op /\ ~is_word_type (lowered_value_type cenv e) ==>
             ptr_buf_ok cenv e op G2 u) /\
   (!tag p. sv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
            ptr_buf_ok cenv e p.ptr_operand G2 u) /\
   (cenv.ce_is_ctor /\ vv_location sv = SOME LocCode ==>
     !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
            eval_operand (vv_operand sv) u = SOME w ==>
            w2n w + type_memory_size rt <= lo /\
            !mem. mem_agree_outside tn2.t_mem u.vs_memory mem ==>
                  val_in_memory rt v (w2n w) mem)` by (suspend "head") >>
  simp[extcall_positional_post_mods_def] >> rpt conj_tac
  >- suspend "row"
  >- (pure_once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
      qpat_assum `cenv.ce_is_ctor /\ vv_location sv = SOME LocCode ==> !rt w. _ ==> _ /\ _`
        (ACCEPT_TAC o cj 1))
  >- suspend "tail"
  >- (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
      qexists_tac `cut` >> fs[ci_mono_def])
  >- suspend "pure"
  >- suspend "vars"
  >> metis_tac[]
QED

Resume ctor_saved_rows_cons_mods[head]:
  `ci_mono sm ss` by
    (qspecl_then [`cenv`,`copy`,`ext_call_arg_value (lowered_value_type cenv e) vv`,`sm`]
       mp_tac ci_mono_compile_snapshot_vv >> simp[]) >>
  `ci_mono ss ss` by simp[ci_mono_refl] >>
  `si.cs_next_var <= ss.cs_next_var /\ si.cs_next_id <= sm.cs_next_id` by
    (drule exprSimUnwrapTheory.compile_expr_extends >> strip_tac >>
     fs[ci_mono_def] >> decide_tac) >>
  `local_ptrs_reserved cenv ss` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `si` >> simp[]) >>
  `!x. vv_operand sv = Var x ==> not_fresh_at ss x` by
    (gen_tac >> strip_tac >>
     irule (SIMP_RULE (srw_ss()) [AND_IMP_INTRO] extcall_saved_operand_not_fresh) >>
     qpat_assum `compile_expr _ _ _ si = _` (irule_at Any) >>
     qpat_assum `compile_snapshot_vv _ _ _ sm = _` (irule_at Any) >> simp[]) >>
  `!x. not_fresh_at ss x ==> not_fresh_at cut x` by
    (gen_tac >> strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `ss` >> simp[]) >>
  `wb_frame cenv mid ee ss t u /\ ghost_kept_at lo cenv mid ss G1 tn1 t G2 tn2 /\
   (!x w. not_fresh_at ss x /\ lookup_var x t = SOME w ==> lookup_var x u = SOME w)` by
     (rpt conj_tac
      >- (qpat_assum `wb_frame cenv mid ee cut t u`
            (strip_assume_tac o REWRITE_RULE [wb_frame_def]) >>
          rewrite_tac[wb_frame_def] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
          >- (rpt strip_tac >> rename1 `lookup_var x u = SOME w` >>
              `not_fresh_at cut x` by simp[] >> simp[]) >>
          qx_genl_tac [`aid`,`off`,`sz`] >> strip_tac >>
          `aid < cut.cs_next_id` by decide_tac >>
          qpat_assum `!aid off sz. FLOOKUP t.vs_allocas aid = SOME (off,sz) /\ _ ==> _`
            (qspecl_then [`aid`,`off`,`sz`] mp_tac) >>
          (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[])
      >- (qpat_assum `ghost_kept_at lo cenv mid cut G1 tn1 t G2 tn2`
            (strip_assume_tac o REWRITE_RULE [ghost_kept_at_def]) >>
          rewrite_tac[ghost_kept_at_def] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
          >- (qx_gen_tac `x` >> strip_tac >> `not_fresh_at cut x` by simp[] >> simp[]) >>
          qx_genl_tac [`aid`,`off`,`sz`,`i`] >> strip_tac >>
          `aid < cut.cs_next_id` by decide_tac >>
          qpat_assum `!aid off sz i. FLOOKUP t.vs_allocas aid = SOME (off,sz) /\ _ ==> _`
            (qspecl_then [`aid`,`off`,`sz`,`i`] mp_tac) >>
          (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]) >>
      rpt strip_tac >> rename1 `lookup_var x u = SOME w` >>
      `not_fresh_at cut x` by simp[] >> simp[]) >>
  namedCases_on `sv` ["tag op", "tag p"]
  >- suspend "stack"
  >> `tag = lowered_value_type cenv e /\ ~is_word_type (lowered_value_type cenv e)` by
    (qpat_assum `(?tag' op0. LocatedValue tag p = StackValue tag' op0) \/ _`
       mp_tac >> simp[NoAsms] >> strip_tac >> gvs[]) >>
  Cases_on `p.ptr_location = LocMemory`
  >- (Cases_on `copy` >- suspend "copy" >> suspend "retain_memory") >>
  `~copy` by
    (Cases_on `copy` >> fs[vv_location_def]) >>
  Cases_on `?tr. p.ptr_location = slot_loc tr`
  >- suspend "slot"
  >> Cases_on `p.ptr_location = LocCode`
  >- suspend "code"
  >> `p.ptr_location = LocCalldata` by
       (Cases_on `p.ptr_location` >> fs[] >>
        qpat_x_assum `!tr. _` (fn th => mp_tac th >> POP_ASSUM_LIST (K ALL_TAC)) >>
        metis_tac[slot_loc_def]) >>
  fs[vv_holds_mods_def,vv_holds_def]
QED
Resume ctor_saved_rows_cons_mods[stack]:
  `~is_word_type (lowered_value_type cenv e) ==> ee.scopes = mid.scopes` by
    (strip_tac >> `~copy` by (Cases_on `copy` >> fs[vv_location_def]) >> simp[]) >>
  qabbrev_tac `ty = lowered_value_type cenv e` >>
  `expr_val_rel cx ty v op t /\ expr_val_at cenv cx ty si ss mid v op t /\
   ptr_val_ok cx ty v op G1 tn1 t` by gvs[vv_holds_mods_def,vv_holds_def,vv_at_def,ptr_vv_ok_def] >>
  `?w. eval_operand op t = SOME w` by fs[expr_val_rel_def] >>
  `!x. op = Var x ==> not_fresh_at ss x` by fs[vv_operand_def] >>
  drule_all ctor_borrowed_operand_frame >> strip_tac >>
  `expr_val_rel cx ty v op u` by
    (Cases_on `is_word_type ty` >- gvs[expr_val_rel_def] >>
     Cases_on `evaluate_type (get_tenv cx) ty` >- simp[expr_val_rel_def] >>
     irule expr_val_rel_footprint_agree >> simp[] >> qexists_tac `t` >> simp[] >>
     qpat_assum `expr_val_at _ _ _ _ ss mid _ _ t`
       (mp_tac o REWRITE_RULE [expr_val_at_def]) >> simp[]) >>
  simp[vv_location_def,vv_storage_live_def] >> qexists_tac `Value v` >>
  simp[vv_holds_mods_def,vv_holds_def,vv_at_def,ptr_vv_ok_def,read_result_def,return_def] >>
  irule ctor_saved_store_bound >> simp[vv_operand_def] >>
  qexistsl_tac [`mid`,`raw`,`t`] >> simp[]
QED
Resume ctor_saved_rows_cons_mods[copy]:
  qpat_x_assum `tag = lowered_value_type cenv e` SUBST_ALL_TAC >>
  qpat_assum `_ ==> ?x w tv. vv_location (LocatedValue _ p) = SOME LocMemory /\ _`
    (mp_tac o REWRITE_RULE [vv_location_def, vv_operand_def]) >>
  (impl_tac >- simp[]) >>
  disch_then (REPEAT_TCL CHOOSE_THEN strip_assume_tac) >>
  rename [`p.ptr_operand = Var x`, `eval_operand p.ptr_operand t = SOME w`,
          `evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv`] >>
  `ptr_val_ok cx (lowered_value_type cenv e) v (Var x) G1 tn1 t /\
   val_in_memory tv v (w2n w) t.vs_memory` by
    gvs[vv_holds_mods_def, vv_holds_def, ptr_vv_ok_def, ptr_val_ok_def] >>
  `lookup_var x t = SOME w` by
    (qpat_assum `p.ptr_operand = Var x` (fn eq =>
       qpat_assum `eval_operand p.ptr_operand t = SOME w`
         (ACCEPT_TAC o REWRITE_RULE [eq, venomStateTheory.eval_operand_def]))) >>
  `w2n w + type_memory_size tv <= t.vs_alloca_next` by
    (irule alloca_site_registered_below >> simp[] >> qexists_tac `sm.cs_next_id` >> simp[]) >>
  `ptr_buf_ok cenv e (Var x) G1 t` by fs[] >>
  `vv_type (ext_call_arg_value (lowered_value_type cenv e) vv) = lowered_value_type cenv e` by
    (drule_then (mp_tac o GSYM) ctor_snapshot_type >> simp[vv_type_def]) >>
  simp[vv_storage_live_def, vv_location_def] >>
  `read_result cx (Value v) ee = (INL v,ee) /\
   vv_holds cenv cx (lowered_value_type cenv e) (Value v)
     (LocatedValue (lowered_value_type cenv e) p) ee u /\
   vv_at cenv cx (lowered_value_type cenv e) si ss ee (Value v)
     (LocatedValue (lowered_value_type cenv e) p) u /\
   ptr_vv_ok cx (lowered_value_type cenv e) (Value v)
     (LocatedValue (lowered_value_type cenv e) p) ee G2 tn2 u /\
   vv_store_bound cx (lowered_value_type cenv e) (lowered_value_type cenv e)
     ee (Value v) (LocatedValue (lowered_value_type cenv e) p) u /\
   ptr_buf_ok cenv e (Var x) G2 u` by
    (irule extcall_request_materialized_endpoint >>
     qpat_assum `compile_snapshot_vv cenv T _ sm = _` (irule_at Any) >>
     qpat_assum `wb_frame cenv mid ee ss t u` (irule_at Any) >>
     qpat_assum `ghost_kept_at lo cenv mid ss G1 tn1 t G2 tn2` (irule_at Any) >>
     qpat_assum `FLOOKUP t.vs_allocas sm.cs_next_id = SOME (w2n w,type_memory_size tv)`
       (irule_at Any) >>
     simp[vv_operand_def, exprSimPropsTheory.val_footprint_le, regions_disjoint_def] >>
     rpt strip_tac >>
     `local_region cenv mid.scopes t n b len` by
       (qpat_assum `!n b sz. local_region cenv mid.scopes t n b sz <=> _`
          (fn th => pure_once_rewrite_tac[th]) >> first_assum ACCEPT_TAC) >>
     qpat_assum `!n b sz. local_region cenv mid.scopes t n b sz ==> _`
       (drule_then mp_tac o REWRITE_RULE [regions_disjoint_def]) >> simp[]) >>
  simp[] >> qexists_tac `Value v` >> simp[vv_holds_mods_def]
QED
Resume ctor_saved_rows_cons_mods[retain_memory]:
  qpat_x_assum `tag = lowered_value_type cenv e` SUBST_ALL_TAC >>
  qabbrev_tac `ty = lowered_value_type cenv e` >>
  `expr_val_at cenv cx ty si ss mid v p.ptr_operand t` by
    (drule_all vv_at_memory_val_at >> simp[]) >>
  `?w. eval_operand p.ptr_operand t = SOME w /\
       !tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
            val_in_memory tv v (w2n w) t.vs_memory` by gvs[vv_holds_mods_def,vv_holds_def] >>
  `ptr_val_ok cx ty v p.ptr_operand G1 tn1 t` by
    (qpat_assum `ptr_vv_ok _ _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [ptr_vv_ok_def]) >>
     simp[ptr_val_ok_def]) >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at ss x` by fs[vv_operand_def] >>
  `~is_word_type ty ==> ee.scopes = mid.scopes` by simp[] >>
  drule_all ctor_borrowed_operand_frame >> strip_tac >>
  simp[vv_location_def,vv_storage_live_def] >> qexists_tac `Value v` >> simp[read_result_def,return_def] >> rpt conj_tac
  >- (simp[vv_holds_mods_def,vv_holds_def,read_result_def,return_def] >> rpt strip_tac >>
      irule val_in_memory_footprint_agree >> simp[] >> conj_tac
      >- (qpat_assum `expr_val_at _ _ _ _ ss mid _ _ t`
            (mp_tac o REWRITE_RULE [expr_val_at_def]) >> simp[]) >>
      qexists_tac `t.vs_memory` >> simp[])
  >- (simp[vv_at_def,read_result_def,return_def,local_place_at_def] >> rpt strip_tac >>
      qpat_assum `expr_val_at _ _ _ _ ss ee _ _ u` (mp_tac o REWRITE_RULE [expr_val_at_def]) >>
      disch_then (qspec_then `tvt` mp_tac) >> simp[])
  >- fs[ptr_val_ok_def,ptr_vv_ok_def,read_result_def,return_def] >>
  irule ctor_saved_store_bound >> simp[vv_operand_def] >>
  qexistsl_tac [`mid`,`raw`,`t`] >> simp[]
QED
Resume ctor_saved_rows_cons_mods[slot]:
  qpat_x_assum `tag = lowered_value_type cenv e` SUBST_ALL_TAC >>
  qpat_x_assum `?tr. p.ptr_location = slot_loc tr` (qx_choose_then `tr` assume_tac) >>
  `slot_loc tr <> LocCode /\ slot_loc tr <> LocMemory` by
    (Cases_on `tr` >> simp[slot_loc_def]) >>
  `dead_lo_ok_mods H (DF H) lo cenv cx` by simp[] >>
  simp[vv_location_def, Excl "vv_storage_live_def"] >>
  irule ctor_saved_slot_endpoint >>
  qpat_assum `stmt_state_rel H ctx func cenv cx ee u` (irule_at Any) >>
  qpat_assum `ghost_inv_at_mods (DF H) lo d cenv cx ee G2 tn2 u` (irule_at Any) >>
  qpat_assum `ghost_kept_at lo cenv mid ss G1 tn1 t G2 tn2` (irule_at Any) >>
  qpat_assum `p.ptr_location = slot_loc tr` (irule_at Any) >>
  qpat_assum `read_result cx raw mid = (INL v,mid)` (irule_at Any) >>
  simp[vv_operand_def, Excl "vv_storage_live_def"]
QED
Resume ctor_saved_rows_cons_mods[code]:
  qpat_x_assum `tag = lowered_value_type cenv e` SUBST_ALL_TAC >>
  qabbrev_tac `ty = lowered_value_type cenv e` >>
  `?w. eval_operand p.ptr_operand t = SOME w` by fs[vv_holds_mods_def] >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at ss x` by fs[vv_operand_def] >>
  `eval_operand p.ptr_operand u = eval_operand p.ptr_operand t` by
    (Cases_on `p.ptr_operand` >> gvs[eval_operand_def] >> simp[]) >>
  `op_taint tn2 p.ptr_operand = {} /\ op_prov G2 p.ptr_operand = NONE` by
    (qpat_assum `ptr_vv_ok _ _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [ptr_vv_ok_def]) >>
     qpat_assum `ghost_kept_at lo cenv mid ss G1 tn1 t G2 tn2`
       (strip_assume_tac o REWRITE_RULE [ghost_kept_at_def]) >>
     Cases_on `p.ptr_operand` >> gvs[op_taint_def,op_prov_def] >> simp[]) >>
  `ee.immutables = mid.immutables` by simp[] >>
  drule_all_then assume_tac ctor_saved_code_holds >>
  simp[vv_location_def,vv_storage_live_def,vv_operand_def] >> conj_tac
  >- (qexists_tac `Value v` >>
      simp[read_result_def,return_def,vv_at_def,ptr_vv_ok_def,vv_store_bound_nonmem]) >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  `dead_lo_ok_mods H (DF H) lo cenv cx` by simp[] >>
  `eval_operand p.ptr_operand u = SOME w` by simp[] >>
  drule_all_then strip_assume_tac ctor_saved_code_read >> first_assum ACCEPT_TAC
QED

Resume ctor_saved_rows_cons_mods[row]:
  qexistsl_tac [`si`,`sm`,`ss`,`vv`,`r`,`copy`] >> simp[] >>
  `sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id /\
   ss.cs_next_var <= sb.cs_next_var /\ ss.cs_next_id <= sb.cs_next_id` by
     (fs[ci_mono_def] >> decide_tac) >>
  simp[expr_can_mutate_def] >> strip_tac >>
  qpat_assum `copy /\ _ ==> ?p w tv. _` mp_tac >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choosel_then [`x`,`w`,`tv`] strip_assume_tac) >>
  qexistsl_tac [`x`,`w`,`tv`] >> simp[] >> rpt strip_tac
  >- (`lookup_var x t = SOME w` by
        ((qpat_assum `eval_operand (vv_operand sv) t = SOME w` mp_tac >>
         simp[eval_operand_def] >> (gvs[eval_operand_def]))) >>
      `not_fresh_at cut x` by
        (qpat_assum `!x. vv_operand sv = Var x ==> _`
           (qspec_then `x` mp_tac) >> simp[]) >>
      simp[eval_operand_def])
  >> `local_region cenv mid.scopes t n b sz` by
       (qpat_assum `!n b sz. local_region cenv mid.scopes t n b sz <=> _`
         (fn th => pure_once_rewrite_tac[th]) >> first_assum ACCEPT_TAC) >>
  qpat_assum `!n b sz. local_region cenv mid.scopes t n b sz ==> _`
    (drule_then ACCEPT_TAC)
QED

Resume ctor_saved_rows_cons_mods[tail]:
  irule LIST_REL_mono >>
  qpat_assum `LIST_REL _ (ZIP (xs,svs)) vs` (irule_at Any) >>
  `!a. cut.cs_next_var <= a.cs_next_var /\ cut.cs_next_id <= a.cs_next_id ==>
       sa.cs_next_var <= a.cs_next_var /\ sa.cs_next_id <= a.cs_next_id` by
    (fs[ci_mono_def] >> rpt strip_tac >> decide_tac) >>
  pop_assum (fn bounds => POP_ASSUM_LIST (K ALL_TAC) >> assume_tac bounds) >>
  Cases >> simp[] >> rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2
    (REPEAT_TCL CHOOSE_THEN (MAP_EVERY assume_tac o CONJUNCTS))
    (K ALL_TAC)) >>
  qexistsl_tac [`si`,`sm`,`ss`,`vv`,`raw`,`copy`] >> simp[]
QED

Resume ctor_saved_rows_cons_mods[pure]:
  strip_tac >> irule pure_frame_trans >> simp[] >>
  qexistsl_tac [`mid`,`cut`,`t`] >> fs[ci_mono_def] >> simp[EQ_SYM_EQ]
QED

Resume ctor_saved_rows_cons_mods[vars]:
  rpt strip_tac >>
  rename1 `lookup_var x u = SOME w` >>
  `not_fresh_at cut x` by
    (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> fs[ci_mono_def]) >>
  `lookup_var x t = SOME w` by simp[] >> simp[]
QED
Finalise ctor_saved_rows_cons_mods

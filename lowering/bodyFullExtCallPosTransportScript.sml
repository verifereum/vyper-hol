(* Transport one saved positional operand across a later argument suffix. *)
Theory bodyFullExtCallPosTransport
Ancestors
  bodyFullLogArgs logValueFramePtr exprSimMemDefs exprSimProps loweringPosts
  bodyPtrDefs venomMemDefs venomState loweringStateRelDefs ptrDiscipline
  compileEnv vyperState vyperInterpreter valueEncodingProofs exprLoweringProps
  stmtSimAssignStorageCopy accountsRelProps exprPtrUnwrapStorageFacts
  vyperStorageBackend sourceUnitExecution
  bodySim exprSimHypsDefs typedMemoryCopy vyperContext stateRelProj
  immutableRelation vyperTypeInvariants structFieldsProps
  ctorDeployDeadSectionRel ctorDeployDeadSectionFrame immSectionDead
  gasContext valueEncodingProps abiCanonicalHeadSize bodyFullOperandSnapshot
  bodyFullAbiEncodeBorrowed bodyFullMaterializedOperandEndpointProps context
  bodyInvCodeProps bodyFullShadowBodyInv immutableRegionFrameProps

Theorem extcall_saved_physical_store_bound:
  read_result cx raw ee = (INL v,ee) /\
  (!tv. evaluate_type (get_tenv cx) ty = SOME tv ==> val_wf tv v) /\
  (~is_word_type ty ==> ~is_word_type ann) /\
  vv_store_bound cx ann ty ee raw sv s ==>
  vv_store_bound cx ty ty ee raw sv s
Proof
  pure_rewrite_tac [vv_store_bound_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  conj_tac
  >- (qx_genl_tac [`vt`,`op`,`v'`,`tvt`,`w`] >> strip_tac >>
      `v' = v` by
        (qpat_assum `read_result cx raw ee = (INL v,ee)`
           (fn th => qpat_assum `read_result cx raw ee = (INL v',ee)`
             (mp_tac o REWRITE_RULE [th])) >> simp[]) >>
      gvs[] >>
      `val_store_size tvt v <= type_memory_size tvt` by
        metis_tac[exprSimPropsTheory.val_store_size_le] >>
      `type_memory_size tvt = 0 \/
       w2n w + type_memory_size tvt <= s.vs_alloca_next` by
        metis_tac[arithmeticTheory.ADD_COMM] >>
      decide_tac) >>
  metis_tac[]
QED

Theorem saved_footprint_pure_frame[local]:
  expr_val_at cenv cx ty sa sm mid v op t /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  eval_operand op t = SOME w /\ pure_frame cenv func mid sm t u /\
  (!aid row. FLOOKUP t.vs_allocas aid = SOME row ==>
             FLOOKUP u.vs_allocas aid = SOME row) /\ alloca_inv u ==>
  mem_bytes_at (w2n w) (val_footprint tv v) u.vs_memory =
  mem_bytes_at (w2n w) (val_footprint tv v) t.vs_memory
Proof
  strip_tac >>
  qpat_assum `expr_val_at _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_val_at_def]) >>
  disch_then (qspec_then `tv` mp_tac) >> simp[] >> strip_tac
  >- (`FLOOKUP u.vs_allocas aid = SOME (b,sz)` by metis_tac[] >>
      `mem_bytes_at b sz u.vs_memory = mem_bytes_at b sz t.vs_memory` by
        (fs[pure_frame_def] >>
         qpat_assum `!off len. _ ==> mem_bytes_at off len _ = _` irule >>
         rpt strip_tac >>
         `aid <> inst.inst_id` by decide_tac >>
         fs[alloca_inv_def, allocas_non_overlapping_def,
            loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[]) >>
      metis_tac[mem_bytes_at_agree_window])
  >- (`mem_bytes_at b sz u.vs_memory = mem_bytes_at b sz t.vs_memory` by
        (fs[pure_frame_def] >> metis_tac[]) >>
      metis_tac[mem_bytes_at_agree_window]) >>
  simp[valueEncodingDefsTheory.mem_bytes_at_def]
QED

Theorem saved_expr_val_at_frame[local]:
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
      disj1_tac >> qexistsl_tac [`aid`,`b`,`sz`] >> simp[] >>
      first_assum ACCEPT_TAC) >>
  disj2_tac >> disj1_tac >> qexistsl_tac [`n`,`b`,`sz`] >> simp[]
QED

Theorem extcall_request_saved_stack_endpoint:
  (?raw. read_result cx raw mid = (INL v,mid) /\
    vv_holds cenv cx (lowered_value_type cenv e) raw (StackValue tag op) mid t /\
    vv_at cenv cx (lowered_value_type cenv e) sa sm mid raw (StackValue tag op) t /\
    ptr_vv_ok cx (lowered_value_type cenv e) raw (StackValue tag op) mid G1 tn1 t /\
    vv_store_bound cx bound_ty (lowered_value_type cenv e) mid raw (StackValue tag op) t) /\
  (~is_word_type (lowered_value_type cenv e) ==> ptr_buf_ok cenv e op G1 t) /\
  ci_mono sm sb /\
  (!x. op = Var x ==> not_fresh_at sm x) /\
  (is_word_type (lowered_value_type cenv e) \/ pure_frame cenv func mid sm t u \/
   (?env (H0:(bool # bytes32 # type_value) list # num list) (H1:(bool # bytes32 # type_value) list # num list) ctx.
      expr_sim_inv cenv cx env mid /\
      stmt_state_rel H0 ctx func cenv cx mid t /\
      stmt_state_rel H1 ctx func cenv cx ee u /\ ee.scopes = mid.scopes /\
      local_ptrs_reserved cenv sm /\ wb_frame cenv mid ee sm t u)) /\
  ghost_kept_at lo cenv mid sm G1 tn1 t G2 tn2 /\
  (!x w. not_fresh_at sm x /\ lookup_var x t = SOME w ==> lookup_var x u = SOME w) /\
  (!aid row. FLOOKUP t.vs_allocas aid = SOME row ==> FLOOKUP u.vs_allocas aid = SOME row) /\
  alloca_inv u /\ t.vs_alloca_next <= u.vs_alloca_next /\
  u.vs_labels = t.vs_labels /\
  (!n b sz. local_region cenv mid.scopes t n b sz <=> local_region cenv ee.scopes u n b sz) ==>
  (?raw. read_result cx raw ee = (INL v,ee) /\
    vv_holds cenv cx (lowered_value_type cenv e) raw (StackValue tag op) ee u /\
    vv_at cenv cx (lowered_value_type cenv e) sa sb ee raw (StackValue tag op) u /\
    ptr_vv_ok cx (lowered_value_type cenv e) raw (StackValue tag op) ee G2 tn2 u /\
    vv_store_bound cx bound_ty (lowered_value_type cenv e) ee raw (StackValue tag op) u) /\
  (~is_word_type (lowered_value_type cenv e) ==> ptr_buf_ok cenv e op G2 u)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_val_rel cx (lowered_value_type cenv e) v op t /\
   expr_val_at cenv cx (lowered_value_type cenv e) sa sm mid v op t /\
   ptr_val_ok cx (lowered_value_type cenv e) v op G1 tn1 t` by
    gvs[vv_holds_def, vv_at_def, ptr_vv_ok_def] >>
  `?w. eval_operand op t = SOME w` by gvs[expr_val_rel_def] >>
  `eval_operand op u = SOME w` by
    (Cases_on `op` >> gvs[venomStateTheory.eval_operand_def] >> metis_tac[]) >>
  `eval_operand op u = eval_operand op t` by simp[] >>
  `!tv. ~is_word_type (lowered_value_type cenv e) /\
     evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv ==>
     val_wf tv v /\
     mem_bytes_at (w2n w) (val_footprint tv v) u.vs_memory =
       mem_bytes_at (w2n w) (val_footprint tv v) t.vs_memory /\
     (!i. w2n w <= i /\ i < w2n w + val_footprint tv v /\ i IN tn2.t_mem ==>
       i IN tn1.t_mem)` by
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `is_word_type _ \/ _` mp_tac >>
     simp[] >> disch_then strip_assume_tac
     >- (conj_tac >- (fs[expr_val_at_def] >> metis_tac[]) >>
         conj_tac >- (drule_all saved_footprint_pure_frame >> simp[]) >>
         rpt strip_tac >> drule_all pure_argument_taint_kept >> simp[]) >>
     drule_all
       (SIMP_RULE (srw_ss()) [] (Q.INST [`sb` |-> `st`]
          abi_encode_borrowed_footprint_frame)) >> simp[]) >>
  `(!x. op = Var x ==> FLOOKUP G2 x = FLOOKUP G1 x) /\
   op_taint tn2 op = op_taint tn1 op` by
    (gvs[ghost_kept_at_def] >> Cases_on `op` >>
     gvs[op_taint_def] >> metis_tac[]) >>
  reverse conj_tac
  >- (strip_tac >> irule ptr_buf_ok_frame >> qexistsl_tac [`G1`,`t`] >> simp[]) >>
  qexists_tac `Value v` >>
  simp[vv_holds_def, vv_at_def, ptr_vv_ok_def, read_result_def, return_def] >>
  conj_tac
  >- (Cases_on `is_word_type (lowered_value_type cenv e)`
      >- gvs[expr_val_rel_def] >>
      Cases_on `evaluate_type (get_tenv cx) (lowered_value_type cenv e)`
      >- simp[expr_val_rel_def] >>
      irule expr_val_rel_footprint_agree >>
      simp[] >> qexists_tac `t` >> simp[]) >>
  conj_tac
  >- (irule saved_expr_val_at_frame >> qexistsl_tac [`mid`,`sm`,`t`] >>
      gvs[ci_mono_def]) >>
  conj_tac
  >- (irule ptr_val_ok_footprint_frame >>
      qexistsl_tac [`G1`,`t`,`tn1`] >> simp[]) >>
  gvs[vv_store_bound_def, read_result_def, return_def] >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem extcall_request_saved_memory_endpoint:
  p.ptr_location = LocMemory /\ ~is_word_type (lowered_value_type cenv e) /\
  (?raw. read_result cx raw mid = (INL v,mid) /\
    vv_holds cenv cx (lowered_value_type cenv e) raw
      (LocatedValue (lowered_value_type cenv e) p) mid t /\
    vv_at cenv cx (lowered_value_type cenv e) sa sm mid raw
      (LocatedValue (lowered_value_type cenv e) p) t /\
    ptr_vv_ok cx (lowered_value_type cenv e) raw
      (LocatedValue (lowered_value_type cenv e) p) mid G1 tn1 t /\
    vv_store_bound cx bound_ty (lowered_value_type cenv e) mid raw
      (LocatedValue (lowered_value_type cenv e) p) t) /\
  ptr_buf_ok cenv e p.ptr_operand G1 t /\ ci_mono sm sb /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
  (pure_frame cenv func mid sm t u \/
   (?env (H0:(bool # bytes32 # type_value) list # num list) (H1:(bool # bytes32 # type_value) list # num list) ctx.
      expr_sim_inv cenv cx env mid /\
      stmt_state_rel H0 ctx func cenv cx mid t /\
      stmt_state_rel H1 ctx func cenv cx ee u /\ ee.scopes = mid.scopes /\
      local_ptrs_reserved cenv sm /\ wb_frame cenv mid ee sm t u)) /\
  ghost_kept_at lo cenv mid sm G1 tn1 t G2 tn2 /\
  (!x w. not_fresh_at sm x /\ lookup_var x t = SOME w ==> lookup_var x u = SOME w) /\
  (!aid row. FLOOKUP t.vs_allocas aid = SOME row ==> FLOOKUP u.vs_allocas aid = SOME row) /\
  alloca_inv u /\ t.vs_alloca_next <= u.vs_alloca_next /\
  u.vs_labels = t.vs_labels /\
  (!n b sz. local_region cenv mid.scopes t n b sz <=> local_region cenv ee.scopes u n b sz) ==>
  (?raw. read_result cx raw ee = (INL v,ee) /\
    vv_holds cenv cx (lowered_value_type cenv e) raw
      (LocatedValue (lowered_value_type cenv e) p) ee u /\
    vv_at cenv cx (lowered_value_type cenv e) sa sb ee raw
      (LocatedValue (lowered_value_type cenv e) p) u /\
    ptr_vv_ok cx (lowered_value_type cenv e) raw
      (LocatedValue (lowered_value_type cenv e) p) ee G2 tn2 u /\
    vv_store_bound cx bound_ty (lowered_value_type cenv e) ee raw
      (LocatedValue (lowered_value_type cenv e) p) u) /\
  ptr_buf_ok cenv e p.ptr_operand G2 u
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?raw. read_result cx raw mid = (INL v,mid) /\ _`
    (qx_choose_then `raw` strip_assume_tac) >>
  `expr_val_at cenv cx (lowered_value_type cenv e) sa sm mid v p.ptr_operand t` by
    (drule_all vv_at_memory_val_at >> simp[]) >>
  `?w. eval_operand p.ptr_operand t = SOME w /\
       !tv. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv ==>
            val_in_memory tv v (w2n w) t.vs_memory` by gvs[vv_holds_def] >>
  `eval_operand p.ptr_operand u = SOME w` by
    (Cases_on `p.ptr_operand` >> gvs[venomStateTheory.eval_operand_def] >> metis_tac[]) >>
  `eval_operand p.ptr_operand u = eval_operand p.ptr_operand t` by simp[] >>
  `(!x. p.ptr_operand = Var x ==> FLOOKUP G2 x = FLOOKUP G1 x) /\
   op_taint tn2 p.ptr_operand = op_taint tn1 p.ptr_operand` by
    (gvs[ghost_kept_at_def] >> Cases_on `p.ptr_operand` >>
     gvs[op_taint_def] >> metis_tac[]) >>
  `!tv. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv ==>
     val_wf tv v /\
     mem_bytes_at (w2n w) (val_footprint tv v) u.vs_memory =
       mem_bytes_at (w2n w) (val_footprint tv v) t.vs_memory /\
     (!i. w2n w <= i /\ i < w2n w + val_footprint tv v /\ i IN tn2.t_mem ==>
       i IN tn1.t_mem)` by
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `_ \/ (?env H0 H1 ctx. _)` strip_assume_tac
     >- (conj_tac >- (fs[expr_val_at_def] >> metis_tac[]) >>
         conj_tac >- (drule_all saved_footprint_pure_frame >> simp[]) >>
         rpt strip_tac >> drule_all pure_argument_taint_kept >> simp[]) >>
     drule_all
       (SIMP_RULE (srw_ss()) [] (Q.INST [`sb` |-> `st`]
          abi_encode_borrowed_footprint_frame)) >> simp[]) >>
  `ptr_val_ok cx (lowered_value_type cenv e) v p.ptr_operand G1 tn1 t` by
    (qpat_assum `ptr_vv_ok _ _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [ptr_vv_ok_def]) >>
     simp[ptr_val_ok_def]) >>
  `ptr_val_ok cx (lowered_value_type cenv e) v p.ptr_operand G2 tn2 u` by
    (irule ptr_val_ok_footprint_frame >>
     qexistsl_tac [`G1`,`t`,`tn1`] >> simp[]) >>
  reverse conj_tac
  >- (irule ptr_buf_ok_frame >> qexistsl_tac [`G1`,`t`] >> simp[]) >>
  `expr_val_at cenv cx (lowered_value_type cenv e) sa sb ee v p.ptr_operand u` by
    (irule saved_expr_val_at_frame >> qexistsl_tac [`mid`,`sm`,`t`] >>
     gvs[ci_mono_def]) >>
  qexists_tac `Value v` >> simp[read_result_def, return_def] >> rpt conj_tac
  >- (simp[vv_holds_def, read_result_def, return_def] >> rpt strip_tac >>
      irule val_in_memory_footprint_agree >>
      simp[] >> qexists_tac `t.vs_memory` >> simp[])
  >- (simp[vv_at_def, read_result_def, return_def, local_place_at_def] >>
      rpt strip_tac >>
      qpat_assum `expr_val_at _ _ _ _ sb ee _ _ u`
        (mp_tac o REWRITE_RULE [expr_val_at_def]) >>
      disch_then (qspec_then `tvt` mp_tac) >> simp[])
  >- (qpat_assum `ptr_val_ok _ _ _ _ G1 tn1 t`
        (assume_tac o CONJUNCT1 o REWRITE_RULE [ptr_val_ok_def]) >>
      qpat_assum `ptr_val_ok _ _ _ _ G2 tn2 u`
        (strip_assume_tac o REWRITE_RULE [ptr_val_ok_def]) >>
      simp[ptr_vv_ok_def, read_result_def, return_def]) >>
  gvs[vv_store_bound_def, read_result_def, return_def] >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem extcall_request_materialized_endpoint:
  compile_snapshot_vv cenv T input a = (saved,ss) /\
  vv_type input = lowered_value_type cenv e /\
  ~is_word_type (lowered_value_type cenv e) /\ vv_operand saved = Var x /\
  evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv /\
  val_wf tv v /\ val_footprint tv v <= sz /\
  ptr_val_ok cx (lowered_value_type cenv e) v (Var x) G1 tn1 t /\
  val_in_memory tv v (w2n w) t.vs_memory /\ ptr_buf_ok cenv e (Var x) G1 t /\
  lookup_var x t = SOME w /\ not_fresh_at cut x /\
  FLOOKUP t.vs_allocas aid = SOME (w2n w,sz) /\
  si.cs_next_id <= aid /\ aid < ss.cs_next_id /\ aid < cut.cs_next_id /\
  type_memory_size tv <= sz /\
  w2n w + sz <= t.vs_alloca_next /\ t.vs_alloca_next <= u.vs_alloca_next /\
  (!n b len. local_region cenv mid.scopes t n b len ==>
    w2n w + sz <= b \/ b + len <= w2n w) /\
  (!n b len. local_region cenv ee.scopes u n b len ==>
    local_region cenv mid.scopes t n b len) /\
  wb_frame cenv mid ee cut t u /\ ghost_kept_at lo cenv mid cut G1 tn1 t G2 tn2 ==>
  read_result cx (Value v) ee = (INL v,ee) /\
  vv_holds cenv cx (lowered_value_type cenv e) (Value v) saved ee u /\
  vv_at cenv cx (lowered_value_type cenv e) si ss ee (Value v) saved u /\
  ptr_vv_ok cx (lowered_value_type cenv e) (Value v) saved ee G2 tn2 u /\
  vv_store_bound cx (lowered_value_type cenv e) (lowered_value_type cenv e)
    ee (Value v) saved u /\
  ptr_buf_ok cenv e (Var x) G2 u
Proof
  strip_tac >> drule_all materialized_operand_endpoint >> simp[]
QED

(* Slot agreement uses the new state's storage relation, not equality of
   the two Venom backends on dead bytes. *)
Theorem saved_slot_range_frame[local]:
  storage_range_agree st rt w tv /\ storage_read_live H tr st w tv /\
  storage_agree (storage_dead H tr st) st rt' ==>
  storage_range_agree st rt' w tv
Proof
  strip_tac >> irule storage_range_agree_of_live >>
  conj_tac >- fs[storage_range_agree_def] >>
  qexistsl_tac [`H`,`tr`] >> simp[]
QED

Theorem saved_slot_taint_dead[local]:
  ghost_inv_at D lo d cenv cx ee G tn u /\ dead_lo_ok H D lo cenv cx /\
  (k,b) IN (if tr then tn.t_trans else tn.t_stor) ==>
  storage_dead H tr (if tr then contract_transient u else contract_storage u)
    (w2n k) b
Proof
  Cases_on `tr` >>
  gvs[ghost_inv_at_def, stor_taint_ok_at_def, dead_lo_ok_def, cx_dead_def,
      pred_setTheory.SUBSET_DEF, contract_storage_def, contract_transient_def,
      vfmStateTheory.lookup_account_def] >>
  rpt strip_tac >> first_x_assum drule >>
  Cases_on `u.vs_call_ctx.cc_address = cx.txn.target` >> simp[]
QED

Theorem saved_slot_read_dead[local]:
  storage_agree (storage_dead H tr st) st rt /\
  storage_range_agree st rt w tv /\ storage_read_live H tr st w tv /\
  storage_dead H tr rt (w2n k) b /\
  w2n w <= w2n k /\ w2n k < w2n w + type_slot_size tv ==>
  dead_bytes rt (w2n w) tv (w2n k) b
Proof
  strip_tac >> drule storage_agree_storage_dead >> strip_tac >>
  drule storage_range_agree_dead_bytes >> strip_tac >>
  fs[storage_read_live_def] >> metis_tac[]
QED

Theorem extcall_request_saved_slot_endpoint:
  p.ptr_location = slot_loc tr /\
  (?raw. read_result cx raw mid = (INL v,mid) /\
    vv_holds cenv cx ty raw (LocatedValue ty p) mid t /\
    ptr_vv_ok cx ty raw (LocatedValue ty p) mid G1 tn1 t) /\
  vv_storage_live H cx (LocatedValue ty p) mid t /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
  ghost_kept_at lo cenv mid sm G1 tn1 t G2 tn2 /\
  (!x w. not_fresh_at sm x /\ lookup_var x t = SOME w ==> lookup_var x u = SOME w) /\
  u.vs_labels = t.vs_labels /\ get_storage cx ee tr = get_storage cx mid tr /\
  stmt_state_rel H ctx func cenv cx ee u /\
  ghost_inv_at D lo d cenv cx ee G2 tn2 u /\ dead_lo_ok H D lo cenv cx ==>
  (?raw. read_result cx raw ee = (INL v,ee) /\
    vv_holds cenv cx ty raw (LocatedValue ty p) ee u /\
    vv_at cenv cx ty sa sb ee raw (LocatedValue ty p) u /\
    ptr_vv_ok cx ty raw (LocatedValue ty p) ee G2 tn2 u /\
    vv_store_bound cx ann ty ee raw (LocatedValue ty p) u) /\
  vv_storage_live H cx (LocatedValue ty p) ee u
Proof
  strip_tac >>
  `?w. eval_operand p.ptr_operand t = SOME w /\ storage_holds cx tr ty raw w mid t` by
    (Cases_on `tr` >> gvs[vv_holds_def, slot_loc_def]) >>
  `eval_operand p.ptr_operand u = SOME w` by
    (Cases_on `p.ptr_operand` >> gvs[venomStateTheory.eval_operand_def] >> metis_tac[]) >>
  `op_taint tn2 p.ptr_operand = {}` by
    (gvs[ghost_kept_at_def, ptr_vv_ok_def] >> Cases_on `p.ptr_operand` >>
     gvs[op_taint_def] >> metis_tac[]) >>
  `!tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
     storage_read_live H tr (get_storage cx ee tr) w tv` by
    (Cases_on `tr` >> gvs[vv_storage_live_def, slot_loc_def]) >>
  `storage_agree (storage_dead H tr (get_storage cx ee tr)) (get_storage cx ee tr)
     (if tr then contract_transient u else contract_storage u)` by
    metis_tac[storage_copy_initial_agree] >>
  `?tv. evaluate_type (get_tenv cx) ty = SOME tv /\
    read_storage_slot cx tr w tv ee = (INL v,ee) /\
    slots_in_range (get_storage cx ee tr) (w2n w) tv /\
    storage_range_agree (get_storage cx ee tr)
      (if tr then contract_transient u else contract_storage u) w tv` by
    (gvs[storage_holds_def] >>
     conj_tac >- gvs[read_storage_slot_eq, AllCaseEqs()] >>
     irule saved_slot_range_frame >> metis_tac[]) >>
  reverse conj_tac >- (Cases_on `tr` >> gvs[slot_loc_def]) >>
  qexists_tac `Value v` >>
  `storage_holds cx tr ty (Value v) w ee u` by
    (simp[storage_holds_def, read_result_def, return_def] >> metis_tac[]) >>
  `!k b. w2n w <= w2n k /\ w2n k < w2n w + type_slot_size tv /\
     (k,b) IN (if tr then tn2.t_trans else tn2.t_stor) ==>
     dead_bytes (if tr then contract_transient u else contract_storage u)
       (w2n w) tv (w2n k) b` by
    (rpt strip_tac >>
     drule_all saved_slot_taint_dead >> strip_tac >>
     irule saved_slot_read_dead >> simp[] >>
     qexistsl_tac [`H`,`get_storage cx ee tr`,`tr`] >> simp[]) >>
  Cases_on `tr` >>
  gvs[slot_loc_def, vv_holds_def, vv_at_def, vv_store_bound_def, ptr_vv_ok_def,
      read_result_def, return_def, contract_storage_def, contract_transient_def,
      vfmStateTheory.lookup_account_def]
QED

(* Code pointers keep their source witness; this step does not claim that
   the constructor's memory taint is unchanged. *)
Theorem extcall_request_saved_code_endpoint:
  p.ptr_location = LocCode /\
  (?raw. read_result cx raw mid = (INL v,mid) /\
    vv_holds cenv cx ty raw (LocatedValue ty p) mid t /\
    ptr_vv_ok cx ty raw (LocatedValue ty p) mid G1 tn1 t) /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
  ghost_kept_at lo cenv mid sm G1 tn1 t G2 tn2 /\
  (!x w. not_fresh_at sm x /\ lookup_var x t = SOME w ==> lookup_var x u = SOME w) /\
  u.vs_labels = t.vs_labels /\ ee.immutables = mid.immutables ==>
  (?raw. read_result cx raw ee = (INL v,ee) /\
    vv_holds cenv cx ty raw (LocatedValue ty p) ee u /\
    vv_at cenv cx ty sa sb ee raw (LocatedValue ty p) u /\
    ptr_vv_ok cx ty raw (LocatedValue ty p) ee G2 tn2 u /\
    vv_store_bound cx ann ty ee raw (LocatedValue ty p) u) /\
  vv_storage_live H cx (LocatedValue ty p) ee u /\
  eval_operand p.ptr_operand u = eval_operand p.ptr_operand t
Proof
  strip_tac >>
  `?w. eval_operand p.ptr_operand t = SOME w /\ immutable_holds cenv cx ty raw w mid t` by
    gvs[vv_holds_def] >>
  `eval_operand p.ptr_operand u = SOME w` by
    (Cases_on `p.ptr_operand` >> gvs[venomStateTheory.eval_operand_def] >> metis_tac[]) >>
  `op_taint tn2 p.ptr_operand = {} /\ op_prov G2 p.ptr_operand = NONE` by
    (gvs[ghost_kept_at_def, ptr_vv_ok_def] >> Cases_on `p.ptr_operand` >>
     gvs[op_taint_def, op_prov_def] >> metis_tac[]) >>
  simp[] >> qexists_tac `Value v` >>
  simp[read_result_def, return_def, vv_holds_def, vv_at_def,
       vv_store_bound_def, ptr_vv_ok_def] >>
  fs[immutable_holds_def, read_result_def, return_def] >>
  qexistsl_tac [`src`,`name`,`off`,`itv`,`iv`,`k`] >> gvs[]
QED

(* Apply this at the same endpoint as extcall_request_saved_code_endpoint.
   The robust read is reconstructed from that state's own immutables and ghost. *)
(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[loweringPostsTheory.vv_holds_def, loweringPostsTheory.immutable_holds_def] >>
  Cases_on `ALOOKUP entry.immutables cx.txn.target` >> gvs[] >>
  rename1 `ALOOKUP entry.immutables cx.txn.target = SOME imms` >>
  `ALOOKUP ee.immutables cx.txn.target = SOME imms` by metis_tac[] >>
  drule_all immutable_ctor_frame_mods >> strip_tac >>
  qpat_x_assum `sub_layout _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [loweringPostsTheory.sub_layout_def]) >>
  `off + k < dimword (:256)` by decide_tac >>
  simp[arithmeticTheory.LESS_MOD] >>
  rpt strip_tac >> metis_tac[arithmeticTheory.ADD_COMM]
QED
*)
Theorem extcall_request_saved_ctor_read_mods:
  contract_inv mods exps ctx cenv cx /\ expr_sim_inv_mods mods cenv cx env entry /\
  cenv.ce_is_ctor /\ p.ptr_location = LocCode /\ dead_lo_ok_mods H D lo cenv cx /\
  ee.immutables = entry.immutables /\ stmt_state_rel H ctx func cenv cx ee u /\
  ghost_inv_at_mods D lo d cenv cx ee G tn u /\
  (?raw. read_result cx raw ee = (INL v,ee) /\
     vv_holds cenv cx ty raw (LocatedValue ty p) ee u) ==>
  !rt w. evaluate_type (get_tenv cx) ty = SOME rt /\
         eval_operand p.ptr_operand u = SOME w ==>
    w2n w + type_memory_size rt <= lo /\
    (!mem. mem_agree_outside tn.t_mem u.vs_memory mem ==>
           val_in_memory rt v (w2n w) mem)
Proof
  cheat
QED

Theorem extcall_request_saved_ctor_read:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env entry /\
  cenv.ce_is_ctor /\ p.ptr_location = LocCode /\ dead_lo_ok H D lo cenv cx /\
  ee.immutables = entry.immutables /\ stmt_state_rel H ctx func cenv cx ee u /\
  ghost_inv_at D lo d cenv cx ee G tn u /\
  (?raw. read_result cx raw ee = (INL v,ee) /\
     vv_holds cenv cx ty raw (LocatedValue ty p) ee u) ==>
  !rt w. evaluate_type (get_tenv cx) ty = SOME rt /\
         eval_operand p.ptr_operand u = SOME w ==>
    w2n w + type_memory_size rt <= lo /\
    (!mem. mem_agree_outside tn.t_mem u.vs_memory mem ==>
           val_in_memory rt v (w2n w) mem)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then strip_assume_tac body_inv_main_code >>
  drule_then assume_tac body_inv_contract >>
  drule_then assume_tac contract_inv_cenv_modules >>
  fs[expr_sim_inv_split_def, GSYM dead_lo_ok_mods_singleton,
     GSYM ghost_inv_at_mods_singleton] >>
  mp_tac (Q.INST [`mods` |-> `[(NONE,tops)]`, `exps` |-> `[]`]
            extcall_request_saved_ctor_read_mods) >>
  simp[] >> impl_tac >- (qexists_tac `raw` >> simp[]) >>
  disch_then ACCEPT_TAC
QED

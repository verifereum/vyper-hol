(* Storage old-value loading from readiness after target evaluation. *)
Theory augAssignPlaceReadyStorage
Ancestors
  augAssignPlaceMemoryTarget augAssignPlaceSourceMemory
  bodyAugAssignOther bodyMemoryDefs exprSimHyps vyperInterpreter exprSimMemDefs
  stmtSimAugAssignPlaceStorage exprSimHypsDefs exprSimProps
  freshWrites loweringPosts stmtSimAugAssignPlace bodySim
  augAssignPlaceLoadContinuation augAssignPlaceStorageContinuation
  augAssignPlaceEndpointMemory

Theorem aug_place_ready_storage_loaded:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env e es /\
  slots_in_range (get_storage cx mid tr) (w2n slot) tv /\
  storage_read_live H tr (get_storage cx mid tr) slot tv /\
  eval_target_place cx bt (es with gas_obs := gs) =
    (INL (StoragePlace tr slot tv),mid) /\
  target_post H ctx func cenv cx es sa sp s0 mid
    (PlaceR (StoragePlace tr slot tv)) (Type ty) r t /\
  is_word_type ty /\
  emit_op (if tr then TLOAD else SLOAD) [FST r] sp = (cur,sl) /\
  fn_has_code sp sl func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sp /\ alloca_history func t /\ ~t.vs_halted /\
  t.vs_current_bb = sp.cs_current_bb /\
  t.vs_inst_idx = LENGTH sp.cs_current_insts /\
  (!z. not_fresh_at sa z ==> not_fresh_at sp z) ==>
  ?old u. read_place cx (StoragePlace tr slot tv) mid = (INL old,mid) /\
    place_type_value cx (StoragePlace tr slot tv) mid = (INL tv,mid) /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv old /\
    gas_marked_path T ctx func t 0 (OK u) /\
    eval_operand cur u = SOME (typed_val_to_w256 tv old) /\
    eval_operand (FST r) u = SOME slot /\
    place_ptr_rel cenv cx u (PlaceR (StoragePlace tr slot tv)) slot
      (SOME (slot_loc tr)) (Type ty) /\
    stmt_state_rel H ctx func cenv cx mid u /\
    ~u.vs_halted /\ u.vs_current_bb = sl.cs_current_bb /\
    u.vs_inst_idx = LENGTH sl.cs_current_insts /\
    local_ptrs_reserved cenv sl /\ alloca_history func u /\
    (!z v. not_fresh_at sa z /\ lookup_var z s0 = SOME v ==>
      lookup_var z u = SOME v) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
      FLOOKUP u.vs_allocas aid = SOME b) /\
    u.vs_alloca_next = t.vs_alloca_next /\ u.vs_memory = t.vs_memory /\
    (!z. not_fresh_at sp z ==> lookup_var z u = lookup_var z t) /\
    (!z. FST r = Var z ==> not_fresh_at sl z) /\
    (?out. cur = Var out /\ not_fresh_at sl out) /\
    u.vs_accounts = t.vs_accounts /\ u.vs_transient = t.vs_transient /\
    u.vs_requests = t.vs_requests /\ u.vs_call_ctx = t.vs_call_ctx
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `evaluate_type (get_tenv cx) ty = SOME tv /\
   stmt_state_rel H ctx func cenv cx mid t /\
   eval_operand (FST r) t = SOME slot /\
   (!x. FST r = Var x ==> not_fresh_at sp x)` by
    gvs[target_post_def, place_ptr_rel_def] >>
  drule_all aug_place_storage_read_ready >> strip_tac >>
  drule_all aug_place_storage_load_ready >> strip_tac >>
  drule_all aug_place_storage_access_path >> strip_tac >>
  qpat_x_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [target_post_def]) >>
  `place_ptr_rel cenv cx u (PlaceR (StoragePlace tr slot tv)) slot
    (SOME (slot_loc tr)) (Type ty)` by fs[place_ptr_rel_def] >>
  qexistsl_tac [`cur'`, `u`] >> simp[] >>
  metis_tac[freshWritesTheory.not_fresh_at_mono]
QED

Theorem aug_place_ready_storage_endpoint:
  body_inv tops ctx cenv cx /\
  ((?b fld. bt = AttributeTarget b fld) \/ (?b k. bt = SubscriptTarget b k)) /\
  type_stmt env ret_ty (AugAssign ty bt bop e) = SOME env' /\
  expr_body_pre cenv cx env e es /\ target_indices_pre cenv cx env bt /\
  (!s p s1 s2 cur s3 s4 ptv s5.
    eval_target_place cx bt s = (INL p,s1) /\ read_place cx p s2 = (INL cur,s3) /\
    place_type_value cx p s4 = (INL ptv,s5) ==> body_expr_mem_ok cx e) /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
       target_post H ctx func cenv cx es sa sp s0 mid
         (PlaceR (StoragePlace tr slot tv)) (Type ty) r t /\
       slots_in_range (get_storage cx mid tr) (w2n slot) tv /\
       storage_read_live H tr (get_storage cx mid tr) slot tv) /\
  (!tail. eval_target_place cx bt
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
    (INL (StoragePlace tr slot tv),mid with gas_obs := tail)) /\
  gas_admissible (eval_stmt cx (AugAssign ty bt bop e)) (stmt_res_ok lctx) es /\
  compile_get_target_ptr compile_expr cenv bt sa = (r,sp) /\
  emit_op (if tr then TLOAD else SLOAD) [FST r] sp = (cur,sl) /\
  lower_value compile_expr cenv ty e sl = (rhs,s2) /\
  compile_binop bop cur rhs ty NONE
    (if bop = Exp then expr_int_literal e else NONE) s2 = (result,s3) /\
  emit_void (if tr then TSTORE else SSTORE) [FST r;result] s3 = ((),sf) /\
  fn_has_code sp sl func /\ fn_has_code sl s2 func /\
  fn_has_code s2 s3 func /\ fn_has_code s3 sf func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sp /\ local_ptrs_reserved cenv s2 /\
  local_ptrs_reserved cenv s3 /\
  (!z. not_fresh_at sa z ==> not_fresh_at sp z) /\
  (!z. not_fresh_at sp z ==> not_fresh_at sl z) /\
  (!z. not_fresh_at sl z ==> not_fresh_at s2 z) /\
  (!z. not_fresh_at s2 z ==> not_fresh_at s3 z) /\
  alloca_history func t /\ ~t.vs_halted /\
  t.vs_current_bb = sp.cs_current_bb /\ t.vs_inst_idx = LENGTH sp.cs_current_insts /\
  s0.vs_alloca_next <= t.vs_alloca_next /\
  alloca_frame cenv es0 sa s0 cenv mid t /\
  (!H res ee v. res = INL () /\
    stmt_post H ctx func cx lctx cenv cenv sa sf es0 s0 res ee v /\
    alloca_history func v /\ s0.vs_alloca_next <= v.vs_alloca_next ==>
    Q H res ee v) ==>
  gas_outcome T (cx_tops cx) (ctx,func) cx st0
    (bind (read_place cx (StoragePlace tr slot tv)) (\old.
      bind (place_type_value cx (StoragePlace tr slot tv)) (\ptv.
      bind (bind (eval_expr cx e) (read_result cx)) (\rhs.
      bind (lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
        ptv bop old rhs)) (write_place cx (StoragePlace tr slot tv)))))) (mid,t) Q
    (\H res ff rr. !tail. stmt_exit (RetQ H) (ff with gas_obs := tail) res rr)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule aug_place_typing >> strip_tac >>
  `is_word_type ty` by metis_tac[exprSimSourceTheory.word_value_type_word] >>
  `type_bits ty MOD 8 = 0` by
    metis_tac[vyperTypeSystemTheory.assignable_type_well_formed,
              stmtSimAugAssignTheory.well_formed_type_bits] >>
  qpat_assum `!tail. eval_target_place _ _ _ = _`
    (assume_tac o SRULE [] o Q.SPEC `mid.gas_obs`) >>
  `?H0. valid_horizon cx st0 H0 mid.storage_trace` by
    (qexists_tac `storage_trace_horizon mid.storage_trace` >>
     qpat_x_assum `storage_trace_domain _ _ _` mp_tac >>
     simp[vyperStorageFootprintTheory.storage_trace_domain_def]) >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _ /\ _ /\ _`
    (qspec_then `H0` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
       target_post H ctx func cenv cx es sa sp s0 mid
         (PlaceR (StoragePlace tr slot tv)) (Type ty) r t` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _ /\ _ /\ _`
       (qspec_then `H` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> strip_tac >> first_assum ACCEPT_TAC) >>
  drule_at (Pat `target_post`) aug_place_ready_storage_loaded >>
  disch_then (drule_at (Pat `eval_target_place`)) >>
  disch_then (drule_at (Pat `emit_op`)) >> simp[] >>
  disch_then (qspec_then `tops` mp_tac) >> simp[] >>
  disch_then (drule_at (Pat `expr_body_pre`)) >> simp[] >> strip_tac >>
  `expr_body_pre cenv cx env e mid` by
    (irule stmtSimAugAssignPlaceMemoryTheory.aug_place_rhs_pre_target_gas_obs >>
     goal_assum (drule_at (Pat `eval_target_place`)) >> simp[]) >>
  `expr_sim_mem ctx func cenv cx ty e mid` by
    (`body_expr_mem_ok cx e` by metis_tac[] >>
     fs[bodyMemoryPredsTheory.body_expr_mem_ok_def] >> metis_tac[]) >>
  `acyclic_struct_metadata cenv.ce_struct_fields` by fs[body_inv_def] >>
  `IS_SOME (evaluate_type (get_tenv cx) (expr_type e))` by
    metis_tac[exprSimHypsTheory.expr_body_pre_type_evaluates] >>
  `~cx.txn.is_static` by fs[exprLoweringPropsTheory.stmt_state_rel_def,
                           loweringStateRelDefsTheory.state_rel_def] >>
  `?offset tv0 path delta. MEM (StorageRoot tr offset tv0) mid.storage_trace /\
     storage_subregion tv0 path delta tv /\ slot = n2w offset + n2w delta` by
    (qpat_assum `eval_target_place cx bt (es with gas_obs := _) = _`
       (mp_tac o MATCH_MP
         vyperFiniteStoragePreservationTheory.eval_target_place_observed_region) >>
     simp[]) >>
  `~block_is_terminated sf` by
    (Cases_on `tr` >> irule stmtSimDeclMemTheory.emit_void_nonterminator_open >>
     goal_assum (drule_at Any) >> simp[venomInstTheory.is_terminator_def]) >>
  `!l. cur <> Label l /\ FST r <> Label l` by
    (drule_all stmtSimAugAssignPlaceTheory.aug_place_target_ptr_not_label >>
     strip_tac >> gvs[]) >>
  `!z. not_fresh_at sa z ==> not_fresh_at sl z` by metis_tac[] >>
  `s0.vs_alloca_next <= u.vs_alloca_next` by simp[] >>
  `sa.cs_next_id <= sl.cs_next_id` by
    (`sa.cs_next_id <= sp.cs_next_id` by
       metis_tac[exprLoweringPropsTheory.ci_mono_compile_get_target_ptr_cfn,
                 exprLoweringPropsTheory.compile_expr_ci_mono,
                 exprLoweringPropsTheory.ci_mono_def, pairTheory.SND] >>
     `sp.cs_next_id <= sl.cs_next_id` by
       metis_tac[exprLoweringPropsTheory.ci_mono_emit_op,
                 exprLoweringPropsTheory.ci_mono_def, pairTheory.SND] >>
     decide_tac) >>
  `stmt_state_rel H0 ctx func cenv cx mid t` by
    (qpat_assum `target_post H0 _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     rewrite_tac[loweringPostsTheory.target_post_def] >>
     disch_then (ACCEPT_TAC o CONJUNCT1)) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
       stmt_state_rel H ctx func cenv cx mid u /\
       storage_well_formed_on cx mid (FST H)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
                       target_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
       (qspec_then `H` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     rewrite_tac[loweringPostsTheory.target_post_def] >> strip_tac >>
     conj_tac
     >- (mp_tac (Q.INST [`es` |-> `mid`, `s` |-> `t`]
           exprLoweringPropsTheory.stmt_state_rel_fields_transport) >>
         impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
         strip_tac >> first_assum ACCEPT_TAC) >>
     first_assum ACCEPT_TAC) >>
  `alloca_frame cenv es0 sa s0 cenv mid u` by
    (qspecl_then [`H0`, `cenv`, `es0`, `sa`, `s0`, `cenv`, `mid`, `t`, `ctx`, `func`,
                  `cx`, `sp`, `mid`, `u`] mp_tac
       augAssignPlaceWordStoreMemoryTheory.alloca_frame_memory_kept >>
     impl_tac >- simp[] >> simp[]) >>
  irule aug_place_reads_suffix >> simp[] >>
  qexists_tac `\H res ee v. res = INL () /\
    stmt_post H ctx func cx lctx cenv cenv sa sf es0 s0 res ee v /\
    alloca_history func v /\ s0.vs_alloca_next <= v.vs_alloca_next` >> simp[] >>
  goal_assum (drule_at (Pat `gas_marked_path`)) >> simp[] >>
  irule aug_place_loaded_storage_suffix >> simp[] >> conj_tac
  >- (goal_assum (drule_at (Pat `lower_value`)) >>
      goal_assum (drule_at (Pat `compile_binop`)) >> simp[] >> metis_tac[]) >>
  goal_assum (drule_at (Pat `type_stmt`)) >>
  goal_assum (drule_at (Pat `eval_target_place`)) >> simp[]
QED

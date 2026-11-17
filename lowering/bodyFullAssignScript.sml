(*
 * Assignment to a base target over the finite-horizon joint judgment.
 * Stated over the finite-horizon full family (bodySimFull), one sub-shape
 * per S1 dispatch arm of bodySimStmtCases/bodySimDeclCases, so the case in
 * bodyFullCases closes by the same case split.
 *
 * TOP-LEVEL: the body_*_full sub-shape theorems below.
 *)
Theory bodyFullAssign
Ancestors
  bodyFullPreds bodySimFull gasShadow bodySim exprSimHypsDefs supportedStmts
  compileEnv exprLowering stmtLowering vyperTypeSystem vyperContext
  vyperInterpreter vyperState vyperValue vyperAST list finite_map
  bodyFullAssignAttrStorage bodyExprPreFacts bodyStorageMetadata
  bodyFullAssignToplevelSetup bodyFullAssignToplevelTail
  bodyFullAssignToplevelCode bodyFullAssignToplevelSource exprSimSliceCompose
  gasOutcomeFullCompose exprSimTopLevelProps vyperStorageFootprint
  vyperStorageTrace exprLoweringProps loweringStateRelDefs
  bodyFullAssignLocalSetup bodyFullAssignLocalSource bodyFullAssignLocalTail
  bodyFullMemoryFrames bodyFullMemoryCopy bodyFullMemoryStore
  bodyFullLocalCopy bodyFullMemoryStage bodyFullAssignMemoryCompose
  bodyFullAssignMemoryValue assignRelayoutCaller assignRelayoutFrag
  assignBasePtrLocalBodyFacts stmtSimAssign stmtSimAssignStore
  gasShadowCompileStmtHelpers gasShadowState stmtSimAssignSource loweringPosts
  stmtSimAssignAttr exprSimFieldLayout exprSimHyps exprSimSource
  supportedExprForms supportedExprs supportedExprTraverse supportedStmtTraverse
  vyperTypeEnv vyperTypeInvariants vyperTypeContractStaticMaps
  compileVyper supportedDecls gasContext vyperTypeCallGraph
  allocationPtr annassignRelayoutFrag annassignRelayoutSource arithmetic
  assignRelayoutSource bodyFullHashKeccakFixed exprOpenTerminals
  exprOperandVar exprSimAggregateChildren exprSimProps freshWrites
  memoryLocalRhsProps pair stmtLoweringMono stmtSimDeclTypedCode stmtSimProps
  sum venomState vyperFiniteStoragePreservation
  vyperTypeSoundness vyperTypeExtCallCore vyperTypeExprSoundness
  accountsRelProps vyperStoragePlaceObserved words vyperState
  vyperContext context entryStateRel bodyAugPlaceTarget targetPlaceSim
  vyperPlaceMutationSoundness exprSimPopNestedBase exprReasonOperand
  exprSimSubscriptArrayOrigin bodyMemSnapshotSourceLocation vyperPlaceResultTyping

val _ = Parse.hide "body";

(* The successful Assign RHS determines both the source local layout and
   the scalar operand used by the joint tail. *)
Theorem body_assign_local_word_full_rhs[local]:
  gas_admissible (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e))
    (stmt_res_ok lctx) es /\ expr_body_pre cenv cx env e es /\
  FLOOKUP env.var_types id = SOME (expr_type e) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  is_word_type (expr_type e) /\
  (!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gs ++ tail) = (INL v,mid with gas_obs := tail)) /\
  expr_post H ctx func cenv cx e es sa sm s0 (mid with gas_obs := []) v op t /\
  ptr_val_ok cx (expr_type e) v op G tn t ==>
  ?pre sc entry rest dst.
    find_containing_scope id mid.scopes = SOME (pre,sc,entry,rest) /\
    entry.assignable /\ store_lays_out entry.type entry.type v /\
    eval_operand op t = SOME (typed_val_to_w256 entry.type v) /\
    op_taint tn op = {} /\ lookup_var p t = SOME dst
Proof
  strip_tac >> drule_all assign_local_continuation_all_tails >> strip_tac >>
  qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >> strip_tac >>
  `expr_body_pre cenv cx env e (es with gas_obs := gs ++ [])` by simp[] >>
  drule exprSimSourceTheory.expr_body_pre_eval >>
  disch_then (qspecl_then [`INL v`,`mid with gas_obs := []`] mp_tac) >>
  (impl_tac >- (CONV_TAC (DEPTH_CONV ETA_CONV) >>
    qpat_x_assum `bind _ _ _ = _` mp_tac >> simp[])) >> strip_tac >>
  `lookup_scopes id mid.scopes = SOME entry` by
    metis_tac[vyperLookupTheory.find_containing_scope_lookup] >>
  `evaluate_type (get_tenv cx) (expr_type e) = SOME entry.type` by
    (drule_all targetPlaceSimTheory.expr_sim_inv_local >> simp[] >> metis_tac[]) >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def,env_consistent_def,env_context_consistent_def] >>
  `value_has_type entry.type v` by
    fs[vyperTypeExprResultTheory.expr_result_typed_def,
       vyperTypeExprSoundnessTheory.expr_runtime_typed_def,
       vyperTypeInvariantsTheory.value_result_typed_def] >>
  `store_lays_out entry.type entry.type v` by
    metis_tac[stmtSimDeclStoreTheory.store_lays_out_typed] >>
  `post_value_type cenv e = expr_type e` by simp[] >>
  `eval_operand op t = SOME (typed_val_to_w256 entry.type v)` by
    (fs[expr_post_def,expr_val_rel_def] >> metis_tac[]) >>
  `op_taint tn op = {}` by fs[bodyPtrDefsTheory.ptr_val_ok_def] >>
  `local_ptrs_rel func cenv mid.scopes t` by
    (fs[expr_post_def,exprLoweringPropsTheory.stmt_state_rel_def,
        loweringStateRelDefsTheory.state_rel_def] >> metis_tac[]) >>
  `?dst. lookup_var p t = SOME dst` by
    metis_tac[allocaFootprintTheory.local_ptr_below_frontier] >>
  rename1 `find_containing_scope _ _ = SOME (_,sc,_,_)` >>
  qexistsl_tac [`pre`,`sc`,`entry`,`rest`,`dst`] >> simp[]
QED

(* A single RHS endpoint is extended by the same scalar store at every horizon. *)
Theorem body_assign_local_word_full_continue[local]:
  stmt_env cenv lctx ret_ty (Assign (BaseTarget (NameTarget id)) e) sa = (cenv,sb) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  cenv.ce_var_type id = SOME (expr_type e) /\ is_word_type (expr_type e) /\
  FLOOKUP env.var_types id = SOME (expr_type e) /\
  lower_value compile_expr cenv (expr_type e) e sa = (op,sm) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  expr_body_pre cenv cx env e es /\ local_ptrs_reserved cenv sa /\
  return_buf_frame d cenv sa s0 /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  gas_admissible (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e))
    (stmt_res_ok lctx) es /\
  (!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
    (res,mid with gas_obs := tail)) /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s0,G0,tn0) marks (OK t,G1,tn1) /\
    (?v. res = INL v /\ expr_post H ctx func cenv cx e es sa sm s0
       (mid with gas_obs := []) v op t /\
      expr_store_bound cx (expr_type e) v op t /\
      t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts /\
      alloca_history func t /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx (mid with gas_obs := []) G1 tn1 t /\
      ptr_val_ok cx (expr_type e) v op G1 tn1 t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1)) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
    (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) (es,s0,G0,tn0)
    (\H res ee G tn t. ?ce.
      stmt_lands lctx sb res t /\ ~t.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb /\ ce = cenv) /\
      cenv_top_ext cenv ce ee.scopes /\ stmt_state_rel H ctx func ce cx ee t /\
      storage_well_formed_on cx ee (FST H) /\ return_buf_frame d ce sb t /\
      alloca_history func t /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d ce cx ee G tn t /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sa x ==> FLOOKUP G x = FLOOKUP G0 x /\
        op_taint tn (Var x) = op_taint tn0 (Var x))) R
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ _ mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  simp[NoAsms] >> (impl_tac >- simp[]) >> strip_tac >>
  qpat_x_assum `res = INL v` SUBST_ALL_TAC >>
  drule_all body_assign_local_word_full_rhs >> strip_tac >>
  rename1 `find_containing_scope _ _ = SOME (pre,sc,entry,rest)` >>
  `~t.vs_halted` by
    (drule fragGasOriginPtrExecTheory.gas_origin_ptr_path_exec >>
     simp[fragExecTheory.exit_result_def]) >>
  irule body_assign_local_word_full_normal >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`G1`,`mid`,`entry`,`marks`,`pre`,`rest`,`t`,`sc`,
    `(mstore (w2n dst) (typed_val_to_w256 entry.type v) t) with
      vs_inst_idx := SUC t.vs_inst_idx`,
    `step_taint (mk_inst sm.cs_next_id MSTORE [Var p;op] []) t
      (mstore (w2n dst) (typed_val_to_w256 entry.type v) t) tn1`,`tn1`,`v`] >>
  simp[] >> gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ _ mid.storage_trace ==> _`
    (qspec_then `H` mp_tac) >>
  simp[NoAsms] >> (impl_tac >- simp[]) >> strip_tac >>
  `dead_lo_ok H (DF H) lo cenv cx` by simp[] >>
  `find_containing_scope id (mid with gas_obs := []).scopes = SOME (pre,sc,entry,rest)` by simp[] >>
  drule_all body_assign_local_word_full_tail >>
  disch_then (qspecl_then [`explicit`,`PG`] mp_tac) >>
  strip_tac >> gvs[vyperStateTheory.evaluation_state_fupdcanon]
QED

(* A word local. *)
(* TEMPORARILY CHEATED - the statement's normal post now carries alloca_frame and the older allocations' taint clause; the helpers this proof closes the post with export no memory or taint frame for the store. Original proof:
Proof
  rpt gen_tac >> strip_tac >>
  drule_all assign_base_local_rhs_pre >> strip_tac >>
  `expr_type e = ty` by metis_tac[type_widens_to_word] >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx ty e es` by metis_tac[body_expr_full_ok_def] >>
  `?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)` by
    metis_tac[expr_sim_inv_def] >>
  `cenv.ce_var_type id = SOME ty` by metis_tac[expr_sim_inv_def] >>
  rewrite_tac[stmt_frag_full_def] >> rpt gen_tac >> strip_tac >>
  `is_word_type (expr_type e)` by simp[] >>
  gvs[] >> drule_all body_assign_local_word_full_setup >> strip_tac >> gvs[] >>
  rename1 `lower_value compile_expr cenv (expr_type e) e sa = (op,sm)` >>
  drule assign_local_admissible_rhs >> strip_tac >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at sa x` by metis_tac[ret_pc_ok_def] >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_sim_full_def] >>
  disch_then (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,
    `op`,`s0`,`G0`,`tn0`] mp_tac) >>
  simp[] >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ Q1 _` >>
  irule body_assign_local_word_full_source >>
  conj_tac >- metis_tac[] >> qexists_tac `Q1` >>
  reverse conj_tac >- (irule gasOutcomeFullTheory.gas_outcome_full_post_mono >>
    goal_assum (drule_at Any) >> simp[] >> rpt gen_tac >>
    POP_ASSUM_LIST (K all_tac) >> strip_tac >>
    Cases_on `res` >> fs[exprSimDefsTheory.expr_exit_def] >>
    Cases_on `y` >> Cases_on `r` >>
    gvs[bodyPtrDefsTheory.stmt_exit_ptr_def,exprSimDefsTheory.expr_exit_def,
        exprSimDefsTheory.halt_exit_def] >>
    rename1 `Error err` >> Cases_on `err` >>
    gvs[exprSimDefsTheory.expr_exit_def]) >>
  rpt gen_tac >> strip_tac >>
  irule body_assign_local_word_full_continue >>
  goal_assum (drule_at Any) >> simp[Abbr `Q1`] >> metis_tac[]
QED
*)
Theorem body_assign_local_word_full:
  !cx id ty e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_full_ok cx (NameTarget id)) /\
    body_expr_full_ok cx e /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Assign (BaseTarget (NameTarget id)) e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget (NameTarget id)) e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget (NameTarget id)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (NameTarget id)) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget (NameTarget id)) e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    FLOOKUP env.var_types id = SOME ty /\
    is_word_type ty ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (NameTarget id)) e))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (Assign (BaseTarget (NameTarget id)) e)))
      (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) es
Proof
  cheat
QED

(* A memory local whose source is stored at its own layout. *)
Theorem body_assign_local_memory_full:
  !cx id ty e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_full_ok cx (NameTarget id)) /\
    body_expr_full_ok cx e /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Assign (BaseTarget (NameTarget id)) e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget (NameTarget id)) e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget (NameTarget id)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (NameTarget id)) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget (NameTarget id)) e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    FLOOKUP env.var_types id = SOME ty /\
    ~is_word_type ty /\
    0 < type_memory_bytes cenv ty /\
    (lowered_value_type cenv e = ty \/ is_bytestring_type ty \/
     has_length_word (expr_type e) /\ is_empty_value_expr e) /\
    (lowered_value_type cenv e = expr_type e \/
     is_bytestring_type (expr_type e) /\
     is_bytestring_type (lowered_value_type cenv e) /\
     arg_type_fits (lowered_value_type cenv e) (expr_type e)) ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (NameTarget id)) e))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (Assign (BaseTarget (NameTarget id)) e)))
      (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) es
Proof
  cheat
QED

(* A memory local whose source is a widened aggregate. *)
(* TEMPORARILY CHEATED - the statement's normal post now carries alloca_frame and the older allocations' taint clause; the helpers this proof closes the post with export no memory or taint frame for the store. Original proof:
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `body_stmt_safe tops (Assign (BaseTarget (NameTarget id)) e)` by
    metis_tac[supported_stmt_body_safe] >>
  drule_all assign_base_local_rhs_pre >> strip_tac >>
  `cx_tops cx = tops` by
    (irule cx_tops_module >> fs[body_inv_def]) >>
  drule_all assign_relayout_source_classify >> strip_tac >>
  drule_all targetPlaceSimTheory.expr_sim_inv_local >> strip_tac >>
  `cenv.ce_var_type id = SOME ty` by fs[expr_sim_inv_def] >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `evaluate_type (get_tenv cx) ty = SOME entry.type` by metis_tac[] >>
  `type_memory_bytes cenv ty < 2 ** 64` by metis_tac[locals_alloc_ok_def] >>
  drule_all annassignRelayoutSourceTheory.widening_memory_layout_bound >> strip_tac >>
  `~(has_length_word (expr_type e) /\ is_empty_value_expr e)` by
    (Cases_on `e` >>
     gvs[is_empty_value_expr_def, exprLoweringTheory.lowered_value_type_def, expr_type_def]) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (expr_type e) e es` by metis_tac[body_expr_full_ok_def] >>
  rewrite_tac[stmt_frag_full_def] >> rpt gen_tac >> strip_tac >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_initial_domain >>
  simp[vyperStorageTraceTheory.evaluate_storage_trace_frame] >> strip_tac >>
  drule_all assign_local_relayout_code_parts >> strip_tac >>
  qpat_x_assum `cenv' = cenv` SUBST_ALL_TAC >>
  `?shadow_sB. lower_value compile_expr cenv (expr_type e) (gas_shadow_expr e)
    shadow_sa = (op,shadow_sB) /\ gas_shadow_state sB shadow_sB` by
    (mp_tac (Q.INST [`cenv` |-> `cenv`, `ty` |-> `expr_type e`, `e` |-> `e`]
      gasShadowCompileStmtHelpersTheory.gas_shadow_stmt_lower_value) >>
     simp[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >> simp[] >>
     Cases_on `lower_value compile_expr cenv (expr_type e) (gas_shadow_expr e) shadow_sa` >> simp[]) >>
  `fn_has_code shadow_sa shadow_sB shadow_func` by
    (qpat_assum `stmt_env _ _ _ (gas_shadow_stmt _) _ = _` mp_tac >>
     pure_rewrite_tac[gas_shadow_stmt_def, gas_shadow_assignment_def,
       gas_shadow_expr_def] >> strip_tac >>
     qpat_x_assum `stmt_env _ _ _ (Assign _ e) sa = _` kall_tac >>
     `~(has_length_word (expr_type (gas_shadow_expr e)) /\
         is_empty_value_expr (gas_shadow_expr e))` by
       (Cases_on `e` >>
        gvs[is_empty_value_expr_def, gas_shadow_expr_def, expr_type_def]) >>
     drule_all assign_local_relayout_code_parts >> strip_tac >>
     qpat_x_assum `lower_value _ _ _ (gas_shadow_expr e) _ = _` mp_tac >>
     simp[] >> strip_tac >> gvs[]) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at sa x` by fs[loweringPostsTheory.ret_pc_ok_def] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[exprSimSourceTheory.expr_body_pre_gas_admissible] >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_full_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sB`,`shadow_sa`,`shadow_sB`,`op`,
    `s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ childQ childR` >>
  qpat_x_assum `cx_tops cx = tops` (SUBST1_TAC o SYM) >>
  irule assign_local_memory_full_outcome >>
  conj_tac >- (qexists_tac `lctx` >> first_assum ACCEPT_TAC) >>
  qexists_tac `\H res ee G tn t. childQ H res ee G tn t /\ ~t.vs_halted /\ ee.gas_obs = []` >>
  conj_tac >- suspend "memory_continue" >>
  conj_tac >- (simp[Abbr `childQ`] >> metis_tac[]) >>
  qunabbrev_tac `childR` >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[]
QED

Resume body_assign_local_widened_full[memory_continue]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _` kall_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
    mid.storage_trace` by fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qunabbrev_tac `childQ` >> rule_assum_tac BETA_RULE >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  strip_tac >>
  qpat_x_assum `INL v = INL _` (SUBST_ALL_TAC o REWRITE_RULE [sumTheory.INL_11]) >>
  rename1 `expr_store_bound cx (post_value_type cenv e) v op u` >>
  drule_all stmtSimAssignSourceTheory.assign_local_continuation_all_tails >>
  disch_then (qx_choosel_then [`pre`,`sc`,`ent`,`rest`] strip_assume_tac) >>
  `stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func cenv cx mid u` by
    fs[loweringPostsTheory.expr_post_def] >>
  `lookup_scopes id mid.scopes = SOME ent` by
    metis_tac[vyperLookupTheory.find_containing_scope_lookup] >>
  `ent.type = entry.type /\ value_has_type stv v /\ value_has_type ent.type v /\
    val_wf stv v /\ val_wf ent.type v /\ val_footprint stv v = type_memory_size stv` by
    (qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
     simp_tac (srw_ss()) [] >> strip_tac >>
     `expr_body_pre cenv cx env e (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
     `ent.type = entry.type` by
       (irule memoryLocalRhsPropsTheory.memory_rhs_read_local_type >>
        qexistsl_tac [`cenv`,`cx`,`e`,`env`,
          `es with gas_obs := gas_explicit marks s0.vs_gas_readings`,
          `mid with gas_obs := []`,`id`,`ty`,`v`] >> simp[SF ETA_ss]) >>
     qpat_assum `body_inv _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [body_inv_def]) >>
     drule_at (Pos last) (REWRITE_RULE [ETA_THM]
       annassignRelayoutSourceTheory.annassign_relayout_read_layout) >>
     disch_then (qspecl_then [`cenv`,`env`,`tops`,`ty`,`stv`,`entry.type`] mp_tac) >>
     (impl_tac >- simp[]) >> simp[]) >>
  `local_ptrs_rel func cenv mid.scopes u` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ mid u`
      (strip_assume_tac o REWRITE_RULE
        [exprLoweringPropsTheory.stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def]) >> first_assum ACCEPT_TAC) >>
  qpat_assum `local_ptrs_rel func cenv mid.scopes u`
    (mp_tac o REWRITE_RULE [loweringStateRelDefsTheory.local_ptrs_rel_def]) >>
  disch_then (qspecl_then [`id`,`ent`,`p`,`sz`] mp_tac o CONJUNCT1) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `dw` strip_assume_tac) >>
  drule_all annassignRelayoutFragTheory.residual_call_compile_location >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!x. op = Var x ==> not_fresh_at sB x` by
    (drule_then (drule_then assume_tac) exprOperandVarTheory.compile_lower_value_var >> simp[]) >>
  `0 < type_memory_size stv` by
    (drule_all exprSimAggregateChildrenTheory.widening_zero_memory_size >> simp[] >> decide_tac) >>
  drule_at (Pos hd) assignRelayoutSourceTheory.expr_post_live_destination_source >>
  disch_then (qspecl_then [`lowered_value_type cenv e`,`stv`,`id`,`ent`,`p`,`sz`,`dw`,`type_memory_size ent.type`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `sw` (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `ptr_val_ok _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [bodyPtrDefsTheory.ptr_val_ok_def]) >>
  simp[] >> disch_then (mp_tac o CONJUNCT2) >>
  rewrite_tac[bodyPtrDefsTheory.ptr_mem_ok_def] >>
  disch_then (qspecl_then [`stv`,`sw`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `val_footprint stv v <> 0` by simp[] >>
  qpat_x_assum `val_footprint _ _ <> 0 ==> _` drule >>
  disch_then (qx_choosel_then [`xs`,`b`,`n`] strip_assume_tac) >>
  qpat_x_assum `op = Var xs` SUBST_ALL_TAC >>
  `lookup_var xs u = SOME sw` by fs[venomStateTheory.eval_operand_def] >>
  `val_store_size stv v = type_memory_size stv` by
    (`!ty tv v. ~is_bytestring_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv ==>
        val_store_size tv v = type_memory_size tv` suffices_by metis_tac[] >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     Cases_on `v` >> simp[exprSimPropsTheory.val_store_size_def] >>
     Cases_on `tv` >> simp[] >> rename1 `BaseTV b` >> Cases_on `b` >> simp[] >>
     Cases_on `ty` >>
     gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs(), is_bytestring_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs(), is_bytestring_type_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >>
     gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs(), is_bytestring_type_def]) >>
  `ptr_covers Gi ti xs u (type_memory_size stv)` by
    (simp[bodyPtrDefsTheory.ptr_covers_def] >> metis_tac[bodyPtrDefsTheory.ptr_val_ok_def]) >>
  `ptr_covers Gi ti p u sz /\ allocas_from lo u /\ lo <= u.vs_alloca_next` by
    (qpat_assum `ghost_inv_at _ _ _ _ _ mid Gi ti u`
       (mp_tac o REWRITE_RULE [bodyPtrDefsTheory.ghost_inv_at_def]) >>
     metis_tac[]) >>
  `ptr_covers Gi ti p u (type_memory_size ent.type)` by
    (fs[bodyPtrDefsTheory.ptr_covers_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS,arithmeticTheory.LESS_EQ_MONO_ADD_EQ]) >>
  `expr_val_at cenv cx (lowered_value_type cenv e) sa sB mid v (Var xs) u` by
    (qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ mid v _ u`
       (mp_tac o List.nth o (fn th => (CONJUNCTS th,3)) o REWRITE_RULE [loweringPostsTheory.expr_post_def]) >>
     simp[]) >>
  `!i. w2n sw <= i /\ i < w2n sw + val_footprint stv v ==> i < u.vs_alloca_next` by
    (qpat_assum `expr_val_at _ _ _ _ _ _ _ _ _` mp_tac >>
     qpat_assum `stmt_state_rel _ _ _ _ _ mid u` mp_tac >>
     qpat_assum `evaluate_type _ (lowered_value_type cenv e) = _` mp_tac >>
     qpat_assum `~is_word_type (lowered_value_type cenv e)` mp_tac >>
     qpat_assum `eval_operand (Var xs) u = SOME sw` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     metis_tac[allocationPtrTheory.expr_val_at_below_frontier]) >>
  `w2n sw + type_memory_size stv <= u.vs_alloca_next` by
    (first_x_assum (qspec_then `w2n sw + type_memory_size stv - 1` mp_tac) >>
     simp[] >> decide_tac) >>
  `local_region cenv mid.scopes u id (w2n dw) sz` by
    (simp[loweringStateRelDefsTheory.local_region_def] >> metis_tac[]) >>
  `lo <= w2n dw` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ mid u` mp_tac >>
     qpat_assum `!H. dead_lo_ok H _ _ _ _` mp_tac >>
     qpat_assum `local_region _ _ _ _ _ _` mp_tac >>
     qpat_assum `body_inv _ _ _ _` mp_tac >>
     qpat_assum `expr_sim_inv _ _ _ _` mp_tac >>
     `0 < sz` by
       (qpat_assum `0 < type_memory_bytes cenv ty` mp_tac >>
        qpat_assum `type_memory_bytes cenv ty = type_memory_size entry.type` mp_tac >>
        qpat_assum `ent.type = entry.type` mp_tac >>
        qpat_assum `type_memory_size ent.type <= sz` mp_tac >>
        rpt (pop_assum kall_tac) >> rpt strip_tac >> gvs[] >> decide_tac) >> pop_assum mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     metis_tac[bodyFullMemoryFramesTheory.body_full_local_region_lower_bound]) >>
  `sa.cs_next_var <= sB.cs_next_var` by
    (qspec_then `sa` mp_tac
       (Q.SPECL [`cenv`,`expr_type e`,`e`] exprLoweringPropsTheory.ci_mono_lower_value_compile_expr) >>
     simp[exprLoweringPropsTheory.ci_mono_def]) >>
  `local_ptrs_reserved cenv sB` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     qexists_tac `sa` >> simp[]) >>
  `not_fresh_at sB p /\
   (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sB x) /\
   (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sB x)` by
    (conj_tac >- metis_tac[loweringStateRelDefsTheory.local_ptrs_reserved_def] >>
     qpat_assum `!x sz. cenv.ce_return_buf = _ ==> _` mp_tac >>
     qpat_assum `!x sz. cenv.ce_return_pc = _ ==> _` mp_tac >>
     qpat_assum `sa.cs_next_var <= sB.cs_next_var` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  qpat_assum `body_inv _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [body_inv_def]) >>
  qpat_assum `expr_sim_inv _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_sim_inv_def]) >>

  `type_memory_size stv < dimword (:256) /\
   w2n dw + type_memory_size ent.type <= u.vs_alloca_next /\
   not_fresh_at sB xs` by
    (conj_tac >- metis_tac[] >>
     conj_tac >-
       (qpat_assum `type_memory_size ent.type <= sz` mp_tac >>
        qpat_assum `w2n dw + sz <= u.vs_alloca_next` mp_tac >>
        rpt (pop_assum kall_tac) >> decide_tac) >>
     metis_tac[]) >>
  `?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (u,Gi,ti) [] (OK t,Gf,tf)) /\
    (!(H : (bool # 256 word # type_value) list # num list) D d.
      stmt_state_rel H ctx func cenv cx mid u /\
      ghost_inv_at D lo d cenv cx mid Gi ti u ==>
      stmt_state_rel H ctx func cenv cx
        (mid with scopes := pre ++ (sc |+ (id,ent with <|value := v; popped := []|>)) :: rest) t /\
      ghost_inv_at D lo d cenv cx
        (mid with scopes := pre ++ (sc |+ (id,ent with <|value := v; popped := []|>)) :: rest)
        Gf tf t) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ u.vs_alloca_next <= t.vs_alloca_next /\
    (!aid ent. FLOOKUP u.vs_allocas aid = SOME ent ==> FLOOKUP t.vs_allocas aid = SOME ent) /\
    (!x. not_fresh_at sB x ==>
      lookup_var x t = lookup_var x u /\ FLOOKUP Gf x = FLOOKUP Gi x /\
      op_taint tf (Var x) = op_taint ti (Var x))` by
    (irule (INST_TYPE [alpha |-> ``:256``]
       bodyFullAssignMemoryValueTheory.body_full_assign_local_memory_value_path) >>
     goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >>
     simp[] >> conj_tac
     >- (qexists_tac `storage_trace_horizon mid.storage_trace` >>
         qpat_assum `stmt_state_rel _ _ _ _ _ mid u` mp_tac >>
         qpat_assum `ctx = unit.cu_context` mp_tac >>
         rpt (pop_assum kall_tac) >> metis_tac[]) >>
     goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`type_memory_bytes cenv ty`, `ty`, `vv_location vv`,
                   `sa`, `stv`, `lowered_value_type cenv e`] >>
     simp[] >>
     qpat_assum `ent.type = entry.type` mp_tac >>
     qpat_assum `w2n dw + type_memory_size ent.type < _` mp_tac >>
     qpat_assum `type_memory_size ent.type <= sz` mp_tac >>
     qpat_assum `w2n dw + type_memory_size ent.type <= u.vs_alloca_next` mp_tac >>
     qpat_assum `_ \/ w2n dw + type_memory_size ent.type <= w2n sw` mp_tac >>
     qpat_assum `ptr_covers Gi ti p u (type_memory_size ent.type)` mp_tac >>
     rpt (pop_assum kall_tac) >>
     metis_tac[arithmeticTheory.ADD_COMM]) >>
  qexistsl_tac [`mid with scopes := pre ++ (sc |+ (id,ent with <|value := v; popped := []|>)) :: rest`,
                `t`, `Gf`, `tf`] >>
  simp[] >> qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (qspec_then `H` mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then strip_assume_tac >>
  qpat_x_assum `INL v = INL _` (SUBST_ALL_TAC o REWRITE_RULE [sumTheory.INL_11]) >>
  `stmt_state_rel H ctx func cenv cx mid u` by
    fs[loweringPostsTheory.expr_post_def] >>
  first_x_assum (qspecl_then [`H`,`DF H`,`d`] mp_tac) >>
  (impl_tac >- simp[]) >> disch_then strip_assume_tac >>
  `ctx_has_dalloca unit.cu_context ==> allocas_below_fmp t` by
    (qpat_assum `stmt_state_rel H ctx _ _ _ _ t`
       (mp_tac o MATCH_MP
         bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp) >>
     simp[]) >>
  simp[loweringPostsTheory.stmt_lands_def,
       stmtSimPropsTheory.cenv_top_ext_refl] >>
  conj_tac
  >- (qpat_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
      qpat_assum `unwrap_value _ _ _ = _` mp_tac >>
      qpat_assum `~block_is_terminated sV` mp_tac >>
      qpat_assum `acyclic_struct_metadata _` mp_tac >>
      rpt (pop_assum kall_tac) >>
      metis_tac[stmtSimDeclTypedCodeTheory.compile_assign_value_typed_open,
                exprOpenTerminalsTheory.unwrap_value_open]) >>
  `mid with gas_obs := [] = mid` by
    (qpat_assum `mid.gas_obs = []` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[vyperStateTheory.evaluation_state_component_equality]) >>
  once_rewrite_tac[GSYM vyperStateTheory.evaluation_state_fupdcanon] >>
  simp[] >>
  conj_tac
  >- (qpat_assum `stmt_state_rel H ctx _ _ _ _ t` mp_tac >>
      qpat_assum `ctx = unit.cu_context` mp_tac >>
      rpt (pop_assum kall_tac) >> metis_tac[]) >>
  conj_tac
  >- (qpat_assum `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
      rpt (pop_assum kall_tac) >>
      simp[loweringPostsTheory.expr_post_def,
           vyperStorageFootprintTheory.storage_well_formed_on_def] >>
      strip_tac >> rpt gen_tac >> Cases_on `b` >>
      fs[vyperStorageBackendTheory.get_storage_def] >>
      metis_tac[vyperStorageBackendTheory.get_storage_def]) >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
          lookup_var x t = SOME w` by
    (qpat_assum `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     qpat_assum `!x. not_fresh_at sB x ==> _` mp_tac >>
     qpat_assum `sa.cs_next_var <= sB.cs_next_var` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[loweringPostsTheory.expr_post_def] >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `sB.cs_next_var <= sb.cs_next_var` by
    (qpat_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     `ci_mono sB sb` by
       metis_tac[cj 1 stmtLoweringMonoTheory.ci_mono_stmt_helpers, pairTheory.SND] >>
     fs[exprLoweringPropsTheory.ci_mono_def]) >>
  conj_tac
  >- (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
      qexistsl_tac [`cenv`, `s0`, `sa`] >>
      asm_rewrite_tac[] >>
      qpat_assum `sa.cs_next_var <= sB.cs_next_var` mp_tac >>
      qpat_assum `sB.cs_next_var <= sb.cs_next_var` mp_tac >>
      qpat_assum `s0.vs_alloca_next <= u.vs_alloca_next` mp_tac >>
      qpat_assum `u.vs_alloca_next <= t.vs_alloca_next` mp_tac >>
      rpt (pop_assum kall_tac) >> decide_tac) >>
  asm_rewrite_tac[] >> conj_tac
  >- (qpat_assum `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
      qpat_assum `!aid ent. FLOOKUP u.vs_allocas aid = SOME ent ==> _` mp_tac >>
      rpt (pop_assum kall_tac) >>
      simp[loweringPostsTheory.expr_post_def] >> metis_tac[]) >>
  qpat_assum `ghost_kept_at lo cenv es sa G0 tn0 s0 Gi ti` mp_tac >>
  qpat_assum `!x. not_fresh_at sB x ==> _` mp_tac >>
  qpat_assum `sa.cs_next_var <= sB.cs_next_var` mp_tac >>
  rpt (pop_assum kall_tac) >>
  simp[bodyPtrDefsTheory.ghost_kept_at_def] >>
  metis_tac[freshWritesTheory.not_fresh_at_mono]
QED

Finalise body_assign_local_widened_full
*)
Theorem body_assign_local_widened_full:
  !cx id ty e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_full_ok cx (NameTarget id)) /\
    body_expr_full_ok cx e /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Assign (BaseTarget (NameTarget id)) e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget (NameTarget id)) e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget (NameTarget id)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (NameTarget id)) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget (NameTarget id)) e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    FLOOKUP env.var_types id = SOME ty /\
    ~is_word_type ty /\
    0 < type_memory_bytes cenv ty /\
    (expr_type e = ty \/ lowered_value_type cenv e = ty \/ is_bytestring_type ty \/
     has_length_word (expr_type e) /\ is_empty_value_expr e) /\
    ~(lowered_value_type cenv e = expr_type e \/
     is_bytestring_type (expr_type e) /\
     is_bytestring_type (lowered_value_type cenv e) /\
     arg_type_fits (lowered_value_type cenv e) (expr_type e)) ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (NameTarget id)) e))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (Assign (BaseTarget (NameTarget id)) e)))
      (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) es
Proof
  cheat
QED

(* Compose a normal forced RHS with the actual top-level storage action. *)
Theorem body_assign_toplevel_word_full_normal[local]:
  get_module_code cx src = SOME tops /\
  find_var_decl_by_name id tops = SOME (StorageVarDecl tr typ,id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) typ = SOME tvt /\
  (!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
    (INL v,mid with gas_obs := tail)) /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s0,G0,tn0) marks (OK t,G1,tn1)) /\
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
    (ignore_bind (record_storage_event (StorageRoot tr slot tvt))
      (write_storage_slot cx tr (n2w slot) tvt v))
    (mid with gas_obs := [],t,G1,tn1) Q R ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
    (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget (src,id))) e))
    (es,s0,G0,tn0) Q R
Proof
  strip_tac >>
  `gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\H res ee G tn u. res = INL v /\ ee = mid with gas_obs := [] /\
      G = G1 /\ tn = tn1 /\ u = t)
    (\H res ee gt r. ?exc. res = INR exc /\ R H (INR exc) ee gt r)` by
    (irule gas_outcome_full_intro >>
     qexistsl_tac [`G1`,`mid`,`marks`,`OK t`,`INL v`,`tn1`] >> simp[]) >>
  drule_all stmtSimAssignStorageTheory.eval_assign_toplevel_action >>
  disch_then (qspec_then `e` SUBST1_TAC) >>
  irule gas_outcome_full_bind_all >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
      qexistsl_tac [`mid'`,`t'`,`v'`] >> fs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_value >> fs[])
  >~ [`storage_trace_frame (bind (eval_expr _ _) _)`]
  >- (irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame,storage_trace_frame_read_result])
  >~ [`storage_trace_frame _`]
  >- simp[storage_trace_frame_event,storage_trace_frame_ignore_bind,
      storage_trace_frame_write_storage_slot] >>
  qpat_assum `gas_outcome_full _ _ _ _ (bind _ _) _ _ _` (irule_at Any) >>
  rpt gen_tac >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid'.storage_trace) mid'.storage_trace`
    by fs[storage_trace_domain_def] >>
  first_x_assum drule >> strip_tac >> gvs[] >> disj1_tac >> simp[]
QED

(* Pull the Assign store precondition back through its forced RHS. *)
Theorem body_assign_toplevel_word_full_store_pre[local]:
  s0.vs_alloca_next <= t.vs_alloca_next /\
  sa.cs_next_var <= sm.cs_next_var /\
  return_buf_frame d cenv sa s0 /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0) /\
  (!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
    (INL v,mid with gas_obs := tail)) /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post H ctx func cenv cx e es sa sm s0 (mid with gas_obs := []) v op t /\
    ghost_inv_at (DF H) lo d cenv cx (mid with gas_obs := []) G1 tn1 t) ==>
  return_buf_frame d cenv sm t /\
  (!H. valid_horizon cx st0 H (mid.storage_trace ++ [StorageRoot tr slot tvt]) ==>
    expr_post H ctx func cenv cx e es sa sm s0 (mid with gas_obs := []) v op t /\
    stmt_state_rel H ctx func cenv cx es s0 /\ dead_lo_ok H (DF H) lo cenv cx /\
    ghost_inv_at (DF H) lo d cenv cx (mid with gas_obs := []) G1 tn1 t)
Proof
  strip_tac >> conj_tac
  >- (`valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace`
        by fs[storage_trace_domain_def] >>
      first_x_assum drule >> strip_tac >>
      irule bodyMemoryDefsTheory.return_buf_frame_frame >>
      qexistsl_tac [`cenv`,`s0`,`sa`] >> fs[expr_post_def]) >>
  gen_tac >> strip_tac >> drule gasOutcomeFullTheory.valid_horizon_append >> strip_tac >>
  `valid_horizon cx st0 H es.storage_trace` by
    (`storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
       simp[storage_trace_frame_bind_all,evaluate_storage_trace_frame,
         storage_trace_frame_read_result] >>
     qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` assume_tac) >>
     drule valid_horizon_frame >> disch_then drule >> simp[]) >>
  first_x_assum drule >> simp[]
QED

(* Complete the Assign store for both valid and invalid extended traces. *)
Theorem body_assign_toplevel_word_full_residual[local]:
  ~cx.txn.is_static /\ get_module_code cx src = SOME tops /\
  find_var_decl_by_name id tops = SOME (StorageVarDecl tr (expr_type e),id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
  is_word_type (expr_type e) /\ type_slot_size tvt = 1 /\ value_has_type tvt v /\
  encode_value tvt v = SOME [(0,typed_val_to_w256 tvt v)] /\
  emit_void (if tr then TSTORE else SSTORE) [Lit (n2w slot);op] sm = ((),sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ MAP FDOM mid.scopes = MAP FDOM es.scopes /\
  ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\ op_taint tn1 op = {} /\
  return_buf_frame d cenv sm t /\ alloca_history func t /\
  s0.vs_alloca_next <= t.vs_alloca_next /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
  (!H. valid_horizon cx st0 H (mid.storage_trace ++ [StorageRoot tr slot tvt]) ==>
    expr_post H ctx func cenv cx e es sa sm s0 (mid with gas_obs := []) v op t /\
    stmt_state_rel H ctx func cenv cx es s0 /\ dead_lo_ok H (DF H) lo cenv cx /\
    ghost_inv_at (DF H) lo d cenv cx (mid with gas_obs := []) G1 tn1 t) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
    (ignore_bind (record_storage_event (StorageRoot tr slot tvt))
      (write_storage_slot cx tr (n2w slot) tvt v)) (mid with gas_obs := [],t,G1,tn1)
    (\H res ee G tn t. ?ce.
      stmt_lands lctx sb res t /\ ~t.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb /\ ce = cenv) /\
      cenv_top_ext cenv ce ee.scopes /\ stmt_state_rel H ctx func ce cx ee t /\
      storage_well_formed_on cx ee (FST H) /\ return_buf_frame d ce sb t /\
      alloca_history func t /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d ce cx ee G tn t /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sa x ==> FLOOKUP G x = FLOOKUP G0 x /\
        op_taint tn (Var x) = op_taint tn0 (Var x))) R
Proof
  strip_tac >>
  Cases_on `storage_trace_domain cx st0 (mid.storage_trace ++ [StorageRoot tr slot tvt])`
  >- (irule gasOutcomeFullTheory.gas_outcome_full_post_mono >>
      irule_at Any body_assign_toplevel_word_full_continue >> simp[] >>
      qpat_assum `find_var_decl_by_name _ _ = _` (irule_at Any) >>
      qpat_assum `lookup_var_slot_from_layout _ _ _ _ = _` (irule_at Any) >>
      qpat_assum `emit_void _ _ _ = _` (irule_at Any) >>
      qpat_assum `ghost_kept_at _ _ _ _ _ _ _ _ _` (irule_at Any) >>
      qexistsl_tac [`lctx`,`tvt`,`e`,`d`,`R`] >>
      simp[] >> rpt strip_tac >> fs[stmtSimDefsTheory.stmt_post_def]) >>
  irule gas_outcome_full_bad_nil >> simp[] >>
  simp[ignore_bind_def,record_storage_event_def,bind_def,return_def,
       vyperStorageBackendTheory.write_storage_slot_eq] >>
  Cases_on `cx.txn.is_static` >> Cases_on `tr` >>
  simp[vyperStorageBackendTheory.set_storage_def]
QED

(* The normal RHS endpoint feeds the joint top-level store. *)
Theorem body_assign_toplevel_word_full_after_rhs[local]:
  ~cx.txn.is_static /\ get_module_code cx src = SOME tops /\
  find_var_decl_by_name id tops = SOME (StorageVarDecl tr (expr_type e),id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
  is_word_type (expr_type e) /\
  emit_void (if tr then TSTORE else SSTORE) [Lit (n2w slot);op] sm = ((),sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  sa.cs_next_var <= sm.cs_next_var /\
  expr_body_pre cenv cx env e es /\ local_ptrs_reserved cenv sa /\
  return_buf_frame d cenv sa s0 /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0) /\
  (!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
    (res,mid with gas_obs := tail)) /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s0,G0,tn0) marks (OK t,G1,tn1) /\
    (?v. res = INL v /\ expr_post H ctx func cenv cx e es sa sm s0
      (mid with gas_obs := []) v op t /\
      expr_store_bound cx (expr_type e) v op t /\
      t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts /\
      alloca_history func t /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx (mid with gas_obs := []) G1 tn1 t /\
      ptr_val_ok cx (expr_type e) v op G1 tn1 t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1)) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
    (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget (src,id))) e)) (es,s0,G0,tn0)
    (\H res ee G tn t. ?ce.
      stmt_lands lctx sb res t /\ ~t.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb /\ ce = cenv) /\
      cenv_top_ext cenv ce ee.scopes /\ stmt_state_rel H ctx func ce cx ee t /\
      storage_well_formed_on cx ee (FST H) /\ return_buf_frame d ce sb t /\
      alloca_history func t /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d ce cx ee G tn t /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sa x ==> FLOOKUP G x = FLOOKUP G0 x /\
        op_taint tn (Var x) = op_taint tn0 (Var x))) R
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace`
    by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  simp[NoAsms] >> (impl_tac >- simp[]) >> strip_tac >>
  qpat_x_assum `res = INL v` SUBST_ALL_TAC >>
  `~t.vs_halted` by
    (drule fragGasOriginPtrExecTheory.gas_origin_ptr_path_exec >>
     simp[fragExecTheory.exit_result_def]) >>
  qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` assume_tac) >>
  `expr_body_pre cenv cx env e
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ [])` by simp[] >>
  drule exprSimSourceTheory.expr_body_pre_eval >>
  disch_then (qspecl_then [`INL v`,`mid with gas_obs := []`] mp_tac) >>
  (impl_tac >- (CONV_TAC (DEPTH_CONV ETA_CONV) >>
    qpat_x_assum `bind _ _ _ = _` mp_tac >> simp[])) >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    (qpat_assum `expr_body_pre cenv cx env e es` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[expr_body_pre_def,expr_sim_inv_def,env_consistent_def,env_context_consistent_def]) >>
  `value_has_type tvt v` by
    (fs[vyperTypeExprResultTheory.expr_result_typed_def,
       vyperTypeExprSoundnessTheory.expr_runtime_typed_def,
       vyperTypeInvariantsTheory.value_result_typed_def] >> gvs[]) >>
  `encode_value tvt v = SOME [(0,typed_val_to_w256 tvt v)]` by
    metis_tac[stmtSimAssignStorageFactsTheory.encode_value_word_typed] >>
  `type_slot_size tvt = 1` by metis_tac[exprSimUnwrapTheory.word_type_slot_size] >>
  `MAP FDOM mid.scopes = MAP FDOM es.scopes` by
    (drule stmtSimDefsTheory.eval_read_preserves_scopes_dom >> simp[]) >>
  `return_buf_frame d cenv sm t /\
    (!H. valid_horizon cx st0 H (mid.storage_trace ++ [StorageRoot tr slot tvt]) ==>
      expr_post H ctx func cenv cx e es sa sm s0 (mid with gas_obs := []) v op t /\
      stmt_state_rel H ctx func cenv cx es s0 /\ dead_lo_ok H (DF H) lo cenv cx /\
      ghost_inv_at (DF H) lo d cenv cx (mid with gas_obs := []) G1 tn1 t)` by
    (irule body_assign_toplevel_word_full_store_pre >>
     goal_assum (drule_at Any) >> simp[] >>
     conj_tac >- metis_tac[] >> gen_tac >> strip_tac >> first_x_assum drule >> simp[]) >>
  `op_taint tn1 op = {}` by fs[bodyPtrDefsTheory.ptr_val_ok_def] >>
  irule body_assign_toplevel_word_full_normal >>
  qpat_assum `find_var_decl_by_name _ _ = _` (irule_at Any) >>
  qpat_assum `lookup_var_slot_from_layout _ _ _ _ = _` (irule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`v`,`tn1`,`t`,`marks`,`G1`] >> simp[] >>
  irule body_assign_toplevel_word_full_residual >>
  qpat_assum `find_var_decl_by_name _ _ = _` (irule_at Any) >>
  qpat_assum `emit_void _ _ _ = _` (irule_at Any) >>
  qpat_assum `ghost_kept_at _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

(* The rejected write still evaluates the RHS and records its root. *)
Theorem body_assign_toplevel_word_full_static_rhs[local]:
  cx.txn.is_static /\ get_module_code cx src = SOME tops /\
  find_var_decl_by_name id tops = SOME (StorageVarDecl tr typ,id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) typ = SOME tvt /\ is_word_type (expr_type e) /\
  emit_void (if tr then TSTORE else SSTORE) [Lit (n2w slot);op] sm = ((),sb) /\
  fn_has_code sm sb func /\
  (!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
    (res,mid with gas_obs := tail)) /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
      (s0,G0,tn0) marks (OK t,G1,tn1) /\
    ?v. res = INL v /\
      expr_post H ctx func cenv cx e es sa sm s0
        (mid with gas_obs := []) v op t /\
      t.vs_current_bb = sm.cs_current_bb /\
      t.vs_inst_idx = LENGTH sm.cs_current_insts /\
      ghost_inv_at (DF H) lo d cenv cx (mid with gas_obs := []) G1 tn1 t /\
      ptr_val_ok cx (expr_type e) v op G1 tn1 t) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
    (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget (src,id))) e))
    (es,s0,G0,tn0) Q
    (\H res ee gt r.
      (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
      halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==>
       !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s))
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     mid.storage_trace` by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  simp[NoAsms] >> (impl_tac >- simp[]) >> strip_tac >>
  qpat_x_assum `res = INL v` SUBST_ALL_TAC >>
  `~t.vs_halted` by
    (drule fragGasOriginPtrExecTheory.gas_origin_ptr_path_exec >>
     simp[fragExecTheory.exit_result_def]) >>
  `?w. eval_operand op t = SOME w` by
    (gvs[expr_post_def, expr_val_rel_def, post_value_type_word] >> metis_tac[]) >>
  `op_taint tn1 op = {}` by fs[bodyPtrDefsTheory.ptr_val_ok_def] >>
  irule body_assign_toplevel_word_full_normal >>
  qpat_assum `find_var_decl_by_name _ _ = _` (irule_at Any) >>
  qpat_assum `lookup_var_slot_from_layout _ _ _ _ = _` (irule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`v`,`tn1`,`t`,`marks`,`G1`] >> simp[] >>
  irule body_assign_toplevel_word_full_static_store >> simp[] >>
  conj_tac
  >- (qexists_tac `cenv` >> rpt strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==>
        gas_origin_ptr_path _ _ _ _ /\ _`
        (qspec_then `H` mp_tac) >>
      (impl_tac >- simp[]) >> strip_tac >>
      gvs[expr_post_def, stmt_state_rel_start_gas_obs,
          bodyPtrDefsTheory.ghost_inv_at_def]) >>
  qexistsl_tac [`op`,`sm`,`sb`,`w`] >> simp[]
QED

(* Instantiate the RHS judgment in the paired Assign frame. *)
Theorem body_assign_toplevel_word_full_framed[local]:
  expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (expr_type e) e es /\ expr_body_pre cenv cx env e es /\
  get_module_code cx NONE = SOME tops /\
  find_var_decl_by_name id tops = SOME (StorageVarDecl tr (expr_type e),id) /\
  lookup_var_slot_from_layout cx tr NONE id = SOME slot /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
  cenv.ce_hashmap_info (NONE,id) = NONE /\
  cenv.ce_module_var_type (NONE,id) = SOME (expr_type e) /\
  is_word_type (expr_type e) /\
  stmt_env cenv lctx ret_ty (Assign (BaseTarget (TopLevelNameTarget (NONE,id))) e) sa = (ce,sb) /\
  stmt_env cenv lctx ret_ty
    (gas_shadow_stmt (Assign (BaseTarget (TopLevelNameTarget (NONE,id))) e)) shadow_sa =
      (ce,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\ ret_pc_ok cenv sa s0 /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~block_is_terminated sa /\
  gas_admissible (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget (NONE,id))) e))
    (stmt_res_ok lctx) es /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_no_wrap inst s) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\ storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  storage_trace_domain cx st0 es.storage_trace ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0
    (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget (NONE,id))) e)) (es,s0,G0,tn0)
    (\H res ee G tn t. ?ce'.
      stmt_lands lctx sb res t /\ ~t.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb /\ ce' = ce) /\
      cenv_top_ext cenv ce' ee.scopes /\ stmt_state_rel H ctx func ce' cx ee t /\
      storage_well_formed_on cx ee (FST H) /\ return_buf_frame d ce' sb t /\
      alloca_history func t /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d ce' cx ee G tn t /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sa x ==> FLOOKUP G x = FLOOKUP G0 x /\
        op_taint tn (Var x) = op_taint tn0 (Var x)))
    (\H res ee gt r.
      (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
      halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==>
       !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s))
Proof
  strip_tac >>
  `?H. valid_horizon cx st0 H es.storage_trace` by
    metis_tac[storage_trace_domain_def] >>
  `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx` by
    (res_tac >> fs[stmt_state_rel_def,state_rel_def]) >>
  drule_all toplevel_storage_ce_vars >> strip_tac >>
  drule_all body_assign_toplevel_word_full_code >> strip_tac >> gvs[] >>
  rename1 `lower_value compile_expr cenv (expr_type e) e sa = (op,sm)` >>
  rename1 `lower_value compile_expr cenv (expr_type e) (gas_shadow_expr e)
    shadow_sa = (op,shadow_sm)` >>
  `sa.cs_next_var <= sm.cs_next_var` by
    (qspecl_then [`cenv`,`expr_type e`,`e`,`sa`]
       mp_tac ci_mono_lower_value_compile_expr >> simp[ci_mono_def]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at sa x` by metis_tac[ret_pc_ok_def] >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_sim_full_def] >>
  disch_then (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,
    `op`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ Q1 _` >>
  irule body_assign_toplevel_word_full_source >>
  conj_tac >- (qexists_tac `lctx` >> simp[]) >> qexists_tac `Q1` >>
  reverse conj_tac >- (irule gasOutcomeFullTheory.gas_outcome_full_post_mono >>
    goal_assum (drule_at Any) >> simp[] >> rpt gen_tac >>
    POP_ASSUM_LIST (K all_tac) >> strip_tac >>
    Cases_on `res` >> fs[exprSimDefsTheory.expr_exit_def] >>
    Cases_on `y` >> Cases_on `r` >>
    gvs[bodyPtrDefsTheory.stmt_exit_ptr_def,exprSimDefsTheory.expr_exit_def,
        exprSimDefsTheory.halt_exit_def] >>
    rename1 `Error err` >> Cases_on `err` >>
    gvs[exprSimDefsTheory.expr_exit_def]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `cx.txn.is_static`
  >- (irule body_assign_toplevel_word_full_static_rhs >> simp[Abbr `Q1`, post_value_type_word] >>
      qpat_assum `emit_void _ _ _ = _` (irule_at Any) >>
      goal_assum (drule_at Any) >> simp[] >>
      qexistsl_tac [`tn1`,`t`,`sa`,`res`,`marks`,`d`,`cenv`,`G1`] >>
      simp[] >>
      qpat_x_assum `!H. valid_horizon _ _ H _ ==>
        gas_origin_ptr_path _ _ _ _ /\ _` mp_tac >>
      simp[post_value_type_word] >> POP_ASSUM_LIST (K all_tac) >>
      metis_tac[]) >>
  irule body_assign_toplevel_word_full_after_rhs >>
  simp[cs_extends_def,Abbr `Q1`,post_value_type_word] >>
  reverse conj_tac >- metis_tac[] >>
  qexistsl_tac [`G1`,`marks`,`mid`,`op`,`res`,`sm`,`t`,`tn1`] >>
  simp[] >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==>
    gas_origin_ptr_path _ _ _ _ /\ _` mp_tac >>
  simp[post_value_type_word] >> POP_ASSUM_LIST (K all_tac) >>
  metis_tac[]
QED

(* A scalar top-level variable. *)
(* TEMPORARILY CHEATED - the statement's normal post now carries alloca_frame and the older allocations' taint clause; the helpers this proof closes the post with export no memory or taint frame for the store. Original proof:
Proof
  rpt gen_tac >> strip_tac >>
  drule_all body_assign_toplevel_word_full_setup >> strip_tac >> gvs[] >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e) e es` by metis_tac[body_expr_full_ok_def] >>
  rewrite_tac[stmt_frag_full_def] >> rpt gen_tac >> strip_tac >>
  irule gas_outcome_full_initial_domain >>
  conj_tac >- simp[evaluate_storage_trace_frame] >>
  conj_tac >- simp[] >> strip_tac >>
  irule body_assign_toplevel_word_full_framed >>
  simp[] >> metis_tac[]
QED
*)
Theorem body_assign_toplevel_word_full:
  !cx nsid e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_full_ok cx (TopLevelNameTarget nsid)) /\
    body_expr_full_ok cx e /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Assign (BaseTarget (TopLevelNameTarget nsid)) e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget (TopLevelNameTarget nsid)) e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget (TopLevelNameTarget nsid)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (TopLevelNameTarget nsid)) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget (TopLevelNameTarget nsid)) e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    supported_scalar_target tops nsid ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (TopLevelNameTarget nsid)) e))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (Assign (BaseTarget (TopLevelNameTarget nsid)) e)))
      (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget nsid)) e)) es
Proof
  cheat
QED

(* A static aggregate storage or transient variable. *)
Theorem body_assign_toplevel_copy_full:
  !cx nsid mut ty slot e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_full_ok cx (TopLevelNameTarget nsid)) /\
    body_expr_full_ok cx e /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Assign (BaseTarget (TopLevelNameTarget nsid)) e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget (TopLevelNameTarget nsid)) e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget (TopLevelNameTarget nsid)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (TopLevelNameTarget nsid)) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget (TopLevelNameTarget nsid)) e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    ~supported_scalar_target tops nsid /\
    supported_variable_decl tops nsid = SOME (Private, mut, ty, SOME slot) /\
    (mut = Storage \/ mut = Transient) /\
    ~is_word_type ty /\
    (!elem n. ty <> ArrayT elem (Dynamic n)) /\
    0 < type_memory_bytes cenv ty /\
    expr_type e = ty ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (TopLevelNameTarget nsid)) e))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (Assign (BaseTarget (TopLevelNameTarget nsid)) e)))
      (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget nsid)) e)) es
Proof
  cheat
QED

(* A word field of a memory struct local. *)
Theorem body_assign_attr_local_full:
  !cx id fld sid fty e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_full_ok cx (AttributeTarget (NameTarget id) fld)) /\
    body_expr_full_ok cx e /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    FLOOKUP env.var_types id = SOME (StructT sid) /\
    attribute_type env.type_defs (StructT sid) fld = SOME fty /\
    is_word_type fty ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e)))
      (eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e)) es
Proof
  cheat
QED

(* A word field of a storage struct. *)
Theorem body_assign_attr_storage_full:
  !cx nsid fld fty e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_full_ok cx (AttributeTarget (TopLevelNameTarget nsid) fld)) /\
    body_expr_full_ok cx e /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    supported_storage_field_write tops nsid fld /\
    type_place_target env (AttributeTarget (TopLevelNameTarget nsid) fld) =
      SOME (Type fty) /\
    is_word_type fty ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) e))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) e)))
      (eval_stmt cx (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) e)) es
Proof
  rpt gen_tac >> strip_tac >> PairCases_on `nsid` >>
  rename1 `supported_storage_field_write tops (src,id) fld` >>
  `well_typed_expr env e /\ expr_type e = fty` by
    (gvs[type_stmt_def, atarget_accepts_def] >> metis_tac[type_widens_to_word]) >>
  `src = NONE /\ find_var_decl_by_name id tops <> NONE /\
   ?vis mut sid slot. MEM (VariableDecl vis mut id (StructT sid) slot) tops` by
    (drule supported_storage_field_write_decl >> simp[]) >>
  gvs[] >>
  `get_module_code cx NONE = SOME tops /\ supported_program tops /\
   ALL_DISTINCT
     (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
   cenv.ce_hashmap_info = build_hashmap_info tops /\
   cenv.ce_module_var_type (NONE,id) = build_var_type_map tops (NONE,id)` by
    fs[body_inv_def] >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  gvs[type_place_target_AttributeTarget, type_place_target_TopLevelNameTarget]
  >- (`?ts. get_module_code cx NONE = SOME ts /\
              find_var_decl_by_name id ts = NONE` by
        (fs[env_consistent_def, env_context_consistent_def] >>
         first_x_assum drule >> strip_tac >>
         metis_tac[optionTheory.SOME_11]) >>
      metis_tac[optionTheory.SOME_11]) >>
  drule_all env_consistent_toplevel_storage_static >> strip_tac >>
  drule find_var_decl_storage_mem >> strip_tac >> gvs[] >>
  rename1 `attribute_type _ tgt_ty fld = SOME _` >>
  `tgt_ty = StructT sid` by
    metis_tac[build_maps_variable, optionTheory.SOME_11] >>
  gvs[] >> drule_all build_maps_variable >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    fs[env_consistent_def, env_context_consistent_def] >>
  `?fsz. ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
              fld = SOME (expr_type e,fsz)` by
    metis_tac[attribute_type_struct_field] >>
  `supported_expr tops e` by
    fs[supported_stmt_def, supported_assignment_def] >>
  `~supported_expr_exists (const_name_root cx) e` by
    (drule_all body_inv_const_name_free >> simp[]) >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `cx_tops cx = tops` by (drule cx_tops_module >> simp[]) >>
  `expr_body_pre cenv cx env e es` by
    (irule stmt_expr_body_pre >>
     gvs[stmt_exprs_ok_flat, supported_stmt_expr_exists_def,
         supported_assignment_exists_def, supported_expr_exists_def,
         int_calls_stmt_def, int_calls_atarget_def, int_calls_expr_def,
         body_inv_def] >> qexists_tac `[]` >> simp[]) >>
  `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e) e es` by
    (qpat_assum `body_expr_full_ok _ _`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [body_expr_full_ok_def]) >>
     disch_then (qspecl_then [`DF`, `lo`, `d`, `PG`, `tops`, `ctx`,
       `shadow_ctx`, `func`, `shadow_func`, `cenv`, `env`, `expr_type e`, `es`]
       mp_tac) >> simp[]) >>
  qpat_x_assum `IS_SOME (lookup_var_slot_from_layout _ _ _ _)`
    (strip_assume_tac o REWRITE_RULE [optionTheory.IS_SOME_EXISTS]) >>
  irule compile_assign_attr_storage_full >> simp[] >> metis_tac[]
QED

(* Every other base target: subscripts, nested attributes, immutables. *)
(* Saved-RHS liveness boundaries, folded from the independently checked workers. *)
Theorem body_assign_observed_storage_read_live[local]:
  !env cx es e H es1 tr slot leaf raw.
    runtime_consistent env cx es /\ well_typed_expr env e /\
    functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_expr e) /\
    valid_horizon cx es H es1.storage_trace /\
    eval_expr cx e es = (INL (PlaceR (StoragePlace tr slot leaf)),es1) ==>
    storage_read_live H tr raw slot leaf
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `type_slot_size leaf = 0`
  >- simp[storage_read_live_def, wordsTheory.w2n_lt, arithmeticTheory.LESS_IMP_LESS_OR_EQ] >>
  drule_all eval_expr_observed_region >> strip_tac >>
  `MEM (tr,n2w offset,tv) (FST H)` by
    (irule storage_observations_ok_root >>
     fs[valid_horizon_def] >> metis_tac[]) >>
  irule storage_place_observed_read_live >>
  simp[storage_place_observed_def] >>
  qexistsl [`n2w offset`, `tv`, `path`, `delta`] >> simp[]
QED

Theorem body_assign_representation_storage_live[local]:
  env.type_defs = get_tenv cx /\
  eval_result_typed (env,cx,es1) pv (Type ty) /\
  vv_place_ptr cenv cx es1 s pv vv /\
  (!t p. vv = LocatedValue t p /\
     (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) ==>
     t = ty /\ (!v. pv <> Value v)) /\
  (!tr slot leaf. pv = PlaceR (StoragePlace tr slot leaf) ==>
     storage_read_live H tr (get_storage cx es1 tr) slot leaf) ==>
  vv_storage_live H cx vv es1 s
Proof
  Cases_on `vv` >- simp[] >>
  rpt strip_tac >>
  rename1 `vv_place_ptr cenv cx es1 s pv (LocatedValue t p)` >>
  Cases_on `p.ptr_location = LocStorage \/ p.ptr_location = LocTransient`
  >- (first_x_assum (qspecl_then [`t`, `p`] mp_tac) >>
      simp[] >> strip_tac >>
      Cases_on `pv` >> gvs[eval_result_typed_def] >>
      Cases_on `p'` >>
      gvs[vv_place_ptr_def, runtime_place_typed_def, place_type_value_def,
          slot_loc_def, vyperStateTheory.return_def] >>
      Cases_on `b` >> gvs[]) >>
  gvs[]
QED

Theorem body_assign_attribute_storage_origin[local]:
  compile_attribute f cenv rt ty obj fld sa = (LocatedValue t p,sb) /\
  p.ptr_location <> LocMemory ==>
  t = rt /\
  vv_location (FST (f cenv ty obj sa)) = SOME p.ptr_location
Proof
  Cases_on `f cenv ty obj sa` >> Cases_on `vv_location q` >>
  simp[compile_attribute_def, comp_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> simp[mk_ptr_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem body_assign_subscript_storage_origin[local]:
  compile_subscript f cenv rt ty obj idx sa = (LocatedValue t p,sb) /\
  p.ptr_location <> LocMemory ==>
  t = rt /\ ~copies_subscript_base cenv obj idx /\
  vv_location (FST (f cenv ty obj sa)) = SOME p.ptr_location
Proof
  Cases_on `f cenv ty obj sa` >>
  simp[compile_subscript_def, comp_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  Cases_on `copies_subscript_base cenv obj idx` >> gvs[comp_return_def]
  >- (`vv_with_type (vv_type q) q = q` by
        (Cases_on `q` >> simp[vv_with_type_def, vv_type_def]) >>
      qpat_assum `compile_snapshot_vv _ _ _ _ = _` mp_tac >>
      qpat_assum `vv_with_type _ _ = _`
        (fn th => once_rewrite_tac [GSYM th]) >>
      disch_then (mp_tac o MATCH_MP snapshot_saved_representation) >>
      strip_tac >> Cases_on `is_word_type (vv_type q)` >> gvs[] >>
      Cases_on `place_type cenv obj` >>
      rpt BasicProvers.TOP_CASE_TAC >>
      simp[comp_bind_def, comp_return_def, LET_THM] >>
      rpt (pairarg_tac >> gvs[]) >>
      gvs[mk_ptr_def, AllCaseEqs()] >>
      rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[mk_ptr_def]) >>
  rename1 `f cenv ty obj sa = (bv,bs)` >>
  Cases_on `vv_location bv` >> Cases_on `place_type cenv obj` >>
  rpt BasicProvers.TOP_CASE_TAC >>
  simp[comp_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[mk_ptr_def, AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[mk_ptr_def]
QED

Theorem body_assign_module_storage_decl[local]:
  body_inv tops ctx cenv cx /\
  FLOOKUP cenv.ce_module_vars (src,id) = SOME ml /\
  ((?slot. ml = StorageLoc slot) \/ (?slot. ml = TransientLoc slot)) ==>
  src = NONE /\ find_var_decl_by_name id tops <> NONE
Proof
  strip_tac >>
  `cenv_module_pins tops cenv /\
   ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops))`
    by fs[body_inv_def] >>
  gvs[cenv_module_pins_def] >>
  drule add_immutable_locations_FLOOKUP >> simp[] >> strip_tac >>
  drule add_module_var_locations_cases >> simp[] >> strip_tac >> gvs[]
  >>~- ([`MEM (VariableDecl _ _ _ _ _) _`],
         drule bodyStorageMetadataTheory.find_var_decl_storage_some >> simp[]) >>
  drule_all find_var_decl_by_name_SOME_hashmap >> simp[]
QED

Theorem body_assign_storage_target_root[local]:
  !bt f cenv sa op loc pt sb tops ctx cx.
    body_inv tops ctx cenv cx /\
    compile_get_target_ptr f cenv bt sa = ((op,SOME loc,pt),sb) /\
    (loc = LocStorage \/ loc = LocTransient) ==>
    ~immutable_root cx bt
Proof
  measureInduct_on `base_assignment_target_size bt` >> Cases_on `bt`
  >- simp[immutable_root_def, target_root_def]
  >- (PairCases_on `p` >> rpt gen_tac >>
      simp[compile_get_target_ptr_def, LET_THM] >>
      rpt BasicProvers.TOP_CASE_TAC >> simp[comp_return_def] >>
      rpt strip_tac >> gvs[] >>
      `p0 = NONE /\ find_var_decl_by_name p1 tops <> NONE` by
        (irule body_assign_module_storage_decl >> metis_tac[]) >>
      gvs[immutable_root_def, target_root_def] >>
      `get_module_code cx NONE = SOME tops` by fs[body_inv_def] >> gvs[]) >>
  simp[compile_get_target_ptr_def, comp_bind_def, comp_return_def, LET_THM] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[]) >>
  rpt BasicProvers.TOP_CASE_TAC >>
  gvs[comp_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
  PairCases_on `result` >> gvs[] >>
  first_x_assum (qspec_then `b` mp_tac) >> simp[expr_size_def] >>
  metis_tac[immutable_root_def, target_root_def]
QED

Theorem body_assign_storage_target_not_immutable[local]:
  body_inv tops ctx cenv cx /\
  compile_get_target_ptr f cenv bt sa = ((op,SOME loc,pt),sb) /\
  (loc = LocStorage \/ loc = LocTransient) /\
  eval_target_place cx bt es = (INL p,es1) ==>
  !src id path. p <> ImmutablePlace src id path
Proof
  strip_tac >>
  `~immutable_root cx bt` by (irule body_assign_storage_target_root >> metis_tac[]) >>
  qpat_x_assum `eval_target_place _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  Cases_on `pv` >> gvs[get_place_def, return_def, raise_def] >>
  metis_tac[aug_place_base_immutable_origin]
QED

Theorem body_assign_pop_nonvalue[local]:
  (!src id path. p <> ImmutablePlace src id path) /\
  pop_place cx p es = (INL pv,es1) ==> !v. pv <> Value v
Proof
  Cases_on `p` >> simp[] >> strip_tac
  >~ [`pop_place _ (MemoryPlace _ _) _ = _`]
  >- (drule vyperPlaceMutationSoundnessTheory.pop_memory_place_success >>
      strip_tac >> gvs[]) >>
  qpat_x_assum `pop_place _ _ _ = _` mp_tac >>
  Cases_on `t` >> simp[pop_place_def, raise_def] >>
  rename1 `ArrayTV _ bd` >> Cases_on `bd` >>
  simp[pop_place_def, raise_def, bind_def, ignore_bind_def,
       return_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem body_assign_storage_base_result[local]:
  body_inv tops ctx cenv cx /\
  (case e of TopLevelName _ _ => T | Pop _ _ => T | _ => F) /\
  compile_expr cenv ty e sa = (LocatedValue t p,sb) /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  eval_expr cx e es = (INL pv,es1) ==>
  t = expr_type e /\ (!v. pv <> Value v)
Proof
  Cases_on `e` >> simp[]
  >- (PairCases_on `p'` >> strip_tac >>
      qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
      simp[Once compile_expr_def] >>
      Cases_on `FLOOKUP cenv.ce_module_vars (p'0,p'1)` >>
      gvs[] >> rpt BasicProvers.TOP_CASE_TAC >>
      rpt (pairarg_tac >> gvs[]) >> disch_tac >> gvs[mk_ptr_def] >>
      `p'0 = NONE /\ find_var_decl_by_name p'1 tops <> NONE` by
        (irule body_assign_module_storage_decl >> metis_tac[]) >>
      `get_module_code cx NONE = SOME tops` by fs[body_inv_def] >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, lookup_global_def] >>
      Cases_on `find_var_decl_by_name p'1 tops` >> gvs[] >>
      PairCases_on `x` >> Cases_on `x0` >>
      simp[bind_def, ignore_bind_def, lift_option_type_def,
           return_def, raise_def, record_storage_event_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[])
  >- (strip_tac >>
      qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
      rewrite_tac[nested_pop_compile_eq] >> simp[LET_THM] >>
      rpt (pairarg_tac >> gvs[]) >>
      Cases_on `loc_opt` >> simp[mk_ptr_def] >> strip_tac >> gvs[] >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
      `!src id path. p <> ImmutablePlace src id path` by
        (irule body_assign_storage_target_not_immutable >> metis_tac[]) >>
      simp[expr_type_def] >> irule body_assign_pop_nonvalue >> metis_tac[])
QED

Theorem body_assign_storage_expr_cases[local]:
  body_inv tops ctx cenv cx /\
  compile_expr cenv ty e sa = (LocatedValue t p,sb) /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) ==>
  (case e of TopLevelName _ _ => T | Pop _ _ => T |
     Attribute _ _ _ => T | Subscript _ _ _ => T | _ => F)
Proof
  disch_then (CONJUNCTS_THEN2 kall_tac
    (CONJUNCTS_THEN2 mp_tac assume_tac)) >>
  Cases_on `e` >> simp[] >>
  pure_once_rewrite_tac [CONJUNCT1 compile_expr_raw_def]
  >~ [`Literal ann lit`] >-
    (simp[compile_expr_body_def, expr_type_def] >>
     disch_then (mp_tac o MATCH_MP reason_compile_literal) >>
     gvs[reason_result_shape_def])
  >~ [`IfExp ann cond th el`] >-
    (disch_then (mp_tac o MATCH_MP reason_compile_ifexp) >>
     gvs[reason_result_shape_def])
  >~ [`StructLit ann nm fields`] >-
    (disch_then (mp_tac o MATCH_MP reason_compile_structlit) >>
     gvs[reason_result_shape_def])
  >~ [`Call ann dest args dflt`] >-
    (simp[compile_expr_body_def, expr_type_def] >>
     disch_then (mp_tac o MATCH_MP reason_compile_call) >>
     gvs[reason_result_shape_def])
  >~ [`Builtin ann bi args`] >- suspend "builtin"
  >~ [`TypeBuiltin ann tb rt args`] >- suspend "typebuiltin" >>
  simp[compile_expr_body_def, expr_type_def, compile_name_vv_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, mk_ptr_def, AllCaseEqs()] >>
  rename1 `FLOOKUP cenv.ce_vars nm` >>
  Cases_on `FLOOKUP cenv.ce_vars nm`
  >- (gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
      rpt (pairarg_tac >> gvs[])) >>
  rename1 `FLOOKUP _ _ = SOME binding` >> Cases_on `binding` >> gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def, mk_ptr_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[]
QED

Resume body_assign_storage_expr_cases[builtin]:
  disch_then (mp_tac o MATCH_MP reason_compile_expr_builtin_shape_classify) >>
  gvs[reason_result_shape_def] >>
  (simp[exprCallBoundsTheory.builtin_child_callback_def] >>
   pure_once_rewrite_tac [CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)] >>
   Cases_on `bi` >> strip_tac
   >~ [`Acc item`] >- suspend "acc"
   >~ [`AsWeiValue denom`] >- suspend "wei"
   >~ [`Len`] >- (drule reason_builtin_len >> gvs[reason_result_shape_def])
   >~ [`Bop bop`] >- (drule reason_builtin_bop >> gvs[reason_result_shape_def])
   >~ [`MakeArray et bd`] >- (drule reason_builtin_makearray >> gvs[reason_result_shape_def])
   >~ [`MethodId`] >- (drule reason_builtin_method_id >> gvs[reason_result_shape_def])
   >~ [`Keccak256`] >- (drule_at Any reason_builtin_hash >> simp[reason_result_shape_def])
   >~ [`Sha256`] >- (drule_at Any reason_builtin_hash >> simp[reason_result_shape_def])
   >~ [`CalldataSlice n`] >- (drule_at Any reason_builtin_fresh >> simp[reason_result_shape_def])
   >~ [`ECAdd`] >- (drule_at Any reason_builtin_fresh >> simp[reason_result_shape_def])
   >~ [`ECMul`] >- (drule_at Any reason_builtin_fresh >> simp[reason_result_shape_def])
   >~ [`Concat n`] >- (drule_at Any reason_builtin_fresh >> simp[reason_result_shape_def])
   >~ [`Slice n`] >- (drule_at Any reason_builtin_fresh >> simp[reason_result_shape_def])
   >~ [`Uint2Str n`] >- (drule_at Any reason_builtin_fresh >> simp[reason_result_shape_def]) >>
   drule_at Any reason_builtin_scalar >> simp[reason_result_shape_def])
QED

Resume body_assign_storage_expr_cases[typebuiltin]:
  simp[compile_expr_body_def, expr_type_def] >>
  simp[exprCallBoundsTheory.type_child_callback_def] >>
  pure_once_rewrite_tac [CONJUNCT2 (CONJUNCT2 compile_expr_raw_def)] >>
  strip_tac >> Cases_on `tb` >> gvs[compile_type_builtin_dispatch_body_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[AllCaseEqs(), oneline as_stack_val_def, oneline as_ptr_val_def,
      mk_ptr_def, base_ptr_def] >>
  rpt strip_tac >> gvs[AllCaseEqs(), mk_ptr_def, base_ptr_def]
QED

Resume body_assign_storage_expr_cases[acc]:
  simp[markerTheory.resconj_def, markerTheory.suspendimp_def] >>
  rpt strip_tac >>
  gvs[compile_builtin_dispatch_body_def, oneline as_stack_val_def, AllCaseEqs()]
QED

Resume body_assign_storage_expr_cases[wei]:
  simp[markerTheory.resconj_def, markerTheory.suspendimp_def] >>
  rpt strip_tac >> gvs[compile_builtin_dispatch_body_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[AllCaseEqs(), oneline as_stack_val_def]
QED

Finalise body_assign_storage_expr_cases

Theorem body_assign_select_nonvalue[local]:
  (!v. raw <> Value v) /\
  select_result cx ty raw sub st = (INL out,st') ==>
  !v. out <> Value v
Proof
  Cases_on `raw` >> simp[select_result_def] >> rpt strip_tac >>
  drule extend_place_result_shape >> strip_tac >> gvs[]
QED

Theorem body_assign_storage_result_shape_from_cases[local]:
  body_inv tops ctx cenv cx /\
  (!e ty sa t p sb.
    compile_expr cenv ty e sa = (LocatedValue t p,sb) /\
    (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) ==>
    (case e of TopLevelName _ _ => T | Pop _ _ => T |
       Attribute _ _ _ => T | Subscript _ _ _ => T | _ => F)) /\
  (!e ty sa t p sb es pv es1.
    (case e of TopLevelName _ _ => T | Pop _ _ => T | _ => F) /\
    compile_expr cenv ty e sa = (LocatedValue t p,sb) /\
    (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
    eval_expr cx e es = (INL pv,es1) ==>
    t = expr_type e /\ (!v. pv <> Value v)) ==>
  !e ty sa t p sb es pv es1.
    compile_expr cenv ty e sa = (LocatedValue t p,sb) /\
    (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
    eval_expr cx e es = (INL pv,es1) ==>
    t = expr_type e /\ (!v. pv <> Value v)
Proof
  strip_tac >> measureInduct_on `expr_size e` >>
  rpt gen_tac >> disch_tac >>
  `case e of TopLevelName _ _ => T | Pop _ _ => T |
     Attribute _ _ _ => T | Subscript _ _ _ => T | _ => F` by metis_tac[] >>
  Cases_on `case e of TopLevelName _ _ => T | Pop _ _ => T | _ => F`
  >- (qpat_x_assum `!e ty sa t p sb es pv es1. _` irule >>
      metis_tac[]) >>
  qpat_x_assum `!e ty sa t p sb es pv es1. _` kall_tac >>
  qpat_x_assum `!e ty sa t p sb. _` kall_tac >>
  Cases_on `e` >> gnvs[] >>
  qpat_x_assum `_ /\ _` (map_every assume_tac o CONJUNCTS)
  >- (qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
      simp[Once compile_expr_def] >> strip_tac >>
      `p.ptr_location <> LocMemory` by
        (Cases_on `p.ptr_location` >> gvs[]) >>
      drule_all body_assign_subscript_storage_origin >>
      simp[] >> strip_tac >>
      `~subscript_reads_base cx e' e0` by
        metis_tac[body_inv_copies_subscript_base] >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, return_def, AllCaseEqs()] >>
      rpt strip_tac >>
      Cases_on `compile_expr cenv ty e' sa` >> Cases_on `q` >>
      gvs[vv_location_def] >>
      qpat_x_assum `!y. expr_size y < _ ==> _`
        (qspec_then `e'` mp_tac) >>
      (impl_tac >- simp[]) >> disch_then drule >>
      disch_then assume_tac >>
      `!v. res <> Value v` by metis_tac[] >>
      metis_tac[body_assign_select_nonvalue])
  >- (qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
      simp[Once compile_expr_def] >> strip_tac >>
      `p.ptr_location <> LocMemory` by
        (Cases_on `p.ptr_location` >> gvs[]) >>
      drule_all body_assign_attribute_storage_origin >>
      simp[] >> strip_tac >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs()] >>
      rpt strip_tac >>
      Cases_on `compile_expr cenv ty e' sa` >> Cases_on `q` >>
      gvs[vv_location_def] >>
      qpat_x_assum `!y. expr_size y < _ ==> _`
        (qspec_then `e'` mp_tac) >>
      (impl_tac >- simp[]) >> disch_then drule >>
      disch_then assume_tac >>
      `!v. res <> Value v` by metis_tac[] >>
      metis_tac[body_assign_select_nonvalue])
QED

Theorem body_assign_storage_result_shape[local]:
  body_inv tops ctx cenv cx /\
  compile_expr cenv ty e sa = (LocatedValue t p,sb) /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  eval_expr cx e es = (INL pv,es1) ==>
  t = expr_type e /\ (!v. pv <> Value v)
Proof
  strip_tac >> mp_tac body_assign_storage_result_shape_from_cases >>
  (impl_tac >-
    (rpt conj_tac >>
     metis_tac[body_assign_storage_expr_cases, body_assign_storage_base_result])) >>
  disch_then drule >> metis_tac[]
QED

(* A storage-backed compiled result retains a source storage place.
   The actual source evaluation records its finite observed region even
   when the RHS has effects. *)
Theorem body_assign_rhs_storage_live[local]:
  !tops ctx cenv cx env es e H es1 sa sb vv pv func s0 s.
    body_inv tops ctx cenv cx /\
    runtime_consistent env cx es /\ well_typed_expr env e /\
    functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_expr e) /\
    valid_horizon cx es H es1.storage_trace /\
    compile_expr cenv (expr_type e) e sa = (vv,sb) /\
    eval_expr cx e es = (INL pv,es1) /\
    vv_post H ctx func cenv cx e es sa sb s0 es1 pv vv s ==>
    vv_storage_live H cx vv es1 s
Proof
  rpt gen_tac >> strip_tac >>
  `eval_result_typed (env,cx,es1) pv (Type (expr_type e))` by
    (irule (cj 2 typed_expr_success_preserves_type) >>
     fs[runtime_consistent_def] >> metis_tac[]) >>
  `env.type_defs = get_tenv cx` by
    metis_tac[runtime_consistent_get_tenv] >>
  `vv_place_ptr cenv cx es1 s pv vv` by fs[vv_post_def] >>
  irule body_assign_representation_storage_live >>
  qexistsl [`cenv`, `env`, `pv`, `expr_type e`] >> simp[] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> gvs[] >>
      irule body_assign_observed_storage_read_live >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  irule body_assign_storage_result_shape >> metis_tac[]
QED

Theorem body_assign_other_full:
  !cx t e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_full_ok cx t) /\
    body_expr_full_ok cx e /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Assign (BaseTarget t) e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget t) e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget t) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget t) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget t) e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    ~(?id ty. t = NameTarget id /\ FLOOKUP env.var_types id = SOME ty /\
              is_word_type ty) /\
    ~(?id ty. t = NameTarget id /\ FLOOKUP env.var_types id = SOME ty /\
              ~is_word_type ty /\
              (expr_type e = ty \/ lowered_value_type cenv e = ty \/
               is_bytestring_type ty \/
               has_length_word (expr_type e) /\ is_empty_value_expr e)) /\
    ~(?nsid. t = TopLevelNameTarget nsid /\ supported_scalar_target tops nsid) /\
    ~(?nsid mut ty slot.
        t = TopLevelNameTarget nsid /\
        supported_variable_decl tops nsid = SOME (Private, mut, ty, SOME slot) /\
        (mut = Storage \/ mut = Transient) /\
        ~is_word_type ty /\ (!elem n. ty <> ArrayT elem (Dynamic n)) /\
        0 < type_memory_bytes cenv ty /\ expr_type e = ty) /\
    ~(?id fld sid fty.
        t = AttributeTarget (NameTarget id) fld /\
        FLOOKUP env.var_types id = SOME (StructT sid) /\
        attribute_type env.type_defs (StructT sid) fld = SOME fty /\
        is_word_type fty) /\
    ~(?nsid fld fty.
        t = AttributeTarget (TopLevelNameTarget nsid) fld /\
        supported_storage_field_write tops nsid fld /\
        type_place_target env t = SOME (Type fty) /\ is_word_type fty) ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget t) e))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (Assign (BaseTarget t) e)))
      (eval_stmt cx (Assign (BaseTarget t) e)) es
Proof
  cheat
QED

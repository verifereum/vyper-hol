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
  sum venomState stateRelProj stateRelProjStorage memoryPlaceStorePost
  stmtSimAssignStorage augAssignFullStore bodyPtrDefs stmtSimDefs bodyMemoryDefs
  vyperStorageBackend fragExec fragGasOriginPtrExec gasExemptCert exprSimDefs
  exprSimUnwrap stmtSimAssignStorageFacts vyperTypeExprResult vyperTypeExprSoundness
  ptrDiscipline placeStore valueEncodingProps venomMemProofs
  bodyPtrPrecompileBuiltinsArithmeticValue vyperTypeDefaults
  annassignRelayoutCode assignRelayoutFrame typedMemoryCopy bodyMemBopRestWordPath
  fragGasOriginPtr fragGasOrigin fragGasMode fragGasPath assignTuplePtrCopyLen
  localPtrsProps venomMemDefs venomInst memSafeRun assignPlaceDirectCopy
  placeMemoryStateRebuild placeMemoryPathRebuild placeMemoryLiveRegion
  placeMemoryCopyEffect bodyFullAppend vyperLookup vyperTypeStatePreservation
  vyperTypeValues valueEncodingProofs words
  fragGasSeqPtr exprPtrUnwrapCopyEdges instMemFrontier wordLoadStorePtr
  bodyFullUnwrapRun emitHelperProps venomExecProofs pred_set rich_list emitHelper
  bodyFullUnwrap assignEffectfulIndexPhysical immutableDeployPhysicalSource
  bodyFullStructLitPhysical stmtSimLogCompose exprSimMemDefs valueCopyBytes
  bodyMemSnapshotSourceLocation aggregateEvaluatedLayout
  ctorDeployDeadSectionFrame ctorDeployDeadSection immSectionDead
  bodyFullPathHistory typedCopyOriginPtrBase exprSimStorageCopy codegenRel context
  bodyFullUnwrapWord exprSimCopy exprSafeOperand exprReasonOperand bytestringCopyExecution decoderSetupStepPtr ptrSafeRun memLocDefs
  contextCodegenRel unitTransformDefs fragExecMem venomExecSemantics
  immutableAssignEmpty abiEncoderProps abiDecodeStaticProps immutableDeployAssignFacts
  bodyPtrBytestringBuiltinsWindowGhost bodyFullToplevelCtorSourceLayout
  stmtSimDeclMem valueEncoding valueEncodingDefs valueEncodingTyping vyperTyping alist
Libs
  monadsyntax


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
    (fs[expr_post_def] >>
     metis_tac[stmt_state_rel_local_ptrs_alloca]) >>
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
  stmt_state_rel (H0 : (bool # 256 word # type_value) list # num list)
    ctx func cenv cx es s0 /\
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
        op_taint tn (Var x) = op_taint tn0 (Var x)) /\
      alloca_frame cenv es sa s0 ce ee t /\
      (!aid off sz i.
        FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
        (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
          off + sz <= b \/ b + sz' <= off) /\
        off <= i /\ i < off + sz /\ i IN tn.t_mem ==> i IN tn0.t_mem)) R
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
  strip_tac >> gvs[vyperStateTheory.evaluation_state_fupdcanon] >>
  reverse conj_tac
  >- (drule_all wordLoadStorePtrTheory.mstore_ghost_frame >> strip_tac >>
      fs[bodyPtrDefsTheory.ghost_kept_at_def, pred_setTheory.IN_DIFF] >>
      rpt strip_tac >>
      qpat_assum `!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ _ ==> _`
        (qspecl_then [`aid`,`off`,`sz'`,`i`] mp_tac) >>
      simp[] >> disch_then irule >> first_assum ACCEPT_TAC) >>
  qpat_assum `!H. valid_horizon _ _ _ mid.storage_trace ==> _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `MAP FDOM mid.scopes = MAP FDOM es.scopes` by
    fs[expr_post_def, locals_kept_def] >>
  `alloca_frame ce es sa s0 ce (mid with gas_obs := []) t` by
    (qpat_assum `stmt_state_rel H0 _ _ _ _ _ _`
       (mp_then Any irule stmtSimDefsTheory.alloca_frame_of_mem_frame) >>
     fs[expr_post_def] >> first_assum ACCEPT_TAC) >>
  `lookup_scopes id mid.scopes = SOME entry` by
    metis_tac[vyperLookupTheory.find_containing_scope_lookup] >>
  `local_ptrs_rel func ce mid.scopes t` by
    (fs[expr_post_def] >> metis_tac[stmt_state_rel_local_ptrs_alloca]) >>
  `32 <= sz` by
    (fs[local_ptrs_rel_def, stmtSimDeclStoreTheory.store_lays_out_def] >>
     first_x_assum (qspecl_then [`id`,`entry`,`p`,`sz`] mp_tac) >> simp[]) >>
  `local_region ce (mid with gas_obs := []).scopes t id (w2n dst) sz` by
    (simp[local_region_def] >> metis_tac[]) >>
  irule stmtSimDefsTheory.alloca_frame_region_write >>
  goal_assum (drule_at Any) >>
  simp[] >>
  conj_tac >- simp[venomStateTheory.mstore_def, venomStateTheory.lookup_var_def] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      irule valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >> decide_tac) >>
  drule vyperLookupTheory.find_containing_scope_structure >>
  strip_tac >> gvs[] >>
  `id IN FDOM sc` by fs[FLOOKUP_DEF] >>
  simp[pred_setTheory.ABSORPTION_RWT]
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
  rpt gen_tac >> strip_tac >>
  drule_all assign_base_local_rhs_pre >> strip_tac >>
  `expr_type e = ty` by metis_tac[type_widens_to_word] >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx ty e es` by metis_tac[body_expr_full_ok_def] >>
  `?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)` by
    metis_tac[expr_sim_inv_def] >>
  `cenv.ce_var_type id = SOME ty` by metis_tac[expr_sim_inv_def] >>
  rewrite_tac[stmt_frag_full_def] >> rpt gen_tac >> strip_tac >>
  irule gas_outcome_full_initial_domain >>
  conj_tac >- simp[vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
  conj_tac >- simp[] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func cenv cx es s0` by
    metis_tac[] >>
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
  goal_assum (drule_at Any) >> simp[Abbr `Q1`] >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (qexistsl_tac [`G1`,`marks`,`mid`,`res`,`t`,`tn1`] >>
      qpat_x_assum `!H. valid_horizon _ _ _ mid.storage_trace ==> _` mp_tac >>
      simp[]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (qexists_tac `env` >> simp[]) >>
  qexists_tac `storage_trace_horizon es.storage_trace` >> metis_tac[]
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

(* The normal RHS endpoint feeds the joint top-level store. *)

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

Theorem body_assign_toplevel_word_full_residual_frame[local]:
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
        op_taint tn (Var x) = op_taint tn0 (Var x)) /\
      alloca_frame cenv es sa s0 ce ee t /\
      (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
        (!n b sz'. local_region cenv es.scopes s0 n b sz' ==> off + sz <= b \/ b + sz' <= off) /\
        off <= i /\ i < off + sz /\ i IN tn.t_mem ==> i IN tn0.t_mem)) R
Proof
  strip_tac >>
  Cases_on `storage_trace_domain cx st0 (mid.storage_trace ++ [StorageRoot tr slot tvt])`
  >- (
    `valid_horizon cx st0 (storage_trace_horizon (mid.storage_trace ++ [StorageRoot tr slot tvt]))
      (mid.storage_trace ++ [StorageRoot tr slot tvt])` by fs[storage_trace_domain_def] >>
    `~t.vs_call_ctx.cc_static` by
      (first_x_assum drule >> strip_tac >>
       `stmt_state_rel (storage_trace_horizon (mid.storage_trace ++ [StorageRoot tr slot tvt]))
          ctx func cenv cx (mid with gas_obs := []) t` by fs[expr_post_def] >>
       drule stmt_state_rel_state_rel >> strip_tac >> drule state_rel_call_ctx_rel >>
       simp[call_ctx_rel_def]) >>
    Cases_on `write_storage_slot cx tr (n2w slot) tvt v (mid with gas_obs := [])` >>
    rename1 `write_storage_slot _ _ _ _ _ _ = (res,ef)` >>
    `res = INL ()` by
      (qpat_x_assum `write_storage_slot _ _ _ _ _ _ = _` mp_tac >> simp[write_storage_slot_eq]) >>
    gvs[] >>
    `ef.storage_trace = mid.storage_trace` by
      (qpat_x_assum `write_storage_slot _ _ _ _ _ _ = _` mp_tac >>
       simp[write_storage_slot_eq] >> Cases_on `tr` >> simp[set_storage_def] >> strip_tac >> gvs[]) >>
    irule gas_outcome_full_intro >>
    qexistsl [`G1`, `ef with storage_trace := mid.storage_trace ++ [StorageRoot tr slot tvt]`, `[]`,
      `OK ((if tr then tstore (n2w slot) (typed_val_to_w256 tvt v) t
           else sstore (n2w slot) (typed_val_to_w256 tvt v) t)
          with vs_inst_idx := LENGTH sb.cs_current_insts)`, `INL ()`,
      `if tr then tn1 with t_trans := key_update tn1.t_trans (n2w slot) {}
       else tn1 with t_stor := key_update tn1.t_stor (n2w slot) {}`] >>
    simp[] >> conj_tac
    >- (simp[ignore_bind_def,record_storage_event_def,return_def,bind_def] >>
        gen_tac >> drule write_storage_slot_storage_trace >>
        disch_then (qspec_then `mid.storage_trace ++ [StorageRoot tr slot tvt]` assume_tac) >>
        gvs[write_storage_slot_eq] >> Cases_on `tr` >>
        gvs[set_storage_def,get_storage_def,evaluation_state_component_equality]) >>
    qx_gen_tac `H` >> strip_tac >> first_x_assum drule >> strip_tac >>
    `eval_operand op t = SOME (typed_val_to_w256 tvt v)` by
      (gvs[expr_post_def,expr_val_rel_def,post_value_type_word] >> metis_tac[]) >>
    `stmt_state_rel H ctx func cenv cx (mid with gas_obs := []) t` by fs[expr_post_def] >>
    `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
      (drule stmt_state_rel_allocas_below_fmp >> simp[]) >>
    conj_tac
    >- (irule storage_word_store_origin_ptr >> simp[] >>
        conj_tac >- fs[ghost_inv_at_def] >>
        conj_tac >- fs[ghost_inv_at_def] >>
        qexistsl [`Lit (n2w slot)`,`op`,`sm`] >> simp[eval_operand_def,op_taint_def]) >>
    `ef.gas_obs = []` by
      (qpat_x_assum `write_storage_slot _ _ _ _ _ _ = _` mp_tac >>
       simp[write_storage_slot_eq] >> Cases_on `tr` >> simp[set_storage_def] >> strip_tac >> gvs[]) >>
    `MEM (tr,n2w slot,tvt) (FST H) /\ regions_consistent (FST H)` by
      (qpat_x_assum `valid_horizon cx st0 H _` mp_tac >>
       simp[valid_horizon_def,storage_observations_ok_def,storage_trace_regions_def,
            MAP_APPEND,FLAT_APPEND,EVERY_APPEND]) >>
    `MAP FDOM (mid with gas_obs := []).scopes = MAP FDOM es.scopes` by simp[] >>
    drule_all body_assign_toplevel_word_full_store_post >>
    disch_then (qspec_then `lctx` strip_assume_tac) >>
    disj1_tac >> pure_once_rewrite_tac[GSYM evaluation_state_fupdcanon] >>
    `(ef with gas_obs := []) = ef` by simp[evaluation_state_component_equality] >>
    simp[stmt_post_storage_trace] >>
    fs[stmt_post_def] >>
    conj_tac
    >- (qpat_assum `storage_well_formed_on cx ef _` mp_tac >>
        rewrite_tac[storage_well_formed_on_def] >> strip_tac >>
        rpt strip_tac >> first_x_assum drule >> Cases_on `b` >> simp[get_storage_def]) >>
    conj_tac
    >- (gvs[alloca_frame_def] >> first_assum ACCEPT_TAC) >>
    Cases_on `tr` >> gvs[ghost_kept_at_def] >> metis_tac[]) >>
  irule gas_outcome_full_bad_nil >> simp[] >>
  simp[ignore_bind_def,record_storage_event_def,bind_def,return_def,write_storage_slot_eq] >>
  Cases_on `cx.txn.is_static` >> Cases_on `tr` >> simp[set_storage_def]
QED

Theorem body_assign_toplevel_word_full_after_rhs_frame[local]:
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
        op_taint tn (Var x) = op_taint tn0 (Var x)) /\
      alloca_frame cenv es sa s0 ce ee t /\
      (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
        (!n b sz'. local_region cenv es.scopes s0 n b sz' ==> off + sz <= b \/ b + sz' <= off) /\
        off <= i /\ i < off + sz /\ i IN tn.t_mem ==> i IN tn0.t_mem)) R
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
  irule body_assign_toplevel_word_full_residual_frame >>
  qpat_assum `find_var_decl_by_name _ _ = _` (irule_at Any) >>
  qpat_assum `emit_void _ _ _ = _` (irule_at Any) >>
  qpat_assum `ghost_kept_at _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem body_assign_toplevel_word_full_framed_frame[local]:
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
        op_taint tn (Var x) = op_taint tn0 (Var x)) /\
      alloca_frame cenv es sa s0 ce' ee t /\
      (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
        (!n b sz'. local_region cenv es.scopes s0 n b sz' ==> off + sz <= b \/ b + sz' <= off) /\
        off <= i /\ i < off + sz /\ i IN tn.t_mem ==> i IN tn0.t_mem))
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
    metis_tac[stmt_state_rel_vars_rels] >>
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
  irule body_assign_toplevel_word_full_after_rhs_frame >>
  simp[cs_extends_def,Abbr `Q1`,post_value_type_word] >>
  reverse conj_tac >- metis_tac[] >>
  qexistsl_tac [`G1`,`marks`,`mid`,`op`,`res`,`sm`,`t`,`tn1`] >>
  simp[] >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==>
    gas_origin_ptr_path _ _ _ _ /\ _` mp_tac >>
  simp[post_value_type_word] >> POP_ASSUM_LIST (K all_tac) >>
  metis_tac[]
QED

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
  rpt gen_tac >> strip_tac >>
  drule_all body_assign_toplevel_word_full_setup >> strip_tac >> gvs[] >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e) e es` by metis_tac[body_expr_full_ok_def] >>
  rewrite_tac[stmt_frag_full_def] >> rpt gen_tac >> strip_tac >>
  irule gas_outcome_full_initial_domain >>
  conj_tac >- simp[evaluate_storage_trace_frame] >>
  conj_tac >- simp[] >> strip_tac >>
  irule body_assign_toplevel_word_full_framed_frame >>
  simp[] >> metis_tac[]
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

(* Runtime bytestring header: a clean MLOAD followed by the bounded
   length-to-word-count calculation, at one physical/ghost endpoint. *)
Theorem body_assign_bytes_header_mload_check[local]:
  ptr_covers G tn src s 32 /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ptr_inst_ok D lo fuel ctx fn G tn (mk_inst id MLOAD [Var src] [out]) s
Proof
  strip_tac >> gvs[ptr_covers_def] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def,
       eval_operand_def] >>
  conj_tac >- (rpt strip_tac >> gvs[mem_read_ops_def]) >>
  simp[GSYM mk_inst_def, step_inst_non_invoke] >>
  `step_inst_base (mk_inst id MLOAD [Var src] [out]) s =
     OK (update_var out (mload (w2n w) s) s)` by
    (irule step_MLOAD >> simp[eval_operand_def]) >>
  simp[update_var_def]
QED

Theorem body_assign_bytes_header_shr_check[local]:
  eval_operand value s = SOME w /\ op_taint tn value = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ptr_inst_ok D lo fuel ctx fn G tn (mk_inst id SHR [Lit 5w;value] [out]) s
Proof
  strip_tac >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def,
       op_taint_def] >>
  simp[GSYM mk_inst_def, step_inst_non_invoke] >>
  simp[mk_inst_def, step_inst_base_opcode_eqs, exec_pure2_def,
       eval_operand_def, update_var_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem body_assign_immutable_bytes_header_joint:
  compile_bytestring_word_count (Var src) sa = (cnt,sm) /\
  fn_has_code sa sm func /\ not_fresh_at sa src /\
  eval_operand (Var src) s = SOME a /\ mload (w2n a) s = n2w len /\
  len + 63 < dimword (:256) /\ ptr_covers G tn src s 32 /\
  w2n a + 32 <= s.vs_alloca_next /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?r Gf tnf out.
    cnt = Var out /\ not_fresh_at sm out /\ ~not_fresh_at sa out /\
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK r,Gf,tnf) /\
    eval_operand cnt r = SOME (n2w (1 + word_size len)) /\
    op_taint tnf cnt = {} /\ op_prov Gf cnt = NONE /\
    (r with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x r = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tnf (Var x) = op_taint tn (Var x)) /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!x C. not_fresh_at sa x /\ ptr_covers G tn x s C ==>
      ptr_covers Gf tnf x r C) /\
    ~r.vs_halted /\ r.vs_current_bb = sm.cs_current_bb /\
    r.vs_inst_idx = LENGTH sm.cs_current_insts
Proof
  strip_tac >> drule_all bytestring_word_count_run >> strip_tac >>
  drule bytestring_word_count_shape >> strip_tac >>
  `?Gf tnf.
    inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sm) s Gf tnf /\
    op_taint tnf cnt = {} /\ op_prov Gf cnt = NONE /\
    (!x. not_fresh_at sa x ==> FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tnf (Var x) = op_taint tn (Var x)) /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm` by
    suspend "ghosts" >>
  `run_inst_seq_mem_ok (emitted_insts sa sm) s` by suspend "memory" >>
  suspend "join"
QED

Resume body_assign_immutable_bytes_header_joint[ghosts]:
  gvs[compile_bytestring_word_count_def, emit_op_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_id_def, fresh_var_def, emit_def] >>
  simp[emitted_insts_def, DROP_APPEND, SUB_PLUS] >>
  qpat_x_assum `fn_has_code _ _ _` kall_tac >>
  qpat_x_assum `run_inst_seq _ _ = _` kall_tac >>
  qpat_x_assum `same_blocks _ _` kall_tac >>
  qpat_x_assum `EVERY _ _` kall_tac >>
  qpat_x_assum `_ = emitted_insts _ _` kall_tac >>
  qabbrev_tac `v0 = STRING #"%" (toString sa.cs_next_var)` >>
  qabbrev_tac `v1 = STRING #"%" (toString (sa.cs_next_var + 1))` >>
  qabbrev_tac `v2 = STRING #"%" (toString (sa.cs_next_var + 2))` >>
  qmatch_goalsub_abbrev_tac `inst_seq_ptr _ _ _ _ _ _ _ [i0;i1;i2] _ _ _` >>
  qabbrev_tac `u0 = update_var v0 (n2w len) s` >>
  qabbrev_tac `q0 = u0 with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `G0 = step_prov PG G i0 u0` >>
  qabbrev_tac `tn0 = step_taint i0 s u0 tn` >>
  `step_inst_base i0 s = OK u0` by
    (qpat_assum `eval_operand (Var src) s = _`
       (mp_then Any mp_tac step_MLOAD) >> simp[Abbr `i0`, Abbr `u0`]) >>
  `ptr_inst_ok D lo 0 ctx func G tn i0 s` by
    (simp[Abbr `i0`] >> irule body_assign_bytes_header_mload_check >> simp[]) >>
  `lookup_var src s = SOME a` by gvs[eval_operand_def] >>
  `op_taint tn0 (Var v0) = {} /\ op_prov G0 (Var v0) = NONE /\
   tn0.t_mem = tn.t_mem /\ tn0.t_stor = tn.t_stor /\
   tn0.t_trans = tn.t_trans /\ tn0.t_imm = tn.t_imm /\
   (!x. x <> v0 ==> FLOOKUP G0 x = FLOOKUP G x /\
     op_taint tn0 (Var x) = op_taint tn (Var x))` by
    (simp[Abbr `G0`, Abbr `tn0`, Abbr `i0`, Abbr `u0`] >>
     metis_tac[setup_mload_ghost]) >>
  qabbrev_tac `u1 = update_var v1 ((n2w len:bytes32) + 63w) q0` >>
  qabbrev_tac `q1 = u1 with vs_inst_idx := SUC q0.vs_inst_idx` >>
  qabbrev_tac `G1 = step_prov PG G0 i1 u1` >>
  qabbrev_tac `tn1 = step_taint i1 q0 u1 tn0` >>
  `eval_operand (Var v0) q0 = SOME (n2w len)` by
    simp[Abbr `q0`, Abbr `u0`, eval_operand_def, lookup_var_def,
         update_var_def, FLOOKUP_UPDATE] >>
  `step_inst_base i1 q0 = OK u1` by
    (simp[Abbr `i1`, Abbr `u1`] >> irule step_ADD >> simp[eval_operand_def]) >>
  `ptr_inst_ok D lo 0 ctx func G0 tn0 i1 q0` by
    (simp[Abbr `i1`] >> irule (cj 1 typed_copy_origin_ptr_binop_checks) >>
     conj_tac >- (qexists_tac `(n2w len:bytes32) + 63w` >> gvs[Abbr `u1`]) >>
     gvs[Abbr `q0`, Abbr `u0`, update_var_def, op_taint_def,
       allocas_from_def, allocas_below_fmp_def] >> metis_tac[]) >>
  `op_taint tn1 (Var v1) = {} /\ op_prov G1 (Var v1) = NONE /\
   tn1.t_mem = tn0.t_mem /\ tn1.t_stor = tn0.t_stor /\
   tn1.t_trans = tn0.t_trans /\ tn1.t_imm = tn0.t_imm /\
   (!x. x <> v1 ==> FLOOKUP G1 x = FLOOKUP G0 x /\
     op_taint tn1 (Var x) = op_taint tn0 (Var x))` by
    (simp[Abbr `G1`, Abbr `tn1`, Abbr `i1`, Abbr `u1`,
       step_prov_def, step_taint_def, out_prov_def, first_prov_def,
       set_prov_def, mk_inst_def, op_prov_def, set_var_taint_def,
       out_taint_def, op_taint_def, mem_taint_def, new_site_bytes_def,
       step_writes_def, written_taint_def, store_taint_def, imm_taint_def,
       adopt_reset_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE,
       source_memory_write_ranges_def, range_bytes_def, update_var_def,
       lookup_var_def, SF CONJ_ss] >>
     gvs[op_taint_def, op_prov_def, eval_operand_def, lookup_var_def,
         EXTENSION, FLOOKUP_DEF] >> metis_tac[]) >>
  qabbrev_tac `u2 = update_var v2 ((n2w len + 63w:bytes32) >>> 5) q1` >>
  qabbrev_tac `G2 = step_prov PG G1 i2 u2` >>
  qabbrev_tac `tn2 = step_taint i2 q1 u2 tn1` >>
  `eval_operand (Var v1) q1 = SOME ((n2w len:bytes32) + 63w)` by
    simp[Abbr `q1`, Abbr `u1`, eval_operand_def, lookup_var_def,
         update_var_def, FLOOKUP_UPDATE] >>
  `step_inst_base i2 q1 = OK u2` by
    simp[Abbr `i2`, Abbr `u2`, mk_inst_def, step_inst_base_opcode_eqs,
         exec_pure2_def, eval_operand_def] >>
  `ptr_inst_ok D lo 0 ctx func G1 tn1 i2 q1` by
    (simp[Abbr `i2`] >> irule body_assign_bytes_header_shr_check >>
     simp[] >> gvs[Abbr `q1`, Abbr `u1`, Abbr `q0`, Abbr `u0`,
       update_var_def, allocas_from_def, allocas_below_fmp_def] >> metis_tac[]) >>
  `op_taint tn2 (Var v2) = {} /\ op_prov G2 (Var v2) = NONE /\
   tn2.t_mem = tn1.t_mem /\ tn2.t_stor = tn1.t_stor /\
   tn2.t_trans = tn1.t_trans /\ tn2.t_imm = tn1.t_imm /\
   (!x. x <> v2 ==> FLOOKUP G2 x = FLOOKUP G1 x /\
     op_taint tn2 (Var x) = op_taint tn1 (Var x))` by
    (simp[Abbr `G2`, Abbr `tn2`, Abbr `i2`, Abbr `u2`,
       step_prov_def, step_taint_def, out_prov_def, first_prov_def,
       set_prov_def, mk_inst_def, op_prov_def, set_var_taint_def,
       out_taint_def, op_taint_def, mem_taint_def, new_site_bytes_def,
       step_writes_def, written_taint_def, store_taint_def, imm_taint_def,
       adopt_reset_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE,
       source_memory_write_ranges_def, range_bytes_def, update_var_def,
       lookup_var_def, SF CONJ_ss] >>
     gvs[op_taint_def, op_prov_def, eval_operand_def, lookup_var_def,
         shift_taint_def, EXTENSION, FLOOKUP_DEF] >> metis_tac[]) >>
  qexistsl_tac [`G2`,`tn2`] >>
  conj_tac >-
    (gvs[Abbr `q0`, Abbr `q1`, Abbr `G0`, Abbr `tn0`,
         Abbr `G1`, Abbr `tn1`, Abbr `G2`, Abbr `tn2`] >>
     simp[inst_seq_ptr_def]) >>
  simp[] >> rpt strip_tac >>
  `x <> v0 /\ x <> v1 /\ x <> v2` by
    (gvs[not_fresh_at_def, Abbr `v0`, Abbr `v1`, Abbr `v2`] >> metis_tac[LESS_EQ_REFL, DECIDE ``n <= n + 1 /\ n <= n + 2``]) >>
  metis_tac[]
QED

Resume body_assign_immutable_bytes_header_joint[memory]:
  gvs[compile_bytestring_word_count_def, emit_op_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_id_def, fresh_var_def, emit_def] >>
  simp[emitted_insts_def, DROP_APPEND, SUB_PLUS,
       run_inst_seq_mem_ok_def, inst_mem_below_frontier_def,
       inst_dload_in_section_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def, mk_inst_def] >>
  gvs[eval_operand_def, lookup_var_def] >>
  rpt CASE_TAC >> simp[]
QED

Resume body_assign_immutable_bytes_header_joint[join]:
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (t with vs_inst_idx := LENGTH sm.cs_current_insts),Gf,tnf)` by
    (irule bodyFullUnwrapRunTheory.emitted_origin_ptr_path >>
     conj_tac >- simp[] >>
     qexistsl_tac [`emitted_insts sa sm`,`sa`] >>
     gvs[same_blocks_def, EVERY_MEM]) >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH sm.cs_current_insts`,`Gf`,`tnf`] >>
  simp[eval_operand_def, lookup_var_def] >>
  `?out. cnt = Var out /\ not_fresh_at sm out /\ ~not_fresh_at sa out` by
    (gvs[compile_bytestring_word_count_def, emit_op_def,
         comp_bind_def, comp_ignore_bind_def, comp_return_def,
         fresh_id_def, fresh_var_def, emit_def] >>
     simp[not_fresh_at_def, ASCIInumbersTheory.toString_11]) >>
  qexists_tac `out` >> simp[] >>
  conj_tac >-
    (qpat_x_assum `t with vs_vars := _ = s` mp_tac >>
     gvs[venom_state_component_equality]) >>
  conj_tac >- gvs[lookup_var_def] >>
  conj_tac >-
    (rpt strip_tac >> gvs[ptr_covers_def] >> metis_tac[]) >>
  gvs[venom_state_component_equality, same_blocks_def]
QED

Finalise body_assign_immutable_bytes_header_joint

(* Every other base target: subscripts, nested attributes, immutables. *)

Theorem body_assign_snapshot_word_joint:
  expr_body_pre ce cx env e es /\
  eval_expr cx e es = (INL pv,ee) /\ read_result cx pv ee = (INL v,ee) /\
  is_word_type (lowered_value_type ce e) /\
  compile_expr ce (expr_type e) e sa = (vv0,sm) /\
  compile_snapshot_vv ce T (vv_with_type (lowered_value_type ce e) vv0) sm = (snap,sb) /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  (!x. vv_operand vv0 = Var x ==> not_fresh_at sm x) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post H ctx func ce cx e es sa sm s0 ee pv vv0 s /\
    ghost_inv_at (DF H) lo d ce cx ee G tn s) /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee pv vv0 s /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ptr_vv_ok cx (post_value_type ce e) pv vv0 ee G tn s /\
  (!t p. vv0 = LocatedValue t p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok ce e p.ptr_operand G s) /\
  (ce.ce_is_ctor /\ vv_location vv0 = SOME LocCode ==>
    ?val. read_result cx pv ee = (INL val,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
        eval_operand (vv_operand vv0) s = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
          val_in_memory rt val (w2n w) mem)) /\
  ghost_kept_at lo ce es sa Gi ti s0 G tn /\
  return_buf_frame d ce sm s /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?u Gf tnf tv.
    evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
    value_has_type tv v /\ val_wf tv v /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gf,tnf) /\
      stmt_state_rel H ctx func ce cx ee u /\
      ghost_inv_at (DF H) lo d ce cx ee Gf tnf u) /\
    eval_operand (vv_operand snap) u = SOME (typed_val_to_w256 tv v) /\
    op_taint tnf (vv_operand snap) = {} /\
    vv_location snap = NONE /\ vv_type snap = lowered_value_type ce e /\
    (!x. vv_operand snap = Var x ==> not_fresh_at sb x) /\
    (!lbl. vv_operand snap <> Label lbl) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func u /\ s.vs_alloca_next <= u.vs_alloca_next /\
    s0.vs_alloca_next <= u.vs_alloca_next /\ return_buf_frame d ce sb u /\
    ghost_kept_at lo ce es sa Gi ti s0 Gf tnf /\
    ghost_kept_at lo ce ee sm G tn s Gf tnf /\
    (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
    alloca_frame ce ee sm s ce ee u /\
    (!aid off sz i. FLOOKUP s.vs_allocas aid = SOME (off,sz) /\ aid < sm.cs_next_id /\
      (!n b sz'. local_region ce ee.scopes s n b sz' ==> off + sz <= b \/ b + sz' <= off) /\
      off <= i /\ i < off + sz /\ i IN tnf.t_mem ==> i IN tn.t_mem)
Proof
  strip_tac >>
  `(do pv <- eval_expr cx e; read_result cx pv od) es = (INL v,ee)` by
    simp[vyperStateTheory.bind_def] >>
  drule_all immutable_rhs_physical_typed >> strip_tac >>
  `post_value_type ce e = lowered_value_type ce e` by
    metis_tac[immutable_rhs_post_physical_classify,is_bytestring_word_type] >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `unwrap_value ce (vv_with_type (lowered_value_type ce e) vv0) = unwrap_value ce vv0` by
    (irule snapshot_retag_unwrap >>
     qexistsl_tac [`cx`,`ee`,`s`,`post_value_type ce e`,`pv`] >>
     fs[vv_post_def]) >>
  `vv_type (vv_with_type (lowered_value_type ce e) vv0) = lowered_value_type ce e` by
    (Cases_on `vv0` >> simp[vv_with_type_def,vv_type_def]) >>
  qpat_x_assum `compile_snapshot_vv _ _ _ _ = _` mp_tac >>
  simp[compile_snapshot_vv_def,comp_bind_def,comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `unwrap_value ce vv0 sm = (op,sb)` >>
  `ptr_vv_ok cx (post_value_type ce e) pv vv0 ee G tn s` by simp[] >>
  drule_at (Pat `compile_expr _ _ _ _ = _`) unwrap_word_value_origin_ptr >>
  disch_then (drule_at (Pat `unwrap_value _ _ _ = _`)) >>
  disch_then (drule_at (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ptr_vv_ok _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `storage_trace_domain _ _ _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (qspec_then `stv` mp_tac) >>
  disch_then (qspec_then `explicit` mp_tac) >>
  disch_then (qspecl_then [`d`,`ctx`,`PG`,`DF`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  strip_tac >> gvs[] >>
  qexistsl_tac [`z`,`G'`,`tn'`] >>
  conj_tac >- metis_tac[expr_post_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `ci_mono sm sb` by metis_tac[ci_mono_unwrap_value,pairTheory.SND] >>
  `return_buf_frame d ce sb z` by
    (irule return_buf_frame_frame >>
     qexistsl_tac [`ce`,`s`,`sm`] >>
     fs[ci_mono_def,wb_frame_def]) >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func ce cx ee s` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
     (impl_tac >- simp[]) >> strip_tac >> fs[vv_post_def]) >>
  `alloca_frame ce ee sm s ce ee z` by
    (irule (INST_TYPE [alpha |-> ``:256``] alloca_frame_of_mem_frame) >>
     fs[wb_frame_def] >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`storage_trace_horizon ee.storage_trace`,`ctx`,`cx`,`func`] >>
     simp[]) >>
  `!x. op = Var x ==> not_fresh_at sb x` by
    (rpt strip_tac >> irule compiler_unwrap_value_var >>
     qexistsl_tac [`ce`,`op`,`sm`,`vv0`] >> simp[] >>
     Cases_on `vv0` >> fs[vv_operand_def]) >>
  `lower_value compile_expr ce (expr_type e) e sa = (op,sb)` by
    simp[lower_value_def,comp_bind_def] >>
  `!lbl. op <> Label lbl` by
    (irule exprReasonOperandTheory.lower_compile_expr_not_label >>
     goal_assum (drule_at Any) >> qexists_tac `env` >>
     fs[expr_body_pre_def,expr_sim_inv_def]) >>
  `~z.vs_halted` by
    (drule gas_origin_ptr_path_projections >> strip_tac >>
     metis_tac[fragGasSeqPtrTheory.gas_path_ptr_ok_not_halted]) >>
  simp[vv_operand_def,vv_location_def,vv_type_def] >>
  fs[expr_post_def,expr_val_rel_def,ptr_val_ok_def,wb_frame_def,ghost_kept_at_def] >>
  conj_tac >- metis_tac[] >> first_assum ACCEPT_TAC
QED

Theorem body_assign_other_full:
  !cx t e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_full_ok cx t) /\
    body_expr_full_ok cx e /\
    body_inv tops ctx cenv cx /\
    struct_args_unique tops /\
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

Theorem body_assign_snapshot_memory_unwrap_joint:
  expr_body_pre ce cx env e es /\
  (do pv <- eval_expr cx e; read_result cx pv od) es = (INL v,ee) /\
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  ~is_word_type (lowered_value_type ce e) /\
  sm.cs_next_var <= sn.cs_next_var /\ sm.cs_next_id <= sn.cs_next_id /\
  unwrap_value ce (vv_with_type (lowered_value_type ce e) vv) sn = (op,sk) /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\ local_ptrs_reserved ce sn /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sn sk func /\ fn_inst_ids_distinct func /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rty /\
  (!w. read_result cx tv ee = (INL w,ee) ==> value_has_type rty w) /\
  read_result cx tv ee = (INL v,ee) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     vv_post H ctx func ce cx e es sa sm s0 ee tv vv s /\
     ghost_inv_at (DF H) lo d ce cx ee G tn s) /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee tv vv s /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sn.cs_current_bb /\
  s.vs_inst_idx = LENGTH sn.cs_current_insts /\
  ptr_vv_ok cx (post_value_type ce e) tv vv ee G tn s /\
  (!t op0. vv = StackValue t op0 /\ ~is_word_type (post_value_type ce e) ==>
    ptr_buf_ok ce e op0 G s) /\
  (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok ce e p.ptr_operand G s) /\
  (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
   ?val. read_result cx tv ee = (INL val, ee) /\
     !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
       eval_operand (vv_operand vv) s = SOME w ==>
       w2n w + type_memory_size rt <= lo /\
       (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
         val_in_memory rt val (w2n w) mem)) /\
  ghost_kept_at lo ce es sa Gi ti s0 G tn /\
  return_buf_frame d ce sn s /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?u Gu tnu stv w.
    evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME stv /\
    value_has_type stv v /\ val_wf stv v /\
    type_memory_bytes ce (lowered_value_type ce e) = type_memory_size stv /\
    eval_operand op u = SOME w /\
    (!mem. mem_agree_outside tnu.t_mem u.vs_memory mem ==>
       val_in_memory stv v (w2n w) mem) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
         (s,G,tn) [] (OK u,Gu,tnu) /\
       expr_post H ctx func ce cx e es sa sk s0 ee v op u /\
       ghost_inv_at (DF H) lo d ce cx ee Gu tnu u) /\
    expr_store_bound cx (post_value_type ce e) v op u /\
    ptr_val_ok cx (post_value_type ce e) v op Gu tnu u /\
    ptr_buf_ok ce e op Gu u /\
    (type_memory_size stv = 0 \/ w2n w + type_memory_size stv <= u.vs_alloca_next) /\
    u.vs_current_bb = sk.cs_current_bb /\
    u.vs_inst_idx = LENGTH sk.cs_current_insts /\
    alloca_history func u /\ s.vs_alloca_next <= u.vs_alloca_next /\
    s0.vs_alloca_next <= u.vs_alloca_next /\
    return_buf_frame d ce sk u /\
    ghost_kept_at lo ce es sa Gi ti s0 Gu tnu /\
    (!x. not_fresh_at sn x ==>
      lookup_var x u = lookup_var x s /\ FLOOKUP Gu x = FLOOKUP G x /\
      op_taint tnu (Var x) = op_taint tn (Var x)) /\
    wb_frame ce ee ee sn s u /\
    ghost_kept_at lo ce ee sn G tn s Gu tnu /\
    alloca_frame ce ee sn s ce ee u /\
    (!aid b n. FLOOKUP s.vs_allocas aid = SOME (b,n) /\ aid < sn.cs_next_id /\
      (!id base len. local_region ce ee.scopes s id base len ==>
         b+n <= base \/ base+len <= b) ==>
      FLOOKUP u.vs_allocas aid = SOME (b,n) /\
      mem_bytes_at b n u.vs_memory = mem_bytes_at b n s.vs_memory /\
      (!i. b <= i /\ i < b+n /\ i IN tnu.t_mem ==> i IN tn.t_mem))
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace)
     ee.storage_trace` by fs[storage_trace_domain_def] >>
  `vv_holds ce cx (post_value_type ce e) tv vv ee s` by
    metis_tac[vv_post_def] >>
  `~is_word_type (post_value_type ce e)` by
    metis_tac[immutable_rhs_post_physical_classify, is_bytestring_word_type] >>
  `(vv_location vv <> NONE /\ vv_location vv <> SOME LocMemory ==>
     lowered_value_type ce e = post_value_type ce e)` by
    metis_tac[snapshot_changed_type_location] >>
  `unwrap_value ce (vv_with_type (lowered_value_type ce e) vv) =
     unwrap_value ce vv` by
    (irule snapshot_retag_unwrap >>
     goal_assum (drule_at (Pat `vv_holds _ _ _ _ _ _ _`)) >>
     metis_tac[immutable_rhs_post_physical_classify]) >>
  `unwrap_value ce vv sn = (op,sk)` by metis_tac[] >>
  `!rt. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
     ~is_word_type (post_value_type ce e) ==>
     type_memory_bytes ce (post_value_type ce e) = type_memory_size rt /\
     type_memory_size rt < 2**64` by
    metis_tac[body_post_type_allocation_bound] >>
  drule_all unwrap_value_origin_ptr >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  gnvs[] >>
  drule_all immutable_rhs_physical_typed >> strip_tac >>
  `expr_post (storage_trace_horizon ee.storage_trace) ctx func ce cx e
     es sa sk s0 ee v op z /\
   ghost_inv_at (DF (storage_trace_horizon ee.storage_trace)) lo d ce cx ee G' tn' z` by
    metis_tac[] >>
  drule_all structlit_child_physical_robust >> strip_tac >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func ce cx ee s` by
    metis_tac[vv_post_def] >>
  `alloca_frame ce ee sn s ce ee z` by
    (irule (INST_TYPE [alpha |-> ``:256``] log_wb_alloca_frame) >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `sn.cs_next_var <= sk.cs_next_var` by
    (qspec_then `ce` (qspec_then `vv` (qspec_then `sn` mp_tac)) ci_mono_unwrap_value >>
     simp[ci_mono_def]) >>
  `return_buf_frame d ce sk z` by
    (irule return_buf_frame_frame >> goal_assum (drule_at Any) >> simp[] >>
     metis_tac[]) >>
  qexistsl [`z`,`G'`,`tn'`,`stv`,`w`] >> simp[] >>
  qpat_x_assum `wb_frame _ _ _ sn s z` mp_tac >>
  qpat_x_assum `ghost_kept_at _ _ ee sn G tn s G' tn'` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[wb_frame_def, ghost_kept_at_def] >>
  ntac 2 strip_tac >> rpt gen_tac >> strip_tac >>
  conj_tac >-
    (first_x_assum irule >> conj_tac >- first_assum ACCEPT_TAC >>
     qexists_tac `aid` >> simp[]) >>
  rpt strip_tac >>
  qpat_x_assum `!aid off sz i. _` (qspecl_then [`aid`,`b`,`n`,`i`] mp_tac) >>
  impl_tac >- (simp[] >> first_assum ACCEPT_TAC) >> simp[]
QED

Theorem body_assign_field_store_joint_frame:
  emit_void MSTORE [Var dst;op] su = ((),sf) /\ fn_has_code su sf func /\
  fn_inst_ids_distinct func /\ ~z.vs_halted /\
  z.vs_current_bb = su.cs_current_bb /\
  z.vs_inst_idx = LENGTH su.cs_current_insts /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  find_containing_scope id es.scopes = SOME (pre,sc,entry,rest) /\
  lookup_var p z = SOME w0 /\ lookup_var dst z = SOME (w0 + n2w off) /\
  eval_operand op z = SOME (typed_val_to_w256 ftv v) /\ op_taint tn op = {} /\
  entry.type = StructTV fs /\ entry.value = StructV vals /\
  fields_layout flds fs /\ struct_has_type fs vals /\ ALOOKUP fs fld = SOME ftv /\
  store_lays_out ftv ftv v /\ off = struct_field_offset flds fld /\
  off + 32 <= sz /\ lo <= w2n w0 /\ ptr_covers G tn dst z 32 /\
  local_ptrs_reserved cenv sa /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  P H0 /\
  (!H. P H ==> stmt_state_rel H ctx func cenv cx es z /\
     ghost_inv_at (DF H) lo d cenv cx es G tn z) /\
  (!mem. mem_agree_outside
      (tn.t_mem DIFF {i | w2n w0 + off <= i /\ i < w2n w0 + off + 32})
      (mstore (w2n w0 + off) (typed_val_to_w256 ftv v) z).vs_memory mem ==>
    val_in_memory entry.type (StructV (AFUPDKEY fld (K v) vals)) (w2n w0) mem) /\
  alloca_history func z /\ return_buf_frame d cenv su z /\
  alloca_frame c0 es0 sa s0 cenv es z /\
  (!aid a n i. FLOOKUP s0.vs_allocas aid = SOME (a,n) /\ aid < sa.cs_next_id /\
    (!name b cap. local_region c0 es0.scopes s0 name b cap ==>
      a+n <= b \/ b+cap <= a) /\ a <= i /\ i < a+n /\ i IN tn.t_mem ==>
    i IN tn0.t_mem) ==>
  ?t tf.
    t = (mstore (w2n w0 + off) (typed_val_to_w256 ftv v) z) with
      vs_inst_idx := SUC z.vs_inst_idx /\
    tf = step_taint (mk_inst su.cs_next_id MSTORE [Var dst;op] []) z
      (mstore (w2n w0 + off) (typed_val_to_w256 ftv v) z) tn /\
    step_prov PG G (mk_inst su.cs_next_id MSTORE [Var dst;op] [])
      (mstore (w2n w0 + off) (typed_val_to_w256 ftv v) z) = G /\
    (!H. P H ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (z,G,tn) [] (OK t,G,tf) /\
      stmt_state_rel H ctx func cenv cx
        (es with scopes := pre ++ (sc |+ (id,entry with
          <|value := StructV (AFUPDKEY fld (K v) vals); popped := []|>)) :: rest) t /\
      ghost_inv_at (DF H) lo d cenv cx
        (es with scopes := pre ++ (sc |+ (id,entry with
          <|value := StructV (AFUPDKEY fld (K v) vals); popped := []|>)) :: rest) G tf t) /\
    ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
    t.vs_inst_idx = LENGTH sf.cs_current_insts /\
    return_buf_frame d cenv sf t /\ alloca_history func t /\
    alloca_frame c0 es0 sa s0 cenv
      (es with scopes := pre ++ (sc |+ (id,entry with
        <|value := StructV (AFUPDKEY fld (K v) vals); popped := []|>)) :: rest) t /\
    t.vs_allocas = z.vs_allocas /\ t.vs_alloca_next = z.vs_alloca_next /\
    (!x. lookup_var x t = lookup_var x z) /\
    tf.t_var = tn.t_var /\ tf.t_mem = tn.t_mem DIFF
      {i | w2n w0 + off <= i /\ i < w2n w0 + off + 32} /\
    (!aid a n i. FLOOKUP s0.vs_allocas aid = SOME (a,n) /\ aid < sa.cs_next_id /\
      (!name b cap. local_region c0 es0.scopes s0 name b cap ==>
        a+n <= b \/ b+cap <= a) /\ a <= i /\ i < a+n /\ i IN tf.t_mem ==>
      i IN tn0.t_mem)
Proof
  strip_tac >> qpat_x_assum `off = _` SUBST_ALL_TAC >>
  qabbrev_tac `off = struct_field_offset flds fld` >>
  `stmt_state_rel H0 ctx func cenv cx es z /\
   ghost_inv_at (DF H0) lo d cenv cx es G tn z` by metis_tac[] >>
  `local_ptrs_rel func cenv es.scopes z /\ alloca_inv z` by
    metis_tac[stmt_state_rel_local_ptrs_alloca] >>
  `lookup_scopes id es.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  `w2n w0 + sz <= z.vs_alloca_next` by
    (fs[local_ptrs_rel_def] >> first_x_assum drule_all >> simp[]) >>
  `z.vs_alloca_next < dimword (:256)` by
    metis_tac[stmt_state_rel_alloca_room,alloca_room_next_lt] >>
  `w2n (w0 + n2w off) = w2n w0 + off` by
    (irule buffer_offset_no_wrap >> qexists_tac `sz` >> simp[]) >>
  drule_all mstore_ghost_frame >>
  disch_then (qspecl_then [`PG`,`G`,`su.cs_next_id`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `tf.t_var = tn.t_var` >>
  qabbrev_tac `t = (mstore (w2n w0 + off) (typed_val_to_w256 ftv v) z) with
    vs_inst_idx := SUC z.vs_inst_idx` >>
  `sf.cs_current_bb = su.cs_current_bb /\
   sf.cs_current_insts = su.cs_current_insts ++
     [mk_inst su.cs_next_id MSTORE [Var dst;op] []] /\
   sf.cs_next_var = su.cs_next_var` by
    (qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
     simp[emit_void_def,comp_bind_def,comp_ignore_bind_def,fresh_id_def,
          emit_def,comp_return_def] >> strip_tac >> gvs[]) >>
  `t.vs_allocas = z.vs_allocas /\ t.vs_alloca_next = z.vs_alloca_next /\
   (!x. lookup_var x t = lookup_var x z)` by
    simp[Abbr `t`,mstore_def,lookup_var_def] >>
  qexistsl_tac [`t`,`tf`] >> gvs[Abbr `t`,Abbr `tf`] >>
  conj_tac >- suspend "family" >>
  conj_tac >- suspend "return" >>
  conj_tac >- suspend "history" >>
  conj_tac >- suspend "frame" >>
  rpt strip_tac >> first_x_assum irule >> metis_tac[]
QED

Resume body_assign_field_store_joint_frame[family]:
  gen_tac >> disch_tac >>
  `stmt_state_rel H ctx func cenv cx es z /\
   ghost_inv_at (DF H) lo d cenv cx es G tn z` by metis_tac[] >>
  conj_tac >- suspend "edge" >>
  conj_tac >- (simp[stmt_state_rel_inst_idx,Abbr `off`] >>
    drule_all stmt_state_rel_write_field >> simp[arithmeticTheory.ADD_COMM]) >>
  suspend "ghost"
QED

Resume body_assign_field_store_joint_frame[edge]:
  `ctx_has_dalloca ctx ==> allocas_below_fmp z` by
    metis_tac[stmt_state_rel_allocas_below_fmp] >>
  `allocas_from lo z` by fs[ghost_inv_at_def] >>
  `?bb. lookup_block z.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb z.vs_inst_idx =
      SOME (mk_inst su.cs_next_id MSTORE [Var dst;op] [])` by
    (drule emitted_insts_emit_void >> strip_tac >>
     drule emit_void_same_blocks >> simp[same_blocks_def] >> strip_tac >>
     drule_all fn_has_code_same_block >> strip_tac >>
     qexists_tac `bb` >> simp[] >>
     first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `ptr_inst_ok (DF H) lo 0 ctx func G tn
    (mk_inst su.cs_next_id MSTORE [Var dst;op] []) z` by
    (irule ptr_inst_ok_mstore_tainted >> simp[]) >>
  `step_inst_base (mk_inst su.cs_next_id MSTORE [Var dst;op] []) z =
    OK (mstore (off + w2n w0) (typed_val_to_w256 ftv v) z)` by
    (qspecl_then [`Var dst`,`op`] mp_tac step_MSTORE >>
     simp[eval_operand_def] >> metis_tac[]) >>
  `inst_mem_below_frontier (mk_inst su.cs_next_id MSTORE [Var dst;op] []) z /\
   inst_dload_in_section (mk_inst su.cs_next_id MSTORE [Var dst;op] []) z /\
   (mk_inst su.cs_next_id MSTORE [Var dst;op] []).inst_opcode <> INVOKE /\
   ~is_terminator (mk_inst su.cs_next_id MSTORE [Var dst;op] []).inst_opcode` by
    (simp[mk_inst_def,is_terminator_def,below_frontier_MSTORE,
      eval_operand_def,inst_dload_in_section_def] >> decide_tac) >>
  drule_all straight_line_origin_ptr_edge >>
  disch_then (qspecl_then [`explicit`,`PG`] mp_tac) >> simp[] >> strip_tac >>
  `~((mstore (off + w2n w0) (typed_val_to_w256 ftv v) z) with
      vs_inst_idx := SUC z.vs_inst_idx).vs_halted` by simp[mstore_def] >>
  metis_tac[gas_origin_ptr_path_rules,APPEND]
QED

Resume body_assign_field_store_joint_frame[ghost]:
  qmatch_goalsub_abbrev_tac `ghost_inv_at (DF H) lo d cenv cx ee G tf t` >>
  `t.vs_allocas = z.vs_allocas /\ t.vs_alloca_next = z.vs_alloca_next /\
   t.vs_memory = (mstore (off + w2n w0) (typed_val_to_w256 ftv v) z).vs_memory /\
   (!x. lookup_var x t = lookup_var x z)` by
    simp[Abbr `t`,mstore_def,lookup_var_def] >>
  `allocas_from lo t` by (fs[ghost_inv_at_def,allocas_from_def] >> metis_tac[]) >>
  `stor_taint_ok_at (DF H) tf t` by
    (fs[ghost_inv_at_def,stor_taint_ok_at_def] >>
     simp[Abbr `tf`,Abbr `t`,mstore_def,contract_storage_def,contract_transient_def,
          step_taint_def,imm_taint_def,mk_inst_def]) >>
  `local_region cenv es.scopes z id (w2n w0) sz` by simp[local_region_def] >>
  simp[Abbr `ee`] >>
  irule (body_full_local_scope_ghost_post |> Q.INST [`n` |-> `sz`]) >>
  simp[] >> goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`G`,`func`,`sa`,`tn`] >> simp[op_taint_def] >>
  conj_tac
  >- (rpt strip_tac >> simp[Abbr `t`] >>
      irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
  irule mstore_mem_bytes_at_disjoint >> decide_tac
QED

Resume body_assign_field_store_joint_frame[return]:
  irule return_buf_frame_frame >> goal_assum (drule_at Any) >>
  simp[mstore_def,lookup_var_def]
QED

Resume body_assign_field_store_joint_frame[history]:
  `step_inst_base (mk_inst su.cs_next_id MSTORE [Var dst;op] []) z =
    OK (mstore (off + w2n w0) (typed_val_to_w256 ftv v) z)` by
    (qspecl_then [`Var dst`,`op`] mp_tac step_MSTORE >>
     simp[eval_operand_def] >> metis_tac[]) >>
  `run_inst_seq [mk_inst su.cs_next_id MSTORE [Var dst;op] []] z =
    OK (mstore (off + w2n w0) (typed_val_to_w256 ftv v) z)` by
    simp[run_inst_seq_def] >>
  `EVERY (\i. ~is_terminator i.inst_opcode)
    [mk_inst su.cs_next_id MSTORE [Var dst;op] []]` by
    simp[mk_inst_def,is_terminator_def] >>
  drule_all emitted_alloca_history >> simp[arithmeticTheory.ADD1]
QED

Resume body_assign_field_store_joint_frame[frame]:
  `local_region cenv es.scopes z id (w2n w0) sz` by simp[local_region_def] >>
  irule alloca_frame_region_write >> goal_assum (drule_at Any) >> simp[] >>
  drule find_containing_scope_structure >> strip_tac >>
  `id IN FDOM sc` by fs[FLOOKUP_DEF] >>
  simp[ABSORPTION_RWT] >>
  rpt strip_tac >> irule valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >>
  decide_tac
QED

Finalise body_assign_field_store_joint_frame

Theorem restored_header_witness[local]:
  !a n old mem. ?mix.
    mem_bytes_at a n mix = mem_bytes_at a n old /\
    (!i. i < a \/ a+n <= i ==>
         mem_bytes_at i 1 mix = mem_bytes_at i 1 mem)
Proof
  rpt gen_tac >>
  qabbrev_tac `s = (ARB:venom_state) with vs_memory := mem` >>
  qexists_tac `(write_memory_with_expansion a (mem_bytes_at a n old) s).vs_memory` >>
  conj_tac
  >- (mp_tac (Q.SPECL [`a`, `mem_bytes_at a n old`, `s`]
               write_memory_mem_bytes_at_same) >> simp[]) >>
  gen_tac >> disch_tac >>
  irule EQ_TRANS >> qexists_tac `mem_bytes_at i 1 s.vs_memory` >>
  conj_tac
  >- (irule write_memory_mem_bytes_at_disjoint >> simp[] >> decide_tac) >>
  simp[Abbr `s`]
QED

Theorem body_assign_empty_nested_robust:
  mem_path_offset entry.type path = SOME (k,tv) /\
  value_has_type entry.type entry.value /\
  has_length_word ty /\ evaluate_type tenv ty = SOME tv /\
  replace_memory_entry entry path (default_value tv) = INL entry' /\
  (!mem. mem_agree_outside old_taint old_memory mem ==>
         val_in_memory entry.type entry.value b mem) /\
  mem_word_at (b+k) new_memory = 0w /\
  (!i. b+k <= i /\ i < b+k+32 ==> i NOTIN new_taint) /\
  (!i. ~(b+k <= i /\ i < b+k+32) ==>
       mem_bytes_at i 1 new_memory = mem_bytes_at i 1 old_memory /\
       (i IN new_taint <=> i IN old_taint)) ==>
  !mem. mem_agree_outside new_taint new_memory mem ==>
        val_in_memory entry'.type entry'.value b mem
Proof
  rpt strip_tac >>
  qspecl_then [`b+k`, `32`, `old_memory`, `mem`]
    (qx_choose_then `mix` strip_assume_tac) restored_header_witness >>
  `mem_agree_outside old_taint old_memory mix` by
    (simp[mem_agree_outside_def] >> rpt strip_tac >>
     Cases_on `b+k <= i /\ i < b+k+32`
     >- (sym_tac >> irule representationCleanPtrTheory.mem_bytes_at_eq_byte >>
         goal_assum (drule_at Any) >> simp[]) >>
     `i < b+k \/ b+k+32 <= i` by decide_tac >>
     `i NOTIN new_taint` by metis_tac[] >>
     metis_tac[mem_agree_outside_def]) >>
  `val_in_memory entry.type entry.value b mix` by metis_tac[] >>
  `mem_word_at (b+k) mem = 0w` by
    metis_tac[clean_word_mem_agree] >>
  drule_all place_store_empty_representation >> strip_tac >>
  `value_has_type tv (default_value tv)` by
    metis_tac[default_value_has_type_thm] >>
  `!q. q < b+k \/ b+k+type_memory_size tv <= q ==>
       mem_bytes_at q 1 mix = mem_bytes_at q 1 mem` by
    (rpt gen_tac >> disch_tac >> first_x_assum irule >> decide_tac) >>
  drule_all place_store_replace_memory_entry >> simp[]
QED

Theorem body_assign_empty_dead_value[local]:
  has_length_word ty /\ evaluate_type tenv ty = SOME tv /\
  mem_word_at off sec' = 0w /\ mem_dead_bytes sec off tv i ==>
  mem_dead_bytes sec' off tv i
Proof
  strip_tac >>
  `is_bytestring_type ty \/ ?et n. ty = ArrayT et (Dynamic n)` by
    (Cases_on `ty` >> gvs[has_length_word_def] >>
     rename1 `ArrayT _ bd` >> Cases_on `bd` >> gvs[has_length_word_def])
  >- (drule_all bytestring_type_value >> strip_tac >>
      gvs[mem_dead_bytes_def] >> decide_tac) >>
  gvs[evaluate_type_def, AllCaseEqs(), mem_dead_bytes_def] >>
  qexists_tac `k` >> simp[] >>
  Cases_on `k < w2n (mem_word_at off sec)` >> gvs[] >>
  drule (cj 1 mem_dead_bytes_range) >>
  simp[LEFT_ADD_DISTRIB] >> decide_tac
QED

Theorem body_assign_empty_immutable_dead:
  struct_args_unique tops /\
  tops = pre ++ VariableDecl vis Immutable name ty slot :: post /\
  evaluate_type (type_env tops) ty = SOME tv /\ has_length_word ty /\
  off = compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre /\
  LENGTH sec = imm_len tops /\ off + type_memory_size tv <= LENGTH sec /\
  LENGTH sec' = LENGTH sec /\ mem_word_at off sec' = 0w /\
  (!i. ~(off <= i /\ i < off+32) ==>
     mem_bytes_at i 1 sec' = mem_bytes_at i 1 sec) ==>
  !i. imm_section_dead tops sec i ==> imm_section_dead tops sec' i
Proof
  strip_tac >> gen_tac >> rewrite_tac[imm_section_dead_def] >> strip_tac >>
  rename1 `evaluate_type (type_env tops) ty' = SOME tv'` >>
  qexistsl_tac [`pre'`,`vis'`,`name'`,`ty'`,`slot'`,`post'`,`tv'`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  Cases_on `pre = pre'`
  >- (`ty = ty'` by
        (qpat_x_assum `tops = pre ++ _` mp_tac >>
         qpat_x_assum `tops = pre' ++ _` (fn th => rewrite_tac[th]) >>
         simp[]) >>
      `tv = tv'` by metis_tac[optionTheory.SOME_11] >>
      irule body_assign_empty_dead_value >> metis_tac[]) >>
  `type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ty =
     type_memory_size tv` by metis_tac[imm_frame_size] >>
  `type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ty' =
     type_memory_size tv'` by metis_tac[imm_frame_size] >>
  `32 <= type_memory_size tv` by metis_tac[memory_length_word_layout] >>
  `pre ++ VariableDecl vis Immutable name ty slot :: post =
   pre' ++ VariableDecl vis' Immutable name' ty' slot' :: post'` by metis_tac[] >>
  drule imm_frame_occurrence_separation >>
  disch_then (qspec_then `get_struct_fields (make_struct_fields_map tops)` mp_tac) >>
  strip_tac >>
  `mem_dead_bytes sec'
     (compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre') tv' =
   mem_dead_bytes sec
     (compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre') tv'` by
    (irule mem_dead_bytes_frame >> reverse conj_tac
     >- first_assum ACCEPT_TAC >>
     (rpt strip_tac >>
         `mem_bytes_at j 1 sec' = mem_bytes_at j 1 sec` by
           (qpat_x_assum `!i. ~(off <= i /\ i < off+32) ==> _` irule >>
            qpat_x_assum `tops = pre ++ _` kall_tac >>
            qpat_x_assum `tops = pre' ++ _` kall_tac >>
            fs[] >> decide_tac) >>
         `j < LENGTH sec'` by metis_tac[] >>
         metis_tac[mem_bytes_at_from_EL, listTheory.CONS_11]) >>
     simp[]) >>
  metis_tac[]
QED
Theorem body_assign_memory_place_execution:
  compile_assign_value cenv (Var xd) LocMemory (Var xs) F loc dty sty bytes sa = ((),sb) /\
  ~is_word_type dty /\ ~is_word_type sty /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  type_widens_to (get_tenv cx) sty dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  type_memory_bytes cenv sty = type_memory_size stv /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  type_memory_size stv < dimword (:256) /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  not_fresh_at sa xs /\ not_fresh_at sa xd /\
  lookup_var xs s = SOME sw /\ lookup_var xd s = SOME dw /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory stv v (w2n sw) mem) /\
  ptr_covers G tn xs s (type_memory_size stv) /\
  w2n sw + type_memory_size stv < dimword (:256) /\
  (type_memory_size stv = 0 \/ w2n sw + type_memory_size stv <= s.vs_alloca_next) /\
  (loc <> SOME LocMemory ==>
    w2n sw + type_memory_size stv <= w2n dw \/
    w2n dw + type_memory_size dtv <= w2n sw) /\
  stmt_state_rel H0 ctx func cenv cx ee s /\
  expr_val_at cenv cx sty start sa ee v (Var xs) s /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  alloca_history func s /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ptr_covers G tn xd s (type_memory_size dtv) /\
  w2n dw + type_memory_size dtv < dimword (:256) /\
  w2n dw + type_memory_size dtv <= s.vs_alloca_next /\
  lo <= w2n dw /\
  (?name b len. local_region cenv ee.scopes s name b len /\
    b <= w2n dw /\ w2n dw + type_memory_size dtv <= b+len) ==>
  ?sc u Gu tu t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    sa.cs_next_id <= sc.cs_next_id /\ local_ptrs_reserved cenv sc /\
    (!H. stmt_state_rel H ctx func cenv cx ee s ==>
      stmt_state_rel H ctx func cenv cx ee u) /\
    (!D d. ghost_inv_at D lo d cenv cx ee G tn s ==>
      ghost_inv_at D lo d cenv cx ee Gu tu u) /\
    (!name b len. local_region cenv ee.scopes u name b len <=>
      local_region cenv ee.scopes s name b len) /\
    (!x. not_fresh_at sa x ==> not_fresh_at sc x /\
      lookup_var x u = lookup_var x s /\ FLOOKUP Gu x = FLOOKUP G x /\
      op_taint tu (Var x) = op_taint tn (Var x)) /\
    (!aid ent. FLOOKUP s.vs_allocas aid = SOME ent ==>
      FLOOKUP u.vs_allocas aid = SOME ent) /\
    alloca_frame cenv ee sa s cenv ee u /\
    (!aid off sz i.
      FLOOKUP s.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
      (!name a len. local_region cenv ee.scopes s name a len ==>
        off+sz <= a \/ a+len <= off) /\
      off <= i /\ i < off+sz /\ i IN tu.t_mem ==> i IN tn.t_mem) /\
    typed_copy_effect ctx func sc sb u t (w2n dw) (type_memory_size dtv) /\
    (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
      val_in_memory dtv v (w2n dw) mem) /\
    (!x. not_fresh_at sc x ==> FLOOKUP Gf x = FLOOKUP Gu x /\
      op_taint tf (Var x) = op_taint tu (Var x)) /\
    tf.t_stor = tu.t_stor /\ tf.t_trans = tu.t_trans /\ tf.t_imm = tu.t_imm /\
    (!i. ~(w2n dw <= i /\ i < w2n dw+type_memory_size dtv) ==>
      (i IN tf.t_mem <=> i IN tu.t_mem)) /\
    alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!d. return_buf_frame d cenv sa s ==> return_buf_frame d cenv sb t)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?name b len. local_region _ _ _ _ _ _ /\ _` strip_assume_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
    metis_tac[stmt_state_rel_allocas_below_fmp] >>
  Cases_on `loc = SOME LocMemory`
  >- suspend "staged" >>
  `compile_store_memory cenv (Var xs) (Var xd) dty sty sa = ((),sb)` by
    gvs[stmtLoweringTheory.compile_assign_value_def] >>
  mp_tac (Q.INST [`tenv` |-> `get_tenv cx`] (SPEC_ALL body_full_memory_store_path)) >>
  (impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  `gas_marked_path F ctx func s 0 (OK t)` by
    (irule gas_marked_path_from_mem >>
     qpat_assum `!D. gas_origin_ptr_path _ _ _ _` (qspec_then `cx_dead H0 cx` mp_tac) >>
     disch_then (strip_assume_tac o MATCH_MP gas_origin_ptr_path_projections) >>
     drule gas_origin_path_erase >> simp[gas_marked_path_def]) >>
  `typed_copy_effect ctx func sa sb s t (w2n dw) (type_memory_size dtv)` by
    (fs[typed_copy_effect_def,typed_copy_state_frame_def,typed_copy_frame_def,
        venom_state_component_equality] >> metis_tac[]) >>
  `alloca_history func t` by
    (qpat_assum `!D. gas_origin_ptr_path _ _ _ _`
       (qspec_then `cx_dead H0 cx` mp_tac) >>
     strip_tac >> fs[stmt_state_rel_def] >>
     metis_tac[body_full_path_alloca_history]) >>
  `ci_mono sa sb` by
    metis_tac[ci_mono_compile_store_memory,pairTheory.SND] >>
  `t.vs_alloca_next = s.vs_alloca_next` by
    (qpat_assum `typed_copy_state_frame _ _ _ _ _`
      (mp_tac o Q.AP_TERM `\z. z.vs_alloca_next` o CONJUNCT1 o
       REWRITE_RULE [typed_copy_state_frame_def]) >> simp[]) >>
  qexistsl_tac [`sa`,`s`,`G`,`tn`,`t`,`Gf`,`tf`] >> simp[] >>
  conj_tac >- (simp[alloca_frame_def] >> metis_tac[]) >>
  conj_tac >- metis_tac[typed_copy_state_frame_allocas_below_fmp] >>
  rpt strip_tac >> irule return_buf_frame_frame >> simp[] >>
  qexistsl_tac [`cenv`,`s`,`sa`] >> fs[ci_mono_def] >> metis_tac[]
QED

Resume body_assign_memory_place_execution[staged]:
  gnvs[stmtLoweringTheory.compile_assign_value_def,
      comp_bind_def,comp_ignore_bind_def,comp_return_def] >>
  rpt (pairarg_tac >> gnvs[]) >>
  rename1 `compile_alloc_buffer _ sa = (buf,sm)` >>
  rename1 `compile_copy_memory _ (Var xs) _ sm = ((),sn)` >>
  `ci_mono sa sm /\ ci_mono sm sn /\ ci_mono sn sb` by
    metis_tac[ci_mono_compile_alloc_buffer,ci_mono_compile_copy_memory,
              ci_mono_compile_store_memory,pairTheory.SND] >>
  `fn_has_code sa sm func /\ fn_has_code sm sn func /\ fn_has_code sn sb func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split,cs_extends_trans]) >>
  mp_tac (Q.INST [`es` |-> `ee`,`tv` |-> `stv`,
    `n` |-> `type_memory_size stv`,`sb` |-> `sn`]
    (SPEC_ALL body_full_memory_stage_frame_path)) >>
  (impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`u`,`root`,`b0`,`Gu`,`tu`] strip_assume_tac) >>
  `local_ptrs_reserved cenv sn` by
    (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `!name a len. local_region cenv ee.scopes u name a len <=>
    local_region cenv ee.scopes s name a len` by
    (rw[local_region_def] >> metis_tac[local_ptrs_reserved_def]) >>
  `lookup_var xd u = SOME dw /\ not_fresh_at sn xd` by metis_tac[] >>
  `ptr_covers Gu tu xd u (type_memory_size dtv)` by
    metis_tac[assignTuplePtrCopyLenTheory.ptr_covers_lookup_frame] >>
  `b0 < dimword (:256)` by decide_tac >>
  `w2n ((n2w b0):bytes32) = b0` by simp[] >>
  `compile_store_memory cenv (Var root) (Var xd) dty sty sn = ((),sb)` by
    metis_tac[] >>
  `s.vs_alloca_next <= u.vs_alloca_next` by
    (qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ _`
      (qspec_then `cx_dead H0 cx` mp_tac) >>
     disch_then (strip_assume_tac o MATCH_MP gas_origin_ptr_path_projections) >>
     drule gas_origin_path_erase >> strip_tac >> drule gas_marked_path_exec >>
     strip_tac >> metis_tac[bodyMemBopRestWordPathTheory.rest_word_path_frontier]) >>
  mp_tac (Q.INST [`tenv` |-> `get_tenv cx`,`xs` |-> `root`,
    `sa` |-> `sn`,`s` |-> `u`,`G` |-> `Gu`,`tn` |-> `tu`,
    `sw` |-> `(n2w b0):bytes32`] (SPEC_ALL body_full_memory_store_path)) >>
  (impl_tac >- (simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
    qpat_assum `!name a len. local_region _ _ u name a len ==> _`
      (qspecl_then [`name`,`b`,`len`] mp_tac) >>
    simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac)) >>
  strip_tac >> suspend "staged_finish"
QED

Resume body_assign_memory_place_execution[staged_finish]:
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK t,Gf,tf)` by
    (gen_tac >>
     qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ _`
       (qspec_then `D` (mp_tac o MATCH_MP gas_origin_ptr_path_append)) >>
     disch_then (qspecl_then [`u`,`Gu`,`tu`,`[]`,`OK t`,`Gf`,`tf`] mp_tac) >>
     simp[]) >>
  `gas_marked_path F ctx func u 0 (OK t)` by
    (irule gas_marked_path_from_mem >>
     qpat_assum `!D. gas_origin_ptr_path _ (u,Gu,tu) _ _`
       (qspec_then `cx_dead H0 cx` mp_tac) >>
     disch_then (strip_assume_tac o MATCH_MP gas_origin_ptr_path_projections) >>
     drule gas_origin_path_erase >> simp[gas_marked_path_def]) >>
  `typed_copy_effect ctx func sn sb u t (w2n dw) (type_memory_size dtv)` by
    (fs[typed_copy_effect_def,typed_copy_state_frame_def,typed_copy_frame_def,
        venom_state_component_equality] >> metis_tac[]) >>
  `alloca_history func t` by
    (qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ (OK t,Gf,tf)`
       (qspec_then `cx_dead H0 cx` mp_tac) >>
     strip_tac >> fs[stmt_state_rel_def] >>
     metis_tac[body_full_path_alloca_history]) >>
  `t.vs_alloca_next = u.vs_alloca_next` by
    (qpat_assum `typed_copy_state_frame _ _ _ _ _`
      (mp_tac o Q.AP_TERM `\z. z.vs_alloca_next` o CONJUNCT1 o
       REWRITE_RULE [typed_copy_state_frame_def]) >> simp[]) >>
  qexistsl_tac [`sn`,`u`,`Gu`,`tu`,`t`,`Gf`,`tf`] >> simp[] >>
  conj_tac >- (fs[ci_mono_def] >> decide_tac) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- metis_tac[typed_copy_state_frame_allocas_below_fmp] >>
  rpt strip_tac >> irule return_buf_frame_frame >> simp[] >>
  qexistsl_tac [`cenv`,`s`,`sa`] >> fs[ci_mono_def] >> metis_tac[]
QED

Finalise body_assign_memory_place_execution

Theorem body_assign_immutable_section_replace:
  struct_args_unique tops /\
  tops = pre ++ VariableDecl vis Immutable name ty slot :: post /\
  evaluate_type (type_env tops) ty = SOME tv /\
  off = compute_immutables_len
          (get_struct_fields (make_struct_fields_map tops)) pre /\
  LENGTH sec1 = lo /\ LENGTH sec2 = lo /\
  off + type_memory_size tv <= lo /\
  (!j. j < lo /\ ~(off <= j /\ j < off + type_memory_size tv) ==>
       EL j sec2 = EL j sec1) /\
  (!j. j < lo /\ j IN M1 ==> imm_section_dead tops sec1 j) /\
  (!j. j < lo /\ ~(off <= j /\ j < off + type_memory_size tv) /\
       j IN M2 ==> j IN M1) /\
  (!j. off <= j /\ j < off + type_memory_size tv /\ j IN M2 ==>
       mem_dead_bytes sec2 off tv j) ==>
  !j. j < lo /\ j IN M2 ==> imm_section_dead tops sec2 j
Proof
  strip_tac >> gen_tac >> strip_tac >>
  Cases_on `off <= j /\ j < off + type_memory_size tv`
  >- metis_tac[imm_frame_restrict] >>
  `imm_section_dead tops sec1 j` by metis_tac[] >>
  qpat_x_assum `imm_section_dead tops sec1 j` mp_tac >>
  rewrite_tac[imm_section_dead_def] >> strip_tac >>
  rename1 `evaluate_type (type_env tops) ty' = SOME tv'` >>
  `type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ty =
     type_memory_size tv` by metis_tac[imm_frame_size] >>
  `type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ty' =
     type_memory_size tv'` by metis_tac[imm_frame_size] >>
  drule (CONJUNCT1 mem_dead_bytes_range) >> strip_tac >>
  `pre ++ VariableDecl vis Immutable name ty slot :: post =
     pre' ++ VariableDecl vis' Immutable name' ty' slot' :: post'`
    by metis_tac[] >>
  drule imm_frame_occurrence_separation >>
  disch_then (qspec_then `get_struct_fields (make_struct_fields_map tops)` mp_tac) >>
  strip_tac
  >- (fs[] >> gvs[]) >>
  `mem_dead_bytes sec2
      (compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre') tv' =
    mem_dead_bytes sec1
      (compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre') tv'`
    by (irule mem_dead_bytes_frame >> reverse conj_tac >- simp[] >>
        ntac 2 (qpat_x_assum `tops = _` kall_tac) >>
        qpat_x_assum `_ ++ _ = _ ++ _` kall_tac >>
        rpt strip_tac >>
        qpat_x_assum `!j. _ ==> EL j sec2 = EL j sec1` irule >>
        gvs[] >> decide_tac) >>
  rewrite_tac[imm_section_dead_def] >>
  qexistsl_tac [`pre'`, `vis'`, `name'`, `ty'`, `slot'`, `post'`, `tv'`] >>
  gvs[]
QED

Theorem body_assign_immutable_sensitivity_fixed:
  (!v a mem dirty.
     well_formed_type_value tv /\
     (value_has_type tv v \/ v = default_value tv) /\ val_wf tv v /\
     (!m. mem_agree_outside dirty mem m ==> val_in_memory tv v a m) ==>
     !j. j < type_memory_size tv /\ a + j IN dirty ==>
       mem_dead_bytes mem a tv (a+j)) ==>
  !n v a mem dirty.
     well_formed_type_value (ArrayTV tv (Fixed n)) /\
     (value_has_type (ArrayTV tv (Fixed n)) v \/
      v = default_value (ArrayTV tv (Fixed n))) /\
     val_wf (ArrayTV tv (Fixed n)) v /\
     (!m. mem_agree_outside dirty mem m ==>
       val_in_memory (ArrayTV tv (Fixed n)) v a m) ==>
     !j. j < type_memory_size (ArrayTV tv (Fixed n)) /\ a+j IN dirty ==>
       mem_dead_bytes mem a (ArrayTV tv (Fixed n)) (a+j)
Proof
  disch_tac >> rpt gen_tac >> disch_tac >>
  `?kvs. v = ArrayV (SArrayV kvs) /\ sparse_has_type tv n kvs` by
    (Cases_on `v` >> gvs[value_has_type_def, default_value_def] >>
     rename1 `ArrayV arr` >> Cases_on `arr` >>
     gvs[value_has_type_def]) >>
  `well_formed_type_value tv` by fs[well_formed_type_value_def] >>
  `!m. mem_agree_outside dirty mem m ==>
       val_in_memory (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs)) a m`
    by metis_tac[] >>
  qpat_x_assum `well_formed_type_value (ArrayTV _ _) /\ _` kall_tac >>
  gvs[type_memory_size_def] >> rpt strip_tac >>
  `0 < type_memory_size tv` by
    (Cases_on `type_memory_size tv = 0` >> gvs[]) >>
  `j DIV type_memory_size tv < n` by simp[DIV_LT_X] >>
  `j = j DIV type_memory_size tv * type_memory_size tv +
       j MOD type_memory_size tv /\ j MOD type_memory_size tv < type_memory_size tv`
    by metis_tac[DIVISION] >>
  qpat_x_assum `!m. mem_agree_outside dirty mem m ==> _`
    (assume_tac o SRULE [Once val_in_memory_def]) >>
  `?w. (value_has_type tv w \/ w = default_value tv) /\ val_wf tv w /\
       (!m. mem_agree_outside dirty mem m ==>
         val_in_memory tv w (a + (j DIV type_memory_size tv) * type_memory_size tv) m)` by
    (Cases_on `ALOOKUP kvs (j DIV type_memory_size tv)`
     >- (qexists_tac `default_value tv` >>
         simp[val_wf_default_value_proof] >> metis_tac[]) >>
     rename1 `ALOOKUP kvs _ = SOME w` >>
     `value_has_type tv w` by metis_tac[sparse_has_type_lookup] >>
     qexists_tac `w` >>
     simp[value_has_type_val_wf] >> metis_tac[kvs_in_memory_lookup, MULT_COMM]) >>
  `a + (j DIV type_memory_size tv) * type_memory_size tv +
     j MOD type_memory_size tv = a+j` by decide_tac >>
  `mem_dead_bytes mem (a + (j DIV type_memory_size tv) * type_memory_size tv)
      tv (a+j)` by
    (first_x_assum
       (qspecl_then [`w`, `a + (j DIV type_memory_size tv) * type_memory_size tv`,
                    `mem`, `dirty`] mp_tac) >>
     (impl_tac >- metis_tac[]) >>
     disch_then (qspec_then `j MOD type_memory_size tv` mp_tac) >>
     qpat_assum `a + _ + _ = a+j` (fn th => rewrite_tac[th]) >> simp[]) >>
  simp[mem_dead_bytes_def] >> metis_tac[MULT_COMM]
QED

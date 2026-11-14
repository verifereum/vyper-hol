(*
 * Augmented assignment over the finite-horizon joint judgment.
 * Stated over the finite-horizon full family (bodySimFull), one sub-shape
 * per S1 dispatch arm of bodySimStmtCases/bodySimDeclCases, so the case in
 * bodyFullCases closes by the same case split.
 *
 * TOP-LEVEL: the body_*_full sub-shape theorems below.
 *)
Theory bodyFullAugAssign
Ancestors
  augAssignStorageFieldSource augAssignFullScalarAbort augAssignFullScalarFresh
  augAssignFullLoad augAssignFullStore augAssignFullStoreGhost augAssignFullOperator
  augAssignFullAddress augAssignFullFieldRead augAssignFullSource augAssignFullSourcePrefix
  augAssignFullRhs augAssignFullStateFrame augAssignFullHistory augAssignFullFieldStore
  gasOutcomeFullRunning augAssignFullLocalPrefix augAssignFullLocalOutcome
  augAssignPtrLocalLayout bodyExprPreFacts supportedStmtTraverse
  supportedExprTraverse vyperTypeCallGraph gasContext vyperTypeInvariants
  gasOutcomeFullCompose vyperStorageFootprint vyperStorageTrace
  representationCleanPtr exprSimUnwrap valueEncodingProps
  loweringStateRelDefs bodyMemoryDefs bodyPtrDefs emitHelperProps
  stmtSimAugAssign exprSimSource exprLoweringProps loweringSlice memoryValueEncoding
  bodyFullPreds bodySimFull gasShadow bodySim exprSimHypsDefs supportedStmts
  compileEnv exprLowering stmtLowering vyperTypeSystem vyperContext
  vyperInterpreter vyperState vyperValue vyperAST list finite_map

val _ = Parse.hide "body";

Theorem augassign_local_load_inputs_full[local]:
  type_stmt env ret_ty (AugAssign ty (NameTarget id) bop e) = SOME env' /\
  expr_body_pre cenv cx env e es /\ lookup_scopes id es.scopes = SOME entry /\
  bop <> In /\ bop <> NotIn /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  stmt_state_rel H ctx func cenv cx es s /\
  ghost_inv_at D lo d cenv cx es G tn s ==>
  ?aw. lookup_var p s = SOME aw /\ ptr_covers G tn p s 32 /\
    w2n aw + 32 <= s.vs_alloca_next /\
    mload (w2n aw) s = val_to_w256 entry.value /\
    (!i. w2n aw <= i /\ i < w2n aw + 32 ==> i NOTIN tn.t_mem)
Proof
  strip_tac >> drule_all augassign_local_entry_word_full >> strip_tac >>
  `?aw. lookup_var p s = SOME aw /\
     type_memory_size entry.type <= sz /\ w2n aw + sz <= s.vs_alloca_next /\
     val_wf entry.type entry.value /\
     val_in_memory entry.type entry.value (w2n aw) s.vs_memory` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
     first_x_assum drule_all >> strip_tac >>
     qexists_tac `w` >> simp[] >>
     irule memory_value_rel_val_in_memory >> simp[]) >>
  `32 <= sz` by
    (gvs[word_value_def, valueEncodingDefsTheory.val_wf_def] >> decide_tac) >>
  qexists_tac `aw` >> simp[] >> rpt conj_tac
  >- (`ptr_covers G tn p s sz` by (fs[ghost_inv_at_def] >> metis_tac[]) >>
      gvs[ptr_covers_def] >> qexistsl_tac [`aw`, `b`, `sz'`] >> simp[] >> decide_tac)
  >- (gvs[word_value_def] >> gvs[val_in_memory_prim, mem_word_at_eq_mload]) >>
  gen_tac >> strip_tac >> irule robust_val_in_memory_prim_clean >>
  qexistsl_tac [`w2n aw`, `s.vs_memory`, `entry.type`, `entry.value`] >>
  simp[GSYM word_value_def] >> fs[ghost_inv_at_def] >> metis_tac[]
QED

Theorem augassign_local_expr_pre_full[local]:
  body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (AugAssign aty (NameTarget id) bop e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
    (AugAssign aty (NameTarget id) bop e) ==> occurs_abi_decode_target target tops) /\
  expr_sim_inv cenv cx env es /\
  type_stmt env ret_ty (AugAssign aty (NameTarget id) bop e) = SOME env' /\
  stmt_exprs_ok cenv (AugAssign aty (NameTarget id) bop e) /\
  call_evaluation_safe cx (int_calls_stmt (AugAssign aty (NameTarget id) bop e)) ==>
  expr_body_pre cenv cx env e es
Proof
  strip_tac >>
  `supported_expr tops e` by gvs[supported_stmt_def] >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `get_module_code cx NONE = SOME tops /\ supported_program tops` by fs[body_inv_def] >>
  `cx_tops cx = tops` by metis_tac[cx_tops_module] >>
  `!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
     is_dynamic (vyper_to_abi_type (type_env tops) target)` by fs[body_inv_def] >>
  irule stmt_expr_body_pre >>
  gvs[type_stmt_def, stmt_exprs_ok_flat, supported_stmt_expr_exists_def,
      supported_expr_exists_def, int_calls_stmt_def, int_calls_expr_def, optionTheory.IS_SOME_EXISTS] >>
  qexists_tac `[]` >> simp[]
QED

Theorem augassign_local_rhs_finish_full[local]:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  expr_body_pre cenv cx env e es /\
  type_stmt env ret_ty (AugAssign aty (NameTarget id) bop e) = SOME env' /\
  stmt_env cenv lctx ret_ty (AugAssign aty (NameTarget id) bop e) sa = (cenv,sb) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_scopes id es.scopes = SOME entry /\
  (!gs. eval_target_place cx (NameTarget id) (es with gas_obs := gs) =
    (INL (MemoryPlace id []),es with gas_obs := gs) /\
    read_place cx (MemoryPlace id []) (es with gas_obs := gs) =
    (INL entry.value,es with gas_obs := gs) /\
    place_type_value cx (MemoryPlace id []) (es with gas_obs := gs) =
    (INL entry.type,es with gas_obs := gs)) /\
  emit_op MLOAD [Var p] sa = (Var out,s1) /\
  lower_value compile_expr cenv aty e s1 = (rhs_op,s2) /\
  compile_binop bop (Var out) rhs_op aty NONE
    (if bop = Exp then expr_int_literal e else NONE) s2 = (res_op,s3) /\
  emit_void MSTORE [Var p;res_op] s3 = ((),sb) /\
  cs_extends sa s1 /\ cs_extends s1 s2 /\
  fn_has_code s1 s2 func /\ fn_has_code s2 s3 func /\ fn_has_code s3 sb func /\
  fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\ local_ptrs_reserved cenv sa /\
  ret_pc_ok cenv sa s0 /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  gas_admissible (eval_stmt cx (AugAssign aty (NameTarget id) bop e)) (stmt_res_ok lctx) es /\
  storage_trace_domain cx st0 es.storage_trace /\
  (!H. gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (s0,G0,tn0) [] (OK t,G',tn')) /\
  eval_operand (Var out) t = SOME (val_to_w256 entry.value) /\
  op_prov G' (Var out) = NONE /\ op_taint tn' (Var out) = {} /\
  ~t.vs_halted /\ t.vs_current_bb = s1.cs_current_bb /\
  t.vs_inst_idx = LENGTH s1.cs_current_insts /\
  t.vs_alloca_next = s0.vs_alloca_next /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn' /\
  (!z. not_fresh_at sa z ==> lookup_var z t = lookup_var z s0) /\
  t.vs_allocas = s0.vs_allocas /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\ alloca_frame cenv es sa s0 cenv es t) /\
  return_buf_frame d cenv s1 t /\
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx)) (es,t,G',tn')
    (\H res ee G tn u. ?v. res = INL v /\
      expr_post H ctx func cenv cx e es s1 s2 t ee v rhs_op u /\
      expr_store_bound cx (expr_type e) v rhs_op u /\
      u.vs_current_bb = s2.cs_current_bb /\ u.vs_inst_idx = LENGTH s2.cs_current_insts /\
      alloca_history func u /\ t.vs_alloca_next <= u.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn u /\
      ptr_val_ok cx (post_value_type cenv e) v rhs_op G tn u /\
      (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e rhs_op G u) /\
      ghost_kept_at lo cenv es s1 G' tn' t G tn)
    (\H res ee gt r. ?ex. res = INR ex /\
      !tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) (INR ex) gt r) ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (eval_stmt cx (AugAssign aty (NameTarget id) bop e)) (es,s0,G0,tn0)
    (\H res ee G tn u. ?cenv'. stmt_lands lctx sb res u /\ ~u.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb /\ cenv' = cenv) /\
      cenv_top_ext cenv cenv' ee.scopes /\ stmt_state_rel H ctx func cenv' cx ee u /\
      storage_well_formed_on cx ee (FST H) /\ return_buf_frame d cenv' sb u /\
      alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv' cx ee G tn u /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x u = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sa x ==> FLOOKUP G x = FLOOKUP G0 x /\
        op_taint tn (Var x) = op_taint tn0 (Var x)))
    (\H res ee gt r. !tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r)
Proof
  strip_tac >>
  qpat_assum `emit_op MLOAD [Var p] sa = _`
    (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  irule augassign_pure_prefix_full >>
  qexistsl_tac [`G'`, `entry.value`, `es`, `[]`, `MemoryPlace id []`,
    `entry.type`, `t`, `tn'`] >> simp[] >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _`
    (mp_tac o HO_MATCH_MP gas_outcome_full_value_running) >> strip_tac >>
  qabbrev_tac `Qrhs = \H v ee G tn u.
    ~u.vs_halted /\ expr_post H ctx func cenv cx e es s1 s2 t ee v rhs_op u /\
    expr_store_bound cx (expr_type e) v rhs_op u /\
    u.vs_current_bb = s2.cs_current_bb /\ u.vs_inst_idx = LENGTH s2.cs_current_insts /\
    alloca_history func u /\ t.vs_alloca_next <= u.vs_alloca_next /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn u /\
    ptr_val_ok cx (post_value_type cenv e) v rhs_op G tn u /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e rhs_op G u) /\
    ghost_kept_at lo cenv es s1 G' tn' t G tn` >>
  irule augassign_rhs_bind_full >> qexists_tac `Qrhs` >>
  reverse conj_tac >- (gvs[Abbr `Qrhs`]) >>
  rpt gen_tac >> strip_tac >> gvs[Abbr `Qrhs`] >>
  irule augassign_local_continuation_full >> simp[] >>
  conj_tac >- fs[loweringPostsTheory.ret_pc_ok_def] >>
  conj_tac >- metis_tac[storage_trace_domain_def] >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`G'`, `e`, `entry`, `env`, `env'`, `es`, `es`, `marks`,
    `res_op`, `ret_ty`, `rhs_op`, `t`, `s2`, `s3`, `tn'`] >>
  simp[ghost_kept_at_def, loweringStateRelDefsTheory.not_fresh_at_def] >>
  fs[ghost_kept_at_def, loweringStateRelDefsTheory.not_fresh_at_def] >> metis_tac[]
QED

Theorem augassign_local_rhs_setup_full[local]:
  lookup_scopes id es.scopes = SOME entry /\
  body_expr_full_ok cx e /\ body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env e es /\
  stmt_env cenv lctx ret_ty (gas_shadow_stmt (AugAssign aty (NameTarget id) bop e))
    shadow_sa = (cenv,shadow_sb) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  emit_op MLOAD [Var p] sa = (Var out,s1) /\
  lower_value compile_expr cenv aty e s1 = (rhs_op,s2) /\
  cs_extends sa s1 /\ fn_has_code s1 s2 func /\
  gas_shadow_state sa shadow_sa /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code shadow_sa shadow_sb shadow_func /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  gas_admissible (eval_stmt cx (AugAssign aty (NameTarget id) bop e)) (stmt_res_ok lctx) es /\
  valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es t /\ storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G' tn' t /\
    return_buf_frame d cenv s1 t /\ ret_pc_ok cenv s1 t /\ local_ptrs_reserved cenv s1) /\
  alloca_history func t /\ ~t.vs_halted /\ t.vs_current_bb = s1.cs_current_bb /\
  t.vs_inst_idx = LENGTH s1.cs_current_insts ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx)) (es,t,G',tn')
    (\H res ee G tn u. ?v. res = INL v /\
      expr_post H ctx func cenv cx e es s1 s2 t ee v rhs_op u /\
      expr_store_bound cx (expr_type e) v rhs_op u /\
      u.vs_current_bb = s2.cs_current_bb /\ u.vs_inst_idx = LENGTH s2.cs_current_insts /\
      alloca_history func u /\ t.vs_alloca_next <= u.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn u /\
      ptr_val_ok cx (post_value_type cenv e) v rhs_op G tn u /\
      (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e rhs_op G u) /\
      ghost_kept_at lo cenv es s1 G' tn' t G tn)
    (\H res ee gt r. ?ex. res = INR ex /\
      !tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) (INR ex) gt r)
Proof
  strip_tac >>
  `stmt_env cenv lctx ret_ty
     (AugAssign aty (NameTarget id) bop (gas_shadow_expr e)) shadow_sa =
     (cenv,shadow_sb)` by fs[gas_shadow_stmt_def, gas_shadow_expr_def] >>
  drule_all augassign_local_layout_ptr >> strip_tac >>
  `cur_op = Var out /\ gas_shadow_state s1 s1'` by
    (mp_tac (Q.INST [`opc` |-> `MLOAD`, `ops` |-> `[Var p]`] gasShadowCompileContextTheory.gas_shadow_compiles_emit_op_same) >>
     pure_rewrite_tac[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`, `shadow_sa`] mp_tac) >> simp[]) >>
  qpat_x_assum `cur_op = _` SUBST_ALL_TAC >>
  `rhs_op' = rhs_op /\ gas_shadow_state s2 s2'` by
    (mp_tac (Q.INST [`cenv` |-> `cenv`, `ty` |-> `aty`, `e` |-> `e`] gasShadowCompileStmtHelpersTheory.gas_shadow_stmt_lower_value) >>
     pure_rewrite_tac[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`s1`, `s1'`] mp_tac) >> simp[]) >>
  qpat_x_assum `rhs_op' = _` SUBST_ALL_TAC >>
  `return_buf_frame d cenv s1 t /\ ret_pc_ok cenv s1 t /\
   local_ptrs_reserved cenv s1` by metis_tac[] >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s1 x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[] >>
     qpat_assum `emit_op MLOAD [Var p] sa = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_op) >> simp[]) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s1 x` by
    fs[loweringPostsTheory.ret_pc_ok_def] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[augAssignPtrLocalSourceTheory.augassign_rhs_admissible_ptr] >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es t /\ storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G' tn' t` by metis_tac[] >>
  drule_all augassign_rhs_invoke_full >>
  disch_then (qspecl_then [`RetQ`, `PG`] ACCEPT_TAC)
QED

(* A local. *)
Theorem body_augassign_local_full:
  !cx aty bop id e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx (NameTarget id) s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_full_ok cx e) /\
    body_base_target_full_ok cx (NameTarget id) /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (AugAssign aty (NameTarget id) bop e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (AugAssign aty (NameTarget id) bop e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (AugAssign aty (NameTarget id) bop e) = SOME env' /\
    stmt_exprs_ok cenv (AugAssign aty (NameTarget id) bop e) /\
    call_evaluation_safe cx (int_calls_stmt (AugAssign aty (NameTarget id) bop e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AugAssign aty (NameTarget id) bop e))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (AugAssign aty (NameTarget id) bop e)))
      (eval_stmt cx (AugAssign aty (NameTarget id) bop e)) es
Proof
  rpt gen_tac >> strip_tac >>
  drule_all augassign_local_expr_pre_full >> strip_tac >>
  drule_all augassign_local_source_prefix_full >> strip_tac >>
  simp[stmt_frag_full_def] >> rpt gen_tac >> strip_tac >>
  drule_all augassign_local_layout_ptr >> strip_tac >> gvs[] >>
  irule gas_outcome_full_initial_domain >>
  simp[evaluate_storage_trace_frame] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  drule_all augassign_local_load_inputs_full >> strip_tac >>
  `allocas_from lo s0 /\ alloca_inv s0` by
    fs[ghost_inv_at_def, stmt_state_rel_def, state_rel_def] >>
  `?out. cur_op = Var out` by metis_tac[emitted_insts_emit_op] >> gvs[] >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func cenv cx es s0 /\
     ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0` by metis_tac[] >>
  drule_all augassign_local_prefix_full >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`, `PG`] mp_tac) >>
  strip_tac >>
  qpat_assum `emit_op MLOAD [Var p] sa = _`
    (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  `!z. not_fresh_at sa z ==> z <> out` by
    (fs[loweringStateRelDefsTheory.not_fresh_at_def] >> decide_tac) >>
  `!z. not_fresh_at sa z ==> lookup_var z t = lookup_var z s0` by
    simp[venomStateTheory.update_var_def, venomStateTheory.lookup_var_def, FLOOKUP_UPDATE] >>
  `t.vs_memory = s0.vs_memory /\ t.vs_allocas = s0.vs_allocas` by
    simp[venomStateTheory.update_var_def] >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func cenv cx es s0 /\
     alloca_frame cenv es sa s0 cenv es t` by
    (gen_tac >> strip_tac >>
     `stmt_state_rel H ctx func cenv cx es s0` by metis_tac[] >>
     simp[] >> irule (INST_TYPE [alpha |-> ``:256``] stmtSimDefsTheory.alloca_frame_of_mem_frame) >>
     simp[venomStateTheory.update_var_def, venomStateTheory.lookup_var_def,
          FLOOKUP_UPDATE] >> qexistsl_tac [`H`, `ctx`, `cx`, `func`] >> simp[]) >>
  qpat_x_assum `t = _` kall_tac >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es t /\ storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G' tn' t /\
    return_buf_frame d cenv s1 t /\ ret_pc_ok cenv s1 t /\ local_ptrs_reserved cenv s1` by metis_tac[] >>
  drule_all augassign_local_rhs_setup_full >>
  disch_then (qspecl_then [`RetQ`, `PG`] assume_tac) >>
  irule augassign_local_rhs_finish_full >> simp[] >>
  conj_tac >- (qexists_tac `tops` >> simp[]) >>
  conj_tac >- (qexistsl_tac [`env`, `env'`, `ret_ty`] >> simp[]) >>
  qexistsl_tac [`G'`, `res_op`, `s3`, `t`, `tn'`] >> simp[] >>
  fs[] >> metis_tac[]
QED

(* A scalar top-level variable. *)
Theorem body_augassign_toplevel_word_full:
  !cx aty bop nsid e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx (TopLevelNameTarget nsid) s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_full_ok cx e) /\
    body_base_target_full_ok cx (TopLevelNameTarget nsid) /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (AugAssign aty (TopLevelNameTarget nsid) bop e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (AugAssign aty (TopLevelNameTarget nsid) bop e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (AugAssign aty (TopLevelNameTarget nsid) bop e) = SOME env' /\
    stmt_exprs_ok cenv (AugAssign aty (TopLevelNameTarget nsid) bop e) /\
    call_evaluation_safe cx (int_calls_stmt (AugAssign aty (TopLevelNameTarget nsid) bop e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    supported_scalar_target tops nsid ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AugAssign aty (TopLevelNameTarget nsid) bop e))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (AugAssign aty (TopLevelNameTarget nsid) bop e)))
      (eval_stmt cx (AugAssign aty (TopLevelNameTarget nsid) bop e)) es
Proof
  cheat
QED

(* A field of a struct local. *)
Theorem body_augassign_attr_local_full:
  !cx aty bop id fld e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx (AttributeTarget (NameTarget id) fld) s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_full_ok cx e) /\
    body_base_target_full_ok cx (AttributeTarget (NameTarget id) fld) /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (AugAssign aty (AttributeTarget (NameTarget id) fld) bop e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (AugAssign aty (AttributeTarget (NameTarget id) fld) bop e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (AugAssign aty (AttributeTarget (NameTarget id) fld) bop e) = SOME env' /\
    stmt_exprs_ok cenv (AugAssign aty (AttributeTarget (NameTarget id) fld) bop e) /\
    call_evaluation_safe cx (int_calls_stmt (AugAssign aty (AttributeTarget (NameTarget id) fld) bop e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AugAssign aty (AttributeTarget (NameTarget id) fld) bop e))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (AugAssign aty (AttributeTarget (NameTarget id) fld) bop e)))
      (eval_stmt cx (AugAssign aty (AttributeTarget (NameTarget id) fld) bop e)) es
Proof
  cheat
QED

(* A field of a storage struct. *)
Theorem body_augassign_attr_storage_full:
  !cx aty bop nsid fld e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx (AttributeTarget (TopLevelNameTarget nsid) fld) s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_full_ok cx e) /\
    body_base_target_full_ok cx (AttributeTarget (TopLevelNameTarget nsid) fld) /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (AugAssign aty (AttributeTarget (TopLevelNameTarget nsid) fld) bop e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (AugAssign aty (AttributeTarget (TopLevelNameTarget nsid) fld) bop e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (AugAssign aty (AttributeTarget (TopLevelNameTarget nsid) fld) bop e) = SOME env' /\
    stmt_exprs_ok cenv (AugAssign aty (AttributeTarget (TopLevelNameTarget nsid) fld) bop e) /\
    call_evaluation_safe cx (int_calls_stmt (AugAssign aty (AttributeTarget (TopLevelNameTarget nsid) fld) bop e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    supported_storage_field_write tops nsid fld ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AugAssign aty (AttributeTarget (TopLevelNameTarget nsid) fld) bop e))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (AugAssign aty (AttributeTarget (TopLevelNameTarget nsid) fld) bop e)))
      (eval_stmt cx (AugAssign aty (AttributeTarget (TopLevelNameTarget nsid) fld) bop e)) es
Proof
  cheat
QED

(* Every other base target. *)
Theorem body_augassign_other_full:
  !cx aty bop t e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx t s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_full_ok cx e) /\
    body_base_target_full_ok cx t /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (AugAssign aty t bop e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (AugAssign aty t bop e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (AugAssign aty t bop e) = SOME env' /\
    stmt_exprs_ok cenv (AugAssign aty t bop e) /\
    call_evaluation_safe cx (int_calls_stmt (AugAssign aty t bop e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    ~(?id. t = NameTarget id) /\
    ~(?nsid. t = TopLevelNameTarget nsid /\
             supported_scalar_target tops nsid) /\
    ~(?id fld. t = AttributeTarget (NameTarget id) fld) /\
    ~(?nsid fld. t = AttributeTarget (TopLevelNameTarget nsid) fld /\
                 supported_storage_field_write tops nsid fld) ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AugAssign aty t bop e))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (AugAssign aty t bop e)))
      (eval_stmt cx (AugAssign aty t bop e)) es
Proof
  cheat
QED

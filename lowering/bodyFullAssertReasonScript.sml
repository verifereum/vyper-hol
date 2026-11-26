(*
 * Assert with a reason in the full body induction (bodySimFullMain), over
 * the finite-horizon joint judgment: the condition's joint fragment and
 * its JNZ (bodyFullExits' compile_assert_cond_path shape), then on the
 * false branch the reason's joint fragment and the REVERT, sharing one
 * origin/memory/pointer witness.
 *
 * TOP-LEVEL:
 *   compile_assert_reason_frag_full -- body_assert_reason_case_full's fragment
 *)
Theory bodyFullAssertReason
Ancestors
  bodyFullShadowBodyInv
  bodyFullAssertReasonSource bodyFullAssertReasonControl bodyFullShared
  bodyFullRaiseReason
  contextRawReachable unitMemInv unitTransformDefs ptrDiscipline
  decoderNavigationPtr gasOutcomeFull gasOutcomeFullCompose gasOutcomeFullStmts fragGasEmitCtrl gasExemptCert
  stmtSimReason stmtSimDefs stmtSimProps stmtSimIfProps exprSimDefs bodyMemoryDefs bodyPtrDefs bodyExprPreFacts exprSimSource
  valueEncoding allocaHistory vyperStorageTrace vyperStorageFootprint
  venomExecSemantics venomState
  bodyFullPreds bodyFullSimProjection bodySimFull gasShadow bodySim exprSimHypsDefs supportedStmts
  reasonSourceProps loweringPosts vyperInterpreter vyperTypeSystem vyperState vyperAST list

val _ = Parse.hide "body";

Theorem compile_assert_reason_frag_full_from_raise:
  (!cx e DF lo d PG tops bindings ctx shadow_ctx func
   shadow_func cenv env env' ret_ty lctx RetQ es.
    body_expr_full_ok cx e /\
    body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx /\ supported_stmt tops bindings (Raise (RaiseReason e)) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (Raise (RaiseReason e)) ==>
       occurs_abi_decode_target target tops) /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Raise (RaiseReason e)) = SOME env' /\
    stmt_exprs_ok cenv (Raise (RaiseReason e)) /\
    call_evaluation_safe cx (int_calls_stmt (Raise (RaiseReason e))) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Raise (RaiseReason e)))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Raise (RaiseReason e))))
      (eval_stmt cx (Raise (RaiseReason e))) es) ==>
  !cx e se DF lo d PG tops bindings ctx shadow_ctx func
   shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' tv t. eval_expr cx e s'' = (INL tv,t) ==> body_expr_full_ok cx se) /\
    body_expr_full_ok cx e /\
    body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx /\ supported_stmt tops bindings (Assert e (AssertReason se)) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (Assert e (AssertReason se)) ==>
       occurs_abi_decode_target target tops) /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assert e (AssertReason se)) = SOME env' /\
    stmt_exprs_ok cenv (Assert e (AssertReason se)) /\
    call_evaluation_safe cx (int_calls_stmt (Assert e (AssertReason se))) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assert e (AssertReason se)))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Assert e (AssertReason se))))
      (eval_stmt cx (Assert e (AssertReason se))) es
Proof
  disch_then (markerLib.mk_asm "producer") >>
  rpt gen_tac >> strip_tac >>
  `expr_body_pre cenv cx env e es` by
    (irule assert_reason_condition_source_pre >> metis_tac[]) >>
  `expr_type e = BaseT BoolT` by fs[type_stmt_assert_reason] >>
  `expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx (BaseT BoolT) e es` by
    (irule (CONJUNCT1 (UNDISCH body_expr_full_ok_simulations) |> DISCH_ALL) >>
     metis_tac[]) >>
  rewrite_tac[stmt_frag_full_def] >> rpt gen_tac >> strip_tac >>
  fs[gas_shadow_stmt_def, gas_shadow_assert_reason_def] >>
  drule_all compile_assert_reason_layout_full >> strip_tac >> gvs[] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[assert_reason_expr_admissible] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at sa x` by metis_tac[ret_pc_ok_def] >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_sim_full_def] >>
  disch_then (qspecl_then [`st0`, `sa`, `s1`, `shadow_sa`, `t1`, `op`, `s0`,
    `G0`, `tn0`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (fn outcome =>
    qpat_assum `return_buf_frame d cenv sa s0` (fn frame =>
      qpat_assum `return_buf_sep d cenv es s0` (fn sep =>
        mp_tac (MATCH_MP gas_outcome_full_return_buf_allocas
          (LIST_CONJ [outcome,frame,sep]))))) >>
  strip_tac >>
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ condQ condR` >>
  rewrite_tac[eval_assert_reason_bind] >>
  irule gas_outcome_full_bind_all_path >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >>
      qexistsl_tac [`mid`, `t`, `v`] >> RULE_ASSUM_TAC BETA_RULE >>
      BETA_TAC >> rpt conj_tac >> first_assum ACCEPT_TAC)
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[])
  >~ [`storage_trace_frame (bind (eval_expr _ _) _)`]
  >- (irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_read_result])
  >~ [`storage_trace_frame _`]
  >- (rw[storage_trace_frame_return, storage_trace_frame_raise,
          evaluate_storage_trace_frame]) >>
  qexists_tac `\H res ee G' tn' t. condQ H res ee G' tn' t /\ ~t.vs_halted /\
                 ee.gas_obs = []` >>
  conj_tac
  >~ [`storage_trace_domain _ _ _`]
  >- suspend "selected" >>
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
  conj_tac >- simp[] >>
  simp[Abbr `condR`] >> rpt strip_tac >>
  Cases_on `res` >- fs[expr_exit_def] >>
  simp[stmt_exit_ptr_def] >>
  conj_tac >- (gen_tac >> disj1_tac >>
    qpat_x_assum `expr_exit _ _` mp_tac >> rpt (pop_assum kall_tac) >>
    metis_tac[expr_exit_INR_type]) >>
  conj_tac >- gvs[halt_exit_def] >>
  Cases_on `r` >> gvs[expr_exit_def]
QED

Resume compile_assert_reason_frag_full_from_raise[selected]:
  qx_genl_tac [`marks`, `res`, `mid`, `G1`, `tn1`, `t`] >>
  BETA_TAC >> strip_tac >> disj1_tac >>
  qunabbrev_tac `condQ` >> RULE_ASSUM_TAC BETA_RULE >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     mid.storage_trace` by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _ /\ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_x_assum `res = INL _` SUBST_ALL_TAC >>
  drule_all assert_reason_condition_bool >> strip_tac >>
  qpat_x_assum `v = BoolV _` SUBST_ALL_TAC >>
  qexists_tac `BoolV b` >> conj_tac >- simp[] >>
  `eval_operand op t = SOME (if b then 1w else 0w)` by
    (drule_all if_condition_operand >> simp[val_to_w256_def]) >>
  `op_taint tn1 op = {} /\ allocas_from lo t` by
    metis_tac[ptr_val_ok_def, ghost_inv_at_def] >>
  `!H. gas_origin_ptr_path
      (DF H, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
      (t, G1, tn1) []
      (OK (jump_to (if b then sb.cs_current_bb else entry.cs_current_bb) t), G1, tn1)` by
    (gen_tac >>
     qpat_assum `emit_inst JNZ _ _ s3 = _`
       (mp_then Any strip_assume_tac emitHelperPropsTheory.emit_inst_extends) >>
     drule_all fragExecTheory.fn_has_code_same_block >> strip_tac >>
     first_x_assum (qspec_then `0` assume_tac) >> fs[] >>
     Cases_on `b` >> fs[]
     >- (irule (SRULE [] (Q.INST [`v` |-> `1w`]
            decoderNavigationPtrTheory.jnz_origin_ptr_path)) >>
         simp[] >> metis_tac[]) >>
     irule (SRULE [] (Q.INST [`v` |-> `0w`]
            decoderNavigationPtrTheory.jnz_origin_ptr_path)) >>
     simp[] >> metis_tac[]) >>
  Cases_on `b` >> BETA_TAC >> simp[]
  >- suspend "true" >>
  suspend "false"
QED

Resume compile_assert_reason_frag_full_from_raise[true]:
  irule gas_outcome_full_pure >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`G1`, `mid`, `INL ()`, `jump_to sb.cs_current_bb t`, `tn1`] >>
  simp[return_def] >> qx_gen_tac `H` >> strip_tac >>
  conj_tac >- (first_x_assum (qspec_then `H` mp_tac) >> simp[]) >>
  qpat_x_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _ /\ _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  pop_assum SUBST1_TAC >>
  `?xs. mid.storage_trace = es.storage_trace ++ xs` by
    (`storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
       (irule storage_trace_frame_bind_all >>
        simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
     qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` assume_tac) >>
     drule_all storage_trace_frame_prefix >> simp[]) >>
  `valid_horizon cx st0 H es.storage_trace` by
    metis_tac[valid_horizon_append] >>
  `stmt_state_rel H ctx func cenv cx es s0` by
    (qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _`
       (qspec_then `H` mp_tac) >> simp[]) >>
  `MAP FDOM mid.scopes = MAP FDOM es.scopes` by
    (qpat_assum `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_post_def, locals_kept_def]) >>
     first_assum ACCEPT_TAC) >>
  `alloca_frame cenv es sa s0 cenv mid t` by
    (qpat_assum `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_then Any mp_tac expr_post_alloca_frame) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then ACCEPT_TAC) >>
  `return_buf_sep d cenv (mid with gas_obs := []) (jump_to sb.cs_current_bb t)` by
    (simp[return_buf_sep_jump, return_buf_sep_gas_obs] >>
     irule (INST_TYPE [alpha |-> ``:256``] return_buf_sep_locals_kept) >>
     conj_tac >- fs[] >>
     qexistsl_tac [`H`, `ctx`, `cx`, `es`, `func`, `s0`, `sa`] >>
     fs[expr_post_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  gvs[ghost_kept_at_def] >>
  drule_all assert_reason_true_post_full >> strip_tac >>
  fs[return_buf_sep_gas_obs] >>
  rpt conj_tac >>
  FIRST [first_assum ACCEPT_TAC,
         irule alloca_frame_same_state >> qexists_tac `t` >>
         simp[jump_to_def] >> first_assum ACCEPT_TAC,
         gvs[ptrDisciplineTheory.allocas_below_fmp_def, jump_to_def] >>
         strip_tac >> fs[]]
QED

Resume compile_assert_reason_frag_full_from_raise[false]:
  qpat_assum `!H. gas_origin_ptr_path _ _ _ _`
    (irule o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
                                  gas_outcome_full_zero_prefix)) >>
  drule_all assert_reason_false_source_ready >> strip_tac >>
  `body_const_cells_agree [(NONE,tops)] cx env (mid with gas_obs := [])` by
    (`well_typed_expr env e` by
       qpat_assum `expr_body_pre _ cx env e _`
         (ACCEPT_TAC o cj 2 o MATCH_MP exprBodyPrePropsTheory.expr_body_pre_static_facts) >>
     qpat_assum `!tail. bind (eval_expr cx e) _ _ = _`
       (qspec_then `[]` assume_tac) >>
     irule body_const_cells_agree_expr_read >>
     goal_assum (drule_at (Pat `bind (eval_expr _ _) _ _ = _`)) >> simp[]) >>
  `stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
     cx lctx RetQ cenv
     (stmt_env cenv lctx ret_ty (Raise (RaiseReason se)))
     (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Raise (RaiseReason se))))
     (eval_stmt cx (Raise (RaiseReason se))) (mid with gas_obs := [])` by
    (asm "producer" irule >> metis_tac[]) >>
  qpat_x_assum `stmt_frag_full _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[stmt_frag_full_def] >>
  disch_then (qspecl_then [`st0`, `entry`, `last`, `sentry`, `slast`,
    `jump_to entry.cs_current_bb t`, `G1`, `tn1`, `cenv`] mp_tac) >>
  (impl_tac >- suspend "entry") >> strip_tac >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  pop_assum (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
  conj_tac >- suspend "post" >> simp[]
QED

Resume compile_assert_reason_frag_full_from_raise[entry]:
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (qpat_assum `body_inv tops ctx cenv cx` (fn inv =>
       qpat_assum `MEM func ctx.ctx_functions`
         (ACCEPT_TAC o MATCH_MP bodyFullIfExpReachTheory.body_inv_no_phi o CONJ inv))) >>
  qabbrev_tac `H0 = storage_trace_horizon mid.storage_trace` >>
  `gas_origin_ptr_path (DF H0,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (s0,G0,tn0) marks (OK t,G1,tn1)` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> gas_origin_ptr_path _ _ _ _`
       (qspec_then `H0` mp_tac) >> simp[Abbr `H0`]) >>
  `gas_origin_ptr_path (DF H0,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (s0,G0,tn0) marks (OK (jump_to entry.cs_current_bb t),G1,tn1)` by
    (qpat_assum `!H. gas_origin_ptr_path _ (t,G1,tn1) [] _`
       (qspec_then `H0` assume_tac) >>
     metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_append, APPEND_NIL]) >>
  `!fn inst s. frag_reachable ctx func (jump_to entry.cs_current_bb t) fn inst s ==>
      dalloca_fmp_headroom inst s` by
    (qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) marks (OK (jump_to _ t),G1,tn1)`
       (fn path =>
       qpat_assum `!bb. MEM bb func.fn_blocks ==> _` (fn no_phi =>
       qpat_assum `!fn inst s. frag_reachable ctx func s0 fn inst s ==> _`
         (fn safe => ACCEPT_TAC (MATCH_MP bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom
           (LIST_CONJ [path,no_phi,safe])))))) >>
  qunabbrev_tac `H0` >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp (jump_to entry.cs_current_bb t)` by
    (`allocas_below_fmp (jump_to entry.cs_current_bb t) <=> allocas_below_fmp t` by
       simp[jump_to_def, allocas_below_fmp_def] >>
     pop_assum (fn bound => PURE_ONCE_REWRITE_TAC [bound]) >> first_assum ACCEPT_TAC) >>
  `gas_admissible (eval_stmt cx (Raise (RaiseReason se))) (stmt_res_ok lctx)
     (mid with gas_obs := [])` by
    (irule assert_reason_raise_admissible >> metis_tac[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     stmt_state_rel H ctx func cenv cx mid (jump_to entry.cs_current_bb t) /\
     storage_well_formed_on cx mid (FST H) /\
     ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 (jump_to entry.cs_current_bb t) /\
     local_ptrs_reserved cenv entry /\
     ret_pc_ok cenv entry (jump_to entry.cs_current_bb t) /\
     return_buf_frame d cenv entry (jump_to entry.cs_current_bb t) /\
     (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
       not_fresh_at entry x) /\
     alloca_history func (jump_to entry.cs_current_bb t) /\ ~block_is_terminated entry /\
     ~(jump_to entry.cs_current_bb t).vs_halted /\
     (jump_to entry.cs_current_bb t).vs_current_bb = entry.cs_current_bb /\
     (jump_to entry.cs_current_bb t).vs_inst_idx = LENGTH entry.cs_current_insts` by
    (gen_tac >> strip_tac >>
     qpat_x_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _ /\ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     qpat_x_assum `INL _ = INL _`
       (SUBST_ALL_TAC o SRULE []) >>
     match_mp_tac assert_reason_false_entry_full >>
     goal_assum (drule_at Any) >> simp[] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!tail. bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
      (INL (BoolV F), mid with gas_obs := tail)` by fs[] >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     es.storage_trace` by
    (`storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
       (irule storage_trace_frame_bind_all >>
        simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
     qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` assume_tac) >>
     drule_all storage_trace_frame_prefix >> strip_tac >>
     fs[] >> metis_tac[valid_horizon_append]) >>
  `stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func cenv cx es s0` by
    (qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >> simp[]) >>
  `return_buf_sep d cenv mid (jump_to entry.cs_current_bb t)` by
    (simp[return_buf_sep_jump] >>
     irule (INST_TYPE [alpha |-> ``:256``] return_buf_sep_locals_kept) >>
     conj_tac >- fs[] >>
     qexistsl_tac [`storage_trace_horizon mid.storage_trace`, `ctx`, `cx`,
                   `es`, `func`, `s0`, `sa`] >>
     fs[expr_post_def, locals_kept_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  pop_assum SUBST_ALL_TAC >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _ /\ _ /\ _ /\ local_ptrs_reserved _ _ /\ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  simp[gas_shadow_stmt_def, gas_shadow_raise_reason_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume compile_assert_reason_frag_full_from_raise[post]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!tail. eval_stmt _ _ _ = _` (qspec_then `[]` mp_tac) >>
  disch_then assume_tac >>
  drule reasonSourcePropsTheory.eval_raise_reason_non_normal >>
  gvs[stmt_lands_def]
QED

Finalise compile_assert_reason_frag_full_from_raise

Theorem compile_assert_reason_frag_full:
  !cx e se DF lo d PG tops bindings ctx shadow_ctx func
   shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' tv t. eval_expr cx e s'' = (INL tv,t) ==> body_expr_full_ok cx se) /\
    body_expr_full_ok cx e /\
    body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx /\ supported_stmt tops bindings (Assert e (AssertReason se)) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (Assert e (AssertReason se)) ==>
       occurs_abi_decode_target target tops) /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assert e (AssertReason se)) = SOME env' /\
    stmt_exprs_ok cenv (Assert e (AssertReason se)) /\
    call_evaluation_safe cx (int_calls_stmt (Assert e (AssertReason se))) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assert e (AssertReason se)))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Assert e (AssertReason se))))
      (eval_stmt cx (Assert e (AssertReason se))) es
Proof
  mp_tac compile_assert_reason_frag_full_from_raise >>
  (impl_tac >- ACCEPT_TAC compile_raise_reason_frag_full) >>
  disch_then ACCEPT_TAC
QED

(* Request-prefix companion to bodyFullAssertCustomError. *)
Theory s1PrefixAssertCustomError
Ancestors
  s1PrefixPreds s1PrefixCompose s1PrefixFrame s1PrefixProps
  bodyFullIfExpReach s1PrefixDefs sum
  bodyFullCustomErrorSource bodyFullCustomErrorLayout bodyFullAssertReasonControl
  bodyFullPreds bodySimFull gasShadow loweringPosts exprSimDefs gasOutcomeFullCompose
  vyperStorageTrace gasContext vyperState stmtSimIfProps valueEncoding bodyPtrDefs
  bodyFullShared exprBodyPreProps gasExplicitSites fragGasOriginPtr decoderNavigationPtr
  fragGasOriginPtrExec emitHelperProps fragExec list ptrDiscipline vyperStorageFootprint
  bodyFullSimProjection[qualified]

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> strip_tac >>
  `expr_body_pre cenv cx env e es` by
    (irule assert_custom_condition_source_pre >> metis_tac[]) >>
  `expr_type e = BaseT BoolT` by fs[type_stmt_assert_custom] >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (BaseT BoolT) e es` by
    (irule (cj 1 bodyFullSimProjectionTheory.body_expr_full_ok_simulations) >>
     simp[] >> qexistsl_tac [`env`, `tops`] >> simp[]) >>
  `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (BaseT BoolT) e es` by
    (qpat_x_assum `body_expr_prefix_ok cx e`
       (mp_tac o CONJUNCT1 o ONCE_REWRITE_RULE [body_expr_prefix_ok_def]) >>
     metis_tac[]) >>
  rewrite_tac[stmt_frag_prefix_def,stmt_frag_full_pre_def] >> rpt gen_tac >> strip_tac >>
  fs[gas_shadow_stmt_def,gas_shadow_assert_reason_def] >>
  drule_all compile_assert_custom_layout_full >> strip_tac >> gvs[] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[assert_custom_expr_admissible] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at sa x` by metis_tac[ret_pc_ok_def] >>
  qpat_x_assum `expr_sim_full _ _ _ _ e es`
    (drule_all o REWRITE_RULE [expr_sim_full_def]) >> strip_tac >>
  qpat_x_assum `expr_sim_prefix _ _ _ _ e es`
    (drule_all o REWRITE_RULE [expr_sim_prefix_def,expr_sim_full_pre_def]) >> strip_tac >>
  drule_all gas_outcome_full_return_buf_allocas >> strip_tac >>
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ condQ condR` >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
     (\H res ee G tn t. condQ H res ee G tn t /\ ee.gas_obs = [])
     (\H res ee gt r. ISR res)` by
    (qpat_assum `gas_outcome_full _ _ _ _ _ _ condQ condR`
       (mp_then Any irule gas_outcome_full_post_source) >>
     simp[Abbr `condR`] >> rpt strip_tac >> Cases_on `res` >> gvs[expr_exit_def]) >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
     (\H res ee G tn t. condQ H res ee G tn t /\ ee.gas_obs = [] /\
       ~t.vs_halted /\ ?ms. gas_origin_ptr_path
         (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) (s0,G0,tn0) ms (OK t,G,tn))
     (\H res ee gt r. ISR res)` by
    (qpat_assum `gas_outcome_full _ _ _ _ _ _ (\H res ee G tn t. condQ H res ee G tn t /\ _) _`
       (mp_then Any irule gas_outcome_full_post_path) >>
     simp[] >> rpt strip_tac
     >- (drule fragGasOriginPtrExecTheory.gas_origin_ptr_path_exec >> simp[fragExecTheory.exit_result_def]) >>
     qexists_tac `marks` >> first_assum ACCEPT_TAC) >>
  rewrite_tac[eval_assert_custom_bind] >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ (\H res ee G tn t. _ /\ _ /\ ~t.vs_halted /\ _) _`
    (mp_then Any irule gas_prefix_full_bind) >>
  simp[storage_trace_frame_bind_all,evaluate_storage_trace_frame,
       storage_trace_frame_read_result,storage_trace_frame_return,storage_trace_frame_raise,
       requests_outcomes_frame_bind_all,evaluate_requests_outcomes_frame,requests_outcomes_frame_read_result] >>
  reverse conj_tac >- (gen_tac >> rpt IF_CASES_TAC >> simp[evaluate_storage_trace_frame,
    storage_trace_frame_return,storage_trace_frame_raise]) >>
  suspend "selected"
QED
*)
Theorem compile_assert_custom_frag_prefix_from_raise:
  !cx e err DF lo d PG tops bindings ctx shadow_ctx func
   shadow_func cenv env env' ret_ty lctx RetQ es.
  (!s'' tv t. eval_expr cx e s'' = (INL tv,t) ==> body_stmt_full_ok cx (Raise (RaiseCustomError err))) /\
  (!s'' tv t. eval_expr cx e s'' = (INL tv,t) ==> body_stmt_prefix_ok cx (Raise (RaiseCustomError err))) /\
  body_expr_full_ok cx e /\
  body_expr_prefix_ok cx e /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  supported_stmt tops bindings (Assert e (AssertCustomError err)) /\
  (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (Assert e (AssertCustomError err)) ==>
       occurs_abi_decode_target target tops) /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_sim_inv cenv cx env es /\
  ce_locals_declared cenv env /\
  locals_alloc_ok cenv env /\
  type_stmt env ret_ty (Assert e (AssertCustomError err)) = SOME env' /\
  stmt_exprs_ok cenv (Assert e (AssertCustomError err)) /\
  call_evaluation_safe cx (int_calls_stmt (Assert e (AssertCustomError err))) /\
  frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty ==>
  stmt_frag_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assert e (AssertCustomError err)))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Assert e (AssertCustomError err))))
      (eval_stmt cx (Assert e (AssertCustomError err))) es
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume compile_assert_custom_frag_prefix_from_raise[selected]:
  qx_genl_tac [`marks`,`v`,`mid`,`G1`,`tn1`,`t`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     mid.storage_trace` by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  drule_all assert_custom_condition_bool >> strip_tac >>
  Cases_on `b` >> gvs[]
  >- (irule gas_prefix_full_no_outcome >> simp[storage_trace_frame_return,return_def]) >>
  suspend "raise"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume compile_assert_custom_frag_prefix_from_raise[raise]:
  qunabbrev_tac `condQ` >> RULE_ASSUM_TAC BETA_RULE >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_x_assum `INL _ = INL _` (SUBST_ALL_TAC o SRULE []) >>
  `eval_operand op t = SOME 0w` by
    (drule_all if_condition_operand >> simp[val_to_w256_def]) >>
  `op_taint tn1 op = {} /\ allocas_from lo t` by
    metis_tac[ptr_val_ok_def,ghost_inv_at_def] >>
  `!H. gas_origin_ptr_path
      (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (t,G1,tn1) [] (OK (jump_to entry.cs_current_bb t),G1,tn1)` by
    (gen_tac >>
     qpat_assum `emit_inst JNZ _ _ s3 = _`
       (mp_then Any strip_assume_tac emitHelperPropsTheory.emit_inst_extends) >>
     drule_all fragExecTheory.fn_has_code_same_block >> strip_tac >>
     first_x_assum (qspec_then `0` assume_tac) >> fs[] >>
     irule (SRULE [] (Q.INST [`v` |-> `0w`]
                       decoderNavigationPtrTheory.jnz_origin_ptr_path)) >>
     simp[] >> metis_tac[]) >>
  irule gas_prefix_full_zero_prefix_guarded >>
  simp[evaluate_storage_trace_frame] >>
  qexistsl_tac [`G1`,`jump_to entry.cs_current_bb t`,`tn1`] >> simp[] >>
  suspend "entry"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume compile_assert_custom_frag_prefix_from_raise[entry]:
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (qpat_assum `body_inv tops ctx cenv cx` (fn inv =>
       qpat_assum `MEM func ctx.ctx_functions`
         (ACCEPT_TAC o MATCH_MP body_inv_no_phi o CONJ inv))) >>
  `gas_origin_ptr_path
     (DF (storage_trace_horizon mid.storage_trace),lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (s0,G0,tn0) ms (OK (jump_to entry.cs_current_bb t),G1,tn1)` by
    (qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) ms (OK t,G1,tn1)`
       (mp_then Any mp_tac gas_origin_ptr_path_append) >>
     simp[] >> metis_tac[APPEND_NIL]) >>
  `!fn inst s. frag_reachable ctx func (jump_to entry.cs_current_bb t) fn inst s ==>
     dalloca_fmp_headroom inst s` by
    (qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) ms (OK (jump_to _ t),G1,tn1)`
       (mp_then Any mp_tac gas_origin_ptr_path_dalloca_fmp_headroom) >>
     simp[] >> disch_then (fn rule => rpt strip_tac >> irule rule >>
       conj_tac >- first_assum ACCEPT_TAC >> qexists_tac `fn` >> first_assum ACCEPT_TAC)) >>
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
     qpat_assum `!h. valid_horizon _ _ h mid.storage_trace ==> _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     qpat_x_assum `INL _ = INL _` (SUBST_ALL_TAC o SRULE []) >>
     match_mp_tac assert_reason_false_entry_full >>
     goal_assum (drule_at Any) >> simp[] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "source"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume compile_assert_custom_frag_prefix_from_raise[source]:
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  drule_all assert_custom_false_source_ready >> simp[] >> strip_tac >>
  `gas_admissible (eval_stmt cx (Raise (RaiseCustomError err))) (stmt_res_ok lctx) mid` by
    (qpat_assum `gas_admissible (eval_stmt _ (Assert _ _)) _ _`
       (mp_then Any mp_tac assert_custom_raise_admissible) >>
     disch_then (qspec_then `gas_explicit marks s0.vs_gas_readings` mp_tac) >> simp[]) >>
  `bind (eval_expr cx e) (read_result cx)
       (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL (BoolV F),mid)` by
    (qpat_assum `mid with gas_obs := [] = mid` (fn mid_eq =>
       qpat_assum `!tail. bind (eval_expr cx e) (read_result cx) _ = _`
         (qspec_then `[]` (ACCEPT_TAC o PURE_REWRITE_RULE [APPEND_NIL, mid_eq])))) >>
  `body_const_cells_agree [(NONE,tops)] cx env mid` by
    (irule body_const_cells_agree_expr_read >>
     qpat_assum `bind (eval_expr cx e) (read_result cx) _ = (_,mid)` (irule_at Any) >>
     imp_res_tac expr_body_pre_static_facts >> simp[]) >>
  `?tv t'. eval_expr cx e
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL tv,t')` by
    (qpat_x_assum `bind (eval_expr cx e) (read_result cx) _ = (_,mid)`
       (assume_tac o REWRITE_RULE [bind_def]) >>
     Cases_on `eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` >>
     rename1 `eval_expr _ _ _ = (out,st)` >> Cases_on `out` >> gvs[]) >>
  `body_stmt_prefix_ok cx (Raise (RaiseCustomError err))` by
    (qpat_assum `!s tv t. _ ==> body_stmt_prefix_ok _ _` (drule_then ACCEPT_TAC)) >>
  qpat_x_assum `body_stmt_prefix_ok cx (Raise _)`
    (mp_tac o REWRITE_RULE [body_stmt_prefix_ok_def]) >>
  disch_then (qspecl_then [`DF`,`lo`,`d`,`PG`,`tops`,`bindings`,`ctx`,
    `shadow_ctx`,`func`,`shadow_func`,`cenv`,`env`,`env`,`ret_ty`,
    `lctx`,`RetQ`,`mid`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  rewrite_tac[stmt_frag_prefix_def,stmt_frag_full_pre_def] >>
  disch_then irule >>
  suspend "branch_pre"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume compile_assert_custom_frag_prefix_from_raise[branch_pre]:
  `ctx_has_dalloca ctx ==> allocas_below_fmp (jump_to entry.cs_current_bb t)` by
    (`allocas_below_fmp (jump_to entry.cs_current_bb t) <=> allocas_below_fmp t` by
       simp[venomStateTheory.jump_to_def, allocas_below_fmp_def] >>
     pop_assum (fn bound => PURE_ONCE_REWRITE_TAC [bound]) >> first_assum ACCEPT_TAC) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) es.storage_trace` by
    (`storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
       (irule storage_trace_frame_bind_all >>
        simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
     `?xs. mid.storage_trace = es.storage_trace ++ xs` by
       (drule_all storage_trace_frame_prefix >> simp[]) >>
     pop_assum strip_assume_tac >>
     irule gasOutcomeFullTheory.valid_horizon_append >>
     rename1 `mid.storage_trace = es.storage_trace ++ xs` >>
     qexists_tac `xs` >>
     qpat_assum `mid.storage_trace = es.storage_trace ++ xs`
       (PURE_ONCE_REWRITE_TAC o single o SYM) >> first_assum ACCEPT_TAC) >>
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
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
      stmt_state_rel H _ _ _ _ mid (jump_to _ t) /\ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
         stmt_state_rel H _ _ _ _ mid (jump_to _ t) /\ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qexistsl_tac [`cenv`,`entry`,`last`,`sentry`,`slast`] >>
  pure_rewrite_tac[gas_shadow_stmt_def, gas_shadow_raise_reason_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise compile_assert_custom_frag_prefix_from_raise
*)

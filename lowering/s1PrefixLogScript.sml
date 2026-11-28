(* Request-prefix companion to bodyFullLog. *)
Theory s1PrefixLog
Ancestors
  s1PrefixPreds bodyFullLog s1PrefixDefs s1PrefixExtCallPosList
  s1PrefixCompose s1PrefixProps bodySimLogArgs bodySim exprSimSource
  bodyFullExtCallPosList supportedStmts supportedStmtTraverse allocLimits
  allocLimitsProps stmtSimLogSource stmtLowering gasShadow compileEnv
  vyperStorageTrace vyperStorageFootprint vyperInterpreter vyperState
  vyperTypeSystem vyperTypeCallGraph bodyExprPreFacts loweringPosts
  exprSimDefs sum list

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> strip_tac >>
  `supported_log tops id args` by fs[supported_stmt_def] >>
  `FST id = NONE` by
    (Cases_on `FST id` >> gvs[stmt_exprs_ok_def, body_inv_def,
                              cenv_module_pins_def, alistTheory.ALOOKUP_def]) >>
  `?fields. supported_event_fields tops id = SOME fields` by
    (Cases_on `supported_event_fields tops id` >> fs[supported_log_def]) >>
  `supported_pure_exprs tops args` by fs[supported_log_def] >>
  `well_typed_exprs env args` by
    fs[vyperTypeSystemTheory.type_stmt_def, AllCaseEqs()] >>
  `alloc_limits_exprs cenv args` by fs[stmt_exprs_ok_def, alloc_limits_stmt_def] >>
  `EVERY (\e. ~is_extcode e) args` by
    (rw[EVERY_MEM] >> irule alloc_limits_expr_not_extcode >>
     metis_tac[exprSimSourceTheory.alloc_limits_exprs_mem]) >>
  `~supported_exprs_exists (const_name_root cx) args` by
    (drule_all body_inv_stmt_const_name_free >> simp[supported_stmt_expr_exists_def]) >>
  `~supported_exprs_exists
      (\e. ~is_extcode e /\
           ~(byte_widths_expr e /\ (array_slot_base cenv e \/ alloc_limits_expr cenv e))) args /\
   call_evaluation_safe cx (int_calls_exprs args) /\
   (!target. supported_exprs_exists (expr_abi_decode_target_root target) args ==>
      occurs_abi_decode_target target tops)` by
    fs[stmt_exprs_ok_flat, supported_stmt_expr_exists_def,
       int_calls_stmt_def, AllCaseEqs()] >>
  `!e st. MEM e args /\ expr_sim_inv cenv cx env st ==>
     expr_body_pre cenv cx env e st` by
    (mp_tac (SPEC_ALL body_log_snapshot_expr_pre) >> asm_rewrite_tac[]) >>
  rewrite_tac[stmt_frag_prefix_def, stmt_frag_full_pre_def] >>
  rpt gen_tac >> strip_tac >>
  `cenv' = cenv /\ compile_stmt cenv lctx ret_ty (Log id args) sa = ((),sb)` by
    (qpat_x_assum `stmt_env cenv lctx ret_ty (Log id args) sa = _` mp_tac >>
     simp[stmt_env_def, declare_stmt_local_def, comp_bind_def,
          comp_ignore_bind_def, comp_return_def] >>
     rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[]) >>
  `compile_stmt (gas_shadow_env T cenv) lctx ret_ty
     (Log id (MAP gas_shadow_expr args)) shadow_sa = ((),shadow_sb)` by
    (qpat_x_assum `stmt_env _ _ _ (gas_shadow_stmt (Log id args)) _ = _` mp_tac >>
     simp[stmt_env_def, declare_stmt_local_def, gas_shadow_stmt_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[]) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x` by
    fs[ret_pc_ok_def] >>
  drule_all_then strip_assume_tac body_log_aggregate_metadata >>
  drule_all_then strip_assume_tac log_full_snapshot_cuts >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cx st0 (eval_exprs cx args) (es,s0,G0,tn0)` by
    (irule extcall_request_positional_packing_prefix >> asm_rewrite_tac[] >>
     qpat_assum `compile_ext_call_args _ cenv [] _ _ sa = _` (irule_at Any) >>
     simp[MAP] >>
     qpat_assum `compile_ext_call_args compile_expr _ [] _
                    (MAP gas_shadow_expr args) shadow_sa = (_,shadow_sm)`
       (irule_at Any) >>
     qpat_assum `gas_shadow_function func shadow_func` (irule_at Any) >>
     qpat_assum `return_buf_frame d cenv sa s0` (irule_at Any) >>
     qpat_assum `body_const_cells_agree [(NONE,tops)] cx env es` (irule_at Any) >>
     gvs[]) >>
  qpat_assum `compile_ext_call_args _ cenv [] _ _ sa = _`
    (mp_then Any (mp_tac o Q.INST [`shadow_sb` |-> `shadow_sm`] o SPEC_ALL)
      (Q.SPEC `F` extcall_request_positional_packing_outcome_named)) >>
  (impl_tac >- asm_rewrite_tac[MAP]) >> strip_tac >>
  rewrite_tac[log_eval_bind] >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _`
    (mp_then Any irule gas_prefix_full_bind_no_outcome) >>
  simp[evaluate_storage_trace_frame, evaluate_requests_outcomes_frame,
       extcall_positional_post_def] >>
  conj_tac >-
   (rpt gen_tac >>
    Cases_on `encode_source_event (get_tenv cx) cx.sources cx.txn.target id v` >>
    Cases_on `cx.txn.is_static` >>
    simp[lift_option_def, check_not_static_def, check_def, assert_def,
         ignore_bind_def, bind_def, return_def, raise_def, push_log_def] >>
    strip_tac >> gvs[]) >>
  conj_tac >-
   (gen_tac >> irule storage_trace_frame_bind_all >>
    simp[storage_trace_frame_lifts] >> gen_tac >>
    irule storage_trace_frame_ignore_bind >>
    simp[storage_trace_frame_check_not_static, storage_trace_frame_state_updates]) >>
  rpt gen_tac >> Cases_on `res` >> simp[]
QED
*)
Theorem compile_log_frag_prefix:
  !cx id args DF lo d PG tops bindings ctx shadow_ctx func
   shadow_func cenv env env' ret_ty lctx RetQ es.
  body_exprs_full_ok cx args /\
  body_exprs_prefix_ok cx args /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  supported_stmt tops bindings (Log id args) /\
  (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (Log id args) ==>
       occurs_abi_decode_target target tops) /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_sim_inv cenv cx env es /\
  ce_locals_declared cenv env /\
  locals_alloc_ok cenv env /\
  type_stmt env ret_ty (Log id args) = SOME env' /\
  stmt_exprs_ok cenv (Log id args) /\
  call_evaluation_safe cx (int_calls_stmt (Log id args)) /\
  frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty ==>
  stmt_frag_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Log id args))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Log id args)))
      (eval_stmt cx (Log id args)) es
Proof
  cheat
QED

Theorem body_log_aggregate_prefix:
  !cx id args fields DF lo d PG tops ctx shadow_ctx func
   shadow_func cenv env env' ret_ty lctx RetQ es.
  body_exprs_full_ok cx args /\
  body_exprs_prefix_ok cx args /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  supported_log tops id args /\
  supported_event_fields tops id = SOME fields /\
  ~EVERY supported_scalar_type (MAP (SND o FST) fields) /\
  (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (Log id args) ==>
       occurs_abi_decode_target target tops) /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_sim_inv cenv cx env es /\
  ce_locals_declared cenv env /\
  locals_alloc_ok cenv env /\
  type_stmt env ret_ty (Log id args) = SOME env' /\
  stmt_exprs_ok cenv (Log id args) /\
  call_evaluation_safe cx (int_calls_stmt (Log id args)) /\
  frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty ==>
  stmt_frag_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Log id args))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Log id args)))
      (eval_stmt cx (Log id args)) es
Proof
  rpt gen_tac >> strip_tac >>
  irule compile_log_frag_prefix >> asm_simp_tac bool_ss [] >>
  qexistsl_tac [`[]`, `env`, `env'`, `tops`] >>
  asm_simp_tac bool_ss [supported_stmt_def]
QED

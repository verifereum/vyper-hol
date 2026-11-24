(* Source entry for the selected arm of a linked If statement. *)
Theory bodyIfSourceEntryMods
Ancestors
  bodyFullPredsMods bodyBranchCellFrameMods bodyExprPreFacts bodyNormalHeadTailMods
  bodyInvCodeProps bodyInvMetadataProps bodySim bodySimStmtFacts exprBodyPreProps
  supportedStmts supportedExprs supportedStmtTraverse supportedExprTraverse
  allocLimits allocLimitsProps vyperTypeSystem vyperTypeCallGraph vyperTypeCallStackSoundness
  exprSimHypsDefs vyperTypeEnvPreservation vyperTypeInvariants vyperState finite_map
  vyperSubscriptOverlap[qualified] compileVyper vyperInterpreter vyperTypeExprResult

Theorem if_condition_pre_mods:
  (!ctx cenv src tops env es bindings s ret_ty env'.
     contract_inv mods exps ctx cenv cx /\
     module_body_inv mods src tops cenv cx /\
     expr_sim_inv_mods mods cenv cx env es /\
     body_const_cells_agree_mods mods cx env es /\
     supported_stmt tops bindings s /\ type_stmt env ret_ty s = SOME env' ==>
     EVERY (source_body_call_supported cx) (int_calls_stmt s)) ==>
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\
  expr_sim_inv_mods mods cenv cx env es /\
  body_const_cells_agree_mods mods cx env es /\
  supported_stmt tops bindings (If e yes no) /\
  type_stmt env ret_ty (If e yes no) = SOME env' /\
  stmt_exprs_ok cenv (If e yes no) /\
  ~supported_stmt_expr_exists (unallocated_bare_global_root cenv env) (If e yes no) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
      (If e yes no) ==> EXISTS (occurs_abi_decode_target target o SND) mods) /\
  call_evaluation_safe cx (int_calls_stmt (If e yes no)) ==>
  expr_type e = BaseT BoolT /\ expr_body_pre_mods mods cenv cx env e es
Proof
  disch_then (mk_asm "resolve") >> strip_tac >>
  `EVERY (source_body_call_supported cx) (int_calls_stmt (If e yes no))` by
    (asm "resolve" irule >> metis_tac[]) >>
  asm_x "resolve" kall_tac >>
  `well_typed_expr env e /\ expr_type e = BaseT BoolT` by
    fs[type_stmt_def, AllCaseEqs()] >>
  `supported_expr tops e` by fs[Once supported_stmt_def, supported_expr_def] >>
  drule_then assume_tac supported_expr_no_evm_run >>
  drule_then assume_tac contract_inv_cenv_modules >>
  drule_then assume_tac contract_inv_type_env >>
  `alloc_limits_expr cenv e` by fs[stmt_exprs_ok_def, alloc_limits_stmt_def] >>
  drule_then assume_tac alloc_limits_expr_not_extcode >>
  drule_then assume_tac (cj 1 alloc_limits_expr_exists) >>
  simp[] >>
  irule (Q.INST [`calls` |-> `int_calls_stmts yes ++ int_calls_stmts no`]
    (SPEC_ALL stmt_expr_body_pre_mods)) >>
  fs[stmt_exprs_ok_def, supported_stmt_expr_exists_def, int_calls_stmt_def,
     DE_MORGAN_THM, LEFT_AND_OVER_OR, supported_expr_exists_disj] >>
  qexistsl_tac [`no`, `yes`] >> simp[]
QED

Theorem expr_sim_inv_mods_if_push[local]:
  expr_sim_inv_mods mods cenv cx env st ==>
  expr_sim_inv_mods mods cenv cx env (st with scopes := FEMPTY :: st.scopes)
Proof
  simp[scopes_CONS_updated, expr_sim_inv_mods_def] >> strip_tac >>
  conj_tac >- (irule push_scope_env_consistent >> simp[]) >>
  conj_tac >- fs[state_well_typed_def, scope_well_typed_def] >>
  `popped_keys_indexed (FEMPTY :: st.scopes)` by fs[popped_keys_indexed_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

(* The exact two success witnesses used in the evaluator induction. *)
Theorem if_branch_ih_mods[local]:
  (!s tv t st x t'. eval_expr cx e s = (INL tv,t) /\ push_scope st = (INL x,t') ==>
     body_stmts_full_ok_mods mods exps cx yes) /\
  (!s tv t st x t'. eval_expr cx e s = (INL tv,t) /\ push_scope st = (INL x,t') ==>
     body_stmts_full_ok_mods mods exps cx no) /\
  bind (eval_expr cx e) (read_result cx) st = (INL (BoolV b),mid) ==>
  body_stmts_full_ok_mods mods exps cx (if b then yes else no)
Proof
  strip_tac >>
  `?tv t. eval_expr cx e st = (INL tv,t)` by
    (qpat_x_assum `bind _ _ _ = _` mp_tac >> simp[bind_def, AllCaseEqs()] >>
     metis_tac[]) >>
  `push_scope mid = (INL (), mid with scopes updated_by CONS FEMPTY)` by
    simp[push_scope_def, return_def] >>
  Cases_on `b` >> simp[] >> metis_tac[]
QED

Theorem if_branch_frag_from_ih_mods[local]:
  body_stmts_full_ok_mods mods exps cx (if b then yes else no) /\
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  supported_stmt tops bindings (If e yes no) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (If e yes no) ==> EXISTS (occurs_abi_decode_target target o SND) mods) /\
  body_const_cells_agree_mods mods cx env mid /\
  expr_sim_inv_mods mods cenv cx env mid /\
  ce_locals_declared cenv env /\ locals_alloc_ok cenv env /\
  type_stmt env ret_ty (If e yes no) = SOME env' /\
  stmt_exprs_ok cenv (If e yes no) /\
  ~supported_stmt_expr_exists (unallocated_bare_global_root cenv env) (If e yes no) /\
  (!key. MEM (vyperSubscriptOverlap$WriteAcc (vyperSubscriptOverlap$StateRef key))
              (vyperSubscriptOverlap$accesses_stmt (If e yes no)) /\
         IS_SOME (FLOOKUP env.bare_global_assignable key) ==>
         IS_SOME (FLOOKUP cenv.ce_module_vars key)) /\
  call_evaluation_safe cx (int_calls_stmt (If e yes no)) /\
  frame_ret_ok_full_mods mods (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cx RetQ cenv ret_ty ==>
  stmt_frag_full_mods (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cx lctx RetQ cenv (stmts_env cenv lctx ret_ty (if b then yes else no))
    (stmts_env (gas_shadow_env T cenv) lctx ret_ty
      (MAP gas_shadow_stmt (if b then yes else no)))
    (eval_stmts cx (if b then yes else no)) (mid with scopes := FEMPTY :: mid.scopes)
Proof
  strip_tac >> drule_then assume_tac expr_sim_inv_mods_if_push >>
  qpat_x_assum `body_stmts_full_ok_mods _ _ _ _`
    (irule o REWRITE_RULE [body_stmts_full_ok_mods_def]) >>
  Cases_on `b` >>
  gvs[scopes_CONS_updated, type_stmt_def, supported_stmt_def,
      supported_stmt_expr_exists_def, optionTheory.IS_SOME_EXISTS,
      vyperSubscriptOverlapTheory.accesses_stmt_def, int_calls_stmt_def,
      stmts_exprs_ok_thm, stmt_exprs_ok_def, alloc_limits_stmt_def,
      stmt_valued_return_def] >>
  metis_tac[call_evaluation_safe_append_left, call_evaluation_safe_append_right]
QED

(* A forced read does not change the raw endpoint.  The expression-statement
   wrapper gives access to the linked constant frame even on a type-check exit. *)
Theorem if_condition_cells_mods[local]:
  well_typed_expr env e /\ body_const_cells_agree_mods mods cx env st /\
  bind (eval_expr cx e) (read_result cx) st = (INL (BoolV b),mid) ==>
  body_const_cells_agree_mods mods cx env mid
Proof
  strip_tac >>
  `?tv. eval_expr cx e st = (INL tv,mid)` by
    (qpat_x_assum `bind _ _ _ = _` mp_tac >> simp[bind_def, AllCaseEqs()] >>
     metis_tac[read_result_state]) >>
  `?res. eval_stmt cx (Expr e) st = (res,mid)` by
    (simp[Once evaluate_def, bind_def, type_check_def, assert_def, return_def, raise_def] >>
     Cases_on `is_HashMapRef tv` >> simp[]) >>
  `type_stmt env NoneT (Expr e) = SOME env` by
    simp[type_stmt_def, well_typed_expr_not_hashmap_place] >>
  irule body_const_cells_agree_mods_stmt >>
  qexistsl_tac [`env`, `st`, `res`, `NoneT`, `Expr e`] >> simp[]
QED

Theorem if_selected_fragment_mods:
  (!s tv t st x t'. eval_expr cx e s = (INL tv,t) /\ push_scope st = (INL x,t') ==>
     body_stmts_full_ok_mods mods exps cx yes) /\
  (!s tv t st x t'. eval_expr cx e s = (INL tv,t) /\ push_scope st = (INL x,t') ==>
     body_stmts_full_ok_mods mods exps cx no) /\
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  supported_stmt tops bindings (If e yes no) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (If e yes no) ==> EXISTS (occurs_abi_decode_target target o SND) mods) /\
  body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods cenv cx env e es /\
  ce_locals_declared cenv env /\ locals_alloc_ok cenv env /\
  type_stmt env ret_ty (If e yes no) = SOME env' /\
  stmt_exprs_ok cenv (If e yes no) /\
  ~supported_stmt_expr_exists (unallocated_bare_global_root cenv env) (If e yes no) /\
  (!key. MEM (vyperSubscriptOverlap$WriteAcc (vyperSubscriptOverlap$StateRef key))
              (vyperSubscriptOverlap$accesses_stmt (If e yes no)) /\
         IS_SOME (FLOOKUP env.bare_global_assignable key) ==>
         IS_SOME (FLOOKUP cenv.ce_module_vars key)) /\
  call_evaluation_safe cx (int_calls_stmt (If e yes no)) /\
  frame_ret_ok_full_mods mods (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cx RetQ cenv ret_ty ==>
  !gs b mid. bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
               (INL (BoolV b),mid) ==>
    stmt_frag_full_mods (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv (stmts_env cenv lctx ret_ty (if b then yes else no))
      (stmts_env (gas_shadow_env T cenv) lctx ret_ty
        (MAP gas_shadow_stmt (if b then yes else no)))
      (eval_stmts cx (if b then yes else no)) (mid with scopes := FEMPTY :: mid.scopes)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `(expr_body_pre_mods mods cenv cx env e (es with gas_obs := gs) <=>
    expr_body_pre_mods mods cenv cx env e es)` by
    simp_tac (srw_ss()) [expr_body_pre_mods_def, expr_sim_inv_mods_def] >>
  `expr_body_pre_mods mods cenv cx env e (es with gas_obs := gs)` by simp[] >>
  `expr_sim_inv_mods mods cenv cx env mid` by
    (drule (CONV_RULE (DEPTH_CONV ETA_CONV) expr_body_pre_eval_mods) >>
     disch_then (drule_then strip_assume_tac) >> simp[]) >>
  `body_const_cells_agree_mods mods cx env mid` by
    (irule if_condition_cells_mods >>
     goal_assum (drule_at (Pat `bind _ _ _ = _`)) >>
     simp[] >> drule expr_body_pre_mods_well_typed >> simp[]) >>
  `body_stmts_full_ok_mods mods exps cx (if b then yes else no)` by
    (irule if_branch_ih_mods >> goal_assum (drule_at (Pat `bind _ _ _ = _`)) >>
     simp[] >> rpt conj_tac >> rpt gen_tac >> strip_tac >> metis_tac[]) >>
  irule if_branch_frag_from_ih_mods >>
  qexistsl_tac [`bindings`, `e`, `env`, `env'`, `exps`, `mods`, `src`, `tops`] >> simp[]
QED

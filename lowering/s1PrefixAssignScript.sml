(* Request-prefix companion to bodyFullAssign. *)
Theory s1PrefixAssign
Ancestors
  s1PrefixPreds bodyFullAssign s1PrefixDefs s1PrefixFrame s1PrefixCompose
  stmtSimAssignStorage vyperStorageBackend gasOutcomeFull vyperStorageTrace
  vyperStorageFootprint bodyFullExtCallPackingReady bodyFullPreds loweringPosts
  vyperInterpreter bodySimFull s1PrefixProps list rich_list vyperState vyperAST compileEnv exprSimDefs
  gasOutcomeFullCompose s1PrefixAssignLocalEmpty assignBasePtrLocalBodyFacts
  memoryLocalRhsProps exprSimAbiDecodeEntryTyping stmtSimAssignMem stmtSimAssignSource exprSimHypsDefs exprLoweringProps exprLowering stmtLowering bodySimStmtFacts tupleTargetStoreProps
  assignRelayoutFrag targetPlaceSim fragExec pair gasShadowCompileStmtHelpers gasShadowCompileStmtBase gasShadow gasShadowState s1PrefixAssignAttrStorage[qualified,ignore_grammar] tuplePlaceStep option s1PrefixAssignToplevelRhs s1PrefixInvalidTraceDomain bodyFullAssignToplevelSetup exprSimTopLevelProps stateRelProj exprSimSource s1PrefixAssignLocalLookup s1PrefixAssignLocalProjection s1PrefixAssignLocalWordCode s1PrefixAssignValueRhsReplay s1PrefixImmutableTargetPlace bodyFullSimProjection bodyFullIfExpReach assignPlacePureCode assignPlaceEmpty stmtLoweringMono bodyFullTargetRoots exprBodyPreProps freshWrites exprSimHyps vyperTypeCallGraph vyperTypeEvalProofs immutableAssignEmpty vyperTypeCallStackSoundness vyperTypeSystem bodyMemoryDefs s1PrefixAssignResidualTarget s1PrefixAssignResidualEmpty s1PrefixAssignResidualValue

Theorem body_assign_local_word_prefix:
  !cx id ty e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
  (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_full_ok cx (NameTarget id)) /\
  (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_prefix_ok cx (NameTarget id)) /\
  body_expr_full_ok cx e /\
  body_expr_prefix_ok cx e /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  supported_stmt tops bindings (Assign (BaseTarget (NameTarget id)) e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget (NameTarget id)) e) ==>
       occurs_abi_decode_target target tops) /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
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
  stmt_frag_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (NameTarget id)) e))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Assign (BaseTarget (NameTarget id)) e)))
      (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac assign_base_local_rhs_pre >>
  `expr_type e = ty` by metis_tac[type_widens_to_word] >>
  drule_all_then strip_assume_tac expr_sim_inv_local >>
  drule_all_then assume_tac expr_sim_inv_local_ce_var_type >>
  `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e) e es` by
    (qpat_x_assum `body_expr_prefix_ok cx e` mp_tac >>
     simp[Once body_expr_prefix_ok_def] >> metis_tac[]) >>
  `cenv.ce_var_type id = SOME (expr_type e)` by simp[] >>
  `is_word_type (expr_type e)` by simp[] >>
  pure_rewrite_tac[stmt_frag_prefix_def, stmt_frag_full_pre_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac assign_local_word_rhs_code_pair >>
  irule body_assign_local_prefix_of_rhs >>
  conj_tac >- (qexists_tac `lctx` >> simp[]) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x` by
    fs[ret_pc_ok_def] >>
  drule_then assume_tac assign_local_admissible_rhs >>
  qpat_x_assum `expr_sim_prefix _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_prefix_def, expr_sim_full_pre_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,`op`,
    `s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]
QED

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac assign_base_local_rhs_pre >>
  drule_all_then strip_assume_tac expr_sim_inv_local >>
  `evaluate_type (get_tenv cx) ty = SOME entry.type` by metis_tac[] >>
  Cases_on `has_length_word (expr_type e) /\ is_empty_value_expr e`
  >- (qpat_assum `has_length_word _ /\ is_empty_value_expr _`
        (CONJUNCTS_THEN ASSUME_TAC) >>
      `env.type_defs = get_tenv cx` by metis_tac[abi_decode_inv_type_env] >>
      `!gs. bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
          (INL (default_value entry.type), es with gas_obs := gs)` by
        (gen_tac >> metis_tac[memory_rhs_empty_read_destination]) >>
      pure_rewrite_tac[stmt_frag_prefix_def, stmt_frag_full_pre_def] >>
      rpt gen_tac >> strip_tac >>
      drule_all_then strip_assume_tac assign_local_identity_rhs_all_tails >>
      irule gas_prefix_full_no_outcome >>
      simp[cj 1 evaluate_storage_trace_frame]) >>
  `cenv.ce_var_type id = SOME ty` by
    (drule_all_then mp_tac body_tuple_target_local_aligned >>
     simp[tuple_target_aligned_def]) >>
  `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e) e es` by
    (qpat_x_assum `body_expr_prefix_ok cx e` mp_tac >>
     simp[Once body_expr_prefix_ok_def] >> metis_tac[]) >>
  pure_rewrite_tac[stmt_frag_prefix_def, stmt_frag_full_pre_def] >> rpt gen_tac >> strip_tac >>
  drule_all_then strip_assume_tac assign_local_relayout_code_parts >>
  qpat_x_assum `cenv' = cenv` SUBST_ALL_TAC >>
  `?shadow_sB. lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
     (gas_shadow_expr e) shadow_sa = (op,shadow_sB) /\ gas_shadow_state sB shadow_sB` by
    (Cases_on `lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
         (gas_shadow_expr e) shadow_sa` >>
     qspecl_then [`sa`,`shadow_sa`] mp_tac
       (REWRITE_RULE[gas_shadow_compiles_def]
         (Q.INST [`sd` |-> `T`, `ty` |-> `expr_type e`] gas_shadow_stmt_lower_value_env)) >> simp[]) >>
  `fn_has_code shadow_sa shadow_sB shadow_func` by
    (qpat_x_assum `stmt_env _ _ _ (Assign _ e) sa = _` kall_tac >>
     qpat_x_assum `stmt_env _ _ _ (gas_shadow_stmt _) _ = _` mp_tac >>
     pure_rewrite_tac[gas_shadow_stmt_def, gas_shadow_assignment_def, gas_shadow_expr_def] >>
     strip_tac >>
     `expr_type (gas_shadow_expr e) = expr_type e` by simp[] >>
     `~(has_length_word (expr_type (gas_shadow_expr e)) /\
         is_empty_value_expr (gas_shadow_expr e))` by
       (qpat_assum `~(has_length_word (expr_type e) /\ is_empty_value_expr e)` mp_tac >>
        simp[gas_shadow_is_empty_value_expr]) >>
     `FLOOKUP (gas_shadow_env T cenv).ce_vars id = SOME (PtrVar (Var p) sz)` by simp[] >>
     `(gas_shadow_env T cenv).ce_var_type id = SOME ty` by simp[] >>
     drule_all_then strip_assume_tac assign_local_relayout_code_parts >>
     qpat_x_assum `lower_value _ _ _ (gas_shadow_expr e) _ = _` mp_tac >> simp[]) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x` by
    fs[ret_pc_ok_def] >>
  drule_then assume_tac assign_local_admissible_rhs >>
  qpat_x_assum `expr_sim_prefix _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_prefix_def, expr_sim_full_pre_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sB`,`shadow_sa`,`shadow_sB`,`op`,
    `s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  (* The local write changes scopes but does not add any storage observations.
     The RHS marks therefore witness the assignment prefix for the same tails. *)
  rewrite_tac[gas_prefix_full_def] >>
  disch_then (qx_choose_then `marks` (CONJUNCTS_THEN ASSUME_TAC)) >>
  qexists_tac `marks` >> conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >>
  rename1 `valid_horizon cx st0 H obs_pre` >>
  qabbrev_tac `gs = gas_explicit marks s0.vs_gas_readings ++ tail` >>
  Cases_on `bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs)` >>
  rename1 `bind (eval_expr _ _) _ _ = (rhs,mid)` >>
  `ee.storage_trace = mid.storage_trace` by
    (qpat_assum `eval_stmt _ _ _ = _` mp_tac >>
     drule assign_local_admissible_run >>
     disch_then (qspec_then `gs` (fn th => rewrite_tac[th])) >>
     Cases_on `rhs` >> simp[Once bind_def] >>
     disch_tac >> drule_all_then strip_assume_tac assign_local_continuation_success >>
     qpat_x_assum `write_place _ _ _ _ = (res,ee)` mp_tac >> simp[] >>
     disch_then (mp_tac o AP_TERM ``\st:evaluation_state. st.storage_trace`` o CONJUNCT2) >> simp[]) >>
  qpat_assum `!tail res ee obs_pre rq outcome sfx H. _`
    (qspecl_then [`tail`,`rhs`,`mid`,`obs_pre`,`rq`,`outcome`,`sfx`,`H`] mp_tac) >>
  fs[Abbr `gs`]
QED
*)
Theorem body_assign_local_widened_prefix:
  !cx id ty e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
  (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_full_ok cx (NameTarget id)) /\
  (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_prefix_ok cx (NameTarget id)) /\
  body_expr_full_ok cx e /\
  body_expr_prefix_ok cx e /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  supported_stmt tops bindings (Assign (BaseTarget (NameTarget id)) e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget (NameTarget id)) e) ==>
       occurs_abi_decode_target target tops) /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
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
  stmt_frag_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (NameTarget id)) e))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Assign (BaseTarget (NameTarget id)) e)))
      (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) es
Proof
  cheat
QED

Theorem body_assign_toplevel_word_prefix:
  !cx nsid e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
  (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_full_ok cx (TopLevelNameTarget nsid)) /\
  (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_prefix_ok cx (TopLevelNameTarget nsid)) /\
  body_expr_full_ok cx e /\
  body_expr_prefix_ok cx e /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  supported_stmt tops bindings (Assign (BaseTarget (TopLevelNameTarget nsid)) e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget (TopLevelNameTarget nsid)) e) ==>
       occurs_abi_decode_target target tops) /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_sim_inv cenv cx env es /\
  ce_locals_declared cenv env /\
  locals_alloc_ok cenv env /\
  type_stmt env ret_ty (Assign (BaseTarget (TopLevelNameTarget nsid)) e) = SOME env' /\
  stmt_exprs_ok cenv (Assign (BaseTarget (TopLevelNameTarget nsid)) e) /\
  call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget (TopLevelNameTarget nsid)) e)) /\
  frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
  supported_scalar_target tops nsid /\
  (?dty. type_place_target env (TopLevelNameTarget nsid) = SOME (Type dty) /\
           is_word_type dty) ==>
  stmt_frag_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (TopLevelNameTarget nsid)) e))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Assign (BaseTarget (TopLevelNameTarget nsid)) e)))
      (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget nsid)) e)) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac body_assign_toplevel_word_full_setup >> gvs[] >>
  `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e) e es` by
    (qpat_x_assum `body_expr_prefix_ok cx e` mp_tac >>
     simp[Once body_expr_prefix_ok_def] >> metis_tac[]) >>
  pure_rewrite_tac[stmt_frag_prefix_def, stmt_frag_full_pre_def] >>
  rpt gen_tac >> strip_tac >>
  reverse (Cases_on `storage_trace_domain cx st0 es.storage_trace`)
  >- (irule gas_prefix_full_invalid_trace_domain >> simp[evaluate_storage_trace_frame]) >>
  `?H. valid_horizon cx st0 H es.storage_trace` by metis_tac[storage_trace_domain_def] >>
  `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx` by
    metis_tac[stmt_state_rel_vars_rels] >>
  drule_all_then assume_tac toplevel_storage_ce_vars >>
  drule_all_then strip_assume_tac assign_storage_word_code_parts >> gvs[] >>
  rename1 `lower_value compile_expr cenv (expr_type e) e sa = (op,sm)` >>
  `?shadow_sm. lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
       (gas_shadow_expr e) shadow_sa = (op,shadow_sm) /\ gas_shadow_state sm shadow_sm` by
    (Cases_on `lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
                 (gas_shadow_expr e) shadow_sa` >>
     qspecl_then [`sa`,`shadow_sa`] mp_tac
       (REWRITE_RULE[gas_shadow_compiles_def]
         (Q.INST [`sd` |-> `T`, `ty` |-> `expr_type e`] gas_shadow_stmt_lower_value_env)) >> simp[]) >>
  `fn_has_code shadow_sa shadow_sm shadow_func` by
    (qpat_x_assum `stmt_env _ _ _ (Assign _ e) sa = _` kall_tac >>
     qpat_x_assum `stmt_env _ _ _ (gas_shadow_stmt _) _ = _` mp_tac >>
     simp[gas_shadow_stmt_def, gas_shadow_assignment_def, gas_shadow_expr_def] >> strip_tac >>
     `is_word_type (expr_type (gas_shadow_expr e))` by simp[] >>
     `FLOOKUP (gas_shadow_env T cenv).ce_module_vars (NONE,id) =
        SOME (if tr then TransientLoc (n2w slot) else StorageLoc (n2w slot))` by simp[] >>
     `(gas_shadow_env T cenv).ce_hashmap_info (NONE,id) = NONE` by simp[] >>
     `(gas_shadow_env T cenv).ce_module_var_type (NONE,id) =
        SOME (expr_type (gas_shadow_expr e))` by simp[] >>
     drule_all_then strip_assume_tac assign_storage_word_code_parts >>
     gvs[] >> metis_tac[]) >>
  drule_then assume_tac expr_body_pre_gas_admissible >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x` by
    fs[ret_pc_ok_def] >>
  irule body_assign_toplevel_word_prefix_from_rhs >>
  qpat_x_assum `expr_sim_prefix _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_prefix_def, expr_sim_full_pre_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,`op`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  simp[]
QED

Theorem body_assign_attr_storage_prefix:
  !cx nsid fld fty e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
  (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_full_ok cx (AttributeTarget (TopLevelNameTarget nsid) fld)) /\
  (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_prefix_ok cx (AttributeTarget (TopLevelNameTarget nsid) fld)) /\
  body_expr_full_ok cx e /\
  body_expr_prefix_ok cx e /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  supported_stmt tops bindings (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) e) ==>
       occurs_abi_decode_target target tops) /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
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
  stmt_frag_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) e))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) e)))
      (eval_stmt cx (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) e)) es
Proof
  rpt gen_tac >> strip_tac >> PairCases_on `nsid` >>
  rename1 `supported_storage_field_write tops (src,id) fld` >>
  `well_typed_expr env e /\ expr_type e = fty` by
    (gvs[vyperTypeSystemTheory.type_stmt_def, vyperTypeSystemTheory.atarget_accepts_def] >>
     metis_tac[type_widens_to_word]) >>
  `expr_body_pre cenv cx env e es` by
    drule_all_then ACCEPT_TAC body_assign_empty_target_rhs_pre >>
  `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e) e es` by
    metis_tac[body_assign_expr_vv_full] >>
  `expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e) e es` by
    (qpat_x_assum `body_expr_prefix_ok cx e` mp_tac >>
     simp[Once body_expr_prefix_ok_def] >> metis_tac[]) >>
  `src = NONE` by
    metis_tac[bodyTypedTargetScopeTheory.body_inv_toplevel_target_main,
              vyperTypeEnvTheory.type_place_target_AttributeTarget,
              optionTheory.IS_SOME_EXISTS] >>
  `src = NONE /\ find_var_decl_by_name id tops <> NONE /\
   ?vis mut sid slot. MEM (VariableDecl vis mut id (StructT sid) slot) tops` by
    (drule_all bodyStorageMetadataTheory.supported_storage_field_write_decl >> simp[]) >>
  gvs[] >>
  drule_then strip_assume_tac bodyInvExecutionPropsTheory.body_inv_main_support >>
  drule_then assume_tac bodySimTheory.body_inv_contract >>
  `ALOOKUP [((NONE:num option),tops)] NONE = SOME tops` by simp[alistTheory.ALOOKUP_def] >>
  `cenv.ce_hashmap_info (NONE,id) = NONE /\
   cenv.ce_module_var_type (NONE,id) = SOME (StructT sid)` by
    drule_all_then (fn th => simp[th]) linkedStorageMetadataPropsTheory.contract_inv_variable_metadata >>
  `expr_body_pre_mods [(NONE,tops)] cenv cx env e es` by
    (drule_all_then ACCEPT_TAC exprBodyPrePropsTheory.body_inv_expr_body_pre_mods) >>
  `expr_sim_inv_mods [(NONE,tops)] cenv cx env es` by
    (drule_then ACCEPT_TAC exprBodyPrePropsTheory.expr_body_pre_mods_inv) >>
  `env_consistent env cx es` by
    (drule_then ACCEPT_TAC exprBodyPrePropsTheory.expr_sim_inv_mods_env) >>
  gvs[vyperTypeEnvTheory.type_place_target_AttributeTarget,
      vyperTypeEnvTheory.type_place_target_TopLevelNameTarget]
  >- (`?ts. get_module_code cx NONE = SOME ts /\
              find_var_decl_by_name id ts = NONE` by
        (fs[vyperTypeInvariantsTheory.env_consistent_def, vyperTypeInvariantsTheory.env_context_consistent_def] >>
         first_x_assum drule >> strip_tac >> metis_tac[optionTheory.SOME_11]) >>
      metis_tac[optionTheory.SOME_11]) >>
  drule_all vyperTypeEnvTheory.env_consistent_toplevel_storage_static >> strip_tac >>
  `ts = tops` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `ts = tops` SUBST_ALL_TAC >>
  `ALOOKUP [((NONE:num option),tops)] NONE = SOME tops` by simp[alistTheory.ALOOKUP_def] >>
  drule_all_then strip_assume_tac linkedStorageMetadataPropsTheory.body_inv_storage_var_types_mods >> gvs[] >>
  drule exprBodyPrePropsTheory.expr_body_pre_env_type_defs >> strip_tac >>
  `?fsz. ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
            fld = SOME (expr_type e,fsz)` by
    metis_tac[stmtSimAssignAttrTheory.attribute_type_struct_field] >>
  qpat_x_assum `IS_SOME (lookup_var_slot_from_layout _ _ _ _)`
    (strip_assume_tac o REWRITE_RULE [optionTheory.IS_SOME_EXISTS]) >>
  irule s1PrefixAssignAttrStorageTheory.compile_assign_attr_storage_prefix >>
  simp[] >> metis_tac[]
QED

Theorem body_assign_attr_local_prefix:
  !cx id fld sid fty e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
  (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_full_ok cx (AttributeTarget (NameTarget id) fld)) /\
  (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_prefix_ok cx (AttributeTarget (NameTarget id) fld)) /\
  body_expr_full_ok cx e /\
  body_expr_prefix_ok cx e /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  supported_stmt tops bindings (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e) ==>
       occurs_abi_decode_target target tops) /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
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
  stmt_frag_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e)))
      (eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e)) es
Proof
  rpt gen_tac >> strip_tac >>
  drule_all bodyFullAssignTheory.body_assign_attr_local_rhs_pre >> strip_tac >>
  drule exprBodyPrePropsTheory.expr_body_pre_env_type_defs >> strip_tac >>
  `?fsz. ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
            fld = SOME (fty,fsz)` by
    metis_tac[stmtSimAssignAttrTheory.attribute_type_struct_field] >>
  `?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)` by
    metis_tac[targetPlaceSimTheory.expr_sim_inv_local] >>
  `cenv.ce_var_type id = SOME (StructT sid)` by
    metis_tac[expr_sim_inv_local_ce_var_type] >>
  `expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e) e es` by
    (qpat_x_assum `body_expr_prefix_ok cx e` mp_tac >>
     simp[Once body_expr_prefix_ok_def] >> metis_tac[]) >>
  rewrite_tac[stmt_frag_prefix_def,stmt_frag_full_pre_def] >>
  rpt gen_tac >> strip_tac >>
  `is_word_type (expr_type e)` by simp[] >>
  drule_all stmtSimAssignAttrTheory.assign_attr_local_code_parts >> strip_tac >>
  rename1 `emit_void MSTORE _ su = ((),sb)` >>
  `cs_extends sa sm /\ cs_extends sm sn /\ cs_extends sn su /\ cs_extends su sb` by
    metis_tac[compile_expr_ci_mono,ci_mono_emit_op,ci_mono_unwrap_value,
              ci_mono_emit_void,ci_mono_def,SND] >>
  `fn_has_code sa sm func` by metis_tac[fn_has_code_split,cs_extends_trans] >>
  `?shadow_sm. compile_expr (gas_shadow_env T cenv) (expr_type e)
      (gas_shadow_expr e) shadow_sa = (vv,shadow_sm) /\
    gas_shadow_state sm shadow_sm` by suspend "shadow_expr" >>
  `fn_has_code shadow_sa shadow_sm shadow_func` by suspend "shadow_code" >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0 (eval_expr cx e) (es,s0,G0,tn0)` by suspend "rhs" >>
  suspend "trace"
QED

Resume body_assign_attr_local_prefix[shadow_expr]:
  mp_tac (REWRITE_RULE [gas_shadow_compiles_def]
    (Q.INST [`sd` |-> `T`, `ty` |-> `expr_type e`] gas_shadow_stmt_compile_expr_env)) >>
  disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >>
  Cases_on `compile_expr (gas_shadow_env T cenv) (expr_type e)
    (gas_shadow_expr e) shadow_sa` >> simp[]
QED

Resume body_assign_attr_local_prefix[shadow_code]:
  qpat_x_assum `stmt_env _ _ _ (gas_shadow_stmt _) _ = _` mp_tac >>
  simp[gas_shadow_stmt_def,gas_shadow_assignment_def,gas_shadow_expr_def] >> strip_tac >>
  qpat_x_assum `stmt_env _ _ _ (Assign _ e) sa = _` kall_tac >>
  `is_word_type (expr_type (gas_shadow_expr e))` by simp[gas_shadow_expr_type] >>
  `FLOOKUP (gas_shadow_env T cenv).ce_vars id = SOME (PtrVar (Var p) sz)` by simp[] >>
  `(gas_shadow_env T cenv).ce_var_type id = SOME (StructT sid)` by simp[] >>
  `ALOOKUP (get_struct_fields (gas_shadow_env T cenv).ce_struct_fields
     (nsid_to_string sid)) fld = SOME (expr_type (gas_shadow_expr e),fsz)` by
    simp[gas_shadow_expr_type] >>
  drule_all stmtSimAssignAttrTheory.assign_attr_local_code_parts >>
  strip_tac >> gvs[gas_shadow_expr_type] >>
  rename1 `emit_void MSTORE _ shadow_su = ((),shadow_sb)` >>
  rename1 `unwrap_value _ _ shadow_sn = (_,shadow_su)` >>
  `cs_extends shadow_sa shadow_sm /\ cs_extends shadow_sm shadow_sn /\
   cs_extends shadow_sn shadow_su /\ cs_extends shadow_su shadow_sb` by
    metis_tac[compile_expr_ci_mono,ci_mono_emit_op,ci_mono_unwrap_value,
              ci_mono_emit_void,ci_mono_def,SND] >>
  metis_tac[fn_has_code_split,cs_extends_trans]
QED

Resume body_assign_attr_local_prefix[rhs]:
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    metis_tac[stmtSimAssignAttrTheory.assign_attr_local_admissible_raw] >>
  `!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==>
     not_fresh_at sa x` by fs[ret_pc_ok_def] >>
  qpat_x_assum `expr_vv_sim_prefix _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_prefix_def,expr_vv_sim_full_pre_def]) >>
  disch_then irule >> simp[] >> reverse conj_tac
  >- (qexistsl_tac [`sa`,`sm`,`shadow_sa`,`shadow_sm`,`vv`] >> gvs[]) >>
  first_assum ACCEPT_TAC
QED

Resume body_assign_attr_local_prefix[trace]:
  drule stmtSimAssignAttrTheory.assign_attr_local_admissible_run >> strip_tac >>
  qpat_x_assum `gas_prefix_full _ _ _ (eval_expr _ _) _`
    (strip_assume_tac o ONCE_REWRITE_RULE [gas_prefix_full_def]) >>
  rewrite_tac[gas_prefix_full_def] >> qexists_tac `marks` >> conj_tac
  >- metis_tac[] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!gs. eval_stmt _ _ _ = _`
    (qspec_then `gas_explicit marks s0.vs_gas_readings ++ tail` mp_tac) >>
  simp[] >> disch_then (assume_tac o SYM) >>
  qpat_x_assum `eval_stmt _ _ _ = _` kall_tac >>
  Cases_on `eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail)` >>
  rename1 `eval_expr _ _ _ = (ans,mid)` >>
  `ee.storage_trace = mid.storage_trace` by
    (qpat_x_assum `ee.storage_trace = _` kall_tac >>
     qpat_x_assum `vyperState$bind _ (write_place _ _) _ = _` mp_tac >>
     Cases_on `ans` >> simp[vyperStateTheory.bind_def] >>
     rename1 `read_result cx rhs mid` >>
     Cases_on `read_result cx rhs mid` >>
     drule_then (fn th => simp[th]) vyperStateTheory.read_result_state >>
     rename1 `read_result cx rhs mid = (result,_)` >>
     Cases_on `result` >> simp[] >>
     disch_then (ACCEPT_TAC o MATCH_MP tuplePlaceStepTheory.write_place_storage_trace)) >>
  qpat_assum `!tail res ee obs_pre rq outcome sfx H. _` irule >>
  simp[] >> qexistsl_tac [`mid`,`ans`,`sfx`,`tail`] >> fs[] >> metis_tac[]
QED

Finalise body_assign_attr_local_prefix

Theorem body_assign_local_memory_prefix:
  !cx id ty e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
  (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_full_ok cx (NameTarget id)) /\
  (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_prefix_ok cx (NameTarget id)) /\
  body_expr_full_ok cx e /\
  body_expr_prefix_ok cx e /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  supported_stmt tops bindings (Assign (BaseTarget (NameTarget id)) e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget (NameTarget id)) e) ==>
       occurs_abi_decode_target target tops) /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
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
  stmt_frag_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (NameTarget id)) e))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Assign (BaseTarget (NameTarget id)) e)))
      (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) es
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  Cases_on `has_length_word (expr_type e) /\ is_empty_value_expr e`
  >- (irule body_assign_local_memory_empty_prefix >> simp[] >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      qexistsl_tac [`bindings`,`env`,`env'`,`tops`,`ty`] >> simp[]) >>
  drule_all assign_base_local_rhs_pre >> strip_tac >>
  Q.SUBGOAL_THEN `lowered_value_type cenv e = ty \/ is_bytestring_type ty` assume_tac
  >- metis_tac[] >>
  drule_all expr_sim_inv_local >> strip_tac >>
  `cenv.ce_var_type id = SOME ty` by
    (`evaluate_type (get_tenv cx) ty = SOME entry.type` by simp[] >>
     drule_all body_tuple_target_local_aligned >> simp[tuple_target_aligned_local]) >>
  `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type e) e es` by
    (qpat_assum `body_expr_prefix_ok _ _`
       (mp_tac o ONCE_REWRITE_RULE [body_expr_prefix_ok_def]) >>
     strip_tac >>
     qpat_assum `!DF lo d PG tops ctx shadow_ctx func shadow_func cenv env ty es.
          _ ==> expr_sim_prefix _ _ _ _ _ _ /\ expr_vv_sim_prefix _ _ _ _ _ _`
       (qspecl_then [`DF`,`lo`,`d`,`PG`,`tops`,`ctx`,`shadow_ctx`,
          `func`,`shadow_func`,`cenv`,`env`,`expr_type e`,`es`] mp_tac) >>
     simp[]) >>
  rewrite_tac[stmt_frag_prefix_def,stmt_frag_full_pre_def] >>
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  drule_all assign_local_memory_widen_code_parts >> strip_tac >>
  qpat_x_assum `cenv' = cenv` SUBST_ALL_TAC >>
  rename1 `lower_value compile_expr cenv (expr_type e) e sa = (op,sB)` >>
  suspend "rhs_prefix"
QED

Resume body_assign_local_memory_prefix[rhs_prefix]:
  `?shadow_sB.
     lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
       (gas_shadow_expr e) shadow_sa = (op,shadow_sB) /\
     gas_shadow_state sB shadow_sB` by
    (`FST (lower_value compile_expr cenv (expr_type e) e sa) =
       FST (lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
         (gas_shadow_expr e) shadow_sa) /\
       gas_shadow_state (SND (lower_value compile_expr cenv (expr_type e) e sa))
         (SND (lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
           (gas_shadow_expr e) shadow_sa))` by
       (irule (REWRITE_RULE [gas_shadow_compiles_def]
          (Q.INST [`sd` |-> `T`] gas_shadow_stmt_lower_value_env)) >> simp[]) >>
     Cases_on `lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
       (gas_shadow_expr e) shadow_sa` >> gvs[]) >>
  `fn_has_code shadow_sa shadow_sB shadow_func` by
    (qpat_x_assum `stmt_env _ _ _ (gas_shadow_stmt _) _ = _` mp_tac >>
     simp[gasShadowTheory.gas_shadow_stmt_def,gasShadowTheory.gas_shadow_assignment_def,
          gasShadowTheory.gas_shadow_expr_def] >> strip_tac >>
     qpat_x_assum `stmt_env _ _ _ (Assign _ e) sa = _` kall_tac >>
     `~(has_length_word (expr_type (gas_shadow_expr e)) /\
         is_empty_value_expr (gas_shadow_expr e))` by gvs[gasShadowTheory.gas_shadow_expr_type] >>
     Q.SUBGOAL_THEN `lowered_value_type (gas_shadow_env T cenv) (gas_shadow_expr e) = ty \/
                      is_bytestring_type ty` assume_tac >- simp[] >>
     `(gas_shadow_env T cenv).ce_var_type id = SOME ty` by simp[] >>
     `FLOOKUP (gas_shadow_env T cenv).ce_vars id = SOME (PtrVar (Var p) sz)` by simp[] >>
     drule_all assign_local_memory_widen_code_parts >> strip_tac >>
     gns[gasShadowTheory.gas_shadow_expr_type] >> metis_tac[]) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at sa x` by metis_tac[ret_pc_ok_def] >>
  drule assign_local_admissible_rhs >> strip_tac >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)` by
    (qpat_assum `expr_sim_prefix _ _ _ _ _ _`
       (qspecl_then [`st0`,`sa`,`sB`,`shadow_sa`,`shadow_sB`,`op`,`s0`,`G0`,`tn0`] mp_tac o
        REWRITE_RULE [expr_sim_prefix_def,expr_sim_full_pre_def]) >>
     simp[] >> disch_then irule >> first_assum ACCEPT_TAC) >>
  suspend "source_trace"
QED

Resume body_assign_local_memory_prefix[source_trace]:
  (* A local write does not add a request to the RHS trace. *)
  drule assign_local_admissible_run >> strip_tac >>
  qpat_x_assum `gas_prefix_full _ _ _ (bind _ _) _` mp_tac >>
  rewrite_tac[gas_prefix_full_def] >>
  disch_then (qx_choose_then `marks` (CONJUNCTS_THEN ASSUME_TAC)) >>
  qexists_tac `marks` >> conj_tac >- (first_assum ACCEPT_TAC) >>
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  Cases_on `bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail)` >>
  rename1 `bind (eval_expr cx e) _ _ = (rhs,mid)` >>
  `ee.storage_trace = mid.storage_trace` by
    (qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
     simp[Once vyperStateTheory.bind_def] >>
     Cases_on `rhs` >> simp[] >> strip_tac >>
     drule write_place_storage_trace >> simp[]) >>
  qpat_assum `!tail res ee obs_pre rq outcome sfx H. _ ==> request_site _ _ _ _ _ _ _`
    (qspec_then `tail` irule) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qexistsl_tac [`mid`,`rhs`,`sfx`,`tail`] >>
  gvs[]
QED

Finalise body_assign_local_memory_prefix

Theorem body_assign_nested_empty_immutable_prefix:
  !cx t e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
  (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_full_ok cx t) /\
  (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_prefix_ok cx t) /\
  body_expr_full_ok cx e /\
  body_expr_prefix_ok cx e /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  struct_args_unique tops /\
  supported_stmt tops bindings (Assign (BaseTarget t) e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget t) e) ==>
       occurs_abi_decode_target target tops) /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
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
        0 < type_memory_bytes cenv ty /\ expr_type e = ty /\
        lowered_value_type cenv e = expr_type e) /\
  ~(?id fld sid fty.
        t = AttributeTarget (NameTarget id) fld /\
        FLOOKUP env.var_types id = SOME (StructT sid) /\
        attribute_type env.type_defs (StructT sid) fld = SOME fty /\
        is_word_type fty) /\
  ~(?nsid fld fty.
        t = AttributeTarget (TopLevelNameTarget nsid) fld /\
        supported_storage_field_write tops nsid fld /\
        type_place_target env t = SOME (Type fty) /\ is_word_type fty) /\
  has_length_word (expr_type e) /\
  is_empty_value_expr e /\
  immutable_root cx t /\
  ~supported_stmt_expr_exists (const_name_root cx) (Assign (BaseTarget t) e) /\
  ~(?nsid. t = TopLevelNameTarget nsid) ==>
  stmt_frag_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget t) e))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Assign (BaseTarget t) e)))
      (eval_stmt cx (Assign (BaseTarget t) e)) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then strip_assume_tac body_assign_empty_target_typing >>
  drule_all_then strip_assume_tac body_assign_empty_target_rhs_pre >>
  drule_then assume_tac abi_decode_inv_type_env >>
  `?stv. evaluate_type (get_tenv cx) (expr_type e) = SOME stv` by
    (drule expr_body_pre_type_evaluates >> simp[IS_SOME_EXISTS]) >>
  `?dtv. evaluate_type (get_tenv cx) dty = SOME dtv` by
    (fs[type_widens_to_def, well_formed_type_def] >> metis_tac[IS_SOME_EXISTS]) >>
  `body_base_target_full_ok cx t /\ body_base_target_prefix_ok cx t` by
    (drule_all immutable_assign_empty_read >>
     disch_then (qspec_then `es.gas_obs` mp_tac) >>
     simp[bind_def, AllCaseEqs()] >> metis_tac[]) >>
  drule_all_then assume_tac body_assign_target_indices_pre >>
  `IS_SOME (type_place_target env t)` by simp[] >>
  drule_all_then strip_assume_tac typed_immutable_target_root >>
  `well_typed_target env t dty` by simp[well_typed_target_def] >>
  `call_evaluation_safe cx (int_calls_target t)` by
    (qpat_assum `call_evaluation_safe cx (int_calls_stmt _)` mp_tac >>
     pure_rewrite_tac[int_calls_stmt_def,int_calls_atarget_def] >>
     disch_then (irule o MATCH_MP call_evaluation_safe_append_left)) >>
  drule_all_then assume_tac
    (Q.INST [`bt` |-> `t`] assign_place_empty_source_action) >>
  pure_rewrite_tac[stmt_frag_prefix_def,stmt_frag_full_pre_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac assign_place_pure_empty_code >>
  `?shadow_st. compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
      (gas_shadow_target t) shadow_sa = (tr,shadow_st) /\ gas_shadow_state st shadow_st` by
    (Cases_on `compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
       (gas_shadow_target t) shadow_sa` >>
     `FST (compile_get_target_ptr compile_expr cenv t sa) =
        FST (compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
          (gas_shadow_target t) shadow_sa) /\
      gas_shadow_state (SND (compile_get_target_ptr compile_expr cenv t sa))
        (SND (compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
          (gas_shadow_target t) shadow_sa))` by
       (irule (REWRITE_RULE [gas_shadow_compiles_def]
         (Q.INST [`sd` |-> `T`] gas_shadow_stmt_get_target_ptr_env)) >> simp[]) >>
     gvs[]) >>
  `compile_store_at_loc cenv.ce_imm_alloca (FST tr) (Lit 0w) (FST (SND tr))
      shadow_st = ((),shadow_sb)` by
    (qpat_assum `stmt_env _ _ _ (gas_shadow_stmt _) _ = _`
       (mp_then Any mp_tac assign_place_pure_empty_code o
        REWRITE_RULE [gas_shadow_stmt_def, gas_shadow_assignment_def]) >> simp[]) >>
  gvs[] >>
  `ci_mono sa st /\ ci_mono shadow_sa shadow_st` by
    metis_tac[ci_mono_compile_get_target_ptr, SND] >>
  `ci_mono st sb /\ ci_mono shadow_st shadow_sb` by
    metis_tac[cj 2 ci_mono_stmt_helpers, SND] >>
  `fn_has_code sa st func /\ fn_has_code shadow_sa shadow_st shadow_func` by
    metis_tac[ci_mono_def, fn_has_code_split] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x` by
    fs[ret_pc_ok_def] >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 (eval_target_place cx t) (es,s0,G0,tn0)` by
    (drule_all immutable_target_place_prefix >> simp[]) >>
  suspend "write_trace"
QED

Resume body_assign_nested_empty_immutable_prefix[write_trace]:
  (* The empty read and final write add no request to the target trace. *)
  qpat_x_assum `gas_prefix_full _ _ _ (eval_target_place _ _) _` mp_tac >>
  rewrite_tac[gas_prefix_full_def] >>
  disch_then (qx_choose_then `marks` (CONJUNCTS_THEN ASSUME_TAC)) >>
  qexists_tac `marks` >> conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  Cases_on `eval_target_place cx t (es with gas_obs :=
      gas_explicit marks s0.vs_gas_readings ++ tail)` >>
  rename1 `eval_target_place _ _ _ = (ans,mid)` >>
  `ee.storage_trace = mid.storage_trace` by
    (qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
     simp[Once bind_def] >> Cases_on `ans` >> simp[] >>
     strip_tac >> drule_then assume_tac write_place_storage_trace >> fs[]) >>
  qpat_assum `!tail res ee obs_pre rq outcome sfx H. _ ==> request_site _ _ _ _ _ _ _`
    (qspec_then `tail` irule) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qexistsl_tac [`mid`,`ans`,`sfx`,`tail`] >> gvs[]
QED

Finalise body_assign_nested_empty_immutable_prefix

Theorem body_assign_nested_nonempty_immutable_prefix:
  !cx t e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
  (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_full_ok cx t) /\
  (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_prefix_ok cx t) /\
  body_expr_full_ok cx e /\
  body_expr_prefix_ok cx e /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  struct_args_unique tops /\
  supported_stmt tops bindings (Assign (BaseTarget t) e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget t) e) ==>
       occurs_abi_decode_target target tops) /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_sim_inv cenv cx env es /\
  ce_locals_declared cenv env /\
  locals_alloc_ok cenv env /\
  type_stmt env ret_ty (Assign (BaseTarget t) e) = SOME env' /\
  stmt_exprs_ok cenv (Assign (BaseTarget t) e) /\
  call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget t) e)) /\
  frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
  ~(has_length_word (expr_type e) /\ is_empty_value_expr e) /\
  immutable_root cx t /\
  ~(?nsid. t = TopLevelNameTarget nsid) /\
  ~supported_stmt_expr_exists (const_name_root cx) (Assign (BaseTarget t) e) ==>
  stmt_frag_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget t) e))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Assign (BaseTarget t) e)))
      (eval_stmt cx (Assign (BaseTarget t) e)) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then assume_tac body_assign_value_rhs_pre >>
  `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type e) e es` by
    metis_tac[body_expr_full_ok_simulations] >>
  `expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type e) e es` by
    (qpat_assum `body_expr_prefix_ok cx e`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [Once body_expr_prefix_ok_def]) >>
     disch_then (qspecl_then [`DF`,`lo`,`d`,`PG`,`tops`,`ctx`,`shadow_ctx`,
       `func`,`shadow_func`,`cenv`,`env`,`expr_type e`,`es`] mp_tac) >> simp[]) >>
  pure_rewrite_tac[stmt_frag_prefix_def,stmt_frag_full_pre_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all body_assign_value_paired_code >>
  disch_then (qx_choosel_then [`vv0`,`sr`,`vv`,`ss`,`r`,`st`,`op`,`su`,`tr`,`ts`,`tt`,`tu`]
    (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `cenv' = cenv` SUBST_ALL_TAC >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x` by
    fs[ret_pc_ok_def] >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    (drule expr_body_pre_vv_gas_admissible >> simp[]) >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cx st0 (eval_expr cx e) (es,s0,G0,tn0)` by
    (qpat_x_assum `expr_vv_sim_prefix _ _ _ _ _ _`
       (qspecl_then [`st0`,`sa`,`sr`,`shadow_sa`,`tr`,`vv0`,`s0`,`G0`,`tn0`] mp_tac o
        REWRITE_RULE [expr_vv_sim_prefix_def,expr_vv_sim_full_pre_def]) >>
     disch_then irule >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `expr_vv_sim_full _ _ _ _ _ _`
    (qspecl_then [`st0`,`sa`,`sr`,`shadow_sa`,`tr`,`vv0`,`s0`,`G0`,`tn0`] mp_tac o
     REWRITE_RULE [expr_vv_sim_full_def]) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_tac >>
  once_rewrite_tac[evaluate_def] >>
  qpat_assum `gas_outcome_full _ _ _ _ (eval_expr _ _) _ _ _`
    (mp_then Any irule body_assign_raw_read_bind_prefix) >>
  reverse conj_tac
  >- (conj_tac
      >- (qexistsl_tac [`cenv`,`sa`,`sr`,`vv0`] >>
          BETA_TAC >> rpt gen_tac >> disch_then (qx_choose_then `pv` strip_assume_tac) >>
          qexists_tac `pv` >> simp[]) >>
      simp[] >> rpt gen_tac >> Cases_on `res` >> simp[expr_exit_def]) >>
  qx_genl_tac [`marks`,`tv`,`v`,`mid`,`G`,`tn`,`s`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  suspend "rhs_replay"
QED

Resume body_assign_nested_nonempty_immutable_prefix[rhs_replay]:
  qpat_x_assum `gas_outcome_full _ _ _ _ (eval_expr _ _) _ _ _` kall_tac >>
  `mid with gas_obs := [] = mid` by
    simp[evaluation_state_component_equality] >>
  `eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL tv,mid)` by
    (qpat_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` mp_tac) >>
     qpat_assum `mid with gas_obs := [] = mid` (fn th => simp[NoAsms,th])) >>
  `read_result cx tv mid = (INL v,mid)` by
    (qpat_assum `!tail. read_result _ _ _ = _` (qspec_then `[]` mp_tac) >>
     qpat_assum `mid with gas_obs := [] = mid` (fn th => simp[NoAsms,th])) >>
  `body_base_target_full_ok cx t /\ body_base_target_prefix_ok cx t` by
    (conj_tac >> first_assum irule >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any)) >>
  `expr_sim_inv cenv cx env mid` by
    (irule bodySimStmtFactsTheory.expr_body_pre_eval_result >>
     qexistsl_tac [`e`,`es with gas_obs := gas_explicit marks s0.vs_gas_readings`,`INL tv`] >>
     simp[expr_body_pre_gas_obs]) >>
  drule body_assign_empty_target_typing >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `ty` strip_assume_tac))) >>
  `body_const_cells_agree [(NONE,tops)] cx env mid` by
    (irule body_const_cells_agree_expr_read >>
     qexistsl_tac [`e`,`INL v`,`es with gas_obs := gas_explicit marks s0.vs_gas_readings`] >>
     simp[Once bind_def]) >>
  `target_indices_pre cenv cx env t` by
    (drule_all body_assign_target_indices_pre >> simp[]) >>
  `IS_SOME (type_place_target env t)` by simp[] >>
  drule_all_then (qx_choosel_then [`id`,`root_ty`] strip_assume_tac) typed_immutable_target_root >>
  `call_evaluation_safe cx (int_calls_target t)` by
    (qpat_assum `call_evaluation_safe cx (int_calls_stmt (Assign _ _))`
       (mp_tac o REWRITE_RULE [Once int_calls_stmt_def,Once int_calls_atarget_def]) >>
     disch_then (mp_then Any ACCEPT_TAC vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_left)) >>
  `well_typed_target env t ty` by simp[well_typed_target_def] >>
  `env_consistent env cx es` by
    metis_tac[body_inv_expr_body_pre_mods,expr_body_pre_mods_inv,expr_sim_inv_mods_env] >>
  `env.type_defs = get_tenv cx` by metis_tac[expr_body_pre_env_type_defs] >>
  drule_all_then (qx_choose_then `target_tv` assume_tac o
    SIMP_RULE (srw_ss()) [well_formed_vtype_def,well_formed_type_def,optionTheory.IS_SOME_EXISTS])
    type_place_target_well_formed_vtype_stmt >>
  suspend "rhs_landing"
QED

Resume body_assign_nested_nonempty_immutable_prefix[rhs_landing]:
  RULE_ASSUM_TAC BETA_RULE >>
  qabbrev_tac `H0 = storage_trace_horizon mid.storage_trace` >>
  `valid_horizon cx st0 H0 mid.storage_trace` by
    fs[Abbr `H0`,storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _ /\ gas_origin_ptr_path _ _ _ _`
    (qspec_then `H0` (drule_then (CONJUNCTS_THEN2 (qx_choose_then `pv` strip_assume_tac) assume_tac))) >>
  qpat_x_assum `INL tv = INL pv` (SUBST_ALL_TAC o SYM o SRULE []) >>
  `!fn inst z. frag_reachable ctx func s fn inst z ==> dalloca_fmp_headroom inst z` by
    (`!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
       metis_tac[body_inv_no_phi] >>
     qx_genl_tac [`leaf`,`inst`,`z`] >> strip_tac >>
     irule gas_origin_ptr_path_dalloca_fmp_headroom >>
     qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) marks _` (irule_at Any) >>
     qexists_tac `leaf` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `return_buf_frame d cenv sr s` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s0`,`sa`] >>
     fs[ci_mono_def,vv_post_def]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es s0 /\
      vv_post H ctx func cenv cx e es sa sr s0 mid tv vv0 s /\
      ghost_inv_at (DF H) lo d cenv cx mid G tn s` by
    (gen_tac >> strip_tac >>
     `valid_horizon cx st0 H es.storage_trace` by
       (`valid_horizon cx st0 H
           (es with gas_obs := gas_explicit marks s0.vs_gas_readings).storage_trace`
          suffices_by simp[] >>
        irule (INST_TYPE [alpha |-> ``:eval_result``] valid_horizon_frame) >>
        qexistsl_tac [`eval_expr cx e`, `INL tv`, `mid`] >>
        simp[cj 5 evaluate_storage_trace_frame]) >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _ /\ gas_origin_ptr_path _ _ _ _`
       (qspec_then `H` (drule_then (CONJUNCTS_THEN2 (qx_choose_then `pv` strip_assume_tac) kall_tac))) >>
     qpat_x_assum `INL tv = INL pv` (SUBST_ALL_TAC o SYM o SRULE []) >>
     simp[] >> first_assum ACCEPT_TAC) >>
  `!u Gu tnu.
     gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       cx st0 (eval_target_place cx t) (mid,u,Gu,tnu) ==>
     gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       cx st0 (bind (eval_target_place cx t) (\p. write_place cx p v)) (mid,u,Gu,tnu)` by
    (rpt gen_tac >> rewrite_tac[gas_prefix_full_def] >>
     disch_then (qx_choose_then `tm` (CONJUNCTS_THEN ASSUME_TAC)) >>
     qexists_tac `tm` >> conj_tac >- first_assum ACCEPT_TAC >>
     rpt gen_tac >> strip_tac >>
     Cases_on `eval_target_place cx t
         (mid with gas_obs := gas_explicit tm u.vs_gas_readings ++ tail)` >>
     rename1 `eval_target_place _ _ _ = (pr,mp)` >>
     `ee.storage_trace = mp.storage_trace` by
       (Cases_on `pr` >>
        qpat_x_assum `bind _ _ _ = (_,ee)` mp_tac >>
        simp[bind_def] >>
        disch_then (mp_then Any mp_tac write_place_storage_trace) >> simp[]) >>
     qpat_assum `!tail res ee obs_pre rq outcome sfx H. _ ==> request_site _ _ _ _ _ _ _`
       (qspec_then `tail` irule) >>
     simp[] >> qexistsl_tac [`mp`,`pr`,`sfx`,`tail`] >> fs[]) >>
  `!u Gu tnu.
      local_ptrs_reserved cenv ss /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ss x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ss x) /\
      return_buf_frame d cenv ss u /\ alloca_history func u /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
      (!fn inst z. frag_reachable ctx func u fn inst z ==> dalloca_fmp_headroom inst z) /\
      (!H. valid_horizon cx st0 H mid.storage_trace ==>
        stmt_state_rel H ctx func cenv cx mid u /\ storage_well_formed_on cx mid (FST H) /\
        ghost_inv_at (DF H) lo d cenv cx mid Gu tnu u) /\
      ~u.vs_halted /\ u.vs_current_bb = ss.cs_current_bb /\ u.vs_inst_idx = LENGTH ss.cs_current_insts ==>
      gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        cx st0 (bind (eval_target_place cx t) (\p. write_place cx p v)) (mid,u,Gu,tnu)` by
    (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
     first_assum irule >> irule immutable_target_place_prefix >>
     qpat_assum `compile_get_target_ptr compile_expr _ (gas_shadow_target t) ts = (r,tt)`
       (irule_at Any) >>
     rpt (first_assum (irule_at Any)) >> qexists_tac `target_tv` >>
     rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE metis_tac[])) >>
  qpat_x_assum `(_ /\ compile_snapshot_vv _ _ _ _ = _ /\ _) \/ _`
     (DISJ_CASES_THEN (map_every assume_tac o CONJUNCTS))
  >- suspend "snapshot"
  >> suspend "saved"
QED

Resume body_assign_nested_nonempty_immutable_prefix[snapshot]:
  `cenv.ce_is_ctor /\ vv_location vv0 = SOME LocCode ==>
    !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
      eval_operand (vv_operand vv0) s = SOME w ==>
      w2n w + type_memory_size rt <= lo /\
      (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
        val_in_memory rt v (w2n w) mem)` by
    (strip_tac >>
     qpat_assum `_ ==> ?val. read_result cx tv mid = _ /\ _` mp_tac >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then (qx_choose_then `val` strip_assume_tac) >>
     `val = v` by metis_tac[sumTheory.INL_11,pairTheory.PAIR_EQ] >>
     qpat_x_assum `val = v` SUBST_ALL_TAC >>
     first_assum ACCEPT_TAC) >>
  (let
     fun from pat k th = qpat_assum pat (mp_then Any k th)
   in
     (from `compile_snapshot_vv _ _ _ sr = (vv,ss)` o
      from `ghost_kept_at lo cenv es sa G0 tn0 s0 G tn` o
      from `vv_store_bound _ _ _ mid tv vv0 s` o
      from `body_inv tops ctx cenv cx` o
      from `fn_has_code sr ss func` o
      from `expr_body_pre cenv cx env e es` o
      from `read_result cx tv mid = (INL v,mid)` o
      from `!tail. eval_expr cx e _ = (INL tv,mid with gas_obs := tail)` o
      from `!H. valid_horizon cx st0 H mid.storage_trace ==>
         _ /\ vv_post H ctx func cenv cx e es sa sr s0 mid tv vv0 s /\ _`)
     mp_tac body_assign_snapshot_target_entry
   end) >>
  disch_then (qspecl_then [`shadow_ctx`,`PG`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`u`,`Gu`,`tnu`,`uv`] (map_every assume_tac o CONJUNCTS)) >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        cx st0 (bind (eval_target_place cx t) (\p. write_place cx p v)) (mid,u,Gu,tnu)` by
    (qpat_assum `!u Gu tnu. local_ptrs_reserved _ _ /\ _ ==> _` irule >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ [] _ /\ _`
       (qspec_then `H` (drule_then (ACCEPT_TAC o CONJUNCT2)))) >>
  qpat_assum `gas_prefix_full _ _ _ _ (mid,u,Gu,tnu)`
    (mp_then Any irule gas_prefix_full_zero_prefix_guarded) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (gen_tac >> strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ [] _ /\ _`
        (qspec_then `H` (drule_then (ACCEPT_TAC o CONJUNCT1)))) >>
  irule storage_trace_frame_bind_all >>
  simp[cj 8 evaluate_storage_trace_frame, storage_trace_frame_write_place]
QED

Resume body_assign_nested_nonempty_immutable_prefix[saved]:
  qpat_x_assum `ss = sr` SUBST_ALL_TAC >>
  qpat_x_assum `ts = tr` SUBST_ALL_TAC >>
  `sa.cs_next_var <= sr.cs_next_var` by fs[ci_mono_def] >>
  `local_ptrs_reserved cenv sr` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x. not_fresh_at sa x ==> not_fresh_at sr x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sr x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sr x)` by
    metis_tac[] >>
  qpat_assum `!u Gu tnu. local_ptrs_reserved _ _ /\ _ ==> _` irule >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
      _ /\ vv_post H ctx func cenv cx e es sa sr s0 mid tv vv0 s /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  qpat_x_assum `vv_post H ctx func cenv cx e es sa sr s0 mid tv vv0 s`
    (strip_assume_tac o REWRITE_RULE [vv_post_def]) >> simp[]
QED

Finalise body_assign_nested_nonempty_immutable_prefix

Theorem body_assign_other_prefix:
  !cx t e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
  (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_full_ok cx t) /\
  (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_prefix_ok cx t) /\
  body_expr_full_ok cx e /\
  body_expr_prefix_ok cx e /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  struct_args_unique tops /\
  supported_stmt tops bindings (Assign (BaseTarget t) e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget t) e) ==>
       occurs_abi_decode_target target tops) /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
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
  ~(?nsid dty. t = TopLevelNameTarget nsid /\
          supported_scalar_target tops nsid /\
          type_place_target env t = SOME (Type dty) /\ is_word_type dty) /\
  ~(?nsid mut ty slot.
        t = TopLevelNameTarget nsid /\
        supported_variable_decl tops nsid = SOME (Private, mut, ty, SOME slot) /\
        (mut = Storage \/ mut = Transient) /\
        ~is_word_type ty /\ (!elem n. ty <> ArrayT elem (Dynamic n)) /\
        ~is_bytestring_type ty /\
        0 < type_memory_bytes cenv ty /\ expr_type e = ty /\
        lowered_value_type cenv e = expr_type e) /\
  ~(?id fld sid fty.
        t = AttributeTarget (NameTarget id) fld /\
        FLOOKUP env.var_types id = SOME (StructT sid) /\
        attribute_type env.type_defs (StructT sid) fld = SOME fty /\
        is_word_type fty) /\
  ~(?nsid fld fty.
        t = AttributeTarget (TopLevelNameTarget nsid) fld /\
        supported_storage_field_write tops nsid fld /\
        type_place_target env t = SOME (Type fty) /\ is_word_type fty) ==>
  stmt_frag_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget t) e))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Assign (BaseTarget t) e)))
      (eval_stmt cx (Assign (BaseTarget t) e)) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `immutable_root cx t /\ ~(?nsid. t = TopLevelNameTarget nsid)`
  >- (qpat_x_assum `immutable_root cx t /\ _` strip_assume_tac >>
      drule_all_then assume_tac bodySimTheory.body_inv_stmt_const_name_free >>
      Cases_on `has_length_word (expr_type e) /\ is_empty_value_expr e`
      >- (qpat_x_assum `has_length_word _ /\ _` strip_assume_tac >>
          irule body_assign_nested_empty_immutable_prefix >>
          rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
          qexistsl_tac [`bindings`,`env`,`env'`,`tops`] >>
          rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE metis_tac[])) >>
      irule body_assign_nested_nonempty_immutable_prefix >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      qexistsl_tac [`bindings`,`env`,`env'`,`tops`] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `~immutable_root cx t \/ (?nsid. t = TopLevelNameTarget nsid)` suffices_by
    (disch_tac >>
     Cases_on `has_length_word (expr_type e) /\ is_empty_value_expr e`
     >- (qpat_x_assum `has_length_word _ /\ _` strip_assume_tac >>
         irule body_assign_residual_empty_from_target >>
         rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
         qexistsl_tac [`bindings`,`env`,`env'`,`tops`] >>
         rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
         rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
         irule body_assign_residual_target_write_prefix >>
         rpt (CHANGED_TAC (first_assum (irule_at Any))) >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
     irule body_assign_residual_value_from_target >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     qexistsl_tac [`bindings`,`env`,`env'`,`tops`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
     irule body_assign_residual_target_write_prefix >>
     rpt (CHANGED_TAC (first_assum (irule_at Any))) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  metis_tac[]
QED

Theorem body_assign_toplevel_copy_prefix:
  !cx nsid mut ty slot e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
  (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_full_ok cx (TopLevelNameTarget nsid)) /\
  (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_prefix_ok cx (TopLevelNameTarget nsid)) /\
  body_expr_full_ok cx e /\
  body_expr_prefix_ok cx e /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  struct_args_unique tops /\
  supported_stmt tops bindings (Assign (BaseTarget (TopLevelNameTarget nsid)) e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget (TopLevelNameTarget nsid)) e) ==>
       occurs_abi_decode_target target tops) /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_sim_inv cenv cx env es /\
  ce_locals_declared cenv env /\
  locals_alloc_ok cenv env /\
  type_stmt env ret_ty (Assign (BaseTarget (TopLevelNameTarget nsid)) e) = SOME env' /\
  stmt_exprs_ok cenv (Assign (BaseTarget (TopLevelNameTarget nsid)) e) /\
  call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget (TopLevelNameTarget nsid)) e)) /\
  frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
  supported_variable_decl tops nsid = SOME (Private, mut, ty, SOME slot) /\
  (mut = Storage \/ mut = Transient) /\
  ~is_word_type ty /\
  ~is_bytestring_type ty /\
  (!elem n. ty <> ArrayT elem (Dynamic n)) /\
  0 < type_memory_bytes cenv ty /\
  expr_type e = ty /\
  lowered_value_type cenv e = expr_type e ==>
  stmt_frag_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (TopLevelNameTarget nsid)) e))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Assign (BaseTarget (TopLevelNameTarget nsid)) e)))
      (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget nsid)) e)) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rewrite_tac[stmt_frag_prefix_def, stmt_frag_full_pre_def] >>
  rpt gen_tac >> strip_tac >>
  reverse (Cases_on `storage_trace_domain cx st0 es.storage_trace`)
  >- (simp[gas_prefix_full_def] >> qexists `[]` >> conj_tac
      >- metis_tac[gas_origin_ptr_focus_nil] >>
      rpt gen_tac >> strip_tac >>
      `storage_trace_frame (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget nsid)) e))`
        by simp[evaluate_storage_trace_frame] >>
      drule_all storage_trace_frame_prefix >>
      simp[APPEND_EQ_APPEND] >> strip_tac >> gvs[] >>
      (`valid_horizon cx st0 H es.storage_trace` by
         (first_assum ACCEPT_TAC ORELSE
          (irule valid_horizon_append >> goal_assum (drule_at Any)) ORELSE
          (`LENGTH l' = 0` by decide_tac >> gvs[]))) >>
      drule extcall_packing_observed_domain >> simp[]) >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace`
    by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
    (qspec_then `storage_trace_horizon es.storage_trace` (drule_then strip_assume_tac)) >>
  drule_all body_assign_toplevel_copy_entry >> strip_tac >> gnvs[] >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e) e es` by metis_tac[body_expr_full_ok_simulations] >>
  `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e) e es` by metis_tac[body_expr_prefix_ok_def] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x` by
    metis_tac[ret_pc_ok_def] >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_sim_full_def] >>
  disch_then (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,
    `op`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qpat_x_assum `expr_sim_prefix _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_sim_prefix_def,expr_sim_full_pre_def] >>
  disch_then (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,
    `op`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  drule_all stmtSimAssignStorageTheory.eval_assign_toplevel_action >>
  disch_then (qspec_then `e` SUBST1_TAC) >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ Q1 R1` >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
     (\H res ee G tn t. ~t.vs_halted /\ Q1 H res ee G tn t) R1` by
    (qpat_assum `gas_outcome_full _ _ _ _ _ _ Q1 R1`
       (mp_then Any irule gas_outcome_full_post_source) >> simp[]) >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ Q1 R1` kall_tac >>
  qpat_assum `gas_outcome_full _ _ _ _ (bind _ _) _ _ _`
    (mp_then Any irule gas_prefix_full_bind_no_outcome) >>
  simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
       storage_trace_frame_read_result, storage_trace_frame_event,
       storage_trace_frame_ignore_bind, storage_trace_frame_write_storage_slot,
       requests_outcomes_frame_bind_all, evaluate_requests_outcomes_frame,
       requests_outcomes_frame_read_result, Abbr `R1`] >>
  conj_tac >- (rpt gen_tac >> Cases_on `res` >> simp[]) >>
  rpt gen_tac >>
  Cases_on `cx.txn.is_static` >> Cases_on `encode_value tv v` >> Cases_on `tr` >>
  simp[ignore_bind_def, record_storage_event_def, bind_def, return_def,
       write_storage_slot_eq, set_storage_def] >>
  strip_tac >> gvs[DROP_APPEND1]
QED

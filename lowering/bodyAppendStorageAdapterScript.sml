(* Body-side discharge for primitive storage Append. *)
Theory bodyAppendStorageAdapter
Ancestors
  supportedExprTraverse supportedExprs loweringPosts exprLowering vyperAST allocLimits allocLimitsProps
  vyperTyping valueEncodingTyping exprSimProps
  stmtSimDefs exprSimSource exprSimHypsDefs
  bodyAppendStorageFacts bodyExprPreFacts stmtSimAppendStorageCompose
  stmtSimAssignStorageFacts bodySim supportedStmts supportedStmtTraverse
  vyperStorageLayoutSafety vyperTypeSystem vyperTypeValues compileEnv loweringStateRelDefs
  vyperTypeCallGraph vyperState vyperInterpreter
  vyperTypeInvariants vyperTypeExprSoundness vyperTypeExprResult
  supportedDecls supportedTypes vyperValue bodyStorageMetadata
  gasOutcome gasStorage gasSummary vyperStorageTrace vyperStorageFootprint
Libs
  monadsyntax

Theorem body_append_expr_pre:
  body_stmt_safe tops (Append (TopLevelNameTarget nid) e) /\
  body_inv tops ctx cenv cx /\ supported_expr tops e /\
  expr_sim_inv cenv cx env es /\ well_typed_expr env e /\
  stmt_exprs_ok cenv (Append (TopLevelNameTarget nid) e) /\
  call_evaluation_safe cx (int_calls_stmt (Append (TopLevelNameTarget nid) e)) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
              (Append (TopLevelNameTarget nid) e) ==>
            occurs_abi_decode_target target tops) ==>
  expr_body_pre cenv cx env e es
Proof
  strip_tac >> qpat_assum `body_stmt_safe _ _` (strip_assume_tac o
    SIMP_RULE std_ss [body_stmt_safe_def, supported_stmt_expr_exists_def,
      supported_assignment_exists_def, supported_iterator_exists_def,
      supported_assert_exists_def, supported_raise_exists_def,
      supported_expr_exists_def, int_calls_stmt_def, int_calls_atarget_def,
      int_calls_iterator_def, int_calls_assert_reason_def, int_calls_raise_reason_def,
      listTheory.EVERY_APPEND, listTheory.EVERY_CONJ,
      DE_MORGAN_THM, GSYM expr_has_evm_run_def]) >>
  qpat_assum `stmt_exprs_ok _ _` (strip_assume_tac o
    SIMP_RULE std_ss [stmt_exprs_ok_def, alloc_limits_stmt_def,
      alloc_limits_iterator_def, alloc_limits_assert_def, alloc_limits_raise_def,
      alloc_limits_expr_def]) >>
  imp_res_tac alloc_limits_expr_not_extcode >>

  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    fs[body_inv_def] >>
  `cx_tops cx = tops` by simp[gasContextTheory.cx_tops_def] >>
  irule stmt_expr_body_pre >>
  gvs[stmt_exprs_ok_flat, supported_stmt_expr_exists_def,
      supportedExprTraverseTheory.supported_expr_exists_def,
      int_calls_stmt_def, int_calls_expr_def, body_inv_def] >>
  rpt conj_tac
  >~ [`call_evaluation_safe`] >- (qexists_tac `[]` >> simp[]) >>
  metis_tac[]
QED

Theorem body_append_word_encoding:
  expr_body_pre cenv cx env e es /\ is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  (do result <- eval_expr cx e; read_result cx result od) es = (INL v,es1) ==>
  encode_value tv v = SOME [(0,typed_val_to_w256 tv v)]
Proof
  strip_tac >> drule_all expr_body_pre_eval >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    fs[expr_body_pre_def, expr_sim_inv_def, env_consistent_def,
       env_context_consistent_def] >>
  gvs[expr_result_typed_def, expr_runtime_typed_def, value_result_typed_def] >>
  metis_tac[encode_value_word_typed]
QED

Theorem stmt_frag_storage_rel_discharge[local]:
  storage_trace_frame source /\
  ((storage_vars_rel cenv cx /\ transient_vars_rel cenv cx) ==>
    stmt_frag ctx func cx lctx RetQ cenv m source es) ==>
  stmt_frag ctx func cx lctx RetQ cenv m source es
Proof
  strip_tac >>
  rewrite_tac[stmtSimDefsTheory.stmt_frag_def,
              stmtSimDefsTheory.stmt_framed_frag_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx`
  >- (qpat_x_assum `_ ==> stmt_frag _ _ _ _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [stmtSimDefsTheory.stmt_frag_def,
                                stmtSimDefsTheory.stmt_framed_frag_def]) >>
      simp[] >> metis_tac[]) >>
  `~storage_trace_domain cx st0 es.storage_trace` by
    (strip_tac >>
     fs[storage_trace_domain_def] >>
     `stmt_state_rel (storage_trace_horizon es.storage_trace)
        ctx func cenv cx es s0` by metis_tac[] >>
     fs[exprLoweringPropsTheory.stmt_state_rel_def, state_rel_def]) >>
  simp[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  irule gas_bad_storage_at_initial >> simp[]
QED

Theorem body_append_storage_fragment:
  body_stmt_safe tops (Append (TopLevelNameTarget (src,id)) e) /\
  (!s p t. eval_target_place cx (TopLevelNameTarget (src,id)) s = (INL p,t) ==>
             body_expr_ok cx e) /\
  body_inv tops ctx cenv cx /\ supported_storage_dynamic_array tops (src,id) /\
  supported_expr tops e /\ expr_sim_inv cenv cx env es /\
  type_stmt env ret_ty (Append (TopLevelNameTarget (src,id)) e) = SOME env' /\
  stmt_exprs_ok cenv (Append (TopLevelNameTarget (src,id)) e) /\
  call_evaluation_safe cx (int_calls_stmt (Append (TopLevelNameTarget (src,id)) e)) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
              (Append (TopLevelNameTarget (src,id)) e) ==>
            occurs_abi_decode_target target tops) ==>
  stmt_frag ctx func cx lctx RetQ cenv
    (stmt_env cenv lctx ret_ty (Append (TopLevelNameTarget (src,id)) e))
    (eval_stmt cx (Append (TopLevelNameTarget (src,id)) e)) es
Proof
  strip_tac >> drule_all body_append_target_bounds >> strip_tac >>
  drule append_typing_target >> strip_tac >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  `cenv.ce_hashmap_info (src,id) = NONE` by
    (drule supported_append_storage_decl >> strip_tac >>
     drule_all body_append_root_metadata >> simp[]) >>
  drule_all body_append_runtime_metadata >> strip_tac >> gvs[] >>
  drule supported_append_element_layout >>
  disch_then (qspec_then `get_tenv cx` strip_assume_tac) >>
  `expr_type e = elem` by metis_tac[type_widens_to_word] >>
  `!observations. expr_body_pre cenv cx env e
     (es with storage_trace := observations)` by
    metis_tac[body_append_expr_pre, expr_body_pre_storage_trace] >>
  `body_expr_ok cx e` by metis_tac[] >>
  `!observations. expr_sim ctx func cenv cx elem e
     (es with storage_trace := observations)` by metis_tac[body_expr_ok_def] >>
  `get_module_code cx src = SOME tops` by
    (drule supported_append_storage_decl >> strip_tac >>
     drule supported_variable_decl_mem >> strip_tac >> gvs[body_inv_def]) >>
  irule stmt_frag_storage_rel_discharge >>
  conj_tac >- simp[evaluate_storage_trace_frame] >> strip_tac >>
  drule_all append_storage_compiler_location >> strip_tac >>
  `type_memory_bytes cenv elem = 32` by
    (gvs[supported_full_word_type_def] >> simp[type_memory_bytes_def]) >>
  imp_res_tac (cj 1 vyperTypingTheory.evaluate_type_well_formed) >>
  gvs[evaluate_type_def] >>
  irule compile_append_storage_word_stmt_frag >>
  simp[] >>
  qexistsl_tac [`src`, `id`] >>
  simp[declared_storage_region_def, evaluate_type_def] >>
  qexists_tac `slot` >> simp[] >>
  rpt strip_tac >>
  qmatch_asmsub_abbrev_tac
    `bind (eval_expr cx e) (read_result cx) start = (INL v,es1)` >>
  `expr_body_pre cenv cx env e start` by simp[Abbr `start`]
  >~ [`encode_value _ _ = _`] >- metis_tac[body_append_word_encoding] >>
  qspecl_then [`cenv`, `cx`, `env`, `e`, `start`, `INL v`, `es1`]
    mp_tac (REWRITE_RULE [ETA_AX] expr_body_pre_eval) >> simp[] >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    fs[expr_body_pre_def, expr_sim_inv_def, env_consistent_def,
       env_context_consistent_def] >>
  gvs[expr_result_typed_def, expr_runtime_typed_def, value_result_typed_def]
QED

Theorem append_aggregate_lowered_type:
  !cenv e env. ~is_bytestring_type (expr_type e) /\ int_calls_expr e = [] /\
    well_typed_expr env e ==> lowered_value_type cenv e = expr_type e
Proof
  ho_match_mp_tac lowered_value_type_ind >>
  rw[lowered_value_type_def, expr_type_def, int_calls_expr_def,
     is_bytestring_type_def] >>
  gvs[well_typed_expr_def, well_typed_builtin_app_def,
      type_builtin_result_ok_def, well_typed_type_builtin_args_def, AllCaseEqs(),
      is_bytestring_type_def, concat_buffer_type_def]
QED

Theorem body_append_storage_aggregate_fragment:
  body_stmt_safe tops (Append (TopLevelNameTarget (src,id)) e) /\
  (!s p t. eval_target_place cx (TopLevelNameTarget (src,id)) s = (INL p,t) ==>
             body_expr_ok cx e) /\
  body_inv tops ctx cenv cx /\
  supported_variable_decl tops (src,id) = SOME (vis,mut,ArrayT elem (Dynamic cap),SOME ast_slot) /\
  (mut = Storage \/ mut = Transient) /\ ~supported_full_word_type elem /\
  type_memory_bytes cenv elem < 2 ** 64 /\
  supported_stmt tops bindings (Append (TopLevelNameTarget (src,id)) e) /\
  supported_pure_expr tops e /\ expr_sim_inv cenv cx env es /\
  type_stmt env ret_ty (Append (TopLevelNameTarget (src,id)) e) = SOME env' /\
  stmt_exprs_ok cenv (Append (TopLevelNameTarget (src,id)) e) /\
  call_evaluation_safe cx (int_calls_stmt (Append (TopLevelNameTarget (src,id)) e)) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
              (Append (TopLevelNameTarget (src,id)) e) ==>
            occurs_abi_decode_target target tops) ==>
  stmt_frag ctx func cx lctx RetQ cenv
    (stmt_env cenv lctx ret_ty (Append (TopLevelNameTarget (src,id)) e))
    (eval_stmt cx (Append (TopLevelNameTarget (src,id)) e)) es
Proof
  strip_tac >> drule body_append_aggregate_metadata >>
  disch_then (drule_at (Pat `supported_variable_decl _ _ = _`)) >>
  simp[] >> disch_then drule_all >> strip_tac >> gvs[] >> (
  `supported_expr tops e` by simp[supported_expr_def] >>
  `well_typed_expr env e` by
    (drule append_typing_target >> metis_tac[]) >>
  `expr_body_pre cenv cx env e es` by metis_tac[body_append_expr_pre] >>
  `body_expr_ok cx e` by metis_tac[] >>
  `expr_sim ctx func cenv cx (expr_type e) e es` by metis_tac[body_expr_ok_def] >>
  `int_calls_expr e = []` by metis_tac[supported_pure_int_calls] >>
  `post_value_type cenv e = expr_type e` by
    (irule post_value_type_not_int_call >> rpt strip_tac >> gvs[int_calls_expr_def]) >>
  `lowered_value_type cenv e = expr_type e` by
    metis_tac[append_aggregate_lowered_type] >>
  irule stmt_frag_storage_rel_discharge >> strip_tac >>
  `32 * type_slot_size tv < dimword (:256)` by
    (fs[wordsTheory.dimword_def] >> decide_tac) >>
  irule compile_append_storage_aggregate_stmt_frag >> simp[] >>
  qexistsl_tac [`NONE`, `id`] >> simp[] >>
  reverse conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `expr_body_pre cenv cx env e (es with gas_obs := gs)` by simp[] >>
      qpat_x_assum `expr_body_pre _ _ _ _ es` kall_tac >>
      drule (REWRITE_RULE [bind_def] expr_body_pre_eval) >>
      disch_then (qspecl_then [`INL v`, `ee`] mp_tac) >>
      gvs[bind_def] >> strip_tac >>
      `env.type_defs = get_tenv cx` by
        fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
      `value_has_type tv v` by
        gvs[expr_result_typed_def, expr_runtime_typed_def,
            value_result_typed_def, value_runtime_typed_def] >>
      `val_wf tv v` by metis_tac[cj 1 value_has_type_val_wf] >>
      `type_memory_size tv = 32 * type_slot_size tv` by
        metis_tac[expr_sim_inv_memory_size] >>
      metis_tac[val_footprint_le]) >>
  rpt gen_tac >> strip_tac >>
  `?writes. encode_value tv v = SOME writes` by
    metis_tac[cj 1 value_has_type_equiv, optionTheory.IS_SOME_EXISTS] >>
  drule_at (Pat `append_place _ _ _ _ = _`) append_storage_copy_success_post >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then irule >> simp[] >>
  `storage_layout_safe cx` by fs[expr_sim_inv_def] >>
  `well_formed_type_value tv` by metis_tac[evaluate_type_well_formed_type_value] >>
  rpt conj_tac
  >- (rpt strip_tac >>
      irule (SRULE [] (Q.INST [`slot1` |-> `(n2w off):bytes32`]
        storage_layout_safe_region_separation)) >>
      goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >>
      simp[] >> rpt strip_tac >> gvs[]) >>
  simp[]
  >- (drule_all storage_layout_safe_region_nonoverflow >> simp[])
  >- metis_tac[]
  >- (qexists_tac `sb` >> simp[]) >>
  qexists_tac `b` >> simp[])
QED

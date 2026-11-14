Theory bodyFullTypeBuiltinEmpty
Ancestors
  bodyFullPreds bodyFullOfVV bodyFullExprGeneric bodyFullAllocGeneric
  gasOutcomeFullCompose exprSimHyps exprSimSource exprSimAggregatesAllocCounted
  bodyFullEmptyCertificate bodyFullEmptyPost aggregateEvaluatedLayout
  bodyFullTypeBuiltinWords
  exprLoweringProps gasShadow vyperTypeSystem exprSimHypsDefs vyperTypeCallGraph
  vyperContext vyperInterpreter vyperState vyperAST

Theorem empty_expr_full_ok:
  !cx v11 typ es.
    (!s'' x t.
       type_check (type_builtin_args_length_ok Empty (LENGTH es))
         "TypeBuiltin args" s'' = (INL x,t) ==>
       body_exprs_full_ok cx es) ==>
    body_expr_full_ok cx (TypeBuiltin v11 Empty typ es)
Proof
  rpt gen_tac >> strip_tac >>
  rw[body_expr_full_ok_def] >>
  `es = [] /\ v11 = typ` by
    gvs[expr_body_pre_def, well_typed_expr_def,
        well_typed_type_builtin_args_def, type_builtin_result_ok_def] >>
  gvs[] >>
  `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (TypeBuiltin typ Empty typ []) es'` by suspend "vv" >>
  simp[] >> suspend "value"
QED

Resume empty_expr_full_ok[vv]:
  Cases_on `is_word_type typ` >- suspend "word" >>
  rewrite_tac[bodySimFullTheory.expr_vv_sim_full_def] >>
  rpt gen_tac >> strip_tac >>
  irule gas_outcome_full_initial_domain >>
  simp[vyperStorageTraceTheory.evaluate_storage_trace_frame] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon es'.storage_trace) es'.storage_trace` by
    gvs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `stmt_state_rel (storage_trace_horizon es'.storage_trace) ctx func cenv cx es' s0` by
    metis_tac[] >>
  `expr_sim_pre cenv cx env (TypeBuiltin typ Empty typ []) es'` by
    (gvs[expr_sim_pre_body, int_calls_expr_def]) >>
  drule well_typed_expr_type_evaluates >>
  simp[expr_type_def, optionTheory.IS_SOME_EXISTS] >> strip_tac >>
  rename1 `evaluate_type (get_tenv cx) typ = SOME rt` >>
  qpat_x_assum `compile_expr cenv ty (TypeBuiltin typ Empty typ []) sa = _` mp_tac >>
  simp[compile_expr_type_builtin_dispatch,
       Once exprLoweringTheory.compile_expr_def,
       compileEnvTheory.comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  `expr_sim_inv cenv cx env es'` by gvs[expr_body_pre_def] >>
  `type_memory_bytes cenv typ < dimword (:256)` by
    (drule body_post_type_allocation_bound >>
     simp[expr_type_def] >> strip_tac >>
     simp[wordsTheory.dimword_def] >> decide_tac) >>
  drule_all exprSimAggregateLayoutTheory.empty_type_buffer_size >> strip_tac >>
  `stmt_state_rel (storage_trace_horizon es'.storage_trace) ctx func cenv cx es' s0` by
    metis_tac[] >>
  drule_all exprSimBufferEmptyExecTheory.compile_builtin_empty_complex_run >> strip_tac >>
  `lo <= s0.vs_alloca_next` by
    ( `ghost_inv_at (DF (storage_trace_horizon es'.storage_trace)) lo d cenv cx es' G0 tn0 s0` by metis_tac[] >>
      fs[bodyPtrDefsTheory.ghost_inv_at_def]) >>
  `!H. valid_horizon cx st0 H es'.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es' s0 /\
    ghost_inv_at (DF H) lo d cenv cx es' G0 tn0 s0` by metis_tac[] >>
  drule_all empty_buffer_origin_full >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  irule gas_outcome_full_pure >>
  reverse conj_tac >- simp[] >>
  qexistsl_tac [`Gf`, `es'`, `INL (Value (default_value rt))`,
    `t with vs_inst_idx := LENGTH sb.cs_current_insts`, `tnf`] >>
  simp[NoAsms] >> conj_tac
  >- (simp[Once evaluate_def, evaluate_type_builtin_def,
        bind_def, return_def, lift_option_def, lift_sum_def] >>
      simp[evaluate_def, ignore_bind_def, type_check_def,
        type_builtin_args_length_ok_def, bind_def, return_def,
        assert_def]) >>
  qx_gen_tac `H` >> strip_tac >>
  `stmt_state_rel H ctx func cenv cx es' s0 /\
   storage_well_formed_on cx es' (FST H)` by metis_tac[] >>
  drule_all empty_memory_full_post >> strip_tac >>
  simp[exprLoweringTheory.lowered_value_type_def,
    contextTheory.base_ptr_def, contextTheory.vv_location_def] >>
  fs[loweringPostsTheory.vv_post_def, bodyPtrDefsTheory.ptr_vv_ok_def,
     bodyPtrDefsTheory.ptr_val_ok_def, read_result_def, return_def,
     contextTheory.base_ptr_def] >>
  conj_tac
  >- (qpat_x_assum `!D base explicit. _` irule >>
      simp[] >>
      `ghost_inv_at (DF H) lo d cenv cx es' G0 tn0 s0` by metis_tac[] >>
      gvs[bodyPtrDefsTheory.ghost_inv_at_def]) >>
  conj_tac
  >- (conj_tac
      >- (qpat_x_assum `storage_well_formed_on cx es' (FST H)` mp_tac >>
          simp[NoAsms, vyperStorageFootprintTheory.storage_well_formed_on_def,
            vyperStorageBackendTheory.get_storage_def] >>
          strip_tac >> rpt gen_tac >>
          first_x_assum (qspecl_then [`b`, `slot`, `tv`] mp_tac) >>
          Cases_on `b` >> simp[vyperStorageBackendTheory.get_storage_def]) >>
      conj_tac
      >- (qpat_x_assum `vv_holds _ _ _ _ _ _ _` mp_tac >>
          simp[loweringPostsTheory.vv_holds_def, read_result_def, return_def]) >>
      conj_tac
      >- (qpat_x_assum `vv_at _ _ _ _ _ _ _ _ _` mp_tac >>
          simp[loweringPostsTheory.vv_at_def, read_result_def, return_def]) >>
      conj_tac >- (qpat_x_assum `!aid off sz. _` MATCH_ACCEPT_TAC) >>
      qpat_x_assum `locals_kept _ _ _ _ _` mp_tac >>
      simp[NoAsms, loweringPostsTheory.locals_kept_def,
        loweringPostsTheory.popped_kept_def]) >>
  conj_tac
  >- (qpat_x_assum `vv_store_bound _ _ _ _ _ _ _` mp_tac >>
      simp[exprSimMemDefsTheory.vv_store_bound_def, expr_type_def,
        read_result_def, return_def]) >>
  conj_tac
  >- (`ghost_inv_at (DF H) lo d cenv cx es' Gf tnf
         (t with vs_inst_idx := LENGTH sb.cs_current_insts)` by metis_tac[] >>
      pop_assum mp_tac >>
      simp[NoAsms, bodyPtrDefsTheory.ghost_inv_at_def] >>
      strip_tac >> simp[]) >>
  conj_tac >- metis_tac[] >> metis_tac[]
QED
Resume empty_expr_full_ok[value]:
  irule expr_sim_full_of_vv >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> drule_all exprSimHypsTheory.expr_body_pre_copy_ok >> simp[]) >>
  drule expr_body_pre_type_evaluates >>
  simp[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
  qexists_tac `x` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  `expr_body_pre cenv cx env (TypeBuiltin typ Empty typ [])
     (es' with gas_obs := gs)` by simp[] >>
  drule_all exprSimSourceTheory.expr_body_pre_runtime_typed >>
  strip_tac >> gvs[] >> metis_tac[]
QED
Resume empty_expr_full_ok[word]:
  drule expr_body_pre_type_evaluates >>
  simp[expr_type_def, optionTheory.IS_SOME_EXISTS] >> strip_tac >>
  rename1 `evaluate_type (get_tenv cx) typ = SOME rt` >>
  irule type_builtin_literal_vv_full >>
  reverse conj_tac >- (simp[] >> metis_tac[]) >>
  qexistsl_tac [`default_value rt`, `0w`] >>
  conj_tac
  >- simp[compile_expr_type_builtin_dispatch,
          Once exprLoweringTheory.compile_expr_def, compileEnvTheory.comp_bind_def] >>
  conj_tac
  >- (simp[Once evaluate_def, evaluate_type_builtin_def,
        bind_def, return_def, lift_option_def, lift_sum_def] >>
      simp[evaluate_def, ignore_bind_def, type_check_def,
        type_builtin_args_length_ok_def, bind_def, return_def, assert_def]) >>
  rpt strip_tac >> gvs[] >>
  irule exprSimAggregatesTheory.typed_val_to_w256_default_word >>
  metis_tac[]
QED
Finalise empty_expr_full_ok

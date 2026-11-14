(* Tuple literal production: ownership is retained inside the gas success post. *)
Theory tupleAssignImmutableDeployMakeTupleOwned
Ancestors
  tupleAssignImmutableDeployConstructors exprSimAggregatesAllocCounted
  exprSimAggregates exprSimAggregateChildren exprSimAggregateLoops
  stmtSimDeclCompose vyperEvalExprPreservesScopesDom bodyMemAggregateAssembly
  exprSimSource exprSimProps exprSimHypsDefs exprSimDefs loweringPosts
  exprSimAlloc allocLimits exprSimHyps exprLowering compileEnv loweringStateRelDefs
  exprSimValues gasNormalPrefix gasSummary gasOutcome gasContext
  fragGasMode fragGasPath fragGasSeq valueEncoding valueEncodingDefs
  vyperAST vyperInterpreter vyperState vyperContext vyperValueOperation
  vyperTypeSystem fragExec venomState exprSimBuffer exprSimBufferEmptyExec
  exprSimAggregateLayout exprSimAggregateSource exprLoweringProps

Theorem tuple_immutable_make_tuple_owned:
  exprs_case nocalls ctx func cenv cx args /\
  (~nocalls ==> !e. MEM e args ==>
    int_calls_expr e = [] \/ lowered_value_type cenv e = expr_type e) /\
  expr_body_pre cenv cx env (Builtin ann (MakeArray NONE bnd) args) es /\
  (nocalls ==> int_calls_expr (Builtin ann (MakeArray NONE bnd) args) = []) /\
  compile_expr cenv ty (Builtin ann (MakeArray NONE bnd) args) sa = (vv,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  gas_admissible (eval_expr cx (Builtin ann (MakeArray NONE bnd) args))
    expr_vv_res_ok es /\
  stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?ba sm tvs.
    compile_alloc_buffer (SUM (MAP (type_memory_bytes cenv o expr_type) args))
      sa = (ba,sm) /\
    evaluate_type (get_tenv cx) ann = SOME (TupleTV tvs) /\
    vv = LocatedValue ann (mk_ptr ba.buf_operand LocMemory) /\
    gas_outcome F (cx_tops cx) (ctx,func)
      (eval_expr cx (Builtin ann (MakeArray NONE bnd) args)) (es,s0)
      (\res ee r. ?tv w. res = INL tv /\
        vv_post ctx func cenv cx (Builtin ann (MakeArray NONE bnd) args)
          es sa sb s0 ee tv vv r /\
        r.vs_current_bb = sb.cs_current_bb /\
        r.vs_inst_idx = LENGTH sb.cs_current_insts /\
        eval_operand ba.buf_operand r = SOME w /\
        (type_memory_size_list tvs = 0 \/
         ?aid b n. FLOOKUP r.vs_allocas aid = SOME (b,n) /\
           sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
           b <= w2n w /\ w2n w + type_memory_size_list tvs <= b+n /\
           (!name lb lsz. local_region cenv ee.scopes r name lb lsz ==>
             b+n <= lb \/ lb+lsz <= b)))
      (\res ee exit. expr_exit res exit)
Proof
  strip_tac >>
  drule compile_tuple_literal_inv >> strip_tac >> gvs[] >>
  drule make_tuple_evaluated_layout >> strip_tac >> gvs[] >>
  `expr_sim_inv cenv cx env es` by gvs[expr_body_pre_def] >>
  `!e st. MEM e args /\ expr_sim_inv cenv cx env st ==>
    expr_body_pre cenv cx env e st /\ (nocalls ==> int_calls_expr e = [])` by
    (`!n t b. MakeArray t b <> Slice n` by simp[] >>
     metis_tac[expr_body_pre_builtin_arg, int_calls_builtin_arg]) >>
  `!e. MEM e args /\ nocalls ==> int_calls_expr e = []` by metis_tac[] >>
  `compatible_bound bnd (LENGTH args)` by
    gvs[expr_body_pre_def, vyperTypeSystemTheory.well_typed_expr_def,
      vyperTypeSystemTheory.well_typed_builtin_app_def] >>
  `ci_mono sa sm` by metis_tac[ci_mono_compile_alloc_buffer, pairTheory.SND] >>
  `ci_mono sm sb` by
    metis_tac[ci_mono_compile_make_tuple_cfn, compile_expr_ci_mono, pairTheory.SND] >>
  `cs_extends sa sm /\ cs_extends sm sb` by gvs[ci_mono_def] >>
  drule_all fn_has_code_split >> strip_tac >>
  `SUM (MAP (type_memory_bytes cenv o expr_type) args) < dimword (:256)` by
    (gvs[expr_body_pre_def, alloc_limits_expr_def] >>
     simp[wordsTheory.dimword_def] >> decide_tac) >>
  `type_memory_size_list tvs < dimword (:256)` by metis_tac[] >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule_all buffer_alloc_counted >> strip_tac >> gvs[] >>
  drule_at (Pat `compile_make_tuple _ _ _ _ _ _ = _`) aggregate_make_tuple_sim >>
  disch_then drule >> disch_then drule >>
  disch_then (drule_at (Pat `lookup_var _ _ = _`)) >>
  disch_then (drule_at (Pat `MEM _ (fn_insts _)`)) >> simp[] >>
  disch_then (qspecl_then [`ctx`,`nocalls`] mp_tac) >> simp[] >>
  (impl_tac >- (rpt strip_tac >> simp[] >>
    irule aggregate_alloca_immutable_sep >>
    goal_assum (drule_at (Pat `stmt_state_rel ctx _ _ _ _ _`)) >>
    qpat_x_assum `MEM inst (fn_insts func)` kall_tac >>
    goal_assum (drule_at (Pat `MEM _ (fn_insts _)`)) >>
    simp[venomInstTheory.mk_inst_def] >>
    goal_assum (drule_at Any) >> simp[])) >> strip_tac >> gvs[] >>
  irule gas_outcome_zero_prefix >> goal_assum (drule_at Any) >>
  simp[aggregate_tuple_action_mem] >>
  drule aggregate_outcome_source_run_mem >> strip_tac >>
  irule aggregate_outcome_map_mem >> goal_assum (drule_at Any) >>
  conj_tac >- (rpt strip_tac >> gvs[sumTheory.SUM_MAP]) >>
  rpt strip_tac >> gvs[sumTheory.SUM_MAP] >>
  rename1 `eval_exprs cx args (es with gas_obs := gs) = (INL vs,ee)` >>
  `eval_expr cx (Builtin (TupleT (MAP expr_type args)) (MakeArray NONE bnd) args)
    (es with gas_obs := gs) = (INL (Value (ArrayV (TupleV vs))),ee)` by
    (drule_all aggregate_eval_make_tuple >> simp[]) >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` kall_tac >>
  rename1 `stmt_state_rel ctx func cenv cx ee s` >>
  `expr_body_pre cenv cx env
    (Builtin (TupleT (MAP expr_type args)) (MakeArray NONE bnd) args)
    (es with gas_obs := gs)` by simp[] >>
  `val_wf (TupleTV tvs) (ArrayV (TupleV vs))` by
    (irule aggregate_materialised_child_wf >>
     goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >>
     simp[expr_type_def, read_result_def, return_def] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `val_footprint (TupleTV tvs) (ArrayV (TupleV vs)) <= type_memory_size_list tvs` by
    (drule val_footprint_le >> simp[type_memory_size_def]) >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (drule vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom >> simp[]) >>
  `!nm lb len. local_region cenv ee.scopes s nm lb len ==>
     b + type_memory_size_list tvs <= lb \/ lb + len <= b` by
    (rpt strip_tac >> drule_all aggregate_buffer_clearance >> simp[]) >>
  `~expr_has_effect (Builtin (TupleT (MAP expr_type args)) (MakeArray NONE bnd) args) ==>
     pure_frame cenv func es sa s0 s` by
    (rewrite_tac[expr_has_effect_thm] >> strip_tac >>
     qpat_x_assum `EVERY _ _ ==> _` mp_tac >>
     (impl_tac >- (qpat_x_assum `~EXISTS _ _` mp_tac >>
        simp_tac (srw_ss()) [listTheory.EVERY_MAP, listTheory.EXISTS_MAP,
                             combinTheory.o_DEF])) >> strip_tac >>
     irule aggregate_pure_frame_buffer >>
     reverse conj_tac
     >- (goal_assum (drule_at Any)) >>
     qexistsl [`type_memory_size_list tvs`, `b`, `sm`, `t`] >>
     simp[arithmeticTheory.ADD_COMM] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     first_assum ACCEPT_TAC) >>
  qexists `n2w b` >> simp[eval_operand_def] >>
  reverse conj_tac
  >- (disj2_tac >>
      qexistsl [`sa.cs_next_id`, `b`, `type_memory_size_list tvs`] >>
      gvs[ci_mono_def] >> first_assum ACCEPT_TAC) >>
  irule (buffer_loop_memory_vv_post |> Q.INST
    [`e` |-> `Builtin (TupleT (MAP expr_type args)) (MakeArray NONE bnd) args`]
    |> SIMP_RULE (srw_ss()) [expr_type_def]) >>
  simp[expr_type_def, is_word_type_def, contextTheory.mk_ptr_def, contextTheory.base_ptr_def,
    eval_operand_def, val_in_memory_def] >>
  qexistsl [`b`,`sm`,`type_memory_size_list tvs`,`t`] >>
  simp[wordsTheory.dimword_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `!aid p n. FLOOKUP t.vs_allocas aid = SOME (p,n) /\ _ ==> _` mp_tac >>
  qpat_x_assum `_ ==> pure_frame _ _ _ _ _ _` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[arithmeticTheory.ADD_COMM]
QED

(* Shared MakeArray memory simulation, including physically widened children. *)
Theory bodyMemMakeArrayAssembly
Ancestors
  bodyMemAggregateFrames bodyMemArrayLayout bodyMemTupleLayout bodyMemAggregateResult bodyMemAggregateAlloc bodyMemAggregateAssembly
  bodyMemAggregateTraversal bodyMemArrayAdapters bodyExprForceMemory
  exprSimAggregates exprSimAggregateLayout exprSimHyps exprSimMemDefs
  exprSimHypsDefs exprLoweringProps exprSimProps fragExec compileEnv allocLimits
  exprSimAggregateSource exprSimBuffer bodyMemAggregateBounds valueEncoding
  loweringPosts exprSimSource exprSimAggregateChildren vyperAST vyperInterpreter vyperState

Theorem make_array_body_inputs[local]:
  expr_body_pre ce cx env (Builtin ty (MakeArray t n) es) st /\
  (builtin_args_length_ok (MakeArray t n) (LENGTH es) ==> body_exprs_mem_ok cx es) ==>
  expr_sim_inv ce cx env st /\ compatible_bound n (LENGTH es) /\
  body_exprs_mem_ok cx es /\
  (!e s. MEM e es /\ expr_sim_inv ce cx env s ==> expr_body_pre ce cx env e s)
Proof
  strip_tac >>
  `compatible_bound n (LENGTH es)` by
    (Cases_on `t` >>
     gvs[expr_body_pre_def, vyperTypeSystemTheory.well_typed_expr_def,
         vyperTypeSystemTheory.well_typed_builtin_app_def]) >>
  `body_exprs_mem_ok cx es` by
    (first_x_assum irule >> gvs[vyperContextTheory.builtin_args_length_ok_def]) >>
  simp[] >> conj_tac >- gvs[expr_body_pre_def] >>
  `!n t b. MakeArray t b <> Slice n` by simp[] >>
  metis_tac[expr_body_pre_builtin_arg]
QED

Theorem make_tuple_body_vv_mem[local]:
  (builtin_args_length_ok (MakeArray NONE n) (LENGTH es) ==> body_exprs_mem_ok cx es) /\
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (Builtin ty (MakeArray NONE n) es) st ==>
  expr_vv_sim_mem ctx func cenv cx ty' (Builtin ty (MakeArray NONE n) es) st
Proof
  strip_tac >> drule_all make_array_body_inputs >> strip_tac >>
  rw[expr_vv_sim_mem_def] >>
  drule_all tuple_body_allocation_layout >> strip_tac >> gvs[] >>
  drule_all aggregate_buffer_alloc_counted_mem_any_block >> strip_tac >> gvs[] >>
  drule_at (Pat `compile_make_tuple _ _ _ _ _ _ = _`) aggregate_make_tuple_body_sim_mem >>
  disch_then drule >> disch_then drule >>
  disch_then (drule_at (Pat `lookup_var _ _ = _`)) >>
  disch_then (drule_at (Pat `MEM _ (fn_insts _)`)) >> simp[] >>
  disch_then (qspecl_then [`ctx`,`tops`] mp_tac) >> simp[] >>
  (impl_tac >- (rpt strip_tac >> simp[] >>
    irule aggregate_alloca_immutable_sep >>
    goal_assum (drule_at (Pat `stmt_state_rel ctx _ _ _ _ _`)) >>
    qpat_x_assum `MEM inst (fn_insts func)` kall_tac >>
    goal_assum (drule_at (Pat `MEM _ (fn_insts _)`)) >>
    simp[venomInstTheory.mk_inst_def] >>
    goal_assum (drule_at Any) >> simp[])) >> strip_tac >> gvs[] >>
  irule bodyDeclMemoryComposeTheory.gas_outcome_zero_prefix_mem >>
  qexists_tac `t` >>
  conj_tac >- gvs[fragGasModeTheory.gas_marked_path_def] >>
  simp[aggregate_tuple_action_mem] >>
  drule aggregate_outcome_source_run_mem >> strip_tac >>
  irule aggregate_outcome_map_mem >> goal_assum (drule_at Any) >>
  conj_tac >- (rpt strip_tac >> gvs[sumTheory.SUM_MAP]) >>
  rpt strip_tac >> gvs[sumTheory.SUM_MAP] >>
  rpt (qpat_x_assum `gas_outcome _ _ _ _ _ _ _` kall_tac) >>
  drule_at (Pat `expr_body_pre _ _ _ _ _`) aggregate_completed_buffer_result >>
  simp[expr_type_def, exprLoweringTheory.lowered_value_type_def] >>
  disch_then match_mp_tac >>
  simp[expr_type_def, exprLoweringTheory.lowered_value_type_def, is_word_type_def,
       contextTheory.mk_ptr_def, venomStateTheory.eval_operand_def,
       val_in_memory_def, type_memory_size_def] >>
  qexistsl_tac [`t`, `type_memory_size_list tvs`, `sm`, `gs`, `b`] >>
  simp[aggregate_tuple_action_mem, bind_def, return_def] >>
  conj_tac >- (rpt strip_tac >>
    qpat_x_assum `!aid p n. aid < sa.cs_next_id /\ _ ==> _` irule >>
    goal_assum (drule_at Any) >> simp[]) >>
  conj_tac >- (rpt strip_tac >>
    qpat_x_assum `!name p n. local_region _ _ s0 _ _ _ ==> _` irule >>
    goal_assum (drule_at Any)) >>
  rpt strip_tac >> irule aggregate_exterior_frame_transport >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem make_array_body_vv_mem[local]:
  (builtin_args_length_ok (MakeArray (SOME et) n) (LENGTH es) ==> body_exprs_mem_ok cx es) /\
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (Builtin ty (MakeArray (SOME et) n) es) st ==>
  expr_vv_sim_mem ctx func cenv cx ty' (Builtin ty (MakeArray (SOME et) n) es) st
Proof
  strip_tac >> drule_all make_array_body_inputs >> strip_tac >>
  rw[expr_vv_sim_mem_def] >>
  drule_all array_body_allocation_layout >> strip_tac >> gvs[] >>
  drule_all aggregate_buffer_alloc_counted_mem_any_block >> strip_tac >> gvs[] >>
  drule_at (Pat `compile_make_array _ _ _ _ _ _ _ _ = _`) aggregate_make_array_body_sim_mem >>
  disch_then drule >> disch_then drule >>
  disch_then (drule_at (Pat `lookup_var _ _ = _`)) >>
  disch_then (drule_at (Pat `MEM _ (fn_insts _)`)) >> simp[] >>
  disch_then (qspecl_then [`env`,`st`,`ctx`,`tops`] mp_tac) >> simp[] >>
  (impl_tac >- (rpt strip_tac >> simp[regions_disjoint_def] >>
    irule aggregate_alloca_immutable_prefix_sep >>
    goal_assum (drule_at (Pat `stmt_state_rel ctx _ _ _ _ _`)) >>
    qpat_x_assum `MEM inst (fn_insts func)` kall_tac >>
    goal_assum (drule_at (Pat `MEM _ (fn_insts _)`)) >>
    simp[venomInstTheory.mk_inst_def] >>
    goal_assum (drule_at Any) >> simp[])) >> strip_tac >> gvs[] >>
  irule bodyDeclMemoryComposeTheory.gas_outcome_zero_prefix_mem >>
  qexists_tac `t` >>
  conj_tac >- gvs[fragGasModeTheory.gas_marked_path_def] >>
  `eval_expr cx (Builtin (ArrayT et n) (MakeArray (SOME et) n) es) =
    bind (eval_exprs cx es) (return o (\vs. Value (ArrayV (make_array_value tv n vs))))` by
    (irule aggregate_array_action_mem >> simp[]) >>
  qpat_assum `eval_expr _ _ = bind _ _` (fn th => once_rewrite_tac[th]) >>
  drule aggregate_outcome_source_run_mem >> strip_tac >>
  irule aggregate_outcome_map_mem >> goal_assum (drule_at Any) >>
  conj_tac >- (rpt strip_tac >> gvs[sumTheory.SUM_MAP]) >>
  rpt strip_tac >> gvs[sumTheory.SUM_MAP] >>
  `LENGTH vs = LENGTH es` by (drule eval_exprs_length >> simp[]) >>
  `val_in_memory (ArrayTV tv n) (ArrayV (make_array_value tv n vs)) b t'.vs_memory` by
    (irule array_from_dense_memory >> simp[] >> Cases_on `n` >> gvs[]) >>
  rpt (qpat_x_assum `gas_outcome _ _ _ _ _ _ _` kall_tac) >>
  drule_at (Pat `expr_body_pre _ _ _ _ _`) aggregate_completed_buffer_result >>
  simp[expr_type_def, exprLoweringTheory.lowered_value_type_def] >>
  disch_then match_mp_tac >>
  simp[expr_type_def, exprLoweringTheory.lowered_value_type_def, is_word_type_def,
       contextTheory.mk_ptr_def, venomStateTheory.eval_operand_def] >>
  qexistsl_tac [`t`, `type_memory_bytes cenv (ArrayT et n)`, `sm`, `gs`, `b`] >>
  simp[bind_def, return_def] >>
  `type_memory_bytes cenv (ArrayT et n) = type_memory_size (ArrayTV tv n)` by
    (irule expr_sim_inv_memory_size >> goal_assum (drule_at Any) >> simp[]) >>
  gvs[] >>
  conj_tac >- (rpt strip_tac >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> metis_tac[]) >>
  rpt strip_tac >> irule aggregate_exterior_frame_transport >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

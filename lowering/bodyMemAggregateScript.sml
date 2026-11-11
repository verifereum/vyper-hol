(* Memory judgments of struct and array literals whose elements the lowering
   lays out at their own types: the main halves of bodyMemStructLit's and
   bodyMemMakeArray's cases, the memory twins of exprSimAggregates'
   compile_struct_lit_vv_case and compile_make_array_vv_case.  An element
   that is an internal call whose return type the call's type widens is the
   other half (bodyMemStructLitWidened, bodyMemMakeArrayWidened). *)
Theory bodyMemAggregate
Ancestors
  bodyMemoryPreds bodyMemAggregateAlloc bodyMemAggregateAssembly
  bodyMemAggregateAdapters bodyMemAggregateLoopBoundary bodyExprForceMemory
  exprSimAggregates exprSimAggregateLayout exprSimHyps exprSimMemDefs
  exprSimHypsDefs exprLoweringProps exprSimProps fragExec compileEnv loweringStateRelDefs allocLimits
  exprSimAggregateSource exprSimBuffer bodyMemAggregateBounds valueEncoding valueEncodingDefs
  loweringPosts exprSimSource exprSimAggregateChildren vyperAST vyperInterpreter vyperState

Theorem body_structlit_nowiden_mem:
  !cx v7 src_id_opt id kes tops ctx func cenv env ty es.
    (!ks. ks = MAP FST kes ==> body_exprs_mem_ok cx (MAP SND kes)) /\
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (StructLit v7 (src_id_opt,id) kes) es /\
    (!e. MEM e (MAP SND kes) ==>
         int_calls_expr e = [] \/ lowered_value_type cenv e = expr_type e) ==>
    expr_sim_mem ctx func cenv cx ty (StructLit v7 (src_id_opt,id) kes) es /\
    expr_vv_sim_mem ctx func cenv cx ty (StructLit v7 (src_id_opt,id) kes) es
Proof
  rpt gen_tac >> strip_tac >>
  conj_asm2_tac
  >- (irule body_expr_sim_mem_of_vv_sim_mem >>
      reverse conj_tac >- (simp[] >> qexists_tac `env` >> simp[]) >>
      rpt strip_tac >> drule compile_struct_literal_inv >> simp[]) >>
  rw[expr_vv_sim_mem_def] >>
  drule compile_struct_literal_inv >> strip_tac >> gvs[] >>
  drule struct_literal_lookup_types >> strip_tac >>
  drule struct_literal_evaluated_layout >> strip_tac >>
  `expr_sim_inv cenv cx env es` by gvs[expr_body_pre_def] >>
  `!e st. MEM e (MAP SND kes) /\ expr_sim_inv cenv cx env st ==>
    expr_body_pre cenv cx env e st` by
    metis_tac[expr_body_pre_struct_field] >>
  `ci_mono sa sm` by metis_tac[ci_mono_compile_alloc_buffer, pairTheory.SND] >>
  `ci_mono sm sb` by
    metis_tac[ci_mono_compile_struct_lit_cfn, compile_expr_ci_mono, pairTheory.SND] >>
  `cs_extends sa sm /\ cs_extends sm sb` by
    (qpat_x_assum `ci_mono sa sm` mp_tac >>
     qpat_x_assum `ci_mono sm sb` mp_tac >> simp[ci_mono_def]) >>
  drule_all fn_has_code_split >> strip_tac >>
  `SUM (MAP (SND o SND)
    (get_struct_fields cenv.ce_struct_fields (nsid_to_string (src_id_opt,id)))) <
    dimword (:256)` by
    (gvs[expr_body_pre_def, alloc_limits_expr_def, type_memory_bytes_def] >>
     simp[wordsTheory.dimword_def] >> decide_tac) >>
  drule_all exprSimAllocTheory.buffer_alloc_code >> strip_tac >>
  drule_all aggregate_buffer_alloc_counted_mem_any_block >> strip_tac >>
  qmatch_asmsub_abbrev_tac `compile_alloc_buffer sz sa` >>
  gvs[] >>
  drule_at (Pat `compile_struct_lit _ _ _ _ _ _ _ = _`) aggregate_struct_fields_sim_mem >>
  simp[] >> disch_then drule >>
  disch_then (drule_at (Pat `lookup_var _ _ = _`)) >>
  disch_then (drule_at (Pat `MEM _ (fn_insts _)`)) >>
  simp[] >>
  disch_then (qspecl_then [`env`, `es`, `ctx`, `tops`] mp_tac) >>
  (impl_tac >- (simp[] >> rpt strip_tac >>
    irule aggregate_alloca_immutable_sep >>
    goal_assum (drule_at (Pat `stmt_state_rel ctx _ _ _ _ _`)) >>
    qpat_x_assum `MEM inst (fn_insts func)` kall_tac >>
    goal_assum (drule_at (Pat `MEM _ (fn_insts _)`)) >>
    simp[venomInstTheory.mk_inst_def] >>
    goal_assum (drule_at Any) >> simp[])) >> strip_tac >> gvs[] >>
  irule bodyDeclMemoryComposeTheory.gas_outcome_zero_prefix_mem >>
  qexists_tac `t` >>
  conj_tac >- gvs[fragGasModeTheory.gas_marked_path_def] >>
  rewrite_tac[aggregate_struct_action_mem] >>
  drule aggregate_outcome_source_run_mem >> strip_tac >>
  irule aggregate_outcome_map_mem >>
  goal_assum (drule_at Any) >>
  conj_tac >- (rpt strip_tac >> gvs[sumTheory.SUM_MAP]) >>
  rpt strip_tac >> gvs[sumTheory.SUM_MAP] >>
  suspend "struct_final_post"
QED

Resume body_structlit_nowiden_mem[struct_final_post]:
  `eval_expr cx (StructLit v7 (src_id_opt,id) kes) (es with gas_obs := gs) =
    (INL (Value (StructV (ZIP (MAP FST kes,vs)))),ee)` by
    (drule aggregate_eval_struct >> simp[]) >>
  rpt (qpat_x_assum `gas_outcome _ _ _ _ _ _ _` kall_tac) >>
  `expr_body_pre cenv cx env (StructLit v7 (src_id_opt,id) kes) (es with gas_obs := gs)` by simp[] >>
  `v7 = StructT (src_id_opt,id)` by
    gvs[expr_body_pre_def, vyperTypeSystemTheory.well_typed_expr_def] >>
  gvs[] >>
  `val_wf (StructTV (ZIP (MAP FST kes,tvs)))
    (StructV (ZIP (MAP FST kes,vs)))` by
    (irule aggregate_materialised_child_wf >>
     goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >>
     simp[expr_type_def, read_result_def, return_def] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `val_footprint (StructTV (ZIP (MAP FST kes,tvs)))
     (StructV (ZIP (MAP FST kes,vs))) <= type_memory_size_list tvs` by
    (drule val_footprint_le >> simp[type_memory_size_def] >>
     `LENGTH (MAP FST kes) = LENGTH tvs` by
       (drule vyperTypeABITheory.OPT_MMAP_LENGTH >> simp[]) >>
     simp[struct_layout_size_zip]) >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (drule vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom >> simp[]) >>
  `!nm lb len. local_region cenv ee.scopes t' nm lb len ==>
     b + type_memory_size_list tvs <= lb \/ lb + len <= b` by
    (rpt strip_tac >> drule_all aggregate_buffer_clearance >> simp[]) >>
  `~expr_has_effect (StructLit (StructT (src_id_opt,id)) (src_id_opt,id) kes) ==>
     pure_frame cenv func es sa s0 t'` by
    (rewrite_tac[expr_has_effect_thm] >> strip_tac >>
     qpat_x_assum `EVERY _ _ ==> _` mp_tac >>
     (impl_tac >- (qpat_x_assum `~EXISTS _ _` mp_tac >>
        simp_tac (srw_ss()) [listTheory.EVERY_MAP, listTheory.NOT_EXISTS, combinTheory.o_DEF])) >>
     strip_tac >>
     qpat_assum `FLOOKUP t.vs_allocas _ = SOME (b,_)` (fn th =>
       qpat_assum `!aid a. FLOOKUP t.vs_allocas aid = SOME a ==> _` (fn th2 =>
         assume_tac (MATCH_MP th2 th))) >>
     irule (Q.SPECL [`cenv`, `func`, `es`, `sa`, `sm`, `s0`, `s0`, `t'`]
       aggregate_pure_frame_buffer) >>
     qpat_assum `MEM (mk_inst sa.cs_next_id ALLOCA _ _) _` (irule_at Any) >>
     qpat_assum `FLOOKUP t'.vs_allocas _ = SOME (b,_)` (irule_at Any) >>
     qexists_tac `sm` >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY (simp[] >> NO_TAC) >>
     rpt gen_tac >> disch_tac >>
     qpat_x_assum `!p n. _ /\ (!i c sz. _) ==> _` irule >>
     pop_assum mp_tac >> rpt (pop_assum kall_tac) >>
     strip_tac >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> decide_tac) >>
  conj_asm1_tac
  >- (irule buffer_loop_memory_vv_post >>
      simp[expr_type_def, is_word_type_def, contextTheory.mk_ptr_def, contextTheory.base_ptr_def,
        venomStateTheory.eval_operand_def, val_in_memory_def] >>
      qexistsl [`b`,`sm`,`type_memory_size_list tvs`,`t`] >>
      simp[wordsTheory.dimword_def] >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qpat_x_assum `!aid p n. FLOOKUP t.vs_allocas aid = SOME (p,n) /\ _ ==> _` mp_tac >>
      qpat_x_assum `_ ==> pure_frame _ _ _ _ _ _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >>
      metis_tac[arithmeticTheory.ADD_COMM]) >>
  irule aggregate_allocated_result_store_bound_mem >>
  simp[expr_type_def, exprLoweringTheory.lowered_value_type_def,
       contextTheory.base_ptr_def] >>
  conj_tac >- fs[stmt_state_rel_def] >>
  reverse conj_tac >-
    (qexistsl [`ctx`, `es`, `func`, `s0`, `sa`, `sb`] >>
     gvs[expr_type_def, contextTheory.base_ptr_def]) >>
  qexistsl [`sa.cs_next_id`, `b`, `type_memory_size_list tvs`] >>
  simp[] >>
  `LENGTH (MAP FST kes) = LENGTH tvs` by
    (drule vyperTypeABITheory.OPT_MMAP_LENGTH >> simp[]) >>
  simp[type_memory_size_def, struct_layout_size_zip,
       venomStateTheory.eval_operand_def] >>
  metis_tac[]
QED
Finalise body_structlit_nowiden_mem

Theorem body_make_array_nowiden_mem:
  !cx ty t n es tops ctx func cenv env ty' st.
    (builtin_args_length_ok (MakeArray t n) (LENGTH es) ==>
     body_exprs_mem_ok cx es) /\
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Builtin ty (MakeArray t n) es) st /\
    (!e. MEM e es ==>
         int_calls_expr e = [] \/ lowered_value_type cenv e = expr_type e) ==>
    expr_sim_mem ctx func cenv cx ty' (Builtin ty (MakeArray t n) es) st /\
    expr_vv_sim_mem ctx func cenv cx ty' (Builtin ty (MakeArray t n) es) st
Proof
  rpt gen_tac >> strip_tac >>
  conj_asm2_tac
  >- (irule body_expr_sim_mem_of_vv_sim_mem >>
      reverse conj_tac >- (simp[] >> qexists_tac `env` >> simp[]) >>
      rpt strip_tac >> Cases_on `t`
      >- (drule compile_tuple_literal_inv >> simp[]) >>
      drule compile_array_literal_inv >> simp[]) >>
  Cases_on `t` >- suspend "tuple" >> suspend "array"
QED

Resume body_make_array_nowiden_mem[tuple]:
  rw[expr_vv_sim_mem_def] >>
  drule compile_tuple_literal_inv >> strip_tac >> gvs[] >>
  drule make_tuple_evaluated_layout >> strip_tac >> gvs[] >>
  gvs[exprLoweringTheory.tuple_literal_types_def, listTheory.MAP_MAP_o] >>
  `expr_sim_inv cenv cx env st` by gvs[expr_body_pre_def] >>
  `!e s. MEM e es /\ expr_sim_inv cenv cx env s ==>
    expr_body_pre cenv cx env e s` by
    (`!n t b. MakeArray t b <> Slice n` by simp[] >>
     metis_tac[expr_body_pre_builtin_arg]) >>
  `compatible_bound n (LENGTH es)` by
    gvs[expr_body_pre_def, vyperTypeSystemTheory.well_typed_expr_def,
      vyperTypeSystemTheory.well_typed_builtin_app_def] >>
  `body_exprs_mem_ok cx es` by
    (first_x_assum irule >>
     gvs[vyperContextTheory.builtin_args_length_ok_def]) >>
  `ci_mono sa sm` by metis_tac[ci_mono_compile_alloc_buffer, pairTheory.SND] >>
  `ci_mono sm sb` by
    metis_tac[ci_mono_compile_make_tuple_cfn, compile_expr_ci_mono, pairTheory.SND] >>
  `cs_extends sa sm /\ cs_extends sm sb` by
    (qpat_x_assum `ci_mono sa sm` mp_tac >>
     qpat_x_assum `ci_mono sm sb` mp_tac >> simp[ci_mono_def]) >>
  drule_all fn_has_code_split >> strip_tac >>
  `SUM (MAP (type_memory_bytes cenv o expr_type) es) < dimword (:256)` by
    (gvs[expr_body_pre_def, alloc_limits_expr_def] >>
     simp[wordsTheory.dimword_def] >> decide_tac) >>
  `type_memory_size_list tvs < dimword (:256)` by metis_tac[] >>
  drule_all exprSimAllocTheory.buffer_alloc_code >> strip_tac >>
  drule_all aggregate_buffer_alloc_counted_mem_any_block >> strip_tac >> gvs[] >>
  drule_at (Pat `compile_make_tuple _ _ _ _ _ _ _ = _`)
    bodyMemAggregateLoopsTheory.aggregate_make_tuple_sim_mem >>
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
  suspend "tuple_final_post"
QED

Resume body_make_array_nowiden_mem[tuple_final_post]:
  `eval_expr cx (Builtin (TupleT (MAP expr_type es)) (MakeArray NONE n) es)
    (st with gas_obs := gs) = (INL (Value (ArrayV (TupleV vs))),ee)` by
    (drule_all aggregate_eval_make_tuple >> simp[]) >>
  rpt (qpat_x_assum `gas_outcome _ _ _ _ _ _ _` kall_tac) >>
  `expr_body_pre cenv cx env
    (Builtin (TupleT (MAP expr_type es)) (MakeArray NONE n) es)
    (st with gas_obs := gs)` by simp[] >>
  `val_wf (TupleTV tvs) (ArrayV (TupleV vs))` by
    (irule aggregate_materialised_child_wf >>
     goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >>
     simp[expr_type_def, read_result_def, return_def] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `val_footprint (TupleTV tvs) (ArrayV (TupleV vs)) <= type_memory_size_list tvs` by
    (drule val_footprint_le >> simp[type_memory_size_def]) >>
  `MAP FDOM st.scopes = MAP FDOM ee.scopes` by
    (drule vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom >> simp[]) >>
  `!nm lb len. local_region cenv ee.scopes t' nm lb len ==>
     b + type_memory_size_list tvs <= lb \/ lb + len <= b` by
    (rpt strip_tac >> drule_all aggregate_buffer_clearance >> simp[]) >>
  `~expr_has_effect (Builtin (TupleT (MAP expr_type es)) (MakeArray NONE n) es) ==>
     pure_frame cenv func st sa s0 t'` by
    (rewrite_tac[expr_has_effect_thm] >> strip_tac >>
     qpat_x_assum `EVERY _ _ ==> _` mp_tac >>
     (impl_tac >- (qpat_x_assum `~EXISTS _ _` mp_tac >>
        simp_tac (srw_ss()) [listTheory.EVERY_MAP, listTheory.NOT_EXISTS, combinTheory.o_DEF])) >>
     strip_tac >>
     qpat_assum `FLOOKUP t.vs_allocas _ = SOME (b,_)` (fn th =>
       qpat_assum `!aid a. FLOOKUP t.vs_allocas aid = SOME a ==> _` (fn th2 =>
         assume_tac (MATCH_MP th2 th))) >>
     irule (Q.SPECL [`cenv`, `func`, `st`, `sa`, `sm`, `s0`, `s0`, `t'`]
       aggregate_pure_frame_buffer) >>
     qpat_assum `MEM (mk_inst sa.cs_next_id ALLOCA _ _) _` (irule_at Any) >>
     qpat_assum `FLOOKUP t'.vs_allocas _ = SOME (b,_)` (irule_at Any) >>
     qexists_tac `sm` >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY (simp[] >> NO_TAC) >>
     rpt gen_tac >> disch_tac >>
     qpat_x_assum `!p n. _ /\ (!i c sz. _) ==> _` irule >>
     pop_assum mp_tac >> rpt (pop_assum kall_tac) >>
     strip_tac >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> decide_tac) >>
  conj_asm1_tac
  >- (irule (SRULE [expr_type_def] (Q.INST
        [`e` |-> `Builtin (TupleT (MAP expr_type es)) (MakeArray NONE n) es`]
        (Q.INST [`es` |-> `st`] buffer_loop_memory_vv_post))) >>
      simp[expr_type_def, is_word_type_def, contextTheory.mk_ptr_def, contextTheory.base_ptr_def,
        venomStateTheory.eval_operand_def, val_in_memory_def] >>
      qexistsl [`b`,`sm`,`type_memory_size_list tvs`,`t`] >>
      simp[wordsTheory.dimword_def] >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qpat_x_assum `!aid p n. FLOOKUP t.vs_allocas aid = SOME (p,n) /\ _ ==> _` mp_tac >>
      qpat_x_assum `_ ==> pure_frame _ _ _ _ _ _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >>
      metis_tac[arithmeticTheory.ADD_COMM]) >>
  simp[expr_type_def, exprLoweringTheory.lowered_value_type_def] >>
  irule (SRULE [expr_type_def, exprLoweringTheory.lowered_value_type_def]
    (Q.INST [`e` |-> `Builtin (TupleT (MAP expr_type es)) (MakeArray NONE n) es`]
      (Q.INST [`es` |-> `st`] aggregate_allocated_result_store_bound_mem))) >>
  simp[expr_type_def, exprLoweringTheory.lowered_value_type_def,
       contextTheory.base_ptr_def] >>
  conj_tac >- fs[stmt_state_rel_def] >>
  reverse conj_tac >-
    (qexistsl [`cenv`, `ctx`, `func`, `n`, `s0`, `sa`, `sb`, `st`] >>
     gvs[expr_type_def, contextTheory.base_ptr_def]) >>
  qexistsl [`sa.cs_next_id`, `b`, `type_memory_size_list tvs`] >>
  simp[type_memory_size_def, contextTheory.mk_ptr_def,
       venomStateTheory.eval_operand_def] >>
  metis_tac[]
QED

Resume body_make_array_nowiden_mem[array]:
  rw[expr_vv_sim_mem_def] >>
  drule compile_array_literal_inv >> strip_tac >> gvs[] >>
  drule make_array_evaluated_layout >> strip_tac >> gvs[] >>
  `expr_sim_inv cenv cx env st` by gvs[expr_body_pre_def] >>
  `!e s. MEM e es /\ expr_sim_inv cenv cx env s ==>
    expr_body_pre cenv cx env e s` by
    (`!n t b. MakeArray t b <> Slice n` by simp[] >>
     metis_tac[expr_body_pre_builtin_arg]) >>
  `compatible_bound n (LENGTH es)` by
    gvs[expr_body_pre_def, vyperTypeSystemTheory.well_typed_expr_def,
      vyperTypeSystemTheory.well_typed_builtin_app_def] >>
  `body_exprs_mem_ok cx es` by
    (first_x_assum irule >> gvs[vyperContextTheory.builtin_args_length_ok_def]) >>
  `ci_mono sa sm` by metis_tac[ci_mono_compile_alloc_buffer, pairTheory.SND] >>
  `ci_mono sm sb` by
    metis_tac[ci_mono_compile_make_array_cfn, compile_expr_ci_mono, pairTheory.SND] >>
  `cs_extends sa sm /\ cs_extends sm sb` by
    (qpat_x_assum `ci_mono sa sm` mp_tac >>
     qpat_x_assum `ci_mono sm sb` mp_tac >> simp[ci_mono_def]) >>
  drule_all fn_has_code_split >> strip_tac >>
  `type_memory_bytes cenv (ArrayT x n) < dimword (:256)` by
    (gvs[expr_body_pre_def, alloc_limits_expr_def] >>
     simp[wordsTheory.dimword_def] >> decide_tac) >>
  drule_all exprSimAllocTheory.buffer_alloc_code >> strip_tac >>
  drule_all aggregate_buffer_alloc_counted_mem_any_block >> strip_tac >> gvs[] >>
  drule_at (Pat `compile_make_array _ _ _ _ _ _ _ _ = _`) aggregate_make_array_sim_mem >>
  disch_then drule >> disch_then drule >>
  disch_then (drule_at (Pat `lookup_var _ _ = _`)) >>
  disch_then (drule_at (Pat `MEM _ (fn_insts _)`)) >>
  simp[wordsTheory.dimword_def] >>
  disch_then (qspecl_then [`env`,`st`,`ctx`,`tops`] mp_tac) >> simp[] >>
  (impl_tac >- (conj_tac >- fs[wordsTheory.dimword_def] >>
    rpt strip_tac >>
    `regions_disjoint io (type_memory_size itv) b
       (type_memory_bytes cenv (ArrayT x n))` by
      (irule aggregate_alloca_immutable_sep >>
       goal_assum (drule_at (Pat `stmt_state_rel ctx _ _ _ _ _`)) >>
       qpat_x_assum `MEM inst (fn_insts func)` kall_tac >>
       goal_assum (drule_at (Pat `MEM _ (fn_insts _)`)) >>
       simp[venomInstTheory.mk_inst_def] >>
       goal_assum (drule_at Any) >> simp[]) >>
    gvs[regions_disjoint_def] >>
    qpat_x_assum `_ <= type_memory_bytes _ _` mp_tac >> decide_tac)) >> strip_tac >> gvs[] >>
  irule bodyDeclMemoryComposeTheory.gas_outcome_zero_prefix_mem >>
  qexists_tac `t` >>
  conj_tac >- gvs[fragGasModeTheory.gas_marked_path_def] >>
  `eval_expr cx (Builtin (ArrayT x n) (MakeArray (SOME x) n) es) =
    bind (eval_exprs cx es) (return o (\vs. Value (ArrayV (make_array_value tv n vs))))` by
    (irule aggregate_array_action_mem >> simp[]) >>
  qpat_assum `eval_expr _ _ = bind _ _` (fn th => once_rewrite_tac[th]) >>
  drule aggregate_outcome_source_run_mem >> strip_tac >>
  irule aggregate_outcome_map_mem >> goal_assum (drule_at Any) >>
  conj_tac >- (rpt strip_tac >> gvs[sumTheory.SUM_MAP]) >>
  rpt strip_tac >> gvs[sumTheory.SUM_MAP] >>
  suspend "array_final_post"
QED
Resume body_make_array_nowiden_mem[array_final_post]:
  `eval_expr cx (Builtin (ArrayT x n) (MakeArray (SOME x) n) es)
    (st with gas_obs := gs) = (INL (Value (ArrayV (make_array_value tv n vs))),ee)` by
    (simp[bind_def, return_def]) >>
  rpt (qpat_x_assum `gas_outcome _ _ _ _ _ _ _` kall_tac) >>
  `expr_body_pre cenv cx env (Builtin (ArrayT x n) (MakeArray (SOME x) n) es)
    (st with gas_obs := gs)` by simp[] >>
  `val_wf (ArrayTV tv n) (ArrayV (make_array_value tv n vs))` by
    (irule aggregate_materialised_child_wf >>
     goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >>
     simp[expr_type_def, read_result_def, return_def] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `type_memory_bytes cenv (ArrayT x n) = type_memory_size (ArrayTV tv n)` by
    metis_tac[expr_sim_inv_memory_size] >>
  `val_footprint (ArrayTV tv n) (ArrayV (make_array_value tv n vs)) <=
    type_memory_bytes cenv (ArrayT x n)` by
    (drule val_footprint_le >> simp[]) >>
  `MAP FDOM st.scopes = MAP FDOM ee.scopes` by
    (drule vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom >> simp[]) >>
  `!nm lb len. local_region cenv ee.scopes t' nm lb len ==>
     b + type_memory_bytes cenv (ArrayT x n) <= lb \/ lb + len <= b` by
    (rpt strip_tac >> drule_all aggregate_buffer_clearance >> simp[]) >>
  `~expr_has_effect (Builtin (ArrayT x n) (MakeArray (SOME x) n) es) ==>
     pure_frame cenv func st sa s0 t'` by
    (rewrite_tac[expr_has_effect_thm] >> strip_tac >>
     qpat_x_assum `EVERY _ _ ==> _` mp_tac >>
     (impl_tac >- (qpat_x_assum `~EXISTS _ _` mp_tac >>
        simp_tac (srw_ss()) [listTheory.EVERY_MAP, listTheory.NOT_EXISTS, combinTheory.o_DEF])) >>
     strip_tac >>
     qpat_assum `FLOOKUP t.vs_allocas _ = SOME (b,_)` (fn th =>
       qpat_assum `!aid a. FLOOKUP t.vs_allocas aid = SOME a ==> _` (fn th2 =>
         assume_tac (MATCH_MP th2 th))) >>
     irule (Q.SPECL [`cenv`, `func`, `st`, `sa`, `sm`, `s0`, `s0`, `t'`]
       aggregate_pure_frame_buffer) >>
     qpat_assum `MEM (mk_inst sa.cs_next_id ALLOCA _ _) _` (irule_at Any) >>
     qpat_assum `FLOOKUP t'.vs_allocas _ = SOME (b,_)` (irule_at Any) >>
     qexists_tac `sm` >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY (simp[] >> NO_TAC) >>
     rpt gen_tac >> disch_tac >>
     qpat_x_assum `!p n. _ /\ (!i c sz. _) ==> _` irule >>
     pop_assum mp_tac >> rpt (pop_assum kall_tac) >>
     strip_tac >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> decide_tac) >>
  conj_asm1_tac
  >- (irule (SRULE [expr_type_def] (Q.INST
        [`e` |-> `Builtin (ArrayT x n) (MakeArray (SOME x) n) es`]
        (Q.INST [`es` |-> `st`] buffer_loop_memory_vv_post))) >>
      simp[expr_type_def, is_word_type_def, contextTheory.mk_ptr_def,
        venomStateTheory.eval_operand_def] >>
      qexistsl [`b`,`sm`,`type_memory_bytes cenv (ArrayT x n)`,`t`] >>
      simp[wordsTheory.dimword_def] >>
      conj_tac >- metis_tac[] >>
      conj_tac >- metis_tac[arithmeticTheory.ADD_COMM] >>
      conj_tac >-
        (rpt gen_tac >>
         qpat_x_assum `!aid p n. FLOOKUP t.vs_allocas aid = SOME (p,n) /\ _ ==> _` mp_tac >>
         qpat_x_assum `!name p n. local_region cenv st.scopes t name p n <=> _` mp_tac >>
         qpat_x_assum `t.vs_memory = s0.vs_memory` mp_tac >>
         qpat_x_assum `type_memory_bytes cenv (ArrayT x n) = _` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[arithmeticTheory.ADD_COMM]) >>
      `LENGTH vs = LENGTH es` by (drule eval_exprs_length >> simp[]) >>
      Cases_on `n`
      >- (gvs[vyperValueTheory.compatible_bound_def] >>
          irule exprSimAggregateEncodingTheory.fixed_array_from_dense >> simp[]) >>
      gvs[vyperValueTheory.make_array_value_def, val_in_memory_def]) >>
  simp[expr_type_def, exprLoweringTheory.lowered_value_type_def] >>
  irule (SRULE [expr_type_def, exprLoweringTheory.lowered_value_type_def]
    (Q.INST [`e` |-> `Builtin (ArrayT x n) (MakeArray (SOME x) n) es`]
      (Q.INST [`es` |-> `st`] aggregate_allocated_result_store_bound_mem))) >>
  simp[expr_type_def, exprLoweringTheory.lowered_value_type_def,
       contextTheory.mk_ptr_def] >>
  conj_tac >- fs[stmt_state_rel_def] >>
  reverse conj_tac >-
    (qexistsl [`cenv`,`ctx`,`es`,`func`,`s0`,`sa`,`sb`,`st`] >>
     gvs[contextTheory.mk_ptr_def]) >>
  qexistsl [`sa.cs_next_id`,`b`,`type_memory_bytes cenv (ArrayT x n)`] >>
  simp[venomStateTheory.eval_operand_def] >> metis_tac[]
QED
Finalise body_make_array_nowiden_mem

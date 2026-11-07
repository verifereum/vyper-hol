(* Body-aware MakeArray integration over the counted widened-child loops. *)
Theory exprSimAggregateBodyCase
Ancestors
  exprSimAggregateBodyLoops exprSimAggregatesAllocCounted exprSimAggregateLoops
  exprSimAggregateBodySource exprSimAggregateBodyAlloc stmtSimDeclCompose
  exprSimAggregateLayout exprSimAggregateSource exprSimAggregateChildren
  exprSimHyps exprSimHypsDefs exprSimDefs exprSimSource exprSimProps
  loweringPosts exprLoweringProps exprLowering compileEnv
  gasOutcome gasSummary gasContext fragGasMode fragGasPath fragGasSeq fragExec
  vyperInterpreter vyperState vyperTypeSystem valueEncoding

Theorem compile_make_array_body_vv_case:
  !ctx func cenv cx ann topt bnd args.
    exprs_case F ctx func cenv cx args /\
    acyclic_struct_metadata cenv.ce_struct_fields ==>
    expr_vv_case F ctx func cenv cx (Builtin ann (MakeArray topt bnd) args)
Proof
  rpt gen_tac >> strip_tac >>
  simp[expr_vv_case_def, expr_vv_sim_def] >> rpt gen_tac >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `topt`
  >- (drule compile_tuple_literal_inv >> strip_tac >>
      drule make_tuple_evaluated_layout >> strip_tac >>
      `ci_mono sa sm /\ ci_mono sm sb` by
        metis_tac[ci_mono_compile_alloc_buffer, ci_mono_compile_make_tuple_cfn,
                  compile_expr_ci_mono, pairTheory.SND] >>
      `fn_has_code sa sm func /\ fn_has_code sm sb func` by
        metis_tac[fn_has_code_split, ci_mono_def] >>
      `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
      `type_memory_size_list tvs < dimword (:256)` by
        (drule expr_body_pre_copy_ok >>
         simp[vyperASTTheory.expr_type_def, is_word_type_def] >>
         disch_then (qspec_then `TupleTV tvs` mp_tac) >>
         gvs[valueEncodingTheory.type_memory_size_def,
             wordsTheory.dimword_def]) >>
      drule buffer_alloc_counted >>
      disch_then (drule_at (Pat `fn_has_code sa sm func`)) >>
      disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
      simp[] >> strip_tac >>
      `!e st. MEM e args /\ expr_sim_inv cenv cx env st ==>
         expr_body_pre cenv cx env e st /\ (F ==> int_calls_expr e = [])` by
        (rpt strip_tac >> irule expr_body_pre_builtin_arg >>
         conj_tac >- simp[] >> qexistsl_tac [`ann`, `args`, `MakeArray NONE bnd`, `es`] >> simp[]) >>
      `cenv.ce_is_ctor ==> !name itv iv io.
        FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc io) /\
        FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
          | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (itv,iv) ==>
        regions_disjoint io (type_memory_size itv) b (type_memory_size_list tvs)` by
        (drule aggregate_body_alloc_immutable_prefix >>
         disch_then (drule_at (Pat `fn_has_code sa sm func`)) >>
         disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ t`)) >>
         disch_then (qspec_then `type_memory_size_list tvs` mp_tac) >>
         gvs[] >> metis_tac[]) >>
      qpat_x_assum `compile_make_tuple _ _ _ _ _ _ = _` mp_tac >>
      asm_rewrite_tac[] >> strip_tac >>
      drule aggregate_body_make_tuple_sim >>
      disch_then (drule_at (Pat `OPT_MMAP _ _ = _`)) >>
      disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ t`)) >>
      disch_then (qspec_then `env` mp_tac) >> simp[] >>
      disch_then (qspecl_then [`inst`, `b`, `type_memory_size_list tvs`] mp_tac) >>
      simp[] >> (impl_tac >- metis_tac[]) >> strip_tac >>
      `compatible_bound bnd (LENGTH args)` by
        fs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
      `eval_expr cx (Builtin ann (MakeArray NONE bnd) args) =
       bind (eval_exprs cx args) (return o (\vs. Value (ArrayV (TupleV vs))))` by
        (simp[FUN_EQ_THM] >> gen_tac >>
         Cases_on `eval_exprs cx args x'` >>
         drule aggregate_eval_make_tuple >> simp[bind_def, return_def] >>
         disch_then drule >> Cases_on `q` >> simp[]) >>
      irule gas_outcome_zero_prefix >> goal_assum (drule_at Any) >>
      gvs[] >>
      irule gas_outcome_map_source_run >> goal_assum (drule_at Any) >>
      conj_tac >- (simp[] >> rpt strip_tac >> gvs[]) >>
      simp[] >> rpt strip_tac >> gvs[] >> suspend "tuple_post")
  >> suspend "array_case"
QED

Resume compile_make_array_body_vv_case[tuple_post]:
  qmatch_goalsub_abbrev_tac `vv_post _ _ _ _ e` >>
  `TupleT (MAP expr_type args) = expr_type e` by
    simp[Abbr `e`, vyperASTTheory.expr_type_def] >>
  pop_assum SUBST1_TAC >> irule buffer_loop_memory_vv_post >>
  simp[Abbr `e`, vyperASTTheory.expr_type_def, post_value_type_def, is_word_type_def,
       contextTheory.mk_ptr_def] >>
  qexistsl_tac [`b`, `sm`, `type_memory_size_list tvs`, `t`] >>
  simp[venomStateTheory.eval_operand_def, valueEncodingTheory.val_in_memory_def] >>
  conj_tac >- (rpt strip_tac >>
    `FLOOKUP t'.vs_allocas inst.inst_id = SOME (b,type_memory_size_list tvs)` by metis_tac[] >>
    drule_at (Pat `local_region _ _ _ _ _ _`) aggregate_alloca_slice_excludes_local >>
    disch_then (qspecl_then [`x`, `0`, `type_memory_size_list tvs`] mp_tac) >>
    disch_then (drule_at (Pat `MEM _ _`)) >> simp[] >>
    disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >> simp[]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (rpt strip_tac >> first_x_assum irule >> simp[] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  `val_wf (TupleTV tvs) (ArrayV (TupleV vs))` suffices_by
    (strip_tac >> simp[] >> drule val_footprint_le >>
     simp[valueEncodingTheory.type_memory_size_def]) >>
  `eval_expr cx (Builtin (TupleT (MAP expr_type args)) (MakeArray NONE bnd) args)
    (es with gas_obs := gs) = (INL (Value (ArrayV (TupleV vs))),ee)` by
    simp[bind_def, return_def] >>
  irule aggregate_materialised_child_wf >>
  goal_assum (drule_at Any) >>
  simp[expr_body_pre_gas_obs, vyperASTTheory.expr_type_def, read_result_def, return_def] >>
  goal_assum (drule_at Any)
QED

Resume compile_make_array_body_vv_case[array_case]:
  rename1 `MakeArray (SOME et) bnd` >>
  drule compile_array_literal_inv >> strip_tac >>
  drule make_array_evaluated_layout >> strip_tac >> gvs[] >>
  `ci_mono sa sm /\ ci_mono sm sb` by
    metis_tac[ci_mono_compile_alloc_buffer, ci_mono_compile_make_array_cfn,
              compile_expr_ci_mono, pairTheory.SND] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fn_has_code_split, ci_mono_def] >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  `type_memory_bytes cenv (ArrayT et bnd) < dimword (:256)` by
    (drule expr_body_pre_copy_ok >>
     simp[vyperASTTheory.expr_type_def, is_word_type_def] >>
     gvs[wordsTheory.dimword_def]) >>
  drule buffer_alloc_counted >>
  disch_then (drule_at (Pat `fn_has_code sa sm func`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  simp[] >> strip_tac >>
  `!e st. MEM e args /\ expr_sim_inv cenv cx env st ==>
     expr_body_pre cenv cx env e st` by
    (rpt strip_tac >> irule expr_body_pre_builtin_arg >>
     conj_tac >- simp[] >>
     qexistsl_tac [`ArrayT et bnd`, `args`, `MakeArray (SOME et) bnd`, `es`] >> simp[]) >>
  `cenv.ce_is_ctor ==> !name itv iv io.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv) b
      ((if (case bnd of Fixed _ => F | Dynamic _ => T) then 32 else 0) +
       LENGTH args * type_memory_size tv)` by
    (drule aggregate_body_alloc_immutable_prefix >>
     disch_then (drule_at (Pat `fn_has_code sa sm func`)) >>
     disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ t`)) >>
     disch_then (qspec_then
       `((if (case bnd of Fixed _ => F | Dynamic _ => T) then 32 else 0) +
         LENGTH args * type_memory_size tv)` mp_tac) >>
     gvs[] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  qpat_x_assum `compile_make_array _ _ _ _ _ _ _ _ = _` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  drule aggregate_body_make_array_sim >>
  disch_then (drule_at (Pat `evaluate_type _ et = _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ t`)) >>
  disch_then (qspec_then `env` mp_tac) >> simp[] >>
  disch_then (drule_at (Pat `compile_make_array _ _ _ _ _ _ _ _ = _`)) >>
  disch_then (qspecl_then [`inst`, `b`, `type_memory_bytes cenv (ArrayT et bnd)`] mp_tac) >>
  simp[] >> (impl_tac >- metis_tac[arithmeticTheory.ADD_COMM]) >> strip_tac >>
  `compatible_bound bnd (LENGTH args)` by
    fs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
  `eval_expr cx (Builtin (ArrayT et bnd) (MakeArray (SOME et) bnd) args) =
    bind (eval_exprs cx args) (return o (\vs. Value (ArrayV (make_array_value tv bnd vs))))` by
    (simp[FUN_EQ_THM] >> gen_tac >> Cases_on `eval_exprs cx args x'` >>
     qpat_x_assum `evaluate_type _ (ArrayT _ _) = _` kall_tac >>
     drule_at (Pat `eval_exprs _ _ _ = _`) aggregate_eval_make_array >>
     disch_then (drule_at (Pat `evaluate_type _ et = _`)) >>
     simp[bind_def, return_def] >> Cases_on `q` >> simp[]) >>
  irule gas_outcome_zero_prefix >> goal_assum (drule_at Any) >> gvs[] >>
  irule gas_outcome_map_source_run >> goal_assum (drule_at Any) >>
  conj_tac >- (simp[] >> rpt strip_tac >> gvs[]) >>
  simp[] >> rpt strip_tac >> gvs[] >> suspend "array_post"
QED

Resume compile_make_array_body_vv_case[array_post]:
  qmatch_goalsub_abbrev_tac `vv_post _ _ _ _ e` >>
  `ArrayT et bnd = expr_type e` by
    simp[Abbr `e`, vyperASTTheory.expr_type_def] >>
  pop_assum SUBST1_TAC >> irule buffer_loop_memory_vv_post >>
  simp[Abbr `e`, vyperASTTheory.expr_type_def, post_value_type_def, is_word_type_def,
       contextTheory.mk_ptr_def] >>
  qexistsl_tac [`b`, `sm`, `type_memory_bytes cenv (ArrayT et bnd)`, `t`] >>
  simp[venomStateTheory.eval_operand_def] >>
  conj_tac >- (rpt strip_tac >>
    `FLOOKUP t'.vs_allocas inst.inst_id = SOME (b,type_memory_bytes cenv (ArrayT et bnd))` by metis_tac[] >>
    drule_at (Pat `local_region _ _ _ _ _ _`) aggregate_alloca_slice_excludes_local >>
    disch_then (qspecl_then [`x`, `0`, `type_memory_bytes cenv (ArrayT et bnd)`] mp_tac) >>
    disch_then (drule_at (Pat `MEM _ _`)) >> simp[] >>
    disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >> simp[]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (rpt strip_tac >> first_x_assum irule >> simp[] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  `val_wf (ArrayTV tv bnd) (ArrayV (make_array_value tv bnd vs))` by
    (`eval_expr cx (Builtin (ArrayT et bnd) (MakeArray (SOME et) bnd) args)
      (es with gas_obs := gs) = (INL (Value (ArrayV (make_array_value tv bnd vs))),ee)` by
       simp[bind_def, return_def] >>
     irule aggregate_materialised_child_wf >> goal_assum (drule_at Any) >>
     simp[expr_body_pre_gas_obs, vyperASTTheory.expr_type_def, read_result_def, return_def] >>
     goal_assum (drule_at Any)) >>
  conj_tac >- (drule val_footprint_le >>
    `type_memory_bytes cenv (ArrayT et bnd) = type_memory_size (ArrayTV tv bnd)` by
       metis_tac[expr_sim_inv_memory_size] >> simp[]) >>
  simp[] >>
  `LENGTH vs = LENGTH args` by (drule eval_exprs_length >> simp[]) >>
  Cases_on `bnd` >> gvs[vyperValueTheory.compatible_bound_def]
  >- (irule exprSimAggregateEncodingTheory.fixed_array_from_dense >> simp[]) >>
  simp[vyperValueTheory.make_array_value_def, val_in_memory_def]
QED

Finalise compile_make_array_body_vv_case

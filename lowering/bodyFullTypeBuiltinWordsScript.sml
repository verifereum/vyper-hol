Theory bodyFullTypeBuiltinWords
Ancestors
  bodyFullOfVV bodyFullPreds bodySimFull gasOutcomeFullCompose
  exprSimHyps exprSimHypsDefs exprSimSource exprSimProps exprLoweringProps
  exprLowering loweringPosts exprSimMemDefs bodyPtrDefs gasShadow fragGasOriginPtr
  ptrDiscipline compileEnv context valueEncoding vyperTyping vyperTypeSystem
  vyperContext vyperValueOperation vyperAST vyperInterpreter vyperState venomState

Theorem type_builtin_literal_vv_full[local]:
  expr_body_pre cenv cx env (TypeBuiltin ann tb typ args) es /\
  is_word_type ann /\
  (!gs. eval_expr cx (TypeBuiltin ann tb typ args) (es with gas_obs := gs) =
        (INL (Value v), es with gas_obs := gs)) /\
  (!sa. compile_expr cenv ty (TypeBuiltin ann tb typ args) sa =
        (StackValue ann (Lit w), sa)) /\
  (!rt. evaluate_type (get_tenv cx) ann = SOME rt ==>
        typed_val_to_w256 rt v = w) ==>
  expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (TypeBuiltin ann tb typ args) es
Proof
  strip_tac >> rw[expr_vv_sim_full_def] >>
  qpat_x_assum `!sa. compile_expr _ _ _ sa = _`
    (qspec_then `sa` assume_tac) >> gvs[] >>
  irule gas_outcome_full_pure >>
  reverse conj_tac >- simp[] >>
  qexistsl_tac [`G0`, `es`, `INL (Value v)`, `s0`, `tn0`] >>
  simp[] >> rpt strip_tac >> first_x_assum drule >> strip_tac >>
  simp[gas_origin_ptr_path_rules, vv_store_bound_def, vv_location_def,
       expr_type_def, ptr_vv_ok_def, ptr_val_ok_def,
       read_result_def, return_def, op_taint_def,
       ghost_inv_at_def, ghost_kept_at_def] >>
  `stmt_state_rel H ctx func cenv cx (es with gas_obs := []) s0` by
    (drule msg_gas_state_frame >>
     disch_then (qspecl_then [`s0.vs_gas_readings`, `s0.vs_inst_idx`, `[]`] mp_tac) >>
     simp[NoAsms]) >>
  simp[vv_post_def, vv_holds_def, vv_at_def, vv_storage_live_def,
       read_result_def, return_def, expr_val_rel_def, expr_val_at_def,
       expr_type_def, eval_operand_def, locals_kept_def] >>
  gvs[ghost_inv_at_def, vyperStorageFootprintTheory.storage_well_formed_on_def]
  >- (rpt gen_tac >>
      qpat_x_assum `!b slot tv. _` (qspec_then `b` mp_tac) >>
      Cases_on `b` >> simp[vyperStorageBackendTheory.get_storage_def])
  >- (gvs[op_taint_def] >> metis_tac[]) >>
  gvs[expr_type_def] >> gvs[vv_location_def]
QED

Theorem bound_builtin_vv_full[local]:
  MEM tb [MaxValue; MinValue; Epsilon] /\
  expr_body_pre cenv cx env (TypeBuiltin ann tb typ args) es ==>
  expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (TypeBuiltin ann tb typ args) es
Proof
  strip_tac >>
  `args = [] /\ ann = typ /\ is_numeric_type typ /\
   (tb = Epsilon ==> typ = BaseT DecimalT)` by
    (Cases_on `tb` >>
     gvs[expr_body_pre_def, well_typed_expr_def,
         well_typed_type_builtin_args_def, type_builtin_result_ok_def]) >>
  drule expr_body_pre_type_evaluates >> simp[expr_type_def] >> strip_tac >>
  `(?n. typ = BaseT (UintT n)) \/ (?n. typ = BaseT (IntT n)) \/
   typ = BaseT DecimalT` by
    (Cases_on `typ` >> gvs[] >> rename1 `BaseT bt` >> Cases_on `bt` >> gvs[]) >>
  gvs[] >>
  irule type_builtin_literal_vv_full >> simp[is_word_type_def] >>
  simp[compile_expr_type_builtin_dispatch, Once compile_expr_def,
       comp_return_def, type_bounds_def, type_bits_def, is_signed_type_def] >>
  simp[Once evaluate_def, type_builtin_args_length_ok_def, type_check_def,
       assert_def, ignore_bind_def, bind_def, return_def] >>
  simp[Once evaluate_def, bind_def, return_def, lift_sum_def,
       evaluate_type_builtin_def, evaluate_max_value_def, evaluate_min_value_def] >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  simp[integerTheory.INT_SUB, return_def] >>
  PURE_REWRITE_TAC [typed_val_to_w256_def, val_to_w256_def,
    integer_wordTheory.i2w_0, integer_wordTheory.i2w_pos] >>
  simp[] >> metis_tac[]
QED

Theorem bound_builtin_expr_full_ok:
  !cx ann tb typ args.
    MEM tb [MaxValue; MinValue; Epsilon] ==>
    body_expr_full_ok cx (TypeBuiltin ann tb typ args)
Proof
  rpt gen_tac >> strip_tac >>
  simp[body_expr_full_ok_def] >> rpt gen_tac >> strip_tac >>
  `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx ty (TypeBuiltin ann tb typ args) es` by
    (irule bound_builtin_vv_full >> metis_tac[]) >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  irule expr_sim_full_of_vv >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> drule_all exprSimHypsTheory.expr_body_pre_copy_ok >> simp[]) >>
  qpat_assum `expr_body_pre _ _ _ (TypeBuiltin _ _ _ _) _`
    (mp_tac o MATCH_MP expr_body_pre_type_evaluates) >>
  simp[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
  qexists_tac `x` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  `expr_body_pre cenv cx env (TypeBuiltin ann tb typ args)
     (es with gas_obs := gs)` by simp[] >>
  drule_all exprSimSourceTheory.expr_body_pre_runtime_typed >>
  strip_tac >> gvs[] >> metis_tac[]
QED

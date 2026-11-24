(* Numeric type bounds compile to literal operands and leave both states alone. *)
Theory bodyTypeBoundWordsMods
Ancestors
  bodyFullPredsMods bodyFullPostsMods bodyFullShadowBodyInv exprBodyPreProps exprSimHyps
  exprLoweringProps exprLowering loweringPosts exprSimMemDefs
  gasShadowCompileStmtHelpers gasShadowState gasShadow
  gasOutcomeFullPostMods fragGasOriginPtr bodyPtrDefs ptrDiscipline
  vyperStorageFootprint loweringStateRelDefs bodyInvSplit
  vyperTyping vyperTypeSystem vyperValue vyperValueOperation
  vyperInterpreter vyperAST vyperContext vyperState valueEncoding compileEnv venomState loweringSlice
  list

Theorem bound_int_shape[local]:
  is_int_type typ <=> (?m. typ = BaseT (IntT m)) \/ (?m. typ = BaseT (UintT m))
Proof
  Cases_on `typ` >> simp[] >> rename1 `BaseT bt` >> Cases_on `bt` >> simp[]
QED

Theorem bound_word_literal[local]:
  MEM tb [MaxValue; MinValue; Epsilon] /\
  well_typed_expr env (TypeBuiltin ann tb typ args) ==>
  args = [] /\ is_word_type ann /\
  ?v w.
    (!st. eval_expr cx (TypeBuiltin ann tb typ args) st = (INL (Value v),st)) /\
    (!ce ty sa. compile_expr ce ty (TypeBuiltin ann tb typ args) sa =
                 (StackValue ann (Lit w),sa)) /\
    (!s. expr_val_rel cx ann v (Lit w) s)
Proof
  simp[] >> strip_tac >>
  gvs[well_typed_expr_def, well_typed_type_builtin_args_def,
      type_builtin_result_ok_def, MAP_EQ_NIL, bound_int_shape] >>
  gvs[is_word_type_def, well_formed_type_def, vyperValueTheory.evaluate_type_def,
      optionTheory.IS_SOME_EXISTS] >>
  simp[compile_expr_type_builtin_dispatch, Once compile_expr_def,
       comp_return_def, type_bounds_def, type_bits_def, is_signed_type_def] >>
  simp[Once evaluate_def, type_builtin_args_length_ok_def, type_check_def,
       assert_def, ignore_bind_def, bind_def, return_def] >>
  simp[Once evaluate_def, bind_def, return_def, lift_sum_def,
       evaluate_type_builtin_def, evaluate_max_value_def, evaluate_min_value_def] >>
  simp[expr_val_rel_def, eval_operand_def, is_word_type_def,
       vyperValueTheory.evaluate_type_def, integerTheory.INT_SUB, return_def] >>
  PURE_REWRITE_TAC[typed_val_to_w256_def, val_to_w256_def,
    integer_wordTheory.i2w_0, integer_wordTheory.i2w_pos] >>
  simp[]
QED

Theorem bound_frame_gas_obs[local]:
  stmt_state_rel H ctx func cenv cx es s /\
  immutable_frame_mods func cenv cx es s /\
  storage_well_formed_on cx es (FST H) /\
  ghost_inv_at_mods D lo d cenv cx es G tn s ==>
  stmt_state_rel H ctx func cenv cx (es with gas_obs := []) s /\
  immutable_frame_mods func cenv cx (es with gas_obs := []) s /\
  storage_well_formed_on cx (es with gas_obs := []) (FST H) /\
  ghost_inv_at_mods D lo d cenv cx (es with gas_obs := []) G tn s
Proof
  strip_tac >> conj_tac
  >- (drule msg_gas_state_frame >>
      disch_then (qspecl_then [`s.vs_gas_readings`, `s.vs_inst_idx`, `[]`] mp_tac) >>
      simp[stmt_state_rel_inst_idx]) >>
  conj_tac
  >- (qpat_assum `immutable_frame_mods _ _ _ es _` mp_tac >>
      PURE_REWRITE_TAC[immutable_frame_mods_def, immutables_rel_mods_def,
        immutable_alloca_sep_mods_def, immutable_alloca_sep_def,
        loweringStateRelDefsTheory.immutables_rel_def, evaluation_state_accfupds] >> simp[]) >>
  conj_tac
  >- (`storage_well_formed_on cx (es with gas_obs := []) (FST H) <=>
       storage_well_formed_on cx es (FST H)` suffices_by simp[] >>
      irule storage_well_formed_on_backends >> simp[]) >>
  qpat_assum `ghost_inv_at_mods _ _ _ _ _ es _ _ _` mp_tac >>
  PURE_ONCE_REWRITE_TAC[ghost_inv_at_mods_def] >>
  PURE_REWRITE_TAC[evaluation_state_accfupds] >> simp[]
QED

Theorem bound_shadow_literal[local]:
  (!ce ty s. compile_expr ce ty (TypeBuiltin ann tb typ []) s =
             (StackValue ann (Lit w),s)) /\ gas_shadow_state sa shadow_sa ==>
  compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr (TypeBuiltin ann tb typ []))
    shadow_sa = (StackValue ann (Lit w),shadow_sa)
Proof
  strip_tac >>
  `gas_shadow_compiles (compile_expr cenv ty (TypeBuiltin ann tb typ []))
    (compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr (TypeBuiltin ann tb typ [])))`
    by irule gas_shadow_stmt_compile_expr_env >>
  qpat_x_assum `gas_shadow_compiles _ _`
    (qspecl_then [`sa`,`shadow_sa`] mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
  simp[gas_shadow_expr_def]
QED

val bound_shadow_tac =
  `compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr (TypeBuiltin ann tb typ []))
      shadow_sa = (StackValue ann (Lit w),shadow_sa)` by
    (irule bound_shadow_literal >> simp[] >> qexists_tac `sa` >> simp[]);

Theorem bound_word_value_sim[local]:
  is_word_type ann /\
  (!st. eval_expr cx (TypeBuiltin ann tb typ []) st = (INL (Value v),st)) /\
  (!ce ty sa. compile_expr ce ty (TypeBuiltin ann tb typ []) sa =
               (StackValue ann (Lit w),sa)) /\
  (!s. expr_val_rel cx ann v (Lit w) s) ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (TypeBuiltin ann tb typ []) es
Proof
  strip_tac >> rw[expr_sim_full_mods_def] >> bound_shadow_tac >>
  `op = Lit w /\ sb = sa /\ shadow_sb = shadow_sa` by
    (qpat_x_assum `lower_value _ _ _ (gas_shadow_expr _) _ = _` mp_tac >>
     qpat_x_assum `lower_value _ cenv _ _ _ = _` mp_tac >>
     simp[lower_value_def, comp_bind_def, unwrap_value_def, comp_return_def]) >>
  gvs[] >> irule gas_outcome_full_mods_pure >> simp[] >>
  qexistsl_tac [`G0`,`es`,`INL v`,`s0`,`tn0`] >>
  simp[bind_def, read_result_def, return_def, gas_origin_ptr_path_rules, expr_type_def] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  drule_all_then strip_assume_tac bound_frame_gas_obs >>
  simp[expr_post_mods_def, expr_post_def, expr_store_bound_def,
       expr_val_at_def, expr_type_def, ptr_val_ok_def, op_taint_def,
       locals_kept_def, ghost_kept_at_def]
QED

Theorem bound_word_vv_sim[local]:
  is_word_type ann /\
  (!st. eval_expr cx (TypeBuiltin ann tb typ []) st = (INL (Value v),st)) /\
  (!ce ty sa. compile_expr ce ty (TypeBuiltin ann tb typ []) sa =
               (StackValue ann (Lit w),sa)) /\
  (!s. expr_val_rel cx ann v (Lit w) s) ==>
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (TypeBuiltin ann tb typ []) es
Proof
  strip_tac >> rw[expr_vv_sim_full_mods_def] >> bound_shadow_tac >>
  gvs[] >> irule gas_outcome_full_mods_pure >> simp[] >>
  qexistsl_tac [`G0`,`es`,`INL (Value v)`,`s0`,`tn0`] >>
  simp[gas_origin_ptr_path_rules, expr_type_def, contextTheory.vv_location_def] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  drule_all_then strip_assume_tac bound_frame_gas_obs >>
  simp[vv_post_mods_def, vv_holds_mods_def, vv_place_ptr_mods_def,
       vv_holds_def, vv_at_def, vv_storage_live_def, vv_place_ptr_def,
       vv_store_bound_def, lowered_value_type_def, contextTheory.vv_location_def,
       read_result_def, return_def, expr_val_at_def, expr_type_def,
       ptr_vv_ok_def, ptr_val_ok_def, op_taint_def, locals_kept_def,
       ghost_kept_at_def]
QED

Theorem bound_builtin_expr_full_ok_mods:
  !mods exps cx ann tb typ args. MEM tb [MaxValue; MinValue; Epsilon] ==>
    body_expr_full_ok_mods mods exps cx (TypeBuiltin ann tb typ args)
Proof
  rpt gen_tac >> strip_tac >> simp[Once body_expr_full_ok_mods_def] >>
  rpt gen_tac >> strip_tac >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule_all_then (qspec_then `cx` strip_assume_tac) bound_word_literal >>
  qpat_x_assum `args = []` SUBST_ALL_TAC >>
  conj_tac
  >- (irule bound_word_value_sim >> simp[] >> qexistsl_tac [`v`,`w`] >> simp[]) >>
  irule bound_word_vv_sim >> simp[] >> qexistsl_tac [`v`,`w`] >> simp[]
QED

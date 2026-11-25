(* Folding MethodId to bytes4 emits no instructions. *)
Theory bodyMethodIdFixedLiteralMods
Ancestors
  bodyFullPostsMods bodyFullShadowBodyInv exprSimHash exprLoweringProps
  gasOutcomeFullPostMods gasShadowCompileStmtHelpers
  gasShadowState gasShadow loweringPosts exprSimMemDefs loweringStateRelDefs
  bodyInvSplit bodyPtrDefs vyperStorageFootprint exprLowering compileEnv
  vyperInterpreter vyperAST vyperState vyperValue vyperContext valueEncoding
  fragGasOriginPtr ptrDiscipline venomState loweringSlice

Theorem fixed_method_id_compile[local]:
  method_id_literal (Literal la l) = SOME bs ==>
  !ce ty sa. compile_expr ce ty (Builtin (BaseT (BytesT (Fixed 4))) MethodId [Literal la l]) sa =
    (StackValue (BaseT (BytesT (Fixed 4)))
      (Lit (typed_val_to_w256 (BaseTV (BytesT (Fixed 4)))
                            (BytesV (TAKE 4 (Keccak_256_w64 bs))))),sa)
Proof
  strip_tac >> drule compile_expr_method_id_literal >>
  simp[compile_literal_vv_def, comp_return_def]
QED

Theorem fixed_method_id_eval[local]:
  method_id_literal (Literal la l) = SOME bs ==>
  !cx st. eval_expr cx (Builtin (BaseT (BytesT (Fixed 4))) MethodId [Literal la l]) st =
    (INL (Value (BytesV (TAKE 4 (Keccak_256_w64 bs)))),st)
Proof
  strip_tac >> rpt gen_tac >>
  Cases_on `eval_expr cx (Builtin (BaseT (BytesT (Fixed 4))) MethodId [Literal la l]) st` >>
  drule_all eval_expr_method_id_literal >> simp[]
QED

Theorem fixed_method_id_frame[local]:
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

Theorem fixed_method_id_value[local]:
  method_id_literal (Literal la l) = SOME bs ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty
    (Builtin (BaseT (BytesT (Fixed 4))) MethodId [Literal la l]) es
Proof
  strip_tac >> rw[expr_sim_full_mods_def] >>
  qabbrev_tac `v = BytesV (TAKE 4 (Keccak_256_w64 bs))` >>
  qabbrev_tac `w = typed_val_to_w256 (BaseTV (BytesT (Fixed 4))) v` >>
  `!ce s. compile_expr ce ty
      (Builtin (BaseT (BytesT (Fixed 4))) MethodId [Literal la l]) s =
      (StackValue (BaseT (BytesT (Fixed 4))) (Lit w),s)` by
    simp[fixed_method_id_compile, Abbr `v`, Abbr `w`] >>
  `!st. eval_expr cx (Builtin (BaseT (BytesT (Fixed 4))) MethodId [Literal la l]) st =
     (INL (Value v),st)` by
    (drule fixed_method_id_eval >> simp[Abbr `v`]) >>
  `gas_shadow_compiles
     (compile_expr cenv ty (Builtin (BaseT (BytesT (Fixed 4))) MethodId [Literal la l]))
     (compile_expr (gas_shadow_env T cenv) ty
       (gas_shadow_expr (Builtin (BaseT (BytesT (Fixed 4))) MethodId [Literal la l])))` by
    irule gas_shadow_stmt_compile_expr_env >>
  `compile_expr (gas_shadow_env T cenv) ty
       (gas_shadow_expr (Builtin (BaseT (BytesT (Fixed 4))) MethodId [Literal la l])) shadow_sa =
     (StackValue (BaseT (BytesT (Fixed 4))) (Lit w),shadow_sa)` by
    (qpat_x_assum `gas_shadow_compiles _ _`
       (qspecl_then [`sa`,`shadow_sa`] mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
     simp[gas_shadow_expr_def, gas_shadow_builtin_def]) >>
  `op = Lit w /\ sb = sa /\ shadow_sb = shadow_sa` by
    (qpat_x_assum `lower_value _ _ _ (gas_shadow_expr _) _ = _` mp_tac >>
     qpat_x_assum `lower_value _ cenv _ _ _ = _` mp_tac >>
     simp[lower_value_def, comp_bind_def, unwrap_value_def, comp_return_def]) >>
  gvs[] >> irule gas_outcome_full_mods_pure >> simp[] >>
  qexistsl_tac [`G0`, `es`, `INL v`, `s0`, `tn0`] >>
  simp[bind_def, read_result_def, return_def, gas_origin_ptr_path_rules, expr_type_def] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  drule_all_then strip_assume_tac fixed_method_id_frame >>
  simp[expr_post_mods_def, expr_post_def, expr_store_bound_def,
       expr_val_at_def, expr_type_def, ptr_val_ok_def, op_taint_def,
       locals_kept_def, ghost_kept_at_def, is_word_type_def] >>
  gvs[expr_val_rel_def, is_word_type_def, evaluate_type_def, eval_operand_def, Abbr `w`]
QED

Theorem method_id_fixed_literal_sim_mods:
  (!DF lo d ctx sh PG f sf cenv cx ty e es.
     is_word_type (post_value_type cenv e) /\
     expr_sim_full_mods (DF,lo,d,ctx,sh,PG,f,sf) cenv cx ty e es /\
     (!sa. ?a op sb. compile_expr cenv ty e sa = (StackValue a op,sb)) /\
     (!s tv t. eval_expr cx e s = (INL tv,t) ==> ?v. tv = Value v) ==>
     expr_vv_sim_full_mods (DF,lo,d,ctx,sh,PG,f,sf) cenv cx ty e es) ==>
  !DF lo d ctx shadow_ctx PG func shadow_func cenv cx ty la l bs es.
    method_id_literal (Literal la l) = SOME bs ==>
    expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty
      (Builtin (BaseT (BytesT (Fixed 4))) MethodId [Literal la l]) es /\
    expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty
      (Builtin (BaseT (BytesT (Fixed 4))) MethodId [Literal la l]) es
Proof
  disch_tac >> rpt gen_tac >> strip_tac >> conj_asm1_tac
  >- (irule fixed_method_id_value >> qexists_tac `bs` >> simp[]) >>
  qpat_x_assum `!DF lo d ctx sh PG f sf cenv cx ty e es. _ ==> _` irule >>
  drule fixed_method_id_compile >> drule fixed_method_id_eval >>
  simp[expr_type_def, is_word_type_def]
QED

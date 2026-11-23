Theory bodyWordLiteralMods
Ancestors
  bodyFullPredsMods bodyFullPostsMods bodyFullShadowBodyInv exprBodyPreProps
  exprSimLiteralWord exprSimProps exprSimMemDefs exprLoweringProps loweringPosts
  exprLowering gasShadow gasShadowCompileStmtHelpers gasShadowState
  gasOutcomeFullMods gasOutcomeFull gasSummary gasStorage fragGasOriginPtr bodyPtrDefs ptrDiscipline
  vyperStorageFootprint vyperTyping vyperTypeSystem vyperValue vyperValueOperation
  vyperInterpreter vyperAST vyperContext vyperState valueEncoding compileEnv
  venomState loweringSlice loweringStateRelDefs bodyInvSplit

(* A typed word literal has one encoding, independent of either compile env. *)
Theorem word_literal_encoding[local]:
  well_typed_expr env (Literal ann l) /\ is_word_type ann ==>
  ?w. (!cenv ty sa. compile_expr cenv ty (Literal ann l) sa =
                     (StackValue ann (Lit w),sa)) /\
      (!cx s. expr_val_rel cx ann (evaluate_literal l) (Lit w) s)
Proof
  strip_tac >> fs[well_typed_expr_def] >>
  Cases_on `?bs. l = HexBytesL bs`
  >- (gvs[] >> drule well_typed_literal_hex_bytes >> strip_tac >> gvs[is_word_type_def]) >>
  Cases_on `ann` >> gvs[well_typed_literal_def, is_word_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  Cases_on `l` >> gvs[well_typed_literal_def, is_word_type_def] >>
  all_tac >~ [`BytesT bd`] >- (
    Cases_on `bd` >> gvs[is_word_type_def] >>
    simp[compile_expr_def, compile_literal_vv_def, comp_return_def,
         expr_type_def, expr_val_rel_def, eval_operand_def, evaluate_literal_def, is_word_type_def,
         vyperValueTheory.evaluate_type_def]) >>
  all_tac >~ [`BoolL b`] >- (
    Cases_on `b` >>
    simp[compile_expr_def, compile_literal_vv_def, comp_return_def,
         expr_type_def, expr_val_rel_def, eval_operand_def, evaluate_literal_def, is_word_type_def,
         vyperValueTheory.evaluate_type_def, typed_val_to_w256_word_value,
         word_value_def, val_to_w256_def]) >>
  simp[compile_expr_def, compile_literal_vv_def, comp_return_def,
       expr_type_def, expr_val_rel_def, eval_operand_def, evaluate_literal_def, is_word_type_def,
       vyperValueTheory.evaluate_type_def, typed_val_to_w256_word_value,
       word_value_def, val_to_w256_def]
QED

(* Transport the result to the shadow compiler.  The literal equation
   additionally identifies its exact landing, not just related states. *)
Theorem word_literal_shadow_compile[local]:
  (!ce ty s. compile_expr ce ty (Literal ann l) s =
              (StackValue ann (Lit w),s)) /\ gas_shadow_state sa shadow_sa ==>
  compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr (Literal ann l))
    shadow_sa = (StackValue ann (Lit w),shadow_sa)
Proof
  strip_tac >>
  `gas_shadow_compiles (compile_expr cenv ty (Literal ann l))
     (compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr (Literal ann l)))`
    by irule gas_shadow_stmt_compile_expr_env >>
  qpat_x_assum `gas_shadow_compiles _ _`
    (assume_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
  first_x_assum drule >> simp[] >>
  strip_tac >> qmatch_goalsub_abbrev_tac `FST v` >>
  `SND v = shadow_sa` by
    (qpat_x_assum `StackValue _ _ = FST v` kall_tac >>
     simp[Abbr `v`, gas_shadow_expr_def]) >>
  Cases_on `v` >> gvs[]
QED

val word_literal_shadow_tac =
  `compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr (Literal ann l))
      shadow_sa = (StackValue ann (Lit w),shadow_sa)` by
    (irule word_literal_shadow_compile >> simp[] >> qexists_tac `sa` >> simp[]);

(* The empty path keeps the physical and ghost states on the same landing. *)
Theorem word_literal_pure_outcome[local]:
  ~s.vs_halted /\
  (!tail. source (es with gas_obs := tail) = (res, es with gas_obs := tail)) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
       Q H res (es with gas_obs := []) G tn s) ==>
  gas_outcome_full_mods (DF, lo, explicit, ctx, func, PG) mods cx st0
    source (es, s, G, tn) Q R
Proof
  strip_tac >> PURE_REWRITE_TAC[gas_outcome_full_mods_def] >> qexists_tac `[]` >>
  reverse (Cases_on `storage_trace_domain cx st0 es.storage_trace`)
  >- (disj1_tac >>
      conj_tac >- simp[gas_bad_storage_at_def, gas_explicit_def] >>
      qexistsl_tac [`ARB`, `func`, `PG`, `G`, `tn`, `s`] >>
      simp[gas_origin_ptr_focus_nil]) >>
  disj2_tac >> disj1_tac >>
  qexistsl_tac [`res`, `es`, `OK s`, `G`, `tn`] >>
  simp[gas_explicit_def, gas_origin_ptr_path_rules]
QED

Theorem word_literal_frame_gas_obs[local]:
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
  >- (qpat_assum `immutable_frame_mods _ _ _ es _`
        (fn th => POP_ASSUM_LIST (K ALL_TAC) >> mp_tac th) >>
      simp[immutable_frame_mods_def, immutables_rel_mods_def,
           immutable_alloca_sep_mods_def, immutable_alloca_sep_def,
           loweringStateRelDefsTheory.immutables_rel_def] >>
      metis_tac[]) >>
  conj_tac
  >- (`storage_well_formed_on cx (es with gas_obs := []) (FST H) <=>
       storage_well_formed_on cx es (FST H)` suffices_by simp[] >>
      irule storage_well_formed_on_backends >> simp[]) >>
  qpat_assum `ghost_inv_at_mods _ _ _ _ _ es _ _ _`
    (fn th => POP_ASSUM_LIST (K ALL_TAC) >> mp_tac th) >>
  PURE_ONCE_REWRITE_TAC[ghost_inv_at_mods_def] >>
  PURE_REWRITE_TAC[evaluation_state_accfupds] >> simp[]
QED

Theorem word_literal_value_mods[local]:
  well_typed_expr env (Literal ann l) /\ is_word_type ann ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Literal ann l) es
Proof
  strip_tac >> drule_all_then strip_assume_tac word_literal_encoding >>
  rw[expr_sim_full_mods_def] >>
  word_literal_shadow_tac >>
  `op = Lit w /\ sb = sa /\ shadow_sb = shadow_sa` by
    (qpat_x_assum `lower_value _ _ _ (gas_shadow_expr _) _ = _` mp_tac >>
     qpat_x_assum `lower_value _ cenv _ _ _ = _` mp_tac >>
     simp[lower_value_def, comp_bind_def, unwrap_value_def, comp_return_def]) >>
  gvs[] >>
  irule word_literal_pure_outcome >> simp[expr_type_def] >>
  qexists_tac `INL (evaluate_literal l)` >> simp[literal_read_all_tails] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  drule_all_then strip_assume_tac word_literal_frame_gas_obs >>
  simp[expr_post_mods_def, expr_post_def, expr_store_bound_def,
       expr_val_at_def, expr_type_def, ptr_val_ok_def, op_taint_def,
       locals_kept_def, ghost_kept_at_def]
QED

Theorem word_literal_vv_mods[local]:
  well_typed_expr env (Literal ann l) /\ is_word_type ann ==>
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Literal ann l) es
Proof
  strip_tac >> drule_all_then strip_assume_tac word_literal_encoding >>
  rw[expr_vv_sim_full_mods_def] >>
  word_literal_shadow_tac >>
  gvs[] >>
  irule word_literal_pure_outcome >> simp[expr_type_def, contextTheory.vv_location_def] >>
  qexists_tac `INL (Value (evaluate_literal l))` >>
  simp[Once evaluate_def, return_def] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  drule_all_then strip_assume_tac word_literal_frame_gas_obs >>
  simp[vv_post_mods_def, vv_holds_mods_def, vv_place_ptr_mods_def,
       vv_holds_def, vv_at_def, vv_storage_live_def, vv_place_ptr_def,
       vv_store_bound_def, lowered_value_type_def, contextTheory.vv_location_def,
       read_result_def, return_def, expr_val_at_def, expr_type_def,
       ptr_vv_ok_def, ptr_val_ok_def, op_taint_def, locals_kept_def,
       ghost_kept_at_def]
QED

Theorem word_literal_full_ok_mods:
  !mods exps cx ann l. is_word_type ann ==>
    body_expr_full_ok_mods mods exps cx (Literal ann l)
Proof
  simp[Once body_expr_full_ok_mods_def] >> rpt strip_tac >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  (irule word_literal_value_mods ORELSE irule word_literal_vv_mods) >>
  simp[] >> qexists_tac `env` >> simp[]
QED

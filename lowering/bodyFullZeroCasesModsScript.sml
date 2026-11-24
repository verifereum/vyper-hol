Theory bodyFullZeroCasesMods
Ancestors
  bodyFullPredsMods bodyFullPostsMods bodyFullShadowBodyInv bodyInvSplit
  bodyFullShared bodySim loweringPosts stmtSimDefs
  gasOutcomeFullMods gasOutcomeFull gasSummary gasStorage gasContext
  fragGasOriginPtr vyperStorageFootprint exprLoweringProps
  vyperInterpreter vyperState stmtLowering compileEnv gasShadow
  loweringStateRelDefs

(* Empty fragments keep the whole unit's immutable frame and pointer ghosts. *)
Theorem stmt_frag_nil_full_mods[local]:
  !DF lo d ctx shadow_ctx PG func shadow_func cx lctx RetQ cenv ty es.
    stmt_frag_full_mods (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmts_env cenv lctx ty []) (stmts_env (gas_shadow_env T cenv) lctx ty [])
      (eval_stmts cx []) es
Proof
  rw[stmt_frag_full_mods_def, stmts_env_def, comp_return_def] >>
  `!tail. eval_stmts cx [] (es with gas_obs := tail) =
          (INL (), es with gas_obs := tail)` by
    simp[Once evaluate_def, return_def] >>
  PURE_REWRITE_TAC[gas_outcome_full_mods_def] >> qexists_tac `[]` >>
  reverse (Cases_on `storage_trace_domain cx st0 es.storage_trace`)
  >- (disj1_tac >>
      conj_tac >- simp[gas_bad_storage_at_def, gas_explicit_def] >>
      qexistsl_tac [`ARB`, `func`, `PG`, `G0`, `tn0`, `s0`] >>
      simp[gas_origin_ptr_focus_nil]) >>
  disj2_tac >> disj1_tac >>
  qexistsl_tac [`INL ()`, `es`, `OK s0`, `G0`, `tn0`] >>
  conj_tac >- simp[gas_explicit_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >> first_x_assum drule >> strip_tac >>
  conj_tac >- simp[gas_origin_ptr_path_rules] >>
  disj1_tac >> qexists_tac `s0` >> simp[] >>
  `stmt_state_rel H ctx func cenv cx (es with gas_obs := []) s0` by
    (drule msg_gas_state_frame >>
     disch_then (qspecl_then [`s0.vs_gas_readings`, `s0.vs_inst_idx`, `[]`]
       mp_tac) >> simp[stmt_state_rel_inst_idx]) >>
  `storage_well_formed_on cx (es with gas_obs := []) (FST H) <=>
   storage_well_formed_on cx es (FST H)` by
    (irule storage_well_formed_on_backends >> simp[]) >>
  `return_buf_sep d cenv (es with gas_obs := []) s0` by
    simp[return_buf_sep_gas_obs] >>
  `immutable_frame_mods func cenv cx (es with gas_obs := []) s0` by
    (qpat_assum `immutable_frame_mods _ _ _ es _`
       (fn th => POP_ASSUM_LIST (K ALL_TAC) >> mp_tac th) >>
     simp[immutable_frame_mods_def, immutables_rel_mods_def,
          immutable_alloca_sep_mods_def, immutable_alloca_sep_def,
          loweringStateRelDefsTheory.immutables_rel_def] >>
     metis_tac[]) >>
  `ghost_inv_at_mods (DF H) lo d cenv cx (es with gas_obs := []) G0 tn0 s0` by
    (qpat_assum `ghost_inv_at_mods _ _ _ _ _ es _ _ _`
       (fn th => POP_ASSUM_LIST (K ALL_TAC) >> mp_tac th) >>
     PURE_ONCE_REWRITE_TAC[ghost_inv_at_mods_def] >>
     PURE_REWRITE_TAC[evaluation_state_accfupds] >> simp[]) >>
  simp[stmt_lands_def, cenv_top_ext_def, compile_env_component_equality,
       alloca_frame_same]
QED

Theorem body_stmts_nil_case_full_mods:
  !mods exps cx. body_stmts_full_ok_mods mods exps cx []
Proof
  simp[body_stmts_full_ok_mods_def, stmt_frag_nil_full_mods]
QED

Theorem body_pass_case_full_mods:
  !mods exps cx. body_stmt_full_ok_mods mods exps cx Pass
Proof
  rpt gen_tac >>
  `eval_stmt cx Pass = eval_stmts cx []` by
    simp[FUN_EQ_THM, evaluate_def, return_def] >>
  `!ce lctx ty. stmt_env ce lctx ty Pass = stmts_env ce lctx ty []` by
    simp[FUN_EQ_THM, stmt_env_def, stmts_env_def, declare_stmt_local_def,
         comp_bind_def, comp_ignore_bind_def, compile_stmt_def, comp_return_def] >>
  simp[body_stmt_full_ok_mods_def, gas_shadow_stmt_def, stmt_frag_nil_full_mods]
QED

Theorem body_return_none_case_full_mods:
  !mods exps cx. body_stmt_full_ok_mods mods exps cx (Return NONE)
Proof
  rw[body_stmt_full_ok_mods_def, frame_ret_ok_full_mods_def, gas_shadow_stmt_def] >>
  first_x_assum (qspecl_then [`cenv`, `env`, `lctx`, `NONE`, `es`] mp_tac) >>
  simp[same_frame_refl]
QED

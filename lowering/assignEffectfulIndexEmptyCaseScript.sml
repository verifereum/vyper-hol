Theory assignEffectfulIndexEmptyCase
Ancestors
  assignEffectfulIndexEmpty assignPlaceEmptyCompose assignPlacePureCode
  assignPlaceEmptySource assignPlaceGasCompose assignPlaceEndpoint
  targetPlaceSimCases targetPlaceSim stmtSimDefs exprSimHyps exprSimHypsDefs
  stmtLoweringMono exprLoweringProps loweringPosts compileEnv exprLowering
  immutableAssignEmpty bodySimAugPlaceLoad vyperStoragePlaceProvenance memoryLocalRhsProps
  stmtSimAugAssign stmtSimAugAssignPlaceMemory vyperTypeDefaults
  tuplePlaceWriteOutcome vyperTypeCallStackSoundness vyperTypeInvariants
  vyperTypeSystem vyperState loweringStateRelDefs fragExec
Libs monadsyntax

Theorem assign_place_effectful_empty_case:
  !ctx func cx lctx RetQ cenv ty env tops bt e es dty.
    has_length_word (expr_type e) /\ is_empty_value_expr e /\
    ~supported_target_pure tops bt /\
    type_place_target env bt = SOME (Type dty) /\
    type_widens_to env.type_defs (expr_type e) dty /\
    assignable_type env.type_defs (expr_type e) /\
    ((?s pv s1 sread v s2. eval_expr cx e s = (INL pv,s1) /\
                           read_result cx pv sread = (INL v,s2)) ==>
     target_case F ctx func cenv cx bt) /\
    ~immutable_root cx bt /\ assign_alloc_ok cenv bt e /\
    target_indices_pre cenv cx env bt /\
    expr_vv_sim ctx func cenv cx (expr_type e) e es /\
    expr_body_pre cenv cx env e es /\ cenv.ce_target CapMcopy /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    body_inv tops ctx cenv cx /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget bt) e)) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Assign (BaseTarget bt) e))
      (eval_stmt cx (Assign (BaseTarget bt) e)) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `?stv. evaluate_type (get_tenv cx) (expr_type e) = SOME stv` by
    (drule expr_body_pre_type_evaluates >>
     simp[optionTheory.IS_SOME_EXISTS]) >>
  `?dtv. evaluate_type (get_tenv cx) dty = SOME dtv` by
    (fs[type_widens_to_def, well_formed_type_def] >>
     metis_tac[optionTheory.IS_SOME_EXISTS]) >>
  `call_evaluation_safe cx (int_calls_target bt)` by
    (qpat_assum `call_evaluation_safe _ (int_calls_stmt _)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[vyperTypeCallGraphTheory.int_calls_stmt_def,
          vyperTypeCallGraphTheory.int_calls_atarget_def] >>
     metis_tac[call_evaluation_safe_append_left, call_evaluation_safe_append_right]) >>
  `target_case F ctx func cenv cx bt` by
    (drule_all immutable_assign_empty_read >>
     disch_then (qspec_then `es.gas_obs` mp_tac) >>
     simp[bind_def, AllCaseEqs()] >> metis_tac[]) >>
  `target_sim ctx func cenv cx env bt es` by
    metis_tac[target_case_def, target_pre_def] >>
  simp[stmt_frag_def, stmt_framed_frag_def] >> rpt gen_tac >> strip_tac >>
  drule_all assign_place_pure_empty_code >> strip_tac >> gvs[] >>
  `ci_mono sa st` by
    metis_tac[ci_mono_compile_get_target_ptr, pairTheory.SND] >>
  `ci_mono st sb` by
    metis_tac[ci_mono_stmt_helpers, pairTheory.SND] >>
  `fn_has_code sa st func /\ fn_has_code st sb func` by
    metis_tac[ci_mono_def, fn_has_code_split] >>
  `gas_admissible (eval_target_place cx bt) target_place_res_ok es` by
    metis_tac[assign_place_empty_target_admissible] >>
  irule assign_place_empty_prefix_outcome >>
  simp[] >> qexistsl_tac [`cenv`, `dtv`, `dty`, `env`] >> simp[] >>
  irule assign_place_target_outcome >>
  qexistsl_tac [`\res ee t. ?p. res = INL p /\
    target_post ctx func cenv cx (es with gas_obs := []) sa st s0 ee
      (PlaceR p) (Type dty) tr t /\
    t.vs_current_bb = st.cs_current_bb /\
    t.vs_inst_idx = LENGTH st.cs_current_insts`,
    `\res ee r. expr_exit res r`] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> gvs[] >>
      `eval_target_place cx bt
         (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
         (INL p, mid with gas_obs := [])` by
        (drule gas_marked_exec_observation >>
         disch_then (qspec_then `[]` mp_tac) >> simp[]) >>
      `expr_sim_inv cenv cx env (mid with gas_obs := [])` by
        (irule aug_place_target_inv >>
         goal_assum (drule_at (Pat `eval_target_place _ _ _ = _`)) >>
         simp[expr_sim_inv_def]) >>
      `storage_place_region cx p` by metis_tac[eval_target_place_region] >>
      `has_length_word dty` by metis_tac[type_widens_to_has_length_word] >>
      `local_ptrs_reserved cenv st` by
        (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> fs[ci_mono_def]) >>
      `alloca_frame cenv (es with gas_obs := []) sa s0
         cenv (mid with gas_obs := []) t` by
        (drule target_post_alloca_frame >> disch_then irule >>
         fs[target_post_def, locals_kept_def]) >>
      `alloca_frame cenv es sa s0 cenv (mid with gas_obs := []) t` by
        (gvs[alloca_frame_def, local_region_def] >> first_assum ACCEPT_TAC) >>
      `?dst loc. tr = (dst,SOME loc,SOME (ValPT dty)) /\
          loc <> LocCode /\ loc <> LocCalldata` by
        (qpat_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[target_post_def] >> strip_tac >> Cases_on `p` >>
         gvs[place_ptr_rel_def, slot_loc_def] >> Cases_on `b` >> gvs[] >>
         PairCases_on `tr` >> gvs[value_type_place_def]) >>
      rpt BasicProvers.VAR_EQ_TAC >>
      `stmt_state_rel ctx func cenv cx (mid with gas_obs := []) t` by
        gvs[target_post_def] >>
      `?wr ff. write_place cx p (default_value dtv)
          (mid with gas_obs := []) = (wr,ff)` by
        metis_tac[pairTheory.PAIR] >>
      `wr = INL ()` by
        (irule tuple_place_source_write_success >>
         qpat_assum `write_place _ _ _ _ = _` (irule_at Any) >>
         qpat_assum `eval_target_place _ _ _ = _` (irule_at Any) >>
         qpat_assum `stmt_state_rel _ _ _ _ (_ with gas_obs := []) t`
           (irule_at Any) >>
         qexistsl_tac [`dty`, `dtv`, `env`] >>
         simp[target_pre_def, well_typed_target_def] >>
         metis_tac[expr_sim_inv_gas_obs, default_value_has_type_thm]) >>
      rpt BasicProvers.VAR_EQ_TAC >>
      `~t.vs_halted` by
        (irule aug_place_marked_path_not_halted >>
         fs[gasSummaryTheory.gas_marked_exec_def] >> metis_tac[]) >>
      `!id path entry t0.
         p = MemoryPlace id path /\ lookup_scopes id mid.scopes = SOME entry /\
         cenv.ce_var_type id = SOME t0 ==>
         evaluate_type (get_tenv cx) t0 = SOME entry.type` by
        (qpat_assum `expr_sim_inv _ _ _ (_ with gas_obs := [])` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> simp[] >>
         metis_tac[aug_place_store_entry_types]) >>
      `~block_is_terminated st` by
        (irule endpoint_path_open >>
         qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _`
           (assume_tac o CONJUNCT2 o REWRITE_RULE [gasSummaryTheory.gas_marked_exec_def]) >>
         goal_assum (drule_at (Pat `gas_marked_path _ _ _ s0 _ (OK t)`)) >>
         qexists_tac `sa` >> simp[] >> fs[ci_mono_def]) >>
      `target_post ctx func cenv cx es sa st s0 (mid with gas_obs := [])
         (PlaceR p) (Type dty) (dst,SOME loc,SOME (ValPT dty)) t` by
        (qpat_assum `target_post _ _ _ _ (_ with gas_obs := []) _ _ _ _ _ _ _ _`
           mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[target_post_def, locals_kept_def, popped_kept_def] >>
         strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
      pop_assum (mp_then (Pat `target_post _ _ _ _ _ _ _ _ _ _ _ _ _`) mp_tac
        (SIMP_RULE (srw_ss())
          [stmtSimDeclComposeTheory.stmt_post_end_gas_obs, SF ETA_ss]
          assign_effectful_empty_target_store)) >>
      disch_then (drule_at (Pat `write_place _ _ _ _ = _`)) >>
      disch_then (drule_at (Pat `expr_sim_inv _ _ _ _`)) >>
      disch_then irule >> fs[] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      Cases_on `res` >> fs[exprSimDefsTheory.expr_exit_INL, stmt_exit_def] >>
      metis_tac[stmtSimPropsTheory.expr_exit_INR_type]) >>
  irule target_place_sim >> simp[] >>
  qexists_tac `env` >> simp[] >>
  fs[target_case_def] >> first_x_assum irule >>
  simp[target_pre_def, expr_sim_inv_def]
QED

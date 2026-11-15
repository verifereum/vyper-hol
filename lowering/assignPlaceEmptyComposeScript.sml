Theory assignPlaceEmptyCompose
Ancestors
  loweringStateRelDefs
  assignPlaceEmpty assignPlacePureCode assignPlaceGasCompose placeStore
  targetPlaceSimCases stmtSimDefs gasContext vyperExprNoControl vyperState
  assignPlaceEmptySource assignPlaceEmptyStore assignPlaceTargetLive exprSimHyps stmtLoweringMono
  memoryLocalRhsProps vyperTypeArgFits exprSimHypsDefs vyperTypeInvariants
  bodySimAugPlaceLoad vyperStoragePlaceProvenance stmtSimAugAssign
  vyperTypeDefaults vyperStorageFrame stmtSimAugAssignPlaceMemory
  loweringPosts compileEnv valueEncoding exprLowering
  vyperTypeSystem option immutableAssignEmpty targetPlaceSim exprLoweringProps fragExec
Libs monadsyntax

Theorem assign_place_empty_target_admissible:
  expr_body_pre cenv cx env e es /\ is_empty_value_expr e /\
  has_length_word (expr_type e) /\
  type_widens_to env.type_defs (expr_type e) dty /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  gas_admissible (eval_stmt cx (Assign (BaseTarget bt) e))
    (stmt_res_ok lctx) es ==>
  gas_admissible (eval_target_place cx bt) target_place_res_ok es
Proof
  strip_tac >> drule_all assign_place_empty_source_action >> strip_tac >>
  rw[gas_admissible_def] >>
  Cases_on `res` >- simp[target_place_res_ok_def] >>
  rename1 `INR ex` >>
  `no_control_exc ex` by metis_tac[eval_target_place_no_control] >>
  `stmt_res_ok lctx (INR ex)` by
    (drule gas_admissible_result >> disch_then irule >>
     qexistsl_tac [`ee`, `gs`] >> simp[bind_def]) >>
  gvs[stmt_res_ok_def, target_place_res_ok_def, no_control_exc_def]
QED


Theorem assign_place_empty_stmt_frag:
  !ctx func cx lctx RetQ cenv ty env bt e es dty.
    ~expr_can_mutate cenv (target_to_expr bt) /\
    type_place_target env bt = SOME (Type dty) /\
    type_widens_to env.type_defs (expr_type e) dty /\
    assignable_type env.type_defs (expr_type e) /\
    (lowered_value_type cenv e = expr_type e \/
     is_bytestring_type (expr_type e) /\
     is_bytestring_type (lowered_value_type cenv e) /\
     arg_type_fits (lowered_value_type cenv e) (expr_type e)) /\
    ((?s pv s1 sread v s2. eval_expr cx e s = (INL pv,s1) /\
                           read_result cx pv sread = (INL v,s2)) ==>
     target_case F ctx func cenv cx bt) /\
    ~immutable_root cx bt /\ assign_alloc_ok cenv bt e /\
    target_indices_pre cenv cx env bt /\
    expr_vv_sim ctx func cenv cx (expr_type e) e es /\
    expr_body_pre cenv cx env e es /\ cenv.ce_target CapMcopy /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    ~expr_has_effect e /\ has_length_word (expr_type e) /\ is_empty_value_expr e ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Assign (BaseTarget bt) e))
      (eval_stmt cx (Assign (BaseTarget bt) e)) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `lowered_value_type _ _ = _ \/ _` kall_tac >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `?stv. evaluate_type (get_tenv cx) (expr_type e) = SOME stv` by
    (drule expr_body_pre_type_evaluates >>
     simp[IS_SOME_EXISTS]) >>
  `?dtv. evaluate_type (get_tenv cx) dty = SOME dtv` by
    (fs[type_widens_to_def, well_formed_type_def] >> metis_tac[IS_SOME_EXISTS]) >>
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
      `alloca_frame cenv (es with gas_obs := []) sa s0 cenv (mid with gas_obs := []) t` by
        (drule target_post_alloca_frame >> disch_then irule >>
         fs[target_post_def, locals_kept_def]) >>
      `alloca_frame cenv es sa s0 cenv (mid with gas_obs := []) t` by
        (gvs[alloca_frame_def, local_region_def] >> first_assum ACCEPT_TAC) >>
      `?dst loc. tr = (dst,SOME loc,SOME (ValPT dty)) /\
          loc <> LocCode /\ loc <> LocCalldata` by
        (fs[target_post_def] >> Cases_on `p` >>
         gvs[place_ptr_rel_def, slot_loc_def] >> Cases_on `b` >> gvs[] >>
         PairCases_on `tr` >> gvs[value_type_place_def]) >>
      gvs[] >>
      `?wr ff. write_place cx p (default_value dtv) (mid with gas_obs := []) = (wr,ff)` by
        metis_tac[pairTheory.PAIR] >>
      `stmt_res_ok lctx wr` by
        (`eval_stmt cx (Assign (BaseTarget bt) e)
            (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (wr,ff)` by
           (drule assign_place_empty_source_action >>
            disch_then (qspecl_then [`dty`, `dtv`] mp_tac) >>
            simp[] >> disch_then (qspec_then `bt` mp_tac) >>
            disch_then (qspec_then `gas_explicit marks s0.vs_gas_readings` mp_tac) >>
            simp[bind_def]) >>
         metis_tac[gas_admissible_result]) >>
      `wr = INL ()` by
        (Cases_on `p`
         >- (fs[target_post_def, place_ptr_rel_def] >>
             `~cx.txn.is_static` by fs[stmt_state_rel_def, state_rel_def] >>
             `value_has_type dtv (default_value dtv)` by
               metis_tac[default_value_has_type_thm] >>
             gvs[write_place_def] >>
             metis_tac[write_storage_slot_succeeds, pairTheory.FST])
         >- (drule_all assign_place_pure_memory_write_success >> simp[]) >>
         fs[target_post_def, place_ptr_rel_def]) >>
      gvs[] >>
      `~t.vs_halted` by
        (irule aug_place_marked_path_not_halted >>
         fs[gasSummaryTheory.gas_marked_exec_def] >> metis_tac[]) >>
      `!id path entry t0.
         p = MemoryPlace id path /\ lookup_scopes id mid.scopes = SOME entry /\
         cenv.ce_var_type id = SOME t0 ==>
         evaluate_type (get_tenv cx) t0 = SOME entry.type` by
        (metis_tac[aug_place_store_entry_types]) >>
      `?u. gas_marked_path F ctx func t 0 (OK u) /\
           stmt_state_rel ctx func cenv cx ff u /\
           (!x. not_fresh_at st x ==> lookup_var x u = lookup_var x t) /\
           (!aid b. FLOOKUP t.vs_allocas aid = SOME b ==>
                    FLOOKUP u.vs_allocas aid = SOME b) /\
           ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
           u.vs_inst_idx = LENGTH sb.cs_current_insts /\
           alloca_frame cenv es sa s0 cenv ff u` by
        (irule assign_place_empty_store_framed >>
         qpat_assum `compile_store_at_loc _ _ _ _ _ = _` (irule_at Any) >>
         qpat_assum `write_place _ _ _ _ = _` (irule_at Any) >>
         fs[target_post_def] >>
         qexistsl_tac [`env`, `dty`] >> simp[]) >>
      `!tail. write_place cx p (default_value dtv) (mid with gas_obs := tail) =
          (INL (), ff with gas_obs := tail)` by
        (Cases_on `p`
         >- (qpat_x_assum `write_place _ _ _ _ = _` mp_tac >>
             simp[write_place_def,
               stmtSimAssignStorageTheory.write_storage_slot_gas_obs,
               AllCaseEqs()] >> rpt strip_tac >> gvs[])
         >- (drule aug_place_memory_write_gas_obs >> simp[]) >>
         fs[target_post_def, place_ptr_rel_def]) >>
      `stmt_post ctx func cx lctx cenv cenv sa sb es s0
          (INL ()) (ff with gas_obs := []) u` by
        (irule aug_place_normal_post >> simp[] >>
         conj_tac
         >- (fs[target_post_def] >>
             metis_tac[exprOperandVarTheory.compiler_ci_mono_not_fresh]) >>
         conj_tac
         >- (fs[target_post_def] >> metis_tac[]) >>
         Cases_on `loc` >>
         gvs[stmtLoweringTheory.compile_store_at_loc_def] >>
         irule stmtSimDeclMemTheory.emit_void_nonterminator_open >>
         goal_assum (drule_at Any) >>
         simp[venomInstTheory.is_terminator_def]) >>
      simp[gasOutcomeTheory.gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
      simp[gasSummaryTheory.gas_summary_at_def, gasSummaryTheory.gas_marked_exec_def] >>
      qexistsl_tac [`INL ()`, `ff`, `OK u`] >> simp[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      Cases_on `res` >> fs[exprSimDefsTheory.expr_exit_INL, stmt_exit_def] >>
      metis_tac[stmtSimPropsTheory.expr_exit_INR_type]) >>
  irule target_place_sim >>
  simp[] >>
  qexists_tac `env` >> simp[] >>
  fs[target_case_def] >>
  first_x_assum irule >>
  simp[target_pre_def, expr_sim_inv_def]
QED

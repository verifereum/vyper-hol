(* Non-mutating targets with aggregate physical RHS widening. *)
Theory assignEffectfulIndexNonmutating
Ancestors
  placeRelayoutSemantic placeRelayoutFrag placeRelayoutGasCompose
  placeRelayoutCode placeRelayoutRawSource placeRelayoutGasSource
  placeRelayoutBounds placeRelayoutOpen assignPlaceEndpoint
  immutableDeployPhysicalSource exprSimAggregateBodySource exprSimSource typedMemoryCopy
  exprSimDefs exprSimHypsDefs exprSimHyps loweringPosts stmtSimDefs compileEnv
  targetPlaceSimCases gasSummary gasSummaryCompose exprSimSubscriptMap
  supportedExprs supportedTargets bodySim
Libs monadsyntax

Theorem assign_place_nonmutating_widened_case:
  !ctx func cx lctx RetQ cenv ty env tops bt e es dty.
    ~supported_target_pure tops bt /\
    type_place_target env bt = SOME (Type dty) /\
    type_widens_to env.type_defs (expr_type e) dty /\
    assignable_type env.type_defs (expr_type e) /\
    ((?s pv s1 sread v s2. eval_expr cx e s = (INL pv,s1) /\
                           read_result cx pv sread = (INL v,s2)) ==>
     target_case F ctx func cenv cx bt) /\
    ~immutable_root cx bt /\
    assign_alloc_ok cenv bt e /\
    target_indices_pre cenv cx env bt /\
    expr_vv_sim ctx func cenv cx (expr_type e) e es /\
    expr_body_pre cenv cx env e es /\ cenv.ce_target CapMcopy /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    body_inv tops ctx cenv cx /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget bt) e)) /\
    ~expr_can_mutate cenv (target_to_expr bt) /\
    ~(lowered_value_type cenv e = expr_type e \/
      is_bytestring_type (expr_type e) /\
      is_bytestring_type (lowered_value_type cenv e) /\
      arg_type_fits (lowered_value_type cenv e) (expr_type e)) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Assign (BaseTarget bt) e))
      (eval_stmt cx (Assign (BaseTarget bt) e)) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def, vyperTypeInvariantsTheory.env_consistent_def,
       vyperTypeInvariantsTheory.env_context_consistent_def] >>
  `~is_word_type dty` by metis_tac[strict_widened_assignment_nonword] >>
  drule_all assignRelayoutCallerTheory.assign_relayout_source_classify >> strip_tac >>
  `~(has_length_word (expr_type e) /\ is_empty_value_expr e)` by
    (Cases_on `e` >>
     gvs[stmtLoweringTheory.is_empty_value_expr_def,
       oneline exprLoweringTheory.lowered_value_type_def, vyperASTTheory.expr_type_def]) >>
  `post_value_type cenv e <> expr_type e /\
   ~is_word_type (post_value_type cenv e)` by fs[] >>
  rewrite_tac[stmt_frag_def, stmt_framed_frag_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all assign_place_relayout_code_parts >> strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  `gas_outcome F (cx_tops cx) (ctx,func) (eval_expr cx e) (es,s0)
    (\res ee t. ?v. res = INL (Value v) /\
      vv_post ctx func cenv cx e es sa sv s0 ee (Value v) vv t /\
      t.vs_current_bb = sv.cs_current_bb /\
      t.vs_inst_idx = LENGTH sv.cs_current_insts)
    (\res ee r. expr_exit res r)` by
    (`!ss pv ee. eval_expr cx e ss = (INL pv,ee) ==> ?v. pv = Value v` by
       metis_tac[placeRelayoutRawSourceTheory.strict_widened_rhs_delayed_read] >>
     `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
       metis_tac[placeRelayoutGasSourceTheory.assign_place_raw_rhs_admissible] >>
     qpat_x_assum `expr_vv_sim _ _ _ _ _ _ _` mp_tac >>
     rewrite_tac[expr_vv_sim_def] >> disch_then drule_all >> strip_tac >>
     drule gas_outcome_source_invariant >>
     disch_then (qspec_then
       `\res. !pv. res = INL pv ==> ?v. pv = Value v` mp_tac) >>
     (impl_tac >- (rpt strip_tac >> gvs[] >> metis_tac[])) >> strip_tac >>
     irule gas_outcome_conseq >> goal_assum (drule_at Any) >> simp[] >>
     metis_tac[]) >>
  irule assign_place_raw_outcome >>
  goal_assum (drule_at (Pat `gas_outcome _ _ _ _ _ _ _`)) >> simp[] >>

  conj_tac >- (rpt gen_tac >> strip_tac >>
    `?ex. res = INR ex` by
      (qpat_x_assum `expr_exit _ _` mp_tac >>
       Cases_on `res` >> simp[expr_exit_def]) >>
    qexists_tac `ex` >> asm_rewrite_tac[] >> gen_tac >>
    pure_rewrite_tac[stmt_exit_def] >> disj1_tac >>
    qpat_x_assum `res = INR ex` SUBST_ALL_TAC >>
    qpat_x_assum `expr_exit _ _` mp_tac >>
    rpt (pop_assum kall_tac) >>
    simp[stmtSimPropsTheory.expr_exit_INR_type]) >>
  reverse conj_tac >- (rpt strip_tac >> qexists_tac `v` >> asm_rewrite_tac[]) >>
  rpt strip_tac >>
  `!tail. eval_expr cx e
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
    (INL (Value v),mid with gas_obs := tail)` by fs[gas_marked_exec_def] >>
  `expr_sim_inv cenv cx env (mid with gas_obs := [])` by
    (`expr_body_pre cenv cx env e
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
     qpat_x_assum `!tail. eval_expr _ _ _ = _`
       (assume_tac o SIMP_RULE (srw_ss()) [] o Q.SPEC `[]`) >>
     drule_all (cj 1 exprSimSourceTheory.expr_body_pre_eval_result) >> simp[]) >>
  `target_case F ctx func cenv cx bt` by
    (`!ss. read_result cx (Value v) ss = (INL v,ss)` by
       simp[vyperStateTheory.read_result_def, vyperStateTheory.return_def] >>
     qpat_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` mp_tac) >>
     metis_tac[]) >>
  `target_sim ctx func cenv cx env bt (mid with gas_obs := [])` by
    metis_tac[targetPlaceSimTheory.target_case_def,
              targetPlaceSimTheory.target_pre_def] >>
  `local_ptrs_reserved cenv sv /\ local_ptrs_reserved cenv st` by
    (`sa.cs_next_var <= sv.cs_next_var /\ sa.cs_next_var <= st.cs_next_var` by
       fs[exprLoweringPropsTheory.ci_mono_def] >>
     metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var]) >>
  `stmt_state_rel ctx func cenv cx (mid with gas_obs := []) t` by
    metis_tac[vv_post_def] >>
  `~t.vs_halted` by
    (irule stmtSimAugAssignPlaceMemoryTheory.aug_place_marked_path_not_halted >>
     qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> metis_tac[]) >>
  `gas_admissible (eval_target_place cx bt) target_place_res_ok
    (mid with gas_obs := [])` by
    (irule placeRelayoutGasSourceTheory.assign_place_target_admissible >>
     goal_assum (drule_at (Pat `gas_admissible _ _ _`)) >> metis_tac[]) >>
  drule_all target_place_sim >> strip_tac >>
  irule gas_outcome_bind_place >>
  goal_assum (drule_at (Pat `gas_outcome _ _ _ (eval_target_place _ _) _ _ _`)) >>
  simp[] >> reverse conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `?ex. res = INR ex` by
        (qpat_x_assum `expr_exit _ _` mp_tac >>
         Cases_on `res` >> simp[expr_exit_def]) >>
      qexists_tac `ex` >> asm_rewrite_tac[] >> gen_tac >>
      pure_rewrite_tac[stmt_exit_def] >> disj1_tac >>
      qpat_x_assum `res = INR ex` SUBST_ALL_TAC >>
      qpat_x_assum `expr_exit _ _` mp_tac >>
      rpt (pop_assum kall_tac) >>
      simp[stmtSimPropsTheory.expr_exit_INR_type]) >>
  rpt gen_tac >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  qexists_tac `p` >> simp[] >>
  `!tail. eval_target_place cx bt
    (mid with gas_obs := gas_explicit marks' t.vs_gas_readings ++ tail) =
    (INL p,mid' with gas_obs := tail)` by fs[gas_marked_exec_def] >>
  `eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++
     gas_explicit marks' t.vs_gas_readings) =
    (INL (Value v),mid with gas_obs := gas_explicit marks' t.vs_gas_readings)` by
    metis_tac[listTheory.APPEND_NIL] >>
  `eval_target_place cx bt
    (mid with gas_obs := gas_explicit marks' t.vs_gas_readings) =
    (INL p,mid' with gas_obs := [])` by
    (qpat_assum `!tail. eval_target_place _ _ _ = _`
       (assume_tac o SIMP_RULE (srw_ss()) [] o Q.SPEC `[]`) >>
     first_assum ACCEPT_TAC) >>
  `expr_sim_inv cenv cx env (mid' with gas_obs := [])` by
    (irule bodySimAugPlaceLoadTheory.aug_place_target_inv >>
     goal_assum (drule_at (Pat `eval_target_place _ _ _ = _`)) >>
     metis_tac[exprSimHypsDefsTheory.expr_sim_inv_gas_obs]) >>
  `storage_place_region cx p` by
    metis_tac[vyperStoragePlaceProvenanceTheory.eval_target_place_region] >>
  `(do pv <- eval_expr cx e; read_result cx pv od)
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++
        gas_explicit marks' t.vs_gas_readings) =
      (INL v,mid with gas_obs := gas_explicit marks' t.vs_gas_readings)` by
    simp[vyperStateTheory.bind_def, vyperStateTheory.read_result_def,
         vyperStateTheory.return_def] >>
  `expr_body_pre cenv cx env e
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++
        gas_explicit marks' t.vs_gas_readings)` by
    metis_tac[exprSimSourceTheory.expr_body_pre_gas_obs] >>
  `value_has_type stv v /\ val_wf stv v /\
   type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size stv` by
    (drule_all immutableDeployPhysicalSourceTheory.immutable_rhs_physical_typed >>
     metis_tac[optionTheory.SOME_11]) >>
  `?dtv. evaluate_type (get_tenv cx) dty = SOME dtv /\ value_has_type dtv v` by
    metis_tac[vyperTypeArgFitsTheory.type_widens_to_value_has_type] >>
  `val_wf dtv v` by
    metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
  `assignable_type (get_tenv cx) (lowered_value_type cenv e)` by
    (irule (cj 1 arg_type_fits_source_assignable) >>
     reverse conj_tac
     >- simp[vyperTypeSystemTheory.well_formed_type_def,
             optionTheory.IS_SOME_EXISTS] >>
     qexists_tac `expr_type e` >> simp[] >>
     fs[vyperTypeSystemTheory.type_widens_to_def] >> gvs[]) >>
  `type_memory_bytes cenv (lowered_value_type cenv e) < dimword (:256)` by
    (`~is_word_type (expr_type e)` by
       metis_tac[typedMemoryCopyTheory.return_source_word_widens_eq] >>
     drule_all placeRelayoutBoundsTheory.expr_body_pre_relayout_source_bound >>
     simp[]) >>
  `?dst loc. tr = (dst,SOME loc,SOME (ValPT dty))` by
    (qpat_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     PairCases_on `tr` >> Cases_on `p` >>
     simp[target_post_def, place_ptr_rel_def,
       exprLoweringTheory.value_type_place_def] >> metis_tac[]) >>
  pop_assum strip_assume_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  `~t'.vs_halted` by
    (irule stmtSimAugAssignPlaceMemoryTheory.aug_place_marked_path_not_halted >>
     qpat_x_assum `gas_marked_exec _ _ (eval_target_place _ _) _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> metis_tac[]) >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sv x /\ not_fresh_at st x` by
    (rpt strip_tac >>
     drule_all (CONJUNCT1 exprOperandVarTheory.compiler_compile_var) >>
     metis_tac[exprOperandVarTheory.compiler_ci_mono_not_fresh]) >>
  `lower_value compile_expr cenv (expr_type e) e sa = (vv_operand vv,sv)` by
    simp[exprLoweringTheory.lower_value_def, compileEnvTheory.comp_bind_def] >>
  `well_typed_expr env e` by
    (qpat_assum `expr_body_pre _ _ _ _ _`
       (mp_tac o SIMP_RULE (srw_ss()) [expr_body_pre_def]) >> metis_tac[]) >>
  `!id ty. FLOOKUP env.var_types id = SOME ty ==>
     ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)` by
    (qpat_assum `expr_sim_inv _ _ _ es`
       (mp_tac o SIMP_RULE (srw_ss()) [expr_sim_inv_def]) >> metis_tac[]) >>
  `!l. vv_operand vv <> Label l` by
    (drule_all exprReasonOperandTheory.lower_compile_expr_not_label >> simp[]) >>
  Cases_on `write_place cx p v (mid' with gas_obs := [])` >>
  rename1 `write_place cx p v (mid' with gas_obs := []) = (wr,ff)` >>
  `stmt_res_ok lctx wr` by
    (qpat_assum `gas_admissible (eval_stmt _ _) _ _`
       (mp_tac o REWRITE_RULE [gasContextTheory.gas_admissible_def]) >>
     disch_then irule >>
     qexistsl_tac [`ff`, `gas_explicit marks s0.vs_gas_readings ++
       gas_explicit marks' t.vs_gas_readings`] >>
     simp[Once vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       vyperStateTheory.read_result_def, vyperStateTheory.return_def]) >>
  qpat_assum `!dst' loc' dty'. _`
    (assume_tac o SIMP_RULE (srw_ss()) [] o Q.SPECL [`dst`, `loc`, `dty`]) >>
  `gas_marked_path F ctx func s0 (LENGTH marks) (OK t)` by
    fs[gasSummaryTheory.gas_marked_exec_def] >>
  `~block_is_terminated sv` by
    (irule assignPlaceEndpointTheory.endpoint_path_open >>
     goal_assum (drule_at (Pat `gas_marked_path _ _ _ s0 _ (OK t)`)) >>
     qexists_tac `sa` >>
     simp[] >> fs[exprLoweringPropsTheory.ci_mono_def]) >>
  `~block_is_terminated st` by
    metis_tac[compile_get_target_ptr_endpoint_open] >>
  `(loc = LocMemory \/ loc = LocStorage \/ loc = LocTransient)` by
    (qpat_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     Cases_on `p` >> simp[target_post_def, place_ptr_rel_def] >>
     rename1 `PlaceR pp` >> Cases_on `pp` >>
     simp[place_ptr_rel_def, slot_loc_def] >>
     metis_tac[]) >>
  `(vv_location vv = NONE \/ vv_location vv = SOME LocMemory)` by
    (drule_all exprSimIfExpWidenedCountedTheory.compile_changed_physical_unwrap_shape >>
     strip_tac >> gvs[contextTheory.vv_location_def]) >>
  `~block_is_terminated sb` by
    (qpat_assum `~is_word_type dty` (fn th =>
       qpat_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _`
         (mp_tac o REWRITE_RULE [th])) >>
     disch_then (mp_then Any mp_tac compile_assign_place_endpoint_open) >>
     simp[]) >>
  irule widened_target_store_gas_outcome >> simp[] >>
  (conj_tac >- metis_tac[expr_sim_inv_gas_obs]) >>
  goal_assum (drule_at (Pat `target_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `assign_alloc_ok _ _ _`)) >>
  simp[] >>
  gvs[]
QED

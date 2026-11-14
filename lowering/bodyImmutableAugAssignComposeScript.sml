Theory bodyImmutableAugAssignCompose
Ancestors
  bodyImmutableAugAssignFacts bodyImmutableAugAssignPaths bodyImmutableAugAssignExec
  stmtSimAugAssignStorage stmtSimAugAssignAttr stmtSimAugAssignPlace
  bodySim exprSimHypsDefs exprSimHyps stmtSimDefs stmtSimProps
  stmtLowering exprLowering exprLoweringProps compileEnv loweringPosts
  freshWrites emitHelperProps localPtrsProps finite_map fragExec venomState
  exprSimDefs gasContext gasSummary gasOutcome fragGasMode fragGasPath
  stmtSimAugAssign vyperTypeInvariants vyperTypeSystem
  exprSimSource exprSimProps exprBopSimProps exprBopSimDefs exprOperandVar
  vyperInterpreter vyperState gasStorage vyperStorageTrace vyperStorageFootprint
  immutableAssignCompose

Theorem immutable_augassign_rhs_bad_storage[local]:
  (!gs. eval_target_place cx (TopLevelNameTarget nsid) (es with gas_obs := gs) =
          (INL p,es with gas_obs := gs) /\
        read_place cx p (es with gas_obs := gs) = (INL v0,es with gas_obs := gs) /\
        place_type_value cx p (es with gas_obs := gs) = (INL tv,es with gas_obs := gs)) /\
  gas_marked_path F ctx func s0 0 (OK t) /\
  gas_bad_storage_at cx st0 (bind (eval_expr cx e) (read_result cx))
    (es with gas_obs := []) t marks ==>
  gas_bad_storage_at cx st0
    (eval_stmt cx (AugAssign ty (TopLevelNameTarget nsid) bop e)) es s0 marks
Proof
  strip_tac >>
  `gas_explicit marks s0.vs_gas_readings =
   gas_explicit marks t.vs_gas_readings` by
    (drule gas_marked_path_exec >> strip_tac >>
     drule gas_path_suffix >> simp[gasCountTheory.gas_count_suffix_def]) >>
  `gas_bad_storage_at cx st0
    (bind (bind (eval_expr cx e) (read_result cx))
      (\v. bind (lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
        tv bop v0 v)) (write_place cx p))) es s0 marks` by
    (irule gas_bad_storage_at_bind_left >> conj_tac
     >- (gen_tac >> BETA_TAC >> irule storage_trace_frame_bind_all >>
         simp[storage_trace_frame_lifts,storage_trace_frame_write_place]) >>
     fs[gas_bad_storage_at_def]) >>
  pop_assum mp_tac >> rewrite_tac[gas_bad_storage_at_def] >>
  strip_tac >> gen_tac >> first_x_assum (qspec_then `tail` mp_tac) >>
  qpat_x_assum `!gs. eval_target_place _ _ _ = _ /\ _`
    (qspec_then `gas_explicit marks s0.vs_gas_readings ++ tail` strip_assume_tac) >>
  drule_all immutable_augassign_forced >>
  disch_then (qspecl_then [`ty`,`e`,`bop`] SUBST1_TAC) >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]
QED

Theorem immutable_deploy_augassign_frag:
  !ctx func cx lctx RetQ cenv ret_ty env env' tops nsid ty bop e es ity.
    body_inv tops ctx cenv cx /\ cx.in_deploy /\
    supported_immutable_type tops nsid = SOME ity /\
    type_stmt env ret_ty (AugAssign ty (TopLevelNameTarget nsid) bop e) =
      SOME env' /\
    ((?s p s1 s2 cur s3 s4 ptv s5.
        eval_target_place cx (TopLevelNameTarget nsid) s = (INL p,s1) /\
        read_place cx p s2 = (INL cur,s3) /\
        place_type_value cx p s4 = (INL ptv,s5)) ==>
     expr_sim_case F ctx func cenv cx e) /\
    expr_body_pre cenv cx env e es ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AugAssign ty (TopLevelNameTarget nsid) bop e))
      (eval_stmt cx (AugAssign ty (TopLevelNameTarget nsid) bop e)) es
Proof
  rpt gen_tac >> strip_tac >> PairCases_on `nsid` >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  drule_all immutable_augassign_metadata >> strip_tac >> gvs[] >>
  drule_all immutable_augassign_entry >> strip_tac >>
  drule_all immutable_augassign_source_prefix >> strip_tac >>
  `expr_sim_case F ctx func cenv cx e` by metis_tac[] >>
  drule_all immutable_augassign_prefix_obs >> strip_tac >>
  drule aug_place_typing >> strip_tac >>
  simp[stmt_frag_def,stmt_framed_frag_def] >> rpt gen_tac >> strip_tac >>
  drule_all immutable_augassign_code_parts >> strip_tac >> gvs[] >>
  reverse (Cases_on `storage_trace_domain cx st0 es.storage_trace`)
  >- (rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
      irule gas_bad_storage_at_initial >>
      simp[vyperStorageTraceTheory.evaluate_storage_trace_frame]) >>
  `?H0. valid_horizon cx st0 H0 es.storage_trace` by
    metis_tac[storage_trace_domain_def] >>
  `stmt_state_rel H0 ctx func cenv cx es s0 /\
   storage_well_formed_on cx es (FST H0)` by metis_tac[] >>
  suspend "load_prefix"
QED

Resume immutable_deploy_augassign_frag[load_prefix]:
  `cs_extends sa s1` by
    metis_tac[cs_appends_emit_helpers,cs_appends_def] >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  drule compile_binop_grows >> strip_tac >>
  `cs_extends s3 sb` by
    metis_tac[cs_appends_emit_helpers,cs_appends_def] >>
  `cs_extends s1 s3 /\ cs_extends s1 sb /\ cs_extends s2 sb /\
   cs_extends sa s2 /\ cs_extends sa s3` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\
   fn_has_code s2 s3 func /\ fn_has_code s3 sb func` by
    metis_tac[fn_has_code_mid,cs_extends_refl] >>
  `off < dimword (:256)` by decide_tac >>
  `mload off s0 = typed_val_to_w256 tv v` by
    (irule (INST_TYPE [alpha |-> ``:256``] immutable_augassign_load) >> simp[] >>
     qexistsl_tac [`H0`,`cenv`,`ctx`,`cx`,`es`,`func`,`nsid1`,`imms`,`ity`] >>
     simp[]) >>
  drule_all (Q.INST [`H` |-> `H0`] immutable_augassign_load_frame_fields) >>
  strip_tac >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es t /\
    storage_well_formed_on cx es (FST H)` by
    (rpt strip_tac
     >- (irule (INST_TYPE [alpha |-> ``:256``] stmt_state_rel_fields_transport) >>
         conj_tac >- (qexists_tac `s0` >> simp[] >> metis_tac[]) >>
         qexists_tac `H0` >> simp[]) >> metis_tac[]) >>
  rename1 `value_has_type tv v0` >>
  suspend "rhs_outcome"
QED

Resume immutable_deploy_augassign_frag[rhs_outcome]:
  `expr_sim ctx func cenv cx ity e (es with gas_obs := [])` by
    (irule expr_sim_case_apply >> simp[] >> conj_tac
     >- (qexists_tac `env` >> simp[]) >>
     qexists_tac `F` >> simp[]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok
    (es with gas_obs := [])` by
    (simp[] >> irule immutable_augassign_rhs_admissible >> metis_tac[]) >>

  qpat_x_assum `expr_sim _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`st0`,`s1`,`s2`,`rhs_op`,`t`] mp_tac) >>
  impl_tac
  >- (simp[] >> rpt strip_tac >>
      `storage_well_formed_on cx (es with gas_obs := []) (FST H) <=>
       storage_well_formed_on cx es (FST H)` by
        (irule storage_well_formed_on_backends >> simp[]) >>
      metis_tac[]) >>
  rewrite_tac[gasOutcomeTheory.gas_outcome_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      irule immutable_augassign_rhs_bad_storage >> metis_tac[])
  >- suspend "rhs_summary" >>
  qexists_tac `marks` >> disj2_tac >> disj2_tac >>
  qexistsl_tac [`err`,`ee`,`leaf`,`finish'`] >>
  irule immutable_augassign_rhs_exempt >> conj_tac
  >- metis_tac[] >> qexists_tac `t` >> simp[]
QED

Resume immutable_deploy_augassign_frag[rhs_summary]:
  qexists_tac `marks` >>
  Cases_on `gas_bad_storage_at cx st0 (bind (eval_expr cx e) (read_result cx))
    (es with gas_obs := []) t marks`
  >- (disj1_tac >> irule immutable_augassign_rhs_bad_storage >> metis_tac[]) >>
  disj2_tac >> disj1_tac >>
  qpat_x_assum `gasSummary$gas_summary_at _ _ _ _ _ _ _`
    (strip_assume_tac o BETA_RULE o REWRITE_RULE [gas_summary_at_def]) >>
  `storage_trace_domain cx st0 es_end.storage_trace` by
    (CCONTR_TAC >> metis_tac[gas_bad_storage_at_counted_prefix]) >>
  `?H2. valid_horizon cx st0 H2 es_end.storage_trace` by
    metis_tac[storage_trace_domain_def] >>
  simp[gas_summary_at_def]
  >- suspend "rhs_normal" >>
  `expr_exit res r` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> expr_exit _ _`
      (qspec_then `H2` mp_tac) >> simp[]) >>
  `?ex. res = INR ex` by (Cases_on `res` >> gvs[]) >> gvs[] >>
  qexistsl_tac [`INR ex`,`es_end`,`r`] >> conj_tac
  >- (irule immutable_augassign_rhs_exception_exec >> conj_tac
      >- metis_tac[] >> qexists_tac `t` >> simp[]) >>
  disj2_tac >> simp[] >> rpt strip_tac >> simp[stmt_exit_def] >> disj1_tac >>
  metis_tac[expr_exit_INR_type]
QED

Resume immutable_deploy_augassign_frag[rhs_normal]:
  gvs[] >> rename1 `gas_marked_exec _ _ _ _ _ _ ee (OK u)` >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (qspec_then `H2` mp_tac) >> impl_tac >- simp[] >> strip_tac >> gvs[] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    expr_post H ctx func cenv cx e (es with gas_obs := [])
      s1 s2 t (ee with gas_obs := []) v rhs_op u` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
       (qspec_then `H` mp_tac) >> simp[]) >>
  `bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks t.vs_gas_readings) =
      (INL v,ee with gas_obs := [])` by
    (drule gas_marked_exec_observation >>
     disch_then (qspec_then `[]` mp_tac) >> simp[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       valid_horizon cx st0 H es.storage_trace` by
    (rpt strip_tac >>
     qpat_x_assum `bind (eval_expr cx e) _ _ = _` assume_tac >>
     drule_at (Pos (el 2)) valid_horizon_frame >>
     simp[stmtSimAugAssignTheory.augassign_rhs_trace_frame]) >>
  `well_formed_type (get_tenv cx) ity` by
    (fs[expr_sim_inv_def,env_consistent_def,env_context_consistent_def] >>
     metis_tac[assignable_type_well_formed]) >>
  drule_all augassign_attr_binop_ready >>
  disch_then (qspecl_then [`func`,`ee with gas_obs := []`,`ctx`] strip_assume_tac) >>
  `expr_res_ok (bop_result cx ity bop [ity;expr_type e] v0 v ee)` by
    (`expr_res_ok (bop_result cx ity bop [ity;expr_type e] v0 v
       (ee with gas_obs := []))` suffices_by simp[] >>
     `word_value v0` by metis_tac[exprSimSourceTheory.word_value_type_typed] >>
     irule immutable_augassign_binop_admissible >> metis_tac[]) >>
  suspend "binop_ready"
QED

Resume immutable_deploy_augassign_frag[binop_ready]:
  `expr_body_pre cenv cx env e
     (es with gas_obs := gas_explicit marks t.vs_gas_readings)` by simp[] >>
  drule_all (REWRITE_RULE [ETA_AX] expr_body_pre_word_result) >>
  strip_tac >> gvs[] >>
  `expr_post H2 ctx func cenv cx e (es with gas_obs := [])
     s1 s2 t (ee with gas_obs := []) v rhs_op u` by metis_tac[] >>
  qpat_assum `expr_post H2 _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  `word_value v0` by metis_tac[exprSimSourceTheory.word_value_type_typed] >>
  `eval_operand (Var out) t = SOME (val_to_w256 v0)` by
    simp[typed_val_to_w256_word_value] >>
  `is_word_type (expr_type e)` by
    metis_tac[exprSimSourceTheory.word_value_type_word] >>
  `eval_operand rhs_op u = SOME (val_to_w256 v)` by
    (qspecl_then [`cx`,`expr_type e`,`v`,`rhs_op`,`u`] mp_tac expr_val_rel_word >>
     fs[expr_post_def] >> metis_tac[]) >>
  `eval_operand (Var out) u = SOME (val_to_w256 v0)` by
    (irule eval_operand_frame >> simp[] >>
     qexistsl_tac [`s1`,`t`] >> gvs[expr_post_def]) >>
  `not_fresh_at s2 out /\ local_ptrs_reserved cenv s2` by
    metis_tac[not_fresh_at_mono,local_ptrs_reserved_next_var] >>
  `stmt_state_rel H2 ctx func cenv cx (ee with gas_obs := []) u` by
    fs[expr_post_def] >>
  `~u.vs_halted` by
    metis_tac[gas_marked_exec_def,gas_marked_path_exec,gas_path_normal] >>
  qpat_x_assum `binop_frag _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [exprBopSimDefsTheory.binop_frag_def,
                           exprBopSimDefsTheory.binop_frag_words_def]) >>
  disch_then (qspecl_then [`st0`,`s2`,`s3`,`Var out`,`rhs_op`,`res_op`,`u`] mp_tac) >>
  impl_tac
  >- (simp[] >> rpt strip_tac >>
      fs[expr_post_def] >> metis_tac[exprOperandVarTheory.compile_lower_value_var]) >>
  strip_tac >- suspend "operator_normal" >> suspend "operator_exit"
QED

Resume immutable_deploy_augassign_frag[operator_normal]:
  gvs[] >> rename1 `eval_operand res_op s = SOME (val_to_w256 result)` >>
  `bop_result cx ity bop [ity;expr_type e] v0 v ee =
     case evaluate_binop
       (case type_to_int_bound ity of SOME bound => bound | NONE => Unsigned 0)
       tv bop v0 v of INL x => INL x | INR err => INR (Error err)` by
    (irule bop_result_augassign >> metis_tac[word_value_not_bytes]) >>
  `evaluate_binop
     (case type_to_int_bound ity of SOME bound => bound | NONE => Unsigned 0)
     tv bop v0 v = INL result` by gvs[AllCaseEqs()] >>
  `value_has_type tv result` by simp[] >>
  `eval_operand res_op s = SOME (typed_val_to_w256 tv result)` by
    simp[typed_val_to_w256_word_value] >>
  `stmt_state_rel H2 ctx func cenv cx (ee with gas_obs := []) s /\
   storage_well_formed_on cx (ee with gas_obs := []) (FST H2)` by
    (qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
      (qspec_then `H2` mp_tac) >> simp[]) >>
  `?fin last. write_place cx (ImmutablePlace cenv.ce_module nsid1 []) result
      (ee with gas_obs := []) = (INL (),fin) /\
    gas_marked_path F ctx func s 0 (OK last) /\
    last.vs_accounts = s.vs_accounts /\ last.vs_transient = s.vs_transient /\
    last.vs_requests = s.vs_requests /\ last.vs_call_ctx = s.vs_call_ctx /\
    stmt_post H2 ctx func cx lctx cenv cenv s3 sb (ee with gas_obs := []) s
      (INL ()) fin last` by
    (irule immutable_augassign_store_post_path_fields >>
     simp[alloca_frame_same] >>
     conj_tac >- metis_tac[] >>
     qexistsl_tac [`env`,`res_op`,`s3`] >> simp[]) >>
  suspend "store_post"
QED

Resume immutable_deploy_augassign_frag[store_post]:
  `alloca_frame cenv ee s2 u cenv ee s` by
    (irule (INST_TYPE [alpha |-> ``:256``] alloca_frame_of_mem_frame) >>
     qpat_assum `stmt_state_rel _ _ _ _ _ ee u`
       (irule_at Any) >>
     simp[] >> metis_tac[]) >>
  `stmt_post H2 ctx func cx lctx cenv cenv s2 sb (ee with gas_obs := []) u
     (INL ()) fin last` by
    (irule stmtSimDeclComposeTheory.stmt_post_entry_frame >>
     qpat_assum `stmt_post _ _ _ _ _ _ _ s3 _ _ s _ _ _` (irule_at Any) >>
     simp[] >> metis_tac[not_fresh_at_mono]) >>
  `stmt_post H2 ctx func cx lctx cenv cenv s1 sb
     (es with gas_obs := []) t
     (INL ()) fin last` by
    (`MAP FDOM ee.scopes = MAP FDOM es.scopes` by
       (qpat_assum `bind (eval_expr cx e) (read_result cx) _ = _`
          (mp_tac o MATCH_MP eval_read_preserves_scopes_dom) >> simp[]) >>
     `stmt_state_rel H2 ctx func cenv cx es t` by metis_tac[] >>
     `expr_post H2 ctx func cenv cx e (es with gas_obs := [])
        s1 s2 t (ee with gas_obs := []) v rhs_op u` by metis_tac[] >>
     irule stmt_post_expr_entry_frame >>
     qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     simp[]) >>
  `alloca_frame cenv es sa s0 cenv es t` by
    (`stmt_state_rel H0 ctx func cenv cx es s0` by metis_tac[] >>
     irule (INST_TYPE [alpha |-> ``:256``] alloca_frame_of_mem_frame) >>
     qpat_assum `stmt_state_rel _ _ _ _ _ es s0` (irule_at Any) >>
     simp[] >> metis_tac[]) >>
  `stmt_post H2 ctx func cx lctx cenv cenv sa sb es s0 (INL ()) fin last` by
    (irule stmtSimDeclComposeTheory.stmt_post_entry_frame >>
     qpat_assum `stmt_post _ _ _ _ _ _ _ s1 _ _ t _ _ _` (irule_at Any) >>
     qspecl_then [`MLOAD`,`[Lit (n2w off)]`,`sa`] mp_tac ci_mono_emit_op >>
     simp[ci_mono_def] >> rpt strip_tac >>
     irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `gas_marked_path F ctx func u 0 (OK last)` by
    (drule_all gas_marked_path_then >> simp[]) >>
  `fin = fin with gas_obs := []` by
    (drule immutable_write_place_gas_obs >>
     disch_then (qspec_then `[]` mp_tac) >> simp[] >> strip_tac >> gvs[]) >>
  `fin.storage_trace = ee.storage_trace` by
    (drule vyperPlaceFramesTheory.write_immutable_place_frame >> strip_tac >> gvs[]) >>
  `!H. valid_horizon cx st0 H fin.storage_trace ==>
    stmt_post H ctx func cx lctx cenv cenv sa sb es s0 (INL ()) fin last` by
    (rpt strip_tac >>
     `stmt_state_rel H ctx func cenv cx (ee with gas_obs := []) s /\
      storage_well_formed_on cx (ee with gas_obs := []) (FST H)` by
       (`valid_horizon cx st0 H ee.storage_trace` by metis_tac[] >>
        simp[] >> metis_tac[]) >>
     mp_tac (Q.INST
       [`H0` |-> `H2`, `ce` |-> `cenv`, `q` |-> `last`,
        `ee` |-> `ee with gas_obs := []`, `u` |-> `s`,
        `src` |-> `cenv.ce_module`, `id` |-> `nsid1`, `v` |-> `result`]
       (INST_TYPE [alpha |-> ``:256``, beta |-> ``:256``]
         immutable_assign_stmt_post_transport)) >> simp[]) >>
  qexistsl_tac [`INL ()`,`fin`,`OK last`] >> simp[] >>
  reverse conj_tac >- (disj1_tac >> metis_tac[]) >>
  irule immutable_augassign_rhs_normal_exec >>
  qexistsl_tac [`ee`,`ImmutablePlace NONE nsid1 []`,`t`,`tv`,`u`,`v`,`v0`] >>
  simp[] >> irule immutable_augassign_continuation_exec >>
  simp[lift_sum_def,bind_def,return_def] >>
  qpat_x_assum `write_place _ _ _ _ = _` mp_tac >> simp[]
QED

Resume immutable_deploy_augassign_frag[operator_exit]:
  `bop_result cx ity bop [ity;expr_type e] v0 v ee =
     case evaluate_binop
       (case type_to_int_bound ity of SOME bound => bound | NONE => Unsigned 0)
       tv bop v0 v of
       INL x => INL x | INR err => INR (Error err)` by
    (irule bop_result_augassign >> metis_tac[word_value_not_bytes]) >>
  Cases_on `evaluate_binop
       (case type_to_int_bound ity of SOME bound => bound | NONE => Unsigned 0)
       tv bop v0 v`
  >- (gvs[] >> fs[expr_exit_def,exit_result_def]) >>
  gvs[] >>
  qexistsl_tac [`INR (Error y)`,`ee with gas_obs := []`,`r`] >>
  conj_tac
  >- (irule immutable_augassign_rhs_normal_exec >>
      qexistsl_tac [`ee`,`ImmutablePlace NONE nsid1 []`,`t`,`tv`,`u`,`v`,`v0`] >>
      simp[] >> irule immutable_augassign_continuation_exec >>
      simp[lift_sum_def,bind_def,raise_def]) >>
  disj2_tac >> simp[] >> rpt strip_tac >>
  simp[stmt_exit_def] >> metis_tac[expr_exit_INR_type]
QED

Finalise immutable_deploy_augassign_frag

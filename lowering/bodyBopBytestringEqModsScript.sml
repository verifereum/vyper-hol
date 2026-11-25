(* Linked bytestring equality/inequality route. *)
Theory bodyBopBytestringEqMods
Ancestors
  bodyFullPredsMods bodyFullPostsMods bodyFullShadowBodyInv bodyInvSplit
  bodyFullBopBytestringCuts bodyFullBopBytestringChild bodyFullBopBytestringIntervals
  bodyFullBopBytestringPost bodyFullBopBytestringFinalPost
  bodyFullBopBytestringHash bodyFullBopBytestringDigest bodyFullBopBytestringFinish
  bodyBopBytestringOperandRunMods bodyBopBytestringPrepareMods
  bodyBopBytestringBindMods bodyBopBytestringEndpointMods
  bodyFullIfExpReach vyperTypeBuiltins bodyMemBopHeldFacts
  gasOutcomeFullBindMods gasOutcomeFullPostMods gasOutcomeFullPostPathMods
  gasExemptCertMods bodyMemoryDefs exprSimFullBundleProps exprBodyPreProps
  exprSimHypsDefs exprLoweringProps loweringPosts bodyPtrDefs
  gasStorage gasShadow gasShadowState vyperStorageTrace vyperStorageFootprint
  vyperState compileEnv exprBopSimProps exprBopSimDefs exprSimSource
  vyperTypeSystem vyperTypeInvariants vyperAST vyperInterpreter contextRawReachable
Libs monadsyntax

Theorem bop_bytestring_eq_value_sim_mods:
  !DF lo d PG src tops ctx shadow_ctx func shadow_func cenv cx env ty ann bop e1 e2 es.
    (bop = Eq \/ bop = NotEq) /\ is_bytestring_type (expr_type e1) /\
    body_exprs_full_ok_mods mods exps cx [e1; e2] /\
    contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
    shadow_body_inv_mods mods exps ctx shadow_ctx /\
    body_const_cells_agree_mods mods cx env es /\
    expr_body_pre_mods mods cenv cx env (Builtin ann (Bop bop) [e1; e2]) es ==>
    expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin ann (Bop bop) [e1; e2]) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then strip_assume_tac bop_bytestring_child_pres_mods >>
  `well_typed_binop ann bop (expr_type e1) (expr_type e2)` by
    (qpat_assum `expr_body_pre_mods _ _ _ _ (Builtin _ _ _) _`
       (mp_tac o MATCH_MP expr_body_pre_mods_well_typed) >>
     simp[Once well_typed_expr_def, well_typed_builtin_app_def]) >>
  `ann = BaseT BoolT /\ expr_type e2 = expr_type e1` by
    metis_tac[well_typed_binop_def] >>
  qpat_x_assum `ann = _` SUBST_ALL_TAC >>
  rewrite_tac[expr_sim_full_mods_def] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all bop_bytestring_selected_compile_cuts >> strip_tac >>
  drule_all bop_bytestring_selected_code_intervals >> strip_tac >>
  `(!m cb. bytestring_literal_hash (gas_shadow_expr e1) = NONE /\
      lower_value compile_expr (gas_shadow_env T cenv) (expr_type e1) (gas_shadow_expr e1) shadow_sa = (m,cb) ==>
      fn_has_code shadow_sa cb shadow_func) /\
   (!m cb. bytestring_literal_hash (gas_shadow_expr e2) = NONE /\
      lower_value compile_expr (gas_shadow_env T cenv) (expr_type e2) (gas_shadow_expr e2) shadow_sh1 = (m,cb) ==>
      fn_has_code shadow_sh1 cb shadow_func)` by
    (qpat_x_assum `lower_value _ _ _ (Builtin _ _ [e1;e2]) _ = _` kall_tac >>
     qpat_x_assum `lower_value _ _ _ (gas_shadow_expr (Builtin _ _ _)) _ = _`
       (assume_tac o SIMP_RULE (srw_ss()) [gas_shadow_expr_def, gas_shadow_builtin_def, listTheory.MAP]) >>
     `is_bytestring_type (expr_type (gas_shadow_expr e1)) /\
      expr_type (gas_shadow_expr e2) = expr_type (gas_shadow_expr e1)` by simp[] >>
     drule_all bop_bytestring_selected_code_intervals >> simp[] >> strip_tac >> simp[]) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >> irule body_inv_no_phi_mods >>
     qpat_assum `contract_inv _ _ _ _ _` (irule_at Any) >> qexists_tac `func` >> simp[]) >>
  qpat_x_assum `body_exprs_full_ok_mods _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_exprs_full_ok_mods_def]) >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e1) e1 es` by
    (irule bop_bytestring_child_sim_mods >> qexistsl_tac [`env`,`exps`,`mods`,`src`,`tops`] >> simp[]) >>
  qpat_x_assum `gas_admissible _ _ _`
    (assume_tac o PURE_REWRITE_RULE [REWRITE_RULE [ETA_AX] eval_expr_bop_bind]) >>
  pure_once_rewrite_tac[REWRITE_RULE [ETA_AX] eval_expr_bop_bind] >>
  `gas_admissible (bind (eval_expr cx e1) (read_result cx)) expr_res_ok es` by
    (drule bop_bytestring_forced_head >> simp[]) >>
  irule (BETA_RULE bop_bytestring_bind_hashes_mods) >>
  qexistsl_tac [`d`,`env`,`h1`,`h2`,`mods`,`sa`,`sh1`,`sh2`] >>
  reverse (rpt conj_tac)
  >- (irule (BETA_RULE bop_bytestring_operand_run_mods) >>
      rpt (conj_tac >- (first_assum ACCEPT_TAC ORELSE
        (gen_tac >> disch_tac >> first_x_assum (drule_then strip_assume_tac) >>
         first_assum ACCEPT_TAC))) >>
      qexistsl_tac [`shadow_func`,`shadow_sa`] >>
      reverse conj_tac >- first_assum ACCEPT_TAC >>
      irule (cj 1 bop_bytestring_child_cut_mods) >> simp[])
  >- suspend "right_operand" >>
  suspend "compare"
QED

Resume bop_bytestring_eq_value_sim_mods[right_operand]:
  qx_genl_tac [`m1`,`v1`,`mid`,`G1`,`tn1`,`t`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then (qspec_then `st0` strip_assume_tac) bop_bytestring_operand_source_mods >>
  `body_expr_full_ok_mods mods exps cx e2` by
    (drule (REWRITE_RULE [ETA_AX] exprSimSourceTheory.eval_expr_read_INL) >> strip_tac >>
     qpat_assum `_ ==> body_exprs_full_ok_mods _ _ _ [e2]` mp_tac >>
     (impl_tac >- rpt (goal_assum (drule_at Any))) >>
     simp[Once body_exprs_full_ok_mods_def]) >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e2) e2 mid` by
    (irule bop_bytestring_child_sim_mods >> qexistsl_tac [`env`,`exps`,`mods`,`src`,`tops`] >> simp[]) >>
  `gas_admissible (bind (eval_expr cx e2) (read_result cx)) expr_res_ok mid` by
    (qpat_assum `gas_admissible (bind (bind (eval_expr cx e1) _) _) _ _`
       (mp_then (Pat `gas_admissible _ _ _`) mp_tac stmtSimForRoundsTheory.gas_admissible_bind_tail) >>
     BETA_TAC >> disch_then (drule_then mp_tac) >> simp[evaluation_state_component_equality] >>
     disch_then (ACCEPT_TAC o MATCH_MP bop_bytestring_forced_head)) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _ /\ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` (drule_then strip_assume_tac)) >>
  `return_buf_frame d cenv sh1 t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s0`,`sa`] >> fs[wb_frame_def]) >>
  `local_ptrs_reserved cenv sh1` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `!z. not_fresh_at sa z ==> not_fresh_at sh1 z` by
    (rpt strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  irule (BETA_RULE bop_bytestring_operand_run_mods) >>
  rpt (conj_tac >- (first_assum ACCEPT_TAC ORELSE
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _ /\ _`
       (qspec_then `H` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
     strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) ORELSE
    (simp[] >> NO_TAC))) >>
  qexistsl_tac [`shadow_func`,`shadow_sh1`] >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  drule_all_then strip_assume_tac
    (Q.INST [`e` |-> `e2`, `sa` |-> `sh1`, `shadow_sa` |-> `shadow_sh1`]
       bop_bytestring_child_cut_mods) >> first_assum ACCEPT_TAC
QED

Resume bop_bytestring_eq_value_sim_mods[compare]:
  qx_genl_tac [`m1`,`v1`,`mid`,`G1`,`tn1`,`t`,`m2`,`v2`,`ee`,`G2`,`tn2`,`u`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `sa.cs_next_id <= sh1.cs_next_id` by
    (drule_all_then strip_assume_tac
       (Q.INST [`e` |-> `e1`,`sz` |-> `sh1`] bop_bytestring_child_cut_mods) >>
     first_assum ACCEPT_TAC) >>
  drule_all_then (qspec_then `st0` strip_assume_tac) bop_bytestring_operand_source_mods >>
  `expr_body_pre_mods mods cenv cx env e2 mid` by simp[] >>
  drule_all_then (qspec_then `st0` strip_assume_tac)
    (Q.INST [`e` |-> `e2`,`es` |-> `mid`,`ee` |-> `ee`] bop_bytestring_operand_source_mods) >>
  qpat_x_assum `expr_type e2 = expr_type e1` SUBST_ALL_TAC >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) mid.storage_trace` by simp[] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> (?v bs. _) /\ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` (drule_then
      (qx_choose_then `vl` (qx_choose_then `contents1` (map_every assume_tac o CONJUNCTS)) o CONJUNCT1))) >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> (?v bs. _) /\ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` (drule_then
      (qx_choose_then `vr` (qx_choose_then `contents2` (map_every assume_tac o CONJUNCTS)) o CONJUNCT1))) >>
  qpat_x_assum `INL v1 = INL vl` (SUBST_ALL_TAC o SYM o REWRITE_RULE [sumTheory.INL_11]) >>
  qpat_x_assum `INL v2 = INL vr` (SUBST_ALL_TAC o SYM o REWRITE_RULE [sumTheory.INL_11]) >>
  qabbrev_tac `w1 = word_of_bytes_be (Keccak_256_w64 contents1) : bytes32` >>
  qabbrev_tac `w2 = word_of_bytes_be (Keccak_256_w64 contents2) : bytes32` >>
  irule gas_outcome_full_mods_post_source >>
  qexistsl_tac
    [`\H res ee' Gf tnf t.
       res = INL (BoolV (if bop = Eq then (w1:bytes32) = w2 else w1 <> w2)) /\
       ee' = (ee with gas_obs := []) /\
       eval_operand op t = SOME (bool_to_word (if bop = Eq then w1 = w2 else w1 <> w2)) /\
       ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
       t.vs_inst_idx = LENGTH sb.cs_current_insts /\
       (?raw. t = (raw with vs_inst_idx := LENGTH sb.cs_current_insts) /\
        run_inst_seq (emitted_insts sh2 sb) u = OK raw /\
        (raw with vs_vars := u.vs_vars) = u) /\
       (!x. not_fresh_at sh2 x ==> lookup_var x t = lookup_var x u /\
        FLOOKUP Gf x = FLOOKUP G2 x /\ FLOOKUP tnf.t_var x = FLOOKUP tn2.t_var x) /\
       tnf.t_mem = tn2.t_mem /\ tnf.t_stor = tn2.t_stor /\
       tnf.t_trans = tn2.t_trans /\ tnf.t_imm = tn2.t_imm /\
       op_prov Gf op = NONE /\ op_taint tnf op = {} /\
       (!x. op = Var x ==> not_fresh_at sb x)`,
     `\H res ee' gt r.
       expr_exit res r /\ halt_exit H cx ee' res r /\
       (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u)`] >>
  rpt conj_tac
  >- suspend "normal_endpoint"
  >- (BETA_TAC >> rpt gen_tac >> MATCH_ACCEPT_TAC bop_bytestring_compare_exit_endpoint_mods) >>
  irule_at Any bop_bytestring_compare_digest_endpoint_mods >> suspend "digest_requirements"
QED

Resume bop_bytestring_eq_value_sim_mods[normal_endpoint]:
  qx_genl_tac [`H`,`res`,`ef`,`Gf`,`tnf`,`ss`] >> BETA_TAC >>
  disch_then (map_every strip_assume_tac o CONJUNCTS) >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  qpat_x_assum `ef = _` SUBST_ALL_TAC >>
  qpat_x_assum `res = _` SUBST_ALL_TAC >>
  qexists_tac `BoolV (if bop = Eq then w1 = w2 else w1 <> w2)` >>
  rewrite_tac[post_value_type_def] >>
  irule (REWRITE_RULE [post_value_type_def] bop_bytestring_compare_final_post_endpoint_mods) >>
  qpat_assum `ee with gas_obs := [] = ee`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> PURE_REWRITE_TAC [th]) >>
  `valid_horizon cx st0 H ee.storage_trace` by fs[] >>
  `valid_horizon cx st0 H mid.storage_trace` by simp[] >>
  `valid_horizon cx st0 H es.storage_trace` by simp[] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> (?v bs. _) /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> (?v bs. _) /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  `sa.cs_next_var <= sh2.cs_next_var` by decide_tac >>
  `local_ptrs_reserved cenv sh2` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `!z. not_fresh_at sa z ==> not_fresh_at sh2 z` by
    (rpt strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`G1`,`G2`,`mid`,`h1`,`h2`,`raw`,`raw`,`sh1`,`sh2`,`t`,`tn1`,`tn2`,`u`] >>
  simp[]
QED

Resume bop_bytestring_eq_value_sim_mods[digest_requirements]:
  `eval_operand h1 u = SOME w1 /\ op_prov G2 h1 = NONE /\ op_taint tn2 h1 = {}` by
    (qpat_assum `wb_frame cenv mid ee sh1 t u`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [wb_frame_def]) >>
     qpat_assum `ghost_kept_at lo cenv mid sh1 G1 tn1 t G2 tn2`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [ghost_kept_at_def]) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`eval_operand h1 t = SOME w1`, `op_prov G1 h1 = NONE`,
        `op_taint tn1 h1 = {}`, `!z. h1 = Var z ==> not_fresh_at sh1 z`,
        `!l. h1 <> Label l`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `h1` >>
     simp[venomStateTheory.eval_operand_def,ptrDisciplineTheory.op_prov_def,
          ptrDisciplineTheory.op_taint_def] >> metis_tac[]) >>
  `!z. h1 = Var z ==> not_fresh_at sh2 z` by
    (rpt strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >>
     qexists_tac `sh1` >> simp[]) >>
  `allocas_from lo u` by
    (qpat_assum `ghost_inv_at_mods _ lo _ cenv cx ee G2 tn2 u`
       (mp_tac o REWRITE_RULE [ghost_inv_at_mods_def]) >> simp[]) >>
  `env.type_defs = get_tenv cx` by
    (qpat_assum `expr_sim_inv_mods mods cenv cx env ee`
       (mp_then Any assume_tac expr_sim_inv_mods_env) >>
     drule vyperTypeEvalCaseProofsTheory.env_consistent_type_defs_get_tenv >> simp[]) >>
  conj_tac
  >- (drule_all held_bytestring_eqne_types >>
      simp[] >> disch_then (DISJ_CASES_THEN (qx_choose_then `cap` assume_tac)) >>
      qexists_tac `cap` >> simp[]) >>
  simp[] >> conj_tac
  >- (qexistsl_tac [`h1`,`h2`] >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `v1 = BytesV contents1 \/ _` strip_assume_tac >>
      simp[Abbr `w1`,byteTheory.word_of_bytes_be_def]) >>
  conj_tac
  >- (qpat_x_assum `v2 = BytesV contents2 \/ _` strip_assume_tac >>
      simp[Abbr `w2`,byteTheory.word_of_bytes_be_def]) >>
  qpat_x_assum `value_runtime_typed env _ v1` mp_tac >>
  qpat_x_assum `value_runtime_typed env _ v2` mp_tac >>
  simp[vyperTypeExprSoundnessTheory.value_runtime_typed_def] >>
  disch_then (qx_choose_then `tv` (map_every assume_tac o CONJUNCTS)) >>
  disch_then (qx_choose_then `tv'` (map_every assume_tac o CONJUNCTS)) >>
  `tv' = tv` by fs[] >>
  qexists_tac `tv` >> fs[]
QED

Finalise bop_bytestring_eq_value_sim_mods

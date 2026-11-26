(* Linked tuple selection is a base evaluation followed by one address ADD. *)
Theory bodySubscriptTupleVVMods
Ancestors
  bodySubscriptValueBaseMods bodySubscriptTupleSourceMods bodySubscriptTupleAddMods
  bodySubscriptTuplePostMods bodyAttributeReadOperandMods bodySimStmtFacts
  createSizeRawGasAdmissibleMods bodyFullPostsMods exprBodyPreProps exprSimTuple exprSimDefs
  exprSimAccounts exprSimAttributeProps exprSimUnwrap exprLowering exprLoweringProps bodyPtrDefs fragExec
  gasShadowCompilePure bodyFullShadowBodyInv
  gasOutcomeFullBindMods gasOutcomeFullPostMods gasExemptCertMods
  gasShadowCompileStmtHelpers gasShadowCompile gasShadowState gasShadow
  vyperStorageTrace vyperStorageFootprint vyperInterpreter vyperState vyperAST
  vyperTyping context compileEnv list integer
Libs monadsyntax

Triviality tuple_shadow_base_cut:
  compile_expr cenv ty obj sa = (bvv,sm) /\
  compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr (Subscript ann obj (Literal ity (IntL (&k))))) sha = (vv,shb) /\
  expr_type obj = TupleT tys /\ place_type cenv obj = ValPT (TupleT tys) /\
  gas_shadow_state sa sha ==>
  ?shm. compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr obj) sha = (bvv,shm) /\
        gas_shadow_state sm shm /\ cs_extends sha shm /\ cs_extends shm shb
Proof
  strip_tac >>
  qpat_assum `compile_expr _ _ (gas_shadow_expr _) _ = _` mp_tac >>
  simp[NoAsms,gas_shadow_expr_def] >> strip_tac >>
  `expr_type (gas_shadow_expr obj) = TupleT tys /\
   place_type (gas_shadow_env T cenv) (gas_shadow_expr obj) = ValPT (TupleT tys)` by
    simp[gas_shadow_place_type] >>
  drule_all_then strip_assume_tac compile_expr_tuple_subscript >>
  `gas_shadow_compiles (compile_expr cenv ty obj)
     (compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr obj))` by
    irule gas_shadow_stmt_compile_expr_env >>
  qpat_x_assum `gas_shadow_compiles _ _`
    (qspecl_then [`sa`,`sha`] mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
  simp[] >> strip_tac >> gvs[] >>
  qpat_assum `compile_expr _ _ (gas_shadow_expr obj) _ = _`
    (strip_assume_tac o MATCH_MP compile_expr_extends) >>
  drule_then strip_assume_tac emit_op_extends_next_var >> simp[]
QED

Theorem subscript_tuple_vv_sim_full_mods:
  !DF lo d ctx shadow_ctx PG func shadow_func mods cenv cx env ty ann obj idx es tys.
    expr_body_pre_mods mods cenv cx env (Subscript ann obj idx) es /\
    expr_type obj = TupleT tys /\ place_type cenv obj = ValPT (TupleT tys) /\
    post_value_type cenv obj = expr_type obj /\
    expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty obj es ==>
    expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Subscript ann obj idx) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac subscript_tuple_pre_mods >>
  qpat_x_assum `idx = _` SUBST_ALL_TAC >> qpat_x_assum `ann = _` SUBST_ALL_TAC >>
  rewrite_tac[expr_vv_sim_full_mods_def] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac compile_expr_tuple_subscript >>
  qpat_x_assum `vv = LocatedValue _ _` SUBST_ALL_TAC >>
  rename1 `compile_expr cenv ty obj sa = (bvv,sm)` >>
  rename1 `fn_has_code sha shb shadow_func` >>
  drule_all_then strip_assume_tac tuple_shadow_base_cut >>
  rename1 `gas_shadow_state sm shm` >>
  drule_then strip_assume_tac emit_op_extends_next_var >>
  `cs_extends sa sm` by
    (qpat_assum `compile_expr cenv ty obj sa = _`
       (strip_assume_tac o MATCH_MP compile_expr_extends) >> simp[]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (irule fn_has_code_split >> simp[]) >>
  `fn_has_code sha shm shadow_func /\ fn_has_code shm shb shadow_func` by
    (irule fn_has_code_split >> simp[]) >>
  `gas_admissible (eval_expr cx obj) expr_vv_res_ok es` by
    (irule create_raw_gas_admissible_mods >> goal_assum (drule_at Any) >> simp[]) >>
  qhdtm_x_assum `expr_vv_sim_full_mods` (mp_tac o REWRITE_RULE [expr_vv_sim_full_mods_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sm`,`sha`,`shm`,`bvv`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  suspend "bind"
QED

Resume subscript_tuple_vv_sim_full_mods[bind]:
  qmatch_asmsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ (eval_expr cx obj) _ baseQ baseR` >>
  simp[tuple_source] >> irule gas_outcome_full_mods_bind_all >> BETA_TAC >>
  rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_result >>
      goal_assum (drule_at Any) >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_result >> simp[])
  >~ [`storage_trace_frame (eval_expr _ _)`]
  >- simp[evaluate_storage_trace_frame]
  >~ [`storage_trace_frame (select_result _ _ _ _)`]
  >- simp[storage_trace_frame_select] >>
  qexists_tac `\H res ee G tn t. baseQ H res ee G tn t /\ ~t.vs_halted /\ ee.gas_obs = []` >>
  reverse conj_tac
  >- (irule gas_outcome_full_mods_post_source >>
      qpat_assum `gas_outcome_full_mods _ _ _ _ (eval_expr _ _) _ baseQ baseR` (irule_at Any) >>
      conj_tac >- simp[] >> simp[Abbr `baseR`] >> gen_tac >> Cases >> simp[expr_exit_def]) >>
  suspend "selected"
QED

Resume subscript_tuple_vv_sim_full_mods[selected]:
  qx_genl_tac [`marks`,`res`,`mid`,`G1`,`tn1`,`s`] >> BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qunabbrev_tac `baseQ` >> RULE_ASSUM_TAC BETA_RULE >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> (?tv. _) /\ _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `res = INL tv` SUBST_ALL_TAC >>
  rename1 `vv_post_mods _ _ _ _ _ obj _ _ _ _ mid raw bvv s` >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  `eval_expr cx obj (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL raw,mid)` by
    (qpat_assum `!tail. eval_expr cx obj (es with gas_obs := _ ++ tail) =
                         (_,mid with gas_obs := tail)` (qspec_then `[]` mp_tac) >>
     rewrite_tac[APPEND_NIL] >>
     qpat_assum `mid with gas_obs := [] = mid` (fn th => rewrite_tac[th])) >>
  `well_typed_expr env (Subscript (EL k tys) obj (Literal ity (IntL (&k))))` by
    (qpat_assum `expr_body_pre_mods _ _ _ _ (Subscript _ _ _) _`
       (mp_tac o MATCH_MP expr_body_pre_mods_well_typed) >> simp[]) >>
  `expr_body_pre_mods mods cenv cx env obj
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  `post_value_type cenv obj = TupleT tys` by simp[] >>
  drule_all_then strip_assume_tac
    (SIMP_RULE bool_ss [] (Q.INST [`idx` |-> `Literal ity (IntL (&k))`,
                                  `ann` |-> `EL k tys`] tuple_subscript_selected_source_mods)) >>
  rename1 `select_result _ _ _ _ _ = (INL raw',mid)` >>
  `bind (eval_expr cx obj) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL (ArrayV (TupleV vs)),mid)` by
    simp[bind_def] >>
  `expr_sim_inv_mods mods cenv cx env mid` by
    (drule_all_then strip_assume_tac (REWRITE_RULE [ETA_THM] expr_body_pre_eval_mods) >> simp[]) >>
  `vv_holds_mods cenv cx (TupleT tys) raw bvv mid s` by
    (qhdtm_assum `vv_post_mods` (mp_tac o REWRITE_RULE [vv_post_mods_def]) >> simp[]) >>
  drule_then strip_assume_tac attribute_read_operand_mods >>
  `ptr_vv_ok cx (TupleT tys) raw bvv mid G1 tn1 s` by fs[] >>
  `op_taint tn1 (vv_operand bvv) = {}` by
    (qpat_assum `ptr_vv_ok cx (TupleT tys) _ _ _ _ _ _` mp_tac >>
     Cases_on `bvv` >> simp[NoAsms,ptr_vv_ok_def,ptr_val_ok_def,vv_operand_def] >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  `!v. raw = Value v ==> vv_own cenv cx (TupleT tys) sa sm mid raw bvv s /\
                        vv_loc bvv = LocMemory` by
    (qpat_x_assum `!v. raw = Value v /\ _ ==> _` mp_tac >>
     simp[is_word_type_def,is_bytestring_type_def] >> strip_tac >>
     gen_tac >> disch_tac >> first_x_assum (drule_then strip_assume_tac) >>
     Cases_on `bvv` >> fs[vv_loc_def,vv_location_def]) >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[] >>
     qpat_assum `compile_expr cenv ty obj sa = _`
       (strip_assume_tac o MATCH_MP compile_expr_extends) >> simp[]) >>
  suspend "endpoint"
QED

Resume subscript_tuple_vv_sim_full_mods[endpoint]:
  qabbrev_tac `off = tuple_offset cenv tys (vv_loc bvv) k` >>
  qpat_x_assum `emit_op ADD _ sm = (p,sb)`
    (mp_tac o SIMP_RULE (srw_ss()) [literal_int_index_def]) >>
  qpat_assum `Abbrev (off = _)`
    (fn th => rewrite_tac[GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
  disch_tac >>
  qpat_assum `Abbrev (off = _)` (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_x_assum `gas_outcome_full_mods _ _ _ _ (eval_expr cx obj) _ _ _` kall_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H mid.storage_trace ==> (?tv. _) /\ _`
    (assume_tac o SIMP_RULE (srw_ss()) []) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
       vv_post_mods H ctx func cenv cx obj es sa sm s0 mid raw bvv s /\
       ghost_inv_at_mods (DF H) lo d cenv cx mid G1 tn1 s` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `H` (drule_then strip_assume_tac)) >> asm_rewrite_tac[]) >>
  drule_all_then (qspec_then `PG`
    (qx_choosel_then [`out`,`i`,`u`,`t`,`G2`,`tn2`] strip_assume_tac))
    tuple_subscript_add_endpoint_mods >>
  disj1_tac >> qexists_tac `raw` >> (conj_tac >- REFL_TAC) >>
  irule gas_outcome_full_mods_pure >> (reverse conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`G2`,`mid`,`INL raw'`,`t`,`tn2`] >> BETA_TAC >>
  (conj_tac >- (drule_then ACCEPT_TAC tuple_select_gas_obs)) >>
  gen_tac >> strip_tac >>
  (conj_tac >- (first_x_assum irule >>
     qpat_assum `ghost_inv_at_mods _ lo d cenv cx mid G1 tn1 s`
       (strip_assume_tac o REWRITE_RULE [ghost_inv_at_mods_def]) >>
     first_assum ACCEPT_TAC)) >>
  suspend "post"
QED

Resume subscript_tuple_vv_sim_full_mods[post]:
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> vv_post_mods _ _ _ _ _ _ _ _ sb _ _ _ _ t /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  qpat_assum `off = tuple_offset _ _ _ _` (fn eq =>
    qpat_assum `eval_operand p t = _` (assume_tac o REWRITE_RULE [eq])) >>
  qpat_assum `post_value_type cenv obj = TupleT tys` (fn eq =>
    map_every (fn pat => qpat_assum pat (assume_tac o REWRITE_RULE [eq]))
      [`vv_store_bound _ (post_value_type cenv obj) _ _ _ _ s`,
       `cenv.ce_is_ctor /\ vv_location bvv = SOME LocCode ==> _`]) >>
  qpat_assum `mid with gas_obs := [] = mid` (fn th => rewrite_tac[th]) >>
  qexists_tac `raw'` >> simp_tac (srw_ss()) [expr_type_def,mk_ptr_def,arithmeticTheory.ADD_COMM] >>
  irule (CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss())
      [LET_THM,expr_type_def,mk_ptr_def,arithmeticTheory.ADD_COMM]))
    (INST_TYPE [alpha |-> ``:256``] tuple_subscript_selected_post_mods)) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  goal_assum (drule_at (Pat `ptr_vv_ok _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `expr_sim_inv_mods _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `read_result _ raw _ = (INL (ArrayV (TupleV _)),_)`)) >>
  goal_assum (drule_at (Pat `OPT_MMAP _ _ = _`)) >>
  goal_assum (drule_at (Pat `p = Var _`)) >>
  goal_assum (drule_at (Pat `eval_operand (vv_operand bvv) s = _`)) >>
  qexists_tac `sm` >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qexists_tac `w` >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (gen_tac >> disch_tac >>
      qpat_assum `!x. not_fresh_at sm x ==> _ /\ _` (drule_then strip_assume_tac) >>
      first_assum ACCEPT_TAC)
  >> irule arithmeticTheory.LESS_IMP_LESS_OR_EQ >> first_assum ACCEPT_TAC
QED

Finalise subscript_tuple_vv_sim_full_mods

(* Force a linked Attribute result at the reached raw execution endpoint. *)
Theory bodyAttributeValueOfVVMods
Ancestors
  bodyAttributeWordUnwrapMods bodyAttributeNonwordUnwrapMods
  bodyFullPostsMods bodyFullShared exprSimUnwrap exprSimMemorySource
  gasShadowCompile gasShadowState gasOutcomeFullBindMods
  gasOutcomeFullPostMods gasExemptCertMods haltExitProj stmtSimProps
  vyperStorageTrace vyperStorageFootprint exprLowering compileEnv fragExec
  exprSimDefs loweringPosts vyperAST vyperState
Libs monadsyntax

Theorem attribute_unwrap_cut_mods[local]:
  lower_value compile_expr ce ty (Attribute ann obj fld) sa = (op,sb) /\
  lower_value compile_expr (gas_shadow_env T ce) ty
    (gas_shadow_expr (Attribute ann obj fld)) sha = (op,shb) /\
  gas_shadow_state sa sha /\ fn_has_code sa sb func /\
  fn_has_code sha shb shadow_func ==>
  ?vv sm shm.
    compile_expr ce ty (Attribute ann obj fld) sa = (vv,sm) /\
    compile_expr (gas_shadow_env T ce) ty
      (gas_shadow_expr (Attribute ann obj fld)) sha = (vv,shm) /\
    unwrap_value ce vv sm = (op,sb) /\ gas_shadow_state sm shm /\
    fn_has_code sa sm func /\ fn_has_code sm sb func /\
    fn_has_code sha shm shadow_func
Proof
  strip_tac >>
  qpat_x_assum `lower_value compile_expr ce ty (Attribute _ _ _) sa = _` mp_tac >>
  simp[lower_value_def, comp_bind_def] >>
  Cases_on `compile_expr ce ty (Attribute ann obj fld) sa` >>
  rename1 `_ = (vv,sm)` >> simp[] >> strip_tac >>
  qpat_x_assum `lower_value compile_expr _ _ (gas_shadow_expr _) _ = _` mp_tac >>
  simp[lower_value_def, comp_bind_def] >>
  Cases_on `compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr (Attribute ann obj fld)) sha` >>
  rename1 `_ = (vsh,shm)` >>
  simp[gasShadowCompileBaseTheory.unwrap_value_gas_shadow_env] >> strip_tac >>
  `gas_shadow_compiles (compile_expr ce ty (Attribute ann obj fld))
     (compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr (Attribute ann obj fld)))` by
    irule (cj 1 gas_shadow_compile_expr_env |> SPEC_ALL |>
           Q.INST [`shadow` |-> `T`] |> REWRITE_RULE [COND_CLAUSES]) >>
  drule_all_then strip_assume_tac gas_shadow_step >>
  qpat_x_assum `vsh = vv` SUBST_ALL_TAC >>
  qpat_assum `compile_expr ce ty (Attribute _ _ _) _ = _`
    (strip_assume_tac o MATCH_MP compile_expr_extends) >>
  qpat_assum `unwrap_value ce vv sm = _`
    (strip_assume_tac o MATCH_MP unwrap_value_extends) >>
  qpat_assum `compile_expr _ _ (gas_shadow_expr _) _ = _`
    (strip_assume_tac o MATCH_MP compile_expr_extends) >>
  qpat_assum `unwrap_value ce vv shm = _`
    (strip_assume_tac o MATCH_MP unwrap_value_extends) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
     (irule fn_has_code_split >> simp[]) >>
  `fn_has_code sha shm shadow_func /\ fn_has_code shm shb shadow_func` by
     (irule fn_has_code_split >> simp[]) >>
  asm_rewrite_tac[]
QED

Theorem attribute_value_of_vv_mods:
  expr_body_pre_mods mods ce cx env (Attribute ann obj fld) es /\
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx ty (Attribute ann obj fld) es ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx ty (Attribute ann obj fld) es
Proof
  strip_tac >> rewrite_tac[expr_sim_full_mods_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then (qx_choosel_then [`vv`,`sm`,`shm`] strip_assume_tac)
    attribute_unwrap_cut_mods >>
  drule_then assume_tac forced_expr_admissible_raw >>
  qpat_x_assum `expr_vv_sim_full_mods _ _ _ _ _ _`
    (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`shm`,`vv`,`s0`,`G0`,`tn0`] mp_tac o
     REWRITE_RULE [expr_vv_sim_full_mods_def]) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ childQ childR` >>
  irule gas_outcome_full_mods_bind_all >> BETA_TAC >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_result >>
      qexistsl_tac [`mid`,`t`,`v`] >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_result >> simp[])
  >~ [`storage_trace_frame (eval_expr _ _)`]
  >- simp[evaluate_storage_trace_frame]
  >~ [`!v. storage_trace_frame (read_result _ v)`]
  >- simp[storage_trace_frame_read_result] >>
  qexists_tac `\H res ee G tn u. childQ H res ee G tn u /\ ee.gas_obs = [] /\ ~u.vs_halted` >>
  reverse conj_tac
  >- (irule gas_outcome_full_mods_post_source >>
      qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ childQ childR` (irule_at Any) >>
      conj_tac >- simp[] >>
      rpt gen_tac >> Cases_on `res` >> simp[Abbr `childR`,expr_exit_def] >>
      ONCE_REWRITE_TAC [INST_TYPE [beta |-> ``:value``] expr_exit_INR_type,
        INST_TYPE [beta |-> ``:value``] halt_exit_INR_type] >> simp[]) >>
  suspend "read"
QED

Resume attribute_value_of_vv_mods[read]:
  qx_genl_tac [`marks`,`res`,`ee`,`G`,`tn`,`s`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qunabbrev_tac `childQ` >>
  qpat_x_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (assume_tac o BETA_RULE) >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `res = INL tv` SUBST_ALL_TAC >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  `eval_expr cx (Attribute ann obj fld) (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL tv,ee)` by
    (qpat_assum `!tail. eval_expr _ _ _ = _`
       (qspec_then `[]` (mp_tac o REWRITE_RULE [listTheory.APPEND_NIL])) >>
     asm_rewrite_tac[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func ce cx (Attribute ann obj fld) es sa sm s0 ee tv vv s /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G tn s` by
    (qx_gen_tac `H` >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> (?r. _ = INL r /\ _) /\ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  disj1_tac >> qexists_tac `tv` >> simp[] >>
  rule_assum_tac (REWRITE_RULE [post_value_type_def,expr_type_def,lowered_value_type_def]) >>
  Cases_on `is_word_type ann`
  >- suspend "word" >>
  suspend "nonword"
QED

Resume attribute_value_of_vv_mods[word]:
  drule_all_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`] mp_tac)
    attribute_word_unwrap_endpoint_mods >>
  disch_then (qx_choosel_then [`v`,`u`,`Gf`,`tf`] strip_assume_tac) >>
  irule gas_outcome_full_mods_pure >> simp[] >>
  qexistsl [`Gf`,`ee`,`INL v`,`u`,`tf`] >> simp[read_result_gas_obs] >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >> simp[expr_type_def]
QED

Resume attribute_value_of_vv_mods[nonword]:
  `!tag x. vv = StackValue tag x ==> ptr_buf_ok ce (Attribute ann obj fld) x G s` by
    simp[] >>
  drule_all_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`] mp_tac)
    (SIMP_RULE (srw_ss()) [expr_type_def,lowered_value_type_def]
      (Q.INST [`k` |-> `sm`] (SPEC_ALL attribute_nonword_unwrap_endpoint_mods))) >>
  disch_then (qx_choosel_then [`v`,`u`,`Gf`,`tf`,`pt`,`rt`,`w`]
    (map_every assume_tac o CONJUNCTS)) >>
  `s0.vs_alloca_next <= u.vs_alloca_next` by decide_tac >>
  irule gas_outcome_full_mods_pure >> simp[] >>
  qexistsl [`Gf`,`ee`,`INL v`,`u`,`tf`] >> simp[read_result_gas_obs] >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >> simp[expr_type_def]
QED

Finalise attribute_value_of_vv_mods

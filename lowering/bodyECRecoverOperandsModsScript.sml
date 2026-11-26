(* Bind the linked ECRecover operand run to its reached suffix. *)
Theory bodyECRecoverOperandsMods
Ancestors
  bodyECRecoverOperandListMods bodyECRecoverSuffixMods
  bodyECRecoverOperandReadyMods bodyECRecoverOperandCodeMods
  bodyFullPredsMods bodyFullPostsMods bodyFullShadowBodyInv
  exprSimFullBundleProps exprSimPrecompiles exprLoweringProps
  compileEnv gasShadowState gasShadow
  vyperStorageTrace vyperStorageFootprint vyperInterpreter vyperState
  vyperAST vyperContext list finite_map
  exprBodyPreProps gasOutcomeFullBindMods gasOutcomeFullPostMods gasExemptCertMods
  exprSimWordArgs exprSimDefs loweringPosts bodyMemoryDefs vyperEvalExprPreservesScopesDom
Libs monadsyntax

Theorem ecrecover_from_suffix_mods:
  (builtin_args_length_ok ECRecover (LENGTH args) ==>
     body_exprs_full_ok_mods mods exps cx args) /\
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods cenv cx env (Builtin ann ECRecover args) es /\
  (!DF lo d ctx shadow_ctx PG func shadow_func cenv cx ty e es.
     is_word_type (post_value_type cenv e) /\
     expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
       cenv cx ty e es /\
     (!sa. ?t op sb. compile_expr cenv ty e sa = (StackValue t op,sb)) /\
     (!s tv s'. eval_expr cx e s = (INL tv,s') ==> ?v. tv = Value v) ==>
     expr_vv_sim_full_mods
       (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es) ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Builtin ann ECRecover args) es /\
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Builtin ann ECRecover args) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac ecrecover_operand_ready_mods >>
  conj_asm1_tac
  >- suspend "forced"
  >> suspend "vv"
QED

Resume ecrecover_from_suffix_mods[forced]:
  pure_rewrite_tac[expr_sim_full_mods_def] >> rpt gen_tac >> strip_tac >>
  `expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,sb,shadow_sa,shadow_sb)` by
    simp[expr_sim_full_code_def] >>
  drule_all_then strip_assume_tac ecrecover_operand_code_mods >>
  `expr_sim_inv_mods mods cenv cx env es` by (drule expr_body_pre_mods_inv >> simp[]) >>
  `body_exprs_full_ok_mods mods exps cx args` by simp[builtin_args_length_ok_def] >>
  `!e st. MEM e args /\ expr_sim_inv_mods mods cenv cx env st ==>
           expr_body_pre_mods mods cenv cx env e st` by simp[] >>
  `!e. MEM e args ==> is_word_type (expr_type e) /\
          ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv` by simp[] >>
  drule_all_then assume_tac ecrecover_operand_admissible_mods >>
  drule_all_then (qspec_then `PG` (assume_tac o BETA_RULE)) ecrecover_operand_list_run_mods >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ (eval_exprs _ _) _ listQ listR` >>
  qpat_x_assum `ann = BaseT AddressT` SUBST_ALL_TAC >>
  simp[Once eval_expr_ecrecover_read_action] >>
  irule gas_outcome_full_mods_bind_all >> BETA_TAC >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_values >>
      goal_assum (drule_at Any) >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_values >> simp[])
  >~ [`storage_trace_frame (eval_exprs _ _)`]
  >- simp[evaluate_storage_trace_frame]
  >~ [`storage_trace_frame _`]
  >- (qx_gen_tac `vs` >>
      `!(w:value). storage_trace_frame
         (do precompile_call_success ECRecover vs; return w od)` by
        simp[storage_trace_frame_ignore_bind, storage_trace_frame_return,
             storage_trace_frame_precompile_call_success] >>
      simp[storage_trace_frame_def] >> rpt gen_tac >>
      Cases_on `builtin_result cx st.accounts (BaseT AddressT) ECRecover (MAP expr_type args) vs` >>
      simp[] >>
      qpat_assum `!w. storage_trace_frame _` (qspec_then `x` mp_tac) >>
      disch_then (mp_tac o Q.SPECL [`st`,`observations`] o
                  PURE_ONCE_REWRITE_RULE [storage_trace_frame_def]) >> simp[])
  >> qexists_tac `\H res ee G tn t. listQ H res ee G tn t /\ ~t.vs_halted` >>
  reverse conj_tac
  >- (irule gas_outcome_full_mods_post_source >>
      qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ listQ listR` (irule_at Any) >>
      reverse conj_tac
      >- (simp[Abbr `listR`, wb_args_exit_def] >> rpt gen_tac >> Cases_on `res` >>
          simp[halt_exit_def]) >> simp[]) >>
  suspend "suffix"
QED

Resume ecrecover_from_suffix_mods[suffix]:
  qx_genl_tac [`marks`,`res`,`mid`,`G1`,`tn1`,`t`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qunabbrev_tac `listQ` >> RULE_ASSUM_TAC BETA_RULE >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _` (drule_then strip_assume_tac) >>
  qpat_x_assum `res = INL _` SUBST_ALL_TAC >>
  disj1_tac >> qexists_tac `vs` >> simp[] >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (qpat_assum `!tail. eval_exprs _ _ _ = _`
       (qspec_then `[]` (mp_then (Pat `eval_exprs _ _ _ = _`) mp_tac eval_exprs_preserves_scopes_dom)) >>
     simp[]) >>
  `return_buf_frame d cenv sf t` by
    (irule return_buf_frame_frame >> qpat_assum `return_buf_frame _ _ sa s0` (irule_at Any) >>
     fs[typed_args_post_def, wb_frame_def, ci_mono_def]) >>
  irule (REWRITE_RULE [post_value_type_def] (BETA_RULE ecrecover_suffix_mods)) >>
  qpat_assum `compile_ecrecover _ _ _ _ sf = _` (irule_at Any) >>
  qpat_assum `compile_ecrecover _ _ _ _ shadow_sf = _` (irule_at Any) >>
  qpat_assum `expr_sim_full_code _ (sf,sb,shadow_sf,shadow_sb)` (irule_at Any) >>
  qexists_tac `marks` >> simp[] >> conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
        (drule_then (mp_tac o SIMP_RULE (srw_ss()) [])) >> simp[]) >>
  qpat_assum `EVERY (\x. op_prov G1 x = NONE /\ _) _` mp_tac >>
  qpat_assum `EVERY (\x. (!l. x <> Label l) /\ _) _` mp_tac >> simp[NoAsms]
QED

Resume ecrecover_from_suffix_mods[vv]:
  qpat_x_assum `ann = BaseT AddressT` SUBST_ALL_TAC >>
  first_x_assum irule >>
  simp[post_value_type_def, vyperASTTheory.expr_type_def, is_word_type_def] >>
  conj_tac
  >- (qx_gen_tac `sa` >> Cases_on `compile_expr cenv ty (Builtin (BaseT AddressT) ECRecover args) sa` >>
      drule_all_then strip_assume_tac compile_ecrecover_stack >> simp[]) >>
  rpt strip_tac >> drule eval_expr_builtin_value >> simp[]
QED

Finalise ecrecover_from_suffix_mods

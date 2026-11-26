(* Linked value simulation for the flag arm of ordinary membership. *)
Theory bodyMembershipFlagValueMods
Ancestors
  bodyMembershipFlagLayoutMods bodyMembershipFlagOperandsMods
  bodyMembershipFlagResultMods bodyMembershipOperandEntryMods
  bodyBopBytestringBindMods bodyFullPredsMods bodyFullPostsMods
  exprSimFullBundleProps exprBodyPreProps exprWordOperand exprSimSource
  vyperTypeEvalCaseProofs vyperTypeExprSoundness stmtSimDefs
  gasOutcomeFullMods gasContext vyperState freshWrites compileEnv vyperTypeSystem
Libs monadsyntax

Triviality flag_operand_sim:
  body_expr_full_ok_mods mods exps cx e /\
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods cenv cx env e es ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es
Proof
  strip_tac >>
  qpat_x_assum `body_expr_full_ok_mods _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es /\
   expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es` by
    (qpat_assum `!DF lo d PG src tops ctx shctx func shfunc cenv env ty es.
      _ ==> expr_sim_full_mods _ _ _ _ _ _ /\ expr_vv_sim_full_mods _ _ _ _ _ _` irule >>
     simp[] >> conj_tac >- (qexistsl_tac [`src`,`tops`] >> simp[]) >>
     qexists_tac `env` >> simp[]) >>
  first_assum ACCEPT_TAC
QED

Triviality flag_left_not_label:
  expr_body_pre_mods mods cenv cx env e es /\ is_word_type (expr_type e) /\
  lower_value compile_expr cenv ty e sa = (x,s1) ==> !l. x <> Label l
Proof
  strip_tac >> drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule_then (assume_tac o MATCH_MP expr_sim_inv_mods_env) expr_body_pre_mods_inv >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  `!id ty. FLOOKUP env.var_types id = SOME ty ==> well_formed_type env.type_defs ty` by
    (simp[well_formed_type_def] >> rpt strip_tac >>
     drule_all env_consistent_var_type_evaluates >> simp[]) >>
  drule_all lower_value_word_shape >> simp[]
QED

Theorem membership_flag_value_mods:
  (bop = In \/ bop = NotIn) /\
  expr_type e1 = FlagT fid /\ expr_type e2 = FlagT fid /\
  ann = BaseT BoolT /\ well_typed_binop ann bop (expr_type e1) (expr_type e2) /\
  body_exprs_full_ok_mods mods exps cx [e1;e2] /\
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods cenv cx env (Builtin ann (Bop bop) [e1;e2]) es ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Builtin ann (Bop bop) [e1;e2]) es
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rewrite_tac[expr_sim_full_mods_def] >>
  qx_genl_tac [`st0`,`sa`,`sb`,`shadow_sa`,`shadow_sb`,`op`,`s0`,`G0`,`tn0`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then (strip_assume_tac o Q.SPEC `st0`) membership_operand_entry_mods >>
  drule_then (assume_tac o MATCH_MP expr_sim_inv_mods_env) expr_body_pre_mods_inv >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  `is_word_type (expr_type e1) /\ is_word_type (expr_type e2)` by
    simp[is_word_type_def, is_flag_type_def] >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (expr_type e1) e1 es` by
    (irule flag_operand_sim >>
     qpat_assum `module_body_inv _ _ _ _ _` (irule_at Any) >>
     qpat_assum `body_const_cells_agree_mods _ _ _ es` (irule_at Any) >>
     qexists_tac `exps` >> simp[]) >>
  drule_all_then strip_assume_tac membership_flag_layout_mods >>
  drule_all_then assume_tac flag_left_not_label >>
  qpat_x_assum `local_ptrs_reserved cenv sa ==> _ /\ _`
    (drule_then strip_assume_tac) >>
  irule (BETA_RULE membership_flag_operands_mods) >>
  qpat_assum `lower_value compile_expr cenv _ e1 sa = _` (irule_at Any) >>
  qpat_assum `lower_value compile_expr cenv _ e2 s1 = _` (irule_at Any) >>
  qpat_assum `contract_inv _ _ _ _ _` (irule_at Any) >>
  qpat_assum `lower_value _ _ _ (gas_shadow_expr e1) _ = _` (irule_at Any) >>
  qpat_assum `lower_value _ _ _ (gas_shadow_expr e2) _ = _` (irule_at Any) >>
  qpat_assum `expr_sim_full_mods _ _ _ _ e1 _` (irule_at Any) >>
  BETA_TAC >>
  qpat_x_assum `expr_type e1 = FlagT fid` (fn eq1 =>
    qpat_x_assum `expr_type e2 = FlagT fid` (fn eq2 =>
      qpat_x_assum `ann = BaseT BoolT` (fn ae =>
        asm_rewrite_tac[expr_sim_full_code_def] >> map_every assume_tac [eq1,eq2,ae]))) >>
  conj_tac >- suspend "suffix" >> suspend "right_entry"
QED

Resume membership_flag_value_mods[right_entry]:
  qx_genl_tac [`left`,`v1`,`mid`,`G1`,`tn1`,`t`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!obs needle mid. _ ==> body_expr_full_ok_mods _ _ _ e2 /\ _`
    (qspecl_then [`gas_explicit left s0.vs_gas_readings`,`v1`,`mid`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  irule flag_operand_sim >>
  qpat_assum `module_body_inv _ _ _ _ _` (irule_at Any) >>
  qpat_assum `body_const_cells_agree_mods _ _ _ mid` (irule_at Any) >>
  qexists_tac `exps` >> simp[]
QED

Resume membership_flag_value_mods[suffix]:
  qx_genl_tac [`left`,`v1`,`mid`,`G1`,`tn1`,`t`,`right`,`v2`,`fin`,`G2`,`tn2`,`u`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!obs needle mid. _ ==> body_expr_full_ok_mods _ _ _ e2 /\ _`
    (qspecl_then [`gas_explicit left s0.vs_gas_readings`,`v1`,`mid`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  drule_all_then (strip_assume_tac o Q.SPEC `st0`) bop_bytestring_operand_source_mods >>
  drule_then (assume_tac o SYM o SRULE []) eval_read_preserves_scopes_dom >>
  `?tv. evaluate_type (get_tenv cx) (FlagT fid) = SOME tv /\
        value_has_type tv v1 /\ value_has_type tv v2` by
    (qpat_assum `value_runtime_typed env (expr_type e1) v1`
       (qx_choose_then `tv1` strip_assume_tac o REWRITE_RULE [value_runtime_typed_def]) >>
     qpat_assum `value_runtime_typed env (expr_type e2) v2`
       (qx_choose_then `tv2` strip_assume_tac o REWRITE_RULE [value_runtime_typed_def]) >>
     qpat_assum `evaluate_type _ (expr_type e1) = SOME tv1` mp_tac >>
     qpat_assum `evaluate_type _ (expr_type e2) = SOME tv2` mp_tac >>
     qpat_assum `env.type_defs = get_tenv cx` (fn tenv =>
       qpat_assum `expr_type e1 = FlagT fid` (fn eq1 =>
         qpat_assum `expr_type e2 = FlagT fid` (fn eq2 =>
           pure_rewrite_tac[tenv,eq1,eq2]))) >>
     Cases_on `evaluate_type (get_tenv cx) (FlagT fid)` >> simp[] >>
     rpt strip_tac >> qpat_x_assum `tv2 = tv1` SUBST_ALL_TAC >>
     first_assum ACCEPT_TAC) >>
  irule membership_flag_result_mods >>
  qpat_assum `compile_binop _ _ _ _ _ _ s2 = _` (irule_at Any) >>
  qpat_assum `evaluate_type _ (FlagT fid) = SOME tv` (irule_at Any) >>
  qexistsl_tac [`tn1`,`t`,`s1`,`right`,`mid`,`left`,`G1`] >>
  asm_rewrite_tac[] >>
  rpt conj_tac >> gen_tac >> disch_tac >>
  (qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==>
       expr_post_mods H _ _ _ _ e2 _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) ORELSE
   qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
       expr_post_mods H _ _ _ _ e1 _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) ORELSE
   qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==>
       stmt_state_rel H _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac)) >> asm_rewrite_tac[]
QED

Finalise membership_flag_value_mods

(* Source typing and forced-key facts at the reached Value-array cut. *)
Theory bodyArrayOwnedSourceKeyMods
Ancestors
  bodyArrayNoCopyCutsMods bodyArrayNoCopySourceMods bodySubscriptArrayRouteDefsMods
  bodyFullPostsMods bodySimStmtFacts bodyAssignNameLinkedSetup bodyPtrDefs
  exprSimSource exprSimArith exprSimSubscriptArrayOrigin
  exprBodyPreProps exprSimHypsDefs exprReasonOperand exprOperandVar exprLowering
  arithmeticProps typedMemoryCopy valueEncoding compileEnv context loweringPosts
  vyperTypeExprSoundness vyperTypeExprResult vyperTypeInvariants
  vyperTypeValues vyperTypeEvalCaseProofs vyperTypeConstantFold
  vyperTypeEvalSoundness vyperEvalOutcomeSuffix vyperStorageFootprint
  vyperTypeSystem vyperTyping vyperValue vyperInterpreter vyperState vyperAST

Theorem array_owned_raw_eval_sound_mods[local]:
  expr_sim_inv_mods mods cenv cx env es /\ well_typed_expr env e0 /\
  call_evaluation_safe cx (int_calls_expr e0) /\
  eval_expr cx e0 es = (res,ee) ==>
  expr_sim_inv_mods mods cenv cx env ee /\ no_type_error_result res /\
  (case res of INL raw => eval_result_typed (env,cx,ee) raw (Type (expr_type e0))
             | INR _ => T)
Proof
  strip_tac >>
  `IS_SOME ee.outcomes` by
    (irule eval_expr_outcomes_some >> fs[expr_sim_inv_mods_def] >> metis_tac[]) >>
  qpat_x_assum `expr_sim_inv_mods _ _ _ _ _` mp_tac >>
  simp[expr_sim_inv_mods_def] >> strip_tac >>
  drule_all_then assume_tac eval_expr_popped_keys_indexed >>
  qspecl_then [`cx`,`e0`] (mp_tac o CONJUNCT1)
    (cj 5 eval_scc_type_sound_mutual) >>
  disch_then (qspecl_then [`env`,`es`,`res`,`ee`] mp_tac) >>
  simp[] >> strip_tac >>
  `outcomes_accounts_typed ee.outcomes` by
    (rw[outcomes_accounts_typed_def] >>
     drule (cj 5 eval_outcome_suffix_mutual) >> strip_tac >>
     drule_then irule outcome_suffix_EVERY >> fs[outcomes_accounts_typed_def]) >>
  simp[] >> conj_tac >> first_assum ACCEPT_TAC
QED

Theorem owned_index_word_mods[local]:
  is_int_type (expr_type idx) /\
  evaluate_type (get_tenv cx) (expr_type idx) = SOME tv /\ value_has_type tv key /\
  expr_post_mods H ctx func cenv cx idx mid sm st2 s fin key iop it ==>
  ?iw. eval_operand iop it = SOME iw /\
       key = IntV (if is_signed_type (expr_type idx) then w2i iw else &(w2n iw))
Proof
  strip_tac >> qspec_then `expr_type idx` mp_tac math_val_i2w >>
  Cases_on `expr_type idx` >> gvs[is_int_type_def] >>
  rename1 `is_int_type (BaseT bt)` >> Cases_on `bt` >>
  gvs[is_int_type_def, evaluate_type_def, AllCaseEqs(), well_formed_type_def] >>
  Cases_on `key` >>
  gvs[value_has_type_def, expr_post_mods_def, expr_post_def, expr_val_rel_def,
      is_word_type_def,
      evaluate_type_def, typed_val_to_w256_def, val_to_w256_def, AllCaseEqs(),
      math_val_def, is_signed_type_def, type_bits_def, within_int_bound_def] >>
  disch_then (qspec_then `i` mp_tac) >> simp[]
QED

Theorem owned_base_operand_mods[local]:
  compile_expr cenv ty obj sa = (bvv,sm) /\
  expr_type obj = ArrayT et bd /\ well_typed_expr env obj /\
  expr_sim_inv_mods mods cenv cx env es /\
  (!t p. bvv = LocatedValue t p ==> p.ptr_location = LocMemory) ==>
  !l. vv_operand bvv <> Label l
Proof
  strip_tac >>
  `!id t. FLOOKUP env.var_types id = SOME t ==>
          ?q sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var q) sz)` by
    fs[expr_sim_inv_mods_def] >>
  Cases_on `bvv` >> gvs[vv_operand_def]
  >- (rename1 `compile_expr cenv ty obj sa = (StackValue _ bop,sm)` >>
      `lower_value compile_expr cenv ty obj sa = (bop,sm)` by
        simp[lower_value_def, unwrap_value_def, comp_return_def, comp_bind_def] >>
      drule_all lower_compile_expr_not_label >> simp[]) >>
  irule compile_array_pointer_not_label >> simp[] >>
  goal_assum (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `expr_type _ = ArrayT _ _`)) >>
  qexists `env` >> simp[]
QED

Theorem array_owned_source_key_mods:
  linked_subscript_array_context_mods mods exps cx ann obj idx
    DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es et bd /\
  ~subscript_reads_base cx obj idx /\
  array_nocopy_cut_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty obj idx et bd st0
    (es,s0,G0,tn0) (sa,sm,st2,sb,bvv,iop,dst,loc)
    (shadow_sa,shadow_sm,shadow_st2,shadow_sb)
    (gs1,mid,raw,s,G1,tn1) (gs2,fin,key,it,Gi,tni) /\
  raw = Value v ==>
  ?etv i iw.
    ann = et /\
    evaluate_type (get_tenv cx) et = SOME etv /\
    evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
    value_has_type (ArrayTV etv bd) v /\
    type_memory_bytes cenv et = type_memory_size etv /\
    key = IntV i /\
    eval_operand iop it = SOME iw /\
    i = (if is_signed_type (expr_type idx) then w2i iw else &(w2n iw)) /\
    op_taint tni iop = {} /\
    op_prov Gi iop = NONE /\
    (!l. vv_operand bvv <> Label l) /\
    (!x. vv_operand bvv = Var x ==> not_fresh_at sm x) /\
    (!x. iop = Var x ==> not_fresh_at st2 x) /\
    (case bd of Fixed n => n | Dynamic n => n) < dimword (:256)
Proof
  strip_tac >>
  qhdtm_assum `array_nocopy_cut_mods`
    (strip_assume_tac o REWRITE_RULE [array_nocopy_cut_mods_def]) >>
  drule_all_then strip_assume_tac array_nocopy_base_inputs_mods >>
  drule_all_then strip_assume_tac array_nocopy_index_inputs_mods >>
  `valid_horizon cx st0 (storage_trace_horizon fin.storage_trace) fin.storage_trace` by
    fs[storage_trace_domain_def] >>
  drule_all_then strip_assume_tac array_nocopy_cut_posts_mods >>
  `expr_sim_inv_mods mods cenv cx env (es with gas_obs := gs1)` by simp[] >>
  drule_all_then
    (strip_assume_tac o BETA_RULE o REWRITE_RULE [sumTheory.sum_case_def])
    array_owned_raw_eval_sound_mods >>
  qhdtm_x_assum `linked_subscript_array_context_mods`
    (strip_assume_tac o REWRITE_RULE [linked_subscript_array_context_mods_def]) >>
  `ann = et /\ is_int_type (expr_type idx)` by
    (qpat_assum `expr_body_pre_mods _ _ _ _ (Subscript _ _ _) _`
       (mp_then Any assume_tac expr_body_pre_mods_well_typed) >>
     drule_all constant_subscript_type_ok >> simp[subscript_type_ok_def]) >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  `expr_body_pre_mods mods cenv cx env idx (mid with gas_obs := gs2)` by simp[] >>
  `?tv. evaluate_type (get_tenv cx) (expr_type idx) = SOME tv /\
        value_has_type tv key` by
    (drule_all_then strip_assume_tac (REWRITE_RULE [ETA_AX] expr_body_pre_eval_mods) >>
     fs[value_runtime_typed_def] >> qexists `tv` >>
     qpat_assum `env.type_defs = get_tenv cx` (SUBST1_TAC o SYM) >> simp[]) >>
  `is_word_type (expr_type idx)` by
    (qpat_x_assum `is_int_type (expr_type idx)` mp_tac >>
     Cases_on `expr_type idx` >> simp[is_int_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> simp[is_int_type_def, is_word_type_def]) >>
  drule_all_then strip_assume_tac owned_index_word_mods >>
  `op_taint tni iop = {} /\ op_prov Gi iop = NONE` by
    (qpat_x_assum `ptr_val_ok _ _ _ _ _ _ _` mp_tac >> simp[ptr_val_ok_def]) >>
  `!x. vv_operand bvv = Var x ==> not_fresh_at sm x` by
    (qpat_assum `compile_expr cenv ty obj sa = _`
       (mp_then Any mp_tac (cj 1 compiler_compile_var)) >> simp[]) >>
  `!x. iop = Var x ==> not_fresh_at st2 x` by
    (qpat_assum `lower_value compile_expr cenv ty idx sm = _`
       (mp_then Any mp_tac compile_lower_value_var) >> simp[]) >>
  `!t p. bvv = LocatedValue t p ==> p.ptr_location = LocMemory` by
    (qpat_x_assum `!v. raw = Value v /\ _ ==> _` (qspec_then `v` mp_tac) >>
     simp[is_word_type_def, is_bytestring_type_def]) >>
  drule_all_then assume_tac owned_base_operand_mods >>
  `?tv. evaluate_type (get_tenv cx) (ArrayT et bd) = SOME tv /\ value_has_type tv v` by
    (qpat_x_assum `eval_result_typed _ raw _` mp_tac >>
     simp[eval_result_typed_def]) >>
  drule_then strip_assume_tac evaluate_type_ArrayT_cases >>
  `type_memory_bytes cenv et = type_memory_size elem_tv` by
    (irule assign_name_memory_bytes_mods >> simp[] >>
     goal_assum (drule_at (Pat `expr_sim_inv_mods _ _ _ _ _`)) >> simp[]) >>
  `bound_length bd < dimword (:256)` by
    (irule typed_copy_array_count_bound >> goal_assum (drule_at Any)) >>
  Cases_on `bd` >> gvs[]
QED

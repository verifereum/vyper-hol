Theory bodyForRangePtr
Ancestors forPtrRangeLiteral forPtrRangeDynamic bodyPtrPreds
  bodySimDeclCases bodySimStmtCases bodyExprPreFacts exprSimSource
  exprSimHyps supportedStmts supportedExprs supportedStmtTraverse
  supportedExprTraverse stmtSimFor stmtSimProps exprSimProps
  vyperTypeSystem vyperTypeCallStackSoundness
  vyperTyping vyperValueOperation integer_word exprSimHypsDefs
  vyperAST vyperTypeExprSoundness vyperTypeValues vyperTypeEvalSoundness
  allocLimits stmtLoweringMono vyperTypeInvariants
  vyperInterpreter vyperState vyperValue vyperTypeCallGraph
  finite_map list bodySim stmtSimForRange stmtSimForParts
  exprSimWordArgs loweringPosts stmtLowering compileEnv stmtSimReturn compileVyper
  fragExec bodyPtrDefs gasContext vyperABI
Libs monadsyntax intLib

val _ = Parse.hide "body";

Theorem body_for_range_lit_ptr:
  (!tenv s'' tyv t s3 vs t' s4 x t''.
     tenv = get_tenv cx /\
     lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' = (INL tyv,t) /\
     eval_iterator cx (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) s3 =
       (INL vs,t') /\
     check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s4 = (INL x,t'') ==>
     body_for_ptr_ok cx tyv id body vs) ==>
  body_stmt_ptr_ok cx
    (For id typ (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) n body)
Proof
  strip_tac >> rewrite_tac[body_stmt_ptr_ok_def] >> rpt gen_tac >> strip_tac >>
  `FLOOKUP cenv.ce_vars id = NONE` by
    (irule declared_name_unbound >> metis_tac[]) >>
  `id NOTIN FDOM env.var_types /\ is_int_type typ /\
   well_typed_literal typ (IntL n1) /\ well_typed_literal typ (IntL n2) /\
   well_formed_type env.type_defs typ /\
   ?env_b. type_stmts (extend_local env id typ F) ret_ty body = SOME env_b` by
    gvs[type_stmt_def, well_typed_iterator_def, well_typed_expr_def,
        expr_type_def, optionTheory.IS_SOME_EXISTS, AllCaseEqs()] >>
  `n1 <= n2 /\ n = Num (n2 - n1) /\ supported_stmts tops bindings body` by
    gvs[supported_stmt_def, supported_iterator_def] >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `?tyv. evaluate_type (get_tenv cx) typ = SOME tyv` by
    gvs[well_formed_type_def, optionTheory.IS_SOME_EXISTS] >>
  `!k. well_typed_literal typ (IntL k) ==> value_has_type tyv (IntV k)` by
    (rpt strip_tac >> drule_all well_typed_literal_sound >>
     simp[vyperValueOperationTheory.evaluate_literal_def]) >>
  suspend "facts"
QED

Resume body_for_range_lit_ptr[facts]:
  `GENLIST (\j. IntV (n1 + &j)) (Num (n2 - n1)) <> [] ==>
   body_stmts_ptr_ok cx body` by
    (strip_tac >>
     qpat_x_assum `!tenv s'' tyv t s3 vs t' s4 x t''. _`
       (qspecl_then [`get_tenv cx`, `es`, `tyv`, `es`, `es`,
         `GENLIST (\j. IntV (n1 + &j)) (Num (n2 - n1))`, `es`, `es`, `()`, `es`] mp_tac) >>
     simp[lift_option_type_def, return_def, eval_iterator_range_lit,
          check_def, assert_def, compatible_bound_def, body_for_ptr_ok_def]) >>
  `Num (n2 - n1) < dimword (:256)` by metis_tac[range_end_words] >>
  `cenv.ce_alloca_locals` by fs[body_inv_def] >>
  `lookup_scopes id es.scopes = NONE` by
    (Cases_on `lookup_scopes id es.scopes` >> simp[] >>
     gvs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def] >>
     res_tac >> gvs[FLOOKUP_DEF]) >>
  `is_word_type typ` by
    (Cases_on `typ` >> gvs[is_int_type_def, is_word_type_def] >>
     rename1 `is_int_type (BaseT bt)` >> Cases_on `bt` >>
     gvs[is_int_type_def, is_word_type_def]) >>
  drule_all word_type_sizes >> disch_then (qspec_then `cenv` strip_assume_tac) >>
  `call_evaluation_safe cx (int_calls_stmts body)` by
    (fs[int_calls_stmt_def] >> metis_tac[call_evaluation_safe_append_right]) >>
  `EVERY (stmt_exprs_ok cenv) body /\ type_memory_bytes cenv typ < 2 ** 64` by
    fs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
       stmts_exprs_ok_EVERY, alloc_limits_stmt_def, stmt_valued_return_def] >>
  match_mp_tac (BETA_RULE (Q.SPECL [`d`, `PG`, `\ei. expr_sim_inv cenv cx env ei`]
    compile_for_range_frag_ptr)) >>
  qexistsl_tac [`n1`, `n2`, `tyv`] >>
  simp[eval_expr_int_lit, lower_value_int_lit, wordsTheory.dimword_def] >>
  rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule (SIMP_RULE std_ss [cs_mono_def] (cj 2 compile_stmt_cs_mono)) >> simp[])
  >- suspend "body"
  >> suspend "pop"
QED

Resume body_for_range_lit_ptr[body]:
  rpt strip_tac >>
  `body_stmts_ptr_ok cx body` by
    (first_x_assum irule >> simp[listTheory.GENLIST_EQ_NIL] >>
     strip_tac >> gvs[]) >>
  `same_frame cenv c` by
    (drule_then irule declare_local_same_frame >> simp[]) >>
  `value_has_type tyv (IntV (n1 + &j))` by
    (irule range_value_has_type >> simp[] >> qexists_tac `n2` >> simp[]) >>
  `body_inv tops ctx c cx` by metis_tac[body_inv_same_frame] >>
  `!target. supported_stmts_expr_exists
      (expr_abi_decode_target_root target) body ==>
      occurs_abi_decode_target target tops` by
    (qpat_x_assum `!target. _` mp_tac >> simp[supported_stmt_expr_exists_def]) >>
  qpat_x_assum `body_stmts_ptr_ok _ _`
    (irule o REWRITE_RULE [body_stmts_ptr_ok_def]) >>
  simp[] >> rpt conj_tac
  >- metis_tac[stmt_exprs_ok_same_frame]
  >- (qexistsl_tac [`bindings`, `tops`] >> simp[])
  >- (qexistsl_tac [`extend_local env id typ F`, `env_b`] >> simp[] >>
      `c.ce_struct_fields = cenv.ce_struct_fields` by
        metis_tac[same_frame_struct_fields] >>
      conj_tac >- (irule ce_locals_declared_declare_local >> metis_tac[]) >>
      conj_tac >- (irule locals_alloc_ok_extend >> qexists_tac `cenv` >> simp[]) >>
      irule (SRULE [] (Q.INST [`es` |-> `ei with gas_obs := []`]
        (SPEC_ALL expr_sim_inv_for_scope))) >> simp[] >> metis_tac[]) >>
  fs[frame_ret_ok_ptr_def] >> rpt strip_tac >>
  first_x_assum irule >> simp[] >> metis_tac[same_frame_trans]
QED

Resume body_for_range_lit_ptr[pop]:
  rpt strip_tac >>
  `value_has_type tyv (IntV (n1 + &j))` by
    (irule range_value_has_type >> simp[] >> qexists_tac `n2` >> simp[]) >>
  `expr_sim_inv cenv cx env (ei with gas_obs := gs)` by simp[] >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    fs[body_inv_def] >>
  drule_at (Pat `eval_stmts`)
    (SRULE [] (Q.INST [`es` |-> `ei with gas_obs := gs`]
      (SPEC_ALL expr_sim_inv_for_pop))) >>
  disch_then irule >> simp[] >>
  conj_tac >- (qexistsl_tac [`env_b`, `typ`, `ret_ty`] >> simp[]) >>
  metis_tac[]
QED

Finalise body_for_range_lit_ptr

Theorem body_for_range_active_ptr[local]:
  (!tenv s'' tv t s3 vs t' s4 x t''.
     tenv = get_tenv cx /\
     lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' = (INL tv,t) /\
     eval_iterator cx (Range e1 e2) s3 = (INL vs,t') /\
     check (compatible_bound (Dynamic bound) (LENGTH vs)) "For too long" s4 = (INL x,t'') ==>
     body_for_ptr_ok cx tv id body vs) /\
  evaluate_type (get_tenv cx) typ = SOME tyv /\
  (do raw <- eval_expr cx e1; read_result cx raw od) es0 = (INL (IntV lo), es1) /\
  (do raw <- eval_expr cx e2; read_result cx raw od) es1 = (INL (IntV hi), es2) /\
  lo <= hi /\ Num (hi - lo) <= bound /\ 0 < Num (hi - lo) ==>
  body_stmts_ptr_ok cx body
Proof
  strip_tac >>
  `eval_iterator cx (Range e1 e2) es0 =
   (INL (GENLIST (\j. IntV (lo + &j)) (Num (hi - lo))), es2)` by
    (gvs[bind_def, AllCaseEqs()] >>
     simp[Once evaluate_def, bind_def, get_range_limits_def,
          lift_sum_def, return_def]) >>
  gvs[lift_option_type_def, return_def, check_def, assert_def,
      compatible_bound_def] >>
  first_x_assum drule >> simp[body_for_ptr_ok_def, GENLIST_EQ_NIL] >>
  Cases_on `hi = lo` >> gvs[]
QED

Theorem for_ptr_range_typing[local]:
  type_stmt env ret_ty (For id typ (Range e1 e2) bound body) = SOME env' /\
  ~(?a1 n1 a2 n2. e1 = Literal a1 (IntL n1) /\ e2 = Literal a2 (IntL n2)) ==>
  id NOTIN FDOM env.var_types /\ is_int_type typ /\
  well_typed_expr env e1 /\ well_typed_expr env e2 /\
  expr_type e1 = typ /\ expr_type e2 = typ /\
  well_formed_type env.type_defs typ /\
  0 < bound /\ well_typed_literal typ (IntL (&bound)) /\
  ?env_b. type_stmts (extend_local env id typ F) ret_ty body = SOME env_b
Proof
  strip_tac >>
  `((case Range e1 e2 of
       Range (Literal _ (IntL _)) (Literal _ (IntL _)) => T
     | Range _ _ => 0 < bound /\ well_typed_literal typ (IntL (&bound))
     | Array _ => T) =
    (0 < bound /\ well_typed_literal typ (IntL (&bound))))` by
    (Cases_on `e1` >> gvs[] >>
     rename1 `Literal a lit` >> Cases_on `lit` >> gvs[] >>
     Cases_on `e2` >> gvs[] >>
     rename1 `Range _ (Literal a' lit')` >> Cases_on `lit'` >> gvs[]) >>
  gvs[type_stmt_def, well_typed_iterator_def, optionTheory.IS_SOME_EXISTS] >>
  metis_tac[assignable_type_well_formed]
QED

Theorem for_ptr_range_endpoint_read[local]:
  expr_body_pre cenv cx env e es /\ is_int_type typ /\
  expr_type e = typ /\ evaluate_type (get_tenv cx) typ = SOME tyv /\
  (do raw <- eval_expr cx e; read_result cx raw od) es = (INL tv, es') ==>
  expr_sim_inv cenv cx env es' /\
  ?n. tv = IntV n /\ value_has_type tyv (IntV n)
Proof
  strip_tac >> drule_all exprSimSourceTheory.expr_body_pre_eval >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_body_pre_def, expr_sim_inv_def, env_consistent_def,
        env_context_consistent_def] >>
  gvs[vyperTypeExprResultTheory.expr_result_typed_def,
      expr_runtime_typed_def, value_result_typed_def] >>
  Cases_on `expr_type e` >> gvs[is_int_type_def] >>
  rename1 `expr_type e = BaseT bt` >> Cases_on `bt` >> gvs[is_int_type_def] >>
  gvs[vyperValueTheory.evaluate_type_def] >>
  Cases_on `tv` >> gvs[vyperTypingTheory.value_has_type_def]
QED

Theorem body_for_range_ptr:
  (!tenv s'' tyv t s3 vs t' s4 x t''.
     tenv = get_tenv cx /\
     lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' = (INL tyv,t) /\
     eval_iterator cx (Range e1 e2) s3 = (INL vs,t') /\
     check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s4 = (INL x,t'') ==>
     body_for_ptr_ok cx tyv id body vs) /\
  (!tenv s'' tyv t.
     tenv = get_tenv cx /\
     lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' = (INL tyv,t) ==>
     body_iterator_ptr_ok cx (Range e1 e2)) ==>
  body_stmt_ptr_ok cx (For id typ (Range e1 e2) n body)
Proof
  strip_tac >>
  Cases_on `?a1 n1 a2 n2. e1 = Literal a1 (IntL n1) /\ e2 = Literal a2 (IntL n2)`
  >- (gvs[] >> irule body_for_range_lit_ptr >> simp[] >> metis_tac[]) >>
  rewrite_tac[body_stmt_ptr_ok_def] >> rpt gen_tac >> strip_tac >>
  drule for_ptr_range_typing >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `?tyv. evaluate_type (get_tenv cx) typ = SOME tyv` by
    gvs[well_formed_type_def, optionTheory.IS_SOME_EXISTS] >>
  `body_iterator_ptr_ok cx (Range e1 e2)` by
    (first_x_assum irule >> simp[lift_option_type_def, return_def] >> metis_tac[]) >>
  `cenv.ce_alloca_locals` by fs[body_inv_def] >>
  `FLOOKUP cenv.ce_vars id = NONE` by
    (irule declared_name_unbound >> metis_tac[]) >>
  `lookup_scopes id es.scopes = NONE` by
    (Cases_on `lookup_scopes id es.scopes` >> simp[] >>
     gvs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def] >>
     res_tac >> gvs[FLOOKUP_DEF]) >>
  `is_word_type typ` by
    (Cases_on `typ` >> gvs[is_int_type_def, is_word_type_def] >>
     rename1 `is_int_type (BaseT bt)` >> Cases_on `bt` >>
     gvs[is_int_type_def, is_word_type_def]) >>
  drule_all word_type_sizes >> strip_tac >>
  `value_has_type tyv (IntV (&n))` by
    (drule_all well_typed_literal_sound >>
     simp[vyperValueOperationTheory.evaluate_literal_def]) >>
  `value_has_type tyv (IntV 0)` by
    (Cases_on `typ` >> gvs[is_int_type_def] >>
     rename1 `evaluate_type _ (BaseT bt) = _` >> Cases_on `bt` >>
     gvs[is_int_type_def, vyperValueTheory.evaluate_type_def,
         vyperTypingTheory.value_has_type_def, vyperValueTheory.within_int_bound_def]) >>
  `n < dimword (:256)` by
    (drule_at (Pat `evaluate_type _ _ = _`) range_end_words >>
     disch_then (qspecl_then [`0`, `&n`] mp_tac) >> simp[]) >>
  suspend "pre"
QED

Resume body_for_range_ptr[pre]:
  `supported_pure_expr tops e1 /\ supported_pure_expr tops e2` by
    (qpat_x_assum `supported_stmt _ _ _` mp_tac >>
     simp[supported_stmt_def, supported_iterator_def] >>
     Cases_on `e1` >> gvs[] >>
     rename1 `Range (Literal a lit) _` >> Cases_on `lit` >> gvs[] >>
     Cases_on `e2` >> gvs[] >>
     rename1 `Range _ (Literal a' lit')` >> Cases_on `lit'` >> gvs[]) >>
  `supported_expr tops e1 /\ supported_expr tops e2` by
    simp[supportedExprsTheory.supported_expr_def] >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by fs[body_inv_def] >>
  `cx_tops cx = tops` by (irule gasContextTheory.cx_tops_module >> simp[]) >>
  `!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
            is_dynamic (vyper_to_abi_type (type_env tops) target)` by fs[body_inv_def] >>
  `expr_body_pre cenv cx env e1 es` by
    (irule stmt_expr_body_pre >>
     qpat_assum `supported_expr tops e1`
       (strip_assume_tac o MATCH_MP supported_expr_body_calls) >>
     gvs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         supported_iterator_exists_def, int_calls_stmt_def, int_calls_iterator_def] >>
     qexists_tac `int_calls_expr e2 ++ int_calls_stmts body` >> simp[]) >>
  `!ei. expr_sim_inv cenv cx env ei ==> expr_body_pre cenv cx env e2 ei` by
    (rpt strip_tac >> irule stmt_expr_body_pre >>
     qpat_assum `supported_expr tops e2`
       (strip_assume_tac o MATCH_MP supported_expr_body_calls) >>
     gvs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         supported_iterator_exists_def, int_calls_stmt_def, int_calls_iterator_def] >>
     qexists_tac `int_calls_stmts body` >>
     metis_tac[call_evaluation_safe_append_right, listTheory.APPEND_ASSOC]) >>
  `expr_sim_ptr d ctx PG func cenv cx typ e1 es` by
    (gvs[body_iterator_ptr_ok_def, body_expr_ptr_ok_def] >> metis_tac[]) >>
  `!x t. FLOOKUP env.var_types x = SOME t ==> well_formed_type env.type_defs t` by
    (qpat_assum `expr_sim_inv cenv cx env es` mp_tac >>
     simp[NoAsms, expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def] >>
     rpt strip_tac >> simp[well_formed_type_def] >>
     metis_tac[optionTheory.IS_SOME_EXISTS]) >>
  match_mp_tac (SIMP_RULE std_ss [pairTheory.FORALL_PROD]
    (CONV_RULE (RAND_CONV (REWR_CONV (GSYM ETA_AX)))
      (Q.SPECL [`expr_sim_inv cenv cx env`, `body_stmts_ptr_ok cx body`]
         compile_for_range_checked_frag_active_ptr))) >>
  qexistsl_tac [`env`, `tyv`] >> simp[wordsTheory.dimword_def] >>
  rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule (SIMP_RULE std_ss [cs_mono_def] (cj 2 compile_stmt_cs_mono)) >> simp[])
  >- suspend "endpoints"
  >- suspend "active"
  >- metis_tac[]
  >- metis_tac[]
  >- suspend "body"
  >> suspend "pop"
QED

Resume body_for_range_ptr[endpoints]:
  rpt strip_tac >>
  `expr_body_pre cenv cx env e1 (es with gas_obs := gs)` by simp[] >>
  qpat_x_assum `expr_body_pre cenv cx env e1 es` kall_tac >>
  drule for_ptr_range_endpoint_read >>
  disch_then (qspec_then `tyv` mp_tac) >> simp[] >> strip_tac >>
  rename1 `tv = IntV lo` >> qexists_tac `lo` >> simp[] >>
  `expr_body_pre cenv cx env e2 es1` by metis_tac[] >>
  conj_tac
  >- (gvs[body_iterator_ptr_ok_def, body_expr_ptr_ok_def, bind_def, AllCaseEqs()] >>
      metis_tac[]) >>
  rpt strip_tac >>
  `expr_body_pre cenv cx env e2 (es1 with gas_obs := gs2)` by simp[] >>
  qpat_x_assum `expr_body_pre cenv cx env e1 (es with gas_obs := gs)` kall_tac >>
  qpat_x_assum `expr_body_pre cenv cx env e2 es1` kall_tac >>
  drule for_ptr_range_endpoint_read >>
  disch_then (qspec_then `tyv` mp_tac) >> simp[]
QED

Resume body_for_range_ptr[active]:
  rpt strip_tac >> drule_all body_for_range_active_ptr >> simp[]
QED

Resume body_for_range_ptr[body]:
  rpt strip_tac >>
  drule supported_loop_body_contract >> strip_tac >>
  `same_frame cenv c` by
    (drule_then irule declare_local_same_frame >> simp[]) >>
  `call_evaluation_safe cx (int_calls_stmts body)` by
    (fs[int_calls_stmt_def, int_calls_iterator_def] >>
     metis_tac[call_evaluation_safe_append_right]) >>
  `EVERY (stmt_exprs_ok cenv) body` by
    fs[stmts_exprs_ok_EVERY, stmt_exprs_ok_def,
       supported_stmt_expr_exists_def, alloc_limits_stmt_def, stmt_valued_return_def] >>
  `body_inv tops ctx c cx` by metis_tac[body_inv_same_frame] >>
  `!target. supported_stmts_expr_exists
      (expr_abi_decode_target_root target) body ==>
      occurs_abi_decode_target target tops` by
    (qpat_x_assum `!target. supported_stmt_expr_exists _ _ ==> _` mp_tac >>
     simp[supported_stmt_expr_exists_def]) >>
  qpat_x_assum `body_stmts_ptr_ok _ _`
    (irule o REWRITE_RULE [body_stmts_ptr_ok_def]) >>
  simp[] >> rpt conj_tac
  >- metis_tac[stmt_exprs_ok_same_frame]
  >- (qexistsl_tac [`bindings`, `tops`] >> simp[])
  >- (qexistsl_tac [`extend_local env id typ F`, `env_b`] >> simp[] >>
      conj_tac >- (irule ce_locals_declared_declare_local >> metis_tac[]) >>
      conj_tac >- (irule locals_alloc_ok_extend >> qexists_tac `cenv` >>
        simp[] >> metis_tac[same_frame_struct_fields]) >>
      irule expr_sim_inv_for_scope >> metis_tac[]) >>
  fs[frame_ret_ok_ptr_def] >> rpt strip_tac >>
  first_x_assum irule >> simp[] >> metis_tac[same_frame_trans]
QED

Resume body_for_range_ptr[pop]:
  rpt gen_tac >> disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  drule supported_loop_body_contract >> strip_tac >>
  `call_evaluation_safe cx (int_calls_stmts body)` by
    (fs[int_calls_stmt_def, int_calls_iterator_def] >>
     metis_tac[call_evaluation_safe_append_right]) >>
  `expr_sim_inv cenv cx env (ei with gas_obs := gs)` by simp[] >>
  drule_at (Pat `eval_stmts`)
    (SRULE [] (Q.INST [`es` |-> `ei with gas_obs := gs`]
      (SPEC_ALL expr_sim_inv_for_pop))) >>
  disch_then irule >> simp[] >>
  conj_tac >- (qexistsl_tac [`env_b`, `typ`, `ret_ty`] >> simp[]) >> metis_tac[]
QED

Finalise body_for_range_ptr

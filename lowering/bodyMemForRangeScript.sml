(* Memory case of the body induction, for loop (bodyMemFor's dispatch):
   a range with a computed endpoint, checked against the bound (S1's
   body_for_range), from stmtForRangeMemory's
   compile_for_range_checked_frag_active_mem with expr_sim_inv as the loop
   invariant. *)
Theory bodyMemForRange
Ancestors
  allocLimitsProps supportedExprTraverse bodyMemoryPreds bodySeqMemory stmtForRangeMemory exprSimMemDefs bodySimDeclCases
  exprSimSource bodyExprPreFacts stmtSimProps exprSimHypsDefs
  vyperTypeStoragePreservation list finite_map bodySim bodySimStmtCases
  allocLimits exprSimHyps exprLoweringProps stmtLowering stmtLoweringMono
  stmtSimForParts stmtSimForRange vyperTyping fragExec compileEnv
  supportedStmts supportedStmtTraverse supportedExprs vyperAST
  vyperInterpreter vyperState vyperValue vyperTypeSystem
  vyperTypeInvariants vyperTypeCallGraph gasContext stmtSimReturn
  vyperTypeCallStackSoundness vyperTypeValues compileVyper
Libs
  monadsyntax

val _ = Parse.hide "body";

(* Normalize only a paired outer binder at theorem application boundaries. *)
fun range_tuple_forall th =
  SIMP_RULE std_ss [pairTheory.FORALL_PROD]
    (CONV_RULE (RAND_CONV (REWR_CONV (GSYM ETA_AX))) th);

Theorem body_for_range_mem:
  !cx id typ it n body d tops bindings ctx func cenv env env' ret_ty lctx RetQ
   es.
    body_stmt_safe tops (For id typ it n body) /\
    (!tenv s'' tyv t s'3' vs t' s'4' x t''.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) /\ eval_iterator cx it s'3' = (INL vs,t') /\
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' =
       (INL x,t'') ==>
       body_for_mem_ok cx tyv id body vs) /\
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) ==>
       body_iterator_mem_ok cx it) /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (For id typ it n body) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (For id typ it n body) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (For id typ it n body) = SOME env' /\
    stmt_exprs_ok cenv (For id typ it n body) /\
    call_evaluation_safe cx (int_calls_stmt (For id typ it n body)) /\
    frame_ret_ok_mem d ctx func cx RetQ cenv ret_ty /\
    (?e1 e2. it = Range e1 e2) /\
    ~(?a1 n1 a2 n2. it = Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (For id typ it n body))
      (eval_stmt cx (For id typ it n body)) es
Proof
  rpt strip_tac >>
  imp_res_tac body_stmt_safe_for_body >> gvs[] >> rename1 `For id typ _ n stmts` >>
  drule (range_tuple_forall body_range_typing) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `?tyv. evaluate_type (get_tenv cx) typ = SOME tyv` by
    gvs[well_formed_type_def, optionTheory.IS_SOME_EXISTS] >>
  `body_iterator_mem_ok cx (Range e1 e2)` by
    (first_x_assum irule >> simp[lift_option_type_def, return_def] >> metis_tac[]) >>
  `cenv.ce_alloca_locals` by fs[body_inv_def] >>
  `FLOOKUP cenv.ce_vars id = NONE` by
    (irule declared_name_unbound >> metis_tac[]) >>
  `lookup_scopes id es.scopes = NONE` by
    (Cases_on `lookup_scopes id es.scopes` >> simp[] >>
     gvs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def] >>
     res_tac >> gvs[FLOOKUP_DEF]) >>
  `is_word_type typ` by
    (Cases_on `typ` >> gvs[is_int_type_def] >> rename1 `BaseT bt` >>
     Cases_on `bt` >> gvs[is_int_type_def, is_word_type_def]) >>
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
            is_dynamic (vyper_to_abi_type (type_env tops) target)` by
    fs[body_inv_def] >>
  qpat_assum `body_stmt_safe _ _` (strip_assume_tac o
    SIMP_RULE std_ss [body_stmt_safe_def, supported_stmt_expr_exists_def,
      supported_assignment_exists_def, supported_iterator_exists_def,
      supported_assert_exists_def, supported_raise_exists_def,
      supported_expr_exists_def, int_calls_stmt_def, int_calls_atarget_def,
      int_calls_iterator_def, int_calls_assert_reason_def, int_calls_raise_reason_def,
      listTheory.EVERY_APPEND, listTheory.EVERY_CONJ,
      DE_MORGAN_THM, GSYM expr_has_evm_run_def]) >>
  qpat_assum `stmt_exprs_ok _ _` (strip_assume_tac o
    SIMP_RULE std_ss [stmt_exprs_ok_def, alloc_limits_stmt_def,
      alloc_limits_iterator_def, alloc_limits_assert_def, alloc_limits_raise_def,
      alloc_limits_expr_def]) >>
  imp_res_tac alloc_limits_expr_not_extcode >>
  `expr_body_pre cenv cx env e1 es` by
    (irule stmt_expr_body_pre >>
     gvs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         supported_iterator_exists_def, int_calls_stmt_def, int_calls_iterator_def] >>
     qexists_tac `int_calls_expr e2 ++ int_calls_stmts stmts` >> simp[]) >>
  `!ei. expr_sim_inv cenv cx env ei ==> expr_body_pre cenv cx env e2 ei` by
    (rpt strip_tac >> irule stmt_expr_body_pre >>
     gvs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         supported_iterator_exists_def, int_calls_stmt_def, int_calls_iterator_def] >>
     qexists_tac `int_calls_stmts stmts` >>
     metis_tac[call_evaluation_safe_append_right, listTheory.APPEND_ASSOC]) >>
  `expr_sim_mem ctx func cenv cx typ e1 es` by
    (gvs[body_iterator_mem_ok_def, body_expr_mem_ok_def] >> metis_tac[]) >>
  `!x t. FLOOKUP env.var_types x = SOME t ==> well_formed_type env.type_defs t` by
    (qpat_assum `expr_sim_inv cenv cx env es` mp_tac >>
     simp[NoAsms, expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def] >>
     rpt strip_tac >> simp[well_formed_type_def] >>
     metis_tac[optionTheory.IS_SOME_EXISTS]) >>
  MATCH_MP_TAC (range_tuple_forall
    (Q.SPECL [`expr_sim_inv cenv cx env`, `body_stmts_mem_ok cx stmts`, `d`]
       compile_for_range_checked_frag_active_mem)) >>
  qexistsl_tac [`env`, `tyv`] >> simp[wordsTheory.dimword_def] >>
  rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule (SIMP_RULE std_ss [cs_mono_def] (cj 2 compile_stmt_cs_mono)) >>
      simp[])
  >- suspend "endpoints"
  >- suspend "active"
  >- metis_tac[]
  >- suspend "body"
  >> suspend "pop"
QED

Resume body_for_range_mem[endpoints]:
  rpt strip_tac >>
  `expr_body_pre cenv cx env e1 (es with gas_obs := gs)` by simp[] >>
  qpat_x_assum `expr_body_pre cenv cx env e1 es` kall_tac >>
  drule (range_tuple_forall body_range_endpoint_read) >>
  disch_then (qspec_then `tyv` mp_tac) >>
  simp[] >> strip_tac >>
  rename1 `tv = IntV lo` >> qexists_tac `lo` >> simp[] >>
  `expr_body_pre cenv cx env e2 es1` by metis_tac[] >>
  conj_tac
  >- (gvs[body_iterator_mem_ok_def, body_expr_mem_ok_def, bind_def,
          AllCaseEqs()] >>
      metis_tac[]) >>
  rpt strip_tac >>
  `expr_body_pre cenv cx env e2 (es1 with gas_obs := gs2)` by simp[] >>
  qpat_x_assum `expr_body_pre cenv cx env e1 (es with gas_obs := gs)` kall_tac >>
  qpat_x_assum `expr_body_pre cenv cx env e2 es1` kall_tac >>
  drule (range_tuple_forall body_range_endpoint_read) >>
  disch_then (qspec_then `tyv` mp_tac) >> simp[]
QED

(* A successful nonempty checked iterator activates the body's IH. *)
Resume body_for_range_mem[active]:
  rpt strip_tac >>
  `eval_iterator cx (Range e1 e2) (es with gas_obs := gs) =
   (INL (GENLIST (\j. IntV (n1 + &j)) (Num (n2 - n1))), es2)` by
    (gvs[bind_def, AllCaseEqs()] >>
     simp[Once evaluate_def, bind_def, get_range_limits_def,
          lift_sum_def, return_def]) >>
  first_x_assum (qspecl_then [`es`, `tyv`, `es`, `es with gas_obs := gs`,
    `GENLIST (\j. IntV (n1 + &j)) (Num (n2 - n1))`, `es2`, `es`, `es`]
    mp_tac) >>
  simp[lift_option_type_def, return_def, check_def, assert_def,
       compatible_bound_def, body_for_mem_ok_def, GENLIST_EQ_NIL] >>
  Cases_on `n2 = n1` >> gvs[]
QED

Resume body_for_range_mem[body]:
  rpt strip_tac >>
  drule supported_loop_body_contract >> strip_tac >>
  `same_frame cenv c` by
    (drule_then irule declare_local_same_frame >> simp[]) >>
  `call_evaluation_safe cx (int_calls_stmts stmts)` by
    (fs[int_calls_stmt_def, int_calls_iterator_def] >>
     metis_tac[call_evaluation_safe_append_right]) >>
  `EVERY (stmt_exprs_ok cenv) stmts` by
    metis_tac[body_for_exprs_ok] >>
  `body_inv tops ctx c cx` by metis_tac[body_inv_same_frame] >>
  `!target. supported_stmts_expr_exists (expr_abi_decode_target_root target)
              stmts ==> occurs_abi_decode_target target tops` by
    fs[supported_stmt_expr_exists_def] >>
  `body_stmts_safe tops stmts` by
    metis_tac[body_stmt_safe_for_body] >>
  qpat_x_assum `body_stmts_mem_ok _ _`
    (irule o REWRITE_RULE [body_stmts_mem_ok_def]) >>
  simp[] >> rpt conj_tac
  >- metis_tac[stmt_exprs_ok_same_frame]
  >- (qexistsl_tac [`bindings`, `tops`] >> simp[])
  >- (qexistsl_tac [`extend_local env id typ F`, `env_b`] >> simp[] >>
      conj_tac
      >- (irule ce_locals_declared_declare_local >> metis_tac[]) >>
      conj_tac
      >- (irule locals_alloc_ok_extend >> qexists_tac `cenv` >>
          simp[] >> metis_tac[same_frame_struct_fields]) >>
      irule expr_sim_inv_for_scope >> metis_tac[]) >>
  metis_tac[frame_ret_ok_mem_same_frame]
QED

Resume body_for_range_mem[pop]:
  rpt gen_tac >> disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  drule supported_loop_body_contract >> strip_tac >>
  `call_evaluation_safe cx (int_calls_stmts stmts)` by
    (fs[int_calls_stmt_def, int_calls_iterator_def] >>
     metis_tac[call_evaluation_safe_append_right]) >>
  `expr_sim_inv cenv cx env (ei with gas_obs := gs)` by simp[] >>
  qspecl_then [`cenv`, `cx`, `env`, `ei with gas_obs := gs`, `id`, `typ`,
               `tyv`, `IntV (n1 + &j)`, `ret_ty`, `stmts`, `env_b`, `r2`,
               `es2`, `sc`, `rest`, `tops`, `bindings`]
    mp_tac expr_sim_inv_for_pop >>
  simp[]
QED

Finalise body_for_range_mem

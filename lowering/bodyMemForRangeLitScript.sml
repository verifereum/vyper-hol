(* Memory case of the body induction, for loop (bodyMemFor's dispatch):
   a range of two integer literals (S1's body_for_range_lit), from
   stmtForRangeLitMemory's compile_for_range_lit_frag_mem with expr_sim_inv
   as the loop invariant. *)
Theory bodyMemForRangeLit
Ancestors
  bodyMemoryPreds bodySeqMemory stmtForRangeLitMemory bodySimDeclCases
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

Theorem body_for_range_lit_mem:
  !cx id typ it n body d tops bindings ctx func cenv env env' ret_ty lctx RetQ
   es.
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
    (?a1 n1 a2 n2. it = Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (For id typ it n body))
      (eval_stmt cx (For id typ it n body)) es
Proof
  rpt strip_tac >> gvs[] >> rename1 `For id typ _ n stmts` >>
  `FLOOKUP cenv.ce_vars id = NONE` by
    (irule declared_name_unbound >> metis_tac[]) >>
  `id NOTIN FDOM env.var_types /\ is_int_type typ /\
   well_typed_literal typ (IntL n1) /\ well_typed_literal typ (IntL n2) /\
   well_formed_type env.type_defs typ /\
   ?env_b. type_stmts (extend_local env id typ F) ret_ty stmts = SOME env_b` by
    gvs[type_stmt_def, well_typed_iterator_def, well_typed_expr_def,
        expr_type_def, optionTheory.IS_SOME_EXISTS, AllCaseEqs()] >>
  `n1 <= n2 /\ n = Num (n2 - n1) /\ supported_stmts tops bindings stmts` by
    gvs[supported_stmt_def, supported_iterator_def] >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `?tyv. evaluate_type (get_tenv cx) typ = SOME tyv` by
    gvs[well_formed_type_def, optionTheory.IS_SOME_EXISTS] >>
  `!k. well_typed_literal typ (IntL k) ==> value_has_type tyv (IntV k)` by
    (rpt strip_tac >> drule_all well_typed_literal_sound >>
     simp[vyperValueOperationTheory.evaluate_literal_def]) >>
  `GENLIST (\j. IntV (n1 + &j)) (Num (n2 - n1)) <> [] ==>
   body_stmts_mem_ok cx stmts` by
    (strip_tac >>
     first_x_assum (qspecl_then [`es`, `tyv`, `es`, `es`,
       `GENLIST (\j. IntV (n1 + &j)) (Num (n2 - n1))`, `es`, `es`,
       `es`] mp_tac) >>
     simp[lift_option_type_def, return_def, eval_iterator_range_lit,
          check_def, assert_def, compatible_bound_def, body_for_mem_ok_def]) >>
  `Num (n2 - n1) < dimword (:256)` by metis_tac[range_end_words] >>
  `cenv.ce_alloca_locals` by fs[body_inv_def] >>
  `lookup_scopes id es.scopes = NONE` by
    (Cases_on `lookup_scopes id es.scopes` >> simp[] >>
     gvs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def] >>
     res_tac >> gvs[FLOOKUP_DEF]) >>
  `is_word_type typ` by
    (Cases_on `typ` >> gvs[is_int_type_def] >> rename1 `BaseT bt` >>
     Cases_on `bt` >> gvs[is_int_type_def, is_word_type_def]) >>
  drule_all word_type_sizes >> disch_then (qspec_then `cenv` strip_assume_tac) >>
  `call_evaluation_safe cx (int_calls_stmts stmts)` by
    (fs[int_calls_stmt_def] >> metis_tac[call_evaluation_safe_append_right]) >>
  `EVERY (stmt_exprs_ok cenv) stmts /\ type_memory_bytes cenv typ < 2 ** 64` by
    fs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
       stmts_exprs_ok_EVERY, alloc_limits_stmt_def, stmt_valued_return_def] >>
  `!target. supported_stmts_expr_exists (expr_abi_decode_target_root target)
              stmts ==> occurs_abi_decode_target target tops` by
    fs[supported_stmt_expr_exists_def] >>
  MATCH_MP_TAC
    (BETA_RULE (Q.SPEC `\ei. expr_sim_inv cenv cx env ei`
                  compile_for_range_lit_frag_mem)) >>
  qexists_tac `tyv` >> simp[wordsTheory.dimword_def] >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule (SIMP_RULE std_ss [cs_mono_def] (cj 2 compile_stmt_cs_mono)) >>
      simp[])
  >- (rpt strip_tac >>
      `body_stmts_mem_ok cx stmts` by
        (first_x_assum irule >> simp[listTheory.GENLIST_EQ_NIL] >>
         strip_tac >> gvs[]) >>
      `same_frame cenv c` by
        (drule_then irule declare_local_same_frame >> simp[]) >>
      `value_has_type tyv (IntV (n1 + &j))` by
        (irule range_value_has_type >> simp[] >> qexists_tac `n2` >> simp[]) >>
      qpat_x_assum `body_stmts_mem_ok _ _`
        (irule o REWRITE_RULE [body_stmts_mem_ok_def]) >>
      simp[] >> rpt conj_tac
      >- metis_tac[stmt_exprs_ok_same_frame]
      >- metis_tac[body_inv_same_frame]
      >- (qexistsl_tac [`extend_local env id typ F`, `env_b`] >> simp[] >>
          `c.ce_struct_fields = cenv.ce_struct_fields` by
            metis_tac[same_frame_struct_fields] >>
          metis_tac[expr_sim_inv_for_scope, ce_locals_declared_declare_local,
                    locals_alloc_ok_extend]) >>
      metis_tac[frame_ret_ok_mem_same_frame]) >>
  rpt strip_tac >>
  `value_has_type tyv (IntV (n1 + &j))` by
    (irule range_value_has_type >> simp[] >> qexists_tac `n2` >> simp[]) >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    fs[body_inv_def] >>
  `expr_sim_inv cenv cx env (ei with gas_obs := gs)` by simp[] >>
  qspecl_then [`cenv`, `cx`, `env`, `ei with gas_obs := gs`, `id`, `typ`,
               `tyv`, `IntV (n1 + &j)`, `ret_ty`, `stmts`, `env_b`, `r2`,
               `es2`, `sc`, `rest`, `tops`, `bindings`]
    mp_tac expr_sim_inv_for_pop >>
  simp[]
QED

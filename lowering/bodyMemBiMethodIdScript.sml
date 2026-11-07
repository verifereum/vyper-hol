(* Memory case of the body induction, one family of bodyMemBuiltinRest's
   builtins: method_id (S1: exprSimBuiltins' compile_method_id_case). *)
Theory bodyMemBiMethodId
Ancestors
  bodyMemoryPreds bodyMemBiMethodIdRuntime bodyMemBiMethodIdLiteral
  exprSimHash exprSimHyps exprSimMemDefs bodyExprForceMemory exprLowering
  exprLoweringProps exprSimHypsDefs vyperTypeSystem list loweringPosts
  vyperInterpreter exprSimSource vyperContext vyperAST compileEnv

Theorem body_builtin_method_id_mem:
  !cx ty es.
    (builtin_args_length_ok MethodId (LENGTH es) ==> body_exprs_mem_ok cx es) ==>
    body_expr_mem_ok cx (Builtin ty MethodId es)
Proof
  rpt gen_tac >> strip_tac >> (rpt gen_tac >> match_mp_tac body_expr_mem_ok_intro >>
   conj_tac >- (rpt strip_tac >> gvs[])) >>
  rpt gen_tac >> strip_tac >>
  `well_typed_builtin_app ty MethodId (MAP expr_type es)` by
    gvs[expr_body_pre_def, well_typed_expr_def] >>
  drule (SRULE [] (Q.INST [`b` |-> `MethodId`] hash_builtin_types)) >> simp[] >> strip_tac >>
  `?e. es = [e]` by
    (Cases_on `es` >> gvs[] >> Cases_on `t` >> gvs[]) >> gvs[] >>
  `body_expr_mem_ok cx e` by
    (qpat_x_assum `_ ==> body_exprs_mem_ok _ _` mp_tac >>
     simp[builtin_args_length_ok_def, body_exprs_mem_ok_def]) >>
  `expr_body_pre cenv cx env e es'` by
    (drule expr_body_pre_builtin_arg >> disch_then irule >> gvs[expr_body_pre_def]) >>
  `expr_sim_mem ctx func cenv cx (expr_type e) e es'` by
    metis_tac[body_expr_mem_ok_def] >>
  qmatch_goalsub_abbrev_tac `Builtin ann MethodId [e]` >>
  `expr_vv_sim_mem ctx func cenv cx ty' (Builtin ann MethodId [e]) es'` by
    (unabbrev_all_tac >> Cases_on `method_id_literal e = NONE`
     >- (irule method_id_runtime_vv_sim_mem >> simp[] >> metis_tac[]) >>
     `?la l. e = Literal la l` by
       (Cases_on `e` >> gvs[method_id_literal_def] >>
        rename1 `Literal la l` >> metis_tac[]) >> gvs[] >>
     `IS_SOME (method_id_literal (Literal la l))` by
       (Cases_on `method_id_literal (Literal la l)` >> gvs[]) >>
     metis_tac[method_id_literal_dynamic_vv_sim_mem,
       body_method_id_literal_word_mem, body_expr_mem_ok_def]) >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `expr_body_pre _ _ _ (Builtin _ _ _) _`
    (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
      body_expr_sim_mem_of_vv_sim_mem)) >>
  disch_then (qspecl_then [`ctx`, `func`, `ty'`] mp_tac) >>
  simp[] >>
  impl_tac >- (
    simp[expr_type_def, is_word_type_def, Abbr `ann`] >>
    rpt gen_tac >> Cases_on `method_id_literal e`
    >- (simp[compile_method_id_singleton_runtime, as_ptr_val_def,
          comp_bind_def, comp_return_def] >>
        rpt (pairarg_tac >> gvs[]) >>
        Cases_on `compile_method_id_runtime (expr_type e) v F sm` >>
        simp[as_ptr_val_def]) >>
    `?la l. e = Literal la l` by
      (Cases_on `e` >> gvs[method_id_literal_def] >> metis_tac[]) >>
    gvs[] >> drule compile_expr_method_id_literal >>
    disch_then (qspecl_then [`cenv`, `ty'`, `BaseT (BytesT (Dynamic 4))`, `sa`] mp_tac) >>
    disch_then SUBST1_TAC >>
    simp[compile_literal_vv_def, comp_bind_def, comp_return_def] >>
    pairarg_tac >> simp[]) >>
  simp[expr_type_def, is_word_type_def, Abbr `ann`]
QED

(* Statement guards for request-prefix proofs in a single-file body. *)
Theory bodySingletonStmtGuards
Ancestors
  bodyCallSupport bodySim bodyExprPreFacts bodyInvCodeProps exprSimHypsDefs
  compileUnit supportedStmtTraverse finite_map option list pair
  loweringShapeSource[qualified] vyperTypeInvariants[qualified]

Theorem singleton_stmt_expr_guards:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  supported_stmt tops bindings stmt /\ type_stmt env ret stmt = SOME env' /\
  stmt_exprs_ok cenv stmt ==>
  ~supported_stmt_expr_exists (unallocated_bare_global_root cenv env) stmt /\
  EVERY (source_body_call_supported cx) (int_calls_stmt stmt)
Proof
  strip_tac >> conj_tac
  >- (`~supported_stmt_expr_exists (const_name_root cx) stmt` by
        (drule_all_then ACCEPT_TAC body_inv_stmt_const_name_free) >>
      `!src id ty. FLOOKUP env.bare_globals (src,id) = SOME ty /\
         (~cx_const_name cx (src,id) \/
          IS_SOME (FLOOKUP env.bare_global_assignable (src,id))) ==>
         IS_SOME (FLOOKUP cenv.ce_module_vars (src,id))` by
        (qpat_assum `expr_sim_inv _ _ _ _`
           (strip_assume_tac o REWRITE_RULE [expr_sim_inv_split_def]) >>
         rpt strip_tac >> res_tac >> simp[]) >>
      `!src id ty. FLOOKUP env.bare_global_assignable (src,id) = SOME ty ==>
         FLOOKUP env.bare_globals (src,id) = SOME ty` by
        (qpat_assum `expr_sim_inv _ _ _ _`
           (strip_assume_tac o REWRITE_RULE [expr_sim_inv_def,
              vyperTypeInvariantsTheory.env_consistent_def,
              vyperTypeInvariantsTheory.env_context_consistent_def]) >>
         rpt strip_tac >> res_tac) >>
      `!x. unallocated_bare_global_root cenv env x ==> const_name_root cx x` by
        (Cases >> simp[unallocated_bare_global_root_def, const_name_root_def]
         >- (rename1 `cx_const_name cx nsid` >> PairCases_on `nsid` >>
             strip_tac >> CCONTR_TAC >> fs[IS_SOME_EXISTS] >>
             rename1 `FLOOKUP env.bare_globals (nsid0,nsid1) = SOME ty` >>
             qpat_assum `!src id ty. FLOOKUP env.bare_globals _ = _ /\ _ ==> _`
               (qspecl_then [`nsid0`,`nsid1`,`ty`] mp_tac) >> simp[]) >>
         gen_tac >> PairCases_on `nsid` >> strip_tac >>
         Cases_on `FLOOKUP env.bare_global_assignable (nsid0,nsid1)` >> simp[] >>
         rename1 `FLOOKUP env.bare_global_assignable (nsid0,nsid1) = SOME ty` >>
         res_tac >>
         qpat_x_assum `!src id ty. FLOOKUP env.bare_globals _ = _ /\ _ ==> _`
           (qspecl_then [`nsid0`,`nsid1`,`ty`] mp_tac) >> fs[]) >>
      strip_tac >>
      qpat_x_assum `~supported_stmt_expr_exists (const_name_root cx) stmt` mp_tac >>
      simp[] >> irule (CONJUNCT1 loweringShapeSourceTheory.supported_stmt_expr_exists_mono) >>
      qexists_tac `unallocated_bare_global_root cenv env` >> simp[]) >>
  drule_then assume_tac body_inv_contract >>
  drule_then strip_assume_tac body_inv_main_code >>
  `expr_sim_inv_mods [(NONE,tops)] cenv cx env es` by fs[expr_sim_inv_split_def] >>
  drule_all_then (mp_tac o CONJUNCT1) supported_stmts_main_calls_mods >>
  simp[main_module_def, alistTheory.ALOOKUP_def] >>
  disch_then (qspecl_then [`bindings`,`stmt`,`ret`,`env'`] mp_tac) >> simp[]
QED

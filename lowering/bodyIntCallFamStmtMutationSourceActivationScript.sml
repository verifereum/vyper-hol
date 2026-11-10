(* Source-only declaration continuation, independent of initialization mode. *)
Theory bodyIntCallFamStmtMutationSourceActivation
Ancestors
  bodyIntCallJointContract stmtSimDeclSource stmtSimDeclCompose gasSummary
  exprSimSource bodySim bodyExprPreFacts stmtSimDefs exprSimHypsDefs vyperInterpreter
  vyperState vyperTypeSystem vyperTypeInvariants compileEnv finite_map

Theorem intcall_annassign_source_activation:
  body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  intcall_joint_res fp ce env es sa0 s0 /\
  supported_stmt fp.jc_tops bindings (AnnAssign id ty e) /\
  type_stmt env ret (AnnAssign id ty e) = SOME env' /\
  stmt_exprs_ok ce (AnnAssign id ty e) /\
  call_evaluation_safe fp.jc_cx (int_calls_stmt (AnnAssign id ty e)) /\
  stmt_env ce lctx ret (AnnAssign id ty e) sa0 = (c,sf) /\
  declare_local ce id ty sa0 = (c,st) /\
  gas_admissible (eval_stmt fp.jc_cx (AnnAssign id ty e)) (stmt_res_ok lctx) es /\
  evaluate_type (get_tenv fp.jc_cx) ty = SOME tv /\
  (!tail. bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx)
     (es with gas_obs := prefix ++ tail) = (INL v,ee with gas_obs := tail)) ==>
  ?ff sc rest.
    ee.scopes = sc :: rest /\ lookup_scopes id ee.scopes = NONE /\
    ff = ee with scopes :=
      (sc |+ (id,<|assignable := T; type := tv; value := v; popped := []|>)) :: rest /\
    (!tail. new_variable id tv v (ee with gas_obs := tail) =
      (INL (),ff with gas_obs := tail)) /\
    eval_stmt fp.jc_cx (AnnAssign id ty e) (es with gas_obs := prefix) =
      (INL (),ff with gas_obs := []) /\
    expr_sim_inv c fp.jc_cx env' (ff with gas_obs := []) /\
    locals_alloc_ok c env' /\ ce_locals_declared c env' /\
    cenv_top_ext ce c ff.scopes
Proof
  strip_tac >> drule_all annassign_continuation_all_tails >> strip_tac >>
  qabbrev_tac `ff = ee with scopes :=
    (sc |+ (id,<|assignable := T; type := tv; value := v; popped := []|>)) :: rest` >>
  `eval_stmt fp.jc_cx (AnnAssign id ty e) (es with gas_obs := prefix) =
     (INL (),ff with gas_obs := [])` by
    (drule eval_annassign_action >>
     disch_then (qspecl_then [`id`,`e`] SUBST1_TAC) >>
     qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` assume_tac) >>
     fs[] >> simp[Once bind_def,Abbr `ff`]) >>
  `expr_sim_inv ce fp.jc_cx env es /\ locals_alloc_ok ce env /\
   ce_locals_declared ce env` by
    fs[intcall_joint_res_def,intcall_expr_res_def] >>
  `supported_program fp.jc_tops /\
   get_module_code fp.jc_cx NONE = SOME fp.jc_tops /\ ce.ce_alloca_locals` by
    fs[body_inv_def] >>
  drule_all locals_alloc_ok_stmt >> strip_tac >>
  drule_all ce_locals_declared_stmt >> strip_tac >>
  `expr_sim_inv ce fp.jc_cx env (es with gas_obs := prefix)` by simp[] >>
  drule_all expr_sim_inv_stmt >> strip_tac >> suspend "extension"
QED

Resume intcall_annassign_source_activation[extension]:
  qexistsl [`ff`,`sc`,`rest`] >> simp[Abbr `ff`] >>
  irule cenv_top_ext_declare_local >>
  simp[] >> qexistsl [`id`,`sa0`,`st`,`ty`] >>
  fs[lookup_scopes_def,ce_locals_declared_def,type_stmt_def,AllCaseEqs()] >>
  conj_tac >-
    (rpt strip_tac >>
     qpat_x_assum `!n l. FLOOKUP ce.ce_vars n = SOME l ==> _`
       (drule_then assume_tac) >> fs[]) >>
  qpat_x_assum `lookup_scopes id ee.scopes = NONE` mp_tac >>
  qpat_assum `ee.scopes = _` (fn th => rewrite_tac[th]) >>
  Cases_on `FLOOKUP sc id` >> simp[lookup_scopes_def]
QED

Finalise intcall_annassign_source_activation

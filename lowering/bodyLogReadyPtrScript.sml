(* Conditional argument readiness for the pointer body induction. *)
Theory bodyLogReadyPtr
Ancestors
  logArgsPtr bodyPtrPreds exprSimSource bodyExprPreFacts exprSimHypsDefs
  bodySim bodySimStmtCases exprSimHyps compileEnv supportedTypes
  supportedExprs supportedExprTraverse supportedStmtTraverse vyperInterpreter
  vyperState vyperTypeSystem supportedProgram supportedNames vyperContext
  vyperABI vyperTypeInvariants vyperTypeExprSoundness vyperTypeCallGraph
  vyperTypeCallStackSoundness

Theorem log_pure_expr_body_pre:
  !tops ctx cenv cx env e calls es.
    body_inv tops ctx cenv cx /\ supported_pure_expr tops e /\
    well_typed_expr env e /\
    ~supported_expr_exists
       (\e. ~is_extcode e /\
            ~(byte_widths_expr e /\ alloc_limits_expr cenv e)) e /\
    call_evaluation_safe cx (int_calls_expr e ++ calls) /\
    (!target. supported_expr_exists (expr_abi_decode_target_root target) e ==>
              occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es ==>
    expr_body_pre cenv cx env e es
Proof
  rpt strip_tac >>
  `int_calls_expr e = []` by metis_tac[supported_pure_int_calls] >>
  `supported_expr tops e` by simp[supported_expr_def] >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `get_module_code cx NONE = SOME tops` by fs[body_inv_def] >>
  `cx_tops cx = tops` by simp[gasContextTheory.cx_tops_def] >>
  irule stmt_expr_body_pre >> simp[] >>
  conj_tac >- (fs[body_inv_def] >> metis_tac[]) >>
  qexists_tac `calls` >> gvs[]
QED

Theorem body_log_args_ready_ptr:
  !tops d ctx PG func cenv cx env args.
    body_inv tops ctx cenv cx /\ body_exprs_ptr_ok cx args /\
    supported_pure_exprs tops args /\ well_typed_exprs env args /\
    ~supported_exprs_exists
       (\e. ~is_extcode e /\
            ~(byte_widths_expr e /\ alloc_limits_expr cenv e)) args /\
    call_evaluation_safe cx (int_calls_exprs args) /\
    (!target. supported_exprs_exists (expr_abi_decode_target_root target) args ==>
              occurs_abi_decode_target target tops) ==>
    log_args_ready_ptr d ctx PG func cenv cx (\es. expr_sim_inv cenv cx env es) args
Proof
  Induct_on `args` >> simp[log_args_ready_ptr_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `supported_pure_exprs _ _` (strip_assume_tac o
    SIMP_RULE std_ss [Once supported_pure_expr_def]) >>
  qpat_x_assum `well_typed_exprs _ _` (strip_assume_tac o
    SIMP_RULE std_ss [Once well_typed_expr_def]) >>
  qpat_x_assum `~supported_exprs_exists _ _` (strip_assume_tac o
    SIMP_RULE std_ss [Once supported_expr_exists_def, DE_MORGAN_THM]) >>
  qpat_x_assum `call_evaluation_safe _ _` (assume_tac o
    SIMP_RULE std_ss [Once int_calls_expr_def]) >>
  qpat_x_assum `!target. supported_exprs_exists _ _ ==> _` (strip_assume_tac o
    SIMP_RULE std_ss [Once supported_expr_exists_def, DISJ_IMP_THM,
                      FORALL_AND_THM]) >>
  gvs[body_exprs_ptr_ok_def] >>
  `call_evaluation_safe cx (int_calls_exprs args)` by
    (irule call_evaluation_safe_append_right >>
     qexists_tac `int_calls_expr h` >> simp[]) >>
  reverse conj_tac >- (strip_tac >> first_x_assum irule >> metis_tac[]) >>
  gen_tac >> strip_tac >>
  `expr_body_pre cenv cx env h es` by
    (irule log_pure_expr_body_pre >> simp[DE_MORGAN_THM] >> metis_tac[]) >>
  conj_tac >- metis_tac[body_expr_ptr_ok_def] >>
  rpt gen_tac >> strip_tac >>
  drule_all expr_body_pre_eval >> strip_tac >>
  gvs[vyperTypeExprResultTheory.expr_result_typed_def, expr_runtime_typed_def,
      value_result_typed_def, value_runtime_typed_def] >>
  `env.type_defs = get_tenv cx` suffices_by metis_tac[] >>
  gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def]
QED

(* Memory case of the body induction (bodyMemory's body_mem_mutual): log. *)
Theory bodyMemLog
Ancestors
  allocLimitsProps exprSimSource
  bodyMemoryPreds stmtLogMemory bodySimLog
  exprSimMemDefs exprSimHypsDefs bodyExprPreFacts bodySimStmtCases bodySim
  supportedExprs supportedExprTraverse supportedStmtTraverse supportedStmts
  supportedProgram vyperTypeCallGraph vyperTypeSystem vyperTypeExprResult
  vyperTypeInvariants vyperTypeExprSoundness vyperTypeCallStackSoundness
  gasContext allocLimits vyperInterpreter vyperState list

(* The argument's explicit body-safety facts supply the call preconditions. *)
Theorem log_mem_arg_body_pre[local]:
  !tops ctx cenv cx env e es.
    body_stmt_safe tops (Expr e) /\ ~is_extcode e /\
    body_inv tops ctx cenv cx /\ supported_pure_expr tops e /\
    well_typed_expr env e /\
    ~supported_expr_exists
       (\e. ~is_extcode e /\ ~(byte_widths_expr e /\ alloc_limits_expr cenv e)) e /\
    call_evaluation_safe cx (int_calls_expr e) /\
    (!target. supported_expr_exists (expr_abi_decode_target_root target) e ==>
              occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es ==>
    expr_body_pre cenv cx env e es
Proof
  rpt strip_tac >>
  qpat_assum `body_stmt_safe _ _` (strip_assume_tac o
    SIMP_RULE std_ss [body_stmt_safe_def, supported_stmt_expr_exists_def,
      int_calls_stmt_def, listTheory.EVERY_CONJ, GSYM expr_has_evm_run_def]) >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops /\
   (!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
       is_dynamic (vyper_to_abi_type (type_env tops) target))` by
    fs[body_inv_def] >>
  `cx_tops cx = tops` by simp[gasContextTheory.cx_tops_def] >>
  qspecl_then [`cenv`, `cx`, `env`, `e`, `es`, `[]`]
    irule stmt_expr_body_pre >> simp[] >> metis_tac[]
QED

(* One step of the arguments: the head simulates under the memory
   judgment, and once it evaluates, the tail meets the same conditions
   and the head's value has its type. *)
Theorem log_mem_args_step[local]:
  !tops ctx func cenv cx env e tail s.
    EVERY (\e. body_stmt_safe tops (Expr e) /\ ~is_extcode e) (e::tail) /\
    body_inv tops ctx cenv cx /\ body_exprs_mem_ok cx (e::tail) /\
    expr_sim_inv cenv cx env s /\
    supported_pure_exprs tops (e::tail) /\ well_typed_exprs env (e::tail) /\
    ~supported_exprs_exists
       (\e. ~is_extcode e /\ ~(byte_widths_expr e /\ alloc_limits_expr cenv e)) (e::tail) /\
    call_evaluation_safe cx (int_calls_exprs (e::tail)) /\
    (!target. supported_exprs_exists (expr_abi_decode_target_root target) (e::tail) ==>
              occurs_abi_decode_target target tops) ==>
    expr_sim_mem ctx func cenv cx (expr_type e) e s /\
    !v s1. (do r <- eval_expr cx e; read_result cx r od) s = (INL v,s1) ==>
      (EVERY (\e. body_stmt_safe tops (Expr e) /\ ~is_extcode e) tail /\
       body_exprs_mem_ok cx tail /\ expr_sim_inv cenv cx env s1 /\
       supported_pure_exprs tops tail /\ well_typed_exprs env tail /\
       ~supported_exprs_exists
          (\e. ~is_extcode e /\ ~(byte_widths_expr e /\ alloc_limits_expr cenv e)) tail /\
       call_evaluation_safe cx (int_calls_exprs tail) /\
       (!target. supported_exprs_exists (expr_abi_decode_target_root target) tail ==>
                 occurs_abi_decode_target target tops)) /\
      ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
           value_has_type tv v
Proof
  rpt gen_tac >> simp[EVERY_DEF] >> strip_tac >>
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
  gvs[body_exprs_mem_ok_def] >>
  `call_evaluation_safe cx (int_calls_expr e)` by
    (irule call_evaluation_safe_append_left >>
     qexists_tac `int_calls_exprs tail` >> simp[]) >>
  `call_evaluation_safe cx (int_calls_exprs tail)` by
    (irule call_evaluation_safe_append_right >>
     qexists_tac `int_calls_expr e` >> simp[]) >>
  `expr_body_pre cenv cx env e s` by
    (irule log_mem_arg_body_pre >> simp[DE_MORGAN_THM] >> metis_tac[]) >>
  conj_tac >- metis_tac[body_expr_mem_ok_def] >>
  rpt gen_tac >> strip_tac >>
  drule_all expr_body_pre_eval >> strip_tac >>
  `?tv t s2 t1. eval_expr cx e s = (INL tv, t) /\
                read_result cx tv s2 = (INL v, t1)` by
    (qpat_x_assum `(do r <- eval_expr cx e; read_result cx r od) s = _` mp_tac >>
     simp[bind_def, AllCaseEqs()] >> metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  gvs[expr_result_typed_def, expr_runtime_typed_def, value_result_typed_def,
      value_runtime_typed_def] >>
  `env.type_defs = get_tenv cx` suffices_by metis_tac[] >>
  gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def]
QED

Theorem body_log_mem_case:
  !cx id es. body_exprs_mem_ok cx es ==> body_stmt_mem_ok cx (Log id es)
Proof
  rw[body_stmt_mem_ok_def] >>
  rename1 `stmt_frag_mem _ _ _ _ _ _ _ _ _ st` >>
  `?fields. supported_event_fields tops id = SOME fields /\
            supported_pure_exprs tops es /\
            MAP expr_type es = MAP (SND o FST) fields` by
    (gvs[supported_stmt_def, supported_log_def, AllCaseEqs()] >>
     Cases_on `supported_event_fields tops id` >> gvs[]) >>
  drule_all body_log_metadata >> strip_tac >>
  `SUM (MAP (type_memory_bytes cenv)
          (log_non_indexed_types (MAP SND fields)
             (MAP (SND o FST) fields))) < dimword (:256) /\
   abi_size_bound cenv.ce_struct_fields
     (TupleT (log_non_indexed_types (MAP SND fields)
                (MAP (SND o FST) fields))) < dimword (:256)` by
    (gvs[stmt_exprs_ok_def, alloc_limits_stmt_def, log_alloc_ok_def] >>
     conj_tac >> irule arithmeticTheory.LESS_LESS_EQ_TRANS >>
     qexists_tac `2 ** 64` >> gvs[wordsTheory.dimword_def]) >>
  `well_typed_exprs env es /\
   !id t. FLOOKUP env.var_types id = SOME t ==>
     ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)` by
    gvs[type_stmt_def, expr_sim_inv_def, AllCaseEqs()] >>
  `~supported_exprs_exists
      (\e. ~is_extcode e /\ ~(byte_widths_expr e /\ alloc_limits_expr cenv e)) es /\
   call_evaluation_safe cx (int_calls_exprs es) /\
   (!target. supported_exprs_exists (expr_abi_decode_target_root target) es ==>
             occurs_abi_decode_target target tops)` by
    gvs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
        int_calls_stmt_def, AllCaseEqs()] >>
  `alloc_limits_exprs cenv es` by
    fs[stmt_exprs_ok_def, alloc_limits_stmt_def] >>
  `EVERY (\e. body_stmt_safe tops (Expr e) /\ ~is_extcode e) es` by
    (fs[body_stmt_safe_log_args, EVERY_CONJ] >>
     rw[EVERY_MEM] >> irule alloc_limits_expr_not_extcode >>
     metis_tac[exprSimSourceTheory.alloc_limits_exprs_mem]) >>
  qabbrev_tac `RR = \tail s. EVERY (\e. body_stmt_safe tops (Expr e) /\ ~is_extcode e) tail /\ body_exprs_mem_ok cx tail /\ expr_sim_inv cenv cx env s /\ supported_pure_exprs tops tail /\ well_typed_exprs env tail /\ ~supported_exprs_exists (\e. ~is_extcode e /\ ~(byte_widths_expr e /\ alloc_limits_expr cenv e)) tail /\ call_evaluation_safe cx (int_calls_exprs tail) /\ (!target. supported_exprs_exists (expr_abi_decode_target_root target) tail ==> occurs_abi_decode_target target tops)` >>
  irule compile_log_ready_stmt_frag_mem >>
  conj_tac >- (
    qexists_tac `RR` >> simp[Abbr `RR`] >>
    rpt gen_tac >> strip_tac >>
    irule (SIMP_RULE std_ss [DE_MORGAN_THM] log_mem_args_step) >>
    simp[]) >>
  conj_tac >- (
    qexistsl_tac [`MAP SND fields`, `h`, `MAP (SND o FST) fields`] >>
    simp[] >>
    qpat_x_assum `MAP expr_type _ = _` (mp_tac o Q.AP_TERM `LENGTH`) >>
    simp[]) >>
  qexists_tac `env` >> simp[]
QED

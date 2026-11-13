(* Memory case of the body induction (bodyMemory's body_mem_mutual): log. *)
Theory bodyMemLog
Ancestors
  allocLimitsProps exprSimSource
  bodyMemoryPreds stmtLogMemory bodySimLogArgs
  exprSimMemDefs exprSimHypsDefs bodyExprPreFacts bodySimStmtCases bodySim
  supportedExprs supportedExprTraverse supportedStmtTraverse supportedStmts
  supportedProgram vyperTypeCallGraph vyperTypeSystem vyperTypeExprResult
  vyperTypeInvariants vyperTypeExprSoundness vyperTypeCallStackSoundness
  gasContext allocLimits vyperInterpreter vyperState list

(* Memory twin of body_log_widen_case: compatible scalar argument bounds. *)
Theorem body_log_widen_mem_case:
  !d cx id args tops ctx func cenv env env' ret_ty lctx RetQ es fields.
    body_stmt_safe tops (Log id args) /\
    body_exprs_mem_ok cx args /\ body_inv tops ctx cenv cx /\
    supported_pure_exprs tops args /\
    supported_event_fields tops id = SOME fields /\
    EVERY supported_scalar_type (MAP (SND o FST) fields) /\
    LIST_REL (\e ((_,fty),_). event_arg_compatible fty (expr_type e)) args fields /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (Log id args) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (Log id args) = SOME env' /\
    stmt_exprs_ok cenv (Log id args) /\
    call_evaluation_safe cx (int_calls_stmt (Log id args)) ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Log id args)) (eval_stmt cx (Log id args)) es
Proof
  rpt strip_tac >>
  drule_all body_log_metadata >> strip_tac >>
  `LIST_REL event_arg_compatible (MAP (SND o FST) fields) (MAP expr_type args)` by
    (gvs[LIST_REL_EL_EQN, EL_MAP] >> rpt strip_tac >>
     first_x_assum (qspec_then `n` mp_tac) >> simp[] >>
     qabbrev_tac `fld = EL n fields` >> PairCases_on `fld` >> simp[]) >>
  `SUM (MAP (type_memory_bytes cenv)
          (log_non_indexed_types (MAP SND fields) (MAP expr_type args))) < dimword (:256) /\
   abi_size_bound cenv.ce_struct_fields
     (TupleT (log_non_indexed_types (MAP SND fields) (MAP expr_type args))) < dimword (:256)` by
    (gvs[stmt_exprs_ok_def, alloc_limits_stmt_def, log_alloc_ok_def] >>
     conj_tac >> irule arithmeticTheory.LESS_LESS_EQ_TRANS >>
     qexists_tac `2 ** 64` >> gvs[wordsTheory.dimword_def]) >>
  `well_typed_exprs env args /\
   !id t. FLOOKUP env.var_types id = SOME t ==>
     ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)` by
    gvs[type_stmt_def, expr_sim_inv_def, AllCaseEqs()] >>
  `~supported_exprs_exists
      (\e. ~is_extcode e /\ ~(byte_widths_expr e /\ alloc_limits_expr cenv e)) args /\
   call_evaluation_safe cx (int_calls_exprs args) /\
   (!target. supported_exprs_exists (expr_abi_decode_target_root target) args ==>
             occurs_abi_decode_target target tops)` by
    gvs[stmt_exprs_ok_flat, supported_stmt_expr_exists_def,
        int_calls_stmt_def, AllCaseEqs()] >>
  `alloc_limits_exprs cenv args` by
    fs[stmt_exprs_ok_def, alloc_limits_stmt_def] >>
  `EVERY (\e. body_stmt_safe tops (Expr e) /\ ~is_extcode e) args` by
    (fs[body_stmt_safe_log_args, EVERY_CONJ] >>
     rw[EVERY_MEM] >> irule alloc_limits_expr_not_extcode >>
     metis_tac[exprSimSourceTheory.alloc_limits_exprs_mem]) >>
  qabbrev_tac `RR = \tail s. EVERY (\e. body_stmt_safe tops (Expr e) /\ ~is_extcode e) tail /\ body_exprs_mem_ok cx tail /\ expr_sim_inv cenv cx env s /\ supported_pure_exprs tops tail /\ well_typed_exprs env tail /\ ~supported_exprs_exists (\e. ~is_extcode e /\ ~(byte_widths_expr e /\ alloc_limits_expr cenv e)) tail /\ call_evaluation_safe cx (int_calls_exprs tail) /\ (!target. supported_exprs_exists (expr_abi_decode_target_root target) tail ==> occurs_abi_decode_target target tops)` >>
  irule compile_log_ready_stmt_frag_mem_widen >>
  conj_tac >- (
    qexists_tac `RR` >> simp[Abbr `RR`] >>
    rpt gen_tac >> strip_tac >>
    rename1 `body_exprs_mem_ok cx (e::tail)` >>
    qmatch_goalsub_rename_tac `expr_sim_mem ctx func cenv cx (expr_type e) e s` >>
    qspecl_then [`tops`, `ctx`, `func`, `cenv`, `cx`, `env`, `e`, `tail`, `s`]
      mp_tac log_mem_args_step >> simp[DE_MORGAN_THM]) >>
  conj_tac >- (
    qexistsl_tac [`MAP SND fields`, `h`, `MAP (SND o FST) fields`] >> simp[]) >>
  qexists_tac `env` >> simp[]
QED

(* Memory counterpart of the non-scalar event data case. *)
Theorem body_log_aggregate_mem_case:
  !cx id es tops ctx cenv fields.
    body_stmt_safe tops (Log id es) /\
    body_exprs_mem_ok cx es /\ body_inv tops ctx cenv cx /\
    supported_event_fields tops id = SOME fields /\
    ~EVERY supported_scalar_type (MAP (SND o FST) fields) ==>
    body_stmt_mem_ok cx (Log id es)
Proof
  cheat
QED

Theorem body_log_mem_case:
  !cx id es. body_exprs_mem_ok cx es ==> body_stmt_mem_ok cx (Log id es)
Proof
  rw[body_stmt_mem_ok_def] >>
  rename1 `stmt_frag_mem _ _ _ _ _ _ _ _ _ st` >>
  `?fields. supported_event_fields tops id = SOME fields /\
            supported_pure_exprs tops es /\
            LIST_REL (\e ((_,fty),_).
              event_arg_compatible fty (expr_type e)) es fields` by
    (gvs[supported_stmt_def, supported_log_def, AllCaseEqs()] >>
     Cases_on `supported_event_fields tops id` >> gvs[]) >>
  reverse (Cases_on `EVERY supported_scalar_type (MAP (SND o FST) fields)`)
  >- (`body_stmt_mem_ok cx (Log id es)` by
        (drule_all body_log_aggregate_mem_case >> simp[]) >>
      fs[body_stmt_mem_ok_def] >> metis_tac[]) >>
  reverse (Cases_on `supported_log_exact tops id es`)
  >- (drule_all body_log_widen_mem_case >> simp[]) >>
  `MAP expr_type es = MAP (SND o FST) fields` by
    (gvs[supported_log_exact_def, AllCaseEqs()] >>
     Cases_on `supported_event_fields tops id` >> gvs[]) >>
  drule_all body_log_metadata >> strip_tac >>
  `SUM (MAP (type_memory_bytes cenv)
          (log_non_indexed_types (MAP SND fields)
             (MAP (SND o FST) fields))) < dimword (:256) /\
   abi_size_bound cenv.ce_struct_fields
     (TupleT (log_non_indexed_types (MAP SND fields)
                (MAP (SND o FST) fields))) < dimword (:256)` by
    (gvs[stmt_exprs_ok_flat, alloc_limits_stmt_def, log_alloc_ok_def] >>
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
    gvs[stmt_exprs_ok_flat, supported_stmt_expr_exists_def,
        int_calls_stmt_def, AllCaseEqs()] >>
  `alloc_limits_exprs cenv es` by
    fs[stmt_exprs_ok_def, alloc_limits_stmt_def] >>
  `EVERY (\e. body_stmt_safe tops (Expr e) /\ ~is_extcode e) es` by
    (fs[body_stmt_safe_log_args, EVERY_CONJ] >>
     rw[EVERY_MEM] >> irule alloc_limits_expr_not_extcode >>
     metis_tac[exprSimSourceTheory.alloc_limits_exprs_mem]) >>
  qabbrev_tac `RR = \tail s. EVERY (\e. body_stmt_safe tops (Expr e) /\ ~is_extcode e) tail /\ body_exprs_mem_ok cx tail /\ expr_sim_inv cenv cx env s /\ supported_pure_exprs tops tail /\ well_typed_exprs env tail /\ ~supported_exprs_exists (\e. ~is_extcode e /\ ~(byte_widths_expr e /\ alloc_limits_expr cenv e)) tail /\ call_evaluation_safe cx (int_calls_exprs tail) /\ (!target. supported_exprs_exists (expr_abi_decode_target_root target) tail ==> occurs_abi_decode_target target tops)` >>
  `~exprs_can_mutate cenv es` by metis_tac[supported_pure_expr_no_mutate] >>
  `EVERY (\e. is_bytestring_type (lowered_value_type cenv e) <=>
              is_bytestring_type (expr_type e)) es` by
    metis_tac[supported_pure_exprs_bytestring_iff] >>
  irule compile_log_ready_stmt_frag_mem >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (
    qexists_tac `RR` >> simp[Abbr `RR`] >>
    rpt gen_tac >> strip_tac >>
    rename1 `body_exprs_mem_ok cx (e::tail)` >>
    qmatch_goalsub_rename_tac `expr_sim_mem ctx func cenv cx (expr_type e) e s` >>
    qspecl_then [`tops`, `ctx`, `func`, `cenv`, `cx`, `env`, `e`, `tail`, `s`]
      mp_tac log_mem_args_step >> simp[DE_MORGAN_THM]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (
    qexistsl_tac [`MAP SND fields`, `h`, `MAP (SND o FST) fields`] >>
    simp[] >>
    qpat_x_assum `MAP expr_type _ = _` (mp_tac o Q.AP_TERM `LENGTH`) >>
    simp[]) >>
  qexists_tac `env` >> simp[]
QED

(* S1 Log dispatch: scalar fields retain the exact/compatible proofs;
   non-scalar event data uses its separate case. *)
Theory bodySimLog
Ancestors
  bodyLogDeclaredCapture stmtSimLogDeclaredSuffix stmtSimLogTrace stmtSimLogSource
  stmtSimLogCompose bodySimCallRawLog stmtSimDeclCompose logComposeFacts
  eventLogSplitProps typedLogSplitComplete abiLogSourceEncoding
  exprLoweringProps exprSimDefs fragGasMode fragGasPath freshWrites
  loweringPosts loweringStateRelDefs stmtLowering stmtSimDefs stmtSimProps
  stmtSimLogArgsGrowth stmtSimLogArgsRun gasContext gasOutcome gasSummary
  bodySimLogArgs whitelistLogWiden
  allocLimits allocLimitsProps
  exprSimSource bodyExprPreFacts exprSimHypsDefs list bodySim bodySimStmtCases stmtSimLog exprSimHyps
  compileEnv compileVyper supportedStmts supportedDecls supportedTypes
  supportedExprs supportedExprTraverse supportedStmtTraverse vyperEvent vyperInterpreter
  vyperState vyperTypeSystem supportedProgram supportedNames vyperContext
  vyperABI vyperTypeInvariants vyperTypeExprSoundness vyperTypeCallGraph
  vyperTypeCallStackSoundness exprLowering

(* Non-scalar event data is handled separately from scalar topics. *)
Theorem body_log_aggregate_case:
  !cx id es tops ctx cenv fields.
    body_stmt_safe tops (Log id es) /\
    body_exprs_ok cx es /\ body_inv tops ctx cenv cx /\
    supported_event_fields tops id = SOME fields /\
    ~EVERY supported_scalar_type (MAP (SND o FST) fields) ==>
    body_stmt_ok cx (Log id es)
Proof
  rpt strip_tac >> rename1 `body_exprs_ok cx args` >>
  rewrite_tac[body_stmt_ok_def] >>
  MAP_EVERY qx_gen_tac
    [`ts`, `bnds`, `cc`, `func`, `ce`, `env`, `env'`, `ret_ty`, `lctx`, `RetQ`, `es`] >>
  strip_tac >>
  `?fs. supported_event_fields ts id = SOME fs /\
    supported_pure_exprs ts args /\
    LIST_REL (\e ((name,dty),indexed).
      event_arg_compatible dty (expr_type e)) args fs` by
    (gvs[supported_stmt_def, supported_log_def, AllCaseEqs()] >>
     Cases_on `supported_event_fields ts id` >> gvs[]) >>
  `well_typed_exprs env args /\
   !name ty. FLOOKUP env.var_types name = SOME ty ==>
     ?p sz. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz)` by
    gvs[type_stmt_def, expr_sim_inv_def, AllCaseEqs()] >>
  `~supported_exprs_exists
      (\e. ~is_extcode e /\ ~(byte_widths_expr e /\ alloc_limits_expr ce e)) args /\
   call_evaluation_safe cx (int_calls_exprs args) /\
   (!target. supported_exprs_exists (expr_abi_decode_target_root target) args ==>
     occurs_abi_decode_target target ts)` by
    gvs[stmt_exprs_ok_flat, supported_stmt_expr_exists_def,
        int_calls_stmt_def, AllCaseEqs()] >>
  `alloc_limits_exprs ce args /\ log_alloc_ok ce id args` by
    fs[stmt_exprs_ok_def, alloc_limits_stmt_def] >>
  `EVERY (\e. body_stmt_safe ts (Expr e) /\ ~is_extcode e) args` by
    (fs[body_stmt_safe_log_args, EVERY_CONJ] >>
     rw[EVERY_MEM] >> irule alloc_limits_expr_not_extcode >>
     metis_tac[exprSimSourceTheory.alloc_limits_exprs_mem]) >>
  qspecl_then [`ts`, `cc`, `ce`, `cx`, `id`, `fs`]
    mp_tac body_log_aggregate_metadata >>
  impl_tac >- simp[] >> strip_tac >>
  rewrite_tac[stmt_frag_def, stmt_framed_frag_def] >>
  MAP_EVERY qx_gen_tac [`sa`, `sb`, `s0`, `ce'`] >> strip_tac >>
  `~cx.txn.is_static` by fs[stmt_state_rel_def, state_rel_def] >>
  gvs[stmt_env_def, declare_stmt_local_def, comp_bind_def, comp_return_def,
      comp_ignore_bind_def] >>
  pairarg_tac >> gvs[] >>
  Cases_on `compile_log_eval_all ce args sa` >>
  rename1 `compile_log_eval_all ce args sa = (ops,sm)` >>
  drule_all compile_log_eval_all_code >> strip_tac >>
  `~exprs_can_mutate ce args` by
    metis_tac[supported_pure_expr_no_mutate] >>
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by
    (drule_all compile_log_eval_all_grows >> simp[]) >>
  `local_ptrs_reserved ce sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `gas_admissible (eval_exprs cx args) log_args_res_ok es` by
    (drule_all log_arguments_admissible >>
     simp[gas_admissible_def, log_args_res_ok_def]) >>
  mp_tac (Q.INST
    [`tops` |-> `ts`, `ctx` |-> `cc`, `cenv` |-> `ce`, `cx` |-> `cx`,
     `env` |-> `env`, `args` |-> `args`, `id` |-> `id`, `fields` |-> `fs`,
     `es` |-> `es`, `sa` |-> `sa`, `sb` |-> `sm`, `ops` |-> `ops`,
     `func` |-> `func`, `s0` |-> `s0`] body_log_declared_capture) >>
  impl_tac >- simp[] >> disch_then assume_tac >>
  qpat_assum `~cx.txn.is_static`
    (rewrite_tac o single o MATCH_MP eval_log_nonstatic_bind) >>
  irule raw_log_outcome_bind_values >> goal_assum (drule_at Any) >>
  reverse conj_tac
  >- (MAP_EVERY qx_gen_tac [`res`, `ee`, `r`] >> strip_tac >>
      `?ex. res = INR ex` by (Cases_on `res` >> gvs[expr_exit_def]) >>
      gvs[] >> gen_tac >>
      rewrite_tac[stmt_exit_def] >> disj1_tac >>
      metis_tac[expr_exit_INR_type]) >>
  MAP_EVERY qx_gen_tac [`marks`, `rr`, `mid`, `t`] >> strip_tac >>
  gvs[Excl "enc_def"] >>
  `~t.vs_halted` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >>
     metis_tac[gas_marked_path_exec, gas_path_normal]) >>
  `LENGTH args = LENGTH vs` by metis_tac[LIST_REL_LENGTH, LENGTH_ZIP] >>
  `LIST_REL event_arg_compatible (MAP (SND o FST) fs) (MAP expr_type args)` by
    (fs[LIST_REL_EL_EQN, EL_MAP] >> rpt strip_tac >>
     Cases_on `EL n fs` >> rename1 `EL n fs = (decl_arg,indexed)` >>
     Cases_on `decl_arg` >> fs[] >>
     qpat_x_assum `!n. n < LENGTH fs ==> _`
       (qspec_then `n` mp_tac) >> simp[]) >>
  `EVERY (\(ty,indexed). indexed ==> supported_scalar_type ty)
    (ZIP (MAP (SND o FST) fs,MAP SND fs))` by
    (fs[EVERY_EL, EL_ZIP, EL_MAP, combinTheory.o_DEF] >>
     rpt strip_tac >> Cases_on `EL n fs` >>
     rename1 `EL n fs = (decl_arg,indexed)` >> Cases_on `decl_arg` >>
     qpat_x_assum `!n. n < LENGTH fs ==> if _ then _ else _`
       (qspec_then `n` mp_tac) >> simp[] >>
     Cases_on `indexed` >> simp[]) >>
  `LIST_REL (\ty v. ?tv. evaluate_type (get_tenv cx) ty = SOME tv /\
      value_has_type tv v) (MAP expr_type args) vs` by
    (fs[LIST_REL_EL_EQN, EL_ZIP, EL_MAP] >> rpt strip_tac >>
     Cases_on `EL n ops` >> Cases_on `EL n fs` >>
     rename1 `EL n fs = (decl_arg,indexed)` >> Cases_on `decl_arg` >>
     qpat_x_assum `!n. n < LENGTH ops /\ n < LENGTH vs ==> _`
       (qspec_then `n` mp_tac) >> simp[EL_ZIP] >> metis_tac[]) >>
  `LIST_REL (\ty v. ?tv. evaluate_type (get_tenv cx) ty = SOME tv /\
      value_has_type tv v)
    (log_non_indexed_types (MAP SND fs) (MAP (SND o FST) fs))
    (log_non_indexed_values (MAP SND fs) vs)` by
    (rewrite_tac[log_non_indexed_types_select, log_non_indexed_values_select] >>
     irule select_log_args_rel >> simp[] >>
     fs[LIST_REL_EL_EQN, EL_ZIP, EL_MAP, combinTheory.o_DEF] >>
     rpt strip_tac >> Cases_on `EL n ops` >>
     Cases_on `EL n fs` >> rename1 `EL n fs = (decl_arg,indexed)` >>
     Cases_on `decl_arg` >> fs[] >>
     qpat_x_assum `!n. n < LENGTH ops /\ n < LENGTH vs ==> _`
       (qspec_then `n` mp_tac) >> simp[EL_ZIP] >> metis_tac[]) >>
  `LENGTH (MAP SND fs) = LENGTH (MAP (SND o FST) fs)` by simp[] >>
  drule_all log_compatible_source_event_encoded >> strip_tac >>
  qabbrev_tac `ev = <|logger := cx.txn.target; topics := n2w h::topics;
    data := enc (Tuple (vyper_to_abi_types (get_tenv cx)
      (log_non_indexed_types (MAP SND fs) (MAP (SND o FST) fs))))
      (ListV avs)|>` >>
  `encode_source_event (get_tenv cx) cx.sources cx.txn.target id vs = SOME ev`
    by simp[Abbr `ev`] >>
  mp_tac (Q.INST
    [`tops` |-> `ts`, `ctx` |-> `cc`, `cenv` |-> `ce`, `cx` |-> `cx`,
     `env` |-> `env`, `es0` |-> `es`, `es` |-> `mid with gas_obs := []`,
     `s` |-> `t`, `args` |-> `args`, `fields` |-> `fs`, `id` |-> `id`,
     `ty` |-> `ret_ty`, `lctx` |-> `lctx`, `sa` |-> `sa`, `sm` |-> `sm`,
     `sb` |-> `cs'`, `ops` |-> `ops`, `func` |-> `func`,
     `h` |-> `h`, `topics` |-> `topics`, `avs` |-> `avs`]
      log_declared_suffix_path) >>
  impl_tac >- simp[] >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  `alloca_frame ce es sa s0 ce (mid with gas_obs := []) t` by
    (irule log_wb_alloca_frame >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[]) >>
  `stmt_post cc func cx lctx ce ce sa cs' es s0 (INL ())
    (mid with <|logs := mid.logs ++ [ev]; gas_obs := []|>) u` by
    (irule stmt_post_entry_frame >>
     qexistsl_tac [`mid with gas_obs := []`, `t`, `sm`] >>
     simp[Abbr `ev`] >> fs[wb_frame_def] >> metis_tac[not_fresh_at_mono]) >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INL ()`, `mid with logs := mid.logs ++ [ev]`, `OK u`] >>
  simp[gas_marked_exec_def, gas_marked_path_def, gas_explicit_def,
       bind_def, lift_option_def, return_def, push_log_def,
       Abbr `ev`, Excl "enc_def"]
QED

Theorem body_log_case:
  !cx id es. body_exprs_ok cx es ==> body_stmt_ok cx (Log id es)
Proof
  rw[body_stmt_ok_def] >>
  `?fields. supported_event_fields tops id = SOME fields /\
            supported_pure_exprs tops es /\
            LIST_REL (\e ((_,fty),_).
              event_arg_compatible fty (expr_type e)) es fields` by
    (gvs[supported_stmt_def, supported_log_def, AllCaseEqs()] >>
     Cases_on `supported_event_fields tops id` >> gvs[]) >>
  reverse (Cases_on `EVERY supported_scalar_type (MAP (SND o FST) fields)`)
  >- (`body_stmt_ok cx (Log id es)` by
        (drule_all body_log_aggregate_case >> simp[]) >>
      fs[body_stmt_ok_def] >> metis_tac[]) >>
  reverse (Cases_on `supported_log_exact tops id es`)
  >- (drule_all body_log_widen_case >> simp[]) >>
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
    (gvs[stmt_exprs_ok_flat, allocLimitsTheory.alloc_limits_stmt_def,
         allocLimitsTheory.log_alloc_ok_def] >>
     conj_tac >> irule arithmeticTheory.LESS_LESS_EQ_TRANS >>
     qexists_tac `2 ** 64` >> gvs[wordsTheory.dimword_def]) >>
  `well_typed_exprs env es /\
   !id t. FLOOKUP env.var_types id = SOME t ==>
     ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)` by
    gvs[type_stmt_def, expr_sim_inv_def, AllCaseEqs()] >>
  `alloc_limits_exprs cenv es` by
    fs[stmt_exprs_ok_def, alloc_limits_stmt_def] >>
  `EVERY (\e. body_stmt_safe tops (Expr e) /\ ~is_extcode e) es` by
    (fs[body_stmt_safe_log_args, EVERY_CONJ] >>
     rw[EVERY_MEM] >> irule alloc_limits_expr_not_extcode >>
     metis_tac[exprSimSourceTheory.alloc_limits_exprs_mem]) >>
  `~exprs_can_mutate cenv es` by metis_tac[supported_pure_expr_no_mutate] >>
  `EVERY (\e. is_bytestring_type (lowered_value_type cenv e) <=>
              is_bytestring_type (expr_type e)) es` by
    metis_tac[supported_pure_exprs_bytestring_iff] >>
  irule compile_log_stmt_frag >> simp[] >>
  conj_tac
  >- (qpat_x_assum `MAP expr_type _ = _` (mp_tac o Q.AP_TERM `LENGTH`) >>
      simp[]) >>
  conj_tac >- (qexists_tac `env` >> simp[]) >>
  qexists_tac `\s. expr_sim_inv cenv cx env s` >> simp[] >>
  irule body_log_args_ready >>
  gvs[type_stmt_def, stmt_exprs_ok_flat, supported_stmt_expr_exists_def,
      int_calls_stmt_def, AllCaseEqs()] >>
  metis_tac[]
QED

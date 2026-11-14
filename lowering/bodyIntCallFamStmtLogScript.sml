(* Seam 2 joint induction, a family leaf of the stmt step: Log.
   bodyIntCallFamStmtLogSuffixTheory.intcall_log_suffix_run is the frozen
   suffix run with its memory and allocation frame. *)
Theory bodyIntCallFamStmtLog
Ancestors
  bodyIntCallJointContract bodyIntCallFamStmtLogSuffix
  bodyIntCallFamStmtLogArgsFrame bodyIntCallFamStmtLogGas
  bodyIntCallFamStmtLogResource bodyIntCallFamStmtLogReady
  bodyIntCallFamStmtLogPost bodyIntCallFamStmtLogArgs
  bodyIntCallFamStmtLogMarked bodyIntCallFamStmtLogCounted bodyIntCallFamStmtLogCompose
  bodyIntCallJointStmtSeq stmtSimProps stmtSimDefs loweringPosts stmtLowering
  compileEnv loweringStateRelDefs emitHelper exprLoweringProps bodySimLog supportedStmts supportedExprs
  supportedStmtTraverse vyperTypeSystem vyperInterpreter vyperState
  exprSimHypsDefs gasOutcome gasContext stmtSimLogCompose freshWrites list
  vyperTypeCallGraph vyperTypeCallStackSoundness bodyExprPreFacts allocLimits
  supportedExprTraverse exprSimSubscriptMap bodySimLogArgs bodyIntCallFamStmtLogWiden
  vyperEventArgCompat

Theorem intcall_log_stmt_step:
  (!e. intcall_expr_producer fp e /\ intcall_forced_producer fp e /\
       intcall_map_producer fp e) /\
  (!ss. list_size stmt_size ss < stmt_size st ==>
         intcall_stmts_producer fp ss) /\
  (?n es. st = Log n es) ==>
  intcall_stmts_producer fp [st]
Proof
  strip_tac >> gvs[] >>
  simp[intcall_stmts_producer_def, eval_stmts_singleton] >>
  rpt gen_tac >> strip_tac >>
  gvs[supported_stmt_def] >>
  qpat_assum `supported_log _ _ _`
    (strip_assume_tac o REWRITE_RULE [supported_log_def]) >>
  qpat_x_assum `stmts_env _ _ _ _ _ = _` mp_tac >>
  simp[stmts_env_singleton, stmt_env_def, declare_stmt_local_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  Cases_on `supported_event_fields fp.jc_tops n` >> gvs[] >>
  drule_all body_log_metadata >> strip_tac >>
  rename1 `supported_event_fields _ _ = SOME fields` >>
  `LIST_REL event_arg_compatible (MAP (SND o FST) fields) (MAP expr_type es)` by
    (`LENGTH es = LENGTH fields` by metis_tac[LIST_REL_LENGTH] >>
     qpat_x_assum `LIST_REL _ es fields` mp_tac >>
     rw[LIST_REL_EL_EQN, EL_MAP] >>
     rename1 `i < LENGTH fields` >>
     first_x_assum (qspec_then `i` mp_tac) >>
     Cases_on `EL i fields` >> Cases_on `q` >> simp[]) >>
  suspend "widen"
QED

Resume intcall_log_stmt_step[widen]:
  `type_stmt env fp.jc_ret_ty (Log n es) = SOME env'` by
    fs[type_stmt_def, AllCaseEqs()] >>
  `~fp.jc_cx.txn.is_static` by
    fs[intcall_joint_res_def, intcall_expr_res_def, exprLoweringPropsTheory.stmt_state_rel_def,
       state_rel_def] >>
  `SUM (MAP (type_memory_bytes ce)
      (log_non_indexed_types (MAP SND fields) (MAP (SND o FST) fields))) < dimword (:256) /\
   abi_size_bound ce.ce_struct_fields
      (TupleT (log_non_indexed_types (MAP SND fields) (MAP (SND o FST) fields))) <
     dimword (:256)` by
    (fs[bodySimTheory.stmt_exprs_ok_def, alloc_limits_stmt_def, log_alloc_ok_def] >>
     fs[wordsTheory.dimword_def]) >>
  `EVERY (supported_expr fp.jc_tops) es` by
    (fs[supported_pure_exprs_every, EVERY_MEM, supported_expr_def] >> metis_tac[]) >>
  `EVERY (\e. calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr e)) es` by
    (fs[int_calls_stmt_def, calls_follow_call_graph_def, EVERY_MEM] >>
     metis_tac[exprSimSourceTheory.int_calls_exprs_every_mem, EVERY_MEM]) >>
  `env' = env` by fs[type_stmt_def, AllCaseEqs()] >>
  `EVERY (\e. expr_body_pre ce fp.jc_cx env e es') es` by
    (irule intcall_log_args_body_pre >>
     fs[intcall_joint_res_def, intcall_expr_res_def, supported_stmts_expr_exists_list] >>
     conj_tac
     >- (fs[int_calls_stmt_def, intcall_frame_ok_def] >>
         metis_tac[call_evaluation_safe_def]) >>
     metis_tac[]) >>
  `LENGTH (MAP SND fields) = LENGTH es` by
    (imp_res_tac LIST_REL_LENGTH >> fs[]) >>
  `well_typed_exprs env es` by fs[type_stmt_def, AllCaseEqs()] >>
  `~exprs_can_mutate ce es` by metis_tac[supported_pure_expr_no_mutate] >>
  `EVERY (\e. is_bytestring_type (lowered_value_type ce e) <=>
              is_bytestring_type (expr_type e)) es` by
    metis_tac[supported_pure_exprs_bytestring_iff] >>
  drule_all log_compile_structure_compat >> strip_tac >>
  suspend "widen_compose"
QED

Resume intcall_log_stmt_step[widen_compose]:
  `gas_admissible (eval_exprs fp.jc_cx es) log_args_res_ok es'` by
    metis_tac[log_args_admissible] >>
  `EVERY supported_scalar_type (MAP expr_type es)` by
    metis_tac[compatible_scalar_types] >>
  `!e. intcall_forced_producer fp e` by metis_tac[] >>
  qpat_assum `intcall_joint_res _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [intcall_joint_res_def]) >>
  drule_all intcall_compile_log_eval_all >> strip_tac >>
  `sa.cs_next_var <= sm.cs_next_var` by
    metis_tac[stmtSimLogArgsGrowthTheory.compile_log_eval_all_grows] >>
  `MAP FST ys = MAP FST xs` by
    (qpat_assum `xs = ZIP _` SUBST1_TAC >>
     qpat_assum `LENGTH (MAP SND fields) = LENGTH es` mp_tac >>
     qpat_assum `LENGTH ys = LENGTH es` mp_tac >>
     simp_tac std_ss [LENGTH_MAP] >> rpt strip_tac >>
     asm_simp_tac std_ss [MAP_ZIP, LENGTH_MAP]) >>
  qpat_assum `MAP FST ys = _`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  `EVERY supported_scalar_type (MAP SND xs)` by
    (qpat_assum `MAP SND xs = _` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  qpat_assum `MAP SND xs = _` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [GSYM th])) >>
  `LENGTH (MAP SND fields) = LENGTH xs` by simp[] >>
  drule_all intcall_log_counted_compose >> strip_tac >>
  `EVERY (supported_scalar_type o SND) xs` by
    fs[EVERY_MAP, combinTheory.o_DEF] >>
  `~block_is_terminated cs'` by metis_tac[log_stmt_open] >>
  irule gas_outcome_conseq >>
  goal_assum (drule_at Any) >> simp[] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  simp[stmt_lands_def, cenv_top_ext_refl]
QED

Finalise intcall_log_stmt_step

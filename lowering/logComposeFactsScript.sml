(* Public compiler/source boundaries for readiness-parametric Log composition.
   S1's analogous facts are local to stmtSimLogCompose, not exported. *)
Theory logComposeFacts
Ancestors
  stmtSimLogSuffixCode stmtSimLogArgsGrowth stmtSimLogSource stmtSimLogTrace
  stmtSimLogTopics stmtSimLogArgs compileEnv stmtLowering context
  exprLoweringProps emitHelperProps loweringSlice stmtSimDefs stmtSimProps
  exprSimDefs vyperInterpreter vyperState gasSummary gasOutcome
  list rich_list venomInst emitHelper fragExec gasContext

Theorem log_emit_not_terminated:
  emit_inst LOG ops [] sa = ((),sb) ==> ~block_is_terminated sb
Proof
  simp[emit_inst_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, emit_def] >> strip_tac >> gvs[] >>
  Cases_on `sa.cs_current_insts` >>
  simp[block_is_terminated_def, LAST_APPEND, LAST_CONS_cond,
       mk_inst_def, is_terminator_def]
QED

Theorem eval_log_nonstatic_bind:
  ~cx.txn.is_static ==>
  eval_stmt cx (Log id args) =
    bind (eval_exprs cx args)
      (\vs. bind (lift_option (encode_source_event (get_tenv cx) cx.sources
                                 cx.txn.target id vs) "Log encode event")
                 push_log)
Proof
  strip_tac >> simp[Once evaluate_def] >>
  simp[FUN_EQ_THM, bind_def, ignore_bind_def] >> rpt gen_tac >>
  rpt (CASE_TAC >> gvs[])
QED

Theorem log_arguments_admissible:
  ~cx.txn.is_static /\
  gas_admissible (eval_stmt cx (Log id args)) (stmt_res_ok lctx) es ==>
  gas_admissible (eval_exprs cx args)
    (\r. !exc. r = INR exc ==> expr_res_ok (INR exc : value + exception)) es
Proof
  rw[gas_admissible_def] >>
  `eval_stmt cx (Log id args) (es with gas_obs := gs) = (INR exc, ee)` by
    simp[log_eval_outcome] >>
  first_x_assum drule >> strip_tac >> metis_tac[log_argument_error_ok]
QED

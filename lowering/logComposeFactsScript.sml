(* Public compiler/source boundaries for readiness-parametric Log composition.
   S1's analogous facts are local to stmtSimLogCompose, not exported. *)
Theory logComposeFacts
Ancestors
  stmtSimLogSuffixCode stmtSimLogArgsGrowth stmtSimLogSource stmtSimLogTrace
  stmtSimLogTopics stmtSimLogArgs compileEnv stmtLowering context
  exprLoweringProps emitHelperProps loweringSlice stmtSimDefs stmtSimProps
  exprSimDefs vyperInterpreter vyperState gasSummary gasOutcome
  list rich_list venomInst emitHelper fragExec gasContext

Theorem log_compile_decompose:
  cenv.ce_event_info (nsid_to_string id) = SOME (h,MAP expr_type args,flags) /\
  LENGTH flags = LENGTH args /\ EVERY supported_scalar_type (MAP expr_type args) /\
  compile_stmt cenv lctx ty (Log id args) sa = ((),sb) /\
  fn_has_code sa sb func ==>
  ?xs sm ops st. compile_log_eval_all cenv args sa = (xs,sm) /\
    compile_log_topic_ops (FST (split_log_ops xs flags)) sm = (ops,st) /\
    MAP SND xs = MAP expr_type args /\ LENGTH flags = LENGTH xs /\
    inst_extends sm sb /\ same_blocks sm sb /\ sm.cs_next_var <= sb.cs_next_var /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sm sb) /\ cs_extends sa sm /\ cs_extends sm sb /\
    fn_has_code sa sm func /\ fn_has_code sm sb func
Proof
  strip_tac >> Cases_on `compile_log_eval_all cenv args sa` >>
  rename1 `compile_log_eval_all cenv args sa = (xs,sm)` >>
  Cases_on `compile_log_topic_ops (FST (split_log_ops xs flags)) sm` >>
  rename1 `compile_log_topic_ops _ sm = (ops,st)` >>
  `MAP SND xs = MAP expr_type args` by
    (drule compile_log_eval_all_types >> simp[]) >>
  `LENGTH xs = LENGTH args` by metis_tac[LENGTH_MAP] >>
  `EVERY (supported_scalar_type o SND) xs` by
    (`EVERY supported_scalar_type (MAP SND xs)` by metis_tac[] >>
     gvs[EVERY_MAP, combinTheory.o_DEF]) >>
  `LENGTH flags = LENGTH xs` by decide_tac >>
  drule_all log_success_suffix_code >> strip_tac >>
  `cs_extends sa sm` by (drule compile_log_eval_all_grows >> simp[]) >>
  `cs_extends sm sb` by
    (irule cs_extends_same_block >>
     gvs[same_blocks_def, inst_extends_def, IS_PREFIX_APPEND] >> metis_tac[]) >>
  qexistsl_tac [`xs`, `sm`, `ops`, `st`] >> simp[] >>
  metis_tac[fn_has_code_mid, cs_extends_refl]
QED

Theorem log_emit_not_terminated:
  emit_inst LOG ops [] sa = ((),sb) ==> ~block_is_terminated sb
Proof
  simp[emit_inst_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, emit_def] >> strip_tac >> gvs[] >>
  Cases_on `sa.cs_current_insts` >>
  simp[block_is_terminated_def, LAST_APPEND, LAST_CONS_cond,
       mk_inst_def, is_terminator_def]
QED

Theorem log_compiled_not_terminated:
  cenv.ce_event_info (nsid_to_string id) = SOME (h,tys,flags) /\
  compile_log_eval_all cenv args sa = (xs,sm) /\
  compile_log_topic_ops (FST (split_log_ops xs flags)) sm = (ops,st) /\
  compile_stmt cenv lctx ty (Log id args) sa = ((),sb) ==>
  ~block_is_terminated sb
Proof
  strip_tac >> Cases_on `SND (split_log_ops xs flags) = []`
  >- (drule_all compile_log_empty_trace >> strip_tac >>
      qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >> simp[] >>
      metis_tac[log_emit_not_terminated]) >>
  drule_all (SRULE [] (Q.INST [`data_ops` |-> `SND (split_log_ops xs flags)`]
    compile_log_data_trace)) >> strip_tac >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >> simp[] >>
  strip_tac >> drule log_emit_not_terminated >> simp[]
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

Theory runtimeSymSrcStatementLogs
Ancestors
  runtimeSymSrcInterfaces runtimeSymSrcEmission runtimeSymSrcContext runtimeSymSrcContextComplete
  runtimeSymSrcExternalArgStaging runtimeSymSrcExternalPrimitive runtimeLabelExprCallbacks
  eventLoweringStructure stmtLowering compileEnv context venomInst stackPlanTypes
  list rich_list supportedStmts supportedStmtTraverse supportedExprs
  supportedExprTraverse

Theorem runtime_sym_log_saved_topics[local]:
  !rows s topics s'. runtime_sym_env tops ce /\
    EVERY (runtime_sym_value o FST) rows /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_log_saved_topics ce rows s = (topics,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\
    EVERY (\op. ~is_label_operand op) topics
Proof
  Induct >- simp[compile_log_saved_topics_def, comp_return_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[compile_log_saved_topics_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  drule_all runtime_sym_unwrap_value >> strip_tac >>
  drule_all runtime_sym_encode_log_topic >> strip_tac >>
  first_x_assum drule_all >> gvs[]
QED

Theorem runtime_sym_stmt_log:
  (!e. MEM e args ==> runtime_sym_expr_contract tops compile_expr ce (expr_type e) e) /\
  (!b v info s op s'. ~is_label_operand b /\ ~is_label_operand v /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_abi_encode_to_buf b v info s = (op,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) ==>
  runtime_sym_stmt_contract tops bindings compile_stmt ce lc ty (Log id args)
Proof
  strip_tac >> pure_rewrite_tac[runtime_sym_stmt_contract_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `ce.ce_event_info (nsid_to_string id)`
  >- (qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
      simp[Once compile_stmt_def] >> strip_tac >>
      irule runtime_sym_emit_inst >> goal_assum (drule_at Any) >> qexists `0` >>
      simp[runtime_sym_ordinary_inst]) >>
  PairCases_on `x` >>
  drule_all compile_log_stmt_trace >> simp[LET_THM, pairTheory.ELIM_UNCURRY] >>
  disch_then (qx_choose_then `saved` (qx_choose_then `sm`
    (qx_choose_then `topics` (qx_choose_then `st` strip_assume_tac)))) >>
  `EVERY runtime_sym_inst (state_insts sm) /\ EVERY runtime_sym_value saved` by
    (drule_at (Pat `compile_ext_call_args _ _ _ _ _ _ = _`)
       runtime_sym_ext_call_args >> disch_then irule >> simp[] >>
     conj_tac >- fs[supported_stmt_expr_exists_def] >>
     qexists_tac `tops` >>
     fs[supported_stmt_def, supported_log_def, supported_pure_exprs_every]) >>
  `EVERY (runtime_sym_value o FST)
      (FST (split_log_ops (ZIP (saved,MAP (lowered_value_type ce) args)) x2)) /\
   EVERY (runtime_sym_value o FST)
      (SND (split_log_ops (ZIP (saved,MAP (lowered_value_type ce) args)) x2))` by
    (irule every_split_log_ops >> simp[rb_every_zip_fst]) >>
  drule_all runtime_sym_log_saved_topics >> strip_tac
  >- (irule runtime_sym_emit_inst >> goal_assum (drule_at Any) >> qexists `0` >>
      goal_assum (drule_at Any) >> irule runtime_sym_ordinary_inst >>
      simp[EVERY_APPEND, EVERY_REVERSE, is_label_operand_def]) >>
  drule_all runtime_sym_alloc_buffer >> strip_tac >>
  drule runtime_sym_abi_encode_values_to_buf >>
  disch_then (qspecl_then [`tops`,`ce`,`buf.buf_operand`,
    `SND (split_log_ops (ZIP (saved,MAP (lowered_value_type ce) args)) x2)`,
    `sb`,`len`,`se`] mp_tac) >>
  impl_tac >- fs[combinTheory.o_DEF] >> strip_tac >>
  irule runtime_sym_emit_inst >> goal_assum (drule_at Any) >> qexists `0` >>
  goal_assum (drule_at Any) >> irule runtime_sym_ordinary_inst >>
  simp[EVERY_APPEND, EVERY_REVERSE, is_label_operand_def]
QED

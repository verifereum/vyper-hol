(* Bind counted arguments to counted event emission, keeping exemptions separate. *)
Theory bodyIntCallFamStmtLogCompose
Ancestors
  bodyIntCallJointContract bodyIntCallFamStmtLogCounted
  stmtSimLogCompose stmtSimLogSource stmtSimLogArgs
  exprSimRawLogSimCompose exprSimSubscriptMap exprSimDefs
  gasOutcome gasSummary gasContext vyperState vyperInterpreter
  freshWrites loweringSlice venomState list rich_list

Theorem intcall_log_counted_compose:
  ce.ce_event_info (nsid_to_string id) = SOME (h,MAP SND xs,flags) /\
  lookup_event_metadata (get_tenv fp.jc_cx) fp.jc_cx.sources fp.jc_cx.txn.target id =
    SOME (h,MAP SND xs,flags) /\
  EVERY supported_scalar_type (MAP SND xs) /\
  LENGTH flags = LENGTH xs /\ LENGTH (FILTER I flags) <= 3 /\
  SUM (MAP (type_memory_bytes ce) (log_non_indexed_types flags (MAP SND xs))) < dimword (:256) /\
  abi_size_bound ce.ce_struct_fields (TupleT (log_non_indexed_types flags (MAP SND xs))) < dimword (:256) /\
  compile_log_eval_all ce args sa = (xs,sm) /\
  compile_log_topic_ops (FST (split_log_ops xs flags)) sm = (ops,st) /\
  compile_stmt ce lctx ty (Log id args) sa = ((),sb) /\
  intcall_frame_ok fp /\ sm.cs_next_var <= sb.cs_next_var /\
  sa.cs_next_var <= sm.cs_next_var /\
  fn_has_code sm sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  same_blocks sm sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sm sb) /\ ~fp.jc_cx.txn.is_static /\
  gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (eval_exprs fp.jc_cx args) (es,s0)
    (\res ee u. ?vs. res = INL vs /\
      log_args_post fp.jc_ctx fp.jc_func ce fp.jc_cx es sa sm s0 ee xs vs u /\
      intcall_expr_cont fp ce env es sa s0 ee sm u /\
      LIST_REL (\ty v. ?tv. evaluate_type (get_tenv fp.jc_cx) ty = SOME tv /\ value_has_type tv v) (MAP SND xs) vs /\
      EVERY (\p. (!z. FST p = Var z ==> not_fresh_at sm z) /\ (!lab. FST p <> Label lab)) xs)
    (\res ee r. expr_exit res r) ==>
  gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (eval_stmt fp.jc_cx (Log id args)) (es,s0)
    (\res ee u. res = INL () /\
      intcall_joint_res fp ce env ee sb u /\ ~u.vs_halted /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
             lookup_var x u = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
               FLOOKUP u.vs_allocas aid = SOME b) /\
      s0.vs_alloca_next <= u.vs_alloca_next)
    (intcall_stmt_exit fp)
Proof
  strip_tac >> simp[eval_log_bind] >>
  irule raw_log_topics_bind >>
  qexists_tac `\vs ee u.
    log_args_post fp.jc_ctx fp.jc_func ce fp.jc_cx es sa sm s0 ee xs vs u /\
    intcall_expr_cont fp ce env es sa s0 ee sm u /\
    LIST_REL (\ty v. ?tv. evaluate_type (get_tenv fp.jc_cx) ty = SOME tv /\ value_has_type tv v) (MAP SND xs) vs /\
    EVERY (\p. (!z. FST p = Var z ==> not_fresh_at sm z) /\ (!lab. FST p <> Label lab)) xs` >>
  reverse conj_tac
  >- (irule gas_outcome_conseq >> goal_assum (drule_at Any) >>
      simp[] >> rpt gen_tac >> strip_tac >>
      Cases_on `res` >> fs[expr_exit_INL] >>
      fs[intcall_stmt_exit_def, stmtSimPropsTheory.expr_exit_INR_type]) >>
  rpt gen_tac >> strip_tac >>
  fs[] >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` kall_tac >>
  `LENGTH flags = LENGTH (MAP SND xs)` by simp[] >>
  drule_all log_source_event_encoded >> strip_tac >>
  `LIST_REL (\arg v. log_arg_rel ce fp.jc_cx sa sm
       (mid with gas_obs := []) t arg v /\ supported_scalar_type (SND arg) /\
       ?tv. evaluate_type (get_tenv fp.jc_cx) (SND arg) = SOME tv /\
            value_has_type tv v) xs vs` by
    (fs[log_args_post_def, LIST_REL_EL_EQN, EVERY_EL, EL_MAP] >>
     rpt strip_tac >> simp[] >> metis_tac[]) >>
  `intcall_joint_res fp ce env (mid with gas_obs := []) sm t /\
   ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
   t.vs_inst_idx = LENGTH sm.cs_current_insts` by
    fs[intcall_expr_cont_def] >>
  irule gas_outcome_conseq >>
  qexistsl_tac [`\res ee u. res = INL () /\
    intcall_joint_res fp ce env ee sb u /\ ~u.vs_halted /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x w. not_fresh_at sm x /\ lookup_var x t = SOME w ==>
       lookup_var x u = SOME w) /\
    (!aid b. FLOOKUP t.vs_allocas aid = SOME b ==>
       FLOOKUP u.vs_allocas aid = SOME b) /\
    t.vs_alloca_next <= u.vs_alloca_next`, `intcall_stmt_exit fp`] >>
  conj_tac >- simp[] >>
  reverse conj_tac
  >- (irule intcall_log_suffix_counted >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  simp[] >> rpt gen_tac >> strip_tac >>
  fs[intcall_expr_cont_def] >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    metis_tac[not_fresh_at_mono] >>
  metis_tac[]
QED

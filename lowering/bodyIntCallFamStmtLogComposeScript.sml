(* Bind counted arguments to counted event emission, keeping exemptions separate. *)
Theory bodyIntCallFamStmtLogCompose
Ancestors
  bodyIntCallJointContract bodyIntCallFamStmtLogCounted
  stmtSimLogCompose stmtSimLogSource stmtSimLogArgs
  whitelistLogWiden vyperEventArgCompat vyperEventCompatibility
  bodyIntCallFamStmtLogWiden
  exprSimRawLogSimCompose exprSimSubscriptMap exprSimDefs
  gasOutcome gasSummary gasContext vyperState vyperInterpreter
  freshWrites loweringSlice venomState list rich_list
Libs
  logWidenTacticsLib

Theorem intcall_log_counted_compose:
  ce.ce_event_info (nsid_to_string id) = SOME (h,MAP SND xs,flags) /\
  lookup_event_metadata (get_tenv fp.jc_cx) fp.jc_cx.sources fp.jc_cx.txn.target id =
    SOME (h,MAP SND xs,flags) /\
  EVERY supported_scalar_type (MAP SND xs) /\
  LIST_REL event_arg_compatible (MAP SND xs) (MAP expr_type args) /\
  LENGTH flags = LENGTH xs /\ LENGTH (FILTER I flags) <= 3 /\
  SUM (MAP (type_memory_bytes ce) (log_non_indexed_types flags (MAP SND xs))) < dimword (:256) /\
  abi_size_bound ce.ce_struct_fields (TupleT (log_non_indexed_types flags (MAP SND xs))) < dimword (:256) /\
  log_eval_view ce args sa xs sm /\
  compile_log_topic_ops (FST (split_log_ops xs flags)) sm = (ops,st) /\
  compile_stmt ce lctx ty (Log id args) sa = ((),sb) /\
  intcall_frame_ok fp /\ ce_locals_declared ce env /\ sm.cs_next_var <= sb.cs_next_var /\
  sa.cs_next_var <= sm.cs_next_var /\
  fn_has_code sm sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  same_blocks sm sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sm sb) /\ ~fp.jc_cx.txn.is_static /\
  gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (eval_exprs fp.jc_cx args) (es,s0)
    (\res ee u. ?vs. res = INL vs /\
      log_args_post fp.jc_ctx fp.jc_func ce fp.jc_cx es sa sm s0 ee
        (ZIP (MAP FST xs, MAP expr_type args)) vs u /\
      intcall_expr_cont fp ce env es sa s0 ee sm u /\
      LIST_REL (\ty v. ?tv. evaluate_type (get_tenv fp.jc_cx) ty = SOME tv /\ value_has_type tv v) (MAP expr_type args) vs /\
      EVERY (\p. (!z. FST p = Var z ==> not_fresh_at sm z) /\ (!lab. FST p <> Label lab))
        (ZIP (MAP FST xs, MAP expr_type args)))
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
    log_args_post fp.jc_ctx fp.jc_func ce fp.jc_cx es sa sm s0 ee
      (ZIP (MAP FST xs, MAP expr_type args)) vs u /\
    intcall_expr_cont fp ce env es sa s0 ee sm u /\
    LIST_REL (\ty v. ?tv. evaluate_type (get_tenv fp.jc_cx) ty = SOME tv /\ value_has_type tv v) (MAP expr_type args) vs /\
    EVERY (\p. (!z. FST p = Var z ==> not_fresh_at sm z) /\ (!lab. FST p <> Label lab))
      (ZIP (MAP FST xs, MAP expr_type args))` >>
  reverse conj_tac
  >- (irule gas_outcome_conseq >> goal_assum (drule_at Any) >>
      simp[] >> rpt gen_tac >> strip_tac >>
      Cases_on `res` >> fs[expr_exit_INL] >>
      fs[intcall_stmt_exit_def, stmtSimPropsTheory.expr_exit_INR_type]) >>
  rpt gen_tac >> strip_tac >>
  fs[] >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` kall_tac >>
  suspend "values"
QED

Resume intcall_log_counted_compose[values]:
  rename1 `log_eval_view cenv args sa ds sm` >>
  qabbrev_tac `cx = fp.jc_cx` >>
  qabbrev_tac `tys = MAP SND ds` >>
  qabbrev_tac `axs = ZIP (MAP FST ds, MAP expr_type args)` >>
  `LENGTH flags = LENGTH tys` by simp[Abbr `tys`] >>
  `LENGTH ds = LENGTH args` by
    (imp_res_tac LIST_REL_LENGTH >> fs[Abbr `tys`]) >>
  drule_all log_source_event_encoded_widen >> strip_tac >>
  `LIST_REL (\arg v. supported_scalar_type (SND arg) /\
    ?aty tv. event_arg_compatible (SND arg) aty /\ supported_scalar_type aty /\
      log_arg_rel cenv cx sa sm (mid with gas_obs := []) t (FST arg,aty) v /\
      evaluate_type (get_tenv cx) aty = SOME tv /\ value_has_type tv v /\
      (is_bytestring_type aty <=> is_bytestring_type (SND arg)) /\
      encode_event_topic aty v = encode_event_topic (SND arg) v) ds vs` by
    (gvs[log_args_post_def, LIST_REL_EL_EQN, EVERY_EL, EL_MAP,
         Abbr `axs`, Abbr `tys`, EL_ZIP, Excl "enc_def"] >>
     rpt strip_tac >> qexists_tac `expr_type (EL n args)` >>
     qpat_x_assum `!n. n < LENGTH vs ==> ?tv. _`
       (qspec_then `n` mp_tac) >> simp[] >> strip_tac >>
     qexists_tac `tv` >> simp[] >>
     `supported_scalar_type (SND (EL n ds))` by simp[] >>
     `event_arg_compatible (SND (EL n ds)) (expr_type (EL n args))` by simp[] >>
     drule_all compatible_scalar_type >> strip_tac >>
     drule_all scalar_event_arg_compatible >> simp[]) >>
  `LIST_REL (\arg v. log_arg_rel cenv cx sa sm (mid with gas_obs := []) t arg v /\
    supported_scalar_type (SND arg) /\
    ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\ value_has_type tv v)
    (SND (split_log_ops ds flags)) (log_non_indexed_values flags vs)` by
    logWidenTacticsLib.selected_data (CONJUNCT1 event_arg_compatible_scalar_cases) >>
  `encode_indexed_event_topics flags tys vs = SOME topics /\
   vyper_to_abi_list (get_tenv cx) (log_non_indexed_types flags tys)
     (log_non_indexed_values flags vs) = SOME avs /\
   vyper_to_abi_types (get_tenv cx) (log_non_indexed_types flags tys) =
     vyper_to_abi_types (get_tenv cx) (log_non_indexed_types flags (MAP expr_type args))` by
    logWidenTacticsLib.encoding_facts scalar_event_arg_compatible >>
  `LIST_REL (\arg v. supported_scalar_type (SND arg) /\
    ?aty tv. supported_scalar_type aty /\
      log_arg_rel cenv cx sa sm (mid with gas_obs := []) t (FST arg,aty) v /\
      evaluate_type (get_tenv cx) aty = SOME tv /\ value_has_type tv v /\
      (is_bytestring_type aty <=> is_bytestring_type (SND arg)) /\
      encode_event_topic aty v = encode_event_topic (SND arg) v) ds vs` by
    (irule LIST_REL_mono >> first_assum (irule_at Any) >> simp[] >> metis_tac[]) >>
  `EVERY (\p. (!z. FST p = Var z ==> not_fresh_at sm z) /\
    (!lab. FST p <> Label lab)) ds` by
    (gvs[EVERY_EL, Abbr `axs`, EL_ZIP, EL_MAP, Excl "enc_def"] >> metis_tac[]) >>
  qunabbrev_tac `tys` >> qunabbrev_tac `cx` >>
  suspend "suffix"
QED

Resume intcall_log_counted_compose[suffix]:
  `intcall_joint_res fp cenv env (mid with gas_obs := []) sm t /\
   ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
   t.vs_inst_idx = LENGTH sm.cs_current_insts` by
    fs[intcall_expr_cont_def, intcall_joint_res_def] >>
  irule gas_outcome_conseq >>
  qexistsl_tac [`\res ee u. res = INL () /\
    intcall_joint_res fp cenv env ee sb u /\ ~u.vs_halted /\
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

Finalise intcall_log_counted_compose

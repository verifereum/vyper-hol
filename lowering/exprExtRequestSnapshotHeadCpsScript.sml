(* Single immediate-read producer/snapshot boundary. *)
Theory exprExtRequestSnapshotHeadCps
Ancestors
  exprExtRequestSnapshotCellIntro exprExtRequestSnapshotWord
  exprExtRequestSnapshotNonword exprExtRequestKwargCps
  exprExtRequestStrongCapture exprExtRequestHistoryCompose
  exprExtRequestJointUnwrap exprExtRequestReadProbe exprExtRequestTypedCells
  exprLowering exprLoweringProps loweringPosts compileEnv context
  exprSimHypsDefs exprSimDefs exprSimSource exprSafeOperand
  memoryLocalRhsProps valueEncodingTyping vyperTyping gasSummary
  fragGasMode fragGasPath vyperState vyperInterpreter
  bodyIntCallCompilerTags exprSimHyps abiEncodeArgsSim exprExtRequestHistory
  exprSimMemorySource aggregateEvaluatedLayout

Theorem extrequest_snapshot_read_endpoint[local]:
  expr_body_pre ce cx env e es /\ ~expr_has_effect e /\
  compile_expr ce (expr_type e) e sa = (vv,sc) /\
  vv_post ctx func ce cx e es sa sc s0 ee r vv t /\
  extrequest_strong_capture ctx func ce cx e r vv ee sc t /\
  stmt_state_rel ctx func ce cx ee t /\ ee.gas_obs = [] /\
  read_result cx r ee = (INL v,ee) /\
  value_runtime_typed env (expr_type e) v /\
  value_runtime_typed env (lowered_value_type ce e) v /\
  compile_snapshot_vv ce F (ext_call_arg_value (lowered_value_type ce e) vv) sc = (sv,sb) /\
  (case vv of StackValue ty a => safe_operand sc a
    | LocatedValue ty p => safe_operand sc p.ptr_operand) /\
  (!ty p tr w tv. vv = LocatedValue ty p /\ p.ptr_location = slot_loc tr /\
    eval_operand p.ptr_operand t = SOME w /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
    storage_read_live cx tr (get_storage cx ee tr) w tv) /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sc /\
  sa.cs_next_var <= sc.cs_next_var /\ sa.cs_next_id <= sc.cs_next_id /\
  fn_has_code sc sb func /\ fn_inst_ids_distinct func /\
  ~t.vs_halted /\ t.vs_current_bb = sc.cs_current_bb /\
  t.vs_inst_idx = LENGTH sc.cs_current_insts ==>
  ?u tv. gas_marked_exec F (ctx,func) (read_result cx r) (ee,t) [] (INL v) ee (OK u) /\
    extrequest_snapshot_cell ctx func ce cx ee sb u (sv,lowered_value_type ce e,tv,v) /\
    stmt_state_rel ctx func ce cx ee u /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    extrequest_history_frame ce cx ee sc t ee sb u
Proof
  strip_tac >>
  `vv_type vv = expr_type e` by
    (drule intcall_compile_expr_tag >>
     disch_then (qspecl_then [`expr_type e`, `sa`, `ce`] mp_tac) >> simp[]) >>
  Cases_on `is_word_type (lowered_value_type ce e)`
  >- suspend "word" >>
  `~is_word_type (vv_type (ext_call_arg_value (lowered_value_type ce e) vv))` by
    (Cases_on `vv` >> gvs[vv_type_def, ext_call_arg_value_def] >>
     metis_tac[expr_body_pre_lowered_fits, arg_type_fits_word_type]) >>
  `sv = ext_call_arg_value (lowered_value_type ce e) vv /\ sb = sc` by
    metis_tac[exprExtRequestSnapshotProbeTheory.extrequest_snapshot_nonword_no_copy,
      pairTheory.PAIR_EQ] >> gvs[] >>
  rename1 `compile_expr ce (expr_type e) e sa = (vv,sc)` >>
  `?tv. extrequest_snapshot_cell ctx func ce cx ee sc t
      (ext_call_arg_value (lowered_value_type ce e) vv,lowered_value_type ce e,tv,v)` by
    (irule extrequest_snapshot_cell_nonword_intro >> metis_tac[]) >>
  qexistsl_tac [`t`, `tv`] >> simp[extrequest_history_frame_refl] >>
  simp[gas_marked_exec_def] >> conj_tac
  >- metis_tac[read_result_gas_obs] >>
  simp[gas_marked_path_def] >> metis_tac[gas_path_rules]
QED

Resume extrequest_snapshot_read_endpoint[word]:
  `is_word_type (expr_type e)` by
    metis_tac[expr_body_pre_lowered_fits, arg_type_fits_word_type] >>
  `lowered_value_type ce e = expr_type e` by
    metis_tac[expr_body_pre_lowered_fits, abi_args_word_fits_eq] >>
  `ext_call_arg_value (lowered_value_type ce e) vv = vv` by
    (Cases_on `vv` >> gvs[ext_call_arg_value_def, vv_type_def]) >>
  `?op. unwrap_value ce vv sc = (op,sb) /\ sv = StackValue (expr_type e) op` by
    (fs[compile_snapshot_vv_def, comp_bind_def, comp_return_def] >>
     pairarg_tac >> gvs[] >> metis_tac[]) >>
  `?u. compile_snapshot_vv ce F (ext_call_arg_value (lowered_value_type ce e) vv) sc =
      (StackValue (lowered_value_type ce e) op,sb) /\
    gas_marked_exec F (ctx,func) (read_result cx r) (ee,t) [] (INL v) ee (OK u) /\
    expr_val_rel cx (expr_type e) v op u /\ safe_operand sb op /\
    stmt_state_rel ctx func ce cx ee u /\
    u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!aid p k. aid < sc.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (p,k) ==>
      mem_bytes_at p k u.vs_memory = mem_bytes_at p k t.vs_memory) /\
    extrequest_history_frame ce cx ee sc t ee sb u` by
    (irule extrequest_snapshot_word_endpoint >>
     qpat_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     simp[extrequest_history_frame_refl] >> metis_tac[]) >>
  `?tv. extrequest_tuple_cell ctx func ce cx ee sc t ee
      (e,r,vv,lowered_value_type ce e,tv,v)` by
    (irule extrequest_typed_cell >> metis_tac[]) >>
  `extrequest_snapshot_cell ctx func ce cx ee sb u
      (StackValue (lowered_value_type ce e) op,lowered_value_type ce e,tv,v)` by
    (irule extrequest_snapshot_cell_word_intro >>
     fs[exprExtRequestTupleFoldTheory.extrequest_tuple_cell_def] >> metis_tac[]) >>
  qexistsl_tac [`u`, `tv`] >> gvs[] >>
  fs[gas_marked_exec_def, gas_marked_path_def] >> metis_tac[gas_path_normal]
QED

Finalise extrequest_snapshot_read_endpoint

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
  exprExtRequestKwargSuffix exprExtRequestGasBind exprExtRequestUnreadCps
  exprExtRequestSourceFrame exprExtRequestOperandSafety exprExtRequestDefaultProbe
  exprOperandVar exprSimProps freshWrites exprSimAggregateSource
  gasOutcome gasSummaryCompose vyperCallOutcomeFrame fragExec
  vyperTypeArgFits vyperTypeExprSoundness vyperTypeInvariants

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


Theorem extrequest_snapshot_head_cps:
  expr_vv_case nocalls ctx func ce cx e /\
  expr_body_pre ce cx env e es /\ ~expr_has_effect e /\
  (nocalls ==> int_calls_expr e = []) /\
  compile_expr ce (expr_type e) e sa = (vv,sc) /\
  compile_snapshot_vv ce F (ext_call_arg_value (lowered_value_type ce e) vv) sc = (sv,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ stmt_state_rel ctx func ce cx es s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  gas_admissible (eval_expr cx e) expr_vv_res_ok es /\
  (!e ee sm sn t ef r vv u ty p w tv.
    vv_post ctx func ce cx e ee sm sn t ef r vv u /\
    ~expr_has_effect e /\ vv = LocatedValue ty p /\
    eval_operand p.ptr_operand u = SOME w /\
    evaluate_type (get_tenv cx) ty = SOME tv ==>
    (p.ptr_location = LocStorage ==>
      storage_read_live cx F (get_storage cx ef F) w tv) /\
    (p.ptr_location = LocTransient ==>
      storage_read_live cx T (get_storage cx ef T) w tv)) /\
  (!e ee sm sn t ef r vv u.
    vv_post ctx func ce cx e ee sm sn t ef r vv u /\
    ~expr_has_effect e ==>
    (!n b sz. local_region ce ee.scopes t n b sz ==>
      mem_bytes_at b sz u.vs_memory = mem_bytes_at b sz t.vs_memory) /\
    (!off len.
      (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
        sm.cs_next_id <= inst.inst_id /\
        FLOOKUP u.vs_allocas inst.inst_id = SOME (b,sz) ==>
        loweringStateRelDefs$regions_disjoint off len b sz) ==>
      mem_bytes_at off len u.vs_memory = mem_bytes_at off len t.vs_memory)) /\
  (!v ee u tv.
    extrequest_snapshot_cell ctx func ce cx ee sb u (sv,lowered_value_type ce e,tv,v) /\
    stmt_state_rel ctx func ce cx ee u /\ ~u.vs_halted /\
    u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    local_ptrs_reserved ce sb /\ ee.gas_obs = [] /\
    wb_frame ce es ee sa s0 u /\
    extrequest_history_frame ce cx (es with gas_obs := []) sa s0 ee sb u /\
    (?used. !tail. bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := used ++ tail) = (INL v,ee with gas_obs := tail)) ==>
    gas_outcome F (cx_tops cx) (ctx,func)
      ((kont : value -> evaluation_state -> eval_result evaluation_result) v) (ee,u) Q
      (\res ef result. expr_exit res result)) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (bind (bind (eval_expr cx e) (read_result cx)) kont) (es,s0) Q
    (\res ef result. expr_exit res result)
Proof
  strip_tac >>
  `post_value_type ce e = expr_type e` by
    (irule post_value_type_not_int_call >> metis_tac[expr_has_effect_thm]) >>
  `ci_mono sa sc` by
    (mp_tac (Q.SPECL [`ce`, `expr_type e`, `e`, `sa`]
      (cj 1 compile_expr_ci_mono)) >> simp[]) >>
  `ci_mono sc sb` by metis_tac[ci_mono_compile_snapshot_vv, pairTheory.SND] >>
  `fn_has_code sa sc func /\ fn_has_code sc sb func` by
    (irule fn_has_code_split >> gvs[ci_mono_def]) >>
  `local_ptrs_reserved ce sc /\ local_ptrs_reserved ce sb` by
    metis_tac[compiler_ci_mono_reserved] >>
  `expr_vv_sim ctx func ce cx (expr_type e) e es` by
    (gvs[expr_vv_case_def] >> first_x_assum irule >> qexists `env` >> simp[]) >>
  `gas_outcome F (cx_tops cx) (ctx,func) (eval_expr cx e) (es,s0)
    (\res ee t. ?r. res = INL r /\
      vv_post ctx func ce cx e es sa sc s0 ee r vv t /\
      t.vs_current_bb = sc.cs_current_bb /\
      t.vs_inst_idx = LENGTH sc.cs_current_insts)
    (\res ee r. expr_exit res r)` by
    (gvs[expr_vv_sim_def] >> first_x_assum irule >> simp[]) >>
  rewrite_tac[bind_assoc] >>
  drule (INST_TYPE [alpha |-> ``:eval_result``] extrequest_outcome_bind_result) >>
  disch_then irule >> reverse conj_tac
  >- (rpt gen_tac >> Cases_on `rr` >> simp[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  `!tail. eval_expr cx e
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
     (INL r, mid with gas_obs := tail)` by gvs[gas_marked_exec_def] >>
  `!l. vv_operand vv <> Label l` by
    (irule (cj 1 extrequest_compiler_nonlabel) >>
     goal_assum (drule_at Any) >> qexists `env` >>
     qpat_assum `expr_body_pre _ _ _ e es` mp_tac >>
     simp[NoAsms, expr_body_pre_def, expr_sim_inv_def] >> metis_tac[]) >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sc x` by
    metis_tac[CONJUNCT1 compiler_compile_var] >>
  `safe_operand sc (vv_operand vv)` by simp[safe_operand_def] >>
  `(case vv of StackValue ty op => safe_operand sc op
    | LocatedValue ty p => safe_operand sc p.ptr_operand)` by
    (Cases_on `vv` >> gvs[vv_operand_def]) >>
  `~t.vs_halted` by
    (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[NoAsms, gas_marked_exec_def, gas_marked_path_def] >> metis_tac[gas_path_normal]) >>
  `stmt_state_rel ctx func ce cx (mid with gas_obs := []) t` by
    (qpat_assum `vv_post _ _ _ _ e _ _ _ _ _ _ _ _` mp_tac >>
     simp[NoAsms, vv_post_def] >> metis_tac[]) >>
  `extrequest_read_frame cx (es with gas_obs := []) (mid with gas_obs := [])` by
    (drule extrequest_pure_expr_read_frame >> rewrite_tac[state_rel_frame_result] >>
     disch_then (qspecl_then [`cx`,
       `es with gas_obs := gas_explicit marks s0.vs_gas_readings`,
       `INL r`, `mid with gas_obs := []`] mp_tac) >>
     qpat_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` assume_tac) >>
     fs[extrequest_read_frame_def]) >>
  suspend "capture"
QED

Resume extrequest_snapshot_head_cps[capture]:
  `vv_post ctx func ce cx e (es with gas_obs := []) sa sc s0
    (mid with gas_obs := []) r vv t` by simp[vv_post_initial_gas] >>
  `extrequest_history_frame ce cx (es with gas_obs := []) sa s0
    (mid with gas_obs := []) sc t` by
    (irule extrequest_history_frame_extend >>
     qpat_assum `vv_post _ _ _ _ e (es with gas_obs := []) _ _ _ _ _ _ _` (irule_at Any) >>
     simp[extrequest_history_frame_refl] >>
     qpat_assum `!e ee sm sn t ef r vv u. _` (drule_all_then mp_tac) >> fs[ci_mono_def]) >>
  `extrequest_strong_capture ctx func ce cx e r vv (mid with gas_obs := []) sc t` by
    (irule extrequest_strong_capture_intro >>
     qpat_assum `vv_post _ _ _ _ e es _ _ _ _ _ _ _` (irule_at Any) >>
     simp[] >> fs[ci_mono_def] >> metis_tac[]) >>
  `?v. read_result cx r (mid with gas_obs := []) = (INL v,mid with gas_obs := [])` by
    metis_tac[vv_post_materialises] >>
  `bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
    (INL v,mid with gas_obs := [])` by
    (qpat_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` assume_tac) >>
     fs[bind_def]) >>
  `value_runtime_typed env (expr_type e) v /\
   value_runtime_typed env (lowered_value_type ce e) v` by
    (`expr_body_pre ce cx env e
       (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
     `type_widens_to env.type_defs (expr_type e) (expr_type e)` by simp[] >>
     qpat_x_assum `expr_body_pre _ _ _ _ es` kall_tac >>
     drule extrequest_default_runtime_types >>
     disch_then (qspecl_then [`expr_type e`, `mid with gas_obs := []`, `v`] mp_tac) >>
     simp[] >> strip_tac >>
     `env.type_defs = get_tenv cx` by
       fs[expr_body_pre_def, expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
     simp[value_runtime_typed_def] >> metis_tac[]) >>
  `!ty p tr w tv. vv = LocatedValue ty p /\ p.ptr_location = slot_loc tr /\
    eval_operand p.ptr_operand t = SOME w /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
    storage_read_live cx tr (get_storage cx (mid with gas_obs := []) tr) w tv` by
    (rpt strip_tac >>
     `vv_type (LocatedValue ty p) = expr_type e` by
       (drule intcall_compile_expr_tag >>
        disch_then (qspecl_then [`expr_type e`, `sa`, `ce`] mp_tac) >> simp[]) >>
     `ty = expr_type e` by fs[vv_type_def] >>
     Cases_on `tr` >> gvs[slot_loc_def] >> metis_tac[]) >>
  suspend "snapshot_suffix"
QED

Resume extrequest_snapshot_head_cps[snapshot_suffix]:
  `?u tv. gas_marked_exec F (ctx,func) (read_result cx r)
      (mid with gas_obs := [],t) [] (INL v) (mid with gas_obs := []) (OK u) /\
    extrequest_snapshot_cell ctx func ce cx (mid with gas_obs := []) sb u
      (sv,lowered_value_type ce e,tv,v) /\
    stmt_state_rel ctx func ce cx (mid with gas_obs := []) u /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    extrequest_history_frame ce cx (mid with gas_obs := []) sc t
      (mid with gas_obs := []) sb u` by
    (irule extrequest_snapshot_read_endpoint >>
     qpat_assum `vv_post _ _ _ _ e es _ _ _ _ _ _ _` (irule_at Any) >>
     simp[] >> fs[ci_mono_def] >> metis_tac[]) >>
  `extrequest_history_frame ce cx (es with gas_obs := []) sa s0
    (mid with gas_obs := []) sb u` by
    (irule extrequest_history_frame_trans >>
     qpat_assum `extrequest_history_frame _ _ _ sa s0 _ sc t` (irule_at Any) >>
     simp[] >> metis_tac[exprSimWordArgsTheory.stmt_state_rel_gas_obs]) >>
  `wb_frame ce es (mid with gas_obs := []) sa s0 u` by
    (irule extrequest_kwarg_history_writeback >>
     qpat_assum `vv_post _ _ _ _ e es _ _ _ _ _ _ _` (irule_at Any) >>
     fs[extrequest_read_frame_def] >> metis_tac[]) >>
  `!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
    (INL v,mid with gas_obs := tail)` by
    (drule_all extrequest_kwarg_counted_read >> simp[]) >>
  irule extrequest_kwarg_suffix_cps >>
  qpat_assum `gas_marked_exec _ _ (read_result _ _) _ _ _ _ _` (irule_at Any) >>
  simp[] >> first_x_assum irule >> simp[] >>
  conj_tac >- (qexists `gas_explicit marks s0.vs_gas_readings` >>
    simp[evaluation_state_component_equality]) >> metis_tac[]

QED

Finalise extrequest_snapshot_head_cps

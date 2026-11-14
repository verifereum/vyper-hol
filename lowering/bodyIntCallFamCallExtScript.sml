(* Seam 2 joint induction, a family leaf of the call step: every other call target (external calls and send; the rest are not supported_expr). *)
Theory bodyIntCallFamCallExt
Ancestors
  bodyIntCallJointContract bodyIntCallJointCallCore bodyIntCallJointPurePath
  bodyIntCallJointCallSource
  exprExtRequestHistory extcallProtFramePath exprSimSliceCompose
  exprExtRequestSnapshotHeadCps extcallProtFrameUnread
  exprLoweringProps fragExec exprSimMemorySource vyperInterpreter exprExtRequestGasBind
  exprLowering compileEnv exprExtRequestSnapshotPositionalCps vyperState stmtSimDeclGas

Theorem intcall_ext_history_cont[local]:
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s /\
  extrequest_history_frame ce fp.jc_cx es sa s ee sb u /\
  stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx ee u /\
  expr_sim_inv ce fp.jc_cx env ee /\ ee.immutables = es.immutables /\
  gas_marked_path F fp.jc_ctx fp.jc_func s n (OK u) /\
  ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
  u.vs_inst_idx = LENGTH sb.cs_current_insts /\
  (!a k. fp.jc_prot a k ==>
    mem_bytes_at a k u.vs_memory = mem_bytes_at a k s.vs_memory) ==>
  intcall_expr_cont fp ce env es sa s ee sb u
Proof
  strip_tac >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s /\
   allocas_above fp.jc_lo s` by fs[intcall_expr_res_def] >>
  `s.vs_alloca_next <= u.vs_alloca_next` by
    metis_tac[gas_marked_path_alloca_next_mono] >>
  `allocas_above fp.jc_lo u` by
    metis_tac[gas_marked_path_allocas_above] >>
  `!n b k. local_region ce es.scopes s n b k <=>
            local_region ce ee.scopes u n b k` by
    metis_tac[extrequest_history_local_regions] >>
  `!op. fp.jc_reserved op ==> eval_operand op u = eval_operand op s` by
    (rpt strip_tac >>
     `?x w. op = Var x /\ lookup_var x fp.jc_oorig = SOME w` by
       metis_tac[intcall_frame_ok_def] >>
     `not_fresh_at sa x /\ eval_operand op s = SOME w` by
       (fs[intcall_expr_res_def, venomStateTheory.eval_operand_def] >> metis_tac[]) >>
     gvs[venomStateTheory.eval_operand_def] >>
     metis_tac[extrequest_history_frame_def]) >>
  `intcall_expr_res fp ce env ee sb u` by
    (irule intcall_joint_res_frame >>
     simp[] >> qexistsl [`es`, `s`, `sa`] >>
     fs[extrequest_history_frame_def] >> metis_tac[]) >>
  `locals_kept ce es ee s u` by
    (`ee.scopes = es.scopes` by
       fs[extrequest_history_frame_def, exprExtRequestReadProbeTheory.extrequest_read_frame_def] >>
     `locals_kept ce es es s u` by
       (irule exprSimPropsTheory.locals_kept_regions >>
        fs[extrequest_history_frame_def] >> metis_tac[]) >>
     fs[loweringPostsTheory.locals_kept_def, loweringPostsTheory.popped_kept_def] >>
     metis_tac[]) >>
  fs[intcall_expr_cont_def, extrequest_history_frame_def,
     loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[]
QED

Theorem intcall_ext_target_cps[local]:
  intcall_forced_producer fp e /\ intcall_frame_ok fp /\
  body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  expr_body_pre ce fp.jc_cx env e es /\ expr_type e = BaseT AddressT /\
  supported_expr fp.jc_tops e /\
  calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr e) /\
  lower_value compile_expr ce (BaseT AddressT) e sa = (op,sb) /\
  fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  gas_admissible (bind (bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx)) kont)
    expr_vv_res_ok es /\
  intcall_expr_res fp ce env es sa s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!v ee u.
    expr_post fp.jc_ctx fp.jc_func ce fp.jc_cx e es sa sb s ee v op u /\
    intcall_expr_cont fp ce env es sa s ee sb u /\ ee.gas_obs = [] /\
    (?used. !tail. bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx)
      (es with gas_obs := used ++ tail) = (INL v,ee with gas_obs := tail)) ==>
    gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
      (kont v) (ee,u) Q (\r ee z. expr_exit r z)) ==>
  gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (bind (bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx)) kont)
    (es,s) Q (\r ee z. expr_exit r z)
Proof
  strip_tac >>
  `gas_admissible (bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx))
     expr_res_ok es` by metis_tac[slice_gas_admissible_expr_head] >>
  `gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx)) (es,s)
    (\res ee u. ?v. res = INL v /\
      expr_post fp.jc_ctx fp.jc_func ce fp.jc_cx e es sa sb s ee v op u /\
      intcall_expr_cont fp ce env es sa s ee sb u)
    (\res ee r. ?ex. res = INR ex /\ expr_exit (INR ex) r)` by
    (fs[intcall_forced_producer_def] >>
     first_x_assum (drule_all_then mp_tac) >>
     strip_tac >> irule slice_gas_outcome_conseq >>
     goal_assum (drule_at Any) >>
     qpat_x_assum `gas_outcome _ _ _ _ _ _ _` kall_tac >>
     qpat_x_assum `!v ee u. _` kall_tac >>
     rpt conj_tac >> rpt gen_tac >> Cases_on `res` >>
     simp[exprSimDefsTheory.expr_exit_def] >> strip_tac >>
     gvs[loweringPostsTheory.expr_post_def, intcall_expr_cont_def,
         intcall_expr_res_def] >>
     metis_tac[stmtSimPropsTheory.expr_exit_INR_type]) >>
  irule slice_gas_outcome_bind_value >>
  qexists `\v ee u. expr_post fp.jc_ctx fp.jc_func ce fp.jc_cx e es sa sb s ee v op u /\
    intcall_expr_cont fp ce env es sa s ee sb u` >>
  reverse conj_tac
  >- (BETA_TAC >> irule slice_gas_outcome_conseq >>
      goal_assum (drule_at Any) >> simp[] >>
      metis_tac[stmtSimPropsTheory.expr_exit_INR_type]) >>
  rpt gen_tac >> strip_tac >>
  first_x_assum irule >> fs[] >>
  qexists `gas_explicit marks s.vs_gas_readings` >>
  gvs[gasSummaryTheory.gas_marked_exec_def]
QED

Theorem intcall_ext_snapshot_head_cps[local]:
  intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  intcall_expr_producer fp e /\ supported_expr fp.jc_tops e /\
  calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr e) /\
  expr_body_pre ce fp.jc_cx env e es /\ ~expr_has_effect e /\
  compile_expr ce (expr_type e) e sa = (vv,sc) /\
  compile_snapshot_vv ce F (ext_call_arg_value (lowered_value_type ce e) vv) sc = (sv,sb) /\
  fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  intcall_expr_res fp ce env es sa s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  gas_admissible (bind (bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx)) kont)
    expr_vv_res_ok es /\
  (!v ee u tv.
    extrequest_snapshot_cell_protected fp.jc_prot fp.jc_morig.vs_memory
      fp.jc_ctx fp.jc_func ce fp.jc_cx ee sb u (sv,lowered_value_type ce e,tv,v) /\
    intcall_expr_cont fp ce env es sa s ee sb u /\
    extrequest_history_frame ce fp.jc_cx (es with gas_obs := []) sa s ee sb u /\
    ee.gas_obs = [] /\
    (?used. !tail. bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx)
      (es with gas_obs := used ++ tail) = (INL v,ee with gas_obs := tail)) ==>
    gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
      (kont v) (ee,u) Q (\r ef z. expr_exit r z)) ==>
  gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (bind (bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx)) kont)
    (es,s) Q (\r ef z. expr_exit r z)
Proof
  strip_tac >>
  `ci_mono sa sc` by
    (mp_tac (Q.SPECL [`ce`, `expr_type e`, `e`, `sa`]
      (cj 1 compile_expr_ci_mono)) >> simp[]) >>
  `ci_mono sc sb` by metis_tac[ci_mono_compile_snapshot_vv, pairTheory.SND] >>
  `fn_has_code sa sc fp.jc_func /\ fn_has_code sc sb fp.jc_func` by
    (irule fn_has_code_split >> gvs[ci_mono_def]) >>
  `gas_admissible (eval_expr fp.jc_cx e) expr_vv_res_ok es` by
    metis_tac[slice_gas_admissible_expr_head, forced_expr_admissible_raw] >>
  `gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (eval_expr fp.jc_cx e) (es,s)
    (\res ee t. ?r. res = INL r /\
      vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx e es sa sc s ee r vv t /\
      vv_storage_live fp.jc_cx vv ee t /\ pure_frame ce fp.jc_func es sa s t /\
      intcall_expr_cont fp ce env es sa s ee sc t)
    (\res ee z. expr_exit res z)` by
    (fs[intcall_expr_producer_def] >>
     first_x_assum (drule_all_then mp_tac) >> strip_tac >>
     irule slice_gas_outcome_conseq >> goal_assum (drule_at Any) >>
     qpat_x_assum `gas_outcome _ _ _ _ _ _ _` kall_tac >>
     qpat_x_assum `!v ee u tv. _` kall_tac >>
     simp[] >> rpt gen_tac >> strip_tac >> gvs[] >>
     metis_tac[intcall_vv_post_intro]) >>
  rewrite_tac[vyperStateTheory.bind_assoc] >>
  drule (INST_TYPE [alpha |-> ``:eval_result``] extrequest_outcome_bind_result) >>
  disch_then irule >> reverse conj_tac
  >- (rpt gen_tac >> Cases_on `rr` >> simp[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  suspend "capture"
QED

Resume intcall_ext_snapshot_head_cps[capture]:
  `!tail. eval_expr fp.jc_cx e
    (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
    (INL r,mid with gas_obs := tail)` by
      gvs[gasSummaryTheory.gas_marked_exec_def] >>
  `local_ptrs_reserved ce sa /\ stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s` by
    fs[intcall_expr_res_def] >>
  `local_ptrs_reserved ce sc` by metis_tac[exprOperandVarTheory.compiler_ci_mono_reserved] >>
  `!l. vv_operand vv <> Label l` by
    (irule (cj 1 exprExtRequestOperandSafetyTheory.extrequest_compiler_nonlabel) >>
     goal_assum (drule_at Any) >> qexists `env` >>
     qpat_assum `expr_body_pre _ _ _ _ _` mp_tac >>
     simp[NoAsms, exprSimHypsDefsTheory.expr_body_pre_def,
       exprSimHypsDefsTheory.expr_sim_inv_def] >> metis_tac[]) >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sc x` by
    metis_tac[CONJUNCT1 exprOperandVarTheory.compiler_compile_var] >>
  `safe_operand sc (vv_operand vv)` by
    simp[exprSafeOperandTheory.safe_operand_def] >>
  `extrequest_strong_capture fp.jc_ctx fp.jc_func ce fp.jc_cx e r vv
    (mid with gas_obs := []) sc t` by
    (irule exprExtRequestStrongCaptureTheory.extrequest_strong_capture_intro >>
     qpat_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     simp[] >> fs[ci_mono_def] >>
     conj_tac
     >- (rpt strip_tac >> gvs[loweringPostsTheory.vv_storage_live_def,
           vyperStorageBackendTheory.get_storage_def] >>
         metis_tac[]) >>
     conj_tac
     >- (irule loweringPostsTheory.post_value_type_not_int_call >>
         metis_tac[loweringPostsTheory.expr_has_effect_thm]) >>
     Cases_on `vv` >> gvs[contextTheory.vv_operand_def]) >>
  `?v. read_result fp.jc_cx r (mid with gas_obs := []) =
    (INL v,mid with gas_obs := [])` by
    metis_tac[exprSimAggregateSourceTheory.vv_post_materialises] >>
  `extrequest_read_frame fp.jc_cx (es with gas_obs := []) (mid with gas_obs := [])` by
    (drule exprExtRequestSourceFrameTheory.extrequest_pure_expr_read_frame >>
     rewrite_tac[vyperCallOutcomeFrameTheory.state_rel_frame_result] >>
     disch_then (qspecl_then [`fp.jc_cx`,
       `es with gas_obs := gas_explicit marks s.vs_gas_readings`,
       `INL r`, `mid with gas_obs := []`] mp_tac) >>
     qpat_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` assume_tac) >>
     fs[exprExtRequestReadProbeTheory.extrequest_read_frame_def]) >>
  `vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx e (es with gas_obs := []) sa sc s
     (mid with gas_obs := []) r vv t` by
    simp[exprSimPropsTheory.vv_post_initial_gas] >>
  `extrequest_history_frame ce fp.jc_cx (es with gas_obs := []) sa s
    (mid with gas_obs := []) sc t` by
    (irule exprExtRequestHistoryTheory.extrequest_history_frame_extend >>
     qpat_assum `vv_post _ _ _ _ _ (es with gas_obs := []) _ _ _ _ _ _ _`
       (irule_at Any) >>
     simp[exprExtRequestHistoryTheory.extrequest_history_frame_refl,
       exprSimWordArgsTheory.stmt_state_rel_gas_obs] >>
     fs[ci_mono_def, loweringPostsTheory.pure_frame_def] >>
     metis_tac[]) >>
  `bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx)
    (es with gas_obs := gas_explicit marks s.vs_gas_readings) =
    (INL v,mid with gas_obs := [])` by
    (qpat_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` assume_tac) >>
     fs[vyperStateTheory.bind_def]) >>
  `value_runtime_typed env (expr_type e) v /\
   value_runtime_typed env (lowered_value_type ce e) v` by
    (`expr_body_pre ce fp.jc_cx env e
       (es with gas_obs := gas_explicit marks s.vs_gas_readings)` by simp[] >>
     `type_widens_to env.type_defs (expr_type e) (expr_type e)` by simp[] >>
     qpat_x_assum `expr_body_pre _ _ _ _ es` kall_tac >>
     drule exprExtRequestDefaultProbeTheory.extrequest_default_runtime_types >>
     disch_then (qspecl_then [`expr_type e`, `mid with gas_obs := []`, `v`] mp_tac) >>
     simp[] >> strip_tac >>
     `env.type_defs = get_tenv fp.jc_cx` by
       fs[exprSimHypsDefsTheory.expr_body_pre_def,
          exprSimHypsDefsTheory.expr_sim_inv_def,
          vyperTypeInvariantsTheory.env_consistent_def,
          vyperTypeInvariantsTheory.env_context_consistent_def] >>
     fs[vyperStateTheory.bind_def,
        vyperTypeExprSoundnessTheory.value_runtime_typed_def] >> metis_tac[]) >>
  `(!a k. fp.jc_prot a k ==> a + k <= t.vs_alloca_next /\
    mem_bytes_at a k t.vs_memory = mem_bytes_at a k fp.jc_morig.vs_memory /\
    !i b n. FLOOKUP t.vs_allocas i = SOME (b,n) ==>
      loweringStateRelDefs$regions_disjoint a k b n)` by
    (qpat_x_assum `gas_outcome _ _ _ _ _ _ _` kall_tac >>
     qpat_x_assum `!v ee u tv. _` kall_tac >>
     fs[intcall_expr_cont_def, intcall_expr_res_def, intcall_frame_ok_def,
        intCallFrameTheory.allocas_above_def,
        loweringStateRelDefsTheory.regions_disjoint_def] >>
     rpt gen_tac >> strip_tac >>
     `a + k <= fp.jc_lo` by metis_tac[] >>
     conj_tac >- decide_tac >> rpt strip_tac >>
     `fp.jc_lo <= b` by metis_tac[] >> decide_tac) >>
  suspend "snapshot_suffix"
QED

Resume intcall_ext_snapshot_head_cps[snapshot_suffix]:
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx (mid with gas_obs := []) t /\
   ~t.vs_halted /\ t.vs_current_bb = sc.cs_current_bb /\
   t.vs_inst_idx = LENGTH sc.cs_current_insts` by
    fs[intcall_expr_cont_def, intcall_expr_res_def,
       exprSimWordArgsTheory.stmt_state_rel_gas_obs] >>
  `vv_type vv = expr_type e` by
    (drule bodyIntCallCompilerTagsTheory.intcall_compile_expr_tag >>
     disch_then (qspecl_then [`expr_type e`, `sa`, `ce`] mp_tac) >> simp[]) >>
  `(case vv of StackValue ty a => safe_operand sc a
    | LocatedValue ty p => safe_operand sc p.ptr_operand)` by
    (Cases_on `vv` >> gvs[contextTheory.vv_operand_def]) >>
  `!ty p tr w tv. vv = LocatedValue ty p /\ p.ptr_location = slot_loc tr /\
    eval_operand p.ptr_operand t = SOME w /\
    evaluate_type (get_tenv fp.jc_cx) (expr_type e) = SOME tv ==>
    storage_read_live fp.jc_cx tr (get_storage fp.jc_cx (mid with gas_obs := []) tr) w tv` by
    (rpt strip_tac >> gvs[contextTheory.vv_type_def,
      loweringPostsTheory.vv_storage_live_def,
      vyperStorageBackendTheory.get_storage_def] >>
     Cases_on `tr` >> gvs[loweringPostsTheory.slot_loc_def,
       vyperStorageBackendTheory.get_storage_def]) >>
  `?u tv. gas_marked_exec F (fp.jc_ctx,fp.jc_func) (read_result fp.jc_cx r)
      (mid with gas_obs := [],t) [] (INL v) (mid with gas_obs := []) (OK u) /\
    extrequest_snapshot_cell_protected fp.jc_prot fp.jc_morig.vs_memory
      fp.jc_ctx fp.jc_func ce fp.jc_cx (mid with gas_obs := []) sb u
      (sv,lowered_value_type ce e,tv,v) /\
    stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx (mid with gas_obs := []) u /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    extrequest_history_frame ce fp.jc_cx (mid with gas_obs := []) sc t
      (mid with gas_obs := []) sb u /\
    (!a k. fp.jc_prot a k ==> a + k <= u.vs_alloca_next /\
      mem_bytes_at a k u.vs_memory = mem_bytes_at a k fp.jc_morig.vs_memory /\
      !i b n. FLOOKUP u.vs_allocas i = SOME (b,n) ==>
        loweringStateRelDefs$regions_disjoint a k b n)` by
    (Cases_on `is_word_type (lowered_value_type ce e)`
     >- suspend "word_suffix" >>
     suspend "nonword_suffix") >>
  suspend "suffix_join"
QED

Resume intcall_ext_snapshot_head_cps[word_suffix]:
  `is_word_type (expr_type e)` by
    metis_tac[exprSimHypsTheory.expr_body_pre_lowered_fits,
      aggregateEvaluatedLayoutTheory.arg_type_fits_word_type] >>
  `lowered_value_type ce e = expr_type e` by
    metis_tac[exprSimHypsTheory.expr_body_pre_lowered_fits,
      abiEncodeArgsSimTheory.abi_args_word_fits_eq] >>
  `ext_call_arg_value (lowered_value_type ce e) vv = vv` by
    (Cases_on `vv` >> gvs[exprLoweringTheory.ext_call_arg_value_def,
       contextTheory.vv_type_def]) >>
  `?op. unwrap_value ce vv sc = (op,sb) /\ sv = StackValue (expr_type e) op` by
    (fs[exprLoweringTheory.compile_snapshot_vv_def,
        compileEnvTheory.comp_bind_def, compileEnvTheory.comp_return_def] >>
     pairarg_tac >> gvs[] >> metis_tac[]) >>
  `?u. compile_snapshot_vv ce F (ext_call_arg_value (lowered_value_type ce e) vv) sc =
      (StackValue (lowered_value_type ce e) op,sb) /\
    gas_marked_exec F (fp.jc_ctx,fp.jc_func) (read_result fp.jc_cx r)
      (mid with gas_obs := [],t) [] (INL v) (mid with gas_obs := []) (OK u) /\
    expr_val_rel fp.jc_cx (expr_type e) v op u /\ safe_operand sb op /\
    stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx (mid with gas_obs := []) u /\
    u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!aid p k. aid < sc.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (p,k) ==>
      mem_bytes_at p k u.vs_memory = mem_bytes_at p k t.vs_memory) /\
    extrequest_history_frame ce fp.jc_cx (mid with gas_obs := []) sc t
      (mid with gas_obs := []) sb u /\
    (!a k. fp.jc_prot a k ==> a + k <= u.vs_alloca_next /\
      mem_bytes_at a k u.vs_memory = mem_bytes_at a k fp.jc_morig.vs_memory /\
      !i b n. FLOOKUP u.vs_allocas i = SOME (b,n) ==>
        loweringStateRelDefs$regions_disjoint a k b n)` by
    (irule exprExtRequestSnapshotWordTheory.extrequest_snapshot_word_endpoint_protected >>
     qpat_assum `vv_post _ _ _ _ _ es _ _ _ _ _ _ _` (irule_at Any) >>
     simp[exprExtRequestHistoryTheory.extrequest_history_frame_refl] >>
     fs[ci_mono_def] >> metis_tac[]) >>
  `?tv. extrequest_tuple_cell fp.jc_ctx fp.jc_func ce fp.jc_cx
    (mid with gas_obs := []) sc t (mid with gas_obs := [])
    (e,r,vv,lowered_value_type ce e,tv,v)` by
    (irule exprExtRequestTypedCellsTheory.extrequest_typed_cell >> metis_tac[]) >>
  `extrequest_snapshot_cell_protected fp.jc_prot fp.jc_morig.vs_memory
    fp.jc_ctx fp.jc_func ce fp.jc_cx (mid with gas_obs := []) sb u
    (StackValue (lowered_value_type ce e) op,lowered_value_type ce e,tv,v)` by
    (irule exprExtRequestSnapshotCellIntroTheory.extrequest_snapshot_cell_word_intro_protected >>
     fs[exprExtRequestTupleFoldTheory.extrequest_tuple_cell_def] >> metis_tac[]) >>
  qexistsl [`u`, `tv`] >> gvs[] >>
  fs[gasSummaryTheory.gas_marked_exec_def, fragGasModeTheory.gas_marked_path_def] >>
  metis_tac[fragGasPathTheory.gas_path_normal]
QED

Resume intcall_ext_snapshot_head_cps[nonword_suffix]:
  `~is_word_type (vv_type (ext_call_arg_value (lowered_value_type ce e) vv))` by
    (Cases_on `vv` >> gvs[contextTheory.vv_type_def, exprLoweringTheory.ext_call_arg_value_def] >>
     metis_tac[exprSimHypsTheory.expr_body_pre_lowered_fits,
       aggregateEvaluatedLayoutTheory.arg_type_fits_word_type]) >>
  `sv = ext_call_arg_value (lowered_value_type ce e) vv /\ sb = sc` by
    metis_tac[exprExtRequestSnapshotProbeTheory.extrequest_snapshot_nonword_no_copy,
      pairTheory.PAIR_EQ] >> gvs[] >>
  rename1 `compile_expr ce (expr_type e) e sa = (vv,sc)` >>
  `?tv. extrequest_snapshot_cell_protected fp.jc_prot fp.jc_morig.vs_memory
    fp.jc_ctx fp.jc_func ce fp.jc_cx (mid with gas_obs := []) sc t
    (ext_call_arg_value (lowered_value_type ce e) vv,lowered_value_type ce e,tv,v)` by
    (irule exprExtRequestSnapshotCellIntroTheory.extrequest_snapshot_cell_nonword_intro_protected >>
     simp[exprSimWordArgsTheory.stmt_state_rel_gas_obs] >> metis_tac[]) >>
  `!tail. read_result fp.jc_cx r ((mid with gas_obs := []) with gas_obs := tail) =
    (INL v,(mid with gas_obs := []) with gas_obs := tail)` by
    (irule exprSimMemorySourceTheory.read_result_gas_obs >> simp[]) >>
  `gas_path fp.jc_ctx fp.jc_func t 0 (OK t)` by
    (irule (cj 1 fragGasPathTheory.gas_path_rules) >> simp[]) >>
  qexistsl [`t`, `tv`] >>
  simp[exprExtRequestHistoryTheory.extrequest_history_frame_refl,
    gasSummaryTheory.gas_marked_exec_def, fragGasModeTheory.gas_marked_path_def] >>
  rpt strip_tac >> metis_tac[]
QED

Resume intcall_ext_snapshot_head_cps[suffix_join]:
  `extrequest_history_frame ce fp.jc_cx (es with gas_obs := []) sa s
    (mid with gas_obs := []) sb u` by
    (irule exprExtRequestHistoryComposeTheory.extrequest_history_frame_trans >>
     qpat_assum `extrequest_history_frame _ _ _ sa s _ sc t` (irule_at Any) >>
     simp[] >> metis_tac[exprSimWordArgsTheory.stmt_state_rel_gas_obs]) >>
  `extrequest_history_frame ce fp.jc_cx es sa s (mid with gas_obs := []) sb u` by
    (qpat_assum `extrequest_history_frame _ _ (es with gas_obs := []) sa s _ sb u` mp_tac >>
     simp[NoAsms, exprExtRequestHistoryTheory.extrequest_history_frame_def,
       exprExtRequestReadProbeTheory.extrequest_read_frame_def] >>
     strip_tac >> gvs[] >> metis_tac[]) >>
  `?n. gas_marked_path F fp.jc_ctx fp.jc_func s n (OK u)` by
    (qpat_assum `gas_marked_exec _ _ (eval_expr _ _) _ _ _ _ _` mp_tac >>
     qpat_assum `gas_marked_exec _ _ (read_result _ _) _ _ _ _ _` mp_tac >>
     simp[NoAsms, gasSummaryTheory.gas_marked_exec_def] >>
     metis_tac[fragGasModeTheory.gas_marked_path_then]) >>
  `expr_sim_inv ce fp.jc_cx env (mid with gas_obs := [])` by
    fs[intcall_expr_cont_def, intcall_expr_res_def] >>
  `(mid with gas_obs := []).immutables = es.immutables` by
    (`supported_pure_expr fp.jc_tops e` by
       metis_tac[supportedExprsTheory.supported_expr_def,
         supportedExprTraverseTheory.supported_effects_have_effect] >>
     qpat_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` mp_tac) >>
     strip_tac >> drule_all bodyIntCallJointCallSourceTheory.intcall_pure_expr_immutables >>
     simp[]) >>
  `intcall_expr_cont fp ce env es sa s (mid with gas_obs := []) sb u` by
    (irule intcall_ext_history_cont >> simp[] >>
     fs[intcall_expr_res_def] >> metis_tac[]) >>
  `!tail. bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx)
    (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
    (INL v,mid with gas_obs := tail)` by
    (drule_all exprExtRequestKwargSuffixTheory.extrequest_kwarg_counted_read >> simp[]) >>
  irule exprExtRequestKwargSuffixTheory.extrequest_kwarg_suffix_cps >>
  qpat_assum `gas_marked_exec _ _ (read_result _ _) _ _ _ _ _` (irule_at Any) >>
  simp[] >> first_x_assum irule >> simp[] >>
  rpt strip_tac >> metis_tac[vyperStateTheory.evaluation_state_component_equality]
QED

Finalise intcall_ext_snapshot_head_cps

Theorem intcall_ext_positional_from_head[local]:
  (!e es sa sc vv sv sb s kont Q.
    intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
    intcall_expr_producer fp e /\ supported_expr fp.jc_tops e /\
    calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr e) /\
    expr_body_pre ce fp.jc_cx env e es /\ ~expr_has_effect e /\
    compile_expr ce (expr_type e) e sa = (vv,sc) /\
    compile_snapshot_vv ce F (ext_call_arg_value (lowered_value_type ce e) vv) sc = (sv,sb) /\
    fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
    intcall_expr_res fp ce env es sa s /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    gas_admissible (bind (bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx)) kont)
      expr_vv_res_ok es /\
    (!v ee u tv.
      extrequest_snapshot_cell_protected fp.jc_prot fp.jc_morig.vs_memory
        fp.jc_ctx fp.jc_func ce fp.jc_cx ee sb u (sv,lowered_value_type ce e,tv,v) /\
      intcall_expr_cont fp ce env es sa s ee sb u /\
      extrequest_history_frame ce fp.jc_cx (es with gas_obs := []) sa s ee sb u /\
      ee.gas_obs = [] /\
      (?used. !tail. bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx)
        (es with gas_obs := used ++ tail) = (INL v,ee with gas_obs := tail)) ==>
      gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
        (kont v) (ee,u) Q (\r ef z. expr_exit r z)) ==>
    gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
      (bind (bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx)) kont)
      (es,s) Q (\r ef z. expr_exit r z)) ==>
  !xs es sa sb vvs s k old_cells.
    intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
    EVERY (intcall_expr_producer fp) xs /\ EVERY (supported_expr fp.jc_tops) xs /\
    EVERY (\e. calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr e)) xs /\
    EVERY (\e. !mid. expr_sim_inv ce fp.jc_cx env mid ==>
      expr_body_pre ce fp.jc_cx env e mid) xs /\
    EVERY (\e. ~expr_has_effect e) (xs ++ kws) /\
    compile_ext_call_args compile_expr ce kws (MAP (lowered_value_type ce) xs) xs sa = (vvs,sb) /\
    fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
    intcall_expr_res fp ce env es sa s /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    EVERY (extrequest_snapshot_cell_protected fp.jc_prot fp.jc_morig.vs_memory
      fp.jc_ctx fp.jc_func ce fp.jc_cx (es with gas_obs := []) sa s) old_cells /\
    gas_admissible (bind (eval_exprs fp.jc_cx xs) k) expr_vv_res_ok es /\
    (!vs ee u cells.
      MAP (\(vv,ty,tv,v). vv) cells = vvs /\
      MAP (\(vv,ty,tv,v). ty) cells = MAP (lowered_value_type ce) xs /\
      MAP (\(vv,ty,tv,v). v) cells = vs /\
      EVERY (extrequest_snapshot_cell_protected fp.jc_prot fp.jc_morig.vs_memory
        fp.jc_ctx fp.jc_func ce fp.jc_cx ee sb u) (old_cells ++ cells) /\
      intcall_expr_cont fp ce env es sa s ee sb u /\
      extrequest_history_frame ce fp.jc_cx (es with gas_obs := []) sa s ee sb u /\
      ee.gas_obs = [] /\
      (?used. !tail. eval_exprs fp.jc_cx xs (es with gas_obs := used ++ tail) =
        (INL vs,ee with gas_obs := tail)) ==>
      gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
        (k vs) (ee,u) Q (\r ef z. expr_exit r z)) ==>
    gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
      (bind (eval_exprs fp.jc_cx xs) k) (es,s) Q (\r ef z. expr_exit r z)
Proof
  disch_then (mk_asm "head") >>
  Induct_on `xs` >> rpt gen_tac
  >- (simp[compile_ext_call_args_def, comp_return_def] >>
      rpt strip_tac >> gvs[] >>
      `gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func) (k [])
        (es with gas_obs := [],s) Q (\r ef z. expr_exit r z)` by
        (first_x_assum irule >>
         simp[exprExtRequestHistoryTheory.extrequest_history_frame_refl] >>
         conj_tac
         >- (qexists `[]` >> simp[Once evaluate_def, return_def,
               vyperStateTheory.evaluation_state_component_equality]) >>
         fs[intcall_expr_res_def,
           exprExtRequestHistoryTheory.extrequest_history_frame_refl] >>
         simp[intcall_expr_cont_def, intcall_expr_res_def,
           loweringPostsTheory.locals_kept_def,
           loweringPostsTheory.popped_kept_def] >> metis_tac[]) >>
      simp[Once evaluate_def, bind_return] >>
      qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
      rewrite_tac[gasOutcomeTheory.gas_outcome_def] >> strip_tac
      >- (qexists `marks` >> disj1_tac >>
          gvs[gasSummaryTheory.gas_summary_at_def, gasSummaryTheory.gas_marked_exec_def] >>
          metis_tac[]) >>
      drule stmtSimDeclGasTheory.gas_exempt_cert_start_gas_obs >>
      disch_then (qspec_then `es.gas_obs` mp_tac) >> simp[] >> metis_tac[]) >>
  strip_tac >>
  `~exprs_can_mutate ce (xs ++ kws)` by
    (irule exprExtRequestSnapshotProbeTheory.extrequest_snapshot_tail_no_copy >> gvs[]) >>
  qpat_x_assum `compile_ext_call_args _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_ext_call_args_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rename1 `compile_expr ce (expr_type h) h sa = (head_vv,sm)` >>
  rename1 `compile_snapshot_vv ce F _ sm = (head_sv,sn)` >>
  `ci_mono sa sm` by
    (mp_tac (Q.SPECL [`ce`, `expr_type h`, `h`, `sa`] (cj 1 compile_expr_ci_mono)) >> simp[]) >>
  `ci_mono sm sn` by metis_tac[ci_mono_compile_snapshot_vv, pairTheory.SND] >>
  rename1 `compile_ext_call_args compile_expr ce kws _ xs sn = (tail_vvs,sb)` >>
  `ci_mono sn sb` by
    (qpat_assum `compile_ext_call_args _ _ _ _ _ _ = _` mp_tac >>
     mp_tac (Q.SPECL [`xs`, `MAP (lowered_value_type ce) xs`, `compile_expr`, `ce`, `kws`, `sn`]
       ci_mono_compile_ext_call_args) >>
     simp[cj 1 compile_expr_ci_mono] >> metis_tac[pairTheory.SND]) >>
  `ci_mono sa sn` by metis_tac[ci_mono_trans] >>
  `fn_has_code sa sn fp.jc_func /\ fn_has_code sn sb fp.jc_func` by
    (irule fn_has_code_split >> gvs[ci_mono_def]) >>
  `expr_body_pre ce fp.jc_cx env h es` by
    (fs[intcall_expr_res_def] >> metis_tac[]) >>
  simp[exprSimWordArgsTheory.eval_exprs_cons_action, bind_assoc, bind_return] >>
  once_rewrite_tac[GSYM bind_assoc] >>
  asm "head" irule >>
  qpat_assum `compile_expr _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `compile_snapshot_vv _ _ _ _ = _` (irule_at Any) >>
  simp[] >> conj_tac
  >- (qpat_x_assum `gas_admissible _ _ _` mp_tac >>
      simp[exprSimWordArgsTheory.eval_exprs_cons_action, bind_assoc, bind_return]) >>
  rpt gen_tac >> strip_tac >>
  `ee with gas_obs := [] = ee` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  `gas_admissible (bind (eval_exprs fp.jc_cx xs) (\vs. k (v::vs))) expr_vv_res_ok ee` by
    (qpat_x_assum `gas_admissible _ _ _` mp_tac >>
     simp[exprSimWordArgsTheory.eval_exprs_cons_action, bind_assoc, bind_return] >>
     once_rewrite_tac[GSYM bind_assoc] >>
     strip_tac >> drule stmtSimForRoundsTheory.gas_admissible_bind_tail >>
     disch_then drule >> simp[]) >>
  `intcall_expr_res fp ce env ee sn u /\ ~u.vs_halted /\
    u.vs_current_bb = sn.cs_current_bb /\ u.vs_inst_idx = LENGTH sn.cs_current_insts` by
    fs[intcall_expr_cont_def] >>
  `EVERY (extrequest_snapshot_cell_protected fp.jc_prot fp.jc_morig.vs_memory
      fp.jc_ctx fp.jc_func ce fp.jc_cx ee sn u) old_cells` by
    (fs[listTheory.EVERY_MEM] >> rpt strip_tac >>
     irule exprExtRequestSnapshotStoreInterfaceTheory.extrequest_snapshot_cell_protected_history >>
     qexistsl [`sa`, `es with gas_obs := []`, `s`] >>
     fs[intcall_expr_res_def] >> metis_tac[exprSimWordArgsTheory.stmt_state_rel_gas_obs]) >>
  first_x_assum irule >>
  qpat_assum `compile_ext_call_args _ _ _ _ _ _ = _` (irule_at Any) >>
  qexists `(head_sv,lowered_value_type ce h,tv,v)::old_cells` >>
  simp[] >>
  rpt gen_tac >> strip_tac >>
      qpat_x_assum `!ee u cells. _`
        (qspecl_then [`ee'`, `u'`, `(head_sv,lowered_value_type ce h,tv,v)::cells`] mp_tac) >>
      simp[] >> disch_then irule >> conj_tac
      >- (qexists `used ++ used'` >>
          irule exprExtRequestKwargsTheory.extrequest_kwargs_counted_cons >>
          qexists `ee` >> simp[]) >>
      conj_tac
      >- (irule exprExtRequestHistoryComposeTheory.extrequest_history_frame_trans >>
          conj_tac
          >- (qexistsl [`fp.jc_ctx`, `fp.jc_func`] >>
              fs[intcall_expr_res_def]) >>
          qexistsl [`ee`, `sn`, `u`] >> gvs[]) >>
      irule intcall_expr_cont_trans >> conj_tac >- simp[] >>
      qexistsl [`sn`, `ee`, `u`] >>
      fs[ci_mono_def, exprExtRequestHistoryTheory.extrequest_history_frame_def,
         exprExtRequestReadProbeTheory.extrequest_read_frame_def]
QED

Theorem intcall_ext_positional_cps[local]:
  !xs es sa sb vvs s k old_cells.
    intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
    EVERY (intcall_expr_producer fp) xs /\ EVERY (supported_expr fp.jc_tops) xs /\
    EVERY (\e. calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr e)) xs /\
    EVERY (\e. !mid. expr_sim_inv ce fp.jc_cx env mid ==>
      expr_body_pre ce fp.jc_cx env e mid) xs /\
    EVERY (\e. ~expr_has_effect e) (xs ++ kws) /\
    compile_ext_call_args compile_expr ce kws (MAP (lowered_value_type ce) xs) xs sa = (vvs,sb) /\
    fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
    intcall_expr_res fp ce env es sa s /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    EVERY (extrequest_snapshot_cell_protected fp.jc_prot fp.jc_morig.vs_memory
      fp.jc_ctx fp.jc_func ce fp.jc_cx (es with gas_obs := []) sa s) old_cells /\
    gas_admissible (bind (eval_exprs fp.jc_cx xs) k) expr_vv_res_ok es /\
    (!vs ee u cells.
      MAP (\(vv,ty,tv,v). vv) cells = vvs /\
      MAP (\(vv,ty,tv,v). ty) cells = MAP (lowered_value_type ce) xs /\
      MAP (\(vv,ty,tv,v). v) cells = vs /\
      EVERY (extrequest_snapshot_cell_protected fp.jc_prot fp.jc_morig.vs_memory
        fp.jc_ctx fp.jc_func ce fp.jc_cx ee sb u) (old_cells ++ cells) /\
      intcall_expr_cont fp ce env es sa s ee sb u /\
      extrequest_history_frame ce fp.jc_cx (es with gas_obs := []) sa s ee sb u /\
      ee.gas_obs = [] /\
      (?used. !tail. eval_exprs fp.jc_cx xs (es with gas_obs := used ++ tail) =
        (INL vs,ee with gas_obs := tail)) ==>
      gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
        (k vs) (ee,u) Q (\r ef z. expr_exit r z)) ==>
    gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
      (bind (eval_exprs fp.jc_cx xs) k) (es,s) Q (\r ef z. expr_exit r z)
Proof
  match_mp_tac intcall_ext_positional_from_head >>
  metis_tac[intcall_ext_snapshot_head_cps]
QED

Theorem intcall_ext_kwarg_head_cps[local]:
  intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  intcall_expr_producer fp e /\ supported_expr fp.jc_tops e /\
  calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr e) /\
  expr_body_pre ce fp.jc_cx env e es /\ ~expr_has_effect e /\
  expr_type e = ext_call_kw_type ret kw /\
  compile_ext_call_kwarg compile_expr ce ret kw e sa = ((op,dty),sb) /\
  fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  intcall_expr_res fp ce env es sa s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  extrequest_strong_captures fp.jc_ctx fp.jc_func ce fp.jc_cx old_es old_rs old_vvs
    (es with gas_obs := []) sa s /\
  gas_admissible (bind (bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx)) kont)
    expr_vv_res_ok es /\
  (!v ee u.
    extrequest_kwarg_post fp.jc_ctx fp.jc_func ce fp.jc_cx env ret kw e es sa s sb op dty
      old_es old_rs old_vvs v ee u /\
    extrequest_retained_value ce fp.jc_cx
      (if kw = EKDefault then dty else BaseT (UintT 256)) v op ee sb u /\
    extrequest_history_frame ce fp.jc_cx (es with gas_obs := []) sa s ee sb u /\
    (?used. !tail. bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx)
      (es with gas_obs := used ++ tail) = (INL v,ee with gas_obs := tail)) /\
    intcall_expr_cont fp ce env es sa s ee sb u ==>
    gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
      (kont v) (ee,u) Q (\r ef z. expr_exit r z)) ==>
  gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (bind (bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx)) kont)
    (es,s) Q (\r ef z. expr_exit r z)
Proof
  strip_tac >>
  `?vv sc. compile_expr ce (expr_type e) e sa = (vv,sc) /\
    (if kw = EKDefault /\ ~is_word_type ret then
       compile_materialize_vv ce (lowered_value_type ce e) vv sc = (op,sb)
     else unwrap_value ce vv sc = (op,sb))` by
    (qpat_x_assum `compile_ext_call_kwarg _ _ _ _ _ _ = _` mp_tac >>
     Cases_on `kw` >> Cases_on `is_word_type ret` >>
     simp[compile_ext_call_kwarg_def, lower_value_def, vyperTypeSystemTheory.ext_call_kw_type_def,
       comp_bind_def, comp_return_def] >>
     rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
     metis_tac[pairTheory.PAIR]) >>
  `ci_mono sa sc` by
    (mp_tac (Q.SPECL [`ce`, `expr_type e`, `e`, `sa`]
      (cj 1 compile_expr_ci_mono)) >> simp[]) >>
  `ci_mono sc sb` by
    (Cases_on `kw = EKDefault /\ ~is_word_type ret` >> fs[] >>
     metis_tac[ci_mono_compile_materialize_vv, ci_mono_unwrap_value, pairTheory.SND]) >>
  `fn_has_code sa sc fp.jc_func /\ fn_has_code sc sb fp.jc_func` by
    (irule fn_has_code_split >> gvs[ci_mono_def]) >>
  `gas_admissible (eval_expr fp.jc_cx e) expr_vv_res_ok es` by
    metis_tac[slice_gas_admissible_expr_head, forced_expr_admissible_raw] >>
  `gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (eval_expr fp.jc_cx e) (es,s)
    (\res ee t. ?r. res = INL r /\
      vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx e es sa sc s ee r vv t /\
      vv_storage_live fp.jc_cx vv ee t /\ pure_frame ce fp.jc_func es sa s t /\
      intcall_expr_cont fp ce env es sa s ee sc t)
    (\res ee z. expr_exit res z)` by
    (fs[intcall_expr_producer_def] >>
     first_x_assum (drule_all_then mp_tac) >> strip_tac >>
     irule slice_gas_outcome_conseq >> goal_assum (drule_at Any) >>
     qpat_x_assum `gas_outcome _ _ _ _ _ _ _` kall_tac >>
     qpat_x_assum `!v ee u. _` kall_tac >>
     simp[] >> rpt gen_tac >> strip_tac >> gvs[] >>
     metis_tac[intcall_vv_post_intro]) >>
  rewrite_tac[vyperStateTheory.bind_assoc] >>
  drule (INST_TYPE [alpha |-> ``:eval_result``] extrequest_outcome_bind_result) >>
  disch_then irule >> reverse conj_tac
  >- (rpt gen_tac >> Cases_on `rr` >> simp[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  suspend "kw_capture"
QED

Resume intcall_ext_kwarg_head_cps[kw_capture]:
  `!tail. eval_expr fp.jc_cx e
    (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
    (INL r,mid with gas_obs := tail)` by
      gvs[gasSummaryTheory.gas_marked_exec_def] >>
  `local_ptrs_reserved ce sa /\ stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s` by
    fs[intcall_expr_res_def] >>
  `local_ptrs_reserved ce sc` by metis_tac[exprOperandVarTheory.compiler_ci_mono_reserved] >>
  `!l. vv_operand vv <> Label l` by
    (irule (cj 1 exprExtRequestOperandSafetyTheory.extrequest_compiler_nonlabel) >>
     goal_assum (drule_at Any) >> qexists `env` >>
     qpat_assum `expr_body_pre _ _ _ _ _` mp_tac >>
     simp[NoAsms, exprSimHypsDefsTheory.expr_body_pre_def,
       exprSimHypsDefsTheory.expr_sim_inv_def] >> metis_tac[]) >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sc x` by
    metis_tac[CONJUNCT1 exprOperandVarTheory.compiler_compile_var] >>
  `safe_operand sc (vv_operand vv)` by
    simp[exprSafeOperandTheory.safe_operand_def] >>
  `extrequest_strong_capture fp.jc_ctx fp.jc_func ce fp.jc_cx e r vv
    (mid with gas_obs := []) sc t` by
    (irule exprExtRequestStrongCaptureTheory.extrequest_strong_capture_intro >>
     qpat_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     simp[] >> fs[ci_mono_def] >>
     conj_tac
     >- (rpt strip_tac >> gvs[loweringPostsTheory.vv_storage_live_def,
           vyperStorageBackendTheory.get_storage_def] >> metis_tac[]) >>
     conj_tac
     >- metis_tac[loweringPostsTheory.post_value_type_not_int_call,
         loweringPostsTheory.expr_has_effect_thm] >>
     Cases_on `vv` >> gvs[contextTheory.vv_operand_def]) >>
  `?v. read_result fp.jc_cx r (mid with gas_obs := []) =
    (INL v,mid with gas_obs := [])` by
    metis_tac[exprSimAggregateSourceTheory.vv_post_materialises] >>
  `extrequest_read_frame fp.jc_cx (es with gas_obs := []) (mid with gas_obs := [])` by
    (drule exprExtRequestSourceFrameTheory.extrequest_pure_expr_read_frame >>
     rewrite_tac[vyperCallOutcomeFrameTheory.state_rel_frame_result] >>
     disch_then (qspecl_then [`fp.jc_cx`,
       `es with gas_obs := gas_explicit marks s.vs_gas_readings`,
       `INL r`, `mid with gas_obs := []`] mp_tac) >>
     qpat_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` assume_tac) >>
     fs[exprExtRequestReadProbeTheory.extrequest_read_frame_def]) >>
  `vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx e (es with gas_obs := []) sa sc s
     (mid with gas_obs := []) r vv t` by
    simp[exprSimPropsTheory.vv_post_initial_gas] >>
  `extrequest_history_frame ce fp.jc_cx (es with gas_obs := []) sa s
    (mid with gas_obs := []) sc t` by
    (irule exprExtRequestHistoryTheory.extrequest_history_frame_extend >>
     qpat_assum `vv_post _ _ _ _ _ (es with gas_obs := []) _ _ _ _ _ _ _`
       (irule_at Any) >>
     simp[exprExtRequestHistoryTheory.extrequest_history_frame_refl,
       exprSimWordArgsTheory.stmt_state_rel_gas_obs] >>
     fs[ci_mono_def, loweringPostsTheory.pure_frame_def] >> metis_tac[]) >>
  suspend "kw_suffix"
QED

Resume intcall_ext_kwarg_head_cps[kw_suffix]:
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx (mid with gas_obs := []) t /\
   ~t.vs_halted /\ t.vs_current_bb = sc.cs_current_bb /\
   t.vs_inst_idx = LENGTH sc.cs_current_insts` by
    fs[intcall_expr_cont_def, intcall_expr_res_def] >>
  `(!a k. fp.jc_prot a k ==> a + k <= t.vs_alloca_next /\
    mem_bytes_at a k t.vs_memory = mem_bytes_at a k fp.jc_morig.vs_memory /\
    !i b n. FLOOKUP t.vs_allocas i = SOME (b,n) ==>
      loweringStateRelDefs$regions_disjoint a k b n)` by
    (qpat_x_assum `gas_outcome _ _ _ _ _ _ _` kall_tac >>
     qpat_x_assum `!v ee u. _` kall_tac >>
     fs[intcall_expr_cont_def, intcall_expr_res_def, intcall_frame_ok_def,
        intCallFrameTheory.allocas_above_def,
        loweringStateRelDefsTheory.regions_disjoint_def] >>
     rpt gen_tac >> strip_tac >>
     `a + k <= fp.jc_lo` by metis_tac[] >>
     conj_tac >- decide_tac >> rpt strip_tac >>
     `fp.jc_lo <= b` by metis_tac[] >> decide_tac) >>
  `!tv. evaluate_type (get_tenv fp.jc_cx) (expr_type e) = SOME tv /\
    ~is_word_type (expr_type e) ==>
    type_memory_bytes ce (expr_type e) = type_memory_size tv /\
    type_memory_size tv < 2**64` by
    (rpt strip_tac >>
     `type_memory_bytes ce (expr_type e) = type_memory_size tv` by
       (irule typedMemoryCopyTheory.typed_copy_memory_size >>
        qexists `get_tenv fp.jc_cx` >> simp[] >>
        qpat_assum `expr_body_pre _ _ _ e es` mp_tac >>
        simp[NoAsms, exprSimHypsDefsTheory.expr_body_pre_def,
          exprSimHypsDefsTheory.expr_sim_inv_def] >> metis_tac[]) >>
     simp[] >> `alloc_limits_expr ce e` by fs[exprSimHypsDefsTheory.expr_body_pre_def] >>
     drule exprSimHypsTheory.alloc_limits_expr_type_alloc_ok >>
     simp[allocLimitsTheory.type_alloc_ok_def]) >>
  reverse (Cases_on `kw = EKDefault /\ ~is_word_type ret`)
  >- suspend "kw_unwrap" >>
  suspend "kw_materialize"
QED

Resume intcall_ext_kwarg_head_cps[kw_unwrap]:
  gvs[] >>
  `post_value_type ce e = expr_type e` by
    metis_tac[loweringPostsTheory.post_value_type_not_int_call,
      loweringPostsTheory.expr_has_effect_thm] >>
  `(case vv of StackValue ty a => safe_operand sc a
    | LocatedValue ty p => safe_operand sc p.ptr_operand)` by
    (Cases_on `vv` >> gvs[contextTheory.vv_operand_def]) >>
  `!ty p tr w tv. vv = LocatedValue ty p /\ p.ptr_location = slot_loc tr /\
    eval_operand p.ptr_operand t = SOME w /\
    evaluate_type (get_tenv fp.jc_cx) (expr_type e) = SOME tv ==>
    storage_read_live fp.jc_cx tr (get_storage fp.jc_cx (mid with gas_obs := []) tr) w tv` by
    (rpt strip_tac >>
     `ty = expr_type e` by
       (drule bodyIntCallCompilerTagsTheory.intcall_compile_expr_tag >>
        disch_then (qspecl_then [`expr_type e`, `sa`, `ce`] mp_tac) >>
        simp[contextTheory.vv_type_def]) >>
     gvs[loweringPostsTheory.vv_storage_live_def,
       vyperStorageBackendTheory.get_storage_def] >>
     Cases_on `tr` >> gvs[loweringPostsTheory.slot_loc_def,
       vyperStorageBackendTheory.get_storage_def]) >>
  drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)
    (SRULE [] extcallProtFrameJointUnwrapTheory.extcall_joint_unwrap_read_protected) >>
  disch_then (qspecl_then [`t`, `sc`, `sb`, `fp.jc_prot`, `op`,
    `mid with gas_obs := []`, `fp.jc_morig.vs_memory`] mp_tac) >>
  simp[exprExtRequestHistoryTheory.extrequest_history_frame_refl] >>
  (impl_tac >- metis_tac[ci_mono_def]) >> strip_tac >>
  `v' = v` by
    (qpat_assum `gas_marked_exec _ _ (read_result _ _) _ _ _ _ _` mp_tac >>
     simp[NoAsms, gasSummaryTheory.gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >> gvs[] >>
  `dty = ret` by
    (qpat_x_assum `compile_ext_call_kwarg _ _ _ _ _ _ = _` mp_tac >>
     Cases_on `kw` >> fs[compile_ext_call_kwarg_def, lower_value_def,
       comp_bind_def, comp_return_def, vyperTypeSystemTheory.ext_call_kw_type_def]) >>
  `is_word_type (expr_type e) /\
   (if kw = EKDefault then dty else BaseT (UintT 256)) = expr_type e` by
    (Cases_on `kw` >> fs[vyperTypeSystemTheory.ext_call_kw_type_def,
      compileEnvTheory.is_word_type_def]) >>
  `(do r <- eval_expr fp.jc_cx e; read_result fp.jc_cx r od)
    (es with gas_obs := gas_explicit marks s.vs_gas_readings) =
    (INL v,mid with gas_obs := [])` by
    (qpat_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` assume_tac) >>
     fs[vyperStateTheory.bind_def]) >>
  `expr_body_pre ce fp.jc_cx env e
    (es with gas_obs := gas_explicit marks s.vs_gas_readings)` by simp[] >>
  drule_all extcallProtFrameKwargPrepareTheory.extcall_read_runtime_prepare >> strip_tac >>
  `safe_operand sb op` by
    (irule exprSafeOperandTheory.unwrap_value_safe_operand >>
     goal_assum (drule_at Any) >>
     `vv_type vv = expr_type e` by
       (drule bodyIntCallCompilerTagsTheory.intcall_compile_expr_tag >>
        disch_then (qspecl_then [`expr_type e`, `sa`, `ce`] mp_tac) >> simp[]) >>
     Cases_on `vv` >> gvs[exprSafeOperandTheory.word_result_ok_def,
       contextTheory.vv_type_def, contextTheory.vv_operand_def]) >>
  `~u.vs_halted` by
    (qpat_assum `gas_marked_exec _ _ (read_result _ _) _ _ _ _ _` mp_tac >>
     simp[NoAsms, gasSummaryTheory.gas_marked_exec_def,
       fragGasModeTheory.gas_marked_path_def] >>
     metis_tac[fragGasPathTheory.gas_path_normal]) >>
  suspend "kw_unwrap_finish"
QED

Resume intcall_ext_kwarg_head_cps[kw_unwrap_finish]:
  `extrequest_strong_captures fp.jc_ctx fp.jc_func ce fp.jc_cx old_es old_rs old_vvs
    (mid with gas_obs := []) sc t` by
    (irule exprExtRequestStrongCaptureTheory.extrequest_strong_captures_extend >>
     qpat_assum `extrequest_strong_captures _ _ _ _ _ _ _ _ sa s` (irule_at Any) >>
     qpat_assum `vv_post _ _ _ _ _ (es with gas_obs := []) _ _ _ _ _ _ _` (irule_at Any) >>
     simp[] >> fs[ci_mono_def, loweringPostsTheory.pure_frame_def] >> metis_tac[]) >>
  `extrequest_kwarg_post fp.jc_ctx fp.jc_func ce fp.jc_cx env ret kw e es sa s sb op dty
    old_es old_rs old_vvs v (mid with gas_obs := []) u` by
    (irule exprExtRequestKwargSuffixTheory.extrequest_kwarg_suffix_post >>
     goal_assum (drule_at Any) >> simp[] >>
     fs[loweringPostsTheory.expr_post_def,
       exprExtRequestReadProbeTheory.extrequest_read_frame_def] >>
     conj_tac >- (qexists `tv` >> metis_tac[]) >>
     conj_tac >- (Cases_on `kw = EKDefault` >>
       fs[vyperTypeSystemTheory.ext_call_kw_type_def]) >>
     conj_tac >- (strip_tac >> qexists `tv` >>
       fs[vyperTypeSystemTheory.ext_call_kw_type_def] >> metis_tac[]) >>
     conj_tac >- metis_tac[] >>
     qexistsl [`r`, `sc`, `t`, `gas_explicit marks s.vs_gas_readings`, `vv`] >>
     simp[] >> metis_tac[]) >>
  `extrequest_retained_value ce fp.jc_cx
    (if kw = EKDefault then dty else BaseT (UintT 256)) v op
    (mid with gas_obs := []) sb u` by
    (simp[exprExtRequestRetainedTheory.extrequest_retained_value_def] >>
     fs[loweringPostsTheory.expr_post_def] >> metis_tac[]) >>
  suspend "kw_join"
QED


Resume intcall_ext_kwarg_head_cps[kw_materialize]:
  gvs[] >>
  `expr_type e = ret` by fs[vyperTypeSystemTheory.ext_call_kw_type_def] >>
  `dty = lowered_value_type ce e` by
    (qpat_x_assum `compile_ext_call_kwarg _ _ _ _ _ _ = _` mp_tac >>
     simp[compile_ext_call_kwarg_def, LET_THM, comp_bind_def, comp_return_def] >>
     rpt (pairarg_tac >> gvs[]) >> metis_tac[]) >>
  `(do r <- eval_expr fp.jc_cx e; read_result fp.jc_cx r od)
    (es with gas_obs := gas_explicit marks s.vs_gas_readings) =
    (INL v,mid with gas_obs := [])` by
    (qpat_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` assume_tac) >>
     fs[vyperStateTheory.bind_def]) >>
  `expr_body_pre ce fp.jc_cx env e
    (es with gas_obs := gas_explicit marks s.vs_gas_readings)` by simp[] >>
  drule_all extcallProtFrameKwargPrepareTheory.extcall_default_read_prepare >>
  disch_then (qx_choose_then `dtv` (qx_choose_then `rtv`
    (REPEAT_TCL CONJUNCTS_THEN assume_tac))) >>
  `!v' src z. read_result fp.jc_cx r (mid with gas_obs := []) =
      (INL v',mid with gas_obs := []) /\ expr_val_rel fp.jc_cx (expr_type e) v' src z ==>
    value_has_type dtv v' /\ val_wf dtv v' /\
    expr_val_rel fp.jc_cx (lowered_value_type ce e) v' src z` by
    (rpt strip_tac >> `v' = v` by metis_tac[sumTheory.INL_11, pairTheory.PAIR_EQ] >>
     simp[] >> metis_tac[]) >>
  `post_value_type ce e = expr_type e` by
    metis_tac[loweringPostsTheory.post_value_type_not_int_call,
      loweringPostsTheory.expr_has_effect_thm] >>
  `(case vv of StackValue ty a => safe_operand sc a
    | LocatedValue ty p => safe_operand sc p.ptr_operand)` by
    (Cases_on `vv` >> gvs[contextTheory.vv_operand_def]) >>
  `!ty p tr w tv. vv = LocatedValue ty p /\ p.ptr_location = slot_loc tr /\
    eval_operand p.ptr_operand t = SOME w /\
    evaluate_type (get_tenv fp.jc_cx) (expr_type e) = SOME tv ==>
    storage_read_live fp.jc_cx tr (get_storage fp.jc_cx (mid with gas_obs := []) tr) w tv` by
    (rpt strip_tac >>
     `ty = expr_type e` by
       (drule bodyIntCallCompilerTagsTheory.intcall_compile_expr_tag >>
        disch_then (qspecl_then [`expr_type e`, `sa`, `ce`] mp_tac) >>
        fs[contextTheory.vv_type_def, vyperTypeSystemTheory.ext_call_kw_type_def]) >>
     gvs[loweringPostsTheory.vv_storage_live_def,
       vyperStorageBackendTheory.get_storage_def] >>
     Cases_on `tr` >> gvs[loweringPostsTheory.slot_loc_def,
       vyperStorageBackendTheory.get_storage_def]) >>
  drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)
    (SRULE [] extcallProtFrameKwargMaterializeTheory.extcall_materialize_read_protected) >>
  disch_then (qspecl_then [`t`, `sc`, `sb`, `fp.jc_prot`,
    `mid with gas_obs := []`, `lowered_value_type ce e`, `dtv`, `op`,
    `fp.jc_morig.vs_memory`] mp_tac) >>
  simp[exprExtRequestHistoryTheory.extrequest_history_frame_refl] >>
  (impl_tac >- metis_tac[ci_mono_def, vyperTypeSystemTheory.ext_call_kw_type_def,
    exprSimWordArgsTheory.stmt_state_rel_gas_obs]) >> strip_tac >>
  suspend "kw_materialize_finish"
QED

Resume intcall_ext_kwarg_head_cps[kw_materialize_finish]:
  `v' = v` by
    (qpat_assum `gas_marked_exec _ _ (read_result _ _) _ _ _ _ _` mp_tac >>
     simp[NoAsms, gasSummaryTheory.gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  gvs[] >>
  `extrequest_strong_captures fp.jc_ctx fp.jc_func ce fp.jc_cx old_es old_rs old_vvs
    (mid with gas_obs := []) sc t` by
    (irule exprExtRequestStrongCaptureTheory.extrequest_strong_captures_extend >>
     qpat_assum `extrequest_strong_captures _ _ _ _ _ _ _ _ sa s` (irule_at Any) >>
     qpat_assum `vv_post _ _ _ _ _ (es with gas_obs := []) _ _ _ _ _ _ _` (irule_at Any) >>
     simp[] >> fs[ci_mono_def, loweringPostsTheory.pure_frame_def] >> metis_tac[]) >>
  `extrequest_kwarg_post fp.jc_ctx fp.jc_func ce fp.jc_cx env (expr_type e) EKDefault e es sa s sb op
    (lowered_value_type ce e) old_es old_rs old_vvs v (mid with gas_obs := []) z` by
    (irule exprExtRequestKwargSuffixTheory.extrequest_kwarg_suffix_post >>
     goal_assum (drule_at Any) >> simp[vyperTypeSystemTheory.ext_call_kw_type_def] >>
     fs[exprExtRequestReadProbeTheory.extrequest_read_frame_def] >> metis_tac[]) >>
  `sc.cs_next_id < sb.cs_next_id` by
    (qpat_assum `compile_materialize_vv _ _ _ _ = _` mp_tac >>
     simp[NoAsms, compile_materialize_vv_def, comp_bind_def, comp_return_def] >>
     rpt (pairarg_tac >> gvs[]) >> strip_tac >>
     drule loweringHaltTheory.compile_alloc_buffer_parts >> strip_tac >>
     rename1 `unwrap_value ce vv ca = (src,cu)` >>
     `ci_mono ca cu` by metis_tac[ci_mono_unwrap_value, pairTheory.SND] >>
     qpat_x_assum `do compile_store_memory _ _ _ _ _; _ od _ = _` mp_tac >>
     simp[NoAsms, comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
     pairarg_tac >> gvs[] >> strip_tac >>
     `ci_mono cu sb` by metis_tac[ci_mono_compile_store_memory, pairTheory.SND] >>
     fs[ci_mono_def]) >>
  `extrequest_retained_value ce fp.jc_cx (lowered_value_type ce e) v op
    (mid with gas_obs := []) sb z` by
    (irule extcallProtFrameKwargPrepareTheory.extcall_materialized_retained >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  rename1 `gas_marked_exec _ _ (read_result _ _) _ _ _ _ (OK u)` >>
  suspend "kw_join_mat"
QED
Resume intcall_ext_kwarg_head_cps[kw_join_mat]:
  markerLib.RESUME_TAC >> (
  `extrequest_history_frame ce fp.jc_cx (es with gas_obs := []) sa s
    (mid with gas_obs := []) sb u` by
    (irule exprExtRequestHistoryComposeTheory.extrequest_history_frame_trans >>
     qpat_assum `extrequest_history_frame _ _ _ sa s _ sc t` (irule_at Any) >>
     simp[] >> metis_tac[exprSimWordArgsTheory.stmt_state_rel_gas_obs]) >>
  `extrequest_history_frame ce fp.jc_cx es sa s (mid with gas_obs := []) sb u` by
    (qpat_assum `extrequest_history_frame _ _ (es with gas_obs := []) sa s _ sb u` mp_tac >>
     simp[NoAsms, exprExtRequestHistoryTheory.extrequest_history_frame_def,
       exprExtRequestReadProbeTheory.extrequest_read_frame_def] >>
     strip_tac >> gvs[] >> metis_tac[]) >>
  `?n. gas_marked_path F fp.jc_ctx fp.jc_func s n (OK u)` by
    (qpat_assum `gas_marked_exec _ _ (eval_expr _ _) _ _ _ _ _` mp_tac >>
     qpat_assum `gas_marked_exec _ _ (read_result _ _) _ _ _ _ _` mp_tac >>
     simp[NoAsms, gasSummaryTheory.gas_marked_exec_def] >>
     metis_tac[fragGasModeTheory.gas_marked_path_then]) >>
  `expr_sim_inv ce fp.jc_cx env (mid with gas_obs := [])` by
    fs[intcall_expr_cont_def, intcall_expr_res_def] >>
  `(mid with gas_obs := []).immutables = es.immutables` by
    (`supported_pure_expr fp.jc_tops e` by
       metis_tac[supportedExprsTheory.supported_expr_def,
         supportedExprTraverseTheory.supported_effects_have_effect] >>
     qpat_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` mp_tac) >>
     strip_tac >> drule_all bodyIntCallJointCallSourceTheory.intcall_pure_expr_immutables >> simp[]) >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx (mid with gas_obs := []) u` by
    fs[exprExtRequestKwargSuffixTheory.extrequest_kwarg_post_def] >>
  `intcall_expr_cont fp ce env es sa s (mid with gas_obs := []) sb u` by
    (irule intcall_ext_history_cont >> simp[] >>
     fs[intcall_expr_res_def] >> metis_tac[]) >>
  `!tail. bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx)
    (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
    (INL v,mid with gas_obs := tail)` by
    (drule_all exprExtRequestKwargSuffixTheory.extrequest_kwarg_counted_read >> simp[]) >>
  irule exprExtRequestKwargSuffixTheory.extrequest_kwarg_suffix_cps >>
  qpat_assum `gas_marked_exec _ _ (read_result _ _) _ _ _ _ _` (irule_at Any) >>
  simp[] >> first_x_assum irule >> simp[] >>
  metis_tac[] )
QED
Resume intcall_ext_kwarg_head_cps[kw_join]:
  `extrequest_history_frame ce fp.jc_cx (es with gas_obs := []) sa s
    (mid with gas_obs := []) sb u` by
    (irule exprExtRequestHistoryComposeTheory.extrequest_history_frame_trans >>
     qpat_assum `extrequest_history_frame _ _ _ sa s _ sc t` (irule_at Any) >>
     simp[] >> metis_tac[exprSimWordArgsTheory.stmt_state_rel_gas_obs]) >>
  `extrequest_history_frame ce fp.jc_cx es sa s (mid with gas_obs := []) sb u` by
    (qpat_assum `extrequest_history_frame _ _ (es with gas_obs := []) sa s _ sb u` mp_tac >>
     simp[NoAsms, exprExtRequestHistoryTheory.extrequest_history_frame_def,
       exprExtRequestReadProbeTheory.extrequest_read_frame_def] >>
     strip_tac >> gvs[] >> metis_tac[]) >>
  `?n. gas_marked_path F fp.jc_ctx fp.jc_func s n (OK u)` by
    (qpat_assum `gas_marked_exec _ _ (eval_expr _ _) _ _ _ _ _` mp_tac >>
     qpat_assum `gas_marked_exec _ _ (read_result _ _) _ _ _ _ _` mp_tac >>
     simp[NoAsms, gasSummaryTheory.gas_marked_exec_def] >>
     metis_tac[fragGasModeTheory.gas_marked_path_then]) >>
  `expr_sim_inv ce fp.jc_cx env (mid with gas_obs := [])` by
    fs[intcall_expr_cont_def, intcall_expr_res_def] >>
  `(mid with gas_obs := []).immutables = es.immutables` by
    (`supported_pure_expr fp.jc_tops e` by
       metis_tac[supportedExprsTheory.supported_expr_def,
         supportedExprTraverseTheory.supported_effects_have_effect] >>
     qpat_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` mp_tac) >>
     strip_tac >> drule_all bodyIntCallJointCallSourceTheory.intcall_pure_expr_immutables >> simp[]) >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx (mid with gas_obs := []) u` by
    fs[exprExtRequestKwargSuffixTheory.extrequest_kwarg_post_def] >>
  `intcall_expr_cont fp ce env es sa s (mid with gas_obs := []) sb u` by
    (irule intcall_ext_history_cont >> simp[] >>
     fs[intcall_expr_res_def] >> metis_tac[]) >>
  `!tail. bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx)
    (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
    (INL v,mid with gas_obs := tail)` by
    (drule_all exprExtRequestKwargSuffixTheory.extrequest_kwarg_counted_read >> simp[]) >>
  irule exprExtRequestKwargSuffixTheory.extrequest_kwarg_suffix_cps >>
  qpat_assum `gas_marked_exec _ _ (read_result _ _) _ _ _ _ _` (irule_at Any) >>
  simp[] >> first_x_assum irule >> simp[] >> metis_tac[]
QED
Finalise intcall_ext_kwarg_head_cps

Theorem intcall_ext_kwargs_fold_from_head[local]:
  (!e es sa sb s ret kw op dty old_es old_rs old_vvs kont Q.
    intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
    intcall_expr_producer fp e /\ supported_expr fp.jc_tops e /\
    calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr e) /\
    expr_body_pre ce fp.jc_cx env e es /\ ~expr_has_effect e /\
    expr_type e = ext_call_kw_type ret kw /\
    compile_ext_call_kwarg compile_expr ce ret kw e sa = ((op,dty),sb) /\
    fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
    intcall_expr_res fp ce env es sa s /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    extrequest_strong_captures fp.jc_ctx fp.jc_func ce fp.jc_cx old_es old_rs old_vvs
      (es with gas_obs := []) sa s /\
    gas_admissible (bind (bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx)) kont)
      expr_vv_res_ok es /\
    (!v ee u.
      extrequest_kwarg_post fp.jc_ctx fp.jc_func ce fp.jc_cx env ret kw e es sa s sb op dty
        old_es old_rs old_vvs v ee u /\
      extrequest_retained_value ce fp.jc_cx
        (if kw = EKDefault then dty else BaseT (UintT 256)) v op ee sb u /\
      extrequest_history_frame ce fp.jc_cx (es with gas_obs := []) sa s ee sb u /\
      (?used. !tail. bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx)
        (es with gas_obs := used ++ tail) = (INL v,ee with gas_obs := tail)) /\
      intcall_expr_cont fp ce env es sa s ee sb u ==>
      gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
        (kont v) (ee,u) Q (\r ef z. expr_exit r z)) ==>
    gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
      (bind (bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx)) kont)
      (es,s) Q (\r ef z. expr_exit r z)) ==>
  !ks xs es sa sb value_op gas_op default_op s k old_es old_rs old_vvs.
    intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
    LENGTH ks = LENGTH xs /\ EVERY (intcall_expr_producer fp) xs /\
    EVERY (supported_expr fp.jc_tops) xs /\
    EVERY (\e. calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr e)) xs /\
    EVERY (\e. ~expr_has_effect e) xs /\
    (!i ee. i < LENGTH xs /\ extrequest_kwargs_reach fp.jc_cx xs es i ee ==>
      expr_body_pre ce fp.jc_cx env (EL i xs) ee) /\
    (!i. i < LENGTH xs ==> expr_type (EL i xs) =
      (if EL i ks = EKDefault then ret else BaseT (UintT 256))) /\
    compile_ext_call_kwargs compile_expr ce ret ks xs sa = ((value_op,gas_op,default_op),sb) /\
    fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
    intcall_expr_res fp ce env es sa s /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    extrequest_strong_captures fp.jc_ctx fp.jc_func ce fp.jc_cx old_es old_rs old_vvs
      (es with gas_obs := []) sa s /\
    gas_admissible (bind (eval_exprs fp.jc_cx xs) k) expr_vv_res_ok es /\
    (!vs ee u.
      extrequest_kwargs_post fp.jc_ctx fp.jc_func ce fp.jc_cx ret ks xs es sa s sb
        value_op gas_op default_op old_es old_rs old_vvs vs ee u /\
      intcall_expr_cont fp ce env es sa s ee sb u ==>
      gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
        (k vs) (ee,u) Q (\r ef z. expr_exit r z)) ==>
    gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
      (bind (eval_exprs fp.jc_cx xs) k) (es,s) Q (\r ef z. expr_exit r z)
Proof
  disch_then (mk_asm "head") >>
  Induct_on `ks` >> rpt gen_tac
  >- (Cases_on `xs` >> simp[compile_ext_call_kwargs_def, comp_return_def] >>
      rpt strip_tac >> gvs[] >>
      `gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func) (k [])
        (es with gas_obs := [],s) Q (\r ef z. expr_exit r z)` by
        (first_x_assum irule >> conj_tac
         >- (fs[intcall_expr_res_def] >>
             simp[intcall_expr_cont_def, intcall_expr_res_def,
               loweringPostsTheory.locals_kept_def, loweringPostsTheory.popped_kept_def] >>
             metis_tac[]) >>
         irule exprExtRequestKwargsTheory.extrequest_kwargs_post_nil >>
         fs[intcall_expr_res_def]) >>
      simp[Once evaluate_def, bind_return] >>
      qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
      rewrite_tac[gasOutcomeTheory.gas_outcome_def] >> strip_tac
      >- (qexists `marks` >> disj1_tac >>
          gvs[gasSummaryTheory.gas_summary_at_def, gasSummaryTheory.gas_marked_exec_def] >>
          metis_tac[]) >>
      drule stmtSimDeclGasTheory.gas_exempt_cert_start_gas_obs >>
      disch_then (qspec_then `es.gas_obs` mp_tac) >> simp[] >> metis_tac[]) >>
  qpat_x_assum `!xs es sa sb value_op gas_op default_op s k old_es old_rs old_vvs. _`
    (mk_asm "tail_ih") >>
  Cases_on `xs` >- simp[NoAsms] >>
  simp[NoAsms, Once compile_ext_call_kwargs_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >>
  qpat_x_assum `!vs ee u. _` (mk_asm "continuation") >>
  rename1 `compile_ext_call_kwarg compile_expr ce ret kw e sa = ((op,dty),sm)` >>
  qpat_x_assum `comp_bind _ _ sm = _` mp_tac >>
  simp[comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[comp_return_def] >>
  rename1 `compile_ext_call_kwargs compile_expr ce ret ks xs sm = ((vo,go,dopt),sb)` >>
  `ci_mono sa sm` by
    (mp_tac (Q.SPECL [`compile_expr`, `ce`, `ret`, `kw`, `e`, `sa`]
      ci_mono_compile_ext_call_kwarg) >> simp[cj 1 compile_expr_ci_mono]) >>
  `ci_mono sm sb` by
    (mp_tac (Q.SPECL [`ks`, `xs`, `ce`, `ret`, `sm`]
      exprExtRequestKwargsTheory.extrequest_kwargs_mono) >> simp[]) >>
  `fn_has_code sa sm fp.jc_func /\ fn_has_code sm sb fp.jc_func` by
    (irule fn_has_code_split >> fs[ci_mono_def]) >>
  `expr_body_pre ce fp.jc_cx env e es` by
    (qpat_x_assum `!i ee. _` (qspecl_then [`0`, `es with gas_obs := []`] mp_tac) >> simp[]) >>
  `expr_type e = ext_call_kw_type ret kw` by
    (qpat_x_assum `!i. _` (qspec_then `0` mp_tac) >>
     Cases_on `kw` >> simp[vyperTypeSystemTheory.ext_call_kw_type_def]) >>
  rewrite_tac[exprExtRequestKwargsTheory.extrequest_kwargs_bind_cons] >>
  asm "head" irule >>
  qpat_assum `compile_ext_call_kwarg _ _ _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `extrequest_strong_captures _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[GSYM exprExtRequestKwargsTheory.extrequest_kwargs_bind_cons] >>
  suspend "kwargs_head_cont"
QED

Resume intcall_ext_kwargs_fold_from_head[kwargs_head_cont]:
  rpt gen_tac >> strip_tac >>
  rename1 `extrequest_kwarg_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ v mid tm` >>
  `mid.gas_obs = [] /\
   extrequest_strong_captures fp.jc_ctx fp.jc_func ce fp.jc_cx old_es old_rs old_vvs mid sm tm` by
    fs[exprExtRequestKwargSuffixTheory.extrequest_kwarg_post_def] >>
  `mid with gas_obs := [] = mid` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  `intcall_expr_res fp ce env mid sm tm /\ ~tm.vs_halted /\
   tm.vs_current_bb = sm.cs_current_bb /\ tm.vs_inst_idx = LENGTH sm.cs_current_insts` by
    fs[intcall_expr_cont_def] >>
  `gas_admissible (bind (eval_exprs fp.jc_cx xs) (\vs. k (v::vs))) expr_vv_res_ok mid` by
    (qpat_assum `gas_admissible _ _ es` mp_tac >>
     rewrite_tac[exprExtRequestKwargsTheory.extrequest_kwargs_bind_cons] >> strip_tac >>
     drule_all stmtSimForRoundsTheory.gas_admissible_bind_tail >> simp[]) >>
  `!i ee. i < LENGTH xs /\ extrequest_kwargs_reach fp.jc_cx xs mid i ee ==>
    expr_body_pre ce fp.jc_cx env (EL i xs) ee` by
    (rpt strip_tac >>
     `extrequest_kwargs_reach fp.jc_cx (e::xs) es (SUC i) ee` by
       (irule exprExtRequestKwargsTheory.extrequest_kwargs_reach_cons >>
        goal_assum (drule_at Any) >> simp[]) >>
     qpat_x_assum `!i ee. i < SUC _ /\ _ ==> _`
       (qspecl_then [`SUC i`, `ee`] mp_tac) >> simp[]) >>
  asm "tail_ih" irule >>
  qpat_assum `compile_ext_call_kwargs _ _ _ _ _ _ = _` (irule_at Any) >>
  qexistsl [`old_vvs`, `old_rs`, `old_es`] >> simp[] >>
  suspend "kwargs_tail_cont"
QED

Resume intcall_ext_kwargs_fold_from_head[kwargs_tail_cont]:
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!i. i < SUC _ ==> _` (qspec_then `SUC i` mp_tac) >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  asm "continuation" irule >> simp[] >> conj_tac
  >- (irule intcall_expr_cont_trans >> conj_tac >- simp[] >>
      qexistsl [`sm`, `mid`, `tm`] >>
      fs[ci_mono_def, exprExtRequestHistoryTheory.extrequest_history_frame_def,
        exprExtRequestReadProbeTheory.extrequest_read_frame_def]) >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s /\ local_ptrs_reserved ce sa` by
    fs[intcall_expr_res_def] >>
  drule_all exprExtRequestKwargsTheory.extrequest_kwargs_post_cons >>
  Cases_on `kw` >> gvs[] >> metis_tac[]
QED
Finalise intcall_ext_kwargs_fold_from_head
Theorem intcall_ext_kwargs_cps[local]:
  !ks xs es sa sb value_op gas_op default_op s k old_es old_rs old_vvs.
    intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
    LENGTH ks = LENGTH xs /\ EVERY (intcall_expr_producer fp) xs /\
    EVERY (supported_expr fp.jc_tops) xs /\
    EVERY (\e. calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr e)) xs /\
    EVERY (\e. ~expr_has_effect e) xs /\
    (!i ee. i < LENGTH xs /\ extrequest_kwargs_reach fp.jc_cx xs es i ee ==>
      expr_body_pre ce fp.jc_cx env (EL i xs) ee) /\
    (!i. i < LENGTH xs ==> expr_type (EL i xs) =
      (if EL i ks = EKDefault then ret else BaseT (UintT 256))) /\
    compile_ext_call_kwargs compile_expr ce ret ks xs sa = ((value_op,gas_op,default_op),sb) /\
    fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
    intcall_expr_res fp ce env es sa s /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    extrequest_strong_captures fp.jc_ctx fp.jc_func ce fp.jc_cx old_es old_rs old_vvs
      (es with gas_obs := []) sa s /\
    gas_admissible (bind (eval_exprs fp.jc_cx xs) k) expr_vv_res_ok es /\
    (!vs ee u.
      extrequest_kwargs_post fp.jc_ctx fp.jc_func ce fp.jc_cx ret ks xs es sa s sb
        value_op gas_op default_op old_es old_rs old_vvs vs ee u /\
      intcall_expr_cont fp ce env es sa s ee sb u ==>
      gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
        (k vs) (ee,u) Q (\r ef z. expr_exit r z)) ==>
    gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
      (bind (eval_exprs fp.jc_cx xs) k) (es,s) Q (\r ef z. expr_exit r z)
Proof
  match_mp_tac intcall_ext_kwargs_fold_from_head >>
  metis_tac[intcall_ext_kwarg_head_cps]
QED


Theorem intcall_ext_operands_cps[local]:
  (!e. expr_size e < expr_size (Call ann (ExtCall stat skip (fname,ats,rt) opts) (a::rest) NONE) ==>
    intcall_expr_producer fp e /\ intcall_forced_producer fp e /\ intcall_map_producer fp e) /\
  intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  expr_body_pre ce fp.jc_cx env
    (Call ann (ExtCall stat skip (fname,ats,rt) opts) (a::rest) NONE) es /\
  supported_expr fp.jc_tops
    (Call ann (ExtCall stat skip (fname,ats,rt) opts) (a::rest) NONE) /\
  calls_follow_call_graph fp.jc_edges fp.jc_owner
    (int_calls_expr (Call ann (ExtCall stat skip (fname,ats,rt) opts) (a::rest) NONE)) /\
  lower_value compile_expr ce (BaseT AddressT) a sa = (addr_op,s1) /\
  compile_ext_call_args compile_expr ce (DROP (LENGTH ats) rest)
    (MAP (lowered_value_type ce) (TAKE (LENGTH ats) rest))
    (TAKE (LENGTH ats) rest) s1 = (arg_vvs,s2) /\
  compile_ext_call_kwargs compile_expr ce rt opts (DROP (LENGTH ats) rest) s2 =
    ((value_op,gas_op,default_op),s3) /\
  fn_has_code sa s1 fp.jc_func /\ fn_has_code s1 s2 fp.jc_func /\
  fn_has_code s2 s3 fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  intcall_expr_res fp ce env es sa s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  gas_admissible
    (bind (bind (eval_expr fp.jc_cx a) (read_result fp.jc_cx))
      (\target. bind (eval_exprs fp.jc_cx (TAKE (LENGTH ats) rest))
        (\posvs. bind (eval_exprs fp.jc_cx (DROP (LENGTH ats) rest)) (kont target posvs))))
    expr_vv_res_ok es /\
  (!target posvs kwvs esA esB tB ee t target_addr cells.
    (?used. !tail. bind (eval_expr fp.jc_cx a) (read_result fp.jc_cx)
      (es with gas_obs := used ++ tail) = (INL target,esA with gas_obs := tail)) /\
    dest_AddressV target = SOME target_addr /\
    eval_operand addr_op t = SOME (w2w target_addr) /\ safe_operand s3 addr_op /\
    (?used. !tail. eval_exprs fp.jc_cx (TAKE (LENGTH ats) rest)
      (esA with gas_obs := used ++ tail) = (INL posvs,esB with gas_obs := tail)) /\
    MAP (\(vv,ty,tv,v). vv) cells = arg_vvs /\
    MAP (\(vv,ty,tv,v). ty) cells = MAP (lowered_value_type ce) (TAKE (LENGTH ats) rest) /\
    MAP (\(vv,ty,tv,v). v) cells = posvs /\
    EVERY (extrequest_snapshot_cell_protected fp.jc_prot fp.jc_morig.vs_memory
      fp.jc_ctx fp.jc_func ce fp.jc_cx ee s3 t) cells /\
    extrequest_kwargs_post fp.jc_ctx fp.jc_func ce fp.jc_cx rt opts (DROP (LENGTH ats) rest)
      esB s2 tB s3 value_op gas_op default_op [] [] [] kwvs ee t /\
    wb_frame ce es ee sa s t /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
    sa.cs_next_var <= s3.cs_next_var /\ sa.cs_next_id <= s3.cs_next_id /\
    intcall_expr_cont fp ce env es sa s ee s3 t ==>
    gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func) (kont target posvs kwvs)
      (ee,t) Q (\r ef z. expr_exit r z)) ==>
  gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (bind (bind (eval_expr fp.jc_cx a) (read_result fp.jc_cx))
      (\target. bind (eval_exprs fp.jc_cx (TAKE (LENGTH ats) rest))
        (\posvs. bind (eval_exprs fp.jc_cx (DROP (LENGTH ats) rest)) (kont target posvs))))
    (es,s) Q (\r ef z. expr_exit r z)
Proof
  strip_tac >>
  drule exprExtRequestShapeTheory.extrequest_body_typed >> strip_tac >>
  `expr_body_pre ce fp.jc_cx env a es` by
    (irule exprExtRequestShapeTheory.extrequest_body_pre_arg >>
     first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >>
     gvs[exprSimHypsDefsTheory.expr_body_pre_def]) >>
  `expr_type a = BaseT AddressT` by
    (qpat_assum `well_typed_expr _ (Call _ _ _ _)` mp_tac >>
     simp[NoAsms, Once vyperTypeSystemTheory.well_typed_expr_def]) >>
  suspend "operand_support"
QED

Resume intcall_ext_operands_cps[operand_support]:
  `supported_pure_exprs fp.jc_tops (a::rest)` by
    (fs[supportedExprsTheory.supported_expr_def,
        supportedExprsTheory.supported_pure_call_pop_rejected,
        supportedExprsTheory.supported_external_call_contract]) >>
  `supported_expr fp.jc_tops a` by
    fs[supportedExprsTheory.supported_pure_exprs_every,
       supportedExprsTheory.supported_expr_def] >>
  `supported_pure_expr fp.jc_tops a` by
    fs[supportedExprsTheory.supported_pure_exprs_every] >>
  `int_calls_expr a = []` by
    metis_tac[bodyExprPreFactsTheory.supported_pure_int_calls] >>
  `calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr a)` by simp[] >>
  `intcall_forced_producer fp a` by
    (first_x_assum (qspec_then `a` mp_tac) >>
     simp[vyperASTTheory.expr_size_def]) >>
  irule intcall_ext_target_cps >>
  first_assum (irule_at (Pat `lower_value _ _ _ _ _ = _`)) >>
  simp[] >> qexists `env` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  suspend "target_endpoint"
QED
Resume intcall_ext_operands_cps[target_endpoint]:
  `gas_admissible
    (bind (eval_exprs fp.jc_cx (TAKE (LENGTH ats) rest))
      (\posvs. bind (eval_exprs fp.jc_cx (DROP (LENGTH ats) rest)) (kont v posvs)))
    expr_vv_res_ok ee` by
    (drule_all stmtSimForRoundsTheory.gas_admissible_bind_tail >> simp[]) >>
  `EVERY (intcall_expr_producer fp) rest` by
    (simp[listTheory.EVERY_MEM] >> rpt strip_tac >>
     first_x_assum (qspec_then `e` mp_tac) >>
     drule exprCallBoundsTheory.expr_list_member_bound >>
     simp[vyperASTTheory.expr_size_def] >> rpt strip_tac >> fs[]) >>
  `EVERY (supported_expr fp.jc_tops) rest /\
   EVERY (\e. calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr e)) rest` by
    (fs[supportedExprsTheory.supported_pure_exprs_every, listTheory.EVERY_MEM] >>
     metis_tac[supportedExprsTheory.supported_expr_def,
       bodyExprPreFactsTheory.supported_pure_int_calls,
       vyperTypeCallStackSoundnessTheory.calls_follow_call_graph_nil]) >>
  `EVERY (\e. !mid. expr_sim_inv ce fp.jc_cx env mid ==>
    expr_body_pre ce fp.jc_cx env e mid) rest` by
    (drule exprExtRequestStagesSourceTheory.extrequest_operand_body_pre >> simp[]) >>
  irule intcall_ext_positional_cps >>
  first_assum (irule_at (Pat `compile_ext_call_args _ _ _ _ _ _ = _`)) >>
  qexists `[]` >> simp[listTheory.TAKE_DROP] >>
  qexists `env` >>
  `intcall_expr_res fp ce env ee s1 u /\ ~u.vs_halted /\
   u.vs_current_bb = s1.cs_current_bb /\ u.vs_inst_idx = LENGTH s1.cs_current_insts` by
    fs[intcall_expr_cont_def] >>
  simp[] >>
  conj_tac >- metis_tac[rich_listTheory.EVERY_TAKE] >>
  conj_tac >- metis_tac[rich_listTheory.EVERY_TAKE] >>
  conj_tac >- metis_tac[rich_listTheory.EVERY_TAKE] >>
  reverse conj_tac >-
    (fs[] >> metis_tac[rich_listTheory.EVERY_TAKE, rich_listTheory.EVERY_DROP]) >>
  rpt gen_tac >> strip_tac >>
  suspend "positional_endpoint"
QED
Resume intcall_ext_operands_cps[positional_endpoint]:
  rename1 `intcall_expr_cont fp ce env ee s1 u pos_end s2 pos_state` >>
  `gas_admissible (bind (eval_exprs fp.jc_cx (DROP (LENGTH ats) rest))
    (kont v (MAP (\(vv,ty,tv,v). v) cells))) expr_vv_res_ok pos_end` by
    (drule_all stmtSimForRoundsTheory.gas_admissible_bind_tail >> simp[]) >>
  `LENGTH opts = LENGTH (DROP (LENGTH ats) rest)` by
    (fs[supportedExprsTheory.supported_expr_def,
        supportedExprsTheory.supported_pure_call_pop_rejected,
        supportedExprsTheory.supported_external_call_contract]) >>
  `intcall_expr_res fp ce env pos_end s2 pos_state /\ ~pos_state.vs_halted /\
   pos_state.vs_current_bb = s2.cs_current_bb /\
   pos_state.vs_inst_idx = LENGTH s2.cs_current_insts /\
   expr_sim_inv ce fp.jc_cx env pos_end` by
    (fs[intcall_expr_cont_def, intcall_expr_res_def] >> metis_tac[]) >>
  `EVERY (\e. ~expr_has_effect e) (DROP (LENGTH ats) rest)` by
    (fs[] >> metis_tac[rich_listTheory.EVERY_DROP]) >>
  `!i ef. i < LENGTH (DROP (LENGTH ats) rest) /\
    extrequest_kwargs_reach fp.jc_cx (DROP (LENGTH ats) rest) pos_end i ef ==>
    expr_body_pre ce fp.jc_cx env (EL i (DROP (LENGTH ats) rest)) ef` by
    (rpt strip_tac >> irule exprExtRequestStagesSourceTheory.extrequest_kwargs_reach_pre >>
     simp[] >> conj_tac >- metis_tac[rich_listTheory.EVERY_DROP] >>
     qexists `pos_end` >> simp[]) >>
  irule intcall_ext_kwargs_cps >>
  first_assum (irule_at (Pat `compile_ext_call_kwargs _ _ _ _ _ _ = _`)) >>
  qexistsl [`[]`, `[]`, `[]`, `env`] >>
  simp[exprExtRequestStrongCaptureTheory.extrequest_strong_captures_def] >>
  conj_tac >- metis_tac[rich_listTheory.EVERY_DROP] >>
  conj_tac >- metis_tac[rich_listTheory.EVERY_DROP] >>
  conj_tac >- metis_tac[rich_listTheory.EVERY_DROP] >>
  reverse conj_tac >- suspend "kwarg_types" >>
  rpt gen_tac >> strip_tac >>
  suspend "kwargs_endpoint"
QED
Resume intcall_ext_operands_cps[kwarg_types]:
  qpat_assum `well_typed_expr _ (Call _ _ _ _)` mp_tac >>
  simp[NoAsms, Once vyperTypeSystemTheory.well_typed_expr_def] >>
  strip_tac >> rpt strip_tac >>
  `i < LENGTH opts /\ i < LENGTH (DROP (LENGTH ats) rest)` by fs[] >>
  `EL i (MAP expr_type (DROP (LENGTH ats) rest)) =
   EL i (MAP (ext_call_kw_type rt) opts)` by simp[] >>
  qpat_x_assum `EL i (MAP expr_type _) = _` mp_tac >>
  simp[listTheory.EL_MAP, listTheory.LENGTH_DROP] >>
  Cases_on `EL i opts` >> fs[vyperTypeSystemTheory.ext_call_kw_type_def]
QED
Resume intcall_ext_operands_cps[kwargs_endpoint]:
  rename1 `intcall_expr_cont fp ce env pos_end s2 pos_state kw_end s3 kw_state` >>
  `ci_mono sa s1` by
    (mp_tac (Q.SPECL [`ce`, `BaseT AddressT`, `a`, `sa`]
      exprLoweringPropsTheory.ci_mono_lower_value_compile_expr) >> simp[]) >>
  `ci_mono s1 s2` by
    (qpat_assum `compile_ext_call_args _ _ _ _ _ _ = _` mp_tac >>
     mp_tac (Q.SPECL [`TAKE (LENGTH (ats:type list)) rest`,
       `MAP (lowered_value_type ce) (TAKE (LENGTH (ats:type list)) rest)`,
       `compile_expr`, `ce`, `DROP (LENGTH (ats:type list)) rest`, `s1`]
       exprLoweringPropsTheory.ci_mono_compile_ext_call_args) >>
     simp[cj 1 exprLoweringPropsTheory.compile_expr_ci_mono]) >>
  qpat_assum `extrequest_kwargs_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o SRULE [exprExtRequestKwargsTheory.extrequest_kwargs_post_def]) >>
  `sa.cs_next_var <= s2.cs_next_var /\ sa.cs_next_id <= s2.cs_next_id` by
    (fs[exprLoweringPropsTheory.ci_mono_def] >> decide_tac) >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes /\
   sa.cs_next_var <= s1.cs_next_var /\ sa.cs_next_id <= s1.cs_next_id` by
    fs[loweringPostsTheory.expr_post_def, loweringPostsTheory.locals_kept_def,
       exprLoweringPropsTheory.ci_mono_def] >>
  `MAP FDOM ee.scopes = MAP FDOM pos_end.scopes` by
    fs[exprExtRequestHistoryTheory.extrequest_history_frame_def,
       exprExtRequestReadProbeTheory.extrequest_read_frame_def] >>
  `intcall_expr_cont fp ce env es sa s pos_end s2 pos_state` by
    (irule bodyIntCallJointCallCoreTheory.intcall_expr_cont_trans >> metis_tac[]) >>
  `intcall_expr_cont fp ce env es sa s kw_end s3 kw_state` by
    (irule bodyIntCallJointCallCoreTheory.intcall_expr_cont_trans >> metis_tac[]) >>
  `pos_end with gas_obs := [] = pos_end` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  `EVERY (extrequest_snapshot_cell_protected fp.jc_prot fp.jc_morig.vs_memory
      fp.jc_ctx fp.jc_func ce fp.jc_cx kw_end s3 kw_state) cells` by
    (fs[listTheory.EVERY_MEM] >> rpt strip_tac >>
     irule exprExtRequestSnapshotStoreInterfaceTheory.extrequest_snapshot_cell_protected_history >>
     qpat_assum `extrequest_history_frame _ _ pos_end _ _ kw_end _ _`
       (irule_at Any) >>
     fs[bodyIntCallJointContractTheory.intcall_expr_res_def] >> metis_tac[]) >>
  drule_all exprExtRequestTargetCpsTheory.extrequest_target_address >> strip_tac >>
  `is_word_type (expr_type a)` by simp[compileEnvTheory.is_word_type_def] >>
  `safe_operand s1 addr_op` by
    (drule_all exprSimSourceTheory.expr_body_pre_lower_value_word_shape >>
     simp[compileEnvTheory.is_word_type_def] >> strip_tac >>
     Cases_on `addr_op` >> fs[exprSafeOperandTheory.safe_operand_def]) >>
  `safe_operand s2 addr_op` by
    (irule exprSafeOperandTheory.safe_operand_mono >> qexists `s1` >>
     fs[exprLoweringPropsTheory.ci_mono_def]) >>
  `safe_operand s3 addr_op` by
    metis_tac[exprSafeOperandTheory.safe_operand_mono] >>
  `wb_frame ce ee pos_end s1 u pos_state` by
    metis_tac[bodyIntCallJointCallCoreTheory.intcall_expr_cont_frame] >>
  `eval_operand addr_op pos_state = SOME (w2w addr)` by
    (Cases_on `addr_op` >>
     gvs[exprSafeOperandTheory.safe_operand_def, venomStateTheory.eval_operand_def] >>
     metis_tac[exprSimWordArgsTheory.wb_frame_vars]) >>
  `eval_operand addr_op kw_state = SOME (w2w addr)` by
    (Cases_on `addr_op` >>
     gvs[exprSafeOperandTheory.safe_operand_def, venomStateTheory.eval_operand_def] >>
     metis_tac[exprSimWordArgsTheory.wb_frame_vars]) >>
  `wb_frame ce es kw_end sa s kw_state` by
    metis_tac[bodyIntCallJointCallCoreTheory.intcall_expr_cont_frame] >>
  qpat_x_assum `!target posvs kwvs esA esB tB ee t target_addr cells. _`
    (qspecl_then [`v`, `MAP (\(vv,ty,tv,v). v) cells`, `vs`,
      `ee`, `pos_end`, `pos_state`, `kw_end`, `kw_state`, `addr`, `cells`] mp_tac) >>
  simp[] >> disch_then irule >>
  conj_tac >- (qexists `used'` >> simp[]) >>
  conj_tac >- (qexists `used` >> gvs[]) >>
  simp[vyperValueTheory.dest_AddressV_def, byteTheory.word_of_bytes_be_def,
       byteTheory.word_of_bytes_word_to_bytes, dividesTheory.compute_divides,
       fcpLib.INDEX_CONV ``dimindex(:160)``]
QED
Finalise intcall_ext_operands_cps

(* The operand hypotheses carry the internal frame, rather than exprs_case's
   universally quantified contract.  Execute each child with the smaller
   producer hypothesis, then reuse the canonical suffix:

   ExtCall: extrequest_compile_call_split exposes target, snapshot args,
   kwargs, tuple prefix, call and return.  At each raw eval_expr landing,
   intcall_vv_post_intro recovers vv_post and intcall_expr_cont retains the
   resource frame.  The snapshot word/cell-intro, unread, joint-unwrap and
   kwarg-suffix lemmas handle the remaining operand work.  Existing layout,
   gas-selection and protected tuple-prefix lemmas feed extcall_request_ready;
   extcall_call_step and extcall_return_values_owned finish with the real
   protected set.  Send's two or three word operands use the forced-producer
   hypothesis; retain memory, allocation-map and frontier equality across the
   canonical CALL/ASSERT steps when composing send_tail_path.

   intcall_joint_res_frame and intcall_expr_cont_vv_post repackage the final
   certificate.  The global expression root and a copy of its pure induction
   would inherit unrelated aggregate/subscript admission tags. *)
Theorem intcall_extcall_step:
  (!e'. expr_size e' < expr_size e ==>
        intcall_expr_producer fp e' /\ intcall_forced_producer fp e' /\
        intcall_map_producer fp e') /\
  (?a tgt args dflt. e = Call a tgt args dflt /\ !nsid. tgt <> IntCall nsid) ==>
  intcall_expr_producer fp e /\ intcall_map_producer fp e
Proof
  cheat
QED

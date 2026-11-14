(* Seam 2 joint induction, a family leaf of the call step: every other call target (external calls and send; the rest are not supported_expr). *)
Theory bodyIntCallFamCallExt
Ancestors
  bodyIntCallJointContract bodyIntCallJointCallCore bodyIntCallJointPurePath
  bodyIntCallJointCallSource
  exprExtRequestHistory extcallProtFramePath exprSimSliceCompose
  exprExtRequestSnapshotHeadCps extcallProtFrameUnread
  exprLoweringProps fragExec exprSimMemorySource vyperInterpreter exprExtRequestGasBind
  exprLowering compileEnv exprExtRequestSnapshotPositionalCps vyperState stmtSimDeclGas
  exprExtRequestSnapshotLayout exprExtRequestGasSelections
  exprExtRequestSnapshotStorePrefix extcallProtFramePrefixCompose exprSimExtCallCase
  vyperCallOutcomeFrame bodyIntCallJointPureSlot exprSimSend sendSourceFrame
  venomExecSemantics venomInst venomState fragGasPath gasExemptCert
  loweringPosts loweringStateRelDefs localPtrsProps wordArgsPtr exprSimProps
  exprSimPrecompiles exprSimDefs exprSimOperands exprSimWordArgs
  exprExtRequestTupleCapturedHead

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
  (impl_tac >-
    (fs[ci_mono_def, vyperTypeSystemTheory.ext_call_kw_type_def,
        wordsTheory.dimword_def] >>
     rpt conj_tac >> metis_tac[])) >> strip_tac >>
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

Theorem intcall_ext_ready_suffix[local]:
  intcall_frame_ok fp /\
  expr_body_pre ce fp.jc_cx env
    (Call ann (ExtCall stat skip (fname,ats,rt) opts) (a::rest) NONE) es /\
  intcall_expr_res fp ce env es sa s0 /\
  intcall_expr_cont fp ce env es sa s0 ee s3 t /\
  wb_frame ce es ee sa s0 t /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= s3.cs_next_var /\ sa.cs_next_id <= s3.cs_next_id /\
  eval_operand addr_op t = SOME (w2w (target_addr : 160 word)) /\ safe_operand s3 addr_op /\
  MAP (\(vv,ty,tv,v). vv) cells = arg_vvs /\
  MAP (\(vv,ty,tv,v). ty) cells = MAP (lowered_value_type ce) (TAKE (LENGTH ats) rest) /\
  MAP (\(vv,ty,tv,v). v) cells = posvs /\
  EVERY (extrequest_snapshot_cell_protected fp.jc_prot fp.jc_morig.vs_memory
    fp.jc_ctx fp.jc_func ce fp.jc_cx ee s3 t) cells /\
  extrequest_kwargs_post fp.jc_ctx fp.jc_func ce fp.jc_cx rt opts (DROP (LENGTH ats) rest)
    esB s2 tB s3 value_opt gas_opt default_opt [] [] [] vs ee t /\
  (case gas_opt of SOME g => (g,s3) | NONE => emit_op GAS [] s3) = (gas_op,s4) /\
  (case default_opt of SOME (d,dty) => (T,d,dty) | NONE => (F,Lit 0w,rt)) =
    (has_default,default_op,default_ty) /\
  extrequest_compile_prefix ce arg_vvs
    (MAP (lowered_value_type ce) (TAKE (LENGTH ats) rest))
    (SUM (MAP (type_memory_bytes ce) (MAP (lowered_value_type ce) (TAKE (LENGTH ats) rest))))
    (abi_size_bound ce.ce_struct_fields
      (TupleT (MAP (lowered_value_type ce) (TAKE (LENGTH ats) rest))))
    (ce.ce_method_id fname ats)
    (abi_size_bound ce.ce_struct_fields (if needs_external_call_wrap rt then TupleT [rt] else rt))
    (type_to_abi_enc_info ce.ce_struct_fields ce
      (TupleT (MAP (lowered_value_type ce) (TAKE (LENGTH ats) rest)))) s4 = ((buf,off,len),sp) /\
  fn_has_code s3 s4 fp.jc_func /\ fn_has_code s4 sp fp.jc_func /\
  fn_inst_ids_distinct fp.jc_func ==>
  ?u calldata.
    gas_marked_path F fp.jc_ctx fp.jc_func t (if IS_NONE gas_opt then 1 else 0) (OK u) /\
    extrequest_history_frame ce fp.jc_cx ee s3 t ee sp u /\
    intcall_expr_cont fp ce env es sa s0 ee sp u /\
    LENGTH posvs = LENGTH ats /\ LENGTH vs = LENGTH opts /\ ext_call_opts_ok stat opts /\
    build_ext_calldata (get_tenv fp.jc_cx) fname ats posvs = SOME calldata /\
    extcall_request_ready fp.jc_ctx fp.jc_func ce fp.jc_cx rt es sa s0 fp.jc_prot sp stat
      addr_op (case value_opt of NONE => Lit 0w | SOME v => v) gas_op buf off len
      (abi_size_bound ce.ce_struct_fields (if needs_external_call_wrap rt then TupleT [rt] else rt))
      target_addr (if stat then NONE else case ext_call_kwarg EKValue opts vs of
        NONE => SOME 0 | SOME v => dest_NumV v)
      calldata has_default default_op default_ty (ext_call_kwarg EKDefault opts vs) ee u
Proof
  strip_tac >>
  `expr_sim_inv ce fp.jc_cx env ee` by
    fs[intcall_expr_cont_def, intcall_expr_res_def] >>
  `EVERY (extrequest_snapshot_cell fp.jc_ctx fp.jc_func ce fp.jc_cx ee s3 t) cells` by
    (fs[listTheory.EVERY_MEM] >>
     metis_tac[exprExtRequestSnapshotStoreInterfaceTheory.extrequest_snapshot_cell_protected_plain]) >>
  drule_all exprExtRequestSnapshotLayoutTheory.extrequest_snapshot_call_typed_cells >> strip_tac >>
  drule_all exprExtRequestSnapshotLayoutTheory.extrequest_snapshot_call_positional_calldata >> strip_tac >>
  drule_all exprExtRequestGasSelectionsTheory.extrequest_kwargs_gas_endpoint >> strip_tac >>
  suspend "prefix"
QED

Resume intcall_ext_ready_suffix[prefix]:
  rename1 `gas_marked_path F fp.jc_ctx fp.jc_func t _ (OK tg)` >>
  `EVERY (extrequest_snapshot_cell_protected fp.jc_prot fp.jc_morig.vs_memory
    fp.jc_ctx fp.jc_func ce fp.jc_cx ee s4 tg) cells` by
    (fs[listTheory.EVERY_MEM] >> rpt strip_tac >>
     irule exprExtRequestSnapshotStoreInterfaceTheory.extrequest_snapshot_cell_protected_history >>
     qpat_assum `extrequest_history_frame _ _ ee s3 t ee s4 tg` (irule_at Any) >>
     simp[] >> fs[exprExtRequestKwargsTheory.extrequest_kwargs_post_def]) >>
  `local_ptrs_reserved ce s4` by fs[extrequest_history_frame_def] >>
  `ee.gas_obs = []` by fs[exprExtRequestKwargsTheory.extrequest_kwargs_post_def] >>
  `!pa pk. fp.jc_prot pa pk ==> pa + pk <= tg.vs_alloca_next /\
    mem_bytes_at pa pk tg.vs_memory = mem_bytes_at pa pk fp.jc_morig.vs_memory /\
    !i b n. FLOOKUP tg.vs_allocas i = SOME (b,n) ==>
      loweringStateRelDefs$regions_disjoint pa pk b n` by
    (rpt gen_tac >> strip_tac >>
     `intcall_expr_res fp ce env ee s3 t` by fs[intcall_expr_cont_def] >>
     `window_alloca_growth t tg` by
       metis_tac[extcallProtFramePathTheory.gas_marked_path_window_alloca_growth] >>
     `allocas_above fp.jc_lo tg` by
       metis_tac[bodyIntCallJointPurePathTheory.gas_marked_path_allocas_above,
         intcall_expr_res_def] >>
     qpat_assum `intcall_frame_ok fp` mp_tac >>
     qpat_assum `allocas_above fp.jc_lo tg` mp_tac >>
     qpat_assum `intcall_expr_res fp ce env ee s3 t` mp_tac >>
     qpat_assum `tg.vs_memory = t.vs_memory` mp_tac >>
     qpat_assum `fp.jc_prot pa pk` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[intcall_frame_ok_def, intcall_expr_res_def,
       intCallFrameTheory.allocas_above_def, loweringStateRelDefsTheory.regions_disjoint_def] >>
     rpt strip_tac >> res_tac >> decide_tac) >>
  suspend "layout"
QED

Resume intcall_ext_ready_suffix[layout]:
  `SUM (MAP (type_memory_bytes ce)
    (MAP (lowered_value_type ce) (TAKE (LENGTH ats) rest))) < 2 ** 64 /\
   MAX (abi_size_bound ce.ce_struct_fields
    (TupleT (MAP (lowered_value_type ce) (TAKE (LENGTH ats) rest))))
    (abi_size_bound ce.ce_struct_fields (if needs_external_call_wrap rt then TupleT [rt] else rt)) + 32 < 2 ** 64` by
    (qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _`
       (strip_assume_tac o SRULE [exprSimHypsDefsTheory.expr_body_pre_def,
         allocLimitsTheory.alloc_limits_expr_def, allocLimitsTheory.ext_call_alloc_ok_def, LET_THM]) >>
     simp[]) >>
  `LENGTH arg_vvs = LENGTH (TAKE (LENGTH ats) rest)` by metis_tac[listTheory.LENGTH_MAP] >>
  `SUM (MAP (\(vv,ty,tv,v). type_memory_size tv) cells) = type_memory_size_list tvs` by
    (qpat_assum `type_memory_size (TupleTV tvs) = SUM _`
       (ACCEPT_TAC o SYM o REWRITE_RULE [valueEncodingTheory.type_memory_size_def])) >>
  `?u (w:bytes32).
    gas_marked_path F fp.jc_ctx fp.jc_func tg 0 (OK u) /\
    stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx ee u /\
    extrequest_history_frame ce fp.jc_cx ee s4 tg ee sp u /\
    ~u.vs_halted /\ u.vs_current_bb = sp.cs_current_bb /\
    u.vs_inst_idx = LENGTH sp.cs_current_insts /\
    eval_operand len u = SOME (n2w (4 + LENGTH (enc
      (vyper_to_abi_type (get_tenv fp.jc_cx) (TupleT
        (MAP (lowered_value_type ce) (TAKE (LENGTH ats) rest)))) av))) /\
    eval_operand off u = SOME (n2w (w2n w + 28)) /\
    read_memory (w2n w + 28) (4 + LENGTH (enc
      (vyper_to_abi_type (get_tenv fp.jc_cx) (TupleT
        (MAP (lowered_value_type ce) (TAKE (LENGTH ats) rest)))) av)) u =
      function_selector fname (vyper_to_abi_types (get_tenv fp.jc_cx) ats) ++
      enc (vyper_to_abi_type (get_tenv fp.jc_cx) (TupleT
        (MAP (lowered_value_type ce) (TAKE (LENGTH ats) rest)))) av /\
    FLOOKUP u.vs_allocas s4.cs_next_id = SOME (w2n w, MAX
      (abi_size_bound ce.ce_struct_fields (TupleT
        (MAP (lowered_value_type ce) (TAKE (LENGTH ats) rest))))
      (abi_size_bound ce.ce_struct_fields
        (if needs_external_call_wrap rt then TupleT [rt] else rt)) + 32) /\
    w2n w + abi_size_bound ce.ce_struct_fields
      (if needs_external_call_wrap rt then TupleT [rt] else rt) < dimword (:256) /\
    local_ptrs_reserved ce sp /\ safe_operand sp len /\ safe_operand sp off /\
    eval_operand buf u = SOME w /\ safe_operand sp buf /\
    (!pa pk. fp.jc_prot pa pk ==> pa + pk <= u.vs_alloca_next /\
      mem_bytes_at pa pk u.vs_memory = mem_bytes_at pa pk fp.jc_morig.vs_memory /\
      !i b n. FLOOKUP u.vs_allocas i = SOME (b,n) ==>
        loweringStateRelDefs$regions_disjoint pa pk b n)` by
   (Cases_on `arg_vvs = []`
  >- suspend "empty_prefix" >>
  `ats <> [] /\ rest <> []` by
    (Cases_on `ats` >> Cases_on `rest` >> fs[]) >>
  `assignable_type (get_tenv fp.jc_cx)
    (TupleT (MAP (lowered_value_type ce) (TAKE (LENGTH ats) rest)))` by
    (first_x_assum irule >> simp[]) >>
  drule_at (Pat `extrequest_compile_prefix _ _ _ _ _ _ _ _ _ = _`)
    (Q.INST [`vs` |-> `posvs`, `M` |-> `fp.jc_morig.vs_memory`]
      exprExtRequestSnapshotStorePrefixTheory.extrequest_snapshot_tuple_prefix_protected) >>
  disch_then (drule_at (Pat `EVERY _ cells`)) >>
  disch_then (mp_tac o SPEC_ALL) >>
  (impl_tac >- (simp[valueEncodingTheory.type_memory_size_def] >>
    fs[wordsTheory.dimword_def] >> rpt strip_tac >> metis_tac[])) >>
  strip_tac >>
  rename1 `gas_marked_path F fp.jc_ctx fp.jc_func tg 0 (OK up)` >>
  qexistsl_tac [`up`, `w`] >> simp[] >>
  rpt strip_tac >>
  qpat_x_assum `!pa pk. fp.jc_prot pa pk ==> _` drule >>
  simp[] >> metis_tac[]) >> suspend "ready"
QED

Resume intcall_ext_ready_suffix[empty_prefix]:
  `ats = []` by
    (drule exprExtRequestShapeTheory.extrequest_body_typed >>
     simp[Once vyperTypeSystemTheory.well_typed_expr_def] >> strip_tac >>
     fs[listTheory.LENGTH_TAKE_EQ, listTheory.LENGTH_NIL]) >>
  fs[valueEncodingTheory.type_memory_size_def] >>
  drule_at (Pat `extrequest_compile_prefix _ _ _ _ _ _ _ _ _ = _`)
    extcallProtFramePrefixComposeTheory.extcall_protframe_empty_prefix_endpoint >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ tg`)) >>
  disch_then (mp_tac o Q.INST [`original` |-> `fp.jc_morig.vs_memory`,
    `prot` |-> `fp.jc_prot`] o SPEC_ALL) >>
  (impl_tac >- (simp[] >> fs[wordsTheory.dimword_def] >>
    rpt strip_tac >> metis_tac[])) >>
  strip_tac >> gvs[vyperABITheory.vyper_to_abi_def] >>
  rename1 `gas_marked_path F fp.jc_ctx fp.jc_func tg 0 (OK up)` >>
  qexistsl_tac [`up`, `w`] >>
  simp[contractABITheory.enc_def, listTheory.REV_DEF, wordsTheory.dimword_def] >>
  rpt strip_tac >>
  qpat_x_assum `!pa pk. fp.jc_prot pa pk ==> _` drule >>
  simp[] >> metis_tac[]
QED

Resume intcall_ext_ready_suffix[ready]:
  `extrequest_history_frame ce fp.jc_cx ee s3 t ee sp u` by
    (irule exprExtRequestHistoryComposeTheory.extrequest_history_frame_trans >>
     conj_tac >- (qexistsl_tac [`fp.jc_ctx`, `fp.jc_func`] >>
       fs[exprExtRequestKwargsTheory.extrequest_kwargs_post_def]) >>
     qexistsl_tac [`ee`, `s4`, `tg`] >> simp[]) >>
  `gas_marked_path F fp.jc_ctx fp.jc_func t (if IS_NONE gas_opt then 1 else 0) (OK u)` by
    (qpat_assum `gas_marked_path F _ _ t _ (OK tg)` mp_tac >>
     qpat_assum `gas_marked_path F _ _ tg 0 (OK u)` mp_tac >>
     metis_tac[fragGasModeTheory.gas_marked_path_then, arithmeticTheory.ADD_0]) >>
  suspend "ready_resources"
QED
Resume intcall_ext_ready_suffix[ready_resources]:
  `intcall_expr_res fp ce env ee s3 t` by fs[intcall_expr_cont_def] >>
  `intcall_expr_cont fp ce env ee s3 t ee sp u` by
    (irule intcall_ext_history_cont >> simp[] >>
     reverse conj_tac
     >- (qexists_tac `if IS_NONE gas_opt then 1 else 0` >> simp[]) >>
     fs[intcall_expr_res_def]) >>
  `intcall_expr_cont fp ce env es sa s0 ee sp u` by
    (irule bodyIntCallJointCallCoreTheory.intcall_expr_cont_trans >>
     simp[] >> qexistsl_tac [`s3`, `ee`, `t`] >> simp[]) >>
  `LENGTH posvs = LENGTH ats` by
    (drule exprExtRequestShapeTheory.extrequest_body_typed >>
     simp[Once vyperTypeSystemTheory.well_typed_expr_def] >>
     strip_tac >> gvs[listTheory.LENGTH_MAP, listTheory.LENGTH_TAKE_EQ]) >>
  `LENGTH vs = LENGTH opts` by
    fs[exprExtRequestKwargsTheory.extrequest_kwargs_post_def] >>
  `ext_call_opts_ok stat opts` by
    (drule exprExtRequestShapeTheory.extrequest_body_typed >>
     simp[Once vyperTypeSystemTheory.well_typed_expr_def]) >>
  qexists_tac `u` >> goal_assum (drule_at Any) >> simp[] >>
  suspend "ready_contract"
QED
Resume intcall_ext_ready_suffix[ready_contract]:
  `wb_frame ce es ee sa s0 u` by
    (irule exprSimWordArgsTheory.wb_frame_trans >>
     simp[] >> conj_tac
     >- fs[intcall_expr_res_def] >>
     conj_tac >- (qexistsl [`fp.jc_ctx`, `fp.jc_cx`, `fp.jc_func`] >>
       fs[intcall_expr_res_def]) >>
     qexistsl [`ee`, `s3`, `t`] >> simp[] >>
     irule exprExtRequestPrefixTheory.extrequest_history_writeback >>
     qexistsl [`fp.jc_cx`, `sp`] >> simp[]) >>
  `extrequest_kwarg_selection ce fp.jc_cx rt EKDefault
    (ext_call_kwarg EKDefault opts vs) default_opt ee sp u` by
    (irule exprExtRequestKwargsTheory.extrequest_kwarg_selection_transport >>
     qexistsl [`fp.jc_ctx`, `ee`, `fp.jc_func`, `s4`, `tg`] >> simp[]) >>
  `extrequest_kwarg_selection ce fp.jc_cx rt EKValue
    (ext_call_kwarg EKValue opts vs) (OPTION_MAP (\op. (op,rt)) value_opt) ee sp u` by
    (irule exprExtRequestKwargsTheory.extrequest_kwarg_selection_transport >>
     qexistsl [`fp.jc_ctx`, `ee`, `fp.jc_func`, `s4`, `tg`] >> simp[]) >>
  `eval_operand addr_op u = SOME (w2w target_addr)` by
    (irule exprExtRequestReconstructTheory.extrequest_history_operand >>
     qexistsl [`ce`, `fp.jc_cx`, `ee`, `ee`, `s3`, `sp`, `t`] >> simp[]) >>
  `eval_operand gas_op u = SOME gw` by
    (irule exprExtRequestReconstructTheory.extrequest_history_operand >>
     qexistsl [`ce`, `fp.jc_cx`, `ee`, `ee`, `s4`, `sp`, `tg`] >> simp[]) >>
  suspend "ready_default"
QED
Resume intcall_ext_ready_suffix[ready_default]:
  `extcall_default_ready fp.jc_cx rt has_default default_op default_ty
    (ext_call_kwarg EKDefault opts vs) u` by
    (`IS_SOME default_opt ==> rt <> NoneT` by
       (strip_tac >> Cases_on `rt = NoneT` >> simp[] >>
        `~MEM EKDefault opts` by
          (drule exprExtRequestShapeTheory.extrequest_body_typed >>
           simp[Once vyperTypeSystemTheory.well_typed_expr_def]) >>
        `ext_call_kwarg EKDefault opts vs = NONE` by
          metis_tac[vyperTypeExtCallSoundnessTheory.ext_call_kwarg_not_mem] >>
        gvs[exprExtRequestKwargsTheory.extrequest_kwarg_selection_def]) >>
     qpat_assum `IS_SOME default_opt ==> _` mp_tac >>
     qpat_assum `extrequest_kwarg_selection _ _ _ EKDefault _ _ _ sp u` mp_tac >>
     qpat_assum `_ = (has_default,default_op,default_ty)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     Cases_on `default_opt` >>
     fs[extcall_default_ready_def,
        exprExtRequestKwargsTheory.extrequest_kwarg_selection_def] >>
     PairCases_on `x` >> gvs[] >>
     `rt <> NoneT` by fs[] >>
     conj_tac >- (Cases_on `ext_call_kwarg EKDefault opts vs` >> simp[] >> fs[]) >>
     rpt strip_tac >>
     fs[exprExtRequestRetainedTheory.extrequest_retained_value_def] >>
     `?w. eval_operand default_op u = SOME w` by
       (qpat_assum `expr_val_rel _ _ _ default_op u` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp[loweringPostsTheory.expr_val_rel_def] >> metis_tac[]) >>
     metis_tac[]) >>
  suspend "ready_geometry"
QED
Resume intcall_ext_ready_suffix[ready_geometry]:
  `ci_mono s4 sp` by
    (drule exprExtRequestPrefixTheory.extrequest_prefix_split >> strip_tac >>
     Cases_on `arg_vvs = []`
     >- (fs[] >>
         `ci_mono s4 sm` by
           metis_tac[exprLoweringPropsTheory.ci_mono_compile_alloc_buffer, pairTheory.SND] >>
         `ci_mono sm sn` by
           metis_tac[exprLoweringPropsTheory.ci_mono_emit_void, pairTheory.SND] >>
         `ci_mono sn sp` by
           metis_tac[exprLoweringPropsTheory.ci_mono_emit_op, pairTheory.SND] >>
         fs[exprLoweringPropsTheory.ci_mono_def] >>
         metis_tac[compileEnvTheory.cs_extends_trans]) >>
     fs[] >> drule_all exprExtRequestPrefixTheory.extrequest_tuple_prefix_code >>
     strip_tac >> fs[exprLoweringPropsTheory.ci_mono_def] >>
     metis_tac[compileEnvTheory.cs_extends_trans]) >>
  suspend "ready_alloc_code"
QED
Resume intcall_ext_ready_suffix[ready_alloc_code]:
  `?inst p. MEM inst (fn_insts fp.jc_func) /\
      inst.inst_id = s4.cs_next_id /\ inst.inst_opcode = ALLOCA /\
      inst.inst_outputs = [p] /\
      not_local_ptr ce ee.scopes p /\ s4.cs_next_id < sp.cs_next_id` by
    (drule exprExtRequestPrefixTheory.extrequest_prefix_split >> strip_tac >>
     (`fn_has_code s4 sm fp.jc_func /\ ci_mono s4 sm /\ ci_mono sm sp` by
       (Cases_on `arg_vvs = []`
        >- (fs[] >>
            `ci_mono s4 sm` by
              metis_tac[exprLoweringPropsTheory.ci_mono_compile_alloc_buffer, pairTheory.SND] >>
            `ci_mono sm sn` by
              metis_tac[exprLoweringPropsTheory.ci_mono_emit_void, pairTheory.SND] >>
            `ci_mono sn sp` by
              metis_tac[exprLoweringPropsTheory.ci_mono_emit_op, pairTheory.SND] >>
            fs[exprLoweringPropsTheory.ci_mono_def] >>
            metis_tac[fragExecTheory.fn_has_code_split, compileEnvTheory.cs_extends_trans]) >>
        fs[] >>
        drule_all exprExtRequestPrefixTheory.extrequest_tuple_prefix_code >>
        strip_tac >> fs[exprLoweringPropsTheory.ci_mono_def] >>
        metis_tac[compileEnvTheory.cs_extends_trans])) >>
     qpat_assum `compile_alloc_buffer _ s4 = _`
       (mp_then Any mp_tac exprSimAllocTheory.buffer_alloc_code) >>
     disch_then drule >> strip_tac >>
     qpat_assum `compile_alloc_buffer _ s4 = _`
       (strip_assume_tac o MATCH_MP loweringHaltTheory.compile_alloc_buffer_parts) >>
     `not_local_ptr ce ee.scopes (STRING #"%" (toString s4.cs_next_var))` by
       (irule exprSimOperandsTheory.fresh_not_local_ptr >>
        qexists_tac `s4` >> simp[]) >>
     qmatch_asmsub_abbrev_tac `MEM alloc_inst (fn_insts fp.jc_func)` >>
     qexistsl [`alloc_inst`, `STRING #"%" (toString s4.cs_next_var)`] >>
     simp[Abbr `alloc_inst`, venomInstTheory.mk_inst_def] >>
     fs[exprLoweringPropsTheory.ci_mono_def] >> decide_tac) >>
  suspend "ready_separation"
QED
Resume intcall_ext_ready_suffix[ready_separation]:
  `!name b sz. local_region ce ee.scopes u name b sz ==>
      loweringStateRelDefs$regions_disjoint (w2n w)
        (abi_size_bound ce.ce_struct_fields
          (if needs_external_call_wrap rt then TupleT [rt] else rt)) b sz` by
    (rpt strip_tac >>
     `alloca_inv u /\ local_ptrs_rel fp.jc_func ce ee.scopes u` by
       (qpat_assum `stmt_state_rel _ _ _ _ ee u` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp[stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def]) >>
     qpat_assum `inst.inst_id = s4.cs_next_id`
       (fn th => rule_assum_tac (ONCE_REWRITE_RULE [GSYM th])) >>
     drule_all localPtrsPropsTheory.local_ptrs_rel_alloca_disjoint >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[arithmeticTheory.MAX_DEF] >> decide_tac) >>
  `!name b sz. local_region ce es.scopes s0 name b sz ==>
      loweringStateRelDefs$regions_disjoint (w2n w)
        (abi_size_bound ce.ce_struct_fields
          (if needs_external_call_wrap rt then TupleT [rt] else rt)) b sz` by
    (`stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s0 /\
       local_ptrs_reserved ce sa` by fs[intcall_expr_res_def] >>
     drule_all wordArgsPtrTheory.wb_frame_local_regions >> strip_tac >>
     metis_tac[]) >>
  `!aid b sz. aid <> s4.cs_next_id /\
      FLOOKUP u.vs_allocas aid = SOME (b,sz) ==>
      loweringStateRelDefs$regions_disjoint (w2n w)
        (abi_size_bound ce.ce_struct_fields
          (if needs_external_call_wrap rt then TupleT [rt] else rt)) b sz` by
    (`allocas_non_overlapping u` by
       (qpat_assum `stmt_state_rel _ _ _ _ ee u` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp[stmt_state_rel_def, venomMemDefsTheory.alloca_inv_def]) >>
     qpat_assum `FLOOKUP u.vs_allocas s4.cs_next_id = SOME _` mp_tac >>
     qpat_assum `allocas_non_overlapping u` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[venomMemDefsTheory.allocas_non_overlapping_def] >> rpt strip_tac >>
     first_x_assum drule >> disch_then drule >> simp[] >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def, arithmeticTheory.MAX_DEF] >>
     decide_tac) >>
  `!aid b sz. aid < sa.cs_next_id /\
      FLOOKUP u.vs_allocas aid = SOME (b,sz) ==>
      loweringStateRelDefs$regions_disjoint (w2n w)
        (abi_size_bound ce.ce_struct_fields
          (if needs_external_call_wrap rt then TupleT [rt] else rt)) b sz` by
    (rpt strip_tac >> first_x_assum irule >> qexists_tac `aid` >> simp[] >>
     fs[exprLoweringPropsTheory.ci_mono_def] >> decide_tac) >>
  `ce.ce_is_ctor ==> !name tv v off.
      FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
      FLOOKUP (case ALOOKUP ee.immutables fp.jc_cx.txn.target of
        NONE => FEMPTY | SOME imms => get_source_immutables ce.ce_module imms)
        name = SOME (tv,v) ==>
      loweringStateRelDefs$regions_disjoint (w2n w)
        (abi_size_bound ce.ce_struct_fields
          (if needs_external_call_wrap rt then TupleT [rt] else rt))
        off (type_memory_size tv)` by
    (`immutable_alloca_sep fp.jc_func ce fp.jc_cx ee u` by
       (qpat_assum `stmt_state_rel _ _ _ _ ee u` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp[stmt_state_rel_def]) >>
     rpt strip_tac >>
     qpat_x_assum `immutable_alloca_sep _ _ _ _ _` mp_tac >>
     simp[immutable_alloca_sep_def] >>
     disch_then (drule o CONJUNCT2) >> disch_then drule >> strip_tac >>
     qpat_x_assum `!inst b sz. _` (qspec_then `inst` mp_tac) >>
     simp[] >> simp[loweringStateRelDefsTheory.regions_disjoint_def] >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[arithmeticTheory.MAX_DEF] >> decide_tac) >>
  suspend "ready_default_separation"
QED
Resume intcall_ext_ready_suffix[ready_default_separation]:
  `!d dw tv. ext_call_kwarg EKDefault opts vs = SOME d /\
      ~is_word_type default_ty /\ eval_operand default_op u = SOME dw /\
      evaluate_type (get_tenv fp.jc_cx) default_ty = SOME tv ==>
      loweringStateRelDefs$regions_disjoint (w2n w)
        (abi_size_bound ce.ce_struct_fields
          (if needs_external_call_wrap rt then TupleT [rt] else rt))
        (w2n dw) (val_footprint tv d)` by
    (qpat_assum `extrequest_kwarg_selection _ _ _ EKDefault _ _ _ s4 tg` mp_tac >>
     qpat_assum `_ = (has_default,default_op,default_ty)` mp_tac >>
     qpat_assum `extrequest_history_frame _ _ _ s4 tg _ sp u` mp_tac >>
     qpat_assum `!aid b sz. aid <> s4.cs_next_id /\ _ ==> _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     Cases_on `default_opt` >>
     fs[exprExtRequestKwargsTheory.extrequest_kwarg_selection_def] >>
     PairCases_on `x` >> gvs[] >> rpt strip_tac >>
     fs[exprExtRequestRetainedTheory.extrequest_retained_value_def] >>
     `eval_operand default_op u = SOME w'` by
       (drule_all exprExtRequestReconstructTheory.extrequest_history_operand >> simp[]) >>
     `dw = w'` by gvs[] >> fs[] >>
     fs[exprExtRequestHistoryTheory.extrequest_history_frame_def] >>
     `FLOOKUP u.vs_allocas aid = SOME (w2n w',size')` by metis_tac[] >>
     `loweringStateRelDefs$regions_disjoint (w2n w)
        (abi_size_bound ce.ce_struct_fields
          (if needs_external_call_wrap rt then TupleT [rt] else rt))
        (w2n w') size'` by
       (first_x_assum irule >> qexists_tac `aid` >> simp[]) >>
     fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  suspend "ready_safety"
QED
Resume intcall_ext_ready_suffix[ready_safety]:
  `outcomes_accounts_typed ee.outcomes /\ accounts_runtime_well_typed ee.accounts` by
    (qpat_assum `expr_sim_inv ce fp.jc_cx env ee` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[exprSimHypsDefsTheory.expr_sim_inv_def,
       vyperTypeExtCallCoreTheory.accounts_runtime_well_typed_accounts_well_typed]) >>
  `sa.cs_next_var <= sp.cs_next_var /\ sa.cs_next_id <= sp.cs_next_id` by
    (fs[exprLoweringPropsTheory.ci_mono_def] >> decide_tac) >>
  `safe_operand sp addr_op /\ safe_operand sp gas_op` by
    (conj_tac
     >- (irule exprSafeOperandTheory.safe_operand_mono >> qexists_tac `s3` >> simp[] >>
         fs[exprLoweringPropsTheory.ci_mono_def] >> decide_tac) >>
     irule exprSafeOperandTheory.safe_operand_mono >> qexists_tac `s4` >> simp[] >>
     fs[exprLoweringPropsTheory.ci_mono_def]) >>
  `safe_operand sp default_op` by
    (qpat_assum `extrequest_kwarg_selection _ _ _ EKDefault _ _ _ sp u` mp_tac >>
     qpat_assum `_ = (has_default,default_op,default_ty)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     Cases_on `default_opt` >>
     fs[exprExtRequestKwargsTheory.extrequest_kwarg_selection_def, exprSafeOperandTheory.safe_operand_def] >>
     PairCases_on `x` >> gvs[] >>
     Cases_on `ext_call_kwarg EKDefault opts vs` >> gvs[] >>
     fs[exprExtRequestRetainedTheory.extrequest_retained_value_def, exprSafeOperandTheory.safe_operand_def]) >>
  `w2n w + MAX
      (abi_size_bound ce.ce_struct_fields
        (TupleT (MAP (lowered_value_type ce) (TAKE (LENGTH ats) rest))))
      (abi_size_bound ce.ce_struct_fields
        (if needs_external_call_wrap rt then TupleT [rt] else rt)) + 32
      <= u.vs_alloca_next` by
    (qpat_assum `stmt_state_rel _ _ _ _ ee u` mp_tac >>
     qpat_assum `FLOOKUP u.vs_allocas s4.cs_next_id = SOME _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     fs[stmt_state_rel_def, venomMemDefsTheory.alloca_inv_def,
        venomMemDefsTheory.alloca_next_valid_def] >> metis_tac[]) >>
  `u.vs_alloca_next < dimword (:256)` by
    (qpat_assum `stmt_state_rel _ _ _ _ ee u` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def,
       exprLoweringPropsTheory.alloca_room_def] >>
     strip_tac >> decide_tac) >>
  `safe_operand sp (case value_opt of NONE => Lit 0w | SOME v => v)` by
    (qpat_assum `extrequest_kwarg_selection _ _ _ EKValue _ _ _ sp u` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `value_opt` >>
     simp[exprExtRequestKwargsTheory.extrequest_kwarg_selection_def, exprSafeOperandTheory.safe_operand_def] >>
     strip_tac >> Cases_on `ext_call_kwarg EKValue opts vs` >> gvs[] >>
     fs[exprExtRequestRetainedTheory.extrequest_retained_value_def, exprSafeOperandTheory.safe_operand_def]) >>
  suspend "ready_pack"
QED
Resume intcall_ext_ready_suffix[ready_pack]:
  simp[extcall_request_ready_def, wordsTheory.w2w_w2w] >>
  conj_tac >-
    (simp[wordsTheory.WORD_BITS_EXTRACT] >>
     irule wordsTheory.WORD_EXTRACT_ID >>
     mp_tac (Q.ISPEC `target_addr : 160 word` wordsTheory.w2n_lt) >>
     simp[wordsTheory.dimword_def,
       fcpLib.INDEX_CONV ``dimindex(:160)``]) >>
  conj_tac >-
    (irule exprExtRequestValueTheory.extrequest_value_static >>
     goal_assum (drule_at Any)) >>
  conj_tac >-
    (qpat_assum `extrequest_kwarg_selection _ _ _ EKValue _ _ _ sp u` mp_tac >>
     qpat_assum `ext_call_opts_ok stat opts` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     metis_tac[exprExtRequestValueTheory.extrequest_value_operand]) >>
  suspend "ready_pack_memory"
QED
Resume intcall_ext_ready_suffix[ready_pack_memory]:
  `!n a b p q D:num.
    n <= a /\ p + MAX a b + 32 <= q /\ q < D ==>
    n + 4 < D /\ p + b < D` by
    (POP_ASSUM_LIST (K ALL_TAC) >> rpt gen_tac >>
     Cases_on `a <= b` >> simp[arithmeticTheory.MAX_DEF] >> decide_tac) >>
  `LENGTH (enc (vyper_to_abi_type (get_tenv fp.jc_cx)
    (TupleT (MAP (lowered_value_type ce) (TAKE (LENGTH ats) rest)))) av) + 4
    < dimword (:256)` by
    (qpat_assum `!n a b p q D:num. _` mp_tac >>
     qpat_assum `LENGTH (enc _ av) <= _` mp_tac >>
     qpat_assum `w2n w + MAX _ _ + 32 <= _` mp_tac >>
     qpat_assum `u.vs_alloca_next < dimword (:256)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> metis_tac[]) >>
  conj_tac >-
    (qpat_assum `read_memory (w2n w + 28) _ u = _` mp_tac >>
     qpat_assum `LENGTH (enc _ av) + 4 < dimword (:256)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     pure_rewrite_tac [cj 2 vyperABITheory.vyper_to_abi_type_def] >>
     simp[wordsTheory.dimword_def] >>
     CONV_TAC (DEPTH_CONV numLib.REDUCE_CONV) >> rpt strip_tac >>
     fs[arithmeticTheory.MOD_LESS, arithmeticTheory.ADD_COMM]) >>
  conj_tac >-
    (conj_tac >-
      (qexistsl [`s4.cs_next_id`, `MAX
        (abi_size_bound ce.ce_struct_fields
          (TupleT (MAP (lowered_value_type ce) (TAKE (LENGTH ats) rest))))
        (abi_size_bound ce.ce_struct_fields
          (if needs_external_call_wrap rt then TupleT [rt] else rt)) + 32`] >>
       simp[] >> fs[ci_mono_def] >>
       POP_ASSUM_LIST (K ALL_TAC) >>
       `!a b:num. b <= MAX a b + 32` by
         (rpt gen_tac >> Cases_on `a <= b` >>
          simp[arithmeticTheory.MAX_DEF] >> decide_tac) >> metis_tac[]) >>
     rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  rpt strip_tac >>
  fs[intcall_expr_res_def, intcall_expr_cont_def] >> metis_tac[]
QED
Finalise intcall_ext_ready_suffix

Theorem intcall_extcall_expr_step[local]:
  (!e'. expr_size e' < expr_size (Call a (ExtCall static skip sig opts) args NONE) ==>
    intcall_expr_producer fp e' /\ intcall_forced_producer fp e' /\
    intcall_map_producer fp e') ==>
  intcall_expr_producer fp (Call a (ExtCall static skip sig opts) args NONE)
Proof
  PairCases_on `sig` >>
  strip_tac >> pure_rewrite_tac[intcall_expr_producer_def] >> rpt strip_tac >>
  rename1 `ExtCall stat skip (fname,ats,rt) opts` >>
  `args <> []` by
    (fs[exprSimHypsDefsTheory.expr_body_pre_def] >>
     metis_tac[exprExtRequestShapeTheory.extrequest_typed_nonempty]) >>
  Cases_on `args` >> fs[] >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  rewrite_tac[exprExtRequestShapeTheory.extrequest_compile_expr_extcall] >> strip_tac >>
  drule exprExtRequestShapeTheory.extrequest_compile_call_split >> strip_tac >>
  qpat_x_assum `let call_types = _ in _` mp_tac >>
  simp[NoAsms, LET_THM] >> pairarg_tac >> simp[] >> strip_tac >>
  `ci_mono sa s1` by
    metis_tac[cj 2 stmtLoweringMonoTheory.ci_mono_compile_expr_sa, pairTheory.SND] >>
  `ci_mono s1 s2` by
    (qpat_assum `compile_ext_call_args _ _ _ _ _ _ = _` mp_tac >>
     mp_tac (Q.SPECL [`TAKE (LENGTH (ats:type list)) t`,
       `MAP (lowered_value_type ce) (TAKE (LENGTH (ats:type list)) t)`,
       `compile_expr`, `ce`, `DROP (LENGTH (ats:type list)) t`, `s1`]
       ci_mono_compile_ext_call_args) >>
     simp[cj 1 compile_expr_ci_mono] >> metis_tac[pairTheory.SND]) >>
  `ci_mono s2 s3` by
    metis_tac[exprExtRequestKwargsTheory.extrequest_kwargs_mono, pairTheory.SND] >>
  `ci_mono s3 s4` by
    (Cases_on `gas_opt` >- (gvs[] >> metis_tac[ci_mono_emit_op, pairTheory.SND]) >>
     gvs[ci_mono_refl]) >>
  `ci_mono s4 sb` by
    metis_tac[exprExtRequestCodeTheory.extrequest_external_mono, pairTheory.SND] >>
  `fn_has_code sa s1 fp.jc_func /\ fn_has_code s1 s2 fp.jc_func /\
   fn_has_code s2 s3 fp.jc_func /\ fn_has_code s3 s4 fp.jc_func /\
   fn_has_code s4 sb fp.jc_func` by
    (fs[ci_mono_def] >>
     `cs_extends s3 sb` by metis_tac[cs_extends_trans] >>
     `cs_extends s2 sb` by metis_tac[cs_extends_trans] >>
     `cs_extends s1 sb` by metis_tac[cs_extends_trans] >>
     `fn_has_code sa s1 fp.jc_func /\ fn_has_code s1 sb fp.jc_func` by
       metis_tac[fragExecTheory.fn_has_code_split] >>
     `fn_has_code s1 s2 fp.jc_func /\ fn_has_code s2 sb fp.jc_func` by
       metis_tac[fragExecTheory.fn_has_code_split] >>
     `fn_has_code s2 s3 fp.jc_func /\ fn_has_code s3 sb fp.jc_func` by
       metis_tac[fragExecTheory.fn_has_code_split] >>
     metis_tac[fragExecTheory.fn_has_code_split]) >>
  fs[exprExtRequestStagesSourceTheory.extrequest_source_stages] >>
  irule (BETA_RULE (Q.INST [`kont` |->
    `\target posvs kwargs. eval_ext_call fp.jc_cx stat skip (fname,ats,rt) opts
      (target::(posvs ++ kwargs))`] intcall_ext_operands_cps)) >>
  first_assum (irule_at (Pat `lower_value _ _ _ _ _ = _`)) >>
  first_assum (irule_at (Pat `compile_ext_call_args _ _ _ _ _ _ = _`)) >>
  first_assum (irule_at (Pat `compile_ext_call_kwargs _ _ _ _ _ _ = _`)) >>
  qexistsl [`env`, `a`] >>
  simp[vyperASTTheory.expr_size_def] >>
  rpt gen_tac >> strip_tac >>
  drule_all exprExtRequestShapeTheory.extrequest_compile_kwargs_code >> strip_tac >>
  `MAP (\(vv,ty,tv,v). v) cells = MAP (\(vv,ty,tv,v). v) cells` by simp[] >>
  drule_all intcall_ext_ready_suffix >> strip_tac >>
  qmatch_goalsub_abbrev_tac `gas_outcome _ _ _ source _ post _` >>
  `?marks. gas_summary_at F (fp.jc_ctx,fp.jc_func) marks source (ee,u') post
    (\r ef z. expr_exit r z)` suffices_by
    (strip_tac >> rewrite_tac[gasOutcomeTheory.gas_outcome_def] >>
     qexists `REPLICATE (if IS_NONE gas_opt then 1 else 0) F ++ marks` >>
     disj1_tac >> irule bodyIntCallPackagePrefixTheory.gas_summary_at_path_prefix >>
     qexists `u'` >> gvs[fragGasModeTheory.gas_marked_path_def]) >>
  qabbrev_tac `retpost = \(res : eval_result + vyperState$exception) ef z. ?tv. res = INL tv /\
    vv_own ce fp.jc_cx
      (expr_type (Call a (ExtCall stat skip (fname,ats,rt) opts) (h::t) NONE))
      sa sb ef tv vv z /\
    vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx
      (Call a (ExtCall stat skip (fname,ats,rt) opts) (h::t) NONE)
      es sa sb s ef tv vv z /\
    z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!pa pk. fp.jc_prot pa pk ==>
      mem_bytes_at pa pk z.vs_memory = mem_bytes_at pa pk s.vs_memory)` >>
  `?marks. gas_summary_at F (fp.jc_ctx,fp.jc_func) marks source (ee,u') retpost
    (\r ef z. expr_exit r z)` suffices_by
    (strip_tac >> qexists `marks` >>
     qpat_x_assum `gas_summary_at _ _ _ _ _ retpost _` mp_tac >>
     rewrite_tac[gasSummaryTheory.gas_summary_at_def] >> strip_tac >>
     qexistsl [`res`, `es_end`, `r`] >> simp[] >>
     disj1_tac >>
     `gas_marked_path F fp.jc_ctx fp.jc_func u' (LENGTH marks) (OK t'')` by
       fs[gasSummaryTheory.gas_marked_exec_def] >>
     `allocas_above fp.jc_lo t''` by
       (irule gas_marked_path_allocas_above >>
        goal_assum (drule_at Any) >>
        fs[intcall_expr_cont_def, intcall_expr_res_def]) >>
     `u'.vs_alloca_next <= t''.vs_alloca_next` by
       metis_tac[gas_marked_path_alloca_next_mono] >>
     gvs[Abbr `retpost`] >>
     rename1 `vv_post _ _ _ _ _ es sa sb s _ result _ endpoint` >>
     `?kwused. !tail. eval_exprs fp.jc_cx (DROP (LENGTH ats) t)
       (esB with gas_obs := kwused ++ tail) =
       (INL kwvs,ee with gas_obs := tail)` by
       (fs[exprExtRequestKwargsTheory.extrequest_kwargs_post_def] >> metis_tac[]) >>
     `?obs. eval_expr fp.jc_cx
       (Call a (ExtCall stat skip (fname,ats,rt) opts) (h::t) NONE)
       (es with gas_obs := obs) = (INL result,es_end with gas_obs := [])` by
       (qexists `used ++ used' ++ kwused ++ gas_explicit marks u'.vs_gas_readings` >>
        qpat_assum `!tail. bind _ _ _ = _` mp_tac >>
        qpat_assum `!tail. eval_exprs _ (TAKE _ _) _ = _` mp_tac >>
        qpat_assum `!tail. eval_exprs _ (DROP _ _) (esB with gas_obs := kwused ++ tail) = _` mp_tac >>
        qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
        qpat_assum `Abbrev (source = _)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp[markerTheory.Abbrev_def, gasSummaryTheory.gas_marked_exec_def] >>
        rpt strip_tac >>
        pure_rewrite_tac[exprExtRequestStagesSourceTheory.extrequest_source_stages] >>
        CONV_TAC (LHS_CONV (REWR_CONV vyperStateTheory.bind_def)) >>
        pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >>
        pure_asm_rewrite_tac[] >> simp[] >>
        CONV_TAC (LHS_CONV (REWR_CONV vyperStateTheory.bind_def)) >>
        pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >>
        pure_asm_rewrite_tac[] >> simp[] >>
        CONV_TAC (LHS_CONV (REWR_CONV vyperStateTheory.bind_def)) >>
        pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >>
        pure_asm_rewrite_tac[] >> simp[] >>
        qpat_x_assum `!tail. eval_ext_call _ _ _ _ _ _ _ = _`
          (qspec_then `[]` mp_tac) >> simp[]) >>
     `expr_body_pre ce fp.jc_cx env
       (Call a (ExtCall stat skip (fname,ats,rt) opts) (h::t) NONE)
       (es with gas_obs := obs)` by simp[] >>
     `expr_sim_inv ce fp.jc_cx env (es_end with gas_obs := [])` by
       (drule_all exprSimSourceTheory.expr_body_pre_eval_result >> simp[]) >>
     suspend "outer_return_post_join") >>
  simp[Abbr `source`] >>
  `stat <=> (if stat then NONE else case ext_call_kwarg EKValue opts kwvs of
    NONE => SOME 0 | SOME v => dest_NumV v) = NONE` by
    fs[exprSimExtCallCaseTheory.extcall_request_ready_def] >>
  rename1 `dest_AddressV source_target = SOME target_addr` >>
  mp_tac (Q.INST [`cx` |-> `fp.jc_cx`, `arg_types` |-> `ats`,
    `target_v` |-> `source_target`, `target` |-> `target_addr`,
    `skip` |-> `skip`, `ret_type` |-> `rt`,
    `rest` |-> `MAP (\(vv,ty,tv,v). v) (cells : (vyper_value # type # type_value # value) list) ++ kwvs`,
    `value_opt` |-> `(if stat then NONE else case ext_call_kwarg EKValue opts kwvs of
      NONE => SOME 0 | SOME v => dest_NumV v)`]
    exprSimExtCallCaseTheory.eval_ext_call_request) >>
  qpat_assum `LENGTH (MAP (\(vv,ty,tv,v). v) cells) = LENGTH ats`
    (fn th => pure_rewrite_tac[GSYM th]) >>
  simp[rich_listTheory.TAKE_LENGTH_APPEND, listTheory.DROP_APPEND] >>
  disch_then SUBST1_TAC >>
  ho_match_mp_tac exprSimExtCallCaseTheory.extcall_call_step >>
  qpat_assum `extrequest_compile_step _ _ _ _ _ _ _ _ _ _ _ = _`
    (fn th => assume_tac (REWRITE_RULE [exprExtRequestShapeTheory.extrequest_compile_step_def] th)) >>
  first_assum (irule_at (Pat `extcall_request_ready _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  first_assum (irule_at (Pat `comp_ignore_bind _ _ _ = _`)) >>
  simp[] >> rpt gen_tac >> strip_tac >>
  qpat_assum `extrequest_compile_return _ _ _ _ _ _ _ _ _ _ _ _ _ = _`
    (fn th => assume_tac (REWRITE_RULE [exprExtRequestShapeTheory.extrequest_compile_return_def] th)) >>
  `local_ptrs_reserved ce sa` by
    fs[bodyIntCallJointContractTheory.intcall_expr_res_def] >>
  drule_all (SRULE [LET_THM] exprSimExtCallCaseTheory.extcall_return_values_owned) >>
  strip_tac >>
  qexists `marks` >> fs[Abbr `retpost`]
QED

Resume intcall_extcall_expr_step[outer_return_post_join]:
  `wb_frame ce es (es_end with gas_obs := []) sa s endpoint` by
    (fs[loweringPostsTheory.vv_post_def, loweringPostsTheory.wb_frame_def] >>
     metis_tac[]) >>
  `MAP FDOM es.scopes = MAP FDOM es_end.scopes` by
    fs[loweringPostsTheory.wb_frame_def, loweringPostsTheory.locals_kept_def] >>
  `!n b k. local_region ce es.scopes s n b k <=>
            local_region ce es_end.scopes endpoint n b k` by
    (irule wordArgsPtrTheory.wb_frame_local_regions >>
     fs[intcall_expr_res_def] >> metis_tac[]) >>
  `supported_pure_expr fp.jc_tops h /\
   supported_pure_exprs fp.jc_tops (TAKE (LENGTH ats) t) /\
   supported_pure_exprs fp.jc_tops (DROP (LENGTH ats) t)` by
    (fs[supportedExprsTheory.supported_expr_def,
        supportedExprsTheory.supported_pure_expr_def,
        supportedExprsTheory.supported_effect_expr_def,
        supportedExprsTheory.supported_pure_exprs_every] >>
     metis_tac[rich_listTheory.EVERY_TAKE, rich_listTheory.EVERY_DROP]) >>
  `esA.immutables = es.immutables` by
    (qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
     simp[NoAsms, vyperStateTheory.bind_def, AllCaseEqs()] >> strip_tac >>
     drule_all bodyIntCallJointCallSourceTheory.intcall_pure_expr_immutables >>
     drule vyperStateTheory.read_result_state >> rpt strip_tac >> gvs[]) >>
  `esB.immutables = esA.immutables` by
    (qpat_assum `!tail. eval_exprs _ (TAKE _ _) _ = _`
       (qspec_then `[]` assume_tac) >>
     mp_tac (Q.SPECL [`fp.jc_tops`, `TAKE (LENGTH (ats : type list)) t`]
       (cj 2 bodyIntCallJointCallSourceTheory.intcall_pure_immutables_mutual)) >>
     impl_tac >- simp[] >> strip_tac >> first_x_assum drule >> simp[]) >>
  `ee.immutables = esB.immutables` by
    (qpat_assum `!tail. eval_exprs _ (DROP _ _) (esB with gas_obs := kwused ++ tail) = _`
       (qspec_then `[]` assume_tac) >>
     mp_tac (Q.SPECL [`fp.jc_tops`, `DROP (LENGTH (ats : type list)) t`]
       (cj 2 bodyIntCallJointCallSourceTheory.intcall_pure_immutables_mutual)) >>
     impl_tac >- simp[] >> strip_tac >> first_x_assum drule >> simp[]) >>
  `es_end.immutables = ee.immutables` by
    (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[NoAsms, gasSummaryTheory.gas_marked_exec_def, Abbr `source`] >>
     strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >>
     simp[] >> strip_tac >>
     drule vyperCallOutcomeFrameTheory.eval_ext_call_preserves_non_accounts >> simp[]) >>
  `s.vs_alloca_next <= endpoint.vs_alloca_next` by
    (fs[intcall_expr_cont_def] >> decide_tac) >>
  `!op. fp.jc_reserved op ==> eval_operand op endpoint = eval_operand op s` by
    (rpt strip_tac >>
     `?x w. op = Var x /\ lookup_var x fp.jc_oorig = SOME w` by
       metis_tac[intcall_frame_ok_def] >>
     gvs[] >>
     fs[intcall_expr_res_def, loweringPostsTheory.wb_frame_def,
        venomStateTheory.eval_operand_def] >>
     `lookup_var x s = SOME w` by
       (qpat_x_assum `!op. fp.jc_reserved op ==> _`
          (qspec_then `Var x` mp_tac) >> simp[venomStateTheory.eval_operand_def]) >>
     `not_fresh_at sa x` by metis_tac[] >>
     qpat_x_assum `!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==> lookup_var x endpoint = SOME w`
       (qspecl_then [`x`, `w`] mp_tac) >> simp[]) >>
  `intcall_expr_res fp ce env (es_end with gas_obs := []) sb endpoint` by
    (irule bodyIntCallJointCallCoreTheory.intcall_joint_res_frame >>
     conj_tac >- simp[] >>
     conj_tac >- simp[] >>
     conj_tac >- simp[] >>
     reverse conj_tac
     >- fs[loweringPostsTheory.vv_post_def] >>
     qexistsl [`es`, `s`, `sa`] >> simp[] >>
     fs[loweringPostsTheory.vv_post_def, loweringPostsTheory.wb_frame_def,
        intcall_frame_ok_def, intcall_expr_res_def, ci_mono_def]) >>
  `~endpoint.vs_halted` by
    (qpat_assum `gas_marked_path F _ _ u' _ (OK endpoint)` mp_tac >>
     pure_rewrite_tac[fragGasModeTheory.gas_marked_path_def, boolTheory.COND_CLAUSES] >>
     disch_then (strip_assume_tac o MATCH_MP fragGasPathTheory.gas_path_normal)) >>
  `intcall_expr_cont fp ce env es sa s (es_end with gas_obs := []) sb endpoint` by
    (drule_all bodyIntCallJointCallCoreTheory.intcall_expr_cont_vv_post >> simp[]) >>
  simp[Abbr `post`] >>
  fs[loweringPostsTheory.vv_post_def, loweringPostsTheory.vv_own_def] >>
  conj_tac
  >- (drule (GEN_ALL (SRULE [exprLoweringPropsTheory.compile_expr_ci_mono]
        (Q.INST [`cfn` |-> `compile_expr`] exprOperandVarTheory.compiler_call_var))) >> simp[]) >>
  rpt strip_tac >>
  `a = rt` by
    fs[exprSimHypsDefsTheory.expr_body_pre_def, vyperTypeSystemTheory.well_typed_expr_def] >>
  `supported_value_type fp.jc_tops
     (expr_type (Call a (ExtCall stat skip (fname,ats,rt) opts) (h::t) NONE))` by
    fs[supportedExprsTheory.supported_expr_def,
       supportedExprsTheory.supported_pure_call_pop_rejected,
       supportedExprsTheory.supported_effect_expr_def,
       supportedExprFormsTheory.supported_external_return_type_def,
       vyperASTTheory.expr_type_def] >>
  `?v. read_result fp.jc_cx result (es_end with gas_obs := []) =
       (INL v,es_end with gas_obs := [])` by
    (qpat_x_assum `vv_holds _ _ _ _ _ _ _` mp_tac >>
     Cases_on `rt = NoneT` >>
     simp[loweringPostsTheory.vv_holds_def, contextTheory.mk_ptr_def] >>
     metis_tac[]) >>
  drule_all bodyIntCallJointPureSlotTheory.joint_supported_result_slot >>
  simp[arithmeticTheory.ADD_COMM]
QED
Finalise intcall_extcall_expr_step

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
   certificate.  Compose call_step with the exact owned-return normal post
   first; strengthen it only after extracting the complete outer marked path.
   Inferring allocation bounds inside its universal continuation loses that
   path.  The global expression root and a copy of its pure induction
   would inherit unrelated aggregate/subscript admission tags. *)
Theorem intcall_send_word_cps[local]:
  intcall_forced_producer fp e /\ intcall_frame_ok fp /\
  body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  expr_body_pre ce fp.jc_cx env e es /\ is_word_type (expr_type e) /\
  supported_expr fp.jc_tops e /\
  calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr e) /\
  lower_value compile_expr ce (expr_type e) e sa = (op,sb) /\
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

Theorem intcall_send_tail_path_frame[local]:
  expr_has_effect e /\
  emit_op CALL [gas_op; addr_op; val_op; Lit 0w; Lit 0w; Lit 0w; Lit 0w]
    sm = (success, s3) /\
  emit_void ASSERT [success] s3 = (u, sb) /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  fn_has_code sm sb func /\
  stmt_state_rel ctx func cenv cx es1 t /\ wb_frame cenv es es1 sa s0 t /\
  ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  outcomes_accounts_typed es1.outcomes /\
  accounts_runtime_well_typed es1.accounts /\
  IS_SOME (eval_operand gas_op t) /\
  eval_operand addr_op t = SOME aw /\ dest_AddressV to_v = SOME (w2w aw) /\
  eval_operand val_op t = SOME vw /\ dest_NumV amount_v = SOME (w2n vw) /\
  LENGTH gas_vs = (if has_gas then 1 else 0) /\
  (do tv <- eval_send cx has_gas (to_v :: amount_v :: gas_vs);
      read_result cx tv od) es1 = (res, es') /\
  post_value_type cenv e = expr_type e /\ expr_type e = NoneT ==>
  ?n r. gas_marked_path F ctx func t n r /\
    ((?w. r = OK w /\
          (?v. res = INL v /\
               expr_post ctx func cenv cx e es sa sb s0 es' v (Lit 0w) w) /\
          w.vs_current_bb = sb.cs_current_bb /\
          w.vs_inst_idx = LENGTH sb.cs_current_insts /\
          w.vs_memory = t.vs_memory /\ w.vs_allocas = t.vs_allocas /\
          w.vs_alloca_next = t.vs_alloca_next) \/
     (exit_result r /\ expr_exit res r))
Proof
  strip_tac >> drule_all send_tail_shape >> strip_tac >>
  `~not_fresh_at sm out` by gvs[not_fresh_at_def] >>
  `emitted_insts sm sb =
     [mk_inst sm.cs_next_id CALL
        [gas_op; addr_op; val_op; Lit 0w; Lit 0w; Lit 0w; Lit 0w] [out];
      mk_inst (sm.cs_next_id + 1) ASSERT [Var out] []]` by
    fs[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND] >>
  drule_all send_call_read_step >>
  disch_then (qspecl_then [`out`, `sm.cs_next_id`] strip_assume_tac) >>
  rename1 `s' = t with <| vs_outcomes := _; vs_requests := _;
    vs_accounts := _; vs_transient := _; vs_logs := _;
    vs_pending_deletions := _; vs_returndata := _ |>` >>
  `s'.vs_allocas = t.vs_allocas /\ s'.vs_alloca_next = t.vs_alloca_next /\
   s'.vs_memory = t.vs_memory /\ s'.vs_vars = t.vs_vars /\
   s'.vs_labels = t.vs_labels` by
    (qpat_x_assum `s' = _` (fn th => ONCE_REWRITE_TAC [th]) >> simp[]) >>
  qspecl_then [`ctx`, `func`, `sm`, `sb`, `t`,
    `\w. (?v. res = INL v /\
            expr_post ctx func cenv cx e es sa sb s0 es' v (Lit 0w) w) /\
       w.vs_memory = t.vs_memory /\ w.vs_allocas = t.vs_allocas /\
       w.vs_alloca_next = t.vs_alloca_next`,
    `expr_exit res`] mp_tac run_inst_seq_gas_path >>
  BETA_TAC >> reverse impl_tac >- (strip_tac >> metis_tac[]) >>
  simp[rich_listTheory.IS_PREFIX_APPEND, mk_inst_def, is_terminator_def] >>
  gvs[run_inst_seq_def, SRULE [mk_inst_def] send_assert_ok,
      SRULE [mk_inst_def] send_assert_fail, expr_exit_def, mk_inst_def] >>
  simp[update_var_def] >>
  qpat_assum `s'.vs_vars = t.vs_vars` (fn th => rewrite_tac[GSYM th]) >>
  rewrite_tac[GSYM update_var_def] >>
  irule expr_post_none_intro >> simp[stmt_state_rel_inst_idx] >>
  conj_tac
  >- (irule stmt_state_rel_update_var >> conj_tac
      >- (irule fresh_not_local_ptr >> qexists `sm` >> fs[]) >>
      `es'.scopes = es1.scopes /\ es'.immutables = es1.immutables` by
        (drule eval_send_read >> strip_tac >>
         drule eval_send_preserves_non_accounts >> simp[]) >>
      `immutable_alloca_sep func cenv cx es' s'` by
        (irule immutable_alloca_sep_fields >> qexistsl [`t`, `es1`] >>
         gvs[stmt_state_rel_def] >>
         rpt strip_tac >> qexists `id` >>
         gvs[local_region_def, lookup_var_def]) >>
      `immutable_base_zero cenv s'` by
        (irule immutable_base_zero_frame >> qexists `t` >>
         fs[stmt_state_rel_def, lookup_var_def]) >>
      irule stmt_state_rel_allocas_frame >> simp[] >>
      qexistsl [`es1`, `t`] >> simp[] >>
      qpat_x_assum `s' = _ with <|vs_transient := _; vs_returndata := _;
        vs_accounts := _; vs_logs := _; vs_outcomes := _; vs_requests := _;
        vs_pending_deletions := _|>`
        (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `wb_frame cenv es es' sa s0 t` by
    (`es'.scopes = es1.scopes` by
       (drule eval_send_read >> strip_tac >>
        drule eval_send_preserves_non_accounts >> simp[]) >>
     qpat_x_assum `wb_frame cenv es es1 sa s0 t` mp_tac >>
     pure_rewrite_tac[wb_frame_def, locals_kept_def, popped_kept_def] >>
     qpat_x_assum `es'.scopes = es1.scopes` (fn th => pure_rewrite_tac[th]) >>
     disch_then ACCEPT_TAC) >>
  irule wb_frame_readonly_tail >>
  qexists `sm` >>
  qpat_assum `wb_frame cenv es es' sa s0 t` (irule_at Any) >>
  simp[update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rw[] >> gvs[not_fresh_at_def] >> metis_tac[]
QED

Theorem intcall_send_expr_step[local]:
  (!e'. expr_size e' < expr_size (Call a (Send flag) args NONE) ==>
        intcall_expr_producer fp e' /\ intcall_forced_producer fp e' /\
        intcall_map_producer fp e') ==>
  intcall_expr_producer fp (Call a (Send flag) args NONE)
Proof
  strip_tac >> rewrite_tac[intcall_expr_producer_def] >>
  rpt gen_tac >> strip_tac >>
  drule exprSimSendTheory.send_pre_types >> strip_tac >>
  drule exprSimSendTheory.compile_expr_send_stack >> strip_tac >> gvs[] >>
  drule_all exprSimSendTheory.compile_expr_send >> strip_tac >>
  `?dst amt gs. args = dst::amt::gs /\ LENGTH gs = (if flag then 1 else 0)` by
    (Cases_on `flag` >> gvs[listTheory.LENGTH_EQ_NUM_compute]) >>
  gvs[] >>
  gvs[lower_word_args_cons] >>
  `EVERY (supported_pure_expr fp.jc_tops) (dst::amt::gs)` by
    (Cases_on `flag` >> gvs[listTheory.LENGTH_EQ_NUM_compute,
       supportedExprsTheory.supported_expr_def,
       supportedExprsTheory.supported_pure_call_pop_rejected,
       supportedExprsTheory.supported_effect_expr_def]) >>
  `supported_expr fp.jc_tops dst /\
   calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr dst)` by
    (fs[] >> metis_tac[supportedExprsTheory.supported_expr_def,
      bodyExprPreFactsTheory.supported_pure_int_calls,
      vyperTypeCallStackSoundnessTheory.calls_follow_call_graph_nil]) >>
  `intcall_forced_producer fp dst` by
    (first_x_assum (qspec_then `dst` mp_tac) >> simp[]) >>
  `expr_body_pre ce fp.jc_cx env dst es` by
    (irule exprSimSendTheory.expr_body_pre_send_arg >>
     qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _` (irule_at Any) >>
     simp[] >> fs[intcall_expr_res_def]) >>
  `ci_mono sa s1 /\ ci_mono s1 s1'` by
    metis_tac[cj 2 stmtLoweringMonoTheory.ci_mono_compile_expr_sa, pairTheory.SND] >>
  `ci_mono s1' sm` by
    (Cases_on `flag` >> gvs[listTheory.LENGTH_EQ_NUM_compute,
       lower_word_args_cons, lower_word_args_nil] >>
     metis_tac[cj 2 stmtLoweringMonoTheory.ci_mono_compile_expr_sa, pairTheory.SND,
       ci_mono_refl]) >>
  `ci_mono sm s3 /\ ci_mono s3 sb` by
    metis_tac[ci_mono_emit_op, ci_mono_emit_void, pairTheory.SND] >>
  `fn_has_code sa s1 fp.jc_func` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans, fn_has_code_split]) >>
  simp[vyperASTTheory.expr_type_def, contextTheory.vv_operand_def] >>
  once_rewrite_tac[vyperInterpreterTheory.evaluate_def] >>
  simp[vyperStateTheory.type_check_def, vyperStateTheory.assert_def,
       vyperStateTheory.ignore_bind_def, vyperStateTheory.return_def] >>
  `assert T (Error (TypeError "Send args")) = return ()` by
    simp[FUN_EQ_THM, vyperStateTheory.assert_def, vyperStateTheory.return_def] >>
  asm_rewrite_tac[vyperStateTheory.bind_return] >>
  once_rewrite_tac[eval_exprs_cons_action] >>
  rewrite_tac[vyperStateTheory.bind_assoc, vyperStateTheory.bind_return] >>
  once_rewrite_tac[GSYM vyperStateTheory.bind_assoc] >>
  irule intcall_send_word_cps >>
  simp[] >>
  conj_tac
  >- (qpat_x_assum `gas_admissible _ _ _` mp_tac >>
      once_rewrite_tac[vyperInterpreterTheory.evaluate_def] >>
      simp[vyperStateTheory.type_check_def, vyperStateTheory.ignore_bind_def] >>
      asm_rewrite_tac[vyperStateTheory.bind_return] >>
      simp[eval_exprs_cons_action, vyperStateTheory.bind_assoc,
           vyperStateTheory.bind_return]) >>
  qpat_assum `lower_value _ _ _ dst sa = _` (irule_at Any) >>
  qexists `env` >> simp[] >>
  rpt gen_tac >> strip_tac >> suspend "after_dst"
QED

Resume intcall_send_expr_step[after_dst]:
  `intcall_expr_res fp ce env ee s1 u /\ ~u.vs_halted /\
   u.vs_current_bb = s1.cs_current_bb /\
   u.vs_inst_idx = LENGTH s1.cs_current_insts` by
    fs[intcall_expr_cont_def] >>
  `intcall_forced_producer fp amt` by
    (first_x_assum (qspec_then `amt` mp_tac) >> simp[]) >>
  `supported_expr fp.jc_tops amt /\
   calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr amt)` by
    (fs[] >> metis_tac[supportedExprsTheory.supported_expr_def,
      bodyExprPreFactsTheory.supported_pure_int_calls,
      vyperTypeCallStackSoundnessTheory.calls_follow_call_graph_nil]) >>
  `expr_body_pre ce fp.jc_cx env amt ee` by
    (irule exprSimSendTheory.expr_body_pre_send_arg >>
     qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _` (irule_at Any) >>
     simp[] >> fs[intcall_expr_res_def]) >>
  `fn_has_code s1 s1' fp.jc_func` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans, fn_has_code_split]) >>
  simp[eval_exprs_cons_action, vyperStateTheory.bind_assoc,
       vyperStateTheory.bind_return] >>
  once_rewrite_tac[GSYM vyperStateTheory.bind_assoc] >>
  irule intcall_send_word_cps >> simp[] >>
  conj_tac
  >- (qpat_x_assum `gas_admissible _ _ _` mp_tac >>
      once_rewrite_tac[vyperInterpreterTheory.evaluate_def] >>
      simp[vyperStateTheory.type_check_def, vyperStateTheory.ignore_bind_def] >>
      asm_rewrite_tac[vyperStateTheory.bind_return] >>
      simp[eval_exprs_cons_action, vyperStateTheory.bind_assoc,
           vyperStateTheory.bind_return] >>
      once_rewrite_tac[GSYM vyperStateTheory.bind_assoc] >> strip_tac >>
      drule_all stmtSimForRoundsTheory.gas_admissible_bind_tail >>
      simp[eval_exprs_cons_action, vyperStateTheory.bind_assoc,
           vyperStateTheory.bind_return, vyperStateTheory.evaluation_state_component_equality]) >>
  qpat_assum `lower_value _ _ _ amt s1 = _` (irule_at Any) >>
  qexists `env` >> simp[] >> rpt gen_tac >> strip_tac >>
  suspend "after_amt"
QED
Resume intcall_send_expr_step[after_amt]:
  qmatch_goalsub_abbrev_tac `gas_outcome _ _ _ _ _ post _` >>
  `!hg gas_vs gop ready_cs es_ready t aw vw.
    hg = flag /\
    emit_op CALL [gop; addr_op; val_op; Lit 0w; Lit 0w; Lit 0w; Lit 0w]
      ready_cs = (success,s3) /\
    local_ptrs_reserved ce ready_cs /\
    ci_mono sa ready_cs /\ fn_has_code ready_cs sb fp.jc_func /\
    intcall_expr_cont fp ce env es sa s es_ready ready_cs t /\
    wb_frame ce es es_ready sa s t /\ es_ready.gas_obs = [] /\
    eval_operand addr_op t = SOME aw /\ dest_AddressV v = SOME (w2w aw) /\
    eval_operand val_op t = SOME vw /\ dest_NumV v' = SOME (w2n vw) /\
    IS_SOME (eval_operand gop t) /\ LENGTH gas_vs = (if hg then 1 else 0) /\
    (?prefix. !tail. eval_exprs fp.jc_cx (dst::amt::gs)
      (es with gas_obs := prefix ++ tail) =
      (INL (v::v'::gas_vs), es_ready with gas_obs := tail)) ==>
    gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
      (eval_send fp.jc_cx hg (v::v'::gas_vs)) (es_ready,t) post
      (\r ee z. expr_exit r z)` by suspend "suffix_join" >>
  Cases_on `flag`
  >- suspend "gas_operand" >>
  gvs[lower_word_args_nil, listTheory.LENGTH_EQ_NUM_compute] >>
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_return] >>
  suspend "no_gas_ready"
QED
Resume intcall_send_expr_step[suffix_join]:
  rpt gen_tac >> strip_tac >> gvs[] >>
  Cases_on `eval_send fp.jc_cx flag (v::v'::gas_vs) es_ready` >>
  rename1 `eval_send _ _ _ es_ready = (raw,es_end)` >>
  `?res. bind (eval_send fp.jc_cx flag (v::v'::gas_vs)) (read_result fp.jc_cx)
      es_ready = (res,es_end) /\
    raw = (case res of INL z => INL (Value z) | INR ex => INR ex)` by
    (Cases_on `raw`
     >- (drule eval_send_value >> strip_tac >> gvs[] >>
         simp[vyperStateTheory.bind_def, vyperStateTheory.read_result_def,
              vyperStateTheory.return_def]) >>
     simp[vyperStateTheory.bind_def]) >>
  `intcall_expr_res fp ce env es_ready ready_cs t /\ ~t.vs_halted /\
   t.vs_current_bb = ready_cs.cs_current_bb /\
   t.vs_inst_idx = LENGTH ready_cs.cs_current_insts` by
    fs[intcall_expr_cont_def] >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es_ready t /\
   outcomes_accounts_typed es_ready.outcomes /\
   accounts_runtime_well_typed es_ready.accounts` by
    fs[intcall_expr_res_def, exprSimHypsDefsTheory.expr_sim_inv_def,
       vyperTypeExtCallCoreTheory.accounts_runtime_well_typed_accounts_well_typed] >>
  `expr_has_effect (Call NoneT (Send flag) (dst::amt::gs) NONE) /\
   post_value_type ce (Call NoneT (Send flag) (dst::amt::gs) NONE) = NoneT /\
   expr_type (Call NoneT (Send flag) (dst::amt::gs) NONE) = NoneT` by
    simp[loweringPostsTheory.expr_has_effect_thm, vyperASTTheory.expr_type_def] >>
  `sa.cs_next_var <= ready_cs.cs_next_var` by fs[ci_mono_def] >>
  `post_value_type ce (Call NoneT (Send flag) (dst::amt::gs) NONE) =
     expr_type (Call NoneT (Send flag) (dst::amt::gs) NONE)` by simp[vyperASTTheory.expr_type_def] >>
  `(do tv <- eval_send fp.jc_cx flag (v::v'::gas_vs);
       read_result fp.jc_cx tv od) es_ready = (res,es_end)` by
    (CONV_TAC (DEPTH_CONV ETA_CONV) >> first_assum ACCEPT_TAC) >>
  `bind (eval_send fp.jc_cx flag (v::v'::gas_vs)) return =
     eval_send fp.jc_cx flag (v::v'::gas_vs)` by
    (simp[FUN_EQ_THM, vyperStateTheory.bind_def] >> gen_tac >>
     Cases_on `eval_send fp.jc_cx flag (v::v'::gas_vs) x` >>
     Cases_on `q` >> simp[vyperStateTheory.return_def]) >>
  `es_end.gas_obs = [] /\
   !tail. eval_send fp.jc_cx flag (v::v'::gas_vs)
       (es_ready with gas_obs := tail) = (raw,es_end with gas_obs := tail)` by
    (`!cx hg vs st rr en.
       bind (eval_send cx hg vs) return st = (rr,en) ==>
       en.gas_obs = st.gas_obs /\
       !tail. bind (eval_send cx hg vs) return (st with gas_obs := tail) =
         (rr,en with gas_obs := tail)` by
       (ho_match_mp_tac sendSourceFrameTheory.send_bind_gas_frame >>
        simp[vyperStateTheory.return_def]) >>
     metis_tac[]) >>
  drule_all intcall_send_tail_path_frame >> strip_tac
  >- suspend "suffix_success" >>
  rewrite_tac[gasOutcomeTheory.gas_outcome_def] >>
  qexists `REPLICATE n F` >> disj1_tac >>
  rewrite_tac[gasSummaryTheory.gas_summary_at_def] >>
  qexistsl [`raw`, `es_end`, `r`] >>
  simp[gasSummaryTheory.gas_marked_exec_def, rich_listTheory.LENGTH_REPLICATE,
       gasSummaryTheory.gas_explicit_replicate_false] >>
  gvs[] >> Cases_on `res` >> fs[expr_exit_def] >>
  gvs[stmtSimPropsTheory.expr_exit_INR_type]
QED
Resume intcall_send_expr_step[suffix_success]:
  rewrite_tac[gasOutcomeTheory.gas_outcome_def] >>
  qexists `REPLICATE n F` >> disj1_tac >>
  rewrite_tac[gasSummaryTheory.gas_summary_at_def] >>
  qexistsl [`raw`, `es_end`, `r`] >>
  simp[gasSummaryTheory.gas_marked_exec_def, rich_listTheory.LENGTH_REPLICATE,
       gasSummaryTheory.gas_explicit_replicate_false] >>
  gvs[] >>

  `es_end with gas_obs := [] = es_end` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  asm_rewrite_tac[] >>
  `eval_expr fp.jc_cx (Call NoneT (Send flag) (dst::amt::gs) NONE)
      (es with gas_obs := prefix) = (INL (Value v''), es_end)` by
    (once_rewrite_tac[vyperInterpreterTheory.evaluate_def] >>
     simp[vyperStateTheory.type_check_def, vyperStateTheory.ignore_bind_def] >>
     asm_rewrite_tac[vyperStateTheory.bind_return] >>
     once_rewrite_tac[vyperStateTheory.bind_def] >>
     qpat_assum `!tail. eval_exprs _ _ _ = _` (qspec_then `[]` assume_tac) >>
     `es_ready with gas_obs := [] = es_ready` by
       simp[vyperStateTheory.evaluation_state_component_equality] >>
     fs[]) >>
  `expr_body_pre ce fp.jc_cx env
      (Call NoneT (Send flag) (dst::amt::gs) NONE) (es with gas_obs := prefix)` by
    simp[] >>
  drule_all exprSimSourceTheory.expr_body_pre_eval_result >> strip_tac >>
  simp[Abbr `post`] >>
  conj_tac
  >- gvs[loweringPostsTheory.expr_post_def, loweringPostsTheory.vv_holds_def,
        loweringPostsTheory.expr_val_rel_def,
        vyperStateTheory.read_result_def, vyperStateTheory.return_def,
        compileEnvTheory.is_word_type_def] >>
  conj_tac
  >- gvs[loweringPostsTheory.vv_at_def, loweringPostsTheory.expr_post_def,
         vyperStateTheory.read_result_def, vyperStateTheory.return_def] >>
  `~w.vs_halted` by
    (drule fragGasModeTheory.gas_marked_path_exec >>
     metis_tac[exprExtRequestTupleCapturedHeadTheory.extrequest_head_path_nonhalting]) >>
  `es_end.scopes = es_ready.scopes /\
   es_end.immutables = es_ready.immutables` by
    metis_tac[vyperCallOutcomeFrameTheory.eval_send_preserves_non_accounts] >>
  `MAP FDOM es.scopes = MAP FDOM es_end.scopes` by
    (qpat_assum `eval_expr _ _ _ = _` mp_tac >>
     disch_then (assume_tac o MATCH_MP vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom) >> fs[]) >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s /\
   local_ptrs_reserved ce sa` by fs[intcall_expr_res_def] >>
  `wb_frame ce es es_end sa s w` by
    (fs[loweringPostsTheory.expr_post_def, loweringPostsTheory.wb_frame_def] >>
     metis_tac[]) >>
  `!n b k. local_region ce es.scopes s n b k <=>
            local_region ce es_end.scopes w n b k` by
    (irule wordArgsPtrTheory.wb_frame_local_regions >> metis_tac[]) >>
  `!n b k. local_region ce es.scopes s n b k <=>
            local_region ce es_ready.scopes t n b k` by
    (irule wordArgsPtrTheory.wb_frame_local_regions >> metis_tac[]) >>
  `!op. fp.jc_reserved op ==> eval_operand op w = eval_operand op t` by
    (rpt strip_tac >>
     `?x z. op = Var x /\ lookup_var x fp.jc_oorig = SOME z` by
       metis_tac[intcall_frame_ok_def] >>
     `not_fresh_at sa x /\ eval_operand op s = SOME z /\
      eval_operand op t = SOME z` by
       (fs[intcall_expr_res_def, venomStateTheory.eval_operand_def] >> metis_tac[]) >>
     qpat_x_assum `op = Var x` SUBST_ALL_TAC >>
     fs[loweringPostsTheory.wb_frame_def, venomStateTheory.eval_operand_def] >>
     `lookup_var x w = SOME z` by
       (qpat_x_assum `!x w'. not_fresh_at sa x /\ lookup_var x s = SOME w' ==> lookup_var x w = SOME w'` irule >> simp[]) >>
     simp[]) >>
  `supported_pure_exprs fp.jc_tops (dst::amt::gs)` by
    simp[supportedExprsTheory.supported_pure_exprs_every] >>
  `es_ready.immutables = es.immutables` by
    (drule (cj 2 bodyIntCallJointCallSourceTheory.intcall_pure_immutables_mutual) >>
     strip_tac >>
     qpat_assum `!tail. eval_exprs _ _ _ = _` (qspec_then `[]` assume_tac) >>
     first_x_assum drule >> simp[]) >>
  `ready_cs.cs_next_var <= sb.cs_next_var` by
    (drule compilerInstructionSuffixTheory.added_insts_emit_op >>
     strip_tac >> fs[ci_mono_def] >> decide_tac) >>
  `intcall_expr_res fp ce env es_end sb w` by
    (irule bodyIntCallJointCallCoreTheory.intcall_joint_res_frame >>
     `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es_end w` by
       fs[loweringPostsTheory.expr_post_def] >>
     `allocas_above fp.jc_lo w` by
       (gvs[intcall_expr_res_def, intCallFrameTheory.allocas_above_def] >>
        rpt strip_tac >> first_x_assum drule >> simp[]) >>
     simp[] >>
     qexistsl [`es`, `s`, `sa`] >> simp[] >>
     conj_tac
     >- (qpat_x_assum `wb_frame ce es es_end sa s w` mp_tac >>
         simp[loweringPostsTheory.wb_frame_def]) >>
     conj_tac
     >- (rpt strip_tac >> metis_tac[]) >>
     conj_tac
     >- (qpat_x_assum `intcall_expr_res fp ce env es_ready ready_cs t` mp_tac >>
         qpat_x_assum `intcall_expr_res fp ce env es sa s` mp_tac >>
         simp[intcall_expr_res_def] >> rpt strip_tac >> metis_tac[]) >>
     conj_tac
     >- (qpat_x_assum `intcall_expr_res fp ce env es_ready ready_cs t` mp_tac >>
         qpat_x_assum `intcall_expr_res fp ce env es sa s` mp_tac >>
         simp[intcall_expr_res_def] >> rpt strip_tac >> metis_tac[]) >>
     fs[intcall_expr_cont_def]) >>
  fs[intcall_expr_cont_def, loweringPostsTheory.expr_post_def] >>
  metis_tac[]
QED
Resume intcall_send_expr_step[gas_operand]:
  gvs[listTheory.LENGTH_EQ_NUM_compute, lower_word_args_cons, lower_word_args_nil] >>
  rename1 `expr_type gas_e = BaseT (UintT 256)` >>
  `intcall_expr_res fp ce env ee' s1' u' /\ ~u'.vs_halted /\
   u'.vs_current_bb = s1'.cs_current_bb /\
   u'.vs_inst_idx = LENGTH s1'.cs_current_insts` by
    fs[intcall_expr_cont_def] >>
  `intcall_forced_producer fp gas_e` by
    (first_x_assum (qspec_then `gas_e` mp_tac) >> simp[]) >>
  `supported_expr fp.jc_tops gas_e /\
   calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr gas_e)` by
    (fs[] >> metis_tac[supportedExprsTheory.supported_expr_def,
      bodyExprPreFactsTheory.supported_pure_int_calls,
      vyperTypeCallStackSoundnessTheory.calls_follow_call_graph_nil]) >>
  `expr_body_pre ce fp.jc_cx env gas_e ee'` by
    (irule exprSimSendTheory.expr_body_pre_send_arg >>
     qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _` (irule_at Any) >>
     simp[] >> fs[intcall_expr_res_def]) >>
  `fn_has_code s1' sm fp.jc_func` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans, fn_has_code_split]) >>
  simp[eval_exprs_cons_action, vyperInterpreterTheory.evaluate_def,
       vyperStateTheory.bind_assoc, vyperStateTheory.bind_return] >>
  once_rewrite_tac[GSYM vyperStateTheory.bind_assoc] >>
  irule intcall_send_word_cps >> simp[] >>
  conj_tac
  >- (qpat_x_assum `gas_admissible _ _ _` mp_tac >>
      once_rewrite_tac[vyperInterpreterTheory.evaluate_def] >>
      simp[vyperStateTheory.type_check_def, vyperStateTheory.ignore_bind_def] >>
      asm_rewrite_tac[vyperStateTheory.bind_return] >>
      simp[eval_exprs_cons_action, vyperStateTheory.bind_assoc,
           vyperStateTheory.bind_return, vyperInterpreterTheory.evaluate_def] >>
      once_rewrite_tac[GSYM vyperStateTheory.bind_assoc] >> strip_tac >>
      drule_all stmtSimForRoundsTheory.gas_admissible_bind_tail >>
      simp[vyperStateTheory.bind_assoc] >>
      once_rewrite_tac[GSYM vyperStateTheory.bind_assoc] >> strip_tac >>
      drule_all stmtSimForRoundsTheory.gas_admissible_bind_tail >>
      simp[vyperStateTheory.evaluation_state_component_equality,
           vyperStateTheory.bind_assoc]) >>
  qpat_assum `lower_value _ _ _ gas_e s1' = _` (irule_at Any) >>
  qexists `env` >> simp[] >> rpt gen_tac >> strip_tac >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (qpat_assum `!tail. monad_bind (eval_expr _ dst) _ _ = _`
       (qspec_then `[]` assume_tac) >>
     `expr_body_pre ce fp.jc_cx env dst (es with gas_obs := used ++ [])` by simp[] >>
     qpat_assum `monad_bind (eval_expr _ _) _ _ = _`
       (mp_then Any mp_tac (CONV_RULE (DEPTH_CONV ETA_CONV)
         abiEncodeArgsCaseTheory.abi_args_success_ready)) >> simp[] >>
     disch_then (qspecl_then [`env`, `ce`] mp_tac) >> simp[]) >>
  `MAP FDOM ee.scopes = MAP FDOM ee'.scopes` by
    (qpat_assum `!tail. monad_bind (eval_expr _ amt) _ _ = _`
       (qspec_then `[]` assume_tac) >>
     `expr_body_pre ce fp.jc_cx env amt (ee with gas_obs := used' ++ [])` by simp[] >>
     qpat_assum `monad_bind (eval_expr _ _) _ _ = _`
       (mp_then Any mp_tac (CONV_RULE (DEPTH_CONV ETA_CONV)
         abiEncodeArgsCaseTheory.abi_args_success_ready)) >> simp[] >>
     disch_then (qspecl_then [`env`, `ce`] mp_tac) >> simp[]) >>
  `intcall_expr_cont fp ce env es sa s ee' s1' u'` by
    (irule bodyIntCallJointCallCoreTheory.intcall_expr_cont_trans >>
     conj_tac >- simp[] >>
     qexistsl [`s1`, `ee`, `u`] >> simp[] >> fs[ci_mono_def]) >>
  `intcall_expr_cont fp ce env es sa s ee'' sm u''` by
    (irule bodyIntCallJointCallCoreTheory.intcall_expr_cont_trans >>
     conj_tac >- simp[] >>
     qexistsl [`s1'`, `ee'`, `u'`] >> simp[] >> fs[ci_mono_def]) >>
  `wb_frame ce es ee'' sa s u''` by
    metis_tac[bodyIntCallJointCallCoreTheory.intcall_expr_cont_frame] >>
  `ci_mono sa sm` by metis_tac[ci_mono_trans] >>
  `local_ptrs_reserved ce sm` by fs[intcall_expr_cont_def, intcall_expr_res_def] >>
  `fn_has_code sm sb fp.jc_func` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans, fn_has_code_split]) >>
  `?prefix. !tail. eval_exprs fp.jc_cx [dst;amt;gas_e]
     (es with gas_obs := prefix ++ tail) =
     (INL [v;v';v''],ee'' with gas_obs := tail)` by
    (qexists `used ++ used' ++ used''` >> gen_tac >>
     once_rewrite_tac[eval_exprs_cons_action] >>
     once_rewrite_tac[vyperStateTheory.bind_def] >>
     asm_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >>
     simp_tac (srw_ss()) [] >>
     once_rewrite_tac[vyperStateTheory.bind_def] >>
     once_rewrite_tac[eval_exprs_cons_action] >>
     once_rewrite_tac[vyperStateTheory.bind_def] >>
     asm_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >>
     simp_tac (srw_ss()) [] >>
     once_rewrite_tac[vyperStateTheory.bind_def] >>
     asm_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >>
     once_rewrite_tac[eval_exprs_cons_action] >>
     once_rewrite_tac[vyperStateTheory.bind_def] >>
     asm_rewrite_tac[] >>
     simp[eval_exprs_nil, vyperStateTheory.bind_def, vyperStateTheory.return_def]) >>
  `value_has_type (BaseTV AddressT) v` by
    (`expr_body_pre ce fp.jc_cx env dst (es with gas_obs := used ++ [])` by simp[] >>
     qpat_assum `!tail. monad_bind (eval_expr _ dst) _ _ = _`
       (qspec_then `[]` assume_tac) >>
     qpat_assum `monad_bind (eval_expr _ _) _ _ = _`
       (mp_then Any mp_tac (CONV_RULE (DEPTH_CONV ETA_CONV)
         exprSimSourceTheory.expr_body_pre_word_value)) >>
     disch_then (qspecl_then [`ce`, `env`] mp_tac) >>
     simp[vyperValueTheory.evaluate_type_def]) >>
  `value_has_type (BaseTV (UintT 256)) v'` by
    (`expr_body_pre ce fp.jc_cx env amt (ee with gas_obs := used' ++ [])` by simp[] >>
     qpat_assum `!tail. monad_bind (eval_expr _ amt) _ _ = _`
       (qspec_then `[]` assume_tac) >>
     qpat_assum `monad_bind (eval_expr _ _) _ _ = _`
       (mp_then Any mp_tac (CONV_RULE (DEPTH_CONV ETA_CONV)
         exprSimSourceTheory.expr_body_pre_word_value)) >>
     disch_then (qspecl_then [`ce`, `env`] mp_tac) >>
     simp[vyperValueTheory.evaluate_type_def]) >>
  `eval_operand addr_op u = SOME (typed_val_to_w256 (BaseTV AddressT) v)` by
    (irule exprSimPrecompilesTheory.expr_post_typed_stack_operand >>
     qpat_assum `expr_post _ _ _ _ dst _ _ _ _ _ _ _ _` (irule_at Any) >>
     simp[vyperValueTheory.evaluate_type_def]) >>
  `eval_operand val_op u' = SOME (typed_val_to_w256 (BaseTV (UintT 256)) v')` by
    (irule exprSimPrecompilesTheory.expr_post_typed_stack_operand >>
     qpat_assum `expr_post _ _ _ _ amt _ _ _ _ _ _ _ _` (irule_at Any) >>
     simp[vyperValueTheory.evaluate_type_def]) >>
  `eval_operand gas_op u'' = SOME (typed_val_to_w256 (BaseTV (UintT 256)) v'')` by
    (irule exprSimPrecompilesTheory.expr_post_typed_stack_operand >>
     qpat_assum `expr_post _ _ _ _ gas_e _ _ _ _ _ _ _ _` (irule_at Any) >>
     simp[vyperValueTheory.evaluate_type_def]) >>
  `(!z. addr_op = Var z ==> not_fresh_at s1 z) /\
   (!l. addr_op <> Label l)` by
    (qpat_assum `lower_value _ _ _ dst _ = _`
       (mp_then Any mp_tac exprSimSourceTheory.expr_body_pre_lower_value_word_shape) >>
     disch_then (qspecl_then [`fp.jc_cx`, `env`, `es`] mp_tac) >> simp[]) >>
  `(!z. val_op = Var z ==> not_fresh_at s1' z) /\
   (!l. val_op <> Label l)` by
    (qpat_assum `lower_value _ _ _ amt _ = _`
       (mp_then Any mp_tac exprSimSourceTheory.expr_body_pre_lower_value_word_shape) >>
     disch_then (qspecl_then [`fp.jc_cx`, `env`, `ee`] mp_tac) >> simp[]) >>
  `wb_frame ce ee ee' s1 u u' /\ wb_frame ce ee' ee'' s1' u' u''` by
    metis_tac[bodyIntCallJointCallCoreTheory.intcall_expr_cont_frame] >>
  `eval_operand addr_op u' = SOME (typed_val_to_w256 (BaseTV AddressT) v)` by
    (irule abiEncodeArgsSimTheory.abi_args_operand_kept >>
     conj_tac >- simp[] >>
     qexistsl [`ce`, `ee`, `ee'`, `u`, `s1`] >> simp[]) >>
  `!z. addr_op = Var z ==> not_fresh_at s1' z` by
    (fs[ci_mono_def, not_fresh_at_def] >> rpt strip_tac >>
     first_x_assum drule >> simp[not_fresh_at_def] >> decide_tac) >>
  `eval_operand addr_op u'' = SOME (typed_val_to_w256 (BaseTV AddressT) v)` by
    (irule abiEncodeArgsSimTheory.abi_args_operand_kept >>
     conj_tac >- simp[] >>
     qexistsl [`ce`, `ee'`, `ee''`, `u'`, `s1'`] >> simp[]) >>
  `eval_operand val_op u'' = SOME (typed_val_to_w256 (BaseTV (UintT 256)) v')` by
    (irule abiEncodeArgsSimTheory.abi_args_operand_kept >>
     conj_tac >- simp[] >>
     qexistsl [`ce`, `ee'`, `ee''`, `u'`, `s1'`] >> simp[]) >>
  first_x_assum irule >>
  simp[exprSimSendTheory.address_typed_dest, exprSimSendTheory.uint256_typed_dest] >>
  conj_tac >- metis_tac[] >>
  qexistsl [`gas_op`, `sm`] >> simp[]
QED
Resume intcall_send_expr_step[no_gas_ready]:
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (qpat_assum `!tail. monad_bind (eval_expr _ dst) _ _ = _`
       (qspec_then `[]` assume_tac) >>
     `expr_body_pre ce fp.jc_cx env dst (es with gas_obs := used ++ [])` by simp[] >>
     qpat_assum `monad_bind (eval_expr _ _) _ _ = _`
       (mp_then Any mp_tac (CONV_RULE (DEPTH_CONV ETA_CONV)
         abiEncodeArgsCaseTheory.abi_args_success_ready)) >> simp[] >>
     disch_then (qspecl_then [`env`, `ce`] mp_tac) >> simp[]) >>
  `intcall_expr_cont fp ce env es sa s ee' s1' u'` by
    (irule bodyIntCallJointCallCoreTheory.intcall_expr_cont_trans >>
     conj_tac >- simp[] >>
     qexistsl [`s1`, `ee`, `u`] >> simp[] >> fs[ci_mono_def]) >>
  `wb_frame ce es ee' sa s u'` by
    metis_tac[bodyIntCallJointCallCoreTheory.intcall_expr_cont_frame] >>
  `ci_mono sa s1'` by metis_tac[ci_mono_trans] >>
  `local_ptrs_reserved ce s1'` by fs[intcall_expr_cont_def, intcall_expr_res_def] >>
  `fn_has_code s1' sb fp.jc_func` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans, fn_has_code_split]) >>
  `?prefix. !tail. eval_exprs fp.jc_cx [dst;amt]
     (es with gas_obs := prefix ++ tail) =
     (INL [v;v'],ee' with gas_obs := tail)` by
    (qexists `used ++ used'` >> gen_tac >>
     once_rewrite_tac[eval_exprs_cons_action] >>
     once_rewrite_tac[vyperStateTheory.bind_def] >>
     asm_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >>
     simp_tac (srw_ss()) [] >>
     once_rewrite_tac[vyperStateTheory.bind_def] >>
     once_rewrite_tac[eval_exprs_cons_action] >>
     once_rewrite_tac[vyperStateTheory.bind_def] >>
     asm_rewrite_tac[] >>
     simp[eval_exprs_nil, vyperStateTheory.bind_def, vyperStateTheory.return_def]) >>
  `value_has_type (BaseTV AddressT) v` by
    (`expr_body_pre ce fp.jc_cx env dst (es with gas_obs := used ++ [])` by simp[] >>
     qpat_assum `!tail. monad_bind (eval_expr _ dst) _ _ = _`
       (qspec_then `[]` assume_tac) >>
     qpat_assum `monad_bind (eval_expr _ _) _ _ = _`
       (mp_then Any mp_tac (CONV_RULE (DEPTH_CONV ETA_CONV)
         exprSimSourceTheory.expr_body_pre_word_value)) >>
     disch_then (qspecl_then [`ce`, `env`] mp_tac) >>
     simp[vyperValueTheory.evaluate_type_def]) >>
  `value_has_type (BaseTV (UintT 256)) v'` by
    (`expr_body_pre ce fp.jc_cx env amt (ee with gas_obs := used' ++ [])` by simp[] >>
     qpat_assum `!tail. monad_bind (eval_expr _ amt) _ _ = _`
       (qspec_then `[]` assume_tac) >>
     qpat_assum `monad_bind (eval_expr _ _) _ _ = _`
       (mp_then Any mp_tac (CONV_RULE (DEPTH_CONV ETA_CONV)
         exprSimSourceTheory.expr_body_pre_word_value)) >>
     disch_then (qspecl_then [`ce`, `env`] mp_tac) >>
     simp[vyperValueTheory.evaluate_type_def]) >>
  `eval_operand addr_op u = SOME (typed_val_to_w256 (BaseTV AddressT) v)` by
    (irule exprSimPrecompilesTheory.expr_post_typed_stack_operand >>
     qpat_assum `expr_post _ _ _ _ dst _ _ _ _ _ _ _ _` (irule_at Any) >>
     simp[vyperValueTheory.evaluate_type_def]) >>
  `eval_operand val_op u' = SOME (typed_val_to_w256 (BaseTV (UintT 256)) v')` by
    (irule exprSimPrecompilesTheory.expr_post_typed_stack_operand >>
     qpat_assum `expr_post _ _ _ _ amt _ _ _ _ _ _ _ _` (irule_at Any) >>
     simp[vyperValueTheory.evaluate_type_def]) >>
  `(!z. addr_op = Var z ==> not_fresh_at s1 z) /\
   (!l. addr_op <> Label l)` by
    metis_tac[exprSimSourceTheory.expr_body_pre_lower_value_word_shape] >>
  `wb_frame ce ee ee' s1 u u'` by
    metis_tac[bodyIntCallJointCallCoreTheory.intcall_expr_cont_frame] >>
  `eval_operand addr_op u' = SOME (typed_val_to_w256 (BaseTV AddressT) v)` by
    (irule abiEncodeArgsSimTheory.abi_args_operand_kept >>
     metis_tac[]) >>
  first_x_assum irule >>
  simp[exprSimSendTheory.address_typed_dest, exprSimSendTheory.uint256_typed_dest] >>
  conj_tac >- metis_tac[] >>
  qexistsl [`Lit 0w`, `s1'`] >> simp[venomStateTheory.eval_operand_def]
QED
Finalise intcall_send_expr_step

Theorem intcall_extcall_step:
  (!e'. expr_size e' < expr_size e ==>
        intcall_expr_producer fp e' /\ intcall_forced_producer fp e' /\
        intcall_map_producer fp e') /\
  (?a tgt args dflt. e = Call a tgt args dflt /\ !nsid. tgt <> IntCall nsid) ==>
  intcall_expr_producer fp e /\ intcall_map_producer fp e
Proof
  cheat
QED

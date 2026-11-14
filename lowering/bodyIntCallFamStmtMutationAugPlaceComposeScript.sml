(* Normal target endpoints and counted composition for augmented places. *)
Theory bodyIntCallFamStmtMutationAugPlaceCompose
Ancestors
  bodyIntCallFamStmtMutationAugPlaceJoin
  bodyIntCallFamStmtMutationAugPlaceMemoryReady
  bodyIntCallFamStmtMutationAugPlaceStorageReady
  bodyIntCallJointContract stmtSimAugAssignPlaceMemory
  stmtSimAugAssignPlaceStorage compileEnv exprSimOperands
  stmtSimDeclCompose exprSimSliceCompose loweringPosts loweringStateRelDefs
  tuplePlaceHeadGas bodyIntCallFamAggSubscriptGas bodyIntCallFamAggStructFields
  exprSimIfExpWidenedAdapter exprSimExtract32Counted

Theorem intcall_aug_place_load_frame:
  target_post fp.jc_ctx fp.jc_func ce fp.jc_cx es sa sb s0 mid
    (PlaceR p) (Type ty) rp s /\
  local_ptrs_reserved ce sb /\
  intcall_expr_cont fp ce env mid sb s mid sl u /\
  gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) ==>
  ?w. eval_operand (FST rp) u = SOME w /\
    place_ptr_rel ce fp.jc_cx u (PlaceR p) w (FST (SND rp)) (Type ty)
Proof
  strip_tac >>
  `?w. eval_operand (FST rp) s = SOME w /\
    place_ptr_rel ce fp.jc_cx s (PlaceR p) w (FST (SND rp)) (Type ty)` by
    fs[target_post_def] >>
  `eval_operand (FST rp) u = SOME w` by
    (irule aug_place_saved_operand >>
     qexistsl [`sb`,`fp.jc_ctx`,`fp.jc_func`,`F`,`0`,`s`] >>
     fs[intcall_expr_cont_def,target_post_def]) >>
  qexists `w` >> simp[] >> Cases_on `p` >>
  fs[place_ptr_rel_def] >>
  fs[intcall_expr_cont_def,local_ptrs_reserved_def] >> metis_tac[]
QED

Theorem intcall_aug_place_memory_loaded:
  intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  supported_stmt fp.jc_tops bindings (AugAssign ty tg bop rhs) /\
  ((?bt fld. tg = AttributeTarget bt fld) \/
   (?bt key. tg = SubscriptTarget bt key)) /\
  type_stmt env ret_ty (AugAssign ty tg bop rhs) = SOME env' /\
  expr_body_pre ce fp.jc_cx env rhs es /\
  target_indices_pre ce fp.jc_cx env tg /\
  eval_target_place fp.jc_cx tg es = (INL (MemoryPlace id path),ee) /\
  target_post fp.jc_ctx fp.jc_func ce fp.jc_cx es sa sb s ee
    (PlaceR (MemoryPlace id path)) (Type ty) rp t /\
  intcall_expr_cont fp ce env es sa s ee sb t /\
  emit_op MLOAD [FST rp] sb = (cur,sl) /\ fn_has_code sb sl fp.jc_func ==>
  ?old tv w u.
    read_place fp.jc_cx (MemoryPlace id path) ee = (INL old,ee) /\
    place_type_value fp.jc_cx (MemoryPlace id path) ee = (INL tv,ee) /\
    evaluate_type (get_tenv fp.jc_cx) ty = SOME tv /\ value_has_type tv old /\
    type_bits ty MOD 8 = 0 /\ expr_body_pre ce fp.jc_cx env rhs ee /\
    gas_marked_path F fp.jc_ctx fp.jc_func t 0 (OK u) /\
    eval_operand cur u = SOME (typed_val_to_w256 tv old) /\
    (!x. cur = Var x ==> not_fresh_at sl x) /\
    eval_operand (FST rp) u = SOME w /\
    place_ptr_rel ce fp.jc_cx u (PlaceR (MemoryPlace id path)) w
      (FST (SND rp)) (Type ty) /\
    intcall_expr_cont fp ce env ee sb t ee sl u
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all intcall_aug_place_memory_read_ready >> strip_tac >>
  rename1 `read_place _ _ ee = (INL old,ee)` >>
  `intcall_expr_res fp ce env ee sb t /\ ~t.vs_halted /\
   t.vs_current_bb = sb.cs_current_bb /\
   t.vs_inst_idx = LENGTH sb.cs_current_insts` by fs[intcall_expr_cont_def] >>
  drule_all intcall_aug_place_memory_load_cont >> strip_tac >>
  `local_ptrs_reserved ce sb` by fs[intcall_expr_res_def] >>
  drule_all intcall_aug_place_load_frame >> strip_tac >>
  qexistsl [`old`,`tv`] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem intcall_aug_place_storage_loaded:
  intcall_frame_ok fp /\
  is_word_type ty /\
  expr_body_pre ce fp.jc_cx env rhs es /\
  target_indices_pre ce fp.jc_cx env tg /\
  eval_target_place fp.jc_cx tg es = (INL (StoragePlace tr slot tv),ee) /\
  target_post fp.jc_ctx fp.jc_func ce fp.jc_cx es sa sb s ee
    (PlaceR (StoragePlace tr slot tv)) (Type ty) rp t /\
  intcall_expr_cont fp ce env es sa s ee sb t /\
  emit_op (if tr then TLOAD else SLOAD) [FST rp] sb = (cur,sl) /\
  fn_has_code sb sl fp.jc_func ==>
  ?old u.
    read_place fp.jc_cx (StoragePlace tr slot tv) ee = (INL old,ee) /\
    place_type_value fp.jc_cx (StoragePlace tr slot tv) ee = (INL tv,ee) /\
    evaluate_type (get_tenv fp.jc_cx) ty = SOME tv /\ value_has_type tv old /\
    storage_place_region fp.jc_cx (StoragePlace tr slot tv) /\
    expr_body_pre ce fp.jc_cx env rhs ee /\
    gas_marked_path F fp.jc_ctx fp.jc_func t 0 (OK u) /\
    eval_operand cur u = SOME (typed_val_to_w256 tv old) /\
    (!x. cur = Var x ==> not_fresh_at sl x) /\
    eval_operand (FST rp) u = SOME slot /\
    place_ptr_rel ce fp.jc_cx u (PlaceR (StoragePlace tr slot tv)) slot
      (FST (SND rp)) (Type ty) /\
    intcall_expr_cont fp ce env ee sb t ee sl u
Proof
  strip_tac >>
  `evaluate_type (get_tenv fp.jc_cx) ty = SOME tv` by
    fs[target_post_def,place_ptr_rel_def] >>
  `intcall_expr_res fp ce env ee sb t /\ ~t.vs_halted /\
   t.vs_current_bb = sb.cs_current_bb /\
   t.vs_inst_idx = LENGTH sb.cs_current_insts` by fs[intcall_expr_cont_def] >>
  `storage_layout_safe fp.jc_cx /\ contract_storage_well_formed fp.jc_cx ee` by
    fs[intcall_expr_res_def,exprSimHypsDefsTheory.expr_sim_inv_def] >>
  drule_all intcall_storage_place_read_ready >> strip_tac >>
  rename1 `read_place _ _ ee = (INL old,ee)` >>
  drule_all intcall_aug_place_storage_load_cont >> strip_tac >>
  `local_ptrs_reserved ce sb` by fs[intcall_expr_res_def] >>
  drule_all intcall_aug_place_load_frame >> strip_tac >>
  `expr_body_pre ce fp.jc_cx env rhs ee` by
    metis_tac[aug_place_rhs_pre_target] >>
  qexistsl [`old`,`u`] >> fs[place_ptr_rel_def]
QED

Theorem intcall_aug_place_loaded_prefix:
  sa.cs_next_var <= sb.cs_next_var /\ sb.cs_next_var <= sl.cs_next_var /\
  intcall_expr_cont fp ce env es sa s mid sb t /\
  intcall_expr_cont fp ce env mid sb t mid sl u /\
  gas_marked_path F fp.jc_ctx fp.jc_func t 0 (OK u) /\
  gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func) source (mid,u)
    (\res ff v. res = INL () /\ intcall_joint_res fp ce env ff sf v /\
      ~v.vs_halted /\ v.vs_current_bb = sf.cs_current_bb /\
      v.vs_inst_idx = LENGTH sf.cs_current_insts /\
      (!z w. not_fresh_at sl z /\ lookup_var z u = SOME w ==> lookup_var z v = SOME w) /\
      (!aid b. FLOOKUP u.vs_allocas aid = SOME b ==> FLOOKUP v.vs_allocas aid = SOME b) /\
      u.vs_alloca_next <= v.vs_alloca_next) (intcall_stmt_exit fp) ==>
  gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func) source (mid,t)
    (\res ff v. res = INL () /\ intcall_joint_res fp ce env ff sf v /\
      ~v.vs_halted /\ v.vs_current_bb = sf.cs_current_bb /\
      v.vs_inst_idx = LENGTH sf.cs_current_insts /\
      (!z w. not_fresh_at sa z /\ lookup_var z s = SOME w ==> lookup_var z v = SOME w) /\
      (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP v.vs_allocas aid = SOME b) /\
      s.vs_alloca_next <= v.vs_alloca_next) (intcall_stmt_exit fp)
Proof
  strip_tac >> irule gas_outcome_zero_prefix >> goal_assum (drule_at Any) >>
  irule slice_gas_outcome_conseq >> goal_assum (drule_at Any) >> simp[] >>
  rpt strip_tac >> fs[intcall_expr_cont_def] >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` kall_tac >>
  metis_tac[loweringShapeDefsTheory.not_fresh_at_mono,arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem intcall_aug_place_normal_outcome:
  intcall_forced_producer fp rhs /\ intcall_frame_ok fp /\
  body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  supported_program fp.jc_tops /\ get_module_code fp.jc_cx NONE = SOME fp.jc_tops /\
  supported_stmt fp.jc_tops bindings (AugAssign ty tg bop rhs) /\
  supported_target_info fp.jc_tops bindings tg = SOME info /\
  supportedExprs$supported_expr fp.jc_tops rhs /\
  calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr rhs) /\
  call_evaluation_safe fp.jc_cx (int_calls_stmt (AugAssign ty tg bop rhs)) /\
  type_stmt env ret_ty (AugAssign ty tg bop rhs) = SOME env /\
  expr_body_pre ce fp.jc_cx env rhs es /\ target_indices_pre ce fp.jc_cx env tg /\
  ce.ce_alloca_locals /\ ce_locals_declared ce env /\ ~fp.jc_cx.txn.is_static /\
  word_value_type ty /\ word_value_type (expr_type rhs) /\
  type_bits ty MOD 8 = 0 /\
  IS_SOME (evaluate_type (get_tenv fp.jc_cx) (expr_type rhs)) /\
  (!tail. eval_target_place fp.jc_cx tg (es with gas_obs := prefix ++ tail) =
    (INL p,mid with gas_obs := tail)) /\ mid.gas_obs = [] /\
  (case p of MemoryPlace id path =>
    ((?bt fld. tg = AttributeTarget bt fld) \/ (?bt key. tg = SubscriptTarget bt key))
    | _ => T) /\
  target_post fp.jc_ctx fp.jc_func ce fp.jc_cx es sa sp s mid (PlaceR p) (Type ty) rp t /\
  intcall_expr_cont fp ce env es sa s mid sp t /\
  FST (SND rp) = SOME loc /\
  emit_op (case loc of LocStorage => SLOAD | LocTransient => TLOAD | _ => MLOAD)
    [FST rp] sp = (cur,sl) /\
  lower_value compile_expr ce ty rhs sl = (rhsop,s2) /\
  compile_binop bop cur rhsop ty NONE
    (if bop = Exp then expr_int_literal rhs else NONE) s2 = (result,s3) /\
  emit_void (case loc of LocStorage => SSTORE | LocTransient => TSTORE | _ => MSTORE)
    [FST rp;result] s3 = ((),sf) /\
  fn_has_code sp sl fp.jc_func /\ fn_has_code sl s2 fp.jc_func /\
  fn_has_code s2 s3 fp.jc_func /\ fn_has_code s3 sf fp.jc_func /\
  fn_inst_ids_distinct fp.jc_func /\ sa.cs_next_var <= sp.cs_next_var /\
  sp.cs_next_var <= sl.cs_next_var /\ sl.cs_next_var <= s2.cs_next_var /\
  gas_admissible (eval_stmt fp.jc_cx (AugAssign ty tg bop rhs)) (stmt_res_ok lctx) es ==>
  ?old tv.
    read_place fp.jc_cx p mid = (INL old,mid) /\
    place_type_value fp.jc_cx p mid = (INL tv,mid) /\
    gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
      (bind (bind (eval_expr fp.jc_cx rhs) (read_result fp.jc_cx))
        (\v. bind (lift_sum (evaluate_binop
          (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
          tv bop old v)) (write_place fp.jc_cx p))) (mid,t)
      (\res ff v. res = INL () /\ intcall_joint_res fp ce env ff sf v /\
        ~v.vs_halted /\ v.vs_current_bb = sf.cs_current_bb /\
        v.vs_inst_idx = LENGTH sf.cs_current_insts /\
        (!z w. not_fresh_at sa z /\ lookup_var z s = SOME w ==> lookup_var z v = SOME w) /\
        (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP v.vs_allocas aid = SOME b) /\
        s.vs_alloca_next <= v.vs_alloca_next) (intcall_stmt_exit fp)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `eval_target_place fp.jc_cx tg (es with gas_obs := prefix) = (INL p,mid)` by
    (qpat_x_assum `!tail. eval_target_place _ _ _ = _`
       (qspec_then `[]` mp_tac) >> simp[vyperStateTheory.evaluation_state_component_equality]) >>
  drule_all bodyAugPlaceTargetTheory.aug_place_supported_success_kind >>
  strip_tac >> gvs[]
  >- suspend "memory"
  >- suspend "memory"
  >> suspend "storage"
QED

Resume intcall_aug_place_normal_outcome[memory]:
  markerLib.RESUME_TAC >>
  `loc = LocMemory` by fs[target_post_def,place_ptr_rel_def] >> gvs[] >>
  `target_post fp.jc_ctx fp.jc_func ce fp.jc_cx (es with gas_obs := prefix)
    sa sp s mid (PlaceR (MemoryPlace id path)) (Type ty) rp t /\
   intcall_expr_cont fp ce env (es with gas_obs := prefix) sa s mid sp t /\
   expr_body_pre ce fp.jc_cx env rhs (es with gas_obs := prefix)` by simp[] >>
  drule_at (Pat `eval_target_place`) intcall_aug_place_memory_loaded >>
  simp[] >> disch_then drule_all >> strip_tac >>
  rename1 `read_place _ _ mid = (INL old,mid)` >>
  qexistsl [`old`,`tv`] >> simp[] >>
  irule intcall_aug_place_loaded_prefix >>
  goal_assum (drule_at (Pat `gas_marked_path`)) >>
  goal_assum (drule_at (Pat `intcall_expr_cont`)) >>
  goal_assum (drule_at (Pat `intcall_expr_cont`)) >> simp[] >>
  `expr_sim_inv ce fp.jc_cx env es` by fs[exprSimHypsDefsTheory.expr_body_pre_def] >>
  `intcall_expr_res fp ce env mid sl u /\ ~u.vs_halted /\
    u.vs_current_bb = sl.cs_current_bb /\
    u.vs_inst_idx = LENGTH sl.cs_current_insts` by fs[intcall_expr_cont_def] >>
  `!z. FST rp = Var z ==> not_fresh_at sl z` by
    (fs[target_post_def] >> metis_tac[loweringShapeDefsTheory.not_fresh_at_mono]) >>
  `!z. not_fresh_at sl z ==> not_fresh_at s2 z` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  qpat_x_assum `FST (SND rp) = SOME LocMemory` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  drule_at (Pat `lower_value`) intcall_aug_place_suffix_outcome >>
  disch_then (drule_at (Pat `place_ptr_rel`)) >> simp[] >>
  disch_then drule_all >> CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]
QED

Resume intcall_aug_place_normal_outcome[storage]:
  `loc = slot_loc tr` by fs[target_post_def,place_ptr_rel_def] >>
  `emit_op (if tr then TLOAD else SLOAD) [FST rp] sp = (cur,sl) /\
   emit_void (if tr then TSTORE else SSTORE) [FST rp;result] s3 = ((),sf)` by
    (Cases_on `tr` >> gvs[slot_loc_def]) >>
  `is_word_type ty` by metis_tac[exprSimSourceTheory.word_value_type_word] >>
  `target_post fp.jc_ctx fp.jc_func ce fp.jc_cx (es with gas_obs := prefix)
    sa sp s mid (PlaceR (StoragePlace tr slot tv)) (Type ty) rp t /\
   intcall_expr_cont fp ce env (es with gas_obs := prefix) sa s mid sp t /\
   expr_body_pre ce fp.jc_cx env rhs (es with gas_obs := prefix)` by simp[] >>
  drule_at (Pat `eval_target_place`) intcall_aug_place_storage_loaded >>
  disch_then drule_all >> strip_tac >>
  rename1 `read_place _ _ mid = (INL old,mid)` >>
  qexistsl [`old`,`tv`] >> simp[] >>
  irule intcall_aug_place_loaded_prefix >>
  goal_assum (drule_at (Pat `gas_marked_path`)) >>
  goal_assum (drule_at (Pat `intcall_expr_cont`)) >>
  goal_assum (drule_at (Pat `intcall_expr_cont`)) >> simp[] >>
  `expr_sim_inv ce fp.jc_cx env es` by fs[exprSimHypsDefsTheory.expr_body_pre_def] >>
  `intcall_expr_res fp ce env mid sl u /\ ~u.vs_halted /\
    u.vs_current_bb = sl.cs_current_bb /\
    u.vs_inst_idx = LENGTH sl.cs_current_insts` by fs[intcall_expr_cont_def] >>
  `!z. FST rp = Var z ==> not_fresh_at sl z` by
    (fs[target_post_def] >> metis_tac[loweringShapeDefsTheory.not_fresh_at_mono]) >>
  `!z. not_fresh_at sl z ==> not_fresh_at s2 z` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  qpat_x_assum `FST (SND rp) = SOME loc` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  drule_at (Pat `lower_value`) intcall_aug_place_suffix_outcome >>
  disch_then (drule_at (Pat `place_ptr_rel`)) >> simp[NoAsms] >>
  disch_then drule_all >> CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]
QED

Finalise intcall_aug_place_normal_outcome

Theorem intcall_place_type_value_outcome_prefix[local]:
  (!src id path. p <> ImmutablePlace src id path) /\
  place_type_value cx p es = (INL tv,es) /\
  gas_outcome memory tops (ctx,func) (k tv) (es,s) Q R ==>
  gas_outcome memory tops (ctx,func) (bind (place_type_value cx p) k) (es,s) Q R
Proof
  strip_tac >> drule place_type_value_gas_obs >> strip_tac >>
  fs[gasOutcomeTheory.gas_outcome_def] >> qexists `marks`
  >- (disj1_tac >>
      fs[gasSummaryTheory.gas_summary_at_def] >>
      qexistsl [`res`,`es_end`,`r`] >> simp[] >>
      fs[gasSummaryTheory.gas_marked_exec_def] >>
      simp[vyperStateTheory.bind_def]) >>
  disj2_tac >> rename1 `gas_exempt_cert _ _ _ _ _ _ _ (leaf,fin)` >>
  qexistsl [`err`,`ee`,`leaf`,`fin`] >>
  qpat_x_assum `!tail. _` kall_tac >>
  Cases_on `p`
  >- gvs[vyperStateTheory.place_type_value_def,vyperStateTheory.bind_return,
         vyperStateTheory.return_def]
  >- (rename1 `MemoryPlace id path` >>
      `?entry. lookup_scopes id es.scopes = SOME entry /\
         subscripts_type entry.type path = SOME tv` by
        (qpat_x_assum `gas_exempt_cert _ _ _ _ _ _ _ _` kall_tac >>
         qpat_x_assum `place_type_value _ _ es = _` mp_tac >>
         simp[vyperStateTheory.place_type_value_def,vyperStateTheory.get_scopes_def,
              vyperStateTheory.bind_def,vyperStateTheory.lift_option_type_def,
              vyperStateTheory.return_def,vyperStateTheory.raise_def,
              vyperMiscTheory.option_CASE_rator,AllCaseEqs()] >>
         metis_tac[sumTheory.INL_11,sumTheory.INR_neq_INL]) >>
      pure_rewrite_tac[vyperStateTheory.place_type_value_def,vyperStateTheory.ignore_bind_def,
           vyperStateTheory.bind_assoc] >>
      irule gasExemptCertTheory.gas_exempt_cert_get_scopes >> BETA_TAC >>
      simp[vyperStateTheory.lift_option_type_def,vyperStateTheory.bind_return,
        GSYM vyperStateTheory.ignore_bind_def]) >>
  metis_tac[]
QED

Theorem intcall_aug_place_prepared_outcome:
  intcall_forced_producer fp rhs /\ intcall_frame_ok fp /\
  body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  supported_program fp.jc_tops /\ get_module_code fp.jc_cx NONE = SOME fp.jc_tops /\
  supported_stmt fp.jc_tops bindings (AugAssign ty tg bop rhs) /\
  supported_target_info fp.jc_tops bindings tg = SOME info /\
  supportedExprs$supported_expr fp.jc_tops rhs /\
  calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr rhs) /\
  call_evaluation_safe fp.jc_cx (int_calls_stmt (AugAssign ty tg bop rhs)) /\
  type_stmt env ret_ty (AugAssign ty tg bop rhs) = SOME env /\
  expr_body_pre ce fp.jc_cx env rhs es /\ target_pre ce fp.jc_cx env tg es /\
  stmt_env ce lctx cty (AugAssign ty tg bop rhs) sa = (ce',sf) /\
  compile_get_target_ptr compile_expr ce tg sa = (rp,sp) /\
  fn_has_code sa sf fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  intcall_joint_res fp ce env es sa s /\
  gas_admissible (eval_stmt fp.jc_cx (AugAssign ty tg bop rhs)) (stmt_res_ok lctx) es /\
  (!id path gs mid. eval_target_place fp.jc_cx tg (es with gas_obs := gs) =
    (INL (MemoryPlace id path),mid) ==>
    ((?bt fld. tg = AttributeTarget bt fld) \/ (?bt key. tg = SubscriptTarget bt key))) /\
  gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (eval_base_place fp.jc_cx tg) (es,s)
    (\res ee t. ?pv. res = INL pv /\
      target_post fp.jc_ctx fp.jc_func ce fp.jc_cx es sa sp s ee pv (Type ty) rp t /\
      intcall_expr_cont fp ce env es sa s ee sp t)
    (\res ee r. expr_exit res r) ==>
  gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (eval_stmt fp.jc_cx (AugAssign ty tg bop rhs)) (es,s)
    (\res ff v. res = INL () /\ intcall_joint_res fp ce env ff sf v /\
      ~v.vs_halted /\ v.vs_current_bb = sf.cs_current_bb /\
      v.vs_inst_idx = LENGTH sf.cs_current_insts /\
      (!z w. not_fresh_at sa z /\ lookup_var z s = SOME w ==> lookup_var z v = SOME w) /\
      (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP v.vs_allocas aid = SOME b) /\
      s.vs_alloca_next <= v.vs_alloca_next) (intcall_stmt_exit fp)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  simp[Once vyperInterpreterTheory.evaluate_def] >>
  simp[Once vyperInterpreterTheory.evaluate_def,vyperStateTheory.bind_assoc] >>
  irule exprSimSubscriptMapTheory.gas_outcome_bind_result_exec >>
  goal_assum (drule_at (Pat `gas_outcome`)) >> simp[] >>
  conj_tac >- (rpt strip_tac >>
    Cases_on `res` >> fs[exprSimDefsTheory.expr_exit_def,intcall_stmt_exit_def] >>
    disj1_tac >> metis_tac[stmtSimPropsTheory.expr_exit_INR_type]) >>
  rpt strip_tac >> gvs[] >>
  `?p. v = PlaceR p` by
    (Cases_on `v` >> fs[target_post_def,place_ptr_rel_def]) >> gvs[] >>
  simp[vyperStateTheory.get_place_def,vyperStateTheory.bind_def,vyperStateTheory.return_def] >>
  `!tail. eval_target_place fp.jc_cx tg
    (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
    (INL p,mid with gas_obs := tail)` by
    (fs[gasSummaryTheory.gas_marked_exec_def] >>
     simp[Once vyperInterpreterTheory.evaluate_def,vyperStateTheory.bind_def,
          vyperStateTheory.get_place_def,vyperStateTheory.return_def]) >>
  drule_all stmtSimAugAssignPlaceTheory.aug_place_code_parts >> strip_tac >>
  gvs[]
  >- (Cases_on `p` >> fs[target_post_def,place_ptr_rel_def]) >>
  suspend "normal"
QED

Resume intcall_aug_place_prepared_outcome[normal]:
  `cs_extends sa s0` by
    (qspecl_then [`tg`,`ce`,`sa`] mp_tac stmtLoweringMonoTheory.ci_mono_compile_get_target_ptr >>
     simp[exprLoweringPropsTheory.ci_mono_def]) >>
  `cs_extends s0 s1 /\ cs_extends s1 s2 /\ cs_extends s2 s3 /\ cs_extends s3 sf` by
    metis_tac[stmtSimAugAssignPlaceTheory.aug_place_emit_op_grows,
      stmtSimAugAssignPlaceTheory.aug_place_emit_void_grows,
      cj 2 exprLoweringPropsTheory.compile_expr_grows,exprLoweringPropsTheory.compile_binop_grows] >>
  `fn_has_code s0 s1 fp.jc_func /\ fn_has_code s1 s2 fp.jc_func /\
   fn_has_code s2 s3 fp.jc_func /\ fn_has_code s3 sf fp.jc_func` by
    metis_tac[fragExecTheory.fn_has_code_mid,compileEnvTheory.cs_extends_trans,
      compileEnvTheory.cs_extends_refl] >>
  `sa.cs_next_var <= s0.cs_next_var /\ s0.cs_next_var <= s1.cs_next_var /\
   s1.cs_next_var <= s2.cs_next_var` by
    (qspecl_then [`tg`,`ce`,`sa`] mp_tac stmtLoweringMonoTheory.ci_mono_compile_get_target_ptr >>
     qspecl_then [`case loc of LocStorage => SLOAD | LocTransient => TLOAD | _ => MLOAD`,
       `[FST r]`,`s0`] mp_tac exprLoweringPropsTheory.ci_mono_emit_op >>
     simp[exprLoweringPropsTheory.ci_mono_def] >>
     metis_tac[cj 2 exprLoweringPropsTheory.compile_expr_grows]) >>
  drule stmtSimAugAssignPlaceTheory.aug_place_typing >> strip_tac >>
  `expr_sim_inv ce fp.jc_cx env es /\ ce_locals_declared ce env` by
    fs[intcall_joint_res_def,intcall_expr_res_def] >>
  `env.type_defs = get_tenv fp.jc_cx` by
    fs[exprSimHypsDefsTheory.expr_sim_inv_def,
       vyperTypeInvariantsTheory.env_consistent_def,
       vyperTypeInvariantsTheory.env_context_consistent_def] >>
  `type_bits ty MOD 8 = 0 /\
   IS_SOME (evaluate_type (get_tenv fp.jc_cx) (expr_type rhs))` by
    metis_tac[vyperTypeSystemTheory.assignable_type_well_formed,
      stmtSimAugAssignTheory.well_formed_type_bits,vyperTypeSystemTheory.well_formed_type_def] >>
  `ce.ce_alloca_locals` by fs[bodySimTheory.body_inv_def] >>
  `~fp.jc_cx.txn.is_static` by
    fs[intcall_joint_res_def,intcall_expr_res_def,
       exprSimHypsDefsTheory.expr_sim_inv_def,exprLoweringPropsTheory.stmt_state_rel_def,
       loweringStateRelDefsTheory.state_rel_def] >>
  `target_indices_pre ce fp.jc_cx env tg` by fs[targetPlaceSimTheory.target_pre_def] >>
  suspend "normal_join"
QED

Resume intcall_aug_place_prepared_outcome[normal_join]:
  `target_post fp.jc_ctx fp.jc_func ce fp.jc_cx es sa s0 s
     (mid with gas_obs := []) (PlaceR p) (Type ty) r t` by simp[] >>
  qpat_x_assum `target_post _ _ _ _ _ _ _ _ mid _ _ _ _` kall_tac >>
  drule_at (Pat `lower_value`) intcall_aug_place_normal_outcome >>
  disch_then (drule_at (Pat `target_post`)) >>
  disch_then (drule_at (Pat `supported_stmt`)) >>
  disch_then (drule_at (Pat `emit_void`)) >>
  disch_then (drule_at (Pat `type_stmt`)) >>
  disch_then (drule_at (Pat `supported_target_info`)) >>
  disch_then (drule_at (Pat `emit_op`)) >>
  disch_then (drule_at (Pat `gas_admissible`)) >>
  disch_then (qspec_then `gas_explicit marks s.vs_gas_readings` mp_tac) >>
  impl_tac >- (simp[] >> Cases_on `p` >> simp[] >>
    first_x_assum (qspec_then `[]` mp_tac) >>
    metis_tac[]) >>
  strip_tac >>
  `!src id path. p <> ImmutablePlace src id path` by
    (Cases_on `p` >> fs[target_post_def,place_ptr_rel_def]) >>
  simp[vyperStateTheory.bind_return] >>
  irule exprSimExtract32CountedTheory.extract32_outcome_read_prefix >>
  qexistsl [`mid with gas_obs := []`,`t`,`old`] >>
  reverse conj_tac
  >- (simp[gasSummaryTheory.gas_marked_exec_def,
           fragGasModeTheory.gas_marked_path_def] >>
      conj_tac
      >- (gen_tac >>
          `mid with <|outcomes := mid.outcomes; gas_obs := tail|> =
             mid with gas_obs := tail` by
            simp[vyperStateTheory.evaluation_state_component_equality] >>
          mp_tac (bodyIntCallSourceFrameTheory.read_place_outcomes |>
            Q.INST [`cx` |-> `fp.jc_cx`, `p` |-> `p`,
              `es` |-> `mid with gas_obs := []`,
              `os` |-> `mid.outcomes`, `gs` |-> `tail`]) >>
          simp[vyperStateTheory.evaluation_state_component_equality]) >>
      irule (cj 1 fragGasPathTheory.gas_path_rules) >>
      fs[intcall_expr_cont_def,intcall_expr_res_def]) >>
  simp[NoAsms] >>
  irule intcall_place_type_value_outcome_prefix >>
  simp[vyperStateTheory.bind_assoc] >>
  qpat_x_assum `gas_outcome _ _ _ (bind (bind _ _) _) _ _ _` mp_tac >>
  simp[vyperStateTheory.bind_assoc] >> metis_tac[]
QED

Finalise intcall_aug_place_prepared_outcome

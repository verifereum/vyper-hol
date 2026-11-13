(* Concrete introductions for current-value snapshot cells. *)
Theory exprExtRequestSnapshotCellIntro
Ancestors
  exprExtRequestSnapshotStoreInterface exprExtRequestSnapshotWord
  exprExtRequestSnapshotNonword exprExtRequestTypedCells
  exprExtRequestHistoryCompose exprLowering gasSummary fragGasMode
  exprExtRequestTupleCapturedHead exprExtRequestHistory compileEnv fragExec fragGasPath
  exprExtRequestTupleFold exprExtRequestReadProbe exprExtRequestStrongCapture
  exprExtRequestJointUnwrap loweringPosts valueCopyBytes exprSafeOperand exprOperandVar

Theorem extrequest_snapshot_cell_word_intro:
  is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_size tv < dimword (:256) /\
  expr_val_rel cx ty v op tb /\ safe_operand cb op ==>
  extrequest_snapshot_cell ctx func ce cx eb cb tb (StackValue ty op,ty,tv,v)
Proof
  strip_tac >> simp[extrequest_snapshot_cell_def, unwrap_value_def, comp_return_def] >>
  rpt strip_tac >> gvs[] >>
  `expr_val_rel cx ty v op s /\ safe_operand sm op` by
    (drule_all extrequest_snapshot_word_history >> simp[]) >>
  qexists_tac `s` >> simp[extrequest_history_frame_refl, gas_marked_path_def,
    frag_exec_refl] >> metis_tac[gas_path_rules]
QED

Theorem extrequest_snapshot_cell_nonword_intro:
  expr_body_pre ce cx env e es /\ ~expr_has_effect e /\
  compile_expr ce cty e sa = (vv,sc) /\
  extrequest_strong_capture ctx func ce cx e r vv eb cb tb /\
  stmt_state_rel ctx func ce cx eb tb /\
  read_result cx r eb = (INL v,eb) /\
  value_runtime_typed env (expr_type e) v /\
  value_runtime_typed env (lowered_value_type ce e) v /\
  ~is_word_type (vv_type (ext_call_arg_value (lowered_value_type ce e) vv)) ==>
  ?tv. extrequest_snapshot_cell ctx func ce cx eb cb tb
    (ext_call_arg_value (lowered_value_type ce e) vv,lowered_value_type ce e,tv,v)
Proof
  strip_tac >>
  `?tv. extrequest_tuple_cell ctx func ce cx eb cb tb eb
    (e,r,vv,lowered_value_type ce e,tv,v)` by
    (irule extrequest_typed_cell >> metis_tac[]) >>
  `unwrap_value ce (ext_call_arg_value (lowered_value_type ce e) vv) =
    unwrap_value ce vv` by
    (fs[exprSimHypsDefsTheory.expr_body_pre_def] >>
     drule_all extrequest_snapshot_nonword_endpoint >> simp[]) >>
  qexists_tac `tv` >>
  fs[extrequest_tuple_cell_def] >> gvs[] >>
  simp[extrequest_snapshot_cell_def] >> rpt strip_tac >>
  `extrequest_read_frame cx eb ee` by fs[extrequest_history_frame_def] >>
  `read_result cx r ee = (INL v,ee)` by
    (drule extrequest_read_result_frame >> simp[]) >>
  qpat_x_assum `extrequest_strong_capture _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[extrequest_strong_capture_def] >> strip_tac >>
  `stmt_state_rel ctx func ce cx ec tc` by fs[vv_post_def] >>
  `extrequest_history_frame ce cx ec sc' tc ee sm s` by
    (drule_all extrequest_history_frame_trans >> simp[]) >>
  drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)
    extrequest_joint_unwrap_read >> simp[] >>
  disch_then (qspecl_then [`s`, `sm`, `su`, `op`, `ee`] mp_tac) >>
  simp[] >> strip_tac >>
  `ee with gas_obs := [] = ee` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  `v' = v` by
    (gvs[gas_marked_exec_def] >>
     qpat_x_assum `!tail. read_result _ _ _ = _`
       (qspec_then `[]` mp_tac) >>
     simp[vyperStateTheory.evaluation_state_component_equality]) >>
  `stmt_state_rel ctx func ce cx ee u /\
    expr_val_rel cx (expr_type e) v op u` by gvs[expr_post_def] >>
  `expr_val_rel cx (lowered_value_type ce e) v op u` by
    (Cases_on `lowered_value_type ce e = expr_type e`
     >- gvs[] >>
     `~is_word_type (lowered_value_type ce e) /\ ~is_word_type (expr_type e)` by
       metis_tac[is_bytestring_word_type] >>
     fs[expr_val_rel_def] >> simp[expr_val_rel_def] >>
     irule bytestring_val_in_memory_transfer >>
     (conj_tac >- simp[]) >>
     qexistsl_tac [`expr_type e`, `lowered_value_type ce e`, `get_tenv cx`] >>
     fs[optionTheory.IS_SOME_EXISTS] >> metis_tac[]) >>
  `safe_operand sm (vv_operand vv)` by
    (`sc'.cs_next_var <= sm.cs_next_var` by
       (fs[extrequest_history_frame_def] >> decide_tac) >>
     irule safe_operand_mono >> qexists_tac `sc'` >>
     Cases_on `vv` >> gvs[contextTheory.vv_operand_def]) >>
  `safe_operand su op` by
    (fs[safe_operand_def] >> conj_tac
     >- (rpt strip_tac >> irule compiler_unwrap_value_var >>
         qexistsl_tac [`ce`, `op`, `sm`, `vv`] >> simp[] >>
         Cases_on `vv` >> gvs[contextTheory.vv_operand_def]) >>
     drule_at (Pat `unwrap_value _ _ _ = _`) unwrap_value_not_label >> simp[]) >>
  `~u.vs_halted` by
    (fs[gas_marked_exec_def, gas_marked_path_def] >>
     metis_tac[extrequest_head_path_nonhalting]) >>
  qexists_tac `u` >> fs[gas_marked_exec_def] >> metis_tac[]
QED

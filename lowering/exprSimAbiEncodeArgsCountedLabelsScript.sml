Theory exprSimAbiEncodeArgsCountedLabels
Ancestors
  fragGasMode fragGasPath abiArgsObservation venomExecProofs gasOutcome gasSummary gasExemptCert exprSimDefs
  exprSimAbiEncodeArgsLabelReplay exprSimWordArgs loweringPosts

Theorem abi_args_gas_edge_labels[local]:
  gas_path_edge ctx func s n (OK t) ==> t.vs_labels = s.vs_labels
Proof
  rw[gas_path_edge_def] >> gvs[fragExecTheory.exit_result_def]
  >> imp_res_tac step_inst_preserves_labels_always
  >> imp_res_tac venomExecPropsTheory.eval_phis_preserves_labels
  >> gvs[venomStateTheory.jump_to_def]
  >> metis_tac[step_inst_preserves_labels_always]
QED

Theorem abi_args_gas_path_labels[local]:
  !ctx func s n r. gas_path ctx func s n r ==>
    !t. r = OK t ==> t.vs_labels = s.vs_labels
Proof
  ho_match_mp_tac gas_path_ind >> rpt conj_tac >> rpt strip_tac >> gvs[]
  >- metis_tac[abi_args_gas_edge_labels]
  >> gvs[fragExecTheory.exit_result_def]
QED

Theorem abi_args_marked_path_labels:
  gas_marked_path F ctx func s n (OK t) ==> t.vs_labels = s.vs_labels
Proof
  metis_tac[gas_marked_path_exec, abi_args_gas_path_labels]
QED

(* This probe deliberately requires stream-independent success.  Admissibility
   alone is not a replacement for this premise. *)
Theorem abi_args_no_read_outcome_success:
  (!tail. source (es with gas_obs := tail) =
    (INL v, ee with gas_obs := tail)) /\
  gas_outcome F tops (ctx,func) source (es,s0) Q
    (\res fin r. expr_exit res r) ==>
  ?t. Q (INL v) (ee with gas_obs := []) t /\
      t.vs_labels = s0.vs_labels
Proof
  strip_tac >>
  gvs[gas_outcome_def, gas_summary_at_def]
  >- (gvs[gas_marked_exec_def] >>
      first_x_assum (qspec_then `[]` mp_tac) >>
      simp[] >> strip_tac >> gvs[] >>
      qpat_x_assum `ee with gas_obs := _ = _`
        (mp_tac o Q.AP_TERM `\st. st with gas_obs := []`) >>
      simp[] >> strip_tac >>
      metis_tac[abi_args_marked_path_labels])
  >- (gvs[gas_marked_exec_def] >>
      first_x_assum (qspec_then `[]` mp_tac) >> simp[] >>
      strip_tac >> gvs[]) >>
  drule gas_exempt_cert_execution >>
  simp[vyperStateTheory.ignore_bind_def, vyperStateTheory.bind_def,
       vyperStateTheory.return_def]
QED

Theorem abi_args_counted_label_success:
  expr_sim ctx func ce cx ty e es /\
  lower_value compile_expr ce ty e sa = (Label l,sb) /\
  bind (eval_expr cx e) (read_result cx) es = (INL v,ee) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  stmt_state_rel ctx func ce cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. expr_post ctx func ce cx e es sa sb s0 (ee with gas_obs := []) v (Label l) t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      t.vs_labels = s0.vs_labels
Proof
  strip_tac >>
  drule_all expr_sim_apply >> strip_tac >>
  drule_all abi_args_lower_label_replay >> strip_tac >>
  drule_all abi_args_no_read_outcome_success >>
  simp[] >> metis_tac[]
QED

Theorem abi_args_counted_label_observe:
  expr_sim ctx func ce cx ty e es /\
  lower_value compile_expr ce ty e sa = (Label l,sb) /\
  bind (eval_expr cx e) (read_result cx) es = (INL v,ee) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  stmt_state_rel ctx func ce cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. stmt_state_rel ctx func ce cx ee t /\
      expr_val_rel cx (post_value_type ce e) v (Label l) t /\
      expr_val_at ce cx (post_value_type ce e) sa sb ee v (Label l) t /\
      t.vs_labels = s0.vs_labels
Proof
  strip_tac >> drule_all abi_args_counted_label_success >>
  simp[expr_post_def, expr_val_at_def] >> strip_tac >>
  goal_assum (drule_at Any) >> simp[]
QED

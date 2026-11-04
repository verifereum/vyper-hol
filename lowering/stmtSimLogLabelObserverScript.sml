(* Successful straight expression observation from a label-erased entry. *)
Theory stmtSimLogLabelObserver
Ancestors
  stmtSimLogLabelApplicability stmtSimLogLabelStraight entrySinkExtraction
  exprSim exprLoweringProps abiDecodeStaticProps fragExec
  venomExecProps venomExecSemantics venomState finite_map list

Theorem log_straight_run_labels[local]:
  run_inst_seq insts s = OK t /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) insts ==>
  t.vs_labels = s.vs_labels
Proof
  strip_tac >> irule run_inst_seq_preserves_field >>
  first_assum (irule_at Any) >> rpt strip_tac >>
  `i.inst_opcode <> INVOKE` by fs[EVERY_MEM] >>
  `step_inst 0 ARB i ss1 = OK ss2` by simp[step_inst_non_invoke] >>
  drule step_inst_preserves_labels_always >> simp[]
QED

Theorem log_expr_sim_straight_erased_post:
  expr_sim ctx func ce cx ty e es /\
  lower_value compile_expr ce ty e sa = (op,sb) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,es') /\
  dec_straight sa sb /\ fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ stmt_state_rel ctx func ce cx es s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. expr_post ctx func ce cx e es sa sb (s0 with vs_labels := FEMPTY) es' v op t /\
      t.vs_labels = FEMPTY
Proof
  strip_tac >> drule_all log_expr_sim_erased_fragment >> strip_tac >>
  drule_at (Pat `frag_exec`) frag_exec_straight_run >>
  disch_then (qspec_then `s0 with vs_labels := FEMPTY` mp_tac) >>
  simp[] >> strip_tac >>
  rename1 `run_inst_seq _ _ = OK u` >>
  `u.vs_labels = FEMPTY` by
    (drule log_straight_run_labels >>
     fs[dec_straight_def]) >>
  qexists `u with vs_inst_idx := LENGTH sb.cs_current_insts` >> simp[]
QED

Theorem log_expr_sim_label_impossible:
  expr_sim ctx func ce cx ty e es /\
  lower_value compile_expr ce ty e sa = (Label lab,sb) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,es') /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ stmt_state_rel ctx func ce cx es s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==> F
Proof
  strip_tac >>
  `dec_straight sa sb` by
    (drule log_lower_compile_expr_label_straight >> simp[]) >>
  drule_all log_expr_sim_straight_erased_post >> strip_tac >>
  gvs[expr_post_def, expr_val_rel_def, eval_operand_def]
QED

Theorem log_expr_sim_not_label:
  expr_sim ctx func ce cx ty e es /\
  lower_value compile_expr ce ty e sa = (op,sb) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,es') /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ stmt_state_rel ctx func ce cx es s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==> !lab. op <> Label lab
Proof
  rpt strip_tac >> gvs[] >> drule_all log_expr_sim_label_impossible >> simp[]
QED

(* A log argument's expression fragment run from a label-erased entry. *)
Theory stmtSimLogLabelApplicability
Ancestors
  exprSim
  exprLoweringProps compileEnv fragExec
  venomExecSemantics venomState venomMemDefs finite_map

Theorem log_stmt_state_rel_erase_labels:
  stmt_state_rel ctx func ce cx es s ==>
  stmt_state_rel ctx func ce cx es (s with vs_labels := FEMPTY)
Proof
  strip_tac >>
  fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def,
       local_region_def, local_backed_def, lookup_var_def,
       storage_rel_def, transient_rel_def, accounts_rel_def,
       immutables_rel_def, logs_rel_def, alloca_inv_def,
       alloca_room_def, pending_alloca_size_def, immutable_alloca_sep_def,
       contract_storage_def, contract_transient_def,
       allocas_non_overlapping_def, alloca_next_valid_def, fmp_room_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem log_expr_sim_erased_fragment:
  expr_sim ctx func ce cx ty e es /\
  lower_value compile_expr ce ty e sa = (op,sb) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,es') /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ stmt_state_rel ctx func ce cx es s0 ==>
  frag_exec ctx sa sb (\s. s = (s0 with vs_labels := FEMPTY))
    (expr_post ctx func ce cx e es sa sb
      (s0 with vs_labels := FEMPTY) es' v op) (\r. F)
Proof
  strip_tac >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _` mp_tac >>
  simp[expr_sim_def, expr_res_ok_def] >> strip_tac >>
  first_x_assum drule_all >>
  disch_then (qspec_then `s0 with vs_labels := FEMPTY` mp_tac) >>
  simp[expr_res_ok_def] >> strip_tac >>
  drule frag_exec_weaken >> disch_then irule >>
  simp[log_stmt_state_rel_erase_labels]
QED

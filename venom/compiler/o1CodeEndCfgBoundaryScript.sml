(* Value-sensitive boundary for unchanged SimplifyCFG instructions.
   scfg_payload is the concrete control-coordinate relation, unlike mem_corr. *)
Theory o1CodeEndCfgBoundary
Ancestors
  simplifyCfgControl memSafeRun

Theorem scfg_payload_code_data:
  scfg_payload s t ==>
  s.vs_code = t.vs_code /\ s.vs_data_section = t.vs_data_section
Proof
  rewrite_tac[scfg_payload_def] >> strip_tac >>
  qpat_x_assum `t = _` SUBST1_TAC >> simp[scfg_ctrl_def]
QED

Theorem scfg_payload_dload_in_section:
  scfg_payload s t ==>
  (inst_dload_in_section inst s <=> inst_dload_in_section inst t)
Proof
  strip_tac >>
  `!op. eval_operand op s = eval_operand op t` by
    metis_tac[scfg_payload_operand] >>
  drule scfg_payload_code_data >> strip_tac >>
  simp[inst_dload_in_section_def]
QED

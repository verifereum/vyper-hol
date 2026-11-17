(* Value-sensitive boundary for unchanged SimplifyCFG instructions.
   scfg_payload is the concrete control-coordinate relation, unlike mem_corr. *)
Theory o1CodeEndCfgBoundary
Ancestors
  simplifyCfgControl memSafeRun stateFrame

Theorem scfg_payload_dload_in_section:
  scfg_payload s t ==>
  (inst_dload_in_section inst s <=> inst_dload_in_section inst t)
Proof
  strip_tac >>
  `!op. eval_operand op s = eval_operand op t` by
    metis_tac[scfg_payload_operand] >>
  drule scfg_payload_frame >>
  disch_then (mp_tac o AP_TERM ``\s. (s.vs_code,s.vs_data_section)``) >>
  simp[execution_frame_def] >> strip_tac >>
  simp[inst_dload_in_section_def]
QED

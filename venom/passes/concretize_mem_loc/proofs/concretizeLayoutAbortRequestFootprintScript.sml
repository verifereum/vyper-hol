(* Base-instruction aborts retain the request history.  External calls and
   creates can append requests only on their normally returning paths; their
   abort guards execute before those requests are issued. *)
Theory concretizeLayoutAbortRequestFootprint
Ancestors
  venomExecSemantics venomState opcodeClass passSharedFrame

Theorem step_inst_base_abort_requests:
  step_inst_base inst s = Abort a post ==>
  post.vs_requests = s.vs_requests
Proof
  strip_tac >>
  drule step_inst_base_abort_opcodes >> strip_tac >>
  TRY (drule step_inst_base_static_write_abort >> simp[] >> strip_tac >>
       gvs[halt_state_def, set_returndata_def]) >>
  qpat_x_assum `step_inst_base inst s = Abort a post` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[venomInstTheory.opcode_case_def] >>
  simp[AllCaseEqs(), exec_create_abort_iff] >>
  rpt strip_tac >>
  gvs[halt_state_def, revert_state_def, set_returndata_def]
QED

(* Observation interface for extracting execution from continuation simulation.
   STOP hides haltedness and return data, but retains the encoder observations. *)
Theory abiEncoderObserver
Ancestors
  abiDecoderLoop fragExec venomState venomExecSemantics emitHelper venomInst

Definition stop_view_def:
  stop_view s = halt_state (s with vs_returndata := [])
End

Theorem stop_view_fields:
  stop_view s = stop_view t ==>
  s.vs_memory = t.vs_memory /\ s.vs_vars = t.vs_vars /\
  s.vs_allocas = t.vs_allocas /\ s.vs_alloca_next = t.vs_alloca_next /\
  s.vs_accounts = t.vs_accounts /\ s.vs_transient = t.vs_transient /\
  s.vs_logs = t.vs_logs /\ s.vs_requests = t.vs_requests /\
  s.vs_labels = t.vs_labels
Proof
  simp[stop_view_def, halt_state_def, venom_state_component_equality]
QED

Theorem stop_view_operand:
  stop_view s = stop_view t ==> eval_operand op s = eval_operand op t
Proof
  strip_tac >> drule stop_view_fields >> strip_tac >>
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def]
QED

Theorem run_from_stop_view:
  lookup_block t.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME (mk_inst id STOP [] []) ==>
  run_from 0 ctx fn t = Halt (stop_view t)
Proof
  strip_tac >> rewrite_tac[stop_view_def] >> irule run_from_halt >>
  qexistsl_tac [`bb`, `mk_inst id STOP [] []`] >>
  simp[Once step_inst_base_def, mk_inst_def]
QED

Theorem abi_decode_sim_stop_run:
  abi_decode_sim ctx fn s t /\
  lookup_block t.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME (mk_inst id STOP [] []) ==>
  ?fuel. run_from fuel ctx fn s = Halt (stop_view t)
Proof
  strip_tac >> drule_all run_from_stop_view >> strip_tac >>
  fs[abi_decode_sim_def] >>
  qpat_x_assum `!fuel. _` (qspec_then `0` mp_tac) >> simp[]
QED

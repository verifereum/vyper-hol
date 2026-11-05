(* Small checked interfaces for external return paths. *)
Theory extRetCountedProbePtr
Ancestors
  fragGasPathPtr fragExecPtr bodyPtrDefs ptrSafeRun ptrDiscipline
  venomExecSemantics venomInst venomState gasCount fragExec

Theorem stop_gas_path_ptr:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id STOP [] []) /\
  stor_taint_ok cx tn s /\ ~ctx_has_dalloca ctx ==>
  gas_path_ptr (cx_dead cx) 0 ctx fn PG G tn s 0 G tn
    (Halt (halt_state (s with vs_returndata := [])))
Proof
  strip_tac >>
  `ptr_inst_ok (cx_dead cx) 0 0 ctx fn G tn
     (mk_inst id STOP [] []) s` by simp[ptr_inst_ok_stop] >>
  `step_inst_base (mk_inst id STOP [] []) s =
     Halt (halt_state (s with vs_returndata := []))` by
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >> simp[mk_inst_def]) >>
  irule (cj 3 gas_path_ptr_rules) >>
  simp[exit_result_def] >>
  simp[gas_path_ptr_edge_def] >>
  qexists_tac `0` >>
  simp[step_inst_non_invoke, Once step_inst_base_def, mk_inst_def,
       gas_count_step_def, ptr_safe_step_def, ptr_inst_ok_stop,
       exit_result_def]
QED

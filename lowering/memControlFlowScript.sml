(* No-PHI CFG edges transfer both execution and memory safety. *)
Theory memControlFlow
Ancestors
  memContinuation fragExec memSafeRun venomExecSemantics

Theorem mem_cont_sim_edge:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  (!f. exec_block f ctx bb s = OK t) /\
  (!f. mem_safe_block f ctx bb s) /\ ~t.vs_halted /\
  lookup_block t.vs_current_bb fn.fn_blocks = SOME next_bb /\
  phi_prefix_length next_bb.bb_instructions = 0 /\ t.vs_inst_idx = 0 ==>
  mem_cont_sim ctx fn s t
Proof
  strip_tac >> rw[mem_cont_sim_def] >> qexists_tac `SUC fuel` >>
  conj_tac
  >- (simp[run_from_def] >>
      drule_all run_blocks_run_from_no_phi >> simp[run_from_def]) >>
  strip_tac >> simp[mem_safe_run_def] >>
  `eval_phis t next_bb.bb_instructions = OK t` by
    simp[eval_phis_no_phi] >>
  drule_all mem_safe_blocks_run >> simp[]
QED

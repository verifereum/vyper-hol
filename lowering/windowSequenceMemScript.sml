(* Exact straight-line window execution with memory-safe continuation. *)
Theory windowSequenceMem
Ancestors
  abiEncoderWindowSequence memContinuation fragExecMem fragExec
  exprLoweringProps emitHelperProps venomState fragGasSeqMem rich_list

Theorem window_seq_mem_fragment[local]:
  window_seq st st' s t /\
  run_inst_seq_mem_ok (emitted_insts st st') s ==>
  frag_exec_mem ctx st st' (\u. u = s)
    (\u. u = (t with vs_inst_idx := LENGTH st'.cs_current_insts)) (K F)
Proof
  strip_tac >> irule frag_exec_mem_run_inst_seq >>
  fs[window_seq_def, inst_extends_def] >> rpt strip_tac >> gvs[] >>
  disj1_tac >> qexists_tac `t` >> simp[]
QED

Theorem window_seq_counted_mem:
  window_seq st st' s t /\
  run_inst_seq_mem_ok (emitted_insts st st') s /\
  fn_has_code st st' func /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  gas_path_mem ctx func s
    (LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts st st')))
    (OK (t with vs_inst_idx := LENGTH st'.cs_current_insts))
Proof
  strip_tac >> fs[window_seq_def, inst_extends_def] >>
  `?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
      DROP s.vs_inst_idx bb.bb_instructions = emitted_insts st st' ++ rest` by
    (gvs[fn_has_code_def, IS_PREFIX_APPEND] >> qexists_tac `l` >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> REFL_TAC) >>
  `isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[IS_PREFIX_APPEND] >>
  drule_all run_inst_seq_gas_path_mem >> simp[]
QED

Theorem window_seq_mem_cont:
  window_seq st st' s t /\
  run_inst_seq_mem_ok (emitted_insts st st') s /\
  fn_has_code st st' func /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  mem_cont_sim ctx func s (t with vs_inst_idx := LENGTH st'.cs_current_insts)
Proof
  strip_tac >>
  drule_all window_seq_mem_fragment >>
  disch_then (qspec_then `ctx` assume_tac) >>
  drule mem_cont_sim_from_fragment >>
  disch_then (qspec_then `s` mp_tac) >> simp[]
QED

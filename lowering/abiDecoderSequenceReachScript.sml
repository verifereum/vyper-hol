(* Generic straight-line execution reach, independent of encoder correctness. *)
Theory abiDecoderSequenceReach
Ancestors
  abiDecoderLoop abiDecoderContract fragExec emitHelperProps compileEnv
  venomExecSemantics venomState venomInst list rich_list

Theorem abi_decoder_run_sequence_reach:
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\ inst_extends st st' /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts st st') /\
  fn_has_code st st' func /\ run_inst_seq (emitted_insts st st') initial = OK encoded /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. t = encoded with vs_inst_idx := LENGTH st'.cs_current_insts /\
    t.vs_current_bb = st'.cs_current_bb /\ t.vs_inst_idx = LENGTH st'.cs_current_insts /\
    abi_decode_sim ctx func initial t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `isPREFIX st.cs_current_insts st'.cs_current_insts` by
    (gvs[inst_extends_def, IS_PREFIX_APPEND] >> metis_tac[]) >>
  `frag_exec ctx st st' (\s. s = initial)
    (\t. t = encoded with vs_inst_idx := LENGTH st'.cs_current_insts) (K F)` by
    (irule frag_exec_run_inst_seq >> simp[] >> qexists_tac `encoded` >> simp[]) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[]
QED

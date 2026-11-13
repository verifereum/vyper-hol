(* Shared load phase: a single safe, framed, memory-preserving endpoint. *)
Theory abiEncoderWindowLoadMemoryMem
Ancestors
  abiEncoderWindowSequenceFrameMem abiEncoderWindowMemFrame
  abiEncoderWindowCursor abiEncoderWindowPhase abiEncoderWindowSequence
  windowSequenceMem allocaFootprint emitHelperProps emitHelper instMemFrontier
  abiDecoderVarSequence venomState venomExecSemantics venomInst fragExec list

Theorem window_cursor_load_phase_memory_mem:
  emit_op MLOAD [ptr_op] st = (out,en) /\
  eval_operand ptr_op s = SOME (n2w b) /\ b < dimword (:256) /\
  b+32 <= s.vs_alloca_next /\
  fn_has_code st en func /\ alloca_inv s /\ alloca_room ctx func s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. window_phase ctx func st en {} [] s t /\
    eval_operand out t = SOME (mload b s) /\
    (!x. out = Var x ==> not_fresh_at en x) /\ t.vs_labels = s.vs_labels /\
    mem_cont_sim ctx func s t /\
    (fn_inst_ids_distinct func ==> window_mem_frame ctx func s t) /\
    t.vs_memory = s.vs_memory
Proof
  strip_tac >> drule_all window_cursor_load_sequence >> strip_tac >>
  `window_seq st en s t /\ t.vs_memory = s.vs_memory` by fs[window_pure_seq_def] >>
  `run_inst_seq_mem_ok (emitted_insts st en) s` by
    (drule emit_mload_mem_ok >> disch_then irule >> simp[]) >>
  `mem_cont_sim ctx func s (t with vs_inst_idx := LENGTH en.cs_current_insts)` by
    metis_tac[window_seq_mem_cont] >>
  `fn_inst_ids_distinct func ==>
   window_mem_frame ctx func s (t with vs_inst_idx := LENGTH en.cs_current_insts)` by
    (strip_tac >> irule window_seq_mem_frame >> simp[] >> qexists `st` >> simp[] >>
     drule emitted_insts_emit_op >> simp[mk_inst_def, abi_decoder_reentry_opcode_def]) >>
  qexists `t with vs_inst_idx := LENGTH en.cs_current_insts` >>
  (conj_tac >- metis_tac[window_pure_seq_phase]) >>
  simp_tac (srw_ss()) [eval_operand_def, lookup_var_def] >>
  `t.vs_labels = s.vs_labels` by metis_tac[window_seq_labels] >>
  Cases_on `out` >> fs[eval_operand_def, lookup_var_def]
QED

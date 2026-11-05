(* Exact-endpoint safety companions for primitive window phases. *)
Theory windowPhaseMem
Ancestors
  abiEncoderWindowPhase windowSequenceMem allocaFootprint instMemFrontier
  abiEncoderWindowCursor abiEncoderWindowSequence abiEncoderWindowContract
  abiEncoderWindowLeaves emitHelperProps emitHelper compileEnv
  venomState venomExecSemantics venomInst fragExec list words

Theorem window_emit_no_ranges_mem[local]:
  emit_op opc ops st = (out,en) /\ (opc = ADD \/ opc = ALLOCA) ==>
  run_inst_seq_mem_ok (emitted_insts st en) s
Proof
  strip_tac >> drule emit_op_mem_ok >> disch_then irule >>
  simp[] >> irule below_frontier_no_ranges >> gvs[mk_inst_def]
QED

Theorem window_emit_add_phase_mem:
  emit_op ADD [lhs;rhs] st = (out,en) /\
  eval_operand lhs s = SOME a /\ eval_operand rhs s = SOME b /\
  fn_has_code st en func /\ alloca_inv s /\ alloca_room ctx func s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. window_phase ctx func st en {} [] s t /\
    eval_operand out t = SOME (a+b) /\
    (!x. out = Var x ==> not_fresh_at en x) /\ t.vs_labels = s.vs_labels /\
    mem_cont_sim ctx func s t
Proof
  strip_tac >> drule_all window_emit_add_pure >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts st en) s` by
    metis_tac[window_emit_no_ranges_mem] >>
  `mem_cont_sim ctx func s (t with vs_inst_idx := LENGTH en.cs_current_insts)` by
    metis_tac[window_seq_mem_cont, window_pure_seq_def] >>
  qexists_tac `t with vs_inst_idx := LENGTH en.cs_current_insts` >>
  (conj_tac >- metis_tac[window_pure_seq_phase]) >>
  simp_tac (srw_ss()) [eval_operand_def, lookup_var_def] >>
  `t.vs_labels = s.vs_labels` by
    metis_tac[window_pure_seq_def, window_seq_labels] >>
  Cases_on `out` >> fs[eval_operand_def, lookup_var_def]
QED

Theorem window_emit_alloca32_phase_mem:
  emit_op ALLOCA [Lit 32w] st = (out,en) /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func) /\
  fn_has_code st en func /\ alloca_room ctx func s /\ alloca_inv s /\
  (!b sz. FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,sz) ==> sz = 32) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t b. window_phase ctx func st en {st.cs_next_id} [] s t /\
    eval_operand out t = SOME (n2w b) /\
    (!x. out = Var x ==> not_fresh_at en x) /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (b,32) /\
    b+32 <= t.vs_alloca_next /\ t.vs_memory = s.vs_memory /\
    t.vs_labels = s.vs_labels /\ mem_cont_sim ctx func s t
Proof
  strip_tac >> drule_all window_emit_alloca32_sequence >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts st en) s` by
    metis_tac[window_emit_no_ranges_mem] >>
  `mem_cont_sim ctx func s (t with vs_inst_idx := LENGTH en.cs_current_insts)` by
    metis_tac[window_seq_mem_cont] >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH en.cs_current_insts`, `b`] >>
  (conj_tac >- metis_tac[window_seq_phase]) >>
  simp_tac (srw_ss()) [eval_operand_def, lookup_var_def] >>
  `t.vs_labels = s.vs_labels` by metis_tac[window_seq_labels] >>
  Cases_on `out` >> fs[eval_operand_def, lookup_var_def]
QED

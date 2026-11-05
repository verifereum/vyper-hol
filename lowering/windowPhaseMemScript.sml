(* Exact-endpoint safety companions for primitive window phases. *)
Theory windowPhaseMem
Ancestors
  abiEncoderWindowPhase windowSequenceMem allocaFootprint instMemFrontier
  abiEncoderWindowCursor abiEncoderWindowSequence abiEncoderWindowContract
  abiEncoderWindowLeaves emitHelperProps emitHelper compileEnv
  venomState venomExecSemantics venomInst fragExec list words
  abiEncoderRegisteredEffect abiEncoderPrimitiveEffect pred_set

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

Theorem window_cursor_load_phase_mem:
  emit_op MLOAD [ptr_op] st = (out,en) /\
  eval_operand ptr_op s = SOME (n2w b) /\ b < dimword (:256) /\
  b+32 <= s.vs_alloca_next /\
  fn_has_code st en func /\ alloca_inv s /\ alloca_room ctx func s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. window_phase ctx func st en {} [] s t /\
    eval_operand out t = SOME (mload b s) /\
    (!x. out = Var x ==> not_fresh_at en x) /\ t.vs_labels = s.vs_labels /\
    mem_cont_sim ctx func s t
Proof
  strip_tac >> drule_all window_cursor_load_sequence >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts st en) s` by
    (drule emit_mload_mem_ok >> disch_then irule >> simp[]) >>
  `mem_cont_sim ctx func s (t with vs_inst_idx := LENGTH en.cs_current_insts)` by
    metis_tac[window_seq_mem_cont, window_pure_seq_def] >>
  qexists_tac `t with vs_inst_idx := LENGTH en.cs_current_insts` >>
  (conj_tac >- metis_tac[window_pure_seq_phase]) >>
  simp_tac (srw_ss()) [eval_operand_def, lookup_var_def] >>
  `t.vs_labels = s.vs_labels` by
    metis_tac[window_pure_seq_def, window_seq_labels] >>
  Cases_on `out` >> fs[eval_operand_def, lookup_var_def]
QED

Theorem window_store_phase_mem:
  emit_void MSTORE [ptr_op;value] st = ((),en) /\
  eval_operand ptr_op s = SOME (n2w b) /\ eval_operand value s = SOME w /\
  b < dimword (:256) /\ b+32 <= s.vs_alloca_next /\ fn_has_code st en func /\
  alloca_inv s /\ alloca_room ctx func s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  abi_encoder_registered_effect ids outs s (mstore b w s) ==>
  window_phase ctx func st en ids outs s
    ((mstore b w s) with vs_inst_idx := LENGTH en.cs_current_insts) /\
  mem_cont_sim ctx func s
    ((mstore b w s) with vs_inst_idx := LENGTH en.cs_current_insts)
Proof
  strip_tac >> conj_tac >- metis_tac[window_store_phase] >>
  `run_inst_seq_mem_ok (emitted_insts st en) s` by
    (drule emit_mstore_mem_ok >> disch_then irule >> simp[]) >>
  drule_all window_emit_store_run >> strip_tac >>
  `en.cs_next_var = st.cs_next_var` by
    (qpat_assum `emit_void _ _ _ = _` mp_tac >>
     simp_tac (srw_ss()) [emit_void_def, fresh_id_def, emit_def,
       comp_bind_def, comp_return_def, LET_THM] >>
     disch_then (SUBST1_TAC o GSYM) >> simp[]) >>
  `window_seq st en s (mstore b w s)` by
    (simp[window_seq_def] >>
     simp_tac (srw_ss()) [lookup_var_def, mstore_def,
       write_memory_with_expansion_def, LET_THM]) >>
  metis_tac[window_seq_mem_cont]
QED

Theorem window_cursor_store_phase_mem:
  emit_void MSTORE [ptr_op;value] st = ((),en) /\
  eval_operand ptr_op s = SOME (n2w b) /\ eval_operand value s = SOME w /\
  b < dimword (:256) /\ b+32 <= s.vs_alloca_next /\
  FLOOKUP s.vs_allocas id = SOME (b,32) /\
  fn_has_code st en func /\ alloca_inv s /\ alloca_room ctx func s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  window_phase ctx func st en {id} [] s
    ((mstore b w s) with vs_inst_idx := LENGTH en.cs_current_insts) /\
  mem_cont_sim ctx func s
    ((mstore b w s) with vs_inst_idx := LENGTH en.cs_current_insts)
Proof
  strip_tac >> irule window_store_phase_mem >> asm_rewrite_tac[] >>
  metis_tac[abi_encoder_registered_slot_store, IN_SING]
QED

Theorem window_output_store_phase_mem:
  emit_void MSTORE [ptr_op;value] st = ((),en) /\
  eval_operand ptr_op s = SOME (n2w b) /\ eval_operand value s = SOME w /\
  b < dimword (:256) /\ b+32 <= s.vs_alloca_next /\ fn_has_code st en func /\
  alloca_inv s /\ alloca_room ctx func s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  window_phase ctx func st en {} [(b,32)] s
    ((mstore b w s) with vs_inst_idx := LENGTH en.cs_current_insts) /\
  mem_cont_sim ctx func s
    ((mstore b w s) with vs_inst_idx := LENGTH en.cs_current_insts)
Proof
  strip_tac >> irule window_store_phase_mem >> asm_rewrite_tac[] >>
  conj_tac >- metis_tac[] >>
  irule abi_encoder_output_store >> simp[]
QED

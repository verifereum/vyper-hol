Theory exprSimAbiEncodeFramedPhases
Ancestors
  exprSimAbiEncodeFramedBuiltin abiEncoderWindowPhase abiEncoderWindowCursor
  abiEncoderWindowSequence abiEncoderWindowContract exprSimAbiEncodeExecFrame
  exprSimAbiEncodeFramedLeaves emitHelperProps emitHelper compileEnv fragExec
  venomState venomExecSemantics venomMemDefs venomInst words finite_map list
  exprLoweringProps abiEncoderWindowLookup

Theorem abi_encode_framed_contract_strong:
  abi_encode_framed_contract ei ==> window_strong_contract ei
Proof
  simp[abi_encode_framed_contract_def, window_strong_contract_def] >> metis_tac[]
QED

Theorem abi_encode_framed_cursor_store_phase_observed:
  emit_void MSTORE [ptr_op;value] st = ((),en) /\
  eval_operand ptr_op s = SOME (n2w b) /\ eval_operand value s = SOME w /\
  b < dimword (:256) /\ FLOOKUP s.vs_allocas id = SOME (b,32) /\
  fn_has_code st en func /\ alloca_inv s /\ alloca_room ctx func s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  window_phase ctx func st en {id} [] s
    ((mstore b w s) with vs_inst_idx := LENGTH en.cs_current_insts) /\
  (!x. ~not_fresh_at en x ==>
    lookup_var x ((mstore b w s) with vs_inst_idx := LENGTH en.cs_current_insts) = lookup_var x s) /\
  abi_encode_exec_frame func s
    ((mstore b w s) with vs_inst_idx := LENGTH en.cs_current_insts)
Proof
  strip_tac >> drule_all window_cursor_store_phase_observed >> strip_tac >>
  simp[abi_encode_exec_frame_def, pending_alloca_size_def,
    mstore_def, write_memory_with_expansion_def]
QED

Theorem abi_encode_framed_cursor_load_phase_observed:
  emit_op MLOAD [ptr_op] st = (out,en) /\
  eval_operand ptr_op s = SOME (n2w b) /\ b < dimword (:256) /\
  fn_has_code st en func /\ alloca_inv s /\ alloca_room ctx func s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. window_phase ctx func st en {} [] s t /\
    eval_operand out t = SOME (mload b s) /\
    (!x. out = Var x ==> not_fresh_at en x) /\ t.vs_labels = s.vs_labels /\
    (!x. ~not_fresh_at en x ==> lookup_var x t = lookup_var x s) /\
    abi_encode_exec_frame func s t
Proof
  strip_tac >> drule_all window_cursor_load_sequence >> strip_tac >>
  `EVERY (\i. MEM i.inst_opcode [ADD;AND;MLOAD;MSTORE;MCOPY]) (emitted_insts st en)` by
    (drule emitted_insts_emit_op >> simp[mk_inst_def]) >>
  `abi_encode_exec_frame func s t` by
    (`run_inst_seq (emitted_insts st en) s = OK t` by
       gvs[window_pure_seq_def, window_seq_def] >>
     drule_all abi_encode_leaf_sequence_fmp >>
     gvs[window_pure_seq_def, abi_encode_exec_frame_def, pending_alloca_size_def]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ EVERY (not_fresh_at en) i.inst_outputs)
    (emitted_insts st en)` by
    (irule abi_window_emit_register_bounds >>
     qexistsl_tac [`[ptr_op]`, `MLOAD`, `out`] >> simp[]) >>
  `!x. ~not_fresh_at en x ==>
    lookup_var x (t with vs_inst_idx := LENGTH en.cs_current_insts) = lookup_var x s` by
    metis_tac[window_seq_high_vars, window_pure_seq_def] >>
  qexists_tac `t with vs_inst_idx := LENGTH en.cs_current_insts` >>
  (conj_tac >- metis_tac[window_pure_seq_phase]) >>
  simp_tac (srw_ss()) [eval_operand_def, lookup_var_def] >>
  `t.vs_labels = s.vs_labels` by
    metis_tac[window_pure_seq_def, window_seq_labels] >>
  Cases_on `out` >> fs[eval_operand_def, lookup_var_def]
QED

Theorem abi_encode_framed_alloca32_phase_observed:
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
    t.vs_labels = s.vs_labels /\
    (!x. ~not_fresh_at en x ==> lookup_var x t = lookup_var x s) /\
    abi_encode_exec_frame func s t
Proof
  strip_tac >> drule_all window_emit_alloca32_sequence >> strip_tac >>
  `EVERY (\i. MEM i.inst_opcode [ALLOCA;ADD;MSTORE]) (emitted_insts st en)` by
    (drule emitted_insts_emit_op >> simp[mk_inst_def]) >>
  `abi_encode_exec_frame func s t` by
    (`run_inst_seq (emitted_insts st en) s = OK t` by gvs[window_seq_def] >>
     drule_all abi_encode_setup_sequence_frame >> simp[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ EVERY (not_fresh_at en) i.inst_outputs)
    (emitted_insts st en)` by
    (irule abi_window_emit_register_bounds >>
     qexistsl_tac [`[Lit 32w]`, `ALLOCA`, `out`] >> simp[]) >>
  `!x. ~not_fresh_at en x ==>
    lookup_var x (t with vs_inst_idx := LENGTH en.cs_current_insts) = lookup_var x s` by
    metis_tac[window_seq_high_vars] >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH en.cs_current_insts`, `b`] >>
  (conj_tac >- metis_tac[window_seq_phase]) >>
  simp_tac (srw_ss()) [eval_operand_def, lookup_var_def] >>
  `t.vs_labels = s.vs_labels` by metis_tac[window_seq_labels] >>
  Cases_on `out` >> fs[eval_operand_def, lookup_var_def]
QED

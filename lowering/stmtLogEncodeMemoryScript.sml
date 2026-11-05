(* Instruction-check boundaries for scalar Log encoding. *)
Theory stmtLogEncodeMemory
Ancestors
  abiEncoderWindowBytesMem fragExecMem contractABI words arithmetic
  abiEncoderChildCode emitHelper emitHelperProps exprLoweringProps compileEnv list rich_list
  instMemFrontier venomExecSemantics venomInst venomState stmtReasonMemory moduleLoweringProps

(* The child reads an unrounded payload; its destination zeroing is rounded. *)
Theorem log_bytes_encode_mem_ok:
  compile_abi_encode_to_buf dst src (AbiBytestring maxlen) st = (out,en) /\
  eval_operand src s = SOME (n2w sb) /\ mload sb s = n2w cnt /\
  eval_operand dst s = SOME (n2w db) /\
  (!x. dst = Var x \/ src = Var x ==> not_fresh_at st x) /\
  sb + 32 + cnt <= s.vs_alloca_next /\
  db + 32 + contractABI$ceil32 cnt <= s.vs_alloca_next /\
  s.vs_alloca_next < dimword (:256) ==>
  run_inst_seq_mem_ok (emitted_insts st en) s
Proof
  strip_tac >>
  `cnt <= contractABI$ceil32 cnt /\
   cnt + 31 < 32 + contractABI$ceil32 cnt` by
    (mp_tac abiEncoderRoundingTheory.abi_encoder_ceil32_bounds >> decide_tac) >>
  drule window_bytes_mem_checks >> disch_then irule >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`cnt`, `db`, `sb`] >> simp[] >> decide_tac
QED

Theorem log_child_prefix_mem_ok:
  abi_encode_child_prefix dst ho dp st = (ops,en) /\
  eval_operand dp s = SOME (n2w slot) /\
  (!x. dp = Var x ==> not_fresh_at st x) /\
  slot < dimword (:256) /\ slot+32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts st en) s
Proof
  strip_tac >>
  qpat_x_assum `abi_encode_child_prefix _ _ _ _ = _` mp_tac >>
  simp[abi_encode_child_prefix_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def, fresh_var_def,
    fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, Once run_inst_seq_mem_ok_cons] >>
  (conj_tac >- (irule below_frontier_no_ranges >> simp[mk_inst_def])) >>
  simp[step_add_eq, eval_operand_def] >>
  Cases_on `eval_operand dst s` >> simp[] >>
  `eval_operand dp (update_var (STRING #"%" (toString st.cs_next_var))
    (x + n2w ho) s) = SOME (n2w slot)` by
    (Cases_on `dp` >> gvs[eval_operand_def] >>
     metis_tac[lookup_var_update_not_fresh, LESS_EQ_REFL]) >>
  simp[Once run_inst_seq_mem_ok_cons, below_frontier_MLOAD, update_var_def] >>
  Cases_on `step_inst_base
    (mk_inst (st.cs_next_id + 1) MLOAD [dp]
      [STRING #"%" (toString (st.cs_next_var + 1))])
    (s with vs_vars := s.vs_vars |+
      (STRING #"%" (toString st.cs_next_var),x + n2w ho))` >> simp[] >>
  irule run_inst_seq_mem_ok_every >> simp[] >> rpt strip_tac >>
  irule below_frontier_no_ranges >> simp[mk_inst_def]
QED

Theorem log_child_suffix_mem_ok:
  abi_encode_child_suffix head dp offset len st = (out,en) /\
  eval_operand head s = SOME (n2w hp) /\
  eval_operand dp s = SOME (n2w slot) /\
  (!x. dp = Var x ==> not_fresh_at st x) /\
  hp < dimword (:256) /\ slot < dimword (:256) /\
  hp+32 <= s.vs_alloca_next /\ slot+32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts st en) s
Proof
  strip_tac >>
  qpat_x_assum `abi_encode_child_suffix _ _ _ _ _ = _` mp_tac >>
  simp[abi_encode_child_suffix_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
    fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, Once run_inst_seq_mem_ok_cons, below_frontier_MSTORE] >>
  simp[step_mstore_eq] >>
  Cases_on `eval_operand offset s` >> simp[] >>
  simp[Once run_inst_seq_mem_ok_cons] >>
  (conj_tac >- (irule below_frontier_no_ranges >> simp[mk_inst_def])) >>
  simp[step_add_eq, eval_operand_mstore] >>
  Cases_on `eval_operand len s` >> simp[] >>
  `eval_operand dp (update_var (STRING #"%" (toString st.cs_next_var))
    (x + x') (mstore hp x s)) = SOME (n2w slot)` by
    (Cases_on `dp` >> gvs[eval_operand_def, eval_operand_mstore] >>
     metis_tac[lookup_var_update_not_fresh, LESS_EQ_REFL,
       lookup_var_mstore]) >>
  simp[run_inst_seq_mem_ok_last, below_frontier_MSTORE,
    update_var_def, mstore_def, write_memory_with_expansion_def]
QED

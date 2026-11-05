(* Boundary probe: the Log rounded-source bound suffices for a bytes member. *)
Theory stmtLogEncodeMemoryProbe
Ancestors
  abiEncoderWindowBytesMem abiEncoderWindowLeavesMem abiEncoderWindowComplexMem
  stmtSimLogStoreCompose fragExecMem contractABI words arithmetic
  abiEncoderChildCode emitHelper emitHelperProps exprLoweringProps compileEnv list rich_list
  instMemFrontier venomExecSemantics venomInst venomState stmtReasonMemory freshWrites moduleLoweringProps

Theorem log_bytes_window_probe:
  compile_abi_encode_to_buf dst src (AbiBytestring maxlen) st = (out,en) /\
  eval_operand src s = SOME (n2w sb) /\ mload sb s = n2w cnt /\
  eval_operand dst s = SOME (n2w db) /\
  (!x. dst = Var x \/ src = Var x ==> not_fresh_at st x) /\
  sb + 32 + contractABI$ceil32 cnt <= s.vs_alloca_next /\
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

Theorem log_child_prefix_mem_probe:
  abi_encode_child_prefix dst ho dp st = (ops,en) /\
  eval_operand dp s = SOME (n2w slot) /\
  (!x. dp = Var x ==> not_fresh_at st x) /\
  slot < dimword (:256) /\ slot+32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts st en) s
Proof
  strip_tac >>
  qpat_x_assum `abi_encode_child_prefix _ _ _ _ = _` mp_tac >>
  simp[abiEncoderChildCodeTheory.abi_encode_child_prefix_def,
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

Theorem log_child_suffix_mem_probe:
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
    update_var_def, venomStateTheory.mstore_def,
    venomStateTheory.write_memory_with_expansion_def]
QED

(* Raw-state probe: the two sequence witnesses are functional, not safety
   assumptions. No phase/control-normalized state is identified with a raw one. *)
Theorem log_dynamic_bytes_child_mem_probe:
  abi_encode_child_prefix dst ho dp st = (ops,prepared) /\
  compile_abi_encode_to_buf (SND (SND ops)) src (AbiBytestring maxlen)
    prepared = (len,copied) /\
  abi_encode_child_suffix (FST ops) dp (FST (SND ops)) len copied = (out,en) /\
  window_seq st prepared s p /\ window_seq prepared copied p q /\
  eval_operand dp s = SOME (n2w slot) /\
  (!x. dp = Var x ==> not_fresh_at st x) /\
  slot < dimword (:256) /\ slot+32 <= s.vs_alloca_next /\
  eval_operand src p = SOME (n2w sb) /\ mload sb p = n2w cnt /\
  eval_operand (SND (SND ops)) p = SOME (n2w db) /\
  (!x. SND (SND ops) = Var x \/ src = Var x ==> not_fresh_at prepared x) /\
  sb+32+contractABI$ceil32 cnt <= p.vs_alloca_next /\
  db+32+contractABI$ceil32 cnt <= p.vs_alloca_next /\
  p.vs_alloca_next < dimword (:256) /\
  eval_operand (FST ops) q = SOME (n2w hp) /\
  eval_operand dp q = SOME (n2w slot) /\
  (!x. dp = Var x ==> not_fresh_at copied x) /\
  hp < dimword (:256) /\ hp+32 <= q.vs_alloca_next /\
  slot+32 <= q.vs_alloca_next ==>
  compile_abi_encode_child dst src (AbiBytestring maxlen) T ho dp st = (out,en) /\
  run_inst_seq_mem_ok (emitted_insts st en) s
Proof
  strip_tac >> conj_tac
  >- simp[abi_encode_dynamic_child_phases, comp_bind_def] >>
  `run_inst_seq_mem_ok (emitted_insts st prepared) s` by
    (drule log_child_prefix_mem_probe >> disch_then irule >>
     (conj_tac >- first_assum ACCEPT_TAC) >> qexists_tac `slot` >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts prepared copied) p` by
    (drule log_bytes_window_probe >> disch_then irule >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     simp[] >> qexistsl_tac [`cnt`, `db`, `sb`] >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts copied en) q` by
    (drule log_child_suffix_mem_probe >> disch_then irule >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     conj_tac >- (qexists_tac `slot` >> simp[]) >>
     qexists_tac `hp` >> simp[]) >>
  `inst_extends copied en` by metis_tac[abi_encode_child_suffix_shape] >>
  fs[abiEncoderWindowSequenceTheory.window_seq_def] >>
  `emitted_insts st en = emitted_insts st prepared ++
    (emitted_insts prepared copied ++ emitted_insts copied en)` by
    metis_tac[emitted_insts_append, inst_extends_trans, inst_extends_def] >>
  simp[] >> irule run_inst_seq_mem_ok_append >> reverse conj_tac
  >- (irule run_inst_seq_mem_ok_append >> simp[]) >>
  rpt strip_tac >>
  qpat_assum `run_inst_seq (emitted_insts st prepared) s = OK p`
    (mp_then Any mp_tac run_inst_seq_append) >>
  disch_then (qspec_then `emitted_insts prepared copied` assume_tac) >> gvs[]
QED

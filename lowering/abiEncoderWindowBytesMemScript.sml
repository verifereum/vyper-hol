(* Memory checks for the exact straight-line bytes encoder trace. *)
Theory abiEncoderWindowBytesMem
Ancestors
  abiEncoderWindowBytes abiEncoderWindowLeaves windowSequenceMem allocaFootprint
  abiEncoderBytesCode abiEncoderWindowSequence fragExecMem instMemFrontier
  abiEncoderRounding abiEncoderMemory emitHelperProps exprLoweringProps
  compileEnv loweringStateRelDefs emitHelper freshWrites venomState venomExecSemantics venomInst
  words list rich_list arithmetic

Theorem window_seq_mem_checks_chain[local]:
  window_seq st mid s t /\ window_seq mid fin t u /\
  run_inst_seq_mem_ok (emitted_insts st mid) s /\
  run_inst_seq_mem_ok (emitted_insts mid fin) t ==>
  run_inst_seq_mem_ok (emitted_insts st fin) s
Proof
  simp_tac bool_ss [window_seq_def] >> strip_tac >>
  `emitted_insts st fin = emitted_insts st mid ++ emitted_insts mid fin` by
    metis_tac[emitted_insts_append, inst_extends_def] >>
  simp[] >> irule run_inst_seq_mem_ok_append >> simp[]
QED


Theorem window_bytes_suffix_mem_checks[local]:
  abi_encode_bytes_suffix len st = (out,fin) ==>
  run_inst_seq_mem_ok (emitted_insts st fin) s
Proof
  simp[abi_encode_bytes_suffix_def, abi_encode_round_def, comp_bind_def,
    emit_op_def, fresh_var_def, fresh_id_def, emit_def, comp_return_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  gvs[] >> simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >> simp[DROP_LENGTH_APPEND] >>
  irule run_inst_seq_mem_ok_every >> simp[] >> rpt strip_tac >>
  irule below_frontier_no_ranges >> simp[mk_inst_def]
QED

Theorem window_bytes_prefix_mem_checks[local]:
  abi_encode_bytes_prefix dst src st = (ops,fin) /\
  eval_operand src s = SOME (n2w sb) /\ sb < dimword (:256) /\
  sb + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts st fin) s
Proof
  strip_tac >>
  qpat_x_assum `abi_encode_bytes_prefix _ _ _ = _` mp_tac >>
  simp[abi_encode_bytes_prefix_def, abi_encode_round_def, comp_bind_def,
    emit_op_def, fresh_var_def, fresh_id_def, emit_def, comp_return_def,
    comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, Once run_inst_seq_mem_ok_cons,
    below_frontier_MLOAD] >>
  Cases_on `step_inst_base (mk_inst st.cs_next_id MLOAD [src]
    [STRING #"%" (toString st.cs_next_var)]) s` >> simp[] >>
  irule run_inst_seq_mem_ok_every >> simp[] >> rpt strip_tac >>
  irule below_frontier_no_ranges >> simp[mk_inst_def]
QED

Theorem window_bytes_copy_mem_checks[local]:
  abi_encode_bytes_copy dst src len lastptr st = ((),fin) /\
  eval_operand dst s = SOME (n2w db) /\ eval_operand src s = SOME (n2w sb) /\
  eval_operand len s = SOME (n2w cnt) /\
  eval_operand lastptr s = SOME (n2w (db+rounded)) /\
  db+rounded < dimword (:256) /\ sb < dimword (:256) /\
  32+cnt < dimword (:256) /\ cnt <= rounded /\
  sb+32+cnt <= s.vs_alloca_next /\ db+32+rounded <= s.vs_alloca_next /\
  (!x. dst = Var x \/ src = Var x ==> not_fresh_at st x) ==>
  run_inst_seq_mem_ok (emitted_insts st fin) s
Proof
  simp_tac bool_ss [abi_encode_bytes_copy_def, comp_bind_def,
    comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  rename1 `emit_void MSTORE [lastptr;Lit 0w] st = ((),c1)` >>
  rename1 `emit_op ADD [Lit 32w;len] c1 = (copylen,c2)` >>
  rename1 `emit_void MCOPY [dst;src;copylen] c2 = ((),fin)` >>
  drule window_emit_store_run >>
  disch_then (qspecl_then [`0w`, `s`, `db+rounded`] mp_tac) >>
  simp[eval_operand_def] >> strip_tac >>
  drule window_emit_add_pure >>
  disch_then (qspec_then `mstore (db+rounded) 0w s` mp_tac) >>
  simp[eval_operand_mstore, eval_operand_def, word_add_n2w] >> strip_tac >>
  `c1.cs_next_var = st.cs_next_var` by
    gvs[emit_void_def, fresh_id_def, emit_def, comp_bind_def, comp_return_def] >>
  `eval_operand dst t = SOME (n2w db) /\
   eval_operand src t = SOME (n2w sb)` by
    (fs[window_pure_seq_def] >> conj_tac >>
     drule window_seq_eval >> disch_then irule >>
     simp[eval_operand_mstore, not_fresh_at_def] >>
     fs[not_fresh_at_def]) >>
  `t.vs_alloca_next = s.vs_alloca_next` by
    fs[window_pure_seq_def, mstore_def, write_memory_with_expansion_def] >>
  `run_inst_seq_mem_ok (emitted_insts c2 fin) t` by
    (drule emit_mcopy_mem_ok >> disch_then irule >>
     simp[] >> decide_tac) >>
  `run_inst_seq_mem_ok (emitted_insts st c1) s` by
    (drule emit_mstore_mem_ok >> disch_then irule >> simp[]) >>
  drule inst_extends_emit_op >> strip_tac >>
  drule inst_extends_emit_void >> strip_tac >>
  `emitted_insts st fin = emitted_insts st c1 ++
    (emitted_insts c1 c2 ++ emitted_insts c2 fin)` by
    metis_tac[emitted_insts_append, inst_extends_def, inst_extends_trans] >>
  simp[] >> irule run_inst_seq_mem_ok_append >> conj_tac
  >- (qpat_assum `run_inst_seq (emitted_insts st c1) s = _`
        (mp_then Any mp_tac run_inst_seq_append) >>
      disch_then (qspec_then `emitted_insts c1 c2` assume_tac) >>
      fs[window_pure_seq_def, window_seq_def]) >>
  irule run_inst_seq_mem_ok_append >> simp[] >> rpt strip_tac >> gvs[] >>
  drule emit_op_mem_ok >> disch_then irule >>
  simp[] >> irule below_frontier_no_ranges >> simp[mk_inst_def]
QED

Theorem window_bytes_body_mem_checks[local]:
  abi_encode_bytes_prefix dst src st = (ops,ready) /\
  abi_encode_bytes_copy dst src (FST ops) (SND ops) ready = ((),copied) /\
  eval_operand src s = SOME (n2w sb) /\ mload sb s = n2w cnt /\
  eval_operand dst s = SOME (n2w db) /\
  (!x. dst = Var x \/ src = Var x ==> not_fresh_at st x) /\
  sb < dimword (:256) /\ cnt+31 < dimword (:256) /\
  db+contractABI$ceil32 cnt < dimword (:256) /\ 32+cnt < dimword (:256) /\
  sb+32+cnt <= s.vs_alloca_next /\
  db+32+contractABI$ceil32 cnt <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts st copied) s
Proof
  strip_tac >>
  `!x. dst = Var x ==> not_fresh_at st x` by metis_tac[] >>
  drule_all window_bytes_prefix_sequence >> strip_tac >>
  rename1 `window_pure_seq st ready s prepared` >>
  `eval_operand dst prepared = SOME (n2w db) /\
   eval_operand src prepared = SOME (n2w sb)` by
    metis_tac[window_seq_eval, window_pure_seq_def] >>
  `!x. dst = Var x \/ src = Var x ==> not_fresh_at ready x` by
    metis_tac[not_fresh_at_mono, window_seq_mono, window_pure_seq_def] >>
  drule_all window_bytes_copy_sequence >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts st ready) s` by
    (drule window_bytes_prefix_mem_checks >> disch_then irule >>
     qexists_tac `sb` >> simp[] >> decide_tac) >>
  `run_inst_seq_mem_ok (emitted_insts ready copied) prepared` by
    (drule window_bytes_copy_mem_checks >> disch_then irule >>
     simp[] >> (conj_tac >- first_assum ACCEPT_TAC) >>
     qexistsl_tac [`cnt`, `db`, `contractABI$ceil32 cnt`, `sb`] >>
     fs[window_pure_seq_def] >>
     mp_tac (Q.INST [`cnt` |-> `cnt`] abi_encoder_ceil32_bounds) >>
     simp[] >> decide_tac) >>
  irule window_seq_mem_checks_chain >>
  fs[window_pure_seq_def] >> goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem window_bytes_mem_checks:
  compile_abi_encode_to_buf dst src (AbiBytestring maxlen) st = (out,final) /\
  eval_operand src s = SOME (n2w sb) /\ mload sb s = n2w cnt /\
  eval_operand dst s = SOME (n2w db) /\
  (!x. dst = Var x \/ src = Var x ==> not_fresh_at st x) /\
  sb < dimword (:256) /\ cnt+31 < dimword (:256) /\
  db+contractABI$ceil32 cnt < dimword (:256) /\ 32+cnt < dimword (:256) /\
  sb+32+cnt <= s.vs_alloca_next /\
  db+32+contractABI$ceil32 cnt <= s.vs_alloca_next /\
  sb+32+cnt < dimword (:256) /\
  db+32+contractABI$ceil32 cnt < dimword (:256) ==>
  run_inst_seq_mem_ok (emitted_insts st final) s
Proof
  strip_tac >> drule abi_encode_bytes_trace >> strip_tac >>
  drule_all window_bytes_body_sequence >> strip_tac >>
  rename1 `window_seq st copied s prepared` >>
  drule_all window_bytes_suffix_sequence >> strip_tac >>
  drule_all window_bytes_body_mem_checks >> strip_tac >>
  drule window_bytes_suffix_mem_checks >>
  disch_then (qspec_then `prepared` assume_tac) >>
  irule window_seq_mem_checks_chain >>
  fs[window_pure_seq_def] >> goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem window_bytes_sequence_mem:
  compile_abi_encode_to_buf dst src (AbiBytestring maxlen) st = (out,final) /\
  eval_operand src s = SOME (n2w sb) /\ mload sb s = n2w cnt /\
  eval_operand dst s = SOME (n2w db) /\
  (!x. dst = Var x \/ src = Var x ==> not_fresh_at st x) /\
  sb < dimword (:256) /\ cnt+31 < dimword (:256) /\
  db+contractABI$ceil32 cnt < dimword (:256) /\ 32+cnt < dimword (:256) /\
  sb+32+cnt <= s.vs_alloca_next /\
  db+32+contractABI$ceil32 cnt <= s.vs_alloca_next /\
  sb+32+cnt < dimword (:256) /\
  db+32+contractABI$ceil32 cnt < dimword (:256) /\
  fn_has_code st final func /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. window_seq st final s t /\
    mem_cont_sim ctx func s (t with vs_inst_idx := LENGTH final.cs_current_insts) /\
    eval_operand out t = SOME (n2w (32+contractABI$ceil32 cnt)) /\
    t.vs_memory = (mcopy db sb (32+cnt)
      (mstore (db+contractABI$ceil32 cnt) 0w s)).vs_memory /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section /\
    t.vs_halted = s.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
    t.vs_inst_idx = s.vs_inst_idx /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_logs = s.vs_logs /\ t.vs_requests = s.vs_requests /\
    t.vs_pending_deletions = s.vs_pending_deletions
Proof
  strip_tac >> drule_all window_bytes_mem_checks >> strip_tac >>
  drule_all window_bytes_sequence >> strip_tac >>
  qexists_tac `t` >> simp[] >> irule window_seq_mem_cont >>
  (conj_tac >- first_assum ACCEPT_TAC) >> qexists_tac `st` >> simp[]
QED

(* Zero payload still copies its header and writes a complete zero word. *)
Theorem window_bytes_empty_mem_checks:
  compile_abi_encode_to_buf dst src (AbiBytestring maxlen) st = (out,final) /\
  eval_operand src s = SOME (n2w sb) /\ mload sb s = 0w /\
  eval_operand dst s = SOME (n2w db) /\
  (!x. dst = Var x \/ src = Var x ==> not_fresh_at st x) /\
  sb+32 <= s.vs_alloca_next /\ db+32 <= s.vs_alloca_next /\
  sb+32 < dimword (:256) /\ db+32 < dimword (:256) ==>
  run_inst_seq_mem_ok (emitted_insts st final) s
Proof
  strip_tac >> drule window_bytes_mem_checks >> disch_then irule >>
  (conj_tac >- first_assum ACCEPT_TAC) >> qexistsl_tac [`0`, `db`, `sb`] >>
  simp[contractABITheory.ceil32_def] >> decide_tac
QED
